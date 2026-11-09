"""Read pinned ScalaTest bytecode only. Inventory is not effect authority."""
import hashlib
import importlib.util
import json
from pathlib import Path
import zipfile

OUT = Path(__file__).resolve().parent
ROOT = OUT.parents[1]
FIXTURE = ROOT / "fixtures/scalatest-execution"
READER = ROOT / "benchmark-output/native-footprint-diagnostic-v1/local_capsules.py"
FLOW_READER = ROOT / "benchmark-output/framework-callback-proof-v1/verify.py"
spec = importlib.util.spec_from_file_location("independent_reader", READER)
reader = importlib.util.module_from_spec(spec)
spec.loader.exec_module(reader)
spec = importlib.util.spec_from_file_location("transport_reader", FLOW_READER)
flow = importlib.util.module_from_spec(spec)
spec.loader.exec_module(flow)
MAVEN = Path("/Users/danielporter/Library/Caches/Coursier/v1/https/repo1.maven.org/maven2/org/scalatest")
PROVIDERS = {
    "word": ("scalatest-wordspec_2.13", "08050f3d05c72575cac29a1483185b443d5f9f34c1fcf80c683083330385ef93"),
    "core": ("scalatest-core_2.13", "30230081d029f6341b83fe7f157d336113e1c97497fe950169293d28a5bf2936"),
}
OWNERS = {
    "word": ["AnyWordSpec", "AnyWordSpecLike", "AnyWordSpecLike$$anon$1", "AnyWordSpecLike$$anon$2",
        "AnyWordSpecLike$$anon$3", "AnyWordSpecLike$WordSpecStringWrapper",
        "AnyWordSpecLike$ResultOfTaggedAsInvocationOnString", "AnyWordSpecLike$ItWord",
        "AnyWordSpecLike$TheyWord", "AnyWordSpecLike$AfterWord"],
    "core": ["verbs/ShouldVerb", "verbs/ShouldVerb$StringShouldWrapperForVerb", "verbs/ShouldVerb$$anon$1",
        "verbs/StringVerbBlockRegistration", "verbs/SubjectWithAfterWordRegistration", "verbs/BehaveWord",
        "Engine", "SuperEngine", "SuperEngine$TestLeaf", "Transformer", "TestSuite", "TestSuite$NoArgTest",
        "Suite", "Suite$", "TestRegistration", "Filter", "Args", "ConfigMap", "TestData"],
}
FULL = {"org/scalatest/wordspec/AnyWordSpecLike", "org/scalatest/wordspec/AnyWordSpecLike$$anon$1",
    "org/scalatest/wordspec/AnyWordSpecLike$$anon$2", "org/scalatest/wordspec/AnyWordSpecLike$$anon$3",
    "org/scalatest/wordspec/AnyWordSpecLike$WordSpecStringWrapper",
    "org/scalatest/verbs/ShouldVerb", "org/scalatest/verbs/ShouldVerb$StringShouldWrapperForVerb",
    "org/scalatest/verbs/ShouldVerb$$anon$1", "org/scalatest/Engine"}
SELECTED = {"<init>", "$init$", "registerTest", "registerIgnoredTest", "registerNestedBranch", "registerFlatBranch",
    "registerTestImpl", "registerIgnoredTestImpl", "run", "runTest", "runTests", "runImpl", "runTestImpl", "runTestsImpl",
    "runNestedSuites", "runNestedSuitesImpl", "testNames", "tags", "expectedTestCount", "withFixture", "nestedSuites",
    "suiteName", "suiteId", "testDataFor", "autoTagClassAnnotations", "convertToWordSpecStringWrapper",
    "convertToStringShouldWrapperForVerb", "testFun", "apply", "name", "configMap", "filter", "stopper",
    "distributor", "newInstance", "styleName", "testSortingReporter", "testNamesList", "testsMap"}


def sha(raw):
    return hashlib.sha256(raw).hexdigest()


def dynamic(cls, cp):
    entry = cls["ref"](cp, (18,))
    handle, arguments = cls["bootstraps"][entry[1]]
    target = cls["ref"](handle, (15,))
    nt = cls["ref"](entry[2], (12,))
    result = {"name": cls["utf"](nt[1]), "descriptor": cls["utf"](nt[2]),
        "bootstrap": cls["member"](target[2]), "bootstrap_handle_kind": target[1]}
    implementations = []
    for value in arguments:
        item = cls["cp"][value]
        if item and item[0] == 15:
            implementations.append({"handle_kind": item[1], **cls["member"](item[2])})
    result["method_handles"] = implementations
    return result


def method_record(cls, method):
    row = {"owner": cls["name"], "name": method["name"], "descriptor": method["descriptor"], "flags": method["flags"]}
    if "code" not in method:
        return dict(row, code_present=False, requirement="abstract/native remains unresolved until exact implementation/contract")
    code = method["code"]
    instructions = reader.instructions(cls, method)
    calls, fields, allocations, dynamics, constants = [], [], [], [], []
    for pc, op, operand, width in instructions:
        if 182 <= op <= 185:
            calls.append({"pc": pc, "opcode": op, **cls["member"](operand)})
        elif 178 <= op <= 181:
            fields.append({"pc": pc, "opcode": op, **cls["member"](operand, (9,))})
        elif op == 187:
            allocations.append({"pc": pc, "class": cls["cls"](operand)})
        elif op == 186:
            dynamics.append({"pc": pc, **dynamic(cls, operand)})
        elif op in (18, 19):
            item = cls["cp"][operand]
            if item[0] in (7, 8):
                constants.append({"pc": pc, "kind": "class" if item[0] == 7 else "string", "value": cls["utf"](item[1])})
    row.update(code_present=True, code_bytes=len(code), code_sha256=sha(code),
        instructions=len(instructions), exception_handlers=method.get("exception_handlers", []),
        calls=calls, field_accesses=fields, allocations=allocations, dynamics=dynamics, constants=constants)
    if cls["name"] in FULL or method["name"] in ("<init>", "$init$"):
        try:
            row["local_transport"] = flow.flow(cls, method)
        except (ValueError, IndexError, KeyError) as error:
            row["local_transport_open"] = str(error)
    return row


def main():
    if (FIXTURE / "manifest.json").exists() or (OUT / "inventory.json").exists():
        raise ValueError("new fixture/inventory paths required")
    classes, methods, providers, files = [], [], [], []
    for key, (artifact, expected) in PROVIDERS.items():
        jar = MAVEN / artifact / "3.2.19" / (artifact + "-3.2.19.jar")
        before = reader.pin(jar)
        if before["sha256"] != expected:
            raise ValueError("wrong pinned provider")
        providers.append(dict(before, artifact=artifact, version="3.2.19"))
        with zipfile.ZipFile(jar) as archive:
            names = archive.namelist()
            if len(names) != len(set(names)):
                raise ValueError("duplicate archive entries")
            for suffix in OWNERS[key]:
                owner = ("org/scalatest/wordspec/" if key == "word" else "org/scalatest/") + suffix
                entry = owner + ".class"
                raw = archive.read(entry)
                cls = reader.classfile(raw)
                if cls["name"] != owner:
                    raise ValueError("wrong class owner")
                relative = "classes/" + entry
                target = FIXTURE / relative
                target.parent.mkdir(parents=True, exist_ok=True)
                target.write_bytes(raw)
                files.append({"path": relative, "bytes": len(raw), "sha256": sha(raw),
                    "provider": key, "provider_entry": entry, "provider_sha256": expected})
                classes.append({"owner": owner, "class_sha256": sha(raw), "bytes": len(raw),
                    "flags": cls["flags"], "parent": cls["parent"], "interfaces": cls["interfaces"],
                    "provider": key, "methods": len(cls["methods"]), "fields": cls.get("fields", [])})
                for method in cls["methods"]:
                    if (owner in FULL or method["name"] in SELECTED
                            or method["name"].startswith(("$anonfun$run", "$anonfun$register", "org$scalatest$wordspec$AnyWordSpecLike"))):
                        methods.append(method_record(cls, method))
        if reader.pin(jar) != before:
            raise ValueError("provider changed while reading")
    report = {"schema": "scalatest-synchronous-wordspec-bytecode-inventory/v1", "diagnostic_only": True,
        "qualification": "Exact genuine pinned class/code/ABI inventory; no JVM execution, effect closure, framework purity, catalogue authority or exclusion proof",
        "providers": providers, "reader": reader.pin(READER), "transport_reader": reader.pin(FLOW_READER),
        "inventory_tool": reader.pin(Path(__file__)), "classes": classes, "methods": methods,
        "no_compiler_JVM_or_native_query_children": True}
    path = OUT / "inventory.json"
    path.write_text(json.dumps(report, indent=2, sort_keys=True) + "\n")
    manifest = {"schema": "scalatest-synchronous-wordspec-extracted-classes/v1", "providers": providers,
        "qualification": report["qualification"], "inventory_tool": reader.pin(Path(__file__)),
        "inventory": reader.pin(path), "files": sorted(files, key=lambda r: r["path"])}
    (FIXTURE / "manifest.json").write_text(json.dumps(manifest, indent=2, sort_keys=True) + "\n")
    print(json.dumps({"classes": len(classes), "methods": len(methods), "fixture_bytes": sum(r["bytes"] for r in files),
        "inventory": reader.pin(path), "manifest": reader.pin(FIXTURE / "manifest.json")}))


if __name__ == "__main__":
    main()
