//! CLI event rendering. The solver sends fixed-size records at publication barriers.
use selector_solve::{SolveControl, SolveEvent, SolveObserver, StopReason};
use serde_json::{Value, json};
use std::{
    fs::{self, File, OpenOptions},
    io::{self, Write},
    path::Path,
    sync::{
        Arc, Condvar, Mutex,
        atomic::{AtomicBool, Ordering},
    },
    time::{Duration, Instant},
};

static INTERRUPTED: AtomicBool = AtomicBool::new(false);

#[derive(Debug, Clone, Default)]
pub struct EventSink(Arc<Mutex<Option<File>>>);
impl EventSink {
    pub fn new(path: Option<&Path>) -> io::Result<Self> {
        let file = path
            .map(|path| {
                if let Some(parent) = path.parent().filter(|p| !p.as_os_str().is_empty()) {
                    fs::create_dir_all(parent)?;
                }
                OpenOptions::new()
                    .create(true)
                    .truncate(true)
                    .write(true)
                    .open(path)
            })
            .transpose()?;
        Ok(Self(Arc::new(Mutex::new(file))))
    }
    pub fn emit(&self, value: &Value) {
        // One lock also keeps concurrent revision records as complete JSON lines.
        let Ok(mut file) = self.0.lock() else {
            return;
        };
        let mut stderr = io::stderr().lock();
        let _ = serde_json::to_writer(&mut stderr, value);
        let _ = stderr.write_all(b"\n");
        if let Some(file) = file.as_mut() {
            let _ = serde_json::to_writer(&mut *file, value);
            let _ = file.write_all(b"\n");
            let _ = file.flush();
        }
    }
}

/// A quiet long stage still reports its current phase and elapsed time. Dropping
/// the guard wakes and joins the timer immediately; no timer outlives its stage.
pub struct StageProgress {
    done: Arc<(Mutex<bool>, Condvar)>,
    worker: Option<std::thread::JoinHandle<()>>,
    sink: EventSink,
    phase: String,
    revision: String,
    started: Instant,
}
impl StageProgress {
    pub fn start(sink: EventSink, phase: impl Into<String>, revision: impl Into<String>) -> Self {
        Self::with_interval(sink, phase.into(), revision.into(), Duration::from_secs(1))
    }
    fn with_interval(sink: EventSink, phase: String, revision: String, interval: Duration) -> Self {
        let started = Instant::now();
        let done = Arc::new((Mutex::new(false), Condvar::new()));
        sink.emit(&json!({"stage":"stage_begin","phase":phase,"revision":revision,"pid":std::process::id()}));
        let worker = {
            let done = done.clone();
            let sink = sink.clone();
            let phase = phase.clone();
            let revision = revision.clone();
            std::thread::spawn(move || {
                let (lock, condition) = &*done;
                let Ok(mut guard) = lock.lock() else {
                    return;
                };
                loop {
                    let Ok((next, _)) =
                        condition.wait_timeout_while(guard, interval, |done| !*done)
                    else {
                        return;
                    };
                    guard = next;
                    if *guard {
                        break;
                    }
                    sink.emit(
                        &json!({"stage":"stage_progress","phase":phase,"revision":revision,
                        "pid":std::process::id(),"elapsed_ns":started.elapsed().as_nanos()}),
                    );
                }
            })
        };
        Self {
            done,
            worker: Some(worker),
            sink,
            phase,
            revision,
            started,
        }
    }
}
impl Drop for StageProgress {
    fn drop(&mut self) {
        if let Ok(mut done) = self.done.0.lock() {
            *done = true;
            self.done.1.notify_one();
        }
        if let Some(worker) = self.worker.take() {
            let _ = worker.join();
        }
        self.sink.emit(
            &json!({"stage":"stage_end","phase":self.phase,"revision":self.revision,
            "pid":std::process::id(),"elapsed_ns":self.started.elapsed().as_nanos()}),
        );
    }
}

#[derive(Debug)]
pub struct Observer {
    revision: &'static str,
    sink: EventSink,
    control: Arc<SolveControl>,
    max_contexts: usize,
    max_steps: u64,
    memory_budget: usize,
}
impl Observer {
    pub fn new(
        revision: &'static str,
        sink: EventSink,
        control: Arc<SolveControl>,
        options: &selector_solve::SolveOptions,
    ) -> Self {
        Self {
            revision,
            sink,
            control,
            max_contexts: options.max_contexts,
            max_steps: options.max_steps,
            memory_budget: options.memory_budget_bytes,
        }
    }
    fn event_json(&self, event: SolveEvent) -> Value {
        let c = event.counters;
        let budget = event.stop.map(|reason| match reason {
            StopReason::ContextLimit => {
                json!({"kind":"contexts", "observed":c.contexts, "limit":self.max_contexts})
            }
            StopReason::StepLimit => {
                json!({"kind":"steps", "observed":c.operations, "limit":self.max_steps})
            }
            StopReason::MemoryLimit => {
                json!({"kind":"owned_bytes", "observed":c.owned_bytes, "limit":self.memory_budget})
            }
            _ => json!({"kind":format!("{reason:?}")}),
        });
        let cache = event.cache.map(|cache| json!({
            "action":format!("{:?}",cache.action), "reason":format!("{:?}",cache.reason),
            "families":cache.families,"contexts":cache.contexts,
            "producer":cache.identity.producer.to_string(),
            "facts":cache.identity.facts.to_string(),"graph":cache.identity.graph.to_string(),
            "models":cache.identity.models.to_string(),"options":cache.identity.options.to_string(),
            "artifact":cache.artifact.to_string(),
        }));
        json!({"stage":"query_solve", "revision":self.revision,
            "phase":format!("{:?}",event.phase),"round":event.round,
            "elapsed_ns":event.elapsed_ns,"contexts":c.contexts,"context_hits":c.context_hits,
            "evaluations":c.evaluations,"reevaluations":c.reevaluations,
            "novel_publications":c.novel_publications,"repeated_publications":c.repeated_publications,
            "dispatch_targets":c.dispatch_targets,"callback_targets":c.callback_targets,
            "operations":c.operations,"pending":c.pending,"owned_bytes":c.owned_bytes,
            "widened_contexts":c.widened_contexts,"stop":budget,"cache":cache})
    }
}
impl SolveObserver for Observer {
    fn observe(&self, event: SolveEvent) {
        if INTERRUPTED.load(Ordering::Relaxed) {
            self.control.cancel();
        }
        self.sink.emit(&self.event_json(event));
    }
    fn work_row(&self, row: selector_solve::WorkRow) {
        self.sink.emit(&json!({"stage":"query_work_census", "revision":self.revision,
            "node":row.node.0,"new_contexts":row.new_contexts,"evaluations":row.evaluations,
            "reevaluations":row.reevaluations,"novel_publications":row.novel_publications,
            "repeated_publications":row.repeated_publications,"dispatch_targets":row.dispatch_targets,
            "callback_targets":row.callback_targets,"widened_contexts":row.widened_contexts,
            "inherited_weight":row.inherited_weight}));
    }
    fn work_row_with_origin(
        &self,
        row: selector_solve::WorkRow,
        origin: selector_solve::WorkOrigin<'_>,
    ) {
        self.sink.emit(&json!({"stage":"query_work_census","revision":self.revision,
            "node":row.node.0,"symbol":origin.symbol,"context":origin.context,"path":origin.path,
            "new_contexts":row.new_contexts,"evaluations":row.evaluations,"reevaluations":row.reevaluations,
            "novel_publications":row.novel_publications,"repeated_publications":row.repeated_publications,
            "dispatch_targets":row.dispatch_targets,"callback_targets":row.callback_targets,
            "widened_contexts":row.widened_contexts,"inherited_weight":row.inherited_weight}));
    }
}

/// Signal handlers only store an atomic flag. All allocation and checkpoint work
/// remains on the coordinator, after the next progress/publication callback.
pub struct SignalGuard {
    #[cfg(unix)]
    old_int: libc::sighandler_t,
    #[cfg(unix)]
    old_term: libc::sighandler_t,
}
impl SignalGuard {
    pub fn install() -> io::Result<Self> {
        INTERRUPTED.store(false, Ordering::Relaxed);
        #[cfg(unix)]
        {
            extern "C" fn interrupt(_: libc::c_int) {
                INTERRUPTED.store(true, Ordering::Relaxed);
            }
            let old_int =
                unsafe { libc::signal(libc::SIGINT, interrupt as *const () as libc::sighandler_t) };
            if old_int == libc::SIG_ERR {
                return Err(io::Error::last_os_error());
            }
            let old_term = unsafe {
                libc::signal(libc::SIGTERM, interrupt as *const () as libc::sighandler_t)
            };
            if old_term == libc::SIG_ERR {
                unsafe {
                    libc::signal(libc::SIGINT, old_int);
                }
                return Err(io::Error::last_os_error());
            }
            Ok(Self { old_int, old_term })
        }
        #[cfg(not(unix))]
        {
            Ok(Self {})
        }
    }
}
impl Drop for SignalGuard {
    fn drop(&mut self) {
        #[cfg(unix)]
        unsafe {
            libc::signal(libc::SIGINT, self.old_int);
            libc::signal(libc::SIGTERM, self.old_term);
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use selector_solve::{SolvePhase, WorkCounters};
    #[test]
    fn typed_limits_keep_observed_values_and_revision() {
        let options = selector_solve::SolveOptions {
            max_steps: 17,
            ..Default::default()
        };
        let observer = Observer::new(
            "base",
            EventSink::new(None).unwrap(),
            Arc::new(SolveControl::default()),
            &options,
        );
        let record = observer.event_json(SolveEvent {
            phase: SolvePhase::Stopped,
            round: 3,
            elapsed_ns: 41,
            counters: WorkCounters {
                operations: 19,
                pending: 2,
                ..Default::default()
            },
            stop: Some(StopReason::StepLimit),
            cache: None,
        });
        assert_eq!(record["revision"], "base");
        assert_eq!(
            record["stop"],
            json!({"kind":"steps","observed":19,"limit":17})
        );
        assert_eq!(record["pending"], 2);
    }
    #[test]
    fn progress_file_contains_complete_concurrent_records() {
        let dir = tempfile::tempdir().unwrap();
        let path = dir.path().join("progress.jsonl");
        let sink = EventSink::new(Some(&path)).unwrap();
        std::thread::scope(|scope| {
            for revision in ["base", "head"] {
                let sink = sink.clone();
                scope.spawn(move || {
                    for round in 0..3 {
                        sink.emit(&json!({"revision":revision,"round":round}));
                    }
                });
            }
        });
        let text = fs::read_to_string(path).unwrap();
        assert_eq!(
            text.lines()
                .map(|line| serde_json::from_str::<Value>(line).unwrap())
                .count(),
            6
        );
    }
    #[test]
    fn stage_timer_stops_at_stage_boundary_and_keeps_phase_metadata() {
        let dir = tempfile::tempdir().unwrap();
        let path = dir.path().join("events.jsonl");
        let sink = EventSink::new(Some(&path)).unwrap();
        let stage = StageProgress::with_interval(
            sink,
            "extract".into(),
            "base".into(),
            Duration::from_millis(2),
        );
        let deadline = Instant::now() + Duration::from_secs(1);
        while !fs::read_to_string(&path)
            .unwrap()
            .contains("stage_progress")
        {
            assert!(
                Instant::now() < deadline,
                "stage timer did not publish progress"
            );
            std::thread::sleep(Duration::from_millis(2));
        }
        drop(stage);
        let text = fs::read_to_string(&path).unwrap();
        let events: Vec<Value> = text
            .lines()
            .map(|line| serde_json::from_str(line).unwrap())
            .collect();
        assert_eq!(events.first().unwrap()["stage"], "stage_begin");
        assert_eq!(events.last().unwrap()["stage"], "stage_end");
        assert!(
            events
                .iter()
                .all(|event| event["phase"] == "extract" && event["revision"] == "base")
        );
        assert!(
            events
                .iter()
                .any(|event| event["stage"] == "stage_progress")
        );
        std::thread::sleep(Duration::from_millis(5));
        assert_eq!(fs::read_to_string(path).unwrap(), text);
    }
}
