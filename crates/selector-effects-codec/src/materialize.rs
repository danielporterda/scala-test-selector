use crate::*;
use std::mem::size_of;

/// Explicit one-time decoded columns. Both the checked wire owner and the DTO
/// stay alive together; there is no API detaching a DTO from its provenance.
pub struct Materialized {
    wire: VerifiedCapsules,
    capsules: Capsules,
    transport_bytes: usize,
    owned_bytes: usize,
}
impl Materialized {
    pub fn wire(&self) -> &VerifiedCapsules {
        &self.wire
    }
    pub fn capsules(&self) -> &Capsules {
        &self.capsules
    }
    /// Add this to Capsules::owned_bytes when charging a planner World.
    pub fn transport_bytes(&self) -> usize {
        self.transport_bytes
    }
    pub fn owned_bytes(&self) -> usize {
        self.owned_bytes
    }
}

impl VerifiedCapsules {
    /// Conservative retained wire charge, including the artifact's 33 fixed
    /// section-directory records and this wrapper. The transport's private
    /// section metadata is scalar-only and below 128 bytes per entry in the
    /// current pinned selector-artifacts implementation. This allowance is
    /// deliberately above that layout; production should expose its own ledger.
    /// Mapped owners are also charged their entire wire length conservatively.
    pub fn transport_bytes(&self) -> Result<usize, Error> {
        self.byte_len()
            .checked_add(SECTIONS * 128)
            .and_then(|n| n.checked_add(size_of::<Self>()))
            .ok_or(Error::Limit("wire owner charge"))
    }
    pub fn minimum_materialized_bytes(&self) -> Result<usize, Error> {
        let mut bytes = self.transport_bytes()?;
        macro_rules! charge{($($count:ident:$ty:ty),+$(,)?)=>{$(bytes=bytes.checked_add(self.$count().checked_mul(size_of::<$ty>()).ok_or(Error::Limit("decoded column bytes"))?).ok_or(Error::Limit("materialized bytes"))?;)+};}
        charge!(method_count:MethodRow,call_count:CallRow,origin_count:Origin,code_observation_count:CodeRef,read_count:StorageRef,write_count:StorageRef,escape_count:EscapeRef,initialize_count:MethodId,throw_count:u32,synchronize_count:SyncRef,external_count:ExternalRef,flow_count:FlowRef,callable_value_count:ValueRef,sam_count:u32,creation_count:CallableCreation,value_flow_count:ValueFlow,callable_bridge_count:CallableBridge);
        Ok(bytes)
    }
    /// Materialization is optional and explicitly charged. Check the combined
    /// wire+key-metadata+column-capacity budget before allocating any column;
    /// reserve once per flat column, recheck actual capacities, then fill.
    pub fn materialize(
        self,
        limits: selector_effects::Limits,
        max_owned_bytes: usize,
    ) -> Result<Materialized, Error> {
        let transport_bytes = self.transport_bytes()?;
        let minimum = self.minimum_materialized_bytes()?;
        let mut rows = 0usize;
        for n in [
            self.method_count(),
            self.call_count(),
            self.origin_count(),
            self.code_observation_count(),
            self.read_count(),
            self.write_count(),
            self.escape_count(),
            self.initialize_count(),
            self.throw_count(),
            self.synchronize_count(),
            self.external_count(),
            self.flow_count(),
            self.callable_value_count(),
            self.sam_count(),
            self.creation_count(),
            self.value_flow_count(),
            self.callable_bridge_count(),
        ] {
            rows = rows
                .checked_add(n)
                .ok_or(Error::Limit("materialized rows"))?;
        }
        if minimum > max_owned_bytes
            || minimum - transport_bytes > limits.max_bytes
            || rows > limits.max_rows
            || self.method_count() > limits.max_methods
        {
            return Err(Error::Limit("materialization preflight"));
        }
        let mut data = CapsuleData::default();
        macro_rules! reserve{($($field:ident:$count:ident),+$(,)?)=>{$(data.$field.try_reserve_exact(self.$count()).map_err(|_|Error::Limit("decoded column capacity"))?;)+};}
        reserve!(methods:method_count,calls:call_count,origins:origin_count,code_observations:code_observation_count,reads:read_count,writes:write_count,escapes:escape_count,initializes:initialize_count,throws:throw_count,synchronizes:synchronize_count,external:external_count,flows:flow_count,callable_values:callable_value_count,sam_arities:sam_count,creations:creation_count,value_flows:value_flow_count,callable_bridges:callable_bridge_count);
        let columns = data
            .owned_bytes()
            .map_err(|_| Error::Limit("decoded capacity charge"))?;
        let owned_bytes = transport_bytes
            .checked_add(columns)
            .ok_or(Error::Limit("materialized capacity charge"))?;
        if columns > limits.max_bytes || owned_bytes > max_owned_bytes {
            return Err(Error::Limit("materialized capacity admission"));
        }
        macro_rules! fill{($($field:ident:$count:ident:$get:ident),+$(,)?)=>{$(for i in 0..self.$count(){data.$field.push(self.$get(i).ok_or(Error::Invalid("admitted scalar changed during materialization"))?);})+};}
        fill!(methods:method_count:method,calls:call_count:call,origins:origin_count:origin,code_observations:code_observation_count:code_observation,reads:read_count:read,writes:write_count:write,escapes:escape_count:escape,initializes:initialize_count:initialize,throws:throw_count:r#throw,synchronizes:synchronize_count:synchronize,external:external_count:external,flows:flow_count:flow,callable_values:callable_value_count:callable_value,sam_arities:sam_count:sam_arity,creations:creation_count:creation,value_flows:value_flow_count:value_flow,callable_bridges:callable_bridge_count:callable_bridge);
        let capsules = Capsules::new(data, self.bounds, limits)
            .map_err(|_| Error::Invalid("materialized effect contract"))?;
        Ok(Materialized {
            wire: self,
            capsules,
            transport_bytes,
            owned_bytes,
        })
    }
}
