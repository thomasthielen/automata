#![allow(missing_docs)]

use tracing::{trace, warn};

mod error;
pub use error::HoaError;

pub mod input;
pub use input::{
    HoaAutomatonStream, IntoDeterministicHoaAutomatonStream, NoneterministicHoaAutomatonStream,
    dcw_from_hoa, ncw_from_hoa,
};

pub mod output;
pub use output::WriteHoa;

pub use hoars::*;

use crate::alphabet::PropAlphabet;

pub type HoaAutomaton<const DET: bool> = crate::automaton::OmegaAutomaton<PropAlphabet, DET>;

#[derive(Debug, Clone, Eq, PartialEq)]
pub struct HoaString(pub(crate) String);

impl HoaString {
    pub fn into_inner(self) -> String {
        self.0
    }

    pub fn pop<const DET: bool>(&mut self) -> Option<HoaAutomaton<DET>> {
        const END_LEN: usize = "--END--".len();
        const ABORT_LEN: usize = "--ABORT--".len();

        loop {
            match (self.0.find("--ABORT--"), self.0.find("--END--")) {
                (None, Some(pos)) => {
                    trace!("Returnting first automaton, going up to position {pos}");
                    match input::parse_omega_automaton_range(&self.0, 0, pos + END_LEN) {
                        Ok(aut) => return Some(aut),
                        Err(e) => {
                            warn!("Could not parse automaton, skipping... {:?}", e);
                            self.0 = self.0[pos + END_LEN..].trim_start().to_string();
                        }
                    }
                }
                (Some(abort), None) => {
                    trace!(
                        "Found only one automaton --ABORT--ed at {abort}, but no subsequent --END-- of automaton to parse."
                    );
                    return None;
                }
                (Some(abort), Some(end)) => {
                    if abort < end {
                        trace!(
                            "Found --ABORT-- before --END--, returning first automaton from {abort} to {end}"
                        );
                        match input::parse_omega_automaton_range(
                            &self.0,
                            abort + ABORT_LEN,
                            end + END_LEN,
                        ) {
                            Ok(aut) => return Some(aut),
                            Err(e) => {
                                warn!("Could not parse automaton, skipping... {:?}", e);
                                self.0 = self.0[end + END_LEN..].trim_start().to_string();
                            }
                        }
                    } else {
                        trace!("Found --END--, returning first automaton up to {end}");
                        match input::parse_omega_automaton_range(&self.0, 0, end + END_LEN) {
                            Ok(aut) => return Some(aut),
                            Err(e) => {
                                warn!("Could not parse automaton, skipping... {:?}", e);
                                self.0 = self.0[end + END_LEN..].trim_start().to_string();
                            }
                        }
                    }
                }
                (None, None) => {
                    trace!("No end of automaton found, there is no automaton to parse.");
                    return None;
                }
            }
        }
    }
}

impl std::ops::Deref for HoaString {
    type Target = String;

    fn deref(&self) -> &Self::Target {
        &self.0
    }
}
impl std::ops::DerefMut for HoaString {
    fn deref_mut(&mut self) -> &mut Self::Target {
        &mut self.0
    }
}
impl std::borrow::Borrow<str> for HoaString {
    fn borrow(&self) -> &str {
        self.0.as_str()
    }
}
impl From<String> for HoaString {
    fn from(value: String) -> Self {
        Self(value)
    }
}
impl From<HoaString> for String {
    fn from(value: HoaString) -> Self {
        value.0
    }
}

#[cfg(test)]
mod tests {
    use crate::{TransitionSystem, hoa::input::hoa_to_ts};

    #[test]
    fn parse_generated_hoa() {
        let hoa = r#"HOA: v1
        States: 10
        Start: 0
        AP: 3 "2" "a" "b"
        acc-name: parity min even 5
        Acceptance: 5 Inf(0) | (Fin(1) & (Inf(2) | (Fin(3) & Inf(4))))
        properties: trans-labels explicit-labels trans-acc complete
        properties: deterministic
        --BODY--
        State: 0
        [0&1] 4
        [0&!1] 8
        [!0] 6 {0}
        State: 1
        [!0&1&2] 7 {0}
        [!0&1&!2] 3 {4}
        [!0&!1&2] 4 {0 4}
        [!0&!1&!2] 9 {0}
        [0] 5 {0 4}
        State: 2
        [0&1&2] 2 {0 4}
        [0&1&!2] 6 {3}
        [0&!1&2] 1 {1}
        [0&!1&!2] 4 {1}
        [!0] 7
        State: 3
        [0&1] 0 {2}
        [0&!1] 2
        [!0&1] 4 {3 4}
        [!0&!1] 6 {1 2}
        State: 4
        [0&1] 0 {3}
        [0&!1] 6 {1}
        [!0&1] 7 {0}
        [!0&!1] 4
        State: 5
        [0&1] 9
        [0&!1] 2
        [!0] 4
        State: 6
        [0&1] 9 {4}
        [0&!1] 0 {2}
        [!0&1] 6 {2 3}
        [!0&!1] 4 {0}
        State: 7
        [0&!1&2] 8 {4}
        [0&!1&!2] 1 {4}
        [0&1] 2 {1}
        [!0] 4 {2}
        State: 8
        [!0&1] 2
        [!0&!1] 6
        [0] 4
        State: 9
        [0] 5
        [!0] 3
        --END--
        "#;
        let auts = hoa_to_ts(hoa);
        assert_eq!(auts.len(), 1);
        let aut = &auts[0];
        assert_eq!(aut.size(), 10);
    }
}
