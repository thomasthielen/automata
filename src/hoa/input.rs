use std::{io::BufRead, ops::Deref};

use crate::automaton::{
    AcceptanceMask, DCW, DeterministicOmegaAutomaton, NCW, OmegaAcceptanceCondition, OmegaAutomaton,
};
use crate::ts::{ForAlphabet, Sproutable, TransitionSystem};
use crate::{
    Int, NTS, Void,
    alphabet::{CharAlphabet, PropAlphabet, PropExpression},
};
use biodivine_lib_bdd::BddValuation;
use hoars::{
    AbstractLabelExpression, AcceptanceName, HeaderItem, HoaRepresentation, LabelExpression,
};
use tracing::{trace, warn};

use super::{HoaError, HoaString};

#[derive(Debug, Clone, Eq, PartialEq)]
pub struct IntoDeterministicHoaAutomatonStream<R> {
    base: HoaAutomatonStream<R, false>,
}

impl<R> IntoDeterministicHoaAutomatonStream<R> {
    pub fn new(read: R) -> IntoDeterministicHoaAutomatonStream<R> {
        Self {
            base: HoaAutomatonStream::new(read),
        }
    }
}

impl<R: BufRead> Iterator for IntoDeterministicHoaAutomatonStream<R> {
    type Item = DeterministicOmegaAutomaton<PropAlphabet>;

    fn next(&mut self) -> Option<Self::Item> {
        loop {
            {
                let aut = self.base.next()?;
                if let Ok(det) = aut.try_into_deterministic() {
                    return Some(det);
                } else {
                    warn!("Encountered automaton that is not deterministic, skipping...")
                }
            }
        }
    }
}

pub type NoneterministicHoaAutomatonStream<R> = HoaAutomatonStream<R, false>;

#[derive(Debug, Clone, Eq, PartialEq)]
pub struct HoaAutomatonStream<R, const DET: bool = true> {
    read: R,
    buf: String,
    pos: usize,
}

impl<R: BufRead, const DET: bool> Iterator for HoaAutomatonStream<R, DET> {
    type Item = OmegaAutomaton<PropAlphabet, DET>;

    fn next(&mut self) -> Option<Self::Item> {
        loop {
            match self.read.read_line(&mut self.buf) {
                Ok(0) => return None,
                Ok(read_bytes) => {
                    if self.buf[self.pos..].contains("--ABORT--") {
                        trace!("encountered --ABORT-- in stream, resetting");
                        self.buf.clear();
                        self.pos = 0;
                        continue;
                    }

                    if self.buf[self.pos..].contains("--END--") {
                        let end = self.pos + "--END--".len();
                        trace!(
                            "encountered --END-- in stream, attempting to parse automaton \n{}",
                            &self.buf[..end]
                        );
                        let aut: Result<OmegaAutomaton<PropAlphabet, DET>, _> =
                            parse_omega_automaton_range(&self.buf, 0, end);
                        self.buf.clear();
                        self.pos = 0;

                        match aut {
                            Err(e) => {
                                warn!(
                                    "Encountered automaton that could not be parsed, skipping... {:?}",
                                    e
                                );
                            }
                            Ok(aut) => {
                                assert!(!DET || aut.ts().is_deterministic(), "type error");
                                return Some(aut);
                            }
                        }
                    }

                    self.pos += read_bytes;
                }
                Err(_e) => return None,
            }
        }
    }
}

impl<R, const DET: bool> HoaAutomatonStream<R, DET> {
    pub fn new(read: R) -> Self {
        Self {
            read,
            pos: 0,
            buf: String::new(),
        }
    }
}

pub fn parse_omega_automaton_range<const DET: bool>(
    hoa: &str,
    start: usize,
    end: usize,
) -> Result<OmegaAutomaton<PropAlphabet, DET>, HoaError> {
    let in_range = |source: HoaError| HoaError::InRange {
        start,
        end,
        source: Box::new(source),
    };
    let aut = HoaRepresentation::try_from(&hoa[start..end]).map_err(|e| in_range(e.into()))?;
    OmegaAutomaton::try_from(aut).map_err(in_range)
}

pub fn pop_deterministic_omega_automaton(
    hoa: HoaString,
) -> Option<(DeterministicOmegaAutomaton<PropAlphabet>, HoaString)> {
    pop_omega_automaton(hoa)
}

/// Tries to `pop` the foremost valid HOA automaton from the given [`HoaString`].
/// If no valid automaton is found before the end of the stream is reached, the
/// function returns `None`.
pub fn pop_omega_automaton<const DET: bool>(
    hoa: HoaString,
) -> Option<(OmegaAutomaton<PropAlphabet, DET>, HoaString)> {
    let mut hoa = hoa;
    const END_LEN: usize = "--END--".len();
    const ABORT_LEN: usize = "--ABORT--".len();

    loop {
        match (hoa.0.find("--ABORT--"), hoa.0.find("--END--")) {
            (None, Some(pos)) => {
                trace!("Returnting first automaton, going up to position {pos}");
                match parse_omega_automaton_range(&hoa.0, 0, pos + END_LEN) {
                    Ok(aut) => {
                        return Some((
                            aut,
                            HoaString(hoa.0[pos + END_LEN..].trim_start().to_string()),
                        ));
                    }
                    Err(e) => {
                        warn!("Could not parse automaton, skipping... {:?}", e);
                        hoa = HoaString(hoa.0[pos + END_LEN..].trim_start().to_string());
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
                    match parse_omega_automaton_range(&hoa.0, abort + ABORT_LEN, end + END_LEN) {
                        Ok(aut) => {
                            return Some((
                                aut,
                                HoaString(hoa.0[end + END_LEN..].trim_start().to_string()),
                            ));
                        }
                        Err(e) => {
                            warn!("Could not parse automaton, skipping... {:?}", e);
                            hoa = HoaString(hoa.0[end + END_LEN..].trim_start().to_string());
                        }
                    }
                } else {
                    trace!("Found --END--, returning first automaton up to {end}");
                    match parse_omega_automaton_range(&hoa.0, 0, end + END_LEN) {
                        Ok(aut) => {
                            return Some((
                                aut,
                                HoaString(hoa.0[end + END_LEN..].trim_start().to_string()),
                            ));
                        }
                        Err(e) => {
                            warn!("Could not parse automaton, skipping... {:?}", e);
                            hoa = HoaString(hoa.0[end + END_LEN..].trim_start().to_string());
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

/// Considers the given HOA string as a single automaton and tries to parse it into an
/// [`OmegaAutomaton`].
pub fn hoa_to_ts<const DET: bool>(hoa: &str) -> Vec<OmegaAutomaton<PropAlphabet, DET>> {
    let mut out = vec![];
    for hoa_aut in hoars::parse_hoa_automata(hoa) {
        match hoa_aut.try_into() {
            Ok(aut) => out.push(aut),
            Err(e) => tracing::warn!("Encountered parsing error {}", e),
        }
    }
    out
}

impl TryFrom<&hoars::Header> for OmegaAcceptanceCondition {
    type Error = HoaError;

    fn try_from(value: &hoars::Header) -> Result<Self, Self::Error> {
        let acceptance_sets = value.iter().find_map(|it| match it {
            hoars::HeaderItem::Acceptance(acceptance, _cond) => Some(*acceptance),
            _ => None,
        });
        let name = value
            .iter()
            .find_map(|it| it.try_acceptance_name())
            .ok_or_else(|| HoaError::UnsupportedAcceptance("missing acc-name".to_string()))?;

        match name.0 {
            hoars::AcceptanceName::Buchi => Ok(OmegaAcceptanceCondition::Buchi),
            hoars::AcceptanceName::CoBuchi => Ok(OmegaAcceptanceCondition::CoBuchi),
            hoars::AcceptanceName::Parity => {
                let sets = acceptance_sets.ok_or(HoaError::MissingAcceptanceSets)?;
                Ok(OmegaAcceptanceCondition::Parity(0, sets as Int))
            }
            other => Err(HoaError::UnsupportedAcceptance(format!("{other:?}"))),
        }
    }
}

impl<const DET: bool> TryFrom<HoaRepresentation> for OmegaAutomaton<PropAlphabet, DET> {
    type Error = HoaError;
    fn try_from(value: HoaRepresentation) -> Result<Self, Self::Error> {
        hoa_automaton_to_ts(value)
    }
}

/// Converts a [`HoaRepresentation`] into a [`crate::NTS`] with the same semantics. This creates the appropriate
/// number of states and inserts transitions with the appropriate labels and colors.
pub fn hoa_automaton_to_ts<const DET: bool>(
    aut: HoaRepresentation,
) -> Result<OmegaAutomaton<PropAlphabet, DET>, HoaError> {
    let aps = aut.num_aps();
    assert!(aps <= crate::hoa::MAX_APS);

    let alphabet = PropAlphabet::from_apnames(aut.aps().iter());
    let mut ts: crate::TS<PropAlphabet, Int, AcceptanceMask, DET> =
        crate::TS::for_alphabet(alphabet);

    for (id, state) in aut.body().iter().enumerate() {
        assert_eq!(id, state.id() as usize);
        assert_eq!(id, ts.add_state(state.id() as Int) as usize);
    }

    for state in aut.body().iter() {
        for edge in state.edges() {
            let target = edge
                .state_conjunction()
                .get_singleton()
                .expect("Cannot yet deal with conjunctions of target states");
            let label = edge.label().deref().clone();

            let expr = label
                .try_into_hoa_expression(aps)
                .map_err(HoaError::InvalidLabel)?;
            let color: AcceptanceMask = edge.acceptance_signature().into();

            if ts
                .add_edge((state.id(), PropExpression::from_bdd(expr), color, target))
                .is_some()
            {
                // this thing is not deterministic, so we return
                if DET {
                    warn!("rejecting nondeterministic automaton");
                    return Err(HoaError::NotDeterministic);
                }
            }
        }
    }

    debug_assert!(!DET || ts.is_deterministic());

    let start = aut.start();
    assert_eq!(start.len(), 1);
    let initial = start[0]
        .get_singleton()
        .expect("Initial state must be a singleton");

    let acceptance: OmegaAcceptanceCondition = aut.header().try_into()?;

    Ok(OmegaAutomaton::from_parts_with_acceptance(
        ts, initial, acceptance,
    ))
}

/// Reads a tNCW from `hoa`, with the letters encoded *one-hot* as [`super::WriteHoa`] writes
/// them for a [`CharAlphabet`]: every atomic proposition names a letter, and a letter is
/// read on an edge if the label holds when exactly the proposition of this letter holds.
/// All other valuations are ignored, so the labels may be arbitrary boolean expressions,
/// such as the merged labels that [Spot](https://spot.lre.epita.fr/) writes. The state ids
/// of `hoa` become the state indices.
///
/// # Errors
/// Returns a [`HoaError`] if `hoa` is not a valid HOA automaton, if its acceptance
/// condition is not `co-Buchi` (as `acc-name`), if an atomic proposition does not name a
/// single letter, or if it uses alternation or does not have exactly one initial state.
///
/// # Example
/// ```
/// use automata::automaton::NCW;
/// use automata::hoa::{WriteHoa, ncw_from_hoa};
/// use automata::{Pointed, TransitionSystem};
///
/// let ncw = NCW::builder()
///     .with_edges([(0, 'a', false, 0), (0, 'a', true, 1), (1, 'b', false, 1)])
///     .into_ncw(0);
/// let read = ncw_from_hoa(&ncw.to_hoa()).unwrap();
/// assert_eq!(read.size(), 2);
/// assert_eq!(read.initial(), 0);
/// // the nondeterministic choice on `a` in state 0 is kept
/// assert!(read.try_into_dcw().is_err());
/// ```
pub fn ncw_from_hoa(hoa: &str) -> Result<NCW, HoaError> {
    let aut = HoaRepresentation::try_from(hoa)?;
    let header = aut.header();

    match header.iter().find_map(|it| it.try_acceptance_name()) {
        Some((AcceptanceName::CoBuchi, _)) => {}
        other => {
            return Err(HoaError::UnsupportedAcceptance(format!(
                "{:?}, expected co-Buchi",
                other.map(|(name, _)| name)
            )));
        }
    }

    let aps = header
        .iter()
        .find_map(|it| match it {
            HeaderItem::AP(aps) => Some(aps.as_slice()),
            _ => None,
        })
        .unwrap_or_default();
    let mut letters = Vec::with_capacity(aps.len());
    for ap in aps {
        let mut chars = ap.chars();
        match (chars.next(), chars.next()) {
            (Some(letter), None) if !letters.contains(&letter) => letters.push(letter),
            _ => return Err(HoaError::InvalidApName(ap.clone())),
        }
    }

    let states = header
        .count_states()
        .or_else(|| aut.body().iter().map(|q| q.id() as usize + 1).max())
        .unwrap_or(0);
    let mut ts = NTS::for_alphabet(CharAlphabet::new(letters.clone()));
    let ids: Vec<_> = (0..states).map(|_| ts.add_state(Void)).collect();
    let state = |id: hoars::Id| {
        ids.get(id as usize)
            .copied()
            .ok_or(HoaError::Unsupported("reference to an undeclared state"))
    };

    for q in aut.body() {
        let source = state(q.id())?;
        for edge in q.edges() {
            let target = edge
                .state_conjunction()
                .get_singleton()
                .ok_or(HoaError::Unsupported("alternation"))?;
            let target = state(target)?;
            let color = match edge.acceptance_signature()[..] {
                [] => false,
                [0] => true,
                ref other => {
                    return Err(HoaError::UnsupportedAcceptance(format!(
                        "acceptance signature {other:?} in a co-Büchi automaton"
                    )));
                }
            };
            for (position, &letter) in letters.iter().enumerate() {
                if one_hot_satisfies(edge.label(), position, letters.len()) {
                    ts.add_edge((source, letter, color, target));
                }
            }
        }
    }

    let initial = match aut.start()[..] {
        [initial] => initial
            .get_singleton()
            .ok_or(HoaError::Unsupported("alternation"))?,
        _ => return Err(HoaError::Unsupported("not exactly one initial state")),
    };
    Ok(NCW::from_parts(ts, state(initial)?))
}

/// Reads a tDCW from `hoa`, see [`ncw_from_hoa`].
///
/// # Errors
/// Returns [`HoaError::NotDeterministic`] if the automaton is not deterministic, and otherwise
/// the errors of [`ncw_from_hoa`].
pub fn dcw_from_hoa(hoa: &str) -> Result<DCW, HoaError> {
    ncw_from_hoa(hoa)?
        .try_into_dcw()
        .map_err(|_| HoaError::NotDeterministic)
}

/// Evaluates `label` under the valuation of `aps` atomic propositions in which exactly the
/// proposition `position` holds.
fn one_hot_satisfies(label: &LabelExpression, position: usize, aps: usize) -> bool {
    fn eval(expr: &AbstractLabelExpression, position: usize) -> bool {
        match expr {
            AbstractLabelExpression::Boolean(b) => *b,
            AbstractLabelExpression::Integer(ap) => *ap as usize == position,
            AbstractLabelExpression::Negated(expr) => !eval(expr, position),
            AbstractLabelExpression::Conjunction(exprs) => exprs.iter().all(|e| eval(e, position)),
            AbstractLabelExpression::Disjunction(exprs) => exprs.iter().any(|e| eval(e, position)),
        }
    }

    match label {
        LabelExpression::Abstract(expr) => eval(expr, position),
        LabelExpression::Expression(bdd) => bdd.eval_in(&BddValuation::new(
            (0..aps).map(|i| i == position).collect(),
        )),
    }
}

#[cfg(test)]
mod tests {
    use tracing::debug;

    use super::HoaError;
    use crate::{TransitionSystem, hoa::HoaString};

    #[test]
    fn hoa_tdba_with_abort_and_nondeterministic() {
        let raw_hoa = r#"
        HOA: v1
        States: 3
        Start: 0
        acc-name: Buchi
        Acceptance: 1 Inf(0)
        AP: 1 "a"
        --BODY--
        State: 0
        [0] 1
        --ABORT--
        HOA: v1
        States: 2
        Start: 0
        acc-name: Buchi
        Acceptance: 1 Inf(0)
        AP: 1 "a"
        --BODY--
        State: 0
        [0] 0 {0}
        [!0] 0
        State: 1
        [0] 0 {0}
        [0] 1
        [!0] 0
        --END--
        HOA: v1
        States: 1
        Start: 0
        acc-name: Buchi
        Acceptance: 1 Inf(0)
        AP: 1 "a"
        --BODY--
        State: 0
        [0] 0 {0}
        [!0] 0
        --END--
        "#;
        let hoa = HoaString(raw_hoa.to_string());
        debug!("SADF");

        let first = super::pop_deterministic_omega_automaton(hoa);
        assert!(first.is_some());
        let (first, hoa) = first.unwrap();
        assert_eq!(first.size(), 1);
        assert!(hoa.0.is_empty());
    }

    #[test]
    fn parity_without_acceptance_item_is_an_error() {
        let raw_hoa = r#"
        HOA: v1
        States: 1
        Start: 0
        acc-name: parity min even 2
        AP: 1 "a"
        --BODY--
        State: 0
        [0] 0 {0}
        [!0] 0
        --END--
        "#;
        let parsed = hoars::HoaRepresentation::try_from(raw_hoa).expect("valid HOA syntax");
        assert_eq!(
            super::OmegaAcceptanceCondition::try_from(parsed.header()),
            Err(super::HoaError::MissingAcceptanceSets)
        );
    }

    const NONDETERMINISTIC: &str = r#"HOA: v1
States: 2
Start: 0
acc-name: Buchi
Acceptance: 1 Inf(0)
AP: 1 "a"
--BODY--
State: 0
[0] 0 {0}
[0] 1
[!0] 0
State: 1
[t] 1
--END--
"#;

    #[test]
    fn nondeterministic_input_is_rejected_for_deterministic_automata() {
        use super::{HoaError, parse_omega_automaton_range};

        let end = NONDETERMINISTIC.len();
        assert!(parse_omega_automaton_range::<false>(NONDETERMINISTIC, 0, end).is_ok());
        match parse_omega_automaton_range::<true>(NONDETERMINISTIC, 0, end) {
            Err(HoaError::InRange {
                start: 0,
                end: e,
                source,
            }) => {
                assert_eq!(e, end);
                assert_eq!(*source, HoaError::NotDeterministic);
            }
            other => panic!("unexpected result: {:?}", other.map(|_| ())),
        }
    }

    #[test]
    fn invalid_input_reports_a_parse_error() {
        use super::{HoaError, parse_omega_automaton_range};

        let garbage = "HOA: v1\nthis is not an automaton\n--END--";
        match parse_omega_automaton_range::<true>(garbage, 0, garbage.len()) {
            Err(HoaError::InRange { source, .. }) => {
                assert!(matches!(*source, HoaError::Parse(_)));
            }
            other => panic!("unexpected result: {:?}", other.map(|_| ())),
        }
    }

    /// The edges of `aut` as `(source, letter, color, target)`, sorted.
    fn edges<D>(aut: &D) -> Vec<(u32, char, bool, u32)>
    where
        D: TransitionSystem<StateIndex = u32, EdgeColor = bool>,
        D::Alphabet: crate::alphabet::Alphabet<Expression = char>,
    {
        use crate::ts::IsEdge;
        use itertools::Itertools;
        aut.state_indices()
            .flat_map(|q| {
                aut.edges_from(q)
                    .into_iter()
                    .flatten()
                    .map(|e| (e.source(), *e.expression(), e.color(), e.target()))
                    .collect_vec()
            })
            .sorted()
            .collect()
    }

    #[test]
    fn ncw_round_trip() {
        use crate::Pointed;
        use crate::automaton::NCW;
        use crate::hoa::WriteHoa;

        let ncw: NCW = NCW::builder()
            .with_edges([
                (0, 'a', false, 0),
                (0, 'a', true, 1),
                (0, 'c', true, 2),
                (1, 'b', false, 1),
                (1, 'c', true, 0),
                (2, 'a', false, 2),
            ])
            .into_ncw(1);
        let read = super::ncw_from_hoa(&ncw.to_hoa()).unwrap();
        assert_eq!(read.alphabet(), ncw.alphabet());
        assert_eq!(read.initial(), 1);
        assert_eq!(edges(&read), edges(&ncw));
    }

    /// Output of `autfilt -D --sat-minimize='acc="Fin(0)"'` (Spot 2.16.1) for "finitely many
    /// `c`s" over `{a, b, c}`: Spot merges the edges for `a` and `b` into one label.
    const SPOT_DCW: &str = r#"HOA: v1
States: 1
Start: 0
AP: 3 "a" "b" "c"
acc-name: co-Buchi
Acceptance: 1 Fin(0)
properties: trans-labels explicit-labels trans-acc deterministic
--BODY--
State: 0
[!0&1&!2 | 0&!1&!2] 0
[!0&!1&2] 0 {0}
--END--
"#;

    #[test]
    fn dcw_from_spot_output() {
        let dcw = super::dcw_from_hoa(SPOT_DCW).unwrap();
        assert_eq!(dcw.size(), 1);
        assert_eq!(
            edges(&dcw),
            vec![(0, 'a', false, 0), (0, 'b', false, 0), (0, 'c', true, 0)]
        );
    }

    /// Labels that only hold for valuations in which not exactly one proposition holds read no
    /// letter, as Spot may produce them when it completes an automaton.
    #[test]
    fn invalid_valuations_are_ignored() {
        let hoa = SPOT_DCW.replace(
            "[!0&!1&2] 0 {0}",
            "[!0&!1&2] 0 {0}\n[!0&!1&!2 | 0&1 | 0&2 | 1&2] 0 {0}",
        );
        let ncw = super::ncw_from_hoa(&hoa).unwrap();
        assert_eq!(
            edges(&ncw),
            vec![(0, 'a', false, 0), (0, 'b', false, 0), (0, 'c', true, 0)]
        );
    }

    #[test]
    fn co_buchi_import_errors() {
        let buchi = SPOT_DCW
            .replace("acc-name: co-Buchi", "acc-name: Buchi")
            .replace("Fin(0)", "Inf(0)");
        assert!(matches!(
            super::ncw_from_hoa(&buchi),
            Err(HoaError::UnsupportedAcceptance(_))
        ));

        let long_name = SPOT_DCW.replace("\"c\"", "\"cc\"");
        assert_eq!(
            super::ncw_from_hoa(&long_name).map(|_| ()),
            Err(HoaError::InvalidApName("cc".to_string()))
        );

        let nondeterministic = SPOT_DCW.replace("[!0&!1&2] 0 {0}", "[!0&!1&2] 0 {0}\n[2] 0");
        assert!(super::ncw_from_hoa(&nondeterministic).is_ok());
        assert_eq!(
            super::dcw_from_hoa(&nondeterministic).map(|_| ()),
            Err(HoaError::NotDeterministic)
        );
    }

    #[test]
    fn co_buchi_header_is_recognized() {
        let parsed = hoars::HoaRepresentation::try_from(SPOT_DCW).expect("valid HOA syntax");
        assert_eq!(
            super::OmegaAcceptanceCondition::try_from(parsed.header()),
            Ok(super::OmegaAcceptanceCondition::CoBuchi)
        );
    }
}
