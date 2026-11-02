use itertools::Itertools;
use tracing::trace;

use std::collections::HashMap;
use std::fmt::{Result, Write};

use crate::{
    Automaton, Color, Int, Pointed, Show, TransitionSystem,
    alphabet::{Alphabet, CharAlphabet, PropAlphabet},
    automaton::{
        BuchiCondition, CoBuchiCondition, MinEvenParityCondition, OmegaAcceptanceCondition,
    },
    ts::{EdgeColor, IsEdge},
};

use super::HoaError;

/// Writes an automaton in the [HOA format](https://adl.github.io/hoaf/), which tools such as
/// [Spot](https://spot.lre.epita.fr/) read.
///
/// The states are numbered `0..n` in the order of [`TransitionSystem::state_indices`], as HOA
/// requires; after states were removed, these numbers may differ from the state indices of
/// `self`. How the symbols are encoded as atomic propositions is up to the
/// [`HoaSuitableAlphabet`].
pub trait WriteHoa: TransitionSystem<Alphabet: HoaSuitableAlphabet> + Pointed {
    /// Writes the `acc-name` and `Acceptance` header lines.
    fn write_acceptance<W: Write>(&self, w: &mut W) -> Result;

    /// Writes the acceptance signature of an edge with the given color, including the leading
    /// space, or nothing if the edge belongs to no acceptance set.
    fn write_edge_color<W: Write>(&self, w: &mut W, color: EdgeColor<Self>) -> Result;

    /// Writes `self` in the HOA format to `w`.
    fn write_hoa<W: Write>(&self, w: &mut W) -> Result {
        let ids: HashMap<Self::StateIndex, usize> = self
            .state_indices()
            .enumerate()
            .map(|(id, q)| (q, id))
            .collect();
        let id = |q: Self::StateIndex| ids.get(&q).copied().ok_or(std::fmt::Error);

        w.write_str("HOA: v1\n")?;
        self.alphabet().write_alphabet_description(w)?;
        writeln!(w, "States: {}", ids.len())?;
        writeln!(w, "Start: {}", id(self.initial())?)?;
        self.write_acceptance(w)?;
        w.write_str("--BODY--")?;

        for state in self.state_indices() {
            write!(w, "\nState: {}", id(state)?)?;
            for edge in self.edges_from(state).into_iter().flatten() {
                w.write_str("\n[")?;
                self.alphabet().write_expression(w, edge.expression())?;
                write!(w, "] {}", id(edge.target())?)?;
                self.write_edge_color(w, edge.color())?;
            }
        }

        w.write_str("\n--END--\n")
    }

    /// Returns `self` in the HOA format, see [`Self::write_hoa`].
    fn to_hoa(&self) -> String {
        let mut w = String::new();
        // writing into a `String` only fails if the automaton is inconsistent, i.e. its initial
        // state or the target of an edge is not one of its states
        if self.write_hoa(&mut w).is_err() {
            tracing::error!("could not write automaton in HOA format");
        }
        trace!("produced HOA string from automaton\n{}", w);
        w
    }
}

impl OmegaAcceptanceCondition {
    /// Writes the `acc-name` and `Acceptance` header lines for `self`. A parity condition
    /// `Parity(_, high)` is written as `parity min even` over the acceptance sets `0..=high`.
    ///
    /// # Errors
    /// Returns [`HoaError::UnsupportedAcceptance`] for conditions other than Büchi, co-Büchi and
    /// (min even) parity, and [`HoaError::Format`] if `w` fails.
    pub fn write_hoa<W: Write>(&self, w: &mut W) -> std::result::Result<(), HoaError> {
        match self {
            OmegaAcceptanceCondition::Buchi => write_buchi_acceptance(w)?,
            OmegaAcceptanceCondition::CoBuchi => write_co_buchi_acceptance(w)?,
            OmegaAcceptanceCondition::Parity(_, high) => write_parity_acceptance(w, *high)?,
            other => return Err(HoaError::UnsupportedAcceptance(format!("{other:?}"))),
        }
        Ok(())
    }
}

fn write_buchi_acceptance<W: Write>(w: &mut W) -> Result {
    w.write_str("acc-name: Buchi\nAcceptance: 1 Inf(0)\n")
}

fn write_co_buchi_acceptance<W: Write>(w: &mut W) -> Result {
    w.write_str("acc-name: co-Buchi\nAcceptance: 1 Fin(0)\n")
}

/// Writes a `parity min even` condition over the acceptance sets `0..=high`, so that every
/// priority up to `high` can be used directly as the acceptance set of an edge.
fn write_parity_acceptance<W: Write>(w: &mut W, high: Int) -> Result {
    let sets = high + 1;
    write!(
        w,
        "acc-name: parity min even {sets}\nAcceptance: {sets} {}\n",
        build_parity_condition_hoa(0, high)
    )
}

/// Writes the acceptance signature `{0}` for edges colored `true`, and nothing otherwise.
fn write_bool_edge_color<W: Write>(w: &mut W, color: bool) -> Result {
    if color { w.write_str(" {0}") } else { Ok(()) }
}

/// An [`Alphabet`] whose symbols and expressions can be encoded as atomic propositions.
pub trait HoaSuitableAlphabet: Alphabet {
    /// Writes the given expression as an HOA label (without the brackets).
    fn write_expression<W: Write>(&self, w: &mut W, expr: &Self::Expression) -> Result;
    /// Writes the `AP` header line.
    fn write_alphabet_description<W: Write>(&self, w: &mut W) -> Result;
}

impl<A, Q, D> WriteHoa for Automaton<A, BuchiCondition, Q, bool, D, true>
where
    A: HoaSuitableAlphabet,
    Q: Color,
    D: TransitionSystem<Alphabet = A, StateColor = Q, EdgeColor = bool>,
{
    fn write_acceptance<W: Write>(&self, w: &mut W) -> Result {
        write_buchi_acceptance(w)
    }

    fn write_edge_color<W: Write>(&self, w: &mut W, color: bool) -> Result {
        write_bool_edge_color(w, color)
    }
}

/// Written with `Acceptance: 1 Fin(0)`, the `α`-transitions (colored `true`) form the acceptance
/// set `0`. This covers both [`crate::automaton::DCW`] and [`crate::automaton::NCW`].
impl<A, Q, D> WriteHoa for Automaton<A, CoBuchiCondition, Q, bool, D, true>
where
    A: HoaSuitableAlphabet,
    Q: Color,
    D: TransitionSystem<Alphabet = A, StateColor = Q, EdgeColor = bool>,
{
    fn write_acceptance<W: Write>(&self, w: &mut W) -> Result {
        write_co_buchi_acceptance(w)
    }

    fn write_edge_color<W: Write>(&self, w: &mut W, color: bool) -> Result {
        write_bool_edge_color(w, color)
    }
}

/// Written as `parity min even` over the acceptance sets `0..=p`, where `p` is the greatest
/// priority, so that the priority of an edge is its acceptance set.
impl<A, Q, D> WriteHoa for Automaton<A, MinEvenParityCondition, Q, Int, D, true>
where
    A: HoaSuitableAlphabet,
    Q: Color,
    D: TransitionSystem<Alphabet = A, StateColor = Q, EdgeColor = Int>,
{
    fn write_acceptance<W: Write>(&self, w: &mut W) -> Result {
        let high = self
            .state_indices()
            .flat_map(|q| self.edges_from(q).into_iter().flatten())
            .map(|edge| edge.color())
            .max()
            .unwrap_or(0);
        write_parity_acceptance(w, high)
    }

    fn write_edge_color<W: Write>(&self, w: &mut W, color: Int) -> Result {
        write!(w, " {{{color}}}")
    }
}

/// Encodes the letters *one-hot*: the `i`-th letter becomes the atomic proposition `i`, named
/// after the letter, and reading it means that exactly this proposition holds. Valuations in
/// which not exactly one proposition holds have no edges, so they are rejected. This works for
/// every alphabet size; [`super::ncw_from_hoa`] reads the encoding back.
impl HoaSuitableAlphabet for CharAlphabet {
    fn write_alphabet_description<W: Write>(&self, w: &mut W) -> Result {
        write!(w, "AP: {}", self.size())?;
        for letter in self.universe() {
            w.write_str(" \"")?;
            if matches!(letter, '"' | '\\') {
                w.write_char('\\')?;
            }
            w.write_char(letter)?;
            w.write_char('"')?;
        }
        w.write_char('\n')
    }

    fn write_expression<W: Write>(&self, w: &mut W, expr: &Self::Expression) -> Result {
        let position = self.universe().position(|letter| letter == *expr);
        let position = position.ok_or(std::fmt::Error)?;
        write!(
            w,
            "{}",
            (0..self.size())
                .map(|i| if i == position {
                    format!("{i}")
                } else {
                    format!("!{i}")
                })
                .join(" & ")
        )
    }
}

impl HoaSuitableAlphabet for PropAlphabet {
    fn write_alphabet_description<W: Write>(&self, w: &mut W) -> Result {
        writeln!(
            w,
            "AP: {} {}",
            self.aps(),
            self.apnames()
                .iter()
                .map(|name| format!("\"{}\"", name))
                .join(" ")
        )
    }

    fn write_expression<W: Write>(&self, w: &mut W, expr: &Self::Expression) -> Result {
        write!(w, "{}", expr.show())
    }
}

/// Builds the `parity min even` condition over the acceptance sets `low..=high`, where `low`
/// is even for the usual condition. For `high < low`, the condition is trivial.
fn build_parity_condition_hoa(low: Int, high: Int) -> String {
    let even = low.is_multiple_of(2);

    if high < low {
        return if even { "t" } else { "f" }.to_string();
    }

    match (high - low, even) {
        (0, true) => format!("Inf({low})"),
        (0, false) => format!("Fin({low})"),
        (1, true) => format!("Inf({low}) | Fin({high})"),
        (1, false) => format!("Fin({low}) & Inf({high})"),
        (_, true) => format!(
            "Inf({low}) | ({})",
            build_parity_condition_hoa(low + 1, high)
        ),
        (_, false) => format!(
            "Fin({low}) & ({})",
            build_parity_condition_hoa(low + 1, high)
        ),
    }
}

#[cfg(test)]
mod tests {
    use super::WriteHoa;
    use crate::automaton::{DCW, NCW, OmegaAcceptanceCondition};
    use crate::hoa::HoaError;
    use crate::ts::{Shrinkable, TSBuilder};

    #[test]
    fn build_parity_hoa_string() {
        assert_eq!(super::build_parity_condition_hoa(0, 0), "Inf(0)");
        assert_eq!(super::build_parity_condition_hoa(0, 1), "Inf(0) | Fin(1)");
        assert_eq!(
            super::build_parity_condition_hoa(0, 2),
            "Inf(0) | (Fin(1) & Inf(2))"
        );
        assert_eq!(
            super::build_parity_condition_hoa(0, 4),
            "Inf(0) | (Fin(1) & (Inf(2) | (Fin(3) & Inf(4))))"
        );
    }

    #[test]
    fn write_hoa_dpa() {
        let dpa = TSBuilder::without_state_colors()
            .with_edges([(0, 'a', 0, 0), (0, 'b', 1, 0), (0, 'c', 2, 0)])
            .into_dpa(0);
        let hoa = dpa.to_hoa();
        assert_eq!(
            hoa,
            "HOA: v1\nAP: 3 \"a\" \"b\" \"c\"\nStates: 1\nStart: 0\nacc-name: parity min even 3\nAcceptance: 3 Inf(0) | (Fin(1) & Inf(2))\n--BODY--\nState: 0\n[0 & !1 & !2] 0 {0}\n[!0 & 1 & !2] 0 {1}\n[!0 & !1 & 2] 0 {2}\n--END--\n"
        );
    }

    /// Priorities that do not start at 0 still need all acceptance sets up to the greatest one.
    #[test]
    fn write_hoa_dpa_without_low_priorities() {
        let dpa = TSBuilder::without_state_colors()
            .with_edges([(0, 'a', 1, 0), (0, 'b', 3, 0)])
            .into_dpa(0);
        let hoa = dpa.to_hoa();
        assert!(hoa.contains(
            "acc-name: parity min even 4\nAcceptance: 4 Inf(0) | (Fin(1) & (Inf(2) | Fin(3)))\n"
        ));
        assert!(hoa.contains("[0 & !1] 0 {1}\n[!0 & 1] 0 {3}\n"));
    }

    #[test]
    fn write_hoa_dba() {
        let dba = TSBuilder::without_state_colors()
            .with_edges([(0, 'a', true, 0), (0, 'b', false, 0), (0, 'c', true, 0)])
            .into_dba(0);
        let hoa = dba.to_hoa();
        assert_eq!(
            hoa,
            "HOA: v1\nAP: 3 \"a\" \"b\" \"c\"\nStates: 1\nStart: 0\nacc-name: Buchi\nAcceptance: 1 Inf(0)\n--BODY--\nState: 0\n[0 & !1 & !2] 0 {0}\n[!0 & 1 & !2] 0\n[!0 & !1 & 2] 0 {0}\n--END--\n"
        );
    }

    #[test]
    fn write_hoa_dcw() {
        let dcw = DCW::builder()
            .with_edges([
                (0, 'a', false, 0),
                (0, 'b', true, 1),
                (1, 'a', false, 1),
                (1, 'b', true, 0),
            ])
            .into_dcw(0);
        assert_eq!(
            dcw.to_hoa(),
            "HOA: v1\nAP: 2 \"a\" \"b\"\nStates: 2\nStart: 0\nacc-name: co-Buchi\nAcceptance: 1 Fin(0)\n--BODY--\nState: 0\n[0 & !1] 0\n[!0 & 1] 1 {0}\nState: 1\n[0 & !1] 1\n[!0 & 1] 0 {0}\n--END--\n"
        );
    }

    /// A nondeterministic tNCW is written with several edges per letter, and after removing a
    /// state the remaining states are renumbered without gaps.
    #[test]
    fn write_hoa_ncw_renumbers_states() {
        let mut ncw: NCW = NCW::builder()
            .with_edges([
                (0, 'a', false, 0),
                (0, 'a', true, 2),
                (1, 'a', true, 1),
                (2, 'b', false, 0),
            ])
            .into_ncw(0);
        ncw.remove_state(1);
        assert_eq!(
            ncw.to_hoa(),
            "HOA: v1\nAP: 2 \"a\" \"b\"\nStates: 2\nStart: 0\nacc-name: co-Buchi\nAcceptance: 1 Fin(0)\n--BODY--\nState: 0\n[0 & !1] 1 {0}\n[0 & !1] 0\nState: 1\n[!0 & 1] 0\n--END--\n"
        );
    }

    #[test]
    fn letters_are_named_after_the_alphabet() {
        let dcw = DCW::builder()
            .with_edges([(0, 'x', false, 0), (0, 'y', true, 0)])
            .into_dcw(0);
        let hoa = dcw.to_hoa();
        assert!(hoa.contains("AP: 2 \"x\" \"y\"\n"));
        assert!(hoa.contains("[0 & !1] 0\n[!0 & 1] 0 {0}\n"));
    }

    #[test]
    fn unsupported_acceptance_is_an_error() {
        let mut w = String::new();
        assert!(matches!(
            OmegaAcceptanceCondition::Rabin.write_hoa(&mut w),
            Err(HoaError::UnsupportedAcceptance(_))
        ));
        OmegaAcceptanceCondition::CoBuchi
            .write_hoa(&mut w)
            .expect("co-Büchi is supported");
        assert_eq!(w, "acc-name: co-Buchi\nAcceptance: 1 Fin(0)\n");
    }
}
