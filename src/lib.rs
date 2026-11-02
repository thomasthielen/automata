#![doc = include_str!("../README.md")]
#![deny(missing_docs)]
#![deny(rustdoc::broken_intra_doc_links)]

/// The crate-wide [`Error`] type.
pub mod error;
pub use error::Error;

/// An alphabet defines a collection of possible symbols. This
/// module implements simple alphabets which consist of just a
/// collection of symbols, and propositional alphabets where each
/// symbol is represented by a boolean expression over some
/// set of base atomic propositions.
#[macro_use]
pub mod alphabet;

/// A word is a sequence of symbols from some alphabet. Herein,
/// different types of words are defined, specifically finite ones
/// and different reprsentations of infinite ones.
/// Moreover, some constructions of manipulating words, taking suffixes,
/// infixes and such are given.
/// Finally, the module also implements normalization for words.
#[macro_use]
pub mod word;

/// Defines some mathematical objects that are used such as bijections,
/// sets and mappings.
pub mod math;

/// Defines a representation of directed, acyclic graphs. These are for example
/// used for the representation of the strongly connected components of a transition system.
pub mod dag;

mod color;
pub use color::{Color, Int, Lattice, Void};

mod show;
pub use show::Show;

/// Points to the default implementation of [`TransitionSystem`] in the [`Deterministic`] case.
pub type TS<A = alphabet::CharAlphabet, Q = Void, C = Void, const DET: bool = true> =
    ts::LinkedListTransitionSystem<A, Q, C, DET>;
/// Points to the default implementation of [`TransitionSystem`] in the [`Deterministic`] case.
pub type DTS<A = alphabet::CharAlphabet, Q = Void, C = Void> = TS<A, Q, C, true>;
/// Points to the default implementation of [`TransitionSystem`] in the case where it is
/// **now known to be** [`Deterministic`].
pub type NTS<A = alphabet::CharAlphabet, Q = Void, C = Void> = TS<A, Q, C, false>;

/// implements the interface to the `hoars` package. Is only available on create feature `hoa`.
#[cfg(feature = "hoa")]
pub mod hoa;

#[allow(missing_docs)]
pub mod families;

/// This module defines transition systems and successor functions and such.
#[macro_use]
pub mod ts;
pub use ts::{Deterministic, Pointed, TransitionSystem};

/// Defines automata and common types of combinations of transition system with acceptance condition.
#[allow(clippy::upper_case_acronyms)]
pub mod automaton;
pub use automaton::Automaton;

/// Defines different representations of automata as mappings between an input and
/// an output alphabet.
pub mod representation;

/// Defines congruence relations and congruence classes.
pub mod congruence;
pub use congruence::{Class, Congruence, RightCongruence};

/// Contains implementations different minimization algorithms.
pub mod minimization;

pub mod games;

/// Implements the generation of random transition systems.
#[cfg(feature = "random")]
pub mod random;

#[cfg(feature = "spot")]
pub mod spot;

/// This module deals with transforming a transition system (or similar) into a representation in the dot (graphviz) format.
pub mod dot;

#[cfg(test)]
mod tests {
    pub fn wiki_dfa() -> crate::automaton::DFA<crate::alphabet::CharAlphabet> {
        use crate::ts::TSBuilder;

        TSBuilder::without_edge_colors()
            .with_state_colors([false, false, true, true, true, false])
            .with_edges([
                (0, 'a', 1),
                (0, 'b', 2),
                (1, 'a', 0),
                (1, 'b', 3),
                (2, 'a', 4),
                (2, 'b', 5),
                (3, 'a', 4),
                (3, 'b', 5),
                (4, 'a', 4),
                (4, 'b', 5),
                (5, 'a', 5),
                (5, 'b', 5),
            ])
            .into_dfa(0)
    }
}
