# CLAUDE.md

Guidance for working in this repository. See `PLAN.md` for the roadmap and known problems.

## What this is

`automata` is a single Rust crate for working with transition systems and automata over finite and infinite (omega) words. It was extracted, with history, from `leonbohn/frieda` (where it lived as `crates/automata` plus `crates/automata-core`). The former `automata-core` crate was merged in as top-level modules (`alphabet`, `word`, `math`, `dag`, plus `Color`/`Lattice`/`Void`/`Int`/`Show` at the crate root). Edition 2024, version 0.1.0, MSRV 1.88 (`rust-version`; checked by the `msrv` CI job).

Related crates that stay elsewhere: `hoars` (HOA parser, `leonbohn/hoars`, depended on from crates.io, currently 0.3) and `automata-learning` (learning algorithms, in `leonbohn/frieda`).

## Commands

```shell
cargo build --all-targets
cargo test                         # 68 unit tests, 45 doctests (some ignored)
cargo fmt --check
cargo clippy --all-targets --all-features -- -D warnings
RUSTDOCFLAGS="-D warnings" cargo doc --no-deps
cargo test --features spot spot:: -- --ignored   # Spot tests, need autfilt (via WSL on Windows)
cargo run --release --features random --example hd_criteria -- samples=1500   # CSV sweep: criteria vs. DBP; flag `spot` (feature spot) confirms witnesses
./scripts/check                    # same as CI: fmt, clippy, doc, per-feature check (needs cargo-hack), tests in three feature configurations
```

## Layout

- Foundations (formerly the `automata-core` crate):
  - `src/alphabet.rs` (+ `alphabet/`): `Symbol`, `Expression`/`Matcher`, `Alphabet`; `CharAlphabet`, `Fixed<S, N>`, `Directional`, and propositional (`PropAlphabet`, BDD-backed, used for HOA).
  - `src/word.rs` (+ `word/`): `Word`, `FiniteWord`, `OmegaWord`; `PeriodicOmegaWord`, `ReducedOmegaWord`, `NormalizedOmegaWord`; adapters (`Concat`, `Repeat`, `Skip`, `Infix`, `Rotate`). The `upw!` macro is exported at the crate root.
  - `src/math.rs`, `src/dag.rs`, `src/color.rs` (`Int`, `Void`, `Color`, `Lattice`), `src/show.rs` (`Show`).
- `src/ts.rs` and `src/ts/`: the `TransitionSystem` trait and everything around it.
  - `impls/`: `LinkedListTransitionSystem` (the only implementation; aliases `TS`, `DTS`, `NTS`).
  - `operations/`: lazy adapters (`map`, `product`, `quotient`, `restricted`, `reverse`, `subset`, `with_state_color`).
  - `run.rs`/`path.rs`: runs with `Observer`s, `Path`, `Lasso`.
  - `connected_components/`: Tarjan SCCs, `SccDecomposition`. `reachable.rs`: reachability, minimal representatives. `builder.rs`: `TSBuilder`.
  - Capability traits: `Deterministic`, `Pointed`, `Sproutable`, `Shrinkable`, `PredecessorIterable`; conversions in `representation.rs` (`CollectTs`, `IntoTs`).
- `src/automaton.rs` and `src/automaton/`: `Automaton<A, Z, Q, C, D, const OMEGA, const DET>` pairs a TS with an initial state and acceptance condition `Z`. Aliases `DFA`, `DBA`, `DPA`, Moore/Mealy. `omega/` has `buchi`, `parity` (four min/max even/odd variants), `rabin`, `muller`; the `Semantics` trait defines acceptance.
  - `omega/co_buchi/`: the [AK22] minimization pipeline (`NCW::minimize`); `dbp.rs` has `NCW::hd_characteristics` (cells, sufficient `Criterion`s for d = hd, exact DBP search that returns a pruned tDCW as witness).
- `src/congruence/` (right congruences, Cayley graphs, transition profiles), `src/minimization/partition_refinement.rs`, `src/families/` (FDFA, FWPM), `src/hoa/` (feature `hoa`), `src/dot.rs` (Graphviz/dot output and rendering), `src/random/` (feature `random`; `layered.rs`: two-layer GFG-tNCW generator `LayeredNcw`), `src/spot.rs` (feature `spot`: runs Spot's `autfilt` through a launcher, `wsl -e` by default on Windows, overridable via `AUTOMATA_SPOT`; HOA over stdin/stdout, helper `sh` scripts for multi-automaton calls).

Edges are labeled with alphabet *expressions*; a *transition* is the concrete (state, symbol) step. Capabilities are layered via extra traits rather than one large trait; add a trait or blanket impl rather than extending `TransitionSystem`.

Features: `default = ["hoa"]`; opt-in: `random`, `spot` (implies `hoa`, no extra dependencies), `render` (SVG/PNG via `resvg`/`layout-rs`, experimental), `graphviz` (calls the `dot` executable, implies `render`). Text `dot` output is always available.

## Conventions

- `#![deny(missing_docs)]` and `deny(rustdoc::broken_intra_doc_links)` are on; README is `include_str!`ed into the crate docs, so README code blocks are doctests.
- Use `tracing` for logging in library code.
- Do not panic in library code: return `Result` with typed errors (`src/error.rs` has the crate-wide `#[non_exhaustive]` `Error`; domain errors such as `PropAlphabetError`, `NotPeriodicError`, `hoa::HoaError` convert into it; never use `String` as an error type); use `Error::NotYetImplemented` instead of `todo!()`/`unimplemented!()`. Existing panics are being removed (see `PLAN.md`).
- Ask before committing or pushing.

## Known sharp edges

- `Automaton` has seven generic parameters; type errors can be long.
- Features must stay independent: code using an optional dependency needs the matching `#[cfg(feature = "...")]` (`scripts/check` builds with `--no-default-features` too).
- ~320 `unwrap`/`expect` and ~65 `panic!` calls in library code; many `#[allow(missing_docs)]`.
