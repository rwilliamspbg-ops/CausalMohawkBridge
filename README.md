# CausalMohawkBridge

A Mathlib-free Lean 4.14.0 formalization bridging two sources:

- the **causal-lattice / parity-quotient preprint** — Theorem 3.1 causal geometry
  (null coordinates, parity sector, spatial quotient) and the Theorem 5.2
  common-domain result for affine Lorentz words; and
- the **Sovereign-Mohawk-Proto epoch model** — Multi-Krum selection, epoch
  rotation, and the Byzantine safety envelope `n > 2f + 2`.

The bridge claim is that causal reachability on the lifted lattice induces a
chain of epoch rotations whose length is exactly the causal distance, and that
the pair (parity sector, Krum envelope) is an invariant of the combined
causal/epoch step.

## Toolchain

- `leanprover/lean4:v4.14.0` (see `lean-toolchain`).
- **No Mathlib** and no external dependencies; `lakefile.lean` declares a single
  `lean_lib`. All modules are written against Lean core only.

## Module map

| Module | Contents |
| --- | --- |
| `CausalLattice.lean` | Lifted lattice events, generator steps `stepPlus`/`stepMinus`, reachability `Reach`, parity sector `OnParity`, null coordinates `u = t+j`, `v = t-j`. |
| `EpochTransition.lean` | Mohawk epoch state `(epoch, n, f)`, Krum envelope `2f+2 < n`, single step and `StepStar` transitions. |
| `Bridge.lean` | A causal path induces an epoch-rotation chain advancing by the causal `t`-gap, with parity and envelope preserved. |
| `KrumSpec.lean` | Faithful Mathlib-free port of the upstream Multi-Krum selection specification. |
| `KrumRefinement.lean` | Row-12 refinement lemmas; identifies `Mohawk.krumEnvelope` with upstream `bftImplSafe`. |
| `CausalOrder.lean` | Reachability characterized as null-coordinate order with an even `u`-gap. |
| `EpochRot.lean` | Explicit-length rotation relation `Rot`; causal distance equals rotation count. |
| `Correspondence.lean` | Re-evaluates the six Go-pinned Multi-Krum test vectors on the Lean side to catch port drift. |
| `SelectionEquivalence.lean` | General-`m` Multi-Krum selection equals `multiKrumSelectImpl` at `m = 1`; `FloatOrderLaws` trust boundary. |
| `NullCoordinates.lean` | `r = (t+j)/2`, `l = (t-j)/2`; Theorem 3.1(i): on the parity sector, reachability is coordinatewise order. |
| `ParityQuotient.lean` | Spatial quotient `j mod n`; even-`n` parity preservation and the no-winding lift condition. |
| `PreprintBridge.lean` | Theorem 3.1 composite: parity descent, no-winding lift (spacing `sp`), epoch count = null-increment sum. |
| `Lorentz.lean` | Integer affine Lorentz words on refining sublattices; Theorem 5.2 domain and exact-preservation clauses. |
| `Composition.lean` | Abstract local-to-global composition vocabulary, instantiated on the deterministic systems; Chernoff normalisation. |
| `Chernoff.lean` | Self-contained binomial identity and exponential tail bound in integer form. |

`CausalMohawkBridge.lean` (root) imports all of the above and carries the
`#print axioms` audit lines.

## Build and verify

```sh
lake build
```

Building the root elaborates every module and emits the `#print axioms` output
for the audited theorems listed in `CausalMohawkBridge.lean`. To run the audit
on the root alone:

```sh
lake env lean CausalMohawkBridge.lean
```

`make ci` runs the same gate as `.github/workflows/build.yml`: `build`,
`audit`, and `lint` (the vacuous-claim scan in `scripts/lint_vacuous_claims.py`).

No `sorry` or global `axiom` appears in the sources.

## Provenance and non-claims

- `PREPRINT_MAPPING.md` maps the external preprint's statements to the Lean
  theorems and logs every deviation (strengthened / weakened / analogue / open).
  The preprint text is **not** in this repository; the mapping is reconstructed
  from the correspondence that motivated the work.
- `NONCLAIMS.md` lists what is deliberately not established: the Theorem 5.2
  analytic clause, "arbitrarily fine" affine refinement, the missing `Rat`,
  the `FloatOrderLaws` trust boundary, and the empirical (not machine-checked)
  Go↔Lean correspondence.

## Claim status

### Proved — headline theorems

- **Causal geometry (Theorem 3.1 reading).**
  `CausalLattice.reach_iff_null`, `CausalOrder.null_iff_uv_order`,
  `CausalOrder.reach_iff_uv_order` (reachability = null-coordinate order plus
  an even `u`-gap), `NullCoordinates.reach_iff_rl_order` (on the parity sector,
  reachability = coordinatewise order in `r`, `l`), `NullCoordinates.reach_antisymm`,
  `NullCoordinates.reach_t_eq_rl`.
- **Parity quotient.** `ParityQuotient.q_parity` (even `n` preserves the parity
  sector), `ParityQuotient.reach_of_qReach_of_noWinding` (discrete `ℓ_n > 4B`
  implies quotient reachability lifts), `ParityQuotient.reach_j_bound`,
  `reach_of_qReach_of_noWinding_unit` (`sp = 1`), and the negative controls
  `noWinding_hypothesis_load_bearing`, `q_parity_odd_counterexample`.
- **Epoch bridge.** `Bridge.reach_to_epochs`, `EpochRot.Rot.epoch_eq`,
  `EpochRot.reach_to_rot`, `PreprintBridge.epoch_count_eq_rl`,
  `PreprintBridge.epoch_count_quotient` (rotation count = sum of null-coordinate
  increments), `PreprintBridge.theorem31` (composite: parity descent ∧ no-winding
  lift ∧ epoch count, for even `n` and spacing `sp`).
- **Multi-Krum.** `KrumRefinement.go_neighbors_valid`, `go_neighbors_no_clamp`,
  `multiKrumSelectSafe_none_outside_envelope`, `krumEnvelope_iff_bftImplSafe`,
  `bft_impl_refines_spec`, and
  `SelectionEquivalence.multiKrumSelectManyImpl_one_eq_multiKrumSelectImpl`
  (`m = 1` agreement, conditioned on `FloatOrderLaws`).
- **Theorem 5.2 core (Lorentz).** `Lorentz.commonRefinement_exists`,
  `commonRefinement_fine`, `commonRefinement_of_dvd_cd`,
  `commonRefinement_linear_arbitrary`, `hMap_iff_dvd_cd` (invariance iff the
  modulus divides the translation part), `sq_sub_eq_one` (over `Int`,
  `a²-b²=1` forces `(a,b)=(±1,0)`, so the integer affine group is degenerate and
  the non-trivial content is `ScaledLorentz`), `sq_sub_eq_one_converse`,
  `Q_scaled`, `Q_word`.
- **Chernoff.** `Chernoff.binomial`, `Chernoff.tail_bound`, `tailNat_bound`,
  `tailNat_le`, `tailNat_cleared`, `tail_bound_z_lt_one` (negative control);
  normalisation in `Composition.chernoff_tail_two`,
  `chernoff_probability_bound`, `chernoff_probability_tail`,
  `chernoff_probability_form`, `chernoff_probability_bound_nat`,
  `Composition.probRepairProb` (probability form) and
  `Composition.tailProbSys_prob`.
- **Composition vocabulary.** `Composition.preservesStar_of_preserves`,
  `causalSys_preserves`, `epochSys_preserves`, `lorentzQSys_preserves`,
  `scaledLorentzQSys_preserves` (non-degenerate rational Lorentz instance,
  via `qPreservesScaled`), `nullQSys_preserves`, `probRepair_of_le`.

### Deliberately not formalized

- The analytic **"uniform approximation on compact sets"** clause of Theorem
  5.2. It needs a normed/compactness infrastructure this project does not
  carry. The domain clause (`commonRefinement_*`) and the exact-preservation
  clause (`Q_scaled`, `Q_word`) are formalized.
- **Probability bounds are stated in cleared-integer form.** Core 4.14 has no
  `Rat`, so the tail comparison is e.g.
  `f * 2^(m+k) ≤ 2^m * 3^m` (equivalently `f / 2^m ≤ (3/4)^m · 2^(m-k)`) rather
  than a rational inequality.
- **Go ↔ Lean correspondence scope.** Only the deterministic Multi-Krum
  material plus the Chernoff/Lorentz test. The Go halves live upstream in
  `internal/multikrum_lean_correspondence_test.go` and
  `internal/chernoff_lean_correspondence_test.go`; this repository re-evaluates
  the Lean side only.
- `SelectionEquivalence.FloatOrderLaws` (IEEE-754 comparison laws for non-NaN
  doubles) is an **explicit structure argument, not an axiom** — the single
  trust boundary of that module, visible at each use site.
