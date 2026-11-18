# Preprint mapping and deviation log

This document maps the external preprint's claims to the machine-checked
theorems in this repository, and records every place the formal statement is a
strengthening, a weakening, an analogue, or open.

> **Provenance caveat.** The preprint itself is *not* in this repository. The
> source statements below are reconstructed from the private correspondence
> that motivated this formalization (the C1–R8 construction letter and the
> theorem list exchanged with the author). Each row marks whether the wording
> is *quoted* from that correspondence or *inferred*. Treat the mapping as a
> claim about intent, not a verbatim transcription, until the preprint text is
> added alongside this file.

## Toolchain

Mathlib-free Lean 4.14.0 (`lean-toolchain`). No Mathlib, no `Rat`, no
normed/compactness infrastructure. Consequences are listed in `NONCLAIMS.md`.

## Source statements

### P1 — causal lattice, parity sector, spatial quotient (the "Theorem 3.1" reading)

*Quoted/inferred from the correspondence:* the spatial cycle is `ℤ/nℤ` with even
`n ≥ 4`; the lifted parity lattice `Γ = {t + j even}` carries steps
`(t, j) → (t+1, j±1)`; time is unwrapped; causal order is strict forward in
time; local commuting diamonds coexist with it; the cyclic identification is
spatial, and the quotient-to-lift correspondence is local under a no-winding
condition; in null coordinates `r = (t+j)/2`, `l = (t−j)/2`, reachability is
nonnegative increments in both.

| Preprint element | Lean theorem | Status |
| --- | --- | --- |
| `Γ = {t+j even}`, steps `±1` | `CausalLattice.Event`, `Step.plus/minus`, `OnParity` | proved (definitions) |
| reachability = null-coordinate order | `CausalOrder.reach_iff_uv_order`, `NullCoordinates.reach_iff_rl_order` | proved |
| spatial quotient `j mod n` | `ParityQuotient.q`, `QStep`, `QReach` | proved (definitions) |
| even `n` preserves the parity sector | `ParityQuotient.q_parity` | proved, hypothesis `n % 2 = 0` |
| no-winding lift, `ℓ_n > 4B` | `ParityQuotient.reach_of_qReach_of_noWinding` (`4·B < n·sp`) | proved, `sp` generalised; `sp = 1` recovers `4·B < n` (`reach_of_qReach_of_noWinding_unit`) |
| composite transfer | `PreprintBridge.theorem31` | proved (see deviations) |
| epoch rotation count = `Δr + Δl` | `EpochRot.reach_to_rot`, `PreprintBridge.epoch_count_quotient` | proved |

**Deviations.**
1. `n ≥ 4` is weakened to `2 ≤ n` in the Lean statements; the evenness
   hypothesis (`n % 2 = 0`) is carried separately by `q_parity`/`theorem31`.
   No theorem uses `n ≥ 4`; `n = 2` is admitted by the current hypotheses.
2. The lattice spacing is a parameter `sp`, so the circumference is `n·sp`
   (`ParityQuotient.Window`). The preprint's `a_n` is read as `sp`.
3. `theorem31`'s parity clause is `OnParity e₁ → OnParity e₂` for the lifted
   realisation, not the converse; the descent statement `q_parity` is proved
   separately.

### P2 — common refining domains for affine Lorentz words (Theorem 5.2)

*Inferred from the correspondence:* "common refining domains for bounded finite
compositions of affine Lorentz transformations".

| Preprint element | Lean theorem | Status |
| --- | --- | --- |
| affine Lorentz map, `a² − b² = 1` | `Lorentz.ALorentz` | proved, **degenerate over `Int`** (`sq_sub_eq_one`) |
| rational affine Lorentz map | `Lorentz.ScaledLorentz` (`A² − B² = N²`) | proved (the non-trivial content) |
| interval preserved | `Lorentz.Q_apply_sub`, `Lorentz.Q_scaled`, `Lorentz.Q_word` | proved |
| common refining domain | `Lorentz.commonRefinement_exists`, `commonRefinement_fine`, `commonRefinement_of_dvd_cd` | proved (see deviations) |
| invariance criterion | `Lorentz.hMap_iff_dvd_cd` | proved |
| analytic "uniform approximation on compact sets" | — | **open**, see `NONCLAIMS.md` |

**Deviations.**
1. Over `Int`, `a² − b² = 1` forces `(a,b) = (±1,0)` (`sq_sub_eq_one`), so the
   integer affine group is degenerate. The non-trivial content is the rational
   form `ScaledLorentz`; `Composition.scaledLorentzQSys` instantiates the
   composition vocabulary on it, with the interval scaled by `N²`
   (`Composition.qPreservesScaled`).
2. `commonRefinement_fine` gives `M₀ · ∏_{L∈w} L.N` for a **linear** word
   (zero translation part). For a general affine word a modulus must divide
   every translation component (`commonRefinement_of_dvd_cd`,
   `hMap_iff_dvd_cd`); "arbitrarily fine" is false in general.
3. The analytic clause is not formalized.

## Negative controls

Each load-bearing hypothesis has a machine-checked refutation when dropped:

| Hypothesis | Counterexample |
| --- | --- |
| `4·B < n·sp` in no-winding | `ParityQuotient.noWinding_hypothesis_load_bearing` |
| `n % 2 = 0` in `q_parity` | `ParityQuotient.q_parity_odd_counterexample` |
| `1 ≤ z` in `tail_bound` | `Chernoff.tail_bound_z_lt_one` |
| `b = 0` in `sq_sub_eq_one` | `Lorentz.sq_sub_eq_one_converse` |
