# Non-claims

What this repository does **not** establish. Stated explicitly so the proved
results in `README.md` are not over-read.

## Open mathematics

1. **Theorem 5.2, analytic clause.** The preprint's "uniform approximation on
   compact sets" statement is not formalized. It needs a normed-space and
   compactness infrastructure that this Mathlib-free toolchain does not carry.
   What is proved: the domain clause (`Lorentz.commonRefinement_*`) and exact
   preservation on the refined lattice (`Lorentz.Q_scaled`, `Q_word`).
2. **"Arbitrarily fine" affine refinement.** For a word with nonzero
   translation part, a common refining modulus must *divide* every translation
   component (`Lorentz.hMap_iff_dvd_cd`), so the modulus is bounded above. The
   unbounded version holds only for linear words
   (`Lorentz.commonRefinement_linear_arbitrary`).
3. **`n ≥ 4`.** The Lean no-winding statements assume `2 ≤ n` (plus
   `n % 2 = 0` where parity is used), not the preprint's `n ≥ 4`.

## Infrastructure limits

4. **No `Rat`.** Core Lean 4.14 has no rational type, so probability bounds are
   stated in cleared-integer form: `f · 2^(m+k) ≤ 2^m · 3^m`, equivalently
   `f / 2^m ≤ (3/4)^m · 2^(m-k)`. `Composition.probRepairProb` is the
   probability statement; `Composition.probRepair` is a raw *count* bound and
   its `3^m` instance is exponentially large, not a probability.
5. **No `LinearOrder Float`.** `SelectionEquivalence.FloatOrderLaws` is an
   explicit structure argument (the eight IEEE-754 order laws for non-NaN
   doubles), not a derivation. See the scope note at that declaration.

## Empirical, not machine-checked

6. **Go ↔ Lean correspondence.** Lean cannot invoke Go, so the cross-language
   agreement is pinned by test vectors, not proved. The Go halves live in
   `Sovereign-Mohawk-Proto`: `internal/multikrum_lean_correspondence_test.go`
   and `internal/chernoff_lean_correspondence_test.go`. This repository
   re-evaluates the Lean side only.

## Provenance

7. **The preprint text is not in this repository.** `PREPRINT_MAPPING.md`
   reconstructs the source statements from the private correspondence that
   motivated the work and marks each row quoted vs. inferred. Until the
   preprint is added, the mapping is a claim about intent, not a transcription.
8. **The lattice-spacing convention is assumed.** `ParityQuotient.Window`
   reads `sp` as the lattice spacing (`n·sp` is the circumference, `B` the
   window half-width in physical units). This is the reading that makes
   `4·B < n·sp` the discrete `ℓ_n > 4B`; the preprint's own convention should be
   checked against it.
