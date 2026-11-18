import CausalMohawkBridge.KrumSpec

/-!
# Lean-side correspondence tests — mirror of the Go test vectors

`internal/multikrum_lean_correspondence_test.go` in Sovereign-Mohawk-Proto
pins, for six input vectors, the selection computed by the Lean spec
(`#eval multiKrumSelectImpl` / `#eval multiKrumSelectManyImpl`) and asserts
that Go's `MultiKrumSelect` returns exactly the same indices and gradients.
Lean cannot invoke Go, so the Go half of that check lives in Go.

This module is the *other* half: it re-evaluates the same Lean functions on the
same inputs and asserts they still produce the pinned values, so any drift in
the ported spec is caught by `lake build`. It also exercises the row-12 safety
envelope (`multiKrumSelectSafe`) on and off the boundary.

The expected values below are taken verbatim from the Go test file; the two
halves together are the correspondence claim of
`proofs/FORMAL_TRACEABILITY_MATRIX.md` row 12.
-/

namespace CausalMohawkBridge.Correspondence

open KrumSpec

def nd (id : Nat) (g : List Float) : Node :=
  { id := id, gradient := g, isByzantine := false }

/-- n=5, f=1 → neighbors=2. Three honest gradients clustered near
    `[0.1, 0.1]`, two far Byzantine outliers. -/
def n5f1 : List Node :=
  [nd 0 [0.1, 0.1], nd 1 [0.1, 0.1], nd 2 [0.12, 0.09],
   nd 3 [100.0, -100.0], nd 4 [-99.0, 98.0]]

/-- n=7, f=2 → neighbors=3. Four honest gradients near `[1,1,1]`, three far
    Byzantine outliers. -/
def n7f2 : List Node :=
  [nd 0 [1.0, 1.0, 1.0], nd 1 [1.1, 0.9, 1.0], nd 2 [0.9, 1.1, 1.0],
   nd 3 [1.0, 1.0, 1.1], nd 4 [100.0, -100.0, 0.0],
   nd 5 [-90.0, 90.0, 90.0], nd 6 [0.0, 0.0, -200.0]]

/-- n=4, f=0 → neighbors=2, all honest. -/
def n4f0 : List Node :=
  [nd 0 [2.0, 3.0], nd 1 [2.1, 2.9], nd 2 [1.9, 3.1], nd 3 [2.0, 3.05]]

/-- n=3, f=0 → neighbors=1. Three evenly spaced points give an exact 3-way
    score tie; lowest index must win. -/
def n3f0 : List Node :=
  [nd 0 [0.0], nd 1 [1.0], nd 2 [2.0]]

/-- n=7, f=1 → neighbors=4, m=2. Five honest gradients near `[1,1]`. -/
def n7f1m2 : List Node :=
  [nd 0 [1.0, 1.0], nd 1 [1.05, 0.95], nd 2 [0.95, 1.05], nd 3 [1.02, 0.98],
   nd 4 [0.98, 1.02], nd 5 [50.0, -50.0], nd 6 [-50.0, 50.0]]

/-- n=6, f=1 → neighbors=3, m=3. Four honest gradients near `[2,2,2]`. -/
def n6f1m3 : List Node :=
  [nd 0 [2.0, 2.0, 2.0], nd 1 [2.1, 1.9, 2.0], nd 2 [1.9, 2.1, 2.0],
   nd 3 [2.0, 2.0, 2.1], nd 4 [100.0, -100.0, 0.0], nd 5 [-100.0, 100.0, 0.0]]

def check (name : String) (ok : Bool) : IO Unit :=
  if ok then IO.println s!"PASS {name}"
  else throw (IO.userError s!"FAIL {name}")

def main : IO Unit := do
  -- m = 1 correspondence vectors (TestMultiKrumLeanCorrespondence)
  check "n5_f1_honest_cluster" (multiKrumSelectImpl n5f1 2 == some [0.1, 0.1])
  check "n7_f2_honest_cluster" (multiKrumSelectImpl n7f2 3 == some [1.0, 1.0, 1.0])
  check "n4_f0_all_honest" (multiKrumSelectImpl n4f0 2 == some [2.0, 3.05])
  check "n3_f0_tie_break" (multiKrumSelectImpl n3f0 1 == some [0.0])
  -- general-m correspondence vectors (TestMultiKrumLeanCorrespondence_GeneralM)
  check "n7_f1_m2" (multiKrumSelectManyImpl n7f1m2 2 4 == [0, 3])
  check "n6_f1_m3" (multiKrumSelectManyImpl n6f1m3 3 3 == [0, 3, 1])
  -- row-12 safety envelope
  check "safe_n5_f1" (multiKrumSelectSafe n5f1 1 == some [0.1, 0.1])
  check "safe_n4_f0" (multiKrumSelectSafe n4f0 0 == some [2.0, 3.05])
  check "safe_n4_f1_rejected" (multiKrumSelectSafe n4f0 1 == none)
  check "safe_n3_f0_rejected" (multiKrumSelectSafe n3f0 1 == none)
  -- determinism
  check "deterministic" (multiKrumSelectImpl n7f2 3 == multiKrumSelectImpl n7f2 3)

#eval main

end CausalMohawkBridge.Correspondence
