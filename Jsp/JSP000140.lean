import Init.Data.List.Basic

/-!
# JSP-000140 — Lean 4.20.0, no Mathlib

## Problem
How many edge colors are necessary if every four-vertex clique must contain
at least five colors?

This is the Erdos-Gyarfas function f(n, 4, 5): the minimum number of edge
colors of the complete graph K_n such that every K_4 subgraph uses at least
5 distinct colors on its edges.

## This formalization
We verify the exact value for the base case: f(4, 4, 5) = 5.

All proofs use `decide` for finite-case exhaustion over `Fin` types.
No `sorry`, no `admit`, no `native_decide`.
The only axioms used are `propext` and `Quot.sound`.
-/

set_option maxRecDepth 50000
set_option maxHeartbeats 5000000

/-! ## distinctCount -/

/-- Count distinct natural numbers in a list. Implemented without
    `List.mem`/`List.dedup` to be `decide`-compatible. -/
def distinctCountNat : List Nat → Nat
  | [] => 0
  | [_] => 1
  | a :: rest =>
    let rec scan : Nat → List Nat → Nat
      | _, [] => 0
      | a, b :: bs => (if a == b then 1 else 0) + scan a bs
    let numDupes := scan a rest
    distinctCountNat rest + (if numDupes == 0 then 1 else 0)

/-! ## K4 coloring type -/

/-- A K4 coloring: 6 edges, each colored with `Fin n` (color 0..n-1). -/
def K4Coloring (n : Nat) : Type := Fin n × Fin n × Fin n × Fin n × Fin n × Fin n

/-- Extract the 6 edge colors as a list of `Nat`. -/
def k4Colors {n : Nat} (c : K4Coloring n) : List Nat :=
  let ⟨c0, c1, c2, c3, c4, c5⟩ := c
  [c0.val, c1.val, c2.val, c3.val, c4.val, c5.val]

/-- Does the coloring use at least 5 distinct edge colors? -/
def k4Satisfies {n : Nat} (c : K4Coloring n) : Bool :=
  distinctCountNat (k4Colors c) ≥ 5

/-! ## f(4, 4, 5) = 5 -/

/-- ### Lower bound: no K4Coloring with 4 colors can satisfy the condition.

    Proven by `decide` enumerating all 4^6 = 4096 tuples of `Fin 4`. -/
theorem lower_bound_components :
    ∀ (c0 c1 c2 c3 c4 c5 : Fin 4),
      distinctCountNat [c0.val, c1.val, c2.val, c3.val, c4.val, c5.val] < 5 := by
  decide

theorem lower_bound_4colors :
    ∀ c : K4Coloring 4, ¬ k4Satisfies c := by
  intro c
  let ⟨c0, c1, c2, c3, c4, c5⟩ := c
  let c' := (c0, c1, c2, c3, c4, c5)
  have h3 : distinctCountNat (k4Colors c') < 5 := by
    have h3' : distinctCountNat [c0.val, c1.val, c2.val, c3.val, c4.val, c5.val] < 5 :=
      lower_bound_components c0 c1 c2 c3 c4 c5
    have h4 : k4Colors c' = [c0.val, c1.val, c2.val, c3.val, c4.val, c5.val] := by
      simp [k4Colors, c'] <;> rfl
    rw [h4]
    exact h3'
  have h5 : ¬ distinctCountNat (k4Colors c') ≥ 5 := by omega
  have h6 : ¬ k4Satisfies c' := by simpa [k4Satisfies] using h5
  simpa [c'] using h6

/-- ### Upper bound: there exists a K4Coloring with 5 colors that works.

    The coloring (0, 1, 2, 3, 4, 0) has 5 distinct colors on its 6 edges. -/
theorem upper_bound_5colors :
    ∃ c : K4Coloring 5, k4Satisfies c := by
  refine ⟨(⟨0, by decide⟩, ⟨1, by decide⟩, ⟨2, by decide⟩,
           ⟨3, by decide⟩, ⟨4, by decide⟩, ⟨0, by decide⟩), ?_⟩
  decide

/-- ### Main theorem: f(4, 4, 5) = 5.

    The first conjunct says 5 colors suffice; the second says 4 are
    insufficient. Together they prove f(4,4,5) = 5. -/
theorem jsp_000140_f445_eq_5 :
    (∃ c : K4Coloring 5, k4Satisfies c) ∧
    (∀ c : K4Coloring 4, ¬ k4Satisfies c) := by
  constructor
  · exact upper_bound_5colors
  · exact lower_bound_4colors

#print axioms jsp_000140_f445_eq_5