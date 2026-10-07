import Init.Data.List.Basic
import Init.Data.List.Lemmas

/-!
# JSP-000290 — Lean 4.20.0, no Mathlib

## Question
Does every 5-element subset of {1,...,10} contain two distinct elements
whose sum equals 11?

## Answer: NO

**Counterexample**: The set {1, 2, 3, 4, 5} (5 elements from {1,...,10}).

Pairwise sums: 3, 4, 5, 5, 6, 6, 7, 7, 8, 9. None equals 11.

All proofs use decide — the core combinatorial fact is verified by
exhaustive checking. No sorry, no admit, no native_decide.
-/

/-- Does a list of nats contain two distinct elements summing to n? -/
def hasSumTo (l : List Nat) (target : Nat) : Bool :=
  l.any (fun a => l.any (fun b => a != b && a + b == target))

/-- The counterexample set {1, 2, 3, 4, 5}. -/
def S : List Nat := [1, 2, 3, 4, 5]

/-- The range {1,...,10}. -/
def range1to10 : List Nat := [1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- All elements of S are within {1,...,10}. -/
theorem S_in_range : forall x, x ∈ S -> x ∈ range1to10 := by decide

/-- The counterexample has exactly 5 elements. -/
theorem S_has_5_elements : S.length = 5 := by decide

/-- The counterexample has no two distinct elements summing to 11. -/
theorem no_sum_to_11 : hasSumTo S 11 = false := by decide

/-- Main theorem: there exists a 5-element subset of {1,...,10} with no pair summing to 11. -/
theorem jsp_000290_main :
    exists (S' : List Nat),
      S'.length = 5 /\
      (forall x, x ∈ S' -> x ∈ range1to10) /\
      hasSumTo S' 11 = false :=
  ⟨S, S_has_5_elements, S_in_range, no_sum_to_11⟩

#print axioms S_in_range
#print axioms S_has_5_elements
#print axioms no_sum_to_11
#print axioms jsp_000290_main
