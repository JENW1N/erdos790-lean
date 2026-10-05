/-
Erdős Problem 790: sanity checks that the definitions are not vacuous.
-/
import Erdos790.Main

open Finset

namespace Erdos790

/-- `{1, 2, 3}` is not sum-free: `3 = 1 + 2`. -/
example : ¬ IsSumFree {1, 2, 3} := by
  intro h
  exact h 3 (by decide) {1, 2} (by decide) (by decide) (by decide)

/-- `{1, 2, 4}` is sum-free. -/
example : IsSumFree {1, 2, 4} := by
  intro b hb S hS hcard
  have hS' : S ∈ (({1, 2, 4} : Finset ℤ).erase b).powerset := mem_powerset.2 hS
  simp only [mem_insert, mem_singleton] at hb
  rcases hb with rfl | rfl | rfl <;>
  · revert hS' hcard
    decide +revert

/-- A sum-free set may contain `0` and negative numbers; e.g. `{-1, 1}`... -/
example : IsSumFree {-1, 1} := by
  intro b hb S hS hcard
  have : (({-1, 1} : Finset ℤ).erase b).card ≤ 1 := by
    simp only [mem_insert, mem_singleton] at hb
    rcases hb with rfl | rfl <;> decide
  have := card_le_card hS
  omega

/-- ... but `{-1, 0, 1}` is not: `0 = (-1) + 1`. -/
example : ¬ IsSumFree {-1, 0, 1} := by
  intro h
  exact h 0 (by decide) {-1, 1} (by decide) (by decide) (by decide)

/-- `l n ≤ n`, and `l n` is attained. -/
example (n : ℕ) : l n ≤ n := l_le n

end Erdos790
