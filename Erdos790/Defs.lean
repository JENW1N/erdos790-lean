/-
Erdős Problem 790 (JSP-000649): definitions.

Mathematical source: S. Korsky, "Large Sum-Free Subsets of Sets of Integers"
(13 September 2026), proving l(n) ≫ n/(log n)^2.
-/
import Mathlib

open Finset

namespace Erdos790

/-- A finite set `B` of integers is *sum-free* in the sense of Erdős Problem 790 if there are
no solutions to `a₁ = a₂ + ⋯ + aᵣ` with all `aᵢ ∈ B` pairwise distinct, i.e. no element of `B`
is the sum of two or more distinct other elements of `B`. -/
def IsSumFree (B : Finset ℤ) : Prop :=
  ∀ b ∈ B, ∀ S ⊆ B.erase b, 2 ≤ S.card → ∑ x ∈ S, x ≠ b

/-- The set of admissible values: every `n`-element set of integers contains a sum-free subset
of size at least `m`. -/
def admissible (n : ℕ) : Set ℕ :=
  {m : ℕ | ∀ A : Finset ℤ, A.card = n → ∃ B ⊆ A, IsSumFree B ∧ m ≤ B.card}

/-- `l n` is maximal such that every set `A ⊆ ℤ` with `|A| = n` contains a sum-free subset `B`
with `|B| ≥ l n` (Erdős Problem 790). -/
noncomputable def l (n : ℕ) : ℕ := sSup (admissible n)

lemma isSumFree_empty : IsSumFree ∅ := by
  intro b hb
  simp at hb

lemma IsSumFree.mono {B C : Finset ℤ} (hB : IsSumFree B) (hCB : C ⊆ B) : IsSumFree C := by
  intro b hb S hS hcard
  exact hB b (hCB hb) S (hS.trans (erase_subset_erase b hCB)) hcard

lemma zero_mem_admissible (n : ℕ) : 0 ∈ admissible n := by
  intro A _
  exact ⟨∅, empty_subset _, isSumFree_empty, le_rfl⟩

lemma le_of_mem_admissible {n m : ℕ} (hm : m ∈ admissible n) : m ≤ n := by
  classical
  let A : Finset ℤ := (range n).map ⟨fun k : ℕ => (k : ℤ), Nat.cast_injective⟩
  have hA : A.card = n := by simp [A]
  obtain ⟨B, hBA, -, hmB⟩ := hm A hA
  exact hmB.trans ((card_le_card hBA).trans hA.le)

lemma bddAbove_admissible (n : ℕ) : BddAbove (admissible n) :=
  ⟨n, fun _ hm => le_of_mem_admissible hm⟩

lemma l_mem_admissible (n : ℕ) : l n ∈ admissible n :=
  Nat.sSup_mem ⟨0, zero_mem_admissible n⟩ (bddAbove_admissible n)

/-- The defining property of `l n`. -/
lemma l_spec (n : ℕ) (A : Finset ℤ) (hA : A.card = n) :
    ∃ B ⊆ A, IsSumFree B ∧ l n ≤ B.card :=
  l_mem_admissible n A hA

/-- Maximality of `l n`. -/
lemma le_l {n m : ℕ} (hm : m ∈ admissible n) : m ≤ l n :=
  le_csSup (bddAbove_admissible n) hm

lemma l_le (n : ℕ) : l n ≤ n := le_of_mem_admissible (l_mem_admissible n)

end Erdos790
