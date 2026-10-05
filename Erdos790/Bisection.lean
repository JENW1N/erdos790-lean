/-
Erdős Problem 790: the bisection lemma (Lemma 2 of Korsky's paper).

For a finite set `A` of integers there are sets `D a` of at most `⌈log₂ |A|⌉` numbers such that
every difference `b - a` (`a < b` in `A`) is approximated within a factor two by some element
of `D a ∪ D b`.  We use integer dividing points (the largest element of the lower half), which
only changes the proof in that some recorded distances may be `0`; such distances are harmless.
-/
import Erdos790.Defs

open Finset

namespace Erdos790

/-- Every finite set of integers has a "lower part" of any prescribed size. -/
theorem exists_lower_part (A : Finset ℤ) :
    ∀ k : ℕ, k ≤ A.card → ∃ L ⊆ A, L.card = k ∧ ∀ x ∈ L, ∀ y ∈ A, y ∉ L → x < y := by
  intro k
  induction k with
  | zero => exact fun _ => ⟨∅, empty_subset _, rfl, by simp⟩
  | succ k ih =>
    intro hk
    obtain ⟨L, hLA, hLc, hL⟩ := ih (by omega)
    have hne : (A \ L).Nonempty := by
      rw [← card_pos, card_sdiff_of_subset hLA]
      omega
    have hy : (A \ L).min' hne ∈ A \ L := min'_mem _ _
    refine ⟨insert ((A \ L).min' hne) L, insert_subset (mem_sdiff.1 hy).1 hLA, ?_, ?_⟩
    · rw [card_insert_of_notMem (mem_sdiff.1 hy).2, hLc]
    · intro x hx z hzA hz
      rw [mem_insert] at hx hz
      simp only [not_or] at hz
      rcases hx with rfl | hx
      · exact lt_of_le_of_ne (min'_le _ _ (mem_sdiff.2 ⟨hzA, hz.2⟩)) (Ne.symm hz.1)
      · exact hL x hx z hzA hz.2

/-- **Bisection lemma** (Korsky, Lemma 2). -/
theorem bisection : ∀ (n : ℕ) (A : Finset ℤ), A.card = n →
    ∃ D : ℤ → Finset ℤ, (∀ a, (D a).card ≤ Nat.clog 2 n) ∧
      ∀ a ∈ A, ∀ b ∈ A, a < b → ∃ δ ∈ D a ∪ D b, b - a ≤ 2 * δ ∧ δ ≤ b - a := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro A hA
  rcases Nat.lt_or_ge n 2 with hn | hn
  · refine ⟨fun _ => ∅, by simp, ?_⟩
    intro a ha b hb hab
    exfalso
    have h1 : A.card ≤ 1 := by omega
    exact (ne_of_lt hab) (card_le_one.1 h1 a ha b hb)
  · obtain ⟨L, hLA, hLc, hL⟩ := exists_lower_part A (n / 2) (by omega)
    have hRc : (A \ L).card = n - n / 2 := by
      rw [card_sdiff_of_subset hLA, hA, hLc]
    obtain ⟨DL, hDLc, hDL⟩ := ih (n / 2) (by omega) L hLc
    obtain ⟨DR, hDRc, hDR⟩ := ih (n - n / 2) (by omega) (A \ L) hRc
    have hLne : L.Nonempty := by
      rw [← card_pos]
      omega
    refine ⟨fun a => if a ∈ L then insert (L.max' hLne - a) (DL a)
      else insert (a - L.max' hLne) (DR a), ?_, ?_⟩
    · intro a
      have hclog : Nat.clog 2 n = Nat.clog 2 ((n + 2 - 1) / 2) + 1 :=
        Nat.clog_of_two_le (by norm_num) hn
      have h1 : Nat.clog 2 (n / 2) ≤ Nat.clog 2 ((n + 2 - 1) / 2) :=
        Nat.clog_mono_right _ (by omega)
      have h2 : Nat.clog 2 (n - n / 2) ≤ Nat.clog 2 ((n + 2 - 1) / 2) :=
        Nat.clog_mono_right _ (by omega)
      dsimp only
      split_ifs
      · exact (card_insert_le _ _).trans (by have := hDLc a; omega)
      · exact (card_insert_le _ _).trans (by have := hDRc a; omega)
    · intro a ha b hb hab
      by_cases haL : a ∈ L <;> by_cases hbL : b ∈ L
      · obtain ⟨δ, hδ, h⟩ := hDL a haL b hbL hab
        refine ⟨δ, ?_, h⟩
        simp only [haL, hbL, if_true]
        rcases mem_union.1 hδ with h' | h'
        · exact mem_union_left _ (mem_insert_of_mem h')
        · exact mem_union_right _ (mem_insert_of_mem h')
      · have hat : a ≤ L.max' hLne := le_max' _ _ haL
        have htb : L.max' hLne < b := hL _ (max'_mem _ _) b hb hbL
        by_cases hcase : b - L.max' hLne ≤ L.max' hLne - a
        · refine ⟨L.max' hLne - a, ?_, by omega, by omega⟩
          simp [haL, hbL]
        · refine ⟨b - L.max' hLne, ?_, by omega, by omega⟩
          simp [haL, hbL]
      · exact absurd (hL b hbL a ha haL) (not_lt.2 hab.le)
      · obtain ⟨δ, hδ, h⟩ := hDR a (mem_sdiff.2 ⟨ha, haL⟩) b (mem_sdiff.2 ⟨hb, hbL⟩) hab
        refine ⟨δ, ?_, h⟩
        simp only [haL, hbL, if_false]
        rcases mem_union.1 hδ with h' | h'
        · exact mem_union_left _ (mem_insert_of_mem h')
        · exact mem_union_right _ (mem_insert_of_mem h')

end Erdos790
