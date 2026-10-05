/-
Erdős Problem 790: Korsky's theorem for finite sets of positive integers.

Every finite set `A` of `n ≥ 1` positive integers contains a sum-free subset `B` with
`n ≤ 4 K(n) |B|`, where `K(n) = (⌈log₂ n⌉ + 1)(⌊log₂ (8n)⌋ + 1) = O((log n)²)`.
-/
import Erdos790.Bisection
import Erdos790.Average

open Finset

namespace Erdos790

/-- The dyadic index of a positive integer `x`: `2 ^ jf x ≤ x < 2 ^ (jf x + 1)`. -/
def jf (x : ℤ) : ℕ := Nat.log 2 x.toNat

lemma two_pow_jf_le {x : ℤ} (hx : 0 < x) : (2 : ℤ) ^ jf x ≤ x := by
  have h : 2 ^ jf x ≤ x.toNat := Nat.pow_log_le_self 2 (by omega)
  have h' : ((2 ^ jf x : ℕ) : ℤ) ≤ ((x.toNat : ℕ) : ℤ) := Nat.cast_le.2 h
  push_cast at h'
  rwa [Int.toNat_of_nonneg hx.le] at h'

lemma lt_two_pow_jf_succ {x : ℤ} (hx : 0 < x) : x < (2 : ℤ) ^ (jf x + 1) := by
  have h : x.toNat < 2 ^ (jf x + 1) := Nat.lt_pow_succ_log_self (by norm_num) _
  have h' : ((x.toNat : ℕ) : ℤ) < ((2 ^ (jf x + 1) : ℕ) : ℤ) := Nat.cast_lt.2 h
  push_cast at h'
  rwa [Int.toNat_of_nonneg hx.le] at h'

/-- Two positive integers in the same dyadic interval are within a factor two. -/
lemma lt_two_mul_of_jf_eq {z w : ℤ} (hz : 0 < z) (hw : 0 < w) (h : jf z = jf w) :
    w < 2 * z := by
  have h1 := lt_two_pow_jf_succ hw
  have h2 := two_pow_jf_le hz
  rw [← h, pow_succ] at h1
  linarith

/-- For fixed `δ`, the positive integers `z` with `δ ≤ 2nz` and `z ≤ 2δ` occupy at most
`⌊log₂ (8n)⌋ + 1` dyadic intervals. -/
lemma card_window (A : Finset ℤ) (hpos : ∀ a ∈ A, 0 < a) (n : ℕ) (hn : 1 ≤ n) (δ : ℤ) :
    ((A.filter (fun z => δ ≤ 2 * (n : ℤ) * z ∧ z ≤ 2 * δ)).image jf).card
      ≤ Nat.log 2 (8 * n) + 1 := by
  set G := (A.filter (fun z => δ ≤ 2 * (n : ℤ) * z ∧ z ≤ 2 * δ)).image jf with hG
  rcases G.eq_empty_or_nonempty with h | hne
  · simp [h]
  · have hsub : G ⊆ Icc (G.min' hne) (G.min' hne + Nat.log 2 (8 * n)) := by
      intro k hk
      rw [mem_Icc]
      refine ⟨min'_le _ _ hk, ?_⟩
      have hmin : G.min' hne ∈
          (A.filter (fun z => δ ≤ 2 * (n : ℤ) * z ∧ z ≤ 2 * δ)).image jf := min'_mem G hne
      rw [hG] at hk
      obtain ⟨z, hz, rfl⟩ := mem_image.1 hk
      obtain ⟨z0, hz0, hz0m⟩ := mem_image.1 hmin
      rw [mem_filter] at hz hz0
      have hzp := hpos z hz.1
      have hz0p := hpos z0 hz0.1
      have hle : jf z0 ≤ jf z := by
        rw [hz0m]
        exact min'_le _ _ (mem_image_of_mem _ (mem_filter.2 hz))
      have a1 := two_pow_jf_le hzp
      have a2 := lt_two_pow_jf_succ hz0p
      have hnpos : (0 : ℤ) < 4 * n := by
        have : (1 : ℤ) ≤ n := by exact_mod_cast hn
        linarith
      have hz4 : z ≤ 4 * n * z0 := by nlinarith [hz.2.2, hz0.2.1]
      have key : (2 : ℤ) ^ (jf z - jf z0) * 2 ^ jf z0 < (8 * n) * 2 ^ jf z0 := by
        rw [← pow_add, Nat.sub_add_cancel hle]
        calc (2 : ℤ) ^ jf z ≤ z := a1
          _ ≤ 4 * n * z0 := hz4
          _ < 4 * n * 2 ^ (jf z0 + 1) := mul_lt_mul_of_pos_left a2 hnpos
          _ = 8 * n * 2 ^ jf z0 := by ring
      have key2 : (2 : ℤ) ^ (jf z - jf z0) < 8 * n :=
        lt_of_mul_lt_mul_right key (by positivity)
      have key3 : 2 ^ (jf z - jf z0) ≤ 8 * n := by
        have : ((2 ^ (jf z - jf z0) : ℕ) : ℤ) < ((8 * n : ℕ) : ℤ) := by push_cast; exact key2
        exact_mod_cast this.le
      have := Nat.le_log_of_pow_le (by norm_num) key3
      rw [← hz0m]
      omega
    calc G.card ≤ (Icc (G.min' hne) (G.min' hne + Nat.log 2 (8 * n))).card := card_le_card hsub
      _ = Nat.log 2 (8 * n) + 1 := by simp; omega

/-- The quantity `K(n) = (⌈log₂ n⌉ + 1)(⌊log₂ (8n)⌋ + 1)`. -/
def Kbound (n : ℕ) : ℕ := (Nat.clog 2 n + 1) * (Nat.log 2 (8 * n) + 1)

lemma one_le_Kbound (n : ℕ) : 1 ≤ Kbound n := by
  unfold Kbound
  exact Nat.one_le_iff_ne_zero.2 (by positivity)

lemma Kbound_mono {m n : ℕ} (h : m ≤ n) : Kbound m ≤ Kbound n := by
  unfold Kbound
  exact Nat.mul_le_mul (Nat.add_le_add_right (Nat.clog_mono_right 2 h) 1)
    (Nat.add_le_add_right (Nat.log_mono_right (by omega)) 1)

/-- **Korsky's theorem for positive integers.** -/
theorem positive_case (A : Finset ℤ) (hpos : ∀ a ∈ A, 0 < a) (hn : 1 ≤ A.card) :
    ∃ B ⊆ A, IsSumFree B ∧ (A.card : ℝ) ≤ 4 * Kbound A.card * B.card := by
  classical
  set n := A.card with hndef
  obtain ⟨D₀, hD₀c, hD₀⟩ := bisection n A rfl
  -- add `a` itself to the list of distances of `a`
  set D : ℤ → Finset ℤ := fun a => insert a (D₀ a) with hD
  have hDc : ∀ a, (D a).card ≤ Nat.clog 2 n + 1 := fun a =>
    (card_insert_le _ _).trans (by have := hD₀c a; omega)
  set J : Finset ℕ := A.image jf with hJ
  -- forbidden dyadic intervals of `a`
  set F : ℤ → Finset ℕ := fun a =>
    ((A.filter (fun z => ∃ δ ∈ D a, δ ≤ 2 * (n : ℤ) * z ∧ z ≤ 2 * δ)).image jf).erase (jf a)
    with hF
  have hjJ : ∀ a ∈ A, jf a ∈ J := fun a ha => mem_image_of_mem _ ha
  have hFJ : ∀ a ∈ A, F a ⊆ J := by
    intro a _ k hk
    obtain ⟨z, hz, rfl⟩ := mem_image.1 (mem_of_mem_erase hk)
    exact mem_image_of_mem _ (mem_filter.1 hz).1
  have hjF : ∀ a ∈ A, jf a ∉ F a := fun a _ => notMem_erase _ _
  have hFK : ∀ a ∈ A, (F a).card ≤ Kbound n := by
    intro a _
    have hsub : F a ⊆ (D a).biUnion
        (fun δ => (A.filter (fun z => δ ≤ 2 * (n : ℤ) * z ∧ z ≤ 2 * δ)).image jf) := by
      intro k hk
      obtain ⟨z, hz, rfl⟩ := mem_image.1 (mem_of_mem_erase hk)
      rw [mem_filter] at hz
      obtain ⟨δ, hδ, h1, h2⟩ := hz.2
      exact mem_biUnion.2 ⟨δ, hδ, mem_image_of_mem _ (mem_filter.2 ⟨hz.1, h1, h2⟩)⟩
    calc (F a).card
        ≤ ((D a).biUnion (fun δ =>
            (A.filter (fun z => δ ≤ 2 * (n : ℤ) * z ∧ z ≤ 2 * δ)).image jf)).card :=
          card_le_card hsub
      _ ≤ ∑ δ ∈ D a,
            ((A.filter (fun z => δ ≤ 2 * (n : ℤ) * z ∧ z ≤ 2 * δ)).image jf).card :=
          card_biUnion_le
      _ ≤ ∑ _δ ∈ D a, (Nat.log 2 (8 * n) + 1) :=
          sum_le_sum (fun δ _ => card_window A hpos n hn δ)
      _ = (D a).card * (Nat.log 2 (8 * n) + 1) := by simp
      _ ≤ Kbound n := Nat.mul_le_mul_right _ (hDc a)
  obtain ⟨S, -, hS⟩ :=
    exists_good_selection A J jf F (Kbound n) (one_le_Kbound n) hjJ hFJ hjF hFK
  set B := A.filter (fun a => jf a ∈ S ∧ Disjoint (F a) S) with hB
  refine ⟨B, filter_subset _ _, ?_, hS⟩
  -- every possible selection is sum-free
  have hBA : B ⊆ A := filter_subset _ _
  have hBS : ∀ w ∈ B, jf w ∈ S := fun w hw => (mem_filter.1 hw).2.1
  -- the basic contradiction: `w` would lie in a forbidden interval of `a`
  have hFalse : ∀ a ∈ B, ∀ w ∈ B, jf w ≠ jf a →
      (∃ δ ∈ D a, δ ≤ 2 * (n : ℤ) * w ∧ w ≤ 2 * δ) → False := by
    intro a ha w hw hne hδ
    have hmem : jf w ∈ F a := by
      rw [hF]
      exact mem_erase.2 ⟨hne, mem_image_of_mem _ (mem_filter.2 ⟨hBA hw, hδ⟩)⟩
    exact disjoint_left.1 (mem_filter.1 ha).2.2 hmem (hBS w hw)
  intro b0 hb0 T hT hTc hsum
  have hTB : T ⊆ B := hT.trans (erase_subset _ _)
  have hTA : T ⊆ A := hTB.trans hBA
  have hTpos : ∀ x ∈ T, 0 < x := fun x hx => hpos x (hTA hx)
  have hTcard : T.card ≤ n := card_le_card hTA
  have hTne : T.Nonempty := by
    rw [← card_pos]
    omega
  set b1 := T.max' hTne with hb1
  have hb1T : b1 ∈ T := max'_mem _ _
  have hT1ne : (T.erase b1).Nonempty := by
    rw [← card_pos, card_erase_of_mem hb1T]
    omega
  set z := (T.erase b1).max' hT1ne with hz
  have hzT1 : z ∈ T.erase b1 := max'_mem _ _
  have hzT : z ∈ T := mem_of_mem_erase hzT1
  have hzb1 : z < b1 := lt_of_le_of_ne (le_max' _ _ hzT) (ne_of_mem_erase hzT1)
  have hzpos : 0 < z := hTpos z hzT
  have hb1pos : 0 < b1 := hTpos b1 hb1T
  have hsplit : ∑ x ∈ T, x = b1 + ∑ x ∈ T.erase b1, x := (add_sum_erase _ _ hb1T).symm
  have hd1 : z ≤ ∑ x ∈ T.erase b1, x :=
    single_le_sum (fun x hx => (hTpos x (mem_of_mem_erase hx)).le) hzT1
  have hd2 : ∑ x ∈ T.erase b1, x ≤ n * z := by
    have h1 : ∑ x ∈ T.erase b1, x ≤ (T.erase b1).card • z :=
      sum_le_card_nsmul _ _ _ (fun x hx => le_max' _ _ hx)
    have h2 : (T.erase b1).card ≤ n := (card_le_card (erase_subset _ _)).trans hTcard
    rw [nsmul_eq_mul] at h1
    have h3 : ((T.erase b1).card : ℤ) ≤ n := by exact_mod_cast h2
    nlinarith
  have hb0pos : 0 < b0 := hpos b0 (hBA hb0)
  have hb0z : 2 * z < b0 := by linarith
  have hb1b0 : b1 < b0 := by linarith
  have hb1B : b1 ∈ B := hTB hb1T
  have hzB : z ∈ B := hTB hzT
  have hjb0 : jf z ≠ jf b0 := by
    intro h
    have := lt_two_mul_of_jf_eq hzpos hb0pos h
    linarith
  have hnz : (0 : ℤ) ≤ n * z := by positivity
  by_cases hcase : jf b1 = jf z
  · -- `b1` and `z` lie in the same dyadic interval: use `δ = b0 ∈ D b0`
    have hb1lt : b1 < 2 * z := lt_two_mul_of_jf_eq hzpos hb1pos hcase.symm
    have hb0le : b0 ≤ n * b1 := by
      have h1 : ∑ x ∈ T, x ≤ T.card • b1 := sum_le_card_nsmul _ _ _ (fun x hx => le_max' _ _ hx)
      rw [nsmul_eq_mul] at h1
      have h3 : (T.card : ℤ) ≤ n := by exact_mod_cast hTcard
      nlinarith
    have hnpos : (0 : ℤ) < n := by exact_mod_cast hn
    refine hFalse b0 hb0 z hzB hjb0 ⟨b0, mem_insert_self _ _, ?_, by linarith⟩
    nlinarith
  · -- different dyadic intervals: use the bisection lemma for `b1 < b0`
    obtain ⟨δ, hδ, hδ1, hδ2⟩ := hD₀ b1 (hBA hb1B) b0 (hBA hb0) hb1b0
    have hδz : δ ≤ 2 * (n : ℤ) * z := by linarith
    have hzδ : z ≤ 2 * δ := by linarith
    rcases mem_union.1 hδ with h | h
    · exact hFalse b1 hb1B z hzB (Ne.symm hcase) ⟨δ, mem_insert_of_mem h, hδz, hzδ⟩
    · exact hFalse b0 hb0 z hzB hjb0 ⟨δ, mem_insert_of_mem h, hδz, hzδ⟩

end Erdos790
