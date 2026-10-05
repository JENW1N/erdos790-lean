/-
Erdős Problem 790: the random-selection step, done as an exact weighted average over the
subsets of a finite set (product Bernoulli weights), so that no measure theory is needed.
-/
import Erdos790.Defs

open Finset

namespace Erdos790

/-- The product-Bernoulli weight of the subset `S` of `J` (each element kept with
probability `q`). -/
noncomputable def wt (q : ℝ) (J S : Finset ℕ) : ℝ := q ^ S.card * (1 - q) ^ (J.card - S.card)

lemma wt_nonneg {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q ≤ 1) (J S : Finset ℕ) : 0 ≤ wt q J S :=
  mul_nonneg (pow_nonneg hq0 _) (pow_nonneg (by linarith) _)

lemma wt_pos {q : ℝ} (hq0 : 0 < q) (hq1 : q < 1) (J S : Finset ℕ) : 0 < wt q J S :=
  mul_pos (pow_pos hq0 _) (pow_pos (by linarith) _)

/-- The weights form a probability distribution. -/
lemma sum_wt (q : ℝ) (J : Finset ℕ) : ∑ S ∈ J.powerset, wt q J S = 1 := by
  have h := Finset.sum_pow_mul_eq_add_pow q (1 - q) J
  simp only [wt]
  rw [h]
  simp

/-- The probability that `x` is kept and every element of `T` is discarded. -/
lemma sum_wt_filter (q : ℝ) (J T : Finset ℕ) (x : ℕ) (hx : x ∈ J) (hT : T ⊆ J)
    (hxT : x ∉ T) :
    ∑ S ∈ J.powerset.filter (fun S => x ∈ S ∧ Disjoint T S), wt q J S
      = q * (1 - q) ^ T.card := by
  classical
  set J' := J \ insert x T with hJ'
  have hsub : insert x T ⊆ J := insert_subset hx hT
  have hJ'c : J'.card + 1 + T.card = J.card := by
    rw [hJ', card_sdiff_of_subset hsub, card_insert_of_notMem hxT]
    have := card_le_card hsub
    rw [card_insert_of_notMem hxT] at this
    omega
  have hxJ' : x ∉ J' := by simp [hJ']
  have himage : J.powerset.filter (fun S => x ∈ S ∧ Disjoint T S)
      = J'.powerset.image (insert x) := by
    ext S
    simp only [mem_filter, mem_powerset, mem_image]
    constructor
    · rintro ⟨hSJ, hxS, hTS⟩
      refine ⟨S.erase x, ?_, insert_erase hxS⟩
      intro y hy
      rw [mem_erase] at hy
      rw [hJ', mem_sdiff, mem_insert]
      refine ⟨hSJ hy.2, ?_⟩
      rintro (h | h)
      · exact hy.1 h
      · exact disjoint_left.1 hTS h hy.2
    · rintro ⟨S', hS', rfl⟩
      refine ⟨insert_subset hx (hS'.trans sdiff_subset), mem_insert_self _ _, ?_⟩
      rw [disjoint_insert_right]
      refine ⟨hxT, ?_⟩
      rw [disjoint_left]
      intro y hyT hyS'
      have := hS' hyS'
      rw [hJ', mem_sdiff, mem_insert] at this
      exact this.2 (Or.inr hyT)
  rw [himage, sum_image]
  · have key : ∀ S' ∈ J'.powerset,
        wt q J (insert x S') = q * (1 - q) ^ T.card * wt q J' S' := by
      intro S' hS'
      rw [mem_powerset] at hS'
      have hxS' : x ∉ S' := fun h => hxJ' (hS' h)
      have hS'c : S'.card ≤ J'.card := card_le_card hS'
      simp only [wt, card_insert_of_notMem hxS']
      have : J.card - (S'.card + 1) = (J'.card - S'.card) + T.card := by omega
      rw [this, pow_succ, pow_add]
      ring
    rw [sum_congr rfl key, ← mul_sum, sum_wt, mul_one]
  · intro S₁ h₁ S₂ h₂ h
    rw [mem_coe, mem_powerset] at h₁ h₂
    have hx₁ : x ∉ S₁ := fun hh => hxJ' (h₁ hh)
    have hx₂ : x ∉ S₂ := fun hh => hxJ' (h₂ hh)
    have := congrArg (fun S => S.erase x) h
    simpa [erase_insert hx₁, erase_insert hx₂] using this

/-- **Averaging.**  Let `a ↦ j a` assign to each element of a finite set `A` an index in `J`,
and let `F a ⊆ J` be a set of at most `K` "forbidden" indices with `j a ∉ F a`.  Then for some
`S ⊆ J`, at least `|A| / (4K)` elements `a` satisfy `j a ∈ S` and `F a ∩ S = ∅`. -/
theorem exists_good_selection {α : Type*} [DecidableEq α] (A : Finset α) (J : Finset ℕ)
    (j : α → ℕ) (F : α → Finset ℕ) (K : ℕ) (hK : 1 ≤ K)
    (hjJ : ∀ a ∈ A, j a ∈ J) (hFJ : ∀ a ∈ A, F a ⊆ J) (hjF : ∀ a ∈ A, j a ∉ F a)
    (hFK : ∀ a ∈ A, (F a).card ≤ K) :
    ∃ S ⊆ J, (A.card : ℝ) ≤ 4 * K *
      (A.filter (fun a => j a ∈ S ∧ Disjoint (F a) S)).card := by
  classical
  set q : ℝ := 1 / (2 * K) with hq
  have hKpos : (0 : ℝ) < K := by exact_mod_cast hK
  have hK1 : (1 : ℝ) ≤ K := by exact_mod_cast hK
  have hq0 : 0 < q := by rw [hq]; positivity
  have hq1 : q < 1 := by
    rw [hq, div_lt_one (by positivity)]
    linarith
  have hqK : q * K = 1 / 2 := by
    rw [hq]
    field_simp
  -- expected number of kept elements
  have hexp : ∑ S ∈ J.powerset,
      wt q J S * ((A.filter (fun a => j a ∈ S ∧ Disjoint (F a) S)).card : ℝ)
        = ∑ a ∈ A, q * (1 - q) ^ (F a).card := by
    have : ∀ S ∈ J.powerset,
        wt q J S * ((A.filter (fun a => j a ∈ S ∧ Disjoint (F a) S)).card : ℝ)
          = ∑ a ∈ A, if j a ∈ S ∧ Disjoint (F a) S then wt q J S else 0 := by
      intro S _
      rw [card_filter, Nat.cast_sum, mul_sum]
      refine sum_congr rfl fun a _ => ?_
      split_ifs <;> simp
    rw [sum_congr rfl this, sum_comm]
    refine sum_congr rfl fun a ha => ?_
    rw [← sum_filter]
    exact sum_wt_filter q J (F a) (j a) (hjJ a ha) (hFJ a ha) (hjF a ha)
  have hlow : ∀ a ∈ A, q / 2 ≤ q * (1 - q) ^ (F a).card := by
    intro a ha
    have hb : 1 + ((F a).card : ℝ) * (-q) ≤ (1 + -q) ^ (F a).card :=
      one_add_mul_le_pow (by linarith) _
    have hc : ((F a).card : ℝ) ≤ K := by exact_mod_cast hFK a ha
    have : (1 : ℝ) / 2 ≤ (1 - q) ^ (F a).card := by
      have h1 : ((F a).card : ℝ) * q ≤ K * q := mul_le_mul_of_nonneg_right hc hq0.le
      rw [show (1 : ℝ) - q = 1 + -q by ring]
      nlinarith
    nlinarith
  have hsum_low : (A.card : ℝ) * (q / 2) ≤
      ∑ S ∈ J.powerset,
        wt q J S * ((A.filter (fun a => j a ∈ S ∧ Disjoint (F a) S)).card : ℝ) := by
    rw [hexp]
    calc (A.card : ℝ) * (q / 2) = ∑ _a ∈ A, q / 2 := by simp
      _ ≤ ∑ a ∈ A, q * (1 - q) ^ (F a).card := sum_le_sum hlow
  have hne : J.powerset.Nonempty := ⟨∅, empty_mem_powerset J⟩
  have hle : ∑ S ∈ J.powerset, wt q J S * ((A.card : ℝ) * (q / 2)) ≤
      ∑ S ∈ J.powerset,
        wt q J S * ((A.filter (fun a => j a ∈ S ∧ Disjoint (F a) S)).card : ℝ) := by
    rw [← sum_mul, sum_wt, one_mul]
    exact hsum_low
  obtain ⟨S, hS, hSle⟩ := exists_le_of_sum_le hne hle
  refine ⟨S, mem_powerset.1 hS, ?_⟩
  have hw := wt_pos hq0 hq1 J S
  have h2 : (A.card : ℝ) * (q / 2) ≤
      ((A.filter (fun a => j a ∈ S ∧ Disjoint (F a) S)).card : ℝ) :=
    le_of_mul_le_mul_left hSle hw
  have h3 : (4 * K : ℝ) * (q / 2) = 1 := by
    rw [hq]
    field_simp
    ring
  calc (A.card : ℝ) = (A.card : ℝ) * ((4 * K) * (q / 2)) := by rw [h3, mul_one]
    _ = 4 * K * ((A.card : ℝ) * (q / 2)) := by ring
    _ ≤ 4 * K * ((A.filter (fun a => j a ∈ S ∧ Disjoint (F a) S)).card : ℝ) :=
      mul_le_mul_of_nonneg_left h2 (by positivity)

end Erdos790
