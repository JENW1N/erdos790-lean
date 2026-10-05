/-
Erdős Problem 790 (JSP-000649): main results.

* `Erdos790.korsky` : there is `c > 0` with `l n ≥ c n / (log n)²` for all `n ≥ 2`
  (S. Korsky, 13 September 2026; conjecture of Choi–Komlós–Szemerédi, `l n ≥ n^{1-o(1)}`).
* `Erdos790.erdos_790_part_i`  : `l n / √n → ∞` (Erdős's first question: **yes**).
* `Erdos790.erdos_790_part_ii` : there is **no** `c > 0` with `l n < n^{1-c}` for all large `n`
  (Erdős's second question: **no**).
* `Erdos790.erdos_790_exponent` : `log l(n) / log n → 1`, i.e. `l n = n^{1+o(1)}`.
-/
import Erdos790.Positive

open Finset Filter Asymptotics Real
open scoped Topology

namespace Erdos790

/-- Negation preserves sum-freeness. -/
lemma IsSumFree.image_neg {B : Finset ℤ} (hB : IsSumFree B) : IsSumFree (B.image (fun x => -x)) := by
  classical
  intro b hb S hS hcard hsum
  have hinj : Function.Injective (fun x : ℤ => -x) := neg_injective
  have hbB : -b ∈ B := by
    obtain ⟨y, hy, rfl⟩ := mem_image.1 hb
    simpa using hy
  refine hB (-b) hbB (S.image (fun x => -x)) ?_ ?_ ?_
  · intro y hy
    obtain ⟨x, hx, rfl⟩ := mem_image.1 hy
    have hx' := hS hx
    rw [mem_erase] at hx' ⊢
    refine ⟨fun h => hx'.1 (neg_injective h), ?_⟩
    obtain ⟨w, hw, rfl⟩ := mem_image.1 hx'.2
    simpa using hw
  · rwa [card_image_of_injective _ hinj]
  · rw [sum_image (fun x _ y _ h => hinj h), sum_neg_distrib, hsum]

/-- **Korsky's theorem** for arbitrary finite sets of integers. -/
theorem korsky_finset (A : Finset ℤ) (hn : 2 ≤ A.card) :
    ∃ B ⊆ A, IsSumFree B ∧ ((A.card : ℝ) - 1) ≤ 8 * Kbound A.card * B.card := by
  classical
  set P := A.filter (fun x => 0 < x) with hP
  set N := A.filter (fun x => x < 0) with hN
  have hcover : A.card ≤ P.card + N.card + 1 := by
    have hsub : A ⊆ (P ∪ N) ∪ {0} := by
      intro x hx
      rcases lt_trichotomy x 0 with h | h | h
      · simp [hN, hx, h]
      · simp [h]
      · simp [hP, hx, h]
    calc A.card ≤ ((P ∪ N) ∪ {0}).card := card_le_card hsub
      _ ≤ (P ∪ N).card + 1 := by
          have := card_union_le (P ∪ N) {0}
          simpa using this
      _ ≤ P.card + N.card + 1 := by
          have := card_union_le P N
          omega
  have hKpos : (0 : ℝ) ≤ 8 * Kbound A.card := by positivity
  rcases le_or_gt N.card P.card with hNP | hPN
  · -- many positive elements
    have hP1 : 1 ≤ P.card := by omega
    obtain ⟨B, hBP, hBsf, hBc⟩ := positive_case P (fun x hx => (mem_filter.1 hx).2) hP1
    refine ⟨B, hBP.trans (filter_subset _ _), hBsf, ?_⟩
    have hKm : (Kbound P.card : ℝ) ≤ Kbound A.card := by
      exact_mod_cast Kbound_mono (card_le_card (filter_subset _ _))
    have h2P : (A.card : ℝ) - 1 ≤ 2 * P.card := by
      have : A.card ≤ 2 * P.card + 1 := by omega
      have : (A.card : ℝ) ≤ 2 * P.card + 1 := by exact_mod_cast this
      linarith
    have hB0 : (0 : ℝ) ≤ B.card := by positivity
    calc (A.card : ℝ) - 1 ≤ 2 * P.card := h2P
      _ ≤ 2 * (4 * Kbound P.card * B.card) := by linarith
      _ ≤ 2 * (4 * Kbound A.card * B.card) := by
          have := mul_le_mul_of_nonneg_right hKm hB0
          nlinarith
      _ = 8 * Kbound A.card * B.card := by ring
  · -- many negative elements: negate them
    set N' := N.image (fun x => -x) with hN'
    have hinj : Function.Injective (fun x : ℤ => -x) := neg_injective
    have hN'c : N'.card = N.card := card_image_of_injective _ hinj
    have hN'pos : ∀ x ∈ N', 0 < x := by
      intro x hx
      obtain ⟨y, hy, rfl⟩ := mem_image.1 hx
      have := (mem_filter.1 hy).2
      linarith
    have hN1 : 1 ≤ N'.card := by omega
    obtain ⟨B', hB'N', hB'sf, hB'c⟩ := positive_case N' hN'pos hN1
    refine ⟨B'.image (fun x => -x), ?_, hB'sf.image_neg, ?_⟩
    · intro x hx
      obtain ⟨y, hy, rfl⟩ := mem_image.1 hx
      obtain ⟨w, hw, rfl⟩ := mem_image.1 (hB'N' hy)
      simpa using (mem_filter.1 hw).1
    · rw [card_image_of_injective _ hinj]
      have hKm : (Kbound N'.card : ℝ) ≤ Kbound A.card := by
        rw [hN'c]
        exact_mod_cast Kbound_mono (card_le_card (filter_subset _ _))
      have h2N : (A.card : ℝ) - 1 ≤ 2 * N'.card := by
        have : A.card ≤ 2 * N'.card + 1 := by omega
        have : (A.card : ℝ) ≤ 2 * N'.card + 1 := by exact_mod_cast this
        linarith
      have hB0 : (0 : ℝ) ≤ B'.card := by positivity
      calc (A.card : ℝ) - 1 ≤ 2 * N'.card := h2N
        _ ≤ 2 * (4 * Kbound N'.card * B'.card) := by linarith
        _ ≤ 2 * (4 * Kbound A.card * B'.card) := by
            have := mul_le_mul_of_nonneg_right hKm hB0
            nlinarith
        _ = 8 * Kbound A.card * B'.card := by ring

/-- Lower bound for `l n` with the explicit polylogarithmic factor `K(n)`. -/
theorem l_lower (n : ℕ) (hn : 2 ≤ n) : ((n : ℝ) - 1) ≤ 8 * Kbound n * l n := by
  have hK : (0 : ℝ) < 8 * Kbound n := by
    have := one_le_Kbound n
    have : (1 : ℝ) ≤ Kbound n := by exact_mod_cast this
    linarith
  set m := ⌈((n : ℝ) - 1) / (8 * Kbound n)⌉₊ with hm
  have hmadm : m ∈ admissible n := by
    intro A hA
    obtain ⟨B, hBA, hBsf, hBc⟩ := korsky_finset A (by omega)
    refine ⟨B, hBA, hBsf, ?_⟩
    rw [hm, Nat.ceil_le, div_le_iff₀ hK]
    rw [hA] at hBc
    linarith
  have hml : (m : ℝ) ≤ l n := by exact_mod_cast le_l hmadm
  have h1 : ((n : ℝ) - 1) / (8 * Kbound n) ≤ m := Nat.le_ceil _
  rw [div_le_iff₀ hK] at h1
  nlinarith

/-! ### Bounding `K(n)` by a power of `log n` -/

lemma clog_le_log_succ (n : ℕ) : Nat.clog 2 n ≤ Nat.log 2 n + 1 := by
  rcases Nat.lt_or_ge n 2 with hn | hn
  · interval_cases n <;> simp
  · have h := Nat.pow_pred_clog_lt_self (b := 2) (by norm_num) (by omega : 1 < n)
    have := Nat.le_log_of_pow_le (by norm_num) h.le
    rw [Nat.pred_eq_sub_one] at this
    omega

lemma log_eight_mul_le (n : ℕ) (hn : 1 ≤ n) : Nat.log 2 (8 * n) ≤ Nat.log 2 n + 3 := by
  have h1 : 8 * n < 2 ^ (Nat.log 2 n + 4) := by
    have := Nat.lt_pow_succ_log_self (b := 2) (by norm_num) n
    rw [pow_add]
    norm_num
    omega
  have h2 := Nat.pow_log_le_self 2 (show 8 * n ≠ 0 by omega)
  have h3 : 2 ^ Nat.log 2 (8 * n) < 2 ^ (Nat.log 2 n + 4) := lt_of_le_of_lt h2 h1
  have := (Nat.pow_lt_pow_iff_right (by norm_num : 1 < 2)).1 h3
  omega

lemma natLog_le_real (n : ℕ) (hn : 1 ≤ n) :
    (Nat.log 2 n : ℝ) ≤ Real.log n / Real.log 2 := by
  have h := Nat.pow_log_le_self 2 (show n ≠ 0 by omega)
  have h' : ((2 : ℝ)) ^ Nat.log 2 n ≤ n := by exact_mod_cast h
  have hlog : Real.log ((2 : ℝ) ^ Nat.log 2 n) ≤ Real.log n :=
    Real.log_le_log (by positivity) h'
  rw [Real.log_pow] at hlog
  rw [le_div_iff₀ (Real.log_pos (by norm_num))]
  exact hlog

lemma Kbound_le (n : ℕ) (hn : 1 ≤ n) :
    (Kbound n : ℝ) ≤ (Real.log n / Real.log 2 + 4) ^ 2 := by
  have h1 := clog_le_log_succ n
  have h2 := log_eight_mul_le n hn
  have h3 := natLog_le_real n hn
  have hL0 : (0 : ℝ) ≤ Nat.log 2 n := by positivity
  unfold Kbound
  have e1 : ((Nat.clog 2 n + 1 : ℕ) : ℝ) ≤ Nat.log 2 n + 2 := by
    have : Nat.clog 2 n + 1 ≤ Nat.log 2 n + 2 := by omega
    exact_mod_cast this
  have e2 : ((Nat.log 2 (8 * n) + 1 : ℕ) : ℝ) ≤ Nat.log 2 n + 4 := by
    have : Nat.log 2 (8 * n) + 1 ≤ Nat.log 2 n + 4 := by omega
    exact_mod_cast this
  push_cast
  push_cast at e1 e2
  calc ((Nat.clog 2 n : ℝ) + 1) * ((Nat.log 2 (8 * n) : ℝ) + 1)
      ≤ ((Nat.log 2 n : ℝ) + 4) * ((Nat.log 2 n : ℝ) + 4) := by
        apply mul_le_mul (by linarith) e2 (by positivity) (by positivity)
    _ ≤ (Real.log n / Real.log 2 + 4) * (Real.log n / Real.log 2 + 4) := by
        apply mul_le_mul (by linarith) (by linarith) (by positivity) (by linarith)
    _ = (Real.log n / Real.log 2 + 4) ^ 2 := by ring

/-- **Korsky's theorem** (Erdős Problem 790): `l n ≥ c n / (log n)²` for all `n ≥ 2`. -/
theorem korsky : ∃ c > 0, ∀ n : ℕ, 2 ≤ n → c * n / Real.log n ^ 2 ≤ l n := by
  -- For `n ≥ 2`: `log n ≥ log 2`, so `log n / log 2 + 4 ≤ 5 log n / log 2`.
  set L2 := Real.log 2 with hL2
  have hL2pos : 0 < L2 := Real.log_pos (by norm_num)
  refine ⟨L2 ^ 2 / 400, by positivity, ?_⟩
  intro n hn
  have hn1 : (1 : ℝ) ≤ n - 1 + 0 := by
    have : (2 : ℝ) ≤ n := by exact_mod_cast hn
    linarith
  have hlogn : L2 ≤ Real.log n := Real.log_le_log (by norm_num) (by exact_mod_cast hn)
  have hlogpos : 0 < Real.log n := lt_of_lt_of_le hL2pos hlogn
  have hK := Kbound_le n (by omega)
  have hl := l_lower n hn
  have hK' : (Kbound n : ℝ) ≤ 25 * Real.log n ^ 2 / L2 ^ 2 := by
    have : Real.log n / L2 + 4 ≤ 5 * Real.log n / L2 := by
      rw [div_add' _ _ _ hL2pos.ne', div_le_div_iff_of_pos_right hL2pos]
      linarith
    have h0 : 0 ≤ Real.log n / L2 + 4 := by positivity
    calc (Kbound n : ℝ) ≤ (Real.log n / L2 + 4) ^ 2 := hK
      _ ≤ (5 * Real.log n / L2) ^ 2 := pow_le_pow_left₀ h0 this 2
      _ = 25 * Real.log n ^ 2 / L2 ^ 2 := by ring
  have hlpos : (0 : ℝ) ≤ l n := by positivity
  have hnn : (n : ℝ) ≤ 2 * ((n : ℝ) - 1) := by
    have : (2 : ℝ) ≤ n := by exact_mod_cast hn
    linarith
  rw [div_le_iff₀ (by positivity)]
  have step : (n : ℝ) ≤ 16 * Kbound n * l n := by nlinarith
  have step2 : (16 * Kbound n * l n : ℝ) ≤ 16 * (25 * Real.log n ^ 2 / L2 ^ 2) * l n := by
    have := mul_le_mul_of_nonneg_right hK' hlpos
    nlinarith
  have : L2 ^ 2 / 400 * n ≤ L2 ^ 2 / 400 * (16 * (25 * Real.log n ^ 2 / L2 ^ 2) * l n) :=
    mul_le_mul_of_nonneg_left (step.trans step2) (by positivity)
  calc L2 ^ 2 / 400 * n ≤ L2 ^ 2 / 400 * (16 * (25 * Real.log n ^ 2 / L2 ^ 2) * l n) := this
    _ = l n * Real.log n ^ 2 := by field_simp; ring

/-! ### Consequences: the answers to Erdős's questions -/

/-- `(log x)² = o(x^ε)`. -/
lemma log_sq_isLittleO (ε : ℝ) (hε : 0 < ε) :
    (fun x : ℝ => Real.log x ^ 2) =o[atTop] (fun x : ℝ => x ^ ε) := by
  have h := isLittleO_log_rpow_rpow_atTop (2 : ℝ) hε
  refine h.congr' ?_ (Eventually.of_forall fun _ => rfl)
  filter_upwards [eventually_gt_atTop 1] with x hx
  have : 0 ≤ Real.log x := Real.log_nonneg hx.le
  rw [← Real.rpow_natCast]
  norm_num

/-- For every `ε > 0`, eventually `l n ≥ n^{1-ε}` (the Choi–Komlós–Szemerédi conjecture). -/
theorem eventually_rpow_le_l (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop, (n : ℝ) ^ (1 - ε) ≤ l n := by
  obtain ⟨c, hc, hkor⟩ := korsky
  have hlo := (log_sq_isLittleO ε hε).comp_tendsto tendsto_natCast_atTop_atTop
  have hev := hlo.def (show 0 < c by exact hc)
  filter_upwards [hev, eventually_ge_atTop 2] with n hn hn2
  simp only [Function.comp, Real.norm_eq_abs] at hn
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hlog : 0 < Real.log n := Real.log_pos (by exact_mod_cast (show 1 < n by omega))
  rw [abs_of_nonneg (by positivity), abs_of_nonneg (by positivity)] at hn
  have hk := hkor n hn2
  -- `c n / (log n)^2 ≥ n / n^ε = n^{1-ε}`
  have hrpow : (n : ℝ) ^ (1 - ε) * (n : ℝ) ^ ε = n := by
    rw [← Real.rpow_add hnpos]
    simp
  have hnε : 0 < (n : ℝ) ^ ε := Real.rpow_pos_of_pos hnpos ε
  have h1 : (n : ℝ) ^ (1 - ε) ≤ c * n / Real.log n ^ 2 := by
    rw [le_div_iff₀ (by positivity)]
    calc (n : ℝ) ^ (1 - ε) * Real.log n ^ 2 ≤ (n : ℝ) ^ (1 - ε) * (c * (n : ℝ) ^ ε) :=
          mul_le_mul_of_nonneg_left hn (by positivity)
      _ = c * ((n : ℝ) ^ (1 - ε) * (n : ℝ) ^ ε) := by ring
      _ = c * n := by rw [hrpow]
  exact h1.trans hk

/-- **Erdős Problem 790, first question: yes.**  `l(n) n^{-1/2} → ∞`. -/
theorem erdos_790_part_i :
    Tendsto (fun n : ℕ => (l n : ℝ) / Real.sqrt n) atTop atTop := by
  have h := eventually_rpow_le_l (1 / 4) (by norm_num)
  have hpow : Tendsto (fun n : ℕ => (n : ℝ) ^ (1 / 4 : ℝ)) atTop atTop :=
    (tendsto_rpow_atTop (by norm_num)).comp tendsto_natCast_atTop_atTop
  refine tendsto_atTop_mono' atTop ?_ hpow
  filter_upwards [h, eventually_ge_atTop 1] with n hn hn1
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hsq : Real.sqrt n = (n : ℝ) ^ (1 / 2 : ℝ) := Real.sqrt_eq_rpow n
  rw [hsq, le_div_iff₀ (Real.rpow_pos_of_pos hnpos _), ← Real.rpow_add hnpos]
  norm_num at hn ⊢
  exact hn

/-- **Erdős Problem 790, second question: no.**  There is no `c > 0` such that
`l(n) < n^{1-c}` for all sufficiently large `n`. -/
theorem erdos_790_part_ii :
    ¬ ∃ c > (0 : ℝ), ∀ᶠ n : ℕ in atTop, (l n : ℝ) < (n : ℝ) ^ (1 - c) := by
  rintro ⟨c, hc, hev⟩
  obtain ⟨n, h1, h2⟩ := (hev.and (eventually_rpow_le_l c hc)).exists
  linarith

/-- **Erdős Problem 790, the order of growth: `l n = n^{1+o(1)}`.** -/
theorem erdos_790_exponent :
    Tendsto (fun n : ℕ => Real.log (l n) / Real.log n) atTop (𝓝 1) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨N, hN⟩ := eventually_atTop.1
    ((eventually_rpow_le_l (ε / 2) (by linarith)).and (eventually_ge_atTop 2))
  refine ⟨N, fun n hn => ?_⟩
  obtain ⟨hl, hn2⟩ := hN n hn
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hlog : 0 < Real.log n := Real.log_pos (by exact_mod_cast (show 1 < n by omega))
  have hlpos : (0 : ℝ) < l n := lt_of_lt_of_le (Real.rpow_pos_of_pos hnpos _) hl
  have hup : Real.log (l n) ≤ Real.log n :=
    Real.log_le_log hlpos (by exact_mod_cast l_le n)
  have hdown : (1 - ε / 2) * Real.log n ≤ Real.log (l n) := by
    have := Real.log_le_log (Real.rpow_pos_of_pos hnpos _) hl
    rwa [Real.log_rpow hnpos] at this
  rw [Real.dist_eq, abs_lt]
  constructor
  · rw [lt_sub_iff_add_lt, lt_div_iff₀ hlog]
    nlinarith
  · rw [sub_lt_iff_lt_add, div_lt_iff₀ hlog]
    nlinarith

/-- **Erdős Problem 790** — complete answer to both questions. -/
theorem erdos_790 :
    Tendsto (fun n : ℕ => (l n : ℝ) / Real.sqrt n) atTop atTop ∧
      ¬ (∃ c > (0 : ℝ), ∀ᶠ n : ℕ in atTop, (l n : ℝ) < (n : ℝ) ^ (1 - c)) :=
  ⟨erdos_790_part_i, erdos_790_part_ii⟩

end Erdos790
