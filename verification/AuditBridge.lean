import Erdos790

open Filter

/-- Erdős Problem 790 restated with every definition written out inline. -/
theorem AuditBridge.intended :
    let l : ℕ → ℕ := fun n => sSup {m : ℕ | ∀ A : Finset ℤ, A.card = n →
      ∃ B ⊆ A, (∀ b ∈ B, ∀ S ⊆ B.erase b, 2 ≤ S.card → ∑ x ∈ S, x ≠ b) ∧ m ≤ B.card}
    Tendsto (fun n : ℕ => (l n : ℝ) / Real.sqrt n) atTop atTop ∧
      ¬ (∃ c > (0 : ℝ), ∀ᶠ n : ℕ in atTop, (l n : ℝ) < (n : ℝ) ^ (1 - c)) :=
  Erdos790.erdos_790

#print axioms AuditBridge.intended
