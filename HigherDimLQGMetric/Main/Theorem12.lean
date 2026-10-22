import HigherDimLQGMetric.Main.Cor104

/-! # Theorem 1.2 from the named Phase A, Phase B, and Section 10 inputs -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace HigherDimLQGMetric

open HigherDimLFPP (Rd)

/-- Existence, kernel-independent LFPP convergence, and uniqueness of strong
metric assignments up to a positive deterministic constant. -/
theorem theorem12_of_inputs (hB3 : B3Goal)
    (hB2 : ∀ (d : ℕ) (κ : Rd d → ℝ) (ξ Q : ℝ),
      DGZ.RealEpsAdapterShape d κ ξ Q)
    (hE2 : Theorem16Shape) (h14s : Theorem14SharpStmt)
    (h102 : Cor102SharpShape) (h103 : Lemma103Shape)
    (hShell : ShellDecouplingFun) : Theorem12Stmt := by
  intro d ξ hd hξ hsub
  obtain ⟨D, c, hD, hstrong, _, hconv⟩ :=
    cor104_of_inputs hB3 hB2 hE2 h14s h102 h103 hShell d ξ hd hξ hsub
  constructor
  · exact ⟨D, hstrong, hconv⟩
  · intro D₁ D₂ hD₁ hD₂
    exact h14s d ξ (distExp d ξ) hd hξ hsub D₁ D₂
      (lemma101 (by omega : 2 ≤ d) hξ hD₁)
      (lemma101 (by omega : 2 ≤ d) hξ hD₂)

end HigherDimLQGMetric
