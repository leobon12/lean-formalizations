import SupercriticalLQGUniqueness.B2.PfeAxioms.LocalObservableLFPPChain

 








set_option autoImplicit false
noncomputable section

open Set Topology

namespace SupercriticalLQGUniqueness.B2.PfeAxioms

theorem exists_uniform_lfpp_ball_data
    {ξ : ℝ} {φ : ℂ → ℝ} (hφ : Continuous φ)
    {K U : Set ℂ} (hK : IsCompact K) (hneK : K.Nonempty)
    (hU : IsOpen U) (hKU : K ⊆ U) :
    ∃ r : ℝ, 0 < r ∧ ∃ m : ℝ, 0 < m ∧
      ∀ x ∈ K, Metric.closedBall x r ⊆ U ∧
        ∀ u ∈ Metric.closedBall x r, m ≤ Real.exp (ξ * φ u) := by
  obtain ⟨r, hr, hthickU⟩ := hK.exists_cthickening_subset_open hU hKU
  let T : Set ℂ := Metric.cthickening r K
  have hT : IsCompact T := hK.cthickening
  have hTne : T.Nonempty := by
    obtain ⟨x, hx⟩ := hneK
    exact ⟨x, Metric.self_subset_cthickening K hx⟩
  have hE : Continuous (fun u : ℂ => Real.exp (ξ * φ u)) :=
    Real.continuous_exp.comp (continuous_const.mul hφ)
  obtain ⟨u₀, -, hmin⟩ := hT.exists_isMinOn hTne hE.continuousOn
  refine ⟨r, hr, Real.exp (ξ * φ u₀), Real.exp_pos _, ?_⟩
  intro x hx
  have hball : Metric.closedBall x r ⊆ T :=
    Metric.closedBall_subset_cthickening hx r
  exact ⟨hball.trans hthickU, fun u hu => hmin (hball hu)⟩

end SupercriticalLQGUniqueness.B2.PfeAxioms
