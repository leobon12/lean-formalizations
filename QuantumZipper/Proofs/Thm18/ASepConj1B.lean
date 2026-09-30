import QuantumZipper.Proofs.Thm18.ASepConj1A

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# ASEP conjunct 1 (b): the rescaled field is exact once the continuous-radius limit exists

`conj1_of_limit`: let `U` be a regular sample with witness `F`, `a > 0`, `μ` a probability
measure on `ℍ̄` and `ν = μ.map (a ·)` compactly supported in `ℍ̄`. If
`∫ F(v, ρ) dν(v)` converges as `ρ → 0⁺` (all radii, not only dyadic ones), then
`evalReg (rescale U Q a) μ = rescale U Q a μ`: both sides equal the limit plus `Q log a`
(the smoothed rescaled field at scale `2^{-j}` is `F(a ·, a 2^{-j}) + Q log a`).
Own elementary bookkeeping.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology

namespace QuantumZipper
namespace ASep

/-- The raw value of the rescaled field at a folded circle. -/
theorem rescale_fc_eq {U : FieldSample} {F : ℂ × ℝ → ℝ} (hF : IsRegularWith U F) (Q : ℝ)
    {a : ℝ} (ha : 0 < a) {c : ℂ} (hc : c ∈ Hbar) {s : ℝ} (hs : 0 < s) :
    rescale U Q a (foldedCircle c s) = F ((a : ℂ) * c, a * s) + Q * Real.log a := by
  have hac : (a : ℂ) * c ∈ Hbar := by
    show 0 ≤ ((a : ℂ) * c).im
    have : 0 ≤ c.im := hc
    simpa using mul_nonneg ha.le this
  have hder : ∀ z : ℂ, Real.log ‖deriv (fun z : ℂ => (a : ℂ) * z) z‖ = Real.log a := by
    intro z
    have hd : deriv (fun z : ℂ => (a : ℂ) * z) z = (a : ℂ) := by
      rw [deriv_const_mul_field']; simp
    rw [hd, Complex.norm_real, Real.norm_of_nonneg ha.le]
  show evalReg U ((foldedCircle c s).map fun z => (a : ℂ) * z) +
      Q * ∫ z, Real.log ‖deriv (fun z : ℂ => (a : ℂ) * z) z‖ ∂foldedCircle c s = _
  simp only [hder]
  rw [Thm18Asm.foldedCircle_map_mul ha, hF.evalReg_fc_of_mem hac (mul_pos ha hs), integral_const,
    probReal_univ, one_smul]

/-- **Conjunct 1 from the continuous-radius limit.** -/
theorem conj1_of_limit {U : FieldSample} {F : ℂ × ℝ → ℝ} (hF : IsRegularWith U F) (Q : ℝ)
    {a : ℝ} (ha : 0 < a) {μ ν : Measure ℂ} [IsProbabilityMeasure μ]
    (hμν : μ.map (fun z => (a : ℂ) * z) = ν) (hμH : ∀ᵐ z ∂μ, z ∈ Hbar) {R₁ : ℝ}
    (hsupp : ν (CircleFubini.ballH R₁)ᶜ = 0) {L : ℝ}
    (hL : Tendsto (fun ρ => ∫ v, F (v, ρ) ∂ν) (𝓝[>] 0) (𝓝 L)) :
    evalReg (rescale U Q a) μ = rescale U Q a μ := by
  have hm : Measurable fun z : ℂ => (a : ℂ) * z := measurable_const_mul _
  have : IsProbabilityMeasure ν := by
    rw [← hμν]; exact (Measure.isProbabilityMeasure_map_iff hm.aemeasurable).2 inferInstance
  have hνH : ∀ᵐ v ∂ν, v ∈ Hbar :=
    (show ∀ᵐ v ∂ν, v ∈ CircleFubini.ballH R₁ from mem_ae_iff.2 hsupp).mono fun v hv => hv.2
  have hint : ∀ s : ℝ, 0 < s → Integrable (fun v => F (v, s)) ν := fun s hs =>
    FrostmanReg.integrable_of_continuousOn_frostman (CircleFubini.isCompact_ballH R₁)
      inter_subset_right hsupp (RegClosure.continuousOn_slice hF.1 hs)
  have hmap : ∀ s : ℝ, 0 < s → ∫ z, F ((a : ℂ) * z, s) ∂μ = ∫ v, F (v, s) ∂ν := by
    intro s hs
    rw [← hμν, integral_map hm.aemeasurable]
    rw [hμν]; exact (hint s hs).aestronglyMeasurable
  have hintμ : ∀ s : ℝ, 0 < s → Integrable (fun z => F ((a : ℂ) * z, s)) μ := by
    intro s hs
    have h := hint s hs
    rw [← hμν] at h
    exact h.comp_measurable hm
  -- smoothed rescaled field
  have havg : ∀ j : ℕ, ∀ z ∈ Hbar, avgReg (rescale U Q a) j z =
      F ((a : ℂ) * z, a * radius j) + Q * Real.log a := by
    intro j z hz
    have hs : 0 < a * radius j := mul_pos ha (radius_pos j)
    have hazH : (a : ℂ) * z ∈ Hbar := by
      show 0 ≤ ((a : ℂ) * z).im
      have : 0 ≤ z.im := hz
      simpa using mul_nonneg ha.le this
    refine Tendsto.limUnder_eq ?_
    have e : ∀ n : ℕ, rescale U Q a (foldedCircle (dyadicRoundC n z) (radius j)) =
        F ((a : ℂ) * dyadicRoundC n z, a * radius j) + Q * Real.log a := fun n =>
      rescale_fc_eq hF Q ha (CircleCont.dyadicRoundC_mem_Hbar hz n) (radius_pos j)
    simp_rw [e]
    refine Tendsto.add ?_ tendsto_const_nhds
    have hc := hF.1 ((a : ℂ) * z, a * radius j) ⟨hazH, hs⟩
    refine hc.tendsto.comp (tendsto_nhdsWithin_iff.2 ⟨?_, Eventually.of_forall fun n => ?_⟩)
    · exact ((tendsto_const_nhds.mul (RegClosure.tendsto_dyadicRoundC z)).prodMk_nhds
        tendsto_const_nhds)
    · refine ⟨?_, hs⟩
      show 0 ≤ ((a : ℂ) * dyadicRoundC n z).im
      have : 0 ≤ (dyadicRoundC n z).im := CircleCont.dyadicRoundC_mem_Hbar hz n
      simpa using mul_nonneg ha.le this
  have hlim_a : Tendsto (fun j : ℕ => a * radius j) atTop (𝓝[>] 0) := by
    refine tendsto_nhdsWithin_iff.2 ⟨?_, Eventually.of_forall fun j => mul_pos ha (radius_pos j)⟩
    have := (RegClosure.tendsto_radius_nhdsGT.mono_right nhdsWithin_le_nhds).const_mul a
    rwa [mul_zero] at this
  -- left side
  have hLHS : evalReg (rescale U Q a) μ = L + Q * Real.log a := by
    unfold evalReg
    refine Tendsto.limUnder_eq ?_
    have e : ∀ j : ℕ, ∫ z, avgReg (rescale U Q a) j z ∂μ =
        (∫ v, F (v, a * radius j) ∂ν) + Q * Real.log a := by
      intro j
      have hs : 0 < a * radius j := mul_pos ha (radius_pos j)
      rw [integral_congr_ae (hμH.mono fun z hz => havg j z hz),
        integral_add (hintμ _ hs) (integrable_const _), integral_const, probReal_univ, one_smul,
        hmap _ hs]
    simp_rw [e]
    exact (hL.comp hlim_a).add tendsto_const_nhds
  -- right side
  have hRHS : rescale U Q a μ = L + Q * Real.log a := by
    have hder : ∀ z : ℂ, Real.log ‖deriv (fun z : ℂ => (a : ℂ) * z) z‖ = Real.log a := by
      intro z
      have hd : deriv (fun z : ℂ => (a : ℂ) * z) z = (a : ℂ) := by
        rw [deriv_const_mul_field']; simp
      rw [hd, Complex.norm_real, Real.norm_of_nonneg ha.le]
    show evalReg U (μ.map fun z => (a : ℂ) * z) +
        Q * ∫ z, Real.log ‖deriv (fun z : ℂ => (a : ℂ) * z) z‖ ∂μ = _
    simp only [hder]
    rw [integral_const, probReal_univ, one_smul, hμν]
    congr 1
    unfold evalReg
    refine Tendsto.limUnder_eq ?_
    have e : ∀ j : ℕ, ∫ v, avgReg U j v ∂ν = ∫ v, F (v, radius j) ∂ν := fun j =>
      integral_congr_ae (hνH.mono fun v hv => hF.avgReg_eq j hv)
    simp_rw [e]
    exact hL.comp RegClosure.tendsto_radius_nhdsGT
  rw [hLHS, hRHS]

end ASep
end QuantumZipper
