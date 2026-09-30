import QuantumZipper.Proofs.Thm18.ASep3Fub
import QuantumZipper.Proofs.Thm18.ASep3Resc
import QuantumZipper.Proofs.LQG.RegularSample
import QuantumZipper.Proofs.LQG.AllOffsetsBasic

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# ASEP3 (step 11): the identity input of the scale run at a fixed parameter

* `ae_integral_evalReg_fc_eq_bind`: for a fixed probability measure `ν` carried by a compact
  subset of `ℍ̄` and a fixed radius `ρ > 0`, almost surely
  `∫ evalReg X (fc(z, ρ)) dν(z) = X(ν ⋆ fc(·, ρ))` (stochastic Fubini at radius `ρ`,
  `integral_circleAvg_ae_eq_bind_rho`, with the regularized circle values as the continuous version:
  `RegSample.ae_isRegularSample`, `AllOffsets.ae_evalReg_fc_eq`);
* **`ae_integral_avgReg_rescale_eq`**: for fixed `s > 0`, `j`, and such `ν`, almost surely
  `∫ avgReg (rescale X Q s) j dν = X((ν ⋆ fc(·, 2^{-j})).map (s ·)) + Q log s` — the identity
  `Φ = X(μ) + det` of the engine for the dilated circle-smoothed family (`genFam_bindνT_dil`,
  ASep3Psi.lean) at a fixed parameter.

Own bookkeeping (stochastic Fubini: Duplantier–Sheffield, Invent. Math. 185 (2011), §3).
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Metric

namespace QuantumZipper
namespace ASep

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {X : Ω → FieldSample}

/-- **Stochastic Fubini with the regularized circle values, at any radius.** -/
theorem ae_integral_evalReg_fc_eq_bind [IsProbabilityMeasure P] (hX : IsFreeGFFModConstH X P)
    {ρ : ℝ} (hρ : 0 < ρ) (ν : Measure ℂ) [IsProbabilityMeasure ν] {K : Set ℂ} (hK : IsCompact K)
    (hKH : K ⊆ Hbar) (hνK : ν Kᶜ = 0) :
    ∀ᵐ ω ∂P, ∫ z, evalReg (X ω) (foldedCircle z ρ) ∂ν =
      X ω (ν.bind fun w => foldedCircle w ρ) := by
  classical
  have hz₀ : (0 : ℂ) ∈ Hbar := show (0 : ℝ) ≤ (0 : ℂ).im by simp
  set Y : ℂ → Ω → ℝ := fun z ω => if IsRegularSample (X ω) then
    evalReg (X ω) (foldedCircle z ρ) - evalReg (X ω) (foldedCircle 0 ρ) else 0 with hYdef
  have hcont : ∀ ω, IsRegularSample (X ω) →
      ContinuousOn (fun z => evalReg (X ω) (foldedCircle z ρ)) Hbar := by
    intro ω ⟨F, hF⟩
    have hc : ContinuousOn (fun z : ℂ => F (z, ρ)) Hbar :=
      hF.1.comp (continuousOn_id.prodMk continuousOn_const) fun z hz => ⟨hz, hρ⟩
    exact hc.congr fun z hz => hF.evalReg_fc_of_mem hz hρ
  have hYc : ∀ ω, ContinuousOn (fun z => Y z ω) Hbar := by
    intro ω
    by_cases h : IsRegularSample (X ω)
    · simp only [hYdef, if_pos h]
      exact (hcont ω h).sub continuousOn_const
    · simp only [hYdef, if_neg h]
      exact continuousOn_const
  have hY : ∀ z ∈ Hbar, (fun ω => Y z ω) =ᵐ[P]
      fun ω => X ω (foldedCircle z ρ) - X ω (foldedCircle 0 ρ) := by
    intro z hz
    filter_upwards [RegSample.ae_isRegularSample hX, AllOffsets.ae_evalReg_fc_eq hX hz hρ,
      AllOffsets.ae_evalReg_fc_eq hX hz₀ hρ] with ω hreg h1 h2
    simp only [hYdef, if_pos hreg, h1, h2]
  have hF := integral_circleAvg_ae_eq_bind_rho hX hρ hz₀ hYc hY ν hK hKH hνK
  have hres : ν.restrict K = ν := Measure.restrict_eq_self_of_ae_mem (ae_iff.2 hνK)
  filter_upwards [hF, RegSample.ae_isRegularSample hX, AllOffsets.ae_evalReg_fc_eq hX hz₀ hρ]
    with ω h hreg h0
  have hint : Integrable (fun z => evalReg (X ω) (foldedCircle z ρ)) ν := by
    have := ((hcont ω hreg).mono hKH).integrableOn_compact (μ := ν) hK
    rwa [IntegrableOn, hres] at this
  have e1 : ∫ z, Y z ω ∂ν = ∫ z, evalReg (X ω) (foldedCircle z ρ) ∂ν -
      evalReg (X ω) (foldedCircle 0 ρ) := by
    simp only [hYdef, if_pos hreg]
    rw [integral_sub hint (integrable_const _), integral_const]
    simp
  have e2 : ν Set.univ • foldedCircle 0 ρ = foldedCircle 0 ρ := by
    rw [measure_univ, one_smul]
  rw [e1, e2, h0] at h
  linarith

/-- **The identity at a fixed parameter for the rescaled field.** -/
theorem ae_integral_avgReg_rescale_eq [IsProbabilityMeasure P] (hX : IsFreeGFFModConstH X P)
    (Q : ℝ) {s : ℝ} (hs : 0 < s) (j : ℕ) (ν : Measure ℂ) [IsProbabilityMeasure ν]
    {K : Set ℂ} (hK : IsCompact K) (hKH : K ⊆ Hbar) (hνK : ν Kᶜ = 0) :
    ∀ᵐ ω ∂P, ∫ z, avgReg (rescale (X ω) Q s) j z ∂ν =
      X ω ((RegCont.bindFc ν (radius j)).map fun z => (s : ℂ) * z) + Q * Real.log s := by
  have hm : Measurable fun z : ℂ => (s : ℂ) * z := measurable_const_mul _
  have : IsProbabilityMeasure (ν.map fun z => (s : ℂ) * z) :=
    (Measure.isProbabilityMeasure_map_iff hm.aemeasurable).2 inferInstance
  set K' : Set ℂ := (fun z => (s : ℂ) * z) '' K with hK'
  have hK'c : IsCompact K' := hK.image (continuous_const.mul continuous_id)
  have hK'H : K' ⊆ Hbar := by
    rintro _ ⟨z, hz, rfl⟩; exact RegClosure.mapsTo_mul_pos hs (hKH hz)
  have hνK' : (ν.map fun z => (s : ℂ) * z) K'ᶜ = 0 := by
    rw [Measure.map_apply hm hK'c.isClosed.measurableSet.compl]
    refine measure_mono_null (fun z hz => ?_) hνK
    exact fun hzK => hz ⟨z, hzK, rfl⟩
  have hρ : 0 < s * radius j := mul_pos hs (radius_pos j)
  filter_upwards [ae_integral_evalReg_fc_eq_bind hX hρ _ hK'c hK'H hνK',
    RegSample.ae_isRegularSample hX] with ω h hreg
  obtain ⟨F, hF⟩ := hreg
  have hae : ∀ᵐ z ∂ν, avgReg (rescale (X ω) Q s) j z =
      evalReg (X ω) (foldedCircle ((s : ℂ) * z) (s * radius j)) + Q * Real.log s := by
    have hKae : ∀ᵐ z ∂ν, z ∈ K := ae_iff.2 hνK
    filter_upwards [hKae] with z hz
    rw [(hF.rescale' Q hs).avgReg_eq j (hKH hz),
      hF.evalReg_fc_of_mem (RegClosure.mapsTo_mul_pos hs (hKH hz)) hρ]
  rw [integral_congr_ae hae]
  have hc : ContinuousOn (fun w => evalReg (X ω) (foldedCircle w (s * radius j))) Hbar := by
    have hc0 : ContinuousOn (fun w : ℂ => F (w, s * radius j)) Hbar :=
      hF.1.comp (continuousOn_id.prodMk continuousOn_const) fun w hw => ⟨hw, hρ⟩
    exact hc0.congr fun w hw => hF.evalReg_fc_of_mem hw hρ
  have hresK : (ν.map fun z => (s : ℂ) * z).restrict K' = ν.map fun z => (s : ℂ) * z :=
    Measure.restrict_eq_self_of_ae_mem (ae_iff.2 hνK')
  have hint' : Integrable (fun w => evalReg (X ω) (foldedCircle w (s * radius j)))
      (ν.map fun z => (s : ℂ) * z) := by
    have := (hc.mono hK'H).integrableOn_compact (μ := ν.map fun z => (s : ℂ) * z) hK'c
    rwa [IntegrableOn, hresK] at this
  have hint : Integrable (fun z => evalReg (X ω) (foldedCircle ((s : ℂ) * z) (s * radius j))) ν :=
    (integrable_map_measure hint'.aestronglyMeasurable hm.aemeasurable).1 hint'
  rw [integral_add hint (integrable_const _), integral_const, probReal_univ, one_smul]
  have e := integral_map (μ := ν) hm.aemeasurable hint'.aestronglyMeasurable
  rw [← e, h, ← bindFc_map_mul ν hs]

end ASep
end QuantumZipper
