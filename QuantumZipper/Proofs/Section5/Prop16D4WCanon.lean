import QuantumZipper.Proofs.Section5.Prop16D4WRescale

/-!
# Proposition 1.6, D4⁺ʷ tool: area pairings of canonical local fields

Decision D24 (`DECISIONS.md`): the area measure of the canonical description of a locally good
field is the push-forward of its local area measure under `z ↦ z / a` (`a` the local scale), and
adding a continuous function `φ` multiplies the local area measure by `e^{γφ}`. Hence, with
`a = scaleParamOn γ x U` and `a' = scaleParamOn γ (ofFun φ + x) U`,

  `∫ f dμ_{canon(ofFun φ + x)} = ∫ e^{γφ(z)} f(z / a') dμ^U_x(z)`,
  `∫ f dμ_{canon x} = ∫ f(z / a) dμ^U_x(z)`

(`integral_canonicalOn_ofFun_add`, `integral_canonicalOn_of_locallyGood`). This is the identity
behind D24's "the area measure of the canonical field is the push-forward of `e^{γφ}·μ_Z` under
`w ↦ λw`".

Own argument (AGENT_GUIDE cost rule), from the local rescaling rule
(`Prop16D4WRescale.lean`) and the local rule (5.1) (`LocalRule.isVagueLimitOn_add_ofFun`).
-/

noncomputable section

open MeasureTheory Filter Topology Set Metric
open scoped ENNReal

namespace QuantumZipper

namespace Prop16Asm

open Prop16Area.G GoodSample RegClosure LocalRule

/-- Adding a function continuous on `V` preserves local goodness on `V`. -/
theorem isLocallyGoodOn_ofFun_add {γ : ℝ} {V : Set ℂ} {x : FieldSample}
    (hx : IsLocallyGoodOn γ V x) {φ : ℂ → ℝ} (hφ : ContinuousOn φ V) :
    IsLocallyGoodOn γ V (ofFun φ + x) := by
  obtain ⟨W, hWo, hWV, y, ψ, hy, hψ, h⟩ := hx
  exact ⟨W, hWo, hWV, y, fun z => ψ z + φ z, hy, hψ.add hφ, circAgree_ofFun_add hWV hψ hφ h⟩

/-- The local area measure of the canonical field of a locally good sample, at a positive scale. -/
theorem qAreaMeasureOn_canonicalOn_of_locallyGood {γ : ℝ} (hγ : 0 < γ) {V U : Set ℂ}
    {x : FieldSample} (hx : IsLocallyGoodOn γ V x) (hU : IsOpen U) (hUH : U ⊆ H) (hUV : U ⊆ V)
    (ha : 0 < scaleParamOn γ x U) :
    qAreaMeasureOn γ (canonicalOn γ x U) (canonicalDomainOn γ x U) =
      (qAreaMeasureOn γ x U).map fun z : ℂ => z / (scaleParamOn γ x U : ℂ) :=
  qAreaMeasureOn_rescale_of_locallyGood hγ hx hU hUH hUV ha

/-- Area pairings of the canonical field: `∫ f dμ_{canon x} = ∫ f(z / a) dμ^U_x`. -/
theorem integral_canonicalOn_of_locallyGood {γ : ℝ} (hγ : 0 < γ) {V U : Set ℂ}
    {x : FieldSample} (hx : IsLocallyGoodOn γ V x) (hU : IsOpen U) (hUH : U ⊆ H) (hUV : U ⊆ V)
    (ha : 0 < scaleParamOn γ x U) {f : ℂ → ℝ} (hf : Continuous f) :
    ∫ z, f z ∂qAreaMeasureOn γ (canonicalOn γ x U) (canonicalDomainOn γ x U) =
      ∫ z, f (z / (scaleParamOn γ x U : ℂ)) ∂qAreaMeasureOn γ x U := by
  rw [qAreaMeasureOn_canonicalOn_of_locallyGood hγ hx hU hUH hUV ha,
    integral_map (by fun_prop : Measurable fun z : ℂ => z / (scaleParamOn γ x U : ℂ)).aemeasurable
      hf.aestronglyMeasurable]

theorem restrict_compl_eq_zero (ν : Measure ℂ) {U : Set ℂ} (hU : MeasurableSet U) :
    ν.restrict U Uᶜ = 0 := by
  rw [Measure.restrict_apply hU.compl, compl_inter_self, measure_empty]

/-- Local rule (5.1) for locally good samples: `μ^U_{ofFun φ + x} = e^{γφ}·μ^U_x`, in integrated
form. -/
theorem integral_qAreaMeasureOn_ofFun_add {γ : ℝ} {V U : Set ℂ} {x : FieldSample}
    (hx : IsLocallyGoodOn γ V x) (hU : IsOpen U) (hUH : U ⊆ H) (hUV : U ⊆ V) {φ : ℂ → ℝ}
    (hφ : ContinuousOn φ V) (g : ℂ → ℝ) :
    ∫ z, g z ∂qAreaMeasureOn γ (ofFun φ + x) U =
      ∫ z, Real.exp (γ * φ z) * g z ∂qAreaMeasureOn γ x U := by
  obtain ⟨W, hWo, hWV, y, ψ, hy, hψ, h⟩ := hx
  have hUW : U ⊆ W := fun z hz => by rw [← hWV] at hUV; exact (hUV hz).1
  have hψ' : ContinuousOn ψ (W ∩ Hbar) := by rw [hWV]; exact hψ
  have hψφ : ContinuousOn (fun z => ψ z + φ z) (W ∩ Hbar) := by rw [hWV]; exact hψ.add hφ
  have hUV' : U ⊆ V := hUV
  rw [qAreaMeasureOn_eq_withDensity_of_agree hWo hy hψφ (circAgree_ofFun_add hWV hψ hφ h) hU hUH
      hUW, qAreaMeasureOn_eq_withDensity_of_agree hWo hy hψ' h hU hUH hUW,
    integral_withDensity_exp_of_continuousOn (w := fun z => γ * (ψ z + φ z)) hU
      (restrict_compl_eq_zero _ hU.measurableSet) (continuousOn_const.mul (hψφ.mono fun z hz => ⟨hUW hz, H_subset_Hbar (hUH hz)⟩)),
    integral_withDensity_exp_of_continuousOn (w := fun z => γ * ψ z) hU
      (restrict_compl_eq_zero _ hU.measurableSet) (continuousOn_const.mul (hψ'.mono fun z hz => ⟨hUW hz, H_subset_Hbar (hUH hz)⟩))]
  refine integral_congr_ae (Eventually.of_forall fun z => ?_)
  simp only [mul_add, Real.exp_add]
  ring

/-- **Area pairings of the canonical field of a perturbed sample**:
`∫ f dμ_{canon(ofFun φ + x)} = ∫ e^{γφ(z)} f(z / a') dμ^U_x(z)`, `a'` the local scale of
`ofFun φ + x`. -/
theorem integral_canonicalOn_ofFun_add {γ : ℝ} (hγ : 0 < γ) {V U : Set ℂ} {x : FieldSample}
    (hx : IsLocallyGoodOn γ V x) (hU : IsOpen U) (hUH : U ⊆ H) (hUV : U ⊆ V) {φ : ℂ → ℝ}
    (hφ : ContinuousOn φ V) (ha : 0 < scaleParamOn γ (ofFun φ + x) U) {f : ℂ → ℝ}
    (hf : Continuous f) :
    ∫ z, f z ∂qAreaMeasureOn γ (canonicalOn γ (ofFun φ + x) U)
        (canonicalDomainOn γ (ofFun φ + x) U) =
      ∫ z, Real.exp (γ * φ z) * f (z / (scaleParamOn γ (ofFun φ + x) U : ℂ))
        ∂qAreaMeasureOn γ x U := by
  rw [integral_canonicalOn_of_locallyGood hγ (isLocallyGoodOn_ofFun_add hx hφ) hU hUH hUV ha hf,
    integral_qAreaMeasureOn_ofFun_add hx hU hUH hUV hφ]

end Prop16Asm

end QuantumZipper
