import QuantumZipper.Proofs.Zipper.F1PStarShiftRegRed
import QuantumZipper.Proofs.Zipper.WedgeUnzipB3d

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# Theorem 1.3, node F1 (D29): deterministic transport of the continuum limit to `P_*` fields

Sheffield, *Conformal weldings of random surfaces*, arXiv:1012.4797, §5.1 (rule (5.1): adding a
constant to a field) and §5.4 (pp. 70–72, "by scaling"). Own elementary bookkeeping.

A `P_*` field `Y` is (core P) `avgReg`-equal to `rescale Z Q b`, `Z` the unscaled wedge field and
`b = scaleParam γ Z`. Core W-C gives the continuum limit of the smoothed pairings of `Z` along
the pushed circles of the unscaled driver `W''`. This file transports it:

* `ContData x μ`: the smoothed pairings `ρ ↦ ∫ evalReg x (fc(u, ρ)) dμ(u)` are integrable and
  converge as `ρ → 0⁺`;
* `contData_of_dilate`: if `evalReg x (fc(u, ρ)) = evalReg Z (fc(b u, b ρ)) + C` on `ℍ̄`, the
  continuum limit of `Z` along `b_* μ` gives that of `x` along `μ`;
* `regShift_of_contData`: for a regular sample the continuum limit gives `E1.RegShift`
  (so `evalReg` commutes with additive constants there);
* `evalReg_fc_of_avgReg_rescale`: the regularized circle values of a field `avgReg`-equal to
  `rescale Z Q b + k`.
-/

noncomputable section

open MeasureTheory Filter Set Function
open scoped Topology

namespace QuantumZipper
namespace F1

/-- The continuum limit of the smoothed pairings of `x` along `μ` (the data of core W-C). -/
def ContData (x : FieldSample) (μ : Measure ℂ) : Prop :=
  (∀ ρ : ℝ, 0 < ρ → Integrable (fun u => evalReg x (foldedCircle u ρ)) μ) ∧
    ∃ L : ℝ, Tendsto (fun ρ => ∫ u, evalReg x (foldedCircle u ρ) ∂μ) (𝓝[>] 0) (𝓝 L)

/-- `ρ ↦ b ρ` preserves `𝓝[>] 0` for `b > 0`. -/
theorem tendsto_mul_nhdsGT_zero {b : ℝ} (hb : 0 < b) :
    Tendsto (fun ρ : ℝ => b * ρ) (𝓝[>] 0) (𝓝[>] 0) := by
  refine tendsto_nhdsWithin_iff.2 ⟨?_, ?_⟩
  · have : Tendsto (fun ρ : ℝ => b * ρ) (𝓝 0) (𝓝 (b * 0)) :=
      (continuous_const.mul continuous_id).tendsto 0
    rw [mul_zero] at this
    exact this.mono_left nhdsWithin_le_nhds
  · filter_upwards [self_mem_nhdsWithin] with ρ (hρ : 0 < ρ)
    exact mul_pos hb hρ

/-- **Continuum limit through a dilation.** -/
theorem contData_of_dilate {x Z : FieldSample} {b C : ℝ} (hb : 0 < b) {μ : Measure ℂ}
    [IsFiniteMeasure μ] (hμ : ∀ᵐ u ∂μ, u ∈ Hbar)
    (hx : ∀ u ∈ Hbar, ∀ ρ : ℝ, 0 < ρ →
      evalReg x (foldedCircle u ρ) = evalReg Z (foldedCircle ((b : ℂ) * u) (b * ρ)) + C)
    (hZ : ContData Z (μ.map fun z => (b : ℂ) * z)) : ContData x μ := by
  obtain ⟨hint, L, hL⟩ := hZ
  have hm : Measurable (fun z : ℂ => (b : ℂ) * z) := measurable_const_mul _
  have hae : ∀ ρ : ℝ, 0 < ρ → (fun u => evalReg x (foldedCircle u ρ)) =ᵐ[μ]
      fun u => evalReg Z (foldedCircle ((b : ℂ) * u) (b * ρ)) + C := fun ρ hρ =>
    hμ.mono fun u hu => hx u hu ρ hρ
  have hi : ∀ ρ : ℝ, 0 < ρ →
      Integrable (fun u => evalReg Z (foldedCircle ((b : ℂ) * u) (b * ρ))) μ := fun ρ hρ =>
    (hint _ (mul_pos hb hρ)).comp_measurable hm
  have heq : ∀ ρ : ℝ, 0 < ρ → ∫ u, evalReg x (foldedCircle u ρ) ∂μ =
      ∫ u, evalReg Z (foldedCircle u (b * ρ)) ∂(μ.map fun z => (b : ℂ) * z) + μ.real univ * C :=
    fun ρ hρ => by
      rw [integral_congr_ae (hae ρ hρ), integral_add (hi ρ hρ) (integrable_const C),
        integral_const, smul_eq_mul,
        integral_map hm.aemeasurable (hint _ (mul_pos hb hρ)).aestronglyMeasurable]
  refine ⟨fun ρ hρ => ((hi ρ hρ).add (integrable_const C)).congr (hae ρ hρ).symm,
    L + μ.real univ * C, ?_⟩
  have h1 := (hL.comp (tendsto_mul_nhdsGT_zero hb)).add_const (μ.real univ * C)
  refine h1.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with ρ (hρ : 0 < ρ)
  exact (heq ρ hρ).symm

/-- **`RegShift` from the continuum limit**, for a regular sample. -/
theorem regShift_of_contData {x : FieldSample} (hx : IsRegularSample x) {μ : Measure ℂ}
    (hμ : ∀ᵐ u ∂μ, u ∈ Hbar) (h : ContData x μ) : E1.RegShift x μ := by
  obtain ⟨F, hF⟩ := hx
  have hF' := hF.congr_evalReg
  obtain ⟨hint, L, hL⟩ := h
  have hae : ∀ k : ℕ, (fun u => avgReg x k u) =ᵐ[μ]
      fun u => evalReg x (foldedCircle u (radius k)) :=
    fun k => hμ.mono fun u hu => hF'.avgReg_eq k hu
  refine ⟨Eventually.of_forall fun z k => ⟨_, tendsto_raw_of_isRegularWith hF k z⟩,
    fun k => (hint _ (radius_pos k)).congr (hae k).symm, L, ?_⟩
  refine (hL.comp RegClosure.tendsto_radius_nhdsGT).congr fun k => ?_
  exact (integral_congr_ae (hae k)).symm

/-- **Regularized circle values of a field `avgReg`-equal to `rescale Z Q b + k`.** -/
theorem evalReg_fc_of_avgReg_rescale {x Z : FieldSample} (hZ : IsRegularSample Z) (Q : ℝ)
    {b : ℝ} (hb : 0 < b) (k : ℝ) (h : avgReg x = avgReg (addConst (rescale Z Q b) k))
    {u : ℂ} (hu : u ∈ Hbar) {ρ : ℝ} (hρ : 0 < ρ) :
    evalReg x (foldedCircle u ρ) =
      evalReg Z (foldedCircle ((b : ℂ) * u) (b * ρ)) + (Q * Real.log b + k) := by
  obtain ⟨F, hF⟩ := hZ
  have hW := (hF.congr_evalReg.rescale' Q hb).addConst' k
  rw [Factorization.evalReg_congr h, hW.evalReg_fc_of_mem hu hρ]
  ring

/-- The pushed folded circle `(fc(d, r)).map (f_s⁻¹)` is a finite measure carried by `ℍ̄`. -/
theorem fc_map_fwdMapInv_props {W : ℝ → ℝ} (hW : Continuous W) (hW0 : W 0 = 0) {s : ℝ}
    (hs : 0 ≤ s) (d : ℂ) {r : ℝ} (hr : 0 < r) :
    IsFiniteMeasure ((foldedCircle d r).map (fwdMapInv W s)) ∧
      ∀ᵐ u ∂((foldedCircle d r).map (fwdMapInv W s)), u ∈ Hbar := by
  set φ := fwdMapInv W s
  have hφm : Measurable (WedgeUnzip.modH φ) :=
    WedgeUnzip.measurable_modH (WedgeUnzip.fwdMapInv_props hW hW0 hs).1.continuousOn
  refine ⟨by rw [← WedgeUnzip.fc_map_modH φ d hr]; infer_instance, ?_⟩
  rw [← WedgeUnzip.fc_map_modH φ d hr]
  refine (ae_map_iff (p := fun u => u ∈ Hbar) hφm.aemeasurable
    isClosed_Hbar.measurableSet).2 ?_
  exact (TwoPoint.foldedCircle_ae_mem_H d hr).mono fun w hw => by
    rw [WedgeUnzip.modH_eqOn φ hw]
    show 0 ≤ (φ w).im
    exact le_of_lt (show 0 < (φ w).im from RS.fwdMapInv_mem_H hW hW0 hs hw)

end F1
end QuantumZipper
