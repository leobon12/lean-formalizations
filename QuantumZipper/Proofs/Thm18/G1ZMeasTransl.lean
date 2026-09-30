import QuantumZipper.Proofs.Thm18.G1ZoomPalmCov
import QuantumZipper.Proofs.Thm18.G3FidProxy

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# G1Z-MEAS, part 1: Borel dependence on the translation of the canonical local data

Deterministic core of node B1-MEAS (`G1SideTranslMeasStmt`, G1ZoomPalmCov.lean): for a regular
sample `x`, `b ↦ locFieldFull R (canonical γ (translate x b))` is Borel.

* `canonical γ y = rescale y Q (scaleParam γ y)` reads `y` only through its dyadic circle
  coordinates (`Prop16Area.rescale_reconstruct_coords`), and `(x, b) ↦ coords (translate x b)`
  is jointly measurable (`IndepParams.measurable_coords_translate`).
* `scaleParam γ y` is the measurable proxy `scaleProxy γ y` when the area approximations of `y`
  have a vague limit on `ℍ` (`scaleProxy_eq_scaleParam`, G3FidProxy.lean), and `0` otherwise
  (junk: `qAreaMeasure = 0`, `sInf ∅ = 0`, `g1zMeas_scaleParam_of_not`).
* For a regular `x` the existence of that vague limit does not depend on the real translation
  (`g1zAreaEx_translate_iff`): the area approximations of `translate x t` are those of `x`
  translated (`GoodSample.areaR_radius`, `GoodTransforms.integral_areaR_translate`), and vague
  limits transfer along homeomorphisms of `ℂ` preserving `ℍ` (sequence version of
  `GoodTransforms.hasAreaLimit_map`).

So for fixed regular `x` the scale is either `b ↦ scaleProxy γ (translate x b)` (measurable) or
identically `0`. Own elementary argument (measurability bookkeeping, AGENT_GUIDE cost rule).
-/

noncomputable section

open MeasureTheory Filter Set Function
open scoped NNReal ENNReal Topology

namespace QuantumZipper
namespace Thm18Asm

open D3Plus Factorization

/-- The area approximations of `y` have a vague limit on `ℍ` (the existence clause read by
`qAreaMeasure`, hence by `scaleParam`). -/
def G1ZAreaEx (γ : ℝ) (y : FieldSample) : Prop := ∃ μ, IsVagueLimitOn H (areaApprox γ y) μ

/-- Junk value of the scale without the area limit. -/
theorem g1zMeas_scaleParam_of_not {γ : ℝ} {y : FieldSample} (h : ¬ G1ZAreaEx γ y) :
    scaleParam γ y = 0 := by
  have hq : qAreaMeasure γ y = 0 := by
    unfold qAreaMeasure
    split_ifs with h'
    exacts [absurd h' h, rfl]
  unfold scaleParam
  rw [hq]
  have e : {a : ℝ | 0 < a ∧ 1 ≤ (0 : Measure ℂ) (Metric.ball 0 a ∩ H)} = ∅ := by
    ext a; simp
  rw [e, Real.sInf_empty]

/-- Area approximations of a translated regular sample. -/
theorem g1zMeas_integral_areaApprox_translate {γ : ℝ} {x : FieldSample} {F : ℂ × ℝ → ℝ}
    (hF : IsRegularWith x F) (t : ℝ) (k : ℕ) (f : ℂ → ℝ) :
    ∫ z, f z ∂areaApprox γ (translate x (t : ℂ)) k = ∫ w, f (w - t) ∂areaApprox γ x k := by
  rw [← GoodSample.areaR_radius γ (hF.translate' t) k, ← GoodSample.areaR_radius γ hF k,
    one_mul]
  exact GoodTransforms.integral_areaR_translate hF γ t (radius_pos k) f

/-- Transfer of a vague limit on `ℍ` along a homeomorphism of `ℂ` preserving `ℍ` (sequence
version of `GoodTransforms.hasAreaLimit_map`). -/
theorem g1zMeas_isVagueLimitOn_map {μs μs' : ℕ → Measure ℂ} {μ : Measure ℂ}
    (hμ : IsVagueLimitOn H μs μ) (h : ℂ ≃ₜ ℂ) (hH : ∀ z, h z ∈ H ↔ z ∈ H)
    (hint : ∀ (f : ℂ → ℝ) (k : ℕ), ∫ z, f z ∂μs' k = ∫ w, f (h.symm w) ∂μs k) :
    IsVagueLimitOn H μs' (μ.map h.symm) := by
  have hmeas : Measurable h.symm := h.symm.continuous.measurable
  have hHs : ∀ z, h.symm z ∈ H ↔ z ∈ H := fun z => by
    rw [← hH (h.symm z), Homeomorph.apply_symm_apply]
  refine ⟨?_, fun K hK hKH => ?_, fun f hf hfc hfH => ?_⟩
  · rw [Measure.map_apply hmeas isOpen_H.measurableSet.compl]
    have : h.symm ⁻¹' Hᶜ = Hᶜ := by ext z; simp [hHs]
    rw [this]; exact hμ.1
  · rw [Measure.map_apply hmeas hK.isClosed.measurableSet]
    refine hμ.2.1 _ (h.symm.isCompact_preimage.2 hK) fun z hz => ?_
    exact (hHs z).1 (hKH hz)
  · rw [integral_map hmeas.aemeasurable hf.aestronglyMeasurable]
    have hfc' : HasCompactSupport (f ∘ h.symm) := hfc.comp_homeomorph h.symm
    have hfH' : tsupport (f ∘ h.symm) ⊆ H := fun z hz =>
      (hHs z).1 (hfH (GoodTransforms.tsupport_comp_subset h.symm.continuous hz))
    simp_rw [hint f]
    exact hμ.2.2 _ (hf.comp h.symm.continuous) hfc' hfH'

/-- For a regular sample, the area limit exists after a real translation iff it exists before. -/
theorem g1zAreaEx_translate_iff {γ : ℝ} {x : FieldSample} (hx : IsRegularSample x) (t : ℝ) :
    G1ZAreaEx γ (translate x (t : ℂ)) ↔ G1ZAreaEx γ x := by
  obtain ⟨F, hF⟩ := hx
  constructor
  · rintro ⟨μ, hμ⟩
    set h : ℂ ≃ₜ ℂ := (Homeomorph.addRight (t : ℂ)).symm with hh
    have hs : ∀ w, h.symm w = w + t := fun w => by simp [hh]
    have hc : ∀ z, h z = z - t := fun z => by
      rw [hh, Homeomorph.symm_apply_eq]; simp
    refine ⟨_, g1zMeas_isVagueLimitOn_map hμ h (fun z => ?_) (fun f k => ?_)⟩
    · rw [hc]; show 0 < (z - t).im ↔ 0 < z.im; simp
    · rw [g1zMeas_integral_areaApprox_translate hF t k (fun w => f (h.symm w))]
      simp only [hs, sub_add_cancel]
  · rintro ⟨μ, hμ⟩
    exact ⟨_, g1zMeas_isVagueLimitOn_map hμ (Homeomorph.addRight (t : ℂ))
      (fun z => show 0 < (z + t).im ↔ 0 < z.im by simp)
      (fun f k => g1zMeas_integral_areaApprox_translate hF t k f)⟩

/-- The measurable scale proxy of the translated sample is jointly measurable. -/
theorem g1zMeas_measurable_scaleProxy_translate (γ : ℝ) :
    Measurable fun q : FieldSample × ℝ => scaleProxy γ (translate q.1 (q.2 : ℂ)) := by
  have e : (fun q : FieldSample × ℝ => scaleProxy γ (translate q.1 (q.2 : ℂ))) =
      fun q => scaleProxy γ (reconstruct (coords (translate q.1 (q.2 : ℂ)))) := by
    funext q; rw [scaleProxy_recon]
  rw [e]
  exact (measurable_scaleProxy γ).comp
    (measurable_reconstruct.comp IndepParams.measurable_coords_translate)

/-- `canonical` read through the dyadic circle coordinates. -/
theorem g1zMeas_canonical_apply_eq (γ : ℝ) (y : FieldSample) (ν : Measure ℂ) :
    canonical γ y ν = rescale (reconstruct (coords y)) (Qc γ) (scaleParam γ y) ν := by
  rw [Prop16Area.rescale_reconstruct_coords]
  rfl

/-- **Borel dependence on the translation**, one evaluation: for a regular sample `x` and an
s-finite `ν`, `b ↦ canonical γ (translate x b) ν` is measurable. -/
theorem g1zMeas_canonical_translate_apply (γ : ℝ) {x : FieldSample} (hx : IsRegularSample x)
    (ν : Measure ℂ) [SFinite ν] :
    Measurable fun b : ℝ => canonical γ (translate x (b : ℂ)) ν := by
  have hp : Measurable fun b : ℝ => ((x, b) : FieldSample × ℝ) :=
    measurable_const.prodMk measurable_id
  have hc : Measurable fun b : ℝ => reconstruct (coords (translate x (b : ℂ))) :=
    Measurable.comp (g := fun q : FieldSample × ℝ => reconstruct (coords (translate q.1 (q.2 : ℂ))))
      (f := fun b : ℝ => ((x, b) : FieldSample × ℝ))
      (measurable_reconstruct.comp IndepParams.measurable_coords_translate) hp
  have hs : Measurable fun b : ℝ => scaleProxy γ (translate x (b : ℂ)) :=
    Measurable.comp (g := fun q : FieldSample × ℝ => scaleProxy γ (translate q.1 (q.2 : ℂ)))
      (f := fun b : ℝ => ((x, b) : FieldSample × ℝ))
      (g1zMeas_measurable_scaleProxy_translate γ) hp
  have hR := Prop16Area.measurable_rescale_apply_joint (Qc γ) ν
  by_cases hE : G1ZAreaEx γ x
  · have e : (fun b : ℝ => canonical γ (translate x (b : ℂ)) ν) = fun b : ℝ =>
        rescale (reconstruct (coords (translate x (b : ℂ)))) (Qc γ)
          (scaleProxy γ (translate x (b : ℂ))) ν := by
      funext b
      rw [g1zMeas_canonical_apply_eq, ← scaleProxy_eq_scaleParam γ _
        ((g1zAreaEx_translate_iff hx b).2 hE)]
    rw [e]
    exact Measurable.comp (g := fun q : FieldSample × ℝ => rescale q.1 (Qc γ) q.2 ν)
      (f := fun b : ℝ => (reconstruct (coords (translate x (b : ℂ))),
        scaleProxy γ (translate x (b : ℂ)))) hR (hc.prodMk hs)
  · have e : (fun b : ℝ => canonical γ (translate x (b : ℂ)) ν) = fun b : ℝ =>
        rescale (reconstruct (coords (translate x (b : ℂ)))) (Qc γ) 0 ν := by
      funext b
      rw [g1zMeas_canonical_apply_eq, g1zMeas_scaleParam_of_not
        (fun h => hE ((g1zAreaEx_translate_iff hx b).1 h))]
    rw [e]
    exact Measurable.comp (g := fun q : FieldSample × ℝ => rescale q.1 (Qc γ) q.2 ν)
      (f := fun b : ℝ => (reconstruct (coords (translate x (b : ℂ))), (0 : ℝ)))
      hR (hc.prodMk measurable_const)

/-- `locFieldFull` of a family of samples whose values at s-finite measures are measurable. -/
theorem g1zMeas_measurable_locFieldFull {α : Type*} [MeasurableSpace α] {f : α → FieldSample}
    (hf : ∀ (ν : Measure ℂ) [SFinite ν], Measurable fun a => f a ν) (R : ℕ) :
    Measurable fun a => locFieldFull R (f a) := by
  classical
  unfold locFieldFull
  refine Measurable.prodMk (measurable_pi_iff.2 fun i => ?_) (measurable_pi_iff.2 fun ρ => ?_)
  · by_cases h : inBallFull R i
    · simp only [h, ite_true, CoordsFull.coordsFull]; exact hf _
    · simp only [h, ite_false]; exact measurable_const
  · by_cases h : suppIn R ρ
    · simp only [h, ite_true, pairRaw]; exact (hf _).sub (hf _)
    · simp only [h, ite_false]; exact measurable_const

/-- **B1-MEAS, first clause, deterministic form**: for a regular sample `x`, the local canonical
data of `x` translated to `b` are Borel in `b`. -/
theorem g1zMeas_locFieldFull_translate (γ : ℝ) {x : FieldSample} (hx : IsRegularSample x)
    (R : ℕ) : Measurable fun b : ℝ => locFieldFull R (canonical γ (translate x (b : ℂ))) :=
  g1zMeas_measurable_locFieldFull (fun ν _ => g1zMeas_canonical_translate_apply γ hx ν) R

end Thm18Asm
end QuantumZipper
