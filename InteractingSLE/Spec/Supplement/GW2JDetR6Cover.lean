/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW2JDetR2Hull

/-!
# Stopped GW2 buffers also prove canonical lifetime coverage

The stopped match includes the inequality between the buffer stop and the
canonical lifetime. Keeping that inequality proves availability of the
canonical driver at every physical time covered by the buffers.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal
open LQGMetric (DistOn)

universe u v

namespace InteractingSLE.Theorem14.GW2JDetR6

open Restart Exist Exist.Staged Sec2.Assembly Supp8.GB6 Supp8.GB6.RelDrv GW2JDetR2

/-- The zero initial driver value transfers from the stopped conditional
models to their actual samples, including zero stops. -/
theorem ae_driver_zero_of_buffer
    {κ θ : ℝ} {Ω : Type u} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P]
    {C : Type v} [MeasurableSpace C] {r : Ω → C} (hr : Measurable r)
    {M : Set Ω} (hM : MeasurableSet M) {word : C → BoundaryWord}
    {Hc : Ω → DistOn upperHalfPlaneOpens}
    (D : StoppedKernelBuffer κ θ P r M word Hc) :
    ∀ᵐ ω ∂P, ω ∈ M → D.driver 0 (D.sample ω) = 0 := by
  let _ := D.mSample
  have := D.markov
  apply Sec5.MarkovOther.ae_mem_of_compProd_eq_prod hM hr
    D.measurable_sample D.law
    (measurableSet_eq_fun ((D.measurable_driver 0).comp measurable_snd) measurable_const)
  filter_upwards [D.models] with x hx
  obtain ⟨X, 𝓕, VL, VR, B, R, -, hSC, -⟩ := hx.2.2
  filter_upwards [hSC.1.ae_path] with z hz using hz.w_zero

/-- The same countable buffer cover gives the hull identity and strict
availability before the canonical continuation lifetime. -/
theorem ae_hull_lifetime_of_buffers
    (h12p : Theorem12ParamStatement.{0}) (h13 : Theorem13Statement.{0})
    {κ θ : ℝ} (hκ : 0 < κ)
    {F : BoundaryWord × DistOn upperHalfPlaneOpens → PCode × ℝ≥0∞}
    (hF : IsCanonicalDriverCode κ θ F)
    {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {C : Type v} [MeasurableSpace C] {r : Ω → C} (hr : Measurable r)
    {M : Set Ω} (hM : MeasurableSet M) {word : C → BoundaryWord} (hw : Measurable word)
    {Hc : Ω → DistOn upperHalfPlaneOpens}
    (D : ℕ → StoppedKernelBuffer κ θ P r M word Hc)
    (clock : Ω → ℝ≥0 → ℝ) (hulls : Ω → ℝ≥0 → Set ℂ)
    (available : Ω → ℝ≥0 → Prop)
    (hcover : ∀ᵐ ω ∂P, ω ∈ M → ∀ t, available ω t →
      ∃ (n : ℕ) (q : ℝ≥0), (q : ℝ) = clock ω t ∧
        (q : ℝ≥0∞) < (D n).stop ((D n).sample ω) ∧
        QuantumZipper.fwdHull
          (fun a : ℝ => (D n).driver a.toNNReal ((D n).sample ω)) (q : ℝ) = hulls ω t) :
    ∀ᵐ ω ∂P, ω ∈ M → IsGoodDrvCode (F (word (r ω), Hc ω)) ∧
      ∀ t, available ω t →
        0 ≤ clock ω t ∧
        ((clock ω t).toNNReal : ℝ≥0∞) < (F (word (r ω), Hc ω)).2 ∧
        QuantumZipper.fwdHull
          (fun a : ℝ => drvDec (F (word (r ω), Hc ω)) a.toNNReal)
          (clock ω t) = hulls ω t := by
  have hall := ae_all_iff.mpr fun n => (D n).ae_good_match h12p h13 hκ hF hr hM hw
  have hgeom := ae_hull_eq_of_buffers h12p h13 hκ hF hr hM hw
    D clock hulls available hcover
  filter_upwards [hall, hgeom, hcover] with ω hmatch hg hc hωM
  refine ⟨(hg hωM).1, fun t ht => ?_⟩
  obtain ⟨n, q, hq, hstop, -⟩ := hc hωM t ht
  refine ⟨hq ▸ q.coe_nonneg, ?_, (hg hωM).2 t ht⟩
  rw [← hq, Real.toNNReal_coe]
  exact hstop.trans_le (hmatch n hωM).2.1

/-- A single covered time forces the canonical initial value to be zero.
This is proved from the stopped models, rather than imposed on the code. -/
theorem ae_decoded_zero_of_buffer_cover
    (h12p : Theorem12ParamStatement.{0}) (h13 : Theorem13Statement.{0})
    {κ θ : ℝ} (hκ : 0 < κ)
    {F : BoundaryWord × DistOn upperHalfPlaneOpens → PCode × ℝ≥0∞}
    (hF : IsCanonicalDriverCode κ θ F)
    {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {C : Type v} [MeasurableSpace C] {r : Ω → C} (hr : Measurable r)
    {M : Set Ω} (hM : MeasurableSet M) {word : C → BoundaryWord} (hw : Measurable word)
    {Hc : Ω → DistOn upperHalfPlaneOpens}
    (D : ℕ → StoppedKernelBuffer κ θ P r M word Hc) :
    ∀ᵐ ω ∂P, ω ∈ M →
      (∃ (n : ℕ) (q : ℝ≥0), (q : ℝ≥0∞) < (D n).stop ((D n).sample ω)) →
      drvDec (F (word (r ω), Hc ω)) 0 = 0 := by
  have hall := ae_all_iff.mpr fun n => (D n).ae_good_match h12p h13 hκ hF hr hM hw
  have hz := ae_all_iff.mpr fun n => ae_driver_zero_of_buffer hr hM (D n)
  filter_upwards [hall, hz] with ω hm hzero hωM hex
  obtain ⟨n, q, hq⟩ := hex
  exact (eqOn_drvDec_of_isStopDrvMatch (hm n hωM).1
    ((D n).continuous_driver ((D n).sample ω)) (hm n hωM).2 0
    (bot_le.trans_lt hq)).trans (hzero n hωM)

end InteractingSLE.Theorem14.GW2JDetR6
