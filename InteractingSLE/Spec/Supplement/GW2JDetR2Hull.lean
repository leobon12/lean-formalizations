/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW2JDetR2Buffer
import InteractingSLE.Spec.Restart.DomainMarkovLocKer

/-!
# GW2: countable stopped kernels identify physical hulls

The buffer models determine measurable stopped driver codes. Intersecting their
events is countable; afterwards a pathwise buffer cover can handle every
physical time simultaneously. The retained datum is arbitrary, so the theorem
also applies when it includes the complete finite-stage record.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal
open LQGMetric (DistOn)

universe u v

namespace InteractingSLE.Theorem14.GW2JDetR2

open Restart Exist Exist.Staged Sec2.Assembly Supp8.GB6 Supp8.GB6.RelDrv

/-- Countably many joint stopped kernels and pathwise buffer coverage identify
the full family of physical hulls on the alive event. -/
theorem ae_hull_eq_of_buffers
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
        QuantumZipper.fwdHull
          (fun a : ℝ => drvDec (F (word (r ω), Hc ω)) a.toNNReal)
          (clock ω t) = hulls ω t := by
  have hall := ae_all_iff.2 fun n => (D n).ae_good_match h12p h13 hκ hF hr hM hw
  filter_upwards [hall, hcover] with ω hmatch hcov hωM
  refine ⟨(hmatch 0 hωM).1, fun t ht => ?_⟩
  obtain ⟨n, q, hclock, hq, hgeom⟩ := hcov hωM t ht
  have hcode := eqOn_drvDec_of_isStopDrvMatch (hmatch n hωM).1
    ((D n).continuous_driver ((D n).sample ω)) (hmatch n hωM).2
  rw [← hclock]
  exact (DomainMarkov.fwdHull_rpath_congr_of_lt hcode hq).trans hgeom

end InteractingSLE.Theorem14.GW2JDetR2
