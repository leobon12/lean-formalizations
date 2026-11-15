/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Restart.RetPlumbProofLocal
import InteractingSLE.Spec.Restart.ClockMeasCap

/-!
# Capacity and safe-event measurability adapters

Packet PROVE-RETPLUMB. The remaining physical inputs are stated below at the
level of hitting-measurable chart prefixes and the live event. In particular,
measurability of the regularization branch is an explicit input: its definition
quantifies over the entire future path and is not automatically adapted.
-/

set_option autoImplicit false

noncomputable section

open Complex Set Metric Filter Topology MeasureTheory
open scoped NNReal ENNReal

namespace InteractingSLE.Restart.RetAux79

open QuantumZipper (H fwdHull)
open DomainMarkov.Aux79

variable {Ω : Type*}

/-- Grid capacity recovers the nonnegative chart clock of a continuous prefix. -/
theorem chartClock_toNNReal_eq_grid {Γ : ℝ≥0 → ℂ} {t : ℝ≥0}
    (hc : ContinuousOn Γ (Icc 0 t)) (h0 : (Γ 0).im ≤ 0) :
    (chartClock Γ t).toNNReal =
      ((WholeField.hcapHit (Γ '' Icc 0 t)).toReal / 2).toNNReal := by
  have hcap : 0 ≤ ConformalImage.hcapSet (fillH (Γ '' Icc 0 t)) := by
    rw [ConformalImage.hcapSet_eq (isHPHull_fillH_image hc h0)]
    exact HPHull.hcap_nonneg _
  rw [hcapHit_image_eq hc h0, ENNReal.toReal_ofReal hcap]
  rfl

/-- The precise geometric/measurable inputs for the regularized retained clock.
All measurability is with respect to the physical information at the given line.
These inputs do not assert the conclusion `Measurable retClock`. -/
structure RetClockMeasInput (ℋ : MeasurableSpace Ω) (G : ℝ≥0 → Set Ω)
    (η₁' η₂' : Ω → ℝ≥0 → ℂ) (ζ₂ : Ω → ℝ≥0∞) (u r t : ℝ≥0) : Prop where
  branch : MeasurableSet[ℋ] {ω |
    Continuous (chartClock (retChartPath G η₁' η₂' ζ₂ u r ω)) ∧
      Monotone (chartClock (retChartPath G η₁' η₂' ζ₂ u r ω)) ∧
        chartClock (retChartPath G η₁' η₂' ζ₂ u r ω) 0 = 0}
  prefixMeas : Measurable[ℋ, hittingSigma]
    (fun ω => retChartPath G η₁' η₂' ζ₂ u r ω '' Icc 0 t)
  continuousOn : ∀ ω, ContinuousOn (retChartPath G η₁' η₂' ζ₂ u r ω) (Icc 0 t)
  start : ∀ ω, (retChartPath G η₁' η₂' ζ₂ u r ω 0).im ≤ 0

/-- Physical measurability of the clock from its chart-prefix inputs. -/
theorem measurable_retClock_of_prefix {ℋ : MeasurableSpace Ω}
    {G : ℝ≥0 → Set Ω} {η₁' η₂' : Ω → ℝ≥0 → ℂ} {ζ₂ : Ω → ℝ≥0∞}
    {u r t : ℝ≥0} (hi : RetClockMeasInput ℋ G η₁' η₂' ζ₂ u r t) :
    Measurable[ℋ] (retClock G η₁' η₂' ζ₂ u r t) := by
  let _ : MeasurableSpace Ω := ℋ
  have hm : Measurable fun ω =>
      ((WholeField.hcapHit (retChartPath G η₁' η₂' ζ₂ u r ω '' Icc 0 t)).toReal / 2).toNNReal :=
    (((WholeField.measurable_hcapHit.comp hi.prefixMeas).ennreal_toReal).div_const 2).real_toNNReal
  have he : (fun ω => (chartClock (retChartPath G η₁' η₂' ζ₂ u r ω) t).toNNReal) =
      (fun ω => ((WholeField.hcapHit
        (retChartPath G η₁' η₂' ζ₂ u r ω '' Icc 0 t)).toReal / 2).toNNReal) :=
    funext fun ω => chartClock_toNNReal_eq_grid (hi.continuousOn ω) (hi.start ω)
  have hclock : Measurable fun ω => (chartClock (retChartPath G η₁' η₂' ζ₂ u r ω) t).toNNReal :=
    he.symm ▸ hm
  exact Measurable.ite hi.branch hclock measurable_const

/-- Avoidance of a compact set by a random relatively closed hull is measurable. -/
theorem measurableSet_disjoint_of_hitting {ℋ : MeasurableSpace Ω}
    {B : Ω → Set ℂ} (hB : Measurable[ℋ, hittingSigma] B)
    (hBc : ∀ ω, B ω ⊆ H ∧ IsOpen (H \ B ω))
    {C : Set ℂ} (hC : IsCompact C) (hCH : C ⊆ H) :
    MeasurableSet[ℋ] {ω | Disjoint C (B ω)} := by
  have he : {ω | Disjoint C (B ω)} =
      B ⁻¹' {S | Disjoint C (LocalSets.relClosureH S)} := by
    ext ω
    simp only [mem_ofPred_eq, mem_preimage,
      LocalSets.relClosureH_eq (hBc ω).1 (hBc ω).2]
  rw [he]
  exact hB (LocalSets.measurableSet_disjoint_relClosureH hC hCH)

/-- Safe events reduce to the live event and hitting measurability of the hull.
The hull has to be the hull at the random capacity time, not a deterministic-time hull. -/
theorem measurableSet_lineSafe_of_hull {ℋ : MeasurableSpace Ω}
    {Q : ℝ≥0 → Ω → ℝ≥0} {W : ℝ≥0 → Ω → ℝ} {V : Ω → ℝ≥0∞}
    {t : ℝ≥0} {C : Set ℂ} (hC : IsCompact C) (hCH : C ⊆ H)
    (hlive : MeasurableSet[ℋ] {ω | (Q t ω : ℝ≥0∞) < V ω})
    (hull : Measurable[ℋ, hittingSigma]
      (fun ω => fwdHull (fun s : ℝ => W s.toNNReal ω) (Q t ω)))
    (closedHull : ∀ ω,
      fwdHull (fun s : ℝ => W s.toNNReal ω) (Q t ω) ⊆ H ∧
        IsOpen (H \ fwdHull (fun s : ℝ => W s.toNNReal ω) (Q t ω))) :
    MeasurableSet[ℋ] (lineSafe Q W V C t) :=
  hlive.inter (measurableSet_disjoint_of_hitting hull closedHull hC hCH)

/-- For a continuous driver, relative closedness of every random-time hull is
automatic; only the random hull's hitting measurability and the live event remain. -/
theorem measurableSet_lineSafe_of_continuous_driver {ℋ : MeasurableSpace Ω}
    {Q : ℝ≥0 → Ω → ℝ≥0} {W : ℝ≥0 → Ω → ℝ} {V : Ω → ℝ≥0∞}
    {t : ℝ≥0} {C : Set ℂ} (hC : IsCompact C) (hCH : C ⊆ H)
    (hW : ∀ ω, Continuous fun s => W s ω)
    (hlive : MeasurableSet[ℋ] {ω | (Q t ω : ℝ≥0∞) < V ω})
    (hull : Measurable[ℋ, hittingSigma]
      (fun ω => fwdHull (fun s : ℝ => W s.toNNReal ω) (Q t ω))) :
    MeasurableSet[ℋ] (lineSafe Q W V C t) :=
  measurableSet_lineSafe_of_hull hC hCH hlive hull (fun ω =>
    ⟨fun _ hz => hz.1, QuantumZipper.FwdHolo.isOpen_compl_fwdHull
      ((hW ω).comp continuous_real_toNNReal) (Q t ω).coe_nonneg⟩)

/-- The live event is measurable when the capacity clock and lifetime are. -/
theorem measurableSet_lineLive {ℋ : MeasurableSpace Ω} {Q : Ω → ℝ≥0}
    {V : Ω → ℝ≥0∞} (hQ : Measurable[ℋ] Q) (hV : Measurable[ℋ] V) :
    MeasurableSet[ℋ] {ω | (Q ω : ℝ≥0∞) < V ω} :=
  measurableSet_lt hQ.coe_nnreal_ennreal hV

end InteractingSLE.Restart.RetAux79
