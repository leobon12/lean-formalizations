/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Coupling.WFSLeafSurvEOptional

/-!
# Strict survival gaps simultaneously before the cutoff

First contact with the nonpositive half-line is a Galmarino rule. Its bounded
clips are driving stopping times. Optional sampling excludes that contact
before the lifetime, on one event of full measure.
-/

set_option autoImplicit false
noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal

namespace InteractingSLE.WFS

open LawUnique Restart.StoppedExtendWF Restart.FlowStopIdentG

/-- The difference between the current discount and its optional future reader. -/
def survivalGap {nL nR : ℕ} (M : HistorySpace nL nR → ℝ≥0 → ℝ)
    (γ : HistorySpace nL nR) (t : ℝ≥0) : ℝ := survivalDiscount (t : ℝ≥0∞) - M γ t

/-- The deterministic time discount is continuous. -/
theorem continuous_survivalDiscount_time : Continuous (fun t : ℝ≥0 => survivalDiscount (t : ℝ≥0∞)) := by
  simp only [survivalDiscount_coe]
  exact (continuous_subtype_val.add continuous_const).inv₀ (fun t => ne_of_gt (add_pos_of_nonneg_of_pos t.property zero_lt_one))

/-- Borel dyadic evaluations pass to the survival gap. -/
theorem measurable_survivalGap {nL nR : ℕ} {M : HistorySpace nL nR → ℝ≥0 → ℝ}
    (hm : ∀ p, Measurable fun γ => M γ (dyadicTime p)) (p : ℕ × ℕ) :
    Measurable fun γ => survivalGap M γ (dyadicTime p) := measurable_const.sub (hm p)

/-- The survival gap is non-anticipating whenever the reader is. -/
theorem isNonAnticipating_survivalGap {nL nR : ℕ} {M : HistorySpace nL nR → ℝ≥0 → ℝ}
    (hM : IsNonAnticipating M) : IsNonAnticipating (survivalGap M) := by
  intro γ δ p h
  exact congrArg (fun z => survivalDiscount (dyadicTime p : ℝ≥0∞) - z) (hM γ δ p h)

/-- Continuity and optional sampling promote strict gaps at stopping times to
strict gaps at every time before the lifetime. No announcing sequence is used. -/
theorem ae_survivalGap_pos {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} [IsFiniteMeasure P] {nL nR : ℕ}
    {W : ℝ≥0 → Ω → ℝ} {VL : Fin nL → ℝ≥0 → Ω → ℝ}
    {VR : Fin nR → ℝ≥0 → Ω → ℝ} {V : Ω → ℝ≥0∞}
    (hX : IsMeasurableKilledDriving W VL VR V)
    (hc : ∀ᵐ ω ∂P, ContinuousOn (Restart.Aux54.dState W VL VR ω) {t | (t : ℝ≥0∞) < V ω})
    (hpos : ∀ᵐ ω ∂P, 0 < V ω)
    {M : HistorySpace nL nR → ℝ≥0 → ℝ}
    (hm : ∀ p, Measurable fun γ => M γ (dyadicTime p)) (hM : IsNonAnticipating M)
    (hcont : ∀ᵐ ω ∂P, Continuous (M (killedHistory W VL VR V ω)))
    (hread : IsOptionalSurvivalReader P (drivingFiltration P hX) V (killedHistory W VL VR V) M) :
    ∀ᵐ ω ∂P, ∀ t : ℝ≥0, (t : ℝ≥0∞) < V ω → 0 < survivalGap M (killedHistory W VL VR V ω) t := by
  let Y := killedHistory W VL VR V
  let Q := hitRule (survivalGap M) (Iic 0)
  have hV := Restart.Aux54.isStoppingTime_lifetime_driving (P := P) hX
  have hS := Restart.Aux54.isStoppingTime_ruleStop (P := P) hX
    (measurable_hitRule (measurable_survivalGap hm) (Iic 0))
    (isStrongGalmarino_hitRule (isNonAnticipating_survivalGap hM) (Iic 0)).isHistGalmarino hc
  have hn (n : ℕ) := ae_survival_gap_pos_at_stop hV (hS.min_const (n : ℝ≥0)) hread
    ⟨(n : ℝ≥0), fun _ => min_le_right _ _⟩
  have hall := ae_all_iff.2 hn
  have hzero := ae_survival_gap_pos_at_stop hV (isStoppingTime_const (drivingFiltration P hX) 0)
    hread ⟨0, fun _ => le_rfl⟩
  filter_upwards [hc, hpos, hcont, hall, hzero] with ω hc hpos hcont hall hzero
  have hγ : IsKilledContHist (Y ω) := isKilledContHist_killedHistory hc
  have hg : Continuous (survivalGap M (Y ω)) := continuous_survivalDiscount_time.sub hcont
  have hg0 : 0 < survivalGap M (Y ω) 0 := by
    have hz := hzero hpos
    change 0 < survivalDiscount 0 - M (Y ω) (0 : ℝ≥0∞).toNNReal at hz
    simpa only [survivalGap, ENNReal.coe_zero, ENNReal.toNNReal_zero] using hz
  intro U hU
  by_contra hneg
  have hU0 : 0 ≤ -survivalGap M (Y ω) U := neg_nonneg.2 (le_of_not_gt hneg)
  obtain ⟨T, hT0, hTU, hT, hoff⟩ := exists_first_level_contact hg.neg.continuousOn
    (neg_neg_of_pos hg0) hU0
  have hTV : (T : ℝ≥0∞) < V ω := (ENNReal.coe_le_coe.2 hTU).trans_lt hU
  have hhit : Q (Y ω) = T := hitRule_eq_of_hit_before (isNonAnticipating_survivalGap hM)
    isClosed_Iic hγ hT0 hTV.le hg.continuousOn
    (fun s hs => not_le.2 (neg_neg_iff_pos.1 (hoff s hs)))
    (neg_nonneg.1 hT) (fun _ _ => rfl)
  obtain ⟨n, hn⟩ := exists_nat_ge T
  have hTN : (T : ℝ≥0∞) ≤ (n : ℝ≥0∞) := by exact_mod_cast hn
  have he : min (min (Q (Y ω)) (V ω)) (n : ℝ≥0∞) = T := by
    rw [hhit, min_eq_left hTV.le, min_eq_left hTN]
  have hstrict := hall n
  change min (min (Q (Y ω)) (V ω)) (n : ℝ≥0∞) < V ω →
    0 < survivalDiscount (min (min (Q (Y ω)) (V ω)) (n : ℝ≥0∞)) -
      M (Y ω) (min (min (Q (Y ω)) (V ω)) (n : ℝ≥0∞)).toNNReal at hstrict
  rw [he, ENNReal.toNNReal_coe] at hstrict
  have hp : 0 < survivalGap M (Y ω) T := hstrict hTV
  exact (not_le_of_gt hp) (neg_nonneg.1 hT)

end InteractingSLE.WFS
