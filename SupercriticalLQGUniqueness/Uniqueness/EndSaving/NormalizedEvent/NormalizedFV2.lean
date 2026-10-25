import SupercriticalLQGUniqueness.Uniqueness.EndSaving.FiniteEvents.FiniteEventsV2
import LQGMetric.Field.CircleAvgLaw




 






set_option autoImplicit false
noncomputable section
open MeasureTheory
open scoped ENNReal
namespace SupercriticalLQGUniqueness.Uniqueness.EndSaving.NormalizedEvent
open LQGMetric (DistC TestC)

 
def unitNorm (g : DistC) : ℝ :=
  LQGMetric.GFFLaw.equivNorm (LQGMetric.bumpTest 0 0)
    (fun v => LQGMetric.circleAvg v 1 0) g

 
def normalizedField (g : DistC) : DistC :=
  LQGMetric.addConst g (-(unitNorm g))

theorem unitNorm_addConst (g : DistC) (c : ℝ) :
    unitNorm (LQGMetric.addConst g c) = unitNorm g + c := by
  exact LQGMetric.GFFLaw.equivNorm_addConst
    (LQGMetric.GFFLaw.integral_bumpTest 0 0)
    (fun v => LQGMetric.circleAvg v 1 0) g c

theorem normalizedField_addConst (g : DistC) (c : ℝ) :
    normalizedField (LQGMetric.addConst g c) = normalizedField g := by
  change LQGMetric.addConst (LQGMetric.addConst g c)
      (-(unitNorm (LQGMetric.addConst g c))) =
    LQGMetric.addConst g (-(unitNorm g))
  rw [unitNorm_addConst, LQGMetric.GFFLaw.addConst_addConst]
  congr 1
  ring

theorem measurable_unitNorm : Measurable unitNorm := by
  have hρ : ∫ x, LQGMetric.bumpTest 0 0 x = 1 :=
    LQGMetric.GFFLaw.integral_bumpTest 0 0
  have hrec : Measurable (LQGMetric.GFFLaw.recenter (LQGMetric.bumpTest 0 0)) := by
    refine (LQGMetric.GFFLaw.measurable_recenter_sigma0 hρ).mono ?_ le_rfl
    rw [LQGMetric.GFFLaw.sigma0, ← measurable_iff_comap_le]
    exact LQGMetric.measurable_pair0
  exact (LQGMetric.GFFInv.measurable_pair _).add
    ((LQGMetric.measurable_circleAvg_left 1 0).comp hrec)

theorem measurable_normalizedField : Measurable normalizedField := by
  refine LQGMetric.GFFInv.measurable_distC_iff.2 fun φ => ?_
  simp only [normalizedField, LQGMetric.GFFInv.addConst_apply]
  exact (LQGMetric.GFFInv.measurable_pair φ).add
    (measurable_unitNorm.neg.const_mul _)

theorem normalizedField_eq_self (g : DistC)
    (hshift : ∀ c : ℝ,
      LQGMetric.circleAvg (LQGMetric.addConst g c) 1 0 =
        LQGMetric.circleAvg g 1 0 + c)
    (hzero : LQGMetric.circleAvg g 1 0 = 0) :
    normalizedField g = g := by
  have hnorm : unitNorm g = 0 :=
    (LQGMetric.GFFLaw.equivNorm_eq hshift).trans hzero
  simpa only [normalizedField, hnorm, neg_zero] using
    LQGMetric.GFFLaw.addConst_zero' g

theorem normalizedField_eq_self_of_unitCircle (g : DistC)
    (hzero : IsCircleAverage g ⟨1, Set.mem_Ioi.mpr one_pos⟩ 0 0) :
    normalizedField g = g := by
  have hz : LQGMetric.circleAvg g 1 0 = 0 :=
    LQGMetric.CircleAvg.circleAvg_eq_of_tendsto hzero
  exact normalizedField_eq_self g
    (fun c => LQGMetric.CircleAvg.circleAvg_addConst_of_tendsto hzero c) hz

theorem normalizedField_ae_eq_of_normalized
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) (h : Ω → DistC)
    (hh : IsNormalizedWholePlaneGFF h P) :
    ∀ᵐ ω ∂P, normalizedField (h ω) = h ω := by
  filter_upwards [hh.2] with ω hω
  exact normalizedField_eq_self_of_unitCircle (h ω) hω

 
def NormalizedFV2 {Ω : Type} [MeasurableSpace Ω]
    (μ : Measure Ω) (h : Ω → DistC) (D D' : DistC → LSCMetric)
    (ξ : Set.Ioi (0 : ℝ)) (Q cMid : ℝ) (cPlus : ℝ≥0∞)
    (par : EndSaving.Interfaces.Parameters ξ) (pbar : Set.Ioo (0 : ℝ) 1)
    (r b q : Set.Ioi (0 : ℝ)) (K₁ K₂ : Set ℂ)
    (obj : ∀ i : ℤ × ℤ,
      EndSaving.InterfaceV2.ObjectAtV2 μ h D D' ξ Q cMid par pbar
        (LQGMetric.GM.gridPt ((r : ℝ) / 100) i) r)
    (Z : Finset (ℤ × ℤ)) (g : DistC) : Prop :=
  EndSaving.FiniteEvents.FV2 μ h D D' ξ Q cMid cPlus par pbar r b q K₁ K₂ obj Z
    (normalizedField g)

theorem normalizedFV2_addConst {Ω : Type} [MeasurableSpace Ω]
    (μ : Measure Ω) (h : Ω → DistC) (D D' : DistC → LSCMetric)
    (ξ : Set.Ioi (0 : ℝ)) (Q cMid : ℝ) (cPlus : ℝ≥0∞)
    (par : EndSaving.Interfaces.Parameters ξ) (pbar : Set.Ioo (0 : ℝ) 1)
    (r b q : Set.Ioi (0 : ℝ)) (K₁ K₂ : Set ℂ)
    (obj : ∀ i : ℤ × ℤ,
      EndSaving.InterfaceV2.ObjectAtV2 μ h D D' ξ Q cMid par pbar
        (LQGMetric.GM.gridPt ((r : ℝ) / 100) i) r)
    (Z : Finset (ℤ × ℤ)) (g : DistC) (c : ℝ) :
    NormalizedFV2 μ h D D' ξ Q cMid cPlus par pbar r b q K₁ K₂ obj Z
      (LQGMetric.addConst g c) ↔
    NormalizedFV2 μ h D D' ξ Q cMid cPlus par pbar r b q K₁ K₂ obj Z g := by
  simp only [NormalizedFV2, normalizedField_addConst]

 

theorem normalizedFV2_ae_iff_raw {Ω : Type} [MeasurableSpace Ω]
    (P : Measure Ω) (h : Ω → DistC)
    (hh : IsNormalizedWholePlaneGFF h P)
    (D D' : DistC → LSCMetric)
    (ξ : Set.Ioi (0 : ℝ)) (Q cMid : ℝ) (cPlus : ℝ≥0∞)
    (par : EndSaving.Interfaces.Parameters ξ) (pbar : Set.Ioo (0 : ℝ) 1)
    (r b q : Set.Ioi (0 : ℝ)) (K₁ K₂ : Set ℂ)
    (obj : ∀ i : ℤ × ℤ,
      EndSaving.InterfaceV2.ObjectAtV2 P h D D' ξ Q cMid par pbar
        (LQGMetric.GM.gridPt ((r : ℝ) / 100) i) r)
    (Z : Finset (ℤ × ℤ)) :
    ∀ᵐ ω ∂P,
      NormalizedFV2 P h D D' ξ Q cMid cPlus par pbar r b q K₁ K₂ obj Z (h ω) ↔
      EndSaving.FiniteEvents.FV2 P h D D' ξ Q cMid cPlus par pbar r b q K₁ K₂ obj Z (h ω) := by
  filter_upwards [normalizedField_ae_eq_of_normalized P h hh] with ω hω
  simp only [NormalizedFV2, hω]

end SupercriticalLQGUniqueness.Uniqueness.EndSaving.NormalizedEvent
