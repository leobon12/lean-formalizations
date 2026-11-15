/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW2JDetR7Record
import InteractingSLE.Spec.Sec5.Aux61ULocCore

/-!
# The actual pair of GW2 histories is marked local

Work in the counterflow parameter's original half-plane. The flow hull is
inverted into this frame. Its source retained-set convention fills the domain
when the physical flow has already died, and makes no positive-lifetime
assumption. Both exact stopped records remain among the marks.
-/

set_option autoImplicit false

noncomputable section

open Set Filter MeasureTheory ProbabilityTheory Topology
open scoped NNReal ENNReal
open LQGMetric (DistOn IsZeroBoundaryGFF)
open QuantumZipper (H fwdHull chiC)

universe u

namespace InteractingSLE.Theorem14.GW2JDetR7

open Restart Exist Exist.StagedLaw WholeField LocalSets
open Supp8.GB6 Supp8.GB6LineL Supp8.GB6LMean Supp8.Q3Chain Supp8.RelSafeS
open GW2TipSystem

/-- The physical stopped pair has marked locality with its actual two records
retained. The marks are field-determined, including their null completion.
There is no conditional-kernel or relative-driving-law assumption. -/
theorem exists_actual_union_local
    (h12 : Theorem12Statement.{u}) (h13 : Theorem13Statement.{u})
    {κ θ : ℝ} (hκ : 0 < κ) {c : BoundaryWord}
    {Ω : Type u} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {h h' : Ω → DistOn upperHalfPlaneOpens}
    (hh : IsGFFWithBoundaryData P h c.fn c.jumps)
    {b' : ℝ → ℝ} {J' : Finset ℝ} (hb' : IsPiecewiseConstantBoundaryData b' J')
    (hT : ∀ ω, IsChartTransport infinitySourceChart (-1)
      (-(Real.pi * chiC κ)) (chiC (16 / κ)) (h ω) (h' ω))
    {W Wα : ℝ≥0 → Ω → ℝ} {ζ ζα : Ω → ℝ≥0∞}
    (hcf : IsFlowLineDriver (16 / κ) b' J' 0 P h' W ζ)
    (hζ : ∀ᵐ ω ∂P, ζ ω = ⊤)
    (hfl : IsFlowLineDriver κ c.fn c.jumps θ P h Wα ζα) (s t : ℝ≥0) :
    ∃ (u₀ : ℂ → ℝ) (ℋ : {m : MeasurableSpace Ω // m ≤ mΩ}) (K : Ω → Set ℂ),
      IsBoundedHarmonicExtension (cfData (16 / κ) b' J')
        (forceJumpSet (flowLineXL b' J' 0) (flowLineXR b' J' 0)) u₀ ∧
      IsZeroBoundaryGFF upperHalfPlaneOpens (centredField h' u₀) P ∧
      Measurable[ℋ.1] (gb6Rec t Wα ζα) ∧
      Measurable[ℋ.1] (cfRec s W ζ) ∧ Measurable[ℋ.1, hittingSigma] K ∧
      (∀ᵐ ω ∂P, K ω = fwdHull (Ito.rpath (W · ω)) s) ∧
      (∀ᵐ ω ∂P, K ω ⊆ H ∧ IsOpen (H \ K ω)) ∧
      Measurable[ℋ.1, hittingSigma] (retSet t Wα ζα) ∧
      ℋ.1 ≤ aeSigma (MeasurableSpace.comap (centredField h' u₀) inferInstance) P ∧
      IsLocalSet (retSet t Wα ζα) (centredField h' u₀) P ∧
      IsLocalSet K (centredField h' u₀) P ∧
      IsHistoryAvoidanceLocal ℋ.1 (fun ω => retSet t Wα ζα ω ∪ K ω)
        (centredField h' u₀) P := by
  have hk : 0 < 16 / κ := by positivity
  have hG' := GW2aPiece.isGFFWithBoundaryData_of_isFlowLineDriver hk hb' hcf
  obtain ⟨u, hu, -⟩ :=
    PiecewiseConstant.existsUnique_isBoundedHarmonicExtension c.isPiecewiseConstantBoundaryData
  obtain ⟨u₀, hu₀⟩ := Sec7.StripSysField.exists_isBoundedHarmonicExtension_forceBoundaryData
    (16 / κ) (flowLineRhoL (16 / κ) b' J' 0 0) (flowLineRhoR (16 / κ) b' J' 0 0)
    (flowLineXL b' J' 0) (flowLineXR b' J' 0)
  have hcen := centredField_eq_reflect hκ c.isPiecewiseConstantBoundaryData hh
    hb' hG' hT hu hu₀
  have hcf₀ := hcf
  obtain ⟨X, 𝓕, VL, VR, B, htr, hC⟩ := hcf
  have hXX : X = h' := funext fun ω =>
    GW2Cone.eq_of_isTranslateAddConst_zero (zero_mul _) (htr ω)
  rw [hXX] at hC
  let hX := hC.2.2.2.1
  have hzero := isZeroBoundaryGFF_centredField hC hu₀
  have hdet := Exist.Param12.hasFieldDeterminedHistories h12 h13 hk
    (Theorem15.isOrderedForceWord_flowLine b' J' 0) P 𝓕 W VL VR B ζ h' hC
  have hcomap : MeasurableSpace.comap h' inferInstance ≤
      aeSigma (MeasurableSpace.comap (centredField h' u₀) inferInstance) P :=
    KernelTower.comap_le_aeSigma_comap (measurable_add_dist _)
      (Eventually.of_forall fun ω => (sub_add_cancel (h' ω)
        (SupercriticalConformalCovariance.GM24.smoothDist upperHalfPlaneOpens u₀)).symm)
  have hCFdet : drivingFiltration P hX s ≤
      aeSigma (MeasurableSpace.comap (centredField h' u₀) inferInstance) P :=
    (Supp8.Q3Chain.drivingFiltration_le_aeSigma hdet hX s).trans
      (Supp8.Q3Chain.aeSigma_le_of_le hcomap)
  have hdetα : LP.HasFieldDeterminedHistories.{u} κ
      (flowLineXL c.fn c.jumps 0) (flowLineXR c.fn c.jumps 0)
      (flowLineRhoL κ c.fn c.jumps 0 θ) (flowLineRhoR κ c.fn c.jumps 0 θ) :=
    Exist.Param12.hasFieldDeterminedHistories h12 h13 hκ
      (Theorem15.isOrderedForceWord_flowLine c.fn c.jumps 0)
  obtain ⟨ℋ₀, -, hR, hFdet, hlocF⟩ :=
    exists_retained_marks hκ hfl hdetα hu hzero.measurable hcen t
  let ℋ : {m : MeasurableSpace Ω // m ≤ mΩ} :=
    ⟨ℋ₀.1 ⊔ drivingFiltration P hX s, sup_le ℋ₀.2 ((drivingFiltration P hX).le s)⟩
  let K : Ω → Set ℂ := fun ω => Sec5.GlueCond.hullAt s
    (LawUnique.killedHistory W VL VR ζ ω)
  have hK : Measurable[drivingFiltration P hX s, hittingSigma] K :=
    Sec5.Aux61ULoc.measurable_hitting_of_avoid fun U hU hUH =>
      measurableSet_avoid_cfHull hX s hU hUH
  have hRm : Measurable (cfRec s W ζ) := by
    exact (measurable_recOf_cfE hcf₀ s).2
  have hCm := measurable_cfRec_driving hC hζ s hRm
  have hAm : Measurable[ℋ₀.1, hittingSigma] (retSet t Wα ζα) :=
    (measurable_retOfRec t).comp hR
  have hKc : ∀ᵐ ω ∂P, K ω ⊆ H ∧ IsOpen (H \ K ω) := by
    have hτ := isStoppingTime_const (drivingFiltration P hX) s
    have hsζ : ∀ᵐ ω ∂P,
        (((fun _ : Ω => (s : WithTop ℝ≥0)) ω : WithTop ℝ≥0) : ℝ≥0∞) < ζ ω := by
      filter_upwards [hζ] with ω hω
      rw [hω]
      exact ENNReal.coe_lt_top
    have hg := (hC.2.2.2.2 _ hτ hsζ).1.2.1
    filter_upwards [hg, ae_cfHull_eq hC hζ s] with ω hgeom heq
    rw [show K ω = fwdHull (Ito.rpath (W · ω)) s from heq]
    change fwdHull (fun r : ℝ => W r.toNNReal ω) s ⊆ H ∧
      IsOpen (H \ fwdHull (fun r : ℝ => W r.toNNReal ω) s) at hgeom
    exact hgeom
  have hFc : ∀ᵐ ω ∂P, retSet t Wα ζα ω ⊆ H ∧ IsOpen (H \ retSet t Wα ζα ω) :=
    Eventually.of_forall fun ω =>
      ⟨retSet_subset_H t Wα ζα ω, isOpen_H_diff_retSet t Wα ζα ω⟩
  have hFlocal : IsLocalSet (retSet t Wα ζα) (centredField h' u₀) P :=
    ((isLocalSet_tfae hzero (hAm.mono ℋ₀.2 le_rfl) hFc).out 4 1).2
      hlocF.isAvoidanceLocal
  have hClocal : IsLocalSet K (centredField h' u₀) P :=
    ((isLocalSet_tfae hzero (hK.mono ((drivingFiltration P hX).le s) le_rfl) hKc).out 4 1).2
      (isHistoryAvoidanceLocal_cfHull hC hk hζ hu₀ s).isAvoidanceLocal
  refine ⟨u₀, ℋ, K, hu₀, hzero,
    hR.mono le_sup_left le_rfl, hCm.mono le_sup_right le_rfl,
    hK.mono le_sup_right le_rfl, ae_cfHull_eq hC hζ s, hKc,
    hAm.mono le_sup_left le_rfl, sup_le hFdet hCFdet, hFlocal, hClocal, ?_⟩
  exact WalkLaw.isHistoryAvoidanceLocal_union_of_det hzero.measurable
    (fun U hUH => hAm (measurableSet_avoid U.isOpen hUH))
    (fun U hUH => hK (measurableSet_avoid U.isOpen hUH)) hFdet hCFdet
    hlocF (isHistoryAvoidanceLocal_cfHull hC hk hζ hu₀ s)

end InteractingSLE.Theorem14.GW2JDetR7
