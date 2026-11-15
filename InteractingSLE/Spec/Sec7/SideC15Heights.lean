/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.SideC15ArcMarks
import InteractingSLE.Spec.Sec7.SideC15ReadyBranch

/-!
# The native finite-word heights are the actual source-wall heights

PROVE-SIDE-COLLAR2. The wall's own angle changes and the installed force
marks give identical boundary heights. Both left-word shapes and both
pocket shapes are included; no native-word identification is assumed.
-/

set_option autoImplicit false
noncomputable section

open MeasureTheory Set Filter Topology Complex
open QuantumZipper (chiC)
open scoped NNReal Real

namespace InteractingSLE.Wire.Current.SideTest

open WangWu Sec7 Sec7.SideC15 Sec7.SideC13 Sec7.SideC12 Sec7.PocketCoord Sec7.PocketJordan
  Sec7.PocketCoupling Sec7.Aux2728Pocket Sec7.PocketStopSide Sec7.Lemma71O Sec7.Lemma71I

variable {Ω : Type} [MeasurableSpace Ω]

/-- Exact identification of the actual source boundary data with the
incoming-angle profiles of the native word, off the source exceptions. -/
theorem chartData_eq_initialFlowAngles_of_ready {j : SideTest Ω} {i : BothLow} {d : WordObjects Ω}
    (hj : j.Ready d) (hRc : ∀ ω, Continuous (d.rightWall ω))
    (hLc : ∀ ω, Continuous (d.leftWall j.seed ω)) {ω : Ω}
    (hω : ω ∈ (j.target i d).event) {ξ : ℝ}
    (hξ : ξ ∉ exSet (d.leftWall j.seed ω) (d.rightWall ω) {StripSys.rt j.seed} {1}
      (conjugateFlowChart ((j.target i d).baseChart ω))) :
    chartData (d.leftWall j.seed ω) (d.rightWall ω)
      (fun s => sleLambda (16 / i.kappa) -
        (if s < StripSys.rt j.seed then π / 2 else rs136Theta2 (16 / i.kappa) i.rightWeight) * chiC (16 / i.kappa))
      (fun s => -sleLambda (16 / i.kappa) -
        (if s < 1 then -(π / 2) else rs136Theta1 (16 / i.kappa) i.leftWeight) * chiC (16 / i.kappa))
      (conjugateFlowChart ((j.target i d).baseChart ω)) ξ =
        cf92Lower (16 / i.kappa) (j.initialFlowAngle₁ i d ω ξ) (j.initialFlowAngle₂ i d ω ξ) ξ := by
  have hF := j.isFlowChart_conjugate_of_ready hj hRc hLc hω
  have h := hF.config
  have hξ0 : ξ ≠ 0 := fun he => hξ (he ▸ mem_insert 0 _)
  rcases lt_or_gt_of_ne hξ0 with hneg | hpos
  · obtain ⟨t, ht, hland, htξ⟩ := exists_left_flowArc_landing hF hneg
    have ht01 : t ∈ Ico (0 : ℝ) 1 :=
      ⟨h.changeCorner_props.2.2.2.1.1.trans ht.1.le,
        ht.2.trans_le h.changeCorner_props.2.2.2.2.1.2⟩
    have hInv : Function.invFun (d.leftWall j.seed ω)
        (land (conjugateFlowChart ((j.target i d).baseChart ω)) ξ) = (arcTime t).toNNReal := by
      rw [hland, Function.leftInverse_invFun h.left.2.1]
    have hne : (arcTime t).toNNReal ≠ StripSys.rt j.seed := by
      intro he
      apply hξ
      exact mem_insert_of_mem 0 (Or.inl ⟨hneg, by rw [hInv, he]; exact mem_singleton _⟩)
    have htne : t ≠ discTime (StripSys.rt j.seed) := by
      intro he
      apply hne
      rw [he, arcTime_discTime (StripSys.rt j.seed).coe_nonneg]
      exact Real.toNNReal_coe
    have hmark := left_mark_le_iff hF h.changeCorners.2.2.2.2.1 ht htξ
    have htime := own_time_lt_iff ht01 (StripSys.rt j.seed)
    have hiff : (arcTime t).toNNReal < StripSys.rt j.seed ↔
        (j.chart ω (cfPt (toDisc (realPath (d.leftWall j.seed ω)) (discTime (StripSys.rt j.seed))))).re ≤ -ξ⁻¹ := by
      rw [htime, hmark]
      exact lt_iff_le_and_ne.trans (and_iff_left htne)
    have hAngle : (if (arcTime t).toNNReal < StripSys.rt j.seed then π / 2
        else rs136Theta2 (16 / i.kappa) i.rightWeight) = j.initialFlowAngle₂ i d ω ξ := by
      change _ = if (j.chart ω (cfPt (toDisc (realPath (d.leftWall j.seed ω))
        (discTime (StripSys.rt j.seed))))).re ≤ -ξ⁻¹ then π / 2 else _
      simp only [← hiff]
    simp only [chartData, hneg, ↓reduceIte, hInv, hAngle, cf92Lower]
  · obtain ⟨t, ht, hland, htξ⟩ := exists_right_flowArc_landing hF hpos
    have ht01 : t ∈ Ico (0 : ℝ) 1 :=
      ⟨h.changeCorner_props.1.1.trans ht.1.le,
        ht.2.trans_le h.changeCorner_props.2.1.2⟩
    have hInv : Function.invFun (d.rightWall ω)
        (land (conjugateFlowChart ((j.target i d).baseChart ω)) ξ) = (arcTime t).toNNReal := by
      rw [hland, Function.leftInverse_invFun h.right.2.1]
    have htime := own_time_lt_iff ht01 1
    simp only [NNReal.coe_one] at htime
    have hω' := hω
    rw [target_event] at hω'
    obtain ⟨_, _, _, hG, _, _, _, _, hAG, _, _, _, hShape⟩ := hj
    have hωG : ω ∈ j.outerEvent := by
      cases hI : j.infinite <;> simp only [hI, Bool.false_eq_true, ↓reduceIte] at hAG <;>
        exact (hAG hω').1
    have hAngle : (if (arcTime t).toNNReal < 1 then -(π / 2)
        else rs136Theta1 (16 / i.kappa) i.leftWeight) = j.initialFlowAngle₁ i d ω ξ := by
      cases htwo : j.twoLeft
      · simp only [htwo, Bool.false_eq_true, ↓reduceIte] at hShape
        have hle : discTime (1 : ℝ) ≤ rightLo (d.rightWall ω) (d.leftWall j.seed ω) (StripSys.rt j.seed) := by
          by_contra hlt
          exact hShape ω hω' ⟨lt_of_not_ge hlt, (hG ω hωG).2⟩
        have hn : ¬ (arcTime t).toNNReal < 1 := fun hs =>
          not_lt_of_ge (hle.trans ht.1.le) (htime.1 hs)
        simp only [initialFlowAngle₁, htwo, Bool.false_eq_true, ↓reduceIte, hn]
      · simp only [htwo, ↓reduceIte] at hShape
        have hmark := right_lt_mark_iff hF (hShape ω hω') ht htξ
        simp only [initialFlowAngle₁, htwo, ↓reduceIte]
        change _ = if -ξ⁻¹ < (j.chart ω (cfPt (toDisc (realPath (d.rightWall ω)) (discTime 1)))).re
          then -(π / 2) else _
        simp only [hmark, htime]
    simp only [chartData, not_lt.2 hpos.le, hpos, ↓reduceIte, hInv, hAngle, cf92Lower]

end InteractingSLE.Wire.Current.SideTest
