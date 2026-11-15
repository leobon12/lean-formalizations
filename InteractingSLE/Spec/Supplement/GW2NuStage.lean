/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW2NuDeath
import InteractingSLE.Spec.Supplement.GW2NuExp

/-!
# The threshold at the candidate's death, read in the stage chart (D35 (D-a))

Packet PROVE-GW2-NOTHR (round 3). The same launch↔stage identification as `noThreshold` (route (M)) gives the stage
threshold at the death. The stage word is the joint word dilated by `λ` (data equal off a finite set, Claim(j)), and the
dilated stage path `scD λ D` generates the relative hulls up to the death. Then SAFE's converse at the death
(`ae_threshold_gw2_at_death`) and the data-level transfer (an iff, `GW2Nt.thresholdCondition_iff_of_dil`) give a
continuation threshold of the stage word along the stage path at the death's stage time `u` (`λ² u` = the relative
clock of the death).

* **`threshold_stage_of_joint`** (deterministic): a joint threshold along `Rr` at `λ² u` with `Rr = scD λ D` on
  `[0, λ² u]` is a stage threshold along `D` at `u`;
* **`ae_stage_threshold_at_death`**: SAFE's configuration under any probability measure, almost surely, for every
  identification (`λ`, the data identity, the hull identity of `scD λ D` up to the death): the stage threshold
  at the death, in the form of BUF's `GW2Bh.StageThreshold` (unfolded).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Filter Topology MeasureTheory
open scoped NNReal ENNReal
open QuantumZipper (H chiC fwdHull)
open LQGMetric (DistOn)

namespace InteractingSLE.Theorem14.GW2Nu

open Restart Exist.StagedLaw Sec7.PocketTraversal Supp8 Supp8.GB6 Supp8.GB6.RelDrv GW2Rd GW2TipSystem GW2Sf
  MartChar.RealFlow Sec5.CrossCond.StagedRepLater

/-- **A joint threshold at `λ² u` is a stage threshold at `u`** (the data-level transfer is an iff). -/
theorem threshold_stage_of_joint {κ : ℝ} (hκ : 0 < κ) {β K : BoundaryWord} {lam : ℝ} (hlam : 0 < lam)
    {F : Set ℝ} (hF : F.Finite) (hdata : ∀ y, y ∉ F → β.fn y = K.fn (lam * y)) {D : ℝ → ℝ} (hD : Continuous D)
    {Rr : ℝ≥0 → ℝ} {u : ℝ≥0} (hW : ∀ v ∈ Icc (0 : ℝ) (lam ^ 2 * u), Rr v.toNNReal = scD lam D v)
    (hth : ForceWord.ThresholdCondition (flowLineRhoL κ K.fn K.jumps 0 0) (flowLineRhoR κ K.fn K.jumps 0 0)
      (Rr (lam ^ 2 * u).toNNReal)
      (fun i => -rightImg (fun v : ℝ => -Rr v.toNNReal) (-flowLineXL K.fn K.jumps 0 i) (lam ^ 2 * u).toNNReal)
      (fun j => rightImg (fun v : ℝ => Rr v.toNNReal) (flowLineXR K.fn K.jumps 0 j) (lam ^ 2 * u).toNNReal)) :
    ForceWord.ThresholdCondition (flowLineRhoL κ β.fn β.jumps 0 0) (flowLineRhoR κ β.fn β.jumps 0 0) (D u)
      (fun i => -rightImg (fun v => -D v) (-flowLineXL β.fn β.jumps 0 i) u)
      (fun j => rightImg D (flowLineXR β.fn β.jumps 0 j) u) := by
  have hpos : (0 : ℝ) ≤ lam ^ 2 * u := mul_nonneg (sq_nonneg _) u.coe_nonneg
  have hcoe : (((lam ^ 2 * u).toNNReal : ℝ≥0) : ℝ) = lam ^ 2 * u := Real.coe_toNNReal _ hpos
  refine (GW2Nt.thresholdCondition_iff_of_dil (θ₁ := 0) (θ₂ := 0) hκ K.isPiecewiseConstantBoundaryData
    β.isPiecewiseConstantBoundaryData hlam hF (fun y hy => by simp only [zero_mul, add_zero]; exact hdata y hy) hD
    u.coe_nonneg (WL := fun v : ℝ => Rr v.toNNReal) hW).2 ?_
  rw [hcoe] at hth
  exact hth

variable {Ω : Type*} {κ θ : ℝ} {b : ℝ → ℝ} {J : Finset ℝ}
  {Wα W : ℝ≥0 → Ω → ℝ} {ζα ζ : Ω → ℝ≥0∞} {α γ : Ω → ℝ≥0 → ℂ}

/-- **D35 (D-a): the stage threshold at the candidate's death** (SAFE's configuration under any probability
measure). Almost surely, at every own time `S` of the counterflow with an interior tip, if the candidate dies at a
finite positive time `T` before the relative contact, then for every identification with a stage chart the stage
word has a continuation threshold along the stage path at the death's stage time `u`. The identification consists of
the dilation `λ > 0`, the stage word equal to the dilated joint word off a finite set, `λ² u` the relative clock of
the death, and the dilated stage path generating the relative hulls up to the death. -/
theorem ae_stage_threshold_at_death {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P]
    {h h' : Ω → DistOn upperHalfPlaneOpens} {b' : ℝ → ℝ} {J' : Finset ℝ} (hκ : 0 < κ) (hκ4 : κ < 4)
    (hb : IsPiecewiseConstantBoundaryData b J) (hG : IsGFFWithBoundaryData P h b J)
    (hb' : IsPiecewiseConstantBoundaryData b' J')
    (hT : ∀ ω, IsChartTransport infinitySourceChart (-1) (-(Real.pi * chiC κ)) (chiC (16 / κ)) (h ω) (h' ω))
    (hfl : IsFlowLineDriver κ b J θ P h Wα ζα)
    (hα : ∀ᵐ ω ∂P, IsGeneratingTrace (fun t => Wα t ω) (ζα ω) (α ω))
    (hcf : IsFlowLineDriver (16 / κ) b' J' 0 P h' W ζ)
    (hγ : ∀ᵐ ω ∂P, ζ ω = ⊤ ∧ IsGeneratingTrace (fun t => W t ω) ⊤ (γ ω))
    (c' : BoundaryWord) (hc'J : c'.jumps = J') (hc'b : ∀ y ∉ J', c'.fn y = b' y) :
    ∀ᵐ ω ∂P, ∀ S : ℝ≥0, γ ω S ∈ H → ∀ T : ℝ≥0, 0 < T → ζα ω = T →
      (T : ℝ≥0∞) < gb6Tc S (extTr S Wα ζα α) γ ω →
      ∀ (β : BoundaryWord) (lam : ℝ) (F : Set ℝ) (D : ℝ≥0 → ℝ) (u : ℝ≥0), 0 < lam → F.Finite →
        (∀ y, y ∉ F → β.fn y = (gw2Word κ θ c' (gb6Rec S W ζ ω)).fn (lam * y)) → Continuous D → D 0 = 0 →
        lam ^ 2 * u = gb6Clock S (regW S Wα ζα) W ω T →
        (∀ t : ℝ≥0, t ≤ T →
          fwdHull (scD lam (fun q : ℝ => D q.toNNReal)) (gb6Clock S (regW S Wα ζα) W ω t) =
            relMap (fun r : ℝ => W r.toNNReal ω) S '' fwdHull (fun r : ℝ => regW S Wα ζα r.toNNReal ω) t) →
        ForceWord.ThresholdCondition (flowLineRhoL κ β.fn β.jumps 0 0) (flowLineRhoR κ β.fn β.jumps 0 0) (D u)
          (fun i => -rightImg (fun v : ℝ => -D v.toNNReal) (-flowLineXL β.fn β.jumps 0 i) u)
          (fun j => rightImg (fun v : ℝ => D v.toNNReal) (flowLineXR β.fn β.jumps 0 j) u) := by
  filter_upwards [ae_threshold_gw2_at_death hκ hκ4 hb hG hb' hT hfl hα hcf hγ c' hc'J hc'b]
    with ω hdeath S hSH T hT0 hζT hTc β lam F D u hlam hF hdata hDc hD0 hclk hhull
  set D' : ℝ → ℝ := fun q : ℝ => D q.toNNReal with hD'def
  have hD'c : Continuous D' := hDc.comp continuous_real_toNNReal
  have hD'0 : D' 0 = 0 := by simp [hD'def, hD0]
  set Rr : ℝ≥0 → ℝ := fun v => scD lam D' v with hRrdef
  have hRrc : Continuous Rr := (continuous_scD hD'c).comp NNReal.continuous_coe
  have hRr0 : Rr 0 = 0 := by simp [hRrdef, scD, hD'0]
  have hRrW : ∀ v ∈ Icc (0 : ℝ) (lam ^ 2 * u), Rr v.toNNReal = scD lam D' v := fun v hv => by
    simp only [hRrdef, Real.coe_toNNReal _ hv.1]
  have hth := hdeath S hSH T hT0 hζT hTc Rr hRrc hRr0 fun t ht => by
    rw [← hhull t ht]
    refine YuanCorollary13.fwdHull_eq_of_eqOn_Icc (hRrc.comp continuous_real_toNNReal) (continuous_scD hD'c)
      (gb6Clock_nonneg _ _ _ _ _) fun v hv => ?_
    show scD lam D' ((v.toNNReal : ℝ≥0) : ℝ) = scD lam D' v
    rw [Real.coe_toNNReal _ hv.1]
  rw [← hclk] at hth
  have h1 := threshold_stage_of_joint hκ hlam hF hdata hD'c (Rr := Rr) hRrW hth
  simp only [hD'def, Real.toNNReal_coe] at h1
  exact h1

end InteractingSLE.Theorem14.GW2Nu
