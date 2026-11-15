/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.SBS3MarkedStage

/-!
# S3: physical side labels immediately after a finite stop

The post-stop chart and word retain the physical side invariant even when
the next instruction never launches. This is the single finite Loewner
step, with no subsequent recentering or launch assumption.
-/

set_option autoImplicit false

noncomputable section

open Set Filter Topology
open scoped NNReal ENNReal
open QuantumZipper (H)

namespace InteractingSLE.Theorem14.SB.S3

open Exist Exist.Staged Exist.StagedLaw Restart GW1W

/-- Physical interior values of the post-stop word come from sides launched
by that stop. No launch of the next instruction is needed. -/
theorem interior_stageSide_post_launch {κ : ℝ} (hκ : 0 < κ)
    {b : ℝ → ℝ} {jumps : Finset ℝ} {spec : ExplSpec}
    {D : ℕ → (ℝ≥0 → ℝ) × ℝ≥0∞} (hR : LuM.RegLaunches κ b jumps spec D)
    {k : ℕ} (hl : (ExplState.run κ b jumps spec D (k + 1)).2.2.2.1 k ≠ none)
    (hfin : min (instrTime spec k) (D k).2 ≠ ⊤)
    (hreg : IsRegularDriver (D k))
    (hgood : LocalExt.IsDrvGood (recHist (recOf (instrTime spec k) (D k))))
    {word : BoundaryWord} (hOld : HasInteriorStageSides κ b jumps spec D k word) :
    HasInteriorStageSides κ b jumps spec D (k + 1)
      (stopWord κ (word, instrAngle spec k, recOf (instrTime spec k) (D k))) := by
  obtain ⟨⟨c, θ⟩, hcθ⟩ := Option.ne_none_iff_exists'.1 hl
  have hP := hR k c θ hcθ
  have hBOld := GW1WalkFinish.hasBdryLimits_chart_run spec D hR k
  have hAfter : (ExplState.run κ b jumps spec D (k + 1)).2.2.2.2.1 =
      (ExplState.run κ b jumps spec D k).2.2.2.2.1.loewner
        (rdrv (recOf (instrTime spec k) (D k))) (rtime (recOf (instrTime spec k) (D k))) := by
    obtain ⟨-, he, -⟩ := eq_launch_of_launches spec D hcθ
    rw [he, chart_launch _ _ _ _ _ hfin, rdrv_recOf, recDrv_eq_stopDrv hreg hgood, rtime_recOf]
    rfl
  have hB : HasBdryLimits (QuantumZipper.fwdMapInv
      (rdrv (recOf (instrTime spec k) (D k))) (rtime (recOf (instrTime spec k) (D k)))) := by
    rw [rdrv_recOf, recDrv_eq_stopDrv hreg hgood, rtime_recOf]
    exact hP.hasBdryLimits hfin
  intro y hy hyH
  change LuM.bdVal (ExplState.run κ b jumps spec D (k + 1)).2.2.2.2.1 (y : ℂ) ∈ H at hyH
  rw [hAfter] at hyH
  exact stopWord_interior_values_bdVal hκ hBOld hB
    (fun x hx hxH => (hOld x hx hxH).mono (Nat.le_succ k))
    ⟨k, Nat.lt_succ_self k, hl, Or.inr rfl⟩
    ⟨k, Nat.lt_succ_self k, hl, Or.inl rfl⟩ hy hyH

end InteractingSLE.Theorem14.SB.S3
