/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.SBS3MarkedBoundary
import InteractingSLE.Spec.Supplement.SB2WdInd
import InteractingSLE.Spec.Supplement.GW1WalkFinishTip

/-!
# S3: propagate physical side provenance along the actual staged run

A value whose physical landing lies in the upper half plane must come from
an actually launched side. This invariant retains the physical inverse
chart as well as the word, and excludes original real values by their
landing, without making a numerical assumption on the original data.
-/

set_option autoImplicit false

noncomputable section

open Set Filter Topology
open scoped NNReal ENNReal
open QuantumZipper (H chiC)

namespace InteractingSLE.Theorem14.SB.S3

open Exist Exist.Staged Exist.StagedLaw Restart GW1W

/-- A side of an actually launched earlier piece, with no original-data
alternative. -/
def StageSide (κ : ℝ) (b : ℝ → ℝ) (jumps : Finset ℝ) (spec : ExplSpec)
    (D : ℕ → (ℝ≥0 → ℝ) × ℝ≥0∞) (k : ℕ) (v : ℝ) : Prop :=
  ∃ j < k, (ExplState.run κ b jumps spec D (j + 1)).2.2.2.1 j ≠ none ∧
    (v = sleLambda κ - instrAngle spec j * chiC κ ∨
      v = -sleLambda κ - instrAngle spec j * chiC κ)

/-- Previously launched sides remain available at all later stages. -/
theorem StageSide.mono {κ : ℝ} {b : ℝ → ℝ} {jumps : Finset ℝ} {spec : ExplSpec}
    {D : ℕ → (ℝ≥0 → ℝ) × ℝ≥0∞} {k n : ℕ} (hkn : k ≤ n) {v : ℝ}
    (hv : StageSide κ b jumps spec D k v) : StageSide κ b jumps spec D n v := by
  obtain ⟨j, hj, hl, he⟩ := hv
  exact ⟨j, hj.trans_le hkn, hl, he⟩

/-- At stage zero the inverse chart lands on the original real line. -/
theorem bdVal_init_real (x₀ y : ℝ) :
    LuM.bdVal (Chart.id.recenter x₀) (y : ℂ) = ((y + x₀ : ℝ) : ℂ) := by
  apply LuM.bdVal_eq_of_tendsto (by simp only [Complex.ofReal_im, le_refl])
  change Tendsto (fun z : ℂ => z + x₀) (𝓝[H] (y : ℂ)) (𝓝 ((y + x₀ : ℝ) : ℂ))
  have hc : Continuous (fun z : ℂ => z + (x₀ : ℂ)) := continuous_id.add continuous_const
  rw [Complex.ofReal_add]
  exact (hc.tendsto (y : ℂ)).mono_left nhdsWithin_le_nhds

/-- The exact explicit-word recursion at a last launch preserves physical
side provenance through its finite Loewner step and all later recenterings. -/
theorem interior_stageSide_of_last_launch {κ : ℝ} (hκ : 0 < κ)
    {b : ℝ → ℝ} {jumps : Finset ℝ} {spec : ExplSpec}
    {D : ℕ → (ℝ≥0 → ℝ) × ℝ≥0∞} (hR : LuM.RegLaunches κ b jumps spec D)
    {k ℓ : ℕ} (hℓk : ℓ < k)
    (hk : (ExplState.run κ b jumps spec D (k + 1)).2.2.2.1 k ≠ none)
    (hl : (ExplState.run κ b jumps spec D (ℓ + 1)).2.2.2.1 ℓ ≠ none)
    (hn : ∀ j, ℓ < j → j < k → (ExplState.run κ b jumps spec D (j + 1)).2.2.2.1 j = none)
    (hreg : IsRegularDriver (D ℓ))
    (hgood : LocalExt.IsDrvGood (recHist (recOf (instrTime spec ℓ) (D ℓ))))
    {oldWord newWord : BoundaryWord}
    (hOld : ∀ y ∉ oldWord.jumps,
      LuM.bdVal (ExplState.run κ b jumps spec D ℓ).2.2.2.2.1 (y : ℂ) ∈ H →
        StageSide κ b jumps spec D ℓ (oldWord.fn y))
    (hword : newWord = BoundaryWord.shiftW
      (((ExplState.run κ b jumps spec D (ℓ + 1)).2.2.2.2.1.1 0 -
        (ExplState.run κ b jumps spec D k).2.2.2.2.1.1 0).re)
      (stopWord κ (oldWord, instrAngle spec ℓ, recOf (instrTime spec ℓ) (D ℓ)))) :
    ∀ y ∉ newWord.jumps,
      LuM.bdVal (ExplState.run κ b jumps spec D k).2.2.2.2.1 (y : ℂ) ∈ H →
        StageSide κ b jumps spec D k (newWord.fn y) := by
  obtain ⟨hstop, a, ha⟩ := last_launch_props hℓk hk hl hn
  obtain ⟨⟨c, θ⟩, hcθ⟩ := Option.ne_none_iff_exists'.1 hl
  have hP := hR ℓ c θ hcθ
  have hBOld := GW1WalkFinish.hasBdryLimits_chart_run spec D hR ℓ
  have hBAfter := GW1WalkFinish.hasBdryLimits_chart_run spec D hR (ℓ + 1)
  have hAfter : (ExplState.run κ b jumps spec D (ℓ + 1)).2.2.2.2.1 =
      (ExplState.run κ b jumps spec D ℓ).2.2.2.2.1.loewner
        (rdrv (recOf (instrTime spec ℓ) (D ℓ))) (rtime (recOf (instrTime spec ℓ) (D ℓ))) := by
    obtain ⟨-, he, -⟩ := eq_launch_of_launches spec D hcθ
    rw [he, chart_launch _ _ _ _ _ hstop, rdrv_recOf, recDrv_eq_stopDrv hreg hgood, rtime_recOf]
    rfl
  have hB : HasBdryLimits (QuantumZipper.fwdMapInv
      (rdrv (recOf (instrTime spec ℓ) (D ℓ))) (rtime (recOf (instrTime spec ℓ) (D ℓ)))) := by
    rw [rdrv_recOf, recDrv_eq_stopDrv hreg hgood, rtime_recOf]
    exact hP.hasBdryLimits hstop
  have ha' : ((ExplState.run κ b jumps spec D (ℓ + 1)).2.2.2.2.1.1 0 -
      (ExplState.run κ b jumps spec D k).2.2.2.2.1.1 0).re = a := by
    simp only [ha, Chart.recenter, sub_sub_cancel, Complex.ofReal_re]
  rw [ha'] at hword
  intro y hy hyH
  rw [hword, BoundaryWord.fn_shiftW]
  have hyJ : y + a ∉ (stopWord κ (oldWord, instrAngle spec ℓ,
      recOf (instrTime spec ℓ) (D ℓ))).jumps := by
    intro h
    apply hy
    rw [hword, BoundaryWord.jumps_shiftW]
    exact Finset.mem_image.2 ⟨y + a, h, by ring⟩
  rw [ha, bdVal_recenter_real hBAfter] at hyH
  change LuM.bdVal (ExplState.run κ b jumps spec D (ℓ + 1)).2.2.2.2.1 ((y + a : ℝ) : ℂ) ∈ H at hyH
  rw [hAfter] at hyH
  exact stopWord_interior_values_bdVal hκ hBOld hB
    (fun x hx hxH => (hOld x hx hxH).mono hℓk.le)
    ⟨ℓ, hℓk, hl, Or.inr rfl⟩ ⟨ℓ, hℓk, hl, Or.inl rfl⟩ hyJ hyH

end InteractingSLE.Theorem14.SB.S3
