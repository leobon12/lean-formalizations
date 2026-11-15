/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW1WalkExitData

/-! # GW1: all geometric assertions of a single finite ordinary stage -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Filter Topology
open scoped NNReal ENNReal
open QuantumZipper (H Hbar)

namespace InteractingSLE.Theorem14.GW1WalkExit

open Exist Exist.Staged Exist.StagedLaw GW1WalkFinish GW1WalkChain GW1Bookkeep

structure FiniteLaunchData (right : Bool) (root : ℝ) (s : ExplState) (k : ℕ)
    (D : (ℝ≥0 → ℝ) × ℝ≥0∞) (θ : ℝ) : Prop where
  profile : OwnProfile right (ExplState.launch s k D θ ⊤)
  point : sideCoord right (stPt (ExplState.launch s k D θ ⊤)) =
    outwardRecord right (ExplState.launch s k D θ ⊤)
  inverse : ExteriorInverse right (ExplState.launch s k D θ ⊤)
  raw : RawRecordBound right root (ExplState.launch s k D θ ⊤)
  piece : ∀ x : ℝ, (x : ℂ) ∈ (stChart s).tipSet
    (fun r => D.1 (min (r : ℝ≥0∞) D.2).toNNReal) D.2 →
      sideCoord right x ≤ outwardRecord right (ExplState.launch s k D θ ⊤)

theorem finiteLaunchData {κ θ root : ℝ} {b : ℝ → ℝ} {right : Bool} {s : ExplState}
    (hOld : RawRecordBound right root s) (hInv : ExteriorInverse right s)
    (hs : OwnProfile right s) (hr : OwnReady right s) (k : ℕ)
    {D : (ℝ≥0 → ℝ) × ℝ≥0∞} (hreg : IsRegularDriver D)
    (hP : GW1P.PieceRegular D.1 D.2)
    (hgood : LocalExt.IsDrvGood (recHist (recOf ⊤ D))) (hfin : D.2 ≠ ⊤)
    (hC : ClassifiedExit κ b right s (ExplState.launch s k D θ ⊤))
    (hF : GW1Z.FiberGood (stChart s) (statePhysicalSet root s)) :
    FiniteLaunchData right root s k D θ := by
  have hmono := outwardRecord_le_launch hs k θ hreg hgood hfin
  have hAlive := fun x hx => alive_of_lt_outwardRecord hs k θ hreg hgood hfin (x := x) hx
  have hpiece := piece_real_bound_of_exteriorInverse hOld hInv hs.isRealChart hmono hP hfin
    (fun x hx => (hAlive x hx).2) hF
  obtain ⟨hprofile, hpoint⟩ := profile_point_of_finite_classified hs hr k hreg hgood hfin hC
  refine ⟨hprofile, hpoint, exteriorInverse_launch hInv hs.isRealChart k θ hP hfin hAlive,
    ?_, hpiece⟩
  intro x hx
  rw [statePhysicalSet_launch] at hx
  simp only [min_eq_right (le_top : D.2 ≤ ⊤)] at hx
  rcases hx with hx | hx
  · exact (hOld x hx).trans hmono
  · exact hpiece x hx

theorem exteriorRecord_of_profile_inverse {right : Bool} {s : ExplState}
    (hB : HasBdryLimits (stChart s).2.1) (hs : OwnProfile right s)
    (hpt : sideCoord right (stPt s) = outwardRecord right s) (hInv : ExteriorInverse right s) :
    ExteriorRecord right s := by
  have hcorr (x : ℝ) (hx : outwardRecord right s < sideCoord right x) :
      extendFrom H (stChart s).2.1 ((stChart s).1 (x : ℂ)) = (x : ℂ) := by
    have hp : (stChart s).1 (x : ℂ) ∈ Hbar := by
      show 0 ≤ ((stChart s).1 (x : ℂ)).im
      rw [hs.isRealChart x]
    have : (𝓝[H] ((stChart s).1 (x : ℂ))).NeBot := GW1P.neBot_nhdsWithin_H hp
    exact tendsto_nhds_unique (hB.tendsto hp) (hInv x hx)
  cases right
  · exact ⟨hs, neg_injective hpt, fun x hx => hcorr x (neg_lt_neg hx)⟩
  · exact ⟨hs, hpt, hcorr⟩

theorem OwnReady.not_done {right : Bool} {s : ExplState} (h : OwnReady right s) :
    stStatus s ≠ stDone := by
  cases right <;> rcases h.1 with h | h <;> rw [h] <;> intro he <;> cases he

theorem LaunchReady.not_done {κ θ : ℝ} {b : ℝ → ℝ} {right : Bool} {s : ExplState}
    (h : LaunchReady κ b θ right s) : stStatus s ≠ stDone := by
  rcases h with h | ⟨h, -⟩ <;> rw [h] <;> intro he <;> cases he

end InteractingSLE.Theorem14.GW1WalkExit
