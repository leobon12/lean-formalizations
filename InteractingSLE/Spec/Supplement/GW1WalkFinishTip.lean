/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW1WalkFinishClear

/-!
# GW1: tip coordinates from the exterior-ray correspondence

The unproved geometric datum `ExteriorRecord` is stated using the ordinary chart and its
canonical boundary extension. Radial tip equalities and existence of boundary limits are
not included in that datum: the former are proved here, and regular pieces supply the latter.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Filter Topology
open scoped NNReal ENNReal
open QuantumZipper (H Hbar)

namespace InteractingSLE.Theorem14.GW1WalkFinish

open Exist Exist.Staged Exist.StagedLaw GW1WalkChain

/-- The own exterior ray is parametrized by the current chart, with inverse boundary
correspondence, and the current point is its endpoint record. This is the local
chart/record geometry still to be obtained from R53 D.4 for the actual walk. -/
def ExteriorRecord (right : Bool) (s : ExplState) : Prop :=
  if right then GW1W.RProf s ∧ stPt s = stRecR s ∧
    ∀ x, stRecR s < x →
      extendFrom H (stChart s).2.1 ((stChart s).1 (x : ℂ)) = (x : ℂ)
  else GW1W.LProf s ∧ stPt s = stRecL s ∧
    ∀ x, x < stRecL s →
      extendFrom H (stChart s).2.1 ((stChart s).1 (x : ℂ)) = (x : ℂ)

theorem boundary_limit_of_exteriorRecord {right : Bool} {s : ExplState}
    (hB : HasBdryLimits (stChart s).2.1) (hE : ExteriorRecord right s) :
    Tendsto (stChart s).2.1 (𝓝[H] 0) (𝓝 (stPt s : ℂ)) := by
  have hr : Tendsto (fun x : ℝ => (x : ℂ)) (𝓝 0) (𝓝[Hbar] 0) := by
    refine tendsto_nhdsWithin_iff.2 ⟨?_, Eventually.of_forall fun x => ?_⟩
    · simpa only [Complex.ofReal_zero] using Complex.continuous_ofReal.tendsto 0
    · show 0 ≤ (x : ℂ).im
      simp only [Complex.ofReal_im, le_refl]
  have hf : ContinuousAt (fun x : ℝ => extendFrom H (stChart s).2.1 (x : ℂ)) 0 :=
    (hB.continuousOn 0 zero_mem_Hbar).tendsto.comp hr
  have hvalue : extendFrom H (stChart s).2.1 0 = (stPt s : ℂ) := by
    cases right
    · obtain ⟨hs, hpt, hinv⟩ := hE
      have h := left_record_value hs hf (fun x hx => by
        simpa only [hs.1.eq_ofReal x] using hinv x hx)
      simpa only [Complex.ofReal_zero, ← hpt] using h
    · obtain ⟨hs, hpt, hinv⟩ := hE
      have h := right_record_value hs hf (fun x hx => by
        simpa only [hs.1.eq_ofReal x] using hinv x hx)
      simpa only [Complex.ofReal_zero, ← hpt] using h
  simpa only [hvalue] using hB.tendsto zero_mem_Hbar

/-- Existence of all run-chart boundary limits reuses the already proved fibre invariant. -/
theorem hasBdryLimits_chart_run {κ : ℝ} {b : ℝ → ℝ} {jumps : Finset ℝ}
    (spec : ExplSpec) (D : ℕ → (ℝ≥0 → ℝ) × ℝ≥0∞)
    (hreg : ∀ k c θ, (ExplState.run κ b jumps spec D (k + 1)).2.2.2.1 k = some (c, θ) →
      GW1P.PieceRegular (D k).1 (min (instrTime spec k) (D k).2)) (n : ℕ) :
    HasBdryLimits (stChart (ExplState.run κ b jumps spec D n)).2.1 := by
  obtain ⟨f, C, hf, -, -⟩ := GW1Z.chartFiber_run spec D hreg n
  exact fun p hp => ⟨f p, hf p hp⟩

/-- The physical seed and terminal tip coordinates follow from exterior correspondence
at the launch and at its finite exit. Regularity supplies every boundary-limit existence. -/
theorem walkTipCoordinates_of_exteriorRecords {κ : ℝ} {b : ℝ → ℝ} {jumps : Finset ℝ}
    {θ : ℝ} {right : Bool} (D : ℕ → (ℝ≥0 → ℝ) × ℝ≥0∞)
    (hreg : ∀ k c θ',
      (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ right) D (k + 1)).2.2.2.1 k =
        some (c, θ') →
      GW1P.PieceRegular (D k).1 (min (instrTime (boundaryWalkSpec b jumps θ right) k) (D k).2))
    (hE : ∀ k, let R := ExplState.run κ b jumps (boundaryWalkSpec b jumps θ right) D
      (R (k + 1)).2.2.2.1 k ≠ none →
        ExteriorRecord right (R k) ∧ ((D k).2 ≠ ⊤ → ExteriorRecord right (R (k + 1)))) :
    WalkTipCoordinates κ b jumps (boundaryWalkSpec b jumps θ right) D := by
  let spec := boundaryWalkSpec b jumps θ right
  let R := ExplState.run κ b jumps spec D
  intro k c θ' hl
  have hln : (R (k + 1)).2.2.2.1 k ≠ none := by rw [hl]; exact Option.some_ne_none _
  have htime : instrTime (boundaryWalkSpec b jumps θ right) k = ⊤ := by
    obtain ⟨hev, hk⟩ := GW1W.even_of_launches_walk hln
    unfold instrTime
    rw [GW1Conn.getElem?_boundaryWalkSpec, ite_eq_left hk, ite_eq_left hev]
  obtain ⟨-, -, hc⟩ := eq_launch_of_launches spec D hl
  obtain ⟨hE0, hE1⟩ := hE k hln
  have hB := hasBdryLimits_chart_run spec D hreg
  have hregk := hreg k c θ' hl
  have hW := hregk.continuous_stoppedReal
  have hW0 : (fun r : ℝ≥0 => (D k).1
      (min (r : ℝ≥0∞) (min (instrTime spec k) (D k).2)).toNNReal) 0 = 0 := by
    simpa only [Real.toNNReal_zero] using hW.2
  constructor
  · rw [hc]
    exact tipAt_zero_of_boundary_limit hW.1 hW0 (boundary_limit_of_exteriorRecord (hB k) hE0)
  · intro hfin
    have hf : (D k).2 ≠ ⊤ := by simpa only [htime, min_eq_right le_top] using hfin
    have hlim := boundary_limit_of_exteriorRecord (hB (k + 1)) (hE1 hf)
    have hrun : R (k + 1) = ExplState.launch (R k) k (D k) θ ⊤ := GW1W.launch_walk hln
    change Tendsto (stChart (R (k + 1))).2.1 (𝓝[H] 0) (𝓝 (stPt (R (k + 1)) : ℂ)) at hlim
    rw [hrun] at hlim
    have ht := tipAt_stop_of_boundary_limit hf hlim
    rw [← hrun] at ht
    rw [hc]
    simpa only [htime, min_eq_right le_top] using ht

end InteractingSLE.Theorem14.GW1WalkFinish
