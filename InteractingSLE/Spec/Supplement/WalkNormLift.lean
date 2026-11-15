/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.WalkInfPair
import InteractingSLE.Spec.Supplement.GW2aContStepAux
import InteractingSLE.Spec.Supplement.WalkSideSpec
import InteractingSLE.Spec.Supplement.WalkSideDom

/-!
# Theorem 1.4's walk leaves: the lifts of run and prefix charts are derivative logarithms

Packet PROVE-T14-WALKNORM. The lift `c.2.2` of every chart of a run (built from the identity, real recentrings and
centred Loewner stages) is the imaginary part of an analytic logarithm of the derivative of its forward map on its
domain (Specification p. 2, "let `L_ψ` be the chosen analytic logarithm of `ψ'`"; the hydrodynamic branch
`logDerivFwd` of each stage, `isDerivLog_fwdMap`, composed by the chain rule). This is what the Schwarz reflection
of a transition between two charts needs (`WalkNormTrans`).

* `Chart.HasDerivLift c`: `c.2.2 = Im L` on `c.dom` for an analytic logarithm `L` of `c.1′`;
* closure under `Chart.id`, `Chart.recenter` and `Chart.loewner` (`HasDerivLift.loewner`);
* **`hasDerivLift_runChart`**: the chart of a run whose launched pieces are regular;
* **`hasDerivLift_prefixChart`** / **`isConformal_prefixChart`**: the prefix chart of a recorded piece.

Deterministic.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Filter Set Topology Complex
open scoped NNReal ENNReal
open QuantumZipper (H Hbar fwdMap fwdMapInv fwdHull logDerivFwd)

namespace InteractingSLE

/-- The lift of the chart `c` is the imaginary part of an analytic logarithm of the derivative of its forward map
on its domain. -/
def Chart.HasDerivLift (c : Chart) : Prop :=
  ∃ L : ℂ → ℂ, IsDerivLog c.1 L c.dom ∧ ∀ z ∈ (c.dom : Set ℂ), c.2.2 z = (L z).im

namespace Theorem14.WalkNorm

variable {c : Chart}

theorem coe_dom_id : ((Chart.id.dom : TopologicalSpace.Opens ℂ) : Set ℂ) = H := by
  rw [Chart.isConformal_id.coe_dom]
  ext z
  simp [Chart.id]

theorem hasDerivLift_id : Chart.id.HasDerivLift := by
  refine ⟨fun _ => 0, ⟨differentiableOn_const _, fun z _ => ?_⟩, fun z _ => ?_⟩
  · change exp 0 = deriv (fun z : ℂ => z) z
    rw [exp_zero, deriv_id'']
  · change (0 : ℝ) = (0 : ℂ).im
    simp

theorem HasDerivLift.recenter (h : c.HasDerivLift) (a : ℝ) : (c.recenter a).HasDerivLift := by
  obtain ⟨L, hL, hlift⟩ := h
  rw [Chart.HasDerivLift, WalkSide.dom_recenter]
  refine ⟨L, ⟨hL.1, fun z hz => ?_⟩, hlift⟩
  change exp (L z) = deriv (fun w => c.1 w - (a : ℂ)) z
  rw [deriv_sub_const, hL.2 z hz]

/-- The domain of a Loewner stage of a conformal chart lies in the old domain, off the stage's hull. -/
theorem mem_dom_of_mem_dom_loewner (hc : c.IsConformal) {W : ℝ → ℝ} (hW : Continuous W) (hW0 : W 0 = 0) {t : ℝ}
    (ht : 0 ≤ t) {z : ℂ} (hz : z ∈ (c.loewner W t).dom) : z ∈ c.dom ∧ c.1 z ∈ H \ fwdHull W t := by
  rw [← SetLike.mem_coe, (hc.loewner hW hW0 ht).coe_dom] at hz
  obtain ⟨w, hw, rfl⟩ := hz
  have hwH : fwdMapInv W t w ∈ H := QuantumZipper.RS.fwdMapInv_mem_H hW hW0 ht hw
  refine ⟨hc.inv_mem_dom hwH, ?_⟩
  change c.1 (c.2.1 (fwdMapInv W t w)) ∈ H \ fwdHull W t
  rw [hc.2.2 _ hwH, ← QuantumZipper.RS.image_fwdMapInv_H hW hW0 ht]
  exact mem_image_of_mem _ hw

theorem HasDerivLift.loewner (hc : c.IsConformal) (h : c.HasDerivLift) {W : ℝ → ℝ} (hW : Continuous W)
    (hW0 : W 0 = 0) {t : ℝ} (ht : 0 ≤ t) : (c.loewner W t).HasDerivLift := by
  obtain ⟨L, hL, hlift⟩ := h
  have hF := isDerivLog_fwdMap hW ht
  have hUo : IsOpen (H \ fwdHull W t) := QuantumZipper.FwdHolo.isOpen_compl_fwdHull hW ht
  have hsub : ((c.loewner W t).dom : Set ℂ) ⊆ c.dom := fun z hz =>
    (mem_dom_of_mem_dom_loewner hc hW hW0 ht hz).1
  have hmaps : MapsTo c.1 ((c.loewner W t).dom : Set ℂ) (H \ fwdHull W t) := fun z hz =>
    (mem_dom_of_mem_dom_loewner hc hW hW0 ht hz).2
  refine ⟨fun z => logDerivFwd W t (c.1 z) + L z, ⟨?_, fun z hz => ?_⟩, fun z hz => ?_⟩
  · exact (hF.1.comp (hc.differentiableOn_fwd.mono hsub) hmaps).add (hL.1.mono hsub)
  · have hzc := hsub hz
    have hd1 : DifferentiableAt ℂ (fwdMap W t) (c.1 z) :=
      (QuantumZipper.FwdHolo.differentiableOn_fwdMap hW ht).differentiableAt (hUo.mem_nhds (hmaps hz))
    have hd2 : DifferentiableAt ℂ c.1 z :=
      hc.differentiableOn_fwd.differentiableAt (c.dom.isOpen.mem_nhds hzc)
    change exp (logDerivFwd W t (c.1 z) + L z) = deriv (fun w => fwdMap W t (c.1 w)) z
    rw [exp_add, hF.2 _ (hmaps hz), hL.2 z hzc]
    exact (deriv_comp z hd1 hd2).symm
  · change (logDerivFwd W t (c.1 z)).im + c.2.2 z = (logDerivFwd W t (c.1 z) + L z).im
    rw [hlift z (hsub hz), add_im]

/-! ### Run charts -/

section Run

variable {κ : ℝ} {b : ℝ → ℝ} {jumps : Finset ℝ}

open Exist.Staged Exist.StagedLaw GW2aCont in
/-- **The chart of a run whose launched pieces are regular has a derivative lift.** -/
theorem hasDerivLift_runChart (spec : ExplSpec) (D : ℕ → (ℝ≥0 → ℝ) × ℝ≥0∞) :
    ∀ k, (∀ j < k, ∀ (c : Chart) (θ : ℝ), (ExplState.run κ b jumps spec D (j + 1)).2.2.2.1 j = some (c, θ) →
      GW1P.PieceRegular (D j).1 (min (instrTime spec j) (D j).2)) →
      (ExplState.run κ b jumps spec D k).2.2.2.2.1.HasDerivLift
  | 0, _ => HasDerivLift.recenter hasDerivLift_id spec.1
  | k + 1, hreg => by
    have hreg' : ∀ j < k, ∀ (c : Chart) (θ : ℝ),
        (ExplState.run κ b jumps spec D (j + 1)).2.2.2.1 j = some (c, θ) →
        GW1P.PieceRegular (D j).1 (min (instrTime spec j) (D j).2) := fun j hj => hreg j (Nat.lt_succ_of_lt hj)
    have hL := hasDerivLift_runChart spec D k hreg'
    have hc := (isConformal_runChart (κ := κ) (b := b) (jumps := jumps) spec D k hreg').1
    rcases hl : (ExplState.run κ b jumps spec D (k + 1)).2.2.2.1 k with _ | ⟨c, θ⟩
    · obtain ⟨a, ha⟩ := chart_run_succ_of_noLaunch (κ := κ) (b := b) (jumps := jumps) spec D hl
      rw [ha]
      exact HasDerivLift.recenter hL a
    · obtain ⟨-, he, -⟩ := eq_launch_of_launches (κ := κ) (b := b) (jumps := jumps) spec D hl
      rw [he]
      by_cases htop : min (instrTime spec k) (D k).2 = ⊤
      · rw [GW2aCont.chart_launch_of_top _ _ _ _ _ htop]
        exact hL
      rw [chart_launch _ _ _ _ _ htop]
      obtain ⟨hU, hU0⟩ := (hreg k (Nat.lt_succ_self k) c θ hl).continuous_stoppedReal
      exact HasDerivLift.loewner hc hL hU hU0 (NNReal.coe_nonneg _)

open Exist.Staged Exist.StagedLaw in
/-- **The prefix chart of a recorded piece of a run with regular pieces is conformal and has a derivative lift.** -/
theorem prefixChart_props (spec : ExplSpec) (D : ℕ → (ℝ≥0 → ℝ) × ℝ≥0∞) (n : ℕ)
    (hreg : ∀ j < n, ∀ (c : Chart) (θ : ℝ), (ExplState.run κ b jumps spec D (j + 1)).2.2.2.1 j = some (c, θ) →
      GW1P.PieceRegular (D j).1 (min (instrTime spec j) (D j).2))
    (hD : ∀ j, IsRegularDriver (D j)) {pre post : List WalkBdry.Piece} {pc : WalkBdry.Piece}
    (h : (ExplState.run κ b jumps spec D n).1 = pre ++ pc :: post) {τ : ℝ≥0} (hτ : (τ : ℝ≥0∞) < pc.2.2) :
    (WalkBdry.prefixChart pc τ).IsConformal ∧ (WalkBdry.prefixChart pc τ).HasDerivLift := by
  obtain ⟨ℓ, hℓ, θ', -, -, hpc⟩ := WalkSide.exists_launch_of_pieces_eq (κ := κ) (b := b) (jumps := jumps) spec D n h
  subst hpc
  have hτ' : (τ : ℝ≥0∞) < min (instrTime spec ℓ) (D ℓ).2 := hτ
  rw [WalkSide.prefixChart_recPiece _ (hD ℓ) hτ']
  have hτζ : (τ : ℝ≥0∞) < (D ℓ).2 := lt_of_lt_of_le hτ' (min_le_right _ _)
  have hmin : min (τ : ℝ≥0∞) (D ℓ).2 = τ := min_eq_left hτζ.le
  have hreg' : ∀ j < ℓ, ∀ (c : Chart) (θ : ℝ),
      (ExplState.run κ b jumps spec D (j + 1)).2.2.2.1 j = some (c, θ) →
      GW1P.PieceRegular (D j).1 (min (instrTime spec j) (D j).2) := fun j hj => hreg j (hj.trans hℓ)
  have hc := (GW2aCont.isConformal_runChart (κ := κ) (b := b) (jumps := jumps) spec D ℓ hreg').1
  have hL := hasDerivLift_runChart (κ := κ) (b := b) (jumps := jumps) spec D ℓ hreg'
  have hWon : ContinuousOn (D ℓ).1 {t : ℝ≥0 | (t : ℝ≥0∞) ≤ min (τ : ℝ≥0∞) (D ℓ).2} :=
    (hD ℓ).1.mono fun t ht => lt_of_le_of_lt (le_trans ht (min_le_left _ _)) hτζ
  have hWc : Continuous fun x : ℝ =>
      (D ℓ).1 (min ((x.toNNReal : ℝ≥0) : ℝ≥0∞) (min (τ : ℝ≥0∞) (D ℓ).2)).toNNReal :=
    (CounterflowRange.continuous_stopped hWon).comp continuous_real_toNNReal
  have hW0 : (fun x : ℝ => (D ℓ).1 (min ((x.toNNReal : ℝ≥0) : ℝ≥0∞) (min (τ : ℝ≥0∞) (D ℓ).2)).toNNReal) 0 = 0 := by
    simp only [Real.toNNReal_zero, ENNReal.coe_zero, zero_le, min_eq_left, ENNReal.toNNReal_zero]
    exact (hD ℓ).2.1
  exact ⟨hc.loewner hWc hW0 (NNReal.coe_nonneg _), HasDerivLift.loewner hc hL hWc hW0 (NNReal.coe_nonneg _)⟩

end Run

end Theorem14.WalkNorm

end InteractingSLE
