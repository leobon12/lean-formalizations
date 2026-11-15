/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.SB2LsRec

/-!
# Physical records and hits of a walk launch

Packet PROVE-T14-SB2LIFT (round 9; item 1 of handoff §R8.2, physical form). For a boundary-walk run with regular
launches and a launch at stage `n` with a finite lifetime, the hypotheses of `lAlive_run_iff` at a real point `x` are
collected in **`BeyondOK`**:

* every earlier piece has a finite lifetime and leaves `x` alive;
* `x` is off the closure of every filled prefix up to stage `n`;
* the inverse chart has boundary limit `x` at `c.1 x`;
* `c.1 x ≠ 0`.

Then:

* **`lRecR_run_eq`**: if `BeyondOK` holds at every point beyond the record, the new right record is the supremum of
  the points beyond the record that lie in the closure of the new filled prefix;
* **`lHit_run_iff`**: at a point with `BeyondOK`, the piece hits `x` at the stop iff
  - for every time `r ∈ [0, T)`, `x` is off the closure of the filled set made of the old prefix and the physical
    piece up to time `r` (`bdVal` of the chart along the trace);
  - and `x` is on the closure of the new filled prefix.

  The intermediate times use lemma (T) for the truncated trace. The old prefix enters through the compact set of
  `image_runChart_walk` (`fillH_eq_of_union_im`).

Both are statements about physical sets only, so they transfer between two runs whose physical sets correspond (the
lifted walk of SB2(2) against the actual lower walk).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Filter Topology Metric
open scoped NNReal ENNReal
open QuantumZipper (H Hbar fwdMap fwdHull IsForwardSol)

namespace InteractingSLE.Theorem14.SB.Lk

open Exist Exist.Staged Exist.StagedLaw LuM

variable {κ θ : ℝ} {b : ℝ → ℝ} {jumps : Finset ℝ} {right : Bool}

/-- **The hypotheses of physical aliveness at a real point** (stage `n` of a walk run). -/
def BeyondOK (κ : ℝ) (b : ℝ → ℝ) (jumps : Finset ℝ) (θ : ℝ) (right : Bool) (D : ℕ → (ℝ≥0 → ℝ) × ℝ≥0∞) (n : ℕ)
    (x : ℝ) : Prop :=
  (∀ j < n, (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ right) D (j + 1)).2.2.2.1 j ≠ none →
    (D j).2 ≠ ⊤ ∧ lAlive (stChart (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ right) D j)) ⊤ (D j) x) ∧
  (∀ j ≤ n, (x : ℂ) ∉ closure (fillH (SB.prefixPhysSet κ b jumps (boundaryWalkSpec b jumps θ right) D j))) ∧
  Tendsto (stChart (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ right) D n)).2.1
    (𝓝[H] ((stChart (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ right) D n)).1 x)) (𝓝 (x : ℂ)) ∧
  (stChart (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ right) D n)).1 x ≠ 0

/-- **The new right record of a walk launch, physically.** -/
theorem lRecR_run_eq {D : ℕ → (ℝ≥0 → ℝ) × ℝ≥0∞}
    (hP : RegLaunches κ b jumps (boundaryWalkSpec b jumps θ right) D) {n : ℕ} {c : Chart} {θ' : ℝ}
    (hl : (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ right) D (n + 1)).2.2.2.1 n = some (c, θ'))
    (hfin : (D n).2 ≠ ⊤)
    (hok : ∀ x : ℝ, stRecR (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ right) D n) < x →
      BeyondOK κ b jumps θ right D n x) :
    lRecR (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ right) D n) ⊤ (D n) =
      sSup (insert (stRecR (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ right) D n))
        {x : ℝ | stRecR (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ right) D n) < x ∧
          (x : ℂ) ∈ closure (fillH (SB.prefixPhysSet κ b jumps (boundaryWalkSpec b jumps θ right) D (n + 1)))}) :=
  lRecR_eq_of_alive_iff fun x hx => by
    obtain ⟨h1, h2, h3, h4⟩ := hok x hx
    exact lAlive_run_iff hP hl hfin x h1 h2 h3 h4

/-- **Physical hits of a walk launch.** -/
theorem lHit_run_iff {D : ℕ → (ℝ≥0 → ℝ) × ℝ≥0∞}
    (hP : RegLaunches κ b jumps (boundaryWalkSpec b jumps θ right) D) {n : ℕ} {c : Chart} {θ' : ℝ}
    (hl : (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ right) D (n + 1)).2.2.2.1 n = some (c, θ'))
    (hfin : (D n).2 ≠ ⊤) {x : ℝ} (hok : BeyondOK κ b jumps θ right D n x) :
    lHit (stChart (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ right) D n)) ⊤ (D n) x ↔
      (∀ r : ℝ, 0 ≤ r → r < stopTime ⊤ (D n) →
        (x : ℂ) ∉ closure (fillH (SB.prefixPhysSet κ b jumps (boundaryWalkSpec b jumps θ right) D n ∪
          bdVal (stChart (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ right) D n)) ''
            (trOf (D n) '' Icc 0 r.toNNReal)))) ∧
      (x : ℂ) ∈ closure (fillH (SB.prefixPhysSet κ b jumps (boundaryWalkSpec b jumps θ right) D (n + 1))) := by
  obtain ⟨hlaunch, hoff, hbd, hne⟩ := hok
  set spec := boundaryWalkSpec b jumps θ right with hspec
  set s₀ := ExplState.run κ b jumps spec D n with hs₀
  have hlne : (ExplState.run κ b jumps spec D (n + 1)).2.2.2.1 n ≠ none := by rw [hl]; simp
  have hPR := pieceRegular_of_launch hP hlne
  have hcc := isConformal_runChart_of_reg spec hP n
  have hinj : InjOn (stChart s₀).2.1 H := fun w hw w' hw' h => by rw [← hcc.2.2 w hw, h, hcc.2.2 w' hw']
  -- the boundary map of the launch chart
  obtain ⟨hbe, -⟩ := GW1P.isClosed_pieces_run spec D hP n
  obtain ⟨ĝ, C, hf, hC⟩ := hbe
  have hĝ : ContinuousOn ĝ {z : ℂ | 0 ≤ z.im} := GW1P.continuousOn_of_tendsto hf
  have hgg : EqOn ĝ (stChart s₀).2.1 H := fun z hz => by
    have : (𝓝[H] z).NeBot := GW1P.neBot_nhdsWithin_H (QuantumZipper.H_subset_Hbar hz)
    exact tendsto_nhds_unique (hf z (QuantumZipper.H_subset_Hbar hz))
      ((hcc.1.continuousOn.continuousAt (QuantumZipper.isOpen_H.mem_nhds hz)).tendsto.mono_left nhdsWithin_le_nhds)
  have hbdV : ∀ p ∈ Hbar, bdVal (stChart s₀) p = ĝ p := fun p hp => bdVal_eq_of_tendsto hp (hf p hp)
  -- the old prefix through a compact set
  have hfin' : ∀ j < n, (ExplState.run κ b jumps spec D (j + 1)).2.2.2.1 j ≠ none → (D j).2 ≠ ⊤ :=
    fun j hj hj' => (hlaunch j hj hj').1
  obtain ⟨K, hKc, hKR, hDK⟩ := image_runChart_walk hP n hfin'
  -- the chart point and the injectivity at it
  obtain ⟨hfc, hre⟩ := continuousWithinAt_runChart_fwd hP x n hlaunch hoff
  have hyH : (stChart s₀).1 x ∈ Hbar := show 0 ≤ ((stChart s₀).1 x).im by rw [hre]
  have hyx : ĝ ((stChart s₀).1 x) = x := by
    have : (𝓝[H] ((stChart s₀).1 x)).NeBot := GW1P.neBot_nhdsWithin_H hyH
    exact tendsto_nhds_unique (hf _ hyH) hbd
  have hinjy := injAt_of_continuousWithinAt hcc.2.1 hcc.2.2 hĝ hgg (by simp) hyx hfc rfl
  have hfKP : fillH K = fillH (SB.prefixPhysSet κ b jumps spec D n) := fillH_eq_of_union_im hKR
  have hy0 : ĝ ((stChart s₀).1 x) ∉ closure (fillH K) := by rw [hyx, hfKP]; exact hoff n le_rfl
  -- the trace
  have hα := isGeneratingTrace_trOf hPR
  have hαH : ∀ t : ℝ≥0, (t : ℝ≥0∞) ≤ (D n).2 → 0 ≤ (trOf (D n) t).im := fun t ht =>
    im_nonneg_of_isGeneratingTrace_le hα hPR.2.1 hPR.1 ht
  rw [lHit_iff_closure hPR hfin hre hne]
  refine and_congr ?_ ?_
  · refine forall_congr' fun r => imp_congr_right fun hr0 => imp_congr_right fun hrT => ?_
    have hrle : ((r.toNNReal : ℝ≥0) : ℝ≥0∞) ≤ (D n).2 := by
      obtain ⟨-, -, htime⟩ := stopDrv_eq_and_isGeneratingTrace hPR hfin
      rw [← ENNReal.coe_toNNReal hfin, ENNReal.coe_le_coe, ← NNReal.coe_le_coe, Real.coe_toNNReal _ hr0]
      rw [htime] at hrT
      exact hrT.le
    have hAr : IsCompact (trOf (D n) '' Icc 0 r.toNNReal) := isCompact_Icc.image_of_continuousOn
      (hα.2.1.mono fun t ht => (ENNReal.coe_le_coe.2 ht.2).trans hrle)
    have hArH : trOf (D n) '' Icc 0 r.toNNReal ⊆ Hbar := by
      rintro _ ⟨t, ht, rfl⟩
      exact hαH t ((ENNReal.coe_le_coe.2 ht.2).trans hrle)
    have hDr := image_H_diff_fillH_of_chart hcc.1 hinj hĝ hgg hC hKc hDK hAr hArH
    have hiff := mem_closure_fillH_iff_of_chart hinj hĝ hgg hDK hDr hAr hyH hy0 hinjy
    have hfill : fillH (K ∪ ĝ '' (trOf (D n) '' Icc 0 r.toNNReal)) =
        fillH (SB.prefixPhysSet κ b jumps spec D n ∪ bdVal (stChart s₀) '' (trOf (D n) '' Icc 0 r.toNNReal)) := by
      have himg : bdVal (stChart s₀) '' (trOf (D n) '' Icc 0 r.toNNReal) =
          ĝ '' (trOf (D n) '' Icc 0 r.toNNReal) := image_congr fun p hp => hbdV p (hArH hp)
      rw [himg]
      refine fillH_eq_of_union_im ?_
      rw [union_right_comm, hKR, union_right_comm]
    rw [hyx, hfill] at hiff
    exact not_congr hiff
  · have h1 := lAlive_run_iff hP hl hfin x hlaunch hoff hbd hne
    have h2 := lAlive_iff_notMem_closure_fillH hPR hfin hre hne
    constructor
    · intro hm
      by_contra hn
      exact (h2.1 (h1.2 hn)) hm
    · intro hm
      by_contra hn
      exact h1.1 (h2.2 hn) hm

end InteractingSLE.Theorem14.SB.Lk
