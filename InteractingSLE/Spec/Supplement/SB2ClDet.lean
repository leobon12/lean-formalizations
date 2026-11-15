/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.SB2CkEntr
import InteractingSLE.Spec.Supplement.SB2JyEnd
import InteractingSLE.Spec.Dimension.TraceBridge

/-!
# The entrance time is decided by the record capped at the query time (deterministic core)

Packet PROVE-SB2-CONDFIN (round 6; root route, step 1). For a launched regular piece, `{entrTime ≤ s}` is a function of
the state at the launch and of the piece's record capped at `s` (`retOf s`):

* `trOf_eq_of_agree`: two regular pieces agreeing up to `s` (below both lifetimes) have the same chosen trace before
  `s` (`IsGeneratingTrace.trace_eq`: the chosen trace is the library trace; the inverse maps before `s` only read the
  driver on `[0, s]`, `fwdMapInv_eq_of_eqOn`);
* `pcPt_eqOn_of_agree`: their points agree on `[0, s]` (continuity at `s`, `Lk.continuousOn_pcPt_launch`);
* **`entrTime_le_iff_of_retOf_eq`**: two launched regular pieces from the same state with the same record capped at `s`
  have `entrTime ≤ s` together.

Deterministic (no input).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Filter Topology
open scoped NNReal ENNReal

namespace InteractingSLE.Theorem14.SB.Cl

open Exist Exist.Staged Exist.StagedLaw Lk GW1W LuM

/-- **Two regular pieces agreeing up to `s` (below both lifetimes) have the same chosen trace before `s`.** -/
theorem trOf_eq_of_agree {e e' : Drv} (hP : GW1P.PieceRegular e.1 e.2) (hP' : GW1P.PieceRegular e'.1 e'.2)
    {s : ℝ≥0} (hs : (s : ℝ≥0∞) < e.2) (hs' : (s : ℝ≥0∞) < e'.2) (h : ∀ r : ℝ≥0, r ≤ s → e.1 r = e'.1 r)
    {t : ℝ≥0} (ht : t < s) : trOf e t = trOf e' t := by
  have hη := isGeneratingTrace_trOf hP
  have hη' := isGeneratingTrace_trOf hP'
  have htT : (t : ℝ≥0∞) < e.2 := lt_trans (ENNReal.coe_lt_coe.2 ht) hs
  have htT' : (t : ℝ≥0∞) < e'.2 := lt_trans (ENNReal.coe_lt_coe.2 ht) hs'
  have h1 := hη.trace_eq (hP.2.1.mono fun r (hr : (r : ℝ≥0∞) < e.2) => show (r : ℝ≥0∞) ≤ e.2 from le_of_lt hr)
    hP.1 htT
  have h1' := hη'.trace_eq
    (hP'.2.1.mono fun r (hr : (r : ℝ≥0∞) < e'.2) => show (r : ℝ≥0∞) ≤ e'.2 from le_of_lt hr) hP'.1 htT'
  rw [← h1, ← h1']
  have hinv : QuantumZipper.fwdMapInv (fun x : ℝ => e.1 x.toNNReal) (t : ℝ) =
      QuantumZipper.fwdMapInv (fun x : ℝ => e'.1 x.toNNReal) (t : ℝ) := by
    refine fwdMapInv_eq_of_eqOn t.2 (NNReal.coe_lt_coe.2 ht) fun x hx => ?_
    have hxs : x.toNNReal ≤ s := by
      rw [Real.toNNReal_le_iff_le_coe]
      exact hx.2
    exact h _ hxs
  unfold QuantumZipper.trace
  rw [hinv]

variable {κ θ : ℝ} {b : ℝ → ℝ} {jumps : Finset ℝ}

/-- **The points of two launched regular pieces from the same state, agreeing up to `s`, agree on `[0, s]`.** -/
theorem pcPt_eqOn_of_agree {D D' : ℕ → Drv} (hP : RegLaunches κ b jumps (boundaryWalkSpec b jumps θ true) D)
    (hP' : RegLaunches κ b jumps (boundaryWalkSpec b jumps θ true) D') {n : ℕ}
    (hl : (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) D (n + 1)).2.2.2.1 n ≠ none)
    (hl' : (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) D' (n + 1)).2.2.2.1 n ≠ none)
    (hrun : ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) D n =
      ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) D' n)
    {s : ℝ≥0} (hs : (s : ℝ≥0∞) < (D n).2) (hs' : (s : ℝ≥0∞) < (D' n).2)
    (h : ∀ r : ℝ≥0, r ≤ s → (D n).1 r = (D' n).1 r) :
    EqOn (pcPt (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) D n) (D n))
      (pcPt (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) D' n) (D' n)) {t : ℝ≥0 | t ≤ s} := by
  have hPR := pieceRegular_of_launch hP hl
  have hPR' := pieceRegular_of_launch hP' hl'
  have hc := continuousOn_pcPt_launch hP hl
  have hc' := continuousOn_pcPt_launch hP' hl'
  have hlt : EqOn (pcPt (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) D n) (D n))
      (pcPt (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) D' n) (D' n)) {t : ℝ≥0 | t < s} := by
    intro t ht
    unfold pcPt
    rw [hrun, trOf_eq_of_agree hPR hPR' hs hs' h ht]
  rcases eq_or_ne s 0 with rfl | hs0
  · intro t ht
    have ht0 : t = 0 := le_antisymm ht (zero_le)
    subst ht0
    unfold pcPt
    rw [hrun, (isGeneratingTrace_trOf hPR).1, (isGeneratingTrace_trOf hPR').1]
  · have hsub : {t : ℝ≥0 | t ≤ s} ⊆ {t : ℝ≥0 | (t : ℝ≥0∞) ≤ (D n).2} := fun t ht =>
      (ENNReal.coe_le_coe.2 ht).trans hs.le
    have hsub' : {t : ℝ≥0 | t ≤ s} ⊆ {t : ℝ≥0 | (t : ℝ≥0∞) ≤ (D' n).2} := fun t ht =>
      (ENNReal.coe_le_coe.2 ht).trans hs'.le
    have hcl : {t : ℝ≥0 | t ≤ s} ⊆ closure {t : ℝ≥0 | t < s} := by
      have e1 : {t : ℝ≥0 | t < s} = Iio s := rfl
      have e2 : {t : ℝ≥0 | t ≤ s} = Iic s := rfl
      rw [e1, e2, closure_Iio' ⟨0, pos_iff_ne_zero.2 hs0⟩]
    exact hlt.of_subset_closure (hc.mono hsub) (hc'.mono hsub') (fun t (ht : t < s) => show t ≤ s from le_of_lt ht) hcl

/-- **The entrance time is decided by the record capped at `s`**: two launched regular pieces from the same state with
the same record capped at `s` have `entrTime ≤ s` together. -/
theorem entrTime_le_iff_of_retOf_eq {D D' : ℕ → Drv}
    (hP : RegLaunches κ b jumps (boundaryWalkSpec b jumps θ true) D)
    (hP' : RegLaunches κ b jumps (boundaryWalkSpec b jumps θ true) D') {n : ℕ}
    (hl : (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) D (n + 1)).2.2.2.1 n ≠ none)
    (hrun : ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) D n =
      ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) D' n)
    {s : ℝ≥0} (hrec : retOf (s : ℝ≥0∞) (D n) = retOf (s : ℝ≥0∞) (D' n)) (R : ℝ) :
    Ck.entrTime (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) D n) (D n) R ≤ s ↔
      Ck.entrTime (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) D' n) (D' n) R ≤ s := by
  have hl' : (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) D' (n + 1)).2.2.2.1 n ≠ none := by
    rw [← launches_run_succ_of_run_eq _ hrun]
    exact hl
  rw [Ck.entrTime_le_iff hP hl R, Ck.entrTime_le_iff hP' hl' R]
  have hflag : (D n).2 ≤ s ↔ (D' n).2 ≤ s := by
    have h3 := congrArg (fun r => r.2.2) hrec
    simp only [retOf, decide_eq_decide] at h3
    exact h3
  by_cases hζ : (D n).2 ≤ s
  · exact iff_of_true (Or.inr hζ) (Or.inr (hflag.1 hζ))
  · have hζ' : ¬ (D' n).2 ≤ s := fun h => hζ (hflag.2 h)
    push Not at hζ hζ'
    have hagree : ∀ r : ℝ≥0, r ≤ s → (D n).1 r = (D' n).1 r := by
      intro r hr
      have h1 := congrFun (congrArg Prod.fst hrec) r
      simp only [retOf] at h1
      rw [min_eq_left hζ.le, min_eq_left hζ'.le, min_eq_left (ENNReal.coe_le_coe.2 hr),
        ENNReal.toNNReal_coe] at h1
      exact h1
    have heq := pcPt_eqOn_of_agree hP hP' hl hl' hrun hζ hζ' hagree
    rw [min_eq_left hζ.le, min_eq_left hζ'.le]
    simp only [hζ.not_ge, hζ'.not_ge, or_false]
    constructor
    · rintro ⟨t, ht, htR⟩
      exact ⟨t, ht, by rw [← heq (ENNReal.coe_le_coe.1 ht)]; exact htR⟩
    · rintro ⟨t, ht, htR⟩
      exact ⟨t, ht, by rw [heq (ENNReal.coe_le_coe.1 ht)]; exact htR⟩

end InteractingSLE.Theorem14.SB.Cl
