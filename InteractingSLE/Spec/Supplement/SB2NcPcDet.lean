/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.SB2NcRhoM
import InteractingSLE.Spec.Supplement.GW4LeafPiece

/-!
# B's piece up to time `t` is decided by the capped run

Packet PROVE-AUX61-NOJUMP (round 21, D34, component B), deterministic. The line filtration at time `t` observes B's
stage `ℓ` through the program capped at own time `t` (`WalkSide.capSpec`). Its run after instruction `ℓ` records the
stopped piece (`WalkSide.recPiece`: the chart, the driver stopped at `min t ζ`, and `min t ζ`). So two families
whose capped runs agree have the same `min t ζ` and the same piece on `[0, min t ζ]`:

* `trOf_eq_of_eqOn` (the chosen trace only sees the driver before the time);
* **`pcPt_eq_of_capRun_eq`**.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Filter Set Topology
open scoped NNReal ENNReal

namespace InteractingSLE.Theorem14.SB.Nc

open Exist Exist.Staged Exist.StagedLaw LuM Lk WalkSide

/-- **The chosen trace only sees the driver before the time**: two regular drivers agreeing up to `S` (below both
lifetimes) have the same chosen trace on `[0, S]`. -/
theorem trOf_eq_of_eqOn {e e' : (ℝ≥0 → ℝ) × ℝ≥0∞} (h : GW1P.PieceRegular e.1 e.2) (h' : GW1P.PieceRegular e'.1 e'.2)
    {S : ℝ≥0∞} (hS : S ≤ e.2) (hS' : S ≤ e'.2) (hww : ∀ s : ℝ≥0, (s : ℝ≥0∞) ≤ S → e.1 s = e'.1 s) :
    ∀ s : ℝ≥0, (s : ℝ≥0∞) ≤ S → trOf e s = trOf e' s := by
  have hb := WalkInf.isGeneratingTrace_min (isGeneratingTrace_trOf h) S
  rw [min_eq_left hS] at hb
  have hb' := WalkInf.isGeneratingTrace_min (isGeneratingTrace_trOf h') S
  rw [min_eq_left hS'] at hb'
  have hb'' : IsGeneratingTrace e.1 S (trOf e') :=
    Sec5.CrossRestart.isGeneratingTrace_congr_drive hb' fun t ht => hww t ht.le
  intro s hs
  exact (GW4Leaf.eqOn_of_isGeneratingTrace hb hb''
    (h.2.1.mono fun r (hr : (r : ℝ≥0∞) < S) => show (r : ℝ≥0∞) ≤ e.2 from hr.le.trans hS) h.1 s hs).symm

variable {κ : ℝ} {b : ℝ → ℝ} {jumps : Finset ℝ} {θ : ℝ}

/-- **The capped run decides B's piece up to time `t`.** -/
theorem pcPt_eq_of_capRun_eq {ℓ : ℕ} (hℓ : ℓ ≤ (boundaryWalkSpec b jumps θ true).2.2.length)
    (hwℓ : (boundaryWalkSpec b jumps θ true).2.2[ℓ]? = some (Sum.inl (θ, ⊤)))
    {D D' : ℕ → (ℝ≥0 → ℝ) × ℝ≥0∞} (hP : RegLaunches κ b jumps (boundaryWalkSpec b jumps θ true) D)
    (hP' : RegLaunches κ b jumps (boundaryWalkSpec b jumps θ true) D')
    (hl : (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) D (ℓ + 1)).2.2.2.1 ℓ ≠ none)
    (hl' : (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) D' (ℓ + 1)).2.2.2.1 ℓ ≠ none)
    (t : ℝ≥0∞)
    (hrun : ∀ n, n ≤ ℓ + 1 → ExplState.run κ b jumps (capSpec (boundaryWalkSpec b jumps θ true) ℓ θ t) D n =
      ExplState.run κ b jumps (capSpec (boundaryWalkSpec b jumps θ true) ℓ θ t) D' n) :
    ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) D ℓ =
        ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) D' ℓ ∧
      min t (D ℓ).2 = min t (D' ℓ).2 ∧
      ∀ s : ℝ≥0, (s : ℝ≥0∞) ≤ min t (D ℓ).2 →
        pcPt (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) D ℓ) (D ℓ) s =
          pcPt (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) D' ℓ) (D' ℓ) s := by
  set w := boundaryWalkSpec b jumps θ true with hw
  have hrℓ : ExplState.run κ b jumps w D ℓ = ExplState.run κ b jumps w D' ℓ := by
    rw [← run_capSpec_of_le (θ := θ) (τ := t) hℓ D le_rfl, ← run_capSpec_of_le (θ := θ) (τ := t) hℓ D' le_rfl]
    exact hrun ℓ (Nat.le_succ ℓ)
  obtain ⟨⟨c, θ₁⟩, hc⟩ := Option.ne_none_iff_exists'.1 hl
  obtain ⟨⟨c', θ₁'⟩, hc'⟩ := Option.ne_none_iff_exists'.1 hl'
  have hp1 := pieces_run_capSpec_succ (κ := κ) (b := b) (jumps := jumps) hℓ hwℓ D hc t
  have hp2 := pieces_run_capSpec_succ (κ := κ) (b := b) (jumps := jumps) hℓ hwℓ D' hc' t
  have hpe := congrArg Prod.fst (hrun (ℓ + 1) le_rfl)
  rw [hp1, hp2, hrℓ] at hpe
  have hrp : recPiece (ExplState.run κ b jumps w D' ℓ) (D ℓ) t =
      recPiece (ExplState.run κ b jumps w D' ℓ) (D' ℓ) t := by
    have := List.append_cancel_left hpe
    simpa using this
  have hmin : min t (D ℓ).2 = min t (D' ℓ).2 := congrArg (fun x => x.2.2) hrp
  have hpath : (fun r : ℝ≥0 => (D ℓ).1 (min (r : ℝ≥0∞) (min t (D ℓ).2)).toNNReal) =
      fun r : ℝ≥0 => (D' ℓ).1 (min (r : ℝ≥0∞) (min t (D' ℓ).2)).toNNReal := congrArg (fun x => x.2.1) hrp
  have hR := pieceRegular_of_launch (κ := κ) (b := b) (jumps := jumps) (θ := θ) (right := true) hP hl
  have hR' := pieceRegular_of_launch (κ := κ) (b := b) (jumps := jumps) (θ := θ) (right := true) hP' hl'
  have hww : ∀ s : ℝ≥0, (s : ℝ≥0∞) ≤ min t (D ℓ).2 → (D ℓ).1 s = (D' ℓ).1 s := fun s hs => by
    have h1 := congrFun hpath s
    simp only [min_eq_left hs, ENNReal.toNNReal_coe] at h1
    rw [hmin] at hs
    simp only [min_eq_left hs, ENNReal.toNNReal_coe] at h1
    exact h1
  refine ⟨hrℓ, hmin, fun s hs => ?_⟩
  have htr := trOf_eq_of_eqOn hR hR' (min_le_right _ _) (hmin ▸ min_le_right _ _) hww s hs
  unfold pcPt
  rw [hrℓ, htr]

end InteractingSLE.Theorem14.SB.Nc
