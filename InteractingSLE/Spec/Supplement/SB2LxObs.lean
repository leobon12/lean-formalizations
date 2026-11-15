/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.SB2LxPt

/-!
# The launch observables of `StepOK` at a pair of launches

Packet PROVE-T14-SB2LIFT (round 12; item 3 of handoff §R11.3). **`launch_obs_of_fill`** proves, at corresponding
launches of the actual walk (stage `n₁`) and the relative walk (stage `n₂`), the conjunction required by
`SB2LtRun.StepOK` in the admissible case:

* the lifetimes are infinite together and zero together: the named input (L1), from the lifted pieces;
* right hits beyond the records occur together. For finite lifetimes this is `lHit_launch_corr`, from the named
  input `FillCorr` and the record invariants. For infinite lifetimes there are no hits beyond the records: at stop
  time `0` every point with a nonzero chart point is alive (`lAlive_of_stopTime_zero`);
* no left hits, the named input `NoLeftHit`, in both runs;
* the new records correspond after `max · p`: `lRecR_launch_corr`, with `p ≤ recR₁ ≤ lRecR₁`.

The record invariants of both runs come from `recInv_ptRec_run`, and `recR₂ = ι (max recR₁ p)` from the lockstep
correspondence `StCorr`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Filter Topology Metric
open scoped NNReal ENNReal
open QuantumZipper (H Hbar fwdMap IsForwardSol)

namespace InteractingSLE.Theorem14.SB.Lk

open Exist Exist.Staged Exist.StagedLaw LuM

variable {κ θ : ℝ} {b₁ b₂ : ℝ → ℝ} {J₁ J₂ : Finset ℝ}

/-- At stop time `0` every point with a nonzero chart point is alive. -/
theorem lAlive_of_stopTime_zero {c : Chart} {d : (ℝ≥0 → ℝ) × ℝ≥0∞} (hd0 : d.1 0 = 0) (hT : stopTime ⊤ d = 0)
    {z : ℂ} (hz : c.1 z ≠ 0) : lAlive c ⊤ d z := by
  have hW0 : stopDrv ⊤ d 0 = 0 := by simp [stopDrv, retOf, hd0]
  refine ⟨fun _ => c.1 z, ?_⟩
  rw [hT]
  refine ⟨continuousOn_const, fun t ht => ?_⟩
  have ht0 : t = 0 := le_antisymm ht.2 ht.1
  subst ht0
  refine ⟨hz, ?_⟩
  simp [hW0]

/-- No right hits beyond the record of a launch with an infinite lifetime. -/
theorem not_lHit_of_top {b : ℝ → ℝ} {J : Finset ℝ} {D : ℕ → (ℝ≥0 → ℝ) × ℝ≥0∞} {n : ℕ}
    (hd0 : (D n).1 0 = 0) (hT : (D n).2 = ⊤) (hok : RecInv κ b J θ D n) :
    ¬ ∃ x : ℝ, stRecR (ExplState.run κ b J (boundaryWalkSpec b J θ true) D n) < x ∧
      lHit (stChart (ExplState.run κ b J (boundaryWalkSpec b J θ true) D n)) ⊤ (D n) x := by
  rintro ⟨x, hx, -, hna⟩
  have hT0 : stopTime ⊤ (D n) = 0 := by simp [stopTime, hT]
  exact hna (lAlive_of_stopTime_zero hd0 hT0 (hok x hx).2.2.2)

/-- **The launch observables of `StepOK` at a pair of launches.** -/
theorem launch_obs_of_fill {D₁ D₂ : ℕ → (ℝ≥0 → ℝ) × ℝ≥0∞} {n₁ n₂ : ℕ} {R p : ℝ} {ι : ℝ → ℝ}
    (hι : RayCorr b₁ J₁ b₂ J₂ R ι) (hcont : ContinuousOn ι (Ici R))
    (hP₁ : RegLaunches κ b₁ J₁ (boundaryWalkSpec b₁ J₁ θ true) D₁)
    (hP₂ : RegLaunches κ b₂ J₂ (boundaryWalkSpec b₂ J₂ θ true) D₂) {c₁ c₂ : Chart} {θ₁ θ₂ : ℝ}
    (hl₁ : (ExplState.run κ b₁ J₁ (boundaryWalkSpec b₁ J₁ θ true) D₁ (n₁ + 1)).2.2.2.1 n₁ = some (c₁, θ₁))
    (hl₂ : (ExplState.run κ b₂ J₂ (boundaryWalkSpec b₂ J₂ θ true) D₂ (n₂ + 1)).2.2.2.1 n₂ = some (c₂, θ₂))
    (hok₁ : RecInv κ b₁ J₁ θ D₁ n₁) (hok₂ : RecInv κ b₂ J₂ θ D₂ n₂) (hRp : R ≤ p)
    (hp : p ≤ stRecR (ExplState.run κ b₁ J₁ (boundaryWalkSpec b₁ J₁ θ true) D₁ n₁))
    (hrecc : stRecR (ExplState.run κ b₂ J₂ (boundaryWalkSpec b₂ J₂ θ true) D₂ n₂) =
      ι (max (stRecR (ExplState.run κ b₁ J₁ (boundaryWalkSpec b₁ J₁ θ true) D₁ n₁)) p))
    (hL1 : ((D₂ n₂).2 = ⊤ ↔ (D₁ n₁).2 = ⊤) ∧ ((D₂ n₂).2 = 0 ↔ (D₁ n₁).2 = 0))
    (hF : (D₁ n₁).2 ≠ ⊤ → FillCorr κ θ b₁ J₁ D₁ n₁ b₂ J₂ D₂ n₂ ι)
    (hlh₁ : NoLeftHit κ b₁ J₁ θ D₁ n₁) (hlh₂ : NoLeftHit κ b₂ J₂ θ D₂ n₂) :
    ((D₂ n₂).2 = ⊤ ↔ (D₁ n₁).2 = ⊤) ∧ ((D₂ n₂).2 = 0 ↔ (D₁ n₁).2 = 0) ∧
      ((∃ x : ℝ, stRecR (ExplState.run κ b₂ J₂ (boundaryWalkSpec b₂ J₂ θ true) D₂ n₂) < x ∧
          lHit (stChart (ExplState.run κ b₂ J₂ (boundaryWalkSpec b₂ J₂ θ true) D₂ n₂)) ⊤ (D₂ n₂) x) ↔
        ∃ x : ℝ, stRecR (ExplState.run κ b₁ J₁ (boundaryWalkSpec b₁ J₁ θ true) D₁ n₁) < x ∧
          lHit (stChart (ExplState.run κ b₁ J₁ (boundaryWalkSpec b₁ J₁ θ true) D₁ n₁)) ⊤ (D₁ n₁) x) ∧
      (¬ ∃ x : ℝ, x < stRecL (ExplState.run κ b₁ J₁ (boundaryWalkSpec b₁ J₁ θ true) D₁ n₁) ∧
          lHit (stChart (ExplState.run κ b₁ J₁ (boundaryWalkSpec b₁ J₁ θ true) D₁ n₁)) ⊤ (D₁ n₁) x) ∧
      (¬ ∃ x : ℝ, x < stRecL (ExplState.run κ b₂ J₂ (boundaryWalkSpec b₂ J₂ θ true) D₂ n₂) ∧
          lHit (stChart (ExplState.run κ b₂ J₂ (boundaryWalkSpec b₂ J₂ θ true) D₂ n₂)) ⊤ (D₂ n₂) x) ∧
      ((D₁ n₁).2 ≠ ⊤ →
        lRecR (ExplState.run κ b₂ J₂ (boundaryWalkSpec b₂ J₂ θ true) D₂ n₂) ⊤ (D₂ n₂) =
          ι (max (lRecR (ExplState.run κ b₁ J₁ (boundaryWalkSpec b₁ J₁ θ true) D₁ n₁) ⊤ (D₁ n₁)) p)) := by
  have hlne₁ : (ExplState.run κ b₁ J₁ (boundaryWalkSpec b₁ J₁ θ true) D₁ (n₁ + 1)).2.2.2.1 n₁ ≠ none := by
    rw [hl₁]; simp
  have hlne₂ : (ExplState.run κ b₂ J₂ (boundaryWalkSpec b₂ J₂ θ true) D₂ (n₂ + 1)).2.2.2.1 n₂ ≠ none := by
    rw [hl₂]; simp
  have hPR₁ := pieceRegular_of_launch hP₁ hlne₁
  have hPR₂ := pieceRegular_of_launch hP₂ hlne₂
  have hR : R ≤ stRecR (ExplState.run κ b₁ J₁ (boundaryWalkSpec b₁ J₁ θ true) D₁ n₁) := hRp.trans hp
  have hrec : stRecR (ExplState.run κ b₂ J₂ (boundaryWalkSpec b₂ J₂ θ true) D₂ n₂) =
      ι (stRecR (ExplState.run κ b₁ J₁ (boundaryWalkSpec b₁ J₁ θ true) D₁ n₁)) := by
    rw [hrecc, max_eq_left hp]
  refine ⟨hL1.1, hL1.2, ?_, hlh₁ hlne₁, hlh₂ hlne₂, fun hfin₁ => ?_⟩
  · by_cases hT : (D₁ n₁).2 = ⊤
    · have hT₂ : (D₂ n₂).2 = ⊤ := hL1.1.2 hT
      exact ⟨fun h => absurd h (not_lHit_of_top hPR₂.1 hT₂ hok₂),
        fun h => absurd h (not_lHit_of_top hPR₁.1 hT hok₁)⟩
    · have hfin₂ : (D₂ n₂).2 ≠ ⊤ := fun h => hT (hL1.1.1 h)
      exact lHit_launch_corr hι hP₁ hP₂ hl₁ hl₂ hT hfin₂ hok₁ hok₂ hR hrec (hF hT)
  · have hfin₂ : (D₂ n₂).2 ≠ ⊤ := fun h => hfin₁ (hL1.1.1 h)
    have hcorr := lRecR_launch_corr hι hcont hP₁ hP₂ hl₁ hl₂ hfin₁ hfin₂ hok₁ hok₂ hR hrec (hF hfin₁)
    -- the actual new record is beyond the old one, hence beyond `p`
    obtain ⟨hmono, -⟩ := beyond_launch_step hP₁ hl₁ hfin₁ hok₁
    obtain ⟨-, he, -⟩ := eq_launch_of_launches (κ := κ) (b := b₁) (jumps := J₁) _ D₁ hl₁
    rw [Lx.instrTime_boundaryWalk_of_launch hl₁] at he
    have hmin : min (⊤ : ℝ≥0∞) (D₁ n₁).2 ≠ ⊤ := by rw [min_eq_right le_top]; exact hfin₁
    have hrec' := (launch_eq_of_ne_top (ExplState.run κ b₁ J₁ (boundaryWalkSpec b₁ J₁ θ true) D₁ n₁) n₁ (D₁ n₁)
      θ₁ ⊤ hmin).2.2.1
    rw [he, hrec'] at hmono
    rw [hcorr, max_eq_left (hp.trans hmono)]

end InteractingSLE.Theorem14.SB.Lk
