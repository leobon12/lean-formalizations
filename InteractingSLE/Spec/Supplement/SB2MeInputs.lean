/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.SB2MdLift
import InteractingSLE.Spec.Supplement.SB2LpLift

/-!
# The record invariants before done, the actual walk's inputs, and the final form of `FillCorr`

Packet PROVE-T14-SB2LIFT (round 19; the inputs of `fillCorr_of_stage`, handoff §R18.2).

* `done_of_le`: done is absorbing along the run;
* **`recInv_of_not_done`**: if the walk is not done at stage `N`, the record invariant `RecInv` holds at every stage up
  to `N`, from no left moves and no left hits alone. Launched lifetimes before `N` are finite (`fin_of_not_done`), and
  PROVE-SB2-LIFTSET's bounded `recInv_ptRec_run_le` applies;
* **`sb2LowerActualInputs`**: almost surely under the retained kernel of every retained launch (SB2(2)'s setting), the
  actual lower walk has regular launches, GW1's per-step facts, no left moves, no left hits, and no zero lifetime at a
  later launch (rounds 15 and 18, Theorems 1.2–1.3);
* `eq_liftImage_of_closure`: a relative set that is the closure of the intrinsic lift of an actual set is its lift image
  (LIFTSET's `liftImage_eq_closure`). This is the form in which the per-time trace lift of `fillCorr_of_stage` comes
  from the construction of `EL`;
* **`fillCorr_of_stage'`**: `fillCorr_of_stage` with the record invariants of both walks discharged by
  `recInv_of_not_done` and the visit to `R` by prefix monotonicity from any earlier stage.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped NNReal ENNReal
open QuantumZipper (H Hbar)

universe u

namespace InteractingSLE.Theorem14.SB.Lk

open Exist Exist.Staged Exist.StagedLaw LuM GW1W

variable {κ θ : ℝ}

/-- Done is absorbing along the run. -/
theorem done_of_le {b : ℝ → ℝ} {J : Finset ℝ} {D : ℕ → (ℝ≥0 → ℝ) × ℝ≥0∞} {i N : ℕ}
    (h : stStatus (ExplState.run κ b J (boundaryWalkSpec b J θ true) D i) = stDone) (hiN : i ≤ N) :
    stStatus (ExplState.run κ b J (boundaryWalkSpec b J θ true) D N) = stDone := by
  induction N, hiN using Nat.le_induction with
  | base => exact h
  | succ k _ ih =>
    rw [GW1WalkFinish.done_run_succ _ D ih]
    exact ih

/-- **The record invariant at every stage up to a stage where the walk is not done**, from no left moves and no left
hits. -/
theorem recInv_of_not_done {b : ℝ → ℝ} {J : Finset ℝ} {D : ℕ → (ℝ≥0 → ℝ) × ℝ≥0∞}
    (hP : RegLaunches κ b J (boundaryWalkSpec b J θ true) D) (hlm : ∀ j, NoLeftMove κ b J θ D j)
    (hlh : ∀ j, NoLeftHit κ b J θ D j) {N : ℕ}
    (hnd : stStatus (ExplState.run κ b J (boundaryWalkSpec b J θ true) D N) ≠ stDone) :
    ∀ k, k ≤ N → RecInv κ b J θ D k := by
  have hnd' : ∀ i, i ≤ N → stStatus (ExplState.run κ b J (boundaryWalkSpec b J θ true) D i) ≠ stDone :=
    fun i hi hd => hnd (done_of_le hd hi)
  have hfin : ∀ j, j < N → (ExplState.run κ b J (boundaryWalkSpec b J θ true) D (j + 1)).2.2.2.1 j ≠ none →
      (D j).2 ≠ ⊤ := fun j hj hl => fin_of_not_done (hnd' (j + 1) hj) hl
  exact fun k hk => (recInv_ptRec_run_le hP hfin hlm hlh k hk).1

/-- **The actual lower walk's inputs, almost surely under the retained kernel** (SB2(2)'s setting; Theorems 1.2–1.3):
regular launches, GW1's per-step facts, and at every step no left move, no left hit and no zero lifetime at a later
launch. -/
theorem sb2LowerActualInputs (h12 : Exist.Theorem12Statement.{u}) (h13 : Exist.Theorem13Statement.{u})
    (h12₀ : Exist.Theorem12Statement.{0}) (h13₀ : Exist.Theorem13Statement.{0}) :
    Lf.SB2LowerSetting.{u} fun κ b jumps _ _ _ P _ E u l k ω₀ _ _ _ _ =>
      ∀ᵐ ω ∂(condExpKernel P (pastSigma κ b jumps (Lu.upperSpec u l) (E (Lu.upperSpec u l)) k) ω₀),
        RegLaunches κ b jumps (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)
          (fun j => E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) j ω) ∧
        WalkChainFacts κ b jumps (-(Real.pi / 2)) (fun j => E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) j ω) ∧
        ∀ n,
          NoLeftMove κ b jumps (-(Real.pi / 2)) (fun j => E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) j ω) n ∧
          NoLeftHit κ b jumps (-(Real.pi / 2)) (fun j => E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) j ω) n ∧
          (0 < n → (ExplState.run κ b jumps (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)
              (fun j => E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) j ω) (n + 1)).2.2.2.1 n ≠ none →
            (E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) n ω).2 ≠ 0) := by
  intro κ hκ hκ4 b jumps hb Ω _ _ P _ h hh W' ζ' hcf hζ' E hE hER u l k hu hlp hlθ hL hleft
  filter_upwards [sb2LowerWalkInputs h13₀ κ hκ hκ4 b jumps hb P h hh W' ζ' hcf hζ' E hE hER u l k hu hlp hlθ hL hleft,
    sb2LowerWalkSegInputs h12 h13 h12₀ h13₀ κ hκ hκ4 b jumps hb P h hh W' ζ' hcf hζ' E hE hER u l k hu hlp hlθ hL
      hleft] with ω₀ h1 h2
  intro c θ hlaunch b' J' h' hb' hT' hG'
  filter_upwards [h1 c θ hlaunch b' J' h' hb' hT' hG', h2 c θ hlaunch b' J' h' hb' hT' hG'] with ω hω1 hω2
  exact ⟨hω2.2, hω2.1, hω1⟩

/-- **A relative set that is the closure of the intrinsic lift of an actual set on the tail is its lift image**
(LIFTSET's `liftImage_eq_closure`; the form of the per-time trace lift of `fillCorr_of_stage`). -/
theorem eq_liftImage_of_closure {c : Chart} {R m : ℝ} {β₀ γ : ℝ≥0 → ℂ} {tL : ℝ≥0}
    (hγ : IsTailLiftCurve c R m β₀ tL γ) (hcH : ContinuousOn c.2.1 H) (hc1 : ∀ w ∈ H, c.1 (c.2.1 w) = w)
    (hoff : BdryOff c) {S₁ S₂ : Set ℂ} (hTc : IsCompact {s | β₀ (tL + s) ∈ S₁})
    (hdense : {s | β₀ (tL + s) ∈ S₁} ⊆ closure {s | β₀ (tL + s) ∈ S₁ ∩ c.2.1 '' H})
    (hS : S₂ = closure (liftPt c m '' (S₁ ∩ c.2.1 '' H ∩ β₀ '' Ici tL))) : S₂ = liftImage β₀ tL γ S₁ := by
  rw [hS, liftImage_eq_closure hγ hcH hc1 hoff hTc hdense]

variable {b₁ b₂ : ℝ → ℝ} {J₁ J₂ : Finset ℝ} {β₀ γ : ℝ≥0 → ℂ} {tL : ℝ≥0} {R : ℝ} {ι : ℝ → ℝ}

/-- **`FillCorr` at a pair of corresponding launches, final form**: `fillCorr_of_stage` with the record invariants of
both walks from no left moves and no left hits, and the visit to `R` from any earlier stage. -/
theorem fillCorr_of_stage' {D₁ D₂ : ℕ → (ℝ≥0 → ℝ) × ℝ≥0∞} {n₁ n₂ k₀ : ℕ} {c₁ c₂ : Chart} {θ₁ θ₂ : ℝ}
    (hι : RayCorr b₁ J₁ b₂ J₂ R ι) (hβ : Supp9B.IsProperCurve β₀) (hD : LiftCurveData β₀ γ tL R ι)
    (hβr : range β₀ = ExplState.physSet κ b₁ J₁ (boundaryWalkSpec b₁ J₁ θ true) D₁) (hβ0 : β₀ 0 = 0)
    (hRa : R ≤ stRecR (ExplState.run κ b₁ J₁ (boundaryWalkSpec b₁ J₁ θ true) D₁ n₁))
    (hrecc : stRecR (ExplState.run κ b₂ J₂ (boundaryWalkSpec b₂ J₂ θ true) D₂ n₂) =
      ι (stRecR (ExplState.run κ b₁ J₁ (boundaryWalkSpec b₁ J₁ θ true) D₁ n₁)))
    (hP₁ : RegLaunches κ b₁ J₁ (boundaryWalkSpec b₁ J₁ θ true) D₁) (hW₁ : WalkChainFacts κ b₁ J₁ θ D₁)
    (hlm₁ : ∀ k, NoLeftMove κ b₁ J₁ θ D₁ k) (hlh₁ : ∀ k, NoLeftHit κ b₁ J₁ θ D₁ k)
    (hl₁ : (ExplState.run κ b₁ J₁ (boundaryWalkSpec b₁ J₁ θ true) D₁ (n₁ + 1)).2.2.2.1 n₁ = some (c₁, θ₁))
    (hfin₁ : (D₁ n₁).2 ≠ ⊤) (hn₁ : n₁ + 1 ≤ (boundaryWalkSpec b₁ J₁ θ true).2.2.length)
    (hL : β₀ tL ∈ SB.prefixPhysSet κ b₁ J₁ (boundaryWalkSpec b₁ J₁ θ true) D₁ k₀) (hk₀ : k₀ ≤ n₁)
    (hP₂ : RegLaunches κ b₂ J₂ (boundaryWalkSpec b₂ J₂ θ true) D₂)
    (hlm₂ : ∀ k, NoLeftMove κ b₂ J₂ θ D₂ k) (hlh₂ : ∀ k, NoLeftHit κ b₂ J₂ θ D₂ k)
    (hl₂ : (ExplState.run κ b₂ J₂ (boundaryWalkSpec b₂ J₂ θ true) D₂ (n₂ + 1)).2.2.2.1 n₂ = some (c₂, θ₂))
    (hfin₂ : (D₂ n₂).2 ≠ ⊤)
    (hstage : SB.prefixPhysSet κ b₂ J₂ (boundaryWalkSpec b₂ J₂ θ true) D₂ n₂ =
      liftImage β₀ tL γ (SB.prefixPhysSet κ b₁ J₁ (boundaryWalkSpec b₁ J₁ θ true) D₁ n₁))
    (hpc : LiftRel β₀ tL γ (newPc (ExplState.run κ b₁ J₁ (boundaryWalkSpec b₁ J₁ θ true) D₁ n₁) (D₁ n₁))
      (newPc (ExplState.run κ b₂ J₂ (boundaryWalkSpec b₂ J₂ θ true) D₂ n₂) (D₂ n₂)))
    (htr₁ : ∀ r : ℝ, 0 ≤ r → r < stopTime ⊤ (D₁ n₁) → ∃ r' : ℝ, 0 ≤ r' ∧ r' < stopTime ⊤ (D₂ n₂) ∧
      bdVal (stChart (ExplState.run κ b₂ J₂ (boundaryWalkSpec b₂ J₂ θ true) D₂ n₂)) ''
          (trOf (D₂ n₂) '' Icc 0 r'.toNNReal) =
        liftImage β₀ tL γ (bdVal (stChart (ExplState.run κ b₁ J₁ (boundaryWalkSpec b₁ J₁ θ true) D₁ n₁)) ''
          (trOf (D₁ n₁) '' Icc 0 r.toNNReal)))
    (htr₂ : ∀ r' : ℝ, 0 ≤ r' → r' < stopTime ⊤ (D₂ n₂) → ∃ r : ℝ, 0 ≤ r ∧ r < stopTime ⊤ (D₁ n₁) ∧
      bdVal (stChart (ExplState.run κ b₂ J₂ (boundaryWalkSpec b₂ J₂ θ true) D₂ n₂)) ''
          (trOf (D₂ n₂) '' Icc 0 r'.toNNReal) =
        liftImage β₀ tL γ (bdVal (stChart (ExplState.run κ b₁ J₁ (boundaryWalkSpec b₁ J₁ θ true) D₁ n₁)) ''
          (trOf (D₁ n₁) '' Icc 0 r.toNNReal))) :
    FillCorr κ θ b₁ J₁ D₁ n₁ b₂ J₂ D₂ n₂ ι :=
  fillCorr_of_stage hι hβ hD hβr hβ0 hRa hrecc hP₁ hW₁ hl₁ hfin₁
    (recInv_of_not_done hP₁ hlm₁ hlh₁ (WalkIntRunChron.not_done_of_launch _ D₁ hl₁)) hlm₁ hn₁
    (WalkIntRunChron.prefixPhysSet_mono _ D₁ hk₀ hL) hP₂ hl₂ hfin₂
    (recInv_of_not_done hP₂ hlm₂ hlh₂ (WalkIntRunChron.not_done_of_launch _ D₂ hl₂)) hlm₂ hstage hpc htr₁ htr₂

end InteractingSLE.Theorem14.SB.Lk
