/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.SB2MeInputs

/-!
# No left moves of the relative walk along the lockstep

Packet PROVE-T14-SB2LIFT (round 19; the relative walk's `NoLeftMove`, `RunInputs.lm₂`, handoff §R18.2 2). A left move
appends a connector, so steps that keep the connectors (flow steps, steps past the program) never move left. A
connector step from an allowed status moves right, ends or keeps the state (`allowedSt_cont`, round 14). Allowed
statuses pass from the actual walk to the relative one through the state correspondence `StCorr`, since the ray
correspondence carries right limits (`RayCorr.rightLim_eq`). Hence:

* `arcs_length_moveAlong`, **`noLeftMove_of_arcs_eq`**: no left move at a step that keeps the connectors;
* `arcs_run_succ_flow`: flow steps keep the connectors;
* **`allowedSt_corr`**: an allowed actual state gives an allowed relative state under `StCorr`;
* **`noLeftMove_rel_of_stCorr`**: at every relative stage where the states correspond (with an allowed actual state),
  the relative walk does not move left;
* **`sb2LowerAllowed`**: almost surely under the retained kernel of every retained launch, the actual lower walk is in
  an allowed state at every stage `≥ 1` (GW1's stage data, `allowedSt_run`, through the regularized family).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped NNReal ENNReal

universe u

namespace InteractingSLE.Theorem14.SB.Lk

open Exist Exist.Staged Exist.StagedLaw LuM GW1W GW1WalkExit GW1WalkFinish
open PiecewiseConstantBoundaryData (rightLim leftLim jumpSet)

variable {κ θ : ℝ}

/-- A move appends one connector. -/
theorem arcs_length_moveAlong (s : ExplState) (r : Bool) (w : ℝ) (m : Bool) :
    (ExplState.moveAlong s r w m).2.1.length = s.2.1.length + 1 := by
  obtain ⟨pieces, arcs, ret, lau, chart, status, pt, angle, recR, recL⟩ := s
  cases r <;> simp [ExplState.moveAlong]

/-- **No left move at a step that keeps the connectors.** -/
theorem noLeftMove_of_arcs_eq {b : ℝ → ℝ} {J : Finset ℝ} {D : ℕ → (ℝ≥0 → ℝ) × ℝ≥0∞} {n : ℕ}
    (h : (ExplState.run κ b J (boundaryWalkSpec b J θ true) D (n + 1)).2.1 =
      (ExplState.run κ b J (boundaryWalkSpec b J θ true) D n).2.1) : NoLeftMove κ b J θ D n := by
  intro w m he
  have hl := congrArg (fun s : ExplState => s.2.1.length) he
  simp only [arcs_length_moveAlong] at hl
  rw [h] at hl
  omega

/-- Flow steps and steps past the program keep the connectors. -/
theorem arcs_run_succ_flow {b : ℝ → ℝ} {J : Finset ℝ} {D : ℕ → (ℝ≥0 → ℝ) × ℝ≥0∞} {n : ℕ}
    (hn : ¬ (n < (boundaryWalkSpec b J θ true).2.2.length ∧ n % 2 = 1)) :
    (ExplState.run κ b J (boundaryWalkSpec b J θ true) D (n + 1)).2.1 =
      (ExplState.run κ b J (boundaryWalkSpec b J θ true) D n).2.1 := by
  set s := ExplState.run κ b J (boundaryWalkSpec b J θ true) D n with hsdef
  by_cases hk : n < (boundaryWalkSpec b J θ true).2.2.length
  · have hev : n % 2 = 0 := by
      rcases Nat.mod_two_eq_zero_or_one n with h | h
      · exact h
      · exact absurd ⟨hk, h⟩ hn
    have hstep := GW1W.run_succ_walk_flow (κ := κ) (b := b) (jumps := J) (θ := θ) (right := true) (D := D) hk hev
    rw [hstep]
    rcases flowStep_trichotomy (κ := κ) (b := b) false s n (D n) θ ⊤ with e | e | e
    · rw [e]
    · rw [e, arcs_setDead]
    · rw [e, Lx.arcs_launch']
  · have e : ExplState.run κ b J (boundaryWalkSpec b J θ true) D (n + 1) = s := by
      rw [run_succ]
      have : (boundaryWalkSpec b J θ true).2.2[n]? = none := List.getElem?_eq_none (not_lt.1 hk)
      rw [this]
    rw [e]

variable {b₁ b₂ : ℝ → ℝ} {J₁ J₂ : Finset ℝ} {R p : ℝ} {ι : ℝ → ℝ}

/-- **An allowed actual state gives an allowed relative state** under the state correspondence (at a threshold
without a hit the actual point is at least `p`). -/
theorem allowedSt_corr (hι : RayCorr b₁ J₁ b₂ J₂ R ι) (hRp : R ≤ p) {s₁ s₂ : ExplState} (hc : StCorr ι p s₁ s₂)
    (hA : AllowedSt κ b₁ s₁) (hp : stStatus s₁ = stThr none → p ≤ stPt s₁) : AllowedSt κ b₂ s₂ := by
  obtain ⟨hpt, hst, hθ, -⟩ := hc
  rcases hA with h | h | h | h | ⟨h, hlow⟩
  · exact Or.inl (hst.trans h)
  · exact Or.inr (Or.inl (hst.trans h))
  · exact Or.inr (Or.inr (Or.inl (hst.trans h)))
  · exact Or.inr (Or.inr (Or.inr (Or.inl (hst.trans h))))
  · refine Or.inr (Or.inr (Or.inr (Or.inr ⟨hst.trans h, ?_⟩)))
    have hpp := hp h
    simp only [↓reduceIte] at hlow ⊢
    rw [hpt, max_eq_left hpp, hι.rightLim_eq _ (hRp.trans hpp), hθ]
    exact hlow

/-- **The relative walk does not move left at a stage where the states correspond.** -/
theorem noLeftMove_rel_of_stCorr {D₁ D₂ : ℕ → (ℝ≥0 → ℝ) × ℝ≥0∞} {k i : ℕ} (hι : RayCorr b₁ J₁ b₂ J₂ R ι)
    (hRp : R ≤ p)
    (hc : StCorr ι p (ExplState.run κ b₁ J₁ (boundaryWalkSpec b₁ J₁ θ true) D₁ k)
      (ExplState.run κ b₂ J₂ (boundaryWalkSpec b₂ J₂ θ true) D₂ i))
    (hA : AllowedSt κ b₁ (ExplState.run κ b₁ J₁ (boundaryWalkSpec b₁ J₁ θ true) D₁ k))
    (hp : stStatus (ExplState.run κ b₁ J₁ (boundaryWalkSpec b₁ J₁ θ true) D₁ k) = stThr none →
      p ≤ stPt (ExplState.run κ b₁ J₁ (boundaryWalkSpec b₁ J₁ θ true) D₁ k)) :
    NoLeftMove κ b₂ J₂ θ D₂ i := by
  by_cases hcont : i < (boundaryWalkSpec b₂ J₂ θ true).2.2.length ∧ i % 2 = 1
  · exact (allowedSt_cont hcont.1 hcont.2 (allowedSt_corr hι hRp hc hA hp)).2
  · exact noLeftMove_of_arcs_eq (arcs_run_succ_flow hcont)

/-- **The actual lower walk is almost surely in an allowed state at every stage `≥ 1`** under the retained kernel of
every retained launch (SB2(2)'s setting; Theorem 1.3 at universe `0`). -/
theorem sb2LowerAllowed (h13₀ : Exist.Theorem13Statement.{0}) :
    Lf.SB2LowerSetting.{u} fun κ b jumps _ _ _ P _ E u l k ω₀ _ _ _ _ =>
      ∀ᵐ ω ∂(condExpKernel P (pastSigma κ b jumps (Lu.upperSpec u l) (E (Lu.upperSpec u l)) k) ω₀), ∀ n, 1 ≤ n →
        AllowedSt κ b (ExplState.run κ b jumps (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)
          (fun j => E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) j ω) n) := by
  intro κ hκ hκ4 b jumps hb Ω _ _ P _ h hh W' ζ' hcf hζ' E hE hER u l k hu hlp hlθ hL hleft
  have hlwp : IsBoundaryContinuedProgram (boundaryWalkSpec b jumps (-(Real.pi / 2)) true).2.2 :=
    isBoundaryContinuedProgram_boundaryWalkSpec b jumps ⟨le_rfl, by linarith [Real.pi_pos]⟩ true
  obtain ⟨hE', hreg', hrun⟩ := StagedReg.regFam_spec hb hE hER
  have hS := walkStageData_of_theorem13 h13₀ κ hκ hκ4 b jumps hb P h hh W' ζ' hcf hζ' _ hE' hreg' true
  have hP : ∀ᵐ ω ∂P, ∀ n, 1 ≤ n →
      AllowedSt κ b (ExplState.run κ b jumps (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)
        (fun j => E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) j ω) n) := by
    filter_upwards [hS, hrun _ hlwp] with ω hω hr n hn
    rw [← hr n]
    exact (allowedSt_run hω n).1 hn
  have hsp : IsBoundaryContinuedProgram (Lu.upperSpec u l).2.2 := Lu.isBoundaryContinuedProgram_upperSpec hlθ
  have hm𝒢 := (hE _ hsp).2.1 k
  filter_upwards [KernelTower.ae_ae_condExpKernel_of_ae hm𝒢 hP] with ω₀ hω₀
  intro c θ hlaunch b' J' h' hb' hT' hG'
  exact hω₀

end InteractingSLE.Theorem14.SB.Lk
