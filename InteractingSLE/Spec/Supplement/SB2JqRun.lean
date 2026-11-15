/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.SB2JqArc
import InteractingSLE.Spec.Supplement.GW1WalkExitStatement

/-!
# SB2(2): the actual walk's fields of the run inputs (option-independent part of D6)

Packet PROVE-SB2-LIFTSET (round 15). The data clause's `RunInputs' … o N` has actual-walk fields `fin₁`, `done`,
`len₁`, `two_le` and the actual half of `len`. With `N + o` the first finished stage of the actual walk they hold as
soon as the walk is not finished at `o + 1`:

* **`sb2LowerCompletion`**: almost surely under the retained kernel the lower walk is finished at the end of its
  program (GW1's completion from Theorem 1.3 at universe `0`, through the regularised family);
* `first_done_le_length`, **`actualRunFields`**: for the first finished stage `M` and `o + 1 < M` (the walk not finished
  at `o + 1`), `N = M − o` has `2 ≤ N`, `N + o ≤ length`, the walk finished at `N + o`, finite lifetimes at the launches
  `j` with `j + 1 < N + o`, and `i + o < length` for `i < N`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal
open QuantumZipper (chiC H Hbar)
open LQGMetric (DistOn)

universe u

namespace InteractingSLE.Theorem14.SB.Lk

open Supp9B Lx Lu Leaf FlowDilate Sec4 Exist Exist.Staged Exist.StagedLaw LuM GW1W GW1Bookkeep GW1P

/-- **The lower walk finishes, almost surely under the retained kernel** (Theorem 1.3 at universe `0`). -/
theorem sb2LowerCompletion (h13₀ : Exist.Theorem13Statement.{0}) :
    Lf.SB2LowerSetting.{u} fun κ b jumps _ _ _ P _ E u l k ω₀ _ _ _ _ =>
      ∀ᵐ ω ∂(condExpKernel P (pastSigma κ b jumps (Lu.upperSpec u l) (E (Lu.upperSpec u l)) k) ω₀),
        stStatus (ExplState.run κ b jumps (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)
          (fun j => E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) j ω)
          (boundaryWalkSpec b jumps (-(Real.pi / 2)) true).2.2.length) = stDone := by
  intro κ hκ hκ4 b jumps hb Ω _ _ P _ h hh W' ζ' hcf hζ' E hE hER u l k hu hlp hlθ hL hleft
  have hlwp : IsBoundaryContinuedProgram (boundaryWalkSpec b jumps (-(Real.pi / 2)) true).2.2 :=
    isBoundaryContinuedProgram_boundaryWalkSpec b jumps ⟨le_rfl, by linarith [Real.pi_pos]⟩ true
  obtain ⟨hE', hreg', hrun⟩ := StagedReg.regFam_spec hb hE hER
  have hS := GW1WalkExit.walkCompletionStatement_of_theorem13 h13₀ κ hκ hκ4 b jumps hb P h hh W' ζ' hcf hζ' _
    hE' hreg' true
  have hP : ∀ᵐ ω ∂P, stStatus (ExplState.run κ b jumps (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)
      (fun j => E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) j ω)
      (boundaryWalkSpec b jumps (-(Real.pi / 2)) true).2.2.length) = stDone := by
    filter_upwards [hS, hrun _ hlwp] with ω hω hr
    rw [← hr]
    exact hω
  have hsp : IsBoundaryContinuedProgram (Lu.upperSpec u l).2.2 := Lu.isBoundaryContinuedProgram_upperSpec hlθ
  have hm𝒢 := (hE _ hsp).2.1 k
  filter_upwards [KernelTower.ae_ae_condExpKernel_of_ae hm𝒢 hP] with ω₀ hω₀
  intro c θ hlaunch b' J' h' hb' hT' hG'
  exact hω₀

variable {κ θ : ℝ} {b : ℝ → ℝ} {jumps : Finset ℝ} {D : ℕ → Drv}

/-- **The actual walk's fields of the run inputs** at offset `o`, with `N + o` the first finished stage. -/
theorem actualRunFields
    (hdone : stStatus (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) D
      (boundaryWalkSpec b jumps θ true).2.2.length) = stDone) {o : ℕ}
    (hnd : stStatus (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) D (o + 1)) ≠ stDone) :
    ∃ N : ℕ, 2 ≤ N ∧ N + o ≤ (boundaryWalkSpec b jumps θ true).2.2.length ∧
      stStatus (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) D (N + o)) = stDone ∧
      (∀ j, j + 1 < N + o →
        (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) D (j + 1)).2.2.2.1 j ≠ none → (D j).2 ≠ ⊤) ∧
      ∀ i, i < N → i + o < (boundaryWalkSpec b jumps θ true).2.2.length := by
  obtain ⟨M, hM, hmin⟩ := exists_first_done (κ := κ) (b := b) (jumps := jumps) (θ := θ) (D := D) ⟨_, hdone⟩
  have hML : M ≤ (boundaryWalkSpec b jumps θ true).2.2.length := by
    by_contra h
    push Not at h
    exact hmin _ h hdone
  have hoM : o + 1 < M := by
    by_contra h
    push Not at h
    exact hnd (by rw [stay_of_done hM (o + 1) h]; exact hM)
  refine ⟨M - o, by omega, by omega, by rw [show M - o + o = M by omega]; exact hM, fun j hj hl => ?_,
    fun i hi => by omega⟩
  exact fin_before_first_done hmin j (by omega) hl

end InteractingSLE.Theorem14.SB.Lk
