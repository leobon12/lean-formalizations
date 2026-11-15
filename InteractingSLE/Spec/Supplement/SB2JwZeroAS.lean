/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.SB2JwAS
import InteractingSLE.Spec.Supplement.SB2JwCorner

/-!
# SB2(2): the v4 rule's zero relative stage `0`, almost surely (round 17)

Packet PROVE-SB2-LIFTSET (round 17). **`sb2LowerStage0ZeroV4`**: almost surely, off a zero root, at a launch at
`relOff` whose shifted lifetime `L₀ − t_R` is `0` — a zero-lifetime start piece (`liftRel_zero_stage0`) or the corner
case (`liftRel_corner`) — the lift relation with any regular zero-lifetime relative piece from the root holds. This is
`StagesGeom4`'s last stage-`0` clause (the v4 rule makes the stage a zero event, so `EL 0 = zeroDrv` there).
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

/-- **The zero relative stage `0` of the v4 rule, almost surely.** -/
theorem sb2LowerStage0ZeroV4 (h12 : Exist.Theorem12Statement.{u}) (h13 : Exist.Theorem13Statement.{u})
    (h12₀ : Exist.Theorem12Statement.{0}) (h13₀ : Exist.Theorem13Statement.{0}) :
    Lf.SB2LowerSetting.{u} fun κ b jumps _ _ _ P _ E u l k ω₀ c _ _ _ =>
      ∀ᵐ ω ∂(condExpKernel P (pastSigma κ b jumps (upperSpec u l) (E (upperSpec u l)) k) ω₀),
        ∀ β₀ : ℝ≥0 → ℂ, IsProperCurve β₀ → β₀ 0 = 0 → range β₀ = lowerWalkSet κ b jumps E ω →
          ∀ (tL : ℝ≥0) (γ : ℝ≥0 → ℂ) (m : ℝ), IsTailLiftCurve c (lR κ b jumps E u l k ω₀) m β₀ tL γ →
            ¬ ZeroRoot κ (-(Real.pi / 2)) b jumps (lR κ b jumps E u l k ω₀) (lD₁ b jumps E ω) →
            (wRun κ (-(Real.pi / 2)) b jumps (lD₁ b jumps E ω)
              (relOff κ (-(Real.pi / 2)) b jumps (lR κ b jumps E u l k ω₀) (lD₁ b jumps E ω) + 1)).2.2.2.1
                (relOff κ (-(Real.pi / 2)) b jumps (lR κ b jumps E u l k ω₀) (lD₁ b jumps E ω)) ≠ none →
            (lD₁ b jumps E ω (relOff κ (-(Real.pi / 2)) b jumps (lR κ b jumps E u l k ω₀) (lD₁ b jumps E ω))).2 -
                shiftD κ (-(Real.pi / 2)) b jumps (lR κ b jumps E u l k ω₀) (lD₁ b jumps E ω) 0 = 0 →
            ∀ e₂ : Drv, IsRegularDriver e₂ → e₂.2 = 0 →
              LiftRel β₀ tL γ
                (newPc (wRun κ (-(Real.pi / 2)) b jumps (lD₁ b jumps E ω)
                    (relOff κ (-(Real.pi / 2)) b jumps (lR κ b jumps E u l k ω₀) (lD₁ b jumps E ω)))
                  (lD₁ b jumps E ω (relOff κ (-(Real.pi / 2)) b jumps (lR κ b jumps E u l k ω₀) (lD₁ b jumps E ω))))
                (newPc (ExplState.init 0) e₂) := by
  have hW := sb2LowerChainStatement_of_thm12_thm13 h12 h13 h12₀ h13₀
  intro κ hκ hκ4 b jumps hb Ω _ _ P _ h hh W' ζ' hcf hζ' E hE hER u l k hu hlp hlθ hL hleft
  have hsp : IsBoundaryContinuedProgram (upperSpec u l).2.2 := isBoundaryContinuedProgram_upperSpec hlθ
  have hm𝒢 := (hE _ hsp).2.1 k
  have hRLQ := KernelTower.ae_ae_condExpKernel_of_ae hm𝒢
    (GW1W.regLaunches_of_stagedPiecesRegular (hER _ (GW1X.isBoundaryContinuedProgram_walkR b jumps)))
  filter_upwards [hW κ hκ hκ4 b jumps hb P h hh W' ζ' hcf hζ' E hE hER u l k hu hlp hlθ hL hleft,
    sb2LowerWalkInputs h13₀ κ hκ hκ4 b jumps hb P h hh W' ζ' hcf hζ' E hE hER u l k hu hlp hlθ hL hleft,
    hRLQ] with ω₀ hW₀ hI₀ hR₀
  intro c θ hlaunch b' J' h' hb' hT' hG'
  filter_upwards [hW₀ c θ hlaunch b' J' h' hb' hT' hG', hI₀ c θ hlaunch b' J' h' hb' hT' hG', hR₀]
    with ω hWω hIω hRω
  intro β₀ hβ hβ0 hβr tL γ m hγ hZ hl hL0 e₂ hreg he₂
  have hRmem : ((lR κ b jumps E u l k ω₀ : ℝ) : ℂ) ∈ ExplState.physSet κ b jumps
      (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) (lD₁ b jumps E ω) := by
    rw [← hγ.1]; exact (hβr ▸ mem_range_self tL : β₀ tL ∈ lowerWalkSet κ b jumps E ω)
  by_cases h0 : (lD₁ b jumps E ω
      (relOff κ (-(Real.pi / 2)) b jumps (lR κ b jumps E u l k ω₀) (lD₁ b jumps E ω))).2 = 0
  · exact liftRel_zero_stage0 hRω hWω (fun n hn hl' => (hIω n).2.2 hn hl') hRmem hZ hl h0 hβ hγ.1 hγ.2.2.1 hreg
      he₂
  · rw [shiftD_zero] at hL0
    exact liftRel_corner hRω hWω hl h0 hβ hβ0 hβr hγ.1 (mem_succ_of_not_zeroRoot hRmem hZ) hL0 hγ.2.2.1 hreg he₂

end InteractingSLE.Theorem14.SB.Lk
