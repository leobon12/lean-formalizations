/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.SB2JwZero
import InteractingSLE.Spec.Supplement.SBS3LtDensity

/-!
# SB2(2): the relative stage `0`'s actual side, almost surely (D6 v3, items 1–2)

Packet PROVE-SB2-LIFTSET (round 17). Almost surely under the retained kernel, for every parametrization `β₀` of the
lower walk and every visit time `t_L` of `R`, off a zero root and at a launch at `relOff`:

* **`sb2LowerStage0Act`**: when the shifted lifetime `L₀ − t_R` is nonzero, the shifted start piece's actual-piece
  fields (`Stage0Act`) hold (Theorems 1.2–1.3, Lemma S2's tail clause, CORNER's S3 tail form in `ℍ`);
* **`sb2LowerStage0Zero`**: when the start piece has lifetime `0`, the lift relation with any regular zero-lifetime
  relative piece from the root holds (Theorems 1.2–1.3 at universe `0` for GW1's chain facts and positivity).
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

/-- The stage-`0` shift is the start piece's visit time of `R`. -/
theorem shiftD_zero (κ θ : ℝ) (b₁ : ℝ → ℝ) (J₁ : Finset ℝ) (R : ℝ) (D₁ : ℕ → Drv) :
    shiftD κ θ b₁ J₁ R D₁ 0 =
      visitTime (wRun κ θ b₁ J₁ D₁ (relOff κ θ b₁ J₁ R D₁)) (D₁ (relOff κ θ b₁ J₁ R D₁)) R :=
  if_pos rfl

/-- **The shifted start piece's actual-piece fields, almost surely** (off a zero root, at a launch at `relOff` of
positive shifted lifetime). -/
theorem sb2LowerStage0Act (h12 : Exist.Theorem12Statement.{u}) (h13 : Exist.Theorem13Statement.{u})
    (h12₀ : Exist.Theorem12Statement.{0}) (h13₀ : Exist.Theorem13Statement.{0}) :
    Lf.SB2LowerSetting.{u} fun κ b jumps _ _ _ P _ E u l k ω₀ c _ _ _ =>
      ∀ᵐ ω ∂(condExpKernel P (pastSigma κ b jumps (upperSpec u l) (E (upperSpec u l)) k) ω₀),
        ∀ β₀ : ℝ≥0 → ℂ, IsProperCurve β₀ → β₀ 0 = 0 → range β₀ = lowerWalkSet κ b jumps E ω →
          ∀ tL : ℝ≥0, β₀ tL = lR κ b jumps E u l k ω₀ → ∀ m : ℝ,
            ¬ ZeroRoot κ (-(Real.pi / 2)) b jumps (lR κ b jumps E u l k ω₀) (lD₁ b jumps E ω) →
            (wRun κ (-(Real.pi / 2)) b jumps (lD₁ b jumps E ω)
              (relOff κ (-(Real.pi / 2)) b jumps (lR κ b jumps E u l k ω₀) (lD₁ b jumps E ω) + 1)).2.2.2.1
                (relOff κ (-(Real.pi / 2)) b jumps (lR κ b jumps E u l k ω₀) (lD₁ b jumps E ω)) ≠ none →
            (lD₁ b jumps E ω (relOff κ (-(Real.pi / 2)) b jumps (lR κ b jumps E u l k ω₀) (lD₁ b jumps E ω))).2 ≠ 0 →
            (lD₁ b jumps E ω (relOff κ (-(Real.pi / 2)) b jumps (lR κ b jumps E u l k ω₀) (lD₁ b jumps E ω))).2 -
                shiftD κ (-(Real.pi / 2)) b jumps (lR κ b jumps E u l k ω₀) (lD₁ b jumps E ω) 0 ≠ 0 →
            Stage0Act c m β₀ tL
              (wRun κ (-(Real.pi / 2)) b jumps (lD₁ b jumps E ω)
                (relOff κ (-(Real.pi / 2)) b jumps (lR κ b jumps E u l k ω₀) (lD₁ b jumps E ω)))
              (lD₁ b jumps E ω (relOff κ (-(Real.pi / 2)) b jumps (lR κ b jumps E u l k ω₀) (lD₁ b jumps E ω)))
              (fun t => pcPt (wRun κ (-(Real.pi / 2)) b jumps (lD₁ b jumps E ω)
                  (relOff κ (-(Real.pi / 2)) b jumps (lR κ b jumps E u l k ω₀) (lD₁ b jumps E ω)))
                (lD₁ b jumps E ω (relOff κ (-(Real.pi / 2)) b jumps (lR κ b jumps E u l k ω₀) (lD₁ b jumps E ω)))
                (shiftD κ (-(Real.pi / 2)) b jumps (lR κ b jumps E u l k ω₀) (lD₁ b jumps E ω) 0 + t))
              ((lD₁ b jumps E ω (relOff κ (-(Real.pi / 2)) b jumps (lR κ b jumps E u l k ω₀)
                (lD₁ b jumps E ω))).2 -
                shiftD κ (-(Real.pi / 2)) b jumps (lR κ b jumps E u l k ω₀) (lD₁ b jumps E ω) 0) := by
  have hW := sb2LowerChainStatement_of_thm12_thm13 h12 h13 h12₀ h13₀
  have hS3 := S3.Asm.sb2LowerWalkTailNoCommonArcHStatement_of_thm12_thm13 h12 h13 h12₀ h13₀
  intro κ hκ hκ4 b jumps hb Ω _ _ P _ h hh W' ζ' hcf hζ' E hE hER u l k hu hlp hlθ hL hleft
  have hsp : IsBoundaryContinuedProgram (upperSpec u l).2.2 := isBoundaryContinuedProgram_upperSpec hlθ
  have hm𝒢 := (hE _ hsp).2.1 k
  have hRu := hER _ hsp
  have hRLQ := KernelTower.ae_ae_condExpKernel_of_ae hm𝒢
    (GW1W.regLaunches_of_stagedPiecesRegular (hER _ (GW1X.isBoundaryContinuedProgram_walkR b jumps)))
  filter_upwards [hW κ hκ hκ4 b jumps hb P h hh W' ζ' hcf hζ' E hE hER u l k hu hlp hlθ hL hleft,
    hS3 κ hκ hκ4 b jumps hb P h hh W' ζ' hcf hζ' E hE hER u l k hu hlp hlθ hL hleft,
    sb2LowerUpperChart κ hκ hκ4 b jumps hb P h hh W' ζ' hcf hζ' E hE hER u l k hu hlp hlθ hL hleft,
    sb2LowerTailRight κ hκ hκ4 b jumps hb P h hh W' ζ' hcf hζ' E hE hER u l k hu hlp hlθ hL hleft,
    sb2LowerHeadHull κ hκ hκ4 b jumps hb P h hh W' ζ' hcf hζ' E hE hER u l k hu hlp hlθ hL hleft,
    hRLQ, hRu] with ω₀ hW₀ hS₀ hC₀ hT₀ hH₀ hR₀ hRu₀
  intro c θ hlaunch b' J' h' hb' hT' hG'
  obtain ⟨hcc, -, hDom⟩ := hC₀ c θ hlaunch b' J' h' hb' hT' hG'
  have hreg₀ : ∀ (j : ℕ) (c' : Chart) (θ' : ℝ),
      (ExplState.run κ b jumps (upperSpec u l) (fun i => E (upperSpec u l) i ω₀) (j + 1)).2.2.2.1 j =
        some (c', θ') →
      PieceRegular (E (upperSpec u l) j ω₀).1 (min (instrTime (upperSpec u l) j) (E (upperSpec u l) j ω₀).2) :=
    fun j c' θ' hl' => hRu₀ j θ' _ c' (eq_launch_of_launches _ _ hl').1 hl'
  have hA : IsClosed (upperPrefix κ b jumps E u l k ω₀) :=
    (isCompact_upperPrefix hreg₀ (mem_upperLaunchSet hlaunch)).isClosed
  filter_upwards [hW₀ c θ hlaunch b' J' h' hb' hT' hG', hS₀ c θ hlaunch b' J' h' hb' hT' hG',
    hT₀ c θ hlaunch b' J' h' hb' hT' hG', hH₀ c θ hlaunch b' J' h' hb' hT' hG', hR₀]
    with ω hWω hSω hTω hHω hRω
  intro β₀ hβ hβ0 hβr tL hβL m hZ hl hpos hL
  have hRmem : ((lR κ b jumps E u l k ω₀ : ℝ) : ℂ) ∈ ExplState.physSet κ b jumps
      (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) (lD₁ b jumps E ω) := by
    rw [← hβL]; exact (hβr ▸ mem_range_self tL : β₀ tL ∈ lowerWalkSet κ b jumps E ω)
  rw [shiftD_zero] at hL ⊢
  exact stage0Act_of_mem hRω hWω hl hpos hcc m hA hDom hβ hβ0 hβr (hHω β₀ hβ hβ0 hβr tL hβL) hβL
    (mem_succ_of_not_zeroRoot hRmem hZ) hL (hTω β₀ hβ hβ0 hβr tL hβL) (hSω β₀ hβ hβ0 hβr tL hβL)

/-- **The zero-lifetime relative stage `0`, almost surely**: off a zero root, at a launch at `relOff` of lifetime `0`,
the lift relation with any regular zero-lifetime relative piece from the root. -/
theorem sb2LowerStage0Zero (h12 : Exist.Theorem12Statement.{u}) (h13 : Exist.Theorem13Statement.{u})
    (h12₀ : Exist.Theorem12Statement.{0}) (h13₀ : Exist.Theorem13Statement.{0}) :
    Lf.SB2LowerSetting.{u} fun κ b jumps _ _ _ P _ E u l k ω₀ c _ _ _ =>
      ∀ᵐ ω ∂(condExpKernel P (pastSigma κ b jumps (upperSpec u l) (E (upperSpec u l)) k) ω₀),
        ∀ β₀ : ℝ≥0 → ℂ, IsProperCurve β₀ → range β₀ = lowerWalkSet κ b jumps E ω →
          ∀ (tL : ℝ≥0) (γ : ℝ≥0 → ℂ) (m : ℝ), IsTailLiftCurve c (lR κ b jumps E u l k ω₀) m β₀ tL γ →
            ¬ ZeroRoot κ (-(Real.pi / 2)) b jumps (lR κ b jumps E u l k ω₀) (lD₁ b jumps E ω) →
            (wRun κ (-(Real.pi / 2)) b jumps (lD₁ b jumps E ω)
              (relOff κ (-(Real.pi / 2)) b jumps (lR κ b jumps E u l k ω₀) (lD₁ b jumps E ω) + 1)).2.2.2.1
                (relOff κ (-(Real.pi / 2)) b jumps (lR κ b jumps E u l k ω₀) (lD₁ b jumps E ω)) ≠ none →
            (lD₁ b jumps E ω (relOff κ (-(Real.pi / 2)) b jumps (lR κ b jumps E u l k ω₀) (lD₁ b jumps E ω))).2 = 0 →
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
  intro β₀ hβ hβr tL γ m hγ hZ hl h0 e₂ hreg he₂
  have hRmem : ((lR κ b jumps E u l k ω₀ : ℝ) : ℂ) ∈ ExplState.physSet κ b jumps
      (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) (lD₁ b jumps E ω) := by
    rw [← hγ.1]; exact (hβr ▸ mem_range_self tL : β₀ tL ∈ lowerWalkSet κ b jumps E ω)
  exact liftRel_zero_stage0 hRω hWω (fun n hn hl' => (hIω n).2.2 hn hl') hRmem hZ hl h0 hβ hγ.1 hγ.2.2.1 hreg he₂

end InteractingSLE.Theorem14.SB.Lk
