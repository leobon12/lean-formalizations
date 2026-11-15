/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.SB2YdPiece
import InteractingSLE.Spec.Supplement.SB2YaCl
import InteractingSLE.Spec.Supplement.SB2JcAS
import InteractingSLE.Spec.Supplement.SB2JwAS
import InteractingSLE.Spec.Supplement.SB2JvV5
import InteractingSLE.Spec.Supplement.SB2JqArc
import InteractingSLE.Spec.Supplement.SB2JqRun
import InteractingSLE.Spec.Supplement.SB2MeInputs
import InteractingSLE.Spec.Supplement.SB2MeRel
import InteractingSLE.Spec.Supplement.SB2UxExit
import InteractingSLE.Spec.Supplement.SB2LpAE
import InteractingSLE.Spec.Supplement.SB2JyHull

/-!
# SB2(2)'s start data at `relOff`, almost surely, from the stage-`0` facts only (decision D40)

Packet PROVE-T14-SB2LIFT (round 32; decision D40, LIFTSET's handoff §R20.3 item 1). The start disjunction of the
corrected bundle `Mn.ClauseTW` at the offset `relOff` — `ArcStart`, a finite `PieceStartV` or an infinite one, for every
ray correspondence `ι` — is the input `hS` of LIFTSET's joint induction `sb2LowerJointAS`. It needs only the relative
stage `0`, so it is exported here on its own, breaking the cycle with LIFTSET's `GeomAt4 ∧ StageFactsAS`:

* `startData_of0` (deterministic): the disjunction from the actual walk's facts, the root facts `RootFactsAt` and the
  root lift relation (`arcStart_of_zeroRoot`, `arcStart_of_corner`, `pieceStartV_of0`);
* **`SB2LowerStartDataStatement`**: for every everywhere regular relative family `EL` generating LIFTSET's stage-`0`
  curve on an event `G` off the stage-`0` zero event and equal to `zeroDrv` on it, kernel-almost surely on `G`: for
  every parametrization `β₀` of the lower walk, tail lift `γ` and ray correspondence `ι` (ray limit, ray identity),
  the start disjunction at `relOff`;
* **`sb2LowerStartDataStatement_of_thms`**: PROVED from Theorems 1.2–1.3, via LIFTSET's stage-`0` statements
  (`sb2LowerRootFull`, `sb2LowerStage0Act`, `liftRel_of_stage0`) and GW1's walk facts.

R48: Theorems 1.2–1.3 appear only as hypotheses (Theorem 1.4).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal
open QuantumZipper (H Hbar chiC)
open LQGMetric (DistOn)

universe u

namespace InteractingSLE.Theorem14.SB.Lk

open Supp9B Lx Lu Leaf FlowDilate Sec4 Exist Exist.Staged Exist.StagedLaw LuM GW1W GW1Bookkeep
open PiecewiseConstantBoundaryData (rightLim leftLim jumpSet)
open Sec7.PocketTraversal Sec7.Lemma71C

section Det

variable {κ θ : ℝ} {b₁ b₂ : ℝ → ℝ} {J₁ J₂ : Finset ℝ} {R : ℝ} {ι : ℝ → ℝ} {D₁ D₂ : ℕ → Drv}
  {β₀ γ : ℝ≥0 → ℂ} {tL : ℝ≥0} {c : Chart} {m : ℝ} {A : Set ℂ}

/-- **The start disjunction at `relOff` from the stage-`0` facts** (deterministic, one sample). -/
theorem startData_of0 (hb : IsPiecewiseConstantBoundaryData b₁ J₁) (hX : RunExitData κ b₁ J₁ θ D₁)
    (hP₁ : RegLaunches κ b₁ J₁ (boundaryWalkSpec b₁ J₁ θ true) D₁) (hW₁ : WalkChainFacts κ b₁ J₁ θ D₁)
    (hlm₁ : ∀ j, NoLeftMove κ b₁ J₁ θ D₁ j) (hlh₁ : ∀ j, NoLeftHit κ b₁ J₁ θ D₁ j)
    (hposW : ∀ n, 0 < n → (ExplState.run κ b₁ J₁ (boundaryWalkSpec b₁ J₁ θ true) D₁ (n + 1)).2.2.2.1 n ≠ none →
      (D₁ n).2 ≠ 0)
    (hallow : ∀ n, 1 ≤ n → AllowedSt κ b₁ (ExplState.run κ b₁ J₁ (boundaryWalkSpec b₁ J₁ θ true) D₁ n))
    (hdone : stStatus (ExplState.run κ b₁ J₁ (boundaryWalkSpec b₁ J₁ θ true) D₁
      (boundaryWalkSpec b₁ J₁ θ true).2.2.length) = stDone)
    (hRH : ∀ n, (ExplState.run κ b₁ J₁ (boundaryWalkSpec b₁ J₁ θ true) D₁ (n + 1)).2.2.2.1 n ≠ none →
      (D₁ n).2 ≠ ⊤ → (D₁ n).2 ≠ 0 → ∃ x : ℝ, stRecR (ExplState.run κ b₁ J₁ (boundaryWalkSpec b₁ J₁ θ true) D₁ n) < x ∧
        lHit (stChart (ExplState.run κ b₁ J₁ (boundaryWalkSpec b₁ J₁ θ true) D₁ n)) ⊤ (D₁ n) x)
    (hι : RayCorr b₁ J₁ b₂ J₂ R ι) (hD : LiftCurveData β₀ γ tL R ι) (hγ : IsTailLiftCurve c R m β₀ tL γ)
    (hβ : IsProperCurve β₀) (hβ0 : β₀ 0 = 0)
    (hβr : range β₀ = ExplState.physSet κ b₁ J₁ (boundaryWalkSpec b₁ J₁ θ true) D₁) (hU : UpperChartOK c)
    (hK : β₀ '' Icc 0 tL ⊆ hullK A) (hDom : c.2.1 '' H = H \ fillH A)
    (hhead : ∀ t ≤ tL, ∀ x : ℝ, β₀ t = x → x ≤ R) (hreg₂ : IsRegularDriver (D₂ 0))
    (hRF : RootFactsAt κ θ b₁ J₁ b₂ J₂ R c m D₁ D₂)
    (hPL0 : ¬ ZeroRoot κ θ b₁ J₁ R D₁ →
      (ExplState.run κ b₁ J₁ (boundaryWalkSpec b₁ J₁ θ true) D₁ (relOff κ θ b₁ J₁ R D₁ + 1)).2.2.2.1
        (relOff κ θ b₁ J₁ R D₁) ≠ none →
      (D₁ (relOff κ θ b₁ J₁ R D₁)).2 - shiftD κ θ b₁ J₁ R D₁ 0 ≠ 0 →
      LiftRel β₀ tL γ (newPc (ExplState.run κ b₁ J₁ (boundaryWalkSpec b₁ J₁ θ true) D₁ (relOff κ θ b₁ J₁ R D₁))
        (D₁ (relOff κ θ b₁ J₁ R D₁))) (newPc (ExplState.init 0) (D₂ 0))) :
    (ArcStart κ θ b₁ J₁ R D₁ D₂ β₀ tL (relOff κ θ b₁ J₁ R D₁) ∨
        (PieceStartV κ θ b₁ J₁ b₂ J₂ R ι D₁ D₂ β₀ γ tL (relOff κ θ b₁ J₁ R D₁) ∧
          (D₁ (relOff κ θ b₁ J₁ R D₁)).2 ≠ ⊤)) ∨
      (PieceStartV κ θ b₁ J₁ b₂ J₂ R ι D₁ D₂ β₀ γ tL (relOff κ θ b₁ J₁ R D₁) ∧
        (D₁ (relOff κ θ b₁ J₁ R D₁)).2 = ⊤) := by
  by_cases hZ : ZeroRoot κ θ b₁ J₁ R D₁
  · exact Or.inl (Or.inl (arcStart_of_zeroRoot hb hX hP₁ hW₁ hlm₁ hlh₁ hposW hallow hdone hβ hβ0 hβr hγ.1 hZ
      hreg₂ (hRF.1 (Or.inl hZ))))
  by_cases hL0 : (D₁ (relOff κ θ b₁ J₁ R D₁)).2 - shiftD κ θ b₁ J₁ R D₁ 0 = 0
  · exact Or.inl (Or.inl (arcStart_of_corner hb hX hP₁ hW₁ hlm₁ hlh₁ hposW hallow hdone hRH hβ hβ0 hβr hγ.1 hZ
      hL0 hreg₂ (hRF.1 (Or.inr hL0))))
  have hV := pieceStartV_of0 hb hX hP₁ hW₁ hlm₁ hlh₁ hposW hallow hdone hRH hι hD hγ hβ hβ0 hβr hU hK hDom hhead
    hZ hL0 hreg₂ hRF fun hZ' hl => hPL0 hZ' hl hL0
  by_cases htop : (D₁ (relOff κ θ b₁ J₁ R D₁)).2 = ⊤
  · exact Or.inr ⟨hV, htop⟩
  · exact Or.inl (Or.inr ⟨hV, htop⟩)

end Det

/-- **Named target (D40): SB2(2)'s start data at `relOff`, from the stage-`0` facts only.** For every everywhere
regular relative family `EL` that generates LIFTSET's stage-`0` curve on an event `G` off the stage-`0` zero event and
is `zeroDrv` on it, kernel-almost surely on `G`, for every parametrization `β₀` of the lower walk, tail lift `γ` and
ray correspondence `ι` (with its ray limit and ray identity): `ArcStart`, a finite `PieceStartV`, or an infinite
`PieceStartV` at `relOff`. -/
def SB2LowerStartDataStatement : Prop :=
  Lf.SB2LowerSetting.{u} fun κ b jumps _ _ _ P _ E u l k ω₀ c b' J' _ =>
    ∀ m : ℝ, m = -upperEntry κ b jumps E u l k ω₀ → ∀ EL : ℕ → _ → Drv, (∀ j ω, IsRegularDriver (EL j ω)) →
    ∀ G : Set _, (∀ ω ∈ G, ω ∉ lZ4 κ b jumps E u l k ω₀ 0 EL →
        (EL 0 ω).2 = capLife (lρ3 κ b jumps E u l k ω₀ c b' J' m 0 EL ω) ∧
        ∀ T < capLife (lρ3 κ b jumps E u l k ω₀ c b' J' m 0 EL ω),
          IsGeneratingTrace (EL 0 ω).1 T (capTrace (lρ3 κ b jumps E u l k ω₀ c b' J' m 0 EL ω))) →
      (∀ ω ∈ G, ω ∈ lZ4 κ b jumps E u l k ω₀ 0 EL → EL 0 ω = zeroDrv) →
      ∀ᵐ ω ∂(condExpKernel P (pastSigma κ b jumps (upperSpec u l) (E (upperSpec u l)) k) ω₀), ω ∈ G →
        ∀ β₀ : ℝ≥0 → ℂ, IsProperCurve β₀ → β₀ 0 = 0 → range β₀ = lowerWalkSet κ b jumps E ω →
        ∀ (tL : ℝ≥0) (γ : ℝ≥0 → ℂ), IsTailLiftCurve c (lR κ b jumps E u l k ω₀) m β₀ tL γ →
        ∀ ι : ℝ → ℝ, RayCorr b jumps (affData 1 m b') (affJumps 1 m J') (lR κ b jumps E u l k ω₀) ι →
          RayChartLim c (lR κ b jumps E u l k ω₀) m ι →
          (∀ s, ∀ x : ℝ, lR κ b jumps E u l k ω₀ < x → β₀ (tL + s) = x → γ s = ι x) →
          (ArcStart κ (-(Real.pi / 2)) b jumps (lR κ b jumps E u l k ω₀) (lD₁ b jumps E ω) (fun j => EL j ω) β₀ tL
              (relOff κ (-(Real.pi / 2)) b jumps (lR κ b jumps E u l k ω₀) (lD₁ b jumps E ω)) ∨
            (PieceStartV κ (-(Real.pi / 2)) b jumps (affData 1 m b') (affJumps 1 m J') (lR κ b jumps E u l k ω₀) ι
                (lD₁ b jumps E ω) (fun j => EL j ω) β₀ γ tL
                (relOff κ (-(Real.pi / 2)) b jumps (lR κ b jumps E u l k ω₀) (lD₁ b jumps E ω)) ∧
              (lD₁ b jumps E ω (relOff κ (-(Real.pi / 2)) b jumps (lR κ b jumps E u l k ω₀) (lD₁ b jumps E ω))).2 ≠
                ⊤)) ∨
          (PieceStartV κ (-(Real.pi / 2)) b jumps (affData 1 m b') (affJumps 1 m J') (lR κ b jumps E u l k ω₀) ι
              (lD₁ b jumps E ω) (fun j => EL j ω) β₀ γ tL
              (relOff κ (-(Real.pi / 2)) b jumps (lR κ b jumps E u l k ω₀) (lD₁ b jumps E ω)) ∧
            (lD₁ b jumps E ω (relOff κ (-(Real.pi / 2)) b jumps (lR κ b jumps E u l k ω₀) (lD₁ b jumps E ω))).2 = ⊤)

/-- **The start data at `relOff`, PROVED** (Theorems 1.2–1.3). -/
theorem sb2LowerStartDataStatement_of_thms (h12 : Exist.Theorem12Statement.{u})
    (h13 : Exist.Theorem13Statement.{u}) (h12₀ : Exist.Theorem12Statement.{0})
    (h13₀ : Exist.Theorem13Statement.{0}) : SB2LowerStartDataStatement.{u} := by
  intro κ hκ hκ4 b jumps hb Ω _ _ P _ h hh W' ζ' hcf hζ' E hE hER u l k hu hlp hlθ hL hleft
  filter_upwards [sb2LowerRunExit h13₀ κ hκ hκ4 b jumps hb P h hh W' ζ' hcf hζ' E hE hER u l k hu hlp hlθ hL hleft,
    sb2LowerActualInputs h12 h13 h12₀ h13₀ κ hκ hκ4 b jumps hb P h hh W' ζ' hcf hζ' E hE hER u l k hu hlp hlθ hL
      hleft,
    sb2LowerAllowed h13₀ κ hκ hκ4 b jumps hb P h hh W' ζ' hcf hζ' E hE hER u l k hu hlp hlθ hL hleft,
    sb2LowerCompletion h13₀ κ hκ hκ4 b jumps hb P h hh W' ζ' hcf hζ' E hE hER u l k hu hlp hlθ hL hleft,
    sb2LowerRightHits h13₀ κ hκ hκ4 b jumps hb P h hh W' ζ' hcf hζ' E hE hER u l k hu hlp hlθ hL hleft,
    sb2LowerHead κ hκ hκ4 b jumps hb P h hh W' ζ' hcf hζ' E hE hER u l k hu hlp hlθ hL hleft,
    sb2LowerHeadHull κ hκ hκ4 b jumps hb P h hh W' ζ' hcf hζ' E hE hER u l k hu hlp hlθ hL hleft,
    sb2LowerUpperChart κ hκ hκ4 b jumps hb P h hh W' ζ' hcf hζ' E hE hER u l k hu hlp hlθ hL hleft,
    sb2LowerRootFull h12 h13 h12₀ h13₀ κ hκ hκ4 b jumps hb P h hh W' ζ' hcf hζ' E hE hER u l k hu hlp hlθ hL hleft,
    sb2LowerStage0Act h12 h13 h12₀ h13₀ κ hκ hκ4 b jumps hb P h hh W' ζ' hcf hζ' E hE hER u l k hu hlp hlθ hL
      hleft]
    with ω₀ hX₀ hI₀ hA₀ hd₀ hRH₀ hH₀ hK₀ hU₀ hRF₀ hAc₀
  intro c θ hlaunch b' J' h' hb' hT' hG' m hm EL hreg G hgen hZ
  obtain ⟨-, hU, hDom⟩ := hU₀ c θ hlaunch b' J' h' hb' hT' hG'
  filter_upwards [hX₀ c θ hlaunch b' J' h' hb' hT' hG', hI₀ c θ hlaunch b' J' h' hb' hT' hG',
    hA₀ c θ hlaunch b' J' h' hb' hT' hG', hd₀ c θ hlaunch b' J' h' hb' hT' hG',
    hRH₀ c θ hlaunch b' J' h' hb' hT' hG', hH₀ c θ hlaunch b' J' h' hb' hT' hG',
    hK₀ c θ hlaunch b' J' h' hb' hT' hG', hRF₀ c θ hlaunch b' J' h' hb' hT' hG' m hm,
    hAc₀ c θ hlaunch b' J' h' hb' hT' hG']
    with ω hXω hIω hAω hdω hRHω hHω hKω hRFω hAcω
  intro hGω β₀ hβ hβ0 hβr tL γ hγ ι hι hlim hray
  obtain ⟨hP₁, hW₁, hn⟩ := hIω
  have hhead := hHω β₀ hβ hβ0 hβr tL hγ.1
  have hD : LiftCurveData β₀ γ tL (lR κ b jumps E u l k ω₀) ι :=
    ⟨hβ.1, hβ.2.2.1, hγ.2.1.1, hγ.2.1.2.2.1, hγ.1, hγ.2.2.1,
      fun t ht him => hhead t ht _ (Complex.ext (by simp) (by simp [him])), hray, back_of_rayChartLim hγ hlim⟩
  -- the relative root off the zero event: generation, drivenness and the stage facts
  have hroot : ¬ ZeroRoot κ (-(Real.pi / 2)) b jumps (lR κ b jumps E u l k ω₀) (lD₁ b jumps E ω) →
      (lD₁ b jumps E ω (relOff κ (-(Real.pi / 2)) b jumps (lR κ b jumps E u l k ω₀) (lD₁ b jumps E ω))).2 -
        shiftD κ (-(Real.pi / 2)) b jumps (lR κ b jumps E u l k ω₀) (lD₁ b jumps E ω) 0 ≠ 0 →
      rootLife (wRun κ (-(Real.pi / 2)) b jumps (lD₁ b jumps E ω)
          (relOff κ (-(Real.pi / 2)) b jumps (lR κ b jumps E u l k ω₀) (lD₁ b jumps E ω)))
        (lD₁ b jumps E ω (relOff κ (-(Real.pi / 2)) b jumps (lR κ b jumps E u l k ω₀) (lD₁ b jumps E ω)))
        (lR κ b jumps E u l k ω₀) ≠ 0 ∧ ω ∉ lZ4 κ b jumps E u l k ω₀ 0 EL := by
    intro hZR hL0
    refine ⟨?_, fun hz => ((mem_cZ4_zero_iff _ _ _ _ _ _ _ _).1 hz).elim hZR hL0⟩
    unfold rootLife
    rw [← shiftD_zero]
    exact hL0
  have hRFat : RootFactsAt κ (-(Real.pi / 2)) b jumps (affData 1 m b') (affJumps 1 m J') (lR κ b jumps E u l k ω₀)
      c m (lD₁ b jumps E ω) (fun j => EL j ω) := by
    have hpos : ¬ ZeroRoot κ (-(Real.pi / 2)) b jumps (lR κ b jumps E u l k ω₀) (lD₁ b jumps E ω) →
        (lD₁ b jumps E ω (relOff κ (-(Real.pi / 2)) b jumps (lR κ b jumps E u l k ω₀) (lD₁ b jumps E ω))).2 -
          shiftD κ (-(Real.pi / 2)) b jumps (lR κ b jumps E u l k ω₀) (lD₁ b jumps E ω) 0 ≠ 0 →
        (EL 0 ω).2 ≠ 0 ∧ Mn.StageFacts c m (wRun κ (-(Real.pi / 2)) b jumps (lD₁ b jumps E ω)
            (relOff κ (-(Real.pi / 2)) b jumps (lR κ b jumps E u l k ω₀) (lD₁ b jumps E ω)))
          (lD₁ b jumps E ω (relOff κ (-(Real.pi / 2)) b jumps (lR κ b jumps E u l k ω₀) (lD₁ b jumps E ω)))
          (shiftD κ (-(Real.pi / 2)) b jumps (lR κ b jumps E u l k ω₀) (lD₁ b jumps E ω) 0)
          (wRun κ (-(Real.pi / 2)) (affData 1 m b') (affJumps 1 m J') (fun j => EL j ω) 0) (EL 0 ω) := by
      intro hZR hL0
      obtain ⟨hlife, hnz⟩ := hroot hZR hL0
      obtain ⟨he, hg⟩ := hgen ω hGω hnz
      rw [lρ3_zero] at he hg
      have hR0 := hRFω hZR hlife (wRun κ (-(Real.pi / 2)) (affData 1 m b') (affJumps 1 m J') (fun j => EL j ω) 0)
        rfl
      have hdr := hR0.1
      refine ⟨?_, (hR0.2 (EL 0 ω) (hreg 0 ω) he hg).2⟩
      rw [he]
      exact (capLife_pos_of_driven hdr).ne'
    refine ⟨fun hz => hZ ω hGω ((mem_cZ4_zero_iff _ _ _ _ _ _ _ _).2 hz), hpos, fun hfin => ?_⟩
    show LocalExt.IsDrvGood (recHist (recOf ⊤ (EL 0 ω)))
    by_cases hz : ZeroRoot κ (-(Real.pi / 2)) b jumps (lR κ b jumps E u l k ω₀) (lD₁ b jumps E ω) ∨
        (lD₁ b jumps E ω (relOff κ (-(Real.pi / 2)) b jumps (lR κ b jumps E u l k ω₀) (lD₁ b jumps E ω))).2 -
          shiftD κ (-(Real.pi / 2)) b jumps (lR κ b jumps E u l k ω₀) (lD₁ b jumps E ω) 0 = 0
    · rw [hZ ω hGω ((mem_cZ4_zero_iff _ _ _ _ _ _ _ _).2 hz)]
      exact isDrvGood_zeroDrv
    · push Not at hz
      obtain ⟨-, hF⟩ := hpos hz.1 hz.2
      exact isDrvGood_of_continuousOn_le (hreg 0 ω) (GW1W.min_top_ne_top hfin)
        (by rw [min_eq_right (le_top : (EL 0 ω).2 ≤ ⊤)]; exact hF.2.2.2.2.2.2.2.1)
  -- the root lift relation at a positive shifted lifetime
  have hPL0 : ¬ ZeroRoot κ (-(Real.pi / 2)) b jumps (lR κ b jumps E u l k ω₀) (lD₁ b jumps E ω) →
      (wRun κ (-(Real.pi / 2)) b jumps (lD₁ b jumps E ω)
        (relOff κ (-(Real.pi / 2)) b jumps (lR κ b jumps E u l k ω₀) (lD₁ b jumps E ω) + 1)).2.2.2.1
          (relOff κ (-(Real.pi / 2)) b jumps (lR κ b jumps E u l k ω₀) (lD₁ b jumps E ω)) ≠ none →
      (lD₁ b jumps E ω (relOff κ (-(Real.pi / 2)) b jumps (lR κ b jumps E u l k ω₀) (lD₁ b jumps E ω))).2 -
        shiftD κ (-(Real.pi / 2)) b jumps (lR κ b jumps E u l k ω₀) (lD₁ b jumps E ω) 0 ≠ 0 →
      LiftRel β₀ tL γ (newPc (wRun κ (-(Real.pi / 2)) b jumps (lD₁ b jumps E ω)
          (relOff κ (-(Real.pi / 2)) b jumps (lR κ b jumps E u l k ω₀) (lD₁ b jumps E ω)))
        (lD₁ b jumps E ω (relOff κ (-(Real.pi / 2)) b jumps (lR κ b jumps E u l k ω₀) (lD₁ b jumps E ω))))
        (newPc (ExplState.init 0) (EL 0 ω)) := by
    intro hZR hl hL0
    obtain ⟨hlife, hnz⟩ := hroot hZR hL0
    obtain ⟨he, hg⟩ := hgen ω hGω hnz
    rw [lρ3_zero] at he hg
    have hR0 := hRFω hZR hlife (wRun κ (-(Real.pi / 2)) (affData 1 m b') (affJumps 1 m J') (fun j => EL j ω) 0)
      rfl
    have hdr := hR0.1
    have hrel := (hR0.2 (EL 0 ω) (hreg 0 ω) he hg).1
    have hpos₁ : (lD₁ b jumps E ω
        (relOff κ (-(Real.pi / 2)) b jumps (lR κ b jumps E u l k ω₀) (lD₁ b jumps E ω))).2 ≠ 0 := fun h0 =>
      hL0 (by rw [h0]; exact zero_tsub _)
    have hact := hAcω β₀ hβ hβ0 hβr tL hγ.1 m hZR hl hpos₁ hL0
    rw [shiftD_zero] at hact
    exact liftRel_of_stage0 hγ hU hDom (hKω β₀ hβ hβ0 hβr tL hγ.1) hβ hβr hP₁ hl
      (fun hLt htop => hLt (by rw [htop]; exact ENNReal.top_sub_coe)) (hact.facts hrel) hdr he hg
      (hreg 0 ω).2.1
  exact startData_of0 hb hXω hP₁ hW₁ (fun j => (hn j).1) (fun j => (hn j).2.1) (fun j => (hn j).2.2) hAω hdω hRHω hι
    hD hγ hβ hβ0 hβr hU (hKω β₀ hβ hβ0 hβr tL hγ.1) hDom hhead (hreg 0 ω) hRFat hPL0

end InteractingSLE.Theorem14.SB.Lk
