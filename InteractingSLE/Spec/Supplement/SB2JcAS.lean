/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.SB2JcInd
import InteractingSLE.Spec.Supplement.SB2JcPinv
import InteractingSLE.Spec.Supplement.SB2XzAS
import InteractingSLE.Spec.Supplement.SBS3LtMain
import InteractingSLE.Spec.Supplement.SBS3LtDensity
import InteractingSLE.Spec.Supplement.SB2JqRun
import InteractingSLE.Spec.Supplement.SB2MzFacts
import InteractingSLE.Spec.Supplement.SB2XlDom

/-!
# SB2(2)'s joint stage induction at `j ≥ 2`, almost surely under the retained kernel

Packet PROVE-SB2-LIFTSET (round 20, D29, D36). **`sb2LowerJointAS`** (Theorems 1.2–1.3): in SB2(2)'s setting, at an
upper launch, for every everywhere regular relative family `EL` generating the v4 stage curves on an event `G`, almost
surely under the retained kernel, on `G`: for every proper parametrization `β₀` of the lower walk and tail lift `γ`,
every ray correspondence `ι` of the corrected bundle (`RayCorr`, `RayChartLim`, the ray identity, continuity), and
**SB2LIFT's start disjunction at `relOff`** (`ArcStart`, or a finite `PieceStartV` — the `RunInputs''`-free part of
`ClauseTW`'s start, the input `hS` of SB2LIFT's `runInputs_of_lifts`), with the relative root regular when launched:

* `Mn.StageFacts` at every launching relative stage `j ≥ 2` (the `j ≥ 2` part of `Mn.StageFactsAll`);
* drivenness and `StageRelP` at every actual launch at `i + relOff`, `i ≥ 2` (the `i ≥ 2` part of `StagesGeom4`).

The per-sample inputs of `joint_all` come from the landed almost-sure facts (actual inputs, allowed states, right
hits, completion, head and head hull, connectors right of `0`, S1 through the frozen upper run, Lemma S3's tail form,
the density of good times, the upper chart's facts, the pinch-invariant prefixes `ae_pinv_walk`, the upper prefix as
a pinch-invariant path).
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

open Supp9B Lx Lu Leaf FlowDilate Sec4 Exist Exist.Staged Exist.StagedLaw LuM GW1W GW1Bookkeep GW1P
open Sec7.PocketTraversal Sec7.Lemma71C

/-- The launch-level v4 stage curve away from stage `0` is the unshifted run-chart stage curve. -/
theorem lρ3_of_ne {κ : ℝ} {b : ℝ → ℝ} {jumps : Finset ℝ} {Ω : Type u} {E : ExplSpec → ℕ → Ω → Drv} {u : ℝ}
    {l : List (ℝ × ℝ≥0)} {k : ℕ} {ω₀ : Ω} {c : Chart} {b' : ℝ → ℝ} {J' : Finset ℝ} {m : ℝ} {j : ℕ} (hj : j ≠ 0)
    (F : ℕ → Ω → Drv) (ω : Ω) :
    lρ3 κ b jumps E u l k ω₀ c b' J' m j F ω = stCurvep c m
      (pcPt (wRun κ (-(Real.pi / 2)) b jumps (lD₁ b jumps E ω)
        (j + relOff κ (-(Real.pi / 2)) b jumps (lR κ b jumps E u l k ω₀) (lD₁ b jumps E ω)))
        (lD₁ b jumps E ω (j + relOff κ (-(Real.pi / 2)) b jumps (lR κ b jumps E u l k ω₀) (lD₁ b jumps E ω))))
      (lD₁ b jumps E ω (j + relOff κ (-(Real.pi / 2)) b jumps (lR κ b jumps E u l k ω₀) (lD₁ b jumps E ω))).2
      (wRun κ (-(Real.pi / 2)) (affData 1 m b') (affJumps 1 m J') (fun i => F i ω) j) := by
  have hq : (fun t => pcPt (wRun κ (-(Real.pi / 2)) b jumps (lD₁ b jumps E ω)
        (j + relOff κ (-(Real.pi / 2)) b jumps (lR κ b jumps E u l k ω₀) (lD₁ b jumps E ω)))
        (lD₁ b jumps E ω (j + relOff κ (-(Real.pi / 2)) b jumps (lR κ b jumps E u l k ω₀) (lD₁ b jumps E ω)))
        (0 + t)) = pcPt (wRun κ (-(Real.pi / 2)) b jumps (lD₁ b jumps E ω)
        (j + relOff κ (-(Real.pi / 2)) b jumps (lR κ b jumps E u l k ω₀) (lD₁ b jumps E ω)))
        (lD₁ b jumps E ω (j + relOff κ (-(Real.pi / 2)) b jumps (lR κ b jumps E u l k ω₀) (lD₁ b jumps E ω))) :=
    funext fun t => by rw [zero_add]
  show cΦ3 κ (-(Real.pi / 2)) b jumps (lR κ b jumps E u l k ω₀) c m (lD₁ b jumps E) j ω _ = _
  unfold cΦ3 stageShift
  simp only [hj, ↓reduceIte, ENNReal.coe_zero, tsub_zero]
  rw [hq]

/-- The launch-level v4 stage curve at stage `0` is the run-chart stage curve of the shifted start piece. -/
theorem lρ3_zero {κ : ℝ} {b : ℝ → ℝ} {jumps : Finset ℝ} {Ω : Type u} {E : ExplSpec → ℕ → Ω → Drv} {u : ℝ}
    {l : List (ℝ × ℝ≥0)} {k : ℕ} {ω₀ : Ω} {c : Chart} {b' : ℝ → ℝ} {J' : Finset ℝ} {m : ℝ}
    (F : ℕ → Ω → Drv) (ω : Ω) :
    lρ3 κ b jumps E u l k ω₀ c b' J' m 0 F ω = stCurvep c m
      (rootPt (wRun κ (-(Real.pi / 2)) b jumps (lD₁ b jumps E ω)
          (relOff κ (-(Real.pi / 2)) b jumps (lR κ b jumps E u l k ω₀) (lD₁ b jumps E ω)))
        (lD₁ b jumps E ω (relOff κ (-(Real.pi / 2)) b jumps (lR κ b jumps E u l k ω₀) (lD₁ b jumps E ω)))
        (lR κ b jumps E u l k ω₀))
      (rootLife (wRun κ (-(Real.pi / 2)) b jumps (lD₁ b jumps E ω)
          (relOff κ (-(Real.pi / 2)) b jumps (lR κ b jumps E u l k ω₀) (lD₁ b jumps E ω)))
        (lD₁ b jumps E ω (relOff κ (-(Real.pi / 2)) b jumps (lR κ b jumps E u l k ω₀) (lD₁ b jumps E ω)))
        (lR κ b jumps E u l k ω₀))
      (wRun κ (-(Real.pi / 2)) (affData 1 m b') (affJumps 1 m J') (fun i => F i ω) 0) := by
  show cΦ3 κ (-(Real.pi / 2)) b jumps (lR κ b jumps E u l k ω₀) c m (lD₁ b jumps E) 0 ω _ = _
  unfold cΦ3 stageShift rootPt rootLife
  simp only [↓reduceIte, zero_add]

/-- **SB2(2)'s joint stage induction at `j ≥ 2`, almost surely under the retained kernel** (Theorems 1.2–1.3). -/
theorem sb2LowerJointAS (h12 : Exist.Theorem12Statement.{u}) (h13 : Exist.Theorem13Statement.{u})
    (h12₀ : Exist.Theorem12Statement.{0}) (h13₀ : Exist.Theorem13Statement.{0}) :
    Lf.SB2LowerSetting.{u} fun κ b jumps _ _ _ P _ E u l k ω₀ c b' J' _ =>
      ∀ m : ℝ, m = -upperEntry κ b jumps E u l k ω₀ → ∀ EL : ℕ → _ → Drv, (∀ j ω, IsRegularDriver (EL j ω)) →
      ∀ G : Set _, (∀ j, ∀ ω ∈ G, ω ∉ lZ4 κ b jumps E u l k ω₀ j EL →
        (EL j ω).2 = capLife (lρ3 κ b jumps E u l k ω₀ c b' J' m j EL ω) ∧
        ∀ T < capLife (lρ3 κ b jumps E u l k ω₀ c b' J' m j EL ω),
          IsGeneratingTrace (EL j ω).1 T (capTrace (lρ3 κ b jumps E u l k ω₀ c b' J' m j EL ω))) →
      (∀ j, ∀ ω ∈ G, ω ∈ lZ4 κ b jumps E u l k ω₀ j EL → EL j ω = zeroDrv) →
      ∀ᵐ ω ∂(condExpKernel P (pastSigma κ b jumps (upperSpec u l) (E (upperSpec u l)) k) ω₀), ω ∈ G →
        ∀ β₀ : ℝ≥0 → ℂ, IsProperCurve β₀ → β₀ 0 = 0 → range β₀ = lowerWalkSet κ b jumps E ω →
        ∀ (tL : ℝ≥0) (γ : ℝ≥0 → ℂ), IsTailLiftCurve c (lR κ b jumps E u l k ω₀) m β₀ tL γ →
        ∀ ι : ℝ → ℝ, RayCorr b jumps (affData 1 m b') (affJumps 1 m J') (lR κ b jumps E u l k ω₀) ι →
          RayChartLim c (lR κ b jumps E u l k ω₀) m ι →
          (∀ s, ∀ x : ℝ, lR κ b jumps E u l k ω₀ < x → β₀ (tL + s) = x → γ s = ι x) →
          ContinuousOn ι (Ici (lR κ b jumps E u l k ω₀)) →
          (ArcStart κ (-(Real.pi / 2)) b jumps (lR κ b jumps E u l k ω₀) (lD₁ b jumps E ω) (fun j => EL j ω) β₀ tL
              (relOff κ (-(Real.pi / 2)) b jumps (lR κ b jumps E u l k ω₀) (lD₁ b jumps E ω)) ∨
            (PieceStartV κ (-(Real.pi / 2)) b jumps (affData 1 m b') (affJumps 1 m J') (lR κ b jumps E u l k ω₀) ι
                (lD₁ b jumps E ω) (fun j => EL j ω) β₀ γ tL
                (relOff κ (-(Real.pi / 2)) b jumps (lR κ b jumps E u l k ω₀) (lD₁ b jumps E ω)) ∧
              (lD₁ b jumps E ω (relOff κ (-(Real.pi / 2)) b jumps (lR κ b jumps E u l k ω₀) (lD₁ b jumps E ω))).2 ≠
                ⊤)) →
          (∀ j, 2 ≤ j →
            (wRun κ (-(Real.pi / 2)) (affData 1 m b') (affJumps 1 m J') (fun i => EL i ω) (j + 1)).2.2.2.1 j ≠ none →
            Mn.StageFacts c m (wRun κ (-(Real.pi / 2)) b jumps (lD₁ b jumps E ω)
                (j + relOff κ (-(Real.pi / 2)) b jumps (lR κ b jumps E u l k ω₀) (lD₁ b jumps E ω)))
              (lD₁ b jumps E ω (j + relOff κ (-(Real.pi / 2)) b jumps (lR κ b jumps E u l k ω₀) (lD₁ b jumps E ω)))
              0 (wRun κ (-(Real.pi / 2)) (affData 1 m b') (affJumps 1 m J') (fun i => EL i ω) j) (EL j ω)) ∧
          (∀ i, 2 ≤ i →
            (wRun κ (-(Real.pi / 2)) b jumps (lD₁ b jumps E ω)
              (i + relOff κ (-(Real.pi / 2)) b jumps (lR κ b jumps E u l k ω₀) (lD₁ b jumps E ω) + 1)).2.2.2.1
              (i + relOff κ (-(Real.pi / 2)) b jumps (lR κ b jumps E u l k ω₀) (lD₁ b jumps E ω)) ≠ none →
            IsDrivenCurve (stCurvep c m (pcPt (wRun κ (-(Real.pi / 2)) b jumps (lD₁ b jumps E ω)
                (i + relOff κ (-(Real.pi / 2)) b jumps (lR κ b jumps E u l k ω₀) (lD₁ b jumps E ω)))
                (lD₁ b jumps E ω (i + relOff κ (-(Real.pi / 2)) b jumps (lR κ b jumps E u l k ω₀) (lD₁ b jumps E ω))))
              (lD₁ b jumps E ω (i + relOff κ (-(Real.pi / 2)) b jumps (lR κ b jumps E u l k ω₀) (lD₁ b jumps E ω))).2
              (wRun κ (-(Real.pi / 2)) (affData 1 m b') (affJumps 1 m J') (fun j => EL j ω) i)) ∧
            StageRelP c m (pcPt (wRun κ (-(Real.pi / 2)) b jumps (lD₁ b jumps E ω)
                (i + relOff κ (-(Real.pi / 2)) b jumps (lR κ b jumps E u l k ω₀) (lD₁ b jumps E ω)))
                (lD₁ b jumps E ω (i + relOff κ (-(Real.pi / 2)) b jumps (lR κ b jumps E u l k ω₀) (lD₁ b jumps E ω))))
              (lD₁ b jumps E ω (i + relOff κ (-(Real.pi / 2)) b jumps (lR κ b jumps E u l k ω₀) (lD₁ b jumps E ω))).2
              (wRun κ (-(Real.pi / 2)) (affData 1 m b') (affJumps 1 m J') (fun j => EL j ω) i) (EL i ω)) := by
  intro κ hκ hκ4 b jumps hb Ω _ _ P _ h hh W' ζ' hcf hζ' E hE hER u l k hu hlp hlθ hL hleft
  have hsp : IsBoundaryContinuedProgram (upperSpec u l).2.2 := isBoundaryContinuedProgram_upperSpec hlθ
  have hEu := hE _ hsp
  have hRu := hER _ hsp
  have hm𝒢 := hEu.2.1 k
  have hleftQ := KernelTower.ae_ae_condExpKernel_of_ae hm𝒢 hleft
  have hrunQ := Retain.ae_ae_run_eq (upperSpec u l) hRu hm𝒢 le_rfl
  have hpinvQ := KernelTower.ae_ae_condExpKernel_of_ae hm𝒢
    (ae_pinv_walk h13 h13₀ hκ hκ4 hb hh hcf hζ' hE hER)
  have hRLQ := KernelTower.ae_ae_condExpKernel_of_ae hm𝒢
    (GW1W.regLaunches_of_stagedPiecesRegular (hER _ (GW1X.isBoundaryContinuedProgram_walkR b jumps)))
  filter_upwards [hleftQ, hrunQ, hRu, ae_injLaunches h13 hκ hκ4 hb hEu hRu, hpinvQ,
    sb2LowerActualInputs h12 h13 h12₀ h13₀ κ hκ hκ4 b jumps hb P h hh W' ζ' hcf hζ' E hE hER u l k hu hlp hlθ hL
      hleft,
    sb2LowerAllowed h13₀ κ hκ hκ4 b jumps hb P h hh W' ζ' hcf hζ' E hE hER u l k hu hlp hlθ hL hleft,
    sb2LowerRightHits h13₀ κ hκ hκ4 b jumps hb P h hh W' ζ' hcf hζ' E hE hER u l k hu hlp hlθ hL hleft,
    sb2LowerCompletion h13₀ κ hκ hκ4 b jumps hb P h hh W' ζ' hcf hζ' E hE hER u l k hu hlp hlθ hL hleft,
    sb2LowerHead κ hκ hκ4 b jumps hb P h hh W' ζ' hcf hζ' E hE hER u l k hu hlp hlθ hL hleft,
    sb2LowerHeadHull κ hκ hκ4 b jumps hb P h hh W' ζ' hcf hζ' E hE hER u l k hu hlp hlθ hL hleft,
    Lk.sb2LowerArcsIci h13₀ κ hκ hκ4 b jumps hb P h hh W' ζ' hcf hζ' E hE hER u l k hu hlp hlθ hL hleft,
    S3.Asm.sb2LowerWalkTailNoCommonArcHStatement_of_thm12_thm13 h12 h13 h12₀ h13₀ κ hκ hκ4 b jumps hb P h hh W' ζ'
      hcf hζ' E hE hER u l k hu hlp hlθ hL hleft,
    S3.Asm.sb2LowerStageDensity_of_thm12_thm13 h12 h13 h12₀ h13₀ κ hκ hκ4 b jumps hb P h hh W' ζ' hcf hζ' E hE hER u
      l k hu hlp hlθ hL hleft,
    sb2LowerUpperChart κ hκ hκ4 b jumps hb P h hh W' ζ' hcf hζ' E hE hER u l k hu hlp hlθ hL hleft,
    hRLQ, sb2LowerRootFull h12 h13 h12₀ h13₀ κ hκ hκ4 b jumps hb P h hh W' ζ' hcf hζ' E hE hER u l k hu hlp hlθ hL
      hleft]
    with ω₀ hleft₀ hrun₀ hR₀ hinj₀ hpinv₀ hI₀ hA₀ hX₀ hC₀ hH₀ hK₀ hZ₀ hS₀ hD₀ hU₀ hRL₀ hRF₀
  intro c θ hlaunch b' J' h' hb' hT' hG' m hm EL hreg G hgen hZ
  -- the upper prefix as a pinch-invariant path, and the upper chart
  have hreg₀ : ∀ (j : ℕ) (c' : Chart) (θ' : ℝ),
      (ExplState.run κ b jumps (upperSpec u l) (fun i => E (upperSpec u l) i ω₀) (j + 1)).2.2.2.1 j =
        some (c', θ') →
      PieceRegular (E (upperSpec u l) j ω₀).1 (min (instrTime (upperSpec u l) j) (E (upperSpec u l) j ω₀).2) :=
    fun j c' θ' hl' => hR₀ j θ' _ c' (eq_launch_of_launches _ _ hl').1 hl'
  obtain ⟨pA, hp, hp0, hpH, hpA, hcl⟩ :=
    Lf.exists_path_upperPrefix (κ := κ) (b := b) (jumps := jumps) hu l (fun j => E (upperSpec u l) j ω₀) hreg₀ k
  have hpA' : pA '' Icc 0 1 = upperPrefix κ b jumps E u l k ω₀ := hpA
  have hpv : LuM.PInv 0 (pA '' Icc 0 1) := by rw [hpA]; exact Lk.pinv_schedule hu l _ hreg₀ hinj₀ k
  obtain ⟨hcc, hU, hDom⟩ := hU₀ c θ hlaunch b' J' h' hb' hT' hG'
  have hup : RegLaunches κ b jumps (upperSpec u l) (fun i => E (upperSpec u l) i ω₀) := fun j c' θ' hl' =>
    hreg₀ j c' θ' hl'
  obtain ⟨hcD, -, hcbd⟩ := Mn.upperChart_facts hup hlaunch
  have hcN := Mz.isNormalized_launchChart (upperSpec u l) hup hlaunch
  have hcD' : IsDomainChart (H \ fillH (pA '' Icc 0 1)) c := by rw [hpA']; exact hcD
  have hDom' : c.2.1 '' H = H \ fillH (pA '' Icc 0 1) := by rw [hpA']; exact hDom
  -- the sample
  filter_upwards [hrun₀, hleft₀, hpinv₀, hI₀ c θ hlaunch b' J' h' hb' hT' hG', hA₀ c θ hlaunch b' J' h' hb' hT' hG',
    hX₀ c θ hlaunch b' J' h' hb' hT' hG', hC₀ c θ hlaunch b' J' h' hb' hT' hG', hH₀ c θ hlaunch b' J' h' hb' hT' hG',
    hK₀ c θ hlaunch b' J' h' hb' hT' hG', hZ₀ c θ hlaunch b' J' h' hb' hT' hG',
    hS₀ c θ hlaunch b' J' h' hb' hT' hG', hD₀ c θ hlaunch b' J' h' hb' hT' hG',
    hRF₀ c θ hlaunch b' J' h' hb' hT' hG' m hm]
    with ω hω hleftω hpinvω hIω hAω hXω hCω hHω hKω hZω hSω hDω hRFω
  intro hGω β₀ hβ hβ0 hβr tL γ hγ ι hι hlim hray hcont hS
  -- the relative root is regular (the root facts, or the zero driver)
  have hroot : (wRun κ (-(Real.pi / 2)) (affData 1 m b') (affJumps 1 m J') (fun j => EL j ω) 1).2.2.2.1 0 ≠
      none → GW1P.PieceRegular (EL 0 ω).1 (EL 0 ω).2 := fun _ => by
    by_cases hz : ω ∈ lZ4 κ b jumps E u l k ω₀ 0 EL
    · rw [hZ 0 ω hGω hz]; exact Mn.pieceRegular_of_zero isRegularDriver_zeroDrv rfl
    · have hnZR : ¬ ZeroRoot κ (-(Real.pi / 2)) b jumps (lR κ b jumps E u l k ω₀) (lD₁ b jumps E ω) :=
        fun h => hz (Or.inr (Or.inl ⟨rfl, h⟩))
      have hlife : rootLife (wRun κ (-(Real.pi / 2)) b jumps (lD₁ b jumps E ω)
            (relOff κ (-(Real.pi / 2)) b jumps (lR κ b jumps E u l k ω₀) (lD₁ b jumps E ω)))
          (lD₁ b jumps E ω (relOff κ (-(Real.pi / 2)) b jumps (lR κ b jumps E u l k ω₀) (lD₁ b jumps E ω)))
          (lR κ b jumps E u l k ω₀) ≠ 0 := fun h => hz (Or.inr (Or.inr (by
        unfold stageShift; simp only [↓reduceIte, zero_add]; exact h)))
      obtain ⟨he, hg⟩ := hgen 0 ω hGω hz
      rw [lρ3_zero] at he hg
      have hroot := (hRFω hnZR hlife _ rfl).2 (EL 0 ω) (hreg 0 ω) he hg
      exact hroot.2.2.2.2.2.2.2
  obtain ⟨hP₁, hW₁, hn⟩ := hIω
  -- S1 through the frozen upper run
  have hlaunchω : ω ∈ upperLaunchSet κ b jumps E u l k := by
    show (ExplState.run κ b jumps (upperSpec u l) (fun j => E (upperSpec u l) j ω) (k + 1)).2.2.2.1 k ≠ none
    rw [launches_run_succ_of_run_eq (upperSpec u l) hω, hlaunch]
    exact Option.some_ne_none _
  have hAeq : upperPrefix κ b jumps E u l k ω = upperPrefix κ b jumps E u l k ω₀ := by
    show prefixPhysSet κ b jumps (upperSpec u l) (fun j => E (upperSpec u l) j ω) k ∪ ((↑) : ℝ → ℂ) '' Icc u 0 =
      prefixPhysSet κ b jumps (upperSpec u l) (fun j => E (upperSpec u l) j ω₀) k ∪ ((↑) : ℝ → ℂ) '' Icc u 0
    unfold prefixPhysSet; rw [hω]
  have hav := hleftω hlaunchω
  rw [hAeq] at hav
  have hav' : prefixPhysSet κ b jumps (upperSpec u l) (fun j => E (upperSpec u l) j ω₀) k ∩
      rightSideOf (range β₀) = ∅ := by
    rw [hβr]
    exact eq_empty_of_subset_empty ((inter_subset_inter_left _ subset_union_left).trans hav.subset)
  have hAL : upperPrefix κ b jumps E u l k ω₀ ⊆ closedLeftSide β₀ :=
    Lf.subset_closedLeftSide_of_avoid hβ hβ0 hcl hav'
  have hS1 : pA '' Icc 0 1 ⊆ closedLeftSide β₀ := by rw [hpA']; exact hAL
  -- the per-sample inputs of the joint induction
  have hhead := hHω β₀ hβ hβ0 hβr tL hγ.1
  have hhull : β₀ '' Icc 0 tL ⊆ hullK (pA '' Icc 0 1) := by rw [hpA']; exact hKω β₀ hβ hβ0 hβr tL hγ.1
  have htail : TailArc κ (-(Real.pi / 2)) b jumps (lD₁ b jumps E ω) (lR κ b jumps E u l k ω₀) β₀ tL := by
    rcases hS with hA | ⟨hV, -⟩
    · exact tailArc_of_arcStart hβ hβr hγ.1 hhead hZω hP₁ (fun j => (hn j).1) (fun j => (hn j).2.1) hA
    · exact tailArc_of_pieceStart hβ hγ.1 hZω hP₁ (fun j => (hn j).1) (fun j => (hn j).2.1) hV
  have hD : LiftCurveData β₀ γ tL (lR κ b jumps E u l k ω₀) ι :=
    ⟨hβ.1, hβ.2.2.1, hγ.2.1.1, hγ.2.1.2.2.1, hγ.1, hγ.2.2.1,
      fun t ht him => hhead t ht _ (Complex.ext (by simp) (by simp [him])), hray, back_of_rayChartLim hγ hlim⟩
  have hS3 : ∀ tR : ℝ≥0, β₀ tR = ((lR κ b jumps E u l k ω₀ : ℝ) : ℂ) → ∀ s₁ s₂ : ℝ≥0, tR ≤ s₁ → s₁ < s₂ →
      ¬ β₀ '' Ioo s₁ s₂ ⊆ pA '' Icc 0 1 ∩ H := by
    rw [hpA']; exact hSω β₀ hβ hβ0 hβr
  have hJ : JointIn κ (-(Real.pi / 2)) b jumps (affData 1 m b') (affJumps 1 m J') (lR κ b jumps E u l k ω₀) ι
      (lD₁ b jumps E ω) (fun j => EL j ω) β₀ γ tL
      (relOff κ (-(Real.pi / 2)) b jumps (lR κ b jumps E u l k ω₀) (lD₁ b jumps E ω)) c m pA := by
    refine ⟨by rw [hpA'], relOff_even _ _ _ _ _ _, hP₁, hW₁, fun j => (hn j).1, fun j => (hn j).2.1,
      fun k' hk' => hAω k' (by omega), fun k' _ => hXω k', hCω, hpinvω, hp, hp0, hpH, hpv, hcD', hcN, hcbd, hU,
      hβ, hβ0, hβr, hS1, hS3, hγ, hhull, hhead, htail, hray, hD, hι, hcont, hS, fun j => hreg j ω, hroot, ?_, ?_⟩
    · intro j hj hl₁ hpos
      have hj0 : j ≠ 0 := by omega
      have hev : j % 2 = 0 := by
        have h1 := (GW1W.even_of_launches_walk hl₁).1
        have h2 := relOff_even κ (-(Real.pi / 2)) b jumps (lR κ b jumps E u l k ω₀) (lD₁ b jumps E ω)
        omega
      have hnZ : ω ∉ lZ4 κ b jumps E u l k ω₀ j EL := by
        rintro (h1 | ⟨h1, -⟩ | h1)
        · omega
        · exact hj0 h1
        · have hs : stageShift κ (-(Real.pi / 2)) b jumps (lR κ b jumps E u l k ω₀) (lD₁ b jumps E) j ω = 0 := by
            unfold stageShift; simp only [hj0, ↓reduceIte]
          rw [hs, ENNReal.coe_zero, tsub_zero] at h1
          exact hpos h1
      obtain ⟨he, hg⟩ := hgen j ω hGω hnZ
      rw [lρ3_of_ne hj0] at he hg
      exact ⟨he, hg⟩
    · exact fun i hi hl => hDω β₀ hβ hβ0 hβr tL hγ.1 i hi hl
  exact ⟨joint_stageFacts hJ, joint_stageRelP hJ⟩

end InteractingSLE.Theorem14.SB.Lk
