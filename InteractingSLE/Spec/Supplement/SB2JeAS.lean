/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.SB2JeFam

/-!
# SB2(2): LIFTSET's v6 input `Nv.SB2LowerGeomRestV6Statement`, proved from the start data (D40)

Packet PROVE-SB2-LIFTSET (round 21). **`sb2LowerGeomRestV6`** (Theorems 1.2–1.3 and SB2LIFT's start data
`SB2LowerStartDataFamStatement`, D40 — verbatim SB2LIFT's `Lk.SB2LowerStartDataStatement`, proved there by
`sb2LowerStartDataStatement_of_thms`): GEOM2's `Nv.SB2LowerGeomRestV6Statement` — inside every measurable
kernel-conull event `G₀` there is a measurable `Gd ⊆ G₀` such that

* (admissibility) for every family known below a stage `j`, the stage curve is driven on the v6 mask (stage `0`: the
  root facts; odd stages: excluded by the mask; stages `j ≥ 2`: `sample_core6` on the family truncated at `j`);
* (per-stage facts) every admissible family `EL` has `GeomAt4` (driven events the mask) and `Mn.StageFactsAS`
  (stage `0`: `root_pkg` and the head clause; stages `j ≥ 2`: `sample_core6` with `N = j + 1`).

`Gd` is `G₀` intersected with a measurable conull event on which all the per-sample facts hold
(`exists_meas_subset`), including the start data uniformly in the family (`sb2LowerStartDataU_of_fam`).
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

/-- An almost-sure property holds on a measurable conull set. -/
theorem exists_meas_subset {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {p : Ω → Prop} (h : ∀ᵐ ω ∂μ, p ω) :
    ∃ S : Set Ω, MeasurableSet S ∧ μ Sᶜ = 0 ∧ ∀ ω ∈ S, p ω := by
  obtain ⟨T, hT, hTm, hT0⟩ := exists_measurable_superset_of_null (ae_iff.1 h)
  refine ⟨Tᶜ, hTm.compl, by rw [compl_compl]; exact hT0, fun ω hω => ?_⟩
  by_contra hc
  exact hω (hT hc)

/-- **LIFTSET's v6 input from Theorems 1.2–1.3 and SB2LIFT's start data** (D40). -/
theorem sb2LowerGeomRestV6 (h12 : Exist.Theorem12Statement.{u}) (h13 : Exist.Theorem13Statement.{u})
    (h12₀ : Exist.Theorem12Statement.{0}) (h13₀ : Exist.Theorem13Statement.{0})
    (hSD : SB2LowerStartDataFamStatement.{u}) : Nv.SB2LowerGeomRestV6Statement.{u} := by
  intro κ hκ hκ4 b jumps hb Ω _ _ P _ h hh W' ζ' hcf hζ' E hE hER u l k hu hlp hlθ hL hleft
  have hsp : IsBoundaryContinuedProgram (upperSpec u l).2.2 := isBoundaryContinuedProgram_upperSpec hlθ
  have hEu := hE _ hsp
  have hRu := hER _ hsp
  have hm𝒢 := hEu.2.1 k
  have hleftQ := KernelTower.ae_ae_condExpKernel_of_ae hm𝒢 hleft
  have hrunQ := Retain.ae_ae_run_eq (upperSpec u l) hRu hm𝒢 le_rfl
  have hpinvQ := KernelTower.ae_ae_condExpKernel_of_ae hm𝒢
    (ae_pinv_walk h13 h13₀ hκ hκ4 hb hh hcf hζ' hE hER)
  have hβQ := KernelTower.ae_ae_condExpKernel_of_ae hm𝒢
    (Mn.rightWalkProperReg_of_thms h12 h13 h12₀ h13₀ κ hκ hκ4 b jumps hb P h hh W' ζ' hcf hζ' E hE hER)
  filter_upwards [hleftQ, hrunQ, hRu, ae_injLaunches h13 hκ hκ4 hb hEu hRu, hpinvQ, hβQ,
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
    sb2LowerTailLiftCurve h13 κ hκ hκ4 b jumps hb P h hh W' ζ' hcf hζ' E hE hER u l k hu hlp hlθ hL hleft,
    sb2LowerRayCorr h13 h13₀ κ hκ hκ4 b jumps hb P h hh W' ζ' hcf hζ' E hE hER u l k hu hlp hlθ hL hleft,
    sb2LowerStartDataU_of_fam hSD κ hκ hκ4 b jumps hb P h hh W' ζ' hcf hζ' E hE hER u l k hu hlp hlθ hL hleft,
    sb2LowerRootFull h12 h13 h12₀ h13₀ κ hκ hκ4 b jumps hb P h hh W' ζ' hcf hζ' E hE hER u l k hu hlp hlθ hL hleft,
    sb2LowerStage0Act h12 h13 h12₀ h13₀ κ hκ hκ4 b jumps hb P h hh W' ζ' hcf hζ' E hE hER u l k hu hlp hlθ hL hleft,
    sb2LowerStage0ZeroV4 h12 h13 h12₀ h13₀ κ hκ hκ4 b jumps hb P h hh W' ζ' hcf hζ' E hE hER u l k hu hlp hlθ hL
      hleft,
    sb2LowerLaunchRelOff h12 h13 h12₀ h13₀ κ hκ hκ4 b jumps hb P h hh W' ζ' hcf hζ' E hE hER u l k hu hlp hlθ hL
      hleft,
    sb2LowerHeadClause h12 h13 h12₀ h13₀ κ hκ hκ4 b jumps hb P h hh W' ζ' hcf hζ' E hE hER u l k hu hlp hlθ hL
      hleft]
    with ω₀ hleft₀ hrun₀ hR₀ hinj₀ hpinv₀ hβ₀ hI₀ hA₀ hX₀ hC₀ hH₀ hK₀ hZ₀ hS₀ hD₀ hU₀ hT₀ hι₀ hSD₀ hRF₀ hS0A₀
      hcor₀ hl0₀ hHC₀
  intro c θ hlaunch b' J' h' hb' hT' hG' _ m hm G₀ hG₀m hG₀n
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
  obtain ⟨-, hU, hDom⟩ := hU₀ c θ hlaunch b' J' h' hb' hT' hG'
  have hup : RegLaunches κ b jumps (upperSpec u l) (fun i => E (upperSpec u l) i ω₀) := fun j c' θ' hl' =>
    hreg₀ j c' θ' hl'
  obtain ⟨hcD, -, hcbd⟩ := Mn.upperChart_facts hup hlaunch
  have hcN := Mz.isNormalized_launchChart (upperSpec u l) hup hlaunch
  have hcD' : IsDomainChart (H \ fillH (pA '' Icc 0 1)) c := by rw [hpA']; exact hcD
  have hDom' : c.2.1 '' H = H \ fillH (pA '' Icc 0 1) := by rw [hpA']; exact hDom
  have hR' : lR κ b jumps E u l k ω₀ = realMax (pA '' Icc 0 1) := by rw [hpA']
  obtain ⟨hι, hcont, hlim, hinjι⟩ := hι₀ c θ hlaunch b' J' h' hb' hT' hG' m hm
  -- the measurable conull event of the per-sample facts
  obtain ⟨S, hSm, hS0, hSp⟩ := exists_meas_subset (hrun₀.and (hleft₀.and (hpinv₀.and (hβ₀.and ((hI₀ c θ hlaunch b' J'
    h' hb' hT' hG').and ((hA₀ c θ hlaunch b' J' h' hb' hT' hG').and ((hX₀ c θ hlaunch b' J' h' hb' hT' hG').and ((hC₀
    c θ hlaunch b' J' h' hb' hT' hG').and ((hH₀ c θ hlaunch b' J' h' hb' hT' hG').and ((hK₀ c θ hlaunch b' J' h' hb'
    hT' hG').and ((hZ₀ c θ hlaunch b' J' h' hb' hT' hG').and ((hS₀ c θ hlaunch b' J' h' hb' hT' hG').and ((hD₀ c θ
    hlaunch b' J' h' hb' hT' hG').and ((hT₀ c θ hlaunch b' J' h' hb' hT' hG' m hm).and ((hSD₀ c θ hlaunch b' J' h' hb'
    hT' hG' m hm).and ((hRF₀ c θ hlaunch b' J' h' hb' hT' hG' m hm).and ((hS0A₀ c θ hlaunch b' J' h' hb' hT' hG').and
    ((hcor₀ c θ hlaunch b' J' h' hb' hT' hG').and ((hl0₀ c θ hlaunch b' J' h' hb' hT' hG').and ((hHC₀ c θ hlaunch b'
    J' h' hb' hT' hG')))))))))))))))))))))
  -- one sample of `S`, one relative family following the v6 rule: `sample_core6`
  have hcore : ∀ ω ∈ S, ∀ (D₂ : ℕ → Drv) (N : ℕ), (∀ i, IsRegularDriver (D₂ i)) →
      RootRule6 κ (-(Real.pi / 2)) b jumps (lR κ b jumps E u l k ω₀) c m (lD₁ b jumps E ω) D₂ →
      StageRule6 κ (-(Real.pi / 2)) b jumps (affData 1 m b') (affJumps 1 m J') c m (lD₁ b jumps E ω) D₂
        (relOff κ (-(Real.pi / 2)) b jumps (lR κ b jumps E u l k ω₀) (lD₁ b jumps E ω)) N →
      ∀ β₀ : ℝ≥0 → ℂ, IsProperCurve β₀ → β₀ 0 = 0 → range β₀ = lowerWalkSet κ b jumps E ω →
      ∀ (tL : ℝ≥0) (γ : ℝ≥0 → ℂ), IsTailLiftCurve c (lR κ b jumps E u l k ω₀) m β₀ tL γ →
      ((∀ j, 1 ≤ j → (ExplState.run κ (affData 1 m b') (affJumps 1 m J')
          (boundaryWalkSpec (affData 1 m b') (affJumps 1 m J') (-(Real.pi / 2)) true) D₂ (j + 1)).2.2.2.1 j = none) ∧
        ∀ i, 1 ≤ i → (ExplState.run κ b jumps (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) (lD₁ b jumps E ω)
          (i + relOff κ (-(Real.pi / 2)) b jumps (lR κ b jumps E u l k ω₀) (lD₁ b jumps E ω) + 1)).2.2.2.1
            (i + relOff κ (-(Real.pi / 2)) b jumps (lR κ b jumps E u l k ω₀) (lD₁ b jumps E ω)) = none) ∨
      ∀ M, 2 ≤ M → M ≤ N → JointQ6 κ (-(Real.pi / 2)) b jumps (affData 1 m b') (affJumps 1 m J')
        (lD₁ b jumps E ω) D₂ β₀ γ tL (relOff κ (-(Real.pi / 2)) b jumps (lR κ b jumps E u l k ω₀) (lD₁ b jumps E ω))
        c m N M := by
    intro ω hωS D₂ N hreg hroot hstage β₀ hβ hβ0 hβr tL γ hγ
    obtain ⟨hω, hleftω, hpinvω, -, hIω, hAω, hXω, hCω, hHω, hKω, hZω, hSω, hDω, -, hSDω, hRFω, hS0Aω, hcorω,
      hl0ω, -⟩ := hSp ω hωS
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
    -- the per-sample inputs
    have hhead := hHω β₀ hβ hβ0 hβr tL hγ.1
    have hhull : β₀ '' Icc 0 tL ⊆ hullK (pA '' Icc 0 1) := by rw [hpA']; exact hKω β₀ hβ hβ0 hβr tL hγ.1
    have hray := lift_eq_of_rayChartInj hγ hinjι
    have hD : LiftCurveData β₀ γ tL (lR κ b jumps E u l k ω₀) (lι κ b jumps E u l k ω₀ c) :=
      ⟨hβ.1, hβ.2.2.1, hγ.2.1.1, hγ.2.1.2.2.1, hγ.1, hγ.2.2.1,
        fun t ht him => hhead t ht _ (Complex.ext (by simp) (by simp [him])), hray, back_of_rayChartLim hγ hlim⟩
    have hS3 : ∀ tR : ℝ≥0, β₀ tR = ((lR κ b jumps E u l k ω₀ : ℝ) : ℂ) → ∀ s₁ s₂ : ℝ≥0, tR ≤ s₁ → s₁ < s₂ →
        ¬ β₀ '' Ioo s₁ s₂ ⊆ pA '' Icc 0 1 ∩ H := by
      rw [hpA']; exact hSω β₀ hβ hβ0 hβr
    have hS0A' := fun hZ hl he hL => hS0Aω β₀ hβ hβ0 hβr tL hγ.1 m hZ hl he hL
    have hcor' := fun hZ hl hL => hcorω β₀ hβ hβ0 hβr tL γ m hγ hZ hl hL
    -- the dense root readings give the stage-`0` facts of the family, hence its start data
    obtain ⟨hdense0, -, -, -, -⟩ := root_pkg (b₂ := affData 1 m b') (J₂ := affJumps 1 m J') hP₁ hU.2.1
      hcD'.1.isOpen_image (hreg 0) hroot.1 hroot.2 hRFω hl0ω hS0A' hcor' hγ hU hDom' hhull hβ hβr
    have hR0 : Root0At κ b jumps E u l k ω₀ c b' J' m (fun j _ => D₂ j) ω := by
      refine ⟨hreg, fun hz => ?_, fun hz => hroot.1 ((mem_cZ4_zero_iff _ _ _ _ _ _ _ _).1 hz)⟩
      have hnz : ¬ (ZeroRoot κ (-(Real.pi / 2)) b jumps (lR κ b jumps E u l k ω₀) (lD₁ b jumps E ω) ∨
          (lD₁ b jumps E ω (relOff κ (-(Real.pi / 2)) b jumps (lR κ b jumps E u l k ω₀) (lD₁ b jumps E ω))).2 -
            shiftD κ (-(Real.pi / 2)) b jumps (lR κ b jumps E u l k ω₀) (lD₁ b jumps E ω) 0 = 0) :=
        fun h => hz ((mem_cZ4_zero_iff _ _ _ _ _ _ _ _).2 h)
      push Not at hnz
      rw [lρ3_zero]
      exact hroot.2 hnz.1 hnz.2 (hdense0 hnz.1 hnz.2)
    have hS := hSDω (fun j _ => D₂ j) hR0 β₀ hβ hβ0 hβr tL γ hγ (lι κ b jumps E u l k ω₀ c) hι hlim hray
    exact sample_core6 hR' hP₁ hW₁ (fun j => (hn j).1) (fun j => (hn j).2.1) (fun k' hk' => hAω k' (by omega))
      (fun k' _ => hXω k') hCω hpinvω hp hp0 hpH hpv hcD' hcN hcbd hU hβ hβ0 hβr hS1 hS3 hγ hhull hhead hZω hray hD
      hι hcont (fun i hi hl => hDω β₀ hβ hβ0 hβr tL hγ.1 i hi hl) hRFω hl0ω hS0A' hcor' hS hreg hroot hstage
  have hGdm : MeasurableSet (G₀ ∩ S) := hG₀m.inter hSm
  have hGdae : ∀ᵐ ω ∂(condExpKernel P (pastSigma κ b jumps (upperSpec u l) (E (upperSpec u l)) k) ω₀),
      ω ∈ G₀ ∩ S := by
    have h0 : condExpKernel P (pastSigma κ b jumps (upperSpec u l) (E (upperSpec u l)) k) ω₀ (G₀ ∩ S)ᶜ = 0 := by
      rw [compl_inter]; exact measure_union_null hG₀n hS0
    exact mem_ae_iff.2 h0
  refine ⟨G₀ ∩ S, hGdm, inter_subset_left, ?_, ?_⟩
  · -- admissibility: drivenness on the mask for every family known before the stage
    intro j F _ hFr hFz hFg ω hωm
    have hωGd : ω ∈ G₀ ∩ S := hωm.1
    obtain ⟨-, -, -, hβω, hIω, -, -, -, -, -, -, -, -, hTω, -, hRFω, -, -, hl0ω, -⟩ := hSp ω hωGd.2
    have hnz : ω ∉ lZ4 κ b jumps E u l k ω₀ j F := hωm.2.1
    rcases Nat.lt_or_ge j 2 with hj2 | hj2
    · obtain rfl : j = 0 := by
        by_contra hj0
        exact hnz ((mem_cZ4_of_ne hj0 F ω).2 (Or.inl (by omega)))
      have hz' := (mem_cZ4_zero_iff _ _ _ _ _ _ F ω).not.1 hnz
      push Not at hz'
      rw [lρ3_zero]
      exact (hRFω hz'.1 (rootLife_ne_zero_of hz'.2) _ rfl).1
    · have hj0 : j ≠ 0 := by omega
      obtain ⟨β₀, hβ, hβ0, hβr⟩ := hβω
      obtain ⟨tL, γ, hγ⟩ := hTω β₀ hβ hβ0 hβr
      have hl := hωm.2.2.1
      have hpos : (lD₁ b jumps E ω (j + relOff κ (-(Real.pi / 2)) b jumps (lR κ b jumps E u l k ω₀)
          (lD₁ b jumps E ω))).2 ≠ 0 := fun h0 => hnz ((mem_cZ4_of_ne hj0 F ω).2 (Or.inr h0))
      rcases hcore ω hωGd.2 (truncDrv (fun i => F i ω) j) j (isRegularDriver_truncDrv fun i hi => hFr i hi ω)
          (rootRule6_truncDrv (by omega) (rootRule6_of_fam hωGd (hFz 0 (by omega) ω) (hFg 0 (by omega) ω) hl0ω))
          (stageRule6_truncDrv (stageRule6_of_fam hωGd fun i hi => hFg i hi ω)) β₀ hβ hβ0 hβr tL γ hγ with
        ⟨-, hno⟩ | hall
      · exact absurd (hno j (by omega)) hl
      · have hdr := (hall j hj2 le_rfl).2 hl hpos
        rw [run_truncDrv _ _ le_rfl] at hdr
        rw [lρ3_of_ne hj0]
        exact hdr
  · -- the per-stage facts of every admissible family
    intro EL _ hEr hEz hEg
    have hroot : ∀ ω ∈ G₀ ∩ S, RootRule6 κ (-(Real.pi / 2)) b jumps (lR κ b jumps E u l k ω₀) c m
        (lD₁ b jumps E ω) (fun i => EL i ω) := fun ω hω =>
      rootRule6_of_fam hω (hEz 0 ω) (hEg 0 ω) (hSp ω hω.2).2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
    have hstage : ∀ ω ∈ G₀ ∩ S, ∀ N, StageRule6 κ (-(Real.pi / 2)) b jumps (affData 1 m b') (affJumps 1 m J') c m
        (lD₁ b jumps E ω) (fun i => EL i ω)
        (relOff κ (-(Real.pi / 2)) b jumps (lR κ b jumps E u l k ω₀) (lD₁ b jumps E ω)) N :=
      fun ω hω _ => stageRule6_of_fam hω fun i _ => hEg i ω
    refine ⟨?_, ?_⟩
    · filter_upwards [hGdae] with ω hωGd
      intro β₀ hβ hβ0 hβr tL γ hγ
      obtain ⟨-, -, -, -, hIω, -, -, -, -, hKω, -, -, -, -, -, hRFω, hS0Aω, hcorω, hl0ω, -⟩ := hSp ω hωGd.2
      obtain ⟨hP₁, -, hn⟩ := hIω
      have hhull : β₀ '' Icc 0 tL ⊆ hullK (pA '' Icc 0 1) := by rw [hpA']; exact hKω β₀ hβ hβ0 hβr tL hγ.1
      obtain ⟨hdense0, -, -, -, hpkg⟩ := root_pkg (b₂ := affData 1 m b') (J₂ := affJumps 1 m J')
        (D₂ := fun i => EL i ω) hP₁ hU.2.1 hcD'.1.isOpen_image (hEr 0 ω) (hroot ω hωGd).1 (hroot ω hωGd).2 hRFω hl0ω
        (fun hZ hl he hL => hS0Aω β₀ hβ hβ0 hβr tL hγ.1 m hZ hl he hL)
        (fun hZ hl hL => hcorω β₀ hβ hβ0 hβr tL γ m hγ hZ hl hL) hγ hU hDom' hhull hβ hβr
      refine ⟨fun hZ hl => ⟨fun hL => ⟨⟨hωGd, fun h => ?_, (mem_launchEv_zero_iff ω).2 hl,
        fun i hi => absurd hi (Nat.not_lt_zero i), (mem_denseEv_zero_iff EL ω).2 (hdense0 hZ hL)⟩,
        (hpkg hZ hl).1 hL⟩, fun _ => (hpkg hZ hl).2⟩, ?_⟩
      · rcases (mem_cZ4_zero_iff _ _ _ _ _ _ EL ω).1 h with h' | h'
        · exact hZ h'
        · exact hL h'
      intro i hi2 _ hl _ _
      have hi0 : i ≠ 0 := by omega
      rcases hcore ω hωGd.2 (fun i => EL i ω) (i + 1) (fun i => hEr i ω) (hroot ω hωGd) (hstage ω hωGd (i + 1))
          β₀ hβ hβ0 hβr tL γ hγ with ⟨-, hno⟩ | hall
      · exact absurd (hno i (by omega)) hl
      · obtain ⟨hQ, hRD⟩ := (hall i hi2 (by omega)).1 (by omega)
        obtain ⟨hrg, hdn⟩ := hRD hl
        have hev : i % 2 = 0 := by
          have h1 := (GW1W.even_of_launches_walk hl).1
          have h2 := relOff_even κ (-(Real.pi / 2)) b jumps (lR κ b jumps E u l k ω₀) (lD₁ b jumps E ω)
          omega
        have hpos := (hn (i + relOff κ (-(Real.pi / 2)) b jumps (lR κ b jumps E u l k ω₀) (lD₁ b jumps E ω))).2.2
          (by omega) hl
        refine ⟨⟨hωGd, fun h => ?_, hl, hrg, (mem_denseEv_iff_of_ne hi0 EL ω).2 hdn⟩, (hQ.2.2.2 hl).2.1⟩
        rcases (mem_cZ4_of_ne hi0 EL ω).1 h with h' | h'
        · omega
        · exact hpos h'
    · filter_upwards [hGdae] with ω hωGd
      obtain ⟨-, -, -, hβω, hIω, -, -, -, -, hKω, -, -, hDω, hTω, -, hRFω, hS0Aω, hcorω, hl0ω, hHCω⟩ :=
        hSp ω hωGd.2
      obtain ⟨hP₁, -, -⟩ := hIω
      obtain ⟨β₀, hβ, hβ0, hβr⟩ := hβω
      obtain ⟨tL, γ, hγ⟩ := hTω β₀ hβ hβ0 hβr
      intro j hl₂ hpos₂
      have hnz : ω ∉ lZ4 κ b jumps E u l k ω₀ j EL := fun hz => hpos₂ (by
        beta_reduce; rw [hEz j ω (subset_mZ hz)]; rfl)
      rcases Nat.lt_or_ge j 2 with hj2 | hj2
      · obtain rfl : j = 0 := by
          by_contra hj0
          exact hnz ((mem_cZ4_of_ne hj0 EL ω).2 (Or.inl (by omega)))
        have hz' := (mem_cZ4_zero_iff _ _ _ _ _ _ EL ω).not.1 hnz
        push Not at hz'
        have hhull : β₀ '' Icc 0 tL ⊆ hullK (pA '' Icc 0 1) := by rw [hpA']; exact hKω β₀ hβ hβ0 hβr tL hγ.1
        obtain ⟨-, -, -, hRFA, -⟩ := root_pkg (b₂ := affData 1 m b') (J₂ := affJumps 1 m J')
          (D₂ := fun i => EL i ω) hP₁ hU.2.1 hcD'.1.isOpen_image (hEr 0 ω) (hroot ω hωGd).1 (hroot ω hωGd).2 hRFω hl0ω
          (fun hZ hl he hL => hS0Aω β₀ hβ hβ0 hβr tL hγ.1 m hZ hl he hL)
          (fun hZ hl hL => hcorω β₀ hβ hβ0 hβr tL γ m hγ hZ hl hL) hγ hU hDom' hhull hβ hβr
        simp only [zero_add]
        exact ⟨(hRFA.2.1 hz'.1 hz'.2).2, fun _ => hHCω hz'.1 fun h0 => hz'.2 (by rw [h0]; exact zero_tsub _)⟩
      · have hj0 : j ≠ 0 := by omega
        have hpos₁ : (lD₁ b jumps E ω (j + relOff κ (-(Real.pi / 2)) b jumps (lR κ b jumps E u l k ω₀)
            (lD₁ b jumps E ω))).2 ≠ 0 := fun h0 => hnz ((mem_cZ4_of_ne hj0 EL ω).2 (Or.inr h0))
        rcases hcore ω hωGd.2 (fun i => EL i ω) (j + 1) (fun i => hEr i ω) (hroot ω hωGd) (hstage ω hωGd (j + 1))
            β₀ hβ hβ0 hβr tL γ hγ with ⟨hno, -⟩ | hall
        · exact absurd (hno j (by omega)) hl₂
        · obtain ⟨hQ, hRD⟩ := (hall j hj2 (by omega)).1 (by omega)
          have hl₁ := hQ.2.2.1 hl₂
          obtain ⟨hrg, hdn⟩ := hRD hl₁
          obtain ⟨hdr, hrel, hpr⟩ := hQ.2.2.2 hl₁
          have hm : ω ∈ Nv.lMask κ b jumps E u l k ω₀ c b' J' m (G₀ ∩ S) j EL :=
            ⟨hωGd, hnz, hl₁, hrg, (mem_denseEv_iff_of_ne hj0 EL ω).2 hdn⟩
          obtain ⟨he, hg⟩ := hEg j ω hm
          rw [lρ3_of_ne hj0] at he hg
          rw [Mn.shiftD_of_ne hj0]
          exact ⟨stageFacts_of_act hdr hrel hpr he hg (hDω β₀ hβ hβ0 hβr tL hγ.1 j hj2 hl₁) hpos₁,
            fun h => absurd h hj0⟩

end InteractingSLE.Theorem14.SB.Lk
