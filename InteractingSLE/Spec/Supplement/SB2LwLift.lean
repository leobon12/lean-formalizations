/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.SB2LwSucc
import InteractingSLE.Spec.Supplement.SB4RLift

/-!
# SB2(2) with the pointwise lift on its own output (ruling R104a): the first launch

Packet PROVE-T14-SB2LOW. Ruling R104a: SB2(2)'s target is the combined existential "there is an output `(m, EL)`
satisfying SB2(2)'s clauses (`Lf.IsLowerLaunchOutput`, R99) whose completed lower tail has the injective, proper lift"
(the lift clause of `Lf.SB2LowerTailLiftStatement`, for that output). This file:

* `LiftOut`, **`SB2LowerLaunchLiftStatement`**: the combined target (in PROVE-T14-SB4LEAF's `Lf.SB2LowerSetting`);
  `sb2LowerLaunchEntryAdmStatement_of_lift`: it gives R99's form;
* `LowerWalkLeftFreeStatement` (named input): almost surely the completed lower walk misses some real point left of
  any given level (the walk's real points left of `0` are left records of simple pieces, which contain no interval);
* **`sb2LowerLaunchLift_zero`**: the combined target at the first launch `k = 0`, from Theorem 1.3 and that input:
  the output of `sb2LowerLaw_zero`'s construction (the relative walk is the regularized lower walk, whose physical set
  is the lower walk's almost surely), and the lift is the identity reparametrization (`t_L = 0`, `γ = β₀`; the
  recentred launch chart is the translation `z ↦ z + u`);
* `SB2LowerLaunchLiftSuccStatement` (named input: the combined target at the later launches) and
  **`sb2LowerLaunchLiftStatement_of_succ`**.

R48: Theorem 1.3 appears only as a hypothesis.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal
open QuantumZipper (chiC H)
open LQGMetric (DistOn)

universe u

namespace InteractingSLE.Theorem14.SB.Lh

open Exist Exist.StagedLaw Exist.Staged Restart FlowDilate Supp9B
open PiecewiseConstantBoundaryData (leftLim rightLim jumpSet)

/-- **SB2(2)'s combined output at one launch** (R104a): an output of SB2(2) whose completed lower tail lifts. -/
def LiftOut (κ : ℝ) (b : ℝ → ℝ) (jumps : Finset ℝ) {Ω : Type u} [MeasurableSpace Ω] [StandardBorelSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (E : ExplSpec → ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞) (u : ℝ)
    (l : List (ℝ × ℝ≥0)) (k : ℕ) (ω₀ : Ω) (c : Chart) (b' : ℝ → ℝ) (J' : Finset ℝ)
    (h' : Ω → DistOn upperHalfPlaneOpens) : Prop :=
  ∃ (m : ℝ) (EL : ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞), Lf.IsLowerLaunchOutput κ b jumps P E u l k ω₀ c b' J' h' m EL ∧
    ∀ᵐ ω ∂(condExpKernel P (pastSigma κ b jumps (Lu.upperSpec u l) (E (Lu.upperSpec u l)) k) ω₀),
      (∃ y : ℝ, y < 0 ∧ y < realMin (upperPrefix κ b jumps E u l k ω₀) ∧
          (y : ℂ) ∉ lowerWalkSet κ b jumps E ω) ∧
        ∀ β₀ : ℝ≥0 → ℂ, IsProperCurve β₀ → β₀ 0 = 0 → range β₀ = lowerWalkSet κ b jumps E ω →
          Lf.IsTailLiftOf c (realMax (upperPrefix κ b jumps E u l k ω₀)) m β₀
            (Leaf.relWalkSet κ (affData 1 m b') (affJumps 1 m J') EL ω)

/-- **SB2(2)'s target with the pointwise lift on its own output** (ruling R104a). -/
def SB2LowerLaunchLiftStatement : Prop :=
  Lf.SB2LowerSetting.{u} fun κ b jumps _ _ _ P _ E u l k ω₀ c b' J' h' => LiftOut κ b jumps P E u l k ω₀ c b' J' h'

/-- **The combined target at the later launches** (named input). -/
def SB2LowerLaunchLiftSuccStatement : Prop :=
  Lf.SB2LowerSetting.{u} fun κ b jumps _ _ _ P _ E u l k ω₀ c b' J' h' =>
    0 < k → LiftOut κ b jumps P E u l k ω₀ c b' J' h'

/-- **The combined target gives R99's form.** -/
theorem sb2LowerLaunchEntryAdmStatement_of_lift (h : SB2LowerLaunchLiftStatement.{u}) :
    Lz.SB2LowerLaunchEntryAdmStatement.{u} := by
  intro κ hκ hκ4 b jumps hb Ω _ _ P _ hf hh W' ζ' hcf hζ' E hE hER u l k hu hl hlθ hL hleft
  filter_upwards [h κ hκ hκ4 b jumps hb P hf hh W' ζ' hcf hζ' E hE hER u l k hu hl hlθ hL hleft] with ω₀ h₀
  intro c θ hcθ b' J' h' hb' hT' hG'
  obtain ⟨m, EL, ⟨hm, hlm, hent, hword, hst, hreg, hadd, hlink⟩, -⟩ := h₀ c θ hcθ b' J' h' hb' hT' hG'
  exact ⟨m, EL, hm, hlm, hent, hword, hst, hreg, hadd, hlink⟩

/-- **Named input: the completed lower walk leaves real points free far left.** In the setting of Theorem 1.4, for
every level `a`, almost surely some real point `y < a` is not on the completed lower walk. -/
def LowerWalkLeftFreeStatement : Prop :=
  ∀ κ : ℝ, 0 < κ → κ < 4 → ∀ (b : ℝ → ℝ) (jumps : Finset ℝ), IsPiecewiseConstantBoundaryData b jumps →
    ∀ {Ω : Type u} [MeasurableSpace Ω] [StandardBorelSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
      (h : Ω → DistOn upperHalfPlaneOpens), IsGFFWithBoundaryData P h b jumps →
    ∀ (W' : ℝ≥0 → Ω → ℝ) (ζ' : Ω → ℝ≥0∞), IsCenteredCounterflowDriver κ P h W' ζ' →
      (∀ᵐ ω ∂P, ζ' ω = ⊤) →
    ∀ E : ExplSpec → ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞,
      (∀ spec : ExplSpec, IsBoundaryContinuedProgram spec.2.2 →
        IsStagedHistory κ b jumps P h spec (E spec)) →
      (∀ spec : ExplSpec, IsBoundaryContinuedProgram spec.2.2 →
        StagedPiecesRegular κ b jumps P spec (E spec)) →
    ∀ a : ℝ, ∀ᵐ ω ∂P, ∃ y : ℝ, y < a ∧ (y : ℂ) ∉ lowerWalkSet κ b jumps E ω

/-- **SB2(2)'s combined target at the first launch** (`k = 0`; R104a). -/
theorem sb2LowerLaunchLift_zero (h13 : Exist.Theorem13Statement.{u}) (h130 : Exist.Theorem13Statement.{0})
    (hfree : LowerWalkLeftFreeStatement.{u}) {κ : ℝ} (hκ : 0 < κ) (hκ4 : κ < 4) {b : ℝ → ℝ} {jumps : Finset ℝ}
    (hb : IsPiecewiseConstantBoundaryData b jumps) {Ω : Type u} [MeasurableSpace Ω] [StandardBorelSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] {h : Ω → DistOn upperHalfPlaneOpens}
    (hh : IsGFFWithBoundaryData P h b jumps) {W' : ℝ≥0 → Ω → ℝ} {ζ' : Ω → ℝ≥0∞}
    (hcf : IsCenteredCounterflowDriver κ P h W' ζ') (hζ' : ∀ᵐ ω ∂P, ζ' ω = ⊤)
    {E : ExplSpec → ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞}
    (hE : ∀ spec : ExplSpec, IsBoundaryContinuedProgram spec.2.2 → IsStagedHistory κ b jumps P h spec (E spec))
    (hER : ∀ spec : ExplSpec, IsBoundaryContinuedProgram spec.2.2 → StagedPiecesRegular κ b jumps P spec (E spec))
    {x₀ : ℝ} {l : List (ℝ × ℝ≥0)} (hx₀ : x₀ ≤ 0) (hl : l.Pairwise (fun p q => p.2 < q.2))
    (hlθ : ∀ p ∈ l, p.1 ∈ Ioc (-(Real.pi / 2)) (Real.pi / 2))
    (hL : ∀ x ∈ Ioo x₀ 0, x ∉ jumps → -2 < Sec4.cumWeightLeft κ (b x + -(Real.pi / 2) * chiC κ))
    (hleft : ∀ᵐ ω ∂P, ω ∈ Lu.upperLaunchSet κ b jumps E x₀ l 0 →
      upperPrefix κ b jumps E x₀ l 0 ω ∩ rightSideOf (lowerWalkSet κ b jumps E ω) = ∅) :
    ∀ᵐ ω₀ ∂P, ∀ (c : Chart) (θ : ℝ),
      (ExplState.run κ b jumps (Lu.upperSpec x₀ l) (fun j => E (Lu.upperSpec x₀ l) j ω₀) (0 + 1)).2.2.2.1 0 =
          some (c, θ) →
      ∀ (b' : ℝ → ℝ) (J' : Finset ℝ) (h' : Ω → DistOn upperHalfPlaneOpens),
        IsPiecewiseConstantBoundaryData b' J' →
        (∀ ω, IsChartTransport c 1 0 (chiC κ) (h ω) (h' ω)) →
        IsGFFWithBoundaryData (condExpKernel P (pastSigma κ b jumps (Lu.upperSpec x₀ l) (E (Lu.upperSpec x₀ l)) 0) ω₀)
          h' b' J' →
        LiftOut κ b jumps P E x₀ l 0 ω₀ c b' J' h' := by
  have hGW0 : GW0.GW0ForwardStatement.{u} := BR3Ref.gw0ForwardStatement_of_theorem13 h130
  have hamb := (GW1Conn.ambient_bounds hGW0 hκ hκ4 hb hh hcf hζ').1
  set lw := boundaryWalkSpec b jumps (-(Real.pi / 2)) true with hlw
  have hlwp : IsBoundaryContinuedProgram lw.2.2 :=
    isBoundaryContinuedProgram_boundaryWalkSpec b jumps ⟨le_rfl, by linarith [Real.pi_pos]⟩ true
  have hsp : IsBoundaryContinuedProgram (Lu.upperSpec x₀ l).2.2 := Lu.isBoundaryContinuedProgram_upperSpec hlθ
  obtain ⟨hE', hreg', hrun⟩ := StagedReg.regFam_spec hb hE hER
  have hR' : StagedPiecesRegular κ b jumps P lw (StagedReg.regFam E lw) :=
    Exist.StagedLaw.stagedPiecesRegular_of_regular h13 hκ hb (hE' lw hlwp) (hreg' lw)
  have hWRA : ∀ᵐ ω ∂P, Lx.WalkRightAdds κ b jumps (StagedReg.regFam E) ω :=
    Ly.ae_walkRightAdds_of_bound h13 hκ hb hh (hE' lw hlwp) (hreg' lw) hamb
  filter_upwards [sb2LowerWordAdmStatement_of_theorem13 h130 κ hκ hκ4 b jumps hb P h hh W' ζ' hcf hζ' E hE hER x₀ l 0
    hx₀ hl hlθ hL hleft, Lu.ae_isRightEntryValue_upperEntry (hER _ hsp) 0] with ω₀ hw₀ hent₀
  intro c θ hcθ b' J' h' hb' hT' hG'
  obtain ⟨hadm, hact⟩ := hw₀ c θ hcθ b' J' h' hb' hT' hG' _ rfl
  have hent := hent₀ (Lu.mem_upperLaunchSet hcθ)
  rw [Lu.upperLaunchChart_eq hcθ] at hent
  rw [Lv.condExpKernel_pastSigma_zero] at hG'
  -- the launch chart is the translation to the upper seed
  obtain ⟨-, -, hc⟩ := eq_launch_of_launches _ _ hcθ
  have hc0 : c = Chart.id.recenter x₀ := hc
  have hLc := Lu.upperLaunchChart_eq hcθ
  subst hc0
  have hconf : (Chart.id.recenter x₀).IsConformal := Chart.isConformal_id.recenter x₀
  -- the entry point: `R = 0`, `e_R = −x₀`, so `m = x₀`
  have hpre : ∀ y : ℝ, (y : ℂ) ∈ upperPrefix κ b jumps E x₀ l 0 ω₀ → y ≤ 0 := by
    intro y hy
    rcases hy with hy | ⟨z, hz, hzy⟩
    · have hr0 : ExplState.run κ b jumps (Lu.upperSpec x₀ l) (fun j => E (Lu.upperSpec x₀ l) j ω₀) 0 =
          ExplState.init x₀ := rfl
      change (y : ℂ) ∈ SB.prefixPhysSet κ b jumps (Lu.upperSpec x₀ l) (fun j => E (Lu.upperSpec x₀ l) j ω₀) 0 at hy
      simp only [SB.prefixPhysSet, hr0, ExplState.init, List.not_mem_nil, iUnion_of_empty, iUnion_empty,
        union_empty, mem_singleton_iff] at hy
      have : y = x₀ := by exact_mod_cast hy
      rw [this]
      exact hx₀
    · have : z = y := by exact_mod_cast hzy
      rw [← this]
      exact hz.2
  have h0 : ((0 : ℝ) : ℂ) ∈ upperPrefix κ b jumps E x₀ l 0 ω₀ := Or.inr ⟨0, ⟨hx₀, le_rfl⟩, rfl⟩
  have hR0 : realMax (upperPrefix κ b jumps E x₀ l 0 ω₀) = 0 :=
    le_antisymm (csSup_le ⟨0, h0⟩ hpre) (le_csSup ⟨0, hpre⟩ h0)
  have hbv : Lx.bdryValue (Chart.id.recenter x₀) = fun x => x - x₀ := by
    funext x
    have ht : Tendsto (Chart.id.recenter x₀).1 (𝓝[H] (x : ℂ)) (𝓝 ((x : ℂ) - x₀)) := by
      change Tendsto (fun z : ℂ => z - x₀) (𝓝[H] (x : ℂ)) (𝓝 ((x : ℂ) - x₀))
      exact ((continuous_id.sub continuous_const).tendsto _).mono_left nhdsWithin_le_nhds
    have := (Lx.tendsto_bdryValue ht (by simp)).1
    rw [this]
    simp
  have he : Lu.upperEntry κ b jumps E x₀ l 0 ω₀ = -x₀ := by
    unfold Lu.upperEntry Lx.rightEntry
    rw [hLc, hR0, hbv]
    have : Tendsto (fun x : ℝ => x - x₀) (𝓝[>] 0) (𝓝 (0 - x₀)) :=
      ((continuous_id.sub continuous_const).tendsto _).mono_left nhdsWithin_le_nhds
    rw [this.limUnder_eq, zero_sub]
  -- the field: `h(· + x₀)`, read back in the frame `affField x₀`
  have hh' : ∀ ω, h' ω = BR4aPath.recField x₀ (h ω) := fun ω =>
    (hT' ω).unique hconf (BR4aPath.isChartTransport_recField (chiC κ) x₀ (h ω))
  have hfield : (fun ω => affField x₀ one_pos (h' ω)) = h := by
    funext ω
    rw [hh' ω]
    exact Lv.affField_one_flowField x₀ (h ω)
  -- the data: `b(· + x₀)` off a finite set
  have hbs : IsPiecewiseConstantBoundaryData (fun y => b (y + x₀)) (jumps.image (· - x₀)) := by
    intro y hy
    have hy' : y + x₀ ∉ jumps := fun hJ => hy (Finset.mem_image.2 ⟨y + x₀, hJ, by ring⟩)
    have hcm : Continuous fun z : ℝ => z + x₀ := continuous_id.add continuous_const
    exact (hcm.tendsto y).eventually (hb (y + x₀) hy')
  have hG2 : IsGFFWithBoundaryData P h' (fun y => b (y + x₀)) (jumps.image (· - x₀)) := by
    rw [show h' = fun ω => Exist.flowField x₀ 0 (h ω) from funext hh']
    exact Supp9.IsGFFWithBoundaryData.recenter hb x₀ hh
  have hagree := Exist.StagedLaw.eq_of_isGFFWithBoundaryData hb' hbs hG' hG2
  set F : Finset ℝ := (J' ∪ jumps.image (· - x₀)).image (· + x₀) with hF
  have hdat : ∀ y ∉ F, affData 1 x₀ b' y = b y := by
    intro y hy
    have hy' : y - x₀ ∉ J' ∪ jumps.image (· - x₀) := fun h1 => hy (Finset.mem_image.2 ⟨y - x₀, h1, by ring⟩)
    simp only [affData, div_one]
    rw [hagree _ hy', sub_add_cancel]
  have hL : leftLim (affData 1 x₀ b') = leftLim b := Restart.leftLim_congr hdat
  have hR : rightLim (affData 1 x₀ b') = rightLim b := Restart.rightLim_congr hdat
  have hS : jumpSet (affData 1 x₀ b') (affJumps 1 x₀ J') = jumpSet b jumps :=
    GW1.jumpSet_eq_of_lims (isPiecewiseConstantBoundaryData_affData one_pos hb') hb hL hR
  have hrunc := run_congr_data (κ := κ) hL hR hS
  have hspec : Lu.relLowerSpec b' J' x₀ = lw := by
    unfold Lu.relLowerSpec
    exact boundaryWalkSpec_congr hS _ _
  rw [he, neg_neg] at hadm hact
  rw [he] at hent
  unfold LiftOut Lf.IsLowerLaunchOutput
  simp only [Lv.condExpKernel_pastSigma_zero]
  have hbws : boundaryWalkSpec (affData 1 x₀ b') (affJumps 1 x₀ J') (-(Real.pi / 2)) true = lw :=
    boundaryWalkSpec_congr hS _ _
  have hwalk : ∀ ω, (∀ n, ExplState.run κ b jumps lw (fun j => StagedReg.regFam E lw j ω) n =
      ExplState.run κ b jumps lw (fun j => E lw j ω) n) →
      Leaf.relWalkSet κ (affData 1 x₀ b') (affJumps 1 x₀ J') (StagedReg.regFam E lw) ω =
        lowerWalkSet κ b jumps E ω := by
    intro ω hrω
    unfold Leaf.relWalkSet lowerWalkSet ExplState.physSet
    rw [hbws, run_eq_data hrunc, hrω]
  -- the smallest real point of the upper prefix is the upper seed
  have hpreL : ∀ y : ℝ, (y : ℂ) ∈ upperPrefix κ b jumps E x₀ l 0 ω₀ → x₀ ≤ y := by
    intro y hy
    rcases hy with hy | ⟨z, hz, hzy⟩
    · have hr0 : ExplState.run κ b jumps (Lu.upperSpec x₀ l) (fun j => E (Lu.upperSpec x₀ l) j ω₀) 0 =
          ExplState.init x₀ := rfl
      change (y : ℂ) ∈ SB.prefixPhysSet κ b jumps (Lu.upperSpec x₀ l) (fun j => E (Lu.upperSpec x₀ l) j ω₀) 0 at hy
      simp only [SB.prefixPhysSet, hr0, ExplState.init, List.not_mem_nil, iUnion_of_empty, iUnion_empty,
        union_empty, mem_singleton_iff] at hy
      have : y = x₀ := by exact_mod_cast hy
      rw [this]
    · have : z = y := by exact_mod_cast hzy
      rw [← this]
      exact hz.1
  have hmin : x₀ ≤ realMin (upperPrefix κ b jumps E x₀ l 0 ω₀) := le_csInf ⟨0, h0⟩ hpreL
  refine ⟨x₀, StagedReg.regFam E lw, ⟨hx₀, hadm, hent, hact, ?_, ?_, ?_, ?_⟩, ?_⟩
  · rw [hspec, hfield, isStagedHistory_congr_data hrunc]
    exact hE' lw hlwp
  · rw [hspec, stagedPiecesRegular_congr_data hrunc]
    exact hR'
  · filter_upwards [hWRA] with ω hω
    unfold Lx.WalkRightAdds Lx.LowerLaunch lowerWalkState at hω ⊢
    rw [hbws, run_eq_data hrunc]
    simp only [prefixPhysSet_congr_data hrunc]
    exact hω
  · filter_upwards [hrun lw hlwp] with ω hrω
    have hid : ∀ z, ((Chart.id.recenter x₀).recenter (-x₀)).2.1 z = z := fun z => by
      change z + ((-x₀ : ℝ) : ℂ) + (x₀ : ℂ) = z
      push_cast
      ring
    have hset : relPhysSet κ (affData 1 x₀ b') (affJumps 1 x₀ J') ((Chart.id.recenter x₀).recenter (-x₀))
        (Lu.relLowerSpec b' J' x₀) (fun j => StagedReg.regFam E lw j ω) = lowerWalkSet κ b jumps E ω := by
      rw [relPhysSet_of_id hid, hspec]
      unfold ExplState.physSet lowerWalkSet ExplState.physSet
      rw [run_eq_data hrunc, hrω]
    rw [hset]
    exact ⟨inter_subset_left, subset_rfl⟩
  · filter_upwards [hrun lw hlwp, hfree κ hκ hκ4 b jumps hb P h hh W' ζ' hcf hζ' E hE hER (min x₀ 0)]
      with ω hrω hfr
    obtain ⟨y, hy, hyB⟩ := hfr
    refine ⟨⟨y, lt_of_lt_of_le hy (min_le_right _ _), lt_of_lt_of_le (lt_of_lt_of_le hy (min_le_left _ _)) hmin,
      hyB⟩, fun β₀ hβ hβ0 hrange => ?_⟩
    rw [hR0]
    refine ⟨0, β₀, by rw [hβ0]; simp, hβ, hβ0, by rw [hrange, hwalk ω hrω], fun s => ?_⟩
    change Tendsto (fun z : ℂ => z + (x₀ : ℂ)) (𝓝[H] (β₀ s - (x₀ : ℂ))) (𝓝 (β₀ (0 + s)))
    rw [zero_add]
    have hc : Continuous fun z : ℂ => z + (x₀ : ℂ) := continuous_id.add continuous_const
    have := (hc.tendsto (β₀ s - (x₀ : ℂ))).mono_left (nhdsWithin_le_nhds (s := H))
    simpa using this

/-- **SB2(2)'s combined target (R104a) from its later launches**, Theorem 1.3 and the left-free input. -/
theorem sb2LowerLaunchLiftStatement_of_succ (h13 : Exist.Theorem13Statement.{u})
    (h130 : Exist.Theorem13Statement.{0}) (hfree : LowerWalkLeftFreeStatement.{u})
    (hs : SB2LowerLaunchLiftSuccStatement.{u}) : SB2LowerLaunchLiftStatement.{u} := by
  intro κ hκ hκ4 b jumps hb Ω _ _ P _ h hh W' ζ' hcf hζ' E hE hER x₀ l k hx₀ hl hlθ hL hleft
  cases k with
  | zero => exact sb2LowerLaunchLift_zero h13 h130 hfree hκ hκ4 hb hh hcf hζ' hE hER hx₀ hl hlθ hL hleft
  | succ k =>
    filter_upwards [hs κ hκ hκ4 b jumps hb P h hh W' ζ' hcf hζ' E hE hER x₀ l (k + 1) hx₀ hl hlθ hL hleft]
      with ω₀ h₀
    intro c θ hcθ b' J' h' hb' hT' hG'
    exact h₀ c θ hcθ b' J' h' hb' hT' hG' (Nat.succ_pos k)

end InteractingSLE.Theorem14.SB.Lh
