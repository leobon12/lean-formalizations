/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec5.WordSafePort3

/-!
# The pocket word from a two-angle strip system, with no driver-regularity input

Packet PROVE-WORDSAFE. The pocket-word consumers (`WordSafe.pocketWordEvolution_of_stripSystem_restartGen`,
`WordSafe.pocketChartFieldStatement_of_stripSystem_restartGen`, ports of PROVE-RESTART-GEN's and PROVE-STRIPMARKS'
assemblies to `IsTwoAngleStripSystem`) still ask the three experiment drivers `α`, `β^{(q)}` and `β = η_{π/2}` to be
regular at every sample (`hr`, `hl`, `he`). Ruling R51: that cannot be read off the conditional laws. Here these
inputs are removed by regularizing the family, as PROVE-SWITCHED does for one two-angle wall:

* **`regTwo`**: every two-angle history is replaced by its regularization `Theorem14.StagedReg.regHist` (a staged
  history again with no regularity input, `RestartSw.isStagedHistory_regHist_twoAngle`); every other program is
  treated as in `StripWall.regStrip`;
* **`isTwoAngle_regTwo`**: the regularized family is a two-angle strip system;
* **`isWallVersion_regTwo`**: a wall version of a two-angle history is a wall version of its regularization
  (`RestartSw.ae_wall_eq_of_regHist`);
* **`pocketWordEvolution_of_twoAngle_restartGen`**, **`pocketChartFieldStatement_of_twoAngle_restartGen`**: the two
  consumers for a two-angle strip system, without `hr`, `hl`, `he` (every other binder unchanged).

R48: nothing here uses Theorem 1.2/1.3, `Theorem12ParamStatement`, `Theorem13Statement` or any `*_of_param`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology Function
open scoped NNReal ENNReal Real

universe u

namespace InteractingSLE.Sec7.WordSafe

open QuantumZipper (H Hbar chiC)
open LQGMetric (DistOn TestOn)
open SupercriticalConformalCovariance.GM24 (smoothDist)
open R7Aux131 (constSpec)
open Exist.Staged (IsRegularDriver)
open Theorem14.StagedReg (regHist isRegularDriver_regHist regHist_snd)
open StripWall StripSideHeightProb StripPocketPath WangWu WholeField
open Lemma71I PocketCoord PocketJordan PocketMarks PocketSeedOpen PocketCoupling PocketWordAssembly
open PocketLeftFrontier PocketWordPerQ Aux119Nested LocalSets StripPocketConfig PocketWordIn

/-! ### The regularized family -/

/-- The two-angle programs `η^{t₀,∞}_{θ₀,θ}`. -/
def IsTwoAngleProgram (spec : ExplSpec) : Prop :=
  ∃ (θ₀ : ℝ) (t₀ : ℝ≥0) (θ : ℝ), spec = StripSys.twoAngleSpec θ₀ t₀ θ

theorem isTwoAngleProgram_twoAngleSpec (θ₀ : ℝ) (t₀ : ℝ≥0) (θ : ℝ) :
    IsTwoAngleProgram (StripSys.twoAngleSpec θ₀ t₀ θ) :=
  ⟨θ₀, t₀, θ, rfl⟩

/-- A constant-angle program has one instruction, a two-angle program two. -/
theorem not_isTwoAngleProgram_constSpec (θ : ℝ) : ¬ IsTwoAngleProgram (constSpec θ) := by
  rintro ⟨θ₀, t₀, θ', hθ⟩
  have hl := congrArg (fun s : ExplSpec => s.2.2.length) hθ
  simp only [constSpec, StripSys.twoAngleSpec, StripSys.twoAngleProg, List.length_cons, List.length_nil] at hl
  omega

section Reg

variable {κ : ℝ} {b : ℝ → ℝ} {J : Finset ℝ} {Ω : Type u} [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω]
  {P : Measure Ω} [IsProbabilityMeasure P] {h : Ω → DistOn upperHalfPlaneOpens} {W' : ℝ≥0 → Ω → ℝ}
  {ζ' : Ω → ℝ≥0∞} {E : ExplSpec → ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞}

omit [StandardBorelSpace Ω] [IsProbabilityMeasure P] in
open Classical in
/-- **The regularized family**: every two-angle history is replaced by its regularization; every other program as in
`StripWall.regStrip` (regularized when it is `StagedPiecesRegular`, kept otherwise). -/
def regTwo (κ : ℝ) (b : ℝ → ℝ) (J : Finset ℝ) (P : Measure Ω) (E : ExplSpec → ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞) :
    ExplSpec → ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞ :=
  fun spec => if IsTwoAngleProgram spec then regHist spec (E spec) else StripWall.regStrip κ b J P E spec

omit [StandardBorelSpace Ω] [IsProbabilityMeasure P] in
theorem regTwo_twoAngle (θ₀ : ℝ) (t₀ : ℝ≥0) (θ : ℝ) :
    regTwo κ b J P E (StripSys.twoAngleSpec θ₀ t₀ θ) =
      regHist (StripSys.twoAngleSpec θ₀ t₀ θ) (E (StripSys.twoAngleSpec θ₀ t₀ θ)) := by
  unfold regTwo
  rw [ite_eq_left (isTwoAngleProgram_twoAngleSpec θ₀ t₀ θ)]

omit [StandardBorelSpace Ω] [IsProbabilityMeasure P] in
theorem regTwo_const (θ : ℝ) : regTwo κ b J P E (constSpec θ) = StripWall.regStrip κ b J P E (constSpec θ) := by
  unfold regTwo
  rw [ite_eq_right (not_isTwoAngleProgram_constSpec θ)]

omit [StandardBorelSpace Ω] [IsProbabilityMeasure P] in
/-- Every driver of a two-angle history of the regularized family is regular at every sample. -/
theorem isRegularDriver_regTwo_twoAngle (θ₀ : ℝ) (t₀ : ℝ≥0) (θ : ℝ) (j : ℕ) (ω : Ω) :
    IsRegularDriver (regTwo κ b J P E (StripSys.twoAngleSpec θ₀ t₀ θ) j ω) := by
  rw [regTwo_twoAngle]
  exact isRegularDriver_regHist j ω

/-- The strip heights at the first angle `θ₀`, in the form of PROVE-SWITCHED's regularization lemmas. -/
theorem heights_first (hκ : 0 < κ) (hκ4 : κ < 4)
    (hleft : ∀ a ∈ Icc (-(π / 2)) (π / 2), ∀ y : ℝ, y < 0 → y ∉ J → b y + a * chiC κ ≤ -sleLambda κ)
    (hright : ∀ a ∈ Icc (-(π / 2)) (π / 2), ∀ y : ℝ, 0 < y → y ∉ J → sleLambda κ ≤ b y + a * chiC κ)
    {θ₀ : ℝ} (hθ₀ : θ₀ ∈ Icc (-(π / 2)) (π / 2)) :
    (∀ y : ℝ, y < 0 → y ∉ J → b y + θ₀ * chiC κ ≤ -sleLambda κ + Real.pi * chiC κ) ∧
      ∀ y : ℝ, 0 < y → y ∉ J → sleLambda κ ≤ b y + θ₀ * chiC κ := by
  have hπχ : 0 < Real.pi * chiC κ := mul_pos Real.pi_pos (Sec4.chiC_pos hκ hκ4)
  refine ⟨fun y hy hyJ => ?_, hright θ₀ hθ₀⟩
  have := hleft θ₀ hθ₀ y hy hyJ
  linarith

/-- **The regularized family of a two-angle strip system is a two-angle strip system** (with Aux. 130's heights; no
regularity input: PROVE-SWITCHED's `isStagedHistory_regHist_twoAngle` for the two-angle programs). -/
theorem isTwoAngle_regTwo (hS : IsTwoAngleStripSystem κ b J P h W' ζ' E)
    (hleft : ∀ a ∈ Icc (-(π / 2)) (π / 2), ∀ y : ℝ, y < 0 → y ∉ J → b y + a * chiC κ ≤ -sleLambda κ)
    (hright : ∀ a ∈ Icc (-(π / 2)) (π / 2), ∀ y : ℝ, 0 < y → y ∉ J → sleLambda κ ≤ b y + a * chiC κ) :
    IsTwoAngleStripSystem κ b J P h W' ζ' (regTwo κ b J P E) := by
  refine ⟨hS.kappa_pos, hS.kappa_lt_four, hS.boundaryData, hS.gff, hS.counterflow, hS.lifetime,
    fun θ hθ => ?_, fun {θ₀ θ} hθ₀ hθ t₀ => ?_⟩
  · rw [regTwo_const]
    exact isStagedHistory_regStrip hS.boundaryData (hS.staged θ hθ)
  · rw [regTwo_twoAngle]
    obtain ⟨hL0, hR0⟩ := heights_first hS.kappa_pos hS.kappa_lt_four hleft hright hθ₀
    exact Sec5.RestartSw.isStagedHistory_regHist_twoAngle hS.kappa_pos hS.kappa_lt_four hS.boundaryData hS.gff
      (hS.stagedTwoAngle hθ₀ hθ t₀) hL0 hR0

/-- **A wall version of a two-angle history is a wall version of its regularization** (the argument of PROVE-SWITCHED's
`switchedWallFirstHitStatement_of_input`: a wall version `γ` of the regularized history exists, the second lifetime is
almost surely infinite, and `RestartSw.ae_wall_eq_of_regHist` identifies the two walls almost surely). -/
theorem isWallVersion_regTwo (hS : IsTwoAngleStripSystem κ b J P h W' ζ' E)
    (hleft : ∀ a ∈ Icc (-(π / 2)) (π / 2), ∀ y : ℝ, y < 0 → y ∉ J → b y + a * chiC κ ≤ -sleLambda κ)
    (hright : ∀ a ∈ Icc (-(π / 2)) (π / 2), ∀ y : ℝ, 0 < y → y ∉ J → sleLambda κ ≤ b y + a * chiC κ)
    {θ₀ θ : ℝ} (hθ₀ : θ₀ ∈ Icc (-(π / 2)) (π / 2)) (hθ : θ ∈ Icc (-(π / 2)) (π / 2)) {t₀ : ℝ≥0}
    {R : Ω → ℝ≥0 → ℂ} (hR : IsWallVersion P (E (StripSys.twoAngleSpec θ₀ t₀ θ)) t₀ R) :
    IsWallVersion P (regTwo κ b J P E (StripSys.twoAngleSpec θ₀ t₀ θ)) t₀ R := by
  have hκ := hS.kappa_pos
  have hκ4 := hS.kappa_lt_four
  have hb := hS.boundaryData
  have hh := hS.gff
  obtain ⟨hL0, hR0⟩ := heights_first hκ hκ4 hleft hright hθ₀
  have hL : ∀ y : ℝ, y < 0 → y ∉ J → b y + θ * chiC κ ≤ -sleLambda κ + Real.pi * chiC κ :=
    (heights_first hκ hκ4 hleft hright hθ).1
  have hπχ : 0 < Real.pi * chiC κ := mul_pos Real.pi_pos (Sec4.chiC_pos hκ hκ4)
  have hRθ : ∀ y : ℝ, 0 < y → y ∉ J → sleLambda κ - Real.pi * chiC κ ≤ b y + θ * chiC κ := fun y hy hyJ => by
    have := hright θ hθ y hy hyJ
    linarith
  have hθπ : θ ≤ θ₀ + Real.pi := by linarith [hθ.2, hθ₀.1, Real.pi_pos]
  have hθπ' : θ₀ ≤ θ + Real.pi := by linarith [hθ₀.2, hθ.1, Real.pi_pos]
  have hE := hS.stagedTwoAngle hθ₀ hθ t₀
  have hE' := Sec5.RestartSw.isStagedHistory_regHist_twoAngle hκ hκ4 hb hh hE hL0 hR0
  have hreg' : ∀ j ω, IsRegularDriver (regHist (StripSys.twoAngleSpec θ₀ t₀ θ)
      (E (StripSys.twoAngleSpec θ₀ t₀ θ)) j ω) := fun j ω => isRegularDriver_regHist j ω
  obtain ⟨γ, hγ, -⟩ := StripWall.exists_isWallVersion_twoAngle hκ hκ4 hb hh hE' hreg' hL0 hR0 hL hRθ hθπ hθπ'
  have hz1 : ∀ᵐ ω ∂P, (E (StripSys.twoAngleSpec θ₀ t₀ θ) 1 ω).2 = ⊤ :=
    (StripWall.ae_goodPath_one hκ hκ4 hb hh hE' hreg' hL0 hR0 hL hRθ hθπ hθπ').mono fun ω hω =>
      (regHist_snd 1 ω).symm.trans (StripWall.mem_goodPathSet.1 hω).1
  have hRγ := Sec5.RestartSw.ae_wall_eq_of_regHist hκ hκ4 hb hh hE hL0 hR0 hz1 hR hγ
  rw [regTwo_twoAngle]
  exact ⟨hR.continuous, hR.zero, hR.measurable, by
    filter_upwards [hγ.ae_trace, hRγ] with ω h1 h2
    rw [h2]
    exact h1⟩

/-- **The unchanged extremal path of the regularized family**: regular at every sample, with almost surely the original
driver (it is the stage-`0` flow line of `h`, `WordSafe.regStrip_leftExtremal`). -/
theorem regTwo_leftExtremal (hS : IsTwoAngleStripSystem κ b J P h W' ζ' E)
    (hleft : ∀ a ∈ Icc (-(π / 2)) (π / 2), ∀ y : ℝ, y < 0 → y ∉ J → b y + a * chiC κ ≤ -sleLambda κ)
    (hright : ∀ a ∈ Icc (-(π / 2)) (π / 2), ∀ y : ℝ, 0 < y → y ∉ J → sleLambda κ ≤ b y + a * chiC κ) :
    (∀ ω, IsRegularDriver (regTwo κ b J P E StripSys.leftExtremalSpec 0 ω)) ∧
      ∀ᵐ ω ∂P, (regTwo κ b J P E StripSys.leftExtremalSpec 0 ω).1 = (E StripSys.leftExtremalSpec 0 ω).1 := by
  have e : regTwo κ b J P E StripSys.leftExtremalSpec = StripWall.regStrip κ b J P E StripSys.leftExtremalSpec :=
    regTwo_const (π / 2)
  rw [e]
  exact WordSafe.regStrip_leftExtremal hS hleft hright

end Reg

/-! ### The consumers without driver regularity -/

section Consumers

/-- **The conditional pocket word from a two-angle strip system** (Aux. 130, pp. 410–412):
`WordSafe.pocketWordEvolution_of_stripSystem_restartGen` without the three driver-regularity inputs `hr`, `hl`, `he`.
The family is replaced by its regularization `regTwo` (a two-angle strip system with the same field and counterflow,
regular at every sample on the three walls, of which the given walls are again versions). -/
theorem pocketWordEvolution_of_twoAngle_restartGen
    {κ rL rR : ℝ} {b : ℝ → ℝ} {J : Finset ℝ} {Ω : Type u}
    [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {h : Ω → DistOn upperHalfPlaneOpens} {W : ℝ≥0 → Ω → ℝ} {ζ : Ω → ℝ≥0∞}
    {E : ExplSpec → ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞}
    (h44 : AdmCode.Theorem12ParamCond44Statement.{u})
    (haux7 : Sec4.Aux7Statement.{u} (16 / κ))
    (h411 : Sec5.Cond44Ref.Prop411QStatement.{u})
    (h47 : Sec5.Prop411Q.Lemma47QHitStatement.{u})
    (hsw : WordSafe.SwitchedWallFirstHitStatement.{u})
    (hS : IsTwoAngleStripSystem κ b J P h W ζ E)
    (hleft : ∀ a ∈ Icc (-(π / 2)) (π / 2), ∀ y : ℝ, y < 0 → y ∉ J →
      b y + a * chiC κ ≤ -sleLambda κ)
    (hright : ∀ a ∈ Icc (-(π / 2)) (π / 2), ∀ y : ℝ, 0 < y → y ∉ J →
      sleLambda κ ≤ b y + a * chiC κ)
    {θ₁ θ₂ : ℝ} (hθ₁ : θ₁ ∈ Ioo (-(π / 2)) (π / 2))
    (hθ₂ : θ₂ ∈ Ioc (-(π / 2)) (π / 2))
    (hL : -2 < rL) (hLd : rL < 16 / κ / 2 - 4)
    (hR : -2 < rR) (hRd : rR < 16 / κ / 2 - 4)
    {u₀ : ℂ → ℝ} (hu₀ : IsBoundedHarmonicExtension b J u₀)
    {α β : Ω → ℝ≥0 → ℂ} {Lr : ℚ → Ω → ℝ≥0 → ℂ} {η : Ω → ℝ → ℂ}
    (hvα : IsWallVersion P (E (StripSys.alphaSpec θ₁)) 1 α)
    (hvL : ∀ q, IsWallVersion P (E (StripSys.betaSpec (StripSys.rt (positiveSeed q)) θ₂))
      (StripSys.rt (positiveSeed q)) (Lr q))
    (hβc : ∀ ω, Continuous (β ω)) (hβ0 : ∀ ω, β ω 0 = 0)
    (hβm : ∀ t, Measurable fun ω => β ω t)
    (hβtr : ∀ᵐ ω ∂P, IsGeneratingTrace (E StripSys.leftExtremalSpec 0 ω).1 ⊤ (β ω))
    (hηc : ∀ ω, ContinuousOn (η ω) (Ici 0))
    (hηH : ∀ ω, ∀ t : ℝ, 0 ≤ t → η ω t ∈ Hbar) (hη0 : ∀ ω, η ω 0 = 0)
    (hηm : ∀ t : ℝ, 0 ≤ t → Measurable fun ω => η ω t)
    (hηtr : ∀ᵐ ω ∂P, IsGeneratingTrace (fun t => W t ω) ⊤ (fun t : ℝ≥0 => η ω t))
    (𝔥 : DistOn upperHalfPlaneOpens) {u : ℂ → ℝ}
    (hu : InnerProductSpace.HarmonicOnNhd u H) (hub : ∃ M : ℝ, ∀ z ∈ H, |u z| ≤ M)
    (h𝔥 : ∀ φ : TestOn upperHalfPlaneOpens, 𝔥 φ = ∫ z, u z * φ z)
    (hside : ∀ q : ℚ, 0 < q → ∀ G : Set Ω,
      MeasurableSet[wallsSigma P α (Lr q)] G → 0 < P G →
      (∀ ω ∈ G, IsChangeConfigInc (α ω) (Lr q ω) (StripSys.rt q) ∧
        discTime 1 < rightHi (α ω) (Lr q ω) (StripSys.rt q)) →
      (∀ ω ∈ G, ζ ω = ⊤) →
      (∀ ω ∈ G, 0 < rightLo (α ω) (Lr q ω) (StripSys.rt q) →
        IsCfPocketConfig (α ω) (Lr q ω) (StripSys.rt q)
          (fun s : ℝ => W s.toNNReal ω) (η ω)) →
      (∀ ω ∈ G, rightLo (α ω) (Lr q ω) (StripSys.rt q) = 0 →
        IsCfPocketConfigInf (α ω) (Lr q ω) (StripSys.rt q)
          (fun s : ℝ => W s.toNNReal ω) (η ω)) →
      let d := counterflowObjects hS.counterflow
      PocketSideLimitInput0 (16 / (16 / κ)) rL rR (wallsSigma P α (Lr q)) P α (Lr q)
        (StripSys.rt q) η {ω | ω ∈ G ∧ 0 < rightLo (α ω) (Lr q ω) (StripSys.rt q)}
        (centredField d.field d.mean) u ∧
      PocketSideLimitInputInf0 (16 / (16 / κ)) rL rR (wallsSigma P α (Lr q)) P α (Lr q)
        (StripSys.rt q) η {ω | ω ∈ G ∧ ¬ 0 < rightLo (α ω) (Lr q ω) (StripSys.rt q)}
        (centredField d.field d.mean) u) :
    Lemma725Ref.PocketWordEvolution.{u} (16 / κ) rL rR := by
  have hθ₁c : θ₁ ∈ Icc (-(π / 2)) (π / 2) := Ioo_subset_Icc_self hθ₁
  have hθ₂c : θ₂ ∈ Icc (-(π / 2)) (π / 2) := Ioc_subset_Icc_self hθ₂
  have hS' := isTwoAngle_regTwo hS hleft hright
  obtain ⟨he', hEe⟩ := regTwo_leftExtremal hS hleft hright
  have hβtr' : ∀ᵐ ω ∂P, IsGeneratingTrace (regTwo κ b J P E StripSys.leftExtremalSpec 0 ω).1 ⊤ (β ω) := by
    filter_upwards [hβtr, hEe] with ω h1 h2
    rw [h2]
    exact h1
  exact WordSafe.pocketWordEvolution_of_stripSystem_restartGen h44 haux7 h411 h47 hsw hS' hleft hright hθ₁ hθ₂
    hL hLd hR hRd (isRegularDriver_regTwo_twoAngle (-(π / 2)) 1 θ₁)
    (fun q _ => isRegularDriver_regTwo_twoAngle (π / 2) (StripSys.rt q) θ₂) he' hu₀
    (isWallVersion_regTwo hS hleft hright StripSys.neg_pi_div_two_mem_Icc hθ₁c hvα)
    (fun q => isWallVersion_regTwo hS hleft hright StripSys.pi_div_two_mem_Icc hθ₂c (hvL q))
    hβc hβ0 hβm hβtr' hηc hηH hη0 hηm hηtr 𝔥 hu hub h𝔥 hside

/-- **Lemma 7.25's field reference from a two-angle strip system**:
`WordSafe.pocketChartFieldStatement_of_stripSystem_restartGen` without `hr`, `hl`, `he` (through `regTwo`). -/
theorem pocketChartFieldStatement_of_twoAngle_restartGen
    {κ rL rR : ℝ} {b : ℝ → ℝ} {J : Finset ℝ} {Ω : Type u}
    [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {h : Ω → DistOn upperHalfPlaneOpens} {W : ℝ≥0 → Ω → ℝ} {ζ : Ω → ℝ≥0∞}
    {E : ExplSpec → ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞}
    (h44 : AdmCode.Theorem12ParamCond44Statement.{u})
    (haux7 : Sec4.Aux7Statement.{u} (16 / κ))
    (h411 : Sec5.Cond44Ref.Prop411QStatement.{u})
    (h47 : Sec5.Prop411Q.Lemma47QHitStatement.{u})
    (hsw : WordSafe.SwitchedWallFirstHitStatement.{u})
    (hS : IsTwoAngleStripSystem κ b J P h W ζ E)
    (hleft : ∀ a ∈ Icc (-(π / 2)) (π / 2), ∀ y : ℝ, y < 0 → y ∉ J →
      b y + a * chiC κ ≤ -sleLambda κ)
    (hright : ∀ a ∈ Icc (-(π / 2)) (π / 2), ∀ y : ℝ, 0 < y → y ∉ J →
      sleLambda κ ≤ b y + a * chiC κ)
    {θ₁ θ₂ : ℝ} (hθ₁ : θ₁ ∈ Ioo (-(π / 2)) (π / 2))
    (hθ₂ : θ₂ ∈ Ioc (-(π / 2)) (π / 2))
    (hL : -2 < rL) (hLd : rL < 16 / κ / 2 - 4)
    (hR : -2 < rR) (hRd : rR < 16 / κ / 2 - 4)
    {u₀ : ℂ → ℝ} (hu₀ : IsBoundedHarmonicExtension b J u₀)
    {α β : Ω → ℝ≥0 → ℂ} {Lr : ℚ → Ω → ℝ≥0 → ℂ} {η : Ω → ℝ → ℂ}
    (hvα : IsWallVersion P (E (StripSys.alphaSpec θ₁)) 1 α)
    (hvL : ∀ q, IsWallVersion P (E (StripSys.betaSpec (StripSys.rt (positiveSeed q)) θ₂))
      (StripSys.rt (positiveSeed q)) (Lr q))
    (hβc : ∀ ω, Continuous (β ω)) (hβ0 : ∀ ω, β ω 0 = 0)
    (hβm : ∀ t, Measurable fun ω => β ω t)
    (hβtr : ∀ᵐ ω ∂P, IsGeneratingTrace (E StripSys.leftExtremalSpec 0 ω).1 ⊤ (β ω))
    (hηc : ∀ ω, ContinuousOn (η ω) (Ici 0))
    (hηH : ∀ ω, ∀ t : ℝ, 0 ≤ t → η ω t ∈ Hbar) (hη0 : ∀ ω, η ω 0 = 0)
    (hηm : ∀ t : ℝ, 0 ≤ t → Measurable fun ω => η ω t)
    (hηtr : ∀ᵐ ω ∂P, IsGeneratingTrace (fun t => W t ω) ⊤ (fun t : ℝ≥0 => η ω t))
    {u : ℂ → ℝ}
    (hu : InnerProductSpace.HarmonicOnNhd u H) (hub : ∃ M : ℝ, ∀ z ∈ H, |u z| ≤ M)
    (hside : ∀ q : ℚ, 0 < q → ∀ G : Set Ω,
      MeasurableSet[wallsSigma P α (Lr q)] G → 0 < P G →
      (∀ ω ∈ G, IsChangeConfigInc (α ω) (Lr q ω) (StripSys.rt q) ∧
        discTime 1 < rightHi (α ω) (Lr q ω) (StripSys.rt q)) →
      (∀ ω ∈ G, ζ ω = ⊤) →
      (∀ ω ∈ G, 0 < rightLo (α ω) (Lr q ω) (StripSys.rt q) →
        IsCfPocketConfig (α ω) (Lr q ω) (StripSys.rt q)
          (fun s : ℝ => W s.toNNReal ω) (η ω)) →
      (∀ ω ∈ G, rightLo (α ω) (Lr q ω) (StripSys.rt q) = 0 →
        IsCfPocketConfigInf (α ω) (Lr q ω) (StripSys.rt q)
          (fun s : ℝ => W s.toNNReal ω) (η ω)) →
      let d := counterflowObjects hS.counterflow
      PocketSideLimitInput0 (16 / (16 / κ)) rL rR (wallsSigma P α (Lr q)) P α (Lr q)
        (StripSys.rt q) η {ω | ω ∈ G ∧ 0 < rightLo (α ω) (Lr q ω) (StripSys.rt q)}
        (centredField d.field d.mean) u ∧
      PocketSideLimitInputInf0 (16 / (16 / κ)) rL rR (wallsSigma P α (Lr q)) P α (Lr q)
        (StripSys.rt q) η {ω | ω ∈ G ∧ ¬ 0 < rightLo (α ω) (Lr q ω) (StripSys.rt q)}
        (centredField d.field d.mean) u)
    (h513 : let d := counterflowObjects hS.counterflow
      ∃ Γ' : Ω → ℝ≥0 → ℂ, (∀ t, StronglyMeasurable[MeasurableSpace.comap
        (fun ω => centredField d.field d.mean ω + smoothDist upperHalfPlaneOpens u) inferInstance]
          fun ω => Γ' ω t) ∧ ∀ᵐ ω ∂P, Γ' ω = fun t : ℝ≥0 => η ω t) :
    Lemma725RefSafe.PocketChartFieldStatement.{u} (16 / κ) rL rR := by
  have hθ₁c : θ₁ ∈ Icc (-(π / 2)) (π / 2) := Ioo_subset_Icc_self hθ₁
  have hθ₂c : θ₂ ∈ Icc (-(π / 2)) (π / 2) := Ioc_subset_Icc_self hθ₂
  have hS' := isTwoAngle_regTwo hS hleft hright
  obtain ⟨he', hEe⟩ := regTwo_leftExtremal hS hleft hright
  have hβtr' : ∀ᵐ ω ∂P, IsGeneratingTrace (regTwo κ b J P E StripSys.leftExtremalSpec 0 ω).1 ⊤ (β ω) := by
    filter_upwards [hβtr, hEe] with ω h1 h2
    rw [h2]
    exact h1
  exact WordSafe.pocketChartFieldStatement_of_stripSystem_restartGen h44 haux7 h411 h47 hsw hS' hleft hright hθ₁ hθ₂
    hL hLd hR hRd (isRegularDriver_regTwo_twoAngle (-(π / 2)) 1 θ₁)
    (fun q _ => isRegularDriver_regTwo_twoAngle (π / 2) (StripSys.rt q) θ₂) he' hu₀
    (isWallVersion_regTwo hS hleft hright StripSys.neg_pi_div_two_mem_Icc hθ₁c hvα)
    (fun q => isWallVersion_regTwo hS hleft hright StripSys.pi_div_two_mem_Icc hθ₂c (hvL q))
    hβc hβ0 hβm hβtr' hηc hηH hη0 hηm hηtr hu hub hside
    h513

end Consumers

end InteractingSLE.Sec7.WordSafe
