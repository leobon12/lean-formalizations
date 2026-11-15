/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec5.WordSafePort2
import InteractingSLE.Spec.Sec7.StripMarksSource
import InteractingSLE.Spec.Sec5.RestartSwReg

/-!
# Ports to the two-angle strip system, part 3

Packet PROVE-WORDSAFE. Copies of the pocket-word lemmas below with `StripSys.IsStripSystem` weakened to
`WordSafe.IsTwoAngleStripSystem` (same statements otherwise, same proofs; they read the strip system's
staged histories only at `constSpec θ` and `twoAngleSpec θ₀ t₀ θ`). Calls to ported lemmas are redirected to
the ports (`WordSafe.…`); calls to PROVE-STRIPSYS-SAFE's constant-angle ports go through
`IsTwoAngleStripSystem.toConst`. Each section names its source file. No new mathematics.

Ported: `pocketChartFieldStatement_of_stripSystem_sideLimit`, `pocketChartFieldStatement_of_stripSystem_firstHit`,
`pocketChartFieldStatement_of_stripSystem_restartGen`, `switchedWallFirstHitStatement_of_input`.

R48: nothing here uses Theorem 1.2/1.3, `Theorem12ParamStatement`, `Theorem13Statement` or any `*_of_param`.
-/

set_option autoImplicit false

noncomputable section

universe u v w

open MeasureTheory ProbabilityTheory Filter Set Topology Function
open scoped NNReal ENNReal Real

namespace InteractingSLE.Sec7.WordSafe

section
-- from InteractingSLE/Spec/Sec7/StripMarksSource.lean
open InteractingSLE.Sec7.StripMarks
set_option relaxedAutoImplicit false
open MeasureTheory ProbabilityTheory Set Filter Topology Function
open LQGMetric (DistOn TestOn)
open QuantumZipper (H Hbar chiC)
open SupercriticalConformalCovariance.GM24 (smoothDist)
open scoped NNReal ENNReal Real
open StripWall StripSideHeightProb StripPocketPath WangWu WholeField
open Lemma71I PocketCoord PocketJordan PocketMarks PocketSeedOpen PocketCoupling PocketWordAssembly
open PocketLeftFrontier PocketWordPerQ Aux119Nested LocalSets StripPocketConfig PocketWordIn
open Exist.Staged (IsRegularDriver)

/-- (PROVE-WORDSAFE port to `IsTwoAngleStripSystem`.)
**Lemma 7.25's field reference from the strip system** (Aux. lemma 130's objects). The field transport,
coupling, lifetime, wall simplicity, joining point, late separation, trace, avoidance, attachment constancy,
determination and locality are derived from the strip system exactly as for the pocket word; the per-seed side limits
and Proposition 5.13 for the strip's counterflow remain. -/
theorem pocketChartFieldStatement_of_stripSystem_sideLimit
    {κ rL rR : ℝ} {b : ℝ → ℝ} {J : Finset ℝ} {Ω : Type u}
    [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {h : Ω → DistOn upperHalfPlaneOpens} {W : ℝ≥0 → Ω → ℝ} {ζ : Ω → ℝ≥0∞}
    {E : ExplSpec → ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞}
    (h44 : AdmCode.Theorem12ParamCond44Statement.{u})
    (haux7 : Sec4.Aux7Statement.{u} (16 / κ))
    (h411 : Sec5.Cond44Ref.Prop411QStatement.{u})
    (hS : IsTwoAngleStripSystem κ b J P h W ζ E)
    (hleft : ∀ a ∈ Icc (-(π / 2)) (π / 2), ∀ y : ℝ, y < 0 → y ∉ J →
      b y + a * chiC κ ≤ -sleLambda κ)
    (hright : ∀ a ∈ Icc (-(π / 2)) (π / 2), ∀ y : ℝ, 0 < y → y ∉ J →
      sleLambda κ ≤ b y + a * chiC κ)
    {θ₁ θ₂ : ℝ} (hθ₁ : θ₁ ∈ Ioo (-(π / 2)) (π / 2))
    (hθ₂ : θ₂ ∈ Ioc (-(π / 2)) (π / 2))
    (hL : -2 < rL) (hLd : rL < 16 / κ / 2 - 4)
    (hR : -2 < rR) (hRd : rR < 16 / κ / 2 - 4)
    (hr : ∀ j ω, IsRegularDriver (E (StripSys.alphaSpec θ₁) j ω))
    (hl : ∀ q : ℚ, 0 < q → ∀ j ω,
      IsRegularDriver (E (StripSys.betaSpec (StripSys.rt q) θ₂) j ω))
    (he : ∀ ω, IsRegularDriver (E StripSys.leftExtremalSpec 0 ω))
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
    (hwalls : ∀ᵐ ω ∂P, IsWallReverseVisit (α ω) (η ω) ∧ IsWallVisited (α ω) (η ω) ∧
      IsWallReverseVisit (β ω) (η ω) ∧ IsWallVisited (β ω) (η ω))
    (hwallsL : ∀ q : ℚ, 0 < q → ∀ᵐ ω ∂P,
      IsWallReverseVisit (Lr q ω) (η ω) ∧ IsWallVisited (Lr q ω) (η ω))
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
  have hθ₁c := Ioo_subset_Icc_self hθ₁
  have hθ₂c := Ioc_subset_Icc_self hθ₂
  have hvLp : ∀ q : ℚ, 0 < q →
      IsWallVersion P (E (StripSys.betaSpec (StripSys.rt q) θ₂)) (StripSys.rt q) (Lr q) :=
    fun q hq => by simpa only [positiveSeed_of_pos hq] using hvL q
  have hw := fun q => WordSafe.wall_inputs h44 hS hleft hright hθ₁c hθ₂c (positiveSeed_pos q)
    hr (hl _ (positiveSeed_pos q)) hu₀ hvα (hvL q)
  have hdα := (hw 1).1
  have hlocα := (hw 1).2.1
  have hdL := fun q => (hw q).2.2.1
  have hlocL := fun q => (hw q).2.2.2
  have hh := Restart.isZeroBoundaryGFF_centredField_of_isGFFWithBoundaryData hS.gff hu₀
  have hβsp := WordSafe.ae_isSimpleProper_leftExtremal hS hleft hright he hβc hβ0 hβtr
  have hαsp := WordSafe.ae_isSimpleProper_alpha hS hleft hright hθ₁c hr
    hvα.continuous hvα.zero hvα.ae_isGeneratingTrace
  have hgeomR := hαsp.and hwalls
  have hgeomβ : ∀ᵐ ω ∂P, IsSimpleProper (β ω) ∧ IsWallReverseVisit (β ω) (η ω) ∧
      IsWallVisited (β ω) (η ω) := by
    filter_upwards [hβsp, hwalls] with ω hs hv
    exact ⟨hs, hv.2.2.1, hv.2.2.2⟩
  have hgeomL : ∀ q : ℚ, 0 < q → ∀ᵐ ω ∂P, IsSimpleProper (Lr q ω) ∧
      IsWallReverseVisit (Lr q ω) (η ω) ∧ Lr q ω (StripSys.rt q) = β ω (StripSys.rt q) := by
    intro q hq
    have hv := hvLp q hq
    filter_upwards [WordSafe.ae_isSimpleProper_beta hS hleft hright hθ₂c (StripSys.rt q) (hl q hq)
      hv.continuous hv.zero hv.ae_isGeneratingTrace, hwallsL q hq,
      WordSafe.ae_eq_leftExtremal_of_le h44 hS hleft hright hθ₂c (StripSys.rt q) (hl q hq 0)
        hv.ae_isGeneratingTrace hβtr] with ω hs hvisit hjoin
    exact ⟨hs, hvisit.1, hjoin _ le_rfl⟩
  have hlate := WordSafe.ae_late_strip h44 hS hleft hright hθ₁ hr he
    hvα.continuous hvα.zero hvα.measurable hvα.ae_isGeneratingTrace hβc hβ0 hβm hβtr hηc hwalls
  have htrace := StripSafe.ae_isLoewnerTrace_counterflow hS.toConst hleft hright hηtr
  have hnohit := WordSafe.ae_noReturn_counterflow haux7 hS hleft hright hηtr
  have hav := WordSafe.ae_avoidance h411 hS hleft hright hβtr hηtr
  have hwR : ∀ᵐ ω ∂P, IsWallReverseVisit (α ω) (η ω) ∧ IsWallVisited (α ω) (η ω) :=
    hwalls.mono fun _ hv => ⟨hv.1, hv.2.1⟩
  have hattach := WordSafe.hattach_strip h44 hS hleft hright hθ₁ hθ₂ hr hl he
    hvα.continuous hvα.zero hvα.measurable hvα.ae_isGeneratingTrace hβc hβ0 hβtr
    (fun q => (hvL q).continuous) (fun q => (hvL q).zero) (fun q => (hvL q).measurable)
    (fun q hq => (hvLp q hq).ae_isGeneratingTrace) hηc hηtr hwR
    (fun q hq => (hwallsL q hq).mono fun _ hv => hv.1) hav
  have hattachI := WordSafe.hattachI_strip h44 haux7 hS hleft hright hθ₁ hθ₂ hr hl he
    hvα.continuous hvα.zero hvα.measurable hvα.ae_isGeneratingTrace hβc hβ0 hβtr
    (fun q => (hvL q).continuous) (fun q => (hvL q).zero) (fun q => (hvL q).measurable)
    (fun q hq => (hvLp q hq).ae_isGeneratingTrace) hηc hηtr hwR hwallsL hav
  obtain ⟨hT, hTr, hC, hu'⟩ := counterflowObjects_spec hS.counterflow
  have hk' : 4 < 16 / κ := by
    rw [lt_div_iff₀ hS.kappa_pos]
    linarith only [hS.kappa_lt_four]
  exact RefWire.pocketChartFieldStatement_of_sideLimit_perQ hk' hL hLd hR hRd hT hTr hu₀.1 hh
    hC hu' (counterflowObjects_measurable hS.counterflow) hS.lifetime
    hvα.measurable (fun q => (hvL q).measurable) hvα.continuous (fun q => (hvL q).continuous)
    hvα.zero (fun q => (hvL q).zero) hβm hηm hηc hηH hη0
    (hgeomR.mono fun _ hg => ⟨hg.1, hg.2.1, hg.2.2.1⟩) hgeomβ hgeomL hnohit hlate
    (by simpa only [Real.toNNReal_zero] using htrace) hav hattach hattachI
    hdα hdL hlocα hlocL hu hub hside h513

/-- (PROVE-WORDSAFE port to `IsTwoAngleStripSystem`.)
**Lemma 7.25's field reference with the wall visits reduced to rational first contacts** (as
`WordSafe.pocketWordEvolution_of_stripSystem_firstHit`). -/
theorem pocketChartFieldStatement_of_stripSystem_firstHit
    {κ rL rR : ℝ} {b : ℝ → ℝ} {J : Finset ℝ} {Ω : Type u}
    [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {h : Ω → DistOn upperHalfPlaneOpens} {W : ℝ≥0 → Ω → ℝ} {ζ : Ω → ℝ≥0∞}
    {E : ExplSpec → ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞}
    (h44 : AdmCode.Theorem12ParamCond44Statement.{u})
    (haux7 : Sec4.Aux7Statement.{u} (16 / κ))
    (h411 : Sec5.Cond44Ref.Prop411QStatement.{u})
    (hS : IsTwoAngleStripSystem κ b J P h W ζ E)
    (hleft : ∀ a ∈ Icc (-(π / 2)) (π / 2), ∀ y : ℝ, y < 0 → y ∉ J →
      b y + a * chiC κ ≤ -sleLambda κ)
    (hright : ∀ a ∈ Icc (-(π / 2)) (π / 2), ∀ y : ℝ, 0 < y → y ∉ J →
      sleLambda κ ≤ b y + a * chiC κ)
    {θ₁ θ₂ : ℝ} (hθ₁ : θ₁ ∈ Ioo (-(π / 2)) (π / 2))
    (hθ₂ : θ₂ ∈ Ioc (-(π / 2)) (π / 2))
    (hL : -2 < rL) (hLd : rL < 16 / κ / 2 - 4)
    (hR : -2 < rR) (hRd : rR < 16 / κ / 2 - 4)
    (hr : ∀ j ω, IsRegularDriver (E (StripSys.alphaSpec θ₁) j ω))
    (hl : ∀ q : ℚ, 0 < q → ∀ j ω,
      IsRegularDriver (E (StripSys.betaSpec (StripSys.rt q) θ₂) j ω))
    (he : ∀ ω, IsRegularDriver (E StripSys.leftExtremalSpec 0 ω))
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
    (hfirstR : ∀ q : ℚ, 0 < q → ∀ᵐ ω ∂P,
      Sec5.Prop411Q.IsFirstHitQ (Lemma71I.realPath (α ω)) (η ω) q)
    (hfirstE : ∀ q : ℚ, 0 < q → ∀ᵐ ω ∂P,
      Sec5.Prop411Q.IsFirstHitQ (Lemma71I.realPath (β ω)) (η ω) q)
    (hfirstL : ∀ r : ℚ, 0 < r → ∀ q : ℚ, 0 < q → ∀ᵐ ω ∂P,
      Sec5.Prop411Q.IsFirstHitQ (Lemma71I.realPath (Lr r ω)) (η ω) q)
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
  have hθ₁c := Ioo_subset_Icc_self hθ₁
  have hθ₂c := Ioc_subset_Icc_self hθ₂
  have hvisitR := ae_wall_visits_of_firstHitQ
    (WordSafe.ae_isSimpleProper_alpha hS hleft hright hθ₁c hr
      hvα.continuous hvα.zero hvα.ae_isGeneratingTrace) hηc hη0 hfirstR
  have hvisitE := ae_wall_visits_of_firstHitQ
    (WordSafe.ae_isSimpleProper_leftExtremal hS hleft hright he hβc hβ0 hβtr) hηc hη0 hfirstE
  have hwalls : ∀ᵐ ω ∂P, IsWallReverseVisit (α ω) (η ω) ∧ IsWallVisited (α ω) (η ω) ∧
      IsWallReverseVisit (β ω) (η ω) ∧ IsWallVisited (β ω) (η ω) := by
    filter_upwards [hvisitR, hvisitE] with ω hrω heω
    exact ⟨hrω.1, hrω.2, heω⟩
  have hwallsL : ∀ r : ℚ, 0 < r → ∀ᵐ ω ∂P,
      IsWallReverseVisit (Lr r ω) (η ω) ∧ IsWallVisited (Lr r ω) (η ω) := by
    intro r hrpos
    have hv : IsWallVersion P (E (StripSys.betaSpec (StripSys.rt r) θ₂))
        (StripSys.rt r) (Lr r) := by
      simpa only [positiveSeed_of_pos hrpos] using hvL r
    exact ae_wall_visits_of_firstHitQ
      (WordSafe.ae_isSimpleProper_beta hS hleft hright hθ₂c (StripSys.rt r) (hl r hrpos)
        hv.continuous hv.zero hv.ae_isGeneratingTrace) hηc hη0 (hfirstL r hrpos)
  exact WordSafe.pocketChartFieldStatement_of_stripSystem_sideLimit h44 haux7 h411 hS hleft hright
    hθ₁ hθ₂ hL hLd hR hRd hr hl he hu₀ hvα hvL hβc hβ0 hβm hβtr
    hηc hηH hη0 hηm hηtr hwalls hwallsL hu hub hside h513

/-- (PROVE-WORDSAFE port to `IsTwoAngleStripSystem`.)
**Lemma 7.25's field reference from the restart law** (as
`WordSafe.pocketWordEvolution_of_stripSystem_restartGen`): the three rational first-hit laws come from Lemma 4.7
(`h47`) and the switched-wall law (`hsw`). Every other binder is a binder of the pocket-word assembly, except `h513`. -/
theorem pocketChartFieldStatement_of_stripSystem_restartGen
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
    (hr : ∀ j ω, IsRegularDriver (E (StripSys.alphaSpec θ₁) j ω))
    (hl : ∀ q : ℚ, 0 < q → ∀ j ω,
      IsRegularDriver (E (StripSys.betaSpec (StripSys.rt q) θ₂) j ω))
    (he : ∀ ω, IsRegularDriver (E StripSys.leftExtremalSpec 0 ω))
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
  have href := Sec5.Cond44Ref.cond44ReferenceStatement_of_prop411Q h411
  have hηtr' := hηtr
  exact WordSafe.pocketChartFieldStatement_of_stripSystem_firstHit h44 haux7 h411 hS hleft hright
    hθ₁ hθ₂ hL hLd hR hRd hr hl he hu₀ hvα hvL hβc hβ0 hβm hβtr
    hηc hηH hη0 hηm hηtr
    (WordSafe.hfirstR_of_restartGen' h47 href hsw hS hleft hright hθ₁ hvα hηtr')
    (WordSafe.hfirstE_of_restartGen h47 href hS hleft hright hβtr hηtr')
    (WordSafe.hfirstL_of_restartGen h47 href hsw hS hleft hright hθ₂ hvL hηtr')
    hu hub hside h513

end

section
-- from InteractingSLE/Spec/Sec5/RestartSwReg.lean
open InteractingSLE.Sec5 InteractingSLE.Sec5.RestartSw
open MeasureTheory ProbabilityTheory Filter Set Topology Function
open scoped NNReal ENNReal Real
open QuantumZipper (H chiC)
open LQGMetric (DistOn TestOn)
open Prop411Q (IsFirstHitQ)
open Sec7.Lemma71I (realPath)
open Sec7.StripSideHeightProb (catPath)
open Exist Exist.Staged Exist.StagedLaw Sec7.StripDet
open Theorem14.StagedReg (regHist regularize isRegularDriver_regHist measurable_regHist regHist_snd
  regularize_eq_of_le regularize_eq_of_lt regularize_zero canonDrv_regularize run_eq_of_canonDrv_eq_on_launch
  ae_condExpKernel_eq_of_ae_eq isFlowLineDriver_congr_ae)

/-- (PROVE-WORDSAFE port to `IsTwoAngleStripSystem`.)
**`WordSafe.SwitchedWallFirstHitStatement` from the inputs** (Lemma 5.7 with `ℓ = 2`): Lemma 4.7 in the chart `Q`
(the landed `Prop411Q.Lemma47QHitStatement`, relative angle `π/2`) and at every interior relative angle
(`RestartGen.Lemma47QHitTStatement θ`, `θ ∈ (−π/2, π/2)`; the angle `−π/2` goes by reflection to `π/2`), the §4.2
reference and Lemma 4.7's conditional law at the switch (`CounterflowGivenPrefixStatement`). The two-angle staged
history is replaced by its regularization (`isStagedHistory_regHist_twoAngle`), of which the wall is again a version
(`ae_wall_eq_of_regHist`), and `ae_isFirstHitQ_switched_of_reg` applies. -/
theorem switchedWallFirstHitStatement_of_input (h47 : Prop411Q.Lemma47QHitStatement.{u})
    (h47T : ∀ θ ∈ Ioo (-(π / 2)) (π / 2), RestartGen.Lemma47QHitTStatement.{u} θ)
    (href : Sec7.Lemma71H.Cond44ReferenceStatement.{u}) (hcg : CounterflowGivenPrefixStatement.{u}) :
    WordSafe.SwitchedWallFirstHitStatement.{u} := by
  intro κ b J Ω _ _ P _ h W' ζ' E hS hleft hright θ₀ θ hθ₀ hθ t₀ R hR η hη q hqt
  have hκ := hS.kappa_pos
  have hκ4 := hS.kappa_lt_four
  have hb := hS.boundaryData
  have hh := hS.gff
  have hχ : 0 < chiC κ := Sec4.chiC_pos hκ hκ4
  have hπχ : 0 < Real.pi * chiC κ := mul_pos Real.pi_pos hχ
  have hL0 : ∀ y : ℝ, y < 0 → y ∉ J → b y + θ₀ * chiC κ ≤ -sleLambda κ + Real.pi * chiC κ := fun y hy hyJ => by
    have := hleft θ₀ hθ₀ y hy hyJ; linarith
  have hR0 : ∀ y : ℝ, 0 < y → y ∉ J → sleLambda κ ≤ b y + θ₀ * chiC κ := hright θ₀ hθ₀
  have hL : ∀ y : ℝ, y < 0 → y ∉ J → b y + θ * chiC κ ≤ -sleLambda κ + Real.pi * chiC κ := fun y hy hyJ => by
    have := hleft θ hθ y hy hyJ; linarith
  have hRθ : ∀ y : ℝ, 0 < y → y ∉ J → sleLambda κ - Real.pi * chiC κ ≤ b y + θ * chiC κ := fun y hy hyJ => by
    have := hright θ hθ y hy hyJ; linarith
  have hθπ : θ ≤ θ₀ + Real.pi := by linarith [hθ.2, hθ₀.1, Real.pi_pos]
  have hθπ' : θ₀ ≤ θ + Real.pi := by linarith [hθ₀.2, hθ.1, Real.pi_pos]
  have hE := hS.stagedTwoAngle hθ₀ hθ t₀
  have hE' := isStagedHistory_regHist_twoAngle hκ hκ4 hb hh hE hL0 hR0
  have hreg' : ∀ j ω, IsRegularDriver (regHist (Sec7.StripSys.twoAngleSpec θ₀ t₀ θ)
      (E (Sec7.StripSys.twoAngleSpec θ₀ t₀ θ)) j ω) := fun j ω => isRegularDriver_regHist j ω
  obtain ⟨γ, hγ, -⟩ := Sec7.StripWall.exists_isWallVersion_twoAngle hκ hκ4 hb hh hE' hreg' hL0 hR0 hL hRθ hθπ hθπ'
  have hz1 : ∀ᵐ ω ∂P, (E (Sec7.StripSys.twoAngleSpec θ₀ t₀ θ) 1 ω).2 = ⊤ :=
    (Sec7.StripWall.ae_goodPath_one hκ hκ4 hb hh hE' hreg' hL0 hR0 hL hRθ hθπ hθπ').mono fun ω hω =>
      (regHist_snd 1 ω).symm.trans (Sec7.StripWall.mem_goodPathSet.1 hω).1
  have hRγ := ae_wall_eq_of_regHist hκ hκ4 hb hh hE hL0 hR0 hz1 hR hγ
  have hR' : Sec7.StripWall.IsWallVersion P (regHist (Sec7.StripSys.twoAngleSpec θ₀ t₀ θ)
      (E (Sec7.StripSys.twoAngleSpec θ₀ t₀ θ))) t₀ R :=
    ⟨hR.continuous, hR.zero, hR.measurable, by
      filter_upwards [hγ.ae_trace, hRγ] with ω h1 h2
      rw [h2]
      exact h1⟩
  exact ae_isFirstHitQ_switched_of_reg (lemma47QHitT_Ioc h47 h47T) href hcg hκ hκ4 hb hh hS.counterflow hS.lifetime
    hleft hright hθ₀ hθ hE' hreg' hR' hη q hqt

end

end InteractingSLE.Sec7.WordSafe
