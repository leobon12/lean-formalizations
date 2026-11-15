/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec5.RestartGenPocket
import InteractingSLE.Spec.Sec7.RefWireSide

/-!
# Lemma 7.25's field reference from the strip system

Packet PROVE-STRIPMARKS. Lemma 7.25's proof (`source/spec/p385-432.md` L489–L515, pp. 413–414): "Construct the
non-boundary centered counterflow and the two schedules in Aux. lemma 130 …". The determination reference of
Theorem 1.2's wiring (`Wire.late_determinationReferenceFamily`, the `hStripMarks` slot of PROVE-WIRE-PARTA) asked for a
separate reference object with about forty source facts (coupling, chart transport, walls, visits, attachments,
determination, locality, …). They are exactly the facts that the pocket-word assembly
(`PocketWordIn.pocketWordEvolution_of_stripSystem_sideLimit`) already derives from the strip system of Aux. lemma 130.

* **`pocketChartFieldStatement_of_stripSystem_sideLimit`**: `Lemma725RefSafe.PocketChartFieldStatement (16/κ) rL rR`
  from the strip system with the same source binders as the pocket word, the per-seed side limits and Proposition
  5.13 for the strip's own counterflow (`h513`);
* **`pocketChartFieldStatement_of_stripSystem_firstHit`**: the wall visits replaced by the three rational first-hit
  laws (as `pocketWordEvolution_of_stripSystem_firstHit`);
* **`pocketChartFieldStatement_of_stripSystem_restartGen`**: the first-hit laws replaced by Lemma 4.7 and the
  switched-wall law (as `pocketWordEvolution_of_stripSystem_restartGen`).

Every binder is a binder of the pocket-word assembly except `h513`. R48: nothing uses Theorem 1.2/1.3,
`Theorem12ParamStatement`, `Theorem13Statement` or any `*_of_param`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter Topology Function
open LQGMetric (DistOn TestOn)
open QuantumZipper (H Hbar chiC)
open SupercriticalConformalCovariance.GM24 (smoothDist)
open scoped NNReal ENNReal Real

universe u

namespace InteractingSLE.Sec7.StripMarks

open StripWall StripSideHeightProb StripPocketPath WangWu WholeField
open Lemma71I PocketCoord PocketJordan PocketMarks PocketSeedOpen PocketCoupling PocketWordAssembly
open PocketLeftFrontier PocketWordPerQ Aux119Nested LocalSets StripPocketConfig PocketWordIn
open Exist.Staged (IsRegularDriver)

/-- **Lemma 7.25's field reference from the strip system** (Aux. lemma 130's objects). The field transport,
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
    (hS : StripSys.IsStripSystem κ b J P h W ζ E)
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
  have hw := fun q => wall_inputs h44 hS hleft hright hθ₁c hθ₂c (positiveSeed_pos q)
    hr (hl _ (positiveSeed_pos q)) hu₀ hvα (hvL q)
  have hdα := (hw 1).1
  have hlocα := (hw 1).2.1
  have hdL := fun q => (hw q).2.2.1
  have hlocL := fun q => (hw q).2.2.2
  have hh := Restart.isZeroBoundaryGFF_centredField_of_isGFFWithBoundaryData hS.gff hu₀
  have hβsp := ae_isSimpleProper_leftExtremal hS hleft hright he hβc hβ0 hβtr
  have hαsp := ae_isSimpleProper_alpha hS hleft hright hθ₁c hr
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
    filter_upwards [ae_isSimpleProper_beta hS hleft hright hθ₂c (StripSys.rt q) (hl q hq)
      hv.continuous hv.zero hv.ae_isGeneratingTrace, hwallsL q hq,
      ae_eq_leftExtremal_of_le h44 hS hleft hright hθ₂c (StripSys.rt q) (hl q hq 0)
        hv.ae_isGeneratingTrace hβtr] with ω hs hvisit hjoin
    exact ⟨hs, hvisit.1, hjoin _ le_rfl⟩
  have hlate := ae_late_strip h44 hS hleft hright hθ₁ hr he
    hvα.continuous hvα.zero hvα.measurable hvα.ae_isGeneratingTrace hβc hβ0 hβm hβtr hηc hwalls
  have htrace := ae_isLoewnerTrace_counterflow hS hleft hright hηtr
  have hnohit := ae_noReturn_counterflow haux7 hS hleft hright hηtr
  have hav := ae_avoidance h411 hS hleft hright hβtr hηtr
  have hwR : ∀ᵐ ω ∂P, IsWallReverseVisit (α ω) (η ω) ∧ IsWallVisited (α ω) (η ω) :=
    hwalls.mono fun _ hv => ⟨hv.1, hv.2.1⟩
  have hattach := Aux37Walls.hattach_strip h44 hS hleft hright hθ₁ hθ₂ hr hl he
    hvα.continuous hvα.zero hvα.measurable hvα.ae_isGeneratingTrace hβc hβ0 hβtr
    (fun q => (hvL q).continuous) (fun q => (hvL q).zero) (fun q => (hvL q).measurable)
    (fun q hq => (hvLp q hq).ae_isGeneratingTrace) hηc hηtr hwR
    (fun q hq => (hwallsL q hq).mono fun _ hv => hv.1) hav
  have hattachI := Aux37Walls.hattachI_strip h44 haux7 hS hleft hright hθ₁ hθ₂ hr hl he
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

/-- **Lemma 7.25's field reference with the wall visits reduced to rational first contacts** (as
`PocketWordIn.pocketWordEvolution_of_stripSystem_firstHit`). -/
theorem pocketChartFieldStatement_of_stripSystem_firstHit
    {κ rL rR : ℝ} {b : ℝ → ℝ} {J : Finset ℝ} {Ω : Type u}
    [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {h : Ω → DistOn upperHalfPlaneOpens} {W : ℝ≥0 → Ω → ℝ} {ζ : Ω → ℝ≥0∞}
    {E : ExplSpec → ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞}
    (h44 : AdmCode.Theorem12ParamCond44Statement.{u})
    (haux7 : Sec4.Aux7Statement.{u} (16 / κ))
    (h411 : Sec5.Cond44Ref.Prop411QStatement.{u})
    (hS : StripSys.IsStripSystem κ b J P h W ζ E)
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
    (ae_isSimpleProper_alpha hS hleft hright hθ₁c hr
      hvα.continuous hvα.zero hvα.ae_isGeneratingTrace) hηc hη0 hfirstR
  have hvisitE := ae_wall_visits_of_firstHitQ
    (ae_isSimpleProper_leftExtremal hS hleft hright he hβc hβ0 hβtr) hηc hη0 hfirstE
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
      (ae_isSimpleProper_beta hS hleft hright hθ₂c (StripSys.rt r) (hl r hrpos)
        hv.continuous hv.zero hv.ae_isGeneratingTrace) hηc hη0 (hfirstL r hrpos)
  exact pocketChartFieldStatement_of_stripSystem_sideLimit h44 haux7 h411 hS hleft hright
    hθ₁ hθ₂ hL hLd hR hRd hr hl he hu₀ hvα hvL hβc hβ0 hβm hβtr
    hηc hηH hη0 hηm hηtr hwalls hwallsL hu hub hside h513

/-- **Lemma 7.25's field reference from the restart law** (as
`PocketWordIn.pocketWordEvolution_of_stripSystem_restartGen`): the three rational first-hit laws come from Lemma 4.7
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
    (hsw : Sec5.RestartGen.SwitchedWallFirstHitStatement.{u})
    (hS : StripSys.IsStripSystem κ b J P h W ζ E)
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
  exact pocketChartFieldStatement_of_stripSystem_firstHit h44 haux7 h411 hS hleft hright
    hθ₁ hθ₂ hL hLd hR hRd hr hl he hu₀ hvα hvL hβc hβ0 hβm hβtr
    hηc hηH hη0 hηm hηtr
    (Sec5.RestartGen.hfirstR_of_restartGen' h47 href hsw hS hleft hright hθ₁ hvα hηtr')
    (Sec5.RestartGen.hfirstE_of_restartGen h47 href hS hleft hright hβtr hηtr')
    (Sec5.RestartGen.hfirstL_of_restartGen h47 href hsw hS hleft hright hθ₂ hvL hηtr')
    hu hub hside h513

end InteractingSLE.Sec7.StripMarks
