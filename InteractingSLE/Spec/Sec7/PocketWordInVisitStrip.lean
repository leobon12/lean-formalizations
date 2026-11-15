/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.PocketWordInVisitPath

/-!
# The pocket word with wall visits reduced to rational first contacts

PROVE-POCKET-WORDIN continuation. The three first-contact laws below refer to
exactly the strip system's right, unchanged extremal, and rational left walls.
They replace the former full wall-visit hypotheses. The side limits remain the
separate SIDEIN input on the same fields and selected-pair sigma algebra.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter Topology Function
open LQGMetric (DistOn TestOn)
open QuantumZipper (H Hbar chiC)
open scoped NNReal ENNReal Real

universe u

namespace InteractingSLE.Sec7.PocketWordIn

open StripWall StripSideHeightProb StripPocketPath WangWu WholeField
open Lemma71I PocketCoord PocketJordan PocketMarks PocketSeedOpen PocketCoupling PocketWordAssembly
open PocketLeftFrontier PocketWordPerQ Aux119Nested LocalSets StripPocketConfig
open Exist.Staged (IsRegularDriver)

/-- The pocket-word assembly from the actual rational first-contact laws.
All reverse-order visits and positive-time visitation are proved in this theorem. -/
theorem pocketWordEvolution_of_stripSystem_firstHit
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
  exact pocketWordEvolution_of_stripSystem_sideLimit h44 haux7 h411 hS hleft hright
    hθ₁ hθ₂ hL hLd hR hRd hr hl he hu₀ hvα hvL hβc hβ0 hβm hβtr
    hηc hηH hη0 hηm hηtr hwalls hwallsL 𝔥 hu hub h𝔥 hside

end InteractingSLE.Sec7.PocketWordIn
