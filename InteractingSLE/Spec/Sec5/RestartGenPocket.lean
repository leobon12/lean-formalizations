/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec5.RestartGenReflect
import InteractingSLE.Spec.Sec7.PocketWordInVisitStrip

/-!
# The pocket word from the restart law

Packet PROVE-RESTART-GEN. `PocketWordIn.pocketWordEvolution_of_stripSystem_firstHit` (PROVE-POCKET-WORDIN) takes the
three rational first-exit laws `hfirstR`, `hfirstE`, `hfirstL` of the walls of Aux. 130. They are derived here from the
restart law (`Sec5.RestartGen`): the unchanged extremal wall from the landed Lemma 4.7 alone; the walls
`α = η^{1,∞}_{−π/2,θ₁}` and `β^{(r)} = η^{r,∞}_{π/2,θ₂}` from the landed Lemma 4.7 before their switch (at relative
angle `−π/2` by reflection, `RestartGenReflect`) and from the general law `SwitchedWallFirstHitStatement` after it.
The §4.2 reference comes from the assembly's own `Prop411QStatement` binder.

* **`pocketWordEvolution_of_stripSystem_restartGen`**: the conditional pocket word with `hfirstR`, `hfirstE`,
  `hfirstL` replaced by `h47` (the landed named input `Prop411Q.Lemma47QHitStatement`, PROVE-CFRESTART5's target) and
  `hsw` (the switched law). Every other binder is unchanged.

R48: nothing uses Theorem 1.2/1.3, `Theorem12ParamStatement`, `Theorem13Statement` or any `*_of_param`.
-/

set_option autoImplicit false

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

/-- **The conditional pocket word from the restart law** (Aux. 130, pp. 410–412): the landed assembly
`pocketWordEvolution_of_stripSystem_firstHit` with its three wall first-exit laws derived from the landed Lemma 4.7
and the general switched-wall law. -/
theorem pocketWordEvolution_of_stripSystem_restartGen
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
  have href := Sec5.Cond44Ref.cond44ReferenceStatement_of_prop411Q h411
  have hηtr' := hηtr
  exact pocketWordEvolution_of_stripSystem_firstHit h44 haux7 h411 hS hleft hright
    hθ₁ hθ₂ hL hLd hR hRd hr hl he hu₀ hvα hvL hβc hβ0 hβm hβtr
    hηc hηH hη0 hηm hηtr
    (Sec5.RestartGen.hfirstR_of_restartGen' h47 href hsw hS hleft hright hθ₁ hvα hηtr')
    (Sec5.RestartGen.hfirstE_of_restartGen h47 href hS hleft hright hβtr hηtr')
    (Sec5.RestartGen.hfirstL_of_restartGen h47 href hsw hS hleft hright hθ₂ hvL hηtr')
    𝔥 hu hub h𝔥 hside

end InteractingSLE.Sec7.PocketWordIn
