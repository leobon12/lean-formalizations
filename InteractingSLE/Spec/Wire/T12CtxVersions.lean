/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Wire.T12CtxBase
import InteractingSLE.Spec.Sec5.WordSafePort2

/-! # Versions of the paths in the physical word context

These are the existing wall and trace version constructions specialized to
the canonical two-angle family used by `Relay.words`.
-/

set_option autoImplicit false
noncomputable section

open MeasureTheory ProbabilityTheory Set Filter Topology Function Bornology
open QuantumZipper (H Hbar chiC)
open LQGMetric (DistOn)
open scoped NNReal ENNReal Real

namespace InteractingSLE.Wire.T12Ctx

open Current Sec7 Sec5.TwoAngle Sec7.StripWall Sec7.StripSideHeightProb
open Exist.Staged (IsRegularDriver)

section Canonical

variable (i : BothLow) {Ω : Type} [MeasurableSpace Ω] [StandardBorelSpace Ω]
  {P : Measure Ω} [IsProbabilityMeasure P] {h : Ω → DistOn upperHalfPlaneOpens}
  {W : ℝ≥0 → Ω → ℝ} {ζ : Ω → ℝ≥0∞}

/-- The canonical experiment family, independent of choices of path versions. -/
abbrev experiments (h : Ω → DistOn upperHalfPlaneOpens) :=
  twoAngleFam cond44 (sixteen_div_kappa_pos i) (sixteen_div_kappa_lt_four i)
    (wordOf (boundary_piecewise i)) h

/-- The canonical experiments satisfy both strip-system clauses and are regular everywhere. -/
theorem experiments_system
    (hh : IsGFFWithBoundaryData P h (boundary i) jumps)
    (hcf : IsCenteredCounterflowDriver (16 / i.kappa) P h W ζ)
    (hζ : ∀ᵐ ω ∂P, ζ ω = ⊤) :
    WordSafe.IsTwoAngleStripSystem (16 / i.kappa) (boundary i) jumps P h W ζ (experiments i h) ∧
    ∀ spec k ω, IsRegularDriver (experiments i h spec k ω) := by
  have hp := sixteen_div_kappa_pos i
  have h4 := sixteen_div_kappa_lt_four i
  have hb := boundary_piecewise i
  obtain ⟨hleft, hright⟩ := boundary_heights i
  refine ⟨⟨hp, h4, hb, hh, hcf, hζ, fun θ hθ => ?_, fun {θ₀ θ} hθ₀ hθ t₀ => ?_⟩,
    twoAngleFam_regular cond44 hp h4 (wordOf hb) h⟩
  · change IsStagedHistory _ _ _ _ _ _ (twoAngleFam _ _ _ _ _ _)
    rw [twoAngleFam_constSpec]
    obtain ⟨hL, hR⟩ := R7Aux131.heights_const hp h4 hleft hright hθ
    exact StripSafe.isStagedHistory_constFam cond44 hp h4 hb (wordOf_jumps hb)
      (wordOf_fn hb) hh hL hR
  · change IsStagedHistory _ _ _ _ _ _ (twoAngleFam _ _ _ _ _ _)
    rw [twoAngleFam_twoAngleSpec]
    exact isStagedHistory_twoFam_strip cond44 hp h4 hb hleft hright hh
      (wordOf_jumps hb) (wordOf_fn hb) hθ₀ hθ

end Canonical

section Versions

variable {Ω : Type} [MeasurableSpace Ω] [StandardBorelSpace Ω]
  {P : Measure Ω} [IsProbabilityMeasure P] {κ : ℝ} {b : ℝ → ℝ} {J : Finset ℝ}
  {h : Ω → DistOn upperHalfPlaneOpens} {W : ℝ≥0 → Ω → ℝ} {ζ : Ω → ℝ≥0∞}
  {E : ExplSpec → ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞}
  (hS : WordSafe.IsTwoAngleStripSystem κ b J P h W ζ E)
  (hleft : ∀ a ∈ Icc (-(π / 2)) (π / 2), ∀ y : ℝ, y < 0 → y ∉ J →
    b y + a * chiC κ ≤ -sleLambda κ)
  (hright : ∀ a ∈ Icc (-(π / 2)) (π / 2), ∀ y : ℝ, 0 < y → y ∉ J →
    sleLambda κ ≤ b y + a * chiC κ)

include hS hleft hright

/-- The right wall version binder. -/
theorem exists_rightWall {θ : ℝ} (hθ : θ ∈ Icc (-(π / 2)) (π / 2))
    (hreg : ∀ k ω, IsRegularDriver (E (StripSys.alphaSpec θ) k ω)) :
    ∃ R : Ω → ℝ≥0 → ℂ, IsWallVersion P (E (StripSys.alphaSpec θ)) 1 R := by
  have ht := WordSafe.ae_simple_trace_alpha hS hleft hright hθ hreg
  obtain ⟨R, hR, -⟩ := StripWall.exists_isWallVersion
    (fun k => (hS.isStagedHistory_alpha hθ).1 k) hreg 1
    (ht.mono fun _ hω => hω.1) (ht.mono fun _ hω => hω.2)
  exact ⟨R, hR⟩

/-- All rationally indexed left wall version binders, on this same space. -/
theorem exists_leftWalls {θ : ℝ} (hθ : θ ∈ Icc (-(π / 2)) (π / 2))
    (hreg : ∀ r k ω, IsRegularDriver (E (StripSys.betaSpec r θ) k ω)) :
    ∃ L : ℚ → Ω → ℝ≥0 → ℂ, ∀ q,
      IsWallVersion P (E (StripSys.betaSpec (StripSys.rt (PocketWordIn.positiveSeed q)) θ))
        (StripSys.rt (PocketWordIn.positiveSeed q)) (L q) := by
  have hex : ∀ q : ℚ, ∃ L : Ω → ℝ≥0 → ℂ,
      IsWallVersion P (E (StripSys.betaSpec (StripSys.rt (PocketWordIn.positiveSeed q)) θ))
        (StripSys.rt (PocketWordIn.positiveSeed q)) L := by
    intro q
    have ht := WordSafe.ae_simple_trace_beta hS hleft hright hθ
      (StripSys.rt (PocketWordIn.positiveSeed q)) (hreg _)
    obtain ⟨L, hL, -⟩ := StripWall.exists_isWallVersion
      (fun k => (hS.isStagedHistory_beta hθ _).1 k) (hreg _)
      (StripSys.rt (PocketWordIn.positiveSeed q))
      (ht.mono fun _ hω => hω.1) (ht.mono fun _ hω => hω.2)
    exact ⟨L, hL⟩
  exact Classical.axiomOfChoice hex

/-- The outer wall's continuity, zero, measurability and trace binders. -/
theorem exists_outerWall :
    ∃ β : Ω → ℝ≥0 → ℂ, (∀ ω, Continuous (β ω)) ∧ (∀ ω, β ω 0 = 0) ∧
      (∀ t, Measurable fun ω => β ω t) ∧
      ∀ᵐ ω ∂P, IsGeneratingTrace (E StripSys.leftExtremalSpec 0 ω).1 ⊤ (β ω) := by
  obtain ⟨β, hc, h0, -, hm, ht⟩ := StripPocketVersions.exists_traceVersion
    (measurable_fst.comp (hS.isStagedHistory_leftExtremal.1 0)) (by
      filter_upwards [WordSafe.ae_regular_leftExtremal hS hleft hright] with ω hω
      exact ⟨hω.2.2.1, hω.2.1, hω.2.2.2.choose, hω.2.2.2.choose_spec.1⟩)
  exact ⟨β, hc, h0, hm, ht⟩

/-- The counterflow's continuity, half-plane, zero, measurability and trace binders. -/
theorem exists_curve :
    ∃ η : Ω → ℝ → ℂ, (∀ ω, ContinuousOn (η ω) (Ici 0)) ∧
      (∀ ω t, 0 ≤ t → η ω t ∈ Hbar) ∧ (∀ ω, η ω 0 = 0) ∧
      (∀ t, 0 ≤ t → Measurable fun ω => η ω t) ∧
      ∀ᵐ ω ∂P, IsGeneratingTrace (fun t => W t ω) ⊤ (fun t : ℝ≥0 => η ω t) := by
  let w : Ω → ℝ≥0 → ℝ := fun ω => Sec5.CfRegQ.hDrv (Sec5.Cond44Ref.cfHistory W ζ ω)
  have hm : Measurable w := Sec5.CfRegQ.measurable_hDrv.comp
    (Sec5.Cond44Ref.measurable_cfHistory
      (Sec5.Cond44Ref.isMeasurableKilledDriving_of_isCenteredCounterflowDriver hS.counterflow))
  have he : ∀ᵐ ω ∂P, Continuous (fun t => W t ω) ∧ W 0 ω = 0 ∧
      (∃ η : ℝ≥0 → ℂ, IsGeneratingTrace (fun t => W t ω) ⊤ η) ∧ w ω = fun t => W t ω := by
    filter_upwards [StripSafe.ae_counterflow_trace hS.toConst hleft hright] with ω hω
    obtain ⟨hζ, hc, h0, η, hη⟩ := hω
    refine ⟨hc, h0, ⟨η, hη⟩, funext fun t => ?_⟩
    exact WangWu.pathsOfHistory_killedHistory_driver hc.continuousOn
      (by rw [hζ]; exact ENNReal.coe_lt_top)
  obtain ⟨γ, hc, h0, hH, hm, ht⟩ := StripPocketVersions.exists_traceVersion hm (by
    filter_upwards [he] with ω hω
    rw [hω.2.2.2]
    exact ⟨hω.1, hω.2.1, hω.2.2.1⟩)
  refine ⟨fun ω s => γ ω s.toNNReal,
    fun ω => ((hc ω).comp continuous_real_toNNReal).continuousOn,
    fun ω t _ => hH ω _, fun ω => ?_, fun t _ => hm _, ?_⟩
  · simpa only [Real.toNNReal_zero] using h0 ω
  · filter_upwards [ht, he] with ω h1 h2
    rw [h2.2.2.2] at h1
    simpa only [Real.toNNReal_coe] using h1

end Versions

end InteractingSLE.Wire.T12Ctx
