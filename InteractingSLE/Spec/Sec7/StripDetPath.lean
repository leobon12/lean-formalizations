/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.StripDetMain
import InteractingSLE.Spec.Coupling.Locality11Gauss

/-!
# Lemma 6.2's determination input for the angle-varying path

Packet PROVE-STRIPSYS21, §5.1 (i) of `planning/handoffs/PROVE-STRIPSYS19.md`, ruling R48. From
`StripDetMain.lean` (both pieces of the two-angle staged history are almost surely field-determined):

* **`exists_borel_drivers`**: Borel maps `D₀`, `D₁` of the field with, almost surely, `E 0 = D₀ h` and `E 1 = D₁ h`
  (as driver–lifetime pairs; the lifetimes are infinite);
* **`hdet_of_trace`** (the hypothesis `hdet` of `StripMark.isHistoryAvoidanceLocal_pastTwo` and of
  `RS133.ae_late_of_sideHeights`): every path `αc` that is almost surely a generating trace of the concatenated driver
  `catPath (E 0).1 t₀ (E 1).1` on `[0, ∞)` is, at every time, almost surely a Borel function of the centred field
  `h − 𝔥₀` (LP11's reconstruction `LP.traceAt` of the concatenated determined driver).

Hypotheses: (4.4) heights of the data at both angles, `θ₀ ≤ θ ≤ θ₀ + π` (spec p. 410), and
`AdmCode.Theorem12ParamCond44Statement` (proved from the §4.2 reference). No Theorem 1.2/1.3.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal

universe u

namespace InteractingSLE

namespace Sec7

namespace StripDet

open LQGMetric Restart Exist Exist.Staged Exist.StagedLaw Exist.StagedLaw.BoundaryWord AdmCode Sec4 QuantumZipper
open StripSideHeightProb (catPath catPath_zero continuous_catPath)
open SupercriticalConformalCovariance.GM24 (smoothDist)

theorem measurable_catPath (T₀ : ℝ≥0) :
    Measurable fun p : (ℝ≥0 → ℝ) × (ℝ≥0 → ℝ) => catPath p.1 T₀ p.2 := by
  refine measurable_pi_iff.2 fun t => ?_
  by_cases ht : t ≤ T₀
  · simp only [catPath, ht, ↓reduceIte]
    exact (measurable_pi_apply t).comp measurable_fst
  · simp only [catPath, ht, ↓reduceIte]
    exact ((measurable_pi_apply T₀).comp measurable_fst).add ((measurable_pi_apply (t - T₀)).comp measurable_snd)

section Strip

variable {κ : ℝ} {b : ℝ → ℝ} {jumps : Finset ℝ} {Ω : Type u} [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω]
  {P : Measure Ω} [IsProbabilityMeasure P] {h : Ω → DistOn upperHalfPlaneOpens} {θ₀ θ : ℝ} {t₀ : ℝ≥0}
  {E : ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞}

/-- **Both pieces of the angle-varying path are Borel functions of the field** (R48-safe; spec p. 410, "Conditional
field determination makes the continuation measurable from the first prefix and the original field"). -/
theorem exists_borel_drivers (h44 : Theorem12ParamCond44Statement.{u}) (hκ : 0 < κ) (hκ4 : κ < 4)
    (hb : IsPiecewiseConstantBoundaryData b jumps) (hh : IsGFFWithBoundaryData P h b jumps)
    (hE : IsStagedHistory κ b jumps P h (StripSys.twoAngleSpec θ₀ t₀ θ) E) (hreg : ∀ j ω, IsRegularDriver (E j ω))
    (hL0 : ∀ y : ℝ, y < 0 → y ∉ jumps → b y + θ₀ * chiC κ ≤ -sleLambda κ + Real.pi * chiC κ)
    (hR0 : ∀ y : ℝ, 0 < y → y ∉ jumps → sleLambda κ ≤ b y + θ₀ * chiC κ)
    (hL : ∀ y : ℝ, y < 0 → y ∉ jumps → b y + θ * chiC κ ≤ -sleLambda κ + Real.pi * chiC κ)
    (hR : ∀ y : ℝ, 0 < y → y ∉ jumps → sleLambda κ ≤ b y + θ * chiC κ) (hθ : θ₀ ≤ θ)
    (hθπ : θ ≤ θ₀ + Real.pi) :
    ∃ D₀ D₁ : DistOn upperHalfPlaneOpens → (ℝ≥0 → ℝ) × ℝ≥0∞, Measurable D₀ ∧ Measurable D₁ ∧
      (∀ f, IsRegularDriver (D₀ f)) ∧ (∀ f, IsRegularDriver (D₁ f)) ∧
      ∀ᵐ ω ∂P, (E 0 ω).2 = ⊤ ∧ (E 1 ω).2 = ⊤ ∧ E 0 ω = D₀ (h ω) ∧ E 1 ω = D₁ (h ω) := by
  obtain ⟨c₀, hc₀J, hc₀⟩ := Restart.BoundaryWord.exists_fn_eq hb
  set D₀ : DistOn upperHalfPlaneOpens → (ℝ≥0 → ℝ) × ℝ≥0∞ := fun f =>
    admDrv h44 hκ hκ4 θ₀ (shiftW 0 c₀, flowField 0 0 f) with hD₀def
  have hD₀ : Measurable D₀ :=
    (measurable_admDrv h44 hκ hκ4 θ₀).comp (measurable_const.prodMk (measurable_flowField 0 0))
  have hD₀r : ∀ f, IsRegularDriver (D₀ f) := fun f => admDrv_regular h44 hκ hκ4 θ₀ _
  have hR₀ : Measurable fun f => recOf (t₀ : ℝ≥0∞) (D₀ f) := measurable_recOf hD₀ hD₀r _
  set D₁ : DistOn upperHalfPlaneOpens → (ℝ≥0 → ℝ) × ℝ≥0∞ := fun f =>
    admDrv h44 hκ hκ4 θ (word₁ κ θ₀ c₀ (recOf (t₀ : ℝ≥0∞) (D₀ f)), field₁ κ (recOf (t₀ : ℝ≥0∞) (D₀ f)) f)
    with hD₁def
  have hD₁ : Measurable D₁ := by
    refine (measurable_admDrv h44 hκ hκ4 θ).comp (((measurable_word₁ κ θ₀ c₀).comp hR₀).prodMk ?_)
    exact Measurable.comp (g := fun p : RecData × DistOn upperHalfPlaneOpens => field₁ κ p.1 p.2)
      (f := fun f => (recOf (t₀ : ℝ≥0∞) (D₀ f), f)) (measurable_field₁ κ) (hR₀.prodMk measurable_id)
  refine ⟨D₀, D₁, hD₀, hD₁, hD₀r, fun f => admDrv_regular h44 hκ hκ4 θ _, ?_⟩
  filter_upwards [ae_drv_zero h44 hκ hκ4 hb hh hE hreg hc₀J hc₀ hL0 hR0,
    ae_drv_one h44 hκ hκ4 hb hh hE hreg hc₀J hc₀ hL0 hR0 hL hR hθ hθπ] with ω h0 h1
  have e0 : E 0 ω = D₀ (h ω) := by
    refine Prod.ext (funext fun t => ?_) h0.2.1.symm
    refine (h0.2.2 t ?_).symm
    rw [h0.1]; exact ENNReal.coe_lt_top
  refine ⟨h0.1, h1.1, e0, ?_⟩
  rw [e0] at h1
  refine Prod.ext (funext fun t => ?_) h1.2.1.symm
  refine (h1.2.2 t ?_).symm
  rw [h1.1]; exact ENNReal.coe_lt_top

/-- **`hdet` for the angle-varying path** (Lemma 6.2's determination input, §5.1 (i) of PROVE-STRIPSYS19). Every
path `αc` that is almost surely a generating trace of the concatenated driver on `[0, ∞)` is, at every time, almost
surely a Borel function of the centred field `h − 𝔥₀`. -/
theorem hdet_of_trace (h44 : Theorem12ParamCond44Statement.{u}) (hκ : 0 < κ) (hκ4 : κ < 4)
    (hb : IsPiecewiseConstantBoundaryData b jumps) (hh : IsGFFWithBoundaryData P h b jumps)
    (hE : IsStagedHistory κ b jumps P h (StripSys.twoAngleSpec θ₀ t₀ θ) E) (hreg : ∀ j ω, IsRegularDriver (E j ω))
    (hL0 : ∀ y : ℝ, y < 0 → y ∉ jumps → b y + θ₀ * chiC κ ≤ -sleLambda κ + Real.pi * chiC κ)
    (hR0 : ∀ y : ℝ, 0 < y → y ∉ jumps → sleLambda κ ≤ b y + θ₀ * chiC κ)
    (hL : ∀ y : ℝ, y < 0 → y ∉ jumps → b y + θ * chiC κ ≤ -sleLambda κ + Real.pi * chiC κ)
    (hR : ∀ y : ℝ, 0 < y → y ∉ jumps → sleLambda κ ≤ b y + θ * chiC κ) (hθ : θ₀ ≤ θ)
    (hθπ : θ ≤ θ₀ + Real.pi) (u₀ : ℂ → ℝ) {αc : Ω → ℝ≥0 → ℂ}
    (htr : ∀ᵐ ω ∂P, IsGeneratingTrace (catPath (E 0 ω).1 t₀ (E 1 ω).1) ⊤ (αc ω)) :
    ∀ t : ℝ≥0, ∃ f : DistOn upperHalfPlaneOpens → ℂ, Measurable f ∧
      (fun ω => αc ω t) =ᵐ[P] fun ω => f (WholeField.centredField h u₀ ω) := by
  obtain ⟨D₀, D₁, hD₀, hD₁, hD₀r, hD₁r, hD⟩ :=
    exists_borel_drivers h44 hκ hκ4 hb hh hE hreg hL0 hR0 hL hR hθ hθπ
  intro t
  set c : DistOn upperHalfPlaneOpens := smoothDist upperHalfPlaneOpens u₀ with hc
  have hadd : Measurable fun g : DistOn upperHalfPlaneOpens => g + c := Coupling.measurable_add_distOnConst c
  refine ⟨fun g => LP.traceAt t (catPath (D₀ (g + c)).1 t₀ (D₁ (g + c)).1), ?_, ?_⟩
  · exact (LP.measurable_traceAt t).comp ((measurable_catPath t₀).comp
      ((measurable_fst.comp (hD₀.comp hadd)).prodMk (measurable_fst.comp (hD₁.comp hadd))))
  · filter_upwards [hD, htr] with ω hω hη
    obtain ⟨h0, h1, e0, e1⟩ := hω
    have hcent : WholeField.centredField h u₀ ω + c = h ω := by
      simp only [WholeField.centredField, hc, sub_add_cancel]
    simp only [hcent, ← e0, ← e1]
    have hc0 : Continuous (E 0 ω).1 := by
      have := (hreg 0 ω).1
      rw [h0] at this
      exact continuousOn_univ.1 (by simpa using this)
    have hc1 : Continuous (E 1 ω).1 := by
      have := (hreg 1 ω).1
      rw [h1] at this
      exact continuousOn_univ.1 (by simpa using this)
    exact (LP.traceAt_eq_of_isGeneratingTrace hη (continuous_catPath hc0 hc1 (hreg 1 ω).2.1).continuousOn
      (catPath_zero (hreg 0 ω).2.1) ENNReal.coe_lt_top).symm

end Strip

end StripDet

end Sec7

end InteractingSLE
