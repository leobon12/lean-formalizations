/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec5.Aux61NestAccess

/-!
# Assembly of the fibre cover: the nested conditioning algebras

Packet PROVE-AUX61-ASSEMBLE. The conditioning σ-algebra at fibre time `q` is the germ of the live
marked set at `q`, joined with the marks at `q` and the germ of the live marked set at time `0`
(`asmSigma`). The decompositions at every fibre time exist by NEST's pair theorem (from the
physical marked local sets), and the time-`0` algebra is contained in every later one.

An a.e. congruence for `IsChartGaussAt` lets a caller replace the decomposition at time `0` by any
measurable version that agrees with it almost surely on the live event.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter
open QuantumZipper (H)
open LQGMetric (DistOn TestOn IsZeroBoundaryGFF)
open scoped NNReal ENNReal

namespace InteractingSLE.Sec5.Aux61Asm

open Aux61Fib (FibCode)
open Aux61FibK (codeFiltration)
open Aux61FibData (IsRestartSpec IsMeasChart)
open Aux61GInst (HasAccessLanding accessExitCode)
open Aux61ChLoc (IsChartGaussAt liveEv liveSet measurableSet_live)
open Aux61UnionK (chartHull norm_cexp_I_mul_ofReal_le measurable_field_apply measurable_apply_of_measurable)
open LocalSets (germSigma)
open WholeField (IsHistoryAvoidanceLocal centredField)

universe u

section Congr

variable {X : Type u} {𝒢 : MeasurableSpace X} [mX : MeasurableSpace X]
  {β : Type*} [mβ : MeasurableSpace β]

/-- **A.e. congruence of the chart decomposition.** A `𝒢`-measurable version of the harmonic part
that agrees with it almost surely on the live event is again a decomposition given `𝒢`. -/
theorem isChartGaussAt_congr_ae {μ : Measure X} [IsFiniteMeasure μ] {Z : X → β} {B : Set β}
    (hB : MeasurableSet B) {Y : X → FibCode} (hY : Measurable Y) {q : ℝ≥0}
    {g g' : X → DistOn upperHalfPlaneOpens} (hG : IsChartGaussAt μ Z B Y q 𝒢 g)
    (hg' : Measurable[𝒢] g')
    (heq : ∀ᵐ x ∂μ, Z x ∈ B → (q : ℝ≥0∞) < (Y x).life → g' x = g x) :
    IsChartGaussAt μ Z B Y q 𝒢 g' where
  le := hG.le
  marksZ := hG.marksZ
  marksY := hG.marksY
  measurable := hg'
  harmonic := by
    filter_upwards [hG.harmonic, heq] with x hx he hxB hxq
    rw [he hxB hxq]
    exact hx hxB hxq
  gff φ := by
    have hS : MeasurableSet[𝒢] (liveEv Z B Y q) := measurableSet_live hG.marksZ hG.marksY hB
    have hgm : Measurable g := hG.measurable.mono hG.le le_rfl
    have hg'm : Measurable g' := hg'.mono hG.le le_rfl
    set f : X → ℂ := fun x' => Complex.exp (Complex.I * (((Y x').field φ - g x' φ : ℝ) : ℂ)) with hf
    set f' : X → ℂ := fun x' => Complex.exp (Complex.I * (((Y x').field φ - g' x' φ : ℝ) : ℂ))
      with hf'
    have hfi : Integrable f μ := Integrable.of_bound
      (Complex.measurable_exp.comp (measurable_const.mul (Complex.measurable_ofReal.comp
        ((measurable_field_apply hY φ).sub (measurable_apply_of_measurable hgm φ))))).aestronglyMeasurable
      1 (ae_of_all _ fun x => norm_cexp_I_mul_ofReal_le _)
    have hf'i : Integrable f' μ := Integrable.of_bound
      (Complex.measurable_exp.comp (measurable_const.mul (Complex.measurable_ofReal.comp
        ((measurable_field_apply hY φ).sub (measurable_apply_of_measurable hg'm φ))))).aestronglyMeasurable
      1 (ae_of_all _ fun x => norm_cexp_I_mul_ofReal_le _)
    have h3 : (liveEv Z B Y q).indicator f' =ᵐ[μ] (liveEv Z B Y q).indicator f := by
      filter_upwards [heq] with x hx
      by_cases hxS : x ∈ liveEv Z B Y q
      · rw [indicator_of_mem hxS, indicator_of_mem hxS]
        simp only [hf, hf', hx hxS.1 hxS.2]
      · rw [indicator_of_notMem hxS, indicator_of_notMem hxS]
    have h4 := condExp_congr_ae (m := 𝒢) h3
    filter_upwards [condExp_indicator (m := 𝒢) hf'i hS, condExp_indicator (m := 𝒢) hfi hS, h4, hG.gff φ]
      with x e1 e2 e4 e5 hxB hxq
    have hxS : x ∈ liveEv Z B Y q := ⟨hxB, hxq⟩
    have e6 : (liveEv Z B Y q).indicator (μ[f' | 𝒢]) x = (liveEv Z B Y q).indicator (μ[f | 𝒢]) x := by
      rw [← e1, e4, e2]
    rw [indicator_of_mem hxS, indicator_of_mem hxS] at e6
    rw [e6]
    exact e5 hxB hxq

end Congr

section Sigma

variable {X : Type u} [mX : MeasurableSpace X] {β : Type*} [mβ : MeasurableSpace β]

/-- **The conditioning σ-algebra at fibre time `q`**: the germ of the live marked set at `q`, the marks at
`q`, and the germ of the live marked set at time `0` (retained so that the algebras are nested). -/
@[instance_reducible]
def asmSigma (Z : X → β) (B : Set β) (Y : X → FibCode) (A : ℝ≥0 → X → Set ℂ)
    (ℋ : ℝ≥0 → MeasurableSpace X) (h : X → DistOn upperHalfPlaneOpens) (q : ℝ≥0) : MeasurableSpace X :=
  germSigma (liveSet (liveEv Z B Y q) (A q)) h ⊔ (ℋ q ⊔ germSigma (liveSet (liveEv Z B Y 0) (A 0)) h)

omit mX mβ in
/-- The time-`0` conditioning algebra is contained in every later one. -/
theorem asmSigma_zero_le {Z : X → β} {B : Set β} {Y : X → FibCode} {A : ℝ≥0 → X → Set ℂ}
    {ℋ : ℝ≥0 → MeasurableSpace X} (h : X → DistOn upperHalfPlaneOpens) {q : ℝ≥0} (hℋ : ℋ 0 ≤ ℋ q) :
    asmSigma Z B Y A ℋ h 0 ≤ asmSigma Z B Y A ℋ h q :=
  sup_le (le_sup_right.trans le_sup_right)
    (sup_le (hℋ.trans (le_sup_left.trans le_sup_right)) (le_sup_right.trans le_sup_right))

/-- **The decompositions at every fibre time** for the selected-access restart code, from the physical marked
local sets: NEST's pair theorem with the time-`0` set and marks as the retained ones. -/
theorem exists_isChartGaussAt_asmSigma
    {μ : Measure X} [IsProbabilityMeasure μ] {Z : X → β} {B : Set β}
    (hB : MeasurableSet B) {Er : Set X} {c : X → Chart}
    {ρ : X → ℝ≥0 → ℂ} {T : X → ℝ≥0∞} {V : Set ℂ} {a k : ℝ}
    (hs : IsRestartSpec Er c ρ T) (hVo : IsOpen V) (hV0 : (0 : ℂ) ∈ V)
    (hland : HasAccessLanding Er c ρ T V)
    (hinj : ∀ x ∈ Er, InjOn (ρ x) {r | (r : ℝ≥0∞) < T x})
    (hliftc : ∀ x ∈ Er, ContinuousOn (c x).2.2 (c x).dom)
    (hlift : ∀ x ∈ Er, InnerProductSpace.HarmonicOnNhd (c x).2.2 (c x).dom)
    {h : X → DistOn upperHalfPlaneOpens} (hhm : Measurable h) {u₀ : ℂ → ℝ}
    (hu₀ : InnerProductSpace.HarmonicOnNhd u₀ H)
    (hh0 : IsZeroBoundaryGFF upperHalfPlaneOpens (centredField h u₀) μ)
    {ℋ : ℝ≥0 → MeasurableSpace X} {A : ℝ≥0 → X → Set ℂ}
    (hℋ : ∀ r, ℋ r ≤ mX) (hℋmono : ∀ r, ℋ 0 ≤ ℋ r) (hZℋ : mβ.comap Z ≤ ℋ 0)
    (hYℋ : ∀ r : ℝ≥0, (codeFiltration.{u} r).comap
      (fun x => ULift.up.{u} (accessExitCode Er c ρ T V a k h x)) ≤ ℋ r)
    (hEℋ : MeasurableSet[ℋ 0] Er) (hcℋ : @IsMeasChart X (ℋ 0) c)
    (hA0m : Measurable[ℋ 0, hittingSigma] (A 0)) (hAm : ∀ r, Measurable[mX, hittingSigma] (A r))
    (hAc : ∀ r x, A r x ⊆ H ∧ IsOpen (H \ A r x)) (hAmono : ∀ r x, A 0 x ⊆ A r x)
    (hloc : ∀ r, IsHistoryAvoidanceLocal (ℋ r) (A r) (centredField h u₀) μ)
    (hgeo : ∀ r : ℝ≥0, ∀ᵐ x ∂μ, Z x ∈ B → (r : ℝ≥0∞) < (accessExitCode Er c ρ T V a k h x).life →
      H \ A r x = (c x).2.1 '' (H \ chartHull (accessExitCode Er c ρ T V a k h) r x))
    (q : ℝ≥0) :
    ∃ g : X → DistOn upperHalfPlaneOpens, IsChartGaussAt μ Z B (accessExitCode Er c ρ T V a k h) q
      (asmSigma Z B (accessExitCode Er c ρ T V a k h) A ℋ (centredField h u₀) q) g := by
  obtain ⟨-, g, -, hg, -⟩ := Aux61Nest.exists_isChartGaussAt_pair_accessExit hB hs hVo hV0 hland hinj
    hliftc hlift hhm hu₀ hh0 q (hℋ q) (hℋmono q) hZℋ (hYℋ 0) (hYℋ q) hEℋ hcℋ hA0m (hAm q) (hAc 0) (hAc q)
    (hAmono q) (hloc 0) (hloc q) (hgeo 0) (hgeo q)
  exact ⟨g, hg⟩

end Sigma

end InteractingSLE.Sec5.Aux61Asm
