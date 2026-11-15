/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec5.Aux61GInstAccessCover
import InteractingSLE.Spec.Sec5.Aux61ChLocRestart

/-! # Marked Gaussian chart decompositions for selected-access codes -/

set_option autoImplicit false
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter Topology Function
open QuantumZipper (H)
open LQGMetric (DistOn TestOn IsZeroBoundaryGFF)
open scoped NNReal ENNReal

namespace InteractingSLE.Sec5.Aux61GInst
open Aux61ChLoc
open Aux61Fib (FibCode FibData fibW)
open Aux61FibK (codeFiltration)
open Aux61FibData (IsRestartSpec IsMeasChart exitEv chartOf clr visitSet)
open Aux61UnionK (chartHull IsChartLocalAt canonMean HasFibreLocalCover)
open Aux61Win (IsCutoffOn)
open LocalSets (germSigma)
open WholeField (IsHistoryAvoidanceLocal centredField)
open Restart.FlowStopIdentCMI (CMCut)
universe u

section Exit

variable {X : Type u} {ℋ : MeasurableSpace X} [mX : MeasurableSpace X] {β : Type*} [mβ : MeasurableSpace β]
  {Er : Set X} {c : X → Chart} {ρ : X → ℝ≥0 → ℂ} {T : X → ℝ≥0∞} {V : Set ℂ} {a k : ℝ}
  {h : X → DistOn upperHalfPlaneOpens}

omit mX in
/-- **The restart code is alive only inside the exit event.** -/
theorem mem_exitEv_of_lt_accessLife {x : X} {q : ℝ≥0} (hq : (q : ℝ≥0∞) < (accessExitCode Er c ρ T V a k h x).life) :
    x ∈ exitEv Er c ρ T V := by
  by_contra hx
  have e : (accessExitCode Er c ρ T V a k h x).life = 0 := by
    simp only [accessExitCode_life, Aux61FibData.capEnd, hx, ↓reduceIte]
  rw [e] at hq
  exact ENNReal.not_lt_zero hq

omit mX in
/-- **The field of the restart code** on the exit event is the chart transport of the field by `chartOf Er c`. -/
theorem accessExitCode_field_eq (hconf : ∀ x ∈ Er, (c x).IsConformal) {x : X} (hx : x ∈ exitEv Er c ρ T V) :
    (accessExitCode Er c ρ T V a k h x).field =
      Chart.chartTransport (Aux61FibData.isConformal_chartOf hconf x) 1 a k (h x) := by
  have hxE : x ∈ Er := hx.1.1
  change Aux61FibData.chartFieldOf (exitEv Er c ρ T V) c a k h x = _
  rw [Aux61FibData.chartFieldOf, Aux61FibData.chartOf_of_mem hx, ← chartField_eq_chartTransport,
    Aux61FibData.chartOf_of_mem hxE]

/-- **(K-a) for the restart code from the physical marked local set.** The restart data of PROVE-AUX61-FIBDATA with a
harmonic lift; the field `h` with `h − u₀` a zero-boundary GFF; marks `ℋ` containing the history `Z`, the raw code at
`q`, the restart event and the restart chart; a hitting-measurable relatively closed physical set `A` satisfying the
history-marked avoidance criterion for `ℋ`, with `ℍ ∖ A = c⁻¹(ℍ ∖ K_q)` on the live event. -/
theorem exists_isChartGaussAt_accessExit {μ : Measure X} [IsProbabilityMeasure μ] {Z : X → β} {B : Set β}
    (hB : MeasurableSet B) (hs : IsRestartSpec Er c ρ T) (hVo : IsOpen V) (hV0 : (0 : ℂ) ∈ V)
    (hland : HasAccessLanding Er c ρ T V) (hinj : ∀ x ∈ Er, InjOn (ρ x) {u | (u : ℝ≥0∞) < T x})
    (hliftc : ∀ x ∈ Er, ContinuousOn (c x).2.2 (c x).dom)
    (hlift : ∀ x ∈ Er, InnerProductSpace.HarmonicOnNhd (c x).2.2 (c x).dom)
    (hhm : Measurable h) {u₀ : ℂ → ℝ} (hu₀ : InnerProductSpace.HarmonicOnNhd u₀ H)
    (hh0 : IsZeroBoundaryGFF upperHalfPlaneOpens (centredField h u₀) μ) (q : ℝ≥0)
    (hℋ : ℋ ≤ mX) (hZℋ : mβ.comap Z ≤ ℋ)
    (hYℋ : (codeFiltration.{u} q).comap (fun x => ULift.up.{u} (accessExitCode Er c ρ T V a k h x)) ≤ ℋ)
    (hEℋ : MeasurableSet[ℋ] Er) (hcℋ : @IsMeasChart X ℋ c)
    {A : X → Set ℂ} (hAm : Measurable[mX, hittingSigma] A) (hAc : ∀ x, A x ⊆ H ∧ IsOpen (H \ A x))
    (hloc : IsHistoryAvoidanceLocal ℋ A (centredField h u₀) μ)
    (hgeo : ∀ᵐ x ∂μ, Z x ∈ B → (q : ℝ≥0∞) < (accessExitCode Er c ρ T V a k h x).life →
      H \ A x = (c x).2.1 '' (H \ chartHull (accessExitCode Er c ρ T V a k h) q x)) :
    ∃ h₁ : X → DistOn upperHalfPlaneOpens, IsChartGaussAt μ Z B (accessExitCode Er c ρ T V a k h) q
      (germSigma (liveSet (liveEv Z B (accessExitCode Er c ρ T V a k h) q) A) (centredField h u₀) ⊔ ℋ) h₁ := by
  have hcm := @IsMeasChart.chartOf X ℋ Er hEℋ c hcℋ
  refine exists_isChartGaussAt_of_marked hB (measurable_accessExitCode hs hVo hV0 hland hinj hliftc hhm) q hhm hu₀
    hh0 (Aux61FibData.isConformal_chartOf hs.conf) a k (fun x _ hq => accessExitCode_field_eq hs.conf
      (mem_exitEv_of_lt_accessLife hq)) hℋ hZℋ hYℋ (@IsMeasChart.dom X ℋ _ hcm) (@IsMeasChart.fwd X ℋ _ hcm)
    (@IsMeasChart.lift X ℋ _ hcm) (continuousOn_lift_chartOf hliftc) (harmonicOnNhd_lift_chartOf hlift) hAm hAc
    hloc ?_
  filter_upwards [hgeo] with x hx hxB hq
  rw [Aux61FibData.chartOf_of_mem (mem_exitEv_of_lt_accessLife hq).1.1]
  exact hx hxB hq

end Exit

/-! ### The fibre-local cover -/

section Cover

variable {X : Type u} [mX : MeasurableSpace X] {ι : Type} [Countable ι] {β : ι → Type u}
  [mβ : ∀ i, MeasurableSpace (β i)]

/-- **The fibre-local cover from (K-a) in chart form and the mean identification**: the restart data of
`hasFibreLocalCover_of_accessRestart`, and at every index `i` and fibre time `r` a conditional Gaussian
decomposition `(𝒢 i r, h₁ i r)` of the chart field of the restart code whose harmonic part pairs like the canonical
(PC1) mean off the chart hull. -/
theorem hasFibreLocalCover_of_accessRestart_gauss {μ : Measure X} [IsFiniteMeasure μ] {E : X → Prop}
    (Z : ∀ i, X → β i) (hZ : ∀ i, Measurable (Z i)) (B : ∀ i, Set (β i)) (hB : ∀ i, MeasurableSet (B i))
    (Er : ι → Set X) (c : ι → X → Chart) (ρ : ι → X → ℝ≥0 → ℂ) (T : ι → X → ℝ≥0∞)
    (hs : ∀ i, IsRestartSpec (Er i) (c i) (ρ i) (T i)) (V : ι → Set ℂ) (hVo : ∀ i, IsOpen (V i))
    (hV0 : ∀ i, (0 : ℂ) ∈ V i) (hland : ∀ i, HasAccessLanding (Er i) (c i) (ρ i) (T i) (V i))
    (hinj : ∀ i, ∀ x ∈ Er i, InjOn (ρ i x) {u | (u : ℝ≥0∞) < T i x})
    (hliftc : ∀ i, ∀ x ∈ Er i, ContinuousOn (c i x).2.2 (c i x).dom)
    (h : X → DistOn upperHalfPlaneOpens) (hh : Measurable h) (a k : ℝ)
    (d : ∀ i, β i → FibData) (hdV : ∀ i z, (d i z).V = V i) (hdℓ : ∀ i z, (d i z).ℓ = clr (V i))
    (p q : ι → ℝ) (hRef : ∀ i, ∀ z ∈ B i, Aux61Cov.RefWin (d i z).κ (d i z).bR (d i z).JR (Ioo (p i) (q i)))
    (hexit : ∀ i, ∀ᵐ x ∂μ, Z i x ∈ B i → x ∈ exitEv (Er i) (c i) (ρ i) (T i) (V i))
    (hcover : ∀ᵐ x ∂μ, E x → ∃ i, Z i x ∈ B i)
    (hE : ∀ i, ∀ᵐ x ∂μ, Z i x ∈ B i → E x →
      accessExitCode (Er i) (c i) (ρ i) (T i) (V i) a k h x ∈ visitSet (p i) (q i))
    (F₀ : ∀ i, β i → CMCut) (N₀ : ∀ i, β i → Set ℂ)
    (hcut : ∀ i, ∀ z ∈ B i, IsCutoffOn (F₀ i z) (d i z).q (N₀ i z) (d i z).O₀ ∧ (d i z).buffer ⊆ N₀ i z)
    (κ₀ : ι → ℝ) (bR₀ : ι → ℝ → ℝ) (JR₀ : ι → Finset ℝ)
    (hword : ∀ i z, (d i z).κ = κ₀ i ∧ (d i z).bR = bR₀ i ∧ (d i z).JR = JR₀ i)
    (hqm : ∀ i, Measurable fun p : β i × ℂ => (d i p.1).q p.2)
    (hfm : ∀ i, Measurable fun p : β i × ℂ => (F₀ i p.1).f p.2)
    (hsrc : ∀ i, Measurable fun p : β i × ℂ => QuantumZipper.K3.greenDensity (F₀ i p.1).f p.2)
    (𝒢 : ι → ℝ≥0 → MeasurableSpace X) (h₁ : ι → ℝ≥0 → X → DistOn upperHalfPlaneOpens)
    (hG : ∀ i (r : ℝ≥0), IsChartGaussAt μ (Z i) (B i) (accessExitCode (Er i) (c i) (ρ i) (T i) (V i) a k h) r (𝒢 i r)
      (h₁ i r))
    (hmean : ∀ i (r : ℝ≥0), ∀ᵐ x ∂μ, Z i x ∈ B i →
      (r : ℝ≥0∞) < (accessExitCode (Er i) (c i) (ρ i) (T i) (V i) a k h x).life → ∀ ψ : TestOn upperHalfPlaneOpens,
      Disjoint (tsupport ψ) (chartHull (accessExitCode (Er i) (c i) (ρ i) (T i) (V i) a k h) r x) →
      h₁ i r x ψ = ∫ z, canonMean (d i (Z i x)) (F₀ i (Z i x))
        (ULift.up.{u} (accessExitCode (Er i) (c i) (ρ i) (T i) (V i) a k h x)) r z * ψ z) :
    HasFibreLocalCover μ E :=
  hasFibreLocalCover_of_accessRestart Z hZ B hB Er c ρ T hs V hVo hV0 hland hinj hliftc h hh a k d hdV hdℓ
    p q hRef hexit hcover hE F₀ N₀ hcut κ₀ bR₀ JR₀ hword hqm hfm hsrc h₁ fun i r =>
      (hG i r).isChartLocalAt (measurable_accessExitCode (hs i) (hVo i) (hV0 i) (hland i) (hinj i) (hliftc i) hh)
        (hB i) (hmean i r)

/-- **The fibre-local cover from the physical marked local sets and Aux. lemma 61's mean.** The restart data of
`hasFibreLocalCover_of_accessRestart` with harmonic lifts; the field `h` with `h − u₀` a zero-boundary GFF; at
every index `i` and fibre time `r`: marks `ℋ i r` containing the history, the raw code at `r`, the restart event and
the restart chart; a physical set `A i r` satisfying the history-marked avoidance criterion for `ℋ i r` with
`ℍ ∖ A = c⁻¹(ℍ ∖ K_r)` on the live event (K-a); and (K-b) for the conditioning σ-algebra `𝒜_{A'} ∨ ℋ i r` with the
canonical (PC1) mean. -/
theorem hasFibreLocalCover_of_accessRestart_marked {μ : Measure X} [IsProbabilityMeasure μ] {E : X → Prop}
    (Z : ∀ i, X → β i) (hZ : ∀ i, Measurable (Z i)) (B : ∀ i, Set (β i)) (hB : ∀ i, MeasurableSet (B i))
    (Er : ι → Set X) (c : ι → X → Chart) (ρ : ι → X → ℝ≥0 → ℂ) (T : ι → X → ℝ≥0∞)
    (hs : ∀ i, IsRestartSpec (Er i) (c i) (ρ i) (T i)) (V : ι → Set ℂ) (hVo : ∀ i, IsOpen (V i))
    (hV0 : ∀ i, (0 : ℂ) ∈ V i) (hland : ∀ i, HasAccessLanding (Er i) (c i) (ρ i) (T i) (V i))
    (hinj : ∀ i, ∀ x ∈ Er i, InjOn (ρ i x) {u | (u : ℝ≥0∞) < T i x})
    (hliftc : ∀ i, ∀ x ∈ Er i, ContinuousOn (c i x).2.2 (c i x).dom)
    (hlift : ∀ i, ∀ x ∈ Er i, InnerProductSpace.HarmonicOnNhd (c i x).2.2 (c i x).dom)
    (h : X → DistOn upperHalfPlaneOpens) (hh : Measurable h) (a k : ℝ)
    (d : ∀ i, β i → FibData) (hdV : ∀ i z, (d i z).V = V i) (hdℓ : ∀ i z, (d i z).ℓ = clr (V i))
    (p q : ι → ℝ) (hRef : ∀ i, ∀ z ∈ B i, Aux61Cov.RefWin (d i z).κ (d i z).bR (d i z).JR (Ioo (p i) (q i)))
    (hexit : ∀ i, ∀ᵐ x ∂μ, Z i x ∈ B i → x ∈ exitEv (Er i) (c i) (ρ i) (T i) (V i))
    (hcover : ∀ᵐ x ∂μ, E x → ∃ i, Z i x ∈ B i)
    (hE : ∀ i, ∀ᵐ x ∂μ, Z i x ∈ B i → E x →
      accessExitCode (Er i) (c i) (ρ i) (T i) (V i) a k h x ∈ visitSet (p i) (q i))
    (F₀ : ∀ i, β i → CMCut) (N₀ : ∀ i, β i → Set ℂ)
    (hcut : ∀ i, ∀ z ∈ B i, IsCutoffOn (F₀ i z) (d i z).q (N₀ i z) (d i z).O₀ ∧ (d i z).buffer ⊆ N₀ i z)
    (κ₀ : ι → ℝ) (bR₀ : ι → ℝ → ℝ) (JR₀ : ι → Finset ℝ)
    (hword : ∀ i z, (d i z).κ = κ₀ i ∧ (d i z).bR = bR₀ i ∧ (d i z).JR = JR₀ i)
    (hqm : ∀ i, Measurable fun p : β i × ℂ => (d i p.1).q p.2)
    (hfm : ∀ i, Measurable fun p : β i × ℂ => (F₀ i p.1).f p.2)
    (hsrc : ∀ i, Measurable fun p : β i × ℂ => QuantumZipper.K3.greenDensity (F₀ i p.1).f p.2)
    {u₀ : ℂ → ℝ} (hu₀ : InnerProductSpace.HarmonicOnNhd u₀ H)
    (hh0 : IsZeroBoundaryGFF upperHalfPlaneOpens (centredField h u₀) μ)
    (ℋ : ι → ℝ≥0 → MeasurableSpace X) (hℋ : ∀ i r, ℋ i r ≤ mX) (hZℋ : ∀ i r, (mβ i).comap (Z i) ≤ ℋ i r)
    (hYℋ : ∀ i (r : ℝ≥0),
      (codeFiltration.{u} r).comap (fun x => ULift.up.{u} (accessExitCode (Er i) (c i) (ρ i) (T i) (V i) a k h x)) ≤
        ℋ i r)
    (hEℋ : ∀ i r, MeasurableSet[ℋ i r] (Er i)) (hcℋ : ∀ i r, @IsMeasChart X (ℋ i r) (c i))
    (A : ι → ℝ≥0 → X → Set ℂ) (hAm : ∀ i r, Measurable[mX, hittingSigma] (A i r))
    (hAc : ∀ i r x, A i r x ⊆ H ∧ IsOpen (H \ A i r x))
    (hloc : ∀ i r, IsHistoryAvoidanceLocal (ℋ i r) (A i r) (centredField h u₀) μ)
    (hgeo : ∀ i (r : ℝ≥0), ∀ᵐ x ∂μ, Z i x ∈ B i →
      (r : ℝ≥0∞) < (accessExitCode (Er i) (c i) (ρ i) (T i) (V i) a k h x).life →
      H \ A i r x = (c i x).2.1 '' (H \ chartHull (accessExitCode (Er i) (c i) (ρ i) (T i) (V i) a k h) r x))
    (hKb : ∀ i (r : ℝ≥0), IsChartMeanAt μ (Z i) (B i) (accessExitCode (Er i) (c i) (ρ i) (T i) (V i) a k h) r
      (germSigma (liveSet (liveEv (Z i) (B i) (accessExitCode (Er i) (c i) (ρ i) (T i) (V i) a k h) r) (A i r))
        (centredField h u₀) ⊔ ℋ i r)
      (fun x => canonMean (d i (Z i x)) (F₀ i (Z i x))
        (ULift.up.{u} (accessExitCode (Er i) (c i) (ρ i) (T i) (V i) a k h x)) r)) :
    HasFibreLocalCover μ E := by
  choose h₁ hG using fun i (r : ℝ≥0) => exists_isChartGaussAt_accessExit (Z := Z i) (hB i) (hs i) (hVo i) (hV0 i)
    (hland i) (hinj i) (hliftc i) (hlift i) (a := a) (k := k) hh hu₀ hh0 r (hℋ i r) (hZℋ i r) (hYℋ i r) (hEℋ i r)
    (hcℋ i r) (hAm i r) (hAc i r) (hloc i r) (hgeo i r)
  exact hasFibreLocalCover_of_accessRestart_gauss Z hZ B hB Er c ρ T hs V hVo hV0 hland hinj hliftc h hh a k d hdV hdℓ
    p q hRef hexit hcover hE F₀ N₀ hcut κ₀ bR₀ JR₀ hword hqm hfm hsrc _ h₁ hG fun i r => hKb i r (h₁ i r) (hG i r)

end Cover

end InteractingSLE.Sec5.Aux61GInst
