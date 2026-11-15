/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Jordan.Transport
import InteractingSLE.Frozen.Spec.IsCenteredCounterflowDriver
import InteractingSLE.Frozen.Spec.IsGFFWithBoundaryData
import InteractingSLE.Frozen.Spec.IsGeneratingTrace
import InteractingSLE.Frozen.Spec.IsPiecewiseConstantBoundaryData
import InteractingSLE.GFF.LocalSets.Characterization
import Mathlib.Probability.Kernel.Condexp

/-!
# Couplings in a domain with two marked prime ends

Packet PROVE-JORDANCPL. The carriers shared by supplement GB6 (`source/spec/p481-528.md` L929–L975), the
non-boundary couplings of Remarks 6.9–6.10 and Aux. 32–37 (`source/spec/p145-192.md` L608–L626, L778–L1000), and the
pocket kernels of Aux. 119–125. In each, the field and the curves live in a domain `D` with two marked boundary points
and are read in a conformal chart of `D` (Specification p. 2: "the field in the new coordinate is
`h ∘ ψ − χ Im L_ψ`", (1.4)); the curve laws are the half-plane ones in that chart (Aux. 32: "compactified by a fixed
conformal map to a Jordan domain"; GB6: "Work first in the original flow chart `(D, x, y) = (ℍ, 0, ∞)`").

Fields are random distributions on `ℍ` (the original chart); a domain `D ⊆ ℍ` is the image `inv '' ℍ` of a chart
`c` (`IsDomainChart`), and the field in `D` read in `c` is the frozen `IsChartTransport`. Boundary points are prime
ends (`IsDomainChartAt`).

## Main definitions

* `ownComponentChart W σ`: the chart of the flow's own target component `U = ℍ \ K_σ` taking `(∞, tip)` to `(0, ∞)`:
  the own hydrodynamic chart `f_σ` followed by `I(z) = −1/z` with `L_I = −2 Log z` (GB6 proof, first paragraph);
* `IsDomainFlowLine κ D x y c b J θ P h W ζ`: `W` drives the angle-`θ` flow line of `h` in `D` from `x` towards `y`,
  read in a chart `c` of `D` taking `x, y` to `0, ∞` (frozen `IsFlowLineDriver` of the field read in `c`);
* `IsDomainCounterflow κ D x y c b J P h W ζ`: in that chart the field is a GFF with data `b` and `W` drives its
  centred counterflow from `y` to `x` (frozen `IsCenteredCounterflowDriver`: Theorem 1.1's coupling of
  `F = −h − πχ` at `16/κ` in the inversion);
* `IsCompleteTransientTrace W ζ`: infinite lifetime and a continuous transient generating trace (GB6: "its complete
  continuous transient trace");
* `IsCondChartField 𝒢 σ a k P h c bc jc`: conditionally on `𝒢`, the field read in the (𝒢-random) chart `c` with the
  rule `(σ, a, k)` is a GFF with the data `bc` (the "conditional component field … in the chart of `U`", GB6; the
  conditional laws of Aux. 32–37 and 119–125);
* `IsMarkedLocalSetLaw 𝒢 A h P`: the marked local-set law (Specification §3.2, Lemma 3.6 (iii) with the retained
  labels: conditionally on the marked σ-algebra `𝒢 ⊇` germ σ-algebra, `h = h₁ + h₂`, `h₁` harmonic off `A`,
  `h₂` a zero-boundary GFF on `ℍ \ A`).

## Main results

* `isDomainChart_loewner`, `isDomainChart_infinitySourceChart`, **`isDomainChart_ownComponentChart`**;
* `isChartTransport_id`, `isDomainFlowLine_id_iff`, `isDomainCounterflow_id_iff`: in `ℍ` with the identity chart the
  carriers are the frozen half-plane predicates;
* `isCondChartField_trans_iff`: restriction to a subdomain (reading the conditional field in a further chart);
* `IsMarkedLocalSetLaw.of_isGermConditionalLaw`: Lemma 3.6 (iii) is the marked law with the germ σ-algebra.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped NNReal ENNReal
open QuantumZipper (H isOpen_H fwdHull fwdMap fwdMapInv)
open LQGMetric (TestOn DistOn)

universe u

namespace InteractingSLE

/-! ### The charts of GB6 -/

/-- The centred Loewner chart `f_t` of a continuous driver is a chart of `ℍ \ K_t`, with the hydrodynamic lift. -/
theorem isDomainChart_loewner {W : ℝ → ℝ} (hW : Continuous W) (hW0 : W 0 = 0) {t : ℝ} (ht : 0 ≤ t) :
    IsDomainChart (H \ fwdHull W t) (Chart.id.loewner W t) := by
  refine ⟨Chart.isConformal_id.loewner hW hW0 ht, QuantumZipper.RS.image_fwdMapInv_H hW hW0 ht,
    QuantumZipper.logDerivFwd W t, isDerivLog_fwdMap hW ht, fun z _ => ?_⟩
  change (QuantumZipper.logDerivFwd W t z).im + 0 = (QuantumZipper.logDerivFwd W t z).im
  rw [add_zero]

/-- The inversion `I(z) = −1/z` with `L_I = −2 Log z` (FD12.1) is a chart of `ℍ`. -/
theorem isDomainChart_infinitySourceChart : IsDomainChart H infinitySourceChart := by
  refine ⟨Chart.isConformal_infinitySourceChart, ?_, fun z => -2 * Complex.log z, isDerivLog_neg_inv,
    fun _ _ => rfl⟩
  refine Subset.antisymm ?_ fun w hw => ⟨-w⁻¹, Chart.isConformal_infinitySourceChart.2.1 hw, ?_⟩
  · rintro _ ⟨w, hw, rfl⟩
    exact Chart.isConformal_infinitySourceChart.2.1 hw
  · change -(-w⁻¹)⁻¹ = w
    rw [inv_neg, inv_inv, neg_neg]

/-- **The chart of the flow's own target component** (GB6, proof: "Map its current flow tip to zero with the own
hydrodynamic chart, and then use `I(z) = −1/z` to take its tip to infinity and `y` to zero. Use `L_I = −2 Log z`"):
`fwd = −1/f_σ`, `inv = f_σ⁻¹ ∘ I`, lift `Im(−2 Log f_σ) + Im L_{f_σ}`. -/
def ownComponentChart (W : ℝ → ℝ) (σ : ℝ) : Chart :=
  (Chart.id.loewner W σ).trans infinitySourceChart

/-- The own-component chart is a chart of `U = ℍ \ K_σ`. -/
theorem isDomainChart_ownComponentChart {W : ℝ → ℝ} (hW : Continuous W) (hW0 : W 0 = 0) {σ : ℝ}
    (hσ : 0 ≤ σ) : IsDomainChart (H \ fwdHull W σ) (ownComponentChart W σ) := by
  have h₁ := isDomainChart_loewner hW hW0 hσ
  have h := h₁.trans isDomainChart_infinitySourceChart
  rwa [h₁.image_eq] at h

/-! ### The field read in the identity chart -/

/-- The identity chart reads every field as itself. -/
theorem isChartTransport_id (k : ℝ) (h : DistOn upperHalfPlaneOpens) : IsChartTransport Chart.id 1 0 k h h := by
  intro φ φ' _ hφ
  have e : φ = φ' := by
    ext z
    by_cases hz : z ∈ H
    · rw [hφ z (by simpa [Chart.id] using hz)]
      change φ' z * ‖deriv (fun z : ℂ => z) z‖ ^ 2 = φ' z
      rw [deriv_id'', norm_one, one_pow, mul_one]
    · rw [testOn_eq_zero_of_notMem_H φ hz, testOn_eq_zero_of_notMem_H φ' hz]
  rw [e]
  change h φ' = 1 * h φ' + 0 * (∫ w, φ' w) + k * ∫ w, (0 : ℝ) * φ' w
  simp

/-- A field read in the identity chart is the field itself. -/
theorem IsChartTransport.eq_of_id {k : ℝ} {h h' : DistOn upperHalfPlaneOpens}
    (ht : IsChartTransport Chart.id 1 0 k h h') : h' = h :=
  ht.unique Chart.isConformal_id (isChartTransport_id k h)

/-! ### Couplings in a domain -/

section Couplings

variable {Ω : Type u} [mΩ : MeasurableSpace Ω]

/-- **The flow line in a domain** (Specification p. 2, (1.4) and p. 10, Definition: "an `SLE_κ(ρ)` curve coupled with
the field as in Theorem 1.1, transported by the chart"; GB6's flow prefix "from `x`"; Remarks 6.9–6.10): in the
chart `c` of `D` taking the prime ends `x, y` to `0, ∞`, the field `h` read with the flow rule (coefficient
`χ(κ)`) has the piecewise-constant data `b` off `J`, and `W` (lifetime `ζ`) drives its angle-`θ` flow line from `0`
(frozen `IsFlowLineDriver`). -/
def IsDomainFlowLine (κ : ℝ) (D : Set ℂ) (x y : PrimeEnd D) (c : Chart) (b : ℝ → ℝ) (J : Finset ℝ) (θ : ℝ)
    (P : Measure Ω) (h : Ω → DistOn upperHalfPlaneOpens) (W : ℝ≥0 → Ω → ℝ) (ζ : Ω → ℝ≥0∞) : Prop :=
  IsDomainChartAt D x y c ∧ IsPiecewiseConstantBoundaryData b J ∧
    ∃ h' : Ω → DistOn upperHalfPlaneOpens, (∀ ω, IsChartTransport c 1 0 (QuantumZipper.chiC κ) (h ω) (h' ω)) ∧
      IsGFFWithBoundaryData P h' b J ∧ IsFlowLineDriver κ b J θ P h' W ζ

/-- **The counterflow in a domain from `y` to `x`** (GB6: "the original counterflow `η` from `y` to `x` … its
universal marked field coupling"; Remarks 6.9–6.10): in the chart `c` of `D` taking `x, y` to `0, ∞` (the flow
chart), the field `h` read with the flow rule has the piecewise-constant data `b` off `J`, and `W` (lifetime `ζ`)
drives its centred counterflow from `∞` to `0` (frozen `IsCenteredCounterflowDriver`: in the inversion `R`, the
Theorem 1.1 coupling at parameter `16/κ` of the counterflow field `F = −h − πχ`, whose finite force word is the
counterflow word). -/
def IsDomainCounterflow (κ : ℝ) (D : Set ℂ) (x y : PrimeEnd D) (c : Chart) (b : ℝ → ℝ) (J : Finset ℝ)
    (P : Measure Ω) (h : Ω → DistOn upperHalfPlaneOpens) (W : ℝ≥0 → Ω → ℝ) (ζ : Ω → ℝ≥0∞) : Prop :=
  IsDomainChartAt D x y c ∧ IsPiecewiseConstantBoundaryData b J ∧
    ∃ h' : Ω → DistOn upperHalfPlaneOpens, (∀ ω, IsChartTransport c 1 0 (QuantumZipper.chiC κ) (h ω) (h' ω)) ∧
      IsGFFWithBoundaryData P h' b J ∧ IsCenteredCounterflowDriver κ P h' W ζ

/-- **A complete continuous transient trace** (GB6: "Use its complete continuous transient trace"; Theorem 1.3 and
LP10–LP11): almost surely the lifetime is infinite and the driver has a continuous generating trace on `[0, ∞)`
tending to `∞` (in the curve's own chart). -/
def IsCompleteTransientTrace (P : Measure Ω) (W : ℝ≥0 → Ω → ℝ) (ζ : Ω → ℝ≥0∞) : Prop :=
  ∀ᵐ ω ∂P, ζ ω = ⊤ ∧ ∃ γ : ℝ≥0 → ℂ, IsGeneratingTrace (fun t => W t ω) ⊤ γ ∧
    Tendsto (fun t => ‖γ t‖) atTop atTop

/-- In `ℍ` with the identity chart, the flow line in a domain is the frozen half-plane flow line. -/
theorem isDomainFlowLine_id_iff {κ : ℝ} {b : ℝ → ℝ} {J : Finset ℝ} {θ : ℝ} {P : Measure Ω}
    {h : Ω → DistOn upperHalfPlaneOpens} {W : ℝ≥0 → Ω → ℝ} {ζ : Ω → ℝ≥0∞} :
    IsDomainFlowLine κ H (primeEndH ((0 : ℝ) : OnePoint ℝ)) (primeEndH OnePoint.infty) Chart.id b J θ P h W ζ ↔
      IsPiecewiseConstantBoundaryData b J ∧ IsGFFWithBoundaryData P h b J ∧ IsFlowLineDriver κ b J θ P h W ζ := by
  constructor
  · rintro ⟨-, hb, h', ht, hG, hF⟩
    have e : h' = h := funext fun ω => (ht ω).eq_of_id
    subst e
    exact ⟨hb, hG, hF⟩
  · rintro ⟨hb, hG, hF⟩
    exact ⟨isDomainChartAt_id, hb, h, fun ω => isChartTransport_id _ (h ω), hG, hF⟩

/-- In `ℍ` with the identity chart, the counterflow in a domain is the frozen centred counterflow. -/
theorem isDomainCounterflow_id_iff {κ : ℝ} {b : ℝ → ℝ} {J : Finset ℝ} {P : Measure Ω}
    {h : Ω → DistOn upperHalfPlaneOpens} {W : ℝ≥0 → Ω → ℝ} {ζ : Ω → ℝ≥0∞} :
    IsDomainCounterflow κ H (primeEndH ((0 : ℝ) : OnePoint ℝ)) (primeEndH OnePoint.infty) Chart.id b J P h W ζ ↔
      IsPiecewiseConstantBoundaryData b J ∧ IsGFFWithBoundaryData P h b J ∧
        IsCenteredCounterflowDriver κ P h W ζ := by
  constructor
  · rintro ⟨-, hb, h', ht, hG, hF⟩
    have e : h' = h := funext fun ω => (ht ω).eq_of_id
    subst e
    exact ⟨hb, hG, hF⟩
  · rintro ⟨hb, hG, hF⟩
    exact ⟨isDomainChartAt_id, hb, h, fun ω => isChartTransport_id _ (h ω), hG, hF⟩

omit mΩ in
/-- The field read in the chart is determined by the field (any two witnesses agree). -/
theorem IsDomainChartAt.chartField_unique {D : Set ℂ} {x y : PrimeEnd D} {c : Chart} {σ a k : ℝ}
    {h : Ω → DistOn upperHalfPlaneOpens} (hc : IsDomainChartAt D x y c)
    {h₁ h₂ : Ω → DistOn upperHalfPlaneOpens} (h₁t : ∀ ω, IsChartTransport c σ a k (h ω) (h₁ ω))
    (h₂t : ∀ ω, IsChartTransport c σ a k (h ω) (h₂ ω)) : h₁ = h₂ :=
  funext fun ω => (h₁t ω).unique hc.isDomainChart.isConformal (h₂t ω)

end Couplings

/-! ### Conditional fields and marked local-set laws -/

section Conditional

/- The conditioning σ-algebra `𝒢` is bound before the ambient instance `mΩ`, so that instance search (which prefers
the most recent local instance) always finds `mΩ`. -/

/-- **The conditional field in a domain, read in its chart** (GB6: "the conditional component field … in the chart of
`U` taking `(y, p)` to `(0, ∞)`"; Aux. 32–37 and 119–125; the frozen `IsStagedHistory` uses the same form):
conditionally on `𝒢` (`condExpKernel P 𝒢 ω₀`, for `P`-a.e. `ω₀`), the field `h` read in the chart `c ω₀` with the
rule `(σ, a, k)` of (1.4) is a GFF on `ℍ` whose data is the piecewise-constant `bc ω₀` off `jc ω₀`. The chart and
the data are those of the realization `ω₀` (they are `𝒢`-measurable in the applications, so this is the conditional
law given `𝒢`). -/
def IsCondChartField {Ω : Type u} (𝒢 : MeasurableSpace Ω) [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω]
    (σ a k : ℝ) (P : Measure Ω) [IsFiniteMeasure P] (h : Ω → DistOn upperHalfPlaneOpens) (c : Ω → Chart)
    (bc : Ω → ℝ → ℝ) (jc : Ω → Finset ℝ) : Prop :=
  ∀ᵐ ω₀ ∂P, IsPiecewiseConstantBoundaryData (bc ω₀) (jc ω₀) ∧
    ∃ h' : Ω → DistOn upperHalfPlaneOpens, (∀ ω, IsChartTransport (c ω₀) σ a k (h ω) (h' ω)) ∧
      IsGFFWithBoundaryData (condExpKernel P 𝒢 ω₀) h' (bc ω₀) (jc ω₀)

/-- **Restriction to a subdomain.** Reading `h` in the composed chart `c ω₀` followed by a chart `c₂ ω₀` of a
subdomain (in the coordinate of `c ω₀`) is reading, in `c₂ ω₀`, the field already read in `c ω₀`
(`IsChartTransport.trans`, `IsChartTransport.of_trans`): the conditional field in the subdomain
`inv '' D₂ ⊆ D` is the conditional field of the field read in `D`'s chart. -/
theorem isCondChartField_trans_iff {Ω : Type u} {𝒢 : MeasurableSpace Ω} [mΩ : MeasurableSpace Ω]
    [StandardBorelSpace Ω] {σ a k : ℝ} {P : Measure Ω} [IsFiniteMeasure P] {h : Ω → DistOn upperHalfPlaneOpens}
    {c c₂ : Ω → Chart} {bc : Ω → ℝ → ℝ} {jc : Ω → Finset ℝ}
    {D D₂ : Ω → Set ℂ} (hD : ∀ ω, IsDomainChart (D ω) (c ω)) (hD₂ : ∀ ω, IsDomainChart (D₂ ω) (c₂ ω)) :
    IsCondChartField 𝒢 σ a k P h (fun ω₀ => (c ω₀).trans (c₂ ω₀)) bc jc ↔
      ∀ᵐ ω₀ ∂P, IsPiecewiseConstantBoundaryData (bc ω₀) (jc ω₀) ∧
        ∃ h'' : Ω → DistOn upperHalfPlaneOpens,
          (∀ ω, IsChartTransport (c₂ ω₀) 1 0 k (Chart.chartTransport (hD ω₀).isConformal σ a k (h ω)) (h'' ω)) ∧
          IsGFFWithBoundaryData (condExpKernel P 𝒢 ω₀) h'' (bc ω₀) (jc ω₀) := by
  have ht₁ : ∀ ω₀ ω, IsChartTransport (c ω₀) σ a k (h ω)
      (Chart.chartTransport (hD ω₀).isConformal σ a k (h ω)) := fun ω₀ ω =>
    Chart.isChartTransport_chartTransport _
      (Chart.locallyIntegrableOn_of_continuousOn (hD ω₀).continuousOn_lift_inv) σ a k (h ω)
  constructor
  · intro hF
    filter_upwards [hF] with ω₀ ⟨hb, h'', hh'', hG⟩
    exact ⟨hb, h'', fun ω => IsChartTransport.of_trans (hD ω₀).isConformal (hD₂ ω₀).isConformal
      (hD ω₀).continuousOn_lift_inv (hD₂ ω₀).continuousOn_lift_inv (ht₁ ω₀ ω) (hh'' ω), hG⟩
  · intro hF
    filter_upwards [hF] with ω₀ ⟨hb, h'', hh'', hG⟩
    exact ⟨hb, h'', fun ω => (ht₁ ω₀ ω).trans (hD ω₀).isConformal (hD₂ ω₀).isConformal
      (hD ω₀).continuousOn_lift_inv (hD₂ ω₀).continuousOn_lift_inv (hh'' ω), hG⟩

/-- **The marked local-set law** (Specification §3.2, pp. 49–52: Lemma 3.6 (iii) with the history labels retained;
p. 4: "the marked locality and optional-kernel results in Section 3"; GB6: "its canonical finite-piece own marked
law"): the σ-algebra `𝒢` of the retained marked history contains the germ σ-algebra of `(A, h)`, and conditionally
on `𝒢` the field is `h₁ + h₂` with `h₁` a `𝒢`-measurable random distribution almost surely harmonic on `ℍ \ A` and
`h₂` a zero-boundary GFF on `ℍ \ A`. -/
def IsMarkedLocalSetLaw {Ω : Type u} (𝒢 : MeasurableSpace Ω) [mΩ : MeasurableSpace Ω] (A : Ω → Set ℂ)
    (h : Ω → DistOn upperHalfPlaneOpens) (P : Measure Ω) : Prop :=
  𝒢 ≤ mΩ ∧ LocalSets.germSigma A h ≤ 𝒢 ∧
    ∃ h₁ : Ω → DistOn upperHalfPlaneOpens, Measurable[𝒢] h₁ ∧
      (∀ᵐ ω ∂P, IsHarmonicDistOn (h₁ ω) (H \ A ω)) ∧
      IsCondZeroBoundaryGFF P 𝒢 (fun ω => H \ A ω) (fun ω => h ω - h₁ ω)

/-- Lemma 3.6 (iii) is the marked local-set law with the germ σ-algebra. -/
theorem IsMarkedLocalSetLaw.of_isGermConditionalLaw {Ω : Type u} [mΩ : MeasurableSpace Ω] {A : Ω → Set ℂ}
    {h : Ω → DistOn upperHalfPlaneOpens} {P : Measure Ω} (hA : Measurable[mΩ, hittingSigma] A)
    (hh : Measurable h) (hG : LocalSets.IsGermConditionalLaw A h P) :
    IsMarkedLocalSetLaw (LocalSets.germSigma A h) A h P :=
  ⟨LocalSets.germSigma_le hA hh, le_rfl, hG⟩

end Conditional

end InteractingSLE
