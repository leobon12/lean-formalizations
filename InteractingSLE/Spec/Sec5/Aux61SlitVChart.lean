/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec5.Aux61SlitVNest
import InteractingSLE.Spec.Sec5.Aux61ChLocCore
import InteractingSLE.Spec.Sec6.Prop61Mean
import InteractingSLE.Spec.Restart.MarkovChart
import InteractingSLE.Spec.Coupling.WholeField8Flow

/-!
# Aux. lemma 61, second half: the slit-side comparison read in the restart chart

Packet PROVE-AUX61-SLIT. `Aux61SlitV.ae_tendsto_sub_flowMean` compares, in the physical domain, the union mean at the
glued stop with the flow line's own mean near the new slit. Here that comparison is read in the restart chart `c`
(the chart in which the code `Y` lives), for the chart decompositions of PROVE-AUX61-CHARTLOC (`IsChartGaussAt`, given
`𝒢 = germ(A on the live event) ∨ ℋ`):

* **`pullField_apply_eq_integral_of_subset`**, **`chartTransport_apply_eq_integral_of_subset`**: the transport of a
  distribution represented by `m` on `inv(O)` is represented by `m ∘ inv` (resp. `m ∘ inv + a + k · lift ∘ inv`) on `O`;
* **`isChartGaussAt_chartTransport`**: the chart transport `chartTransport (g + u₀)` of ANY physical decomposition `g`
  given `𝒢` is a chart decomposition given `𝒢` (the explicit form of `LocalExt.exists_condDecomp_chart`); so, by the
  uniqueness of PROVE-AUX61-MEAN, every chart decomposition is this one off the chart hull;
* **`ae_tendsto_chart_sub_flowMean`**: almost surely on the live event and on the comparison event `S' i`, every
  harmonic representative `v` of a chart decomposition satisfies `v − w₂ → 0` along every filter `l` inside
  `ℍ ∖ K_q` on which the chart inverse tends to a point `z₀ ∈ L i ∪ ℝ` near which `A ⊆ L i`; here
  `w₂ = M₂ ∘ inv + a + k · lift ∘ inv` is the chart reading of the flow line's own pointwise mean `M₂` (Astra's
  "canonical flow-line germs" in the restart chart). This is the probabilistic half of item (c2) of
  `planning/handoffs/PROVE-AUX61-MEAN.md`, with `l = map F_q (𝓝[ℍ] x)` at a real point `x` of the slit image.

Conditional helpers with distinct names; they replace no source theorem. R48/R77: nothing here uses Theorem 1.2/1.3,
`Theorem12ParamStatement`, `Theorem13Statement`, any `*_of_param` result, or Astra's post-contact kernel.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

universe u

open MeasureTheory ProbabilityTheory Filter Set Topology Metric
open scoped NNReal ENNReal

namespace InteractingSLE.Sec5.Aux61SlitV

open QuantumZipper (H zeroGFFTestCov)
open LQGMetric (DistOn TestOn IsZeroBoundaryGFF)
open LocalSets (germSigma IsLocalSetMean lowerUnion)
open WholeField (IsHistoryAvoidanceLocal centredField)
open SupercriticalConformalCovariance.GM24 (smoothDist)
open Aux61Fib (FibCode)
open Aux61FibK (codeFiltration)
open Aux61ChLoc (IsChartGaussAt liveEv liveSet liveSet_of_mem liveSet_of_notMem measurableSet_live
  isHistoryAvoidanceLocal_liveSet ae_condExp_eq_of_eqOn)
open Aux61UnionK (chartHull norm_cexp_I_mul_ofReal_le measurable_field_apply measurable_apply_of_measurable
  isOpen_H_diff_chartHull)

/-! ### Transported representatives -/

section Transport

variable {c : Chart}

/-- **The pull-back of a represented distribution.** If `T` is represented by `m` on `inv(O)`, then the pull-back of
`T` is represented by `m ∘ inv` on `O`. -/
theorem pullField_apply_eq_integral_of_subset (hc : c.IsConformal) {O : Set ℂ} (hOH : O ⊆ H)
    {T : DistOn upperHalfPlaneOpens} {m : ℂ → ℝ}
    (hT : ∀ φ : TestOn upperHalfPlaneOpens, tsupport φ ⊆ c.2.1 '' O → T φ = ∫ z, m z * φ z)
    {φ : TestOn upperHalfPlaneOpens} (hφ : tsupport φ ⊆ O) :
    Chart.pullField hc T φ = ∫ w, m (c.2.1 w) * φ w := by
  rw [Chart.pullField_apply, hT _ (Restart.MarkovChart.tsupport_pushTest_subset_of_chartPre hc fun w hw =>
    ⟨hOH (hφ hw), mem_image_of_mem _ (hφ hw)⟩), Chart.integral_mul_pushTest]

/-- **The chart transport of a represented distribution.** If `T` is represented by a function `m` continuous on
`inv(O)`, then `chartTransport T` (height shift `a`, lift coefficient `k`) is represented on `O` by
`m ∘ inv + a + k · lift ∘ inv`. -/
theorem chartTransport_apply_eq_integral_of_subset (hc : c.IsConformal) (hℓ : ContinuousOn c.2.2 c.dom)
    {O : Set ℂ} (hOH : O ⊆ H) {T : DistOn upperHalfPlaneOpens} {m : ℂ → ℝ} (hmc : ContinuousOn m (c.2.1 '' O))
    (hT : ∀ φ : TestOn upperHalfPlaneOpens, tsupport φ ⊆ c.2.1 '' O → T φ = ∫ z, m z * φ z) (a k : ℝ)
    {φ : TestOn upperHalfPlaneOpens} (hφ : tsupport φ ⊆ O) :
    Chart.chartTransport hc 1 a k T φ = ∫ w, (m (c.2.1 w) + a + k * c.2.2 (c.2.1 w)) * φ w := by
  have hℓc := hc.continuousOn_lift_inv hℓ
  have hinvc : ContinuousOn c.2.1 O := hc.1.continuousOn.mono hOH
  have hmi : ContinuousOn (fun w => m (c.2.1 w)) O := hmc.comp hinvc (mapsTo_image _ _)
  have i₁ : Integrable fun w => m (c.2.1 w) * φ w := WholeField.integrable_mul_testOn hmi φ hφ
  have i₂ : Integrable fun w => φ w := φ.continuous.integrable_of_hasCompactSupport φ.hasCompactSupport
  have i₃ : Integrable fun w => c.2.2 (c.2.1 w) * φ w := WholeField.integrable_mul_testOn hℓc φ (hφ.trans hOH)
  have i₁₂ : Integrable fun w => m (c.2.1 w) * φ w + a * φ w := i₁.add (i₂.const_mul a)
  have e : (fun w => (m (c.2.1 w) + a + k * c.2.2 (c.2.1 w)) * φ w) =
      fun w => (m (c.2.1 w) * φ w + a * φ w) + k * (c.2.2 (c.2.1 w) * φ w) := by
    funext w
    ring
  rw [Chart.chartTransport_apply', ← Chart.pullField_apply, pullField_apply_eq_integral_of_subset hc hOH hT hφ,
    Chart.oneDist_apply, Chart.liftDist_apply (Chart.locallyIntegrableOn_of_continuousOn hℓc), one_mul, e,
    integral_add i₁₂ (i₃.const_mul k), integral_add i₁ (i₂.const_mul a), integral_const_mul, integral_const_mul]

end Transport

/-! ### The chart transport of a physical decomposition -/

section Chart

variable {X : Type u} {𝒢 ℋ : MeasurableSpace X} [mX : MeasurableSpace X] {β : Type*} [mβ : MeasurableSpace β]

/-- **The chart transport of a physical decomposition is a chart decomposition** (the explicit form of
`LocalExt.exists_condDecomp_chart`, with `E = Ω`). Let `g` be `𝒢`-measurable, harmonic off `A` on the live event,
with `h − u₀ − g` conditionally a zero-boundary GFF on `ℍ ∖ A` (`A` replaced by `ℍ` off the live event) given `𝒢`;
let the chart be `𝒢`-measurable with a continuous harmonic lift and `ℍ ∖ A = inv(ℍ ∖ K_q)` on the live event. Then
`chartTransport (g + u₀)` is a conditional Gaussian decomposition of the chart field given `𝒢`. -/
theorem isChartGaussAt_chartTransport {μ : Measure X} [IsProbabilityMeasure μ] {Z : X → β} {B : Set β}
    (hB : MeasurableSet B) {Y : X → FibCode} (hY : Measurable Y) (q : ℝ≥0)
    {h : X → DistOn upperHalfPlaneOpens} (hhm : Measurable h) {u₀ : ℂ → ℝ}
    (hu₀ : InnerProductSpace.HarmonicOnNhd u₀ H)
    {c : X → Chart} (hc : ∀ x, (c x).IsConformal) (a k : ℝ)
    (hfield : ∀ x, Z x ∈ B → (q : ℝ≥0∞) < (Y x).life → (Y x).field = Chart.chartTransport (hc x) 1 a k (h x))
    (h𝒢 : 𝒢 ≤ mX) (hZ𝒢 : mβ.comap Z ≤ 𝒢)
    (hY𝒢 : (codeFiltration.{u} q).comap (fun x => ULift.up.{u} (Y x)) ≤ 𝒢)
    (hdom : ∀ z, MeasurableSet[𝒢] {x | z ∈ (c x).dom})
    (hfwd : ∀ z, Measurable[𝒢] ({x | z ∈ (c x).dom}.indicator fun x => (c x).1 z))
    (hliftm : ∀ z, Measurable[𝒢] ({x | z ∈ (c x).dom}.indicator fun x => (c x).2.2 z))
    (hliftc : ∀ x, ContinuousOn (c x).2.2 (c x).dom)
    (hlift : ∀ x, InnerProductSpace.HarmonicOnNhd (c x).2.2 (c x).dom) {A : X → Set ℂ}
    (hgeo : ∀ᵐ x ∂μ, Z x ∈ B → (q : ℝ≥0∞) < (Y x).life → H \ A x = (c x).2.1 '' (H \ chartHull Y q x))
    {g : X → DistOn upperHalfPlaneOpens} (hgm : Measurable[𝒢] g)
    (hgh : ∀ᵐ x ∂μ, Z x ∈ B → (q : ℝ≥0∞) < (Y x).life → IsHarmonicDistOn (g x) (H \ A x))
    (hgc : IsCondZeroBoundaryGFF μ 𝒢 (fun x => H \ liveSet (liveEv Z B Y q) A x)
      fun x => centredField h u₀ x - g x) :
    @IsChartGaussAt X mX β mβ μ Z B Y q 𝒢
      fun x => Chart.chartTransport (hc x) 1 a k (g x + smoothDist upperHalfPlaneOpens u₀) := by
  classical
  set S := liveEv Z B Y q with hSdef
  set h0 := centredField h u₀ with hh0def
  have hSG : MeasurableSet[𝒢] S := measurableSet_live hZ𝒢 hY𝒢 hB
  have hh0m : Measurable h0 := WholeField.measurable_centredField hhm u₀
  have hgm' : Measurable g := hgm.mono h𝒢 le_rfl
  have hXm : Measurable fun x => h0 x - g x :=
    LQGMetric.measurable_distOn_iff.2 fun φ =>
      ((Sobolev.measurable_distOn_apply φ).comp hh0m).sub ((Sobolev.measurable_distOn_apply φ).comp hgm')
  -- the chart hull on the live event, `ℍ` elsewhere
  set K' : X → Set ℂ := liveSet S (chartHull Y q) with hK'def
  have hK' : ∀ x, IsOpen (H \ K' x) ∧ H \ K' x ⊆ H := fun x => by
    by_cases hx : x ∈ S
    · rw [hK'def, liveSet_of_mem hx]
      exact ⟨isOpen_H_diff_chartHull Y hx.2, sdiff_subset⟩
    · rw [hK'def, liveSet_of_notMem hx, Set.sdiff_self]
      exact ⟨isOpen_empty, empty_subset _⟩
  -- the conditional law on the image domain
  have hcondE : IsCondZeroBoundaryGFF μ 𝒢 (fun x => (c x).2.1 '' (H \ K' x)) fun x => h0 x - g x := by
    intro φ
    filter_upwards [hgc φ, hgeo] with x h1 h2
    rw [h1]
    by_cases hx : x ∈ S
    · rw [hK'def, liveSet_of_mem hx, liveSet_of_mem hx, h2 hx.1 hx.2]
    · rw [hK'def, liveSet_of_notMem hx, liveSet_of_notMem hx, Set.sdiff_self, image_empty]
  have hpull := Sec7.Lemma72C.isCondZeroBoundaryGFF_pullField_sub h𝒢 hc hdom hfwd (O := fun x => H \ K' x)
    (fun x => (hK' x).1) (fun x => (hK' x).2) hXm hcondE
  set M₀ : X → DistOn upperHalfPlaneOpens := fun x => g x + smoothDist upperHalfPlaneOpens u₀ with hM₀def
  have hM₀m : Measurable[𝒢] M₀ := (Coupling.measurable_add_distOnConst _).comp hgm
  have hMm : Measurable[𝒢] fun x => Chart.chartTransport (hc x) 1 a k (M₀ x) :=
    @Chart.measurable_chartTransport_random' X 𝒢 c hc hdom hfwd hliftm hliftc M₀ hM₀m 1 a k
  have hMm' : Measurable fun x => Chart.chartTransport (hc x) 1 a k (M₀ x) := hMm.mono h𝒢 le_rfl
  refine ⟨h𝒢, hZ𝒢, hY𝒢, hMm, ?_, fun φ => ?_⟩
  · filter_upwards [hgh, hgeo] with x hx hgx hxB hxq
    have hO : IsOpen (H \ chartHull Y q x) := isOpen_H_diff_chartHull Y hxq
    have hAo : IsOpen (H \ A x) := by
      rw [hgx hxB hxq]
      exact (hc x).isOpen_image_of_subset hO sdiff_subset
    have hMh : IsHarmonicDistOn (M₀ x) ((c x).2.1 '' (H \ chartHull Y q x)) := by
      rw [← hgx hxB hxq]
      exact Coupling.IsHarmonicDistOn.add' hAo (hx hxB hxq)
        (LocalSets.IsHarmonicDistOn.mono (WholeField.isHarmonicDistOn_smoothDist hu₀) sdiff_subset)
    exact Sec7.Lemma72C.isHarmonicDistOn_chartTransport (hc x) (hliftc x) (hlift x) hO sdiff_subset hMh a k
  · have hT : Measurable fun x => Chart.chartTransport (hc x) 1 a k (h x) :=
      Chart.measurable_chartTransport_random' hc (fun z => h𝒢 _ (hdom z)) (fun z => (hfwd z).mono h𝒢 le_rfl)
        (fun z => (hliftm z).mono h𝒢 le_rfl) hliftc hhm 1 a k
    have hfm : Measurable fun x' => Complex.exp (Complex.I * (((Y x').field φ -
        Chart.chartTransport (hc x') 1 a k (M₀ x') φ : ℝ) : ℂ)) :=
      Complex.measurable_exp.comp (measurable_const.mul (Complex.measurable_ofReal.comp
        ((measurable_field_apply hY φ).sub (measurable_apply_of_measurable hMm' φ))))
    have hf'm : Measurable fun x' => Complex.exp (Complex.I *
        ((Chart.chartTransport (hc x') 1 a k (h x') φ - Chart.chartTransport (hc x') 1 a k (M₀ x') φ : ℝ) : ℂ)) :=
      Complex.measurable_exp.comp (measurable_const.mul (Complex.measurable_ofReal.comp
        ((measurable_apply_of_measurable hT φ).sub (measurable_apply_of_measurable hMm' φ))))
    have heq := ae_condExp_eq_of_eqOn (μ := μ) hSG
      (Integrable.of_bound hfm.aestronglyMeasurable 1 (ae_of_all _ fun x => norm_cexp_I_mul_ofReal_le _))
      (Integrable.of_bound hf'm.aestronglyMeasurable 1 (ae_of_all _ fun x => norm_cexp_I_mul_ofReal_le _))
      (fun x hx => by rw [hfield x hx.1 hx.2])
    have hdiff : ∀ x, Chart.chartTransport (hc x) 1 a k (h x) - Chart.chartTransport (hc x) 1 a k (M₀ x) =
        Chart.pullField (hc x) (h0 x - g x) := fun x => by
      rw [Chart.chartTransport_sub, one_smul]
      congr 1
      simp only [hM₀def, hh0def, centredField]
      abel
    have e : (fun x' => Complex.exp (Complex.I *
        ((Chart.chartTransport (hc x') 1 a k (h x') φ - Chart.chartTransport (hc x') 1 a k (M₀ x') φ : ℝ) : ℂ))) =
        fun x' => Complex.exp (Complex.I * ((Chart.pullField (hc x') (h0 x' - g x') φ : ℝ) : ℂ)) := by
      funext x'
      rw [← hdiff x']
      rfl
    filter_upwards [heq, hpull φ] with x h1 h2 hxB hxq
    have hxS : x ∈ S := ⟨hxB, hxq⟩
    rw [h1 hxS, e, h2, hK'def, liveSet_of_mem hxS]

end Chart

/-! ### The slit-side comparison in the restart chart -/

section Slit

variable {X : Type u} {ℋ : MeasurableSpace X} [mX : MeasurableSpace X] {β : Type*} [mβ : MeasurableSpace β]

/-- A harmonic function on an open set is continuous there. -/
theorem continuousOn_of_harmonicOnNhd {f : ℂ → ℝ} {O : Set ℂ} (hf : InnerProductSpace.HarmonicOnNhd f O) :
    ContinuousOn f O := fun z hz => (hf z hz).1.continuousAt.continuousWithinAt

/-- **Aux. lemma 61's slit-side comparison in the restart chart** (the probabilistic half of item (c2) of
`planning/handoffs/PROVE-AUX61-MEAN.md`; Astra's follow-up 4 §1.1, L113–L123).

Setting: the restart data of PROVE-AUX61-CHARTLOC (chart `c` with harmonic lift, code `Y` whose field is the chart
transport of `h` on the live event, the physical union `A` at the glued stop, history-marked local for marks `ℋ`, with
`ℍ ∖ A = inv(ℍ ∖ K_q)` on the live event), and any chart decomposition `h₁` given
`𝒢 = germ(A on the live event) ∨ ℋ`. Comparison data, for countably many indices `i` (the rational own times of the
flow line): the flow line's own prefix `L i`, an ordinary local set of the centred field with mean `g₂ i`, represented
by `M₂ i − u₀` with `M₂ i` harmonic off `L i` (the pointwise flow-line mean); a larger union `A' i ⊇ A, L i` (on `ℍ`),
marked local for marks `ℳ i ⊇ ℋ` that record `A` and `L i`; an event `S' i ∈ ℋ` on which `A' i = A`.

Conclusion: almost surely, for every `i`, on the live event and on `S' i`, every harmonic representative `v` of `h₁` on
`ℍ ∖ K_q` satisfies `v − (M₂ i ∘ inv + a + k · lift ∘ inv) → 0` along every filter `l` inside `ℍ ∖ K_q` on which the
chart inverse tends to a point `z₀ ∈ L i ∪ ℝ` near which `A ⊆ L i`. -/
theorem ae_tendsto_chart_sub_flowMean {μ : Measure X} [IsProbabilityMeasure μ] {Z : X → β} {B : Set β}
    (hB : MeasurableSet B) {Y : X → FibCode} (hY : Measurable Y) (q : ℝ≥0)
    {h : X → DistOn upperHalfPlaneOpens} (hhm : Measurable h) {u₀ : ℂ → ℝ}
    (hu₀ : InnerProductSpace.HarmonicOnNhd u₀ H)
    (hh0 : IsZeroBoundaryGFF upperHalfPlaneOpens (centredField h u₀) μ)
    {c : X → Chart} (hc : ∀ x, (c x).IsConformal) (a k : ℝ)
    (hfield : ∀ x, Z x ∈ B → (q : ℝ≥0∞) < (Y x).life → (Y x).field = Chart.chartTransport (hc x) 1 a k (h x))
    (hℋ : ℋ ≤ mX) (hZℋ : mβ.comap Z ≤ ℋ)
    (hYℋ : (codeFiltration.{u} q).comap (fun x => ULift.up.{u} (Y x)) ≤ ℋ)
    (hdom : ∀ z, MeasurableSet[ℋ] {x | z ∈ (c x).dom})
    (hfwd : ∀ z, Measurable[ℋ] ({x | z ∈ (c x).dom}.indicator fun x => (c x).1 z))
    (hliftm : ∀ z, Measurable[ℋ] ({x | z ∈ (c x).dom}.indicator fun x => (c x).2.2 z))
    (hliftc : ∀ x, ContinuousOn (c x).2.2 (c x).dom)
    (hlift : ∀ x, InnerProductSpace.HarmonicOnNhd (c x).2.2 (c x).dom)
    {A : X → Set ℂ} (hAm : Measurable[mX, hittingSigma] A) (hAc : ∀ x, A x ⊆ H ∧ IsOpen (H \ A x))
    (hloc : IsHistoryAvoidanceLocal ℋ A (centredField h u₀) μ)
    (hgeo : ∀ᵐ x ∂μ, Z x ∈ B → (q : ℝ≥0∞) < (Y x).life → H \ A x = (c x).2.1 '' (H \ chartHull Y q x))
    {ι : Type*} [Countable ι] {L : ι → X → Set ℂ} {g₂ : ι → X → DistOn upperHalfPlaneOpens}
    (hLm : ∀ i, Measurable[mX, hittingSigma] (L i)) (hLc : ∀ i, ∀ᵐ x ∂μ, L i x ⊆ H ∧ IsOpen (H \ L i x))
    (hLunb : ∀ i, ∀ᵐ x ∂μ, ∀ z ∈ lowerUnion (L i x),
      ¬ Bornology.IsBounded (connectedComponentIn (lowerUnion (L i x)) z))
    (hg₂ : ∀ i, IsLocalSetMean (L i) (centredField h u₀) μ (g₂ i))
    {M₂ : ι → X → ℂ → ℝ} (hM₂h : ∀ i, ∀ᵐ x ∂μ, InnerProductSpace.HarmonicOnNhd (M₂ i x) (H \ L i x))
    (hM₂ : ∀ i, ∀ᵐ x ∂μ, ∀ φ : TestOn upperHalfPlaneOpens, tsupport φ ⊆ H \ L i x →
      g₂ i x φ = ∫ z, (M₂ i x z - u₀ z) * φ z)
    {A' : ι → X → Set ℂ} {ℳ : ι → MeasurableSpace X} (hℳ : ∀ i, ℳ i ≤ mX)
    (hA'm : ∀ i, Measurable[mX, hittingSigma] (A' i)) (hA'c : ∀ i x, A' i x ⊆ H ∧ IsOpen (H \ A' i x))
    (hloc' : ∀ i, IsHistoryAvoidanceLocal (ℳ i) (A' i) (centredField h u₀) μ)
    (hℋℳ : ∀ i, ℋ ≤ ℳ i) (hAℳ : ∀ i, Measurable[ℳ i, hittingSigma] A) (hAA' : ∀ i x, A x ∩ H ⊆ A' i x)
    (hLℳ : ∀ i, Measurable[ℳ i, hittingSigma] (L i)) (hLA' : ∀ i x, L i x ∩ H ⊆ A' i x)
    {S' : ι → Set X} (hS' : ∀ i, MeasurableSet[ℋ] (S' i)) (hSA : ∀ i, ∀ᵐ x ∂μ, x ∈ S' i → A' i x = A x)
    {h₁ : X → DistOn upperHalfPlaneOpens}
    (hG : @IsChartGaussAt X mX β mβ μ Z B Y q
      (germSigma (liveSet (liveEv Z B Y q) A) (centredField h u₀) ⊔ ℋ) h₁) :
    ∀ᵐ x ∂μ, ∀ i, Z x ∈ B → (q : ℝ≥0∞) < (Y x).life → x ∈ S' i →
      ∀ v : ℂ → ℝ, InnerProductSpace.HarmonicOnNhd v (H \ chartHull Y q x) →
      (∀ ψ : TestOn upperHalfPlaneOpens, tsupport ψ ⊆ H \ chartHull Y q x → h₁ x ψ = ∫ z, v z * ψ z) →
      ∀ z₀ ∈ L i x ∪ {z : ℂ | z.im = 0}, (∃ r > 0, A x ∩ ball z₀ r ⊆ L i x) →
      ∀ l : Filter ℂ, l ≤ 𝓟 (H \ chartHull Y q x) → Tendsto (c x).2.1 l (𝓝 z₀) →
        Tendsto (fun ζ => v ζ - (M₂ i x ((c x).2.1 ζ) + a + k * (c x).2.2 ((c x).2.1 ζ))) l (𝓝 0) := by
  classical
  set S := liveEv Z B Y q with hSdef
  set h0 := centredField h u₀ with hh0def
  have hh0m : Measurable h0 := WholeField.measurable_centredField hhm u₀
  have hSℋ : MeasurableSet[ℋ] S := measurableSet_live hZℋ hYℋ hB
  have hS : MeasurableSet S := hℋ _ hSℋ
  have hSℳ : ∀ i, MeasurableSet[ℳ i] S := fun i => hℋℳ i _ hSℋ
  -- the physical union on the live event and its germ decomposition
  set Al : X → Set ℂ := liveSet S A with hAldef
  have hAlm : Measurable[mX, hittingSigma] Al := Measurable.piecewise hS hAm measurable_const
  have hAlc : ∀ x, Al x ⊆ H ∧ IsOpen (H \ Al x) := fun x => by
    by_cases hx : x ∈ S
    · rw [hAldef, liveSet_of_mem hx]; exact hAc x
    · rw [hAldef, liveSet_of_notMem hx, Set.sdiff_self]; exact ⟨subset_rfl, isOpen_empty⟩
  have hlocl : IsHistoryAvoidanceLocal ℋ Al h0 μ := isHistoryAvoidanceLocal_liveSet hloc hSℋ
  obtain ⟨g, hgm, hgh, hgc⟩ :=
    Sec7.Lemma72C.exists_germLaw_of_isHistoryAvoidanceLocal hh0 hAlm hℋ hlocl (ae_of_all _ hAlc)
  have h𝒢 : germSigma Al h0 ⊔ ℋ ≤ mX := sup_le (LocalSets.germSigma_le hAlm hh0m) hℋ
  have hg𝒢 : Measurable[germSigma Al h0 ⊔ ℋ] g := hgm.mono le_sup_left le_rfl
  have hℋ𝒢 : ℋ ≤ germSigma Al h0 ⊔ ℋ := le_sup_right
  -- the physical comparison for the live versions of the larger unions
  have hA'lm : ∀ i, Measurable[mX, hittingSigma] (liveSet S (A' i)) := fun i =>
    Measurable.piecewise hS (hA'm i) measurable_const
  have hA'lc : ∀ i, ∀ᵐ x ∂μ, liveSet S (A' i) x ⊆ H ∧ IsOpen (H \ liveSet S (A' i) x) := fun i =>
    ae_of_all _ fun x => by
      by_cases hx : x ∈ S
      · rw [liveSet_of_mem hx]; exact hA'c i x
      · rw [liveSet_of_notMem hx, Set.sdiff_self]; exact ⟨subset_rfl, isOpen_empty⟩
  have hAlℳ : ∀ i, Measurable[ℳ i, hittingSigma] Al := fun i =>
    Measurable.piecewise (hSℳ i) (hAℳ i) measurable_const
  have hsubl : ∀ (E : X → Set ℂ) (i : ι), (∀ x, E x ∩ H ⊆ A' i x) → ∀ x, liveSet S E x ∩ H ⊆ liveSet S (A' i) x :=
    fun E i hE x => by
      by_cases hx : x ∈ S
      · rw [liveSet_of_mem hx, liveSet_of_mem hx]; exact hE x
      · rw [liveSet_of_notMem hx, liveSet_of_notMem hx]; exact inter_subset_left
  have hLsub : ∀ i x, L i x ∩ H ⊆ liveSet S (A' i) x := fun i x => by
    by_cases hx : x ∈ S
    · rw [liveSet_of_mem hx]; exact hLA' i x
    · rw [liveSet_of_notMem hx]; exact inter_subset_right
  have hphys := ae_tendsto_sub_flowMean (𝒢 := germSigma Al h0 ⊔ ℋ) (S := S') hh0 hAlm hg𝒢 hgh hgc hLm hLc hLunb hg₂
    hℳ hA'lm hA'lc (fun i => isHistoryAvoidanceLocal_liveSet (hloc' i) (hSℳ i)) hAlℳ
    (fun i => hsubl A i (hAA' i)) hLℳ hLsub (fun i => sup_le_sup_left (hℋℳ i) _)
    (fun i => hℋ𝒢 _ (hS' i)) (fun i => by
      filter_upwards [hSA i] with x hx hxS'
      by_cases hxS : x ∈ S
      · rw [hAldef, liveSet_of_mem hxS, liveSet_of_mem hxS, hx hxS']
      · rw [hAldef, liveSet_of_notMem hxS, liveSet_of_notMem hxS])
  -- the explicit chart decomposition, and uniqueness
  have hM := isChartGaussAt_chartTransport (𝒢 := germSigma Al h0 ⊔ ℋ) hB hY q hhm hu₀ hc a k hfield h𝒢
    (hZℋ.trans hℋ𝒢) (hYℋ.trans hℋ𝒢) (fun z => hℋ𝒢 _ (hdom z)) (fun z => (hfwd z).mono hℋ𝒢 le_rfl)
    (fun z => (hliftm z).mono hℋ𝒢 le_rfl) hliftc hlift hgeo hg𝒢
    (by filter_upwards [hgh] with x hx hxB hxq; rwa [hAldef, liveSet_of_mem (show x ∈ S from ⟨hxB, hxq⟩)] at hx)
    hgc
  have huniq := Aux61MeanId.gauss_ae_forall_apply_eq hG hM hY hB
  filter_upwards [hphys, huniq, ae_all_iff.2 hM₂, ae_all_iff.2 hM₂h, hgeo, ae_all_iff.2 hSA, ae_all_iff.2 hLc]
    with x hph hun hM₂x hM₂hx hgeox hSAx hLcx
  intro i hxB hxq hxS' v hv hrep z₀ hz₀ hrA l hl hinv
  have hxS : x ∈ S := ⟨hxB, hxq⟩
  have hAl : Al x = A x := liveSet_of_mem hxS
  have hA'A : A' i x = A x := hSAx i hxS'
  obtain ⟨u, hu, hurep, hulim⟩ := hph i hxS'
  rw [hAl] at hu hurep hulim
  have hOo : IsOpen (H \ chartHull Y q x) := isOpen_H_diff_chartHull Y hxq
  have hgx : H \ A x = (c x).2.1 '' (H \ chartHull Y q x) := hgeox hxB hxq
  have hLA : L i x ∩ H ⊆ A x := hA'A ▸ hLA' i x
  have hAL : H \ A x ⊆ H \ L i x := fun z hz => ⟨hz.1, fun hzL => hz.2 (hLA ⟨hzL, hz.1⟩)⟩
  have hAo : IsOpen (H \ A x) := (hAc x).2
  have hinvO : MapsTo (c x).2.1 (H \ chartHull Y q x) (H \ A x) := by rw [hgx]; exact mapsTo_image _ _
  have hinvd : DifferentiableOn ℂ (c x).2.1 (H \ chartHull Y q x) := (hc x).1.mono sdiff_subset
  -- the harmonic candidate `u ∘ inv + w₂`
  have huinv : InnerProductSpace.HarmonicOnNhd (u ∘ (c x).2.1) (H \ chartHull Y q x) :=
    LQGMetric.harmonicOnNhd_comp_holo hAo hOo hu hinvd hinvO
  have hM₂inv : InnerProductSpace.HarmonicOnNhd (M₂ i x ∘ (c x).2.1) (H \ chartHull Y q x) :=
    LQGMetric.harmonicOnNhd_comp_holo (hLcx i).2 hOo (hM₂hx i) hinvd (hinvO.mono_right hAL)
  have hlinv : InnerProductSpace.HarmonicOnNhd ((c x).2.2 ∘ (c x).2.1) (H \ chartHull Y q x) :=
    LQGMetric.harmonicOnNhd_comp_holo (c x).dom.isOpen hOo (hlift x) hinvd fun w hw => (hc x).inv_mem_dom hw.1
  set w₂ : ℂ → ℝ := fun ζ => M₂ i x ((c x).2.1 ζ) + a + k * (c x).2.2 ((c x).2.1 ζ) with hw₂def
  have hw₂ : InnerProductSpace.HarmonicOnNhd w₂ (H \ chartHull Y q x) := by
    have h3 := (hM₂inv.add (InnerProductSpace.harmonicOnNhd_const a)).add (hlinv.const_smul (c := k))
    convert h3 using 1
    funext ζ
    simp only [Pi.add_apply, Function.comp_apply, Pi.smul_apply, smul_eq_mul, hw₂def]
  have hsum : InnerProductSpace.HarmonicOnNhd (fun ζ => u ((c x).2.1 ζ) + w₂ ζ) (H \ chartHull Y q x) :=
    huinv.add hw₂
  -- the pairings of `h₁` against tests off the chart hull
  set sm := smoothDist upperHalfPlaneOpens u₀ with hsmdef
  have hu₀c : ContinuousOn u₀ (upperHalfPlaneOpens : Set ℂ) := fun z hz =>
    (hu₀ z hz).1.continuousAt.continuousWithinAt
  have hM₂c : ContinuousOn (M₂ i x) (H \ L i x) := continuousOn_of_harmonicOnNhd (hM₂hx i)
  have hrep₂ : ∀ φ : TestOn upperHalfPlaneOpens, tsupport φ ⊆ (c x).2.1 '' (H \ chartHull Y q x) →
      (g₂ i x + sm) φ = ∫ z, M₂ i x z * φ z := by
    intro φ hφ
    have hφL : tsupport φ ⊆ H \ L i x := (hgx ▸ hφ).trans hAL
    have i₁ : Integrable fun z => (M₂ i x z - u₀ z) * φ z :=
      WholeField.integrable_mul_testOn (hM₂c.sub (hu₀c.mono (sdiff_subset))) φ hφL
    have i₂ : Integrable fun z => u₀ z * φ z := WholeField.integrable_mul_testOn hu₀c φ φ.tsupport_subset
    rw [add_apply, hM₂x i φ hφL, hsmdef, SupercriticalConformalCovariance.GM24.smoothDist_apply hu₀c,
      ← integral_add i₁ (by simpa only [mul_comm] using i₂)]
    refine integral_congr_ae (ae_of_all _ fun z => ?_)
    simp only
    ring
  have hpair : ∀ ψ : TestOn upperHalfPlaneOpens, tsupport ψ ⊆ H \ chartHull Y q x →
      ∫ z, v z * ψ z = ∫ z, (u ((c x).2.1 z) + w₂ z) * ψ z := by
    intro ψ hψ
    have hdisj : Disjoint (tsupport ψ) (chartHull Y q x) :=
      Set.disjoint_left.2 fun z hz hzK => (hψ hz).2 hzK
    rw [← hrep ψ hψ, hun hxB hxq ψ hdisj]
    have hsplit : Chart.chartTransport (hc x) 1 a k (g x + sm) ψ =
        Chart.chartTransport (hc x) 1 a k (g₂ i x + sm) ψ + Chart.pullField (hc x) (g x - g₂ i x) ψ := by
      have e := congrArg (fun T : DistOn upperHalfPlaneOpens => T ψ)
        (Chart.chartTransport_sub (hc x) 1 a k (g x + sm) (g₂ i x + sm))
      have e' : g x + sm - (g₂ i x + sm) = g x - g₂ i x := by abel
      simp only [sub_apply, one_smul, e'] at e
      linarith
    have h1 : Chart.chartTransport (hc x) 1 a k (g₂ i x + sm) ψ = ∫ w, w₂ w * ψ w :=
      chartTransport_apply_eq_integral_of_subset (hc x) (hliftc x) sdiff_subset (hM₂c.mono (hgx ▸ hAL)) hrep₂ a k
        hψ
    have h2 : Chart.pullField (hc x) (g x - g₂ i x) ψ = ∫ w, u ((c x).2.1 w) * ψ w :=
      pullField_apply_eq_integral_of_subset (hc x) sdiff_subset (fun φ hφ => by
        rw [sub_apply]; exact hurep φ (hgx ▸ hφ)) hψ
    have i₁ : Integrable fun w => w₂ w * ψ w :=
      WholeField.integrable_mul_testOn (continuousOn_of_harmonicOnNhd hw₂) ψ hψ
    have i₂ : Integrable fun w => u ((c x).2.1 w) * ψ w :=
      WholeField.integrable_mul_testOn (continuousOn_of_harmonicOnNhd huinv) ψ hψ
    rw [hsplit, h1, h2, ← integral_add i₁ i₂]
    refine integral_congr_ae (ae_of_all _ fun w => ?_)
    simp only
    ring
  have hEq : EqOn v (fun ζ => u ((c x).2.1 ζ) + w₂ ζ) (H \ chartHull Y q x) :=
    Sec6.eqOn_of_integral_mul_eq hOo sdiff_subset hv hsum hpair
  -- the limit
  have hO : H \ chartHull Y q x ∈ l := hl (mem_principal_self _)
  have hinv' : Tendsto (c x).2.1 l (𝓝[H \ A x] z₀) :=
    tendsto_nhdsWithin_iff.2 ⟨hinv, Filter.mem_of_superset hO fun ζ hζ => hinvO hζ⟩
  have hlim : Tendsto (fun ζ => u ((c x).2.1 ζ)) l (𝓝 0) := (hulim z₀ hz₀ hrA).comp hinv'
  refine hlim.congr' ?_
  filter_upwards [hO] with ζ hζ
  rw [hEq hζ]
  simp only [hw₂def]
  ring

/-- **The slit-side limit at a real point** (how `ae_tendsto_chart_sub_flowMean` is consumed by
`Aux61MeanId.isChartMeanAt_of_slit`): if `v − w₂ → 0` along every filter inside `O` on which `inv → z₀`, the map `F`
(the inverse Loewner map `F_q`) sends `ℍ` into `O` with `inv ∘ F → z₀` at the real point `x'`, and the deterministic
comparison `w₂ ∘ F − M ∘ F → 0` holds at `x'`, then `v ∘ F − M ∘ F → 0` at `x'`. -/
theorem tendsto_slit_of_chart {v w₂ M : ℂ → ℝ} {inv F : ℂ → ℂ} {O : Set ℂ} {z₀ x' : ℂ}
    (hconv : ∀ l : Filter ℂ, l ≤ 𝓟 O → Tendsto inv l (𝓝 z₀) → Tendsto (fun ζ => v ζ - w₂ ζ) l (𝓝 0))
    (hF : ∀ y ∈ H, F y ∈ O) (hinvF : Tendsto (fun y => inv (F y)) (𝓝[H] x') (𝓝 z₀))
    (hdet : Tendsto (fun y => w₂ (F y) - M (F y)) (𝓝[H] x') (𝓝 0)) :
    Tendsto (fun y => v (F y) - M (F y)) (𝓝[H] x') (𝓝 0) := by
  have hl : Filter.map F (𝓝[H] x') ≤ 𝓟 O := by
    rw [Filter.le_principal_iff, Filter.mem_map]
    exact Filter.mem_of_superset self_mem_nhdsWithin fun y hy => hF y hy
  have h1 := (hconv _ hl (Filter.tendsto_map'_iff.2 hinvF)).comp Filter.tendsto_map
  have h2 := h1.add hdet
  rw [add_zero] at h2
  refine h2.congr' (Eventually.of_forall fun y => ?_)
  simp only [Function.comp_apply]
  ring

end Slit

end InteractingSLE.Sec5.Aux61SlitV
