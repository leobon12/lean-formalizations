/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec5.CfGivenKernel
import InteractingSLE.Spec.Sec5.RestartSwMain
import InteractingSLE.Spec.Supplement.CondDriverBridge
import InteractingSLE.Spec.Supplement.StagedRegularize
import InteractingSLE.Spec.Sec7.Prop74BMain

/-!
# Lemma 4.7's conditional law at a switch time from its unconditional (`P`-side) form

Packet PROVE-CFGIVEN. `RestartSw.CounterflowGivenPrefixStatement` (PROVE-SWITCHED's named input) asks, for almost
every `ω₀`, for a centred counterflow driver of the field read in the record chart of the flow prefix of `ω₀`, under the
regular conditional law given that record. Following the source (Lemma 4.7's proof, spec p. 118: the conditional law of
`η′` given `η([0, τ])` from Propositions 3.7–3.8 and Theorem 2.4), this file reduces it to its **unconditional form**
on the given space (`CfGivenPSideStatement`): with `𝒢` the σ-algebra of the record `R = recOf t₀ D`, a filtration
`𝓗 ⊇ 𝒢` carrying a globally continuous driver `W″` from `0` (the image counterflow driver in the record chart), the
geometric images of a `𝒢`-measurable flow-type word, almost surely infinite continuation threshold, and K2's inputs:

* (S) `HasSafeLaw`: the field `X = imgField κ R h` (the field read in the record chart and then in the chart
  `R(z) = −1/z` with the counterflow rule) has, on the avoidance events of `𝓗_q`, the coupling characteristic
  functional of the image word at every capacity time `q` (Lemma 4.7's coupling clause in image coordinates);
* (L) `HasSafeMembers`: the image hulls are local for `X` given `𝓗` (the union of the flow prefix and the counterflow
  hull is local);

together with the pathwise identification of the image trace with the physical counterflow.

The kernel step is `CfGivenKernel.ae_isOptionalHullCoupling_of_hasSafeLaw_top` (K2 on the space itself, the threshold
being infinite), followed by the identification of the field (`imgField` of the record at `ω₀`, kernel-almost surely)
and of the word (`FCDet.IsFlowType`) with the frozen `IsCenteredCounterflowDriver`.

## Main results

* `imgField`, `isChartTransport_imgField`, `measurable_imgField`;
* **`isCenteredCounterflowDriver_of_isFlowType`**: an optional hull coupling at `16/κ` of a flow-type word, for a
  field transported from `f` by the counterflow rule through `R`, is a centred counterflow driver of `f`;
* **`ae_isCenteredCounterflowDriver_of_hasSafeLaw`**: (S), (L) and the threshold give, for almost every `ω₀`, the
  centred counterflow of the field read in the record chart of `ω₀`, under `condExpKernel P (σ(R)) ω₀`;
* `CfGivenPSideStatement` (named input: Lemma 4.7's coupling in unconditional form) and
  **`counterflowGivenPrefixStatement_of_pSide`**.

R48: nothing here uses Theorem 1.2/1.3, `Theorem12ParamStatement`, `Theorem13Statement` or any `*_of_param`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open QuantumZipper (H fwdHull chiC)
open LQGMetric (TestOn DistOn)
open scoped NNReal ENNReal Real

universe u

namespace InteractingSLE.Sec5.CfGiven

open Restart Restart.DomainMarkov Restart.DomainMarkov.K2 Sec7.Aux122Disint Sec7.PocketTraversal
open Exist Exist.Staged Exist.StagedLaw
open WangWu (negInv)

/-! ### The field read in the image chart -/

/-- **The field read in the record chart and then in the chart `R(z) = −1/z` with the counterflow rule**
(`IsCenteredCounterflowDriver`'s transport `(σ, a, k) = (−1, −πχ, χ(16/κ))` of `recField κ r f`). -/
def imgField (κ : ℝ) (r : RecData) (f : DistOn upperHalfPlaneOpens) : DistOn upperHalfPlaneOpens :=
  Chart.chartTransport Chart.isConformal_infinitySourceChart (-1) (-(π * chiC κ)) (chiC (16 / κ))
    (recField κ r f)

theorem isChartTransport_imgField (κ : ℝ) (r : RecData) (f : DistOn upperHalfPlaneOpens) :
    IsChartTransport infinitySourceChart (-1) (-(π * chiC κ)) (chiC (16 / κ)) (recField κ r f)
      (imgField κ r f) :=
  Chart.isChartTransport_chartTransport Chart.isConformal_infinitySourceChart
    (Chart.locallyIntegrableOn_of_continuousOn Chart.continuousOn_infinitySourceChart_lift) _ _ _ _

theorem measurable_imgField (κ : ℝ) :
    Measurable fun p : RecData × DistOn upperHalfPlaneOpens => imgField κ p.1 p.2 :=
  (Chart.measurable_chartTransport Chart.isConformal_infinitySourceChart _ _ _).comp (measurable_recField κ)

/-! ### From a coupling of a flow-type word to the centred counterflow -/

section Bridge

/-- The translate by `0` with the constant `0 · c` is the identity. -/
theorem isTranslateAddConst_zero_mul_self (X : DistOn upperHalfPlaneOpens) (c : ℝ) :
    IsTranslateAddConst 0 (0 * c) X X := by
  intro φ φ' hφ
  have e : φ' = φ := DFunLike.ext _ _ fun z => by rw [hφ z, Complex.ofReal_zero, add_zero]
  rw [e, zero_mul, zero_mul, add_zero]

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {κ : ℝ} {nL nR : ℕ} {xL : Fin nL → ℝ} {xR : Fin nR → ℝ}
  {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ}

/-- **An optional hull coupling at `16/κ` of a flow-type word is a centred counterflow driver.** If the word
`(xL, xR, ρL, ρR)` is the angle-`0` flow-line word of a boundary word `c` at `16/κ`, and `g` is the counterflow-rule
transport of `f` through `R(z) = −1/z`, a coupling of the word with the field `g` makes the driver a centred counterflow
driver of `f` (the data of the frozen predicate are `c`). -/
theorem isCenteredCounterflowDriver_of_isFlowType {Q : Measure Ω} {c : BoundaryWord}
    (htype : FCDet.IsFlowType (16 / κ) 0 c xL xR ρL ρR) {f g : Ω → DistOn upperHalfPlaneOpens}
    (htr : ∀ ω, IsChartTransport infinitySourceChart (-1) (-(π * chiC κ)) (chiC (16 / κ)) (f ω) (g ω))
    {𝓕 : Filtration ℝ≥0 mΩ} {W : ℝ≥0 → Ω → ℝ} {VL : Fin nL → ℝ≥0 → Ω → ℝ} {VR : Fin nR → ℝ≥0 → Ω → ℝ}
    {B : ℝ≥0 → Ω → ℝ} {ζ : Ω → ℝ≥0∞} (hc : IsOptionalHullCoupling (16 / κ) xL xR ρL ρR Q 𝓕 W VL VR B ζ g) :
    IsCenteredCounterflowDriver κ Q f W ζ := by
  obtain ⟨eL, eR, hxL, hxR, hρL, hρR⟩ := htype
  have h' := FCDet.isOptionalHullCoupling_cast eL eR hc
  rw [hxL, hxR, hρL, hρR] at h'
  exact ⟨c.fn, c.jumps, g, c.isPiecewiseConstantBoundaryData, htr, g, 𝓕, _, _, B,
    fun ω => isTranslateAddConst_zero_mul_self (g ω) _, h'⟩

end Bridge

/-! ### The kernel step for the image counterflow -/

section Kernel

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {κ : ℝ} {nL nR : ℕ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ}

/-- **The centred counterflow of the field read in the record chart, under the regular conditional law given the
record**, from K2's inputs (S) and (L) for the image field `imgField κ R h` and the image driver `W` (globally
continuous from `0`, adapted to `𝓗 ⊇ σ(R)`, with the geometric images of a `σ(R)`-measurable flow-type word and
almost surely infinite threshold). -/
theorem ae_isCenteredCounterflowDriver_of_hasSafeLaw (hκ : 0 < κ) {h : Ω → DistOn upperHalfPlaneOpens}
    (hh : Measurable h) {R : Ω → RecData} (hR : Measurable R) {𝓗 : Filtration ℝ≥0 mΩ}
    (h𝒢 : MeasurableSpace.comap R inferInstance ≤ 𝓗 0) {xL : Ω → Fin nL → ℝ} {xR : Ω → Fin nR → ℝ}
    (hxL : Measurable[MeasurableSpace.comap R inferInstance] xL)
    (hxR : Measurable[MeasurableSpace.comap R inferInstance] xR) (hxL0 : ∀ ω i, xL ω i ≤ 0)
    (hxR0 : ∀ ω j, 0 ≤ xR ω j) (hxLa : ∀ ω, Antitone (xL ω)) (hxRm : ∀ ω, Monotone (xR ω))
    {W : ℝ≥0 → Ω → ℝ} (hW0 : ∀ ω, W 0 ω = 0) (hWc : ∀ ω, Continuous fun t => W t ω) (hWa : StronglyAdapted 𝓗 W)
    (hint : ∀ φ : TestOn upperHalfPlaneOpens, Integrable (fun ω => imgField κ (R ω) (h ω) φ) P)
    (hthr : ∀ᵐ ω ∂P, FCDet.thr ρL ρR W xL xR ω = ⊤)
    (htype : ∀ᵐ ω ∂P, ∃ c : BoundaryWord, FCDet.IsFlowType (16 / κ) 0 c (xL ω) (xR ω) ρL ρR)
    (hlaw : HasSafeLaw (16 / κ) ρL ρR P 𝓗 univ (fun _ => ⊤) W (geomLW W xL) (geomRW W xR)
      (fun ω => imgField κ (R ω) (h ω)))
    (hmem : HasSafeMembers P 𝓗 univ (fun _ => ⊤) W (fun ω => imgField κ (R ω) (h ω))) :
    ∀ᵐ ω₀ ∂P, IsCenteredCounterflowDriver κ (condExpKernel P (MeasurableSpace.comap R inferInstance) ω₀)
      (fun ω => recField κ (R ω₀) (h ω)) W (fun _ => ⊤) := by
  have h𝒢m : MeasurableSpace.comap R inferInstance ≤ mΩ := hR.comap_le
  have hX : Measurable fun ω => imgField κ (R ω) (h ω) :=
    Measurable.comp (g := fun p : RecData × DistOn upperHalfPlaneOpens => imgField κ p.1 p.2)
      (f := fun ω => (R ω, h ω)) (measurable_imgField κ) (hR.prodMk hh)
  have h16 : 0 < 16 / κ := by positivity
  have hK := ae_isOptionalHullCoupling_of_hasSafeLaw_top (𝒢 := MeasurableSpace.comap R inferInstance)
    (κ := 16 / κ) h16 h𝒢 hxL hxR hxL0 hxR0 hxLa hxRm hW0 hWc hWa hX hint hthr hlaw hmem
  have hReq := ae_ae_condExpKernel_eq (P := P) h𝒢m (f := R) (Measurable.of_comap_le le_rfl)
  have hWm : ∀ t, Measurable (W t) := fun t => (hWa t).measurable.mono (𝓗.le t) le_rfl
  filter_upwards [hK, hReq, htype] with ω₀ hK₀ hR₀ hty₀
  obtain ⟨𝓕', W', VL', VR', B', hcpl, hag⟩ := hK₀
  obtain ⟨c, hc⟩ := hty₀
  have hg₀m : Measurable fun ω => imgField κ (R ω₀) (h ω) :=
    Measurable.comp (g := fun p : RecData × DistOn upperHalfPlaneOpens => imgField κ p.1 p.2)
      (f := fun ω => (R ω₀, h ω)) (measurable_imgField κ) (measurable_const.prodMk hh)
  have he : (fun ω => imgField κ (R ω₀) (h ω)) =ᵐ[condExpKernel P (MeasurableSpace.comap R inferInstance) ω₀]
      fun ω => imgField κ (R ω) (h ω) := by
    filter_upwards [hR₀] with ω hω
    rw [hω]
  have hgff : ∀ u₀ : ℂ → ℝ, IsBoundedHarmonicExtension (forceBoundaryData (16 / κ) ρL ρR (xL ω₀) (xR ω₀))
      (forceJumpSet (xL ω₀) (xR ω₀)) u₀ →
      LQGMetric.IsZBGFFProcess upperHalfPlaneOpens (fun φ ω => imgField κ (R ω₀) (h ω) φ - ∫ z, u₀ z * φ z)
        (condExpKernel P (MeasurableSpace.comap R inferInstance) ω₀) := fun u₀ hu₀ =>
    Theorem14.CondDriverBridge.isZBGFFProcess_congr_ae (hcpl.2.2.1 u₀ hu₀)
      (fun φ => ((LQGMetric.measurable_distOn_apply φ).comp hg₀m).sub_const _)
      (fun φ => he.mono fun ω hω => by simp only [hω])
  have hcpl' := Sec7.Prop74B.IsOptionalHullCoupling.congr_field hcpl hg₀m hgff he
  obtain ⟨b', J', h', hb', htr', hfl⟩ := isCenteredCounterflowDriver_of_isFlowType hc
    (fun ω => isChartTransport_imgField κ (R ω₀) (h ω)) hcpl'
  refine ⟨b', J', h', hb', htr', Theorem14.StagedReg.isFlowLineDriver_congr_ae hfl hWm ?_⟩
  filter_upwards [hag] with ω hω
  exact ⟨(hω 0).1.symm, fun t _ => (hω t).1.symm⟩

end Kernel

/-! ### The named input and the reduction -/

/-- **Named input: Lemma 4.7's conditional law at a deterministic own time, in unconditional form** (spec p. 118:
"the conditional law of `η′` given `η([0, τ])` … Propositions 3.7–3.8 and Theorem 2.4"; Lemma 5.7's proof, p. 138).
Binders verbatim from `RestartSw.CounterflowGivenPrefixStatement`. With `R = recOf t₀ D` (the record of the flow prefix)
and `𝒢 = σ(R)`, there are a filtration `𝓗 ⊇ 𝒢`, a word type `(nL, nR, ρL, ρR)`, `𝒢`-measurable ordered positions
`(xL, xR)` (the images of the counterflow's marks and of the two sides of the prefix, a flow-type word almost surely),
a globally continuous `𝓗`-adapted driver `W″` from `0` (the image counterflow driver in the record chart) with almost
surely infinite continuation threshold, and a family `η″`, such that

* the image field `imgField κ R h` has integrable pairings and satisfies K2's (S) and (L) for `W″` with lifetime `⊤`
  (Lemma 4.7's coupling clause in image coordinates, and the locality of the union of the prefix and the counterflow
  hull, given `𝒢` and the image counterflow up to each capacity time);
* almost surely `η″` is the generating trace of `W″` and a continuous increasing clock `ℓ` from `0` carries it to the
  physical counterflow: `R(η′(ℓ u)) = c⁻¹(R(η″ u))`, `R(η″ u) ∈ ℍ`, `u > 0` (as in the conditional statement). -/
def CfGivenPSideStatement : Prop :=
  ∀ (κ : ℝ) (b : ℝ → ℝ) (J : Finset ℝ) {Ω : Type u} [MeasurableSpace Ω] [StandardBorelSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (h : Ω → DistOn upperHalfPlaneOpens) (W' : ℝ≥0 → Ω → ℝ) (ζ' : Ω → ℝ≥0∞),
    0 < κ → κ < 4 → IsPiecewiseConstantBoundaryData b J → IsGFFWithBoundaryData P h b J →
    IsCenteredCounterflowDriver κ P h W' ζ' → (∀ᵐ ω ∂P, ζ' ω = ⊤) →
    (∀ a ∈ Icc (-(π / 2)) (π / 2), ∀ y : ℝ, y < 0 → y ∉ J → b y + a * chiC κ ≤ -sleLambda κ) →
    (∀ a ∈ Icc (-(π / 2)) (π / 2), ∀ y : ℝ, 0 < y → y ∉ J → sleLambda κ ≤ b y + a * chiC κ) →
    ∀ θ₀ : ℝ, θ₀ ∈ Icc (-(π / 2)) (π / 2) → ∀ D : Ω → (ℝ≥0 → ℝ) × ℝ≥0∞, Measurable D →
    (∀ ω, IsRegularDriver (D ω)) → IsFlowLineDriver κ b J θ₀ P h (fun t ω => (D ω).1 t) (fun ω => (D ω).2) →
    ∀ (t₀ : ℝ≥0) (η : Ω → ℝ≥0 → ℂ), (∀ᵐ ω ∂P, IsGeneratingTrace (fun t => W' t ω) ⊤ (η ω)) →
    ∃ (𝓗 : Filtration ℝ≥0 (inferInstance : MeasurableSpace Ω)) (nL nR : ℕ) (ρL : Fin nL → ℝ) (ρR : Fin nR → ℝ)
      (xL : Ω → Fin nL → ℝ) (xR : Ω → Fin nR → ℝ) (W'' : ℝ≥0 → Ω → ℝ) (η'' : Ω → ℝ≥0 → ℂ),
      MeasurableSpace.comap (fun ω => recOf (t₀ : ℝ≥0∞) (D ω)) inferInstance ≤ 𝓗 0 ∧
      Measurable[MeasurableSpace.comap (fun ω => recOf (t₀ : ℝ≥0∞) (D ω)) inferInstance] xL ∧
      Measurable[MeasurableSpace.comap (fun ω => recOf (t₀ : ℝ≥0∞) (D ω)) inferInstance] xR ∧
      (∀ ω i, xL ω i ≤ 0) ∧ (∀ ω j, 0 ≤ xR ω j) ∧ (∀ ω, Antitone (xL ω)) ∧ (∀ ω, Monotone (xR ω)) ∧
      (∀ ω, W'' 0 ω = 0) ∧ (∀ ω, Continuous fun t => W'' t ω) ∧ StronglyAdapted 𝓗 W'' ∧
      (∀ᵐ ω ∂P, FCDet.thr ρL ρR W'' xL xR ω = ⊤) ∧
      (∀ᵐ ω ∂P, ∃ c : BoundaryWord, FCDet.IsFlowType (16 / κ) 0 c (xL ω) (xR ω) ρL ρR) ∧
      (∀ φ : TestOn upperHalfPlaneOpens,
        Integrable (fun ω => imgField κ (recOf (t₀ : ℝ≥0∞) (D ω)) (h ω) φ) P) ∧
      HasSafeLaw (16 / κ) ρL ρR P 𝓗 univ (fun _ => ⊤) W'' (geomLW W'' xL) (geomRW W'' xR)
        (fun ω => imgField κ (recOf (t₀ : ℝ≥0∞) (D ω)) (h ω)) ∧
      HasSafeMembers P 𝓗 univ (fun _ => ⊤) W'' (fun ω => imgField κ (recOf (t₀ : ℝ≥0∞) (D ω)) (h ω)) ∧
      ∀ᵐ ω ∂P, IsGeneratingTrace (fun t => W'' t ω) ⊤ (η'' ω) ∧
        ∃ ℓ : ℝ≥0 → ℝ≥0, Continuous ℓ ∧ StrictMono ℓ ∧ ℓ 0 = 0 ∧
          ∀ u : ℝ≥0, 0 < u → negInv (η'' ω u) ∈ H ∧
            negInv (η ω (ℓ u)) = (recChart (recOf (t₀ : ℝ≥0∞) (D ω))).2.1 (negInv (η'' ω u))

/-- **Lemma 4.7's conditional law at a switch time from its unconditional form**: `CfGivenPSideStatement` implies
PROVE-SWITCHED's `RestartSw.CounterflowGivenPrefixStatement` (K2 on the space itself, the field and word
identifications of this file; the lifetime is `⊤`). -/
theorem counterflowGivenPrefixStatement_of_pSide (hS : CfGivenPSideStatement.{u}) :
    RestartSw.CounterflowGivenPrefixStatement.{u} := by
  intro κ b J Ω mΩ hΩ P hP h W' ζ' hκ hκ4 hb hh hcf hζ' hleft hright θ₀ hθ₀ D hDm hDreg hD t₀ η hη
  obtain ⟨𝓗, nL, nR, ρL, ρR, xL, xR, W'', η'', h𝒢, hxL, hxR, hxL0, hxR0, hxLa, hxRm, hW0, hWc, hWa, hthr, htype,
    hint, hlaw, hmem, hpath⟩ := hS κ b J P h W' ζ' hκ hκ4 hb hh hcf hζ' hleft hright θ₀ hθ₀ D hDm hDreg hD t₀ η hη
  have hRm : Measurable fun ω => recOf (t₀ : ℝ≥0∞) (D ω) := measurable_recOf hDm hDreg _
  refine ⟨W'', fun _ => ⊤, η'', ?_, hpath⟩
  filter_upwards [ae_isCenteredCounterflowDriver_of_hasSafeLaw hκ hh.1 hRm h𝒢 hxL hxR hxL0 hxR0 hxLa hxRm hW0 hWc
    hWa hint hthr htype hlaw hmem] with ω₀ hω₀
  exact ⟨hω₀, ae_of_all _ fun _ => rfl⟩

end InteractingSLE.Sec5.CfGiven
