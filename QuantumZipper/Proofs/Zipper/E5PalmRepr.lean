import QuantumZipper.Proofs.Zipper.E5PalmJoint
import QuantumZipper.Proofs.Zipper.E5Main1

/-!
# E5-PALM, part 2: the Palm representation of E5's left side (iterated form)

Task E5-PALM. Sheffield, arXiv:1012.4797, §5.4 (pp. 66–72), proof of Lemma 5.6: under the Palm
measure `P ⊗ ν_ω|_{[−δ,0] ∩ {τ<T}}`, E5's zoomed configuration `Z_C C̄_x` can be computed with the
true normalized collided field `Y_τ − m` replaced by `targetColl κ V τ ϖ X'` for an independent
free field `X'` (E4, extended to joint tests in `E5PalmJoint`).

E4 only controls the field through `coordsFull` (raw values at dyadic folded circles), while the
local data `loc R (Z_C …)` read the **canonically rescaled** field (at a random, non-dyadic scale)
and, for `locFieldFull`, raw test pairings; the driver is read at random times `a² s`. So the
transfer needs a **readability input** (`PalmReadable`): one fixed measurable reader `Rd` of
`(x, V^τ, W⁰, coordsFull)` which, test by test, reproduces the local data a.e. on both sides of
E4. (This is the Palm-side analogue of `E6.RegReadable`/`E6.ReadableBy`; per-test a.e. equality
is the right form since `locFieldFull` has uncountably many pairing coordinates, and a measurable
test depends on countably many.) It is stated as an exact named Prop, not assumed elsewhere.

* `palm_repr_iter`: `lhsF … C Γ = ∫⁻ ω ∫⁻_{[−δ,0]} 1_{τ<T} ∫⁻ Γ(Zc C ω x ω') dP' dν_ω dP`,
  with `Zc` the zoomed configuration built from `targetColl … X'` and the collided driver.

Own bookkeeping around E4 (`e4_joint`).
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal ENNReal

namespace QuantumZipper
namespace E5

open B2 E1 CoordsFull E4Grid

/-- The zoomed configuration on the E4 model side: the collision target field `targetColl … X'`
shifted by `C/γ`, with the collided driver, canonicalized. -/
def zcfgT {Ω Ω' : Type*} (κ T : ℝ) (B : ℝ≥0 → Ω → ℝ) (X : Ω → FieldSample) (ϖ : Measure ℂ)
    (X' : Ω' → FieldSample) (C : ℝ) (ω : Ω) (x : ℝ) (ω' : Ω') : FieldSample × (ℝ → ℝ) :=
  canonConfig (Real.sqrt κ) (addConst (targetColl κ (Vr κ T B ω) (palmTau κ T B ω x) ϖ (X' ω'))
    (C / Real.sqrt κ), (collided κ T B X ω x).2)

/-- **Palm readability input** (named hypothesis, level `C`, radius `R`): a measurable reader
`Rd` of `(x, V^τ, W⁰, coordsFull)` such that, for every measurable test `Γ`, a.e. under the Palm
measure (on `{τ < T}`) `Γ ∘ loc R` of E5's zoomed configuration equals `Γ ∘ Rd` of the true E4
data, and a.e. (also in `X'`) `Γ ∘ loc R` of the model configuration `zcfgT` equals `Γ ∘ Rd` of
the model E4 data. -/
def PalmReadable {L : Type*} [MeasurableSpace L] (loc : ℕ → FieldSample × (ℝ → ℝ) → L)
    (κ T : ℝ) {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (B : ℝ≥0 → Ω → ℝ)
    (X : Ω → FieldSample) (ϖ : Measure ℂ) {Ω' : Type*} [MeasurableSpace Ω'] (P' : Measure Ω')
    (X' : Ω' → FieldSample) (δ : ℝ) (R : ℕ) (C : ℝ) (Rd : CfgE × (ℕ → ℝ) → L) : Prop :=
  Measurable Rd ∧ ∀ Γ : L → ℝ≥0∞, Measurable Γ →
    (∀ᵐ ω ∂P, ∀ᵐ x ∂(nuPalm κ T B X ϖ ω).restrict (Icc (-δ) 0), x ∈ palmA κ T B ω →
      Γ (loc R (zcfg κ T B X ϖ C ω x)) = Γ (Rd (palmQ κ T B ω x, palmPhi κ T B X ϖ ω x))) ∧
    (∀ᵐ ω ∂P, ∀ᵐ x ∂(nuPalm κ T B X ϖ ω).restrict (Icc (-δ) 0), x ∈ palmA κ T B ω →
      ∀ᵐ ω' ∂P', Γ (loc R (zcfgT κ T B X ϖ X' C ω x ω')) =
        Γ (Rd (palmQ κ T B ω x, palmR κ T B ϖ X' ω x ω')))

variable {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {κ T : ℝ} {B : ℝ≥0 → Ω → ℝ} {X : Ω → FieldSample} {ϖ : Measure ℂ}
  {Ω' : Type} [MeasurableSpace Ω'] {P' : Measure Ω'} [IsProbabilityMeasure P']
  {X' : Ω' → FieldSample}

/-- **Palm representation of E5's left side** (iterated form): given E5's setup, an independent
free field `X'`, `δ > 0` and the readability input at level `C`, for every measurable test `Γ`,
E5's left side equals the Palm integral of the `X'`-average of `Γ ∘ loc R` of the model
configuration `zcfgT`. -/
theorem palm_repr_iter {L : Type*} [MeasurableSpace L] (loc : ℕ → FieldSample × (ℝ → ℝ) → L)
    (hS : E5.Setup κ T P B X ϖ) (hX' : IsFreeGFFModConstH X' P') {δ : ℝ} (hδ : 0 < δ)
    (R : ℕ) (C : ℝ) {Rd : CfgE × (ℕ → ℝ) → L}
    (hRd : PalmReadable loc κ T P B X ϖ P' X' δ R C Rd) (Γ : L → ℝ≥0∞) (hΓ : Measurable Γ) :
    lhsF loc κ T P B X ϖ δ R C Γ =
      ∫⁻ ω, ∫⁻ x in Icc (-δ) 0, (palmA κ T B ω).indicator
        (fun x => ∫⁻ ω', Γ (loc R (zcfgT κ T B X ϖ X' C ω x ω')) ∂P') x
          ∂nuPalm κ T B X ϖ ω ∂P := by
  obtain ⟨hRdm, hread⟩ := hRd
  obtain ⟨h1, h2⟩ := hread Γ hΓ
  have hj := e4_joint hS hX' hδ (Γ ∘ Rd) (hΓ.comp hRdm)
  calc lhsF loc κ T P B X ϖ δ R C Γ
      = ∫⁻ ω, ∫⁻ x in Icc (-δ) 0, jointL κ T B X ϖ (Γ ∘ Rd) ω x ∂nuPalm κ T B X ϖ ω ∂P := by
        refine lintegral_congr_ae ?_
        filter_upwards [h1] with ω hω
        refine lintegral_congr_ae ?_
        filter_upwards [hω] with x hx
        by_cases hA : x ∈ palmA κ T B ω
        · change (palmA κ T B ω).indicator _ x = (palmA κ T B ω).indicator _ x
          rw [indicator_of_mem hA, indicator_of_mem hA]
          exact hx hA
        · change (palmA κ T B ω).indicator _ x = (palmA κ T B ω).indicator _ x
          rw [indicator_of_notMem hA, indicator_of_notMem hA]
    _ = ∫⁻ ω, ∫⁻ x in Icc (-δ) 0, jointR κ T B ϖ P' X' (Γ ∘ Rd) ω x ∂nuPalm κ T B X ϖ ω ∂P := hj
    _ = _ := by
        refine lintegral_congr_ae ?_
        filter_upwards [h2] with ω hω
        refine lintegral_congr_ae ?_
        filter_upwards [hω] with x hx
        by_cases hA : x ∈ palmA κ T B ω
        · simp only [jointR, indicator_of_mem hA, Function.comp_apply]
          exact lintegral_congr_ae ((hx hA).mono fun ω' h => h.symm)
        · simp only [jointR, indicator_of_notMem hA]

end E5
end QuantumZipper
