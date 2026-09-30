import QuantumZipper.Proofs.Zipper.LocRichBasic

/-!
# D3⁺(i), (ii) for the rich local data (decision D25)

Decision **D25** (`DECISIONS.md`). The statements `D3PlusIStmt`, `D3PlusIIStmt` of
`D3PlusStmt.lean` (decision D23) with `TV.locField R` replaced by the rich local field data
`locFieldFull R` (raw values at all `coordsFull` circles inside `closedBall 0 R` and raw pairings
with all test functions supported in `closedBall 0 R`). Hypotheses (`Setup`), model field
(`zoomModel`), local reading (`canonicalOn` on `halfDisc r`) and the two-sided `ℝ≥0∞`
conditional TV form are unchanged.

The rich statements are **stronger** than D23's: `d3PlusI_of_rich`, `d3PlusII_of_rich`
(`locField R = (projection) ∘ locFieldFull R`, `D3Plus.locField_eq_proj`).
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal ENNReal

namespace QuantumZipper
namespace D3Plus

/-- Projection of rich local field data onto D23's local field data. -/
def projField (y : (ℕ → ℝ) × (TestFun H → ℝ)) : ℕ → ℝ := fun n => y.1 (E6.fullIdx n)

theorem measurable_projField : Measurable projField :=
  measurable_pi_iff.2 fun n => (measurable_pi_apply (E6.fullIdx n)).comp measurable_fst

theorem locField_eq_projField (R : ℕ) (x : FieldSample) :
    TV.locField R x = projField (locFieldFull R x) :=
  funext fun n => locField_eq_proj R x n

/-- **D3⁺(i), rich form**: as `D3PlusIStmt`, for the rich local field data `locFieldFull R`. -/
def D3PlusIStmtRich : Prop :=
  ∀ (γ α r : ℝ) (ρ₀ : Measure ℂ) {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (X : Ω → FieldSample) {E' : Type} [MeasurableSpace E'] (Ξ : Ω → E')
    (g : Ω → ℂ → ℝ) {Ω' : Type} [MeasurableSpace Ω'] (P' : Measure Ω')
    [IsProbabilityMeasure P'] (Y' : Ω' → FieldSample),
    Setup γ α r ρ₀ P X Ξ g → IsQuantumWedge γ α Y' P' →
    ∀ R : ℕ, ∀ η : ℝ≥0∞, 0 < η → ∀ᶠ L in atTop,
      ∀ Φ : Ω × ((ℕ → ℝ) × (TestFun H → ℝ)) → ℝ≥0∞,
        Measurable[(condSigma Ξ X r).prod inferInstance] Φ → (∀ p, Φ p ≤ 1) →
        let lhs := ∫⁻ ω, Φ (ω, locFieldFull R
          (canonicalOn γ (zoomModel γ α L ρ₀ (X ω) (g ω)) (halfDisc r))) ∂P
        let rhs := ∫⁻ ω, ∫⁻ ω', Φ (ω, locFieldFull R (Y' ω')) ∂P' ∂P
        lhs ≤ rhs + η ∧ rhs ≤ lhs + η

/-- The pair (rich local canonical data, log of the local scale) of the model field. -/
def zoomPairRich (γ α L r : ℝ) (R : ℕ) (ρ₀ : Measure ℂ) (x : FieldSample) (g : ℂ → ℝ) :
    ((ℕ → ℝ) × (TestFun H → ℝ)) × ℝ :=
  (locFieldFull R (canonicalOn γ (zoomModel γ α L ρ₀ x g) (halfDisc r)),
    Real.log (scaleParamOn γ (zoomModel γ α L ρ₀ x g) (halfDisc r)))

/-- **D3⁺(ii), rich form (LSC)**: as `D3PlusIIStmt`, for `zoomPairRich`. -/
def D3PlusIIStmtRich : Prop :=
  ∀ (γ α r : ℝ) (ρ₀ : Measure ℂ) {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (X : Ω → FieldSample) {E' : Type} [MeasurableSpace E'] (Ξ : Ω → E')
    (g g' : Ω → ℂ → ℝ) (K : ℝ),
    Setup γ α r ρ₀ P X Ξ g → Setup γ α r ρ₀ P X Ξ g' →
    (∀ ω, ∀ z ∈ Metric.ball (0 : ℂ) r ∩ Hbar, |g ω z - g' ω z| ≤ K) →
    ∀ R : ℕ, ∀ η : ℝ≥0∞, 0 < η → ∀ᶠ L in atTop,
      ∀ Φ : Ω × (((ℕ → ℝ) × (TestFun H → ℝ)) × ℝ) → ℝ≥0∞,
        Measurable[(condSigma Ξ X r).prod inferInstance] Φ → (∀ p, Φ p ≤ 1) →
        let lhs := ∫⁻ ω, Φ (ω, zoomPairRich γ α L r R ρ₀ (X ω) (g ω)) ∂P
        let rhs := ∫⁻ ω, Φ (ω, zoomPairRich γ α L r R ρ₀ (X ω) (g' ω)) ∂P
        lhs ≤ rhs + η ∧ rhs ≤ lhs + η

/-- Precomposition with `id × f` preserves `condSigma ⊗ Borel`-measurability. -/
theorem measurable_prod_precomp {Ω A B : Type*} (m : MeasurableSpace Ω) [MeasurableSpace A]
    [MeasurableSpace B] {f : A → B} (hf : Measurable f) {Φ : Ω × B → ℝ≥0∞}
    (hΦ : Measurable[m.prod inferInstance] Φ) :
    Measurable[m.prod inferInstance] fun p : Ω × A => Φ (p.1, f p.2) := by
  letI : MeasurableSpace Ω := m
  exact hΦ.comp (measurable_fst.prodMk (hf.comp measurable_snd))

/-- The rich D3⁺(i) implies D23's D3⁺(i). -/
theorem d3PlusI_of_rich (h : D3PlusIStmtRich) : D3PlusIStmt := by
  intro γ α r ρ₀ Ω _ P _ X E' _ Ξ g Ω' _ P' _ Y' hS hW R η hη
  filter_upwards [h γ α r ρ₀ P X Ξ g P' Y' hS hW R η hη] with L hL Φ hΦ hΦ1
  have := hL (fun p => Φ (p.1, projField p.2))
    (measurable_prod_precomp _ measurable_projField hΦ) (fun p => hΦ1 _)
  simpa only [locField_eq_projField] using this

end D3Plus
end QuantumZipper
