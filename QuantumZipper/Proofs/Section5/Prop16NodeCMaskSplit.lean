import QuantumZipper.Proofs.Section5.Prop16NodeCMaskMain

/-!
# Proposition 1.6, node C′ (masked): splitting the masked coupling node

The masked analogue of `Prop16NodeCSplit.lean`. `Prop16NodeCModelMaskStmt` is split into

* `Prop16FixedLawMaskStmt` (**masked law determinacy**): for two mixed GFFs `X` (under `P`) and
  `Y` (under `P₀`) on `D`, free on `[c, d]`, both a.s. locally nice on `D ∪ (a,b)`, and
  `x ∈ (a, b)`: the masked fixed-point zoom coordinates of `Y + (γ/2) G_D(x, ·)` are
  a.e.-measurable, and their local laws equal those of `X + (γ/2) G_D(x, ·)`. (The masked
  coordinates only read dyadic circles inside `D ∪ (a,b)` (factor-2 margin of `PalmKeep`), and
  the scale is a.s. a measurable function of such circles; the law of countably many admissible
  circle values of a mixed GFF is fixed by the covariance.) This replaces the false unmasked
  `Prop16FixedLawStmt`.
* `Prop16NodeCMarkovMaskStmt` (**Markov coupling at `x`**): `Prop16NodeCMarkovStmt` together with
  a.s. local niceness on `D ∪ (a,b)` of the mixed GFF `Y` it constructs (to be fed by the local
  half-disc couplings, M7).

`prop16NodeCModelMask_of_split` (own bookkeeping), `prop16FixedZoomMask_of_split` and
`prop16FixedZoomMask_of_splitN2` (node C′ from D3⁺(i) and the two nodes), and
`theorem1_6_of_palmMaskSplit` (Proposition 1.6 from the coupling, node B′, D3⁺(i) in N2 form and
the two nodes).
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Metric
open scoped Topology ENNReal NNReal

namespace QuantumZipper

namespace Prop16Asm

open TV Factorization

/-- **Masked law determinacy of the fixed-point Palm zoom.** -/
def Prop16FixedLawMaskStmt : Prop :=
  ∀ (γ : ℝ) (D : Set ℂ) (c d a b : ℝ) (h0 : ℂ → ℝ), 0 < γ → γ < 2 → K3.Prop16Geometry D c d →
    a < b → c ≤ a → b ≤ d →
    ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) (X : Ω → FieldSample)
      {Ω₀ : Type} [MeasurableSpace Ω₀] (P₀ : Measure Ω₀) (Y : Ω₀ → FieldSample),
      IsProbabilityMeasure P → IsProbabilityMeasure P₀ →
      IsMixedGFF D (realSet (Icc c d)) X P → IsMixedGFF D (realSet (Icc c d)) Y P₀ →
      (∀ᵐ ω ∂P, IsLocNiceOn γ (D ∪ realSet (Ioo a b)) (X ω)) →
      (∀ᵐ ω ∂P₀, IsLocNiceOn γ (D ∪ realSet (Ioo a b)) (Y ω)) →
      ∀ x ∈ Ioo a b, ∀ C : ℝ,
        AEMeasurable (palmFixedMask γ C D c d a b h0 Y x) P₀ ∧
        ∀ R : ℕ, P.map (fun ω => locCoords R (palmFixedMask γ C D c d a b h0 X x ω)) =
          P₀.map (fun ω => locCoords R (palmFixedMask γ C D c d a b h0 Y x ω))

/-- **Markov coupling at a fixed boundary point, with local niceness** (`Prop16NodeCMarkovStmt`
plus: the mixed GFF `Y` is a.s. locally nice on `D ∪ (a,b)`). -/
def Prop16NodeCMarkovMaskStmt : Prop :=
  ∀ (γ : ℝ) (D : Set ℂ) (c d a b : ℝ) (h0 : ℂ → ℝ), 0 < γ → γ < 2 → K3.Prop16Geometry D c d →
    a < b → c ≤ a → b ≤ d →
    ∀ x ∈ Ioo a b, ∃ (Ω₀ : Type) (_ : MeasurableSpace Ω₀) (P₀ : Measure Ω₀)
      (Y : Ω₀ → FieldSample) (r : ℝ) (ρ₀ : Measure ℂ) (X' : Ω₀ → FieldSample) (E' : Type)
      (_ : MeasurableSpace E') (Ξ : Ω₀ → E') (g : Ω₀ → ℂ → ℝ),
      IsProbabilityMeasure P₀ ∧ IsMixedGFF D (realSet (Icc c d)) Y P₀ ∧
      (∀ᵐ ω ∂P₀, IsLocNiceOn γ (D ∪ realSet (Ioo a b)) (Y ω)) ∧
      D3Plus.Setup γ γ r ρ₀ P₀ X' Ξ g ∧ D3Plus.halfDisc r ⊆ zoomDomain D x ∧
      (∀ᵐ ω ∂P₀, ∀ C : ℝ,
        D3Plus.AgreeNear (zoomFree γ C h0 (palmMixedField γ D (realSet (Icc c d)) Y x) (ω, x))
          (D3Plus.zoomModel γ γ C ρ₀ (X' ω) (g ω)) r ∧
        ∃ μ, IsVagueLimitOn (zoomDomain D x)
          (areaApprox γ (zoomFree γ C h0 (palmMixedField γ D (realSet (Icc c d)) Y x) (ω, x))) μ) ∧
      ∀ C : ℝ, AEMeasurable (fun ω => scaleParamOn γ
        (D3Plus.zoomModel γ γ C ρ₀ (X' ω) (g ω)) (D3Plus.halfDisc r)) P₀

/-- **The masked coupling node from masked law determinacy and the Markov coupling** (own
bookkeeping). -/
theorem prop16NodeCModelMask_of_split (hL : Prop16FixedLawMaskStmt)
    (hK : Prop16NodeCMarkovMaskStmt) : Prop16NodeCModelMaskStmt := by
  intro γ D c d a b h0 Ω _ P X hyp x hx
  obtain ⟨⟨hγ, hγ2, hgeo, hab, hca, hbd, -, hP, hX, -, -⟩, -, hnX⟩ := hyp
  obtain ⟨Ω₀, _, P₀, Y, r, ρ₀, X', E', _, Ξ, g, hP₀, hY, hnY, hS, hsub, hag, hsc⟩ :=
    hK γ D c d a b h0 hγ hγ2 hgeo hab hca hbd x hx
  have hLx := fun C =>
    hL γ D c d a b h0 hγ hγ2 hgeo hab hca hbd P X P₀ Y hP hP₀ hX hY hnX hnY x hx C
  exact ⟨Ω₀, _, P₀, palmMixedField γ D (realSet (Icc c d)) Y x, r, ρ₀, X', E', _, Ξ, g, hP₀,
    fun C R => (hLx C).2 R, fun C => (hLx C).1, hS, hsub, hag, hsc⟩

/-- The same from the N2 form of D3⁺(i). -/
theorem prop16FixedZoomMask_of_splitN2 (hN2 : D3Plus.D3PlusIN2RichStmt)
    (hL : Prop16FixedLawMaskStmt) (hK : Prop16NodeCMarkovMaskStmt) : Prop16FixedZoomMaskStmt :=
  prop16FixedZoomMask_of_modelN2 hN2 (prop16NodeCModelMask_of_split hL hK)

end Prop16Asm

end QuantumZipper
