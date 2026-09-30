import QuantumZipper.Proofs.Section5.Prop16LitCore
import QuantumZipper.Proofs.Section5.Prop16LitSlutsky

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# Proposition 1.6, literal form (decision D95): reduction to conformal covariance

`Prop16Lit.theorem1_6_literal_of_nodes`: `theorem1_6_literal` from the proved
`theorem1_6_proved` and four inputs:

* `Prop16LitCovStmt` — conformal covariance of the Liouville area measure (Duplantier–Sheffield,
  *Liouville quantum gravity and KPZ*, arXiv:0808.1560, Prop. 2.1) for the zoomed field at
  quantum-typical points: `ψ_* μ_{h∘ψ + Q log|ψ'|} = μ_h|_{ψ(U)}` for the chart `ψ = ψ_x`, and the
  rescaling rule (the case of a dilation) for the field read through the chart;
* `Prop16LitMeasStmt` — a.e.-measurability of the literal canonical pairings under the weighted
  law (without it the Bochner integrals of `AreaConvergesInLawOn` are junk);
* `Prop16Asm.Prop16ScaleStmt` — the straight canonical scale tends to `0` in probability
  (D3⁺(iii) under the weighted law; an existing node of the Prop. 1.6 blueprint);
* `Prop16LitFinStmt` — the straight local area of `B(0,t) ∩ ℍ` is finite for some `t > 0`,
  uniformly in the level `C`.

The argument (Sheffield, arXiv:1012.4797, p. 21, (1.8): the dilation `ψ_x'(0)` is absorbed by
the normalization): `LitChart.pointwise_close` / `Prop16Lit.core_pointwise` compare the canonical
pairings sample by sample at small scale; `LitSlutsky.tendsto_close_of_pointwise` turns this
into closeness in probability; `LitSlutsky.tight_of_tendsto` gives tightness from
`theorem1_6_proved`; `LitSlutsky.tendsto_integral_sub` (Slutsky) transfers the limit.
Own assembly.
-/

noncomputable section

open Filter Set Metric MeasureTheory ProbabilityTheory
open scoped Topology ENNReal

namespace QuantumZipper

namespace Prop16Lit

open LitChart Prop16Asm Prop16Area.G

/-- The family hypotheses of `theorem1_6_literal`. -/
def LitFamily (D : Set ℂ) (a b : ℝ) (ψ : ℝ → ℂ → ℂ) (r₀ : ℝ → ℝ) : Prop :=
  Measurable (fun q : ℝ × ℂ => ψ q.1 q.2) ∧ Measurable r₀ ∧
    ∀ x ∈ Set.Ioo a b, IsLitChart (zoomDomain D x) (r₀ x) (ψ x)

/-- **Node (measurability of the literal canonical pairings).** -/
def Prop16LitMeasStmt : Prop :=
  ∀ (γ : ℝ) (D : Set ℂ) (c d a b : ℝ) (h0 : ℂ → ℝ) {Ω : Type} [MeasurableSpace Ω]
    (P : Measure Ω) (X : Ω → FieldSample), Prop16Data γ D c d a b h0 P X →
    ∀ (ψ : ℝ → ℂ → ℂ) (r₀ : ℝ → ℝ), LitFamily D a b ψ r₀ →
    ∀ (C : ℝ) (f : ℂ → ℝ), Continuous f → HasCompactSupport f →
      AEMeasurable (fun p => canPair γ (zoomFieldLit γ C (ofFun h0 + X p.1) p.2 (ψ p.2))
        (ball 0 (r₀ p.2) ∩ H) f) (prop16Q γ h0 a b P X)

/-- **Node (finite straight local area near the zoom point, uniformly in the level).** -/
def Prop16LitFinStmt : Prop :=
  ∀ (γ : ℝ) (D : Set ℂ) (c d a b : ℝ) (h0 : ℂ → ℝ) {Ω : Type} [MeasurableSpace Ω]
    (P : Measure Ω) (X : Ω → FieldSample), Prop16Data γ D c d a b h0 P X →
    ∀ᵐ p ∂(prop16Q γ h0 a b P X), ∃ t > 0, ∀ C : ℝ,
      qAreaMeasureOn γ (zoomField γ C (ofFun h0 + X p.1) p.2) (zoomDomain D p.2)
        (ball 0 t ∩ H) < ⊤

/-- Wedge area pairings are a.e.-measurable. -/
theorem aemeasurable_wedge_pair {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) {Ω' : Type}
    [MeasurableSpace Ω'] {P' : Measure Ω'} {W : Ω' → FieldSample}
    (hW : IsQuantumWedge γ γ W P') {f : ℂ → ℝ} (hf : Continuous f) (hfs : HasCompactSupport f) :
    AEMeasurable (fun ω => ∫ z, f z ∂qAreaMeasure γ (W ω)) P' := by
  obtain ⟨R₀, hR₀⟩ := (isBounded_iff_subset_ball (0 : ℂ)).1 hfs.isCompact.isBounded
  obtain ⟨R, hR⟩ := exists_nat_ge R₀
  have hfR : ∀ z, f z ≠ 0 → z ∈ ball (0 : ℂ) R := fun z hz =>
    ball_subset_ball hR (hR₀ (subset_tsupport f hz))
  have hrec : AEMeasurable (fun ω => Prop16Area.recon (W ω)) P' :=
    Factorization.measurable_reconstruct.comp_aemeasurable (wedge_coords_aemeasurable hγ hγ2 hW)
  refine ((Prop16Area.measurable_locArea γ R hf.measurable).comp_aemeasurable hrec).congr ?_
  filter_upwards [wedge_ae_exists_vague hγ hγ2 hW] with ω hω
  have hω' : ∃ μ, IsVagueLimitOn H (areaApprox γ (Prop16Area.recon (W ω))) μ := by
    rwa [Prop16Area.areaApprox_recon]
  rw [Function.comp_apply, ← Prop16Area.integral_qAreaMeasure_eq_locArea hω' hf hfs hfR,
    Prop16Area.qAreaMeasure_recon]

end Prop16Lit

end QuantumZipper
