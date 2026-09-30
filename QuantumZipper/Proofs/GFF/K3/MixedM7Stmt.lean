import QuantumZipper.Proofs.GFF.K3.MixedM5Stmt
import QuantumZipper.Proofs.GFF.K3.HalfDiscMarkov
import Mathlib.Analysis.InnerProductSpace.Harmonic.Basic

/-!
# K3-mixed node M7: σ-algebra comparison and the corrected (half-disc) statement

**Status: approved as the M7 statement by decision D22 (`DECISIONS.md`), with one change to the
worker's proposal: `g ω ∘ foldH` is required to be harmonic on a neighbourhood of the *closed*
disc `closedBall t r'` (the proposal had the open disc `ball t r'`), so that `g ω` is continuous
on the support of every measure in the identity.** The fixed M7 statement
`MixedFreeCouplingStmt` (in `MixedM5Stmt.lean`) asks for a correction term `g` that is only
continuous on `K` and measurable for `σ(Ξ) ⊔ freeIncrSigma X` (the whole free field). The
consumer of M7 is the zoom lemma D3⁺ (`blueprint/E_BRANCH_BLUEPRINT.md` §3, correcting
`SECTION5_BLUEPRINT.md` D3), which needs `g` **harmonic (Neumann on `ℝ`)** on a half-disc and
measurable for `σ(Ξ) ⊔ outsideSigma X t r` (the free field *outside* the half-disc): with the
whole of `σ(X)` allowed, `g` may depend on the germ of `X` at the zoom point, and D3⁺'s
blueprint records that the conclusion is then false. So the fixed M7, although (we believe)
true, does not feed D3⁺.

This file records:

* `outsideSigma_le_freeIncrSigma`: the outside σ-algebra of L2 is contained in
  `freeIncrSigma X`, so the half-disc statement's measurability implies the fixed one's.
* `MixedFreeCouplingHalfDiscStmt`: the replacement (approved, D22) (per half-disc `ball t r ∩ H ⊆ D`
  centred on the free arc), in exactly the shape D3⁺ consumes.

Suggested proof route for the replacement (domain Markov property; Sheffield, *Gaussian free
fields for mathematicians*, PTRF 139 (2007), Thm. 2.17, for the Dirichlet case; the free-field
half-disc version is `freeGFF_halfDisc_markov`, node L2): let `Y₀` be a mixed GFF independent of
`X` and, on local measures, `Y μ = Y₀ (bal t r μ) + (X μ − X (bal t r μ))` (globally `Y` is defined
through the orthogonal decomposition of the mixed Hilbert space, see `MixedM7Nodes.lean`). The mixed Markov property
(`Cov_D(μ,ν) = Cov_D(bal μ, bal ν) + kernelCov halfDiscGreen μ ν`, the local part being the
same half-disc field as for the free field) makes `Y` a mixed GFF; on measures carried by
`closedBall t r'`, `Y μ − (X μ − μ(ℂ) X ρ₀) = ∫ g dμ` with
`g z = Y₀(P_z) − (X(P_z) − X ρ₀)` (continuous harmonic versions), which is measurable for
`σ(Y₀) ⊔ outsideSigma X t r` because `P_z` and `ρ₀` give no mass to `ball t r`; `Ξ := Y₀`.
-/

noncomputable section

open MeasureTheory Set Metric ProbabilityTheory

namespace QuantumZipper.K3

/-- The σ-algebra of the free field outside `ball t r` (node L2) is contained in the σ-algebra
of all balanced increments of the free field. -/
theorem outsideSigma_le_freeIncrSigma {Ω : Type*} [MeasurableSpace Ω] (X : Ω → FieldSample)
    (t r : ℝ) : outsideSigma X t r ≤ freeIncrSigma X := by
  refine iSup_le fun p => ?_
  let q : {p : Measure ℂ × Measure ℂ //
      IsAdmissibleH p.1 ∧ IsAdmissibleH p.2 ∧ p.1 Set.univ = p.2 Set.univ} :=
    ⟨p.1, p.2.1, p.2.2.1, p.2.2.2.1⟩
  have hm : Measurable[freeIncrSigma X] fun ω => X ω p.1.1 - X ω p.1.2 :=
    (measurable_pi_apply q).comp (comap_measurable (m := MeasurableSpace.pi)
      fun ω (p' : {p : Measure ℂ × Measure ℂ //
        IsAdmissibleH p.1 ∧ IsAdmissibleH p.2 ∧ p.1 Set.univ = p.2 Set.univ}) =>
          X ω p'.1.1 - X ω p'.1.2)
  exact measurable_iff_comap_le.1 hm

/-- **M7 (half-disc form, D3⁺-compatible; approved in D22).** For a half-disc
`ball t r ∩ H ⊆ D` centred at `t ∈ (c, d)` and `0 < r' < r`, and an admissible reference
probability measure `ρ₀` giving no mass to `ball t r`: a mixed GFF `Y` and a free GFF `X` on one
space, a random element `Ξ` independent of `X`, and a correction `g` whose even extension
`g ∘ foldH` is harmonic on a neighbourhood of `closedBall t r'` (Neumann on `ℝ`), measurable for
`σ(Ξ) ⊔ outsideSigma X t r`, with `Y = X − X(ρ₀)·mass + g` on measures carried by
`closedBall t r'`. -/
def MixedFreeCouplingHalfDiscStmt (D : Set ℂ) (c d t r r' : ℝ) (ρ₀ : Measure ℂ) : Prop :=
  Prop16Geometry D c d → t ∈ Set.Ioo c d → 0 < r' → r' < r → ball (t : ℂ) r ∩ H ⊆ D →
    IsAdmissibleH ρ₀ → ρ₀ Set.univ = 1 → ρ₀ (ball (t : ℂ) r) = 0 →
    ∃ (Ω₀ : Type) (_ : MeasurableSpace Ω₀) (P₀ : Measure Ω₀) (Y X : Ω₀ → FieldSample)
      (g : Ω₀ → ℂ → ℝ) (E' : Type) (_ : MeasurableSpace E') (Ξ : Ω₀ → E'),
      IsProbabilityMeasure P₀ ∧ IsMixedGFF D (realSet (Set.Icc c d)) Y P₀ ∧
      IsFreeGFFModConstH X P₀ ∧ Measurable Ξ ∧
      Indep (MeasurableSpace.comap Ξ inferInstance) (freeIncrSigma X) P₀ ∧
      (∀ ω, InnerProductSpace.HarmonicOnNhd (fun z => g ω (foldH z)) (closedBall (t : ℂ) r')) ∧
      (∀ z, Measurable[MeasurableSpace.comap Ξ inferInstance ⊔ outsideSigma X t r]
        fun ω => g ω z) ∧
      ∀ μ : Measure ℂ, IsAdmissibleH μ → μ (closedBall (t : ℂ) r')ᶜ = 0 →
        ∀ᵐ ω ∂P₀, Y ω μ = X ω μ - (μ Set.univ).toReal * X ω ρ₀ + ∫ z, g ω z ∂μ

end QuantumZipper.K3
