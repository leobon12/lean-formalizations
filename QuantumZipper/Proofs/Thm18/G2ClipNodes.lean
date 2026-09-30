import QuantumZipper.Proofs.Thm18.G3Concrete
import QuantumZipper.Proofs.Thm18.G2ClipFrozen
import Mathlib.Probability.Distributions.Gaussian.Real

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# G2 clipped-shift node: the Gaussian bump decomposition (named literature node)

Sheffield (arXiv:1012.4797, proof of Prop. 5.5, p. 66): "by the definition of the GFF we can write
`h = α₁ φ₁ + α₂ φ₂ + h₀` where `α₁` and `α₂` are centered Gaussian random variables and `h₀` is
the projection of `h` onto the orthogonal complement of the span of `φ₁` and `φ₂` ... `α₁`, `α₂`
and `h₀` are independent of each other." For one bump this is the orthogonal decomposition of
the GFF along a Cameron–Martin direction (Berestycki–Powell, *Gaussian free field and Liouville
quantum gravity*, arXiv:2004.04720, §3.3.3, Lemma 3.14 and Corollary 3.15, p. 83–84; Bogachev,
*Gaussian Measures*, Thm. 2.4.5).

`G2BumpDecompStmt` states it for the free-boundary field modulo constants `gffBase.X`, read on
admissible measures `μ` through the balanced combination `X μ − μ(ℂ) X refS` (normalization at
the unit folded semicircle `refS`, as in `normField`; only balanced combinations are constrained
by `IsFreeGFFModConstH`): for an even (`φ(z̄) = φ(z)`, so Neumann on `ℝ`) smooth bump `φ ≢ 0`
with compact support in the unit disc (so `∫ φ d refS = 0`), there is a Gaussian coefficient `α`
of positive variance such that `μ ↦ X μ − μ(ℂ) X refS − α ∫ φ dμ` is independent of `α`.

Why it is true (the proof to formalize): with `μ± = (Δφ)^∓ dz` on `ℍ` (equal masses, since
`∫_ℍ Δφ = −∫_ℝ ∂_y φ = 0` for even `φ`), `β = X μ₊ − X μ₋` is a coordinate of the balanced-pair
Gaussian process of `IsFreeGFFModConstH`, jointly Gaussian with every `X μ − X refS`, and
`Cov(X μ − μ(ℂ) X refS, β) = kernelCov2 neumannH (μ, μ(ℂ) refS) (μ₊, μ₋) = 2π ∫ φ dμ`
(Green's identity for the Neumann kernel); `α = 2π β / Var β` then works (uncorrelated jointly
Gaussian families are independent).
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Metric
open scoped Topology ENNReal NNReal

namespace QuantumZipper
namespace Thm18Asm

/-- Admissible measures (the index set of the field). -/
abbrev AdmIdx : Type := {μ : Measure ℂ // IsAdmissibleH μ}

/-- **Node (Gaussian bump decomposition of the GFF; Sheffield, arXiv:1012.4797, proof of
Prop. 5.5, p. 66; Berestycki–Powell, arXiv:2004.04720, Lemma 3.14, p. 83).** -/
def G2BumpDecompStmt : Prop :=
  ∀ φ : ℂ → ℝ, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) φ → HasCompactSupport φ →
    tsupport φ ⊆ ball (0 : ℂ) 1 → (∀ z, φ (starRingEnd ℂ z) = φ z) → (∃ z, φ z ≠ 0) →
    ∃ (α : gffBase.Ω → ℝ) (v : ℝ≥0), 0 < v ∧ Measurable α ∧
      gffBase.P.map α = gaussianReal 0 v ∧
      IndepFun α (fun ω (μ : AdmIdx) =>
        gffBase.X ω μ.1 - (μ.1 univ).toReal * gffBase.X ω refS - α ω * ∫ z, φ z ∂μ.1) gffBase.P

end Thm18Asm
end QuantumZipper
