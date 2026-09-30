import QuantumZipper.Proofs.Thm18.G3CvHarm
import QuantumZipper.Proofs.GFF.K3.MixedM7AsmMain

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# G3-CURVE, piece 1 (assembly): local conformal coupling of the pulled-back free field

`exists_pullCouplingHarm`: for a local conformal map `Φ` at the real point `b` (`PullData`), on
one probability space there are free fields `W, X'`, variables `Ξ` independent of the increments of
`X'`, and a random function `g`, continuous on `Hbar`, with `g z` measurable for
`σ(Ξ) ⊔ outsideSigma X' b ρ`, such that for all admissible `μ, μ'` of equal mass carried by
`closedBall b r₁`, a.s.

  `W(Φ_*μ) − W(Φ_*μ') = X'(μ) − X'(μ') + ∫ g dμ − ∫ g dμ'`,

i.e. near `b` the pull-back `W ∘ Φ` of a free field is, modulo additive constants, a free field
plus a continuous function determined by `Ξ` and the outside of `X'`: the data of the D3⁺ model
(`D3Plus.Setup`) except the harmonicity of `g`. This is the conformal form of the domain Markov
coupling (Sheffield, *Gaussian free fields for mathematicians* (2007), §2.2 and Thm. 2.17),
used implicitly in Sheffield arXiv:1012.4797 pp. 70–71. Own adaptation of the M7 assembly
(MixedM7AsmMain.lean): local part `realP_local`, harmonic part of `X'` from
`markov_decomposition`, harmonic part of `W ∘ Φ` as the Kolmogorov version of the `Ξ`-process
(`momentBound_pullIncr`, `pull_stochFubini`).
-/

noncomputable section

open MeasureTheory ProbabilityTheory Metric Filter Set
open scoped ComplexConjugate ENNReal Topology RealInnerProductSpace

namespace QuantumZipper
namespace G3Cv

open K3 GFFExist LQGDimension.ExistAsm

variable {Φ : ℂ → ℂ} {b r₀ ρ r₁ m M : ℝ}

/-- The vector of the harmonic increment `W(Φ_*P_{retr z}) − W(Φ_*P_b)`. -/
def harmVec (Φ : ℂ → ℂ) (b ρ r₁ : ℝ) (z : ℂ) : HkE :=
  fvM ((halfDiscPoisson b ρ (retr b r₁ z)).map Φ) - fvM ((halfDiscPoisson b ρ (b : ℂ)).map Φ)

theorem harmVec_orth (hD : PullData Φ b r₀ ρ r₁ m M) (hr₁0 : 0 < r₁) (z : ℂ)
    (ν : LocIdx b r₁) : ⟪harmVec Φ b ρ r₁ z, pullLocVec Φ b ρ ν.1⟫ = 0 := by
  have hz := norm_retr_sub_le (t := b) hr₁0 z
  have hb : ‖(b : ℂ) - b‖ ≤ r₁ := by rw [norm_self_sub_ofReal]; exact hr₁0.le
  have := isProbabilityMeasure_halfDiscPoisson hD.hρ (mem_ball_of_le_k3 hD.hr₁ hz)
  have := isProbabilityMeasure_halfDiscPoisson hD.hρ (mem_ball_of_le_k3 hD.hr₁ hb)
  exact inner_fvM_map_sub_pullLocVec_eq_zero hD (isAdmissibleH_halfDiscPoisson hD.hρ hD.hr₁ hz)
    (isAdmissibleH_halfDiscPoisson hD.hρ hD.hr₁ hb) (by rw [measure_univ, measure_univ])
    (halfDiscPoisson_closedBall_compl hD.hρ _) (halfDiscPoisson_closedBall_compl hD.hρ _)
    (halfDiscPoisson_ball hD.hρ _) (halfDiscPoisson_ball hD.hρ _) ν

end G3Cv
end QuantumZipper
