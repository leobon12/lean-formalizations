import QuantumZipper.Proofs.Zipper.BaseFin2SleFL

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# FL-THM: the deterministic crosscut-sum node of Field–Lawler Proposition 3.4

**Source.** L. S. Field, G. F. Lawler, *Escape probability and transience for SLE*,
Electron. J. Probab. 20 (2015), no. 10 (arXiv:1407.3314, `literature/1407.3314.pdf`),
proof of **Proposition 3.4** (pp. 8–9) combined with the lower bound in the proof of
**Proposition 3.1** (chordal case, p. 7) and **Lemma 3.3** (p. 8, proved in §4, p. 10).

Setting (their notation, scaled by `R`): `T` is the first time the curve reaches the circle
`{|z| = R}`, `D = H_T = ℍ \ K_T`, `Z_T = g_T − W_T : D → ℍ` (`fwdMap W T`, inverse
`fwdMapInv W T`), and `D ∩ {|z| = ε} = ⋃ⱼ ηⱼ` are crosscuts of `D`. FL show
`Σⱼ ℰ_D(ηⱼ, γ̃) ≤ 2 ℰ_ℍ(C_ε, C_R) ≤ c ε/R` (Lemma 3.3 and (2.4)), and in the proof of Prop 3.1
`ℰ_ℍ(Z_T ηⱼ, ℝ₋) ≥ c (diam Z_T ηⱼ / dist(0, Z_T ηⱼ) ∧ 1)` (conformal invariance of `ℰ`; the
crosscut `Z_T ηⱼ` has both endpoints on one side of `0`). Hence the image
`Z_T(D ∩ B(0, ε))`, which lies under the crosscuts `Z_T ηⱼ`, is covered by disks `B(cⱼ, rⱼ)`
with real centres (an endpoint of `Z_T ηⱼ`), `rⱼ = 2 diam Z_T ηⱼ`, `2 rⱼ ≤ |cⱼ|` and
`Σⱼ rⱼ/|cⱼ| ≤ C ε/R` once `ε/R` is small.

`FLCoverStmt` records exactly this covering (deterministic; the hypotheses are the facts that hold
almost surely at the first hitting time of `{|z| ≥ R}` by a chordal `SLE_κ`, `κ ≤ 4`: simple
trace, hull = trace image, trace inside `B(0, R)` before `T`, tip on the circle and the tip is
the boundary value of `Z_T⁻¹` at `0`). It is the only non-probabilistic input of
Field–Lawler Theorem 1.1; the probabilistic part (strong Markov at `T` and Prop 3.1 summed over
the disks, with `Σ aⱼ^α ≤ (Σ aⱼ)^α`) is `FieldLawlerMarkov.lean`.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Metric
open scoped Topology NNReal ENNReal

namespace QuantumZipper
namespace FieldLawler

/-- **Field–Lawler, proof of Prop. 3.4 with the lower bound of Prop. 3.1 (deterministic
crosscut-sum covering).** At the first time `t` a Loewner chain with a simple trace reaches
`{|z| = R}`, the image under `Z_t` of the part of `H_t` within distance `ε ≤ δ₀ R` of the root is
covered by disks `B(cᵢ, rᵢ)` with real centres, `2 rᵢ ≤ |cᵢ|` and `Σ rᵢ/|cᵢ| ≤ C ε/R`. -/
def FLCoverStmt : Prop :=
  ∃ C δ₀ : ℝ, 0 ≤ C ∧ 0 < δ₀ ∧ ∀ (W : ℝ → ℝ), Continuous W → W 0 = 0 →
    ∀ t R ε : ℝ, 0 ≤ t → 0 < R → 0 < ε → ε ≤ δ₀ * R →
    trace W 0 = 0 → ContinuousOn (trace W) (Icc 0 t) → InjOn (trace W) (Icc 0 t) →
    (∀ s ∈ Ioc 0 t, trace W s ∈ H) →
    fwdHull W t = trace W '' Ioc 0 t →
    (∀ s ∈ Ico 0 t, ‖trace W s‖ < R) → ‖trace W t‖ = R →
    Tendsto (fun y : ℝ => fwdMapInv W t (y * Complex.I)) (𝓝[>] 0) (𝓝 (trace W t)) →
    ∃ c r : ℕ → ℝ, (∀ i, 0 < r i ∧ 2 * r i ≤ |c i|) ∧ Summable (fun i => r i / |c i|) ∧
      ∑' i, r i / |c i| ≤ C * (ε / R) ∧
      ∀ p ∈ H, ‖fwdMapInv W t p‖ < ε → ∃ i, ‖p - (c i : ℂ)‖ < r i

end FieldLawler
end QuantumZipper
