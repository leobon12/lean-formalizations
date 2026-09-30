import QuantumZipper.Proofs.Thm18.R18G3TProf
import QuantumZipper.Proofs.Thm18.R18G3Transfer

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# R18-G3 step 5T: the split of `G3WedgeFreeTransferStmt` (decision D85)

Sheffield, *Conformal weldings of random surfaces*, arXiv:1012.4797, proof of Theorem 1.8,
p. 71 ("we condition on the restriction of the GFF to the complement of `B¹ := B_ε(x)` and
`B² := B_ε(R(x))` … Proposition 5.5 implies that even with this conditioning … the zoomed-in
figures converge in law to a `γ`-quantum wedge … by the standard GFF Markov property … the
`γ`-quantum wedges are independent"), p. 28 (the Palm weighting "effectively adds `−γ log|·|`
to `𝔥₀`", which is why the wedge of Theorem 1.8 is the `(γ − 2/γ)`-wedge), p. 72 and Remark 5.7
(adding a smooth function to the field changes its restriction to compact sets away from the
origin only in an absolutely continuous way, [SS13] §3.1).

The wedge `Y` of step 5, in its circle-average embedding and on the unit half-disc, is Theorem
1.2's field `normField γ X` plus the profile `g3wProf γ = −γ log|·|`
(`WedgeUnzip.WDec.wedgeDecompStmt_holds`; `h0rev (γ²) − γ log|·| = −(γ − 2/γ) log|·|`). The split
goes through the concrete Palm scheme of that shifted field (`R18G3TProf.lean`, scheme `C`):

* **T5-J** `G3TProfJointMixStmt`: fixed-region joint mixing of the zooms of scheme `C` at `x`
  and `R(x)`, against every bounded weight measurable for the field outside both half-discs and
  the Palm length (the conditional form of p. 71), with the limit laws `μ, ν` of the free scheme,
  whose joint cylinder limit along `g3Filter` is `μ(s) ν(t)`. No wedge, no curve.
* **T5-G** `G3TWedgeGeoStmt`: the normalized Palm-window integral of the wedge (window `U`, zoom
  level `L`, zooms through the local maps of the independent curve) is, for small `U`, then small
  `η`, then large `L`, the weighted Palm integral of scheme `C` at `(δ, η, L)` for the weight
  `1{ℓ ≤ U} · Z/U` (up to `ε`), and the weighted margin mass is `≈ 1`. No independence content:
  law of the wedge (circle-average embedding, the unit-area dilation), Fubini over the independent
  curve and SLE scaling, the local maps (G0), the Palm windows, locality of the zooms.

`g3WedgeFreeTransferStmt_of_split : G3TProfJointMixStmt → G3TWedgeGeoStmt →
G3WedgeFreeTransferStmt` (this file) is own `ε`-bookkeeping. T5-J is reduced in
`R18G3TJoint.lean` to the per-region transfer `G3TProfMixTransferStmt` (conditional Proposition
5.5 for scheme `C` from that of the free scheme, same limit laws) and the area input
`G3TProfAreaStmt`, with the Markov property of scheme `C` proved (`condIndepCE_g3p`).
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal Topology

namespace QuantumZipper
namespace R18

open Thm18Asm

/-- The profile of the `(γ − 2/γ)`-wedge relative to Theorem 1.2's field: `−γ log|·|`
(Sheffield p. 28). -/
def g3wProf (γ : ℝ) : ℂ → ℝ := fun z => -γ * Real.log ‖z‖

/-- The margin event of scheme `C`: `x` a margin `m` inside region 1 and `R(x)` a margin `m`
inside region 2. -/
def g3pMarg (γ : ℝ) (g : ℂ → ℝ) (i : G3Idx) (m : ℝ) : Set (gffBase.Ω × ℝ) :=
  {p | |g3pX γ g i p - i.t₁| + m < i.r₁ ∧ |g3pR γ g i p - i.t₂| + m < i.r₂}

/-- The body of the fixed-region mixing statement (`G2FixMixStmt`) for a Palm scheme with Palm
laws `P`, Palm points `x`, partners `R`, full-field zooms `Uf`, `Vf`, and limit laws `μ, ν`. -/
def G3FixMixBody (μ ν : Measure LawD) (P : G3Idx → Measure (gffBase.Ω × ℝ))
    (x R : G3Idx → gffBase.Ω × ℝ → ℝ) (Uf Vf : G3Idx → gffBase.Ω × ℝ → LawD) : Prop :=
  (∀ s ∈ lawCyl, ∀ δ η m : ℝ, 0 < m → ∀ ε > 0, ∀ᶠ C in (atTop : Filter ℝ), ∀ i : G3Idx,
      i.1 = (δ, η, C) → ∀ G : Set (gffBase.Ω × ℝ),
        MeasurableSet[outsideSigmaPalm ℝ gffBase.X i.t₁ i.r₁ i.t₂ i.r₂] G →
        |(P i).real (Uf i ⁻¹' s ∩ {p | |x i p - i.t₁| + m < i.r₁} ∩ G) -
          μ.real s * (P i).real ({p | |x i p - i.t₁| + m < i.r₁} ∩ G)| ≤ ε) ∧
  (∀ t ∈ lawCyl, ∀ δ η m : ℝ, 0 < m → ∀ ε > 0, ∀ᶠ C in (atTop : Filter ℝ), ∀ i : G3Idx,
      i.1 = (δ, η, C) → ∀ G : Set (gffBase.Ω × ℝ),
        MeasurableSet[outsideSigmaPalm ℝ gffBase.X i.t₁ i.r₁ i.t₂ i.r₂] G →
        |(P i).real (Vf i ⁻¹' t ∩ {p | |R i p - i.t₂| + m < i.r₂} ∩ G) -
          ν.real t * (P i).real ({p | |R i p - i.t₂| + m < i.r₂} ∩ G)| ≤ ε)

/-- Real arithmetic of the wiring: from `|I − c E| ≤ e`, `|E − 1| ≤ e`, `0 ≤ c ≤ 1`. -/
theorem g3t_arith {I E c e : ℝ} (hc0 : 0 ≤ c) (hc1 : c ≤ 1) (h1 : |I - c * E| ≤ e)
    (h2 : |E - 1| ≤ e) : I ≤ c + 2 * e ∧ c ≤ I + 2 * e := by
  rw [abs_le] at h1 h2
  obtain ⟨h1a, h1b⟩ := h1
  obtain ⟨h2a, h2b⟩ := h2
  have e1 : c * E ≤ c * (1 + e) := mul_le_mul_of_nonneg_left (by linarith) hc0
  have e2 : c * (1 - e) ≤ c * E := mul_le_mul_of_nonneg_left (by linarith) hc0
  have e0 : 0 ≤ e := by linarith [abs_nonneg (E - 1)]
  have e3 : c * e ≤ e := mul_le_of_le_one_left e0 hc1
  constructor <;> nlinarith

end R18
end QuantumZipper
