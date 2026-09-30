import QuantumZipper.Proofs.Thm18.G3RMain
import QuantumZipper.Proofs.Thm18.R18G3TCM4
import QuantumZipper.Proofs.LQG.Positivity

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# R18-G3 (R-c): the region-1 tail node `G3TRegion1TailStmt`

Sheffield, arXiv:1012.4797, p. 72 and Remark 5.7 (a Cameron–Martin shift of the field inside a
region has an equivalent law and multiplies the boundary measure there by `e^{γ f/2}`);
Berestycki–Powell, arXiv:2004.04720, Lemma 3.12 (Cameron–Martin, in the repository form
`lintegral_incr_shift_eq`); Duplantier–Sheffield (5.1) for the boundary measure of a shifted
field (`LocalRule.isVagueLimitR_add_ofFun`).

Proof. Let `A = {ν₁[−δ, 0] ≥ v}`, `c = P(A | outside)` and `O⁺ = {c ≤ 0}` (an outside event), so
`P(A ∩ O⁺) = 0`. For a smooth bump `ψ` supported in the region-1 half-disc, equal to `1` near
the real interval `J` around `t₁`, and every `M`, the shift by `Mψ` does not change the outside
field, and by Cameron–Martin `P(O⁺ ∩ {ν₁^{+Mψ}[−δ, 0] ≥ v}) = 0`. But
`ν₁^{+Mψ}[−δ, 0] ≥ e^{γM/2} ν₁(J)` and `ν₁(J) > 0` a.s. (M4-P2), so `P(O⁺) = 0`.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Metric
open scoped Topology ENNReal NNReal ComplexConjugate

namespace QuantumZipper
namespace R18

open Thm18Asm

local notation "Ω₀" => gffBase.Ω
local notation "X₀" => gffBase.X

/-! ## The bump -/

/-- Inner radius of the bump. -/
def tρ (i : G3Idx) : ℝ := (i.δ - i.η) / 4
/-- Outer radius of the bump. -/
def ta (i : G3Idx) : ℝ := i.r₁ / 2

theorem tρ_pos (i : G3Idx) : 0 < tρ i := by have := i.hηδ; unfold tρ; linarith
theorem tρ_lt_ta (i : G3Idx) : tρ i < ta i := by
  have := i.hη; unfold tρ ta G3Idx.r₁; linarith

/-- The region-1 bump: `1` on `closedBall t₁ ρ`, `0` off `ball t₁ a`. -/
def tψ (i : G3Idx) (z : ℂ) : ℝ :=
  Real.smoothTransition ((ta i ^ 2 - ‖z - i.t₁‖ ^ 2) / (ta i ^ 2 - tρ i ^ 2))

theorem tden_pos (i : G3Idx) : 0 < ta i ^ 2 - tρ i ^ 2 := by
  have h1 := tρ_pos i; have h2 := tρ_lt_ta i; nlinarith

theorem contDiff_tψ (i : G3Idx) : ContDiff ℝ 2 (tψ i) := by
  have h : ContDiff ℝ 2 fun z : ℂ => ‖z - i.t₁‖ ^ 2 :=
    (contDiff_norm_sq ℝ).comp (contDiff_id.sub contDiff_const)
  exact Real.smoothTransition.contDiff.comp ((contDiff_const.sub h).div_const _)

theorem tψ_eq_zero (i : G3Idx) {z : ℂ} (hz : ta i ≤ ‖z - i.t₁‖) : tψ i z = 0 := by
  unfold tψ
  refine Real.smoothTransition.zero_of_nonpos (div_nonpos_of_nonpos_of_nonneg ?_ (tden_pos i).le)
  have := (tρ_pos i).trans (tρ_lt_ta i)
  nlinarith

theorem tψ_eq_one (i : G3Idx) {z : ℂ} (hz : ‖z - i.t₁‖ ≤ tρ i) : tψ i z = 1 := by
  unfold tψ
  refine Real.smoothTransition.one_of_one_le ?_
  rw [le_div_iff₀ (tden_pos i), one_mul]
  have := tρ_pos i
  nlinarith [norm_nonneg (z - i.t₁)]

theorem hasCompactSupport_tψ (i : G3Idx) : HasCompactSupport (tψ i) :=
  HasCompactSupport.intro (isCompact_closedBall (i.t₁ : ℂ) (ta i)) fun z hz => by
    rw [mem_closedBall, dist_eq_norm, not_le] at hz
    exact tψ_eq_zero i hz.le

theorem tψ_conj (i : G3Idx) (z : ℂ) : tψ i (conj z) = tψ i z := by
  unfold tψ
  have : conj z - (i.t₁ : ℂ) = conj (z - i.t₁) := by simp [map_sub, Complex.conj_ofReal]
  rw [this, Complex.norm_conj]

/-- Outside measures do not see the bump. -/
theorem integral_tψ_eq_zero (i : G3Idx) {μ : Measure ℂ}
    (hμ : μ (ball (i.t₁ : ℂ) i.r₁ ∪ ball (i.t₂ : ℂ) i.r₂) = 0) (M : ℝ) :
    ∫ z, (M • tψ i) z ∂μ = 0 := by
  refine integral_eq_zero_of_ae ?_
  have h1 : μ (ball (i.t₁ : ℂ) i.r₁) = 0 := measure_mono_null subset_union_left hμ
  have hae : ∀ᵐ z ∂μ, z ∉ ball (i.t₁ : ℂ) i.r₁ := measure_eq_zero_iff_ae_notMem.1 h1
  filter_upwards [hae] with z hz
  rw [mem_ball, dist_eq_norm, not_lt] at hz
  have ha : ta i ≤ i.r₁ := by have := i.r₁_pos; unfold ta; linarith
  simp [tψ_eq_zero i (ha.trans hz)]

end R18
end QuantumZipper
