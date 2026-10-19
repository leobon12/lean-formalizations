import GaussianLQG.Uniform.Interfaces
import LQGMetric.Papers.DDDF.RSWUnif

/-!
# The finite family of shapes, uniform in `ξ` (Route U, ledger U7)

Phase B, packet PB-U9 (ledger packet B-4). Uniform-constants ledger
`blueprint/phaseB/uniform-ledger.tex`, statement U7, §`subsec:ledger-shapes`, Finding
`fd:shapes`.

The shapes used by Route U are `𝓕 = {R_{1,3}, R_{1,1}, R_{2,1}, R_{3,1}}`. By
`lenObs_rectAB_mono` (`LQGMetric/Papers/DDDF/RSWUnif.lean`), `L(R_{x,y'}) ≤ L(R_{X,y})` for
`0 ≤ x ≤ X`, `0 ≤ y ≤ y'`, so pathwise
`L_n(R_{1,3}) ≤ L_n(R_{a,b}) ≤ L_n(R_{3,1})` for every `(a, b) ∈ 𝓕`; the lower tails of every
shape follow from the uniform Cor 17 (`IfaceCor17U`, ledger U5) and the upper tails from the
uniform Prop 18 (`IfaceProp18U`, ledger U6), with `p₀ = min`, `C = max`, `c = min` of the two
(ledger row `shapes_unif`). No general-shape RSW is needed.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

namespace GaussianLQG
namespace Uniform

open LQGMetric LQGMetric.DDDF LQGMetric.WhiteNoise

/-- the shapes of `𝓕` lie in `[1, 3]²` -/
lemma shapes_bounds {a b : ℝ}
    (hab : (a, b) ∈ ({(1, 3), (1, 1), (2, 1), (3, 1)} : Set (ℝ × ℝ))) :
    1 ≤ a ∧ a ≤ 3 ∧ 1 ≤ b ∧ b ≤ 3 := by
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff, Prod.mk.injEq] at hab
  rcases hab with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> norm_num

/-- **The finite family of shapes, uniform in `ξ ∈ (0, ξs]` and in the white noise** (ledger U7,
`shapes_unif`): for `p ≤ p₀`, lower tails (relative to `ℓ_n(p)`) and upper tails (relative to
`Λ_n(p) ℓ_n(p)`) of the crossings of `R_{1,3}`, `R_{1,1}`, `R_{2,1}`, `R_{3,1}`, with constants
chosen before the probability space and before `ξ`. Inputs: the uniform Cor 17 and Prop 18
(ledger U5, U6); the positivity of `ξs` is the standing assumption of those nodes. -/
theorem shapes_unif (ξs : ℝ) (_hξs : 0 < ξs) (h17 : IfaceCor17U ξs) (h18 : IfaceProp18U ξs) :
    ∃ p₀ : ℝ, 0 < p₀ ∧ ∀ p : ℝ, 0 < p → p ≤ p₀ → ∃ C c : ℝ, 0 < C ∧ 0 < c ∧
      ∀ {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} {W : WNSpace → Ω → ℝ}, IsWhiteNoise P W →
      ∀ ξ ∈ Ioc (0 : ℝ) ξs, ∀ (n : ℕ) (a b : ℝ),
        (a, b) ∈ ({(1, 3), (1, 1), (2, 1), (3, 1)} : Set (ℝ × ℝ)) →
        (∀ s : ℝ, 0 < s → P {ω | lenObs ξ (phiMN W P 0 n) (rectAB a b) ω ≤
            Real.exp (-s) * ellN ξ W P n (ENNReal.ofReal p)} ≤
          ENNReal.ofReal (C * Real.exp (-c * s ^ 2))) ∧
        (∀ s : ℝ, 2 < s → P {ω | Real.exp s * LambdaN ξ W P n (ENNReal.ofReal p) *
            ellN ξ W P n (ENNReal.ofReal p) ≤ lenObs ξ (phiMN W P 0 n) (rectAB a b) ω} ≤
          ENNReal.ofReal (C * Real.exp (-c * s ^ 2 / Real.log s))) := by
  obtain ⟨p₁, hp₁, h17⟩ := h17
  obtain ⟨p₂, hp₂, h18⟩ := h18
  refine ⟨min p₁ p₂, lt_min hp₁ hp₂, fun p hp hpp => ?_⟩
  obtain ⟨C₁, c₁, hC₁, hc₁, h17⟩ := h17 p hp (hpp.trans (min_le_left _ _))
  obtain ⟨C₂, c₂, hC₂, hc₂, h18⟩ := h18 p hp (hpp.trans (min_le_right _ _))
  refine ⟨max C₁ C₂, min c₁ c₂, lt_max_of_lt_left hC₁, lt_min hc₁ hc₂,
    fun {Ω} _ {P} {W} hW ξ hξ n a b hab => ⟨fun s hs => ?_, fun s hs => ?_⟩⟩
  · obtain ⟨ha1, -, hb1, hb3⟩ := shapes_bounds hab
    have hφ := (isPhiVersion_phiMN hW (Nat.zero_le n)).cont
    -- `L(R_{1,3}) ≤ L(R_{a,b})`
    have hlow : ∀ ω, lenObs ξ (phiMN W P 0 n) (rectAB 1 3) ω ≤
        lenObs ξ (phiMN W P 0 n) (rectAB a b) ω := fun ω =>
      lenObs_rectAB_mono hφ zero_le_one ha1 (by linarith) hb3 ω
    refine (measure_mono fun ω (hω : lenObs ξ (phiMN W P 0 n) (rectAB a b) ω ≤ _) =>
      (show lenObs ξ (phiMN W P 0 n) (rectAB 1 3) ω ≤ _ from (hlow ω).trans hω)).trans
      ((h17 hW ξ hξ n s hs).trans (ENNReal.ofReal_le_ofReal ?_))
    have hc : -c₁ * s ^ 2 ≤ -min c₁ c₂ * s ^ 2 :=
      mul_le_mul_of_nonneg_right (neg_le_neg (min_le_left _ _)) (sq_nonneg s)
    exact mul_le_mul (le_max_left _ _) (Real.exp_le_exp.2 hc) (Real.exp_pos _).le
      (hC₁.le.trans (le_max_left _ _))
  · obtain ⟨ha1, ha3, hb1, -⟩ := shapes_bounds hab
    have hφ := (isPhiVersion_phiMN hW (Nat.zero_le n)).cont
    -- `L(R_{a,b}) ≤ L(R_{3,1})`
    have hup : ∀ ω, lenObs ξ (phiMN W P 0 n) (rectAB a b) ω ≤
        lenObs ξ (phiMN W P 0 n) (rectAB 3 1) ω := fun ω =>
      lenObs_rectAB_mono hφ (by linarith) ha3 zero_le_one hb1 ω
    refine (measure_mono fun ω (hω : _ ≤ lenObs ξ (phiMN W P 0 n) (rectAB a b) ω) =>
      (show _ ≤ lenObs ξ (phiMN W P 0 n) (rectAB 3 1) ω from hω.trans (hup ω))).trans
      ((h18 hW ξ hξ n s hs).trans (ENNReal.ofReal_le_ofReal ?_))
    have hl : 0 < Real.log s := Real.log_pos (by linarith)
    have hc : -c₂ * s ^ 2 / Real.log s ≤ -min c₁ c₂ * s ^ 2 / Real.log s :=
      div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_right (neg_le_neg (min_le_right _ _)) (sq_nonneg s)) hl.le
    exact mul_le_mul (le_max_right _ _) (Real.exp_le_exp.2 hc) (Real.exp_pos _).le
      (hC₂.le.trans (le_max_right _ _))

end Uniform
end GaussianLQG
