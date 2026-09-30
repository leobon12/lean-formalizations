import QuantumZipper.Proofs.Thm18.G1PathCoordFam

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# G1-FROST-B, part 0: Frostman conditions with a general exponent `α`

`PushFrostman` (G1PathCoord.lean) fixes the Frostman exponent at `1/3`. The Koebe-type argument
of G1FrostAlphaKoebe.lean gives a (small) positive exponent only, so this file restates the
Frostman input for an arbitrary exponent `α`:

* `PushFrostmanα α ψ`: `PushFrostman` with `s^α` in place of `s^{1/3}`;
* `FcFrostmanα α ψ`: its unparametrized form (centres `‖c‖ ≤ 2R`, radii `r ∈ [e^{-R}, e^R]`);
* `pushFrostmanα_of_fc`: `FcFrostmanα α ψ → PushFrostmanα α ψ` (for `0 ≤ α`);
* `SideFrostGoodα α γ a`: `SideFrostGood` with `PushFrostmanα α`.

All proofs are own elementary bookkeeping (the rescaling `e^{q₃}` of the pushed circle), the
same as `pushFrostman_of_fc` of G1FrostRed.lean with `1/3 ↦ α`.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Metric Set Function Real
open scoped ENNReal NNReal Topology

namespace QuantumZipper
namespace Thm18Asm
namespace G1RC

open CircleFubini

/-- **Uniform `α`-Frostman bound for the pushed folded circles** (`PushFrostman` with a general
exponent `α`). -/
def PushFrostmanα (α : ℝ) (ψ : ℂ → ℂ) : Prop :=
  ∀ R : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ q ∈ KolmD.boxD (d := 4) R, ∀ (w : ℂ) (s : ℝ),
    0 < s → ((circM.map (pushPhi ψ q)) (closedBall w s)).toReal ≤ C * s ^ α

/-- **Unparametrized `α`-Frostman bound for pushed folded circles**: for every `R`, uniformly
over centres `‖c‖ ≤ 2R` and radii `r ∈ [e^{-R}, e^R]`, the normalized arc-length of the set of
angles `θ` with `ψ(fold(c + r e^{iθ})) ∈ B̄(y, s)` is `≤ C s^α`. -/
def FcFrostmanα (α : ℝ) (ψ : ℂ → ℂ) : Prop :=
  ∀ R : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ c : ℂ, ‖c‖ ≤ 2 * R → ∀ r : ℝ, Real.exp (-R) ≤ r →
    r ≤ Real.exp R → ∀ (y : ℂ) (s : ℝ), 0 < s →
      (circM {θ | ψ (foldH (circleMap c r θ)) ∈ closedBall y s}).toReal ≤ C * s ^ α

theorem norm_cenQ_le_boxα {R : ℕ} {q : Fin 4 → ℝ} (hq : q ∈ KolmD.boxD (d := 4) R) :
    ‖cenQ q‖ ≤ 2 * R := by
  have h0 := hq 0
  have h1 := hq 1
  unfold cenQ
  calc ‖(q 0 : ℂ) + (q 1 : ℂ) * Complex.I‖ ≤ ‖(q 0 : ℂ)‖ + ‖(q 1 : ℂ) * Complex.I‖ :=
        norm_add_le _ _
    _ = |q 0| + |q 1| := by simp [Complex.norm_real]
    _ ≤ 2 * R := by linarith

/-- The preimage of a ball under the parametrized pushed circle. -/
theorem pushPhi_preimage_subsetα (ψ : ℂ → ℂ) (q : Fin 4 → ℝ) (w : ℂ) (s : ℝ) :
    pushPhi ψ q ⁻¹' closedBall w s ⊆
      {θ | ψ (foldH (circleMap (cenQ q) (Real.exp (q 2)) θ)) ∈
        closedBall (w / (Real.exp (q 3) : ℂ)) (s / Real.exp (q 3))} := by
  intro θ hθ
  simp only [mem_preimage, mem_closedBall, dist_eq_norm, pushPhi] at hθ
  simp only [Set.mem_ofPred_eq, mem_closedBall, dist_eq_norm]
  set E : ℂ := (Real.exp (q 3) : ℂ) with hE
  have hE0 : E ≠ 0 := by
    rw [hE]; exact_mod_cast (Real.exp_pos _).ne'
  have hnE : ‖E‖ = Real.exp (q 3) := by
    rw [hE, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  set x := ψ (foldH (circleMap (cenQ q) (Real.exp (q 2)) θ))
  have heq : x - w / E = (E * x - w) / E := by field_simp
  rw [heq, norm_div, hnE]
  exact div_le_div_of_nonneg_right hθ (Real.exp_pos _).le

/-- **`PushFrostmanα` from the unparametrized bound.** -/
theorem pushFrostmanα_of_fc {α : ℝ} (hα : 0 ≤ α) {ψ : ℂ → ℂ} (hc : ContinuousOn ψ Hbar)
    (h : FcFrostmanα α ψ) : PushFrostmanα α ψ := by
  intro R
  obtain ⟨C, hC, hb⟩ := h R
  refine ⟨C * Real.exp (R * α), mul_nonneg hC (Real.exp_pos _).le, ?_⟩
  intro q hq w s hs
  have h2 := hq 2
  have h3 := hq 3
  rw [abs_le] at h2 h3
  have hr1 : Real.exp (-R) ≤ Real.exp (q 2) := Real.exp_le_exp.2 (by linarith)
  have hr2 : Real.exp (q 2) ≤ Real.exp R := Real.exp_le_exp.2 (by linarith)
  have hs' : 0 < s / Real.exp (q 3) := div_pos hs (Real.exp_pos _)
  have hb' := hb (cenQ q) (norm_cenQ_le_boxα hq) _ hr1 hr2 (w / (Real.exp (q 3) : ℂ)) _ hs'
  have hmeas : Measurable (pushPhi ψ q) :=
    ((continuous_pushPhi hc).comp (Continuous.prodMk_right q)).measurable
  have hmono : (circM.map (pushPhi ψ q) (closedBall w s)).toReal ≤
      (circM {θ | ψ (foldH (circleMap (cenQ q) (Real.exp (q 2)) θ)) ∈
        closedBall (w / (Real.exp (q 3) : ℂ)) (s / Real.exp (q 3))}).toReal := by
    refine ENNReal.toReal_mono (measure_ne_top _ _) ?_
    rw [Measure.map_apply hmeas measurableSet_closedBall]
    exact measure_mono (pushPhi_preimage_subsetα ψ q w s)
  refine hmono.trans (hb'.trans ?_)
  have hsc : s / Real.exp (q 3) ≤ s * Real.exp R := by
    rw [div_eq_mul_inv, ← Real.exp_neg]
    exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 (by linarith)) hs.le
  have hpow : (s / Real.exp (q 3)) ^ α ≤ s ^ α * Real.exp (R * α) := by
    calc (s / Real.exp (q 3)) ^ α ≤ (s * Real.exp R) ^ α :=
          Real.rpow_le_rpow hs'.le hsc hα
      _ = s ^ α * Real.exp (R * α) := by
          rw [Real.mul_rpow hs.le (Real.exp_pos _).le, ← Real.exp_mul]
  calc C * (s / Real.exp (q 3)) ^ α ≤ C * (s ^ α * Real.exp (R * α)) :=
        mul_le_mul_of_nonneg_left hpow hC
    _ = C * Real.exp (R * α) * s ^ α := by ring

end G1RC
end Thm18Asm
end QuantumZipper
