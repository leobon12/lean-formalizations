import QuantumZipper.Proofs.Zipper.FieldLawlerSubTopMain
import QuantumZipper.Proofs.Complex.TopoEilenberg

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# FL-TOPSEP, basic tools: logarithms along the circle, far poles, constant differences

Helpers for `flTopSep_holds` (`FLTopSep.lean`).

* `flts_sub_const`: two continuous logarithms of the same function on a preconnected set differ
  by a constant (the generic-space version of `JordanChord.log_sub_eq_of_isPreconnected`).
* `flts_hasLog_of_far`: if `(z - a)/(z - b)` has a continuous logarithm on `J ⊆ B̄(0, r)` and
  `‖b‖ > r`, then so does `z - a` (add the principal branch of `log (z - b)`, which is continuous
  on `B(0, ‖b‖)`).
* `flts_circle_lift`: a continuous logarithm `Lc` of `s ↦ ε e^{2πis} - x` on `[0, 1]` for
  `‖x‖ < ε`, with total increment `Lc 1 - Lc 0 = 2πi` (the index of the circle about `x` is `1`:
  Ahlfors, *Complex Analysis*, 3rd ed., Ch. 4, §2.1, p. 116; computed with `loopDeg`).

All three are own elementary arguments (cost rule, AGENT_GUIDE "Sources first", item 4).
-/

noncomputable section

open Set Metric Complex
open scoped Real

namespace QuantumZipper
namespace FieldLawler

open QuantumZipper.CA.Topo

/-- Two continuous logarithms of the same function on a preconnected set differ by a
constant. -/
theorem flts_sub_const {X : Type*} [TopologicalSpace X] {S : Set X} (hS : IsPreconnected S)
    {f g : X → ℂ} (hf : ContinuousOn f S) (hg : ContinuousOn g S)
    (he : ∀ z ∈ S, exp (f z) = exp (g z)) {u v : X} (hu : u ∈ S) (hv : v ∈ S) :
    f u - g u = f v - g v := by
  have h2 := two_pi_I_ne_zero'
  have hmaps : MapsTo (fun z => (f z - g z) / (2 * π * I)) S (range ((↑) : ℤ → ℂ)) := by
    intro z hz
    obtain ⟨n, hn⟩ := exp_eq_exp_iff_exists_int.1 (he z hz)
    exact ⟨n, by simp only [hn, add_sub_cancel_left, mul_div_cancel_right₀ _ h2]⟩
  have hc := hS.constant_of_mapsTo Complex.isClosedEmbedding_intCast.isInducing.isDiscrete_range
    ((hf.sub hg).div_const _) hmaps hu hv
  exact (div_left_inj' h2).1 hc

/-- A far pole can be removed: a logarithm of `(z - a)/(z - b)` on `J ⊆ B̄(0, r)`, `‖b‖ > r`,
gives a logarithm of `z - a`. -/
theorem flts_hasLog_of_far {J : Set ℂ} {a b : ℂ} {r : ℝ} (hr : 0 ≤ r)
    (hJ : J ⊆ closedBall 0 r) (hb : r < ‖b‖)
    (hL : HasLogOn (fun z => (z - a) / (z - b)) J) : HasLogOn (fun z => z - a) J := by
  obtain ⟨L, hLc, hLe⟩ := hL
  have hb0 : b ≠ 0 := norm_pos_iff.1 (lt_of_le_of_lt hr hb)
  have hlt : ∀ z ∈ J, ‖-z / b‖ < 1 := by
    intro z hz
    have hz' : ‖z‖ ≤ r := by simpa using hJ hz
    rw [norm_div, norm_neg, div_lt_one (norm_pos_iff.2 hb0)]
    linarith
  refine ⟨fun z => L z + log (-b) + log (1 + -z / b), ?_, fun z hz => ?_⟩
  · refine (hLc.add continuousOn_const).add fun z hz => ?_
    exact ((continuousAt_clog (mem_slitPlane_of_norm_lt_one (hlt z hz))).comp
      (f := fun w : ℂ => 1 + -w / b) (by fun_prop)).continuousWithinAt
  · have h1 : (1 : ℂ) + -z / b ≠ 0 := slitPlane_ne_zero (mem_slitPlane_of_norm_lt_one (hlt z hz))
    have hzb : z - b ≠ 0 := by
      intro h
      have hz' : ‖z‖ ≤ r := by simpa using hJ hz
      rw [sub_eq_zero.1 h] at hz'
      linarith
    simp only
    rw [exp_add, exp_add, hLe z hz, exp_log (neg_ne_zero.2 hb0), exp_log h1]
    field_simp
    ring

/-- A continuous logarithm along the circle `s ↦ ε e^{2πis}` about an inner point `x`, with
increment `2πi` over `[0, 1]`. -/
theorem flts_circle_lift {ε : ℝ} (hε : 0 < ε) {x : ℂ} (hx : ‖x‖ < ε) :
    ∃ Lc : ℝ → ℂ, Continuous Lc ∧
      (∀ s ∈ Icc (0 : ℝ) 1, exp (Lc s) = flCirc ε (2 * π * s) - x) ∧
      Lc 1 - Lc 0 = 2 * π * I := by
  let Cx : C(unitInterval, ℂ) :=
    ⟨fun s => flCirc ε (2 * π * (s : ℝ)) - x, by unfold flCirc; fun_prop⟩
  have hne : ∀ s, Cx s ≠ 0 := by
    intro s h
    have h' : flCirc ε (2 * π * (s : ℝ)) = x := sub_eq_zero.1 h
    have := flCirc_norm hε (2 * π * (s : ℝ))
    rw [h'] at this
    linarith
  have hc : Cx 0 = Cx 1 := by
    change flCirc ε (2 * π * 0) - x = flCirc ε (2 * π * 1) - x
    simp only [flCirc, mul_zero, mul_one]
    push_cast
    rw [zero_mul, Complex.exp_zero, Complex.exp_two_pi_mul_I]
  obtain ⟨L0, hL0⟩ := exists_lift_exp Cx hne
  have hdeg : loopDeg Cx hne = 1 := by
    rw [loopDeg_eq_of_norm_sub_lt Cx (circleLoop ε) hne (circleLoop_ne_zero hε.ne') hc
      (by simp [circleLoop, circleMap]) fun s => ?_]
    · exact loopDeg_circle hε.ne'
    · have e1 : Cx s - circleLoop ε s = -x := by
        simp [Cx, circleLoop, circleMap, flCirc]
      have e2 : ‖circleLoop ε s‖ = ε := by
        simp [circleLoop, abs_of_pos hε]
      rw [e1, e2, norm_neg]
      exact hx
  have hinc := loopDeg_eq_of_lift Cx hne hc L0.continuous hL0
  rw [hdeg] at hinc
  refine ⟨fun s => L0 (projIcc 0 1 zero_le_one s), L0.continuous.comp continuous_projIcc,
    fun s hs => ?_, ?_⟩
  · simp only
    rw [projIcc_of_mem _ hs, hL0]
    rfl
  · simp only [projIcc_left, projIcc_right]
    have e0 : (⟨0, left_mem_Icc.2 zero_le_one⟩ : Icc (0 : ℝ) 1) = (0 : unitInterval) := rfl
    have e1 : (⟨1, right_mem_Icc.2 zero_le_one⟩ : Icc (0 : ℝ) 1) = (1 : unitInterval) := rfl
    rw [e0, e1, hinc]
    push_cast
    ring

end FieldLawler
end QuantumZipper
