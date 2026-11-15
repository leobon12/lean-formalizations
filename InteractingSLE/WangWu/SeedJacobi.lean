/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec2.JacobiMoments
import Mathlib.Probability.Distributions.Beta
import Mathlib.Topology.ContinuousMap.Weierstrass
import Mathlib.MeasureTheory.Measure.HasOuterApproxClosed

/-!
# Wang–Wu at `κ = 4`, Proposition 5.2: the invariant law of the Jacobi diffusion

Packet PROVE-WW-C. Source: `source/external/WW17LP/wang_wu_lean_preprocessed.pdf`, §5.2, Proposition 5.2
(p. 34): "For `A, B > 0`, the diffusion on `[0, 1]` with generator `J_{A,B} f = ½ x(1 − x) f'' + ½ (A(1 − x) − Bx) f'`
… Its unique invariant probability measure is `π_{A,B}(dx) = x^{A−1}(1 − x)^{B−1}/B(A, B) dx`." The proof:
"The same moment identities show that `π_{A,B}` is invariant. Any invariant law has zero `p_n`-moment for `n ≥ 1`
because `λ_n > 0`; polynomial density then proves uniqueness."

The generator `J_{A,B}` is the landed `Sec2.Jacobi.gen 2 A B` (`(κ/4) x(1 − x) f'' + ½(a(1 − x) − bx) f'` at `κ = 2`), and
the landed polynomial martingale problem `Sec2.Jacobi.IsJacobiMP 2 A B` (PROVE-SEC2-JAC) is the martingale-problem
form of the diffusion on the clock line. This file proves:

* `integral_pow_betaMeasure`: the moments of `π_{A,B}` (Mathlib's `betaMeasure A B`) are
  `B(A + n, B)/B(A, B)`, and `jacobiMoment_two_eq` identifies them with the landed `jacobiMoment 2 A B n`, i.e. with
  the moments forced by the moment identities `E[J_{A,B} x^n] = 0` (`integral_pow_betaMeasure_eq_jacobiMoment`);
* `eq_of_integral_pow_eq` (polynomial density): two finite measures on `ℝ` carried by `[0, 1]` with the same
  moments are equal (Weierstrass approximation);
* **`IsJacobiMP.map_eq_betaMeasure`** (invariant law and its uniqueness): for `A, B > 0`, at every time the law of a
  solution of the Jacobi martingale problem is `π_{A,B}`; in particular `π_{A,B}` is the only law a stationary
  solution can have, and it has the strictly positive Lebesgue density `betaPDFReal A B` on `(0, 1)` used in
  Proposition 5.5 (`betaPDFReal_pos`).

Not in this file (see the handoff): the transition-density expansion in Jacobi polynomials (absolute continuity
of the transition law from every starting point) and the expected hitting times (formula (J)).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology Polynomial
open scoped NNReal ENNReal

namespace InteractingSLE

namespace WangWu

namespace JacobiLaw

/-! ### The moments of the beta law -/

theorem betaPDFReal_nonneg (A B x : ℝ) (hA : 0 < A) (hB : 0 < B) : 0 ≤ betaPDFReal A B x := by
  unfold betaPDFReal
  split_ifs with h
  · have := beta_pos hA hB
    have h1 : 0 ≤ x ^ (A - 1) := Real.rpow_nonneg h.1.le _
    have h2 : 0 ≤ (1 - x) ^ (B - 1) := Real.rpow_nonneg (by linarith [h.2]) _
    positivity
  · exact le_rfl

theorem integral_betaPDFReal_eq_one {A B : ℝ} (hA : 0 < A) (hB : 0 < B) :
    ∫ x, betaPDFReal A B x = 1 := by
  have h := lintegral_betaPDF_eq_one hA hB
  rw [integral_eq_lintegral_of_nonneg_ae (ae_of_all _ fun x => betaPDFReal_nonneg A B x hA hB)
    (measurable_betaPDFReal A B).aestronglyMeasurable]
  simp only [betaPDF] at h
  rw [h, ENNReal.toReal_one]

/-- The density identity `pdf_{A,B}(x) xⁿ = (B(A + n, B)/B(A, B)) pdf_{A+n,B}(x)`. -/
theorem betaPDFReal_mul_pow {A B : ℝ} (hA : 0 < A) (hB : 0 < B) (n : ℕ) (x : ℝ) :
    betaPDFReal A B x * x ^ n = beta (A + n) B / beta A B * betaPDFReal (A + n) B x := by
  unfold betaPDFReal
  split_ifs with h
  · have hx : x ≠ 0 := h.1.ne'
    have hb := beta_pos hA hB
    have hb' := beta_pos (by positivity : 0 < A + n) hB
    have e : x ^ (A + n - 1) = x ^ (A - 1) * x ^ n := by
      rw [show A + n - 1 = (A - 1) + (n : ℝ) by ring, Real.rpow_add_natCast hx]
    rw [e]
    field_simp
  · simp

theorem measurable_betaPDF' (A B : ℝ) : Measurable (betaPDF A B) :=
  (measurable_betaPDFReal A B).ennreal_ofReal

theorem integrable_pow_betaMeasure {A B : ℝ} (hA : 0 < A) (hB : 0 < B) (n : ℕ) :
    Integrable (fun x : ℝ => x ^ n) (betaMeasure A B) := by
  have : IsProbabilityMeasure (betaMeasure A B) := isProbabilityMeasureBeta hA hB
  refine Integrable.of_bound (C := 1) (continuous_pow n).aestronglyMeasurable ?_
  have hsupp : ∀ᵐ x ∂(betaMeasure A B), x ∈ Icc (0 : ℝ) 1 := by
    rw [betaMeasure, ae_withDensity_iff (measurable_betaPDF' A B)]
    refine ae_of_all _ fun x hx => ?_
    by_contra hxI
    apply hx
    simp only [betaPDF, ENNReal.ofReal_eq_zero, betaPDFReal]
    rw [ite_eq_right_iff.mpr (fun h => absurd h ?_)]
    rintro ⟨h0, h1⟩
    exact hxI ⟨h0.le, h1.le⟩
  filter_upwards [hsupp] with x hx
  rw [Real.norm_eq_abs, abs_pow]
  exact pow_le_one₀ (abs_nonneg x) (by rw [abs_of_nonneg hx.1]; exact hx.2)

/-- **The moments of `π_{A,B}`**: `∫ xⁿ dπ_{A,B} = B(A + n, B)/B(A, B)`. -/
theorem integral_pow_betaMeasure {A B : ℝ} (hA : 0 < A) (hB : 0 < B) (n : ℕ) :
    ∫ x, x ^ n ∂(betaMeasure A B) = beta (A + n) B / beta A B := by
  rw [betaMeasure, integral_withDensity_eq_integral_toReal_smul
    (measurable_betaPDF' A B) (ae_of_all _ fun _ => ENNReal.ofReal_lt_top)]
  simp only [betaPDF, ENNReal.toReal_ofReal (betaPDFReal_nonneg A B _ hA hB), smul_eq_mul,
    betaPDFReal_mul_pow hA hB n, integral_const_mul,
    integral_betaPDFReal_eq_one (by positivity : 0 < A + n) hB, mul_one]

/-- The ratio of consecutive beta moments: `B(A + n + 1, B)/B(A + n, B) = (A + n)/(A + n + B)`. -/
theorem beta_succ_div {A B : ℝ} (hA : 0 < A) (hB : 0 < B) (n : ℕ) :
    beta (A + (n + 1 : ℕ)) B = beta (A + n) B * ((A + n) / (A + n + B)) := by
  have h1 : 0 < A + n := by positivity
  have h2 : 0 < A + n + B := by positivity
  unfold beta
  have e1 : A + ((n + 1 : ℕ) : ℝ) = (A + n) + 1 := by push_cast; ring
  rw [e1, show A + n + 1 + B = (A + n + B) + 1 by ring, Real.Gamma_add_one h1.ne',
    Real.Gamma_add_one h2.ne']
  have g1 := Real.Gamma_pos_of_pos h1
  have g2 := Real.Gamma_pos_of_pos h2
  have g3 := Real.Gamma_pos_of_pos hB
  field_simp

/-- **The moment identities**: `jacobiMoment 2 A B n = B(A + n, B)/B(A, B)`. -/
theorem jacobiMoment_two_eq {A B : ℝ} (hA : 0 < A) (hB : 0 < B) (n : ℕ) :
    Sec2.Jacobi.jacobiMoment 2 A B n = beta (A + n) B / beta A B := by
  have hb := beta_pos hA hB
  induction n with
  | zero => simp [Sec2.Jacobi.jacobiMoment, hb.ne']
  | succ n ih =>
    rw [Sec2.Jacobi.jacobiMoment, ih, beta_succ_div hA hB n, Sec2.Jacobi.dcoef, Sec2.Jacobi.ccoef]
    have h2 : 0 < A + n + B := by positivity
    have h3 : (0 : ℝ) < n + 1 := by positivity
    have hr : (2 / 4 * (((n + 1 : ℕ) : ℝ) * (((n + 1 : ℕ) : ℝ) - 1)) + ((n + 1 : ℕ) : ℝ) * A / 2) /
        -(-(2 / 4 * (((n + 1 : ℕ) : ℝ) * (((n + 1 : ℕ) : ℝ) - 1)) + ((n + 1 : ℕ) : ℝ) * (A + B) / 2)) =
        (A + n) / (A + n + B) := by
      push_cast
      rw [div_eq_div_iff (by nlinarith) h2.ne']
      ring
    rw [hr]
    ring

theorem integral_pow_betaMeasure_eq_jacobiMoment {A B : ℝ} (hA : 0 < A) (hB : 0 < B) (n : ℕ) :
    ∫ x, x ^ n ∂(betaMeasure A B) = Sec2.Jacobi.jacobiMoment 2 A B n := by
  rw [integral_pow_betaMeasure hA hB, jacobiMoment_two_eq hA hB]

/-! ### Polynomial density -/

/-- Two finite measures carried by `[0, 1]` with integrable and equal monomial moments have equal integrals of
every polynomial. -/
theorem integral_eval_eq {μ ν : Measure ℝ} (hμ : ∀ n : ℕ, Integrable (fun x : ℝ => x ^ n) μ)
    (hν : ∀ n : ℕ, Integrable (fun x : ℝ => x ^ n) ν)
    (h : ∀ n : ℕ, ∫ x, x ^ n ∂μ = ∫ x, x ^ n ∂ν) (p : ℝ[X]) :
    ∫ x, p.eval x ∂μ = ∫ x, p.eval x ∂ν := by
  simp_rw [eval_eq_sum_range]
  rw [integral_finsetSum _ fun i _ => (hμ i).const_mul _,
    integral_finsetSum _ fun i _ => (hν i).const_mul _]
  exact Finset.sum_congr rfl fun i _ => by rw [integral_const_mul, integral_const_mul, h i]

/-- **Moment determinacy on `[0, 1]`**: two finite measures on `ℝ` carried by `[0, 1]` with the same moments are
equal. -/
theorem eq_of_integral_pow_eq {μ ν : Measure ℝ} [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (hμI : ∀ᵐ x ∂μ, x ∈ Icc (0 : ℝ) 1) (hνI : ∀ᵐ x ∂ν, x ∈ Icc (0 : ℝ) 1)
    (h : ∀ n : ℕ, ∫ x, x ^ n ∂μ = ∫ x, x ^ n ∂ν) : μ = ν := by
  have hint : ∀ {ρ : Measure ℝ} [IsFiniteMeasure ρ], (∀ᵐ x ∂ρ, x ∈ Icc (0 : ℝ) 1) →
      ∀ n : ℕ, Integrable (fun x : ℝ => x ^ n) ρ := by
    intro ρ _ hρ n
    refine Integrable.of_bound (C := 1) (continuous_pow n).aestronglyMeasurable ?_
    filter_upwards [hρ] with x hx
    rw [Real.norm_eq_abs, abs_pow]
    exact pow_le_one₀ (abs_nonneg x) (by rw [abs_of_nonneg hx.1]; exact hx.2)
  refine ext_of_forall_integral_eq_of_IsFiniteMeasure fun f => ?_
  -- approximate `f` on `[0, 1]` by polynomials
  have hdense := polynomialFunctions_closure_eq_top (0 : ℝ) 1
  set F : C(Icc (0 : ℝ) 1, ℝ) := ⟨fun x => f x, f.continuous.comp continuous_subtype_val⟩
  have hF : F ∈ (polynomialFunctions (Icc (0 : ℝ) 1)).topologicalClosure := by
    rw [hdense]; trivial
  have key : ∀ ε > 0, |∫ x, f x ∂μ - ∫ x, f x ∂ν| ≤ ε * (μ.real univ + ν.real univ) := by
    intro ε hε
    obtain ⟨g, hg, hFg⟩ := Metric.mem_closure_iff.mp hF ε hε
    obtain ⟨p, -, rfl⟩ := Subalgebra.mem_map.mp hg
    have hclose : ∀ x ∈ Icc (0 : ℝ) 1, |f x - p.eval x| ≤ ε := fun x hx => by
      have := ContinuousMap.dist_apply_le_dist (f := F) (g := (Polynomial.toContinuousMapOnAlgHom
        (Icc (0 : ℝ) 1) p)) ⟨x, hx⟩
      simp only [Polynomial.toContinuousMapOnAlgHom_apply, Polynomial.toContinuousMapOn_apply,
        Polynomial.toContinuousMap_apply, F, ContinuousMap.coe_mk, Real.dist_eq] at this
      exact this.trans hFg.le
    have hp := integral_eval_eq (hint hμI) (hint hνI) h p
    have hpμ : Integrable (fun x => p.eval x) μ := by
      have : (fun x => p.eval x) = fun x => ∑ i ∈ Finset.range (p.natDegree + 1), p.coeff i * x ^ i := by
        funext x; exact eval_eq_sum_range x
      rw [this]; exact integrable_finsetSum _ fun i _ => (hint hμI i).const_mul _
    have hpν : Integrable (fun x => p.eval x) ν := by
      have : (fun x => p.eval x) = fun x => ∑ i ∈ Finset.range (p.natDegree + 1), p.coeff i * x ^ i := by
        funext x; exact eval_eq_sum_range x
      rw [this]; exact integrable_finsetSum _ fun i _ => (hint hνI i).const_mul _
    have hb : ∀ {ρ : Measure ℝ} [IsFiniteMeasure ρ], (∀ᵐ x ∂ρ, x ∈ Icc (0 : ℝ) 1) →
        Integrable (fun x => p.eval x) ρ →
        |∫ x, f x ∂ρ - ∫ x, p.eval x ∂ρ| ≤ ε * ρ.real univ := by
      intro ρ _ hρ hpρ
      rw [← integral_sub (f.integrable ρ) hpρ]
      calc |∫ x, (f x - p.eval x) ∂ρ| = ‖∫ x, (f x - p.eval x) ∂ρ‖ := (Real.norm_eq_abs _).symm
        _ ≤ ε * ρ.real univ := by
          refine norm_integral_le_of_norm_le_const ?_
          filter_upwards [hρ] with x hx
          rw [Real.norm_eq_abs]; exact hclose x hx
    have h1 := hb hμI hpμ
    have h2 := hb hνI hpν
    rw [hp] at h1
    calc |∫ x, f x ∂μ - ∫ x, f x ∂ν|
        = |(∫ x, f x ∂μ - ∫ x, p.eval x ∂ν) - (∫ x, f x ∂ν - ∫ x, p.eval x ∂ν)| := by ring_nf
      _ ≤ |∫ x, f x ∂μ - ∫ x, p.eval x ∂ν| + |∫ x, f x ∂ν - ∫ x, p.eval x ∂ν| := abs_sub _ _
      _ ≤ ε * μ.real univ + ε * ν.real univ := add_le_add h1 h2
      _ = ε * (μ.real univ + ν.real univ) := by ring
  have hM : 0 ≤ μ.real univ + ν.real univ := by positivity
  by_contra hne
  have hpos : 0 < |∫ x, f x ∂μ - ∫ x, f x ∂ν| := abs_pos.mpr (sub_ne_zero.mpr hne)
  set M := μ.real univ + ν.real univ
  have := key (|∫ x, f x ∂μ - ∫ x, f x ∂ν| / (2 * (M + 1))) (by positivity)
  have hM1 : 0 < M + 1 := by linarith
  rw [div_mul_eq_mul_div, le_div_iff₀ (by positivity)] at this
  nlinarith

/-! ### The law of the Jacobi diffusion -/

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P]

/-- **Proposition 5.2, the invariant law.** For `A, B > 0`, at every time `u` the law of a solution `U` of the
Jacobi martingale problem with generator `J_{A,B}` (`IsJacobiMP 2 A B`, the stationary diffusion on the clock line)
is `π_{A,B} = betaMeasure A B`. -/
theorem IsJacobiMP.map_eq_betaMeasure {A B : ℝ} (hA : 0 < A) (hB : 0 < B) {U : ℝ → Ω → ℝ}
    (hU : Sec2.Jacobi.IsJacobiMP 2 A B P U) (u : ℝ) : P.map (U u) = betaMeasure A B := by
  have : IsProbabilityMeasure (betaMeasure A B) := isProbabilityMeasureBeta hA hB
  have hm : Measurable (U u) := hU.measurable u
  have : IsProbabilityMeasure (P.map (U u)) := inferInstance
  refine eq_of_integral_pow_eq ?_ ?_ fun n => ?_
  · exact (ae_map_iff hm.aemeasurable measurableSet_Icc).mpr (ae_of_all _ fun ω => hU.mem_Icc u ω)
  · rw [betaMeasure, ae_withDensity_iff (measurable_betaPDF' A B)]
    refine ae_of_all _ fun x hx => ?_
    by_contra hxI
    apply hx
    simp only [betaPDF, ENNReal.ofReal_eq_zero, betaPDFReal]
    rw [ite_eq_right_iff.mpr (fun h => absurd h ?_)]
    rintro ⟨h0, h1⟩
    exact hxI ⟨h0.le, h1.le⟩
  · rw [integral_map hm.aemeasurable (continuous_pow n).aestronglyMeasurable,
      hU.moment_eq (by norm_num) (by linarith) n u, integral_pow_betaMeasure_eq_jacobiMoment hA hB]

end JacobiLaw

end WangWu

end InteractingSLE
