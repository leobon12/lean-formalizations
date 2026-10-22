import HigherDimLQGMetric.Sec10.Cor102Bound

/-!
# Bounded positive multiplicative functions and the exact dilation identity

No regularity of the proportionality factor is needed: positivity, multiplicativity,
and one global upper bound force it to equal one.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace HigherDimLQGMetric

open MeasureTheory
open HigherDimLFPP (Rd)

variable {d : ℕ}

/-- A positive multiplicative function on positive reals with a global upper bound is one. -/
theorem s8c_mul_bdd_one (a : ℝ → ℝ)
    (ha : ∀ r : ℝ, 0 < r → 0 < a r)
    (hmul : ∀ r s : ℝ, 0 < r → 0 < s → a (r * s) = a r * a s)
    (hupper : ∃ M : ℝ, ∀ r : ℝ, 0 < r → a r < M) :
    ∀ r : ℝ, 0 < r → a r = 1 := by
  obtain ⟨M,hM⟩ := hupper
  have ha1 : a 1 = 1 := by
    have he := hmul 1 1 one_pos one_pos
    simp only [one_mul] at he
    have hp := ha 1 one_pos
    nlinarith
  have hpow (r : ℝ) (hr : 0 < r) (n : ℕ) : a (r ^ n) = (a r) ^ n := by
    induction n with
    | zero => simpa only [pow_zero] using ha1
    | succ n ih =>
        rw [pow_succ, hmul _ _ (pow_pos hr n) hr, ih, pow_succ]
  have hle (r : ℝ) (hr : 0 < r) : a r ≤ 1 := by
    by_contra hnot
    have hgt : 1 < a r := lt_of_not_ge hnot
    obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt M hgt
    have hbound := hM (r ^ n) (pow_pos hr n)
    rw [hpow r hr n] at hbound
    exact (not_lt_of_ge hn.le) hbound
  intro r hr
  have hri : 0 < r⁻¹ := inv_pos.mpr hr
  have he := hmul r r⁻¹ hr hri
  rw [mul_inv_cancel₀ hr.ne', ha1] at he
  have hlow : 1 ≤ a r := by
    rw [he]
    exact (mul_le_mul_of_nonneg_left (hle r⁻¹ hri) (ha r hr).le).trans_eq
      (mul_one _)
  exact le_antisymm (hle r hr) hlow

/-- Sharp weak uniqueness and sharp tightness give exact dilation covariance without a
regularity hypothesis on the scaling factor. -/
theorem s8c_transform_eq_ae (h14s : Theorem14SharpStmt)
    (hd : 3 ≤ d) {ξ Q : ℝ} (hξ : 0 < ξ)
    (hQ : Real.sqrt (2 * d) < Q)
    {D : DistRd d → ContMetric d} (hD : IsSharpWeakExpMetric d ξ Q D) :
    ∀ r : ℝ, ∀ hr : 0 < r,
      ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
        (h : Ω → DistRd d), IsLGFPlusCont h P →
        ∀ᵐ ω ∂P, ∀ f : C(Rd d, ℝ), ∀ u v : Rd d,
          (s8c_transform ξ Q r hr D (addFun (h ω) f)).1 (u, v) =
            (D (addFun (h ω) f)).1 (u, v) := by
  let a : ℝ → ℝ := fun r =>
    if hr : 0 < r then (s8c_transform_proportional h14s hd hξ hQ hr hD).choose else 1
  have ha (r : ℝ) (hr : 0 < r) : 0 < a r ∧
      ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
        (h : Ω → DistRd d), IsLGFPlusCont h P →
        ∀ᵐ ω ∂P, ∀ f : C(Rd d, ℝ), ∀ u v : Rd d,
          (s8c_transform ξ Q r hr D (addFun (h ω) f)).1 (u, v) =
            a r * (D (addFun (h ω) f)).1 (u, v) := by
    simpa only [a, dite_eq_left hr] using
      (s8c_transform_proportional h14s hd hξ hQ hr hD).choose_spec
  have hd2 : 2 ≤ d := by omega
  let _ : IsProbabilityMeasure (normLGFLaw d) := (normLGFLaw_spec_holds d hd2).1
  have hn : IsNormalizedLGF id (normLGFLaw d) := (normLGFLaw_spec_holds d hd2).2.1
  have hlaw (r : ℝ) (hr : 0 < r) :=
    s8c_normalized_law hd2 hr hD (ha r hr).2 (normLGFLaw d) id hn
  obtain ⟨lo,hi,hlo,hhi,hbounds⟩ :=
    s8c_factor_bounds hd hD a (fun r hr => (ha r hr).1) hlaw
  have hmul (r s : ℝ) (hr : 0 < r) (hs : 0 < s) : a (r * s) = a r * a s :=
    s8c_factor_mul hd hr hs (ha r hr).2 (ha s hs).2 (ha (r * s) (mul_pos hr hs)).2
  have hone := s8c_mul_bdd_one a (fun r hr => (ha r hr).1) hmul
    ⟨hi, fun r hr => (hbounds r hr).2⟩
  intro r hr Ω _ P _ h hh
  filter_upwards [(ha r hr).2 P h hh] with ω hω f u v
  simpa only [hone r hr, one_mul] using hω f u v

end HigherDimLQGMetric
