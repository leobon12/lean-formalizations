import HigherDimLQGMetric.Sec8b.CountHolder
import HigherDimLQGMetric.Sec8b.CMFinite
import HigherDimLQGMetric.Sec8.AeFav

/-!
# Section 8: Cameron–Martin counting for favorable events

This specializes the finite counting-measure Hölder inequality to the Borel
representatives of Section 8 favorable events. The measure comparison uses
the normalized LGF; constant-shift invariance is handled separately when the
whole-space field is not normalized.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace HigherDimLQGMetric

open MeasureTheory
open HigherDimLFPP (Rd)

variable {d : ℕ} {Q : ℝ}

open Classical in
/-- Lemma 7.1 summed over the labeled sets of one scale/color/bin class. -/
theorem s7b_cm_favorable {ξ cs Cs : ℝ} {D Dt : DistRd d → ContMetric d}
    (hd : 2 ≤ d) (hD : Measurable D) (hDt : Measurable Dt)
    (T : Sec8TrapData d ξ cs Cs D Dt)
    {M0 : ℝ} (hM0 : 0 ≤ M0)
    (hcm : ∀ j < T.J, ∀ r : ℝ, 0 < r → ∀ z : Rd d,
      IsCMBounded (bumpAt (T.f j) r z) M0)
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {h : Ω → DistRd d}
    (hh : IsNormalizedLGF h P)
    (Cstar q R r : ℝ) (hr : 0 < r) (x y : Rd d)
    (S : Finset (Finset (Rd d × ℕ))) {k : ℕ}
    (hS : ∀ Z ∈ S, (∀ site ∈ Z, site.2 < T.J) ∧ Z.card ≤ k)
    {pH : ℝ} (hpH : 1 < pH) {K0 : ℝ} (hK0 : 0 ≤ K0)
    (hcount : ∀ᵐ ω ∂P,
      ((S.filter (fun Z => shiftNorm (h ω) (F_Z T.f r Z) ∈
        FavEventBorel D Dt ξ Q Cstar q R r T.b T.J T.N T.V T.f x y Z)).card : ℝ) ≤ K0) :
    ∑ Z ∈ S, P.real {ω | h ω ∈
      FavEventBorel D Dt ξ Q Cstar q R r T.b T.J T.N T.V T.f x y Z} ≤
      Real.exp ((pH - 1) / 2 * (k * M0) ^ 2) *
        (S.card : ℝ) ^ pH⁻¹ * K0 ^ (1 - pH⁻¹) := by
  have hA : ∀ Z : Finset (Rd d × ℕ),
      MeasurableSet (FavEventBorel D Dt ξ Q Cstar q R r T.b T.J T.N T.V T.f x y Z) := by
    intro Z
    exact measurableSet_FavEventBorel hD hDt ξ Q Cstar q R r T.b hr T.J T.N
      T.measurableN T.V T.openV T.f x y Z
  let F' : Finset (Rd d × ℕ) → C(Rd d, ℝ) :=
    fun Z => if Z ∈ S then F_Z T.f r Z else 0
  have hF : ∀ Z : Finset (Rd d × ℕ),
      IsCMBounded (F' Z) (k * M0) := by
    intro Z
    by_cases hZ : Z ∈ S
    · simpa only [F', ite_eq_left hZ] using
        s7b_cm_F_Z hM0 hcm hr (hS Z hZ).1 (hS Z hZ).2
    · have hC : 0 ≤ (k : ℝ) * M0 := mul_nonneg (Nat.cast_nonneg _) hM0
      simp only [F', ite_eq_right hZ]
      intro φ
      simpa only [ContinuousMap.zero_apply, zero_mul, integral_zero, abs_zero] using
        mul_nonneg hC (logNorm_nonneg φ.1)
  have hcount' : ∀ᵐ ω ∂P,
      ((S.filter (fun Z => shiftNorm (h ω) (F' Z) ∈
        FavEventBorel D Dt ξ Q Cstar q R r T.b T.J T.N T.V T.f x y Z)).card : ℝ) ≤ K0 := by
    filter_upwards [hcount] with ω hw
    have heq : S.filter (fun Z => shiftNorm (h ω) (F' Z) ∈
        FavEventBorel D Dt ξ Q Cstar q R r T.b T.J T.N T.V T.f x y Z) =
        S.filter (fun Z => shiftNorm (h ω) (F_Z T.f r Z) ∈
          FavEventBorel D Dt ξ Q Cstar q R r T.b T.J T.N T.V T.f x y Z) := by
      apply Finset.filter_congr
      intro Z hZ
      simp only [F', ite_eq_left hZ]
    simpa only [heq] using hw
  exact cm_holder_count hd hh S
    (fun Z => FavEventBorel D Dt ξ Q Cstar q R r T.b T.J T.N T.V T.f x y Z)
    hA F' hF hpH hK0 hcount'

end HigherDimLQGMetric
