import HigherDimLQGMetric.Sec10.Cor102Law

/-!
# Composition and uniqueness of fixed dilation factors

The dilation maps form a multiplicative action. Positive point distances make the
proportionality factor unique.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace HigherDimLQGMetric

open MeasureTheory
open HigherDimLFPP (Rd e₁)

variable {d : ℕ}

/-- Composition of the fixed dilation maps. -/
theorem s8c_transform_comp (ξ Q : ℝ) {r s : ℝ} (hr : 0 < r) (hs : 0 < s)
    (D : DistRd d → ContMetric d) :
    s8c_transform ξ Q s hs (s8c_transform ξ Q r hr D) =
      s8c_transform ξ Q (r * s) (mul_pos hr hs) D := by
  funext g
  apply Subtype.ext
  apply ContinuousMap.ext
  rintro ⟨u,v⟩
  rw [s8c_transform_apply, s8c_transform_apply, s8c_transform_apply]
  have hfield : affineComp r⁻¹ 0 (affineComp s⁻¹ 0 g) =
      affineComp (r * s)⁻¹ 0 g := by
    rw [affineComp_affineComp]
    simp only [smul_zero, zero_add]
    congr 1
    exact (mul_inv_rev r s).symm
  rw [hfield, Real.mul_rpow hr.le hs.le]
  simp only [smul_smul, mul_inv_rev]
  ring

/-- A constant multiplying a positive metric point distance is uniquely determined by an
almost-sure proportionality identity. -/
theorem s8c_factor_unique (hd : 1 ≤ d)
    {D : DistRd d → ContMetric d} {a b : ℝ}
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (h : Ω → DistRd d)
    (ha : ∀ᵐ ω ∂P, (D (h ω)).1 (0, e₁ d) * a = (D (h ω)).1 (0, e₁ d) * b) :
    a = b := by
  obtain ⟨ω, hω⟩ := Filter.Eventually.exists ha
  have hp : 0 < (D (h ω)).1 (0, e₁ d) :=
    (D (h ω)).apply_pos (HigherDimLFPP.e₁_ne_zero (by omega : 0 < d)).symm
  exact mul_left_cancel₀ hp.ne' hω

/-- Multiplicativity of the constants obtained from sharp weak uniqueness. -/
theorem s8c_factor_mul (hd : 3 ≤ d) {ξ Q r s : ℝ} (hr : 0 < r) (hs : 0 < s)
    {D : DistRd d → ContMetric d} {a_r a_s a_rs : ℝ}
    (ha_r : ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
      (h : Ω → DistRd d), IsLGFPlusCont h P →
      ∀ᵐ ω ∂P, ∀ f : C(Rd d, ℝ), ∀ u v : Rd d,
        (s8c_transform ξ Q r hr D (addFun (h ω) f)).1 (u, v) =
          a_r * (D (addFun (h ω) f)).1 (u, v))
    (ha_s : ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
      (h : Ω → DistRd d), IsLGFPlusCont h P →
      ∀ᵐ ω ∂P, ∀ f : C(Rd d, ℝ), ∀ u v : Rd d,
        (s8c_transform ξ Q s hs D (addFun (h ω) f)).1 (u, v) =
          a_s * (D (addFun (h ω) f)).1 (u, v))
    (ha_rs : ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
      (h : Ω → DistRd d), IsLGFPlusCont h P →
      ∀ᵐ ω ∂P, ∀ f : C(Rd d, ℝ), ∀ u v : Rd d,
        (s8c_transform ξ Q (r * s) (mul_pos hr hs) D (addFun (h ω) f)).1 (u, v) =
          a_rs * (D (addFun (h ω) f)).1 (u, v)) :
    a_rs = a_r * a_s := by
  have hd2 : 2 ≤ d := by omega
  let _ : IsProbabilityMeasure (normLGFLaw d) := (normLGFLaw_spec_holds d hd2).1
  have hn : IsNormalizedLGF id (normLGFLaw d) := (normLGFLaw_spec_holds d hd2).2.1
  let g : DistRd d → DistRd d := affineComp s⁻¹ 0
  have hg : IsLGFPlusCont g (normLGFLaw d) :=
    s8c_lgfPlusCont_affine hn.1.isLGFPlusCont (inv_pos.mpr hs) 0
  have hAE : ∀ᵐ x ∂(normLGFLaw d),
      a_rs * (D x).1 (0, e₁ d) = a_r * a_s * (D x).1 (0, e₁ d) := by
    filter_upwards [ha_r (normLGFLaw d) g hg,
      ha_s (normLGFLaw d) id hn.1.isLGFPlusCont,
      ha_rs (normLGFLaw d) id hn.1.isLGFPlusCont] with x h1 h2 h3
    have he := congrArg
      (fun F : DistRd d → ContMetric d => (F x).1 (0, e₁ d))
      (s8c_transform_comp ξ Q hr hs D)
    have h1' := h1 0 0 (s • e₁ d)
    have h2' := h2 0 0 (e₁ d)
    have h3' := h3 0 0 (e₁ d)
    simp only [addFun_zero] at h1' h2' h3'
    change (s8c_transform ξ Q s hs D x).1 (0, e₁ d) =
      a_s * (D x).1 (0, e₁ d) at h2'
    change (s8c_transform ξ Q (r * s) (mul_pos hr hs) D x).1 (0, e₁ d) =
      a_rs * (D x).1 (0, e₁ d) at h3'
    rw [s8c_transform_apply] at he
    simp only [smul_zero] at he
    rw [h1', h3'] at he
    rw [s8c_transform_apply] at h2'
    simp only [smul_zero] at he h2'
    calc
      a_rs * (D x).1 (0, e₁ d) =
          (s ^ (ξ * Q))⁻¹ * (a_r * (D (g x)).1 (0, s • e₁ d)) := he.symm
      _ = a_r * ((s ^ (ξ * Q))⁻¹ * (D (g x)).1 (0, s • e₁ d)) := by ring
      _ = a_r * (a_s * (D x).1 (0, e₁ d)) := by rw [h2']
      _ = a_r * a_s * (D x).1 (0, e₁ d) := by ring
  have heq := s8c_factor_unique (by omega : 1 ≤ d) (P := normLGFLaw d)
    (h := id) (D := D) (a := a_rs) (b := a_r * a_s) (by
      filter_upwards [hAE] with x hx
      change (D x).1 (0, e₁ d) * a_rs =
        (D x).1 (0, e₁ d) * (a_r * a_s)
      calc
        (D x).1 (0, e₁ d) * a_rs = a_rs * (D x).1 (0, e₁ d) := mul_comm _ _
        _ = a_r * a_s * (D x).1 (0, e₁ d) := hx
        _ = (D x).1 (0, e₁ d) * (a_r * a_s) := mul_comm _ _)
  exact heq

end HigherDimLQGMetric
