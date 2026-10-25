import SupercriticalLQGUniqueness.B2.PfeAxioms.TranslationFiniteLFPP

 


set_option autoImplicit false
noncomputable section

open Set
open scoped ENNReal
open LQGMetric LQGMetric.DFGPS LQGMetric.LFPP

namespace SupercriticalLQGUniqueness.B2.PfeAxioms

theorem normalizedLFPPMetric_dilate_sub_const
    (ξ : ℝ) (a b : Ioi (0 : ℝ)) (φ ψ : C(ℂ, ℝ))
    (r : ℝ) (hr : 0 < r) (c : ℝ)
    (hψ : ∀ z, ψ z = φ ((r : ℂ) * z) - c)
    (p : ℂ × ℂ) :
    PfeWeyl.normalizedLFPPMetric ξ b ψ p =
      ENNReal.ofReal (((a : ℝ) / (r * (b : ℝ))) * Real.exp (-ξ * c)) *
        B2.LscTop.dilate ⟨r, Set.mem_Ioi.mpr hr⟩
          (PfeWeyl.normalizedLFPPMetric ξ a φ) p := by
  rw [PfeWeyl.normalizedLFPPMetric_apply,
    B2.LscTop.dilate_apply, PfeWeyl.normalizedLFPPMetric_apply,
    B2.LscTop.lfppDistance_eq_lfppD,
    B2.LscTop.lfppDistance_eq_lfppD]
  simp only [LQGMetric.LFPP.lfppD, Complex.real_smul]
  have hφ : (ψ : ℂ → ℝ) =
      fun z => φ ((r : ℂ) * z) + -c := by
    funext z
    rw [hψ z]
    ring
  rw [hφ, lfppDOn_add_const]
  have hA := lfppDOn_affine ξ (φ : ℂ → ℝ)
    (S := Set.univ) (S' := Set.univ) (b := 0) (c := (r : ℂ))
    (by exact_mod_cast hr.ne') (fun z => by simp) p.1 p.2
  simp only [zero_add, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr] at hA
  have hmul : ENNReal.ofReal (r⁻¹) * ENNReal.ofReal r = 1 := by
    rw [← ENNReal.ofReal_mul (by positivity)]
    simp [hr.ne']
  have hL : lfppDOn ξ (fun z => φ ((r : ℂ) * z)) Set.univ p.1 p.2 =
      ENNReal.ofReal (r⁻¹) *
        lfppDOn ξ φ Set.univ ((r : ℂ) * p.1) ((r : ℂ) * p.2) := by
    calc
      _ = ENNReal.ofReal (r⁻¹) * (ENNReal.ofReal r *
          lfppDOn ξ (fun z => φ ((r : ℂ) * z)) Set.univ p.1 p.2) := by
        rw [← mul_assoc, hmul, one_mul]
      _ = _ := by rw [← hA]
  rw [hL]
  have hcoeff :
      ENNReal.ofReal ((b : ℝ)⁻¹) *
        (ENNReal.ofReal (Real.exp (ξ * -c)) *
          (ENNReal.ofReal (r⁻¹) *
            lfppDOn ξ φ Set.univ ((r : ℂ) * p.1) ((r : ℂ) * p.2))) =
      ENNReal.ofReal (((a : ℝ) / (r * (b : ℝ))) * Real.exp (-ξ * c)) *
        (ENNReal.ofReal ((a : ℝ)⁻¹) *
          lfppDOn ξ φ Set.univ ((r : ℂ) * p.1) ((r : ℂ) * p.2)) := by
    have ha : 0 < (a : ℝ) := a.property
    have hb : 0 < (b : ℝ) := b.property
    have ha0 : (a : ℝ) ≠ 0 := ha.ne'
    have hb0 : (b : ℝ) ≠ 0 := hb.ne'
    have hr0 : r ≠ 0 := hr.ne'
    have he : (b : ℝ)⁻¹ * Real.exp (ξ * -c) * r⁻¹ =
        ((a : ℝ) / (r * (b : ℝ)) * Real.exp (-ξ * c)) * (a : ℝ)⁻¹ := by
      field_simp [ha0, hb0, hr0]
    calc
      _ = (ENNReal.ofReal ((b : ℝ)⁻¹) *
          ENNReal.ofReal (Real.exp (ξ * -c)) * ENNReal.ofReal (r⁻¹)) *
          lfppDOn ξ φ Set.univ ((r : ℂ) * p.1) ((r : ℂ) * p.2) := by ac_rfl
      _ = ENNReal.ofReal ((b : ℝ)⁻¹ * Real.exp (ξ * -c) * r⁻¹) *
          lfppDOn ξ φ Set.univ ((r : ℂ) * p.1) ((r : ℂ) * p.2) := by
        rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_mul (by positivity)]
      _ = ENNReal.ofReal
          (((a : ℝ) / (r * (b : ℝ)) * Real.exp (-ξ * c)) * (a : ℝ)⁻¹) *
          lfppDOn ξ φ Set.univ ((r : ℂ) * p.1) ((r : ℂ) * p.2) := by rw [he]
      _ = _ := by
        rw [ENNReal.ofReal_mul (by positivity)]
        ac_rfl
  simpa only [mul_neg] using hcoeff

end SupercriticalLQGUniqueness.B2.PfeAxioms
