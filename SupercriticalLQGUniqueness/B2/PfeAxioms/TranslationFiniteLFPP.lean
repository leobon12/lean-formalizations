import SupercriticalLQGUniqueness.B2.PfeAxioms.TranslationTopology
import SupercriticalLQGUniqueness.B2.PfeWeyl.NormalizedLFPP
import LQGMetric.Papers.DFGPS.L2_8GenHeat

 

set_option autoImplicit false
noncomputable section

open Set
open scoped ENNReal
open LQGMetric LQGMetric.DFGPS

namespace SupercriticalLQGUniqueness.B2.PfeAxioms

theorem normalizedLFPPMetric_translate
    (ξ : ℝ) (a : Ioi (0 : ℝ)) (φ ψ : C(ℂ, ℝ))
    (z : ℂ) (hψ : ∀ u, ψ u = φ (u + z)) :
    PfeWeyl.normalizedLFPPMetric ξ a ψ =
      translateMetric z (PfeWeyl.normalizedLFPPMetric ξ a φ) := by
  apply LSCMetric.ext
  intro p
  rw [translateMetric_apply, PfeWeyl.normalizedLFPPMetric_apply,
    PfeWeyl.normalizedLFPPMetric_apply]
  congr 1
  rw [B2.LscTop.lfppDistance_eq_lfppD,
    B2.LscTop.lfppDistance_eq_lfppD]
  have hA := lfppDOn_affine ξ (φ : ℂ → ℝ)
    (S := Set.univ) (S' := Set.univ) (b := z) (c := 1)
    one_ne_zero (fun x => by simp) p.1 p.2
  simp only [one_mul, norm_one, ENNReal.ofReal_one] at hA
  have hψ' : (ψ : ℂ → ℝ) = fun x => φ (z + x) :=
    funext fun x => by rw [hψ x, add_comm]
  simpa only [LQGMetric.LFPP.lfppD, hψ', add_comm] using hA.symm

theorem lfppDOn_add_const (ξ : ℝ) (φ : ℂ → ℝ)
    (S : Set ℂ) (c : ℝ) (x y : ℂ) :
    LQGMetric.LFPP.lfppDOn ξ (fun u => φ u + c) S x y =
      ENNReal.ofReal (Real.exp (ξ * c)) *
        LQGMetric.LFPP.lfppDOn ξ φ S x y := by
  unfold LQGMetric.LFPP.lfppDOn
  rw [ENNReal.mul_iInf_of_ne (by simp [Real.exp_pos]) ENNReal.ofReal_ne_top]
  simp only [lfppLen_add_const]

theorem normalizedLFPPMetric_translate_sub_const
    (ξ : ℝ) (a : Ioi (0 : ℝ)) (φ ψ : C(ℂ, ℝ))
    (z : ℂ) (c : ℝ)
    (hψ : ∀ u, ψ u = φ (u + z) - c) (p : ℂ × ℂ) :
    PfeWeyl.normalizedLFPPMetric ξ a ψ p =
      ENNReal.ofReal (Real.exp (-ξ * c)) *
        PfeWeyl.normalizedLFPPMetric ξ a φ
          (p.1 + z, p.2 + z) := by
  rw [PfeWeyl.normalizedLFPPMetric_apply,
    PfeWeyl.normalizedLFPPMetric_apply,
    B2.LscTop.lfppDistance_eq_lfppD,
    B2.LscTop.lfppDistance_eq_lfppD]
  have hφ : (ψ : ℂ → ℝ) = fun u => φ (z + u) + -c :=
    funext fun u => by rw [hψ u, add_comm]; ring
  have hC := lfppDOn_add_const ξ (fun u => φ (z + u))
    Set.univ (-c) p.1 p.2
  have hA := lfppDOn_affine ξ (φ : ℂ → ℝ)
    (S := Set.univ) (S' := Set.univ) (b := z) (c := 1)
    one_ne_zero (fun x => by simp) p.1 p.2
  simp only [one_mul, norm_one, ENNReal.ofReal_one] at hA
  simp only [LQGMetric.LFPP.lfppD, hφ, hC]
  rw [← hA]
  rw [show ξ * -c = -(ξ * c) by ring]
  rw [show -(ξ * c) = c * -ξ by ring]
  ac_rfl

end SupercriticalLQGUniqueness.B2.PfeAxioms
