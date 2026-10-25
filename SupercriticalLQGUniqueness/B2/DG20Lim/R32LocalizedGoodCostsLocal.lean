import SupercriticalLQGUniqueness.B2.DG20Lim.R32WiderAnnulusSupport

 




set_option autoImplicit false
noncomputable section

open Set
open scoped ENNReal
open LQGMetric LQGMetric.LFPP LQGMetric.Blueprint

namespace SupercriticalLQGUniqueness.B2.DG20Lim

theorem localized_annulus_costs_eq_of_restrictTo_eqR32
    (ξ : ℝ) (ε : Ioi (0 : ℝ))
    (x y r : ℚ) (hr : 0 < r)
    (hεr : Real.sqrt (ε : ℝ) < (r : ℝ) / 4)
    {g g' : DistC}
    (he : restrictTo (widerCenteredAnnulusR32 x y r) g =
      restrictTo (widerCenteredAnnulusR32 x y r) g') :
    (lfppContMetric ξ (LQGMetric.DFGPS.L217.locMollifyC (ε : ℝ) ε.property g)
      (LQGMetric.DFGPS.L217.locMollifyC (ε : ℝ) ε.property g).continuous).aroundDist
        (centeredRatAnnulusR32 x y r hr).toSet
        (centeredInnerCircleR32 x y r hr).toSet
        (centeredOuterCircleR32 x y r hr).toSet =
      (lfppContMetric ξ (LQGMetric.DFGPS.L217.locMollifyC (ε : ℝ) ε.property g')
      (LQGMetric.DFGPS.L217.locMollifyC (ε : ℝ) ε.property g').continuous).aroundDist
        (centeredRatAnnulusR32 x y r hr).toSet
        (centeredInnerCircleR32 x y r hr).toSet
        (centeredOuterCircleR32 x y r hr).toSet ∧
    setDist (lfppContMetric ξ
      (LQGMetric.DFGPS.L217.locMollifyC (ε : ℝ) ε.property g)
      (LQGMetric.DFGPS.L217.locMollifyC (ε : ℝ) ε.property g).continuous)
        (centeredInnerCircleR32 x y r hr).toSet
        (centeredOuterCircleR32 x y r hr).toSet =
      setDist (lfppContMetric ξ
      (LQGMetric.DFGPS.L217.locMollifyC (ε : ℝ) ε.property g')
      (LQGMetric.DFGPS.L217.locMollifyC (ε : ℝ) ε.property g').continuous)
        (centeredInnerCircleR32 x y r hr).toSet
        (centeredOuterCircleR32 x y r hr).toSet := by
  let φ := LQGMetric.DFGPS.L217.locMollifyC (ε : ℝ) ε.property g
  let ψ := LQGMetric.DFGPS.L217.locMollifyC (ε : ℝ) ε.property g'
  let V : Set ℂ := bufferedCenteredAnnulusR32 x y r
  let A := (centeredRatAnnulusR32 x y r hr).toSet
  let E := (centeredInnerCircleR32 x y r hr).toSet
  let F := (centeredOuterCircleR32 x y r hr).toSet
  have heq : ∀ z w : V, lfppDOn ξ φ V z w = lfppDOn ξ ψ V z w := by
    intro z w
    exact localizedLFPP_buffered_congrR32 ξ ε x y r hr hεr he z w
  have h0 : (1 : ℝ≥0∞) ≠ 0 := by norm_num
  have ht : (1 : ℝ≥0∞) ≠ ∞ := by norm_num
  have hAV : A ⊆ V := centeredRatAnnulus_subset_bufferedR32 x y r hr
  have hAround : (lfppContMetric ξ φ φ.continuous).aroundDist A E F =
      (lfppContMetric ξ ψ ψ.continuous).aroundDist A E F := by
    apply le_antisymm
    · simpa only [one_mul] using
        lfppAroundDist_le_mul_of_lfppDOn_le ξ ψ φ V A E F
          (bufferedCenteredAnnulusR32 x y r).isOpen hAV 1 h0 ht
          (fun z w => by simpa only [one_mul] using (heq z w).le)
    · simpa only [one_mul] using
        lfppAroundDist_le_mul_of_lfppDOn_le ξ φ ψ V A E F
          (bufferedCenteredAnnulusR32 x y r).isOpen hAV 1 h0 ht
          (fun z w => by simpa only [one_mul] using (heq z w).ge)
  let c : ℂ := Complex.mk (x : ℝ) (y : ℝ)
  have hrR : (0 : ℝ) < (r : ℝ) := by exact_mod_cast hr
  have hρ : (r : ℝ) < 3 / 2 * (r : ℝ) := by linarith
  have hCircle : setDist (lfppContMetric ξ φ φ.continuous) E F =
      setDist (lfppContMetric ξ ψ ψ.continuous) E F := by
    have hle := lfppCircleSetDist_le_mul_of_lfppDOn_le ξ ψ φ
      V (bufferedCenteredAnnulusR32 x y r).isOpen c
      (r : ℝ) (3 / 2 * (r : ℝ)) hρ
      (centered_shell_subset_bufferedR32 x y r hr) 1 h0 ht
      (fun z w => by simpa only [one_mul] using (heq z w).le)
    have hge := lfppCircleSetDist_le_mul_of_lfppDOn_le ξ φ ψ
      V (bufferedCenteredAnnulusR32 x y r).isOpen c
      (r : ℝ) (3 / 2 * (r : ℝ)) hρ
      (centered_shell_subset_bufferedR32 x y r hr) 1 h0 ht
      (fun z w => by simpa only [one_mul] using (heq z w).ge)
    apply le_antisymm
    · simpa [E, F, RatCircle.toSet, RatCircle.center,
        centeredInnerCircleR32, centeredOuterCircleR32, c, mul_comm] using hle
    · simpa [E, F, RatCircle.toSet, RatCircle.center,
        centeredInnerCircleR32, centeredOuterCircleR32, c, mul_comm] using hge
  exact ⟨hAround, hCircle⟩

end SupercriticalLQGUniqueness.B2.DG20Lim
