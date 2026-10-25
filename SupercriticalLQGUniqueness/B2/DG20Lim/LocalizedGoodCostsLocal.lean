import SupercriticalLQGUniqueness.B2.DG20Lim.WiderAnnulusSupport

 


set_option autoImplicit false
noncomputable section

open Set
open scoped ENNReal
open LQGMetric LQGMetric.LFPP LQGMetric.Blueprint

namespace SupercriticalLQGUniqueness.B2.DG20Lim

theorem localized_annulus_costs_eq_of_restrictTo_eq
    (ξ : ℝ) (ε : Ioi (0 : ℝ))
    (x y r : ℚ) (hr : 0 < r)
    (hεr : Real.sqrt (ε : ℝ) < (r : ℝ) / 4)
    {g g' : DistC}
    (he : restrictTo (widerCenteredAnnulus x y r) g =
      restrictTo (widerCenteredAnnulus x y r) g') :
    (lfppContMetric ξ (LQGMetric.DFGPS.L217.locMollifyC (ε : ℝ) ε.property g)
      (LQGMetric.DFGPS.L217.locMollifyC (ε : ℝ) ε.property g).continuous).aroundDist
        (centeredRatAnnulus x y r hr).toSet
        (centeredInnerCircle x y r hr).toSet
        (centeredOuterCircle x y r hr).toSet =
      (lfppContMetric ξ (LQGMetric.DFGPS.L217.locMollifyC (ε : ℝ) ε.property g')
      (LQGMetric.DFGPS.L217.locMollifyC (ε : ℝ) ε.property g').continuous).aroundDist
        (centeredRatAnnulus x y r hr).toSet
        (centeredInnerCircle x y r hr).toSet
        (centeredOuterCircle x y r hr).toSet ∧
    setDist (lfppContMetric ξ
      (LQGMetric.DFGPS.L217.locMollifyC (ε : ℝ) ε.property g)
      (LQGMetric.DFGPS.L217.locMollifyC (ε : ℝ) ε.property g).continuous)
        (centeredInnerCircle x y r hr).toSet
        (centeredOuterCircle x y r hr).toSet =
      setDist (lfppContMetric ξ
      (LQGMetric.DFGPS.L217.locMollifyC (ε : ℝ) ε.property g')
      (LQGMetric.DFGPS.L217.locMollifyC (ε : ℝ) ε.property g').continuous)
        (centeredInnerCircle x y r hr).toSet
        (centeredOuterCircle x y r hr).toSet := by
  let φ := LQGMetric.DFGPS.L217.locMollifyC (ε : ℝ) ε.property g
  let ψ := LQGMetric.DFGPS.L217.locMollifyC (ε : ℝ) ε.property g'
  let V : Set ℂ := bufferedCenteredAnnulus x y r
  let A := (centeredRatAnnulus x y r hr).toSet
  let E := (centeredInnerCircle x y r hr).toSet
  let F := (centeredOuterCircle x y r hr).toSet
  have heq : ∀ z w : V, lfppDOn ξ φ V z w = lfppDOn ξ ψ V z w := by
    intro z w
    exact localizedLFPP_buffered_congr ξ ε x y r hr hεr he z w
  have h0 : (1 : ℝ≥0∞) ≠ 0 := by norm_num
  have ht : (1 : ℝ≥0∞) ≠ ∞ := by norm_num
  have hAV : A ⊆ V := centeredRatAnnulus_subset_buffered x y r hr
  have hAround : (lfppContMetric ξ φ φ.continuous).aroundDist A E F =
      (lfppContMetric ξ ψ ψ.continuous).aroundDist A E F := by
    apply le_antisymm
    · simpa only [one_mul] using
        lfppAroundDist_le_mul_of_lfppDOn_le ξ ψ φ V A E F
          (bufferedCenteredAnnulus x y r).isOpen hAV 1 h0 ht
          (fun z w => by simpa only [one_mul] using (heq z w).le)
    · simpa only [one_mul] using
        lfppAroundDist_le_mul_of_lfppDOn_le ξ φ ψ V A E F
          (bufferedCenteredAnnulus x y r).isOpen hAV 1 h0 ht
          (fun z w => by simpa only [one_mul] using (heq z w).ge)
  let c : ℂ := Complex.mk (x : ℝ) (y : ℝ)
  have hrR : (0 : ℝ) < (r : ℝ) := by exact_mod_cast hr
  have hρ : (r : ℝ) < 2 * (r : ℝ) := by linarith
  have hCircle : setDist (lfppContMetric ξ φ φ.continuous) E F =
      setDist (lfppContMetric ξ ψ ψ.continuous) E F := by
    have hle := lfppCircleSetDist_le_mul_of_lfppDOn_le ξ ψ φ
      V (bufferedCenteredAnnulus x y r).isOpen c
      (r : ℝ) (2 * (r : ℝ)) hρ
      (centered_shell_subset_buffered x y r hr) 1 h0 ht
      (fun z w => by simpa only [one_mul] using (heq z w).le)
    have hge := lfppCircleSetDist_le_mul_of_lfppDOn_le ξ φ ψ
      V (bufferedCenteredAnnulus x y r).isOpen c
      (r : ℝ) (2 * (r : ℝ)) hρ
      (centered_shell_subset_buffered x y r hr) 1 h0 ht
      (fun z w => by simpa only [one_mul] using (heq z w).ge)
    apply le_antisymm
    · simpa [E, F, RatCircle.toSet, RatCircle.center,
        centeredInnerCircle, centeredOuterCircle, c, mul_comm] using hle
    · simpa [E, F, RatCircle.toSet, RatCircle.center,
        centeredInnerCircle, centeredOuterCircle, c, mul_comm] using hge
  exact ⟨hAround, hCircle⟩

end SupercriticalLQGUniqueness.B2.DG20Lim
