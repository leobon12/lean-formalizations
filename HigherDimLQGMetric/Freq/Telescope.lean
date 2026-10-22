import HigherDimLQGMetric.Freq.MacroTimes

/-! The deterministic telescoping implication in Proposition 5.4. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace HigherDimLQGMetric

open Set
open HigherDimLFPP (Rd)

variable {d : ℕ}

private theorem s4c_far_center {x p z : Rd d} {r rmax : ℝ}
    (hr : 0 ≤ r) (hrmax : r ≤ rmax)
    (hfar : 4 * rmax ≤ ‖p - x‖) (hnear : ‖p - z‖ < r / 2) :
    2 * r ≤ ‖x - z‖ := by
  have htri : ‖p - x‖ ≤ ‖p - z‖ + ‖x - z‖ := by
    calc
      ‖p - x‖ = ‖(p - z) + (z - x)‖ := by congr 1; abel
      _ ≤ ‖p - z‖ + ‖z - x‖ := norm_add_le _ _
      _ = ‖p - z‖ + ‖x - z‖ := by
        rw [show ‖z - x‖ = ‖x - z‖ from norm_sub_rev _ _]
  linarith only [htri, hfar, hnear, hrmax, hr]

/-- On an arclength geodesic, good shells along the middle part produce a
global improved ratio, up to the two short endpoint segments. The last shell
may overshoot the first entrance near `y`; arclength makes the remainder even
shorter, so no terminal shell trace is needed. -/
theorem s4c_telescope
    (A B : DistRd d → ContMetric d) (ξ Q U a A₀ ℓ β₀ t : ℝ)
    (g : DistRd d) (hℓ : 0 < ℓ) (hℓa : ℓ < a / 100)
    (hA₀ : 0 < A₀) (ht : 0 ≤ t) (htU : t ≤ U)
    (hA : (A g).IsLength)
    (hratio : ∀ x y : Rd d, (B g).1 (x, y) ≤ U * (A g).1 (x, y))
    (P : ℝ → Rd d) (x y : Rd d) {L a₀ b₀ rmin rmax M : ℝ}
    (hP0 : P 0 = x) (hPL : P L = y)
    (ha0 : 0 ≤ a₀) (hab : a₀ ≤ b₀) (hbL : b₀ ≤ L)
    (hPc : ContinuousOn P (Icc 0 L))
    (hunit : ∀ s ∈ Icc 0 L, ∀ v ∈ Icc 0 L, s ≤ v →
      (A g).len P s v = ENNReal.ofReal (v - s) ∧
      (A g).1 (P s, P v) = v - s)
    (hrmin : 0 < rmin)
    (hfar : ∀ s ∈ Ico a₀ b₀,
      4 * rmax ≤ ‖P s - x‖ ∧ 4 * rmax ≤ ‖P s - y‖)
    (hcover : ∀ s ∈ Ico a₀ b₀, ∃ r : ℝ, ∃ z : Rd d,
      rmin ≤ r ∧ r ≤ rmax ∧ ‖P s - z‖ < r / 2 ∧
      g ∈ RegEvent A B ξ Q U a A₀ ℓ β₀ r z \
        WitEvent A B ξ Q U a A₀ ℓ β₀ t r z)
    (hM : 0 ≤ M) (hfirst : a₀ ≤ M) (hlast : L - b₀ ≤ M)
    (hK0 : 0 ≤ U - a / A₀ * (U - t)) :
    (B g).1 (x, y) ≤
      (U - a / A₀ * (U - t)) * L + 2 * U * M := by
  let K := U - a / A₀ * (U - t)
  have hU : 0 ≤ U := ht.trans htU
  have ha : 0 < a := by nlinarith only [hℓ, hℓa]
  have hfrac : 0 ≤ a / A₀ := div_nonneg ha.le hA₀.le
  have hKle : K ≤ U := by
    dsimp [K]
    exact sub_le_self _ (mul_nonneg hfrac (sub_nonneg.mpr htU))
  obtain ⟨δ, hδ, hadvance⟩ := s4c_time_advance_of_spatial P hPc
    (show 0 < rmin / 2 by positivity)
  have hstep : ∀ s ∈ Ico a₀ b₀, ∃ e ∈ Ioc s L,
      δ ≤ e - s ∧ (B g).1 (P s, P e) ≤ K * (e - s) := by
    intro s hs
    obtain ⟨r, z, hrmin', hrmax', hnear, hgood⟩ := hcover s hs
    have hr : 0 < r := hrmin.trans_le hrmin'
    have hsI : s ∈ Icc 0 L := ⟨ha0.trans hs.1, hs.2.le.trans hbL⟩
    have h0far : 2 * r ≤ ‖P 0 - z‖ := by
      rw [hP0]
      exact s4c_far_center hr.le hrmax' ((hfar s hs).1) hnear
    have hLfar : 2 * r ≤ ‖P L - z‖ := by
      rw [hPL]
      exact s4c_far_center hr.le hrmax' ((hfar s hs).2) hnear
    obtain ⟨e, he, _, hspatial, hBe⟩ :=
      s4c_frequency_step A B ξ Q U a A₀ ℓ β₀ t r z g hr hℓ hℓa
        hA₀ ht htU hA hgood.1 hgood.2 hratio P hsI hPc hunit
        h0far hLfar hnear
    refine ⟨e, he, ?_, hBe⟩
    have heI : e ∈ Icc 0 L := ⟨ha0.trans (hs.1.trans he.1.le), he.2⟩
    exact hadvance s hsI e heI he.1.le (le_trans (by linarith : rmin / 2 ≤ r / 2) hspatial)
  obtain ⟨e, he, hBe⟩ := s4c_iterate (B g) P hab hbL hδ hstep
  have h0I : (0 : ℝ) ∈ Icc 0 L := ⟨le_rfl, ha0.trans (hab.trans hbL)⟩
  have haI : a₀ ∈ Icc 0 L := ⟨ha0, hab.trans hbL⟩
  have heI : e ∈ Icc 0 L := ⟨ha0.trans (hab.trans he.1), he.2⟩
  have hLI : L ∈ Icc 0 L := ⟨h0I.2, le_rfl⟩
  have hBa : (B g).1 (x, P a₀) ≤ U * a₀ := by
    have hA0 : (A g).1 (P 0, P a₀) = a₀ := by
      simpa only [sub_zero] using (hunit 0 h0I a₀ haI ha0).2
    calc
      (B g).1 (x, P a₀) = (B g).1 (P 0, P a₀) := by rw [hP0]
      _ ≤ U * (A g).1 (P 0, P a₀) := hratio _ _
      _ = U * a₀ := by rw [hA0]
  have hBy : (B g).1 (P e, y) ≤ U * (L - e) := by
    rw [← hPL, ← (hunit e heI L hLI he.2).2]
    exact hratio _ _
  have htail : 0 ≤ L - e ∧ L - e ≤ M := by
    constructor
    · linarith only [he.2]
    · linarith only [he.1, hlast]
  have hsum : a₀ + (L - e) ≤ 2 * M := by linarith only [hfirst, htail.2]
  have hK0' : 0 ≤ K := hK0
  have hprod : (U - K) * (a₀ + (L - e)) ≤ U * (2 * M) := by
    have h1 := mul_le_mul_of_nonneg_left hsum (sub_nonneg.mpr hKle)
    have h2 := mul_le_mul_of_nonneg_right
      (show U - K ≤ U by linarith only [hK0'])
      (show 0 ≤ 2 * M by linarith only [hM])
    exact h1.trans h2
  have hbound : U * a₀ + K * (e - a₀) + U * (L - e) ≤ K * L + 2 * U * M := by
    calc
      U * a₀ + K * (e - a₀) + U * (L - e) =
          K * L + (U - K) * (a₀ + (L - e)) := by ring
      _ ≤ K * L + U * (2 * M) := by
        simpa only [add_comm] using (add_le_add_left hprod (K * L))
      _ = K * L + 2 * U * M := by ring
  have htri1 := (B g).2.triangle x (P a₀) (P e)
  have htri2 := (B g).2.triangle x (P e) y
  dsimp [K] at hbound
  linarith only [htri1, htri2, hBa, hBe, hBy, hbound]

end HigherDimLQGMetric
