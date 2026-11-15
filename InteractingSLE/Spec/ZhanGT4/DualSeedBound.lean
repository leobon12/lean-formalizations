/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.ZhanGT4.DualSeedField
import InteractingSLE.Spec.ZhanGT4.DualD11Seed
import InteractingSLE.Spec.ZhanGT4.MTildeBound

/-!
# The normalized seeded density on the time axis

Packet PROVE-ZHAN-GT4-A22. Astra's follow-up proofs, A.1.6, (D13)--(D15).
Divided differences cancel the own-chart gaps before they vanish. The normalized
logarithm agrees with `SeedData.ell` away from collisions and remains defined when
seed coordinates coincide. Its bounds use normalized factors, rather than the
individual gaps that vanish at the entrance time.
-/

set_option autoImplicit false

noncomputable section

open Set Filter Topology

namespace InteractingSLE.ZhanGT4

/-- The logarithmic form of the cancellation in (D14)--(D15). -/
theorem log_dslope_eq_sub {f : ℝ → ℝ} {u v : ℝ} (huv : v ≠ u)
    (hf : f v ≠ f u) :
    Real.log (dslope f u v) = Real.log (f v - f u) - Real.log (v - u) := by
  rw [dslope_of_ne _ huv, slope_def_field,
    Real.log_div (sub_ne_zero.2 hf) (sub_ne_zero.2 huv)]

namespace SeedData

variable {n : ℕ} (d : SeedData n)

/-- The normalized version of `ell t (W t)`. The divided differences include
their derivative values on the diagonal, as prescribed in (D14)--(D15). -/
def normEll (t : ℝ) : ℝ :=
  (3 * d.κ - 8) / 16 * Real.log (d.A21 t) - dualLambda d.κ * d.L t
    + (∑ m, (dualGamma d.κ (d.r m) * Real.log (d.B1 t m)
      + -(d.κ / 4) * d.r m * Real.log ((d.A20 t - d.B0 t m) / (d.V₀ t - d.V m t))))
    + pairSum (fun m k => dualDelta d.κ (d.r m) (d.r k)
      * Real.log (dslope (d.F 0 t) (d.V k t) (d.V m t)))
    + (dualAlpha d.κ * Real.log (d.A 1 t)
      - 1 / 2 * Real.log ((d.A 0 t - d.A20 t) / (d.W t - d.V₀ t))
      + ∑ m, d.r m * Real.log (dslope (d.F 0 t) (d.V m t) (d.W t)))

/-- Away from collisions the normalized formula is exactly the logarithm used
by the positive-time Itô calculation. -/
theorem normEll_eq_ell {t : ℝ}
    (h0 : d.A 0 t - d.A20 t ≠ 0) (hv0 : d.W t - d.V₀ t ≠ 0)
    (hm : ∀ m, d.A20 t - d.B0 t m ≠ 0)
    (hvm : ∀ m, d.V₀ t - d.V m t ≠ 0)
    (hWm : ∀ m, d.W t ≠ d.V m t)
    (hFm : ∀ m, d.A 0 t ≠ d.B0 t m)
    (hVmk : ∀ m k, m < k → d.V m t ≠ d.V k t)
    (hBmk : ∀ m k, m < k → d.B0 t m ≠ d.B0 t k) :
    d.normEll t = d.ell t (d.W t) := by
  have hds : ∀ m, Real.log (dslope (d.F 0 t) (d.V m t) (d.W t)) =
      Real.log (d.A 0 t - d.B0 t m) - Real.log (d.W t - d.V m t) :=
    fun m => log_dslope_eq_sub (hWm m) (hFm m)
  have hpair : pairSum (fun m k => dualDelta d.κ (d.r m) (d.r k)
        * Real.log (dslope (d.F 0 t) (d.V k t) (d.V m t))) =
      pairSum (fun m k => dualDelta d.κ (d.r m) (d.r k)
        * (Real.log (d.B0 t m - d.B0 t k) - Real.log (d.V m t - d.V k t))) := by
    unfold pairSum
    apply Finset.sum_congr rfl
    intro p hp
    have hlt := (Finset.mem_filter.1 hp).2
    dsimp only
    rw [log_dslope_eq_sub (hVmk p.1 p.2 hlt) (hBmk p.1 p.2 hlt)]
    rfl
  unfold normEll
  rw [hpair, Real.log_div h0 hv0]
  simp only [Real.log_div (hm _) (hvm _), hds]
  simp only [ell, LT, LT0, LS, LS0, dualLogTime, dualLogSpace, F_driver,
    Real.log_one, mul_zero, sub_zero, zero_add, Vv]
  simp only [mul_sub, Finset.sum_add_distrib, Finset.sum_sub_distrib, pairSum]
  ring

/-- A logarithmic bound for every normalized factor gives a bound independent
of the sizes of the own-chart seed gaps. -/
theorem abs_normEll_le_of_log_bounds {t L : ℝ} (hL : 0 ≤ L)
    (h21 : |Real.log (d.A21 t)| ≤ L) (hlogF : |d.L t| ≤ L)
    (hB1 : ∀ m, |Real.log (d.B1 t m)| ≤ L)
    (h2m : ∀ m, |Real.log ((d.A20 t - d.B0 t m) / (d.V₀ t - d.V m t))| ≤ L)
    (hmk : ∀ m k, m < k →
      |Real.log (dslope (d.F 0 t) (d.V k t) (d.V m t))| ≤ L)
    (h1 : |Real.log (d.A 1 t)| ≤ L)
    (h0 : |Real.log ((d.A 0 t - d.A20 t) / (d.W t - d.V₀ t))| ≤ L)
    (hm : ∀ m, |Real.log (dslope (d.F 0 t) (d.V m t) (d.W t))| ≤ L) :
    |d.normEll t| ≤ coefTot d.κ d.r * L := by
  have mulb : ∀ a x : ℝ, |x| ≤ L → |a * x| ≤ |a| * L := by
    intro a x hx
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_left hx (abs_nonneg a)
  have hb : |∑ m, (dualGamma d.κ (d.r m) * Real.log (d.B1 t m)
        + -(d.κ / 4) * d.r m *
          Real.log ((d.A20 t - d.B0 t m) / (d.V₀ t - d.V m t)))| ≤
      (∑ m, (|dualGamma d.κ (d.r m)| + |d.κ / 4 * d.r m|)) * L := by
    rw [Finset.sum_mul]
    apply (Finset.abs_sum_le_sum_abs _ _).trans
    apply Finset.sum_le_sum
    intro m _
    have h2 := mulb (-(d.κ / 4) * d.r m) _ (h2m m)
    rw [neg_mul, abs_neg] at h2
    calc
      _ ≤ |dualGamma d.κ (d.r m) * Real.log (d.B1 t m)|
          + |-(d.κ / 4) * d.r m *
            Real.log ((d.A20 t - d.B0 t m) / (d.V₀ t - d.V m t))| := abs_add_le _ _
      _ ≤ |dualGamma d.κ (d.r m)| * L + |d.κ / 4 * d.r m| * L :=
        add_le_add (mulb _ _ (hB1 m)) (by simpa only [neg_mul] using h2)
      _ = _ := by ring
  have hp : |pairSum (fun m k => dualDelta d.κ (d.r m) (d.r k)
      * Real.log (dslope (d.F 0 t) (d.V k t) (d.V m t)))| ≤
      pairSum (fun m k => |dualDelta d.κ (d.r m) (d.r k)|) * L := by
    rw [← pairSum_mul_const]
    exact abs_pairSum_le fun m k hmk' => mulb _ _ (hmk m k hmk')
  have hs := abs_sum_mul_le (r := d.r) hm
  have hspace : |dualAlpha d.κ * Real.log (d.A 1 t)
      - 1 / 2 * Real.log ((d.A 0 t - d.A20 t) / (d.W t - d.V₀ t))
      + ∑ m, d.r m * Real.log (dslope (d.F 0 t) (d.V m t) (d.W t))| ≤
      (|dualAlpha d.κ| + 1 / 2 + ∑ m, |d.r m|) * L := by
    have hh : |1 / 2 * Real.log ((d.A 0 t - d.A20 t) / (d.W t - d.V₀ t))|
        ≤ 1 / 2 * L := by
      simpa only [show |(1 / 2 : ℝ)| = 1 / 2 by norm_num] using mulb (1 / 2) _ h0
    calc
      _ ≤ (|dualAlpha d.κ * Real.log (d.A 1 t)|
          + |1 / 2 * Real.log ((d.A 0 t - d.A20 t) / (d.W t - d.V₀ t))|)
          + |∑ m, d.r m * Real.log (dslope (d.F 0 t) (d.V m t) (d.W t))| :=
        (abs_add_le _ _).trans (add_le_add (abs_sub _ _) le_rfl)
      _ ≤ (|dualAlpha d.κ| * L + 1 / 2 * L) + (∑ m, |d.r m|) * L :=
        add_le_add (add_le_add (mulb _ _ h1) hh) hs
      _ = _ := by ring
  have htime := (abs_sub ((3 * d.κ - 8) / 16 * Real.log (d.A21 t))
      (dualLambda d.κ * d.L t)).trans
    (add_le_add (mulb _ _ h21) (mulb _ _ hlogF))
  have htotal := (abs_add_le _ _).trans
    (add_le_add ((abs_add_le _ _).trans
      (add_le_add ((abs_add_le _ _).trans (add_le_add htime hb)) hp)) hspace)
  change |d.normEll t| ≤ _ at htotal
  apply htotal.trans
  unfold coefTot
  simp only [Finset.sum_add_distrib]
  nlinarith only [hL]

/-- The seeded (D9) estimate from bounds on its normalized factors. -/
theorem abs_normEll_le_of_inScale {t L : ℝ} (hL : 0 ≤ L)
    (h21 : InScale L (d.A21 t)) (hlogF : |d.L t| ≤ L)
    (hB1 : ∀ m, InScale L (d.B1 t m))
    (h2m : ∀ m, InScale L ((d.A20 t - d.B0 t m) / (d.V₀ t - d.V m t)))
    (hmk : ∀ m k, m < k → InScale L (dslope (d.F 0 t) (d.V k t) (d.V m t)))
    (h1 : InScale L (d.A 1 t))
    (h0 : InScale L ((d.A 0 t - d.A20 t) / (d.W t - d.V₀ t)))
    (hm : ∀ m, InScale L (dslope (d.F 0 t) (d.V m t) (d.W t))) :
    |d.normEll t| ≤ coefTot d.κ d.r * L :=
  d.abs_normEll_le_of_log_bounds hL (abs_log_le_of_inScale h21) hlogF
    (fun m => abs_log_le_of_inScale (hB1 m))
    (fun m => abs_log_le_of_inScale (h2m m))
    (fun m k hmk' => abs_log_le_of_inScale (hmk m k hmk'))
    (abs_log_le_of_inScale h1) (abs_log_le_of_inScale h0)
    (fun m => abs_log_le_of_inScale (hm m))

end SeedData

end InteractingSLE.ZhanGT4
