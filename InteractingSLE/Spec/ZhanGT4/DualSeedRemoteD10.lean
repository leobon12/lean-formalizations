/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.ZhanGT4.DualSeedRemoteDet
import InteractingSLE.Spec.ZhanGT4.DualGirsanovFrozen

/-!
# The seeded drift cancellation and the image entrance integral

Packet PROVE-ZHAN-GT4-A22. The base force drift cancels the height-zero
part of the logarithmic derivative. Thus the mapped drift is exactly (D10).
Image-force integrability at the entrance is an explicit named condition;
`DualSeedRemoteEntrance` supplies it from the original seed equation. The
positive-time image equation then extends to zero by the ordinary
fundamental theorem of calculus.
-/

set_option autoImplicit false

noncomputable section

open Set Filter Topology MeasureTheory

namespace InteractingSLE.ZhanGT4

namespace SeedData

/-- The drift of the mapped driver in own time, as in (D10). -/
def d10Rate {n : ℕ} (s : SeedData n) (t : ℝ) : ℝ :=
  s.A 1 t ^ 2 * (-(s.κ / (2 * (s.A 0 t - s.A20 t))) +
    ∑ m, s.κ * s.r m / (s.A 0 t - s.B0 t m))

/-- Girsanov adds the difference of the two log-field drifts; the original
force drift supplies exactly the subtracted height-zero term. -/
theorem drift_add_kappa_mul_ellX {n : ℕ} (s : SeedData n) (t : ℝ) :
    s.drift t + s.κ * s.ellX t (s.W t) =
      s.κ * dualQ s.κ (s.A 1 t) (s.A 2 t) (s.A 0 t - s.A20 t) s.r
        (fun m => s.A 0 t - s.B0 t m) := by
  have hq : dualLogSpaceX s.κ s.r (s.A 0 t) (s.A 1 t) (s.A 2 t) (s.A20 t) (s.B0 t) =
      dualQ s.κ (s.A 1 t) (s.A 2 t) (s.A 0 t - s.A20 t) s.r
        (fun m => s.A 0 t - s.B0 t m) := by
    unfold dualLogSpaceX dualQ
    have he : ∀ x y : ℝ, x / (2 * y) = 1 / 2 * (x / y) := by intro x y; ring
    rw [he]
  simp only [drift, ellX, F_driver]
  rw [hq]
  ring

/-- **The seeded (D10) drift identity.** It has the same final drift as the
ordinary calculation; the singular own seed gaps have cancelled. -/
theorem d10_drift {n : ℕ} (s : SeedData n) {t : ℝ}
    (hκ : s.κ ≠ 0) (hA1 : s.A 1 t ≠ 0) :
    -3 * s.A 2 t + s.κ / 2 * s.A 2 t +
      (s.drift t + s.κ * s.ellX t (s.W t)) * s.A 1 t = s.d10Rate t := by
  rw [s.drift_add_kappa_mul_ellX]
  exact dualD10_drift s.r (fun m => s.A 0 t - s.B0 t m) hκ hA1

/-- The entrance integrability needed to pass the image force equations
from positive own times to the time axis. -/
def ImageEntranceIntegrable {n : ℕ} (s : SeedData n) (T : ℝ) : Prop :=
  ∀ m t, t ∈ Icc (0 : ℝ) T →
    IntervalIntegrable (fun u => 2 * s.A 1 u ^ 2 / (s.B0 u m - s.A 0 u)) volume 0 t

/-- The image force equation, including its seed entrance, from its checked
positive-time rate and the explicitly named entrance integrability input. -/
theorem integrated_image_marks {n : ℕ} (s : SeedData n) {T : ℝ}
    (hc : ∀ m, ContinuousOn (fun t => s.B0 t m) (Icc 0 T))
    (hd : ∀ m u, u ∈ Ioc (0 : ℝ) T →
      HasDerivWithinAt (fun t => s.B0 t m)
        (2 * s.A 1 u ^ 2 / (s.B0 u m - s.A 0 u)) (Ioc 0 T) u)
    (hi : s.ImageEntranceIntegrable T) :
    ∀ m t, t ∈ Icc (0 : ℝ) T → s.B0 t m = s.B0 0 m +
      ∫ u in (0 : ℝ)..t, 2 * s.A 1 u ^ 2 / (s.B0 u m - s.A 0 u) := by
  intro m t ht
  have he := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le ht.1
    ((hc m).mono (Icc_subset_Icc_right ht.2)) (fun u hu =>
      (hd m u ⟨hu.1, hu.2.le.trans ht.2⟩).hasDerivAt
        (Ioc_mem_nhds hu.1 (hu.2.trans_le ht.2))) (hi m t ht)
  linarith only [he]

end SeedData

end InteractingSLE.ZhanGT4
