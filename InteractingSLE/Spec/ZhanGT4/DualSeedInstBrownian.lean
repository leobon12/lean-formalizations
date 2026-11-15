/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.ZhanGT4.DualSeedRowIdEight
import Mathlib.Probability.Process.Stopping

/-!
# The actual drift decomposition of a stopped Brownian source driver

Packet PROVE-ZHAN-GT4-A22. The original Brownian motion is retained.
The continuous adapted drift compensates the stopped driver after its exit;
its derivative on the entire closed protected prefix is zero.
-/

set_option autoImplicit false
noncomputable section
open Set Filter Topology MeasureTheory ProbabilityTheory
open scoped NNReal
namespace InteractingSLE.ZhanGT4
variable {Ω : Type*} {mΩ : MeasurableSpace Ω}

/-- The actual stopped original driver, translated to its physical source. -/
def seedStoppedDriver (σ p : ℝ) (B : ℝ≥0 → Ω → ℝ) (T : Ω → ℝ≥0) (ω : Ω) (t : ℝ) : ℝ :=
  σ * B (min t.toNNReal (T ω)) ω + p

/-- The original Brownian compensation after the protected stop. -/
def seedStoppedDrift (σ : ℝ) (B : ℝ≥0 → Ω → ℝ) (T : Ω → ℝ≥0) (t : ℝ≥0) (ω : Ω) : ℝ :=
  σ * (B (min t (T ω)) ω - B t ω)

/-- Literal zero compensation throughout the stopped prefix. -/
theorem seedStoppedDrift_eq_zero {σ : ℝ} {B : ℝ≥0 → Ω → ℝ} {T : Ω → ℝ≥0}
    {t : ℝ≥0} {ω : Ω} (ht : t ≤ T ω) : seedStoppedDrift σ B T t ω = 0 := by
  simp only [seedStoppedDrift, min_eq_left ht, sub_self, mul_zero]

/-- The globally stopped driver has the actual original Brownian plus
adapted-drift form, without stopping the Brownian noise in that decomposition. -/
theorem seedStoppedDriver_eq_driftDriver (σ p : ℝ) (B : ℝ≥0 → Ω → ℝ) (T : Ω → ℝ≥0) (ω : Ω) :
    (fun t => seedStoppedDriver σ p B T ω t - p) = driftDriver σ B (seedStoppedDrift σ B T) ω := by
  funext t
  simp only [seedStoppedDriver, driftDriver, seedStoppedDrift]
  ring

/-- The compensation is adapted in the actual original filtration. -/
theorem measurable_seedStoppedDrift {𝓕 : Filtration ℝ≥0 mΩ} {B : ℝ≥0 → Ω → ℝ}
    (hB : Adapted 𝓕 B) (hBc : ∀ ω, Continuous (B · ω)) {T : Ω → ℝ≥0}
    (hT : IsStoppingTime 𝓕 fun ω => (T ω : WithTop ℝ≥0)) (σ : ℝ) (t : ℝ≥0) :
    Measurable[𝓕 t] (seedStoppedDrift σ B T t) := by
  have hs := (hB.stronglyAdapted.stoppedProcess hBc hT).adapted t
  have hm : Measurable[𝓕 t] fun ω => B (min t (T ω)) ω := by
    have he : stoppedProcess B (fun ω => (T ω : WithTop ℝ≥0)) t =
        fun ω => B (min t (T ω)) ω := by
      funext ω
      simp only [stoppedProcess, ← WithTop.coe_min]
      rfl
    rw [he] at hs
    exact hs
  exact measurable_const.mul (hm.sub (hB t))

/-- The compensation has continuous paths. -/
theorem continuous_seedStoppedDrift {B : ℝ≥0 → Ω → ℝ} (hBc : ∀ ω, Continuous (B · ω))
    (σ : ℝ) (T : Ω → ℝ≥0) (ω : Ω) : Continuous fun t => seedStoppedDrift σ B T t ω :=
  continuous_const.mul (((hBc ω).comp (continuous_id.min continuous_const)).sub (hBc ω))

/-- The stopped source driver is globally continuous as a real-time driver. -/
theorem continuous_seedStoppedDriver {B : ℝ≥0 → Ω → ℝ} (hBc : ∀ ω, Continuous (B · ω))
    (σ p : ℝ) (T : Ω → ℝ≥0) (ω : Ω) : Continuous (seedStoppedDriver σ p B T ω) :=
  (continuous_const.mul ((hBc ω).comp (continuous_real_toNNReal.min continuous_const))).add continuous_const

/-- The true derivative of the adapted compensation is zero on the closed
protected prefix, including its two endpoints. -/
theorem hasDerivWithinAt_seedStoppedDrift {B : ℝ≥0 → Ω → ℝ} (σ : ℝ) (T : Ω → ℝ≥0)
    (ω : Ω) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) (T ω)) :
    HasDerivWithinAt (fun u : ℝ => seedStoppedDrift σ B T u.toNNReal ω) 0 (Icc (0 : ℝ) (T ω)) t := by
  refine (hasDerivWithinAt_const t (Icc (0 : ℝ) (T ω)) (0 : ℝ)).congr_of_mem ?_ ht
  intro u hu
  exact seedStoppedDrift_eq_zero (Real.toNNReal_le_iff_le_coe.2 hu.2)

end InteractingSLE.ZhanGT4
