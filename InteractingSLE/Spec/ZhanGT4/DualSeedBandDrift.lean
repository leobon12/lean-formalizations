/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.ZhanGT4.DualSeedBandField

/-!
# The actual restarted drifted field is a regular band

Packet PROVE-ZHAN-GT4-A22. Absorb the drift, restart after the entrance,
and use Brownian spatial coordinates. This adapter proves all the
pathwise finite-pasting inputs from the landed drifted-field predicate.
-/

set_option autoImplicit false

noncomputable section

open Set Filter Topology MeasureTheory ProbabilityTheory
open scoped NNReal

namespace InteractingSLE.ZhanGT4

variable {Ω : Type*} {mΩ : MeasurableSpace Ω}

/-- The drift-absorbed logarithm in Brownian coordinates after `ε`. -/
def seedRestartLog (ℓ : Ω → ℝ → ℝ → ℝ) (σ : ℝ) (B D : ℝ≥0 → Ω → ℝ) (ε : ℝ≥0) :
    ℝ → Ω → ℝ → ℝ := fun u ω x => shiftField ℓ σ B D ε ω u (σ * x)

/-- Spatial derivatives of the restarted logarithm carry `σ^j`. -/
def seedRestartDeriv (j : ℕ) (ℓj : Ω → ℝ → ℝ → ℝ) (σ : ℝ)
    (B D : ℝ≥0 → Ω → ℝ) (ε : ℝ≥0) : ℝ → Ω → ℝ → ℝ :=
  fun u ω x => σ ^ j * shiftField ℓj σ B D ε ω u (σ * x)

/-- Its time derivative includes the force drift times `ℓ_x`. -/
def seedRestartTime (ℓx ℓt : Ω → ℝ → ℝ → ℝ) (b : Ω → ℝ → ℝ) (σ : ℝ)
    (B D : ℝ≥0 → Ω → ℝ) (ε : ℝ≥0) : ℝ → Ω → ℝ → ℝ :=
  fun u ω x => shiftFieldT ℓx ℓt b σ B D ε ω u (σ * x)

/-- The concrete restarted drifted log-field satisfies every analytic
input of the full moving-band pasting theorem. -/
theorem IsDriftLogField.seed_restarted_band
    {𝓕 : Filtration ℝ≥0 mΩ} {σ ρ K : ℝ} {B D : ℝ≥0 → Ω → ℝ}
    {b : Ω → ℝ → ℝ} {ε : ℝ≥0} {S : Ω → ℝ≥0}
    {ℓ ℓx ℓxx ℓxxx ℓt : Ω → ℝ → ℝ → ℝ}
    (h : IsDriftLogField 𝓕 σ ρ K B D b ε S ℓ ℓx ℓxx ℓxxx ℓt)
    (hB : ∀ ω, Continuous (B · ω)) (hσ : 0 < σ) (hρ : 0 < ρ) :
    SeedRegularBand (shiftBM B ε) (fun ω => S ω - ε)
      (seedRestartLog ℓ σ B D ε) (seedRestartDeriv 1 ℓx σ B D ε)
      (seedRestartDeriv 2 ℓxx σ B D ε) (seedRestartDeriv 3 ℓxxx σ B D ε)
      (seedRestartTime ℓx ℓt b σ B D ε) (ρ / σ)
      ((1 + σ + σ ^ 2 + σ ^ 3) * (K + K * K)) := by
  have hmul (x z : ℝ) (hx : |x - z| < 3 * (ρ / σ)) : |σ * x - σ * z| < 4 * ρ := by
    rw [← mul_sub, abs_mul, abs_of_pos hσ]
    have he : σ * (3 * (ρ / σ)) = 3 * ρ := by field_simp
    have hh := (mul_lt_mul_of_pos_left hx hσ).trans_eq he
    linarith
  have hmaps (ω : Ω) : MapsTo
      (fun p : ℝ × ℝ => ((ε : ℝ) + p.1, σ * p.2 + shiftOff σ B D ε ω p.1))
      (seedPathTube (fun u => shiftBM B ε u.toNNReal ω) 0 ((S ω - ε : ℝ≥0) : ℝ) (3 * (ρ / σ)))
      (driftTube σ B D ε (S ω) (4 * ρ) ω) := by
    intro p hp
    exact h.mem_tube hp.1 (hmul _ _ hp.2)
  have hcm (ω : Ω) : ContinuousOn
      (fun p : ℝ × ℝ => ((ε : ℝ) + p.1, σ * p.2 + shiftOff σ B D ε ω p.1))
      (seedPathTube (fun u => shiftBM B ε u.toNNReal ω) 0 ((S ω - ε : ℝ≥0) : ℝ) (3 * (ρ / σ))) :=
    (continuousOn_const.add continuousOn_fst).prodMk
      ((continuousOn_const.mul continuousOn_snd).add
        ((h.continuousOn_shiftOff ω).comp continuousOn_fst (fun _ hp => hp.1)))
  refine ⟨div_pos hρ hσ, by have := h.Knonneg; positivity, ?_, ?_, ?_, ?_, ?_⟩
  · intro ω a c y ha _ hc hy
    have hh := h.isLogField_shift hB hρ ω ha hc (y := σ * y) (fun u hu => by
      rw [← mul_sub, abs_mul, abs_of_pos hσ]
      have he : σ * (ρ / σ) = ρ := mul_div_cancel₀ _ hσ.ne'
      exact (mul_lt_mul_of_pos_left (hy u hu) hσ).trans_eq he)
    simpa only [seedRestartLog, seedRestartDeriv, seedRestartTime, pow_one] using hh.seed_scale hσ
  · intro ω
    exact (h.cont ω).comp (hcm ω) (hmaps ω)
  · intro ω
    exact continuousOn_const.mul ((h.contX ω).comp (hcm ω) (hmaps ω))
  · intro ω
    have ht := (h.contT ω).comp (hcm ω) (hmaps ω)
    have hx := (h.contX ω).comp (hcm ω) (hmaps ω)
    have hb : ContinuousOn (fun p : ℝ × ℝ => b ω ((ε : ℝ) + p.1))
        (seedPathTube (fun u => shiftBM B ε u.toNNReal ω) 0 ((S ω - ε : ℝ≥0) : ℝ)
          (3 * (ρ / σ))) :=
      (h.contb ω).comp (continuousOn_const.add continuousOn_fst)
        (fun p hp => h.mapsTo_add ω hp.1)
    exact ht.add (hb.mul hx)
  · intro ω
    exact continuousOn_const.mul ((h.contXX ω).comp (hcm ω) (hmaps ω))

end InteractingSLE.ZhanGT4
