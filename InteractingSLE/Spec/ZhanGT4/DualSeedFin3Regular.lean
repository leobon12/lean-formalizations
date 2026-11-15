/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.ZhanGT4.DualSeedFin2Finite
import InteractingSLE.Spec.ZhanGT4.DualSeedFin2Drift

/-!
# Regular drifted fields without a martingale generator condition

Packet PROVE-ZHAN-GT4-A22. The reflected map has its D10 generator rather
than a zero exponential generator. Retain exactly the analytic drifted
field assumptions and reuse the existing coordinate-change geometry.
-/

set_option autoImplicit false

noncomputable section

open Set Filter Topology MeasureTheory ProbabilityTheory
open scoped NNReal

namespace InteractingSLE.ZhanGT4

variable {Ω : Type*} {mΩ : MeasurableSpace Ω}

/-- A regular field on a drifted-driver tube. Its generator is unrestricted;
these analytic properties will be proved for the actual reflected map. -/
structure IsSeedDriftField (σ ρ K : ℝ) (B D : ℝ≥0 → Ω → ℝ) (b : Ω → ℝ → ℝ)
    (ε : ℝ≥0) (S : Ω → ℝ≥0) (ℓ ℓx ℓxx ℓxxx ℓt : Ω → ℝ → ℝ → ℝ) : Prop where
  le : ∀ ω, ε ≤ S ω
  Knonneg : 0 ≤ K
  dD : ∀ ω, ∀ t ∈ Icc (ε : ℝ) (S ω),
    HasDerivWithinAt (fun s : ℝ => D s.toNNReal ω) (b ω t) (Icc (ε : ℝ) (S ω)) t
  contb : ∀ ω, ContinuousOn (b ω) (Icc (ε : ℝ) (S ω))
  bound_b : ∀ ω, ∀ t ∈ Icc (ε : ℝ) (S ω), |b ω t| ≤ K
  dx : ∀ ω, ∀ p ∈ driftTube σ B D ε (S ω) (4 * ρ) ω, HasDerivAt (ℓ ω p.1) (ℓx ω p.1 p.2) p.2
  dxx : ∀ ω, ∀ p ∈ driftTube σ B D ε (S ω) (4 * ρ) ω, HasDerivAt (ℓx ω p.1) (ℓxx ω p.1 p.2) p.2
  dxxx : ∀ ω, ∀ p ∈ driftTube σ B D ε (S ω) (4 * ρ) ω, HasDerivAt (ℓxx ω p.1) (ℓxxx ω p.1 p.2) p.2
  dt : ∀ ω, ∀ p ∈ driftTube σ B D ε (S ω) (4 * ρ) ω,
    HasDerivWithinAt (fun s => ℓ ω s p.2) (ℓt ω p.1 p.2) (Icc (ε : ℝ) (S ω)) p.1
  cont : ∀ ω, ContinuousOn (fun p : ℝ × ℝ => ℓ ω p.1 p.2) (driftTube σ B D ε (S ω) (4 * ρ) ω)
  contX : ∀ ω, ContinuousOn (fun p : ℝ × ℝ => ℓx ω p.1 p.2) (driftTube σ B D ε (S ω) (4 * ρ) ω)
  contXX : ∀ ω, ContinuousOn (fun p : ℝ × ℝ => ℓxx ω p.1 p.2) (driftTube σ B D ε (S ω) (4 * ρ) ω)
  contT : ∀ ω, ContinuousOn (fun p : ℝ × ℝ => ℓt ω p.1 p.2) (driftTube σ B D ε (S ω) (4 * ρ) ω)
  bound : ∀ ω, ∀ p ∈ driftTube σ B D ε (S ω) (4 * ρ) ω, |ℓ ω p.1 p.2| ≤ K ∧ |ℓx ω p.1 p.2| ≤ K ∧
    |ℓxx ω p.1 p.2| ≤ K ∧ |ℓxxx ω p.1 p.2| ≤ K ∧ |ℓt ω p.1 p.2| ≤ K

namespace IsSeedDriftField

variable {σ ρ K : ℝ} {B D : ℝ≥0 → Ω → ℝ} {b : Ω → ℝ → ℝ}
  {ε : ℝ≥0} {S : Ω → ℝ≥0} {ℓ ℓx ℓxx ℓxxx ℓt : Ω → ℝ → ℝ → ℝ}
  (h : IsSeedDriftField σ ρ K B D b ε S ℓ ℓx ℓxx ℓxxx ℓt)

include h

/-- The constant log field retains the drift data and makes the existing
shift geometry available without imposing any condition on the map's generator. -/
theorem zero_logField (𝓕 : Filtration ℝ≥0 mΩ) :
    IsDriftLogField 𝓕 σ ρ K B D b ε S (fun _ _ _ => 0) (fun _ _ _ => 0)
      (fun _ _ _ => 0) (fun _ _ _ => 0) (fun _ _ _ => 0) where
  le := h.le
  Knonneg := h.Knonneg
  dD := h.dD
  contb := h.contb
  bound_b := h.bound_b
  dx := fun _ _ _ => hasDerivAt_const _ _
  dxx := fun _ _ _ => hasDerivAt_const _ _
  dxxx := fun _ _ _ => hasDerivAt_const _ _
  dt := fun _ _ _ => hasDerivWithinAt_const _ _ _
  cont := fun _ => continuousOn_const
  contX := fun _ => continuousOn_const
  contXX := fun _ => continuousOn_const
  contT := fun _ => continuousOn_const
  bound := fun _ _ _ => ⟨by simpa only [abs_zero] using h.Knonneg,
    by simpa only [abs_zero] using h.Knonneg, by simpa only [abs_zero] using h.Knonneg,
    by simpa only [abs_zero] using h.Knonneg, by simpa only [abs_zero] using h.Knonneg⟩
  gen := fun _ _ _ => by simp only [mul_zero, zero_pow two_ne_zero, add_zero]
  meas0 := fun _ _ => by
    convert measurable_const (a := (0 : ℝ)) using 1
    exact Set.indicator_zero ℝ _
  meas1 := fun _ _ => by
    convert measurable_const (a := (0 : ℝ)) using 1
    exact Set.indicator_zero ℝ _
  meas2 := fun _ _ => by
    convert measurable_const (a := (0 : ℝ)) using 1
    exact Set.indicator_zero ℝ _

/-- The actual regular field absorbs its finite-variation offset. -/
theorem isLogField_shift (𝓕 : Filtration ℝ≥0 mΩ) (hBc : ∀ ω, Continuous (B · ω))
    (hρ : 0 < ρ) (ω : Ω) {bb c y : ℝ} (hb : 0 ≤ bb)
    (hc : c ≤ ((S ω - ε : ℝ≥0) : ℝ)) (hy : ∀ r ∈ Icc bb c, |σ * shiftBM B ε r.toNNReal ω - y| < ρ) :
    IsLogField (shiftField ℓ σ B D ε ω) (shiftField ℓx σ B D ε ω) (shiftField ℓxx σ B D ε ω)
      (shiftField ℓxxx σ B D ε ω) (shiftFieldT ℓx ℓt b σ B D ε ω) bb c y ρ (K + K * K) := by
  have hC := h.zero_logField 𝓕
  have hK := h.Knonneg
  have hsub : Icc bb c ⊆ Icc 0 ((S ω - ε : ℝ≥0) : ℝ) := Icc_subset_Icc hb hc
  -- points of the box are near the shifted driver
  have hnear : ∀ t ∈ Icc bb c, ∀ x, |x - y| < 3 * ρ → |x - σ * shiftBM B ε t.toNNReal ω| < 4 * ρ :=
    fun t ht x hx => by
      have h1 := hy t ht
      calc |x - σ * shiftBM B ε t.toNNReal ω| ≤ |x - y| + |y - σ * shiftBM B ε t.toNNReal ω| := abs_sub_le _ _ _
        _ < 3 * ρ + ρ := by rw [abs_sub_comm y]; exact add_lt_add hx h1
        _ = 4 * ρ := by ring
  have hmem : ∀ t ∈ Icc bb c, ∀ x, |x - y| < 3 * ρ →
      ((ε : ℝ) + t, x + shiftOff σ B D ε ω t) ∈ driftTube σ B D ε (S ω) (4 * ρ) ω :=
    fun t ht x hx => hC.mem_tube (hsub ht) (hnear t ht x hx)
  have hmaps : MapsTo (fun p : ℝ × ℝ => ((ε : ℝ) + p.1, p.2 + shiftOff σ B D ε ω p.1))
      (Icc bb c ×ˢ {x | |x - y| < 3 * ρ}) (driftTube σ B D ε (S ω) (4 * ρ) ω) :=
    fun p hp => hmem p.1 hp.1 p.2 hp.2
  have hcm := hC.continuousOn_shiftMap (σ := σ) hsub {x | |x - y| < 3 * ρ}
  -- the drifted driver at the shifted point
  have hdrv : ∀ t ∈ Icc bb c, ∀ x, |x - y| < 3 * ρ →
      |x + shiftOff σ B D ε ω t - driftDriver σ B D ω (ε + t)| < 4 * ρ := fun t ht x hx => (hmem t ht x hx).2
  refine ⟨hρ, by positivity, fun t ht x hx => ?_, fun t ht x hx => ?_, fun t ht x hx => ?_, fun t ht x hx => ?_,
    ?_, ?_, ?_, ?_, fun t ht x hx => ?_⟩
  · exact HasDerivAt.comp_add_const x _ (h.dx ω _ (hmem t ht x hx))
  · exact HasDerivAt.comp_add_const x _ (h.dxx ω _ (hmem t ht x hx))
  · exact HasDerivAt.comp_add_const x _ (h.dxxx ω _ (hmem t ht x hx))
  · -- the chain rule along the moving point `x + σB_ε + D_{ε+u}`
    set v : ℝ → ℝ := fun u => x + shiftOff σ B D ε ω u with hv
    have hmt := hmem t ht x hx
    have hft : HasDerivWithinAt (fun τ => ℓ ω (ε + τ) (v t)) (ℓt ω (ε + t) (v t)) (Icc bb c) t := by
      have h1 := h.dt ω _ hmt
      have h2 : HasDerivWithinAt (fun τ : ℝ => (ε : ℝ) + τ) 1 (Icc bb c) t :=
        (hasDerivWithinAt_id t _).const_add _
      exact (h1.comp t h2 ((hC.mapsTo_add ω).mono_left hsub)).congr_deriv (mul_one _)
    have hvd : HasDerivWithinAt v (b ω (ε + t)) (Icc bb c) t := by
      have h1 := h.dD ω _ (hC.mapsTo_add ω (hsub ht))
      have h2 : HasDerivWithinAt (fun τ : ℝ => (ε : ℝ) + τ) 1 (Icc bb c) t :=
        (hasDerivWithinAt_id t _).const_add _
      have h3 := (h1.comp t h2 ((hC.mapsTo_add ω).mono_left hsub)).congr_deriv (mul_one _)
      exact (h3.const_add (σ * B ε ω)).const_add x
    have hz : |v t - driftDriver σ B D ω (ε + t)| < 4 * ρ := hdrv t ht x hx
    have hfx : ∀ᶠ p in 𝓝[Icc bb c] t ×ˢ 𝓝 (v t), HasDerivAt (fun z => ℓ ω (ε + p.1) z) (ℓx ω (ε + p.1) p.2) p.2 :=
      (hC.eventually_mem_tube hBc hsub ht hz).mono fun p hp => h.dx ω _ hp
    have hcx := hC.tendsto_shift hBc (f := ℓx ω) (h.contX ω) hsub ht hz
    have hch := hasDerivWithinAt_comp_of_partial (f := fun τ z => ℓ ω (ε + τ) z) (fx := fun τ z => ℓx ω (ε + τ) z)
      hft hvd hfx hcx
    refine hch.congr_deriv ?_
    simp only [shiftFieldT, hv]
    ring
  · exact (h.cont ω).comp hcm hmaps
  · exact (h.contX ω).comp hcm hmaps
  · exact (h.contXX ω).comp hcm hmaps
  · refine ((h.contT ω).comp hcm hmaps).add (ContinuousOn.mul ?_ ((h.contX ω).comp hcm hmaps))
    exact (h.contb ω).comp (continuousOn_const.add continuousOn_fst) fun p hp => hC.mapsTo_add ω (hsub hp.1)
  · obtain ⟨b0, b1, b2, b3, b4⟩ := h.bound ω _ (hmem t ht x hx)
    have hbb := h.bound_b ω _ (hC.mapsTo_add ω (hsub ht))
    have hKK : K ≤ K + K * K := le_add_of_nonneg_right (mul_nonneg hK hK)
    refine ⟨b0.trans hKK, b1.trans hKK, b2.trans hKK, b3.trans hKK, ?_⟩
    simp only [shiftFieldT]
    calc _ ≤ |ℓt ω (ε + t) (x + shiftOff σ B D ε ω t)|
          + |b ω (ε + t) * ℓx ω (ε + t) (x + shiftOff σ B D ε ω t)| := abs_add_le _ _
      _ ≤ K + K * K := by
          rw [abs_mul]
          exact add_le_add b4 (mul_le_mul hbb b1 (abs_nonneg _) hK)


end IsSeedDriftField

end InteractingSLE.ZhanGT4
