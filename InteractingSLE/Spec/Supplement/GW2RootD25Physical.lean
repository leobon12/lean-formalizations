/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW2RootD25Sample

/-!
# Physical-time observations are the actual charted tips and are causal

Packet PROVE-T14-GW2ROOT2. The proved strict capacity clock inverts at
every protected physical time. Consequently the random-capacity tip is
the actual boundary-chart tip, preserves interior visits, and both
coordinates are unchanged by extending the physical recording cutoff.
-/

set_option autoImplicit false
noncomputable section

open Set Filter Topology MeasureTheory
open scoped NNReal ENNReal
open QuantumZipper (H)

namespace InteractingSLE.Theorem14.GW2TipSystem.RootD25

open Exist Staged StagedLaw Restart Supp8.GB6 Supp8.GB6.CoordB RootB23

theorem physicalObservationRead_eq {a : ℝ≥0} (ha : 0 < a) (s v t : ℝ≥0)
    (p : RecData × RecData) :
    physicalObservationRead a s v t p =
      ((a : ℝ) * relativeDriverRead s v (RootZ21.forwardCapacity s t p).toNNReal p,
        ((a : ℝ) : ℂ) * RootA22.relativeTipRead s v
          (RootZ21.forwardCapacity s t p).toNNReal p) := by
  simp only [physicalObservationRead, scaledRelativeObservationRead,
    scaledRelativeDriverRead, scaledRelativeTipRead, physicalClock,
    mul_div_cancel_left₀ _ (pow_ne_zero 2 ha.ne')]

section Protected

variable {Ω : Type*} (W : ℝ≥0 → Ω → ℝ) (ζ : Ω → ℝ≥0∞) (ω : Ω)
  {α : ℝ≥0 → ℂ} (hα : IsGeneratingTrace (W · ω) (ζ ω) α)
  (hW : ContinuousOn (W · ω) {t | (t : ℝ≥0∞) < ζ ω}) (hW0 : W 0 ω = 0)
  {s : ℝ≥0} (hs : (s : ℝ≥0∞) < ζ ω) (hsH : α s ∈ H)
  {e : (ℝ≥0 → ℝ) × ℝ≥0∞} (he : IsRegularDriver e) {γ : ℝ≥0 → ℂ}
  (hγ : IsGeneratingTrace e.1 e.2 γ) {v : ℝ≥0}
  (hv : (v : ℝ≥0∞) < min
    (firstContactTime (fun q => sphereInv (γ q : OnePoint ℂ))
      ((fun q => (α q : OnePoint ℂ)) '' Icc 0 s)) e.2)

include hα hW hW0 hs hsH he hγ hv

/-- Composing the actual inverse with the attained forward capacity gives
the physical time itself, through the protected endpoint. -/
theorem forwardClockInverse_forwardCapacity {t : ℝ≥0} (htv : t ≤ v) :
    let p := (cfRec s W ζ ω, recOf (v : ℝ≥0∞) e)
    RootZ21.forwardClockInverse s v (RootZ21.forwardCapacity s t p).toNNReal p = t := by
  exact (RootA22.isClockOn_forwardCapacity_before_contact
    W ζ ω hα hW hW0 hs hsH he hγ hv).invClock_apply (ENNReal.coe_le_coe.mpr htv)

/-- The physical-time tip reader is the literal boundary extension of the
original physical trace, including real visits and the finite endpoint. -/
theorem physicalObservationRead_snd_eq {a : ℝ≥0} (ha : 0 < a)
    {t : ℝ≥0} (htv : t ≤ v) :
    let p := (cfRec s W ζ ω, recOf (v : ℝ≥0∞) e)
    (physicalObservationRead a s v t p).2 =
      ((a : ℝ) : ℂ) * relBdry (rdrv p.1) s (γ t) := by
  dsimp only
  rw [physicalObservationRead_eq ha]
  have hclock := RootA22.isClockOn_forwardCapacity_before_contact
    W ζ ω hα hW hW0 hs hsH he hγ hv
  have hu : ((RootZ21.forwardCapacity s t
      (cfRec s W ζ ω, recOf (v : ℝ≥0∞) e)).toNNReal : ℝ) ≤
      RootZ21.forwardCapacity s v (cfRec s W ζ ω, recOf (v : ℝ≥0∞) e) := by
    rw [Real.coe_toNNReal _ (RootZ21.forwardCapacity_nonneg _ _ _)]
    exact hclock.strictMonoOn.monotoneOn (ENNReal.coe_le_coe.mpr htv)
      (show (v : ℝ≥0∞) ≤ v from le_rfl) htv
  rw [RootA22.relativeTipRead_eq_before_contact
    W ζ ω hα hW hW0 hs hsH he hγ hv _ hu,
    forwardClockInverse_forwardCapacity W ζ ω hα hW hW0 hs hsH he hγ hv htv]

/-- A protected chart preserves precisely the physical interior visits. -/
theorem physicalObservationRead_snd_mem_H_iff {a : ℝ≥0} (ha : 0 < a)
    {t : ℝ≥0} (htv : t ≤ v) :
    (physicalObservationRead a s v t
      (cfRec s W ζ ω, recOf (v : ℝ≥0∞) e)).2 ∈ H ↔ γ t ∈ H := by
  rw [physicalObservationRead_snd_eq W ζ ω hα hW hW0 hs hsH he hγ hv ha htv]
  have hsafe := RootA22.trace_mem_record_relSafe_before_contact
    W ζ ω hα hW hW0 hs he hγ hv htv
  have hscale : ∀ z : ℂ, ((a : ℝ) : ℂ) * z ∈ H ↔ z ∈ H := by
    intro z
    change 0 < (((a : ℝ) : ℂ) * z).im ↔ 0 < z.im
    rw [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, zero_mul, add_zero]
    exact mul_pos_iff_of_pos_left (NNReal.coe_pos.mpr ha)
  exact (hscale _).trans
    (relBdry_mem_H_iff (continuous_rdrv _) (rdrv_zero _) s.coe_nonneg hsafe)

/-- Physical-time driver and tip readings through an earlier cutoff use
no later physical continuation, even though their capacity time is random. -/
theorem physicalObservationRead_prefix_eq {a : ℝ≥0} (ha : 0 < a)
    {t V : ℝ≥0} (htv : t ≤ V) (hVv : V ≤ v) :
    physicalObservationRead a s V t (cfRec s W ζ ω, recOf (V : ℝ≥0∞) e) =
      physicalObservationRead a s v t (cfRec s W ζ ω, recOf (v : ℝ≥0∞) e) := by
  have hV := (ENNReal.coe_le_coe.mpr hVv).trans_lt hv
  have hcap : RootZ21.forwardCapacity s t (cfRec s W ζ ω, recOf (V : ℝ≥0∞) e) =
      RootZ21.forwardCapacity s t (cfRec s W ζ ω, recOf (v : ℝ≥0∞) e) :=
    (RootZ21.forwardCapacity_prefix_eq s _ he (lt_min_iff.mp hV).2 htv).trans
      (RootZ21.forwardCapacity_prefix_eq s _ he (lt_min_iff.mp hv).2
        (htv.trans hVv)).symm
  have hclock := RootA22.isClockOn_forwardCapacity_before_contact
    W ζ ω hα hW hW0 hs hsH he hγ hV
  have hu : ((RootZ21.forwardCapacity s t
      (cfRec s W ζ ω, recOf (V : ℝ≥0∞) e)).toNNReal : ℝ) ≤
      RootZ21.forwardCapacity s V (cfRec s W ζ ω, recOf (V : ℝ≥0∞) e) := by
    rw [Real.coe_toNNReal _ (RootZ21.forwardCapacity_nonneg _ _ _)]
    exact hclock.strictMonoOn.monotoneOn (ENNReal.coe_le_coe.mpr htv)
      (show (V : ℝ≥0∞) ≤ V from le_rfl) htv
  have hpref := relativeObservationRead_prefix_eq_before_contact
    W ζ ω hα hW hW0 hs hsH he hγ hVv hv _ hu
  rw [physicalObservationRead_eq ha, physicalObservationRead_eq ha, ← hcap]
  exact Prod.ext (congrArg (fun z : ℝ × ℂ => (a : ℝ) * z.1) hpref)
    (congrArg (fun z : ℝ × ℂ => ((a : ℝ) : ℂ) * z.2) hpref)

end Protected

end InteractingSLE.Theorem14.GW2TipSystem.RootD25
