/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.ZhanGT4.MixtureA33ChordalObs
import InteractingSLE.Spec.Zhan.StripTimePath

/-!
# Upper strip marks: the strip coordinates along a chordal path

Packet PROVE-ZHAN-A33. The analogue of PROVE-ZHAN-A2's `StripTimePath.lean` with the end mark `v = V^{L,0}` the
innermost left mark: the coordinates `Λ = (V^L, V^R, t(s))`, `t(s) = ∫₀ˢ (W − v)⁻²` (`upCoordAt`), are absolutely
continuous on the strip life with density `upDensAt`, of total variation bounded by the displacements and the clock,
and the generators of `upObs` and `upObs2` vanish at almost every time.
-/

set_option autoImplicit false

noncomputable section

open Set Filter MeasureTheory Topology
open scoped NNReal ENNReal

namespace InteractingSLE.ZhanGT4.UpMark

open Zhan

variable {nL nR : ℕ}

/-- The strip coordinates of a chordal path at time `t`, the end mark at index `0`. -/
def upCoordAt (w : ℝ≥0 → ℝ) (vL : Fin (nL + 1) → ℝ≥0 → ℝ) (vR : Fin nR → ℝ≥0 → ℝ) (t : ℝ≥0) :
    SCoord nL nR :=
  (fun i => vL i t, fun j => vR j t, Strip.stripClock (Strip.extPath w) (Strip.extPath (vL 0)) t)

/-- Their density at real time `s`. -/
def upDensAt (w : ℝ≥0 → ℝ) (vL : Fin (nL + 1) → ℝ≥0 → ℝ) (vR : Fin nR → ℝ≥0 → ℝ) (s : ℝ) : SCoord nL nR :=
  upDens (w s.toNNReal) (fun i => vL i s.toNNReal) (fun j => vR j s.toNNReal)

section Path

variable {a : ℝ} {xL : Fin (nL + 1) → ℝ} {xR : Fin nR → ℝ} {ρL : Fin (nL + 1) → ℝ} {ρR : Fin nR → ℝ}
  {w : ℝ≥0 → ℝ} {vL : Fin (nL + 1) → ℝ≥0 → ℝ} {vR : Fin nR → ℝ≥0 → ℝ} {b : ℝ≥0 → ℝ} {ζ : ℝ≥0∞}

theorem continuousOn_clockRate (h : Sec2.IsForcePath xL xR ρL ρR w vL vR ζ) {t : ℝ≥0}
    (hs : Strip.IsStripLife w (vL 0) ζ t) :
    ContinuousOn (fun s : ℝ => ((w s.toNNReal - vL 0 s.toNNReal) ^ 2)⁻¹) (Icc 0 (t : ℝ)) := by
  have hsub : MapsTo Real.toNNReal (Icc 0 (t : ℝ)) {s : ℝ≥0 | (s : ℝ≥0∞) < ζ} := fun r hr =>
    Sec2.toNNReal_lt_of_mem_Icc hs.1 hr
  refine (((h.continuousOn_w.comp continuous_real_toNNReal.continuousOn hsub).sub
    ((h.continuousOn_vL _).comp continuous_real_toNNReal.continuousOn hsub)).pow 2).inv₀ fun r hr => ?_
  exact pow_ne_zero 2 (sub_pos.2 (hs.2 _ (Sec2.toNNReal_le_of_mem_Icc hr))).ne'

theorem intervalIntegrable_clockRate (h : Sec2.IsForcePath xL xR ρL ρR w vL vR ζ) {t : ℝ≥0}
    (hs : Strip.IsStripLife w (vL 0) ζ t) :
    IntervalIntegrable (fun s : ℝ => ((w s.toNNReal - vL 0 s.toNNReal) ^ 2)⁻¹) volume 0 t :=
  (continuousOn_clockRate h hs).intervalIntegrable_of_Icc t.coe_nonneg

theorem intervalIntegrable_upDensAt (h : Sec2.IsForcePath xL xR ρL ρR w vL vR ζ) {t : ℝ≥0}
    (hs : Strip.IsStripLife w (vL 0) ζ t) :
    IntervalIntegrable (upDensAt w vL vR) volume 0 t :=
  intervalIntegrable_scoord (fun i => h.intervalIntegrable_forceL hs.1 i)
    (fun j => h.intervalIntegrable_forceR hs.1 j) (intervalIntegrable_clockRate h hs)

/-- **The strip coordinates are absolutely continuous**: `Λ_t = Λ_0 + ∫₀ᵗ λ` on the strip life. -/
theorem upCoordAt_eq_add_integral (h : Sec2.IsForcePath xL xR ρL ρR w vL vR ζ) {t : ℝ≥0}
    (hs : Strip.IsStripLife w (vL 0) ζ t) :
    upCoordAt w vL vR t = upCoordAt w vL vR 0 + ∫ s in (0 : ℝ)..t, upDensAt w vL vR s := by
  have hint := intervalIntegrable_upDensAt h hs
  refine Prod.ext (funext fun i => ?_) (Prod.ext (funext fun j => ?_) ?_)
  · simp only [Prod.fst_add, Pi.add_apply, integral_scoord_L hint]
    simp only [upCoordAt, upDensAt, upDens, h.vL_zero]
    exact h.vL_eq hs.1 i
  · simp only [Prod.snd_add, Prod.fst_add, Pi.add_apply, integral_scoord_R hint]
    simp only [upCoordAt, upDensAt, upDens, h.vR_zero]
    exact h.vR_eq hs.1 j
  · simp only [Prod.snd_add, integral_scoord_T hint]
    simp only [upCoordAt, upDensAt, upDens, Strip.stripClock, Strip.extPath,
      NNReal.coe_zero, intervalIntegral.integral_same, zero_add]

/-- **The total variation of the strip coordinates** is bounded by their displacements and the strip clock. -/
theorem integral_norm_upDensAt_le (h : Sec2.IsForcePath xL xR ρL ρR w vL vR ζ) {t : ℝ≥0}
    (hs : Strip.IsStripLife w (vL 0) ζ t) :
    ∫ s in (0 : ℝ)..t, ‖upDensAt w vL vR s‖ ≤
      ∑ i, (xL i - vL i t) + ∑ j, (vR j t - xR j) +
        Strip.stripClock (Strip.extPath w) (Strip.extPath (vL 0)) t := by
  have hint := intervalIntegrable_upDensAt h hs
  have hL := fun i => (h.intervalIntegrable_forceL hs.1 i).abs
  have hR := fun j => (h.intervalIntegrable_forceR hs.1 j).abs
  have hT := intervalIntegrable_clockRate h hs
  have hL' : IntervalIntegrable (fun s => ∑ i, |2 / (vL i s.toNNReal - w s.toNNReal)|) volume 0 t := by
    have h1 := IntervalIntegrable.sum Finset.univ fun i _ => hL i
    rw [Finset.sum_fn] at h1
    exact h1
  have hR' : IntervalIntegrable (fun s => ∑ j, |2 / (vR j s.toNNReal - w s.toNNReal)|) volume 0 t := by
    have h2 := IntervalIntegrable.sum Finset.univ fun j _ => hR j
    rw [Finset.sum_fn] at h2
    exact h2
  calc ∫ s in (0 : ℝ)..t, ‖upDensAt w vL vR s‖
      ≤ ∫ s in (0 : ℝ)..t, (∑ i, |2 / (vL i s.toNNReal - w s.toNNReal)| +
          ∑ j, |2 / (vR j s.toNNReal - w s.toNNReal)| +
          ((w s.toNNReal - vL 0 s.toNNReal) ^ 2)⁻¹) := by
        refine intervalIntegral.integral_mono_on t.coe_nonneg hint.norm ((hL'.add hR').add hT)
          fun s _ => ?_
        refine (norm_scoord_le _).trans (le_of_eq ?_)
        simp only [upDensAt, upDens]
        rw [abs_of_nonneg (inv_nonneg.2 (sq_nonneg _))]
    _ = _ := by
        rw [intervalIntegral.integral_add (hL'.add hR') hT, intervalIntegral.integral_add hL' hR',
          intervalIntegral.integral_finsetSum fun i _ => hL i,
          intervalIntegral.integral_finsetSum fun j _ => hR j]
        simp only [integral_abs_forceL h hs.1, integral_abs_forceR h hs.1]
        rfl

/-- (N1) in the coordinates: `W = √κ b + ℓ(V)`. -/
theorem w_eq_driftLin (hp : IsIntegratedSLEPath a xL xR ρL ρR w vL vR b ζ) {t : ℝ≥0}
    (ht : (t : ℝ≥0∞) < ζ) : w t = Real.sqrt a * b t + driftLin xL xR ρL ρR (upCoordAt w vL vR t) := by
  rw [hp.isForcePath.w_eq_N1 hp.driverEq ht]
  simp only [driftLin, upCoordAt]
  ring

/-- **Along the path the generator of the observable vanishes almost everywhere.** -/
theorem ae_itoGen_upObs_eq_zero (hp : IsIntegratedSLEPath a xL xR ρL ρR w vL vR b ζ) (ha : 0 ≤ a)
    {t : ℝ≥0} (ht : (t : ℝ≥0∞) < ζ)
    (hreg : ∀ s ≤ t, (upCoordAt w vL vR s, b s) ∈ upRegion a xL xR ρL ρR) :
    ∀ᵐ s ∂volume, s ∈ Ioc 0 (t : ℝ) →
      Ito.itoGen (upObs a xL xR ρL ρR) (upCoordAt w vL vR s.toNNReal, b s.toNNReal)
        (upDensAt w vL vR s) = 0 := by
  filter_upwards [ae_not_collision hp.isForcePath ht] with s hs hsI
  obtain ⟨hL, hR⟩ := hs hsI
  have hst : s.toNNReal ≤ t := Sec2.toNNReal_le_of_mem_Icc ⟨hsI.1.le, hsI.2⟩
  exact itoGen_upObs_upDens a xL xR ρL ρR ha
    (w_eq_driftLin hp (lt_of_le_of_lt (by exact_mod_cast hst) ht)) (hreg _ hst)
    (fun i => hL i.succ) hR

/-- **Along the path the generator of `Φ² − κ t` vanishes almost everywhere.** -/
theorem ae_itoGen_upObs2_eq_zero (hp : IsIntegratedSLEPath a xL xR ρL ρR w vL vR b ζ) (ha : 0 ≤ a)
    {t : ℝ≥0} (ht : (t : ℝ≥0∞) < ζ)
    (hreg : ∀ s ≤ t, (upCoordAt w vL vR s, b s) ∈ upRegion a xL xR ρL ρR) :
    ∀ᵐ s ∂volume, s ∈ Ioc 0 (t : ℝ) →
      Ito.itoGen (upObs2 a xL xR ρL ρR) (upCoordAt w vL vR s.toNNReal, b s.toNNReal)
        (upDensAt w vL vR s) = 0 := by
  filter_upwards [ae_not_collision hp.isForcePath ht] with s hs hsI
  obtain ⟨hL, hR⟩ := hs hsI
  have hst : s.toNNReal ≤ t := Sec2.toNNReal_le_of_mem_Icc ⟨hsI.1.le, hsI.2⟩
  exact itoGen_upObs2_upDens a xL xR ρL ρR ha
    (w_eq_driftLin hp (lt_of_le_of_lt (by exact_mod_cast hst) ht)) (hreg _ hst)
    (fun i => hL i.succ) hR

/-- **On the strip life the upper marks stay strictly below the end mark** (`x_{i+1} < x_0`). -/
theorem vL_succ_lt_vL_zero (hp : IsIntegratedSLEPath a xL xR ρL ρR w vL vR b ζ) {s : ℝ≥0}
    (hs : Strip.IsStripLife w (vL 0) ζ s) (hx : ∀ i : Fin nL, xL i.succ < xL 0) (i : Fin nL) :
    vL i.succ s < vL 0 s := by
  refine hp.isForcePath.vL_lt_vL_of_lt hs.1 (hx i) fun r hr => ?_
  have hr' : (r : ℝ≥0∞) < ζ := lt_of_le_of_lt (ENNReal.coe_le_coe.2 hr) hs.1
  exact lt_of_le_of_lt (hp.2.2.2.2.2.2.1 r hr' (Fin.zero_le i.succ)) (hs.2 r hr)

end Path

end InteractingSLE.ZhanGT4.UpMark
