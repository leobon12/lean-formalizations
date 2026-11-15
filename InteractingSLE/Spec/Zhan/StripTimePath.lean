/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Zhan.StripTimeObs

/-!
# The strip coordinates along a chordal path

Packet PROVE-ZHAN-A2. For a path satisfying the frozen `IsIntegratedSLEPath` with `nL + 1` left marks (the last one
`v` is the strip end `−∞`, ruling R36) the strip coordinates `Λ_t = (V^L_t, V^R_t, t(t))` (`stripCoordAt`, `t(·)` the
strip clock `Strip.stripClock`) are absolutely continuous with density `stripDensAt` before the end mark meets the
driver, their density has total variation bounded by the coordinates themselves (the marks are monotone), and the
generators of the strip observables vanish at almost every time (`ae_itoGen_stripMartObs_eq_zero`).

## Main results

* `stripCoordAt_eq_add_integral`: `Λ_t = Λ_0 + ∫₀ᵗ λ` on the strip life;
* `integral_norm_stripDensAt_le`: `∫₀ᵗ ‖λ‖ ≤ Σ |x − V_t| + t(t)`;
* `ae_itoGen_stripMartObs_eq_zero`, `ae_itoGen_stripMartObs2_eq_zero`: along the path the generators of `Φ` and `Φ² − κ t`
  vanish for almost every time in `(0, t]`.
-/

set_option autoImplicit false

noncomputable section

open Set Filter MeasureTheory Topology
open scoped NNReal ENNReal

namespace InteractingSLE

namespace Zhan

variable {nL nR : ℕ}

/-- The strip coordinates of a chordal path at time `t`: the marks and the strip clock. -/
def stripCoordAt (w : ℝ≥0 → ℝ) (vL : Fin (nL + 1) → ℝ≥0 → ℝ) (vR : Fin nR → ℝ≥0 → ℝ) (t : ℝ≥0) :
    SCoord nL nR :=
  (fun i => vL i t, fun j => vR j t,
    Strip.stripClock (Strip.extPath w) (Strip.extPath (vL (Fin.last nL))) t)

/-- Their density at real time `s`. -/
def stripDensAt (w : ℝ≥0 → ℝ) (vL : Fin (nL + 1) → ℝ≥0 → ℝ) (vR : Fin nR → ℝ≥0 → ℝ) (s : ℝ) :
    SCoord nL nR :=
  stripDens (w s.toNNReal) (fun i => vL i s.toNNReal) (fun j => vR j s.toNNReal)

/-! ### Integrals of `SCoord`-valued functions -/

theorem intervalIntegrable_scoord {g : ℝ → SCoord nL nR} {a b : ℝ}
    (h1 : ∀ i, IntervalIntegrable (fun s => (g s).1 i) volume a b)
    (h2 : ∀ j, IntervalIntegrable (fun s => (g s).2.1 j) volume a b)
    (h3 : IntervalIntegrable (fun s => (g s).2.2) volume a b) :
    IntervalIntegrable g volume a b := by
  rw [intervalIntegrable_iff] at h3 ⊢
  have h1' : IntegrableOn (fun s => (g s).1) (uIoc a b) :=
    integrable_pi_iff.2 fun i => intervalIntegrable_iff.1 (h1 i)
  have h2' : IntegrableOn (fun s => (g s).2.1) (uIoc a b) :=
    integrable_pi_iff.2 fun j => intervalIntegrable_iff.1 (h2 j)
  exact h1'.prodMk (h2'.prodMk h3)

theorem integral_scoord_L {g : ℝ → SCoord nL nR} {a b : ℝ} (hg : IntervalIntegrable g volume a b)
    (i : Fin (nL + 1)) : (∫ s in a..b, g s).1 i = ∫ s in a..b, (g s).1 i :=
  (((ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin (nL + 1) => ℝ) i).comp
    (ContinuousLinearMap.fst ℝ (Fin (nL + 1) → ℝ) ((Fin nR → ℝ) × ℝ))).intervalIntegral_comp_comm
    hg).symm

theorem integral_scoord_R {g : ℝ → SCoord nL nR} {a b : ℝ} (hg : IntervalIntegrable g volume a b)
    (j : Fin nR) : (∫ s in a..b, g s).2.1 j = ∫ s in a..b, (g s).2.1 j :=
  (((ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin nR => ℝ) j).comp
    ((ContinuousLinearMap.fst ℝ (Fin nR → ℝ) ℝ).comp
      (ContinuousLinearMap.snd ℝ (Fin (nL + 1) → ℝ) ((Fin nR → ℝ) × ℝ)))).intervalIntegral_comp_comm
    hg).symm

theorem integral_scoord_T {g : ℝ → SCoord nL nR} {a b : ℝ} (hg : IntervalIntegrable g volume a b) :
    (∫ s in a..b, g s).2.2 = ∫ s in a..b, (g s).2.2 :=
  (((ContinuousLinearMap.snd ℝ (Fin nR → ℝ) ℝ).comp
    (ContinuousLinearMap.snd ℝ (Fin (nL + 1) → ℝ) ((Fin nR → ℝ) × ℝ))).intervalIntegral_comp_comm
    hg).symm

theorem norm_pi_le_sum' {n : ℕ} (f : Fin n → ℝ) : ‖f‖ ≤ ∑ i, |f i| :=
  (pi_norm_le_iff_of_nonneg (Finset.sum_nonneg fun _ _ => abs_nonneg _)).2 fun i => by
    rw [Real.norm_eq_abs]
    exact Finset.single_le_sum (f := fun j => |f j|) (fun _ _ => abs_nonneg _) (Finset.mem_univ i)

theorem norm_scoord_le (p : SCoord nL nR) : ‖p‖ ≤ ∑ i, |p.1 i| + ∑ j, |p.2.1 j| + |p.2.2| := by
  have h1 := norm_pi_le_sum' p.1
  have h2 := norm_pi_le_sum' p.2.1
  have h0 : 0 ≤ ∑ i, |p.1 i| := Finset.sum_nonneg fun _ _ => abs_nonneg _
  have h0' : 0 ≤ ∑ j, |p.2.1 j| := Finset.sum_nonneg fun _ _ => abs_nonneg _
  rw [Prod.norm_def, Prod.norm_def, Real.norm_eq_abs]
  refine max_le (h1.trans (by linarith [abs_nonneg p.2.2])) (max_le (h2.trans ?_) ?_) <;>
    linarith [abs_nonneg p.2.2]

/-! ### The path -/

section Path

variable {a : ℝ} {xL : Fin (nL + 1) → ℝ} {xR : Fin nR → ℝ} {ρL : Fin (nL + 1) → ℝ} {ρR : Fin nR → ℝ}
  {w : ℝ≥0 → ℝ} {vL : Fin (nL + 1) → ℝ≥0 → ℝ} {vR : Fin nR → ℝ≥0 → ℝ} {b : ℝ≥0 → ℝ} {ζ : ℝ≥0∞}

/-- The strip clock rate is continuous, hence integrable, on `[0, t]` while the end mark is left of the driver. -/
theorem continuousOn_clockRate (h : Sec2.IsForcePath xL xR ρL ρR w vL vR ζ) {t : ℝ≥0}
    (hs : Strip.IsStripLife w (vL (Fin.last nL)) ζ t) :
    ContinuousOn (fun s : ℝ => ((w s.toNNReal - vL (Fin.last nL) s.toNNReal) ^ 2)⁻¹) (Icc 0 (t : ℝ)) := by
  have hsub : MapsTo Real.toNNReal (Icc 0 (t : ℝ)) {s : ℝ≥0 | (s : ℝ≥0∞) < ζ} := fun r hr =>
    Sec2.toNNReal_lt_of_mem_Icc hs.1 hr
  refine (((h.continuousOn_w.comp continuous_real_toNNReal.continuousOn hsub).sub
    ((h.continuousOn_vL _).comp continuous_real_toNNReal.continuousOn hsub)).pow 2).inv₀ fun r hr => ?_
  exact pow_ne_zero 2 (sub_pos.2 (hs.2 _ (Sec2.toNNReal_le_of_mem_Icc hr))).ne'

theorem intervalIntegrable_clockRate (h : Sec2.IsForcePath xL xR ρL ρR w vL vR ζ) {t : ℝ≥0}
    (hs : Strip.IsStripLife w (vL (Fin.last nL)) ζ t) :
    IntervalIntegrable (fun s : ℝ => ((w s.toNNReal - vL (Fin.last nL) s.toNNReal) ^ 2)⁻¹) volume 0 t :=
  (continuousOn_clockRate h hs).intervalIntegrable_of_Icc t.coe_nonneg

theorem intervalIntegrable_stripDensAt (h : Sec2.IsForcePath xL xR ρL ρR w vL vR ζ) {t : ℝ≥0}
    (hs : Strip.IsStripLife w (vL (Fin.last nL)) ζ t) :
    IntervalIntegrable (stripDensAt w vL vR) volume 0 t :=
  intervalIntegrable_scoord (fun i => h.intervalIntegrable_forceL hs.1 i)
    (fun j => h.intervalIntegrable_forceR hs.1 j) (intervalIntegrable_clockRate h hs)

/-- **The strip coordinates are absolutely continuous**: `Λ_t = Λ_0 + ∫₀ᵗ λ` on the strip life. -/
theorem stripCoordAt_eq_add_integral (h : Sec2.IsForcePath xL xR ρL ρR w vL vR ζ) {t : ℝ≥0}
    (hs : Strip.IsStripLife w (vL (Fin.last nL)) ζ t) :
    stripCoordAt w vL vR t = stripCoordAt w vL vR 0 + ∫ s in (0 : ℝ)..t, stripDensAt w vL vR s := by
  have hint := intervalIntegrable_stripDensAt h hs
  refine Prod.ext (funext fun i => ?_) (Prod.ext (funext fun j => ?_) ?_)
  · simp only [Prod.fst_add, Pi.add_apply, integral_scoord_L hint]
    simp only [stripCoordAt, stripDensAt, stripDens, h.vL_zero]
    exact h.vL_eq hs.1 i
  · simp only [Prod.snd_add, Prod.fst_add, Pi.add_apply, integral_scoord_R hint]
    simp only [stripCoordAt, stripDensAt, stripDens, h.vR_zero]
    exact h.vR_eq hs.1 j
  · simp only [Prod.snd_add, integral_scoord_T hint]
    simp only [stripCoordAt, stripDensAt, stripDens, Strip.stripClock, Strip.extPath,
      NNReal.coe_zero, intervalIntegral.integral_same, zero_add]

/-- The left force velocities are nonpositive and the right ones nonnegative, so their absolute integrals are the
displacements. -/
theorem integral_abs_forceL (h : Sec2.IsForcePath xL xR ρL ρR w vL vR ζ) {t : ℝ≥0}
    (ht : (t : ℝ≥0∞) < ζ) (i : Fin (nL + 1)) :
    ∫ s in (0 : ℝ)..t, |2 / (vL i s.toNNReal - w s.toNNReal)| = xL i - vL i t := by
  have heq : ∫ s in (0 : ℝ)..t, |2 / (vL i s.toNNReal - w s.toNNReal)| =
      ∫ s in (0 : ℝ)..t, -(2 / (vL i s.toNNReal - w s.toNNReal)) := by
    refine intervalIntegral.integral_congr fun s hs => ?_
    rw [uIcc_of_le t.coe_nonneg] at hs
    have hle := h.vL_le_w (Sec2.toNNReal_lt_of_mem_Icc ht hs) i
    exact abs_of_nonpos (div_nonpos_of_nonneg_of_nonpos zero_le_two (sub_nonpos.2 hle))
  rw [heq, intervalIntegral.integral_neg, h.vL_eq ht i]
  ring

theorem integral_abs_forceR (h : Sec2.IsForcePath xL xR ρL ρR w vL vR ζ) {t : ℝ≥0}
    (ht : (t : ℝ≥0∞) < ζ) (j : Fin nR) :
    ∫ s in (0 : ℝ)..t, |2 / (vR j s.toNNReal - w s.toNNReal)| = vR j t - xR j := by
  have heq : ∫ s in (0 : ℝ)..t, |2 / (vR j s.toNNReal - w s.toNNReal)| =
      ∫ s in (0 : ℝ)..t, 2 / (vR j s.toNNReal - w s.toNNReal) := by
    refine intervalIntegral.integral_congr fun s hs => ?_
    rw [uIcc_of_le t.coe_nonneg] at hs
    have hle := h.w_le_vR (Sec2.toNNReal_lt_of_mem_Icc ht hs) j
    exact abs_of_nonneg (div_nonneg zero_le_two (sub_nonneg.2 hle))
  rw [heq, h.vR_eq ht j]
  ring

/-- **The total variation of the strip coordinates** is bounded by their displacements and the strip clock. -/
theorem integral_norm_stripDensAt_le (h : Sec2.IsForcePath xL xR ρL ρR w vL vR ζ) {t : ℝ≥0}
    (hs : Strip.IsStripLife w (vL (Fin.last nL)) ζ t) :
    ∫ s in (0 : ℝ)..t, ‖stripDensAt w vL vR s‖ ≤
      ∑ i, (xL i - vL i t) + ∑ j, (vR j t - xR j) +
        Strip.stripClock (Strip.extPath w) (Strip.extPath (vL (Fin.last nL))) t := by
  have hint := intervalIntegrable_stripDensAt h hs
  have hL := fun i => (h.intervalIntegrable_forceL hs.1 i).abs
  have hR := fun j => (h.intervalIntegrable_forceR hs.1 j).abs
  have hT := intervalIntegrable_clockRate h hs
  have hsum : IntervalIntegrable (fun s => ∑ i, |2 / (vL i s.toNNReal - w s.toNNReal)| +
      ∑ j, |2 / (vR j s.toNNReal - w s.toNNReal)| +
      ((w s.toNNReal - vL (Fin.last nL) s.toNNReal) ^ 2)⁻¹) volume 0 t := by
    have h1 := IntervalIntegrable.sum Finset.univ fun i _ => hL i
    have h2 := IntervalIntegrable.sum Finset.univ fun j _ => hR j
    rw [Finset.sum_fn] at h1 h2
    exact (h1.add h2).add hT
  calc ∫ s in (0 : ℝ)..t, ‖stripDensAt w vL vR s‖
      ≤ ∫ s in (0 : ℝ)..t, (∑ i, |2 / (vL i s.toNNReal - w s.toNNReal)| +
          ∑ j, |2 / (vR j s.toNNReal - w s.toNNReal)| +
          ((w s.toNNReal - vL (Fin.last nL) s.toNNReal) ^ 2)⁻¹) := by
        refine intervalIntegral.integral_mono_on t.coe_nonneg hint.norm hsum fun s _ => ?_
        refine (norm_scoord_le _).trans (le_of_eq ?_)
        simp only [stripDensAt, stripDens]
        rw [abs_of_nonneg (inv_nonneg.2 (sq_nonneg _))]
    _ = _ := by
        rw [intervalIntegral.integral_add (by
            have h1 := IntervalIntegrable.sum Finset.univ fun i _ => hL i
            have h2 := IntervalIntegrable.sum Finset.univ fun j _ => hR j
            rw [Finset.sum_fn] at h1 h2
            exact h1.add h2) hT,
          intervalIntegral.integral_add (by
            have h1 := IntervalIntegrable.sum Finset.univ fun i _ => hL i
            rw [Finset.sum_fn] at h1
            exact h1) (by
            have h2 := IntervalIntegrable.sum Finset.univ fun j _ => hR j
            rw [Finset.sum_fn] at h2
            exact h2),
          intervalIntegral.integral_finsetSum fun i _ => hL i,
          intervalIntegral.integral_finsetSum fun j _ => hR j]
        simp only [integral_abs_forceL h hs.1, integral_abs_forceR h hs.1]
        rfl

/-- (N1) in the coordinates: `W = √κ b + ℓ(V)`. -/
theorem w_eq_driftLin (hp : IsIntegratedSLEPath a xL xR ρL ρR w vL vR b ζ) {t : ℝ≥0}
    (ht : (t : ℝ≥0∞) < ζ) : w t = Real.sqrt a * b t + driftLin xL xR ρL ρR (stripCoordAt w vL vR t) := by
  rw [hp.isForcePath.w_eq_N1 hp.driverEq ht]
  simp only [driftLin, stripCoordAt]
  ring

/-- At almost every time of `(0, t]` no lower mark meets the driver. -/
theorem ae_not_collision (h : Sec2.IsForcePath xL xR ρL ρR w vL vR ζ) {t : ℝ≥0}
    (ht : (t : ℝ≥0∞) < ζ) :
    ∀ᵐ s ∂volume, s ∈ Ioc 0 (t : ℝ) →
      (∀ i, vL i s.toNNReal ≠ w s.toNNReal) ∧ ∀ j, vR j s.toNNReal ≠ w s.toNNReal := by
  have hL : ∀ i, ∀ᵐ s ∂volume, s ∉ {s : ℝ | 0 ≤ s ∧ (s.toNNReal : ℝ≥0∞) < ζ ∧
      w s.toNNReal = vL i s.toNNReal} := fun i => by
    rw [ae_iff]; simpa using h.volume_collisionL i
  have hR : ∀ j, ∀ᵐ s ∂volume, s ∉ {s : ℝ | 0 ≤ s ∧ (s.toNNReal : ℝ≥0∞) < ζ ∧
      w s.toNNReal = vR j s.toNNReal} := fun j => by
    rw [ae_iff]; simpa using h.volume_collisionR j
  filter_upwards [ae_all_iff.2 hL, ae_all_iff.2 hR] with s hsL hsR hs
  have hsI : s ∈ Icc 0 (t : ℝ) := ⟨hs.1.le, hs.2⟩
  have hsζ := Sec2.toNNReal_lt_of_mem_Icc ht hsI
  exact ⟨fun i he => hsL i ⟨hsI.1, hsζ, he.symm⟩, fun j he => hsR j ⟨hsI.1, hsζ, he.symm⟩⟩

/-- **Along the path the generator of the strip observable vanishes almost everywhere.** -/
theorem ae_itoGen_stripMartObs_eq_zero (hp : IsIntegratedSLEPath a xL xR ρL ρR w vL vR b ζ) (ha : 0 ≤ a)
    {t : ℝ≥0} (ht : (t : ℝ≥0∞) < ζ)
    (hreg : ∀ s ≤ t, (stripCoordAt w vL vR s, b s) ∈ stripMartRegion a xL xR ρL ρR) :
    ∀ᵐ s ∂volume, s ∈ Ioc 0 (t : ℝ) →
      Ito.itoGen (stripMartObs a xL xR ρL ρR) (stripCoordAt w vL vR s.toNNReal, b s.toNNReal)
        (stripDensAt w vL vR s) = 0 := by
  filter_upwards [ae_not_collision hp.isForcePath ht] with s hs hsI
  obtain ⟨hL, hR⟩ := hs hsI
  have hst : s.toNNReal ≤ t := Sec2.toNNReal_le_of_mem_Icc ⟨hsI.1.le, hsI.2⟩
  exact itoGen_stripMartObs_stripDens a xL xR ρL ρR ha
    (w_eq_driftLin hp (lt_of_le_of_lt (by exact_mod_cast hst) ht)) (hreg _ hst)
    (fun i => hL i.castSucc) hR

/-- **Along the path the generator of `Φ² − κ t` vanishes almost everywhere.** -/
theorem ae_itoGen_stripMartObs2_eq_zero (hp : IsIntegratedSLEPath a xL xR ρL ρR w vL vR b ζ) (ha : 0 ≤ a)
    {t : ℝ≥0} (ht : (t : ℝ≥0∞) < ζ)
    (hreg : ∀ s ≤ t, (stripCoordAt w vL vR s, b s) ∈ stripMartRegion a xL xR ρL ρR) :
    ∀ᵐ s ∂volume, s ∈ Ioc 0 (t : ℝ) →
      Ito.itoGen (stripMartObs2 a xL xR ρL ρR) (stripCoordAt w vL vR s.toNNReal, b s.toNNReal)
        (stripDensAt w vL vR s) = 0 := by
  filter_upwards [ae_not_collision hp.isForcePath ht] with s hs hsI
  obtain ⟨hL, hR⟩ := hs hsI
  have hst : s.toNNReal ≤ t := Sec2.toNNReal_le_of_mem_Icc ⟨hsI.1.le, hsI.2⟩
  exact itoGen_stripMartObs2_stripDens a xL xR ρL ρR ha
    (w_eq_driftLin hp (lt_of_le_of_lt (by exact_mod_cast hst) ht)) (hreg _ hst)
    (fun i => hL i.castSucc) hR

end Path

end Zhan

end InteractingSLE
