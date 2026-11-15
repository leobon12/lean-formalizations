/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Coupling.AnnounceLifetime
import InteractingSLE.Spec.Coupling.Assembly11Drv
import InteractingSLE.Spec.Dimension.TraceBridge
import QuantumZipper.Proofs.Loewner.CaraRZ
import InteractingSLE.Spec.Sec2.AddMarksGirsanov
import InteractingSLE.Frozen.Spec.IsOrderedForceWord

/-!
# The local comparison of Aux. lemma 55: the seed radius, the local stop, and the pathwise bounds

Packet PROVE-LOCEXT-A, step 1 (`planning/handoffs/PROVE-AUX52-55.md`, "What is missing", item 1). Source: the
specification's Aux. lemma 55, proof, first paragraph (`source/spec/p241-288.md` L118–L139, p. 247):

"Write `J` for the force indices whose initial positions are nonzero. Choose a positive dyadic `r` with
`8r < min_{j∈J}|x_j|` […]. Use the entirely driving-based stop `S = r²/64 ∧ inf{t : |W_t| ≥ r/4}`. It is strictly
positive by continuity of the driver. The elementary Loewner hull bounds give […] `K_S ⊂ B(0, r/2) ⊂ F`. […] Every
right mark in `J` has `V^j_t ≥ x_j > 8r` and every left mark has `V^j_t ≤ x_j < −8r`. Their distances from the driver
are at least `7r` through `S`. They cannot collide during this interval. The only possible seed collisions have
weights `r_−, r_+ > −2`, so `S` is strictly before any continuation threshold."

## Main results

* `IsSeedRadius xL xR r`: `0 < r` and `8r < |x_j|` for every nonzero position; `seedRadius xL xR` is the largest
  dyadic `2^{-k}` with this property (`isSeedRadius_seedRadius`);
* `localStopPath r ζ w = (r²/64) ∧ inf{t < ζ : |w_t| > r/4}`; `localStop r G ζ W` is the same on a good event `G`;
* pathwise bounds through the stop: `abs_le_of_le_localStopPath` (`|w_t| ≤ r/4`),
  `le_vR_of_lt`/`vL_le_of_lt` (distant marks move away), `seven_mul_le_vR_sub_of_le_localStopPath` and
  `seven_mul_le_sub_vL_of_le_localStopPath` (distance `≥ 7r`), `fwdHull_subset_closedBall_of_le_localStopPath`
  (`K_t ⊆ B̄(0, 5r/8)` through the stop), `vR_eq_vR_of_xR_eq_zero` (the seed marks stay merged);
* `localStopPath_pos`: the stop is strictly positive; `localStopPath_lt_of_isIntegratedSLEPath`: it is strictly
  before the lifetime, given the terminal state of Aux. lemma 3 (the seed weights are admissible);
* `isStoppingTime_localStop`: the stop is a stopping time of every right-continuous filtration in which the driver is
  adapted before the lifetime (in particular of the frozen `drivingFiltration`).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology Metric
open scoped NNReal ENNReal

namespace InteractingSLE

namespace LocalExt

open Coupling

/-! ### The seed radius -/

section Radius

variable {nL nR : ℕ} (xL : Fin nL → ℝ) (xR : Fin nR → ℝ)

/-- **An admissible radius for the local comparison** (Aux. 55, p. 247: "Choose a positive dyadic `r` with
`8r < min_{j∈J}|x_j|`"): `r > 0` and `8r < |x_j|` for every force position `x_j ≠ 0`. -/
def IsSeedRadius (r : ℝ) : Prop :=
  0 < r ∧ (∀ i, xL i ≠ 0 → 8 * r < |xL i|) ∧ ∀ j, xR j ≠ 0 → 8 * r < |xR j|

theorem exists_pos_le_of_fintype {ι : Type*} [Fintype ι] (f : ι → ℝ) (hf : ∀ k, 0 < f k) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ k, ε ≤ f k := by
  rcases isEmpty_or_nonempty ι with hι | hι
  · exact ⟨1, one_pos, fun k => isEmptyElim k⟩
  · refine ⟨Finset.univ.inf' Finset.univ_nonempty f, ?_, fun k => Finset.inf'_le _ (Finset.mem_univ k)⟩
    obtain ⟨k, -, hk⟩ := Finset.exists_mem_eq_inf' Finset.univ_nonempty f
    rw [hk]
    exact hf k

theorem exists_isSeedRadius_half_pow : ∃ k : ℕ, IsSeedRadius xL xR ((1 / 2 : ℝ) ^ k) := by
  classical
  obtain ⟨ε, hε, hεk⟩ := exists_pos_le_of_fintype
    (Sum.elim (fun i => if xL i = 0 then 1 else |xL i|) (fun j => if xR j = 0 then 1 else |xR j|))
    (fun k => by
      cases k with
      | inl i => by_cases hi : xL i = 0 <;> simp [hi, abs_pos]
      | inr j => by_cases hj : xR j = 0 <;> simp [hj, abs_pos])
  obtain ⟨k, hk⟩ := exists_pow_lt_of_lt_one (show 0 < ε / 8 by positivity) (by norm_num : (1 / 2 : ℝ) < 1)
  refine ⟨k, by positivity, fun i hi => ?_, fun j hj => ?_⟩
  · have := hεk (Sum.inl i)
    simp only [Sum.elim_inl, hi, ↓reduceIte] at this
    linarith
  · have := hεk (Sum.inr j)
    simp only [Sum.elim_inr, hj, ↓reduceIte] at this
    linarith

open Classical in
/-- **The seed radius** `r = 2^{-k}`, `k` least with `IsSeedRadius` (Aux. 55: "a positive dyadic `r`"). -/
def seedRadius : ℝ := (1 / 2 : ℝ) ^ Nat.find (exists_isSeedRadius_half_pow xL xR)

theorem isSeedRadius_seedRadius : IsSeedRadius xL xR (seedRadius xL xR) := by
  classical
  exact Nat.find_spec (exists_isSeedRadius_half_pow xL xR)

theorem seedRadius_pos : 0 < seedRadius xL xR := (isSeedRadius_seedRadius xL xR).1

end Radius

/-! ### Hitting times: the level holds up to the hitting time -/

section Hit

variable {f : ℝ≥0 → ℝ} {ζ : ℝ≥0∞} {ε : ℝ}

/-- Up to (and at) the hitting time of `{f < ε}`, `f ≥ ε`, for `f` continuous before `ζ` with `f 0 ≥ ε`. -/
theorem le_of_le_hitBelow (hf : ContinuousOn f {s : ℝ≥0 | (s : ℝ≥0∞) < ζ}) (h0 : ε ≤ f 0) {t : ℝ≥0}
    (ht : (t : WithTop ℝ≥0) ≤ hitBelow f ζ ε) (htζ : (t : ℝ≥0∞) < ζ) : ε ≤ f t := by
  by_contra hlt
  rw [not_le] at hlt
  have ht0 : 0 < t := by
    rcases eq_or_ne t 0 with h | h
    · rw [h] at hlt; linarith
    · exact pos_iff_ne_zero.2 h
  have hcont : ContinuousAt f t := hf.continuousAt ((isOpen_setOf_coe_lt ζ).mem_nhds htζ)
  have hev : ∀ᶠ s in 𝓝 t, f s < ε ∧ (s : ℝ≥0∞) < ζ :=
    (hcont.eventually (gt_mem_nhds hlt)).and ((isOpen_setOf_coe_lt ζ).mem_nhds htζ)
  have : (𝓝[<] t).NeBot := nhdsLT_neBot_of_exists_lt ⟨0, ht0⟩
  obtain ⟨s, ⟨hfs, hsζ⟩, hst⟩ := ((hev.filter_mono nhdsWithin_le_nhds).and
    (self_mem_nhdsWithin : Iio t ∈ 𝓝[<] t)).exists
  have h1 := hitBelow_le hsζ hfs
  have h2 : (t : WithTop ℝ≥0) ≤ s := ht.trans h1
  exact absurd (WithTop.coe_le_coe.1 h2) (not_le.2 hst)

/-- The hitting time of `{f < ε}` is positive if `f 0 > ε` and `f` is continuous before `ζ > 0`. -/
theorem hitBelow_pos (hf : ContinuousOn f {s : ℝ≥0 | (s : ℝ≥0∞) < ζ}) (hζ : 0 < ζ) (h0 : ε < f 0) :
    0 < hitBelow f ζ ε := by
  have hcont : ContinuousAt f 0 := hf.continuousAt ((isOpen_setOf_coe_lt ζ).mem_nhds (by simpa using hζ))
  obtain ⟨δ, hδ, hball⟩ := Metric.eventually_nhds_iff.1 (hcont.eventually (lt_mem_nhds h0))
  have hδ' : 0 < (⟨δ / 2, by positivity⟩ : ℝ≥0) := by
    change (0 : ℝ) < δ / 2
    positivity
  refine lt_of_lt_of_le (WithTop.coe_lt_coe.2 hδ') (le_hitBelow fun s _ hfs => ?_)
  refine le_of_not_gt fun hlt => ?_
  refine absurd (hball ?_) (not_lt.2 hfs.le)
  rw [NNReal.dist_eq, NNReal.coe_zero, sub_zero, abs_of_nonneg s.coe_nonneg]
  have : (s : ℝ) < δ / 2 := hlt
  linarith

end Hit

/-! ### The local stop -/

section Stop

variable {Ω : Type*} {mΩ : MeasurableSpace Ω}

/-- The horizon `r²/64` of the local stop. -/
def stopHorizon (r : ℝ) : ℝ≥0 := (r ^ 2 / 64).toNNReal

theorem coe_stopHorizon (r : ℝ) : (stopHorizon r : ℝ) = r ^ 2 / 64 :=
  Real.coe_toNNReal _ (by positivity)

theorem stopHorizon_pos {r : ℝ} (hr : 0 < r) : 0 < stopHorizon r :=
  Real.toNNReal_pos.2 (by positivity)

/-- The function whose first negative value stops the comparison: `r/4 − |w_s|`. -/
def stopGap (r : ℝ) (w : ℝ≥0 → ℝ) (s : ℝ≥0) : ℝ := r / 4 - |w s|

/-- **The local stop of Aux. 55 along one path** (p. 247): `S = (r²/64) ∧ inf{t < ζ : |w_t| > r/4}`. -/
def localStopPath (r : ℝ) (ζ : ℝ≥0∞) (w : ℝ≥0 → ℝ) : WithTop ℝ≥0 :=
  min (stopHorizon r : WithTop ℝ≥0) (hitBelow (stopGap r w) ζ 0)

open Classical in
/-- **The local stop of Aux. 55** for the driver `W` on a good event `G` (the path rule on `G`, the horizon
`r²/64` off `G`). -/
def localStop (r : ℝ) (G : Set Ω) (ζ : Ω → ℝ≥0∞) (W : ℝ≥0 → Ω → ℝ) (ω : Ω) : WithTop ℝ≥0 :=
  min (stopHorizon r : WithTop ℝ≥0) (if ω ∈ G then hitBelow (stopGap r (W · ω)) (ζ ω) 0 else ⊤)

variable {r : ℝ} {G : Set Ω} {ζ' : Ω → ℝ≥0∞} {W' : ℝ≥0 → Ω → ℝ} {ω : Ω}

theorem localStop_of_mem (hω : ω ∈ G) : localStop r G ζ' W' ω = localStopPath r (ζ' ω) (W' · ω) := by
  simp only [localStop, localStopPath, hω, ↓reduceIte]

theorem localStop_of_notMem (hω : ω ∉ G) : localStop r G ζ' W' ω = stopHorizon r := by
  simp only [localStop, hω, ↓reduceIte, le_top, min_eq_left]

theorem localStop_le_stopHorizon : localStop r G ζ' W' ω ≤ stopHorizon r := min_le_left _ _

theorem localStop_ne_top : localStop r G ζ' W' ω ≠ ⊤ :=
  ne_top_of_le_ne_top WithTop.coe_ne_top localStop_le_stopHorizon

variable {w : ℝ≥0 → ℝ} {ζ : ℝ≥0∞}

theorem localStopPath_le_stopHorizon : localStopPath r ζ w ≤ stopHorizon r := min_le_left _ _

theorem continuousOn_stopGap (hw : ContinuousOn w {s : ℝ≥0 | (s : ℝ≥0∞) < ζ}) :
    ContinuousOn (stopGap r w) {s : ℝ≥0 | (s : ℝ≥0∞) < ζ} :=
  continuousOn_const.sub hw.abs

/-- **Through the stop, `|w_t| ≤ r/4`.** -/
theorem abs_le_of_le_localStopPath (hw : ContinuousOn w {s : ℝ≥0 | (s : ℝ≥0∞) < ζ}) (hw0 : w 0 = 0)
    (hr : 0 ≤ r) {t : ℝ≥0} (ht : (t : WithTop ℝ≥0) ≤ localStopPath r ζ w) (htζ : (t : ℝ≥0∞) < ζ) :
    |w t| ≤ r / 4 := by
  have h := le_of_le_hitBelow (continuousOn_stopGap (r := r) hw)
    (by simp only [stopGap, hw0, abs_zero, sub_zero]; positivity) (ht.trans (min_le_right _ _)) htζ
  simp only [stopGap] at h
  linarith

/-- Through the stop, `t ≤ r²/64`. -/
theorem le_stopHorizon_of_le_localStopPath {t : ℝ≥0} (ht : (t : WithTop ℝ≥0) ≤ localStopPath r ζ w) :
    t ≤ stopHorizon r :=
  WithTop.coe_le_coe.1 (ht.trans localStopPath_le_stopHorizon)

/-- **The stop is strictly positive** (p. 247: "It is strictly positive by continuity of the driver"). -/
theorem localStopPath_pos (hw : ContinuousOn w {s : ℝ≥0 | (s : ℝ≥0∞) < ζ}) (hw0 : w 0 = 0) (hr : 0 < r)
    (hζ : 0 < ζ) : 0 < localStopPath r ζ w :=
  lt_min (WithTop.coe_lt_coe.2 (stopHorizon_pos hr))
    (hitBelow_pos (continuousOn_stopGap hw) hζ (by simp only [stopGap, hw0, abs_zero, sub_zero]; positivity))

end Stop

/-! ### The marks through the stop -/

section Marks

variable {κ : ℝ} {nL nR : ℕ} {xL : Fin nL → ℝ} {xR : Fin nR → ℝ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ}
  {w : ℝ≥0 → ℝ} {vL : Fin nL → ℝ≥0 → ℝ} {vR : Fin nR → ℝ≥0 → ℝ} {b : ℝ≥0 → ℝ} {ζ : ℝ≥0∞}

theorem toNNReal_lt_of_mem_Icc {t : ℝ≥0} (ht : (t : ℝ≥0∞) < ζ) {s : ℝ} (hs : s ∈ Icc (0 : ℝ) t) :
    (s.toNNReal : ℝ≥0∞) < ζ :=
  lt_of_le_of_lt (by exact_mod_cast Real.toNNReal_le_iff_le_coe.2 hs.2) ht

/-- **Right marks move right** (p. 247: "Every right mark in `J` has `V^j_t ≥ x_j`"). -/
theorem le_vR_of_lt (hp : Sec2.IsSLEPathUpTo κ xL xR ρL ρR w vL vR b ζ) (i : Fin nR) {t : ℝ≥0}
    (ht : (t : ℝ≥0∞) < ζ) : xR i ≤ vR i t := by
  rw [hp.vR_eq ht i]
  refine le_add_of_nonneg_right (intervalIntegral.integral_nonneg t.coe_nonneg fun s hs => ?_)
  exact div_nonneg zero_le_two (sub_nonneg.2 (hp.w_le_vR (toNNReal_lt_of_mem_Icc ht hs) i))

/-- **Left marks move left** (p. 247: "every left mark has `V^j_t ≤ x_j`"). -/
theorem vL_le_of_lt (hp : Sec2.IsSLEPathUpTo κ xL xR ρL ρR w vL vR b ζ) (i : Fin nL) {t : ℝ≥0}
    (ht : (t : ℝ≥0∞) < ζ) : vL i t ≤ xL i := by
  rw [hp.vL_eq ht i]
  refine add_le_of_nonpos_right ?_
  rw [← neg_nonneg, ← intervalIntegral.integral_neg]
  refine intervalIntegral.integral_nonneg t.coe_nonneg fun s hs => ?_
  rw [neg_nonneg]
  exact div_nonpos_of_nonneg_of_nonpos zero_le_two (sub_nonpos.2 (hp.vL_le_w (toNNReal_lt_of_mem_Icc ht hs) i))

/-- **Distant right marks stay at distance `≥ 7r`** (p. 247) while `|w_t| ≤ r/4`. -/
theorem seven_mul_le_vR_sub (hp : Sec2.IsSLEPathUpTo κ xL xR ρL ρR w vL vR b ζ)
    (hF : IsOrderedForceWord xL xR) {r : ℝ} (hr : IsSeedRadius xL xR r) {i : Fin nR} (hi : xR i ≠ 0)
    {t : ℝ≥0} (ht : (t : ℝ≥0∞) < ζ) (hwt : |w t| ≤ r / 4) : 7 * r ≤ vR i t - w t := by
  have h1 := le_vR_of_lt hp i ht
  have h2 := hr.2.2 i hi
  rw [abs_of_nonneg (hF.2.2.2 i)] at h2
  have h3 := (abs_le.1 hwt).2
  linarith [hr.1]

/-- **Distant left marks stay at distance `≥ 7r`** (p. 247) while `|w_t| ≤ r/4`. -/
theorem seven_mul_le_sub_vL (hp : Sec2.IsSLEPathUpTo κ xL xR ρL ρR w vL vR b ζ)
    (hF : IsOrderedForceWord xL xR) {r : ℝ} (hr : IsSeedRadius xL xR r) {i : Fin nL} (hi : xL i ≠ 0)
    {t : ℝ≥0} (ht : (t : ℝ≥0∞) < ζ) (hwt : |w t| ≤ r / 4) : 7 * r ≤ w t - vL i t := by
  have h1 := vL_le_of_lt hp i ht
  have h2 := hr.2.1 i hi
  rw [abs_of_nonpos (hF.2.1 i)] at h2
  have h3 := (abs_le.1 hwt).1
  linarith [hr.1]

theorem intervalIntegrable_two_div_vR_sub (hp : Sec2.IsSLEPathUpTo κ xL xR ρL ρR w vL vR b ζ) (i : Fin nR)
    {t : ℝ≥0} (ht : (t : ℝ≥0∞) < ζ) :
    IntervalIntegrable (fun s : ℝ => 2 / (vR i s.toNNReal - w s.toNNReal)) volume 0 t := by
  have h := (hp.integrable_gapR ht i).const_mul (-2)
  refine h.congr_ae (ae_of_all _ fun s => ?_)
  simp only
  rw [div_eq_mul_inv, ← neg_sub, inv_neg]
  ring

theorem intervalIntegrable_two_div_vL_sub (hp : Sec2.IsSLEPathUpTo κ xL xR ρL ρR w vL vR b ζ) (i : Fin nL)
    {t : ℝ≥0} (ht : (t : ℝ≥0∞) < ζ) :
    IntervalIntegrable (fun s : ℝ => 2 / (vL i s.toNNReal - w s.toNNReal)) volume 0 t := by
  have h := (hp.integrable_gapL ht i).const_mul (-2)
  refine h.congr_ae (ae_of_all _ fun s => ?_)
  simp only
  rw [div_eq_mul_inv, ← neg_sub, inv_neg]
  ring

/-- **The right seed marks stay merged**: two right marks started at `0` coincide before the lifetime. -/
theorem vR_eq_vR_of_xR_eq_zero (hp : Sec2.IsSLEPathUpTo κ xL xR ρL ρR w vL vR b ζ) {i j : Fin nR}
    (hi : xR i = 0) (hj : xR j = 0) {t : ℝ≥0} (ht : (t : ℝ≥0∞) < ζ) : vR i t = vR j t := by
  -- it suffices to treat `i ≤ j`
  suffices key : ∀ {i j : Fin nR}, xR i = 0 → xR j = 0 → i ≤ j → vR j t ≤ vR i t by
    rcases le_total i j with hij | hij
    · exact le_antisymm (hp.monotone_vR ht hij) (key hi hj hij)
    · exact le_antisymm (key hj hi hij) (hp.monotone_vR ht hij)
  intro i j hi hj hij
  have hdiff : vR i t - vR j t = ∫ s in (0 : ℝ)..t,
      (2 / (vR i s.toNNReal - w s.toNNReal) - 2 / (vR j s.toNNReal - w s.toNNReal)) := by
    rw [intervalIntegral.integral_sub (intervalIntegrable_two_div_vR_sub hp i ht)
      (intervalIntegrable_two_div_vR_sub hp j ht), hp.vR_eq ht i, hp.vR_eq ht j, hi, hj]
    ring
  have hnn : 0 ≤ vR i t - vR j t := by
    rw [hdiff]
    refine intervalIntegral.integral_nonneg_of_ae_restrict t.coe_nonneg ?_
    have hnull := hp.volume_collisionR i
    rw [EventuallyLE, ae_restrict_iff' measurableSet_Icc]
    refine (measure_eq_zero_iff_ae_notMem.1 hnull).mono fun s hs hsI => ?_
    have hsζ := toNNReal_lt_of_mem_Icc ht hsI
    have hne : w s.toNNReal ≠ vR i s.toNNReal := fun he => hs ⟨hsI.1, hsζ, he⟩
    have ha : 0 < vR i s.toNNReal - w s.toNNReal :=
      sub_pos.2 (lt_of_le_of_ne (hp.w_le_vR hsζ i) hne)
    have hab : vR i s.toNNReal - w s.toNNReal ≤ vR j s.toNNReal - w s.toNNReal :=
      sub_le_sub_right (hp.monotone_vR hsζ hij) _
    simp only [Pi.zero_apply, sub_nonneg]
    exact div_le_div_of_nonneg_left zero_le_two ha hab
  linarith

/-- **The left seed marks stay merged**: two left marks started at `0` coincide before the lifetime. -/
theorem vL_eq_vL_of_xL_eq_zero (hp : Sec2.IsSLEPathUpTo κ xL xR ρL ρR w vL vR b ζ) {i j : Fin nL}
    (hi : xL i = 0) (hj : xL j = 0) {t : ℝ≥0} (ht : (t : ℝ≥0∞) < ζ) : vL i t = vL j t := by
  suffices key : ∀ {i j : Fin nL}, xL i = 0 → xL j = 0 → i ≤ j → vL i t ≤ vL j t by
    rcases le_total i j with hij | hij
    · exact le_antisymm (key hi hj hij) (hp.antitone_vL ht hij)
    · exact le_antisymm (hp.antitone_vL ht hij) (key hj hi hij)
  intro i j hi hj hij
  have hdiff : vL j t - vL i t = ∫ s in (0 : ℝ)..t,
      (2 / (vL j s.toNNReal - w s.toNNReal) - 2 / (vL i s.toNNReal - w s.toNNReal)) := by
    rw [intervalIntegral.integral_sub (intervalIntegrable_two_div_vL_sub hp j ht)
      (intervalIntegrable_two_div_vL_sub hp i ht), hp.vL_eq ht i, hp.vL_eq ht j, hi, hj]
    ring
  have hnn : 0 ≤ vL j t - vL i t := by
    rw [hdiff]
    refine intervalIntegral.integral_nonneg_of_ae_restrict t.coe_nonneg ?_
    have hnull := hp.volume_collisionL i
    rw [EventuallyLE, ae_restrict_iff' measurableSet_Icc]
    refine (measure_eq_zero_iff_ae_notMem.1 hnull).mono fun s hs hsI => ?_
    have hsζ := toNNReal_lt_of_mem_Icc ht hsI
    have hne : w s.toNNReal ≠ vL i s.toNNReal := fun he => hs ⟨hsI.1, hsζ, he⟩
    have ha : 0 < w s.toNNReal - vL i s.toNNReal :=
      sub_pos.2 (lt_of_le_of_ne (hp.vL_le_w hsζ i) (Ne.symm hne))
    have hab : w s.toNNReal - vL i s.toNNReal ≤ w s.toNNReal - vL j s.toNNReal :=
      sub_le_sub_left (hp.antitone_vL hsζ hij) _
    simp only [Pi.zero_apply, sub_nonneg]
    -- `2/(vL j − w) = −2/(w − vL j) ≥ −2/(w − vL i) = 2/(vL i − w)`
    have e1 : 2 / (vL j s.toNNReal - w s.toNNReal) = -(2 / (w s.toNNReal - vL j s.toNNReal)) := by
      rw [← neg_sub, div_neg]
    have e2 : 2 / (vL i s.toNNReal - w s.toNNReal) = -(2 / (w s.toNNReal - vL i s.toNNReal)) := by
      rw [← neg_sub, div_neg]
    rw [e1, e2, neg_le_neg_iff]
    exact div_le_div_of_nonneg_left zero_le_two ha hab
  linarith

end Marks

/-! ### The hull through the stop -/

section Hull

variable {w : ℝ≥0 → ℝ} {ζ : ℝ≥0∞} {r : ℝ}

/-- **The hull through the stop lies in `B̄(0, 5r/8)`** (p. 247: "The elementary Loewner hull bounds give
`|Re z| ≤ r/4` and `0 ≤ Im z ≤ 2√S ≤ r/4` for `z ∈ K_S`. Hence `K_S ⊂ B(0, r/2) ⊂ F`"; here with QuantumZipper's
bound `K_s ⊆ B̄(0, M + 3√s)`, `M = sup |w| ≤ r/4`, `√s ≤ r/8`). -/
theorem fwdHull_subset_closedBall_of_le_localStopPath (hw : ContinuousOn w {s : ℝ≥0 | (s : ℝ≥0∞) < ζ})
    (hw0 : w 0 = 0) (hr : 0 < r) {t : ℝ≥0} (ht : (t : WithTop ℝ≥0) ≤ localStopPath r ζ w)
    (htζ : (t : ℝ≥0∞) < ζ) :
    QuantumZipper.fwdHull (fun s : ℝ => w s.toNNReal) t ⊆ closedBall 0 (5 * r / 8) := by
  obtain ⟨t₂, htt₂, ht₂ζ⟩ := ENNReal.lt_iff_exists_nnreal_btwn.1 htζ
  have htt₂' : (t : ℝ) < t₂ := by exact_mod_cast htt₂
  set A : ℝ → ℝ := Ito.clampDrv (Ito.rpath w) t₂ with hA_def
  have hA : Continuous A := Ito.continuous_clampDrv t₂.coe_nonneg (Ito.continuousOn_rpath hw ht₂ζ)
  have hK : QuantumZipper.fwdHull (fun s : ℝ => w s.toNNReal) t = QuantumZipper.fwdHull A t :=
    fwdHull_eq_of_eqOn t.coe_nonneg htt₂' fun s hs => (Ito.clampDrv_eqOn (W := Ito.rpath w) hs).symm
  rw [hK]
  rcases eq_or_ne t 0 with h0 | h0
  · intro z hz
    exfalso
    have hpos := QuantumZipper.swallowTime_pos hA hz.1
    have hle : QuantumZipper.swallowTime A z ≤ ENNReal.ofReal ((t : ℝ)) := hz.2
    rw [h0, NNReal.coe_zero, ENNReal.ofReal_zero] at hle
    exact absurd (lt_of_lt_of_le hpos hle) (lt_irrefl 0)
  · have hpos : (0 : ℝ) < t := NNReal.coe_pos.2 (pos_iff_ne_zero.2 h0)
    have htH := le_stopHorizon_of_le_localStopPath ht
    have hsq : Real.sqrt t ≤ r / 8 := by
      rw [Real.sqrt_le_left (by positivity)]
      have := NNReal.coe_le_coe.2 htH
      rw [coe_stopHorizon] at this
      nlinarith
    refine (QuantumZipper.CaraR.fwdHull_subset_closedBall hA hpos (M := r / 4) fun s hs => ?_).trans
      (closedBall_subset_closedBall (by linarith))
    rw [hA_def, Ito.clampDrv_eqOn ⟨hs.1, hs.2.trans htt₂'.le⟩]
    have hst : s.toNNReal ≤ t := Real.toNNReal_le_iff_le_coe.2 hs.2
    exact abs_le_of_le_localStopPath hw hw0 hr.le ((WithTop.coe_le_coe.2 hst).trans ht)
      (lt_of_le_of_lt (by exact_mod_cast hst) htζ)

end Hull

/-! ### The stop is strictly before the lifetime -/

section Lifetime

variable {κ : ℝ} {nL nR : ℕ} {xL : Fin nL → ℝ} {xR : Fin nR → ℝ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ}
  {w : ℝ≥0 → ℝ} {vL : Fin nL → ℝ≥0 → ℝ} {vR : Fin nR → ℝ≥0 → ℝ} {b : ℝ≥0 → ℝ} {ζ : ℝ≥0∞} {r : ℝ}

/-- The terminal-state property of Aux. lemma 3 along one path (the conclusion of
`IsIntegratedSLEEvolution.ae_tendsto_threshold`). -/
def HasThresholdLimit (ρL : Fin nL → ℝ) (ρR : Fin nR → ℝ) (w : ℝ≥0 → ℝ) (vL : Fin nL → ℝ≥0 → ℝ)
    (vR : Fin nR → ℝ≥0 → ℝ) (ζ : ℝ≥0∞) : Prop :=
  ∀ T : ℝ≥0, 0 < T → (T : ℝ≥0∞) = ζ →
    ∃ (w₀ : ℝ) (vL₀ : Fin nL → ℝ) (vR₀ : Fin nR → ℝ),
      Tendsto (fun t => (w t, fun i => vL i t, fun i => vR i t)) (𝓝[<] T) (𝓝 (w₀, vL₀, vR₀)) ∧
        ForceWord.ThresholdCondition ρL ρR w₀ vL₀ vR₀

/-- A group sum over the marks at the driver, when the distant marks are away from it and the seed marks are
merged, is the seed weight or zero. -/
theorem sum_filter_eq_zero_or_seed {n : ℕ} (x v : Fin n → ℝ) (ρ : Fin n → ℝ) (w₀ : ℝ)
    (hJ : ∀ i, x i ≠ 0 → v i ≠ w₀) (hmerge : ∀ i j, x i = 0 → x j = 0 → v i = v j) :
    (∑ i ∈ Finset.univ.filter (fun i => v i = w₀), ρ i) = 0 ∨
      (∑ i ∈ Finset.univ.filter (fun i => v i = w₀), ρ i) =
        ∑ i ∈ Finset.univ.filter (fun i => x i = 0), ρ i := by
  classical
  have hsub : Finset.univ.filter (fun i => v i = w₀) ⊆ Finset.univ.filter (fun i => x i = 0) := by
    intro i hi
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi ⊢
    by_contra hx
    exact hJ i hx hi
  rcases (Finset.univ.filter (fun i => v i = w₀)).eq_empty_or_nonempty with he | ⟨i₀, hi₀⟩
  · left
    rw [he, Finset.sum_empty]
  · right
    congr 1
    refine Finset.Subset.antisymm hsub fun j hj => ?_
    have hi₀' := Finset.mem_filter.1 hi₀
    have hx₀ : x i₀ = 0 := (Finset.mem_filter.1 (hsub hi₀)).2
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj ⊢
    rw [hmerge j i₀ hj hx₀]
    exact hi₀'.2

/-- **The local stop is strictly before the lifetime** (p. 247: "The only possible seed collisions have weights
`r_−, r_+ > −2`, so `S` is strictly before any continuation threshold"): at a finite lifetime the terminal state
satisfies the threshold condition (Aux. lemma 3), but through the stop the distant marks stay `7r` away from the
driver and the seed marks are merged with admissible total weights. -/
theorem localStopPath_lt (hp : IsIntegratedSLEPath κ xL xR ρL ρR w vL vR b ζ) (hF : IsOrderedForceWord xL xR)
    (hr : IsSeedRadius xL xR r) (hseed : ¬ ForceWord.ThresholdCondition ρL ρR 0 xL xR)
    (hterm : HasThresholdLimit ρL ρR w vL vR ζ) :
    (localStopPath r ζ w : ℝ≥0∞) < ζ := by
  have hp' := hp.isSLEPathUpTo le_rfl
  have hwc : ContinuousOn w {s : ℝ≥0 | (s : ℝ≥0∞) < ζ} := hp'.continuousOn_w
  refine lt_of_not_ge fun hle => ?_
  have hζtop : ζ ≠ ⊤ := ne_top_of_le_ne_top WithTop.coe_ne_top (hle.trans localStopPath_le_stopHorizon)
  obtain ⟨T, hT⟩ := WithTop.ne_top_iff_exists.1 hζtop
  rcases eq_or_ne T 0 with hT0 | hT0
  · exact hseed (hp.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 (by rw [← hT, hT0]; rfl))
  have hTpos : 0 < T := pos_iff_ne_zero.2 hT0
  obtain ⟨w₀, vL₀, vR₀, hlim, hth⟩ := hterm T hTpos hT
  have hne : (𝓝[<] T).NeBot := nhdsLT_neBot_of_exists_lt ⟨0, hTpos⟩
  -- every `t < T` is before the lifetime and before the stop
  have hbefore : ∀ᶠ t : ℝ≥0 in 𝓝[<] T, (t : ℝ≥0∞) < ζ ∧ (t : WithTop ℝ≥0) ≤ localStopPath r ζ w := by
    filter_upwards [self_mem_nhdsWithin] with t (ht : t < T)
    have h1 : (t : ℝ≥0∞) < ζ := by rw [← hT]; exact WithTop.coe_lt_coe.2 ht
    exact ⟨h1, h1.le.trans hle⟩
  have hw₀ : Tendsto w (𝓝[<] T) (𝓝 w₀) := (continuous_fst.tendsto _).comp hlim
  have hvR₀ : ∀ i, Tendsto (fun t => vR i t) (𝓝[<] T) (𝓝 (vR₀ i)) := fun i =>
    ((continuous_apply i).tendsto _).comp ((continuous_snd.snd.tendsto _).comp hlim)
  have hvL₀ : ∀ i, Tendsto (fun t => vL i t) (𝓝[<] T) (𝓝 (vL₀ i)) := fun i =>
    ((continuous_apply i).tendsto _).comp ((continuous_snd.fst.tendsto _).comp hlim)
  have habs : |w₀| ≤ r / 4 :=
    le_of_tendsto ((continuous_abs.tendsto _).comp hw₀)
      (hbefore.mono fun t ht => abs_le_of_le_localStopPath hwc hp.1 hr.1.le ht.2 ht.1)
  -- distant marks stay away, seed marks stay merged
  have hJR : ∀ i, xR i ≠ 0 → vR₀ i ≠ w₀ := fun i hi he => by
    have h1 : xR i ≤ vR₀ i := ge_of_tendsto (hvR₀ i) (hbefore.mono fun t ht => le_vR_of_lt hp' i ht.1)
    have h2 := hr.2.2 i hi
    rw [abs_of_nonneg (hF.2.2.2 i)] at h2
    have h3 := (abs_le.1 habs).2
    linarith [hr.1]
  have hJL : ∀ i, xL i ≠ 0 → vL₀ i ≠ w₀ := fun i hi he => by
    have h1 : vL₀ i ≤ xL i := le_of_tendsto (hvL₀ i) (hbefore.mono fun t ht => vL_le_of_lt hp' i ht.1)
    have h2 := hr.2.1 i hi
    rw [abs_of_nonpos (hF.2.1 i)] at h2
    have h3 := (abs_le.1 habs).1
    linarith [hr.1]
  have hMR : ∀ i j, xR i = 0 → xR j = 0 → vR₀ i = vR₀ j := fun i j hi hj =>
    tendsto_nhds_unique (hvR₀ i) ((hvR₀ j).congr' (hbefore.mono fun t ht =>
      (vR_eq_vR_of_xR_eq_zero hp' hi hj ht.1).symm))
  have hML : ∀ i j, xL i = 0 → xL j = 0 → vL₀ i = vL₀ j := fun i j hi hj =>
    tendsto_nhds_unique (hvL₀ i) ((hvL₀ j).congr' (hbefore.mono fun t ht =>
      (vL_eq_vL_of_xL_eq_zero hp' hi hj ht.1).symm))
  -- the seed weights are admissible
  simp only [ForceWord.ThresholdCondition, not_or, not_le] at hseed
  obtain ⟨hsL, hsR⟩ := hseed
  have hsL' : -2 < ∑ i ∈ Finset.univ.filter (fun i => xL i = 0), ρL i := by
    simpa only [eq_comm] using hsL
  have hsR' : -2 < ∑ i ∈ Finset.univ.filter (fun i => xR i = 0), ρR i := by
    simpa only [eq_comm] using hsR
  rcases hth with hL | hR
  · rcases sum_filter_eq_zero_or_seed xL vL₀ ρL w₀ hJL hML with h | h <;> rw [h] at hL <;> linarith
  · rcases sum_filter_eq_zero_or_seed xR vR₀ ρR w₀ hJR hMR with h | h <;> rw [h] at hR <;> linarith

end Lifetime

/-! ### The stop of an evolution -/

section Process

variable {κ : ℝ} {nL nR : ℕ} {xL : Fin nL → ℝ} {xR : Fin nR → ℝ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ}
  {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ} {W : ℝ≥0 → Ω → ℝ}
  {VL : Fin nL → ℝ≥0 → Ω → ℝ} {VR : Fin nR → ℝ≥0 → Ω → ℝ} {B : ℝ≥0 → Ω → ℝ} {ζ : Ω → ℝ≥0∞} {r : ℝ}
  {G : Set Ω}

/-- **The good paths of the local comparison**: the integrated path of Definition 2.1 with the terminal state of
Aux. lemma 3. -/
def IsGoodPath (κ : ℝ) (xL : Fin nL → ℝ) (xR : Fin nR → ℝ) (ρL : Fin nL → ℝ) (ρR : Fin nR → ℝ)
    (W : ℝ≥0 → Ω → ℝ) (VL : Fin nL → ℝ≥0 → Ω → ℝ) (VR : Fin nR → ℝ≥0 → Ω → ℝ) (B : ℝ≥0 → Ω → ℝ)
    (ζ : Ω → ℝ≥0∞) (ω : Ω) : Prop :=
  IsIntegratedSLEPath κ xL xR ρL ρR (fun t => W t ω) (fun i t => VL i t ω) (fun i t => VR i t ω)
      (fun t => B t ω) (ζ ω) ∧
    HasThresholdLimit ρL ρR (fun t => W t ω) (fun i t => VL i t ω) (fun i t => VR i t ω) (ζ ω)

theorem ae_isGoodPath [IsProbabilityMeasure P] (hE : IsIntegratedSLEEvolution κ xL xR ρL ρR P 𝓕 W VL VR B ζ) (hκ : 0 < κ) :
    ∀ᵐ ω ∂P, IsGoodPath κ xL xR ρL ρR W VL VR B ζ ω := by
  filter_upwards [hE.2.2.2.2, hE.ae_tendsto_threshold hκ] with ω h1 h2
  exact ⟨h1, h2⟩

/-- **A measurable good event of full measure.** -/
theorem exists_goodEvent [IsProbabilityMeasure P] (hE : IsIntegratedSLEEvolution κ xL xR ρL ρR P 𝓕 W VL VR B ζ) (hκ : 0 < κ) :
    ∃ G : Set Ω, MeasurableSet G ∧ P Gᶜ = 0 ∧ ∀ ω ∈ G, IsGoodPath κ xL xR ρL ρR W VL VR B ζ ω := by
  obtain ⟨N, hN, hNm, hN0⟩ := exists_measurable_superset_of_null (ae_iff.1 (ae_isGoodPath hE hκ))
  refine ⟨Nᶜ, hNm.compl, by rwa [compl_compl], fun ω hω => ?_⟩
  by_contra h
  exact hω (hN h)

theorem IsGoodPath.continuousOn_W {ω : Ω} (hg : IsGoodPath κ xL xR ρL ρR W VL VR B ζ ω) :
    ContinuousOn (fun t => W t ω) {s : ℝ≥0 | (s : ℝ≥0∞) < ζ ω} :=
  hg.1.2.2.2.1

theorem IsGoodPath.W_zero {ω : Ω} (hg : IsGoodPath κ xL xR ρL ρR W VL VR B ζ ω) : W 0 ω = 0 :=
  hg.1.1

theorem IsGoodPath.isSLEPathUpTo {ω : Ω} (hg : IsGoodPath κ xL xR ρL ρR W VL VR B ζ ω) :
    Sec2.IsSLEPathUpTo κ xL xR ρL ρR (fun t => W t ω) (fun i t => VL i t ω) (fun i t => VR i t ω)
      (fun t => B t ω) (ζ ω) :=
  hg.1.isSLEPathUpTo le_rfl

/-- On a good path with an admissible seed, the lifetime is positive. -/
theorem IsGoodPath.zeta_pos {ω : Ω} (hg : IsGoodPath κ xL xR ρL ρR W VL VR B ζ ω)
    (hseed : ¬ ForceWord.ThresholdCondition ρL ρR 0 xL xR) : 0 < ζ ω := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, h19, -⟩ := hg.1
  exact pos_iff_ne_zero.2 fun h0 => hseed (h19 h0)

/-- **The stop is positive** (everywhere: on `G` by continuity, off `G` it is the horizon). -/
theorem localStop_pos (hG : ∀ ω ∈ G, IsGoodPath κ xL xR ρL ρR W VL VR B ζ ω)
    (hseed : ¬ ForceWord.ThresholdCondition ρL ρR 0 xL xR) (hr : 0 < r) (ω : Ω) :
    0 < localStop r G ζ W ω := by
  by_cases hω : ω ∈ G
  · rw [localStop_of_mem hω]
    exact localStopPath_pos (hG ω hω).continuousOn_W (hG ω hω).W_zero hr ((hG ω hω).zeta_pos hseed)
  · rw [localStop_of_notMem hω]
    exact WithTop.coe_lt_coe.2 (stopHorizon_pos hr)

/-- **The stop is before the lifetime** on the good event. -/
theorem localStop_lt (hG : ∀ ω ∈ G, IsGoodPath κ xL xR ρL ρR W VL VR B ζ ω) (hF : IsOrderedForceWord xL xR)
    (hr : IsSeedRadius xL xR r) (hseed : ¬ ForceWord.ThresholdCondition ρL ρR 0 xL xR) {ω : Ω} (hω : ω ∈ G) :
    (localStop r G ζ W ω : ℝ≥0∞) < ζ ω := by
  rw [localStop_of_mem hω]
  exact localStopPath_lt (hG ω hω).1 hF hr hseed (hG ω hω).2

/-- **The local stop is a stopping time** of every right-continuous filtration in which the coordinates are adapted
before the lifetime and which contains the good event at time `0`. -/
theorem isStoppingTime_localStop {𝓖 : Filtration ℝ≥0 mΩ} [𝓖.IsRightContinuous] (hW : AdaptedBefore 𝓖 ζ W)
    (hVL : ∀ i, AdaptedBefore 𝓖 ζ (VL i)) (hVR : ∀ i, AdaptedBefore 𝓖 ζ (VR i))
    (hG0 : MeasurableSet[𝓖 0] G) (hG : ∀ ω ∈ G, IsGoodPath κ xL xR ρL ρR W VL VR B ζ ω) (r : ℝ) :
    IsStoppingTime 𝓖 (localStop r G ζ W) := by
  have hc : ∀ ω ∈ G, ContinuousOn (fun s => stateAt W VL VR s ω) {s : ℝ≥0 | (s : ℝ≥0∞) < ζ ω} :=
    fun ω hω => (hG ω hω).1.2.2.2.1.prodMk ((continuousOn_pi.2 (hG ω hω).1.2.2.2.2.1).prodMk
      (continuousOn_pi.2 (hG ω hω).1.2.2.2.2.2.1))
  have h := isStoppingTime_hitBelow_state hW hVL hVR hG0 hc
    (Φ := fun p : ℝ × (Fin nL → ℝ) × (Fin nR → ℝ) => r / 4 - |p.1|)
    (continuous_const.sub continuous_fst.abs) 0
  exact (isStoppingTime_const 𝓖 (stopHorizon r)).min h

/-- The good event is an event of the driving filtration at time `0`. -/
theorem measurableSet_drivingFiltration_zero_of_null_compl (hX : IsMeasurableKilledDriving W VL VR ζ)
    (hGm : MeasurableSet G) (hG0 : P Gᶜ = 0) : MeasurableSet[drivingFiltration P hX 0] G := by
  have h := Ito.measurableSet_usualAugmentation_of_null (𝓕 := killedDrivingFiltration hX) hGm.compl hG0 0
  have h2 : MeasurableSet[usualAugmentation (killedDrivingFiltration hX) P 0] G := by simpa using h.compl
  exact h2

/-- **The local stop is a stopping time of the frozen driving filtration.** -/
theorem isStoppingTime_localStop_drivingFiltration (hX : IsMeasurableKilledDriving W VL VR ζ)
    (hGm : MeasurableSet G) (hG0 : P Gᶜ = 0) (hG : ∀ ω ∈ G, IsGoodPath κ xL xR ρL ρR W VL VR B ζ ω) (r : ℝ) :
    IsStoppingTime (drivingFiltration P hX) (localStop r G ζ W) := by
  have : (drivingFiltration P hX).IsRightContinuous := by
    unfold drivingFiltration usualAugmentation; infer_instance
  have hle : killedDrivingFiltration hX ≤ drivingFiltration P hX := Ito.le_usualAugmentation _ P
  exact isStoppingTime_localStop (Ito.adaptedBefore_mono hle (adaptedBefore_killedDriving_W hX))
    (fun i => Ito.adaptedBefore_mono hle (adaptedBefore_killedDriving_VL hX i))
    (fun i => Ito.adaptedBefore_mono hle (adaptedBefore_killedDriving_VR hX i))
    (measurableSet_drivingFiltration_zero_of_null_compl hX hGm hG0) hG r

end Process

end LocalExt

end InteractingSLE
