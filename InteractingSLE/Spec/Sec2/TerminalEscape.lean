/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec2.TerminalPath

/-!
# Behaviour of the integrated `SLE_κ(ρ)` driving evolution at a finite lifetime (pathwise part)

Packet PROVE-SEC2-TERM. Specification pp. 21–28: the nonaccumulation argument in the proof of
Theorem 2.2 (`source/spec/p001-048.md` L494) and the proof of Aux. lemma 3 (L555–L650). All results
are deterministic statements about one path satisfying `Sec2.IsForcePath` (every condition of
Definition 2.1 except the driving equation) and `Sec2.DriverEq` (the driving equation), with a
driving path `b` continuous on `[0, T]` at a finite lifetime `ζ = T`.

* `IsForcePath.exists_noCollision`: before a positive lifetime there is a time at which the driver
  is separated from every force point.
* `IsForcePath.vL_ge_of_gap` (the source's `d/dt (m − V)² ≤ 4`): a left force coordinate moves at
  speed at most `2` while its gap to the driver is at least `1`; hence it cannot escape to `−∞`
  while `W` stays bounded below (`IsForcePath.bddBelow_vL_of_bddBelow_w`).
* `IsForcePath.abs_w_sub_le_of_strip` (the nonaccumulation estimate): while the driver stays in a
  strip at distance `δ` from all force points, `|W_q − W_p| ≤ √κ |B_q − B_p| + C (q − p)` with
  `C = δ⁻¹ ∑ |ρ^{i,q}|`.
* `IsForcePath.not_unbounded_both` ("at most one side can escape"): `W` cannot be unbounded both
  below and above before a finite lifetime.
* `IsForcePath.sum_ρL_eq_neg_two_of_escape` (the (N4) argument): if the left side escapes and the
  right side stays bounded, the left side total is exactly `−2`.
* `IsForcePath.tendsto_or_criticalEscape`: at a finite positive lifetime either all coordinates have
  finite limits (and, by maximality, the limiting state satisfies the threshold condition), or one
  side escapes with side total exactly `−2` (the critical case, excluded probabilistically in
  `TerminalCritical`).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology
open scoped NNReal ENNReal

namespace InteractingSLE

namespace Sec2

/-! ### Real-analysis helpers -/

/-- **Crossing extraction.** If a continuous `f` on `[u, v]` starts at or below `α` and ends at or
above `β`, there is a subinterval `[u', v']` with `f u' ≤ α`, `β ≤ f v'` on which `f` stays strictly
between `α` and `β` in the interior. -/
theorem exists_crossing {f : ℝ≥0 → ℝ} {u v : ℝ≥0} (huv : u ≤ v) (hf : ContinuousOn f (Icc u v))
    {α β : ℝ} (hu : f u ≤ α) (hv : β ≤ f v) :
    ∃ u' v', u ≤ u' ∧ u' ≤ v' ∧ v' ≤ v ∧ f u' ≤ α ∧ β ≤ f v' ∧
      ∀ s, u' < s → s < v' → α < f s ∧ f s < β := by
  set A := Icc u v ∩ f ⁻¹' Iic α with hA
  have hAc : IsCompact A :=
    isCompact_Icc.of_isClosed_subset (hf.preimage_isClosed_of_isClosed isClosed_Icc isClosed_Iic)
      inter_subset_left
  have hAne : A.Nonempty := ⟨u, ⟨le_rfl, huv⟩, hu⟩
  have hAbdd : BddAbove A := bddAbove_Icc.mono inter_subset_left
  set u' := sSup A
  have hu'A : u' ∈ A := hAc.sSup_mem hAne
  have hf' : ContinuousOn f (Icc u' v) := hf.mono (Icc_subset_Icc hu'A.1.1 le_rfl)
  set B := Icc u' v ∩ f ⁻¹' Ici β with hB
  have hBc : IsCompact B :=
    isCompact_Icc.of_isClosed_subset (hf'.preimage_isClosed_of_isClosed isClosed_Icc isClosed_Ici)
      inter_subset_left
  have hBne : B.Nonempty := ⟨v, ⟨hu'A.1.2, le_rfl⟩, hv⟩
  have hBbdd : BddBelow B := bddBelow_Icc.mono inter_subset_left
  set v' := sInf B
  have hv'B : v' ∈ B := hBc.sInf_mem hBne
  refine ⟨u', v', hu'A.1.1, hv'B.1.1, hv'B.1.2, hu'A.2, hv'B.2, fun s hs1 hs2 => ⟨?_, ?_⟩⟩
  · by_contra hcon
    have hsA : s ∈ A := ⟨⟨hu'A.1.1.trans hs1.le, hs2.le.trans hv'B.1.2⟩, not_lt.1 hcon⟩
    exact absurd (le_csSup hAbdd hsA) (not_le.2 hs1)
  · by_contra hcon
    have hsB : s ∈ B := ⟨⟨hs1.le, hs2.le.trans hv'B.1.2⟩, not_lt.1 hcon⟩
    exact absurd (csInf_le hBbdd hsB) (not_le.2 hs2)

/-- A finite family of positive reals has a positive lower bound. -/
theorem exists_pos_le_of_pos {n : ℕ} {g : Fin n → ℝ} (hg : ∀ i, 0 < g i) :
    ∃ ε > 0, ∀ i, ε ≤ g i := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · exact ⟨1, one_pos, fun i => i.elim0⟩
  · have : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
    obtain ⟨i₀, -, hi₀⟩ := Finset.univ.exists_min_image g Finset.univ_nonempty
    exact ⟨g i₀, hg i₀, fun i => hi₀ i (Finset.mem_univ i)⟩

/-- The set of times before `ζ` as `Iio T` when `ζ = T`. -/
theorem setOf_lt_coe_eq_Iio (T : ℝ≥0) : {t : ℝ≥0 | (t : ℝ≥0∞) < (T : ℝ≥0∞)} = Iio T := by
  ext; simp

/-- **Drift bound in a strip.** If at real time `r` all left force points are at most `L`, all right
ones at least `R`, and the driver is in `[L + δ, R − δ]`, then the driving drift is at most
`δ⁻¹ ∑ |ρ^{i,q}|` in absolute value. -/
theorem abs_driverDrift_le {nL nR : ℕ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ} {w : ℝ≥0 → ℝ}
    {vL : Fin nL → ℝ≥0 → ℝ} {vR : Fin nR → ℝ≥0 → ℝ} {r L R δ : ℝ} (hδ : 0 < δ)
    (hL : ∀ i, vL i r.toNNReal ≤ L) (hR : ∀ j, R ≤ vR j r.toNNReal)
    (h1 : L + δ ≤ w r.toNNReal) (h2 : w r.toNNReal ≤ R - δ) :
    |driverDrift ρL ρR w vL vR r| ≤ (∑ i, |ρL i| + ∑ j, |ρR j|) / δ := by
  have bound : ∀ (ρ x : ℝ), δ ≤ |x| → |ρ / x| ≤ |ρ| / δ := fun ρ x hx => by
    rw [abs_div]
    exact div_le_div_of_nonneg_left (abs_nonneg ρ) hδ hx
  unfold driverDrift
  rw [add_div, Finset.sum_div, Finset.sum_div]
  refine (abs_add_le _ _).trans (add_le_add ?_ ?_)
  · refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i _ => bound _ _ ?_)
    rw [abs_of_nonneg (by linarith [hL i])]
    linarith [hL i]
  · refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun j _ => bound _ _ ?_)
    rw [abs_of_nonpos (by linarith [hR j])]
    linarith [hR j]

/-- A nonempty `Fin n` has a largest element. -/
theorem exists_forall_le_fin {n : ℕ} (i : Fin n) : ∃ o : Fin n, ∀ j, j ≤ o :=
  ⟨⟨n - 1, by have := i.isLt; omega⟩, fun j => Fin.le_iff_val_le_val.2 (by
    have := j.isLt; simp only; omega)⟩

namespace IsForcePath

variable {a : ℝ} {nL nR : ℕ} {xL : Fin nL → ℝ} {xR : Fin nR → ℝ} {ρL : Fin nL → ℝ}
  {ρR : Fin nR → ℝ} {w : ℝ≥0 → ℝ} {vL : Fin nL → ℝ≥0 → ℝ} {vR : Fin nR → ℝ≥0 → ℝ}
  {b : ℝ≥0 → ℝ} {ζ : ℝ≥0∞}

section Separation

variable (h : IsForcePath xL xR ρL ρR w vL vR ζ)
include h

/-- Before a positive lifetime there is a time at which the driver is strictly separated from every
force point (the collision sets are Lebesgue-null). -/
theorem exists_noCollision (hζ : 0 < ζ) :
    ∃ t : ℝ≥0, (t : ℝ≥0∞) < ζ ∧ (∀ i, vL i t < w t) ∧ ∀ j, w t < vR j t := by
  obtain ⟨T', hT'0, hT'ζ⟩ : ∃ T' : ℝ≥0, 0 < T' ∧ (T' : ℝ≥0∞) < ζ := by
    obtain ⟨T', hT'⟩ := ENNReal.lt_iff_exists_nnreal_btwn.1 hζ
    exact ⟨T', by exact_mod_cast hT'.1, hT'.2⟩
  set N : Set ℝ := (⋃ i, {s : ℝ | 0 ≤ s ∧ (s.toNNReal : ℝ≥0∞) < ζ ∧ w s.toNNReal = vL i s.toNNReal})
    ∪ ⋃ j, {s : ℝ | 0 ≤ s ∧ (s.toNNReal : ℝ≥0∞) < ζ ∧ w s.toNNReal = vR j s.toNNReal}
  have hN : volume N = 0 :=
    measure_union_null (measure_iUnion_null h.volume_collisionL)
      (measure_iUnion_null h.volume_collisionR)
  have hpos : volume (Ioo (0 : ℝ) T' \ N) ≠ 0 := by
    rw [measure_sdiff_null hN, Real.volume_Ioo]
    simpa using hT'0.ne'
  obtain ⟨s, ⟨hs0, hsT⟩, hsN⟩ := nonempty_of_measure_ne_zero hpos
  have hst : s.toNNReal ≤ T' := Real.toNNReal_le_iff_le_coe.2 hsT.le
  have hlt : (s.toNNReal : ℝ≥0∞) < ζ := lt_of_le_of_lt (by exact_mod_cast hst) hT'ζ
  refine ⟨s.toNNReal, hlt, fun i => ?_, fun j => ?_⟩
  · refine lt_of_le_of_ne (h.vL_le_w hlt i) fun he => hsN (Or.inl ?_)
    exact mem_iUnion.2 ⟨i, hs0.le, hlt, he.symm⟩
  · refine lt_of_le_of_ne (h.w_le_vR hlt j) fun he => hsN (Or.inr ?_)
    exact mem_iUnion.2 ⟨j, hs0.le, hlt, he⟩

/-- **Separated nearest marks** (Specification p. 22, "fix a time `t₀` at which the nearest left and
right marks are separated"): there are `t₀ < ζ` and `L < R` with all left force points at most `L`
and all right ones at least `R` from `t₀` on. -/
theorem exists_separated (hζ : 0 < ζ) :
    ∃ (t₀ : ℝ≥0) (L R : ℝ), (t₀ : ℝ≥0∞) < ζ ∧ L < R ∧
      ∀ s : ℝ≥0, t₀ ≤ s → (s : ℝ≥0∞) < ζ → (∀ i, vL i s ≤ L) ∧ ∀ j, R ≤ vR j s := by
  obtain ⟨t₀, ht₀, hL, hR⟩ := h.exists_noCollision hζ
  obtain ⟨ε₁, hε₁, h₁⟩ := exists_pos_le_of_pos fun i => sub_pos.2 (hL i)
  obtain ⟨ε₂, hε₂, h₂⟩ := exists_pos_le_of_pos fun j => sub_pos.2 (hR j)
  refine ⟨t₀, w t₀ - ε₁, w t₀ + ε₂, ht₀, by linarith, fun s hs hsζ => ⟨fun i => ?_, fun j => ?_⟩⟩
  · linarith [h.vL_le_of_le hs hsζ i, h₁ i]
  · linarith [h.le_vR_of_le hs hsζ j, h₂ j]

end Separation

section Rate

variable (h : IsForcePath xL xR ρL ρR w vL vR ζ)
include h

/-- While its gap to the driver is at least `1` on `[p, q]`, a left force point decreases at speed at
most `2`: `v^{i,L}_q ≥ v^{i,L}_p − 2 (q − p)`. -/
theorem vL_sub_ge_of_gap {i : Fin nL} {p q : ℝ≥0} (hpq : p ≤ q) (hq : (q : ℝ≥0∞) < ζ)
    (hgap : ∀ s : ℝ≥0, p ≤ s → s ≤ q → 1 ≤ w s - vL i s) :
    vL i p - 2 * ((q : ℝ) - p) ≤ vL i q := by
  have hpq' : (p : ℝ) ≤ q := by exact_mod_cast hpq
  have hint : IntervalIntegrable (fun r : ℝ => 2 / (vL i r.toNNReal - w r.toNNReal)) volume p q :=
    (h.intervalIntegrable_forceL hq i).mono_set (by
      rw [uIcc_of_le hpq', uIcc_of_le (NNReal.coe_nonneg q)]
      exact Icc_subset_Icc (NNReal.coe_nonneg p) le_rfl)
  have hle : ∫ _ in (p : ℝ)..q, (-2 : ℝ) ≤
      ∫ r in (p : ℝ)..q, 2 / (vL i r.toNNReal - w r.toNNReal) := by
    refine intervalIntegral.integral_mono_on hpq' intervalIntegrable_const hint fun r hr => ?_
    have hr0 : (0 : ℝ) ≤ r := (NNReal.coe_nonneg p).trans hr.1
    have hg := hgap _ ((Real.le_toNNReal_iff_coe_le hr0).2 hr.1)
      (Real.toNNReal_le_iff_le_coe.2 hr.2)
    rw [← neg_sub, div_neg]
    have : 2 / (w r.toNNReal - vL i r.toNNReal) ≤ 2 := by
      rw [div_le_iff₀ (by linarith)]
      linarith
    linarith
  rw [intervalIntegral.integral_const, smul_eq_mul, ← h.vL_sub hpq hq i] at hle
  linarith

/-- **A left force point cannot run away while its gap to the driver is large** (Specification
p. 26, `d/dt (m − V_t)² ≤ 4`): if the gap is at least `1` whenever `v^{i,L} ≤ m`, then
`v^{i,L}_t ≥ min (x^{i,L}, m) − 2t` before `ζ`. -/
theorem vL_ge_of_gap {i : Fin nL} {m : ℝ}
    (hgap : ∀ s : ℝ≥0, (s : ℝ≥0∞) < ζ → vL i s ≤ m → 1 ≤ w s - vL i s) {t : ℝ≥0}
    (ht : (t : ℝ≥0∞) < ζ) : min (xL i) m - 2 * (t : ℝ) ≤ vL i t := by
  have ht0 : (0 : ℝ) ≤ t := NNReal.coe_nonneg t
  have hlt : ∀ s : ℝ≥0, s ≤ t → (s : ℝ≥0∞) < ζ := fun s hs =>
    lt_of_le_of_lt (by exact_mod_cast hs) ht
  rcases le_or_gt m (vL i t) with hmt | hmt
  · linarith [min_le_right (xL i) m]
  rcases le_or_gt (xL i) m with hx | hx
  · have := h.vL_sub_ge_of_gap (zero_le : (0 : ℝ≥0) ≤ t) ht fun s _ hst =>
      hgap s (hlt s hst) ((h.vL_le_of_le (zero_le : (0 : ℝ≥0) ≤ s) (hlt s hst) i).trans
        (by rw [h.vL_zero i]; exact hx))
    rw [h.vL_zero i, NNReal.coe_zero, sub_zero] at this
    linarith [min_le_left (xL i) m]
  · have hcont : ContinuousOn (vL i) (Icc 0 t) :=
      (h.continuousOn_vL i).mono fun s hs => hlt s hs.2
    obtain ⟨s₀, hs₀, hs₀m⟩ := intermediate_value_Icc' (zero_le : (0 : ℝ≥0) ≤ t) hcont
      ⟨hmt.le, by rw [h.vL_zero i]; exact hx.le⟩
    have := h.vL_sub_ge_of_gap hs₀.2 ht fun s hs₀s hst =>
      hgap s (hlt s hst) ((h.vL_le_of_le hs₀s (hlt s hst) i).trans hs₀m.le)
    rw [hs₀m] at this
    linarith [min_le_right (xL i) m, NNReal.coe_nonneg s₀]

/-- If the driver is bounded below by `m` before `ζ`, every left force point is bounded below:
`v^{i,L}_t ≥ min (x^{i,L}, m − 1) − 2t`. -/
theorem vL_ge_of_le_w {m : ℝ} (hm : ∀ s : ℝ≥0, (s : ℝ≥0∞) < ζ → m ≤ w s) (i : Fin nL)
    {t : ℝ≥0} (ht : (t : ℝ≥0∞) < ζ) : min (xL i) (m - 1) - 2 * (t : ℝ) ≤ vL i t :=
  h.vL_ge_of_gap (fun s hs hvs => by linarith [hm s hs]) ht

end Rate

section Strip

variable (h : IsForcePath xL xR ρL ρR w vL vR ζ)
include h

/-- **Increment bound of the driver** from the driving equation and a bound `C` on the drift in the
open interval `(p, q)`: `|w_q − w_p| ≤ √a |b_q − b_p| + C (q − p)`. -/
theorem abs_w_sub_le (hw : DriverEq a ρL ρR w vL vR b ζ) {p q : ℝ≥0} (hpq : p ≤ q)
    (hq : (q : ℝ≥0∞) < ζ) {C : ℝ}
    (hC : ∀ r : ℝ, (p : ℝ) < r → r < q → |driverDrift ρL ρR w vL vR r| ≤ C) :
    |w q - w p| ≤ Real.sqrt a * |b q - b p| + C * ((q : ℝ) - p) := by
  have hpq' : (p : ℝ) ≤ q := by exact_mod_cast hpq
  have hint : ‖∫ r in (p : ℝ)..q, driverDrift ρL ρR w vL vR r‖ ≤ C * |(q : ℝ) - p| := by
    refine intervalIntegral.norm_integral_le_of_norm_le_const_ae ?_
    filter_upwards [Measure.ae_ne volume (q : ℝ)] with r hrq hr
    rw [uIoc_of_le hpq'] at hr
    rw [Real.norm_eq_abs]
    exact hC r hr.1 (lt_of_le_of_ne hr.2 hrq)
  rw [Real.norm_eq_abs, abs_of_nonneg (sub_nonneg.2 hpq')] at hint
  rw [h.w_sub hw hpq hq]
  calc |Real.sqrt a * (b q - b p) + ∫ r in (p : ℝ)..q, driverDrift ρL ρR w vL vR r|
      ≤ |Real.sqrt a * (b q - b p)| + |∫ r in (p : ℝ)..q, driverDrift ρL ρR w vL vR r| :=
        abs_add_le _ _
    _ ≤ Real.sqrt a * |b q - b p| + C * ((q : ℝ) - p) := by
        rw [abs_mul, abs_of_nonneg (Real.sqrt_nonneg a)]
        exact add_le_add le_rfl hint

/-- **The nonaccumulation estimate** (Specification p. 22): if on `[p, q]` all left force points are
at most `L` and all right ones at least `R`, and in `(p, q)` the driver stays in `[L + δ, R − δ]`,
then `|w_q − w_p| ≤ √a |b_q − b_p| + δ⁻¹ (∑ |ρ^{i,L}| + ∑ |ρ^{j,R}|) (q − p)`. -/
theorem abs_w_sub_le_of_strip (hw : DriverEq a ρL ρR w vL vR b ζ) {L R δ : ℝ} (hδ : 0 < δ)
    {p q : ℝ≥0} (hpq : p ≤ q) (hq : (q : ℝ≥0∞) < ζ)
    (hsep : ∀ s : ℝ≥0, p ≤ s → s ≤ q → (∀ i, vL i s ≤ L) ∧ ∀ j, R ≤ vR j s)
    (hstrip : ∀ s : ℝ≥0, p < s → s < q → L + δ ≤ w s ∧ w s ≤ R - δ) :
    |w q - w p| ≤ Real.sqrt a * |b q - b p|
      + (∑ i, |ρL i| + ∑ j, |ρR j|) / δ * ((q : ℝ) - p) := by
  refine h.abs_w_sub_le hw hpq hq fun r hpr hrq => ?_
  have hp' : p < r.toNNReal := Real.lt_toNNReal_iff_coe_lt.2 hpr
  have hq' : r.toNNReal < q :=
    (Real.toNNReal_lt_iff_lt_coe ((NNReal.coe_nonneg p).trans hpr.le)).2 hrq
  obtain ⟨hL, hR⟩ := hsep _ hp'.le hq'.le
  obtain ⟨h1, h2⟩ := hstrip _ hp' hq'
  exact abs_driverDrift_le hδ hL hR h1 h2

end Strip

section TwoSided

variable (h : IsForcePath xL xR ρL ρR w vL vR ζ)
include h

/-- **Nonaccumulation of crossings** (Specification p. 22, "each such crossing takes at least `δ`
units of time"): if from time `t₀` on all left force points are at most `L` and all right ones at
least `R > L`, and `b` is continuous on `[0, T]`, there is `δ > 0` such that every passage of the
driver across the middle third `[L + d/3, R − d/3]` (`d = R − L`) inside `[t₀, T]` before `ζ` takes
at least `δ`. The proof: in the middle third every force gap is at least `d/3`, so the drift is at
most `C = 3 d⁻¹ ∑ |ρ^{i,q}|`, and uniform continuity of `b` gives `δ` with
`√κ |b_q − b_p| + C (q − p) < d/3` whenever `q − p < δ`. -/
theorem exists_pos_crossing_time (hw : DriverEq a ρL ρR w vL vR b ζ) {T : ℝ≥0}
    (hb : ContinuousOn b (Icc 0 T)) {t₀ : ℝ≥0} {L R : ℝ} (hLR : L < R)
    (hsep : ∀ s : ℝ≥0, t₀ ≤ s → (s : ℝ≥0∞) < ζ → (∀ i, vL i s ≤ L) ∧ ∀ j, R ≤ vR j s) :
    ∃ δ > 0, ∀ p q : ℝ≥0, t₀ ≤ p → p ≤ q → q ≤ T → (q : ℝ≥0∞) < ζ →
      (∀ s, p < s → s < q → L + (R - L) / 3 < w s ∧ w s < R - (R - L) / 3) →
      (R - L) / 3 ≤ |w q - w p| → δ ≤ (q : ℝ) - p := by
  set d := R - L with hd
  have hd0 : 0 < d := sub_pos.2 hLR
  set K := ∑ i, |ρL i| + ∑ j, |ρR j| with hK
  have hK0 : 0 ≤ K := add_nonneg (Finset.sum_nonneg fun _ _ => abs_nonneg _)
    (Finset.sum_nonneg fun _ _ => abs_nonneg _)
  set C := K / (d / 3) with hC
  have hC0 : 0 ≤ C := div_nonneg hK0 (by positivity)
  have huc := isCompact_Icc.uniformContinuousOn_of_continuous hb
  rw [Metric.uniformContinuousOn_iff] at huc
  have hsa : 0 ≤ Real.sqrt a := Real.sqrt_nonneg a
  obtain ⟨δ₁, hδ₁, hδ₁b⟩ := huc (d / (6 * (Real.sqrt a + 1))) (by positivity)
  refine ⟨min δ₁ (d / (6 * (C + 1))), lt_min hδ₁ (by positivity),
    fun p q hp hpq hqT hqζ hstrip hcross => ?_⟩
  by_contra hcon
  have hqp : (q : ℝ) - p < min δ₁ (d / (6 * (C + 1))) := not_le.1 hcon
  have hest := h.abs_w_sub_le_of_strip hw (L := L) (R := R) (δ := d / 3) (by positivity) hpq hqζ
    (fun s hps hsq => hsep s (hp.trans hps) (lt_of_le_of_lt (by exact_mod_cast hsq) hqζ))
    (fun s hps hsq => ⟨(hstrip s hps hsq).1.le, (hstrip s hps hsq).2.le⟩)
  have hqp0 : (0 : ℝ) ≤ (q : ℝ) - p := sub_nonneg.2 (by exact_mod_cast hpq)
  have hbqp : |b q - b p| < d / (6 * (Real.sqrt a + 1)) := by
    have hdist : dist q p < δ₁ := by
      rw [NNReal.dist_eq, abs_of_nonneg hqp0]
      exact hqp.trans_le (min_le_left _ _)
    have := hδ₁b q ⟨zero_le, hqT⟩ p ⟨zero_le, hpq.trans hqT⟩ hdist
    rwa [Real.dist_eq] at this
  have h2 : Real.sqrt a * |b q - b p| < d / 6 := by
    calc Real.sqrt a * |b q - b p| ≤ (Real.sqrt a + 1) * |b q - b p| := by
          nlinarith [abs_nonneg (b q - b p)]
      _ < (Real.sqrt a + 1) * (d / (6 * (Real.sqrt a + 1))) :=
          mul_lt_mul_of_pos_left hbqp (by positivity)
      _ = d / 6 := by field_simp
  have h3 : C * ((q : ℝ) - p) < d / 6 := by
    calc C * ((q : ℝ) - p) ≤ C * (d / (6 * (C + 1))) :=
          mul_le_mul_of_nonneg_left (hqp.le.trans (min_le_right _ _)) hC0
      _ < d / 6 := by
          rw [mul_div_assoc', div_lt_div_iff₀ (by positivity) (by norm_num)]
          nlinarith
  rw [← hC] at hest
  linarith

/-- **At most one side can escape** (Specification p. 26, with the nonaccumulation argument of
p. 22): before a finite lifetime `ζ = T`, with `b` continuous on `[0, T]`, the driver cannot be
unbounded both below and above. Proof: fix separated marks `L < R` from a time `t₀` on; in the last
window of length `δ` (`exists_pos_crossing_time`) before `T` the driver would have to cross the
middle third, which takes at least `δ`. -/
theorem not_unbounded_both (hw : DriverEq a ρL ρR w vL vR b ζ) {T : ℝ≥0}
    (hζ : (T : ℝ≥0∞) = ζ) (hb : ContinuousOn b (Icc 0 T))
    (hbelow : ∀ m : ℝ, ∃ s : ℝ≥0, s < T ∧ w s < m)
    (habove : ∀ m : ℝ, ∃ s : ℝ≥0, s < T ∧ m < w s) : False := by
  subst hζ
  have hlt : ∀ s : ℝ≥0, s < T → (s : ℝ≥0∞) < T := fun s hs => by exact_mod_cast hs
  obtain ⟨s₀, hs₀T, -⟩ := hbelow 0
  have hT : (0 : ℝ≥0∞) < T := by exact_mod_cast (zero_le : (0 : ℝ≥0) ≤ s₀).trans_lt hs₀T
  obtain ⟨t₀, L, R, ht₀, hLR, hsep⟩ := h.exists_separated hT
  have ht₀T : t₀ < T := by exact_mod_cast ht₀
  have hTpos : (0 : ℝ) < T := by exact_mod_cast (zero_le : (0 : ℝ≥0) ≤ t₀).trans_lt ht₀T
  obtain ⟨δ, hδ0, hδ⟩ := h.exists_pos_crossing_time hw hb hLR hsep
  set t₁ : ℝ≥0 := max t₀ (Real.toNNReal ((T : ℝ) - δ / 2)) with ht₁
  have ht₁T : t₁ < T := by
    refine max_lt ht₀T ?_
    have := (Real.toNNReal_lt_toNNReal_iff hTpos).2 (by linarith : (T : ℝ) - δ / 2 < T)
    simpa using this
  have hTt₁ : (T : ℝ) - t₁ < δ := by
    have h1 : ((T : ℝ) - δ / 2) ≤ (Real.toNNReal ((T : ℝ) - δ / 2) : ℝ) := Real.le_coe_toNNReal _
    have h2 : (Real.toNNReal ((T : ℝ) - δ / 2) : ℝ) ≤ t₁ := NNReal.coe_le_coe.2 (le_max_right _ _)
    linarith
  have hcw : ContinuousOn w (Icc 0 t₁) :=
    h.continuousOn_w.mono fun s hs => hlt s (hs.2.trans_lt ht₁T)
  obtain ⟨M, hM⟩ := isCompact_Icc.exists_bound_of_continuousOn hcw
  set α := L + (R - L) / 3 with hα
  set β := R - (R - L) / 3 with hβ
  obtain ⟨u, huT, hu⟩ := hbelow (min α (-M))
  obtain ⟨v, hvT, hv⟩ := habove (max β M)
  have ht₁u : t₁ < u := by
    by_contra hc
    have := hM u ⟨zero_le, not_lt.1 hc⟩
    rw [Real.norm_eq_abs] at this
    linarith [(abs_le.1 this).1, min_le_right α (-M)]
  have ht₁v : t₁ < v := by
    by_contra hc
    have := hM v ⟨zero_le, not_lt.1 hc⟩
    rw [Real.norm_eq_abs] at this
    linarith [(abs_le.1 this).2, le_max_right β M]
  -- a crossing inside the last window is too short
  have key : ∀ p q : ℝ≥0, t₁ ≤ p → p ≤ q → q < T →
      (∀ s, p < s → s < q → α < w s ∧ w s < β) → (R - L) / 3 ≤ |w q - w p| → False := by
    intro p q hp hpq hqT hstrip hcross
    have := hδ p q ((le_max_left _ _).trans hp) hpq hqT.le (hlt q hqT) hstrip hcross
    have : (t₁ : ℝ) ≤ p := by exact_mod_cast hp
    have : (q : ℝ) < T := by exact_mod_cast hqT
    linarith
  have hαβ : α < β := by rw [hα, hβ]; linarith
  rcases le_total u v with huv | hvu
  · obtain ⟨u', v', hu', hu'v', hv', hwu', hwv', hstrip⟩ := exists_crossing huv
      (h.continuousOn_w.mono fun s hs => hlt s (hs.2.trans_lt hvT))
      (hu.le.trans (min_le_left _ _)) ((le_max_left _ _).trans hv.le)
    refine key u' v' (ht₁u.le.trans hu') hu'v' (hv'.trans_lt hvT) hstrip ?_
    rw [abs_of_nonneg (by linarith)]
    linarith
  · obtain ⟨v', u', hv', hv'u', hu', hwv', hwu', hstrip⟩ := exists_crossing (f := fun s => -w s)
      hvu ((h.continuousOn_w.mono fun s hs => hlt s (hs.2.trans_lt huT)).neg)
      (α := -β) (β := -α) (by linarith [le_max_left β M]) (by linarith [min_le_left α (-M)])
    refine key v' u' (ht₁v.le.trans hv') hv'u' (hu'.trans_lt huT) (fun s h1 h2 => by
      have := hstrip s h1 h2
      constructor <;> linarith [this.1, this.2]) ?_
    rw [abs_of_nonpos (by linarith)]
    linarith

end TwoSided

section OneSided

variable (h : IsForcePath xL xR ρL ρR w vL vR ζ)
include h

/-- The right-hand mirror of `vL_ge_of_le_w`: if the driver is bounded above by `m` before `ζ`,
every right force point is bounded above by `max (x^{j,R}, m + 1) + 2t`. -/
theorem vR_le_of_w_le {m : ℝ} (hm : ∀ s : ℝ≥0, (s : ℝ≥0∞) < ζ → w s ≤ m) (j : Fin nR)
    {t : ℝ≥0} (ht : (t : ℝ≥0∞) < ζ) : vR j t ≤ max (xR j) (m + 1) + 2 * (t : ℝ) := by
  have := h.reflect.vL_ge_of_le_w (m := -m) (fun s hs => by
    simp only [Pi.neg_apply]; linarith [hm s hs]) j ht
  simp only [Pi.neg_apply] at this
  rw [show -m - 1 = -(m + 1) by ring, min_neg_neg] at this
  linarith

/-- **(N4) and the noncritical one-sided case** (Specification pp. 26–27). Let `o` be the outermost
left index. If the outermost left force point is unbounded below before a finite lifetime `ζ = T`
(with `b` continuous on `[0, T]`), while all right force points stay bounded above, then the left
side total `s = ∑ ρ^{i,L}` is exactly `−2`. Proof: by (N1), `Q = W − V^out` equals
`G − (1 + s/2) V^out` with `G` bounded (the spreads `V^{i,L} − V^out` are bounded and the right
side is bounded); `s < −2` would force `Q < 0`, and `s > −2` makes `Q ≥ 1` once `V^out` is low
enough, so `V^out` moves at speed at most `2` there and stays bounded. -/
theorem sum_ρL_eq_neg_two_of_escape (hw : DriverEq a ρL ρR w vL vR b ζ) {T : ℝ≥0}
    (hζ : (T : ℝ≥0∞) = ζ) (hb : ContinuousOn b (Icc 0 T)) {o : Fin nL} (ho : ∀ i, i ≤ o)
    (hesc : ∀ m : ℝ, ∃ s : ℝ≥0, s < T ∧ vL o s < m)
    (hR : ∀ j, ∃ M : ℝ, ∀ s : ℝ≥0, s < T → vR j s ≤ M) :
    ∑ i, ρL i = -2 := by
  subst hζ
  have hlt : ∀ s : ℝ≥0, s < T → (s : ℝ≥0∞) < T := fun s hs => by exact_mod_cast hs
  set S := ∑ i, ρL i with hS
  obtain ⟨Mb, hMb⟩ := isCompact_Icc.exists_bound_of_continuousOn hb
  choose MR hMR using hR
  set K : ℝ := Real.sqrt a * Mb + (1 / 2) * ∑ i, |ρL i| * (xL i - xL o)
    + (1 / 2) * |∑ i, ρL i * xL i| + (1 / 2) * ∑ j, |ρR j| * (MR j - xR j) with hK
  -- `G = W + (s/2) V^out` is bounded by `K`
  have hG : ∀ t : ℝ≥0, t < T → |w t + (S / 2) * vL o t| ≤ K := by
    intro t ht
    have hN1 := h.w_eq_N1 hw (hlt t ht)
    have e : ∑ i, ρL i * (vL i t - xL i) =
        ∑ i, ρL i * (vL i t - vL o t) + S * vL o t - ∑ i, ρL i * xL i := by
      rw [hS, Finset.sum_mul, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl fun i _ => by ring
    have hGe : w t + (S / 2) * vL o t = Real.sqrt a * b t - (1 / 2) * ∑ i, ρL i * (vL i t - vL o t)
        + (1 / 2) * ∑ i, ρL i * xL i - (1 / 2) * ∑ j, ρR j * (vR j t - xR j) := by
      rw [hN1, e]; ring
    have hb' : |b t| ≤ Mb := by
      have := hMb t ⟨zero_le, ht.le⟩
      rwa [Real.norm_eq_abs] at this
    have h1 : |∑ i, ρL i * (vL i t - vL o t)| ≤ ∑ i, |ρL i| * (xL i - xL o) := by
      refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i _ => ?_)
      rw [abs_mul, abs_of_nonneg (sub_nonneg.2 (h.antitone_vL (hlt t ht) (ho i)))]
      exact mul_le_mul_of_nonneg_left (h.vL_sub_vL_le (hlt t ht) (ho i)) (abs_nonneg _)
    have h2 : |∑ j, ρR j * (vR j t - xR j)| ≤ ∑ j, |ρR j| * (MR j - xR j) := by
      refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun j _ => ?_)
      rw [abs_mul, abs_of_nonneg (sub_nonneg.2 (h.xR_le_vR (hlt t ht) j))]
      exact mul_le_mul_of_nonneg_left (by linarith [hMR j t ht]) (abs_nonneg _)
    have h3 : |Real.sqrt a * b t| ≤ Real.sqrt a * Mb := by
      rw [abs_mul, abs_of_nonneg (Real.sqrt_nonneg a)]
      exact mul_le_mul_of_nonneg_left hb' (Real.sqrt_nonneg a)
    rw [hGe, hK, abs_le]
    have e1 := abs_le.1 h3
    have e2 := abs_le.1 h1
    have e3 := abs_le.1 h2
    have e4 := neg_abs_le (∑ i, ρL i * xL i)
    have e5 := le_abs_self (∑ i, ρL i * xL i)
    constructor <;> linarith
  -- `Q = W − V^out ≥ 0`
  have hQ : ∀ t : ℝ≥0, t < T → vL o t ≤ w t := fun t ht => h.vL_le_w (hlt t ht) o
  rcases lt_trichotomy S (-2) with hS2 | hS2 | hS2
  · exfalso
    set c := -(1 + S / 2) with hc
    have hc0 : 0 < c := by rw [hc]; linarith
    obtain ⟨t, ht, hvt⟩ := hesc (-(K + 1) / c)
    have hmul : vL o t * c < -(K + 1) := (lt_div_iff₀ hc0).1 hvt
    have hce : vL o t * c = -vL o t - S / 2 * vL o t := by rw [hc]; ring
    have := (abs_le.1 (hG t ht)).2
    have := hQ t ht
    linarith
  · exact hS2
  · exfalso
    set c := 1 + S / 2 with hc
    have hc0 : 0 < c := by rw [hc]; linarith
    set m := -(K + 1) / c with hm
    have hgap : ∀ s : ℝ≥0, (s : ℝ≥0∞) < T → vL o s ≤ m → 1 ≤ w s - vL o s := by
      intro s hs hvs
      have hsT : s < T := by exact_mod_cast hs
      have hmul : vL o s * c ≤ -(K + 1) := (le_div_iff₀ hc0).1 hvs
      have hce : vL o s * c = vL o s + S / 2 * vL o s := by rw [hc]; ring
      have := (abs_le.1 (hG s hsT)).1
      linarith
    have hTpos : (0 : ℝ) ≤ T := NNReal.coe_nonneg T
    obtain ⟨t, ht, hvt⟩ := hesc (min (xL o) m - 2 * (T : ℝ))
    have := h.vL_ge_of_gap hgap (hlt t ht)
    have : (t : ℝ) ≤ T := by exact_mod_cast ht.le
    linarith

/-- The right-hand mirror of `sum_ρL_eq_neg_two_of_escape` (by reflection): if the outermost right
force point is unbounded above before a finite lifetime while all left force points stay bounded
below, then the right side total is exactly `−2`. -/
theorem sum_ρR_eq_neg_two_of_escape (hw : DriverEq a ρL ρR w vL vR b ζ) {T : ℝ≥0}
    (hζ : (T : ℝ≥0∞) = ζ) (hb : ContinuousOn b (Icc 0 T)) {o : Fin nR} (ho : ∀ j, j ≤ o)
    (hesc : ∀ m : ℝ, ∃ s : ℝ≥0, s < T ∧ m < vR o s)
    (hL : ∀ i, ∃ M : ℝ, ∀ s : ℝ≥0, s < T → M ≤ vL i s) :
    ∑ j, ρR j = -2 :=
  h.reflect.sum_ρL_eq_neg_two_of_escape hw.reflect hζ hb.neg ho
    (fun m => by
      obtain ⟨s, hs, hv⟩ := hesc (-m)
      exact ⟨s, hs, by simp only [Pi.neg_apply]; linarith⟩)
    (fun i => by
      obtain ⟨M, hM⟩ := hL i
      exact ⟨-M, fun s hs => by simp only [Pi.neg_apply]; linarith [hM s hs]⟩)

end OneSided

section Assembly

variable (h : IsForcePath xL xR ρL ρR w vL vR ζ)
include h

/-- **Finite terminal limits** (Specification p. 28, "monotonicity gives finite force-coordinate
limits, and (N1) gives a finite driver limit"): if at a finite positive lifetime `ζ = T` all left
force points stay bounded below and all right ones bounded above, then the state converges as
`t ↑ T`, and by maximality the limiting state satisfies the threshold condition. -/
theorem exists_tendsto_of_bdd (hw : DriverEq a ρL ρR w vL vR b ζ) {T : ℝ≥0} (hT : 0 < T)
    (hζ : (T : ℝ≥0∞) = ζ) (hb : ContinuousOn b (Icc 0 T))
    (hLb : ∀ i, ∃ M : ℝ, ∀ s : ℝ≥0, s < T → M ≤ vL i s)
    (hRb : ∀ j, ∃ M : ℝ, ∀ s : ℝ≥0, s < T → vR j s ≤ M) :
    ∃ (w₀ : ℝ) (vL₀ : Fin nL → ℝ) (vR₀ : Fin nR → ℝ),
      Tendsto (fun t => (w t, fun i => vL i t, fun i => vR i t)) (𝓝[<] T) (𝓝 (w₀, vL₀, vR₀)) ∧
      ForceWord.ThresholdCondition ρL ρR w₀ vL₀ vR₀ := by
  have hlt : ∀ s : ℝ≥0, s < T → (s : ℝ≥0∞) < ζ := fun s hs => hζ ▸ (by exact_mod_cast hs)
  have hset : {t : ℝ≥0 | (t : ℝ≥0∞) < ζ} = Iio T := by rw [← hζ]; exact setOf_lt_coe_eq_Iio T
  have hL : ∀ i, Tendsto (vL i) (𝓝[<] T) (𝓝 (sInf (vL i '' Iio T))) := fun i => by
    refine AntitoneOn.tendsto_nhdsLT ?_ ?_
    · have := h.antitoneOn_vL i
      rwa [hset] at this
    · obtain ⟨M, hM⟩ := hLb i
      exact ⟨M, by rintro _ ⟨s, hs, rfl⟩; exact hM s hs⟩
  have hR : ∀ j, Tendsto (vR j) (𝓝[<] T) (𝓝 (sSup (vR j '' Iio T))) := fun j => by
    refine MonotoneOn.tendsto_nhdsLT ?_ ?_
    · have := h.monotoneOn_vR j
      rwa [hset] at this
    · obtain ⟨M, hM⟩ := hRb j
      exact ⟨M, by rintro _ ⟨s, hs, rfl⟩; exact hM s hs⟩
  set vL₀ : Fin nL → ℝ := fun i => sInf (vL i '' Iio T)
  set vR₀ : Fin nR → ℝ := fun j => sSup (vR j '' Iio T)
  have hbT : Tendsto b (𝓝[<] T) (𝓝 (b T)) :=
    (hb T ⟨zero_le, le_rfl⟩).tendsto.mono_left
      (nhdsWithin_mono _ fun s hs => ⟨zero_le, le_of_lt hs⟩)
  set w₀ : ℝ := Real.sqrt a * b T - (1 / 2) * (∑ i, ρL i * (vL₀ i - xL i))
    - (1 / 2) * (∑ j, ρR j * (vR₀ j - xR j))
  have hW : Tendsto w (𝓝[<] T) (𝓝 w₀) := by
    have hF : Tendsto (fun t => Real.sqrt a * b t - (1 / 2) * (∑ i, ρL i * (vL i t - xL i))
        - (1 / 2) * (∑ j, ρR j * (vR j t - xR j))) (𝓝[<] T) (𝓝 w₀) :=
      ((hbT.const_mul _).sub ((tendsto_finsetSum _ fun i _ =>
        ((hL i).sub_const _).const_mul _).const_mul _)).sub
        ((tendsto_finsetSum _ fun j _ => ((hR j).sub_const _).const_mul _).const_mul _)
    refine hF.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with t ht
    exact (h.w_eq_N1 hw (hlt t ht)).symm
  have hlim : Tendsto (fun t => (w t, fun i => vL i t, fun i => vR i t)) (𝓝[<] T)
      (𝓝 (w₀, vL₀, vR₀)) :=
    hW.prodMk_nhds ((tendsto_pi_nhds.2 fun i => hL i).prodMk_nhds (tendsto_pi_nhds.2 fun j => hR j))
  exact ⟨w₀, vL₀, vR₀, hlim, h.threshold_of_tendsto hT hζ hlim⟩

/-- **Aux. lemma 3, pathwise part** (Specification pp. 24–28). At a finite positive lifetime
`ζ = T`, with the driving path `b` continuous on `[0, T]`, exactly one of the following holds:

1. the state `(W, V^L, V^R)` has a finite limit as `t ↑ T`, and the limiting state satisfies the
   continuation-threshold condition (so the lifetime is the continuation threshold);
2. the left side escapes to `−∞` (some left force point is unbounded below), the right side stays
   bounded, and the left side total is exactly `−2`;
3. the mirror image of 2 on the right.

Two-sided escape is impossible (`not_unbounded_both`), and one-sided escape with side total
`≠ −2` is impossible (`sum_ρL_eq_neg_two_of_escape`). The critical cases 2–3 are excluded almost
surely by the probabilistic `x log x` argument (N5)–(N8), which a deterministic path cannot
replace. -/
theorem tendsto_or_criticalEscape (hw : DriverEq a ρL ρR w vL vR b ζ) {T : ℝ≥0} (hT : 0 < T)
    (hζ : (T : ℝ≥0∞) = ζ) (hb : ContinuousOn b (Icc 0 T)) :
    (∃ (w₀ : ℝ) (vL₀ : Fin nL → ℝ) (vR₀ : Fin nR → ℝ),
      Tendsto (fun t => (w t, fun i => vL i t, fun i => vR i t)) (𝓝[<] T) (𝓝 (w₀, vL₀, vR₀)) ∧
      ForceWord.ThresholdCondition ρL ρR w₀ vL₀ vR₀) ∨
    ((∑ i, ρL i = -2) ∧ (∃ i, ∀ m : ℝ, ∃ s : ℝ≥0, s < T ∧ vL i s < m) ∧
      ∀ j, ∃ M : ℝ, ∀ s : ℝ≥0, s < T → vR j s ≤ M) ∨
    ((∑ j, ρR j = -2) ∧ (∃ j, ∀ m : ℝ, ∃ s : ℝ≥0, s < T ∧ m < vR j s) ∧
      ∀ i, ∃ M : ℝ, ∀ s : ℝ≥0, s < T → M ≤ vL i s) := by
  have hlt : ∀ s : ℝ≥0, s < T → (s : ℝ≥0∞) < ζ := fun s hs => hζ ▸ (by exact_mod_cast hs)
  have hlt' : ∀ s : ℝ≥0, (s : ℝ≥0∞) < ζ → s < T := fun s hs => by
    rw [← hζ] at hs; exact_mod_cast hs
  by_cases hLb : ∀ i, ∃ M : ℝ, ∀ s : ℝ≥0, s < T → M ≤ vL i s
  · by_cases hRb : ∀ j, ∃ M : ℝ, ∀ s : ℝ≥0, s < T → vR j s ≤ M
    · exact Or.inl (h.exists_tendsto_of_bdd hw hT hζ hb hLb hRb)
    · push Not at hRb
      obtain ⟨j, hj⟩ := hRb
      obtain ⟨o, ho⟩ := exists_forall_le_fin j
      have hesc : ∀ m : ℝ, ∃ s : ℝ≥0, s < T ∧ m < vR o s := fun m => by
        obtain ⟨s, hs, hms⟩ := hj m
        exact ⟨s, hs, hms.trans_le (h.monotone_vR (hlt s hs) (ho j))⟩
      exact Or.inr (Or.inr ⟨h.sum_ρR_eq_neg_two_of_escape hw hζ hb ho hesc hLb, ⟨o, hesc⟩, hLb⟩)
  · push Not at hLb
    obtain ⟨i, hi⟩ := hLb
    obtain ⟨o, ho⟩ := exists_forall_le_fin i
    have hesc : ∀ m : ℝ, ∃ s : ℝ≥0, s < T ∧ vL o s < m := fun m => by
      obtain ⟨s, hs, hms⟩ := hi m
      exact ⟨s, hs, (h.antitone_vL (hlt s hs) (ho i)).trans_lt hms⟩
    by_cases hRb : ∀ j, ∃ M : ℝ, ∀ s : ℝ≥0, s < T → vR j s ≤ M
    · exact Or.inr (Or.inl ⟨h.sum_ρL_eq_neg_two_of_escape hw hζ hb ho hesc hRb, ⟨o, hesc⟩, hRb⟩)
    · exfalso
      push Not at hRb
      obtain ⟨j, hj⟩ := hRb
      refine h.not_unbounded_both hw hζ hb (fun m => ?_) (fun m => ?_)
      · by_contra hcon
        push Not at hcon
        obtain ⟨s, hs, hvs⟩ := hi (min (xL i) (m - 1) - 2 * (T : ℝ))
        have := h.vL_ge_of_le_w (m := m) (fun s' hs' => hcon s' (hlt' s' hs')) i (hlt s hs)
        have : (s : ℝ) ≤ T := by exact_mod_cast hs.le
        linarith
      · by_contra hcon
        push Not at hcon
        obtain ⟨s, hs, hvs⟩ := hj (max (xR j) (m + 1) + 2 * (T : ℝ))
        have := h.vR_le_of_w_le (m := m) (fun s' hs' => hcon s' (hlt' s' hs')) j (hlt s hs)
        have : (s : ℝ) ≤ T := by exact_mod_cast hs.le
        linarith

end Assembly

section Critical

variable (h : IsForcePath xL xR ρL ρR w vL vR ζ)
include h

/-- **(N4) in the critical case** (Specification p. 27, "(N4) makes `Q` bounded"): if the left side
total is `−2` and the right side stays bounded above before a finite lifetime `ζ = T` (with `b`
continuous on `[0, T]`), then `Q = W − V^out` is bounded on `[0, T)`. -/
theorem exists_bound_gap_out (hw : DriverEq a ρL ρR w vL vR b ζ) {T : ℝ≥0}
    (hζ : (T : ℝ≥0∞) = ζ) (hb : ContinuousOn b (Icc 0 T)) {o : Fin nL} (ho : ∀ i, i ≤ o)
    (hS : ∑ i, ρL i = -2) (hR : ∀ j, ∃ M : ℝ, ∀ s : ℝ≥0, s < T → vR j s ≤ M) :
    ∃ K : ℝ, ∀ t : ℝ≥0, t < T → w t - vL o t ≤ K := by
  subst hζ
  have hlt : ∀ s : ℝ≥0, s < T → (s : ℝ≥0∞) < T := fun s hs => by exact_mod_cast hs
  obtain ⟨Mb, hMb⟩ := isCompact_Icc.exists_bound_of_continuousOn hb
  choose MR hMR using hR
  refine ⟨Real.sqrt a * Mb + (1 / 2) * ∑ i, |ρL i| * (xL i - xL o)
    + (1 / 2) * |∑ i, ρL i * xL i| + (1 / 2) * ∑ j, |ρR j| * (MR j - xR j), fun t ht => ?_⟩
  have hN1 := h.w_eq_N1 hw (hlt t ht)
  have e : ∑ i, ρL i * (vL i t - xL i) =
      ∑ i, ρL i * (vL i t - vL o t) + (∑ i, ρL i) * vL o t - ∑ i, ρL i * xL i := by
    rw [Finset.sum_mul, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun i _ => by ring
  have hQe : w t - vL o t = Real.sqrt a * b t - (1 / 2) * ∑ i, ρL i * (vL i t - vL o t)
      + (1 / 2) * ∑ i, ρL i * xL i - (1 / 2) * ∑ j, ρR j * (vR j t - xR j) := by
    rw [hN1, e, hS]; ring
  have hb' : |b t| ≤ Mb := by
    have := hMb t ⟨zero_le, ht.le⟩
    rwa [Real.norm_eq_abs] at this
  have h1 : |∑ i, ρL i * (vL i t - vL o t)| ≤ ∑ i, |ρL i| * (xL i - xL o) := by
    refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i _ => ?_)
    rw [abs_mul, abs_of_nonneg (sub_nonneg.2 (h.antitone_vL (hlt t ht) (ho i)))]
    exact mul_le_mul_of_nonneg_left (h.vL_sub_vL_le (hlt t ht) (ho i)) (abs_nonneg _)
  have h2 : |∑ j, ρR j * (vR j t - xR j)| ≤ ∑ j, |ρR j| * (MR j - xR j) := by
    refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun j _ => ?_)
    rw [abs_mul, abs_of_nonneg (sub_nonneg.2 (h.xR_le_vR (hlt t ht) j))]
    exact mul_le_mul_of_nonneg_left (by linarith [hMR j t ht]) (abs_nonneg _)
  have h3 : |Real.sqrt a * b t| ≤ Real.sqrt a * Mb := by
    rw [abs_mul, abs_of_nonneg (Real.sqrt_nonneg a)]
    exact mul_le_mul_of_nonneg_left hb' (Real.sqrt_nonneg a)
  rw [hQe]
  have e1 := abs_le.1 h3
  have e2 := abs_le.1 h1
  have e3 := abs_le.1 h2
  have e5 := le_abs_self (∑ i, ρL i * xL i)
  linarith

/-- **The critical escape forces `∫ dt/Q = ∞`** (Specification p. 27, "this contradicts
`V^out_t = V^out_q − ∫_q^t 2/Q_u du`"): if the outermost left force point is unbounded below before
`ζ = T`, then `∫₀ᵗ (W − V^out)⁻¹` is unbounded for `t < T`. -/
theorem integral_inv_gap_out_unbounded {T : ℝ≥0} (hζ : (T : ℝ≥0∞) = ζ) {o : Fin nL}
    (hesc : ∀ m : ℝ, ∃ s : ℝ≥0, s < T ∧ vL o s < m) (K : ℝ) :
    ∃ t : ℝ≥0, t < T ∧ K < ∫ s in (0 : ℝ)..t, (w s.toNNReal - vL o s.toNNReal)⁻¹ := by
  obtain ⟨t, ht, hvt⟩ := hesc (xL o - 2 * K)
  refine ⟨t, ht, ?_⟩
  have htζ : (t : ℝ≥0∞) < ζ := hζ ▸ (by exact_mod_cast ht)
  have e := h.vL_eq htζ o
  have hfun : (fun s : ℝ => 2 / (vL o s.toNNReal - w s.toNNReal)) =
      fun s => -2 * (w s.toNNReal - vL o s.toNNReal)⁻¹ := funext fun s => two_div_sub_eq _ _
  rw [hfun, intervalIntegral.integral_const_mul] at e
  linarith

end Critical

end IsForcePath

end Sec2

namespace IsIntegratedSLEPath

variable {a : ℝ} {nL nR : ℕ} {xL : Fin nL → ℝ} {xR : Fin nR → ℝ} {ρL : Fin nL → ℝ}
  {ρR : Fin nR → ℝ} {w : ℝ≥0 → ℝ} {vL : Fin nL → ℝ≥0 → ℝ} {vR : Fin nR → ℝ≥0 → ℝ}
  {b : ℝ≥0 → ℝ} {ζ : ℝ≥0∞}

/-- **Aux. lemma 3, pathwise part, for Definition 2.1** (see
`Sec2.IsForcePath.tendsto_or_criticalEscape`): at a finite positive lifetime `ζ = T`, with `b`
continuous on `[0, T]`, either the state converges and its limit satisfies the threshold condition,
or one side escapes with side total exactly `−2` while the other side stays bounded. -/
theorem tendsto_or_criticalEscape (h : IsIntegratedSLEPath a xL xR ρL ρR w vL vR b ζ)
    {T : ℝ≥0} (hT : 0 < T) (hζ : (T : ℝ≥0∞) = ζ) (hb : ContinuousOn b (Icc 0 T)) :
    (∃ (w₀ : ℝ) (vL₀ : Fin nL → ℝ) (vR₀ : Fin nR → ℝ),
      Tendsto (fun t => (w t, fun i => vL i t, fun i => vR i t)) (𝓝[<] T) (𝓝 (w₀, vL₀, vR₀)) ∧
      ForceWord.ThresholdCondition ρL ρR w₀ vL₀ vR₀) ∨
    ((∑ i, ρL i = -2) ∧ (∃ i, ∀ m : ℝ, ∃ s : ℝ≥0, s < T ∧ vL i s < m) ∧
      ∀ j, ∃ M : ℝ, ∀ s : ℝ≥0, s < T → vR j s ≤ M) ∨
    ((∑ j, ρR j = -2) ∧ (∃ j, ∀ m : ℝ, ∃ s : ℝ≥0, s < T ∧ m < vR j s) ∧
      ∀ i, ∃ M : ℝ, ∀ s : ℝ≥0, s < T → M ≤ vL i s) :=
  h.isForcePath.tendsto_or_criticalEscape h.driverEq hT hζ hb

end IsIntegratedSLEPath

end InteractingSLE
