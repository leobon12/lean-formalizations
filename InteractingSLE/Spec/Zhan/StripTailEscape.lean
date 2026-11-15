/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Zhan.StripTailDrift
import InteractingSLE.Spec.Zhan.StripEndpointEscape

/-!
# Linear escape of the lower strip gaps along a strip path

Packet PROVE-ZHAN-A4. Astra, *Formalization proofs* L1521–L1556 ("Linear escape of lower strip gaps", (3.24)–(3.25),
and "Under (3.3), both escape slopes are positive"). For a strip path with lower marks the nearest gap `X` of one side
solves

  `X_t − X_s = −(N_t − N_s) + ∫ₛᵗ gapDrift sₒ sₚ τd (X, Y) − (E_t − E_s)`

with `Y` the nearest gap of the other side, `N` sublinear and `E` of bounded variation (same-side spreads,
`0 ≤ ∫ₛᵗ (C(X) − C(Xᵢ)) ≤ (Xᵢ − X)(0)`); the landed pathwise barrier lemma `eventually_mul_le_of_gap_eq` then gives
`X_t ≥ α t` eventually. The slope condition is `1 + c > 0`, i.e. `|σ| < 1`.

## Main results

* `Sec4.cothHalf_le_cothHalf`: `C` is antitone on `(0, ∞)`;
* `eventually_mul_le_of_side`: the one-sided escape from the gap equations of all gaps (generic);
* `StripGood.exists_linear_escape`: every lower gap of a strip path grows at least linearly, if the strip driver is
  `N + σ t + ∫ e` with `N` sublinear, `|σ| < 1` and side sums `> −2`;
* `StripGood.eventually_abs_stripErr_le`, `StripGood.exists_energy_le`: the error is eventually small and has finite
  energy on the tail.
-/

set_option autoImplicit false

noncomputable section

open Set Filter Topology MeasureTheory
open scoped NNReal ENNReal

namespace InteractingSLE

namespace Sec4

theorem cothHalf_le_cothHalf {x y : ℝ} (hx : 0 < x) (hxy : x ≤ y) : cothHalf y ≤ cothHalf x := by
  have hy : 0 < y := hx.trans_le hxy
  rw [← sub_le_sub_iff_right 1, cothHalf_sub_one_eq hy.ne', cothHalf_sub_one_eq hx.ne']
  have h1 : 0 < Real.exp x - 1 := by linarith [Real.add_one_lt_exp hx.ne']
  exact div_le_div_of_nonneg_left (by norm_num) h1 (by linarith [Real.exp_le_exp.2 hxy])

end Sec4

namespace Zhan

open Sec4 (cothHalf)

/-- Continuity on `[0, ∞)` from continuity on every `[0, T]`. -/
theorem continuousOn_Ici_of_Icc {f : ℝ → ℝ} (h : ∀ T, 0 ≤ T → ContinuousOn f (Icc 0 T)) :
    ContinuousOn f (Ici 0) := by
  intro t ht
  have ht0 : 0 ≤ t := ht
  have h1 := h (t + 1) (by linarith)
  have hmem : Icc 0 (t + 1) ∈ 𝓝[Ici 0] t := by
    rw [← Ici_inter_Iic]
    exact inter_mem_nhdsWithin _ (Iic_mem_nhds (by linarith))
  exact (h1 t ⟨ht0, by linarith⟩).mono_of_mem_nhdsWithin hmem

theorem continuousOn_cothHalf_comp {X : ℝ → ℝ} (hXc : ContinuousOn X (Ici 0))
    (hX0 : ∀ u, 0 ≤ u → 0 < X u) : ContinuousOn (fun u => cothHalf (X u)) (Ici 0) :=
  Sec4.continuousOn_cothHalf.comp hXc fun u hu => (hX0 u hu).ne'

/-- **One-sided linear escape from the gap equations** (Astra (3.24)–(3.25)). `X` is the nearest gap of its side
(`X ≤ Xo i`), `Y` a positive comparison gap of the other side (`Y ≤ Yp j`); all differences of same-side gaps solve
`d(Xo i − X) = (C(Xo i) − C(X)) dt`, and `X` solves the gap equation with drift
`C(X) + c + Σ (ρo/2)(C(Xo) − 1) − Σ (ρp/2)(C(Yp) − 1)` and martingale part `−N`. If `N` is sublinear,
`1 + sₒ/2 ≥ 0` and `1 + c > 0`, then `X` grows at least linearly. -/
theorem eventually_mul_le_of_side {m k : ℕ} {Xo : Fin m → ℝ → ℝ} {Yp : Fin k → ℝ → ℝ} {X Y N : ℝ → ℝ}
    {ρo : Fin m → ℝ} {ρp : Fin k → ℝ} {c K : ℝ}
    (hXc : ContinuousOn X (Ici 0)) (hYc : ContinuousOn Y (Ici 0))
    (hXoc : ∀ i, ContinuousOn (Xo i) (Ici 0)) (hYpc : ∀ j, ContinuousOn (Yp j) (Ici 0))
    (hX0 : ∀ u, 0 ≤ u → 0 < X u) (hY0 : ∀ u, 0 ≤ u → 0 < Y u)
    (hXo : ∀ i u, 0 ≤ u → X u ≤ Xo i u) (hYp : ∀ j u, 0 ≤ u → Y u ≤ Yp j u)
    (hXod : ∀ i s t, 0 ≤ s → s ≤ t →
      (Xo i t - X t) - (Xo i s - X s) = ∫ r in s..t, (cothHalf (Xo i r) - cothHalf (X r)))
    (hYpd : ∀ j s t, 0 ≤ s → s ≤ t →
      (Yp j t - Y t) - (Yp j s - Y s) = ∫ r in s..t, (cothHalf (Yp j r) - cothHalf (Y r)))
    (hXY : ∀ u, 0 ≤ u → 2 * u - K ≤ X u + Y u)
    (heq : ∀ s t, 0 ≤ s → s ≤ t → X t - X s = -(N t - N s) +
      ∫ r in s..t, (cothHalf (X r) + c + (∑ i, ρo i / 2 * (cothHalf (Xo i r) - 1)) -
        ∑ j, ρp j / 2 * (cothHalf (Yp j r) - 1)))
    (hN : ∀ ε > 0, ∃ C, ∀ u, 0 ≤ u → |N u| ≤ C + ε * u)
    (hso : 0 ≤ 1 + (∑ i, ρo i) / 2) (hc : 0 < 1 + c) :
    ∃ α > 0, ∃ T, ∀ t, T ≤ t → α * t ≤ X t := by
  set so := ∑ i, ρo i with hso_def
  set sp := ∑ j, ρp j with hsp_def
  set τd := c - so / 2 + sp / 2 with hτd
  set spr : ℝ → ℝ := fun r => (∑ i, ρo i / 2 * (cothHalf (Xo i r) - cothHalf (X r))) -
    ∑ j, ρp j / 2 * (cothHalf (Yp j r) - cothHalf (Y r)) with hspr
  have key : ∀ r, cothHalf (X r) + c + (∑ i, ρo i / 2 * (cothHalf (Xo i r) - 1)) -
      ∑ j, ρp j / 2 * (cothHalf (Yp j r) - 1) = gapDrift so sp τd (X r) (Y r) + spr r := fun r => by
    simp only [gapDrift, hspr, hτd, hso_def, hsp_def, mul_sub, mul_one, Finset.sum_sub_distrib,
      ← Finset.sum_mul, Finset.sum_div]
    ring
  have hCX := continuousOn_cothHalf_comp hXc hX0
  have hCY := continuousOn_cothHalf_comp hYc hY0
  have hCXo : ∀ i, ContinuousOn (fun u => cothHalf (Xo i u)) (Ici 0) := fun i =>
    continuousOn_cothHalf_comp (hXoc i) fun u hu => (hX0 u hu).trans_le (hXo i u hu)
  have hCYp : ∀ j, ContinuousOn (fun u => cothHalf (Yp j u)) (Ici 0) := fun j =>
    continuousOn_cothHalf_comp (hYpc j) fun u hu => (hY0 u hu).trans_le (hYp j u hu)
  have hgc : ContinuousOn (fun r => gapDrift so sp τd (X r) (Y r)) (Ici 0) := by
    unfold gapDrift
    exact ((continuousOn_const.mul hCX).sub (continuousOn_const.mul hCY)).add continuousOn_const
  have hsc : ContinuousOn spr (Ici 0) := by
    simp only [hspr]
    exact (continuousOn_finsetSum _ fun i _ => continuousOn_const.mul ((hCXo i).sub hCX)).sub
      (continuousOn_finsetSum _ fun j _ => continuousOn_const.mul ((hCYp j).sub hCY))
  have hsubI : ∀ s t : ℝ, 0 ≤ s → s ≤ t → uIcc s t ⊆ Ici 0 := fun s t hs hst u hu => by
    rw [uIcc_of_le hst] at hu; exact hs.trans hu.1
  have hgi : ∀ s t, 0 ≤ s → s ≤ t →
      IntervalIntegrable (fun r => gapDrift so sp τd (X r) (Y r)) volume s t :=
    fun s t hs hst => (hgc.mono (hsubI s t hs hst)).intervalIntegrable
  have hsi : ∀ s t, 0 ≤ s → s ≤ t → IntervalIntegrable spr volume s t :=
    fun s t hs hst => (hsc.mono (hsubI s t hs hst)).intervalIntegrable
  set E : ℝ → ℝ := fun t => -∫ r in (0 : ℝ)..t, spr r with hE
  have hEst : ∀ s t, 0 ≤ s → s ≤ t → E t - E s = -∫ r in s..t, spr r := fun s t hs hst => by
    have := intervalIntegral.integral_interval_sub_left (μ := volume) (hsi 0 t le_rfl (hs.trans hst))
      (hsi 0 s le_rfl hs)
    simp only [hE]
    linarith
  have heq' : ∀ s t, 0 ≤ s → s ≤ t →
      X t - X s = -(N t - N s) + (∫ r in s..t, gapDrift so sp τd (X r) (Y r)) - (E t - E s) := by
    intro s t hs hst
    rw [heq s t hs hst, intervalIntegral.integral_congr (g := fun r => gapDrift so sp τd (X r) (Y r) + spr r)
      (fun r _ => key r), intervalIntegral.integral_add (hgi s t hs hst) (hsi s t hs hst), hEst s t hs hst]
    ring
  -- the same-side spreads
  have hDo : ∀ i s t, 0 ≤ s → s ≤ t → (Xo i t - X t) - (Xo i s - X s) ≤ 0 := fun i s t hs hst => by
    rw [hXod i s t hs hst]
    have h1 := intervalIntegral.integral_mono_on (μ := volume) hst
      ((((hCXo i).sub hCX).mono (hsubI s t hs hst)).intervalIntegrable) (intervalIntegrable_const (c := (0 : ℝ)))
      fun r hr => sub_nonpos.2 (Sec4.cothHalf_le_cothHalf (hX0 r (hs.trans hr.1)) (hXo i r (hs.trans hr.1)))
    simpa using h1
  have hDp : ∀ j s t, 0 ≤ s → s ≤ t → (Yp j t - Y t) - (Yp j s - Y s) ≤ 0 := fun j s t hs hst => by
    rw [hYpd j s t hs hst]
    have h1 := intervalIntegral.integral_mono_on (μ := volume) hst
      ((((hCYp j).sub hCY).mono (hsubI s t hs hst)).intervalIntegrable) (intervalIntegrable_const (c := (0 : ℝ)))
      fun r hr => sub_nonpos.2 (Sec4.cothHalf_le_cothHalf (hY0 r (hs.trans hr.1)) (hYp j r (hs.trans hr.1)))
    simpa using h1
  have hBo : ∀ i s t, 0 ≤ s → s ≤ t → |(Xo i t - X t) - (Xo i s - X s)| ≤ Xo i 0 - X 0 :=
    fun i s t hs hst => by
      have h1 := hDo i s t hs hst
      have h2 := hDo i 0 s le_rfl hs
      have h3 := hXo i t (hs.trans hst)
      rw [abs_of_nonpos h1]
      linarith
  have hBp : ∀ j s t, 0 ≤ s → s ≤ t → |(Yp j t - Y t) - (Yp j s - Y s)| ≤ Yp j 0 - Y 0 :=
    fun j s t hs hst => by
      have h1 := hDp j s t hs hst
      have h2 := hDp j 0 s le_rfl hs
      have h3 := hYp j t (hs.trans hst)
      rw [abs_of_nonpos h1]
      linarith
  have hint_spr : ∀ s t, 0 ≤ s → s ≤ t → ∫ r in s..t, spr r =
      (∑ i, ρo i / 2 * ((Xo i t - X t) - (Xo i s - X s))) -
        ∑ j, ρp j / 2 * ((Yp j t - Y t) - (Yp j s - Y s)) := by
    intro s t hs hst
    have hio : ∀ i, IntervalIntegrable (fun r => cothHalf (Xo i r) - cothHalf (X r)) volume s t := fun i =>
      (((hCXo i).sub hCX).mono (hsubI s t hs hst)).intervalIntegrable
    have hip : ∀ j, IntervalIntegrable (fun r => cothHalf (Yp j r) - cothHalf (Y r)) volume s t := fun j =>
      (((hCYp j).sub hCY).mono (hsubI s t hs hst)).intervalIntegrable
    have hA : IntervalIntegrable (fun r => ∑ i, ρo i / 2 * (cothHalf (Xo i r) - cothHalf (X r))) volume s t :=
      ((continuousOn_finsetSum _ fun i _ => continuousOn_const.mul ((hCXo i).sub hCX)).mono
        (hsubI s t hs hst)).intervalIntegrable
    have hB : IntervalIntegrable (fun r => ∑ j, ρp j / 2 * (cothHalf (Yp j r) - cothHalf (Y r))) volume s t :=
      ((continuousOn_finsetSum _ fun j _ => continuousOn_const.mul ((hCYp j).sub hCY)).mono
        (hsubI s t hs hst)).intervalIntegrable
    simp only [hspr]
    rw [intervalIntegral.integral_sub hA hB, intervalIntegral.integral_finsetSum fun i _ => (hio i).const_mul _,
      intervalIntegral.integral_finsetSum fun j _ => (hip j).const_mul _]
    simp only [intervalIntegral.integral_const_mul, hXod _ s t hs hst, hYpd _ s t hs hst]
  set V := (∑ i, |ρo i| / 2 * (Xo i 0 - X 0)) + ∑ j, |ρp j| / 2 * (Yp j 0 - Y 0) with hV
  have hEb : ∀ s t, 0 ≤ s → s ≤ t → |E t - E s| ≤ V := by
    intro s t hs hst
    rw [hEst s t hs hst, abs_neg, hint_spr s t hs hst]
    refine (abs_sub _ _).trans (add_le_add ?_ ?_)
    · refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i _ => ?_)
      rw [abs_mul, abs_div, abs_two]
      exact mul_le_mul_of_nonneg_left (hBo i s t hs hst) (by positivity)
    · refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun j _ => ?_)
      rw [abs_mul, abs_div, abs_two]
      exact mul_le_mul_of_nonneg_left (hBp j s t hs hst) (by positivity)
  exact eventually_mul_le_of_gap_eq (T₀ := 0) hXc hX0 hXY hgi heq' hN hEb hso
    (by rw [hτd]; linarith)

/-! ### The strip gaps of a strip path -/

open Strip

namespace StripGood

variable {nL nR : ℕ} {a : ℝ} {pL : Fin nL → ℝ} {xR : Fin nR → ℝ} {ρL : Fin (nL + 1) → ℝ}
  {ρR : Fin nR → ℝ} {w : ℝ≥0 → ℝ} {vL : Fin (nL + 1) → ℝ≥0 → ℝ} {vR : Fin nR → ℝ≥0 → ℝ} {b : ℝ≥0 → ℝ}
  {ζ : ℝ≥0∞}

theorem continuousOn_gapL_Ici (h : StripGood a pL xR ρL ρR w vL vR b ζ) (i : Fin nL) :
    ContinuousOn (gapL w vL i) (Ici 0) :=
  continuousOn_Ici_of_Icc fun T _ => by
    obtain ⟨S, hS, hTS⟩ := h.exists_life T
    exact (h.continuousOn_gapL i hS).mono (Icc_subset_Icc le_rfl hTS)

theorem continuousOn_gapR_Ici (h : StripGood a pL xR ρL ρR w vL vR b ζ) (j : Fin nR) :
    ContinuousOn (gapR w vL vR j) (Ici 0) :=
  continuousOn_Ici_of_Icc fun T _ => by
    obtain ⟨S, hS, hTS⟩ := h.exists_life T
    exact (h.continuousOn_gapR j hS).mono (Icc_subset_Icc le_rfl hTS)

theorem continuousOn_stripDriver_Ici (h : StripGood a pL xR ρL ρR w vL vR b ζ) :
    ContinuousOn (stripDriver (extPath w) (extPath (vL (Fin.last nL)))) (Ici 0) :=
  continuousOn_Ici_of_Icc fun T _ => by
    obtain ⟨S, hS, hTS⟩ := h.exists_life T
    exact (h.continuousOn_stripDriver' hS).mono (Icc_subset_Icc le_rfl hTS)

theorem continuousOn_stripErr_Ici (h : StripGood a pL xR ρL ρR w vL vR b ζ) (ρl : Fin nL → ℝ)
    (ρr : Fin nR → ℝ) : ContinuousOn (stripErr ρl ρr w vL vR) (Ici 0) := by
  unfold stripErr
  exact (continuousOn_finsetSum _ fun i _ => continuousOn_const.mul ((continuousOn_cothHalf_comp
    (h.continuousOn_gapL_Ici i) fun u hu => h.gapL_pos i hu).sub continuousOn_const)).sub
    (continuousOn_finsetSum _ fun j _ => continuousOn_const.mul ((continuousOn_cothHalf_comp
    (h.continuousOn_gapR_Ici j) fun u hu => h.gapR_pos j hu).sub continuousOn_const))

/-- The order of the lower right gaps. -/
theorem gapR_le_gapR (h : StripGood a pL xR ρL ρR w vL vR b ζ) {j₀ j : Fin nR} (hj : j₀ ≤ j) {u : ℝ}
    (hu : 0 ≤ u) : gapR w vL vR j₀ u ≤ gapR w vL vR j u := by
  obtain ⟨S, hS, huS⟩ := h.exists_life u
  have hs := (h.isSepMark hS).chordalTime_mem ⟨hu, huS⟩
  have hl := life_toNNReal hS hs
  have h1 := hl.2 _ le_rfl
  have h2 := (h.noncoll _ hl).2 j₀
  have h3 := h.path.isForcePath.monotone_vR hl.1 hj
  simp only [gapR, stripPoint, extPath]
  rw [abs_of_pos (by linarith), abs_of_pos (by linarith)]
  have := Real.log_le_log (by linarith) (sub_le_sub_right h3 (vL (Fin.last nL) _))
  linarith

/-- The order of the lower left gaps. -/
theorem gapL_le_gapL (h : StripGood a pL xR ρL ρR w vL vR b ζ) {i₀ i : Fin nL} (hi : i₀ ≤ i) {u : ℝ}
    (hu : 0 ≤ u) : gapL w vL i₀ u ≤ gapL w vL i u := by
  obtain ⟨S, hS, huS⟩ := h.exists_life u
  have hs := (h.isSepMark hS).chordalTime_mem ⟨hu, huS⟩
  have hl := life_toNNReal hS hs
  have h1 := vL_last_lt_vL_castSucc h.path hl i
  have h3 := h.path.isForcePath.antitone_vL hl.1 (Fin.castSucc_le_castSucc_iff.2 hi)
  simp only [gapL, stripDriver, stripPoint, extPath]
  rw [abs_of_pos (sub_pos.2 (vL_last_lt_vL_castSucc h.path hl i₀)), abs_of_pos (sub_pos.2 h1)]
  have := Real.log_le_log (sub_pos.2 h1) (sub_le_sub_right h3 (vL (Fin.last nL) _))
  linarith

theorem intervalIntegrable_cothHalf_gapL (h : StripGood a pL xR ρL ρR w vL vR b ζ) (i : Fin nL) {s t : ℝ}
    (hs : 0 ≤ s) (hst : s ≤ t) : IntervalIntegrable (fun r => Sec4.cothHalf (gapL w vL i r)) volume s t :=
  ((continuousOn_cothHalf_comp (h.continuousOn_gapL_Ici i) fun u hu => h.gapL_pos i hu).mono
    (by rw [uIcc_of_le hst]; exact fun u hu => hs.trans hu.1)).intervalIntegrable

theorem intervalIntegrable_cothHalf_gapR (h : StripGood a pL xR ρL ρR w vL vR b ζ) (j : Fin nR) {s t : ℝ}
    (hs : 0 ≤ s) (hst : s ≤ t) : IntervalIntegrable (fun r => Sec4.cothHalf (gapR w vL vR j r)) volume s t :=
  ((continuousOn_cothHalf_comp (h.continuousOn_gapR_Ici j) fun u hu => h.gapR_pos j hu).mono
    (by rw [uIcc_of_le hst]; exact fun u hu => hs.trans hu.1)).intervalIntegrable

theorem intervalIntegrable_stripErr (h : StripGood a pL xR ρL ρR w vL vR b ζ) (ρl : Fin nL → ℝ)
    (ρr : Fin nR → ℝ) {s t : ℝ} (hs : 0 ≤ s) (hst : s ≤ t) :
    IntervalIntegrable (stripErr ρl ρr w vL vR) volume s t :=
  ((h.continuousOn_stripErr_Ici ρl ρr).mono
    (by rw [uIcc_of_le hst]; exact fun u hu => hs.trans hu.1)).intervalIntegrable

theorem gapL_diff (h : StripGood a pL xR ρL ρR w vL vR b ζ) (i i₀ : Fin nL) {s t : ℝ} (hs : 0 ≤ s)
    (hst : s ≤ t) :
    (gapL w vL i t - gapL w vL i₀ t) - (gapL w vL i s - gapL w vL i₀ s) =
      ∫ r in s..t, (Sec4.cothHalf (gapL w vL i r) - Sec4.cothHalf (gapL w vL i₀ r)) := by
  rw [intervalIntegral.integral_sub (h.intervalIntegrable_cothHalf_gapL i hs hst)
    (h.intervalIntegrable_cothHalf_gapL i₀ hs hst)]
  have h1 := h.gapL_sub i hs hst
  have h2 := h.gapL_sub i₀ hs hst
  linarith

theorem gapR_diff (h : StripGood a pL xR ρL ρR w vL vR b ζ) (j j₀ : Fin nR) {s t : ℝ} (hs : 0 ≤ s)
    (hst : s ≤ t) :
    (gapR w vL vR j t - gapR w vL vR j₀ t) - (gapR w vL vR j s - gapR w vL vR j₀ s) =
      ∫ r in s..t, (Sec4.cothHalf (gapR w vL vR j r) - Sec4.cothHalf (gapR w vL vR j₀ r)) := by
  rw [intervalIntegral.integral_sub (h.intervalIntegrable_cothHalf_gapR j hs hst)
    (h.intervalIntegrable_cothHalf_gapR j₀ hs hst)]
  have h1 := h.gapR_sub j hs hst
  have h2 := h.gapR_sub j₀ hs hst
  linarith

/-- The two nearest opposite gaps together grow at rate at least `2`. -/
theorem two_mul_le_gapL_add_gapR (h : StripGood a pL xR ρL ρR w vL vR b ζ) (i : Fin nL) (j : Fin nR)
    {u : ℝ} (hu : 0 ≤ u) : 2 * u ≤ gapL w vL i u + gapR w vL vR j u := by
  have h1 := h.gapL_sub i le_rfl hu
  have h2 := h.gapR_sub j le_rfl hu
  have hL : u ≤ ∫ r in (0 : ℝ)..u, Sec4.cothHalf (gapL w vL i r) := by
    have := intervalIntegral.integral_mono_on (μ := volume) hu intervalIntegrable_const
      (h.intervalIntegrable_cothHalf_gapL i le_rfl hu) fun r hr => Sec4.one_le_cothHalf (h.gapL_pos i hr.1)
    simpa using this
  have hR : u ≤ ∫ r in (0 : ℝ)..u, Sec4.cothHalf (gapR w vL vR j r) := by
    have := intervalIntegral.integral_mono_on (μ := volume) hu intervalIntegrable_const
      (h.intervalIntegrable_cothHalf_gapR j le_rfl hu) fun r hr => Sec4.one_le_cothHalf (h.gapR_pos j hr.1)
    simpa using this
  linarith [h.gapL_pos i le_rfl, h.gapR_pos j le_rfl]

/-- A comparison gap on the left side for the right escape: the nearest left gap, or `2u + 1` without left
marks. -/
theorem exists_cmp_left (h : StripGood a pL xR ρL ρR w vL vR b ζ) :
    ∃ Y : ℝ → ℝ, ContinuousOn Y (Ici 0) ∧ (∀ u, 0 ≤ u → 0 < Y u) ∧
      (∀ i u, 0 ≤ u → Y u ≤ gapL w vL i u) ∧
      (∀ i s t, 0 ≤ s → s ≤ t → (gapL w vL i t - Y t) - (gapL w vL i s - Y s) =
        ∫ r in s..t, (Sec4.cothHalf (gapL w vL i r) - Sec4.cothHalf (Y r))) ∧
      ∀ j u, 0 ≤ u → 2 * u ≤ gapR w vL vR j u + Y u := by
  rcases Nat.eq_zero_or_pos nL with hn | hn
  · subst hn
    refine ⟨fun u => 2 * u + 1, by fun_prop, fun u hu => by linarith, fun i => i.elim0, fun i => i.elim0,
      fun j u hu => by linarith [h.gapR_pos j hu]⟩
  · set i₀ : Fin nL := ⟨0, hn⟩
    refine ⟨gapL w vL i₀, h.continuousOn_gapL_Ici i₀, fun u hu => h.gapL_pos i₀ hu,
      fun i u hu => h.gapL_le_gapL (Fin.le_iff_val_le_val.2 (Nat.zero_le _)) hu,
      fun i s t hs hst => h.gapL_diff i i₀ hs hst,
      fun j u hu => by linarith [h.two_mul_le_gapL_add_gapR i₀ j hu]⟩

/-- A comparison gap on the right side for the left escape. -/
theorem exists_cmp_right (h : StripGood a pL xR ρL ρR w vL vR b ζ) :
    ∃ Y : ℝ → ℝ, ContinuousOn Y (Ici 0) ∧ (∀ u, 0 ≤ u → 0 < Y u) ∧
      (∀ j u, 0 ≤ u → Y u ≤ gapR w vL vR j u) ∧
      (∀ j s t, 0 ≤ s → s ≤ t → (gapR w vL vR j t - Y t) - (gapR w vL vR j s - Y s) =
        ∫ r in s..t, (Sec4.cothHalf (gapR w vL vR j r) - Sec4.cothHalf (Y r))) ∧
      ∀ i u, 0 ≤ u → 2 * u ≤ gapL w vL i u + Y u := by
  rcases Nat.eq_zero_or_pos nR with hn | hn
  · subst hn
    refine ⟨fun u => 2 * u + 1, by fun_prop, fun u hu => by linarith, fun j => j.elim0, fun j => j.elim0,
      fun i u hu => by linarith [h.gapL_pos i hu]⟩
  · set j₀ : Fin nR := ⟨0, hn⟩
    refine ⟨gapR w vL vR j₀, h.continuousOn_gapR_Ici j₀, fun u hu => h.gapR_pos j₀ hu,
      fun j u hu => h.gapR_le_gapR (Fin.le_iff_val_le_val.2 (Nat.zero_le _)) hu,
      fun j s t hs hst => h.gapR_diff j j₀ hs hst,
      fun i u hu => h.two_mul_le_gapL_add_gapR i j₀ hu⟩

variable {ρl : Fin nL → ℝ} {ρr : Fin nR → ℝ} {N : ℝ → ℝ} {σ : ℝ}

theorem stripDriver_sub (h : StripGood a pL xR ρL ρR w vL vR b ζ)
    (hξ : ∀ u, 0 ≤ u → stripDriver (extPath w) (extPath (vL (Fin.last nL))) u =
      N u + σ * u + ∫ r in (0 : ℝ)..u, stripErr ρl ρr w vL vR r) {s t : ℝ} (hs : 0 ≤ s) (hst : s ≤ t) :
    stripDriver (extPath w) (extPath (vL (Fin.last nL))) t -
      stripDriver (extPath w) (extPath (vL (Fin.last nL))) s =
      (N t - N s) + σ * (t - s) + ∫ r in s..t, stripErr ρl ρr w vL vR r := by
  rw [hξ t (hs.trans hst), hξ s hs]
  have := intervalIntegral.integral_interval_sub_left (μ := volume)
    (h.intervalIntegrable_stripErr ρl ρr le_rfl (hs.trans hst)) (h.intervalIntegrable_stripErr ρl ρr le_rfl hs)
  linarith

/-- **Linear escape of the lower right strip gaps** (Astra (3.24)): if the strip driver is `N + σ t + ∫ e` with `N`
sublinear, `σ < 1` and right side sum `≥ −2`, every lower right gap eventually exceeds `α t`. -/
theorem exists_right_escape (h : StripGood a pL xR ρL ρR w vL vR b ζ)
    (hξ : ∀ u, 0 ≤ u → stripDriver (extPath w) (extPath (vL (Fin.last nL))) u =
      N u + σ * u + ∫ r in (0 : ℝ)..u, stripErr ρl ρr w vL vR r)
    (hN : ∀ ε > 0, ∃ C, ∀ u, 0 ≤ u → |N u| ≤ C + ε * u)
    (hsr : 0 ≤ 1 + (∑ j, ρr j) / 2) (hσR : σ < 1) :
    ∃ α > 0, ∃ T, ∀ t, T ≤ t → ∀ j, α * t ≤ gapR w vL vR j t := by
  rcases Nat.eq_zero_or_pos nR with hn | hn
  · exact ⟨1, one_pos, 0, fun t _ j => absurd j.2 (by omega)⟩
  · set j₀ : Fin nR := ⟨0, hn⟩
    obtain ⟨Y, hYc, hY0, hYle, hYd, hXY⟩ := h.exists_cmp_left
    have heq : ∀ s t, 0 ≤ s → s ≤ t → gapR w vL vR j₀ t - gapR w vL vR j₀ s = -(N t - N s) +
        ∫ r in s..t, (Sec4.cothHalf (gapR w vL vR j₀ r) + -σ +
          (∑ j, ρr j / 2 * (Sec4.cothHalf (gapR w vL vR j r) - 1)) -
          ∑ i, ρl i / 2 * (Sec4.cothHalf (gapL w vL i r) - 1)) := by
      intro s t hs hst
      have h1 := h.gapR_sub j₀ hs hst
      have h2 := h.stripDriver_sub hξ hs hst
      have hI : ∫ r in s..t, (Sec4.cothHalf (gapR w vL vR j₀ r) + -σ +
          (∑ j, ρr j / 2 * (Sec4.cothHalf (gapR w vL vR j r) - 1)) -
          ∑ i, ρl i / 2 * (Sec4.cothHalf (gapL w vL i r) - 1)) =
          (∫ r in s..t, Sec4.cothHalf (gapR w vL vR j₀ r)) - σ * (t - s) -
            ∫ r in s..t, stripErr ρl ρr w vL vR r := by
        rw [intervalIntegral.integral_congr
          (g := fun r => (Sec4.cothHalf (gapR w vL vR j₀ r) - σ) - stripErr ρl ρr w vL vR r)
          (fun r _ => by simp only [stripErr]; ring),
          intervalIntegral.integral_sub ((h.intervalIntegrable_cothHalf_gapR j₀ hs hst).sub
            intervalIntegrable_const) (h.intervalIntegrable_stripErr ρl ρr hs hst),
          intervalIntegral.integral_sub (h.intervalIntegrable_cothHalf_gapR j₀ hs hst) intervalIntegrable_const,
          intervalIntegral.integral_const, smul_eq_mul]
        ring
      rw [hI]
      linarith
    obtain ⟨α, hα, T, hT⟩ := eventually_mul_le_of_side (Xo := gapR w vL vR) (Yp := gapL w vL)
      (X := gapR w vL vR j₀) (Y := Y) (N := N) (ρo := ρr) (ρp := ρl) (c := -σ) (K := 0)
      (h.continuousOn_gapR_Ici j₀) hYc h.continuousOn_gapR_Ici h.continuousOn_gapL_Ici
      (fun u hu => h.gapR_pos j₀ hu) hY0
      (fun j u hu => h.gapR_le_gapR (Fin.le_iff_val_le_val.2 (Nat.zero_le _)) hu) hYle
      (fun j s t hs hst => h.gapR_diff j j₀ hs hst) hYd (fun u hu => by linarith [hXY j₀ u hu])
      heq hN hsr (by linarith)
    refine ⟨α, hα, max T 0, fun t ht j => ?_⟩
    have ht0 : 0 ≤ t := (le_max_right _ _).trans ht
    exact (hT t ((le_max_left _ _).trans ht)).trans
      (h.gapR_le_gapR (Fin.le_iff_val_le_val.2 (Nat.zero_le _)) ht0)

/-- **Linear escape of the lower left strip gaps** (Astra (3.24), reflected): if the strip driver is `N + σ t + ∫ e`
with `N` sublinear, `σ > −1` and left side sum `≥ −2`, every lower left gap eventually exceeds `α t`. -/
theorem exists_left_escape (h : StripGood a pL xR ρL ρR w vL vR b ζ)
    (hξ : ∀ u, 0 ≤ u → stripDriver (extPath w) (extPath (vL (Fin.last nL))) u =
      N u + σ * u + ∫ r in (0 : ℝ)..u, stripErr ρl ρr w vL vR r)
    (hN : ∀ ε > 0, ∃ C, ∀ u, 0 ≤ u → |N u| ≤ C + ε * u)
    (hsl : 0 ≤ 1 + (∑ i, ρl i) / 2) (hσL : -1 < σ) :
    ∃ α > 0, ∃ T, ∀ t, T ≤ t → ∀ i, α * t ≤ gapL w vL i t := by
  rcases Nat.eq_zero_or_pos nL with hn | hn
  · exact ⟨1, one_pos, 0, fun t _ i => absurd i.2 (by omega)⟩
  · set i₀ : Fin nL := ⟨0, hn⟩
    obtain ⟨Y, hYc, hY0, hYle, hYd, hXY⟩ := h.exists_cmp_right
    have heq : ∀ s t, 0 ≤ s → s ≤ t → gapL w vL i₀ t - gapL w vL i₀ s =
        -((fun u => -N u) t - (fun u => -N u) s) +
        ∫ r in s..t, (Sec4.cothHalf (gapL w vL i₀ r) + σ +
          (∑ i, ρl i / 2 * (Sec4.cothHalf (gapL w vL i r) - 1)) -
          ∑ j, ρr j / 2 * (Sec4.cothHalf (gapR w vL vR j r) - 1)) := by
      intro s t hs hst
      have h1 := h.gapL_sub i₀ hs hst
      have h2 := h.stripDriver_sub hξ hs hst
      have hI : ∫ r in s..t, (Sec4.cothHalf (gapL w vL i₀ r) + σ +
          (∑ i, ρl i / 2 * (Sec4.cothHalf (gapL w vL i r) - 1)) -
          ∑ j, ρr j / 2 * (Sec4.cothHalf (gapR w vL vR j r) - 1)) =
          (∫ r in s..t, Sec4.cothHalf (gapL w vL i₀ r)) + σ * (t - s) +
            ∫ r in s..t, stripErr ρl ρr w vL vR r := by
        rw [intervalIntegral.integral_congr
          (g := fun r => (Sec4.cothHalf (gapL w vL i₀ r) + σ) + stripErr ρl ρr w vL vR r)
          (fun r _ => by simp only [stripErr]; ring),
          intervalIntegral.integral_add ((h.intervalIntegrable_cothHalf_gapL i₀ hs hst).add
            intervalIntegrable_const) (h.intervalIntegrable_stripErr ρl ρr hs hst),
          intervalIntegral.integral_add (h.intervalIntegrable_cothHalf_gapL i₀ hs hst) intervalIntegrable_const,
          intervalIntegral.integral_const, smul_eq_mul]
        ring
      rw [hI]
      linarith
    obtain ⟨α, hα, T, hT⟩ := eventually_mul_le_of_side (Xo := gapL w vL) (Yp := gapR w vL vR)
      (X := gapL w vL i₀) (Y := Y) (N := fun u => -N u) (ρo := ρl) (ρp := ρr) (c := σ) (K := 0)
      (h.continuousOn_gapL_Ici i₀) hYc h.continuousOn_gapL_Ici h.continuousOn_gapR_Ici
      (fun u hu => h.gapL_pos i₀ hu) hY0
      (fun i u hu => h.gapL_le_gapL (Fin.le_iff_val_le_val.2 (Nat.zero_le _)) hu) hYle
      (fun i s t hs hst => h.gapL_diff i i₀ hs hst) hYd (fun u hu => by linarith [hXY i₀ u hu])
      heq (fun ε hε => (hN ε hε).imp fun C hC u hu => by simpa only [abs_neg] using hC u hu) hsl
      (by linarith)
    refine ⟨α, hα, max T 0, fun t ht i => ?_⟩
    have ht0 : 0 ≤ t := (le_max_right _ _).trans ht
    exact (hT t ((le_max_left _ _).trans ht)).trans
      (h.gapL_le_gapL (Fin.le_iff_val_le_val.2 (Nat.zero_le _)) ht0)

/-- **Linear escape of every lower strip gap** (Astra (3.24): "Under (3.3), both escape slopes are positive"): if
the strip driver is `N + σ t + ∫ e` with `N` sublinear, `|σ| < 1` and both side sums `≥ −2`, then every lower strip
gap eventually exceeds `α t` for some `α > 0`. -/
theorem exists_linear_escape (h : StripGood a pL xR ρL ρR w vL vR b ζ)
    (hξ : ∀ u, 0 ≤ u → stripDriver (extPath w) (extPath (vL (Fin.last nL))) u =
      N u + σ * u + ∫ r in (0 : ℝ)..u, stripErr ρl ρr w vL vR r)
    (hN : ∀ ε > 0, ∃ C, ∀ u, 0 ≤ u → |N u| ≤ C + ε * u)
    (hsl : 0 ≤ 1 + (∑ i, ρl i) / 2) (hsr : 0 ≤ 1 + (∑ j, ρr j) / 2) (hσ : |σ| < 1) :
    ∃ α > 0, ∃ T, ∀ t, T ≤ t → (∀ i, α * t ≤ gapL w vL i t) ∧ ∀ j, α * t ≤ gapR w vL vR j t := by
  have hσ' := abs_lt.1 hσ
  have hR := h.exists_right_escape hξ hN hsr hσ'.2
  have hL := h.exists_left_escape hξ hN hsl hσ'.1
  obtain ⟨αR, hαR, TR, hTR⟩ := hR
  obtain ⟨αL, hαL, TL, hTL⟩ := hL
  refine ⟨min αL αR, lt_min hαL hαR, max (max TL TR) 0, fun t ht => ⟨fun i => ?_, fun j => ?_⟩⟩
  · have ht0 : 0 ≤ t := (le_max_right _ _).trans ht
    exact (mul_le_mul_of_nonneg_right (min_le_left _ _) ht0).trans
      (hTL t ((le_max_left _ _).trans ((le_max_left _ _).trans ht)) i)
  · have ht0 : 0 ≤ t := (le_max_right _ _).trans ht
    exact (mul_le_mul_of_nonneg_right (min_le_right _ _) ht0).trans
      (hTR t ((le_max_right _ _).trans ((le_max_left _ _).trans ht)) j)

/-- `|C(g) − 1| ≤ 4 e^{−αt}` once the gap `g ≥ αt ≥ log 2`. -/
theorem abs_cothHalf_sub_one_le {g α t : ℝ} (hg : α * t ≤ g) (h2 : Real.log 2 ≤ α * t) :
    |Sec4.cothHalf g - 1| ≤ 4 * Real.exp (-(α * t)) := by
  have hg0 : 0 < g := lt_of_lt_of_le (Real.log_pos (by norm_num)) (h2.trans hg)
  rw [abs_of_nonneg (by linarith [Sec4.one_le_cothHalf hg0])]
  exact (Sec4.cothHalf_sub_one_le (h2.trans hg)).trans
    (mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 (neg_le_neg hg)) (by norm_num))

/-- **The drift error decays exponentially**: `|e_t| ≤ B e^{−αt}` once all gaps exceed `αt ≥ log 2`. -/
theorem abs_stripErr_le {α t : ℝ}
    (hgap : (∀ i, α * t ≤ gapL w vL i t) ∧ ∀ j, α * t ≤ gapR w vL vR j t) (h2 : Real.log 2 ≤ α * t) :
    |stripErr ρl ρr w vL vR t| ≤ (2 * ((∑ i, |ρl i|) + ∑ j, |ρr j|)) * Real.exp (-(α * t)) := by
  unfold stripErr
  refine (abs_sub _ _).trans ?_
  have hL : |∑ i, ρl i / 2 * (Sec4.cothHalf (gapL w vL i t) - 1)| ≤
      (∑ i, |ρl i|) * (2 * Real.exp (-(α * t))) := by
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    rw [Finset.sum_mul]
    refine Finset.sum_le_sum fun i _ => ?_
    rw [abs_mul, abs_div, abs_two]
    have := abs_cothHalf_sub_one_le (hgap.1 i) h2
    nlinarith [abs_nonneg (ρl i)]
  have hR : |∑ j, ρr j / 2 * (Sec4.cothHalf (gapR w vL vR j t) - 1)| ≤
      (∑ j, |ρr j|) * (2 * Real.exp (-(α * t))) := by
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    rw [Finset.sum_mul]
    refine Finset.sum_le_sum fun j _ => ?_
    rw [abs_mul, abs_div, abs_two]
    have := abs_cothHalf_sub_one_le (hgap.2 j) h2
    nlinarith [abs_nonneg (ρr j)]
  linarith

/-- `∫_{T}^{t} B² e^{−2αr} dr ≤ B²/(2α)` for `0 ≤ T`. -/
theorem integral_sq_exp_le {B α T t : ℝ} (hα : 0 < α) (hT : 0 ≤ T) :
    ∫ r in T..t, B ^ 2 * Real.exp (-(2 * α * r)) ≤ B ^ 2 / (2 * α) := by
  have hF : ∀ r ∈ uIcc T t, HasDerivAt (fun r => -(B ^ 2 / (2 * α)) * Real.exp (-(2 * α * r)))
      (B ^ 2 * Real.exp (-(2 * α * r))) r := fun r _ => by
    have h1 : HasDerivAt (fun r : ℝ => -(2 * α * r)) (-(2 * α)) r := by
      have h0 := (hasDerivAt_id r).const_mul (-(2 * α))
      rw [mul_one] at h0
      exact h0.congr_of_eventuallyEq (Filter.Eventually.of_forall fun y => by simp only [id]; ring)
    refine (h1.exp.const_mul (-(B ^ 2 / (2 * α)))).congr_deriv ?_
    field_simp
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hF (by
    apply Continuous.intervalIntegrable; fun_prop)]
  have h1 : Real.exp (-(2 * α * T)) ≤ 1 := Real.exp_le_one_iff.2 (by nlinarith)
  have h2 : 0 ≤ Real.exp (-(2 * α * t)) := (Real.exp_pos _).le
  have h3 : 0 ≤ B ^ 2 / (2 * α) := by positivity
  nlinarith

/-- **The error is eventually small and has bounded tail energy**: after linear escape, there are `T' ≥ 0` and
`M` with `|e_t| ≤ 1` and `∫_{T'}^t e² ≤ M` for all `t ≥ T'`. -/
theorem exists_stripErr_bound (h : StripGood a pL xR ρL ρR w vL vR b ζ) {α T : ℝ} (hα : 0 < α)
    (hT : ∀ t, T ≤ t → (∀ i, α * t ≤ gapL w vL i t) ∧ ∀ j, α * t ≤ gapR w vL vR j t) :
    ∃ T' : ℝ, 0 ≤ T' ∧ ∃ M : ℝ, ∀ t, T' ≤ t → |stripErr ρl ρr w vL vR t| ≤ 1 ∧
      ∫ r in T'..t, stripErr ρl ρr w vL vR r ^ 2 ≤ M := by
  set B := 2 * ((∑ i, |ρl i|) + ∑ j, |ρr j|) + 1 with hB
  have hB1 : 1 ≤ B := by
    have : 0 ≤ (∑ i, |ρl i|) + ∑ j, |ρr j| :=
      add_nonneg (Finset.sum_nonneg fun i _ => abs_nonneg _) (Finset.sum_nonneg fun j _ => abs_nonneg _)
    linarith
  set T' := max (max T 0) (max (Real.log 2 / α) (Real.log B / α)) with hT'
  have hT'0 : 0 ≤ T' := (le_max_right _ _).trans (le_max_left _ _)
  have hbound : ∀ t, T' ≤ t → |stripErr ρl ρr w vL vR t| ≤ B * Real.exp (-(α * t)) := by
    intro t ht
    have h1 : T ≤ t := (le_max_left _ _).trans ((le_max_left _ _).trans ht)
    have h2 : Real.log 2 ≤ α * t := by
      have : Real.log 2 / α ≤ t := (le_max_left _ _).trans ((le_max_right _ _).trans ht)
      rwa [div_le_iff₀ hα, mul_comm] at this
    refine (abs_stripErr_le (hT t h1) h2).trans (mul_le_mul_of_nonneg_right (by linarith)
      (Real.exp_pos _).le)
  refine ⟨T', hT'0, B ^ 2 / (2 * α), fun t ht => ⟨?_, ?_⟩⟩
  · refine (hbound t ht).trans ?_
    have h3 : Real.log B ≤ α * t := by
      have : Real.log B / α ≤ t := (le_max_right _ _).trans ((le_max_right _ _).trans ht)
      rwa [div_le_iff₀ hα, mul_comm] at this
    have : Real.exp (-(α * t)) ≤ B⁻¹ := by
      rw [Real.exp_neg, inv_le_inv₀ (Real.exp_pos _) (by linarith)]
      calc B = Real.exp (Real.log B) := (Real.exp_log (by linarith)).symm
        _ ≤ Real.exp (α * t) := Real.exp_le_exp.2 h3
    calc B * Real.exp (-(α * t)) ≤ B * B⁻¹ := mul_le_mul_of_nonneg_left this (by linarith)
      _ = 1 := mul_inv_cancel₀ (by linarith)
  · have hle : ∫ r in T'..t, stripErr ρl ρr w vL vR r ^ 2 ≤ ∫ r in T'..t, B ^ 2 * Real.exp (-(2 * α * r)) := by
      refine intervalIntegral.integral_mono_on ht
        (((h.continuousOn_stripErr_Ici ρl ρr).pow 2).mono (by
          rw [uIcc_of_le ht]; exact fun u hu => hT'0.trans hu.1)).intervalIntegrable
        (by apply Continuous.intervalIntegrable; fun_prop) fun r hr => ?_
      have h1 := hbound r hr.1
      have h2 : B ^ 2 * Real.exp (-(2 * α * r)) = (B * Real.exp (-(α * r))) ^ 2 := by
        rw [mul_pow, ← Real.exp_nat_mul]; ring_nf
      rw [h2, ← sq_abs]
      exact pow_le_pow_left₀ (abs_nonneg _) h1 2
    exact hle.trans (integral_sq_exp_le hα hT'0)

/-- The left part of the error, `Σᵢ (ρᴸᵢ/2)(C(Xᵢ) − 1)`, decays like `e^{−αt}` once the left gaps exceed
`αt ≥ log 2`. -/
theorem abs_leftErr_le {α t : ℝ} (hgap : ∀ i, α * t ≤ gapL w vL i t) (h2 : Real.log 2 ≤ α * t) :
    |∑ i, ρl i / 2 * (Sec4.cothHalf (gapL w vL i t) - 1)| ≤
      (2 * ∑ i, |ρl i|) * Real.exp (-(α * t)) := by
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  rw [mul_comm 2, mul_assoc, Finset.sum_mul]
  refine Finset.sum_le_sum fun i _ => ?_
  rw [abs_mul, abs_div, abs_two]
  have := abs_cothHalf_sub_one_le (hgap i) h2
  nlinarith [abs_nonneg (ρl i)]

/-- **Bounded strip-time energy of the left error** after the left escape: `∫₀ᵗ (Σᵢ (ρᴸᵢ/2)(C(Xᵢ) − 1))² ≤ m` for
all `t ≥ 0` (the strip-time form of the bounded left side energy; with PROVE-ZHAN-B4's `integral_sq_sideErr_eq`
this is its `HasBoundedSideEnergy` in the chart of the outermost left mark). -/
theorem exists_leftErr_energy (h : StripGood a pL xR ρL ρR w vL vR b ζ) {α T : ℝ} (hα : 0 < α)
    (hT : ∀ t, T ≤ t → ∀ i, α * t ≤ gapL w vL i t) :
    ∃ m : ℝ, ∀ t : ℝ, 0 ≤ t →
      ∫ u in (0 : ℝ)..t, (∑ i, ρl i / 2 * (Sec4.cothHalf (gapL w vL i u) - 1)) ^ 2 ≤ m := by
  set f : ℝ → ℝ := fun u => (∑ i, ρl i / 2 * (Sec4.cothHalf (gapL w vL i u) - 1)) ^ 2 with hf
  have hfc : ContinuousOn f (Ici 0) :=
    (continuousOn_finsetSum _ fun i _ => continuousOn_const.mul ((continuousOn_cothHalf_comp
      (h.continuousOn_gapL_Ici i) fun u hu => h.gapL_pos i hu).sub continuousOn_const)).pow 2
  have hfi : ∀ a b : ℝ, 0 ≤ a → 0 ≤ b → IntervalIntegrable f volume a b := fun a b ha hb =>
    (hfc.mono fun u hu => by
      rcases le_total a b with hab | hab
      · rw [uIcc_of_le hab] at hu; exact ha.trans hu.1
      · rw [uIcc_of_ge hab] at hu; exact hb.trans hu.1).intervalIntegrable
  obtain ⟨B, hB⟩ : ∃ B : ℝ, B = 2 * ∑ i, |ρl i| := ⟨_, rfl⟩
  set T₁ := max (max T 0) (Real.log 2 / α) with hT₁
  have hT₁0 : 0 ≤ T₁ := (le_max_right _ _).trans (le_max_left _ _)
  have hbd : ∀ u, T₁ ≤ u → f u ≤ B ^ 2 * Real.exp (-(2 * α * u)) := fun u hu => by
    have h1 : T ≤ u := (le_max_left _ _).trans ((le_max_left _ _).trans hu)
    have h2 : Real.log 2 ≤ α * u := by
      have : Real.log 2 / α ≤ u := (le_max_right _ _).trans hu
      rwa [div_le_iff₀ hα, mul_comm] at this
    have h3 := abs_leftErr_le (ρl := ρl) (hT u h1) h2
    rw [← hB] at h3
    have h4 : (B * Real.exp (-(α * u))) ^ 2 = B ^ 2 * Real.exp (-(2 * α * u)) := by
      rw [mul_pow, ← Real.exp_nat_mul]; ring_nf
    calc f u = |∑ i, ρl i / 2 * (Sec4.cothHalf (gapL w vL i u) - 1)| ^ 2 := (sq_abs _).symm
      _ ≤ (B * Real.exp (-(α * u))) ^ 2 := pow_le_pow_left₀ (abs_nonneg _) h3 2
      _ = B ^ 2 * Real.exp (-(2 * α * u)) := h4
  have hnn : ∀ a b : ℝ, a ≤ b → 0 ≤ ∫ u in a..b, f u := fun a b hab =>
    intervalIntegral.integral_nonneg hab fun u _ => sq_nonneg _
  refine ⟨(∫ u in (0 : ℝ)..T₁, f u) + B ^ 2 / (2 * α), fun t ht => ?_⟩
  have hBα : 0 ≤ B ^ 2 / (2 * α) := by positivity
  have hsplit := intervalIntegral.integral_add_adjacent_intervals (μ := volume) (hfi 0 T₁ le_rfl hT₁0)
    (hfi T₁ t hT₁0 ht)
  rcases le_total t T₁ with htT | htT
  · have hsplit' := intervalIntegral.integral_add_adjacent_intervals (μ := volume) (hfi 0 t le_rfl ht)
      (hfi t T₁ ht hT₁0)
    have := hnn t T₁ htT
    linarith
  · have hle : ∫ u in T₁..t, f u ≤ ∫ u in T₁..t, B ^ 2 * Real.exp (-(2 * α * u)) :=
      intervalIntegral.integral_mono_on htT (hfi T₁ t hT₁0 ht)
        (by apply Continuous.intervalIntegrable; fun_prop) fun u hu => hbd u hu.1
    have := integral_sq_exp_le (B := B) hα hT₁0 (t := t)
    linarith

end StripGood

end Zhan

end InteractingSLE
