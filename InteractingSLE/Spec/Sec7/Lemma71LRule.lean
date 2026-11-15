/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.Lemma71LClock
import InteractingSLE.Spec.Sec5.CrossRestartLawPath

/-!
# Lemma 7.1: the capacity stopping rule of the mapped segment, cut at the closing point

Packet PROVE-LEMMA71L, item R3/G7 (deterministic part). The original time `τ_t` at which the mapped prefix reaches
capacity `t` is the level rule of the grid capacity of the chart values of the middle coordinates
(`Lemma71Pin.levelRule_capFamily_eq`, PROVE-LEMMA71J). If the mapped segment has a finite terminal capacity `t`, that
level rule is reached at the closing time of the pocket; `capRule` therefore returns `⊤` unless the middle curve has
stayed away from the closing point `y₀` up to the level time (`EndOK`), so that `capRule … (2t) < ⊤` exactly when
`t` is below the terminal capacity.

* `capRule` (definition), **`capRule_galmarino`**, **`measurable_capRule`**;
* along a visit clock: **`capRule_eq_visitClock`**, `capRule_zero_eq`, **`lt_capLife_of_capRule_lt_top`**,
  **`ofReal_lt_capLife_iff`** (the terminal capacity read on rational coordinates before the closing point),
  **`inter_image_nonempty_iff`** (the mapped prefix meets a compact `Q` iff chart values of rational coordinates before
  the level time come arbitrarily close to `Q`).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology Metric Complex Bornology
open scoped NNReal ENNReal Real

namespace InteractingSLE.Sec7.Lemma71L

open QuantumZipper (H Hbar)
open QuantumZipper.CA (cayley cayleyInv)
open Lemma71I Lemma71C Sec6

section Rule

variable {X : Type*}

open Classical in
/-- **The capacity stopping rule cut at the closing point**: the level rule of the grid capacity family if it is
finite and the coordinates before it stay away from the closing point `Y x`, and `⊤` otherwise. -/
def capRule (G : X × ℂ → ℂ) (M : Set (X × ℂ)) (Y : X → ℂ) (a : ℝ≥0∞) (x : X) (c : ℚ≥0 → ℂ) : ℝ≥0∞ :=
  if levelRule (capFamily G M) a x c < ⊤ ∧ EndOK (Y x) (levelRule (capFamily G M) a x c) c then
    levelRule (capFamily G M) a x c else ⊤

variable {G : X × ℂ → ℂ} {M : Set (X × ℂ)} {Y : X → ℂ} {a : ℝ≥0∞}

theorem capRule_of_cond {x : X} {c : ℚ≥0 → ℂ}
    (h : levelRule (capFamily G M) a x c < ⊤ ∧ EndOK (Y x) (levelRule (capFamily G M) a x c) c) :
    capRule G M Y a x c = levelRule (capFamily G M) a x c := by
  simp only [capRule, h, and_self, ↓reduceIte]

theorem capRule_of_not_cond {x : X} {c : ℚ≥0 → ℂ}
    (h : ¬(levelRule (capFamily G M) a x c < ⊤ ∧ EndOK (Y x) (levelRule (capFamily G M) a x c) c)) :
    capRule G M Y a x c = ⊤ := by
  simp only [capRule, h, ↓reduceIte]

/-- **The cut rule is Galmarino**: it depends only on the coordinates up to its value. -/
theorem capRule_galmarino (x : X) (c c' : ℚ≥0 → ℂ)
    (h : ∀ q : ℚ≥0, ((q : ℝ≥0) : ℝ≥0∞) ≤ capRule G M Y a x c → c q = c' q) :
    capRule G M Y a x c' = capRule G M Y a x c := by
  by_cases hc : levelRule (capFamily G M) a x c < ⊤ ∧ EndOK (Y x) (levelRule (capFamily G M) a x c) c
  · have hval := capRule_of_cond hc
    rw [hval] at h
    have hL : levelRule (capFamily G M) a x c' = levelRule (capFamily G M) a x c :=
      levelRule_galmarino (capFamily_local G M) x c c' h
    have hc' : levelRule (capFamily G M) a x c' < ⊤ ∧ EndOK (Y x) (levelRule (capFamily G M) a x c') c' := by
      rw [hL]
      exact ⟨hc.1, (endOK_congr h).1 hc.2⟩
    rw [capRule_of_cond hc', hval, hL]
  · have hval := capRule_of_not_cond hc
    rw [hval] at h
    have hcc : c' = c := funext fun q => (h q le_top).symm
    rw [hcc]

/-- **The cut rule is jointly measurable.** -/
theorem measurable_capRule [MeasurableSpace X] (hG : Measurable G) (hM : MeasurableSet M) (hY : Measurable Y)
    (a : ℝ≥0∞) : Measurable fun p : X × (ℚ≥0 → ℂ) => capRule G M Y a p.1 p.2 := by
  classical
  have hL : Measurable fun p : X × (ℚ≥0 → ℂ) => levelRule (capFamily G M) a p.1 p.2 :=
    measurable_levelRule (measurable_capFamily hG hM)
  have hset : MeasurableSet {p : X × (ℚ≥0 → ℂ) | levelRule (capFamily G M) a p.1 p.2 < ⊤ ∧
      EndOK (Y p.1) (levelRule (capFamily G M) a p.1 p.2) p.2} :=
    (measurableSet_lt hL measurable_const).inter (measurableSet_endOK hY hL)
  have heq : (fun p : X × (ℚ≥0 → ℂ) => capRule G M Y a p.1 p.2) = fun p =>
      if p ∈ {p : X × (ℚ≥0 → ℂ) | levelRule (capFamily G M) a p.1 p.2 < ⊤ ∧
        EndOK (Y p.1) (levelRule (capFamily G M) a p.1 p.2) p.2} then
        levelRule (capFamily G M) a p.1 p.2 else ⊤ := by
    funext p
    rfl
  rw [heq]
  exact Measurable.ite hset hL measurable_const

/-- The level rule at level `0` is `0`. -/
theorem levelRule_zero (f : ℚ≥0 → X → (ℚ≥0 → ℂ) → ℝ≥0∞) (x : X) (c : ℚ≥0 → ℂ) : levelRule f 0 x c = 0 := by
  have hinf : levelInf f 0 x c = 0 := by
    refine le_antisymm ((iInf_le _ 0).trans ?_) zero_le
    simp only [zero_le, ↓reduceIte, NNRat.cast_zero, ENNReal.coe_zero, le_refl]
  simp only [levelRule, hinf, zero_le, ↓reduceIte]

end Rule

/-! ### Along a visit clock -/

section Clock

variable {X : Type*} {G : X × ℂ → ℂ} {M : Set (X × ℂ)} {Y : X → ℂ} {x : X} {C : Set ℂ} {F : ℂ → ℂ}
  {γ : ℝ≥0 → ℂ} {Γ : ℝ → ℂ} {κ : ℝ → ℝ}

/-- Along a visit clock, the chart values of the rational coordinates up to a time before which the curve stays away
from the closing point lie in a bounded prefix of the mapped segment, so their grid capacity is below the terminal
one. -/
theorem capFamily_le_of_bound (hM : ∀ z, (x, z) ∈ M ↔ z ∈ C) (hG : ∀ z ∈ C, G (x, z) = F z)
    (hFc : ContinuousOn F C) (hΓ : IsSegCurve Γ) (hvc : IsVisitClock C F γ Γ κ) {T : ℝ} {U : ℝ} (hU : 0 ≤ U)
    (hb : ∀ u, 0 ≤ u → κ u ≤ T → u ≤ U) {q : ℚ≥0} (hq : ((q : ℝ≥0) : ℝ) ≤ T) :
    capFamily G M q x (pathCoord γ) ≤ ENNReal.ofReal (2 * capClock Γ U) := by
  obtain ⟨-, -, -, hlim, hcov, -⟩ := hvc
  calc capFamily G M q x (pathCoord γ) ≤ WholeField.hcapHit (Γ '' Icc 0 U) := by
        refine Lemma71Pin.hcapHit_mono ((Lemma71Pin.capSet_subset hM hG hFc hlim hcov q).trans ?_)
        rintro _ ⟨u, ⟨hu, hκu⟩, rfl⟩
        exact ⟨u, ⟨hu, hb u hu (hκu.trans hq)⟩, rfl⟩
    _ = _ := Lemma71Pin.hcapHit_image_eq_capClock hΓ hU

/-- **The cut rule is the visit-clock time of the capacity time** `t` (`0 < t` below the terminal capacity). -/
theorem capRule_eq_visitClock (hM : ∀ z, (x, z) ∈ M ↔ z ∈ C) (hG : ∀ z ∈ C, G (x, z) = F z) (hCo : IsOpen C)
    (hFc : ContinuousOn F C) (hγ : Continuous γ) (hΓ : IsSegCurve Γ) (hvc : IsVisitClock C F γ Γ κ)
    (hD1 : ∀ u, 0 ≤ u → EndOK (Y x) (ENNReal.ofReal (κ u)) (pathCoord γ))
    {t : ℝ} (ht : 0 < t) (htl : ENNReal.ofReal t < capLife Γ) :
    capRule G M Y (ENNReal.ofReal (2 * t)) x (pathCoord γ) = ENNReal.ofReal (κ (capInv Γ t)) := by
  obtain ⟨hκc, hκm, hκ0, hlim, hcov, hdense⟩ := hvc
  have hL := Lemma71Pin.levelRule_capFamily_eq hM hG hCo hFc hγ hΓ hκc hκm hκ0 hlim hcov hdense ht htl
  rw [capRule_of_cond ⟨by rw [hL]; exact ENNReal.ofReal_lt_top, by rw [hL]; exact hD1 _ (capInv_nonneg Γ t)⟩, hL]

/-- **At capacity time `0` the cut rule is `0`.** -/
theorem capRule_zero_eq {c : ℚ≥0 → ℂ} (hE : EndOK (Y x) 0 c) : capRule G M Y 0 x c = 0 := by
  rw [capRule_of_cond ⟨by rw [levelRule_zero]; exact ENNReal.zero_lt_top, by rw [levelRule_zero]; exact hE⟩,
    levelRule_zero]

/-- **A finite cut rule at the level `2t` means that `t` is below the terminal capacity.** -/
theorem lt_capLife_of_capRule_lt_top (hM : ∀ z, (x, z) ∈ M ↔ z ∈ C) (hG : ∀ z ∈ C, G (x, z) = F z)
    (hFc : ContinuousOn F C) (hΓ : IsSegCurve Γ) (hvc : IsVisitClock C F γ Γ κ)
    (hD2 : ∀ T : ℝ≥0, EndOK (Y x) T (pathCoord γ) → ∃ U, ∀ u, 0 ≤ u → κ u ≤ T → u ≤ U)
    {t : ℝ} (hlt : capRule G M Y (ENNReal.ofReal (2 * t)) x (pathCoord γ) < ⊤) :
    ENNReal.ofReal t < capLife Γ := by
  classical
  set f := capFamily G M with hf
  set L := levelRule f (ENNReal.ofReal (2 * t)) x (pathCoord γ) with hLdef
  have hcond : L < ⊤ ∧ EndOK (Y x) L (pathCoord γ) := by
    by_contra hc
    rw [capRule_of_not_cond hc] at hlt
    exact lt_irrefl _ hlt
  -- the level is reached at `L`
  have hreach : ENNReal.ofReal (2 * t) ≤ runSup f x (pathCoord γ) L := by
    by_cases hc : ENNReal.ofReal (2 * t) ≤
        runSup f x (pathCoord γ) (levelInf f (ENNReal.ofReal (2 * t)) x (pathCoord γ))
    · have hLeq : L = levelInf f (ENNReal.ofReal (2 * t)) x (pathCoord γ) := by
        rw [hLdef, levelRule]
        simp only [hc, ↓reduceIte]
      rw [hLeq]
      exact hc
    · have : L = ⊤ := by
        rw [hLdef, levelRule]
        simp only [hc, ↓reduceIte]
      exact absurd this hcond.1.ne
  set T : ℝ≥0 := L.toNNReal with hT
  have hLT : L = (T : ℝ≥0∞) := (ENNReal.coe_toNNReal hcond.1.ne).symm
  obtain ⟨U₀, hU₀⟩ := hD2 T (hLT ▸ hcond.2)
  set U := max U₀ 0 with hU
  have hU0 : 0 ≤ U := le_max_right _ _
  have hb : ∀ u, 0 ≤ u → κ u ≤ (T : ℝ) → u ≤ U := fun u hu hκu => (hU₀ u hu hκu).trans (le_max_left _ _)
  have hrun : runSup f x (pathCoord γ) L ≤ ENNReal.ofReal (2 * capClock Γ U) := by
    refine iSup_le fun q => ?_
    split_ifs with hq
    · have hq' : ((q : ℝ≥0) : ℝ) ≤ (T : ℝ) := by
        rw [hLT, ENNReal.coe_le_coe] at hq
        exact_mod_cast hq
      exact capFamily_le_of_bound hM hG hFc hΓ hvc hU0 hb hq'
    · exact zero_le
  have h2 : 2 * t ≤ 2 * capClock Γ U := by
    have := hreach.trans hrun
    rwa [ENNReal.ofReal_le_ofReal_iff (by linarith [hΓ.capClock_nonneg hU0])] at this
  calc ENNReal.ofReal t ≤ ENNReal.ofReal (capClock Γ U) := ENNReal.ofReal_le_ofReal (by linarith)
    _ < capLife Γ := hΓ.ofReal_capClock_lt hU0

/-- A nonnegative rational strictly between two reals `0 ≤ a < b`. -/
theorem exists_nnrat_btwn {a b : ℝ} (ha : 0 ≤ a) (hab : a < b) :
    ∃ q : ℚ≥0, a < ((q : ℝ≥0) : ℝ) ∧ ((q : ℝ≥0) : ℝ) < b := by
  obtain ⟨q, hq1, hq2⟩ := exists_rat_btwn hab
  have hq0 : (0 : ℚ) ≤ q := by exact_mod_cast (ha.trans hq1.le)
  have hq'r : (((q.toNNRat : ℚ≥0) : ℝ≥0) : ℝ) = q := by
    have : (((q.toNNRat : ℚ≥0) : ℝ≥0) : ℝ) = ((q.toNNRat : ℚ) : ℝ) := rfl
    rw [this, Rat.coe_toNNRat q hq0]
  exact ⟨q.toNNRat, by rw [hq'r]; exact hq1, by rw [hq'r]; exact hq2⟩

/-- **The terminal capacity on rational coordinates**: `r` is below the terminal capacity iff the grid capacity of the
chart values up to some rational time before which the curve stays away from the closing point exceeds `2r`. -/
theorem ofReal_lt_capLife_iff (hM : ∀ z, (x, z) ∈ M ↔ z ∈ C) (hG : ∀ z ∈ C, G (x, z) = F z) (hCo : IsOpen C)
    (hFc : ContinuousOn F C) (hγ : Continuous γ) (hΓ : IsSegCurve Γ) (hvc : IsVisitClock C F γ Γ κ)
    (hD1 : ∀ u, 0 ≤ u → EndOK (Y x) (ENNReal.ofReal (κ u)) (pathCoord γ))
    (hD2 : ∀ T : ℝ≥0, EndOK (Y x) T (pathCoord γ) → ∃ U, ∀ u, 0 ≤ u → κ u ≤ T → u ≤ U)
    {r : ℝ} (hr : 0 ≤ r) :
    ENNReal.ofReal r < capLife Γ ↔ ∃ q : ℚ≥0, EndOK (Y x) ((q : ℝ≥0) : ℝ≥0∞) (pathCoord γ) ∧
      ENNReal.ofReal (2 * r) < capFamily G M q x (pathCoord γ) := by
  constructor
  · intro hlt
    obtain ⟨n, hn⟩ := exists_lt_capClock_of_lt_capLife hlt
    set V : ℝ := (n : ℝ) with hV
    have hV0 : 0 < V := by
      rcases (Nat.cast_nonneg n : (0 : ℝ) ≤ n).eq_or_lt with h | h
      · have hV' : V = 0 := by rw [hV]; exact h.symm
        rw [hV', hΓ.capClock_zero] at hn
        linarith
      · exact h
    obtain ⟨hκc, hκm, hκ0, hlim, hcov, hdense⟩ := hvc
    have hκV : 0 ≤ κ V := hκ0.trans (hκm.monotoneOn self_mem_Ici hV0.le hV0.le)
    obtain ⟨q, hq1, hq2⟩ := exists_nnrat_btwn hκV (hκm hV0.le (by linarith : (0 : ℝ) ≤ V + 1) (by linarith))
    refine ⟨q, (hD1 (V + 1) (by linarith)).mono ?_, ?_⟩
    · rw [← ENNReal.ofReal_coe_nnreal]
      exact ENNReal.ofReal_le_ofReal hq2.le
    · have hsub := Lemma71Pin.image_Icc_subset_closure_capSet hM hG hCo hFc hγ hΓ.1 hκm hκ0 hlim hcov hdense
        (q := q) hV0 hq1.le
      have hcap : WholeField.hcapHit (Γ '' Icc 0 V) ≤ capFamily G M q x (pathCoord γ) := by
        refine (Lemma71Pin.hcapHit_mono hsub).trans ?_
        rw [Sec5.CrossRestart.hcapHit_closure]
        rfl
      rw [Lemma71Pin.hcapHit_image_eq_capClock hΓ hV0.le] at hcap
      refine lt_of_lt_of_le ?_ hcap
      rw [ENNReal.ofReal_lt_ofReal_iff (by linarith)]
      linarith
  · rintro ⟨q, hE, hlt⟩
    obtain ⟨U₀, hU₀⟩ := hD2 q hE
    set U := max U₀ 0 with hU
    have hU0 : 0 ≤ U := le_max_right _ _
    have hb : ∀ u, 0 ≤ u → κ u ≤ ((q : ℝ≥0) : ℝ) → u ≤ U := fun u hu hκu =>
      (hU₀ u hu hκu).trans (le_max_left _ _)
    have hle := capFamily_le_of_bound hM hG hFc hΓ hvc hU0 hb le_rfl
    have h2 : 2 * r < 2 * capClock Γ U := by
      have := hlt.trans_le hle
      rwa [ENNReal.ofReal_lt_ofReal_iff_of_nonneg (by linarith)] at this
    calc ENNReal.ofReal r ≤ ENNReal.ofReal (capClock Γ U) := ENNReal.ofReal_le_ofReal (by linarith)
      _ < capLife Γ := hΓ.ofReal_capClock_lt hU0

/-- **The mapped prefix meets a compact `Q`** (capacity time `r` below the terminal one) iff chart values of rational
coordinates in the pocket before the level time of `2r` come arbitrarily close to `Q`. -/
theorem inter_image_nonempty_iff (hM : ∀ z, (x, z) ∈ M ↔ z ∈ C) (hG : ∀ z ∈ C, G (x, z) = F z)
    (hCo : IsOpen C) (hFc : ContinuousOn F C) (hγ : Continuous γ) (hΓ : IsSegCurve Γ)
    (hvc : IsVisitClock C F γ Γ κ) {r : ℝ} (hr : 0 < r) (hrl : ENNReal.ofReal r < capLife Γ) {Q : Set ℂ}
    (hQ : IsCompact Q) (hQne : Q.Nonempty) :
    (Q ∩ Γ '' Icc 0 (capInv Γ r)).Nonempty ↔ ∀ m : ℕ, ∃ q : ℚ≥0,
      ((q : ℝ≥0) : ℝ≥0∞) ≤ levelRule (capFamily G M) (ENNReal.ofReal (2 * r)) x (pathCoord γ) ∧
        (x, γ q) ∈ M ∧ infDist (G (x, γ q)) Q < 1 / ((m : ℝ) + 1) := by
  obtain ⟨hκc, hκm, hκ0, hlim, hcov, hdense⟩ := hvc
  have hL := Lemma71Pin.levelRule_capFamily_eq hM hG hCo hFc hγ hΓ hκc hκm hκ0 hlim hcov hdense hr hrl
  rw [hL]
  obtain ⟨hU0, hUr⟩ := hΓ.capInv_spec hr.le hrl
  set U := capInv Γ r with hUdef
  have hUpos : 0 < U := by
    rcases hU0.eq_or_lt with h | h
    · rw [← h, hΓ.capClock_zero] at hUr
      linarith
    · exact h
  have hκU : 0 ≤ κ U := hκ0.trans (hκm.monotoneOn self_mem_Ici hU0 hU0)
  have hcast : ∀ q : ℚ≥0, ((q : ℝ≥0) : ℝ≥0∞) ≤ ENNReal.ofReal (κ U) ↔ ((q : ℝ≥0) : ℝ) ≤ κ U := fun q => by
    rw [← ENNReal.ofReal_coe_nnreal, ENNReal.ofReal_le_ofReal_iff hκU]
  simp_rw [hcast]
  constructor
  · rintro ⟨_, hwQ, u, hu, rfl⟩ m
    have hε : (0 : ℝ) < 1 / ((m : ℝ) + 1) := by positivity
    -- a point `u' < U` of the mapped segment near `Γ u`
    obtain ⟨δ, hδ, hball⟩ := Metric.continuousWithinAt_iff.1 (hΓ.1 u hu.1) _ (half_pos hε)
    set u' := max 0 (u - δ / 2) with hu'
    have hu'0 : 0 ≤ u' := le_max_left _ _
    have hu'U : u' < U := by
      rcases le_total 0 (u - δ / 2) with h | h
      · rw [hu', max_eq_right h]; linarith [hu.2]
      · rw [hu', max_eq_left h]; exact hUpos
    have hdu : dist u' u < δ := by
      rw [Real.dist_eq, abs_lt]
      constructor
      · have := le_max_right 0 (u - δ / 2); linarith
      · rcases le_total 0 (u - δ / 2) with h | h
        · rw [hu', max_eq_right h]; linarith
        · rw [hu', max_eq_left h]; linarith [hu.1]
    have hd1 := hball (show u' ∈ Ici (0 : ℝ) from hu'0) hdu
    -- a rational time between the clock times of `(u' + U)/2` and `U`
    set U' := (u' + U) / 2 with hU'
    have hU'pos : 0 < U' := by rw [hU']; linarith
    have hU'lt : U' < U := by rw [hU']; linarith
    have hκU'0 : 0 ≤ κ U' := hκ0.trans (hκm.monotoneOn self_mem_Ici hU'pos.le hU'pos.le)
    obtain ⟨q, hq1, hq2⟩ := exists_nnrat_btwn hκU'0 (hκm hU'pos.le hU0 hU'lt)
    have hsub := Lemma71Pin.image_Icc_subset_closure_capSet hM hG hCo hFc hγ hΓ.1 hκm hκ0 hlim hcov hdense
      (q := q) hU'pos hq1.le
    have hmem : Γ u' ∈ closure (capSet G M q x (pathCoord γ)) :=
      hsub ⟨u', ⟨hu'0, by rw [hU']; linarith⟩, rfl⟩
    obtain ⟨_, ⟨r', hr'q, hr'M, rfl⟩, hd2⟩ := Metric.mem_closure_iff.1 hmem _ (half_pos hε)
    refine ⟨r', ?_, hr'M, ?_⟩
    · have : ((r' : ℝ≥0) : ℝ) ≤ ((q : ℝ≥0) : ℝ) := by exact_mod_cast hr'q
      linarith
    · calc infDist (G (x, γ r')) Q ≤ dist (G (x, γ r')) (Γ u) := infDist_le_dist_of_mem hwQ
        _ ≤ dist (G (x, γ r')) (Γ u') + dist (Γ u') (Γ u) := dist_triangle _ _ _
        _ < 1 / ((m : ℝ) + 1) / 2 + 1 / ((m : ℝ) + 1) / 2 := by
            rw [dist_comm] at hd2
            exact add_lt_add hd2 hd1
        _ = 1 / ((m : ℝ) + 1) := by ring
  · intro hall
    by_contra hempty
    rw [not_nonempty_iff_eq_empty] at hempty
    set K := Γ '' Icc 0 U with hK
    have hKc : IsCompact K := isCompact_Icc.image_of_continuousOn (hΓ.1.mono Icc_subset_Ici_self)
    have hKne : K.Nonempty := ⟨Γ 0, mem_image_of_mem _ ⟨le_rfl, hU0⟩⟩
    obtain ⟨p₀, hp₀K, hp₀⟩ := hKc.exists_isMinOn hKne (continuous_infDist_pt Q).continuousOn
    have hp₀Q : p₀ ∉ Q := fun h => (eq_empty_iff_forall_notMem.1 hempty) p₀ ⟨h, hp₀K⟩
    have hδ : 0 < infDist p₀ Q := (hQ.isClosed.notMem_iff_infDist_pos hQne).1 hp₀Q
    obtain ⟨m, hm⟩ := exists_nat_one_div_lt hδ
    obtain ⟨q, hqU, hqM, hqd⟩ := hall m
    have hGK : G (x, γ q) ∈ K := by
      have hcs : G (x, γ q) ∈ capSet G M q x (pathCoord γ) := ⟨q, le_rfl, hqM, rfl⟩
      obtain ⟨u, ⟨hu, hκu⟩, hGu⟩ := Lemma71Pin.capSet_subset hM hG hFc hlim hcov q hcs
      refine ⟨u, ⟨hu, ?_⟩, hGu⟩
      by_contra hgt
      have := hκm hU0 hu (not_le.1 hgt)
      linarith
    have := hp₀ hGK
    simp only [mem_ofPred_eq] at this
    linarith

end Clock

end InteractingSLE.Sec7.Lemma71L
