/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec2.AddMarksMerge
import InteractingSLE.Spec.Sec4.ZeroMarks

/-!
# A passive zero-weight mark at a real point, along one path

Packet PROVE-G12B. Proof of Corollary W0a (supplement §9, p. 528): "If a seed is not already a boundary jump for the
other flow, retain it as a passive zero-weight mark; this does not change the driving law or the displayed cumulative
weight." Lemma G12 (`Supp7.G12EvolStatement`) is therefore needed at points `y > 0` that are not marks.

Along one path of an integrated evolution, the passive mark at `y` is the Loewner flow `v = y + ∫ 2/(v − w)` of `y`
until `y` is swallowed, and afterwards the force coordinate `v_k` of the last mark `x_k < y` (the two meet at the
swallowing time). The flow is read off the cut flows `U_n` (`Sec2.markFlow` with the cut drift
`2/max(x, δ_n)`, `δ_n = 1/(n+1)`): `y` is *alive at level `n`* at time `t` when `U_n − w ≥ 2δ_n` on `[0, t]`, and
then `U_m = U_n` on `[0, t]` for every `m ≥ n` (uniqueness of the cut equation).

This file is deterministic. For a driver `w` and cut flows `U` with the properties of `PassHyp`:

* `IsAliveAt`, `Alive`, `passEnd`: the life of `y` and its end `τ` (`lt_passEnd_iff`: `t < τ ↔ Alive t`);
* `pflow`: the flow of `y` on its life (`pflow_eq_integral`: the Loewner equation; `continuousOn_pflow`);
* `tendsto_pflow_passEnd`, `vk_passEnd_eq`: at a finite end `τ < ζ` the flow tends to `w(τ)`, and so does every
  force coordinate starting below `y`;
* `passMarkPath`: the glued passive mark, and its properties (`PassMarkGood`): the force-point equation, continuity,
  integrability, the null collision set and the order with the other marks.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology
open scoped NNReal ENNReal

namespace InteractingSLE

namespace Supp7

namespace G12

/-! ### Cut levels -/

/-- The cut levels `δ_n = 1/(n+1)`. -/
def passDelta (n : ℕ) : ℝ := 1 / ((n : ℝ) + 1)

theorem passDelta_pos (n : ℕ) : 0 < passDelta n := by unfold passDelta; positivity

theorem passDelta_anti {n m : ℕ} (h : n ≤ m) : passDelta m ≤ passDelta n := by
  unfold passDelta
  have : (n : ℝ) ≤ m := by exact_mod_cast h
  gcongr

theorem exists_two_mul_passDelta_le {c : ℝ} (hc : 0 < c) : ∃ n, 2 * passDelta n ≤ c := by
  obtain ⟨n, hn⟩ := exists_nat_gt (2 / c)
  refine ⟨n, ?_⟩
  unfold passDelta
  have hn1 : (0 : ℝ) < n + 1 := by positivity
  rw [mul_one_div, div_le_iff₀ hn1]
  rw [div_lt_iff₀ hc] at hn
  nlinarith

/-! ### The cut flows of one path -/

/-- The properties of the cut flows `U n` of `y` driven by `w` before `ζ` (on a path along which `w` is continuous;
`Sec2.markFlow_eq_of_continuousOn` and uniqueness of the cut equation). -/
structure PassHyp (w : ℝ≥0 → ℝ) (ζ : ℝ≥0∞) (y : ℝ) (U : ℕ → ℝ≥0 → ℝ) : Prop where
  y_pos : 0 < y
  w_zero : w 0 = 0
  cont_w : ContinuousOn w {t | (t : ℝ≥0∞) < ζ}
  cont_U : ∀ n, ContinuousOn (U n) {t | (t : ℝ≥0∞) < ζ}
  zero_U : ∀ n, U n 0 = y
  eq_U : ∀ n {t : ℝ≥0}, (t : ℝ≥0∞) < ζ →
    U n t = y + ∫ s in (0 : ℝ)..t, Sec2.rightMarkDrift (passDelta n) (U n s.toNNReal - w s.toNNReal)
  uniq_U : ∀ n {t₁ : ℝ≥0}, (t₁ : ℝ≥0∞) < ζ → ∀ u : ℝ → ℝ, ContinuousOn u (Icc 0 (t₁ : ℝ)) →
    (∀ s ∈ Icc (0 : ℝ) t₁, u s = y + ∫ r in (0 : ℝ)..s, Sec2.rightMarkDrift (passDelta n) (u r - w r.toNNReal)) →
    ∀ s ∈ Icc (0 : ℝ) t₁, U n s.toNNReal = u s

variable {w : ℝ≥0 → ℝ} {ζ : ℝ≥0∞} {y : ℝ} {U : ℕ → ℝ≥0 → ℝ}

/-- `y` is alive at level `n` at time `t < ζ`: the cut flow keeps the gap `≥ 2δ_n` on `[0, t]`. -/
def IsAliveAt (w : ℝ≥0 → ℝ) (ζ : ℝ≥0∞) (U : ℕ → ℝ≥0 → ℝ) (n : ℕ) (t : ℝ≥0) : Prop :=
  (t : ℝ≥0∞) < ζ ∧ ∀ s ≤ t, 2 * passDelta n ≤ U n s - w s

/-- `y` is alive at time `t` (at some level). -/
def Alive (w : ℝ≥0 → ℝ) (ζ : ℝ≥0∞) (U : ℕ → ℝ≥0 → ℝ) (t : ℝ≥0) : Prop := ∃ n, IsAliveAt w ζ U n t

/-- The flow of `y` on its life: the limit of the cut flows (eventually constant). -/
def pflow (U : ℕ → ℝ≥0 → ℝ) (t : ℝ≥0) : ℝ := limsup (fun n => U n t) atTop

/-- The integrand of a real point's flow on a time set where the gap is at least `δ`. -/
theorem integral_rightMarkDrift_eq {δ : ℝ} {g : ℝ≥0 → ℝ} {t : ℝ≥0}
    (hg : ∀ s ≤ t, δ ≤ g s - w s) :
    ∫ r in (0 : ℝ)..t, Sec2.rightMarkDrift δ (g r.toNNReal - w r.toNNReal) =
      ∫ r in (0 : ℝ)..t, 2 / (g r.toNNReal - w r.toNNReal) := by
  refine intervalIntegral.integral_congr fun r hr => ?_
  rw [uIcc_of_le t.coe_nonneg] at hr
  exact Sec2.rightMarkDrift_of_le (hg _ (Real.toNNReal_le_iff_le_coe.2 hr.2))

/-- **Uniqueness of the cut flow.** A function solving the Loewner equation of `y` on `[0, t₁]`, `t₁ < ζ`, with gap
`≥ δ_n` there, is the cut flow `U n` on `[0, t₁]`. -/
theorem PassHyp.eq_of_solves (hH : PassHyp w ζ y U) (n : ℕ) {t₁ : ℝ≥0} (ht₁ : (t₁ : ℝ≥0∞) < ζ)
    {g : ℝ≥0 → ℝ} (hgc : ContinuousOn g (Icc 0 t₁))
    (hgeq : ∀ s ≤ t₁, g s = y + ∫ r in (0 : ℝ)..s, 2 / (g r.toNNReal - w r.toNNReal))
    (hgap : ∀ s ≤ t₁, passDelta n ≤ g s - w s) : ∀ s ≤ t₁, U n s = g s := by
  intro s hs
  have hmaps : MapsTo Real.toNNReal (Icc (0 : ℝ) t₁) (Icc 0 t₁) := fun r hr =>
    ⟨zero_le, Real.toNNReal_le_iff_le_coe.2 hr.2⟩
  have h := hH.uniq_U n ht₁ (fun r => g r.toNNReal) (hgc.comp continuous_real_toNNReal.continuousOn hmaps)
    (fun r hr => ?_) s ⟨s.coe_nonneg, hs⟩
  · simpa using h
  · have hr' : r.toNNReal ≤ t₁ := Real.toNNReal_le_iff_le_coe.2 hr.2
    rw [hgeq _ hr', Real.coe_toNNReal _ hr.1]
    congr 1
    refine intervalIntegral.integral_congr fun q hq => ?_
    rw [uIcc_of_le hr.1] at hq
    have hq' : q.toNNReal ≤ t₁ := Real.toNNReal_le_iff_le_coe.2 (hq.2.trans hr.2)
    exact (Sec2.rightMarkDrift_of_le (hgap _ hq')).symm

/-- On a life at level `n`, the cut flow solves the Loewner equation. -/
theorem PassHyp.eq_integral_of_isAliveAt (hH : PassHyp w ζ y U) {n : ℕ} {t : ℝ≥0}
    (ha : IsAliveAt w ζ U n t) {s : ℝ≥0} (hs : s ≤ t) :
    U n s = y + ∫ r in (0 : ℝ)..s, 2 / (U n r.toNNReal - w r.toNNReal) := by
  rw [hH.eq_U n (lt_of_le_of_lt (ENNReal.coe_le_coe.2 hs) ha.1),
    integral_rightMarkDrift_eq (δ := passDelta n) fun r hr => ?_]
  have := ha.2 r (hr.trans hs)
  linarith [passDelta_pos n]

theorem PassHyp.continuousOn_Icc (hH : PassHyp w ζ y U) (n : ℕ) {t : ℝ≥0} (ht : (t : ℝ≥0∞) < ζ) :
    ContinuousOn (U n) (Icc 0 t) :=
  (hH.cont_U n).mono fun _s hs => lt_of_le_of_lt (ENNReal.coe_le_coe.2 hs.2) ht

/-- **Higher levels agree on a life.** -/
theorem PassHyp.agree (hH : PassHyp w ζ y U) {n m : ℕ} {t : ℝ≥0} (ha : IsAliveAt w ζ U n t) (hnm : n ≤ m) :
    ∀ s ≤ t, U m s = U n s :=
  hH.eq_of_solves m ha.1 (hH.continuousOn_Icc n ha.1) (fun s hs => hH.eq_integral_of_isAliveAt ha hs)
    fun s hs => by linarith [ha.2 s hs, passDelta_anti hnm, passDelta_pos n]

theorem PassHyp.isAliveAt_mono (hH : PassHyp w ζ y U) {n m : ℕ} {t : ℝ≥0} (ha : IsAliveAt w ζ U n t)
    (hnm : n ≤ m) : IsAliveAt w ζ U m t :=
  ⟨ha.1, fun s hs => by rw [hH.agree ha hnm s hs]; linarith [ha.2 s hs, passDelta_anti hnm]⟩

theorem isAliveAt_anti {n : ℕ} {t t' : ℝ≥0} (ha : IsAliveAt w ζ U n t) (h : t' ≤ t) : IsAliveAt w ζ U n t' :=
  ⟨lt_of_le_of_lt (ENNReal.coe_le_coe.2 h) ha.1, fun s hs => ha.2 s (hs.trans h)⟩

theorem alive_anti {t t' : ℝ≥0} (ha : Alive w ζ U t) (h : t' ≤ t) : Alive w ζ U t' :=
  let ⟨n, hn⟩ := ha; ⟨n, isAliveAt_anti hn h⟩

/-- On a life at level `n`, the flow is the cut flow `U n`. -/
theorem PassHyp.pflow_eq (hH : PassHyp w ζ y U) {n : ℕ} {t : ℝ≥0} (ha : IsAliveAt w ζ U n t) {s : ℝ≥0}
    (hs : s ≤ t) : pflow U s = U n s := by
  refine Tendsto.limsup_eq (tendsto_atTop_of_eventually_const (i₀ := n) fun m hm => ?_)
  exact hH.agree ha hm s hs

/-- `y` is alive at time `0`. -/
theorem PassHyp.alive_zero (hH : PassHyp w ζ y U) (hζ : 0 < ζ) : Alive w ζ U 0 := by
  obtain ⟨n, hn⟩ := exists_two_mul_passDelta_le hH.y_pos
  refine ⟨n, by simpa using hζ, fun s hs => ?_⟩
  rw [nonpos_iff_eq_zero.1 hs, hH.zero_U, hH.w_zero, sub_zero]
  exact hn

/-- **The life is open**: `y` alive at `t` is alive slightly later. -/
theorem PassHyp.exists_alive_gt (hH : PassHyp w ζ y U) {t : ℝ≥0} (ha : Alive w ζ U t) :
    ∃ t' > t, Alive w ζ U t' := by
  obtain ⟨n, hn⟩ := ha
  obtain ⟨t₂, htt₂, ht₂ζ⟩ := ENNReal.lt_iff_exists_nnreal_btwn.1 hn.1
  have htt₂' : t < t₂ := by exact_mod_cast htt₂
  -- the gap stays `≥ δ_n` a little after `t`
  have hcont : ContinuousAt (fun s => U n s - w s) t := by
    have hopen : IsOpen {s : ℝ≥0 | (s : ℝ≥0∞) < ζ} := isOpen_lt ENNReal.continuous_coe continuous_const
    exact ((hH.cont_U n).sub hH.cont_w).continuousAt (hopen.mem_nhds hn.1)
  have hev : ∀ᶠ s in 𝓝 t, passDelta n < U n s - w s :=
    hcont.eventually (lt_mem_nhds (by linarith [hn.2 t le_rfl, passDelta_pos n]))
  obtain ⟨t₃, ht₃, hsub⟩ := (mem_nhdsGE_iff_exists_Ico_subset (a := t)).1
    (mem_nhdsWithin_of_mem_nhds hev)
  set t₄ := min t₃ t₂ with ht₄
  have htt₄ : t < t₄ := lt_min ht₃ htt₂'
  set t' : ℝ≥0 := (t + t₄) / 2 with ht'
  have htt' : t < t' := by rw [ht']; exact left_lt_add_div_two.2 htt₄
  have ht't₄ : t' < t₄ := by rw [ht']; exact add_div_two_lt_right.2 htt₄
  have ht't₃ : t' < t₃ := lt_of_lt_of_le ht't₄ (min_le_left _ _)
  have ht'ζ : (t' : ℝ≥0∞) < ζ :=
    lt_of_le_of_lt (ENNReal.coe_le_coe.2 (ht't₄.le.trans (min_le_right _ _))) ht₂ζ
  have hgap : ∀ s ≤ t', passDelta n ≤ U n s - w s := by
    intro s hs
    rcases le_or_gt s t with hst | hst
    · linarith [hn.2 s hst, passDelta_pos n]
    · exact (hsub ⟨hst.le, lt_of_le_of_lt hs ht't₃⟩).le
  obtain ⟨m, hm⟩ := exists_two_mul_passDelta_le (passDelta_pos n)
  have hsol : ∀ s ≤ t', U n s = y + ∫ r in (0 : ℝ)..s, 2 / (U n r.toNNReal - w r.toNNReal) := by
    intro s hs
    rw [hH.eq_U n (lt_of_le_of_lt (ENNReal.coe_le_coe.2 hs) ht'ζ),
      integral_rightMarkDrift_eq (δ := passDelta n) fun r hr => hgap r (hr.trans hs)]
  have hagree := hH.eq_of_solves m ht'ζ (hH.continuousOn_Icc n ht'ζ) hsol
    fun s hs => by linarith [hgap s hs, passDelta_pos m]
  exact ⟨t', htt', m, ht'ζ, fun s hs => by rw [hagree s hs]; linarith [hgap s hs]⟩

/-! ### The end of the life -/

/-- The end `τ` of the life of `y`. -/
def passEnd (w : ℝ≥0 → ℝ) (ζ : ℝ≥0∞) (U : ℕ → ℝ≥0 → ℝ) : ℝ≥0∞ :=
  ⨆ (t : ℝ≥0) (_ : Alive w ζ U t), (t : ℝ≥0∞)

theorem passEnd_le : passEnd w ζ U ≤ ζ :=
  iSup₂_le fun _ ht => let ⟨_, hn⟩ := ht; hn.1.le

/-- **The life is `[0, τ)`.** -/
theorem PassHyp.lt_passEnd_iff (hH : PassHyp w ζ y U) {t : ℝ≥0} :
    (t : ℝ≥0∞) < passEnd w ζ U ↔ Alive w ζ U t := by
  constructor
  · intro h
    rw [passEnd, lt_iSup_iff] at h
    obtain ⟨t', ht'⟩ := h
    rw [lt_iSup_iff] at ht'
    obtain ⟨ha, hlt⟩ := ht'
    exact alive_anti ha (by exact_mod_cast hlt.le)
  · intro h
    obtain ⟨t', htt', ha'⟩ := hH.exists_alive_gt h
    exact lt_of_lt_of_le (by exact_mod_cast htt')
      (le_iSup₂ (f := fun t (_ : Alive w ζ U t) => (t : ℝ≥0∞)) t' ha')

/-! ### The flow on the life -/

/-- **The Loewner equation of `y` on its life.** -/
theorem PassHyp.pflow_eq_integral (hH : PassHyp w ζ y U) {t : ℝ≥0} (ha : Alive w ζ U t) :
    pflow U t = y + ∫ r in (0 : ℝ)..t, 2 / (pflow U r.toNNReal - w r.toNNReal) := by
  obtain ⟨n, hn⟩ := ha
  rw [hH.pflow_eq hn le_rfl, hH.eq_integral_of_isAliveAt hn le_rfl]
  congr 1
  refine intervalIntegral.integral_congr fun r hr => ?_
  rw [uIcc_of_le t.coe_nonneg] at hr
  simp only [hH.pflow_eq hn (Real.toNNReal_le_iff_le_coe.2 hr.2)]

theorem PassHyp.gap_ge (hH : PassHyp w ζ y U) {n : ℕ} {t : ℝ≥0} (hn : IsAliveAt w ζ U n t) {s : ℝ≥0}
    (hs : s ≤ t) : 2 * passDelta n ≤ pflow U s - w s := by
  rw [hH.pflow_eq hn hs]; exact hn.2 s hs

theorem PassHyp.w_lt_pflow (hH : PassHyp w ζ y U) {t : ℝ≥0} (ha : Alive w ζ U t) : w t < pflow U t := by
  obtain ⟨n, hn⟩ := ha
  linarith [hH.gap_ge hn le_rfl, passDelta_pos n]

theorem PassHyp.continuousAt_pflow (hH : PassHyp w ζ y U) {t : ℝ≥0} (ha : Alive w ζ U t) :
    ContinuousAt (pflow U) t := by
  obtain ⟨t', htt', n, hn⟩ := hH.exists_alive_gt ha
  have hopen : IsOpen {s : ℝ≥0 | (s : ℝ≥0∞) < ζ} := isOpen_lt ENNReal.continuous_coe continuous_const
  have hU : ContinuousAt (U n) t := (hH.cont_U n).continuousAt
    (hopen.mem_nhds (lt_of_le_of_lt (ENNReal.coe_le_coe.2 htt'.le) hn.1))
  refine hU.congr ?_
  filter_upwards [Iio_mem_nhds htt'] with s hs
  exact (hH.pflow_eq hn hs.le).symm

theorem PassHyp.continuousOn_pflow (hH : PassHyp w ζ y U) :
    ContinuousOn (pflow U) {t | (t : ℝ≥0∞) < passEnd w ζ U} := fun _ ht =>
  (hH.continuousAt_pflow (hH.lt_passEnd_iff.1 ht)).continuousWithinAt

/-- On the life, the integrand `2/(v − w)` is continuous on `[0, t]`. -/
theorem PassHyp.continuousOn_integrand (hH : PassHyp w ζ y U) {t : ℝ≥0} (ha : Alive w ζ U t) :
    ContinuousOn (fun r : ℝ => 2 / (pflow U r.toNNReal - w r.toNNReal)) (Icc 0 (t : ℝ)) := by
  obtain ⟨n, hn⟩ := ha
  have hmaps : MapsTo Real.toNNReal (Icc (0 : ℝ) t) (Icc 0 t) := fun r hr =>
    ⟨zero_le, Real.toNNReal_le_iff_le_coe.2 hr.2⟩
  have hc : ContinuousOn (fun r : ℝ≥0 => U n r - w r) (Icc 0 t) :=
    (hH.continuousOn_Icc n hn.1).sub (hH.cont_w.mono fun _s hs =>
      lt_of_le_of_lt (ENNReal.coe_le_coe.2 hs.2) hn.1)
  have hc2 : ContinuousOn (fun r : ℝ => 2 / (U n r.toNNReal - w r.toNNReal)) (Icc 0 (t : ℝ)) :=
    ContinuousOn.div continuousOn_const (hc.comp continuous_real_toNNReal.continuousOn hmaps) fun r hr => by
      have := hn.2 _ (hmaps hr).2
      linarith [passDelta_pos n]
  refine hc2.congr fun r hr => ?_
  simp only [hH.pflow_eq hn (hmaps hr).2]

theorem PassHyp.intervalIntegrable_integrand (hH : PassHyp w ζ y U) {t : ℝ≥0} (ha : Alive w ζ U t) :
    IntervalIntegrable (fun r : ℝ => 2 / (pflow U r.toNNReal - w r.toNNReal)) volume 0 t :=
  (hH.continuousOn_integrand ha).intervalIntegrable_of_Icc t.coe_nonneg

/-- The flow is nondecreasing on the life. -/
theorem PassHyp.pflow_le_of_le (hH : PassHyp w ζ y U) {s t : ℝ≥0} (ha : Alive w ζ U t) (hst : s ≤ t) :
    pflow U s ≤ pflow U t := by
  have hs := alive_anti ha hst
  rw [hH.pflow_eq_integral ha, hH.pflow_eq_integral hs]
  have hI := hH.intervalIntegrable_integrand ha
  have hIs : IntervalIntegrable (fun r : ℝ => 2 / (pflow U r.toNNReal - w r.toNNReal)) volume 0 s :=
    hI.mono_set (by rw [uIcc_of_le s.coe_nonneg, uIcc_of_le t.coe_nonneg]; exact Icc_subset_Icc le_rfl hst)
  have hIst : IntervalIntegrable (fun r : ℝ => 2 / (pflow U r.toNNReal - w r.toNNReal)) volume s t :=
    hI.mono_set (by
      rw [uIcc_of_le (show (s : ℝ) ≤ t from hst), uIcc_of_le t.coe_nonneg]
      exact Icc_subset_Icc s.coe_nonneg le_rfl)
  rw [← intervalIntegral.integral_add_adjacent_intervals hIs hIst]
  have : 0 ≤ ∫ r in (s : ℝ)..t, 2 / (pflow U r.toNNReal - w r.toNNReal) := by
    refine intervalIntegral.integral_nonneg (by exact_mod_cast hst) fun r hr => ?_
    have hr' : r.toNNReal ≤ t := Real.toNNReal_le_iff_le_coe.2 hr.2
    exact div_nonneg zero_le_two (sub_nonneg.2 (hH.w_lt_pflow (alive_anti ha hr')).le)
  linarith

/-! ### At a finite end of the life -/

/-- **Bounded below gap forces life.** If `y` is alive before `τ < ζ` (`0 < τ`) with gap `≥ c > 0`, it is alive at
`τ`. -/
theorem PassHyp.alive_of_gap_ge (hH : PassHyp w ζ y U) {τ : ℝ≥0} (hτ0 : 0 < τ) (hτζ : (τ : ℝ≥0∞) < ζ)
    (hlife : ∀ s < τ, Alive w ζ U s) {c : ℝ} (hc : 0 < c) (hgap : ∀ s < τ, c ≤ pflow U s - w s) :
    Alive w ζ U τ := by
  obtain ⟨n, hn⟩ := exists_two_mul_passDelta_le hc
  have hagree : ∀ s < τ, U n s = pflow U s := by
    intro s hs
    have hsζ : (s : ℝ≥0∞) < ζ := lt_of_le_of_lt (ENNReal.coe_le_coe.2 hs.le) hτζ
    have hcont : ContinuousOn (pflow U) (Icc 0 s) := fun r hr =>
      (hH.continuousAt_pflow (hlife r (lt_of_le_of_lt hr.2 hs))).continuousWithinAt
    exact hH.eq_of_solves n hsζ hcont (fun r hr => hH.pflow_eq_integral (hlife r (lt_of_le_of_lt hr hs)))
      (fun r hr => by linarith [hgap r (lt_of_le_of_lt hr hs), passDelta_pos n]) s le_rfl
  refine ⟨n, hτζ, fun s hs => ?_⟩
  rcases hs.lt_or_eq with hs | hs
  · rw [hagree s hs]; linarith [hgap s hs]
  · -- the value at `τ` is the limit from the left
    rw [hs]
    have hopen : IsOpen {s : ℝ≥0 | (s : ℝ≥0∞) < ζ} := isOpen_lt ENNReal.continuous_coe continuous_const
    have hc' : ContinuousAt (fun s => U n s - w s) τ :=
      ((hH.cont_U n).sub hH.cont_w).continuousAt (hopen.mem_nhds hτζ)
    have hlim : Tendsto (fun s => U n s - w s) (𝓝[<] τ) (𝓝 (U n τ - w τ)) := hc'.tendsto.mono_left nhdsWithin_le_nhds
    have : (𝓝[<] τ).NeBot := nhdsLT_neBot_of_exists_lt ⟨0, hτ0⟩
    refine ge_of_tendsto hlim ?_
    filter_upwards [self_mem_nhdsWithin] with s hs'
    rw [hagree s hs']
    linarith [hgap s hs']

/-- **At a finite end `τ < ζ` the flow of `y` tends to `w(τ)`.** -/
theorem PassHyp.tendsto_pflow_passEnd (hH : PassHyp w ζ y U) {τ : ℝ≥0} (hτ : passEnd w ζ U = τ)
    (hτζ : (τ : ℝ≥0∞) < ζ) : Tendsto (pflow U) (𝓝[<] τ) (𝓝 (w τ)) := by
  have hlife : ∀ s < τ, Alive w ζ U s := fun s hs => hH.lt_passEnd_iff.1 (by rw [hτ]; exact_mod_cast hs)
  have hdead : ¬ Alive w ζ U τ := fun h => lt_irrefl _ (hτ ▸ hH.lt_passEnd_iff.2 h)
  have hτ0 : 0 < τ := by
    refine pos_iff_ne_zero.2 fun h0 => hdead ?_
    rw [h0]; exact hH.alive_zero (lt_of_le_of_lt zero_le (h0 ▸ hτζ))
  have hopen : IsOpen {s : ℝ≥0 | (s : ℝ≥0∞) < ζ} := isOpen_lt ENNReal.continuous_coe continuous_const
  have hwτ : ContinuousAt w τ := hH.cont_w.continuousAt (hopen.mem_nhds hτζ)
  -- the gap is small at times arbitrarily close to `τ`
  have hsmall : ∀ c > 0, ∀ r < τ, ∃ s, r ≤ s ∧ s < τ ∧ pflow U s - w s < c := by
    intro c hc r hr
    by_contra hne
    push Not at hne
    obtain ⟨s₀, hs₀, hmin⟩ := (isCompact_Icc (a := (0 : ℝ≥0)) (b := r)).exists_isMinOn
      ⟨0, zero_le, zero_le⟩ (fun s hs => ((hH.continuousAt_pflow (hlife s (lt_of_le_of_lt hs.2 hr))).sub
        (hH.cont_w.continuousAt (hopen.mem_nhds (lt_of_le_of_lt (ENNReal.coe_le_coe.2
          (hs.2.trans hr.le)) hτζ)))).continuousWithinAt)
    have hm0 : 0 < pflow U s₀ - w s₀ := sub_pos.2 (hH.w_lt_pflow (hlife s₀ (lt_of_le_of_lt hs₀.2 hr)))
    refine hdead (hH.alive_of_gap_ge hτ0 hτζ hlife (lt_min hc hm0) fun s hs => ?_)
    rcases le_or_gt s r with hsr | hsr
    · exact (min_le_right _ _).trans (hmin ⟨zero_le, hsr⟩)
    · exact (min_le_left _ _).trans (hne s hsr.le hs)
  refine tendsto_order.2 ⟨fun a ha => ?_, fun b hb => ?_⟩
  · have hev : ∀ᶠ s in 𝓝[<] τ, a < w s :=
      (hwτ.tendsto.mono_left nhdsWithin_le_nhds).eventually (lt_mem_nhds ha)
    filter_upwards [hev, self_mem_nhdsWithin] with s hs hsτ
    exact hs.trans (hH.w_lt_pflow (hlife s hsτ))
  · set c := (b - w τ) / 2 with hcdef
    have hc : 0 < c := by rw [hcdef]; linarith
    have hev : ∀ᶠ s in 𝓝[<] τ, w s < w τ + c :=
      (hwτ.tendsto.mono_left nhdsWithin_le_nhds).eventually (gt_mem_nhds (by linarith))
    obtain ⟨s₁, hs₁, hsub⟩ := (mem_nhdsLT_iff_exists_Ioo_subset' hτ0).1 hev
    filter_upwards [Ioo_mem_nhdsLT hs₁] with r hr
    obtain ⟨s, hrs, hsτ, hgs⟩ := hsmall c hc r hr.2
    have h1 := hH.pflow_le_of_le (hlife s hsτ) hrs
    have h2 : w s < w τ + c := hsub ⟨lt_of_lt_of_le hr.1 hrs, hsτ⟩
    linarith

end G12

end Supp7

end InteractingSLE
