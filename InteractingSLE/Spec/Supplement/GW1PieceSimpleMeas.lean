/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW1PieceSimple
import InteractingSLE.Spec.Supplement.LPTrace

/-!
# Lemma GW1, the next ordinary piece: a measurable event for simplicity and visits

Packet PROVE-T14-GW1Z. GB6 is applied to the next ordinary piece under the regular conditional law given the
retained past (GW1, p. 619: "Apply GB6, within the independently established complete conditional pair in item 2").
To bring its conclusion back to `P`, the conclusion must be a measurable event (an almost sure statement under every
conditional law need not hold `P`-almost surely otherwise; compare ruling R51). The two pathwise facts that the
physical argument needs — the piece `α` is injective up to its stop `S`, and each `α(t)`, `t > 0`, is a point
`−1/γ(r)` of the conditional counterflow — are equivalent, for continuous paths, to conditions at rational own times:

* `SepAt A S`: for rational `b < c < S` and any rational `d`, the values of `α` at rational times `≤ b` stay at a
  positive distance from its values at rational times in `[c, d] ∩ [0, S)` (two disjoint compact images);
* `VisAt A G S`: at every rational `q ∈ (0, S)`, `α(q)` is a limit of points `−1/γ(r)`, `r` rational
  (closure of the counterflow path; `γ` transient, so the closure adds only `0`).

The values at rational times are read with the measurable trace functional `LP.traceAt` (PROVE-LP), which agrees with
the trace before the horizon. `measurableSet_pieceVisitEvent` is the measurability; `injOn_of_sepAt`,
`sepAt_of_injOn`, `visit_of_visAt`, `visAt_of_visit` are the pathwise equivalences.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology Metric
open scoped NNReal ENNReal

namespace InteractingSLE

namespace Theorem14

namespace GW1Z

/-! ### Rational own times -/

/-- The own time of a rational number (`max q 0`). -/
def rt (q : ℚ) : ℝ≥0 := (q : ℝ).toNNReal

theorem coe_rt_of_nonneg {q : ℚ} (hq : (0 : ℝ) ≤ q) : (rt q : ℝ) = q := Real.coe_toNNReal _ hq

/-- Between two own times there is a rational own time. -/
theorem exists_rt_btwn {x y : ℝ≥0} (h : x < y) : ∃ q : ℚ, x < rt q ∧ rt q < y := by
  obtain ⟨q, hxq, hqy⟩ := exists_rat_btwn (show (x : ℝ) < y from h)
  have hq0 : (0 : ℝ) ≤ q := le_trans x.coe_nonneg hxq.le
  refine ⟨q, ?_, ?_⟩
  · rw [← NNReal.coe_lt_coe, coe_rt_of_nonneg hq0]; exact hxq
  · rw [← NNReal.coe_lt_coe, coe_rt_of_nonneg hq0]; exact hqy

/-- Rational own times in `(x, y)` converging to `x`. -/
theorem exists_seq_rt_right {x y : ℝ≥0} (h : x < y) :
    ∃ q : ℕ → ℚ, (∀ n, x < rt (q n) ∧ rt (q n) < y) ∧ Tendsto (fun n => rt (q n)) atTop (𝓝 x) := by
  have hex : ∀ n : ℕ, ∃ q : ℚ, x < rt q ∧ rt q < min y (x + 1 / ((n : ℝ≥0) + 1)) := fun n =>
    exists_rt_btwn (lt_min h (lt_add_of_pos_right x (by positivity)))
  choose q hq1 hq2 using hex
  refine ⟨q, fun n => ⟨hq1 n, (hq2 n).trans_le (min_le_left _ _)⟩, ?_⟩
  have hup : Tendsto (fun n : ℕ => x + 1 / ((n : ℝ≥0) + 1)) atTop (𝓝 x) := by
    have h0 : Tendsto (fun n : ℕ => 1 / ((n : ℝ≥0) + 1)) atTop (𝓝 0) :=
      _root_.tendsto_one_div_add_atTop_nhds_zero_nat
    simpa using (tendsto_const_nhds (x := x)).add h0
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hup (fun n => (hq1 n).le)
    fun n => ((hq2 n).trans_le (min_le_right _ _)).le

/-- Rational own times in `(x, y)` converging to `y`. -/
theorem exists_seq_rt_left {x y : ℝ≥0} (h : x < y) :
    ∃ q : ℕ → ℚ, (∀ n, x < rt (q n) ∧ rt (q n) < y) ∧ Tendsto (fun n => rt (q n)) atTop (𝓝 y) := by
  have hy0 : 0 < y := lt_of_le_of_lt zero_le h
  have hex : ∀ n : ℕ, ∃ q : ℚ, max x (y - 1 / ((n : ℝ≥0) + 1)) < rt q ∧ rt q < y := fun n =>
    exists_rt_btwn (max_lt h (tsub_lt_self hy0 (by positivity)))
  choose q hq1 hq2 using hex
  refine ⟨q, fun n => ⟨(le_max_left _ _).trans_lt (hq1 n), hq2 n⟩, ?_⟩
  have hlow : Tendsto (fun n : ℕ => y - 1 / ((n : ℝ≥0) + 1)) atTop (𝓝 y) := by
    have h0 : Tendsto (fun n : ℕ => 1 / ((n : ℝ≥0) + 1)) atTop (𝓝 0) :=
      _root_.tendsto_one_div_add_atTop_nhds_zero_nat
    simpa using (tendsto_const_nhds (x := y)).sub h0
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le hlow tendsto_const_nhds
    (fun n => ((le_max_right _ _).trans_lt (hq1 n)).le) fun n => (hq2 n).le

/-! ### The two countable conditions -/

/-- **Separation at rational times**: for rational `b < c` with `c < S` and any rational `d`, the values at rational
times `≤ b` keep a positive distance from those at rational times in `[c, d]` before `S`. -/
def SepAt (A : ℝ≥0 → ℂ) (S : ℝ≥0∞) : Prop :=
  ∀ b c d : ℚ, rt b < rt c → (rt c : ℝ≥0∞) < S → ∃ n : ℕ, ∀ u v : ℚ, rt u ≤ rt b → rt c ≤ rt v → rt v ≤ rt d →
    (rt v : ℝ≥0∞) < S → 1 / ((n : ℝ) + 1) ≤ ‖A (rt u) - A (rt v)‖

/-- **Visits at rational times**: at every rational `q ∈ (0, S)`, the value `A(q)` is a limit of the points
`−1/G(r)`, `r` rational. -/
def VisAt (A G : ℝ≥0 → ℂ) (S : ℝ≥0∞) : Prop :=
  ∀ q : ℚ, 0 < rt q → (rt q : ℝ≥0∞) < S → ∀ n : ℕ, ∃ r : ℚ, G (rt r) ≠ 0 ∧
    ‖A (rt q) + (G (rt r))⁻¹‖ < 1 / ((n : ℝ) + 1)

section Meas

variable {Ω : Type*} [MeasurableSpace Ω]

theorem measurable_sepAt {A : ℝ≥0 → Ω → ℂ} (hA : ∀ t, Measurable (A t)) {S : Ω → ℝ≥0∞}
    (hS : Measurable S) : Measurable fun ω => SepAt (fun t => A t ω) (S ω) := by
  unfold SepAt
  refine Measurable.forall fun b => Measurable.forall fun c => Measurable.forall fun d => ?_
  refine Measurable.imp measurable_const (Measurable.imp ?_ (Measurable.exists fun n => ?_))
  · exact measurableSet_setOfPred.1 (measurableSet_lt measurable_const hS)
  refine Measurable.forall fun u => Measurable.forall fun v => ?_
  refine Measurable.imp measurable_const (Measurable.imp measurable_const (Measurable.imp measurable_const
    (Measurable.imp ?_ ?_)))
  · exact measurableSet_setOfPred.1 (measurableSet_lt measurable_const hS)
  · exact measurableSet_setOfPred.1 (measurableSet_le measurable_const ((hA _).sub (hA _)).norm)

theorem measurable_visAt {A G : ℝ≥0 → Ω → ℂ} (hA : ∀ t, Measurable (A t)) (hG : ∀ t, Measurable (G t))
    {S : Ω → ℝ≥0∞} (hS : Measurable S) :
    Measurable fun ω => VisAt (fun t => A t ω) (fun t => G t ω) (S ω) := by
  unfold VisAt
  refine Measurable.forall fun q => Measurable.imp measurable_const (Measurable.imp ?_
    (Measurable.forall fun n => Measurable.exists fun r => Measurable.and ?_ ?_))
  · exact measurableSet_setOfPred.1 (measurableSet_lt measurable_const hS)
  · exact (measurableSet_setOfPred.1 (measurableSet_eq_fun (hG _) measurable_const)).not
  · exact measurableSet_setOfPred.1 (measurableSet_lt ((hA _).add (hG _).inv).norm measurable_const)

end Meas

/-! ### Separation and injectivity -/

/-- **Separation gives injectivity**: a path continuous up to `S` whose rational values before `S` are `A` is
injective on `[0, S]` if `A` satisfies `SepAt`. -/
theorem injOn_of_sepAt {α A : ℝ≥0 → ℂ} {S : ℝ≥0∞} (hα : ContinuousOn α {t | (t : ℝ≥0∞) ≤ S})
    (hA : ∀ q : ℚ, (rt q : ℝ≥0∞) < S → A (rt q) = α (rt q)) (hsep : SepAt A S) :
    InjOn α {t | (t : ℝ≥0∞) ≤ S} := by
  have key : ∀ t t' : ℝ≥0, (t : ℝ≥0∞) ≤ S → (t' : ℝ≥0∞) ≤ S → t < t' → α t ≠ α t' := by
    intro t t' ht ht' hlt heq
    obtain ⟨b, htb, hbt'⟩ := exists_rt_btwn hlt
    obtain ⟨c, hbc, hct'⟩ := exists_rt_btwn hbt'
    obtain ⟨d, hd, -⟩ := exists_rt_btwn (lt_add_one t')
    have hcS : (rt c : ℝ≥0∞) < S := lt_of_lt_of_le (ENNReal.coe_lt_coe.2 hct') ht'
    obtain ⟨n, hn⟩ := hsep b c d hbc hcS
    obtain ⟨u, hu, hu_tend⟩ := exists_seq_rt_right htb
    obtain ⟨v, hv, hv_tend⟩ := exists_seq_rt_left hct'
    have hvS : ∀ m, (rt (v m) : ℝ≥0∞) < S := fun m => lt_of_lt_of_le (ENNReal.coe_lt_coe.2 (hv m).2) ht'
    have huS : ∀ m, (rt (u m) : ℝ≥0∞) < S := fun m =>
      lt_of_lt_of_le (ENNReal.coe_lt_coe.2 ((hu m).2.trans (hbc.trans hct'))) ht'
    have hbound : ∀ m, 1 / ((n : ℝ) + 1) ≤ ‖α (rt (u m)) - α (rt (v m))‖ := by
      intro m
      have h := hn (u m) (v m) (hu m).2.le (hv m).1.le ((hv m).2.trans hd).le (hvS m)
      rwa [hA _ (huS m), hA _ (hvS m)] at h
    have hlimu : Tendsto (fun m => α (rt (u m))) atTop (𝓝 (α t)) :=
      (hα t ht).tendsto.comp (tendsto_nhdsWithin_iff.2 ⟨hu_tend, Eventually.of_forall fun m =>
        show (rt (u m) : ℝ≥0∞) ≤ S from (huS m).le⟩)
    have hlimv : Tendsto (fun m => α (rt (v m))) atTop (𝓝 (α t')) :=
      (hα t' ht').tendsto.comp (tendsto_nhdsWithin_iff.2 ⟨hv_tend, Eventually.of_forall fun m =>
        show (rt (v m) : ℝ≥0∞) ≤ S from (hvS m).le⟩)
    have hlim := (hlimu.sub hlimv).norm
    have hge := ge_of_tendsto' hlim hbound
    rw [heq, sub_self, norm_zero] at hge
    have hpos : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
    linarith
  intro t ht t' ht' heq
  by_contra hne
  rcases lt_or_gt_of_ne hne with h | h
  · exact key t t' ht ht' h heq
  · exact key t' t ht' ht h heq.symm

/-- **Injectivity gives separation** (two disjoint compact images are at a positive distance). -/
theorem sepAt_of_injOn {α A : ℝ≥0 → ℂ} {S : ℝ≥0∞} (hα : ContinuousOn α {t | (t : ℝ≥0∞) ≤ S})
    (hA : ∀ q : ℚ, (rt q : ℝ≥0∞) < S → A (rt q) = α (rt q)) (hinj : InjOn α {t | (t : ℝ≥0∞) ≤ S}) :
    SepAt A S := by
  intro b c d hbc hcS
  set D₂ : Set ℝ≥0 := Icc (rt c) (rt d) ∩ {v | (v : ℝ≥0∞) ≤ S} with hD₂
  have hD₂c : IsCompact D₂ := isCompact_Icc.inter_right (isClosed_le ENNReal.continuous_coe continuous_const)
  have hbS : (rt b : ℝ≥0∞) ≤ S := (lt_trans (ENNReal.coe_lt_coe.2 hbc) hcS).le
  have hK₁ : IsCompact (α '' Icc 0 (rt b)) := isCompact_Icc.image_of_continuousOn
    (hα.mono fun t ht => show (t : ℝ≥0∞) ≤ S from le_trans (ENNReal.coe_le_coe.2 ht.2) hbS)
  have hK₂ : IsCompact (α '' D₂) := hD₂c.image_of_continuousOn (hα.mono fun t ht => ht.2)
  rcases (α '' D₂).eq_empty_or_nonempty with h2 | h2
  · refine ⟨0, fun u v _ hcv hvd hvS => ?_⟩
    have hmem := mem_image_of_mem α (show rt v ∈ D₂ from ⟨⟨hcv, hvd⟩, hvS.le⟩)
    rw [h2] at hmem
    exact hmem.elim
  · have hpos : ∀ x ∈ α '' Icc 0 (rt b), 0 < infDist x (α '' D₂) := by
      rintro _ ⟨u, hu, rfl⟩
      refine (hK₂.isClosed.notMem_iff_infDist_pos h2).1 ?_
      rintro ⟨v, hv, hvu⟩
      have hu' : (u : ℝ≥0∞) ≤ S := le_trans (ENNReal.coe_le_coe.2 hu.2) hbS
      have huv : u < v := lt_of_le_of_lt hu.2 (lt_of_lt_of_le hbc hv.1.1)
      exact huv.ne' (hinj hv.2 hu' hvu)
    obtain ⟨x₀, hx₀, hmin⟩ := hK₁.exists_isMinOn ⟨α 0, 0, ⟨le_rfl, zero_le⟩, rfl⟩
      (continuous_infDist_pt _).continuousOn
    obtain ⟨n, hn⟩ := exists_nat_one_div_lt (hpos x₀ hx₀)
    refine ⟨n, fun u v hu hcv hvd hvS => ?_⟩
    have huS : (rt u : ℝ≥0∞) < S := lt_of_le_of_lt (ENNReal.coe_le_coe.2 (hu.trans hbc.le)) hcS
    rw [hA u huS, hA v hvS, ← dist_eq_norm]
    calc 1 / ((n : ℝ) + 1) ≤ infDist x₀ (α '' D₂) := hn.le
      _ ≤ infDist (α (rt u)) (α '' D₂) := isMinOn_iff.1 hmin _ (mem_image_of_mem α ⟨zero_le, hu⟩)
      _ ≤ dist (α (rt u)) (α (rt v)) := infDist_le_dist_of_mem (mem_image_of_mem α ⟨⟨hcv, hvd⟩, hvS.le⟩)

/-! ### Visits -/

/-- **Visits give the rational condition.** -/
theorem visAt_of_visit {α A G γ : ℝ≥0 → ℂ} {S : ℝ≥0∞} (hγ : Continuous γ)
    (hA : ∀ q : ℚ, (rt q : ℝ≥0∞) < S → A (rt q) = α (rt q)) (hG : ∀ r : ℚ, G (rt r) = γ (rt r))
    (hvis : ∀ t : ℝ≥0, 0 < t → (t : ℝ≥0∞) ≤ S → ∃ r, γ r ≠ 0 ∧ α t = -(γ r)⁻¹) : VisAt A G S := by
  intro q hq0 hqS n
  obtain ⟨r₀, hr₀, hq⟩ := hvis (rt q) hq0 hqS.le
  have hc : ContinuousAt (fun r => (γ r)⁻¹) r₀ := hγ.continuousAt.inv₀ hr₀
  have hn : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
  have hev : ∀ᶠ r in 𝓝 r₀, γ r ≠ 0 ∧ ‖(γ r)⁻¹ - (γ r₀)⁻¹‖ < 1 / ((n : ℝ) + 1) := by
    refine (hγ.continuousAt.eventually_ne hr₀).and ?_
    filter_upwards [Metric.tendsto_nhds.1 hc _ hn] with r hr
    rwa [dist_eq_norm] at hr
  obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff.1 hev
  obtain ⟨r, h1, h2⟩ := exists_rt_btwn (show r₀ < r₀ + ⟨ε / 2, by positivity⟩ from
    lt_add_of_pos_right r₀ (by show (0 : ℝ) < ε / 2; positivity))
  have hd : dist (rt r) r₀ < ε := by
    rw [NNReal.dist_eq]
    have e1 : (r₀ : ℝ) < rt r := by exact_mod_cast h1
    have e2 : (rt r : ℝ) < r₀ + ε / 2 := by exact_mod_cast h2
    rw [abs_of_pos (by linarith)]
    linarith
  obtain ⟨hne, hlt⟩ := hball hd
  refine ⟨r, by rw [hG]; exact hne, ?_⟩
  rw [hA q hqS, hG, hq, neg_add_eq_sub]
  exact hlt

/-- **The rational condition gives visits**, for a transient continuous counterflow trace `γ` and an injective path
`α` with `α(0) = 0`: the closure of the counterflow points `−1/γ(r)` adds only `0`. -/
theorem visit_of_visAt {α A G γ : ℝ≥0 → ℂ} {S : ℝ≥0∞} (hα : ContinuousOn α {t | (t : ℝ≥0∞) ≤ S})
    (hα0 : α 0 = 0) (hinj : InjOn α {t | (t : ℝ≥0∞) ≤ S}) (hγ : Continuous γ)
    (hγtr : Tendsto (fun r => ‖γ r‖) atTop atTop)
    (hA : ∀ q : ℚ, (rt q : ℝ≥0∞) < S → A (rt q) = α (rt q)) (hG : ∀ r : ℚ, G (rt r) = γ (rt r))
    (hv : VisAt A G S) : ∀ t : ℝ≥0, 0 < t → (t : ℝ≥0∞) ≤ S → ∃ r, γ r ≠ 0 ∧ α t = -(γ r)⁻¹ := by
  set R : Set ℂ := {z | ∃ r, γ r ≠ 0 ∧ z = -(γ r)⁻¹} with hRdef
  have hcl : ∀ z ∈ closure R, z ≠ 0 → z ∈ R := by
    intro z hz hz0
    obtain ⟨x, hxR, hx⟩ := mem_closure_iff_seq_limit.1 hz
    choose r hr hxr using hxR
    have hγlim : Tendsto (fun n => γ (r n)) atTop (𝓝 (-z⁻¹)) := by
      have e : ∀ n, γ (r n) = -(x n)⁻¹ := fun n => by rw [hxr n, inv_neg, inv_inv, neg_neg]
      simp_rw [e]
      exact (hx.inv₀ hz0).neg
    obtain ⟨M, hM⟩ := hγlim.norm.bddAbove_range
    obtain ⟨N, hN⟩ := eventually_atTop.1 (hγtr.eventually_gt_atTop M)
    have hrN : ∀ n, r n ∈ Icc 0 N := fun n => ⟨zero_le, not_lt.1 fun h =>
      (hM ⟨n, rfl⟩).not_gt (hN (r n) h.le)⟩
    obtain ⟨a, -, φ, hφ, hφt⟩ := isCompact_Icc.tendsto_subseq hrN
    have h1 : Tendsto (fun n => γ (r (φ n))) atTop (𝓝 (γ a)) := (hγ.tendsto a).comp hφt
    have h2 : Tendsto (fun n => γ (r (φ n))) atTop (𝓝 (-z⁻¹)) := hγlim.comp hφ.tendsto_atTop
    have ha := tendsto_nhds_unique h1 h2
    have hane : γ a ≠ 0 := by rw [ha]; exact neg_ne_zero.2 (inv_ne_zero hz0)
    exact ⟨a, hane, by rw [ha, inv_neg, inv_inv, neg_neg]⟩
  have hrat : ∀ q : ℚ, 0 < rt q → (rt q : ℝ≥0∞) < S → α (rt q) ∈ closure R := by
    intro q hq0 hqS
    rw [Metric.mem_closure_iff]
    intro ε hε
    obtain ⟨n, hn⟩ := exists_nat_one_div_lt hε
    obtain ⟨r, hr, hlt⟩ := hv q hq0 hqS n
    refine ⟨-(γ (rt r))⁻¹, ⟨rt r, by rwa [← hG], rfl⟩, ?_⟩
    rw [dist_eq_norm, sub_neg_eq_add, ← hA q hqS, ← hG]
    exact hlt.trans hn
  intro t ht0 ht
  obtain ⟨q, hq, hq_tend⟩ := exists_seq_rt_left ht0
  have hqS : ∀ m, (rt (q m) : ℝ≥0∞) < S := fun m => lt_of_lt_of_le (ENNReal.coe_lt_coe.2 (hq m).2) ht
  have hmem : α t ∈ closure R :=
    isClosed_closure.mem_of_tendsto ((hα t ht).tendsto.comp (tendsto_nhdsWithin_iff.2 ⟨hq_tend,
      Eventually.of_forall fun m => show (rt (q m) : ℝ≥0∞) ≤ S from (hqS m).le⟩))
      (Eventually.of_forall fun m => hrat (q m) (hq m).1 (hqS m))
  have hne : α t ≠ 0 := fun h =>
    ht0.ne' (hinj ht (show ((0 : ℝ≥0) : ℝ≥0∞) ≤ S from zero_le) (h.trans hα0.symm))
  obtain ⟨r, hr, hz⟩ := hcl _ hmem hne
  exact ⟨r, hr, hz⟩

/-! ### The measurable piece event -/

section Event

variable {Ω : Type*} [MeasurableSpace Ω]

/-- **The measurable piece event**: separation and visits at rational own times, read from the measurable trace values
`LP.traceAt` of the piece's driver `e` (up to the stop `S`) and of the conditional counterflow's driver `Wk`. -/
def PieceVisitEvent (e : Ω → (ℝ≥0 → ℝ) × ℝ≥0∞) (S : Ω → ℝ≥0∞) (Wk : ℝ≥0 → Ω → ℝ) : Set Ω :=
  {ω | SepAt (fun t => LP.traceAt t (e ω).1) (S ω) ∧
    VisAt (fun t => LP.traceAt t (e ω).1) (fun t => LP.traceAt t fun s => Wk s ω) (S ω)}

theorem measurableSet_pieceVisitEvent {e : Ω → (ℝ≥0 → ℝ) × ℝ≥0∞} (he : Measurable e) {S : Ω → ℝ≥0∞}
    (hS : Measurable S) {Wk : ℝ≥0 → Ω → ℝ} (hWk : ∀ t, Measurable (Wk t)) :
    MeasurableSet (PieceVisitEvent e S Wk) := by
  have hA : ∀ t, Measurable fun ω => LP.traceAt t (e ω).1 := fun t =>
    (LP.measurable_traceAt t).comp (measurable_fst.comp he)
  have hG : ∀ t, Measurable fun ω => LP.traceAt t fun s => Wk s ω := fun t =>
    (LP.measurable_traceAt t).comp (measurable_pi_iff.2 hWk)
  exact measurableSet_setOfPred.2 ((measurable_sepAt hA hS).and (measurable_visAt hA hG hS))

end Event

end GW1Z

end Theorem14

end InteractingSLE
