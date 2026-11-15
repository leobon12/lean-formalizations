/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec5.Prop51HGateSign
import InteractingSLE.Foundations.Topology.ThetaCurve
import InteractingSLE.Foundations.Topology.JaniszewskiHalfPlane

/-!
# Western chart crosscuts at a free positive gate: winding values, unbounded domains, Janiszewski

Packet PROVE-PROP51-TGT (ruling R71; Astra's follow-up 4, §1.7 L377–L463: "two points … can be separated by its union
only if some one crosscut separates them", "the orientation forces an eastern endpoint"). Planar facts about the
completed chart crosscuts `Prop51HGate.ExcursionChartCut` of the excursions of a proper flow arc `η` in
`D = ℍ ∖ R(K_s)`, at a free positive gate `x₀` (a ball about `x₀` missing the closure of the chart flow set):

* `nonempty_excursionChartCut_of_west`: a bounded excursion with a negative finishing limit completes to a chart
  crosscut (no global western-end hypothesis);
* `im_eq_zero_of_mem_cut_inter`: the completed crosscuts of two different excursions meet only on `ℝ`;
* `windNum_loop_eq_one_of_gate`: if `finish < x₀ < start`, the loop winds once about the gate half-ball;
* **`windNum_loop_eq_zero_or_one`**: then (Jordan curve theorem for the loop `cut ∪ [finish, start]`) the loop winds
  `0` or `1` about every chart point off the chart flow set;
* **`mem_H_diff_fillH_of_gate`**: if both ends are left of the gate, the gate half-ball lies in the unbounded domain of
  the completed crosscut (joined to `∞` through the real ray `[x₀, ∞)`);
* **`mem_H_diff_fillH_union`**: Janiszewski's theorem in `ℍ` for finitely many compact sets meeting only on `ℝ`.

Deterministic; nothing here replaces a source theorem.
-/

set_option autoImplicit false

noncomputable section

open Complex Set Metric Filter Topology Bornology
open QuantumZipper (H Hbar fwdHull fwdMap fwdMapInv)

namespace InteractingSLE.Sec5.Prop51Tgt

open WangWu hiding ratPt exists_ratPt_dist_lt
open Prop51G Prop51HTopo Prop51HGate
open _root_.InteractingSLE.Orientation
open HalfPlaneSep

variable {η β : ℝ → ℂ} {w : ℝ → ℝ} {s : ℝ}

/-! ### A chart crosscut for one western excursion -/

/-- **A bounded excursion with a negative finishing limit completes to a chart crosscut** (the bounded branch of
`Prop51HGate.nonempty_excursionChartCut`, with the finishing limit supplied for this excursion only). -/
theorem nonempty_excursionChartCut_of_west (hη : IsProperArc η) (hβ : IsLoewnerTrace w β) (hw : Continuous w)
    (hw0 : w 0 = 0) (hs : 0 ≤ s) (htip : negInv (β s) ∉ arcRange η) {u : ℝ}
    (e : BoundedExcursionInterval η w s u) {xf : ℝ} (hxf : xf < 0)
    (hlimf : Tendsto (fun t => revChart w s (η t)) (𝓝[<] e.finish) (𝓝 (xf : ℂ))) :
    Nonempty (ExcursionChartCut η w s (connectedComponentIn (excursionTimes η w s) u)) := by
  have hsub : connectedComponentIn (excursionTimes η w s) u ⊆ excursionTimes η w s :=
    connectedComponentIn_subset _ _
  set a := e.start
  set b := e.finish
  have hab : a < b := e.start_lt.trans e.lt_finish
  have hba : 0 < b - a := sub_pos.2 hab
  have hD := e.mapsTo
  obtain ⟨xs, hxs⟩ := exists_tendsto_revChart_start hη hβ hw hw0 hs htip e.start_nonneg hab hD
    e.start_outside
  have htime0 : Tendsto (fun t : ℝ => a + t * (b - a)) (𝓝[>] 0) (𝓝[>] a) := by
    refine tendsto_nhdsWithin_iff.2 ⟨?_, ?_⟩
    · have h : Tendsto (fun t : ℝ => a + t * (b - a)) (𝓝 0) (𝓝 (a + 0 * (b - a))) :=
        (continuous_const.add (continuous_id.mul continuous_const)).tendsto 0
      rw [zero_mul, add_zero] at h
      exact h.mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with t ht
      change a < a + t * (b - a)
      nlinarith [mem_Ioi.1 ht]
  have htime1 : Tendsto (fun t : ℝ => a + t * (b - a)) (𝓝[<] 1) (𝓝[<] b) := by
    refine tendsto_nhdsWithin_iff.2 ⟨?_, ?_⟩
    · have h : Tendsto (fun t : ℝ => a + t * (b - a)) (𝓝 1) (𝓝 (a + 1 * (b - a))) :=
        (continuous_const.add (continuous_id.mul continuous_const)).tendsto 1
      rw [one_mul, add_sub_cancel] at h
      exact h.mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with t ht
      change a + t * (b - a) < b
      nlinarith [mem_Iio.1 ht]
  refine ExcursionChartCut.nonempty_of_limits hη hw hs hsub (fun t => a + t * (b - a))
    (by fun_prop) (fun t _ t' _ htt => by nlinarith) (fun t ht => ?_) (fun y hy => ?_)
    (hxs.comp htime0) (hlimf.comp htime1) hxf
  · rw [e.component_eq]
    exact ⟨by nlinarith [ht.1], by nlinarith [ht.2]⟩
  · rw [e.component_eq] at hy
    refine ⟨(y - a) / (b - a), ⟨div_pos (by linarith [hy.1]) hba, (div_lt_one hba).2 (by linarith [hy.2])⟩,
      ?_⟩
    field_simp
    ring

/-! ### The completed crosscut -/

section Cut

variable {C : Set ℝ}

/-- The completed crosscut lies in the closed upper half-plane. -/
theorem cut_im_nonneg (κ : ExcursionChartCut η w s C) (hw : Continuous w) (hs : 0 ≤ s) {t : ℝ}
    (ht : t ∈ Icc (0 : ℝ) 1) : 0 ≤ (κ.cut t).im := by
  rcases eq_endpoints_or_mem_Ioo_of_mem_Icc ht with rfl | rfl | ht'
  · rw [κ.cut_zero]; simp
  · rw [κ.cut_one]; simp
  · exact (show (0 : ℝ) < (κ.cut t).im from κ.cut_mem_H hw hs ht').le

/-- A point of the completed crosscut in `ℍ` is an interior point. -/
theorem mem_Ioo_of_cut_mem_H (κ : ExcursionChartCut η w s C) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1)
    (hH : κ.cut t ∈ H) : t ∈ Ioo (0 : ℝ) 1 := by
  rcases eq_endpoints_or_mem_Ioo_of_mem_Icc ht with rfl | rfl | ht'
  · rw [κ.cut_zero] at hH; exact (ofReal_notMem_H _ hH).elim
  · rw [κ.cut_one] at hH; exact (ofReal_notMem_H _ hH).elim
  · exact ht'

/-- A real point of the completed crosscut is one of its two ends. -/
theorem cut_eq_start_or_finish (κ : ExcursionChartCut η w s C) (hw : Continuous w) (hs : 0 ≤ s) {t : ℝ}
    (ht : t ∈ Icc (0 : ℝ) 1) (hH : κ.cut t ∉ H) :
    κ.cut t = (κ.start : ℂ) ∨ κ.cut t = (κ.finish : ℂ) := by
  rcases eq_endpoints_or_mem_Ioo_of_mem_Icc ht with rfl | rfl | ht'
  · exact Or.inl κ.cut_zero
  · exact Or.inr κ.cut_one
  · exact (hH (κ.cut_mem_H hw hs ht')).elim

/-- A point of `ℍ` on the completed crosscut is in the chart flow set. -/
theorem mem_chartFlowSet_of_mem_cut (κ : ExcursionChartCut η w s C) {z : ℂ} (hz : z ∈ κ.cut '' Icc 0 1)
    (hzH : z ∈ H) : z ∈ chartFlowSet η w s := by
  obtain ⟨t, ht, rfl⟩ := hz
  exact κ.cut_mem_chartFlowSet (mem_Ioo_of_cut_mem_H κ ht hzH)

/-- **The completed crosscuts of two different excursions meet only on `ℝ`.** -/
theorem im_eq_zero_of_mem_cut_inter (hη : IsProperArc η) (hw : Continuous w) (hw0 : w 0 = 0) (hs : 0 ≤ s)
    {C' : Set ℝ} (κ : ExcursionChartCut η w s C) (κ' : ExcursionChartCut η w s C')
    (hC : ∃ u ∈ excursionTimes η w s, C = connectedComponentIn (excursionTimes η w s) u)
    (hC' : ∃ u ∈ excursionTimes η w s, C' = connectedComponentIn (excursionTimes η w s) u) (hne : C ≠ C')
    {z : ℂ} (hz : z ∈ κ.cut '' Icc 0 1) (hz' : z ∈ κ'.cut '' Icc 0 1) : z.im = 0 := by
  obtain ⟨t, ht, rfl⟩ := hz
  obtain ⟨t', ht', he⟩ := hz'
  by_cases hH : κ.cut t ∈ H
  · exfalso
    have h1 := mem_Ioo_of_cut_mem_H κ ht hH
    have h2 := mem_Ioo_of_cut_mem_H κ' ht' (he ▸ hH)
    have h3 : revChart w s (η (κ'.time t')) = revChart w s (η (κ.time t)) := by
      rw [← κ.cut_eq t h1, ← κ'.cut_eq t' h2, he]
    have h4 := injOn_revChart hw hw0 hs (κ'.eta_time_mem h2) (κ.eta_time_mem h1) h3
    have h5 := hη.inj (κ'.time_pos h2).le (κ.time_pos h1).le h4
    obtain ⟨u, -, rfl⟩ := hC
    obtain ⟨u', -, rfl⟩ := hC'
    apply hne
    have hv : κ.time t ∈ connectedComponentIn (excursionTimes η w s) u := κ.time_mem h1
    have hv' : κ.time t ∈ connectedComponentIn (excursionTimes η w s) u' := h5 ▸ κ'.time_mem h2
    rw [connectedComponentIn_eq hv, connectedComponentIn_eq hv']
  · exact le_antisymm (not_lt.1 hH) (cut_im_nonneg κ hw hs ht)

end Cut

/-! ### The loop at a gate between the two ends -/

section Gate

variable {C : Set ℝ}

/-- **The loop winds once about the gate half-ball** when the gate lies between the finishing and the starting end
(the second case of `Prop51HGate.ExcursionChartCut.windNum_loop_nonneg_of_gate`). -/
theorem windNum_loop_eq_one_of_gate (κ : ExcursionChartCut η w s C) (hw : Continuous w) (hs : 0 ≤ s)
    {x₀ r : ℝ} (hr : 0 < r) (havoid : ball (x₀ : ℂ) r ∩ closure (chartFlowSet η w s) = ∅)
    (hfx : κ.finish < x₀) (hxs : x₀ < κ.start) {z : ℂ} (hz : z ∈ ball (x₀ : ℂ) r) (hzH : z ∈ H) :
    windNum κ.loop z = 1 := by
  have hγ := κ.continuousOn_loop
  have hl := κ.loop_closed
  have hfar : ∀ v ∈ closure (chartFlowSet η w s), r ≤ ‖v - x₀‖ := fun v hv =>
    not_lt.1 fun h => (Set.eq_empty_iff_forall_notMem.1 havoid) v
      ⟨by rw [mem_ball, dist_eq_norm]; exact h, hv⟩
  have hst : r ≤ |κ.start - x₀| := by
    have := hfar _ κ.start_mem_closure
    rwa [← ofReal_sub, norm_real, Real.norm_eq_abs] at this
  have hfi : r ≤ |κ.finish - x₀| := by
    have := hfar _ κ.finish_mem_closure
    rwa [← ofReal_sub, norm_real, Real.norm_eq_abs] at this
  set S : Set ℂ := ball (x₀ : ℂ) r ∩ H with hS
  have hSc : IsPreconnected S := ((convex_ball _ _).inter
    (convex_halfSpace_gt (f := fun v : ℂ => v.im) Complex.imLm.isLinear 0)).isPreconnected
  have hSγ : Disjoint S (κ.loop '' Icc 0 1) := by
    refine Set.disjoint_left.2 fun v hv hvγ => ?_
    obtain ⟨t, ht, rfl⟩ := hvγ
    obtain ⟨u, hu, he⟩ := κ.exists_of_loop_mem_H ht hv.2
    have := hfar _ (κ.image_cut_subset_closure ⟨u, Ioo_subset_Icc_self hu, rfl⟩)
    rw [← he, ← dist_eq_norm] at this
    exact absurd (mem_ball.1 hv.1) (not_lt.2 this)
  set L : Set ℂ := {v : ℂ | v.im < 0}
  have hLc : Convex ℝ L := convex_halfSpace_lt (f := fun v : ℂ => v.im) Complex.imLm.isLinear 0
  have hLu : ¬ IsBounded L := by
    intro hb
    obtain ⟨R, hR⟩ := hb.exists_norm_le
    have h := hR (-(((|R| + 1 : ℝ) : ℂ) * I)) (by
      show (-(((|R| + 1 : ℝ) : ℂ) * I)).im < 0
      simp only [neg_im, mul_im, ofReal_re, I_im, mul_one, ofReal_im, I_re, mul_zero, add_zero]
      linarith [abs_nonneg R])
    rw [norm_neg, norm_mul, norm_I, mul_one, norm_real, Real.norm_eq_abs,
      abs_of_pos (by positivity)] at h
    linarith [le_abs_self R]
  have hLγ : Disjoint L (κ.loop '' Icc 0 1) := by
    refine Set.disjoint_left.2 fun v hv hvγ => ?_
    obtain ⟨t, ht, rfl⟩ := hvγ
    exact absurd (κ.im_loop_nonneg hw hs ht) (not_le.2 hv)
  have hsx' : x₀ + r ≤ κ.start := by
    rw [abs_of_pos (by linarith)] at hst
    linarith
  set a := κ.finish
  set b := κ.start
  have hab : 0 < b - a := by linarith
  set δ : ℝ := r / 2
  have hδ : 0 < δ := by positivity
  have hlo : a < x₀ - δ := by
    rw [abs_of_neg (by linarith)] at hfi
    dsimp only [δ]; linarith
  have hhi : x₀ + δ < b := by dsimp only [δ]; linarith
  have heval : ∀ y : ℝ, a + (2 * (1 / 2 + (y - a) / (b - a) / 2) - 1) * (b - a) = y := by
    intro y
    rw [show 2 * (1 / 2 + (y - a) / (b - a) / 2) - 1 = (y - a) / (b - a) by ring,
      div_mul_cancel₀ _ hab.ne']
    ring
  set s₀ : ℝ := 1 / 2 + (x₀ - δ - a) / (b - a) / 2 with hs₀def
  set s₁ : ℝ := 1 / 2 + (x₀ + δ - a) / (b - a) / 2 with hs₁def
  have hev₀ : a + (2 * s₀ - 1) * (b - a) = x₀ - δ := heval _
  have hev₁ : a + (2 * s₁ - 1) * (b - a) = x₀ + δ := heval _
  have hval : ∀ t, 1 / 2 ≤ t → κ.loop t = ((a + (2 * t - 1) * (b - a) : ℝ) : ℂ) :=
    fun t ht => κ.loop_of_ge ht
  have hd₀ : 0 < (x₀ - δ - a) / (b - a) := div_pos (by linarith) hab
  have hd₁ : (x₀ + δ - a) / (b - a) < 1 := (div_lt_one hab).2 (by linarith)
  have hd01 : (x₀ - δ - a) / (b - a) ≤ (x₀ + δ - a) / (b - a) :=
    div_le_div_of_nonneg_right (by linarith) hab.le
  have hs₀ : 1 / 2 ≤ s₀ := by rw [hs₀def]; linarith
  have hs₁ : s₁ ≤ 1 := by rw [hs₁def]; linarith
  have hs01 : s₀ ≤ s₁ := by rw [hs₀def, hs₁def]; linarith
  have hlow : ∀ t, s₀ ≤ t → x₀ - δ ≤ a + (2 * t - 1) * (b - a) := fun t ht => by
    have := mul_le_mul_of_nonneg_right (show 2 * s₀ - 1 ≤ 2 * t - 1 by linarith) hab.le
    linarith
  have hhigh : ∀ t, t ≤ s₁ → a + (2 * t - 1) * (b - a) ≤ x₀ + δ := fun t ht => by
    have := mul_le_mul_of_nonneg_right (show 2 * t - 1 ≤ 2 * s₁ - 1 by linarith) hab.le
    linarith
  have hrest : (x₀ : ℂ) ∉ κ.loop '' Icc 0 s₀ ∪ κ.loop '' Icc s₁ 1 := by
    rintro (⟨t, ht, he⟩ | ⟨t, ht, he⟩)
    · rcases le_or_gt t (1 / 2) with h | h
      · rw [κ.loop_of_le h] at he
        have h2 : 2 * t ∈ Icc (0 : ℝ) 1 := ⟨by linarith [ht.1], by linarith⟩
        rcases eq_endpoints_or_mem_Ioo_of_mem_Icc h2 with h0 | h1 | h2'
        · rw [h0, κ.cut_zero] at he
          have := ofReal_injective he
          linarith
        · rw [h1, κ.cut_one] at he
          have := ofReal_injective he
          linarith
        · have := κ.cut_mem_H hw hs h2'
          rw [he] at this
          exact (ofReal_notMem_H _ this).elim
      · rw [hval t h.le] at he
        have he' := ofReal_injective he
        have : a + (2 * t - 1) * (b - a) ≤ x₀ - δ := by
          have := mul_le_mul_of_nonneg_right (show 2 * t - 1 ≤ 2 * s₀ - 1 by linarith [ht.2]) hab.le
          linarith
        linarith
    · rw [hval t (hs₀.trans (hs01.trans ht.1))] at he
      have he' := ofReal_injective he
      have : x₀ + δ ≤ a + (2 * t - 1) * (b - a) := by
        have := mul_le_mul_of_nonneg_right (show 2 * s₁ - 1 ≤ 2 * t - 1 by linarith [ht.1]) hab.le
        linarith
      linarith
  obtain ⟨ε, hε, hjump⟩ := windNum_jump_real hγ hl (s₀ := s₀) (s₁ := s₁) (x := x₀) (δ := δ)
    (by linarith) hs01 hs₁ hδ
    (fun t ht => ⟨a + (2 * t - 1) * (b - a), ⟨hlow t ht.1, hhigh t ht.2⟩,
      hval t (hs₀.trans ht.1)⟩)
    (by rw [hval s₀ hs₀, hev₀])
    (by rw [hval s₁ (hs₀.trans hs01), hev₁]) hrest
  set e : ℝ := min ε r / 2
  have he0 : 0 < e := by positivity
  have heε : e < ε := by dsimp only [e]; linarith [min_le_left ε r]
  have her : e < r := by dsimp only [e]; linarith [min_le_right ε r]
  have hj := hjump e he0 heε
  have hdown : windNum κ.loop ((x₀ : ℂ) - e * I) = 0 := by
    refine windNum_eq_zero_of_isPreconnected hγ hl hLc.isPreconnected hLu hLγ ?_
    show ((x₀ : ℂ) - e * I).im < 0
    simp only [sub_im, ofReal_im, mul_im, ofReal_re, I_im, mul_one, I_re, mul_zero, add_zero,
      zero_sub]
    linarith
  have hup : (x₀ : ℂ) + e * I ∈ S := by
    refine ⟨?_, ?_⟩
    · rw [mem_ball, dist_eq_norm, add_sub_cancel_left, norm_mul, norm_I, mul_one, norm_real,
        Real.norm_eq_abs, abs_of_pos he0]
      exact her
    · show (0 : ℝ) < ((x₀ : ℂ) + e * I).im
      simp only [add_im, ofReal_im, mul_im, ofReal_re, I_im, mul_one, I_re, mul_zero, add_zero,
        zero_add]
      exact he0
  rw [windNum_eq_of_isPreconnected hγ hl hSc hSγ ⟨hz, hzH⟩ hup, hj, hdown]
  norm_num

/-- The real segment from `start` to `finish`. -/
def realArc (a b : ℝ) (t : ℝ) : ℂ := ((a + t * (b - a) : ℝ) : ℂ)

theorem isArcFrom_realArc {a b : ℝ} (hab : a ≠ b) :
    Foundations.ThetaCurve.IsArcFrom (realArc a b) (a : ℂ) (b : ℂ) := by
  refine ⟨(by unfold realArc; fun_prop : Continuous (realArc a b)).continuousOn, fun t _ t' _ he => ?_,
    by simp [realArc], by simp [realArc]⟩
  have h := ofReal_injective he
  have hba : b - a ≠ 0 := sub_ne_zero.2 hab.symm
  have : t * (b - a) = t' * (b - a) := by linarith
  exact mul_right_cancel₀ hba this

/-- The completed crosscut is injective on `[0, 1]` when its two ends differ. -/
theorem injOn_cut_Icc (κ : ExcursionChartCut η w s C) (hη : IsProperArc η) (hw : Continuous w) (hw0 : w 0 = 0)
    (hs : 0 ≤ s) (hne : κ.start ≠ κ.finish) : InjOn κ.cut (Icc 0 1) := by
  intro t ht t' ht' he
  by_cases hH : κ.cut t ∈ H
  · have h1 := mem_Ioo_of_cut_mem_H κ ht hH
    have h2 := mem_Ioo_of_cut_mem_H κ ht' (he ▸ hH)
    exact κ.injOn_cut hη hw hw0 hs h1 h2 he
  · have hH' : κ.cut t' ∉ H := he ▸ hH
    rcases eq_endpoints_or_mem_Ioo_of_mem_Icc ht with rfl | rfl | h1
    · rcases eq_endpoints_or_mem_Ioo_of_mem_Icc ht' with h0 | h0 | h2
      · exact h0.symm
      · rw [h0, κ.cut_zero, κ.cut_one] at he; exact (hne (ofReal_injective he)).elim
      · exact (hH' (κ.cut_mem_H hw hs h2)).elim
    · rcases eq_endpoints_or_mem_Ioo_of_mem_Icc ht' with h0 | h0 | h2
      · rw [h0, κ.cut_zero, κ.cut_one] at he; exact (hne (ofReal_injective he).symm).elim
      · exact h0.symm
      · exact (hH' (κ.cut_mem_H hw hs h2)).elim
    · exact (hH (κ.cut_mem_H hw hs h1)).elim

/-- **The loop winds `0` or `1` times about every chart point off the chart flow set** when the gate lies between
the finishing and the starting end: the loop is the Jordan curve `cut ∪ [finish, start]`, its winding number is `0`
outside and constant inside, and the inside contains the gate half-ball (winding number `1`). -/
theorem windNum_loop_eq_zero_or_one (κ : ExcursionChartCut η w s C) (hη : IsProperArc η) (hw : Continuous w)
    (hw0 : w 0 = 0) (hs : 0 ≤ s) {x₀ r : ℝ} (hr : 0 < r)
    (havoid : ball (x₀ : ℂ) r ∩ closure (chartFlowSet η w s) = ∅) (hfx : κ.finish < x₀) (hxs : x₀ < κ.start)
    {z : ℂ} (hzH : z ∈ H) (hzA : z ∉ chartFlowSet η w s) :
    windNum κ.loop z = 0 ∨ windNum κ.loop z = 1 := by
  have hγ := κ.continuousOn_loop
  have hl := κ.loop_closed
  have hne : κ.start ≠ κ.finish := by intro h; linarith
  have hcutArc : Foundations.ThetaCurve.IsArcFrom κ.cut (κ.start : ℂ) (κ.finish : ℂ) :=
    ⟨κ.cont, injOn_cut_Icc κ hη hw hw0 hs hne, κ.cut_zero, κ.cut_one⟩
  have hsegArc := isArcFrom_realArc hne
  have hsegR : ∀ v ∈ realArc κ.start κ.finish '' Icc 0 1, v ∉ H := by
    rintro _ ⟨t, -, rfl⟩
    exact ofReal_notMem_H _
  have hinter : κ.cut '' Icc 0 1 ∩ realArc κ.start κ.finish '' Icc 0 1 ⊆
      {(κ.start : ℂ), (κ.finish : ℂ)} := by
    rintro v ⟨⟨t, ht, rfl⟩, hv⟩
    rcases cut_eq_start_or_finish κ hw hs ht (hsegR _ hv) with h | h
    · exact Or.inl h
    · exact Or.inr h
  set J := κ.cut '' Icc 0 1 ∪ realArc κ.start κ.finish '' Icc 0 1 with hJdef
  have hJ : LQGMetric.JordanMap.IsJordanCurve J :=
    Foundations.ThetaCurve.isJordanCurve_arc_union hcutArc hsegArc hinter
  have hloopJ : κ.loop '' Icc 0 1 ⊆ J := by
    rintro _ ⟨t, ht, rfl⟩
    rcases κ.loop_mem ht with ⟨u, hu, he⟩ | ⟨y, he, hy₁, hy₂⟩
    · exact Or.inl ⟨u, hu, he.symm⟩
    · refine Or.inr ⟨(κ.start - y) / (κ.start - κ.finish), ⟨?_, ?_⟩, ?_⟩
      · rw [min_eq_right (by linarith)] at hy₁
        rw [max_eq_left (by linarith)] at hy₂
        exact div_nonneg (by linarith) (by linarith)
      · rw [min_eq_right (by linarith)] at hy₁
        exact (div_le_one (by linarith)).2 (by linarith)
      · rw [he]
        unfold realArc
        congr 1
        have hd : κ.start - κ.finish ≠ 0 := sub_ne_zero.2 hne
        field_simp
        ring
  have hnotJ : ∀ v ∈ H, v ∉ chartFlowSet η w s → v ∉ J := by
    rintro v hvH hvA (hv | hv)
    · exact hvA (mem_chartFlowSet_of_mem_cut κ hv hvH)
    · exact hsegR v hv hvH
  obtain ⟨-, hInPre, -, -, -, hOutPre, hOutUnb, -, -⟩ := JordanSides hJ
  have hInD : Disjoint (jordanIn J) (κ.loop '' Icc 0 1) :=
    Set.disjoint_left.2 fun v hv hvl => (jordanIn_subset_compl J hv) (hloopJ hvl)
  have hOutD : Disjoint (jordanOut J) (κ.loop '' Icc 0 1) :=
    Set.disjoint_left.2 fun v hv hvl => (jordanOut_subset_compl J hv) (hloopJ hvl)
  -- the gate point is inside
  set z₀ : ℂ := (x₀ : ℂ) + ((r / 2 : ℝ) : ℂ) * I with hz₀def
  have hz₀b : z₀ ∈ ball (x₀ : ℂ) r := by
    rw [mem_ball, dist_eq_norm, hz₀def, add_sub_cancel_left, norm_mul, norm_I, mul_one, norm_real,
      Real.norm_eq_abs, abs_of_pos (by positivity)]
    linarith
  have hz₀H : z₀ ∈ H := by
    show (0 : ℝ) < ((x₀ : ℂ) + ((r / 2 : ℝ) : ℂ) * I).im
    simp only [add_im, ofReal_im, mul_im, ofReal_re, I_im, mul_one, I_re, mul_zero, add_zero, zero_add]
    linarith
  have hz₀A : z₀ ∉ chartFlowSet η w s := fun h =>
    (Set.eq_empty_iff_forall_notMem.1 havoid) z₀ ⟨hz₀b, subset_closure h⟩
  have hz₀1 := windNum_loop_eq_one_of_gate κ hw hs hr havoid hfx hxs hz₀b hz₀H
  have hz₀In : z₀ ∈ jordanIn J := by
    have hmem : z₀ ∈ jordanIn J ∪ jordanOut J := by
      rw [← compl_eq_jordanIn_union_jordanOut]; exact hnotJ z₀ hz₀H hz₀A
    rcases hmem with h | h
    · exact h
    · have := windNum_eq_zero_of_isPreconnected hγ hl hOutPre hOutUnb hOutD h
      rw [hz₀1] at this
      exact absurd this one_ne_zero
  have hmem : z ∈ jordanIn J ∪ jordanOut J := by
    rw [← compl_eq_jordanIn_union_jordanOut]; exact hnotJ z hzH hzA
  rcases hmem with h | h
  · right
    rw [windNum_eq_of_isPreconnected hγ hl hInPre hInD h hz₀In, hz₀1]
  · left
    exact windNum_eq_zero_of_isPreconnected hγ hl hOutPre hOutUnb hOutD h

/-- **The gate half-ball lies in the unbounded domain of a completed crosscut whose two ends are left of the gate**:
the half-ball, completed by the real ray `[x₀, ∞)`, is a preconnected unbounded subset of `ℍ̄` off the crosscut. -/
theorem mem_H_diff_fillH_of_gate (κ : ExcursionChartCut η w s C) (hw : Continuous w) (hs : 0 ≤ s)
    {x₀ r : ℝ} (hr : 0 < r) (havoid : ball (x₀ : ℂ) r ∩ closure (chartFlowSet η w s) = ∅)
    (hsx : κ.start < x₀) (hfx : κ.finish < x₀) {z : ℂ} (hz : z ∈ ball (x₀ : ℂ) r) (hzH : z ∈ H) :
    z ∈ H \ fillH (κ.cut '' Icc 0 1) := by
  set F := κ.cut '' Icc 0 1 with hFdef
  have hFc : IsCompact F := isCompact_Icc.image_of_continuousOn κ.cont
  set X : Set ℂ := (ball (x₀ : ℂ) r ∩ {v | 0 ≤ v.im}) ∪ {v | v.im = 0 ∧ x₀ ≤ v.re} with hXdef
  have hX₁ : IsPreconnected (ball (x₀ : ℂ) r ∩ {v | 0 ≤ v.im}) :=
    ((convex_ball _ _).inter
      (convex_halfSpace_ge (f := fun v : ℂ => v.im) Complex.imLm.isLinear 0)).isPreconnected
  have hX₂ : IsPreconnected {v : ℂ | v.im = 0 ∧ x₀ ≤ v.re} := by
    have : {v : ℂ | v.im = 0 ∧ x₀ ≤ v.re} = (fun y : ℝ => (y : ℂ)) '' Ici x₀ := by
      ext v
      constructor
      · rintro ⟨h1, h2⟩
        exact ⟨v.re, h2, Complex.ext (by simp) (by simp [h1])⟩
      · rintro ⟨y, hy, rfl⟩
        exact ⟨by simp, by simpa using hy⟩
    rw [this]
    exact isPreconnected_Ici.image _ continuous_ofReal.continuousOn
  have hx₀X₁ : (x₀ : ℂ) ∈ ball (x₀ : ℂ) r ∩ {v | 0 ≤ v.im} := ⟨mem_ball_self hr, by simp⟩
  have hx₀X₂ : (x₀ : ℂ) ∈ {v : ℂ | v.im = 0 ∧ x₀ ≤ v.re} := ⟨by simp, by simp⟩
  have hXc : IsPreconnected X := hX₁.union (x₀ : ℂ) hx₀X₁ hx₀X₂ hX₂
  have hXu : ¬ IsBounded X := by
    intro hb
    obtain ⟨R, hR⟩ := hb.exists_norm_le
    have h := hR (((|x₀| + |R| + 1 : ℝ) : ℂ)) (Or.inr ⟨by simp, by
      simp only [ofReal_re]; linarith [le_abs_self x₀, abs_nonneg R]⟩)
    rw [norm_real, Real.norm_eq_abs, abs_of_pos (by positivity)] at h
    linarith [le_abs_self R, abs_nonneg x₀]
  have hXF : X ⊆ {v | 0 ≤ v.im} \ F := by
    rintro v (⟨hvb, hvi⟩ | ⟨hvi, hvr⟩)
    · refine ⟨hvi, fun hvF => ?_⟩
      exact (Set.eq_empty_iff_forall_notMem.1 havoid) v ⟨hvb, κ.image_cut_subset_closure hvF⟩
    · refine ⟨le_of_eq hvi.symm, fun hvF => ?_⟩
      obtain ⟨t, ht, rfl⟩ := hvF
      have hH : κ.cut t ∉ H := fun h => lt_irrefl _ ((show (0 : ℝ) < (κ.cut t).im from h).trans_eq hvi)
      rcases cut_eq_start_or_finish κ hw hs ht hH with h | h
      · rw [h, ofReal_re] at hvr; linarith
      · rw [h, ofReal_re] at hvr; linarith
  obtain ⟨ε, hε, hfree⟩ := isFreeAt_of_not_isBounded hFc.isClosed hFc.isBounded hXc hXu hXF z
    (Or.inl ⟨hz, le_of_lt (show (0 : ℝ) < z.im from hzH)⟩)
  exact hfree ⟨mem_ball_self hε, hzH⟩

end Gate

/-! ### Janiszewski's theorem for finitely many compact sets meeting only on `ℝ` -/

/-- **Janiszewski's theorem in `ℍ`, finite form.** A point of `ℍ` in the unbounded domains of a compact `T` and of
finitely many compact sets `F i`, any two of which (and each with `T`) meet only on `ℝ`, is in the unbounded domain
of their union. -/
theorem mem_H_diff_fillH_union {ι : Type*} [DecidableEq ι] (S : Finset ι) {F : ι → Set ℂ} {T : Set ℂ}
    (hT : IsCompact T) (hF : ∀ i ∈ S, IsCompact (F i)) (hTF : ∀ i ∈ S, ∀ v ∈ F i ∩ T, v.im = 0)
    (hFF : ∀ i ∈ S, ∀ j ∈ S, i ≠ j → ∀ v ∈ F i ∩ F j, v.im = 0) {z : ℂ} (hzT : z ∈ H \ fillH T)
    (hzF : ∀ i ∈ S, z ∈ H \ fillH (F i)) : z ∈ H \ fillH (T ∪ ⋃ i ∈ S, F i) := by
  induction S using Finset.induction_on with
  | empty => simpa using hzT
  | insert a S ha ih =>
    have hS : ∀ i ∈ S, i ∈ insert a S := fun i hi => Finset.mem_insert_of_mem hi
    have ih' := ih (fun i hi => hF i (hS i hi)) (fun i hi => hTF i (hS i hi))
      (fun i hi j hj hij => hFF i (hS i hi) j (hS j hj) hij) (fun i hi => hzF i (hS i hi))
    have hcomp : IsCompact (T ∪ ⋃ i ∈ S, F i) :=
      hT.union (S.isCompact_biUnion fun i hi => hF i (hS i hi))
    have ha' : a ∈ insert a S := Finset.mem_insert_self a S
    have hreal : ∀ v ∈ (T ∪ ⋃ i ∈ S, F i) ∩ F a, v.im = 0 := by
      rintro v ⟨hv | hv, hva⟩
      · exact hTF a ha' v ⟨hva, hv⟩
      · obtain ⟨i, hi, hvi⟩ := mem_iUnion₂.1 hv
        exact hFF i (hS i hi) a ha' (fun h => ha (h ▸ hi)) v ⟨hvi, hva⟩
    have hJ := H_diff_fillH_inter_subset hcomp (hF a ha') (fun v hv =>
      ⟨{v}, singleton_subset_iff.2 hv, isPreconnected_singleton, rfl, v, rfl, hreal v hv⟩)
      ⟨ih', hzF a ha'⟩
    have heq : T ∪ ⋃ i ∈ insert a S, F i = (T ∪ ⋃ i ∈ S, F i) ∪ F a := by
      rw [Finset.set_biUnion_insert]
      ext v
      simp only [mem_union]
      tauto
    rw [heq]
    exact hJ

end InteractingSLE.Sec5.Prop51Tgt
