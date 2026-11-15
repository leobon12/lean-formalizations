/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec5.Prop51HGateLocal

/-!
# The crosscut loops near a free positive gate and far away

Packet PROVE-PROP51H-TOPO2 (ruling R71; Astra's follow-up 4, §1.7). For a completed chart crosscut `κ` (finishing
gate `κ.finish < 0`) and a free positive real gate `x₀ > 0` (a ball about `x₀` missing the closure of the chart
flow set):

* `ExcursionChartCut.windNum_loop_nonneg_of_gate`: the closed loop of `κ` has **nonnegative** winding number about
  every point of the upper half-ball at `x₀`. Either `x₀` lies outside the real segment between the two ends of `κ`
  (index `0`, through the lower half-plane), or `κ.finish < x₀ < κ.start` and the real segment is traversed to the
  right through `x₀` (index `1`, by the jump lemma `windNum_jump_real`);
* `ExcursionChartCut.windNum_loop_eq_zero_of_norm`: index `0` outside a ball containing the chart flow set.

Deterministic; nothing here replaces a source theorem.
-/

set_option autoImplicit false

noncomputable section

open Complex Set Filter Topology Metric Bornology
open QuantumZipper (H Hbar)

namespace InteractingSLE.Sec5.Prop51HGate

open WangWu hiding ratPt exists_ratPt_dist_lt
open Prop51G Prop51HTopo
open _root_.InteractingSLE.Orientation

variable {η : ℝ → ℂ} {w : ℝ → ℝ} {s : ℝ} {C : Set ℝ}

namespace ExcursionChartCut

variable (κ : ExcursionChartCut η w s C)

theorem im_loop_nonneg (hw : Continuous w) (hs : 0 ≤ s) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    0 ≤ (κ.loop t).im := by
  rcases κ.loop_mem ht with ⟨u, hu, he⟩ | ⟨y, he, -⟩
  · rw [he]
    rcases eq_endpoints_or_mem_Ioo_of_mem_Icc hu with rfl | rfl | hu'
    · rw [κ.cut_zero]; simp
    · rw [κ.cut_one]; simp
    · exact (show (0 : ℝ) < (κ.cut u).im from κ.cut_mem_H hw hs hu').le
  · rw [he]; simp

/-- Far from the chart flow set the loop has winding number zero. -/
theorem windNum_loop_eq_zero_of_norm {R : ℝ} (hR : closure (chartFlowSet η w s) ⊆ ball 0 R) {z : ℂ}
    (hz : R ≤ ‖z‖) : windNum κ.loop z = 0 :=
  windNum_eq_zero_of_norm_lt κ.continuousOn_loop κ.loop_closed fun _ ht =>
    (κ.norm_loop_lt hR ht).trans_le hz

/-- **Near a free positive gate the loop of a crosscut with a western finishing gate has nonnegative winding
number.** -/
theorem windNum_loop_nonneg_of_gate (hw : Continuous w) (hs : 0 ≤ s) {x₀ r : ℝ} (hx₀ : 0 < x₀)
    (hr : 0 < r) (havoid : ball (x₀ : ℂ) r ∩ closure (chartFlowSet η w s) = ∅) {z : ℂ}
    (hz : z ∈ ball (x₀ : ℂ) r) (hzH : z ∈ H) : 0 ≤ windNum κ.loop z := by
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
  have hfin := κ.finish_neg
  -- the open upper half-ball misses the loop
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
  -- the lower half-plane misses the loop and carries index zero
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
  rcases le_or_gt κ.start x₀ with hsx | hsx
  · -- `x₀` is not between the two ends: index zero through the lower half-plane
    have hsx' : κ.start ≤ x₀ - r := by
      rw [abs_of_nonpos (by linarith)] at hst
      linarith
    have hfx' : κ.finish ≤ x₀ - r := by
      rw [abs_of_neg (by linarith)] at hfi
      linarith
    have hT : IsPreconnected (ball (x₀ : ℂ) r ∪ L) := by
      refine (convex_ball _ _).isPreconnected.union' ⟨(x₀ : ℂ) - ((r / 2 : ℝ) : ℂ) * I, ?_, ?_⟩
        hLc.isPreconnected
      · rw [mem_ball, dist_eq_norm, sub_sub_cancel_left, norm_neg, norm_mul, norm_I, mul_one,
          norm_real, Real.norm_eq_abs, abs_of_pos (by positivity)]
        linarith
      · show ((x₀ : ℂ) - ((r / 2 : ℝ) : ℂ) * I).im < 0
        simp only [sub_im, ofReal_im, mul_im, ofReal_re, I_im, mul_one, I_re, mul_zero, add_zero,
          zero_sub]
        linarith
    have hTγ : Disjoint (ball (x₀ : ℂ) r ∪ L) (κ.loop '' Icc 0 1) := by
      refine Set.disjoint_union_left.2 ⟨Set.disjoint_left.2 fun v hv hvγ => ?_, hLγ⟩
      obtain ⟨t, ht, rfl⟩ := hvγ
      rcases κ.loop_mem ht with ⟨u, hu, he⟩ | ⟨y, he, hy₁, hy₂⟩
      · have := hfar _ (κ.image_cut_subset_closure ⟨u, hu, rfl⟩)
        rw [← he, ← dist_eq_norm] at this
        exact absurd (mem_ball.1 hv) (not_lt.2 this)
      · rw [he, mem_ball, dist_eq_norm, ← ofReal_sub, norm_real, Real.norm_eq_abs, abs_lt] at hv
        have : y ≤ x₀ - r := hy₂.trans (max_le hsx' hfx')
        linarith [hv.1]
    have hTu : ¬ IsBounded (ball (x₀ : ℂ) r ∪ L) := fun hb => hLu (hb.subset subset_union_right)
    rw [windNum_eq_zero_of_isPreconnected hγ hl hT hTu hTγ (Or.inl hz)]
  · -- `κ.finish < x₀ < κ.start`: the real segment crosses `x₀` to the right
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

end ExcursionChartCut

end InteractingSLE.Sec5.Prop51HGate
