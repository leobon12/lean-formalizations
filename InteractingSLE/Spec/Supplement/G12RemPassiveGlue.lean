/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.G12RemPassive

/-!
# A passive zero-weight mark at a real point: gluing the flow to the mark below

Packet PROVE-G12B. Continuation of `G12RemPassive.lean` (one path). Let `v_k` be a force coordinate starting at
`x_k ≤ y` (`ForceCoord`: the Loewner equation with integrable reciprocal gap, a null collision set). Then:

* `vk_le_pflow`, `pflow_le_vj`: on the life of `y`, `v_k ≤ v_y ≤ v_j` for force coordinates from `x_k ≤ y ≤ x_j`;
* `vk_passEnd_eq`: at a finite end `τ < ζ`, `v_k(τ) = w(τ)` (both meet the driver);
* `integral_pflow_passEnd`: `∫₀^τ 2/(v_y − w) = w(τ) − y` (the reciprocal gap is integrable up to `τ`);
* `passMarkPath`: the glued mark (`v_y` on the life, `v_k` afterwards), and `forceCoord_passMarkPath`: **it is a
  force coordinate from `y`**, with `v_k ≤ v_y ≤ v_j` and `w ≤ v_y` at all times before `ζ`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology
open scoped NNReal ENNReal

namespace InteractingSLE

namespace Supp7

namespace G12

/-- A right force coordinate from `x` driven by `w` before `ζ` (the per-mark conditions of Definition 2.1). -/
structure ForceCoord (w : ℝ≥0 → ℝ) (ζ : ℝ≥0∞) (x : ℝ) (v : ℝ≥0 → ℝ) : Prop where
  zero : v 0 = x
  cont : ContinuousOn v {t | (t : ℝ≥0∞) < ζ}
  eq : ∀ {t : ℝ≥0}, (t : ℝ≥0∞) < ζ → v t = x + ∫ s in (0 : ℝ)..t, 2 / (v s.toNNReal - w s.toNNReal)
  int : ∀ {t : ℝ≥0}, (t : ℝ≥0∞) < ζ →
    IntervalIntegrable (fun s : ℝ => 2 / (v s.toNNReal - w s.toNNReal)) volume 0 t
  le : ∀ {t : ℝ≥0}, (t : ℝ≥0∞) < ζ → w t ≤ v t
  null : volume {s : ℝ | 0 ≤ s ∧ (s.toNNReal : ℝ≥0∞) < ζ ∧ w s.toNNReal = v s.toNNReal} = 0

variable {w : ℝ≥0 → ℝ} {ζ : ℝ≥0∞} {y : ℝ} {U : ℕ → ℝ≥0 → ℝ}

/-- `2/(v − w) = −2 (w − v)⁻¹`. -/
theorem two_div_sub_eq (a b : ℝ) : 2 / (a - b) = -2 * (b - a)⁻¹ := by
  rw [div_eq_mul_inv, ← neg_sub, inv_neg]; ring

/-- The right marks of a force path are force coordinates. -/
theorem forceCoord_of_isForcePath {nL nR : ℕ} {xL : Fin nL → ℝ} {xR : Fin nR → ℝ} {ρL : Fin nL → ℝ}
    {ρR : Fin nR → ℝ} {vL : Fin nL → ℝ≥0 → ℝ} {vR : Fin nR → ℝ≥0 → ℝ}
    (h : Sec2.IsForcePath xL xR ρL ρR w vL vR ζ) (j : Fin nR) : ForceCoord w ζ (xR j) (vR j) where
  zero := h.vR_zero j
  cont := h.continuousOn_vR j
  eq ht := h.vR_eq ht j
  int ht := by
    have := (h.integrable_gapR ht j).const_mul (-2)
    refine this.congr fun s _ => ?_
    simp only [two_div_sub_eq]
  le ht := h.w_le_vR ht j
  null := h.volume_collisionR j

theorem ForceCoord.mono {x : ℝ} {v : ℝ≥0 → ℝ} (hv : ForceCoord w ζ x v) {τ : ℝ≥0∞} (hτ : τ ≤ ζ) :
    ForceCoord w τ x v where
  zero := hv.zero
  cont := hv.cont.mono fun _ ht => lt_of_lt_of_le ht hτ
  eq ht := hv.eq (lt_of_lt_of_le ht hτ)
  int ht := hv.int (lt_of_lt_of_le ht hτ)
  le ht := hv.le (lt_of_lt_of_le ht hτ)
  null := by
    refine measure_mono_null (fun s hs => ?_) hv.null
    exact ⟨hs.1, lt_of_lt_of_le hs.2.1 hτ, hs.2.2⟩

/-- **The flow of `y` is a force coordinate on its life.** -/
theorem PassHyp.forceCoord_pflow (hH : PassHyp w ζ y U) : ForceCoord w (passEnd w ζ U) y (pflow U) where
  zero := by
    by_cases h : (0 : ℝ≥0∞) < passEnd w ζ U
    · obtain ⟨n, hn⟩ := hH.lt_passEnd_iff.1 (by rw [ENNReal.coe_zero]; exact h)
      rw [hH.pflow_eq hn le_rfl, hH.zero_U]
    · -- an empty life: `ζ = 0`, and the flow is the constant limit of the cut flows at `0`
      unfold pflow
      simp only [hH.zero_U]
      exact limsup_const y
  cont := hH.continuousOn_pflow
  eq ht := hH.pflow_eq_integral (hH.lt_passEnd_iff.1 ht)
  int ht := hH.intervalIntegrable_integrand (hH.lt_passEnd_iff.1 ht)
  le ht := (hH.w_lt_pflow (hH.lt_passEnd_iff.1 ht)).le
  null := by
    refine measure_mono_null (fun s hs => ?_) (measure_empty (μ := volume))
    exact absurd hs.2.2 (hH.w_lt_pflow (hH.lt_passEnd_iff.1 hs.2.1)).ne

/-- **Order with a force coordinate from `x ≤ x'`** (`Sec2.le_of_forceEq_right`). -/
theorem ForceCoord.le_of_le {τ : ℝ≥0∞} {x x' : ℝ} {u v : ℝ≥0 → ℝ} (hv : ForceCoord w τ x v)
    (hu : ForceCoord w τ x' u) (hxx : x ≤ x') {t : ℝ≥0} (ht : (t : ℝ≥0∞) < τ) : v t ≤ u t :=
  Sec2.le_of_forceEq_right hxx hu.cont hv.cont hu.eq hv.eq hu.int hv.int hu.le hu.null ht

/-- **At a finite end `τ < ζ`, a force coordinate from `x_k ≤ y` meets the driver.** -/
theorem PassHyp.vk_passEnd_eq (hH : PassHyp w ζ y U) {τ : ℝ≥0} (hτ : passEnd w ζ U = τ) (hτζ : (τ : ℝ≥0∞) < ζ)
    {xk : ℝ} {vk : ℝ≥0 → ℝ} (hvk : ForceCoord w ζ xk vk) (hxk : xk ≤ y) : vk τ = w τ := by
  have hlim := hH.tendsto_pflow_passEnd hτ hτζ
  have hτ0 : 0 < τ := by
    refine pos_iff_ne_zero.2 fun h0 => ?_
    have h := hH.alive_zero (lt_of_le_of_lt zero_le (h0 ▸ hτζ))
    have := hH.lt_passEnd_iff.2 h
    rw [hτ, h0] at this
    exact lt_irrefl _ this
  have : (𝓝[<] τ).NeBot := nhdsLT_neBot_of_exists_lt ⟨0, hτ0⟩
  have hopen : IsOpen {s : ℝ≥0 | (s : ℝ≥0∞) < ζ} := isOpen_lt ENNReal.continuous_coe continuous_const
  have hvkc : Tendsto vk (𝓝[<] τ) (𝓝 (vk τ)) :=
    (hvk.cont.continuousAt (hopen.mem_nhds hτζ)).tendsto.mono_left nhdsWithin_le_nhds
  have hle : vk τ ≤ w τ := by
    refine le_of_tendsto_of_tendsto hvkc hlim ?_
    filter_upwards [self_mem_nhdsWithin] with s hs
    exact (hvk.mono (passEnd_le (U := U))).le_of_le hH.forceCoord_pflow hxk (by rw [hτ]; exact_mod_cast hs)
  exact le_antisymm hle (hvk.le hτζ)

/-! ### Up to a finite end of the life -/

theorem tendsto_toNNReal_nhdsLT' {T : ℝ≥0} (hT : 0 < T) : Tendsto Real.toNNReal (𝓝[<] (T : ℝ)) (𝓝[<] T) := by
  refine tendsto_nhdsWithin_iff.2 ⟨?_, ?_⟩
  · have := continuous_real_toNNReal.tendsto (T : ℝ)
    simpa using this.mono_left nhdsWithin_le_nhds
  · filter_upwards [Ioo_mem_nhdsLT (show (0 : ℝ) < T from hT)] with x hx
    show x.toNNReal < T
    rw [Real.toNNReal_lt_iff_lt_coe hx.1.le]; exact hx.2

theorem PassHyp.passEnd_pos (hH : PassHyp w ζ y U) {τ : ℝ≥0} (hτ : passEnd w ζ U = τ) (hτζ : (τ : ℝ≥0∞) < ζ) :
    0 < τ := by
  refine pos_iff_ne_zero.2 fun h0 => ?_
  have h := hH.alive_zero (lt_of_le_of_lt zero_le (h0 ▸ hτζ))
  have := hH.lt_passEnd_iff.2 h
  rw [hτ, h0] at this
  exact lt_irrefl _ this

/-- **The reciprocal gap of `y` is integrable up to a finite end `τ < ζ`, with integral `w(τ) − y`.** -/
theorem PassHyp.integral_pflow_passEnd (hH : PassHyp w ζ y U) {τ : ℝ≥0} (hτ : passEnd w ζ U = τ)
    (hτζ : (τ : ℝ≥0∞) < ζ) :
    IntervalIntegrable (fun r : ℝ => 2 / (pflow U r.toNNReal - w r.toNNReal)) volume 0 τ ∧
      ∫ r in (0 : ℝ)..τ, 2 / (pflow U r.toNNReal - w r.toNNReal) = w τ - y := by
  set f : ℝ → ℝ := fun r => 2 / (pflow U r.toNNReal - w r.toNNReal) with hf
  have hτ0 := hH.passEnd_pos hτ hτζ
  have hτ0' : (0 : ℝ) < τ := hτ0
  have hlife : ∀ s < τ, Alive w ζ U s := fun s hs => hH.lt_passEnd_iff.1 (by rw [hτ]; exact_mod_cast hs)
  have hlim := hH.tendsto_pflow_passEnd hτ hτζ
  have : (𝓝[<] τ).NeBot := nhdsLT_neBot_of_exists_lt ⟨0, hτ0⟩
  have hbound : ∀ s < τ, pflow U s ≤ w τ := by
    intro s hs
    refine ge_of_tendsto hlim ?_
    filter_upwards [Ioo_mem_nhdsLT hs] with r hr
    exact hH.pflow_le_of_le (hlife r hr.2) hr.1.le
  have hR : Tendsto (fun r : ℝ => pflow U r.toNNReal) (𝓝[<] (τ : ℝ)) (𝓝 (w τ)) :=
    hlim.comp (tendsto_toNNReal_nhdsLT' hτ0)
  have hprim : ∀ x ∈ Ico (0 : ℝ) τ, ∫ r in (0 : ℝ)..x, f r = pflow U x.toNNReal - y := by
    intro x hx
    have hxτ : x.toNNReal < τ := by rw [Real.toNNReal_lt_iff_lt_coe hx.1]; exact hx.2
    have := hH.pflow_eq_integral (hlife _ hxτ)
    rw [Real.coe_toNNReal _ hx.1] at this
    rw [hf]; linarith
  have hintx : ∀ x ∈ Ico (0 : ℝ) τ, IntervalIntegrable f volume 0 x := by
    intro x hx
    have hxτ : x.toNNReal < τ := by rw [Real.toNNReal_lt_iff_lt_coe hx.1]; exact hx.2
    have := hH.intervalIntegrable_integrand (hlife _ hxτ)
    rwa [Real.coe_toNNReal _ hx.1] at this
  have hfnn : ∀ x ∈ Ico (0 : ℝ) τ, 0 ≤ f x := by
    intro x hx
    have hxτ : x.toNNReal < τ := by rw [Real.toNNReal_lt_iff_lt_coe hx.1]; exact hx.2
    exact div_nonneg zero_le_two (sub_nonneg.2 (hH.w_lt_pflow (hlife _ hxτ)).le)
  -- integrability on `(0, τ]` from the bounded primitives
  set b : ℕ → ℝ := fun n => τ - τ / ((n : ℝ) + 2) with hb
  have hbI : ∀ n, b n ∈ Ico (0 : ℝ) τ := fun n => by
    have h2 : (0 : ℝ) < (n : ℝ) + 2 := by positivity
    have h1 : (τ : ℝ) / ((n : ℝ) + 2) ≤ τ := div_le_self hτ0'.le (by linarith [n.cast_nonneg (α := ℝ)])
    exact ⟨by rw [hb]; linarith, by rw [hb]; linarith [div_pos hτ0' h2]⟩
  have hbl : Tendsto b atTop (𝓝 (τ : ℝ)) := by
    have : Tendsto (fun n : ℕ => (τ : ℝ) / ((n : ℝ) + 2)) atTop (𝓝 0) := by
      refine tendsto_const_nhds.div_atTop ?_
      exact tendsto_atTop_add_const_right _ 2 tendsto_natCast_atTop_atTop
    simpa [hb] using (tendsto_const_nhds (x := (τ : ℝ))).sub this
  have hIoc : IntegrableOn f (Ioc 0 (τ : ℝ)) := by
    refine integrableOn_Ioc_of_intervalIntegral_norm_bounded_right (I := w τ - y) (l := atTop) (b := b)
      (fun n => (intervalIntegrable_iff_integrableOn_Ioc_of_le (hbI n).1).1 (hintx _ (hbI n))) hbl
      (Eventually.of_forall fun n => ?_)
    have heq : ∫ x in Ioc 0 (b n), ‖f x‖ = ∫ x in Ioc 0 (b n), f x := by
      refine setIntegral_congr_fun measurableSet_Ioc fun x hx => ?_
      exact Real.norm_of_nonneg (hfnn x ⟨hx.1.le, lt_of_le_of_lt hx.2 (hbI n).2⟩)
    rw [heq, ← intervalIntegral.integral_of_le (hbI n).1, hprim _ (hbI n)]
    have hbτ : (b n).toNNReal < τ := by rw [Real.toNNReal_lt_iff_lt_coe (hbI n).1]; exact (hbI n).2
    linarith [hbound _ hbτ]
  have hII : IntervalIntegrable f volume 0 τ :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le hτ0'.le).2 hIoc
  refine ⟨hII, ?_⟩
  -- the value: continuity of the primitive at `τ`
  have hcont : ContinuousOn (fun x => ∫ r in (0 : ℝ)..x, f r) (uIcc 0 (τ : ℝ)) :=
    intervalIntegral.continuousOn_primitive_interval (by
      rw [uIcc_of_le hτ0'.le]; exact (integrableOn_Icc_iff_integrableOn_Ioc (by simp)).2 hIoc)
  rw [uIcc_of_le hτ0'.le] at hcont
  have h1 : Tendsto (fun x => ∫ r in (0 : ℝ)..x, f r) (𝓝[<] (τ : ℝ)) (𝓝 (∫ r in (0 : ℝ)..τ, f r)) := by
    have := (hcont _ ⟨hτ0'.le, le_rfl⟩).tendsto
    refine this.mono_left ?_
    rw [← nhdsWithin_Ico_eq_nhdsLT hτ0']
    exact nhdsWithin_mono _ Ico_subset_Icc_self
  have h2 : Tendsto (fun x => ∫ r in (0 : ℝ)..x, f r) (𝓝[<] (τ : ℝ)) (𝓝 (w τ - y)) := by
    refine (hR.sub_const y).congr' ?_
    filter_upwards [Ioo_mem_nhdsLT hτ0'] with x hx
    exact (hprim x ⟨hx.1.le, hx.2⟩).symm
  have : (𝓝[<] (τ : ℝ)).NeBot := nhdsLT_neBot_of_exists_lt ⟨0, hτ0'⟩
  exact tendsto_nhds_unique h1 h2

/-! ### The glued mark -/

open Classical in
/-- **The passive mark of `y` along one path**: the flow of `y` at time `0` and on its life, the force coordinate
`v_k` of a mark below `y` afterwards. -/
def passMarkPath (w : ℝ≥0 → ℝ) (ζ : ℝ≥0∞) (U : ℕ → ℝ≥0 → ℝ) (vk : ℝ≥0 → ℝ) (t : ℝ≥0) : ℝ :=
  if t = 0 ∨ Alive w ζ U t then pflow U t else vk t

theorem ForceCoord.congr {x : ℝ} {v v' : ℝ≥0 → ℝ} (hv : ForceCoord w ζ x v) (h0 : v' 0 = x)
    (h : ∀ t : ℝ≥0, (t : ℝ≥0∞) < ζ → v' t = v t) : ForceCoord w ζ x v' where
  zero := h0
  cont := hv.cont.congr fun t ht => h t ht
  eq {t} ht := by
    have hr : ∀ r ∈ uIcc (0 : ℝ) t, v' r.toNNReal = v r.toNNReal := fun r hr => by
      rw [uIcc_of_le t.coe_nonneg] at hr
      exact h _ (lt_of_le_of_lt (ENNReal.coe_le_coe.2 (Real.toNNReal_le_iff_le_coe.2 hr.2)) ht)
    rw [h _ ht, hv.eq ht]
    congr 1
    exact intervalIntegral.integral_congr fun r hr' => by simp only [hr r hr']
  int {t} ht := by
    refine (hv.int ht).congr fun r hr => ?_
    rw [uIoc_of_le t.coe_nonneg] at hr
    have := h _ (lt_of_le_of_lt (ENNReal.coe_le_coe.2 (Real.toNNReal_le_iff_le_coe.2 hr.2)) ht)
    simp only [this]
  le ht := by rw [h _ ht]; exact hv.le ht
  null := by
    refine measure_mono_null (fun s hs => ?_) hv.null
    exact ⟨hs.1, hs.2.1, by rw [hs.2.2, h _ hs.2.1]⟩

theorem passMarkPath_of_alive {vk : ℝ≥0 → ℝ} {t : ℝ≥0} (ha : Alive w ζ U t) :
    passMarkPath w ζ U vk t = pflow U t := by
  simp [passMarkPath, ha]

theorem passMarkPath_of_dead {vk : ℝ≥0 → ℝ} {t : ℝ≥0} (ht : t ≠ 0) (ha : ¬ Alive w ζ U t) :
    passMarkPath w ζ U vk t = vk t := by
  simp [passMarkPath, ht, ha]

/-- **The glued passive mark is a force coordinate from `y`**, between the force coordinates from `x_k ≤ y` and from
any `x_j ≥ y` that is above `v_k`. -/
theorem PassHyp.forceCoord_passMarkPath (hH : PassHyp w ζ y U) {xk : ℝ} {vk : ℝ≥0 → ℝ}
    (hvk : ForceCoord w ζ xk vk) (hxk : xk ≤ y) :
    ForceCoord w ζ y (passMarkPath w ζ U vk) ∧
      (∀ t : ℝ≥0, (t : ℝ≥0∞) < ζ → vk t ≤ passMarkPath w ζ U vk t) ∧
      ∀ {xj : ℝ} {vj : ℝ≥0 → ℝ}, ForceCoord w ζ xj vj → y ≤ xj → (∀ t : ℝ≥0, (t : ℝ≥0∞) < ζ → vk t ≤ vj t) →
        ∀ t : ℝ≥0, (t : ℝ≥0∞) < ζ → passMarkPath w ζ U vk t ≤ vj t := by
  set v := passMarkPath w ζ U vk with hvdef
  have hP := hH.forceCoord_pflow
  have hv0 : v 0 = y := by
    simp only [hvdef, passMarkPath, true_or, ↓reduceIte]; exact hP.zero
  have hva : ∀ t, Alive w ζ U t → v t = pflow U t := fun t ha => passMarkPath_of_alive ha
  rcases (passEnd_le (w := w) (ζ := ζ) (U := U)).lt_or_eq with hlt | heq
  swap
  · -- the life is all of `[0, ζ)`
    have hall : ∀ t : ℝ≥0, (t : ℝ≥0∞) < ζ → Alive w ζ U t := fun t ht =>
      hH.lt_passEnd_iff.1 (by rw [heq]; exact ht)
    have hP' : ForceCoord w ζ y (pflow U) := heq ▸ hP
    refine ⟨hP'.congr hv0 fun t ht => hva t (hall t ht), fun t ht => ?_, fun {xj vj} hvj hy _ t ht => ?_⟩
    · rw [hva t (hall t ht)]; exact hvk.le_of_le hP' hxk ht
    · rw [hva t (hall t ht)]; exact hP'.le_of_le hvj hy ht
  -- a finite end `τ < ζ`
  obtain ⟨τ, hτ⟩ := WithTop.ne_top_iff_exists.1 (ne_top_of_lt hlt)
  have hτ' : passEnd w ζ U = τ := hτ.symm
  have hτζ : (τ : ℝ≥0∞) < ζ := hτ' ▸ hlt
  have hτ0 := hH.passEnd_pos hτ' hτζ
  have hτ0' : (0 : ℝ) < τ := hτ0
  have hlife : ∀ s < τ, Alive w ζ U s := fun s hs => hH.lt_passEnd_iff.1 (by rw [hτ']; exact_mod_cast hs)
  have hdead : ∀ s, τ ≤ s → v s = vk s := fun s hs => passMarkPath_of_dead
    (ne_of_gt (lt_of_lt_of_le hτ0 hs)) fun ha => absurd (hH.lt_passEnd_iff.2 ha)
      (by rw [hτ']; exact not_lt.2 (by exact_mod_cast hs))
  have hvkτ := hH.vk_passEnd_eq hτ' hτζ hvk hxk
  obtain ⟨hI, hIval⟩ := hH.integral_pflow_passEnd hτ' hτζ
  have hPτ : ForceCoord w τ y (pflow U) := hτ' ▸ hP
  have hopen : IsOpen {s : ℝ≥0 | (s : ℝ≥0∞) < ζ} := isOpen_lt ENNReal.continuous_coe continuous_const
  -- the reciprocal gap of `v` up to `τ`
  have hae : ∀ᵐ r ∂(volume : Measure ℝ), r ∈ uIoc (0 : ℝ) τ →
      2 / (pflow U r.toNNReal - w r.toNNReal) = 2 / (v r.toNNReal - w r.toNNReal) := by
    have hne : ∀ᵐ r ∂(volume : Measure ℝ), r ≠ (τ : ℝ) := by
      rw [ae_iff]; simp
    filter_upwards [hne] with r hr hrI
    rw [uIoc_of_le hτ0'.le] at hrI
    have hrτ : r.toNNReal < τ := by
      rw [Real.toNNReal_lt_iff_lt_coe hrI.1.le]; exact lt_of_le_of_ne hrI.2 hr
    rw [hva _ (hlife _ hrτ)]
  have hIv : IntervalIntegrable (fun r : ℝ => 2 / (v r.toNNReal - w r.toNNReal)) volume 0 τ :=
    hI.congr_ae ((ae_restrict_iff' measurableSet_uIoc).2 hae)
  have hIvval : ∫ r in (0 : ℝ)..τ, 2 / (v r.toNNReal - w r.toNNReal) = w τ - y := by
    rw [← hIval]; exact (intervalIntegral.integral_congr_ae hae).symm
  have hafter : ∀ {t : ℝ≥0}, τ ≤ t → EqOn (fun r : ℝ => 2 / (v r.toNNReal - w r.toNNReal))
      (fun r : ℝ => 2 / (vk r.toNNReal - w r.toNNReal)) (uIcc (τ : ℝ) t) := fun {t} hτt r hr => by
    rw [uIcc_of_le (show (τ : ℝ) ≤ t from hτt)] at hr
    have : τ ≤ r.toNNReal := by rw [Real.le_toNNReal_iff_coe_le (hτ0'.le.trans hr.1)]; exact hr.1
    simp only [hdead _ this]
  have hint : ∀ {t : ℝ≥0}, (t : ℝ≥0∞) < ζ →
      IntervalIntegrable (fun s : ℝ => 2 / (v s.toNNReal - w s.toNNReal)) volume 0 t := by
    intro t ht
    rcases lt_or_ge t τ with htτ | hτt
    · refine (hPτ.int (by exact_mod_cast htτ)).congr fun r hr => ?_
      rw [uIoc_of_le t.coe_nonneg] at hr
      have : r.toNNReal < τ := by
        rw [Real.toNNReal_lt_iff_lt_coe hr.1.le]; exact lt_of_le_of_lt hr.2 htτ
      simp only [hva _ (hlife _ this)]
    · have hk : IntervalIntegrable (fun s : ℝ => 2 / (vk s.toNNReal - w s.toNNReal)) volume τ t :=
        (hvk.int ht).mono_set (by
          rw [uIcc_of_le (show (τ : ℝ) ≤ t from hτt), uIcc_of_le t.coe_nonneg]
          exact Icc_subset_Icc hτ0'.le le_rfl)
      exact hIv.trans (hk.congr fun r hr => (hafter hτt (uIoc_subset_uIcc hr)).symm)
  refine ⟨⟨hv0, fun t ht => ?_, fun {t} ht => ?_, hint, fun {t} ht => ?_, ?_⟩, fun t ht => ?_,
    fun {xj vj} hvj hy hkj t ht => ?_⟩
  · -- continuity
    rcases lt_trichotomy t τ with htτ | rfl | hτt
    · refine ((hH.continuousAt_pflow (hlife t htτ)).congr ?_).continuousWithinAt
      filter_upwards [Iio_mem_nhds htτ] with s hs
      exact (hva s (hlife s hs)).symm
    · refine (continuousAt_iff_continuous_left_right.2 ⟨?_, ?_⟩).continuousWithinAt
      · rw [← continuousWithinAt_Iio_iff_Iic, ContinuousWithinAt, hdead _ le_rfl, hvkτ]
        refine (hH.tendsto_pflow_passEnd hτ' hτζ).congr' ?_
        filter_upwards [self_mem_nhdsWithin] with s hs
        exact (hva s (hlife s hs)).symm
      · exact ((hvk.cont.continuousAt (hopen.mem_nhds hτζ)).continuousWithinAt).congr
          (fun s hs => hdead s hs) (hdead _ le_rfl)
    · refine ((hvk.cont.continuousAt (hopen.mem_nhds ht)).congr ?_).continuousWithinAt
      filter_upwards [Ioi_mem_nhds hτt] with s hs
      exact (hdead s hs.le).symm
  · -- the equation
    rcases lt_or_ge t τ with htτ | hτt
    · rw [hva t (hlife t htτ), hPτ.eq (by exact_mod_cast htτ)]
      congr 1
      refine intervalIntegral.integral_congr fun r hr => ?_
      rw [uIcc_of_le t.coe_nonneg] at hr
      have : r.toNNReal < τ := by
        rw [Real.toNNReal_lt_iff_lt_coe hr.1]; exact lt_of_le_of_lt hr.2 htτ
      simp only [hva _ (hlife _ this)]
    · have hk : IntervalIntegrable (fun s : ℝ => 2 / (vk s.toNNReal - w s.toNNReal)) volume 0 τ :=
        (hvk.int ht).mono_set (by
          rw [uIcc_of_le hτ0'.le, uIcc_of_le t.coe_nonneg]
          exact Icc_subset_Icc le_rfl hτt)
      have hk2 : IntervalIntegrable (fun s : ℝ => 2 / (vk s.toNNReal - w s.toNNReal)) volume τ t :=
        (hvk.int ht).mono_set (by
          rw [uIcc_of_le (show (τ : ℝ) ≤ t from hτt), uIcc_of_le t.coe_nonneg]
          exact Icc_subset_Icc hτ0'.le le_rfl)
      have hv2 : IntervalIntegrable (fun s : ℝ => 2 / (v s.toNNReal - w s.toNNReal)) volume τ t :=
        hk2.congr fun r hr => (hafter hτt (uIoc_subset_uIcc hr)).symm
      rw [← intervalIntegral.integral_add_adjacent_intervals hIv hv2, hIvval,
        intervalIntegral.integral_congr (hafter hτt), hdead t hτt]
      have h1 := hvk.eq ht
      have h2 := hvk.eq hτζ
      rw [← intervalIntegral.integral_add_adjacent_intervals hk hk2] at h1
      linarith
  · -- `w ≤ v`
    rcases lt_or_ge t τ with htτ | hτt
    · rw [hva t (hlife t htτ)]; exact (hH.w_lt_pflow (hlife t htτ)).le
    · rw [hdead t hτt]; exact hvk.le ht
  · -- the collision set
    refine measure_mono_null (fun s hs => ?_) hvk.null
    refine ⟨hs.1, hs.2.1, ?_⟩
    rcases lt_or_ge s.toNNReal τ with hsτ | hτs
    · exact absurd (hs.2.2.trans (hva _ (hlife _ hsτ))) (hH.w_lt_pflow (hlife _ hsτ)).ne
    · rw [hs.2.2, hdead _ hτs]
  · -- `v_k ≤ v`
    rcases lt_or_ge t τ with htτ | hτt
    · rw [hva t (hlife t htτ)]
      exact (hvk.mono hτζ.le).le_of_le hPτ hxk (by exact_mod_cast htτ)
    · rw [hdead t hτt]
  · -- `v ≤ v_j`
    rcases lt_or_ge t τ with htτ | hτt
    · rw [hva t (hlife t htτ)]
      exact hPτ.le_of_le (hvj.mono hτζ.le) hy (by exact_mod_cast htτ)
    · rw [hdead t hτt]; exact hkj t ht

end G12

end Supp7

end InteractingSLE
