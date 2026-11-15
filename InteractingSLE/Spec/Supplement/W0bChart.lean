/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.ReverseArcMain
import InteractingSLE.Spec.Supplement.S9BOrder
import InteractingSLE.Spec.Supplement.S10Order
import InteractingSLE.WangWu.Prop418Side

/-!
# Lemma W0b, the chart side: approaches from the right side of a completion

Packet PROVE-G12D (specification supplement §9, Lemma W0b, p. 529, `source/spec/p529-576.md#id-W0b-proof`: "Its
common right-hand side is exposed to the joint unbounded component. One direct verification is to use the ordered
proper completion of the right-hand path: its right collar avoids the other path").

Deterministic. Let `γ` be a simple trace stopped at `q` with interior tip `γ(q) ∈ ℍ`, with chart `f` (the centred
mapping-out function of `A = fill γ([0, q])`, `ReverseArc.IsChart`) and inverse `Φ`, and let `γ''` be a proper curve
(`Supp9B.IsProperCurve`: continuous, injective, in `ℍ̄`, tending to `∞`) agreeing with `γ` on `[0, q]` whose tail
`γ''((q, ∞))` lies in `ℍ`. Write `D = ℍ \ fill A` and `R = Supp9B.rightSide γ''` (the side of the curve closed along
its lower vertical seed ray that contains `γ''(0) + 1 − i`).

* The tail lies in `D`, and `γ* = f ∘ γ''(q + ·)` (with `γ*(0) = 0`, the tip) is a simple proper arc of `ℍ` from `0`
  (`isProperArc_futureChartArc`).
* **`mem_rightSideOf_of_mem_rightSide`**: `f` maps `R ∩ D` into the right side of `γ*`. Otherwise the connected set
  `Φ(left side of γ*)` would join `R` to a far-left real point, which lies on the left side of `γ''` (Jordan
  separation, `Supp9B.disjoint_leftSide_rightSide`).
* **`exists_pos_tendsto_of_rightSide`**: along every approach to a non-tip trace point `γ(s) ∈ ℍ` from `R ∩ D`, the
  chart tends to a **positive** real (no negative real point is adherent to the right side of `γ*`).
* **`subset_H_diff_fillH_of_rightSide`**: `R ∩ D` lies in the unbounded domain of every closed set `Γ` that misses
  `R ∩ D` (`Φ` maps the right side of `γ*`, a connected unbounded set, into `R ∩ D`).

The physical forms (seed `x`, chart `z ↦ f_q(z − x)`) are `exists_pos_tendsto_of_rightSide_phys` and
`subset_H_diff_fillH_of_rightSide_phys`.
-/

set_option autoImplicit false

noncomputable section

open Set Metric Filter Topology Bornology Complex
open scoped NNReal ENNReal
open QuantumZipper (H Hbar)

namespace InteractingSLE

namespace Supp9

namespace W0b

open Sec7 Sec7.ReverseArc HalfPlaneSep Supp9B

/-! ### The tail of a completion in the chart -/

section Centred

variable {γ γ'' : ℝ≥0 → ℂ} {q : ℝ≥0} {f Φ : ℂ → ℂ}

/-- The chart image of the tail `γ''([q, ∞))` of a completion, as a curve from `0` (the image of the tip). -/
def futureChartArc (f : ℂ → ℂ) (γ'' : ℝ≥0 → ℂ) (q : ℝ≥0) (t : ℝ) : ℂ :=
  if t ≤ 0 then 0 else f (γ'' (q + t.toNNReal))

theorem futureChartArc_of_pos {t : ℝ} (ht : 0 < t) :
    futureChartArc f γ'' q t = f (γ'' (q + t.toNNReal)) := by
  simp [futureChartArc, not_le.2 ht]

theorem futureChartArc_of_nonpos {t : ℝ} (ht : t ≤ 0) : futureChartArc f γ'' q t = 0 := by
  simp [futureChartArc, ht]

/-- The completion agrees with the stopped trace, so its prefix is the stopped range. -/
theorem image_Icc_eq (hag : ∀ t ≤ q, γ'' t = γ t) : γ'' '' Icc 0 q = γ '' Icc 0 q :=
  image_congr fun t ht => hag t ht.2

/-- **The tail of the completion lies in the unbounded domain of the stopped trace.** -/
theorem tail_mem (hAc : IsCompact (γ '' Icc 0 q)) (hc : IsProperCurve γ'') (hag : ∀ t ≤ q, γ'' t = γ t)
    (htail : ∀ t, q < t → γ'' t ∈ H) {t : ℝ≥0} (ht : q < t) : γ'' t ∈ H \ fillH (γ '' Icc 0 q) := by
  set X := γ'' '' Ioi q with hX
  have hXpc : IsPreconnected X := isPreconnected_Ioi.image _ hc.1.continuousOn
  have hXu : ¬ IsBounded X := by
    intro hb
    obtain ⟨R, hR⟩ := hb.exists_norm_le
    obtain ⟨T, hT⟩ := eventually_atTop.1 (Filter.tendsto_atTop.1 hc.2.2.2 (R + 1))
    have h1 := hT (max T (q + 1)) (le_max_left _ _)
    have h2 := hR _ ⟨max T (q + 1), lt_of_lt_of_le (lt_add_one q) (le_max_right _ _), rfl⟩
    linarith
  have hXA : X ⊆ H \ γ '' Icc 0 q := by
    rintro _ ⟨u, hu, rfl⟩
    refine ⟨htail u hu, ?_⟩
    rintro ⟨v, hv, hvu⟩
    rw [← hag v hv.2] at hvu
    have := hc.2.1 hvu
    exact absurd (this ▸ hv.2) (not_le.2 (show q < u from hu))
  exact subset_H_diff_fillH_of_not_isBounded hAc.isClosed hXpc hXu hXA ⟨t, ht, rfl⟩

theorem tail_ne_zero_of_maps (hch : IsChart γ q f Φ) (hAc : IsCompact (γ '' Icc 0 q)) (hc : IsProperCurve γ'')
    (hag : ∀ t ≤ q, γ'' t = γ t) (htail : ∀ t, q < t → γ'' t ∈ H) {t : ℝ} (ht : 0 < t) :
    futureChartArc f γ'' q t ∈ H := by
  rw [futureChartArc_of_pos ht]
  refine hch.maps (tail_mem hAc hc hag htail ?_)
  exact lt_add_of_pos_right q (Real.toNNReal_pos.2 ht)

/-- **The chart image of the tail is a simple proper arc of `ℍ` from `0`.** -/
theorem isProperArc_futureChartArc (hch : IsChart γ q f Φ) (hAc : IsCompact (γ '' Icc 0 q)) (htip : γ q ∈ H)
    (hc : IsProperCurve γ'') (hag : ∀ t ≤ q, γ'' t = γ t) (htail : ∀ t, q < t → γ'' t ∈ H) :
    WangWu.IsProperArc (futureChartArc f γ'' q) := by
  set D := H \ fillH (γ '' Icc 0 q) with hD
  have hDo : IsOpen D := isOpen_H_diff_fillH hAc.isBounded
  set τ : ℝ → ℂ := fun t => γ'' (q + t.toNNReal) with hτ
  have hτc : Continuous τ := hc.1.comp (continuous_const.add continuous_real_toNNReal)
  have hτD : ∀ t : ℝ, 0 < t → τ t ∈ D := fun t ht =>
    tail_mem hAc hc hag htail (lt_add_of_pos_right q (Real.toNNReal_pos.2 ht))
  have hτ0 : τ 0 = γ q := by simp [hτ, hag q le_rfl]
  have heq : ∀ t : ℝ, 0 < t → futureChartArc f γ'' q t = f (τ t) := fun t ht => futureChartArc_of_pos ht
  refine ⟨?_, ?_, futureChartArc_of_nonpos le_rfl, fun t ht => tail_ne_zero_of_maps hch hAc hc hag htail ht, ?_⟩
  · intro t ht
    rcases eq_or_lt_of_le (mem_Ici.1 ht) with h0 | hpos
    · subst h0
      rw [← continuousWithinAt_Ioi_iff_Ici]
      show Tendsto _ (𝓝[>] 0) (𝓝 (futureChartArc f γ'' q 0))
      rw [futureChartArc_of_nonpos le_rfl]
      have hτt : Tendsto τ (𝓝[>] 0) (𝓝[D] (γ q)) := by
        refine tendsto_nhdsWithin_iff.2 ⟨?_, eventually_nhdsWithin_of_forall fun t ht => hτD t ht⟩
        rw [← hτ0]
        exact hτc.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
      exact ((hch.tendsto_tip htip).comp hτt).congr'
        (eventually_nhdsWithin_of_forall fun t ht => (heq t ht).symm)
    · have hfat : ContinuousAt (fun t => f (τ t)) t :=
        ((hch.cont _ (hτD t hpos)).continuousAt (hDo.mem_nhds (hτD t hpos))).comp hτc.continuousAt
      exact (hfat.congr (eventually_of_mem (isOpen_Ioi.mem_nhds hpos) fun u hu => (heq u hu).symm)
        ).continuousWithinAt
  · intro t ht u hu htu
    rcases eq_or_lt_of_le (mem_Ici.1 ht) with h0 | htp <;> rcases eq_or_lt_of_le (mem_Ici.1 hu) with h0' | hup
    · rw [← h0, ← h0']
    · subst h0
      have := tail_ne_zero_of_maps hch hAc hc hag htail hup
      rw [← htu, futureChartArc_of_nonpos le_rfl] at this
      exact absurd this (by simp [QuantumZipper.H])
    · subst h0'
      have := tail_ne_zero_of_maps hch hAc hc hag htail htp
      rw [htu, futureChartArc_of_nonpos le_rfl] at this
      exact absurd this (by simp [QuantumZipper.H])
    · rw [heq t htp, heq u hup] at htu
      have h1 := hc.2.1 (hch.injOn (hτD t htp) (hτD u hup) htu)
      have h2 : t.toNNReal = u.toNNReal := add_left_cancel h1
      have := congrArg (fun r : ℝ≥0 => (r : ℝ)) h2
      simp only [Real.coe_toNNReal _ htp.le, Real.coe_toNNReal _ hup.le] at this
      exact this
  · obtain ⟨C, hC⟩ := hch.bdd
    rw [Filter.tendsto_atTop]
    intro R
    have hτinf : Tendsto (fun t => ‖τ t‖) atTop atTop :=
      hc.2.2.2.comp (tendsto_atTop_mono (fun t => le_add_self) tendsto_real_toNNReal_atTop)
    filter_upwards [Filter.tendsto_atTop.1 hτinf (R + C), eventually_gt_atTop (0 : ℝ)] with t ht htp
    rw [heq t htp]
    have h1 := hC _ (hτD t htp)
    have h2 : ‖τ t‖ ≤ ‖f (τ t)‖ + ‖f (τ t) - τ t‖ := by
      have := norm_sub_le (f (τ t)) (f (τ t) - τ t)
      rwa [sub_sub_cancel] at this
    linarith

/-- `Φ` maps the complement of the chart arc into the complement of the closed completion. -/
theorem inv_notMem_seedRayClosure (hch : IsChart γ q f Φ) (h0 : (γ'' 0).im = 0)
    (hag : ∀ t ≤ q, γ'' t = γ t) {w : ℂ} (hwH : w ∈ H)
    (hwA : w ∉ WangWu.arcRange (futureChartArc f γ'' q)) : Φ w ∉ seedRayClosure γ'' := by
  have hwD := hch.inv_mem hwH
  rintro (⟨t, ht⟩ | ⟨-, him⟩)
  · by_cases htq : t ≤ q
    · rw [hag t htq] at ht
      exact hwD.2 ⟨hwD.1, Or.inl (subset_closure ⟨t, ⟨zero_le, htq⟩, ht⟩)⟩
    · have htq' : q < t := not_le.1 htq
      refine hwA ⟨(t : ℝ) - q, ?_, ?_⟩
      · exact mem_Ici.2 (sub_nonneg.2 (by exact_mod_cast htq'.le))
      · have hpos : (0 : ℝ) < (t : ℝ) - q := sub_pos.2 (by exact_mod_cast htq')
        rw [futureChartArc_of_pos hpos]
        have ht' : q + ((t : ℝ) - q).toNNReal = t := by
          rw [← NNReal.coe_inj, NNReal.coe_add, Real.coe_toNNReal _ hpos.le]; ring
        rw [ht', ht, hch.f_inv w hwH]
  · have : (Φ w).im ≤ 0 := h0 ▸ him
    exact absurd hwD.1 (not_lt.2 this)

/-- The real points of the completion are those of the stopped trace. -/
theorem notMem_range_of_norm (hag : ∀ t ≤ q, γ'' t = γ t)
    (htail : ∀ t, q < t → γ'' t ∈ H) {M : ℝ} (hM : ∀ z ∈ γ '' Icc 0 q, ‖z‖ ≤ M) {x : ℝ} (hx : M < |x|) :
    (x : ℂ) ∉ range γ'' := by
  rintro ⟨t, ht⟩
  by_cases htq : t ≤ q
  · have := hM _ ⟨t, ⟨zero_le, htq⟩, (hag t htq) ▸ ht⟩
    rw [Complex.norm_real, Real.norm_eq_abs] at this
    linarith
  · have := htail t (not_le.1 htq)
    rw [ht] at this
    exact absurd this (by simp [QuantumZipper.H])

/-- **The chart maps the right side of the completion, off the hull, into the right side of the chart arc.** -/
theorem mem_rightSideOf_of_mem_rightSide (hch : IsChart γ q f Φ) (hAc : IsCompact (γ '' Icc 0 q))
    (htip : γ q ∈ H) (hc : IsProperCurve γ'') (h0 : (γ'' 0).im = 0) (hag : ∀ t ≤ q, γ'' t = γ t)
    (htail : ∀ t, q < t → γ'' t ∈ H) {z : ℂ} (hzR : z ∈ rightSide γ'')
    (hzD : z ∈ H \ fillH (γ '' Icc 0 q)) :
    f z ∈ rightSideOf (WangWu.arcRange (futureChartArc f γ'' q)) := by
  set A := γ '' Icc 0 q with hAdef
  set D := H \ fillH A with hD
  set γs := futureChartArc f γ'' q with hγs
  have hpa := isProperArc_futureChartArc hch hAc htip hc hag htail
  have hfzH : f z ∈ H := hch.maps hzD
  have hzr : z ∉ range γ'' := fun h => (connectedComponentIn_subset _ _ hzR) (Or.inl h)
  have hfzA : f z ∉ WangWu.arcRange γs := by
    rintro ⟨t, ht, hte⟩
    rcases eq_or_lt_of_le (mem_Ici.1 ht) with h0' | htp
    · rw [← h0', hγs, futureChartArc_of_nonpos le_rfl] at hte
      rw [← hte] at hfzH
      exact absurd hfzH (by simp [QuantumZipper.H])
    · rw [hγs, futureChartArc_of_pos htp] at hte
      have hm := tail_mem hAc hc hag htail (lt_add_of_pos_right q (Real.toNNReal_pos.2 htp))
      exact hzr ⟨_, hch.injOn hm hzD hte⟩
  rcases hpa.mem_leftSideOf_or_mem_rightSideOf hfzH hfzA with hL | hR
  · exfalso
    set L := leftSideOf (WangWu.arcRange γs) with hLdef
    have hLH : L ⊆ H := fun w hw => hw.1.1
    have hΦpc : IsPreconnected (Φ '' L) :=
      hpa.isPreconnected_leftSideOf.image Φ (hch.inv_cont.mono fun w hw => H_subset_Hbar (hLH hw))
    have hΦS : Φ '' L ⊆ (seedRayClosure γ'')ᶜ := by
      rintro _ ⟨w, hw, rfl⟩
      exact inv_notMem_seedRayClosure hch h0 hag (hLH hw) hw.1.2
    have hzmem : z ∈ Φ '' L := ⟨f z, hL, hch.inv_f z hzD⟩
    have hsub : Φ '' L ⊆ rightSide γ'' := by
      have := hΦpc.subset_connectedComponentIn hzmem hΦS
      unfold rightSide
      rwa [connectedComponentIn_eq hzR]
    -- a far-left real point
    obtain ⟨M, hM⟩ := hAc.isBounded.exists_norm_le
    obtain ⟨C, hC⟩ := hch.bdd
    set x₀ : ℝ := -(|M| + |C| + 1) with hx₀
    have hx₀M : M < |x₀| := by
      rw [hx₀, abs_neg, abs_of_pos (by positivity)]; linarith [le_abs_self M, abs_nonneg C]
    have hX : {w : ℂ | 0 < w.im ∧ w.re < -|M|} ⊆ D := by
      refine subset_H_diff_fillH_of_not_isBounded hAc.isClosed ?_ ?_ ?_
      · refine Convex.isPreconnected ?_
        exact (convex_halfSpace_gt (f := fun w : ℂ => w.im) Complex.imLm.isLinear 0).inter
          (convex_halfSpace_lt (f := fun w : ℂ => w.re) Complex.reLm.isLinear _)
      · intro hb
        obtain ⟨R, hR⟩ := hb.exists_norm_le
        have hmem : ((-(|M| + |R| + 1) : ℝ) : ℂ) + I ∈ {w : ℂ | 0 < w.im ∧ w.re < -|M|} := by
          refine ⟨by simp, ?_⟩
          simp only [add_re, ofReal_re, I_re, add_zero]; linarith [abs_nonneg R]
        have h1 := hR _ hmem
        have h2 := Complex.abs_re_le_norm (((-(|M| + |R| + 1) : ℝ) : ℂ) + I)
        simp only [add_re, ofReal_re, I_re, add_zero] at h2
        rw [abs_of_neg (by linarith [abs_nonneg M, abs_nonneg R])] at h2
        linarith [le_abs_self R, abs_nonneg M]
      · rintro w ⟨hw1, hw2⟩
        refine ⟨hw1, fun hwA => ?_⟩
        have h1 := hM w hwA
        have h2 := Complex.abs_re_le_norm w
        rw [abs_of_neg (by linarith [abs_nonneg M])] at h2
        linarith [le_abs_self M]
    have hfree : IsFreeAt A (x₀ : ℂ) := by
      refine ⟨1, one_pos, fun w hw => hX ⟨hw.2, ?_⟩⟩
      have h1 : |w.re - x₀| < 1 := by
        have := Complex.abs_re_le_norm (w - x₀)
        rw [sub_re, ofReal_re] at this
        have h2 : ‖w - x₀‖ < 1 := by rw [← dist_eq_norm]; exact hw.1
        linarith
      rw [hx₀] at h1
      linarith [(abs_lt.1 h1).2, abs_nonneg C]
    obtain ⟨c, hfc, -, -⟩ := hch.free_real x₀ hfree
    have hneb : (𝓝[H] (x₀ : ℂ)).NeBot := by
      rw [← mem_closure_iff_nhdsWithin_neBot, closure_H]
      show (0 : ℝ) ≤ ((x₀ : ℝ) : ℂ).im
      simp
    obtain ⟨ε₁, hε₁, hε₁D⟩ := hfree
    have hDev : ∀ᶠ w in 𝓝[H] (x₀ : ℂ), w ∈ D := by
      filter_upwards [self_mem_nhdsWithin, nhdsWithin_le_nhds (ball_mem_nhds _ hε₁)] with w hw hwb
      exact hε₁D ⟨hwb, hw⟩
    have hc0 : c < 0 := by
      have hlim : Tendsto (fun w => f w - w) (𝓝[H] (x₀ : ℂ)) (𝓝 ((c : ℂ) - x₀)) :=
        hfc.sub (tendsto_id.mono_left nhdsWithin_le_nhds)
      have hle : ‖(c : ℂ) - x₀‖ ≤ C :=
        le_of_tendsto hlim.norm (hDev.mono fun w hw => hC w hw)
      rw [← ofReal_sub, Complex.norm_real, Real.norm_eq_abs] at hle
      have := (abs_le.1 hle).2
      rw [hx₀] at this
      linarith [le_abs_self C, abs_nonneg M]
    obtain ⟨δ, hδ, hδL⟩ := hpa.exists_ball_inter_H_subset_leftSideOf hc0
    have hx₀S : (x₀ : ℂ) ∉ seedRayClosure γ'' := by
      rintro (h | ⟨hre, -⟩)
      · exact notMem_range_of_norm hag htail hM hx₀M h
      · have h1 := hM _ ⟨0, ⟨le_rfl, zero_le⟩, rfl⟩
        rw [← hag 0 zero_le] at h1
        have h2 := Complex.abs_re_le_norm (γ'' 0)
        rw [ofReal_re] at hre
        rw [← hre, hx₀, abs_neg, abs_of_pos (by positivity)] at h2
        linarith [le_abs_self M, abs_nonneg C]
    have hx₀re : x₀ < (γ'' 0).re := by
      have h1 := hM _ ⟨0, ⟨le_rfl, zero_le⟩, rfl⟩
      rw [← hag 0 zero_le] at h1
      have h2 := Complex.abs_re_le_norm (γ'' 0)
      rw [hx₀]
      linarith [neg_abs_le (γ'' 0).re, le_abs_self M, abs_nonneg C]
    have hx₀L : (x₀ : ℂ) ∈ leftSide γ'' := ofReal_mem_leftSide hc.2.2.1 h0 hx₀re hx₀S
    obtain ⟨ε, hε, hεL⟩ := Metric.isOpen_iff.1 (isOpen_leftSide hc) _ hx₀L
    have hev : ∀ᶠ w in 𝓝[H] (x₀ : ℂ), w ∈ ball (x₀ : ℂ) ε ∧ w ∈ D ∧ f w ∈ ball (c : ℂ) δ := by
      filter_upwards [nhdsWithin_le_nhds (ball_mem_nhds _ hε), hDev, hfc (ball_mem_nhds _ hδ)] with w h1 h2 h3
      exact ⟨h1, h2, h3⟩
    obtain ⟨w, hwb, hwD, hfw⟩ := hev.exists
    have hwR : w ∈ rightSide γ'' := hsub ⟨f w, hδL ⟨hfw, hch.maps hwD⟩, hch.inv_f w hwD⟩
    exact Set.disjoint_left.1 (disjoint_leftSide_rightSide hc h0) (hεL hwb) hwR
  · exact hR

/-- **Along an approach from the right side of the completion, the chart has a positive limit.** -/
theorem exists_pos_tendsto_of_rightSide (hch : IsChart γ q f Φ) (hAc : IsCompact (γ '' Icc 0 q))
    (htip : γ q ∈ H) (hc : IsProperCurve γ'') (h0 : (γ'' 0).im = 0) (hag : ∀ t ≤ q, γ'' t = γ t)
    (htail : ∀ t, q < t → γ'' t ∈ H) {s : ℝ≥0} (hsq : s < q) (hsH : γ s ∈ H) (U : Ultrafilter ℂ)
    (hU : (U : Filter ℂ) ≤ 𝓝[rightSide γ'' ∩ (H \ fillH (γ '' Icc 0 q))] (γ s)) :
    ∃ y : ℝ, 0 < y ∧ Tendsto f U (𝓝 (y : ℂ)) := by
  have hpa := isProperArc_futureChartArc hch hAc htip hc hag htail
  have hUD : (U : Filter ℂ) ≤ 𝓝[H \ fillH (γ '' Icc 0 q)] (γ s) := hU.trans (nhdsWithin_mono _ inter_subset_right)
  obtain ⟨y₀, hy₀H, hfy, hΦy⟩ := hch.cluster U (γ s) hUD
  have hsK : γ s ∈ fillH (γ '' Icc 0 q) := mem_fillH_of_mem_H hsq.le hsH
  have hy₀im : y₀.im = 0 := le_antisymm (not_lt.1 fun hpos => (hch.inv_mem hpos).2 (hΦy ▸ hsK)) hy₀H
  set y := y₀.re with hydef
  have hy₀eq : y₀ = (y : ℂ) := Complex.ext (by simp [hydef]) (by simp [hy₀im])
  rw [hy₀eq] at hfy hΦy
  have hyne : y ≠ 0 := by
    intro hy0
    rw [hy0, ofReal_zero, hch.tip, ← hag q le_rfl, ← hag s hsq.le] at hΦy
    exact absurd (hc.2.1 hΦy) (ne_of_gt hsq)
  have hev : ∀ᶠ z in (U : Filter ℂ), f z ∈ rightSideOf (WangWu.arcRange (futureChartArc f γ'' q)) :=
    Filter.mem_of_superset (hU self_mem_nhdsWithin) fun z hz =>
      mem_rightSideOf_of_mem_rightSide hch hAc htip hc h0 hag htail hz.1 hz.2
  have hcl := mem_closure_of_tendsto hfy hev
  refine ⟨y, lt_of_le_of_ne (not_lt.1 fun hneg => hpa.notMem_closure_rightSideOf_of_neg hneg hcl) hyne.symm, hfy⟩

/-- **The right side of the completion, off the hull, lies in the unbounded domain of every closed set missing it.** -/
theorem subset_H_diff_fillH_of_rightSide (hch : IsChart γ q f Φ) (hAc : IsCompact (γ '' Icc 0 q))
    (htip : γ q ∈ H) (hc : IsProperCurve γ'') (h0 : (γ'' 0).im = 0) (hag : ∀ t ≤ q, γ'' t = γ t)
    (htail : ∀ t, q < t → γ'' t ∈ H) {Γ : Set ℂ} (hΓ : IsClosed Γ)
    (hΓR : ∀ w ∈ Γ, w ∈ rightSide γ'' → w ∈ H \ fillH (γ '' Icc 0 q) → False) :
    rightSide γ'' ∩ (H \ fillH (γ '' Icc 0 q)) ⊆ H \ fillH Γ := by
  rintro z ⟨hzR, hzD⟩
  set Rs := rightSideOf (WangWu.arcRange (futureChartArc f γ'' q)) with hRs
  have hpa := isProperArc_futureChartArc hch hAc htip hc hag htail
  have hRsH : Rs ⊆ H := fun w hw => hw.1.1
  set X := Φ '' Rs with hXdef
  have hXpc : IsPreconnected X :=
    hpa.isPreconnected_rightSideOf.image Φ (hch.inv_cont.mono fun w hw => H_subset_Hbar (hRsH hw))
  have hXS : X ⊆ (seedRayClosure γ'')ᶜ := by
    rintro _ ⟨w, hw, rfl⟩
    exact inv_notMem_seedRayClosure hch h0 hag (hRsH hw) hw.1.2
  have hzX : z ∈ X := ⟨f z, mem_rightSideOf_of_mem_rightSide hch hAc htip hc h0 hag htail hzR hzD,
    hch.inv_f z hzD⟩
  have hXR : X ⊆ rightSide γ'' := by
    have := hXpc.subset_connectedComponentIn hzX hXS
    unfold rightSide
    rwa [connectedComponentIn_eq hzR]
  have hXD : X ⊆ H \ fillH (γ '' Icc 0 q) := by
    rintro _ ⟨w, hw, rfl⟩
    exact hch.inv_mem (hRsH hw)
  have hXΓ : X ⊆ H \ Γ := fun w hw => ⟨(hXD hw).1, fun hwΓ => hΓR w hwΓ (hXR hw) (hXD hw)⟩
  obtain ⟨C, hC⟩ := hch.bdd
  have hXu : ¬ IsBounded X := by
    intro hb
    obtain ⟨R, hR⟩ := hb.exists_norm_le
    set x : ℝ := |R| + |C| + 1 with hx
    obtain ⟨r, hr, hrR⟩ := hpa.exists_ball_inter_H_subset_rightSideOf (show (0 : ℝ) < x by positivity)
    set w : ℂ := (x : ℂ) + ((r / 2 : ℝ) : ℂ) * I with hw
    have hwH : w ∈ H := by show 0 < w.im; simp [hw]; positivity
    have hwb : w ∈ ball (x : ℂ) r := by
      rw [mem_ball, dist_eq_norm, hw, add_sub_cancel_left, norm_mul, Complex.norm_I, mul_one,
        Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by positivity)]
      linarith
    have hwRs : w ∈ Rs := hrR ⟨hwb, hwH⟩
    have h1 := hR _ ⟨w, hwRs, rfl⟩
    have h2 := hC _ (hch.inv_mem hwH)
    rw [hch.f_inv w hwH] at h2
    have h3 : ‖w‖ ≤ ‖Φ w‖ + ‖w - Φ w‖ :=
      calc ‖w‖ = ‖Φ w + (w - Φ w)‖ := by congr 1; ring
        _ ≤ _ := norm_add_le _ _
    have h4 : x ≤ ‖w‖ := by
      have := Complex.abs_re_le_norm w
      simp only [hw, add_re, ofReal_re, mul_re, ofReal_im, I_re, mul_zero, I_im, mul_one, sub_zero,
        add_zero] at this
      exact (le_abs_self x).trans this
    linarith [le_abs_self R, le_abs_self C]
  exact subset_H_diff_fillH_of_not_isBounded hΓ hXpc hXu hXΓ hzX

end Centred

/-! ### Physical seeds -/

section Phys

/-- Translating a curve by a real number translates its right side. -/
theorem rightSide_add_real (γ : ℝ≥0 → ℂ) (x : ℝ) :
    rightSide (fun t => γ t + x) = (· + (x : ℂ)) '' rightSide γ := by
  set e := Homeomorph.addRight (x : ℂ) with he
  have hS : (e : ℂ → ℂ) '' seedRayClosure γ = seedRayClosure (fun t => γ t + x) :=
    (Supp10.seedRayClosure_add_real γ x).symm
  set p : ℂ := γ 0 + 1 - I with hp
  have hcompl : (e : ℂ → ℂ) '' (seedRayClosure γ)ᶜ = (seedRayClosure (fun t => γ t + x))ᶜ := by
    rw [← hS]; exact e.toEquiv.image_compl _
  have hep : e p = (fun t => γ t + (x : ℂ)) 0 + 1 - I := by
    simp only [he, Homeomorph.coe_addRight, hp]; ring
  unfold rightSide
  by_cases hpS : p ∈ (seedRayClosure γ)ᶜ
  · have h := e.image_connectedComponentIn hpS
    rw [hcompl, hep] at h
    exact h.symm
  · have hpS' : (fun t => γ t + (x : ℂ)) 0 + 1 - I ∉ (seedRayClosure (fun t => γ t + x))ᶜ := by
      rw [← hep, ← hcompl]
      rintro ⟨w, hw, hwp⟩
      exact hpS (e.injective hwp ▸ hw)
    rw [connectedComponentIn_eq_empty hpS', connectedComponentIn_eq_empty hpS, image_empty]

theorem rightSide_sub_real (γ : ℝ≥0 → ℂ) (x : ℝ) :
    rightSide (fun t => γ t - x) = (fun z : ℂ => z - (x : ℂ)) '' rightSide γ := by
  have e₁ : (fun t => γ t - (x : ℂ)) = fun t => γ t + ((-x : ℝ) : ℂ) := by funext t; push_cast; ring
  have e₂ : (fun z : ℂ => z - (x : ℂ)) = fun z => z + ((-x : ℝ) : ℂ) := by funext z; push_cast; ring
  rw [e₁, e₂]
  exact rightSide_add_real γ (-x)

theorem mem_rightSide_sub_iff (γ : ℝ≥0 → ℂ) (x : ℝ) (z : ℂ) :
    z - x ∈ rightSide (fun t => γ t - x) ↔ z ∈ rightSide γ := by
  rw [rightSide_sub_real]
  constructor
  · rintro ⟨w, hw, hwz⟩
    rwa [sub_left_injective hwz] at hw
  · intro hz
    exact ⟨z, hz, rfl⟩

theorem mem_H_diff_fillH_sub_iff (Γ : Set ℂ) (x : ℝ) (z : ℂ) :
    z - x ∈ H \ fillH ((fun w => w - x) '' Γ) ↔ z ∈ H \ fillH Γ := by
  have e₂ : (fun z : ℂ => z - (x : ℂ)) = fun z => z + ((-x : ℝ) : ℂ) := by funext z; push_cast; ring
  rw [e₂, fillH_image_add, Set.mem_sdiff, Set.mem_sdiff]
  have hH : z + ((-x : ℝ) : ℂ) ∈ H ↔ z ∈ H := transR_mem_H (-x) z
  have hz : z - x = z + ((-x : ℝ) : ℂ) := by push_cast; ring
  rw [hz, hH]
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨h1, fun h => h2 ⟨z, h, rfl⟩⟩
  · rintro ⟨h1, h2⟩
    refine ⟨h1, ?_⟩
    rintro ⟨w, hw, hwz⟩
    have : w = z := add_right_cancel hwz
    exact h2 (this ▸ hw)

variable {α α'' : ℝ≥0 → ℂ} {ζ : ℝ≥0∞} {x : ℝ} {W : ℝ≥0 → ℝ} {q : ℝ≥0}

/-- The centred data of a physical trace and completion satisfy the hypotheses of the centred lemmas. -/
theorem centred_data (hg : IsGeneratingTrace W ζ (fun t => α t - x)) (hWc : ContinuousOn W {s | (s : ℝ≥0∞) < ζ})
    (hW0 : W 0 = 0) (hinj : InjOn α {t | (t : ℝ≥0∞) ≤ ζ}) (hq : (q : ℝ≥0∞) < ζ) (hq0 : 0 < q)
    (hc : IsProperCurve α'') (h0 : (α'' 0).im = 0) :
    IsChart (fun t => α t - x) q (QuantumZipper.fwdMap (fun r : ℝ => W r.toNNReal) q)
        (extendFrom H (QuantumZipper.fwdMapInv (fun r : ℝ => W r.toNNReal) q)) ∧
      IsCompact ((fun t => α t - x) '' Icc 0 q) ∧ IsProperCurve (fun t => α'' t - x) ∧
      ((fun t => α'' t - (x : ℂ)) 0).im = 0 := by
  have hinj' : InjOn (fun t => α t - x) {t | (t : ℝ≥0∞) ≤ ζ} := fun a ha b hb hab =>
    hinj ha hb (sub_left_injective hab)
  refine ⟨isChart hg hWc hW0 hinj' hq hq0, isCompact_Icc.image_of_continuousOn
    (hg.2.1.mono fun t ht => (ENNReal.coe_le_coe.2 ht.2).trans hq.le), ⟨hc.1.sub continuous_const,
    fun a b hab => hc.2.1 (sub_left_injective hab), fun t => by simpa using hc.2.2.1 t, ?_⟩, by simpa using h0⟩
  refine tendsto_atTop_mono (fun t => ?_) (tendsto_atTop_add_const_right _ (-|x|) hc.2.2.2)
  have := norm_sub_norm_le (α'' t) (x : ℂ)
  rw [Complex.norm_real, Real.norm_eq_abs] at this
  linarith

/-- **The positive chart limit at a physical seed** (`exists_pos_tendsto_of_rightSide` translated by the seed). -/
theorem exists_pos_tendsto_of_rightSide_phys (hg : IsGeneratingTrace W ζ (fun t => α t - x))
    (hWc : ContinuousOn W {s | (s : ℝ≥0∞) < ζ}) (hW0 : W 0 = 0) (hinj : InjOn α {t | (t : ℝ≥0∞) ≤ ζ})
    (hq : (q : ℝ≥0∞) < ζ) (htip : α q ∈ H) (hc : IsProperCurve α'') (h0 : (α'' 0).im = 0)
    (hag : ∀ t ≤ q, α'' t = α t) (htail : ∀ t, q < t → α'' t ∈ H) {s : ℝ≥0} (hsq : s < q) (hsH : α s ∈ H)
    (U : Ultrafilter ℂ) (hU : (U : Filter ℂ) ≤ 𝓝[rightSide α'' ∩ (H \ fillH (α '' Icc 0 q))] (α s)) :
    ∃ y : ℝ, 0 < y ∧
      Tendsto (fun z => QuantumZipper.fwdMap (fun r : ℝ => W r.toNNReal) q (z - x)) U (𝓝 (y : ℂ)) := by
  have hq0 : 0 < q := lt_of_le_of_lt zero_le hsq
  obtain ⟨hch, hAc, hc', h0'⟩ := centred_data (α'' := α'') hg hWc hW0 hinj hq hq0 hc h0
  have hH : ∀ z : ℂ, z - x ∈ H ↔ z ∈ H := fun z => by
    show 0 < (z - (x : ℂ)).im ↔ 0 < z.im
    simp
  have hU' : ((U.map (fun z => z - (x : ℂ)) : Ultrafilter ℂ) : Filter ℂ) ≤
      𝓝[rightSide (fun t => α'' t - x) ∩ (H \ fillH ((fun t => α t - x) '' Icc 0 q))] (α s - x) := by
    rw [Ultrafilter.coe_map]
    refine (map_mono hU).trans (tendsto_nhdsWithin_iff.2 ⟨?_, eventually_nhdsWithin_of_forall fun z hz => ?_⟩)
    · exact ((continuous_sub_right (x : ℂ)).tendsto _).mono_left nhdsWithin_le_nhds
    · exact ⟨(mem_rightSide_sub_iff α'' x z).2 hz.1, (mem_H_diff_fillH_phys_iff x q z).1 hz.2⟩
  obtain ⟨y, hy, hlim⟩ := exists_pos_tendsto_of_rightSide hch hAc ((hH _).2 htip) hc' h0'
    (fun t ht => by simp only [hag t ht]) (fun t ht => (hH _).2 (htail t ht)) hsq ((hH _).2 hsH) _ hU'
  refine ⟨y, hy, ?_⟩
  rw [Ultrafilter.coe_map] at hlim
  exact hlim.comp tendsto_map

/-- **The right side of a physical completion, off the hull, lies in the unbounded domain of every closed set
missing it.** -/
theorem subset_H_diff_fillH_of_rightSide_phys (hg : IsGeneratingTrace W ζ (fun t => α t - x))
    (hWc : ContinuousOn W {s | (s : ℝ≥0∞) < ζ}) (hW0 : W 0 = 0) (hinj : InjOn α {t | (t : ℝ≥0∞) ≤ ζ})
    (hq : (q : ℝ≥0∞) < ζ) (hq0 : 0 < q) (htip : α q ∈ H) (hc : IsProperCurve α'') (h0 : (α'' 0).im = 0)
    (hag : ∀ t ≤ q, α'' t = α t) (htail : ∀ t, q < t → α'' t ∈ H) {Γ : Set ℂ} (hΓ : IsClosed Γ)
    (hΓR : ∀ w ∈ Γ, w ∈ rightSide α'' → w ∈ H \ fillH (α '' Icc 0 q) → False) :
    rightSide α'' ∩ (H \ fillH (α '' Icc 0 q)) ⊆ H \ fillH Γ := by
  obtain ⟨hch, hAc, hc', h0'⟩ := centred_data (α'' := α'') hg hWc hW0 hinj hq hq0 hc h0
  have hH : ∀ z : ℂ, z - x ∈ H ↔ z ∈ H := fun z => by
    show 0 < (z - (x : ℂ)).im ↔ 0 < z.im
    simp
  set e : ℂ → ℂ := fun w => w - x with he
  have heq : e = transR (-x) := by funext w; simp [he, transR_apply, sub_eq_add_neg]
  have hΓ' : IsClosed (e '' Γ) := by rw [heq]; exact (transR (-x)).isClosedMap _ hΓ
  rintro z ⟨hzR, hzD⟩
  have hsub := subset_H_diff_fillH_of_rightSide hch hAc ((hH _).2 htip) hc' h0'
    (fun t ht => by simp only [hag t ht]) (fun t ht => (hH _).2 (htail t ht)) hΓ' ?_
    ⟨(mem_rightSide_sub_iff α'' x z).2 hzR, (mem_H_diff_fillH_phys_iff x q z).1 hzD⟩
  · exact (mem_H_diff_fillH_sub_iff Γ x z).1 hsub
  · rintro _ ⟨w, hw, rfl⟩ hwR hwD
    exact hΓR w hw ((mem_rightSide_sub_iff α'' x w).1 hwR) ((mem_H_diff_fillH_phys_iff x q w).2 hwD)

end Phys

end W0b

end Supp9

end InteractingSLE
