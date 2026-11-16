/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.RealContact.TermEntryChart
import InteractingSLE.Spec.Supplement.S9BOrder
import InteractingSLE.Spec.Supplement.S9DActivity

/-!
# The explorer and a completed retained path: sides and activity (builder frame)

Packet PROVE-RC-TERM, second run (ruling R124). In the builder frame the explorer `β` starts at `0` and the completed
retained path `Q` starts at a real point `d ≥ 0`, ends at a real point `E`, and has all its real points in `[0, E]`.
W5 (the sealed `IsFlowLine.stays_right_of_lt`) gives ordered proper completions of `(Q([0, c]), β([0, a]))` only for
`c` strictly before the horizon `T`. This file derives, for an explorer prefix `β([0, a])` without a positive-time
contact with `Q([0, T])`:

* `rayQ Q T E`: the completion of `Q` by the real ray `[E, ∞)`; **`IsRetPath.isProperCompletion_rayQ`**;
* **`exists_completion_early`** (no real point of the prefix at or right of `E`): a proper completion `β'` of the
  prefix in the closed left side of `rayQ` (the transfer lemma
  `Supp9B.exists_isProperCompletion_subset_closedLeftSide`), hence `Q([0, T]) ⊆ closedRightSide β'` (duality);
* **`subset_closedRightSide_late`** (the prefix has a real point right of `E`): `Q([0, T])` lies in the closed right
  side of every proper completion of the prefix whose new part is off the prefix's filled hull (the path is trapped
  by the prefix; `Supp9B.mem_closedRightSide_of_avoid` for every `c < T`; closed sides are closed);
* **`isFreeAt_explorer`**: every point `β t`, `0 < t ≤ a`, is free for `Q([0, T])` — the explorer stays in the closure
  of the unbounded component of `ℍ \ Q([0, T])`. For a common seed (`d = 0`) and an early prefix this is the label
  argument: the left side of `rayQ`, intersected with `ℍ̄`, consists of free points.

Deterministic; R48-neutral (W5 enters as a hypothesis about the two prefixes).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Filter Topology Metric Complex Bornology
open scoped NNReal ENNReal
open QuantumZipper (H Hbar)

namespace InteractingSLE.RealContact

namespace Term

open Supp9B HalfPlaneSep

/-! ### Labels and closures of filled hulls -/

theorem isFreeAt_of_notMem_closure {F : Set ℂ} {z : ℂ} (h : z ∉ closure (fillH F)) : IsFreeAt F z := by
  obtain ⟨ε, hε, hd⟩ := Metric.mem_nhds_iff.1 (isClosed_closure.isOpen_compl.mem_nhds h)
  exact ⟨ε, hε, fun w hw => ⟨hw.2, fun hwF => hd hw.1 (subset_closure hwF)⟩⟩

theorem notMem_closure_of_isFreeAt {F : Set ℂ} {z : ℂ} (h : IsFreeAt F z) : z ∉ closure (fillH F) := by
  obtain ⟨ε, hε, hsub⟩ := h
  intro hz
  obtain ⟨w, hw, hwz⟩ := Metric.mem_closure_iff.1 hz ε hε
  have hwH : w ∈ H := hw.1
  exact (hsub ⟨by rwa [mem_ball, dist_comm], hwH⟩).2 hw

theorem mem_fillH_of_isTrappedAt {F : Set ℂ} {z : ℂ} (h : IsTrappedAt F z) (hz : z ∈ H) : z ∈ fillH F := by
  by_contra hn
  exact h.notMem ⟨hz, hn⟩

/-- The image of a compact interval of `ℝ≥0` as the image of a real interval. -/
theorem image_Icc_nnreal (γ : ℝ≥0 → ℂ) (a : ℝ≥0) :
    (fun s : ℝ => γ s.toNNReal) '' Icc 0 (a : ℝ) = γ '' Icc 0 a := by
  ext z
  constructor
  · rintro ⟨s, hs, rfl⟩
    exact ⟨s.toNNReal, ⟨zero_le, Real.toNNReal_le_iff_le_coe.2 hs.2⟩, rfl⟩
  · rintro ⟨t, ht, rfl⟩
    exact ⟨(t : ℝ), ⟨t.coe_nonneg, NNReal.coe_le_coe.2 ht.2⟩, by simp only [Real.toNNReal_coe]⟩

/-- A real point strictly between two real points of a curve in `ℍ̄` and off the curve is in the closure of its
filled hull. -/
theorem mem_closure_fillH_between {γ : ℝ≥0 → ℂ} {a : ℝ≥0} (hc : ContinuousOn γ (Icc 0 a))
    (hH : ∀ t ≤ a, 0 ≤ (γ t).im) {u₁ u₂ : ℝ≥0} (hu₁ : u₁ ≤ a) (hu₂ : u₂ ≤ a) (h1 : (γ u₁).im = 0)
    (h2 : (γ u₂).im = 0) {r : ℝ} (hr1 : (γ u₁).re < r) (hr2 : r < (γ u₂).re)
    (hrP : (r : ℂ) ∉ γ '' Icc 0 a) : (r : ℂ) ∈ closure (fillH (γ '' Icc 0 a)) := by
  rw [← image_Icc_nnreal] at hrP ⊢
  have hc' : ContinuousOn (fun s : ℝ => γ s.toNNReal) (Icc 0 (a : ℝ)) :=
    hc.comp continuous_real_toNNReal.continuousOn fun s hs =>
      ⟨zero_le, Real.toNNReal_le_iff_le_coe.2 hs.2⟩
  have hH' : MapsTo (fun s : ℝ => γ s.toNNReal) (Icc 0 (a : ℝ)) Hbar := fun s hs =>
    hH _ (Real.toNNReal_le_iff_le_coe.2 hs.2)
  exact YuanCharacterisation.mem_closure_fillH_of_lt_of_lt hc' hH'
    (u₁ := (u₁ : ℝ)) (u₂ := (u₂ : ℝ)) ⟨u₁.coe_nonneg, NNReal.coe_le_coe.2 hu₁⟩
    ⟨u₂.coe_nonneg, NNReal.coe_le_coe.2 hu₂⟩ (by simpa only [Real.toNNReal_coe] using h1)
    (by simpa only [Real.toNNReal_coe] using h2) (by simpa only [Real.toNNReal_coe] using hr1)
    (by simpa only [Real.toNNReal_coe] using hr2) hrP

/-- The closed right side of a proper curve from a real seed is the complement of its left side. -/
theorem closedRightSide_eq_compl {γ : ℝ≥0 → ℂ} (hγ : IsProperCurve γ) (h0 : (γ 0).im = 0) :
    closedRightSide γ = (leftSide γ)ᶜ := by
  have hc := compl_seedRayClosure_eq hγ h0
  have hd := disjoint_leftSide_rightSide hγ h0
  ext z
  constructor
  · rintro (hR | hS) hL
    · exact Set.disjoint_left.1 hd hL hR
    · exact leftSide_subset_compl γ hL hS
  · intro hL
    by_cases hS : z ∈ seedRayClosure γ
    · exact Or.inr hS
    · have : z ∈ leftSide γ ∪ rightSide γ := hc ▸ hS
      exact Or.inl (this.resolve_left hL)

theorem isClosed_closedRightSide {γ : ℝ≥0 → ℂ} (hγ : IsProperCurve γ) (h0 : (γ 0).im = 0) :
    IsClosed (closedRightSide γ) := by
  rw [closedRightSide_eq_compl hγ h0]
  exact (isOpen_leftSide hγ).isClosed_compl

/-! ### The completed retained path and its completion by a real ray -/

/-- **A completed retained path in the builder frame**: continuous and injective on `[0, T]`, in `ℍ̄`, from the real
point `d ≥ 0` to the real point `E`, with all real points in `[0, E]`, never returning to `0`. -/
structure IsRetPath (Q : ℝ≥0 → ℂ) (T : ℝ≥0) (d E : ℝ) : Prop where
  cont : ContinuousOn Q (Icc 0 T)
  inj : InjOn Q (Icc 0 T)
  hbar : ∀ t ≤ T, 0 ≤ (Q t).im
  zero : Q 0 = d
  seed : 0 ≤ d
  tip : Q T = E
  pos : 0 < T
  real_ge : ∀ t ≤ T, (Q t).im = 0 → 0 ≤ (Q t).re
  real_le : ∀ t ≤ T, (Q t).im = 0 → (Q t).re ≤ E
  ne_zero : ∀ t ≤ T, 0 < t → Q t ≠ 0

/-- The retained path followed by the real ray from its end point. -/
def rayQ (Q : ℝ≥0 → ℂ) (T : ℝ≥0) (E : ℝ) (t : ℝ≥0) : ℂ :=
  if t ≤ T then Q t else ((E + ((t : ℝ) - T) : ℝ) : ℂ)

variable {Q : ℝ≥0 → ℂ} {T : ℝ≥0} {d E : ℝ}

theorem rayQ_of_le {t : ℝ≥0} (ht : t ≤ T) : rayQ Q T E t = Q t := by
  simp only [rayQ, ht, ↓reduceIte]

theorem rayQ_of_lt {t : ℝ≥0} (ht : T < t) : rayQ Q T E t = ((E + ((t : ℝ) - T) : ℝ) : ℂ) := by
  simp only [rayQ, not_le.2 ht, ↓reduceIte]

theorem IsRetPath.isCompact_image (h : IsRetPath Q T d E) : IsCompact (Q '' Icc 0 T) :=
  isCompact_Icc.image_of_continuousOn h.cont

theorem IsRetPath.image_subset_Hbar (h : IsRetPath Q T d E) : Q '' Icc 0 T ⊆ Hbar := by
  rintro _ ⟨t, ht, rfl⟩
  exact h.hbar t ht.2

theorem IsRetPath.tip_pos (h : IsRetPath Q T d E) : 0 < E := by
  have h1 : (Q T).im = 0 := by rw [h.tip, ofReal_im]
  have h2 := h.real_ge T le_rfl h1
  rw [h.tip, ofReal_re] at h2
  rcases h2.lt_or_eq with h3 | h3
  · exact h3
  · exact absurd (by rw [h.tip, ← h3, ofReal_zero]) (h.ne_zero T le_rfl h.pos)

/-- **The real-ray completion is a proper completion of the retained path.** -/
theorem IsRetPath.isProperCompletion_rayQ (h : IsRetPath Q T d E) : IsProperCompletion Q T (rayQ Q T E) := by
  refine ⟨?_, ?_, fun t => ?_, ?_, fun t ht => rayQ_of_le ht⟩
  · -- continuity
    have hQc : ContinuousOn Q {t : ℝ≥0 | t ≤ T} := h.cont.mono fun t ht => ⟨zero_le, ht⟩
    refine continuous_if_le continuous_id continuous_const hQc (by fun_prop) fun t ht => ?_
    have ht' : t = T := ht
    rw [ht', h.tip, sub_self, add_zero]
  · -- injectivity
    intro s t hst
    rcases le_or_gt s T with hs | hs <;> rcases le_or_gt t T with ht | ht
    · rw [rayQ_of_le hs, rayQ_of_le ht] at hst
      exact h.inj ⟨zero_le, hs⟩ ⟨zero_le, ht⟩ hst
    · rw [rayQ_of_le hs, rayQ_of_lt ht] at hst
      exfalso
      have hTt : (T : ℝ) < t := ht
      have him : (Q s).im = 0 := by rw [hst, ofReal_im]
      have hre := h.real_le s hs him
      rw [hst, ofReal_re] at hre
      linarith
    · rw [rayQ_of_lt hs, rayQ_of_le ht] at hst
      exfalso
      have hTs : (T : ℝ) < s := hs
      have him : (Q t).im = 0 := by rw [← hst, ofReal_im]
      have hre := h.real_le t ht him
      rw [← hst, ofReal_re] at hre
      linarith
    · rw [rayQ_of_lt hs, rayQ_of_lt ht] at hst
      have h1 : E + ((s : ℝ) - T) = E + ((t : ℝ) - T) := by exact_mod_cast hst
      exact NNReal.coe_injective (by linarith)
  · -- the closed half-plane
    rcases le_or_gt t T with ht | ht
    · rw [rayQ_of_le ht]; exact h.hbar t ht
    · rw [rayQ_of_lt ht, ofReal_im]
  · -- properness
    have h1 : Tendsto (fun t : ℝ≥0 => E + ((t : ℝ) - T)) atTop atTop := by
      refine tendsto_atTop_add_const_left _ _ (tendsto_atTop_add_const_right _ _ ?_)
      exact NNReal.tendsto_coe_atTop.2 tendsto_id
    refine tendsto_atTop_mono' _ ?_ h1
    filter_upwards [eventually_gt_atTop T] with t ht
    rw [rayQ_of_lt ht, Complex.norm_real, Real.norm_eq_abs]
    exact le_abs_self _

theorem IsRetPath.isProperCurve_rayQ (h : IsRetPath Q T d E) : IsProperCurve (rayQ Q T E) :=
  isProperCurve_of_isProperCompletion h.isProperCompletion_rayQ

theorem IsRetPath.rayQ_zero (h : IsRetPath Q T d E) : rayQ Q T E 0 = d := by
  rw [rayQ_of_le zero_le, h.zero]

/-- The range of the ray completion: the path and the open real ray right of its end. -/
theorem mem_range_rayQ {z : ℂ} :
    z ∈ range (rayQ Q T E) ↔ z ∈ Q '' Icc 0 T ∨ ∃ y : ℝ, E < y ∧ z = y := by
  constructor
  · rintro ⟨t, rfl⟩
    rcases le_or_gt t T with ht | ht
    · exact Or.inl ⟨t, ⟨zero_le, ht⟩, (rayQ_of_le ht).symm⟩
    · have hTt : (T : ℝ) < t := ht
      exact Or.inr ⟨E + ((t : ℝ) - T), by linarith, rayQ_of_lt ht⟩
  · rintro (⟨t, ht, rfl⟩ | ⟨y, hy, rfl⟩)
    · exact ⟨t, rayQ_of_le ht.2⟩
    · have hpos : 0 < y - E := by linarith
      refine ⟨T + (y - E).toNNReal, ?_⟩
      have hlt : T < T + (y - E).toNNReal := lt_add_of_pos_right T (Real.toNNReal_pos.2 hpos)
      rw [rayQ_of_lt hlt, NNReal.coe_add, Real.coe_toNNReal _ hpos.le]
      congr 1
      ring

/-! ### Real points and labels for the retained path -/

/-- A real point left of `0` is free for the retained path. -/
theorem IsRetPath.isFreeAt_of_neg (h : IsRetPath Q T d E) {r : ℝ} (hr : r < 0) :
    IsFreeAt (Q '' Icc 0 T) (r : ℂ) := by
  refine isFreeAt_of_notMem_closure fun hmem => ?_
  obtain ⟨_, ⟨t, ht, rfl⟩, him, hre⟩ :=
    Sec7.R6Fd.exists_real_le_of_mem_closure_fillH h.isCompact_image h.image_subset_Hbar hmem
  have := h.real_ge t ht.2 him
  linarith

/-- A real point right of the end point is free for the retained path. -/
theorem IsRetPath.isFreeAt_of_gt (h : IsRetPath Q T d E) {r : ℝ} (hr : E < r) :
    IsFreeAt (Q '' Icc 0 T) (r : ℂ) := by
  refine isFreeAt_of_notMem_closure fun hmem => ?_
  obtain ⟨_, ⟨t, ht, rfl⟩, him, hre⟩ :=
    Sec7.R6Fd.exists_real_ge_of_mem_closure_fillH h.isCompact_image h.image_subset_Hbar hmem
  have := h.real_le t ht.2 him
  linarith

/-- For a positive seed, the explorer's seed `0` is free for the retained path. -/
theorem IsRetPath.isFreeAt_zero (h : IsRetPath Q T d E) (hd : 0 < d) : IsFreeAt (Q '' Icc 0 T) (0 : ℂ) := by
  refine isFreeAt_of_notMem_closure fun hmem => ?_
  have hmem' : ((0 : ℝ) : ℂ) ∈ closure (fillH (Q '' Icc 0 T)) := by rwa [ofReal_zero]
  obtain ⟨_, ⟨t, ht, rfl⟩, him, hre⟩ :=
    Sec7.R6Fd.exists_real_le_of_mem_closure_fillH h.isCompact_image h.image_subset_Hbar hmem'
  have hge := h.real_ge t ht.2 him
  have hz : Q t = 0 := Complex.ext (by rw [zero_re]; linarith) (by rw [zero_im]; exact him)
  rcases eq_or_lt_of_le (zero_le : (0 : ℝ≥0) ≤ t) with h0 | h0
  · rw [← h0, h.zero] at hz
    have : d = 0 := by exact_mod_cast hz
    linarith
  · exact h.ne_zero t ht.2 h0 hz

/-- For a common seed, a real point strictly between `0` and the end point and off the path is not free. -/
theorem IsRetPath.not_isFreeAt_between (h : IsRetPath Q T d E) (hd : d = 0) {r : ℝ} (hr0 : 0 < r) (hrE : r < E)
    (hrQ : (r : ℂ) ∉ Q '' Icc 0 T) : ¬ IsFreeAt (Q '' Icc 0 T) (r : ℂ) := by
  intro hf
  refine notMem_closure_of_isFreeAt hf (mem_closure_fillH_between h.cont h.hbar (u₁ := 0) (u₂ := T) zero_le
    le_rfl ?_ ?_ ?_ ?_ hrQ)
  · rw [h.zero, ofReal_im]
  · rw [h.tip, ofReal_im]
  · rw [h.zero, ofReal_re, hd]; exact hr0
  · rw [h.tip, ofReal_re]; exact hrE

/-! ### The left side of the ray completion for a common seed -/

/-- **For a common seed, the left side of the ray completion meets `ℍ̄` in free points.** The set of the lower left
quadrant and the free points of `ℍ̄` off the closed curve is open and closed in the complement of the closed curve. -/
theorem IsRetPath.isFreeAt_of_mem_leftSide (h : IsRetPath Q T d E) (hd : d = 0) {z : ℂ}
    (hz : z ∈ leftSide (rayQ Q T E)) (hzH : 0 ≤ z.im) : IsFreeAt (Q '' Icc 0 T) z := by
  set F := Q '' Icc 0 T with hF
  set Q' := rayQ Q T E with hQ'
  have hP := h.isProperCurve_rayQ
  have hQ0 : Q' 0 = 0 := by rw [hQ', h.rayQ_zero, hd, ofReal_zero]
  have h0im : (Q' 0).im = 0 := by rw [hQ0, zero_im]
  have h0re : (Q' 0).re = 0 := by rw [hQ0, zero_re]
  set S := seedRayClosure Q' with hS
  have hSc : IsClosed S := isClosed_seedRayClosure hP
  have hFc : IsClosed F := h.isCompact_image.isClosed
  have hFS : F ⊆ S := fun w hw => Or.inl (mem_range_rayQ.2 (Or.inl hw))
  have h0S : (0 : ℂ) ∈ S := Or.inl ⟨0, hQ0⟩
  -- real points off the closed curve
  have hrealS : ∀ r : ℝ, (r : ℂ) ∉ S → r < E ∧ r ≠ 0 ∧ (r : ℂ) ∉ F := by
    intro r hr
    refine ⟨?_, ?_, fun hrF => hr (hFS hrF)⟩
    · by_contra hge
      push Not at hge
      rcases hge.lt_or_eq with hlt | heq
      · exact hr (Or.inl (mem_range_rayQ.2 (Or.inr ⟨r, hlt, rfl⟩)))
      · exact hr (hFS ⟨T, ⟨zero_le, le_rfl⟩, by rw [h.tip, heq]⟩)
    · rintro rfl
      exact hr (by rwa [ofReal_zero])
  set G : Set ℂ := lowerLeft 0 ∪ ({w | IsFreeAt F w} ∩ {w | 0 ≤ w.im} ∩ Sᶜ) with hG
  set G' : Set ℂ := lowerRight 0 ∪ ({w | IsTrappedAt F w} ∩ {w | 0 ≤ w.im} ∩ Sᶜ) with hG'
  have hGo : IsOpen G := by
    refine Metric.isOpen_iff.2 fun w hw => ?_
    rcases hw with hw | ⟨⟨hwf, hwH⟩, hwS⟩
    · exact Metric.isOpen_iff.1 (isOpen_lowerLeft 0) w hw |>.imp fun ε hε => ⟨hε.1, hε.2.trans subset_union_left⟩
    · have hopen : IsOpen ({w | IsFreeAt F w} ∩ Sᶜ) := (isOpen_setOf_isFreeAt F).inter hSc.isOpen_compl
      obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 hopen w ⟨hwf, hwS⟩
      have hwH' : 0 ≤ w.im := hwH
      rcases hwH'.lt_or_eq with hpos | hzero
      · refine ⟨min ε w.im, lt_min hε hpos, fun u hu => Or.inr ⟨⟨(hball ?_).1, ?_⟩, (hball ?_).2⟩⟩
        · exact ball_subset_ball (min_le_left _ _) hu
        · have h1 : dist u w < w.im := lt_of_lt_of_le hu (min_le_right _ _)
          have h2 : |u.im - w.im| ≤ dist u w := by
            rw [dist_eq_norm, ← sub_im]; exact abs_im_le_norm _
          have := abs_lt.1 (lt_of_le_of_lt h2 h1)
          show 0 ≤ u.im
          linarith [this.1]
        · exact ball_subset_ball (min_le_left _ _) hu
      · -- a real free point off the closed curve is negative
        have hwr : w = ((w.re : ℝ) : ℂ) := Complex.ext (by simp) (by simp [← hzero])
        have hwS' : ((w.re : ℝ) : ℂ) ∉ S := by rw [← hwr]; exact hwS
        obtain ⟨hlt, hne, hnF⟩ := hrealS w.re hwS'
        have hneg : w.re < 0 := by
          by_contra hge
          push Not at hge
          have hpos : 0 < w.re := lt_of_le_of_ne hge (Ne.symm hne)
          exact h.not_isFreeAt_between hd hpos hlt hnF (by rw [← hwr]; exact hwf)
        refine ⟨min ε (-w.re), lt_min hε (by linarith), fun u hu => ?_⟩
        have hu1 : u ∈ ball w ε := ball_subset_ball (min_le_left _ _) hu
        by_cases huH : 0 ≤ u.im
        · exact Or.inr ⟨⟨(hball hu1).1, huH⟩, (hball hu1).2⟩
        · refine Or.inl ⟨?_, not_le.1 huH⟩
          have h1 : dist u w < -w.re := lt_of_lt_of_le hu (min_le_right _ _)
          have h2 : |u.re - w.re| ≤ dist u w := by
            rw [dist_eq_norm, ← sub_re]; exact abs_re_le_norm _
          have := abs_lt.1 (lt_of_le_of_lt h2 h1)
          linarith [this.2]
  have hG'o : IsOpen G' := by
    refine Metric.isOpen_iff.2 fun w hw => ?_
    rcases hw with hw | ⟨⟨hwt, hwH⟩, hwS⟩
    · exact Metric.isOpen_iff.1 (isOpen_lowerRight 0) w hw |>.imp fun ε hε => ⟨hε.1, hε.2.trans subset_union_left⟩
    · have hopen : IsOpen ({w | IsTrappedAt F w} ∩ Sᶜ) := (isOpen_setOf_isTrappedAt F).inter hSc.isOpen_compl
      obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 hopen w ⟨hwt, hwS⟩
      have hwH' : 0 ≤ w.im := hwH
      rcases hwH'.lt_or_eq with hpos | hzero
      · refine ⟨min ε w.im, lt_min hε hpos, fun u hu => Or.inr ⟨⟨(hball ?_).1, ?_⟩, (hball ?_).2⟩⟩
        · exact ball_subset_ball (min_le_left _ _) hu
        · have h1 : dist u w < w.im := lt_of_lt_of_le hu (min_le_right _ _)
          have h2 : |u.im - w.im| ≤ dist u w := by
            rw [dist_eq_norm, ← sub_im]; exact abs_im_le_norm _
          have := abs_lt.1 (lt_of_le_of_lt h2 h1)
          show 0 ≤ u.im
          linarith [this.1]
        · exact ball_subset_ball (min_le_left _ _) hu
      · -- a real trapped point off the closed curve is positive
        have hwr : w = ((w.re : ℝ) : ℂ) := Complex.ext (by simp) (by simp [← hzero])
        have hwS' : ((w.re : ℝ) : ℂ) ∉ S := by rw [← hwr]; exact hwS
        obtain ⟨-, hne, -⟩ := hrealS w.re hwS'
        have hpos : 0 < w.re := by
          by_contra hle
          push Not at hle
          have hneg : w.re < 0 := lt_of_le_of_ne hle hne
          have hfree := h.isFreeAt_of_neg hneg
          rw [← hwr] at hfree
          exact hfree.not_isTrappedAt hwH hwt
        refine ⟨min ε w.re, lt_min hε hpos, fun u hu => ?_⟩
        have hu1 : u ∈ ball w ε := ball_subset_ball (min_le_left _ _) hu
        by_cases huH : 0 ≤ u.im
        · exact Or.inr ⟨⟨(hball hu1).1, huH⟩, (hball hu1).2⟩
        · refine Or.inl ⟨?_, not_le.1 huH⟩
          have h1 : dist u w < w.re := lt_of_lt_of_le hu (min_le_right _ _)
          have h2 : |u.re - w.re| ≤ dist u w := by
            rw [dist_eq_norm, ← sub_re]; exact abs_re_le_norm _
          have := abs_lt.1 (lt_of_le_of_lt h2 h1)
          linarith [this.1]
  have hdisj : Disjoint G G' := by
    refine Set.disjoint_left.2 fun w hw hw' => ?_
    rcases hw with hw | ⟨⟨hwf, hwH⟩, -⟩ <;> rcases hw' with hw' | ⟨⟨hwt, hwH'⟩, -⟩
    · exact absurd hw'.1 (not_lt.2 hw.1.le)
    · exact absurd hw.2 (not_lt.2 hwH')
    · exact absurd hw'.2 (not_lt.2 hwH)
    · exact hwf.not_isTrappedAt hwH hwt
  have hcover : Sᶜ ⊆ G ∪ G' := by
    intro w hw
    by_cases hwH : 0 ≤ w.im
    · rcases isFreeAt_or_isTrappedAt hFc (fun hwF => hw (hFS hwF)) with hf | ht
      · exact Or.inl (Or.inr ⟨⟨hf, hwH⟩, hw⟩)
      · exact Or.inr (Or.inr ⟨⟨ht, hwH⟩, hw⟩)
    · have hneg : w.im < 0 := not_le.1 hwH
      rcases lt_trichotomy w.re 0 with hlt | heq | hgt
      · exact Or.inl (Or.inl ⟨hlt, hneg⟩)
      · exact absurd (Or.inr ⟨by rw [heq, h0re], by rw [h0im]; exact hneg.le⟩) hw
      · exact Or.inr (Or.inl ⟨hgt, hneg⟩)
  have hpre : IsPreconnected (leftSide Q') := isPreconnected_connectedComponentIn
  have hsub : leftSide Q' ⊆ G ∪ G' := (leftSide_subset_compl Q').trans hcover
  have hne : (leftSide Q' ∩ G).Nonempty := by
    refine ⟨Q' 0 - 1 - I, leftRef_mem_leftSide hP.2.2.1 h0im, Or.inl ?_⟩
    have := left_ref_mem_lowerLeft (γ := Q') h0im
    rwa [h0re] at this
  have hG_all := hpre.subset_left_of_subset_union hGo hG'o hdisj hsub hne
  rcases hG_all hz with hl | ⟨⟨hf, -⟩, -⟩
  · exact absurd hl.2 (not_lt.2 hzH)
  · exact hf

/-! ### The explorer prefix -/

variable {β : ℝ≥0 → ℂ} {a : ℝ≥0}

/-- **An explorer prefix off a completed retained path**: continuous on `[0, a]`, in `ℍ̄`, from `0`, with no
positive-time contact with the path. -/
structure IsExpPrefix (β : ℝ≥0 → ℂ) (a : ℝ≥0) (Q : ℝ≥0 → ℂ) (T : ℝ≥0) : Prop where
  cont : ContinuousOn β (Icc 0 a)
  hbar : ∀ t ≤ a, 0 ≤ (β t).im
  zero : β 0 = 0
  off : ∀ t ≤ a, 0 < t → β t ∉ Q '' Icc 0 T

/-- **The early case**: an explorer prefix with no real point at or right of the end point of the path has a proper
completion in the closed left side of the ray completion of the path. -/
theorem exists_completion_early (h : IsRetPath Q T d E) (hβ : IsExpPrefix β a Q T)
    (hW : ∀ c : ℝ≥0, c < T → HasOrderedProperCompletions Q c β a)
    (hE : ∀ t ≤ a, ∀ y : ℝ, E ≤ y → β t ≠ y) :
    ∃ β', IsProperCompletion β a β' ∧ range β' ⊆ closedLeftSide (rayQ Q T E) ∧
      Q '' Icc 0 T ⊆ closedRightSide β' := by
  set c : ℝ≥0 := T / 2 with hc
  have hc0 : 0 < c := by rw [hc]; exact half_pos h.pos
  have hcT : c < T := by rw [hc]; exact NNReal.half_lt_self h.pos.ne'
  obtain ⟨α', β₀, hα', hβ₀, hord⟩ := hW c hcT
  have hQ0 : (Q 0).im = 0 := by rw [h.zero, ofReal_im]
  have hβ0 : (β 0).im = 0 := by rw [hβ.zero, zero_im]
  have hseed : (β 0).re ≤ (Q 0).re := by rw [hβ.zero, h.zero, zero_re, ofReal_re]; exact h.seed
  have hray := h.isProperCompletion_rayQ
  have hrayc : IsProperCompletion Q c (rayQ Q T E) :=
    ⟨hray.1, hray.2.1, hray.2.2.1, hray.2.2.2.1, fun t ht => hray.2.2.2.2 t (ht.trans hcT.le)⟩
  have htail : ∀ s, c ≤ s → ∀ y ≤ a, rayQ Q T E s ≠ β y := by
    intro s hs y hy heq
    have hs0 : 0 < s := lt_of_lt_of_le hc0 hs
    rcases le_or_gt s T with hsT | hsT
    · rw [rayQ_of_le hsT] at heq
      rcases eq_or_lt_of_le (zero_le : (0 : ℝ≥0) ≤ y) with hy0 | hy0
      · rw [← hy0, hβ.zero] at heq
        exact h.ne_zero s hsT hs0 heq
      · exact hβ.off y hy hy0 ⟨s, ⟨zero_le, hsT⟩, heq⟩
    · rw [rayQ_of_lt hsT] at heq
      have hTs : (T : ℝ) < s := hsT
      exact hE y hy _ (by linarith) heq.symm
  obtain ⟨β', hβ', hord'⟩ :=
    exists_isProperCompletion_subset_closedLeftSide hα' hβ₀ hord hQ0 hβ0 hseed hrayc htail
  refine ⟨β', hβ', hord', ?_⟩
  have hP := h.isProperCurve_rayQ
  have hP' := isProperCurve_of_isProperCompletion hβ'
  have h0 : (rayQ Q T E 0).im = 0 := by rw [h.rayQ_zero, ofReal_im]
  have hb0 : (β' 0).im = 0 := by rw [hβ'.2.2.2.2 0 zero_le]; exact hβ0
  have hseed' : (β' 0).re ≤ (rayQ Q T E 0).re := by
    rw [hβ'.2.2.2.2 0 zero_le, h.rayQ_zero, hβ.zero, zero_re, ofReal_re]; exact h.seed
  have hdual := range_subset_closedRightSide hP hP' h0 hb0 hseed' hord'
  rintro _ ⟨t, ht, rfl⟩
  exact hdual ⟨t, rayQ_of_le ht.2⟩

/-- **The late case**: if the explorer prefix has a real point right of the end point of the path, the path lies in
the closed right side of every proper completion of the prefix whose new part is off the prefix's filled hull. -/
theorem subset_closedRightSide_late (h : IsRetPath Q T d E) (hβ : IsExpPrefix β a Q T)
    (hW : ∀ c : ℝ≥0, c < T → HasOrderedProperCompletions Q c β a)
    {s : ℝ≥0} (hs : s ≤ a) {y : ℝ} (hy : E < y) (hsy : β s = y)
    {βf : ℝ≥0 → ℂ} (hβf : IsProperCompletion β a βf)
    (hfr : ∀ t, a < t → βf t ∈ H \ fillH (β '' Icc 0 a)) :
    Q '' Icc 0 T ⊆ closedRightSide βf := by
  have hE0 := h.tip_pos
  have hs0 : 0 < s := by
    rcases eq_or_lt_of_le (zero_le : (0 : ℝ≥0) ≤ s) with h0 | h0
    · rw [← h0, hβ.zero] at hsy
      have : (0 : ℝ) = y := by exact_mod_cast hsy
      linarith
    · exact h0
  have ha0 : 0 < a := lt_of_lt_of_le hs0 hs
  set F₁ := β '' Icc 0 a with hF₁
  have hF₁c : IsClosed F₁ := (isCompact_Icc.image_of_continuousOn hβ.cont).isClosed
  -- the path after its seed is off the prefix
  have hoff : ∀ u ≤ T, 0 < u → Q u ∉ F₁ := by
    rintro u hu hu0 ⟨t, ht, hqt⟩
    rcases eq_or_lt_of_le (zero_le : (0 : ℝ≥0) ≤ t) with h0 | h0
    · rw [← h0, hβ.zero] at hqt
      exact h.ne_zero u hu hu0 hqt.symm
    · exact hβ.off t ht.2 h0 ⟨u, ⟨zero_le, hu⟩, hqt.symm⟩
  -- the end point is trapped by the prefix
  have hEtr : IsTrappedAt F₁ (E : ℂ) := by
    have hEF : (E : ℂ) ∉ F₁ := by rw [← h.tip]; exact hoff T le_rfl h.pos
    rcases isFreeAt_or_isTrappedAt hF₁c hEF with hf | ht
    · exfalso
      refine notMem_closure_of_isFreeAt hf (mem_closure_fillH_between hβ.cont hβ.hbar (u₁ := 0) (u₂ := s)
        zero_le hs ?_ ?_ ?_ ?_ hEF)
      · rw [hβ.zero, zero_im]
      · rw [hsy, ofReal_im]
      · rw [hβ.zero, zero_re]; exact hE0
      · rw [hsy, ofReal_re]; exact hy
    · exact ht
  -- the whole path after its seed is trapped
  have hX : IsPreconnected (Q '' Ioc 0 T) :=
    isPreconnected_Ioc.image Q (h.cont.mono Ioc_subset_Icc_self)
  have hXF : Q '' Ioc 0 T ⊆ {w | 0 ≤ w.im} \ F₁ := by
    rintro _ ⟨u, hu, rfl⟩
    exact ⟨h.hbar u hu.2, hoff u hu.2 hu.1⟩
  have htr : ∀ u ≤ T, 0 < u → IsTrappedAt F₁ (Q u) := by
    intro u hu hu0
    rcases isFreeAt_or_isTrappedAt_of_isPreconnected hF₁c hX hXF with hall | hall
    · have hfT := hall (Q T) ⟨T, ⟨h.pos, le_rfl⟩, rfl⟩
      rw [h.tip] at hfT
      exact absurd hEtr (hfT.not_isTrappedAt (by rw [ofReal_im]))
    · exact hall (Q u) ⟨u, ⟨hu0, hu⟩, rfl⟩
  have hPf := isProperCurve_of_isProperCompletion hβf
  have hf0 : (βf 0).im = 0 := by rw [hβf.2.2.2.2 0 zero_le, hβ.zero, zero_im]
  have hclosed := isClosed_closedRightSide hPf hf0
  -- the path before the horizon
  have hlt : ∀ t : ℝ≥0, t < T → Q t ∈ closedRightSide βf := by
    intro t htT
    obtain ⟨α', β₀, hα', hβ₀, hord⟩ := hW t htT
    have hPα := isProperCurve_of_isProperCompletion hα'
    have hPβ := isProperCurve_of_isProperCompletion hβ₀
    have hα0 : α' 0 = Q 0 := hα'.2.2.2.2 0 zero_le
    have hβ00 : β₀ 0 = β 0 := hβ₀.2.2.2.2 0 zero_le
    have hα0im : (α' 0).im = 0 := by rw [hα0, h.zero, ofReal_im]
    have hβ0im : (β₀ 0).im = 0 := by rw [hβ00, hβ.zero, zero_im]
    have hseed : (β₀ 0).re ≤ (α' 0).re := by
      rw [hα0, hβ00, hβ.zero, h.zero, zero_re, ofReal_re]; exact h.seed
    have hdual := range_subset_closedRightSide hPα hPβ hα0im hβ0im hseed hord
    have hagree : ∀ u ≤ a, βf u = β₀ u := fun u hu => (hβf.2.2.2.2 u hu).trans (hβ₀.2.2.2.2 u hu).symm
    have havoid : ∀ u ≤ t, ∀ s', a ≤ s' → α' u ≠ βf s' := by
      intro u hu s' hs' heq
      rw [hα'.2.2.2.2 u hu] at heq
      have huT : u ≤ T := hu.trans htT.le
      rcases eq_or_lt_of_le hs' with hsa | hsa
      · -- at the junction the completion is the prefix's end
        rw [← hsa, hβf.2.2.2.2 a le_rfl] at heq
        exact hβ.off a le_rfl ha0 ⟨u, ⟨zero_le, huT⟩, heq⟩
      · have hmem := hfr s' hsa
        rw [← heq] at hmem
        rcases eq_or_lt_of_le (zero_le : (0 : ℝ≥0) ≤ u) with hu0 | hu0
        · rw [← hu0, h.zero] at hmem
          have him : (0 : ℝ) < ((d : ℝ) : ℂ).im := hmem.1
          rw [ofReal_im] at him
          exact lt_irrefl _ him
        · exact hmem.2 (mem_fillH_of_isTrappedAt (htr u huT hu0) hmem.1)
    have := mem_closedRightSide_of_avoid hPβ hPf hβ0im hagree hPα hα0im hseed hdual (t := t) havoid
    rwa [hα'.2.2.2.2 t le_rfl] at this
  rintro _ ⟨t, ht, rfl⟩
  rcases ht.2.lt_or_eq with htT | htT
  · exact hlt t htT
  · -- the end point, by closedness
    rw [htT]
    have hcw : ContinuousWithinAt Q (Icc 0 T) T := h.cont T ⟨zero_le, le_rfl⟩
    have hTcl : T ∈ closure (Ico 0 T) := by
      rw [closure_Ico h.pos.ne]
      exact ⟨zero_le, le_rfl⟩
    have hmem : Q T ∈ closure (Q '' Ico 0 T) :=
      (hcw.mono Ico_subset_Icc_self).mem_closure_image hTcl
    refine hclosed.closure_subset_iff.2 ?_ hmem
    rintro _ ⟨u, hu, rfl⟩
    exact hlt u hu.2

/-- **Activity.** Every point of the explorer prefix at a positive time is free for the completed retained path. -/
theorem isFreeAt_explorer (h : IsRetPath Q T d E) (hβ : IsExpPrefix β a Q T)
    (hW : ∀ c : ℝ≥0, c < T → HasOrderedProperCompletions Q c β a) {t : ℝ≥0} (ht : t ≤ a) (ht0 : 0 < t) :
    IsFreeAt (Q '' Icc 0 T) (β t) := by
  set F := Q '' Icc 0 T with hF
  have hFc : IsClosed F := h.isCompact_image.isClosed
  have hX : IsPreconnected (β '' Ioc 0 a) := isPreconnected_Ioc.image β (hβ.cont.mono Ioc_subset_Icc_self)
  have hXF : β '' Ioc 0 a ⊆ {w | 0 ≤ w.im} \ F := by
    rintro _ ⟨u, hu, rfl⟩
    exact ⟨hβ.hbar u hu.2, hβ.off u hu.2 hu.1⟩
  have hmemX : β t ∈ β '' Ioc 0 a := ⟨t, ⟨ht0, ht⟩, rfl⟩
  -- one free point of the prefix decides
  have hone : ∀ u : ℝ≥0, u ≤ a → 0 < u → IsFreeAt F (β u) → IsFreeAt F (β t) := by
    intro u hu hu0 hfu
    rcases isFreeAt_or_isTrappedAt_of_isPreconnected hFc hX hXF with hall | hall
    · exact hall _ hmemX
    · exact absurd (hall (β u) ⟨u, ⟨hu0, hu⟩, rfl⟩) (hfu.not_isTrappedAt (hβ.hbar u hu))
  by_cases hE : ∀ u ≤ a, ∀ y : ℝ, E ≤ y → β u ≠ y
  · -- the early case
    rcases h.seed.lt_or_eq with hd | hd
    · -- distinct seeds: the explorer's seed is free
      have hX' : IsPreconnected (β '' Icc 0 a) := isPreconnected_Icc.image β hβ.cont
      have hX'F : β '' Icc 0 a ⊆ {w | 0 ≤ w.im} \ F := by
        rintro _ ⟨u, hu, rfl⟩
        refine ⟨hβ.hbar u hu.2, ?_⟩
        rcases eq_or_lt_of_le hu.1 with hu0 | hu0
        · rw [← hu0, hβ.zero]
          rintro ⟨v, hv, hqv⟩
          rcases eq_or_lt_of_le hv.1 with hv0 | hv0
          · rw [← hv0, h.zero] at hqv
            have : d = 0 := by exact_mod_cast hqv
            linarith
          · exact h.ne_zero v hv.2 hv0 hqv
        · exact hβ.off u hu.2 hu0
      rcases isFreeAt_or_isTrappedAt_of_isPreconnected hFc hX' hX'F with hall | hall
      · exact hall _ ⟨t, ⟨zero_le, ht⟩, rfl⟩
      · have h0 := hall (β 0) ⟨0, ⟨le_rfl, zero_le⟩, rfl⟩
        rw [hβ.zero] at h0
        exact absurd h0 ((h.isFreeAt_zero hd).not_isTrappedAt (by rw [zero_im]))
    · -- a common seed: the label argument on the left side of the ray completion
      obtain ⟨β', hβ', hord, -⟩ := exists_completion_early h hβ hW hE
      have hmem : β t ∈ closedLeftSide (rayQ Q T E) := by
        rw [← hβ'.2.2.2.2 t ht]; exact hord ⟨t, rfl⟩
      rcases hmem with hL | hS
      · exact h.isFreeAt_of_mem_leftSide hd.symm hL (hβ.hbar t ht)
      · exfalso
        rcases hS with hR | ⟨hre, him⟩
        · rcases mem_range_rayQ.1 hR with hQ | ⟨y, hy, hty⟩
          · exact hβ.off t ht ht0 hQ
          · exact hE t ht y hy.le hty
        · -- the lower ray meets the closed half-plane at the seed only
          rw [h.rayQ_zero, ofReal_re] at hre
          rw [h.rayQ_zero, ofReal_im] at him
          have him0 : (β t).im = 0 := le_antisymm him (hβ.hbar t ht)
          have hzero : β t = 0 := Complex.ext (by rw [hre, zero_re, hd]) (by rw [him0, zero_im])
          exact hβ.off t ht ht0 ⟨0, ⟨le_rfl, zero_le⟩, by rw [h.zero, ← hd, ofReal_zero, hzero]⟩
  · -- the late case: a real point of the prefix right of the end point is free
    push Not at hE
    obtain ⟨u, hu, y, hy, huy⟩ := hE
    have hu0 : 0 < u := by
      rcases eq_or_lt_of_le (zero_le : (0 : ℝ≥0) ≤ u) with h0 | h0
      · rw [← h0, hβ.zero] at huy
        have h1 : (0 : ℝ) = y := by exact_mod_cast huy
        have := h.tip_pos
        linarith
      · exact h0
    have hyE : E < y := by
      rcases hy.lt_or_eq with hlt | heq
      · exact hlt
      · exact absurd ⟨T, ⟨zero_le, le_rfl⟩, by rw [h.tip, heq, huy]⟩ (hβ.off u hu hu0)
    refine hone u hu hu0 ?_
    rw [huy]
    exact h.isFreeAt_of_gt hyE

end Term

end InteractingSLE.RealContact
