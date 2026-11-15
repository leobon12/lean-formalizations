/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.G7ClockMeas

/-!
# The canonical retained clocks of both continuations of a retained pair (pathwise)

Packet PROVE-G7B. At a retained pair `(u, r)` with the retained chart `(φ, ψ)` at the second tip
(`IsRetChart`, `G7RetainedChart.lean`):

* the second path continues from the chart point: `isRetCont_snd` gives `IsRetCont` with the chart itself;
* the first path continues from its own tip `α(u)`, whose chart preimage is a real point `w₁` (the forward chart
  limit; `α(u)` is a regular point); `isRetCont_fst` gives `IsRetCont` with the chart translated by `w₁`
  (`IsDomChart.shift`).

The **canonical retained clock** of a continuation (`canonRetPath`, `canonRetLife`): the chart path of the
continuation in the chart translated by `c` (`c = 0` for the second path, `c = w₁` for the first), read in its inverse
relative capacity clock and translated back by `c`, with its capacity lifetime. `isRetainedClock_canon` gives the
clock relation `IsRetainedClock` of the named input `RetainedPairRestartStatement` for it.

Congruences (`IsPathGood.congr`, `contSet_congr`, `contPath_congr`, `canonRetPath_congr`, `IsRetainedClock.congr`,
`IsRetainedClock.mono`) transport these objects between paths that agree on their available intervals.
-/

set_option autoImplicit false

noncomputable section

open Complex Set Metric Filter Topology
open scoped NNReal ENNReal

open QuantumZipper (H Hbar)

namespace InteractingSLE

namespace Supp7

open Restart

/-! ### Congruences -/

theorem IsPathGood.congr {η η' : ℝ≥0 → ℂ} {ζ : ℝ≥0∞} {x : ℝ} (hp : IsPathGood η ζ x)
    (he : ∀ t : ℝ≥0, (t : ℝ≥0∞) ≤ ζ → η' t = η t) : IsPathGood η' ζ x := by
  obtain ⟨hi, w, hw, hw0, h0, hc, hf⟩ := hp
  refine ⟨hi.congr fun t ht => (he t ht).symm, w, hw, hw0, ?_, ?_, fun t ht => ?_⟩
  · show η' 0 - x = 0
    rw [he 0 (by simp)]; exact h0
  · exact hc.congr fun t ht => by simp only [he t ht]
  · have : (fun s => η' s - (x : ℂ)) '' Icc 0 t = (fun s => η s - (x : ℂ)) '' Icc 0 t :=
      image_congr fun s hs => by simp only [he s ((ENNReal.coe_le_coe.2 hs.2).trans ht.le)]
    rw [this]
    exact hf t ht

section Congr

variable {η η' : ℝ≥0 → ℂ} {ζ : ℝ≥0∞} {a : ℝ≥0} {K : Set ℂ}

theorem contSet_congr (he : ∀ t : ℝ≥0, (t : ℝ≥0∞) ≤ ζ → η' t = η t) :
    contSet η' ζ a K = contSet η ζ a K := by
  ext t
  constructor
  · rintro ⟨h1, h2, h3⟩
    exact ⟨h1, h2, fun t' a1 a2 => by
      rw [← he t' ((ENNReal.coe_le_coe.2 a2.le).trans h2)]; exact h3 t' a1 a2⟩
  · rintro ⟨h1, h2, h3⟩
    exact ⟨h1, h2, fun t' a1 a2 => by
      rw [he t' ((ENNReal.coe_le_coe.2 a2.le).trans h2)]; exact h3 t' a1 a2⟩

theorem contLife_congr (he : ∀ t : ℝ≥0, (t : ℝ≥0∞) ≤ ζ → η' t = η t) :
    contLife η' ζ a K = contLife η ζ a K := by
  unfold contLife contStop
  rw [contSet_congr he]

theorem contPath_congr {D : Set ℂ} {φ : ℂ → ℂ} {V : ℝ≥0∞}
    (he : ∀ s : ℝ≥0, (s : ℝ≥0∞) < V → η' (a + s) = η (a + s)) : contPath D φ η' a V = contPath D φ η a V := by
  funext r
  by_cases hr : (r : ℝ≥0∞) < V
  · rw [contPath_of_lt hr, contPath_of_lt hr, he r hr]
  · push Not at hr
    rw [contPath_of_le hr, contPath_of_le hr]
    by_cases hV : V = ⊤
    · exact absurd hr (by rw [hV]; exact not_le.2 ENNReal.coe_lt_top)
    · have hev : (fun s => limUnder (𝓝[D] (η' (a + s))) φ) =ᶠ[𝓝[<] V.toNNReal]
          fun s => limUnder (𝓝[D] (η (a + s))) φ := by
        filter_upwards [self_mem_nhdsWithin] with s hs
        rw [he s (by rw [← ENNReal.coe_toNNReal hV]; exact ENNReal.coe_lt_coe.2 hs)]
      have hm := Filter.map_congr hev
      unfold limUnder at hm ⊢
      rw [hm]

end Congr

/-! ### The canonical retained clock -/

/-- **The canonical retained chart path** of a continuation of `η` after `a`, in the chart `φ` translated by `c`,
read in its inverse relative capacity clock and translated back. -/
def canonRetPath (D : Set ℂ) (φ : ℂ → ℂ) (η : ℝ≥0 → ℂ) (ζ : ℝ≥0∞) (a : ℝ≥0) (K : Set ℂ) (c : ℝ) (u : ℝ≥0) :
    ℂ :=
  contPath D (fun z => φ z - c) η a (contLife η ζ a K)
    (invClock (chartClock (contPath D (fun z => φ z - c) η a (contLife η ζ a K))) (contLife η ζ a K) u) + c

/-- **The canonical retained capacity lifetime** of a continuation. -/
def canonRetLife (D : Set ℂ) (φ : ℂ → ℂ) (η : ℝ≥0 → ℂ) (ζ : ℝ≥0∞) (a : ℝ≥0) (K : Set ℂ) (c : ℝ) : ℝ≥0∞ :=
  capLife (chartClock (contPath D (fun z => φ z - c) η a (contLife η ζ a K))) (contLife η ζ a K)

theorem canonRetPath_congr {D : Set ℂ} {φ : ℂ → ℂ} {η η' : ℝ≥0 → ℂ} {ζ : ℝ≥0∞} {a : ℝ≥0} {K : Set ℂ} {c : ℝ}
    (he : ∀ t : ℝ≥0, (t : ℝ≥0∞) ≤ ζ → η' t = η t) :
    canonRetPath D φ η' ζ a K c = canonRetPath D φ η ζ a K c ∧
      canonRetLife D φ η' ζ a K c = canonRetLife D φ η ζ a K c := by
  have hL := contLife_congr (a := a) (K := K) he
  have hP : contPath D (fun z => φ z - c) η' a (contLife η' ζ a K) =
      contPath D (fun z => φ z - c) η a (contLife η ζ a K) := by
    rw [hL]
    refine contPath_congr fun s hs => he _ ?_
    have h1 : ((a + s : ℝ≥0) : ℝ≥0∞) < contStop η ζ a K := coe_add_lt_iff.1 hs
    exact h1.le.trans contStop_le
  refine ⟨funext fun u => ?_, ?_⟩
  · unfold canonRetPath; rw [hP, hL]
  · unfold canonRetLife; rw [hP, hL]

/-! ### The retained clock relation: congruence and monotonicity -/

theorem IsRetainedClock.congr {η η' : ℝ≥0 → ℂ} {ζ : ℝ≥0∞} {a : ℝ≥0} {A A' : Set ℂ} {ψ : ℂ → ℂ}
    {Γ : ℝ≥0 → ℂ} {U : ℝ≥0∞} (h : IsRetainedClock η ζ a A ψ Γ U)
    (he : ∀ t : ℝ≥0, (t : ℝ≥0∞) ≤ ζ → η' t = η t) (hA : A' = A) : IsRetainedClock η' ζ a A' ψ Γ U := by
  subst hA
  obtain ⟨c, σ, hσ, hm, himg, hrel, hH⟩ := h
  refine ⟨c, σ, hσ, hm, ?_, fun s hs => ?_, hH⟩
  · rw [himg]; exact (contSet_congr he).symm
  · have hcs : c s ∈ c '' {s : ℝ≥0 | (s : ℝ≥0∞) ≤ σ} := mem_image_of_mem c hs
    rw [himg] at hcs
    rw [he _ hcs.2.1]
    exact hrel s hs

theorem IsRetainedClock.mono {η : ℝ≥0 → ℂ} {ζ : ℝ≥0∞} {a : ℝ≥0} {A : Set ℂ} {ψ : ℂ → ℂ}
    {Γ Γ' : ℝ≥0 → ℂ} {V U : ℝ≥0∞} (h : IsRetainedClock η ζ a A ψ Γ V) (hVU : V ≤ U)
    (hΓ : ∀ s : ℝ≥0, (s : ℝ≥0∞) ≤ V → Γ' s = Γ s) : IsRetainedClock η ζ a A ψ Γ' U := by
  obtain ⟨c, σ, hσ, hm, himg, hrel, hH⟩ := h
  exact ⟨c, σ, hσ.trans hVU, hm, himg, fun s hs => by rw [hΓ s (hs.trans hσ)]; exact hrel s hs,
    fun s hs => by rw [hΓ s (hs.trans hσ)]; exact hH s hs⟩

/-! ### Translated charts -/

/-- **A chart translated by a real number** is a chart. -/
theorem IsDomChart.shift {K : Set ℂ} {φ ψ : ℂ → ℂ} (hD : IsDomChart K φ ψ) (c : ℝ) :
    IsDomChart K (fun z => φ z - c) (fun w => ψ (w + c)) where
  bijOn_fwd := by
    refine ⟨fun z hz => sub_ofReal_mem_H (hD.bijOn_fwd.mapsTo hz) c,
      fun z₁ h₁ z₂ h₂ he => hD.bijOn_fwd.injOn h₁ h₂ (sub_left_inj.1 he), fun w hw => ?_⟩
    obtain ⟨z, hz, hzw⟩ := hD.bijOn_fwd.surjOn (add_ofReal_mem_H hw c)
    exact ⟨z, hz, by simp only [hzw, add_sub_cancel_right]⟩
  differentiableOn_fwd := hD.differentiableOn_fwd.sub_const _
  cobounded := by
    have h := hD.cobounded
    rw [← tendsto_norm_atTop_iff_cobounded] at h ⊢
    refine tendsto_atTop_mono (fun z => ?_) (tendsto_atTop_add_const_right _ (-‖(c : ℂ)‖) h)
    have := norm_sub_norm_le (φ z) (c : ℂ)
    linarith
  bijOn_inv := by
    refine ⟨fun w hw => hD.bijOn_inv.mapsTo (add_ofReal_mem_H hw c),
      fun w₁ h₁ w₂ h₂ he => add_right_cancel (hD.bijOn_inv.injOn (add_ofReal_mem_H h₁ c) (add_ofReal_mem_H h₂ c) he),
      fun z hz => ?_⟩
    obtain ⟨w, hw, rfl⟩ := hD.bijOn_inv.surjOn hz
    exact ⟨w - c, sub_ofReal_mem_H hw c, by simp only [sub_add_cancel]⟩
  fwd_inv := fun w hw => by simp only [hD.fwd_inv _ (add_ofReal_mem_H hw c), add_sub_cancel_right]
  inv_notMem := fun w hw => hD.inv_notMem _ fun h => hw (by simpa using sub_ofReal_mem_H h c)
  differentiableOn_inv :=
    hD.differentiableOn_inv.comp (differentiableOn_id.add_const _) fun w hw => add_ofReal_mem_H hw c
  continuousOn_inv := hD.continuousOn_inv.comp (continuousOn_id.add continuousOn_const) fun w hw =>
    show 0 ≤ (w + c).im by simpa using (show 0 ≤ w.im from hw)
  bdd := by
    obtain ⟨M, hM⟩ := hD.bdd
    refine ⟨M + ‖(c : ℂ)‖, fun w hw => ?_⟩
    have h1 := hM (w + c) (show 0 ≤ (w + c).im by simpa using (show 0 ≤ w.im from hw))
    calc ‖ψ (w + c) - w‖ = ‖(ψ (w + c) - (w + c)) + c‖ := by ring_nf
      _ ≤ ‖ψ (w + c) - (w + c)‖ + ‖(c : ℂ)‖ := norm_add_le _ _
      _ ≤ M + ‖(c : ℂ)‖ := by linarith

theorem IsDomChart.congr_set {K K' : Set ℂ} {φ ψ : ℂ → ℂ} (hD : IsDomChart K φ ψ) (hK : K = K') :
    IsDomChart K' φ ψ := hK ▸ hD

/-! ### Both continuations of a retained pair -/

section Pair

variable {α β η : ℝ≥0 → ℂ} {ζ : ℝ≥0∞} {x : ℝ} {u r : ℝ≥0} {φ ψ : ℂ → ℂ} {lift : ℂ → ℝ}

/-- The second tip is a regular point of the retained chart. -/
theorem isChartRegularPoint_tip₂ (hc₁ : ContinuousOn α (Icc 0 u)) (hc₂ : ContinuousOn β (Icc 0 r))
    (h0₁ : (α 0).im = 0) (h0₂ : (β 0).im = 0) (hpO : β r ∉ α '' Icc 0 u) (hne : ∀ t < r, β t ≠ β r) :
    IsChartRegularPoint α u β r (β r) := by
  refine Or.inr (isUnboundedLinked_of_forall fun z hz hzq => ?_)
  rcases hz with hz | ⟨t, ht, rfl⟩
  · exact ⟨α '' Icc 0 u, subset_union_left, isPreconnected_Icc.image _ hc₁, hz, hpO, α 0,
      ⟨0, left_mem_Icc.2 zero_le, rfl⟩, h0₁⟩
  · have htr : t < r := lt_of_le_of_ne ht.2 fun h => hzq (by rw [h])
    refine ⟨β '' Ico 0 r, fun w hw => ?_, isPreconnected_Ico.image _ (hc₂.mono Ico_subset_Icc_self),
      ⟨t, ⟨zero_le, htr⟩, rfl⟩, ?_, β 0, ⟨0, ⟨le_rfl, lt_of_le_of_lt zero_le htr⟩, rfl⟩, h0₂⟩
    · obtain ⟨t', ht', rfl⟩ := hw
      exact Or.inr ⟨t', Ico_subset_Icc_self ht', rfl⟩
    · rintro ⟨t', ht', he⟩
      exact hne t' ht'.2 he

/-- The first tip is a regular point of the retained chart. -/
theorem isChartRegularPoint_tip₁ (hc₁ : ContinuousOn α (Icc 0 u)) (hc₂ : ContinuousOn β (Icc 0 r))
    (h0₁ : (α 0).im = 0) (h0₂ : (β 0).im = 0) (hpO : α u ∉ β '' Icc 0 r) (hne : ∀ s < u, α s ≠ α u) :
    IsChartRegularPoint α u β r (α u) := by
  refine Or.inr (isUnboundedLinked_of_forall fun z hz hzq => ?_)
  rcases hz with ⟨s, hs, rfl⟩ | hz
  · have hsu : s < u := lt_of_le_of_ne hs.2 fun h => hzq (by rw [h])
    refine ⟨α '' Ico 0 u, fun w hw => ?_, isPreconnected_Ico.image _ (hc₁.mono Ico_subset_Icc_self),
      ⟨s, ⟨zero_le, hsu⟩, rfl⟩, ?_, α 0, ⟨0, ⟨le_rfl, lt_of_le_of_lt zero_le hsu⟩, rfl⟩, h0₁⟩
    · obtain ⟨s', hs', rfl⟩ := hw
      exact Or.inl ⟨s', Ico_subset_Icc_self hs', rfl⟩
    · rintro ⟨s', hs', he⟩
      exact hne s' hs'.2 he
  · exact ⟨β '' Icc 0 r, subset_union_right, isPreconnected_Icc.image _ hc₂, hz, hpO, β 0,
      ⟨0, left_mem_Icc.2 zero_le, rfl⟩, h0₂⟩

/-- **The second continuation of a retained pair** satisfies `IsRetCont` in the retained chart. -/
theorem isRetCont_snd (hg : IsRetGood α u β r) (hC : IsRetChart α u β r φ ψ lift)
    (hφ : ∃ x₀ : ℝ, ∀ z, φ z = ConformalImage.mapOut (fillH (prefixSet α u β r)) z - x₀)
    (hp : IsPathGood η ζ x) (hβη : ∀ t ≤ r, β t = η t) (hrζ : (r : ℝ≥0∞) < ζ) (hpH : β r ∈ H)
    (hpO : β r ∉ α '' Icc 0 u) (hcl : β r ∈ closure (activeDomain α u β r)) :
    IsRetCont η ζ x r (α '' Icc 0 u) φ ψ := by
  obtain ⟨hc₁, hc₂, -, -, h0₁, h0₂, hne⟩ := hg
  have hKeq : α '' Icc 0 u ∪ η '' Icc 0 r = prefixSet α u β r := by
    rw [prefixSet]
    congr 1
    exact image_congr fun t ht => (hβη t ht.2).symm
  have hK : IsCompact (prefixSet α u β r) := isCompact_prefixSet' hc₁ hc₂
  have hD : activeDomain α u β r = H \ fillH (α '' Icc 0 u ∪ η '' Icc 0 r) := by
    rw [hKeq]; exact activeDomain_eq hK.isClosed
  have hp' : η r = β r := (hβη r le_rfl).symm
  obtain ⟨w, -, -, -, hu⟩ := hC.exists_tendsto_of_regular h0₂ hcl
    (isChartRegularPoint_tip₂ hc₁ hc₂ h0₁ h0₂ hpO hne)
  have hw0 : (0 : ℂ) = w := hu 0 (show (0 : ℝ) ≤ (0 : ℂ).im by simp) (hC.inv_zero h0₂)
  refine ⟨hp, hrζ, isCompact_Icc.image_of_continuousOn hc₁, isPreconnected_image_union_lowerHalf hc₁ h0₁.le,
    by rw [hp']; exact hpH, by rw [hp']; exact hpO, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hp', ← hD]; exact hcl
  · rw [hKeq]; exact hC.isDomChart h0₂ hK.isClosed
  · rw [hKeq]; exact hφ
  · rw [hp', ← hD]; exact (hC.isActiveChart h0₂).2.2.1
  · rw [hp']; exact hC.inv_zero h0₂
  · intro w' hw' he
    rw [hp'] at he
    exact (hu w' hw' he).trans hw0.symm
  · intro z hz hzK
    rw [← hD] at hz ⊢
    rw [hKeq] at hzK
    exact hC.exists_tendsto_of_regular h0₂ hz (isChartRegularPoint_of_notMem hc₁ hc₂ h0₁ h0₂ hzK)

/-- **The first continuation of a retained pair** satisfies `IsRetCont` in the retained chart translated by the
real chart position `w₁` of the first tip (its forward chart limit). -/
theorem isRetCont_fst (hg : IsRetGood α u β r) (hC : IsRetChart α u β r φ ψ lift)
    (hφ : ∃ x₀ : ℝ, ∀ z, φ z = ConformalImage.mapOut (fillH (prefixSet α u β r)) z - x₀)
    (hp : IsPathGood η ζ x) (hαη : ∀ s ≤ u, α s = η s) (huζ : (u : ℝ≥0∞) < ζ) (hpH : α u ∈ H)
    (hpO : α u ∉ β '' Icc 0 r) (hcl : α u ∈ closure (activeDomain α u β r)) (hne₁ : ∀ s < u, α s ≠ α u) :
    ∃ w₁ : ℝ, Tendsto φ (𝓝[activeDomain α u β r] (α u)) (𝓝 (w₁ : ℂ)) ∧
      IsRetCont η ζ x u (β '' Icc 0 r) (fun z => φ z - w₁) (fun w => ψ (w + w₁)) := by
  obtain ⟨hc₁, hc₂, -, -, h0₁, h0₂, -⟩ := hg
  have hK := isCompact_prefixSet' hc₁ hc₂
  have hKeq : β '' Icc 0 r ∪ η '' Icc 0 u = prefixSet α u β r := by
    rw [prefixSet, union_comm]
    congr 1
    exact image_congr fun s hs => (hαη s hs.2).symm
  have hD : activeDomain α u β r = H \ fillH (β '' Icc 0 r ∪ η '' Icc 0 u) := by
    rw [hKeq]; exact activeDomain_eq hK.isClosed
  obtain ⟨w, hwH, hwt, hwψ, hwu⟩ := hC.exists_tendsto_of_regular h0₂ hcl
    (isChartRegularPoint_tip₁ hc₁ hc₂ h0₁ h0₂ hpO hne₁)
  have hwR : w.im = 0 := by
    by_contra hne
    have hwH' : w ∈ H := lt_of_le_of_ne hwH (Ne.symm hne)
    have hmem := (hC.bijOn h0₂).mapsTo hwH'
    rw [hwψ, activeDomain_eq hK.isClosed] at hmem
    exact hmem.2 (mem_fillH_of_mem_closure hmem.1 (subset_closure (Or.inl ⟨u, ⟨zero_le, le_rfl⟩, rfl⟩)))
  have hw : w = ((w.re : ℝ) : ℂ) := (eq_ofReal_re_of_im_eq_zero hwR).symm
  set w₁ : ℝ := w.re with hw₁
  have hp' : η u = α u := (hαη u le_rfl).symm
  have hHbar : ∀ v : ℂ, v ∈ Hbar → ∀ y : ℝ, v + y ∈ Hbar := fun v hv y =>
    show 0 ≤ (v + y).im by simpa using (show 0 ≤ v.im from hv)
  refine ⟨w₁, by rw [← hw]; exact hwt, hp, huζ, isCompact_Icc.image_of_continuousOn hc₂,
    isPreconnected_image_union_lowerHalf hc₂ h0₂.le, by rw [hp']; exact hpH, by rw [hp']; exact hpO, ?_, ?_, ?_,
    ?_, ?_, ?_, ?_⟩
  · rw [hp', ← hD]; exact hcl
  · rw [hKeq]; exact (hC.isDomChart h0₂ hK.isClosed).shift w₁
  · obtain ⟨x₀, hx₀⟩ := hφ
    refine ⟨x₀ + w₁, fun z => ?_⟩
    rw [hKeq, hx₀ z]
    push_cast
    ring
  · rw [hp', ← hD, ← hw]
    have h1 := hwt.sub_const w
    rwa [sub_self] at h1
  · show ψ (0 + w₁) = η u
    rw [zero_add, ← hw, hwψ, hp']
  · intro w' hw' he
    have h2 := hwu _ (hHbar w' hw' w₁) (by rw [he, hp'])
    rw [hw] at h2
    linear_combination h2
  · intro z hz hzK
    rw [← hD] at hz ⊢
    rw [hKeq] at hzK
    obtain ⟨w₀, hw₀H, hw₀t, hw₀ψ, hw₀u⟩ := hC.exists_tendsto_of_regular h0₂ hz
      (isChartRegularPoint_of_notMem hc₁ hc₂ h0₁ h0₂ hzK)
    refine ⟨w₀ - w₁, show 0 ≤ (w₀ - w₁).im by simpa using (show 0 ≤ w₀.im from hw₀H), hw₀t.sub_const _,
      by simp only [sub_add_cancel]; exact hw₀ψ, fun w' hw' he => ?_⟩
    have h3 := hw₀u _ (hHbar w' hw' w₁) he
    rw [← h3]
    ring

/-- `IsRetCont` with the chart translated by `0`. -/
theorem IsRetCont.shift_zero {a : ℝ≥0} {O : Set ℂ} (hR : IsRetCont η ζ x a O φ ψ) :
    IsRetCont η ζ x a O (fun z => φ z - ((0 : ℝ) : ℂ)) (fun w => ψ (w + ((0 : ℝ) : ℂ))) := by
  have e1 : (fun z => φ z - ((0 : ℝ) : ℂ)) = φ := funext fun z => by simp
  have e2 : (fun w => ψ (w + ((0 : ℝ) : ℂ))) = ψ := funext fun w => by simp
  rw [e1, e2]
  exact hR

/-- **The canonical retained clock satisfies the clock relation** of `RetainedPairRestartStatement`. -/
theorem isRetainedClock_canon {a : ℝ≥0} {O A D : Set ℂ} {c : ℝ}
    (hR : IsRetCont η ζ x a O (fun z => φ z - c) (fun w => ψ (w + c))) (hA : O ∪ η '' Icc 0 a = A)
    (hD : D = H \ fillH A) :
    IsRetainedClock η ζ a A ψ (canonRetPath D φ η ζ a A c) (canonRetLife D φ η ζ a A c) := by
  subst hA hD
  exact hR.isRetainedClock c (ψ' := ψ) fun _ => rfl

end Pair

end Supp7

end InteractingSLE
