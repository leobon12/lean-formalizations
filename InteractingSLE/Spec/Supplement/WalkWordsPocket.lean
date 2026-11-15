/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.WalkWordsOrient
import InteractingSLE.Spec.Supplement.GW3Orient
import InteractingSLE.Spec.Sec7.Aux37SideSign
import InteractingSLE.Spec.Supplement.GW3SidedProof

/-!
# The walk order of the pocket chart of a component between two ordered walls

Packet PROVE-WALK-WORDS (the input `WalkComponentWalkOrderStatement`: Lemma GW3's "incoming orientation" of the
component charts). PROVE-ORIENT's chart of a component between two simple proper walls `R`, `L` (`L` on the closed left
side of `R`) is the two-point uniformizer `Ψ ∘ cayley` of the marked pocket
(`GW3.hasOrientedUniformizer_of_mem_betweenComponents`), whose inverse extends continuously and **injectively** to `ℍ̄`
(`Sec7.Prop74B.pocketInv_boundary`), sends `0` to the first contact `R(a)` and `±∞` to the last contact `R(b)` (or to
`∞`): `exists_pocketExt`. This file shows that this chart orders the walls:

* `lt_time_of_injOn` (generic): a continuous injective boundary map on `[0, ∞)` into a proper curve `γ`, with one
  point later than the image of `0`, increases the curve's parameter;
* **`exists_pocketChart_walkOrder`**: the chart's landings at `0 < x < x'` are `R(t)`, `R(t')` with `t < t'`, and at
  `x < x' < 0` they are `L(s)`, `L(s')` with `s' < s` (for the latter, the contact order of the two walls at the two
  ends of the pocket).

No winding number enters: only injectivity of the boundary map and the two ends.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Complex Set Filter Topology Function Bornology Metric
open QuantumZipper (H Hbar isOpen_H)
open QuantumZipper.CA (cayley cayleyInv)
open SupercriticalConformalCovariance (IsConformalBijection)
open scoped NNReal ENNReal Real

namespace InteractingSLE.Theorem14.WalkWords

/-! ### A continuous injective boundary map increases the curve parameter -/

/-- **Generic order lemma.** -/
theorem lt_time_of_injOn {γ : ℝ≥0 → ℂ} (hγ : IsClosedEmbedding γ) {G : ℝ → ℂ} (hGc : ContinuousOn G (Ici 0))
    (hGi : InjOn G (Ici 0)) (hG : ∀ x : ℝ, 0 ≤ x → G x ∈ range γ) {t₀ : ℝ≥0} (h0 : G 0 = γ t₀)
    (hfar : ∃ x₁ : ℝ, 0 < x₁ ∧ ∃ t₁ : ℝ≥0, G x₁ = γ t₁ ∧ t₀ < t₁) {x x' : ℝ} (hx : 0 < x) (hxx' : x < x')
    {t t' : ℝ≥0} (ht : G x = γ t) (ht' : G x' = γ t') : t < t' := by
  classical
  set g : ℝ → ℝ≥0 := fun y => invFun γ (G y) with hgdef
  have hgG : ∀ y : ℝ, 0 ≤ y → γ (g y) = G y := fun y hy => invFun_eq (hG y hy)
  have hgc : ContinuousOn g (Ici 0) := by
    rw [hγ.isInducing.continuousOn_iff]
    exact hGc.congr fun y hy => hgG y hy
  set T : ℝ → ℝ := fun y => (g y : ℝ) with hTdef
  have hTc : ContinuousOn T (Ici 0) := NNReal.continuous_coe.comp_continuousOn hgc
  have hTi : InjOn T (Ici 0) := by
    intro y hy y' hy' he
    have he' : g y = g y' := NNReal.coe_injective he
    have := congrArg γ he'
    rw [hgG y hy, hgG y' hy'] at this
    exact hGi hy hy' this
  have hTeq : ∀ y : ℝ, 0 ≤ y → ∀ s : ℝ≥0, G y = γ s → T y = s := fun y hy s hs => by
    have h1 : γ (g y) = γ s := (hgG y hy).trans hs
    rw [hTdef]; simp only; rw [hγ.injective h1]
  obtain ⟨x₁, hx₁, t₁, hG₁, ht₁⟩ := hfar
  set M : ℝ := max x' x₁ with hM
  have hmono : StrictMonoOn T (Icc 0 M) := by
    refine Sec7.Aux37Side.strictMonoOn_of_pair (le_max_of_le_right hx₁.le) (hTc.mono fun y hy => hy.1)
      (hTi.mono fun y hy => hy.1) (u₁ := 0) (u₂ := x₁) ⟨le_rfl, le_max_of_le_right hx₁.le⟩
      ⟨hx₁.le, le_max_right _ _⟩ hx₁ ?_
    rw [hTeq 0 le_rfl t₀ h0, hTeq x₁ hx₁.le t₁ hG₁]
    exact_mod_cast ht₁
  have h := hmono ⟨hx.le, (hxx'.le.trans (le_max_left _ _))⟩ ⟨(hx.trans hxx').le, le_max_left _ _⟩ hxx'
  rw [hTeq x hx.le t ht, hTeq x' (hx.trans hxx').le t' ht'] at h
  exact_mod_cast h

/-! ### The extended inverse of the pocket chart -/

open Sec7.Lemma71K (IsMarkedPocket wallPt)
open Sec7.Prop74B (pocketInv pocketInv_boundary pocketChartOrientationStatement)

/-- `‖cayleyInv w‖ → ∞` as `w → 1`. -/
theorem tendsto_norm_cayleyInv : Tendsto (fun w => ‖cayleyInv w‖) (𝓝[≠] (1 : ℂ)) atTop := by
  have h1 : Tendsto (fun w : ℂ => ‖w - 1‖⁻¹) (𝓝[≠] (1 : ℂ)) atTop :=
    tendsto_inv_nhdsGT_zero.comp (tendsto_norm_sub_self_nhdsNE 1)
  refine tendsto_atTop_mono' _ ?_ h1
  have hev : ∀ᶠ w in 𝓝[≠] (1 : ℂ), ‖w - 1‖ ≤ 1 := by
    refine nhdsWithin_le_nhds ?_
    filter_upwards [Metric.closedBall_mem_nhds (1 : ℂ) one_pos] with w hw
    rwa [mem_closedBall, dist_eq_norm] at hw
  filter_upwards [hev, self_mem_nhdsWithin] with w hw hw1
  have := Sec7.Prop74B.one_div_le_norm_cayleyInv hw1 hw
  rwa [one_div] at this

/-- The inverse of a boundary map on `E = cl(cayley C) ∖ {q}` tends to `q` at `±∞`. -/
theorem tendsto_invFunOn_cocompact {C : Set ℂ} {Ψ : ℂ → ℂ} {q : ℂ} (hCH : C ⊆ H)
    (hΨc : ContinuousOn Ψ (closure (cayley '' C) \ {q}))
    (hspec : ∀ y : ℝ, invFunOn Ψ (closure (cayley '' C) \ {q}) y ∈ closure (cayley '' C) \ {q} ∧
      Ψ (invFunOn Ψ (closure (cayley '' C) \ {q}) y) = y) :
    Tendsto (fun y : ℝ => invFunOn Ψ (closure (cayley '' C) \ {q}) y) (cocompact ℝ) (𝓝 q) := by
  rw [Metric.tendsto_nhds]
  intro ε hε
  have hK : IsCompact (closure (cayley '' C) \ ball q ε) :=
    (Sec7.Prop74B.isCompact_closure_cayley_image hCH).diff isOpen_ball
  have hKE : closure (cayley '' C) \ ball q ε ⊆ closure (cayley '' C) \ {q} := fun y hy =>
    ⟨hy.1, fun hyq => hy.2 (by rw [mem_singleton_iff.1 hyq]; exact mem_ball_self hε)⟩
  obtain ⟨M, hM⟩ := hK.exists_bound_of_continuousOn (hΨc.mono hKE)
  filter_upwards [(isCompact_closedBall (0 : ℝ) M).compl_mem_cocompact] with y hy
  obtain ⟨hyE, hyΨ⟩ := hspec y
  by_contra hfar
  have hyK : invFunOn Ψ (closure (cayley '' C) \ {q}) (y : ℂ) ∈ closure (cayley '' C) \ ball q ε :=
    ⟨hyE.1, fun hb => hfar (mem_ball.1 hb)⟩
  have h := hM _ hyK
  rw [hyΨ, Complex.norm_real] at h
  exact hy (mem_closedBall_zero_iff.2 h)

/-- **The extended inverse of the pocket chart** (PROVE-ORIENT's two-point uniformizer of the marked pocket): a
conformal bijection `f : C → ℍ` whose inverse extends to a continuous injective `G` on `ℍ̄`, sending the negative
half-line into `L` and the positive one into `R`, with `G 0 = R t₀` (the first contact) and, at `±∞`, either a later
point `R t₁` of the right wall (bounded pocket) or `∞`. -/
theorem exists_pocketExt {R L : ℝ≥0 → ℂ} (hR : Sec7.Lemma71I.IsSimpleProper R)
    (hL : Sec7.Lemma71I.IsSimpleProper L) (hLR : range L ⊆ closedLeftSide R) {C : Set ℂ}
    (hC : C ∈ betweenComponents (range R) (range L)) :
    ∃ f G : ℂ → ℂ, IsConformalBijection f C H ∧ ContinuousOn G Hbar ∧ InjOn G Hbar ∧
      (∀ w ∈ H, ∀ z ∈ C, f z = w → G w = z) ∧ (∀ x : ℝ, x < 0 → G x ∈ range L) ∧
      (∀ x : ℝ, 0 < x → G x ∈ range R) ∧ ∃ t₀ : ℝ≥0, G 0 = R t₀ ∧
        ((∃ t₁ : ℝ≥0, t₀ < t₁ ∧ Tendsto (fun y : ℝ => G y) (cocompact ℝ) (𝓝 (R t₁))) ∨
          Tendsto (fun y : ℝ => ‖G y‖) (cocompact ℝ) atTop) := by
  have hCsub := Sec7.Prop74B.subset_of_mem_betweenComponents hC
  have hCH : C ⊆ H := fun z hz => (hCsub hz).1
  have hRc : IsClosed (range R) :=
    Sec7.Lemma71I.arcRange_realPath R ▸ (Sec7.Lemma71I.IsSimpleProper.isProperArc hR).isClosed_arcRange
  have hLc : IsClosed (range L) :=
    Sec7.Lemma71I.arcRange_realPath L ▸ (Sec7.Lemma71I.IsSimpleProper.isProperArc hL).isClosed_arcRange
  obtain ⟨z₀, hz₀, -, -, hCz⟩ := id hC
  have hCo : IsOpen C := hCz ▸ (isOpen_H.sdiff (hRc.union hLc)).connectedComponentIn
  have hCc : IsConnected C := hCz ▸ isConnected_connectedComponentIn_iff.2 hz₀
  have hord := Sec7.Lemma71I.disjoint_rightSideOf_of_subset_closedLeftSide hR.isProperCurve hR.2.2.1 hLR
  obtain ⟨a, b, hM⟩ := Sec7.Lemma71K.isMarkedPocket_of_mem_betweenComponents hR hL hord hC
  obtain ⟨ha0, hab, hb1, hI, hJ, hpa, hpb, hpq⟩ := id hM
  obtain ⟨Ψ, hΨ, hΨc, hΨi, hΨH, hΨ0, hΨinf⟩ := Sec7.Lemma71F.exists_twoPoint_uniformizer_ext_of_jordan
    (Sec7.Lemma71F.isOpen_cayley_image hCo hCH) (Sec7.Lemma71F.isConnected_cayley_image hCc hCH)
    (Sec7.Lemma71F.isBounded_cayley_image hCH) hJ hpa hpb hpq
  have hf : IsConformalBijection (Ψ ∘ cayley) C H :=
    isConformalBijection_comp hΨ (Sec7.Lemma71F.isConformalBijection_cayley_image hCH)
  have hΨf : ∀ x ∈ C, (Ψ ∘ cayley) x = Ψ (cayley x) := fun _ _ => rfl
  have hor := pocketChartOrientationStatement R L hR hL hLR C hC a b hM (Ψ ∘ cayley) Ψ hf hΨc hΨi hΨH hΨ0 hΨinf
    hΨf
  obtain ⟨hGc, hGi, hGinv, hGL, hGR, -⟩ :=
    pocketInv_boundary hR hL hLR hCo hC hM hf hΨc hΨi hΨH hΨ0 hΨinf hΨf hor
  have hRim : ∀ t, 0 ≤ (R t).im := hR.isProperCurve.2.2.1
  have hqC : ∀ x ∈ C, cayley x ≠ wallPt R b := fun x hx h =>
    (hCsub hx).2 (Or.inl (Sec7.Prop74B.mem_range_of_cayley_eq_toDisc hRim
      (Sec7.Prop74B.mem_Hbar_of_mem_H (hCH hx)) h))
  have hspec := fun {w : ℂ} (hw : w ∈ Hbar) =>
    Sec7.Prop74B.invFunOn_boundaryMap_spec hCH hf hqC hΨc hΨH hΨinf hΨf hw
  have hxH : ∀ x : ℝ, (x : ℂ) ∈ Hbar := fun x => show (0 : ℝ) ≤ (x : ℂ).im by simp
  have hwR : ∀ s : ℝ, s < 1 → wallPt R s = cayley (R (WangWu.arcTime s).toNNReal) := fun s hs =>
    WangWu.toDisc_of_lt hs
  have haE : wallPt R a ∈ closure (cayley '' C) \ {wallPt R b} := by
    have h : a ∈ {s ∈ Icc (0 : ℝ) 1 | wallPt R s ∈ closure (cayley '' C)} := by
      rw [hI]; exact ⟨le_rfl, hab.le⟩
    exact ⟨h.2, hpq⟩
  have h0 : invFunOn Ψ (closure (cayley '' C) \ {wallPt R b}) 0 = wallPt R a := by
    have h := hspec (show (0 : ℂ) ∈ Hbar from show (0 : ℝ) ≤ (0 : ℂ).im by simp)
    exact hΨi h.1 haE (h.2.trans hΨ0.symm)
  refine ⟨Ψ ∘ cayley, pocketInv Ψ (closure (cayley '' C) \ {wallPt R b}), hf, hGc, hGi, hGinv, hGL, hGR,
    (WangWu.arcTime a).toNNReal, ?_, ?_⟩
  · show cayleyInv (invFunOn Ψ (closure (cayley '' C) \ {wallPt R b}) 0) = _
    rw [h0, hwR a (hab.trans_le hb1), WangWu.cayleyInv_cayley_of_mem_Hbar (hRim _)]
  · have hT := tendsto_invFunOn_cocompact hCH hΨc (fun y => hspec (hxH y))
    rcases hb1.lt_or_eq with hb | hb
    · left
      have hlt : WangWu.arcTime a < WangWu.arcTime b :=
        WangWu.strictMonoOn_arcTime ⟨ha0, hab.trans hb⟩ ⟨ha0.trans hab.le, hb⟩ hab
      refine ⟨(WangWu.arcTime b).toNNReal, (Real.toNNReal_lt_toNNReal_iff
        ((WangWu.arcTime_nonneg ⟨ha0, hab.trans hb⟩).trans_lt hlt)).2 hlt, ?_⟩
      have hq1 : wallPt R b ≠ 1 := by rw [hwR b hb]; exact WangWu.cayley_ne_one_of_Hbar (hRim _)
      have hval : cayleyInv (wallPt R b) = R (WangWu.arcTime b).toNNReal := by
        rw [hwR b hb, WangWu.cayleyInv_cayley_of_mem_Hbar (hRim _)]
      have h := (WangWu.continuousAt_cayleyInv hq1).tendsto.comp hT
      rw [hval] at h
      exact h
    · right
      have hq : wallPt R b = 1 := by rw [hb]; exact WangWu.toDisc_one _
      have hT' : Tendsto (fun y : ℝ => invFunOn Ψ (closure (cayley '' C) \ {wallPt R b}) y) (cocompact ℝ)
          (𝓝[≠] 1) := by
        refine tendsto_nhdsWithin_iff.2 ⟨hq ▸ hT, Eventually.of_forall fun y h1 => ?_⟩
        refine (hspec (hxH y)).1.2 ?_
        rw [mem_singleton_iff] at h1 ⊢
        rw [h1, hq]
      exact tendsto_norm_cayleyInv.comp hT'

/-! ### The walk order of the extended inverse -/

/-- A map whose norm tends to `∞` eventually leaves any compact set. -/
theorem eventually_notMem_of_tendsto_norm {α : Type*} {l : Filter α} {g : α → ℂ} {K : Set ℂ} (hK : IsCompact K)
    (h : Tendsto (fun y => ‖g y‖) l atTop) : ∀ᶠ y in l, g y ∉ K := by
  obtain ⟨M, hM⟩ := hK.isBounded.exists_norm_le
  filter_upwards [h.eventually_gt_atTop M] with y hy hyK
  exact absurd (hM _ hyK) (not_le.2 hy)

/-- **The walk order of the extended inverse**: along the right wall the parameter increases on the positive
half-line, along the left wall it decreases on the negative half-line (the latter from the contact order at the two
ends of a bounded pocket). -/
theorem walkOrder_of_pocketExt {R L : ℝ≥0 → ℂ} (hR : Sec7.Lemma71I.IsSimpleProper R)
    (hL : Sec7.Lemma71I.IsSimpleProper L)
    (hco : ∀ s s' t t' : ℝ≥0, R s = L t → R s' = L t' → (s < s' ↔ t < t')) {G : ℂ → ℂ}
    (hGc : ContinuousOn G Hbar) (hGi : InjOn G Hbar) (hGL : ∀ x : ℝ, x < 0 → G x ∈ range L)
    (hGR : ∀ x : ℝ, 0 < x → G x ∈ range R) {t₀ : ℝ≥0} (h0 : G 0 = R t₀)
    (hfar : (∃ t₁ : ℝ≥0, t₀ < t₁ ∧ Tendsto (fun y : ℝ => G y) (cocompact ℝ) (𝓝 (R t₁))) ∨
      Tendsto (fun y : ℝ => ‖G y‖) (cocompact ℝ) atTop) :
    (∀ (x x' : ℝ) (v v' : ℝ≥0), 0 < x → x < x' → G x = R v → G x' = R v' → v < v') ∧
      (∀ (x x' : ℝ) (v v' : ℝ≥0), x < x' → x' < 0 → G x = L v → G x' = L v' → v' < v) := by
  have hxH : ∀ x : ℝ, (x : ℂ) ∈ Hbar := fun x => show (0 : ℝ) ≤ (x : ℂ).im by simp
  have hGr : ContinuousOn (fun y : ℝ => G y) univ :=
    hGc.comp continuous_ofReal.continuousOn fun y _ => hxH y
  have hGcont : Continuous (fun y : ℝ => G y) := continuousOn_univ.1 hGr
  have hGri : Injective (fun y : ℝ => G y) := fun y y' h => ofReal_injective (hGi (hxH y) (hxH y') h)
  have hRe := WalkCont.isClosedEmbedding_of_isProperCurve hR.isProperCurve
  have hLe := WalkCont.isClosedEmbedding_of_isProperCurve hL.isProperCurve
  -- the base point lies on the left wall too
  have h0L : G 0 ∈ range L := by
    have ht : Tendsto (fun y : ℝ => G y) (𝓝[<] 0) (𝓝 (G 0)) := by
      have := (hGcont.tendsto 0).mono_left (nhdsWithin_le_nhds (s := Iio 0))
      simpa only [ofReal_zero] using this
    exact hLe.isClosed_range.mem_of_tendsto ht (eventually_nhdsWithin_of_forall fun y hy => hGL y hy)
  obtain ⟨u₀, hu₀⟩ := h0L
  -- far from the two initial arcs at `±∞`
  have hfarRL : (∀ᶠ y : ℝ in cocompact ℝ, G (y : ℂ) ∉ R '' Icc 0 t₀) ∧
      ∀ᶠ y : ℝ in cocompact ℝ, G (y : ℂ) ∉ L '' Icc 0 u₀ := by
    rcases hfar with ⟨t₁, ht₁, hT⟩ | hT
    · obtain ⟨u₁, hu₁⟩ : R t₁ ∈ range L :=
        hLe.isClosed_range.mem_of_tendsto (hT.mono_left atBot_le_cocompact)
          ((eventually_lt_atBot (0 : ℝ)).mono fun y hy => hGL y hy)
      have hu : u₀ < u₁ := (hco t₀ t₁ u₀ u₁ (h0.symm.trans hu₀.symm) hu₁.symm).1 ht₁
      refine ⟨hT.eventually ((isCompact_Icc.image hR.1).isClosed.isOpen_compl.mem_nhds ?_),
        (show Tendsto (fun y : ℝ => G y) (cocompact ℝ) (𝓝 (L u₁)) by rw [hu₁]; exact hT).eventually
          ((isCompact_Icc.image hL.1).isClosed.isOpen_compl.mem_nhds ?_)⟩
      · rintro ⟨s, hs, hse⟩
        exact absurd (hR.2.1 hse ▸ hs.2) (not_le.2 ht₁)
      · rintro ⟨s, hs, hse⟩
        exact absurd (hL.2.1 hse ▸ hs.2) (not_le.2 hu)
    · exact ⟨eventually_notMem_of_tendsto_norm (isCompact_Icc.image hR.1) hT,
        eventually_notMem_of_tendsto_norm (isCompact_Icc.image hL.1) hT⟩
  obtain ⟨hfR, hfL⟩ := hfarRL
  refine ⟨fun x x' v v' hx hxx' hv hv' => ?_, fun x x' v v' hxx' hx' hv hv' => ?_⟩
  · refine lt_time_of_injOn hRe (G := fun y : ℝ => G y) (hGr.mono (subset_univ _)) hGri.injOn ?_
      (show G ((0 : ℝ) : ℂ) = R t₀ by rw [ofReal_zero]; exact h0) ?_ hx hxx' hv hv'
    · intro y hy
      show G (y : ℂ) ∈ range R
      rcases hy.lt_or_eq with hy | hy
      · exact hGR y hy
      · rw [← hy, ofReal_zero, h0]; exact ⟨t₀, rfl⟩
    · obtain ⟨y, hyK, hy⟩ := ((hfR.filter_mono atTop_le_cocompact).and (eventually_gt_atTop (0 : ℝ))).exists
      obtain ⟨t₁, ht₁⟩ := hGR y hy
      refine ⟨y, hy, t₁, ht₁.symm, ?_⟩
      by_contra hle
      exact hyK ⟨t₁, ⟨by positivity, not_lt.1 hle⟩, ht₁⟩
  · have hneg : ∀ y : ℝ, 0 ≤ y → G ((-y : ℝ) : ℂ) ∈ range L := fun y hy => by
      rcases hy.lt_or_eq with hy | hy
      · exact hGL (-y) (neg_lt_zero.2 hy)
      · rw [← hy, neg_zero, ofReal_zero, ← hu₀]; exact ⟨u₀, rfl⟩
    have hc : ContinuousOn (fun y : ℝ => G ((-y : ℝ) : ℂ)) (Ici 0) :=
      (hGcont.comp continuous_neg).continuousOn
    have hi : InjOn (fun y : ℝ => G ((-y : ℝ) : ℂ)) (Ici 0) := fun y _ y' _ h => neg_injective (hGri h)
    refine lt_time_of_injOn hLe hc hi hneg (t₀ := u₀) (by simp only [neg_zero, ofReal_zero]; exact hu₀.symm) ?_
      (neg_pos.2 hx') (neg_lt_neg hxx') (by simp only [neg_neg]; exact hv') (by simp only [neg_neg]; exact hv)
    obtain ⟨y, hyK, hy⟩ := ((hfL.filter_mono atBot_le_cocompact).and (eventually_lt_atBot (0 : ℝ))).exists
    obtain ⟨u₁, hu₁⟩ := hGL y hy
    refine ⟨-y, neg_pos.2 hy, u₁, by simp only [neg_neg]; exact hu₁.symm, ?_⟩
    by_contra hle
    exact hyK ⟨u₁, ⟨by positivity, not_lt.1 hle⟩, hu₁⟩

end InteractingSLE.Theorem14.WalkWords
