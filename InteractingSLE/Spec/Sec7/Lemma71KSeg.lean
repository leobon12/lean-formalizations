/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.Lemma71KChart
import InteractingSLE.Spec.Sec7.Lemma71ETop

/-!
# Lemma 7.1's mapped middle-curve segment

Packet PROVE-LEMMA71K. Specification §7.1 (`source/spec/p193-240.md` L576–L606, pp. 223–224, with Remark 6.14):
"the middle curve traverses `C` from `x₀` to `y₀`; its image under `ψ` is a continuous simple curve in `ℍ̄` from `0` to
`∞` whose real-boundary times have empty interior".

Everything is done in the compactified (Cayley) picture, where the pocket is the Jordan domain `U = cayley '' C` and
the middle curve is the crosscut `M̃ = toDisc M`. The traversal interval `[σ, τ]` of
`WangWu.IsOrderedArcs.traverse_disc`
is recovered by the measurable rational-time rule of `Lemma71KMarked` (`openTime`/`closeTime` of the middle curve), and
the mapped segment is `u ↦ Ψ (M̃ (segClock σ τ u))` for the boundary map `Ψ` of the chart.

* `segPt M U u`: the middle-curve point `M̃ (segClock σ τ u)` with `σ, τ` the rational traversal times of `U`;
* **`isSegCurve_of_isMarkedPocket`** (deterministic): on three ordered arcs with no common arc of the middle curve with
  either wall, for every component `C` between the walls which is a marked pocket `[a, b]` of the right wall, and every
  boundary map `Ψ` of `C` (continuous and injective on `closure (cayley '' C) ∖ {α̃ b}`, `ℍ̄`-valued, `Ψ (α̃ a) = 0`,
  `|Ψ| → ∞` at `α̃ b`, `Ψ (cayley C) ⊆ ℍ`), the mapped segment is an `IsSegCurve` and its points lie in
  `closure (cayley '' C) ∖ {α̃ b}`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology Metric Complex Bornology
open scoped NNReal ENNReal Real

namespace InteractingSLE.Sec7.Lemma71K

open QuantumZipper (H Hbar)
open QuantumZipper.CA (cayley cayleyInv)

/-- The middle-curve point at segment time `u`: `M̃ (segClock σ τ u)`, with `σ`, `τ` the rational traversal times of
the middle curve through `U`. -/
def segPt (M : ℝ≥0 → ℂ) (U : Set ℂ) (u : ℝ) : ℂ :=
  wallPt M (Lemma71.segClock (openTime M U) (closeTime M U) u)

/-- **The mapped segment of a marked pocket is a segment curve** (Lemma 7.1, pp. 223–224; Remark 6.14). -/
theorem isSegCurve_of_isMarkedPocket {R M L : ℝ≥0 → ℂ}
    (h : WangWu.IsOrderedArcs (Lemma71I.realPath R) (Lemma71I.realPath M) (Lemma71I.realPath L))
    (hcR : interior {t ∈ Ici (0 : ℝ) | Lemma71I.realPath M t ∈ WangWu.arcRange (Lemma71I.realPath R)} = ∅)
    (hcL : interior {t ∈ Ici (0 : ℝ) | Lemma71I.realPath M t ∈ WangWu.arcRange (Lemma71I.realPath L)} = ∅)
    {C : Set ℂ} (hC : C ∈ betweenComponents (range R) (range L)) {a b : ℝ} (hM : IsMarkedPocket R C a b)
    {Ψ : ℂ → ℂ} (hΨc : ContinuousOn Ψ (closure (cayley '' C) \ {wallPt R b}))
    (hΨi : InjOn Ψ (closure (cayley '' C) \ {wallPt R b}))
    (hΨH : MapsTo Ψ (closure (cayley '' C) \ {wallPt R b}) Hbar) (hΨ0 : Ψ (wallPt R a) = 0)
    (hΨinf : Tendsto (fun x => ‖Ψ x‖) (𝓝[closure (cayley '' C) \ {wallPt R b}] (wallPt R b)) atTop)
    (hΨC : ∀ z ∈ C, Ψ (cayley z) ∈ H) :
    0 ≤ openTime M (closure (cayley '' C)) ∧
      openTime M (closure (cayley '' C)) < closeTime M (closure (cayley '' C)) ∧
      closeTime M (closure (cayley '' C)) ≤ 1 ∧
      (∀ u, 0 ≤ u → segPt M (closure (cayley '' C)) u ∈ closure (cayley '' C) \ {wallPt R b}) ∧
      Lemma71C.IsSegCurve (fun u => Ψ (segPt M (closure (cayley '' C)) u)) ∧
      (fun u => Ψ (segPt M (closure (cayley '' C)) u)) '' Ici 0 =
        Ψ '' (cayley '' range M ∩ (closure (cayley '' C) \ {wallPt R b})) := by
  rw [← Lemma71I.arcRange_realPath R, ← Lemma71I.arcRange_realPath L] at hC
  obtain ⟨a₁, b₁, hg, hCU, σ, τ, hσ0, hστ, hτ1, hσa, hτb, hin, hout, hint⟩ := h.traverse_disc hcR hcL hC
  have hα := h.right.isDiscCrosscut_toDisc
  have hβ := h.left.isDiscCrosscut_toDisc
  have hμ := h.middle.isDiscCrosscut_toDisc
  have hord' := (WangWu.disjoint_rightSideOf_iff h.right h.left).1 h.right_left
  set U := cayley '' C with hU
  rw [← hCU] at hin hout hint
  -- the gap of the traversal is the marked interval
  have hI₁ := wallTimes_eq_Icc_of_contactGap hα hβ hord' hg
  rw [← hCU] at hI₁
  obtain ⟨ha0, hab, hb1, hI, -, -, -, -⟩ := hM
  have hIeq : Icc a₁ b₁ = Icc a b := hI₁.symm.trans hI
  obtain ⟨ha₁, hb₁⟩ := (Icc_eq_Icc_iff hg.2.2.1.le).1 hIeq
  rw [ha₁] at hσa
  rw [hb₁] at hτb
  -- the rational traversal times are `σ`, `τ`
  have hIM : {t ∈ Icc (0 : ℝ) 1 | wallPt M t ∈ closure U} = Icc σ τ := by
    ext t
    constructor
    · rintro ⟨ht01, htU⟩
      by_contra hnot
      exact hout t ht01 hnot htU
    · intro ht
      exact ⟨⟨hσ0.trans ht.1, ht.2.trans hτ1⟩, hin t ht⟩
  obtain ⟨eσ, eτ⟩ := openTime_closeTime_eq hσ0 hστ hτ1 hIM
  have hseg : ∀ u, segPt M (closure U) u = WangWu.toDisc (Lemma71I.realPath M) (Lemma71.segClock σ τ u) := by
    intro u
    rw [segPt, eσ, eτ]
    rfl
  simp only [hseg]
  rw [eσ, eτ]
  set η := WangWu.toDisc (Lemma71I.realPath M)
  set q := wallPt R b
  have hq : q = η τ := hτb.symm
  have himg := Lemma71.image_segClock hστ
  have hτ01 : τ ∈ Icc (0 : ℝ) 1 := ⟨hσ0.trans hστ.le, hτ1⟩
  have hIco : Ico σ τ ⊆ Icc (0 : ℝ) 1 := fun t ht => ⟨hσ0.trans ht.1, ht.2.le.trans hτ1⟩
  have hηE : MapsTo η (Ico σ τ) (closure U \ {q}) := fun t ht =>
    ⟨hin t (Ico_subset_Icc_self ht), fun hq' => ht.2.ne (hμ.inj (hIco ht) hτ01 (hq ▸ hq'))⟩
  have hηE' : ∀ u, 0 ≤ u → η (Lemma71.segClock σ τ u) ∈ closure U \ {q} := fun u hu =>
    hηE (himg ▸ (⟨u, hu, rfl⟩ : Lemma71.segClock σ τ u ∈ Lemma71.segClock σ τ '' Ici 0))
  have hrange : (fun u => Ψ (η (Lemma71.segClock σ τ u))) '' Ici 0 =
      Ψ '' (cayley '' range M ∩ (closure U \ {q})) := by
    ext v
    constructor
    · rintro ⟨u, hu, rfl⟩
      have hs : Lemma71.segClock σ τ u ∈ Ico σ τ :=
        himg ▸ (⟨u, hu, rfl⟩ : Lemma71.segClock σ τ u ∈ Lemma71.segClock σ τ '' Ici 0)
      refine ⟨η (Lemma71.segClock σ τ u), ⟨?_, hηE' u hu⟩, rfl⟩
      refine ⟨M (WangWu.arcTime (Lemma71.segClock σ τ u)).toNNReal, mem_range_self _, ?_⟩
      show cayley (M (WangWu.arcTime (Lemma71.segClock σ τ u)).toNNReal) =
        WangWu.toDisc (Lemma71I.realPath M) (Lemma71.segClock σ τ u)
      rw [WangWu.toDisc_of_lt (hs.2.trans_le hτ1)]
      rfl
    · rintro ⟨w, ⟨⟨_, ⟨t, rfl⟩, rfl⟩, hwU, hwq⟩, rfl⟩
      have hs01 := WangWu.discTime_mem_Ico (NNReal.coe_nonneg t)
      have hηs : η (WangWu.discTime t) = cayley (M t) := by
        show WangWu.toDisc (Lemma71I.realPath M) (WangWu.discTime t) = cayley (M t)
        rw [WangWu.toDisc_discTime (Lemma71I.realPath M) (NNReal.coe_nonneg t), Lemma71I.realPath_coe]
      have hsI : WangWu.discTime t ∈ Icc σ τ := by
        rw [← hIM]
        refine ⟨Ico_subset_Icc_self hs01, ?_⟩
        show η (WangWu.discTime t) ∈ closure U
        rw [hηs]; exact hwU
      have hsτ : WangWu.discTime t ≠ τ := fun h' => hwq (by
        rw [mem_singleton_iff, ← hηs, h', ← hq])
      obtain ⟨u, hu, hsu⟩ : WangWu.discTime t ∈ Lemma71.segClock σ τ '' Ici 0 := by
        rw [himg]; exact ⟨hsI.1, lt_of_le_of_ne hsI.2 hsτ⟩
      exact ⟨u, hu, by simp only [hsu, hηs]⟩
  refine ⟨hσ0, hστ, hτ1, hηE', ?_, hrange⟩
  have hlim : Tendsto (fun u => η (Lemma71.segClock σ τ u)) atTop (𝓝 q) := by
    have h1 : Tendsto (Lemma71.segClock σ τ) atTop (𝓝[Icc 0 1] τ) :=
      tendsto_nhdsWithin_iff.2 ⟨(Lemma71.tendsto_segClock hστ).mono_right nhdsWithin_le_nhds,
        (eventually_ge_atTop 0).mono fun u hu => hIco (himg ▸ (⟨u, hu, rfl⟩ :
          Lemma71.segClock σ τ u ∈ Lemma71.segClock σ τ '' Ici 0))⟩
    rw [hq]
    exact (hμ.cont τ hτ01).tendsto.comp h1
  have hΨL : Tendsto Ψ (𝓝 q ⊓ 𝓟 (closure U \ {q})) (cobounded ℂ) :=
    tendsto_norm_atTop_iff_cobounded.1 hΨinf
  have hΨU : MapsTo Ψ U H := by
    intro w hw
    rw [hU] at hw
    obtain ⟨z, hz, rfl⟩ := hw
    exact hΨC z hz
  have hCint : interior {t ∈ Lemma71.segClock σ τ '' Ici 0 | Lemma71.segClock σ τ 0 < t ∧ η t ∉ U} = ∅ := by
    rw [himg, Lemma71.segClock_zero]
    have hsub : {t ∈ Ico σ τ | σ < t ∧ η t ∉ U} ⊆ {t ∈ Icc σ τ | σ < t ∧ η t ∉ U} :=
      fun t ht => ⟨Ico_subset_Icc_self ht.1, ht.2⟩
    exact subset_empty_iff.1 ((interior_mono hsub).trans hint.subset)
  have h0 : Ψ (η (Lemma71.segClock σ τ 0)) = 0 := by
    rw [Lemma71.segClock_zero, hσa]
    exact hΨ0
  exact Lemma71.mappedSegment_props (Lemma71.continuousOn_segClock σ τ) (Lemma71.strictMonoOn_segClock hστ)
    (himg ▸ hμ.cont.mono hIco) (himg ▸ hμ.inj.mono hIco) (himg ▸ hηE) hΨc hΨi hΨH hΨU h0 hlim hΨL hCint

/-! ### Segment curves -/

theorem isSegCurve_congr {f g : ℝ → ℂ} (hf : Lemma71C.IsSegCurve f) (hfg : EqOn f g (Ici 0)) :
    Lemma71C.IsSegCurve g := by
  obtain ⟨hc, hi, hH, h0, hinf, hR⟩ := hf
  refine ⟨hc.congr fun x hx => (hfg hx).symm, hi.congr hfg, hH.congr hfg, ?_, ?_, ?_⟩
  · rw [← hfg (mem_Ici.2 le_rfl)]; exact h0
  · exact hinf.congr' ((eventually_ge_atTop 0).mono fun u hu => by rw [hfg (mem_Ici.2 hu)])
  · have e : {u ∈ Ici (0 : ℝ) | 0 < u ∧ (g u).im = 0} = {u ∈ Ici (0 : ℝ) | 0 < u ∧ (f u).im = 0} := by
      ext u
      constructor
      · rintro ⟨hu, hu0, him⟩; exact ⟨hu, hu0, by rw [hfg hu]; exact him⟩
      · rintro ⟨hu, hu0, him⟩; exact ⟨hu, hu0, by rw [← hfg hu]; exact him⟩
    rw [e]; exact hR

/-- The default segment curve `u ↦ i u`. -/
theorem isSegCurve_ofReal_mul_I : Lemma71C.IsSegCurve fun u : ℝ => (u : ℂ) * I := by
  refine ⟨(Complex.continuous_ofReal.mul continuous_const).continuousOn, fun u _ v _ huv => ?_,
    fun u hu => ?_, by simp, ?_, ?_⟩
  · exact Complex.ofReal_inj.1 (mul_right_cancel₀ Complex.I_ne_zero huv)
  · show 0 ≤ ((u : ℂ) * I).im
    simpa using hu
  · refine (tendsto_abs_atTop_atTop).congr fun u => ?_
    simp
  · have e : {u ∈ Ici (0 : ℝ) | 0 < u ∧ ((u : ℂ) * I).im = 0} = ∅ := by
      ext u
      simp only [mem_ofPred_eq, Complex.mul_im, Complex.ofReal_re, Complex.I_im, mul_one, Complex.ofReal_im,
        Complex.I_re, mul_zero, add_zero, mem_empty_iff_false, iff_false, not_and]
      intro _ hu h
      exact hu.ne' h
    rw [e, interior_empty]

/-! ### Measurable boundary values -/

section Random

variable {Ω : Type*} [MeasurableSpace Ω]

/-- **Measurable boundary values of a random chart.** For a random open `C ω ⊆ ℍ` with measurable membership events, a
random map `f ω` measurable at every point of `C ω`, and measurable points `w u ω`: functions `g ω u`, measurable in
`ω`, which equal `Ψ (w u ω)` whenever `f ω = Ψ ∘ cayley` on `C ω` for a map `Ψ` continuous at `w u ω` within a set
`E ⊇ cayley '' C ω` containing `w u ω`, and `w u ω ∈ closure (cayley '' C ω)`. -/
theorem exists_measurable_boundaryValues {C : Ω → Set ℂ} (hCo : ∀ ω, IsOpen (C ω)) (hCH : ∀ ω, C ω ⊆ H)
    (hCm : ∀ z, MeasurableSet {ω | z ∈ C ω}) {e : ℕ → ℂ} (he : DenseRange e) {Np : Ω → ℕ} (hNp : Measurable Np)
    (hNpC : ∀ ω, e (Np ω) ∈ C ω) {f : Ω → ℂ → ℂ}
    (hf : ∀ z, Measurable ({ω | z ∈ C ω}.indicator fun ω => f ω z)) {w : ℝ → Ω → ℂ} (hw : ∀ u, Measurable (w u)) :
    ∃ g : Ω → ℝ → ℂ, (∀ u, Measurable fun ω => g ω u) ∧
      ∀ (ω : Ω) (u : ℝ) (Ψ : ℂ → ℂ) (E : Set ℂ), cayley '' C ω ⊆ E → w u ω ∈ closure (cayley '' C ω) →
        ContinuousWithinAt Ψ E (w u ω) → (∀ z ∈ C ω, f ω z = Ψ (cayley z)) → g ω u = Ψ (w u ω) := by
  choose N hN hNC hNt using fun u => exists_measurable_approach_cayley hCo hCH hCm he hNp hNpC (hw u)
  refine ⟨fun ω u => limUnder atTop fun m => f ω (e (N u m ω)), fun u => ?_, fun ω u Ψ E hE hwc hΨ hfΨ => ?_⟩
  · exact (StronglyMeasurable.limUnder fun m =>
      (Lemma71E.measurable_at_seq (hN u m) (hNC u m) hf).stronglyMeasurable).measurable
  · have h1 := hNt u ω hwc
    have h2 : Tendsto (fun m => Ψ (cayley (e (N u m ω)))) atTop (𝓝 (Ψ (w u ω))) :=
      hΨ.tendsto.comp (h1.mono_right (nhdsWithin_mono _ hE))
    exact (h2.congr fun m => (hfΨ _ (hNC u m ω)).symm).limUnder_eq

/-- The segment points are measurable when the middle curve's coordinates and the pocket's membership events are. -/
theorem measurable_segPt {C : Ω → Set ℂ} (hCo : ∀ ω, IsOpen (C ω)) (hCH : ∀ ω, C ω ⊆ H)
    (hCm : ∀ z, MeasurableSet {ω | z ∈ C ω}) {e : ℕ → ℂ} (he : DenseRange e) {M : Ω → ℝ≥0 → ℂ}
    (hMc : ∀ ω, Continuous (M ω)) (hMm : ∀ t, Measurable fun ω => M ω t) (u : ℝ) :
    Measurable fun ω => segPt (M ω) (closure (cayley '' C ω)) u := by
  have hU : ∀ q : ℚ, MeasurableSet {ω | wallPt (M ω) q ∈ closure (cayley '' C ω)} := fun q =>
    measurableSet_mem_closure_cayley_image hCo hCH hCm he (measurable_wallPt_const hMm q)
  have hσ := measurable_openTime hU
  have hτ := measurable_closeTime hU
  have hs : Measurable fun ω => Lemma71.segClock (openTime (M ω) (closure (cayley '' C ω)))
      (closeTime (M ω) (closure (cayley '' C ω))) u := by
    unfold Lemma71.segClock
    exact hσ.add ((hτ.sub hσ).mul_const _)
  exact measurable_wallPt hMc hMm hs

end Random

end InteractingSLE.Sec7.Lemma71K
