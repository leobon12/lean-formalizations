/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.AStopProcWire
import InteractingSLE.Spec.Supplement.OrdGapWire
import InteractingSLE.Spec.Supplement.AStopSafeKernel
import InteractingSLE.Spec.Restart.RetPlumbS

/-!
# The later-line facts of the A-stopped second continuation

Packet PROVE-T15-ASTOP-SAFE (item 5 of `RLC.OrdModel.AStopSourceInputs`). The `hline` input of RETPLUMB's
`RetAux79.hasSafeLaw_of_retLines_indicator`, for the A-stopped second continuation of PROVE-T15-ASTOP-PROC (chart path
`AStopProc.sndChart d η₂' ζ₂`, clock `aClock`, capacity lifetime `aLife`, any driver generating `aPath`), in the
charts of a measurable retained family `retFam G η₁'' η₂'' d.u (d.r + t)` (the lines of the stop):

* `isRetMeanIdentOn_of_chart_eq`: the mean identification passes to retained data with the same cutoffs and almost
  surely the same chart on the identification event;
* `image_H_eq_of_inv_eq`: a later chart related to the stop chart by `f_Q⁻¹` maps `ℍ` onto the stop chart's image of
  `ℍ \ K_Q`;
* `continuous_aClock`, `monotone_aClock`, `aClock_zero`: the regularized clock is a clock at every sample;
* **`ae_aLine_snd_pos`** (lines `t > 0`; PROVE-T15-ORDDET5's `ae_retLine_facts_snd_late` and `ae_ord_or_encl_snd`,
  ORDDET's `exists_ordCont_facts`) and **`ae_aLine_snd_zero`** (the stop line): almost surely on a good stop-line event
  of ordinary pairs, at every line reached before the capacity lifetime, the later pair lies in the chart event of its
  line, the later word is sorted and identifies the line kernel's mean, the later chart is the stop chart composed
  with `f_Q⁻¹` (with the lift chain rule), and the force data of the typed stop word at the clock are the later word.

Uses Lemma 7.5 only (R43/R48).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Complex Set Filter Topology MeasureTheory
open scoped NNReal ENNReal
open QuantumZipper (H fwdHull fwdMapInv logDerivFwd chiC)
open LQGMetric (DistOn TestOn)

namespace InteractingSLE.RLC.AStopSafe

open Restart Restart.RetAux79 Supp7 Sec7 Sec7.Lemma76F MartChar.RealFlow AStopProc OrdGap

universe u

/-! ### Charts and clocks -/

section Helpers

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} {κ : ℝ} {h : Ω → DistOn upperHalfPlaneOpens}
  {η₁ η₂ : Ω → ℝ≥0 → ℂ} {ζ₁ ζ₂ : Ω → ℝ≥0∞} {u₀ : ℂ → ℝ}

/-- **The mean identification passes to data with the same cutoffs and almost surely the same chart.** -/
theorem isRetMeanIdentOn_of_chart_eq {d e : RetData Ω} (hd : d.IsMeasGood) (he : e.IsMeasGood) (hu : e.u = d.u)
    (hr : e.r = d.r) {O : Set Ω} {β : Ω → BoundaryWord} (hch : ∀ᵐ ω ∂P, ω ∈ O → e.chart ω = d.chart ω)
    (hm : IsRetMeanIdentOn κ P h η₁ η₂ ζ₁ ζ₂ u₀ hd O β) : IsRetMeanIdentOn κ P h η₁ η₂ ζ₁ ζ₂ u₀ he O β := by
  intro ηc₁ ηc₂ g hc₁ hc₂ hm₁ hm₂ ha₁ ha₂ hg
  rw [hu, hr] at ha₁ ha₂ hg
  filter_upwards [hm ηc₁ ηc₂ g hc₁ hc₂ hm₁ hm₂ ha₁ ha₂ hg, hch] with ω h1 h2 hω φ
  rw [← h1 hω φ]
  rw [chartTransport_congr_chart (h2 hω) _ (hd.isConformal_chart ω)]

/-- **A later chart related to the stop chart by `f_Q⁻¹` maps `ℍ` onto the stop chart's image of `ℍ \ K_Q`.** -/
theorem image_H_eq_of_inv_eq {c c' : Chart} {W : ℝ → ℝ} (hW : Continuous W) (hW0 : W 0 = 0) {Q : ℝ}
    (hQ : 0 ≤ Q) (h : ∀ w ∈ H, c'.2.1 w = c.2.1 (fwdMapInv W Q w)) :
    c'.2.1 '' H = c.2.1 '' (H \ fwdHull W Q) := by
  rw [← QuantumZipper.RS.image_fwdMapInv_H hW hW0 hQ, image_image]
  exact image_congr h

omit mΩ in
theorem continuous_aClock (Γ : Ω → ℝ≥0 → ℂ) (ω : Ω) : Continuous fun t => aClock Γ t ω := by
  classical
  by_cases hc : Continuous (chartClock (Γ ω)) ∧ Monotone (chartClock (Γ ω)) ∧ chartClock (Γ ω) 0 = 0
  · simp only [aClock, hc, and_self, ↓reduceIte]
    exact continuous_real_toNNReal.comp hc.1
  · simp only [aClock, hc, ↓reduceIte]
    exact continuous_const

omit mΩ in
theorem monotone_aClock (Γ : Ω → ℝ≥0 → ℂ) (ω : Ω) : Monotone fun t => aClock Γ t ω := by
  classical
  by_cases hc : Continuous (chartClock (Γ ω)) ∧ Monotone (chartClock (Γ ω)) ∧ chartClock (Γ ω) 0 = 0
  · simp only [aClock, hc, and_self, ↓reduceIte]
    exact fun s t hst => Real.toNNReal_le_toNNReal (hc.2.1 hst)
  · simp only [aClock, hc, ↓reduceIte]
    exact fun _ _ _ => le_rfl

omit mΩ in
theorem aClock_zero (Γ : Ω → ℝ≥0 → ℂ) (ω : Ω) : aClock Γ 0 ω = 0 := by
  classical
  by_cases hc : Continuous (chartClock (Γ ω)) ∧ Monotone (chartClock (Γ ω)) ∧ chartClock (Γ ω) 0 = 0
  · simp only [aClock, hc, and_self, ↓reduceIte, Real.toNNReal_zero]
  · simp only [aClock, hc, ↓reduceIte]

omit mΩ in
/-- On a good chart sample, the inverse of retained data agreeing with `d` is `d`'s inverse. -/
theorem inv_eq_of_chart_eq {d e : RetData Ω} {ω : Ω} (hd : ω ∈ d.E) (he : ω ∈ e.E) (hch : e.chart ω = d.chart ω) :
    e.inv ω = d.inv ω := by
  have h := congrArg (fun c : Chart => c.2.1) hch
  simp only [RetData.chart_of_mem hd, RetData.chart_of_mem he] at h
  exact h

end Helpers

/-! ### The lines after the stop -/

section Line

variable {κ : ℝ} {b : ℝ → ℝ} {jumps : Finset ℝ} {x₁ x₂ θ₁ θ₂ : ℝ} {Ω : Type u} [mΩ : MeasurableSpace Ω]
  {P : Measure Ω} [IsProbabilityMeasure P] {h : Ω → DistOn upperHalfPlaneOpens} {η₁ η₂ : Ω → ℝ≥0 → ℂ}
  {ζ₁ ζ₂ : Ω → ℝ≥0∞}

/-- **The later-line facts of the A-stopped second continuation at a positive line `t`.** -/
theorem ae_aLine_snd_pos (hL75 : Theorem15.Lemma75Statement.{u}) (hκ : 0 < κ) (hκ4 : κ < 4)
    (hb : IsPiecewiseConstantBoundaryData b jumps) (hx : x₂ ≤ x₁) (hθ : θ₁ < θ₂)
    (hh : IsGFFWithBoundaryData P h b jumps)
    (hη₁ : IsFlowLine κ b jumps x₁ θ₁ P h η₁ ζ₁) (hη₂ : IsFlowLine κ b jumps x₂ θ₂ P h η₂ ζ₂)
    {u₀ : ℂ → ℝ} (hu₀ : IsBoundedHarmonicExtension b jumps u₀) {d : RetData Ω} (hd : d.IsMeasGood)
    (hag : ∀ᵐ ω ∂P, (d.u : ℝ≥0∞) < ζ₁ ω → (d.r : ℝ≥0∞) < ζ₂ ω → ω ∈ d.G ∧
      (∀ s ≤ d.u, d.η₁ ω s = η₁ ω s) ∧ ∀ t ≤ d.r, d.η₂ ω t = η₂ ω t)
    {G : ℝ≥0 → Set Ω} {η₁'' η₂'' : Ω → ℝ≥0 → ℂ} (hdG : ∀ r', (retFam G η₁'' η₂'' d.u r').IsMeasGood)
    (hagF : ∀ r' : ℝ≥0, ∀ᵐ ω ∂P, (d.u : ℝ≥0∞) < ζ₁ ω → (r' : ℝ≥0∞) < ζ₂ ω → ω ∈ G r' ∧
      (∀ s ≤ d.u, η₁'' ω s = η₁ ω s) ∧ ∀ t ≤ r', η₂'' ω t = η₂ ω t)
    {β₀ : Ω → BoundaryWord}
    (hm₀ : IsRetMeanIdentOn κ P h η₁ η₂ ζ₁ ζ₂ u₀ (hdG d.r)
      {ω | IsOrdinaryRetainedPair (η₁ ω) (ζ₁ ω) d.u (η₂ ω) (ζ₂ ω) d.r} β₀)
    (hsort : ∀ᵐ ω ∂P, IsOrdinaryRetainedPair (η₁ ω) (ζ₁ ω) d.u (η₂ ω) (ζ₂ ω) d.r → (β₀ ω).IsSorted)
    {η₂' : Ω → ℝ≥0 → ℂ} {M : Set Ω} (hMg : ∀ ω ∈ M, IsSndGood d η₁ η₂ η₂' ζ₁ ζ₂ x₂ ω)
    (hMord : ∀ᵐ ω ∂P, ω ∈ M → IsOrdinaryRetainedPair (η₁ ω) (ζ₁ ω) d.u (η₂ ω) (ζ₂ ω) d.r)
    {W : ℝ≥0 → Ω → ℝ} (hWc : ∀ ω, Continuous fun q => W q ω) (hW0 : ∀ ω, W 0 ω = 0)
    (hgen : ∀ᵐ ω ∂P, ω ∈ M → IsGeneratingTrace (W · ω) (aLife (sndChart d η₂' ζ₂) (sndLifeP d η₂' ζ₂) ω)
      (aPath (sndChart d η₂' ζ₂) (sndLifeP d η₂' ζ₂) ω))
    {nL nR : ℕ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ} {xL : Ω → Fin nL → ℝ} {xR : Ω → Fin nR → ℝ}
    (htype : ∀ ω ∈ M, FCDet.IsFlowType κ θ₂ (β₀ ω) (xL ω) (xR ω) ρL ρR)
    {t : ℝ≥0} (ht : 0 < t) {β₁ : Ω → BoundaryWord}
    (hm₁ : IsRetMeanIdentOn κ P h η₁ η₂ ζ₁ ζ₂ u₀ (hdG (d.r + t))
      (ordEnclSet η₁ η₂ ζ₁ ζ₂ (retFam G η₁'' η₂'' d.u (d.r + t))) β₁)
    (hw₁ : ∀ᵐ ω ∂P, ω ∈ ordEnclSet η₁ η₂ ζ₁ ζ₂ (retFam G η₁'' η₂'' d.u (d.r + t)) →
      (β₁ ω).IsSorted ∧ IsRetainedWord κ θ₁ θ₂ (η₁ ω) (retFam G η₁'' η₂'' d.u (d.r + t)).u (η₂ ω)
        (retFam G η₁'' η₂'' d.u (d.r + t)).r ((retFam G η₁'' η₂'' d.u (d.r + t)).inv ω) (β₁ ω))
    {ηc₁ ηc₂ : Ω → ℝ≥0 → ℂ} {g : Ω → DistOn upperHalfPlaneOpens}
    (hc₁ : ∀ ω, Continuous (ηc₁ ω)) (hc₂ : ∀ ω, Continuous (ηc₂ ω))
    (hmc₁ : ∀ s, Measurable fun ω => ηc₁ ω s) (hmc₂ : ∀ s, Measurable fun ω => ηc₂ ω s)
    (hagc₁ : ∀ᵐ ω ∂P, ∀ s, ηc₁ ω s = η₁ ω (capTime (capR d.u (d.r + t)) (ζ₁ ω) s))
    (hagc₂ : ∀ᵐ ω ∂P, ∀ s, ηc₂ ω s = η₂ ω (capTime (capR d.u (d.r + t)) (ζ₂ ω) s))
    (hg : LocalSets.IsLocalSetMean (cstUnion ηc₁ ηc₂ d.u (d.r + t)) (WholeField.centredField h u₀) P g) :
    ∀ᵐ ω ∂P, ω ∈ M →
      (aClock (sndChart d η₂' ζ₂) t ω : ℝ≥0∞) < aLife (sndChart d η₂' ζ₂) (sndLifeP d η₂' ζ₂) ω →
      ((d.u : ℝ≥0∞) < ζ₁ ω ∧ ((d.r + t : ℝ≥0) : ℝ≥0∞) < ζ₂ ω ∧
        ω ∈ (retFam G η₁'' η₂'' d.u (d.r + t)).E) ∧
      (β₁ ω).IsSorted ∧
      (∀ φ : TestOn upperHalfPlaneOpens,
        Chart.chartTransport ((hdG (d.r + t)).isConformal_chart ω) 1 0 (chiC κ)
          (g ω + SupercriticalConformalCovariance.GM24.smoothDist upperHalfPlaneOpens u₀) φ =
        ∫ w, (β₁ ω).mean w * φ w) ∧
      (∀ w ∈ H, ((retFam G η₁'' η₂'' d.u (d.r + t)).chart ω).2.1 w =
        ((retFam G η₁'' η₂'' d.u d.r).chart ω).2.1
          (fwdMapInv (fun s : ℝ => W s.toNNReal ω) (aClock (sndChart d η₂' ζ₂) t ω) w)) ∧
      (∀ w ∈ H, ((retFam G η₁'' η₂'' d.u (d.r + t)).chart ω).2.2
          (((retFam G η₁'' η₂'' d.u (d.r + t)).chart ω).2.1 w) =
        (logDerivFwd (fun s : ℝ => W s.toNNReal ω) (aClock (sndChart d η₂' ζ₂) t ω)
          (fwdMapInv (fun s : ℝ => W s.toNNReal ω) (aClock (sndChart d η₂' ζ₂) t ω) w)).im +
          ((retFam G η₁'' η₂'' d.u d.r).chart ω).2.2 (((retFam G η₁'' η₂'' d.u d.r).chart ω).2.1
            (fwdMapInv (fun s : ℝ => W s.toNNReal ω) (aClock (sndChart d η₂' ζ₂) t ω) w))) ∧
      ∃ S : Set ℝ, S.Finite ∧ ∀ y ∉ S,
        forceBoundaryData κ ρL ρR
          (fun i => PocketTraversal.geomLW W xL i (aClock (sndChart d η₂' ζ₂) t ω) ω -
            W (aClock (sndChart d η₂' ζ₂) t ω) ω)
          (fun j => PocketTraversal.geomRW W xR j (aClock (sndChart d η₂' ζ₂) t ω) ω -
            W (aClock (sndChart d η₂' ζ₂) t ω) ω) y =
          (β₁ ω).fn y + θ₂ * chiC κ := by
  have hoe := ae_ord_or_encl_snd hκ hκ4 hb hx hθ hh hη₁ hη₂ (hdG d.r) (hdG (d.r + t)) (hagF d.r)
    (hagF (d.r + t)) rfl rfl rfl (t := t) rfl
  have hf := ae_retLine_facts_snd_late (θ₁ := θ₁) hL75 hκ hκ4 hb hx hθ hh hη₁ hη₂ hu₀ (hdG d.r) (hdG (d.r + t))
    (hagF d.r) (hagF (d.r + t)) rfl rfl rfl (t := t) rfl hm₀ hm₁ hw₁
  have hmean := hm₁ ηc₁ ηc₂ g hc₁ hc₂ hmc₁ hmc₂ hagc₁ hagc₂ hg
  filter_upwards [hoe, hf, hmean, hw₁, hMord, hsort, hgen, hag, hagF d.r, hagF (d.r + t)]
    with ω hoeω hfω hmω hwω hordω hsω hgω hagω hF0 hFt hωM hlt
  obtain ⟨hu, hr, hE, hp', a₁, a₂, e₂⟩ := hMg ω hωM
  have hord := hordω hωM
  have hagr := (hMg ω hωM).agree₂
  have hgood := isAGood_snd hd hE hp' hagr hr
  have htL : (t : ℝ≥0∞) < sndLifeP d η₂' ζ₂ ω := hgood.lt_of_aClock_lt hlt
  obtain ⟨-, -, -, -, hinj, hQ⟩ := OrdDet.exists_ordCont_facts hd hE hp' hagr hr
  obtain ⟨hQ0, -, himg, htip⟩ := hQ t ht htL
  have hQe : aClock (sndChart d η₂' ζ₂) t ω = (chartClock (contPath (d.D ω) (d.fwd ω) (η₂' ω) d.r
      (contLife (η₂' ω) (ζ₂ ω) d.r (d.η₁ ω '' Icc 0 d.u ∪ η₂' ω '' Icc 0 d.r))) t).toNNReal :=
    hgood.aClock_eq t
  rw [← hQe, canonRetPath_zero] at himg htip
  rw [canonRetPath_zero, canonRetLife_zero] at hinj
  have hinj' : InjOn (aPath (sndChart d η₂' ζ₂) (sndLifeP d η₂' ζ₂) ω)
      {s | (s : ℝ≥0∞) ≤ aLife (sndChart d η₂' ζ₂) (sndLifeP d η₂' ζ₂) ω} := hinj
  -- the line is alive and the continuation has no new contact before it
  have hstop : ((d.r + t : ℝ≥0) : ℝ≥0∞) < contStop (η₂' ω) (ζ₂ ω) d.r
      (d.η₁ ω '' Icc 0 d.u ∪ η₂' ω '' Icc 0 d.r) := coe_add_lt_iff.1 htL
  have hrt : ((d.r + t : ℝ≥0) : ℝ≥0∞) < ζ₂ ω := hstop.trans_le contStop_le
  have hle : ∀ s : ℝ≥0, s ≤ d.r + t → (s : ℝ≥0∞) ≤ ζ₂ ω := fun s hs =>
    (ENNReal.coe_le_coe.2 hs).trans hrt.le
  have hnc : ∀ s, d.r < s → s ≤ d.r + t → η₂ ω s ∉ η₁ ω '' Icc 0 d.u := by
    intro s hs1 hs2 hmem
    have hs := notMem_of_lt_contStop hs1 ((ENNReal.coe_le_coe.2 hs2).trans_lt hstop)
    rw [e₂ s (hle s hs2), image_congr fun s hs => a₁ s hs.2] at hs
    exact hs (Or.inl hmem)
  -- the stop charts of `d` and of the family agree
  obtain ⟨hG, -, -⟩ := hagω hu hr
  obtain ⟨hG0, f₁, f₂⟩ := hF0 hu hr
  obtain ⟨-, f₁', f₂'⟩ := hFt hu hrt
  obtain ⟨hEiff, -, hch⟩ := RetData.chart_eq_of_agree (d := d) (G' := G d.r) (η₁' := η₁'') (η₂' := η₂'') hG hG0
    (fun s hs => (f₁ s hs).trans (a₁ s hs).symm) (fun s hs => (f₂ s hs).trans (a₂ s hs).symm)
  have hE0 : ω ∈ (retFam G η₁'' η₂'' d.u d.r).E := hEiff.2 hE
  have hinv : (retFam G η₁'' η₂'' d.u d.r).inv ω = d.inv ω := inv_eq_of_chart_eq hE hE0 hch
  have h₂'' : η₂' ω '' Icc d.r (d.r + t) = η₂'' ω '' Icc d.r (d.r + t) :=
    image_congr fun s hs => (e₂ s (hle s hs.2)).trans (f₂' s hs.2).symm
  have himg' : (fun s => (retFam G η₁'' η₂'' d.u d.r).inv ω
      (aPath (sndChart d η₂' ζ₂) (sndLifeP d η₂' ζ₂) ω s)) '' Icc 0 (aClock (sndChart d η₂' ζ₂) t ω) =
      (retFam G η₁'' η₂'' d.u d.r).η₂ ω '' Icc d.r (d.r + t) := by
    rw [hinv]
    exact himg.trans h₂''
  have htip' : (retFam G η₁'' η₂'' d.u d.r).inv ω (aPath (sndChart d η₂' ζ₂) (sndLifeP d η₂' ζ₂) ω
      (aClock (sndChart d η₂' ζ₂) t ω)) = (retFam G η₁'' η₂'' d.u d.r).η₂ ω (d.r + t) := by
    rw [hinv]
    exact htip.trans ((e₂ _ (hle _ le_rfl)).trans (f₂' _ le_rfl).symm)
  have hQ0' : 0 < aClock (sndChart d η₂' ζ₂) t ω := by rw [hQe]; exact hQ0
  have hoe' := hoeω hord hrt hnc (fun q => W q ω) _ _ _ (hgω hωM) (hWc ω) (hW0 ω) hlt himg' htip'
  obtain ⟨hIII, hlift, S, hS, hdat⟩ := hfω hord hord (hsω hord) hrt hnc
    (fun q => W q ω) _ _ _ (hgω hωM) (hWc ω) (hW0 ω) hinj' hlt hQ0' himg' htip'
  have hEt : ω ∈ (retFam G η₁'' η₂'' d.u (d.r + t)).E := by
    rcases hoe' with hord' | hencl
    · exact (hdG (d.r + t)).mem_E_of_ordinary (hFt hu hrt).1 (hFt hu hrt).2.1 (hFt hu hrt).2.2 hord'
    · exact hencl.2.2.1
  refine ⟨⟨hu, hrt, hEt⟩, (hwω hoe').1, hmω hoe', hIII, hlift, S, hS, fun y hy => ?_⟩
  have h1 := forceBoundaryData_geom_of_isFlowType (htype ω hωM) (fun s => W s ω)
    (aClock (sndChart d η₂' ζ₂) t ω) y
  exact h1.trans (hdat y hy)

omit [IsProbabilityMeasure P] in
/-- **The facts at the stop line** (`t = 0`, the clock at `0`): the stop word with its mean identification in the
chart of the line `(u, r + 0)`, the identity chart change and the typed force data at time `0`. -/
theorem ae_aLine_snd_zero (hκ : 0 < κ) {u₀ : ℂ → ℝ} {d : RetData Ω}
    (hag : ∀ᵐ ω ∂P, (d.u : ℝ≥0∞) < ζ₁ ω → (d.r : ℝ≥0∞) < ζ₂ ω → ω ∈ d.G ∧
      (∀ s ≤ d.u, d.η₁ ω s = η₁ ω s) ∧ ∀ t ≤ d.r, d.η₂ ω t = η₂ ω t)
    {G : ℝ≥0 → Set Ω} {η₁'' η₂'' : Ω → ℝ≥0 → ℂ} (hdG : ∀ r', (retFam G η₁'' η₂'' d.u r').IsMeasGood)
    (hagF : ∀ r' : ℝ≥0, ∀ᵐ ω ∂P, (d.u : ℝ≥0∞) < ζ₁ ω → (r' : ℝ≥0∞) < ζ₂ ω → ω ∈ G r' ∧
      (∀ s ≤ d.u, η₁'' ω s = η₁ ω s) ∧ ∀ t ≤ r', η₂'' ω t = η₂ ω t)
    {β₀ : Ω → BoundaryWord}
    (hm₀ : IsRetMeanIdentOn κ P h η₁ η₂ ζ₁ ζ₂ u₀ (hdG (d.r + 0))
      {ω | IsOrdinaryRetainedPair (η₁ ω) (ζ₁ ω) d.u (η₂ ω) (ζ₂ ω) d.r} β₀)
    (hsort : ∀ᵐ ω ∂P, IsOrdinaryRetainedPair (η₁ ω) (ζ₁ ω) d.u (η₂ ω) (ζ₂ ω) d.r → (β₀ ω).IsSorted)
    {η₂' : Ω → ℝ≥0 → ℂ} {M : Set Ω} (hMg : ∀ ω ∈ M, IsSndGood d η₁ η₂ η₂' ζ₁ ζ₂ x₂ ω)
    (hMord : ∀ᵐ ω ∂P, ω ∈ M → IsOrdinaryRetainedPair (η₁ ω) (ζ₁ ω) d.u (η₂ ω) (ζ₂ ω) d.r)
    {W : ℝ≥0 → Ω → ℝ} (hWc : ∀ ω, Continuous fun q => W q ω) (hW0 : ∀ ω, W 0 ω = 0)
    {nL nR : ℕ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ} {xL : Ω → Fin nL → ℝ} {xR : Ω → Fin nR → ℝ}
    (htype : ∀ ω ∈ M, FCDet.IsFlowType κ θ₂ (β₀ ω) (xL ω) (xR ω) ρL ρR)
    {ηc₁ ηc₂ : Ω → ℝ≥0 → ℂ} {g : Ω → DistOn upperHalfPlaneOpens}
    (hc₁ : ∀ ω, Continuous (ηc₁ ω)) (hc₂ : ∀ ω, Continuous (ηc₂ ω))
    (hmc₁ : ∀ s, Measurable fun ω => ηc₁ ω s) (hmc₂ : ∀ s, Measurable fun ω => ηc₂ ω s)
    (hagc₁ : ∀ᵐ ω ∂P, ∀ s, ηc₁ ω s = η₁ ω (capTime (capR d.u (d.r + 0)) (ζ₁ ω) s))
    (hagc₂ : ∀ᵐ ω ∂P, ∀ s, ηc₂ ω s = η₂ ω (capTime (capR d.u (d.r + 0)) (ζ₂ ω) s))
    (hg : LocalSets.IsLocalSetMean (cstUnion ηc₁ ηc₂ d.u (d.r + 0)) (WholeField.centredField h u₀) P g) :
    ∀ᵐ ω ∂P, ω ∈ M →
      ((d.u : ℝ≥0∞) < ζ₁ ω ∧ ((d.r + 0 : ℝ≥0) : ℝ≥0∞) < ζ₂ ω ∧
        ω ∈ (retFam G η₁'' η₂'' d.u (d.r + 0)).E) ∧
      (β₀ ω).IsSorted ∧
      (∀ φ : TestOn upperHalfPlaneOpens,
        Chart.chartTransport ((hdG (d.r + 0)).isConformal_chart ω) 1 0 (chiC κ)
          (g ω + SupercriticalConformalCovariance.GM24.smoothDist upperHalfPlaneOpens u₀) φ =
        ∫ w, (β₀ ω).mean w * φ w) ∧
      (∀ w ∈ H, ((retFam G η₁'' η₂'' d.u (d.r + 0)).chart ω).2.1 w =
        ((retFam G η₁'' η₂'' d.u d.r).chart ω).2.1
          (fwdMapInv (fun s : ℝ => W s.toNNReal ω) (aClock (sndChart d η₂' ζ₂) 0 ω) w)) ∧
      (∀ w ∈ H, ((retFam G η₁'' η₂'' d.u (d.r + 0)).chart ω).2.2
          (((retFam G η₁'' η₂'' d.u (d.r + 0)).chart ω).2.1 w) =
        (logDerivFwd (fun s : ℝ => W s.toNNReal ω) (aClock (sndChart d η₂' ζ₂) 0 ω)
          (fwdMapInv (fun s : ℝ => W s.toNNReal ω) (aClock (sndChart d η₂' ζ₂) 0 ω) w)).im +
          ((retFam G η₁'' η₂'' d.u d.r).chart ω).2.2 (((retFam G η₁'' η₂'' d.u d.r).chart ω).2.1
            (fwdMapInv (fun s : ℝ => W s.toNNReal ω) (aClock (sndChart d η₂' ζ₂) 0 ω) w))) ∧
      ∃ S : Set ℝ, S.Finite ∧ ∀ y ∉ S,
        forceBoundaryData κ ρL ρR
          (fun i => PocketTraversal.geomLW W xL i (aClock (sndChart d η₂' ζ₂) 0 ω) ω -
            W (aClock (sndChart d η₂' ζ₂) 0 ω) ω)
          (fun j => PocketTraversal.geomRW W xR j (aClock (sndChart d η₂' ζ₂) 0 ω) ω -
            W (aClock (sndChart d η₂' ζ₂) 0 ω) ω) y =
          (β₀ ω).fn y + θ₂ * chiC κ := by
  have hfam : retFam G η₁'' η₂'' d.u (d.r + 0) = retFam G η₁'' η₂'' d.u d.r := by rw [add_zero]
  have hmean := hm₀ ηc₁ ηc₂ g hc₁ hc₂ hmc₁ hmc₂ hagc₁ hagc₂ hg
  filter_upwards [hmean, hMord, hsort, hag, hagF d.r] with ω hmω hordω hsω hagω hF0 hωM
  obtain ⟨hu, hr, hE, -, a₁, a₂, -⟩ := hMg ω hωM
  have hord := hordω hωM
  obtain ⟨hG, -, -⟩ := hagω hu hr
  obtain ⟨hG0, f₁, f₂⟩ := hF0 hu hr
  obtain ⟨hEiff, -, -⟩ := RetData.chart_eq_of_agree (d := d) (G' := G d.r) (η₁' := η₁'') (η₂' := η₂'') hG hG0
    (fun s hs => (f₁ s hs).trans (a₁ s hs).symm) (fun s hs => (f₂ s hs).trans (a₂ s hs).symm)
  have hE0 : ω ∈ (retFam G η₁'' η₂'' d.u (d.r + 0)).E := by
    rw [hfam]
    exact hEiff.2 hE
  have hWc' : Continuous fun s : ℝ => W s.toNNReal ω := (hWc ω).comp continuous_real_toNNReal
  have hW0' : (fun s : ℝ => W s.toNNReal ω) 0 = 0 := by
    show W (0 : ℝ).toNNReal ω = 0
    rw [Real.toNNReal_zero]
    exact hW0 ω
  rw [aClock_zero, NNReal.coe_zero]
  refine ⟨⟨hu, by rw [add_zero]; exact hr, hE0⟩, hsω hord, hmω hord, fun w hw => ?_, fun w hw => ?_, ?_⟩
  · rw [InteractingSLE.fwdMapInv_zero_time hWc' hW0' hw, hfam]
  · rw [InteractingSLE.fwdMapInv_zero_time hWc' hW0' hw, hfam,
      show logDerivFwd (fun s : ℝ => W s.toNNReal ω) 0 w = 0 by simp [QuantumZipper.logDerivFwd],
      Complex.zero_im, zero_add]
  · obtain ⟨hgL, hgR⟩ := geom_zero_of_isFlowType hWc hW0 (htype ω hωM)
    refine ⟨{0} ∪ ((β₀ ω).jumps : Set ℝ), (finite_singleton 0).union (β₀ ω).jumps.finite_toSet,
      fun y hy => ?_⟩
    have hy0 : y ≠ 0 := fun h => hy (Or.inl h)
    have hyJ : y + 0 ∉ (β₀ ω).jumps := by
      rw [add_zero]; exact fun h => hy (Or.inr h)
    rw [hgL, hgR, forceBoundaryData_zero_of_isFlowType (htype ω hωM) y,
      Exist.forceBoundaryData_flowLine_seed hκ (BoundaryWord.isPiecewiseConstantBoundaryData (β₀ ω)) 0 θ₂ hy0 hyJ,
      add_zero]

end Line

end InteractingSLE.RLC.AStopSafe
