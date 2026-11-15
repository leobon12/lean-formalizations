/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.OrdFstLine
import InteractingSLE.Spec.Supplement.OrdFstWord
import InteractingSLE.Spec.Supplement.RLCBMain

/-!
# Leaf 3, the first continuation: later-line facts at ordinary later pairs, and the later first tip's activity

Packet PROVE-T15-ORDDET3 (Theorem 1.5's leaf 3, `RLC.RetOrdDetFstStatement`).

* `isRetainedWordFst_congr`: the sided outer word reads only the prefix images and the tip;
* **`later_tip_mem_closure_activeDomain_fst`** (deterministic): the image of `ℍ` under `w ↦ ψ₀(F̄_Q w + τ₀)` lies in
  the later active domain at `(u + t, r)`, and the later first tip `η₁(u + t)` is adherent to it (the first-path
  analogue of `OrdDet.later_tip_mem_closure_activeDomain`; the 7th conjunct of `IsOrdinaryRetainedPair` at the later
  pair);
* **`ae_retLine_facts_fst_of_ordinary`**: `ae_retLine_facts_fst` with the later word taken from the mean identification
  at the later pair (e.g. `RetOrdMeanWordStatement` at `(u + t, r)`): at an ordinary later pair, the later shifted
  chart is centred at `tipPos` of the later data, the injectivity of the first prefix, the later first tip off the
  second prefix, the later chart event, the later tip's chart point and the SIDED outer word are all supplied
  (`ae_isPathGood_of_isFlowLine`, `inv_tipPos_eq`, `ae_isRetainedWordFst_of_meanIdent`); what remains as premises is
  only the chart path of the continuation and the stop-line data;
* **`ae_retLine_facts_snd_of_ordinary`**: the same wiring for the SECOND continuation
  (`ae_retLine_facts_of_retainedWord_dense` of PROVE-T15-ORDDET2 with the outer word of the flow lines at the later
  pair `(u, r + t)` transferred to the data paths, `isRetainedWord_congr`, and the later chart event from
  ordinariness).

For Theorem 1.5; uses Lemma 7.5 only (R43/R48).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology Metric Complex
open scoped NNReal ENNReal

open QuantumZipper (H Hbar fwdMap fwdMapInv fwdHull logDerivFwd)
open LQGMetric (DistOn TestOn)

universe u

namespace InteractingSLE

namespace RLC

namespace OrdDet

open Sec7 Sec7.Lemma76F Restart Restart.RetAux79 Supp7 MartChar.RealFlow

/-- The sided outer word reads only the prefix images and the first tip. -/
theorem isRetainedWordFst_congr {κ θ₁ : ℝ} {α α' β β' : ℝ≥0 → ℂ} {a b : ℝ≥0} {ψ : ℂ → ℂ} {τ : ℝ}
    {c : BoundaryWord} (hw : IsRetainedWordFst κ θ₁ α a β b ψ τ c) (hα : ∀ s ≤ a, α' s = α s)
    (hβ : ∀ s ≤ b, β' s = β s) : IsRetainedWordFst κ θ₁ α' a β' b ψ τ c := by
  intro y hH htip hα' hβ'
  have eα : α' '' Icc 0 a = α '' Icc 0 a := image_congr fun s hs => hα s hs.2
  have eβ : β' '' Icc 0 b = β '' Icc 0 b := image_congr fun s hs => hβ s hs.2
  rw [hα a le_rfl] at htip
  rw [eα] at hα'
  rw [eβ] at hβ'
  exact hw y hH htip hα' hβ'

/-- **The later first tip is adherent to the later active domain** (deterministic; see the module docstring). With the
stop-line chart `ψ₀` of `d` and a chart path `γ` of the first continuation from the seed `τ₀`, the image
`ψ₀(F̄_Q(ℍ) + τ₀)` is a connected unbounded subset of `ℍ` off `η₁([0, u + t]) ∪ η₂([0, r])`, hence lies in the later
active domain, and `ψ₀(F̄_Q(0) + τ₀) = ψ₀(γ(Q) + τ₀)` is the later first tip. -/
theorem later_tip_mem_closure_activeDomain_fst {Ω : Type*} [MeasurableSpace Ω] {d : RetData Ω}
    (hd : d.IsMeasGood) {t : ℝ≥0} {ω : Ω} (hω : ω ∈ d.E) {τ₀ : ℝ} {W : ℝ≥0 → ℝ} {γ : ℝ≥0 → ℂ} {ζc : ℝ≥0∞}
    {Q : ℝ≥0} (hg : IsGeneratingTrace W ζc γ) (hWc : Continuous W) (hW0 : W 0 = 0) (hQ : (Q : ℝ≥0∞) < ζc)
    (himg : (fun s => d.inv ω (γ s + τ₀)) '' Icc 0 Q = d.η₁ ω '' Icc d.u (d.u + t))
    (htip : d.inv ω (γ Q + τ₀) = d.η₁ ω (d.u + t)) :
    (fun w => d.inv ω (extendFrom H (fwdMapInv (fun s : ℝ => W s.toNNReal) Q) w + τ₀)) '' H ⊆
        activeDomain (d.η₁ ω) (d.u + t) (d.η₂ ω) d.r ∧
      d.η₁ ω (d.u + t) ∈ closure (activeDomain (d.η₁ ω) (d.u + t) (d.η₂ ω) d.r) := by
  set w' : ℝ → ℝ := fun s => W s.toNNReal with hw'
  have hQr : (0 : ℝ) ≤ Q := Q.coe_nonneg
  obtain ⟨Wg, γg, T', hQT', hWgc, hWg0, hγg, hWeq, hγeq⟩ :=
    Sec7.ReverseArc.exists_global_model hg hWc.continuousOn hW0 hQ
  have hΦeq : fwdMapInv w' Q = fwdMapInv Wg Q := fwdMapInv_eq_of_eqOn hQr hQT' fun r hr => (hWeq r hr).symm
  have hγQ : γg Q = γ Q := by rw [hγeq Q ⟨hQr, hQT'.le⟩, Real.toNNReal_coe]
  have himgg : γg '' Icc 0 (Q : ℝ) = γ '' Icc 0 Q := by
    rw [image_congr (fun r hr => hγeq r ⟨hr.1, hr.2.trans hQT'.le⟩), image_toNNReal_Icc γ hQr,
      Real.toNNReal_coe]
  rw [hΦeq]
  set Φ := extendFrom H (fwdMapInv Wg Q) with hΦdef
  have hG := hd.good ω (RetData.E₀_subset_G (RetData.E_subset_E₀ hω))
  have h0₂ : (d.η₂ ω 0).im = 0 := hG.2.2.2.2.2.1
  have hC := (hd.isRetChart hω).2
  set ψ₀ := d.inv ω with hψ₀
  have hHbar : ∀ v : ℂ, v ∈ Hbar → ∀ y : ℝ, v + y ∈ Hbar := fun v hv y =>
    show 0 ≤ (v + y).im by simpa using (show 0 ≤ v.im from hv)
  have hHadd : ∀ v : ℂ, v ∈ H → ∀ y : ℝ, v + y ∈ H := fun v hv y =>
    show 0 < (v + y).im by simpa using (show 0 < v.im from hv)
  have hΦc : ContinuousOn Φ Hbar := (hγg.hasBdryLimits hWgc hWg0 hQr).continuousOn
  have hΦm : MapsTo Φ Hbar Hbar := fun x hx => Sec7.Lemma71P.extendFrom_mem_Hbar hγg hWgc hWg0 hQr hx
  have hFc : ContinuousOn (fun w => ψ₀ (Φ w + τ₀)) Hbar :=
    hC.continuousOn_inv.comp (hΦc.add continuousOn_const) fun v hv => hHbar _ (hΦm hv) τ₀
  -- the image of `ℍ` is off the later union
  have hK : fwdHull Wg Q = fillH (γ '' Icc 0 Q) := by rw [hγg.2.2 Q hQr, himgg]
  have hoff : ∀ w ∈ H, ψ₀ (Φ w + τ₀) ∈ H \ (d.η₁ ω '' Icc 0 (d.u + t) ∪ d.η₂ ω '' Icc 0 d.r) := by
    intro w hw
    have hΦw : Φ w ∈ H \ fwdHull Wg Q := by
      rw [hΦdef, ZhanGT4.extendFrom_eq_fwdMapInv hWgc hWg0 hQr hw]
      exact QuantumZipper.RS.fwdMapInv_mem_compl_fwdHull hWgc hWg0 hQr hw
    have hD : ψ₀ (Φ w + τ₀) ∈ activeDomain (d.η₁ ω) d.u (d.η₂ ω) d.r :=
      (hC.bijOn h0₂).mapsTo (hHadd _ hΦw.1 τ₀)
    obtain ⟨hDH, hD₁, hD₂⟩ := notMem_of_mem_activeDomain hD
    refine ⟨hDH, ?_⟩
    rintro (⟨s, hs, hse⟩ | h2)
    · rcases le_total s d.u with hsu | hus
      · exact hD₁ ⟨s, ⟨hs.1, hsu⟩, hse⟩
      -- a point of the new piece is the chart image of a point of the chart path
      have hnew : d.η₁ ω s ∈ (fun s => ψ₀ (γ s + τ₀)) '' Icc 0 Q := by rw [himg]; exact ⟨s, ⟨hus, hs.2⟩, rfl⟩
      obtain ⟨q, hq, hqe⟩ := hnew
      by_cases hγH : γ q + τ₀ ∈ H
      · have he : Φ w + τ₀ = γ q + τ₀ :=
          (hC.bijOn h0₂).injOn (hHadd _ hΦw.1 τ₀) hγH (hqe.trans hse).symm
        have he' : Φ w = γ q := add_right_cancel he
        have hγqH : γ q ∈ H := by rw [← he']; exact hΦw.1
        exact hΦw.2 (by rw [he', hK]; exact ⟨hγqH, Or.inl (subset_closure ⟨q, hq, rfl⟩)⟩)
      · have he : ψ₀ (γ q + τ₀) = ψ₀ (Φ w + τ₀) := hqe.trans hse
        exact hC.inv_notMem h0₂ (γ q + τ₀) hγH (by rw [he]; exact hD)
    · exact hD₂ h2
  -- the image of `ℍ` is preconnected and unbounded
  set S := (fun w => ψ₀ (Φ w + τ₀)) '' H with hSdef
  have hSc : IsPreconnected S := convex_H.isPreconnected.image _ (hFc.mono QuantumZipper.H_subset_Hbar)
  obtain ⟨M, hM⟩ := hC.2.2.2.2.2.2.2.2.2.1
  obtain ⟨C, hCb⟩ := Sec7.Lemma71P.exists_norm_extendFrom_sub_le' hγg hWgc hWg0 hQr
  have hSu : ¬ Bornology.IsBounded S := by
    intro hb
    obtain ⟨R, hR⟩ := hb.subset_closedBall 0
    set w : ℂ := ((|R| + |M| + |C| + |τ₀| + 1 : ℝ) : ℂ) * I with hwdef
    have hwH : w ∈ H := by
      show 0 < w.im
      simp only [hwdef, mul_im, ofReal_re, I_im, ofReal_im, I_re, mul_zero, add_zero, mul_one]
      positivity
    have hwn : ‖w‖ = |R| + |M| + |C| + |τ₀| + 1 := by
      rw [hwdef, norm_mul, norm_I, mul_one, norm_real, Real.norm_eq_abs, abs_of_pos (by positivity)]
    have hΦwb : Φ w + τ₀ ∈ Hbar := hHbar _ (hΦm (QuantumZipper.H_subset_Hbar hwH)) τ₀
    have h1 := hM (Φ w + τ₀) hΦwb
    have h2 := hCb w (QuantumZipper.H_subset_Hbar hwH)
    have h3 : ψ₀ (Φ w + τ₀) ∈ closedBall (0 : ℂ) R := hR ⟨w, hwH, rfl⟩
    rw [mem_closedBall, dist_zero_right] at h3
    have h4 := norm_sub_norm_le w (Φ w)
    have h5 := norm_sub_norm_le (Φ w + τ₀) (ψ₀ (Φ w + τ₀))
    have h6 : ‖Φ w + (τ₀ : ℂ)‖ ≥ ‖Φ w‖ - |τ₀| := by
      have := norm_sub_norm_le (Φ w) (-(τ₀ : ℂ))
      rw [norm_neg, norm_real, Real.norm_eq_abs, sub_neg_eq_add] at this
      linarith
    rw [norm_sub_rev] at h4 h5
    linarith [le_abs_self R, le_abs_self M, le_abs_self C, abs_nonneg τ₀]
  have hSsub : S ⊆ activeDomain (d.η₁ ω) (d.u + t) (d.η₂ ω) d.r := by
    rintro _ ⟨w, hw, rfl⟩
    refine ⟨hoff w hw, fun hb => hSu (hb.subset ?_)⟩
    exact hSc.subset_connectedComponentIn ⟨w, hw, rfl⟩ (by rintro _ ⟨w', hw', rfl⟩; exact hoff w' hw')
  refine ⟨hSsub, ?_⟩
  have h0cl : (0 : ℂ) ∈ closure H := by rw [closure_H]; exact mem_Hbar_of_im_eq_zero (by simp)
  have hcw : ContinuousWithinAt (fun w => ψ₀ (Φ w + τ₀)) H 0 :=
    (hFc 0 (mem_Hbar_of_im_eq_zero (by simp))).mono QuantumZipper.H_subset_Hbar
  have hval : ψ₀ (Φ 0 + τ₀) = d.η₁ ω (d.u + t) := by
    rw [hΦdef, ZhanGT4.extendFrom_zero_eq hγg hWgc hWg0 hQr, hγQ, htip]
  rw [← hval]
  exact closure_mono hSsub (hcw.mem_closure_image h0cl)

section Wire

variable {κ : ℝ} {b : ℝ → ℝ} {jumps : Finset ℝ} {x₁ x₂ θ₁ θ₂ : ℝ} {Ω : Type u} [mΩ : MeasurableSpace Ω]
  {P : Measure Ω} [IsProbabilityMeasure P] {h : Ω → DistOn upperHalfPlaneOpens} {η₁ η₂ : Ω → ℝ≥0 → ℂ}
  {ζ₁ ζ₂ : Ω → ℝ≥0∞}

/-- **The later-line facts of the first continuation at an ordinary later pair** (see the module docstring):
`ae_retLine_facts_fst` with the later word `β₁` mean-identified on the ordinary pairs at `(u + t, r)` with the outer
word there (the data of `RetOrdMeanWordStatement` at the later pair), the later seed `τ₁ = tipPos d' η₁ ω`, and all
pathwise premises at the later line discharged. -/
theorem ae_retLine_facts_fst_of_ordinary (hL75 : Theorem15.Lemma75Statement.{u}) (hκ : 0 < κ) (hκ4 : κ < 4)
    (hb : IsPiecewiseConstantBoundaryData b jumps) (hx : x₂ ≤ x₁) (hθ : θ₁ < θ₂)
    (hh : IsGFFWithBoundaryData P h b jumps)
    (hη₁ : IsFlowLine κ b jumps x₁ θ₁ P h η₁ ζ₁) (hη₂ : IsFlowLine κ b jumps x₂ θ₂ P h η₂ ζ₂)
    {u₀ : ℂ → ℝ} (hu₀ : IsBoundedHarmonicExtension b jumps u₀)
    {d d' : RetData Ω} (hd : d.IsMeasGood) (hd' : d'.IsMeasGood)
    (hag : ∀ᵐ ω ∂P, (d.u : ℝ≥0∞) < ζ₁ ω → (d.r : ℝ≥0∞) < ζ₂ ω → ω ∈ d.G ∧
      (∀ s ≤ d.u, d.η₁ ω s = η₁ ω s) ∧ ∀ t ≤ d.r, d.η₂ ω t = η₂ ω t)
    (hag' : ∀ᵐ ω ∂P, (d'.u : ℝ≥0∞) < ζ₁ ω → (d'.r : ℝ≥0∞) < ζ₂ ω → ω ∈ d'.G ∧
      (∀ s ≤ d'.u, d'.η₁ ω s = η₁ ω s) ∧ ∀ t ≤ d'.r, d'.η₂ ω t = η₂ ω t)
    (h₁ : d'.η₁ = d.η₁) (h₂ : d'.η₂ = d.η₂) {t : ℝ≥0} (hu : d'.u = d.u + t) (hr : d'.r = d.r)
    {O₀ : Set Ω} {β₀ β₁ : Ω → BoundaryWord}
    (hm₀ : IsRetMeanIdentOn κ P h η₁ η₂ ζ₁ ζ₂ u₀ hd O₀ β₀)
    (hm₁ : IsRetMeanIdentOn κ P h η₁ η₂ ζ₁ ζ₂ u₀ hd'
      {ω | IsOrdinaryRetainedPair (η₁ ω) (ζ₁ ω) d'.u (η₂ ω) (ζ₂ ω) d'.r} β₁)
    (hw₁ : ∀ᵐ ω ∂P, IsOrdinaryRetainedPair (η₁ ω) (ζ₁ ω) d'.u (η₂ ω) (ζ₂ ω) d'.r →
      (β₁ ω).IsSorted ∧ IsRetainedWord κ θ₁ θ₂ (η₁ ω) d'.u (η₂ ω) d'.r (d'.inv ω) (β₁ ω)) :
    ∀ᵐ ω ∂P, ω ∈ O₀ → IsOrdinaryRetainedPair (η₁ ω) (ζ₁ ω) d'.u (η₂ ω) (ζ₂ ω) d'.r → ω ∈ d.E →
      (β₀ ω).IsSorted →
      ∀ (τ₀ : ℝ) (W : ℝ≥0 → ℝ) (γ : ℝ≥0 → ℂ) (ζc : ℝ≥0∞) (Q : ℝ≥0), IsGeneratingTrace W ζc γ →
        Continuous W → W 0 = 0 → InjOn γ {s | (s : ℝ≥0∞) ≤ ζc} → (Q : ℝ≥0∞) < ζc → 0 < Q →
        (fun s => d.inv ω (γ s + τ₀)) '' Icc 0 Q = d.η₁ ω '' Icc d.u (d.u + t) →
        d.inv ω (γ Q + τ₀) = d.η₁ ω (d.u + t) →
        (∀ w ∈ H, ((d'.chart ω).recenter (tipPos d' η₁ ω)).2.1 w =
          ((d.chart ω).recenter τ₀).2.1 (fwdMapInv (fun s : ℝ => W s.toNNReal) Q w)) ∧
        (∀ w ∈ H, ((d'.chart ω).recenter (tipPos d' η₁ ω)).2.2 (((d'.chart ω).recenter (tipPos d' η₁ ω)).2.1 w) =
          (logDerivFwd (fun s : ℝ => W s.toNNReal) Q (fwdMapInv (fun s : ℝ => W s.toNNReal) Q w)).im +
            ((d.chart ω).recenter τ₀).2.2
              (((d.chart ω).recenter τ₀).2.1 (fwdMapInv (fun s : ℝ => W s.toNNReal) Q w))) ∧
        ∃ S : Set ℝ, S.Finite ∧ ∀ y ∉ S,
          forceBoundaryData κ
              (flowLineRhoL κ (Exist.StagedLaw.BoundaryWord.shiftW τ₀ (β₀ ω)).fn
                (Exist.StagedLaw.BoundaryWord.shiftW τ₀ (β₀ ω)).jumps 0 θ₁)
              (flowLineRhoR κ (Exist.StagedLaw.BoundaryWord.shiftW τ₀ (β₀ ω)).fn
                (Exist.StagedLaw.BoundaryWord.shiftW τ₀ (β₀ ω)).jumps 0 θ₁)
              (fun i => -rightImg (fun s : ℝ => -W s.toNNReal)
                (-flowLineXL (Exist.StagedLaw.BoundaryWord.shiftW τ₀ (β₀ ω)).fn
                  (Exist.StagedLaw.BoundaryWord.shiftW τ₀ (β₀ ω)).jumps 0 i) Q - W Q)
              (fun j => rightImg (fun s : ℝ => W s.toNNReal)
                (flowLineXR (Exist.StagedLaw.BoundaryWord.shiftW τ₀ (β₀ ω)).fn
                  (Exist.StagedLaw.BoundaryWord.shiftW τ₀ (β₀ ω)).jumps 0 j) Q - W Q) y =
            (Exist.StagedLaw.BoundaryWord.shiftW (tipPos d' η₁ ω) (β₁ ω)).fn y + θ₁ * QuantumZipper.chiC κ := by
  have hsided := ae_isRetainedWordFst_of_meanIdent hL75 hκ hκ4 hb hx hθ hh hη₁ hη₂ hd' hag' hu₀ hm₁ hw₁
  have hl := ae_retLine_facts_fst (θ₂ := θ₂) hL75 hκ hκ4 hb hh hη₁ hη₂ hu₀ hd hd' hag hag' h₁ h₂ hu hr hm₀ hm₁
  have hpg := ae_isPathGood_of_isFlowLine Theorem15.aux25Statement hκ hκ4 hη₁
  filter_upwards [hl, hsided, hag', hw₁, hpg] with ω hlω hsω hag'ω hw₁ω hpgω
  intro hO₀ hord hE hs₀ τ₀ W γ ζc Q hg hWc hW0 hinj hQ hQ0 himg htip
  obtain ⟨hG', a₁', a₂'⟩ := hag'ω hord.1 hord.2.1
  have hE' : ω ∈ d'.E := hd'.mem_E_of_ordinary hG' a₁' a₂' hord
  have hs₁ := (hw₁ω hord).1
  -- the later first prefix, in the data paths
  have e₁ : EqOn (d'.η₁ ω) (η₁ ω) (Icc 0 d'.u) := fun s hs => a₁' s hs.2
  have e₂ : EqOn (d'.η₂ ω) (η₂ ω) (Icc 0 d'.r) := fun s hs => a₂' s hs.2
  have hinj₁ : InjOn (η₁ ω) (Icc 0 d'.u) := Sec7.IsPathGood.injOn_Icc hpgω hord.1.le
  have hi' : InjOn (d'.η₁ ω) (Icc 0 d'.u) := hinj₁.congr e₁.symm
  have hq' : d'.η₁ ω d'.u ∉ d'.η₂ ω '' Icc 0 d'.r := by
    rw [a₁' d'.u le_rfl, e₂.image_eq]; exact hord.2.2.2.2.2.1
  have hcl' : d'.η₁ ω d'.u ∈ closure (activeDomain (d'.η₁ ω) d'.u (d'.η₂ ω) d'.r) := by
    rw [a₁' d'.u le_rfl, activeDomain_congr_Icc e₁ e₂]; exact hord.2.2.2.2.2.2.1
  have htp : tipPos d' η₁ ω = tipPos d' d'.η₁ ω := by
    simp only [tipPos, a₁' d'.u le_rfl]
  have hτ₁ := (inv_tipPos_eq hd' hE' hi' hq' hcl').1
  rw [← htp] at hτ₁
  rw [h₁, hu] at hi' hτ₁ hq'
  rw [h₂, hr] at hq'
  have hfst : IsRetainedWordFst κ θ₁ (d.η₁ ω) (d.u + t) (d.η₂ ω) d.r (d'.inv ω) (tipPos d' η₁ ω) (β₁ ω) := by
    have := isRetainedWordFst_congr (hsω hord) (α' := d'.η₁ ω) (β' := d'.η₂ ω) (fun s hs => a₁' s hs)
      (fun s hs => a₂' s hs)
    rwa [h₁, h₂, hu, hr] at this
  exact hlω hO₀ hord hord.1 hord.2.1 hE hE' hs₀ hs₁ hi' hq' τ₀ (tipPos d' η₁ ω) hτ₁ hfst W γ ζc Q hg hWc hW0
    hinj hQ hQ0 himg htip

/-- **The later-line facts of the second continuation at an ordinary later pair**: PROVE-T15-ORDDET2's
`ae_retLine_facts_of_retainedWord_dense` with the later word `β₁` mean-identified on the ordinary pairs at `(u, r + t)`
with the outer word of the flow lines there, and the later pathwise premises discharged. -/
theorem ae_retLine_facts_snd_of_ordinary (hL75 : Theorem15.Lemma75Statement.{u}) (hκ : 0 < κ) (hκ4 : κ < 4)
    (hb : IsPiecewiseConstantBoundaryData b jumps) (hh : IsGFFWithBoundaryData P h b jumps)
    (hη₁ : IsFlowLine κ b jumps x₁ θ₁ P h η₁ ζ₁) (hη₂ : IsFlowLine κ b jumps x₂ θ₂ P h η₂ ζ₂)
    {u₀ : ℂ → ℝ} (hu₀ : IsBoundedHarmonicExtension b jumps u₀)
    {d d' : RetData Ω} (hd : d.IsMeasGood) (hd' : d'.IsMeasGood)
    (hag : ∀ᵐ ω ∂P, (d.u : ℝ≥0∞) < ζ₁ ω → (d.r : ℝ≥0∞) < ζ₂ ω → ω ∈ d.G ∧
      (∀ s ≤ d.u, d.η₁ ω s = η₁ ω s) ∧ ∀ t ≤ d.r, d.η₂ ω t = η₂ ω t)
    (hag' : ∀ᵐ ω ∂P, (d'.u : ℝ≥0∞) < ζ₁ ω → (d'.r : ℝ≥0∞) < ζ₂ ω → ω ∈ d'.G ∧
      (∀ s ≤ d'.u, d'.η₁ ω s = η₁ ω s) ∧ ∀ t ≤ d'.r, d'.η₂ ω t = η₂ ω t)
    (h₁ : d'.η₁ = d.η₁) (h₂ : d'.η₂ = d.η₂) (hu : d'.u = d.u) {t : ℝ≥0} (hr : d'.r = d.r + t)
    {O₀ : Set Ω} {β₀ β₁ : Ω → BoundaryWord}
    (hm₀ : IsRetMeanIdentOn κ P h η₁ η₂ ζ₁ ζ₂ u₀ hd O₀ β₀)
    (hm₁ : IsRetMeanIdentOn κ P h η₁ η₂ ζ₁ ζ₂ u₀ hd'
      {ω | IsOrdinaryRetainedPair (η₁ ω) (ζ₁ ω) d'.u (η₂ ω) (ζ₂ ω) d'.r} β₁)
    (hw₁ : ∀ᵐ ω ∂P, IsOrdinaryRetainedPair (η₁ ω) (ζ₁ ω) d'.u (η₂ ω) (ζ₂ ω) d'.r →
      (β₁ ω).IsSorted ∧ IsRetainedWord κ θ₁ θ₂ (η₁ ω) d'.u (η₂ ω) d'.r (d'.inv ω) (β₁ ω)) :
    ∀ᵐ ω ∂P, ω ∈ O₀ → IsOrdinaryRetainedPair (η₁ ω) (ζ₁ ω) d'.u (η₂ ω) (ζ₂ ω) d'.r → ω ∈ d.E →
      (β₀ ω).IsSorted →
      ∀ (W : ℝ≥0 → ℝ) (γ : ℝ≥0 → ℂ) (ζc : ℝ≥0∞) (Q : ℝ≥0), IsGeneratingTrace W ζc γ → Continuous W →
        W 0 = 0 → InjOn γ {s | (s : ℝ≥0∞) ≤ ζc} → (Q : ℝ≥0∞) < ζc → 0 < Q →
        (fun s => d.inv ω (γ s)) '' Icc 0 Q = d.η₂ ω '' Icc d.r (d.r + t) →
        d.inv ω (γ Q) = d.η₂ ω (d.r + t) →
        (∀ w ∈ H, (d'.chart ω).2.1 w = (d.chart ω).2.1 (fwdMapInv (fun s : ℝ => W s.toNNReal) Q w)) ∧
        (∀ w ∈ H, (d'.chart ω).2.2 ((d'.chart ω).2.1 w) =
          (logDerivFwd (fun s : ℝ => W s.toNNReal) Q (fwdMapInv (fun s : ℝ => W s.toNNReal) Q w)).im +
            (d.chart ω).2.2 ((d.chart ω).2.1 (fwdMapInv (fun s : ℝ => W s.toNNReal) Q w))) ∧
        ∃ S : Set ℝ, S.Finite ∧ ∀ y ∉ S,
          forceBoundaryData κ (flowLineRhoL κ (β₀ ω).fn (β₀ ω).jumps 0 θ₂)
              (flowLineRhoR κ (β₀ ω).fn (β₀ ω).jumps 0 θ₂)
              (fun i => -rightImg (fun s : ℝ => -W s.toNNReal) (-flowLineXL (β₀ ω).fn (β₀ ω).jumps 0 i) Q - W Q)
              (fun j => rightImg (fun s : ℝ => W s.toNNReal) (flowLineXR (β₀ ω).fn (β₀ ω).jumps 0 j) Q - W Q) y =
            (β₁ ω).fn y + θ₂ * QuantumZipper.chiC κ := by
  have hl := ae_retLine_facts_of_retainedWord_dense (θ₁ := θ₁) (θ₂ := θ₂) hL75 hκ hκ4 hb hh hη₁ hη₂ hu₀ hd hd'
    hag hag' h₁ h₂ hu hr hm₀ hm₁
  filter_upwards [hl, hag', hw₁] with ω hlω hag'ω hw₁ω
  intro hO₀ hord hE hs₀ W γ ζc Q hg hWc hW0 hinj hQ hQ0 himg htip
  obtain ⟨hG', a₁', a₂'⟩ := hag'ω hord.1 hord.2.1
  have hE' : ω ∈ d'.E := hd'.mem_E_of_ordinary hG' a₁' a₂' hord
  obtain ⟨hs₁, hrw⟩ := hw₁ω hord
  have hrw' : IsRetainedWord κ θ₁ θ₂ (d.η₁ ω) d.u (d.η₂ ω) (d.r + t) (d'.inv ω) (β₁ ω) := by
    have := isRetainedWord_congr (α' := d'.η₁ ω) (β' := d'.η₂ ω) (fun s hs => (a₁' s hs.2).symm)
      (fun s hs => (a₂' s hs.2).symm) hrw
    rwa [h₁, h₂, hu, hr] at this
  exact hlω hO₀ hord hord.1 hord.2.1 hE hE' hs₀ hs₁ hrw' W γ ζc Q hg hWc hW0 hinj hQ hQ0 himg htip

/-- **The first continuation's line facts along its canonical clock** (the `hline` facts of K2 at a line `t`, for the
canonical chart path of `RetOrdDetFstStatement`). Fix a line `t > 0` with data `d'` at `(u + t, r)`. Almost surely, at
an ordinary pair `(u, r)` whose later pair `(u + t, r)` is again ordinary, with `t` before the continuation's stop:
the canonical chart path `γ` of the first continuation (the canonical clock in the chart shifted by `tipPos`, equal to
`canonRetPath … (tipPos d η₁ ω) − tipPos d η₁ ω`, `canonRetPath_shift`) reaches the line at a capacity time
`0 < Q <` its lifetime, and for EVERY continuous driver `W` from `0` generating `γ`, the line facts (III-a) and (III-b)
hold at `Q` in the charts recentred at `tipPos d η₁ ω` and `tipPos d' η₁ ω`. The stop-line word `β₀` and the later word
`β₁` are any words with the mean identification and the outer word at the respective ordinary pairs (the data of
`RetOrdMeanWordStatement` at the two pairs). -/
theorem ae_retLine_facts_fst_canon (hL75 : Theorem15.Lemma75Statement.{u}) (hκ : 0 < κ) (hκ4 : κ < 4)
    (hb : IsPiecewiseConstantBoundaryData b jumps) (hx : x₂ ≤ x₁) (hθ : θ₁ < θ₂)
    (hh : IsGFFWithBoundaryData P h b jumps)
    (hη₁ : IsFlowLine κ b jumps x₁ θ₁ P h η₁ ζ₁) (hη₂ : IsFlowLine κ b jumps x₂ θ₂ P h η₂ ζ₂)
    {u₀ : ℂ → ℝ} (hu₀ : IsBoundedHarmonicExtension b jumps u₀)
    {d d' : RetData Ω} (hd : d.IsMeasGood) (hd' : d'.IsMeasGood)
    (hag : ∀ᵐ ω ∂P, (d.u : ℝ≥0∞) < ζ₁ ω → (d.r : ℝ≥0∞) < ζ₂ ω → ω ∈ d.G ∧
      (∀ s ≤ d.u, d.η₁ ω s = η₁ ω s) ∧ ∀ t ≤ d.r, d.η₂ ω t = η₂ ω t)
    (hag' : ∀ᵐ ω ∂P, (d'.u : ℝ≥0∞) < ζ₁ ω → (d'.r : ℝ≥0∞) < ζ₂ ω → ω ∈ d'.G ∧
      (∀ s ≤ d'.u, d'.η₁ ω s = η₁ ω s) ∧ ∀ t ≤ d'.r, d'.η₂ ω t = η₂ ω t)
    (h₁ : d'.η₁ = d.η₁) (h₂ : d'.η₂ = d.η₂) {t : ℝ≥0} (ht0 : 0 < t) (hu : d'.u = d.u + t) (hr : d'.r = d.r)
    {β₀ β₁ : Ω → BoundaryWord}
    (hm₀ : IsRetMeanIdentOn κ P h η₁ η₂ ζ₁ ζ₂ u₀ hd
      {ω | IsOrdinaryRetainedPair (η₁ ω) (ζ₁ ω) d.u (η₂ ω) (ζ₂ ω) d.r} β₀)
    (hw₀ : ∀ᵐ ω ∂P, IsOrdinaryRetainedPair (η₁ ω) (ζ₁ ω) d.u (η₂ ω) (ζ₂ ω) d.r → (β₀ ω).IsSorted)
    (hm₁ : IsRetMeanIdentOn κ P h η₁ η₂ ζ₁ ζ₂ u₀ hd'
      {ω | IsOrdinaryRetainedPair (η₁ ω) (ζ₁ ω) d'.u (η₂ ω) (ζ₂ ω) d'.r} β₁)
    (hw₁ : ∀ᵐ ω ∂P, IsOrdinaryRetainedPair (η₁ ω) (ζ₁ ω) d'.u (η₂ ω) (ζ₂ ω) d'.r →
      (β₁ ω).IsSorted ∧ IsRetainedWord κ θ₁ θ₂ (η₁ ω) d'.u (η₂ ω) d'.r (d'.inv ω) (β₁ ω)) :
    ∀ᵐ ω ∂P, IsOrdinaryRetainedPair (η₁ ω) (ζ₁ ω) d.u (η₂ ω) (ζ₂ ω) d.r →
      IsOrdinaryRetainedPair (η₁ ω) (ζ₁ ω) d'.u (η₂ ω) (ζ₂ ω) d'.r →
      (t : ℝ≥0∞) < contLife (η₁ ω) (ζ₁ ω) d.u (η₁ ω '' Icc 0 d.u ∪ η₂ ω '' Icc 0 d.r) →
      0 < (chartClock (contPath (d.D ω) (fun z => d.fwd ω z - tipPos d η₁ ω) (η₁ ω) d.u
          (contLife (η₁ ω) (ζ₁ ω) d.u (η₁ ω '' Icc 0 d.u ∪ η₂ ω '' Icc 0 d.r))) t).toNNReal ∧
      (((chartClock (contPath (d.D ω) (fun z => d.fwd ω z - tipPos d η₁ ω) (η₁ ω) d.u
          (contLife (η₁ ω) (ζ₁ ω) d.u (η₁ ω '' Icc 0 d.u ∪ η₂ ω '' Icc 0 d.r))) t).toNNReal : ℝ≥0) : ℝ≥0∞) <
        canonRetLife (d.D ω) (fun z => d.fwd ω z - tipPos d η₁ ω) (η₁ ω) (ζ₁ ω) d.u
          (η₁ ω '' Icc 0 d.u ∪ η₂ ω '' Icc 0 d.r) 0 ∧
      ∀ W : ℝ≥0 → ℝ, Continuous W → W 0 = 0 →
        IsGeneratingTrace W (canonRetLife (d.D ω) (fun z => d.fwd ω z - tipPos d η₁ ω) (η₁ ω) (ζ₁ ω) d.u
          (η₁ ω '' Icc 0 d.u ∪ η₂ ω '' Icc 0 d.r) 0)
          (canonRetPath (d.D ω) (fun z => d.fwd ω z - tipPos d η₁ ω) (η₁ ω) (ζ₁ ω) d.u
            (η₁ ω '' Icc 0 d.u ∪ η₂ ω '' Icc 0 d.r) 0) →
        let Q := (chartClock (contPath (d.D ω) (fun z => d.fwd ω z - tipPos d η₁ ω) (η₁ ω) d.u
          (contLife (η₁ ω) (ζ₁ ω) d.u (η₁ ω '' Icc 0 d.u ∪ η₂ ω '' Icc 0 d.r))) t).toNNReal
        (∀ w ∈ H, ((d'.chart ω).recenter (tipPos d' η₁ ω)).2.1 w =
          ((d.chart ω).recenter (tipPos d η₁ ω)).2.1 (fwdMapInv (fun s : ℝ => W s.toNNReal) Q w)) ∧
        (∀ w ∈ H, ((d'.chart ω).recenter (tipPos d' η₁ ω)).2.2 (((d'.chart ω).recenter (tipPos d' η₁ ω)).2.1 w) =
          (logDerivFwd (fun s : ℝ => W s.toNNReal) Q (fwdMapInv (fun s : ℝ => W s.toNNReal) Q w)).im +
            ((d.chart ω).recenter (tipPos d η₁ ω)).2.2
              (((d.chart ω).recenter (tipPos d η₁ ω)).2.1 (fwdMapInv (fun s : ℝ => W s.toNNReal) Q w))) ∧
        ∃ S : Set ℝ, S.Finite ∧ ∀ y ∉ S,
          forceBoundaryData κ
              (flowLineRhoL κ (Exist.StagedLaw.BoundaryWord.shiftW (tipPos d η₁ ω) (β₀ ω)).fn
                (Exist.StagedLaw.BoundaryWord.shiftW (tipPos d η₁ ω) (β₀ ω)).jumps 0 θ₁)
              (flowLineRhoR κ (Exist.StagedLaw.BoundaryWord.shiftW (tipPos d η₁ ω) (β₀ ω)).fn
                (Exist.StagedLaw.BoundaryWord.shiftW (tipPos d η₁ ω) (β₀ ω)).jumps 0 θ₁)
              (fun i => -rightImg (fun s : ℝ => -W s.toNNReal)
                (-flowLineXL (Exist.StagedLaw.BoundaryWord.shiftW (tipPos d η₁ ω) (β₀ ω)).fn
                  (Exist.StagedLaw.BoundaryWord.shiftW (tipPos d η₁ ω) (β₀ ω)).jumps 0 i) Q - W Q)
              (fun j => rightImg (fun s : ℝ => W s.toNNReal)
                (flowLineXR (Exist.StagedLaw.BoundaryWord.shiftW (tipPos d η₁ ω) (β₀ ω)).fn
                  (Exist.StagedLaw.BoundaryWord.shiftW (tipPos d η₁ ω) (β₀ ω)).jumps 0 j) Q - W Q) y =
            (Exist.StagedLaw.BoundaryWord.shiftW (tipPos d' η₁ ω) (β₁ ω)).fn y + θ₁ * QuantumZipper.chiC κ := by
  have hl := ae_retLine_facts_fst_of_ordinary hL75 hκ hκ4 hb hx hθ hh hη₁ hη₂ hu₀ hd hd' hag hag' h₁ h₂ hu hr
    hm₀ hm₁ hw₁
  have hpg := ae_isPathGood_of_isFlowLine Theorem15.aux25Statement hκ hκ4 hη₁
  filter_upwards [hl, hag, hag', hw₀, hpg] with ω hlω hagω hag'ω hw₀ω hpgω
  intro hord hord' htV
  obtain ⟨hG, a₁, a₂⟩ := hagω hord.1 hord.2.1
  obtain ⟨-, a₁', -⟩ := hag'ω hord'.1 hord'.2.1
  have hE : ω ∈ d.E := hd.mem_E_of_ordinary hG a₁ a₂ hord
  have e₁ : EqOn (d.η₁ ω) (η₁ ω) (Icc 0 d.u) := fun s hs => a₁ s hs.2
  have e₂ : EqOn (d.η₂ ω) (η₂ ω) (Icc 0 d.r) := fun s hs => a₂ s hs.2
  have e₁' : ∀ s ≤ d.u + t, d.η₁ ω s = η₁ ω s := fun s hs => by
    rw [← h₁]; exact a₁' s (hu ▸ hs)
  -- the pathwise premises of the canonical clock at the stop line
  have hinj₁ : InjOn (η₁ ω) (Icc 0 d.u) := Sec7.IsPathGood.injOn_Icc hpgω hord.1.le
  have hpH : d.η₁ ω d.u ∈ H := by rw [a₁ d.u le_rfl]; exact hord.2.2.1
  have hpO : d.η₁ ω d.u ∉ d.η₂ ω '' Icc 0 d.r := by
    rw [a₁ d.u le_rfl, e₂.image_eq]; exact hord.2.2.2.2.2.1
  have hcl : d.η₁ ω d.u ∈ closure (activeDomain (d.η₁ ω) d.u (d.η₂ ω) d.r) := by
    rw [a₁ d.u le_rfl, activeDomain_congr_Icc e₁ e₂]; exact hord.2.2.2.2.2.2.1
  have hne₁ : ∀ s < d.u, d.η₁ ω s ≠ d.η₁ ω d.u := fun s hs he => by
    rw [a₁ s hs.le, a₁ d.u le_rfl] at he
    exact hs.ne (hinj₁ ⟨zero_le, hs.le⟩ ⟨zero_le, le_rfl⟩ he)
  obtain ⟨-, -, -, -, hinj, hfacts⟩ :=
    exists_ordContFst_facts hd hE hpgω (fun s hs => a₁ s hs) hord.1 hpH hpO hcl hne₁
  have hK : η₁ ω '' Icc 0 d.u ∪ d.η₂ ω '' Icc 0 d.r = η₁ ω '' Icc 0 d.u ∪ η₂ ω '' Icc 0 d.r := by
    rw [e₂.image_eq]
  have htp : tipPos d d.η₁ ω = tipPos d η₁ ω := by simp only [tipPos, a₁ d.u le_rfl]
  rw [hK, htp] at hinj hfacts
  obtain ⟨hQpos, hQlt, himg, htip⟩ := hfacts t ht0 htV
  refine ⟨hQpos, hQlt, fun W hWc hW0 hgen => ?_⟩
  have himg' : (fun s => d.inv ω (canonRetPath (d.D ω) (fun z => d.fwd ω z - tipPos d η₁ ω) (η₁ ω) (ζ₁ ω) d.u
      (η₁ ω '' Icc 0 d.u ∪ η₂ ω '' Icc 0 d.r) 0 s + tipPos d η₁ ω)) ''
        Icc 0 (chartClock (contPath (d.D ω) (fun z => d.fwd ω z - tipPos d η₁ ω) (η₁ ω) d.u
          (contLife (η₁ ω) (ζ₁ ω) d.u (η₁ ω '' Icc 0 d.u ∪ η₂ ω '' Icc 0 d.r))) t).toNNReal =
      d.η₁ ω '' Icc d.u (d.u + t) := by
    rw [himg]
    exact (image_congr fun s hs => e₁' s hs.2).symm
  have htip' : d.inv ω (canonRetPath (d.D ω) (fun z => d.fwd ω z - tipPos d η₁ ω) (η₁ ω) (ζ₁ ω) d.u
      (η₁ ω '' Icc 0 d.u ∪ η₂ ω '' Icc 0 d.r) 0 (chartClock (contPath (d.D ω)
        (fun z => d.fwd ω z - tipPos d η₁ ω) (η₁ ω) d.u
          (contLife (η₁ ω) (ζ₁ ω) d.u (η₁ ω '' Icc 0 d.u ∪ η₂ ω '' Icc 0 d.r))) t).toNNReal +
        tipPos d η₁ ω) = d.η₁ ω (d.u + t) := by
    rw [htip, e₁' (d.u + t) le_rfl]
  exact hlω hord hord' hE (hw₀ω hord) (tipPos d η₁ ω) W _ _ _ hgen hWc hW0 hinj hQlt hQpos himg' htip'

end Wire

end OrdDet

end RLC

end InteractingSLE
