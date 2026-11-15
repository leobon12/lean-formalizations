/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.AStopSafeLaw
import InteractingSLE.Spec.Supplement.AStopSafeFill
import InteractingSLE.Spec.Supplement.OrdSwapLine

/-!
# The later-line facts of the A-stopped first continuation

Packet PROVE-T15-ASTOP-SAFE (item 5 of `RLC.OrdModel.AStopSourceInputs`, first continuation). The `hline` input of
`RetAux79.hasSafeLaw_of_retLines_indicator` for the A-stopped first continuation of PROVE-T15-ASTOP-PROC (chart path
`AStopProc.fstChart d τ η₁' ζ₁`, the chart of `d` recentred at the seed `τ`), with

* the stop chart `(b₀.chart).recenter τ`, `b₀ = retFam G η₁' η₂'' d.u d.r` (versions of the two flow lines);
* the later charts of the **exchanged** later data `retFam G' η₂'' η₁' d.r (d.u + t)` (PROVE-T15-ORDDET6: one later
  chart for ordinary and enclosed later pairs) and the later word `OrdSwap.fstLateWord`;
* **`ae_aLine_fst_pos`** (lines `t > 0`, ORDDET6's `ae_retLine_facts_fst_late` along PROC's path, ORDDET3's
  `exists_ordContFst_facts`) and **`ae_aLine_fst_zero`** (the stop line, ORDDET6's swap lemma
  `isRetMeanIdentOn_swap`): the later pair is live, lies in the later chart event, and the later domain is the
  filled-union complement; the later word is sorted and identifies the line kernel's mean (in the exchanged later
  chart); the later chart is the recentred stop chart composed with `f_Q⁻¹` (with the lift chain rule); the typed force
  data of the seeded stop word at the clock are the later word.

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

open Restart Restart.RetAux79 Supp7 Sec7 Sec7.Lemma76F MartChar.RealFlow AStopProc OrdGap OrdSwap
open Exist.StagedLaw.BoundaryWord

universe u

section Helpers

variable {Ω : Type*}

/-- The tip position only depends on the domain, the forward chart, the cutoff and the tip. -/
theorem tipPos_eq_of {d e : RetData Ω} {η η' : Ω → ℝ≥0 → ℂ} {ω : Ω} (hD : e.D ω = d.D ω) (hf : e.fwd ω = d.fwd ω)
    (hu : e.u = d.u) (ht : η' ω d.u = η ω d.u) : tipPos e η' ω = tipPos d η ω := by
  unfold tipPos
  rw [hD, hf, hu, ht]

/-- On a sample of both chart events, data with the same chart have the same forward chart. -/
theorem fwd_eq_of_chart_eq {d e : RetData Ω} {ω : Ω} (hd : ω ∈ d.E) (he : ω ∈ e.E) (hch : e.chart ω = d.chart ω) :
    e.fwd ω = d.fwd ω := by
  have h := congrArg (fun c : Chart => c.1) hch
  simp only [RetData.chart_of_mem hd, RetData.chart_of_mem he] at h
  exact h

/-- The domain of retained data at a chart sample is the complement of the filled prefixes. -/
theorem D_eq_fill {d : RetData Ω} {ω : Ω} (hE : ω ∈ d.E) :
    d.D ω = H \ fillH (d.η₁ ω '' Icc 0 d.u ∪ d.η₂ ω '' Icc 0 d.r) := by
  show H \ fillH (d.K ω) = _
  rw [RetData.K_of_mem hE, prefixSet]

end Helpers

section Line

variable {κ : ℝ} {b : ℝ → ℝ} {jumps : Finset ℝ} {x₁ x₂ θ₁ θ₂ : ℝ} {Ω : Type u} [mΩ : MeasurableSpace Ω]
  {P : Measure Ω} [IsProbabilityMeasure P] {h : Ω → DistOn upperHalfPlaneOpens} {η₁ η₂ : Ω → ℝ≥0 → ℂ}
  {ζ₁ ζ₂ : Ω → ℝ≥0∞}

/-- **The later-line facts of the A-stopped first continuation at a positive line `t`.** -/
theorem ae_aLine_fst_pos (hL75 : Theorem15.Lemma75Statement.{u}) (hκ : 0 < κ) (hκ4 : κ < 4)
    (hb : IsPiecewiseConstantBoundaryData b jumps) (hx : x₂ ≤ x₁) (hθ : θ₁ < θ₂)
    (hh : IsGFFWithBoundaryData P h b jumps)
    (hη₁ : IsFlowLine κ b jumps x₁ θ₁ P h η₁ ζ₁) (hη₂ : IsFlowLine κ b jumps x₂ θ₂ P h η₂ ζ₂)
    {u₀ : ℂ → ℝ} (hu₀ : IsBoundedHarmonicExtension b jumps u₀) {d : RetData Ω} (hd : d.IsMeasGood)
    (hag : ∀ᵐ ω ∂P, (d.u : ℝ≥0∞) < ζ₁ ω → (d.r : ℝ≥0∞) < ζ₂ ω → ω ∈ d.G ∧
      (∀ s ≤ d.u, d.η₁ ω s = η₁ ω s) ∧ ∀ t ≤ d.r, d.η₂ ω t = η₂ ω t)
    {η₁' η₂'' : Ω → ℝ≥0 → ℂ} {G G' : ℝ≥0 → Set Ω} (hb₀ : (retFam G η₁' η₂'' d.u d.r).IsMeasGood)
    (hagb : ∀ᵐ ω ∂P, (d.u : ℝ≥0∞) < ζ₁ ω → (d.r : ℝ≥0∞) < ζ₂ ω → ω ∈ G d.r ∧
      (∀ s ≤ d.u, η₁' ω s = η₁ ω s) ∧ ∀ t ≤ d.r, η₂'' ω t = η₂ ω t)
    (hdG' : ∀ u', (retFam G' η₂'' η₁' d.r u').IsMeasGood)
    (hagF' : ∀ u' : ℝ≥0, ∀ᵐ ω ∂P, (d.r : ℝ≥0∞) < ζ₂ ω → (u' : ℝ≥0∞) < ζ₁ ω → ω ∈ G' u' ∧
      (∀ s ≤ d.r, η₂'' ω s = η₂ ω s) ∧ ∀ t ≤ u', η₁' ω t = η₁ ω t)
    {β₀ : Ω → BoundaryWord}
    (hm₀ : IsRetMeanIdentOn κ P h η₁ η₂ ζ₁ ζ₂ u₀ hb₀
      {ω | IsOrdinaryRetainedPair (η₁ ω) (ζ₁ ω) d.u (η₂ ω) (ζ₂ ω) d.r} β₀)
    (hsort : ∀ᵐ ω ∂P, IsOrdinaryRetainedPair (η₁ ω) (ζ₁ ω) d.u (η₂ ω) (ζ₂ ω) d.r → (β₀ ω).IsSorted)
    {τ : Ω → ℝ} {M : Set Ω} (hMg : ∀ ω ∈ M, IsFstGood d η₁ η₂ η₁' ζ₁ ζ₂ x₁ τ ω)
    (hMord : ∀ᵐ ω ∂P, ω ∈ M → IsOrdinaryRetainedPair (η₁ ω) (ζ₁ ω) d.u (η₂ ω) (ζ₂ ω) d.r)
    {W : ℝ≥0 → Ω → ℝ} (hWc : ∀ ω, Continuous fun q => W q ω) (hW0 : ∀ ω, W 0 ω = 0)
    (hgen : ∀ ω ∈ M, IsGeneratingTrace (W · ω) (aLife (fstChart d τ η₁' ζ₁) (fstLifeP d η₁' ζ₁) ω)
      (aPath (fstChart d τ η₁' ζ₁) (fstLifeP d η₁' ζ₁) ω))
    {nL nR : ℕ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ} {xL : Ω → Fin nL → ℝ} {xR : Ω → Fin nR → ℝ}
    (htype : ∀ ω ∈ M, FCDet.IsFlowType κ θ₁ (shiftW (τ ω) (β₀ ω)) (xL ω) (xR ω) ρL ρR)
    {t : ℝ≥0} (ht : 0 < t) {d' : RetData Ω} (hd' : d'.IsMeasGood)
    (hag' : ∀ᵐ ω ∂P, (d'.u : ℝ≥0∞) < ζ₁ ω → (d'.r : ℝ≥0∞) < ζ₂ ω → ω ∈ d'.G ∧
      (∀ s ≤ d'.u, d'.η₁ ω s = η₁ ω s) ∧ ∀ t ≤ d'.r, d'.η₂ ω t = η₂ ω t)
    (hs' : IsSwap d' (retFam G' η₂'' η₁' d.r (d.u + t))) (h₁ : d'.η₁ = η₁') (h₂ : d'.η₂ = η₂'')
    (hu : d'.u = d.u + t) (hr : d'.r = d.r) {β₁ β₂ : Ω → BoundaryWord}
    (hm₁ : IsRetMeanIdentOn κ P h η₁ η₂ ζ₁ ζ₂ u₀ hd' (fstOrdSet η₁ η₂ ζ₁ ζ₂ d') β₁)
    (hw₁ : ∀ᵐ ω ∂P, ω ∈ fstOrdSet η₁ η₂ ζ₁ ζ₂ d' →
      (β₁ ω).IsSorted ∧ IsRetainedWord κ θ₁ θ₂ (η₁ ω) d'.u (η₂ ω) d'.r (d'.inv ω) (β₁ ω))
    (hm₂ : IsRetMeanIdentOn κ P h η₂ η₁ ζ₂ ζ₁ u₀ (hdG' (d.u + t))
      (enclSet η₂ η₁ ζ₂ ζ₁ (retFam G' η₂'' η₁' d.r (d.u + t))) β₂)
    (hw₂ : ∀ᵐ ω ∂P, ω ∈ enclSet η₂ η₁ ζ₂ ζ₁ (retFam G' η₂'' η₁' d.r (d.u + t)) →
      (β₂ ω).IsSorted ∧ IsRetainedWord κ θ₂ θ₁ (η₂ ω) (retFam G' η₂'' η₁' d.r (d.u + t)).u (η₁ ω)
        (retFam G' η₂'' η₁' d.r (d.u + t)).r ((retFam G' η₂'' η₁' d.r (d.u + t)).inv ω) (β₂ ω))
    {ηc₁ ηc₂ : Ω → ℝ≥0 → ℂ} {g : Ω → DistOn upperHalfPlaneOpens}
    (hc₁ : ∀ ω, Continuous (ηc₁ ω)) (hc₂ : ∀ ω, Continuous (ηc₂ ω))
    (hmc₁ : ∀ s, Measurable fun ω => ηc₁ ω s) (hmc₂ : ∀ s, Measurable fun ω => ηc₂ ω s)
    (hagc₁ : ∀ᵐ ω ∂P, ∀ s, ηc₁ ω s = η₁ ω (capTime (capR (d.u + t) d.r) (ζ₁ ω) s))
    (hagc₂ : ∀ᵐ ω ∂P, ∀ s, ηc₂ ω s = η₂ ω (capTime (capR (d.u + t) d.r) (ζ₂ ω) s))
    (hg : LocalSets.IsLocalSetMean (cstUnion ηc₁ ηc₂ (d.u + t) d.r) (WholeField.centredField h u₀) P g) :
    ∀ᵐ ω ∂P, ω ∈ M →
      (aClock (fstChart d τ η₁' ζ₁) t ω : ℝ≥0∞) < aLife (fstChart d τ η₁' ζ₁) (fstLifeP d η₁' ζ₁) ω →
      ((((d.u + t : ℝ≥0) : ℝ≥0∞) < ζ₁ ω ∧ (d.r : ℝ≥0∞) < ζ₂ ω ∧
        ω ∈ (retFam G' η₂'' η₁' d.r (d.u + t)).E ∧
        (retFam G' η₂'' η₁' d.r (d.u + t)).D ω = H \ fillH (η₁ ω '' Icc 0 (d.u + t) ∪ η₂ ω '' Icc 0 d.r))) ∧
      (fstLateWord η₁ η₂ ζ₁ ζ₂ d' β₁ β₂ ω).IsSorted ∧
      (∀ φ : TestOn upperHalfPlaneOpens,
        Chart.chartTransport ((hdG' (d.u + t)).isConformal_chart ω) 1 0 (chiC κ)
          (g ω + SupercriticalConformalCovariance.GM24.smoothDist upperHalfPlaneOpens u₀) φ =
        ∫ w, (fstLateWord η₁ η₂ ζ₁ ζ₂ d' β₁ β₂ ω).mean w * φ w) ∧
      (∀ w ∈ H, ((retFam G' η₂'' η₁' d.r (d.u + t)).chart ω).2.1 w =
        (((retFam G η₁' η₂'' d.u d.r).chart ω).recenter (τ ω)).2.1
          (fwdMapInv (fun s : ℝ => W s.toNNReal ω) (aClock (fstChart d τ η₁' ζ₁) t ω) w)) ∧
      (∀ w ∈ H, ((retFam G' η₂'' η₁' d.r (d.u + t)).chart ω).2.2
          (((retFam G' η₂'' η₁' d.r (d.u + t)).chart ω).2.1 w) =
        (logDerivFwd (fun s : ℝ => W s.toNNReal ω) (aClock (fstChart d τ η₁' ζ₁) t ω)
          (fwdMapInv (fun s : ℝ => W s.toNNReal ω) (aClock (fstChart d τ η₁' ζ₁) t ω) w)).im +
          (((retFam G η₁' η₂'' d.u d.r).chart ω).recenter (τ ω)).2.2
            ((((retFam G η₁' η₂'' d.u d.r).chart ω).recenter (τ ω)).2.1
              (fwdMapInv (fun s : ℝ => W s.toNNReal ω) (aClock (fstChart d τ η₁' ζ₁) t ω) w))) ∧
      ∃ S : Set ℝ, S.Finite ∧ ∀ y ∉ S,
        forceBoundaryData κ ρL ρR
          (fun i => PocketTraversal.geomLW W xL i (aClock (fstChart d τ η₁' ζ₁) t ω) ω -
            W (aClock (fstChart d τ η₁' ζ₁) t ω) ω)
          (fun j => PocketTraversal.geomRW W xR j (aClock (fstChart d τ η₁' ζ₁) t ω) ω -
            W (aClock (fstChart d τ η₁' ζ₁) t ω) ω) y =
          (fstLateWord η₁ η₂ ζ₁ ζ₂ d' β₁ β₂ ω).fn y + θ₁ * chiC κ := by
  have hs : IsSwap (retFam G η₁' η₂'' d.u d.r) (retFam G' η₂'' η₁' d.r d.u) := ⟨rfl, rfl, rfl, rfl⟩
  have hf := ae_retLine_facts_fst_late hL75 hκ hκ4 hb hx hθ hh hη₁ hη₂ hu₀ hb₀ (hdG' d.u) hd' (hdG' (d.u + t))
    hagb (hagF' d.u) hag' (hagF' (d.u + t)) hs h₁ h₂ hu hr hs' hm₀ hm₁ hw₁ hm₂ hw₂
  have hmean := isRetMeanIdentOn_apply_swap hs'
    (isRetMeanIdentOn_fstLateWord hd' (hdG' (d.u + t)) hag' (hagF' (d.u + t)) hs' hm₁ hm₂) ηc₁ ηc₂ g hc₁ hc₂
    hmc₁ hmc₂ (by rw [hu, hr]; exact hagc₁) (by rw [hu, hr]; exact hagc₂) (by rw [hu, hr]; exact hg)
  have hsorted := ae_isSorted_fstLateWord (hw₁.mono fun ω h hω => (h hω).1) (hw₂.mono fun ω h hω => (h hω).1)
  filter_upwards [hf, hmean, hsorted, hMord, hsort, hag, hagb, hagF' (d.u + t)]
    with ω hfω hmω hsω hordω hs₀ hagω hbω hFt hωM hlt
  obtain ⟨hr₂, hfp, a₁, a₂, e₁⟩ := hMg ω hωM
  have hord := hordω hωM
  have hgood := hfp.isAGood hd
  have htL : (t : ℝ≥0∞) < fstLifeP d η₁' ζ₁ ω := hgood.lt_of_aClock_lt hlt
  obtain ⟨-, -, -, -, hinj, hQ⟩ := OrdDet.exists_ordContFst_facts hd hfp.mem_E hfp.path hfp.agree hfp.lt hfp.tipH
    hfp.tipO hfp.tipCl hfp.tipNe
  have hA : fstSet d η₁' ω = η₁' ω '' Icc 0 d.u ∪ d.η₂ ω '' Icc 0 d.r := union_comm _ _
  have hL : fstLifeP d η₁' ζ₁ ω = contLife (η₁' ω) (ζ₁ ω) d.u (η₁' ω '' Icc 0 d.u ∪ d.η₂ ω '' Icc 0 d.r) := by
    rw [fstLifeP, hA]
  have hΓ : fstChart d τ η₁' ζ₁ ω = contPath (d.D ω) (fun z => d.fwd ω z - tipPos d d.η₁ ω) (η₁' ω) d.u
      (contLife (η₁' ω) (ζ₁ ω) d.u (η₁' ω '' Icc 0 d.u ∪ d.η₂ ω '' Icc 0 d.r)) := by
    rw [fstChart, hL, hfp.seed]
  rw [hL] at htL
  obtain ⟨hQ0, -, himg, htip⟩ := hQ t ht htL
  have hQe : aClock (fstChart d τ η₁' ζ₁) t ω = (chartClock (contPath (d.D ω)
      (fun z => d.fwd ω z - tipPos d d.η₁ ω) (η₁' ω) d.u
      (contLife (η₁' ω) (ζ₁ ω) d.u (η₁' ω '' Icc 0 d.u ∪ d.η₂ ω '' Icc 0 d.r))) t).toNNReal := by
    rw [hgood.aClock_eq t, hΓ]
  have hP : aPath (fstChart d τ η₁' ζ₁) (fstLifeP d η₁' ζ₁) ω = canonRetPath (d.D ω)
      (fun z => d.fwd ω z - tipPos d d.η₁ ω) (η₁' ω) (ζ₁ ω) d.u (η₁' ω '' Icc 0 d.u ∪ d.η₂ ω '' Icc 0 d.r) 0 := by
    rw [canonRetPath_zero]
    unfold aPath
    rw [hΓ, hL]
  have hLc : aLife (fstChart d τ η₁' ζ₁) (fstLifeP d η₁' ζ₁) ω = canonRetLife (d.D ω)
      (fun z => d.fwd ω z - tipPos d d.η₁ ω) (η₁' ω) (ζ₁ ω) d.u (η₁' ω '' Icc 0 d.u ∪ d.η₂ ω '' Icc 0 d.r) 0 := by
    rw [canonRetLife_zero]
    unfold aLife
    rw [hΓ, hL]
  rw [← hQe, ← hP] at himg htip
  rw [← hP, ← hLc] at hinj
  -- the line is alive and the continuation has no new contact before it
  have hstop : ((d.u + t : ℝ≥0) : ℝ≥0∞) < contStop (η₁' ω) (ζ₁ ω) d.u
      (η₁' ω '' Icc 0 d.u ∪ d.η₂ ω '' Icc 0 d.r) := coe_add_lt_iff.1 htL
  have hut : ((d.u + t : ℝ≥0) : ℝ≥0∞) < ζ₁ ω := hstop.trans_le contStop_le
  have hle : ∀ s : ℝ≥0, s ≤ d.u + t → (s : ℝ≥0∞) ≤ ζ₁ ω := fun s hs =>
    (ENNReal.coe_le_coe.2 hs).trans hut.le
  have hnc : ∀ s, d.u < s → s ≤ d.u + t → η₁ ω s ∉ η₂ ω '' Icc 0 d.r := by
    intro s hs1 hs2 hmem
    have hs := notMem_of_lt_contStop hs1 ((ENNReal.coe_le_coe.2 hs2).trans_lt hstop)
    rw [e₁ s (hle s hs2), image_congr fun s hs => a₂ s hs.2] at hs
    exact hs (Or.inr hmem)
  -- the stop charts of `d` and of the family agree
  obtain ⟨hG, -, -⟩ := hagω hfp.lt hr₂
  obtain ⟨hG0, f₁, f₂⟩ := hbω hfp.lt hr₂
  obtain ⟨hG'', g₂, g₁⟩ := hFt hr₂ hut
  obtain ⟨hEiff, hDeq, hch⟩ := RetData.chart_eq_of_agree (d := d) (G' := G d.r) (η₁' := η₁') (η₂' := η₂'') hG hG0
    (fun s hs => (f₁ s hs).trans (a₁ s hs).symm) (fun s hs => (f₂ s hs).trans (a₂ s hs).symm)
  have hE0 : ω ∈ (retFam G η₁' η₂'' d.u d.r).E := hEiff.2 hfp.mem_E
  have hinv : (retFam G η₁' η₂'' d.u d.r).inv ω = d.inv ω := inv_eq_of_chart_eq hfp.mem_E hE0 hch
  have hfwd : (retFam G η₁' η₂'' d.u d.r).fwd ω = d.fwd ω := fwd_eq_of_chart_eq hfp.mem_E hE0 hch
  have htipb : tipPos (retFam G η₁' η₂'' d.u d.r) η₁ ω = tipPos d d.η₁ ω :=
    tipPos_eq_of hDeq hfwd rfl ((a₁ d.u le_rfl).symm)
  have himg' : (fun s => (retFam G η₁' η₂'' d.u d.r).inv ω
      (aPath (fstChart d τ η₁' ζ₁) (fstLifeP d η₁' ζ₁) ω s + tipPos (retFam G η₁' η₂'' d.u d.r) η₁ ω)) ''
        Icc 0 (aClock (fstChart d τ η₁' ζ₁) t ω) =
      (retFam G η₁' η₂'' d.u d.r).η₁ ω '' Icc (retFam G η₁' η₂'' d.u d.r).u
        ((retFam G η₁' η₂'' d.u d.r).u + t) := by
    rw [hinv, htipb]
    exact himg
  have htip' : (retFam G η₁' η₂'' d.u d.r).inv ω (aPath (fstChart d τ η₁' ζ₁) (fstLifeP d η₁' ζ₁) ω
      (aClock (fstChart d τ η₁' ζ₁) t ω) + tipPos (retFam G η₁' η₂'' d.u d.r) η₁ ω) =
      (retFam G η₁' η₂'' d.u d.r).η₁ ω ((retFam G η₁' η₂'' d.u d.r).u + t) := by
    rw [hinv, htipb]
    exact htip
  have hQ0' : 0 < aClock (fstChart d τ η₁' ζ₁) t ω := by rw [hQe]; exact hQ0
  obtain ⟨hmem, hIII, hlift, S, hS, hdat⟩ := hfω hord hord (hs₀ hord) hut hnc (fun q => W q ω) _ _ _
    (hgen ω hωM) (hWc ω) (hW0 ω) hinj hlt hQ0' himg' htip'
  have hτ : τ ω = tipPos (retFam G η₁' η₂'' d.u d.r) η₁ ω := hfp.seed.trans htipb.symm
  have hEt : ω ∈ (retFam G' η₂'' η₁' d.r (d.u + t)).E := by
    rcases hmem with hord' | hencl
    · refine hs'.mem_E_of_ordinary (hdG' (d.u + t)) hG'' (fun s hs => ?_) (fun s hs => ?_) hord'
      · rw [h₁]; exact g₁ s (hu ▸ hs)
      · rw [h₂]; exact g₂ s (hr ▸ hs)
    · exact hencl.2.2.1
  have hDt : (retFam G' η₂'' η₁' d.r (d.u + t)).D ω =
      H \ fillH (η₁ ω '' Icc 0 (d.u + t) ∪ η₂ ω '' Icc 0 d.r) := by
    rw [D_eq_fill hEt, union_comm]
    show H \ fillH (η₁' ω '' Icc 0 (d.u + t) ∪ η₂'' ω '' Icc 0 d.r) = _
    rw [image_congr fun s hs => g₁ s hs.2, image_congr fun s hs => g₂ s hs.2]
  refine ⟨⟨hut, hr₂, hEt, hDt⟩, hsω hmem, hmω hmem, ?_, ?_, S, hS, fun y hy => ?_⟩
  · rw [hτ]; exact hIII
  · rw [hτ]; exact hlift
  · have h1 := forceBoundaryData_geom_of_isFlowType (htype ω hωM) (fun s => W s ω)
      (aClock (fstChart d τ η₁' ζ₁) t ω) y
    rw [hτ] at h1
    exact h1.trans (hdat y hy)

omit [IsProbabilityMeasure P] in
/-- **The facts at the stop line of the first continuation** (`t = 0`, the clock at `0`): the seeded stop word with its
mean identification in the exchanged chart of the line `(u + 0, r)` (ORDDET6's swap lemma), the recentred chart, and
the typed force data at time `0`. -/
theorem ae_aLine_fst_zero (hκ : 0 < κ) {u₀ : ℂ → ℝ} {d : RetData Ω}
    (hag : ∀ᵐ ω ∂P, (d.u : ℝ≥0∞) < ζ₁ ω → (d.r : ℝ≥0∞) < ζ₂ ω → ω ∈ d.G ∧
      (∀ s ≤ d.u, d.η₁ ω s = η₁ ω s) ∧ ∀ t ≤ d.r, d.η₂ ω t = η₂ ω t)
    {η₁' η₂'' : Ω → ℝ≥0 → ℂ} {G G' : ℝ≥0 → Set Ω} (hb₀ : (retFam G η₁' η₂'' d.u d.r).IsMeasGood)
    (hagb : ∀ᵐ ω ∂P, (d.u : ℝ≥0∞) < ζ₁ ω → (d.r : ℝ≥0∞) < ζ₂ ω → ω ∈ G d.r ∧
      (∀ s ≤ d.u, η₁' ω s = η₁ ω s) ∧ ∀ t ≤ d.r, η₂'' ω t = η₂ ω t)
    (hdG' : ∀ u', (retFam G' η₂'' η₁' d.r u').IsMeasGood)
    (hagF' : ∀ u' : ℝ≥0, ∀ᵐ ω ∂P, (d.r : ℝ≥0∞) < ζ₂ ω → (u' : ℝ≥0∞) < ζ₁ ω → ω ∈ G' u' ∧
      (∀ s ≤ d.r, η₂'' ω s = η₂ ω s) ∧ ∀ t ≤ u', η₁' ω t = η₁ ω t)
    {β₀ : Ω → BoundaryWord}
    (hm₀ : IsRetMeanIdentOn κ P h η₁ η₂ ζ₁ ζ₂ u₀ hb₀
      {ω | IsOrdinaryRetainedPair (η₁ ω) (ζ₁ ω) d.u (η₂ ω) (ζ₂ ω) d.r} β₀)
    (hsort : ∀ᵐ ω ∂P, IsOrdinaryRetainedPair (η₁ ω) (ζ₁ ω) d.u (η₂ ω) (ζ₂ ω) d.r → (β₀ ω).IsSorted)
    {τ : Ω → ℝ} {M : Set Ω} (hMg : ∀ ω ∈ M, IsFstGood d η₁ η₂ η₁' ζ₁ ζ₂ x₁ τ ω)
    (hMord : ∀ᵐ ω ∂P, ω ∈ M → IsOrdinaryRetainedPair (η₁ ω) (ζ₁ ω) d.u (η₂ ω) (ζ₂ ω) d.r)
    {W : ℝ≥0 → Ω → ℝ} (hWc : ∀ ω, Continuous fun q => W q ω) (hW0 : ∀ ω, W 0 ω = 0)
    {nL nR : ℕ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ} {xL : Ω → Fin nL → ℝ} {xR : Ω → Fin nR → ℝ}
    (htype : ∀ ω ∈ M, FCDet.IsFlowType κ θ₁ (shiftW (τ ω) (β₀ ω)) (xL ω) (xR ω) ρL ρR)
    {ηc₁ ηc₂ : Ω → ℝ≥0 → ℂ} {g : Ω → DistOn upperHalfPlaneOpens}
    (hc₁ : ∀ ω, Continuous (ηc₁ ω)) (hc₂ : ∀ ω, Continuous (ηc₂ ω))
    (hmc₁ : ∀ s, Measurable fun ω => ηc₁ ω s) (hmc₂ : ∀ s, Measurable fun ω => ηc₂ ω s)
    (hagc₁ : ∀ᵐ ω ∂P, ∀ s, ηc₁ ω s = η₁ ω (capTime (capR (d.u + 0) d.r) (ζ₁ ω) s))
    (hagc₂ : ∀ᵐ ω ∂P, ∀ s, ηc₂ ω s = η₂ ω (capTime (capR (d.u + 0) d.r) (ζ₂ ω) s))
    (hg : LocalSets.IsLocalSetMean (cstUnion ηc₁ ηc₂ (d.u + 0) d.r) (WholeField.centredField h u₀) P g) :
    ∀ᵐ ω ∂P, ω ∈ M →
      ((((d.u + 0 : ℝ≥0) : ℝ≥0∞) < ζ₁ ω ∧ (d.r : ℝ≥0∞) < ζ₂ ω ∧
        ω ∈ (retFam G' η₂'' η₁' d.r (d.u + 0)).E ∧
        (retFam G' η₂'' η₁' d.r (d.u + 0)).D ω = H \ fillH (η₁ ω '' Icc 0 (d.u + 0) ∪ η₂ ω '' Icc 0 d.r))) ∧
      (shiftW (τ ω) (β₀ ω)).IsSorted ∧
      (∀ φ : TestOn upperHalfPlaneOpens,
        Chart.chartTransport ((hdG' (d.u + 0)).isConformal_chart ω) 1 0 (chiC κ)
          (g ω + SupercriticalConformalCovariance.GM24.smoothDist upperHalfPlaneOpens u₀) φ =
        ∫ w, (shiftW (τ ω) (β₀ ω)).mean w * φ w) ∧
      (∀ w ∈ H, ((retFam G' η₂'' η₁' d.r (d.u + 0)).chart ω).2.1 w =
        (((retFam G η₁' η₂'' d.u d.r).chart ω).recenter (τ ω)).2.1
          (fwdMapInv (fun s : ℝ => W s.toNNReal ω) (aClock (fstChart d τ η₁' ζ₁) 0 ω) w)) ∧
      (∀ w ∈ H, ((retFam G' η₂'' η₁' d.r (d.u + 0)).chart ω).2.2
          (((retFam G' η₂'' η₁' d.r (d.u + 0)).chart ω).2.1 w) =
        (logDerivFwd (fun s : ℝ => W s.toNNReal ω) (aClock (fstChart d τ η₁' ζ₁) 0 ω)
          (fwdMapInv (fun s : ℝ => W s.toNNReal ω) (aClock (fstChart d τ η₁' ζ₁) 0 ω) w)).im +
          (((retFam G η₁' η₂'' d.u d.r).chart ω).recenter (τ ω)).2.2
            ((((retFam G η₁' η₂'' d.u d.r).chart ω).recenter (τ ω)).2.1
              (fwdMapInv (fun s : ℝ => W s.toNNReal ω) (aClock (fstChart d τ η₁' ζ₁) 0 ω) w))) ∧
      ∃ S : Set ℝ, S.Finite ∧ ∀ y ∉ S,
        forceBoundaryData κ ρL ρR
          (fun i => PocketTraversal.geomLW W xL i (aClock (fstChart d τ η₁' ζ₁) 0 ω) ω -
            W (aClock (fstChart d τ η₁' ζ₁) 0 ω) ω)
          (fun j => PocketTraversal.geomRW W xR j (aClock (fstChart d τ η₁' ζ₁) 0 ω) ω -
            W (aClock (fstChart d τ η₁' ζ₁) 0 ω) ω) y =
          (shiftW (τ ω) (β₀ ω)).fn y + θ₁ * chiC κ := by
  classical
  set O : Set Ω := {ω | IsOrdinaryRetainedPair (η₁ ω) (ζ₁ ω) d.u (η₂ ω) (ζ₂ ω) d.r} with hO
  have hs0 : IsSwap (retFam G η₁' η₂'' d.u d.r) (retFam G' η₂'' η₁' d.r (d.u + 0)) := ⟨rfl, rfl, rfl, add_zero d.u⟩
  -- pathwise facts on `M`
  have hgoodω : ∀ᵐ ω ∂P, ω ∈ M ∩ O → ω ∈ (retFam G η₁' η₂'' d.u d.r).E ∧
      ω ∈ (retFam G' η₂'' η₁' d.r (d.u + 0)).E ∧ τ ω = tipPos (retFam G η₁' η₂'' d.u d.r)
        (retFam G η₁' η₂'' d.u d.r).η₁ ω := by
    filter_upwards [hag, hagb, hagF' (d.u + 0)] with ω hagω hbω hF0 hωMO
    obtain ⟨hr₂, hfp, a₁, a₂, -⟩ := hMg ω hωMO.1
    have hu0 : ((d.u + 0 : ℝ≥0) : ℝ≥0∞) < ζ₁ ω := by rw [add_zero]; exact hfp.lt
    obtain ⟨hG, -, -⟩ := hagω hfp.lt hr₂
    obtain ⟨hG0, f₁, f₂⟩ := hbω hfp.lt hr₂
    obtain ⟨hG'', -, -⟩ := hF0 hr₂ hu0
    obtain ⟨hEiff, hDeq, hch⟩ := RetData.chart_eq_of_agree (d := d) (G' := G d.r) (η₁' := η₁') (η₂' := η₂'')
      hG hG0 (fun s hs => (f₁ s hs).trans (a₁ s hs).symm) (fun s hs => (f₂ s hs).trans (a₂ s hs).symm)
    have hE0 : ω ∈ (retFam G η₁' η₂'' d.u d.r).E := hEiff.2 hfp.mem_E
    refine ⟨hE0, hs0.mem_E_of_ordinary (hdG' (d.u + 0)) hG'' f₁ f₂ hωMO.2, ?_⟩
    rw [hfp.seed]
    exact (tipPos_eq_of (η := d.η₁) (η' := η₁') hDeq (fwd_eq_of_chart_eq hfp.mem_E hE0 hch) rfl
      ((f₁ d.u le_rfl).trans (a₁ d.u le_rfl).symm)).symm
  have hm0' := isRetMeanIdentOn_swap hb₀ (hdG' (d.u + 0)) hs0 (isRetMeanIdentOn_mono hm₀ inter_subset_right) τ
    hgoodω
  have hagc₁' : ∀ᵐ ω ∂P, ∀ s, ηc₁ ω s = η₁ ω (capTime (capR d.u d.r) (ζ₁ ω) s) := by
    simpa only [add_zero] using hagc₁
  have hagc₂' : ∀ᵐ ω ∂P, ∀ s, ηc₂ ω s = η₂ ω (capTime (capR d.u d.r) (ζ₂ ω) s) := by
    simpa only [add_zero] using hagc₂
  have hg' : LocalSets.IsLocalSetMean (cstUnion ηc₁ ηc₂ d.u d.r) (WholeField.centredField h u₀) P g := by
    simpa only [add_zero] using hg
  have hmean := isRetMeanIdentOn_apply_swap hs0 hm0' ηc₁ ηc₂ g hc₁ hc₂ hmc₁ hmc₂ hagc₁' hagc₂' hg'
  filter_upwards [hmean, hgoodω, hMord, hsort, hagb, hagF' (d.u + 0)] with ω hmω hgω hordω hs₀ hbω hF0 hωM
  have hord := hordω hωM
  obtain ⟨hr₂, hfp, -, -, -⟩ := hMg ω hωM
  obtain ⟨hE0, hE0'', hτ⟩ := hgω ⟨hωM, hord⟩
  have hu0 : ((d.u + 0 : ℝ≥0) : ℝ≥0∞) < ζ₁ ω := by rw [add_zero]; exact hfp.lt
  obtain ⟨-, g₂, g₁⟩ := hF0 hr₂ hu0
  have hWc' : Continuous fun s : ℝ => W s.toNNReal ω := (hWc ω).comp continuous_real_toNNReal
  have hW0' : (fun s : ℝ => W s.toNNReal ω) 0 = 0 := by
    show W (0 : ℝ).toNNReal ω = 0
    rw [Real.toNNReal_zero]
    exact hW0 ω
  have hDt : (retFam G' η₂'' η₁' d.r (d.u + 0)).D ω =
      H \ fillH (η₁ ω '' Icc 0 (d.u + 0) ∪ η₂ ω '' Icc 0 d.r) := by
    rw [D_eq_fill hE0'', union_comm]
    show H \ fillH (η₁' ω '' Icc 0 (d.u + 0) ∪ η₂'' ω '' Icc 0 d.r) = _
    rw [image_congr fun s hs => g₁ s hs.2, image_congr fun s hs => g₂ s hs.2]
  have hinv : ∀ w ∈ H, ((retFam G' η₂'' η₁' d.r (d.u + 0)).chart ω).2.1 w =
      (((retFam G η₁' η₂'' d.u d.r).chart ω).recenter (τ ω)).2.1 w := fun w hw => by
    rw [hτ]
    exact hs0.chart_inv hb₀ (hdG' (d.u + 0)) hE0 hE0'' (show 0 ≤ w.im from le_of_lt hw)
  rw [aClock_zero, NNReal.coe_zero]
  refine ⟨⟨hu0, hr₂, hE0'', hDt⟩, isSorted_shiftW (hs₀ hord) _, hmω ⟨hωM, hord⟩, fun w hw => ?_,
    fun w hw => ?_, ?_⟩
  · rw [InteractingSLE.fwdMapInv_zero_time hWc' hW0' hw]
    exact hinv w hw
  · rw [InteractingSLE.fwdMapInv_zero_time hWc' hW0' hw,
      show logDerivFwd (fun s : ℝ => W s.toNNReal ω) 0 w = 0 by simp [QuantumZipper.logDerivFwd],
      Complex.zero_im, zero_add, hinv w hw, hs0.chart_lift hE0 hE0'' (τ ω)]
  · obtain ⟨hgL, hgR⟩ := geom_zero_of_isFlowType hWc hW0 (htype ω hωM)
    refine ⟨{0} ∪ ((shiftW (τ ω) (β₀ ω)).jumps : Set ℝ),
      (finite_singleton 0).union (shiftW (τ ω) (β₀ ω)).jumps.finite_toSet, fun y hy => ?_⟩
    have hy0 : y ≠ 0 := fun h => hy (Or.inl h)
    have hyJ : y + 0 ∉ (shiftW (τ ω) (β₀ ω)).jumps := by
      rw [add_zero]; exact fun h => hy (Or.inr h)
    rw [hgL, hgR, forceBoundaryData_zero_of_isFlowType (htype ω hωM) y,
      Exist.forceBoundaryData_flowLine_seed hκ (BoundaryWord.isPiecewiseConstantBoundaryData (shiftW (τ ω) (β₀ ω)))
        0 θ₁ hy0 hyJ, add_zero]

end Line

end InteractingSLE.RLC.AStopSafe
