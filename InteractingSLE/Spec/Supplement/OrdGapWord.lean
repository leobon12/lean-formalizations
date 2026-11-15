/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.OrdGapZone
import InteractingSLE.Spec.Sec7.SideHeightBoxSingle
import InteractingSLE.Spec.Sec7.SideHeightBoxProb
import InteractingSLE.Spec.Sec7.Aux57
import InteractingSLE.Spec.Supplement.RetZoneMean
import InteractingSLE.Spec.Supplement.RetTouchMean
import InteractingSLE.Spec.Sec5.Cond44Ref

/-!
# Theorem 1.5's leaf 3: the mean word at an enclosed pair

Packet PROVE-T15-ORDDET5. At a retained pair `(u, r)` whose first prefix is **enclosed** by the second
(`η₁[0,u] ∩ ℍ ⊆ fill(η₂[0,r])`, the configuration of `OrdGap.subset_fillH_of_inactive_snd`), the active domain is the
unbounded domain of the second path alone, and the conditional mean of the field given both prefixes is the second
path's own coupling mean there (G7, p. 498: "Any portion of the fixed retained hull it surrounds is swallowed with that
same pocket"). This file proves the corresponding mean word:

* `fillH_union_eq_of_subset`, `mem_of_mem_fillH_of_mem_closure` (deterministic fill facts);
* `enclChart_facts` (deterministic): at an enclosed pair the retained chart is the second path's own centred Loewner
  chart (`d.fwd = f_r(· − x₂)` and `d.lift = arg f_r′(· − x₂)` on the active domain);
* **`exists_enclWord`**: a word `β` with the mean identification `IsRetMeanIdentOn` on the enclosed event, sorted and
  with the outer word `IsRetainedWord` there. The word is the force data of the second path's own coupling at `r`
  (minus `θ₂χ`). Proof: Aux. lemma 82 (`RetZone.ae_tendsto_sub_of_side`, every prime end cleared since the transition
  hull is empty) compares the union mean with the second range mean; the range mean is the coupling mean
  (`SideHeight.ae_apply_eq_flowMean_of_range`); in the chart the coupling mean is the bounded harmonic extension of
  the force data, whose boundary values give the word (Aux. lemmas 28–29: `isRetMeanIdentOn_of_chartBoundaryLimitOn`);
  the side heights come from the slit bound (`SideHeightBox.mem_slit_of_tendsto_fwdMap'`).

Uses Lemma 7.5 (`Theorem15.Lemma75Statement`) only; for Theorem 1.5.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Complex Set Metric Filter Topology MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

open QuantumZipper (H Hbar fwdMap fwdMapInv fwdHull logDerivFwd)
open LQGMetric (DistOn TestOn)

universe u

namespace InteractingSLE.RLC.OrdGap

open Supp7 Restart

/-! ### Fill facts -/

/-- **Adding an enclosed compact set does not change the filling.** -/
theorem fillH_union_eq_of_subset {A B : Set ℂ} (hA : IsCompact A) (hB : IsCompact B) (h : A ∩ H ⊆ fillH B) :
    fillH (A ∪ B) = fillH B := by
  refine le_antisymm (fun z hz => ?_) (fillH_mono subset_union_right)
  by_contra hzB
  have hzH : z ∈ H := hz.1
  obtain ⟨R, hR, hBR, hU⟩ := HalfPlaneSep.exists_H_diff_fillH_eq hB.isClosed hB.isBounded
  have hzU : z ∈ H \ fillH B := ⟨hzH, hzB⟩
  have hUpc : IsPreconnected (H \ fillH B) := by rw [hU]; exact isPreconnected_connectedComponentIn
  have hUAB : H \ fillH B ⊆ H \ closure (A ∪ B) := by
    intro y hy
    refine ⟨hy.1, ?_⟩
    rw [(hA.union hB).isClosed.closure_eq]
    rintro (hyA | hyB)
    · exact hy.2 (h ⟨hyA, hy.1⟩)
    · exact hy.2 (mem_fillH_of_mem_closure hy.1 (subset_closure hyB))
  have hsub : H \ fillH B ⊆ connectedComponentIn (H \ closure (A ∪ B)) z :=
    hUpc.subset_connectedComponentIn hzU hUAB
  -- the unbounded domain of `B` is unbounded
  have hUunb : ¬ Bornology.IsBounded (H \ fillH B) := by
    intro hb
    obtain ⟨M, hM⟩ := hb.subset_closedBall 0
    set y : ℂ := ((max R M + 1 : ℝ) : ℂ) * I with hy
    have hyH : y ∈ H := by
      show 0 < (((max R M + 1 : ℝ) : ℂ) * I).im
      simp only [mul_im, ofReal_re, I_im, mul_one, ofReal_im, I_re, mul_zero, add_zero]
      have := le_max_left R M
      linarith
    have hyn : ‖y‖ = max R M + 1 := by
      rw [hy, norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos (by have := le_max_left R M; linarith)]
    have hyU : y ∈ H \ fillH B := by
      rw [hU]
      exact mem_connectedComponentIn_of_le_norm hR hBR hyH (by rw [hyn]; linarith [le_max_left R M])
    have := hM hyU
    rw [mem_closedBall, dist_zero_right, hyn] at this
    linarith [le_max_right R M]
  rcases hz.2 with hzc | hzb
  · exact (hUAB hzU).2 hzc
  · exact hUunb (hzb.subset hsub)

/-- **A point of `ℍ` in the filling of a closed set and adherent to its complement lies on the set.** -/
theorem mem_of_mem_fillH_of_mem_closure {B : Set ℂ} (hB : IsClosed B) {z : ℂ} (hzH : z ∈ H) (h1 : z ∈ fillH B)
    (h2 : z ∈ closure (H \ fillH B)) : z ∈ B := by
  by_contra hzB
  have hO : IsOpen (connectedComponentIn (H \ B) z) := (QuantumZipper.isOpen_H.sdiff hB).connectedComponentIn
  obtain ⟨y, hyC, hyU⟩ := mem_closure_iff.1 h2 _ hO (mem_connectedComponentIn ⟨hzH, hzB⟩)
  have hb : Bornology.IsBounded (connectedComponentIn (H \ B) z) := by
    rcases h1.2 with h | h
    · rw [hB.closure_eq] at h; exact absurd h hzB
    · rwa [hB.closure_eq] at h
  have hyB : y ∈ H \ B := connectedComponentIn_subset _ _ hyC
  refine hyU.2 ⟨hyB.1, Or.inr ?_⟩
  rw [hB.closure_eq, ← connectedComponentIn_eq hyC]
  exact hb

/-! ### The chart at an enclosed pair -/

section Chart

variable {Ω : Type*} [MeasurableSpace Ω]

open MartChar.RealFlow in
/-- **At an enclosed pair the retained chart is the second path's own centred Loewner chart** (deterministic). If the
retained union's filling is the filling of the second prefix `η[0, r]` of a generating trace `η − x` of `W` (with
`r` before the lifetime) and the second tip is the tip `η(r)`, then the retained domain is `ℍ \ fill(η[0, r])`, the
forward chart is `f_r(· − x)` there, and the lift is `arg f_r′(· − x)`. -/
theorem enclChart_facts {d : RetData Ω} (hd : d.IsMeasGood) {ω : Ω} (hE : ω ∈ d.E) {η : ℝ≥0 → ℂ} {x : ℝ}
    {W : ℝ≥0 → ℝ} {ζ : ℝ≥0∞} (hg : IsGeneratingTrace W ζ (fun t => η t - x))
    (hWc : ContinuousOn W {s | (s : ℝ≥0∞) < ζ}) (hW0 : W 0 = 0) (hr : (d.r : ℝ≥0∞) < ζ)
    (hfill : fillH (d.K ω) = fillH (η '' Icc 0 d.r)) (htip : d.η₂ ω d.r = η d.r) :
    d.D ω = H \ fillH (η '' Icc 0 d.r) ∧
      (∀ z ∈ d.D ω, d.fwd ω z = fwdMap (fun s : ℝ => W s.toNNReal) d.r (z - x)) ∧
      ∀ z ∈ d.D ω, d.lift ω z = (logDerivFwd (fun s : ℝ => W s.toNNReal) d.r (z - x)).im := by
  have hD : d.D ω = H \ fillH (η '' Icc 0 d.r) := by
    show H \ fillH (d.K ω) = _
    rw [hfill]
  obtain ⟨κ', hHull, hMap, hLog⟩ := Sec7.ReverseArc.exists_physChart hg hWc hW0 hr
  have hB := hd.isHPHull ω
  have hgeq' : EqOn (ConformalImage.mapOut (fillH (η '' Icc 0 d.r)))
      (fun z => fwdMap (fun s : ℝ => W s.toNNReal) d.r (z - x) + κ') (H \ fillH (η '' Icc 0 d.r)) :=
    (ConformalImage.isMapOut_mapOut hHull).eqOn hHull hMap
  have hgdef : d.g ω = ConformalImage.mapOut (fillH (η '' Icc 0 d.r)) := by
    show ConformalImage.mapOut (fillH (d.K ω)) = _
    rw [hfill]
  have hgeq : EqOn (d.g ω) (fun z => fwdMap (fun s : ℝ => W s.toNNReal) d.r (z - x) + κ')
      (H \ fillH (η '' Icc 0 d.r)) := by
    rw [hgdef]; exact hgeq'
  -- the forward limit at the tip is `κ'`
  set w' : ℝ → ℝ := fun s => W s.toNNReal with hw'
  have hrr : (0 : ℝ) ≤ d.r := d.r.coe_nonneg
  obtain ⟨t₂, hrt₂, ht₂ζ⟩ := exists_real_btwn_of_lt hr
  have ht₂ : 0 ≤ t₂ := hrr.trans hrt₂.le
  have hWf : Continuous (frozenDrive W t₂) := continuous_frozenDrive_of_lt hWc ht₂ζ
  have hWf0 : frozenDrive W t₂ 0 = 0 := by rw [frozenDrive_zero ht₂, hW0]
  have heqW : ∀ s ∈ Icc (0 : ℝ) d.r, w' s = frozenDrive W t₂ s := fun s hs =>
    (frozenDrive_eq ⟨hs.1, hs.2.trans hrt₂.le⟩).symm
  have hfwdeq : fwdMap w' d.r = fwdMap (frozenDrive W t₂) d.r :=
    funext fun z => fwdMap_eq_of_eqOn hrr heqW
  have hinveq : fwdMapInv w' d.r = fwdMapInv (frozenDrive W t₂) d.r :=
    fwdMapInv_eq_of_eqOn hrr hrt₂ fun s hs => (frozenDrive_eq hs).symm
  have hhulleq : fwdHull w' d.r = fwdHull (frozenDrive W t₂) d.r :=
    fwdHull_eq_of_eqOn hrr hrt₂ fun s hs => (frozenDrive_eq hs).symm
  have hhull : (fun z : ℂ => z + x) '' fwdHull w' d.r = fillH (η '' Icc 0 d.r) := by
    rw [Sec7.SideHeight.fwdHull_eq_fillH_of_isGeneratingTrace hg hr, ← Restart.fillH_image_add_real,
      Restart.image_add_real_eq]
  set zy : ℝ → ℂ := fun y => (x : ℂ) + fwdMapInv w' d.r (y * I) with hzy
  have hzyD : ∀ y : ℝ, 0 < y → zy y ∈ d.D ω := by
    intro y hy
    have hyH : (y : ℂ) * I ∈ H := by
      show 0 < ((y : ℂ) * I).im
      simpa using hy
    have h1 := QuantumZipper.RS.fwdMapInv_mem_compl_fwdHull hWf hWf0 hrr hyH
    rw [← hinveq, ← hhulleq] at h1
    rw [hD, ← hhull]
    refine ⟨show 0 < (zy y).im by simpa [hzy] using (show 0 < (fwdMapInv w' d.r (y * I)).im from h1.1),
      fun h => h1.2 ?_⟩
    obtain ⟨z, hz, hze⟩ := h
    have : z = fwdMapInv w' d.r (y * I) := by
      have := congrArg (fun c => c - (x : ℂ)) hze
      simp only [add_sub_cancel_right, hzy, add_sub_cancel_left] at this
      exact this
    rw [← this]; exact hz
  have hzylim : Tendsto zy (𝓝[>] 0) (𝓝[d.D ω] (d.p ω)) := by
    refine tendsto_nhdsWithin_iff.2 ⟨?_, eventually_nhdsWithin_of_forall fun y hy => hzyD y hy⟩
    rw [RetData.p_of_mem hE, htip]
    have h1 := hg.tendsto_fwdMapInv_mul_I hWc hW0 hr
    have h2 := h1.const_add (x : ℂ)
    simpa only [hzy, add_sub_cancel] using h2
  have hgzy : ∀ y : ℝ, 0 < y → d.g ω (zy y) = (y : ℂ) * I + κ' := by
    intro y hy
    have hyH : (y : ℂ) * I ∈ H := by
      show 0 < ((y : ℂ) * I).im
      simpa using hy
    rw [hD] at hzyD
    rw [hgeq (hzyD y hy)]
    simp only [hzy, add_sub_cancel_left]
    rw [hfwdeq, hinveq, QuantumZipper.RS.fwdMap_fwdMapInv hWf hWf0 hrr hyH]
  have hlim1 : Tendsto (fun y => d.g ω (zy y)) (𝓝[>] 0) (𝓝 (d.shift ω)) := (hd.tendsto_shift ω).comp hzylim
  have hlim2 : Tendsto (fun y => d.g ω (zy y)) (𝓝[>] 0) (𝓝 κ') := by
    have h0 : Tendsto (fun y : ℝ => (y : ℂ) * I + κ') (𝓝[>] 0) (𝓝 ((0 : ℝ) * I + κ')) :=
      ((Continuous.tendsto (by fun_prop) 0).mono_left nhdsWithin_le_nhds)
    rw [ofReal_zero, zero_mul, zero_add] at h0
    refine h0.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with y hy
    exact (hgzy y hy).symm
  have hshift : d.shift ω = κ' := tendsto_nhds_unique hlim1 hlim2
  refine ⟨hD, fun z hz => ?_, fun z hz => ?_⟩
  · show d.g ω z - d.shift ω = _
    rw [hshift, hgeq (hD ▸ hz), add_sub_cancel_right]
  · have hL1 := isCanonicalDerivLog_canonDerivLog hHull
    have hL2 := hL1.congr hHull hgeq'
    have he := IsCanonicalDerivLog.eqOn hL2 hLog hHull hMap (hD ▸ hz)
    show (canonDerivLog (fillH (d.K ω)) z).im = _
    rw [hfill, he]

end Chart

/-! ### The mean word at an enclosed pair -/

/-- **The enclosed event** of retained data `d` for two paths: both cutoffs before the lifetimes, the retained chart
event, and the first prefix enclosed by the second (`η₁[0, u] ∩ ℍ ⊆ fill(η₂[0, r])`). -/
def enclSet {Ω : Type*} (η₁ η₂ : Ω → ℝ≥0 → ℂ) (ζ₁ ζ₂ : Ω → ℝ≥0∞) (d : RetData Ω) : Set Ω :=
  {ω | (d.u : ℝ≥0∞) < ζ₁ ω ∧ (d.r : ℝ≥0∞) < ζ₂ ω ∧ ω ∈ d.E ∧
    η₁ ω '' Icc 0 d.u ∩ H ⊆ fillH (η₂ ω '' Icc 0 d.r)}

section Word

variable {κ : ℝ} {b : ℝ → ℝ} {jumps : Finset ℝ} {x₁ x₂ θ₁ θ₂ : ℝ} {Ω : Type u} [mΩ : MeasurableSpace Ω]
  {P : Measure Ω} [IsProbabilityMeasure P] {h : Ω → DistOn upperHalfPlaneOpens} {η₁ η₂ : Ω → ℝ≥0 → ℂ}
  {ζ₁ ζ₂ : Ω → ℝ≥0∞}

open Sec7 Sec7.SideHeight Sec7.SideHeightBox Sec7.Lemma76F LocalSets Sec6 MartChar.RealFlow in
/-- **The mean word at an enclosed pair** (see the module docstring): a word with the mean identification on the
enclosed event, sorted and with the outer word there (the first-path clause is vacuous: the chart never lands on the
enclosed first prefix off the second). -/
theorem exists_enclWord (hL75 : Theorem15.Lemma75Statement.{u}) (hκ : 0 < κ) (hκ4 : κ < 4)
    (hb : IsPiecewiseConstantBoundaryData b jumps) (hh : IsGFFWithBoundaryData P h b jumps)
    (hη₁ : IsFlowLine κ b jumps x₁ θ₁ P h η₁ ζ₁) (hη₂ : IsFlowLine κ b jumps x₂ θ₂ P h η₂ ζ₂)
    {u₀ : ℂ → ℝ} (hu₀ : IsBoundedHarmonicExtension b jumps u₀) {d : RetData Ω} (hd : d.IsMeasGood)
    (hag : ∀ᵐ ω ∂P, (d.u : ℝ≥0∞) < ζ₁ ω → (d.r : ℝ≥0∞) < ζ₂ ω → ω ∈ d.G ∧
      (∀ s ≤ d.u, d.η₁ ω s = η₁ ω s) ∧ ∀ t ≤ d.r, d.η₂ ω t = η₂ ω t) :
    ∃ β : Ω → BoundaryWord, IsRetMeanIdentOn κ P h η₁ η₂ ζ₁ ζ₂ u₀ hd (enclSet η₁ η₂ ζ₁ ζ₂ d) β ∧
      ∀ᵐ ω ∂P, ω ∈ enclSet η₁ η₂ ζ₁ ζ₂ d → (β ω).IsSorted ∧
        IsRetainedWord κ θ₁ θ₂ (η₁ ω) d.u (η₂ ω) d.r (d.inv ω) (β ω) := by
  classical
  obtain ⟨h', 𝓕, W', VL, VR, B, htrans, hC, htr'⟩ := id hη₂
  set χ := QuantumZipper.chiC κ with hχ
  set ρL := flowLineRhoL κ b jumps x₂ θ₂ with hρL
  set ρR := flowLineRhoR κ b jumps x₂ θ₂ with hρR
  set vL : Ω → Fin (flowLineNL b jumps x₂) → ℝ := fun ω i => VL i d.r ω - W' d.r ω with hvL
  set vR : Ω → Fin (flowLineNR b jumps x₂) → ℝ := fun ω j => VR j d.r ω - W' d.r ω with hvR
  have hex : ∀ ω, ∃ c : BoundaryWord, StrictMonoOn c.2.1 (Iio c.1) ∧
      c.jumps = Sec5.Cond44Ref.forceJumpFinset (vL ω) (vR ω) ∧
      ∀ y ∉ Sec5.Cond44Ref.forceJumpFinset (vL ω) (vR ω),
        c.fn y = forceBoundaryData κ ρL ρR (vL ω) (vR ω) y + -(θ₂ * χ) := fun ω =>
    Restart.BoundaryWord.exists_fn_eq_strictMonoOn
      (Sec5.Cond44Ref.isPiecewiseConstant_forceData κ ρL ρR (vL ω) (vR ω) (-(θ₂ * χ)))
  choose β hβs hβJ hβf using hex
  have hsorted : ∀ ω, (β ω).IsSorted := fun ω i j hij hj =>
    (hβs ω).monotoneOn (show i < (β ω).1 from lt_of_le_of_lt hij hj) (show j < (β ω).1 from hj) hij
  have hJS : ∀ ω y, y ∉ ((β ω).jumps : Set ℝ) → y ∉ forceJumpSet (vL ω) (vR ω) := by
    intro ω y hy
    rw [hβJ ω, Sec5.Cond44Ref.coe_forceJumpFinset] at hy
    exact hy
  have hh0 := isZeroBoundaryGFF_centredField_of_isGFFWithBoundaryData hh hu₀
  -- the pathwise chart facts at an enclosed pair
  have hchart : ∀ᵐ ω ∂P, ω ∈ enclSet η₁ η₂ ζ₁ ζ₂ d →
      IsCompact (η₂ ω '' Icc 0 d.r) ∧ d.D ω = H \ fillH (η₂ ω '' Icc 0 d.r) ∧
      (∀ z ∈ d.D ω, d.fwd ω z = fwdMap (fun s : ℝ => W' s.toNNReal ω) d.r (z - x₂)) ∧
      (∀ z ∈ d.D ω, d.lift ω z = (logDerivFwd (fun s : ℝ => W' s.toNNReal ω) d.r (z - x₂)).im) ∧
      BijOn (d.inv ω) H (d.D ω) ∧ (∀ w ∈ H, d.fwd ω (d.inv ω w) = w) ∧ d.inv ω 0 = η₂ ω d.r ∧
      fillH (prefixSet (η₂ ω) d.r (η₁ ω) d.u) = fillH (η₂ ω '' Icc 0 d.r) ∧
      activeDomain (η₂ ω) d.r (η₁ ω) d.u = d.D ω ∧
      (fun z : ℂ => z + x₂) '' fwdHull (fun s : ℝ => W' s.toNNReal ω) d.r = fillH (η₂ ω '' Icc 0 d.r) := by
    filter_upwards [hag, htr', hC.1.2.2.2.2] with ω hagω htrω hp hO
    obtain ⟨hu, hr, hE, hencl⟩ := hO
    obtain ⟨hG, a₁, a₂⟩ := hagω hu hr
    have hgood := hd.good ω hG
    have i₁ : d.η₁ ω '' Icc 0 d.u = η₁ ω '' Icc 0 d.u := image_congr fun s hs => a₁ s hs.2
    have i₂ : d.η₂ ω '' Icc 0 d.r = η₂ ω '' Icc 0 d.r := image_congr fun t ht => a₂ t ht.2
    have hA₁c : IsCompact (η₁ ω '' Icc 0 d.u) := by
      rw [← i₁]; exact isCompact_Icc.image_of_continuousOn hgood.1
    have hA₂c : IsCompact (η₂ ω '' Icc 0 d.r) := by
      rw [← i₂]; exact isCompact_Icc.image_of_continuousOn hgood.2.1
    have hfillU : fillH (η₁ ω '' Icc 0 d.u ∪ η₂ ω '' Icc 0 d.r) = fillH (η₂ ω '' Icc 0 d.r) :=
      fillH_union_eq_of_subset hA₁c hA₂c hencl
    have hfill : fillH (d.K ω) = fillH (η₂ ω '' Icc 0 d.r) := by
      rw [RetData.K_of_mem hE]
      show fillH (d.η₁ ω '' Icc 0 d.u ∪ d.η₂ ω '' Icc 0 d.r) = _
      rw [i₁, i₂, hfillU]
    obtain ⟨hD, hfwd, hlift⟩ := enclChart_facts hd hE htrω hp.2.2.2.1 hp.1 hr hfill (a₂ d.r le_rfl)
    have h0₂ : (d.η₂ ω 0).im = 0 := hgood.2.2.2.2.2.1
    have hCR := (hd.isRetChart hE).2
    have hDa : d.D ω = activeDomain (d.η₁ ω) d.u (d.η₂ ω) d.r := hd.D_of_mem hE
    refine ⟨hA₂c, hD, hfwd, hlift, by rw [hDa]; exact hCR.bijOn h0₂, hCR.fwd_inv,
      by rw [hCR.inv_zero h0₂, a₂ d.r le_rfl], ?_, ?_, ?_⟩
    · show fillH (η₂ ω '' Icc 0 d.r ∪ η₁ ω '' Icc 0 d.u) = _
      rw [union_comm, hfillU]
    · rw [activeDomain_comm, hDa]
      exact activeDomain_congr_Icc (fun s hs => (a₁ s hs.2).symm) fun t ht => (a₂ t ht.2).symm
    · rw [fwdHull_eq_fillH_of_isGeneratingTrace htrω hr, ← Restart.fillH_image_add_real,
        Restart.image_add_real_eq]
  refine ⟨β, isRetMeanIdentOn_of_chartBoundaryLimitOn hL75 hκ hκ4 hb hh hη₁ hη₂ hd hag hu₀
    (Eventually.of_forall fun ω hω => ⟨hω.1, hω.2.1, hω.2.2.1⟩) (Eventually.of_forall fun ω _ => hsorted ω) ?_,
    ?_⟩
  · intro ηc₁ ηc₂ g hc₁ hc₂ hm₁ hm₂ hag₁ hag₂ hg
    set m := capR d.u d.r with hm
    have hum : d.u < m := lt_capR_left d.u d.r
    have hrm : d.r < m := lt_capR_right d.u d.r
    have hF₂ := range_facts hL75 WholeField.retainedRangeEntranceStatement hκ hκ4 hb hh hη₂ hu₀ m d.r hc₂ hm₂ hag₂
    obtain ⟨G₂, hG₂⟩ := IsLocalSet.exists_isLocalSetMean hh0 hF₂.1 hF₂.2.1
    have hcomm : cstUnion ηc₂ ηc₁ d.r d.u = cstUnion ηc₁ ηc₂ d.u d.r := by
      funext ω; rw [cstUnion_eq, cstUnion_eq, union_comm]
    have hg' : IsLocalSetMean (cstUnion ηc₂ ηc₁ d.r d.u) (WholeField.centredField h u₀) P g := by
      rw [hcomm]; exact hg
    have hW : ∀ᵐ ω ∂P, IsGeneratingTrace (fun t => W' t ω) (ζ₂ ω) (fun t => η₂ ω t - x₂) ∧
        ContinuousOn (fun t => W' t ω) {s | (s : ℝ≥0∞) < ζ₂ ω} ∧ W' 0 ω = 0 := by
      filter_upwards [htr', hC.1.2.2.2.2] with ω h1 hp
      exact ⟨h1, hp.2.2.2.1, hp.1⟩
    have hA82 := RetZone.ae_tendsto_sub_of_side hL75 hκ hκ4 hb hh hη₂ hη₁ hu₀ hrm hum hW hc₂ hc₁ hm₂ hm₁ hag₂
      hag₁ hg' hG₂
    -- the second range is the stopped range, and it contains the earlier hulls in its filling
    set A₂ : Ω → Set ℂ := fun ω => ηc₂ ω '' {t : ℝ≥0 | (t : ℝ≥0∞) ≤ d.r} ∩ H with hA₂_def
    have hA₂b : ∀ ω, Bornology.IsBounded (A₂ ω) := fun ω =>
      (((isCompact_Icc (a := (0 : ℝ≥0)) (b := d.r)).image (hc₂ ω)).isBounded).subset (inter_subset_left.trans (by
        intro z hz
        obtain ⟨t, ht, rfl⟩ := hz
        exact ⟨t, ⟨zero_le, show t ≤ d.r from by exact_mod_cast ht⟩, rfl⟩))
    have hA₂q : ∀ᵐ ω ∂P, (d.r : ℝ≥0∞) < ζ₂ ω → A₂ ω = η₂ ω '' Icc 0 d.r ∩ H := by
      filter_upwards [hag₂] with ω hce hq
      show ηc₂ ω '' {t : ℝ≥0 | (t : ℝ≥0∞) ≤ d.r} ∩ H = η₂ ω '' Icc 0 d.r ∩ H
      congr 1
      ext z
      constructor
      · rintro ⟨t, ht, rfl⟩
        have htq : t ≤ d.r := by exact_mod_cast ht
        refine ⟨t, ⟨zero_le, htq⟩, ?_⟩
        rw [hce t, Restart.capTime_of_le m (ζ₂ ω) (le_min (ht.trans hq.le)
          (ENNReal.coe_le_coe.2 (htq.trans hrm.le)))]
      · rintro ⟨t, ht, rfl⟩
        refine ⟨t, by exact_mod_cast ht.2, ?_⟩
        rw [hce t, Restart.capTime_of_le m (ζ₂ ω)
          (le_min ((ENNReal.coe_le_coe.2 ht.2).trans hq.le) (ENNReal.coe_le_coe.2 (ht.2.trans hrm.le)))]
    have hA₂fill : ∀ᵐ ω ∂P, ∀ t : ℝ≥0, t ≤ d.r → (t : ℝ≥0∞) < ζ₂ ω →
        (fun z : ℂ => z + x₂) '' fwdHull (fun s : ℝ => W' s.toNNReal ω) t ⊆ fillH (A₂ ω) := by
      filter_upwards [htr', hag₂] with ω htrω hce t htq htζ
      rw [fwdHull_eq_fillH_of_isGeneratingTrace htrω htζ, ← Restart.fillH_image_add_real,
        Restart.image_add_real_eq, hA₂_def, fillH_inter_H]
      refine fillH_mono ?_
      rintro _ ⟨s, hs, rfl⟩
      refine ⟨s, show (s : ℝ≥0∞) ≤ d.r from ENNReal.coe_le_coe.2 (hs.2.trans htq), ?_⟩
      rw [hce s, Restart.capTime_of_le m (ζ₂ ω)
        (le_min ((ENNReal.coe_le_coe.2 hs.2).trans htζ.le) (ENNReal.coe_le_coe.2 ((hs.2.trans htq).trans hrm.le)))]
    -- the force data of the second path at `r` and the range mean as the coupling mean
    obtain ⟨u₀', hu₀'⟩ := Sec4.exists_isBoundedHarmonicExtension_forceBoundaryData κ ρL ρR (flowLineXL b jumps x₂)
      (flowLineXR b jumps x₂)
    have hrel := Exist.eqOn_flowLine_harmonicExtension hκ hb x₂ θ₂ hu₀ hu₀'
    obtain ⟨hX, -⟩ := hC.2.2.2
    choose uF huF using fun ω => Sec4.exists_isBoundedHarmonicExtension_forceBoundaryData κ ρL ρR (vL ω) (vR ω)
    have hmain := ae_apply_eq_flowMean_of_range hC hκ htrans hh0 hu₀.1 hu₀' hrel hX htr' hF₂.1
      (fun ω => inter_subset_right) hA₂b hF₂.2.1 hF₂.2.2.1 hA₂q hA₂fill hG₂ huF
    filter_upwards [hA82, hmain, hchart, hC.1.2.2.2.2, hA₂q, hA₂fill, hG₂.2.1] with ω hA82ω hmω hchω hp hA₂qω
      hfillω hR₂ω hO v hv hvrep
    obtain ⟨hu, hr, hE, hencl⟩ := hO
    obtain ⟨-, hD, hfwd, hlift, hψbij, hfi, -, hF7, hF8, -⟩ := hchω ⟨hu, hr, hE, hencl⟩
    obtain ⟨vA, hvA, hvAr⟩ := hR₂ω
    -- `vA + 𝔥₀` is the coupling mean on the domain
    set U := H \ fillH (A₂ ω) with hU
    have hUD : U = d.D ω := by rw [hU, hA₂qω hr, fillH_inter_H, hD]
    have hUo : IsOpen U := isOpen_H_diff_fillH (hA₂b ω)
    have hUA : U ⊆ H \ A₂ ω := fun z hz => ⟨hz.1, fun h => hz.2 (subset_fillH inter_subset_right h)⟩
    set M : ℂ → ℝ := fun z =>
      couplingMean κ (fun s : ℝ => W' s.toNNReal ω) d.r (uF ω) (z - x₂) - θ₂ * χ - u₀ z with hM
    have hKU : U ⊆ H \ (fun z : ℂ => z + x₂) '' fwdHull (fun s : ℝ => W' s.toNNReal ω) d.r := fun z hz =>
      ⟨hz.1, fun h => hz.2 (hfillω d.r le_rfl hr h)⟩
    have hMh : InnerProductSpace.HarmonicOnNhd M U :=
      (harmonicOnNhd_flowMean hp.2.2.2.1 hr (huF ω).1 x₂ (θ₂ * χ) hu₀.1).mono hKU
    have hvM : EqOn vA M U := eqOn_of_integral_mul_eq hUo (hUA.trans sdiff_subset) (hvA.mono hUA) hMh
      fun φ hφ => by rw [← hvAr φ (hφ.trans hUA), hmω hr φ hφ]
    refine ⟨(β ω).jumps, (β ω).jumps.finite_toSet, fun w hw => ?_⟩
    have hψD : ∀ z ∈ H, d.inv ω z ∈ d.D ω := fun z hz => hψbij.mapsTo hz
    have hphys : ∀ z ∈ H, fwdMap (fun s : ℝ => W' s.toNNReal ω) d.r (d.inv ω z - x₂) = z := fun z hz => by
      rw [← hfwd _ (hψD z hz), hfi z hz]
    -- Aux. lemma 82 with every prime end cleared
    have hv' : InnerProductSpace.HarmonicOnNhd v (H \ cstUnion ηc₂ ηc₁ d.r d.u ω) := by rw [hcomm]; exact hv
    have hvrep' : ∀ φ : TestOn upperHalfPlaneOpens, tsupport φ ⊆ H \ cstUnion ηc₂ ηc₁ d.r d.u ω →
        g ω φ = ∫ z, v z * φ z := by rw [hcomm]; exact hvrep
    have hFle : map (d.inv ω) (𝓝[H] (w : ℂ)) ≤ 𝓟 (activeDomain (η₂ ω) d.r (η₁ ω) d.u) := by
      rw [hF8]; exact le_principal_iff.2 (mem_map.2 (mem_of_superset self_mem_nhdsWithin hψD))
    have hFphys : Tendsto (Lemma76G.physF (fun t => W' t ω) d.r x₂) (map (d.inv ω) (𝓝[H] (w : ℂ)))
        (𝓝 (w : ℂ)) := by
      rw [tendsto_map'_iff]
      refine (tendsto_id.mono_left nhdsWithin_le_nhds).congr' ?_
      filter_upwards [self_mem_nhdsWithin] with z hz
      exact (hphys z hz).symm
    have hdisj : Disjoint (ball ((w : ℝ) : ℂ) 1) (Lemma76G.physF (fun t => W' t ω) d.r x₂ ''
        (fillH (prefixSet (η₂ ω) d.r (η₁ ω) d.u) \ fillH (η₂ ω '' Icc 0 d.r))) := by
      rw [hF7, sdiff_self, image_empty]; exact disjoint_empty _
    have h1 := tendsto_map'_iff.1 (hA82ω hr hu v vA hv' hvrep' hvA hvAr w 1 one_pos hdisj _ hFle hFphys)
    have h2 := (huF ω).2.2 w (hJS ω w hw)
    have hlim := (h1.add h2).sub_const (θ₂ * χ)
    have hwJ' : w ∉ Sec5.Cond44Ref.forceJumpFinset (vL ω) (vR ω) := fun hwJ =>
      hw (by rw [hβJ ω]; exact Finset.mem_coe.2 hwJ)
    have hval : (β ω).fn w = 0 + forceBoundaryData κ ρL ρR (vL ω) (vR ω) w - θ₂ * χ := by
      rw [hβf ω w hwJ']; ring
    rw [← hval] at hlim
    refine hlim.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with z hz
    have hzD := hψD z hz
    have hzU : d.inv ω z ∈ U := hUD ▸ hzD
    simp only [Function.comp_apply]
    rw [hvM hzU, hlift _ hzD, hM]
    simp only [couplingMean]
    rw [hphys z hz]
    ring
  · filter_upwards [hchart, htr', hC.1.2.2.2.2] with ω hchω htrω hp hO
    refine ⟨hsorted ω, ?_⟩
    obtain ⟨hu, hr, hE, hencl⟩ := hO
    obtain ⟨hA₂c, hD, hfwd, -, hψbij, hfi, hψ0, -, -, hhull⟩ := hchω ⟨hu, hr, hE, hencl⟩
    intro y hyH hytip₂ hytip₁ hycom
    -- the first-prefix clause is vacuous
    have hcl : d.inv ω y ∈ closure (d.D ω) := (Lemma76G.RetData.IsMeasGood.tendsto_inv_real hd hE y).2
    have hA₁A₂ : d.inv ω y ∈ η₁ ω '' Icc 0 d.u → d.inv ω y ∈ η₂ ω '' Icc 0 d.r := fun h =>
      mem_of_mem_fillH_of_mem_closure hA₂c.isClosed hyH (hencl ⟨h, hyH⟩) (hD ▸ hcl)
    have hy0 : y ≠ 0 := by
      rintro rfl
      exact hytip₂ (by rw [ofReal_zero]; exact hψ0)
    -- the slit bound at an interior point of the second prefix
    have hψD : ∀ z ∈ H, d.inv ω z ∈ d.D ω := fun z hz => hψbij.mapsTo hz
    set F' : Filter ℂ := map (fun z => z - x₂) (map (d.inv ω) (𝓝[H] (y : ℂ))) with hF'
    have : F'.NeBot := ((Lemma76G.neBot_nhdsWithin_H y).map _).map _
    have hF'le : F' ≤ 𝓝[H \ fwdHull (fun s : ℝ => W' s.toNNReal ω) d.r] (d.inv ω y - x₂) := by
      refine tendsto_nhdsWithin_iff.2 ⟨((continuous_sub_right (x₂ : ℂ)).tendsto _).comp
        ((Lemma76G.RetData.IsMeasGood.tendsto_inv_real hd hE y).1.trans nhdsWithin_le_nhds), ?_⟩
      rw [eventually_map]
      filter_upwards [(Lemma76G.RetData.IsMeasGood.tendsto_inv_real hd hE y).1 self_mem_nhdsWithin] with z hz
      rw [hD] at hz
      refine ⟨show 0 < (d.inv ω z - x₂).im by simpa using (show 0 < (d.inv ω z).im from hz.1),
        fun hK => hz.2 ?_⟩
      rw [← hhull]
      exact ⟨d.inv ω z - x₂, hK, by ring⟩
    have hy' : Tendsto (fwdMap (fun s : ℝ => W' s.toNNReal ω) d.r) F' (𝓝 (y : ℂ)) := by
      rw [hF', tendsto_map'_iff, tendsto_map'_iff]
      refine (tendsto_id.mono_left nhdsWithin_le_nhds).congr' ?_
      filter_upwards [self_mem_nhdsWithin] with z hz
      simp only [Function.comp_apply, id]
      rw [← hfwd _ (hψD z hz), hfi z hz]
    have hpy : ¬ ((d.inv ω y - x₂).im = 0 ∧ (d.inv ω y - x₂).re ≤ 0) := fun h => by
      have : (d.inv ω y - x₂).im = (d.inv ω y).im := by simp
      rw [this] at h
      exact (ne_of_gt (show 0 < (d.inv ω y).im from hyH)) h.1
    have hpy' : ¬ ((d.inv ω y - x₂).im = 0 ∧ 0 ≤ (d.inv ω y - x₂).re) := fun h => hpy ⟨h.1, by
      have : (d.inv ω y - x₂).im = (d.inv ω y).im := by simp
      rw [this] at h
      exact absurd h.1 (ne_of_gt (show 0 < (d.inv ω y).im from hyH))⟩
    have hslit := mem_slit_of_tendsto_fwdMap' hp htrω hr hF'le hy'
    have hL : ∀ i, vL ω i < y := hslit.1 hpy
    have hR : ∀ i, y < vR ω i := hslit.2 hpy'
    have hyS : y ∉ forceJumpSet (vL ω) (vR ω) := by
      intro hmem
      simp only [forceJumpSet, mem_insert_iff, mem_union, mem_range] at hmem
      rcases hmem with h0 | ⟨i, hi⟩ | ⟨i, hi⟩
      · exact hy0 h0
      · exact (hL i).ne hi
      · exact (hR i).ne' hi
    have hyJ : y ∉ (β ω).jumps := by
      intro h
      apply hyS
      rw [← Sec5.Cond44Ref.coe_forceJumpFinset, ← hβJ ω]
      exact h
    have hyJ' : y ∉ Sec5.Cond44Ref.forceJumpFinset (vL ω) (vR ω) := by rw [← hβJ ω]; exact hyJ
    refine ⟨hy0, hyJ, fun _ => ⟨fun hyneg => ?_, fun hypos => ?_⟩, fun h => absurd ⟨h, hA₁A₂ h⟩ hycom⟩
    · rw [hβf ω y hyJ']
      have hdata : forceBoundaryData κ ρL ρR (vL ω) (vR ω) y = -sleLambda κ := by
        simp only [forceBoundaryData, hyneg, ↓reduceIte]
        rw [Finset.filter_false_of_mem fun i _ => not_lt.2 (hL i).le, Finset.sum_empty, add_zero, mul_one,
          sleLambda]
      rw [hdata]; ring
    · rw [hβf ω y hyJ']
      have hdata : forceBoundaryData κ ρL ρR (vL ω) (vR ω) y = sleLambda κ := by
        simp only [forceBoundaryData, show ¬ y < 0 from not_lt.2 hypos.le, ↓reduceIte]
        rw [Finset.filter_false_of_mem fun i _ => not_le.2 (hR i), Finset.sum_empty, add_zero, mul_one, sleLambda]
      rw [hdata]; ring

end Word

end InteractingSLE.RLC.OrdGap
