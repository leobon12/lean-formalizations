/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.AStopProcSnd
import InteractingSLE.Spec.Supplement.OrdFstSlit

/-!
# The A-stopped first continuation: chart path, good samples, physical filtration and observations

Packet PROVE-T15-ASTOP-PROC. The first continuation after `d.u`, stopped at its first new contact with the retained
union `A = d.η₂[0, d.r] ∪ η[0, d.u]` only, in the chart of `d` recentred at a seed `τ ω` (in the application the first
tip's chart point `tipPos`, read from the stop line as `(β ω).2`):

* `fstSet`, `fstLifeP`, `fstChart`;
* **`isAGood_fst`**: good samples (`Supp7.isRetCont_fst`, the seed identified with `tipPos` as in
  `OrdDet.exists_ordContFst_facts`);
* `fstPhysFiltration` (the completed retained histories at the lines `(u + t, r)`), **`measurableSet_fstSurv`**,
  **`fstObs`**: the first continuation's processes are observed in it (`AObs`).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Filter Topology MeasureTheory
open scoped NNReal ENNReal

namespace InteractingSLE.RLC.AStopProc

open Restart Restart.RetAux79 Supp7 Sec7 Sec7.Lemma76F LocalSets
open QuantumZipper (H)

section Defs

variable {Ω : Type*}

/-- **The retained union of the first continuation**, with the continuation path `η` on the first prefix. -/
def fstSet (d : RetData Ω) (η : Ω → ℝ≥0 → ℂ) (ω : Ω) : Set ℂ := d.η₂ ω '' Icc 0 d.r ∪ η ω '' Icc 0 d.u

/-- **The physical lifetime of the A-stopped first continuation** (relative to `d.u`). -/
def fstLifeP (d : RetData Ω) (η : Ω → ℝ≥0 → ℂ) (ζ : Ω → ℝ≥0∞) (ω : Ω) : ℝ≥0∞ :=
  contLife (η ω) (ζ ω) d.u (fstSet d η ω)

/-- **The chart path of the A-stopped first continuation** in physical time, in the chart of `d` recentred at `τ`. -/
def fstChart (d : RetData Ω) (τ : Ω → ℝ) (η : Ω → ℝ≥0 → ℂ) (ζ : Ω → ℝ≥0∞) (ω : Ω) : ℝ≥0 → ℂ :=
  contPath (d.D ω) (fun z => d.fwd ω z - τ ω) (η ω) d.u (fstLifeP d η ζ ω)

end Defs

section Pathwise

variable {Ω : Type*} [MeasurableSpace Ω]

/-- **The first continuation at a chart sample of `d` is a retained continuation** in the chart recentred at `tipPos`
(`Supp7.isRetCont_fst`; the proof of `OrdDet.exists_ordContFst_facts`). -/
theorem isRetCont_fstData {d : RetData Ω} (hd : d.IsMeasGood) {ω : Ω} (hω : ω ∈ d.E) {η : ℝ≥0 → ℂ}
    {ζ : ℝ≥0∞} {x : ℝ} (hp : IsPathGood η ζ x) (hα : ∀ s ≤ d.u, d.η₁ ω s = η s) (huζ : (d.u : ℝ≥0∞) < ζ)
    (hpH : d.η₁ ω d.u ∈ H) (hpO : d.η₁ ω d.u ∉ d.η₂ ω '' Icc 0 d.r)
    (hcl : d.η₁ ω d.u ∈ closure (activeDomain (d.η₁ ω) d.u (d.η₂ ω) d.r))
    (hne₁ : ∀ s < d.u, d.η₁ ω s ≠ d.η₁ ω d.u) :
    IsRetCont η ζ x d.u (d.η₂ ω '' Icc 0 d.r) (fun z => d.fwd ω z - tipPos d d.η₁ ω)
        (fun w => d.inv ω (w + tipPos d d.η₁ ω)) ∧
      d.D ω = H \ fillH (d.η₂ ω '' Icc 0 d.r ∪ η '' Icc 0 d.u) := by
  have hg := hd.good ω (RetData.E_subset_G hω)
  obtain ⟨⟨x₀, hx₀⟩, hC⟩ := hd.isRetChart hω
  have hφ : ∃ x₀ : ℝ, ∀ z, d.fwd ω z =
      ConformalImage.mapOut (fillH (prefixSet (d.η₁ ω) d.u (d.η₂ ω) d.r)) z - x₀ :=
    ⟨x₀, fun z => by
      show d.g ω z - d.shift ω = _
      rw [hx₀, RetData.g, RetData.K_of_mem hω]⟩
  obtain ⟨w₁, hw₁, hR⟩ := isRetCont_fst hg hC hφ hp hα huζ hpH hpO hcl hne₁
  have hDω : d.D ω = activeDomain (d.η₁ ω) d.u (d.η₂ ω) d.r := hd.D_of_mem hω
  have htp : tipPos d d.η₁ ω = w₁ := by
    have hNe : (𝓝[d.D ω] (d.η₁ ω d.u)).NeBot := by
      rw [hDω]; exact mem_closure_iff_nhdsWithin_neBot.1 hcl
    show (limUnder (𝓝[d.D ω] (d.η₁ ω d.u)) (d.fwd ω)).re = w₁
    rw [hDω] at hNe ⊢
    rw [hw₁.limUnder_eq, Complex.ofReal_re]
  have hKc : IsClosed (prefixSet (d.η₁ ω) d.u (d.η₂ ω) d.r) := (isCompact_prefixSet' hg.1 hg.2.1).isClosed
  have hK : d.η₂ ω '' Icc 0 d.r ∪ η '' Icc 0 d.u = η '' Icc 0 d.u ∪ d.η₂ ω '' Icc 0 d.r := union_comm _ _
  have hD : H \ fillH (d.η₂ ω '' Icc 0 d.r ∪ η '' Icc 0 d.u) = d.D ω := by
    rw [hDω, activeDomain_eq hKc, prefixSet, image_congr fun s hs => hα s hs.2, hK]
  rw [htp]
  exact ⟨hR, hD.symm⟩

/-- **Good samples of the A-stopped first continuation** (seed `τ ω = tipPos`). -/
theorem isAGood_fst {d : RetData Ω} (hd : d.IsMeasGood) {ω : Ω} (hω : ω ∈ d.E) {τ : Ω → ℝ}
    {η : Ω → ℝ≥0 → ℂ} {ζ : Ω → ℝ≥0∞} {x : ℝ} (hp : IsPathGood (η ω) (ζ ω) x) (hα : ∀ s ≤ d.u, d.η₁ ω s = η ω s)
    (huζ : (d.u : ℝ≥0∞) < ζ ω) (hpH : d.η₁ ω d.u ∈ H) (hpO : d.η₁ ω d.u ∉ d.η₂ ω '' Icc 0 d.r)
    (hcl : d.η₁ ω d.u ∈ closure (activeDomain (d.η₁ ω) d.u (d.η₂ ω) d.r))
    (hne₁ : ∀ s < d.u, d.η₁ ω s ≠ d.η₁ ω d.u) (hτ : τ ω = tipPos d d.η₁ ω) :
    IsAGood (fstChart d τ η ζ) (fstLifeP d η ζ) ω := by
  obtain ⟨hR, hD⟩ := isRetCont_fstData hd hω hp hα huζ hpH hpO hcl hne₁
  refine (isAGood_of_isRetCont hR ω).congr ?_ rfl
  show contPath (d.D ω) (fun z => d.fwd ω z - τ ω) _ _ _ = _
  rw [hD, hτ]
  rfl

/-- **The pathwise hypotheses of the first continuation at a sample** (those of `isAGood_fst`). -/
structure IsFstPath (d : RetData Ω) (η : Ω → ℝ≥0 → ℂ) (ζ : Ω → ℝ≥0∞) (x : ℝ) (τ : Ω → ℝ) (ω : Ω) : Prop where
  mem_E : ω ∈ d.E
  path : IsPathGood (η ω) (ζ ω) x
  agree : ∀ s ≤ d.u, d.η₁ ω s = η ω s
  lt : (d.u : ℝ≥0∞) < ζ ω
  tipH : d.η₁ ω d.u ∈ H
  tipO : d.η₁ ω d.u ∉ d.η₂ ω '' Icc 0 d.r
  tipCl : d.η₁ ω d.u ∈ closure (activeDomain (d.η₁ ω) d.u (d.η₂ ω) d.r)
  tipNe : ∀ s < d.u, d.η₁ ω s ≠ d.η₁ ω d.u
  seed : τ ω = tipPos d d.η₁ ω

theorem IsFstPath.isAGood {d : RetData Ω} (hd : d.IsMeasGood) {η : Ω → ℝ≥0 → ℂ} {ζ : Ω → ℝ≥0∞} {x : ℝ}
    {τ : Ω → ℝ} {ω : Ω} (h : IsFstPath d η ζ x τ ω) : IsAGood (fstChart d τ η ζ) (fstLifeP d η ζ) ω :=
  isAGood_fst hd h.mem_E h.path h.agree h.lt h.tipH h.tipO h.tipCl h.tipNe h.seed

theorem IsFstPath.isRetCont {d : RetData Ω} (hd : d.IsMeasGood) {η : Ω → ℝ≥0 → ℂ} {ζ : Ω → ℝ≥0∞} {x : ℝ}
    {τ : Ω → ℝ} {ω : Ω} (h : IsFstPath d η ζ x τ ω) :
    IsRetCont (η ω) (ζ ω) x d.u (d.η₂ ω '' Icc 0 d.r) (fun z => d.fwd ω z - tipPos d d.η₁ ω)
        (fun w => d.inv ω (w + tipPos d d.η₁ ω)) ∧
      d.D ω = H \ fillH (d.η₂ ω '' Icc 0 d.r ∪ η ω '' Icc 0 d.u) :=
  isRetCont_fstData hd h.mem_E h.path h.agree h.lt h.tipH h.tipO h.tipCl h.tipNe

end Pathwise

/-! ### The physical filtration of the first continuation -/

section Filt

variable {Ω : Type*} [mΩ : MeasurableSpace Ω]

/-- **The physical filtration of the first continuation**: the completed retained histories at the lines
`(u + t, r)`. -/
def fstPhysFiltration (P : Measure Ω) (η₁ η₂ : Ω → ℝ≥0 → ℂ) (ζ₁ ζ₂ : Ω → ℝ≥0∞) (u r : ℝ≥0) :
    Filtration ℝ≥0 mΩ where
  seq t := retSigma76 P η₁ η₂ ζ₁ ζ₂ (u + t) r
  mono' _ _ hst := retSigma76_mono P η₁ η₂ ζ₁ ζ₂ (add_le_add le_rfl hst) le_rfl
  le' t := retSigma76_le P η₁ η₂ ζ₁ ζ₂ (u + t) r

theorem fstPhysFiltration_apply (P : Measure Ω) (η₁ η₂ : Ω → ℝ≥0 → ℂ) (ζ₁ ζ₂ : Ω → ℝ≥0∞) (u r t : ℝ≥0) :
    fstPhysFiltration P η₁ η₂ ζ₁ ζ₂ u r t = retSigma76 P η₁ η₂ ζ₁ ζ₂ (u + t) r := rfl

/-- The killed and clipped proxy of the first flow line is an observable of the completed killed histories (the left
analogue of `RetAux79.measurable_retObservedPath_retSigma76`). -/
theorem measurable_retObservedPath_retSigma76_left {P : Measure Ω} {F : Set Ω} {η₁ η₂ η₁' ηc : Ω → ℝ≥0 → ℂ}
    {ζ₁ ζ₂ : Ω → ℝ≥0∞} {b r : ℝ≥0} (hF : MeasurableSet[retSigma76 P η₁ η₂ ζ₁ ζ₂ b r] F)
    (hm : ∀ s, Measurable fun ω => η₁' ω s) (hζ : Measurable ζ₁) {x : ℝ}
    (hp : ∀ ω ∈ F, IsPathGood (η₁' ω) (ζ₁ ω) x)
    (ha : ∀ᵐ ω ∂P, ∀ s : ℝ≥0, (s : ℝ≥0∞) ≤ ζ₁ ω → η₁' ω s = η₁ ω s)
    (hc : ∀ ω, Continuous (ηc ω)) (hmc : ∀ s, Measurable fun ω => ηc ω s)
    (hac : ∀ᵐ ω ∂P, ∀ s, ηc ω s = η₁ ω (capTime (capR b r) (ζ₁ ω) s)) (s : ℝ≥0) :
    Measurable[retSigma76 P η₁ η₂ ζ₁ ζ₂ b r] (fun ω => retObservedPath F η₁' ζ₁ (capR b r) b ω s) := by
  apply measurable_retSigma76_congr
    (measurable_retObservedPath (retSigma76_le P η₁ η₂ ζ₁ ζ₂ b r _ hF) hm hζ hp _ _ _)
    ((measurable_capped_left_retSigma76 hc hmc hac (min_le_right s b)).indicator hF)
  filter_upwards [ha, hac] with ω he hcω
  by_cases hω : ω ∈ F
  · simp only [retObservedPath, indicator_of_mem hω]
    rw [hcω]
    exact he _ (capTime_le _ _ _)
  · simp only [retObservedPath, indicator_of_notMem hω]

variable {P : Measure Ω} {η₁ η₂ η₁' : Ω → ℝ≥0 → ℂ} {ζ₁ ζ₂ : Ω → ℝ≥0∞} {d : RetData Ω} {M : Set Ω} {x₁ : ℝ}

/-- **Survival of the A-stopped first continuation is observable** in its physical filtration. -/
theorem measurableSet_fstSurv (hd : d.IsMeasGood) (hM : MeasurableSet[retSigma76 P η₁ η₂ ζ₁ ζ₂ d.u d.r] M)
    (hζ₁ : Measurable ζ₁) (hm₁ : ∀ t, Measurable fun ω => η₁' ω t)
    (hag : ∀ᵐ ω ∂P, (d.u : ℝ≥0∞) < ζ₁ ω → (d.r : ℝ≥0∞) < ζ₂ ω → ω ∈ d.G ∧
      (∀ s ≤ d.u, d.η₁ ω s = η₁ ω s) ∧ ∀ t ≤ d.r, d.η₂ ω t = η₂ ω t)
    (ha₁ : ∀ᵐ ω ∂P, ∀ s : ℝ≥0, (s : ℝ≥0∞) ≤ ζ₁ ω → η₁' ω s = η₁ ω s)
    (hMg : ∀ ω ∈ M, (d.u : ℝ≥0∞) < ζ₁ ω ∧ (d.r : ℝ≥0∞) < ζ₂ ω ∧ ω ∈ d.G ∧
      IsPathGood (η₁' ω) (ζ₁ ω) x₁ ∧ 0 < fstLifeP d η₁' ζ₁ ω)
    (ηc₁ ηc₂ : ℝ≥0 → Ω → ℝ≥0 → ℂ) (hc₁ : ∀ t ω, Continuous (ηc₁ t ω)) (hc₂ : ∀ t ω, Continuous (ηc₂ t ω))
    (hmc₁ : ∀ t s, Measurable fun ω => ηc₁ t ω s) (hm₂ : ∀ t s, Measurable fun ω => ηc₂ t ω s)
    (hag₁ : ∀ t, ∀ᵐ ω ∂P, ∀ s, ηc₁ t ω s = η₁ ω (capTime (capR (d.u + t) d.r) (ζ₁ ω) s))
    (hag₂ : ∀ t, ∀ᵐ ω ∂P, ∀ s, ηc₂ t ω s = η₂ ω (capTime (capR (d.u + t) d.r) (ζ₂ ω) s)) (t : ℝ≥0) :
    MeasurableSet[fstPhysFiltration P η₁ η₂ ζ₁ ζ₂ d.u d.r t] (M ∩ {ω | (t : ℝ≥0∞) < fstLifeP d η₁' ζ₁ ω}) := by
  change MeasurableSet[retSigma76 P η₁ η₂ ζ₁ ζ₂ (d.u + t) d.r] _
  have hMt : MeasurableSet[retSigma76 P η₁ η₂ ζ₁ ζ₂ (d.u + t) d.r] M :=
    retSigma76_mono P η₁ η₂ ζ₁ ζ₂ le_self_add le_rfl _ hM
  rcases eq_or_lt_of_le (zero_le : (0 : ℝ≥0) ≤ t) with ht | ht
  · subst t
    have he : M ∩ {ω | ((0 : ℝ≥0) : ℝ≥0∞) < fstLifeP d η₁' ζ₁ ω} = M := by
      ext ω
      exact ⟨fun h => h.1, fun h => ⟨h, by rw [ENNReal.coe_zero]; exact (hMg ω h).2.2.2.2⟩⟩
    rw [he]
    exact hMt
  have hut : d.u < d.u + t := lt_add_of_pos_right d.u ht
  have hrec := measurable_lifeRec_retSigma76_left P η₁ η₂ ζ₁ ζ₂ hζ₁ (d.u + t) d.r
  have hA : MeasurableSet[retSigma76 P η₁ η₂ ζ₁ ζ₂ (d.u + t) d.r]
      (M ∩ {ω | ((d.u + t : ℝ≥0) : ℝ≥0∞) < ζ₁ ω}) := by
    have he : {ω | ((d.u + t : ℝ≥0) : ℝ≥0∞) < ζ₁ ω} = {ω | lifeRec (ζ₁ ω) (d.u + t) = ⊤} := by
      ext ω
      exact (lifeRec_eq_top_iff_of_ne_top ENNReal.coe_ne_top).symm
    rw [he]
    exact hMt.inter (hrec (measurableSet_singleton ⊤))
  have hreadη : ∀ s ≤ d.u + t, Measurable[retSigma76 P η₁ η₂ ζ₁ ζ₂ (d.u + t) d.r]
      ((M ∩ {ω | ((d.u + t : ℝ≥0) : ℝ≥0∞) < ζ₁ ω}).indicator fun ω => η₁' ω s) := by
    intro s hs
    apply measurable_indicator_retSigma76_of_reader hA (hm₁ s)
      (measurable_capped_left_retSigma76 (hc₁ t) (hmc₁ t) (hag₁ t) hs)
    filter_upwards [ha₁, hag₁ t] with ω he hc hω
    rw [hc s, capTime_eq_of_lt hω.2 (lt_capR_left (d.u + t) d.r) hs]
    exact he s ((ENNReal.coe_le_coe.2 hs).trans hω.2.le)
  have hreadβ : ∀ s ≤ d.r, Measurable[retSigma76 P η₁ η₂ ζ₁ ζ₂ (d.u + t) d.r]
      ((M ∩ {ω | ((d.u + t : ℝ≥0) : ℝ≥0∞) < ζ₁ ω}).indicator fun ω => d.η₂ ω s) := by
    intro s hs
    apply measurable_indicator_retSigma76_of_reader hA (hd.meas₂ s)
      (measurable_capped_right_retSigma76 (hc₂ t) (hm₂ t) (hag₂ t) hs)
    filter_upwards [hag, hag₂ t] with ω hagω hc hω
    obtain ⟨hu, hr, -⟩ := hMg ω hω.1
    rw [hc s, capTime_eq_of_lt hr (lt_capR_right (d.u + t) d.r) hs]
    exact (hagω hu hr).2.2 s hs
  have hm := @measurableSet_lt_contStopA_of_prefix Ω (retSigma76 P η₁ η₂ ζ₁ ζ₂ (d.u + t) d.r) M η₁' d.η₂ η₁' ζ₁
    d.u (d.u + t) d.r d.u hut hA hreadη hreadβ (fun s hs => hreadη s (hs.trans le_self_add))
    (fun ω hω hζ => (hMg ω hω).2.2.2.1.continuousOn.mono fun s hs => (ENNReal.coe_le_coe.2 hs).trans hζ.le)
    (fun ω hω hζ => isPathGood_continuousAt (hMg ω hω).2.2.2.1 hζ)
    (fun ω hω => by
      rw [← Icc_zero_eq_Iic]
      exact (hd.good ω (hMg ω hω).2.2.1).2.1)
    (fun ω hω => (hMg ω hω).2.2.2.1.continuousOn.mono fun s hs =>
      (ENNReal.coe_le_coe.2 hs).trans (hMg ω hω).1.le)
  have he : M ∩ {ω | (t : ℝ≥0∞) < fstLifeP d η₁' ζ₁ ω} =
      M ∩ {ω | ((d.u + t : ℝ≥0) : ℝ≥0∞) <
        contStop (η₁' ω) (ζ₁ ω) d.u (d.η₂ ω '' Icc 0 d.r ∪ η₁' ω '' Icc 0 d.u)} := by
    ext ω
    exact and_congr_right fun _ => coe_add_lt_iff
  rw [he]
  exact hm

/-- **The A-stopped first continuation is observed in its physical filtration** (`AObs`). The chart `(D₁, φ₁)` is a
stop-line measurable chart agreeing on `M` with the chart of `d` recentred at the seed `τ`. -/
theorem fstObs (hd : d.IsMeasGood) (hM : MeasurableSet[retSigma76 P η₁ η₂ ζ₁ ζ₂ d.u d.r] M)
    (hζ₁ : Measurable ζ₁) (hm₁ : ∀ t, Measurable fun ω => η₁' ω t)
    (hag : ∀ᵐ ω ∂P, (d.u : ℝ≥0∞) < ζ₁ ω → (d.r : ℝ≥0∞) < ζ₂ ω → ω ∈ d.G ∧
      (∀ s ≤ d.u, d.η₁ ω s = η₁ ω s) ∧ ∀ t ≤ d.r, d.η₂ ω t = η₂ ω t)
    (ha₁ : ∀ᵐ ω ∂P, ∀ s : ℝ≥0, (s : ℝ≥0∞) ≤ ζ₁ ω → η₁' ω s = η₁ ω s) {τ : Ω → ℝ}
    (hMg : ∀ ω ∈ M, (d.r : ℝ≥0∞) < ζ₂ ω ∧ IsFstPath d η₁' ζ₁ x₁ τ ω)
    (ηc₁ ηc₂ : ℝ≥0 → Ω → ℝ≥0 → ℂ) (hc₁ : ∀ t ω, Continuous (ηc₁ t ω)) (hc₂ : ∀ t ω, Continuous (ηc₂ t ω))
    (hmc₁ : ∀ t s, Measurable fun ω => ηc₁ t ω s) (hm₂ : ∀ t s, Measurable fun ω => ηc₂ t ω s)
    (hag₁ : ∀ t, ∀ᵐ ω ∂P, ∀ s, ηc₁ t ω s = η₁ ω (capTime (capR (d.u + t) d.r) (ζ₁ ω) s))
    (hag₂ : ∀ t, ∀ᵐ ω ∂P, ∀ s, ηc₂ t ω s = η₂ ω (capTime (capR (d.u + t) d.r) (ζ₂ ω) s))
    {D₁ : Ω → Set ℂ} {φ₁ : Ω → ℂ → ℂ} (hDo : ∀ ω, IsOpen (D₁ ω))
    (hdom : ∀ z, MeasurableSet[retSigma76 P η₁ η₂ ζ₁ ζ₂ d.u d.r] {ω | z ∈ D₁ ω})
    (hfwd : ∀ z, Measurable[retSigma76 P η₁ η₂ ζ₁ ζ₂ d.u d.r] ({ω | z ∈ D₁ ω}.indicator fun ω => φ₁ ω z))
    (hD₁ : ∀ ω ∈ M, D₁ ω = d.D ω) (hφ₁ : ∀ ω ∈ M, φ₁ ω = fun z => d.fwd ω z - τ ω) :
    AObs (fstPhysFiltration P η₁ η₂ ζ₁ ζ₂ d.u d.r) M (fstChart d τ η₁' ζ₁) (fstLifeP d η₁' ζ₁) := by
  classical
  let 𝓖 := fstPhysFiltration P η₁ η₂ ζ₁ ζ₂ d.u d.r
  have hR := fun ω (hω : ω ∈ M) => (hMg ω hω).2.isRetCont hd
  have hg : ∀ ω ∈ M, IsAGood (fstChart d τ η₁' ζ₁) (fstLifeP d η₁' ζ₁) ω := fun ω hω =>
    (hMg ω hω).2.isAGood hd
  have hsurv : ∀ t : ℝ≥0, MeasurableSet[𝓖 t] (M ∩ {ω | (t : ℝ≥0∞) < fstLifeP d η₁' ζ₁ ω}) :=
    measurableSet_fstSurv hd hM hζ₁ hm₁ hag ha₁ (x₁ := x₁)
      (fun ω hω => ⟨(hMg ω hω).2.lt, (hMg ω hω).1, RetData.E_subset_G (hMg ω hω).2.mem_E, (hMg ω hω).2.path,
        (hg ω hω).pos⟩) ηc₁ ηc₂ hc₁ hc₂ hmc₁ hm₂ hag₁ hag₂
  have hM₀ : MeasurableSet[𝓖 0] M := by
    change MeasurableSet[retSigma76 P η₁ η₂ ζ₁ ζ₂ (d.u + 0) d.r] M
    rw [add_zero]
    exact hM
  refine ⟨hM₀, ?_, hsurv⟩
  intro t s hst
  rcases eq_or_lt_of_le (zero_le : (0 : ℝ≥0) ≤ t) with ht | ht
  · subst t
    have hs : s = 0 := le_antisymm hst zero_le
    subst s
    have he : (M.indicator fun ω => fstChart d τ η₁' ζ₁ ω 0) = fun _ => 0 := by
      funext ω
      by_cases hω : ω ∈ M
      · simp only [indicator_of_mem hω]
        exact (hg ω hω).zero
      · exact indicator_of_notMem hω _
    rw [he]
    exact measurable_const
  have hMt : MeasurableSet[𝓖 t] M := 𝓖.mono zero_le _ hM₀
  let ηk := retObservedPath M η₁' ζ₁ (capR (d.u + t) d.r) (d.u + t)
  have hmη : ∀ q, Measurable[𝓖 t] fun ω => ηk ω q := fun q =>
    measurable_retObservedPath_retSigma76_left hMt hm₁ hζ₁ (fun ω hω => (hMg ω hω).2.path) ha₁ (hc₁ t) (hmc₁ t)
      (hag₁ t) q
  have hprefix : ∀ ω ∈ M, ∀ q : ℝ≥0, (q : ℝ≥0∞) < min (fstLifeP d η₁' ζ₁ ω) (t : ℝ≥0∞) →
      ηk ω (d.u + q) = η₁' ω (d.u + q) := by
    intro ω hω q hq
    have hqt : q < t := ENNReal.coe_lt_coe.1 ((lt_min_iff.1 hq).2)
    have hζ : ((d.u + q : ℝ≥0) : ℝ≥0∞) ≤ ζ₁ ω :=
      ((coe_add_lt_iff.1 (lt_min_iff.1 hq).1).trans_le contStop_le).le
    simp only [ηk, retObservedPath, indicator_of_mem hω, min_eq_left (add_le_add le_rfl hqt.le)]
    rw [capTime_of_le _ _ (le_min hζ (ENNReal.coe_le_coe.2
      ((add_le_add le_rfl hqt.le).trans (lt_capR_left (d.u + t) d.r).le)))]
  suffices hm : Measurable[𝓖 t] (M.indicator fun ω =>
      contPath (D₁ ω) (φ₁ ω) (η₁' ω) d.u (fstLifeP d η₁' ζ₁ ω) s) by
    convert hm using 1
    funext ω
    by_cases hω : ω ∈ M
    · simp only [indicator_of_mem hω, fstChart, hD₁ ω hω, hφ₁ ω hω]
    · simp only [indicator_of_notMem hω]
  apply @measurable_contPath_of_past Ω (𝓖 t) M hMt D₁ hDo
    (fun z => (retSigma76_mono P η₁ η₂ ζ₁ ζ₂ le_self_add le_rfl) _ (hdom z)) φ₁
    (fun z => (hfwd z).mono (retSigma76_mono P η₁ η₂ ζ₁ ζ₂ le_self_add le_rfl) le_rfl)
    η₁' ηk hmη (fun ω _ => continuous_retObservedPath (fun ω hω => (hMg ω hω).2.path) _ _ ω) d.u t ht
    (fstLifeP d η₁' ζ₁) (measurable_indicator_min_of_survival hM₀ hsurv t)
    (fun ω hω => (hg ω hω).pos) hprefix ?_ ?_ ?_ s hst
  · intro ω hω q hq
    rw [hD₁ ω hω, (hR ω hω).2]
    exact (hR ω hω).1.mem_closure_of_mem_contSet (mem_contSet_of_le le_self_add (coe_add_lt_iff.1 hq).le)
  · intro ω hω q hq
    rw [hφ₁ ω hω, hD₁ ω hω, (hR ω hω).2, (hMg ω hω).2.seed]
    exact ⟨_, ((hR ω hω).1.contPath_spec_lt hq).2.1⟩
  · intro ω hω
    have h := (hg ω hω).cont
    simp only [fstChart] at h
    rw [hD₁ ω hω, hφ₁ ω hω]
    exact h

end Filt

end InteractingSLE.RLC.AStopProc
