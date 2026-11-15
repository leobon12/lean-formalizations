/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.AStopProcAdapt
import InteractingSLE.Spec.Supplement.AStopProcSurv
import InteractingSLE.Spec.Supplement.OrdDetLineFacts
import InteractingSLE.Spec.Restart.RetPlumbProofResidualObserved
import InteractingSLE.Spec.Restart.RetPlumbProofResidualPhysical

/-!
# The A-stopped second continuation: chart path, good samples and physical survival

Packet PROVE-T15-ASTOP-PROC. For retained data `d` and a continuation path `η` (in the application a measurable version
of the second flow line), the second continuation after `d.r`, stopped at its first new contact with the retained
union `A = d.η₁[0, d.u] ∪ η[0, d.r]` only (real contacts allowed, G7 p. 497):

* `sndSet`, `sndLifeP` (physical lifetime), `sndChart` (chart path in physical time, the chart of `d`);
* **`isAGood_snd`**: at a chart sample of `d` where `η` is a good path agreeing with `d.η₂` on `[0, d.r]`, the sample is
  good (`AStopProc.IsAGood`; `Supp7.isRetCont_snd`, `RetAux79.canonRetPath_facts`);
* **`measurableSet_sndSurv`**: the survival events `M ∩ {t < sndLifeP}` are events of RETPLUMB's physical filtration
  `retPhysFiltration` (the completed retained histories at the lines `(u, r + t)`), from the capped history readers.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Filter Topology MeasureTheory
open scoped NNReal ENNReal

namespace InteractingSLE.RLC.AStopProc

open Restart Restart.RetAux79 Supp7 Sec7 Sec7.Lemma76F LocalSets

section Defs

variable {Ω : Type*}

/-- **The retained union of the second continuation**, with the continuation path `η` on the second prefix. -/
def sndSet (d : RetData Ω) (η : Ω → ℝ≥0 → ℂ) (ω : Ω) : Set ℂ := d.η₁ ω '' Icc 0 d.u ∪ η ω '' Icc 0 d.r

/-- **The physical lifetime of the A-stopped second continuation** (relative to `d.r`). -/
def sndLifeP (d : RetData Ω) (η : Ω → ℝ≥0 → ℂ) (ζ : Ω → ℝ≥0∞) (ω : Ω) : ℝ≥0∞ :=
  contLife (η ω) (ζ ω) d.r (sndSet d η ω)

/-- **The chart path of the A-stopped second continuation** in physical time, in the chart of `d`. -/
def sndChart (d : RetData Ω) (η : Ω → ℝ≥0 → ℂ) (ζ : Ω → ℝ≥0∞) (ω : Ω) : ℝ≥0 → ℂ :=
  contPath (d.D ω) (d.fwd ω) (η ω) d.r (sndLifeP d η ζ ω)

end Defs

section Pathwise

variable {Ω : Type*} [MeasurableSpace Ω]

/-- **The second continuation at a chart sample of `d` is a retained continuation**, and the domain of `d` is the
complement of the filled retained union (the first lines of `OrdDet.exists_ordCont_facts`). -/
theorem isRetCont_sndData {d : RetData Ω} (hd : d.IsMeasGood) {ω : Ω} (hω : ω ∈ d.E) {η : ℝ≥0 → ℂ}
    {ζ : ℝ≥0∞} {x : ℝ} (hp : IsPathGood η ζ x) (hβ₀ : ∀ s ≤ d.r, d.η₂ ω s = η s) (hrζ : (d.r : ℝ≥0∞) < ζ) :
    IsRetCont η ζ x d.r (d.η₁ ω '' Icc 0 d.u) (d.fwd ω) (d.inv ω) ∧
      d.D ω = QuantumZipper.H \ fillH (d.η₁ ω '' Icc 0 d.u ∪ η '' Icc 0 d.r) := by
  have hg := hd.good ω (RetData.E_subset_G hω)
  obtain ⟨⟨x₀, hx₀⟩, hC⟩ := hd.isRetChart hω
  have hφ : ∃ x₀ : ℝ, ∀ z, d.fwd ω z =
      ConformalImage.mapOut (fillH (prefixSet (d.η₁ ω) d.u (d.η₂ ω) d.r)) z - x₀ :=
    ⟨x₀, fun z => by
      show d.g ω z - d.shift ω = _
      rw [hx₀, RetData.g, RetData.K_of_mem hω]⟩
  have hωE₀ := RetData.E_subset_E₀ hω
  have hcl : d.η₂ ω d.r ∈ closure (activeDomain (d.η₁ ω) d.u (d.η₂ ω) d.r) := by
    rw [← hd.DOf_of_mem RetData.E₀_subset_G hωE₀]
    exact hω.2
  refine ⟨isRetCont_snd hg hC hφ hp hβ₀ hrζ hωE₀.1.2 hωE₀.2 hcl, ?_⟩
  rw [hd.D_of_mem hω, activeDomain_eq (isCompact_prefixSet' hg.1 hg.2.1).isClosed, prefixSet,
    image_congr fun t ht => hβ₀ t ht.2]

/-- **Good samples of the A-stopped second continuation.** -/
theorem isAGood_snd {d : RetData Ω} (hd : d.IsMeasGood) {ω : Ω} (hω : ω ∈ d.E) {η : Ω → ℝ≥0 → ℂ}
    {ζ : Ω → ℝ≥0∞} {x : ℝ} (hp : IsPathGood (η ω) (ζ ω) x) (hβ₀ : ∀ s ≤ d.r, d.η₂ ω s = η ω s)
    (hrζ : (d.r : ℝ≥0∞) < ζ ω) : IsAGood (sndChart d η ζ) (sndLifeP d η ζ) ω := by
  obtain ⟨hR, hD⟩ := isRetCont_sndData hd hω hp hβ₀ hrζ
  refine (isAGood_of_isRetCont hR ω).congr ?_ rfl
  show contPath (d.D ω) _ _ _ _ = _
  rw [hD]
  rfl

end Pathwise

/-! ### Survival in the physical filtration -/

section Survival

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} {η₁ η₂ η₂' : Ω → ℝ≥0 → ℂ}
  {ζ₁ ζ₂ : Ω → ℝ≥0∞} {d : RetData Ω} {M : Set Ω} {x₂ : ℝ}

/-- **Survival of the A-stopped second continuation is observable** in the physical filtration: the live record and
the capped history readers of both flow lines through the line `(u, r + t)`. -/
theorem measurableSet_sndSurv (hd : d.IsMeasGood) (hM : MeasurableSet[retSigma76 P η₁ η₂ ζ₁ ζ₂ d.u d.r] M)
    (hζ₂ : Measurable ζ₂) (hm₂ : ∀ t, Measurable fun ω => η₂' ω t)
    (hag : ∀ᵐ ω ∂P, (d.u : ℝ≥0∞) < ζ₁ ω → (d.r : ℝ≥0∞) < ζ₂ ω → ω ∈ d.G ∧
      (∀ s ≤ d.u, d.η₁ ω s = η₁ ω s) ∧ ∀ t ≤ d.r, d.η₂ ω t = η₂ ω t)
    (ha₂ : ∀ᵐ ω ∂P, ∀ s : ℝ≥0, (s : ℝ≥0∞) ≤ ζ₂ ω → η₂' ω s = η₂ ω s)
    (hMg : ∀ ω ∈ M, (d.u : ℝ≥0∞) < ζ₁ ω ∧ (d.r : ℝ≥0∞) < ζ₂ ω ∧ ω ∈ d.G ∧
      IsPathGood (η₂' ω) (ζ₂ ω) x₂ ∧ 0 < sndLifeP d η₂' ζ₂ ω)
    (ηc₁ ηc₂ : ℝ≥0 → Ω → ℝ≥0 → ℂ) (hc₁ : ∀ t ω, Continuous (ηc₁ t ω)) (hc₂ : ∀ t ω, Continuous (ηc₂ t ω))
    (hm₁ : ∀ t s, Measurable fun ω => ηc₁ t ω s) (hmc₂ : ∀ t s, Measurable fun ω => ηc₂ t ω s)
    (hag₁ : ∀ t, ∀ᵐ ω ∂P, ∀ s, ηc₁ t ω s = η₁ ω (capTime (capR d.u (d.r + t)) (ζ₁ ω) s))
    (hag₂ : ∀ t, ∀ᵐ ω ∂P, ∀ s, ηc₂ t ω s = η₂ ω (capTime (capR d.u (d.r + t)) (ζ₂ ω) s)) (t : ℝ≥0) :
    MeasurableSet[retPhysFiltration P η₁ η₂ ζ₁ ζ₂ d.u d.r t] (M ∩ {ω | (t : ℝ≥0∞) < sndLifeP d η₂' ζ₂ ω}) := by
  change MeasurableSet[retSigma76 P η₁ η₂ ζ₁ ζ₂ d.u (d.r + t)] _
  have hMt : MeasurableSet[retSigma76 P η₁ η₂ ζ₁ ζ₂ d.u (d.r + t)] M :=
    retSigma76_mono P η₁ η₂ ζ₁ ζ₂ le_rfl le_self_add _ hM
  rcases eq_or_lt_of_le (zero_le : (0 : ℝ≥0) ≤ t) with ht | ht
  · subst t
    have he : M ∩ {ω | ((0 : ℝ≥0) : ℝ≥0∞) < sndLifeP d η₂' ζ₂ ω} = M := by
      ext ω
      exact ⟨fun h => h.1, fun h => ⟨h, by rw [ENNReal.coe_zero]; exact (hMg ω h).2.2.2.2⟩⟩
    rw [he]
    exact hMt
  have hrt : d.r < d.r + t := lt_add_of_pos_right d.r ht
  have hrec := measurable_lifeRec_retSigma76_right P η₁ η₂ ζ₁ ζ₂ hζ₂ d.u (d.r + t)
  have hA : MeasurableSet[retSigma76 P η₁ η₂ ζ₁ ζ₂ d.u (d.r + t)] (M ∩ {ω | ((d.r + t : ℝ≥0) : ℝ≥0∞) < ζ₂ ω}) := by
    have he : {ω | ((d.r + t : ℝ≥0) : ℝ≥0∞) < ζ₂ ω} = {ω | lifeRec (ζ₂ ω) (d.r + t) = ⊤} := by
      ext ω
      exact (lifeRec_eq_top_iff_of_ne_top ENNReal.coe_ne_top).symm
    rw [he]
    exact hMt.inter (hrec (measurableSet_singleton ⊤))
  have hread₁ : ∀ s ≤ d.u, Measurable[retSigma76 P η₁ η₂ ζ₁ ζ₂ d.u (d.r + t)]
      ((M ∩ {ω | ((d.r + t : ℝ≥0) : ℝ≥0∞) < ζ₂ ω}).indicator fun ω => d.η₁ ω s) := by
    intro s hs
    apply measurable_indicator_retSigma76_of_reader hA (hd.meas₁ s)
      (measurable_capped_left_retSigma76 (hc₁ t) (hm₁ t) (hag₁ t) hs)
    filter_upwards [hag, hag₁ t] with ω hagω hc hω
    obtain ⟨hu, hr, -⟩ := hMg ω hω.1
    rw [hc s, capTime_eq_of_lt hu (lt_capR_left d.u (d.r + t)) hs]
    exact (hagω hu hr).2.1 s hs
  have hread₂ : ∀ s ≤ d.r + t, Measurable[retSigma76 P η₁ η₂ ζ₁ ζ₂ d.u (d.r + t)]
      ((M ∩ {ω | ((d.r + t : ℝ≥0) : ℝ≥0∞) < ζ₂ ω}).indicator fun ω => η₂' ω s) := by
    intro s hs
    apply measurable_indicator_retSigma76_of_reader hA (hm₂ s)
      (measurable_capped_right_retSigma76 (hc₂ t) (hmc₂ t) (hag₂ t) hs)
    filter_upwards [ha₂, hag₂ t] with ω he hc hω
    rw [hc s, capTime_eq_of_lt hω.2 (lt_capR_right d.u (d.r + t)) hs]
    exact he s ((ENNReal.coe_le_coe.2 hs).trans hω.2.le)
  have hm := @measurableSet_lt_contStopA_of_prefix Ω (retSigma76 P η₁ η₂ ζ₁ ζ₂ d.u (d.r + t)) M η₂' d.η₁ η₂' ζ₂
    d.r (d.r + t) d.u d.r hrt hA hread₂ hread₁ (fun s hs => hread₂ s (hs.trans le_self_add))
    (fun ω hω hζ => (hMg ω hω).2.2.2.1.continuousOn.mono fun s hs => (ENNReal.coe_le_coe.2 hs).trans hζ.le)
    (fun ω hω hζ => isPathGood_continuousAt (hMg ω hω).2.2.2.1 hζ)
    (fun ω hω => by
      rw [← Icc_zero_eq_Iic]
      exact (hd.good ω (hMg ω hω).2.2.1).1)
    (fun ω hω => (hMg ω hω).2.2.2.1.continuousOn.mono fun s hs =>
      (ENNReal.coe_le_coe.2 hs).trans (hMg ω hω).2.1.le)
  have he : M ∩ {ω | (t : ℝ≥0∞) < sndLifeP d η₂' ζ₂ ω} =
      M ∩ {ω | ((d.r + t : ℝ≥0) : ℝ≥0∞) < contStop (η₂' ω) (ζ₂ ω) d.r (d.η₁ ω '' Icc 0 d.u ∪ η₂' ω '' Icc 0 d.r)} := by
    ext ω
    exact and_congr_right fun _ => coe_add_lt_iff
  rw [he]
  exact hm

/-- **The A-stopped second continuation is observed in the physical filtration** (`AObs`): `M` is initial, the chart
coordinates through `t` and the survival through `t` are events of the line `(u, r + t)`. The chart `(D₁, φ₁)` is any
chart measurable for the stop line's completed histories that agrees with the chart of `d` on `M` (in the application
the chart of `d` restricted to the live event, `RetAux79.chart_measurability_retSigma76`). -/
theorem sndObs (hd : d.IsMeasGood) (hM : MeasurableSet[retSigma76 P η₁ η₂ ζ₁ ζ₂ d.u d.r] M)
    (hζ₂ : Measurable ζ₂) (hm₂ : ∀ t, Measurable fun ω => η₂' ω t)
    (hag : ∀ᵐ ω ∂P, (d.u : ℝ≥0∞) < ζ₁ ω → (d.r : ℝ≥0∞) < ζ₂ ω → ω ∈ d.G ∧
      (∀ s ≤ d.u, d.η₁ ω s = η₁ ω s) ∧ ∀ t ≤ d.r, d.η₂ ω t = η₂ ω t)
    (ha₂ : ∀ᵐ ω ∂P, ∀ s : ℝ≥0, (s : ℝ≥0∞) ≤ ζ₂ ω → η₂' ω s = η₂ ω s)
    (hMg : ∀ ω ∈ M, (d.u : ℝ≥0∞) < ζ₁ ω ∧ (d.r : ℝ≥0∞) < ζ₂ ω ∧ ω ∈ d.E ∧
      IsPathGood (η₂' ω) (ζ₂ ω) x₂ ∧ ∀ s ≤ d.r, d.η₂ ω s = η₂' ω s)
    (ηc₁ ηc₂ : ℝ≥0 → Ω → ℝ≥0 → ℂ) (hc₁ : ∀ t ω, Continuous (ηc₁ t ω)) (hc₂ : ∀ t ω, Continuous (ηc₂ t ω))
    (hm₁ : ∀ t s, Measurable fun ω => ηc₁ t ω s) (hmc₂ : ∀ t s, Measurable fun ω => ηc₂ t ω s)
    (hag₁ : ∀ t, ∀ᵐ ω ∂P, ∀ s, ηc₁ t ω s = η₁ ω (capTime (capR d.u (d.r + t)) (ζ₁ ω) s))
    (hag₂ : ∀ t, ∀ᵐ ω ∂P, ∀ s, ηc₂ t ω s = η₂ ω (capTime (capR d.u (d.r + t)) (ζ₂ ω) s))
    {D₁ : Ω → Set ℂ} {φ₁ : Ω → ℂ → ℂ} (hDo : ∀ ω, IsOpen (D₁ ω))
    (hdom : ∀ z, MeasurableSet[retSigma76 P η₁ η₂ ζ₁ ζ₂ d.u d.r] {ω | z ∈ D₁ ω})
    (hfwd : ∀ z, Measurable[retSigma76 P η₁ η₂ ζ₁ ζ₂ d.u d.r] ({ω | z ∈ D₁ ω}.indicator fun ω => φ₁ ω z))
    (hD₁ : ∀ ω ∈ M, D₁ ω = d.D ω) (hφ₁ : ∀ ω ∈ M, φ₁ ω = d.fwd ω) :
    AObs (retPhysFiltration P η₁ η₂ ζ₁ ζ₂ d.u d.r) M (sndChart d η₂' ζ₂) (sndLifeP d η₂' ζ₂) := by
  classical
  let 𝓖 := retPhysFiltration P η₁ η₂ ζ₁ ζ₂ d.u d.r
  have hR : ∀ ω ∈ M, IsRetCont (η₂' ω) (ζ₂ ω) x₂ d.r (d.η₁ ω '' Icc 0 d.u) (d.fwd ω) (d.inv ω) ∧
      d.D ω = QuantumZipper.H \ fillH (d.η₁ ω '' Icc 0 d.u ∪ η₂' ω '' Icc 0 d.r) := fun ω hω =>
    isRetCont_sndData hd (hMg ω hω).2.2.1 (hMg ω hω).2.2.2.1 (hMg ω hω).2.2.2.2 (hMg ω hω).2.1
  have hg : ∀ ω ∈ M, IsAGood (sndChart d η₂' ζ₂) (sndLifeP d η₂' ζ₂) ω := fun ω hω =>
    isAGood_snd hd (hMg ω hω).2.2.1 (hMg ω hω).2.2.2.1 (hMg ω hω).2.2.2.2 (hMg ω hω).2.1
  have hsurv : ∀ t : ℝ≥0, MeasurableSet[𝓖 t] (M ∩ {ω | (t : ℝ≥0∞) < sndLifeP d η₂' ζ₂ ω}) :=
    measurableSet_sndSurv hd hM hζ₂ hm₂ hag ha₂ (x₂ := x₂)
      (fun ω hω => ⟨(hMg ω hω).1, (hMg ω hω).2.1, RetData.E_subset_G (hMg ω hω).2.2.1, (hMg ω hω).2.2.2.1,
        (hg ω hω).pos⟩) ηc₁ ηc₂ hc₁ hc₂ hm₁ hmc₂ hag₁ hag₂
  have hM₀ : MeasurableSet[𝓖 0] M := by
    change MeasurableSet[retSigma76 P η₁ η₂ ζ₁ ζ₂ d.u (d.r + 0)] M
    rw [add_zero]
    exact hM
  refine ⟨hM₀, ?_, hsurv⟩
  intro t s hst
  rcases eq_or_lt_of_le (zero_le : (0 : ℝ≥0) ≤ t) with ht | ht
  · subst t
    have hs : s = 0 := le_antisymm hst zero_le
    subst s
    have he : (M.indicator fun ω => sndChart d η₂' ζ₂ ω 0) = fun _ => 0 := by
      funext ω
      by_cases hω : ω ∈ M
      · simp only [indicator_of_mem hω]
        exact (hg ω hω).zero
      · exact indicator_of_notMem hω _
    rw [he]
    exact measurable_const
  have hMt : MeasurableSet[𝓖 t] M := 𝓖.mono zero_le _ hM₀
  let ηk := retObservedPath M η₂' ζ₂ (capR d.u (d.r + t)) (d.r + t)
  have hmη : ∀ q, Measurable[𝓖 t] fun ω => ηk ω q := fun q =>
    measurable_retObservedPath_retSigma76 hMt hm₂ hζ₂ (fun ω hω => (hMg ω hω).2.2.2.1) ha₂ (hc₂ t) (hmc₂ t)
      (hag₂ t) q
  have hprefix : ∀ ω ∈ M, ∀ q : ℝ≥0, (q : ℝ≥0∞) < min (sndLifeP d η₂' ζ₂ ω) (t : ℝ≥0∞) →
      ηk ω (d.r + q) = η₂' ω (d.r + q) := by
    intro ω hω q hq
    have hqt : q < t := ENNReal.coe_lt_coe.1 ((lt_min_iff.1 hq).2)
    have hζ : ((d.r + q : ℝ≥0) : ℝ≥0∞) ≤ ζ₂ ω :=
      ((coe_add_lt_iff.1 (lt_min_iff.1 hq).1).trans_le contStop_le).le
    simp only [ηk, retObservedPath, indicator_of_mem hω, min_eq_left (add_le_add le_rfl hqt.le)]
    rw [capTime_of_le _ _ (le_min hζ (ENNReal.coe_le_coe.2
      ((add_le_add le_rfl hqt.le).trans (lt_capR_right d.u (d.r + t)).le)))]
  suffices hm : Measurable[𝓖 t] (M.indicator fun ω =>
      contPath (D₁ ω) (φ₁ ω) (η₂' ω) d.r (sndLifeP d η₂' ζ₂ ω) s) by
    convert hm using 1
    funext ω
    by_cases hω : ω ∈ M
    · simp only [indicator_of_mem hω, sndChart, hD₁ ω hω, hφ₁ ω hω]
    · simp only [indicator_of_notMem hω]
  apply @measurable_contPath_of_past Ω (𝓖 t) M hMt D₁ hDo
    (fun z => (retSigma76_mono P η₁ η₂ ζ₁ ζ₂ le_rfl le_self_add) _ (hdom z)) φ₁
    (fun z => (hfwd z).mono (retSigma76_mono P η₁ η₂ ζ₁ ζ₂ le_rfl le_self_add) le_rfl)
    η₂' ηk hmη (fun ω _ => continuous_retObservedPath (fun ω hω => (hMg ω hω).2.2.2.1) _ _ ω) d.r t ht
    (sndLifeP d η₂' ζ₂) (measurable_indicator_min_of_survival hM₀ hsurv t)
    (fun ω hω => (hg ω hω).pos) hprefix ?_ ?_ ?_ s hst
  · intro ω hω q hq
    rw [hD₁ ω hω, (hR ω hω).2]
    exact (hR ω hω).1.mem_closure_of_mem_contSet (mem_contSet_of_le le_self_add (coe_add_lt_iff.1 hq).le)
  · intro ω hω q hq
    rw [hφ₁ ω hω, hD₁ ω hω, (hR ω hω).2]
    exact ⟨_, ((hR ω hω).1.contPath_spec_lt hq).2.1⟩
  · intro ω hω
    have h := (hg ω hω).cont
    simp only [sndChart] at h
    rw [hD₁ ω hω, hφ₁ ω hω]
    exact h

end Survival

end InteractingSLE.RLC.AStopProc
