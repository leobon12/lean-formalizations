/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Restart.FCKerLawLine
import InteractingSLE.Spec.Restart.FCPlumbAssembly2Inputs
import InteractingSLE.Spec.Restart.FCK2FinalClock
import InteractingSLE.Spec.Restart.RetPlumbProofDriverRead
import InteractingSLE.Spec.Restart.RetPlumbProofInputsClock
import InteractingSLE.Spec.Restart.RetPlumbProofMeas
import InteractingSLE.Spec.Supplement.RelSafeCore

/-!
# The first continuation read in the physical filtration

Packet PROVE-T15-FCKER3 (R82). The corrected forward inputs of Theorem 1.5 (`FirstContactK2ForwardKernelsCStatement`)
reduce to laws on deterministic physical lines (`FCKerLawLine`) once the capacity clock is adapted to a physical
filtration that observes the retained history and the driver on the clock cuts. Here the physical filtration is the
completed physical record `fcPhysicalFiltration P d t` (the retained histories and the first path's killed history up
to `s₀ + t`), and:

* `physReadTime`, `physPoint`: the first path at the clamped continuation time, read from the record;
* **`measurable_cPath_fcPhysical`**: the chart path of the first continuation at every time `r ≤ t` is measurable
  for the physical record at `t` (the chart is read from the retained histories through `stopData`);
* `exists_fcContEvent`: a measurable event of full measure in the meeting branch on which both continuations have
  their chart-path specifications and strictly increasing capacity clocks.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal
open QuantumZipper (H Hbar)
open LQGMetric (DistOn TestOn)

namespace InteractingSLE.Restart.FCPlumb.FCKerC

open Sec6 LocalSets

universe u

/-! ### Reading a recorded path at a random time -/

section Read

/-- The recorded coordinate at the dyadic time below a time `τ`, jointly measurable in the record and `τ`. -/
theorem measurable_coord_qBelow (n : ℕ) :
    Measurable fun p : (ℚ≥0 → ℂ) × ℝ≥0 => p.1 (qBelow n p.2) := by
  have hf : Measurable fun p : (ℚ≥0 → ℂ) × ℕ => p.1 ((p.2 : ℚ≥0) / 2 ^ n) :=
    measurable_from_prod_countable_left fun k =>
      (measurable_pi_apply ((k : ℚ≥0) / 2 ^ n) : Measurable fun f : ℚ≥0 → ℂ => f ((k : ℚ≥0) / 2 ^ n))
  exact hf.comp (measurable_fst.prodMk ((LP.measurable_dyadicIdx n).comp measurable_snd))

/-- **Reading a recorded path at a random time** is jointly measurable. -/
theorem measurable_recon_uncurry : Measurable fun p : Hist × ℝ≥0 => recon p.1 p.2 := by
  unfold recon
  exact (StronglyMeasurable.limUnder fun n =>
    ((measurable_coord_qBelow n).comp
      ((measurable_snd.comp measurable_fst).prodMk measurable_snd)).stronglyMeasurable).measurable

/-- The continuation time `contTime s₀ ζ r`, `r ≤ t`, read from the physical record at `t`: the recorded contact time
and the killing record of the first path at `s₀ + t`. -/
def physReadTime (r : ℝ≥0) (y : (KHist × KHist) × (KHist × KHist)) : ℝ≥0 :=
  contTime y.1.1.1.1.toNNReal y.2.1.2 r

theorem measurable_physReadTime (r : ℝ≥0) :
    Measurable (physReadTime r) := by
  have ht : Measurable fun y : (KHist × KHist) × (KHist × KHist) => y.1.1.1.1.toNNReal :=
    ENNReal.measurable_toNNReal.comp
      ((measurable_fst.comp measurable_fst).comp (measurable_fst.comp measurable_fst))
  have hl : Measurable fun y : (KHist × KHist) × (KHist × KHist) => y.2.1.2 :=
    measurable_snd.comp (measurable_fst.comp measurable_snd)
  unfold physReadTime contTime
  exact ht.add (ENNReal.measurable_toNNReal.comp (measurable_const.min
    (hl.sub (measurable_coe_nnreal_ennreal.comp ht))))

/-- The record reader: the first path's recorded history read at `physReadTime r`. -/
def physPointOf (r : ℝ≥0) (y : (KHist × KHist) × (KHist × KHist)) : ℂ :=
  recon y.2.1.1 (physReadTime r y)

theorem measurable_physPointOf (r : ℝ≥0) : Measurable (physPointOf r) := by
  have h1 : Measurable fun y : (KHist × KHist) × (KHist × KHist) => y.2.1.1 :=
    measurable_fst.comp (measurable_fst.comp measurable_snd)
  have hp : Measurable fun y : (KHist × KHist) × (KHist × KHist) => (y.2.1.1, physReadTime r y) :=
    h1.prodMk (measurable_physReadTime r)
  have h := measurable_recon_uncurry.comp hp
  exact h

variable {Ω : Type*} [mΩ : MeasurableSpace Ω]

/-- The first path at the clamped continuation time `contTime s₀ ζ₁ r`, read from the physical record at `t`. -/
def physPoint (d : PairData Ω) (t r : ℝ≥0) (ω : Ω) : ℂ :=
  physPointOf r (fcPhysicalRecord d t ω)

omit mΩ in
theorem measurable_physPoint_comap (d : PairData Ω) (t r : ℝ≥0) :
    Measurable[MeasurableSpace.comap (fcPhysicalRecord d t) inferInstance] (physPoint d t r) := by
  have h := (measurable_physPointOf r).comp (comap_measurable (fcPhysicalRecord d t))
  exact h

theorem comap_fcPhysicalRecord_le {d : PairData Ω} (hd : d.IsMeasGood) (P : Measure Ω) (t : ℝ≥0) :
    MeasurableSpace.comap (fcPhysicalRecord d t) inferInstance ≤ fcPhysicalFiltration P d t :=
  le_inf (measurable_fcPhysicalRecord hd t).comap_le (le_aeSigma _ P)

theorem measurable_physPoint {d : PairData Ω} (hd : d.IsMeasGood) (P : Measure Ω) (t r : ℝ≥0) :
    Measurable[fcPhysicalFiltration P d t] (physPoint d t r) :=
  (measurable_physPoint_comap d t r).mono (comap_fcPhysicalRecord_le hd P t) le_rfl

omit mΩ in
/-- On the contact event, for `r ≤ t`, the record reads the first path at the clamped continuation time. -/
theorem physPoint_eq {d : PairData Ω} {ω : Ω} (hE : ω ∈ d.E)
    (hc : ContinuousOn (d.η₁ ω) {s | (s : ℝ≥0∞) ≤ d.ζ₁ ω}) (hs : (d.s₀ ω : ℝ≥0∞) ≤ d.ζ₁ ω)
    {t r : ℝ≥0} (hrt : r ≤ t) :
    physPoint d t r ω = d.η₁ ω (contTime (d.s₀ ω) (d.ζ₁ ω) r) := by
  have hτ : fcTime₁ d ω = (d.s₀ ω : ℝ≥0∞) := by simp [fcTime₁, hE]
  have hT : (fcPhysicalRecord d t ω).1.1.1.1.toNNReal = d.s₀ ω := by
    change (fcTime₁ d ω).toNNReal = d.s₀ ω
    rw [hτ, ENNReal.toNNReal_coe]
  have hL : (fcPhysicalRecord d t ω).2.1.2 = lifeRec (d.ζ₁ ω) ((d.s₀ ω : ℝ≥0∞) + t) := by
    change lifeRec (d.ζ₁ ω) (fcTime₁ d ω + t) = _
    rw [hτ]
  have hread : physReadTime r (fcPhysicalRecord d t ω) = contTime (d.s₀ ω) (d.ζ₁ ω) r := by
    unfold physReadTime
    rw [hT, hL]
    unfold contTime lifeRec
    congr 2
    split_ifs with hζ
    · rfl
    · have hlt : ((t : ℝ≥0∞)) < d.ζ₁ ω - d.s₀ ω := by
        rw [lt_tsub_iff_left]
        exact lt_of_not_ge hζ
      rw [ENNReal.top_sub_coe, min_eq_left (le_top : (r : ℝ≥0∞) ≤ ⊤),
        min_eq_left ((ENNReal.coe_le_coe.2 hrt).trans hlt.le)]
  have hle : (contTime (d.s₀ ω) (d.ζ₁ ω) r : ℝ≥0∞) ≤ (d.s₀ ω : ℝ≥0∞) + t := by
    rw [contTime_eq_clamp, ENNReal.coe_add]
    refine add_le_add le_rfl ?_
    refine (ENNReal.coe_le_coe.2 ?_)
    exact ((ENNReal.toNNReal_mono ENNReal.coe_ne_top (min_le_left _ _)).trans_eq
      (ENNReal.toNNReal_coe r)).trans hrt
  change recon (histOf (pathCoord (d.η₁ ω)) (fcTime₁ d ω + t)) (physReadTime r (fcPhysicalRecord d t ω)) = _
  rw [hread, hτ]
  exact recon_histOf hc (contTime_le hs r) hle

end Read

/-! ### The chart path read from the physical record -/

section Chart

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} {d : PairData Ω}

omit mΩ in
/-- On the good event, the forward maps of `stopData d` and `d` agree. -/
theorem fwd_stopData_eq [MeasurableSpace Ω] (hd : d.IsMeasGood) {ω : Ω} (hE : ω ∈ d.E) :
    (stopData d).fwd ω = d.fwd ω := by
  have hG : ω ∈ d.G := hE.1
  have h := chart_stopData_eq hd hG
  rw [PairData.chart_of_mem ((stopData_E_iff hd hG).2 hE), PairData.chart_of_mem hE] at h
  exact congrArg Prod.fst h

open scoped Classical in
/-- **The chart path of the first continuation is read from the physical record.** For `r ≤ t` the chart path at
time `r` is measurable for the completed physical record at `t`: its forward chart is read from the retained
histories (`stopData`), the continuation point from the recorded history of the first path. -/
theorem measurable_cPath_fcPhysical (hd : d.IsMeasGood) (hG : ∀ᵐ ω ∂P, ω ∈ d.G) {E : Set Ω}
    (hs : IsContSpec d E d.s₀ d.η₁ d.ζ₁) (hE : MeasurableSet[retSigma d P] E) {t r : ℝ≥0} (hrt : r ≤ t) :
    Measurable[fcPhysicalFiltration P d t] (fun ω => cPath d E d.s₀ d.η₁ d.ζ₁ ω r) := by
  have hR : retSigma d P ≤ fcPhysicalFiltration P d t := retSigma_le_fcPhysicalFiltration P d t
  have hdS := hd.isMeasGood_stopData hG
  have hDS : ∀ z, MeasurableSet[retSigma d P] {ω | z ∈ (stopData d).D ω} := fun z =>
    @PairData.IsMeasGood.measurableSet_mem_D Ω (retSigma d P) (stopData d) hdS z
  have hgS : ∀ z, Measurable[retSigma d P] ({ω | z ∈ (stopData d).D ω}.indicator fun ω => (stopData d).g ω z) :=
    fun z => @PairData.IsMeasGood.measurable_indicator_g Ω (retSigma d P) (stopData d) hdS z
  have hsS : Measurable[retSigma d P] (stopData d).shift :=
    @PairData.IsMeasGood.measurable_shift Ω (retSigma d P) (stopData d) hdS
  have hEℋ : MeasurableSet[fcPhysicalFiltration P d t] E := hR _ hE
  let D' : Ω → Set ℂ := fun ω => if ω ∈ E then (stopData d).D ω else H
  let f' : Ω → ℂ → ℂ := fun ω => if ω ∈ E then (stopData d).fwd ω else id
  let q' : Ω → ℂ := fun ω => if ω ∈ E then physPoint d t r ω else 0
  have hDo : ∀ ω, IsOpen (D' ω) := fun ω => by
    simp only [D']
    split_ifs
    · exact @PairData.IsMeasGood.isOpen_D Ω (retSigma d P) (stopData d) hdS ω
    · exact QuantumZipper.isOpen_H
  have hDm : ∀ z, MeasurableSet[fcPhysicalFiltration P d t] {ω | z ∈ D' ω} := fun z => by
    have he : {ω | z ∈ D' ω} = (E ∩ {ω | z ∈ (stopData d).D ω}) ∪ (Eᶜ ∩ {_ω | z ∈ H}) := by
      ext ω
      by_cases hω : ω ∈ E <;> simp [D', hω]
    rw [he]
    exact (hEℋ.inter (hR _ (hDS z))).union
      (hEℋ.compl.inter (MeasurableSet.const _))
  have hfm : ∀ z, Measurable[fcPhysicalFiltration P d t]
      ({ω | z ∈ D' ω}.indicator fun ω => f' ω z) := fun z => by
    have hfwd : Measurable[retSigma d P]
        ({ω | z ∈ (stopData d).D ω}.indicator fun ω => (stopData d).fwd ω z) := by
      have he : ({ω | z ∈ (stopData d).D ω}.indicator fun ω => (stopData d).fwd ω z) =
          ({ω | z ∈ (stopData d).D ω}.indicator fun ω => (stopData d).g ω z) -
            {ω | z ∈ (stopData d).D ω}.indicator (stopData d).shift := by
        funext ω
        by_cases hω : z ∈ (stopData d).D ω <;> simp [Set.indicator, hω, PairData.fwd]
      rw [he]
      exact (hgS z).sub (hsS.indicator (hDS z))
    have he : ({ω | z ∈ D' ω}.indicator fun ω => f' ω z) =
        E.piecewise ({ω | z ∈ (stopData d).D ω}.indicator fun ω => (stopData d).fwd ω z)
          (fun _ => if z ∈ H then z else 0) := by
      funext ω
      by_cases hω : ω ∈ E <;> by_cases hz : z ∈ H <;>
        simp [Set.indicator, Set.piecewise, D', f', hω, hz]
    rw [he]
    exact (hfwd.mono hR le_rfl).piecewise hEℋ measurable_const
  have hq : Measurable[fcPhysicalFiltration P d t] q' :=
    Measurable.ite hEℋ (measurable_physPoint hd P t r) measurable_const
  have hpt : ∀ ω ∈ E, physPoint d t r ω = d.η₁ ω (contTime (d.s₀ ω) (d.ζ₁ ω) r) := fun ω hω =>
    physPoint_eq (hs.subset hω) (hs.cont ω hω) (hs.lt ω hω).le hrt
  have hqD : ∀ ω, q' ω ∈ closure (D' ω) := fun ω => by
    by_cases hω : ω ∈ E
    · simp only [q', D', hω, ite_true]
      rw [hpt ω hω, D_stopData_eq hd (hs.subset hω).1]
      exact hs.mem ω hω _ (le_contTime _ _ r) (contTime_le (hs.lt ω hω).le r)
    · simp only [q', D', hω, ite_false]
      rw [closure_H]
      show (0 : ℂ).im ≥ 0
      simp
  have hlim : ∀ ω, Tendsto (f' ω) (𝓝[D' ω] (q' ω)) (𝓝 (cPath d E d.s₀ d.η₁ d.ζ₁ ω r)) := fun ω => by
    by_cases hω : ω ∈ E
    · simp only [f', D', q', hω, ite_true]
      rw [hpt ω hω, D_stopData_eq hd (hs.subset hω).1, fwd_stopData_eq hd (hs.subset hω)]
      exact (hs.cPath_spec hω r).2.1
    · simp only [f', D', q', hω, ite_false, cPath]
      exact tendsto_id.mono_left nhdsWithin_le_nhds
  exact @measurable_of_tendsto_nhdsWithin Ω (fcPhysicalFiltration P d t) D' f' q'
    (fun ω => cPath d E d.s₀ d.η₁ d.ζ₁ ω r) hDo hDm hfm hq hqD hlim

end Chart

/-! ### The capacity clock and the driver on the clock cuts -/

section Clock

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} {d : PairData Ω}

/-- The completed physical record contains the null sets. -/
theorem nullSets_le_fcPhysicalFiltration (P : Measure Ω) (d : PairData Ω) (t : ℝ≥0) :
    Ito.nullSets P ≤ fcPhysicalFiltration P d t := by
  refine MeasurableSpace.generateFrom_le fun N hN =>
    ⟨hN.1, ∅, @MeasurableSet.empty Ω (MeasurableSpace.comap (fcPhysicalRecord d t) inferInstance), ?_⟩
  exact ae_eq_empty.2 hN.2

/-- A measurable set agreeing almost surely with a physical event is a physical event. -/
theorem measurableSet_fcPhysical_of_ae_eq {t : ℝ≥0} {A B : Set Ω} (hA : MeasurableSet A)
    (hB : MeasurableSet[fcPhysicalFiltration P d t] B) (h : A =ᵐ[P] B) :
    MeasurableSet[fcPhysicalFiltration P d t] A := by
  obtain ⟨G', hG', he⟩ := hB.2
  exact ⟨hA, G', hG', h.trans he⟩

omit mΩ in
/-- The concrete clock never exceeds the capacity lifetime of the continuation. -/
theorem coe_fcCapacityClock_le_cLife [MeasurableSpace Ω] (hd : d.IsMeasGood) {E : Set Ω}
    (hs : IsContSpec d E d.s₀ d.η₁ d.ζ₁)
    (hclk : ∀ ω ∈ E, IsClockOn (chartClock (cPath d E d.s₀ d.η₁ d.ζ₁ ω)) (d.ζ₁ ω - d.s₀ ω))
    {ω : Ω} (hω : ω ∈ E) (t : ℝ≥0) :
    (fcCapacityClock d E t ω : ℝ≥0∞) ≤ cLife d E d.s₀ d.η₁ d.ζ₁ ω := by
  have hclamp : chartClock (cPath d E d.s₀ d.η₁ d.ζ₁ ω) t =
      chartClock (cPath d E d.s₀ d.η₁ d.ζ₁ ω) (min (t : ℝ≥0∞) (d.ζ₁ ω - d.s₀ ω)).toNNReal := by
    unfold chartClock
    rw [IsContSpec.image_cPath_clamp hω t]
  have hQ : fcCapacityClock d E t ω = (chartClock (cPath d E d.s₀ d.η₁ d.ζ₁ ω) t).toNNReal := by
    unfold fcCapacityClock
    rw [hs.cClock_eq hd hω]
  have hL : cLife d E d.s₀ d.η₁ d.ζ₁ ω =
      capLife (chartClock (cPath d E d.s₀ d.η₁ d.ζ₁ ω)) (d.ζ₁ ω - d.s₀ ω) := by
    rw [cLife, ite_eq_left hω, hs.cClock_eq hd hω]
  rw [hQ, hL, hclamp]
  exact (hclk ω hω).coe_toNNReal_le_capLife (min_le_sub (d.s₀ ω) (d.ζ₁ ω) t)

/-- **The capacity clock is adapted to the physical record.** -/
theorem measurable_fcCapacityClock_fcPhysical (hd : d.IsMeasGood) (hG : ∀ᵐ ω ∂P, ω ∈ d.G) {E : Set Ω}
    (hs : IsContSpec d E d.s₀ d.η₁ d.ζ₁) (hE : MeasurableSet[retSigma d P] E) (t : ℝ≥0) :
    Measurable[fcPhysicalFiltration P d t] (fcCapacityClock d E t) :=
  measurable_fcCapacityClock_of_prefix (retSigma_le_fcPhysicalFiltration P d t _ hE) t
    (@RetAux79.measurable_image_Icc_of_prefix Ω (fcPhysicalFiltration P d t) _ t
      (hs.continuous_cPath hd) fun _ hst => measurable_cPath_fcPhysical hd hG hs hE hst)

open scoped Classical in
/-- The physical time at which the capacity `min u (Qc t)` is reached (`0` off `E`). -/
def fcInvTime (d : PairData Ω) (E : Set Ω) (t u : ℝ≥0) (ω : Ω) : ℝ≥0 :=
  if ω ∈ E then invClock (cClock d E d.s₀ d.η₁ d.ζ₁ ω) (d.ζ₁ ω - d.s₀ ω)
    (min u (fcCapacityClock d E t ω)) else 0

omit mΩ in
theorem fcInvTime_le_iff [MeasurableSpace Ω] (hd : d.IsMeasGood) {E : Set Ω}
    (hs : IsContSpec d E d.s₀ d.η₁ d.ζ₁)
    (hclk : ∀ ω ∈ E, IsClockOn (chartClock (cPath d E d.s₀ d.η₁ d.ζ₁ ω)) (d.ζ₁ ω - d.s₀ ω))
    {ω : Ω} (hω : ω ∈ E) (t u s : ℝ≥0) :
    fcInvTime d E t u ω ≤ s ↔ min u (fcCapacityClock d E t ω) ≤ fcCapacityClock d E s ω := by
  simp only [fcInvTime, hω, ite_true]
  exact fcCapacityClock_inverse_cut hd hs hclk hω
    ((ENNReal.coe_le_coe.2 (min_le_right _ _)).trans (coe_fcCapacityClock_le_cLife hd hs hclk hω t)) s

/-- **The inverse clock below the current clock value is a physical variable.** -/
theorem measurable_fcInvTime (hd : d.IsMeasGood) (hG : ∀ᵐ ω ∂P, ω ∈ d.G) {E : Set Ω}
    (hs : IsContSpec d E d.s₀ d.η₁ d.ζ₁)
    (hclk : ∀ ω ∈ E, IsClockOn (chartClock (cPath d E d.s₀ d.η₁ d.ζ₁ ω)) (d.ζ₁ ω - d.s₀ ω))
    (hE : MeasurableSet[retSigma d P] E) (t u : ℝ≥0) :
    Measurable[fcPhysicalFiltration P d t] (fcInvTime d E t u) := by
  have hEt : MeasurableSet[fcPhysicalFiltration P d t] E := retSigma_le_fcPhysicalFiltration P d t _ hE
  have hQ : ∀ s ≤ t, Measurable[fcPhysicalFiltration P d t] (fcCapacityClock d E s) := fun s hst =>
    (measurable_fcCapacityClock_fcPhysical hd hG hs hE s).mono
      ((fcPhysicalFiltration P d).mono hst) le_rfl
  refine measurable_of_Iic (mδ := fcPhysicalFiltration P d t) fun s => ?_
  by_cases hts : t ≤ s
  · have he : fcInvTime d E t u ⁻¹' Iic s = univ := by
      ext ω
      simp only [mem_preimage, mem_Iic, mem_univ, iff_true]
      by_cases hω : ω ∈ E
      · rw [fcInvTime_le_iff hd hs hclk hω t u s]
        exact (min_le_right _ _).trans (monotone_fcCapacityClock hd hs hclk ω hts)
      · simp only [fcInvTime, hω, ite_false, zero_le]
    rw [he]
    exact MeasurableSet.univ
  · have he : fcInvTime d E t u ⁻¹' Iic s =
        (E ∩ {ω | min u (fcCapacityClock d E t ω) ≤ fcCapacityClock d E s ω}) ∪ Eᶜ := by
      ext ω
      simp only [mem_preimage, mem_Iic, mem_union, mem_inter_iff, mem_ofPred_eq, mem_compl_iff]
      by_cases hω : ω ∈ E
      · simp only [hω, true_and, not_true_eq_false, or_false]
        exact fcInvTime_le_iff hd hs hclk hω t u s
      · simp only [fcInvTime, hω, ite_false, zero_le, false_and, not_false_eq_true, or_true]
    rw [he]
    exact (hEt.inter (measurableSet_le ((measurable_const (a := u)).min (hQ t le_rfl))
      (hQ s (le_of_lt (lt_of_not_ge hts))))).union hEt.compl

/-- The canonical chart path frozen at the current clock value. -/
def fcFrozenTrace (d : PairData Ω) (E : Set Ω) (t : ℝ≥0) (ω : Ω) (u : ℝ≥0) : ℂ :=
  cGamma d E d.s₀ d.η₁ d.ζ₁ ω (min u (fcCapacityClock d E t ω))

end Clock

section Obs

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} {d : PairData Ω} {E : Set Ω}

omit mΩ in
theorem fcFrozenTrace_eq [MeasurableSpace Ω] (hd : d.IsMeasGood) (hs : IsContSpec d E d.s₀ d.η₁ d.ζ₁)
    (hclk : ∀ ω ∈ E, IsClockOn (chartClock (cPath d E d.s₀ d.η₁ d.ζ₁ ω)) (d.ζ₁ ω - d.s₀ ω))
    {ω : Ω} (hω : ω ∈ E) (t u : ℝ≥0) :
    fcFrozenTrace d E t ω u = cPath d E d.s₀ d.η₁ d.ζ₁ ω (min (fcInvTime d E t u ω) t) := by
  have hle : fcInvTime d E t u ω ≤ t := (fcInvTime_le_iff hd hs hclk hω t u t).2 (min_le_right _ _)
  rw [min_eq_left hle]
  simp only [fcFrozenTrace, fcInvTime, cGamma, hω, ite_true]

omit mΩ in
theorem fcFrozenTrace_of_notMem {ω : Ω} (hω : ω ∉ E) (t u : ℝ≥0) : fcFrozenTrace d E t ω u = 0 := by
  simp only [fcFrozenTrace, cGamma, hω, ite_false]

omit mΩ in
theorem continuous_fcFrozenTrace [MeasurableSpace Ω] (hd : d.IsMeasGood) (hs : IsContSpec d E d.s₀ d.η₁ d.ζ₁)
    (hclk : ∀ ω ∈ E, IsClockOn (chartClock (cPath d E d.s₀ d.η₁ d.ζ₁ ω)) (d.ζ₁ ω - d.s₀ ω))
    (t : ℝ≥0) (ω : Ω) : Continuous (fcFrozenTrace d E t ω) := by
  by_cases hω : ω ∈ E
  · have hco := (hs.clockData hd hclk).2.2.1 ω
    exact hco.comp_continuous (continuous_id.min continuous_const) fun u =>
      (ENNReal.coe_le_coe.2 (min_le_right _ _)).trans (coe_fcCapacityClock_le_cLife hd hs hclk hω t)
  · have he : fcFrozenTrace d E t ω = fun _ => 0 := funext fun u => fcFrozenTrace_of_notMem hω t u
    rw [he]
    exact continuous_const

omit mΩ in
theorem fcFrozenTrace_zero [MeasurableSpace Ω] (hd : d.IsMeasGood) (hs : IsContSpec d E d.s₀ d.η₁ d.ζ₁)
    (hclk : ∀ ω ∈ E, IsClockOn (chartClock (cPath d E d.s₀ d.η₁ d.ζ₁ ω)) (d.ζ₁ ω - d.s₀ ω))
    (t : ℝ≥0) (ω : Ω) : fcFrozenTrace d E t ω 0 = 0 := by
  by_cases hω : ω ∈ E
  · have hc : IsClockOn (cClock d E d.s₀ d.η₁ d.ζ₁ ω) (d.ζ₁ ω - d.s₀ ω) := by
      rw [hs.cClock_eq hd hω]
      exact hclk ω hω
    simp only [fcFrozenTrace, cGamma, hω, ite_true, zero_min, RetAux79.invClock_zero hc]
    exact hs.cPath_zero hω
  · exact fcFrozenTrace_of_notMem hω t 0

/-- The frozen canonical chart path is a physical variable at every capacity. -/
theorem measurable_fcFrozenTrace (hd : d.IsMeasGood) (hG : ∀ᵐ ω ∂P, ω ∈ d.G)
    (hs : IsContSpec d E d.s₀ d.η₁ d.ζ₁)
    (hclk : ∀ ω ∈ E, IsClockOn (chartClock (cPath d E d.s₀ d.η₁ d.ζ₁ ω)) (d.ζ₁ ω - d.s₀ ω))
    (hE : MeasurableSet[retSigma d P] E) (t u : ℝ≥0) :
    Measurable[fcPhysicalFiltration P d t] (fun ω => fcFrozenTrace d E t ω u) := by
  classical
  have hEt : MeasurableSet[fcPhysicalFiltration P d t] E := retSigma_le_fcPhysicalFiltration P d t _ hE
  have hpath : ∀ s, Measurable[fcPhysicalFiltration P d t]
      fun ω => cPath d E d.s₀ d.η₁ d.ζ₁ ω (min s t) := fun s =>
    measurable_cPath_fcPhysical hd hG hs hE (min_le_right s t)
  have hcont : ∀ ω, Continuous fun s => cPath d E d.s₀ d.η₁ d.ζ₁ ω (min s t) := fun ω =>
    (hs.continuous_cPath hd ω).comp (continuous_id.min continuous_const)
  have hev := @RetAux79.measurable_eval_of_continuous_coordinates Ω (fcPhysicalFiltration P d t)
    (fun ω s => cPath d E d.s₀ d.η₁ d.ζ₁ ω (min s t)) hcont hpath _
    (measurable_fcInvTime hd hG hs hclk hE t u)
  have he : (fun ω => fcFrozenTrace d E t ω u) =
      E.piecewise (fun ω => cPath d E d.s₀ d.η₁ d.ζ₁ ω (min (fcInvTime d E t u ω) t)) fun _ => 0 := by
    funext ω
    by_cases hω : ω ∈ E
    · rw [Set.piecewise_eq_of_mem _ _ _ hω, fcFrozenTrace_eq hd hs hclk hω]
    · rw [Set.piecewise_eq_of_notMem _ _ _ hω, fcFrozenTrace_of_notMem hω]
  rw [he]
  exact hev.piecewise hEt measurable_const

/-- **The driver is observed on the clock cuts of the physical record** (FCKER2's `hobs`). Let `W` be a continuous
measurable driver from `0` that generates, almost surely on `E`, a path `γ` which agrees with the canonical chart
path `cGamma` up to its lifetime `U = cLife`. Then `1_{r ≤ Qc t} W_r` is a physical variable at `t`. -/
theorem measurable_indicator_driver_fcPhysical (hd : d.IsMeasGood) (hG : ∀ᵐ ω ∂P, ω ∈ d.G)
    (hs : IsContSpec d E d.s₀ d.η₁ d.ζ₁)
    (hclk : ∀ ω ∈ E, IsClockOn (chartClock (cPath d E d.s₀ d.η₁ d.ζ₁ ω)) (d.ζ₁ ω - d.s₀ ω))
    (hE : MeasurableSet[retSigma d P] E) {γ : Ω → ℝ≥0 → ℂ} {U : Ω → ℝ≥0∞} {W : ℝ≥0 → Ω → ℝ}
    (hWm : ∀ r, Measurable (W r)) (hWc : ∀ ω, Continuous (W · ω)) (hW0 : ∀ ω, W 0 ω = 0)
    (hgen : ∀ᵐ ω ∂P, ω ∈ E → IsGeneratingTrace (W · ω) (U ω) (γ ω))
    (hcan : ∀ᵐ ω ∂P, ω ∈ E → (∀ q : ℝ≥0, (q : ℝ≥0∞) ≤ U ω → γ ω q = cGamma d E d.s₀ d.η₁ d.ζ₁ ω q) ∧
      U ω = cLife d E d.s₀ d.η₁ d.ζ₁ ω)
    (r t : ℝ≥0) :
    Measurable[fcPhysicalFiltration P d t] ({ω | r ≤ fcCapacityClock d E t ω}.indicator (W r)) := by
  have hle : fcPhysicalFiltration P d t ≤ mΩ := (fcPhysicalFiltration P d).le t
  have hnull := nullSets_le_fcPhysicalFiltration P d t
  have hQ := measurable_fcCapacityClock_fcPhysical hd hG hs hE t
  have hc : Measurable[fcPhysicalFiltration P d t] fun ω => (fcCapacityClock d E t ω : ℝ≥0∞) :=
    hQ.coe_nnreal_ennreal
  have hY : ∀ u, Measurable[fcPhysicalFiltration P d t] (fcReadDriver (fcFrozenTrace d E t) u) := fun u =>
    @measurable_fcReadDriver Ω (fcPhysicalFiltration P d t) (fcFrozenTrace d E t)
      (continuous_fcFrozenTrace hd hs hclk t) (fun v => measurable_fcFrozenTrace hd hG hs hclk hE t v)
      (fcFrozenTrace_zero hd hs hclk t) u
  have hRY : ∀ᵐ ω ∂P, ∀ u : ℝ≥0, (u : ℝ≥0∞) < (fcCapacityClock d E t ω : ℝ≥0∞) →
      W u ω = fcReadDriver (fcFrozenTrace d E t) u ω := by
    filter_upwards [hgen, hcan] with ω hg hc' u hu
    by_cases hω : ω ∈ E
    · obtain ⟨hγ, hU⟩ := hc' hω
      have hQU : (fcCapacityClock d E t ω : ℝ≥0∞) ≤ U ω :=
        hU ▸ coe_fcCapacityClock_le_cLife hd hs hclk hω t
      have hgt : IsGeneratingTrace (W · ω) (fcCapacityClock d E t ω) (fcFrozenTrace d E t ω) := by
        refine ⟨fcFrozenTrace_zero hd hs hclk t ω, (continuous_fcFrozenTrace hd hs hclk t ω).continuousOn,
          fun s hsQ => ?_⟩
        have himg : fcFrozenTrace d E t ω '' Icc 0 s = γ ω '' Icc 0 s := by
          refine image_congr fun v hv => ?_
          have hvQ : v ≤ fcCapacityClock d E t ω := hv.2.trans (ENNReal.coe_lt_coe.1 hsQ).le
          simp only [fcFrozenTrace, min_eq_left hvQ]
          exact (hγ v ((ENNReal.coe_le_coe.2 hvQ).trans hQU)).symm
        rw [himg]
        exact (hg hω).2.2 s (hsQ.trans_le hQU)
      exact (fcReadDriver_eq (hWc ω) (hW0 ω) hgt hu).symm
    · have h0 : fcCapacityClock d E t ω = 0 := by simp [fcCapacityClock, cClock, hω]
      rw [h0] at hu
      exact absurd hu (not_lt.2 zero_le)
  intro B hB
  have hset := Supp8.RelSafe.measurableSet_le_inter_of_lt hle hnull hWm hWc hW0 hc hY hRY r hB
  have he : {ω | (r : ℝ≥0∞) ≤ (fcCapacityClock d E t ω : ℝ≥0∞)} = {ω | r ≤ fcCapacityClock d E t ω} := by
    ext ω
    simp only [mem_ofPred_eq, ENNReal.coe_le_coe]
  rw [he] at hset
  have hL : MeasurableSet[fcPhysicalFiltration P d t] {ω | r ≤ fcCapacityClock d E t ω} :=
    measurableSet_le measurable_const hQ
  have hpre : ({ω | r ≤ fcCapacityClock d E t ω}.indicator (W r)) ⁻¹' B =
      ({ω | r ≤ fcCapacityClock d E t ω} ∩ W r ⁻¹' B) ∪
        ({ω | r ≤ fcCapacityClock d E t ω}ᶜ ∩ {_ω | (0 : ℝ) ∈ B}) := by
    ext ω
    by_cases h : r ≤ fcCapacityClock d E t ω <;> simp [Set.indicator, h]
  rw [hpre]
  exact hset.union (hL.compl.inter (MeasurableSet.const _))

end Obs

/-! ### The canonical continuation event -/

section Event

/-- **The canonical continuation event.** A retained-measurable part of the meeting branch, of full measure in it, on
which both continuations have their chart-path specifications and strictly increasing capacity clocks (the
construction of `ae_exists_drivers_canonClock`, exported). -/
theorem exists_fcContEvent {Ω : Type u} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    (h77 : Supp10.Lemma77Statement.{u}) {κ : ℝ} (hκ : 0 < κ) (hκ4 : κ < 4)
    {b : ℝ → ℝ} {jumps : Finset ℝ} (hb : IsPiecewiseConstantBoundaryData b jumps)
    {x₁ x₂ θ₁ θ₂ : ℝ} (hx : x₂ < x₁) (hθ : θ₁ < θ₂ + Real.pi)
    {h : Ω → DistOn upperHalfPlaneOpens} (hh : IsGFFWithBoundaryData P h b jumps)
    {η₁ η₂ : Ω → ℝ≥0 → ℂ} {ζ₁ ζ₂ : Ω → ℝ≥0∞}
    (hη₁ : IsFlowLine κ b jumps x₁ θ₁ P h η₁ ζ₁)
    (hη₂ : IsFlowLine κ b jumps x₂ θ₂ P h η₂ ζ₂)
    {d : PairData Ω} (hd : d.IsMeasGood) (hζ₁ : d.ζ₁ = ζ₁) (hζ₂ : d.ζ₂ = ζ₂)
    (hae : ∀ᵐ ω ∂P, ω ∈ d.G ∧
      (∀ s : ℝ≥0, (s : ℝ≥0∞) ≤ ζ₁ ω → d.η₁ ω s = η₁ ω s) ∧
      ∀ s : ℝ≥0, (s : ℝ≥0∞) ≤ ζ₂ ω → d.η₂ ω s = η₂ ω s) :
    ∃ E : Set Ω, MeasurableSet[retSigma d P] E ∧ E ⊆ meetSet d ∧ (∀ᵐ ω ∂P, ω ∈ meetSet d → ω ∈ E) ∧
      IsContSpec d E d.s₀ d.η₁ d.ζ₁ ∧ IsContSpec d E d.t₀ d.η₂ d.ζ₂ ∧
      (∀ ω ∈ E, IsClockOn (chartClock (cPath d E d.s₀ d.η₁ d.ζ₁ ω)) (d.ζ₁ ω - d.s₀ ω)) ∧
      (∀ ω ∈ E, IsClockOn (chartClock (cPath d E d.t₀ d.η₂ d.ζ₂ ω)) (d.ζ₂ ω - d.t₀ ω)) := by
  classical
  have hgeo := ae_continuationGood_flowLines h77 hκ hκ4 hb hx hθ hh hη₁ hη₂ hd hζ₁ hζ₂ hae
  let Good : Set Ω := {ω | ω ∈ meetSet d →
    IsContinuationGood (d.η₁ ω) (d.ζ₁ ω) (d.s₀ ω) (d.η₂ ω) (d.ζ₂ ω) (d.t₀ ω) ∧
    IsContinuationGood (d.η₂ ω) (d.ζ₂ ω) (d.t₀ ω) (d.η₁ ω) (d.ζ₁ ω) (d.s₀ ω) ∧
    (∀ s : ℝ≥0, (s : ℝ≥0∞) < d.ζ₁ ω →
      ConformalImage.hcapSet (fillH (d.η₁ ω '' Icc 0 s)) = 2 * s) ∧
    (∀ s : ℝ≥0, (s : ℝ≥0∞) < d.ζ₂ ω →
      ConformalImage.hcapSet (fillH (d.η₂ ω '' Icc 0 s)) = 2 * s)}
  let G : Set Ω := (toMeasurable P Goodᶜ)ᶜ
  have hG : MeasurableSet G := (measurableSet_toMeasurable P _).compl
  have hGsub : G ⊆ Good := by
    intro ω hω
    by_contra hn
    exact hω (subset_toMeasurable P Goodᶜ hn)
  have hGae : ∀ᵐ ω ∂P, ω ∈ G := by
    rw [ae_iff]
    have he : {ω | ¬ ω ∈ G} = toMeasurable P Goodᶜ := by
      ext ω
      simp only [G, mem_compl_iff, not_not, mem_ofPred_eq]
    rw [he, measure_toMeasurable]
    exact ae_iff.1 hgeo
  have hGr : MeasurableSet[retSigma d P] G := by
    refine measurableSet_retSigma_iff.2 ⟨hG, univ, MeasurableSet.univ, ?_⟩
    filter_upwards [hGae] with ω hω
    simp only [hω, mem_univ]
  let E : Set Ω := G ∩ meetSet d
  have hEr : MeasurableSet[retSigma d P] E := hGr.inter (hd.measurableSet_meetSet P)
  have hE : MeasurableSet E := retSigma_le P _ hEr
  have hsub : E ⊆ d.E := fun _ hω => (mem_meetSet_iff.1 hω.2).1
  have hcg ω (hω : ω ∈ E) := hGsub hω.1 hω.2
  have hC ω (hω : ω ∈ E) := (hd.isFirstContactChart (hsub hω)).2
  have hseed ω (hω : ω ∈ E) : (d.η₁ ω 0).im = 0 ∧ (d.η₂ ω 0).im = 0 :=
    ⟨(hd.good ω (hsub hω).1).2.2.2.2.1, (hd.good ω (hsub hω).1).2.2.2.2.2.1⟩
  have hC₂ ω (hω : ω ∈ E) := (hC ω hω).swap (hd.isFirstContact (hsub hω)).2.2.1
  have hs₁ : IsContSpec d E d.s₀ d.η₁ d.ζ₁ :=
    contSpec_of_continuationGood hE hsub hd.measurable_s₀ hd.measζ₁ hd.meas₁
      (fun ω hω => (mem_meetSet_iff.1 hω.2).2.1) (fun ω hω => (hcg ω hω).1) hC
      (fun _ hω => hd.D_of_mem (hsub hω)) (fun ω hω => (hseed ω hω).2)
  have hs₂ : IsContSpec d E d.t₀ d.η₂ d.ζ₂ :=
    contSpec_of_continuationGood hE hsub hd.measurable_t₀ hd.measζ₂ hd.meas₂
      (fun ω hω => (mem_meetSet_iff.1 hω.2).2.2) (fun ω hω => (hcg ω hω).2.1) hC₂
      (fun ω hω => (hd.D_of_mem (hsub hω)).trans activeDomain_comm)
      (fun ω hω => (hseed ω hω).1)
  have hgm ω (hω : ω ∈ E) :
      IsMapOut (fillH (prefixSet (d.η₁ ω) (d.s₀ ω) (d.η₂ ω) (d.t₀ ω))) (d.g ω) := by
    have hg : IsMapOut (fillH (d.K ω)) (d.g ω) :=
      ConformalImage.isMapOut_mapOut (hd.isHPHull ω)
    rwa [PairData.K_of_mem (hsub hω)] at hg
  have hshift ω (hω : ω ∈ E) : (d.shift ω).im = 0 := by
    obtain ⟨x, hx⟩ := (hd.isFirstContactChart (hsub hω)).1
    rw [hx]
    simp
  refine ⟨E, hEr, fun _ hω => hω.2, ?_, hs₁, hs₂, fun ω hω => ?_, fun ω hω => ?_⟩
  · filter_upwards [hGae] with ω hωG hm using ⟨hωG, hm⟩
  · exact (hcg ω hω).1.isClockOn_chartClock (hC ω hω) (hgm ω hω) (fun _ => rfl)
      (hshift ω hω) (hseed ω hω).2 (hcg ω hω).2.2.1 (hs₁.lt ω hω)
      (hs₁.continuous_cPath hd ω).continuousOn (fun r _ => (hs₁.cPath_spec hω r).1)
      (fun r hr => by rw [(hs₁.cPath_spec hω r).2.2.1, contTime_of_le hr]) (hs₁.cPath_zero hω)
  · exact (hcg ω hω).2.1.isClockOn_chartClock (hC₂ ω hω)
      (by rw [prefixSet_comm]; exact hgm ω hω) (fun _ => rfl)
      (hshift ω hω) (hseed ω hω).1 (hcg ω hω).2.2.2 (hs₂.lt ω hω)
      (hs₂.continuous_cPath hd ω).continuousOn (fun r _ => (hs₂.cPath_spec hω r).1)
      (fun r hr => by rw [(hs₂.cPath_spec hω r).2.2.1, contTime_of_le hr]) (hs₂.cPath_zero hω)

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} {d : PairData Ω} {E : Set Ω}

/-- The supplied canonical first path is `cGamma` up to its lifetime, which is `cLife`, almost surely on `E`. -/
theorem ae_canon_cGamma₁ (hd : d.IsMeasGood) (hs : IsContSpec d E d.s₀ d.η₁ d.ζ₁)
    (hclk : ∀ ω ∈ E, IsClockOn (chartClock (cPath d E d.s₀ d.η₁ d.ζ₁ ω)) (d.ζ₁ ω - d.s₀ ω))
    {γ₁ γ₂ : Ω → ℝ≥0 → ℂ} {U₁ U₂ : Ω → ℝ≥0∞} (hcanon : d.IsCanonClock P γ₁ γ₂ U₁ U₂) :
    ∀ᵐ ω ∂P, ω ∈ E → (∀ q : ℝ≥0, (q : ℝ≥0∞) ≤ U₁ ω → γ₁ ω q = cGamma d E d.s₀ d.η₁ d.ζ₁ ω q) ∧
      U₁ ω = cLife d E d.s₀ d.η₁ d.ζ₁ ω := by
  filter_upwards [hcanon] with ω hc hω
  have hc₁ := (hc (hs.subset hω)).1 (hs.lt ω hω)
  have he := (hs.clockData hd hclk).2.2.2 ω hω
  have hp : cPath d E d.s₀ d.η₁ d.ζ₁ ω = cPath d univ d.s₀ d.η₁ d.ζ₁ ω :=
    funext fun r => by rw [cPath_of_mem hω, cPath_of_mem (mem_univ ω)]
  rw [hp] at he
  refine ⟨fun q hq => ?_, hc₁.2.trans he.2.symm⟩
  rw [he.1]
  exact hc₁.1 q hq

/-- The same for the second path. -/
theorem ae_canon_cGamma₂ (hd : d.IsMeasGood) (hs : IsContSpec d E d.t₀ d.η₂ d.ζ₂)
    (hclk : ∀ ω ∈ E, IsClockOn (chartClock (cPath d E d.t₀ d.η₂ d.ζ₂ ω)) (d.ζ₂ ω - d.t₀ ω))
    {γ₁ γ₂ : Ω → ℝ≥0 → ℂ} {U₁ U₂ : Ω → ℝ≥0∞} (hcanon : d.IsCanonClock P γ₁ γ₂ U₁ U₂) :
    ∀ᵐ ω ∂P, ω ∈ E → (∀ q : ℝ≥0, (q : ℝ≥0∞) ≤ U₂ ω → γ₂ ω q = cGamma d E d.t₀ d.η₂ d.ζ₂ ω q) ∧
      U₂ ω = cLife d E d.t₀ d.η₂ d.ζ₂ ω := by
  filter_upwards [hcanon] with ω hc hω
  have hc₂ := (hc (hs.subset hω)).2 (hs.lt ω hω)
  have he := (hs.clockData hd hclk).2.2.2 ω hω
  have hp : cPath d E d.t₀ d.η₂ d.ζ₂ ω = cPath d univ d.t₀ d.η₂ d.ζ₂ ω :=
    funext fun r => by rw [cPath_of_mem hω, cPath_of_mem (mem_univ ω)]
  rw [hp] at he
  refine ⟨fun q hq => ?_, hc₂.2.trans he.2.symm⟩
  rw [he.1]
  exact hc₂.1 q hq

end Event

end InteractingSLE.Restart.FCPlumb.FCKerC
