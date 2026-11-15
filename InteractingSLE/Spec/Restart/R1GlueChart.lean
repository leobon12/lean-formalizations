/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Restart.R1GlueHist

/-!
# (R1) gluing: the first-contact chart from the stopped paths

Packet PROVE-RESTART-CPL7. Lemma 7.8 conditions on "the retained marked common-contact history. This makes `D`, its
chart, and the piecewise constant initial conditional mean fixed" (p. 294). CPL4's canonical chart `d.chart` is built
from measurable pair data `d`; here the same chart is rebuilt from the **retained histories** alone:

* `recon`: the path read from the rational coordinates of a stopped history (limit along the dyadic times below);
* `stopData d`: the pair data whose paths are read from `retHist d` and whose lifetimes are the first contact (the
  original lifetimes if the paths never meet);
* **`PairData.IsMeasGood.isMeasGood_stopData`**: `stopData d` is measurable pair data **for the retained σ-algebra**
  `retSigma d P` (given that the good event of `d` has full measure);
* **`chart_stopData_eq`**: on the good event of `d` the two charts coincide, so the canonical chart field of `d` is
  that of `stopData d` there (`chartField_stopData_eq`).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set TopologicalSpace Topology
open scoped NNReal ENNReal

namespace InteractingSLE

namespace Restart

open QuantumZipper (H)
open LQGMetric (DistOn TestOn)
open LocalSets Sec6

/-! ### Reading a path from its rational coordinates -/

/-- The rational dyadic time `2^{−n}(⌈2^n t⌉ − 1)` below `t`. -/
def qBelow (n : ℕ) (t : ℝ≥0) : ℚ≥0 := (LP.dyadicIdx n t : ℚ≥0) / 2 ^ n

theorem coe_qBelow (n : ℕ) (t : ℝ≥0) : ((qBelow n t : ℚ≥0) : ℝ≥0) = LP.dyadicBelow n t := by
  simp [qBelow, LP.dyadicBelow]

/-- **The path read from a stopped history**: the limit of the recorded coordinates along the dyadic times below `t`. -/
def recon (y : Hist) (t : ℝ≥0) : ℂ := limUnder atTop fun n => y.2 (qBelow n t)

theorem measurable_recon (t : ℝ≥0) : Measurable fun y : Hist => recon y t := by
  unfold recon
  exact (StronglyMeasurable.limUnder fun n =>
    ((measurable_pi_apply (qBelow n t)).comp measurable_snd).stronglyMeasurable).measurable

/-- The path read from the history of a path continuous on `[0, T']` is the path on `[0, T'] ∩ [0, T]`. -/
theorem recon_histOf {γ : ℝ≥0 → ℂ} {T T' : ℝ≥0∞} (hγ : ContinuousOn γ {s | (s : ℝ≥0∞) ≤ T'}) {t : ℝ≥0}
    (ht : (t : ℝ≥0∞) ≤ T') (htT : (t : ℝ≥0∞) ≤ T) : recon (histOf (pathCoord γ) T) t = γ t := by
  have hle : ∀ n, ((LP.dyadicBelow n t : ℝ≥0) : ℝ≥0∞) ≤ t := fun n => ENNReal.coe_le_coe.2 (dyadicBelow_le n t)
  have e : (fun n => (histOf (pathCoord γ) T).2 (qBelow n t)) = fun n => γ (LP.dyadicBelow n t) := by
    funext n
    simp only [histOf]
    rw [stopCoord_of_le (by rw [coe_qBelow]; exact (hle n).trans htT), pathCoord, coe_qBelow]
  have htend : Tendsto (fun n => LP.dyadicBelow n t) atTop (𝓝[{s : ℝ≥0 | (s : ℝ≥0∞) ≤ T'}] t) :=
    tendsto_nhdsWithin_iff.2 ⟨LP.tendsto_dyadicBelow _, Eventually.of_forall fun n => (hle n).trans ht⟩
  unfold recon
  rw [e]
  exact ((hγ t ht).tendsto.comp htend).limUnder_eq

/-! ### The stopped pair data -/

section Stop

variable {Ω : Type*} (d : PairData Ω)

/-- **The stopped pair data**: the paths read from the retained histories, with lifetimes the first-contact times
(`s₀`, `t₀` on the contact event, the original lifetimes off it). -/
def stopData : PairData Ω where
  G := d.G
  η₁ := fun ω t => recon (retHist d ω).1.1 t
  ζ₁ := fun ω => min (retHist d ω).1.1.1 (retHist d ω).1.2
  η₂ := fun ω t => recon (retHist d ω).2.1 t
  ζ₂ := fun ω => min (retHist d ω).2.1.1 (retHist d ω).2.2

variable {d}

theorem min_lifeRec_of_le {ζ T : ℝ≥0∞} (h : T ≤ ζ) : min T (lifeRec ζ T) = T := by
  unfold lifeRec
  split_ifs with hζ
  · exact min_eq_left h
  · exact min_eq_left le_top

theorem min_lifeRec_top (ζ : ℝ≥0∞) : min ⊤ (lifeRec ζ ⊤) = ζ := by
  simp [lifeRec]

theorem stopData_ζ₁_of_notMem {ω : Ω} (hω : ω ∉ d.E) : (stopData d).ζ₁ ω = d.ζ₁ ω := by
  simp only [stopData, retHist, khistOf, histOf, fcTime₁, hω, ↓reduceIte]
  exact min_lifeRec_top _

theorem stopData_ζ₂_of_notMem {ω : Ω} (hω : ω ∉ d.E) : (stopData d).ζ₂ ω = d.ζ₂ ω := by
  simp only [stopData, retHist, khistOf, histOf, fcTime₂, hω, ↓reduceIte]
  exact min_lifeRec_top _

variable [MeasurableSpace Ω] (hd : d.IsMeasGood)
include hd

theorem stopData_ζ₁_of_mem {ω : Ω} (hω : ω ∈ d.E) : (stopData d).ζ₁ ω = d.s₀ ω := by
  simp only [stopData, retHist, khistOf, histOf, fcTime₁, hω, ↓reduceIte]
  exact min_lifeRec_of_le (hd.isFirstContact hω).1

theorem stopData_ζ₂_of_mem {ω : Ω} (hω : ω ∈ d.E) : (stopData d).ζ₂ ω = d.t₀ ω := by
  simp only [stopData, retHist, khistOf, histOf, fcTime₂, hω, ↓reduceIte]
  exact min_lifeRec_of_le (hd.isFirstContact hω).2.1

theorem stopData_ζ₁_le (ω : Ω) : (stopData d).ζ₁ ω ≤ d.ζ₁ ω := by
  by_cases hE : ω ∈ d.E
  · rw [stopData_ζ₁_of_mem hd hE]; exact (hd.isFirstContact hE).1
  · rw [stopData_ζ₁_of_notMem hE]

theorem stopData_ζ₂_le (ω : Ω) : (stopData d).ζ₂ ω ≤ d.ζ₂ ω := by
  by_cases hE : ω ∈ d.E
  · rw [stopData_ζ₂_of_mem hd hE]; exact (hd.isFirstContact hE).2.1
  · rw [stopData_ζ₂_of_notMem hE]

/-- On the good event the stopped paths are the paths, on the stopped available interval. -/
theorem stopData_η₁_eq {ω : Ω} (hω : ω ∈ d.G) {t : ℝ≥0} (ht : (t : ℝ≥0∞) ≤ (stopData d).ζ₁ ω) :
    (stopData d).η₁ ω t = d.η₁ ω t := by
  have hc := (hd.good ω hω).1
  show recon (histOf (pathCoord (d.η₁ ω)) (fcTime₁ d ω)) t = d.η₁ ω t
  refine recon_histOf hc (ht.trans (stopData_ζ₁_le hd ω)) (ht.trans (min_le_left _ _))

theorem stopData_η₂_eq {ω : Ω} (hω : ω ∈ d.G) {t : ℝ≥0} (ht : (t : ℝ≥0∞) ≤ (stopData d).ζ₂ ω) :
    (stopData d).η₂ ω t = d.η₂ ω t := by
  have hc := (hd.good ω hω).2.1
  show recon (histOf (pathCoord (d.η₂ ω)) (fcTime₂ d ω)) t = d.η₂ ω t
  refine recon_histOf hc (ht.trans (stopData_ζ₂_le hd ω)) (ht.trans (min_le_left _ _))

/-- The first contact of the paths with lifetimes cut at the first contact is the first contact. -/
theorem isFirstContact_stop {ω : Ω} (hω : ω ∈ d.E) :
    IsFirstContact (d.η₁ ω) (d.s₀ ω) (d.η₂ ω) (d.t₀ ω) (d.s₀ ω) (d.t₀ ω) := by
  have h := hd.isFirstContact hω
  exact ⟨le_rfl, le_rfl, h.2.2.1, fun s t hs ht he => h.2.2.2 s t (hs.trans h.1) (ht.trans h.2.1) he⟩

/-- The good-event property of the paths with the stopped lifetimes. -/
theorem isChartGood_stop {ω : Ω} (hω : ω ∈ d.G) :
    IsChartGood (d.η₁ ω) ((stopData d).ζ₁ ω) (d.η₂ ω) ((stopData d).ζ₂ ω) := by
  by_cases hE : ω ∈ d.E
  · rw [stopData_ζ₁_of_mem hd hE, stopData_ζ₂_of_mem hd hE]
    obtain ⟨hc₁, hc₂, hH₁, hH₂, h0₁, h0₂, -⟩ := hd.good ω hω
    have h := hd.isFirstContact hE
    refine ⟨hc₁.mono fun s hs => (show (s : ℝ≥0∞) ≤ d.s₀ ω from hs).trans h.1,
      hc₂.mono fun t ht => (show (t : ℝ≥0∞) ≤ d.t₀ ω from ht).trans h.2.1,
      fun s hs => hH₁ s (hs.trans h.1), fun t ht => hH₂ t (ht.trans h.2.1), h0₁, h0₂, fun _ => ?_⟩
    exact ⟨d.s₀ ω, d.t₀ ω, isFirstContact_stop hd hE, hd.mem_closure hE⟩
  · rw [stopData_ζ₁_of_notMem hE, stopData_ζ₂_of_notMem hE]
    exact hd.good ω hω

theorem isChartGood_stopData {ω : Ω} (hω : ω ∈ d.G) :
    IsChartGood ((stopData d).η₁ ω) ((stopData d).ζ₁ ω) ((stopData d).η₂ ω) ((stopData d).ζ₂ ω) :=
  isChartGood_congr (fun _ hs => stopData_η₁_eq hd hω hs) (fun _ ht => stopData_η₂_eq hd hω ht)
    (isChartGood_stop hd hω)

omit hd in
theorem measurableSet_retSigma_iff {P : Measure Ω} {s : Set Ω} :
    MeasurableSet[retSigma d P] s ↔
      MeasurableSet s ∧ MeasurableSet[aeSigma (MeasurableSpace.comap (retHist d) inferInstance) P] s :=
  Iff.rfl

/-- **The stopped pair data are measurable for the retained σ-algebra.** -/
theorem PairData.IsMeasGood.isMeasGood_stopData {P : Measure Ω} (hG : ∀ᵐ ω ∂P, ω ∈ d.G) :
    @PairData.IsMeasGood Ω (retSigma d P) (stopData d) := by
  have hR : Measurable[retSigma d P] (retHist d) :=
    (comap_measurable (retHist d)).mono (hd.comap_retHist_le_retSigma P) le_rfl
  refine @PairData.IsMeasGood.mk Ω (retSigma d P) (stopData d) ?_ (fun t => ?_) (fun t => ?_) ?_ ?_
    (fun ω hω => isChartGood_stopData hd hω)
  · refine measurableSet_retSigma_iff.2 ⟨hd.measurableSet_G, univ, MeasurableSet.univ, ?_⟩
    exact ae_eq_univ.2 (ae_iff.1 hG)
  · let _ : MeasurableSpace Ω := retSigma d P
    exact (measurable_recon t).comp (measurable_fst.comp (measurable_fst.comp hR))
  · let _ : MeasurableSpace Ω := retSigma d P
    exact (measurable_recon t).comp (measurable_fst.comp (measurable_snd.comp hR))
  · let _ : MeasurableSpace Ω := retSigma d P
    exact ((measurable_fst.comp (measurable_fst.comp measurable_fst)).min
      (measurable_snd.comp measurable_fst)).comp hR
  · let _ : MeasurableSpace Ω := retSigma d P
    exact ((measurable_fst.comp (measurable_fst.comp measurable_snd)).min
      (measurable_snd.comp measurable_snd)).comp hR

/-! ### The chart of the stopped data -/

theorem stopData_E_iff {ω : Ω} (hω : ω ∈ d.G) : ω ∈ (stopData d).E ↔ ω ∈ d.E := by
  have ha₁ := fun (s : ℝ≥0) (hs : (s : ℝ≥0∞) ≤ (stopData d).ζ₁ ω) => stopData_η₁_eq hd hω hs
  have ha₂ := fun (t : ℝ≥0) (ht : (t : ℝ≥0∞) ≤ (stopData d).ζ₂ ω) => stopData_η₂_eq hd hω ht
  show (ω ∈ d.G ∧ HasContact ((stopData d).η₁ ω) ((stopData d).ζ₁ ω) ((stopData d).η₂ ω)
    ((stopData d).ζ₂ ω)) ↔ _
  rw [hasContact_congr ha₁ ha₂]
  constructor
  · rintro ⟨-, s, t, hs, ht, he⟩
    exact ⟨hω, s, t, hs.trans (stopData_ζ₁_le hd ω), ht.trans (stopData_ζ₂_le hd ω), he⟩
  · intro hE
    refine ⟨hω, d.s₀ ω, d.t₀ ω, ?_, ?_, (hd.isFirstContact hE).2.2.1⟩
    · rw [stopData_ζ₁_of_mem hd hE]
    · rw [stopData_ζ₂_of_mem hd hE]

theorem stopData_s₀_t₀ {ω : Ω} (hω : ω ∈ d.E) :
    (stopData d).s₀ ω = d.s₀ ω ∧ (stopData d).t₀ ω = d.t₀ ω := by
  have hG : ω ∈ d.G := hω.1
  have ha₁ := fun (s : ℝ≥0) (hs : (s : ℝ≥0∞) ≤ (stopData d).ζ₁ ω) => stopData_η₁_eq hd hG hs
  have ha₂ := fun (t : ℝ≥0) (ht : (t : ℝ≥0∞) ≤ (stopData d).ζ₂ ω) => stopData_η₂_eq hd hG ht
  have h := isFirstContact_stop hd hω
  rw [← stopData_ζ₁_of_mem hd hω, ← stopData_ζ₂_of_mem hd hω] at h
  have h' := (isFirstContact_congr ha₁ ha₂).2 h
  have := PairData.eq_of_isFirstContact (d := stopData d) hG h'
  exact ⟨this.2.1, this.2.2⟩

/-- **The stopped data have the same chart as `d` on the good event.** -/
theorem chart_stopData_eq {ω : Ω} (hω : ω ∈ d.G) : (stopData d).chart ω = d.chart ω := by
  classical
  by_cases hE : ω ∈ d.E
  · have hE' : ω ∈ (stopData d).E := (stopData_E_iff hd hω).2 hE
    obtain ⟨es, et⟩ := stopData_s₀_t₀ hd hE
    have ha₁ := fun (s : ℝ≥0) (hs : (s : ℝ≥0∞) ≤ (stopData d).ζ₁ ω) => stopData_η₁_eq hd hω hs
    have ha₂ := fun (t : ℝ≥0) (ht : (t : ℝ≥0∞) ≤ (stopData d).ζ₂ ω) => stopData_η₂_eq hd hω ht
    have hs₀ : ((d.s₀ ω : ℝ≥0) : ℝ≥0∞) ≤ (stopData d).ζ₁ ω := (stopData_ζ₁_of_mem hd hE).ge
    have ht₀ : ((d.t₀ ω : ℝ≥0) : ℝ≥0∞) ≤ (stopData d).ζ₂ ω := (stopData_ζ₂_of_mem hd hE).ge
    have hK : (stopData d).K ω = d.K ω := by
      rw [PairData.K_of_mem hE', PairData.K_of_mem hE, es, et, prefixSet_congr ha₁ ha₂ hs₀ ht₀]
    have hp : (stopData d).p ω = d.p ω := by
      rw [PairData.p_of_mem hE', PairData.p_of_mem hE, es, ha₁ _ hs₀]
    have hD : (stopData d).D ω = d.D ω := by
      show H \ fillH ((stopData d).K ω) = H \ fillH (d.K ω); rw [hK]
    have hg : (stopData d).g ω = d.g ω := by
      show ConformalImage.mapOut (fillH ((stopData d).K ω)) = ConformalImage.mapOut (fillH (d.K ω)); rw [hK]
    have hsh : (stopData d).shift ω = d.shift ω := by
      show limUnder (𝓝[(stopData d).D ω] ((stopData d).p ω)) ((stopData d).g ω) =
        limUnder (𝓝[d.D ω] (d.p ω)) (d.g ω)
      rw [hD, hp, hg]
    have hfwd : (stopData d).fwd ω = d.fwd ω := by
      funext z
      show (stopData d).g ω z - (stopData d).shift ω = d.g ω z - d.shift ω
      rw [hg, hsh]
    have hlift : (stopData d).lift ω = d.lift ω := by
      funext z
      show (canonDerivLog (fillH ((stopData d).K ω)) z).im = (canonDerivLog (fillH (d.K ω)) z).im
      rw [hK]
    have hpred : (fun ψ => IsFirstContactChart ((stopData d).η₁ ω) ((stopData d).s₀ ω) ((stopData d).η₂ ω)
        ((stopData d).t₀ ω) ((stopData d).fwd ω) ψ ((stopData d).lift ω)) =
        fun ψ => IsFirstContactChart (d.η₁ ω) (d.s₀ ω) (d.η₂ ω) (d.t₀ ω) (d.fwd ω) ψ (d.lift ω) := by
      funext ψ
      rw [es, et, hfwd, hlift]
      exact propext (isFirstContactChart_congr ha₁ ha₂ hs₀ ht₀)
    have hinv : (stopData d).inv ω = d.inv ω := by
      unfold PairData.inv
      simp only [hpred]
    rw [PairData.chart_of_mem hE', PairData.chart_of_mem hE, hfwd, hinv, hlift]
  · have hE' : ω ∉ (stopData d).E := fun h => hE ((stopData_E_iff hd hω).1 h)
    rw [PairData.chart_of_notMem hE', PairData.chart_of_notMem hE]

theorem D_stopData_eq {ω : Ω} (hω : ω ∈ d.G) : (stopData d).D ω = d.D ω := by
  by_cases hE : ω ∈ d.E
  · have hE' : ω ∈ (stopData d).E := (stopData_E_iff hd hω).2 hE
    obtain ⟨es, et⟩ := stopData_s₀_t₀ hd hE
    have ha₁ := fun (s : ℝ≥0) (hs : (s : ℝ≥0∞) ≤ (stopData d).ζ₁ ω) => stopData_η₁_eq hd hω hs
    have ha₂ := fun (t : ℝ≥0) (ht : (t : ℝ≥0∞) ≤ (stopData d).ζ₂ ω) => stopData_η₂_eq hd hω ht
    show H \ fillH ((stopData d).K ω) = H \ fillH (d.K ω)
    rw [PairData.K_of_mem hE', PairData.K_of_mem hE, es, et,
      prefixSet_congr ha₁ ha₂ (stopData_ζ₁_of_mem hd hE).ge (stopData_ζ₂_of_mem hd hE).ge]
  · have hE' : ω ∉ (stopData d).E := fun h => hE ((stopData_E_iff hd hω).1 h)
    show H \ fillH ((stopData d).K ω) = H \ fillH (d.K ω)
    rw [PairData.K_of_notMem hE', PairData.K_of_notMem hE]

end Stop

/-- Chart transports by equal charts agree. -/
theorem chartTransport_congr_chart {c c' : Chart} (e : c = c') (hc : c.IsConformal) (hc' : c'.IsConformal)
    (σ a k : ℝ) (h : DistOn upperHalfPlaneOpens) :
    Chart.chartTransport hc σ a k h = Chart.chartTransport hc' σ a k h := by
  subst e
  rfl

/-- **The chart field of `d` is the chart field of the stopped data on the good event.** -/
theorem chartField_stopData_eq {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} {d : PairData Ω}
    (hd : d.IsMeasGood) (hG : ∀ᵐ ω ∂P, ω ∈ d.G) (κ : ℝ) (h : Ω → DistOn upperHalfPlaneOpens) {ω : Ω}
    (hω : ω ∈ d.G) :
    @PairData.IsMeasGood.chartField Ω (retSigma d P) (stopData d) (hd.isMeasGood_stopData hG) κ h ω =
      hd.chartField κ h ω :=
  chartTransport_congr_chart (chart_stopData_eq hd hω) _ _ 1 0 _ (h ω)

end Restart

end InteractingSLE
