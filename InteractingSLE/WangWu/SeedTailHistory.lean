/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.WangWu.SeedTailReversal

/-!
# A measurable certificate of properness for reverse histories

Packet PROVE-WW-B27. The history space has countably many dyadic coordinates.
Uniform continuity of their driver code and the existing trace certificate allow
properness of the decoded line to pass through equality of history laws.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter Topology
open QuantumZipper (H)
open scoped NNReal ENNReal

universe u

namespace InteractingSLE.WangWu.SeedTail

open LawUnique Sec2.Assembly Sec2.Assembly2

/-- The dyadic driver coordinates of a history, in the existing path-code format. -/
def driverCode (y : HistorySpace 1 1) : PCode := fun n k => (y.2 (n, k)).1

theorem measurable_driverCode : Measurable driverCode :=
  measurable_pi_iff.2 fun n => measurable_pi_iff.2 fun k =>
    measurable_fst.comp ((measurable_pi_apply (n, k)).comp measurable_snd)

/-- The two decodings agree on uniformly continuous driver codes. -/
theorem history_driver_eq_dec {y : HistorySpace 1 1} (hc : ∀ N : ℕ, UC (driverCode y) N) :
    (pathsOfHistory y).2.1 = dec (driverCode y) := by
  funext t
  have ht : t ≤ (⌈(t : ℝ)⌉₊ : ℕ) := by exact_mod_cast Nat.le_ceil (t : ℝ)
  have h := (hc ⌈(t : ℝ)⌉₊).tendsto_flr ht
  apply Tendsto.limUnder_eq
  convert h using 1
  funext n
  simp only [driverCode, lowerDyadic, flr, mul_comm]

/-- A Borel certificate that the whole decoded reverse line is a proper arc. -/
def properHistory : Set (HistorySpace 1 1) :=
  {y | ∀ N : ℕ, UC (driverCode y) N} ∩
    {y | (pathsOfHistory y).2.1 0 = 0} ∩
    {y | ((pathsOfHistory y).2.1, (⊤ : ℝ≥0∞)) ∈ Sec7.RandRestart.traceSet} ∩
    {y | ImPosCond (histLine y)} ∩ {y | SepCond (histLine y)}

theorem measurableSet_properHistory : MeasurableSet properHistory := by
  have h1 : MeasurableSet {y : HistorySpace 1 1 | ∀ N : ℕ, UC (driverCode y) N} :=
    measurableSet_setOfPred.2 (Measurable.forall fun N : ℕ =>
      measurableSet_setOfPred.1 (measurable_driverCode (measurableSet_UC N)))
  have hw : Measurable fun y : HistorySpace 1 1 => (pathsOfHistory y).2.1 :=
    measurable_fst.comp (measurable_snd.comp measurable_pathsOfHistory)
  have h2 : MeasurableSet {y : HistorySpace 1 1 | (pathsOfHistory y).2.1 0 = 0} :=
    measurableSet_eq_fun ((measurable_pi_apply 0).comp hw) measurable_const
  have h3 : MeasurableSet {y : HistorySpace 1 1 |
      ((pathsOfHistory y).2.1, (⊤ : ℝ≥0∞)) ∈ Sec7.RandRestart.traceSet} :=
    (hw.prodMk measurable_const) Sec7.RandRestart.measurableSet_traceSet
  have h4 : MeasurableSet {y : HistorySpace 1 1 | ImPosCond (histLine y)} := by
    refine measurableSet_setOfPred.2 (Measurable.forall fun a => Measurable.forall fun b => ?_)
    refine Measurable.imp measurable_const (Measurable.imp measurable_const (Measurable.exists fun m => ?_))
    refine Measurable.forall fun p => Measurable.imp measurable_const (Measurable.imp measurable_const ?_)
    exact measurableSet_setOfPred.1
      (measurableSet_le measurable_const (Complex.measurable_im.comp (measurable_histLine _)))
  have h5 : MeasurableSet {y : HistorySpace 1 1 | SepCond (histLine y)} := by
    refine measurableSet_setOfPred.2 (Measurable.forall fun a => Measurable.forall fun b =>
      Measurable.forall fun c => Measurable.forall fun d => ?_)
    refine Measurable.imp measurable_const (Measurable.imp measurable_const (Measurable.imp measurable_const
      (Measurable.imp measurable_const (Measurable.exists fun m => ?_))))
    refine Measurable.forall fun p => Measurable.forall fun q => Measurable.imp measurable_const
      (Measurable.imp measurable_const (Measurable.imp measurable_const (Measurable.imp measurable_const ?_)))
    exact measurableSet_setOfPred.1
      (measurableSet_le measurable_const ((measurable_histLine _).sub (measurable_histLine _)).norm)
  exact (((h1.inter h2).inter h3).inter h4).inter h5

theorem isProperArc_of_mem_properHistory {y : HistorySpace 1 1} (hy : y ∈ properHistory) :
    IsProperArc (histLine y) := by
  obtain ⟨⟨⟨⟨huc, hw0⟩, htr⟩, him⟩, hsep⟩ := hy
  have hwc : Continuous (pathsOfHistory y).2.1 := by
    rw [history_driver_eq_dec huc]
    exact continuous_dec_of_uc huc
  obtain ⟨η, hη, htend⟩ := (Sec7.RandRestart.mem_traceSet_iff hwc.continuousOn hw0
    (fun _ h => absurd h (lt_irrefl _))).1 htr
  have he : histLine y = fun s : ℝ => η s.toNNReal := by
    funext s
    exact LP.traceAt_eq_of_isGeneratingTrace hη hwc.continuousOn hw0 ENNReal.coe_lt_top
  refine isProperArc_of_conds ?_ ?_ hsep him ?_
  · rw [he]
    exact ((continuousOn_univ.1 (hη.2.1.mono fun t _ => show (t : ℝ≥0∞) ≤ ⊤ from le_top)).comp
      continuous_real_toNNReal).continuousOn
  · rw [he]
    simpa only [Real.toNNReal_zero] using hη.1
  · rw [he]
    exact (htend rfl).comp tendsto_real_toNNReal_atTop

/-- A nonnegative two-seed evolution has the Borel certificate almost surely. -/
theorem ae_killedHistory_mem_properHistory {rL rR : ℝ} (hL : 0 ≤ rL) (hR : 0 ≤ rR)
    {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    {W : ℝ≥0 → Ω → ℝ} {VL VR : Fin 1 → ℝ≥0 → Ω → ℝ} {B : ℝ≥0 → Ω → ℝ}
    {ζ : Ω → ℝ≥0∞}
    (hE : IsMarkedChain LP.twoSeedXL LP.twoSeedXR (fun _ => rL) (fun _ => rR) P 𝓕 W VL VR B ζ) :
    ∀ᵐ ω ∂P, killedHistory W VL VR ζ ω ∈ properHistory := by
  filter_upwards [hE.ae_seedLine isOrderedForceWord_twoSeed (hasNonnegCumWeights_twoSeed hL hR),
    hE.2.2.2.2] with ω hω hp
  obtain ⟨hζ, ⟨η, hη, hline⟩, -, hprop, -⟩ := hω
  have hwc : Continuous (W · ω) := continuousOn_univ.1
    (hp.2.2.2.1.mono fun t _ => by rw [hζ]; exact ENNReal.coe_lt_top)
  have hd : (pathsOfHistory (killedHistory W VL VR ζ ω)).2.1 = (W · ω) := by
    funext t
    exact pathsOfHistory_killedHistory_driver hwc.continuousOn (by rw [hζ]; exact ENNReal.coe_lt_top)
  have hl := histLine_killedHistory (VL := VL) (VR := VR) hζ hwc
  have hcode : driverCode (killedHistory W VL VR ζ ω) = enc (W · ω) := by
    funext n k
    simp only [driverCode, killedHistory, hζ, ENNReal.coe_lt_top, ↓reduceIte, enc, dyad, dyadicTime]
  refine ⟨⟨⟨⟨?_, ?_⟩, ?_⟩, ?_⟩, ?_⟩
  · change ∀ N : ℕ, UC (driverCode (killedHistory W VL VR ζ ω)) N
    rw [hcode]
    exact uc_enc_of_continuous hwc
  · change (pathsOfHistory (killedHistory W VL VR ζ ω)).2.1 0 = 0
    rw [hd]
    exact hp.1
  · change ((pathsOfHistory (killedHistory W VL VR ζ ω)).2.1, (⊤ : ℝ≥0∞)) ∈ Sec7.RandRestart.traceSet
    rw [hd]
    apply (Sec7.RandRestart.mem_traceSet_iff hwc.continuousOn hp.1
      (fun _ h => absurd h (lt_irrefl _))).2
    refine ⟨η, hη, fun _ => ?_⟩
    have ht := hprop.tendsto.comp (NNReal.tendsto_coe_atTop.2 tendsto_id)
    simpa only [hline, Function.comp_def, id_eq, Real.toNNReal_coe] using ht
  · change ImPosCond (histLine (killedHistory W VL VR ζ ω))
    rw [hl]
    exact hprop.imPosCond
  · change SepCond (histLine (killedHistory W VL VR ζ ω))
    rw [hl]
    exact hprop.sepCond

end InteractingSLE.WangWu.SeedTail
