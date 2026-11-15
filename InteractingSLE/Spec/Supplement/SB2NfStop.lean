/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.SB2NdStop

/-!
# F2b′'s record-path stops over a general relative curve

Packet PROVE-AUX61-NOJUMP (round 22, the root variant). `Nd.StopIn`'s stop machinery with the stage objects replaced
by any relative curve `ρ` that is driven at every sample and measurable at every time, and a measurable good event
(**`StopG`**). At the root, `ρ` is the root's relative curve `RootObj.ρM` and the good event is the root's. Same
results as `Nd.StopIn`: the canonical driver `Wr`, the record, the stops `Vstop`, the frozen drivers `W m` and their
rule stops `V m`; **`sample`**, **`V_mono`**, **`V_sup`**, `V_eq`, `W_eq`, measurability.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal
open QuantumZipper (H)
open LQGMetric (DistOn)

universe u

namespace InteractingSLE.Theorem14.SB.Nf

open Vs Exist.StagedLaw Supp8.GB6 Supp8.GB6.HullId Supp8.GB6.RelDrv.Version Supp8.Q3Stop Sec7.PocketTraversal
  Sec7.Lemma71C Restart Exist Exist.Staged Lv Ms Mf WalkSide LocalSets Lk LuM Nc Dv Nd

variable {κ : ℝ} {Ω : Type u} [mΩ : MeasurableSpace Ω] {P : Measure Ω}

variable (P) in
/-- **General stop inputs**: a relative curve driven at every sample and measurable at every time, a measurable good
event, a measurable record word, a countable set of types, and a conull event on which the relative facts hold. -/
structure StopG (κ ψ : ℝ) where
  ρ : Ω → ℝ → ℂ
  hd : ∀ ω, IsDrivenCurve (ρ ω)
  hm : ∀ r : ℝ, 0 ≤ r → Measurable fun ω => ρ ω r
  Eg : Set Ω
  hEg : MeasurableSet Eg
  cw : Ω → BoundaryWord
  types : Set WordType
  htypes : types.Countable
  hcw : Measurable cw
  Gr : Set Ω
  hGr : MeasurableSet Gr
  hGrae : ∀ᵐ ω ∂P, ω ∈ Gr
  rel : ∀ ω ∈ Eg ∩ Gr, RelFactsAt κ ψ cw types (ρ ω) ω

namespace StopG

variable {ψ : ℝ} (T : StopG P κ ψ)

/-- The good event of the stops. -/
def Gs : Set Ω := T.Eg ∩ T.Gr

theorem measurableSet_Gs : MeasurableSet T.Gs := T.hEg.inter T.hGr

theorem Gs_subset_Eg : T.Gs ⊆ T.Eg := inter_subset_left

theorem ae_mem_Gs : ∀ᵐ ω ∂P, ω ∈ T.Eg → ω ∈ T.Gs := by
  filter_upwards [T.hGrae] with ω h2 hF using ⟨hF, h2⟩

/-- The canonical driver of the relative stage curves. -/
def Wr : ℝ≥0 → Ω → ℝ := CoordB.drivenDriver T.ρ

theorem measurable_Wr (q : ℝ≥0) : Measurable (T.Wr q) :=
  CoordB.measurable_drivenDriver T.hd (fun s hs => T.hm s hs) q

theorem continuousOn_Wr (ω : Ω) : ContinuousOn (T.Wr · ω) {t | (t : ℝ≥0∞) < capLife (T.ρ ω)} :=
  CoordB.continuousOn_drivenDriver T.hd ω

theorem Wr_zero (ω : Ω) : T.Wr 0 ω = 0 := CoordB.drivenDriver_zero T.hd ω

theorem isGeneratingTrace_Wr (ω : Ω) {V : ℝ≥0∞} (hV : V < capLife (T.ρ ω)) :
    IsGeneratingTrace (T.Wr · ω) V (capTrace (T.ρ ω)) :=
  Sec5.CrossRestart.isGeneratingTrace_congr_drive ((T.hd ω).isGeneratingTrace hV)
    fun _ ht => CoordB.drivenDriver_eq (lt_trans ht hV)

theorem measurable_path_Wr : Measurable fun ω => fun s => T.Wr s ω :=
  measurable_pi_iff.2 fun s => T.measurable_Wr s

open Classical in
/-- **The record**: the grid code of the gauge on the good event, the constant gauge off it. -/
def record (ω : Ω) : RecData := if ω ∈ T.Gs then rec2 κ ψ T.cw T.types ω else recOne

theorem record_of_mem {ω : Ω} (hω : ω ∈ T.Gs) : T.record ω = rec2 κ ψ T.cw T.types ω := by
  simp only [record, hω, ↓reduceIte]

theorem record_of_notMem {ω : Ω} (hω : ω ∉ T.Gs) : T.record ω = recOne := by
  simp only [record, hω, ↓reduceIte]

theorem measurable_record : Measurable T.record := by
  classical
  unfold record
  exact Measurable.ite T.measurableSet_Gs (measurable_rec2 κ ψ T.cw T.types T.hcw T.htypes) measurable_const

/-- The stops of the rule along the canonical driver. -/
def Vstop (m : ℕ) (ω : Ω) : ℝ≥0∞ := stopRule m (T.record ω, fun s => T.Wr s ω)

theorem measurable_Vstop (m : ℕ) : Measurable (T.Vstop m) :=
  (measurable_stopRule m).comp (T.measurable_record.prodMk T.measurable_path_Wr)

/-- The coordinate gauge of a good sample. -/
def gc (ω : Ω) : ℝ≥0 → ℝ := gco (relGauge2 κ ψ T.cw T.types ω) (capTrace (T.ρ ω)) (capLife (T.ρ ω))

theorem relGauge2_zero_pos {ω : Ω} (hω : ω ∈ T.Gs) : 0 < relGauge2 κ ψ T.cw T.types ω 0 := by
  refine lt_min (T.rel ω hω).seed ?_
  unfold Bph
  simp

theorem continuous_gc {ω : Ω} (hω : ω ∈ T.Gs) : Continuous (T.gc ω) := by
  have hR := T.rel ω hω
  refine continuous_gco_rel (continuous_relGauge2 κ ψ T.cw T.types ω) (relGauge2_le_one κ ψ T.cw T.types ω)
    (Vk.continuousOn_of_forall_lt fun V hV => T.isGeneratingTrace_Wr ω hV) fun hU => ?_
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds (hR.endF hU)
    (fun s => ENNReal.toReal_nonneg) fun s => ?_
  exact ENNReal.toReal_mono (ne_top_of_le_ne_top ENNReal.one_ne_top (relGauge_le_one κ ψ T.cw T.types ω _))
    (min_le_left _ _)

/-- **The stops along a good sample.** -/
theorem sample {ω : Ω} (hω : ω ∈ T.Gs) (m : ℕ) :
    T.Vstop m ω = localStop (T.gc ω) m ∧ (localStop (T.gc ω) m : ℝ≥0∞) < capLife (T.ρ ω) ∧
      (∀ n, annRules gaugeRead m n (T.record ω, fun s => T.Wr s ω) < T.Vstop m ω) ∧
      ⨆ n, annRules gaugeRead m n (T.record ω, fun s => T.Wr s ω) = T.Vstop m ω ∧
      ∀ t : ℝ≥0, t < localStop (T.gc ω) m → 0 < relGauge2 κ ψ T.cw T.types ω (capTrace (T.ρ ω) t) := by
  have h := sample_rules_rel (r := T.record ω) (relGauge2_le_one κ ψ T.cw T.types ω) (T.relGauge2_zero_pos hω)
    (T.hd ω) (fun V hV => T.isGeneratingTrace_Wr ω hV) (T.continuousOn_Wr ω) (T.Wr_zero ω)
    (T.continuous_gc hω) (fun z hz => by rw [T.record_of_mem hω]; exact decode_rec2 κ ψ T.cw T.types ω hz) m
  obtain ⟨h1, h2, h3, h4, h5⟩ := h
  have hV : T.Vstop m ω = localStop (T.gc ω) m := h2
  exact ⟨hV, h1, fun n => hV ▸ h3 n, hV ▸ h4, h5⟩

theorem Vstop_lt {m : ℕ} {ω : Ω} (hω : ω ∈ T.Gs) : T.Vstop m ω < capLife (T.ρ ω) := by
  rw [(T.sample hω m).1]; exact (T.sample hω m).2.1

theorem Vstop_ne_top {m : ℕ} {ω : Ω} (hω : ω ∈ T.Gs) : T.Vstop m ω ≠ ⊤ := by
  rw [(T.sample hω m).1]; exact ENNReal.coe_ne_top

theorem Vstop_pos {m : ℕ} {ω : Ω} (hω : ω ∈ T.Gs) : 0 < T.Vstop m ω := by
  rw [(T.sample hω m).1]
  have hg0 : 0 < T.gc ω 0 := by
    unfold gc
    rw [gco_of_lt (by exact_mod_cast Vk.capLife_pos (T.hd ω)), capTrace_zero (T.hd ω)]
    exact ENNReal.toReal_pos (T.relGauge2_zero_pos hω).ne'
      (ne_top_of_le_ne_top ENNReal.one_ne_top (relGauge2_le_one κ ψ T.cw T.types ω 0))
  exact_mod_cast localStop_pos (T.continuous_gc hω) hg0 m

open Classical in
/-- **The driver frozen at the `m`-th stop** (`0` off the good event). -/
def W (m : ℕ) (q : ℝ≥0) (ω : Ω) : ℝ := if ω ∈ T.Gs then T.Wr (min q (T.Vstop m ω).toNNReal) ω else 0

theorem W_of_mem {m : ℕ} {ω : Ω} (hω : ω ∈ T.Gs) (q : ℝ≥0) :
    T.W m q ω = T.Wr (min q (T.Vstop m ω).toNNReal) ω := by simp [W, hω]

theorem W_of_notMem {m : ℕ} {ω : Ω} (hω : ω ∉ T.Gs) (q : ℝ≥0) : T.W m q ω = 0 := by simp [W, hω]

theorem Vstop_toNNReal_lt {m : ℕ} {ω : Ω} (hω : ω ∈ T.Gs) :
    ((T.Vstop m ω).toNNReal : ℝ≥0∞) < capLife (T.ρ ω) := by
  rw [ENNReal.coe_toNNReal (T.Vstop_ne_top hω)]; exact T.Vstop_lt hω

theorem W_zero (m : ℕ) (ω : Ω) : T.W m 0 ω = 0 := by
  by_cases hω : ω ∈ T.Gs
  · rw [T.W_of_mem hω, zero_min, T.Wr_zero]
  · exact T.W_of_notMem hω 0

theorem continuous_W (m : ℕ) (ω : Ω) : Continuous (T.W m · ω) := by
  by_cases hω : ω ∈ T.Gs
  · have e : (T.W m · ω) = fun q => T.Wr (min q (T.Vstop m ω).toNNReal) ω := funext (T.W_of_mem hω)
    rw [e]
    exact (T.continuousOn_Wr ω).comp_continuous (continuous_id.min continuous_const)
      fun q => (ENNReal.coe_le_coe.2 (min_le_right _ _)).trans_lt (T.Vstop_toNNReal_lt hω)
  · have e : (T.W m · ω) = fun _ => 0 := funext (T.W_of_notMem hω)
    rw [e]; exact continuous_const

theorem W_eq_Wr {m : ℕ} {ω : Ω} (hω : ω ∈ T.Gs) {q : ℝ≥0} (hq : (q : ℝ≥0∞) ≤ T.Vstop m ω) :
    T.W m q ω = T.Wr q ω := by
  rw [T.W_of_mem hω, min_eq_left]
  rw [← ENNReal.coe_le_coe, ENNReal.coe_toNNReal (T.Vstop_ne_top hω)]; exact hq

/-- The rule stops of the frozen drivers. -/
def V (m : ℕ) (ω : Ω) : ℝ≥0∞ := stopRule m (T.record ω, fun s => T.W m s ω)

theorem V_eq {m : ℕ} {ω : Ω} (hω : ω ∈ T.Gs) : T.V m ω = T.Vstop m ω :=
  isPathRule_stopRule m _ _ _ fun _ hq => (T.W_eq_Wr hω hq).symm

theorem V_of_notMem {m : ℕ} {ω : Ω} (hω : ω ∉ T.Gs) : T.V m ω = ((m : ℝ≥0) + 1 : ℝ≥0) := by
  unfold V; rw [T.record_of_notMem hω]; exact stopRule_recOne m _

/-- **The stops increase at every sample.** -/
theorem V_mono (ω : Ω) : Monotone fun m => T.V m ω := by
  intro m m' hmm'
  have hc : ((m : ℝ≥0) + 1 : ℝ≥0) ≤ ((m' : ℝ≥0) + 1 : ℝ≥0) := by
    have : (m : ℝ≥0) ≤ m' := by exact_mod_cast hmm'
    exact add_le_add this le_rfl
  by_cases hω : ω ∈ T.Gs
  · simp only [T.V_eq hω, (T.sample hω _).1, localStop]
    refine ENNReal.coe_le_coe.2 (gaugeStop_mono (T.continuous_gc hω) ?_ hc)
    unfold gaugeLevel
    have h1 : ((m : ℝ) + 1) ≤ ((m' : ℝ) + 1) := by have : (m : ℝ) ≤ m' := by exact_mod_cast hmm'
                                                   linarith
    exact min_le_min le_rfl (one_div_le_one_div_of_le (by positivity) h1)
  · simp only [T.V_of_notMem hω]
    exact ENNReal.coe_le_coe.2 hc

/-- **The stops are cofinal in the relative lifetime.** -/
theorem V_sup {ω : Ω} (hω : ω ∈ T.Gs) : ⨆ m, T.V m ω = capLife (T.ρ ω) := by
  simp only [T.V_eq hω, (T.sample hω _).1]
  have hR := T.rel ω hω
  have hg0 : 0 < T.gc ω 0 := by
    unfold gc
    rw [gco_of_lt (by exact_mod_cast Vk.capLife_pos (T.hd ω)), capTrace_zero (T.hd ω)]
    exact ENNReal.toReal_pos (T.relGauge2_zero_pos hω).ne'
      (ne_top_of_le_ne_top ENNReal.one_ne_top (relGauge2_le_one κ ψ T.cw T.types ω 0))
  refine iSup_localStop_eq (T.continuous_gc hω) hg0 (fun T' hT' => gco_of_le hT'.ge) fun t ht => ?_
  unfold gc
  rw [gco_of_lt ht]
  refine ENNReal.toReal_pos (lt_min (hR.avoid t ht) ?_).ne'
    (ne_top_of_le_ne_top ENNReal.one_ne_top (relGauge2_le_one κ ψ T.cw T.types ω _))
  unfold Bph
  exact ENNReal.ofReal_pos.2 (by positivity)

theorem W_eq {m m' : ℕ} (hmm' : m ≤ m') {ω : Ω} (hω : ω ∈ T.Gs) {t : ℝ≥0} (ht : (t : ℝ≥0∞) < T.V m ω) :
    T.W m t ω = T.W m' t ω := by
  rw [T.V_eq hω] at ht
  have h' : (t : ℝ≥0∞) ≤ T.Vstop m' ω := by
    refine ht.le.trans ?_
    have := T.V_mono ω hmm'
    simp only [T.V_eq hω] at this
    exact this
  rw [T.W_eq_Wr hω ht.le, T.W_eq_Wr hω h']

theorem measurable_W (m : ℕ) (q : ℝ≥0) : Measurable (T.W m q) := by
  obtain ⟨Y, hYm, hYoff, hYon⟩ := exists_frozen_reading (𝒢 := mΩ) (Eg := T.Gs) (τ := fun _ => ⊤)
    (Wr := T.Wr) (rec := T.record) (R := stopRule m) T.measurableSet_Gs measurable_const
    (fun r => (T.measurable_Wr r).indicator (T.measurableSet_Gs.inter (measurableSet_lt measurable_const
      measurable_const))) T.measurable_record (measurable_stopRule m) (isPathRule_stopRule m)
    (U := fun ω => capLife (T.ρ ω)) (fun ω _ => T.continuousOn_Wr ω)
    (fun ω hω => T.Vstop_lt hω) (fun ω _ => T.Wr_zero ω) q
  have e : T.W m q = Y := by
    funext ω
    by_cases hω : ω ∈ T.Gs
    · rw [T.W_of_mem hω, hYon ω hω le_top]; rfl
    · rw [T.W_of_notMem hω, hYoff ω hω]
  rw [e]; exact hYm

theorem measurable_path_W (m : ℕ) : Measurable fun ω => fun s => T.W m s ω :=
  measurable_pi_iff.2 fun s => T.measurable_W m s

theorem measurable_V (m : ℕ) : Measurable (T.V m) :=
  (measurable_stopRule m).comp (T.measurable_record.prodMk (T.measurable_path_W m))

end StopG

end InteractingSLE.Theorem14.SB.Nf
