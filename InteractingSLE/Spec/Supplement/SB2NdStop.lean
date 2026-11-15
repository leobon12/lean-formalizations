/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.SB2NdGauge
import InteractingSLE.Spec.Supplement.SB2VsMeas

/-!
# F2b′'s record-path stops

Packet PROVE-AUX61-NOJUMP (round 21, D34, component C). SB2(1)'s stop machinery (round 18, `SB2Vs*`) on F2b′'s stage
objects, with the relative-coordinate gauge `relGauge2`:

* **`RelFactsAt`**: the four facts about the relative stage curve the stops need at a sample (the type is listed, the
  seed is off the closed relative bad set, the trace avoids it before the relative lifetime and approaches it at a
  finite one); component F proves them almost surely;
* **`StopIn`**: the stage objects, a record word measurable at time `0`, and a conull event on which the facts hold;
* the canonical driver `Wr`, the record (`rec2` on the good event `Gs`, the constant gauge `recOne` off it), the
  stops `Vstop m = stopRule m (record, Wr)`, the frozen drivers `W m` and their rule stops `V m`;
* **`sample`** (positive finite stops below the relative lifetime, announced, the gauge positive before them),
  **`V_mono`** (at every sample: off `Gs` the stops are the caps `m + 1`), **`V_sup`** (cofinal in the relative
  lifetime), `V_eq`, `W_eq`, measurability.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal
open QuantumZipper (H)
open LQGMetric (DistOn)

universe u

namespace InteractingSLE.Theorem14.SB.Nd

open Vs Exist.StagedLaw Supp8.GB6 Supp8.GB6.HullId Supp8.GB6.RelDrv.Version Supp8.Q3Stop Sec7.PocketTraversal
  Sec7.Lemma71C Restart Exist Exist.Staged Lv Ms Mf WalkSide LocalSets Lk LuM Nc Dv

/-- **The facts about the relative stage curve the stops need at a sample.** -/
structure RelFactsAt {Ω : Type*} (κ ψ : ℝ) (cw : Ω → BoundaryWord) (types : Set WordType) (ρ : ℝ → ℂ) (ω : Ω) :
    Prop where
  cover : angleWordType κ ψ (cw ω) ∈ types
  seed : 0 < relGauge κ ψ cw types ω 0
  avoid : ∀ s : ℝ≥0, (s : ℝ≥0∞) < capLife ρ → 0 < relGauge κ ψ cw types ω (capTrace ρ s)
  endF : capLife ρ ≠ ⊤ →
    Tendsto (fun s => (relGauge κ ψ cw types ω (capTrace ρ s)).toReal) (𝓝[<] (capLife ρ).toNNReal) (𝓝 0)

/-- The record of the constant gauge `1`. -/
def recOne : RecData := (recFun fun _ => (1 : ℝ), 0, false)

theorem decode_recOne (z : ℂ) : decode recOne z = 1 := by
  unfold decode recOne
  have e : (fun n => (recFun fun _ => (1 : ℝ)) (gridCode (approx n z))) = fun _ => (1 : ℝ) := by
    funext n; rw [recFun_code]
  simp only
  rw [e]
  exact tendsto_const_nhds.limUnder_eq

/-- **With the constant record, the `m`-th stop rule is its cap `m + 1`.** -/
theorem stopRule_recOne (m : ℕ) (w : ℝ≥0 → ℝ) : stopRule m (recOne, w) = ((m : ℝ≥0) + 1 : ℝ≥0) := by
  have hread : ∀ u, gaugeRead u (recOne, w) = (fun _ : ℝ≥0 => (1 : ℝ)) u := fun u => by
    simp only [gaugeRead]; exact decode_recOne _
  have h0 : recLevel gaugeRead m recOne < 1 := by
    unfold recLevel
    have : gaugeRead 0 (recOne, fun _ => 0) = 1 := by simp only [gaugeRead]; exact decode_recOne _
    rw [this]; exact gaugeLevel_lt one_pos m
  have hstop : gaugeStop (fun _ : ℝ≥0 => (1 : ℝ)) (recLevel gaugeRead m recOne) ((m : ℝ≥0) + 1) =
      (m : ℝ≥0) + 1 := by
    refine le_antisymm (gaugeStop_le _ _ _) (not_lt.1 fun hlt => ?_)
    have := gaugeStop_mem continuous_const hlt
    linarith
  unfold stopRule
  rw [hitRule_eq_gaugeStop continuous_const (by positivity) h0 fun u _ => hread u, hstop]

variable {κ : ℝ} {b : ℝ → ℝ} {jumps : Finset ℝ} {Ω : Type u} [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω]
  {P : Measure Ω} [IsProbabilityMeasure P] {E : ExplSpec → ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞} {u : ℝ}
  {l : List (ℝ × ℝ≥0)} {k ℓ : ℕ}

variable (P) in
/-- **F2b′'s stop inputs**: the stage objects, a record word measurable at time `0`, a countable set of types, and a
conull event on which the relative facts hold. -/
structure StopIn (κ : ℝ) (b : ℝ → ℝ) (jumps : Finset ℝ) (E : ExplSpec → ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞) (u : ℝ)
    (l : List (ℝ × ℝ≥0)) (k ℓ : ℕ) (ψ : ℝ) where
  hb : IsPiecewiseConstantBoundaryData b jumps
  S : StageObj P κ b jumps E u l k ℓ
  cw : Ω → BoundaryWord
  types : Set WordType
  htypes : types.Countable
  hcw : Measurable[lineC0 P κ b jumps E u l k ℓ] cw
  Gr : Set Ω
  hGr : MeasurableSet Gr
  hGrae : ∀ᵐ ω ∂P, ω ∈ Gr
  rel : ∀ ω ∈ S.Eg ∩ Gr, RelFactsAt κ ψ cw types (S.ρM ω) ω

namespace StopIn

variable {ψ : ℝ} (T : StopIn P κ b jumps E u l k ℓ ψ)

/-- The good event of the stops. -/
def Gs : Set Ω := T.S.Eg ∩ T.Gr

theorem measurableSet_Gs_line : MeasurableSet[lineC0 P κ b jumps E u l k ℓ] T.Gs :=
  T.S.hEg.inter ⟨T.hGr, ⟨univ, @MeasurableSet.univ Ω (lineSigma0 κ b jumps E u l k ℓ),
    ae_eq_univ.2 (ae_iff.1 T.hGrae)⟩⟩

theorem measurableSet_Gs : MeasurableSet T.Gs := T.measurableSet_Gs_line.1

theorem Gs_subset_Eg : T.Gs ⊆ T.S.Eg := inter_subset_left

theorem ae_mem_Gs : ∀ᵐ ω ∂P, ω ∈ T.S.F → ω ∈ T.Gs := by
  filter_upwards [T.S.hEgae, T.hGrae] with ω h1 h2 hF using ⟨h1 hF, h2⟩

/-- The canonical driver of the relative stage curves. -/
def Wr : ℝ≥0 → Ω → ℝ := CoordB.drivenDriver T.S.ρM

theorem measurable_Wr (q : ℝ≥0) : Measurable (T.Wr q) :=
  CoordB.measurable_drivenDriver T.S.driven_ρM (fun s hs => T.S.measurable_ρM T.hb s hs) q

theorem continuousOn_Wr (ω : Ω) : ContinuousOn (T.Wr · ω) {t | (t : ℝ≥0∞) < capLife (T.S.ρM ω)} :=
  CoordB.continuousOn_drivenDriver T.S.driven_ρM ω

theorem Wr_zero (ω : Ω) : T.Wr 0 ω = 0 := CoordB.drivenDriver_zero T.S.driven_ρM ω

theorem isGeneratingTrace_Wr (ω : Ω) {V : ℝ≥0∞} (hV : V < capLife (T.S.ρM ω)) :
    IsGeneratingTrace (T.Wr · ω) V (capTrace (T.S.ρM ω)) :=
  Sec5.CrossRestart.isGeneratingTrace_congr_drive ((T.S.driven_ρM ω).isGeneratingTrace hV)
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

theorem measurable_record_line : Measurable[lineC0 P κ b jumps E u l k ℓ] T.record := by
  classical
  unfold record
  exact Measurable.ite T.measurableSet_Gs_line (measurable_rec2 κ ψ T.cw T.types T.hcw T.htypes)
    (@measurable_const _ _ _ (lineC0 P κ b jumps E u l k ℓ) recOne)

theorem measurable_record : Measurable T.record := T.measurable_record_line.mono inf_le_left le_rfl

/-- The stops of the rule along the canonical driver. -/
def Vstop (m : ℕ) (ω : Ω) : ℝ≥0∞ := stopRule m (T.record ω, fun s => T.Wr s ω)

theorem measurable_Vstop (m : ℕ) : Measurable (T.Vstop m) :=
  (measurable_stopRule m).comp (T.measurable_record.prodMk T.measurable_path_Wr)

/-- The coordinate gauge of a good sample. -/
def gc (ω : Ω) : ℝ≥0 → ℝ := gco (relGauge2 κ ψ T.cw T.types ω) (capTrace (T.S.ρM ω)) (capLife (T.S.ρM ω))

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
    T.Vstop m ω = localStop (T.gc ω) m ∧ (localStop (T.gc ω) m : ℝ≥0∞) < capLife (T.S.ρM ω) ∧
      (∀ n, annRules gaugeRead m n (T.record ω, fun s => T.Wr s ω) < T.Vstop m ω) ∧
      ⨆ n, annRules gaugeRead m n (T.record ω, fun s => T.Wr s ω) = T.Vstop m ω ∧
      ∀ t : ℝ≥0, t < localStop (T.gc ω) m → 0 < relGauge2 κ ψ T.cw T.types ω (capTrace (T.S.ρM ω) t) := by
  have h := sample_rules_rel (r := T.record ω) (relGauge2_le_one κ ψ T.cw T.types ω) (T.relGauge2_zero_pos hω)
    (T.S.driven_ρM ω) (fun V hV => T.isGeneratingTrace_Wr ω hV) (T.continuousOn_Wr ω) (T.Wr_zero ω)
    (T.continuous_gc hω) (fun z hz => by rw [T.record_of_mem hω]; exact decode_rec2 κ ψ T.cw T.types ω hz) m
  obtain ⟨h1, h2, h3, h4, h5⟩ := h
  have hV : T.Vstop m ω = localStop (T.gc ω) m := h2
  exact ⟨hV, h1, fun n => hV ▸ h3 n, hV ▸ h4, h5⟩

theorem Vstop_lt {m : ℕ} {ω : Ω} (hω : ω ∈ T.Gs) : T.Vstop m ω < capLife (T.S.ρM ω) := by
  rw [(T.sample hω m).1]; exact (T.sample hω m).2.1

theorem Vstop_ne_top {m : ℕ} {ω : Ω} (hω : ω ∈ T.Gs) : T.Vstop m ω ≠ ⊤ := by
  rw [(T.sample hω m).1]; exact ENNReal.coe_ne_top

theorem Vstop_pos {m : ℕ} {ω : Ω} (hω : ω ∈ T.Gs) : 0 < T.Vstop m ω := by
  rw [(T.sample hω m).1]
  have hg0 : 0 < T.gc ω 0 := by
    unfold gc
    rw [gco_of_lt (by exact_mod_cast Vk.capLife_pos (T.S.driven_ρM ω)), capTrace_zero (T.S.driven_ρM ω)]
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
    ((T.Vstop m ω).toNNReal : ℝ≥0∞) < capLife (T.S.ρM ω) := by
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
theorem V_sup {ω : Ω} (hω : ω ∈ T.Gs) : ⨆ m, T.V m ω = capLife (T.S.ρM ω) := by
  simp only [T.V_eq hω, (T.sample hω _).1]
  have hR := T.rel ω hω
  have hg0 : 0 < T.gc ω 0 := by
    unfold gc
    rw [gco_of_lt (by exact_mod_cast Vk.capLife_pos (T.S.driven_ρM ω)), capTrace_zero (T.S.driven_ρM ω)]
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
    (U := fun ω => capLife (T.S.ρM ω)) (fun ω _ => T.continuousOn_Wr ω)
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

end StopIn

end InteractingSLE.Theorem14.SB.Nd
