/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec5.CrossRestartKernelImage
import InteractingSLE.Spec.Exist.StagedDet
import InteractingSLE.Spec.Sec5.Prop49QExitAux22

/-!
# The driver of a path code as a Borel function of the code

Packet PROVE-CFRESTART. The counterflow restart law (`CrossRestart.CounterflowRestartKernelOnStatement`) asks for the
law `IsFlowLineTraceLaw (16/κ) c (K d) decPath (·.2)` on the code space `(PCode × PCode) × ℝ≥0∞` of the restart
variable (`restartVar`, PROVE-SEC5-H/I): the decoded path must be a generating trace of the driver of an integrated
`SLE_κ′(ρ)` evolution **on the code space**, so the driver must be a measurable function of the path code.

PROVE-STAGED's Borel left inverse `Exist.Staged.dInv` of the trace-code map `dTrace` (Lusin–Souslin on the good
driver codes `DSet`: hulls are fillings of the trace and determine continuous drivers) gives exactly this:

* `killCode w U`: the killed dyadic code of a driver `w` with lifetime `U`; **`killCode_mem_DSet`**: it is a good
  driver code when `w` is continuous before `U`, `w 0 = 0`, and `w` has a continuous generating trace `η` on
  `[0, U]`; **`dTrace_killCode`**: its trace code consists of the values of `η` at the dyadic times before `U`;
* `pathTrCode`, `pathDrvCode = dInv ∘ pathTrCode`: the trace code read from a path code, and the driver code read
  from it — **Borel** (`measurable_pathDrvCode`);
* **`pathDrvCode_eq`**, **`drvPath_pathDrvCode`**: if the decoded path `decPath s` is a generating trace, of lifetime
  `s.2`, of a driver `w` continuous before `s.2` with `w 0 = 0`, then the driver code read from `s` is the killed code
  of `w`, and its driver path is `w` before `s.2`;
* **`IsRestartData.drvPath_pathDrvCode_restartChartPath`**: for the counterflow in the restart chart with exhausted
  chart capacity, the driver read from the code of the chart path in capacity time is the image driver of
  `IsRestartData.exists_imageDriver`.
-/

set_option autoImplicit false

noncomputable section

open Complex Set Metric Filter Topology MeasureTheory
open scoped NNReal ENNReal

open QuantumZipper (H)

namespace InteractingSLE.Sec5.CrossRestart

open Sec2.Assembly Exist.Staged Restart

/-! ### The killed code of a driver -/

section Kill

variable {w : ℝ≥0 → ℝ} {U : ℝ≥0∞} {η : ℝ≥0 → ℂ}

/-- **The killed dyadic code of a driver `w` with lifetime `U`**: the values of `w` at the dyadic times before `U`,
and `0` from `U` on. -/
def killCode (w : ℝ≥0 → ℝ) (U : ℝ≥0∞) : DCode :=
  (U, fun n k => if (dyad n k : ℝ≥0∞) < U then w (dyad n k) else 0)

/-- The driver killed at `U`. -/
def killDrv (w : ℝ≥0 → ℝ) (U : ℝ≥0∞) (t : ℝ≥0) : ℝ := if (t : ℝ≥0∞) < U then w t else 0

theorem killCode_snd (w : ℝ≥0 → ℝ) (U : ℝ≥0∞) : (killCode w U).2 = enc (killDrv w U) := rfl

theorem killDrv_eqOn (w : ℝ≥0 → ℝ) (U : ℝ≥0∞) : EqOn (killDrv w U) w {t | (t : ℝ≥0∞) < U} :=
  fun t (ht : (t : ℝ≥0∞) < U) => by simp only [killDrv, ht, ↓reduceIte]

theorem continuousOn_killDrv (hw : ContinuousOn w {t | (t : ℝ≥0∞) < U}) {T : ℝ≥0} (hT : (T : ℝ≥0∞) < U) :
    ContinuousOn (killDrv w U) (Iic T) := by
  have hsub : Iic T ⊆ {t : ℝ≥0 | (t : ℝ≥0∞) < U} := fun t ht =>
    lt_of_le_of_lt (ENNReal.coe_le_coe.2 ht) hT
  exact (hw.mono hsub).congr fun t ht => killDrv_eqOn w U (hsub ht)

/-- Before the lifetime, the decoded killed code is the driver. -/
theorem dec_killCode (hw : ContinuousOn w {t | (t : ℝ≥0∞) < U}) {t : ℝ≥0} (ht : (t : ℝ≥0∞) < U) :
    dec (killCode w U).2 t = w t := by
  rw [killCode_snd, dec_enc ((continuousOn_killDrv hw ht) t (mem_Iic.2 le_rfl)), killDrv_eqOn w U ht]

theorem eqOn_dec_killCode (hw : ContinuousOn w {t | (t : ℝ≥0∞) < U}) :
    EqOn (dec (killCode w U).2) w {t | (t : ℝ≥0∞) < U} := fun _ ht => dec_killCode hw ht

/-- A generating trace on `[0, U]` is one on `[0, r]` for every `r < U`, for any driver agreeing before `U`. -/
theorem isGeneratingTrace_of_eqOn_of_lt {w' : ℝ≥0 → ℝ} (hη : IsGeneratingTrace w U η)
    (he : EqOn w' w {t | (t : ℝ≥0∞) < U}) {r : ℝ≥0} (hr : (r : ℝ≥0∞) < U) :
    IsGeneratingTrace w' (r : ℝ≥0∞) η := by
  refine ⟨hη.1, hη.2.1.mono fun t ht => le_trans ht hr.le, fun t ht => ?_⟩
  have htU : (t : ℝ≥0∞) < U := lt_trans ht hr
  have hK : QuantumZipper.fwdHull (fun s : ℝ => w' s.toNNReal) t =
      QuantumZipper.fwdHull (fun s : ℝ => w s.toNNReal) t := by
    refine fwdHull_eq_of_eqOn (t₂ := r) (NNReal.coe_nonneg t) (by exact_mod_cast ht) fun s hs => ?_
    refine he (lt_of_le_of_lt (ENNReal.coe_le_coe.2 ?_) hr)
    exact Real.toNNReal_le_iff_le_coe.2 hs.2
  rw [hK]
  exact hη.2.2 t htU

/-- **The killed code of a driver with a generating trace is a good driver code.** -/
theorem killCode_mem_DSet (hw : ContinuousOn w {t | (t : ℝ≥0∞) < U}) (hw0 : w 0 = 0)
    (hη : IsGeneratingTrace w U η) : killCode w U ∈ DSet := by
  refine ⟨fun n k h => ?_, fun n k h => ?_, fun n k h => ?_, fun n k h => ?_⟩
  · rw [killCode_snd]
    exact uc_enc (continuousOn_killDrv hw h)
  · show (if (dyad n k : ℝ≥0∞) < U then w (dyad n k) else 0) = 0
    split_ifs
    · rw [h, hw0]
    · rfl
  · show (if (dyad n k : ℝ≥0∞) < U then w (dyad n k) else 0) = 0
    simp only [show ¬ (dyad n k : ℝ≥0∞) < U from h, ↓reduceIte]
  · have he := eqOn_dec_killCode hw
    have hwc : ContinuousOn (dec (killCode w U).2) {t | (t : ℝ≥0∞) < U} := hw.congr he
    have hpos : (0 : ℝ≥0∞) < U := lt_of_le_of_lt bot_le h
    have h0 : dec (killCode w U).2 0 = 0 := by
      rw [dec_killCode hw (by simpa using hpos), hw0]
    exact Prop49Exit.mem_traceSet_of_trace hwc h0 h (isGeneratingTrace_of_eqOn_of_lt hη he h)

/-- **The trace code of the killed code** is the dyadic values of the generating trace before `U`. -/
theorem dTrace_killCode (hw : ContinuousOn w {t | (t : ℝ≥0∞) < U}) (hw0 : w 0 = 0)
    (hη : IsGeneratingTrace w U η) :
    dTrace (killCode w U) = (U, fun n k => if (dyad n k : ℝ≥0∞) < U then η (dyad n k) else 0) := by
  refine Prod.ext rfl (funext fun n => funext fun k => ?_)
  show (if (dyad n k : ℝ≥0∞) < U then LP.traceAt (dyad n k) (dec (killCode w U).2) else 0) =
    (if (dyad n k : ℝ≥0∞) < U then η (dyad n k) else 0)
  by_cases h : (dyad n k : ℝ≥0∞) < U
  · simp only [h, ↓reduceIte]
    rw [LP.traceAt_congr (w' := w) fun r hr => dec_killCode hw (lt_of_le_of_lt (ENNReal.coe_le_coe.2 hr) h)]
    exact LP.traceAt_eq_of_isGeneratingTrace hη hw hw0 h
  · simp only [h, ↓reduceIte]

end Kill

/-! ### The driver code read from a path code -/

section Path

/-- **The trace code read from a path code**: the lifetime and the values of the decoded path at the dyadic times
before it. -/
def pathTrCode (s : (PCode × PCode) × ℝ≥0∞) : ℝ≥0∞ × (ℕ → ℕ → ℂ) :=
  (s.2, fun n k => if (dyad n k : ℝ≥0∞) < s.2 then decPath s (dyad n k) else 0)

theorem measurable_pathTrCode : Measurable pathTrCode := by
  refine measurable_snd.prodMk (measurable_pi_iff.2 fun n => measurable_pi_iff.2 fun k => ?_)
  exact Measurable.ite (measurableSet_lt measurable_const measurable_snd) (measurable_decPath _) measurable_const

/-- **The driver code read from a path code**: PROVE-STAGED's Borel left inverse of the trace-code map. -/
def pathDrvCode (s : (PCode × PCode) × ℝ≥0∞) : DCode := dInv (pathTrCode s)

theorem measurable_pathDrvCode : Measurable pathDrvCode := measurable_dInv.comp measurable_pathTrCode

variable {s : (PCode × PCode) × ℝ≥0∞} {w : ℝ≥0 → ℝ}

/-- **The driver code of a path code that generates a driver**: if `decPath s` is a generating trace of lifetime `s.2`
of a driver `w` continuous before `s.2` with `w 0 = 0`, the driver code read from `s` is the killed code of `w`. -/
theorem pathDrvCode_eq (hw : ContinuousOn w {t | (t : ℝ≥0∞) < s.2}) (hw0 : w 0 = 0)
    (hη : IsGeneratingTrace w s.2 (decPath s)) : pathDrvCode s = killCode w s.2 := by
  have hmem := killCode_mem_DSet hw hw0 hη
  rw [pathDrvCode, show pathTrCode s = dTrace (killCode w s.2) from (dTrace_killCode hw hw0 hη).symm,
    dInv_dTrace hmem]

/-- **The driver read from the code is the driver** before the lifetime. -/
theorem drvPath_pathDrvCode (hw : ContinuousOn w {t | (t : ℝ≥0∞) < s.2}) (hw0 : w 0 = 0)
    (hη : IsGeneratingTrace w s.2 (decPath s)) {t : ℝ≥0} (ht : (t : ℝ≥0∞) < s.2) :
    drvPath (pathDrvCode s) t = w t := by
  rw [pathDrvCode_eq hw hw0 hη, drvPath_of_lt (show (t : ℝ≥0∞) < (killCode w s.2).1 from ht),
    dec_killCode hw ht]

end Path

/-! ### The image driver of the counterflow restart as a function of the chart path code -/

namespace IsRestartData

variable {q : ℝ} {U : ℝ → ℝ} {σ x₁ : ℝ} {w' : ℝ≥0 → ℝ} {ζ' : ℝ≥0∞} {γ' : ℝ≥0 → ℂ} {T : ℝ≥0∞}

/-- **The image driver is read from the code of the chart path.** When the chart capacity is exhausted before the exit,
for a glued image driver `W''` as in `exists_imageDriver`, the driver read from the code `encPath (restartChartPath) ⊤`
is `W''` at every time. -/
theorem drvPath_pathDrvCode_restartChartPath (hd : IsRestartData q U σ x₁ w' ζ' γ' T)
    (hexh : ∀ u : ℝ, ∃ t : ℝ≥0, (t : ℝ≥0∞) < T ∧ u ≤ restartClock q U σ x₁ w' t) {W'' : ℝ → ℝ} (hW''0 : W'' 0 = 0)
    (hW'' : ∀ t₀ : ℝ≥0, (t₀ : ℝ≥0∞) < T →
      ∃ V : ℝ → ℝ, Continuous V ∧ V 0 = 0 ∧ EqOn W'' V (Icc 0 (restartClock q U σ x₁ w' t₀)) ∧
        ∀ t : ℝ≥0, t ≤ t₀ →
          QuantumZipper.fwdHull V (restartClock q U σ x₁ w' t) = restartMap q U σ x₁ '' cfHull w' t)
    (t : ℝ≥0) :
    drvPath (pathDrvCode (encPath (restartChartPath q U σ x₁ w' γ' T) ⊤)) t = W'' t := by
  have hgen := hd.isGeneratingTrace_restartChartPath hexh hW''
  have hcont : ContinuousOn (restartChartPath q U σ x₁ w' γ' T) {t | (t : ℝ≥0∞) ≤ ⊤} := hgen.2.1
  have hdec : decPath (encPath (restartChartPath q U σ x₁ w' γ' T) ⊤) = restartChartPath q U σ x₁ w' γ' T :=
    funext fun t => decPath_encPath hcont le_top
  have ha := hd.isExhaustingClock hexh
  -- `W''` is continuous on every `[0, a(t₀)]`, and these exhaust `[0, ∞)`
  have hWc : ContinuousOn (fun u : ℝ≥0 => W'' u) {t | (t : ℝ≥0∞) < ⊤} := by
    intro u _
    obtain ⟨t₀, ht₀T, hut₀⟩ := ha.unbounded ((u : ℝ) + 1)
    obtain ⟨V, hVc, -, hWV, -⟩ := hW'' t₀ ht₀T
    have hS : {v : ℝ≥0 | (v : ℝ) < (u : ℝ) + 1} ∈ 𝓝 u :=
      (isOpen_lt NNReal.continuous_coe continuous_const).mem_nhds (show (u : ℝ) < u + 1 by linarith)
    have hc : ContinuousAt (fun v : ℝ≥0 => W'' v) u := by
      refine ((hVc.comp NNReal.continuous_coe).continuousAt).congr ?_
      filter_upwards [hS] with v hv
      exact (hWV ⟨NNReal.coe_nonneg v, by linarith [show (v : ℝ) < (u : ℝ) + 1 from hv]⟩).symm
    exact hc.continuousWithinAt
  have hgen' : IsGeneratingTrace (fun u : ℝ≥0 => W'' u)
      (encPath (restartChartPath q U σ x₁ w' γ' T) ⊤).2
      (decPath (encPath (restartChartPath q U σ x₁ w' γ' T) ⊤)) := by
    rw [hdec]; exact hgen
  exact drvPath_pathDrvCode hWc (by simpa using hW''0) hgen'
    (show (t : ℝ≥0∞) < ⊤ from ENNReal.coe_lt_top)

end IsRestartData

end InteractingSLE.Sec5.CrossRestart
