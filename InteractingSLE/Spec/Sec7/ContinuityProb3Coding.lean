/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Foundations.Loewner.TraceCodingTop
import InteractingSLE.Foundations.Loewner.YuanCorollary13Slit
import InteractingSLE.Spec.Sec7.ContinuityProb2Restart

/-!
# §7.3: the Borel coding of the trace event with a random horizon

Packet PROVE-RANDRESTART2. The restarts of §7.3 with a random force word need the event

  `TraceEvent w ζ`: there is a continuous generating trace of the Loewner chain driven by `w` on `[0, ζ]` (on
  `[0, ∞)` if `ζ = ∞`), tending to infinity when `ζ = ∞`

as a Borel set of pairs `(w, ζ)` (driver, horizon), so that conditional laws can be integrated. PROVE-T14-IN's
characterization (`Coding.exists_isGeneratingTrace_iff_traceCond`: a countable uniform-continuity condition on the
measurable trace evaluations `LP.traceAt p w` at rational `p < ζ`, plus a countable hull condition at rational times)
holds for a finite horizon and a driver that is continuous on all of `[0, ∞)`. Here:

* the hull at a rational time `q < ζ` is read from the driver frozen after `q` (`frzQ`), whose rational-time values
  are a measurable function of `w` and whose continuous regularization (`Coding.regQ`) is the frozen driver itself;
  this only needs `w` continuous on `[0, ζ)`;
* a driver continuous on `[0, ζ)` with a left limit at a finite `ζ` extends continuously, which brings the
  characterization to it (`finCond_iff`);
* for `ζ = ∞` the transient coding `transientTraceCodingStatement` (PROVE-TRACECODE) is used.

Main results: `measurableSet_traceSet` and `mem_traceSet_iff`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Filter Set Topology Metric
open scoped NNReal ENNReal NNRat

open QuantumZipper (H fwdHull drive)

namespace InteractingSLE

namespace Sec7

namespace RandRestart

/-- **The trace event** of a driver `w` with horizon `ζ`: a continuous generating trace on `[0, ζ]` (on `[0, ∞)`
when `ζ = ∞`), tending to infinity when `ζ = ∞`. -/
def TraceEvent (w : ℝ≥0 → ℝ) (ζ : ℝ≥0∞) : Prop :=
  ∃ η : ℝ≥0 → ℂ, IsGeneratingTrace w ζ η ∧ (ζ = ⊤ → Tendsto (fun t => ‖η t‖) atTop atTop)

/-- The trace event only sees the driver before the horizon. -/
theorem TraceEvent.congr {w w' : ℝ≥0 → ℝ} {ζ : ℝ≥0∞} (h : TraceEvent w ζ)
    (hww' : ∀ t : ℝ≥0, (t : ℝ≥0∞) < ζ → w t = w' t) : TraceEvent w' ζ := by
  obtain ⟨η, hη, hηt⟩ := h
  exact ⟨η, IsGeneratingTrace.congr_lt hη fun t ht => (hww' t ht).symm, hηt⟩

theorem traceEvent_congr {w w' : ℝ≥0 → ℝ} {ζ : ℝ≥0∞}
    (hww' : ∀ t : ℝ≥0, (t : ℝ≥0∞) < ζ → w t = w' t) : TraceEvent w ζ ↔ TraceEvent w' ζ :=
  ⟨fun h => h.congr hww', fun h => h.congr fun t ht => (hww' t ht).symm⟩

/-! ### Frozen rational values -/

/-- The rational-time values of the driver `w` frozen after time `q`. -/
def frzQ (q : ℝ≥0) (w : ℝ≥0 → ℝ) : ℚ≥0 → ℝ := fun r => LP.freezeAt q w r

theorem measurable_frzQ (q : ℝ≥0) : Measurable (frzQ q) :=
  measurable_pi_iff.2 fun r => (measurable_pi_apply ((r : ℚ≥0) : ℝ≥0)).comp (LP.measurable_freezeAt q)

/-- The rational-time values of `w`. -/
def ratVals (w : ℝ≥0 → ℝ) : ℚ≥0 → ℝ := fun r => w r

theorem measurable_ratVals : Measurable ratVals :=
  measurable_pi_iff.2 fun r => measurable_pi_apply ((r : ℚ≥0) : ℝ≥0)

/-- The hull at a rational time `q` read from the frozen rational values. For a driver continuous on `[0, q]`
and vanishing at `0`, this is the hull of the driver (`hullQ_eq`). -/
def hullQ (q : ℚ≥0) (w : ℝ≥0 → ℝ) : Set ℂ :=
  fwdHull (drive 1 Coding.regQ (frzQ q w)) ((q : ℝ≥0) : ℝ)

theorem hullQ_eq {q : ℚ≥0} {w ŵ : ℝ≥0 → ℝ} (hŵ : Continuous ŵ) (hŵ0 : ŵ 0 = 0)
    (heq : ∀ r : ℝ≥0, r ≤ q → w r = ŵ r) :
    hullQ q w = fwdHull (fun s : ℝ => ŵ s.toNNReal) ((q : ℝ≥0) : ℝ) := by
  have hfr : LP.freezeAt q w = LP.freezeAt q ŵ := LP.freezeAt_congr heq
  have hc : Continuous (LP.freezeAt q ŵ) := LP.continuous_freezeAt hŵ.continuousOn
  have h0 : LP.freezeAt q ŵ 0 = 0 := by simp [LP.freezeAt, hŵ0]
  have hd : drive 1 Coding.regQ (frzQ q w) = fun s : ℝ => LP.freezeAt q ŵ s.toNNReal := by
    have : frzQ q w = fun r : ℚ≥0 => LP.freezeAt q ŵ r := by
      funext r; simp only [frzQ, hfr]
    rw [this]
    exact Coding.drive_regQ hc h0
  rw [hullQ, hd]
  refine YuanCorollary13.fwdHull_eq_of_eqOn_Icc (hc.comp continuous_real_toNNReal) (hŵ.comp continuous_real_toNNReal)
    (NNReal.coe_nonneg _) fun r hr => ?_
  have hrq : r.toNNReal ≤ (q : ℝ≥0) := by
    rw [Real.toNNReal_le_iff_le_coe]; exact hr.2
  show ŵ (min r.toNNReal (q : ℝ≥0)) = ŵ r.toNNReal
  rw [min_eq_left hrq]

/-! ### The finite-horizon condition -/

/-- **The finite-horizon trace condition** (`Coding.TraceCond` with the hull at each rational time read from the
frozen driver): countable uniform continuity of the trace evaluations at rational times before `ζ`, and the
countable hull conditions at rational times before `ζ`. -/
def FinCond (w : ℝ≥0 → ℝ) (ζ : ℝ≥0∞) : Prop :=
  (∀ m : ℕ, ∃ k : ℕ, ∀ p p' : ℚ≥0, ((p : ℝ≥0) : ℝ≥0∞) < ζ → ((p' : ℝ≥0) : ℝ≥0∞) < ζ →
      dist (p : ℝ≥0) (p' : ℝ≥0) < 1 / ((k : ℝ) + 1) →
      dist (LP.traceAt p w) (LP.traceAt p' w) ≤ 1 / ((m : ℝ) + 1)) ∧
  ∀ q : ℚ≥0, ((q : ℝ≥0) : ℝ≥0∞) < ζ →
    (∀ p : ℚ≥0, p ≤ q → LP.traceAt p w ∈ H → LP.traceAt p w ∈ hullQ q w) ∧
    ∀ (ε : ℚ) (c : ℚ × ℚ), 0 < ε → 2 * (ε : ℝ) < c.2 →
      (∀ p : ℚ≥0, p ≤ q → 3 * (ε : ℝ) < dist (Coding.ratPt c) (LP.traceAt p w)) →
      closedBall (Coding.ratPt c) ε ⊆ hullQ q w ∨ Disjoint (closedBall (Coding.ratPt c) ε) (hullQ q w)

/-- On a finite horizon, `FinCond` is PROVE-T14-IN's `TraceCond` of any continuous driver `ŵ` vanishing at `0`
that agrees with `w` before the horizon. -/
theorem finCond_iff {w ŵ : ℝ≥0 → ℝ} {ζ : ℝ≥0∞} (hŵ : Continuous ŵ) (hŵ0 : ŵ 0 = 0)
    (heq : ∀ t : ℝ≥0, (t : ℝ≥0∞) < ζ → w t = ŵ t) :
    FinCond w ζ ↔ Coding.TraceCond (fun s : ℝ => ŵ s.toNNReal) (fun p => LP.traceAt p ŵ)
      (fun p => ((p : ℝ≥0) : ℝ≥0∞) < ζ) := by
  have htr : ∀ p : ℚ≥0, ((p : ℝ≥0) : ℝ≥0∞) < ζ → LP.traceAt p w = LP.traceAt p ŵ := fun p hp =>
    LP.traceAt_congr fun r hr => heq r (lt_of_le_of_lt (ENNReal.coe_le_coe.2 hr) hp)
  have htr' : ∀ q : ℚ≥0, ((q : ℝ≥0) : ℝ≥0∞) < ζ → ∀ p : ℚ≥0, p ≤ q →
      LP.traceAt p w = LP.traceAt p ŵ := fun q hq p hp =>
    htr p (lt_of_le_of_lt (ENNReal.coe_le_coe.2 (by exact_mod_cast hp)) hq)
  have hK : ∀ q : ℚ≥0, ((q : ℝ≥0) : ℝ≥0∞) < ζ →
      hullQ q w = fwdHull (fun s : ℝ => ŵ s.toNNReal) ((q : ℝ≥0) : ℝ) := fun q hq =>
    hullQ_eq hŵ hŵ0 fun r hr => heq r (lt_of_le_of_lt (ENNReal.coe_le_coe.2 hr) hq)
  unfold FinCond Coding.TraceCond
  refine and_congr ?_ ?_
  · refine forall_congr' fun m => exists_congr fun k => forall_congr' fun p => forall_congr' fun p' => ?_
    refine forall_congr' fun hp => forall_congr' fun hp' => ?_
    rw [htr p hp, htr p' hp']
  · refine forall_congr' fun q => forall_congr' fun hq => ?_
    rw [hK q hq]
    refine and_congr ?_ ?_
    · refine forall_congr' fun p => forall_congr' fun hp => ?_
      rw [htr' q hq p hp]
    · refine forall_congr' fun ε => forall_congr' fun c => forall_congr' fun hε => forall_congr' fun hc => ?_
      refine imp_congr ?_ Iff.rfl
      refine forall_congr' fun p => forall_congr' fun hp => ?_
      rw [htr' q hq p hp]

/-- `FinCond` is a measurable condition on (driver, horizon). -/
theorem measurable_finCond : Measurable fun x : (ℝ≥0 → ℝ) × ℝ≥0∞ => FinCond x.1 x.2 := by
  have hL : ∀ p : ℚ≥0, Measurable fun x : (ℝ≥0 → ℝ) × ℝ≥0∞ => ((p : ℝ≥0) : ℝ≥0∞) < x.2 := fun p =>
    measurableSet_setOfPred.1 (measurableSet_lt measurable_const measurable_snd)
  have hτm : ∀ p : ℚ≥0, Measurable fun x : (ℝ≥0 → ℝ) × ℝ≥0∞ => LP.traceAt p x.1 := fun p =>
    (LP.measurable_traceAt p).comp measurable_fst
  have hfm : ∀ q : ℚ≥0, Measurable fun x : (ℝ≥0 → ℝ) × ℝ≥0∞ => frzQ q x.1 := fun q =>
    (measurable_frzQ q).comp measurable_fst
  have hHm : ∀ p : ℚ≥0, Measurable fun x : (ℝ≥0 → ℝ) × ℝ≥0∞ => LP.traceAt p x.1 ∈ H := fun p =>
    (measurable_mem.2 QuantumZipper.isOpen_H.measurableSet).comp (hτm p)
  have hKm : ∀ p q : ℚ≥0, Measurable fun x : (ℝ≥0 → ℝ) × ℝ≥0∞ => LP.traceAt p x.1 ∈ hullQ q x.1 :=
    fun p q => measurableSet_setOfPred.1
      ((QuantumZipper.NonSwallow.measurableSet_fwdHull_prod Coding.measurable_regQ Coding.continuous_regQ 1
        (NNReal.coe_nonneg _)).preimage ((hτm p).prodMk (hfm q)))
  refine Measurable.and ?_ ?_
  · refine Measurable.forall fun m => Measurable.exists fun k => Measurable.forall fun p : ℚ≥0 =>
      Measurable.forall fun p' : ℚ≥0 => (hL p).imp ((hL p').imp (Coding.measurable_imp_const fun _ => ?_))
    exact measurableSet_setOfPred.1 (measurableSet_le ((hτm p).dist (hτm p')) measurable_const)
  · refine Measurable.forall fun q => (hL q).imp (Measurable.and ?_ ?_)
    · exact Measurable.forall fun p : ℚ≥0 => Coding.measurable_imp_const fun _ => (hHm p).imp (hKm p q)
    · refine Measurable.forall fun ε => Measurable.forall fun c => Coding.measurable_imp_const fun hε =>
        Coding.measurable_imp_const fun hc => ?_
      have hε' : (0 : ℝ) < ε := by exact_mod_cast hε
      have hcε : (ε : ℝ) < (Coding.ratPt c).im := by rw [Coding.ratPt_im]; linarith
      refine (Measurable.forall fun p : ℚ≥0 => Coding.measurable_imp_const fun _ => measurableSet_setOfPred.1
        (measurableSet_lt measurable_const (measurable_const.dist (hτm p)))).imp
        (Measurable.or ?_ ?_)
      · exact (Coding.measurable_closedBall_subset_fwdHull Coding.continuous_regQ Coding.measurable_regQ
          (NNReal.coe_nonneg _) hε' hcε).comp (hfm q)
      · exact (Coding.measurable_disjoint_closedBall_fwdHull Coding.continuous_regQ Coding.measurable_regQ
          q hε' hcε).comp (hfm q)

/-! ### Continuous extension at a finite horizon -/

/-- A driver continuous on `[0, S)` with a left limit `w₀` at `S > 0`, extended by `w₀` from `S` on. -/
def extendAt (w : ℝ≥0 → ℝ) (S : ℝ≥0) (w₀ : ℝ) : ℝ≥0 → ℝ := fun t => if t < S then w t else w₀

theorem continuous_extendAt {w : ℝ≥0 → ℝ} {S : ℝ≥0} {w₀ : ℝ} (hw : ContinuousOn w {t | t < S})
    (hlim : Tendsto w (𝓝[<] S) (𝓝 w₀)) : Continuous (extendAt w S w₀) := by
  have hopen : IsOpen {t : ℝ≥0 | t < S} := isOpen_Iio
  refine continuous_iff_continuousAt.2 fun t => ?_
  rcases lt_trichotomy t S with htS | rfl | htS
  · have hev : extendAt w S w₀ =ᶠ[𝓝 t] w := by
      filter_upwards [hopen.mem_nhds htS] with r hr
      simp only [extendAt, show r < S from hr, ↓reduceIte]
    exact ((hw.continuousAt (hopen.mem_nhds htS))).congr hev.symm
  · have h1 : Tendsto (extendAt w t w₀) (𝓝[<] t) (𝓝 w₀) := by
      refine hlim.congr' ?_
      filter_upwards [self_mem_nhdsWithin] with r hr
      simp only [extendAt, show r < t from hr, ↓reduceIte]
    have h2 : Tendsto (extendAt w t w₀) (𝓝[≥] t) (𝓝 w₀) := by
      refine tendsto_const_nhds.congr' ?_
      filter_upwards [self_mem_nhdsWithin] with r hr
      simp only [extendAt, not_lt.2 (show t ≤ r from hr), ↓reduceIte]
    have h3 := h1.sup h2
    rw [nhdsLT_sup_nhdsGE] at h3
    have hval : extendAt w t w₀ t = w₀ := by simp [extendAt]
    rw [ContinuousAt, hval]
    exact h3
  · have hopen' : IsOpen {r : ℝ≥0 | S < r} := isOpen_Ioi
    have hev : extendAt w S w₀ =ᶠ[𝓝 t] fun _ => w₀ := by
      filter_upwards [hopen'.mem_nhds htS] with r hr
      simp only [extendAt, not_lt.2 (le_of_lt (show S < r from hr)), ↓reduceIte]
    exact continuousAt_const.congr hev.symm

/-- **A continuous extension before a finite horizon**: a driver continuous on `[0, ζ)`, vanishing at `0`, with a
left limit at `ζ` when `0 < ζ < ∞`, agrees before `ζ` with a continuous driver vanishing at `0`. -/
theorem exists_continuous_eqOn {w : ℝ≥0 → ℝ} {ζ : ℝ≥0∞} (hζ : ζ ≠ ⊤)
    (hw : ContinuousOn w {t | (t : ℝ≥0∞) < ζ}) (hw0 : w 0 = 0)
    (hlim : 0 < ζ → ∃ w₀ : ℝ, Tendsto w (𝓝[<] ζ.toNNReal) (𝓝 w₀)) :
    ∃ ŵ : ℝ≥0 → ℝ, Continuous ŵ ∧ ŵ 0 = 0 ∧ ∀ t : ℝ≥0, (t : ℝ≥0∞) < ζ → w t = ŵ t := by
  rcases eq_or_ne ζ 0 with rfl | hζ0
  · exact ⟨fun _ => 0, continuous_const, rfl, fun t ht => absurd ht (not_lt.2 bot_le)⟩
  obtain ⟨w₀, hw₀⟩ := hlim (pos_iff_ne_zero.2 hζ0)
  set S := ζ.toNNReal with hS
  have hSζ : (S : ℝ≥0∞) = ζ := ENNReal.coe_toNNReal hζ
  have hlt : ∀ t : ℝ≥0, (t : ℝ≥0∞) < ζ ↔ t < S := fun t => by rw [← hSζ]; exact ENNReal.coe_lt_coe
  have hS0 : 0 < S := (hlt 0).1 (pos_iff_ne_zero.2 hζ0)
  have hw' : ContinuousOn w {t | t < S} := hw.mono fun t ht => (hlt t).2 ht
  refine ⟨extendAt w S w₀, continuous_extendAt hw' hw₀, ?_, fun t ht => ?_⟩
  · simp [extendAt, hS0, hw0]
  · simp [extendAt, (hlt t).1 ht]

/-! ### The coding -/

/-- The rational-time coding of the transient trace event on an infinite horizon (PROVE-TRACECODE). -/
def transientSet : Set (ℚ≥0 → ℝ) := Classical.choose transientTraceCodingStatement

theorem measurableSet_transientSet : MeasurableSet transientSet :=
  (Classical.choose_spec transientTraceCodingStatement).1

theorem mem_transientSet_iff {w : ℝ≥0 → ℝ} (hw : Continuous w) (hw0 : w 0 = 0) :
    ratVals w ∈ transientSet ↔
      ∃ η : ℝ≥0 → ℂ, IsGeneratingTrace w ⊤ η ∧ Tendsto (fun t => ‖η t‖) atTop atTop :=
  (Classical.choose_spec transientTraceCodingStatement).2 w hw hw0

/-- **The Borel set of (driver, horizon) pairs with the trace event.** -/
def traceSet : Set ((ℝ≥0 → ℝ) × ℝ≥0∞) :=
  {x | (x.2 = ⊤ ∧ ratVals x.1 ∈ transientSet) ∨ (x.2 ≠ ⊤ ∧ FinCond x.1 x.2)}

theorem measurableSet_traceSet : MeasurableSet traceSet := by
  refine measurableSet_setOfPred.2 (Measurable.or (Measurable.and ?_ ?_) (Measurable.and ?_ ?_))
  · exact measurableSet_setOfPred.1 (measurable_snd (measurableSet_singleton ⊤))
  · exact measurableSet_setOfPred.1 ((measurable_ratVals.comp measurable_fst) measurableSet_transientSet)
  · exact (measurableSet_setOfPred.1 (measurable_snd (measurableSet_singleton ⊤))).not
  · exact measurable_finCond

/-- **The coding of the trace event.** For a driver `w` continuous on `[0, ζ)` with `w 0 = 0` and a left limit at a
finite positive horizon, `(w, ζ) ∈ traceSet` iff the trace event holds. -/
theorem mem_traceSet_iff {w : ℝ≥0 → ℝ} {ζ : ℝ≥0∞} (hw : ContinuousOn w {t | (t : ℝ≥0∞) < ζ})
    (hw0 : w 0 = 0) (hlim : 0 < ζ → ζ < ⊤ → ∃ w₀ : ℝ, Tendsto w (𝓝[<] ζ.toNNReal) (𝓝 w₀)) :
    (w, ζ) ∈ traceSet ↔ TraceEvent w ζ := by
  rcases eq_or_ne ζ ⊤ with rfl | hζ
  · have hc : Continuous w := by
      rw [← continuousOn_univ]
      exact hw.mono fun t _ => ENNReal.coe_lt_top
    show (⊤ = ⊤ ∧ ratVals w ∈ transientSet) ∨ ((⊤ : ℝ≥0∞) ≠ ⊤ ∧ FinCond w ⊤) ↔ _
    simp only [true_and, ne_eq, not_true_eq_false, false_and, or_false]
    rw [mem_transientSet_iff hc hw0]
    unfold TraceEvent
    simp only [forall_const]
  · obtain ⟨ŵ, hŵ, hŵ0, heq⟩ := exists_continuous_eqOn hζ hw hw0 fun h => hlim h (lt_top_iff_ne_top.2 hζ)
    show (ζ = ⊤ ∧ ratVals w ∈ transientSet) ∨ (ζ ≠ ⊤ ∧ FinCond w ζ) ↔ _
    simp only [hζ, false_and, ne_eq, not_false_eq_true, true_and, false_or]
    rw [finCond_iff hŵ hŵ0 heq, ← Coding.exists_isGeneratingTrace_iff_traceCond hŵ hŵ0 hζ,
      traceEvent_congr heq]
    unfold TraceEvent
    simp only [hζ, false_implies, and_true]

end RandRestart

end Sec7

end InteractingSLE
