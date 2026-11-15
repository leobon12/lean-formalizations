/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.StripSideHeightProbSide
import InteractingSLE.Spec.Sec6.Prop61BMarked
import InteractingSLE.Spec.Sec6.Prop65Point

/-!
# `hmark`: the angle-varying path's range is a local set marked by the two retained records

Packet PROVE-STRIPSYS19. Specification §7.4, proof of Aux. lemma 130 (`source/spec/p385-432.md` L440–L456, p. 411):
"Retain the two full marked local sets. […] To implement that statement with own-path couplings, choose finite
rational own times beyond the compact subarc, use the two stopped canonical means, and then enlarge to the complete
marked union." For the angle-varying path `α = η^{t₀,∞}_{θ₀,θ}` the stopped canonical mean is the mean given the
retained records of both pieces (PROVE-STRIPSYS16, `ae_apply_eq_stageMean`), which needs the **marked** locality of
`A = α([0, t₀ + r]) ∩ ℍ` for the σ-algebra `pastTwo` of the two records (hypothesis `hmark`).

**Route.** Lemma 6.2 with a single path stopped at the deterministic time `T = t₀ + r`
(`Sec6.isHistoryAvoidanceLocal_explored`) gives the marked criterion for the marks of the **path history**
`(α(q))_{q ≤ T}`, from Lemma 6.2's inputs for `α`: a continuous version, field determination at each time, and the
history-sensitive locality at first entrance times. The records are recovered from the path history: on the good event
both records are explicit functions of the concatenated record driver on `[0, T]` (`recsTwo_eq_recsOfDriver`), and
that driver is a Borel function of the trace values at the dyadic times before `T` (`histDriver_eq`: the trace code of
the driver killed at `T` lies in the landed good set `Exist.Staged.DSet`, on which the Lusin–Souslin left inverse
`Exist.Staged.dInv` recovers it). So every record event is almost surely a path-history event, and the marked criterion
passes to `pastTwo` (`isHistoryAvoidanceLocal_of_ae_le`).

## Main results

* `histDriver`, **`histDriver_eq`**: the driver on `[0, T]` read off the stopped path history of its generating trace;
* `recsOfDriver`, **`recsTwo_eq_recsOfDriver`**: on the good event the two records are read off the concatenated
  record driver;
* **`ae_recsTwo_eq`**: almost surely the records are a Borel function of the path history of `α` through `T`;
* `isHistoryAvoidanceLocal_of_ae_le`: the marked criterion passes to marks that are almost surely marks;
* **`isHistoryAvoidanceLocal_pastTwo`** (`hmark`), **`isLocalSet_range`**, **`ae_stopChart_dom`** (`hAD`);
* **`ae_hasSideHeights_stage_of_lemma62`**: STRIPSYS16's (S) for the angle-varying path with `hmark`, `hloc`, `hAD`
  discharged, from Lemma 6.2's inputs for `α`.

The inputs of Lemma 6.2 for `α` (field determination and entrance locality of the two-piece path) are the hypotheses
`hdet`, `hloc` here; they are the specification's "For these two-piece schedules the required continuity, simplicity,
and determination follow directly from the earlier non-boundary results […] Conditional field determination makes the
continuation measurable from the first prefix and the original field" (p. 410) and Aux. lemma 56 for the two-piece path.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open QuantumZipper (H fwdHull)
open scoped NNReal ENNReal

namespace InteractingSLE

namespace Sec7

namespace StripMark

open Sec2.Assembly Exist.Staged Exist.StagedLaw StripSideHeightProb

/-! ### The driver read off the stopped path history of its trace -/

section Code

/-- The dyadic time `k / 2ⁿ` as a nonnegative rational. -/
def dyadQ (n k : ℕ) : ℚ≥0 := (k : ℚ≥0) / 2 ^ n

theorem coe_dyadQ (n k : ℕ) : ((dyadQ n k : ℚ≥0) : ℝ≥0) = dyad n k := by
  simp [dyadQ, dyad]

/-- The trace code at horizon `T` of a stopped path history: the trace values at the dyadic times before `T`. -/
def histCode (T : ℝ≥0) (p : Sec6.Hist) : ℝ≥0∞ × (ℕ → ℕ → ℂ) :=
  ((T : ℝ≥0∞), fun n k => if (dyad n k : ℝ≥0∞) < T then p.2 (dyadQ n k) else 0)

theorem measurable_histCode (T : ℝ≥0) : Measurable (histCode T) := by
  refine measurable_const.prodMk (measurable_pi_iff.2 fun n => measurable_pi_iff.2 fun k => ?_)
  by_cases h : (dyad n k : ℝ≥0∞) < T
  · simp only [h, ↓reduceIte]
    exact (measurable_pi_apply (dyadQ n k)).comp measurable_snd
  · simp only [h, ↓reduceIte]
    exact measurable_const

/-- **The driver read off a stopped path history** at horizon `T`: the Lusin–Souslin inverse of the trace code,
read as a path frozen at its left limit at `T`. -/
def histDriver (T : ℝ≥0) (p : Sec6.Hist) : ℝ≥0 → ℝ := drvPath (dInv (histCode T p))

theorem measurable_histDriver (T : ℝ≥0) : Measurable (histDriver T) :=
  measurable_drvPath.comp (measurable_dInv.comp (measurable_histCode T))

/-- The killed code of a path at the deterministic horizon `T`. -/
abbrev kCode (W : ℝ≥0 → ℝ) (T : ℝ≥0) : PCode :=
  killedCode (fun s (_ : Unit) => W s) 0 (fun _ => (T : ℝ≥0∞)) ()

theorem dec_kCode {W : ℝ≥0 → ℝ} (hW : Continuous W) (hW0 : W 0 = 0) {T s : ℝ≥0} (hs : s < T) :
    dec (kCode W T) s = W s :=
  dec_killedCode (X := fun s (_ : Unit) => W s) (ζ := fun _ => (T : ℝ≥0∞)) hW0 hW.continuousOn
    (ENNReal.coe_lt_coe.2 hs)

/-- **The trace code of a driver killed at `T` is a good driver code.** -/
theorem kCode_mem_DSet {W : ℝ≥0 → ℝ} (hW : Continuous W) (hW0 : W 0 = 0) {T : ℝ≥0} (hT : 0 < T)
    {η : ℝ≥0 → ℂ} (hη : IsGeneratingTrace W T η) : ((T : ℝ≥0∞), kCode W T) ∈ DSet := by
  refine ⟨fun n k hd => ?_, fun n k h0 => ?_, fun n k hd => ?_, fun n k hd => ?_⟩
  · exact uc_killedCode (X := fun s (_ : Unit) => W s) (ζ := fun _ => (T : ℝ≥0∞)) (ω := ()) hW0
      hW.continuousOn hd
  · simp only [killedCode, h0, ↓reduceIte]
  · simp only [killedCode]
    split_ifs <;> rfl
  · -- the decoded path has a generating trace on `[0, d]`
    set d : ℝ≥0 := dyad n k with hd_def
    have hdT : d < T := by
      have hd' : (d : ℝ≥0∞) < T := hd
      exact_mod_cast hd'
    have hdec : ∀ s : ℝ≥0, s < T → dec (kCode W T) s = W s := fun s hs => dec_kCode hW hW0 hs
    have hwc : ContinuousOn (dec (kCode W T)) {t : ℝ≥0 | (t : ℝ≥0∞) < (d : ℝ≥0∞)} := by
      refine hW.continuousOn.congr fun t ht => hdec t ?_
      exact lt_trans (by exact_mod_cast ht) hdT
    have hw0 : dec (kCode W T) 0 = 0 := by rw [hdec 0 hT, hW0]
    rw [RandRestart.mem_traceSet_iff hwc hw0 fun _ _ => ?_]
    · refine ⟨η, IsGeneratingTrace.congr_lt (hη.mono_horizon (ENNReal.coe_le_coe.2 hdT.le)) fun t ht => ?_,
        fun h => absurd h ENNReal.coe_ne_top⟩
      exact hdec t (lt_trans (by exact_mod_cast ht) hdT)
    · refine ⟨W d, ?_⟩
      rw [ENNReal.toNNReal_coe]
      refine (hW.tendsto d).mono_left nhdsWithin_le_nhds |>.congr' ?_
      filter_upwards [self_mem_nhdsWithin] with t ht
      exact (hdec t (lt_trans ht hdT)).symm

/-- The trace code of the killed driver is the trace code of the path history of its trace. -/
theorem dTrace_kCode {W : ℝ≥0 → ℝ} (hW : Continuous W) (hW0 : W 0 = 0) {T : ℝ≥0}
    {η : ℝ≥0 → ℂ} (hη : IsGeneratingTrace W T η) :
    dTrace ((T : ℝ≥0∞), kCode W T) = histCode T (Sec6.histOf (Sec6.pathCoord η) T) := by
  refine Prod.ext rfl (funext fun n => funext fun k => ?_)
  change (if (dyad n k : ℝ≥0∞) < (T : ℝ≥0∞) then LP.traceAt (dyad n k) (dec (kCode W T)) else 0) =
    (if (dyad n k : ℝ≥0∞) < T then Sec6.stopCoord (Sec6.pathCoord η) T (dyadQ n k) else 0)
  split_ifs with hd
  · have hdT : dyad n k < T := by exact_mod_cast hd
    have hle : (((dyadQ n k : ℚ≥0) : ℝ≥0) : ℝ≥0∞) ≤ T := by rw [coe_dyadQ]; exact hd.le
    rw [Sec6.stopCoord_of_le hle, LP.traceAt_congr (w' := W) fun s hs => dec_kCode hW hW0 (lt_of_le_of_lt hs hdT),
      LP.traceAt_eq_of_isGeneratingTrace hη hW.continuousOn hW0 hd]
    simp only [Sec6.pathCoord, coe_dyadQ]
  · rfl

/-- **The driver is read off the stopped path history of its generating trace**: for a continuous driver `W` with
`W 0 = 0` and a generating trace `η` on `[0, T]`, `histDriver T (η|_{[0,T]}) = W` on `[0, T]`. -/
theorem histDriver_eq {W : ℝ≥0 → ℝ} (hW : Continuous W) (hW0 : W 0 = 0) {T : ℝ≥0} (hT : 0 < T)
    {η : ℝ≥0 → ℂ} (hη : IsGeneratingTrace W T η) {s : ℝ≥0} (hs : s ≤ T) :
    histDriver T (Sec6.histOf (Sec6.pathCoord η) T) s = W s := by
  have hz := kCode_mem_DSet hW hW0 hT hη
  have hinv : dInv (histCode T (Sec6.histOf (Sec6.pathCoord η) T)) = ((T : ℝ≥0∞), kCode W T) := by
    rw [← dTrace_kCode hW hW0 hη, dInv_dTrace hz]
  unfold histDriver
  rw [hinv]
  have hlt : ∀ t : ℝ≥0, t < T → drvPath ((T : ℝ≥0∞), kCode W T) t = W t := fun t ht => by
    rw [drvPath_of_lt (show (t : ℝ≥0∞) < (T : ℝ≥0∞) by exact_mod_cast ht)]
    exact dec_kCode hW hW0 ht
  rcases hs.lt_or_eq with hs | rfl
  · exact hlt s hs
  · have h := drvPath_eq_of_tendsto (z := ((s : ℝ≥0∞), kCode W s)) ENNReal.coe_ne_top
      (show (0 : ℝ≥0∞) < (s : ℝ≥0∞) by exact_mod_cast hT) (c := W s) ?_
    · simpa using h
    · rw [ENNReal.toNNReal_coe]
      refine (hW.tendsto s).mono_left nhdsWithin_le_nhds |>.congr' ?_
      filter_upwards [self_mem_nhdsWithin] with t ht
      exact (hlt t ht).symm

end Code

/-! ### The two records read off the concatenated record driver -/

section Records

variable {κ : ℝ} {b : ℝ → ℝ} {jumps : Finset ℝ} {Ω : Type*} {θ₀ θ : ℝ} {t₀ r : ℝ≥0}
  {E : ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞}

/-- The two records read off a driver on `[0, t₀ + r]`: the first piece at `t₀`, the continuation (the restarted
driver) at `r`, both alive. -/
def recsOfDriver (t₀ r : ℝ≥0) (W : ℝ≥0 → ℝ) : PastData 2 :=
  ![((fun q : ℚ => W (min (q : ℝ).toNNReal t₀)), (t₀ : ℝ≥0∞), false),
    ((fun q : ℚ => W (t₀ + min (q : ℝ).toNNReal r) - W t₀), (r : ℝ≥0∞), false)]

theorem measurable_recsOfDriver (t₀ r : ℝ≥0) : Measurable (recsOfDriver t₀ r) := by
  refine measurable_pi_iff.2 fun i => ?_
  fin_cases i
  · change Measurable fun W : ℝ≥0 → ℝ =>
      (((fun q : ℚ => W (min (q : ℝ).toNNReal t₀)), (t₀ : ℝ≥0∞), false) : RecData)
    refine Measurable.prodMk (measurable_pi_iff.2 fun q : ℚ => ?_) measurable_const
    exact measurable_pi_apply _
  · change Measurable fun W : ℝ≥0 → ℝ =>
      (((fun q : ℚ => W (t₀ + min (q : ℝ).toNNReal r) - W t₀), (r : ℝ≥0∞), false) : RecData)
    refine Measurable.prodMk (measurable_pi_iff.2 fun q : ℚ => ?_) measurable_const
    exact (measurable_pi_apply _).sub (measurable_pi_apply _)

/-- The records only see the driver on `[0, t₀ + r]`. -/
theorem recsOfDriver_congr {W W' : ℝ≥0 → ℝ} (h : ∀ s, s ≤ t₀ + r → W s = W' s) :
    recsOfDriver t₀ r W = recsOfDriver t₀ r W' := by
  funext i
  fin_cases i
  · change (((fun q : ℚ => W (min (q : ℝ).toNNReal t₀)), (t₀ : ℝ≥0∞), false) : RecData) =
      ((fun q : ℚ => W' (min (q : ℝ).toNNReal t₀)), (t₀ : ℝ≥0∞), false)
    congr 1
    funext q
    exact h _ ((min_le_right _ _).trans le_self_add)
  · change (((fun q : ℚ => W (t₀ + min (q : ℝ).toNNReal r) - W t₀), (r : ℝ≥0∞), false) : RecData) =
      ((fun q : ℚ => W' (t₀ + min (q : ℝ).toNNReal r) - W' t₀), (r : ℝ≥0∞), false)
    congr 1
    funext q
    have hle : t₀ + min (q : ℝ).toNNReal r ≤ t₀ + r := add_le_add le_rfl (min_le_right _ _)
    rw [h _ hle, h _ le_self_add]

/-- The record of a regular driver alive at its stop. -/
theorem recOf_of_lt {t : ℝ≥0} {e : (ℝ≥0 → ℝ) × ℝ≥0∞} (ht : (t : ℝ≥0∞) < e.2) :
    recOf t e = ((fun q : ℚ => e.1 (min (q : ℝ).toNNReal t)), (t : ℝ≥0∞), false) := by
  have hmin : min (t : ℝ≥0∞) e.2 = t := min_eq_left ht.le
  have hdec : decide (e.2 ≤ (t : ℝ≥0∞)) = false := decide_eq_false (not_le.2 ht)
  change ((fun q : ℚ => e.1 (min (((q : ℝ).toNNReal : ℝ≥0) : ℝ≥0∞) (min (t : ℝ≥0∞) e.2)).toNNReal),
    min (t : ℝ≥0∞) e.2, decide (e.2 ≤ (t : ℝ≥0∞))) = _
  rw [hmin, hdec]
  congr 1

/-- The record driver of a regular driver alive at its stop, on a good record. -/
theorem recW_recOf_of_lt {t : ℝ≥0} {e : (ℝ≥0 → ℝ) × ℝ≥0∞} (he : IsRegularDriver e) (ht : (t : ℝ≥0∞) < e.2)
    (hg : LocalExt.IsDrvGood (recHist (recOf t e))) (s : ℝ≥0) : recW (recOf t e) s = e.1 (min s t) := by
  change LocalExt.histDrv (recHist (recOf t e)) s = _
  rw [histDrv_recHist he hg s]
  change e.1 (min (s : ℝ≥0∞) (min (t : ℝ≥0∞) e.2)).toNNReal = _
  rw [min_eq_left ht.le, ← ENNReal.coe_min, ENNReal.toNNReal_coe]

/-- The record of a regular driver alive at its stop is good. -/
theorem isDrvGood_recOf_of_lt {t : ℝ≥0} {e : (ℝ≥0 → ℝ) × ℝ≥0∞} (he : IsRegularDriver e) (ht : (t : ℝ≥0∞) < e.2) :
    LocalExt.IsDrvGood (recHist (recOf t e)) := by
  refine LocalExt.isDrvGood_of_continuousOn (g := fun s => e.1 (min s t)) (T := t) ?_ (fun q => ?_) ?_
  · refine (he.1.mono fun s hs => lt_of_le_of_lt (by exact_mod_cast hs.2) ht).congr fun s hs => ?_
    simp only [min_eq_left hs.2]
  · rw [recOf_of_lt ht]
    change e.1 (min (((q : ℚ) : ℝ).toNNReal) t) = e.1 (min (min (q : ℝ≥0) t) t)
    rw [min_eq_left (min_le_right _ _), toNNReal_ratCast_nnrat]
  · simp only [zero_le, min_eq_left]
    exact he.2.1

/-- **The continuation is launched as soon as the first piece is alive at its own stop `t₀`**: the first piece then
ends at an interior tip, from which the next ordinary instruction always launches (`ExplState.flowStep`). -/
theorem mem_launchOne_of_lt {ω : Ω} (h0 : (t₀ : ℝ≥0∞) < (E 0 ω).2) : ω ∈ launchOne κ b jumps θ₀ t₀ θ r E := by
  have hst : stStatus (ExplState.launch (ExplState.init 0) 0 (E 0 ω) θ₀ (t₀ : ℝ≥0∞)) = stTip := by
    rw [(launch_eq_of_ne_top (ExplState.init 0) 0 (E 0 ω) θ₀ (t₀ : ℝ≥0∞)
      (ne_top_of_le_ne_top ENNReal.coe_ne_top (min_le_left _ _))).2.2.2.2.1]
    simp only [lStatus, h0, ↓reduceIte]
  have hfs : ∀ s : ExplState, stStatus s = stTip → ∀ D : (ℝ≥0 → ℝ) × ℝ≥0∞,
      ExplState.flowStep κ b false s 1 D θ (r : ℝ≥0∞) = ExplState.launch s 1 D θ (r : ℝ≥0∞) := by
    rintro ⟨pieces, arcs, retained, launches, chart, status, pt, angle, recR, recL⟩ hs D
    change status = stTip at hs
    subst hs
    rfl
  change (ExplState.flowStep κ b false (ExplState.launch (ExplState.init 0) 0 (E 0 ω) θ₀ (t₀ : ℝ≥0∞)) 1 (E 1 ω) θ
    (r : ℝ≥0∞)).2.2.2.1 1 ≠ none
  rw [hfs _ hst, launches_launch, Function.update_self]
  exact Option.some_ne_none _

/-- **The good event holds as soon as both pieces are alive at their stops** (for regular drivers). -/
theorem mem_goodEv_of_lt (hreg : ∀ j ω, IsRegularDriver (E j ω)) {ω : Ω} (h0 : (t₀ : ℝ≥0∞) < (E 0 ω).2)
    (h1 : (r : ℝ≥0∞) < (E 1 ω).2) : ω ∈ goodEv κ b jumps θ₀ t₀ θ r E := by
  have hL := mem_launchOne_of_lt (κ := κ) (b := b) (jumps := jumps) (θ₀ := θ₀) (θ := θ) (r := r) h0
  refine ⟨hL, ?_⟩
  change recsTwo κ b jumps θ₀ t₀ θ r E ω ∈ goodRec
  have e0 : recsTwo κ b jumps θ₀ t₀ θ r E ω 0 = recOf t₀ (E 0 ω) := pastMap_two_zero ω
  have e1 : recsTwo κ b jumps θ₀ t₀ θ r E ω 1 = recOf r (E 1 ω) := pastMap_two_one hL
  refine ⟨?_, ?_, ?_⟩
  · rw [e0, recOf_of_lt h0]
  · rw [e1, recOf_of_lt h1]
  · rw [e0]
    exact isDrvGood_recOf_of_lt (hreg 0 ω) h0

/-- **On the good event the two records are read off the concatenated record driver.** -/
theorem recsTwo_eq_recsOfDriver (hreg : ∀ j ω, IsRegularDriver (E j ω)) {ω : Ω}
    (hω : ω ∈ goodEv κ b jumps θ₀ t₀ θ r E) :
    recsTwo κ b jumps θ₀ t₀ θ r E ω = recsOfDriver t₀ r
      (catPath (recW (recsTwo κ b jumps θ₀ t₀ θ r E ω 0)) t₀ (recW (recsTwo κ b jumps θ₀ t₀ θ r E ω 1))) := by
  have h0 : recsTwo κ b jumps θ₀ t₀ θ r E ω 0 = recOf t₀ (E 0 ω) := pastMap_two_zero ω
  have h1 : recsTwo κ b jumps θ₀ t₀ θ r E ω 1 = recOf r (E 1 ω) := pastMap_two_one hω.1
  have hz0 := lt_zeta_zero_of_mem_goodEv hω
  have hz1 := lt_zeta_one_of_mem_goodEv hω
  have hW0 : ∀ s, recW (recOf t₀ (E 0 ω)) s = (E 0 ω).1 (min s t₀) :=
    recW_recOf_of_lt (hreg 0 ω) hz0 (isDrvGood_of_mem_goodEv hω)
  have hW1 : ∀ s, recW (recOf r (E 1 ω)) s = (E 1 ω).1 (min s r) :=
    recW_recOf_of_lt (hreg 1 ω) hz1 (isDrvGood_recOf_of_lt (hreg 1 ω) hz1)
  funext i
  fin_cases i
  · change recsTwo κ b jumps θ₀ t₀ θ r E ω 0 = recsOfDriver t₀ r
      (catPath (recW (recsTwo κ b jumps θ₀ t₀ θ r E ω 0)) t₀ (recW (recsTwo κ b jumps θ₀ t₀ θ r E ω 1))) 0
    rw [h0, h1]
    change recOf t₀ (E 0 ω) = ((fun q : ℚ => catPath (recW (recOf t₀ (E 0 ω))) t₀ (recW (recOf r (E 1 ω)))
      (min (q : ℝ).toNNReal t₀)), (t₀ : ℝ≥0∞), false)
    conv_lhs => rw [recOf_of_lt hz0]
    congr 1
    funext q
    rw [catPath_of_le (min_le_right _ _), hW0, min_eq_left (min_le_right _ _)]
  · change recsTwo κ b jumps θ₀ t₀ θ r E ω 1 = recsOfDriver t₀ r
      (catPath (recW (recsTwo κ b jumps θ₀ t₀ θ r E ω 0)) t₀ (recW (recsTwo κ b jumps θ₀ t₀ θ r E ω 1))) 1
    rw [h0, h1]
    change recOf r (E 1 ω) = ((fun q : ℚ => catPath (recW (recOf t₀ (E 0 ω))) t₀ (recW (recOf r (E 1 ω)))
      (t₀ + min (q : ℝ).toNNReal r) - catPath (recW (recOf t₀ (E 0 ω))) t₀ (recW (recOf r (E 1 ω))) t₀),
      (r : ℝ≥0∞), false)
    conv_lhs => rw [recOf_of_lt hz1]
    congr 1
    funext q
    rw [catPath_of_le le_rfl]
    set m : ℝ≥0 := min (q : ℝ).toNNReal r with hm
    rcases eq_or_ne m 0 with hm0 | hm0
    · rw [hm0, add_zero, catPath_of_le le_rfl, sub_self, (hreg 1 ω).2.1]
    · have hlt : ¬ t₀ + m ≤ t₀ := fun h => hm0 (le_antisymm (by simpa using h) zero_le)
      simp only [catPath, hlt, ↓reduceIte, add_tsub_cancel_left]
      rw [hW1, min_eq_left (min_le_right _ _)]

/-- **Almost surely the two records are a Borel function of the stopped path history** of a generating trace `α`
of the concatenated record driver (Lemma 6.2's marks). -/
theorem ae_recsTwo_eq [MeasurableSpace Ω] {P : Measure Ω} (hreg : ∀ j ω, IsRegularDriver (E j ω))
    (hT : 0 < t₀ + r) (hgood : ∀ᵐ ω ∂P, ω ∈ goodEv κ b jumps θ₀ t₀ θ r E) {αc : Ω → ℝ≥0 → ℂ}
    (htr : ∀ᵐ ω ∂P, ∃ (W' : ℝ≥0 → ℝ) (ζ' : ℝ≥0∞), ((t₀ + r : ℝ≥0) : ℝ≥0∞) < ζ' ∧
      IsGeneratingTrace W' ζ' (αc ω) ∧ ∀ s : ℝ≥0, s ≤ t₀ + r →
        W' s = catPath (recW (recsTwo κ b jumps θ₀ t₀ θ r E ω 0)) t₀ (recW (recsTwo κ b jumps θ₀ t₀ θ r E ω 1)) s) :
    ∀ᵐ ω ∂P, recsTwo κ b jumps θ₀ t₀ θ r E ω =
      recsOfDriver t₀ r (histDriver (t₀ + r) (Sec6.histOf (Sec6.pathCoord (αc ω)) ((t₀ + r : ℝ≥0) : ℝ≥0∞))) := by
  filter_upwards [hgood, htr] with ω hω hωt
  obtain ⟨W', ζ', hlt, hW', hagree⟩ := hωt
  have hc0 : Continuous (recW (recsTwo κ b jumps θ₀ t₀ θ r E ω 0)) := LocalExt.continuous_histDrv _
  have hc1 : Continuous (recW (recsTwo κ b jumps θ₀ t₀ θ r E ω 1)) := LocalExt.continuous_histDrv _
  have hWc := continuous_catPath (T₀ := t₀) hc0 hc1 (LocalExt.histDrv_zero _)
  have hWc0 := catPath_zero (T₀ := t₀) (w₁ := recW (recsTwo κ b jumps θ₀ t₀ θ r E ω 1))
    (LocalExt.histDrv_zero (recHist (recsTwo κ b jumps θ₀ t₀ θ r E ω 0)))
  have hη : IsGeneratingTrace (catPath (recW (recsTwo κ b jumps θ₀ t₀ θ r E ω 0)) t₀
      (recW (recsTwo κ b jumps θ₀ t₀ θ r E ω 1))) ((t₀ + r : ℝ≥0) : ℝ≥0∞) (αc ω) :=
    IsGeneratingTrace.congr_lt (hW'.mono_horizon hlt.le) fun t ht =>
      (hagree t (le_of_lt (by exact_mod_cast ht))).symm
  rw [recsTwo_eq_recsOfDriver hreg hω]
  exact recsOfDriver_congr fun s hs => (histDriver_eq hWc hWc0 hT hη hs).symm

end Records

/-! ### The marked criterion for marks that are almost surely marks -/

section Marked

variable {Ω : Type*} {ℋ ℋ' : MeasurableSpace Ω} [mΩ : MeasurableSpace Ω] {P : Measure Ω}

/-- **The history-marked avoidance criterion passes to marks that are, up to null sets, marks**: if every event of
`ℋ'` is almost surely equal to an event of `ℋ`, the criterion for `ℋ` gives the criterion for `ℋ'` (conditional
probabilities of almost surely equal events agree). -/
theorem isHistoryAvoidanceLocal_of_ae_le {A : Ω → Set ℂ}
    {X : Ω → LQGMetric.DistOn upperHalfPlaneOpens} (hloc : WholeField.IsHistoryAvoidanceLocal ℋ A X P)
    (hle : ∀ F, MeasurableSet[ℋ'] F → ∃ F', MeasurableSet[ℋ] F' ∧ F =ᵐ[P] F') :
    WholeField.IsHistoryAvoidanceLocal ℋ' A X P := by
  intro U G hUH hG hd F hF
  obtain ⟨F', hF', hFF'⟩ := hle F hF
  obtain ⟨g, hg, hge⟩ := hloc U G hUH hG hd F' hF'
  refine ⟨g, hg, ?_⟩
  have hs : ({ω | Disjoint (A ω) (U : Set ℂ)} ∩ F : Set Ω) =ᵐ[P]
      ({ω | Disjoint (A ω) (U : Set ℂ)} ∩ F' : Set Ω) := EventuallyEqSet.inter (EventuallyEq.refl _ _) hFF'
  exact (condExp_congr_ae (indicator_ae_eq_of_ae_eq_set hs)).trans hge

end Marked

/-! ### `hmark`: the marked locality of the range for the two retained records -/

section Main

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]

omit mΩ [IsProbabilityMeasure P] in
/-- The explored set of one path stopped at the deterministic time `T` is its range on `[0, T]` in `ℍ`. -/
theorem explored_const (αc : Ω → ℝ≥0 → ℂ) (T : ℝ≥0) (ω : Ω) :
    Sec6.explored (fun _ : Fin 1 => αc) (fun _ _ => (T : ℝ≥0∞)) ω = αc ω '' Icc 0 T ∩ H := by
  have e : {t : ℝ≥0 | (t : ℝ≥0∞) ≤ T} = Icc 0 T := by
    ext t
    simp only [mem_ofPred_eq, ENNReal.coe_le_coe, mem_Icc, zero_le, true_and]
  simp only [Sec6.explored, iUnion_const, e]

/-- The range of a continuous path on `[0, T]` is a hitting-measurable random set. -/
theorem measurable_range {αc : Ω → ℝ≥0 → ℂ} (hαc : ∀ ω, Continuous (αc ω))
    (hαm : ∀ t, Measurable fun ω => αc ω t) (T : ℝ≥0) :
    Measurable[mΩ, hittingSigma] fun ω => αc ω '' Icc 0 T ∩ H := by
  have h := Sec6.measurable_explored (η := fun _ : Fin 1 => αc) (τ := fun _ _ => (T : ℝ≥0∞))
    (fun _ => hαc) (fun _ => hαm) (fun _ => measurable_const)
  rwa [show Sec6.explored (fun _ : Fin 1 => αc) (fun _ _ => (T : ℝ≥0∞)) = fun ω => αc ω '' Icc 0 T ∩ H from
    funext (explored_const αc T)] at h

/-- **Lemma 6.2 for the range of one path at a deterministic time** (local set). -/
theorem isLocalSet_range {X : Ω → LQGMetric.DistOn upperHalfPlaneOpens}
    (hX : LQGMetric.IsZeroBoundaryGFF upperHalfPlaneOpens X P) {αc : Ω → ℝ≥0 → ℂ}
    (hαc : ∀ ω, Continuous (αc ω)) (hα0 : ∀ ω, αc ω 0 = 0) (hαm : ∀ t, Measurable fun ω => αc ω t)
    (hdet : ∀ t : ℝ≥0, ∃ f : LQGMetric.DistOn upperHalfPlaneOpens → ℂ, Measurable f ∧
      (fun ω => αc ω t) =ᵐ[P] fun ω => f (X ω))
    (hloc : Sec6.IsEntranceHistoryLocal αc X P) (T : ℝ≥0) :
    IsLocalSet (fun ω => αc ω '' Icc 0 T ∩ H) X P := by
  have h := Sec6.isLocalSet_explored (P := P) (η := fun _ : Fin 1 => αc) (x := fun _ => (0 : ℂ))
    (τ := fun _ _ => (T : ℝ≥0∞)) (S := fun _ _ _ => (T : ℝ≥0∞)) hX (fun _ => hαc) (fun _ => hα0)
    (fun _ => hαm) (fun _ => hdet) (fun _ => hloc) (fun _ => measurable_const) (fun _ _ _ _ _ => rfl)
    (fun _ _ => rfl) (fun _ => measurable_const) (Eventually.of_forall fun ω => ?_)
  · rwa [show Sec6.explored (fun _ : Fin 1 => αc) (fun _ _ => (T : ℝ≥0∞)) = fun ω => αc ω '' Icc 0 T ∩ H from
      funext (explored_const αc T)] at h
  · rw [explored_const, sdiff_inter_self_eq_sdiff]
    exact QuantumZipper.isOpen_H.sdiff (isCompact_Icc.image (hαc ω)).isClosed

/-- **`hmark`: the range of the angle-varying path through `t₀ + r` is a local set marked by the two retained records**
(the source's "Retain the two full marked local sets", for the angle-varying path with its stopped canonical
records). Inputs: Lemma 6.2's data for a continuous version `αc` of the path (field determination at each time,
history-sensitive locality at first entrance times), almost surely the good event, and almost surely `αc` is a
generating trace (beyond `t₀ + r`) of a driver that agrees with the concatenated record driver on `[0, t₀ + r]`. -/
theorem isHistoryAvoidanceLocal_pastTwo {κ : ℝ} {b : ℝ → ℝ} {jumps : Finset ℝ} {θ₀ θ : ℝ} {t₀ r : ℝ≥0}
    {E : ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞} (hreg : ∀ j ω, IsRegularDriver (E j ω)) (hT : 0 < t₀ + r)
    (hgood : ∀ᵐ ω ∂P, ω ∈ goodEv κ b jumps θ₀ t₀ θ r E) {X : Ω → LQGMetric.DistOn upperHalfPlaneOpens}
    (hXm : Measurable X) {αc : Ω → ℝ≥0 → ℂ} (hαc : ∀ ω, Continuous (αc ω)) (hα0 : ∀ ω, αc ω 0 = 0)
    (hαm : ∀ t, Measurable fun ω => αc ω t)
    (hdet : ∀ t : ℝ≥0, ∃ f : LQGMetric.DistOn upperHalfPlaneOpens → ℂ, Measurable f ∧
      (fun ω => αc ω t) =ᵐ[P] fun ω => f (X ω))
    (hloc : Sec6.IsEntranceHistoryLocal αc X P)
    (htr : ∀ᵐ ω ∂P, ∃ (W' : ℝ≥0 → ℝ) (ζ' : ℝ≥0∞), ((t₀ + r : ℝ≥0) : ℝ≥0∞) < ζ' ∧
      IsGeneratingTrace W' ζ' (αc ω) ∧ ∀ s : ℝ≥0, s ≤ t₀ + r →
        W' s = catPath (recW (recsTwo κ b jumps θ₀ t₀ θ r E ω 0)) t₀ (recW (recsTwo κ b jumps θ₀ t₀ θ r E ω 1)) s) :
    WholeField.IsHistoryAvoidanceLocal (pastTwo κ b jumps θ₀ t₀ θ r E) (fun ω => αc ω '' Icc 0 (t₀ + r) ∩ H) X P := by
  have h1 := Sec6.isHistoryAvoidanceLocal_explored (P := P) (η := fun _ : Fin 1 => αc) (x := fun _ => (0 : ℂ))
    (τ := fun _ _ => ((t₀ + r : ℝ≥0) : ℝ≥0∞)) (S := fun _ _ _ => ((t₀ + r : ℝ≥0) : ℝ≥0∞)) hXm (fun _ => hαc)
    (fun _ => hα0) (fun _ => hαm) (fun _ => hdet) (fun _ => hloc) (fun _ => measurable_const)
    (fun _ _ _ _ _ => rfl) (fun _ _ => rfl)
  rw [show Sec6.explored (fun _ : Fin 1 => αc) (fun _ _ => ((t₀ + r : ℝ≥0) : ℝ≥0∞)) =
    fun ω => αc ω '' Icc 0 (t₀ + r) ∩ H from funext (explored_const αc (t₀ + r))] at h1
  refine isHistoryAvoidanceLocal_of_ae_le h1 fun F hF => ?_
  have hF' : MeasurableSet[MeasurableSpace.comap (recsTwo κ b jumps θ₀ t₀ θ r E) inferInstance] F := by
    rw [← pastSigma_eq_comap]
    exact hF
  obtain ⟨B, hB, rfl⟩ := hF'
  have hΦ : Measurable fun y : Fin 1 → Sec6.Hist => recsOfDriver t₀ r (histDriver (t₀ + r) (y 0)) :=
    (measurable_recsOfDriver t₀ r).comp ((measurable_histDriver _).comp (measurable_pi_apply 0))
  refine ⟨(fun ω (_ : Fin 1) => Sec6.histOf (Sec6.pathCoord (αc ω)) ((t₀ + r : ℝ≥0) : ℝ≥0∞)) ⁻¹'
    ((fun y : Fin 1 → Sec6.Hist => recsOfDriver t₀ r (histDriver (t₀ + r) (y 0))) ⁻¹' B), ⟨_, hΦ hB, rfl⟩, ?_⟩
  filter_upwards [ae_recsTwo_eq hreg hT hgood htr] with ω hω
  change (recsTwo κ b jumps θ₀ t₀ θ r E ω ∈ B) = (recsOfDriver t₀ r (histDriver (t₀ + r)
    (Sec6.histOf (Sec6.pathCoord (αc ω)) ((t₀ + r : ℝ≥0) : ℝ≥0∞))) ∈ B)
  rw [hω]

omit [IsProbabilityMeasure P] mΩ in
/-- **`hAD`: the domain after the stopped continuation is a component of the complement of the range.** If `α` is a
generating trace (beyond `T = t₀ + r`) of a driver agreeing with the concatenated record driver on `[0, T]`, the domain
of the two-stage chart is the unbounded component of `ℍ ∖ α([0, T])`, so it lies in the complement of the range and
the rest of the complement is open. -/
theorem twoChart_dom_subset {w₀ w₁ : ℝ≥0 → ℝ} (h₀ : Continuous w₀) (h00 : w₀ 0 = 0) (h₁ : Continuous w₁)
    (h10 : w₁ 0 = 0) {t₀ r : ℝ≥0} {W' : ℝ≥0 → ℝ} {ζ' : ℝ≥0∞} {α : ℝ≥0 → ℂ}
    (hlt : ((t₀ + r : ℝ≥0) : ℝ≥0∞) < ζ') (hα : IsGeneratingTrace W' ζ' α)
    (hagree : ∀ s : ℝ≥0, s ≤ t₀ + r → W' s = catPath w₀ t₀ w₁ s) :
    ((twoChart w₀ t₀ w₁ r).dom : Set ℂ) ⊆ H \ (α '' Icc 0 (t₀ + r) ∩ H) ∧
      IsOpen ((H \ (α '' Icc 0 (t₀ + r) ∩ H)) \ (twoChart w₀ t₀ w₁ r).dom) := by
  have hW'c := SideHeight.continuousOn_of_isGeneratingTrace hα
  obtain ⟨t₂, hTt₂, ht₂⟩ := exists_real_btwn_of_lt hlt
  have hfz := continuous_frozenDrive_of_lt hW'c ht₂
  have hK1 : fwdHull (fun s : ℝ => W' s.toNNReal) ((t₀ + r : ℝ≥0) : ℝ) =
      fwdHull (frozenDrive W' t₂) ((t₀ + r : ℝ≥0) : ℝ) :=
    fwdHull_eq_of_eqOn (t₀ + r).coe_nonneg hTt₂ fun x hx => (frozenDrive_eq hx).symm
  have hK2 : fwdHull (Ito.rpath (catPath w₀ t₀ w₁)) ((t₀ + r : ℝ≥0) : ℝ) =
      fwdHull (frozenDrive W' t₂) ((t₀ + r : ℝ≥0) : ℝ) := by
    refine QuantumZipper.Thm14FromThm13.fwdHull_eq_of_eqOn (continuous_rpath_catPath h₀ h₁ h10) hfz
      (t₀ + r).coe_nonneg fun x hx => ?_
    rw [frozenDrive_eq ⟨hx.1, hx.2.trans hTt₂.le⟩]
    exact (hagree _ (Real.toNNReal_le_iff_le_coe.2 hx.2)).symm
  obtain ⟨⟨z, -, hcomp⟩, -⟩ := hα.2.2 (t₀ + r) hlt
  have hdom : ((twoChart w₀ t₀ w₁ r).dom : Set ℂ) = connectedComponentIn (H \ α '' Icc 0 (t₀ + r)) z := by
    rw [hcomp, twoChart_dom_eq h₀ h00 h₁ h10]
    ext w
    rw [SetLike.mem_coe, mem_dom_catChart_iff h₀ h00 h₁ h10, hK2, ← hK1]
  have hHA : H \ (α '' Icc 0 (t₀ + r) ∩ H) = H \ α '' Icc 0 (t₀ + r) := sdiff_inter_self_eq_sdiff
  rw [hHA, hdom]
  refine ⟨connectedComponentIn_subset _ _, Sec6.Prop65.isOpen_diff_connectedComponentIn ?_ z⟩
  have hK : IsCompact (α '' Icc 0 (t₀ + r)) := isCompact_Icc.image_of_continuousOn
    (hα.2.1.mono fun t ht => (ENNReal.coe_le_coe.2 ht.2).trans hlt.le)
  exact QuantumZipper.isOpen_H.sdiff hK.isClosed

end Main

/-! ### (S) for the angle-varying path from Lemma 6.2's inputs -/

section Stage

universe u

variable {κ : ℝ} {b : ℝ → ℝ} {jumps : Finset ℝ} {Ω : Type u} [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω]
  {P : Measure Ω} [IsProbabilityMeasure P] {h : Ω → LQGMetric.DistOn upperHalfPlaneOpens} {θ₀ θ : ℝ}
  {t₀ : ℝ≥0} {E : ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞}

/-- **(S) for the angle-varying path, with the marked locality discharged** (proof of Aux. lemma 130, p. 411: "Retain
the two full marked local sets […] In each own chart the right-side height is `λ − θχ`, with its inherited
derivative-logarithm lift"). Let `αc` be a continuous version of the two-angle path `η^{t₀,∞}_{θ₀,θ}` with Lemma 6.2's
inputs for the centred field (field determination at each time and history-sensitive locality at first entrance
times), almost surely a generating trace, beyond `t₀ + r`, of a driver agreeing with the concatenated record driver on
`[0, t₀ + r]`, and let the good event be almost sure. Then for every version `g` of the local-set mean of its range
`A = αc([0, t₀ + r]) ∩ ℍ`, almost surely on the good event, every harmonic representative `v` of `g`, every injective
generating trace `α` of the concatenated record driver alive past `t₀ + r` and every `α(t₁) ∈ ℍ`, `t₀ < t₁`:
`HasSideHeights κ θ α 0 W' (t₀ + r) (α t₁) v u₀` (STRIPSYS16's `ae_hasSideHeights_stage` with `hloc`, `hmark`, `hAD`
proved). -/
theorem ae_hasSideHeights_stage_of_lemma62 (hκ : 0 < κ) (hb : IsPiecewiseConstantBoundaryData b jumps)
    (hh : IsGFFWithBoundaryData P h b jumps) (hS : IsStagedHistory κ b jumps P h (StripSys.twoAngleSpec θ₀ t₀ θ) E)
    (hreg : ∀ j ω, IsRegularDriver (E j ω)) (r : ℝ≥0) (hT : 0 < t₀ + r) {u₀ : ℂ → ℝ}
    (hu₀ : IsBoundedHarmonicExtension b jumps u₀) (hgood : ∀ᵐ ω ∂P, ω ∈ goodEv κ b jumps θ₀ t₀ θ r E)
    {αc : Ω → ℝ≥0 → ℂ} (hαc : ∀ ω, Continuous (αc ω)) (hα0 : ∀ ω, αc ω 0 = 0)
    (hαm : ∀ t, Measurable fun ω => αc ω t)
    (hdet : ∀ t : ℝ≥0, ∃ f : LQGMetric.DistOn upperHalfPlaneOpens → ℂ, Measurable f ∧
      (fun ω => αc ω t) =ᵐ[P] fun ω => f (WholeField.centredField h u₀ ω))
    (hloc : Sec6.IsEntranceHistoryLocal αc (WholeField.centredField h u₀) P)
    (htr : ∀ᵐ ω ∂P, ∃ (W' : ℝ≥0 → ℝ) (ζ' : ℝ≥0∞), ((t₀ + r : ℝ≥0) : ℝ≥0∞) < ζ' ∧
      IsGeneratingTrace W' ζ' (αc ω) ∧ ∀ s : ℝ≥0, s ≤ t₀ + r →
        W' s = catPath (recW (recsTwo κ b jumps θ₀ t₀ θ r E ω 0)) t₀ (recW (recsTwo κ b jumps θ₀ t₀ θ r E ω 1)) s)
    {g : Ω → LQGMetric.DistOn upperHalfPlaneOpens}
    (hg : LocalSets.IsLocalSetMean (fun ω => αc ω '' Icc 0 (t₀ + r) ∩ H) (WholeField.centredField h u₀) P g) :
    ∀ᵐ ω ∂P, ω ∈ goodEv κ b jumps θ₀ t₀ θ r E → ∀ v : ℂ → ℝ,
      InnerProductSpace.HarmonicOnNhd v (H \ (αc ω '' Icc 0 (t₀ + r) ∩ H)) →
      (∀ φ : LQGMetric.TestOn upperHalfPlaneOpens, tsupport φ ⊆ H \ (αc ω '' Icc 0 (t₀ + r) ∩ H) →
        g ω φ = ∫ z, v z * φ z) →
      ∀ (W' : ℝ≥0 → ℝ) (α : ℝ≥0 → ℂ) (ζ : ℝ≥0∞), IsGeneratingTrace W' ζ α →
        ContinuousOn W' {s | (s : ℝ≥0∞) < ζ} → W' 0 = 0 →
        (∀ s : ℝ≥0, s ≤ t₀ + r → W' s = catPath (recW (recsTwo κ b jumps θ₀ t₀ θ r E ω 0)) t₀
          (recW (recsTwo κ b jumps θ₀ t₀ θ r E ω 1)) s) →
        InjOn α {t | (t : ℝ≥0∞) ≤ ζ} → ((t₀ + r : ℝ≥0) : ℝ≥0∞) < ζ →
        ∀ t₁ : ℝ≥0, t₀ < t₁ → (t₁ : ℝ≥0∞) < ζ → α t₁ ∈ H →
          StripGeom.HasSideHeights κ θ α 0 W' (t₀ + r) (α t₁) v u₀ := by
  have hh0 := Restart.isZeroBoundaryGFF_centredField_of_isGFFWithBoundaryData hh hu₀
  have hmark := isHistoryAvoidanceLocal_pastTwo hreg hT hgood hh0.measurable hαc hα0 hαm hdet hloc htr
  have hloc' := isLocalSet_range hh0 hαc hα0 hαm hdet hloc (t₀ + r)
  have hA := measurable_range hαc hαm (t₀ + r)
  have hAD : ∀ᵐ ω ∂P, ω ∈ goodEv κ b jumps θ₀ t₀ θ r E →
      ((stopChart κ b jumps θ₀ t₀ θ r E ω).dom : Set ℂ) ⊆ H \ (αc ω '' Icc 0 (t₀ + r) ∩ H) ∧
        IsOpen ((H \ (αc ω '' Icc 0 (t₀ + r) ∩ H)) \ (stopChart κ b jumps θ₀ t₀ θ r E ω).dom) := by
    filter_upwards [htr] with ω hω _
    obtain ⟨W', ζ', hlt, hW', hagree⟩ := hω
    exact twoChart_dom_subset (LocalExt.continuous_histDrv _) (LocalExt.histDrv_zero _)
      (LocalExt.continuous_histDrv _) (LocalExt.histDrv_zero _) hlt hW' hagree
  exact ae_hasSideHeights_stage hκ hb hh hS hreg r hu₀ hA hloc' hmark hAD hg

end Stage

end StripMark

end Sec7

end InteractingSLE
