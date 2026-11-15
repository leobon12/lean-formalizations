/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec5.Aux61MarksRead
import InteractingSLE.Spec.Sec5.Aux61SlitWSelected
import InteractingSLE.Spec.Sec5.Aux61GHistAccess
import QuantumZipper.Proofs.Thm18.G1PkgPath

/-!
# The code's driver read from the stopped record (the driver half of `code_le`)

Packet PROVE-AUX61-MARKS. For the selected-access restart code whose chart is read from the time-`0` record
(`cc x = c (y, stopRec t₀ g)`) and whose restarted path is the record's trace (`ρ x u = histTrace 0 g (t₀ + u)`) —
the interface of SLITW's `exists_selectedAccessRule` — the **driver of the code at every alive capacity time `r'` is a
measurable function of the record stopped at the glued stop `capacityRule c t₀ r` for every `r ≥ r'`**:

* the **record capacity path** `recPath c t₀ p u`: the record's chart point at the physical time
  `capacityRule c t₀ u p − t₀` (read by left dyadic limits), measurable in the record; its frozen continuous
  regularization `recPathReg` (QuantumZipper's `pathReg` on the real and imaginary parts); the **record driver**
  `recDriver c t₀ r' p = fcReadDriver recPathReg r'` (the mapping-out difference quotient of the landed driver
  reconstruction), measurable;
* on the live event the record capacity path is the code's trace (`recPath_eq_trace`, via SLITW's
  `capacityRule_eq_accessTime`, `prefixPoint_eq_accessPath`, `accessExitCode_trace_eq`), so the record driver is the
  code's driver (`driver_eq_recDriver`; `fcReadDriver_eq` for the code's generating trace, `fcReadDriver_congr`);
* the record driver at `r'` does not change when the record is stopped at a time after `capacityRule c t₀ r'`
  (`recDriver_stopRec`; Galmarino's property of the capacity rule), and `capacityRule c t₀ r` is such a time for every
  `r ≥ r'`, alive or not (`le_capacityRule_of_alive`);
* hence `driver_eq_recDriver_stopAt`, and the generator split `codeFiltration_le_nullMarks_of_alive`: the raw code
  σ-algebra at `r` is in the completed marks once the **aliveness events** `{r' < life}`, `r' ≤ r`, are.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology
open QuantumZipper (H)
open scoped NNReal ENNReal

namespace InteractingSLE.Sec5.Aux61Marks

open Aux61ULoc LawUnique Restart.FlowStopIdentG Aux61FibData Aux61GInst Aux61Fib
open Aux61SlitW (prefixPoint capacityRule fullRecord readChart accessTime)
open Restart.FCPlumb (fcReadDriver fcPrefixMap)

universe u

/-! ### Congruence of the driver reconstruction -/

/-- **The driver reconstruction at `q` only reads the path on `[0, q]`.** -/
theorem fcReadDriver_congr {Ω Ω' : Type*} {Γ : Ω → ℝ≥0 → ℂ} {Γ' : Ω' → ℝ≥0 → ℂ} {ω : Ω} {ω' : Ω'} {q : ℝ≥0}
    (h : ∀ t ≤ q, Γ ω t = Γ' ω' t) : fcReadDriver Γ q ω = fcReadDriver Γ' q ω' := by
  classical
  have himg : ∀ q' ≤ q, Γ ω '' Icc 0 q' = Γ' ω' '' Icc 0 q' := fun q' hq' =>
    image_congr fun t ht => h t (ht.2.trans hq')
  have hP : ∀ q' ≤ q, ∀ z, fcPrefixMap Γ q' z ω = fcPrefixMap Γ' q' z ω' := by
    intro q' hq' z
    simp only [fcPrefixMap, indicator_apply, mem_ofPred_eq, himg q' hq']
  unfold fcReadDriver
  by_cases hq : q = 0
  · simp only [hq, ↓reduceIte]
  · simp only [hq, ↓reduceIte]
    congr 1
    funext N
    congr 1
    funext k
    have hk : ((q : ℝ) - 1 / ((k : ℝ) + 1)).toNNReal ≤ q := by
      rw [Real.toNNReal_le_iff_le_coe]
      have : (0 : ℝ) ≤ 1 / ((k : ℝ) + 1) := by positivity
      linarith
    rw [hP q le_rfl, hP _ hk]

/-! ### The record capacity path and the record driver -/

section Record

variable {𝒴 : Type*} [MeasurableSpace 𝒴] {nL nR : ℕ}

/-- **The record's physical code time** at capacity time `u`: the capacity rule minus the restart time. -/
def recTime (c : 𝒴 × HistorySpace nL nR → Chart) (t₀ u : ℝ≥0) (p : 𝒴 × HistorySpace nL nR) : ℝ≥0 :=
  (capacityRule c t₀ u p).toNNReal - t₀

/-- **The record capacity path**: the record's chart point at the physical code time, read by left dyadic limits. -/
def recPath (c : 𝒴 × HistorySpace nL nR → Chart) (t₀ : ℝ≥0) (p : 𝒴 × HistorySpace nL nR) (u : ℝ≥0) : ℂ :=
  limUnder atTop fun n => prefixPoint c t₀ p.1 (fullRecord p.2) (LP.dyadicBelow n (recTime c t₀ u p))

/-- The record capacity path frozen after `R`, regularized to a continuous path (real and imaginary parts). -/
def recPathReg₀ (c : 𝒴 × HistorySpace nL nR → Chart) (t₀ R : ℝ≥0) (p : 𝒴 × HistorySpace nL nR) (t : ℝ≥0) : ℂ :=
  ⟨QuantumZipper.Thm18Asm.G1Pkg.pathReg (fun s => (recPath c t₀ p (min s R)).re) t,
    QuantumZipper.Thm18Asm.G1Pkg.pathReg (fun s => (recPath c t₀ p (min s R)).im) t⟩

/-- **The regularized record capacity path** (continuous, from `0`, for every record). -/
def recPathReg (c : 𝒴 × HistorySpace nL nR → Chart) (t₀ R : ℝ≥0) (p : 𝒴 × HistorySpace nL nR) (t : ℝ≥0) : ℂ :=
  recPathReg₀ c t₀ R p t - recPathReg₀ c t₀ R p 0

/-- **The record driver** at capacity time `R`: the driver reconstruction of the regularized record capacity path. -/
def recDriver (c : 𝒴 × HistorySpace nL nR → Chart) (t₀ R : ℝ≥0) (p : 𝒴 × HistorySpace nL nR) : ℝ :=
  fcReadDriver (recPathReg c t₀ R) R p

variable {c : 𝒴 × HistorySpace nL nR → Chart} (hc : IsMeasChart c) (t₀ : ℝ≥0)
include hc

theorem measurable_recTime (u : ℝ≥0) : Measurable (recTime c t₀ u) :=
  ((Aux61SlitW.measurable_capacityRule hc t₀ u).ennreal_toNNReal).sub measurable_const

/-- The record's chart point at a fixed physical time is measurable in the record. -/
theorem measurable_prefixPoint (v : ℝ≥0) :
    Measurable fun p : 𝒴 × HistorySpace nL nR => prefixPoint c t₀ p.1 (fullRecord p.2) v := by
  have hR : Measurable fun p : 𝒴 × HistorySpace nL nR => (p.1, stopRec t₀ (fullRecord p.2)) :=
    measurable_fst.prodMk (isRecordStop_stopRec.measurable.comp
      (measurable_const.prodMk (Aux61SlitW.measurable_fullRecord.comp measurable_snd)))
  have hc' : IsMeasChart (fun p : 𝒴 × HistorySpace nL nR => c (p.1, stopRec t₀ (fullRecord p.2))) :=
    ⟨fun z => hR (hc.dom z), fun z => (hc.fwd z).comp hR, fun z => (hc.lift z).comp hR⟩
  unfold prefixPoint
  refine Measurable.ite (MeasurableSet.const _) measurable_const ?_
  exact Aux61SlitW.measurable_readChart hc'
    ((measurable_histTrace 0 _).comp (Aux61SlitW.measurable_fullRecord.comp measurable_snd))

theorem measurable_recPath (u : ℝ≥0) : Measurable fun p : 𝒴 × HistorySpace nL nR => recPath c t₀ p u := by
  refine (StronglyMeasurable.limUnder fun n => ?_).measurable
  have hG : Measurable fun q : (𝒴 × HistorySpace nL nR) × ℕ =>
      prefixPoint c t₀ q.1.1 (fullRecord q.1.2) ((q.2 : ℝ≥0) / 2 ^ n) :=
    measurable_from_prod_countable_left fun k => by exact measurable_prefixPoint hc t₀ ((k : ℝ≥0) / 2 ^ n)
  have hI : Measurable fun p : 𝒴 × HistorySpace nL nR => LP.dyadicIdx n (recTime c t₀ u p) :=
    (LP.measurable_dyadicIdx n).comp (measurable_recTime hc t₀ u)
  exact (hG.comp (measurable_id.prodMk hI)).stronglyMeasurable

theorem measurable_recPathReg₀ (R t : ℝ≥0) :
    Measurable fun p : 𝒴 × HistorySpace nL nR => recPathReg₀ c t₀ R p t := by
  have hre : Measurable fun p : 𝒴 × HistorySpace nL nR => fun s : ℝ≥0 => (recPath c t₀ p (min s R)).re :=
    measurable_pi_iff.2 fun s => Complex.measurable_re.comp (measurable_recPath hc t₀ _)
  have him : Measurable fun p : 𝒴 × HistorySpace nL nR => fun s : ℝ≥0 => (recPath c t₀ p (min s R)).im :=
    measurable_pi_iff.2 fun s => Complex.measurable_im.comp (measurable_recPath hc t₀ _)
  have h1 := (measurable_pi_apply t).comp (QuantumZipper.Thm18Asm.G1Pkg.pathReg_spec.1.comp hre)
  have h2 := (measurable_pi_apply t).comp (QuantumZipper.Thm18Asm.G1Pkg.pathReg_spec.1.comp him)
  exact Complex.measurableEquivRealProd.symm.measurable.comp (h1.prodMk h2)

theorem measurable_recPathReg (R t : ℝ≥0) :
    Measurable fun p : 𝒴 × HistorySpace nL nR => recPathReg c t₀ R p t :=
  (measurable_recPathReg₀ hc t₀ R t).sub (measurable_recPathReg₀ hc t₀ R 0)

omit hc [MeasurableSpace 𝒴] in
theorem continuous_recPathReg (R : ℝ≥0) (p : 𝒴 × HistorySpace nL nR) : Continuous (recPathReg c t₀ R p) := by
  have h1 := QuantumZipper.Thm18Asm.G1Pkg.pathReg_spec.2.1 fun s => (recPath c t₀ p (min s R)).re
  have h2 := QuantumZipper.Thm18Asm.G1Pkg.pathReg_spec.2.1 fun s => (recPath c t₀ p (min s R)).im
  have h0 : Continuous (recPathReg₀ c t₀ R p) := by
    have e : recPathReg₀ c t₀ R p = fun t => (Complex.equivRealProdCLM.symm
        ((QuantumZipper.Thm18Asm.G1Pkg.pathReg (fun s => (recPath c t₀ p (min s R)).re) t,
          QuantumZipper.Thm18Asm.G1Pkg.pathReg (fun s => (recPath c t₀ p (min s R)).im) t)) : ℂ) := by
      funext t
      rfl
    rw [e]
    exact Complex.equivRealProdCLM.symm.continuous.comp (h1.prodMk h2)
  exact h0.sub continuous_const

omit hc [MeasurableSpace 𝒴] in
theorem recPathReg_zero (R : ℝ≥0) (p : 𝒴 × HistorySpace nL nR) : recPathReg c t₀ R p 0 = 0 :=
  sub_self _

/-- **The record driver is measurable.** -/
theorem measurable_recDriver (R : ℝ≥0) : Measurable (recDriver c t₀ R) :=
  Restart.FCPlumb.measurable_fcReadDriver (continuous_recPathReg t₀ R)
    (fun t => measurable_recPathReg hc t₀ R t) (recPathReg_zero t₀ R) R

end Record

theorem dyadicBelow_le (n : ℕ) (x : ℝ≥0) : LP.dyadicBelow n x ≤ x := by
  rcases eq_or_ne x 0 with rfl | hx
  · simp [LP.dyadicBelow, LP.dyadicIdx]
  · exact (LP.dyadicBelow_lt (pos_iff_ne_zero.2 hx) n).le

/-! ### The record driver only reads the record up to the glued stop -/

section Stop

variable {𝒴 : Type*} [MeasurableSpace 𝒴] {nL nR : ℕ} {c : 𝒴 × HistorySpace nL nR → Chart} {t₀ : ℝ≥0}
  {y : 𝒴} {g : HistorySpace nL nR} {t : ℝ≥0}

omit [MeasurableSpace 𝒴] in
/-- The record's chart point at a physical time `t₀ + v ≤ t` only reads the record stopped at `t`. -/
theorem prefixPoint_stopRec {v : ℝ≥0} (hv : t₀ + v ≤ t) :
    prefixPoint c t₀ y (fullRecord (stopRec t g)) v = prefixPoint c t₀ y (fullRecord g) v := by
  have ht₀ : t₀ ≤ t := le_self_add.trans hv
  have hst : stopRec t₀ (stopRec t g) = stopRec t₀ g := isRecordStop_stopRec.stop_stop t₀ t g ht₀
  unfold prefixPoint
  rw [Aux61SlitW.stopRec_fullRecord, Aux61SlitW.stopRec_fullRecord, hst, Aux61SlitW.histTrace_fullRecord,
    Aux61SlitW.histTrace_fullRecord, histTrace_stopRec_of_le hv]

/-- **The record capacity path at `u` only reads the record stopped at a time after the rule `capacityRule u`.** -/
theorem recPath_stopRec {u : ℝ≥0} (hut : capacityRule c t₀ u (y, g) ≤ t) :
    recPath c t₀ (y, stopRec t g) u = recPath c t₀ (y, g) u := by
  have hG : capacityRule c t₀ u (y, stopRec t g) = capacityRule c t₀ u (y, g) :=
    Aux61SlitW.isGalmarinoRule_capacityRule c t₀ u y g t (Or.inr hut)
  have hT : recTime c t₀ u (y, stopRec t g) = recTime c t₀ u (y, g) := by
    simp only [recTime, hG]
  have hfin : capacityRule c t₀ u (y, g) ≠ ⊤ := ne_top_of_le_ne_top ENNReal.coe_ne_top hut
  have hst : (t₀ : ℝ≥0∞) ≤ capacityRule c t₀ u (y, g) := Aux61SlitW.start_le_capacityRule c t₀ u (y, g)
  have hle : (capacityRule c t₀ u (y, g)).toNNReal ≤ t := by
    rw [← ENNReal.coe_le_coe, ENNReal.coe_toNNReal hfin]
    exact hut
  have ht₀ : t₀ ≤ (capacityRule c t₀ u (y, g)).toNNReal := by
    rw [← ENNReal.coe_le_coe, ENNReal.coe_toNNReal hfin]
    exact hst
  unfold recPath
  rw [hT]
  congr 1
  funext n
  refine prefixPoint_stopRec ?_
  have hd := dyadicBelow_le n (recTime c t₀ u (y, g))
  unfold recTime at hd
  calc t₀ + LP.dyadicBelow n ((capacityRule c t₀ u (y, g)).toNNReal - t₀)
      ≤ t₀ + ((capacityRule c t₀ u (y, g)).toNNReal - t₀) := (add_le_add_iff_left t₀).2 hd
    _ = (capacityRule c t₀ u (y, g)).toNNReal := add_tsub_cancel_of_le ht₀
    _ ≤ t := hle

/-- **The record driver at `R` only reads the record stopped at a time after every rule up to `R`.** -/
theorem recDriver_stopRec {R : ℝ≥0} (hord : ∀ u ≤ R, capacityRule c t₀ u (y, g) ≤ t) :
    recDriver c t₀ R (y, stopRec t g) = recDriver c t₀ R (y, g) := by
  have hre : (fun s => (recPath c t₀ (y, stopRec t g) (min s R)).re) =
      fun s => (recPath c t₀ (y, g) (min s R)).re :=
    funext fun s => by rw [recPath_stopRec (hord _ (min_le_right _ _))]
  have him : (fun s => (recPath c t₀ (y, stopRec t g) (min s R)).im) =
      fun s => (recPath c t₀ (y, g) (min s R)).im :=
    funext fun s => by rw [recPath_stopRec (hord _ (min_le_right _ _))]
  have hreg : recPathReg c t₀ R (y, stopRec t g) = recPathReg c t₀ R (y, g) := by
    funext t'
    simp only [recPathReg, recPathReg₀, hre, him]
  unfold recDriver
  exact fcReadDriver_congr fun t' _ => congrFun hreg t'

end Stop


/-! ### The record driver is the code's driver on the live event -/

section Access

variable {X : Type*} [MeasurableSpace X] {E : Set X} {cc : X → Chart}
  {ρ : X → ℝ≥0 → ℂ} {T : X → ℝ≥0∞} {V : Set ℂ}
  (hs : IsRestartSpec E cc ρ T) (hV : IsOpen V) (hV0 : (0 : ℂ) ∈ V)
  (hland : HasAccessLanding E cc ρ T V)
  (hinj : ∀ x ∈ E, InjOn (ρ x) {u | (u : ℝ≥0∞) < T x})
  {a k : ℝ} {h : X → LQGMetric.DistOn upperHalfPlaneOpens}
  {𝒴 : Type*} [MeasurableSpace 𝒴] {nL nR : ℕ}
  {c : 𝒴 × HistorySpace nL nR → Chart} {t₀ : ℝ≥0} {y : 𝒴} {g : HistorySpace nL nR}
  {x : X} (hchart : cc x = c (y, stopRec t₀ g))
  (hρ : ∀ u : ℝ≥0, 0 < u → u < exitNN E cc ρ T V x → ρ x u = histTrace 0 g (t₀ + u))
include hs hV hV0 hland hinj hchart hρ

/-- The record's physical code time is the selected-access code time at every alive capacity time. -/
theorem recTime_eq_accessTime {q : ℝ≥0} (hq : (q : ℝ≥0∞) < (accessExitCode E cc ρ T V a k h x).life) :
    recTime c t₀ q (y, g) = accessTime (E := E) (c := cc) (ρ := ρ) (T := T) (V := V) x q := by
  rcases eq_or_ne q 0 with rfl | hq0
  · rw [Aux61SlitW.accessTime_zero hs hV hV0 hland hinj hq]
    simp only [recTime, Aux61SlitW.capacityRule_zero, ENNReal.toNNReal_coe, tsub_self]
  · rw [recTime, Aux61SlitW.capacityRule_eq_accessTime hs hV hV0 hland hinj hchart hρ (pos_iff_ne_zero.2 hq0) hq,
      ENNReal.toNNReal_coe, add_tsub_cancel_left]

omit [MeasurableSpace 𝒴] hchart hρ in
/-- The selected-access code time is monotone in the alive capacity time. -/
theorem accessTime_mono {q q' : ℝ≥0} (hq : (q : ℝ≥0∞) < (accessExitCode E cc ρ T V a k h x).life)
    (hqq : q' ≤ q) :
    accessTime (E := E) (c := cc) (ρ := ρ) (T := T) (V := V) x q' ≤
      accessTime (E := E) (c := cc) (ρ := ρ) (T := T) (V := V) x q := by
  have hq' : (q' : ℝ≥0∞) < (accessExitCode E cc ρ T V a k h x).life :=
    lt_of_le_of_lt (ENNReal.coe_le_coe.2 hqq) hq
  have hx := mem_exitEv_of_lt_accessLife hq
  have hcl := (isPathSpec_accessExitPath hs hV hV0 hland).isClockOn_capClock
    (isClockOn_accessExitPath hs hV hV0 hland hinj) hx
  have h1 := Aux61SlitW.accessTime_spec hs hV hV0 hland hinj hq
  have h2 := Aux61SlitW.accessTime_spec hs hV hV0 hland hinj hq'
  by_contra hlt
  have hlt' := hcl.strictMonoOn (show (accessTime (E := E) (c := cc) (ρ := ρ) (T := T) (V := V) x q : ℝ≥0∞) ≤
      (exitNN E cc ρ T V x : ℝ≥0∞) from ENNReal.coe_le_coe.2 h1.1.le)
    (show (accessTime (E := E) (c := cc) (ρ := ρ) (T := T) (V := V) x q' : ℝ≥0∞) ≤
      (exitNN E cc ρ T V x : ℝ≥0∞) from ENNReal.coe_le_coe.2 h2.1.le) (not_le.1 hlt)
  rw [h1.2, h2.2] at hlt'
  exact absurd hqq (not_le.2 (by exact_mod_cast hlt'))

/-- **The record capacity path is the code's trace** at every alive capacity time. -/
theorem recPath_eq_trace {q : ℝ≥0} (hq : (q : ℝ≥0∞) < (accessExitCode E cc ρ T V a k h x).life) :
    recPath c t₀ (y, g) q = (accessExitCode E cc ρ T V a k h x).trace q := by
  have hx := mem_exitEv_of_lt_accessLife hq
  have hp := isPathSpec_accessExitPath hs hV hV0 hland
  set A := accessTime (E := E) (c := cc) (ρ := ρ) (T := T) (V := V) x q with hAdef
  have hA : A < exitNN E cc ρ T V x := (Aux61SlitW.accessTime_spec hs hV hV0 hland hinj hq).1
  have hpt : ∀ n, prefixPoint c t₀ y (fullRecord g) (LP.dyadicBelow n A) =
      accessExitPath E cc ρ T V x (LP.dyadicBelow n A) := fun n =>
    Aux61SlitW.prefixPoint_eq_accessPath hs hV hV0 hland hx hchart hρ ((dyadicBelow_le n A).trans_lt hA)
  have hlim : Tendsto (fun n => accessExitPath E cc ρ T V x (LP.dyadicBelow n A)) atTop
      (𝓝 (accessExitPath E cc ρ T V x A)) := by
    have hcont := (hp.cont x hx) A (show A ∈ Iic (exitNN E cc ρ T V x) from hA.le)
    refine hcont.tendsto.comp (tendsto_nhdsWithin_iff.2 ⟨LP.tendsto_dyadicBelow A, ?_⟩)
    exact Eventually.of_forall fun n => show LP.dyadicBelow n A ∈ Iic (exitNN E cc ρ T V x) from
      ((dyadicBelow_le n A).trans hA.le)
  have hrec : recPath c t₀ (y, g) q = accessExitPath E cc ρ T V x A := by
    have hfun : (fun n => prefixPoint c t₀ (y, g).1 (fullRecord (y, g).2)
        (LP.dyadicBelow n (recTime c t₀ q (y, g)))) = fun n => accessExitPath E cc ρ T V x (LP.dyadicBelow n A) := by
      funext n
      rw [recTime_eq_accessTime hs hV hV0 hland hinj hchart hρ hq]
      exact hpt n
    unfold recPath
    rw [hfun]
    exact hlim.limUnder_eq
  rw [hrec]
  rcases eq_or_ne q 0 with rfl | hq0
  · have hA0 : A = 0 := Aux61SlitW.accessTime_zero hs hV hV0 hland hinj hq
    rw [hA0, hp.zero x hx, FibCode.trace_zero]
  · have hApos : 0 < A := Aux61SlitW.accessTime_pos hs hV hV0 hland hinj hq (pos_iff_ne_zero.2 hq0)
    have heT : ((exitNN E cc ρ T V x : ℝ≥0) : ℝ≥0∞) ≤ T x := by
      rw [IsRestartSpec.coe_exitNN hx]
      exact IsRestartSpec.exitTime_le x
    have hAT : (A : ℝ≥0∞) < T x := lt_of_lt_of_le (ENNReal.coe_lt_coe.2 hA) heT
    rw [Aux61SlitW.accessExitCode_trace_eq hs hV hV0 hland hinj hq (pos_iff_ne_zero.2 hq0)]
    simp only [accessExitPath, hx, ↓reduceIte, hA]
    exact hs.inPath_eq_fwd hx.1.1 hApos hAT

/-- The regularized record capacity path is the code's trace up to an alive capacity time. -/
theorem recPathReg_eq_trace {R : ℝ≥0} (hR : (R : ℝ≥0∞) < (accessExitCode E cc ρ T V a k h x).life)
    {t : ℝ≥0} (ht : t ≤ R) : recPathReg c t₀ R (y, g) t = (accessExitCode E cc ρ T V a k h x).trace t := by
  set s := accessExitCode E cc ρ T V a k h x with hsdef
  have hfr : (fun u => recPath c t₀ (y, g) (min u R)) = fun u => s.trace (min u R) := by
    funext u
    exact recPath_eq_trace hs hV hV0 hland hinj hchart hρ
      (lt_of_le_of_lt (ENNReal.coe_le_coe.2 (min_le_right u R)) hR)
  have hcont : Continuous fun u => s.trace (min u R) :=
    (FibCode.continuous_trace s).comp (continuous_id.min continuous_const)
  have hre := QuantumZipper.Thm18Asm.G1Pkg.pathReg_spec.2.2 _ (Complex.continuous_re.comp hcont)
  have him := QuantumZipper.Thm18Asm.G1Pkg.pathReg_spec.2.2 _ (Complex.continuous_im.comp hcont)
  have e1 : (fun u => (recPath c t₀ (y, g) (min u R)).re) = (Complex.re ∘ fun u => s.trace (min u R)) := by
    funext u
    simp only [Function.comp_apply, congrFun hfr u]
  have e2 : (fun u => (recPath c t₀ (y, g) (min u R)).im) = (Complex.im ∘ fun u => s.trace (min u R)) := by
    funext u
    simp only [Function.comp_apply, congrFun hfr u]
  have h0 : ∀ t', recPathReg₀ c t₀ R (y, g) t' = s.trace (min t' R) := by
    intro t'
    unfold recPathReg₀
    rw [e1, e2, hre, him]
    exact Complex.ext rfl rfl
  unfold recPathReg
  rw [h0, h0, min_eq_left ht, min_eq_left (zero_le : (0 : ℝ≥0) ≤ R), FibCode.trace_zero, sub_zero]

/-- **The record driver is the code's driver** at every alive capacity time. -/
theorem driver_eq_recDriver (d : FibData) (hdV : d.V = V) (hℓ : d.ℓ = clr V) {R : ℝ≥0}
    (hR : (R : ℝ≥0∞) < (accessExitCode E cc ρ T V a k h x).life) :
    FibCode.driver R (accessExitCode E cc ρ T V a k h x) = recDriver c t₀ R (y, g) := by
  set s := accessExitCode E cc ρ T V a k h x with hsdef
  have hx := mem_exitEv_of_lt_accessLife hR
  have hgood := pathGood_accessExitCode hs hV hV0 hland hinj d hdV hℓ hx (a := a) (k := k) (h := h)
  have hg : IsGeneratingTrace (FibCode.driver · s) s.life s.trace := hgood.1
  rw [← Restart.FCPlumb.fcReadDriver_eq (Γ := fun s' : FibCode => s'.trace) (ω := s)
    (FibCode.continuous_driver s) (FibCode.driver_zero s) hg hR]
  unfold recDriver
  exact fcReadDriver_congr fun t ht => (recPathReg_eq_trace hs hV hV0 hland hinj hchart hρ hR ht).symm

/-- **On a code dead at `r`, the glued stop of `r` is after the window exit**: the record's prefix capacity equals the
capacity clock up to the exit and stays below `r` there, so the first hit of level `r` is after `t₀ + exitNN`. -/
theorem exitNN_le_capacityRule_of_dead {r : ℝ≥0} (hx : x ∈ exitEv E cc ρ T V)
    (hr : (accessExitCode E cc ρ T V a k h x).life ≤ r) :
    (((t₀ + exitNN E cc ρ T V x : ℝ≥0)) : ℝ≥0∞) ≤ capacityRule c t₀ r (y, g) := by
  have hp := isPathSpec_accessExitPath hs hV hV0 hland
  have hclk := isClockOn_accessExitPath hs hV hV0 hland hinj
  have hcl := hp.isClockOn_capClock hclk hx
  have hlpos : 0 < (accessExitCode E cc ρ T V a k h x).life :=
    Aux61GHist.accessExitCode_life_pos hs hV hV0 hland hinj hx
  have hr0 : r ≠ 0 := by
    rintro rfl
    exact absurd hr (not_le.2 hlpos)
  set C := capClock (exitEv E cc ρ T V) (accessExitPath E cc ρ T V) (exitNN E cc ρ T V) x with hCdef
  have hlife : (accessExitCode E cc ρ T V a k h x).life = ENNReal.ofReal (C (exitNN E cc ρ T V x)) := by
    simp only [accessExitCode_life, capEnd, hx, ↓reduceIte, hCdef]
  have hCr : C (exitNN E cc ρ T V x) ≤ r := by
    have := hr
    rw [hlife, ← ENNReal.ofReal_coe_nnreal] at this
    exact (ENNReal.ofReal_le_ofReal_iff (NNReal.coe_nonneg r)).1 this
  have he0 : 0 < exitNN E cc ρ T V x := exitNN_pos hs hV hV0 hx
  have hhit : (((t₀ + exitNN E cc ρ T V x : ℝ≥0)) : ℝ≥0∞) ≤
      Restart.FlowStopIdentG.hitRule (fun g' t => Aux61SlitW.prefixCapacity c t₀ (y, g') t)
        (Ici (r : ℝ)) (fullRecord g) := by
    refine Restart.FlowStopIdentG.le_hitRule_of_off isClosed_Ici (g := fun s => C (s - t₀))
      (((hp.continuous_capClock hclk x).comp (continuous_id.sub continuous_const)).continuousOn) ?_ ?_
    · intro s hs'
      have hs'' : s < t₀ + exitNN E cc ρ T V x := by exact_mod_cast hs'
      have hv : s - t₀ < exitNN E cc ρ T V x := by
        rcases le_total t₀ s with h' | h'
        · exact (tsub_lt_iff_left h').2 hs''
        · rw [tsub_eq_zero_of_le h']
          exact he0
      show ¬ (r : ℝ) ≤ C (s - t₀)
      have hlt := hcl.strictMonoOn (show ((s - t₀ : ℝ≥0) : ℝ≥0∞) ≤ (exitNN E cc ρ T V x : ℝ≥0∞) from
        ENNReal.coe_le_coe.2 hv.le) (show (exitNN E cc ρ T V x : ℝ≥0∞) ≤ (exitNN E cc ρ T V x : ℝ≥0∞) from
        le_rfl) hv
      exact not_le.2 (lt_of_lt_of_le hlt hCr)
    · intro p hp1 _
      have hs'' : dyadicTime p < t₀ + exitNN E cc ρ T V x := by exact_mod_cast hp1
      by_cases hts : t₀ ≤ dyadicTime p
      · have hv : dyadicTime p - t₀ < exitNN E cc ρ T V x := (tsub_lt_iff_left hts).2 hs''
        have he := Aux61SlitW.prefixCapacity_eq_accessClock hs hV hV0 hland hx hchart hρ hv
        rwa [add_tsub_cancel_of_le hts] at he
      · have he := Aux61SlitW.prefixCapacity_eq_accessClock hs hV hV0 hland hx hchart hρ he0
        rw [add_zero] at he
        rw [Aux61SlitW.prefixCapacity_eq_start c t₀ _ (not_le.1 hts).le, he,
          tsub_eq_zero_of_le (not_le.1 hts).le]
  have hcap : capacityRule c t₀ r (y, g) = max (Restart.FlowStopIdentG.hitRule
      (fun g' t => Aux61SlitW.prefixCapacity c t₀ (y, g') t) (Ici (r : ℝ)) (fullRecord g)) t₀ := by
    simp only [capacityRule, hr0, ↓reduceIte]
  rw [hcap]
  exact hhit.trans (le_max_left _ _)

/-- **Every rule up to an alive capacity time precedes the glued stop at any later fibre time**, alive or not: if the
code is dead at `r`, the record's prefix capacity stays below `r` up to the window exit, so the first hit of level `r`
is after the exit. -/
theorem le_capacityRule_of_alive {R r u : ℝ≥0} (hR : (R : ℝ≥0∞) < (accessExitCode E cc ρ T V a k h x).life)
    (hRr : R ≤ r) (hu : u ≤ R) : capacityRule c t₀ u (y, g) ≤ capacityRule c t₀ r (y, g) := by
  have hx := mem_exitEv_of_lt_accessLife hR
  have hp := isPathSpec_accessExitPath hs hV hV0 hland
  have hclk := isClockOn_accessExitPath hs hV hV0 hland hinj
  have hcl := hp.isClockOn_capClock hclk hx
  have hu' : (u : ℝ≥0∞) < (accessExitCode E cc ρ T V a k h x).life :=
    lt_of_le_of_lt (ENNReal.coe_le_coe.2 hu) hR
  set A := accessTime (E := E) (c := cc) (ρ := ρ) (T := T) (V := V) x R with hAdef
  have hAe : A < exitNN E cc ρ T V x := (Aux61SlitW.accessTime_spec hs hV hV0 hland hinj hR).1
  -- the rule at `u` is at most `t₀ + accessTime R`
  have h1 : capacityRule c t₀ u (y, g) ≤ ((t₀ + A : ℝ≥0) : ℝ≥0∞) := by
    rcases eq_or_ne u 0 with rfl | hu0
    · rw [Aux61SlitW.capacityRule_zero]
      exact ENNReal.coe_le_coe.2 le_self_add
    · rw [Aux61SlitW.capacityRule_eq_accessTime hs hV hV0 hland hinj hchart hρ (pos_iff_ne_zero.2 hu0) hu']
      exact ENNReal.coe_le_coe.2 ((add_le_add_iff_left t₀).2 (accessTime_mono hs hV hV0 hland hinj hR hu))
  refine h1.trans ?_
  by_cases hr : (r : ℝ≥0∞) < (accessExitCode E cc ρ T V a k h x).life
  · rcases eq_or_ne r 0 with hr0 | hr0
    · have hR0 : R = 0 := le_antisymm (hr0 ▸ hRr) zero_le
      have hA0 : A = 0 := by
        rw [hAdef, hR0]
        exact Aux61SlitW.accessTime_zero hs hV hV0 hland hinj (lt_of_le_of_lt zero_le hR)
      rw [hr0, Aux61SlitW.capacityRule_zero, hA0, add_zero]
    · rw [Aux61SlitW.capacityRule_eq_accessTime hs hV hV0 hland hinj hchart hρ (pos_iff_ne_zero.2 hr0) hr]
      exact ENNReal.coe_le_coe.2 ((add_le_add_iff_left t₀).2 (accessTime_mono hs hV hV0 hland hinj hr hRr))
  · -- dead at `r`: the first hit of level `r` is after the exit
    have hhit := exitNN_le_capacityRule_of_dead hs hV hV0 hland hinj hchart hρ hx (not_lt.1 hr)
    exact le_trans (ENNReal.coe_le_coe.2 ((add_le_add_iff_left t₀).2 hAe.le)) hhit

/-- **The code's driver at an alive capacity time `R` is the record driver of the record stopped at the glued stop of
any fibre time `r ≥ R`.** -/
theorem driver_eq_recDriver_stopAt (d : FibData) (hdV : d.V = V) (hℓ : d.ℓ = clr V) {R r : ℝ≥0}
    (hR : (R : ℝ≥0∞) < (accessExitCode E cc ρ T V a k h x).life) (hRr : R ≤ r) :
    FibCode.driver R (accessExitCode E cc ρ T V a k h x) =
      recDriver c t₀ R (y, stopAt stopRec (capacityRule c t₀ r (y, g)) g) := by
  rw [driver_eq_recDriver hs hV hV0 hland hinj hchart hρ d hdV hℓ hR]
  by_cases htop : capacityRule c t₀ r (y, g) < ⊤
  · simp only [stopAt, htop, ↓reduceIte]
    refine (recDriver_stopRec fun u hu => ?_).symm
    rw [ENNReal.coe_toNNReal htop.ne]
    exact le_capacityRule_of_alive hs hV hV0 hland hinj hchart hρ hR hRr hu
  · simp only [stopAt, htop, ↓reduceIte]

end Access

/-! ### The raw code σ-algebra in the completed rule marks, up to the aliveness events -/

section CodeLe

/-- **The generator split of `code_le`**: the raw code σ-algebra at `r` is in the null completion of `ℋ` once the
aliveness events `{r' < life}`, `r' ≤ r`, are, and the driver at every `r' ≤ r` is almost surely, while alive, an
`ℋ`-measurable function. -/
theorem codeFiltration_le_nullMarks_of_alive {X : Type u} {ℋ : MeasurableSpace X} [mX : MeasurableSpace X]
    {μ : Measure X} {Y : X → FibCode} {r : ℝ≥0} (hY : Measurable Y)
    (halive : ∀ r' ≤ r, MeasurableSet[nullMarks ℋ μ] {x | ((r' : ℝ≥0) : ℝ≥0∞) < (Y x).life})
    (hdrv : ∀ r' ≤ r, ∃ D : X → ℝ, Measurable[ℋ] D ∧
      ∀ᵐ x ∂μ, ((r' : ℝ≥0) : ℝ≥0∞) < (Y x).life → FibCode.driver r' (Y x) = D x) :
    (Aux61FibK.codeFiltration.{u} r).comap (fun x => ULift.up.{u} (Y x)) ≤ nullMarks ℋ μ := by
  refine codeFiltration_comap_le_nullMarks fun r' hr' A hA => ?_
  obtain ⟨-, J, hJ, hJe⟩ := halive r' hr'
  obtain ⟨D, hD, hDe⟩ := hdrv r' hr'
  have hDA : MeasurableSet[ℋ] {x | (D x, (fun _ : Fin 0 => (0 : ℝ)), fun _ : Fin 0 => (0 : ℝ)) ∈ A} :=
    (hD.prodMk (measurable_const.prodMk measurable_const)) hA
  refine measurableSet_nullMarks_of_ae_eq ?_ (hJ.inter hDA) ?_
  · exact (measurableSet_lt measurable_const (FibCode.measurable_life.comp hY)).inter
      (((FibCode.measurable_driver r').comp hY).prodMk (measurable_const.prodMk measurable_const) hA)
  · filter_upwards [hJe, hDe] with x hx hxD
    have hx' : (((r' : ℝ≥0) : ℝ≥0∞) < (Y x).life) = (x ∈ J) := hx
    refine propext ⟨fun h => ⟨hx' ▸ h.1, ?_⟩, fun h => ⟨hx' ▸ h.1, ?_⟩⟩
    · show (D x, _, _) ∈ A
      rw [← hxD h.1]
      exact h.2
    · have hal : ((r' : ℝ≥0) : ℝ≥0∞) < (Y x).life := hx' ▸ h.1
      show (FibCode.driver r' (Y x), _, _) ∈ A
      rw [hxD hal]
      exact h.2

variable {X : Type u} {𝒢 : MeasurableSpace X} [mX : MeasurableSpace X] {E : Set X} {cc : X → Chart}
  {ρ : X → ℝ≥0 → ℂ} {T : X → ℝ≥0∞} {V : Set ℂ}
  (hs : IsRestartSpec E cc ρ T) (hV : IsOpen V) (hV0 : (0 : ℂ) ∈ V)
  (hland : HasAccessLanding E cc ρ T V)
  (hinj : ∀ x ∈ E, InjOn (ρ x) {u | (u : ℝ≥0∞) < T x})
  {a k : ℝ} {h : X → LQGMetric.DistOn upperHalfPlaneOpens}
  {𝒴 : Type*} [MeasurableSpace 𝒴] {nL nR : ℕ}
  {c : 𝒴 × HistorySpace nL nR → Chart} {t₀ : ℝ≥0} {Y₀ : X → 𝒴} {R₀ : X → HistorySpace nL nR} {μ : Measure X}
include hs hV hV0 hland hinj

/-- **The code's driver is almost surely the record driver of the stopped record**, at every alive capacity time
`r' ≤ r`, when the chart is read from the time-`0` record and the restarted path is the record's trace (SLITW's
interface `hchart`, `hρ`, almost surely). -/
theorem ae_driver_eq_recDriver (hc : IsMeasChart c) (d : FibData) (hdV : d.V = V) (hℓ : d.ℓ = clr V) (r : ℝ≥0)
    (hrec : ∀ᵐ x ∂μ, cc x = c (Y₀ x, stopRec t₀ (R₀ x)) ∧
      ∀ u : ℝ≥0, 0 < u → u < exitNN E cc ρ T V x → ρ x u = histTrace 0 (R₀ x) (t₀ + u)) (r' : ℝ≥0)
    (hr' : r' ≤ r) :
    ∃ D : X → ℝ, Measurable[ruleMarks stopRec (capacityRule c t₀ r) Y₀ R₀] D ∧
      ∀ᵐ x ∂μ, ((r' : ℝ≥0) : ℝ≥0∞) < (accessExitCode E cc ρ T V a k h x).life →
        FibCode.driver r' (accessExitCode E cc ρ T V a k h x) = D x := by
  refine ⟨fun x => recDriver c t₀ r' (Y₀ x, stopAt stopRec (capacityRule c t₀ r (Y₀ x, R₀ x)) (R₀ x)),
    measurable_ruleMarks_of_factor (measurable_recDriver hc t₀ r'), ?_⟩
  filter_upwards [hrec] with x hx halive
  exact driver_eq_recDriver_stopAt hs hV hV0 hland hinj hx.1 hx.2 d hdV hℓ halive hr'

/-- **`code_le` for the completed rule marks from the aliveness events**: the raw code σ-algebra at `r` is in the null
completion of the rule marks of SLITW's glued stop `capacityRule c t₀ r`, once the aliveness events `{r' < life}`,
`r' ≤ r`, are. -/
theorem codeFiltration_le_nullRuleMarks (hc : IsMeasChart c) (d : FibData) (hdV : d.V = V) (hℓ : d.ℓ = clr V)
    (hliftc : ∀ x ∈ E, ContinuousOn (cc x).2.2 (cc x).dom) (hh : Measurable h) (r : ℝ≥0)
    (hrec : ∀ᵐ x ∂μ, cc x = c (Y₀ x, stopRec t₀ (R₀ x)) ∧
      ∀ u : ℝ≥0, 0 < u → u < exitNN E cc ρ T V x → ρ x u = histTrace 0 (R₀ x) (t₀ + u))
    (halive : ∀ r' ≤ r, MeasurableSet[nullMarks (ruleMarks stopRec (capacityRule c t₀ r) Y₀ R₀) μ]
      {x | ((r' : ℝ≥0) : ℝ≥0∞) < (accessExitCode E cc ρ T V a k h x).life}) :
    (Aux61FibK.codeFiltration.{u} r).comap (fun x => ULift.up.{u} (accessExitCode E cc ρ T V a k h x)) ≤
      nullMarks (ruleMarks stopRec (capacityRule c t₀ r) Y₀ R₀) μ :=
  codeFiltration_le_nullMarks_of_alive
    (measurable_accessExitCode hs hV hV0 hland hinj hliftc hh) halive
    fun r' hr' => ae_driver_eq_recDriver hs hV hV0 hland hinj hc d hdV hℓ r hrec r' hr'

end CodeLe

end InteractingSLE.Sec5.Aux61Marks
