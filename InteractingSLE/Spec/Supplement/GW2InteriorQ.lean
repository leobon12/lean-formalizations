/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW2ConeQ
import InteractingSLE.Spec.Supplement.GW2ScheduleTonelli
import InteractingSLE.Spec.Supplement.GW2ScheduleL25

/-!
# Lemma GB9a's deterministic schedule set with interior switching tips

Conditional proof of `GW2InteriorScheduleQStatement`, using the jointly measurable canonical schedule, Lemma 2.5,
the GB9a time selection, and the R51 identification of staged histories.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped NNReal ENNReal
open QuantumZipper (H)

universe u

namespace InteractingSLE

namespace Theorem14

namespace GW2Tip

open GW2Cone GW2Schedule GW2Later Exist Staged StagedLaw Restart LQGMetric
open Exist.Staged
open Sec2.Assembly

/-! ### Measurable trace coordinates of the canonical family -/

/-- The trace path selected by Theorem 1.2 for a word and field. -/
def stagedTrace (h12p : Theorem12ParamStatement.{u}) {κ : ℝ} (hκ : 0 < κ) {R : Type*}
    (nLf nRf : R → ℕ) (pw : R → PadWord) (x : R) (f : DistOn upperHalfPlaneOpens) : ℝ≥0 → ℂ :=
  (paramΦ h12p hκ (nLf x) (nRf x) (truncWord (nLf x) (nRf x) (pw x), f)).2

theorem measurable_stagedTrace (h12p : Theorem12ParamStatement.{u}) {κ : ℝ} (hκ : 0 < κ) {R : Type*}
    [MeasurableSpace R] {nLf nRf : R → ℕ} (hnL : Measurable nLf) (hnR : Measurable nRf)
    {pw : R → PadWord} (hpw : Measurable pw) :
    Measurable fun p : R × DistOn upperHalfPlaneOpens => stagedTrace h12p hκ nLf nRf pw p.1 p.2 := by
  set F : (R × DistOn upperHalfPlaneOpens) × (ℕ × ℕ) → (ℝ≥0 → ℂ) := fun q =>
    (paramΦ h12p hκ q.2.1 q.2.2 (truncWord q.2.1 q.2.2 (pw q.1.1), q.1.2)).2 with hFdef
  have hFm : Measurable F := by
    refine measurable_from_prod_countable_left fun mn => ?_
    exact (measurable_snd.comp (measurable_paramΦ h12p hκ mn.1 mn.2)).comp
      (((measurable_truncWord mn.1 mn.2).comp (hpw.comp measurable_fst)).prodMk measurable_snd)
  have heq : (fun p : R × DistOn upperHalfPlaneOpens => stagedTrace h12p hκ nLf nRf pw p.1 p.2) =
      fun p => F (p, (nLf p.1, nRf p.1)) := rfl
  rw [heq]
  exact hFm.comp (measurable_id.prodMk ((hnL.comp measurable_fst).prodMk (hnR.comp measurable_fst)))

/-- The trace path of the angle-`θ` word driver. -/
def wordTrace (h12p : Theorem12ParamStatement.{u}) {κ : ℝ} (hκ : 0 < κ) (θ : ℝ)
    (c : BoundaryWord) (f : DistOn upperHalfPlaneOpens) : ℝ≥0 → ℂ :=
  stagedTrace h12p hκ wNL wNR (wPad κ θ) c f

theorem measurable_wordTrace (h12p : Theorem12ParamStatement.{u}) {κ : ℝ} (hκ : 0 < κ) (θ : ℝ) :
    Measurable fun p : BoundaryWord × DistOn upperHalfPlaneOpens => wordTrace h12p hκ θ p.1 p.2 := by
  have hw := wordMeasStatement
  exact measurable_stagedTrace h12p hκ hw.1 hw.2.1 (hw.2.2 κ θ)

/-- Evaluation of a measurable path family at the dyadic upper approximation of a measurable time. -/
theorem measurable_eval_dyadUp {α : Type*} [MeasurableSpace α] (F : α → ℝ≥0 → ℂ) (hF : Measurable F)
    (T : α → ℝ≥0) (hT : Measurable T) (n : ℕ) :
    Measurable fun a => F a (dyadUp n (T a)) := by
  have haux : Measurable fun p : α × ℕ => F p.1 (((p.2 : ℝ≥0) / 2 ^ n)) := by
    refine measurable_from_prod_countable_left fun m => ?_
    exact (measurable_pi_apply (((m : ℝ≥0) / 2 ^ n))).comp hF
  have hceil : Measurable fun a => ⌈(T a : ℝ) * 2 ^ n⌉₊ :=
    ((measurable_coe_nnreal_real.comp hT).mul_const _).nat_ceil
  have hcomp := haux.comp (measurable_id.prodMk hceil)
  have heq : (fun a => F a (dyadUp n (T a))) =
      fun a => F a (((⌈(T a : ℝ) * 2 ^ n⌉₊ : ℝ≥0) / 2 ^ n)) := by
    funext a
    congr 1
    apply NNReal.eq
    simp only [coe_dyadUp, NNReal.coe_div]
    norm_cast
  rw [heq]
  exact hcomp

/-- The selected trace evaluated at a measurable time; off the trace's continuity set the limit-under value is the
canonical junk value. -/
def evalTrace {α : Type*} (F : α → ℝ≥0 → ℂ) (T : α → ℝ≥0) (a : α) : ℂ :=
  Filter.limUnder atTop fun n => F a (dyadUp n (T a))

def evalTraceAt (F : ℝ≥0 → ℂ) (T : ℝ≥0) : ℂ :=
  evalTrace (fun _ : Unit => F) (fun _ => T) ()

theorem evalTrace_apply_eq {α : Type*} (F : α → ℝ≥0 → ℂ) (T : α → ℝ≥0) (a : α) :
    evalTrace F T a = evalTraceAt (F a) (T a) := rfl

theorem measurable_evalTrace {α : Type*} [MeasurableSpace α] {F : α → ℝ≥0 → ℂ} (hF : Measurable F)
    {T : α → ℝ≥0} (hT : Measurable T) : Measurable fun a => evalTrace F T a := by
  apply (StronglyMeasurable.limUnder fun n => (measurable_eval_dyadUp F hF T hT n).stronglyMeasurable).measurable

/-- The trace selector read from a deterministic driver code. -/
def driverCodeTrace (z : DCode) : ℝ≥0 → ℂ := fun t => LP.traceAt t (dec z.2)

theorem measurable_driverCodeTrace : Measurable driverCodeTrace :=
  measurable_pi_iff.2 fun t => (LP.measurable_traceAt t).comp measurable_dec_snd

/-- On a good driver code, the dyadic upper limit of the output trace coordinate is the generating trace at every
time below a chosen dyadic lifetime cutoff. -/
theorem evalTrace_driverCode_eq {z : DCode} (hz : z ∈ DSet) {T R : ℝ≥0}
    (hTR : T < R) (hR : (R : ℝ≥0∞) < z.1) {η : ℝ≥0 → ℂ}
    (hη : IsGeneratingTrace (dec z.2) R η) :
    evalTraceAt (driverCodeTrace z) T = η T := by
  have hR0 : 0 < R := lt_of_le_of_lt (show (0 : ℝ≥0) ≤ T from bot_le) hTR
  have hRpos : 0 < z.1 := lt_trans (ENNReal.coe_pos.2 hR0) hR
  have hzero : dec z.2 0 = 0 := dec_zero_of_mem_DSet hz hRpos
  have hcont : ContinuousOn (dec z.2) {s | (s : ℝ≥0∞) < z.1} := continuousOn_of_mem_DSet hz
  have hcontR : ContinuousOn (dec z.2) {s | (s : ℝ≥0∞) < R} :=
    hcont.mono fun s hs => lt_trans hs hR
  have happrox : Tendsto (fun n => dyadUp n T) atTop (𝓝 T) :=
    (tendsto_dyadUp T).mono_right nhdsWithin_le_nhds
  have hevent' : ∀ᶠ n : ℕ in atTop, dyadUp n T < R :=
    happrox.eventually (gt_mem_nhds hTR)
  have hevent : ∀ᶠ n : ℕ in atTop, (dyadUp n T : ℝ≥0∞) < (R : ℝ≥0∞) :=
    hevent'.mono fun n hn => ENNReal.coe_lt_coe.2 hn
  have hseq : Tendsto (fun n => LP.traceAt (dyadUp n T) (dec z.2)) atTop (𝓝 (η T)) := by
    have hηcont : ContinuousOn η {s | (s : ℝ≥0∞) ≤ R} := hη.2.1
    have hTmem : T ∈ {s : ℝ≥0 | (s : ℝ≥0∞) ≤ R} := ENNReal.coe_le_coe.2 hTR.le
    have hwithin : Tendsto (fun n => dyadUp n T) atTop
        (𝓝[{s : ℝ≥0 | (s : ℝ≥0∞) ≤ R}] T) := by
      refine tendsto_nhdsWithin_iff.2 ⟨happrox, ?_⟩
      filter_upwards [hevent] with n hn
      exact hn.le
    have hηseq : Tendsto (fun n => η (dyadUp n T)) atTop (𝓝 (η T)) :=
      (hηcont.continuousWithinAt hTmem).tendsto.comp hwithin
    refine hηseq.congr' ?_
    filter_upwards [hevent] with n hn
    have htζ : (dyadUp n T : ℝ≥0∞) < z.1 := lt_trans hn hR
    have htrace := LP.traceAt_eq_of_isGeneratingTrace hη hcontR hzero hn
    exact htrace.symm
  exact hseq.limUnder_eq

/-- The canonical driver code attached to one word and field by the parametric Theorem 1.2 map. -/
def wordDriverCode (h12p : Theorem12ParamStatement.{u}) {κ : ℝ} (hκ : 0 < κ) (θ : ℝ)
    (c : BoundaryWord) (f : DistOn upperHalfPlaneOpens) : DCode :=
  dInv (outCode (Restart.flowTrace h12p hκ θ ((c, 0), f)))

theorem measurable_wordDriverCode (h12p : Theorem12ParamStatement.{u}) {κ : ℝ} (hκ : 0 < κ) (θ : ℝ) :
    Measurable fun p : BoundaryWord × DistOn upperHalfPlaneOpens => wordDriverCode h12p hκ θ p.1 p.2 := by
  exact measurable_dInv.comp (measurable_outCode.comp (Restart.measurable_flowTrace h12p hκ θ |>.comp
    ((measurable_fst.prodMk measurable_const).prodMk measurable_snd)))

theorem wordDrv_eq_drvOf_wordDriverCode (h12p : Theorem12ParamStatement.{u}) {κ : ℝ} (hκ : 0 < κ)
    (θ : ℝ) (c : BoundaryWord) (f : DistOn upperHalfPlaneOpens) :
    wordDrv hκ h12p θ c f = drvOf (wordDriverCode h12p hκ θ c f) := by
  rw [wordDrv_eq, wordDriverCode, Restart.flowTrace_mk]
  rfl

/-- The preceding absolute schedule time at a finite coordinate, with time zero before the first entry. -/
def vecPrevTime {n : ℕ} (v : Fin n → ℝ) (i : Fin n) : ℝ :=
  if hi : i.val = 0 then 0 else v ⟨i.val - 1, by omega⟩

/-- The own time corresponding to one coordinate of an absolute time vector. -/
def vecOwnTime {n : ℕ} (v : Fin n → ℝ) (i : Fin n) : ℝ≥0 :=
  (v i).toNNReal - (vecPrevTime v i).toNNReal

/-- Extend the own-time vector by zero after the finite schedule. -/
def vecOwnTimes {n : ℕ} (v : Fin n → ℝ) : ℕ → ℝ≥0∞ := fun j =>
  if hj : j < n then (vecOwnTime v ⟨j, hj⟩ : ℝ≥0∞) else 0

theorem measurable_vecOwnTime {n : ℕ} (i : Fin n) :
    Measurable fun v : Fin n → ℝ => vecOwnTime v i := by
  have hp : Measurable fun v : Fin n → ℝ => vecPrevTime v i := by
    by_cases hi : i.val = 0
    · simp [vecPrevTime, hi]
    · simp only [vecPrevTime, hi, ↓reduceDIte]
      exact measurable_pi_apply (⟨i.val - 1, by omega⟩ : Fin n)
  exact (measurable_real_toNNReal.comp (measurable_pi_apply i)).sub
    (measurable_real_toNNReal.comp hp)

theorem measurable_vecOwnTimes {n : ℕ} : Measurable (vecOwnTimes (n := n)) := by
  apply measurable_pi_iff.2
  intro j
  by_cases hj : j < n
  · simp only [vecOwnTimes, hj, ↓reduceDIte]
    exact measurable_coe_nnreal_ennreal.comp (measurable_vecOwnTime ⟨j, hj⟩)
  · simp only [vecOwnTimes, hj, ↓reduceDIte]
    exact measurable_const

/-- Read a countable angle schedule as a total angle function, using zero past its finite end. -/
def anglesOfList (Θ : Set ℝ) (angles : List {a : ℝ // a ∈ Θ}) : ℕ → ℝ :=
  fun j => (angles.map fun a => a.1).getD j 0

/-- The canonical driver code at instruction `k` for a finite absolute time vector. -/
def vecCanonCode (h12p : Theorem12ParamStatement.{u}) {κ : ℝ} (hκ : 0 < κ) (Θ : Set ℝ)
    (βA : BoundaryWord × ℝ × RecData → BoundaryWord) (c₀ : BoundaryWord) (x₀ : ℝ)
    (angles : List {a : ℝ // a ∈ Θ}) {n : ℕ} (v : Fin n → ℝ)
    (f : DistOn upperHalfPlaneOpens) (k : ℕ) : DCode := by
  let θ := anglesOfList Θ angles
  let st := canonState hκ h12p βA c₀ x₀ θ (vecOwnTimes v) f k
  exact wordDriverCode h12p hκ (θ k) st.1 st.2

theorem measurable_vecCanonCode (h12p : Theorem12ParamStatement.{u}) {κ : ℝ} (hκ : 0 < κ) (Θ : Set ℝ)
    (βA : BoundaryWord × ℝ × RecData → BoundaryWord) (c₀ : BoundaryWord) (x₀ : ℝ)
    (hβA : Measurable βA) {Ω : Type*} [MeasurableSpace Ω] {h : Ω → DistOn upperHalfPlaneOpens}
    (hh : Measurable h) (angles : List {a : ℝ // a ∈ Θ}) {n : ℕ} (k : ℕ) :
    Measurable fun p : Ω × (Fin n → ℝ) => vecCanonCode h12p hκ Θ βA c₀ x₀ angles p.2 (h p.1) k := by
  let θ := anglesOfList Θ angles
  have hstate : Measurable fun p : Ω × (Fin n → ℝ) =>
      canonState hκ h12p βA c₀ x₀ θ (vecOwnTimes p.2) (h p.1) k := by
    exact (measurable_canonState hκ h12p βA c₀ x₀ θ hβA k).comp
      ((measurable_vecOwnTimes.comp measurable_snd).prodMk (hh.comp measurable_fst))
  exact (measurable_wordDriverCode h12p hκ (θ k)).comp
    ((measurable_fst.comp hstate).prodMk (measurable_snd.comp hstate))

theorem vecCanonDrive_eq_drvOf_vecCanonCode (h12p : Theorem12ParamStatement.{u}) {κ : ℝ} (hκ : 0 < κ) (Θ : Set ℝ)
    (βA : BoundaryWord × ℝ × RecData → BoundaryWord) (c₀ : BoundaryWord) (x₀ : ℝ)
    (angles : List {a : ℝ // a ∈ Θ}) {n : ℕ} (v : Fin n → ℝ)
    (f : DistOn upperHalfPlaneOpens) (k : ℕ) :
    canonDrive hκ h12p βA c₀ x₀ (anglesOfList Θ angles) (vecOwnTimes v) f k =
      drvOf (vecCanonCode h12p hκ Θ βA c₀ x₀ angles v f k) := by
  simp only [vecCanonCode, canonDrive]
  exact wordDrv_eq_drvOf_wordDriverCode h12p hκ _ _ _

/-- The measurable code trace family of the canonical driver at one schedule coordinate. -/
def vecCanonCodeTrace (h12p : Theorem12ParamStatement.{u}) {κ : ℝ} (hκ : 0 < κ) (Θ : Set ℝ)
    (βA : BoundaryWord × ℝ × RecData → BoundaryWord) (c₀ : BoundaryWord) (x₀ : ℝ)
    (angles : List {a : ℝ // a ∈ Θ}) {n : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    {h : Ω → DistOn upperHalfPlaneOpens} (k : ℕ) (p : Ω × (Fin n → ℝ)) : ℝ≥0 → ℂ :=
  driverCodeTrace (vecCanonCode h12p hκ Θ βA c₀ x₀ angles p.2 (h p.1) k)

theorem measurable_vecCanonCodeTrace (h12p : Theorem12ParamStatement.{u}) {κ : ℝ} (hκ : 0 < κ)
    (Θ : Set ℝ) (βA : BoundaryWord × ℝ × RecData → BoundaryWord) (c₀ : BoundaryWord) (x₀ : ℝ)
    (hβA : Measurable βA) {Ω : Type*} [MeasurableSpace Ω] {h : Ω → DistOn upperHalfPlaneOpens}
    (hh : Measurable h) (angles : List {a : ℝ // a ∈ Θ}) {n : ℕ} (k : ℕ) :
    Measurable (vecCanonCodeTrace h12p hκ Θ βA c₀ x₀ angles (n := n) (Ω := Ω) (h := h) k) := by
  exact measurable_driverCodeTrace.comp
    (measurable_vecCanonCode h12p hκ Θ βA c₀ x₀ hβA hh angles (n := n) k)

/-- The dyadic upper-limit trace coordinate for the canonical piece at its own time. -/
def vecCanonEval (h12p : Theorem12ParamStatement.{u}) {κ : ℝ} (hκ : 0 < κ) (Θ : Set ℝ)
    (βA : BoundaryWord × ℝ × RecData → BoundaryWord) (c₀ : BoundaryWord) (x₀ : ℝ)
    (angles : List {a : ℝ // a ∈ Θ}) {n : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    {h : Ω → DistOn upperHalfPlaneOpens} (k : Fin n) (p : Ω × (Fin n → ℝ)) : ℂ :=
  evalTrace (vecCanonCodeTrace h12p hκ Θ βA c₀ x₀ angles (n := n) (Ω := Ω) (h := h) k.1)
    (fun q => vecOwnTime q.2 k) p

theorem measurable_vecCanonEval (h12p : Theorem12ParamStatement.{u}) {κ : ℝ} (hκ : 0 < κ)
    (Θ : Set ℝ) (βA : BoundaryWord × ℝ × RecData → BoundaryWord) (c₀ : BoundaryWord) (x₀ : ℝ)
    (hβA : Measurable βA) {Ω : Type*} [MeasurableSpace Ω] {h : Ω → DistOn upperHalfPlaneOpens}
    (hh : Measurable h) (angles : List {a : ℝ // a ∈ Θ}) {n : ℕ} (k : Fin n) :
    Measurable (vecCanonEval h12p hκ Θ βA c₀ x₀ angles (Ω := Ω) (h := h) k) := by
  exact measurable_evalTrace
    (measurable_vecCanonCodeTrace h12p hκ Θ βA c₀ x₀ hβA hh angles (n := n) k.1)
    ((measurable_vecOwnTime k).comp measurable_snd)

/-- The code lifetime is the lifetime of the canonical driver, including the junk-code case. -/
def vecCanonLife (h12p : Theorem12ParamStatement.{u}) {κ : ℝ} (hκ : 0 < κ) (Θ : Set ℝ)
    (βA : BoundaryWord × ℝ × RecData → BoundaryWord) (c₀ : BoundaryWord) (x₀ : ℝ)
    (angles : List {a : ℝ // a ∈ Θ}) {n : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    {h : Ω → DistOn upperHalfPlaneOpens} (j : ℕ) (p : Ω × (Fin n → ℝ)) : ℝ≥0∞ :=
  (drvOf (vecCanonCode h12p hκ Θ βA c₀ x₀ angles p.2 (h p.1) j)).2

theorem measurable_vecCanonLife (h12p : Theorem12ParamStatement.{u}) {κ : ℝ} (hκ : 0 < κ)
    (Θ : Set ℝ) (βA : BoundaryWord × ℝ × RecData → BoundaryWord) (c₀ : BoundaryWord) (x₀ : ℝ)
    (hβA : Measurable βA) {Ω : Type*} [MeasurableSpace Ω] {h : Ω → DistOn upperHalfPlaneOpens}
    (hh : Measurable h) (angles : List {a : ℝ // a ∈ Θ}) {n : ℕ} (j : ℕ) :
    Measurable (vecCanonLife h12p hκ Θ βA c₀ x₀ angles (n := n) (Ω := Ω) (h := h) j) := by
  exact measurable_snd.comp (measurable_drvOf.comp
    (measurable_vecCanonCode h12p hκ Θ βA c₀ x₀ hβA hh angles (n := n) j))

/-- The measurable bad set where the successful canonical piece has a boundary trace at its own schedule time. -/
def vecInteriorBadSet (h12p : Theorem12ParamStatement.{u}) {κ : ℝ} (hκ : 0 < κ) (Θ : Set ℝ)
    (βA : BoundaryWord × ℝ × RecData → BoundaryWord) (c₀ : BoundaryWord) (x₀ : ℝ)
    (angles : List {a : ℝ // a ∈ Θ}) {n : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    {h : Ω → DistOn upperHalfPlaneOpens} (i : Fin n) : Set (Ω × (Fin n → ℝ)) :=
  {p | 0 < p.2 i ∧ vecPrevTime p.2 i < p.2 i ∧
    (∀ j < i.val + 1, vecOwnTimes p.2 j <
      vecCanonLife h12p hκ Θ βA c₀ x₀ angles (n := n) (h := h) j p) ∧
    vecCanonEval h12p hκ Θ βA c₀ x₀ angles (n := n) (h := h) i p ∉ H}

theorem measurableSet_vecInteriorBadSet (h12p : Theorem12ParamStatement.{u}) {κ : ℝ} (hκ : 0 < κ)
    (Θ : Set ℝ) (βA : BoundaryWord × ℝ × RecData → BoundaryWord) (c₀ : BoundaryWord) (x₀ : ℝ)
    (hβA : Measurable βA) {Ω : Type*} [MeasurableSpace Ω] {h : Ω → DistOn upperHalfPlaneOpens}
    (hh : Measurable h) (angles : List {a : ℝ // a ∈ Θ}) {n : ℕ} (i : Fin n) :
    MeasurableSet (vecInteriorBadSet h12p hκ Θ βA c₀ x₀ angles (n := n) (Ω := Ω) (h := h) i) := by
  have hi : Measurable fun p : Ω × (Fin n → ℝ) => p.2 i :=
    (measurable_pi_apply i).comp measurable_snd
  have hp : Measurable fun p : Ω × (Fin n → ℝ) => vecPrevTime p.2 i := by
    have hprev : Measurable (fun v : Fin n → ℝ => vecPrevTime v i) := by
      by_cases h0 : i.val = 0
      · simp [vecPrevTime, h0]
      · simp only [vecPrevTime, h0, ↓reduceDIte]
        exact measurable_pi_apply (⟨i.val - 1, by omega⟩ : Fin n)
    exact hprev.comp measurable_snd
  have hsuccess : MeasurableSet {p : Ω × (Fin n → ℝ) | ∀ j < i.val + 1,
      vecOwnTimes p.2 j < vecCanonLife h12p hκ Θ βA c₀ x₀ angles
        (n := n) (h := h) j p} := by
    let C : ℕ → Set (Ω × (Fin n → ℝ)) := fun j =>
      if hj : j < i.val + 1 then {p | vecOwnTimes p.2 j <
        vecCanonLife h12p hκ Θ βA c₀ x₀ angles (n := n) (h := h) j p} else Set.univ
    have hC : ∀ j, MeasurableSet (C j) := by
      intro j
      by_cases hj : j < i.val + 1
      · simp only [C, hj, ↓reduceDIte]
        exact measurableSet_lt
          ((measurable_pi_apply j).comp (measurable_vecOwnTimes.comp measurable_snd))
          (measurable_vecCanonLife h12p hκ Θ βA c₀ x₀ hβA hh angles j)
      · simp only [C, hj, ↓reduceDIte]
        exact MeasurableSet.univ
    have hI : MeasurableSet (⋂ j, C j) := MeasurableSet.iInter hC
    have heq : {p : Ω × (Fin n → ℝ) | ∀ j < i.val + 1,
        vecOwnTimes p.2 j < vecCanonLife h12p hκ Θ βA c₀ x₀ angles
          (n := n) (h := h) j p} = ⋂ j, C j := by
      ext p
      simp only [C, mem_iInter, mem_setOf_eq]
      constructor
      · intro h j
        by_cases hj : j < i.val + 1
        · simpa [hj] using h j hj
        · simp [hj]
      · intro h j hj
        simpa [hj] using h j
    rw [heq]
    exact hI
  have heval := measurable_vecCanonEval h12p hκ Θ βA c₀ x₀ hβA hh angles i
  have hnotH : MeasurableSet {p : Ω × (Fin n → ℝ) |
      vecCanonEval h12p hκ Θ βA c₀ x₀ angles (n := n) (h := h) i p ∉ H} := by
    have hH : MeasurableSet H := QuantumZipper.isOpen_H.measurableSet
    exact (hH.preimage heval).compl
  have hinter : MeasurableSet
      ({p : Ω × (Fin n → ℝ) | 0 < p.2 i} ∩
        {p | vecPrevTime p.2 i < p.2 i} ∩
        {p | ∀ j < i.val + 1, vecOwnTimes p.2 j <
          vecCanonLife h12p hκ Θ βA c₀ x₀ angles (n := n) (h := h) j p} ∩
        {p | vecCanonEval h12p hκ Θ βA c₀ x₀ angles (n := n) (h := h) i p ∉ H}) := by
    exact (((measurableSet_lt measurable_const hi).inter
      (measurableSet_lt hp hi)).inter hsuccess).inter hnotH
  have heq : {p : Ω × (Fin n → ℝ) | 0 < p.2 i ∧ vecPrevTime p.2 i < p.2 i ∧
      (∀ j < i.val + 1, vecOwnTimes p.2 j <
        vecCanonLife h12p hκ Θ βA c₀ x₀ angles (n := n) (h := h) j p) ∧
      vecCanonEval h12p hκ Θ βA c₀ x₀ angles (n := n) (h := h) i p ∉ H} =
      ({p : Ω × (Fin n → ℝ) | 0 < p.2 i} ∩
        {p | vecPrevTime p.2 i < p.2 i} ∩
        {p | ∀ j < i.val + 1, vecOwnTimes p.2 j <
          vecCanonLife h12p hκ Θ βA c₀ x₀ angles (n := n) (h := h) j p} ∩
        {p | vecCanonEval h12p hκ Θ βA c₀ x₀ angles (n := n) (h := h) i p ∉ H}) := by
    ext p
    simp only [mem_inter_iff, mem_setOf_eq]
    tauto
  unfold vecInteriorBadSet
  rw [heq]
  exact hinter

theorem vecOwnTime_update_prev {n : ℕ} (v : Fin n → ℝ) (i k : Fin n) (x : ℝ) (hk : k < i) :
    vecOwnTime (Function.update v i x) k = vecOwnTime v k := by
  unfold vecOwnTime
  rw [Function.update_of_ne (Fin.ne_of_lt hk)]
  by_cases h0 : k.val = 0
  · simp [vecPrevTime, h0]
  · simp only [vecPrevTime, h0, ↓reduceDIte]
    have hprev : (⟨k.val - 1, by omega⟩ : Fin n) ≠ i := by
      intro he
      have hv := congrArg Fin.val he
      simp only [Fin.val_mk] at hv
      omega
    rw [Function.update_of_ne hprev]

theorem vecOwnTimes_update_prev {n : ℕ} (v : Fin n → ℝ) (i : Fin n) (x : ℝ) (j : ℕ)
    (hj : j < i.val) :
    vecOwnTimes (Function.update v i x) j = vecOwnTimes v j := by
  unfold vecOwnTimes
  by_cases hjn : j < n
  · simp only [hjn, ↓reduceDIte]
    congr 1
    exact vecOwnTime_update_prev v i ⟨j, hjn⟩ x (Fin.mk_lt_mk.mpr hj)
  · simp [hjn]

theorem vecPrevTime_update_self {n : ℕ} (v : Fin n → ℝ) (i : Fin n) (x : ℝ) :
    vecPrevTime (Function.update v i x) i = vecPrevTime v i := by
  unfold vecPrevTime
  by_cases h0 : i.val = 0
  · simp [h0]
  · simp only [h0, ↓reduceDIte]
    have hprev : (⟨i.val - 1, by omega⟩ : Fin n) ≠ i := by
      intro he
      have hv := congrArg Fin.val he
      have hsub : i.val - 1 < i.val := Nat.sub_lt (Nat.one_le_iff_ne_zero.mpr h0) (by omega)
      simp only [Fin.val_mk] at hv
      exact (Nat.ne_of_lt hsub) hv
    rw [Function.update_of_ne hprev]

theorem vecOwnTime_pos_of_abs {n : ℕ} (v : Fin n → ℝ) (i : Fin n) (x : ℝ)
    (hx : 0 < x) (hp : vecPrevTime (Function.update v i x) i < x) :
    0 < vecOwnTime (Function.update v i x) i := by
  have hprev : (vecPrevTime (Function.update v i x) i).toNNReal < x.toNNReal :=
    (Real.toNNReal_lt_toNNReal_iff hx).2 hp
  unfold vecOwnTime
  simp only [Function.update_self]
  exact tsub_pos_of_lt hprev

theorem vecCanonCode_update_prev (h12p : Theorem12ParamStatement.{u}) {κ : ℝ} (hκ : 0 < κ)
    (Θ : Set ℝ) (βA : BoundaryWord × ℝ × RecData → BoundaryWord) (c₀ : BoundaryWord) (x₀ : ℝ)
    (angles : List {a : ℝ // a ∈ Θ}) {n : ℕ} (v : Fin n → ℝ) (i : Fin n) (x : ℝ)
    (f : DistOn upperHalfPlaneOpens) :
    vecCanonCode h12p hκ Θ βA c₀ x₀ angles (Function.update v i x) f i.val =
      vecCanonCode h12p hκ Θ βA c₀ x₀ angles v f i.val := by
  unfold vecCanonCode
  dsimp only
  have hΔ : ∀ j < i.val, vecOwnTimes (Function.update v i x) j = vecOwnTimes v j :=
    fun j hj => vecOwnTimes_update_prev v i x j hj
  have hstate := canonState_congr hκ h12p βA c₀ x₀ (anglesOfList Θ angles) f hΔ
  rw [hstate]

theorem volume_driverCode_eval_notH {z : DCode} (hz : z ∈ DSet) :
    volume {t : ℝ | 0 ≤ t ∧ ((t.toNNReal : ℝ≥0) : ℝ≥0∞) < z.1 ∧
      evalTraceAt (driverCodeTrace z) t.toNNReal ∉ H} = 0 := by
  classical
  let B : ℕ × ℕ → Set ℝ := fun nk =>
    if hR : (dyad nk.1 nk.2 : ℝ≥0∞) < z.1 then
      {t : ℝ | 0 ≤ t ∧ ((t.toNNReal : ℝ≥0) : ℝ≥0∞) < (dyad nk.1 nk.2 : ℝ≥0∞) ∧
        ∃ p, Lemma25.IsTipPoint Chart.id (dec z.2) t.toNNReal p ∧ p ∉ H}
    else ∅
  have hB : ∀ nk, volume (B nk) = 0 := by
    intro nk
    by_cases hR : (dyad nk.1 nk.2 : ℝ≥0∞) < z.1
    · let η := Classical.choose (exists_isGeneratingTrace_of_mem_DSet hz hR)
      have hη := Classical.choose_spec (exists_isGeneratingTrace_of_mem_DSet hz hR)
      have hcontR : ContinuousOn (dec z.2)
          {s : ℝ≥0 | (s : ℝ≥0∞) < (dyad nk.1 nk.2 : ℝ≥0∞)} :=
        (continuousOn_of_mem_DSet hz).mono fun s hs => lt_trans hs hR
      simpa [B, hR] using Lemma25.volume_setOf_isTipPoint_notMem_H
        (c := Chart.id) (w := dec z.2) (ζ := (dyad nk.1 nk.2 : ℝ≥0∞))
        Chart.isConformal_id hη hcontR
        (dec_zero_of_mem_DSet hz (lt_of_le_of_lt bot_le hR))
    · simp [B, hR]
  have hU : volume (⋃ nk, B nk) = 0 := measure_iUnion_null hB
  refine measure_mono_null ?_ hU
  rintro t ⟨ht0, htζ, hnotH⟩
  let T : ℝ≥0 := t.toNNReal
  obtain ⟨n, k, hTR, hR⟩ := exists_dyad_btwn (t := T) htζ
  obtain ⟨η, hη⟩ := exists_isGeneratingTrace_of_mem_DSet hz hR
  have hzero : dec z.2 0 = 0 := dec_zero_of_mem_DSet hz (lt_of_le_of_lt bot_le htζ)
  have hcontR : ContinuousOn (dec z.2) {s : ℝ≥0 | (s : ℝ≥0∞) < (dyad n k : ℝ≥0∞)} :=
    (continuousOn_of_mem_DSet hz).mono fun s hs => lt_trans hs hR
  have hTRenn : (T : ℝ≥0∞) < (dyad n k : ℝ≥0∞) := by exact_mod_cast hTR
  have hrad := hη.tendsto_fwdMapInv_mul_I hcontR hzero hTRenn
  have htip : Lemma25.IsTipPoint Chart.id (dec z.2) T (η T) := by
    unfold Lemma25.IsTipPoint
    simpa [Chart.id] using hrad
  have heval := evalTrace_driverCode_eq hz hTR hR hη
  refine Set.mem_iUnion.2 ⟨(n, k), ?_⟩
  dsimp [B]
  rw [if_pos hR]
  refine ⟨ht0, ?_, η T, htip, ?_⟩
  · exact hTRenn
  · simpa [T, heval] using hnotH

/-- An interior trace evaluation gives an interior stop for the code driver. -/
theorem interiorStop_of_driverCode_eval {z : DCode} (hz : z ∈ DSet) {T : ℝ≥0}
    (hTζ : (T : ℝ≥0∞) < z.1) (hH : evalTraceAt (driverCodeTrace z) T ∈ H) :
    GW2Later.IsInteriorStop (drvOf z).1 (T : ℝ≥0∞) := by
  obtain ⟨n, k, hTR, hR⟩ := exists_dyad_btwn (t := T) hTζ
  let R : ℝ≥0 := dyad n k
  let raw : ℝ → ℝ := fun s => dec z.2 s.toNNReal
  let W_R : ℝ → ℝ := Ito.clampDrv raw (R : ℝ)
  let W_T : ℝ → ℝ := Ito.clampDrv raw (T : ℝ)
  have hRz : (R : ℝ≥0∞) < z.1 := by simpa [R] using hR
  have hTRenn : (T : ℝ≥0∞) < (R : ℝ≥0∞) := ENNReal.coe_lt_coe.2 (by simpa [R] using hTR)
  have hRposNN : 0 < R := lt_of_le_of_lt bot_le (by simpa [R] using hTR)
  have hRpos : 0 < (R : ℝ≥0∞) := ENNReal.coe_pos.2 hRposNN
  have hzpos : 0 < z.1 := lt_trans hRpos hRz
  have hzero : dec z.2 0 = 0 := dec_zero_of_mem_DSet hz hzpos
  have hcontRaw : ContinuousOn raw (Icc 0 (R : ℝ)) := by
    refine (continuousOn_of_mem_DSet hz).comp continuous_real_toNNReal.continuousOn fun s hs => ?_
    refine lt_of_le_of_lt (ENNReal.coe_le_coe.2 ?_) hRz
    rw [← NNReal.coe_le_coe, Real.coe_toNNReal _ hs.1]
    exact hs.2
  have hR0 : 0 ≤ (R : ℝ) := NNReal.coe_nonneg R
  have hT0 : 0 ≤ (T : ℝ) := NNReal.coe_nonneg T
  have hcontR : Continuous W_R := Ito.continuous_clampDrv hR0 hcontRaw
  have hcontRawT : ContinuousOn raw (Icc 0 (T : ℝ)) :=
    hcontRaw.mono fun s hs => ⟨hs.1, hs.2.trans (by exact_mod_cast hTR.le)⟩
  have hcontT : Continuous W_T := Ito.continuous_clampDrv hT0 hcontRawT
  have hW_R0 : W_R 0 = 0 := by
    change Ito.clampDrv raw (R : ℝ) 0 = 0
    rw [Ito.clampDrv_eqOn ⟨le_rfl, hR0⟩]
    simpa [raw] using hzero
  have hW_T0 : W_T 0 = 0 := by
    change Ito.clampDrv raw (T : ℝ) 0 = 0
    rw [Ito.clampDrv_eqOn ⟨le_rfl, hT0⟩]
    simpa [raw] using hzero
  have hEqRT : EqOn W_R W_T (Icc 0 (T : ℝ)) := by
    intro s hs
    change Ito.clampDrv raw (R : ℝ) s = Ito.clampDrv raw (T : ℝ) s
    rw [Ito.clampDrv_eqOn ⟨hs.1, hs.2.trans (by exact_mod_cast hTR.le)⟩,
      Ito.clampDrv_eqOn ⟨hs.1, hs.2⟩]
  have hrawR : ∀ s ∈ Icc (0 : ℝ) (R : ℝ), raw s = W_R s := by
    intro s hs
    change raw s = Ito.clampDrv raw (R : ℝ) s
    exact (Ito.clampDrv_eqOn hs).symm
  have hraw_eq_R := fwdMapInv_eq_of_eqOn (W := raw) (W' := W_R)
    (NNReal.coe_nonneg T) (by exact_mod_cast hTR) hrawR
  have hR_eq_T : ∀ y : ℝ, 0 < y →
      QuantumZipper.fwdMapInv W_R (T : ℝ) (y * Complex.I) =
        QuantumZipper.fwdMapInv W_T (T : ℝ) (y * Complex.I) := by
    intro y hy
    have hyH : (y : ℂ) * Complex.I ∈ H := by
      change 0 < ((y : ℂ) * Complex.I).im
      simpa using hy
    exact @LP.fwdMapInv_eq_of_eqOn_Icc W_R W_T hcontR hcontT hW_R0 hW_T0
      (T : ℝ) (NNReal.coe_nonneg T) hEqRT (y * Complex.I) hyH
  have hfwd : ∀ y : ℝ, 0 < y →
      QuantumZipper.fwdMapInv raw (T : ℝ) (y * Complex.I) =
        QuantumZipper.fwdMapInv W_T (T : ℝ) (y * Complex.I) := by
    intro y hy
    rw [hraw_eq_R]
    exact hR_eq_T y hy
  obtain ⟨η, hη⟩ := exists_isGeneratingTrace_of_mem_DSet hz hR
  have hcontR' : ContinuousOn (dec z.2)
      {s : ℝ≥0 | (s : ℝ≥0∞) < (R : ℝ≥0∞)} :=
    (continuousOn_of_mem_DSet hz).mono fun s hs => lt_trans hs hR
  have hrad := hη.tendsto_fwdMapInv_mul_I hcontR' hzero (by exact_mod_cast hTR)
  have hradT : Tendsto (fun y : ℝ => QuantumZipper.fwdMapInv W_T (T : ℝ) (y * Complex.I))
      (𝓝[>] 0) (𝓝 (η T)) := by
    refine hrad.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with y hy
    exact hfwd y hy
  have heval := evalTrace_driverCode_eq hz (by simpa [R] using hTR) hR hη
  have hηH : η T ∈ H := by rw [← heval]; exact hH
  have hWstop : (fun s : ℝ => (drvOf z).1
      (min (s.toNNReal : ℝ≥0∞) (T : ℝ≥0∞)).toNNReal) = W_T := by
    funext s
    by_cases hs : 0 ≤ s
    · have hst : (s.toNNReal : ℝ) = s := Real.coe_toNNReal _ hs
      rw [drvOf_of_mem hz]
      simp only [Prod.fst]
      rw [drvPath_of_lt]
      · simp only [W_T, raw, Ito.clampDrv]
        have harg : (min (s.toNNReal : ℝ≥0∞) (T : ℝ≥0∞)).toNNReal =
            (min s T).toNNReal := by
          calc
            _ = min s.toNNReal T := by rw [← ENNReal.coe_min, ENNReal.toNNReal_coe]
            _ = (min s T).toNNReal := by
              apply NNReal.eq
              rw [NNReal.coe_min, Real.coe_toNNReal _ hs,
                Real.coe_toNNReal _ (le_min hs (NNReal.coe_nonneg T))]
        simpa only [max_eq_left hs] using congrArg (dec z.2) harg
      · exact lt_of_le_of_lt
          (ENNReal.coe_le_coe.2 (show min s.toNNReal T ≤ T from min_le_right _ _))
          hTζ
    · have hs' : s ≤ 0 := le_of_not_ge hs
      have hsn : s.toNNReal = 0 := Real.toNNReal_of_nonpos hs'
      rw [drvOf_of_mem hz]
      simp only [Prod.fst]
      rw [drvPath_of_lt]
      · simp [W_T, raw, Ito.clampDrv, hs', hsn, hzero]
      · simpa [hsn] using hzpos
  unfold GW2Later.IsInteriorStop
  refine ⟨η T, hηH, ?_⟩
  unfold Chart.tipAt Chart.id
  rw [hWstop]
  exact hradT

theorem volume_section_vecInteriorBadSet {h12p : Theorem12ParamStatement.{u}} {κ : ℝ} (hκ : 0 < κ)
    (Θ : Set ℝ) (βA : BoundaryWord × ℝ × RecData → BoundaryWord) (c₀ : BoundaryWord) (x₀ : ℝ)
    (angles : List {a : ℝ // a ∈ Θ}) {n : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    {h : Ω → DistOn upperHalfPlaneOpens}
    (i : Fin n) (ω : Ω) (v : Fin n → ℝ) :
    volume {x : ℝ | (ω, Function.update v i x) ∈
      vecInteriorBadSet h12p hκ Θ βA c₀ x₀ angles (n := n) (h := h) i} = 0 := by
  classical
  by_cases hnonempty : ∃ x, (ω, Function.update v i x) ∈
      vecInteriorBadSet h12p hκ Θ βA c₀ x₀ angles (n := n) (h := h) i
  · obtain ⟨x₀', hbad₀⟩ := hnonempty
    simp only [vecInteriorBadSet, mem_setOf_eq, Function.update_self] at hbad₀
    rcases hbad₀ with ⟨hx₀, hp₀, hsuccess₀, hnotH₀⟩
    let z : DCode := vecCanonCode h12p hκ Θ βA c₀ x₀ angles v (h ω) i.val
    have hcode (x : ℝ) :
        vecCanonCode h12p hκ Θ βA c₀ x₀ angles (Function.update v i x) (h ω) i.val = z :=
      vecCanonCode_update_prev h12p hκ Θ βA c₀ x₀ angles v i x (h ω)
    have htime₀ : (vecOwnTime (Function.update v i x₀') i : ℝ≥0∞) < (drvOf z).2 := by
      have hsucc := hsuccess₀ i (by omega)
      simpa [vecOwnTimes, vecCanonLife, hcode x₀', z] using hsucc
    have htpos₀ : 0 < vecOwnTime (Function.update v i x₀') i :=
      vecOwnTime_pos_of_abs v i x₀' hx₀ hp₀
    have hζpos : 0 < (drvOf z).2 := lt_trans (ENNReal.coe_pos.2 htpos₀) htime₀
    have hz : z ∈ DSet := by
      by_contra hz
      have hzero : (drvOf z).2 = 0 := by simp [drvOf, hz]
      rw [hzero] at hζpos
      exact (lt_irrefl 0) hζpos
    let s : ℝ := (vecPrevTime v i).toNNReal
    let D : Set ℝ := {t : ℝ | 0 ≤ t ∧ ((t.toNNReal : ℝ≥0) : ℝ≥0∞) < (drvOf z).2 ∧
      evalTraceAt (driverCodeTrace z) t.toNNReal ∉ H}
    have hD : volume D = 0 := by
      simpa [D, drvOf, hz] using volume_driverCode_eval_notH hz
    have hshift : volume {x : ℝ | x - s ∈ D} = 0 := by
      have hpre : {x : ℝ | x - s ∈ D} = (fun x : ℝ => x + -s) ⁻¹' D := by
        ext x
        simp only [mem_preimage, mem_setOf_eq, sub_eq_add_neg]
      calc
        volume {x : ℝ | x - s ∈ D} = volume D := by rw [hpre, measure_preimage_add_right]
        _ = 0 := hD
    have hsubset : {x : ℝ | (ω, Function.update v i x) ∈
        vecInteriorBadSet h12p hκ Θ βA c₀ x₀ angles (n := n) (h := h) i} ⊆
        {x : ℝ | x - s ∈ D} := by
      intro x hx
      simp only [vecInteriorBadSet, mem_setOf_eq, Function.update_self] at hx
      rcases hx with ⟨hxpos, hprev, hsucc, hnotH⟩
      let own := vecOwnTime (Function.update v i x) i
      have hownpos : 0 < own := vecOwnTime_pos_of_abs v i x hxpos hprev
      have hownlt : (own : ℝ≥0∞) < (drvOf z).2 := by
        have hi := hsucc i (by omega)
        simpa [own, vecOwnTimes, vecCanonLife, hcode x, z] using hi
      have hownReal : (own : ℝ) = x - s := by
        rw [vecPrevTime_update_self v i x] at hprev
        have hle : (vecPrevTime v i).toNNReal ≤ x.toNNReal := Real.toNNReal_le_toNNReal hprev.le
        unfold own vecOwnTime
        simp only [Function.update_self]
        rw [vecPrevTime_update_self]
        rw [NNReal.coe_sub hle, Real.coe_toNNReal _ hxpos.le]
      have htoNN : (x - s).toNNReal = own := by
        rw [← hownReal, Real.toNNReal_coe]
      have heval : vecCanonEval h12p hκ Θ βA c₀ x₀ angles (h := h) i
          (ω, Function.update v i x) =
          evalTraceAt (driverCodeTrace z) own := by
        unfold vecCanonEval
        rw [evalTrace_apply_eq]
        change evalTraceAt
          (driverCodeTrace (vecCanonCode h12p hκ Θ βA c₀ x₀ angles
            (Function.update v i x) (h ω) i.val)) own = _
        rw [hcode x]
      change 0 ≤ x - s ∧ ((x - s).toNNReal : ℝ≥0∞) < (drvOf z).2 ∧
        evalTraceAt (driverCodeTrace z) (x - s).toNNReal ∉ H
      refine ⟨?_, ?_, ?_⟩
      · linarith [NNReal.coe_nonneg own, hownReal]
      · rw [htoNN]
        exact hownlt
      · rw [htoNN, ← heval]
        exact hnotH
    exact measure_mono_null hsubset hshift
  · have hEmpty : {x : ℝ | (ω, Function.update v i x) ∈
        vecInteriorBadSet h12p hκ Θ βA c₀ x₀ angles (n := n) (h := h) i} = ∅ := by
      ext x
      simp only [vecInteriorBadSet, mem_setOf_eq, mem_empty_iff_false, iff_false]
      exact fun hx => hnonempty ⟨x, hx⟩
    rw [hEmpty, measure_empty]

/-! ### The almost-everywhere coordinate form of GB9a -/

/-- A measurable set of finite vectors is null when almost every section in one coordinate is null. -/
theorem volume_eq_zero_of_ae_update {n : ℕ} {A : Set (Fin (n + 1) → ℝ)} (hA : MeasurableSet A)
    (i : Fin (n + 1))
    (hsec : ∀ᵐ w ∂(Measure.pi fun _ : Fin n => (volume : Measure ℝ)),
      volume {x : ℝ | Function.update (Fin.insertNth (α := fun _ => ℝ) i 0 w) i x ∈ A} = 0) :
    volume A = 0 := by
  set e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => ℝ) i with hedef
  have hmp := measurePreserving_piFinSuccAbove (fun _ : Fin (n + 1) => (volume : Measure ℝ)) i
  have hpre : e ⁻¹' (e.symm ⁻¹' A) = A := by
    ext v
    simp only [mem_preimage, MeasurableEquiv.symm_apply_apply]
  have h1 : volume A = ((volume : Measure ℝ).prod (Measure.pi fun _ : Fin n => (volume : Measure ℝ)))
      (e.symm ⁻¹' A) := by
    rw [← hmp.measure_preimage (e.symm.measurable hA).nullMeasurableSet, hpre, volume_pi]
  rw [h1, Measure.prod_apply_symm (e.symm.measurable hA)]
  refine lintegral_eq_zero_of_ae_eq_zero ?_
  filter_upwards [hsec] with w hw
  show volume ((fun x => (x, w)) ⁻¹' (e.symm ⁻¹' A)) = 0
  have hset : (fun x => (x, w)) ⁻¹' (e.symm ⁻¹' A) =
      {x : ℝ | Function.update (Fin.insertNth (α := fun _ => ℝ) i 0 w) i x ∈ A} := by
    ext x
    simp only [mem_preimage, mem_ofPred_eq]
    rw [← insertNth_eq_update]
    rfl
  rw [hset]
  exact hw

/-- A coordinate section null for almost every field value at each fixed complementary vector makes the joint
field/time bad set null. -/
theorem product_null_of_ae_coord {Ω : Type*} [MeasurableSpace Ω] {n : ℕ} (P : Measure Ω) [SFinite P]
    {A : Set (Ω × (Fin (n + 1) → ℝ))} (hA : MeasurableSet A) (i : Fin (n + 1))
    (hsec : ∀ v : Fin (n + 1) → ℝ, ∀ᵐ ω ∂P,
      volume {x : ℝ | (ω, Function.update v i x) ∈ A} = 0) : (P.prod volume) A = 0 := by
  let ν : Measure (Fin n → ℝ) := Measure.pi fun _ => (volume : Measure ℝ)
  let C : Set (Ω × (Fin n → ℝ)) := {p | volume {x : ℝ |
    (p.1, Function.update (Fin.insertNth (α := fun _ => ℝ) i 0 p.2) i x) ∈ A} = 0}
  have hCmeas : MeasurableSet C := by
    have hmvec : Measurable fun p : (Ω × (Fin n → ℝ)) × ℝ =>
        Function.update (Fin.insertNth (α := fun _ => ℝ) i 0 p.1.2) i p.2 := by
      apply measurable_pi_iff.2
      intro j
      refine Fin.succAboveCases i ?_ (fun q => ?_) j
      · simp only [Function.update_self]
        exact measurable_snd
      · simp only [Function.update_of_ne (Fin.succAbove_ne i q), Fin.insertNth_apply_succAbove]
        exact (measurable_pi_apply q).comp (measurable_snd.comp measurable_fst)
    have hrel : MeasurableSet {p : (Ω × (Fin n → ℝ)) × ℝ |
        (p.1.1, Function.update (Fin.insertNth (α := fun _ => ℝ) i 0 p.1.2) i p.2) ∈ A} :=
      (measurable_fst.comp measurable_fst).prodMk hmvec hA
    exact measurableSet_eq_fun (measurable_measure_prodMk_left hrel) measurable_const
  have haecomm := Measure.ae_ae_comm (μ := P) (ν := ν) (p := fun ω w => (ω, w) ∈ C) (by
    change MeasurableSet C
    exact hCmeas)
  have hae : ∀ᵐ ω ∂P, ∀ᵐ w ∂ν, (ω, w) ∈ C := by
    refine haecomm.mpr ?_
    exact Filter.Eventually.of_forall fun w => hsec (Fin.insertNth (α := fun _ => ℝ) i 0 w)
  have hsect : ∀ᵐ ω ∂P, volume {v : Fin (n + 1) → ℝ | (ω, v) ∈ A} = 0 := by
    filter_upwards [hae] with ω hω
    have hAw : MeasurableSet {v : Fin (n + 1) → ℝ | (ω, v) ∈ A} := measurable_prodMk_left hA
    exact volume_eq_zero_of_ae_update hAw i (by simpa [C] using hω)
  exact (Measure.measure_prod_null hA).2 hsect

theorem product_null_of_ae_coord_any {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [SFinite P]
    {n : ℕ} {A : Set (Ω × (Fin n → ℝ))} (hA : MeasurableSet A) (i : Fin n)
    (hsec : ∀ v : Fin n → ℝ, ∀ᵐ ω ∂P,
      volume {x : ℝ | (ω, Function.update v i x) ∈ A} = 0) : (P.prod volume) A = 0 := by
  cases n with
  | zero => exact i.elim0
  | succ n => exact product_null_of_ae_coord P hA i hsec

/-- GB9a selection with the section quantifiers in the form furnished by a parameterized family: for each fixed
complementary time vector, almost every field sample has a null section in the selected coordinate. -/
theorem gb9a_of_ae_coord_sections {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [SFinite P] {ι : Type*}
    [Countable ι] (S : ι → Finset ℕ)
    (Bad : (j : ι) → Fin (S j).card → Set (Ω × (Fin (S j).card → ℝ)))
    (hm : ∀ j k, MeasurableSet (Bad j k))
    (hsec : ∀ j k (v : Fin (S j).card → ℝ), ∀ᵐ ω ∂P,
      volume {x : ℝ | (ω, Function.update v k x) ∈ Bad j k} = 0) :
    ∃ q : ℕ → ℝ, (∀ m, 0 < q m) ∧ Ioi 0 ⊆ closure (range q) ∧
      ∀ j (e : Fin (S j).card ≃ S j) k, P {ω | (ω, fun i => q (e i)) ∈ Bad j k} = 0 := by
  classical
  set B : (j : ι) → Set (Ω × (S j → ℝ)) := fun j =>
    ⋃ (e : Fin (S j).card ≃ S j) (k : Fin (S j).card), {p | (p.1, fun i => p.2 (e i)) ∈ Bad j k} with hBdef
  have hBm : ∀ j, MeasurableSet (B j) := fun j =>
    MeasurableSet.iUnion fun e => MeasurableSet.iUnion fun k =>
      (measurable_fst.prodMk (measurable_pi_iff.2 fun i => (measurable_pi_apply (e i)).comp measurable_snd))
        (hm j k)
  have hnull : ∀ j, ∀ᵐ y ∂(Measure.pi fun _ : S j => (volume : Measure ℝ)), P {ω | (ω, y) ∈ B j} = 0 := by
    intro j
    refine ae_measure_section_eq_zero_of_ae P _ (hBm j) ?_
    have hsecω : ∀ e : Fin (S j).card ≃ S j, ∀ k : Fin (S j).card,
        ∀ᵐ ω ∂P, (Measure.pi fun _ : S j => (volume : Measure ℝ))
          {y | (ω, fun i => y (e i)) ∈ Bad j k} = 0 := by
      intro e k
      have hA : MeasurableSet {p : Ω × (Fin (S j).card → ℝ) | p ∈ Bad j k} := hm j k
      have hprod := product_null_of_ae_coord_any P hA k (hsec j k)
      have hω : ∀ᵐ ω ∂P, volume {v : Fin (S j).card → ℝ | (ω, v) ∈ Bad j k} = 0 :=
        (Measure.measure_prod_null hA).1 hprod
      filter_upwards [hω] with ω hω
      have hAw : MeasurableSet {v : Fin (S j).card → ℝ | (ω, v) ∈ Bad j k} := measurable_prodMk_left hA
      simpa only [Set.mem_setOf_eq] using (volume_comp_equiv e hAw).trans hω
    have hsecω' : ∀ᵐ ω ∂P, ∀ e : Fin (S j).card ≃ S j, ∀ k : Fin (S j).card,
        (Measure.pi fun _ : S j => (volume : Measure ℝ)) {y | (ω, fun i => y (e i)) ∈ Bad j k} = 0 :=
      ae_all_iff.2 fun e => ae_all_iff.2 fun k => hsecω e k
    filter_upwards [hsecω'] with ω hω
    have hset : {y : S j → ℝ | (ω, y) ∈ B j} =
        ⋃ (e : Fin (S j).card ≃ S j) (k : Fin (S j).card),
          {y : S j → ℝ | (ω, fun i => y (e i)) ∈ Bad j k} := by
      ext y
      simp only [hBdef, mem_iUnion, mem_ofPred_eq]
    rw [hset]
    refine measure_iUnion_null fun e => measure_iUnion_null fun k => hω e k
  obtain ⟨q, hq0, hqd, hq⟩ := Supp8.gb9a_exists_dense P S B hnull
  refine ⟨q, hq0, hqd, fun j e k => measure_mono_null (fun ω hω => ?_) (hq j)⟩
  simp only [mem_ofPred_eq, hBdef, mem_iUnion]
  exact ⟨e, k, hω⟩

end GW2Tip

end Theorem14

end InteractingSLE
