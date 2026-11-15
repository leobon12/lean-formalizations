/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW1BorelGraph
import InteractingSLE.Spec.Supplement.WalkLeafRead
import InteractingSLE.Spec.Supplement.WalkStageLocalMeas
import InteractingSLE.Spec.Supplement.BW1TermStatement

/-!
# BW1's terminal relation: the coded witness set

Packet PROVE-BW1-DET. The relation `BW1Term.IsTermRelOf U V D` (the relative counterflow `U` of `V` after the
piece `D`) is tested on countable data:

* `U`, `V` by their rational codes (`GW1Borel.RegularCode`, with the measurable trace selector `GW1Borel.trace`);
* the piece by its **record** `recOf ⊤ D : RecData` (the retained datum read at rational times; measurable in the
  past of a staged history), with the continuous driver `recDrvC r` (the existing regularization of the rational
  samples) and the measurable trace selector `WalkLeaf.recPath r`;
* the clock by a rational code (`GW1Borel.clock`).

`witnessSet` lists the countable tests: canonical clock code, strict increase, the clock range below the first
visit of the root and the piece (`no hit up to ℓ(n)` and `a hit at sup ℓ` when finite, written with distances to the
inverted piece trace at rational times), the zero pattern of the two traces, and the boundary value of the chart of
the piece at the inverted relative tip (a sequence along vertical segments). Every test is a Borel condition on the
whole witness space (`measurableSet_witnessSet`); `BW1DetIdent` proves that for regular data the tests are exactly
the relation.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology
open scoped NNReal ENNReal NNRat
open QuantumZipper (H Hbar)

namespace InteractingSLE.Theorem14.BW1Det

open Exist Exist.StagedLaw GW1Borel

/-! ### Records of pieces -/

/-- The rational code of the stopped driver of a record. -/
def recCode (r : RecData) : Code := fun q : ℚ≥0 => r.1 (q : ℚ)

/-- **The continuous driver of a record** (the regularization of its rational samples). -/
def recDrvC (r : RecData) : ℝ≥0 → ℝ := driver (recCode r)

/-- **The chart after the piece of a record**, in the launch coordinate (the analogue of `BW1Term.termChart`). -/
def recChart (r : RecData) : Chart :=
  (Chart.id.recenter 0).loewner (fun x : ℝ => recDrvC r x.toNNReal) ((r.2.1.toNNReal : ℝ≥0) : ℝ)

/-- The inversion `z ↦ −1/z`. -/
abbrev negInv (z : ℂ) : ℂ := -z⁻¹

theorem measurable_recCode : Measurable recCode :=
  measurable_pi_iff.2 fun q => (measurable_pi_apply (q : ℚ)).comp measurable_fst

theorem continuous_recDrvC (r : RecData) : Continuous (recDrvC r) := continuous_driver _

theorem recDrvC_zero (r : RecData) : recDrvC r 0 = 0 := driver_zero _

theorem recChart_inv (r : RecData) (w : ℂ) :
    (recChart r).2.1 w =
      QuantumZipper.fwdMapInv (fun x : ℝ => recDrvC r x.toNNReal) ((r.2.1.toNNReal : ℝ≥0) : ℝ) w := by
  change QuantumZipper.fwdMapInv _ _ w + ((0 : ℝ) : ℂ) = _
  rw [Complex.ofReal_zero, add_zero]

/-- The inverse chart of a record, evaluated at a measurable point of `ℍ`, is measurable. -/
theorem measurable_recChart_inv {α : Type*} [MeasurableSpace α] {r : α → RecData} (hr : Measurable r)
    {Z : α → ℂ} (hZ : Measurable Z) (hZH : ∀ a, Z a ∈ H) : Measurable fun a => (recChart (r a)).2.1 (Z a) := by
  simp only [recChart_inv]
  exact WalkLaw.measurable_fwdMapInv_randomTime (B := fun t a => recDrvC (r a) t)
    (fun t => (measurable_driver t).comp (measurable_recCode.comp hr))
    (fun a => continuous_recDrvC (r a)) (fun a => recDrvC_zero (r a))
    (ENNReal.measurable_toNNReal.comp (measurable_fst.comp (measurable_snd.comp hr))) hZ hZH

/-! ### Traces of regular codes lie in the closed half-plane -/

theorem trace_mem_Hbar (f : RegularCode) (t : ℝ≥0) : trace f t ∈ Hbar :=
  Sec7.IsGeneratingTrace.mem_Hbar (trace_properties f).1 (continuous_driver _).continuousOn (driver_zero _) le_top

theorem negInv_trace_add_mem_H (f : RegularCode) (t : ℝ≥0) (n : ℕ) :
    negInv (trace f t) + Complex.I / ((n : ℂ) + 1) ∈ H := by
  have h1 : 0 ≤ (negInv (trace f t)).im := GW4Traverse.negInv_mem_Hbar (trace_mem_Hbar f t)
  have h2 : (Complex.I / ((n : ℂ) + 1)).im = 1 / ((n : ℝ) + 1) := by
    rw [show ((n : ℂ) + 1) = (((n : ℝ) + 1 : ℝ) : ℂ) by push_cast; ring, Complex.div_ofReal_im,
      Complex.I_im]
  change 0 < (negInv (trace f t) + Complex.I / ((n : ℂ) + 1)).im
  rw [Complex.add_im, h2]
  have : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
  linarith

/-! ### The witness space and the tests -/

/-- **The witness space**: codes of the relative driver `U` and of the counterflow `V`, the record of the piece,
the code of the clock. -/
abbrev Wsp : Type := ((RegularCode × RegularCode) × RecData) × Code

/-- The supremum of the coded clock over integer times. -/
def clockSup (c : Code) : ℝ≥0∞ := ⨆ n : ℕ, (clock c n : ℝ≥0∞)

/-- **The countable tests.** -/
def witnessSet : Set Wsp := {x |
  (∀ q : ℚ≥0, x.2 q = (clock x.2 q : ℝ)) ∧
  (∀ a b : ℚ≥0, a < b → clock x.2 a < clock x.2 b) ∧
  (∀ n : ℕ, ∃ k : ℕ, ∀ q p : ℚ≥0, (q : ℝ≥0) ≤ clock x.2 n → ((p : ℝ≥0) : ℝ≥0∞) ≤ x.1.2.2.1 →
    WalkLeaf.recPath x.1.2 p ≠ 0 →
      (1 : ℝ) / ((k : ℝ) + 1) ≤ ‖trace x.1.1.2 q - negInv (WalkLeaf.recPath x.1.2 p)‖) ∧
  (clockSup x.2 < ⊤ → ∀ k : ℕ, ∃ p : ℚ≥0, ((p : ℝ≥0) : ℝ≥0∞) ≤ x.1.2.2.1 ∧ WalkLeaf.recPath x.1.2 p ≠ 0 ∧
    ‖trace x.1.1.2 (clockSup x.2).toNNReal - negInv (WalkLeaf.recPath x.1.2 p)‖ < (1 : ℝ) / ((k : ℝ) + 1)) ∧
  (∀ q : ℚ≥0, (trace x.1.1.1 q = 0 ↔ trace x.1.1.2 (clock x.2 q) = 0)) ∧
  (∀ q : ℚ≥0, trace x.1.1.1 q ≠ 0 →
    Tendsto (fun n : ℕ => (recChart x.1.2).2.1 (negInv (trace x.1.1.1 q) + Complex.I / ((n : ℂ) + 1))) atTop
      (𝓝 (negInv (trace x.1.1.2 (clock x.2 q)))))}

/-! ### Measurability -/

section Meas

theorem measurable_wU : Measurable fun x : Wsp => x.1.1.1 := measurable_fst.comp (measurable_fst.comp measurable_fst)
theorem measurable_wV : Measurable fun x : Wsp => x.1.1.2 := measurable_snd.comp (measurable_fst.comp measurable_fst)
theorem measurable_wR : Measurable fun x : Wsp => x.1.2 := measurable_snd.comp measurable_fst
theorem measurable_wC : Measurable fun x : Wsp => x.2 := measurable_snd

theorem measurable_wclock (t : ℝ≥0) : Measurable fun x : Wsp => clock x.2 t :=
  (measurable_clock t).comp measurable_wC

theorem measurable_traceV_clock (q : ℝ≥0) : Measurable fun x : Wsp => trace x.1.1.2 (clock x.2 q) :=
  @Measurable.comp Wsp (RegularCode × ℝ≥0) ℂ _ _ _ (fun p => trace p.1 p.2) (fun x => (x.1.1.2, clock x.2 q))
    measurable_trace_eval (measurable_wV.prodMk (measurable_wclock q))

theorem measurable_clockSup : Measurable fun x : Wsp => clockSup x.2 :=
  Measurable.iSup fun n => measurable_coe_nnreal_ennreal.comp (measurable_wclock n)

theorem measurable_traceV_sup : Measurable fun x : Wsp => trace x.1.1.2 (clockSup x.2).toNNReal :=
  @Measurable.comp Wsp (RegularCode × ℝ≥0) ℂ _ _ _ (fun p => trace p.1 p.2)
    (fun x => (x.1.1.2, (clockSup x.2).toNNReal))
    measurable_trace_eval (measurable_wV.prodMk (ENNReal.measurable_toNNReal.comp measurable_clockSup))

theorem measurable_recPath_w (p : ℝ≥0) : Measurable fun x : Wsp => WalkLeaf.recPath x.1.2 p :=
  (WalkLeaf.measurable_recPath p).comp measurable_wR

theorem measurable_wL : Measurable fun x : Wsp => x.1.2.2.1 := measurable_fst.comp (measurable_snd.comp measurable_wR)

theorem measurable_traceU (q : ℝ≥0) : Measurable fun x : Wsp => trace x.1.1.1 q :=
  (measurable_trace q).comp measurable_wU

theorem measurable_traceV (q : ℝ≥0) : Measurable fun x : Wsp => trace x.1.1.2 q :=
  (measurable_trace q).comp measurable_wV

/-- `{x | Tendsto (a n x) atTop (𝓝 (b x))}` is measurable for measurable `a n`, `b`. -/
theorem measurableSet_tendsto_fun {α : Type*} [MeasurableSpace α] {a : ℕ → α → ℂ} {b : α → ℂ}
    (ha : ∀ n, Measurable (a n)) (hb : Measurable b) :
    MeasurableSet {x | Tendsto (fun n => a n x) atTop (𝓝 (b x))} := by
  have h := measurableSet_tendsto (𝓝 (0 : ℂ)) (l := atTop) (f := fun n x => a n x - b x)
    fun n => (ha n).sub hb
  have e : {x | Tendsto (fun n => a n x) atTop (𝓝 (b x))} =
      {x | Tendsto (fun n => a n x - b x) atTop (𝓝 0)} := by
    ext x
    exact (tendsto_sub_nhds_zero_iff (l := atTop) (x := b x) (u := fun n => a n x)).symm
  rw [e]
  exact h

theorem measurableSet_witnessSet : MeasurableSet witnessSet := by
  have hrp := measurable_recPath_w
  have hneg : ∀ p : ℝ≥0, Measurable fun x : Wsp => negInv (WalkLeaf.recPath x.1.2 p) :=
    fun p => ((hrp p).inv).neg
  have hP : ∀ {s : Set Wsp}, MeasurableSet s → Measurable fun x => x ∈ s := fun hs => measurable_mem.2 hs
  have h1 : Measurable fun x : Wsp => ∀ q : ℚ≥0, x.2 q = (clock x.2 q : ℝ) :=
    Measurable.forall fun q => hP (measurableSet_eq_fun ((measurable_pi_apply q).comp measurable_wC)
      (measurable_coe_nnreal_real.comp (measurable_wclock q)))
  have h2 : Measurable fun x : Wsp => ∀ a b : ℚ≥0, a < b → clock x.2 a < clock x.2 b :=
    Measurable.forall fun a => Measurable.forall fun b => measurable_const.imp
      (hP (measurableSet_lt (f := fun x : Wsp => clock x.2 a) (g := fun x : Wsp => clock x.2 b)
        (measurable_wclock a) (measurable_wclock b)))
  have h3 : Measurable fun x : Wsp => ∀ n : ℕ, ∃ k : ℕ, ∀ q p : ℚ≥0, (q : ℝ≥0) ≤ clock x.2 n →
      ((p : ℝ≥0) : ℝ≥0∞) ≤ x.1.2.2.1 → WalkLeaf.recPath x.1.2 p ≠ 0 →
        (1 : ℝ) / ((k : ℝ) + 1) ≤ ‖trace x.1.1.2 q - negInv (WalkLeaf.recPath x.1.2 p)‖ :=
    Measurable.forall fun n => Measurable.exists fun k => Measurable.forall fun q => Measurable.forall fun p =>
      (hP (measurableSet_le measurable_const (measurable_wclock n))).imp
        ((hP (measurableSet_le measurable_const measurable_wL)).imp
          ((hP (measurableSet_eq_fun (hrp p) measurable_const)).not.imp
            (hP (measurableSet_le measurable_const (((measurable_traceV q).sub (hneg p)).norm)))))
  have h4 : Measurable fun x : Wsp => clockSup x.2 < ⊤ → ∀ k : ℕ, ∃ p : ℚ≥0,
      ((p : ℝ≥0) : ℝ≥0∞) ≤ x.1.2.2.1 ∧ WalkLeaf.recPath x.1.2 p ≠ 0 ∧
        ‖trace x.1.1.2 (clockSup x.2).toNNReal - negInv (WalkLeaf.recPath x.1.2 p)‖ < (1 : ℝ) / ((k : ℝ) + 1) :=
    (hP (measurableSet_lt measurable_clockSup measurable_const)).imp
      (Measurable.forall fun k => Measurable.exists fun p =>
        (hP (measurableSet_le measurable_const measurable_wL)).and
          ((hP (measurableSet_eq_fun (hrp p) measurable_const)).not.and
            (hP (measurableSet_lt ((measurable_traceV_sup.sub (hneg p)).norm) measurable_const))))
  have h5 : Measurable fun x : Wsp => ∀ q : ℚ≥0, (trace x.1.1.1 q = 0 ↔ trace x.1.1.2 (clock x.2 q) = 0) :=
    Measurable.forall fun q => (hP (measurableSet_eq_fun (measurable_traceU q) measurable_const)).iff
      (hP (measurableSet_eq_fun (measurable_traceV_clock q) measurable_const))
  have h6 : Measurable fun x : Wsp => ∀ q : ℚ≥0, trace x.1.1.1 q ≠ 0 →
      Tendsto (fun n : ℕ => (recChart x.1.2).2.1 (negInv (trace x.1.1.1 q) + Complex.I / ((n : ℂ) + 1)))
        atTop (𝓝 (negInv (trace x.1.1.2 (clock x.2 q)))) := by
    refine Measurable.forall fun q => (hP (measurableSet_eq_fun (measurable_traceU q) measurable_const)).not.imp
      (hP (measurableSet_tendsto_fun (fun n => ?_) ((measurable_traceV_clock q).inv.neg)))
    exact measurable_recChart_inv measurable_wR
      ((((measurable_traceU q).inv).neg).add measurable_const)
      (fun x => negInv_trace_add_mem_H x.1.1.1 q n)
  exact measurableSet_setOfPred.2 (h1.and (h2.and (h3.and (h4.and (h5.and h6)))))

end Meas

end InteractingSLE.Theorem14.BW1Det
