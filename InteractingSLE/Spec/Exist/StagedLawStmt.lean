/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Exist.StagedLawRun
import InteractingSLE.Spec.Exist.StagedLawKernel
import InteractingSLE.Spec.Sec7.LocalExtGChart

/-!
# The staged conditional law: retained records, their charts, and the two named inputs

Packet PROVE-STAGEDLAW. A launched piece is retained through its record `recOf t e` (the entry of `pastMap`: the stopped
driver at rational times, the stop time `min t ζ` and the threshold flag). The Loewner chart of the stopped piece is
read
from the record (`recChart`, through PROVE-LOCEXT-G's `histChart`, conformal for every record); on a good record it is
the frozen chart of the launch (`recChart_eq_loewner`).

## The two named inputs

* **`StopLawStatement`** (Lemma GW1, p. 618: "every finite completed stage … and every available ordinary prefix have
  their full marked local-set kernel"; Theorem 1.1 at the stop `min t ζ`, with the lifetime limit of GW1/C.6 when the
  piece ends at its continuation threshold): for one angle-`θ` flow line of a GFF with a sorted word datum `c` under a
  probability measure `Q`, run for own time `t`, almost surely the stopped driver is continuous (`IsDrvGood` of its
  record) and, conditionally on the record, the field read in the record chart has the Gaussian characteristic
  functional of a word `β (c, θ, record)`, with `β` jointly measurable and sorted.
* **`RunMeasStatement`** (deterministic): for measurable everywhere-regular drivers, the event "instruction `k`
  launches a piece" and the forward chart map at every point after `k` instructions are measurable.

## Main definitions and results

* `retOf`, `recOf`, `measurable_recOf` (for regular drivers);
* `recHist`, `recChart`, `isConformal_recChart`, `recField`, `measurable_recField`;
* `histDrv_recHist`, **`recChart_eq_loewner`**: on a good record the record chart is the frozen launch chart.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal

universe u

namespace InteractingSLE

namespace Exist

namespace StagedLaw

open LQGMetric Restart Staged

/-! ### Records -/

/-- The value space of a retained record (an entry of `Staged.PastData`). -/
abbrev RecData : Type := (ℚ → ℝ) × ℝ≥0∞ × Bool

/-- The retained datum of a piece with driver `e` run for own time `t` (`ExplState.launch`). -/
def retOf (t : ℝ≥0∞) (e : (ℝ≥0 → ℝ) × ℝ≥0∞) : (ℝ≥0 → ℝ) × ℝ≥0∞ × Bool :=
  (fun r => e.1 (min (r : ℝ≥0∞) (min t e.2)).toNNReal, min t e.2, decide (e.2 ≤ t))

/-- The record of a piece: its retained datum read at rational times. -/
def recOf (t : ℝ≥0∞) (e : (ℝ≥0 → ℝ) × ℝ≥0∞) : RecData := readRec (retOf t e)

/-- **The record of a regular driver is a measurable function of the driver.** At a rational time `q` the stopped
driver is the driver at `q` (before the stop), at `t` (a deterministic stop), or at `q` again (after a lifetime
`ζ ≤ q`, where a regular driver is constant). -/
theorem measurable_recOf {Ω : Type*} [MeasurableSpace Ω] {E : Ω → (ℝ≥0 → ℝ) × ℝ≥0∞} (hE : Measurable E)
    (hreg : ∀ ω, IsRegularDriver (E ω)) (t : ℝ≥0∞) : Measurable fun ω => recOf t (E ω) := by
  have hζ : Measurable fun ω => (E ω).2 := measurable_snd.comp hE
  have hev : ∀ s : ℝ≥0, Measurable fun ω => (E ω).1 s := fun s =>
    (measurable_pi_apply s).comp (measurable_fst.comp hE)
  refine Measurable.prodMk (measurable_pi_iff.2 fun q => ?_) (Measurable.prodMk ?_ ?_)
  · -- the sample at `q`
    set s : ℝ≥0 := (q : ℝ).toNNReal
    have e : (fun ω => (retOf t (E ω)).1 s) = fun ω =>
        if (s : ℝ≥0∞) ≤ min t (E ω).2 then (E ω).1 s else if t ≤ (E ω).2 then (E ω).1 t.toNNReal
          else (E ω).1 s := by
      funext ω
      change (E ω).1 (min (s : ℝ≥0∞) (min t (E ω).2)).toNNReal = _
      split_ifs with h1 h2
      · rw [min_eq_left h1, ENNReal.toNNReal_coe]
      · rw [min_eq_right (not_le.1 h1).le, min_eq_left h2]
      · have hlt : (E ω).2 < t := not_le.1 h2
        rw [min_eq_right (not_le.1 h1).le, min_eq_right hlt.le]
        have hζs : (E ω).2 ≤ s := by
          have := (not_le.1 h1).le
          rwa [min_eq_right hlt.le] at this
        exact ((hreg ω).2.2.1 s hζs).symm
    change Measurable fun ω => (retOf t (E ω)).1 s
    rw [e]
    refine Measurable.ite ?_ (hev s) (Measurable.ite ?_ (hev _) (hev s))
    · exact measurableSet_le measurable_const (measurable_const.min hζ)
    · exact measurableSet_le measurable_const hζ
  · exact measurable_const.min hζ
  · have hm : MeasurableSet {ω | (E ω).2 ≤ t} := measurableSet_le hζ measurable_const
    refine measurable_to_countable' fun x => ?_
    cases x
    · convert hm.compl using 1
      ext ω
      simp [retOf]
    · convert hm using 1
      ext ω
      simp [retOf]

/-! ### The chart read from a record -/

/-- The driving history (no force points) read from a record: recorded time `min t ζ`, driver samples. -/
def recHist (r : RecData) : LocalExt.DrivingHist 0 0 :=
  (r.2.1, fun q => (r.1 (q : ℚ), fun i => i.elim0, fun i => i.elim0))

theorem measurable_recHist : Measurable recHist := by
  refine Measurable.prodMk (measurable_fst.comp measurable_snd) (measurable_pi_iff.2 fun q => ?_)
  refine Measurable.prodMk ((measurable_pi_apply (q : ℚ)).comp measurable_fst) (Measurable.prodMk ?_ ?_)
  · exact measurable_pi_iff.2 fun i => i.elim0
  · exact measurable_pi_iff.2 fun i => i.elim0

/-- The Loewner chart of the stopped piece, read from its record. -/
def recChart (r : RecData) : Chart := LocalExt.histChart (recHist r)

theorem isConformal_recChart (r : RecData) : (recChart r).IsConformal :=
  LocalExt.isConformal_histChart (recHist r)

theorem continuousOn_recChart_lift (r : RecData) :
    ContinuousOn (fun w => (recChart r).2.2 ((recChart r).2.1 w)) QuantumZipper.H :=
  (isConformal_recChart r).continuousOn_lift_inv (LocalExt.continuousOn_lift_histChart (recHist r))

/-- The field `f` read in the record chart, with the flow coefficient `χ(κ)`. -/
def recField (κ : ℝ) (r : RecData) (f : DistOn upperHalfPlaneOpens) : DistOn upperHalfPlaneOpens :=
  Chart.chartTransport (isConformal_recChart r) 1 0 (QuantumZipper.chiC κ) f

theorem measurable_recField (κ : ℝ) :
    Measurable fun p : RecData × DistOn upperHalfPlaneOpens => recField κ p.1 p.2 := by
  have h := LocalExt.measurable_histChartField (nL := 0) (nR := 0) 1 0 (QuantumZipper.chiC κ)
  change Measurable ((fun q : DistOn upperHalfPlaneOpens × LocalExt.DrivingHist 0 0 =>
    Chart.chartTransport (LocalExt.isConformal_histChart q.2) 1 0 (QuantumZipper.chiC κ) q.1) ∘
      fun p : RecData × DistOn upperHalfPlaneOpens => (p.2, recHist p.1))
  exact h.comp (measurable_snd.prodMk (measurable_recHist.comp measurable_fst))

theorem isChartTransport_recField (κ : ℝ) (r : RecData) (f : DistOn upperHalfPlaneOpens) :
    IsChartTransport (recChart r) 1 0 (QuantumZipper.chiC κ) f (recField κ r f) :=
  Chart.isChartTransport_chartTransport (isConformal_recChart r)
    (Chart.locallyIntegrableOn_of_continuousOn (continuousOn_recChart_lift r)) 1 0 _ f

theorem toNNReal_ratCast_nnrat (q : ℚ≥0) : (((q : ℚ) : ℝ)).toNNReal = (q : ℝ≥0) := by
  ext
  rw [Real.coe_toNNReal _ (by positivity)]
  norm_cast

/-- **On a good record, the history driver is the stopped driver.** -/
theorem histDrv_recHist {t : ℝ≥0∞} {e : (ℝ≥0 → ℝ) × ℝ≥0∞} (he : IsRegularDriver e)
    (hg : LocalExt.IsDrvGood (recHist (recOf t e))) (s : ℝ≥0) :
    LocalExt.histDrv (recHist (recOf t e)) s = (retOf t e).1 s := by
  have h1 := LocalExt.tendsto_drvSample_histDrv hg s
  have hsamp : ∀ n, ((recHist (recOf t e)).2 (LocalExt.upDyad n s)).1 =
      (retOf t e).1 ((LocalExt.upDyad n s : ℚ≥0) : ℝ≥0) := fun n => by
    change (retOf t e).1 (((LocalExt.upDyad n s : ℚ≥0) : ℚ) : ℝ).toNNReal = _
    rw [toNNReal_ratCast_nnrat]
  simp only [hsamp] at h1
  refine tendsto_nhds_unique h1 ?_
  by_cases hs : (s : ℝ≥0∞) < min t e.2
  · -- before the stop: continuity of the driver at `s`
    have hcont : ContinuousAt (retOf t e).1 s := by
      have hU : IsOpen {x : ℝ≥0 | (x : ℝ≥0∞) < min t e.2} := isOpen_lt ENNReal.continuous_coe continuous_const
      have heq : EqOn (retOf t e).1 e.1 {x : ℝ≥0 | (x : ℝ≥0∞) < min t e.2} := fun x hx => by
        change e.1 (min (x : ℝ≥0∞) (min t e.2)).toNNReal = e.1 x
        rw [min_eq_left (le_of_lt hx), ENNReal.toNNReal_coe]
      have hc : ContinuousOn e.1 {x : ℝ≥0 | (x : ℝ≥0∞) < min t e.2} :=
        he.1.mono fun x (hx : (x : ℝ≥0∞) < min t e.2) => show (x : ℝ≥0∞) < e.2 from
          lt_of_lt_of_le hx (min_le_right _ _)
      exact ((hc.congr heq).continuousAt (hU.mem_nhds hs))
    exact hcont.tendsto.comp (LocalExt.tendsto_upDyad s)
  · -- at and after the stop the stopped driver is constant
    have hge : ∀ n, (retOf t e).1 ((LocalExt.upDyad n s : ℚ≥0) : ℝ≥0) = (retOf t e).1 s := fun n => by
      have h2 : min t e.2 ≤ (((LocalExt.upDyad n s : ℚ≥0) : ℝ≥0) : ℝ≥0∞) :=
        (not_lt.1 hs).trans (ENNReal.coe_le_coe.2 (LocalExt.le_upDyad n s))
      change e.1 (min _ (min t e.2)).toNNReal = e.1 (min _ (min t e.2)).toNNReal
      rw [min_eq_right h2, min_eq_right (not_lt.1 hs)]
    simp only [hge]
    exact tendsto_const_nhds

/-- **On a good record, the record chart is the frozen chart of the launch** (`ExplState.launch`: the chart
`Chart.id.loewner Wr T`, `Wr r = W_{r ∧ stop}`, `T = stop`). -/
theorem recChart_eq_loewner {t : ℝ≥0∞} {e : (ℝ≥0 → ℝ) × ℝ≥0∞} (he : IsRegularDriver e)
    (hg : LocalExt.IsDrvGood (recHist (recOf t e))) :
    recChart (recOf t e) =
      Chart.id.loewner (fun x : ℝ => (retOf t e).1 x.toNNReal) ((min t e.2).toNNReal : ℝ) := by
  have hdrv : (Ito.rpath (LocalExt.histDrv (recHist (recOf t e)))) = fun x : ℝ => (retOf t e).1 x.toNNReal := by
    funext x
    rw [Ito.rpath, histDrv_recHist he hg]
  unfold recChart LocalExt.histChart
  rw [hdrv]
  rfl

/-- On a good record the stopped driver is continuous. -/
theorem continuous_retOf {t : ℝ≥0∞} {e : (ℝ≥0 → ℝ) × ℝ≥0∞} (he : IsRegularDriver e)
    (hg : LocalExt.IsDrvGood (recHist (recOf t e))) : Continuous (retOf t e).1 := by
  have h := LocalExt.continuous_histDrv (recHist (recOf t e))
  have e' : LocalExt.histDrv (recHist (recOf t e)) = (retOf t e).1 := funext (histDrv_recHist he hg)
  rwa [e'] at h

end StagedLaw

end Exist

end InteractingSLE
