/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.WalkIntRunChronCarrier
import InteractingSLE.Spec.Supplement.WalkIntOrientHistory

/-!
# Own-time order of physical tips from committed GW1 piece data

Use PieceSimpleAt, rather than the in-flight WalkWords interfaces.
The continuous physical boundary extension and its injectivity identify
all tipAt witnesses. ArcHistory determines its increasing orientation.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Filter Topology
open scoped NNReal ENNReal
open QuantumZipper (H Hbar)

namespace InteractingSLE.Theorem14.WalkIntRunChron

open GW1WalkChain GW1Bookkeep WalkIntOrient

/-- A simple piece appended to a chronological history has precisely
increasing full-walk parameters in its own time, including finite stops. -/
theorem tipAt_clock_order_of_pieceSimpleAt {α : ℝ≥0 → ℂ}
    (hα : Supp9B.IsProperCurve α) {c : Chart} {W : ℝ≥0 → ℝ} {S : ℝ≥0∞}
    {A : Set ℂ} {q₀ q₁ : ℝ} (hP : PieceSimpleAt c W S A q₀ q₁)
    (hHist : ArcHistory (α 0) A (q₀ : ℂ)) (hA : A ⊆ range α)
    (hpc : c.tipSet (fun r => W (min (r : ℝ≥0∞) S).toNNReal) S ⊆ range α) :
    ∀ (s t : ℝ≥0) (z w : ℂ), (s : ℝ≥0∞) ≤ S → (t : ℝ≥0∞) ≤ S →
      c.tipAt (fun r => W (min (r : ℝ≥0∞) S).toNNReal) s z →
      c.tipAt (fun r => W (min (r : ℝ≥0∞) S).toNNReal) t w →
      (s < t ↔ curveTime α z < curveTime α w) := by
  obtain ⟨f, η, _, hf, _, _, hW0, hW, hη, _, hi, hStart, _, hmeet⟩ := hP
  have hηH (t : ℝ≥0) (ht : (t : ℝ≥0∞) ≤ S) : η t ∈ Hbar :=
    Sec7.IsGeneratingTrace.mem_Hbar hη
      (hW.mono fun _ ht => mem_ofPred.2 ht.le) hW0 ht
  have htip (t : ℝ≥0) (ht : (t : ℝ≥0∞) ≤ S) :
      c.tipAt (fun r => W (min (r : ℝ≥0∞) S).toNNReal) t (f (η t)) :=
    CounterflowRange.tendsto_tip_stopped_of_tendsto hη hW hW0 ht (hf _ (hηH t ht))
  have hset : c.tipSet (fun r => W (min (r : ℝ≥0∞) S).toNNReal) S =
      (fun t => f (η t)) '' {t : ℝ≥0 | (t : ℝ≥0∞) ≤ S} := by
    rw [CounterflowRange.tipSet_stopped_eq_of_tendsto hη hW hW0
      (fun t ht => hf _ (hηH t ht)), image_image]
  have hcont : ContinuousOn (fun t => f (η t)) {t : ℝ≥0 | (t : ℝ≥0∞) ≤ S} :=
    (GW1P.continuousOn_of_tendsto hf).comp hη.2.1 (fun _ ht => hηH _ ht)
  have hh : ArcHistory (α 0) A (f (η 0)) := by rw [hStart]; exact hHist
  obtain ⟨a, hcarrier, hend⟩ := arcHistory_endpoint_initial_segment hα hh hA
  have hmono : StrictMonoOn (fun t => curveTime α (f (η t)))
      {t : ℝ≥0 | (t : ℝ≥0∞) ≤ S} := by
    intro s hs t ht hst
    have hI : Icc (0 : ℝ≥0) t ⊆ {u : ℝ≥0 | (u : ℝ≥0∞) ≤ S} :=
      fun _ hu => (ENNReal.coe_le_coe.2 hu.2).trans ht
    have hinc := strictMonoOn_curveTime_of_initial_segment hα (show (0 : ℝ≥0) ≤ t from zero_le)
      (hcont.mono hI) (hi.mono hI) (fun z hz => hpc (by
        rw [hset]
        exact image_mono hI hz)) hend (fun u hu hmem => by
          have huA : f (η u) ∈ A := hcarrier ▸ hmem
          have huS : (u : ℝ≥0∞) ≤ S := hI hu
          have hsingle : f (η u) ∈ ({f (η 0)} : Set ℂ) := by
            rw [← hmeet]
            refine ⟨?_, huA⟩
            rw [hset]
            exact ⟨u, huS, rfl⟩
          exact hi huS (by simp) (mem_singleton_iff.1 hsingle))
    exact hinc ⟨zero_le, hst.le⟩ ⟨zero_le, le_rfl⟩ hst
  intro s t z w hs ht hz hw
  have hzs : f (η s) = z := Chart.tipAt_unique (htip s hs) hz
  have hwt : f (η t) = w := Chart.tipAt_unique (htip t ht) hw
  rw [← hzs, ← hwt]
  exact (hmono.lt_iff_lt hs ht).symm

end InteractingSLE.Theorem14.WalkIntRunChron
