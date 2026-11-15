/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.LPTrace

/-!
# Lemma LP1: gluing stopped traces along an exhausting sequence of times

Packet PROVE-R17. Supplement §6.1, Lemma LP1 (`source/spec/p433-480.md` L1086–L1121, pp. 478–479), last
step: "Take `R = 2^n`. These times increase to infinity, pathwise, because the integrated single-seed
driver is continuous and nonexplosive on finite intervals. The trace tips obtained from the same
driver agree on overlaps, so the countable union of these closed stopped traces is continuous on every
finite interval."

* `isGeneratingTrace_mono`: a generating trace on `[0, T]` generates on `[0, T']` for `T' ≤ T`.
* `exists_isGeneratingTrace_top_of_forall_lt`: for a continuous driver with `w 0 = 0`, if every time
  `t` lies before some `T_n` for which a generating trace on `[0, T_n]` exists, the traces glue to one
  generating trace on `[0, ∞]` (agreement on overlaps is PROVE-LP's `IsGeneratingTrace.eq_of_le`).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology
open scoped NNReal ENNReal

namespace InteractingSLE.LP

/-- Restriction of a generating trace to a shorter interval. -/
theorem isGeneratingTrace_mono {w : ℝ≥0 → ℝ} {T T' : ℝ≥0∞} {η : ℝ≥0 → ℂ}
    (h : IsGeneratingTrace w T η) (hT : T' ≤ T) : IsGeneratingTrace w T' η :=
  ⟨h.1, h.2.1.mono fun _ hs => le_trans hs hT, fun t ht => h.2.2 t (lt_of_lt_of_le ht hT)⟩

/-- **Gluing stopped traces** (LP1's last step): if `w` is continuous with `w 0 = 0` and every time
lies strictly before some `T n` for which `w` has a generating trace on `[0, T n]`, then `w` has a
generating trace on `[0, ∞]`. -/
theorem exists_isGeneratingTrace_top_of_forall_lt {w : ℝ≥0 → ℝ} (hw : Continuous w) (hw0 : w 0 = 0)
    (T : ℕ → ℝ≥0∞) (hT : ∀ t : ℝ≥0, ∃ n, (t : ℝ≥0∞) < T n)
    (hη : ∀ n, ∃ η : ℝ≥0 → ℂ, IsGeneratingTrace w (T n) η) :
    ∃ η : ℝ≥0 → ℂ, IsGeneratingTrace w ⊤ η := by
  classical
  choose η hη using hη
  let N : ℝ≥0 → ℕ := fun t : ℝ≥0 => Nat.find (hT t)
  have hN : ∀ t : ℝ≥0, (t : ℝ≥0∞) < T (N t) := fun t => Nat.find_spec (hT t)
  -- the glued trace agrees with `η m` on `[0, T m]`
  have hagree : ∀ m (s : ℝ≥0), (s : ℝ≥0∞) ≤ T m → η (N s) s = η m s := by
    intro m s hs
    have hmin : (s : ℝ≥0∞) ≤ min (T (N s)) (T m) := le_min (hN s).le hs
    exact (isGeneratingTrace_mono (hη (N s)) (min_le_left _ _)).eq_of_le
      (isGeneratingTrace_mono (hη m) (min_le_right _ _)) hw.continuousOn hw0 hmin
  refine ⟨fun t => η (N t) t, ?_, ?_, fun t _ => ?_⟩
  · show η (N 0) 0 = 0
    exact (hη _).1
  · intro t _
    have hev : (fun s => η (N s) s) =ᶠ[𝓝 t] η (N t) := by
      have hopen : IsOpen {s : ℝ≥0 | (s : ℝ≥0∞) < T (N t)} :=
        isOpen_lt ENNReal.continuous_coe continuous_const
      filter_upwards [hopen.mem_nhds (hN t)] with s hs
      exact hagree (N t) s (le_of_lt hs)
    have hc : ContinuousAt (η (N t)) t :=
      ((hη (N t)).2.1.mono fun s (hs : (s : ℝ≥0∞) < T (N t)) => hs.le).continuousAt
        ((isOpen_lt ENNReal.continuous_coe continuous_const).mem_nhds (hN t))
    exact (hc.congr hev.symm).continuousWithinAt
  · have himg : (fun s => η (N s) s) '' Icc 0 t = η (N t) '' Icc 0 t := by
      refine image_congr fun s hs => hagree (N t) s (le_trans ?_ (hN t).le)
      exact ENNReal.coe_le_coe.2 hs.2
    rw [himg]
    exact (hη (N t)).2.2 t (hN t)

end InteractingSLE.LP
