import QuantumZipper.Proofs.Zipper.LogShiftW2Transport

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# LSW-ARCS (1): measure bookkeeping for the boundary pieces of one stage

Task LSW-ARCS. Deterministic facts about a finite measure `ν` on `ℝ` and a strictly increasing
position map `A` on `[0, T]` with `A T = 0`, when the measure of every piece `[A v, 0]` is known
(`f v`) and is the complement `LT − L v` of a continuous function `L`:

* `lswa_atom_left`: `ν` has no atom at `A w` (`w ∈ [0, T)`), since `ν [A w, A w') = L w' − L w`;
* `lswa_split_left`: `ν [A v, A w] + f w = f v` for `v ≤ w`;
* reflected versions for a strictly decreasing `B` with `B T = 0` and pieces `[0, B v]`
  (`lswa_atom_right`, `lswa_split_right`), through the image of `ν` under `x ↦ −x`.

Own elementary bookkeeping (additivity of measures, one limit).
-/

noncomputable section

open MeasureTheory Filter Set Topology
open scoped NNReal ENNReal

namespace QuantumZipper
namespace F1

section Left

variable {ν : Measure ℝ} {A : ℝ → ℝ} {T : ℝ} {f : ℝ → ℝ≥0∞}

theorem lswa_le_zero (hA : MonotoneOn A (Icc 0 T)) (hAT : A T = 0) {w : ℝ} (hw : w ∈ Icc 0 T) :
    A w ≤ 0 := by
  rw [← hAT]
  exact hA hw ⟨hw.1.trans hw.2, le_rfl⟩ hw.2

/-- `ν [A v, A w] + f w = f v` for `v ≤ w`, if `ν` has no atom at `A w`. -/
theorem lswa_split_left (hA : MonotoneOn A (Icc 0 T)) (hAT : A T = 0)
    (hf : ∀ v ∈ Icc 0 T, ν (Icc (A v) 0) = f v) {v w : ℝ} (hv : v ∈ Icc 0 T) (hw : w ∈ Icc 0 T)
    (hvw : v ≤ w) (hat : ν {A w} = 0) : ν (Icc (A v) (A w)) + f w = f v := by
  have h1 : A v ≤ A w := hA hv hw hvw
  have h2 : A w ≤ 0 := lswa_le_zero hA hAT hw
  have hd : Disjoint (Icc (A v) (A w)) (Ioc (A w) 0) :=
    Set.disjoint_left.2 fun x hx hx' => absurd hx.2 (not_le.2 hx'.1)
  have hI : ν (Ioc (A w) 0) = ν (Icc (A w) 0) := by
    rw [← Icc_sdiff_left]
    exact measure_sdiff_null hat
  rw [← hf v hv, ← hf w hw, ← hI, ← measure_union hd measurableSet_Ioc,
    Icc_union_Ioc_eq_Icc h1 h2]

/-- No atom at `A w`, `w ∈ [0, T)`. -/
theorem lswa_atom_left (hA : StrictMonoOn A (Icc 0 T)) (hAT : A T = 0)
    (hf : ∀ v ∈ Icc 0 T, ν (Icc (A v) 0) = f v) {L : ℝ → ℝ≥0∞} {LT : ℝ≥0∞}
    (hLf : ∀ v ∈ Icc 0 T, L v + f v = LT) (hLT : LT ≠ ⊤)
    (hLc : ContinuousOn (fun v => (L v).toReal) (Icc 0 T)) {w : ℝ} (hw : w ∈ Ico 0 T) :
    ν {A w} = 0 := by
  have hw' : w ∈ Icc 0 T := ⟨hw.1, hw.2.le⟩
  have hfin : ∀ v ∈ Icc 0 T, f v ≠ ⊤ ∧ L v ≠ ⊤ := fun v hv =>
    ⟨ne_top_of_le_ne_top hLT (by rw [← hLf v hv]; exact le_add_self),
      ne_top_of_le_ne_top hLT (by rw [← hLf v hv]; exact le_self_add)⟩
  -- the bound `ν {A w} ≤ L w' − L w`
  have hb : ∀ w' ∈ Ioc w T, (ν {A w}).toReal ≤ (L w').toReal - (L w).toReal ∧ ν {A w} ≠ ⊤ := by
    intro w' hw''
    have hw1 : w' ∈ Icc 0 T := ⟨hw.1.trans hw''.1.le, hw''.2⟩
    have h1 : A w < A w' := hA hw' hw1 hw''.1
    have h2 : A w' ≤ 0 := lswa_le_zero hA.monotoneOn hAT hw1
    have hd : Disjoint (Ico (A w) (A w')) (Icc (A w') 0) :=
      Set.disjoint_left.2 fun x hx hx' => absurd hx'.1 (not_le.2 hx.2)
    have hsp : ν (Ico (A w) (A w')) + f w' = f w := by
      rw [← hf w hw', ← hf w' hw1, ← measure_union hd measurableSet_Icc,
        Ico_union_Icc_eq_Icc h1.le h2]
    have hle : ν {A w} ≤ ν (Ico (A w) (A w')) :=
      measure_mono (singleton_subset_iff.2 ⟨le_rfl, h1⟩)
    have hle' : ν {A w} + f w' ≤ f w := by
      rw [← hsp]; exact add_le_add hle le_rfl
    have hne : ν {A w} ≠ ⊤ := ne_top_of_le_ne_top (hfin w hw').1 (le_trans le_self_add hle')
    refine ⟨?_, hne⟩
    have hr := (ENNReal.toReal_le_toReal (ENNReal.add_ne_top.2 ⟨hne, (hfin w' hw1).1⟩)
      (hfin w hw').1).2 hle'
    rw [ENNReal.toReal_add hne (hfin w' hw1).1] at hr
    have e1 := congrArg ENNReal.toReal (hLf w hw')
    have e2 := congrArg ENNReal.toReal (hLf w' hw1)
    rw [ENNReal.toReal_add (hfin w hw').2 (hfin w hw').1] at e1
    rw [ENNReal.toReal_add (hfin w' hw1).2 (hfin w' hw1).1] at e2
    linarith
  obtain ⟨-, hne⟩ := hb T ⟨hw.2, le_rfl⟩
  have hlim : Tendsto (fun w' => (L w').toReal - (L w).toReal) (𝓝[>] w) (𝓝 0) := by
    have hc : ContinuousWithinAt (fun v => (L v).toReal) (Ioi w) w :=
      (hLc w hw').mono_of_mem_nhdsWithin
        (mem_of_superset (Ioo_mem_nhdsGT hw.2) fun x hx => ⟨hw.1.trans hx.1.le, hx.2.le⟩)
    have := hc.tendsto.sub_const (L w).toReal
    rwa [sub_self] at this
  have hle0 : (ν {A w}).toReal ≤ 0 :=
    ge_of_tendsto hlim (mem_of_superset (Ioo_mem_nhdsGT hw.2) fun x hx =>
      (hb x ⟨hx.1, hx.2.le⟩).1)
  exact (ENNReal.toReal_eq_zero_iff _).1 (le_antisymm hle0 ENNReal.toReal_nonneg) |>.resolve_right
    hne

end Left

section Right

variable {ν : Measure ℝ} {B : ℝ → ℝ} {T : ℝ} {f : ℝ → ℝ≥0∞}

theorem lswa_map_neg_Icc (ν : Measure ℝ) (a b : ℝ) :
    ν.map (fun x : ℝ => -x) (Icc a b) = ν (Icc (-b) (-a)) := by
  rw [Measure.map_apply measurable_neg measurableSet_Icc]
  congr 1
  ext x
  simp only [mem_preimage, mem_Icc]
  constructor <;> intro h <;> constructor <;> linarith [h.1, h.2]

theorem lswa_neg_facts (hB : StrictAntiOn B (Icc 0 T)) (hBT : B T = 0)
    (hf : ∀ v ∈ Icc 0 T, ν (Icc 0 (B v)) = f v) :
    StrictMonoOn (fun v => -B v) (Icc 0 T) ∧ (fun v => -B v) T = 0 ∧
      ∀ v ∈ Icc 0 T, ν.map (fun x : ℝ => -x) (Icc ((fun v => -B v) v) 0) = f v := by
  refine ⟨fun x hx y hy hxy => neg_lt_neg (hB hx hy hxy), by simp [hBT], fun v hv => ?_⟩
  rw [lswa_map_neg_Icc]
  simpa using hf v hv

end Right

end F1
end QuantumZipper
