/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GB6TraceKernel
import InteractingSLE.Spec.Sec2.Assembly2Life

/-!
# A measurable continuous trace of a measurable driver, and one-sided tail gaps

Packet PROVE-BW1-INPUTS (the endpoint, its kernel half). For a process `W` whose paths are only almost surely
continuous, the event "the path has a transient generating trace avoiding a closed tail" must be made measurable
before it can be passed from the regular conditional laws back to `P`. As GB6's canonical space does (`gb6Γ`), we
regularize:

* `regPath w`: the continuous path decoded from the dyadic values of `w` (`drvDecTop (enc w, ⊤)`; it is `w` itself
  when `w` is continuous), measurable in the sample;
* `TraceGood w`: the regularized path starts at `0` and has a continuous transient generating trace (a Borel event,
  `RandRestart.traceSet`);
* `regTrace w`: that trace on `TraceGood w`, `0` otherwise — continuous for **every** path, measurable in the sample;
* `rightGap j z`, `leftGap j z`: positive iff `z` is not in the closed real tail `[j, ∞)`, resp. `(−∞, j]`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Filter Set Topology
open scoped NNReal ENNReal

namespace InteractingSLE.Theorem14.BW1In

open Supp8.GB6 Sec2.Assembly Sec7.RandRestart

/-! ### The regularized path -/

/-- The continuous regularization of a path through its dyadic values. -/
def regPath (w : ℝ≥0 → ℝ) : ℝ≥0 → ℝ := drvDecTop (enc w, ⊤)

theorem continuous_regPath (w : ℝ≥0 → ℝ) : Continuous (regPath w) := continuous_drvDecTop _

/-- A continuous path is its own regularization. -/
theorem regPath_eq {w : ℝ≥0 → ℝ} (hw : Continuous w) : regPath w = w := by
  funext s
  rw [regPath, drvDecTop_of_uc (Sec2.Assembly2.uc_enc_of_continuous hw)]
  exact congrFun (Sec2.Assembly2.dec_enc_of_continuous hw) s

theorem measurable_enc_path {Ω : Type*} [MeasurableSpace Ω] {W : ℝ≥0 → Ω → ℝ} (hW : ∀ s, Measurable (W s)) :
    Measurable fun ω => enc fun s => W s ω :=
  measurable_pi_iff.2 fun n => measurable_pi_iff.2 fun k => hW (dyad n k)

theorem measurable_regPath {Ω : Type*} [MeasurableSpace Ω] {W : ℝ≥0 → Ω → ℝ} (hW : ∀ s, Measurable (W s))
    (s : ℝ≥0) : Measurable fun ω => regPath (fun u => W u ω) s :=
  (measurable_drvDecTop s).comp ((measurable_enc_path hW).prodMk measurable_const)

theorem measurable_regPath_path {Ω : Type*} [MeasurableSpace Ω] {W : ℝ≥0 → Ω → ℝ}
    (hW : ∀ s, Measurable (W s)) : Measurable fun ω => regPath fun u => W u ω :=
  measurable_pi_iff.2 (measurable_regPath hW)

/-! ### The regularized trace -/

/-- The regularized path starts at `0` and has a continuous transient generating trace on `[0, ∞)`. -/
def TraceGood (w : ℝ≥0 → ℝ) : Prop := (regPath w, (⊤ : ℝ≥0∞)) ∈ traceSet ∧ regPath w 0 = 0

/-- **The regularized trace**: the reconstructed trace of the regularized path on `TraceGood`, `0` otherwise. -/
def regTrace (w : ℝ≥0 → ℝ) : ℝ≥0 → ℂ :=
  open Classical in if TraceGood w then (LP.drivingTrace ((⊤ : ℝ≥0∞), regPath w)).2 else fun _ => 0

theorem measurableSet_traceGood {Ω : Type*} [MeasurableSpace Ω] {W : ℝ≥0 → Ω → ℝ} (hW : ∀ s, Measurable (W s)) :
    MeasurableSet {ω | TraceGood fun u => W u ω} := by
  refine (measurableSet_traceSet.preimage ((measurable_regPath_path hW).prodMk measurable_const)).inter ?_
  exact measurableSet_eq_fun (measurable_regPath hW 0) measurable_const

theorem measurable_regTrace {Ω : Type*} [MeasurableSpace Ω] {W : ℝ≥0 → Ω → ℝ} (hW : ∀ s, Measurable (W s))
    (t : ℝ≥0) : Measurable fun ω => regTrace (fun u => W u ω) t := by
  classical
  have h : Measurable fun ω => (LP.drivingTrace ((⊤ : ℝ≥0∞), regPath fun u => W u ω)).2 t :=
    (measurable_pi_apply t).comp (measurable_snd.comp (LP.measurable_drivingTrace.comp
      (measurable_const.prodMk (measurable_regPath_path hW))))
  have e : (fun ω => regTrace (fun u => W u ω) t) = fun ω => if TraceGood (fun u => W u ω) then
      (LP.drivingTrace ((⊤ : ℝ≥0∞), regPath fun u => W u ω)).2 t else 0 := by
    funext ω
    unfold regTrace
    by_cases hω : TraceGood fun u => W u ω <;> simp [hω]
  rw [e]
  exact Measurable.ite (measurableSet_traceGood hW) h measurable_const

/-- On `TraceGood`, the regularized trace is a continuous transient generating trace of the regularized path. -/
theorem isGeneratingTrace_regTrace {w : ℝ≥0 → ℝ} (hw : TraceGood w) :
    IsGeneratingTrace (regPath w) ⊤ (regTrace w) ∧ Tendsto (fun t => ‖regTrace w t‖) atTop atTop := by
  have hc := continuous_regPath w
  have hev : TraceEvent (regPath w) ⊤ :=
    (mem_traceSet_iff hc.continuousOn hw.2 fun _ h => absurd h (lt_irrefl _)).1 hw.1
  obtain ⟨η, hη, htr⟩ := hev
  have hd := LP.drivingTrace_eq hη hc.continuousOn hw.2 (fun _ _ => rfl)
  have hΓ : regTrace w = η := by
    rw [regTrace, ite_eq_left_of_eq_true _ _ (eq_true hw), hd]
    funext t
    simp
  rw [hΓ]
  exact ⟨hη, htr rfl⟩

theorem continuous_regTrace (w : ℝ≥0 → ℝ) : Continuous (regTrace w) := by
  classical
  by_cases hw : TraceGood w
  · have h := (isGeneratingTrace_regTrace hw).1.2.1
    simp only [le_top, ofPred_true] at h
    exact continuousOn_univ.1 h
  · rw [regTrace, ite_eq_right_of_eq_false _ _ (eq_false hw)]; exact continuous_const

/-- **A continuous path from `0` with a transient generating trace is `TraceGood`, and its regularized trace is that
trace.** -/
theorem traceGood_of {w : ℝ≥0 → ℝ} (hw : Continuous w) (hw0 : w 0 = 0) {η : ℝ≥0 → ℂ}
    (hη : IsGeneratingTrace w ⊤ η) (htr : Tendsto (fun t => ‖η t‖) atTop atTop) :
    TraceGood w ∧ regTrace w = η := by
  have hr := regPath_eq hw
  have hgood : TraceGood w := by
    refine ⟨?_, by rw [hr]; exact hw0⟩
    rw [hr, mem_traceSet_iff hw.continuousOn hw0 fun _ h => absurd h (lt_irrefl _)]
    exact ⟨η, hη, fun _ => htr⟩
  refine ⟨hgood, ?_⟩
  have hd := LP.drivingTrace_eq hη hw.continuousOn hw0 (w' := regPath w) (fun s _ => by rw [hr])
  rw [regTrace, ite_eq_left_of_eq_true _ _ (eq_true hgood), hd]
  funext t
  simp

/-! ### One-sided tail gaps -/

/-- `max |Im z| (j − Re z)`: positive iff `z` is not in the closed real tail `[j, ∞)`. -/
def rightGap (j : ℝ) (z : ℂ) : ℝ := max |z.im| (j - z.re)

/-- `max |Im z| (Re z − j)`: positive iff `z` is not in the closed real tail `(−∞, j]`. -/
def leftGap (j : ℝ) (z : ℂ) : ℝ := max |z.im| (z.re - j)

theorem rightGap_pos_iff {j : ℝ} {z : ℂ} : 0 < rightGap j z ↔ ¬ (z.im = 0 ∧ j ≤ z.re) := by
  unfold rightGap
  rw [lt_max_iff, abs_pos, sub_pos]
  constructor
  · rintro (h | h) ⟨hi, hr⟩
    · exact h hi
    · linarith
  · intro h
    by_cases hi : z.im = 0
    · exact Or.inr (not_le.1 fun hr => h ⟨hi, hr⟩)
    · exact Or.inl hi

theorem leftGap_pos_iff {j : ℝ} {z : ℂ} : 0 < leftGap j z ↔ ¬ (z.im = 0 ∧ z.re ≤ j) := by
  unfold leftGap
  rw [lt_max_iff, abs_pos, sub_pos]
  constructor
  · rintro (h | h) ⟨hi, hr⟩
    · exact h hi
    · linarith
  · intro h
    by_cases hi : z.im = 0
    · exact Or.inr (not_le.1 fun hr => h ⟨hi, hr⟩)
    · exact Or.inl hi

theorem continuous_rightGap (j : ℝ) : Continuous (rightGap j) := by unfold rightGap; fun_prop

theorem continuous_leftGap (j : ℝ) : Continuous (leftGap j) := by unfold leftGap; fun_prop

theorem measurable_rightGap : Measurable fun p : ℝ × ℂ => rightGap p.1 p.2 := by unfold rightGap; fun_prop

theorem measurable_leftGap : Measurable fun p : ℝ × ℂ => leftGap p.1 p.2 := by unfold leftGap; fun_prop

/-- **The regularized trace avoids a measurable closed right tail at every time: a measurable event.** -/
theorem measurableSet_rightAvoid {Ω : Type*} [MeasurableSpace Ω] {W : ℝ≥0 → Ω → ℝ} (hW : ∀ s, Measurable (W s))
    {j : Ω → ℝ} (hj : Measurable j) : MeasurableSet {ω | ∀ t, 0 < rightGap (j ω) (regTrace (fun u => W u ω) t)} :=
  measurableSet_forall_pos (g := fun ω t => rightGap (j ω) (regTrace (fun u => W u ω) t))
    (fun t => measurable_rightGap.comp (hj.prodMk (measurable_regTrace hW t)))
    fun _ => (continuous_rightGap _).comp (continuous_regTrace _)

/-- **The regularized trace avoids a measurable closed left tail at every time: a measurable event.** -/
theorem measurableSet_leftAvoid {Ω : Type*} [MeasurableSpace Ω] {W : ℝ≥0 → Ω → ℝ} (hW : ∀ s, Measurable (W s))
    {j : Ω → ℝ} (hj : Measurable j) : MeasurableSet {ω | ∀ t, 0 < leftGap (j ω) (regTrace (fun u => W u ω) t)} :=
  measurableSet_forall_pos (g := fun ω t => leftGap (j ω) (regTrace (fun u => W u ω) t))
    (fun t => measurable_leftGap.comp (hj.prodMk (measurable_regTrace hW t)))
    fun _ => (continuous_leftGap _).comp (continuous_regTrace _)

end InteractingSLE.Theorem14.BW1In
