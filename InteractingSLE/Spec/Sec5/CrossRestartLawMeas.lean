/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec5.CrossRestartLawReduce
import Mathlib.MeasureTheory.Function.Floor
import Mathlib.MeasureTheory.Constructions.Polish.Basic

/-!
# Measurability of the explicit restart variable from its countable ingredients

Packet PROVE-SEC5-H, layer (iv). The explicit restart variable `CrossRestart.restartVar` is built from countably many
values of the chart path `restartPath` (at fixed times) and of the trace conditions `IsTraceGood` (at rational
times) by countable suprema and infima (`lawExit`, `lawLife`, `lawInv`), the grid capacity `hcapHit` of countable
images (`lawClock`), compositions with countably-valued times (`dyadicUp`) and limits (`limOr0`). Here:

* `measurable_limOr0`, `measurable_comp_of_countable_time`, `measurable_hcapHit_image_of_countable`: the three
  general tools;
* `measurableSet_isTraceGoodQ`: the countable trace condition is an event;
* **`measurable_encPath_lawPath`**: the restart variable is measurable as soon as the chart path and the two traces at
  every fixed time and the counterflow lifetime are;
* `RestartPathMeasurableStatement` (named, smaller than `RestartVarMeasurableStatement`) and
  **`restartVarMeasurableStatement_of_path`**, **`counterflowSegmentRestartStatement_of_kernel_of_path`**.
-/

set_option autoImplicit false

noncomputable section

open Complex Set Metric Filter Topology MeasureTheory ProbabilityTheory
open scoped Real NNReal ENNReal

open QuantumZipper (H)

universe u

namespace InteractingSLE

namespace Sec5

namespace CrossRestart

open ConformalImage ConformalImageFull Sec4 Restart MarkovOther Sec2.Assembly

section Tools

variable {Ω : Type*} [MeasurableSpace Ω]

/-- The limit-or-zero of a measurable sequence of complex random variables is measurable. -/
theorem measurable_limOr0 {f : ℕ → Ω → ℂ} (hf : ∀ n, Measurable (f n)) :
    Measurable fun ω => limOr0 fun n => f n ω := by
  set E := {ω | ∃ l, Tendsto (fun n => f n ω) atTop (𝓝 l)} with hE
  have hEm : MeasurableSet E := MeasureTheory.measurableSet_exists_tendsto hf
  refine measurable_of_restrict_of_restrict_compl hEm ?_ ?_
  · refine measurable_of_tendsto_metrizable' atTop (f := fun n (x : E) => f n x)
      (fun n => (hf n).comp measurable_subtype_coe) ?_
    rw [tendsto_pi_nhds]
    intro x
    obtain ⟨l, hl⟩ := x.2
    show Tendsto (fun n => f n x) atTop (𝓝 (limOr0 fun n => f n x))
    rw [limOr0_eq hl]
    exact hl
  · have h0 : (Eᶜ.domRestrict fun ω => limOr0 fun n => f n ω) = fun _ => 0 := by
      funext x
      simp only [Set.domRestrict_apply, limOr0]
      exact dite_eq_right_of_eq_false (eq_false x.2)
    rw [h0]
    exact measurable_const

/-- A random variable evaluated at a measurable random time with countable range is measurable. -/
theorem measurable_comp_of_countable_time {τ : Ω → ℝ≥0} (hc : (range τ).Countable) (hτ : Measurable τ)
    {f : Ω → ℝ≥0 → ℂ} (hf : ∀ t, Measurable fun ω => f ω t) : Measurable fun ω => f ω (τ ω) := by
  intro B hB
  have heq : (fun ω => f ω (τ ω)) ⁻¹' B = ⋃ c ∈ range τ, (τ ⁻¹' {c} ∩ (fun ω => f ω c) ⁻¹' B) := by
    ext ω
    simp only [mem_preimage, mem_iUnion, mem_inter_iff, mem_singleton_iff, mem_range, exists_prop]
    constructor
    · intro h
      exact ⟨τ ω, ⟨ω, rfl⟩, rfl, h⟩
    · rintro ⟨c, -, hc, h⟩
      rw [hc]
      exact h
  rw [heq]
  exact MeasurableSet.biUnion hc fun c _ => (hτ (measurableSet_singleton c)).inter (hf c hB)

/-- The grid capacity of the image of a countable set under a random path measurable at each time is measurable. -/
theorem measurable_hcapHit_image_of_countable {D : Set ℝ≥0} (hD : D.Countable) {f : Ω → ℝ≥0 → ℂ}
    (hf : ∀ t, Measurable fun ω => f ω t) : Measurable fun ω => WholeField.hcapHit (f ω '' D) := by
  classical
  unfold WholeField.hcapHit
  refine Measurable.iInf fun n => Measurable.iInf fun s => Measurable.ite ?_ measurable_const measurable_const
  have hO : MeasurableSet (H \ WholeField.gridUnion n s) :=
    (QuantumZipper.isOpen_H.sdiff (WholeField.isClosed_gridUnion n s)).measurableSet
  have heq : {ω | Disjoint (f ω '' D) (H \ WholeField.gridUnion n s)} =
      ⋂ t ∈ D, (fun ω => f ω t) ⁻¹' (H \ WholeField.gridUnion n s)ᶜ := by
    ext ω
    simp only [mem_ofPred_eq, mem_iInter, mem_preimage, mem_compl_iff, Set.disjoint_left,
      forall_mem_image]
  rw [heq]
  exact MeasurableSet.biInter hD fun t _ => hf t hO.compl

omit [MeasurableSpace Ω] in
theorem countable_range_dyadicUp (n : ℕ) {τ : Ω → ℝ≥0} : (range fun ω => dyadicUp n (τ ω)).Countable := by
  refine (countable_range fun k : ℕ => (k : ℝ≥0) / 2 ^ n).mono ?_
  rintro _ ⟨ω, rfl⟩
  exact ⟨_, rfl⟩

theorem measurable_dyadicUp (n : ℕ) : Measurable (dyadicUp n) := by
  unfold dyadicUp
  refine Measurable.div_const ?_ _
  exact measurable_from_nat.comp (Nat.measurable_ceil.comp (measurable_coe_nnreal_real.mul_const _))

theorem measurableSet_imp_const {p : Prop} {S : Set Ω} (hS : MeasurableSet S) :
    MeasurableSet {ω | p → ω ∈ S} := by
  by_cases hp : p
  · simpa [hp] using hS
  · simp [hp]

theorem measurableSet_forall_ratGrid (t : ℝ≥0) {P : ℝ≥0 → Ω → Prop} (hP : ∀ x, MeasurableSet {ω | P x ω}) :
    MeasurableSet {ω | ∀ x ∈ ratGrid t, P x ω} := by
  have heq : {ω | ∀ x ∈ ratGrid t, P x ω} = ⋂ r : ℚ, {ω | P ((r : ℝ).toNNReal ⊓ t) ω} := by
    ext ω
    simp only [mem_ofPred_eq, mem_iInter, ratGrid, forall_mem_range]
  rw [heq]
  exact MeasurableSet.iInter fun r => hP _

theorem measurable_mob (q : ℝ) : Measurable (QuantumZipper.CA.realMobius 0 (-(1 + q)) 1 1) := by
  unfold QuantumZipper.CA.realMobius
  exact ((measurable_const.mul measurable_id).add measurable_const).div
    ((measurable_const.mul measurable_id).add measurable_const)

/-- **The countable trace condition is a measurable event** for paths measurable at each time and a measurable
lifetime. -/
theorem measurableSet_isTraceGoodQ {q : ℝ} {s : ℝ≥0} {η γ : Ω → ℝ≥0 → ℂ} {ζ' : Ω → ℝ≥0∞}
    (hηm : ∀ t, Measurable fun ω => η ω t) (hγm : ∀ t, Measurable fun ω => γ ω t) (hζm : Measurable ζ')
    (r : ℝ≥0) : MeasurableSet {ω | IsTraceGoodQ q (η ω) s (ζ' ω) (γ ω) r} := by
  have h1 : MeasurableSet {ω | (r : ℝ≥0∞) < ζ' ω} := measurableSet_lt measurable_const hζm
  have h2 : MeasurableSet {ω | γ ω 0 = 0} := measurableSet_eq_fun (hγm 0) measurable_const
  have h3 : MeasurableSet {ω | ∀ k : ℕ, ∃ m : ℕ, ∀ t ∈ ratGrid r, 0 < t → (r : ℝ) / ((k : ℝ) + 1) ≤ t →
      1 / ((m : ℝ) + 1) ≤ (γ ω t).im} := by
    have heq : {ω | ∀ k : ℕ, ∃ m : ℕ, ∀ t ∈ ratGrid r, 0 < t → (r : ℝ) / ((k : ℝ) + 1) ≤ t →
        1 / ((m : ℝ) + 1) ≤ (γ ω t).im} = ⋂ k : ℕ, ⋃ m : ℕ, {ω | ∀ t ∈ ratGrid r, 0 < t →
          (r : ℝ) / ((k : ℝ) + 1) ≤ t → 1 / ((m : ℝ) + 1) ≤ (γ ω t).im} := by
      ext ω
      simp only [mem_ofPred_eq, mem_iInter, mem_iUnion]
    rw [heq]
    refine MeasurableSet.iInter fun k => MeasurableSet.iUnion fun m => measurableSet_forall_ratGrid r fun t => ?_
    exact measurableSet_imp_const (measurableSet_imp_const
      (measurableSet_le measurable_const (Complex.measurable_im.comp (hγm t))))
  have h4 : MeasurableSet {ω | ∃ m : ℕ, ∀ a ∈ ratGrid s, ∀ b ∈ ratGrid r,
      1 / ((m : ℝ) + 1) ≤ ‖η ω a - QuantumZipper.CA.realMobius 0 (-(1 + q)) 1 1 (γ ω b)‖} := by
    have heq : {ω | ∃ m : ℕ, ∀ a ∈ ratGrid s, ∀ b ∈ ratGrid r,
        1 / ((m : ℝ) + 1) ≤ ‖η ω a - QuantumZipper.CA.realMobius 0 (-(1 + q)) 1 1 (γ ω b)‖} =
        ⋃ m : ℕ, {ω | ∀ a ∈ ratGrid s, ∀ b ∈ ratGrid r,
          1 / ((m : ℝ) + 1) ≤ ‖η ω a - QuantumZipper.CA.realMobius 0 (-(1 + q)) 1 1 (γ ω b)‖} := by
      ext ω
      simp only [mem_ofPred_eq, mem_iUnion]
    rw [heq]
    refine MeasurableSet.iUnion fun m => measurableSet_forall_ratGrid s fun a =>
      measurableSet_forall_ratGrid r fun b => ?_
    exact measurableSet_le measurable_const ((hηm a).sub ((measurable_mob q).comp (hγm b))).norm
  have heq : {ω | IsTraceGoodQ q (η ω) s (ζ' ω) (γ ω) r} = {ω | (r : ℝ≥0∞) < ζ' ω} ∩ ({ω | γ ω 0 = 0} ∩
      ({ω | ∀ k : ℕ, ∃ m : ℕ, ∀ t ∈ ratGrid r, 0 < t → (r : ℝ) / ((k : ℝ) + 1) ≤ t →
        1 / ((m : ℝ) + 1) ≤ (γ ω t).im} ∩ {ω | ∃ m : ℕ, ∀ a ∈ ratGrid s, ∀ b ∈ ratGrid r,
          1 / ((m : ℝ) + 1) ≤ ‖η ω a - QuantumZipper.CA.realMobius 0 (-(1 + q)) 1 1 (γ ω b)‖})) := by
    ext ω
    rfl
  rw [heq]
  exact h1.inter (h2.inter (h3.inter h4))

end Tools

/-! ### The explicit restart variable is measurable from its countable ingredients -/

section Var

variable {Ω : Type*} [MeasurableSpace Ω] {q : ℝ} {U : Ω → ℝ → ℝ} {σ : ℝ} {x₁ : Ω → ℝ}
  {η : Ω → ℝ≥0 → ℂ} {s : ℝ≥0} {ζ' : Ω → ℝ≥0∞} {γ : Ω → ℝ≥0 → ℂ}
  (hpath : ∀ t, Measurable fun ω => restartPath q (U ω) σ (x₁ ω) (γ ω) t)
  (hηm : ∀ t, Measurable fun ω => η ω t) (hγm : ∀ t, Measurable fun ω => γ ω t) (hζm : Measurable ζ')

include hpath in
theorem measurable_lawClock (t : ℝ≥0) : Measurable fun ω => lawClock q (U ω) σ (x₁ ω) (γ ω) t :=
  ((measurable_hcapHit_image_of_countable (countable_ratGrid t) hpath).ennreal_toReal).div_const 2

include hηm hγm hζm in
theorem measurable_lawExit : Measurable fun ω => lawExit q (η ω) s (ζ' ω) (γ ω) := by
  classical
  have heq : (fun ω => lawExit q (η ω) s (ζ' ω) (γ ω)) = fun ω =>
      ⨆ r : ℚ, if IsTraceGoodQ q (η ω) s (ζ' ω) (γ ω) (qnn r) then (qnn r : ℝ≥0∞) else ⊥ := by
    funext ω
    simp only [lawExit, iSup_eq_if]
  rw [heq]
  exact Measurable.iSup fun r => Measurable.ite (measurableSet_isTraceGoodQ hηm hγm hζm _) measurable_const
    measurable_const

include hpath hηm hγm hζm in
theorem measurable_lawLife : Measurable fun ω => lawLife q (U ω) σ (x₁ ω) (η ω) s (ζ' ω) (γ ω) := by
  classical
  have heq : (fun ω => lawLife q (U ω) σ (x₁ ω) (η ω) s (ζ' ω) (γ ω)) = fun ω =>
      ⨆ r : ℚ, if (qnn r : ℝ≥0∞) < lawExit q (η ω) s (ζ' ω) (γ ω) then
        ENNReal.ofReal (lawClock q (U ω) σ (x₁ ω) (γ ω) (qnn r)) else ⊥ := by
    funext ω
    simp only [lawLife, iSup_eq_if]
  rw [heq]
  exact Measurable.iSup fun r => Measurable.ite (measurableSet_lt measurable_const (measurable_lawExit hηm hγm hζm))
    (ENNReal.measurable_ofReal.comp (measurable_lawClock hpath _)) measurable_const

include hpath hηm hγm hζm in
theorem measurable_lawInv (u : ℝ≥0) :
    Measurable fun ω => lawInv q (U ω) σ (x₁ ω) (η ω) s (ζ' ω) (γ ω) u := by
  classical
  have heq : (fun ω => lawInv q (U ω) σ (x₁ ω) (η ω) s (ζ' ω) (γ ω) u) = fun ω =>
      ⨅ r : ℚ, if (qnn r : ℝ≥0∞) < lawExit q (η ω) s (ζ' ω) (γ ω) ∧
          (u : ℝ) ≤ lawClock q (U ω) σ (x₁ ω) (γ ω) (qnn r) then (qnn r : ℝ≥0∞) else ⊤ := by
    funext ω
    simp only [lawInv, iInf_eq_if]
  rw [heq]
  exact Measurable.iInf fun r => Measurable.ite
    ((measurableSet_lt measurable_const (measurable_lawExit hηm hγm hζm)).inter
      (measurableSet_le measurable_const (measurable_lawClock hpath _))) measurable_const measurable_const

include hpath hηm hγm hζm in
theorem measurable_lawPath (u : ℝ≥0) :
    Measurable fun ω => lawPath q (U ω) σ (x₁ ω) (η ω) s (ζ' ω) (γ ω) u := by
  refine measurable_limOr0 fun n => ?_
  exact measurable_comp_of_countable_time (countable_range_dyadicUp n)
    ((measurable_dyadicUp n).comp (ENNReal.measurable_toNNReal.comp (measurable_lawInv hpath hηm hγm hζm u))) hpath

include hpath hηm hγm hζm in
/-- **The explicit restart variable is measurable** as soon as the chart path at every fixed time, the two traces at
every fixed time and the counterflow lifetime are. -/
theorem measurable_encPath_lawPath :
    Measurable fun ω => encPath (lawPath q (U ω) σ (x₁ ω) (η ω) s (ζ' ω) (γ ω))
      (lawLife q (U ω) σ (x₁ ω) (η ω) s (ζ' ω) (γ ω)) :=
  measurable_encPath (fun t => measurable_lawPath hpath hηm hγm hζm t)
    (measurable_lawLife hpath hηm hγm hζm)

end Var

/-- **The countable ingredients of the explicit restart variable are measurable** (the remaining measurable-construction
part of layer (iv)). Setting and binders of `Sec5.CounterflowSegmentRestartStatement`: for every time `σ` there are
versions `w` of the flow-line driver, `η₀`, `γ₀` of the two traces and `ζ₀` of the counterflow lifetime such that the
two traces are measurable at every fixed time, the lifetime is measurable, and the chart path
`restartPath q U σ x₁ γ₀` (segment driver `U = segDrive w ζ σ`, `x₁ = segStart q w ζ σ`) is measurable at every fixed
time. -/
def RestartPathMeasurableStatement : Prop :=
  ∀ κ : ℝ, 0 < κ → κ < 4 → ∀ α x₀ a b a' b' θ : ℝ, IsFig51Bounds κ a b a' b' →
    -(π / 2) ≤ θ → θ ≤ π / 2 →
    ∀ {Ω : Type u} [MeasurableSpace Ω] [StandardBorelSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
      (h : Ω → LQGMetric.DistOn upperHalfPlaneOpens) (hhm : Measurable h),
      IsFig51Field κ α x₀ a b a' b' P h →
    ∀ (η : Ω → ℝ≥0 → ℂ) (ζ : Ω → ℝ≥0∞),
      IsStripFlowLineAt κ α θ (fig51LowerFrame κ α a b) (fig51UpperFrame κ α x₀ a' b') {0} {x₀} P h η ζ →
    ∀ (W' : ℝ≥0 → Ω → ℝ) (ζ' : Ω → ℝ≥0∞) (γ' : Ω → ℝ≥0 → ℂ),
      IsStripCounterflowDriver κ α (Real.exp (π * x₀)) P h W' ζ' →
      (∀ᵐ ω ∂P, IsGeneratingTrace (fun t => W' t ω) (ζ' ω) (γ' ω)) →
      CondIndep (MeasurableSpace.comap h inferInstance)
        (⨆ t : ℝ≥0, MeasurableSpace.comap (fun ω => η ω t) inferInstance)
        (⨆ t : ℝ≥0, MeasurableSpace.comap (W' t) inferInstance) hhm.comap_le P →
    ∀ σ : ℝ≥0, ∃ (w : ℝ≥0 → Ω → ℝ) (η₀ γ₀ : Ω → ℝ≥0 → ℂ) (ζ₀ : Ω → ℝ≥0∞),
      (∀ᵐ ω ∂P, IsGeneratingTrace (fun t => w t ω) (ζ ω) (η ω) ∧
        ContinuousOn (fun t => w t ω) {t | (t : ℝ≥0∞) < ζ ω} ∧ w 0 ω = 0 ∧ η₀ ω = η ω ∧ γ₀ ω = γ' ω ∧
        ζ₀ ω = ζ' ω) ∧
      (∀ t : ℝ≥0, Measurable fun ω => η₀ ω t) ∧ (∀ t : ℝ≥0, Measurable fun ω => γ₀ ω t) ∧ Measurable ζ₀ ∧
      ∀ t : ℝ≥0, Measurable fun ω => restartPath (Real.exp (π * x₀)) (segDrive (fun t => w t ω) (ζ ω) σ) σ
        (segStart (Real.exp (π * x₀)) (fun t => w t ω) (ζ ω) σ) (γ₀ ω) t

/-- The measurability of the explicit restart variable from that of its countable ingredients. -/
theorem restartVarMeasurableStatement_of_path (hP : RestartPathMeasurableStatement.{u}) :
    RestartVarMeasurableStatement.{u} := by
  intro κ hκ hκ4 α x₀ a b a' b' θ hbd hθ₁ hθ₂ Ω _ _ P _ h hhm hh η ζ hη W' ζ' γ' hcf htr' hci σ
  obtain ⟨w, η₀, γ₀, ζ₀, hver, hηm, hγm, hζm, hpath⟩ :=
    hP κ hκ hκ4 α x₀ a b a' b' θ hbd hθ₁ hθ₂ P h hhm hh η ζ hη W' ζ' γ' hcf htr' hci σ
  exact ⟨w, η₀, γ₀, ζ₀, hver, measurable_encPath_lawPath hpath hηm hγm hζm⟩

/-- **SEC5-E's counterflow restart carrier** from Zhan's Part A inputs at `16/κ`, the law of the explicit restart
variable and the measurability of its countable ingredients. -/
theorem counterflowSegmentRestartStatement_of_kernel_of_path (hA : PartAInputsSixteenDiv)
    (hK : CounterflowRestartKernelStatement.{u}) (hP : RestartPathMeasurableStatement.{u}) :
    CounterflowSegmentRestartStatement.{u} :=
  counterflowSegmentRestartStatement_of_kernel hA hK (restartVarMeasurableStatement_of_path hP)

end CrossRestart

end Sec5

end InteractingSLE
