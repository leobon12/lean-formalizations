/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GB6TraceWord
import InteractingSLE.Spec.Supplement.GB6Contact
import InteractingSLE.Spec.Sec7.ContinuityProb3Coding
import InteractingSLE.Spec.Sec7.SideHeightGeom
import InteractingSLE.Spec.Supplement.LPAssembly

/-!
# Proposition GB6: the restart space and the conditional counterflow under one conditional law ((f) and (e)'s tails)

Packet PROVE-GB6D. GB6's canonical space is `GB6Space = 𝒟'(ℍ) × (driver code) × ℝ × ℝ`: the chart field, the canonical
driver code of the conditional counterflow, and the two junctions. Its coordinates:

* `gb6Field`, `gb6Code`, `gb6JL`, `gb6JR`;
* `gb6WCl` (the code decoded before its lifetime `gb6L`) and **`gb6WC`** (decoded on `[0, ∞)`, continuous everywhere);
* **`gb6Γ`**: the trace of `gb6WC` reconstructed by PROVE-LP's measurable map `LP.drivingTrace` when a continuous
  transient generating trace on `[0, ∞)` exists (the measurable event `Sec7.RandRestart.traceSet`), `0` otherwise;
  it is continuous at every point and measurable at every time (`isGB6RestartCoordinates`).

**`gb6_kernel`** (one conditional law `Q`, word `c`): if the chart field is a GFF with an admissible word `c` and the
decoded code with its own lifetime drives the counterflow of the chart field at `16/κ` (the output of
PROVE-RESTARTKERNEL's general kernel), the code is good, and the junction coordinates bound the protected tails of
`c`, then

* **(f)** `IsGB6ConditionalCounterflow κ c Q gb6Field gb6WC gb6Γ`: infinite lifetime (admissibility), the driver on
  `[0, ∞)` (the canonical code again, `Restart.IsCanonicalDriverCode`), the complete transient trace (Theorem 1.3's
  inputs at
  `16/κ`, `CompleteSixteenDivStatement`);
* **(e), probabilistic half**: almost surely the trace never visits the closed tails `[jR, ∞)`, `(−∞, jL]` (GB5 at the
  junctions, `GB6TraceWord.lean`), and the other coordinates are good (`IsGB6KernelGood`), as measurable events
  (`measurableSet_isGB6KernelGood`) that can be integrated back to the original space.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped NNReal ENNReal
open QuantumZipper (H)

namespace InteractingSLE

namespace Supp8

namespace GB6

open Restart Sec2.Assembly LQGMetric Sec7.RandRestart

/-! ### Theorem 1.3's input at `16/κ` -/

/-- **Theorem 1.3 at `κ′ = 16/κ`** (the "complete finite-force theorem" of GB6's proof), in its landed form: every
ordered force word is complete (`LP.IsCompleteForceWord`) at `16/κ`, `0 < κ < 4`. Derived from the twelve open inputs
of the range `κ′ > 4` by `completeSixteenDivStatement_of_open`. -/
def CompleteSixteenDivStatement : Prop :=
  ∀ κ : ℝ, 0 < κ → κ < 4 → ∀ {nL nR : ℕ} (xL : Fin nL → ℝ) (xR : Fin nR → ℝ) (ρL : Fin nL → ℝ) (ρR : Fin nR → ℝ),
    IsOrderedForceWord xL xR → LP.IsCompleteForceWord.{0} (16 / κ) xL xR ρL ρR

/-! ### The space and its coordinates -/

/-- **GB6's canonical space**: chart field, canonical driver code, left and right junctions. -/
abbrev GB6Space : Type := DistOn upperHalfPlaneOpens × (PCode × ℝ≥0∞) × (ℝ × ℝ)

instance : Nonempty GB6Space := ⟨(0, (fun _ _ => 0, 0), (0, 0))⟩

/-- The chart field coordinate. -/
def gb6Field (x : GB6Space) : DistOn upperHalfPlaneOpens := x.1

/-- The driver code coordinate. -/
def gb6Code (x : GB6Space) : PCode × ℝ≥0∞ := x.2.1

/-- The left junction coordinate. -/
def gb6JL (x : GB6Space) : ℝ := x.2.2.1

/-- The right junction coordinate. -/
def gb6JR (x : GB6Space) : ℝ := x.2.2.2

/-- The code's lifetime. -/
def gb6L (x : GB6Space) : ℝ≥0∞ := x.2.1.2

/-- The driver decoded before the code's lifetime. -/
def gb6WCl (t : ℝ≥0) (x : GB6Space) : ℝ := drvDec x.2.1 t

/-- **The chart driver**: the code decoded on `[0, ∞)`. -/
def gb6WC (t : ℝ≥0) (x : GB6Space) : ℝ := drvDecTop x.2.1 t

/-- The event that the chart driver starts at `0` and has a continuous transient generating trace on `[0, ∞)`. -/
def gb6TraceGood (x : GB6Space) : Prop := ((fun t => gb6WC t x), (⊤ : ℝ≥0∞)) ∈ traceSet ∧ gb6WC 0 x = 0

/-- **The chart path**: the reconstructed trace of the chart driver on `gb6TraceGood`, `0` otherwise. -/
def gb6Γ (x : GB6Space) : ℝ≥0 → ℂ :=
  open Classical in if gb6TraceGood x then (LP.drivingTrace ((⊤ : ℝ≥0∞), fun t => gb6WC t x)).2 else fun _ => 0

theorem measurable_gb6Field : Measurable gb6Field := measurable_fst

theorem measurable_gb6Code : Measurable gb6Code := measurable_fst.comp measurable_snd

theorem measurable_gb6JL : Measurable gb6JL := measurable_fst.comp (measurable_snd.comp measurable_snd)

theorem measurable_gb6JR : Measurable gb6JR := measurable_snd.comp (measurable_snd.comp measurable_snd)

theorem measurable_gb6L : Measurable gb6L := measurable_snd.comp measurable_gb6Code

theorem measurable_gb6WCl (t : ℝ≥0) : Measurable (gb6WCl t) := (measurable_drvDec t).comp measurable_gb6Code

theorem measurable_gb6WC (t : ℝ≥0) : Measurable (gb6WC t) := (measurable_drvDecTop t).comp measurable_gb6Code

theorem measurable_gb6WC_path : Measurable fun x : GB6Space => fun t => gb6WC t x :=
  measurable_pi_iff.2 measurable_gb6WC

theorem measurableSet_gb6TraceGood : MeasurableSet {x : GB6Space | gb6TraceGood x} := by
  refine (measurableSet_traceSet.preimage (measurable_gb6WC_path.prodMk measurable_const)).inter ?_
  exact measurableSet_eq_fun (measurable_gb6WC 0) measurable_const

theorem measurable_gb6Γ (t : ℝ≥0) : Measurable fun x => gb6Γ x t := by
  classical
  unfold gb6Γ
  have h : Measurable fun x : GB6Space => (LP.drivingTrace ((⊤ : ℝ≥0∞), fun t => gb6WC t x)).2 t :=
    (measurable_pi_apply t).comp (measurable_snd.comp (LP.measurable_drivingTrace.comp
      (measurable_const.prodMk measurable_gb6WC_path)))
  have e : (fun x : GB6Space => (if gb6TraceGood x then (LP.drivingTrace ((⊤ : ℝ≥0∞), fun t => gb6WC t x)).2
      else fun _ => (0 : ℂ)) t) = fun x => if gb6TraceGood x then
        (LP.drivingTrace ((⊤ : ℝ≥0∞), fun t => gb6WC t x)).2 t else 0 := by
    funext x
    by_cases hx : gb6TraceGood x <;> simp [hx]
  rw [e]
  exact Measurable.ite measurableSet_gb6TraceGood h measurable_const

theorem continuous_gb6WC (x : GB6Space) : Continuous fun t => gb6WC t x := continuous_drvDecTop _

theorem continuousOn_gb6WCl (x : GB6Space) : ContinuousOn (fun t => gb6WCl t x) {t | (t : ℝ≥0∞) < gb6L x} :=
  continuousOn_drvDec _

/-- On `gb6TraceGood`, the chart path is a continuous transient generating trace of the chart driver on `[0, ∞)`. -/
theorem isGeneratingTrace_gb6Γ {x : GB6Space} (hx : gb6TraceGood x) :
    IsGeneratingTrace (fun t => gb6WC t x) ⊤ (gb6Γ x) ∧ Tendsto (fun t => ‖gb6Γ x t‖) atTop atTop := by
  have hc := continuous_gb6WC x
  have hev : TraceEvent (fun t => gb6WC t x) ⊤ :=
    (mem_traceSet_iff hc.continuousOn hx.2 fun _ h => absurd h (lt_irrefl _)).1 hx.1
  obtain ⟨η, hη, htr⟩ := hev
  have hd := LP.drivingTrace_eq hη hc.continuousOn hx.2 (fun _ _ => rfl)
  have hΓ : gb6Γ x = η := by
    rw [gb6Γ, ite_eq_left_of_eq_true _ _ (eq_true hx), hd]
    funext t
    simp
  rw [hΓ]
  exact ⟨hη, htr rfl⟩

theorem continuous_gb6Γ (x : GB6Space) : Continuous (gb6Γ x) := by
  classical
  by_cases hx : gb6TraceGood x
  · have h := (isGeneratingTrace_gb6Γ hx).1.2.1
    simp only [le_top, ofPred_true] at h
    exact continuousOn_univ.1 h
  · rw [gb6Γ, ite_eq_right_of_eq_false _ _ (eq_false hx)]; exact continuous_const

/-- **The coordinates of GB6's canonical space** satisfy `IsGB6RestartCoordinates`. -/
theorem isGB6RestartCoordinates : IsGB6RestartCoordinates gb6Field gb6WC gb6Γ :=
  ⟨measurable_gb6Field, measurable_gb6WC, measurable_gb6Γ, continuous_gb6Γ⟩

/-! ### Avoiding the closed tails, as a measurable event -/

/-- `max |Im z| (min (Re z − jL) (jR − Re z))`: positive iff `z` is not in the closed tails `(−∞, jL] ∪ [jR, ∞)`. -/
def tailGap (jL jR : ℝ) (z : ℂ) : ℝ := max |z.im| (min (z.re - jL) (jR - z.re))

theorem tailGap_pos_iff {jL jR : ℝ} {z : ℂ} :
    0 < tailGap jL jR z ↔ ¬ (z.im = 0 ∧ (jR ≤ z.re ∨ z.re ≤ jL)) := by
  unfold tailGap
  rw [lt_max_iff, lt_min_iff, abs_pos]
  constructor
  · rintro (h | ⟨h1, h2⟩) ⟨hi, hr⟩
    · exact h hi
    · rcases hr with hr | hr <;> linarith
  · intro h
    by_cases hi : z.im = 0
    · right
      push Not at h
      obtain ⟨h1, h2⟩ := h hi
      exact ⟨by linarith, by linarith⟩
    · exact Or.inl hi

theorem continuous_tailGap (jL jR : ℝ) : Continuous (tailGap jL jR) := by
  unfold tailGap; fun_prop

theorem measurable_tailGap : Measurable fun p : (ℝ × ℝ) × ℂ => tailGap p.1.1 p.1.2 p.2 := by
  unfold tailGap; fun_prop

/-- **Positivity at every time is a measurable event for continuous paths** (an infimum over a compact time interval is
an infimum over the dyadic times). -/
theorem measurableSet_forall_pos {S : Type*} [MeasurableSpace S] {g : S → ℝ≥0 → ℝ}
    (hg : ∀ t, Measurable fun x => g x t) (hc : ∀ x, Continuous (g x)) :
    MeasurableSet {x | ∀ t, 0 < g x t} := by
  have e : {x | ∀ t, 0 < g x t} = ⋂ N : ℕ, ⋃ m : ℕ, ⋂ n : ℕ, ⋂ k : ℕ,
      {x | dyad n k ≤ (N : ℝ≥0) → 1 / ((m : ℝ) + 1) ≤ g x (dyad n k)} := by
    ext x
    simp only [mem_ofPred_eq, mem_iInter, mem_iUnion]
    constructor
    · intro h N
      obtain ⟨t₀, -, ht₀⟩ := (isCompact_Icc (a := (0 : ℝ≥0)) (b := (N : ℝ≥0))).exists_isMinOn
        (nonempty_Icc.2 zero_le) (hc x).continuousOn
      obtain ⟨m, hm⟩ := exists_nat_one_div_lt (h t₀)
      exact ⟨m, fun n k hd => le_trans hm.le (ht₀ ⟨zero_le, hd⟩)⟩
    · intro h t
      obtain ⟨N, hN⟩ := exists_nat_ge t
      obtain ⟨m, hm⟩ := h N
      have hlim := ((hc x).tendsto t).comp (tendsto_dyad_flr t)
      have hle : 1 / ((m : ℝ) + 1) ≤ g x t :=
        ge_of_tendsto hlim (Eventually.of_forall fun n => hm n _ ((dyad_flr_le n t).trans hN))
      exact lt_of_lt_of_le (by positivity) hle
  rw [e]
  refine MeasurableSet.iInter fun N => MeasurableSet.iUnion fun m => MeasurableSet.iInter fun n =>
    MeasurableSet.iInter fun k => measurableSet_setOfPred.2 ?_
  exact (measurableSet_setOfPred.1 (MeasurableSet.const _)).imp
    (measurableSet_setOfPred.1 (measurableSet_le measurable_const (hg _)))

/-- The chart path avoids the closed tails of the junction coordinates at every time. -/
def gb6TailAvoid (x : GB6Space) : Prop := ∀ t, 0 < tailGap (gb6JL x) (gb6JR x) (gb6Γ x t)

theorem measurableSet_gb6TailAvoid : MeasurableSet {x : GB6Space | gb6TailAvoid x} :=
  measurableSet_forall_pos (g := fun x t => tailGap (gb6JL x) (gb6JR x) (gb6Γ x t))
    (fun t => measurable_tailGap.comp ((measurable_gb6JL.prodMk measurable_gb6JR).prodMk (measurable_gb6Γ t)))
    fun x => (continuous_tailGap _ _).comp (continuous_gb6Γ x)

/-- **The good event of GB6's canonical space**: infinite code lifetime, a code uniformly continuous on every
`[0, N]`, a chart path that is a continuous transient generating trace of the chart driver, and avoidance of the
closed tails. -/
def IsGB6KernelGood (x : GB6Space) : Prop :=
  gb6L x = ⊤ ∧ (∀ N : ℕ, UC (gb6Code x).1 N) ∧ gb6TraceGood x ∧ gb6TailAvoid x

theorem measurableSet_isGB6KernelGood : MeasurableSet {x : GB6Space | IsGB6KernelGood x} := by
  have e : {x : GB6Space | IsGB6KernelGood x} = {x | gb6L x = ⊤} ∩ (gb6Code ⁻¹' {p | ∀ N : ℕ, UC p.1 N}) ∩
      ({x | gb6TraceGood x} ∩ {x | gb6TailAvoid x}) := by
    ext x; simp only [IsGB6KernelGood, mem_ofPred_eq, mem_inter_iff, mem_preimage, and_assoc]
  rw [e]
  exact ((measurableSet_eq_fun measurable_gb6L measurable_const).inter
    (measurable_gb6Code measurableSet_uc_all)).inter (measurableSet_gb6TraceGood.inter measurableSet_gb6TailAvoid)

end GB6

end Supp8

end InteractingSLE
