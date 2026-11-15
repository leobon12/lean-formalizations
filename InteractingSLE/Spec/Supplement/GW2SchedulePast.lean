/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW2ScheduleCanon

/-!
# The retained past of a GW2 schedule

Packet PROVE-T14-TIP3. For a GW2 flow program (`GW2ScheduleRun`) and any drivers, the retained past `pastMap` (the
map generating the frozen `pastSigma`) is described explicitly:

* on the event `AllSucc` that the first `k` pieces stopped before their lifetimes, it is the sequence of records
  `recOf (Δ i) (E i)` (`pastMap_of_allSucc`);
* that event is read off the threshold flags of the retained past (`allSucc_iff_flags`), so it is an event of every
  later retained past (`measurableSet_allSucc`);
* the canonical boundary word is a measurable function of the retained past (`pastWord`, `pastWord_canonRec`).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology
open scoped NNReal ENNReal

universe u

namespace InteractingSLE

namespace Theorem14

namespace GW2Schedule

open Exist Staged StagedLaw Restart LQGMetric

section Past

variable {κ : ℝ} {b : ℝ → ℝ} {jumps : Finset ℝ} {spec : ExplSpec} {θ : ℕ → ℝ} {Δ : ℕ → ℝ≥0∞} {Ω : Type*}

theorem recOf_flag (t : ℝ≥0∞) (e : (ℝ≥0 → ℝ) × ℝ≥0∞) : (recOf t e).2.2 = decide (e.2 ≤ t) := rfl

/-- **On the event that the first `k` pieces were successful, the retained past is the sequence of their records.** -/
theorem pastMap_of_allSucc (hgw : spec.2.1 = true) (hprog : IsFlowProg spec.2.2 θ Δ) (hΔ : ∀ j, Δ j ≠ ⊤)
    (E : ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞) {k : ℕ} (hk : k ≤ spec.2.2.length) {ω : Ω}
    (hs : AllSucc Δ (fun j => E j ω) k) :
    pastMap κ b jumps spec E k ω = fun i : Fin k => recOf (Δ i) (E i ω) := by
  funext i
  change readRec ((ExplState.run κ b jumps spec (fun j => E j ω) k).2.2.1 i) = _
  rw [retained_run_of_lt spec _ i.2,
    retained_run_gw2 hgw hprog hΔ _ (lt_of_lt_of_le i.2 hk) (hs.mono i.2.le)]
  rfl

/-- **The success of the first `k` pieces is read off the threshold flags of the retained past.** -/
theorem allSucc_iff_flags (hgw : spec.2.1 = true) (hprog : IsFlowProg spec.2.2 θ Δ) (hΔ : ∀ j, Δ j ≠ ⊤)
    (E : ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞) {k : ℕ} (hk : k ≤ spec.2.2.length) (ω : Ω) :
    AllSucc Δ (fun j => E j ω) k ↔ ∀ i : Fin k, (pastMap κ b jumps spec E k ω i).2.2 = false := by
  classical
  constructor
  · intro hs i
    rw [pastMap_of_allSucc hgw hprog hΔ E hk hs, recOf_flag]
    exact decide_eq_false (not_le.2 (hs i i.2))
  · intro hf
    by_contra hns
    have hex : ∃ j, j < k ∧ ¬ Δ j < (E j ω).2 := by
      by_contra hno
      push Not at hno
      exact hns fun j hj => hno j hj
    set j₀ := Nat.find hex with hj₀
    have hj₀k : j₀ < k := (Nat.find_spec hex).1
    have hj₀f : ¬ Δ j₀ < (E j₀ ω).2 := (Nat.find_spec hex).2
    have hs₀ : AllSucc Δ (fun j => E j ω) j₀ := fun j hj => by
      by_contra h'
      exact Nat.find_min hex hj ⟨lt_trans hj hj₀k, h'⟩
    have hflag := hf ⟨j₀, hj₀k⟩
    change (readRec ((ExplState.run κ b jumps spec (fun j => E j ω) k).2.2.1 j₀)).2.2 = false at hflag
    rw [retained_run_of_lt spec _ hj₀k, retained_run_gw2 hgw hprog hΔ _ (lt_of_lt_of_le hj₀k hk) hs₀] at hflag
    have : (recOf (Δ j₀) (E j₀ ω)).2.2 = false := hflag
    rw [recOf_flag, decide_eq_false_iff_not] at this
    exact hj₀f (not_le.1 this)

/-- The success event is an event of the retained past (for drivers with a measurable retained past). -/
theorem measurableSet_allSucc (hgw : spec.2.1 = true) (hprog : IsFlowProg spec.2.2 θ Δ) (hΔ : ∀ j, Δ j ≠ ⊤)
    (E : ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞) {k : ℕ} (hk : k ≤ spec.2.2.length) :
    MeasurableSet[pastSigma κ b jumps spec E k] {ω | AllSucc Δ (fun j => E j ω) k} := by
  have e : {ω | AllSucc Δ (fun j => E j ω) k} =
      pastMap κ b jumps spec E k ⁻¹' {u : PastData k | ∀ i : Fin k, (u i).2.2 = false} := by
    ext ω
    exact allSucc_iff_flags hgw hprog hΔ E hk ω
  rw [e, pastSigma_eq_comap]
  refine ⟨_, ?_, rfl⟩
  have : {u : PastData k | ∀ i : Fin k, (u i).2.2 = false} =
      ⋂ i : Fin k, (fun u : PastData k => (u i).2.2) ⁻¹' {false} :=
    by ext u; simp
  rw [this]
  exact MeasurableSet.iInter fun i =>
    (measurable_snd.comp (measurable_snd.comp (measurable_pi_apply i))) (measurableSet_singleton false)

end Past

/-! ### The canonical word read off the retained past -/

section Word

variable (βA : BoundaryWord × ℝ × RecData → BoundaryWord) (c₀ : BoundaryWord) (x₀ : ℝ) (θ : ℕ → ℝ)

/-- **The canonical word read off a retained past**: the root word, then the single-stage word of each record. -/
def pastWord : (k : ℕ) → PastData k → BoundaryWord
  | 0 => fun _ => BoundaryWord.shiftW x₀ c₀
  | k + 1 => fun u => βA (pastWord k (Fin.init (α := fun _ => RecData) u), θ k, u (Fin.last k))

theorem measurable_pastWord (hβA : Measurable βA) : ∀ k, Measurable (pastWord βA c₀ x₀ θ k)
  | 0 => measurable_const
  | k + 1 => by
    have hinit : Measurable fun u : PastData (k + 1) => Fin.init (α := fun _ => RecData) u :=
      measurable_pi_iff.2 fun i => measurable_pi_apply _
    exact measurable_apply_triple hβA ((measurable_pastWord hβA k).comp hinit) measurable_const
      (measurable_pi_apply (Fin.last k))

variable {κ : ℝ} (hκ : 0 < κ) (h12p : Theorem12ParamStatement.{u})

/-- **The canonical word is the word read off the canonical records.** -/
theorem pastWord_canonRec (Δ : ℕ → ℝ≥0∞) (f : DistOn upperHalfPlaneOpens) :
    ∀ k, pastWord βA c₀ x₀ θ k (fun i => canonRec hκ h12p βA c₀ x₀ θ Δ f i) =
      (canonState hκ h12p βA c₀ x₀ θ Δ f k).1
  | 0 => rfl
  | k + 1 => by
    rw [canonState_succ]
    change βA (pastWord βA c₀ x₀ θ k (fun i : Fin k => canonRec hκ h12p βA c₀ x₀ θ Δ f i), θ k,
      canonRec hκ h12p βA c₀ x₀ θ Δ f k) = _
    rw [pastWord_canonRec Δ f k]

end Word

end GW2Schedule

end Theorem14

end InteractingSLE
