/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.SB2DrvHint

/-!
# S3: genealogy of values in an actual conditional stage word

An unmarked value in the explicit staged word is either an original boundary
value or a side height of an actually launched earlier piece. This uses the
existing stopped-word value classification and explicit stage induction. It
does not yet exclude the original-boundary alternative at an interior landing.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped NNReal ENNReal
open QuantumZipper (chiC)
open LQGMetric (DistOn)

universe u

namespace InteractingSLE.Theorem14.SB.S3

open Exist Exist.Staged Exist.StagedLaw Restart GW1W

/-- Every predicate containing the old unmarked values and the two new side
heights contains all unmarked values of the stopped word. -/
theorem stopWord_values_of_predicate {κ : ℝ} (hκ : 0 < κ) {c : BoundaryWord}
    {P : ℝ → Prop} (hc : ∀ x ∉ c.jumps, P (c.fn x)) (θ : ℝ) (r : RecData)
    (hL : P (-sleLambda κ - θ * chiC κ)) (hR : P (sleLambda κ - θ * chiC κ)) :
    ∀ y ∉ (stopWord κ (c, θ, r)).jumps, P ((stopWord κ (c, θ, r)).fn y) := by
  have hneg : ∀ y < 0, P ((stopWord κ (c, θ, r)).fn y) := by
    intro y hy
    rcases Lh.stopWord_fn_neg_mem hκ c θ r hy with he | ⟨x, -, hxJ, he⟩
    · exact he ▸ hL
    · exact he ▸ hc x hxJ
  intro y hy
  rcases lt_trichotomy y 0 with hy0 | rfl | hy0
  · exact hneg y hy0
  · obtain ⟨z, hz, hz0⟩ := ((BoundaryWord.eventually_index_eq hy).filter_mono
      (nhdsWithin_le_nhds (s := Iio (0 : ℝ)))).and self_mem_nhdsWithin |>.exists
    have he : (stopWord κ (c, θ, r)).fn z = (stopWord κ (c, θ, r)).fn 0 := by
      unfold BoundaryWord.fn
      rw [hz]
    exact he ▸ hneg z hz0
  · rcases Lv.stopWord_fn_pos_mem hκ c θ r hy0 with he | ⟨x, -, hxJ, he⟩
    · exact he ▸ hR
    · exact he ▸ hc x hxJ

/-- Recentering the word preserves every predicate of its unmarked values. -/
theorem shiftW_values_of_predicate {c : BoundaryWord} {P : ℝ → Prop}
    (hc : ∀ x ∉ c.jumps, P (c.fn x)) (a : ℝ) :
    ∀ y ∉ (BoundaryWord.shiftW a c).jumps, P ((BoundaryWord.shiftW a c).fn y) := by
  intro y hy
  rw [BoundaryWord.fn_shiftW]
  apply hc
  intro h
  apply hy
  rw [BoundaryWord.jumps_shiftW]
  exact Finset.mem_image.2 ⟨y + a, h, by ring⟩

/-- The possible origins of a stage word value: original real data or one
side of a genuinely launched earlier piece of the actual run. -/
def StageHeight (κ : ℝ) (b : ℝ → ℝ) (jumps : Finset ℝ) (spec : ExplSpec)
    (D : ℕ → (ℝ≥0 → ℝ) × ℝ≥0∞) (k : ℕ) (v : ℝ) : Prop :=
  (∃ x ∉ jumps, v = b x) ∨
    ∃ j < k, (ExplState.run κ b jumps spec D (j + 1)).2.2.2.1 j ≠ none ∧
      (v = sleLambda κ - instrAngle spec j * chiC κ ∨
        v = -sleLambda κ - instrAngle spec j * chiC κ)

/-- Increasing the stage keeps every previously certified value origin. -/
theorem StageHeight.mono {κ : ℝ} {b : ℝ → ℝ} {jumps : Finset ℝ} {spec : ExplSpec}
    {D : ℕ → (ℝ≥0 → ℝ) × ℝ≥0∞} {k n : ℕ} (hkn : k ≤ n) {v : ℝ}
    (hv : StageHeight κ b jumps spec D k v) : StageHeight κ b jumps spec D n v := by
  rcases hv with h | ⟨j, hj, hlaunch, he⟩
  · exact Or.inl h
  · exact Or.inr ⟨j, hj.trans_le hkn, hlaunch, he⟩

/-- Every stage has an actual conditional-law witness whose unmarked word
values have the displayed genealogy. No ambient boundary bound or walk
admissibility assumption is added to the staged-history hypotheses. -/
theorem exists_stageWitness_heightOrigin {κ : ℝ} (hκ : 0 < κ)
    {b : ℝ → ℝ} {jumps : Finset ℝ} (hb : IsPiecewiseConstantBoundaryData b jumps)
    {Ω : Type u} [MeasurableSpace Ω] [StandardBorelSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] {h : Ω → DistOn upperHalfPlaneOpens}
    (hh : IsGFFWithBoundaryData P h b jumps) {spec : ExplSpec}
    {E : ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞} (hE : IsStagedHistory κ b jumps P h spec E)
    (hreg : ∀ j ω, IsRegularDriver (E j ω)) :
    ∀ k, ∃ (β : Ω → BoundaryWord) (Y : Ω → DistOn upperHalfPlaneOpens),
      IsStageWitness κ b jumps P h spec E k β Y ∧
      ∀ᵐ ω ∂P, (ExplState.run κ b jumps spec (fun j => E j ω) (k + 1)).2.2.2.1 k ≠ none →
        ∀ y ∉ (β ω).jumps,
          StageHeight κ b jumps spec (fun j => E j ω) k ((β ω).fn y) := by
  obtain ⟨c₀, hc₀J, hc₀⟩ := BoundaryWord.exists_fn_eq hb
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    rcases Nat.eq_zero_or_pos k with rfl | hk
    · refine ⟨fun _ => BoundaryWord.shiftW spec.1 c₀,
        fun ω => Exist.flowField spec.1 0 (h ω), GW1W.isStageWitness_zero hh hc₀J hc₀, ?_⟩
      refine Eventually.of_forall fun ω _ => shiftW_values_of_predicate (fun x hx => ?_) spec.1
      have hxJ : x ∉ jumps := by rwa [← hc₀J]
      exact Or.inl ⟨x, hxJ, hc₀ x hxJ⟩
    have Hprev : ∀ ℓ, ∃ (β : Ω → BoundaryWord) (Y : Ω → DistOn upperHalfPlaneOpens),
        ℓ < k → IsStageWitness κ b jumps P h spec E ℓ β Y ∧
          ∀ᵐ ω ∂P, (ExplState.run κ b jumps spec (fun j => E j ω) (ℓ + 1)).2.2.2.1 ℓ ≠ none →
            ∀ y ∉ (β ω).jumps,
              StageHeight κ b jumps spec (fun j => E j ω) ℓ ((β ω).fn y) := by
      intro ℓ
      by_cases hℓ : ℓ < k
      · obtain ⟨β, Y, hW, hval⟩ := ih ℓ hℓ
        exact ⟨β, Y, fun _ => ⟨hW, hval⟩⟩
      · exact ⟨fun _ => default, fun _ => 0, fun h' => absurd h' hℓ⟩
    choose β Y hprev using Hprev
    obtain ⟨βk, Yk, hWk, hexpl⟩ := GW1W.isStageWitness_succ_expl
      (GW1W.isStopLaw_stopWord.{u} hκ) runMeasStatement hκ hb hh hk
      (fun j _ => hE.1 j) (fun j _ => hreg j) (fun j _ => hE.2.2.2 j)
      β Y (fun ℓ hℓ => (hprev ℓ hℓ).1)
    refine ⟨βk, Yk, hWk, ?_⟩
    have hall : ∀ᵐ ω ∂P, ∀ ℓ, ℓ < k →
        (ExplState.run κ b jumps spec (fun j => E j ω) (ℓ + 1)).2.2.2.1 ℓ ≠ none →
        ∀ y ∉ (β ℓ ω).jumps,
          StageHeight κ b jumps spec (fun j => E j ω) ℓ ((β ℓ ω).fn y) := by
      refine ae_all_iff.2 fun ℓ => ?_
      by_cases hℓ : ℓ < k
      · exact (hprev ℓ hℓ).2.mono fun _ hω _ => hω
      · exact Eventually.of_forall fun _ h' => absurd h' hℓ
    filter_upwards [hall] with ω hω hlk
    obtain ⟨⟨c, θ⟩, hcθ⟩ := Option.ne_none_iff_exists'.1 hlk
    obtain ⟨ℓ, hℓk, ⟨c', θ', hl'⟩, -, hn, -⟩ :=
      exists_last_launch spec (fun j => E j ω) hk hcθ
    have hlℓ : (ExplState.run κ b jumps spec (fun j => E j ω) (ℓ + 1)).2.2.2.1 ℓ ≠ none := by
      rw [hl']
      exact Option.some_ne_none _
    rw [hexpl ℓ ω hℓk hlk hlℓ hn]
    apply shiftW_values_of_predicate
    refine stopWord_values_of_predicate hκ ?_ (instrAngle spec ℓ)
      (pastMap κ b jumps spec E (ℓ + 1) ω (Fin.last ℓ)) ?_ ?_
    · exact fun y hy => (hω ℓ hℓk hlℓ y hy).mono hℓk.le
    · exact Or.inr ⟨ℓ, hℓk, hlℓ, Or.inr rfl⟩
    · exact Or.inr ⟨ℓ, hℓk, hlℓ, Or.inl rfl⟩

end InteractingSLE.Theorem14.SB.S3
