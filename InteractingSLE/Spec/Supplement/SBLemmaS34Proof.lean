/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.SBLemmaS2
import InteractingSLE.Spec.Supplement.SB4Clauses

/-!
# Lemmas S3 and S4 under ruling R51; S4's hull clause from S1 and S2

Packet PROVE-T14-SB6. Lemmas S3 and S4 (supplement pp. 579–582, `source/spec/p577-624.md` L49–L101) are stated in
`SBLemmaS` over every family satisfying `IsStagedHistory`. Their conclusions are pathwise statements about the own
history's physical set (`schedulePrefix`), which by R51 is only controlled for `StagedPiecesRegular` families; the
regularized forms carry that hypothesis (right after `hE`, as in `SBFrontierRegStatement`):

* `S3RegStatement`, `S4RegStatement`, with `s3RegStatement_of_unreg`, `s4RegStatement_of_unreg`;
* S4 split into its two clauses: **`S4HullRegStatement`** ("`β([0, T ∧ τ]) ⊆ K_A`", deterministic once `A` is a path
  image) and `S4CondRegStatement` (the conditional flow in the left entry chart — the probabilistic content);
  `s4RegStatement_of_hull_cond`;
* **`image_subset_hullK_of_isOneSided`** (deterministic, proved): if S1 holds for `A = p([0, 1])` and every available
  prefix of `β` from `0`, then `β([0, T ∧ ζ ∧ τ]) ⊆ K_A`, `τ` the first visit of `β` to `L = min(A ∩ ℝ)` (S4's proof:
  "S2 gives `β([0, τ ∧ T]) ⊆ K_A`"); from `s2HullStatement`;
* `OwnHistoryPathRegStatement` (named input: an own history through `k` instructions is the compact range of a
  continuous path from `0` in `closure ℍ`, S0–S1's "parameterized part of the original history"), and
  **`s4HullRegStatement_of_path`**.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal
open QuantumZipper (chiC H)
open LQGMetric (DistOn)

universe u

namespace InteractingSLE

namespace Theorem14

namespace SB

/-! ### S4's hull clause, deterministically -/

/-- **S4's hull clause from S1 and S2** (supplement p. 580: "The point `L` is determined by `A`, so its first visit
`τ` is a stopping time [...] S2 gives `β([0, τ ∧ T]) ⊆ K_A`"). Let `A = p([0, 1])` be the compact range of a
continuous path from `0` in `closure ℍ` and `β` a curve from `0` such that S1 holds for `A` and every prefix
`β([0, a])`, `a ≤ ζ`. Then for every `T`, `β([0, T ∧ ζ ∧ τ]) ⊆ K_A`, where `τ` is the first visit of `β` to
`L = min(A ∩ ℝ)`. Proof: for `s` in the range take an S1 witness `β'` of `β([0, s])`; S2 gives `t_L` with
`β'(t_L) = L` and `β'([0, t_L]) ⊆ K_A`; if `t_L < s` then `β(t_L) = L` and `τ ≤ t_L < s`, impossible. -/
theorem image_subset_hullK_of_isOneSided {p : ℝ → ℂ} {β : ℝ≥0 → ℂ} {ζ T : ℝ≥0∞}
    (hp : ContinuousOn p (Icc 0 1)) (hp0 : p 0 = 0) (hpH : ∀ s ∈ Icc (0 : ℝ) 1, 0 ≤ (p s).im) (hβ0 : β 0 = 0)
    (hS1 : ∀ a : ℝ≥0, (a : ℝ≥0∞) ≤ ζ → IsOneSided (p '' Icc 0 1) β a) :
    β '' {s | (s : ℝ≥0∞) ≤ min (min T ζ) (firstVisit β ζ (realMin (p '' Icc 0 1)))} ⊆
      hullK (p '' Icc 0 1) := by
  rintro _ ⟨s, hs, rfl⟩
  have hs' : (s : ℝ≥0∞) ≤ min (min T ζ) (firstVisit β ζ (realMin (p '' Icc 0 1))) := hs
  have hsζ : (s : ℝ≥0∞) ≤ ζ := hs'.trans ((min_le_left _ _).trans (min_le_right _ _))
  have hsτ : (s : ℝ≥0∞) ≤ firstVisit β ζ (realMin (p '' Icc 0 1)) := hs'.trans (min_le_right _ _)
  obtain ⟨β', hβ', hA⟩ := hS1 s hsζ
  have hβ'0 : β' 0 = 0 := (hβ'.2.2.2.2 0 zero_le).trans hβ0
  obtain ⟨-, tL, htL, -, hsub, -⟩ :=
    s2HullStatement p β' hp hp0 hpH (Supp9B.isProperCurve_of_isProperCompletion hβ') hβ'0 hA
  by_cases hst : s ≤ tL
  · rw [← hβ'.2.2.2.2 s le_rfl]
    exact hsub ⟨s, ⟨zero_le, hst⟩, rfl⟩
  · exfalso
    have hlt : tL < s := not_le.1 hst
    have hvis : firstVisit β ζ (realMin (p '' Icc 0 1)) ≤ tL := by
      refine iInf₂_le tL ⟨(ENNReal.coe_le_coe.2 hlt.le).trans hsζ, ?_⟩
      rw [← hβ'.2.2.2.2 tL hlt.le]
      exact htL
    exact absurd (ENNReal.coe_le_coe.1 (hsτ.trans hvis)) (not_le.2 hlt)

/-! ### The regularized statements -/

/-- **Lemma S3 for regular families** (`S3Statement` with R51's hypothesis `StagedPiecesRegular`). -/
def S3RegStatement : Prop :=
  ∀ κ : ℝ, 0 < κ → κ < 4 → ∀ (b : ℝ → ℝ) (jumps : Finset ℝ), IsPiecewiseConstantBoundaryData b jumps →
    ∀ {Ω : Type u} [MeasurableSpace Ω] [StandardBorelSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
      (h : Ω → DistOn upperHalfPlaneOpens), IsGFFWithBoundaryData P h b jumps →
    ∀ E : ExplSpec → ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞,
      (∀ spec : ExplSpec, IsBoundaryContinuedProgram spec.2.2 →
        IsStagedHistory κ b jumps P h spec (E spec)) →
      (∀ spec : ExplSpec, IsBoundaryContinuedProgram spec.2.2 →
        StagedPiecesRegular κ b jumps P spec (E spec)) →
    ∀ (l : List (ℝ × ℝ≥0)) (k : ℕ) (ϑ : ℝ), l.Pairwise (fun p q => p.2 < q.2) →
      (∀ p ∈ l, p.1 ∈ Icc (-(Real.pi / 2)) (Real.pi / 2) ∧ p.1 < ϑ) → ϑ ≤ Real.pi / 2 →
    ∀ (β : Ω → ℝ≥0 → ℂ) (ζ : Ω → ℝ≥0∞), IsFlowLine κ b jumps 0 ϑ P h β ζ →
      (∀ᵐ ω ∂P, ∀ a : ℝ≥0, (a : ℝ≥0∞) ≤ ζ ω → IsOneSided (schedulePrefix κ b jumps E l k ω) (β ω) a) →
      ∀ᵐ ω ∂P, ∀ s₁ s₂ : ℝ≥0, firstVisit (β ω) (ζ ω) (realMin (schedulePrefix κ b jumps E l k ω)) ≤ s₁ →
        s₁ < s₂ → (s₂ : ℝ≥0∞) ≤ ζ ω → ¬ β ω '' Ioo s₁ s₂ ⊆ schedulePrefix κ b jumps E l k ω

/-- **Lemma S4 for regular families** (`S4Statement` with R51's hypothesis `StagedPiecesRegular`). -/
def S4RegStatement : Prop :=
  ∀ κ : ℝ, 0 < κ → κ < 4 → ∀ (b : ℝ → ℝ) (jumps : Finset ℝ), IsPiecewiseConstantBoundaryData b jumps →
    ∀ {Ω : Type u} [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
      (h : Ω → DistOn upperHalfPlaneOpens), IsGFFWithBoundaryData P h b jumps →
    ∀ E : ExplSpec → ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞,
      (∀ spec : ExplSpec, IsBoundaryContinuedProgram spec.2.2 →
        IsStagedHistory κ b jumps P h spec (E spec)) →
      (∀ spec : ExplSpec, IsBoundaryContinuedProgram spec.2.2 →
        StagedPiecesRegular κ b jumps P spec (E spec)) →
    ∀ (l : List (ℝ × ℝ≥0)) (k : ℕ) (ϑ : ℝ), l.Pairwise (fun p q => p.2 < q.2) →
      (∀ p ∈ l, p.1 ∈ Icc (-(Real.pi / 2)) (Real.pi / 2) ∧ p.1 < ϑ) → ϑ ≤ Real.pi / 2 →
    ∀ (β : Ω → ℝ≥0 → ℂ) (ζ : Ω → ℝ≥0∞), IsFlowLine κ b jumps 0 ϑ P h β ζ →
      (∀ᵐ ω ∂P, ∀ a : ℝ≥0, (a : ℝ≥0∞) ≤ ζ ω → IsOneSided (schedulePrefix κ b jumps E l k ω) (β ω) a) →
    ∀ t : ℝ≥0∞,
      (∀ᵐ ω ∂P, β ω '' {s | (s : ℝ≥0∞) ≤ min (min t (ζ ω))
          (firstVisit (β ω) (ζ ω) (realMin (schedulePrefix κ b jumps E l k ω)))} ⊆
        hullK (schedulePrefix κ b jumps E l k ω)) ∧
      ∃ (𝒢 : MeasurableSpace Ω) (c : Ω → Chart) (bc : Ω → ℝ → ℝ) (jc : Ω → Finset ℝ) (Wr : ℝ≥0 → Ω → ℝ)
        (ζr Tr : Ω → ℝ≥0∞),
        𝒢 ≤ mΩ ∧ pastSigma κ b jumps ⟨0, true, scheduleProgram 0 l⟩ (E ⟨0, true, scheduleProgram 0 l⟩) k ≤ 𝒢 ∧
        IsCondFlowLineDriverOn (mΩ := mΩ) κ ϑ 𝒢 P
          {ω | firstVisit (β ω) (ζ ω) (realMin (schedulePrefix κ b jumps E l k ω)) < min t (ζ ω)} h c bc jc Wr ζr ∧
        ∀ᵐ ω ∂P, firstVisit (β ω) (ζ ω) (realMin (schedulePrefix κ b jumps E l k ω)) < min t (ζ ω) →
          IsLeftEntryChart (schedulePrefix κ b jumps E l k ω) (realMin (schedulePrefix κ b jumps E l k ω)) (c ω) ∧
          RetainsOriginalHeights (schedulePrefix κ b jumps E l k ω) (c ω) b jumps (bc ω) (jc ω) ∧
          Tr ω ≤ ζr ω ∧
          β ω '' {s | firstVisit (β ω) (ζ ω) (realMin (schedulePrefix κ b jumps E l k ω)) < (s : ℝ≥0∞) ∧
              (s : ℝ≥0∞) ≤ min t (ζ ω)} ⊆ (c ω).tipSet (fun r => Wr r ω) (Tr ω) ∧
          (c ω).tipSet (fun r => Wr r ω) (Tr ω) ⊆
            β ω '' {s | firstVisit (β ω) (ζ ω) (realMin (schedulePrefix κ b jumps E l k ω)) ≤ (s : ℝ≥0∞) ∧
              (s : ℝ≥0∞) ≤ min t (ζ ω)}

/-- **Lemma S4, the hull clause, for regular families** (the first conjunct of `S4RegStatement`: "If `T ≤ τ`, its
whole available history is contained in `K_A`"; p. 580 "S2 gives `β([0, τ ∧ T]) ⊆ K_A`"). -/
def S4HullRegStatement : Prop :=
  ∀ κ : ℝ, 0 < κ → κ < 4 → ∀ (b : ℝ → ℝ) (jumps : Finset ℝ), IsPiecewiseConstantBoundaryData b jumps →
    ∀ {Ω : Type u} [MeasurableSpace Ω] [StandardBorelSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
      (h : Ω → DistOn upperHalfPlaneOpens), IsGFFWithBoundaryData P h b jumps →
    ∀ E : ExplSpec → ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞,
      (∀ spec : ExplSpec, IsBoundaryContinuedProgram spec.2.2 →
        IsStagedHistory κ b jumps P h spec (E spec)) →
      (∀ spec : ExplSpec, IsBoundaryContinuedProgram spec.2.2 →
        StagedPiecesRegular κ b jumps P spec (E spec)) →
    ∀ (l : List (ℝ × ℝ≥0)) (k : ℕ) (ϑ : ℝ), l.Pairwise (fun p q => p.2 < q.2) →
      (∀ p ∈ l, p.1 ∈ Icc (-(Real.pi / 2)) (Real.pi / 2) ∧ p.1 < ϑ) → ϑ ≤ Real.pi / 2 →
    ∀ (β : Ω → ℝ≥0 → ℂ) (ζ : Ω → ℝ≥0∞), IsFlowLine κ b jumps 0 ϑ P h β ζ →
      (∀ᵐ ω ∂P, ∀ a : ℝ≥0, (a : ℝ≥0∞) ≤ ζ ω → IsOneSided (schedulePrefix κ b jumps E l k ω) (β ω) a) →
    ∀ t : ℝ≥0∞,
      (∀ᵐ ω ∂P, β ω '' {s | (s : ℝ≥0∞) ≤ min (min t (ζ ω))
          (firstVisit (β ω) (ζ ω) (realMin (schedulePrefix κ b jumps E l k ω)))} ⊆
        hullK (schedulePrefix κ b jumps E l k ω))

/-- **Lemma S4, the conditional clause, for regular families** (the second conjunct of `S4RegStatement`: the lift of
the post-`τ` portion is the canonical angle-`ϑ` flow of the conditional field in a left entry chart of `D_A`, stopped
by the reconstructed rule). This is the probabilistic content of S4. -/
def S4CondRegStatement : Prop :=
  ∀ κ : ℝ, 0 < κ → κ < 4 → ∀ (b : ℝ → ℝ) (jumps : Finset ℝ), IsPiecewiseConstantBoundaryData b jumps →
    ∀ {Ω : Type u} [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
      (h : Ω → DistOn upperHalfPlaneOpens), IsGFFWithBoundaryData P h b jumps →
    ∀ E : ExplSpec → ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞,
      (∀ spec : ExplSpec, IsBoundaryContinuedProgram spec.2.2 →
        IsStagedHistory κ b jumps P h spec (E spec)) →
      (∀ spec : ExplSpec, IsBoundaryContinuedProgram spec.2.2 →
        StagedPiecesRegular κ b jumps P spec (E spec)) →
    ∀ (l : List (ℝ × ℝ≥0)) (k : ℕ) (ϑ : ℝ), l.Pairwise (fun p q => p.2 < q.2) →
      (∀ p ∈ l, p.1 ∈ Icc (-(Real.pi / 2)) (Real.pi / 2) ∧ p.1 < ϑ) → ϑ ≤ Real.pi / 2 →
    ∀ (β : Ω → ℝ≥0 → ℂ) (ζ : Ω → ℝ≥0∞), IsFlowLine κ b jumps 0 ϑ P h β ζ →
      (∀ᵐ ω ∂P, ∀ a : ℝ≥0, (a : ℝ≥0∞) ≤ ζ ω → IsOneSided (schedulePrefix κ b jumps E l k ω) (β ω) a) →
    ∀ t : ℝ≥0∞,
      ∃ (𝒢 : MeasurableSpace Ω) (c : Ω → Chart) (bc : Ω → ℝ → ℝ) (jc : Ω → Finset ℝ) (Wr : ℝ≥0 → Ω → ℝ)
        (ζr Tr : Ω → ℝ≥0∞),
        𝒢 ≤ mΩ ∧ pastSigma κ b jumps ⟨0, true, scheduleProgram 0 l⟩ (E ⟨0, true, scheduleProgram 0 l⟩) k ≤ 𝒢 ∧
        IsCondFlowLineDriverOn (mΩ := mΩ) κ ϑ 𝒢 P
          {ω | firstVisit (β ω) (ζ ω) (realMin (schedulePrefix κ b jumps E l k ω)) < min t (ζ ω)} h c bc jc Wr ζr ∧
        ∀ᵐ ω ∂P, firstVisit (β ω) (ζ ω) (realMin (schedulePrefix κ b jumps E l k ω)) < min t (ζ ω) →
          IsLeftEntryChart (schedulePrefix κ b jumps E l k ω) (realMin (schedulePrefix κ b jumps E l k ω)) (c ω) ∧
          RetainsOriginalHeights (schedulePrefix κ b jumps E l k ω) (c ω) b jumps (bc ω) (jc ω) ∧
          Tr ω ≤ ζr ω ∧
          β ω '' {s | firstVisit (β ω) (ζ ω) (realMin (schedulePrefix κ b jumps E l k ω)) < (s : ℝ≥0∞) ∧
              (s : ℝ≥0∞) ≤ min t (ζ ω)} ⊆ (c ω).tipSet (fun r => Wr r ω) (Tr ω) ∧
          (c ω).tipSet (fun r => Wr r ω) (Tr ω) ⊆
            β ω '' {s | firstVisit (β ω) (ζ ω) (realMin (schedulePrefix κ b jumps E l k ω)) ≤ (s : ℝ≥0∞) ∧
              (s : ℝ≥0∞) ≤ min t (ζ ω)}

/-- **Named input: an own history is a path image** (S0–S1, supplement pp. 576–577: "Take any parameterized part of
the original history in `A` from `0`"; S0: the own histories are actual finite concatenations of continuous pieces),
for regular families: almost surely the own history from `0` through `k` instructions of a schedule `l` is the compact
range `p([0, 1])` of a continuous path from `0` in `closure ℍ`. -/
def OwnHistoryPathRegStatement : Prop :=
  ∀ κ : ℝ, 0 < κ → κ < 4 → ∀ (b : ℝ → ℝ) (jumps : Finset ℝ), IsPiecewiseConstantBoundaryData b jumps →
    ∀ {Ω : Type u} [MeasurableSpace Ω] [StandardBorelSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
      (h : Ω → DistOn upperHalfPlaneOpens), IsGFFWithBoundaryData P h b jumps →
    ∀ E : ExplSpec → ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞,
      (∀ spec : ExplSpec, IsBoundaryContinuedProgram spec.2.2 →
        IsStagedHistory κ b jumps P h spec (E spec)) →
      (∀ spec : ExplSpec, IsBoundaryContinuedProgram spec.2.2 →
        StagedPiecesRegular κ b jumps P spec (E spec)) →
    ∀ (l : List (ℝ × ℝ≥0)) (k : ℕ), l.Pairwise (fun p q => p.2 < q.2) →
      (∀ p ∈ l, p.1 ∈ Icc (-(Real.pi / 2)) (Real.pi / 2)) →
      ∀ᵐ ω ∂P, ∃ p : ℝ → ℂ, ContinuousOn p (Icc 0 1) ∧ p 0 = 0 ∧ (∀ s ∈ Icc (0 : ℝ) 1, 0 ≤ (p s).im) ∧
        schedulePrefix κ b jumps E l k ω = p '' Icc 0 1
/-! ### Bridges and reductions -/

theorem s3RegStatement_of_unreg (h : S3Statement.{u}) : S3RegStatement.{u} :=
  fun κ hκ hκ4 b jumps hb _ _ _ P _ h' hh E hE _ => h κ hκ hκ4 b jumps hb P h' hh E hE

theorem s4RegStatement_of_unreg (h : S4Statement.{u}) : S4RegStatement.{u} :=
  fun κ hκ hκ4 b jumps hb _ _ _ P _ h' hh E hE _ => h κ hκ hκ4 b jumps hb P h' hh E hE

/-- **Lemma S4 from its two clauses** (for regular families). -/
theorem s4RegStatement_of_hull_cond (hH : S4HullRegStatement.{u}) (hC : S4CondRegStatement.{u}) :
    S4RegStatement.{u} := by
  intro κ hκ hκ4 b jumps hb Ω _ _ P _ h hh E hE hreg l k ϑ hl hθ hϑ β ζ hβ hS1 t
  exact ⟨hH κ hκ hκ4 b jumps hb P h hh E hE hreg l k ϑ hl hθ hϑ β ζ hβ hS1 t,
    hC κ hκ hκ4 b jumps hb P h hh E hE hreg l k ϑ hl hθ hϑ β ζ hβ hS1 t⟩

/-- **Lemma S4's hull clause from the path parametrization of the own history** (`image_subset_hullK_of_isOneSided`
at every sample: the flow starts at `0`, S1 holds almost surely, and the own history is a path image). -/
theorem s4HullRegStatement_of_path (hP : OwnHistoryPathRegStatement.{u}) : S4HullRegStatement.{u} := by
  intro κ hκ hκ4 b jumps hb Ω _ _ P _ h hh E hE hreg l k ϑ hl hθ hϑ β ζ hβ hS1 t
  filter_upwards [hP κ hκ hκ4 b jumps hb P h hh E hE hreg l k hl fun p hp => (hθ p hp).1,
    IsFlowLine.ae_seed_continuousOn hβ, hS1] with ω ⟨p, hp, hp0, hpH, hA⟩ ⟨h0, _⟩ hS
  rw [hA] at hS ⊢
  exact image_subset_hullK_of_isOneSided hp hp0 hpH (by simpa using h0) hS

/-- **Lemma S4 for regular families from the own-history parametrization and the conditional clause.** -/
theorem s4RegStatement_of_path_cond (hP : OwnHistoryPathRegStatement.{u}) (hC : S4CondRegStatement.{u}) :
    S4RegStatement.{u} :=
  s4RegStatement_of_hull_cond (s4HullRegStatement_of_path hP) hC

end SB

end Theorem14

end InteractingSLE
