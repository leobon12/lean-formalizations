/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.SB4RMirrorGeom
import InteractingSLE.Spec.Supplement.GW3SidedProofWalk

/-!
# SB4's distinct-seed leaf, left-walk half, with R95's premise

Packet PROVE-T14-SB4LEAF. The second conjunct of `Ly.SB4DistinctSeedLaunchTailRStatement`: an upper schedule from
`v ≥ 0` (angles in `[−π/2, π/2)`) against the left side of the completed left walk (angle `π/2`, continuing left).
Supplement p. 634: "Reflecting gives the upper-walk barrier". Through the reflection `ρ(z) = −z̄` the left walk becomes
a right walk of the reflected field `−h ∘ ρ`, the schedule becomes one from `−v ≤ 0` with angles `−ψ_j ∈ (−π/2, π/2]`,
and the bridge `[0, v]` the bridge `[−v, 0]`. The relative instance of R95's amended SB3 is the reflected one.

Named inputs (the mirror image of SB2(2) and of its pointwise lift, read in the reflected chart):

* **`SB2LeftLaunchStatement`**: for every witness of the conditional launch law, a translation `m ≤ 0` (the left entry
  value of the launch chart at `L = min (A ∩ ℝ)`), the admissible old groups and the active word of the reflected data,
  and a relative right walk `EL` of the reflected translated conditional field;
* **`SB2LeftTailLiftStatement`**: its pointwise lift and the free right collar of the left walk.

Ruling R104a combines the two into **`SB2LeftLaunchLiftStatement`** (an output whose completed left tail lifts),
which is proved from SB2(2)'s combined target by reflection (`SB4RSymLeft.lean`).

Proved here: the reflected bridge and word hypotheses (`bridge_reflect`, `cumWeightLeft_neg`, …);
`scheduleRelativeTailR_left_lift` and `scheduleRelativeTailR_left` are in `SB4RMirrorLeaf.lean`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Complex Set Filter Topology
open scoped NNReal ENNReal
open QuantumZipper (chiC H Hbar)
open LQGMetric (DistOn)

universe u

namespace InteractingSLE.Theorem14.SB.Lf

open Supp9B Lx Lu Ly Leaf FlowDilate Sec4 Exist.Staged Exist.StagedLaw GW2Schedule
open Sec7.FlowReflect (reflData reflJumps reflField)

/-- The completed left walk (angle `π/2`, continuing left), as a physical set. -/
def leftWalkSet {Ω : Type u} (κ : ℝ) (b : ℝ → ℝ) (jumps : Finset ℝ) (E : ExplSpec → ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞)
    (ω : Ω) : Set ℂ :=
  ExplState.physSet κ b jumps (boundaryWalkSpec b jumps (Real.pi / 2) false)
    (fun k => E (boundaryWalkSpec b jumps (Real.pi / 2) false) k ω)

/-- The reflected angle schedule `ψ_j ↦ −ψ_j`. -/
def reflAngles (l : List (ℝ × ℝ≥0)) : List (ℝ × ℝ≥0) := l.map fun p => (-p.1, p.2)

theorem mem_reflAngles {l : List (ℝ × ℝ≥0)} {p : ℝ × ℝ≥0} : p ∈ reflAngles l ↔ (-p.1, p.2) ∈ l := by
  unfold reflAngles
  constructor
  · rintro hp
    obtain ⟨q, hq, rfl⟩ := List.mem_map.1 hp
    simpa using hq
  · intro hp
    exact List.mem_map.2 ⟨(-p.1, p.2), hp, by simp⟩

theorem cumWeightLeft_neg (κ y : ℝ) : cumWeightLeft κ (-y) = cumWeightRight κ y := by
  unfold cumWeightLeft cumWeightRight; ring

theorem cumWeightRight_neg (κ y : ℝ) : cumWeightRight κ (-y) = cumWeightLeft κ y := by
  unfold cumWeightLeft cumWeightRight; ring

section Output

variable (κ : ℝ) (b : ℝ → ℝ) (jumps : Finset ℝ) {Ω : Type u} [MeasurableSpace Ω] [StandardBorelSpace Ω]
  (P : Measure Ω) [IsProbabilityMeasure P] (E : ExplSpec → ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞) (v : ℝ)
  (l : List (ℝ × ℝ≥0)) (k : ℕ) (ω₀ : Ω) (c : Chart) (b' : ℝ → ℝ) (J' : Finset ℝ)
  (h' : Ω → DistOn upperHalfPlaneOpens) (m : ℝ) (EL : ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞)

/-- **The mirror of SB2(2)'s output for one witness**, read in the reflected chart: the left entry value `m ≤ 0` of
the launch chart at `L = min (A ∩ ℝ)`, the admissible old groups of the reflected data left of the reflected tip,
the reflected active word (old sides of the angles `−ψ_j`, low heights, or the reflected bridge heights on `(−v, 0)`),
and the relative right walk `EL` of the reflected translated conditional field. -/
def IsLeftLaunchOutput : Prop :=
  m ≤ 0 ∧
    (∀ y, y ≤ m → y ∉ affJumps 1 m (reflJumps J') →
      -2 < cumWeightLeft κ (affData 1 m (reflData b') y + -(Real.pi / 2) * chiC κ)) ∧
    IsLeftEntryValue c (realMin (arcPrefix κ b jumps E v l k ω₀)) m ∧
    IsActiveHighWord κ (reflData b) (reflJumps jumps) (-v) (reflAngles l) (reflData b') (reflJumps J') m ∧
    IsStagedHistory κ (affData 1 m (reflData b')) (affJumps 1 m (reflJumps J'))
      (condExpKernel P (pastSigma κ b jumps (sspec v l) (E (sspec v l)) k) ω₀)
      (fun ω => affField m one_pos (reflField (h' ω))) (relLowerSpec (reflData b') (reflJumps J') m) EL ∧
    StagedPiecesRegular κ (affData 1 m (reflData b')) (affJumps 1 m (reflJumps J'))
      (condExpKernel P (pastSigma κ b jumps (sspec v l) (E (sspec v l)) k) ω₀)
      (relLowerSpec (reflData b') (reflJumps J') m) EL

end Output

/-- **The setting of the left-walk half** of SB4's distinct-seed leaf (its hypotheses at one switch `k`, with the
retained history on the closed right of the left walk at the launch samples), for a proposition `C` about each
retained launch and each witness of its conditional launch law. -/
def SB2LeftSetting (C : ℝ → (ℝ → ℝ) → Finset ℝ → ∀ {Ω : Type u} [MeasurableSpace Ω]
    [StandardBorelSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P],
    (ExplSpec → ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞) → ℝ → List (ℝ × ℝ≥0) → ℕ → Ω → Chart →
    (ℝ → ℝ) → Finset ℝ → (Ω → DistOn upperHalfPlaneOpens) → Prop) : Prop :=
  ∀ κ : ℝ, 0 < κ → κ < 4 → ∀ (b : ℝ → ℝ) (jumps : Finset ℝ), IsPiecewiseConstantBoundaryData b jumps →
    ∀ {Ω : Type u} [MeasurableSpace Ω] [StandardBorelSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
      (h : Ω → DistOn upperHalfPlaneOpens), IsGFFWithBoundaryData P h b jumps →
    ∀ (W' : ℝ≥0 → Ω → ℝ) (ζ' : Ω → ℝ≥0∞), IsCenteredCounterflowDriver κ P h W' ζ' →
      (∀ᵐ ω ∂P, ζ' ω = ⊤) →
    ∀ E : ExplSpec → ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞,
      (∀ spec : ExplSpec, IsBoundaryContinuedProgram spec.2.2 →
        IsStagedHistory κ b jumps P h spec (E spec)) →
      (∀ spec : ExplSpec, IsBoundaryContinuedProgram spec.2.2 →
        StagedPiecesRegular κ b jumps P spec (E spec)) →
    ∀ (v : ℝ) (l : List (ℝ × ℝ≥0)) (k : ℕ), 0 ≤ v → l.Pairwise (fun p q => p.2 < q.2) →
      (∀ p ∈ l, p.1 ∈ Ico (-(Real.pi / 2)) (Real.pi / 2)) →
      (∀ x ∈ Ioo 0 v, x ∉ jumps → -2 < cumWeightRight κ (b x + Real.pi / 2 * chiC κ)) →
      (∀ᵐ ω ∂P, ω ∈ launchEvent κ b jumps (sspec v l) (E (sspec v l)) k →
        arcPrefix κ b jumps E v l k ω ∩ leftSideOf (leftWalkSet κ b jumps E ω) = ∅) →
      ∀ᵐ ω₀ ∂P, ∀ (c : Chart) (θ : ℝ),
        (ExplState.run κ b jumps (sspec v l) (fun j => E (sspec v l) j ω₀) (k + 1)).2.2.2.1 k = some (c, θ) →
        ∀ (b' : ℝ → ℝ) (J' : Finset ℝ) (h' : Ω → DistOn upperHalfPlaneOpens),
          IsPiecewiseConstantBoundaryData b' J' →
          (∀ ω, IsChartTransport c 1 0 (chiC κ) (h ω) (h' ω)) →
          IsGFFWithBoundaryData (condExpKernel P (pastSigma κ b jumps (sspec v l) (E (sspec v l)) k) ω₀)
            h' b' J' →
          C κ b jumps P E v l k ω₀ c b' J' h'

/-- **Named input: the mirror of SB2(2)** (supplement p. 631, "Use S2, reflected for the second assertion"; p. 634,
"Reflecting gives the upper-walk barrier"), in the reflected chart: for every witness, a translation `m ≤ 0` and a
relative right walk of the reflected field with `IsLeftLaunchOutput`. -/
def SB2LeftLaunchStatement : Prop :=
  SB2LeftSetting.{u} fun κ b jumps _ _ _ P _ E v l k ω₀ c b' J' h' =>
    ∃ (m : ℝ) (EL : ℕ → _ → (ℝ≥0 → ℝ) × ℝ≥0∞), IsLeftLaunchOutput κ b jumps P E v l k ω₀ c b' J' h' m EL

/-- **Named input: the mirror of SB2(2)'s pointwise lift** (as `Lf.SB2LowerTailLiftStatement`, read in the reflected
chart `ρ ∘ c ∘ ρ`): almost surely under the retained kernel, the left walk misses a real point right of `0` and of the
retained history, and the tail of the reflection of every proper parametrization of the left walk from `0`, after its
visit to `−L`, is the reflected chart's boundary image of the relative walk. -/
def SB2LeftTailLiftStatement : Prop :=
  SB2LeftSetting.{u} fun κ b jumps _ _ _ P _ E v l k ω₀ c b' J' h' =>
    ∀ (m : ℝ) (EL : ℕ → _ → (ℝ≥0 → ℝ) × ℝ≥0∞), IsLeftLaunchOutput κ b jumps P E v l k ω₀ c b' J' h' m EL →
      ∀ᵐ ω ∂(condExpKernel P (pastSigma κ b jumps (sspec v l) (E (sspec v l)) k) ω₀),
        (∃ y : ℝ, 0 < y ∧ realMax (arcPrefix κ b jumps E v l k ω₀) < y ∧
            (y : ℂ) ∉ leftWalkSet κ b jumps E ω) ∧
          ∀ βL : ℝ≥0 → ℂ, IsProperCurve βL → βL 0 = 0 → range βL = leftWalkSet κ b jumps E ω →
            IsTailLiftOf (reflChart c) (-realMin (arcPrefix κ b jumps E v l k ω₀)) m (reflectCurve βL)
              (relWalkSet κ (affData 1 m (reflData b')) (affJumps 1 m (reflJumps J')) EL ω)

/-- **The mirror of SB2(2)'s combined output** (ruling R104a), read in the reflected chart: an output with
`IsLeftLaunchOutput` whose completed left tail lifts (the clauses of `SB2LeftTailLiftStatement` for that output). -/
def LeftLiftOut (κ : ℝ) (b : ℝ → ℝ) (jumps : Finset ℝ) {Ω : Type u} [MeasurableSpace Ω] [StandardBorelSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (E : ExplSpec → ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞) (v : ℝ)
    (l : List (ℝ × ℝ≥0)) (k : ℕ) (ω₀ : Ω) (c : Chart) (b' : ℝ → ℝ) (J' : Finset ℝ)
    (h' : Ω → DistOn upperHalfPlaneOpens) : Prop :=
  ∃ (m : ℝ) (EL : ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞), IsLeftLaunchOutput κ b jumps P E v l k ω₀ c b' J' h' m EL ∧
    ∀ᵐ ω ∂(condExpKernel P (pastSigma κ b jumps (sspec v l) (E (sspec v l)) k) ω₀),
      (∃ y : ℝ, 0 < y ∧ realMax (arcPrefix κ b jumps E v l k ω₀) < y ∧
          (y : ℂ) ∉ leftWalkSet κ b jumps E ω) ∧
        ∀ βL : ℝ≥0 → ℂ, IsProperCurve βL → βL 0 = 0 → range βL = leftWalkSet κ b jumps E ω →
          IsTailLiftOf (reflChart c) (-realMin (arcPrefix κ b jumps E v l k ω₀)) m (reflectCurve βL)
            (relWalkSet κ (affData 1 m (reflData b')) (affJumps 1 m (reflJumps J')) EL ω)

/-- **The mirror of SB2(2) with the lift on its own output** (ruling R104a). Proved from SB2(2)'s combined target by
the reflection symmetry of staged histories: `Lf.sb2LeftLaunchLiftStatement_of_lower` (`SB4RSymLeft.lean`). -/
def SB2LeftLaunchLiftStatement : Prop :=
  SB2LeftSetting.{u} fun κ b jumps _ _ _ P _ E v l k ω₀ c b' J' h' => LeftLiftOut κ b jumps P E v l k ω₀ c b' J' h'

/-- The round-1 pair of mirror inputs gives the combined one. -/
theorem sb2LeftLaunchLiftStatement_of_pair (hSB2L : SB2LeftLaunchStatement.{u})
    (hLiftL : SB2LeftTailLiftStatement.{u}) : SB2LeftLaunchLiftStatement.{u} := by
  intro κ hκ hκ4 b jumps hb Ω _ _ P _ h hh W' ζ' hcf hζ' E hE hER v l k hv hl hθ hR hleft
  filter_upwards [hSB2L κ hκ hκ4 b jumps hb P h hh W' ζ' hcf hζ' E hE hER v l k hv hl hθ hR hleft,
    hLiftL κ hκ hκ4 b jumps hb P h hh W' ζ' hcf hζ' E hE hER v l k hv hl hθ hR hleft] with ω₀ h₀ h₁
  intro c θ hcθ b' J' h' hb' hT' hG'
  obtain ⟨m, EL, hout⟩ := h₀ c θ hcθ b' J' h' hb' hT' hG'
  exact ⟨m, EL, hout, h₁ c θ hcθ b' J' h' hb' hT' hG' m EL hout⟩

/-! ### The reflected word -/

/-- **SB1's bridge hypotheses for the reflected bridge** from the left-walk half's hypotheses on `(0, v)`. -/
theorem bridge_reflect {κ : ℝ} {b : ℝ → ℝ} {jumps : Finset ℝ} {v : ℝ} {l : List (ℝ × ℝ≥0)}
    (hR : ∀ x ∈ Ioo 0 v, x ∉ jumps → -2 < cumWeightRight κ (b x + Real.pi / 2 * chiC κ))
    (hH : ∀ p ∈ l, ∀ x ∈ Ioo 0 v, x ∉ jumps → -2 < cumWeightLeft κ (b x + p.1 * chiC κ) ∨
      κ / 2 - 2 ≤ cumWeightRight κ (b x + Real.pi / 2 * chiC κ)) :
    ∀ p ∈ reflAngles l, ∀ B ∈ bridgeHeights (reflData b) (reflJumps jumps) (-v),
      -2 < cumWeightLeft κ (B + -(Real.pi / 2) * chiC κ) ∧
        (-2 < cumWeightRight κ (B + p.1 * chiC κ) ∨
          κ / 2 - 2 ≤ cumWeightLeft κ (B + -(Real.pi / 2) * chiC κ)) := by
  rintro p hp _ ⟨y, ⟨hy, hyJ⟩, rfl⟩
  have hx : -y ∈ Ioo 0 v := ⟨by linarith [hy.2], by linarith [hy.1]⟩
  have hxJ : -y ∉ jumps := fun h => hyJ (Sec7.FlowReflect.mem_reflJumps.2 h)
  have e1 : reflData b y + -(Real.pi / 2) * chiC κ = -(b (-y) + Real.pi / 2 * chiC κ) := by
    simp only [reflData]; ring
  have e2 : reflData b y + p.1 * chiC κ = -(b (-y) + (-p.1) * chiC κ) := by
    simp only [reflData]; ring
  have hp' := mem_reflAngles.1 hp
  rw [e1, e2, cumWeightLeft_neg, cumWeightRight_neg]
  exact ⟨hR _ hx hxJ, hH _ hp' _ hx hxJ⟩

/-- The reflected bridge's lower left groups are admissible. -/
theorem bridgeLeft_reflect {κ : ℝ} {b : ℝ → ℝ} {jumps : Finset ℝ} {v : ℝ}
    (hR : ∀ x ∈ Ioo 0 v, x ∉ jumps → -2 < cumWeightRight κ (b x + Real.pi / 2 * chiC κ)) :
    ∀ x ∈ Ioo (-v) 0, x ∉ reflJumps jumps →
      -2 < cumWeightLeft κ (reflData b x + -(Real.pi / 2) * chiC κ) := by
  intro y hy hyJ
  have hx : -y ∈ Ioo 0 v := ⟨by linarith [hy.2], by linarith [hy.1]⟩
  have hxJ : -y ∉ jumps := fun h => hyJ (Sec7.FlowReflect.mem_reflJumps.2 h)
  have e1 : reflData b y + -(Real.pi / 2) * chiC κ = -(b (-y) + Real.pi / 2 * chiC κ) := by
    simp only [reflData]; ring
  rw [e1, cumWeightLeft_neg]
  exact hR _ hx hxJ

end InteractingSLE.Theorem14.SB.Lf
