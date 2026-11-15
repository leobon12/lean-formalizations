/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.SBLyLeaf
import InteractingSLE.Spec.Supplement.SBS3DxSBLyGen

/-!
# Relative SB3 instances with the upper angle `ψ ≤ π/2` (decision D22, ruling R121)

Worker PROVE-R6-CORNER (round 8). D22 adds `ψ ≤ π/2` to the angle clause of the relative SB3 instances:

* **`Leaf.IsRelSB3InstanceLe`**: `Leaf.IsRelSB3Instance` with `ψ ≤ π/2`; **`Ly.IsRelSB3InstanceRLe`**: the same for
  `Ly.IsRelSB3InstanceR` (R95's premise);
* **`Leaf.isRelSB3Instance_of_wordLe`**: SB4's word paragraph with the two-sided angle hypothesis
  `∀ p ∈ l, p.1 ∈ Ioc (−π/2) (π/2)` (the instance's angle is a schedule angle);
* **`Ly.ae_isOneSided_of_relSB3InstanceRLe`**: the amended SB3 with the bound (`Ly.SB3InductionGenRLeStatement`,
  `SBS3DxSBLyGen`) applied to such an instance (the proof of `Ly.ae_isOneSided_of_relSB3InstanceR`).

Consumer check (D22): every caller of `Leaf.isRelSB3Instance_of_word` takes `ψ = q.1` for a schedule angle `q ∈ l`
with `q.1 ∈ Ioc (−π/2) (π/2)`; at the mirrored caller (`Lf.scheduleRelativeTailR_left_lift`, list `reflAngles l`)
the original angles are in `Ico (−π/2) (π/2)` (its `hθ`), so the reflected angles `−p.1` are in `Ioc (−π/2) (π/2)`:
the upper bound `−p.1 ≤ π/2` is `(hθ _ _).1`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal
open QuantumZipper (chiC H)
open LQGMetric (DistOn)

universe u

namespace InteractingSLE.Theorem14.SB.Leaf

open Sec4

/-- **A relative SB3 instance with the upper angle `ψ ≤ π/2`** (D22). -/
def IsRelSB3InstanceLe (κ : ℝ) {Ω : Type u} [MeasurableSpace Ω] [StandardBorelSpace Ω]
    (Q : Measure Ω) [IsProbabilityMeasure Q] (hQ : Ω → DistOn upperHalfPlaneOpens)
    (b' : ℝ → ℝ) (jumps' : Finset ℝ) (EL : ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞) (u' ψ : ℝ)
    (η : Ω → ℝ≥0 → ℂ) (ζ : Ω → ℝ≥0∞) : Prop :=
  IsRelSB3Instance κ Q hQ b' jumps' EL u' ψ η ζ ∧ ψ ≤ Real.pi / 2

/-- **SB4's word paragraph with two-sided angles**: under `ψ_j ∈ (−π/2, π/2]`, `|ψ_i − ψ_j| < 2λ/χ` and the bridge
hypothesis, the classified relative pair is an SB3 instance with the bound. -/
theorem isRelSB3Instance_of_wordLe {κ : ℝ} (hκ : 0 < κ) (hκ4 : κ < 4) {Ω : Type u}
    [MeasurableSpace Ω] [StandardBorelSpace Ω] {Q : Measure Ω} [IsProbabilityMeasure Q]
    {hQ : Ω → DistOn upperHalfPlaneOpens} {b' : ℝ → ℝ} {jumps' : Finset ℝ}
    {EL : ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞} {u' ψ : ℝ} {η : Ω → ℝ≥0 → ℂ} {ζ : Ω → ℝ≥0∞}
    {l : List (ℝ × ℝ≥0)} {original : Set ℝ}
    (hangles : ∀ p ∈ l, p.1 ∈ Ioc (-(Real.pi / 2)) (Real.pi / 2))
    (hgaps : ∀ p ∈ l, ∀ q ∈ l, |p.1 - q.1| < 2 * sleLambda κ / chiC κ)
    (hbridge : ∀ p ∈ l, ∀ B ∈ original,
      -2 < cumWeightLeft κ (B + -(Real.pi / 2) * chiC κ) ∧
        (-2 < cumWeightRight κ (B + p.1 * chiC κ) ∨
          κ / 2 - 2 ≤ cumWeightLeft κ (B + -(Real.pi / 2) * chiC κ)))
    (hW : IsRelSB3WordInstance κ Q hQ b' jumps' EL u' ψ η ζ l original) :
    IsRelSB3InstanceLe κ Q hQ b' jumps' EL u' ψ η ζ := by
  refine ⟨isRelSB3Instance_of_word hκ hκ4 (fun p hp => (hangles p hp).1) hgaps hbridge hW, ?_⟩
  obtain ⟨-, -, -, -, ⟨q, hq, rfl⟩, -⟩ := hW
  exact (hangles q hq).2

end InteractingSLE.Theorem14.SB.Leaf

namespace InteractingSLE.Theorem14.SB.Ly

open Sec4 Leaf

/-- **`Ly.IsRelSB3InstanceR` with the upper angle `ψ ≤ π/2`** (D22). -/
def IsRelSB3InstanceRLe (κ : ℝ) {Ω : Type u} [MeasurableSpace Ω] [StandardBorelSpace Ω]
    (Q : Measure Ω) [IsProbabilityMeasure Q] (hQ : Ω → DistOn upperHalfPlaneOpens)
    (b' : ℝ → ℝ) (jumps' : Finset ℝ) (EL : ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞) (u' ψ : ℝ)
    (η : Ω → ℝ≥0 → ℂ) (ζ : Ω → ℝ≥0∞) : Prop :=
  IsRelSB3InstanceR κ Q hQ b' jumps' EL u' ψ η ζ ∧ ψ ≤ Real.pi / 2

/-- **The amended SB3 with the bound applied to a relative instance with the bound** (the proof of
`ae_isOneSided_of_relSB3InstanceR`). -/
theorem ae_isOneSided_of_relSB3InstanceRLe (hSB3 : SB3InductionGenRLeStatement.{u})
    (h12 : Exist.Theorem12Statement.{u}) (h13 : Exist.Theorem13Statement.{u})
    {κ : ℝ} (hκ : 0 < κ) (hκ4 : κ < 4) {Ω : Type u} [MeasurableSpace Ω] [StandardBorelSpace Ω]
    {Q : Measure Ω} [IsProbabilityMeasure Q] {hQ : Ω → DistOn upperHalfPlaneOpens}
    {b' : ℝ → ℝ} {jumps' : Finset ℝ} {EL : ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞} {u' ψ : ℝ}
    {η : Ω → ℝ≥0 → ℂ} {ζ : Ω → ℝ≥0∞}
    (hI : IsRelSB3InstanceRLe κ Q hQ b' jumps' EL u' ψ η ζ) :
    ∀ᵐ ω ∂Q, ∀ γ : ℝ≥0 → ℂ, Supp9B.IsProperCurve γ → γ 0 = 0 →
      range γ = relWalkSet κ b' jumps' EL ω →
      ∀ s a : ℝ≥0, (a : ℝ≥0∞) ≤ ζ ω →
        IsOneSided (γ '' Icc 0 s ∪ ((↑) : ℝ → ℂ) '' Icc u' 0) (η ω) a := by
  classical
  obtain ⟨⟨⟨hb, hh, hL, hu, hψ, hA, hH, hη, hζ⟩, hadm⟩, hψle⟩ := hI
  have : Fact (ψ ≤ Real.pi / 2) := ⟨hψle⟩
  obtain ⟨E₀, hE₀⟩ :=
    Exist.StagedLaw.exists_isStagedHistory_regular_of_thm12_thm13 h12 h13 hκ hκ4 hb hh
  have hE : ∀ spec : ExplSpec, IsBoundaryContinuedProgram spec.2.2 →
      IsStagedHistory κ b' jumps' Q hQ spec
          (Function.update E₀ (boundaryWalkSpec b' jumps' (-(Real.pi / 2)) true) EL spec) ∧
        StagedPiecesRegular κ b' jumps' Q spec
          (Function.update E₀ (boundaryWalkSpec b' jumps' (-(Real.pi / 2)) true) EL spec) := by
    intro spec hspec
    by_cases hs : spec = boundaryWalkSpec b' jumps' (-(Real.pi / 2)) true
    · subst hs
      rw [Function.update_self]
      exact hL hspec
    · rw [Function.update_of_ne hs]
      exact hE₀ spec hspec
  have hS := hSB3 κ hκ hκ4 b' jumps' hb Q hQ hh hadm
    (Function.update E₀ (boundaryWalkSpec b' jumps' (-(Real.pi / 2)) true) EL)
    (fun s hs => (hE s hs).1) (fun s hs => (hE s hs).2) u' ψ hu hψ hA hH η ζ hη hζ
  filter_upwards [hS] with ω hω γ hγ hγ0 hr
  exact hω γ hγ hγ0 (by rw [lowerWalkSet_update]; exact hr)

end InteractingSLE.Theorem14.SB.Ly
