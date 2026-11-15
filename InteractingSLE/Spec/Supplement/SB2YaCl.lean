/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.SB2YaStart
import InteractingSLE.Spec.Supplement.SB2XyAsm

/-!
# The start disjunction of the corrected bundle at one sample

Packet PROVE-T14-SB2LIFT (round 31; item 4). **`clauseTW_sample`**: at one sample, from the actual walk's facts
(GW1's run exit data, regular launches, chain facts, no left moves or hits, positive later lifetimes, allowed
statuses, completion, right hits), the ray correspondence with its continuity, the lift curve and the upper chart,
the relative family's regularity, per-stage facts `StageFactsAll` and root facts `RootFactsAt` (LIFTSET, D25), the
good-time density at the later actual stages and the piece lifts `PiecesLift2`: the start disjunction of
`Mn.ClauseTW` at the offset `relOff` —
* at a zero root, or off it at a zero shifted lifetime (the corner): `ArcStart` (`arcStart_of_zeroRoot`,
  `arcStart_of_corner`) with the run inputs (`Mn.runInputs_of_lifts`);
* otherwise `PieceStartV` (`pieceStartV_of`), with the run inputs when the start piece is finite.
Deterministic.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Filter Topology
open scoped NNReal ENNReal
open QuantumZipper (H Hbar chiC)

namespace InteractingSLE.Theorem14.SB.Lk

open Supp9B Exist Exist.Staged Exist.StagedLaw LuM GW1W GW1Bookkeep
open PiecewiseConstantBoundaryData (rightLim leftLim jumpSet)

variable {κ θ : ℝ} {b₁ b₂ : ℝ → ℝ} {J₁ J₂ : Finset ℝ} {R : ℝ} {ι : ℝ → ℝ} {D₁ D₂ : ℕ → Drv}
  {β₀ γ : ℝ≥0 → ℂ} {tL : ℝ≥0} {c : Chart} {m : ℝ} {A : Set ℂ}

/-- **The start disjunction of `Mn.ClauseTW` at `relOff`, at one sample.** -/
theorem clauseTW_sample (hb : IsPiecewiseConstantBoundaryData b₁ J₁) (hX : RunExitData κ b₁ J₁ θ D₁)
    (hP₁ : RegLaunches κ b₁ J₁ (boundaryWalkSpec b₁ J₁ θ true) D₁) (hW₁ : WalkChainFacts κ b₁ J₁ θ D₁)
    (hlm₁ : ∀ j, NoLeftMove κ b₁ J₁ θ D₁ j) (hlh₁ : ∀ j, NoLeftHit κ b₁ J₁ θ D₁ j)
    (hposW : ∀ n, 0 < n → (ExplState.run κ b₁ J₁ (boundaryWalkSpec b₁ J₁ θ true) D₁ (n + 1)).2.2.2.1 n ≠ none →
      (D₁ n).2 ≠ 0)
    (hallow : ∀ n, 1 ≤ n → AllowedSt κ b₁ (ExplState.run κ b₁ J₁ (boundaryWalkSpec b₁ J₁ θ true) D₁ n))
    (hdone : stStatus (ExplState.run κ b₁ J₁ (boundaryWalkSpec b₁ J₁ θ true) D₁
      (boundaryWalkSpec b₁ J₁ θ true).2.2.length) = stDone)
    (hRH : ∀ n, (ExplState.run κ b₁ J₁ (boundaryWalkSpec b₁ J₁ θ true) D₁ (n + 1)).2.2.2.1 n ≠ none →
      (D₁ n).2 ≠ ⊤ → (D₁ n).2 ≠ 0 → ∃ x : ℝ, stRecR (ExplState.run κ b₁ J₁ (boundaryWalkSpec b₁ J₁ θ true) D₁ n) < x ∧
        lHit (stChart (ExplState.run κ b₁ J₁ (boundaryWalkSpec b₁ J₁ θ true) D₁ n)) ⊤ (D₁ n) x)
    (hι : RayCorr b₁ J₁ b₂ J₂ R ι) (hcont : ContinuousOn ι (Ici R)) (hD : LiftCurveData β₀ γ tL R ι)
    (hγ : IsTailLiftCurve c R m β₀ tL γ) (hβ : IsProperCurve β₀) (hβ0 : β₀ 0 = 0)
    (hβr : range β₀ = ExplState.physSet κ b₁ J₁ (boundaryWalkSpec b₁ J₁ θ true) D₁) (hU : UpperChartOK c)
    (hK : β₀ '' Icc 0 tL ⊆ hullK A) (hDom : c.2.1 '' H = H \ fillH A)
    (hhead : ∀ t ≤ tL, ∀ x : ℝ, β₀ t = x → x ≤ R) (hreg₂ : ∀ j, IsRegularDriver (D₂ j))
    (hSF : Mn.StageFactsAll κ θ b₁ J₁ b₂ J₂ R c m A D₁ D₂)
    (hgd : ∀ i, 2 ≤ i →
      (ExplState.run κ b₁ J₁ (boundaryWalkSpec b₁ J₁ θ true) D₁ (i + relOff κ θ b₁ J₁ R D₁ + 1)).2.2.2.1
        (i + relOff κ θ b₁ J₁ R D₁) ≠ none →
      {t : ℝ≥0 | (t : ℝ≥0∞) < (D₁ (i + relOff κ θ b₁ J₁ R D₁)).2} ⊆
        closure (goodT c (ExplState.run κ b₁ J₁ (boundaryWalkSpec b₁ J₁ θ true) D₁ (i + relOff κ θ b₁ J₁ R D₁))
          (D₁ (i + relOff κ θ b₁ J₁ R D₁))))
    (hRF : RootFactsAt κ θ b₁ J₁ b₂ J₂ R c m D₁ D₂) (hPL : PiecesLift2 κ θ b₁ J₁ b₂ J₂ R D₁ D₂ β₀ γ tL) :
    (∃ N : ℕ, RunInputs'' κ θ b₁ J₁ b₂ J₂ R ι D₁ D₂ β₀ γ tL (relOff κ θ b₁ J₁ R D₁) N ∧
        (ArcStart κ θ b₁ J₁ R D₁ D₂ β₀ tL (relOff κ θ b₁ J₁ R D₁) ∨
          PieceStartV κ θ b₁ J₁ b₂ J₂ R ι D₁ D₂ β₀ γ tL (relOff κ θ b₁ J₁ R D₁))) ∨
      (PieceStartV κ θ b₁ J₁ b₂ J₂ R ι D₁ D₂ β₀ γ tL (relOff κ θ b₁ J₁ R D₁) ∧
        (D₁ (relOff κ θ b₁ J₁ R D₁)).2 = ⊤) := by
  have hP₂ : RegLaunches κ b₂ J₂ (boundaryWalkSpec b₂ J₂ θ true) D₂ :=
    Mn.regLaunches_of_facts hreg₂ (fun j hl hz => (hSF j hl hz).1.2.2.2.2.2.2)
  have hrun : ∀ hS : ArcStart κ θ b₁ J₁ R D₁ D₂ β₀ tL (relOff κ θ b₁ J₁ R D₁) ∨
      (PieceStartV κ θ b₁ J₁ b₂ J₂ R ι D₁ D₂ β₀ γ tL (relOff κ θ b₁ J₁ R D₁) ∧
        (D₁ (relOff κ θ b₁ J₁ R D₁)).2 ≠ ⊤),
      ∃ N : ℕ, RunInputs'' κ θ b₁ J₁ b₂ J₂ R ι D₁ D₂ β₀ γ tL (relOff κ θ b₁ J₁ R D₁) N := fun hS =>
    Mn.runInputs_of_lifts hι hcont hP₁ hW₁ hlm₁ hlh₁ hdone hS hPL.1 hreg₂ hSF hgd hγ hU hK hDom hβ hβr hγ.2.1
  by_cases hZ : ZeroRoot κ θ b₁ J₁ R D₁
  · have hA := arcStart_of_zeroRoot hb hX hP₁ hW₁ hlm₁ hlh₁ hposW hallow hdone hβ hβ0 hβr hγ.1 hZ (hreg₂ 0)
      (hRF.1 (Or.inl hZ))
    obtain ⟨N, hN⟩ := hrun (Or.inl hA)
    exact Or.inl ⟨N, hN, Or.inl hA⟩
  by_cases hL0 : (D₁ (relOff κ θ b₁ J₁ R D₁)).2 - shiftD κ θ b₁ J₁ R D₁ 0 = 0
  · have hA := arcStart_of_corner hb hX hP₁ hW₁ hlm₁ hlh₁ hposW hallow hdone hRH hβ hβ0 hβr hγ.1 hZ hL0
      (hreg₂ 0) (hRF.1 (Or.inr hL0))
    obtain ⟨N, hN⟩ := hrun (Or.inl hA)
    exact Or.inl ⟨N, hN, Or.inl hA⟩
  have hV := pieceStartV_of hb hX hP₁ hW₁ hlm₁ hlh₁ hposW hallow hdone hRH hι hD hγ hβ hβ0 hβr hU hK hDom hhead
    hZ hL0 hP₂ (hreg₂ 0) hRF hPL
  by_cases htop : (D₁ (relOff κ θ b₁ J₁ R D₁)).2 = ⊤
  · exact Or.inr ⟨hV, htop⟩
  · obtain ⟨N, hN⟩ := hrun (Or.inr ⟨hV, htop⟩)
    exact Or.inl ⟨N, hN, Or.inr hV⟩

end InteractingSLE.Theorem14.SB.Lk
