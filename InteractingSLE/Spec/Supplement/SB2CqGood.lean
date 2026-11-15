/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.SB2NcData
import InteractingSLE.Spec.Supplement.SB2NcWalk
import InteractingSLE.Spec.Supplement.SB2NcGeo
import InteractingSLE.Spec.Supplement.SB2NcObj

/-!
# NOJUMP's good sample for a successor statement's offset

Packet PROVE-SB2-CANON, round 5 ((P4)). **`ae_stageGoodAt_retX`**: on the live event `F` of a successor statement
(`Cz.SB2LowerStageVersionStatement6`: `F` = stage event ∩ {`relOff < ℓ`} ∩ {B's lifetime positive} almost surely,
and the offset `x₀` is the right entry value of the retained union `X = A ∪ B_{<ℓ}`), almost every sample is good in
NOJUMP's sense (`Nc.StageGoodAt`) for the hull `X` itself, the offset `x₀` and the family `Ê = E` (which agrees with
itself): the walk facts (`Nc.ae_walkGood`), the geometry of `X` (`Nc.ae_retGeom`), the regularized runs
(`StagedReg.regFam_spec`), the offset identity `x₀ = entryRead (fill X) (B's point)` (`Nc.entryRead_retX_eq`) and the
drivenness of the canonical curve (`Nc.bRel_driven`).

R48: Theorems 1.2–1.3 appear only as hypotheses (Theorem 1.4).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal
open QuantumZipper (H Hbar chiC)
open LQGMetric (DistOn)

universe u

namespace InteractingSLE.Theorem14.SB.Cz

open Restart Exist Exist.Staged Exist.StagedLaw Lv Ms Mf Supp8.Q3Stop WalkSide LocalSets Sec7.PocketTraversal Lk LuM

/-- **Almost every sample of the live event is good** for the retained union, the entry offset and `Ê = E`. -/
theorem ae_stageGoodAt_retX (h12 : Theorem12Statement.{u}) (h13 : Theorem13Statement.{u})
    (h12₀ : Theorem12Statement.{0}) (h13₀ : Theorem13Statement.{0}) {κ : ℝ} (hκ : 0 < κ) (hκ4 : κ < 4)
    {b : ℝ → ℝ} {jumps : Finset ℝ} (hb : IsPiecewiseConstantBoundaryData b jumps) {Ω : Type u}
    [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {h : Ω → DistOn upperHalfPlaneOpens} (hh : IsGFFWithBoundaryData P h b jumps) {W' : ℝ≥0 → Ω → ℝ}
    {ζ' : Ω → ℝ≥0∞} (hcf : IsCenteredCounterflowDriver κ P h W' ζ') (hζ' : ∀ᵐ ω ∂P, ζ' ω = ⊤)
    {E : ExplSpec → ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞}
    (hE : ∀ spec : ExplSpec, IsBoundaryContinuedProgram spec.2.2 → IsStagedHistory κ b jumps P h spec (E spec))
    (hER : ∀ spec : ExplSpec, IsBoundaryContinuedProgram spec.2.2 → StagedPiecesRegular κ b jumps P spec (E spec))
    {u : ℝ} {l : List (ℝ × ℝ≥0)} (hu : u ≤ 0) (hlθ : ∀ p ∈ l, p.1 ∈ Ioc (-(Real.pi / 2)) (Real.pi / 2)) (k ℓ : ℕ)
    (hleft : ∀ᵐ ω ∂P, ω ∈ Lu.upperLaunchSet κ b jumps E u l k →
      upperPrefix κ b jumps E u l k ω ∩ rightSideOf (lowerWalkSet κ b jumps E ω) = ∅)
    (hℓ : ℓ < (boundaryWalkSpec b jumps (-(Real.pi / 2)) true).2.2.length) {F : Set Ω} {x₀ : Ω → ℝ}
    (hFae : ∀ᵐ ω ∂P, ω ∈ F → (ω ∈ stageEvent κ b jumps E u l k ℓ ∧
      relOff κ (-(Real.pi / 2)) b jumps (realMax (upperPrefix κ b jumps E u l k ω))
        (fun i => E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) i ω) < ℓ ∧
      0 < (E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) ℓ ω).2))
    (hent : ∀ᵐ ω ∂P, ω ∈ F → IsRightEntryChart (Nc.retX κ b jumps E u l k ℓ ω)
      (realMax (Nc.retX κ b jumps E u l k ℓ ω))
      ((Mo.hullChart (fillH (Nc.retX κ b jumps E u l k ℓ ω)) 0).recenter (x₀ ω))) :
    ∀ᵐ ω ∂P, ω ∈ F → Nc.StageGoodAt κ b jumps E u l k ℓ (Nc.retX κ b jumps E u l k ℓ) x₀
      (fun j ω => E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) j ω) ω := by
  obtain ⟨-, -, hrun'⟩ := StagedReg.regFam_spec hb hE hER
  have hw : IsBoundaryContinuedProgram (boundaryWalkSpec b jumps (-(Real.pi / 2)) true).2.2 :=
    isBoundaryContinuedProgram_boundaryWalkSpec b jumps ⟨le_rfl, by linarith [Real.pi_pos]⟩ true
  have hsu : IsBoundaryContinuedProgram (Lu.upperSpec u l).2.2 := Lu.isBoundaryContinuedProgram_upperSpec hlθ
  have hgood := Nc.ae_walkGood h12 h13 h12₀ h13₀ hκ hκ4 hb hh hcf hζ' hE hER hu hlθ k hleft
  have hgeo := Nc.ae_retGeom h13 h13₀ hκ hκ4 hb hh hcf hζ' hE hER hu hlθ k ℓ hℓ
  filter_upwards [hFae, hent, hgood, hgeo, hrun' _ hw, hrun' _ hsu] with ω h1 h2 h3 h4 h5 h6 hωF
  obtain ⟨hst, hoff, hpos⟩ := h1 hωF
  have hg := h3 hst.1
  obtain ⟨hc, hH, -, hhull, hsf⟩ := h4 hst.2
  have hpos' : Nc.bLife b jumps E ℓ ω ≠ 0 := pos_iff_ne_zero.1 hpos
  have hx0 : x₀ ω = Nc.entryRead (fillH (Nc.retX κ b jumps E u l k ℓ ω))
      (stPt (ExplState.run κ b jumps (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)
        (fun j => E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) j ω) ℓ)) :=
    (Nc.entryRead_retX_eq hg hst.2 hoff (h2 hωF)).symm
  obtain ⟨hdr, hent'⟩ := Nc.bRel_driven hg hst.2 hpos' hoff (K := Nc.retX κ b jumps E u l k ℓ) rfl hx0
  exact ⟨hg, hst, hoff, hpos', rfl, hc, hH, hhull, hsf, h5, h6, ⟨fun _ => rfl, fun _ => rfl, fun _ _ => rfl⟩, hx0,
    hdr, hent'⟩

end InteractingSLE.Theorem14.SB.Cz
