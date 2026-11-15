/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.SB2KdInputs
import InteractingSLE.Spec.Supplement.SBLuAmb

/-!
# SB2(1)'s retained lower prefix is a finite-fibre path, without the counterflow

Packet PROVE-T14-SB2DRV (round 2). S2's relative chain (`FinRel.exists_relConfig_of_path_of_finite`) needs the
retained lower-walk prefix with its bridge as the image of a continuous path with finite fibres. In the ambient setting
of `SB2DriverLinkAmbStatement` (no counterflow; `Ly.LowerLeftAdmissible`) this is PROVE-T14-SBLEAVES6's
`LuM.sb3StagePathRStatement` proof route (`LuM.pinv_prefix_walk` with `LuM.ae_walkTipCoordinates_lower`, which needs
only the left ambient bound, and `LuM.ae_injOn_trOf_walk`, Aux. lemma 25 under the conditional laws). Restated here
for an SB2(1) launch problem at the launch `k + 1` (no flow-line or positive-lifetime binder):

* **`ae_isPrefixPath_launch`**.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal
open QuantumZipper (chiC)
open LQGMetric (DistOn)

universe u

namespace InteractingSLE.Theorem14.SB.Lv

open Exist.Staged Exist.StagedLaw

/-- **The retained lower prefix with its bridge is a finite-fibre path from the upper seed**, almost surely at the
launch `k + 1` of an SB2(1) problem (ambient setting, no counterflow). -/
theorem ae_isPrefixPath_launch {κ : ℝ} {b : ℝ → ℝ} {jumps : Finset ℝ} {Ω : Type u} [MeasurableSpace Ω]
    [StandardBorelSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P] {h : Ω → DistOn upperHalfPlaneOpens}
    {E : ExplSpec → ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞} {k : ℕ} {u ψ : ℝ} {η : Ω → ℝ≥0 → ℂ} {ζ : Ω → ℝ≥0∞}
    (H : SB2LaunchProblem κ b jumps P h E k u ψ η ζ) :
    ∀ᵐ ω ∂P, ω ∈ launchSet κ b jumps E (k + 1) →
      ∃ p : ℝ → ℂ, Lx.IsPrefixPath p u (lowerPrefix κ b jumps E (k + 1) u ω) := by
  have hspec := isBoundaryContinuedProgram_boundaryWalkSpec b jumps (θ := -(Real.pi / 2))
    ⟨le_rfl, by linarith [Real.pi_pos]⟩ true
  have hS := H.staged _ hspec
  have hRs := H.pieces_regular _ hspec
  filter_upwards [LuM.ae_walkTipCoordinates_lower H.kappa_pos H.boundary H.field H.admissible hS
      (H.drivers_regular _) hRs,
    ae_all_iff.2 fun j => LuM.ae_injOn_trOf_walk H.kappa_pos H.kappa_lt_four H.boundary hS
      (H.drivers_regular _) hRs j, hRs.ae_pieceRegular]
    with ω htip hinj hr hl
  have hP : LuM.RegLaunches κ b jumps (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)
      (fun j => E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) j ω) := fun j c θ' hlj => hr j c θ' hlj
  obtain ⟨⟨c, θ'⟩, hcθ⟩ := Option.ne_none_iff_exists'.1 hl
  have hnot := WalkIntRunChron.not_done_of_launch _ _ hcθ
  obtain ⟨hpinv, -⟩ := LuM.pinv_prefix_walk hP (fun j hlj => hinj j hlj) htip H.seed_nonpos (k + 1) hnot
  rcases hpinv with h1 | h2
  · exfalso
    have hne := Lz.prefixPhysSet_ne_root_of_launch (κ := κ) (b := b) (jumps := jumps)
      (fun j => E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) j ω) (by omega) hl
    have h0 : (0 : ℂ) ∈ SB.prefixPhysSet κ b jumps (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)
        (fun j => E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) j ω) (k + 1) :=
      Or.inl (Or.inl (by simp [boundaryWalkSpec]))
    have hsub : SB.prefixPhysSet κ b jumps (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)
        (fun j => E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) j ω) (k + 1) ⊆ {(u : ℂ)} :=
      h1 ▸ subset_union_left
    have hu0 : (u : ℂ) = 0 := (mem_singleton_iff.1 (hsub h0)).symm
    refine hne (Subset.antisymm ?_ ?_)
    · simpa [boundaryWalkSpec, hu0] using hsub
    · simpa [boundaryWalkSpec] using h0
  · exact h2

end InteractingSLE.Theorem14.SB.Lv
