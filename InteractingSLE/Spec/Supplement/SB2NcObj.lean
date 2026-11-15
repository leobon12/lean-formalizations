/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.SB2NcRpt

/-!
# F2b′'s relative stage curve at a sample

Packet PROVE-AUX61-NOJUMP (round 21, D34, component B). B's piece at stage `ℓ` (`bPc`, B's own time) with lifetime
`bLife`; its image under the chart `Mo.hullChart (fillH K) x₀`, in B's time (`bLift`, `Dv.canonVal`) and reparametrized
onto `[0, ∞)` (`bRel`, `Dv.canonCurve`).

* **`exists_entry_driven`** (deterministic, at a sample with the walk facts and a tail launch): the canonical stage
  curve of the retained union is driven for the right entry value (`isDrivenCurve_walkStage_old_entry`);
* **`entryRead_retX_eq`**: the entry read of the retained union at B's point is that entry value;
* **`bRel_driven`**: hence, for a hull `K` with the same fill and `x₀` the entry read at B's point, `bRel` is driven.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Filter Set Topology
open scoped NNReal ENNReal
open QuantumZipper (H Hbar)

namespace InteractingSLE.Theorem14.SB.Nc

open Sec7.PocketTraversal Sec7.Lemma71C Lk LuM GW1Bookkeep Exist Exist.Staged Exist.StagedLaw GW1Conn Dv Mz

section Defs

variable (κ : ℝ) (b : ℝ → ℝ) (jumps : Finset ℝ) {Ω : Type*} (E : ExplSpec → ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞) (ℓ : ℕ)

/-- **B's piece at stage `ℓ`**, in B's own time. -/
def bPc (ω : Ω) : ℝ≥0 → ℂ :=
  pcPt (ExplState.run κ b jumps (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)
    (fun i => E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) i ω) ℓ)
    (E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) ℓ ω)

/-- **B's lifetime at stage `ℓ`.** -/
def bLife (ω : Ω) : ℝ≥0∞ := (E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) ℓ ω).2

/-- **B's lift** through the chart `Mo.hullChart (fillH K) x₀`, in B's time. -/
def bLift (K : Ω → Set ℂ) (x₀ : Ω → ℝ) (ω : Ω) : ℝ≥0 → ℂ :=
  canonVal (K ω) (x₀ ω) (bPc κ b jumps E ℓ ω) (bLife b jumps E ℓ ω)

/-- **The relative stage curve** on `[0, ∞)`. -/
def bRel (K : Ω → Set ℂ) (x₀ : Ω → ℝ) (ω : Ω) : ℝ → ℂ :=
  canonCurve (K ω) (x₀ ω) (bPc κ b jumps E ℓ ω) (bLife b jumps E ℓ ω)

end Defs

variable {κ : ℝ} {b : ℝ → ℝ} {jumps : Finset ℝ} {Ω : Type*} {E : ExplSpec → ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞} {u : ℝ}
  {l : List (ℝ × ℝ≥0)} {k ℓ : ℕ} {ω : Ω}

/-- **The canonical stage curve of the retained union is driven for the right entry value.** -/
theorem exists_entry_driven (hg : WalkGood κ b jumps E u l k ω)
    (hl : (ExplState.run κ b jumps (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)
      (fun j => E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) j ω) (ℓ + 1)).2.2.2.1 ℓ ≠ none)
    (hpos : bLife b jumps E ℓ ω ≠ 0)
    (hoff : relOff κ (-(Real.pi / 2)) b jumps (realMax (upperPrefix κ b jumps E u l k ω))
      (fun i => E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) i ω) < ℓ) :
    ∃ e : ℝ, IsRightEntryChart (retX κ b jumps E u l k ℓ ω) (realMax (retX κ b jumps E u l k ℓ ω))
        ((Mo.hullChart (fillH (retX κ b jumps E u l k ℓ ω)) 0).recenter e) ∧
      IsDrivenCurve (canonCurve (retX κ b jumps E u l k ℓ ω) e (bPc κ b jumps E ℓ ω) (bLife b jumps E ℓ ω)) := by
  classical
  have hev := even_of_launch hl
  have hre := relOff_even κ (-(Real.pi / 2)) b jumps (realMax (upperPrefix κ b jumps E u l k ω))
    (fun i => E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) i ω)
  obtain ⟨hro, e', he', hent⟩ := relOffEvent_of_walkGood hg
  have hge : e' + 1 ≤ ℓ := by omega
  set θ : ℝ := -(Real.pi / 2) with hθ
  set w := boundaryWalkSpec b jumps θ true with hw
  set D : ℕ → (ℝ≥0 → ℝ) × ℝ≥0∞ := fun i => E w i ω with hDdef
  have hR : ((realMax (upperPrefix κ b jumps E u l k ω) : ℝ) : ℂ) ∈
      statePhysicalSet 0 (ExplState.run κ b jumps w D ℓ) :=
    statePhysicalSet_mono (κ := κ) (θ := θ) (b := b) (jumps := jumps) (D := D) hge hent
  obtain ⟨pA, hpc, hp0, hpH, hpv, hpA⟩ := hg.upath
  obtain ⟨β, hβ, hβ0, hβr, hS1, hS3⟩ := hg.proper
  obtain ⟨⟨c₀, θ₀⟩, hl'⟩ := Option.ne_none_iff_exists'.1 hl
  have hnd := WalkIntRunChron.not_done_of_launch _ _ hl'
  have h := isDrivenCurve_walkStage_old_entry hg.reg hg.chain hg.noLeftMove hg.noLeftHit hl hpos
    (hg.pinv ℓ hnd).1 hpc hp0 hpH hpv hβ hβ0 hβr (by rw [hpA]; exact hS1) (by rw [hpA]; exact hR)
    (by rw [hpA]; exact hS3)
  rw [hpA] at h
  exact h

/-- **The entry read of the retained union at B's point is its right entry value.** -/
theorem entryRead_retX_eq (hg : WalkGood κ b jumps E u l k ω)
    (hl : (ExplState.run κ b jumps (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)
      (fun j => E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) j ω) (ℓ + 1)).2.2.2.1 ℓ ≠ none)
    (hoff : relOff κ (-(Real.pi / 2)) b jumps (realMax (upperPrefix κ b jumps E u l k ω))
      (fun i => E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) i ω) < ℓ) {e : ℝ}
    (hrc : IsRightEntryChart (retX κ b jumps E u l k ℓ ω) (realMax (retX κ b jumps E u l k ℓ ω))
      ((Mo.hullChart (fillH (retX κ b jumps E u l k ℓ ω)) 0).recenter e)) :
    entryRead (fillH (retX κ b jumps E u l k ℓ ω))
      (stPt (ExplState.run κ b jumps (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)
        (fun j => E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) j ω) ℓ)) = e := by
  rw [← realMax_retX_eq hg hl hoff (even_of_launch hl)]
  obtain ⟨p, hpc, hp0, -, -, hp⟩ := exists_path_retX hg hl
  have hA : IsHPHull (fillH (retX κ b jumps E u l k ℓ ω)) := by rw [← hp]; exact isHPHull_fillH_path hpc hp0
  exact entryRead_eq (isCompact_retX hg hl) hA hrc

/-- **The relative stage curve is driven**, for a hull with the retained union's fill and the offset read at B's
point. -/
theorem bRel_driven (hg : WalkGood κ b jumps E u l k ω)
    (hl : (ExplState.run κ b jumps (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)
      (fun j => E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) j ω) (ℓ + 1)).2.2.2.1 ℓ ≠ none)
    (hpos : bLife b jumps E ℓ ω ≠ 0)
    (hoff : relOff κ (-(Real.pi / 2)) b jumps (realMax (upperPrefix κ b jumps E u l k ω))
      (fun i => E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) i ω) < ℓ)
    {K : Ω → Set ℂ} {x₀ : Ω → ℝ} (hK : fillH (K ω) = fillH (retX κ b jumps E u l k ℓ ω))
    (hx : x₀ ω = entryRead (fillH (K ω))
      (stPt (ExplState.run κ b jumps (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)
        (fun j => E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) j ω) ℓ))) :
    IsDrivenCurve (bRel κ b jumps E ℓ K x₀ ω) ∧
      IsRightEntryChart (retX κ b jumps E u l k ℓ ω) (realMax (retX κ b jumps E u l k ℓ ω))
        ((Mo.hullChart (fillH (retX κ b jumps E u l k ℓ ω)) 0).recenter (x₀ ω)) := by
  obtain ⟨e, hrc, hdr⟩ := exists_entry_driven hg hl hpos hoff
  have hxe : x₀ ω = e := by rw [hx, hK]; exact entryRead_retX_eq hg hl hoff hrc
  refine ⟨?_, hxe ▸ hrc⟩
  unfold bRel
  rw [canonCurve_congr_fill hK, hxe]
  exact hdr

end InteractingSLE.Theorem14.SB.Nc
