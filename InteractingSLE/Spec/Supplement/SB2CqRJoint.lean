/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.SB2CqHull

/-!
# The line family's sets read as fills, from the walk facts alone (tails and root)

Packet PROVE-SB2-CANON, round 5 (`Mz.CanonIdentOn` at `relOff`). NOJUMP's `Ne.stageSet_first_eq` and
`Ne.stageSet_joint_eq` (and so `fillVer_first_eq`, `fillVer_joint_eq`) are stated at a tail-good sample
(`Nc.StageGoodAt`, which includes `relOff < ℓ` and the tail offset), but use only B's launch at `ℓ`, the agreement of
the regularized runs with the runs, and B's regular launches. **`stageSet_first_eq_of`**, **`stageSet_joint_eq_of`**,
**`fillVer_first_eq_of`**, **`fillVer_joint_eq_of`**, **`union_fillVer_eq_of`** are those statements from these facts
only, so they serve the relative root `ℓ = relOff` as well. The proofs are NOJUMP's.

R48: no source theorem is used.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Filter Topology Metric
open scoped NNReal ENNReal
open QuantumZipper (H Hbar)

namespace InteractingSLE.Theorem14.SB.Cz

open Supp9B Exist Exist.Staged Exist.StagedLaw Sec7.PocketTraversal Sec7.Lemma71C LuM GW1W GW1Bookkeep Lk Dv

variable {κ : ℝ} {b : ℝ → ℝ} {jumps : Finset ℝ} {Ω : Type*} {E : ExplSpec → ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞} {u : ℝ}
  {l : List (ℝ × ℝ≥0)} {k ℓ : ℕ} {ω : Ω}

/-- **The first stage set** (any cap), from B's launch and the run agreements: the retained union in `ℍ`. -/
theorem stageSet_first_eq_of
    (hl : (ExplState.run κ b jumps (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)
      (fun j => E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) j ω) (ℓ + 1)).2.2.2.1 ℓ ≠ none)
    (hrunw : ∀ n, ExplState.run κ b jumps (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)
      (fun j => StagedReg.regFam E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) j ω) n =
      ExplState.run κ b jumps (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)
        (fun j => E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) j ω) n)
    (hrunu : ∀ n, ExplState.run κ b jumps (Lu.upperSpec u l) (fun j => StagedReg.regFam E (Lu.upperSpec u l) j ω) n =
      ExplState.run κ b jumps (Lu.upperSpec u l) (fun j => E (Lu.upperSpec u l) j ω) n) (τ : ℝ≥0∞) :
    WalkLaw.stageSet κ b jumps (Lu.upperSpec u l) (StagedReg.regFam E (Lu.upperSpec u l)) k ω ∪
        WalkLaw.stageSet κ b jumps (WalkSide.capSpec (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) ℓ
          (-(Real.pi / 2)) τ) (StagedReg.regFam E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)) ℓ ω =
      Nc.retX κ b jumps E u l k ℓ ω ∩ H := by
  obtain ⟨-, hlen⟩ := Qx.walk_instr_of_launch hl
  rw [WalkInf.stageSet_capSpec_of_le hlen.le ω le_rfl, Qt.stageSet_eq_prefixPhysSet_inter_H,
    Qt.stageSet_eq_prefixPhysSet_inter_H]
  have hpu : SB.prefixPhysSet κ b jumps (Lu.upperSpec u l) (fun j => StagedReg.regFam E (Lu.upperSpec u l) j ω) k =
      SB.prefixPhysSet κ b jumps (Lu.upperSpec u l) (fun j => E (Lu.upperSpec u l) j ω) k := by
    unfold SB.prefixPhysSet; rw [hrunu k]
  have hpw : SB.prefixPhysSet κ b jumps (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)
      (fun j => StagedReg.regFam E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) j ω) ℓ =
      SB.prefixPhysSet κ b jumps (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)
        (fun j => E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) j ω) ℓ := by
    unfold SB.prefixPhysSet; rw [hrunw ℓ]
  rw [hpu, hpw]
  ext z
  simp only [Nc.retX, upperPrefix, mem_union, mem_inter_iff, mem_image]
  constructor
  · rintro (⟨hz, hzH⟩ | ⟨hz, hzH⟩)
    · exact ⟨Or.inl (Or.inl hz), hzH⟩
    · exact ⟨Or.inr hz, hzH⟩
  · rintro ⟨(hz | ⟨x, -, rfl⟩) | hz, hzH⟩
    · exact Or.inl ⟨hz, hzH⟩
    · exact absurd hzH (by show ¬ 0 < ((x : ℝ) : ℂ).im; simp)
    · exact Or.inr ⟨hz, hzH⟩

/-- **The joint stage set**, capped before B's lifetime, from B's launch, the run agreements and the regular
launches: the retained union and B's piece up to `t`, in `ℍ`. -/
theorem stageSet_joint_eq_of
    (hl : (ExplState.run κ b jumps (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)
      (fun j => E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) j ω) (ℓ + 1)).2.2.2.1 ℓ ≠ none)
    (hrunw : ∀ n, ExplState.run κ b jumps (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)
      (fun j => StagedReg.regFam E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) j ω) n =
      ExplState.run κ b jumps (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)
        (fun j => E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) j ω) n)
    (hrunu : ∀ n, ExplState.run κ b jumps (Lu.upperSpec u l) (fun j => StagedReg.regFam E (Lu.upperSpec u l) j ω) n =
      ExplState.run κ b jumps (Lu.upperSpec u l) (fun j => E (Lu.upperSpec u l) j ω) n)
    (hreg : RegLaunches κ b jumps (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)
      fun j => E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) j ω) {t : ℝ≥0}
    (ht : (t : ℝ≥0∞) < Nc.bLife b jumps E ℓ ω) :
    WalkLaw.stageSet κ b jumps (Lu.upperSpec u l) (StagedReg.regFam E (Lu.upperSpec u l)) k ω ∪
        WalkLaw.stageSet κ b jumps (WalkSide.capSpec (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) ℓ
          (-(Real.pi / 2)) (t : ℝ≥0∞)) (StagedReg.regFam E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true))
          (ℓ + 1) ω =
      (Nc.retX κ b jumps E u l k ℓ ω ∪ Nc.bPc κ b jumps E ℓ ω '' Icc 0 t) ∩ H := by
  rw [Ne.stageSet_capSpec_succ_congr (D' := E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)) hrunw
    (by rw [hrunw (ℓ + 1)]; exact hl) (t : ℝ≥0∞), Ne.stageSet_capSpec_succ_eq hreg hl (t : ℝ≥0∞)]
  have hS : {s : ℝ≥0 | (s : ℝ≥0∞) ≤ min (t : ℝ≥0∞) (E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) ℓ ω).2} =
      Icc 0 t := by
    ext s
    simp only [mem_ofPred_eq, mem_Icc, zero_le, true_and]
    rw [min_eq_left (show (t : ℝ≥0∞) ≤ (E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) ℓ ω).2 from ht.le),
      ENNReal.coe_le_coe]
  have h1 := stageSet_first_eq_of (k := k) hl hrunw hrunu (0 : ℝ≥0∞)
  rw [WalkInf.stageSet_capSpec_of_le (Qx.walk_instr_of_launch hl).2.le ω le_rfl] at h1
  have hw : WalkLaw.stageSet κ b jumps (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)
      (E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)) ℓ ω =
      WalkLaw.stageSet κ b jumps (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)
        (StagedReg.regFam E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)) ℓ ω := by
    unfold WalkLaw.stageSet; rw [hrunw ℓ]
  rw [hS, hw, ← union_assoc, h1, ← union_inter_distrib_right]
  rfl

/-- **The union of the line family's sets**, before B's lifetime, is the joint fill (from the walk facts alone). -/
theorem union_fillVer_eq_of
    (hl : (ExplState.run κ b jumps (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)
      (fun j => E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) j ω) (ℓ + 1)).2.2.2.1 ℓ ≠ none)
    (hrunw : ∀ n, ExplState.run κ b jumps (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)
      (fun j => StagedReg.regFam E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) j ω) n =
      ExplState.run κ b jumps (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)
        (fun j => E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) j ω) n)
    (hrunu : ∀ n, ExplState.run κ b jumps (Lu.upperSpec u l) (fun j => StagedReg.regFam E (Lu.upperSpec u l) j ω) n =
      ExplState.run κ b jumps (Lu.upperSpec u l) (fun j => E (Lu.upperSpec u l) j ω) n)
    (hreg : RegLaunches κ b jumps (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)
      fun j => E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) j ω)
    (hXc : IsCompact (Nc.retX κ b jumps E u l k ℓ ω)) {t : ℝ≥0} (ht : (t : ℝ≥0∞) < Nc.bLife b jumps E ℓ ω)
    {B₁ B₂ : Set ℂ}
    (h₁ : B₁ = Mf.fillVer (fun ω =>
      WalkLaw.stageSet κ b jumps (Lu.upperSpec u l) (StagedReg.regFam E (Lu.upperSpec u l)) k ω ∪
        WalkLaw.stageSet κ b jumps (WalkSide.capSpec (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) ℓ
          (-(Real.pi / 2)) (t : ℝ≥0∞)) (StagedReg.regFam E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)) ℓ ω)
      ω)
    (h₂ : B₂ = Mf.fillVer (fun ω =>
      WalkLaw.stageSet κ b jumps (Lu.upperSpec u l) (StagedReg.regFam E (Lu.upperSpec u l)) k ω ∪
        WalkLaw.stageSet κ b jumps (WalkSide.capSpec (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) ℓ
          (-(Real.pi / 2)) (t : ℝ≥0∞)) (StagedReg.regFam E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true))
          (ℓ + 1) ω) ω) :
    B₁ ∪ B₂ = fillH (Nc.retX κ b jumps E u l k ℓ ω ∪ Nc.bPc κ b jumps E ℓ ω '' Icc 0 t) := by
  have e1 := stageSet_first_eq_of (k := k) hl hrunw hrunu (t : ℝ≥0∞)
  have e2 := stageSet_joint_eq_of (k := k) hl hrunw hrunu hreg ht
  have hcpt : IsCompact (Nc.bPc κ b jumps E ℓ ω '' Icc 0 t) :=
    isCompact_Icc.image_of_continuousOn ((continuousOn_pcPt_launch hreg hl).mono fun s hs =>
      (ENNReal.coe_le_coe.2 hs.2).trans ht.le)
  have hb₁ : Bornology.IsBounded
      (WalkLaw.stageSet κ b jumps (Lu.upperSpec u l) (StagedReg.regFam E (Lu.upperSpec u l)) k ω ∪
        WalkLaw.stageSet κ b jumps (WalkSide.capSpec (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) ℓ
          (-(Real.pi / 2)) (t : ℝ≥0∞)) (StagedReg.regFam E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)) ℓ ω) := by
    rw [e1]; exact hXc.isBounded.subset inter_subset_left
  have hb₂ : Bornology.IsBounded
      (WalkLaw.stageSet κ b jumps (Lu.upperSpec u l) (StagedReg.regFam E (Lu.upperSpec u l)) k ω ∪
        WalkLaw.stageSet κ b jumps (WalkSide.capSpec (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) ℓ
          (-(Real.pi / 2)) (t : ℝ≥0∞)) (StagedReg.regFam E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true))
          (ℓ + 1) ω) := by
    rw [e2]; exact (hXc.union hcpt).isBounded.subset inter_subset_left
  rw [h₁, h₂]
  simp only [Mf.fillVer, hb₁, hb₂, ↓reduceIte]
  rw [e1, e2, Qx.fillH_closure, Qx.fillH_closure, Sec7.SideHeight.fillH_inter_H, Sec7.SideHeight.fillH_inter_H]
  exact union_eq_right.2 (fillH_mono subset_union_left)

/-- **The first set of the line family** is the fill of the retained union (any cap), from the walk facts alone. -/
theorem fillVer_first_eq_of
    (hl : (ExplState.run κ b jumps (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)
      (fun j => E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) j ω) (ℓ + 1)).2.2.2.1 ℓ ≠ none)
    (hrunw : ∀ n, ExplState.run κ b jumps (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)
      (fun j => StagedReg.regFam E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) j ω) n =
      ExplState.run κ b jumps (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)
        (fun j => E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) j ω) n)
    (hrunu : ∀ n, ExplState.run κ b jumps (Lu.upperSpec u l) (fun j => StagedReg.regFam E (Lu.upperSpec u l) j ω) n =
      ExplState.run κ b jumps (Lu.upperSpec u l) (fun j => E (Lu.upperSpec u l) j ω) n)
    (hXc : IsCompact (Nc.retX κ b jumps E u l k ℓ ω)) (τ : ℝ≥0∞) :
    Mf.fillVer (fun ω =>
      WalkLaw.stageSet κ b jumps (Lu.upperSpec u l) (StagedReg.regFam E (Lu.upperSpec u l)) k ω ∪
        WalkLaw.stageSet κ b jumps (WalkSide.capSpec (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) ℓ
          (-(Real.pi / 2)) τ) (StagedReg.regFam E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)) ℓ ω) ω =
      fillH (Nc.retX κ b jumps E u l k ℓ ω) := by
  have e1 := stageSet_first_eq_of (k := k) hl hrunw hrunu τ
  have hb : Bornology.IsBounded
      (WalkLaw.stageSet κ b jumps (Lu.upperSpec u l) (StagedReg.regFam E (Lu.upperSpec u l)) k ω ∪
        WalkLaw.stageSet κ b jumps (WalkSide.capSpec (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) ℓ
          (-(Real.pi / 2)) τ) (StagedReg.regFam E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)) ℓ ω) := by
    rw [e1]; exact hXc.isBounded.subset inter_subset_left
  simp only [Mf.fillVer, hb, ↓reduceIte]
  rw [e1, Qx.fillH_closure, Sec7.SideHeight.fillH_inter_H]

end InteractingSLE.Theorem14.SB.Cz
