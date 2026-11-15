/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.SB2NfObj
import InteractingSLE.Spec.Supplement.SB2NeHullV

/-!
# F2b′'s root: the stage sets and the joint fill at a root sample

Packet PROVE-AUX61-NOJUMP (round 22, the root variant). At a B-time-0 good sample of the root (`Root0At`):

* `stageSet_first_eq₀`, `stageSet_joint_eq₀`: the stage sets of the line family are the retained union and B's piece
  up to `t`, in `ℍ` (`Ne.stageSet_first_eq`, `Ne.stageSet_joint_eq` for `Root0At`);
* `hullK_mono`: the compact hull `K_X` increases with `X`;
* **`fillH_retX_bPc_eq`**: with B's head before the entrance inside `K_A` (`RootGeo.head`), the joint fill at B-time
  `t` is the fill of the retained union and the relative piece up to `t − rSh`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology Metric
open scoped NNReal ENNReal
open QuantumZipper (H Hbar fwdHull)

universe u

namespace InteractingSLE.Theorem14.SB.Nf

open Supp9B Exist Exist.Staged Exist.StagedLaw Sec7.PocketTraversal Sec7.Lemma71C LuM GW1W GW1Bookkeep Lk Dv Ne
  WalkSide

variable {κ θ : ℝ} {b : ℝ → ℝ} {jumps : Finset ℝ}

section Good

variable {Ω : Type u} {E : ExplSpec → ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞} {u : ℝ} {l : List (ℝ × ℝ≥0)} {k ℓ : ℕ}
  {K : Ω → Set ℂ} {x₀ : Ω → ℝ} {Ê : ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞} {ω : Ω}

theorem launch_regFam₀ (hg : Root0At κ b jumps E u l k ℓ K x₀ Ê ω) :
    (ExplState.run κ b jumps (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)
      (fun j => StagedReg.regFam E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) j ω) (ℓ + 1)).2.2.2.1 ℓ ≠
        none := by
  rw [hg.runw (ℓ + 1)]; exact hg.stage.2

theorem continuousOn_bPc₀ (hg : Root0At κ b jumps E u l k ℓ K x₀ Ê ω) :
    ContinuousOn (Nc.bPc κ b jumps E ℓ ω) {t : ℝ≥0 | (t : ℝ≥0∞) ≤ Nc.bLife b jumps E ℓ ω} :=
  continuousOn_pcPt_launch hg.walk.reg hg.stage.2

/-- **The first stage set at a good sample** (any cap): the retained union in `ℍ`. -/
theorem stageSet_first_eq₀ (hg : Root0At κ b jumps E u l k ℓ K x₀ Ê ω) (τ : ℝ≥0∞) :
    WalkLaw.stageSet κ b jumps (Lu.upperSpec u l) (StagedReg.regFam E (Lu.upperSpec u l)) k ω ∪
        WalkLaw.stageSet κ b jumps (capSpec (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) ℓ (-(Real.pi / 2)) τ)
          (StagedReg.regFam E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)) ℓ ω =
      Nc.retX κ b jumps E u l k ℓ ω ∩ H := by
  obtain ⟨-, hlen⟩ := Qx.walk_instr_of_launch hg.stage.2
  rw [WalkInf.stageSet_capSpec_of_le hlen.le ω le_rfl, Qt.stageSet_eq_prefixPhysSet_inter_H,
    Qt.stageSet_eq_prefixPhysSet_inter_H]
  have hpu : SB.prefixPhysSet κ b jumps (Lu.upperSpec u l) (fun j => StagedReg.regFam E (Lu.upperSpec u l) j ω) k =
      SB.prefixPhysSet κ b jumps (Lu.upperSpec u l) (fun j => E (Lu.upperSpec u l) j ω) k := by
    unfold SB.prefixPhysSet; rw [hg.runu k]
  have hpw : SB.prefixPhysSet κ b jumps (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)
      (fun j => StagedReg.regFam E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) j ω) ℓ =
      SB.prefixPhysSet κ b jumps (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)
        (fun j => E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) j ω) ℓ := by
    unfold SB.prefixPhysSet; rw [hg.runw ℓ]
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

/-- **The joint stage set at a good sample**, capped before B's lifetime: the retained union and B's piece up to `t`,
in `ℍ`. -/
theorem stageSet_joint_eq₀ (hg : Root0At κ b jumps E u l k ℓ K x₀ Ê ω) {t : ℝ≥0}
    (ht : (t : ℝ≥0∞) < Nc.bLife b jumps E ℓ ω) :
    WalkLaw.stageSet κ b jumps (Lu.upperSpec u l) (StagedReg.regFam E (Lu.upperSpec u l)) k ω ∪
        WalkLaw.stageSet κ b jumps (capSpec (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) ℓ (-(Real.pi / 2))
          (t : ℝ≥0∞)) (StagedReg.regFam E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)) (ℓ + 1) ω =
      (Nc.retX κ b jumps E u l k ℓ ω ∪ Nc.bPc κ b jumps E ℓ ω '' Icc 0 t) ∩ H := by
  rw [stageSet_capSpec_succ_congr (D' := E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)) hg.runw
    (launch_regFam₀ hg) (t : ℝ≥0∞), stageSet_capSpec_succ_eq hg.walk.reg hg.stage.2 (t : ℝ≥0∞)]
  have hS : {s : ℝ≥0 | (s : ℝ≥0∞) ≤ min (t : ℝ≥0∞) (E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) ℓ ω).2} =
      Icc 0 t := by
    ext s
    simp only [mem_setOf_eq, mem_Icc, zero_le, true_and]
    rw [min_eq_left (show (t : ℝ≥0∞) ≤ (E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) ℓ ω).2 from ht.le),
      ENNReal.coe_le_coe]
  have h1 := stageSet_first_eq₀ hg (0 : ℝ≥0∞)
  rw [WalkInf.stageSet_capSpec_of_le (Qx.walk_instr_of_launch hg.stage.2).2.le ω le_rfl] at h1
  have hw : WalkLaw.stageSet κ b jumps (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)
      (E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)) ℓ ω =
      WalkLaw.stageSet κ b jumps (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)
        (StagedReg.regFam E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)) ℓ ω := by
    unfold WalkLaw.stageSet; rw [hg.runw ℓ]
  rw [hS, hw, ← union_assoc, h1, ← union_inter_distrib_right]
  rfl

/-- The real points of a compact set are bounded. -/
theorem bdd_real_of_isCompact {X : Set ℂ} (hX : IsCompact X) :
    BddAbove {x : ℝ | (x : ℂ) ∈ X} ∧ BddBelow {x : ℝ | (x : ℂ) ∈ X} := by
  obtain ⟨C, hC⟩ := hX.isBounded.exists_norm_le
  refine ⟨⟨C, fun x hx => ?_⟩, ⟨-C, fun x hx => ?_⟩⟩
  · have := hC _ hx; rw [Complex.norm_real, Real.norm_eq_abs] at this; exact (le_abs_self x).trans this
  · have := hC _ hx; rw [Complex.norm_real, Real.norm_eq_abs] at this; linarith [neg_abs_le x]

/-- **The compact hull increases with the set.** -/
theorem hullK_mono {X X' : Set ℂ} (hX' : IsCompact X') (hXX' : X ⊆ X') {x : ℝ} (hx : (x : ℂ) ∈ X) :
    hullK X ⊆ hullK X' := by
  have hne : ({y : ℝ | (y : ℂ) ∈ X}).Nonempty := ⟨x, hx⟩
  have hsub : {y : ℝ | (y : ℂ) ∈ X} ⊆ {y : ℝ | (y : ℂ) ∈ X'} := fun y hy => hXX' hy
  obtain ⟨hA, hB⟩ := bdd_real_of_isCompact hX'
  rintro z (hz | ⟨y, hy, rfl⟩)
  · exact Or.inl (fillH_mono hXX' hz)
  · refine Or.inr ⟨y, ⟨le_trans (csInf_le_csInf hB hne hsub) hy.1, le_trans hy.2 (csSup_le_csSup hA hne hsub)⟩, rfl⟩

/-- B's piece lies in the closed upper half-plane. -/
theorem bPc_im_nonneg (hg : Root0At κ b jumps E u l k ℓ K x₀ Ê ω) {t : ℝ≥0}
    (ht : (t : ℝ≥0∞) ≤ Nc.bLife b jumps E ℓ ω) : 0 ≤ (Nc.bPc κ b jumps E ℓ ω t).im := by
  obtain ⟨β, hβ, -, hβr, -, -⟩ := hg.walk.proper
  have hmem : Nc.bPc κ b jumps E ℓ ω t ∈ range β := by
    rw [hβr]
    have h1 := tipSet_subset_physSet_launch (κ := κ) (b := b) (jumps := jumps) hg.stage.2
    obtain ⟨-, -, -, -, htip⟩ := tipSet_newPc_launch hg.walk.reg hg.stage.2
    exact h1 (by rw [htip]; exact ⟨t, ht, rfl⟩)
  obtain ⟨s, hs⟩ := hmem
  rw [← hs]; exact hβ.2.2.1 s

/-- **The joint fill at a root sample**, through the relative piece. -/
theorem fillH_retX_bPc_eq (hg : Root0At κ b jumps E u l k ℓ K x₀ Ê ω) {x : ℝ}
    (G : RootGeo κ b jumps E u l k ℓ ω x) {t : ℝ≥0} (ht : (t : ℝ≥0∞) < Nc.bLife b jumps E ℓ ω) :
    fillH (Nc.retX κ b jumps E u l k ℓ ω ∪ Nc.bPc κ b jumps E ℓ ω '' Icc 0 t) =
      fillH (Nc.retX κ b jumps E u l k ℓ ω ∪
        rPc κ b jumps E u l k ℓ ω '' Icc 0 (t - rSh κ b jumps E u l k ℓ ω)) := by
  set sh := rSh κ b jumps E u l k ℓ ω with hshdef
  set X := Nc.retX κ b jumps E u l k ℓ ω with hXdef
  set p := Nc.bPc κ b jumps E ℓ ω with hpdef
  have hpc := continuousOn_bPc₀ hg
  have hshL := G.shlt
  have hle : ∀ s : ℝ≥0, s ≤ max t sh → (s : ℝ≥0∞) ≤ Nc.bLife b jumps E ℓ ω := fun s hs =>
    (ENNReal.coe_le_coe.2 hs).trans (by
      rcases le_total t sh with h' | h'
      · rw [max_eq_right h']; exact hshL.le
      · rw [max_eq_left h']; exact ht.le)
  have hcpt : ∀ T : ℝ≥0, T ≤ max t sh → IsCompact (p '' Icc 0 T) := fun T hT =>
    isCompact_Icc.image_of_continuousOn (hpc.mono fun s hs => hle s (hs.2.trans hT))
  have hHn : ∀ T : ℝ≥0, T ≤ max t sh → ∀ z ∈ p '' Icc 0 T, 0 ≤ z.im := by
    rintro T hT _ ⟨s, hs, rfl⟩; exact bPc_im_nonneg hg (hle s (hs.2.trans hT))
  set Y := p '' Icc 0 sh with hYdef
  have hR : ((realMax (upperPrefix κ b jumps E u l k ω) : ℝ) : ℂ) ∈ X := by
    obtain ⟨pA, hpAc, hp0, -, -, hpA⟩ := hg.walk.upath
    have hAc : IsCompact (upperPrefix κ b jumps E u l k ω) := hpA ▸ isCompact_Icc.image_of_continuousOn hpAc
    exact Or.inl (Nc.realMax_mem hAc (x := 0) (by rw [← hpA]; exact ⟨0, ⟨le_rfl, zero_le_one⟩, by rw [hp0]; simp⟩))
  have hY : Y ⊆ hullK X := by
    rintro _ ⟨s, hs, rfl⟩
    refine hullK_mono hg.retc subset_union_left (x := realMax (upperPrefix κ b jumps E u l k ω)) ?_ (G.head s hs.2)
    obtain ⟨pA, hpAc, hp0, -, -, hpA⟩ := hg.walk.upath
    have hAc : IsCompact (upperPrefix κ b jumps E u l k ω) := hpA ▸ isCompact_Icc.image_of_continuousOn hpAc
    exact Nc.realMax_mem hAc (x := 0) (by rw [← hpA]; exact ⟨0, ⟨le_rfl, zero_le_one⟩, by rw [hp0]; simp⟩)
  -- adding the head changes no fill
  have hadd : ∀ Z : Set ℂ, IsCompact Z → (∀ z ∈ Z, 0 ≤ z.im) → fillH (X ∪ Z) = fillH (X ∪ Z ∪ Y) := by
    intro Z hZ hZH
    refine (Dv.fillH_union_of_subset_hullK (hg.retc.union hZ) ?_ ?_).symm
    · rintro z (hz | hz)
      · exact hg.retH z hz
      · exact hZH z hz
    · exact hY.trans (hullK_mono (hg.retc.union hZ) subset_union_left hR)
  have hrP : rPc κ b jumps E u l k ℓ ω '' Icc 0 (t - sh) = p '' Icc sh (sh + (t - sh)) := by
    ext z
    constructor
    · rintro ⟨s, hs, rfl⟩
      exact ⟨sh + s, ⟨le_self_add, add_le_add le_rfl hs.2⟩, rfl⟩
    · rintro ⟨s, hs, rfl⟩
      refine ⟨s - sh, ⟨bot_le, tsub_le_iff_left.2 hs.2⟩, ?_⟩
      show p (sh + (s - sh)) = p s
      rw [add_tsub_cancel_of_le hs.1]
  have hmax : sh + (t - sh) = max t sh := by
    rcases le_total t sh with h' | h'
    · rw [tsub_eq_zero_of_le h', add_zero, max_eq_right h']
    · rw [add_tsub_cancel_of_le h', max_eq_left h']
  have hunion : p '' Icc 0 t ∪ Y = rPc κ b jumps E u l k ℓ ω '' Icc 0 (t - sh) ∪ Y := by
    rw [hrP, hmax]
    ext z
    constructor
    · rintro (⟨s, hs, rfl⟩ | hz)
      · rcases le_total s sh with h' | h'
        · exact Or.inr ⟨s, ⟨bot_le, h'⟩, rfl⟩
        · exact Or.inl ⟨s, ⟨h', hs.2.trans (le_max_left _ _)⟩, rfl⟩
      · exact Or.inr hz
    · rintro (⟨s, hs, rfl⟩ | hz)
      · by_cases h' : s ≤ t
        · exact Or.inl ⟨s, ⟨bot_le, h'⟩, rfl⟩
        · exact Or.inr ⟨s, ⟨bot_le, (le_max_iff.1 hs.2).resolve_left h'⟩, rfl⟩
      · exact Or.inr hz
  have hZ1 := hcpt t (le_max_left _ _)
  have h1H := hHn t (le_max_left _ _)
  have hZ2 : IsCompact (rPc κ b jumps E u l k ℓ ω '' Icc 0 (t - sh)) := by
    rw [hrP, hmax]
    exact isCompact_Icc.image_of_continuousOn (hpc.mono fun s hs => hle s hs.2)
  have hZ2H : ∀ z ∈ rPc κ b jumps E u l k ℓ ω '' Icc 0 (t - sh), 0 ≤ z.im := by
    rw [hrP, hmax]
    rintro _ ⟨s, hs, rfl⟩
    exact bPc_im_nonneg hg (hle s hs.2)
  rw [hadd _ hZ1 h1H, union_assoc, hunion, ← union_assoc, ← hadd _ hZ2 hZ2H]

end Good

end InteractingSLE.Theorem14.SB.Nf
