/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.SB2NfRelStmt

/-!
# F2b′'s root: the relative facts at a sample, PROVED (D77 item 3)

Packet PROVE-T14-SB2LIFT (round 35, decision D77 item 3: the separable piece PROVE-AUX61-NOJUMP names for SB2LIFT).

* **`rootRelFactsStatement`**: NOJUMP's `Nf.RootRelFactsStatement` (`SB2NfRelStmt`), deterministic.

The proof is the root analogue of NOJUMP's tail `Ne.relFacts_of_good`: `Ne.relFactsAt_of` and `Ne.endpoint_bad` with
the piece `p = rPc` (B's piece read from its entrance at `R = max (A ∩ ℝ)`), `L = rLife`, `X = retX`, `x₀ = x`. The
root-specific steps:

* B's record `R_B = stRecR (run ℓ) = stPt (run ℓ)` lies in the retained union, so `R_B ≤ realMax retX = R`; hence
  `origBadR R ⊆ origBadR R_B` (only the side condition `R < ·` differs);
* `R` is off the closed bad set: if `R_B = R` this is the physical fact at B's record; if `R_B < R`, it is the
  avoidance fact at the entrance time `rSh` (B's piece is at `R` there);
* the avoidance for `rPc t = bPc (rSh + t)` is B's avoidance at `rSh + t`;
* at a finite lifetime, `rPc` ends at B's endpoint, a bad point right of `R_B`. It lies right of `R` by the end-right
  fact (at `sh = rSh`, `R' = R`) when `R_B < R`, and trivially when `R_B = R`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Filter Set Topology Metric
open scoped NNReal ENNReal
open QuantumZipper (H Hbar)

universe u

namespace InteractingSLE.Theorem14.SB.Sx

open Vs Exist.StagedLaw Supp8.GB6 Supp8.GB6.HullId Supp8.GB6.RelDrv.Version Supp8.Q3Stop Sec7.PocketTraversal
  Sec7.Lemma71C Restart Exist Exist.Staged Lv Ms Mf WalkSide LocalSets Lk LuM Nc Dv Nd
open _root_.InteractingSLE.Theorem14.SB.Ne _root_.InteractingSLE.Theorem14.SB.Nf

/-- **F2b′'s root relative facts at a sample, PROVED** (NOJUMP's `Nf.RootRelFactsStatement`). -/
theorem rootRelFactsStatement : RootRelFactsStatement.{u} := by
  intro κ b jumps Ω E u l k ℓ ω hκ _hκ4 hb hg hl x G β hH cw types hcw htype hRD hrun hphys hendR
  set w := boundaryWalkSpec b jumps (-(Real.pi / 2)) true with hw
  set D : ℕ → (ℝ≥0 → ℝ) × ℝ≥0∞ := fun j => StagedReg.regFam E w j ω with hD
  set D' : ℕ → (ℝ≥0 → ℝ) × ℝ≥0∞ := fun j => E w j ω with hD'
  set X := retX κ b jumps E u l k ℓ ω with hX
  set R := realMax (upperPrefix κ b jumps E u l k ω) with hRdef
  set sh := rSh κ b jumps E u l k ℓ ω with hsh
  have hlD : (ExplState.run κ b jumps w D (ℓ + 1)).2.2.2.1 ℓ ≠ none := by rw [hrun (ℓ + 1)]; exact hl
  have hRE : GW1P.PieceRegular (D' ℓ).1 (D' ℓ).2 := pieceRegular_of_launch hg.reg hl
  obtain ⟨hLeq, hpeq⟩ := pcPt_eq_of_runs hrun hlD hRD hRE
  obtain ⟨hpt, hRnot, hav, hend⟩ := hphys
  set RB := stRecR (ExplState.run κ b jumps w D ℓ) with hRB
  -- B's record lies left of the seed
  have hXc : IsCompact X := isCompact_retX hg hl
  have hRBle : RB ≤ R := by
    have h1 : stPt (ExplState.run κ b jumps w D' ℓ) ≤ realMax X := Lx.le_realMax_of_mem hXc G.stpt
    rw [G.rmax, ← hrun ℓ, hpt] at h1
    exact h1
  have hcl : closure (origBadR κ b R) ⊆ closure (origBadR κ b RB) :=
    closure_mono fun y hy => ⟨lt_of_le_of_lt hRBle hy.1, hy.2⟩
  have hshD : ((sh : ℝ≥0) : ℝ≥0∞) < (D ℓ).2 := by rw [hLeq]; exact G.shlt
  have hvisD : pcPt (ExplState.run κ b jumps w D ℓ) (D ℓ) sh = ((R : ℝ) : ℂ) := by
    rw [hpeq _ hshD.le]; exact G.visit
  -- the seed is off the closed bad set
  have hRnot' : R ∉ closure (origBadR κ b R) := by
    rcases eq_or_lt_of_le hRBle with heq | hlt
    · rw [← heq]; exact hRnot
    · exact fun hmem => hav sh hshD R hvisD hlt (hcl hmem)
  -- the avoidance of the relative piece
  have hav' : ∀ t : ℝ≥0, (t : ℝ≥0∞) < rLife κ b jumps E u l k ℓ ω → ∀ y : ℝ,
      rPc κ b jumps E u l k ℓ ω t = y → R < y → y ∉ closure (origBadR κ b R) := by
    intro t ht y hy hRy hmem
    have hst : ((sh + t : ℝ≥0) : ℝ≥0∞) < (D ℓ).2 := by
      rw [hLeq, ENNReal.coe_add]
      exact lt_tsub_iff_left.1 ht
    exact hav _ hst y (by rw [hpeq _ hst.le]; exact hy) (lt_of_le_of_lt hRBle hRy) (hcl hmem)
  -- the endpoint of the relative piece
  have hend' : rLife κ b jumps E u l k ℓ ω ≠ ⊤ → ∃ y : ℝ,
      rPc κ b jumps E u l k ℓ ω (rLife κ b jumps E u l k ℓ ω).toNNReal = y ∧ y ∈ origBadR κ b R := by
    intro htop
    have hr : rLife κ b jumps E u l k ℓ ω = (D ℓ).2 - (sh : ℝ≥0∞) := by
      show bLife b jumps E ℓ ω - _ = _
      rw [hLeq]; rfl
    have hbt : (D ℓ).2 ≠ ⊤ := fun h => htop (by rw [hr, h]; exact ENNReal.top_sub_coe)
    obtain ⟨y, hy, hyb⟩ := hend hbt
    have hsum : sh + (rLife κ b jumps E u l k ℓ ω).toNNReal = (D ℓ).2.toNNReal := by
      rw [hr]
      apply ENNReal.coe_injective
      rw [ENNReal.coe_add, ENNReal.coe_toNNReal (ENNReal.sub_ne_top hbt), ENNReal.coe_toNNReal hbt,
        add_tsub_cancel_of_le hshD.le]
    refine ⟨y, ?_, ⟨?_, hyb.2⟩⟩
    · show pcPt (ExplState.run κ b jumps w D' ℓ) (D' ℓ) (sh + (rLife κ b jumps E u l k ℓ ω).toNNReal) = y
      rw [hsum, ← hpeq _ ENNReal.coe_toNNReal_le_self]
      exact hy
    · rcases eq_or_lt_of_le hRBle with heq | hlt
      · rw [← heq]; exact hyb.1
      · exact hendR sh R hshD hlt hvisD hbt y hy hyb
  -- the continuity of the relative piece
  have hpc : ContinuousOn (rPc κ b jumps E u l k ℓ ω) {t : ℝ≥0 | (t : ℝ≥0∞) ≤ rLife κ b jumps E u l k ℓ ω} := by
    have hc := continuousOn_pcPt_launch hg.reg hl
    refine hc.comp (continuous_const.add continuous_id).continuousOn fun t ht => ?_
    show ((sh + t : ℝ≥0) : ℝ≥0∞) ≤ (D' ℓ).2
    rw [ENNReal.coe_add]
    exact add_le_of_le_tsub_left_of_le G.shlt.le ht
  -- the canonical package of the retained union and D34's clause at the seed
  obtain ⟨pX, hpXc, hpX0, hpXH, hpXv, hpXe⟩ := exists_path_retX hg hl
  have hXA : IsHPHull (fillH X) := by
    show IsHPHull (fillH (retX κ b jumps E u l k ℓ ω))
    rw [← hpXe]; exact isHPHull_fillH_path hpXc hpX0
  obtain ⟨e₀, g, -, hgc, hgi, hgt, -, -⟩ := Dv.exists_canon_package_pinv hpXc hpX0 hpXH hpXv
  rw [hpXe] at hgi hgt
  obtain ⟨C, hC⟩ := Lk.hullChart_ext_bounded hXA hgt
  have hfree : ∀ y : ℝ, R < y → ∃ r > 0, Disjoint (ball (y : ℂ) r) (fillH X) := fun y hy =>
    ball_disjoint_fillH_right hXc fun z hz => lt_of_le_of_lt (Lx.le_realMax_of_mem hXc hz) (by rw [G.rmax]; exact hy)
  obtain ⟨e, he, hreal, hmono, ⟨Fy, hFy⟩, hleft⟩ := hH g hgc hgi
  have hxe : x = e := entry_eq hXA hgc hgi G.entry hfree he hreal hmono
  rw [← hxe] at he hreal hmono hFy hleft
  have hcell : ω ∈ wordTypeCell κ (-(Real.pi / 2)) cw univ (angleWordType κ (-(Real.pi / 2)) (cw ω)) :=
    ⟨trivial, rfl⟩
  have hft0 := Restart.FCDet.isFlowType_of_mem_typeSet (mem_typeSet_of_mem_wordTypeCell hcell)
  have hft : Restart.FCDet.IsFlowType κ (-(Real.pi / 2)) (BoundaryWord.shiftW x β)
      (cellXL κ (-(Real.pi / 2)) cw (angleWordType κ (-(Real.pi / 2)) (cw ω)) ω)
      (cellXR κ (-(Real.pi / 2)) cw (angleWordType κ (-(Real.pi / 2)) (cw ω)) ω)
      (typedRhoL (angleWordType κ (-(Real.pi / 2)) (cw ω))) (typedRhoR (angleWordType κ (-(Real.pi / 2)) (cw ω))) := by
    rw [← hcw]; exact hft0
  exact ⟨relFactsAt_of hκ hb hXA G.pos hpc G.driven hgc hgi hC he hreal hmono hFy hleft hfree hRnot' hav' hend'
    G.captop hcw htype, fun hfin => endpoint_bad hκ hb hXA G.pos hpc G.driven hgc hgi hC he hreal hmono hFy hft hfree
    hend' G.captop hfin⟩

end InteractingSLE.Theorem14.SB.Sx
