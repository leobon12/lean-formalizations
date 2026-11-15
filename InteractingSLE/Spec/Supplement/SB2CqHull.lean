/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.SB2CwHull
import InteractingSLE.Spec.Supplement.SB2NeHullV
import InteractingSLE.Spec.Supplement.SB2QxVer
import InteractingSLE.Spec.Supplement.SB2MfFill
import InteractingSLE.Spec.Sec7.SideHeightRange

/-!
# The versions' hull at a B-time is the canonical curve's filled prefix

Packet PROVE-SB2-CANON, round 5 ((P4): the hull input `hhull` of `ident_canon_at`).

* **`fwdHull_eq_canon_of_hull`** (deterministic): if at a B-time `t < L` the complement of the joint fill
  `fill (Y ∪ p[0, t])` is the canonical chart's inverse image of the complement of the hull `fwdHull W a` (the
  versions' hull clause), then `fwdHull W a = fill ρ[0, uOf t]` for the canonical curve `ρ = canonCurve Y x₀ p L`
  (NOJUMP's `Ne.H_diff_fillH_union_canon` at `U = uOf t`, whose B-time is `cTime (uOf t) = t`, and injectivity of the
  inverse chart on `ℍ`).
* **`fillVer_first_eq`**, **`fillVer_joint_eq`** (at a good sample, `Nc.StageGoodAt`): the line family's sets read as
  fills, `A₁ t = fill X` and `A₂ t = fill (X ∪ p[0, t])` for `t` before B's lifetime (`X` the retained union; NOJUMP's
  `Ne.stageSet_first_eq`, `Ne.stageSet_joint_eq`), so `A₁ t ∪ A₂ t = fill (X ∪ p[0, t])` (**`union_fillVer_eq`**).

R48: no source theorem is used.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Filter Topology Metric
open scoped NNReal ENNReal
open QuantumZipper (H Hbar fwdHull)

namespace InteractingSLE.Theorem14.SB.Cz

open Sec7.PocketTraversal Sec7.Lemma71C Dv Exist Exist.Staged Exist.StagedLaw Lk

section Det

variable {Y : Set ℂ} {x₀ : ℝ} {p : ℝ≥0 → ℂ} {L : ℝ≥0∞}

/-- A B-time before the lifetime is before `L` in `Nc.BeforeL`'s sense. -/
theorem beforeL_of_lt {t : ℝ≥0} (ht : (t : ℝ≥0∞) < L) : Nc.BeforeL L (t : ℝ) := by
  refine ⟨t.coe_nonneg, ?_⟩
  by_cases hL : L = ⊤
  · exact Or.inl hL
  · right
    have h := ENNReal.toReal_strict_mono hL ht
    rwa [ENNReal.coe_toReal] at h

/-- **The versions' hull is the canonical curve's filled prefix** (deterministic). -/
theorem fwdHull_eq_canon_of_hull (hYc : IsCompact Y) (hA : IsHPHull (fillH Y)) (hL : L ≠ 0)
    (hpc : ContinuousOn p {t | (t : ℝ≥0∞) ≤ L}) (hdr : IsDrivenCurve (canonCurve Y x₀ p L)) {t : ℝ≥0}
    (ht : (t : ℝ≥0∞) < L) {W : ℝ → ℝ} {a : ℝ}
    (hH : H \ fillH (Y ∪ p '' Icc 0 t) = (Mo.hullChart (fillH Y) x₀).2.1 '' (H \ fwdHull W a)) :
    fwdHull W a = fillH (canonCurve Y x₀ p L '' Icc 0 (Nc.uOf L t)) := by
  have hbt := beforeL_of_lt ht
  have hc : Nc.cTime L (Nc.uOf L t) = t := by rw [Nc.cTime_uOf hbt, Real.toNNReal_coe]
  have hid := Ne.H_diff_fillH_union_canon hYc hA hL hpc hdr (Nc.uOf_nonneg hbt) (x₀ := x₀)
  rw [hc, hH] at hid
  have hinj : InjOn (Mo.hullChart (fillH Y) x₀).2.1 H := fun v hv w hw hvw => by
    rw [← hullChart_fwd_inv hA x₀ hv, hvw, hullChart_fwd_inv hA x₀ hw]
  have h2 := (hinj.image_eq_image_iff sdiff_subset sdiff_subset).1 hid
  exact Qx.eq_of_H_diff_eq (fun z hz => hz.1) (fun z hz => hz.1) h2

end Det

section Good

variable {κ : ℝ} {b : ℝ → ℝ} {jumps : Finset ℝ} {Ω : Type*} {E : ExplSpec → ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞} {u : ℝ}
  {l : List (ℝ × ℝ≥0)} {k ℓ : ℕ} {K : Ω → Set ℂ} {x₀ : Ω → ℝ} {Ê : ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞} {ω : Ω}

/-- **The first set of the line family at a good sample** is the fill of the retained union (any cap). -/
theorem fillVer_first_eq (hg : Nc.StageGoodAt κ b jumps E u l k ℓ K x₀ Ê ω) (τ : ℝ≥0∞) :
    Mf.fillVer (fun ω =>
      WalkLaw.stageSet κ b jumps (Lu.upperSpec u l) (StagedReg.regFam E (Lu.upperSpec u l)) k ω ∪
        WalkLaw.stageSet κ b jumps (WalkSide.capSpec (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) ℓ
          (-(Real.pi / 2)) τ) (StagedReg.regFam E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)) ℓ ω) ω =
      fillH (Nc.retX κ b jumps E u l k ℓ ω) := by
  have e1 := Ne.stageSet_first_eq hg τ
  have hb : Bornology.IsBounded
      (WalkLaw.stageSet κ b jumps (Lu.upperSpec u l) (StagedReg.regFam E (Lu.upperSpec u l)) k ω ∪
        WalkLaw.stageSet κ b jumps (WalkSide.capSpec (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) ℓ
          (-(Real.pi / 2)) τ) (StagedReg.regFam E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)) ℓ ω) := by
    rw [e1]; exact hg.retc.isBounded.subset inter_subset_left
  simp only [Mf.fillVer, hb, ↓reduceIte]
  rw [e1, Qx.fillH_closure, Sec7.SideHeight.fillH_inter_H]

/-- **The second set of the line family at a good sample**, before B's lifetime, is the joint fill of the retained
union and B's piece. -/
theorem fillVer_joint_eq (hg : Nc.StageGoodAt κ b jumps E u l k ℓ K x₀ Ê ω) {t : ℝ≥0}
    (ht : (t : ℝ≥0∞) < Nc.bLife b jumps E ℓ ω) :
    Mf.fillVer (fun ω =>
      WalkLaw.stageSet κ b jumps (Lu.upperSpec u l) (StagedReg.regFam E (Lu.upperSpec u l)) k ω ∪
        WalkLaw.stageSet κ b jumps (WalkSide.capSpec (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) ℓ
          (-(Real.pi / 2)) (t : ℝ≥0∞)) (StagedReg.regFam E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true))
          (ℓ + 1) ω) ω =
      fillH (Nc.retX κ b jumps E u l k ℓ ω ∪ Nc.bPc κ b jumps E ℓ ω '' Icc 0 t) := by
  have e2 := Ne.stageSet_joint_eq hg ht
  have hcpt : IsCompact (Nc.bPc κ b jumps E ℓ ω '' Icc 0 t) :=
    isCompact_Icc.image_of_continuousOn ((Ne.continuousOn_bPc hg).mono fun s hs =>
      (ENNReal.coe_le_coe.2 hs.2).trans ht.le)
  have hb : Bornology.IsBounded
      (WalkLaw.stageSet κ b jumps (Lu.upperSpec u l) (StagedReg.regFam E (Lu.upperSpec u l)) k ω ∪
        WalkLaw.stageSet κ b jumps (WalkSide.capSpec (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) ℓ
          (-(Real.pi / 2)) (t : ℝ≥0∞)) (StagedReg.regFam E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true))
          (ℓ + 1) ω) := by
    rw [e2]; exact (hg.retc.union hcpt).isBounded.subset inter_subset_left
  simp only [Mf.fillVer, hb, ↓reduceIte]
  rw [e2, Qx.fillH_closure, Sec7.SideHeight.fillH_inter_H]

/-- **The union of the line family's sets at a good sample**, before B's lifetime, is the joint fill. -/
theorem union_fillVer_eq (hg : Nc.StageGoodAt κ b jumps E u l k ℓ K x₀ Ê ω) {t : ℝ≥0}
    (ht : (t : ℝ≥0∞) < Nc.bLife b jumps E ℓ ω) {B₁ B₂ : Set ℂ}
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
  rw [h₁, h₂, fillVer_first_eq hg, fillVer_joint_eq hg ht]
  exact union_eq_right.2 (fillH_mono subset_union_left)

end Good

end InteractingSLE.Theorem14.SB.Cz
