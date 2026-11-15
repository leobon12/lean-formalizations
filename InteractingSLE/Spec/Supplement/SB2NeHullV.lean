/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.SB2NeCanon

/-!
# F2b′'s version field `hull` for the joint second set

Packet PROVE-AUX61-NOJUMP (round 22, component D). On the stop structure `Nd.StopIn`, at a sample of the good event
and a B-time `t` whose clock is below the stop `V m`:

* **`StopIn.fwdHull_eq`**: the frozen driver's hull at the clock is the fill of the relative curve up to `uOf t`;
* **`StopIn.hull_joint`**: `ℍ ∖ fill (retX ∪ B[0, t]) = Φ⁻¹(ℍ ∖ fwdHull W (a t))`;
* **`StopIn.hull_of_mem`**: the same with `A₁ t`, `A₂ t` the filled stage sets of `Nd.SB2LowerStageVersionStatement5`
  (the upper history with B's stage set before `ℓ`, and the joint set through `ℓ` capped at `t`).

The bookkeeping: `Ne.stageSet_capSpec_succ_congr` (the capped stage set only sees the walk's runs) and
`Ne.stageSets_eq_of_good` (the two stage sets at a good sample).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology Metric
open scoped NNReal ENNReal
open QuantumZipper (H Hbar fwdHull)

universe u

namespace InteractingSLE.Theorem14.SB.Ne

open Supp9B Exist Exist.Staged Exist.StagedLaw Sec7.PocketTraversal Sec7.Lemma71C LuM GW1W GW1Bookkeep Lk Dv
  WalkSide

variable {κ θ : ℝ} {b : ℝ → ℝ} {jumps : Finset ℝ}

/-- **The capped stage set through `ℓ` only sees the walk's runs.** -/
theorem stageSet_capSpec_succ_congr {Ω : Type*} {D D' : ℕ → Ω → Drv} {ω : Ω} {ℓ : ℕ}
    (hrun : ∀ n, ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) (fun j => D j ω) n =
      ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) (fun j => D' j ω) n)
    (hl : (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) (fun j => D j ω) (ℓ + 1)).2.2.2.1 ℓ ≠ none)
    (τ : ℝ≥0∞) :
    WalkLaw.stageSet κ b jumps (capSpec (boundaryWalkSpec b jumps θ true) ℓ θ τ) D (ℓ + 1) ω =
      WalkLaw.stageSet κ b jumps (capSpec (boundaryWalkSpec b jumps θ true) ℓ θ τ) D' (ℓ + 1) ω := by
  set w := boundaryWalkSpec b jumps θ true with hw
  have hl' : (ExplState.run κ b jumps w (fun j => D' j ω) (ℓ + 1)).2.2.2.1 ℓ ≠ none := by
    rw [← hrun]; exact hl
  obtain ⟨hwℓ, hlen⟩ := Qx.walk_instr_of_launch hl
  obtain ⟨⟨c, θ₁⟩, hc⟩ := Option.ne_none_iff_exists'.1 hl
  obtain ⟨⟨c', θ₁'⟩, hc'⟩ := Option.ne_none_iff_exists'.1 hl'
  have h1 := pieces_run_succ_of_launch hl
  have h2 := pieces_run_succ_of_launch hl'
  rw [hrun (ℓ + 1), hrun ℓ] at h1
  have hx := List.singleton_inj.1 (List.append_cancel_left (h1.symm.trans h2))
  have hL : (D ℓ ω).2 = (D' ℓ ω).2 := by
    have := congrArg (fun x => x.2.2) hx
    simpa using this
  have hpath : ∀ r : ℝ≥0, (D ℓ ω).1 (min (r : ℝ≥0∞) (D' ℓ ω).2).toNNReal =
      (D' ℓ ω).1 (min (r : ℝ≥0∞) (D' ℓ ω).2).toNNReal := fun r => by
    have := congrFun (congrArg (fun x => x.2.1) hx) r
    rw [hL, min_eq_right (le_top : (D' ℓ ω).2 ≤ ⊤)] at this
    exact this
  have key : ∀ r : ℝ≥0, (D ℓ ω).1 (min (r : ℝ≥0∞) (min τ (D' ℓ ω).2)).toNNReal =
      (D' ℓ ω).1 (min (r : ℝ≥0∞) (min τ (D' ℓ ω).2)).toNNReal := fun r => by
    set x : ℝ≥0∞ := min (r : ℝ≥0∞) (min τ (D' ℓ ω).2) with hxdef
    have hxne : x ≠ ⊤ := ne_top_of_le_ne_top ENNReal.coe_ne_top (min_le_left _ _)
    have hxL : x ≤ (D' ℓ ω).2 := (min_le_right _ _).trans (min_le_right _ _)
    have h := hpath x.toNNReal
    rw [ENNReal.coe_toNNReal hxne, min_eq_left hxL] at h
    exact h
  have hrp : recPiece (ExplState.run κ b jumps w (fun j => D' j ω) ℓ) (D ℓ ω) τ =
      recPiece (ExplState.run κ b jumps w (fun j => D' j ω) ℓ) (D' ℓ ω) τ := by
    unfold recPiece
    rw [hL]
    exact Prod.ext rfl (Prod.ext (funext key) rfl)
  unfold WalkLaw.stageSet
  rw [pieces_run_capSpec_succ hlen.le hwℓ _ hc τ, pieces_run_capSpec_succ hlen.le hwℓ _ hc' τ, hrun ℓ]
  exact congrArg (fun S => S ∩ H) (by rw [hrp])


/-! ### The two stage sets at a good sample -/

section Good

variable {Ω : Type*} {E : ExplSpec → ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞} {u : ℝ} {l : List (ℝ × ℝ≥0)} {k ℓ : ℕ}
  {K : Ω → Set ℂ} {x₀ : Ω → ℝ} {Ê : ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞} {ω : Ω}

theorem launch_regFam (hg : Nc.StageGoodAt κ b jumps E u l k ℓ K x₀ Ê ω) :
    (ExplState.run κ b jumps (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)
      (fun j => StagedReg.regFam E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) j ω) (ℓ + 1)).2.2.2.1 ℓ ≠
        none := by
  rw [hg.runw (ℓ + 1)]; exact hg.stage.2

theorem continuousOn_bPc (hg : Nc.StageGoodAt κ b jumps E u l k ℓ K x₀ Ê ω) :
    ContinuousOn (Nc.bPc κ b jumps E ℓ ω) {t : ℝ≥0 | (t : ℝ≥0∞) ≤ Nc.bLife b jumps E ℓ ω} :=
  continuousOn_pcPt_launch hg.walk.reg hg.stage.2

/-- **The first stage set at a good sample** (any cap): the retained union in `ℍ`. -/
theorem stageSet_first_eq (hg : Nc.StageGoodAt κ b jumps E u l k ℓ K x₀ Ê ω) (τ : ℝ≥0∞) :
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
theorem stageSet_joint_eq (hg : Nc.StageGoodAt κ b jumps E u l k ℓ K x₀ Ê ω) {t : ℝ≥0}
    (ht : (t : ℝ≥0∞) < Nc.bLife b jumps E ℓ ω) :
    WalkLaw.stageSet κ b jumps (Lu.upperSpec u l) (StagedReg.regFam E (Lu.upperSpec u l)) k ω ∪
        WalkLaw.stageSet κ b jumps (capSpec (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) ℓ (-(Real.pi / 2))
          (t : ℝ≥0∞)) (StagedReg.regFam E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)) (ℓ + 1) ω =
      (Nc.retX κ b jumps E u l k ℓ ω ∪ Nc.bPc κ b jumps E ℓ ω '' Icc 0 t) ∩ H := by
  rw [stageSet_capSpec_succ_congr (D' := E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)) hg.runw
    (launch_regFam hg) (t : ℝ≥0∞), stageSet_capSpec_succ_eq hg.walk.reg hg.stage.2 (t : ℝ≥0∞)]
  have hS : {s : ℝ≥0 | (s : ℝ≥0∞) ≤ min (t : ℝ≥0∞) (E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) ℓ ω).2} =
      Icc 0 t := by
    ext s
    simp only [mem_setOf_eq, mem_Icc, zero_le, true_and]
    rw [min_eq_left (show (t : ℝ≥0∞) ≤ (E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) ℓ ω).2 from ht.le),
      ENNReal.coe_le_coe]
  have h1 := stageSet_first_eq hg (0 : ℝ≥0∞)
  rw [WalkInf.stageSet_capSpec_of_le (Qx.walk_instr_of_launch hg.stage.2).2.le ω le_rfl] at h1
  have hw : WalkLaw.stageSet κ b jumps (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)
      (E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)) ℓ ω =
      WalkLaw.stageSet κ b jumps (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)
        (StagedReg.regFam E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)) ℓ ω := by
    unfold WalkLaw.stageSet; rw [hg.runw ℓ]
  rw [hS, hw, ← union_assoc, h1, ← union_inter_distrib_right]
  rfl

end Good

end InteractingSLE.Theorem14.SB.Ne

namespace InteractingSLE.Theorem14.SB.Nd

open Vs Exist.StagedLaw Supp8.GB6 Supp8.GB6.HullId Supp8.GB6.RelDrv.Version Supp8.Q3Stop Sec7.PocketTraversal
  Sec7.Lemma71C Restart Exist Exist.Staged Lv Ms Mf WalkSide LocalSets Lk LuM Nc Dv Vr

variable {κ : ℝ} {b : ℝ → ℝ} {jumps : Finset ℝ} {Ω : Type u} [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω]
  {P : Measure Ω} [IsProbabilityMeasure P] {E : ExplSpec → ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞} {u : ℝ}
  {l : List (ℝ × ℝ≥0)} {k ℓ : ℕ} {ψ : ℝ}

namespace StopIn

variable (T : StopIn P κ b jumps E u l k ℓ ψ)

/-- **The frozen driver's hull at the clock** is the fill of the relative curve up to `uOf t`. -/
theorem fwdHull_eq {m : ℕ} {ω : Ω} (hω : ω ∈ T.Gs) {t : ℝ≥0} (ht : T.S.a t ω < T.V m ω) :
    fwdHull (fun s : ℝ => T.W m s.toNNReal ω) ((T.S.a t ω).toNNReal : ℝ) =
      fillH (T.S.ρM ω '' Icc 0 (uOf (bLife b jumps E ℓ ω) t)) := by
  have hEg := T.Gs_subset_Eg hω
  have hd := T.S.driven_ρM ω
  have hpos := T.Vstop_pos (m := m) hω
  have htop := T.Vstop_ne_top (m := m) hω
  set v : ℝ≥0 := (T.Vstop m ω).toNNReal with hv
  have hvc : (v : ℝ≥0∞) = T.Vstop m ω := ENNReal.coe_toNNReal htop
  have hv0 : 0 < v := by rw [← ENNReal.coe_lt_coe, hvc]; exact hpos
  obtain ⟨ηr, hLT, heq⟩ := exists_loewnerTrace_min hv0 (by rw [hvc]; exact T.Vstop_lt hω) (T.Wr_zero ω)
    (T.continuousOn_Wr ω) fun V hV => T.isGeneratingTrace_Wr ω hV
  have e : (fun s : ℝ => T.W m s.toNNReal ω) = fun r : ℝ => T.Wr (min r.toNNReal v) ω :=
    funext fun r => T.W_of_mem hω _
  rw [e, hLT.2.2 _ (NNReal.coe_nonneg _)]
  congr 1
  have hsL : (t : ℝ≥0∞) < bLife b jumps E ℓ ω := T.lt_life_of_lt hω ht
  have hb := beforeL_of_lt hsL
  have hc0 := hd.capClock_nonneg (uOf_nonneg hb)
  have has' : T.S.a t ω = ENNReal.ofReal (capClock (T.S.ρM ω) (uOf (bLife b jumps E ℓ ω) t)) := by
    rw [T.S.a_eq hEg, if_pos hsL]
  have hcv : ((T.S.a t ω).toNNReal : ℝ≥0∞) < v := by
    rw [ENNReal.coe_toNNReal (ne_top_of_lt ht), hvc, ← T.V_eq hω]; exact ht
  have hcR : ((T.S.a t ω).toNNReal : ℝ) = capClock (T.S.ρM ω) (uOf (bLife b jumps E ℓ ω) t) := by
    show (T.S.a t ω).toReal = _
    rw [has', ENNReal.toReal_ofReal hc0]
  have him : ηr '' Icc 0 ((T.S.a t ω).toNNReal : ℝ) = capTrace (T.S.ρM ω) '' Icc 0 (T.S.a t ω).toNNReal := by
    ext z
    constructor
    · rintro ⟨x, hx, rfl⟩
      have hxle : x.toNNReal ≤ (T.S.a t ω).toNNReal := Real.toNNReal_le_iff_le_coe.2 hx.2
      refine ⟨x.toNNReal, ⟨zero_le, hxle⟩, ?_⟩
      have hxv : (x.toNNReal : ℝ≥0∞) < v := lt_of_le_of_lt (ENNReal.coe_le_coe.2 hxle) hcv
      rw [← heq _ hxv, Real.coe_toNNReal _ hx.1]
    · rintro ⟨r, hr, rfl⟩
      exact ⟨r, ⟨r.2, NNReal.coe_le_coe.2 hr.2⟩, heq r (lt_of_le_of_lt (ENNReal.coe_le_coe.2 hr.2) hcv)⟩
  rw [him, hd.image_capTrace (hcv.trans (by rw [hvc]; exact T.Vstop_lt hω)), hcR, hd.capInv_eq (uOf_nonneg hb)]

/-- **The pulled-back relative hull is the joint fill** of the retained union and B's piece up to `t`. -/
theorem hull_joint {m : ℕ} {ω : Ω} (hω : ω ∈ T.Gs) {t : ℝ≥0} (ht : T.S.a t ω < T.V m ω) :
    H \ fillH (retX κ b jumps E u l k ℓ ω ∪ bPc κ b jumps E ℓ ω '' Icc 0 t) =
      (Mo.hullChart (fillH (T.S.K ω)) (T.S.x₀ ω)).2.1 ''
        (H \ fwdHull (fun s : ℝ => T.W m s.toNNReal ω) ((T.S.a t ω).toNNReal : ℝ)) := by
  have hEg := T.Gs_subset_Eg hω
  have hg := T.S.good ω hEg
  have hsL : (t : ℝ≥0∞) < bLife b jumps E ℓ ω := T.lt_life_of_lt hω ht
  have hb := beforeL_of_lt hsL
  rw [T.fwdHull_eq hω ht, T.S.ρM_eq hEg]
  have hcc : canonCurve (T.S.K ω) (T.S.x₀ ω) (bPc κ b jumps E ℓ ω) (bLife b jumps E ℓ ω) =
      canonCurve (retX κ b jumps E u l k ℓ ω) (T.S.x₀ ω) (bPc κ b jumps E ℓ ω) (bLife b jumps E ℓ ω) := by
    unfold canonCurve canonVal canonGood; rw [hg.fill]
  have hdr : IsDrivenCurve (canonCurve (retX κ b jumps E u l k ℓ ω) (T.S.x₀ ω) (bPc κ b jumps E ℓ ω)
      (bLife b jumps E ℓ ω)) := by
    rw [← hcc]; exact hg.driven
  have h := Ne.H_diff_fillH_union_canon hg.retc hg.hull hg.pos (Ne.continuousOn_bPc hg) hdr (uOf_nonneg hb)
  rw [cTime_uOf hb, Real.toNNReal_coe] at h
  rw [hg.fill]
  show _ = _ '' (H \ fillH (canonCurve (T.S.K ω) (T.S.x₀ ω) (bPc κ b jumps E ℓ ω) (bLife b jumps E ℓ ω) '' _))
  rw [hcc]
  exact h

/-- **F2b′'s `hull` field** for the joint second set (`Nd.SB2LowerStageVersionStatement5`'s `A₁`, `A₂`). -/
theorem hull_of_mem {m : ℕ} {ω : Ω} (hω : ω ∈ T.Gs) {t : ℝ≥0} (ht : T.S.a t ω < T.V m ω) {A₁ A₂ : Set ℂ}
    (h₁ : A₁ = fillVer (fun ω =>
      WalkLaw.stageSet κ b jumps (Lu.upperSpec u l) (StagedReg.regFam E (Lu.upperSpec u l)) k ω ∪
      WalkLaw.stageSet κ b jumps (capSpec (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) ℓ
        (-(Real.pi / 2)) (t : ℝ≥0∞)) (StagedReg.regFam E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)) ℓ ω) ω)
    (h₂ : A₂ = fillVer (fun ω =>
      WalkLaw.stageSet κ b jumps (Lu.upperSpec u l) (StagedReg.regFam E (Lu.upperSpec u l)) k ω ∪
      WalkLaw.stageSet κ b jumps (capSpec (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) ℓ
        (-(Real.pi / 2)) (t : ℝ≥0∞)) (StagedReg.regFam E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true))
        (ℓ + 1) ω) ω) :
    H \ (A₁ ∪ A₂) = (Mo.hullChart (fillH (T.S.K ω)) (T.S.x₀ ω)).2.1 ''
      (H \ fwdHull (fun s : ℝ => T.W m s.toNNReal ω) ((T.S.a t ω).toNNReal : ℝ)) := by
  have hEg := T.Gs_subset_Eg hω
  have hg := T.S.good ω hEg
  have hsL : (t : ℝ≥0∞) < bLife b jumps E ℓ ω := T.lt_life_of_lt hω ht
  have hA₁ : A₁ = fillH (retX κ b jumps E u l k ℓ ω) := by
    have hb : Bornology.IsBounded (retX κ b jumps E u l k ℓ ω ∩ H) := hg.retc.isBounded.subset inter_subset_left
    rw [h₁, fillVer_of_bounded (B := fun ω =>
      WalkLaw.stageSet κ b jumps (Lu.upperSpec u l) (StagedReg.regFam E (Lu.upperSpec u l)) k ω ∪
      WalkLaw.stageSet κ b jumps (capSpec (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) ℓ
        (-(Real.pi / 2)) (t : ℝ≥0∞)) (StagedReg.regFam E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)) ℓ ω)
      (by show Bornology.IsBounded (_ ∪ _); rw [Ne.stageSet_first_eq hg]; exact hb)]
    show fillH (closure (_ ∪ _)) = _
    rw [Ne.stageSet_first_eq hg, Mo.fillH_closure_inter_H]
  have hA₂ : A₂ = fillH (retX κ b jumps E u l k ℓ ω ∪ bPc κ b jumps E ℓ ω '' Icc 0 t) := by
    have hPc : IsCompact (bPc κ b jumps E ℓ ω '' Icc 0 t) :=
      isCompact_Icc.image_of_continuousOn ((Ne.continuousOn_bPc hg).mono fun s hs =>
        show (s : ℝ≥0∞) ≤ bLife b jumps E ℓ ω from (ENNReal.coe_le_coe.2 hs.2).trans hsL.le)
    have hb : Bornology.IsBounded ((retX κ b jumps E u l k ℓ ω ∪ bPc κ b jumps E ℓ ω '' Icc 0 t) ∩ H) :=
      (hg.retc.union hPc).isBounded.subset inter_subset_left
    rw [h₂, fillVer_of_bounded (B := fun ω =>
      WalkLaw.stageSet κ b jumps (Lu.upperSpec u l) (StagedReg.regFam E (Lu.upperSpec u l)) k ω ∪
      WalkLaw.stageSet κ b jumps (capSpec (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) ℓ
        (-(Real.pi / 2)) (t : ℝ≥0∞)) (StagedReg.regFam E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true))
        (ℓ + 1) ω)
      (by show Bornology.IsBounded (_ ∪ _); rw [Ne.stageSet_joint_eq hg hsL]; exact hb)]
    show fillH (closure (_ ∪ _)) = _
    rw [Ne.stageSet_joint_eq hg hsL, Mo.fillH_closure_inter_H]
  rw [hA₁, hA₂, union_eq_right.2 (fillH_mono subset_union_left)]
  exact T.hull_joint hω ht

end StopIn

end InteractingSLE.Theorem14.SB.Nd
