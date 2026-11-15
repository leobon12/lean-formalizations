/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec5.StagedNTrUpTo

/-!
# Prop 5.9's tree candidates only read their paths up to the switches

Packet PROVE-STAGED-NODETRANSFER (towards `NodeGluePast`). Causality of PROVE-PROP59-PIECES' tree construction: if two
samples of a tree have the same counterflow chart, root marks and dilation, and the paths of an alive list `T` agree up
to its last switch, then along every prefix the tree marks agree and the candidate pieces agree up to their switching
times (`CanonUpTo`).

* `locDrv_congr`, **`kW_eq_of_eqOn`**, `kInv_eq_of_eqOn`: the local driver, the killed driver and the inverse capacity
  clock of a killed arc only read the arc up to the capacity considered;
* **`pieceUpTo_arcPiece`**: arc pieces of killed arcs agreeing up to `S` agree up to the capacity of `S` (S3's restart
  formula `arcVL_sub_arcW` with the continuous local driver of `S`);
* `TreeSameAt`, **`TreeData.causal`**.

R48: nothing here uses Theorem 1.2/1.3 or any `*_of_param`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Filter Set
open scoped NNReal ENNReal

namespace InteractingSLE.Sec5.CrossCond.StagedNTr

open WangWu WangWu.ImgWord Prop59System Prop59Stage Prop59Pieces StagedCand StagedRepJ StagedS3
open GlueCond Cond44Ref CrossCond.Word49 LawUnique
open Prop59NodeTree (shiftDrv)
open Sec7.Lemma71C (capClock)

/-! ### Killed arcs read up to a capacity -/

section Arc

/-- The local driver of `S` only reads the arc on `[0, S]`. -/
theorem locDrv_congr {γ γ' : ℝ → ℂ} {S : ℝ} (h : EqOn γ γ' (Icc 0 S)) : locDrv γ S = locDrv γ' S := by
  classical
  have hp : (fun W : ℝ → ℝ => Continuous W ∧ W 0 = 0 ∧
        ∀ u ∈ Icc 0 S, QuantumZipper.fwdHull W (capClock γ u) = γ '' Ioc 0 u) =
      fun W => Continuous W ∧ W 0 = 0 ∧ ∀ u ∈ Icc 0 S, QuantumZipper.fwdHull W (capClock γ' u) = γ' '' Ioc 0 u := by
    funext W
    refine propext (and_congr_right fun _ => and_congr_right fun _ => forall₂_congr fun u hu => ?_)
    rw [Prop59Pieces.capClock_congr (h.mono (Icc_subset_Icc_right hu.2)),
      image_congr (h.mono (Ioc_subset_Icc_self.trans (Icc_subset_Icc_right hu.2)))]
  unfold locDrv
  by_cases hex : ∃ W : ℝ → ℝ, Continuous W ∧ W 0 = 0 ∧
      ∀ u ∈ Icc 0 S, QuantumZipper.fwdHull W (capClock γ u) = γ '' Ioc 0 u
  · have hex' : ∃ W : ℝ → ℝ, Continuous W ∧ W 0 = 0 ∧
        ∀ u ∈ Icc 0 S, QuantumZipper.fwdHull W (capClock γ' u) = γ' '' Ioc 0 u := by
      have := hex; rw [show (∃ W : ℝ → ℝ, _) = _ from congrArg Exists hp] at this; exact this
    simp only [hex, hex', ↓reduceDIte]
    exact choose_congr hp hex hex'
  · have hex' : ¬ ∃ W : ℝ → ℝ, Continuous W ∧ W 0 = 0 ∧
        ∀ u ∈ Icc 0 S, QuantumZipper.fwdHull W (capClock γ' u) = γ' '' Ioc 0 u := by
      have := hex; rw [show (∃ W : ℝ → ℝ, _) = _ from congrArg Exists hp] at this; exact this
    simp only [hex, hex', ↓reduceDIte]

variable {γ γ' : ℝ → ℂ} {P P' : Set ℝ} (hγ : IsKilledArc γ P) (hγ' : IsKilledArc γ' P') {S : ℝ}
  (hS : S ∈ P) (hS' : S ∈ P') (h : EqOn γ γ' (Icc 0 S))
include hγ hγ' hS hS' h

theorem lt_kLife_of_le {v : ℝ≥0} (hv : (v : ℝ) ≤ capClock γ S) :
    (v : WithTop ℝ≥0) < kLife γ P ∧ (v : WithTop ℝ≥0) < kLife γ' P' := by
  have hcap : capClock γ S = capClock γ' S := Prop59Pieces.capClock_congr h
  have h1 : v ≤ (capClock γ S).toNNReal := (Real.le_toNNReal_iff_coe_le (hγ.capClock_nonneg hS)).2 hv
  have h2 : v ≤ (capClock γ' S).toNNReal := by rw [← hcap]; exact h1
  exact ⟨lt_of_le_of_lt (WithTop.coe_le_coe.2 h1) (hγ.lt_kLife hS),
    lt_of_le_of_lt (WithTop.coe_le_coe.2 h2) (hγ'.lt_kLife hS')⟩

/-- **The killed drivers of two killed arcs agree up to the capacity of `S`** if the arcs agree on `[0, S]`. -/
theorem kW_eq_of_eqOn (hS0 : 0 < S) {v : ℝ≥0} (hv : (v : ℝ) ≤ capClock γ S) : kW γ P v = kW γ' P' v := by
  have hcap : capClock γ S = capClock γ' S := Prop59Pieces.capClock_congr h
  obtain ⟨h1, h2⟩ := lt_kLife_of_le hγ hγ' hS hS' h hv
  rw [kW_of_lt h1, kW_of_lt h2, hγ.chainDrv_eq hS hS0 ⟨v.coe_nonneg, hv⟩,
    hγ'.chainDrv_eq hS' hS0 ⟨v.coe_nonneg, hcap ▸ hv⟩, locDrv_congr h]

theorem kPath_eqOn_locDrv' (hS0 : 0 < S) : EqOn (kPath γ P) (locDrv γ S) (Icc 0 (capClock γ S)) := by
  intro v hv
  have hv' : ((v.toNNReal : ℝ≥0) : ℝ) ≤ capClock γ S := by rw [Real.coe_toNNReal _ hv.1]; exact hv.2
  obtain ⟨h1, -⟩ := lt_kLife_of_le hγ hγ' hS hS' h hv'
  simp only [kPath]
  rw [kW_of_lt h1, Real.coe_toNNReal _ hv.1, hγ.chainDrv_eq hS hS0 hv]

/-- **The inverse capacity clocks agree up to the capacity of `S`.** -/
theorem kInv_eq_of_eqOn {v : ℝ≥0} (hv : (v : ℝ) ≤ capClock γ S) : kInv γ P v = kInv γ' P' v := by
  obtain ⟨h1, -⟩ := lt_kLife_of_le hγ hγ' hS hS' h hv
  obtain ⟨hu, hcu⟩ := hγ.kInv_spec h1
  have huS : kInv γ P v ≤ S := by
    by_contra hlt
    push Not at hlt
    have := hγ.strictMonoOn_capClock hS hu hlt
    rw [hcu] at this
    exact absurd hv (not_le.2 this)
  have hu0 : 0 ≤ kInv γ P v := hγ.nonneg _ hu
  have hu' : kInv γ P v ∈ P' := hγ'.icc S hS' ⟨hu0, huS⟩
  have hc' : capClock γ' (kInv γ P v) = v := by
    rw [← Prop59Pieces.capClock_congr (h.mono (Icc_subset_Icc_right huS))]; exact hcu
  have e := hγ'.kInv_capClock hu'
  rw [hc'] at e
  exact e.symm

end Arc

/-! ### Arc pieces agree up to the capacity of the switch -/

section Piece

variable {Ω Ω' : Type*} {nL nR : ℕ} {γ : Ω → ℝ → ℂ} {P : Ω → Set ℝ} {S₀ : Ω → ℝ≥0} {A : Set Ω}
  {xL : Ω → Fin nL → ℝ} {xR : Ω → Fin nR → ℝ} {B : ℝ≥0 → Ω → ℝ} {γ' : Ω' → ℝ → ℂ} {P' : Ω' → Set ℝ}
  {S₀' : Ω' → ℝ≥0} {A' : Set Ω'} {xL' : Ω' → Fin nL → ℝ} {xR' : Ω' → Fin nR → ℝ} {B' : ℝ≥0 → Ω' → ℝ}
  {ω : Ω} {ω' : Ω'}

/-- **Arc pieces of killed arcs agreeing on `[0, S]` agree up to the capacity of `S`** (same start capacity, alive,
same initial marks). -/
theorem pieceUpTo_arcPiece (hγ : IsKilledArc (γ ω) (P ω)) (hγ' : IsKilledArc (γ' ω') (P' ω')) {S : ℝ} (hS0 : 0 < S)
    (hS : S ∈ P ω) (hS' : S ∈ P' ω') (h : EqOn (γ ω) (γ' ω') (Icc 0 S)) (hS₀ : S₀ ω = S₀' ω')
    (hle : (S₀ ω : ℝ) ≤ capClock (γ ω) S) (hA : ω ∈ A) (hA' : ω' ∈ A') (hxL : xL ω = xL' ω')
    (hxR : xR ω = xR' ω') :
    PieceUpTo (arcPiece γ P S₀ A xL xR B) (arcPiece γ' P' S₀' A' xL' xR' B') ω ω'
      ((capClock (γ ω) S).toNNReal - S₀ ω) := by
  have hc0 : 0 ≤ capClock (γ ω) S := hγ.capClock_nonneg hS
  have hS₀le : S₀ ω ≤ (capClock (γ ω) S).toNNReal := (Real.le_toNNReal_iff_coe_le hc0).2 hle
  -- the absolute capacity of a piece time before the switch
  have hcap : ∀ u ≤ (capClock (γ ω) S).toNNReal - S₀ ω, ((S₀ ω + u : ℝ≥0) : ℝ) ≤ capClock (γ ω) S := by
    intro u hu
    have h1 : S₀ ω + u ≤ (capClock (γ ω) S).toNNReal := (le_tsub_iff_left hS₀le).1 hu
    have h2 := NNReal.coe_le_coe.2 h1
    rwa [Real.coe_toNNReal _ hc0] at h2
  have hlt : ∀ u ≤ (capClock (γ ω) S).toNNReal - S₀ ω,
      (u : ℝ≥0∞) < arcζ γ P S₀ A ω ∧ (u : ℝ≥0∞) < arcζ γ' P' S₀' A' ω' := by
    intro u hu
    obtain ⟨h1, h2⟩ := lt_kLife_of_le hγ hγ' hS hS' h (hcap u hu)
    exact ⟨lt_arcζ_iff.2 ⟨hA, h1⟩, lt_arcζ_iff.2 ⟨hA', by rw [← hS₀]; exact h2⟩⟩
  have hkW : ∀ v : ℝ≥0, (v : ℝ) ≤ capClock (γ ω) S → kW (γ ω) (P ω) v = kW (γ' ω') (P' ω') v :=
    fun v hv => kW_eq_of_eqOn hγ hγ' hS hS' h hS0 hv
  have hW : ∀ u ≤ (capClock (γ ω) S).toNNReal - S₀ ω, arcW γ P S₀ A u ω = arcW γ' P' S₀' A' u ω' := by
    intro u hu
    rw [arcW_of_lt (hlt u hu).1, arcW_of_lt (hlt u hu).2, ← hS₀, hkW _ (hcap u hu),
      hkW _ (le_trans (by exact_mod_cast le_self_add) (hcap u hu))]
  -- the continuous local driver of `S` extends both killed drivers
  have hw := (hγ.locDrv_spec hS hS0).1
  have hEq : EqOn (kPath (γ ω) (P ω)) (locDrv (γ ω) S) (Icc 0 (capClock (γ ω) S)) :=
    kPath_eqOn_locDrv' hγ hγ' hS hS' h hS0
  have hEq' : EqOn (kPath (γ' ω') (P' ω')) (locDrv (γ ω) S) (Icc 0 (capClock (γ ω) S)) := by
    rw [locDrv_congr h, Prop59Pieces.capClock_congr h]
    exact kPath_eqOn_locDrv' hγ' hγ hS' hS h.symm hS0
  refine ⟨hW, fun i u hu => ?_, fun k u hu => ?_, hlt, fun u hu => ?_⟩
  · have hu1 : ((S₀ ω + u : ℝ≥0) : WithTop ℝ≥0) < kLife (γ ω) (P ω) := (lt_arcζ_iff.1 (hlt u hu).1).2
    have hu2 : ((S₀' ω' + u : ℝ≥0) : WithTop ℝ≥0) < kLife (γ' ω') (P' ω') := (lt_arcζ_iff.1 (hlt u hu).2).2
    have e1 := arcVL_sub_arcW (xL := xL) hA hu1 hw (hEq.mono (Icc_subset_Icc_right (hcap u hu))) i
    have e2 := arcVL_sub_arcW (xL := xL') hA' hu2 hw
      (hEq'.mono (Icc_subset_Icc_right (by rw [← hS₀]; exact hcap u hu))) i
    rw [← hS₀, ← hxL] at e2
    have e3 := hW u hu
    show arcVL γ P S₀ A xL i u ω = arcVL γ' P' S₀' A' xL' i u ω'
    linarith
  · have hu1 : ((S₀ ω + u : ℝ≥0) : WithTop ℝ≥0) < kLife (γ ω) (P ω) := (lt_arcζ_iff.1 (hlt u hu).1).2
    have hu2 : ((S₀' ω' + u : ℝ≥0) : WithTop ℝ≥0) < kLife (γ' ω') (P' ω') := (lt_arcζ_iff.1 (hlt u hu).2).2
    have e1 := arcVR_sub_arcW (xR := xR) hA hu1 hw (hEq.mono (Icc_subset_Icc_right (hcap u hu))) k
    have e2 := arcVR_sub_arcW (xR := xR') hA' hu2 hw
      (hEq'.mono (Icc_subset_Icc_right (by rw [← hS₀]; exact hcap u hu))) k
    rw [← hS₀, ← hxR] at e2
    have e3 := hW u hu
    show arcVR γ P S₀ A xR k u ω = arcVR γ' P' S₀' A' xR' k u ω'
    linarith
  · have hu1 : ((S₀ ω + u : ℝ≥0) : WithTop ℝ≥0) < kLife (γ ω) (P ω) := (lt_arcζ_iff.1 (hlt u hu).1).2
    have hu2 : ((S₀' ω' + u : ℝ≥0) : WithTop ℝ≥0) < kLife (γ' ω') (P' ω') := (lt_arcζ_iff.1 (hlt u hu).2).2
    show arcClk γ P S₀ A ω u = arcClk γ' P' S₀' A' ω' u
    rw [arcClk_of_mem hA, arcClk_of_mem hA']
    show absClock (γ ω) (P ω) (S₀ ω + u) = absClock (γ' ω') (P' ω') (S₀' ω' + u)
    rw [absClock_of_lt hu1, absClock_of_lt hu2, ← hS₀, kInv_eq_of_eqOn hγ hγ' hS hS' h (hcap u hu)]

end Piece

/-! ### Causality of the tree construction -/

section Tree

variable {Ω : Type*} {nL₀ nR₀ : ℕ}

/-- **Two samples of a tree see the same counterflow chart, root marks and dilation**, and both are good. -/
structure TreeSameAt (D : TreeData Ω nL₀ nR₀) (γ γ' : Ω) : Prop where
  lam : D.lam γ = D.lam γ'
  drv : cfDrv0 D.r (D.y γ) = cfDrv0 D.r (D.y γ')
  hull : cfHullQ D.r (D.y γ) = cfHullQ D.r (D.y γ')
  xL0 : D.xL0 γ = D.xL0 γ'
  xR0 : D.xR0 γ = D.xR0 γ'
  G : γ ∈ D.G
  G' : γ' ∈ D.G

variable {D : TreeData Ω nL₀ nR₀} {γ γ' : Ω}

/-- The image arcs agree where the paths agree. -/
theorem TreeSameAt.img_eqOn (hs : TreeSameAt D γ γ') {k : ℕ} {t : Fin k → ℝ≥0} (hv : D.valid k t) {S : ℝ}
    (h : EqOn (D.α k t γ) (D.α k t γ') (Icc 0 S)) : EqOn (D.img k t γ) (D.img k t γ') (Icc 0 S) := by
  intro u hu
  rw [TreeData.img, tImg_of_mem (show γ ∈ D.Gc k t from ⟨hv, hs.G⟩),
    tImg_of_mem (show γ' ∈ D.Gc k t from ⟨hv, hs.G'⟩)]
  simp only [imgCurve, hs.lam, hs.drv, h hu]

/-- The pre-contact times agree where the paths agree. -/
theorem TreeSameAt.mem_pre_iff (hs : TreeSameAt D γ γ') {k : ℕ} {t : Fin k → ℝ≥0} (hv : D.valid k t) {S : ℝ}
    (h : EqOn (D.α k t γ) (D.α k t γ') (Icc 0 S)) {u : ℝ} (hu : u ≤ S) : u ∈ D.pre k t γ ↔ u ∈ D.pre k t γ' := by
  rw [TreeData.pre, tPre_of_mem (show γ ∈ D.Gc k t from ⟨hv, hs.G⟩),
    tPre_of_mem (show γ' ∈ D.Gc k t from ⟨hv, hs.G'⟩), hs.hull]
  exact preContact_congr h hu

/-- A child and its parent see the same pre-contact times up to the child's last switch. -/
theorem mem_pre_init_iff (hT : D.IsTree) {ω : Ω} {k : ℕ} {t : Fin (k + 1) → ℝ≥0}
    (hv : D.valid (k + 1) t) (hG : ω ∈ D.G) {u : ℝ} (hu : u ≤ qLast (k + 1) t) :
    u ∈ D.pre (k + 1) t ω ↔ u ∈ D.pre k (Fin.init t) ω := by
  have hv' := (hT.init k t hv).1
  rw [TreeData.pre, TreeData.pre, tPre_of_mem (show ω ∈ D.Gc (k + 1) t from ⟨hv, hG⟩),
    tPre_of_mem (show ω ∈ D.Gc k (Fin.init t) from ⟨hv', hG⟩)]
  exact preContact_congr (fun v hv'' => hT.pfx k t hv ω v hv''.1 hv''.2) hu

variable [MeasurableSpace Ω]

/-- **Causality of the tree construction.** At two samples of a tree with the same counterflow chart, root marks and
dilation, if a list `T` is alive at the first and the paths of `T` agree up to its last switch, then `T` is alive at the
second, the tree marks and start capacities of `T` agree, and along `T` the candidate pieces agree up to their
switching times. -/
theorem TreeData.causal (hD : D.IsReg) (hT : D.IsTree) (hpos : ∀ k t, D.valid (k + 1) t → 0 < qLast (k + 1) t)
    (hs : TreeSameAt D γ γ') :
    ∀ (ℓ : ℕ) (T : Fin ℓ → ℝ≥0), γ ∈ D.alive ℓ T → EqOn (D.α ℓ T γ) (D.α ℓ T γ') (Icc 0 (qLast ℓ T)) →
      γ' ∈ D.alive ℓ T ∧ D.marks ℓ T γ = D.marks ℓ T γ' ∧ D.startCap ℓ T γ = D.startCap ℓ T γ' ∧
        CanonUpTo D.cand D.cand γ γ' ℓ T
  | 0, T, hA, hα => by
    have hv := hA.1.1
    have hal : γ' ∈ D.alive 0 T := ⟨⟨hv, hs.G'⟩, (hs.mem_pre_iff hv hα le_rfl).1 hA.2⟩
    refine ⟨hal, by simp only [TreeData.marks, hs.xL0, hs.xR0], ?_, trivial⟩
    rw [Prop59NodeTree.TreeData.startCap_eq hA, Prop59NodeTree.TreeData.startCap_eq hal,
      Prop59Pieces.capClock_congr (hs.img_eqOn hv hα)]
  | ℓ + 1, T, hA, hα => by
    have hv := hA.1.1
    obtain ⟨hv', hle, hlt1⟩ := hT.init ℓ T hv
    have hγk := (hD.isKilledFamily ℓ (Fin.init T)).arc γ
    have hγk' := (hD.isKilledFamily ℓ (Fin.init T)).arc γ'
    have hA0 := hT.alive_init hA hγk
    have hS0 : 0 < qLast (ℓ + 1) T := hpos ℓ T hv
    -- the parent's paths agree up to the switch
    have hαk : EqOn (D.α ℓ (Fin.init T) γ) (D.α ℓ (Fin.init T) γ') (Icc 0 (qLast (ℓ + 1) T)) := fun u hu => by
      rw [← hT.pfx ℓ T hv γ u hu.1 hu.2, ← hT.pfx ℓ T hv γ' u hu.1 hu.2]; exact hα hu
    obtain ⟨hA0', hmk, hcap0, hcanon⟩ :=
      TreeData.causal hD hT hpos hs ℓ (Fin.init T) hA0 (hαk.mono (Icc_subset_Icc_right hle))
    have himg := hs.img_eqOn hv' hαk
    -- the switch is pre-contact for the parent at both samples
    have hSP : qLast (ℓ + 1) T ∈ D.pre ℓ (Fin.init T) γ :=
      (mem_pre_init_iff hT hv hs.G le_rfl).1 hA.2
    have hSP' : qLast (ℓ + 1) T ∈ D.pre ℓ (Fin.init T) γ' := (hs.mem_pre_iff hv' hαk le_rfl).1 hSP
    have hSP'' : qLast (ℓ + 1) T ∈ D.pre (ℓ + 1) T γ' :=
      (mem_pre_init_iff hT hv hs.G' le_rfl).2 hSP'
    have hal : γ' ∈ D.alive (ℓ + 1) T := ⟨⟨hv, hs.G'⟩, hSP''⟩
    -- the switching time of the parent
    have hsc := Prop59NodeTree.TreeData.startCap_succ hD hT hA hA0
    have hcapS : D.startCap (ℓ + 1) T γ = (capClock (D.img ℓ (Fin.init T) γ) (qLast (ℓ + 1) T)).toNNReal := by
      rw [Prop59NodeTree.TreeData.startCap_eq hA]
      congr 1
      refine Prop59Pieces.capClock_congr fun u hu => ?_
      rw [TreeData.img, TreeData.img, tImg_of_mem (show γ ∈ D.Gc (ℓ + 1) T from ⟨hv, hs.G⟩),
        tImg_of_mem (show γ ∈ D.Gc ℓ (Fin.init T) from ⟨hv', hs.G⟩)]
      simp only [imgCurve, hT.pfx ℓ T hv γ u hu.1 hu.2]
    have hc0 := hγk.capClock_nonneg hSP
    have hT₀ : candInv D.cand ℓ (Fin.init T) (T (Fin.last ℓ)) γ =
        (capClock (D.img ℓ (Fin.init T) γ) (qLast (ℓ + 1) T)).toNNReal - D.startCap ℓ (Fin.init T) γ := by
      rw [TreeData.candInv_eq, ← hcapS, ← hsc, add_tsub_cancel_left]
    have hle0 : (D.startCap ℓ (Fin.init T) γ : ℝ) ≤ capClock (D.img ℓ (Fin.init T) γ) (qLast (ℓ + 1) T) := by
      have h1 : D.startCap ℓ (Fin.init T) γ ≤ (capClock (D.img ℓ (Fin.init T) γ) (qLast (ℓ + 1) T)).toNNReal := by
        rw [← hcapS, ← hsc]; exact le_self_add
      have h2 := NNReal.coe_le_coe.2 h1
      rwa [Real.coe_toNNReal _ hc0] at h2
    have hpiece := pieceUpTo_arcPiece (B := D.noise ℓ (Fin.init T)) (B' := D.noise ℓ (Fin.init T))
      (xL := fun ω => (D.marks ℓ (Fin.init T) ω).1) (xL' := fun ω => (D.marks ℓ (Fin.init T) ω).1)
      (xR := fun ω => (D.marks ℓ (Fin.init T) ω).2) (xR' := fun ω => (D.marks ℓ (Fin.init T) ω).2)
      hγk hγk' hS0 hSP hSP' himg hcap0 hle0 hA0 hA0' (by rw [hmk]) (by rw [hmk])
    rw [← hT₀] at hpiece
    replace hpiece : PieceUpTo (D.cand ℓ (Fin.init T)) (D.cand ℓ (Fin.init T)) γ γ'
        (candInv D.cand ℓ (Fin.init T) (T (Fin.last ℓ)) γ) := hpiece
    -- the clock reads the switch value at the switching time
    have hclk : (D.cand ℓ (Fin.init T)).clk γ (candInv D.cand ℓ (Fin.init T) (T (Fin.last ℓ)) γ) =
        T (Fin.last ℓ) := by
      rw [TreeData.clk_cand, arcClk_of_mem hA0]
      show absClock (D.img ℓ (Fin.init T) γ) (D.pre ℓ (Fin.init T) γ)
        (D.startCap ℓ (Fin.init T) γ + candInv D.cand ℓ (Fin.init T) (T (Fin.last ℓ)) γ) = _
      have e1 : D.startCap ℓ (Fin.init T) γ + candInv D.cand ℓ (Fin.init T) (T (Fin.last ℓ)) γ =
          (capClock (D.img ℓ (Fin.init T) γ) (qLast (ℓ + 1) T)).toNNReal := by
        rw [TreeData.candInv_eq, hsc, hcapS]
      rw [e1, absClock_of_lt (hγk.lt_kLife hSP), Real.coe_toNNReal _ hc0, hγk.kInv_capClock hSP]
      show (CrossRestart.physTime (decode (T (Fin.last ℓ)))).toNNReal = _
      rw [physTime_decode hlt1, Real.toNNReal_coe]
    have hr := (hD.isRegFam ℓ (Fin.init T))
    have hst := hpiece.stageUpTo (past := ⊥) (past' := ⊥) (R := ∅) (R' := ∅)
      (y := fun _ => (0 : Start (nL₀ + ℓ) (nR₀ + ℓ))) (y' := fun _ => 0) rfl
    obtain ⟨-, hinv, hinvle⟩ := hst.clkInv (hr.clk_mono γ) (hr.clk_mono γ') (le_of_eq hclk.symm)
    have hinv' : candInv D.cand ℓ (Fin.init T) (T (Fin.last ℓ)) γ =
        candInv D.cand ℓ (Fin.init T) (T (Fin.last ℓ)) γ' := hinv
    refine ⟨hal, ?_, ?_, hcanon, hpiece⟩
    · rw [StagedNode.TreeData.marks_succ, StagedNode.TreeData.marks_succ, ← hinv']
      have hle1 : candInv D.cand ℓ (Fin.init T) (T (Fin.last ℓ)) γ ≤
          candInv D.cand ℓ (Fin.init T) (T (Fin.last ℓ)) γ := le_rfl
      simp only [hpiece.W _ hle1, hpiece.VL _ _ hle1, hpiece.VR _ _ hle1]
    · rw [Prop59NodeTree.TreeData.startCap_eq hA, Prop59NodeTree.TreeData.startCap_eq hal,
        Prop59Pieces.capClock_congr (hs.img_eqOn hv hα)]

end Tree

end InteractingSLE.Sec5.CrossCond.StagedNTr
