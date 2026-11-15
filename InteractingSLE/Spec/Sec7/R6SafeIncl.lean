/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.R6SafeFaceP
import InteractingSLE.Spec.Sec7.R5RefCurrent
import InteractingSLE.Spec.Sec7.HOuterGeo

/-!
# R.6's face: the inclusion of the two current domains up to one common point

PROVE-R6-SAFE. Part (a) of the positional face `R6FaceP` is the inclusion of the inner current domain in the outer one.
This file proves its deterministic parts (handoff §4, (a1)–(a2)):

* **`inter_frontier_subset_of_fillH`** (general): for a Jordan coordinate `ψ` of `C` and a set `E ⊆ C̄ ∖ {x₀}` with
  compact image `Z = ψ(E)`, the frontier of `C ∩ ψ⁻¹(ℍ ∖ fill Z)` inside `C` lies in `E`;
* (a1) **`outer_frontier_subset_trace`**: the frontier of an outer pocket's current domain inside the pocket lies on
  the counterflow's trace before the fibre end of the current relative time;
* (a2) **`exists_rat_lt_ambTime0`**: for a contained pocket and an ambient visit time `T`, some rational live
  relative time `q'` has its left stop after `T`, and then the inner current domain misses `η([0, T])`;
* **`dom_subset_of_trace`**: the inner current domain lies in the outer one as soon as they meet (the common point
  (a3) is the only remaining input of (a)).

R48: nothing here uses Theorem 1.2/1.3, `Theorem12ParamStatement`, `Theorem13Statement` or any `*_of_param`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Filter Topology Metric
open QuantumZipper (H Hbar)
open SupercriticalConformalCovariance (IsConformalBijection)
open scoped NNReal ENNReal

namespace InteractingSLE.Sec7.R6Safe

open Sec6 PocketTraversal Lemma71C

/-! ### The frontier of a relative domain lies on the trace (deterministic) -/

section Frontier

/-- **The frontier of `C ∩ ψ⁻¹(ℍ ∖ fill Z)` inside `C` lies in `E`** (`ψ` a Jordan coordinate of `C`, `E ⊆ C̄ ∖ {x₀}`,
`Z = ψ(E)` compact): a point of `C` off `E` maps off `Z`; if it is not in the relative domain, its image lies in a
bounded component of `ℍ ∖ Z`, an open subset of `fill Z`, whose preimage is a neighbourhood missing the domain. -/
theorem inter_frontier_subset_of_fillH {C E : Set ℂ} {ψ : ℂ → ℂ} {x₀ y₀ : ℂ} (hCo : IsOpen C)
    (hψ : IsJordanCoord C x₀ y₀ ψ) (hx₀ : x₀ ∉ C) (hE : E ⊆ closure C \ {x₀}) (hZ : IsCompact (ψ '' E)) :
    C ∩ frontier (C ∩ ψ ⁻¹' (H \ fillH (ψ '' E))) ⊆ E := by
  rintro z ⟨hzC, hzf⟩
  by_contra hzE
  have hψc : ContinuousOn ψ C := hψ.1.mono fun w hw => ⟨subset_closure hw, fun h => hx₀ (h ▸ hw)⟩
  have hψz : ψ z ∈ H := hψ.2.2.2.1.2.mapsTo hzC
  have hzcl : z ∈ closure C \ {x₀} := ⟨subset_closure hzC, fun h => hx₀ (h ▸ hzC)⟩
  have hnZ : ψ z ∉ closure (ψ '' E) := by
    rw [hZ.isClosed.closure_eq]
    rintro ⟨e, he, hez⟩
    exact hzE (hψ.2.1 (hE he) hzcl hez ▸ he)
  have hDo : IsOpen (C ∩ ψ ⁻¹' (H \ fillH (ψ '' E))) := by
    refine hψc.isOpen_inter_preimage hCo ?_
    exact InteractingSLE.isOpen_H_diff_fillH hZ.isBounded
  have hzD : z ∉ C ∩ ψ ⁻¹' (H \ fillH (ψ '' E)) := fun h => by
    rw [hDo.frontier_eq] at hzf
    exact hzf.2 h
  have hfill : ψ z ∈ fillH (ψ '' E) := by
    by_contra h
    exact hzD ⟨hzC, hψz, h⟩
  have hbdd : Bornology.IsBounded (connectedComponentIn (H \ closure (ψ '' E)) (ψ z)) :=
    hfill.2.resolve_left hnZ
  set O := connectedComponentIn (H \ closure (ψ '' E)) (ψ z) with hO
  have hOo : IsOpen O := (QuantumZipper.isOpen_H.sdiff isClosed_closure).connectedComponentIn
  have hzO : ψ z ∈ O := mem_connectedComponentIn ⟨hψz, hnZ⟩
  have hOfill : O ⊆ fillH (ψ '' E) := fun w hw => by
    have hwH := connectedComponentIn_subset _ _ hw
    refine ⟨hwH.1, Or.inr ?_⟩
    rwa [← connectedComponentIn_eq hw]
  have hN : IsOpen (C ∩ ψ ⁻¹' O) := hψc.isOpen_inter_preimage hCo hOo
  have hcl := frontier_subset_closure hzf
  rw [_root_.mem_closure_iff] at hcl
  obtain ⟨w, hwN, hwD⟩ := hcl _ hN ⟨hzC, hzO⟩
  exact hwD.2.2 (hOfill hwN.2)

end Frontier

end InteractingSLE.Sec7.R6Safe

namespace InteractingSLE.Sec7.R6Safe

open Sec6 PocketTraversal Lemma71C PocketJordan PocketCoord PocketCoupling PocketStop PocketStopField HOuter
  PocketWordAssembly

/-! ### (a1) The outer pocket -/

section Outer

variable {Ω : Type*} {A : Set Ω} {R L : Ω → ℝ≥0 → ℂ} {r : ℝ≥0} {W : Ω → ℝ → ℝ} {η : Ω → ℝ → ℂ}
  {ψ : Ω → ℂ → ℂ} {n : Ω → ℤ} {q : ℝ≥0} {ω : Ω}

/-- **The current domain of a pocket chart** is `C ∩ ψ⁻¹(ℍ ∖ K_q)` on the live event (any driven traversal). -/
theorem relChart_dom_eq_inter {C : Ω → Set ℂ} {γ : Ω → ℝ → ℂ} (hCo : ∀ ω ∈ A, IsOpen (C ω))
    (hCH : ∀ ω ∈ A, C ω ⊆ H) (hψ : ∀ ω ∈ A, IsConformalBijection (ψ ω) (C ω) H) (hω : ω ∈ A)
    (hγ : IsDrivenCurve (γ ω)) (hq : (q : ℝ≥0∞) < capLife (γ ω)) :
    ((relChart (fun ω => shiftChart (pChart A C ψ ω) (n ω)) γ q ω).dom : Set ℂ) =
      C ω ∩ ψ ω ⁻¹' (H \ QuantumZipper.fwdHull (fun s : ℝ => segDriver (γ ω) s.toNNReal) q) := by
  obtain ⟨hc, hdom, hfwd⟩ := R5Phase.shiftChart_dom_facts hCo hCH hψ n ω hω
  rw [← PocketStopSide.activeDom_eq_relChart_dom (c := fun ω => shiftChart (pChart A C ψ ω) (n ω)) hω hq hγ hc,
    activeDom_eq hω hq]
  refine PocketUnionPt.inv_image_eq_of_image hc hdom hfwd (hψ ω hω).2.injOn inter_subset_left ?_
  rw [image_inter_preimage, (hψ ω hω).2.image_eq]
  exact inter_eq_right.2 sdiff_subset

/-- **(a1) The frontier of an outer pocket's current domain inside the pocket lies on the trace** before the fibre end
of the current relative time: `C ∩ ∂D_C(q) ⊆ η([0, f_R(clockOf L (capInv γ q))])`. -/
theorem outer_frontier_subset_trace (hcfg : ∀ ω ∈ A, IsOuterCfg (R ω) (L ω) r (W ω) (η ω))
    (hψ : ∀ ω ∈ A, IsCfJordan (R ω) (L ω) r (ψ ω)) (hω : ω ∈ A)
    (hq : (q : ℝ≥0∞) < capLife (travAll R L r η ψ ω)) :
    cfPocket (R ω) (L ω) r ∩ frontier ((relChart (fun ω => shiftChart (pChart A (fun ω => cfPocket (R ω) (L ω) r)
        ψ ω) (n ω)) (travAll R L r η ψ) q ω).dom : Set ℂ) ⊆
      η ω '' Icc 0 (pocketFibre (η ω) (cfPocket (R ω) (L ω) r) (firstHit (η ω) (cfArcR (R ω) (L ω) r 1))
        (firstHit (η ω) (cfArcR (R ω) (L ω) r 0))
        (clockOf (pocketClock (η ω) (cfPocket (R ω) (L ω) r) (firstHit (η ω) (cfArcR (R ω) (L ω) r 1))
          (firstHit (η ω) (cfArcR (R ω) (L ω) r 0)) (firstHit (η ω) (cfArcR (R ω) (L ω) r 0)))
          (capInv (travAll R L r η ψ ω) q))) := by
  have hG : ∀ ω ∈ A, IsChangeConfigInc (R ω) (L ω) r := fun ω hω => (hcfg ω hω).conf
  have hCo : ∀ ω ∈ A, IsOpen (cfPocket (R ω) (L ω) r) := fun ω hω =>
    isOpen_image_negInv' (hG ω hω).isOpen_changePocket (hG ω hω).changePocket_subset_H
  have hCH : ∀ ω ∈ A, cfPocket (R ω) (L ω) r ⊆ H := fun ω hω =>
    PocketJordan.image_negInv_subset_H (hG ω hω).changePocket_subset_H
  have hγ : IsDrivenCurve (travAll R L r η ψ ω) := ((hcfg ω hω).props (hψ ω hω)).1
  have hP := (hcfg ω hω).erase
  set C := cfPocket (R ω) (L ω) r with hC
  set τ := firstHit (η ω) (cfArcR (R ω) (L ω) r 1) with hτ
  set σ := firstHit (η ω) (cfArcR (R ω) (L ω) r 0) with hσ
  set Lc := pocketClock (η ω) C τ σ σ with hLc
  set u := capInv (travAll R L r η ψ ω) q with hu
  have hL : 0 < Lc := hP.clock_σ_pos
  have hu0 : 0 ≤ u := capInv_nonneg _ _
  have hv := clockOf_mem_Ico hL hu0
  have hJ : IsJordanCoord C (cfArcR (R ω) (L ω) r 0) (cfArcR (R ω) (L ω) r 1) (ψ ω) := by
    rw [IsChangeConfigInc.cfArcR_zero, IsChangeConfigInc.cfArcR_one]; exact hψ ω hω
  rw [relChart_dom_eq_inter (n := n) hCo hCH (fun ω hω => (hψ ω hω).2.2.2.1) hω hγ hq,
    hγ.fwdHull_segDriver q.coe_nonneg (by rw [ENNReal.ofReal_coe_nnreal]; exact hq)]
  have himg : travAll R L r η ψ ω '' Icc 0 u = ψ ω '' (erasedPath (η ω) C τ σ '' Icc 0 (clockOf Lc u)) := by
    change relCurve (fun v => ψ ω (erasedPath (η ω) C τ σ v)) Lc '' Icc 0 u = _
    rw [image_relCurve_Icc _ hL hu0, image_image]
  rw [himg]
  have hE : erasedPath (η ω) C τ σ '' Icc 0 (clockOf Lc u) ⊆ closure C \ {cfArcR (R ω) (L ω) r 0} := by
    rintro _ ⟨v, hvI, rfl⟩
    exact hP.erasedPath_mem ⟨hvI.1, hvI.2.trans_lt hv.2⟩
  have hcont : ContinuousOn (fun v => ψ ω (erasedPath (η ω) C τ σ v)) (Icc 0 (clockOf Lc u)) :=
    hJ.1.comp (hP.continuousOn_erasedPath.mono (Icc_subset_Icc_right hv.2.le)) fun v hvI =>
      hE ⟨v, hvI, rfl⟩
  have hZ : IsCompact (ψ ω '' (erasedPath (η ω) C τ σ '' Icc 0 (clockOf Lc u))) := by
    rw [image_image]
    exact isCompact_Icc.image_of_continuousOn hcont
  intro z hz
  have hzE := inter_frontier_subset_of_fillH (hCo ω hω) hJ hP.notMem_x hE hZ hz
  have hmem : z ∈ erasedPath (η ω) C τ σ '' Icc 0 (clockOf Lc u) ∩ C := ⟨hzE, hz.1⟩
  rw [hP.erasedPath_image_inter ⟨hv.1, hv.2.le⟩] at hmem
  exact hmem.1

end Outer

/-! ### (a2) The inner contained pocket: a rational relative time after a given visit time -/

section Inner

variable {Ω : Type*} {A : Set Ω} {R L : Ω → ℝ≥0 → ℂ} {r : ℝ≥0} {W : Ω → ℝ → ℝ} {η : Ω → ℝ → ℂ}
  {ψ : Ω → ℂ → ℂ} {ω : Ω}

/-- **(a2) A rational live relative time with left stop after a given ambient time** (bounded contained pocket): for
`T ∈ [τ, σ)` some positive rational `q'` below the relative lifetime has `T < T⁰(q')` (any `q'` above the relative
capacity reached at `T`, `R5Ref`'s `ambTime0_le_iff`). -/
theorem exists_rat_lt_leftStop (hcfg : IsCfPocketConfig (R ω) (L ω) r (W ω) (η ω))
    (hψ : IsCfJordan (R ω) (L ω) r (ψ ω)) {T : ℝ}
    (hT : T ∈ Ico (firstHit (η ω) (cfArcR (R ω) (L ω) r 1)) (firstHit (η ω) (cfArcR (R ω) (L ω) r 0))) :
    ∃ q' : ℚ, 0 < q' ∧ ((StripSys.rt q' : ℝ≥0) : ℝ≥0∞) < capLife (travAll R L r η ψ ω) ∧
      T < R5Ref.leftStop R L r η ψ (StripSys.rt q') ω := by
  obtain ⟨hP, hJ⟩ := R5Ref.pocket_of_cfg hcfg hψ
  have hlt := PocketStopMarked.relCap_lt_capLife hP hcfg.attach hJ hT
  have hc0 : 0 ≤ PocketStopMarked.relCap (η ω) (cfPocket (R ω) (L ω) r) (firstHit (η ω) (cfArcR (R ω) (L ω) r 1))
      (firstHit (η ω) (cfArcR (R ω) (L ω) r 0)) (ψ ω) T :=
    (isDrivenCurve_relCurve_of_isReversePocket hP hcfg.attach hJ).capClock_nonneg
      (PocketStopMarked.relTime_nonneg hP hcfg.attach hT)
  obtain ⟨q', hq'0, hlo, hhi⟩ := ENNReal.lt_iff_exists_rat_btwn.1 hlt
  have hlo' : PocketStopMarked.relCap (η ω) (cfPocket (R ω) (L ω) r) (firstHit (η ω) (cfArcR (R ω) (L ω) r 1))
      (firstHit (η ω) (cfArcR (R ω) (L ω) r 0)) (ψ ω) T < (q' : ℝ) := by
    rw [ENNReal.ofReal, ENNReal.coe_lt_coe, Real.toNNReal_lt_toNNReal_iff' ] at hlo
    exact hlo.1
  have hqpos : (0 : ℝ) < q' := hc0.trans_lt hlo'
  refine ⟨q', by exact_mod_cast hqpos, hhi, ?_⟩
  have hq0 : (0 : ℝ) ≤ ((StripSys.rt q' : ℝ≥0) : ℝ) := NNReal.coe_nonneg _
  have hqlive : ENNReal.ofReal ((StripSys.rt q' : ℝ≥0) : ℝ) < capLife (travAll R L r η ψ ω) := by
    rwa [ENNReal.ofReal_coe_nnreal]
  have hrt : ((StripSys.rt q' : ℝ≥0) : ℝ) = q' := Real.coe_toNNReal _ hqpos.le
  by_contra hle
  have h := (PocketStopMarked.ambTime0_le_iff hP hcfg.attach hJ hq0 hqlive hT).1 (not_lt.1 hle)
  rw [hrt] at h
  linarith

end Inner

/-! ### The inclusion of the two current domains up to one common point -/

section Incl

variable {Ω : Type*} {A A' : Set Ω} {R L R' L' : Ω → ℝ≥0 → ℂ} {r r' : ℝ≥0} {W : Ω → ℝ → ℝ}
  {η : Ω → ℝ → ℂ} {ψ ψ' : Ω → ℂ → ℂ} {n n' : Ω → ℤ} {q q' : ℝ≥0} {ω : Ω}

/-- **The inner current domain lies in the outer one** (outer pocket `C` at `q`, contained pocket `U ⊆ C` at `q'`):
when the left stop of `U` at `q'` is after the fibre end of `C` at `q` and the two current domains meet. The outer
frontier inside `C` lies on `η([0, T_C])` (`outer_frontier_subset_trace`), which `U`'s current domain
`U ∩ (ℍ ∖ fill η([0, T⁰_U(q')]))` (`R5Ref.current_dom_eq`) misses. -/
theorem inner_dom_subset_outer_dom (hcfg : ∀ ω ∈ A, IsOuterCfg (R ω) (L ω) r (W ω) (η ω))
    (hψ : ∀ ω ∈ A, IsCfJordan (R ω) (L ω) r (ψ ω)) (hω : ω ∈ A)
    (hq : (q : ℝ≥0∞) < capLife (travAll R L r η ψ ω))
    (hcfg' : ∀ ω ∈ A', IsCfPocketConfig (R' ω) (L' ω) r' (W ω) (η ω))
    (hψ' : ∀ ω ∈ A', IsCfJordan (R' ω) (L' ω) r' (ψ' ω)) (hω' : ω ∈ A')
    (hq' : (q' : ℝ≥0∞) < capLife (travAll R' L' r' η ψ' ω))
    (hsub : cfPocket (R' ω) (L' ω) r' ⊆ cfPocket (R ω) (L ω) r)
    (hT : pocketFibre (η ω) (cfPocket (R ω) (L ω) r) (firstHit (η ω) (cfArcR (R ω) (L ω) r 1))
        (firstHit (η ω) (cfArcR (R ω) (L ω) r 0))
        (clockOf (pocketClock (η ω) (cfPocket (R ω) (L ω) r) (firstHit (η ω) (cfArcR (R ω) (L ω) r 1))
          (firstHit (η ω) (cfArcR (R ω) (L ω) r 0)) (firstHit (η ω) (cfArcR (R ω) (L ω) r 0)))
          (capInv (travAll R L r η ψ ω) q)) ≤ R5Ref.leftStop R' L' r' η ψ' q' ω)
    (hmeet : (((relChart (fun ω => shiftChart (pChart A' (fun ω => cfPocket (R' ω) (L' ω) r') ψ' ω) (n' ω))
        (travAll R' L' r' η ψ') q' ω).dom : Set ℂ) ∩
      (relChart (fun ω => shiftChart (pChart A (fun ω => cfPocket (R ω) (L ω) r) ψ ω) (n ω))
        (travAll R L r η ψ) q ω).dom).Nonempty) :
    ((relChart (fun ω => shiftChart (pChart A' (fun ω => cfPocket (R' ω) (L' ω) r') ψ' ω) (n' ω))
        (travAll R' L' r' η ψ') q' ω).dom : Set ℂ) ⊆
      (relChart (fun ω => shiftChart (pChart A (fun ω => cfPocket (R ω) (L ω) r) ψ ω) (n ω))
        (travAll R L r η ψ) q ω).dom := by
  have hG' : ∀ ω ∈ A', IsChangeConfigInc (R' ω) (L' ω) r' := fun ω hω => (hcfg' ω hω).conf
  obtain ⟨hc', hdom', heq'⟩ := R5Phase.shiftChart_dom_facts
    (fun ω hω => isOpen_image_negInv' (hG' ω hω).isOpen_changePocket (hG' ω hω).changePocket_subset_H)
    (fun ω hω => PocketJordan.image_negInv_subset_H (hG' ω hω).changePocket_subset_H)
    (fun ω hω => (hψ' ω hω).2.2.2.1) n' ω hω'
  have hI : (relChart (fun ω => shiftChart (pChart A' (fun ω => cfPocket (R' ω) (L' ω) r') ψ' ω) (n' ω))
      (travAll R' L' r' η ψ') q' ω).IsConformal :=
    PocketStopSide.isConformal_relChart_of_driven ((hcfg' ω hω').isDrivenCurve (hψ' ω hω')).1 hq' hc'
  refine dom_subset_of_frontier_disjoint hI (disjoint_left.2 fun z hzI hzf => ?_) hmeet
  have hzI' := hzI
  rw [R5Ref.current_dom_eq (c := fun ω => shiftChart (pChart A' (fun ω => cfPocket (R' ω) (L' ω) r') ψ' ω) (n' ω))
    hω' (hcfg' ω hω') (hψ' ω hω') hc' hdom' heq' hq'] at hzI'
  have hzT := outer_frontier_subset_trace (n := n) hcfg hψ hω hq ⟨hsub hzI'.1, hzf⟩
  obtain ⟨t, ht, hte⟩ := hzT
  refine hzI'.2.2 ⟨hzI'.2.1, Or.inl (subset_closure ⟨t, ⟨ht.1, ht.2.trans hT⟩, hte⟩)⟩

end Incl

/-! ### The two-outer-arm case: the inner pocket `V` is outer -/

section Two

variable {Ω : Type*} {A A' : Set Ω} {R L R' L' : Ω → ℝ≥0 → ℂ} {r r' : ℝ≥0} {W : Ω → ℝ → ℝ}
  {η : Ω → ℝ → ℂ} {ψ ψ' : Ω → ℂ → ℂ} {n n' : Ω → ℤ} {q q' : ℝ≥0} {ω : Ω}

/-- **(a2) for an outer pocket**: for `T ∈ [τ, σ)` some positive rational live relative time `q'` has `T < T⁰(q')`
(`PocketStopMarked.Outer.ambTime0_le_iff`). -/
theorem exists_rat_lt_ambTime0_outer (hcfg : IsOuterCfg (R ω) (L ω) r (W ω) (η ω))
    (hψ : IsCfJordan (R ω) (L ω) r (ψ ω)) {T : ℝ}
    (hT : T ∈ Ico (firstHit (η ω) (cfArcR (R ω) (L ω) r 1)) (firstHit (η ω) (cfArcR (R ω) (L ω) r 0))) :
    ∃ q' : ℚ, 0 < q' ∧ ((StripSys.rt q' : ℝ≥0) : ℝ≥0∞) < capLife (travAll R L r η ψ ω) ∧
      T < PocketStopWallsFin.ambTime0 (η ω) (cfPocket (R ω) (L ω) r) (firstHit (η ω) (cfArcR (R ω) (L ω) r 1))
        (firstHit (η ω) (cfArcR (R ω) (L ω) r 0)) (ψ ω) (StripSys.rt q') := by
  have hP := hcfg.toPocket hψ
  have hlt := PocketStopMarked.Outer.relCap_lt_capLife hP hT
  have hc0 : 0 ≤ PocketStopMarked.relCap (η ω) (cfPocket (R ω) (L ω) r) (firstHit (η ω) (cfArcR (R ω) (L ω) r 1))
      (firstHit (η ω) (cfArcR (R ω) (L ω) r 0)) (ψ ω) T :=
    hP.driven.capClock_nonneg (PocketStopMarked.Outer.relTime_nonneg hP hT)
  obtain ⟨q', hq'0, hlo, hhi⟩ := ENNReal.lt_iff_exists_rat_btwn.1 hlt
  have hlo' : PocketStopMarked.relCap (η ω) (cfPocket (R ω) (L ω) r) (firstHit (η ω) (cfArcR (R ω) (L ω) r 1))
      (firstHit (η ω) (cfArcR (R ω) (L ω) r 0)) (ψ ω) T < (q' : ℝ) := by
    rw [ENNReal.ofReal, ENNReal.coe_lt_coe, Real.toNNReal_lt_toNNReal_iff' ] at hlo
    exact hlo.1
  have hqpos : (0 : ℝ) < q' := hc0.trans_lt hlo'
  refine ⟨q', by exact_mod_cast hqpos, hhi, ?_⟩
  have hq0 : (0 : ℝ) ≤ ((StripSys.rt q' : ℝ≥0) : ℝ) := NNReal.coe_nonneg _
  have hqlive : ENNReal.ofReal ((StripSys.rt q' : ℝ≥0) : ℝ) < capLife (travAll R L r η ψ ω) := by
    rwa [ENNReal.ofReal_coe_nnreal]
  have hrt : ((StripSys.rt q' : ℝ≥0) : ℝ) = q' := Real.coe_toNNReal _ hqpos.le
  by_contra hle
  have h := (PocketStopMarked.Outer.ambTime0_le_iff hP hq0 hqlive hT).1 (not_lt.1 hle)
  rw [hrt] at h
  linarith

/-- **The inner current domain lies in the outer one, inner pocket outer and bounded** (two outer arms: `C` at `q`,
`V ⊆ C` at `q'`): when the left stop of `V` at `q'` is after the fibre end of `C` at `q` and the two current domains
meet. `V`'s current domain lies in `ℍ ∖ fill η([0, T⁰_V(q')])` (`HOuter.relDomain_subset_domain_ambTime0`). -/
theorem inner_dom_subset_outer_dom_two (hcfg : ∀ ω ∈ A, IsOuterCfg (R ω) (L ω) r (W ω) (η ω))
    (hψ : ∀ ω ∈ A, IsCfJordan (R ω) (L ω) r (ψ ω)) (hω : ω ∈ A)
    (hq : (q : ℝ≥0∞) < capLife (travAll R L r η ψ ω))
    (hcfg' : ∀ ω ∈ A', IsOuterCfg (R' ω) (L' ω) r' (W ω) (η ω))
    (hψ' : ∀ ω ∈ A', IsCfJordan (R' ω) (L' ω) r' (ψ' ω)) (hω' : ω ∈ A')
    (hq' : (q' : ℝ≥0∞) < capLife (travAll R' L' r' η ψ' ω))
    (hsub : cfPocket (R' ω) (L' ω) r' ⊆ cfPocket (R ω) (L ω) r)
    (hT : pocketFibre (η ω) (cfPocket (R ω) (L ω) r) (firstHit (η ω) (cfArcR (R ω) (L ω) r 1))
        (firstHit (η ω) (cfArcR (R ω) (L ω) r 0))
        (clockOf (pocketClock (η ω) (cfPocket (R ω) (L ω) r) (firstHit (η ω) (cfArcR (R ω) (L ω) r 1))
          (firstHit (η ω) (cfArcR (R ω) (L ω) r 0)) (firstHit (η ω) (cfArcR (R ω) (L ω) r 0)))
          (capInv (travAll R L r η ψ ω) q)) ≤
      PocketStopWallsFin.ambTime0 (η ω) (cfPocket (R' ω) (L' ω) r') (firstHit (η ω) (cfArcR (R' ω) (L' ω) r' 1))
        (firstHit (η ω) (cfArcR (R' ω) (L' ω) r' 0)) (ψ' ω) q')
    (hmeet : (((relChart (fun ω => shiftChart (pChart A' (fun ω => cfPocket (R' ω) (L' ω) r') ψ' ω) (n' ω))
        (travAll R' L' r' η ψ') q' ω).dom : Set ℂ) ∩
      (relChart (fun ω => shiftChart (pChart A (fun ω => cfPocket (R ω) (L ω) r) ψ ω) (n ω))
        (travAll R L r η ψ) q ω).dom).Nonempty) :
    ((relChart (fun ω => shiftChart (pChart A' (fun ω => cfPocket (R' ω) (L' ω) r') ψ' ω) (n' ω))
        (travAll R' L' r' η ψ') q' ω).dom : Set ℂ) ⊆
      (relChart (fun ω => shiftChart (pChart A (fun ω => cfPocket (R ω) (L ω) r) ψ ω) (n ω))
        (travAll R L r η ψ) q ω).dom := by
  have hG' : ∀ ω ∈ A', IsChangeConfigInc (R' ω) (L' ω) r' := fun ω hω => (hcfg' ω hω).conf
  have hCo' : ∀ ω ∈ A', IsOpen (cfPocket (R' ω) (L' ω) r') := fun ω hω =>
    isOpen_image_negInv' (hG' ω hω).isOpen_changePocket (hG' ω hω).changePocket_subset_H
  have hCH' : ∀ ω ∈ A', cfPocket (R' ω) (L' ω) r' ⊆ H := fun ω hω =>
    PocketJordan.image_negInv_subset_H (hG' ω hω).changePocket_subset_H
  obtain ⟨hc', -, -⟩ := R5Phase.shiftChart_dom_facts hCo' hCH' (fun ω hω => (hψ' ω hω).2.2.2.1) n' ω hω'
  have hγ' : IsDrivenCurve (travAll R' L' r' η ψ' ω) := ((hcfg' ω hω').props (hψ' ω hω')).1
  have hI : (relChart (fun ω => shiftChart (pChart A' (fun ω => cfPocket (R' ω) (L' ω) r') ψ' ω) (n' ω))
      (travAll R' L' r' η ψ') q' ω).IsConformal := PocketStopSide.isConformal_relChart_of_driven hγ' hq' hc'
  refine dom_subset_of_frontier_disjoint hI (disjoint_left.2 fun z hzI hzf => ?_) hmeet
  have hzI' := hzI
  rw [relChart_dom_eq_inter (n := n') hCo' hCH' (fun ω hω => (hψ' ω hω).2.2.2.1) hω' hγ' hq'] at hzI'
  have hc := hcfg' ω hω'
  have hJ : IsJordanCoord (cfPocket (R' ω) (L' ω) r') (cfArcR (R' ω) (L' ω) r' 0) (cfArcR (R' ω) (L' ω) r' 1)
      (ψ' ω) := by
    rw [IsChangeConfigInc.cfArcR_zero, IsChangeConfigInc.cfArcR_one]; exact hψ' ω hω'
  have hCb : Bornology.IsBounded (cfPocket (R' ω) (L' ω) r') :=
    isBounded_image_negInv (PocketMarks.zero_notMem_closure_of_rightLo_pos hc.conf hc.bounded)
  have hdom := relDomain_subset_domain_ambTime0 hc.erase hc.trace hc.continuous_W hc.W_zero (hCH' ω hω') hCb hJ hγ'
    q'.coe_nonneg (by rw [ENNReal.ofReal_coe_nnreal]; exact hq') hzI'
  have hzT := outer_frontier_subset_trace (n := n) hcfg hψ hω hq ⟨hsub hzI'.1, hzf⟩
  obtain ⟨t, ht, hte⟩ := hzT
  rw [hc.trace.2.2 _ ((hc.erase.nonneg).trans (PocketStopMarked.Outer.ambTime0_mem_Ico (hc.toPocket (hψ' ω hω'))
    q'.coe_nonneg (by rw [ENNReal.ofReal_coe_nnreal]; exact hq')).1)] at hdom
  exact hdom.2 ⟨hdom.1, Or.inl (subset_closure ⟨t, ⟨ht.1, ht.2.trans hT⟩, hte⟩)⟩

end Two


/-! ### The face with the inclusion reduced to one common point (bounded shapes) -/

section FaceQ

open MeasureTheory ProbabilityTheory
open LQGMetric (DistOn)
open QuantumZipper (chiC)
open scoped Real
open WholeField R7Outer R7Leaves R6Nest R6Rel R6Cert HOuter PocketMarks PocketSeedOpen PocketStopWallsFin PocketStopSide

universe u

/-- **The positional face without its inclusion conjunct** (`R6FaceP = (inner ⊆ outer) ∧ R6FaceR`). -/
def R6FaceR (ρL ρR σL σR vL vR wL wR : Fin 1 → ℝ) (outer inner : Chart) (EC EU : Set ℂ) : Prop :=
  ∃ (J : Set ℝ) (y₀ η₀ ξ η : ℝ), IsOpen J ∧ IsPreconnected J ∧
    (∀ x ∈ J, ∃ r > 0, H ∩ ball (x : ℂ) r ⊆ ((pocketTransitionChart outer inner).dom : Set ℂ)) ∧
    (∀ x ∈ J, ∃ M : ℝ, ∀ᶠ z in 𝓝[((pocketTransitionChart outer inner).dom : Set ℂ)] (x : ℂ),
      ‖(pocketTransitionChart outer inner).1 z‖ ≤ M) ∧
    y₀ ∈ J ∧ ξ ∈ J ∧
    Tendsto (pocketTransitionChart outer inner).1
      (𝓝[((pocketTransitionChart outer inner).dom : Set ℂ)] (y₀ : ℂ)) (𝓝 (η₀ : ℂ)) ∧
    Tendsto (pocketTransitionChart outer inner).1
      (𝓝[((pocketTransitionChart outer inner).dom : Set ℂ)] (ξ : ℂ)) (𝓝 (η : ℂ)) ∧
    ((vR 0 < y₀ ∧ wR 0 < η₀ ∧ ρR 0 = σR 0) ∨ (y₀ < vL 0 ∧ η₀ < wL 0 ∧ ρL 0 = σL 0)) ∧
    ((0 < ξ ∧ ξ < vR 0 ∧ 0 < η ∧ η < wR 0) ∨ (vL 0 < ξ ∧ ξ < 0 ∧ wL 0 < η ∧ η < 0)) ∧
    (∀ p : ℂ, Tendsto outer.2.1 (𝓝[H] (y₀ : ℂ)) (𝓝 p) → ∃ ε > 0, EU ∩ ball p ε ⊆ EC) ∧
    (∀ p : ℂ, Tendsto outer.2.1 (𝓝[H] (ξ : ℂ)) (𝓝 p) → ∃ ε > 0, EU ∩ ball p ε ⊆ EC)

/-- `R6FaceP` is the inclusion of the two current domains together with `R6FaceR`. -/
theorem r6FaceP_iff {ρL ρR σL σR vL vR wL wR : Fin 1 → ℝ} {outer inner : Chart} {EC EU : Set ℂ} :
    R6FaceP ρL ρR σL σR vL vR wL wR outer inner EC EU ↔
      (inner.dom : Set ℂ) ⊆ outer.dom ∧ R6FaceR ρL ρR σL σR vL vR wL wR outer inner EC EU := Iff.rfl

/-- **Named, unproved: R.6's face, shape `Mixed`, with the inclusion reduced to one common point**:
`R6FacePMixedRemaining` with the inclusion of the two current domains replaced by the time ordering of the hulls
(the fibre end of `C` at `q` before the left stop of the inner pocket at `q'`) and one common point
(`r6FacePMixedRemaining_of_faceQ`). -/
def R6FaceQMixedRemaining (k rL rR c c' : ℝ) : Prop :=
  (k / 2 - 4 < rL ∧ rR ≤ k / 2 - 4) ∨ (rL ≤ k / 2 - 4 ∧ k / 2 - 4 < rR) →
  ∀ {Ω : Type u} [MeasurableSpace Ω] [StandardBorelSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (h : Ω → DistOn upperHalfPlaneOpens) (W' : ℝ≥0 → Ω → ℝ) (ζ' : Ω → ℝ≥0∞)
    (αR βR βL αL : Ω → ℝ≥0 → ℂ) (ζαR ζβR ζβL ζαL : Ω → ℝ≥0∞),
    IsR7OuterConfig k rL rR c c' P h W' ζ' αR βR βL αL ζαR ζβR ζβL ζαL →
    ∀ (R L : Ω → ℝ≥0 → ℂ) (η : Ω → ℝ → ℂ), IsR7Versions P W' αR αL R L η →
    ∀ MR ML : Ω → ℝ≥0 → ℂ, IsFrontierVersion P βR MR → IsFrontierVersion P βL ML →
    ∀ (r : ℝ≥0) (A A' : Set Ω) (ψ ψ' : Ω → ℂ → ℂ) (n n' : Ω → ℤ) (s q : ℚ),
      (∀ ω ∈ A, IsOuterCfg (R ω) (L ω) r (fun t : ℝ => W' t.toNNReal ω) (η ω) ∧
        IsCfJordan (R ω) (L ω) r (ψ ω)) →
      (∀ ω ∈ A', IsCfPocketConfig (innerRight k rL R MR ω) (innerLeft k rR L ML ω) (StripSys.rt s)
          (fun t : ℝ => W' t.toNNReal ω) (η ω) ∧
        IsCfJordan (innerRight k rL R MR ω) (innerLeft k rR L ML ω) (StripSys.rt s) (ψ' ω)) →
      ∀ᵐ ω ∂P, ω ∈ A → ω ∈ A' →
        ω ∈ nestRelEvent R L r η ψ MR ML (innerRight k rL R MR) (innerLeft k rR L ML) s q →
        ∃ q' : ℚ, ((StripSys.rt q' : ℝ≥0) : ℝ≥0∞) <
            capLife (travAll (innerRight k rL R MR) (innerLeft k rR L ML) (StripSys.rt s) η ψ' ω) ∧
          pocketFibre (η ω) (cfPocket (R ω) (L ω) r) (firstHit (η ω) (cfArcR (R ω) (L ω) r 1))
              (firstHit (η ω) (cfArcR (R ω) (L ω) r 0))
              (clockOf (pocketClock (η ω) (cfPocket (R ω) (L ω) r) (firstHit (η ω) (cfArcR (R ω) (L ω) r 1))
                (firstHit (η ω) (cfArcR (R ω) (L ω) r 0)) (firstHit (η ω) (cfArcR (R ω) (L ω) r 0)))
                (capInv (travAll R L r η ψ ω) (StripSys.rt q))) ≤
            R5Ref.leftStop (innerRight k rL R MR) (innerLeft k rR L ML) (StripSys.rt s) η ψ' (StripSys.rt q') ω ∧
          (((relChart (fun ω => shiftChart (pChart A' (fun ω => cfPocket (innerRight k rL R MR ω)
                (innerLeft k rR L ML ω) (StripSys.rt s)) ψ' ω) (n' ω))
              (travAll (innerRight k rL R MR) (innerLeft k rR L ML) (StripSys.rt s) η ψ') (StripSys.rt q')
                ω).dom : Set ℂ) ∩
            (relChart (fun ω => shiftChart (pChart A (fun ω => cfPocket (R ω) (L ω) r) ψ ω) (n ω))
              (travAll R L r η ψ) (StripSys.rt q) ω).dom).Nonempty ∧
          R6FaceR (fun _ : Fin 1 => rL) (fun _ : Fin 1 => rR) (fun _ : Fin 1 => innerRight k rL rL (k / 2 - 4))
            (fun _ : Fin 1 => innerLeft k rR rR (k / 2 - 4))
            (fun i => geomLW (fun t ω => segDriver (travAll R L r η ψ ω) t) (fun _ => LP.twoSeedXL) i
              (StripSys.rt q) ω - segDriver (travAll R L r η ψ ω) (StripSys.rt q))
            (fun j => geomRW (fun t ω => segDriver (travAll R L r η ψ ω) t) (fun _ => LP.twoSeedXR) j
              (StripSys.rt q) ω - segDriver (travAll R L r η ψ ω) (StripSys.rt q))
            (fun i => geomLW (fun t ω => segDriver (travAll (innerRight k rL R MR) (innerLeft k rR L ML)
                (StripSys.rt s) η ψ' ω) t) (fun _ => LP.twoSeedXL) i (StripSys.rt q') ω -
              segDriver (travAll (innerRight k rL R MR) (innerLeft k rR L ML) (StripSys.rt s) η ψ' ω)
                (StripSys.rt q'))
            (fun j => geomRW (fun t ω => segDriver (travAll (innerRight k rL R MR) (innerLeft k rR L ML)
                (StripSys.rt s) η ψ' ω) t) (fun _ => LP.twoSeedXR) j (StripSys.rt q') ω -
              segDriver (travAll (innerRight k rL R MR) (innerLeft k rR L ML) (StripSys.rt s) η ψ' ω)
                (StripSys.rt q'))
            (relChart (fun ω => shiftChart (pChart A (fun ω => cfPocket (R ω) (L ω) r) ψ ω) (n ω))
              (travAll R L r η ψ) (StripSys.rt q) ω)
            (relChart (fun ω => shiftChart (pChart A' (fun ω => cfPocket (innerRight k rL R MR ω)
                (innerLeft k rR L ML ω) (StripSys.rt s)) ψ' ω) (n' ω))
              (travAll (innerRight k rL R MR) (innerLeft k rR L ML) (StripSys.rt s) η ψ') (StripSys.rt q') ω)
            (pocketSet A R L r η ψ n (StripSys.rt q) ω)
            (pocketSet A' (innerRight k rL R MR) (innerLeft k rR L ML) (StripSys.rt s) η ψ' n' (StripSys.rt q') ω)

/-- **`R6FacePMixedRemaining` from the face with one common point** (`inner_dom_subset_outer_dom`). -/
theorem r6FacePMixedRemaining_of_faceQ {k rL rR c c' : ℝ} (hQ : R6FaceQMixedRemaining.{u} k rL rR c c') :
    R6FacePMixedRemaining.{u} k rL rR c c' := by
  intro hmix Ω _ _ P _ h W' ζ' αR βR βL αL ζαR ζβR ζβL ζαL hcfg R L η hV MR ML hMR hML r A A' ψ ψ' n n' s q hA
    hA'
  filter_upwards [hQ hmix P h W' ζ' αR βR βL αL ζαR ζβR ζβL ζαL hcfg R L η hV MR ML hMR hML r A A' ψ ψ' n n' s q
    hA hA'] with ω hω hωA hωA' hωN
  obtain ⟨q', hq', hT, hmeet, hR⟩ := hω hωA hωA' hωN
  exact ⟨q', hq', inner_dom_subset_outer_dom (fun ω hω => (hA ω hω).1) (fun ω hω => (hA ω hω).2) hωA hωN.2.1
    (fun ω hω => (hA' ω hω).1) (fun ω hω => (hA' ω hω).2) hωA' hq' hωN.2.2.2.1 hT hmeet, hR⟩

/-- **Named, unproved: R.6's face, shape `Two`, with the inclusion reduced to one common point**:
`R6FacePTwoRemaining` with the inclusion of the two current domains replaced by the time ordering of the hulls
(the fibre end of `C` at `q` before the left stop of the inner pocket at `q'`) and one common point
(`r6FacePTwoRemaining_of_faceQ`). -/
def R6FaceQTwoRemaining (k rL rR c c' : ℝ) : Prop :=
  k / 2 - 4 < rL → k / 2 - 4 < rR →
  ∀ {Ω : Type u} [MeasurableSpace Ω] [StandardBorelSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (h : Ω → DistOn upperHalfPlaneOpens) (W' : ℝ≥0 → Ω → ℝ) (ζ' : Ω → ℝ≥0∞)
    (αR βR βL αL : Ω → ℝ≥0 → ℂ) (ζαR ζβR ζβL ζαL : Ω → ℝ≥0∞),
    IsR7OuterConfig k rL rR c c' P h W' ζ' αR βR βL αL ζαR ζβR ζβL ζαL →
    ∀ (R L : Ω → ℝ≥0 → ℂ) (η : Ω → ℝ → ℂ), IsR7Versions P W' αR αL R L η →
    ∀ MR ML : Ω → ℝ≥0 → ℂ, IsFrontierVersion P βR MR → IsFrontierVersion P βL ML →
    ∀ (r : ℝ≥0) (A A' : Set Ω) (ψ ψ' : Ω → ℂ → ℂ) (n n' : Ω → ℤ) (s q : ℚ),
      (∀ ω ∈ A, IsOuterCfg (R ω) (L ω) r (fun t : ℝ => W' t.toNNReal ω) (η ω) ∧
        IsCfJordan (R ω) (L ω) r (ψ ω)) →
      (∀ ω ∈ A', IsOuterCfg (R ω) (ML ω) (StripSys.rt s)
          (fun t : ℝ => W' t.toNNReal ω) (η ω) ∧
        IsCfJordan (R ω) (ML ω) (StripSys.rt s) (ψ' ω)) →
      ∀ᵐ ω ∂P, ω ∈ A → ω ∈ A' →
        ω ∈ nestRelEvent R L r η ψ MR ML R ML s q →
        ∃ q' : ℚ, ((StripSys.rt q' : ℝ≥0) : ℝ≥0∞) <
            capLife (travAll R ML (StripSys.rt s) η ψ' ω) ∧
          pocketFibre (η ω) (cfPocket (R ω) (L ω) r) (firstHit (η ω) (cfArcR (R ω) (L ω) r 1))
              (firstHit (η ω) (cfArcR (R ω) (L ω) r 0))
              (clockOf (pocketClock (η ω) (cfPocket (R ω) (L ω) r) (firstHit (η ω) (cfArcR (R ω) (L ω) r 1))
                (firstHit (η ω) (cfArcR (R ω) (L ω) r 0)) (firstHit (η ω) (cfArcR (R ω) (L ω) r 0)))
                (capInv (travAll R L r η ψ ω) (StripSys.rt q))) ≤
            PocketStopWallsFin.ambTime0 (η ω) (cfPocket (R ω) (ML ω) (StripSys.rt s))
              (firstHit (η ω) (cfArcR (R ω) (ML ω) (StripSys.rt s) 1))
              (firstHit (η ω) (cfArcR (R ω) (ML ω) (StripSys.rt s) 0)) (ψ' ω) (StripSys.rt q') ∧
          (((relChart (fun ω => shiftChart (pChart A' (fun ω => cfPocket (R ω)
                (ML ω) (StripSys.rt s)) ψ' ω) (n' ω))
              (travAll R ML (StripSys.rt s) η ψ') (StripSys.rt q') ω).dom : Set ℂ) ∩
            (relChart (fun ω => shiftChart (pChart A (fun ω => cfPocket (R ω) (L ω) r) ψ ω) (n ω))
              (travAll R L r η ψ) (StripSys.rt q) ω).dom).Nonempty ∧
          R6FaceR (fun _ : Fin 1 => rL) (fun _ : Fin 1 => rR) (fun _ : Fin 1 => rL)
            (fun _ : Fin 1 => k / 2 - 4)
            (fun i => geomLW (fun t ω => segDriver (travAll R L r η ψ ω) t) (fun _ => LP.twoSeedXL) i
              (StripSys.rt q) ω - segDriver (travAll R L r η ψ ω) (StripSys.rt q))
            (fun j => geomRW (fun t ω => segDriver (travAll R L r η ψ ω) t) (fun _ => LP.twoSeedXR) j
              (StripSys.rt q) ω - segDriver (travAll R L r η ψ ω) (StripSys.rt q))
            (fun i => geomLW (fun t ω => segDriver (travAll R ML
                (StripSys.rt s) η ψ' ω) t) (fun _ => LP.twoSeedXL) i (StripSys.rt q') ω -
              segDriver (travAll R ML (StripSys.rt s) η ψ' ω)
                (StripSys.rt q'))
            (fun j => geomRW (fun t ω => segDriver (travAll R ML
                (StripSys.rt s) η ψ' ω) t) (fun _ => LP.twoSeedXR) j (StripSys.rt q') ω -
              segDriver (travAll R ML (StripSys.rt s) η ψ' ω)
                (StripSys.rt q'))
            (relChart (fun ω => shiftChart (pChart A (fun ω => cfPocket (R ω) (L ω) r) ψ ω) (n ω))
              (travAll R L r η ψ) (StripSys.rt q) ω)
            (relChart (fun ω => shiftChart (pChart A' (fun ω => cfPocket (R ω)
                (ML ω) (StripSys.rt s)) ψ' ω) (n' ω))
              (travAll R ML (StripSys.rt s) η ψ') (StripSys.rt q') ω)
            (pocketSet A R L r η ψ n (StripSys.rt q) ω)
            (pocketSet A' R ML (StripSys.rt s) η ψ' n' (StripSys.rt q') ω)

/-- **`R6FacePTwoRemaining` from the face with one common point** (`inner_dom_subset_outer_dom_two`). -/
theorem r6FacePTwoRemaining_of_faceQ {k rL rR c c' : ℝ} (hQ : R6FaceQTwoRemaining.{u} k rL rR c c') :
    R6FacePTwoRemaining.{u} k rL rR c c' := by
  intro hdL hdR Ω _ _ P _ h W' ζ' αR βR βL αL ζαR ζβR ζβL ζαL hcfg R L η hV MR ML hMR hML r A A' ψ ψ' n n' s q hA
    hA'
  filter_upwards [hQ hdL hdR P h W' ζ' αR βR βL αL ζαR ζβR ζβL ζαL hcfg R L η hV MR ML hMR hML r A A' ψ ψ' n n' s q
    hA hA'] with ω hω hωA hωA' hωN
  obtain ⟨q', hq', hT, hmeet, hR⟩ := hω hωA hωA' hωN
  exact ⟨q', hq', inner_dom_subset_outer_dom_two (fun ω hω => (hA ω hω).1) (fun ω hω => (hA ω hω).2) hωA hωN.2.1
    (fun ω hω => (hA' ω hω).1) (fun ω hω => (hA' ω hω).2) hωA' hq' hωN.2.2.2.1 hT hmeet, hR⟩

end FaceQ

/-! ### The final drop-in with the bounded faces reduced to one common point -/

section FinalQ

open R7Outer R7Leaves R6Nest
open QuantumZipper (chiC)
open scoped Real

universe u

variable {k rL rR : ℝ}

/-- **The two-outer-arm inputs with the bounded faces reduced to one common point.** -/
def TwoOuterFaceQInputs (k rL rR : ℝ) : Prop :=
  PhaseCont.R7PhaseWordRemaining.{u} k (innerRight k rL rL (k / 2 - 4))
      (innerLeft k (k / 2 - 4) (k / 2 - 4) (k / 2 - 4))
      (π * chiC (16 / k) + (R7.thetaL k rR - π / 2) * chiC (16 / k) +
        (r7A k (k / 2 - 4) - r7A k (innerLeft k (k / 2 - 4) (k / 2 - 4) (k / 2 - 4))))
      (0 + (r7B k rL - r7B k (innerRight k rL rL (k / 2 - 4)))) ∧
    R6FaceQMixedRemaining.{u} k rL (k / 2 - 4) (π * chiC (16 / k) + (R7.thetaL k rR - π / 2) * chiC (16 / k)) 0 ∧
    R6FacePMixedInfRemaining.{u} k rL (k / 2 - 4)
      (π * chiC (16 / k) + (R7.thetaL k rR - π / 2) * chiC (16 / k)) 0 ∧
    R6FacePMixedInfInfRemaining.{u} k rL (k / 2 - 4)
      (π * chiC (16 / k) + (R7.thetaL k rR - π / 2) * chiC (16 / k)) 0 ∧
    R6Rel.R7OuterPhaseContMRemaining.{u} k rL (k / 2 - 4)
      (π * chiC (16 / k) + (R7.thetaL k rR - π / 2) * chiC (16 / k)) 0 ∧
    R6FaceQTwoRemaining.{u} k rL rR (π * chiC (16 / k)) 0 ∧
    R6FacePTwoInfRemaining.{u} k rL rR (π * chiC (16 / k)) 0 ∧
    R6FacePTwoInfInfRemaining.{u} k rL rR (π * chiC (16 / k)) 0

/-- The reduced two-outer-arm inputs give `TwoOuterFacePInputs`. -/
theorem twoOuterFacePInputs_of_faceQ (h : TwoOuterFaceQInputs.{u} k rL rR) : TwoOuterFacePInputs.{u} k rL rR :=
  ⟨h.1, r6FacePMixedRemaining_of_faceQ h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2.1,
    r6FacePTwoRemaining_of_faceQ h.2.2.2.2.2.1, h.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2⟩

/-- **The outer phase input from R.5 and R.6's faces, the bounded faces reduced to one common point** (drop-in for
`R6Fin.r7OuterPhaseSideRemaining_of_cont_core`, without `hstrip` and `htwo`). -/
theorem r7OuterPhaseSideRemaining_of_cont_faceQ_safe (h411 : Sec5.Cond44Ref.Prop411QStatement.{u})
    (h51 : Sec5.Cond44Ref.Prop51QStatement.{u}) (h47 : Sec5.Prop411Q.Lemma47QHitStatement.{u})
    (h47T : ∀ θ : ℝ, -(π / 2) < θ → θ < π / 2 → Sec5.RestartGen.Lemma47QHitTStatement.{u} θ)
    (haux7 : Sec4.Aux7Statement.{u} k) (h44 : AdmCode.Theorem12ParamCond44Statement.{u})
    (hA : Sec5.PartAInputsSixteenDivOfClearance)
    (hword : PhaseCont.R7PhaseWordRemaining.{u} k (innerRight k rL rL (k / 2 - 4)) (innerLeft k rR rR (k / 2 - 4))
      (π * chiC (16 / k) + (r7A k rR - r7A k (innerLeft k rR rR (k / 2 - 4))))
      (0 + (r7B k rL - r7B k (innerRight k rL rL (k / 2 - 4)))))
    (hface : R6FaceQMixedRemaining.{u} k rL rR (π * chiC (16 / k)) 0)
    (hfaceI : R6FacePMixedInfRemaining.{u} k rL rR (π * chiC (16 / k)) 0)
    (hfaceII : R6FacePMixedInfInfRemaining.{u} k rL rR (π * chiC (16 / k)) 0)
    (hk4 : 4 < k) (hrL : -2 < rL) (hrR : -2 < rR)
    (hcont : OuterPhNext.R7OuterPhaseContRemaining.{u} k rL rR)
    (htwoIn : k / 2 - 4 < rL → k / 2 - 4 < rR → TwoOuterFaceQInputs.{u} k rL rR) :
    OuterIn.R7OuterPhaseSideRemaining.{u} k rL rR :=
  r7OuterPhaseSideRemaining_of_cont_faceP_safe h411 h51 h47 h47T haux7 h44 hA hword
    (r6FacePMixedRemaining_of_faceQ hface) hfaceI hfaceII hk4 hrL hrR hcont
    fun hdL hdR => twoOuterFacePInputs_of_faceQ (htwoIn hdL hdR)

end FinalQ

end InteractingSLE.Sec7.R6Safe
