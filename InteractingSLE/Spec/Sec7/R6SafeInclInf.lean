/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.R6SafeIncl

/-!
# R.6's face: the inclusion of the current domains for pockets opening at the flow seed

PROVE-R6-SAFE. The seed-opening counterparts of `R6SafeIncl` (handoff §4, (a1)–(a2)), and a generic combination:

* `inter_frontier_subset_of_fillH_inf`, **`outer_frontier_subset_traceInf`** (a1);
* **`exists_rat_lt_leftStopInf`** (contained), **`exists_rat_lt_ambTime0Inf_outer`** (outer) (a2);
* the inner current domains miss the trace before their left stop: `notMem_trace_contained(Inf)`,
  `notMem_trace_outer(Inf)`;
* **`dom_subset_of_avoid`**: the inner current domain lies in the outer one when it meets it, lies in the outer
  pocket, and misses a set containing the outer frontier inside the pocket.

R48: nothing here uses Theorem 1.2/1.3, `Theorem12ParamStatement`, `Theorem13Statement` or any `*_of_param`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Filter Topology Metric
open QuantumZipper (H Hbar)
open SupercriticalConformalCovariance (IsConformalBijection)
open scoped NNReal ENNReal

universe u

namespace InteractingSLE.Sec7.R6Safe

open Sec6 PocketTraversal Lemma71C PocketJordan PocketCoord PocketCoupling PocketStop PocketStopField HOuter
  PocketWordAssembly PocketSeedOpen

/-! ### (a1) at infinity -/

section Frontier

/-- **The frontier of `C ∩ ψ⁻¹(ℍ ∖ fill Z)` inside `C` lies in `E`** (Jordan coordinate at infinity). -/
theorem inter_frontier_subset_of_fillH_inf {C E : Set ℂ} {ψ : ℂ → ℂ} {y₀ : ℂ} (hCo : IsOpen C)
    (hψ : IsJordanCoordInf C y₀ ψ) (hE : E ⊆ closure C) (hZ : IsCompact (ψ '' E)) :
    C ∩ frontier (C ∩ ψ ⁻¹' (H \ fillH (ψ '' E))) ⊆ E := by
  rintro z ⟨hzC, hzf⟩
  by_contra hzE
  have hψc : ContinuousOn ψ C := hψ.1.mono subset_closure
  have hψz : ψ z ∈ H := hψ.2.2.2.1.2.mapsTo hzC
  have hnZ : ψ z ∉ closure (ψ '' E) := by
    rw [hZ.isClosed.closure_eq]
    rintro ⟨e, he, hez⟩
    exact hzE (hψ.2.1 (hE he) (subset_closure hzC) hez ▸ he)
  have hDo : IsOpen (C ∩ ψ ⁻¹' (H \ fillH (ψ '' E))) :=
    hψc.isOpen_inter_preimage hCo (InteractingSLE.isOpen_H_diff_fillH hZ.isBounded)
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

variable {Ω : Type*} {A : Set Ω} {R L : Ω → ℝ≥0 → ℂ} {r : ℝ≥0} {W : Ω → ℝ → ℝ} {η : Ω → ℝ → ℂ}
  {ψ : Ω → ℂ → ℂ} {n : Ω → ℤ} {q : ℝ≥0} {ω : Ω}

/-- **(a1) for an outer pocket opening at the flow seed**: `C ∩ ∂D_C(q) ⊆ η([0, f_R(clockOf ℓ(∞) (capInv γ q))])`. -/
theorem outer_frontier_subset_traceInf (hcfg : ∀ ω ∈ A, IsOuterCfgInf (R ω) (L ω) r (W ω) (η ω))
    (hψ : ∀ ω ∈ A, IsCfJordanInf (R ω) (L ω) r (ψ ω)) (hω : ω ∈ A)
    (hq : (q : ℝ≥0∞) < capLife (travAllInf R L r η ψ ω)) :
    cfPocket (R ω) (L ω) r ∩ frontier ((relChart (fun ω => shiftChart (pChart A (fun ω => cfPocket (R ω) (L ω) r)
        ψ ω) (n ω)) (travAllInf R L r η ψ) q ω).dom : Set ℂ) ⊆
      η ω '' Icc 0 (pocketFibreInf (η ω) (cfPocket (R ω) (L ω) r) (firstHit (η ω) (cfArcRInf (R ω) (L ω) r 0))
        (clockOf (clockEnd (η ω) (cfPocket (R ω) (L ω) r) (firstHit (η ω) (cfArcRInf (R ω) (L ω) r 0)))
          (capInv (travAllInf R L r η ψ ω) q))) := by
  have hG : ∀ ω ∈ A, IsChangeConfigInc (R ω) (L ω) r := fun ω hω => (hcfg ω hω).conf
  have hCo : ∀ ω ∈ A, IsOpen (cfPocket (R ω) (L ω) r) := fun ω hω =>
    isOpen_image_negInv' (hG ω hω).isOpen_changePocket (hG ω hω).changePocket_subset_H
  have hCH : ∀ ω ∈ A, cfPocket (R ω) (L ω) r ⊆ H := fun ω hω =>
    PocketJordan.image_negInv_subset_H (hG ω hω).changePocket_subset_H
  have hγ : IsDrivenCurve (travAllInf R L r η ψ ω) := ((hcfg ω hω).props (hψ ω hω)).1
  have hP := (hcfg ω hω).erase
  set C := cfPocket (R ω) (L ω) r with hC
  set τ := firstHit (η ω) (cfArcRInf (R ω) (L ω) r 0) with hτ
  set Lc := clockEnd (η ω) C τ with hLc
  set u := capInv (travAllInf R L r η ψ ω) q with hu
  have hL : 0 < Lc := hP.clockEnd_pos
  have hu0 : 0 ≤ u := capInv_nonneg _ _
  have hv := clockOf_mem_Ico hL hu0
  have hJ := hψ ω hω
  rw [relChart_dom_eq_inter (n := n) hCo hCH (fun ω hω => (hψ ω hω).2.2.2.1) hω hγ hq,
    hγ.fwdHull_segDriver q.coe_nonneg (by rw [ENNReal.ofReal_coe_nnreal]; exact hq)]
  have himg : travAllInf R L r η ψ ω '' Icc 0 u = ψ ω '' (erasedPathInf (η ω) C τ '' Icc 0 (clockOf Lc u)) := by
    change relCurve (fun v => ψ ω (erasedPathInf (η ω) C τ v)) Lc '' Icc 0 u = _
    rw [image_relCurve_Icc _ hL hu0, image_image]
  rw [himg]
  have hE : erasedPathInf (η ω) C τ '' Icc 0 (clockOf Lc u) ⊆ closure C := by
    rintro _ ⟨v, hvI, rfl⟩
    exact hP.erasedPath_mem ⟨hvI.1, hvI.2.trans_lt hv.2⟩
  have hcont : ContinuousOn (fun v => ψ ω (erasedPathInf (η ω) C τ v)) (Icc 0 (clockOf Lc u)) :=
    hJ.1.comp (hP.continuousOn_erasedPath_Icc hv) fun v hvI => hE ⟨v, hvI, rfl⟩
  have hZ : IsCompact (ψ ω '' (erasedPathInf (η ω) C τ '' Icc 0 (clockOf Lc u))) := by
    rw [image_image]
    exact isCompact_Icc.image_of_continuousOn hcont
  intro z hz
  have hzE := inter_frontier_subset_of_fillH_inf (hCo ω hω) hJ hE hZ hz
  have hmem : z ∈ erasedPathInf (η ω) C τ '' Icc 0 (clockOf Lc u) ∩ C := ⟨hzE, hz.1⟩
  rw [hP.erasedPath_image_inter hv] at hmem
  exact hmem.1

end Frontier

/-! ### (a2) at infinity -/

section Stop

variable {Ω : Type*} {R L : Ω → ℝ≥0 → ℂ} {r : ℝ≥0} {W : Ω → ℝ → ℝ} {η : Ω → ℝ → ℂ} {ψ : Ω → ℂ → ℂ} {ω : Ω}

/-- A rational strictly between a relative capacity and a lifetime, read as a positive live time. -/
theorem exists_rat_btwn_relCap {c : ℝ} (hc0 : 0 ≤ c) {ℓ : ℝ≥0∞} (hlt : ENNReal.ofReal c < ℓ) :
    ∃ q' : ℚ, 0 < q' ∧ ((StripSys.rt q' : ℝ≥0) : ℝ≥0∞) < ℓ ∧ c < ((StripSys.rt q' : ℝ≥0) : ℝ) := by
  obtain ⟨q', -, hlo, hhi⟩ := ENNReal.lt_iff_exists_rat_btwn.1 hlt
  have hlo' : c < (q' : ℝ) := by
    rw [ENNReal.ofReal, ENNReal.coe_lt_coe, Real.toNNReal_lt_toNNReal_iff' ] at hlo
    exact hlo.1
  have hqpos : (0 : ℝ) < q' := hc0.trans_lt hlo'
  refine ⟨q', by exact_mod_cast hqpos, hhi, ?_⟩
  rwa [StripSys.rt, Real.coe_toNNReal _ hqpos.le]

/-- **(a2) for a contained pocket opening at the flow seed.** -/
theorem exists_rat_lt_leftStopInf (hcfg : IsCfPocketConfigInf (R ω) (L ω) r (W ω) (η ω))
    (hψ : IsCfJordanInf (R ω) (L ω) r (ψ ω)) {T : ℝ} (hT : firstHit (η ω) (cfArcRInf (R ω) (L ω) r 0) ≤ T) :
    ∃ q' : ℚ, 0 < q' ∧ ((StripSys.rt q' : ℝ≥0) : ℝ≥0∞) < capLife (travAllInf R L r η ψ ω) ∧
      T < R5Ref.leftStopInf R L r η ψ (StripSys.rt q') ω := by
  obtain ⟨hP, hJ⟩ := R5Ref.pocket_of_cfgInf hcfg hψ
  have hlt := PocketStopMarked.relCapInf_lt_capLife hP hcfg.attach hJ hT
  have hc0 : 0 ≤ PocketStopMarked.relCapInf (η ω) (cfPocket (R ω) (L ω) r)
      (firstHit (η ω) (cfArcRInf (R ω) (L ω) r 0)) (ψ ω) T :=
    (isDrivenCurve_relCurve_of_isReversePocketInf hP hcfg.attach hJ).capClock_nonneg
      (PocketStopMarked.relTimeInf_nonneg hP hcfg.attach hT)
  obtain ⟨q', hq'0, hhi, hlo⟩ := exists_rat_btwn_relCap hc0 hlt
  refine ⟨q', hq'0, hhi, ?_⟩
  by_contra hle
  have h := (PocketStopMarked.ambTime0Inf_le_iff hP hcfg.attach hJ (NNReal.coe_nonneg _)
    (by rw [ENNReal.ofReal_coe_nnreal]; exact hhi) hT).1 (not_lt.1 hle)
  linarith

/-- **(a2) for an outer pocket opening at the flow seed.** -/
theorem exists_rat_lt_ambTime0Inf_outer (hcfg : IsOuterCfgInf (R ω) (L ω) r (W ω) (η ω))
    (hψ : IsCfJordanInf (R ω) (L ω) r (ψ ω)) {T : ℝ} (hT : firstHit (η ω) (cfArcRInf (R ω) (L ω) r 0) ≤ T) :
    ∃ q' : ℚ, 0 < q' ∧ ((StripSys.rt q' : ℝ≥0) : ℝ≥0∞) < capLife (travAllInf R L r η ψ ω) ∧
      T < PocketStopWallsFin.ambTime0Inf (η ω) (cfPocket (R ω) (L ω) r)
        (firstHit (η ω) (cfArcRInf (R ω) (L ω) r 0)) (ψ ω) (StripSys.rt q') := by
  have hP := hcfg.toPocketInf hψ
  have hlt := PocketStopMarked.Outer.relCapInf_lt_capLife hP hT
  have hc0 : 0 ≤ PocketStopMarked.relCapInf (η ω) (cfPocket (R ω) (L ω) r)
      (firstHit (η ω) (cfArcRInf (R ω) (L ω) r 0)) (ψ ω) T :=
    hP.driven.capClock_nonneg (PocketStopMarked.Outer.relTimeInf_nonneg hP hT)
  obtain ⟨q', hq'0, hhi, hlo⟩ := exists_rat_btwn_relCap hc0 hlt
  refine ⟨q', hq'0, hhi, ?_⟩
  by_contra hle
  have h := (PocketStopMarked.Outer.ambTime0Inf_le_iff hP (NNReal.coe_nonneg _)
    (by rw [ENNReal.ofReal_coe_nnreal]; exact hhi) hT).1 (not_lt.1 hle)
  linarith

end Stop

/-! ### The inner current domains miss the trace before their left stop -/

section Avoid

variable {Ω : Type*} {A : Set Ω} {R L : Ω → ℝ≥0 → ℂ} {r : ℝ≥0} {W : Ω → ℝ → ℝ} {η : Ω → ℝ → ℂ}
  {ψ : Ω → ℂ → ℂ} {n : Ω → ℤ} {q : ℝ≥0} {ω : Ω}

/-- **The generic inclusion**: an inner current domain meeting the outer one, inside the outer pocket and missing a set
that contains the outer frontier inside the pocket, lies in the outer current domain. -/
theorem dom_subset_of_avoid {outer inner : Chart} {C S : Set ℂ} (hI : inner.IsConformal)
    (hsub : (inner.dom : Set ℂ) ⊆ C) (hfront : C ∩ frontier (outer.dom : Set ℂ) ⊆ S)
    (hav : ∀ z ∈ (inner.dom : Set ℂ), z ∉ S) (hmeet : ((inner.dom : Set ℂ) ∩ outer.dom).Nonempty) :
    (inner.dom : Set ℂ) ⊆ outer.dom :=
  dom_subset_of_frontier_disjoint hI (disjoint_left.2 fun z hz hzf => hav z hz (hfront ⟨hsub hz, hzf⟩)) hmeet

/-- **A contained pocket's live current chart** is conformal, its domain lies in the pocket and misses `η([0, T])` for
`T` up to its left stop. -/
theorem contained_chart_facts (hcfg : ∀ ω ∈ A, IsCfPocketConfig (R ω) (L ω) r (W ω) (η ω))
    (hψ : ∀ ω ∈ A, IsCfJordan (R ω) (L ω) r (ψ ω)) (hω : ω ∈ A)
    (hq : (q : ℝ≥0∞) < capLife (travAll R L r η ψ ω)) :
    (relChart (fun ω => shiftChart (pChart A (fun ω => cfPocket (R ω) (L ω) r) ψ ω) (n ω))
        (travAll R L r η ψ) q ω).IsConformal ∧
      ((relChart (fun ω => shiftChart (pChart A (fun ω => cfPocket (R ω) (L ω) r) ψ ω) (n ω))
        (travAll R L r η ψ) q ω).dom : Set ℂ) ⊆ cfPocket (R ω) (L ω) r ∧
      ∀ T ≤ R5Ref.leftStop R L r η ψ q ω, ∀ z ∈ ((relChart (fun ω => shiftChart (pChart A
        (fun ω => cfPocket (R ω) (L ω) r) ψ ω) (n ω)) (travAll R L r η ψ) q ω).dom : Set ℂ), z ∉ η ω '' Icc 0 T := by
  have hG : ∀ ω ∈ A, IsChangeConfigInc (R ω) (L ω) r := fun ω hω => (hcfg ω hω).conf
  obtain ⟨hc, hdom, heq⟩ := R5Phase.shiftChart_dom_facts
    (fun ω hω => isOpen_image_negInv' (hG ω hω).isOpen_changePocket (hG ω hω).changePocket_subset_H)
    (fun ω hω => PocketJordan.image_negInv_subset_H (hG ω hω).changePocket_subset_H)
    (fun ω hω => (hψ ω hω).2.2.2.1) n ω hω
  have he := R5Ref.current_dom_eq (c := fun ω => shiftChart (pChart A (fun ω => cfPocket (R ω) (L ω) r) ψ ω) (n ω))
    hω (hcfg ω hω) (hψ ω hω) hc hdom heq hq
  refine ⟨PocketStopSide.isConformal_relChart_of_driven ((hcfg ω hω).isDrivenCurve (hψ ω hω)).1 hq hc,
    fun z hz => (he ▸ hz).1, fun T hT z hz ⟨t, ht, hte⟩ => ?_⟩
  have hz' := he ▸ hz
  exact hz'.2.2 ⟨hz'.2.1, Or.inl (subset_closure ⟨t, ⟨ht.1, ht.2.trans hT⟩, hte⟩)⟩

/-- **A contained pocket's live current chart, opening at the flow seed.** -/
theorem contained_chart_factsInf (hcfg : ∀ ω ∈ A, IsCfPocketConfigInf (R ω) (L ω) r (W ω) (η ω))
    (hψ : ∀ ω ∈ A, IsCfJordanInf (R ω) (L ω) r (ψ ω)) (hω : ω ∈ A)
    (hq : (q : ℝ≥0∞) < capLife (travAllInf R L r η ψ ω)) :
    (relChart (fun ω => shiftChart (pChart A (fun ω => cfPocket (R ω) (L ω) r) ψ ω) (n ω))
        (travAllInf R L r η ψ) q ω).IsConformal ∧
      ((relChart (fun ω => shiftChart (pChart A (fun ω => cfPocket (R ω) (L ω) r) ψ ω) (n ω))
        (travAllInf R L r η ψ) q ω).dom : Set ℂ) ⊆ cfPocket (R ω) (L ω) r ∧
      ∀ T ≤ R5Ref.leftStopInf R L r η ψ q ω, ∀ z ∈ ((relChart (fun ω => shiftChart (pChart A
        (fun ω => cfPocket (R ω) (L ω) r) ψ ω) (n ω)) (travAllInf R L r η ψ) q ω).dom : Set ℂ),
        z ∉ η ω '' Icc 0 T := by
  have hG : ∀ ω ∈ A, IsChangeConfigInc (R ω) (L ω) r := fun ω hω => (hcfg ω hω).conf
  obtain ⟨hc, hdom, heq⟩ := R5Phase.shiftChart_dom_facts
    (fun ω hω => isOpen_image_negInv' (hG ω hω).isOpen_changePocket (hG ω hω).changePocket_subset_H)
    (fun ω hω => PocketJordan.image_negInv_subset_H (hG ω hω).changePocket_subset_H)
    (fun ω hω => (hψ ω hω).2.2.2.1) n ω hω
  have he := R5Ref.current_dom_eqInf (c := fun ω => shiftChart (pChart A (fun ω => cfPocket (R ω) (L ω) r) ψ ω)
    (n ω)) hω (hcfg ω hω) (hψ ω hω) hc hdom heq hq
  refine ⟨PocketStopSide.isConformal_relChart_of_driven ((hcfg ω hω).isDrivenCurve (hψ ω hω)).1 hq hc,
    fun z hz => (he ▸ hz).1, fun T hT z hz ⟨t, ht, hte⟩ => ?_⟩
  have hz' := he ▸ hz
  exact hz'.2.2 ⟨hz'.2.1, Or.inl (subset_closure ⟨t, ⟨ht.1, ht.2.trans hT⟩, hte⟩)⟩

end Avoid

section AvoidOuter

variable {Ω : Type*} {A : Set Ω} {R L : Ω → ℝ≥0 → ℂ} {r : ℝ≥0} {W : Ω → ℝ → ℝ} {η : Ω → ℝ → ℂ}
  {ψ : Ω → ℂ → ℂ} {n : Ω → ℤ} {q : ℝ≥0} {ω : Ω}

/-- **An outer bounded pocket's live current chart** is conformal, its domain lies in the pocket and misses `η([0, T])`
for `T` up to its left stop (`HOuter.relDomain_subset_domain_ambTime0`). -/
theorem outer_chart_facts (hcfg : ∀ ω ∈ A, IsOuterCfg (R ω) (L ω) r (W ω) (η ω))
    (hψ : ∀ ω ∈ A, IsCfJordan (R ω) (L ω) r (ψ ω)) (hω : ω ∈ A)
    (hq : (q : ℝ≥0∞) < capLife (travAll R L r η ψ ω)) :
    (relChart (fun ω => shiftChart (pChart A (fun ω => cfPocket (R ω) (L ω) r) ψ ω) (n ω))
        (travAll R L r η ψ) q ω).IsConformal ∧
      ((relChart (fun ω => shiftChart (pChart A (fun ω => cfPocket (R ω) (L ω) r) ψ ω) (n ω))
        (travAll R L r η ψ) q ω).dom : Set ℂ) ⊆ cfPocket (R ω) (L ω) r ∧
      ∀ T ≤ PocketStopWallsFin.ambTime0 (η ω) (cfPocket (R ω) (L ω) r) (firstHit (η ω) (cfArcR (R ω) (L ω) r 1))
        (firstHit (η ω) (cfArcR (R ω) (L ω) r 0)) (ψ ω) q, ∀ z ∈ ((relChart (fun ω => shiftChart (pChart A
        (fun ω => cfPocket (R ω) (L ω) r) ψ ω) (n ω)) (travAll R L r η ψ) q ω).dom : Set ℂ), z ∉ η ω '' Icc 0 T := by
  have hG : ∀ ω ∈ A, IsChangeConfigInc (R ω) (L ω) r := fun ω hω => (hcfg ω hω).conf
  have hCo : ∀ ω ∈ A, IsOpen (cfPocket (R ω) (L ω) r) := fun ω hω =>
    isOpen_image_negInv' (hG ω hω).isOpen_changePocket (hG ω hω).changePocket_subset_H
  have hCH : ∀ ω ∈ A, cfPocket (R ω) (L ω) r ⊆ H := fun ω hω =>
    PocketJordan.image_negInv_subset_H (hG ω hω).changePocket_subset_H
  obtain ⟨hc, -, -⟩ := R5Phase.shiftChart_dom_facts hCo hCH (fun ω hω => (hψ ω hω).2.2.2.1) n ω hω
  have hγ : IsDrivenCurve (travAll R L r η ψ ω) := ((hcfg ω hω).props (hψ ω hω)).1
  have he := relChart_dom_eq_inter (n := n) hCo hCH (fun ω hω => (hψ ω hω).2.2.2.1) hω hγ hq
  have hcf := hcfg ω hω
  have hJ : IsJordanCoord (cfPocket (R ω) (L ω) r) (cfArcR (R ω) (L ω) r 0) (cfArcR (R ω) (L ω) r 1) (ψ ω) := by
    rw [IsChangeConfigInc.cfArcR_zero, IsChangeConfigInc.cfArcR_one]; exact hψ ω hω
  have hCb : Bornology.IsBounded (cfPocket (R ω) (L ω) r) :=
    isBounded_image_negInv (PocketMarks.zero_notMem_closure_of_rightLo_pos hcf.conf hcf.bounded)
  refine ⟨PocketStopSide.isConformal_relChart_of_driven hγ hq hc, fun z hz => (he ▸ hz).1,
    fun T hT z hz ⟨t, ht, hte⟩ => ?_⟩
  have hdom := relDomain_subset_domain_ambTime0 hcf.erase hcf.trace hcf.continuous_W hcf.W_zero (hCH ω hω) hCb hJ
    hγ q.coe_nonneg (by rw [ENNReal.ofReal_coe_nnreal]; exact hq) (he ▸ hz)
  rw [hcf.trace.2.2 _ ((hcf.erase.nonneg).trans (PocketStopMarked.Outer.ambTime0_mem_Ico (hcf.toPocket (hψ ω hω))
    q.coe_nonneg (by rw [ENNReal.ofReal_coe_nnreal]; exact hq)).1)] at hdom
  exact hdom.2 ⟨hdom.1, Or.inl (subset_closure ⟨t, ⟨ht.1, ht.2.trans hT⟩, hte⟩)⟩

/-- **An outer pocket's live current chart, opening at the flow seed**
(`HOuter.relDomain_subset_domain_ambTime0Inf`). -/
theorem outer_chart_factsInf (hcfg : ∀ ω ∈ A, IsOuterCfgInf (R ω) (L ω) r (W ω) (η ω))
    (hψ : ∀ ω ∈ A, IsCfJordanInf (R ω) (L ω) r (ψ ω)) (hω : ω ∈ A)
    (hq : (q : ℝ≥0∞) < capLife (travAllInf R L r η ψ ω)) :
    (relChart (fun ω => shiftChart (pChart A (fun ω => cfPocket (R ω) (L ω) r) ψ ω) (n ω))
        (travAllInf R L r η ψ) q ω).IsConformal ∧
      ((relChart (fun ω => shiftChart (pChart A (fun ω => cfPocket (R ω) (L ω) r) ψ ω) (n ω))
        (travAllInf R L r η ψ) q ω).dom : Set ℂ) ⊆ cfPocket (R ω) (L ω) r ∧
      ∀ T ≤ PocketStopWallsFin.ambTime0Inf (η ω) (cfPocket (R ω) (L ω) r)
        (firstHit (η ω) (cfArcRInf (R ω) (L ω) r 0)) (ψ ω) q, ∀ z ∈ ((relChart (fun ω => shiftChart (pChart A
        (fun ω => cfPocket (R ω) (L ω) r) ψ ω) (n ω)) (travAllInf R L r η ψ) q ω).dom : Set ℂ),
        z ∉ η ω '' Icc 0 T := by
  have hG : ∀ ω ∈ A, IsChangeConfigInc (R ω) (L ω) r := fun ω hω => (hcfg ω hω).conf
  have hCo : ∀ ω ∈ A, IsOpen (cfPocket (R ω) (L ω) r) := fun ω hω =>
    isOpen_image_negInv' (hG ω hω).isOpen_changePocket (hG ω hω).changePocket_subset_H
  have hCH : ∀ ω ∈ A, cfPocket (R ω) (L ω) r ⊆ H := fun ω hω =>
    PocketJordan.image_negInv_subset_H (hG ω hω).changePocket_subset_H
  obtain ⟨hc, -, -⟩ := R5Phase.shiftChart_dom_facts hCo hCH (fun ω hω => (hψ ω hω).2.2.2.1) n ω hω
  have hγ : IsDrivenCurve (travAllInf R L r η ψ ω) := ((hcfg ω hω).props (hψ ω hω)).1
  have he := relChart_dom_eq_inter (n := n) hCo hCH (fun ω hω => (hψ ω hω).2.2.2.1) hω hγ hq
  have hcf := hcfg ω hω
  have hJ : IsJordanCoordInf (cfPocket (R ω) (L ω) r) (cfArcRInf (R ω) (L ω) r 0) (ψ ω) := by
    rw [IsChangeConfigInc.cfArcRInf_zero]; exact hψ ω hω
  refine ⟨PocketStopSide.isConformal_relChart_of_driven hγ hq hc, fun z hz => (he ▸ hz).1,
    fun T hT z hz ⟨t, ht, hte⟩ => ?_⟩
  have hdom := relDomain_subset_domain_ambTime0Inf hcf.erase hcf.trace (hCH ω hω) hJ hγ q.coe_nonneg
    (by rw [ENNReal.ofReal_coe_nnreal]; exact hq) (he ▸ hz)
  rw [hcf.trace.2.2 _ ((hcf.erase.nonneg).trans (PocketStopMarked.Outer.le_ambTime0Inf' (hcf.toPocketInf (hψ ω hω))
    (ψ ω) q))] at hdom
  exact hdom.2 ⟨hdom.1, Or.inl (subset_closure ⟨t, ⟨ht.1, ht.2.trans hT⟩, hte⟩)⟩

end AvoidOuter


/-! ### The seed-opening faces with the inclusion reduced to one common point -/

section FaceQInf

open MeasureTheory ProbabilityTheory
open LQGMetric (DistOn)
open QuantumZipper (chiC)
open scoped Real
open R6Fin WholeField R7Outer R7Leaves R6Nest R6Rel R6Cert HOuter PocketMarks PocketStopWallsFin PocketStopSide

/-- **Named, unproved: R.6's face, shape `MixedInf`, with the inclusion reduced to one common point**
(as `R6FaceQMixedRemaining`; `r6FacePMixedInfRemaining_of_faceQ`). -/
def R6FaceQMixedInfRemaining (k rL rR c c' : ℝ) : Prop :=
  (k / 2 - 4 < rL ∧ rR ≤ k / 2 - 4) ∨ (rL ≤ k / 2 - 4 ∧ k / 2 - 4 < rR) →
  ∀ {Ω : Type u} [MeasurableSpace Ω] [StandardBorelSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (h : Ω → DistOn upperHalfPlaneOpens) (W' : ℝ≥0 → Ω → ℝ) (ζ' : Ω → ℝ≥0∞)
    (αR βR βL αL : Ω → ℝ≥0 → ℂ) (ζαR ζβR ζβL ζαL : Ω → ℝ≥0∞),
    IsR7OuterConfig k rL rR c c' P h W' ζ' αR βR βL αL ζαR ζβR ζβL ζαL →
    ∀ (R L : Ω → ℝ≥0 → ℂ) (η : Ω → ℝ → ℂ), IsR7Versions P W' αR αL R L η →
    ∀ MR ML : Ω → ℝ≥0 → ℂ, IsFrontierVersion P βR MR → IsFrontierVersion P βL ML →
    ∀ (r : ℝ≥0) (A A' : Set Ω) (ψ ψ' : Ω → ℂ → ℂ) (n n' : Ω → ℤ) (s q : ℚ),
      (∀ ω ∈ A, IsOuterCfgInf (R ω) (L ω) r (fun t : ℝ => W' t.toNNReal ω) (η ω) ∧
        IsCfJordanInf (R ω) (L ω) r (ψ ω)) →
      (∀ ω ∈ A', IsCfPocketConfig (innerRight k rL R MR ω) (innerLeft k rR L ML ω) (StripSys.rt s)
          (fun t : ℝ => W' t.toNNReal ω) (η ω) ∧
        IsCfJordan (innerRight k rL R MR ω) (innerLeft k rR L ML ω) (StripSys.rt s) (ψ' ω)) →
      ∀ᵐ ω ∂P, ω ∈ A → ω ∈ A' →
        ω ∈ nestRelEventInf R L r η ψ MR ML (innerRight k rL R MR) (innerLeft k rR L ML) s q →
        ∃ q' : ℚ, ((StripSys.rt q' : ℝ≥0) : ℝ≥0∞) <
            capLife (travAll (innerRight k rL R MR) (innerLeft k rR L ML) (StripSys.rt s) η ψ' ω) ∧
          pocketFibreInf (η ω) (cfPocket (R ω) (L ω) r) (firstHit (η ω) (cfArcRInf (R ω) (L ω) r 0))
              (clockOf (clockEnd (η ω) (cfPocket (R ω) (L ω) r) (firstHit (η ω) (cfArcRInf (R ω) (L ω) r 0)))
                (capInv (travAllInf R L r η ψ ω) (StripSys.rt q))) ≤
            R5Ref.leftStop (innerRight k rL R MR) (innerLeft k rR L ML) (StripSys.rt s) η ψ' (StripSys.rt q') ω ∧
          (((relChart (fun ω => shiftChart (pChart A' (fun ω => cfPocket (innerRight k rL R MR ω)
                (innerLeft k rR L ML ω) (StripSys.rt s)) ψ' ω) (n' ω))
              (travAll (innerRight k rL R MR) (innerLeft k rR L ML) (StripSys.rt s) η ψ') (StripSys.rt q')
                ω).dom : Set ℂ) ∩
            (relChart (fun ω => shiftChart (pChart A (fun ω => cfPocket (R ω) (L ω) r) ψ ω) (n ω))
              (travAllInf R L r η ψ) (StripSys.rt q) ω).dom).Nonempty ∧
          R6FaceR (fun _ : Fin 1 => rL) (fun _ : Fin 1 => rR) (fun _ : Fin 1 => innerRight k rL rL (k / 2 - 4))
            (fun _ : Fin 1 => innerLeft k rR rR (k / 2 - 4))
            (fun i => geomLW (fun t ω => segDriver (travAllInf R L r η ψ ω) t) (fun _ => LP.twoSeedXL) i
              (StripSys.rt q) ω - segDriver (travAllInf R L r η ψ ω) (StripSys.rt q))
            (fun j => geomRW (fun t ω => segDriver (travAllInf R L r η ψ ω) t) (fun _ => LP.twoSeedXR) j
              (StripSys.rt q) ω - segDriver (travAllInf R L r η ψ ω) (StripSys.rt q))
            (fun i => geomLW (fun t ω => segDriver (travAll (innerRight k rL R MR) (innerLeft k rR L ML)
                (StripSys.rt s) η ψ' ω) t) (fun _ => LP.twoSeedXL) i (StripSys.rt q') ω -
              segDriver (travAll (innerRight k rL R MR) (innerLeft k rR L ML) (StripSys.rt s) η ψ' ω)
                (StripSys.rt q'))
            (fun j => geomRW (fun t ω => segDriver (travAll (innerRight k rL R MR) (innerLeft k rR L ML)
                (StripSys.rt s) η ψ' ω) t) (fun _ => LP.twoSeedXR) j (StripSys.rt q') ω -
              segDriver (travAll (innerRight k rL R MR) (innerLeft k rR L ML) (StripSys.rt s) η ψ' ω)
                (StripSys.rt q'))
            (relChart (fun ω => shiftChart (pChart A (fun ω => cfPocket (R ω) (L ω) r) ψ ω) (n ω))
              (travAllInf R L r η ψ) (StripSys.rt q) ω)
            (relChart (fun ω => shiftChart (pChart A' (fun ω => cfPocket (innerRight k rL R MR ω)
                (innerLeft k rR L ML ω) (StripSys.rt s)) ψ' ω) (n' ω))
              (travAll (innerRight k rL R MR) (innerLeft k rR L ML) (StripSys.rt s) η ψ') (StripSys.rt q') ω)
            (pocketSetInf A R L r η ψ n (StripSys.rt q) ω)
            (pocketSet A' (innerRight k rL R MR) (innerLeft k rR L ML) (StripSys.rt s) η ψ' n' (StripSys.rt q') ω)

/-- **`R6FacePMixedInfRemaining` from the face with one common point** (`dom_subset_of_avoid`). -/
theorem r6FacePMixedInfRemaining_of_faceQ {k rL rR c c' : ℝ} (hQ : R6FaceQMixedInfRemaining.{u} k rL rR c c') :
    R6FacePMixedInfRemaining.{u} k rL rR c c' := by
  intro hmix Ω _ _ P _ h W' ζ' αR βR βL αL ζαR ζβR ζβL ζαL hcfg R L η hV MR ML hMR hML r A A' ψ ψ' n n' s q hA
    hA'
  filter_upwards [hQ hmix P h W' ζ' αR βR βL αL ζαR ζβR ζβL ζαL hcfg R L η hV MR ML hMR hML r A A' ψ ψ' n n' s q
    hA hA'] with ω hω hωA hωA' hωN
  obtain ⟨q', hq', hT, hmeet, hR⟩ := hω hωA hωA' hωN
  obtain ⟨hIc, hIsub, hIav⟩ := contained_chart_facts (n := n') (fun ω hω => (hA' ω hω).1)
    (fun ω hω => (hA' ω hω).2) hωA' hq'
  exact ⟨q', hq', dom_subset_of_avoid hIc (hIsub.trans hωN.2.2.2.1)
    (outer_frontier_subset_traceInf (n := n) (fun ω hω => (hA ω hω).1) (fun ω hω => (hA ω hω).2) hωA hωN.2.1)
    (hIav _ hT) hmeet, hR⟩

/-- **Named, unproved: R.6's face, shape `MixedInfInf`, with the inclusion reduced to one common point**
(as `R6FaceQMixedRemaining`; `r6FacePMixedInfInfRemaining_of_faceQ`). -/
def R6FaceQMixedInfInfRemaining (k rL rR c c' : ℝ) : Prop :=
  (k / 2 - 4 < rL ∧ rR ≤ k / 2 - 4) ∨ (rL ≤ k / 2 - 4 ∧ k / 2 - 4 < rR) →
  ∀ {Ω : Type u} [MeasurableSpace Ω] [StandardBorelSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (h : Ω → DistOn upperHalfPlaneOpens) (W' : ℝ≥0 → Ω → ℝ) (ζ' : Ω → ℝ≥0∞)
    (αR βR βL αL : Ω → ℝ≥0 → ℂ) (ζαR ζβR ζβL ζαL : Ω → ℝ≥0∞),
    IsR7OuterConfig k rL rR c c' P h W' ζ' αR βR βL αL ζαR ζβR ζβL ζαL →
    ∀ (R L : Ω → ℝ≥0 → ℂ) (η : Ω → ℝ → ℂ), IsR7Versions P W' αR αL R L η →
    ∀ MR ML : Ω → ℝ≥0 → ℂ, IsFrontierVersion P βR MR → IsFrontierVersion P βL ML →
    ∀ (r : ℝ≥0) (A A' : Set Ω) (ψ ψ' : Ω → ℂ → ℂ) (n n' : Ω → ℤ) (s q : ℚ),
      (∀ ω ∈ A, IsOuterCfgInf (R ω) (L ω) r (fun t : ℝ => W' t.toNNReal ω) (η ω) ∧
        IsCfJordanInf (R ω) (L ω) r (ψ ω)) →
      (∀ ω ∈ A', IsCfPocketConfigInf (innerRight k rL R MR ω) (innerLeft k rR L ML ω) (StripSys.rt s)
          (fun t : ℝ => W' t.toNNReal ω) (η ω) ∧
        IsCfJordanInf (innerRight k rL R MR ω) (innerLeft k rR L ML ω) (StripSys.rt s) (ψ' ω)) →
      ∀ᵐ ω ∂P, ω ∈ A → ω ∈ A' →
        ω ∈ nestRelEventInf R L r η ψ MR ML (innerRight k rL R MR) (innerLeft k rR L ML) s q →
        ∃ q' : ℚ, ((StripSys.rt q' : ℝ≥0) : ℝ≥0∞) <
            capLife (travAllInf (innerRight k rL R MR) (innerLeft k rR L ML) (StripSys.rt s) η ψ' ω) ∧
          pocketFibreInf (η ω) (cfPocket (R ω) (L ω) r) (firstHit (η ω) (cfArcRInf (R ω) (L ω) r 0))
              (clockOf (clockEnd (η ω) (cfPocket (R ω) (L ω) r) (firstHit (η ω) (cfArcRInf (R ω) (L ω) r 0)))
                (capInv (travAllInf R L r η ψ ω) (StripSys.rt q))) ≤
            R5Ref.leftStopInf (innerRight k rL R MR) (innerLeft k rR L ML) (StripSys.rt s) η ψ' (StripSys.rt q') ω ∧
          (((relChart (fun ω => shiftChart (pChart A' (fun ω => cfPocket (innerRight k rL R MR ω)
                (innerLeft k rR L ML ω) (StripSys.rt s)) ψ' ω) (n' ω))
              (travAllInf (innerRight k rL R MR) (innerLeft k rR L ML) (StripSys.rt s) η ψ') (StripSys.rt q')
                ω).dom : Set ℂ) ∩
            (relChart (fun ω => shiftChart (pChart A (fun ω => cfPocket (R ω) (L ω) r) ψ ω) (n ω))
              (travAllInf R L r η ψ) (StripSys.rt q) ω).dom).Nonempty ∧
          R6FaceR (fun _ : Fin 1 => rL) (fun _ : Fin 1 => rR) (fun _ : Fin 1 => innerRight k rL rL (k / 2 - 4))
            (fun _ : Fin 1 => innerLeft k rR rR (k / 2 - 4))
            (fun i => geomLW (fun t ω => segDriver (travAllInf R L r η ψ ω) t) (fun _ => LP.twoSeedXL) i
              (StripSys.rt q) ω - segDriver (travAllInf R L r η ψ ω) (StripSys.rt q))
            (fun j => geomRW (fun t ω => segDriver (travAllInf R L r η ψ ω) t) (fun _ => LP.twoSeedXR) j
              (StripSys.rt q) ω - segDriver (travAllInf R L r η ψ ω) (StripSys.rt q))
            (fun i => geomLW (fun t ω => segDriver (travAllInf (innerRight k rL R MR) (innerLeft k rR L ML)
                (StripSys.rt s) η ψ' ω) t) (fun _ => LP.twoSeedXL) i (StripSys.rt q') ω -
              segDriver (travAllInf (innerRight k rL R MR) (innerLeft k rR L ML) (StripSys.rt s) η ψ' ω)
                (StripSys.rt q'))
            (fun j => geomRW (fun t ω => segDriver (travAllInf (innerRight k rL R MR) (innerLeft k rR L ML)
                (StripSys.rt s) η ψ' ω) t) (fun _ => LP.twoSeedXR) j (StripSys.rt q') ω -
              segDriver (travAllInf (innerRight k rL R MR) (innerLeft k rR L ML) (StripSys.rt s) η ψ' ω)
                (StripSys.rt q'))
            (relChart (fun ω => shiftChart (pChart A (fun ω => cfPocket (R ω) (L ω) r) ψ ω) (n ω))
              (travAllInf R L r η ψ) (StripSys.rt q) ω)
            (relChart (fun ω => shiftChart (pChart A' (fun ω => cfPocket (innerRight k rL R MR ω)
                (innerLeft k rR L ML ω) (StripSys.rt s)) ψ' ω) (n' ω))
              (travAllInf (innerRight k rL R MR) (innerLeft k rR L ML) (StripSys.rt s) η ψ') (StripSys.rt q') ω)
            (pocketSetInf A R L r η ψ n (StripSys.rt q) ω)
            (pocketSetInf A' (innerRight k rL R MR) (innerLeft k rR L ML) (StripSys.rt s) η ψ' n' (StripSys.rt q') ω)

/-- **`R6FacePMixedInfInfRemaining` from the face with one common point** (`dom_subset_of_avoid`). -/
theorem r6FacePMixedInfInfRemaining_of_faceQ {k rL rR c c' : ℝ} (hQ : R6FaceQMixedInfInfRemaining.{u} k rL rR c c') :
    R6FacePMixedInfInfRemaining.{u} k rL rR c c' := by
  intro hmix Ω _ _ P _ h W' ζ' αR βR βL αL ζαR ζβR ζβL ζαL hcfg R L η hV MR ML hMR hML r A A' ψ ψ' n n' s q hA
    hA'
  filter_upwards [hQ hmix P h W' ζ' αR βR βL αL ζαR ζβR ζβL ζαL hcfg R L η hV MR ML hMR hML r A A' ψ ψ' n n' s q
    hA hA'] with ω hω hωA hωA' hωN
  obtain ⟨q', hq', hT, hmeet, hR⟩ := hω hωA hωA' hωN
  obtain ⟨hIc, hIsub, hIav⟩ := contained_chart_factsInf (n := n') (fun ω hω => (hA' ω hω).1)
    (fun ω hω => (hA' ω hω).2) hωA' hq'
  exact ⟨q', hq', dom_subset_of_avoid hIc (hIsub.trans hωN.2.2.2.1)
    (outer_frontier_subset_traceInf (n := n) (fun ω hω => (hA ω hω).1) (fun ω hω => (hA ω hω).2) hωA hωN.2.1)
    (hIav _ hT) hmeet, hR⟩

/-- **Named, unproved: R.6's face, shape `TwoInf`, with the inclusion reduced to one common point**
(as `R6FaceQMixedRemaining`; `r6FacePTwoInfRemaining_of_faceQ`). -/
def R6FaceQTwoInfRemaining (k rL rR c c' : ℝ) : Prop :=
  k / 2 - 4 < rL → k / 2 - 4 < rR →
  ∀ {Ω : Type u} [MeasurableSpace Ω] [StandardBorelSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (h : Ω → DistOn upperHalfPlaneOpens) (W' : ℝ≥0 → Ω → ℝ) (ζ' : Ω → ℝ≥0∞)
    (αR βR βL αL : Ω → ℝ≥0 → ℂ) (ζαR ζβR ζβL ζαL : Ω → ℝ≥0∞),
    IsR7OuterConfig k rL rR c c' P h W' ζ' αR βR βL αL ζαR ζβR ζβL ζαL →
    ∀ (R L : Ω → ℝ≥0 → ℂ) (η : Ω → ℝ → ℂ), IsR7Versions P W' αR αL R L η →
    ∀ MR ML : Ω → ℝ≥0 → ℂ, IsFrontierVersion P βR MR → IsFrontierVersion P βL ML →
    ∀ (r : ℝ≥0) (A A' : Set Ω) (ψ ψ' : Ω → ℂ → ℂ) (n n' : Ω → ℤ) (s q : ℚ),
      (∀ ω ∈ A, IsOuterCfgInf (R ω) (L ω) r (fun t : ℝ => W' t.toNNReal ω) (η ω) ∧
        IsCfJordanInf (R ω) (L ω) r (ψ ω)) →
      (∀ ω ∈ A', IsOuterCfg (R ω) (ML ω) (StripSys.rt s)
          (fun t : ℝ => W' t.toNNReal ω) (η ω) ∧
        IsCfJordan (R ω) (ML ω) (StripSys.rt s) (ψ' ω)) →
      ∀ᵐ ω ∂P, ω ∈ A → ω ∈ A' →
        ω ∈ nestRelEventInf R L r η ψ MR ML R ML s q →
        ∃ q' : ℚ, ((StripSys.rt q' : ℝ≥0) : ℝ≥0∞) <
            capLife (travAll R ML (StripSys.rt s) η ψ' ω) ∧
          pocketFibreInf (η ω) (cfPocket (R ω) (L ω) r) (firstHit (η ω) (cfArcRInf (R ω) (L ω) r 0))
              (clockOf (clockEnd (η ω) (cfPocket (R ω) (L ω) r) (firstHit (η ω) (cfArcRInf (R ω) (L ω) r 0)))
                (capInv (travAllInf R L r η ψ ω) (StripSys.rt q))) ≤
            PocketStopWallsFin.ambTime0 (η ω) (cfPocket (R ω) (ML ω) (StripSys.rt s))
              (firstHit (η ω) (cfArcR (R ω) (ML ω) (StripSys.rt s) 1))
              (firstHit (η ω) (cfArcR (R ω) (ML ω) (StripSys.rt s) 0)) (ψ' ω) (StripSys.rt q') ∧
          (((relChart (fun ω => shiftChart (pChart A' (fun ω => cfPocket (R ω)
                (ML ω) (StripSys.rt s)) ψ' ω) (n' ω))
              (travAll R ML (StripSys.rt s) η ψ') (StripSys.rt q')
                ω).dom : Set ℂ) ∩
            (relChart (fun ω => shiftChart (pChart A (fun ω => cfPocket (R ω) (L ω) r) ψ ω) (n ω))
              (travAllInf R L r η ψ) (StripSys.rt q) ω).dom).Nonempty ∧
          R6FaceR (fun _ : Fin 1 => rL) (fun _ : Fin 1 => rR) (fun _ : Fin 1 => rL)
            (fun _ : Fin 1 => k / 2 - 4)
            (fun i => geomLW (fun t ω => segDriver (travAllInf R L r η ψ ω) t) (fun _ => LP.twoSeedXL) i
              (StripSys.rt q) ω - segDriver (travAllInf R L r η ψ ω) (StripSys.rt q))
            (fun j => geomRW (fun t ω => segDriver (travAllInf R L r η ψ ω) t) (fun _ => LP.twoSeedXR) j
              (StripSys.rt q) ω - segDriver (travAllInf R L r η ψ ω) (StripSys.rt q))
            (fun i => geomLW (fun t ω => segDriver (travAll R ML
                (StripSys.rt s) η ψ' ω) t) (fun _ => LP.twoSeedXL) i (StripSys.rt q') ω -
              segDriver (travAll R ML (StripSys.rt s) η ψ' ω)
                (StripSys.rt q'))
            (fun j => geomRW (fun t ω => segDriver (travAll R ML
                (StripSys.rt s) η ψ' ω) t) (fun _ => LP.twoSeedXR) j (StripSys.rt q') ω -
              segDriver (travAll R ML (StripSys.rt s) η ψ' ω)
                (StripSys.rt q'))
            (relChart (fun ω => shiftChart (pChart A (fun ω => cfPocket (R ω) (L ω) r) ψ ω) (n ω))
              (travAllInf R L r η ψ) (StripSys.rt q) ω)
            (relChart (fun ω => shiftChart (pChart A' (fun ω => cfPocket (R ω)
                (ML ω) (StripSys.rt s)) ψ' ω) (n' ω))
              (travAll R ML (StripSys.rt s) η ψ') (StripSys.rt q') ω)
            (pocketSetInf A R L r η ψ n (StripSys.rt q) ω)
            (pocketSet A' R ML (StripSys.rt s) η ψ' n' (StripSys.rt q') ω)

/-- **`R6FacePTwoInfRemaining` from the face with one common point** (`dom_subset_of_avoid`). -/
theorem r6FacePTwoInfRemaining_of_faceQ {k rL rR c c' : ℝ} (hQ : R6FaceQTwoInfRemaining.{u} k rL rR c c') :
    R6FacePTwoInfRemaining.{u} k rL rR c c' := by
  intro hdL hdR Ω _ _ P _ h W' ζ' αR βR βL αL ζαR ζβR ζβL ζαL hcfg R L η hV MR ML hMR hML r A A' ψ ψ' n n' s q hA
    hA'
  filter_upwards [hQ hdL hdR P h W' ζ' αR βR βL αL ζαR ζβR ζβL ζαL hcfg R L η hV MR ML hMR hML r A A' ψ ψ' n n' s q
    hA hA'] with ω hω hωA hωA' hωN
  obtain ⟨q', hq', hT, hmeet, hR⟩ := hω hωA hωA' hωN
  obtain ⟨hIc, hIsub, hIav⟩ := outer_chart_facts (n := n') (fun ω hω => (hA' ω hω).1)
    (fun ω hω => (hA' ω hω).2) hωA' hq'
  exact ⟨q', hq', dom_subset_of_avoid hIc (hIsub.trans hωN.2.2.2.1)
    (outer_frontier_subset_traceInf (n := n) (fun ω hω => (hA ω hω).1) (fun ω hω => (hA ω hω).2) hωA hωN.2.1)
    (hIav _ hT) hmeet, hR⟩

/-- **Named, unproved: R.6's face, shape `TwoInfInf`, with the inclusion reduced to one common point**
(as `R6FaceQMixedRemaining`; `r6FacePTwoInfInfRemaining_of_faceQ`). -/
def R6FaceQTwoInfInfRemaining (k rL rR c c' : ℝ) : Prop :=
  k / 2 - 4 < rL → k / 2 - 4 < rR →
  ∀ {Ω : Type u} [MeasurableSpace Ω] [StandardBorelSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (h : Ω → DistOn upperHalfPlaneOpens) (W' : ℝ≥0 → Ω → ℝ) (ζ' : Ω → ℝ≥0∞)
    (αR βR βL αL : Ω → ℝ≥0 → ℂ) (ζαR ζβR ζβL ζαL : Ω → ℝ≥0∞),
    IsR7OuterConfig k rL rR c c' P h W' ζ' αR βR βL αL ζαR ζβR ζβL ζαL →
    ∀ (R L : Ω → ℝ≥0 → ℂ) (η : Ω → ℝ → ℂ), IsR7Versions P W' αR αL R L η →
    ∀ MR ML : Ω → ℝ≥0 → ℂ, IsFrontierVersion P βR MR → IsFrontierVersion P βL ML →
    ∀ (r : ℝ≥0) (A A' : Set Ω) (ψ ψ' : Ω → ℂ → ℂ) (n n' : Ω → ℤ) (s q : ℚ),
      (∀ ω ∈ A, IsOuterCfgInf (R ω) (L ω) r (fun t : ℝ => W' t.toNNReal ω) (η ω) ∧
        IsCfJordanInf (R ω) (L ω) r (ψ ω)) →
      (∀ ω ∈ A', IsOuterCfgInf (R ω) (ML ω) (StripSys.rt s)
          (fun t : ℝ => W' t.toNNReal ω) (η ω) ∧
        IsCfJordanInf (R ω) (ML ω) (StripSys.rt s) (ψ' ω)) →
      ∀ᵐ ω ∂P, ω ∈ A → ω ∈ A' →
        ω ∈ nestRelEventInf R L r η ψ MR ML R ML s q →
        ∃ q' : ℚ, ((StripSys.rt q' : ℝ≥0) : ℝ≥0∞) <
            capLife (travAllInf R ML (StripSys.rt s) η ψ' ω) ∧
          pocketFibreInf (η ω) (cfPocket (R ω) (L ω) r) (firstHit (η ω) (cfArcRInf (R ω) (L ω) r 0))
              (clockOf (clockEnd (η ω) (cfPocket (R ω) (L ω) r) (firstHit (η ω) (cfArcRInf (R ω) (L ω) r 0)))
                (capInv (travAllInf R L r η ψ ω) (StripSys.rt q))) ≤
            PocketStopWallsFin.ambTime0Inf (η ω) (cfPocket (R ω) (ML ω) (StripSys.rt s))
              (firstHit (η ω) (cfArcRInf (R ω) (ML ω) (StripSys.rt s) 0)) (ψ' ω) (StripSys.rt q') ∧
          (((relChart (fun ω => shiftChart (pChart A' (fun ω => cfPocket (R ω)
                (ML ω) (StripSys.rt s)) ψ' ω) (n' ω))
              (travAllInf R ML (StripSys.rt s) η ψ') (StripSys.rt q')
                ω).dom : Set ℂ) ∩
            (relChart (fun ω => shiftChart (pChart A (fun ω => cfPocket (R ω) (L ω) r) ψ ω) (n ω))
              (travAllInf R L r η ψ) (StripSys.rt q) ω).dom).Nonempty ∧
          R6FaceR (fun _ : Fin 1 => rL) (fun _ : Fin 1 => rR) (fun _ : Fin 1 => rL)
            (fun _ : Fin 1 => k / 2 - 4)
            (fun i => geomLW (fun t ω => segDriver (travAllInf R L r η ψ ω) t) (fun _ => LP.twoSeedXL) i
              (StripSys.rt q) ω - segDriver (travAllInf R L r η ψ ω) (StripSys.rt q))
            (fun j => geomRW (fun t ω => segDriver (travAllInf R L r η ψ ω) t) (fun _ => LP.twoSeedXR) j
              (StripSys.rt q) ω - segDriver (travAllInf R L r η ψ ω) (StripSys.rt q))
            (fun i => geomLW (fun t ω => segDriver (travAllInf R ML
                (StripSys.rt s) η ψ' ω) t) (fun _ => LP.twoSeedXL) i (StripSys.rt q') ω -
              segDriver (travAllInf R ML (StripSys.rt s) η ψ' ω)
                (StripSys.rt q'))
            (fun j => geomRW (fun t ω => segDriver (travAllInf R ML
                (StripSys.rt s) η ψ' ω) t) (fun _ => LP.twoSeedXR) j (StripSys.rt q') ω -
              segDriver (travAllInf R ML (StripSys.rt s) η ψ' ω)
                (StripSys.rt q'))
            (relChart (fun ω => shiftChart (pChart A (fun ω => cfPocket (R ω) (L ω) r) ψ ω) (n ω))
              (travAllInf R L r η ψ) (StripSys.rt q) ω)
            (relChart (fun ω => shiftChart (pChart A' (fun ω => cfPocket (R ω)
                (ML ω) (StripSys.rt s)) ψ' ω) (n' ω))
              (travAllInf R ML (StripSys.rt s) η ψ') (StripSys.rt q') ω)
            (pocketSetInf A R L r η ψ n (StripSys.rt q) ω)
            (pocketSetInf A' R ML (StripSys.rt s) η ψ' n' (StripSys.rt q') ω)

/-- **`R6FacePTwoInfInfRemaining` from the face with one common point** (`dom_subset_of_avoid`). -/
theorem r6FacePTwoInfInfRemaining_of_faceQ {k rL rR c c' : ℝ} (hQ : R6FaceQTwoInfInfRemaining.{u} k rL rR c c') :
    R6FacePTwoInfInfRemaining.{u} k rL rR c c' := by
  intro hdL hdR Ω _ _ P _ h W' ζ' αR βR βL αL ζαR ζβR ζβL ζαL hcfg R L η hV MR ML hMR hML r A A' ψ ψ' n n' s q hA
    hA'
  filter_upwards [hQ hdL hdR P h W' ζ' αR βR βL αL ζαR ζβR ζβL ζαL hcfg R L η hV MR ML hMR hML r A A' ψ ψ' n n' s q
    hA hA'] with ω hω hωA hωA' hωN
  obtain ⟨q', hq', hT, hmeet, hR⟩ := hω hωA hωA' hωN
  obtain ⟨hIc, hIsub, hIav⟩ := outer_chart_factsInf (n := n') (fun ω hω => (hA' ω hω).1)
    (fun ω hω => (hA' ω hω).2) hωA' hq'
  exact ⟨q', hq', dom_subset_of_avoid hIc (hIsub.trans hωN.2.2.2.1)
    (outer_frontier_subset_traceInf (n := n) (fun ω hω => (hA ω hω).1) (fun ω hω => (hA ω hω).2) hωA hωN.2.1)
    (hIav _ hT) hmeet, hR⟩

end FaceQInf

/-! ### The final drop-in with all six faces reduced to one common point -/

section FinalQFull

open R7Outer R7Leaves R6Nest
open QuantumZipper (chiC)
open scoped Real

variable {k rL rR : ℝ}

/-- **The two-outer-arm inputs with all six faces reduced to one common point.** -/
def TwoOuterFaceQFullInputs (k rL rR : ℝ) : Prop :=
  PhaseCont.R7PhaseWordRemaining.{u} k (innerRight k rL rL (k / 2 - 4))
      (innerLeft k (k / 2 - 4) (k / 2 - 4) (k / 2 - 4))
      (π * chiC (16 / k) + (R7.thetaL k rR - π / 2) * chiC (16 / k) +
        (r7A k (k / 2 - 4) - r7A k (innerLeft k (k / 2 - 4) (k / 2 - 4) (k / 2 - 4))))
      (0 + (r7B k rL - r7B k (innerRight k rL rL (k / 2 - 4)))) ∧
    R6FaceQMixedRemaining.{u} k rL (k / 2 - 4) (π * chiC (16 / k) + (R7.thetaL k rR - π / 2) * chiC (16 / k)) 0 ∧
    R6FaceQMixedInfRemaining.{u} k rL (k / 2 - 4)
      (π * chiC (16 / k) + (R7.thetaL k rR - π / 2) * chiC (16 / k)) 0 ∧
    R6FaceQMixedInfInfRemaining.{u} k rL (k / 2 - 4)
      (π * chiC (16 / k) + (R7.thetaL k rR - π / 2) * chiC (16 / k)) 0 ∧
    R6Rel.R7OuterPhaseContMRemaining.{u} k rL (k / 2 - 4)
      (π * chiC (16 / k) + (R7.thetaL k rR - π / 2) * chiC (16 / k)) 0 ∧
    R6FaceQTwoRemaining.{u} k rL rR (π * chiC (16 / k)) 0 ∧
    R6FaceQTwoInfRemaining.{u} k rL rR (π * chiC (16 / k)) 0 ∧
    R6FaceQTwoInfInfRemaining.{u} k rL rR (π * chiC (16 / k)) 0

/-- The fully reduced two-outer-arm inputs give `TwoOuterFacePInputs`. -/
theorem twoOuterFacePInputs_of_faceQFull (h : TwoOuterFaceQFullInputs.{u} k rL rR) :
    TwoOuterFacePInputs.{u} k rL rR :=
  ⟨h.1, r6FacePMixedRemaining_of_faceQ h.2.1, r6FacePMixedInfRemaining_of_faceQ h.2.2.1,
    r6FacePMixedInfInfRemaining_of_faceQ h.2.2.2.1, h.2.2.2.2.1, r6FacePTwoRemaining_of_faceQ h.2.2.2.2.2.1,
    r6FacePTwoInfRemaining_of_faceQ h.2.2.2.2.2.2.1, r6FacePTwoInfInfRemaining_of_faceQ h.2.2.2.2.2.2.2⟩

/-- **The outer phase input from R.5 and R.6's faces, all reduced to one common point** (drop-in for
`R6Fin.r7OuterPhaseSideRemaining_of_cont_core`, without `hstrip` and `htwo`). -/
theorem r7OuterPhaseSideRemaining_of_cont_faceQFull_safe (h411 : Sec5.Cond44Ref.Prop411QStatement.{u})
    (h51 : Sec5.Cond44Ref.Prop51QStatement.{u}) (h47 : Sec5.Prop411Q.Lemma47QHitStatement.{u})
    (h47T : ∀ θ : ℝ, -(π / 2) < θ → θ < π / 2 → Sec5.RestartGen.Lemma47QHitTStatement.{u} θ)
    (haux7 : Sec4.Aux7Statement.{u} k) (h44 : AdmCode.Theorem12ParamCond44Statement.{u})
    (hA : Sec5.PartAInputsSixteenDivOfClearance)
    (hword : PhaseCont.R7PhaseWordRemaining.{u} k (innerRight k rL rL (k / 2 - 4)) (innerLeft k rR rR (k / 2 - 4))
      (π * chiC (16 / k) + (r7A k rR - r7A k (innerLeft k rR rR (k / 2 - 4))))
      (0 + (r7B k rL - r7B k (innerRight k rL rL (k / 2 - 4)))))
    (hface : R6FaceQMixedRemaining.{u} k rL rR (π * chiC (16 / k)) 0)
    (hfaceI : R6FaceQMixedInfRemaining.{u} k rL rR (π * chiC (16 / k)) 0)
    (hfaceII : R6FaceQMixedInfInfRemaining.{u} k rL rR (π * chiC (16 / k)) 0)
    (hk4 : 4 < k) (hrL : -2 < rL) (hrR : -2 < rR)
    (hcont : OuterPhNext.R7OuterPhaseContRemaining.{u} k rL rR)
    (htwoIn : k / 2 - 4 < rL → k / 2 - 4 < rR → TwoOuterFaceQFullInputs.{u} k rL rR) :
    OuterIn.R7OuterPhaseSideRemaining.{u} k rL rR :=
  r7OuterPhaseSideRemaining_of_cont_faceP_safe h411 h51 h47 h47T haux7 h44 hA hword
    (r6FacePMixedRemaining_of_faceQ hface) (r6FacePMixedInfRemaining_of_faceQ hfaceI)
    (r6FacePMixedInfInfRemaining_of_faceQ hfaceII) hk4 hrL hrR hcont
    fun hdL hdR => twoOuterFacePInputs_of_faceQFull (htwoIn hdL hdR)

end FinalQFull

end InteractingSLE.Sec7.R6Safe
