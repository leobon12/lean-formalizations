/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.R6CorMixed
import InteractingSLE.Spec.Sec7.R6FcWireInf

/-!
# R.6's face for the shape `MixedInf`, seed corner included (Astra's deterministic route)

Packet PROVE-R6-CORNER. The port of `R6CorMixed` to an outer pocket `C` opening at the flow seed (`IsOuterCfgInf`,
Jordan coordinate `Sec6.IsJordanCoordInf`, traversal `travAllInf`, fibre end `outerFibreEndInf`) with a bounded
contained pocket `U`: `inner_dom_subset_outer_dom_at_visitInf`, `hlater_outerInf` (the outer side of the common later
time through `PocketStopMarked.Outer`'s `…Inf` API), **`corner_face_sharedLInf`**, **`corner_face_sharedRInf`**, and
**`r6FaceSMixedInfRemaining`**: `R6Safe.R6FaceSMixedInfRemaining k rL rR c c'` for all parameters, with no input.
The outer pocket has no outgoing corner, so the inner landings need no corner exclusion; the outer aliveness at the
shared-arc landing uses `R6Fc.notMem_closure_of_ball_subsetInf`. Deterministic.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Filter Topology Metric
open QuantumZipper (H Hbar fwdMap fwdMapInv fwdHull)
open scoped NNReal ENNReal

namespace InteractingSLE.Sec7.R6Cor

open Sec6 PocketTraversal Lemma71C PocketJordan PocketCoord PocketCoupling PocketStop PocketStopField HOuter
  PocketWordAssembly PocketSeedOpen R6Safe R6Fc
open WangWu (chartAL chartAR)
open SupercriticalConformalCovariance (IsConformalBijection)

variable {Ω : Type*}

/-- **The same-time inclusion**, outer pocket opening at the flow seed (`inner_dom_subset_outer_dom_at_visit`). -/
theorem inner_dom_subset_outer_dom_at_visitInf {A A' : Set Ω} {R L R' L' : Ω → ℝ≥0 → ℂ} {r r' : ℝ≥0}
    {W : Ω → ℝ → ℝ} {η : Ω → ℝ → ℂ} {ψ ψ' : Ω → ℂ → ℂ} {n n' : Ω → ℤ} {ω : Ω}
    (hcfg : ∀ ω ∈ A, IsOuterCfgInf (R ω) (L ω) r (W ω) (η ω)) (hψ : ∀ ω ∈ A, IsCfJordanInf (R ω) (L ω) r (ψ ω))
    (hcfg' : ∀ ω ∈ A', IsCfPocketConfig (R' ω) (L' ω) r' (W ω) (η ω))
    (hψ' : ∀ ω ∈ A', IsCfJordan (R' ω) (L' ω) r' (ψ' ω)) (hω : ω ∈ A) (hω' : ω ∈ A')
    {q : ℝ≥0} (hq : (q : ℝ≥0∞) < capLife (travAllInf R L r η ψ ω))
    (hsub : cfPocket (R' ω) (L' ω) r' ⊆ cfPocket (R ω) (L ω) r)
    (hT0 : 0 ≤ outerFibreEndInf R L r η ψ q ω)
    (htip : η ω (outerFibreEndInf R L r η ψ q ω) ∈ cfPocket (R' ω) (L' ω) r') :
    ((curChart A' R' L' r' η ψ' n' (R5Phase.visitCap R' L' r' η ψ' ω (outerFibreEndInf R L r η ψ q ω)).toNNReal
      ω).dom : Set ℂ) ⊆ (curChartInf A R L r η ψ n q ω).dom := by
  have hG' : ∀ ω ∈ A', IsChangeConfigInc (R' ω) (L' ω) r' := fun ω hω => (hcfg' ω hω).conf
  have hCo' : ∀ ω ∈ A', IsOpen (cfPocket (R' ω) (L' ω) r') := fun ω hω =>
    isOpen_image_negInv' (hG' ω hω).isOpen_changePocket (hG' ω hω).changePocket_subset_H
  have hCH' : ∀ ω ∈ A', cfPocket (R' ω) (L' ω) r' ⊆ H := fun ω hω =>
    PocketJordan.image_negInv_subset_H (hG' ω hω).changePocket_subset_H
  obtain ⟨hc', hdom', hfwd'⟩ := R5Phase.shiftChart_dom_facts hCo' hCH' (fun ω hω => (hψ' ω hω).2.2.2.1) n' ω hω'
  obtain ⟨-, hlive, hdomT⟩ := R5Phase.visitCap_spec
    (c := fun ω => shiftChart (pChart A' (fun ω => cfPocket (R' ω) (L' ω) r') ψ' ω) (n' ω)) hω' (hcfg' ω hω')
    (hψ' ω hω') hc' hdom' hfwd' hT0 htip
  have hγ' : IsDrivenCurve (travAll R' L' r' η ψ' ω) := ((hcfg' ω hω').isDrivenCurve (hψ' ω hω')).1
  have hI : (curChart A' R' L' r' η ψ' n' (R5Phase.visitCap R' L' r' η ψ' ω
      (outerFibreEndInf R L r η ψ q ω)).toNNReal ω).IsConformal :=
    PocketStopSide.isConformal_relChart_of_driven hγ' hlive hc'
  obtain ⟨z, hzU, hzdom, hzphys⟩ := exists_outer_dom_near_tipInf (n := n) hcfg hψ hω hq (hCo' ω hω') htip (hsub htip)
  refine dom_subset_of_frontier_disjoint hI (disjoint_left.2 fun w hwI hwf => ?_)
    ⟨z, by rw [hdomT]; exact ⟨hzU, hzphys⟩, hzdom⟩
  rw [hdomT] at hwI
  obtain ⟨t, ht, hte⟩ := outer_frontier_subset_traceInf (n := n) hcfg hψ hω hq ⟨hsub hwI.1, hwf⟩
  refine hwI.2.2 ?_
  rw [(hcfg ω hω).trace.2.2 _ hT0]
  exact ⟨hwI.2.1, Or.inl (subset_closure ⟨t, ht, hte⟩)⟩


/-- **The common later time (outer pocket opening at the flow seed)**: for small `s, s'` a physical time `t₂` just
after `T = T_C(q)`
with `η(t₂) ∈ U` gives an inner capacity `q₂' = c_U(t₂) ∈ (q_T, q_T + s')` and an outer capacity
`q₂ ∈ (c_C(t₂), q + s)`; on `U`, `ψ'(z) ∈ K^U_{q₂'}` means `z ∈ K_{t₂}` (`R5Phase.visitCap_spec`), and then `z` is not
in `D_C(q₂) ⊆ ℍ ∖ K_{T⁰_C(q₂)}` since `T⁰_C(q₂) > t₂` (`HOuter.relDomain_subset_domain_ambTime0`,
`PocketStopMarked.Outer.ambTime0_le_iff`). -/
theorem hlater_outerInf {A A' : Set Ω} {R L R' L' : Ω → ℝ≥0 → ℂ} {r r' : ℝ≥0}
    {W : Ω → ℝ → ℝ} {η : Ω → ℝ → ℂ} {ψ ψ' : Ω → ℂ → ℂ} {n n' : Ω → ℤ} {ω : Ω}
    (hcfg : ∀ ω ∈ A, IsOuterCfgInf (R ω) (L ω) r (W ω) (η ω)) (hψ : ∀ ω ∈ A, IsCfJordanInf (R ω) (L ω) r (ψ ω))
    (hcfg' : ∀ ω ∈ A', IsCfPocketConfig (R' ω) (L' ω) r' (W ω) (η ω))
    (hψ' : ∀ ω ∈ A', IsCfJordan (R' ω) (L' ω) r' (ψ' ω)) (hω : ω ∈ A) (hω' : ω ∈ A')
    {q : ℝ≥0} (hq : (q : ℝ≥0∞) < capLife (travAllInf R L r η ψ ω))
    (hsub : cfPocket (R' ω) (L' ω) r' ⊆ cfPocket (R ω) (L ω) r)
    (hT0 : 0 ≤ outerFibreEndInf R L r η ψ q ω)
    (htip : η ω (outerFibreEndInf R L r η ψ q ω) ∈ cfPocket (R' ω) (L' ω) r')
    {WC WU : ℝ → ℝ} {t₁ t₁' : ℝ≥0} (hqt₁ : q < t₁) (ht₁ : (t₁ : ℝ≥0∞) < capLife (travAllInf R L r η ψ ω))
    (hqTt₁' : R5Phase.visitCap R' L' r' η ψ' ω (outerFibreEndInf R L r η ψ q ω) < t₁')
    (hCdom : ∀ q₂ : ℝ≥0, q₂ < t₁ → ((curChartInf A R L r η ψ n q₂ ω).dom : Set ℂ) =
      cfPocket (R ω) (L ω) r ∩ ψ ω ⁻¹' (H \ fwdHull WC q₂))
    (hUdom : ∀ q₂ : ℝ≥0, q₂ < t₁' → ((curChart A' R' L' r' η ψ' n' q₂ ω).dom : Set ℂ) =
      cfPocket (R' ω) (L' ω) r' ∩ ψ' ω ⁻¹' (H \ fwdHull WU q₂)) :
    ∀ s > 0, ∀ s' > 0, ∃ q₂ q₂' : ℝ, (q : ℝ) ≤ q₂ ∧ q₂ < q + s ∧
      R5Phase.visitCap R' L' r' η ψ' ω (outerFibreEndInf R L r η ψ q ω) < q₂' ∧
      q₂' < R5Phase.visitCap R' L' r' η ψ' ω (outerFibreEndInf R L r η ψ q ω) + s' ∧
      ∀ z ∈ cfPocket (R' ω) (L' ω) r', ψ' ω z ∈ fwdHull WU q₂' → ψ ω z ∈ fwdHull WC q₂ := by
  intro s hs s' hs'
  set T := outerFibreEndInf R L r η ψ q ω with hTdef
  set qT := R5Phase.visitCap R' L' r' η ψ' ω T with hqTdef
  have hcf := hcfg ω hω
  have hG : ∀ ω ∈ A, IsChangeConfigInc (R ω) (L ω) r := fun ω hω => (hcfg ω hω).conf
  have hCo : ∀ ω ∈ A, IsOpen (cfPocket (R ω) (L ω) r) := fun ω hω =>
    isOpen_image_negInv' (hG ω hω).isOpen_changePocket (hG ω hω).changePocket_subset_H
  have hCH : ∀ ω ∈ A, cfPocket (R ω) (L ω) r ⊆ H := fun ω hω =>
    PocketJordan.image_negInv_subset_H (hG ω hω).changePocket_subset_H
  have hG' : ∀ ω ∈ A', IsChangeConfigInc (R' ω) (L' ω) r' := fun ω hω => (hcfg' ω hω).conf
  have hCo' : ∀ ω ∈ A', IsOpen (cfPocket (R' ω) (L' ω) r') := fun ω hω =>
    isOpen_image_negInv' (hG' ω hω).isOpen_changePocket (hG' ω hω).changePocket_subset_H
  have hCH' : ∀ ω ∈ A', cfPocket (R' ω) (L' ω) r' ⊆ H := fun ω hω =>
    PocketJordan.image_negInv_subset_H (hG' ω hω).changePocket_subset_H
  have hγ : IsDrivenCurve (travAllInf R L r η ψ ω) := (hcf.props (hψ ω hω)).1
  have hPo := hcf.toPocketInf (hψ ω hω)
  have hqlive : ENNReal.ofReal (q : ℝ) < capLife (travAllInf R L r η ψ ω) := by
    rw [ENNReal.ofReal_coe_nnreal]; exact hq
  obtain ⟨hc0, hcq⟩ := hγ.capInv_spec q.coe_nonneg hqlive
  obtain ⟨hTmem, hTrel⟩ := PocketStopMarked.Outer.relTimeInf_fibre_clockOf hPo hc0
  replace hTmem : firstHit (η ω) (cfArcRInf (R ω) (L ω) r 0) ≤ T := hTmem
  replace hTrel : PocketStopMarked.relTimeInf (η ω) (cfPocket (R ω) (L ω) r) (firstHit (η ω) (cfArcRInf (R ω) (L ω)
      r 0)) T =
      capInv (travAllInf R L r η ψ ω) q := hTrel
  have hrelT : PocketStopMarked.relCapInf (η ω) (cfPocket (R ω) (L ω) r) (firstHit (η ω) (cfArcRInf (R ω) (L ω) r
      0)) (ψ ω) T = q := by
    unfold PocketStopMarked.relCapInf
    rw [hTrel]
    exact hcq
  obtain ⟨hP', hJ'⟩ := R5Ref.pocket_of_cfg (hcfg' ω hω') (hψ' ω hω')
  have hAC := (hcfg' ω hω').attach
  have hTI := hP'.mem_Ioo_of_mem hT0 htip
  -- a physical time just after `T`
  set s₁ := min s ((t₁ : ℝ) - q) with hs₁
  have hs₁0 : 0 < s₁ := lt_min hs (sub_pos.2 (by exact_mod_cast hqt₁))
  set s₁' := min s' ((t₁' : ℝ) - qT) with hs₁'
  have hs₁'0 : 0 < s₁' := lt_min hs' (by linarith)
  have hcC := PocketStopMarked.Outer.continuousOn_relCapInf hPo T hTmem
  have hcU := PocketStopMarked.continuousOn_relCap hP' hAC hJ' T ⟨hTI.1.le, hTI.2⟩
  have hσ : T < firstHit (η ω) (cfArcR (R' ω) (L' ω) r' 0) := hTI.2
  have hmem : ∀ σ₀ τ₀ : ℝ, τ₀ ≤ T → T < σ₀ → Ico τ₀ σ₀ ∈ 𝓝[>] T := fun σ₀ τ₀ h1 h2 =>
    mem_of_superset (Ioo_mem_nhdsGT h2) fun t ht => ⟨h1.trans ht.1.le, ht.2⟩
  have e2 : ∀ᶠ t in 𝓝[>] T, PocketStopMarked.relCapInf (η ω) (cfPocket (R ω) (L ω) r)
      (firstHit (η ω) (cfArcRInf (R ω) (L ω) r 0)) (ψ ω) t < q + s₁ := by
    have h := (hcC.mono_of_mem_nhdsWithin (mem_of_superset self_mem_nhdsWithin fun t ht =>
      show firstHit (η ω) (cfArcRInf (R ω) (L ω) r 0) ≤ t from hTmem.trans (le_of_lt ht))).tendsto
    rw [hrelT] at h
    exact h.eventually (gt_mem_nhds (by linarith))
  have e3 : ∀ᶠ t in 𝓝[>] T, PocketStopMarked.relCap (η ω) (cfPocket (R' ω) (L' ω) r')
      (firstHit (η ω) (cfArcR (R' ω) (L' ω) r' 1)) (firstHit (η ω) (cfArcR (R' ω) (L' ω) r' 0)) (ψ' ω) t <
        qT + s₁' := by
    have h := (hcU.mono_of_mem_nhdsWithin (hmem _ _ hTI.1.le hTI.2)).tendsto
    exact h.eventually (gt_mem_nhds (by show qT < qT + s₁'; linarith))
  have e4 : ∀ᶠ t in 𝓝[>] T, η ω t ∈ cfPocket (R' ω) (L' ω) r' := by
    have h := ((hcf.trace.2.1 T hT0).mono_of_mem_nhdsWithin
      (mem_of_superset self_mem_nhdsWithin fun t ht => le_of_lt (lt_of_le_of_lt hT0 ht))).tendsto
    exact h.eventually ((hCo' ω hω').mem_nhds htip)
  obtain ⟨t₂, ht₂I, ht₂C, ht₂U, ht₂η⟩ :=
    ((show ∀ᶠ t in 𝓝[>] T, t ∈ Ioo T _ from Ioo_mem_nhdsGT hσ).and (e2.and (e3.and e4))).exists
  have ht₂C' : firstHit (η ω) (cfArcRInf (R ω) (L ω) r 0) ≤ t₂ := hTmem.trans ht₂I.1.le
  have ht₂U' : t₂ ∈ Ico (firstHit (η ω) (cfArcR (R' ω) (L' ω) r' 1)) (firstHit (η ω) (cfArcR (R' ω) (L' ω) r' 0)) :=
    ⟨hTI.1.le.trans ht₂I.1.le, ht₂I.2⟩
  have ht₂0 : 0 ≤ t₂ := hT0.trans ht₂I.1.le
  set q₂' := R5Phase.visitCap R' L' r' η ψ' ω t₂ with hq₂'def
  have hq₂' : qT < q₂' := relCap_lt_relCap_of_visit hP' hAC hJ' ⟨hTI.1.le, hTI.2⟩ ht₂U' ht₂I.1 hT0 htip
  set c₂ := PocketStopMarked.relCapInf (η ω) (cfPocket (R ω) (L ω) r) (firstHit (η ω) (cfArcRInf (R ω) (L ω) r 0))
      (ψ ω) t₂ with hc₂
  have hc₂q : (q : ℝ) ≤ c₂ := by
    rw [← hrelT]; exact PocketStopMarked.Outer.monotoneOn_relCapInf hPo hTmem ht₂C' ht₂I.1.le
  set q₂ := (c₂ + (q + s₁)) / 2 with hq₂def
  have hq₂lo : c₂ < q₂ := by linarith
  have hq₂hi : q₂ < q + s₁ := by linarith
  refine ⟨q₂, q₂', by linarith, hq₂hi.trans_le (by linarith [min_le_left s ((t₁ : ℝ) - q)]), hq₂',
    ht₂U.trans_le (by linarith [min_le_left s' ((t₁' : ℝ) - qT)]), fun z hzU hzK => ?_⟩
  -- `z` is in the physical hull at `t₂`
  have hq₂'0 : 0 ≤ q₂' := (R5Phase.visitCap_spec (c := fun ω => shiftChart (pChart A' (fun ω =>
    cfPocket (R' ω) (L' ω) r') ψ' ω) (n' ω)) hω' (hcfg' ω hω') (hψ' ω hω')
    (R5Phase.shiftChart_dom_facts hCo' hCH' (fun ω hω => (hψ' ω hω).2.2.2.1) n' ω hω').1
    (R5Phase.shiftChart_dom_facts hCo' hCH' (fun ω hω => (hψ' ω hω).2.2.2.1) n' ω hω').2.1
    (R5Phase.shiftChart_dom_facts hCo' hCH' (fun ω hω => (hψ' ω hω).2.2.2.1) n' ω hω').2.2 ht₂0 ht₂η).1.le
  obtain ⟨hc', hdom', hfwd'⟩ := R5Phase.shiftChart_dom_facts hCo' hCH' (fun ω hω => (hψ' ω hω).2.2.2.1) n' ω hω'
  obtain ⟨-, -, hdomt₂⟩ := R5Phase.visitCap_spec
    (c := fun ω => shiftChart (pChart A' (fun ω => cfPocket (R' ω) (L' ω) r') ψ' ω) (n' ω)) hω' (hcfg' ω hω')
    (hψ' ω hω') hc' hdom' hfwd' ht₂0 ht₂η
  have hq₂'U : q₂' < qT + s₁' := ht₂U
  have hq₂'t : q₂'.toNNReal < t₁' := by
    rw [← NNReal.coe_lt_coe, Real.coe_toNNReal _ hq₂'0]
    linarith [min_le_right s' ((t₁' : ℝ) - qT)]
  have hzt₂ : z ∈ fwdHull (W ω) t₂ := by
    by_contra hn
    have hz : z ∈ ((curChart A' R' L' r' η ψ' n' q₂'.toNNReal ω).dom : Set ℂ) := by
      show z ∈ ((relChart (fun ω => shiftChart (pChart A' (fun ω => cfPocket (R' ω) (L' ω) r') ψ' ω) (n' ω))
        (travAll R' L' r' η ψ') q₂'.toNNReal ω).dom : Set ℂ)
      rw [hdomt₂]
      exact ⟨hzU, hCH' ω hω' hzU, hn⟩
    rw [hUdom _ hq₂'t, Real.coe_toNNReal _ hq₂'0] at hz
    exact hz.2.2 hzK
  -- and hence in the outer hull at `q₂`
  by_contra hzC
  have hq₂0 : 0 ≤ q₂ := (q.coe_nonneg).trans (by linarith)
  have hq₂t : q₂.toNNReal < t₁ := by
    rw [← NNReal.coe_lt_coe, Real.coe_toNNReal _ hq₂0]
    linarith [min_le_right s ((t₁ : ℝ) - q)]
  have hq₂live : ((q₂.toNNReal : ℝ≥0) : ℝ≥0∞) < capLife (travAllInf R L r η ψ ω) :=
    lt_trans (by exact_mod_cast hq₂t) ht₁
  have hzCq : z ∈ ((curChartInf A R L r η ψ n q₂.toNNReal ω).dom : Set ℂ) := by
    rw [hCdom _ hq₂t, Real.coe_toNNReal _ hq₂0]
    exact ⟨hsub hzU, (hψ ω hω).2.2.2.1.2.mapsTo (hsub hzU), hzC⟩
  rw [relChart_dom_eq_inter (n := n) hCo hCH (fun ω hω => (hψ ω hω).2.2.2.1) hω hγ hq₂live] at hzCq
  have hJarc : IsJordanCoordInf (cfPocket (R ω) (L ω) r) (cfArcRInf (R ω) (L ω) r 0) (ψ ω) := by
    rw [IsChangeConfigInc.cfArcRInf_zero]; exact hψ ω hω
  have hq₂live' : ENNReal.ofReal ((q₂.toNNReal : ℝ≥0) : ℝ) < capLife (travAllInf R L r η ψ ω) := by
    rw [ENNReal.ofReal_coe_nnreal]; exact hq₂live
  have hz' := relDomain_subset_domain_ambTime0Inf hcf.erase hcf.trace (hCH ω hω) hJarc
    hγ (q₂.toNNReal).coe_nonneg hq₂live' hzCq
  have hamb : t₂ < PocketStopWallsFin.ambTime0Inf (η ω) (cfPocket (R ω) (L ω) r) (firstHit (η ω) (cfArcRInf (R ω) (L
      ω) r 0)) (ψ ω)
      ((q₂.toNNReal : ℝ≥0) : ℝ) := by
    by_contra hle
    have h := (PocketStopMarked.Outer.ambTime0Inf_le_iff hPo (q₂.toNNReal).coe_nonneg hq₂live' ht₂C').1
      (not_lt.1 hle)
    rw [Real.coe_toNNReal _ hq₂0] at h
    linarith
  exact hz'.2 (QuantumZipper.fwdHull_mono.1 hamb.le hzt₂)


/-- **R.6's face for the shape `MixedInf` (outer pocket opening at the flow seed), shared wall `L`** (as
`corner_face_sharedL`). -/
theorem corner_face_sharedLInf {A A' : Set Ω} {R L R' : Ω → ℝ≥0 → ℂ} {r r' : ℝ≥0} {W : Ω → ℝ → ℝ}
    {η : Ω → ℝ → ℂ} {ψ ψ' : Ω → ℂ → ℂ} {n n' : Ω → ℤ} {ω : Ω}
    (hcfg : ∀ ω ∈ A, IsOuterCfgInf (R ω) (L ω) r (W ω) (η ω)) (hψ : ∀ ω ∈ A, IsCfJordanInf (R ω) (L ω) r (ψ ω))
    (hcfg' : ∀ ω ∈ A', IsCfPocketConfig (R' ω) (L ω) r' (W ω) (η ω))
    (hψ' : ∀ ω ∈ A', IsCfJordan (R' ω) (L ω) r' (ψ' ω)) (hω : ω ∈ A) (hω' : ω ∈ A')
    {q : ℝ≥0} (hq0 : 0 < q) (hq : (q : ℝ≥0∞) < capLife (travAllInf R L r η ψ ω))
    (hsub : cfPocket (R' ω) (L ω) r' ⊆ cfPocket (R ω) (L ω) r)
    (hT0 : 0 ≤ outerFibreEndInf R L r η ψ q ω)
    (htip : η ω (outerFibreEndInf R L r η ψ q ω) ∈ cfPocket (R' ω) (L ω) r') :
    ∃ εW > 0, ∀ q' : ℝ≥0, innerRelCap R' L r' η ψ' (outerFibreEndInf R L r η ψ q ω) ω < q' →
      (q' : ℝ) < innerRelCap R' L r' η ψ' (outerFibreEndInf R L r η ψ q ω) ω + εW →
      ((curChart A' R' L r' η ψ' n' q' ω).dom : Set ℂ) ⊆ (curChartInf A R L r η ψ n q ω).dom →
      ∀ ρL ρR σL σR vL vR wL wR : Fin 1 → ℝ, vL 0 = seedLInf R L r η ψ q ω → vR 0 = seedRInf R L r η ψ q ω →
        wL 0 = seedL R' L r' η ψ' q' ω → wR 0 = seedR R' L r' η ψ' q' ω → ρR 0 = σR 0 →
        R6FaceR ρL ρR σL σR vL vR wL wR (curChartInf A R L r η ψ n q ω) (curChart A' R' L r' η ψ' n' q' ω)
          (H \ ((curChartInf A R L r η ψ n q ω).dom : Set ℂ)) (H \ ((curChart A' R' L r' η ψ' n' q' ω).dom : Set ℂ))
              := by
  classical
  -- the outer pocket
  have hcf := hcfg ω hω
  have hG : ∀ ω ∈ A, IsChangeConfigInc (R ω) (L ω) r := fun ω hω => (hcfg ω hω).conf
  have hCo : ∀ ω ∈ A, IsOpen (cfPocket (R ω) (L ω) r) := fun ω hω =>
    isOpen_image_negInv' (hG ω hω).isOpen_changePocket (hG ω hω).changePocket_subset_H
  have hCH : ∀ ω ∈ A, cfPocket (R ω) (L ω) r ⊆ H := fun ω hω =>
    PocketJordan.image_negInv_subset_H (hG ω hω).changePocket_subset_H
  have hψc : ∀ ω ∈ A, IsConformalBijection (ψ ω) (cfPocket (R ω) (L ω) r) H := fun ω hω => (hψ ω hω).2.2.2.1
  have hJ : Sec6.IsJordanCoordInf (cfPocket (R ω) (L ω) r) (cfPt (closePt (R ω) (L ω) r)) (ψ ω) := hψ ω hω
  have hγ : IsDrivenCurve (travAllInf R L r η ψ ω) := (hcf.props (hψ ω hω)).1
  obtain ⟨t₁, hqt₁, ht₁⟩ := ENNReal.lt_iff_exists_nnreal_btwn.1 hq
  have hqt₁' : q < t₁ := by exact_mod_cast hqt₁
  obtain ⟨E₀, hE₀, hE₀c, hE₀m, WC, hWC, hWC0, hWCeq, ηC, hηC, hηCeq, hCf⟩ :=
    chart_factsInf (n := n) hCo hCH hψc hJ hω hγ ht₁
  obtain ⟨hOc, hOdom, hOfwd, hOE, hOEc⟩ := hCf q hqt₁'
  have hq0' : (0 : ℝ) < q := by exact_mod_cast hq0
  have hWCq : ∀ s ∈ Icc (0 : ℝ) q, segDriver (travAllInf R L r η ψ ω) s.toNNReal = WC s := fun s hs =>
    hWCeq s ⟨hs.1, hs.2.trans (by exact_mod_cast hqt₁'.le)⟩
  have hvR : seedRInf R L r η ψ q ω = chartAR WC q := seedR_eq hWC hWCq
  have hvL : seedLInf R L r η ψ q ω = chartAL WC q := seedL_eq hWC hWCq
  obtain ⟨hFc, hFeq, hFm⟩ := extendFrom_props hηC hWC hWC0 q.coe_nonneg
  have hTC : η ω (outerFibreEndInf R L r η ψ q ω) ∈ cfPocket (R ω) (L ω) r := hsub htip
  have htrace : capTrace (travAllInf R L r η ψ ω) q = ψ ω (η ω (outerFibreEndInf R L r η ψ q ω)) := rfl
  have h0cl : ((0 : ℝ) : ℂ) ∈ closure H := by
    rw [QuantumZipper.CA.Car.closure_H_eq_Hbar]; exact real_mem_Hbar 0
  have htipC : extendFrom H (fwdMapInv WC q) ((0 : ℝ) : ℂ) ∈ H := by
    have h1 := hηC.tendsto_fwdMapInv_tip hWC hWC0 q.coe_nonneg
    rw [← Complex.ofReal_zero] at h1
    rw [extendFrom_eq h0cl h1, hηCeq q q.coe_nonneg (by exact_mod_cast hqt₁'.le)]
    change capTrace (travAllInf R L r η ψ ω) q ∈ H
    rw [htrace]
    exact (hψc ω hω).2.mapsTo hTC
  have hvR0 : 0 < chartAR WC q := chartAR_pos_of_tip hηC hWC hWC0 q.coe_nonneg htipC
  have hvL0 : chartAL WC q < 0 := chartAL_neg_of_tip hηC hWC hWC0 q.coe_nonneg htipC
  set EO : ℂ → ℂ := fun z => E₀ (extendFrom H (fwdMapInv WC q) z) with hEOdef
  have hOphys : ((curChartInf A R L r η ψ n q ω).dom : Set ℂ) ⊆ H \ fwdHull (W ω) (outerFibreEndInf R L r η ψ q ω) := by
    intro w hwO
    have hzD : w ∈ cfPocket (R ω) (L ω) r ∩
        ψ ω ⁻¹' (H \ fwdHull (fun s : ℝ => segDriver (travAllInf R L r η ψ ω) s.toNNReal) q) := by
      rw [← relChart_dom_eq_inter (n := n) hCo hCH hψc hω hγ hq]; exact hwO
    exact outer_dom_physInf hcfg hψ hω hq hzD
  -- the inner pocket
  have hcf' := hcfg' ω hω'
  have hG' : ∀ ω ∈ A', IsChangeConfigInc (R' ω) (L ω) r' := fun ω hω => (hcfg' ω hω).conf
  have hCo' : ∀ ω ∈ A', IsOpen (cfPocket (R' ω) (L ω) r') := fun ω hω =>
    isOpen_image_negInv' (hG' ω hω).isOpen_changePocket (hG' ω hω).changePocket_subset_H
  have hCH' : ∀ ω ∈ A', cfPocket (R' ω) (L ω) r' ⊆ H := fun ω hω =>
    PocketJordan.image_negInv_subset_H (hG' ω hω).changePocket_subset_H
  have hψc' : ∀ ω ∈ A', IsConformalBijection (ψ' ω) (cfPocket (R' ω) (L ω) r') H := fun ω hω =>
    (hψ' ω hω).2.2.2.1
  have h0U := PocketMarks.zero_notMem_closure_of_rightLo_pos hcf'.conf hcf'.bounded
  have hUb : Bornology.IsBounded (cfPocket (R' ω) (L ω) r') := isBounded_image_negInv h0U
  have hx₀' : cfPt (openPt (R' ω) (L ω) r') ∉ cfPocket (R' ω) (L ω) r' := hcf'.conf.cfPt_openPt_notMem
  have hJ' : Sec6.IsJordanCoord (cfPocket (R' ω) (L ω) r') (cfPt (openPt (R' ω) (L ω) r'))
      (cfPt (closePt (R' ω) (L ω) r')) (ψ' ω) := hψ' ω hω'
  have hγ' : IsDrivenCurve (travAll R' L r' η ψ' ω) := (hcf'.isDrivenCurve (hψ' ω hω')).1
  obtain ⟨hc', hdom', hfwd'⟩ := R5Phase.shiftChart_dom_facts hCo' hCH' hψc' n' ω hω'
  obtain ⟨hqTpos, hqTlive, hqTdom⟩ := R5Phase.visitCap_spec
    (c := fun ω => shiftChart (pChart A' (fun ω => cfPocket (R' ω) (L ω) r') ψ' ω) (n' ω)) hω' hcf' (hψ' ω hω')
    hc' hdom' hfwd' hT0 htip
  set qT := R5Phase.visitCap R' L r' η ψ' ω (outerFibreEndInf R L r η ψ q ω) with hqTdef
  have hqT0 : (0 : ℝ) ≤ qT := hqTpos.le
  have hqTc : ((qT.toNNReal : ℝ≥0) : ℝ) = qT := Real.coe_toNNReal _ hqT0
  obtain ⟨t₁', hqTt₁', ht₁'⟩ := ENNReal.lt_iff_exists_nnreal_btwn.1 hqTlive
  have hqTt : qT.toNNReal < t₁' := by exact_mod_cast hqTt₁'
  have hqTt' : qT < t₁' := by rw [← hqTc]; exact_mod_cast hqTt
  obtain ⟨E₀', hE₀', hE₀'c, hE₀'m, WU, hWU, hWU0, hWUeq, ηU, hηU, hηUeq, hUf⟩ :=
    chart_facts (n := n') hCo' hCH' hψc' hUb hx₀' hJ' hω' hγ' ht₁'
  obtain ⟨hI₀c, hI₀dom, hI₀fwd, hI₀E, hI₀Ec⟩ := hUf qT.toNNReal hqTt
  rw [hqTc] at hI₀dom hI₀fwd hI₀E hI₀Ec
  -- the inner tip at the visit time
  obtain ⟨hP', hJ'arc⟩ := R5Ref.pocket_of_cfg hcf' (hψ' ω hω')
  have hvisit : outerFibreEndInf R L r η ψ q ω ∈ visitSet (η ω) (cfPocket (R' ω) (L ω) r')
      (firstHit (η ω) (cfArcR (R' ω) (L ω) r' 1)) (firstHit (η ω) (cfArcR (R' ω) (L ω) r' 0)) :=
    ⟨hP'.mem_Ioo_of_mem hT0 htip, htip⟩
  have htrU : capTrace (travAll R' L r' η ψ' ω) qT.toNNReal = ψ' ω (η ω (outerFibreEndInf R L r η ψ q ω)) :=
    PocketStopSide.capTrace_relCap_of_visit hP' hcf'.attach hJ'arc hvisit
  have hψ'T : ψ' ω (η ω (outerFibreEndInf R L r η ψ q ω)) ∈ H := (hψc' ω hω').2.mapsTo htip
  have htipU : extendFrom H (fwdMapInv WU qT) ((0 : ℝ) : ℂ) = ψ' ω (η ω (outerFibreEndInf R L r η ψ q ω)) := by
    have h1 := hηU.tendsto_fwdMapInv_tip hWU hWU0 hqT0
    rw [← Complex.ofReal_zero] at h1
    rw [extendFrom_eq h0cl h1, hηUeq qT hqT0 hqTt'.le, ← htrU]
    simp only [capTrace, hqTc]
  have hwR0 : 0 < chartAR WU qT := chartAR_pos_of_tip hηU hWU hWU0 hqT0 (htipU ▸ hψ'T)
  have hwL0 : chartAL WU qT < 0 := chartAL_neg_of_tip hηU hWU hWU0 hqT0 (htipU ▸ hψ'T)
  have hwLR : chartAL WU qT < chartAR WU qT := hwL0.trans hwR0
  obtain ⟨hFTc, hFTeq, hFTm⟩ := extendFrom_props hηU hWU hWU0 hqT0
  set EI₀ : ℂ → ℂ := fun z => E₀' (extendFrom H (fwdMapInv WU qT) z) with hEI₀def
  set tip := η ω (outerFibreEndInf R L r η ψ q ω) with htipdef
  have hEI₀0 : EI₀ ((0 : ℝ) : ℂ) = tip := by
    simp only [hEI₀def, htipU]
    rw [hE₀' hψ'T]
    exact (hψc' ω hω').2.injOn.leftInvOn_invFunOn htip
  -- the same-time inclusion and the two descriptions of the inner domain
  have hI₀O := inner_dom_subset_outer_dom_at_visitInf (n := n) (n' := n') hcfg hψ hcfg' hψ' hω hω' hq hsub hT0 htip
  -- the inverse of the inner Jordan coordinate on `ℍ`
  have hinvU : ∀ k ∈ H, E₀' k ∈ cfPocket (R' ω) (L ω) r' ∧ ψ' ω (E₀' k) = k := fun k hk => by
    rw [hE₀' hk]
    have hex : ∃ a ∈ cfPocket (R' ω) (L ω) r', ψ' ω a = k := (hψc' ω hω').2.surjOn hk
    exact ⟨Function.invFunOn_mem hex, Function.invFunOn_eq hex⟩
  have hullImg : ∀ k ∈ fwdHull WU qT, E₀' k ∈ fwdHull (W ω) (outerFibreEndInf R L r η ψ q ω) := by
    intro k hk
    have hkH : k ∈ H := QuantumZipper.fwdHull_mono.2 _ hk
    obtain ⟨heU, hek⟩ := hinvU k hkH
    by_contra hn
    have hmem : E₀' k ∈ ((curChart A' R' L r' η ψ' n' qT.toNNReal ω).dom : Set ℂ) := by
      show E₀' k ∈ ((relChart (fun ω => shiftChart (pChart A' (fun ω => cfPocket (R' ω) (L ω) r') ψ' ω) (n' ω))
        (travAll R' L r' η ψ') qT.toNNReal ω).dom : Set ℂ)
      rw [hqTdom]; exact ⟨heU, hCH' ω hω' heU, hn⟩
    rw [hI₀dom] at hmem
    have := hmem.2
    rw [Set.mem_preimage, hek] at this
    exact this.2 hk
  have hnotD : ∀ t ∈ Icc (chartAL WU qT) (chartAR WU qT),
      EI₀ t ∉ ((curChartInf A R L r η ψ n q ω).dom : Set ℂ) := fun t ht =>
    notMem_of_mem_closure_of_subset (curChartInf A R L r η ψ n q ω).dom.isOpen hOphys
      (mem_closure_of_dead hE₀'c (QuantumZipper.fwdHull_mono.2 _) hullImg
        (dead_of_mem_Icc hηU hWU hWU0 hqTpos hwLR ht))
  have hb0 : 0 ≤ (extendFrom H (fwdMapInv WU qT) (chartAR WU qT : ℂ)).re :=
    R6Fd.le_re_landR hηU hWU hWU0 hqTpos (x := 0) (by
      simpa using ConformalImageFull.zero_mem_closure_fwdHull hWU hWU0 hqTpos)
  have harcR : ∀ t : ℝ, chartAR WU qT < t → ∃ θ ∈ Ioo (leftLo (R' ω) (L ω) r') (leftHi (R' ω) (L ω) r'),
      EI₀ t = R6Fd.wallPt (L ω) θ := by
    intro t ht
    obtain ⟨him, hgt⟩ := landR_re_lt hηU hWU hWU0 hqTpos hwLR ht
    have hpm := hE₀'m (hFTm (real_mem_Hbar t))
    have hψp : ψ' ω (EI₀ t) = extendFrom H (fwdMapInv WU qT) (t : ℂ) :=
      jordan_comp_ext hJ' hE₀' hE₀'c hE₀'m (hFTm (real_mem_Hbar t))
    have hpU : EI₀ t ∉ cfPocket (R' ω) (L ω) r' := fun h => by
      have := (hψc' ω hω').2.mapsTo h
      rw [hψp] at this
      have h2 : (0 : ℝ) < (extendFrom H (fwdMapInv WU qT) (t : ℂ)).im := this
      rw [him] at h2
      exact lt_irrefl _ h2
    have hpfr : EI₀ t ∈ frontier (cfPocket (R' ω) (L ω) r') :=
      ⟨hpm.1, by rw [(hCo' ω hω').interior_eq]; exact hpU⟩
    exact frontier_pos_left_arc hcf'.conf h0U hcf'.oriented (hψ' ω hω') hpfr hpm.2 (by rw [hψp]; linarith)
  have hθI : ∀ θ ∈ Ioo (leftLo (R' ω) (L ω) r') (leftHi (R' ω) (L ω) r'), θ ∈ Ioc (0 : ℝ) 1 := by
    obtain ⟨-, -, -, -, hb', -, -, -⟩ := hcf'.conf.changeCorner_props
    exact fun θ hθ => ⟨(hcf'.conf.leftLo_pos h0U).trans hθ.1, hθ.2.le.trans hb'.2⟩
  have hnotA : ∀ t : ℝ, chartAR WU qT < t → EI₀ t ∉ cfPocket (R ω) (L ω) r := by
    intro t ht
    obtain ⟨θ, hθ, he⟩ := harcR t ht
    rw [he]
    exact R6Fd.wallPt_notMem hcf.conf (Or.inr rfl) (hθI θ hθ)
  set b := chartAR WU qT + 2 with hbdef
  set ty := chartAR WU qT + 1 with htydef
  have hnot : ∀ t ∈ Ioo (chartAL WU qT) b, EI₀ t ∉ ((curChartInf A R L r η ψ n q ω).dom : Set ℂ) := by
    intro t ht
    rcases le_or_gt t (chartAR WU qT) with h | h
    · exact hnotD t ⟨ht.1.le, h⟩
    · exact fun hm => hnotA t h (hOc.dom_subset hm |> fun _ => by rw [hOdom] at hm; exact hm.1)
  have hEI₀C : ∀ z ∈ Hbar, EI₀ z ∈ closure (cfPocket (R ω) (L ω) r) :=
    fun z hz => closure_mono hsub (hE₀'m (hFTm hz)).1
  obtain ⟨C₀, hC₀⟩ := exists_norm_fwdMapInv_sub_le hWC hWC0 q.coe_nonneg
  have hbdd : ∀ t ∈ Ioo (chartAL WU qT) b, ∃ M : ℝ, ∀ᶠ z in 𝓝[H] (t : ℂ),
      ‖(curChartInf A R L r η ψ n q ω).1 ((curChart A' R' L r' η ψ' n' qT.toNNReal ω).2.1 z)‖ ≤ M := by
    intro t _
    have hpC := hEI₀C t (real_mem_Hbar t)
    obtain ⟨δ, hδ, hδψ⟩ := Metric.continuousWithinAt_iff.1 (hJ.1 _ hpC) 1 one_pos
    refine ⟨‖ψ ω (EI₀ t)‖ + 1 + C₀, ?_⟩
    have hev : ∀ᶠ z in 𝓝[Hbar] (t : ℂ), EI₀ z ∈ ball (EI₀ t) δ :=
      (hI₀Ec _ (real_mem_Hbar t)).tendsto.eventually (ball_mem_nhds _ hδ)
    filter_upwards [nhdsWithin_mono _ QuantumZipper.H_subset_Hbar hev, self_mem_nhdsWithin] with z hzb hzH
    have hwI := hI₀c.inv_mem_dom hzH
    have hwO := hI₀O hwI
    have hwO' := hwO
    rw [hOdom] at hwO'
    rw [hOfwd _ hwO'.1]
    have hwz : (curChart A' R' L r' η ψ' n' qT.toNNReal ω).2.1 z = EI₀ z := (hI₀E hzH).symm
    have h1 := norm_fwdMap_le hWC hWC0 q.coe_nonneg hC₀ hwO'.2
    have hwx : (curChart A' R' L r' η ψ' n' qT.toNNReal ω).2.1 z ∈
        closure (cfPocket (R ω) (L ω) r) := subset_closure hwO'.1
    have h2 := hδψ hwx (by rw [hwz]; exact hzb)
    rw [dist_eq_norm] at h2
    have h3 : ‖ψ ω ((curChart A' R' L r' η ψ' n' qT.toNNReal ω).2.1 z)‖ ≤ ‖ψ ω (EI₀ t)‖ + 1 := by
      have := norm_le_norm_add_norm_sub' (ψ ω ((curChart A' R' L r' η ψ' n' qT.toNNReal ω).2.1 z)) (ψ ω (EI₀ t))
      linarith
    linarith
  -- the driver identification
  have hdrv := hdrv_of_later (O := curChartInf A R L r η ψ n q ω) (I₀ := curChart A' R' L r' η ψ' n' qT.toNNReal ω)
    hWC hWC0 hWU hWU0 q.coe_nonneg hqT0 hOfwd hOdom hI₀fwd hI₀dom hsub hI₀O (hψc' ω hω')
    (hlater_outerInf (n := n) (n' := n') hcfg hψ hcfg' hψ' hω hω' hq hsub hT0 htip hqt₁' ht₁ hqTt'
      (fun q₂ hq₂ => (hCf q₂ hq₂).2.1) (fun q₂ hq₂ => (hUf q₂ hq₂).2.1))
  -- the test point on the old hull inside `U`
  have hEI₀d : DifferentiableOn ℂ EI₀ H := hI₀c.1.congr fun z hz => hI₀E hz
  have hEI₀i : InjOn EI₀ H := hI₀c.injOn.congr hI₀E.symm
  have hEI₀0' : EI₀ 0 = tip := by simpa using hEI₀0
  obtain ⟨tξ, htξ, htξU, htξne⟩ := R6Land.exists_exposed_landing hEI₀d hI₀Ec hEI₀i (hCo' ω hω')
    (by rw [hEI₀0']; exact htip) le_rfl hwR0.le hwR0
  rw [hEI₀0'] at htξne
  have hpytip : EI₀ ty ≠ tip := fun h => hnotA ty (by linarith) (h ▸ hTC)
  set d₀ := min (dist (EI₀ tξ) tip) (dist (EI₀ ty) tip) with hd₀
  have hd₀pos : 0 < d₀ := lt_min (dist_pos.2 htξne) (dist_pos.2 hpytip)
  obtain ⟨ρ₁, hρ₁, hρ₁E⟩ := Metric.continuousWithinAt_iff.1 (hI₀Ec _ (real_mem_Hbar 0)) (d₀ / 2) (half_pos hd₀pos)
  set ρ := min (tξ / 4) (ρ₁ / 2) with hρdef
  have hρ0 : 0 < ρ := lt_min (by linarith [htξ.1]) (half_pos hρ₁)
  have h2ρ : 2 * ρ < tξ := by linarith [min_le_left (tξ / 4) (ρ₁ / 2), htξ.1]
  have hρnear : ∀ z ∈ Hbar, ‖z‖ ≤ ρ → dist (EI₀ z) tip < d₀ / 2 := fun z hz hzn => by
    have h := hρ₁E hz (by
      rw [Complex.ofReal_zero, dist_zero_right]; linarith [min_le_right (tξ / 4) (ρ₁ / 2)])
    rwa [hEI₀0] at h
  -- the window of later inner times
  obtain ⟨θ₁, hθ₁, hθ₁K⟩ := exists_shift_hull_small hWU qT (show (0 : ℝ) < 2 * ρ by linarith)
  obtain ⟨θW, hθW, hθWc⟩ := Metric.continuousAt_iff.1 (hWU.continuousAt (x := qT)) (ρ / 96) (by positivity)
  have hARc : ContinuousAt (fun t => chartAR WU t) qT := by
    have h1 := (MartChar.RealFlow.continuousOn_rightImg hWU 0).continuousAt (Ici_mem_nhds hqTpos)
    exact h1.sub hWU.continuousAt
  have hALc : ContinuousAt (fun t => chartAL WU t) qT := by
    have h1 := (MartChar.RealFlow.continuousOn_rightImg hWU.neg 0).continuousAt (Ici_mem_nhds hqTpos)
    exact h1.neg.sub hWU.continuousAt
  obtain ⟨θa, hθa, hθaR⟩ := Metric.continuousAt_iff.1 hARc (chartAR WU qT) hwR0
  obtain ⟨θb, hθb, hθbL⟩ := Metric.continuousAt_iff.1 hALc (-chartAL WU qT) (by linarith)
  set εW := min (min θ₁ θW) (min ((ρ / 32) ^ 2) (min (min θa θb) (t₁' - qT))) with hεWdef
  have hεW : 0 < εW := lt_min (lt_min hθ₁ hθW) (lt_min (by positivity) (lt_min (lt_min hθa hθb) (by linarith)))
  refine ⟨εW, hεW, fun q' hq'lo hq'hi hIncl ρL ρR σL σR vL vR wL wR hvL' hvR' hwL' hwR' hρσ => ?_⟩
  have hq'lo' : qT < q' := hq'lo
  have hq'hi' : (q' : ℝ) < qT + εW := hq'hi
  have hm1 : εW ≤ θ₁ := (min_le_left _ _).trans (min_le_left _ _)
  have hm2 : εW ≤ θW := (min_le_left _ _).trans (min_le_right _ _)
  have hm3 : εW ≤ (ρ / 32) ^ 2 := (min_le_right _ _).trans (min_le_left _ _)
  have hm4 : εW ≤ min θa θb := (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
  have hm5 : εW ≤ t₁' - qT := (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _))
  have hq't : q' < t₁' := by
    have : (q' : ℝ) < t₁' := by linarith
    exact_mod_cast this
  have hq'pos : (0 : ℝ) < q' := hqTpos.trans hq'lo'
  obtain ⟨hIc, hIdom, hIfwd, hIE, hIEc⟩ := hUf q' hq't
  have hWUq : ∀ s ∈ Icc (0 : ℝ) q', segDriver (travAll R' L r' η ψ' ω) s.toNNReal = WU s := fun s hs =>
    hWUeq s ⟨hs.1, hs.2.trans (by exact_mod_cast hq't.le)⟩
  have hwRe : seedR R' L r' η ψ' q' ω = chartAR WU q' := seedR_eq hWU hWUq
  have hwLe : seedL R' L r' η ψ' q' ω = chartAL WU q' := seedL_eq hWU hWUq
  have hdq : dist (q' : ℝ) qT < min θa θb := by
    rw [Real.dist_eq, abs_of_pos (by linarith)]; linarith
  have hwR0' : 0 < chartAR WU q' := by
    have h := hθaR (hdq.trans_le (min_le_left _ _))
    rw [Real.dist_eq, abs_sub_lt_iff] at h
    linarith [h.2]
  have hwL0' : chartAL WU q' < 0 := by
    have h := hθbL (hdq.trans_le (min_le_right _ _))
    rw [Real.dist_eq, abs_sub_lt_iff] at h
    linarith [h.1]
  have hwLR' : chartAL WU q' < chartAR WU q' := hwL0'.trans hwR0'
  obtain ⟨hF'c, hF'eq, hF'm⟩ := extendFrom_props hηU hWU hWU0 q'.coe_nonneg
  set δ := (q' : ℝ) - qT with hδdef
  have hδ0 : 0 ≤ δ := by linarith
  have hsmall : fwdHull (QuantumZipper.RS.shiftDrive WU qT) δ ⊆ closedBall 0 ρ := by
    have h := hθ₁K δ hδ0 (by linarith)
    rwa [show 2 * ρ / 2 = ρ by ring] at h
  -- the increment: away from `0` in the same-time chart, points stay in the later domain
  have hinc : ∀ z ∈ H, ρ < ‖z‖ →
      (curChart A' R' L r' η ψ' n' qT.toNNReal ω).2.1 z ∈ ((curChart A' R' L r' η ψ' n' q' ω).dom : Set ℂ) := by
    intro z hz hzn
    rw [← hI₀E hz]
    show E₀' (extendFrom H (fwdMapInv WU qT) z) ∈ _
    rw [hFTeq hz]
    have hk := QuantumZipper.RS.fwdMapInv_mem_compl_fwdHull hWU hWU0 hqT0 hz
    obtain ⟨heU, hek⟩ := hinvU _ hk.1
    rw [hIdom]
    refine ⟨heU, ?_⟩
    show ψ' ω (E₀' (fwdMapInv WU qT z)) ∈ H \ fwdHull WU q'
    rw [hek]
    refine ⟨hk.1, fun hkq => ?_⟩
    have hdiff : fwdMapInv WU qT z ∈ fwdHull WU (qT + δ) \ fwdHull WU qT := by
      rw [hδdef, add_sub_cancel]; exact ⟨hkq, hk.2⟩
    rw [Sec5.fwdHull_add_sdiff_eq_image hWU hWU0 hqT0 hδ0] at hdiff
    obtain ⟨a, ha, hae⟩ := hdiff
    have haH : a ∈ H := QuantumZipper.fwdHull_mono.2 _ ha
    have haz : a = z := QuantumZipper.RS.injOn_fwdMapInv hWU hWU0 hqT0 haH hz hae
    have := hsmall ha
    rw [mem_closedBall, dist_zero_right, haz] at this
    linarith
  have hinc0 : ∀ᶠ w in 𝓝[H] (0 : ℂ),
      ‖(curChart A' R' L r' η ψ' n' qT.toNNReal ω).1 ((curChart A' R' L r' η ψ' n' q' ω).2.1 w)‖ ≤ ρ := by
    filter_upwards [self_mem_nhdsWithin, nhdsWithin_le_nhds (ball_mem_nhds (0 : ℂ) (half_pos hρ0))] with w hwH hwb
    rw [← hIE hwH]
    show ‖(curChart A' R' L r' η ψ' n' qT.toNNReal ω).1 (E₀' (extendFrom H (fwdMapInv WU q') w))‖ ≤ ρ
    rw [hF'eq hwH]
    have hvH := QuantumZipper.RS.fwdMapInv_mem_H hWU hWU0 q'.coe_nonneg hwH
    obtain ⟨hvU, hvk⟩ := hinvU _ hvH
    rw [hI₀fwd _ hvU, hvk]
    have hq'eq : (q' : ℝ) = qT + δ := by rw [hδdef]; ring
    rw [hq'eq, QuantumZipper.RS.fwdMapInv_add_shift hWU hWU0 hqT0 hδ0 hwH]
    have hsH := QuantumZipper.RS.fwdMapInv_mem_H (QuantumZipper.RS.continuous_shiftDrive hWU qT)
      (QuantumZipper.RS.shiftDrive_zero WU qT) hδ0 hwH
    rw [QuantumZipper.RS.fwdMap_fwdMapInv hWU hWU0 hqT0 hsH]
    have hM : ∀ s ∈ Icc (0 : ℝ) δ, |QuantumZipper.RS.shiftDrive WU qT s| ≤ ρ / 96 := by
      intro s hs
      have h := hθWc (show dist (qT + s) qT < θW by
        rw [Real.dist_eq, add_sub_cancel_left, abs_of_nonneg hs.1]; linarith [hs.2])
      rw [Real.dist_eq] at h
      exact h.le
    have h1 := InteractingSLE.norm_fwdMapInv_sub_le (QuantumZipper.RS.continuous_shiftDrive hWU qT)
      (QuantumZipper.RS.shiftDrive_zero WU qT) hδ0 hM hwH
    have hsq : Real.sqrt δ < ρ / 32 := by
      rw [Real.sqrt_lt' (by positivity)]; linarith
    have hwn : ‖w‖ < ρ / 2 := by simpa [mem_ball, dist_zero_right] using hwb
    have h2 : ‖fwdMapInv (QuantumZipper.RS.shiftDrive WU qT) δ w‖ ≤
        ‖w‖ + ‖fwdMapInv (QuantumZipper.RS.shiftDrive WU qT) δ w - w‖ := by
      calc _ = ‖w + (fwdMapInv (QuantumZipper.RS.shiftDrive WU qT) δ w - w)‖ := by ring_nf
        _ ≤ _ := norm_add_le _ _
    linarith
  -- the two test landings
  have htξab : tξ ∈ Ioo (chartAL WU qT) b := ⟨by linarith [htξ.1], by linarith [htξ.2]⟩
  have hpξC : EI₀ tξ ∈ cfPocket (R ω) (L ω) r := hsub htξU
  have hpξO := hnot tξ htξab
  have hψpξ : ψ ω (EI₀ tξ) ∈ fwdHull WC q := by
    by_contra hn
    exact hpξO (by rw [hOdom]; exact ⟨hpξC, (hψc ω hω).2.mapsTo hpξC, hn⟩)
  have hψ'pξ : ψ' ω (EI₀ tξ) ∈ fwdHull WU q' := by
    have hn : EI₀ tξ ∉ ((curChart A' R' L r' η ψ' n' qT.toNNReal ω).dom : Set ℂ) := fun h => hpξO (hI₀O h)
    rw [hI₀dom] at hn
    have hH := (hψc' ω hω').2.mapsTo htξU
    have : ψ' ω (EI₀ tξ) ∈ fwdHull WU qT := by
      by_contra hk; exact hn ⟨htξU, hH, hk⟩
    exact QuantumZipper.fwdHull_mono.1 hq'lo'.le this
  obtain ⟨θy, hθy, hpyθ⟩ := harcR ty (by linarith)
  obtain ⟨hNC1, hNC2, hNC3⟩ := R6Fd.nonCorner_of_left_open hcf.conf hcf'.conf h0U hθy
  rw [← hpyθ] at hNC1 hNC2 hNC3
  have hpyU : EI₀ ty ∈ closure (cfPocket (R' ω) (L ω) r') := frontier_subset_closure hNC1
  obtain ⟨εy, hεy, hεyU⟩ := inter_ball_subset_of_noncornerInf hJ (hCo' ω hω') hsub hpyU
    (closure_mono hsub hpyU) hNC2
  have hψ'py : ψ' ω (EI₀ ty) = extendFrom H (fwdMapInv WU qT) (ty : ℂ) :=
    jordan_comp_ext hJ' hE₀' hE₀'c hE₀'m (hFTm (real_mem_Hbar ty))
  have hpyAlive : ψ' ω (EI₀ ty) ∉ closure (fwdHull WU qT) := by
    rw [hψ'py]; exact alive_of_not_mem_Icc hηU hWU hWU0 hqT0 (Or.inr (by linarith))
  have hIncl₀ : cfPocket (R' ω) (L ω) r' ∩ ψ' ω ⁻¹' (H \ fwdHull WU qT) ⊆
      cfPocket (R ω) (L ω) r ∩ ψ ω ⁻¹' (H \ fwdHull WC q) := by
    rw [← hI₀dom, ← hOdom]; exact hI₀O
  have hOU : ∀ w ∈ ((curChartInf A R L r η ψ n q ω).dom : Set ℂ), w ∈ cfPocket (R' ω) (L ω) r' →
      w ∈ ((curChart A' R' L r' η ψ' n' qT.toNNReal ω).dom : Set ℂ) := fun w hwO hwU => by
    show w ∈ ((relChart (fun ω => shiftChart (pChart A' (fun ω => cfPocket (R' ω) (L ω) r') ψ' ω) (n' ω))
      (travAll R' L r' η ψ') qT.toNNReal ω).dom : Set ℂ)
    rw [hqTdom]; exact ⟨hwU, hOphys hwO⟩
  have hpyCalive : ψ ω (EI₀ ty) ∉ closure (fwdHull WC q) := by
    obtain ⟨ρy, hρy, hρysub⟩ := exists_ball_subset_of_alive hJ' hx₀' (hE₀'m (hFTm (real_mem_Hbar ty))) hpyAlive
    refine notMem_closure_of_ball_subsetInf hJ (QuantumZipper.fwdHull_mono.2 _) (hEI₀C ty (real_mem_Hbar ty))
      (lt_min hρy hεy) fun z hz => ?_
    have hzU : z ∈ cfPocket (R' ω) (L ω) r' := hεyU ⟨hz.1, ball_subset_ball (min_le_right _ _) hz.2⟩
    exact hIncl₀ (hρysub ⟨hzU, ball_subset_ball (min_le_left _ _) hz.2⟩)
  -- dead and alive in the outer chart
  have hdeadO : ∀ x : ℝ, EO x = EI₀ tξ → vL 0 ≤ x ∧ x < vR 0 := by
    intro x hx
    rw [hvL', hvL, hvR', hvR]
    have hψx : ψ ω (EO x) = extendFrom H (fwdMapInv WC q) (x : ℂ) :=
      jordan_comp_extInf hJ hE₀ hE₀c hE₀m (hFm (real_mem_Hbar x))
    rw [hx] at hψx
    refine ⟨not_lt.1 fun hlt => ?_, lt_of_not_ge fun hge => ?_⟩
    · exact alive_of_not_mem_Icc hηC hWC hWC0 q.coe_nonneg (Or.inl hlt) (hψx ▸ subset_closure hψpξ)
    · rcases hge.lt_or_eq with hgt | heq
      · exact alive_of_not_mem_Icc hηC hWC hWC0 q.coe_nonneg (Or.inr hgt) (hψx ▸ subset_closure hψpξ)
      · have him := R6Fd.landR_im_eq_zero hηC hWC hWC0 q.coe_nonneg
        rw [heq, ← hψx] at him
        have hH : (0 : ℝ) < (ψ ω (EI₀ tξ)).im := (hψc ω hω).2.mapsTo hpξC
        linarith
  have haliveO : ∀ x : ℝ, EO x = EI₀ ty → x < vL 0 ∨ vR 0 < x := by
    intro x hx
    rw [hvL', hvL, hvR', hvR]
    by_contra hxI
    push Not at hxI
    have hψx : ψ ω (EO x) = extendFrom H (fwdMapInv WC q) (x : ℂ) :=
      jordan_comp_extInf hJ hE₀ hE₀c hE₀m (hFm (real_mem_Hbar x))
    rw [hx] at hψx
    exact hpyCalive (hψx ▸ dead_of_mem_Icc hηC hWC hWC0 hq0' (hvL0.trans hvR0) hxI)
  -- dead and alive in the later inner chart
  have hdeadI : ∀ x : ℝ, E₀' (extendFrom H (fwdMapInv WU q') (x : ℂ)) = EI₀ tξ → wL 0 < x ∧ x < wR 0 := by
    intro x hx
    rw [hwL', hwLe, hwR', hwRe]
    have hψx : ψ' ω (E₀' (extendFrom H (fwdMapInv WU q') (x : ℂ))) = extendFrom H (fwdMapInv WU q') (x : ℂ) :=
      jordan_comp_ext hJ' hE₀' hE₀'c hE₀'m (hF'm (real_mem_Hbar x))
    rw [hx] at hψx
    have hH : (0 : ℝ) < (ψ' ω (EI₀ tξ)).im := (hψc' ω hω').2.mapsTo htξU
    refine ⟨lt_of_not_ge fun hle => ?_, lt_of_not_ge fun hge => ?_⟩
    · rcases hle.lt_or_eq with hlt | heq
      · exact alive_of_not_mem_Icc hηU hWU hWU0 q'.coe_nonneg (Or.inl hlt) (hψx ▸ subset_closure hψ'pξ)
      · have him := R6Fd.landL_im_eq_zero hηU hWU hWU0 q'.coe_nonneg
        rw [← heq, ← hψx] at him
        linarith
    · rcases hge.lt_or_eq with hgt | heq
      · exact alive_of_not_mem_Icc hηU hWU hWU0 q'.coe_nonneg (Or.inr hgt) (hψx ▸ subset_closure hψ'pξ)
      · have him := R6Fd.landR_im_eq_zero hηU hWU hWU0 q'.coe_nonneg
        rw [heq, ← hψx] at him
        linarith
  -- the later hull near the old one: `K_{q'} ⊆ K_{q_T} ∪ F̄_{q_T}(ℍ̄ ∩ B̄(0, ρ))`
  set S := (fun z => extendFrom H (fwdMapInv WU qT) z) '' (Hbar ∩ closedBall 0 ρ) with hSdef
  have hSc : IsClosed S := by
    have hK : IsCompact (Hbar ∩ closedBall (0 : ℂ) ρ) := by
      refine (isCompact_closedBall 0 ρ).inter_left ?_
      rw [← QuantumZipper.CA.Car.closure_H_eq_Hbar]; exact isClosed_closure
    exact (hK.image_of_continuousOn (hFTc.mono inter_subset_left)).isClosed
  have hKsub : fwdHull WU q' ⊆ fwdHull WU qT ∪ S := by
    intro k hk
    by_cases hkT : k ∈ fwdHull WU qT
    · exact Or.inl hkT
    · right
      have hdiff : k ∈ fwdHull WU (qT + δ) \ fwdHull WU qT := by
        rw [hδdef, add_sub_cancel]; exact ⟨hk, hkT⟩
      rw [Sec5.fwdHull_add_sdiff_eq_image hWU hWU0 hqT0 hδ0] at hdiff
      obtain ⟨a, ha, rfl⟩ := hdiff
      have haH : a ∈ H := QuantumZipper.fwdHull_mono.2 _ ha
      exact ⟨a, ⟨QuantumZipper.H_subset_Hbar haH, hsmall ha⟩, hFTeq haH⟩
  have hfar : ∀ p ∈ closure (cfPocket (R' ω) (L ω) r') \ {cfPt (openPt (R' ω) (L ω) r')}, d₀ ≤ dist p tip →
      ψ' ω p ∉ S := by
    rintro p hp hpd ⟨z, hz, hze⟩
    have hpe : EI₀ z = p := by
      show E₀' (extendFrom H (fwdMapInv WU qT) z) = p
      have hze' : extendFrom H (fwdMapInv WU qT) z = ψ' ω p := hze
      rw [hze']; exact R6Fd.extension_psi_eq hJ' hx₀' hE₀' hE₀'c hp
    have := hρnear z hz.1 (by simpa [mem_closedBall, dist_zero_right] using hz.2)
    rw [hpe] at this
    linarith
  have haliveI : ∀ x : ℝ, E₀' (extendFrom H (fwdMapInv WU q') (x : ℂ)) = EI₀ ty → x < wL 0 ∨ wR 0 < x := by
    intro x hx
    rw [hwL', hwLe, hwR', hwRe]
    by_contra hxI
    push Not at hxI
    have hψx : ψ' ω (E₀' (extendFrom H (fwdMapInv WU q') (x : ℂ))) = extendFrom H (fwdMapInv WU q') (x : ℂ) :=
      jordan_comp_ext hJ' hE₀' hE₀'c hE₀'m (hF'm (real_mem_Hbar x))
    rw [hx] at hψx
    have hd := dead_of_mem_Icc hηU hWU hWU0 hq'pos hwLR' hxI
    rw [← hψx] at hd
    have hcl : closure (fwdHull WU q') ⊆ closure (fwdHull WU qT) ∪ S :=
      (closure_mono hKsub).trans (by rw [closure_union, hSc.closure_eq])
    rcases hcl hd with h | h
    · exact hpyAlive h
    · exact hfar _ (hE₀'m (hFTm (real_mem_Hbar ty))) (min_le_right _ _) h
  -- local agreement at the two test landings
  have hloc : ∀ p : ℂ, d₀ ≤ dist p tip → ∀ ε₁ > 0,
      ((curChartInf A R L r η ψ n q ω).dom : Set ℂ) ∩ ball p ε₁ ⊆ cfPocket (R' ω) (L ω) r' →
      ∃ ε > 0, ((curChartInf A R L r η ψ n q ω).dom : Set ℂ) ∩ ball p ε ⊆
        ((curChart A' R' L r' η ψ' n' q' ω).dom : Set ℂ) := by
    intro p hpd ε₁ hε₁ hsubU
    refine ⟨min ε₁ (d₀ / 2), lt_min hε₁ (half_pos hd₀pos), fun w hw => ?_⟩
    have hwU := hsubU ⟨hw.1, ball_subset_ball (min_le_left _ _) hw.2⟩
    have hwI := hOU w hw.1 hwU
    have hz := hI₀c.fwd_mem hwI
    have hwe : (curChart A' R' L r' η ψ' n' qT.toNNReal ω).2.1 ((curChart A' R' L r' η ψ' n' qT.toNNReal ω).1 w) = w :=
      hI₀c.inv_fwd hwI
    rw [← hwe]
    refine hinc _ hz (lt_of_not_ge fun hle => ?_)
    have h1 := hρnear _ (QuantumZipper.H_subset_Hbar hz) hle
    rw [hI₀E hz, hwe] at h1
    have h2 : dist w p < d₀ / 2 := (mem_ball.1 hw.2).trans_le (min_le_right _ _)
    have h3 := dist_triangle p w tip
    rw [dist_comm p w] at h3
    linarith
  have hlocξ : ∃ ε > 0, ((curChartInf A R L r η ψ n q ω).dom : Set ℂ) ∩ ball (EI₀ tξ) ε ⊆
      ((curChart A' R' L r' η ψ' n' q' ω).dom : Set ℂ) := by
    obtain ⟨ε₁, hε₁, hε₁U⟩ := Metric.isOpen_iff.1 (hCo' ω hω') _ htξU
    exact hloc _ (min_le_left _ _) ε₁ hε₁ fun w hw => hε₁U hw.2
  have hlocy := hloc _ (min_le_right _ _) εy hεy fun w hw => by
    rw [hOdom] at hw
    exact hεyU ⟨hw.1.1, hw.2⟩
  -- the bound of the later inner coordinate near the inner landings
  obtain ⟨C₀', hC₀'⟩ := exists_norm_fwdMapInv_sub_le hWU hWU0 q'.coe_nonneg
  have hbddI : ∀ t ∈ Ioo (chartAL WU qT) b, ∃ ε > 0, ∃ M : ℝ,
      ∀ w ∈ ((curChart A' R' L r' η ψ' n' q' ω).dom : Set ℂ) ∩ ball (EI₀ t) ε,
        ‖(curChart A' R' L r' η ψ' n' q' ω).1 w‖ ≤ M := by
    intro t _
    have hpU := hE₀'m (hFTm (real_mem_Hbar t))
    obtain ⟨ε, hε, hεψ⟩ := Metric.continuousWithinAt_iff.1 (hJ'.1 _ hpU) 1 one_pos
    refine ⟨ε, hε, ‖ψ' ω (EI₀ t)‖ + 1 + C₀', fun w hw => ?_⟩
    have hwI := hw.1
    rw [hIdom] at hwI
    rw [hIfwd _ hwI.1]
    have h1 := norm_fwdMap_le hWU hWU0 q'.coe_nonneg hC₀' hwI.2
    have hwx : w ∈ closure (cfPocket (R' ω) (L ω) r') \ {cfPt (openPt (R' ω) (L ω) r')} :=
      ⟨subset_closure hwI.1, fun h => hx₀' (h ▸ hwI.1)⟩
    have h2 := hεψ hwx (mem_ball.1 hw.2)
    rw [dist_eq_norm] at h2
    have h3 := norm_le_norm_add_norm_sub' (ψ' ω w) (ψ' ω (EI₀ t))
    linarith
  exact r6FaceR_right_of_reflection hOc hI₀c hIc hI₀O hIncl hOE hOEc hI₀E hI₀Ec hIE hIEc hwL0 hnot hbdd hdrv hρ0
    hinc hinc0 h2ρ (by linarith [htξ.2]) (by linarith) hdeadO haliveO hdeadI haliveI (by rw [hwR', hwRe]; exact hwR0')
    hρσ hlocξ hlocy hbddI



/-- **R.6's face for the shape `MixedInf`, shared wall `R`** (mirror of `corner_face_sharedLInf`). -/
theorem corner_face_sharedRInf {A A' : Set Ω} {R L L' : Ω → ℝ≥0 → ℂ} {r r' : ℝ≥0} {W : Ω → ℝ → ℝ}
    {η : Ω → ℝ → ℂ} {ψ ψ' : Ω → ℂ → ℂ} {n n' : Ω → ℤ} {ω : Ω}
    (hcfg : ∀ ω ∈ A, IsOuterCfgInf (R ω) (L ω) r (W ω) (η ω)) (hψ : ∀ ω ∈ A, IsCfJordanInf (R ω) (L ω) r (ψ ω))
    (hcfg' : ∀ ω ∈ A', IsCfPocketConfig (R ω) (L' ω) r' (W ω) (η ω))
    (hψ' : ∀ ω ∈ A', IsCfJordan (R ω) (L' ω) r' (ψ' ω)) (hω : ω ∈ A) (hω' : ω ∈ A')
    {q : ℝ≥0} (hq0 : 0 < q) (hq : (q : ℝ≥0∞) < capLife (travAllInf R L r η ψ ω))
    (hsub : cfPocket (R ω) (L' ω) r' ⊆ cfPocket (R ω) (L ω) r)
    (hT0 : 0 ≤ outerFibreEndInf R L r η ψ q ω)
    (htip : η ω (outerFibreEndInf R L r η ψ q ω) ∈ cfPocket (R ω) (L' ω) r') :
    ∃ εW > 0, ∀ q' : ℝ≥0, innerRelCap R L' r' η ψ' (outerFibreEndInf R L r η ψ q ω) ω < q' →
      (q' : ℝ) < innerRelCap R L' r' η ψ' (outerFibreEndInf R L r η ψ q ω) ω + εW →
      ((curChart A' R L' r' η ψ' n' q' ω).dom : Set ℂ) ⊆ (curChartInf A R L r η ψ n q ω).dom →
      ∀ ρL ρR σL σR vL vR wL wR : Fin 1 → ℝ, vL 0 = seedLInf R L r η ψ q ω → vR 0 = seedRInf R L r η ψ q ω →
        wL 0 = seedL R L' r' η ψ' q' ω → wR 0 = seedR R L' r' η ψ' q' ω → ρL 0 = σL 0 →
        R6FaceR ρL ρR σL σR vL vR wL wR (curChartInf A R L r η ψ n q ω) (curChart A' R L' r' η ψ' n' q' ω)
          (H \ ((curChartInf A R L r η ψ n q ω).dom : Set ℂ)) (H \ ((curChart A' R L' r' η ψ' n' q' ω).dom : Set ℂ))
              := by
  classical
  -- the outer pocket
  have hcf := hcfg ω hω
  have hG : ∀ ω ∈ A, IsChangeConfigInc (R ω) (L ω) r := fun ω hω => (hcfg ω hω).conf
  have hCo : ∀ ω ∈ A, IsOpen (cfPocket (R ω) (L ω) r) := fun ω hω =>
    isOpen_image_negInv' (hG ω hω).isOpen_changePocket (hG ω hω).changePocket_subset_H
  have hCH : ∀ ω ∈ A, cfPocket (R ω) (L ω) r ⊆ H := fun ω hω =>
    PocketJordan.image_negInv_subset_H (hG ω hω).changePocket_subset_H
  have hψc : ∀ ω ∈ A, IsConformalBijection (ψ ω) (cfPocket (R ω) (L ω) r) H := fun ω hω => (hψ ω hω).2.2.2.1
  have hJ : Sec6.IsJordanCoordInf (cfPocket (R ω) (L ω) r) (cfPt (closePt (R ω) (L ω) r)) (ψ ω) := hψ ω hω
  have hγ : IsDrivenCurve (travAllInf R L r η ψ ω) := (hcf.props (hψ ω hω)).1
  obtain ⟨t₁, hqt₁, ht₁⟩ := ENNReal.lt_iff_exists_nnreal_btwn.1 hq
  have hqt₁' : q < t₁ := by exact_mod_cast hqt₁
  obtain ⟨E₀, hE₀, hE₀c, hE₀m, WC, hWC, hWC0, hWCeq, ηC, hηC, hηCeq, hCf⟩ :=
    chart_factsInf (n := n) hCo hCH hψc hJ hω hγ ht₁
  obtain ⟨hOc, hOdom, hOfwd, hOE, hOEc⟩ := hCf q hqt₁'
  have hq0' : (0 : ℝ) < q := by exact_mod_cast hq0
  have hWCq : ∀ s ∈ Icc (0 : ℝ) q, segDriver (travAllInf R L r η ψ ω) s.toNNReal = WC s := fun s hs =>
    hWCeq s ⟨hs.1, hs.2.trans (by exact_mod_cast hqt₁'.le)⟩
  have hvR : seedRInf R L r η ψ q ω = chartAR WC q := seedR_eq hWC hWCq
  have hvL : seedLInf R L r η ψ q ω = chartAL WC q := seedL_eq hWC hWCq
  obtain ⟨hFc, hFeq, hFm⟩ := extendFrom_props hηC hWC hWC0 q.coe_nonneg
  have hTC : η ω (outerFibreEndInf R L r η ψ q ω) ∈ cfPocket (R ω) (L ω) r := hsub htip
  have htrace : capTrace (travAllInf R L r η ψ ω) q = ψ ω (η ω (outerFibreEndInf R L r η ψ q ω)) := rfl
  have h0cl : ((0 : ℝ) : ℂ) ∈ closure H := by
    rw [QuantumZipper.CA.Car.closure_H_eq_Hbar]; exact real_mem_Hbar 0
  have htipC : extendFrom H (fwdMapInv WC q) ((0 : ℝ) : ℂ) ∈ H := by
    have h1 := hηC.tendsto_fwdMapInv_tip hWC hWC0 q.coe_nonneg
    rw [← Complex.ofReal_zero] at h1
    rw [extendFrom_eq h0cl h1, hηCeq q q.coe_nonneg (by exact_mod_cast hqt₁'.le)]
    change capTrace (travAllInf R L r η ψ ω) q ∈ H
    rw [htrace]
    exact (hψc ω hω).2.mapsTo hTC
  have hvR0 : 0 < chartAR WC q := chartAR_pos_of_tip hηC hWC hWC0 q.coe_nonneg htipC
  have hvL0 : chartAL WC q < 0 := chartAL_neg_of_tip hηC hWC hWC0 q.coe_nonneg htipC
  set EO : ℂ → ℂ := fun z => E₀ (extendFrom H (fwdMapInv WC q) z) with hEOdef
  have hOphys : ((curChartInf A R L r η ψ n q ω).dom : Set ℂ) ⊆ H \ fwdHull (W ω) (outerFibreEndInf R L r η ψ q ω) := by
    intro w hwO
    have hzD : w ∈ cfPocket (R ω) (L ω) r ∩
        ψ ω ⁻¹' (H \ fwdHull (fun s : ℝ => segDriver (travAllInf R L r η ψ ω) s.toNNReal) q) := by
      rw [← relChart_dom_eq_inter (n := n) hCo hCH hψc hω hγ hq]; exact hwO
    exact outer_dom_physInf hcfg hψ hω hq hzD
  -- the inner pocket
  have hcf' := hcfg' ω hω'
  have hG' : ∀ ω ∈ A', IsChangeConfigInc (R ω) (L' ω) r' := fun ω hω => (hcfg' ω hω).conf
  have hCo' : ∀ ω ∈ A', IsOpen (cfPocket (R ω) (L' ω) r') := fun ω hω =>
    isOpen_image_negInv' (hG' ω hω).isOpen_changePocket (hG' ω hω).changePocket_subset_H
  have hCH' : ∀ ω ∈ A', cfPocket (R ω) (L' ω) r' ⊆ H := fun ω hω =>
    PocketJordan.image_negInv_subset_H (hG' ω hω).changePocket_subset_H
  have hψc' : ∀ ω ∈ A', IsConformalBijection (ψ' ω) (cfPocket (R ω) (L' ω) r') H := fun ω hω =>
    (hψ' ω hω).2.2.2.1
  have h0U := PocketMarks.zero_notMem_closure_of_rightLo_pos hcf'.conf hcf'.bounded
  have hUb : Bornology.IsBounded (cfPocket (R ω) (L' ω) r') := isBounded_image_negInv h0U
  have hx₀' : cfPt (openPt (R ω) (L' ω) r') ∉ cfPocket (R ω) (L' ω) r' := hcf'.conf.cfPt_openPt_notMem
  have hJ' : Sec6.IsJordanCoord (cfPocket (R ω) (L' ω) r') (cfPt (openPt (R ω) (L' ω) r'))
      (cfPt (closePt (R ω) (L' ω) r')) (ψ' ω) := hψ' ω hω'
  have hγ' : IsDrivenCurve (travAll R L' r' η ψ' ω) := (hcf'.isDrivenCurve (hψ' ω hω')).1
  obtain ⟨hc', hdom', hfwd'⟩ := R5Phase.shiftChart_dom_facts hCo' hCH' hψc' n' ω hω'
  obtain ⟨hqTpos, hqTlive, hqTdom⟩ := R5Phase.visitCap_spec
    (c := fun ω => shiftChart (pChart A' (fun ω => cfPocket (R ω) (L' ω) r') ψ' ω) (n' ω)) hω' hcf' (hψ' ω hω')
    hc' hdom' hfwd' hT0 htip
  set qT := R5Phase.visitCap R L' r' η ψ' ω (outerFibreEndInf R L r η ψ q ω) with hqTdef
  have hqT0 : (0 : ℝ) ≤ qT := hqTpos.le
  have hqTc : ((qT.toNNReal : ℝ≥0) : ℝ) = qT := Real.coe_toNNReal _ hqT0
  obtain ⟨t₁', hqTt₁', ht₁'⟩ := ENNReal.lt_iff_exists_nnreal_btwn.1 hqTlive
  have hqTt : qT.toNNReal < t₁' := by exact_mod_cast hqTt₁'
  have hqTt' : qT < t₁' := by rw [← hqTc]; exact_mod_cast hqTt
  obtain ⟨E₀', hE₀', hE₀'c, hE₀'m, WU, hWU, hWU0, hWUeq, ηU, hηU, hηUeq, hUf⟩ :=
    chart_facts (n := n') hCo' hCH' hψc' hUb hx₀' hJ' hω' hγ' ht₁'
  obtain ⟨hI₀c, hI₀dom, hI₀fwd, hI₀E, hI₀Ec⟩ := hUf qT.toNNReal hqTt
  rw [hqTc] at hI₀dom hI₀fwd hI₀E hI₀Ec
  -- the inner tip at the visit time
  obtain ⟨hP', hJ'arc⟩ := R5Ref.pocket_of_cfg hcf' (hψ' ω hω')
  have hvisit : outerFibreEndInf R L r η ψ q ω ∈ visitSet (η ω) (cfPocket (R ω) (L' ω) r')
      (firstHit (η ω) (cfArcR (R ω) (L' ω) r' 1)) (firstHit (η ω) (cfArcR (R ω) (L' ω) r' 0)) :=
    ⟨hP'.mem_Ioo_of_mem hT0 htip, htip⟩
  have htrU : capTrace (travAll R L' r' η ψ' ω) qT.toNNReal = ψ' ω (η ω (outerFibreEndInf R L r η ψ q ω)) :=
    PocketStopSide.capTrace_relCap_of_visit hP' hcf'.attach hJ'arc hvisit
  have hψ'T : ψ' ω (η ω (outerFibreEndInf R L r η ψ q ω)) ∈ H := (hψc' ω hω').2.mapsTo htip
  have htipU : extendFrom H (fwdMapInv WU qT) ((0 : ℝ) : ℂ) = ψ' ω (η ω (outerFibreEndInf R L r η ψ q ω)) := by
    have h1 := hηU.tendsto_fwdMapInv_tip hWU hWU0 hqT0
    rw [← Complex.ofReal_zero] at h1
    rw [extendFrom_eq h0cl h1, hηUeq qT hqT0 hqTt'.le, ← htrU]
    simp only [capTrace, hqTc]
  have hwR0 : 0 < chartAR WU qT := chartAR_pos_of_tip hηU hWU hWU0 hqT0 (htipU ▸ hψ'T)
  have hwL0 : chartAL WU qT < 0 := chartAL_neg_of_tip hηU hWU hWU0 hqT0 (htipU ▸ hψ'T)
  have hwLR : chartAL WU qT < chartAR WU qT := hwL0.trans hwR0
  obtain ⟨hFTc, hFTeq, hFTm⟩ := extendFrom_props hηU hWU hWU0 hqT0
  set EI₀ : ℂ → ℂ := fun z => E₀' (extendFrom H (fwdMapInv WU qT) z) with hEI₀def
  set tip := η ω (outerFibreEndInf R L r η ψ q ω) with htipdef
  have hEI₀0 : EI₀ ((0 : ℝ) : ℂ) = tip := by
    simp only [hEI₀def, htipU]
    rw [hE₀' hψ'T]
    exact (hψc' ω hω').2.injOn.leftInvOn_invFunOn htip
  -- the same-time inclusion and the two descriptions of the inner domain
  have hI₀O := inner_dom_subset_outer_dom_at_visitInf (n := n) (n' := n') hcfg hψ hcfg' hψ' hω hω' hq hsub hT0 htip
  -- the inverse of the inner Jordan coordinate on `ℍ`
  have hinvU : ∀ k ∈ H, E₀' k ∈ cfPocket (R ω) (L' ω) r' ∧ ψ' ω (E₀' k) = k := fun k hk => by
    rw [hE₀' hk]
    have hex : ∃ a ∈ cfPocket (R ω) (L' ω) r', ψ' ω a = k := (hψc' ω hω').2.surjOn hk
    exact ⟨Function.invFunOn_mem hex, Function.invFunOn_eq hex⟩
  have hullImg : ∀ k ∈ fwdHull WU qT, E₀' k ∈ fwdHull (W ω) (outerFibreEndInf R L r η ψ q ω) := by
    intro k hk
    have hkH : k ∈ H := QuantumZipper.fwdHull_mono.2 _ hk
    obtain ⟨heU, hek⟩ := hinvU k hkH
    by_contra hn
    have hmem : E₀' k ∈ ((curChart A' R L' r' η ψ' n' qT.toNNReal ω).dom : Set ℂ) := by
      show E₀' k ∈ ((relChart (fun ω => shiftChart (pChart A' (fun ω => cfPocket (R ω) (L' ω) r') ψ' ω) (n' ω))
        (travAll R L' r' η ψ') qT.toNNReal ω).dom : Set ℂ)
      rw [hqTdom]; exact ⟨heU, hCH' ω hω' heU, hn⟩
    rw [hI₀dom] at hmem
    have := hmem.2
    rw [Set.mem_preimage, hek] at this
    exact this.2 hk
  have hnotD : ∀ t ∈ Icc (chartAL WU qT) (chartAR WU qT),
      EI₀ t ∉ ((curChartInf A R L r η ψ n q ω).dom : Set ℂ) := fun t ht =>
    notMem_of_mem_closure_of_subset (curChartInf A R L r η ψ n q ω).dom.isOpen hOphys
      (mem_closure_of_dead hE₀'c (QuantumZipper.fwdHull_mono.2 _) hullImg
        (dead_of_mem_Icc hηU hWU hWU0 hqTpos hwLR ht))
  have hb0 : (extendFrom H (fwdMapInv WU qT) (chartAL WU qT : ℂ)).re ≤ 0 :=
    R6Fd.re_landL_le hηU hWU hWU0 hqTpos (x := 0) (by
      simpa using ConformalImageFull.zero_mem_closure_fwdHull hWU hWU0 hqTpos)
  have harcR : ∀ t : ℝ, t < chartAL WU qT → ∃ θ ∈ Ioo (rightLo (R ω) (L' ω) r') (rightHi (R ω) (L' ω) r'),
      EI₀ t = R6Fd.wallPt (R ω) θ := by
    intro t ht
    obtain ⟨him, hgt⟩ := landL_re_gt hηU hWU hWU0 hqTpos hwLR ht
    have hpm := hE₀'m (hFTm (real_mem_Hbar t))
    have hψp : ψ' ω (EI₀ t) = extendFrom H (fwdMapInv WU qT) (t : ℂ) :=
      jordan_comp_ext hJ' hE₀' hE₀'c hE₀'m (hFTm (real_mem_Hbar t))
    have hpU : EI₀ t ∉ cfPocket (R ω) (L' ω) r' := fun h => by
      have := (hψc' ω hω').2.mapsTo h
      rw [hψp] at this
      have h2 : (0 : ℝ) < (extendFrom H (fwdMapInv WU qT) (t : ℂ)).im := this
      rw [him] at h2
      exact lt_irrefl _ h2
    have hpfr : EI₀ t ∈ frontier (cfPocket (R ω) (L' ω) r') :=
      ⟨hpm.1, by rw [(hCo' ω hω').interior_eq]; exact hpU⟩
    exact frontier_neg_right_arc hcf'.conf h0U hcf'.oriented (hψ' ω hω') hpfr hpm.2 (by rw [hψp]; linarith)
  have hθI : ∀ θ ∈ Ioo (rightLo (R ω) (L' ω) r') (rightHi (R ω) (L' ω) r'), θ ∈ Ioc (0 : ℝ) 1 := by
    obtain ⟨-, hv', -, -, -, -, -, -⟩ := hcf'.conf.changeCorner_props
    exact fun θ hθ => ⟨(hcf'.conf.rightLo_pos h0U).trans hθ.1, hθ.2.le.trans hv'.2⟩
  have hnotA : ∀ t : ℝ, t < chartAL WU qT → EI₀ t ∉ cfPocket (R ω) (L ω) r := by
    intro t ht
    obtain ⟨θ, hθ, he⟩ := harcR t ht
    rw [he]
    exact R6Fd.wallPt_notMem hcf.conf (Or.inl rfl) (hθI θ hθ)
  set a := chartAL WU qT - 2 with hadef
  set ty := chartAL WU qT - 1 with htydef
  have hnot : ∀ t ∈ Ioo a (chartAR WU qT), EI₀ t ∉ ((curChartInf A R L r η ψ n q ω).dom : Set ℂ) := by
    intro t ht
    rcases le_or_gt (chartAL WU qT) t with h | h
    · exact hnotD t ⟨h, ht.2.le⟩
    · exact fun hm => hnotA t h (hOc.dom_subset hm |> fun _ => by rw [hOdom] at hm; exact hm.1)
  have hEI₀C : ∀ z ∈ Hbar, EI₀ z ∈ closure (cfPocket (R ω) (L ω) r) :=
    fun z hz => closure_mono hsub (hE₀'m (hFTm hz)).1
  obtain ⟨C₀, hC₀⟩ := exists_norm_fwdMapInv_sub_le hWC hWC0 q.coe_nonneg
  have hbdd : ∀ t ∈ Ioo a (chartAR WU qT), ∃ M : ℝ, ∀ᶠ z in 𝓝[H] (t : ℂ),
      ‖(curChartInf A R L r η ψ n q ω).1 ((curChart A' R L' r' η ψ' n' qT.toNNReal ω).2.1 z)‖ ≤ M := by
    intro t _
    have hpC := hEI₀C t (real_mem_Hbar t)
    obtain ⟨δ, hδ, hδψ⟩ := Metric.continuousWithinAt_iff.1 (hJ.1 _ hpC) 1 one_pos
    refine ⟨‖ψ ω (EI₀ t)‖ + 1 + C₀, ?_⟩
    have hev : ∀ᶠ z in 𝓝[Hbar] (t : ℂ), EI₀ z ∈ ball (EI₀ t) δ :=
      (hI₀Ec _ (real_mem_Hbar t)).tendsto.eventually (ball_mem_nhds _ hδ)
    filter_upwards [nhdsWithin_mono _ QuantumZipper.H_subset_Hbar hev, self_mem_nhdsWithin] with z hzb hzH
    have hwI := hI₀c.inv_mem_dom hzH
    have hwO := hI₀O hwI
    have hwO' := hwO
    rw [hOdom] at hwO'
    rw [hOfwd _ hwO'.1]
    have hwz : (curChart A' R L' r' η ψ' n' qT.toNNReal ω).2.1 z = EI₀ z := (hI₀E hzH).symm
    have h1 := norm_fwdMap_le hWC hWC0 q.coe_nonneg hC₀ hwO'.2
    have hwx : (curChart A' R L' r' η ψ' n' qT.toNNReal ω).2.1 z ∈
        closure (cfPocket (R ω) (L ω) r) := subset_closure hwO'.1
    have h2 := hδψ hwx (by rw [hwz]; exact hzb)
    rw [dist_eq_norm] at h2
    have h3 : ‖ψ ω ((curChart A' R L' r' η ψ' n' qT.toNNReal ω).2.1 z)‖ ≤ ‖ψ ω (EI₀ t)‖ + 1 := by
      have := norm_le_norm_add_norm_sub' (ψ ω ((curChart A' R L' r' η ψ' n' qT.toNNReal ω).2.1 z)) (ψ ω (EI₀ t))
      linarith
    linarith
  -- the driver identification
  have hdrv := hdrv_of_later (O := curChartInf A R L r η ψ n q ω) (I₀ := curChart A' R L' r' η ψ' n' qT.toNNReal ω)
    hWC hWC0 hWU hWU0 q.coe_nonneg hqT0 hOfwd hOdom hI₀fwd hI₀dom hsub hI₀O (hψc' ω hω')
    (hlater_outerInf (n := n) (n' := n') hcfg hψ hcfg' hψ' hω hω' hq hsub hT0 htip hqt₁' ht₁ hqTt'
      (fun q₂ hq₂ => (hCf q₂ hq₂).2.1) (fun q₂ hq₂ => (hUf q₂ hq₂).2.1))
  -- the test point on the old hull inside `U`
  have hEI₀d : DifferentiableOn ℂ EI₀ H := hI₀c.1.congr fun z hz => hI₀E hz
  have hEI₀i : InjOn EI₀ H := hI₀c.injOn.congr hI₀E.symm
  have hEI₀0' : EI₀ 0 = tip := by simpa using hEI₀0
  obtain ⟨tξ, htξ, htξU, htξne⟩ := R6Land.exists_exposed_landing hEI₀d hI₀Ec hEI₀i (hCo' ω hω')
    (by rw [hEI₀0']; exact htip) hwL0.le le_rfl hwL0
  rw [hEI₀0'] at htξne
  have hpytip : EI₀ ty ≠ tip := fun h => hnotA ty (by linarith) (h ▸ hTC)
  set d₀ := min (dist (EI₀ tξ) tip) (dist (EI₀ ty) tip) with hd₀
  have hd₀pos : 0 < d₀ := lt_min (dist_pos.2 htξne) (dist_pos.2 hpytip)
  obtain ⟨ρ₁, hρ₁, hρ₁E⟩ := Metric.continuousWithinAt_iff.1 (hI₀Ec _ (real_mem_Hbar 0)) (d₀ / 2) (half_pos hd₀pos)
  set ρ := min (-tξ / 4) (ρ₁ / 2) with hρdef
  have hρ0 : 0 < ρ := lt_min (by linarith [htξ.2]) (half_pos hρ₁)
  have h2ρ : tξ < -(2 * ρ) := by linarith [min_le_left (-tξ / 4) (ρ₁ / 2), htξ.2]
  have hρnear : ∀ z ∈ Hbar, ‖z‖ ≤ ρ → dist (EI₀ z) tip < d₀ / 2 := fun z hz hzn => by
    have h := hρ₁E hz (by
      rw [Complex.ofReal_zero, dist_zero_right]; linarith [min_le_right (-tξ / 4) (ρ₁ / 2)])
    rwa [hEI₀0] at h
  -- the window of later inner times
  obtain ⟨θ₁, hθ₁, hθ₁K⟩ := exists_shift_hull_small hWU qT (show (0 : ℝ) < 2 * ρ by linarith)
  obtain ⟨θW, hθW, hθWc⟩ := Metric.continuousAt_iff.1 (hWU.continuousAt (x := qT)) (ρ / 96) (by positivity)
  have hARc : ContinuousAt (fun t => chartAR WU t) qT := by
    have h1 := (MartChar.RealFlow.continuousOn_rightImg hWU 0).continuousAt (Ici_mem_nhds hqTpos)
    exact h1.sub hWU.continuousAt
  have hALc : ContinuousAt (fun t => chartAL WU t) qT := by
    have h1 := (MartChar.RealFlow.continuousOn_rightImg hWU.neg 0).continuousAt (Ici_mem_nhds hqTpos)
    exact h1.neg.sub hWU.continuousAt
  obtain ⟨θa, hθa, hθaR⟩ := Metric.continuousAt_iff.1 hARc (chartAR WU qT) hwR0
  obtain ⟨θb, hθb, hθbL⟩ := Metric.continuousAt_iff.1 hALc (-chartAL WU qT) (by linarith)
  set εW := min (min θ₁ θW) (min ((ρ / 32) ^ 2) (min (min θa θb) (t₁' - qT))) with hεWdef
  have hεW : 0 < εW := lt_min (lt_min hθ₁ hθW) (lt_min (by positivity) (lt_min (lt_min hθa hθb) (by linarith)))
  refine ⟨εW, hεW, fun q' hq'lo hq'hi hIncl ρL ρR σL σR vL vR wL wR hvL' hvR' hwL' hwR' hρσ => ?_⟩
  have hq'lo' : qT < q' := hq'lo
  have hq'hi' : (q' : ℝ) < qT + εW := hq'hi
  have hm1 : εW ≤ θ₁ := (min_le_left _ _).trans (min_le_left _ _)
  have hm2 : εW ≤ θW := (min_le_left _ _).trans (min_le_right _ _)
  have hm3 : εW ≤ (ρ / 32) ^ 2 := (min_le_right _ _).trans (min_le_left _ _)
  have hm4 : εW ≤ min θa θb := (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
  have hm5 : εW ≤ t₁' - qT := (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _))
  have hq't : q' < t₁' := by
    have : (q' : ℝ) < t₁' := by linarith
    exact_mod_cast this
  have hq'pos : (0 : ℝ) < q' := hqTpos.trans hq'lo'
  obtain ⟨hIc, hIdom, hIfwd, hIE, hIEc⟩ := hUf q' hq't
  have hWUq : ∀ s ∈ Icc (0 : ℝ) q', segDriver (travAll R L' r' η ψ' ω) s.toNNReal = WU s := fun s hs =>
    hWUeq s ⟨hs.1, hs.2.trans (by exact_mod_cast hq't.le)⟩
  have hwRe : seedR R L' r' η ψ' q' ω = chartAR WU q' := seedR_eq hWU hWUq
  have hwLe : seedL R L' r' η ψ' q' ω = chartAL WU q' := seedL_eq hWU hWUq
  have hdq : dist (q' : ℝ) qT < min θa θb := by
    rw [Real.dist_eq, abs_of_pos (by linarith)]; linarith
  have hwR0' : 0 < chartAR WU q' := by
    have h := hθaR (hdq.trans_le (min_le_left _ _))
    rw [Real.dist_eq, abs_sub_lt_iff] at h
    linarith [h.2]
  have hwL0' : chartAL WU q' < 0 := by
    have h := hθbL (hdq.trans_le (min_le_right _ _))
    rw [Real.dist_eq, abs_sub_lt_iff] at h
    linarith [h.1]
  have hwLR' : chartAL WU q' < chartAR WU q' := hwL0'.trans hwR0'
  obtain ⟨hF'c, hF'eq, hF'm⟩ := extendFrom_props hηU hWU hWU0 q'.coe_nonneg
  set δ := (q' : ℝ) - qT with hδdef
  have hδ0 : 0 ≤ δ := by linarith
  have hsmall : fwdHull (QuantumZipper.RS.shiftDrive WU qT) δ ⊆ closedBall 0 ρ := by
    have h := hθ₁K δ hδ0 (by linarith)
    rwa [show 2 * ρ / 2 = ρ by ring] at h
  -- the increment: away from `0` in the same-time chart, points stay in the later domain
  have hinc : ∀ z ∈ H, ρ < ‖z‖ →
      (curChart A' R L' r' η ψ' n' qT.toNNReal ω).2.1 z ∈ ((curChart A' R L' r' η ψ' n' q' ω).dom : Set ℂ) := by
    intro z hz hzn
    rw [← hI₀E hz]
    show E₀' (extendFrom H (fwdMapInv WU qT) z) ∈ _
    rw [hFTeq hz]
    have hk := QuantumZipper.RS.fwdMapInv_mem_compl_fwdHull hWU hWU0 hqT0 hz
    obtain ⟨heU, hek⟩ := hinvU _ hk.1
    rw [hIdom]
    refine ⟨heU, ?_⟩
    show ψ' ω (E₀' (fwdMapInv WU qT z)) ∈ H \ fwdHull WU q'
    rw [hek]
    refine ⟨hk.1, fun hkq => ?_⟩
    have hdiff : fwdMapInv WU qT z ∈ fwdHull WU (qT + δ) \ fwdHull WU qT := by
      rw [hδdef, add_sub_cancel]; exact ⟨hkq, hk.2⟩
    rw [Sec5.fwdHull_add_sdiff_eq_image hWU hWU0 hqT0 hδ0] at hdiff
    obtain ⟨a, ha, hae⟩ := hdiff
    have haH : a ∈ H := QuantumZipper.fwdHull_mono.2 _ ha
    have haz : a = z := QuantumZipper.RS.injOn_fwdMapInv hWU hWU0 hqT0 haH hz hae
    have := hsmall ha
    rw [mem_closedBall, dist_zero_right, haz] at this
    linarith
  have hinc0 : ∀ᶠ w in 𝓝[H] (0 : ℂ),
      ‖(curChart A' R L' r' η ψ' n' qT.toNNReal ω).1 ((curChart A' R L' r' η ψ' n' q' ω).2.1 w)‖ ≤ ρ := by
    filter_upwards [self_mem_nhdsWithin, nhdsWithin_le_nhds (ball_mem_nhds (0 : ℂ) (half_pos hρ0))] with w hwH hwb
    rw [← hIE hwH]
    show ‖(curChart A' R L' r' η ψ' n' qT.toNNReal ω).1 (E₀' (extendFrom H (fwdMapInv WU q') w))‖ ≤ ρ
    rw [hF'eq hwH]
    have hvH := QuantumZipper.RS.fwdMapInv_mem_H hWU hWU0 q'.coe_nonneg hwH
    obtain ⟨hvU, hvk⟩ := hinvU _ hvH
    rw [hI₀fwd _ hvU, hvk]
    have hq'eq : (q' : ℝ) = qT + δ := by rw [hδdef]; ring
    rw [hq'eq, QuantumZipper.RS.fwdMapInv_add_shift hWU hWU0 hqT0 hδ0 hwH]
    have hsH := QuantumZipper.RS.fwdMapInv_mem_H (QuantumZipper.RS.continuous_shiftDrive hWU qT)
      (QuantumZipper.RS.shiftDrive_zero WU qT) hδ0 hwH
    rw [QuantumZipper.RS.fwdMap_fwdMapInv hWU hWU0 hqT0 hsH]
    have hM : ∀ s ∈ Icc (0 : ℝ) δ, |QuantumZipper.RS.shiftDrive WU qT s| ≤ ρ / 96 := by
      intro s hs
      have h := hθWc (show dist (qT + s) qT < θW by
        rw [Real.dist_eq, add_sub_cancel_left, abs_of_nonneg hs.1]; linarith [hs.2])
      rw [Real.dist_eq] at h
      exact h.le
    have h1 := InteractingSLE.norm_fwdMapInv_sub_le (QuantumZipper.RS.continuous_shiftDrive hWU qT)
      (QuantumZipper.RS.shiftDrive_zero WU qT) hδ0 hM hwH
    have hsq : Real.sqrt δ < ρ / 32 := by
      rw [Real.sqrt_lt' (by positivity)]; linarith
    have hwn : ‖w‖ < ρ / 2 := by simpa [mem_ball, dist_zero_right] using hwb
    have h2 : ‖fwdMapInv (QuantumZipper.RS.shiftDrive WU qT) δ w‖ ≤
        ‖w‖ + ‖fwdMapInv (QuantumZipper.RS.shiftDrive WU qT) δ w - w‖ := by
      calc _ = ‖w + (fwdMapInv (QuantumZipper.RS.shiftDrive WU qT) δ w - w)‖ := by ring_nf
        _ ≤ _ := norm_add_le _ _
    linarith
  -- the two test landings
  have htξab : tξ ∈ Ioo a (chartAR WU qT) := ⟨by linarith [htξ.1], by linarith [htξ.2]⟩
  have hpξC : EI₀ tξ ∈ cfPocket (R ω) (L ω) r := hsub htξU
  have hpξO := hnot tξ htξab
  have hψpξ : ψ ω (EI₀ tξ) ∈ fwdHull WC q := by
    by_contra hn
    exact hpξO (by rw [hOdom]; exact ⟨hpξC, (hψc ω hω).2.mapsTo hpξC, hn⟩)
  have hψ'pξ : ψ' ω (EI₀ tξ) ∈ fwdHull WU q' := by
    have hn : EI₀ tξ ∉ ((curChart A' R L' r' η ψ' n' qT.toNNReal ω).dom : Set ℂ) := fun h => hpξO (hI₀O h)
    rw [hI₀dom] at hn
    have hH := (hψc' ω hω').2.mapsTo htξU
    have : ψ' ω (EI₀ tξ) ∈ fwdHull WU qT := by
      by_contra hk; exact hn ⟨htξU, hH, hk⟩
    exact QuantumZipper.fwdHull_mono.1 hq'lo'.le this
  obtain ⟨θy, hθy, hpyθ⟩ := harcR ty (by linarith)
  obtain ⟨hNC1, hNC2, hNC3⟩ := R6Fd.nonCorner_of_right_open hcf.conf hcf'.conf h0U hθy
  rw [← hpyθ] at hNC1 hNC2 hNC3
  have hpyU : EI₀ ty ∈ closure (cfPocket (R ω) (L' ω) r') := frontier_subset_closure hNC1
  obtain ⟨εy, hεy, hεyU⟩ := inter_ball_subset_of_noncornerInf hJ (hCo' ω hω') hsub hpyU
    (closure_mono hsub hpyU) hNC2
  have hψ'py : ψ' ω (EI₀ ty) = extendFrom H (fwdMapInv WU qT) (ty : ℂ) :=
    jordan_comp_ext hJ' hE₀' hE₀'c hE₀'m (hFTm (real_mem_Hbar ty))
  have hpyAlive : ψ' ω (EI₀ ty) ∉ closure (fwdHull WU qT) := by
    rw [hψ'py]; exact alive_of_not_mem_Icc hηU hWU hWU0 hqT0 (Or.inl (by linarith))
  have hIncl₀ : cfPocket (R ω) (L' ω) r' ∩ ψ' ω ⁻¹' (H \ fwdHull WU qT) ⊆
      cfPocket (R ω) (L ω) r ∩ ψ ω ⁻¹' (H \ fwdHull WC q) := by
    rw [← hI₀dom, ← hOdom]; exact hI₀O
  have hOU : ∀ w ∈ ((curChartInf A R L r η ψ n q ω).dom : Set ℂ), w ∈ cfPocket (R ω) (L' ω) r' →
      w ∈ ((curChart A' R L' r' η ψ' n' qT.toNNReal ω).dom : Set ℂ) := fun w hwO hwU => by
    show w ∈ ((relChart (fun ω => shiftChart (pChart A' (fun ω => cfPocket (R ω) (L' ω) r') ψ' ω) (n' ω))
      (travAll R L' r' η ψ') qT.toNNReal ω).dom : Set ℂ)
    rw [hqTdom]; exact ⟨hwU, hOphys hwO⟩
  have hpyCalive : ψ ω (EI₀ ty) ∉ closure (fwdHull WC q) := by
    obtain ⟨ρy, hρy, hρysub⟩ := exists_ball_subset_of_alive hJ' hx₀' (hE₀'m (hFTm (real_mem_Hbar ty))) hpyAlive
    refine notMem_closure_of_ball_subsetInf hJ (QuantumZipper.fwdHull_mono.2 _) (hEI₀C ty (real_mem_Hbar ty))
      (lt_min hρy hεy) fun z hz => ?_
    have hzU : z ∈ cfPocket (R ω) (L' ω) r' := hεyU ⟨hz.1, ball_subset_ball (min_le_right _ _) hz.2⟩
    exact hIncl₀ (hρysub ⟨hzU, ball_subset_ball (min_le_left _ _) hz.2⟩)
  -- dead and alive in the outer chart
  have hdeadO : ∀ x : ℝ, EO x = EI₀ tξ → vL 0 < x ∧ x ≤ vR 0 := by
    intro x hx
    rw [hvL', hvL, hvR', hvR]
    have hψx : ψ ω (EO x) = extendFrom H (fwdMapInv WC q) (x : ℂ) :=
      jordan_comp_extInf hJ hE₀ hE₀c hE₀m (hFm (real_mem_Hbar x))
    rw [hx] at hψx
    refine ⟨lt_of_not_ge fun hle => ?_, not_lt.1 fun hgt => ?_⟩
    · rcases hle.lt_or_eq with hlt | heq
      · exact alive_of_not_mem_Icc hηC hWC hWC0 q.coe_nonneg (Or.inl hlt) (hψx ▸ subset_closure hψpξ)
      · have him := R6Fd.landL_im_eq_zero hηC hWC hWC0 q.coe_nonneg
        rw [← heq, ← hψx] at him
        have hH : (0 : ℝ) < (ψ ω (EI₀ tξ)).im := (hψc ω hω).2.mapsTo hpξC
        linarith
    · exact alive_of_not_mem_Icc hηC hWC hWC0 q.coe_nonneg (Or.inr hgt) (hψx ▸ subset_closure hψpξ)
  have haliveO : ∀ x : ℝ, EO x = EI₀ ty → x < vL 0 ∨ vR 0 < x := by
    intro x hx
    rw [hvL', hvL, hvR', hvR]
    by_contra hxI
    push Not at hxI
    have hψx : ψ ω (EO x) = extendFrom H (fwdMapInv WC q) (x : ℂ) :=
      jordan_comp_extInf hJ hE₀ hE₀c hE₀m (hFm (real_mem_Hbar x))
    rw [hx] at hψx
    exact hpyCalive (hψx ▸ dead_of_mem_Icc hηC hWC hWC0 hq0' (hvL0.trans hvR0) hxI)
  -- dead and alive in the later inner chart
  have hdeadI : ∀ x : ℝ, E₀' (extendFrom H (fwdMapInv WU q') (x : ℂ)) = EI₀ tξ → wL 0 < x ∧ x < wR 0 := by
    intro x hx
    rw [hwL', hwLe, hwR', hwRe]
    have hψx : ψ' ω (E₀' (extendFrom H (fwdMapInv WU q') (x : ℂ))) = extendFrom H (fwdMapInv WU q') (x : ℂ) :=
      jordan_comp_ext hJ' hE₀' hE₀'c hE₀'m (hF'm (real_mem_Hbar x))
    rw [hx] at hψx
    have hH : (0 : ℝ) < (ψ' ω (EI₀ tξ)).im := (hψc' ω hω').2.mapsTo htξU
    refine ⟨lt_of_not_ge fun hle => ?_, lt_of_not_ge fun hge => ?_⟩
    · rcases hle.lt_or_eq with hlt | heq
      · exact alive_of_not_mem_Icc hηU hWU hWU0 q'.coe_nonneg (Or.inl hlt) (hψx ▸ subset_closure hψ'pξ)
      · have him := R6Fd.landL_im_eq_zero hηU hWU hWU0 q'.coe_nonneg
        rw [← heq, ← hψx] at him
        linarith
    · rcases hge.lt_or_eq with hgt | heq
      · exact alive_of_not_mem_Icc hηU hWU hWU0 q'.coe_nonneg (Or.inr hgt) (hψx ▸ subset_closure hψ'pξ)
      · have him := R6Fd.landR_im_eq_zero hηU hWU hWU0 q'.coe_nonneg
        rw [heq, ← hψx] at him
        linarith
  -- the later hull near the old one: `K_{q'} ⊆ K_{q_T} ∪ F̄_{q_T}(ℍ̄ ∩ B̄(0, ρ))`
  set S := (fun z => extendFrom H (fwdMapInv WU qT) z) '' (Hbar ∩ closedBall 0 ρ) with hSdef
  have hSc : IsClosed S := by
    have hK : IsCompact (Hbar ∩ closedBall (0 : ℂ) ρ) := by
      refine (isCompact_closedBall 0 ρ).inter_left ?_
      rw [← QuantumZipper.CA.Car.closure_H_eq_Hbar]; exact isClosed_closure
    exact (hK.image_of_continuousOn (hFTc.mono inter_subset_left)).isClosed
  have hKsub : fwdHull WU q' ⊆ fwdHull WU qT ∪ S := by
    intro k hk
    by_cases hkT : k ∈ fwdHull WU qT
    · exact Or.inl hkT
    · right
      have hdiff : k ∈ fwdHull WU (qT + δ) \ fwdHull WU qT := by
        rw [hδdef, add_sub_cancel]; exact ⟨hk, hkT⟩
      rw [Sec5.fwdHull_add_sdiff_eq_image hWU hWU0 hqT0 hδ0] at hdiff
      obtain ⟨a, ha, rfl⟩ := hdiff
      have haH : a ∈ H := QuantumZipper.fwdHull_mono.2 _ ha
      exact ⟨a, ⟨QuantumZipper.H_subset_Hbar haH, hsmall ha⟩, hFTeq haH⟩
  have hfar : ∀ p ∈ closure (cfPocket (R ω) (L' ω) r') \ {cfPt (openPt (R ω) (L' ω) r')}, d₀ ≤ dist p tip →
      ψ' ω p ∉ S := by
    rintro p hp hpd ⟨z, hz, hze⟩
    have hpe : EI₀ z = p := by
      show E₀' (extendFrom H (fwdMapInv WU qT) z) = p
      have hze' : extendFrom H (fwdMapInv WU qT) z = ψ' ω p := hze
      rw [hze']; exact R6Fd.extension_psi_eq hJ' hx₀' hE₀' hE₀'c hp
    have := hρnear z hz.1 (by simpa [mem_closedBall, dist_zero_right] using hz.2)
    rw [hpe] at this
    linarith
  have haliveI : ∀ x : ℝ, E₀' (extendFrom H (fwdMapInv WU q') (x : ℂ)) = EI₀ ty → x < wL 0 ∨ wR 0 < x := by
    intro x hx
    rw [hwL', hwLe, hwR', hwRe]
    by_contra hxI
    push Not at hxI
    have hψx : ψ' ω (E₀' (extendFrom H (fwdMapInv WU q') (x : ℂ))) = extendFrom H (fwdMapInv WU q') (x : ℂ) :=
      jordan_comp_ext hJ' hE₀' hE₀'c hE₀'m (hF'm (real_mem_Hbar x))
    rw [hx] at hψx
    have hd := dead_of_mem_Icc hηU hWU hWU0 hq'pos hwLR' hxI
    rw [← hψx] at hd
    have hcl : closure (fwdHull WU q') ⊆ closure (fwdHull WU qT) ∪ S :=
      (closure_mono hKsub).trans (by rw [closure_union, hSc.closure_eq])
    rcases hcl hd with h | h
    · exact hpyAlive h
    · exact hfar _ (hE₀'m (hFTm (real_mem_Hbar ty))) (min_le_right _ _) h
  -- local agreement at the two test landings
  have hloc : ∀ p : ℂ, d₀ ≤ dist p tip → ∀ ε₁ > 0,
      ((curChartInf A R L r η ψ n q ω).dom : Set ℂ) ∩ ball p ε₁ ⊆ cfPocket (R ω) (L' ω) r' →
      ∃ ε > 0, ((curChartInf A R L r η ψ n q ω).dom : Set ℂ) ∩ ball p ε ⊆
        ((curChart A' R L' r' η ψ' n' q' ω).dom : Set ℂ) := by
    intro p hpd ε₁ hε₁ hsubU
    refine ⟨min ε₁ (d₀ / 2), lt_min hε₁ (half_pos hd₀pos), fun w hw => ?_⟩
    have hwU := hsubU ⟨hw.1, ball_subset_ball (min_le_left _ _) hw.2⟩
    have hwI := hOU w hw.1 hwU
    have hz := hI₀c.fwd_mem hwI
    have hwe : (curChart A' R L' r' η ψ' n' qT.toNNReal ω).2.1 ((curChart A' R L' r' η ψ' n' qT.toNNReal ω).1 w) = w :=
      hI₀c.inv_fwd hwI
    rw [← hwe]
    refine hinc _ hz (lt_of_not_ge fun hle => ?_)
    have h1 := hρnear _ (QuantumZipper.H_subset_Hbar hz) hle
    rw [hI₀E hz, hwe] at h1
    have h2 : dist w p < d₀ / 2 := (mem_ball.1 hw.2).trans_le (min_le_right _ _)
    have h3 := dist_triangle p w tip
    rw [dist_comm p w] at h3
    linarith
  have hlocξ : ∃ ε > 0, ((curChartInf A R L r η ψ n q ω).dom : Set ℂ) ∩ ball (EI₀ tξ) ε ⊆
      ((curChart A' R L' r' η ψ' n' q' ω).dom : Set ℂ) := by
    obtain ⟨ε₁, hε₁, hε₁U⟩ := Metric.isOpen_iff.1 (hCo' ω hω') _ htξU
    exact hloc _ (min_le_left _ _) ε₁ hε₁ fun w hw => hε₁U hw.2
  have hlocy := hloc _ (min_le_right _ _) εy hεy fun w hw => by
    rw [hOdom] at hw
    exact hεyU ⟨hw.1.1, hw.2⟩
  -- the bound of the later inner coordinate near the inner landings
  obtain ⟨C₀', hC₀'⟩ := exists_norm_fwdMapInv_sub_le hWU hWU0 q'.coe_nonneg
  have hbddI : ∀ t ∈ Ioo a (chartAR WU qT), ∃ ε > 0, ∃ M : ℝ,
      ∀ w ∈ ((curChart A' R L' r' η ψ' n' q' ω).dom : Set ℂ) ∩ ball (EI₀ t) ε,
        ‖(curChart A' R L' r' η ψ' n' q' ω).1 w‖ ≤ M := by
    intro t _
    have hpU := hE₀'m (hFTm (real_mem_Hbar t))
    obtain ⟨ε, hε, hεψ⟩ := Metric.continuousWithinAt_iff.1 (hJ'.1 _ hpU) 1 one_pos
    refine ⟨ε, hε, ‖ψ' ω (EI₀ t)‖ + 1 + C₀', fun w hw => ?_⟩
    have hwI := hw.1
    rw [hIdom] at hwI
    rw [hIfwd _ hwI.1]
    have h1 := norm_fwdMap_le hWU hWU0 q'.coe_nonneg hC₀' hwI.2
    have hwx : w ∈ closure (cfPocket (R ω) (L' ω) r') \ {cfPt (openPt (R ω) (L' ω) r')} :=
      ⟨subset_closure hwI.1, fun h => hx₀' (h ▸ hwI.1)⟩
    have h2 := hεψ hwx (mem_ball.1 hw.2)
    rw [dist_eq_norm] at h2
    have h3 := norm_le_norm_add_norm_sub' (ψ' ω w) (ψ' ω (EI₀ t))
    linarith
  exact r6FaceR_left_of_reflection hOc hI₀c hIc hI₀O hIncl hOE hOEc hI₀E hI₀Ec hIE hIEc hwR0 hnot hbdd hdrv hρ0
    hinc hinc0 h2ρ (by linarith [htξ.1]) (by linarith) hdeadO haliveO hdeadI haliveI (by rw [hwL', hwLe]; exact hwL0')
    hρσ hlocξ hlocy hbddI

/-! ### R.6's face of shape `MixedInf`, with no input -/

section Final

open MeasureTheory ProbabilityTheory
open LQGMetric (DistOn)
open QuantumZipper (chiC)
open scoped Real
open WholeField R7Outer R7Leaves R6Nest R6Rel R6Cert PocketMarks PocketSeedOpen PocketStopWallsFin PocketStopSide

universe u

/-- **R.6's face, shape `MixedInf` (outer pocket opening at the flow seed), PROVED with no input** (as
`r6FaceSMixedRemaining`; no `R6Fc.R6NonCornerMixedInfRemaining` needed). -/
theorem r6FaceSMixedInfRemaining {k rL rR c c' : ℝ} : R6FaceSMixedInfRemaining.{u} k rL rR c c' := by
  intro hmix Ω _ _ P _ h W' ζ' αR βR βL αL ζαR ζβR ζβL ζαL hcfg R L η hV MR ML hMR hML r A A' ψ ψ' n n' s q hA
    hA'
  refine ae_of_all P fun ω hωA hωA' hωN => ?_
  obtain ⟨hq0, hqlive, -, hsub, u, hu0, hcap, hrel, -⟩ := hωN
  have hcfO := (hA ω hωA).1
  have hγ : IsDrivenCurve (travAllInf R L r η ψ ω) := (hcfO.props (hA ω hωA).2).1
  have hrtq : ((StripSys.rt q : ℝ≥0) : ℝ) = q := Real.coe_toNNReal _ (by exact_mod_cast hq0.le)
  have hinv : capInv (travAllInf R L r η ψ ω) ((StripSys.rt q : ℝ≥0) : ℝ) = u := by
    rw [hrtq, ← hcap]
    exact hγ.capInv_eq hu0
  have htip : η ω (outerFibreEndInf R L r η ψ (StripSys.rt q) ω) ∈
      cfPocket (innerRight k rL R MR ω) (innerLeft k rR L ML ω) (StripSys.rt s) := by
    unfold outerFibreEndInf
    rw [hinv]
    exact hrel
  have hT0 : 0 ≤ outerFibreEndInf R L r η ψ (StripSys.rt q) ω :=
    outerFibreEndInf_nonneg (fun ω hω => (hA ω hω).1) hωA
  have hq0' : 0 < StripSys.rt q := by
    show 0 < (q : ℝ).toNNReal
    exact Real.toNNReal_pos.2 (by exact_mod_cast hq0)
  have hc0 : ∀ q' : ℚ, innerRelCap (innerRight k rL R MR) (innerLeft k rR L ML) (StripSys.rt s) η ψ'
      (outerFibreEndInf R L r η ψ (StripSys.rt q) ω) ω < q' → ((StripSys.rt q' : ℝ≥0) : ℝ) = q' := by
    intro q' hlo
    refine Real.coe_toNNReal _ (le_trans ?_ hlo.le)
    exact (R5Phase.visitCap_spec (W := fun ω t => W' t.toNNReal ω) (c := fun ω => shiftChart (pChart A'
      (fun ω => cfPocket (innerRight k rL R MR ω) (innerLeft k rR L ML ω) (StripSys.rt s)) ψ' ω) (n' ω)) hωA'
      (hA' ω hωA').1 (hA' ω hωA').2 (R5Phase.shiftChart_dom_facts (n := n')
        (fun ω hω => isOpen_image_negInv' (hA' ω hω).1.conf.isOpen_changePocket
          (hA' ω hω).1.conf.changePocket_subset_H)
        (fun ω hω => PocketJordan.image_negInv_subset_H (hA' ω hω).1.conf.changePocket_subset_H)
        (fun ω hω => (hA' ω hω).2.2.2.2.1) ω hωA').1
      (R5Phase.shiftChart_dom_facts (n := n')
        (fun ω hω => isOpen_image_negInv' (hA' ω hω).1.conf.isOpen_changePocket
          (hA' ω hω).1.conf.changePocket_subset_H)
        (fun ω hω => PocketJordan.image_negInv_subset_H (hA' ω hω).1.conf.changePocket_subset_H)
        (fun ω hω => (hA' ω hω).2.2.2.2.1) ω hωA').2.1
      (R5Phase.shiftChart_dom_facts (n := n')
        (fun ω hω => isOpen_image_negInv' (hA' ω hω).1.conf.isOpen_changePocket
          (hA' ω hω).1.conf.changePocket_subset_H)
        (fun ω hω => PocketJordan.image_negInv_subset_H (hA' ω hω).1.conf.changePocket_subset_H)
        (fun ω hω => (hA' ω hω).2.2.2.2.1) ω hωA').2.2 hT0 htip).1.le
  rcases hmix with ⟨hdL, hdR⟩ | ⟨hdL, hdR⟩
  · -- the shared wall is `L`
    have hLe : innerLeft k rR L ML = L := by simp only [innerLeft, not_lt.2 hdR, ↓reduceIte]
    have hρ : rR = innerLeft k rR rR (k / 2 - 4) := by simp only [innerLeft, not_lt.2 hdR, ↓reduceIte]
    rw [hLe] at htip hsub hc0 ⊢
    obtain ⟨εW, hεW, hpkg⟩ := corner_face_sharedLInf (n := n) (n' := n') (fun ω hω => (hA ω hω).1)
      (fun ω hω => (hA ω hω).2) (fun ω hω => hLe ▸ (hA' ω hω).1) (fun ω hω => hLe ▸ (hA' ω hω).2) hωA hωA' hq0'
      hqlive hsub hT0 htip
    refine ⟨εW, hεW, fun q' hlo hhi hlive _ hincl => ?_⟩
    have hrt' := hc0 q' hlo
    have hcfg' : ∀ ω ∈ A', IsCfPocketConfig (innerRight k rL R MR ω) (L ω) (StripSys.rt s)
        (fun t : ℝ => W' t.toNNReal ω) (η ω) := fun ω hω => hLe ▸ (hA' ω hω).1
    have hψ' : ∀ ω ∈ A', IsCfJordan (innerRight k rL R MR ω) (L ω) (StripSys.rt s) (ψ' ω) := fun ω hω =>
      hLe ▸ (hA' ω hω).2
    have hγ' : IsDrivenCurve (travAll (innerRight k rL R MR) L (StripSys.rt s) η ψ' ω) :=
      ((hcfg' ω hωA').isDrivenCurve (hψ' ω hωA')).1
    have hcO := (R5Phase.shiftChart_dom_facts (n := n)
      (fun ω hω => isOpen_image_negInv' (hA ω hω).1.conf.isOpen_changePocket (hA ω hω).1.conf.changePocket_subset_H)
      (fun ω hω => PocketJordan.image_negInv_subset_H (hA ω hω).1.conf.changePocket_subset_H)
      (fun ω hω => (hA ω hω).2.2.2.2.1) ω hωA).1
    have hcI := (R5Phase.shiftChart_dom_facts (n := n')
      (fun ω hω => isOpen_image_negInv' (hcfg' ω hω).conf.isOpen_changePocket (hcfg' ω hω).conf.changePocket_subset_H)
      (fun ω hω => PocketJordan.image_negInv_subset_H (hcfg' ω hω).conf.changePocket_subset_H)
      (fun ω hω => (hψ' ω hω).2.2.2.1) ω hωA').1
    rw [R6Fc.pocketSetInf_eq hωA hqlive hγ hcO, pocketSet_eq hωA' hlive hγ' hcI]
    exact hpkg (StripSys.rt q') (by rw [hrt']; exact hlo) (by rw [hrt']; exact hhi) hincl _ _ _ _ _ _ _ _ rfl rfl rfl
      rfl hρ
  · -- the shared wall is `R`
    have hRe : innerRight k rL R MR = R := by simp only [innerRight, not_lt.2 hdL, ↓reduceIte]
    have hρ : rL = innerRight k rL rL (k / 2 - 4) := by simp only [innerRight, not_lt.2 hdL, ↓reduceIte]
    rw [hRe] at htip hsub hc0 ⊢
    have hcfg' : ∀ ω ∈ A', IsCfPocketConfig (R ω) (innerLeft k rR L ML ω) (StripSys.rt s)
        (fun t : ℝ => W' t.toNNReal ω) (η ω) := fun ω hω => hRe ▸ (hA' ω hω).1
    have hψ' : ∀ ω ∈ A', IsCfJordan (R ω) (innerLeft k rR L ML ω) (StripSys.rt s) (ψ' ω) := fun ω hω =>
      hRe ▸ (hA' ω hω).2
    obtain ⟨εW, hεW, hpkg⟩ := corner_face_sharedRInf (n := n) (n' := n') (fun ω hω => (hA ω hω).1)
      (fun ω hω => (hA ω hω).2) hcfg' hψ' hωA hωA' hq0' hqlive hsub hT0 htip
    refine ⟨εW, hεW, fun q' hlo hhi hlive _ hincl => ?_⟩
    have hrt' := hc0 q' hlo
    have hγ' : IsDrivenCurve (travAll R (innerLeft k rR L ML) (StripSys.rt s) η ψ' ω) :=
      ((hcfg' ω hωA').isDrivenCurve (hψ' ω hωA')).1
    have hcO := (R5Phase.shiftChart_dom_facts (n := n)
      (fun ω hω => isOpen_image_negInv' (hA ω hω).1.conf.isOpen_changePocket (hA ω hω).1.conf.changePocket_subset_H)
      (fun ω hω => PocketJordan.image_negInv_subset_H (hA ω hω).1.conf.changePocket_subset_H)
      (fun ω hω => (hA ω hω).2.2.2.2.1) ω hωA).1
    have hcI := (R5Phase.shiftChart_dom_facts (n := n')
      (fun ω hω => isOpen_image_negInv' (hcfg' ω hω).conf.isOpen_changePocket (hcfg' ω hω).conf.changePocket_subset_H)
      (fun ω hω => PocketJordan.image_negInv_subset_H (hcfg' ω hω).conf.changePocket_subset_H)
      (fun ω hω => (hψ' ω hω).2.2.2.1) ω hωA').1
    rw [R6Fc.pocketSetInf_eq hωA hqlive hγ hcO, pocketSet_eq hωA' hlive hγ' hcI]
    exact hpkg (StripSys.rt q') (by rw [hrt']; exact hlo) (by rw [hrt']; exact hhi) hincl _ _ _ _ _ _ _ _ rfl rfl rfl
      rfl hρ

end Final

end InteractingSLE.Sec7.R6Cor
