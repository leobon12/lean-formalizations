/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.R6CorTwoInf

/-!
# R.6's local agreement for the shape `TwoInfInf`, without Aux. lemma 136

Packet PROVE-R6-CORNER, second round. As `R6CorTwoInf`, with both the outer pocket `C = cfPocket R L r` and the
outer pocket `V = cfPocket R M_L s ⊆ C` opening at the flow seed (no finite opening corner of `V`; Jordan coordinates
at infinity):

* `two_dom_subset_at_visitInfInf`, `two_inter_subset_at_visitInfInf`, **`two_identity_at_visitInfInf`**: the
  same-time inclusion and Astra's inner-side identity (reverse visits of `M_L`; the arcs of `V` are `(0, rightHi]`
  on `R` and `(0, leftHi]` on `M_L`);
* `hlater_twoInfInf`: the common later time for joint access;
* `two_localInfInf`: `R6Cor.TwoLocalAgreement` per sample, landing set `closure V`;
* **`localAgreementTwoInfInf`**: almost surely on the source event of `R6Lw.R6PhysicalIntervalTwoInfInfRemaining`,
  with LANDING's exact charts, tip and mark.

R43/R48: nothing here uses Theorem 1.2/1.3, `Theorem12ParamStatement`, `Theorem13Statement` or any `*_of_param`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Filter Topology Metric
open QuantumZipper (H Hbar fwdMap fwdMapInv fwdHull)
open scoped NNReal ENNReal

namespace InteractingSLE.Sec7.R6Cor

open Sec6 PocketTraversal Lemma71C PocketJordan PocketCoord PocketCoupling PocketStop PocketStopField HOuter
  PocketWordAssembly R6Safe R6Fc PocketSeedOpen
open WangWu (chartAL chartAR)
open SupercriticalConformalCovariance (IsConformalBijection)

section TwoInfInf

variable {Ω : Type*} {A A' : Set Ω} {R L : Ω → ℝ≥0 → ℂ} {r r' : ℝ≥0} {W : Ω → ℝ → ℝ} {η : Ω → ℝ → ℂ}
  {ψ ψ' : Ω → ℂ → ℂ} {n n' : Ω → ℤ} {ω : Ω}

/-- The same-time inclusion at a strict visit, both pockets opening at the flow seed. -/
theorem two_dom_subset_at_visitInfInf {R' L' : Ω → ℝ≥0 → ℂ}
    (hcfg : ∀ ω ∈ A, IsOuterCfgInf (R ω) (L ω) r (W ω) (η ω)) (hψ : ∀ ω ∈ A, IsCfJordanInf (R ω) (L ω) r (ψ ω))
    (hcfg' : ∀ ω ∈ A', IsOuterCfgInf (R' ω) (L' ω) r' (W ω) (η ω))
    (hψ' : ∀ ω ∈ A', IsCfJordanInf (R' ω) (L' ω) r' (ψ' ω)) (hω : ω ∈ A) (hω' : ω ∈ A')
    (hsub : cfPocket (R' ω) (L' ω) r' ⊆ cfPocket (R ω) (L ω) r) {t : ℝ} (ht0 : 0 ≤ t)
    (ht : η ω t ∈ cfPocket (R' ω) (L' ω) r') {c c' : ℝ≥0} (hc : (c : ℝ) = innerRelCapInf R L r η ψ t ω)
    (hc' : (c' : ℝ) = innerRelCapInf R' L' r' η ψ' t ω)
    (hmeet : (((curChartInf A' R' L' r' η ψ' n' c' ω).dom : Set ℂ) ∩
      (curChartInf A R L r η ψ n c ω).dom).Nonempty) :
    ((curChartInf A' R' L' r' η ψ' n' c' ω).dom : Set ℂ) ⊆ (curChartInf A R L r η ψ n c ω).dom := by
  obtain ⟨-, hlive', -, hdomV, -⟩ := outer_visit_factsInf (n := n') hcfg' hψ' hω' ht0 ht hc'
  obtain ⟨-, -, -, -, hfrC⟩ := outer_visit_factsInf (n := n) hcfg hψ hω ht0 (hsub ht) hc
  have hG' : ∀ ω ∈ A', IsChangeConfigInc (R' ω) (L' ω) r' := fun ω hω => (hcfg' ω hω).conf
  have hCo' : ∀ ω ∈ A', IsOpen (cfPocket (R' ω) (L' ω) r') := fun ω hω =>
    isOpen_image_negInv' (hG' ω hω).isOpen_changePocket (hG' ω hω).changePocket_subset_H
  have hCH' : ∀ ω ∈ A', cfPocket (R' ω) (L' ω) r' ⊆ H := fun ω hω =>
    PocketJordan.image_negInv_subset_H (hG' ω hω).changePocket_subset_H
  obtain ⟨hcI, -, -⟩ := R5Phase.shiftChart_dom_facts hCo' hCH' (fun ω hω => (hψ' ω hω).2.2.2.1) n' ω hω'
  have hγ' : IsDrivenCurve (travAllInf R' L' r' η ψ' ω) := ((hcfg' ω hω').props (hψ' ω hω')).1
  have hI : (curChartInf A' R' L' r' η ψ' n' c' ω).IsConformal :=
    PocketStopSide.isConformal_relChart_of_driven hγ' hlive' hcI
  refine dom_subset_of_frontier_disjoint hI (disjoint_left.2 fun w hwI hwf => ?_) hmeet
  have hwV : w ∈ cfPocket (R' ω) (L' ω) r' :=
    ((relChart_dom_eq_inter (n := n') hCo' hCH' (fun ω hω => (hψ' ω hω).2.2.2.1) hω' hγ' hlive').subset hwI).1
  have hwt := hfrC ⟨hsub hwV, hwf⟩
  have hwK := hdomV hwI
  refine hwK.2 ?_
  rw [(hcfg ω hω).trace.2.2 t ht0]
  exact ⟨hwK.1, Or.inl (subset_closure hwt)⟩

/-- **The identity at a strict visit, both pockets opening at the flow seed** (`two_inter_subset_at_visit`; the
inner pocket has no finite opening corner). -/
theorem two_inter_subset_at_visitInfInf {M : Ω → ℝ≥0 → ℂ}
    (hcfg : ∀ ω ∈ A, IsOuterCfgInf (R ω) (L ω) r (W ω) (η ω)) (hψ : ∀ ω ∈ A, IsCfJordanInf (R ω) (L ω) r (ψ ω))
    (hcfg' : ∀ ω ∈ A', IsOuterCfgInf (R ω) (M ω) r' (W ω) (η ω))
    (hψ' : ∀ ω ∈ A', IsCfJordanInf (R ω) (M ω) r' (ψ' ω)) (hω : ω ∈ A) (hω' : ω ∈ A')
    (hrev : IsWallReverseVisit (M ω) (η ω))
    (hsub : cfPocket (R ω) (M ω) r' ⊆ cfPocket (R ω) (L ω) r) {t : ℝ} (ht0 : 0 ≤ t)
    (ht : η ω t ∈ cfPocket (R ω) (M ω) r') {c c' : ℝ≥0} (hc : (c : ℝ) = innerRelCapInf R L r η ψ t ω)
    (hc' : (c' : ℝ) = innerRelCapInf R M r' η ψ' t ω)
    (hincl : ((curChartInf A' R M r' η ψ' n' c' ω).dom : Set ℂ) ⊆ (curChartInf A R L r η ψ n c ω).dom) :
    ((curChartInf A R L r η ψ n c ω).dom : Set ℂ) ∩ cfPocket (R ω) (M ω) r' ⊆
      (curChartInf A' R M r' η ψ' n' c' ω).dom := by
  have hcf := hcfg ω hω
  have hcf' := hcfg' ω hω'
  obtain ⟨-, hlive, -, hdomC, -⟩ := outer_visit_factsInf (n := n) hcfg hψ hω ht0 (hsub ht) hc
  obtain ⟨-, hlive', -, -, hfrV⟩ := outer_visit_factsInf (n := n') hcfg' hψ' hω' ht0 ht hc'
  have hG : ∀ ω ∈ A, IsChangeConfigInc (R ω) (L ω) r := fun ω hω => (hcfg ω hω).conf
  have hCo : ∀ ω ∈ A, IsOpen (cfPocket (R ω) (L ω) r) := fun ω hω =>
    isOpen_image_negInv' (hG ω hω).isOpen_changePocket (hG ω hω).changePocket_subset_H
  have hCH : ∀ ω ∈ A, cfPocket (R ω) (L ω) r ⊆ H := fun ω hω =>
    PocketJordan.image_negInv_subset_H (hG ω hω).changePocket_subset_H
  have hG' : ∀ ω ∈ A', IsChangeConfigInc (R ω) (M ω) r' := fun ω hω => (hcfg' ω hω).conf
  have hCo' : ∀ ω ∈ A', IsOpen (cfPocket (R ω) (M ω) r') := fun ω hω =>
    isOpen_image_negInv' (hG' ω hω).isOpen_changePocket (hG' ω hω).changePocket_subset_H
  have hCH' : ∀ ω ∈ A', cfPocket (R ω) (M ω) r' ⊆ H := fun ω hω =>
    PocketJordan.image_negInv_subset_H (hG' ω hω).changePocket_subset_H
  obtain ⟨hcO, -, -⟩ := R5Phase.shiftChart_dom_facts hCo hCH (fun ω hω => (hψ ω hω).2.2.2.1) n ω hω
  obtain ⟨hcI, -, -⟩ := R5Phase.shiftChart_dom_facts hCo' hCH' (fun ω hω => (hψ' ω hω).2.2.2.1) n' ω hω'
  have hγ : IsDrivenCurve (travAllInf R L r η ψ ω) := (hcf.props (hψ ω hω)).1
  have hγ' : IsDrivenCurve (travAllInf R M r' η ψ' ω) := (hcf'.props (hψ' ω hω')).1
  have hO : (curChartInf A R L r η ψ n c ω).IsConformal := PocketStopSide.isConformal_relChart_of_driven hγ hlive hcO
  have hI : (curChartInf A' R M r' η ψ' n' c' ω).IsConformal :=
    PocketStopSide.isConformal_relChart_of_driven hγ' hlive' hcI
  have hOdom := relChart_dom_eq_inter (n := n) hCo hCH (fun ω hω => (hψ ω hω).2.2.2.1) hω hγ hlive
  have hIdom := relChart_dom_eq_inter (n := n') hCo' hCH' (fun ω hω => (hψ' ω hω).2.2.2.1) hω' hγ' hlive'
  have hD : IsPreconnected ((curChartInf A R L r η ψ n c ω).dom : Set ℂ) := by
    rw [hO.coe_dom]; exact convex_H.isPreconnected.image _ hO.1.continuousOn
  have hne : ((curChartInf A' R M r' η ψ' n' c' ω).dom : Set ℂ).Nonempty := by
    rw [hI.coe_dom]
    exact ⟨_, Complex.I, show (0 : ℝ) < Complex.I.im by simp, rfl⟩
  have hKt : ∀ w ∈ H, w ∈ η ω '' Icc 0 t → w ∈ fwdHull (W ω) t := fun w hwH hw => by
    rw [hcf.trace.2.2 t ht0]; exact ⟨hwH, Or.inl (subset_closure hw)⟩
  refine inter_subset_of_frontier_balls hD (hCo' ω hω') (curChartInf A' R M r' η ψ' n' c' ω).dom.isOpen hne hincl
    ?_ ?_
  · intro w hwD hwV hwcl
    by_contra hwI
    have hwf : w ∈ frontier ((curChartInf A' R M r' η ψ' n' c' ω).dom : Set ℂ) :=
      ⟨hwcl, by rw [(curChartInf A' R M r' η ψ' n' c' ω).dom.isOpen.interior_eq]; exact hwI⟩
    have hwK := hdomC hwD
    exact hwK.2 (hKt w hwK.1 (hfrV ⟨hwV, hwf⟩))
  intro m hmD hmfr
  have hmK := hdomC hmD
  have hmC : m ∈ cfPocket (R ω) (L ω) r := (hOdom.subset hmD).1
  obtain ⟨-, hv, huv, -, hb, hab, -, -⟩ := hcf'.conf.changeCorner_props
  have hhiR : 0 < rightHi (R ω) (M ω) r' := hcf'.seed ▸ huv
  have hhiL : 0 < leftHi (R ω) (M ω) r' := (hcf'.conf.leftLo_eq_zero_of_rightLo_eq_zero hcf'.seed) ▸ hab
  have hRnot : ∀ θ ∈ Ioc (0 : ℝ) (rightHi (R ω) (M ω) r'), R6Fd.wallPt (R ω) θ ∉ cfPocket (R ω) (L ω) r :=
    fun θ hθ => R6Fd.wallPt_notMem hcf.conf (Or.inl rfl) ⟨hθ.1, hθ.2.trans hv.2⟩
  have hmcl : m ∈ closure (cfPocket (R ω) (M ω) r') := hmfr.1
  have hJ : Sec6.IsJordanCoordInf (cfPocket (R ω) (M ω) r') (cfPt (closePt (R ω) (M ω) r')) (ψ' ω) := hψ' ω hω'
  have him : (ψ' ω m).im = 0 := hJ.2.2.2.2.1 m hmfr
  rcases lt_trichotomy (ψ' ω m).re 0 with hneg | hzero | hpos
  · obtain ⟨θ, hθ, hmθ⟩ := frontier_neg_right_arcInf hcf'.conf hcf'.seed hcf'.oriented (hψ' ω hω') hmfr hneg
    rw [hmθ] at hmC
    exact absurd hmC (hRnot θ ⟨hθ.1, hθ.2.le⟩)
  · have hy := ((R6Fd.right_arc_factsInf hcf'.conf hcf'.seed hcf'.oriented (hψ' ω hω')).1 _ ⟨hhiR, le_rfl⟩)
    have he : ψ' ω m = ψ' ω (R6Fd.wallPt (R ω) (rightHi (R ω) (M ω) r')) := by
      have hy0 : ψ' ω (R6Fd.wallPt (R ω) (rightHi (R ω) (M ω) r')) = 0 := hJ.2.2.2.2.2.1
      apply Complex.ext
      · rw [hzero, hy0, Complex.zero_re]
      · rw [him, hy.2]
    have hme := hJ.2.1 hmcl hy.1 he
    rw [hme] at hmC
    exact absurd hmC (hRnot _ ⟨hhiR, le_rfl⟩)
  obtain ⟨θ, hθ, hmθ⟩ := frontier_pos_left_arcInf hcf'.conf hcf'.seed hcf'.oriented (hψ' ω hω') hmfr hpos
  obtain ⟨-, -, hanti⟩ := R6Fd.left_arc_factsInf hcf'.conf hcf'.seed hcf'.oriented (hψ' ω hω')
  have hP' := hcf'.toPocketInf (hψ' ω hω')
  have hL' := hP'.erase.clockEnd_pos
  have hv' := hP'.erase.mem_visitSet ht0 ht
  have htI : firstHit (η ω) (cfArcRInf (R ω) (M ω) r' 0) ≤ t := le_of_lt hv'.1
  have hrel0 := PocketStopMarked.Outer.relTimeInf_nonneg hP' htI
  have hcapInv : capInv (travAllInf R M r' η ψ' ω) c' = PocketStopMarked.relTimeInf (η ω) (cfPocket (R ω) (M ω) r')
      (firstHit (η ω) (cfArcRInf (R ω) (M ω) r' 0)) t := by
    rw [hc']; exact hγ'.capInv_eq hrel0
  have halive : ψ' ω m ∉ closure (fwdHull (fun s : ℝ => segDriver (travAllInf R M r' η ψ' ω) s.toNNReal) c') := by
    rw [hγ'.fwdHull_segDriver c'.coe_nonneg (by rw [ENNReal.ofReal_coe_nnreal]; exact hlive')]
    intro hcl
    have hmreal : ψ' ω m = (((ψ' ω m).re : ℝ) : ℂ) := Complex.ext rfl (by rw [Complex.ofReal_im]; exact him)
    rw [hmreal] at hcl
    have hZc : IsCompact (travAllInf R M r' η ψ' ω '' Icc 0 (capInv (travAllInf R M r' η ψ' ω) c')) :=
      isCompact_Icc.image_of_continuousOn (hγ'.continuousOn.mono Icc_subset_Ici_self)
    have hZH : travAllInf R M r' η ψ' ω '' Icc 0 (capInv (travAllInf R M r' η ψ' ω) c') ⊆ Hbar := by
      rintro _ ⟨u, hu, rfl⟩
      exact hJ.2.2.1 (hP'.erase.erasedPath_mem (clockOf_mem_Ico hL' hu.1))
    obtain ⟨_, ⟨u, hu, rfl⟩, hzim, hzre⟩ := R6Fd.exists_real_ge_of_mem_closure_fillH hZc hZH hcl
    have hpm := hP'.erase.erasedPath_mem (clockOf_mem_Ico hL' hu.1)
    set p := erasedPathInf (η ω) (cfPocket (R ω) (M ω) r') (firstHit (η ω) (cfArcRInf (R ω) (M ω) r' 0))
      (clockOf (clockEnd (η ω) (cfPocket (R ω) (M ω) r') (firstHit (η ω) (cfArcRInf (R ω) (M ω) r' 0))) u)
      with hpdef
    have hψp : travAllInf R M r' η ψ' ω u = ψ' ω p := rfl
    rw [hψp] at hzim hzre
    have hpV : p ∉ cfPocket (R ω) (M ω) r' := fun h => by
      have h2 : (0 : ℝ) < (ψ' ω p).im := (hψ' ω hω').2.2.2.1.2.mapsTo h
      rw [hzim] at h2; exact lt_irrefl _ h2
    have hpfr : p ∈ frontier (cfPocket (R ω) (M ω) r') :=
      ⟨hpm, by rw [(hCo' ω hω').interior_eq]; exact hpV⟩
    obtain ⟨θ', hθ', hpθ⟩ := frontier_pos_left_arcInf hcf'.conf hcf'.seed hcf'.oriented (hψ' ω hω') hpfr
      (by linarith)
    have hθθ' : θ' ≤ θ := by
      by_contra hlt
      push Not at hlt
      have h : (ψ' ω (R6Fd.wallPt (M ω) θ')).re < (ψ' ω (R6Fd.wallPt (M ω) θ)).re :=
        hanti ⟨hθ.1, hθ.2.le⟩ ⟨hθ'.1, hθ'.2.le⟩ hlt
      rw [← hpθ, ← hmθ] at h
      linarith
    have hct : pocketClockInf (η ω) (cfPocket (R ω) (M ω) r') (firstHit (η ω) (cfArcRInf (R ω) (M ω) r' 0)) t ∈
        Ico 0 (clockEnd (η ω) (cfPocket (R ω) (M ω) r') (firstHit (η ω) (cfArcRInf (R ω) (M ω) r' 0))) :=
      ⟨hP'.erase.clock_nonneg htI, hP'.erase.clock_lt_clockEnd_of_mem hv'⟩
    have hu' : clockOf (clockEnd (η ω) (cfPocket (R ω) (M ω) r') (firstHit (η ω) (cfArcRInf (R ω) (M ω) r' 0))) u ≤
        pocketClockInf (η ω) (cfPocket (R ω) (M ω) r') (firstHit (η ω) (cfArcRInf (R ω) (M ω) r' 0)) t := by
      rw [← PocketStopMarked.Outer.clockOf_relTimeInf hP' htI]
      exact (strictMonoOn_clockOf hL').monotoneOn hu.1 hrel0 (hcapInv ▸ hu.2)
    have hft := hP'.erase.monotoneOn_fibre (clockOf_mem_Ico hL' hu.1) hct hu'
    rw [hP'.erase.fibre_clock_of_mem hv'] at hft
    have hpt : p ∈ η ω '' Icc 0 t :=
      ⟨_, ⟨hP'.erase.fibre_nonneg (clockOf_mem_Ico hL' hu.1), hft⟩, rfl⟩
    have hθ'I : θ' ∈ Ioc (0 : ℝ) 1 := ⟨hθ'.1, hθ'.2.le.trans hb.2⟩
    have hθI : θ ∈ Ioc (0 : ℝ) 1 := ⟨hθ.1, hθ.2.le.trans hb.2⟩
    rw [hpθ] at hpt
    have hmt : m ∈ η ω '' Icc 0 t := by
      rw [hmθ]; exact PocketJordan.wall_rev hcf'.conf.left hcf.trace.1 hrev hθ'I hθI hθθ' hpt
    exact hmK.2 (hKt m hmK.1 hmt)
  obtain ⟨ρ, hρ, hρI⟩ := exists_ball_subset_of_aliveInf hJ hmcl halive
  refine ⟨ρ, hρ, fun z hz => ?_⟩
  rw [hIdom]
  exact hρI hz

/-- **The identity at a strict visit, with the common point found near the tip**
(`R6Two.exists_rat_meet_near_tip_two`): both `D_V(c_V(t)) ⊆ D_C(c_C(t))` and `D_C(c_C(t)) ∩ V ⊆ D_V(c_V(t))`. -/
theorem two_identity_at_visitInfInf {M : Ω → ℝ≥0 → ℂ}
    (hcfg : ∀ ω ∈ A, IsOuterCfgInf (R ω) (L ω) r (W ω) (η ω)) (hψ : ∀ ω ∈ A, IsCfJordanInf (R ω) (L ω) r (ψ ω))
    (hcfg' : ∀ ω ∈ A', IsOuterCfgInf (R ω) (M ω) r' (W ω) (η ω))
    (hψ' : ∀ ω ∈ A', IsCfJordanInf (R ω) (M ω) r' (ψ' ω)) (hω : ω ∈ A) (hω' : ω ∈ A')
    (hrev : IsWallReverseVisit (M ω) (η ω))
    (hsub : cfPocket (R ω) (M ω) r' ⊆ cfPocket (R ω) (L ω) r) {t : ℝ} (ht0 : 0 ≤ t)
    (ht : η ω t ∈ cfPocket (R ω) (M ω) r') {c c' : ℝ≥0} (hc : (c : ℝ) = innerRelCapInf R L r η ψ t ω)
    (hc' : (c' : ℝ) = innerRelCapInf R M r' η ψ' t ω) :
    ((curChartInf A' R M r' η ψ' n' c' ω).dom : Set ℂ) ⊆ (curChartInf A R L r η ψ n c ω).dom ∧
      ((curChartInf A R L r η ψ n c ω).dom : Set ℂ) ∩ cfPocket (R ω) (M ω) r' ⊆
        (curChartInf A' R M r' η ψ' n' c' ω).dom := by
  obtain ⟨-, hlive, hend, -, -⟩ := outer_visit_factsInf (n := n) hcfg hψ hω ht0 (hsub ht) hc
  obtain ⟨-, -, -, -, -⟩ := outer_visit_factsInf (n := n') hcfg' hψ' hω' ht0 ht hc'
  have htip : η ω (outerFibreEndInf R L r η ψ c ω) ∈ cfPocket (R ω) (M ω) r' := by rw [hend]; exact ht
  obtain ⟨q'', hlo, -, hlive'', -, hmeet, -⟩ := R6Two.exists_rat_meet_near_tip_twoInfInf (n := n) (n' := n') hcfg hψ hω
    hlive hcfg' hψ' hω' hsub htip one_pos
  rw [hend, ← hc'] at hlo
  have hG' : ∀ ω ∈ A', IsChangeConfigInc (R ω) (M ω) r' := fun ω hω => (hcfg' ω hω).conf
  have hCo' : ∀ ω ∈ A', IsOpen (cfPocket (R ω) (M ω) r') := fun ω hω =>
    isOpen_image_negInv' (hG' ω hω).isOpen_changePocket (hG' ω hω).changePocket_subset_H
  have hCH' : ∀ ω ∈ A', cfPocket (R ω) (M ω) r' ⊆ H := fun ω hω =>
    PocketJordan.image_negInv_subset_H (hG' ω hω).changePocket_subset_H
  obtain ⟨hcI, -, -⟩ := R5Phase.shiftChart_dom_facts hCo' hCH' (fun ω hω => (hψ' ω hω).2.2.2.1) n' ω hω'
  have hγ' : IsDrivenCurve (travAllInf R M r' η ψ' ω) := ((hcfg' ω hω').props (hψ' ω hω')).1
  have hle : c' ≤ StripSys.rt q'' := by
    rw [← NNReal.coe_le_coe, StripSys.rt, Real.coe_toNNReal _ ((NNReal.coe_nonneg c').trans hlo.le)]
    exact hlo.le
  have hanti := R6Two.relChart_dom_antitone (c := fun ω => shiftChart (pChart A' (fun ω => cfPocket (R ω) (M ω) r')
    ψ' ω) (n' ω)) hcI hγ' hlive'' hle
  obtain ⟨z, hzV, hzC⟩ := hmeet
  have hincl := two_dom_subset_at_visitInfInf (n := n) (n' := n') hcfg hψ hcfg' hψ' hω hω' hsub ht0 ht hc hc'
    ⟨z, hanti hzV, hzC⟩
  exact ⟨hincl, two_inter_subset_at_visitInfInf hcfg hψ hcfg' hψ' hω hω' hrev hsub ht0 ht hc hc' hincl⟩

/-- **The common later time (two outer pockets)**: for small `s, s'` a time `t₂` just after `T = T_C(q)` with
`η(t₂) ∈ V` gives an inner capacity `q₂' = c_V(t₂) ∈ (q_T, q_T + s')` and an outer capacity `q₂ ∈ (c_C(t₂), q + s)`;
on `V`, `ψ'(z) ∈ K^V_{q₂'}` means `z ∉ D_V(c_V(t₂))`, hence (the identity at `t₂`) `z ∉ D_C(c_C(t₂)) ⊇ D_C(q₂)`. -/
theorem hlater_twoInfInf {M : Ω → ℝ≥0 → ℂ}
    (hcfg : ∀ ω ∈ A, IsOuterCfgInf (R ω) (L ω) r (W ω) (η ω)) (hψ : ∀ ω ∈ A, IsCfJordanInf (R ω) (L ω) r (ψ ω))
    (hcfg' : ∀ ω ∈ A', IsOuterCfgInf (R ω) (M ω) r' (W ω) (η ω))
    (hψ' : ∀ ω ∈ A', IsCfJordanInf (R ω) (M ω) r' (ψ' ω)) (hω : ω ∈ A) (hω' : ω ∈ A')
    (hrev : IsWallReverseVisit (M ω) (η ω))
    {q : ℝ≥0} (hq : (q : ℝ≥0∞) < capLife (travAllInf R L r η ψ ω))
    (hsub : cfPocket (R ω) (M ω) r' ⊆ cfPocket (R ω) (L ω) r)
    (hT0 : 0 ≤ outerFibreEndInf R L r η ψ q ω)
    (htip : η ω (outerFibreEndInf R L r η ψ q ω) ∈ cfPocket (R ω) (M ω) r')
    {WC WU : ℝ → ℝ} {t₁ t₁' : ℝ≥0} (hqt₁ : q < t₁) (ht₁ : (t₁ : ℝ≥0∞) < capLife (travAllInf R L r η ψ ω))
    (hqTt₁' : innerRelCapInf R M r' η ψ' (outerFibreEndInf R L r η ψ q ω) ω < t₁')
    (hCdom : ∀ q₂ : ℝ≥0, q₂ < t₁ → ((curChartInf A R L r η ψ n q₂ ω).dom : Set ℂ) =
      cfPocket (R ω) (L ω) r ∩ ψ ω ⁻¹' (H \ fwdHull WC q₂))
    (hUdom : ∀ q₂ : ℝ≥0, q₂ < t₁' → ((curChartInf A' R M r' η ψ' n' q₂ ω).dom : Set ℂ) =
      cfPocket (R ω) (M ω) r' ∩ ψ' ω ⁻¹' (H \ fwdHull WU q₂)) :
    ∀ s > 0, ∀ s' > 0, ∃ q₂ q₂' : ℝ, (q : ℝ) ≤ q₂ ∧ q₂ < q + s ∧
      innerRelCapInf R M r' η ψ' (outerFibreEndInf R L r η ψ q ω) ω < q₂' ∧
      q₂' < innerRelCapInf R M r' η ψ' (outerFibreEndInf R L r η ψ q ω) ω + s' ∧
      ∀ z ∈ cfPocket (R ω) (M ω) r', ψ' ω z ∈ fwdHull WU q₂' → ψ ω z ∈ fwdHull WC q₂ := by
  intro s hs s' hs'
  set T := outerFibreEndInf R L r η ψ q ω with hTdef
  set qT := innerRelCapInf R M r' η ψ' T ω with hqTdef
  have hcf := hcfg ω hω
  have hcf' := hcfg' ω hω'
  have hG : ∀ ω ∈ A, IsChangeConfigInc (R ω) (L ω) r := fun ω hω => (hcfg ω hω).conf
  have hCo : ∀ ω ∈ A, IsOpen (cfPocket (R ω) (L ω) r) := fun ω hω =>
    isOpen_image_negInv' (hG ω hω).isOpen_changePocket (hG ω hω).changePocket_subset_H
  have hCH : ∀ ω ∈ A, cfPocket (R ω) (L ω) r ⊆ H := fun ω hω =>
    PocketJordan.image_negInv_subset_H (hG ω hω).changePocket_subset_H
  have hγ : IsDrivenCurve (travAllInf R L r η ψ ω) := (hcf.props (hψ ω hω)).1
  have hPo := hcf.toPocketInf (hψ ω hω)
  have hP'o := hcf'.toPocketInf (hψ' ω hω')
  have hqlive : ENNReal.ofReal (q : ℝ) < capLife (travAllInf R L r η ψ ω) := by
    rw [ENNReal.ofReal_coe_nnreal]; exact hq
  obtain ⟨hc0, hcq⟩ := hγ.capInv_spec q.coe_nonneg hqlive
  obtain ⟨hTmem, hTrel⟩ := PocketStopMarked.Outer.relTimeInf_fibre_clockOf hPo hc0
  replace hTmem : firstHit (η ω) (cfArcRInf (R ω) (L ω) r 0) ≤ T := hTmem
  replace hTrel : PocketStopMarked.relTimeInf (η ω) (cfPocket (R ω) (L ω) r)
      (firstHit (η ω) (cfArcRInf (R ω) (L ω) r 0)) T = capInv (travAllInf R L r η ψ ω) q := hTrel
  have hrelT : PocketStopMarked.relCapInf (η ω) (cfPocket (R ω) (L ω) r)
      (firstHit (η ω) (cfArcRInf (R ω) (L ω) r 0)) (ψ ω) T = q := by
    unfold PocketStopMarked.relCapInf
    rw [hTrel]
    exact hcq
  have hvT := hP'o.erase.mem_visitSet hT0 htip
  have hTI : firstHit (η ω) (cfArcRInf (R ω) (M ω) r' 0) ≤ T := le_of_lt hvT.1
  set s₁ := min s ((t₁ : ℝ) - q) with hs₁
  have hs₁0 : 0 < s₁ := lt_min hs (sub_pos.2 (by exact_mod_cast hqt₁))
  set s₁' := min s' ((t₁' : ℝ) - qT) with hs₁'
  have hs₁'0 : 0 < s₁' := lt_min hs' (by linarith)
  have hcC := PocketStopMarked.Outer.continuousOn_relCapInf hPo T hTmem
  have hcU := PocketStopMarked.Outer.continuousOn_relCapInf hP'o T hTI
  have hmem : ∀ σ₀ τ₀ : ℝ, τ₀ ≤ T → T < σ₀ → Ico τ₀ σ₀ ∈ 𝓝[>] T := fun σ₀ τ₀ h1 h2 =>
    mem_of_superset (Ioo_mem_nhdsGT h2) fun t ht => ⟨h1.trans ht.1.le, ht.2⟩
  have e2 : ∀ᶠ t in 𝓝[>] T, PocketStopMarked.relCapInf (η ω) (cfPocket (R ω) (L ω) r)
      (firstHit (η ω) (cfArcRInf (R ω) (L ω) r 0)) (ψ ω) t < q + s₁ := by
    have h := (hcC.mono_of_mem_nhdsWithin (mem_of_superset self_mem_nhdsWithin fun t ht =>
      show firstHit (η ω) (cfArcRInf (R ω) (L ω) r 0) ≤ t from hTmem.trans (le_of_lt ht))).tendsto
    rw [hrelT] at h
    exact h.eventually (gt_mem_nhds (by linarith))
  have e3 : ∀ᶠ t in 𝓝[>] T, PocketStopMarked.relCapInf (η ω) (cfPocket (R ω) (M ω) r')
      (firstHit (η ω) (cfArcRInf (R ω) (M ω) r' 0)) (ψ' ω) t < qT + s₁' := by
    have h := (hcU.mono_of_mem_nhdsWithin (mem_of_superset self_mem_nhdsWithin fun t ht =>
      show firstHit (η ω) (cfArcRInf (R ω) (M ω) r' 0) ≤ t from hTI.trans (le_of_lt ht))).tendsto
    exact h.eventually (gt_mem_nhds (by show qT < qT + s₁'; linarith))
  have e4 : ∀ᶠ t in 𝓝[>] T, η ω t ∈ cfPocket (R ω) (M ω) r' := by
    have h := ((hcf.trace.2.1 T hT0).mono_of_mem_nhdsWithin
      (mem_of_superset self_mem_nhdsWithin fun t ht => le_of_lt (lt_of_le_of_lt hT0 ht))).tendsto
    exact h.eventually (hP'o.erase.isOpen.mem_nhds htip)
  obtain ⟨t₂, ht₂I, ht₂C, ht₂U, ht₂η⟩ :=
    ((show ∀ᶠ t in 𝓝[>] T, t ∈ Ioi T from self_mem_nhdsWithin).and (e2.and (e3.and e4))).exists
  have hTt₂ : T < t₂ := ht₂I
  have ht₂C' : firstHit (η ω) (cfArcRInf (R ω) (L ω) r 0) ≤ t₂ := hTmem.trans hTt₂.le
  have ht₂0 : 0 ≤ t₂ := hT0.trans hTt₂.le
  set q₂' := innerRelCapInf R M r' η ψ' t₂ ω with hq₂'def
  have hq₂' : qT < q₂' := R6Two.relCapInf_outer_lt_of_visit hP'o hvT hTt₂
  set c₂ := innerRelCapInf R L r η ψ t₂ ω with hc₂
  have hc₂q : (q : ℝ) ≤ c₂ := by
    rw [← hrelT]; exact PocketStopMarked.Outer.monotoneOn_relCapInf hPo hTmem ht₂C' hTt₂.le
  have ht₂C'' : c₂ < q + s₁ := ht₂C
  set q₂ := (c₂ + (q + s₁)) / 2 with hq₂def
  have hq₂lo : c₂ < q₂ := by linarith
  have hq₂hi : q₂ < q + s₁ := by linarith
  refine ⟨q₂, q₂', by linarith, hq₂hi.trans_le (by linarith [min_le_left s ((t₁ : ℝ) - q)]), hq₂',
    ht₂U.trans_le (by linarith [min_le_left s' ((t₁' : ℝ) - qT)]), fun z hzU hzK => ?_⟩
  have hqT0' : 0 ≤ qT := (SideVis.erasureInf_relCap_pos_lt_of_visit hP'o.erase hP'o.driven hvT).1.le
  have hq₂'0 : 0 ≤ q₂' := hqT0'.trans hq₂'.le
  have hc₂0 : 0 ≤ c₂ := (q.coe_nonneg).trans hc₂q
  -- the identity at `t₂`
  obtain ⟨-, hid⟩ := two_identity_at_visitInfInf (n := n) (n' := n') hcfg hψ hcfg' hψ' hω hω' hrev hsub ht₂0 ht₂η
    (c := c₂.toNNReal) (c' := q₂'.toNNReal) (Real.coe_toNNReal _ hc₂0) (Real.coe_toNNReal _ hq₂'0)
  have ht₂U'' : q₂' < qT + s₁' := ht₂U
  have hq₂'t : q₂'.toNNReal < t₁' := by
    rw [← NNReal.coe_lt_coe, Real.coe_toNNReal _ hq₂'0]
    linarith [min_le_right s' ((t₁' : ℝ) - qT)]
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
  obtain ⟨hcO, -, -⟩ := R5Phase.shiftChart_dom_facts hCo hCH (fun ω hω => (hψ ω hω).2.2.2.1) n ω hω
  have hle : c₂.toNNReal ≤ q₂.toNNReal := Real.toNNReal_le_toNNReal hq₂lo.le
  have hz2 := R6Two.relChart_dom_antitone (c := fun ω => shiftChart (pChart A (fun ω => cfPocket (R ω) (L ω) r)
    ψ ω) (n ω)) hcO hγ hq₂live hle hzCq
  have hzV := hid ⟨hz2, hzU⟩
  have hzV' : z ∈ ((curChartInf A' R M r' η ψ' n' q₂'.toNNReal ω).dom : Set ℂ) := hzV
  rw [hUdom _ hq₂'t, Real.coe_toNNReal _ hq₂'0] at hzV'
  exact hzV'.2.2 hzK



/-- **Local agreement, shape `TwoInfInf`** (both pockets opening at the flow seed; per sample): as
`two_localInf`, with `two_identity_at_visitInfInf` and the seed-opening chart of `V`. -/
theorem two_localInfInf {A A' : Set Ω} {R L Lv : Ω → ℝ≥0 → ℂ} {r r' : ℝ≥0} {W : Ω → ℝ → ℝ}
    {η : Ω → ℝ → ℂ} {ψ ψ' : Ω → ℂ → ℂ} {n n' : Ω → ℤ} {ω : Ω}
    (hcfg : ∀ ω ∈ A, IsOuterCfgInf (R ω) (L ω) r (W ω) (η ω)) (hψ : ∀ ω ∈ A, IsCfJordanInf (R ω) (L ω) r (ψ ω))
    (hcfg' : ∀ ω ∈ A', IsOuterCfgInf (R ω) (Lv ω) r' (W ω) (η ω))
    (hψ' : ∀ ω ∈ A', IsCfJordanInf (R ω) (Lv ω) r' (ψ' ω)) (hω : ω ∈ A) (hω' : ω ∈ A')
    (hrev : IsWallReverseVisit (Lv ω) (η ω)) {q : ℝ≥0} (hq0 : 0 < q)
    (hq : (q : ℝ≥0∞) < capLife (travAllInf R L r η ψ ω))
    (hsub : cfPocket (R ω) (Lv ω) r' ⊆ cfPocket (R ω) (L ω) r)
    (hT0 : 0 ≤ outerFibreEndInf R L r η ψ q ω)
    (htip : η ω (outerFibreEndInf R L r η ψ q ω) ∈ cfPocket (R ω) (Lv ω) r') :
    TwoLocalAgreement (curChartInf A R L r η ψ n q ω)
      (curChartInf A' R Lv r' η ψ' n' (innerRelCapInf R Lv r' η ψ' (outerFibreEndInf R L r η ψ q ω) ω).toNNReal ω)
      (cfPocket (R ω) (Lv ω) r') (closure (cfPocket (R ω) (Lv ω) r'))
      (η ω (outerFibreEndInf R L r η ψ q ω)) (seedLInf R L r η ψ q ω) := by
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
  have hOphys : ((curChartInf A R L r η ψ n q ω).dom : Set ℂ) ⊆
      H \ fwdHull (W ω) (outerFibreEndInf R L r η ψ q ω) := by
    intro w hwO
    have hzD : w ∈ cfPocket (R ω) (L ω) r ∩
        ψ ω ⁻¹' (H \ fwdHull (fun s : ℝ => segDriver (travAllInf R L r η ψ ω) s.toNNReal) q) := by
      rw [← relChart_dom_eq_inter (n := n) hCo hCH hψc hω hγ hq]; exact hwO
    exact outer_dom_physInf hcfg hψ hω hq hzD
  -- the inner pocket
  have hcf' := hcfg' ω hω'
  have hG' : ∀ ω ∈ A', IsChangeConfigInc (R ω) (Lv ω) r' := fun ω hω => (hcfg' ω hω).conf
  have hCo' : ∀ ω ∈ A', IsOpen (cfPocket (R ω) (Lv ω) r') := fun ω hω =>
    isOpen_image_negInv' (hG' ω hω).isOpen_changePocket (hG' ω hω).changePocket_subset_H
  have hCH' : ∀ ω ∈ A', cfPocket (R ω) (Lv ω) r' ⊆ H := fun ω hω =>
    PocketJordan.image_negInv_subset_H (hG' ω hω).changePocket_subset_H
  have hψc' : ∀ ω ∈ A', IsConformalBijection (ψ' ω) (cfPocket (R ω) (Lv ω) r') H := fun ω hω =>
    (hψ' ω hω).2.2.2.1
  have hJ' : Sec6.IsJordanCoordInf (cfPocket (R ω) (Lv ω) r') (cfPt (closePt (R ω) (Lv ω) r')) (ψ' ω) := hψ' ω hω'
  have hγ' : IsDrivenCurve (travAllInf R Lv r' η ψ' ω) := (hcf'.props (hψ' ω hω')).1
  have hP'o := hcf'.toPocketInf (hψ' ω hω')
  have hvisit := hP'o.erase.mem_visitSet hT0 htip
  obtain ⟨hqTpos, hqTlive⟩ : 0 < innerRelCapInf R Lv r' η ψ' (outerFibreEndInf R L r η ψ q ω) ω ∧
      ENNReal.ofReal (innerRelCapInf R Lv r' η ψ' (outerFibreEndInf R L r η ψ q ω) ω) <
        capLife (travAllInf R Lv r' η ψ' ω) :=
    SideVis.erasureInf_relCap_pos_lt_of_visit hP'o.erase hP'o.driven hvisit
  set qT := innerRelCapInf R Lv r' η ψ' (outerFibreEndInf R L r η ψ q ω) ω with hqTdef
  have hqT0 : (0 : ℝ) ≤ qT := hqTpos.le
  have hqTc : ((qT.toNNReal : ℝ≥0) : ℝ) = qT := Real.coe_toNNReal _ hqT0
  obtain ⟨t₁', hqTt₁', ht₁'⟩ := ENNReal.lt_iff_exists_nnreal_btwn.1 hqTlive
  have hqTt : qT.toNNReal < t₁' := ENNReal.coe_lt_coe.1 hqTt₁'
  have hqTt' : qT < t₁' := by rw [← hqTc]; exact_mod_cast hqTt
  obtain ⟨E₀', hE₀', hE₀'c, hE₀'m, WU, hWU, hWU0, hWUeq, ηU, hηU, hηUeq, hUf⟩ :=
    chart_factsInf (n := n') hCo' hCH' hψc' hJ' hω' hγ' ht₁'
  obtain ⟨hI₀c, hI₀dom, hI₀fwd, hI₀E, hI₀Ec⟩ := hUf qT.toNNReal hqTt
  rw [hqTc] at hI₀dom hI₀fwd hI₀E hI₀Ec
  -- the same-time inclusion and the identity
  obtain ⟨hI₀O, hid⟩ := two_identity_at_visitInfInf (n := n) (n' := n') hcfg hψ hcfg' hψ' hω hω' hrev hsub hT0
    htip (c := q) (c' := qT.toNNReal) (relCap_outerFibreEndInf hcfg hψ hω hq).symm hqTc
  -- the outer landing description
  have hOsubC : ((curChartInf A R L r η ψ n q ω).dom : Set ℂ) ⊆ cfPocket (R ω) (L ω) r := fun w hw => by
    rw [hOdom] at hw; exact hw.1
  refine ⟨hI₀O, hid, ?_, ?_, ?_⟩
  · obtain ⟨ε, hε, hεV⟩ := Metric.isOpen_iff.1 (hCo' ω hω') _ htip
    exact ⟨ε, hε, fun w hw => hid ⟨hw.1, hεV hw.2⟩⟩
  · intro EOx hEOx hEOxc x hx hxP
    have heq : EqOn EOx EO Hbar :=
      (hEOx.trans hOE.symm).of_subset_closure hEOxc hOEc QuantumZipper.H_subset_Hbar
        (by rw [QuantumZipper.CA.Car.closure_H_eq_Hbar])
    rw [heq (real_mem_Hbar x)] at hxP ⊢
    have hxL : x < chartAL WC q := by rw [← hvL]; exact hx
    have hpm := hE₀m (hFm (real_mem_Hbar x))
    have hψx : ψ ω (EO x) = extendFrom H (fwdMapInv WC q) (x : ℂ) :=
      jordan_comp_extInf hJ hE₀ hE₀c hE₀m (hFm (real_mem_Hbar x))
    have halC : ψ ω (EO x) ∉ closure (fwdHull WC q) := by
      rw [hψx]; exact alive_of_not_mem_Icc hηC hWC hWC0 q.coe_nonneg (Or.inl hxL)
    obtain ⟨him, hgt⟩ := landL_re_gt hηC hWC hWC0 hq0' (hvL0.trans hvR0) hxL
    have hbC : (extendFrom H (fwdMapInv WC q) (chartAL WC q : ℂ)).re ≤ 0 :=
      R6Fd.re_landL_le hηC hWC hWC0 hq0' (x := 0) (by
        simpa using ConformalImageFull.zero_mem_closure_fwdHull hWC hWC0 hq0')
    have hpC : EO x ∉ cfPocket (R ω) (L ω) r := fun h => by
      have h1 := (hψc ω hω).2.mapsTo h
      rw [hψx] at h1
      have h2 : (0 : ℝ) < (extendFrom H (fwdMapInv WC q) (x : ℂ)).im := h1
      rw [him] at h2
      exact lt_irrefl _ h2
    have hpfrC : EO x ∈ frontier (cfPocket (R ω) (L ω) r) := ⟨hpm, by rw [(hCo ω hω).interior_eq]; exact hpC⟩
    obtain ⟨θ, hθ, hpθ⟩ := frontier_neg_right_arcInf hcf.conf hcf.seed hcf.oriented (hψ ω hω) hpfrC
      (by rw [hψx]; linarith)
    obtain ⟨-, hvC, -, -, -, -, -, -⟩ := hcf.conf.changeCorner_props
    have hθC : θ ∈ Ioc (0 : ℝ) 1 := ⟨hθ.1, hθ.2.le.trans hvC.2⟩
    have hpV : EO x ∉ cfPocket (R ω) (Lv ω) r' := fun h => hpC (hsub h)
    have hpfrV : EO x ∈ frontier (cfPocket (R ω) (Lv ω) r') :=
      ⟨hxP, by rw [(hCo' ω hω').interior_eq]; exact hpV⟩
    have himV : (ψ' ω (EO x)).im = 0 := hJ'.2.2.2.2.1 _ hpfrV
    rcases lt_trichotomy (ψ' ω (EO x)).re 0 with hneg | hzero | hpos
    · obtain ⟨θ', hθ', hpθ'⟩ := frontier_neg_right_arcInf hcf'.conf hcf'.seed hcf'.oriented (hψ' ω hω') hpfrV hneg
      obtain ⟨-, hNC2⟩ := R6Fd.nonCorner_of_right_openInf hcf.conf hcf'.conf hcf'.seed hθ'
      rw [← hpθ'] at hNC2
      obtain ⟨εy, hεy, hεyU⟩ := inter_ball_subset_of_noncornerInf hJ (hCo' ω hω') hsub hxP hpm hNC2
      exact ⟨εy, hεy, fun w hw => hid ⟨hw.1, hεyU ⟨hOsubC hw.1, hw.2⟩⟩⟩
    · exfalso
      have h0 : ψ' ω (EO x) = 0 := Complex.ext hzero himV
      obtain ⟨ρ, hρ, hρC⟩ := exists_ball_subset_of_aliveInf hJ hpm halC
      have hball : cfPocket (R ω) (Lv ω) r' ∩ ball (EO x) ρ ⊆
          cfPocket (R ω) (Lv ω) r' ∩ ψ' ω ⁻¹' (H \ fwdHull WU qT) := fun w hw => by
        have hwO : w ∈ ((curChartInf A R L r η ψ n q ω).dom : Set ℂ) := by
          rw [hOdom]; exact hρC ⟨hsub hw.1, hw.2⟩
        have h1 := hid ⟨hwO, hw.1⟩
        rwa [hI₀dom] at h1
      have hnot := notMem_closure_of_ball_subsetInf hJ' (QuantumZipper.fwdHull_mono.2 _) hxP hρ hball
      rw [h0] at hnot
      exact hnot (ConformalImageFull.zero_mem_closure_fwdHull hWU hWU0 hqTpos)
    · exfalso
      obtain ⟨θ'', hθ'', hpθ''⟩ := frontier_pos_left_arcInf hcf'.conf hcf'.seed hcf'.oriented (hψ' ω hω') hpfrV hpos
      obtain ⟨-, -, -, -, hb, -, -, -⟩ := hcf'.conf.changeCorner_props
      have hθ''I : θ'' ∈ Ioc (0 : ℝ) 1 := ⟨hθ''.1, hθ''.2.le.trans hb.2⟩
      have hgap := (hcf'.conf.changeCorners).2.2.2.1.2.2.2 θ''
        (by rw [hcf'.conf.leftLo_eq_zero_of_rightLo_eq_zero hcf'.seed]; exact hθ'')
      have h1 : cfPt (WangWu.toDisc (Lemma71I.realPath (R ω)) θ) =
          cfPt (WangWu.toDisc (Lemma71I.realPath (Lv ω)) θ'') := hpθ.symm.trans hpθ''
      have h2 := injOn_cfPt (R6Fd.toDisc_ne_neg_one hcf.conf.right hθC)
        (R6Fd.toDisc_ne_neg_one hcf'.conf.left hθ''I) h1
      exact hgap ⟨⟨hθ''I.1.le, hθ''I.2⟩, θ, ⟨hθC.1.le, hθC.2⟩, h2⟩
  · exact hdrv_of_later (O := curChartInf A R L r η ψ n q ω) (I₀ := curChartInf A' R Lv r' η ψ' n' qT.toNNReal ω)
      hWC hWC0 hWU hWU0 q.coe_nonneg hqT0 hOfwd hOdom hI₀fwd hI₀dom hsub hI₀O (hψc' ω hω')
      (hlater_twoInfInf (n := n) (n' := n') hcfg hψ hcfg' hψ' hω hω' hrev hq hsub hT0 htip hqt₁' ht₁ hqTt'
        (fun q₂ hq₂ => (hCf q₂ hq₂).2.1) (fun q₂ hq₂ => (hUf q₂ hq₂).2.1))

end TwoInfInf

section FinalInfInf

open MeasureTheory ProbabilityTheory
open LQGMetric (DistOn)
open QuantumZipper (chiC)
open scoped Real
open WholeField R7Outer R7Leaves R6Nest R6Rel R6Cert PocketMarks PocketSeedOpen PocketStopWallsFin PocketStopSide

universe u

/-- **Local agreement for the shape `TwoInfInf`, PROVED** (reverse visits of `M_L` through Prop. 4.11 and Lemma 4.7; no
Aux. lemma 136): on the source binders of `R6Lw.R6PhysicalIntervalTwoInfInfRemaining`, almost surely on the shape event,
the actual outer chart `C` at `q`, the actual inner chart of `V` at `c_V(T)` (LANDING's `I t`), the current tip and
the actual outer left mark satisfy `TwoLocalAgreement` — in particular `PhysicalIncidentInterval`'s `tip_local`,
`shared_local` (for every `x < v` landing in `P`, any interval), `inclusion` and `joint_access`. -/
theorem localAgreementTwoInfInf {k rL rR c c' : ℝ} (h411 : Sec5.Cond44Ref.Prop411QStatement.{u})
    (h47 : Sec5.Prop411Q.Lemma47QHitStatement.{u})
    (h47T : ∀ θ : ℝ, -(π / 2) < θ → θ < π / 2 → Sec5.RestartGen.Lemma47QHitTStatement.{u} θ)
    (hk4 : 4 < k) (hc : 0 ≤ c) (hc' : 0 ≤ c') :
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
          TwoLocalAgreement (R6Two.currentChartInf A R L r η ψ n (StripSys.rt q) ω)
            ((fun q' : ℝ => R6Two.currentChartInf A' R ML (StripSys.rt s) η ψ' n' q'.toNNReal ω)
              (innerRelCapInf R ML (StripSys.rt s) η ψ' (outerFibreEndInf R L r η ψ (StripSys.rt q) ω) ω))
            (cfPocket (R ω) (ML ω) (StripSys.rt s))
            (closure (cfPocket (R ω) (ML ω) (StripSys.rt s)))
            (η ω (outerFibreEndInf R L r η ψ (StripSys.rt q) ω))
            (R6Tn.leftSeed (travAllInf R L r η ψ) (StripSys.rt q) ω) := by
  intro _ _ Ω _ _ P _ h W' ζ' αR βR βL αL ζαR ζβR ζβL ζαL hcfg R L η hV MR ML hMR hML r A A' ψ ψ' n n' s q hA
    hA'
  filter_upwards [ae_rev_ML h411 h47 h47T hk4 hc hc' hcfg hV hML] with ω hrev hωA hωA' hωN
  obtain ⟨hq0, hqlive, -, hsub, u, hu0, hcap, hrel, -⟩ := hωN
  have hcfO := (hA ω hωA).1
  have hγ : IsDrivenCurve (travAllInf R L r η ψ ω) := (hcfO.props (hA ω hωA).2).1
  have hrtq : ((StripSys.rt q : ℝ≥0) : ℝ) = q := Real.coe_toNNReal _ (by exact_mod_cast hq0.le)
  have hinv : capInv (travAllInf R L r η ψ ω) ((StripSys.rt q : ℝ≥0) : ℝ) = u := by
    rw [hrtq, ← hcap]
    exact hγ.capInv_eq hu0
  have htip : η ω (outerFibreEndInf R L r η ψ (StripSys.rt q) ω) ∈ cfPocket (R ω) (ML ω) (StripSys.rt s) := by
    unfold outerFibreEndInf
    rw [hinv]
    exact hrel
  have hT0 : 0 ≤ outerFibreEndInf R L r η ψ (StripSys.rt q) ω :=
    outerFibreEndInf_nonneg (fun ω hω => (hA ω hω).1) hωA
  have hq0' : 0 < StripSys.rt q := by
    show 0 < (q : ℝ).toNNReal
    exact Real.toNNReal_pos.2 (by exact_mod_cast hq0)
  exact two_localInfInf (n := n) (n' := n') (fun ω hω => (hA ω hω).1) (fun ω hω => (hA ω hω).2)
    (fun ω hω => (hA' ω hω).1) (fun ω hω => (hA' ω hω).2) hωA hωA' hrev hq0' hqlive hsub hT0 htip

end FinalInfInf

end InteractingSLE.Sec7.R6Cor
