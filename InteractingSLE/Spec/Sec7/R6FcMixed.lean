/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.R6FcCore
import InteractingSLE.Spec.Sec7.R6FcLocal
import InteractingSLE.Spec.Sec7.R5PhaseVisit
import InteractingSLE.Spec.Sec7.PocketSideInPatchClock
import InteractingSLE.Spec.Supplement.Q3ChainMeas

/-!
# R.6's face for the bounded mixed shape at a non-corner landing

Packet PROVE-R6-FACE2. One realization: the bounded outer pocket `C = cfPocket R L r` (`IsOuterCfg`, Jordan coordinate
`ψ`) at a live relative capacity `q > 0`, with fibre end `T = T_C(q)`; the contained bounded pocket
`U = cfPocket R' L' r' ⊆ C` (`IsCfPocketConfig`, Jordan coordinate `ψ'`) holding the tip `η(T)`. Let
`p_F = E_O(v)` be the physical landing of the outer current chart at a real coordinate `v`.

`face_package`: if `p_F` is a **non-corner point of `U`'s boundary on `∂C`** (`p_F ∈ ∂U`, `p_F ∉ closure (∂U ∩ C)`,
`p_F` not `U`'s outgoing corner), then for every inner time `q'` in a right neighbourhood of `c_U(T)` (with the
inclusion of the current domains) all the hypotheses of `R6FcCore.r6FaceR_right`/`_left` at `v` hold:
* the outer and inner inverse extensions `E_O = E₀ ∘ F̄_q`, `E_I = E₀' ∘ F̄'_{q'}` (`chart_facts`);
* the signs of the four centred seed coordinates (the tips at `q` and at `c_U(T)` are interior points; continuity in
  time of the inner force points);
* the **local inclusion** `D_C(q) ∩ B(p_F, ε) ⊆ D_U(q')`: `C ∩ B(p_F, ε) ⊆ U` (`inter_ball_subset_of_noncorner`),
  `D_C(q)` misses the physical hull at `T` (`HOuter.relDomain_subset_domain`), `U`'s chart at the visit time `T` has
  domain `U ∖ K_T` (`R5Phase.visitCap_spec`), and the inner increment stays near the tip `η(T) ≠ p_F`
  (`mem_of_increment`, tip by `PocketStopSide.capTrace_relCap_of_visit`);
* the bound of the inner coordinate near `p_F` and the **dead/alive dichotomy** (`alive_iff` and the hull image
  interval `[a_L, a_R]` in both charts).

Deterministic.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Filter Topology Metric
open QuantumZipper (H Hbar fwdMap fwdMapInv fwdHull)
open scoped NNReal ENNReal

namespace InteractingSLE.Sec7.R6Fc

open Sec6 PocketTraversal Lemma71C PocketJordan PocketCoord PocketCoupling PocketStop PocketStopField HOuter
  PocketWordAssembly R6Safe
open WangWu (chartAL chartAR)
open SupercriticalConformalCovariance (IsConformalBijection)

variable {Ω : Type*}

/-- The current chart of the change pocket of `(R, L)` at `r`, at relative capacity `q`. -/
abbrev curChart (A : Set Ω) (R L : Ω → ℝ≥0 → ℂ) (r : ℝ≥0) (η : Ω → ℝ → ℂ) (ψ : Ω → ℂ → ℂ) (n : Ω → ℤ)
    (q : ℝ≥0) (ω : Ω) : Chart :=
  relChart (fun ω => shiftChart (pChart A (fun ω => cfPocket (R ω) (L ω) r) ψ ω) (n ω)) (travAll R L r η ψ) q ω

/-- The centred right seed coordinate of the traversal at relative capacity `q`. -/
abbrev seedR (R L : Ω → ℝ≥0 → ℂ) (r : ℝ≥0) (η : Ω → ℝ → ℂ) (ψ : Ω → ℂ → ℂ) (q : ℝ≥0) (ω : Ω) : ℝ :=
  geomRW (fun t ω => segDriver (travAll R L r η ψ ω) t) (fun _ => LP.twoSeedXR) 0 q ω -
    segDriver (travAll R L r η ψ ω) q

/-- The centred left seed coordinate of the traversal at relative capacity `q`. -/
abbrev seedL (R L : Ω → ℝ≥0 → ℂ) (r : ℝ≥0) (η : Ω → ℝ → ℂ) (ψ : Ω → ℂ → ℂ) (q : ℝ≥0) (ω : Ω) : ℝ :=
  geomLW (fun t ω => segDriver (travAll R L r η ψ ω) t) (fun _ => LP.twoSeedXL) 0 q ω -
    segDriver (travAll R L r η ψ ω) q

theorem seedR_eq {γ : Ω → ℝ → ℂ} {ω : Ω} {W : ℝ → ℝ} (hW : Continuous W) {q : ℝ≥0}
    (h : ∀ r ∈ Icc (0 : ℝ) q, segDriver (γ ω) r.toNNReal = W r) :
    geomRW (fun t ω => segDriver (γ ω) t) (fun _ => LP.twoSeedXR) 0 q ω - segDriver (γ ω) q = chartAR W q := by
  rw [← Supp8.Q3Chain.chartAR_eq_of_eqOn hW q.coe_nonneg h]
  simp only [geomRW, chartAR, LP.twoSeedXR, Real.toNNReal_coe]
  rfl

theorem seedL_eq {γ : Ω → ℝ → ℂ} {ω : Ω} {W : ℝ → ℝ} (hW : Continuous W) {q : ℝ≥0}
    (h : ∀ r ∈ Icc (0 : ℝ) q, segDriver (γ ω) r.toNNReal = W r) :
    geomLW (fun t ω => segDriver (γ ω) t) (fun _ => LP.twoSeedXL) 0 q ω - segDriver (γ ω) q = chartAL W q := by
  rw [← Supp8.Q3Chain.chartAL_eq_of_eqOn hW q.coe_nonneg h]
  simp only [geomLW, chartAL, LP.twoSeedXL, Real.toNNReal_coe, neg_zero]
  rfl

/-- **The face package** for the bounded mixed shape at a non-corner landing (see the module docstring). -/
theorem face_package {A A' : Set Ω} {R L R' L' : Ω → ℝ≥0 → ℂ} {r r' : ℝ≥0} {W : Ω → ℝ → ℝ}
    {η : Ω → ℝ → ℂ} {ψ ψ' : Ω → ℂ → ℂ} {n n' : Ω → ℤ} {ω : Ω}
    (hcfg : ∀ ω ∈ A, IsOuterCfg (R ω) (L ω) r (W ω) (η ω)) (hψ : ∀ ω ∈ A, IsCfJordan (R ω) (L ω) r (ψ ω))
    (hcfg' : ∀ ω ∈ A', IsCfPocketConfig (R' ω) (L' ω) r' (W ω) (η ω))
    (hψ' : ∀ ω ∈ A', IsCfJordan (R' ω) (L' ω) r' (ψ' ω)) (hω : ω ∈ A) (hω' : ω ∈ A')
    {q : ℝ≥0} (hq0 : 0 < q) (hq : (q : ℝ≥0∞) < capLife (travAll R L r η ψ ω))
    (hsub : cfPocket (R' ω) (L' ω) r' ⊆ cfPocket (R ω) (L ω) r)
    (hT0 : 0 ≤ outerFibreEnd R L r η ψ q ω)
    (htip : η ω (outerFibreEnd R L r η ψ q ω) ∈ cfPocket (R' ω) (L' ω) r') {v : ℝ}
    (hgen : extendFrom H (curChart A R L r η ψ n q ω).2.1 v ∈ frontier (cfPocket (R' ω) (L' ω) r') ∧
      extendFrom H (curChart A R L r η ψ n q ω).2.1 v ∉
        closure (frontier (cfPocket (R' ω) (L' ω) r') ∩ cfPocket (R ω) (L ω) r) ∧
      extendFrom H (curChart A R L r η ψ n q ω).2.1 v ≠ cfPt (openPt (R' ω) (L' ω) r')) :
    ∃ εW > 0, ∀ q' : ℝ≥0, innerRelCap R' L' r' η ψ' (outerFibreEnd R L r η ψ q ω) ω < q' →
      (q' : ℝ) < innerRelCap R' L' r' η ψ' (outerFibreEnd R L r η ψ q ω) ω + εW →
      ((curChart A' R' L' r' η ψ' n' q' ω).dom : Set ℂ) ⊆ (curChart A R L r η ψ n q ω).dom →
      (curChart A R L r η ψ n q ω).IsConformal ∧ (curChart A' R' L' r' η ψ' n' q' ω).IsConformal ∧
      ∃ EO EI : ℂ → ℂ, EqOn EO (curChart A R L r η ψ n q ω).2.1 H ∧ ContinuousOn EO Hbar ∧
        EqOn EI (curChart A' R' L' r' η ψ' n' q' ω).2.1 H ∧ ContinuousOn EI Hbar ∧
        seedL R L r η ψ q ω < 0 ∧ 0 < seedR R L r η ψ q ω ∧
        seedL R' L' r' η ψ' q' ω < 0 ∧ 0 < seedR R' L' r' η ψ' q' ω ∧
        ∃ ε > 0, ((curChart A R L r η ψ n q ω).dom : Set ℂ) ∩ ball (EO v) ε ⊆
            (curChart A' R' L' r' η ψ' n' q' ω).dom ∧
          (∃ M : ℝ, ∀ w ∈ ((curChart A' R' L' r' η ψ' n' q' ω).dom : Set ℂ) ∩ ball (EO v) ε,
            ‖(curChart A' R' L' r' η ψ' n' q' ω).1 w‖ ≤ M) ∧
          (∀ ξ : ℝ, ξ ∈ Icc (seedL R L r η ψ q ω) (seedR R L r η ψ q ω) → EO ξ ∈ ball (EO v) (ε / 2) →
            ∀ x : ℝ, EI x = EO ξ → x ∈ Icc (seedL R' L' r' η ψ' q' ω) (seedR R' L' r' η ψ' q' ω)) ∧
          (∀ y : ℝ, y ∉ Icc (seedL R L r η ψ q ω) (seedR R L r η ψ q ω) → EO y ∈ ball (EO v) (ε / 2) →
            ∀ x : ℝ, EI x = EO y → x ∉ Icc (seedL R' L' r' η ψ' q' ω) (seedR R' L' r' η ψ' q' ω)) := by
  classical
  -- the outer pocket
  have hcf := hcfg ω hω
  have hG : ∀ ω ∈ A, IsChangeConfigInc (R ω) (L ω) r := fun ω hω => (hcfg ω hω).conf
  have hCo : ∀ ω ∈ A, IsOpen (cfPocket (R ω) (L ω) r) := fun ω hω =>
    isOpen_image_negInv' (hG ω hω).isOpen_changePocket (hG ω hω).changePocket_subset_H
  have hCH : ∀ ω ∈ A, cfPocket (R ω) (L ω) r ⊆ H := fun ω hω =>
    PocketJordan.image_negInv_subset_H (hG ω hω).changePocket_subset_H
  have hψc : ∀ ω ∈ A, IsConformalBijection (ψ ω) (cfPocket (R ω) (L ω) r) H := fun ω hω => (hψ ω hω).2.2.2.1
  have hCb : Bornology.IsBounded (cfPocket (R ω) (L ω) r) :=
    isBounded_image_negInv (PocketMarks.zero_notMem_closure_of_rightLo_pos hcf.conf hcf.bounded)
  have hx₀ : cfPt (openPt (R ω) (L ω) r) ∉ cfPocket (R ω) (L ω) r := hcf.conf.cfPt_openPt_notMem
  have hJ : Sec6.IsJordanCoord (cfPocket (R ω) (L ω) r) (cfPt (openPt (R ω) (L ω) r))
      (cfPt (closePt (R ω) (L ω) r)) (ψ ω) := hψ ω hω
  have hγ : IsDrivenCurve (travAll R L r η ψ ω) := (hcf.props (hψ ω hω)).1
  obtain ⟨t₁, hqt₁, ht₁⟩ := ENNReal.lt_iff_exists_nnreal_btwn.1 hq
  have hqt₁' : q < t₁ := by exact_mod_cast hqt₁
  obtain ⟨E₀, hE₀, hE₀c, hE₀m, WC, hWC, hWC0, hWCeq, ηC, hηC, hηCeq, hCf⟩ :=
    chart_facts (n := n) hCo hCH hψc hCb hx₀ hJ hω hγ ht₁
  obtain ⟨hOc, hOdom, -, hOE, hOEc⟩ := hCf q hqt₁'
  have hq0' : (0 : ℝ) < q := by exact_mod_cast hq0
  have hWCq : ∀ s ∈ Icc (0 : ℝ) q, segDriver (travAll R L r η ψ ω) s.toNNReal = WC s := fun s hs =>
    hWCeq s ⟨hs.1, hs.2.trans (by exact_mod_cast hqt₁'.le)⟩
  have hvR : seedR R L r η ψ q ω = chartAR WC q := seedR_eq hWC hWCq
  have hvL : seedL R L r η ψ q ω = chartAL WC q := seedL_eq hWC hWCq
  obtain ⟨hFc, hFeq, hFm⟩ := extendFrom_props hηC hWC hWC0 q.coe_nonneg
  -- the outer tip
  have hTC : η ω (outerFibreEnd R L r η ψ q ω) ∈ cfPocket (R ω) (L ω) r := hsub htip
  have htrace : capTrace (travAll R L r η ψ ω) q = ψ ω (η ω (outerFibreEnd R L r η ψ q ω)) := rfl
  have h0cl : ((0 : ℝ) : ℂ) ∈ closure H := by
    rw [QuantumZipper.CA.Car.closure_H_eq_Hbar]; exact real_mem_Hbar 0
  have htipC : extendFrom H (fwdMapInv WC q) ((0 : ℝ) : ℂ) ∈ H := by
    have h1 := hηC.tendsto_fwdMapInv_tip hWC hWC0 q.coe_nonneg
    rw [← Complex.ofReal_zero] at h1
    rw [extendFrom_eq h0cl h1, hηCeq q q.coe_nonneg (by exact_mod_cast hqt₁'.le)]
    change capTrace (travAll R L r η ψ ω) q ∈ H
    rw [htrace]
    exact (hψc ω hω).2.mapsTo hTC
  have hvR0 : 0 < chartAR WC q := chartAR_pos_of_tip hηC hWC hWC0 q.coe_nonneg htipC
  have hvL0 : chartAL WC q < 0 := chartAL_neg_of_tip hηC hWC hWC0 q.coe_nonneg htipC
  -- the inner pocket
  have hcf' := hcfg' ω hω'
  have hG' : ∀ ω ∈ A', IsChangeConfigInc (R' ω) (L' ω) r' := fun ω hω => (hcfg' ω hω).conf
  have hCo' : ∀ ω ∈ A', IsOpen (cfPocket (R' ω) (L' ω) r') := fun ω hω =>
    isOpen_image_negInv' (hG' ω hω).isOpen_changePocket (hG' ω hω).changePocket_subset_H
  have hCH' : ∀ ω ∈ A', cfPocket (R' ω) (L' ω) r' ⊆ H := fun ω hω =>
    PocketJordan.image_negInv_subset_H (hG' ω hω).changePocket_subset_H
  have hψc' : ∀ ω ∈ A', IsConformalBijection (ψ' ω) (cfPocket (R' ω) (L' ω) r') H := fun ω hω =>
    (hψ' ω hω).2.2.2.1
  have hUb : Bornology.IsBounded (cfPocket (R' ω) (L' ω) r') :=
    isBounded_image_negInv (PocketMarks.zero_notMem_closure_of_rightLo_pos hcf'.conf hcf'.bounded)
  have hx₀' : cfPt (openPt (R' ω) (L' ω) r') ∉ cfPocket (R' ω) (L' ω) r' := hcf'.conf.cfPt_openPt_notMem
  have hJ' : Sec6.IsJordanCoord (cfPocket (R' ω) (L' ω) r') (cfPt (openPt (R' ω) (L' ω) r'))
      (cfPt (closePt (R' ω) (L' ω) r')) (ψ' ω) := hψ' ω hω'
  have hγ' : IsDrivenCurve (travAll R' L' r' η ψ' ω) := (hcf'.isDrivenCurve (hψ' ω hω')).1
  obtain ⟨hc', hdom', hfwd'⟩ := R5Phase.shiftChart_dom_facts hCo' hCH' hψc' n' ω hω'
  obtain ⟨hqTpos, hqTlive, hqTdom⟩ := R5Phase.visitCap_spec
    (c := fun ω => shiftChart (pChart A' (fun ω => cfPocket (R' ω) (L' ω) r') ψ' ω) (n' ω)) hω' hcf' (hψ' ω hω')
    hc' hdom' hfwd' hT0 htip
  set qT := R5Phase.visitCap R' L' r' η ψ' ω (outerFibreEnd R L r η ψ q ω) with hqTdef
  have hqT0 : (0 : ℝ) ≤ qT := hqTpos.le
  have hqTc : ((qT.toNNReal : ℝ≥0) : ℝ) = qT := Real.coe_toNNReal _ hqT0
  obtain ⟨t₁', hqTt₁', ht₁'⟩ := ENNReal.lt_iff_exists_nnreal_btwn.1 hqTlive
  have hqTt : qT.toNNReal < t₁' := by exact_mod_cast hqTt₁'
  have hqTt' : qT < t₁' := by rw [← hqTc]; exact_mod_cast hqTt
  obtain ⟨E₀', hE₀', hE₀'c, hE₀'m, WU, hWU, hWU0, hWUeq, ηU, hηU, hηUeq, hUf⟩ :=
    chart_facts (n := n') hCo' hCH' hψc' hUb hx₀' hJ' hω' hγ' ht₁'
  obtain ⟨-, hITdom, -, -, -⟩ := hUf qT.toNNReal hqTt
  rw [hqTc] at hITdom
  -- the inner tip at the visit time
  obtain ⟨hP', hJ'arc⟩ := R5Ref.pocket_of_cfg hcf' (hψ' ω hω')
  have hvisit : outerFibreEnd R L r η ψ q ω ∈ visitSet (η ω) (cfPocket (R' ω) (L' ω) r')
      (firstHit (η ω) (cfArcR (R' ω) (L' ω) r' 1)) (firstHit (η ω) (cfArcR (R' ω) (L' ω) r' 0)) :=
    ⟨hP'.mem_Ioo_of_mem hT0 htip, htip⟩
  have htrU : capTrace (travAll R' L' r' η ψ' ω) qT.toNNReal = ψ' ω (η ω (outerFibreEnd R L r η ψ q ω)) :=
    PocketStopSide.capTrace_relCap_of_visit hP' hcf'.attach hJ'arc hvisit
  have hψ'T : ψ' ω (η ω (outerFibreEnd R L r η ψ q ω)) ∈ H := (hψc' ω hω').2.mapsTo htip
  have htipU : extendFrom H (fwdMapInv WU qT) ((0 : ℝ) : ℂ) = ψ' ω (η ω (outerFibreEnd R L r η ψ q ω)) := by
    have h1 := hηU.tendsto_fwdMapInv_tip hWU hWU0 hqT0
    rw [← Complex.ofReal_zero] at h1
    rw [extendFrom_eq h0cl h1, hηUeq qT hqT0 hqTt'.le, ← htrU]
    simp only [capTrace, hqTc]
  have hwR0 : 0 < chartAR WU qT := chartAR_pos_of_tip hηU hWU hWU0 hqT0 (htipU ▸ hψ'T)
  have hwL0 : chartAL WU qT < 0 := chartAL_neg_of_tip hηU hWU hWU0 hqT0 (htipU ▸ hψ'T)
  obtain ⟨hFTc, hFTeq, hFTm⟩ := extendFrom_props hηU hWU hWU0 hqT0
  set ET : ℂ → ℂ := fun z => E₀' (extendFrom H (fwdMapInv WU qT) z) with hETdef
  have hETc : ContinuousOn ET Hbar := hE₀'c.comp hFTc hFTm
  have hET0 : ET ((0 : ℝ) : ℂ) = η ω (outerFibreEnd R L r η ψ q ω) := by
    simp only [hETdef, htipU]
    rw [hE₀' hψ'T]
    exact (hψc' ω hω').2.injOn.leftInvOn_invFunOn htip
  -- continuity in time of the inner force coordinates
  have hARc : ContinuousAt (fun t => chartAR WU t) qT := by
    have h1 := (MartChar.RealFlow.continuousOn_rightImg hWU 0).continuousAt (Ici_mem_nhds hqTpos)
    exact h1.sub hWU.continuousAt
  have hALc : ContinuousAt (fun t => chartAL WU t) qT := by
    have h1 := (MartChar.RealFlow.continuousOn_rightImg hWU.neg 0).continuousAt (Ici_mem_nhds hqTpos)
    exact h1.neg.sub hWU.continuousAt
  obtain ⟨θa, hθa, hθaR⟩ := Metric.continuousAt_iff.1 hARc (chartAR WU qT) hwR0
  obtain ⟨θb, hθb, hθbL⟩ := Metric.continuousAt_iff.1 hALc (-chartAL WU qT) (by linarith)
  -- the landing
  set pF := extendFrom H (curChart A R L r η ψ n q ω).2.1 v with hpFdef
  set EO : ℂ → ℂ := fun z => E₀ (extendFrom H (fwdMapInv WC q) z) with hEOdef
  have hvcl : (v : ℂ) ∈ closure H := by rw [QuantumZipper.CA.Car.closure_H_eq_Hbar]; exact real_mem_Hbar v
  have hEOv : EO v = pF := (extendFrom_eq hvcl (tendsto_of_extension hOE hOEc v)).symm
  have hpFC : pF ∈ closure (cfPocket (R ω) (L ω) r) \ {cfPt (openPt (R ω) (L ω) r)} :=
    hEOv ▸ hE₀m (hFm (real_mem_Hbar v))
  have hpFne : pF ≠ η ω (outerFibreEnd R L r η ψ q ω) := fun h =>
    hgen.1.2 (by rw [h, (hCo' ω hω').interior_eq]; exact htip)
  set d := dist pF (η ω (outerFibreEnd R L r η ψ q ω)) with hd
  have hdpos : 0 < d := dist_pos.2 hpFne
  obtain ⟨ρ₀, hρ₀, hρ₀ET⟩ := Metric.continuousWithinAt_iff.1 (hETc _ (real_mem_Hbar 0)) (d / 2) (half_pos hdpos)
  have hB : ∀ z ∈ H, ‖z‖ ≤ ρ₀ / 2 →
      E₀' (fwdMapInv WU qT z) ∈ ball (η ω (outerFibreEnd R L r η ψ q ω)) (d / 2) := by
    intro z hz hzn
    have hzd : dist z ((0 : ℝ) : ℂ) < ρ₀ := by
      rw [Complex.ofReal_zero, dist_zero_right]; linarith
    have h := hρ₀ET (QuantumZipper.H_subset_Hbar hz) hzd
    rw [hET0] at h
    have hEz : ET z = E₀' (fwdMapInv WU qT z) := by simp only [hETdef, hFTeq hz]
    rw [hEz] at h
    exact h
  obtain ⟨θ₁, hθ₁, hθ₁K⟩ := exists_shift_hull_small hWU qT hρ₀
  set εW := min (min θ₁ (min θa θb)) (t₁' - qT) with hεWdef
  have hεW : 0 < εW := lt_min (lt_min hθ₁ (lt_min hθa hθb)) (by linarith)
  refine ⟨εW, hεW, fun q' hq'lo hq'hi hIncl => ?_⟩
  have hq'lo' : qT < q' := hq'lo
  have hq'hi' : (q' : ℝ) < qT + εW := hq'hi
  have hq't : q' < t₁' := by
    have : (q' : ℝ) < t₁' := by linarith [min_le_right (min θ₁ (min θa θb)) (t₁' - qT)]
    exact_mod_cast this
  have hq'pos : (0 : ℝ) < q' := hqTpos.trans hq'lo'
  obtain ⟨hIc, hIdom, -, hIE, hIEc⟩ := hUf q' hq't
  have hWUq : ∀ s ∈ Icc (0 : ℝ) q', segDriver (travAll R' L' r' η ψ' ω) s.toNNReal = WU s := fun s hs =>
    hWUeq s ⟨hs.1, hs.2.trans (by exact_mod_cast hq't.le)⟩
  have hwR : seedR R' L' r' η ψ' q' ω = chartAR WU q' := seedR_eq hWU hWUq
  have hwL : seedL R' L' r' η ψ' q' ω = chartAL WU q' := seedL_eq hWU hWUq
  have hdq : dist (q' : ℝ) qT < min θa θb := by
    rw [Real.dist_eq, abs_of_pos (by linarith)]
    linarith [min_le_left (min θ₁ (min θa θb)) (t₁' - qT), min_le_right θ₁ (min θa θb)]
  have hwR0' : 0 < chartAR WU q' := by
    have h := hθaR (hdq.trans_le (min_le_left _ _))
    rw [Real.dist_eq, abs_sub_lt_iff] at h
    linarith [h.2]
  have hwL0' : chartAL WU q' < 0 := by
    have h := hθbL (hdq.trans_le (min_le_right _ _))
    rw [Real.dist_eq, abs_sub_lt_iff] at h
    linarith [h.1]
  obtain ⟨hF'c, hF'eq, hF'm⟩ := extendFrom_props hηU hWU hWU0 q'.coe_nonneg
  set EI : ℂ → ℂ := fun z => E₀' (extendFrom H (fwdMapInv WU q') z) with hEIdef
  -- local containment and the radius
  obtain ⟨εa, hεa, hΛa⟩ := inter_ball_subset_of_noncorner hJ hCb hx₀ (hCo' ω hω') hsub
    (frontier_subset_closure hgen.1) hpFC.1 hpFC.2 hgen.2.1
  have hpFU : pF ∈ closure (cfPocket (R' ω) (L' ω) r') \ {cfPt (openPt (R' ω) (L' ω) r')} :=
    ⟨frontier_subset_closure hgen.1, hgen.2.2⟩
  obtain ⟨ε₂, hε₂, hε₂ψ⟩ := Metric.continuousWithinAt_iff.1 (hJ'.1 pF hpFU) 1 one_pos
  set ε := min (min εa (d / 2)) ε₂ with hεdef
  have hε : 0 < ε := lt_min (lt_min hεa (half_pos hdpos)) hε₂
  have hεa' : ε ≤ εa := (min_le_left _ _).trans (min_le_left _ _)
  have hεd : ε ≤ d / 2 := (min_le_left _ _).trans (min_le_right _ _)
  have hε2 : ε ≤ ε₂ := min_le_right _ _
  have hΛa' : cfPocket (R ω) (L ω) r ∩ ball pF ε ⊆ cfPocket (R' ω) (L' ω) r' := fun w hw =>
    hΛa ⟨hw.1, ball_subset_ball hεa' hw.2⟩
  -- the local inclusion
  have hΛ : ((curChart A R L r η ψ n q ω).dom : Set ℂ) ∩ ball pF ε ⊆
      (curChart A' R' L' r' η ψ' n' q' ω).dom := by
    rintro w ⟨hwO, hwb⟩
    have hwU : w ∈ cfPocket (R' ω) (L' ω) r' := hΛa' ⟨hOc.dom_subset hwO |> fun _ => (by
      rw [hOdom] at hwO; exact hwO.1), hwb⟩
    have hJarc : IsJordanCoord (cfPocket (R ω) (L ω) r) (cfArcR (R ω) (L ω) r 0) (cfArcR (R ω) (L ω) r 1)
        (ψ ω) := by
      rw [IsChangeConfigInc.cfArcR_zero, IsChangeConfigInc.cfArcR_one]; exact hψ ω hω
    have hzD : w ∈ cfPocket (R ω) (L ω) r ∩
        ψ ω ⁻¹' (H \ fwdHull (fun s : ℝ => segDriver (travAll R L r η ψ ω) s.toNNReal) q) := by
      rw [← relChart_dom_eq_inter (n := n) hCo hCH hψc hω hγ hq]; exact hwO
    have hwphys : w ∈ H \ fwdHull (W ω) (outerFibreEnd R L r η ψ q ω) :=
      relDomain_subset_domain hcf.erase hcf.trace hcf.continuous_W hcf.W_zero (hCH ω hω) hCb hJarc hγ
        q.coe_nonneg (by rw [ENNReal.ofReal_coe_nnreal]; exact hq) hzD
    have hwT : ψ' ω w ∉ fwdHull WU qT := by
      have hmem : w ∈ ((relChart (fun ω => shiftChart (pChart A' (fun ω => cfPocket (R' ω) (L' ω) r') ψ' ω)
          (n' ω)) (travAll R' L' r' η ψ') qT.toNNReal ω).dom : Set ℂ) := by
        rw [hqTdom]; exact ⟨hwU, hwphys⟩
      rw [hITdom] at hmem
      exact hmem.2.2
    have hwB : w ∉ ball (η ω (outerFibreEnd R L r η ψ q ω)) (d / 2) := by
      intro hwB'
      have h1 := mem_ball.1 hwB'
      have h2 : dist w pF < d / 2 := (mem_ball.1 hwb).trans_le hεd
      have h3 := dist_triangle pF w (η ω (outerFibreEnd R L r η ψ q ω))
      rw [dist_comm pF w] at h3
      linarith
    have hm1 : εW ≤ θ₁ := (min_le_left _ _).trans (min_le_left _ _)
    have hsmall : fwdHull (QuantumZipper.RS.shiftDrive WU qT) ((q' : ℝ) - qT) ⊆ closedBall 0 (ρ₀ / 2) :=
      hθ₁K _ (by linarith) (by linarith)
    have hwq := mem_of_increment hE₀' (hψc' ω hω') hWU hWU0 hqT0 hB hq'lo'.le hsmall hwU hwT hwB
    rw [hIdom]
    exact ⟨hwU, (hψc' ω hω').2.mapsTo hwU, hwq⟩
  -- the bound of the inner coordinate near the landing
  have hbdd : ∃ M : ℝ, ∀ w ∈ ((curChart A' R' L' r' η ψ' n' q' ω).dom : Set ℂ) ∩ ball (EO v) ε,
      ‖(curChart A' R' L' r' η ψ' n' q' ω).1 w‖ ≤ M := by
    obtain ⟨Cq, hCq⟩ := exists_norm_fwdMapInv_sub_le hWU hWU0 q'.coe_nonneg
    refine ⟨‖ψ' ω pF‖ + 1 + Cq, fun w hw => ?_⟩
    rw [hEOv] at hw
    have hwI := hw.1
    have hwU : w ∈ cfPocket (R' ω) (L' ω) r' := by rw [hIdom] at hwI; exact hwI.1
    set z := (curChart A' R' L' r' η ψ' n' q' ω).1 w with hz
    have hzH : z ∈ H := hIc.fwd_mem hwI
    have hzw : (curChart A' R' L' r' η ψ' n' q' ω).2.1 z = w := hIc.inv_fwd hwI
    have hψw : ψ' ω w = fwdMapInv WU q' z := by
      rw [← hzw, ← hIE hzH]
      have h := jordan_comp_ext hJ' hE₀' hE₀'c hE₀'m (hF'm (QuantumZipper.H_subset_Hbar hzH))
      rw [h, hF'eq hzH]
    have hwx : w ∈ closure (cfPocket (R' ω) (L' ω) r') \ {cfPt (openPt (R' ω) (L' ω) r')} :=
      ⟨subset_closure hwU, fun h => hx₀' (h ▸ hwU)⟩
    have h1 := hε₂ψ hwx ((mem_ball.1 hw.2).trans_le hε2)
    have h2 := hCq z hzH
    rw [← hψw] at h2
    have h3 : ‖ψ' ω w‖ ≤ ‖ψ' ω pF‖ + 1 := by
      have := norm_le_norm_add_norm_sub' (ψ' ω w) (ψ' ω pF)
      rw [dist_eq_norm] at h1
      linarith
    have h4 : ‖z‖ ≤ ‖ψ' ω w‖ + ‖ψ' ω w - z‖ := by
      have := norm_sub_norm_le z (ψ' ω w)
      rw [norm_sub_rev] at this
      linarith [norm_sub_rev z (ψ' ω w)]
    linarith
  -- aliveness in the two charts near the landing
  have hKH : fwdHull WC q ⊆ H := fun z hz => hz.1
  have hK'H : fwdHull WU q' ⊆ H := fun z hz => hz.1
  have hIncl' : cfPocket (R' ω) (L' ω) r' ∩ ψ' ω ⁻¹' (H \ fwdHull WU q') ⊆
      cfPocket (R ω) (L ω) r ∩ ψ ω ⁻¹' (H \ fwdHull WC q) := by
    rw [← hIdom, ← hOdom]; exact hIncl
  have hΛ' : cfPocket (R ω) (L ω) r ∩ ψ ω ⁻¹' (H \ fwdHull WC q) ∩ ball pF ε ⊆
      cfPocket (R' ω) (L' ω) r' ∩ ψ' ω ⁻¹' (H \ fwdHull WU q') := by
    rw [← hIdom, ← hOdom]; exact hΛ
  have halive : ∀ p : ℂ, p ∈ ball pF (ε / 2) →
      p ∈ closure (cfPocket (R ω) (L ω) r) \ {cfPt (openPt (R ω) (L ω) r)} →
      p ∈ closure (cfPocket (R' ω) (L' ω) r') \ {cfPt (openPt (R' ω) (L' ω) r')} →
      (ψ ω p ∉ closure (fwdHull WC q) ↔ ψ' ω p ∉ closure (fwdHull WU q')) := fun p hp hpC hpU =>
    alive_iff hJ hCb hx₀ hJ' hUb hx₀' hsub hKH hK'H hIncl' hΛa' hΛ' hp hpC hpU
  have hlt : chartAL WU q' < chartAR WU q' := hwL0'.trans hwR0'
  refine ⟨hOc, hIc, EO, EI, hOE, hOEc, hIE, hIEc, by rw [hvL]; exact hvL0, by rw [hvR]; exact hvR0,
    by rw [hwL]; exact hwL0', by rw [hwR]; exact hwR0', ε, hε, by rw [hEOv]; exact hΛ, hbdd,
    fun ξ hξ hξb x hx => ?_, fun y hy hyb x hx => ?_⟩
  · rw [hvL, hvR] at hξ
    rw [hwL, hwR]
    by_contra hxI
    have hdeadC := dead_of_mem_Icc hηC hWC hWC0 hq0' (hvL0.trans hvR0) hξ
    have haliveU : extendFrom H (fwdMapInv WU q') (x : ℂ) ∉ closure (fwdHull WU q') := by
      refine alive_of_not_mem_Icc hηU hWU hWU0 q'.coe_nonneg ?_
      simp only [mem_Icc, not_and_or, not_le] at hxI
      exact hxI
    have hpC : EO ξ ∈ closure (cfPocket (R ω) (L ω) r) \ {cfPt (openPt (R ω) (L ω) r)} :=
      hE₀m (hFm (real_mem_Hbar ξ))
    have hpU : EO ξ ∈ closure (cfPocket (R' ω) (L' ω) r') \ {cfPt (openPt (R' ω) (L' ω) r')} :=
      hx ▸ hE₀'m (hF'm (real_mem_Hbar x))
    have hψp : ψ ω (EO ξ) = extendFrom H (fwdMapInv WC q) ξ :=
      jordan_comp_ext hJ hE₀ hE₀c hE₀m (hFm (real_mem_Hbar ξ))
    have hψ'p : ψ' ω (EO ξ) = extendFrom H (fwdMapInv WU q') x := by
      rw [← hx]; exact jordan_comp_ext hJ' hE₀' hE₀'c hE₀'m (hF'm (real_mem_Hbar x))
    rw [hEOv] at hξb
    have h := (halive (EO ξ) hξb hpC hpU).2 (by rw [hψ'p]; exact haliveU)
    exact h (by rw [hψp]; exact hdeadC)
  · rw [hvL, hvR] at hy
    rw [hwL, hwR]
    intro hxI
    have haliveC : extendFrom H (fwdMapInv WC q) (y : ℂ) ∉ closure (fwdHull WC q) := by
      refine alive_of_not_mem_Icc hηC hWC hWC0 q.coe_nonneg ?_
      simp only [mem_Icc, not_and_or, not_le] at hy
      exact hy
    have hdeadU := dead_of_mem_Icc hηU hWU hWU0 hq'pos hlt hxI
    have hpC : EO y ∈ closure (cfPocket (R ω) (L ω) r) \ {cfPt (openPt (R ω) (L ω) r)} :=
      hE₀m (hFm (real_mem_Hbar y))
    have hpU : EO y ∈ closure (cfPocket (R' ω) (L' ω) r') \ {cfPt (openPt (R' ω) (L' ω) r')} :=
      hx ▸ hE₀'m (hF'm (real_mem_Hbar x))
    have hψp : ψ ω (EO y) = extendFrom H (fwdMapInv WC q) y :=
      jordan_comp_ext hJ hE₀ hE₀c hE₀m (hFm (real_mem_Hbar y))
    have hψ'p : ψ' ω (EO y) = extendFrom H (fwdMapInv WU q') x := by
      rw [← hx]; exact jordan_comp_ext hJ' hE₀' hE₀'c hE₀'m (hF'm (real_mem_Hbar x))
    rw [hEOv] at hyb
    have h := (halive (EO y) hyb hpC hpU).1 (by rw [hψp]; exact haliveC)
    exact h (by rw [hψ'p]; exact hdeadU)

end InteractingSLE.Sec7.R6Fc
