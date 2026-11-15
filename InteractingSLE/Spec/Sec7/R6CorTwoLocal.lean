/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.R6CorTwo
import InteractingSLE.Spec.Sec7.R6LwInterval

/-!
# R.6's local agreement for the bounded two-outer shape, without Aux. lemma 136

Packet PROVE-R6-CORNER, second round (LANDING's `R6Lw.PhysicalIncidentInterval`). For the actual outer chart
`O = D_C(q)`, the actual inner chart `I = D_V(c_V(T))` (`T = T_C(q)`), `V = cfPocket R M_L s`, the current tip
`p = η(T)` and the outer left mark `v`:

* `TwoLocalAgreement O I V P p v`: `I.dom ⊆ O.dom`, the identity `O.dom ∩ V ⊆ I.dom`, the tip ball
  (`tip_local`), the shared balls at every landing `E_O(x) ∈ P`, `x < v` (`shared_local`), and joint access;
* `two_local`: the per-sample proof. The identity is `R6Cor.two_identity_at_visit` (Astra's inner-side argument,
  reverse visits of `M_L`); the tip ball is a ball in `V`. At `x < v` the landing `E_O(x)` is alive for `C` and on
  `C`'s open right arc (on `R`); on `∂V` its `V`-coordinate is negative (so it is on `V`'s open right arc, a
  non-corner point, `C ∩ B ⊆ V`): coordinate `0` would make `0 = ψ_V(E_O(x))` alive for `V` (by the identity),
  against `0 ∈ closure K^V`, and a positive coordinate would put an `R`-point on `M_L`'s open arc, against the
  contact gap;
* `physicalIncidentInterval_of_local`: the drop-in for `R6Lw.PhysicalIncidentInterval` (interval, collars,
  landings and the force landing are LANDING's);
* **`localAgreementTwo`**: almost surely on the source event of `R6Lw.R6PhysicalIntervalTwoRemaining`, with
  LANDING's exact charts, tip and mark, from Prop. 4.11 and Lemma 4.7 (`h411`, `h47`, `h47T`).

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
  PocketWordAssembly R6Safe R6Fc
open WangWu (chartAL chartAR)
open SupercriticalConformalCovariance (IsConformalBijection)

/-- **Local agreement of the two current domains** (the fields of `R6Lw.PhysicalIncidentInterval` that Aux. lemma 136
used to give, and more): for the outer chart `O`, the inner chart `I` at the same original time, the inner pocket `V`,
the landing set `P`, the current tip `p` and the outer left seed coordinate `v`. -/
structure TwoLocalAgreement (O I : Chart) (V P : Set ℂ) (p : ℂ) (v : ℝ) : Prop where
  inclusion : (I.dom : Set ℂ) ⊆ O.dom
  identity : (O.dom : Set ℂ) ∩ V ⊆ I.dom
  tip_local : ∃ r > 0, (O.dom : Set ℂ) ∩ ball p r ⊆ I.dom
  shared_local : ∀ EO : ℂ → ℂ, EqOn EO O.2.1 H → ContinuousOn EO Hbar → ∀ x : ℝ, x < v → EO (x : ℂ) ∈ P →
    ∃ r > 0, (O.dom : Set ℂ) ∩ ball (EO (x : ℂ)) r ⊆ I.dom
  joint_access : ∀ ε > 0, ∃ z ∈ (I.dom : Set ℂ), ‖I.1 z‖ < ε ∧ ‖O.1 z‖ < ε

/-- `shared_local` in the exact form of `R6Lw.PhysicalIncidentInterval.shared_local`, for any real interval whose
points land in `P`. -/
theorem TwoLocalAgreement.shared_local_on {O I : Chart} {V P : Set ℂ} {p : ℂ} {v : ℝ}
    (hL : TwoLocalAgreement O I V P p v) {EO : ℂ → ℂ} (hEO : EqOn EO O.2.1 H) (hEOc : ContinuousOn EO Hbar)
    {S : Set ℝ} (hS : ∀ x ∈ S, EO (x : ℂ) ∈ P) :
    ∀ x ∈ S, x < v → ∃ r > 0, (O.dom : Set ℂ) ∩ ball (EO (x : ℂ)) r ⊆ I.dom :=
  fun x hx hxv => hL.shared_local EO hEO hEOc x hxv (hS x hx)

/-- **Drop-in for `R6Lw.PhysicalIncidentInterval`**: the local agreement supplies `inclusion`, `joint_access`,
`tip_local` and `shared_local`; the interval, its collars and landings and the force landing remain. -/
theorem physicalIncidentInterval_of_local {O I : Chart} {V P : Set ℂ} {p : ℂ} {v : ℝ}
    (hL : TwoLocalAgreement O I V P p v) {EO : ℂ → ℂ} (hEO : EqOn EO O.2.1 H) (hEOc : ContinuousOn EO Hbar)
    (S : Set ℝ) (hSo : IsOpen S) (hSc : IsPreconnected S) (hv : v ∈ S) (h0 : (0 : ℝ) ∈ S) (hv0 : v < 0)
    (hcol : ∀ x ∈ S, ∃ r > 0, H ∩ ball (x : ℂ) r ⊆ O.1 '' (I.dom : Set ℂ)) (hland : ∀ x ∈ S, EO (x : ℂ) ∈ P)
    (hne : EO (v : ℂ) ≠ p) : Nonempty (R6Lw.PhysicalIncidentInterval O I EO P p v) :=
  ⟨⟨S, hSo, hSc, hv, h0, hv0, hL.inclusion, hcol, hland, hne, hL.joint_access, hL.tip_local,
    hL.shared_local_on hEO hEOc hland⟩⟩

variable {Ω : Type*}

/-- **Local agreement, bounded two-outer shape** (per sample): with `T = T_C(q)` and the inner chart at
`c_V(T)`, `TwoLocalAgreement` holds. The tip ball is a ball inside `V` (`two_identity_at_visit`); at a shared
landing `E_O(x)`, `x < v`, the landing is alive for `C`, on `R`, and (by the gap of the contacts of `Lv` with `R`
and `0 ∈ closure K^V`) on `V`'s open right arc, so `C ∩ B ⊆ V` there; joint access is `hdrv_of_later`. -/
theorem two_local {A A' : Set Ω} {R L Lv : Ω → ℝ≥0 → ℂ} {r r' : ℝ≥0} {W : Ω → ℝ → ℝ}
    {η : Ω → ℝ → ℂ} {ψ ψ' : Ω → ℂ → ℂ} {n n' : Ω → ℤ} {ω : Ω}
    (hcfg : ∀ ω ∈ A, IsOuterCfg (R ω) (L ω) r (W ω) (η ω)) (hψ : ∀ ω ∈ A, IsCfJordan (R ω) (L ω) r (ψ ω))
    (hcfg' : ∀ ω ∈ A', IsOuterCfg (R ω) (Lv ω) r' (W ω) (η ω))
    (hψ' : ∀ ω ∈ A', IsCfJordan (R ω) (Lv ω) r' (ψ' ω)) (hω : ω ∈ A) (hω' : ω ∈ A')
    (hrev : IsWallReverseVisit (Lv ω) (η ω)) {q : ℝ≥0} (hq0 : 0 < q)
    (hq : (q : ℝ≥0∞) < capLife (travAll R L r η ψ ω))
    (hsub : cfPocket (R ω) (Lv ω) r' ⊆ cfPocket (R ω) (L ω) r)
    (hT0 : 0 ≤ outerFibreEnd R L r η ψ q ω)
    (htip : η ω (outerFibreEnd R L r η ψ q ω) ∈ cfPocket (R ω) (Lv ω) r') :
    TwoLocalAgreement (curChart A R L r η ψ n q ω)
      (curChart A' R Lv r' η ψ' n' (innerRelCap R Lv r' η ψ' (outerFibreEnd R L r η ψ q ω) ω).toNNReal ω)
      (cfPocket (R ω) (Lv ω) r') (closure (cfPocket (R ω) (Lv ω) r') \ {cfPt (openPt (R ω) (Lv ω) r')})
      (η ω (outerFibreEnd R L r η ψ q ω)) (seedL R L r η ψ q ω) := by
  classical
  -- the outer pocket
  have hcf := hcfg ω hω
  have hG : ∀ ω ∈ A, IsChangeConfigInc (R ω) (L ω) r := fun ω hω => (hcfg ω hω).conf
  have hCo : ∀ ω ∈ A, IsOpen (cfPocket (R ω) (L ω) r) := fun ω hω =>
    isOpen_image_negInv' (hG ω hω).isOpen_changePocket (hG ω hω).changePocket_subset_H
  have hCH : ∀ ω ∈ A, cfPocket (R ω) (L ω) r ⊆ H := fun ω hω =>
    PocketJordan.image_negInv_subset_H (hG ω hω).changePocket_subset_H
  have hψc : ∀ ω ∈ A, IsConformalBijection (ψ ω) (cfPocket (R ω) (L ω) r) H := fun ω hω => (hψ ω hω).2.2.2.1
  have h0C := PocketMarks.zero_notMem_closure_of_rightLo_pos hcf.conf hcf.bounded
  have hCb : Bornology.IsBounded (cfPocket (R ω) (L ω) r) := isBounded_image_negInv h0C
  have hx₀ : cfPt (openPt (R ω) (L ω) r) ∉ cfPocket (R ω) (L ω) r := hcf.conf.cfPt_openPt_notMem
  have hJ : Sec6.IsJordanCoord (cfPocket (R ω) (L ω) r) (cfPt (openPt (R ω) (L ω) r))
      (cfPt (closePt (R ω) (L ω) r)) (ψ ω) := hψ ω hω
  have hγ : IsDrivenCurve (travAll R L r η ψ ω) := (hcf.props (hψ ω hω)).1
  obtain ⟨t₁, hqt₁, ht₁⟩ := ENNReal.lt_iff_exists_nnreal_btwn.1 hq
  have hqt₁' : q < t₁ := by exact_mod_cast hqt₁
  obtain ⟨E₀, hE₀, hE₀c, hE₀m, WC, hWC, hWC0, hWCeq, ηC, hηC, hηCeq, hCf⟩ :=
    chart_facts (n := n) hCo hCH hψc hCb hx₀ hJ hω hγ ht₁
  obtain ⟨hOc, hOdom, hOfwd, hOE, hOEc⟩ := hCf q hqt₁'
  have hq0' : (0 : ℝ) < q := by exact_mod_cast hq0
  have hWCq : ∀ s ∈ Icc (0 : ℝ) q, segDriver (travAll R L r η ψ ω) s.toNNReal = WC s := fun s hs =>
    hWCeq s ⟨hs.1, hs.2.trans (by exact_mod_cast hqt₁'.le)⟩
  have hvR : seedR R L r η ψ q ω = chartAR WC q := seedR_eq hWC hWCq
  have hvL : seedL R L r η ψ q ω = chartAL WC q := seedL_eq hWC hWCq
  obtain ⟨hFc, hFeq, hFm⟩ := extendFrom_props hηC hWC hWC0 q.coe_nonneg
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
  set EO : ℂ → ℂ := fun z => E₀ (extendFrom H (fwdMapInv WC q) z) with hEOdef
  have hOphys : ((curChart A R L r η ψ n q ω).dom : Set ℂ) ⊆ H \ fwdHull (W ω) (outerFibreEnd R L r η ψ q ω) := by
    intro w hwO
    have hJarc : IsJordanCoord (cfPocket (R ω) (L ω) r) (cfArcR (R ω) (L ω) r 0) (cfArcR (R ω) (L ω) r 1)
        (ψ ω) := by
      rw [IsChangeConfigInc.cfArcR_zero, IsChangeConfigInc.cfArcR_one]; exact hψ ω hω
    have hzD : w ∈ cfPocket (R ω) (L ω) r ∩
        ψ ω ⁻¹' (H \ fwdHull (fun s : ℝ => segDriver (travAll R L r η ψ ω) s.toNNReal) q) := by
      rw [← relChart_dom_eq_inter (n := n) hCo hCH hψc hω hγ hq]; exact hwO
    exact relDomain_subset_domain hcf.erase hcf.trace hcf.continuous_W hcf.W_zero (hCH ω hω) hCb hJarc hγ
      q.coe_nonneg (by rw [ENNReal.ofReal_coe_nnreal]; exact hq) hzD
  -- the inner pocket
  have hcf' := hcfg' ω hω'
  have hG' : ∀ ω ∈ A', IsChangeConfigInc (R ω) (Lv ω) r' := fun ω hω => (hcfg' ω hω).conf
  have hCo' : ∀ ω ∈ A', IsOpen (cfPocket (R ω) (Lv ω) r') := fun ω hω =>
    isOpen_image_negInv' (hG' ω hω).isOpen_changePocket (hG' ω hω).changePocket_subset_H
  have hCH' : ∀ ω ∈ A', cfPocket (R ω) (Lv ω) r' ⊆ H := fun ω hω =>
    PocketJordan.image_negInv_subset_H (hG' ω hω).changePocket_subset_H
  have hψc' : ∀ ω ∈ A', IsConformalBijection (ψ' ω) (cfPocket (R ω) (Lv ω) r') H := fun ω hω =>
    (hψ' ω hω).2.2.2.1
  have h0U := PocketMarks.zero_notMem_closure_of_rightLo_pos hcf'.conf hcf'.bounded
  have hUb : Bornology.IsBounded (cfPocket (R ω) (Lv ω) r') := isBounded_image_negInv h0U
  have hx₀' : cfPt (openPt (R ω) (Lv ω) r') ∉ cfPocket (R ω) (Lv ω) r' := hcf'.conf.cfPt_openPt_notMem
  have hJ' : Sec6.IsJordanCoord (cfPocket (R ω) (Lv ω) r') (cfPt (openPt (R ω) (Lv ω) r'))
      (cfPt (closePt (R ω) (Lv ω) r')) (ψ' ω) := hψ' ω hω'
  have hγ' : IsDrivenCurve (travAll R Lv r' η ψ' ω) := (hcf'.props (hψ' ω hω')).1
  have hP'o := hcf'.toPocket (hψ' ω hω')
  have hvisit := hP'o.erase.mem_visitSet hT0 htip
  obtain ⟨hqTpos, hqTlive⟩ : 0 < innerRelCap R Lv r' η ψ' (outerFibreEnd R L r η ψ q ω) ω ∧
      ENNReal.ofReal (innerRelCap R Lv r' η ψ' (outerFibreEnd R L r η ψ q ω) ω) <
        capLife (travAll R Lv r' η ψ' ω) :=
    SideVis.erasure_relCap_pos_lt_of_visit hP'o.erase hP'o.driven hvisit
  set qT := innerRelCap R Lv r' η ψ' (outerFibreEnd R L r η ψ q ω) ω with hqTdef
  have hqT0 : (0 : ℝ) ≤ qT := hqTpos.le
  have hqTc : ((qT.toNNReal : ℝ≥0) : ℝ) = qT := Real.coe_toNNReal _ hqT0
  obtain ⟨t₁', hqTt₁', ht₁'⟩ := ENNReal.lt_iff_exists_nnreal_btwn.1 hqTlive
  have hqTt : qT.toNNReal < t₁' := ENNReal.coe_lt_coe.1 hqTt₁'
  have hqTt' : qT < t₁' := by rw [← hqTc]; exact_mod_cast hqTt
  obtain ⟨E₀', hE₀', hE₀'c, hE₀'m, WU, hWU, hWU0, hWUeq, ηU, hηU, hηUeq, hUf⟩ :=
    chart_facts (n := n') hCo' hCH' hψc' hUb hx₀' hJ' hω' hγ' ht₁'
  obtain ⟨hI₀c, hI₀dom, hI₀fwd, hI₀E, hI₀Ec⟩ := hUf qT.toNNReal hqTt
  rw [hqTc] at hI₀dom hI₀fwd hI₀E hI₀Ec
  -- the inner tip at the visit time
  have htrU : capTrace (travAll R Lv r' η ψ' ω) qT.toNNReal = ψ' ω (η ω (outerFibreEnd R L r η ψ q ω)) :=
    R6Two.capTrace_relCap_outer_of_visit hP'o hvisit
  have hψ'T : ψ' ω (η ω (outerFibreEnd R L r η ψ q ω)) ∈ H := (hψc' ω hω').2.mapsTo htip
  have htipU : extendFrom H (fwdMapInv WU qT) ((0 : ℝ) : ℂ) = ψ' ω (η ω (outerFibreEnd R L r η ψ q ω)) := by
    have h1 := hηU.tendsto_fwdMapInv_tip hWU hWU0 hqT0
    rw [← Complex.ofReal_zero] at h1
    rw [extendFrom_eq h0cl h1, hηUeq qT hqT0 hqTt'.le, ← htrU]
    simp only [capTrace, hqTc]
  have hwR0 : 0 < chartAR WU qT := chartAR_pos_of_tip hηU hWU hWU0 hqT0 (htipU ▸ hψ'T)
  have hwL0 : chartAL WU qT < 0 := chartAL_neg_of_tip hηU hWU hWU0 hqT0 (htipU ▸ hψ'T)
  have hwLR : chartAL WU qT < chartAR WU qT := hwL0.trans hwR0
  obtain ⟨hFTc, hFTeq, hFTm⟩ := extendFrom_props hηU hWU hWU0 hqT0
  set EI₀ : ℂ → ℂ := fun z => E₀' (extendFrom H (fwdMapInv WU qT) z) with hEI₀def
  set tip := η ω (outerFibreEnd R L r η ψ q ω) with htipdef
  have hEI₀0 : EI₀ ((0 : ℝ) : ℂ) = tip := by
    simp only [hEI₀def, htipU]
    rw [hE₀' hψ'T]
    exact (hψc' ω hω').2.injOn.leftInvOn_invFunOn htip
  -- the same-time inclusion and the identity (Astra's inner-side argument, reverse visits of `Lv`)
  obtain ⟨hI₀O, hid⟩ := two_identity_at_visit (n := n) (n' := n') hcfg hψ hcfg' hψ' hω hω' hrev hsub hT0 htip
    (c := q) (c' := qT.toNNReal) (relCap_outerFibreEnd hcfg hψ hω hq).symm hqTc

  -- the outer landing description
  have hOsubC : ((curChart A R L r η ψ n q ω).dom : Set ℂ) ⊆ cfPocket (R ω) (L ω) r := fun w hw => by
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
      jordan_comp_ext hJ hE₀ hE₀c hE₀m (hFm (real_mem_Hbar x))
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
    have hpfrC : EO x ∈ frontier (cfPocket (R ω) (L ω) r) := ⟨hpm.1, by rw [(hCo ω hω).interior_eq]; exact hpC⟩
    obtain ⟨θ, hθ, hpθ⟩ := frontier_neg_right_arc hcf.conf h0C hcf.oriented (hψ ω hω) hpfrC hpm.2
      (by rw [hψx]; linarith)
    obtain ⟨-, hvC, -, -, -, -, -, -⟩ := hcf.conf.changeCorner_props
    have hθC : θ ∈ Ioc (0 : ℝ) 1 := ⟨(hcf.conf.rightLo_pos h0C).trans hθ.1, hθ.2.le.trans hvC.2⟩
    have hpV : EO x ∉ cfPocket (R ω) (Lv ω) r' := fun h => hpC (hsub h)
    have hpfrV : EO x ∈ frontier (cfPocket (R ω) (Lv ω) r') :=
      ⟨hxP.1, by rw [(hCo' ω hω').interior_eq]; exact hpV⟩
    have himV : (ψ' ω (EO x)).im = 0 := hJ'.2.2.2.2.1 _ ⟨hpfrV, hxP.2⟩
    rcases lt_trichotomy (ψ' ω (EO x)).re 0 with hneg | hzero | hpos
    · obtain ⟨θ', hθ', hpθ'⟩ := frontier_neg_right_arc hcf'.conf h0U hcf'.oriented (hψ' ω hω') hpfrV hxP.2 hneg
      obtain ⟨-, hNC2, -⟩ := R6Fd.nonCorner_of_right_open hcf.conf hcf'.conf h0U hθ'
      rw [← hpθ'] at hNC2
      obtain ⟨εy, hεy, hεyU⟩ := inter_ball_subset_of_noncorner hJ hCb hx₀ (hCo' ω hω') hsub hxP.1 hpm.1 hpm.2 hNC2
      exact ⟨εy, hεy, fun w hw => hid ⟨hw.1, hεyU ⟨hOsubC hw.1, hw.2⟩⟩⟩
    · exfalso
      have h0 : ψ' ω (EO x) = 0 := Complex.ext hzero himV
      obtain ⟨ρ, hρ, hρC⟩ := R6Fc.exists_ball_subset_of_alive hJ hx₀ hpm halC
      have hball : cfPocket (R ω) (Lv ω) r' ∩ ball (EO x) ρ ⊆
          cfPocket (R ω) (Lv ω) r' ∩ ψ' ω ⁻¹' (H \ fwdHull WU qT) := fun w hw => by
        have hwO : w ∈ ((curChart A R L r η ψ n q ω).dom : Set ℂ) := by
          rw [hOdom]; exact hρC ⟨hsub hw.1, hw.2⟩
        have h1 := hid ⟨hwO, hw.1⟩
        rwa [hI₀dom] at h1
      have hnot := R6Fc.notMem_closure_of_ball_subset hJ' hUb hx₀' (QuantumZipper.fwdHull_mono.2 _) hxP hρ hball
      rw [h0] at hnot
      exact hnot (ConformalImageFull.zero_mem_closure_fwdHull hWU hWU0 hqTpos)
    · exfalso
      obtain ⟨θ'', hθ'', hpθ''⟩ := frontier_pos_left_arc hcf'.conf h0U hcf'.oriented (hψ' ω hω') hpfrV hxP.2 hpos
      obtain ⟨-, -, -, ha, hb, -, -, -⟩ := hcf'.conf.changeCorner_props
      have ha0 := hcf'.conf.leftLo_pos h0U
      have hθ''I : θ'' ∈ Ioc (0 : ℝ) 1 := ⟨ha0.trans hθ''.1, hθ''.2.le.trans hb.2⟩
      have hgap := (hcf'.conf.changeCorners).2.2.2.1.2.2.2 θ'' hθ''
      have h1 : cfPt (WangWu.toDisc (Lemma71I.realPath (R ω)) θ) =
          cfPt (WangWu.toDisc (Lemma71I.realPath (Lv ω)) θ'') := hpθ.symm.trans hpθ''
      have h2 := injOn_cfPt (R6Fd.toDisc_ne_neg_one hcf.conf.right hθC)
        (R6Fd.toDisc_ne_neg_one hcf'.conf.left hθ''I) h1
      exact hgap ⟨⟨hθ''I.1.le, hθ''I.2⟩, θ, ⟨hθC.1.le, hθC.2⟩, h2⟩
  · exact hdrv_of_later (O := curChart A R L r η ψ n q ω) (I₀ := curChart A' R Lv r' η ψ' n' qT.toNNReal ω)
      hWC hWC0 hWU hWU0 q.coe_nonneg hqT0 hOfwd hOdom hI₀fwd hI₀dom hsub hI₀O (hψc' ω hω')
      (hlater_two (n := n) (n' := n') hcfg hψ hcfg' hψ' hω hω' hrev hq hsub hT0 htip hqt₁' ht₁ hqTt'
        (fun q₂ hq₂ => (hCf q₂ hq₂).2.1) (fun q₂ hq₂ => (hUf q₂ hq₂).2.1))

section Final

open MeasureTheory ProbabilityTheory
open LQGMetric (DistOn)
open QuantumZipper (chiC)
open scoped Real
open WholeField R7Outer R7Leaves R6Nest R6Rel R6Cert PocketMarks PocketSeedOpen PocketStopWallsFin PocketStopSide

universe u

/-- **Local agreement for the shape `Two`, PROVED** (reverse visits of `M_L` through Prop. 4.11 and Lemma 4.7; no
Aux. lemma 136): on the source binders of `R6Lw.R6PhysicalIntervalTwoRemaining`, almost surely on the shape event,
the actual outer chart `C` at `q`, the actual inner chart of `V` at `c_V(T)` (LANDING's `I t`), the current tip and
the actual outer left mark satisfy `TwoLocalAgreement` — in particular `PhysicalIncidentInterval`'s `tip_local`,
`shared_local` (for every `x < v` landing in `P`, any interval), `inclusion` and `joint_access`. -/
theorem localAgreementTwo {k rL rR c c' : ℝ} (h411 : Sec5.Cond44Ref.Prop411QStatement.{u})
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
        (∀ ω ∈ A, IsOuterCfg (R ω) (L ω) r (fun t : ℝ => W' t.toNNReal ω) (η ω) ∧
          IsCfJordan (R ω) (L ω) r (ψ ω)) →
        (∀ ω ∈ A', IsOuterCfg (R ω) (ML ω) (StripSys.rt s)
            (fun t : ℝ => W' t.toNNReal ω) (η ω) ∧
          IsCfJordan (R ω) (ML ω) (StripSys.rt s) (ψ' ω)) →
        ∀ᵐ ω ∂P, ω ∈ A → ω ∈ A' →
          ω ∈ nestRelEvent R L r η ψ MR ML R ML s q →
          TwoLocalAgreement (R6Two.currentChart A R L r η ψ n (StripSys.rt q) ω)
            ((fun q' : ℝ => R6Two.currentChart A' R ML (StripSys.rt s) η ψ' n' q'.toNNReal ω)
              (innerRelCap R ML (StripSys.rt s) η ψ' (outerFibreEnd R L r η ψ (StripSys.rt q) ω) ω))
            (cfPocket (R ω) (ML ω) (StripSys.rt s))
            (closure (cfPocket (R ω) (ML ω) (StripSys.rt s)) \ {cfPt (openPt (R ω) (ML ω) (StripSys.rt s))})
            (η ω (outerFibreEnd R L r η ψ (StripSys.rt q) ω))
            (R6Tn.leftSeed (travAll R L r η ψ) (StripSys.rt q) ω) := by
  intro _ _ Ω _ _ P _ h W' ζ' αR βR βL αL ζαR ζβR ζβL ζαL hcfg R L η hV MR ML hMR hML r A A' ψ ψ' n n' s q hA
    hA'
  filter_upwards [ae_rev_ML h411 h47 h47T hk4 hc hc' hcfg hV hML] with ω hrev hωA hωA' hωN
  obtain ⟨hq0, hqlive, -, hsub, u, hu0, hcap, hrel, -⟩ := hωN
  have hcfO := (hA ω hωA).1
  have hγ : IsDrivenCurve (travAll R L r η ψ ω) := (hcfO.props (hA ω hωA).2).1
  have hrtq : ((StripSys.rt q : ℝ≥0) : ℝ) = q := Real.coe_toNNReal _ (by exact_mod_cast hq0.le)
  have hinv : capInv (travAll R L r η ψ ω) ((StripSys.rt q : ℝ≥0) : ℝ) = u := by
    rw [hrtq, ← hcap]
    exact hγ.capInv_eq hu0
  have htip : η ω (outerFibreEnd R L r η ψ (StripSys.rt q) ω) ∈ cfPocket (R ω) (ML ω) (StripSys.rt s) := by
    unfold outerFibreEnd
    rw [hinv]
    exact hrel
  have hT0 : 0 ≤ outerFibreEnd R L r η ψ (StripSys.rt q) ω :=
    hcfO.erase.nonneg.trans (hcfO.erase.fibre_mem _).1
  have hq0' : 0 < StripSys.rt q := by
    show 0 < (q : ℝ).toNNReal
    exact Real.toNNReal_pos.2 (by exact_mod_cast hq0)
  exact two_local (n := n) (n' := n') (fun ω hω => (hA ω hω).1) (fun ω hω => (hA ω hω).2)
    (fun ω hω => (hA' ω hω).1) (fun ω hω => (hA' ω hω).2) hωA hωA' hrev hq0' hqlive hsub hT0 htip

end Final

end InteractingSLE.Sec7.R6Cor
