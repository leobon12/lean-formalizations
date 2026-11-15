/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.R6CorTwoInfInf

/-!
# R.6's two-outer faces at infinity without Aux. lemma 136

Packet PROVE-R6-CORNER, second round. The faces of the shapes `TwoInf` (outer pocket opening at the flow seed, bounded
outer inner pocket) and `TwoInfInf` (both opening at the flow seed), as `R6Cor.two_face` for `Two`:

* `two_faceInf`, `two_faceInfInf`: `R6FaceR` for the current charts of `C` at `q` and `V` at every close later `q'`,
  from `corner_face_sharedRInf` / `corner_face_sharedRInfInf` with the identities `two_identity_at_visitInf` /
  `two_identity_at_visitInfInf` in place of the contained pocket's `D_U(c_U(T)) = U ∖ K_T`, and the common later
  times `hlater_twoInf` / `hlater_twoInfInf`;
* **`r6FaceSTwoInfRemaining_of_walls`**, **`r6FaceSTwoInfInfRemaining_of_walls`**:
  `R6Two.R6FaceSTwo{Inf,InfInf}Remaining k rL rR c c'` from Prop. 4.11 and Lemma 4.7 (`h411`, `h47`, `h47T`),
  `4 < k`, `0 ≤ c`, `0 ≤ c'`.

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

variable {Ω : Type*}

/-- **R.6's face for the shape `TwoInf` at every close later inner time** (outer pocket opening at the flow seed,
bounded outer `V = cfPocket R Lv r' ⊆ C`): as `corner_face_sharedRInf`, with `two_identity_at_visitInf`. -/
theorem two_faceInf {A A' : Set Ω} {R L Lv : Ω → ℝ≥0 → ℂ} {r r' : ℝ≥0} {W : Ω → ℝ → ℝ}
    {η : Ω → ℝ → ℂ} {ψ ψ' : Ω → ℂ → ℂ} {n n' : Ω → ℤ} {ω : Ω}
    (hcfg : ∀ ω ∈ A, IsOuterCfgInf (R ω) (L ω) r (W ω) (η ω)) (hψ : ∀ ω ∈ A, IsCfJordanInf (R ω) (L ω) r (ψ ω))
    (hcfg' : ∀ ω ∈ A', IsOuterCfg (R ω) (Lv ω) r' (W ω) (η ω))
    (hψ' : ∀ ω ∈ A', IsCfJordan (R ω) (Lv ω) r' (ψ' ω)) (hω : ω ∈ A) (hω' : ω ∈ A')
    (hrev : IsWallReverseVisit (Lv ω) (η ω)) {q : ℝ≥0} (hq0 : 0 < q)
    (hq : (q : ℝ≥0∞) < capLife (travAllInf R L r η ψ ω))
    (hsub : cfPocket (R ω) (Lv ω) r' ⊆ cfPocket (R ω) (L ω) r)
    (hT0 : 0 ≤ outerFibreEndInf R L r η ψ q ω)
    (htip : η ω (outerFibreEndInf R L r η ψ q ω) ∈ cfPocket (R ω) (Lv ω) r') :
    ∃ εW > 0, ∀ q' : ℝ≥0, innerRelCap R Lv r' η ψ' (outerFibreEndInf R L r η ψ q ω) ω < q' →
      (q' : ℝ) < innerRelCap R Lv r' η ψ' (outerFibreEndInf R L r η ψ q ω) ω + εW →
      ((curChart A' R Lv r' η ψ' n' q' ω).dom : Set ℂ) ⊆ (curChartInf A R L r η ψ n q ω).dom →
      ∀ ρL ρR σL σR vL vR wL wR : Fin 1 → ℝ, vL 0 = seedLInf R L r η ψ q ω → vR 0 = seedRInf R L r η ψ q ω →
        wL 0 = seedL R Lv r' η ψ' q' ω → wR 0 = seedR R Lv r' η ψ' q' ω → ρL 0 = σL 0 →
        R6FaceR ρL ρR σL σR vL vR wL wR (curChartInf A R L r η ψ n q ω) (curChart A' R Lv r' η ψ' n' q' ω)
          (H \ ((curChartInf A R L r η ψ n q ω).dom : Set ℂ)) (H \ ((curChart A' R Lv r' η ψ' n' q' ω).dom : Set ℂ))
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
  obtain ⟨hqTpos, hqTlive⟩ : 0 < innerRelCap R Lv r' η ψ' (outerFibreEndInf R L r η ψ q ω) ω ∧
      ENNReal.ofReal (innerRelCap R Lv r' η ψ' (outerFibreEndInf R L r η ψ q ω) ω) <
        capLife (travAll R Lv r' η ψ' ω) :=
    SideVis.erasure_relCap_pos_lt_of_visit hP'o.erase hP'o.driven hvisit
  set qT := innerRelCap R Lv r' η ψ' (outerFibreEndInf R L r η ψ q ω) ω with hqTdef
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
  have htrU : capTrace (travAll R Lv r' η ψ' ω) qT.toNNReal = ψ' ω (η ω (outerFibreEndInf R L r η ψ q ω)) :=
    R6Two.capTrace_relCap_outer_of_visit hP'o hvisit
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
  obtain ⟨hI₀O, hid⟩ := two_identity_at_visitInf (n := n) (n' := n') hcfg hψ hcfg' hψ' hω hω' hrev hsub hT0 htip
    (c := q) (c' := qT.toNNReal) (relCap_outerFibreEndInf hcfg hψ hω hq).symm hqTc
  -- the inverse of the inner Jordan coordinate on `ℍ`
  have hinvU : ∀ k ∈ H, E₀' k ∈ cfPocket (R ω) (Lv ω) r' ∧ ψ' ω (E₀' k) = k := fun k hk => by
    rw [hE₀' hk]
    have hex : ∃ a ∈ cfPocket (R ω) (Lv ω) r', ψ' ω a = k := (hψc' ω hω').2.surjOn hk
    exact ⟨Function.invFunOn_mem hex, Function.invFunOn_eq hex⟩
  have hullImg : ∀ k ∈ fwdHull WU qT, E₀' k ∉ ((curChartInf A R L r η ψ n q ω).dom : Set ℂ) := by
    intro k hk hkO
    have hkH : k ∈ H := QuantumZipper.fwdHull_mono.2 _ hk
    obtain ⟨heU, hek⟩ := hinvU k hkH
    have hmem : E₀' k ∈ ((curChart A' R Lv r' η ψ' n' qT.toNNReal ω).dom : Set ℂ) := hid ⟨hkO, heU⟩
    rw [hI₀dom] at hmem
    have := hmem.2
    rw [Set.mem_preimage, hek] at this
    exact this.2 hk
  have hnotD : ∀ t ∈ Icc (chartAL WU qT) (chartAR WU qT),
      EI₀ t ∉ ((curChartInf A R L r η ψ n q ω).dom : Set ℂ) := fun t ht =>
    notMem_of_mem_closure_of_subset (K := E₀' '' fwdHull WU qT) (curChartInf A R L r η ψ n q ω).dom.isOpen
      (fun w hw => ⟨(hOphys hw).1, fun ⟨k, hk, hke⟩ => hullImg k hk (hke ▸ hw)⟩)
      (mem_closure_of_dead (KT := E₀' '' fwdHull WU qT) hE₀'c (QuantumZipper.fwdHull_mono.2 _)
        (fun k hk => ⟨k, hk, rfl⟩) (dead_of_mem_Icc hηU hWU hWU0 hqTpos hwLR ht))
  have hb0 : (extendFrom H (fwdMapInv WU qT) (chartAL WU qT : ℂ)).re ≤ 0 :=
    R6Fd.re_landL_le hηU hWU hWU0 hqTpos (x := 0) (by
      simpa using ConformalImageFull.zero_mem_closure_fwdHull hWU hWU0 hqTpos)
  have harcR : ∀ t : ℝ, t < chartAL WU qT → ∃ θ ∈ Ioo (rightLo (R ω) (Lv ω) r') (rightHi (R ω) (Lv ω) r'),
      EI₀ t = R6Fd.wallPt (R ω) θ := by
    intro t ht
    obtain ⟨him, hgt⟩ := landL_re_gt hηU hWU hWU0 hqTpos hwLR ht
    have hpm := hE₀'m (hFTm (real_mem_Hbar t))
    have hψp : ψ' ω (EI₀ t) = extendFrom H (fwdMapInv WU qT) (t : ℂ) :=
      jordan_comp_ext hJ' hE₀' hE₀'c hE₀'m (hFTm (real_mem_Hbar t))
    have hpU : EI₀ t ∉ cfPocket (R ω) (Lv ω) r' := fun h => by
      have := (hψc' ω hω').2.mapsTo h
      rw [hψp] at this
      have h2 : (0 : ℝ) < (extendFrom H (fwdMapInv WU qT) (t : ℂ)).im := this
      rw [him] at h2
      exact lt_irrefl _ h2
    have hpfr : EI₀ t ∈ frontier (cfPocket (R ω) (Lv ω) r') :=
      ⟨hpm.1, by rw [(hCo' ω hω').interior_eq]; exact hpU⟩
    exact frontier_neg_right_arc hcf'.conf h0U hcf'.oriented (hψ' ω hω') hpfr hpm.2 (by rw [hψp]; linarith)
  have hθI : ∀ θ ∈ Ioo (rightLo (R ω) (Lv ω) r') (rightHi (R ω) (Lv ω) r'), θ ∈ Ioc (0 : ℝ) 1 := by
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
      ‖(curChartInf A R L r η ψ n q ω).1 ((curChart A' R Lv r' η ψ' n' qT.toNNReal ω).2.1 z)‖ ≤ M := by
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
    have hwz : (curChart A' R Lv r' η ψ' n' qT.toNNReal ω).2.1 z = EI₀ z := (hI₀E hzH).symm
    have h1 := norm_fwdMap_le hWC hWC0 q.coe_nonneg hC₀ hwO'.2
    have hwx : (curChart A' R Lv r' η ψ' n' qT.toNNReal ω).2.1 z ∈
        closure (cfPocket (R ω) (L ω) r) := subset_closure hwO'.1
    have h2 := hδψ hwx (by rw [hwz]; exact hzb)
    rw [dist_eq_norm] at h2
    have h3 : ‖ψ ω ((curChart A' R Lv r' η ψ' n' qT.toNNReal ω).2.1 z)‖ ≤ ‖ψ ω (EI₀ t)‖ + 1 := by
      have := norm_le_norm_add_norm_sub' (ψ ω ((curChart A' R Lv r' η ψ' n' qT.toNNReal ω).2.1 z)) (ψ ω (EI₀ t))
      linarith
    linarith
  -- the driver identification
  have hdrv := hdrv_of_later (O := curChartInf A R L r η ψ n q ω) (I₀ := curChart A' R Lv r' η ψ' n' qT.toNNReal ω)
    hWC hWC0 hWU hWU0 q.coe_nonneg hqT0 hOfwd hOdom hI₀fwd hI₀dom hsub hI₀O (hψc' ω hω')
    (hlater_twoInf (n := n) (n' := n') hcfg hψ hcfg' hψ' hω hω' hrev hq hsub hT0 htip hqt₁' ht₁ hqTt'
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
  refine ⟨εW, hεW, fun q' hq'lo hq'hi hIncl ρL ρR σL σR vL vR wL wR hvLv hvR' hwLv hwR' hρσ => ?_⟩
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
  have hWUq : ∀ s ∈ Icc (0 : ℝ) q', segDriver (travAll R Lv r' η ψ' ω) s.toNNReal = WU s := fun s hs =>
    hWUeq s ⟨hs.1, hs.2.trans (by exact_mod_cast hq't.le)⟩
  have hwRe : seedR R Lv r' η ψ' q' ω = chartAR WU q' := seedR_eq hWU hWUq
  have hwLe : seedL R Lv r' η ψ' q' ω = chartAL WU q' := seedL_eq hWU hWUq
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
      (curChart A' R Lv r' η ψ' n' qT.toNNReal ω).2.1 z ∈ ((curChart A' R Lv r' η ψ' n' q' ω).dom : Set ℂ) := by
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
      ‖(curChart A' R Lv r' η ψ' n' qT.toNNReal ω).1 ((curChart A' R Lv r' η ψ' n' q' ω).2.1 w)‖ ≤ ρ := by
    filter_upwards [self_mem_nhdsWithin, nhdsWithin_le_nhds (ball_mem_nhds (0 : ℂ) (half_pos hρ0))] with w hwH hwb
    rw [← hIE hwH]
    show ‖(curChart A' R Lv r' η ψ' n' qT.toNNReal ω).1 (E₀' (extendFrom H (fwdMapInv WU q') w))‖ ≤ ρ
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
    have hn : EI₀ tξ ∉ ((curChart A' R Lv r' η ψ' n' qT.toNNReal ω).dom : Set ℂ) := fun h => hpξO (hI₀O h)
    rw [hI₀dom] at hn
    have hH := (hψc' ω hω').2.mapsTo htξU
    have : ψ' ω (EI₀ tξ) ∈ fwdHull WU qT := by
      by_contra hk; exact hn ⟨htξU, hH, hk⟩
    exact QuantumZipper.fwdHull_mono.1 hq'lo'.le this
  obtain ⟨θy, hθy, hpyθ⟩ := harcR ty (by linarith)
  obtain ⟨hNC1, hNC2, hNC3⟩ := R6Fd.nonCorner_of_right_open hcf.conf hcf'.conf h0U hθy
  rw [← hpyθ] at hNC1 hNC2 hNC3
  have hpyU : EI₀ ty ∈ closure (cfPocket (R ω) (Lv ω) r') := frontier_subset_closure hNC1
  obtain ⟨εy, hεy, hεyU⟩ := inter_ball_subset_of_noncornerInf hJ (hCo' ω hω') hsub hpyU
    (closure_mono hsub hpyU) hNC2
  have hψ'py : ψ' ω (EI₀ ty) = extendFrom H (fwdMapInv WU qT) (ty : ℂ) :=
    jordan_comp_ext hJ' hE₀' hE₀'c hE₀'m (hFTm (real_mem_Hbar ty))
  have hpyAlive : ψ' ω (EI₀ ty) ∉ closure (fwdHull WU qT) := by
    rw [hψ'py]; exact alive_of_not_mem_Icc hηU hWU hWU0 hqT0 (Or.inl (by linarith))
  have hIncl₀ : cfPocket (R ω) (Lv ω) r' ∩ ψ' ω ⁻¹' (H \ fwdHull WU qT) ⊆
      cfPocket (R ω) (L ω) r ∩ ψ ω ⁻¹' (H \ fwdHull WC q) := by
    rw [← hI₀dom, ← hOdom]; exact hI₀O
  have hOU : ∀ w ∈ ((curChartInf A R L r η ψ n q ω).dom : Set ℂ), w ∈ cfPocket (R ω) (Lv ω) r' →
      w ∈ ((curChart A' R Lv r' η ψ' n' qT.toNNReal ω).dom : Set ℂ) := fun w hwO hwU => hid ⟨hwO, hwU⟩
  have hpyCalive : ψ ω (EI₀ ty) ∉ closure (fwdHull WC q) := by
    obtain ⟨ρy, hρy, hρysub⟩ := exists_ball_subset_of_alive hJ' hx₀' (hE₀'m (hFTm (real_mem_Hbar ty))) hpyAlive
    refine notMem_closure_of_ball_subsetInf hJ (QuantumZipper.fwdHull_mono.2 _) (hEI₀C ty (real_mem_Hbar ty))
      (lt_min hρy hεy) fun z hz => ?_
    have hzU : z ∈ cfPocket (R ω) (Lv ω) r' := hεyU ⟨hz.1, ball_subset_ball (min_le_right _ _) hz.2⟩
    exact hIncl₀ (hρysub ⟨hzU, ball_subset_ball (min_le_left _ _) hz.2⟩)
  -- dead and alive in the outer chart
  have hdeadO : ∀ x : ℝ, EO x = EI₀ tξ → vL 0 < x ∧ x ≤ vR 0 := by
    intro x hx
    rw [hvLv, hvL, hvR', hvR]
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
    rw [hvLv, hvL, hvR', hvR]
    by_contra hxI
    push Not at hxI
    have hψx : ψ ω (EO x) = extendFrom H (fwdMapInv WC q) (x : ℂ) :=
      jordan_comp_extInf hJ hE₀ hE₀c hE₀m (hFm (real_mem_Hbar x))
    rw [hx] at hψx
    exact hpyCalive (hψx ▸ dead_of_mem_Icc hηC hWC hWC0 hq0' (hvL0.trans hvR0) hxI)
  -- dead and alive in the later inner chart
  have hdeadI : ∀ x : ℝ, E₀' (extendFrom H (fwdMapInv WU q') (x : ℂ)) = EI₀ tξ → wL 0 < x ∧ x < wR 0 := by
    intro x hx
    rw [hwLv, hwLe, hwR', hwRe]
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
  have hfar : ∀ p ∈ closure (cfPocket (R ω) (Lv ω) r') \ {cfPt (openPt (R ω) (Lv ω) r')}, d₀ ≤ dist p tip →
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
    rw [hwLv, hwLe, hwR', hwRe]
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
      ((curChartInf A R L r η ψ n q ω).dom : Set ℂ) ∩ ball p ε₁ ⊆ cfPocket (R ω) (Lv ω) r' →
      ∃ ε > 0, ((curChartInf A R L r η ψ n q ω).dom : Set ℂ) ∩ ball p ε ⊆
        ((curChart A' R Lv r' η ψ' n' q' ω).dom : Set ℂ) := by
    intro p hpd ε₁ hε₁ hsubU
    refine ⟨min ε₁ (d₀ / 2), lt_min hε₁ (half_pos hd₀pos), fun w hw => ?_⟩
    have hwU := hsubU ⟨hw.1, ball_subset_ball (min_le_left _ _) hw.2⟩
    have hwI := hOU w hw.1 hwU
    have hz := hI₀c.fwd_mem hwI
    have hwe : (curChart A' R Lv r' η ψ' n' qT.toNNReal ω).2.1 ((curChart A' R Lv r' η ψ' n' qT.toNNReal ω).1 w) = w :=
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
      ((curChart A' R Lv r' η ψ' n' q' ω).dom : Set ℂ) := by
    obtain ⟨ε₁, hε₁, hε₁U⟩ := Metric.isOpen_iff.1 (hCo' ω hω') _ htξU
    exact hloc _ (min_le_left _ _) ε₁ hε₁ fun w hw => hε₁U hw.2
  have hlocy := hloc _ (min_le_right _ _) εy hεy fun w hw => by
    rw [hOdom] at hw
    exact hεyU ⟨hw.1.1, hw.2⟩
  -- the bound of the later inner coordinate near the inner landings
  obtain ⟨C₀', hC₀'⟩ := exists_norm_fwdMapInv_sub_le hWU hWU0 q'.coe_nonneg
  have hbddI : ∀ t ∈ Ioo a (chartAR WU qT), ∃ ε > 0, ∃ M : ℝ,
      ∀ w ∈ ((curChart A' R Lv r' η ψ' n' q' ω).dom : Set ℂ) ∩ ball (EI₀ t) ε,
        ‖(curChart A' R Lv r' η ψ' n' q' ω).1 w‖ ≤ M := by
    intro t _
    have hpU := hE₀'m (hFTm (real_mem_Hbar t))
    obtain ⟨ε, hε, hεψ⟩ := Metric.continuousWithinAt_iff.1 (hJ'.1 _ hpU) 1 one_pos
    refine ⟨ε, hε, ‖ψ' ω (EI₀ t)‖ + 1 + C₀', fun w hw => ?_⟩
    have hwI := hw.1
    rw [hIdom] at hwI
    rw [hIfwd _ hwI.1]
    have h1 := norm_fwdMap_le hWU hWU0 q'.coe_nonneg hC₀' hwI.2
    have hwx : w ∈ closure (cfPocket (R ω) (Lv ω) r') \ {cfPt (openPt (R ω) (Lv ω) r')} :=
      ⟨subset_closure hwI.1, fun h => hx₀' (h ▸ hwI.1)⟩
    have h2 := hεψ hwx (mem_ball.1 hw.2)
    rw [dist_eq_norm] at h2
    have h3 := norm_le_norm_add_norm_sub' (ψ' ω w) (ψ' ω (EI₀ t))
    linarith
  exact r6FaceR_left_of_reflection hOc hI₀c hIc hI₀O hIncl hOE hOEc hI₀E hI₀Ec hIE hIEc hwR0 hnot hbdd hdrv hρ0
    hinc hinc0 h2ρ (by linarith [htξ.1]) (by linarith) hdeadO haliveO hdeadI haliveI (by rw [hwLv, hwLe]; exact hwL0')
    hρσ hlocξ hlocy hbddI

/-- **R.6's face for the shape `TwoInfInf` at every close later inner time** (both pockets opening at the flow
seed): as `corner_face_sharedRInfInf`, with `two_identity_at_visitInfInf`. -/
theorem two_faceInfInf {A A' : Set Ω} {R L Lv : Ω → ℝ≥0 → ℂ} {r r' : ℝ≥0} {W : Ω → ℝ → ℝ}
    {η : Ω → ℝ → ℂ} {ψ ψ' : Ω → ℂ → ℂ} {n n' : Ω → ℤ} {ω : Ω}
    (hcfg : ∀ ω ∈ A, IsOuterCfgInf (R ω) (L ω) r (W ω) (η ω)) (hψ : ∀ ω ∈ A, IsCfJordanInf (R ω) (L ω) r (ψ ω))
    (hcfg' : ∀ ω ∈ A', IsOuterCfgInf (R ω) (Lv ω) r' (W ω) (η ω))
    (hψ' : ∀ ω ∈ A', IsCfJordanInf (R ω) (Lv ω) r' (ψ' ω)) (hω : ω ∈ A) (hω' : ω ∈ A')
    (hrev : IsWallReverseVisit (Lv ω) (η ω)) {q : ℝ≥0} (hq0 : 0 < q)
    (hq : (q : ℝ≥0∞) < capLife (travAllInf R L r η ψ ω))
    (hsub : cfPocket (R ω) (Lv ω) r' ⊆ cfPocket (R ω) (L ω) r)
    (hT0 : 0 ≤ outerFibreEndInf R L r η ψ q ω)
    (htip : η ω (outerFibreEndInf R L r η ψ q ω) ∈ cfPocket (R ω) (Lv ω) r') :
    ∃ εW > 0, ∀ q' : ℝ≥0, innerRelCapInf R Lv r' η ψ' (outerFibreEndInf R L r η ψ q ω) ω < q' →
      (q' : ℝ) < innerRelCapInf R Lv r' η ψ' (outerFibreEndInf R L r η ψ q ω) ω + εW →
      ((curChartInf A' R Lv r' η ψ' n' q' ω).dom : Set ℂ) ⊆ (curChartInf A R L r η ψ n q ω).dom →
      ∀ ρL ρR σL σR vL vR wL wR : Fin 1 → ℝ, vL 0 = seedLInf R L r η ψ q ω → vR 0 = seedRInf R L r η ψ q ω →
        wL 0 = seedLInf R Lv r' η ψ' q' ω → wR 0 = seedRInf R Lv r' η ψ' q' ω → ρL 0 = σL 0 →
        R6FaceR ρL ρR σL σR vL vR wL wR (curChartInf A R L r η ψ n q ω) (curChartInf A' R Lv r' η ψ' n' q' ω)
          (H \ ((curChartInf A R L r η ψ n q ω).dom : Set ℂ)) (H \ ((curChartInf A' R Lv r' η ψ' n' q' ω).dom : Set
              ℂ)) := by
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
  -- the inner tip at the visit time
  have htrU : capTrace (travAllInf R Lv r' η ψ' ω) qT.toNNReal = ψ' ω (η ω (outerFibreEndInf R L r η ψ q ω)) :=
    R6Two.capTrace_relCapInf_outer_of_visit hP'o hvisit
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
  obtain ⟨hI₀O, hid⟩ := two_identity_at_visitInfInf (n := n) (n' := n') hcfg hψ hcfg' hψ' hω hω' hrev hsub hT0
    htip (c := q) (c' := qT.toNNReal) (relCap_outerFibreEndInf hcfg hψ hω hq).symm hqTc
  -- the inverse of the inner Jordan coordinate on `ℍ`
  have hinvU : ∀ k ∈ H, E₀' k ∈ cfPocket (R ω) (Lv ω) r' ∧ ψ' ω (E₀' k) = k := fun k hk => by
    rw [hE₀' hk]
    have hex : ∃ a ∈ cfPocket (R ω) (Lv ω) r', ψ' ω a = k := (hψc' ω hω').2.surjOn hk
    exact ⟨Function.invFunOn_mem hex, Function.invFunOn_eq hex⟩
  have hullImg : ∀ k ∈ fwdHull WU qT, E₀' k ∉ ((curChartInf A R L r η ψ n q ω).dom : Set ℂ) := by
    intro k hk hkO
    have hkH : k ∈ H := QuantumZipper.fwdHull_mono.2 _ hk
    obtain ⟨heU, hek⟩ := hinvU k hkH
    have hmem : E₀' k ∈ ((curChartInf A' R Lv r' η ψ' n' qT.toNNReal ω).dom : Set ℂ) := hid ⟨hkO, heU⟩
    rw [hI₀dom] at hmem
    have := hmem.2
    rw [Set.mem_preimage, hek] at this
    exact this.2 hk
  have hnotD : ∀ t ∈ Icc (chartAL WU qT) (chartAR WU qT),
      EI₀ t ∉ ((curChartInf A R L r η ψ n q ω).dom : Set ℂ) := fun t ht =>
    notMem_of_mem_closure_of_subset (K := E₀' '' fwdHull WU qT) (curChartInf A R L r η ψ n q ω).dom.isOpen
      (fun w hw => ⟨(hOphys hw).1, fun ⟨k, hk, hke⟩ => hullImg k hk (hke ▸ hw)⟩)
      (mem_closure_of_dead (KT := E₀' '' fwdHull WU qT) hE₀'c (QuantumZipper.fwdHull_mono.2 _)
        (fun k hk => ⟨k, hk, rfl⟩) (dead_of_mem_Icc hηU hWU hWU0 hqTpos hwLR ht))
  have hb0 : (extendFrom H (fwdMapInv WU qT) (chartAL WU qT : ℂ)).re ≤ 0 :=
    R6Fd.re_landL_le hηU hWU hWU0 hqTpos (x := 0) (by
      simpa using ConformalImageFull.zero_mem_closure_fwdHull hWU hWU0 hqTpos)
  have harcR : ∀ t : ℝ, t < chartAL WU qT → ∃ θ ∈ Ioo 0 (rightHi (R ω) (Lv ω) r'),
      EI₀ t = R6Fd.wallPt (R ω) θ := by
    intro t ht
    obtain ⟨him, hgt⟩ := landL_re_gt hηU hWU hWU0 hqTpos hwLR ht
    have hpm := hE₀'m (hFTm (real_mem_Hbar t))
    have hψp : ψ' ω (EI₀ t) = extendFrom H (fwdMapInv WU qT) (t : ℂ) :=
      jordan_comp_extInf hJ' hE₀' hE₀'c hE₀'m (hFTm (real_mem_Hbar t))
    have hpU : EI₀ t ∉ cfPocket (R ω) (Lv ω) r' := fun h => by
      have := (hψc' ω hω').2.mapsTo h
      rw [hψp] at this
      have h2 : (0 : ℝ) < (extendFrom H (fwdMapInv WU qT) (t : ℂ)).im := this
      rw [him] at h2
      exact lt_irrefl _ h2
    have hpfr : EI₀ t ∈ frontier (cfPocket (R ω) (Lv ω) r') :=
      ⟨hpm, by rw [(hCo' ω hω').interior_eq]; exact hpU⟩
    exact frontier_neg_right_arcInf hcf'.conf hcf'.seed hcf'.oriented (hψ' ω hω') hpfr (by rw [hψp]; linarith)
  have hθI : ∀ θ ∈ Ioo 0 (rightHi (R ω) (Lv ω) r'), θ ∈ Ioc (0 : ℝ) 1 := by
    obtain ⟨-, hv', -, -, -, -, -, -⟩ := hcf'.conf.changeCorner_props
    exact fun θ hθ => ⟨hθ.1, hθ.2.le.trans hv'.2⟩
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
    fun z hz => closure_mono hsub (hE₀'m (hFTm hz))
  obtain ⟨C₀, hC₀⟩ := exists_norm_fwdMapInv_sub_le hWC hWC0 q.coe_nonneg
  have hbdd : ∀ t ∈ Ioo a (chartAR WU qT), ∃ M : ℝ, ∀ᶠ z in 𝓝[H] (t : ℂ),
      ‖(curChartInf A R L r η ψ n q ω).1 ((curChartInf A' R Lv r' η ψ' n' qT.toNNReal ω).2.1 z)‖ ≤ M := by
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
    have hwz : (curChartInf A' R Lv r' η ψ' n' qT.toNNReal ω).2.1 z = EI₀ z := (hI₀E hzH).symm
    have h1 := norm_fwdMap_le hWC hWC0 q.coe_nonneg hC₀ hwO'.2
    have hwx : (curChartInf A' R Lv r' η ψ' n' qT.toNNReal ω).2.1 z ∈
        closure (cfPocket (R ω) (L ω) r) := subset_closure hwO'.1
    have h2 := hδψ hwx (by rw [hwz]; exact hzb)
    rw [dist_eq_norm] at h2
    have h3 : ‖ψ ω ((curChartInf A' R Lv r' η ψ' n' qT.toNNReal ω).2.1 z)‖ ≤ ‖ψ ω (EI₀ t)‖ + 1 := by
      have := norm_le_norm_add_norm_sub' (ψ ω ((curChartInf A' R Lv r' η ψ' n' qT.toNNReal ω).2.1 z)) (ψ ω (EI₀ t))
      linarith
    linarith
  -- the driver identification
  have hdrv := hdrv_of_later (O := curChartInf A R L r η ψ n q ω) (I₀ := curChartInf A' R Lv r' η ψ' n' qT.toNNReal ω)
    hWC hWC0 hWU hWU0 q.coe_nonneg hqT0 hOfwd hOdom hI₀fwd hI₀dom hsub hI₀O (hψc' ω hω')
    (hlater_twoInfInf (n := n) (n' := n') hcfg hψ hcfg' hψ' hω hω' hrev hq hsub hT0 htip hqt₁' ht₁ hqTt'
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
  refine ⟨εW, hεW, fun q' hq'lo hq'hi hIncl ρL ρR σL σR vL vR wL wR hvLv hvR' hwLv hwR' hρσ => ?_⟩
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
  have hWUq : ∀ s ∈ Icc (0 : ℝ) q', segDriver (travAllInf R Lv r' η ψ' ω) s.toNNReal = WU s := fun s hs =>
    hWUeq s ⟨hs.1, hs.2.trans (by exact_mod_cast hq't.le)⟩
  have hwRe : seedRInf R Lv r' η ψ' q' ω = chartAR WU q' := seedR_eq hWU hWUq
  have hwLe : seedLInf R Lv r' η ψ' q' ω = chartAL WU q' := seedL_eq hWU hWUq
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
      (curChartInf A' R Lv r' η ψ' n' qT.toNNReal ω).2.1 z ∈ ((curChartInf A' R Lv r' η ψ' n' q' ω).dom : Set ℂ) := by
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
      ‖(curChartInf A' R Lv r' η ψ' n' qT.toNNReal ω).1 ((curChartInf A' R Lv r' η ψ' n' q' ω).2.1 w)‖ ≤ ρ := by
    filter_upwards [self_mem_nhdsWithin, nhdsWithin_le_nhds (ball_mem_nhds (0 : ℂ) (half_pos hρ0))] with w hwH hwb
    rw [← hIE hwH]
    show ‖(curChartInf A' R Lv r' η ψ' n' qT.toNNReal ω).1 (E₀' (extendFrom H (fwdMapInv WU q') w))‖ ≤ ρ
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
    have hn : EI₀ tξ ∉ ((curChartInf A' R Lv r' η ψ' n' qT.toNNReal ω).dom : Set ℂ) := fun h => hpξO (hI₀O h)
    rw [hI₀dom] at hn
    have hH := (hψc' ω hω').2.mapsTo htξU
    have : ψ' ω (EI₀ tξ) ∈ fwdHull WU qT := by
      by_contra hk; exact hn ⟨htξU, hH, hk⟩
    exact QuantumZipper.fwdHull_mono.1 hq'lo'.le this
  obtain ⟨θy, hθy, hpyθ⟩ := harcR ty (by linarith)
  obtain ⟨hNC1, hNC2⟩ := R6Fd.nonCorner_of_right_openInf hcf.conf hcf'.conf hcf'.seed hθy
  rw [← hpyθ] at hNC1 hNC2
  have hpyU : EI₀ ty ∈ closure (cfPocket (R ω) (Lv ω) r') := frontier_subset_closure hNC1
  obtain ⟨εy, hεy, hεyU⟩ := inter_ball_subset_of_noncornerInf hJ (hCo' ω hω') hsub hpyU
    (closure_mono hsub hpyU) hNC2
  have hψ'py : ψ' ω (EI₀ ty) = extendFrom H (fwdMapInv WU qT) (ty : ℂ) :=
    jordan_comp_extInf hJ' hE₀' hE₀'c hE₀'m (hFTm (real_mem_Hbar ty))
  have hpyAlive : ψ' ω (EI₀ ty) ∉ closure (fwdHull WU qT) := by
    rw [hψ'py]; exact alive_of_not_mem_Icc hηU hWU hWU0 hqT0 (Or.inl (by linarith))
  have hIncl₀ : cfPocket (R ω) (Lv ω) r' ∩ ψ' ω ⁻¹' (H \ fwdHull WU qT) ⊆
      cfPocket (R ω) (L ω) r ∩ ψ ω ⁻¹' (H \ fwdHull WC q) := by
    rw [← hI₀dom, ← hOdom]; exact hI₀O
  have hOU : ∀ w ∈ ((curChartInf A R L r η ψ n q ω).dom : Set ℂ), w ∈ cfPocket (R ω) (Lv ω) r' →
      w ∈ ((curChartInf A' R Lv r' η ψ' n' qT.toNNReal ω).dom : Set ℂ) := fun w hwO hwU => hid ⟨hwO, hwU⟩
  have hpyCalive : ψ ω (EI₀ ty) ∉ closure (fwdHull WC q) := by
    obtain ⟨ρy, hρy, hρysub⟩ := exists_ball_subset_of_aliveInf hJ' (hE₀'m (hFTm (real_mem_Hbar ty))) hpyAlive
    refine notMem_closure_of_ball_subsetInf hJ (QuantumZipper.fwdHull_mono.2 _) (hEI₀C ty (real_mem_Hbar ty))
      (lt_min hρy hεy) fun z hz => ?_
    have hzU : z ∈ cfPocket (R ω) (Lv ω) r' := hεyU ⟨hz.1, ball_subset_ball (min_le_right _ _) hz.2⟩
    exact hIncl₀ (hρysub ⟨hzU, ball_subset_ball (min_le_left _ _) hz.2⟩)
  -- dead and alive in the outer chart
  have hdeadO : ∀ x : ℝ, EO x = EI₀ tξ → vL 0 < x ∧ x ≤ vR 0 := by
    intro x hx
    rw [hvLv, hvL, hvR', hvR]
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
    rw [hvLv, hvL, hvR', hvR]
    by_contra hxI
    push Not at hxI
    have hψx : ψ ω (EO x) = extendFrom H (fwdMapInv WC q) (x : ℂ) :=
      jordan_comp_extInf hJ hE₀ hE₀c hE₀m (hFm (real_mem_Hbar x))
    rw [hx] at hψx
    exact hpyCalive (hψx ▸ dead_of_mem_Icc hηC hWC hWC0 hq0' (hvL0.trans hvR0) hxI)
  -- dead and alive in the later inner chart
  have hdeadI : ∀ x : ℝ, E₀' (extendFrom H (fwdMapInv WU q') (x : ℂ)) = EI₀ tξ → wL 0 < x ∧ x < wR 0 := by
    intro x hx
    rw [hwLv, hwLe, hwR', hwRe]
    have hψx : ψ' ω (E₀' (extendFrom H (fwdMapInv WU q') (x : ℂ))) = extendFrom H (fwdMapInv WU q') (x : ℂ) :=
      jordan_comp_extInf hJ' hE₀' hE₀'c hE₀'m (hF'm (real_mem_Hbar x))
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
  have hfar : ∀ p ∈ closure (cfPocket (R ω) (Lv ω) r'), d₀ ≤ dist p tip →
      ψ' ω p ∉ S := by
    rintro p hp hpd ⟨z, hz, hze⟩
    have hpe : EI₀ z = p := by
      show E₀' (extendFrom H (fwdMapInv WU qT) z) = p
      have hze' : extendFrom H (fwdMapInv WU qT) z = ψ' ω p := hze
      rw [hze']; exact R6Fd.extension_psi_eqInf hJ' hE₀' hE₀'c hp
    have := hρnear z hz.1 (by simpa [mem_closedBall, dist_zero_right] using hz.2)
    rw [hpe] at this
    linarith
  have haliveI : ∀ x : ℝ, E₀' (extendFrom H (fwdMapInv WU q') (x : ℂ)) = EI₀ ty → x < wL 0 ∨ wR 0 < x := by
    intro x hx
    rw [hwLv, hwLe, hwR', hwRe]
    by_contra hxI
    push Not at hxI
    have hψx : ψ' ω (E₀' (extendFrom H (fwdMapInv WU q') (x : ℂ))) = extendFrom H (fwdMapInv WU q') (x : ℂ) :=
      jordan_comp_extInf hJ' hE₀' hE₀'c hE₀'m (hF'm (real_mem_Hbar x))
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
      ((curChartInf A R L r η ψ n q ω).dom : Set ℂ) ∩ ball p ε₁ ⊆ cfPocket (R ω) (Lv ω) r' →
      ∃ ε > 0, ((curChartInf A R L r η ψ n q ω).dom : Set ℂ) ∩ ball p ε ⊆
        ((curChartInf A' R Lv r' η ψ' n' q' ω).dom : Set ℂ) := by
    intro p hpd ε₁ hε₁ hsubU
    refine ⟨min ε₁ (d₀ / 2), lt_min hε₁ (half_pos hd₀pos), fun w hw => ?_⟩
    have hwU := hsubU ⟨hw.1, ball_subset_ball (min_le_left _ _) hw.2⟩
    have hwI := hOU w hw.1 hwU
    have hz := hI₀c.fwd_mem hwI
    have hwe : (curChartInf A' R Lv r' η ψ' n' qT.toNNReal ω).2.1 ((curChartInf A' R Lv r' η ψ' n' qT.toNNReal ω).1
        w) = w :=
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
      ((curChartInf A' R Lv r' η ψ' n' q' ω).dom : Set ℂ) := by
    obtain ⟨ε₁, hε₁, hε₁U⟩ := Metric.isOpen_iff.1 (hCo' ω hω') _ htξU
    exact hloc _ (min_le_left _ _) ε₁ hε₁ fun w hw => hε₁U hw.2
  have hlocy := hloc _ (min_le_right _ _) εy hεy fun w hw => by
    rw [hOdom] at hw
    exact hεyU ⟨hw.1.1, hw.2⟩
  -- the bound of the later inner coordinate near the inner landings
  obtain ⟨C₀', hC₀'⟩ := exists_norm_fwdMapInv_sub_le hWU hWU0 q'.coe_nonneg
  have hbddI : ∀ t ∈ Ioo a (chartAR WU qT), ∃ ε > 0, ∃ M : ℝ,
      ∀ w ∈ ((curChartInf A' R Lv r' η ψ' n' q' ω).dom : Set ℂ) ∩ ball (EI₀ t) ε,
        ‖(curChartInf A' R Lv r' η ψ' n' q' ω).1 w‖ ≤ M := by
    intro t _
    have hpU := hE₀'m (hFTm (real_mem_Hbar t))
    obtain ⟨ε, hε, hεψ⟩ := Metric.continuousWithinAt_iff.1 (hJ'.1 _ hpU) 1 one_pos
    refine ⟨ε, hε, ‖ψ' ω (EI₀ t)‖ + 1 + C₀', fun w hw => ?_⟩
    have hwI := hw.1
    rw [hIdom] at hwI
    rw [hIfwd _ hwI.1]
    have h1 := norm_fwdMap_le hWU hWU0 q'.coe_nonneg hC₀' hwI.2
    have hwx : w ∈ closure (cfPocket (R ω) (Lv ω) r') := subset_closure hwI.1
    have h2 := hεψ hwx (mem_ball.1 hw.2)
    rw [dist_eq_norm] at h2
    have h3 := norm_le_norm_add_norm_sub' (ψ' ω w) (ψ' ω (EI₀ t))
    linarith
  exact r6FaceR_left_of_reflection hOc hI₀c hIc hI₀O hIncl hOE hOEc hI₀E hI₀Ec hIE hIEc hwR0 hnot hbdd hdrv hρ0
    hinc hinc0 h2ρ (by linarith [htξ.1]) (by linarith) hdeadO haliveO hdeadI haliveI (by rw [hwLv, hwLe]; exact hwL0')
    hρσ hlocξ hlocy hbddI

section FinalFace

open MeasureTheory ProbabilityTheory
open LQGMetric (DistOn)
open QuantumZipper (chiC)
open scoped Real
open WholeField R7Outer R7Leaves R6Nest R6Rel R6Cert PocketMarks PocketSeedOpen PocketStopWallsFin PocketStopSide

universe u

/-- **R.6's face, shape `TwoInf` (outer pocket opening at the flow seed, bounded outer inner pocket), PROVED**
from the reverse visits of `M_L` (Prop. 4.11 and Lemma 4.7 through `OuterIn.ae_walls_r7`). -/
theorem r6FaceSTwoInfRemaining_of_walls {k rL rR c c' : ℝ} (h411 : Sec5.Cond44Ref.Prop411QStatement.{u})
    (h47 : Sec5.Prop411Q.Lemma47QHitStatement.{u})
    (h47T : ∀ θ : ℝ, -(π / 2) < θ → θ < π / 2 → Sec5.RestartGen.Lemma47QHitTStatement.{u} θ)
    (hk4 : 4 < k) (hc : 0 ≤ c) (hc' : 0 ≤ c') : R6Two.R6FaceSTwoInfRemaining.{u} k rL rR c c' := by
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
  have hcfg' : ∀ ω ∈ A', IsOuterCfg (R ω) (ML ω) (StripSys.rt s) (fun t : ℝ => W' t.toNNReal ω) (η ω) :=
    fun ω hω => (hA' ω hω).1
  have hψ' : ∀ ω ∈ A', IsCfJordan (R ω) (ML ω) (StripSys.rt s) (ψ' ω) := fun ω hω => (hA' ω hω).2
  have hP'o := (hcfg' ω hωA').toPocket (hψ' ω hωA')
  have hqT0 : 0 ≤ innerRelCap R ML (StripSys.rt s) η ψ' (outerFibreEndInf R L r η ψ (StripSys.rt q) ω) ω :=
    (SideVis.erasure_relCap_pos_lt_of_visit hP'o.erase hP'o.driven (hP'o.erase.mem_visitSet hT0 htip)).1.le
  obtain ⟨εW, hεW, hpkg⟩ := two_faceInf (n := n) (n' := n') (fun ω hω => (hA ω hω).1) (fun ω hω => (hA ω hω).2)
    hcfg' hψ' hωA hωA' hrev hq0' hqlive hsub hT0 htip
  refine ⟨εW, hεW, fun q' hlo hhi hlive _ hincl => ?_⟩
  have hrt' : ((StripSys.rt q' : ℝ≥0) : ℝ) = q' := Real.coe_toNNReal _ (hqT0.trans hlo.le)
  have hγ' : IsDrivenCurve (travAll R ML (StripSys.rt s) η ψ' ω) := ((hcfg' ω hωA').props (hψ' ω hωA')).1
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
    rfl rfl

/-- **R.6's face, shape `TwoInfInf` (both pockets opening at the flow seed), PROVED** from the reverse visits
of `M_L` (Prop. 4.11 and Lemma 4.7 through `OuterIn.ae_walls_r7`). -/
theorem r6FaceSTwoInfInfRemaining_of_walls {k rL rR c c' : ℝ} (h411 : Sec5.Cond44Ref.Prop411QStatement.{u})
    (h47 : Sec5.Prop411Q.Lemma47QHitStatement.{u})
    (h47T : ∀ θ : ℝ, -(π / 2) < θ → θ < π / 2 → Sec5.RestartGen.Lemma47QHitTStatement.{u} θ)
    (hk4 : 4 < k) (hc : 0 ≤ c) (hc' : 0 ≤ c') : R6Two.R6FaceSTwoInfInfRemaining.{u} k rL rR c c' := by
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
  have hcfg' : ∀ ω ∈ A', IsOuterCfgInf (R ω) (ML ω) (StripSys.rt s) (fun t : ℝ => W' t.toNNReal ω) (η ω) :=
    fun ω hω => (hA' ω hω).1
  have hψ' : ∀ ω ∈ A', IsCfJordanInf (R ω) (ML ω) (StripSys.rt s) (ψ' ω) := fun ω hω => (hA' ω hω).2
  have hP'o := (hcfg' ω hωA').toPocketInf (hψ' ω hωA')
  have hqT0 : 0 ≤ innerRelCapInf R ML (StripSys.rt s) η ψ' (outerFibreEndInf R L r η ψ (StripSys.rt q) ω) ω :=
    (SideVis.erasureInf_relCap_pos_lt_of_visit hP'o.erase hP'o.driven (hP'o.erase.mem_visitSet hT0 htip)).1.le
  obtain ⟨εW, hεW, hpkg⟩ := two_faceInfInf (n := n) (n' := n') (fun ω hω => (hA ω hω).1) (fun ω hω => (hA ω hω).2)
    hcfg' hψ' hωA hωA' hrev hq0' hqlive hsub hT0 htip
  refine ⟨εW, hεW, fun q' hlo hhi hlive _ hincl => ?_⟩
  have hrt' : ((StripSys.rt q' : ℝ≥0) : ℝ) = q' := Real.coe_toNNReal _ (hqT0.trans hlo.le)
  have hγ' : IsDrivenCurve (travAllInf R ML (StripSys.rt s) η ψ' ω) := ((hcfg' ω hωA').props (hψ' ω hωA')).1
  have hcO := (R5Phase.shiftChart_dom_facts (n := n)
    (fun ω hω => isOpen_image_negInv' (hA ω hω).1.conf.isOpen_changePocket (hA ω hω).1.conf.changePocket_subset_H)
    (fun ω hω => PocketJordan.image_negInv_subset_H (hA ω hω).1.conf.changePocket_subset_H)
    (fun ω hω => (hA ω hω).2.2.2.2.1) ω hωA).1
  have hcI := (R5Phase.shiftChart_dom_facts (n := n')
    (fun ω hω => isOpen_image_negInv' (hcfg' ω hω).conf.isOpen_changePocket (hcfg' ω hω).conf.changePocket_subset_H)
    (fun ω hω => PocketJordan.image_negInv_subset_H (hcfg' ω hω).conf.changePocket_subset_H)
    (fun ω hω => (hψ' ω hω).2.2.2.1) ω hωA').1
  rw [R6Fc.pocketSetInf_eq hωA hqlive hγ hcO, R6Fc.pocketSetInf_eq hωA' hlive hγ' hcI]
  exact hpkg (StripSys.rt q') (by rw [hrt']; exact hlo) (by rw [hrt']; exact hhi) hincl _ _ _ _ _ _ _ _ rfl rfl rfl
    rfl rfl

end FinalFace

end InteractingSLE.Sec7.R6Cor
