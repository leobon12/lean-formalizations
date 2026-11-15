/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.R6TrFromFacts
import InteractingSLE.Spec.Sec7.R6TnOuter
import InteractingSLE.Spec.Sec7.R6FcWireInfInf

/-! # Actual inner relative chains at a strict original visit -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Filter Topology Metric
open QuantumZipper (H Hbar fwdMapInv)
open scoped NNReal ENNReal

namespace InteractingSLE.Sec7.R6Tr

open PocketStop PocketStopSide PocketTraversal Lemma71C R6Fc R6Two HOuter PocketSeedOpen
open Sec6 PocketJordan PocketCoord PocketCoupling PocketStopField PocketWordAssembly R6Safe R6Cert R6Nest R6Rel

variable {Ω : Type*} {A : Set Ω} {R L : Ω → ℝ≥0 → ℂ} {r : ℝ≥0}
  {W : Ω → ℝ → ℝ} {η : Ω → ℝ → ℂ} {ψ : Ω → ℂ → ℂ} {n : Ω → ℤ} {ω : Ω}

/-- Finite outgoing target. All fields of `InnerChain`, including the
actual geometric force mark, are proved from the existing chart and
erasure theorems. There is no landing or non-corner input. -/
theorem innerChain_of_visit
    (hcfg : ∀ ω ∈ A, IsOuterCfg (R ω) (L ω) r (W ω) (η ω))
    (hψ : ∀ ω ∈ A, IsCfJordan (R ω) (L ω) r (ψ ω)) (hω : ω ∈ A)
    {T : ℝ} (hT : 0 ≤ T) (htip : η ω T ∈ cfPocket (R ω) (L ω) r) :
    ∃ M : InnerChain (cfPocket (R ω) (L ω) r)
        (closure (cfPocket (R ω) (L ω) r) \ {cfPt (openPt (R ω) (L ω) r)})
        (fun q => currentChart A R L r η ψ n q.toNNReal ω) (η ω T),
      M.time = innerRelCap R L r η ψ T ω ∧ ∀ q ∈ Ico M.time (M.time + M.horizon),
        R6Tn.leftSeed (travAll R L r η ψ) q.toNNReal ω = WangWu.chartAL M.driver q := by
  have hP := (hcfg ω hω).toPocket (hψ ω hω)
  have hv := hP.erase.mem_visitSet hT htip
  have hγ : IsDrivenCurve (travAll R L r η ψ ω) := hP.driven
  obtain ⟨hpos, hlive⟩ := SideVis.erasure_relCap_pos_lt_of_visit hP.erase hP.driven hv
  let qT : ℝ≥0 := (innerRelCap R L r η ψ T ω).toNNReal
  have hqTc : (qT : ℝ) = innerRelCap R L r η ψ T ω := Real.coe_toNNReal _ hpos.le
  have hqpos : 0 < qT := by rw [← NNReal.coe_pos, hqTc]; exact hpos
  have hqLive : (qT : ℝ≥0∞) < capLife (travAll R L r η ψ ω) := by
    rw [← ENNReal.ofReal_coe_nnreal, hqTc]; exact hlive
  obtain ⟨t₁, hqt, ht₁⟩ := ENNReal.lt_iff_exists_nnreal_btwn.1 hqLive
  have hqt' : qT < t₁ := by exact_mod_cast hqt
  have hb : Bornology.IsBounded (cfPocket (R ω) (L ω) r) :=
    isBounded_image_negInv (PocketMarks.zero_notMem_closure_of_rightLo_pos (hcfg ω hω).conf (hcfg ω hω).bounded)
  obtain ⟨E₀, hE₀, -, -, WI, hWI, hWI0, hWIeq, ηI, hηI, hηIeq, hFacts⟩ :=
    chart_facts (n := n) (fun ω hω => (hcfg ω hω).erase.isOpen)
      (fun ω hω => ((hcfg ω hω).toPocket (hψ ω hω)).subset_H)
      (fun ω hω => (hψ ω hω).2.2.2.1) hb (hcfg ω hω).conf.cfPt_openPt_notMem (hψ ω hω) hω hγ ht₁
  have htrace : capTrace (travAll R L r η ψ ω) qT = ψ ω (η ω T) := capTrace_relCap_outer_of_visit hP hv
  have hFtip : extendFrom H (fwdMapInv WI qT) (0 : ℂ) = ψ ω (η ω T) := by
    have hlim := hηI.tendsto_fwdMapInv_tip hWI hWI0 qT.coe_nonneg
    rw [extendFrom_eq (by rw [closure_H]; exact real_mem_Hbar 0) hlim,
      hηIeq qT qT.coe_nonneg (by exact_mod_cast hqt'.le)]
    exact htrace
  have hEtip : E₀ (extendFrom H (fwdMapInv WI qT) 0) = η ω T := by
    rw [hFtip, hE₀ ((hψ ω hω).2.2.2.1.2.mapsTo htip)]
    exact (hψ ω hω).2.2.2.1.2.injOn.leftInvOn_invFunOn htip
  obtain ⟨M, hMt, hmarks⟩ := innerChain_of_facts
    (P := closure (cfPocket (R ω) (L ω) r) \ {cfPt (openPt (R ω) (L ω) r)}) (hψ ω hω).2.2.2.1
    (fun z hz => ⟨subset_closure hz, fun heq => (hcfg ω hω).conf.cfPt_openPt_notMem (heq ▸ hz)⟩)
    (hψ ω hω).1 hE₀ hWI hWI0 hqpos hqt' hWIeq hEtip hFacts
  exact ⟨M, hMt.trans hqTc, hmarks⟩

/-- Infinite outgoing target; the real-window construction is the
same and its compact interval never reaches the pole at infinity. -/
theorem innerChain_of_visitInf
    (hcfg : ∀ ω ∈ A, IsOuterCfgInf (R ω) (L ω) r (W ω) (η ω))
    (hψ : ∀ ω ∈ A, IsCfJordanInf (R ω) (L ω) r (ψ ω)) (hω : ω ∈ A)
    {T : ℝ} (hT : 0 ≤ T) (htip : η ω T ∈ cfPocket (R ω) (L ω) r) :
    ∃ M : InnerChain (cfPocket (R ω) (L ω) r) (closure (cfPocket (R ω) (L ω) r))
        (fun q => currentChartInf A R L r η ψ n q.toNNReal ω) (η ω T),
      M.time = innerRelCapInf R L r η ψ T ω ∧ ∀ q ∈ Ico M.time (M.time + M.horizon),
        R6Tn.leftSeed (travAllInf R L r η ψ) q.toNNReal ω = WangWu.chartAL M.driver q := by
  have hP := (hcfg ω hω).toPocketInf (hψ ω hω)
  have hv := hP.erase.mem_visitSet hT htip
  have hγ : IsDrivenCurve (travAllInf R L r η ψ ω) := hP.driven
  obtain ⟨hpos, hlive⟩ := SideVis.erasureInf_relCap_pos_lt_of_visit hP.erase hP.driven hv
  let qT : ℝ≥0 := (innerRelCapInf R L r η ψ T ω).toNNReal
  have hqTc : (qT : ℝ) = innerRelCapInf R L r η ψ T ω := Real.coe_toNNReal _ hpos.le
  have hqpos : 0 < qT := by rw [← NNReal.coe_pos, hqTc]; exact hpos
  have hqLive : (qT : ℝ≥0∞) < capLife (travAllInf R L r η ψ ω) := by
    rw [← ENNReal.ofReal_coe_nnreal, hqTc]; exact hlive
  obtain ⟨t₁, hqt, ht₁⟩ := ENNReal.lt_iff_exists_nnreal_btwn.1 hqLive
  have hqt' : qT < t₁ := by exact_mod_cast hqt
  obtain ⟨E₀, hE₀, -, -, WI, hWI, hWI0, hWIeq, ηI, hηI, hηIeq, hFacts⟩ :=
    chart_factsInf (n := n) (fun ω hω => (hcfg ω hω).erase.isOpen)
      (fun ω hω => ((hcfg ω hω).toPocketInf (hψ ω hω)).subset_H)
      (fun ω hω => (hψ ω hω).2.2.2.1) (hψ ω hω) hω hγ ht₁
  have htrace : capTrace (travAllInf R L r η ψ ω) qT = ψ ω (η ω T) := capTrace_relCapInf_outer_of_visit hP hv
  have hFtip : extendFrom H (fwdMapInv WI qT) (0 : ℂ) = ψ ω (η ω T) := by
    have hlim := hηI.tendsto_fwdMapInv_tip hWI hWI0 qT.coe_nonneg
    rw [extendFrom_eq (by rw [closure_H]; exact real_mem_Hbar 0) hlim,
      hηIeq qT qT.coe_nonneg (by exact_mod_cast hqt'.le)]
    exact htrace
  have hEtip : E₀ (extendFrom H (fwdMapInv WI qT) 0) = η ω T := by
    rw [hFtip, hE₀ ((hψ ω hω).2.2.2.1.2.mapsTo htip)]
    exact (hψ ω hω).2.2.2.1.2.injOn.leftInvOn_invFunOn htip
  obtain ⟨M, hMt, hmarks⟩ := innerChain_of_facts
    (P := closure (cfPocket (R ω) (L ω) r)) (hψ ω hω).2.2.2.1 subset_closure
    (hψ ω hω).1 hE₀ hWI hWI0 hqpos hqt' hWIeq hEtip hFacts
  exact ⟨M, hMt.trans hqTc, hmarks⟩

end InteractingSLE.Sec7.R6Tr
