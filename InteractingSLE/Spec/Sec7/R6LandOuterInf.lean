/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.R6LandOuter
import InteractingSLE.Spec.Sec7.R6TnOuter

/-!
# R.6: seed-opening outer force landings

PROVE-R6-LANDING. The current chart and force coordinate are precisely
those used by the two-outer landing patches. No reverse-visit order is
assumed on an outer arm. The statement includes the entrance-corner
case; it makes no non-corner or local-incidence claim.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Filter Topology
open QuantumZipper (H Hbar fwdMapInv)
open scoped NNReal ENNReal

namespace InteractingSLE.Sec7.R6Land

open Sec6 PocketTraversal Lemma71C PocketJordan PocketCoord PocketCoupling
  PocketStop PocketStopField HOuter PocketWordAssembly PocketSeedOpen
  PocketStopMarked R6Nest R6Safe
open WangWu (chartAL chartAR)

variable {Ω : Type*} {A : Set Ω} {R L : Ω → ℝ≥0 → ℂ} {r : ℝ≥0}
  {W : Ω → ℝ → ℝ} {η : Ω → ℝ → ℂ} {ψ : Ω → ℂ → ℂ}
  {n : Ω → ℤ} {q : ℝ≥0} {ω : Ω}

/-- The left force mark of a seed-opening outer current chart lands at a
visited physical point and minimizes the initial coordinate among its
relative trace's real contacts. This is the actual chart of the
`TwoInf` and `TwoInfInf` landing-patch inputs, with the entrance corner allowed. -/
theorem outerInf_left_force_spec
    (hcfg : ∀ ω ∈ A, IsOuterCfgInf (R ω) (L ω) r (W ω) (η ω))
    (hψ : ∀ ω ∈ A, IsCfJordanInf (R ω) (L ω) r (ψ ω)) (hω : ω ∈ A)
    (hq0 : 0 < q) (hq : (q : ℝ≥0∞) < capLife (travAllInf R L r η ψ ω))
    (htip : capTrace (travAllInf R L r η ψ ω) q ∈ H) :
    let p := extendFrom H (R6Fc.curChartInf A R L r η ψ n q ω).2.1
      (R6Fc.seedLInf R L r η ψ q ω : ℂ)
    p ∈ (fun u => relTipInf R L r η u ω) '' Icc 0 (capInv (travAllInf R L r η ψ ω) q) ∧
      p ∈ η ω '' Icc 0 (outerFibreEndInf R L r η ψ q ω) ∧
      IsLeast {y : ℝ | ∃ t ∈ Icc (0 : ℝ) q,
        (capTrace (travAllInf R L r η ψ ω) t.toNNReal).im = 0 ∧
        y = (capTrace (travAllInf R L r η ψ ω) t.toNNReal).re} (ψ ω p).re := by
  let γ := travAllInf R L r η ψ ω
  have hcf := hcfg ω hω
  have hJ := hψ ω hω
  have hγ : IsDrivenCurve γ := (hcf.props hJ).1
  obtain ⟨t₁, hqt₁, ht₁⟩ := ENNReal.lt_iff_exists_nnreal_btwn.1 hq
  have hqt₁' : q < t₁ := by exact_mod_cast hqt₁
  obtain ⟨E₀, hE₀, hE₀c, hE₀m, WC, hWC, hWC0, hWCeq, ζ, hζ, hζeq, hfacts⟩ :=
    R6Fc.chart_factsInf (n := n) (fun ω hω => (hcfg ω hω).erase.isOpen)
      (fun ω hω => ((hcfg ω hω).toPocketInf (hψ ω hω)).subset_H)
      (fun ω hω => (hψ ω hω).2.2.2.1)
      hJ hω hγ ht₁
  obtain ⟨-, -, -, hE, hEc⟩ := hfacts q hqt₁'
  have hq0' : (0 : ℝ) < q := by exact_mod_cast hq0
  have hcode : ∀ t ∈ Icc (0 : ℝ) q,
      ζ t = ψ ω (relTipInf R L r η (capInv γ t) ω) := fun t ht =>
    hζeq t ht.1 (ht.2.trans (by exact_mod_cast hqt₁'.le))
  have hcomp : ∀ z ∈ Hbar, ψ ω (E₀ z) = z := fun z hz =>
    R6Fc.jordan_comp_extInf hJ hE₀ hE₀c hE₀m hz
  have hsign : chartAL WC q < chartAR WC q := by
    have hz : extendFrom H (fwdMapInv WC q) ((0 : ℝ) : ℂ) ∈ H := by
      rw [extendFrom_eq (by rw [QuantumZipper.CA.Car.closure_H_eq_Hbar]; exact R6Fc.real_mem_Hbar 0)
        (by simpa only [Complex.ofReal_zero] using hζ.tendsto_fwdMapInv_tip hWC hWC0 q.coe_nonneg)]
      rw [hζeq q q.coe_nonneg (by exact_mod_cast hqt₁'.le)]
      exact htip
    exact (R6Fc.chartAL_neg_of_tip hζ hWC hWC0 q.coe_nonneg hz).trans
      (R6Fc.chartAR_pos_of_tip hζ hWC hWC0 q.coe_nonneg hz)
  have hΓ : MapsTo (fun t => relTipInf R L r η (capInv γ t) ω)
      (Icc (0 : ℝ) q) (closure (cfPocket (R ω) (L ω) r)) := by
    intro t _
    exact hcf.erase.erasedPath_mem (clockOf_mem_Ico hcf.erase.clockEnd_pos (capInv_nonneg γ t))
  have hspec := physical_left_force_spec hζ hWC hWC0 hq0' hsign hJ.2.1 hΓ hcode
    hE₀m hcomp hE hEc
  have hseed : R6Fc.seedLInf R L r η ψ q ω = chartAL WC q := R6Fc.seedL_eq hWC
    (fun t ht => hWCeq t ⟨ht.1, ht.2.trans (by exact_mod_cast hqt₁'.le)⟩)
  dsimp only
  rw [hseed]
  obtain ⟨t, ht, heq⟩ := hspec.1
  have hcap : capInv γ t ≤ capInv γ q :=
    hγ.capInv_le (capInv_nonneg γ q) ht.1 (by
      rw [(hγ.capInv_spec q.coe_nonneg (by simpa only [ENNReal.ofReal_coe_nnreal] using hq)).2]
      exact ht.2)
  refine ⟨⟨capInv γ t, ⟨capInv_nonneg γ t, hcap⟩, heq⟩, ?_, ?_⟩
  · rw [← heq]
    refine ⟨_, ⟨hcf.erase.fibre_nonneg (clockOf_mem_Ico hcf.erase.clockEnd_pos (capInv_nonneg γ t)), ?_⟩, rfl⟩
    exact hcf.erase.monotoneOn_fibre
      (clockOf_mem_Ico hcf.erase.clockEnd_pos (capInv_nonneg γ t))
      (clockOf_mem_Ico hcf.erase.clockEnd_pos (capInv_nonneg γ q))
      ((strictMonoOn_clockOf hcf.erase.clockEnd_pos).monotoneOn
        (capInv_nonneg γ t) (capInv_nonneg γ q) hcap)
  · convert hspec.2 using 1
    ext y
    constructor
    · rintro ⟨s, hs, him, hy⟩
      refine ⟨s, hs, ?_, ?_⟩
      · simpa only [capTrace, Real.coe_toNNReal _ hs.1, γ, travAllInf, cfTraversalInf, travInf, relCurve,
          relTipInf] using him
      · simpa only [capTrace, Real.coe_toNNReal _ hs.1, γ, travAllInf, cfTraversalInf, travInf, relCurve,
          relTipInf] using hy
    · rintro ⟨s, hs, him, hy⟩
      refine ⟨s, hs, ?_, ?_⟩
      · simpa only [capTrace, Real.coe_toNNReal _ hs.1, γ, travAllInf, cfTraversalInf, travInf, relCurve,
          relTipInf] using him
      · simpa only [capTrace, Real.coe_toNNReal _ hs.1, γ, travAllInf, cfTraversalInf, travInf, relCurve,
          relTipInf] using hy

end InteractingSLE.Sec7.R6Land
