/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.R6LandTrace
import InteractingSLE.Spec.Sec7.R6TnOuter

/-!
# R.6: the actual outer left force mark is a visited extremal point

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

/-- The left force mark of a bounded outer current chart lands at a
visited physical point and minimizes the initial coordinate among its
relative trace's real contacts. This is the actual chart of the
`Two` landing-patch input, with the entrance corner allowed. -/
theorem outer_left_force_spec
    (hcfg : ∀ ω ∈ A, IsOuterCfg (R ω) (L ω) r (W ω) (η ω))
    (hψ : ∀ ω ∈ A, IsCfJordan (R ω) (L ω) r (ψ ω)) (hω : ω ∈ A)
    (hq0 : 0 < q) (hq : (q : ℝ≥0∞) < capLife (travAll R L r η ψ ω))
    (htip : capTrace (travAll R L r η ψ ω) q ∈ H) :
    let p := extendFrom H (R6Fc.curChart A R L r η ψ n q ω).2.1
      (R6Fc.seedL R L r η ψ q ω : ℂ)
    p ∈ (fun u => relTip R L r η u ω) '' Icc 0 (capInv (travAll R L r η ψ ω) q) ∧
      p ∈ η ω '' Icc 0 (outerFibreEnd R L r η ψ q ω) ∧
      IsLeast {y : ℝ | ∃ t ∈ Icc (0 : ℝ) q,
        (capTrace (travAll R L r η ψ ω) t.toNNReal).im = 0 ∧
        y = (capTrace (travAll R L r η ψ ω) t.toNNReal).re} (ψ ω p).re := by
  let γ := travAll R L r η ψ ω
  have hcf := hcfg ω hω
  have hJ := hψ ω hω
  have hγ : IsDrivenCurve γ := (hcf.props hJ).1
  obtain ⟨t₁, hqt₁, ht₁⟩ := ENNReal.lt_iff_exists_nnreal_btwn.1 hq
  have hqt₁' : q < t₁ := by exact_mod_cast hqt₁
  obtain ⟨E₀, hE₀, hE₀c, hE₀m, WC, hWC, hWC0, hWCeq, ζ, hζ, hζeq, hfacts⟩ :=
    R6Fc.chart_facts (n := n) (fun ω hω => (hcfg ω hω).erase.isOpen)
      (fun ω hω => ((hcfg ω hω).toPocket (hψ ω hω)).subset_H)
      (fun ω hω => (hψ ω hω).2.2.2.1)
      (isBounded_image_negInv (PocketMarks.zero_notMem_closure_of_rightLo_pos hcf.conf hcf.bounded))
      hcf.conf.cfPt_openPt_notMem hJ hω hγ ht₁
  obtain ⟨-, -, -, hE, hEc⟩ := hfacts q hqt₁'
  have hq0' : (0 : ℝ) < q := by exact_mod_cast hq0
  have hcode : ∀ t ∈ Icc (0 : ℝ) q,
      ζ t = ψ ω (relTip R L r η (capInv γ t) ω) := fun t ht =>
    hζeq t ht.1 (ht.2.trans (by exact_mod_cast hqt₁'.le))
  have hcomp : ∀ z ∈ Hbar, ψ ω (E₀ z) = z := fun z hz =>
    R6Fc.jordan_comp_ext hJ hE₀ hE₀c hE₀m hz
  have hsign : chartAL WC q < chartAR WC q := by
    have hz : extendFrom H (fwdMapInv WC q) ((0 : ℝ) : ℂ) ∈ H := by
      rw [extendFrom_eq (by rw [QuantumZipper.CA.Car.closure_H_eq_Hbar]; exact R6Fc.real_mem_Hbar 0)
        (by simpa only [Complex.ofReal_zero] using hζ.tendsto_fwdMapInv_tip hWC hWC0 q.coe_nonneg)]
      rw [hζeq q q.coe_nonneg (by exact_mod_cast hqt₁'.le)]
      exact htip
    exact (R6Fc.chartAL_neg_of_tip hζ hWC hWC0 q.coe_nonneg hz).trans
      (R6Fc.chartAR_pos_of_tip hζ hWC hWC0 q.coe_nonneg hz)
  have hΓ : MapsTo (fun t => relTip R L r η (capInv γ t) ω)
      (Icc (0 : ℝ) q) (closure (cfPocket (R ω) (L ω) r) \ {cfPt (openPt (R ω) (L ω) r)}) := by
    intro t _
    have hcorner : cfArcR (R ω) (L ω) r 0 = cfPt (openPt (R ω) (L ω) r) := by
      simp only [cfArcR, zero_mul, add_zero]
      rfl
    rw [← hcorner]
    exact hcf.erase.erasedPath_mem (clockOf_mem_Ico hcf.erase.clock_σ_pos (capInv_nonneg γ t))
  have hspec := physical_left_force_spec hζ hWC hWC0 hq0' hsign hJ.2.1 hΓ hcode
    hE₀m hcomp hE hEc
  have hseed : R6Fc.seedL R L r η ψ q ω = chartAL WC q := R6Fc.seedL_eq hWC
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
    refine ⟨_, ⟨hcf.erase.nonneg.trans (hcf.erase.fibre_mem _).1, ?_⟩, rfl⟩
    exact hcf.erase.monotone_fibre ((strictMonoOn_clockOf hcf.erase.clock_σ_pos).monotoneOn
      (capInv_nonneg γ t) (capInv_nonneg γ q) hcap)
  · convert hspec.2 using 1
    ext y
    constructor
    · rintro ⟨s, hs, him, hy⟩
      refine ⟨s, hs, ?_, ?_⟩
      · simpa only [capTrace, Real.coe_toNNReal _ hs.1, γ, travAll, cfTraversal, trav, relCurve,
          relTip] using him
      · simpa only [capTrace, Real.coe_toNNReal _ hs.1, γ, travAll, cfTraversal, trav, relCurve,
          relTip] using hy
    · rintro ⟨s, hs, him, hy⟩
      refine ⟨s, hs, ?_, ?_⟩
      · simpa only [capTrace, Real.coe_toNNReal _ hs.1, γ, travAll, cfTraversal, trav, relCurve,
          relTip] using him
      · simpa only [capTrace, Real.coe_toNNReal _ hs.1, γ, travAll, cfTraversal, trav, relCurve,
          relTip] using hy

end InteractingSLE.Sec7.R6Land
