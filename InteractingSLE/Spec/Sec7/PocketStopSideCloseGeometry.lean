/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.PocketStopSideFinalGeometry
import Mathlib.Topology.ExtendFrom

/-!
# Finite inverse landings for a bounded Jordan pocket

PROVE-STRIPSYS38. A bounded Jordan coordinate already supplies the incoming
inverse extension previously left as `hJordanInverse`. Compactness gives cluster
points; the pole excludes the terminal corner and boundary injectivity makes the
cluster point unique. The extension is the ordinary `extendFrom` of the inverse.
-/

set_option autoImplicit false

noncomputable section

open Set Filter Topology Metric Bornology
open QuantumZipper (H Hbar)
open scoped NNReal ENNReal

namespace InteractingSLE.Sec7.PocketStopSide

/-- A bounded Jordan coordinate has a finite continuous inverse on the closed
half-plane, taking no finite value at the terminal pole. -/
theorem exists_inverse_extension_of_jordan_coord {C : Set ℂ} {x₀ y₀ : ℂ}
    {ψ : ℂ → ℂ} (hCb : IsBounded C) (hx₀ : x₀ ∉ C)
    (hψ : Sec6.IsJordanCoord C x₀ y₀ ψ) {c : Chart} (hc : c.IsConformal)
    (hdom : (c.dom : Set ℂ) = C) (heq : EqOn c.1 ψ C) :
    ∃ E : ℂ → ℂ, EqOn E c.2.1 H ∧ ContinuousOn E Hbar ∧
      MapsTo E Hbar (closure C \ {x₀}) := by
  rcases hψ with ⟨hψc, hψi, -, -, -, -, hψinf⟩
  have hmem : ∀ z ∈ H, c.2.1 z ∈ closure C \ {x₀} := by
    intro z hz
    have hzC : c.2.1 z ∈ C := hdom ▸ hc.inv_mem_dom hz
    exact ⟨subset_closure hzC, fun he => hx₀ (he ▸ hzC)⟩
  have hψe : ∀ z ∈ H, ψ (c.2.1 z) = z := by
    intro z hz
    rw [← heq (hdom ▸ hc.inv_mem_dom hz)]
    exact hc.2.2 z hz
  have hex : ∀ z ∈ Hbar, ∃ p ∈ closure C \ {x₀},
      Tendsto c.2.1 (𝓝[H] z) (𝓝 p) := by
    intro z hz
    have hzcl : z ∈ closure H := by
      rw [QuantumZipper.CA.Car.closure_H_eq_Hbar]
      exact hz
    have : NeBot (𝓝[H] z) := mem_closure_iff_nhdsWithin_neBot.1 hzcl
    have hmapD : map c.2.1 (𝓝[H] z) ≤ 𝓟 (closure C \ {x₀}) :=
      le_principal_iff.2 (eventually_nhdsWithin_of_forall hmem)
    have hmapC : ∀ᶠ w in 𝓝[H] z, c.2.1 w ∈ closure C :=
      (eventually_nhdsWithin_of_forall hmem).mono fun _ hw => hw.1
    have hψmap : Tendsto ψ (map c.2.1 (𝓝[H] z)) (𝓝 z) := by
      apply tendsto_map'_iff.2
      exact (show Tendsto (fun w : ℂ => w) (𝓝[H] z) (𝓝 z) from
        nhdsWithin_le_nhds).congr' (eventually_nhdsWithin_of_forall fun w hw => (hψe w hw).symm)
    have hcluster : ∀ p ∈ closure C, MapClusterPt p (𝓝[H] z) c.2.1 →
        p ≠ x₀ ∧ ψ p = z := by
      intro p hp hcp
      have : NeBot (𝓝 p ⊓ map c.2.1 (𝓝[H] z)) := hcp
      have hsub : 𝓝 p ⊓ map c.2.1 (𝓝[H] z) ≤ 𝓝[closure C \ {x₀}] p :=
        le_inf inf_le_left (inf_le_right.trans hmapD)
      have hψlim : Tendsto ψ (𝓝 p ⊓ map c.2.1 (𝓝[H] z)) (𝓝 z) :=
        hψmap.mono_left inf_le_right
      have hpne : p ≠ x₀ := by
        intro he
        have hesc : Tendsto ψ (𝓝 p ⊓ map c.2.1 (𝓝[H] z)) (cobounded ℂ) :=
          hψinf.mono_left (he ▸ hsub)
        have hbad := (tendsto_inf.2 ⟨hψlim, hesc⟩).neBot
        exact hbad.ne (disjoint_nhds_cobounded z).eq_bot
      exact ⟨hpne, tendsto_nhds_unique
        (((hψc p ⟨hp, hpne⟩).tendsto).mono_left hsub) hψlim⟩
    obtain ⟨p, hp, hcp⟩ := hCb.isCompact_closure.exists_mapClusterPt
      (f := 𝓝[H] z) (u := c.2.1) (le_principal_iff.2 hmapC)
    obtain ⟨hpne, hpψ⟩ := hcluster p hp hcp
    refine ⟨p, ⟨hp, hpne⟩, hCb.isCompact_closure.tendsto_nhds_of_unique_mapClusterPt hmapC ?_⟩
    intro v hv hcv
    obtain ⟨hvne, hvψ⟩ := hcluster v hv hcv
    exact hψi ⟨hv, hvne⟩ ⟨hp, hpne⟩ (hvψ.trans hpψ.symm)
  refine ⟨extendFrom H c.2.1, extendFrom_extends hc.1.continuousOn,
    continuousOn_extendFrom (by rw [QuantumZipper.CA.Car.closure_H_eq_Hbar])
      (fun z hz => ⟨(hex z hz).choose, (hex z hz).choose_spec.2⟩), fun z hz => ?_⟩
  obtain ⟨p, hp, ht⟩ := hex z hz
  rwa [extendFrom_eq (by rw [QuantumZipper.CA.Car.closure_H_eq_Hbar]; exact hz) ht]

open PocketCoord PocketJordan PocketWordAssembly PocketMarks PocketTraversal PocketCoupling
  PocketUnionPt Lemma71C PocketStop PocketStopField

/-- Specialization to the bounded strip change pocket. All inputs here are
already part of its constructed configuration and conformal Jordan chart. -/
theorem exists_inverse_extension_cfPocket {R L : ℝ≥0 → ℂ} {r : ℝ≥0}
    {W : ℝ → ℝ} {ψ : ℂ → ℂ} {η' : ℝ → ℂ}
    (hcfg : IsCfPocketConfig R L r W η') (hψ : IsCfJordan R L r ψ)
    {c : Chart} (hc : c.IsConformal) (hdom : (c.dom : Set ℂ) = cfPocket R L r)
    (heq : EqOn c.1 ψ (cfPocket R L r)) :
    ∃ E : ℂ → ℂ, EqOn E c.2.1 H ∧ ContinuousOn E Hbar ∧
      MapsTo E Hbar (closure (cfPocket R L r) \ {cfPt (openPt R L r)}) := by
  have hp := hcfg.conf.isCfPocket (zero_notMem_closure_of_rightLo_pos hcfg.conf hcfg.bounded)
  exact exists_inverse_extension_of_jordan_coord hp.isBounded hcfg.conf.cfPt_openPt_notMem hψ hc hdom heq

/-- The continuous inverse extension still inverts the Jordan coordinate at every
finite closed-half-plane point. This fixes its initial-seed boundary fibre. -/
theorem inverse_extension_jordan_right_inverse {C : Set ℂ} {x₀ y₀ : ℂ} {ψ E : ℂ → ℂ}
    (hψ : Sec6.IsJordanCoord C x₀ y₀ ψ) {c : Chart} (hc : c.IsConformal)
    (hdom : (c.dom : Set ℂ) = C) (heq : EqOn c.1 ψ C)
    (hE : EqOn E c.2.1 H) (hEc : ContinuousOn E Hbar)
    (hED : MapsTo E Hbar (closure C \ {x₀})) : ∀ z ∈ Hbar, ψ (E z) = z := by
  intro z hz
  have hzcl : z ∈ closure H := by
    rw [QuantumZipper.CA.Car.closure_H_eq_Hbar]
    exact hz
  have : NeBot (𝓝[H] z) := mem_closure_iff_nhdsWithin_neBot.1 hzcl
  have hEt : Tendsto E (𝓝[H] z) (𝓝[closure C \ {x₀}] (E z)) :=
    tendsto_nhdsWithin_iff.2 ⟨((hEc z hz).mono QuantumZipper.H_subset_Hbar).tendsto,
      eventually_nhdsWithin_of_forall fun w hw => hED (QuantumZipper.H_subset_Hbar hw)⟩
  have ht := ((hψ.1 (E z) (hED hz)).tendsto).comp hEt
  have hi : Tendsto (fun w => ψ (E w)) (𝓝[H] z) (𝓝 z) := by
    refine (show Tendsto (fun w : ℂ => w) (𝓝[H] z) (𝓝 z) from
      nhdsWithin_le_nhds).congr' (eventually_nhdsWithin_of_forall fun w hw => ?_)
    change w = ψ (E w)
    rw [hE hw, ← heq (hdom ▸ hc.inv_mem_dom hw), hc.2.2 w hw]
  exact tendsto_nhds_unique ht hi

/-- A nonzero finite point under the inverse extension is not the incoming seed,
which the Jordan coordinate sends to zero. -/
theorem inverse_extension_ne_seed_of_ne_zero {C : Set ℂ} {x₀ y₀ : ℂ} {ψ E : ℂ → ℂ}
    (hψ : Sec6.IsJordanCoord C x₀ y₀ ψ) {c : Chart} (hc : c.IsConformal)
    (hdom : (c.dom : Set ℂ) = C) (heq : EqOn c.1 ψ C)
    (hE : EqOn E c.2.1 H) (hEc : ContinuousOn E Hbar)
    (hED : MapsTo E Hbar (closure C \ {x₀})) {z : ℂ} (hz : z ∈ Hbar) (hz0 : z ≠ 0) :
    E z ≠ y₀ := by
  intro he
  have h := inverse_extension_jordan_right_inverse hψ hc hdom heq hE hEc hED z hz
  rw [he, hψ.2.2.2.2.2.1] at h
  exact hz0 h.symm

/-- The bounded strip pocket supplies the active-domain identity used in the side
comparison; no separate domain-geometry input is needed. -/
theorem activeDom_cfPocket_eq_stopHull {Ω : Type*} {A : Set Ω}
    {R L : Ω → ℝ≥0 → ℂ} {r q : ℝ≥0} {W : Ω → ℝ → ℝ} {ψ : Ω → ℂ → ℂ}
    {η' : Ω → ℝ → ℂ} {c : Ω → Chart} {ω : Ω} (hω : ω ∈ A)
    (hcfg : IsCfPocketConfig (R ω) (L ω) r (W ω) (η' ω))
    (hψ : IsCfJordan (R ω) (L ω) r (ψ ω)) (hc : (c ω).IsConformal)
    (hdom : ((c ω).dom : Set ℂ) = cfPocket (R ω) (L ω) r)
    (heq : EqOn (c ω).1 (ψ ω) (cfPocket (R ω) (L ω) r))
    (hq : (q : ℝ≥0∞) < capLife (travAll R L r η' ψ ω)) :
    activeDom A (travAll R L r η' ψ) c q ω =
      cfPocket (R ω) (L ω) r ∩ (H \ stopHull R L r W η' ψ q ω) := by
  have hP := hcfg.conf.isReversePocket_of_counterflow
    (zero_notMem_closure_of_rightLo_pos hcfg.conf hcfg.bounded)
    hcfg.trace hcfg.continuous_W hcfg.W_zero hcfg.revR hcfg.revL hcfg.visR
  have hψ' : Sec6.IsJordanCoord (cfPocket (R ω) (L ω) r)
      (cfArcR (R ω) (L ω) r 0) (cfArcR (R ω) (L ω) r 1) (ψ ω) := by
    rw [PocketCoord.IsChangeConfigInc.cfArcR_zero, PocketCoord.IsChangeConfigInc.cfArcR_one]
    exact hψ
  exact activeDom_eq_inter (C := fun ω => cfPocket (R ω) (L ω) r)
    (F := stopHull R L r W η' ψ q) (ψ := ψ) hω hq hc hdom heq hψ.2.2.2.1.2.injOn
    (image_inter_domain_ambTime hP hcfg.attach hψ' q.coe_nonneg
      (by rw [ENNReal.ofReal_coe_nnreal]; exact hq))

end InteractingSLE.Sec7.PocketStopSide
