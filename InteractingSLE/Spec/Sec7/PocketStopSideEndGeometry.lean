/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.PocketStopSideCloseGeometry
import InteractingSLE.Spec.Sec7.PocketSeedOpen

/-!
# Finite inverse landings for the pocket opening at infinity

PROVE-STRIPSYS38. Properness at infinity in `IsJordanCoordInf` makes the
preimages of compact sets compact. The bounded-pocket cluster-point argument
therefore applies locally at each finite closed-half-plane point, without
assuming that the pocket is bounded. This removes the incoming inverse-extension
input in the second pocket shape.
-/

set_option autoImplicit false

noncomputable section

open Set Filter Topology Metric Bornology
open QuantumZipper (H Hbar)
open scoped NNReal ENNReal

namespace InteractingSLE.Sec7.PocketStopSide

/-- The properness clause of a Jordan coordinate at infinity supplies compact
preimages in the closed pocket. -/
theorem isCompact_jordan_coordInf_preimage {C : Set ℂ} {y₀ : ℂ} {ψ : ℂ → ℂ}
    (hψ : Sec6.IsJordanCoordInf C y₀ ψ) {K : Set ℂ} (hK : IsCompact K) :
    IsCompact (closure C ∩ ψ ⁻¹' K) := by
  have hbounded : IsBounded (closure C ∩ ψ ⁻¹' K) := by
    have h := mem_inf_principal.1 (hψ.2.2.2.2.2.2 hK.isBounded.compl)
    change (closure C ∩ ψ ⁻¹' K)ᶜ ∈ cobounded ℂ
    convert h using 1
    ext x
    simp only [mem_compl_iff, mem_inter_iff, mem_preimage, not_and, mem_ofPred_eq]
  exact isCompact_iff_isClosed_bounded.2
    ⟨hψ.1.preimage_isClosed_of_isClosed isClosed_closure hK.isClosed, hbounded⟩

/-- An unbounded Jordan pocket with its pole at infinity has a finite continuous
inverse extension at every finite point of the closed half-plane. -/
theorem exists_inverse_extension_of_jordan_coordInf {C : Set ℂ} {y₀ : ℂ}
    {ψ : ℂ → ℂ} (hψ : Sec6.IsJordanCoordInf C y₀ ψ) {c : Chart} (hc : c.IsConformal)
    (hdom : (c.dom : Set ℂ) = C) (heq : EqOn c.1 ψ C) :
    ∃ E : ℂ → ℂ, EqOn E c.2.1 H ∧ ContinuousOn E Hbar ∧ MapsTo E Hbar (closure C) := by
  have hmem : ∀ z ∈ H, c.2.1 z ∈ closure C :=
    fun z hz => subset_closure (hdom ▸ hc.inv_mem_dom hz)
  have hψe : ∀ z ∈ H, ψ (c.2.1 z) = z := by
    intro z hz
    rw [← heq (hdom ▸ hc.inv_mem_dom hz)]
    exact hc.2.2 z hz
  have hex : ∀ z ∈ Hbar, ∃ p ∈ closure C, Tendsto c.2.1 (𝓝[H] z) (𝓝 p) := by
    intro z hz
    have hzcl : z ∈ closure H := by
      rw [QuantumZipper.CA.Car.closure_H_eq_Hbar]
      exact hz
    have : NeBot (𝓝[H] z) := mem_closure_iff_nhdsWithin_neBot.1 hzcl
    let S := closure C ∩ ψ ⁻¹' closedBall z 1
    have hSc : IsCompact S := isCompact_jordan_coordInf_preimage hψ (isCompact_closedBall z 1)
    have hmapS : ∀ᶠ w in 𝓝[H] z, c.2.1 w ∈ S := by
      filter_upwards [self_mem_nhdsWithin,
        (nhdsWithin_le_nhds : 𝓝[H] z ≤ 𝓝 z) (closedBall_mem_nhds z zero_lt_one)] with w hw hwB
      exact ⟨hmem w hw, by change ψ (c.2.1 w) ∈ closedBall z 1; rwa [hψe w hw]⟩
    have hψmap : Tendsto ψ (map c.2.1 (𝓝[H] z)) (𝓝 z) := by
      apply tendsto_map'_iff.2
      exact (show Tendsto (fun w : ℂ => w) (𝓝[H] z) (𝓝 z) from
        nhdsWithin_le_nhds).congr' (eventually_nhdsWithin_of_forall fun w hw => (hψe w hw).symm)
    have hcluster : ∀ p ∈ S, MapClusterPt p (𝓝[H] z) c.2.1 → ψ p = z := by
      intro p hp hcp
      have : NeBot (𝓝 p ⊓ map c.2.1 (𝓝[H] z)) := hcp
      have hsub : 𝓝 p ⊓ map c.2.1 (𝓝[H] z) ≤ 𝓝[closure C] p :=
        le_inf inf_le_left (inf_le_right.trans
          (le_principal_iff.2 (eventually_nhdsWithin_of_forall hmem)))
      exact tendsto_nhds_unique (((hψ.1 p hp.1).tendsto).mono_left hsub)
        (hψmap.mono_left inf_le_right)
    obtain ⟨p, hp, hcp⟩ := hSc.exists_mapClusterPt
      (f := 𝓝[H] z) (u := c.2.1) (le_principal_iff.2 hmapS)
    have hpψ := hcluster p hp hcp
    refine ⟨p, hp.1, hSc.tendsto_nhds_of_unique_mapClusterPt hmapS ?_⟩
    intro v hv hcv
    exact hψ.2.1 hv.1 hp.1 ((hcluster v hv hcv).trans hpψ.symm)
  refine ⟨extendFrom H c.2.1, extendFrom_extends hc.1.continuousOn,
    continuousOn_extendFrom (by rw [QuantumZipper.CA.Car.closure_H_eq_Hbar])
      (fun z hz => ⟨(hex z hz).choose, (hex z hz).choose_spec.2⟩), fun z hz => ?_⟩
  obtain ⟨p, hp, ht⟩ := hex z hz
  rwa [extendFrom_eq (by rw [QuantumZipper.CA.Car.closure_H_eq_Hbar]; exact hz) ht]

open PocketCoord PocketJordan PocketSeedOpen

/-- Specialization to the strip pocket opening at the flow seed. -/
theorem exists_inverse_extension_cfPocketInf {R L : ℝ≥0 → ℂ} {r : ℝ≥0} {ψ : ℂ → ℂ}
    (hψ : IsCfJordanInf R L r ψ) {c : Chart} (hc : c.IsConformal)
    (hdom : (c.dom : Set ℂ) = cfPocket R L r) (heq : EqOn c.1 ψ (cfPocket R L r)) :
    ∃ E : ℂ → ℂ, EqOn E c.2.1 H ∧ ContinuousOn E Hbar ∧
      MapsTo E Hbar (closure (cfPocket R L r)) :=
  exists_inverse_extension_of_jordan_coordInf hψ hc hdom heq

/-- The incoming inverse-extension obligation is discharged for either strip
pocket shape. The bounded alternative lists only its constructed Jordan data. -/
theorem exists_inverse_extension_of_jordan_cases {C : Set ℂ} {seed : ℂ} {ψ : ℂ → ℂ}
    (hJordan : (∃ pole : ℂ, IsBounded C ∧ pole ∉ C ∧ Sec6.IsJordanCoord C pole seed ψ) ∨
      Sec6.IsJordanCoordInf C seed ψ)
    {c : Chart} (hc : c.IsConformal) (hdom : (c.dom : Set ℂ) = C) (heq : EqOn c.1 ψ C) :
    ∃ E : ℂ → ℂ, EqOn E c.2.1 H ∧ ContinuousOn E Hbar ∧ MapsTo E Hbar (closure C) := by
  rcases hJordan with ⟨pole, hCb, hpole, hψ⟩ | hψ
  · obtain ⟨E, hE, hEc, hED⟩ := exists_inverse_extension_of_jordan_coord hCb hpole hψ hc hdom heq
    exact ⟨E, hE, hEc, fun z hz => (hED hz).1⟩
  · exact exists_inverse_extension_of_jordan_coordInf hψ hc hdom heq

open PocketTraversal Lemma71C PocketStop PocketStopField

/-- If the entry is in H, the two-arc pocket has no finite real corner. In
either Jordan shape every finite relative inverse therefore lands in H, with
no force-mark exclusion. -/
theorem exists_relative_inverse_landing_of_jordan_cases_seed_mem_H
    {Ω : Type*} {c : Ω → Chart} {γ : Ω → ℝ → ℂ} {q : ℝ≥0} {ω : Ω}
    (hγ : IsDrivenCurve (γ ω)) (hq : (q : ℝ≥0∞) < capLife (γ ω))
    {C : Set ℂ} {seed : ℂ} {ψ : ℂ → ℂ}
    (hJordan : (∃ pole : ℂ, IsBounded C ∧ pole ∉ C ∧ Sec6.IsJordanCoord C pole seed ψ) ∨
      Sec6.IsJordanCoordInf C seed ψ)
    (hc : (c ω).IsConformal) (hdom : ((c ω).dom : Set ℂ) = C)
    (heq : EqOn (c ω).1 ψ C) (hclosure : closure C ⊆ H ∪ {seed}) (hseed : seed ∈ H) :
    ∀ ξ : ℝ, ∃ p ∈ H, Tendsto (relChart c γ q ω).2.1 (𝓝[H] (ξ : ℂ)) (𝓝 p) := by
  obtain ⟨E, hE, hEc, hED⟩ := exists_inverse_extension_of_jordan_cases hJordan hc hdom heq
  apply exists_relative_inverse_landing hγ hq hE hEc
  intro z hz
  rcases hclosure (hED hz) with hpH | hpseed
  · exact hpH
  · exact mem_singleton_iff.1 hpseed ▸ hseed

open PocketMarks PocketCoupling PocketUnionPt

/-- The unbounded strip pocket also supplies its active-domain identity directly
from its constructed erasure. -/
theorem activeDom_cfPocketInf_eq_stopHull {Ω : Type*} {A : Set Ω}
    {R L : Ω → ℝ≥0 → ℂ} {r q : ℝ≥0} {W : Ω → ℝ → ℝ} {ψ : Ω → ℂ → ℂ}
    {η : Ω → ℝ → ℂ} {c : Ω → Chart} {ω : Ω} (hω : ω ∈ A)
    (hcfg : IsCfPocketConfigInf (R ω) (L ω) r (W ω) (η ω))
    (hψ : IsCfJordanInf (R ω) (L ω) r (ψ ω)) (hc : (c ω).IsConformal)
    (hdom : ((c ω).dom : Set ℂ) = cfPocket (R ω) (L ω) r)
    (heq : EqOn (c ω).1 (ψ ω) (cfPocket (R ω) (L ω) r))
    (hq : (q : ℝ≥0∞) < capLife (travAllInf R L r η ψ ω)) :
    activeDom A (travAllInf R L r η ψ) c q ω =
      cfPocket (R ω) (L ω) r ∩ (H \ stopHullInf R L r W η ψ q ω) := by
  have hP := hcfg.isReversePocketInf
  have hψ' : Sec6.IsJordanCoordInf (cfPocket (R ω) (L ω) r)
      (cfArcRInf (R ω) (L ω) r 0) (ψ ω) := by
    rw [PocketCoord.IsChangeConfigInc.cfArcRInf_zero]
    exact hψ
  exact activeDom_eq_inter (C := fun ω => cfPocket (R ω) (L ω) r)
    (F := stopHullInf R L r W η ψ q) (ψ := ψ) hω hq hc hdom heq hψ.2.2.2.1.2.injOn
    (image_inter_domain_ambTimeInf hP hcfg.attach hψ' q.coe_nonneg
      (by rw [ENNReal.ofReal_coe_nnreal]; exact hq))

end InteractingSLE.Sec7.PocketStopSide
