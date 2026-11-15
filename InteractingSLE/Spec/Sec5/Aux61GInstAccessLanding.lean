/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec5.Aux61GInstAccessPath

/-! # Selected-access landing from the inverse chart's continuous extension -/

set_option autoImplicit false
noncomputable section
open Set Filter Topology MeasureTheory Metric
open scoped NNReal ENNReal
open QuantumZipper (H Hbar)

namespace InteractingSLE.Sec5.Aux61GInst
open Aux61FibData

/-- The connected-filter input of the existing cluster-set theorem for a
continuous chart path approaching a positive finite contact time. -/
theorem inPath_connected_left_basis {X : Type*} [MeasurableSpace X]
    {E : Set X} {c : X → Chart} {ρ : X → ℝ≥0 → ℂ} {T : X → ℝ≥0∞}
    (hs : IsRestartSpec E c ρ T) {x : X} (hx : x ∈ E) {e : ℝ≥0}
    (he : 0 < e) (heT : (e : ℝ≥0∞) ≤ T x) :
    ∀ U ∈ 𝓝[<] e, ∃ S ∈ 𝓝[<] e, S ⊆ U ∧ IsPreconnected S ∧
      ContinuousOn (inPath E c ρ T x) S := by
  intro U hU
  obtain ⟨a, hae, haU⟩ := (nhdsLT_basis_of_exists_lt ⟨0, he⟩).mem_iff.1 hU
  refine ⟨Ioo a e, Ioo_mem_nhdsLT hae, haU, isPreconnected_Ioo, ?_⟩
  exact (hs.continuousOn_inPath hx).mono fun u hu =>
    (ENNReal.coe_lt_coe.2 hu.2).trans_le heT

/-- A bounded window makes the source's connected-cluster argument apply to
the actual approaching path. The extension may use a bounded physical
coordinate, so no globally finite physical inverse is required. -/
theorem accessLanding_of_comp_limit {X : Type*} [MeasurableSpace X]
    {E : Set X} {c : X → Chart} {ρ : X → ℝ≥0 → ℂ} {T : X → ℝ≥0∞}
    (hs : IsRestartSpec E c ρ T) {V : Set ℂ} (hVb : Bornology.IsBounded V)
    {x : X} (hx : x ∈ E) {e : ℝ≥0} (he : 0 < e) (heT : (e : ℝ≥0∞) ≤ T x)
    (hin : ∀ᶠ u in 𝓝[<] e, inPath E c ρ T x u ∈ V)
    {F : ℂ → ℂ} (hFd : DifferentiableOn ℂ F H) (hFc : ContinuousOn F Hbar)
    (hFi : InjOn F H) (hFR : ∀ z : ℂ, z.im = 0 → F z ∉ F '' H)
    {p : ℂ} (hlim : Tendsto (fun u => F (inPath E c ρ T x u)) (𝓝[<] e) (𝓝 p))
    (hp : p ∉ F '' (V ∩ Hbar)) :
    ∃ L : ℂ, L ∉ V ∧ Tendsto (inPath E c ρ T x) (𝓝[<] e) (𝓝 L) := by
  have : (𝓝[<] e).NeBot := nhdsLT_neBot_of_exists_lt ⟨0, he⟩
  obtain ⟨R, hR⟩ := hVb.subset_closedBall (0 : ℂ)
  have hGH : ∀ᶠ u in 𝓝[<] e, inPath E c ρ T x u ∈ Hbar := by
    filter_upwards [Ioo_mem_nhdsLT he] with u hu
    rw [hs.inPath_eq_fwd hx hu.1 ((ENNReal.coe_lt_coe.2 hu.2).trans_le heT)]
    exact H_subset_Hbar ((hs.conf x hx).fwd_mem
      (hs.inside x hx u hu.1 ((ENNReal.coe_lt_coe.2 hu.2).trans_le heT)))
  obtain ⟨L, hLbar, hFL, hL⟩ := YuanCharacterisation.exists_tendsto_of_tendsto_comp_filter
    hFd hFc hFi hFR (inPath_connected_left_basis hs hx he heT) hGH
    (hin.mono fun u hu => mem_closedBall_zero_iff.1 (hR hu)) hlim
  exact ⟨L, fun hLV => hp ⟨L, ⟨hLV, hLbar⟩, hFL⟩, hL⟩

/-- A family of inverse extensions gives the successor landing condition.
Its endpoint exclusion is a geometric window condition, not a limit through
every access to the physical endpoint. -/
theorem hasAccessLanding_of_comp_limits {X : Type*} [MeasurableSpace X]
    {E : Set X} {c : X → Chart} {ρ : X → ℝ≥0 → ℂ} {T : X → ℝ≥0∞}
    (hs : IsRestartSpec E c ρ T) {V : Set ℂ} (hVb : Bornology.IsBounded V)
    (F : X → ℂ → ℂ) (p : X → ℂ)
    (hFd : ∀ x ∈ E, DifferentiableOn ℂ (F x) H)
    (hFc : ∀ x ∈ E, ContinuousOn (F x) Hbar)
    (hFi : ∀ x ∈ E, InjOn (F x) H)
    (hFR : ∀ x ∈ E, ∀ z : ℂ, z.im = 0 → F x z ∉ F x '' H)
    (hlim : ∀ x ∈ E, 0 < T x → T x < ⊤ →
      Tendsto (fun u => F x (inPath E c ρ T x u)) (𝓝[<] (T x).toNNReal) (𝓝 (p x)))
    (hp : ∀ x ∈ E, 0 < T x → Aux61FibData.exitTime E c ρ T V x = T x → T x < ⊤ →
      p x ∉ F x '' (V ∩ Hbar)) : HasAccessLanding E c ρ T V := by
  intro x hx hT0 hexit hTfin
  have heT : ((T x).toNNReal : ℝ≥0∞) = T x := ENNReal.coe_toNNReal hTfin.ne
  have he0 : 0 < (T x).toNNReal := by exact_mod_cast (heT ▸ hT0)
  refine accessLanding_of_comp_limit hs hVb hx he0 heT.le ?_
    (hFd x hx) (hFc x hx) (hFi x hx) (hFR x hx) (hlim x hx hT0 hTfin)
      (hp x hx hT0 hexit hTfin)
  filter_upwards [self_mem_nhdsWithin] with u hu
  exact (IsRestartSpec.lt_exitTime (by
    rw [hexit, ← heT]
    exact ENNReal.coe_lt_coe.2 (mem_Iio.1 hu))).2

end InteractingSLE.Sec5.Aux61GInst
