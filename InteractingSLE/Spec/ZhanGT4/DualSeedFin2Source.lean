/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.ZhanGT4.DualSeedFin2Remove

/-!
# The actual seeded positive-time logarithmic Itô formula

Packet PROVE-ZHAN-GT4-A22. Construct the gap versions and every localized
field from protected data, and remove the actual bands. No Taylor bound,
band agreement or positive-time stochastic identity is an input.
-/

set_option autoImplicit false

noncomputable section

open Set Filter Topology Metric MeasureTheory ProbabilityTheory
open scoped NNReal

namespace InteractingSLE.ZhanGT4

open QuantumZipper (IsForwardSol fwdMap)

variable {Ω : Type*} {mΩ : MeasurableSpace Ω}

/-- The original seeded logarithm satisfies Itô's formula on every positive
prefix from the actual enclosure geometry and force equations. -/
theorem seedPositiveLogIto_of_protected_data
    (𝓕 : Filtration ℝ≥0 mΩ) {P : Measure Ω}
    {κ : ℝ} (hκ : 0 < κ) {n : ℕ} (rr : Fin n → ℝ)
    {B D : ℝ≥0 → Ω → ℝ} (hB : IsFilteredBrownianReal 𝓕 B P)
    (hBc : ∀ ω, Continuous (B · ω))
    (hDm : ∀ u, Measurable[𝓕 u] (D u)) (hDc : ∀ ω, Continuous (D · ω))
    {d : Ω → SeedData n}
    (hdW : ∀ ω, (d ω).W = driftDriver (Real.sqrt κ) B D ω)
    (hdκ : ∀ ω, (d ω).κ = κ) (hdr : ∀ ω, (d ω).r = rr)
    {A : Set ℂ} {φ : ℂ → ℂ} {ζ₀ : ℝ}
    (hdφ : ∀ ω, (d ω).φ = φ) (hdζ : ∀ ω, (d ω).ζ₀ = ζ₀)
    {T : Ω → ℝ≥0} (hT : IsStoppingTime 𝓕 fun ω => (T ω : WithTop ℝ≥0))
    {Tm : ℝ} (hTm : ∀ ω, (T ω : ℝ) ≤ Tm)
    {r a₀ ρm : ℝ} (hr : 0 < r) (ha₀ : 0 < a₀) (hρm : 0 < ρm)
    (h : ∀ ω, OwnData (d ω).W A (d ω).φ (T ω) (d ω).a (d ω).W')
    (hv₀ : ∀ ω, ∃ v₀ : ℝ → ℂ,
      IsForwardSol (d ω).W' (d ω).ζ₀ ((d ω).a (T ω)) v₀)
    (hclr : ∀ ω t, t ∈ Icc (0 : ℝ) (T ω) →
      Disjoint (ball ((d ω).W t : ℂ) r)
        ((fun z => fwdMap (d ω).W t z + (d ω).W t) '' A))
    (hA1 : ∀ ω t, t ∈ Icc (0 : ℝ) (T ω) → a₀ ≤ (d ω).A 1 t)
    (hmclr : ∀ ω m t, t ∈ Icc (0 : ℝ) (T ω) →
      Disjoint (ball ((d ω).V m t : ℂ) ρm)
        ((fun z => fwdMap (d ω).W t z + (d ω).W t) '' A))
    (hV₀ : ∀ ω t, t ∈ Ioc (0 : ℝ) (T ω) →
      HasDerivWithinAt (d ω).V₀ (2 / ((d ω).V₀ t - (d ω).W t)) (Ioc 0 (T ω)) t)
    (hG₀ : ∀ ω t, t ∈ Ioc (0 : ℝ) (T ω) →
      HasDerivWithinAt (d ω).G₀
        (-2 * (d ω).G₀ t / ((d ω).V₀ t - (d ω).W t) ^ 2) (Ioc 0 (T ω)) t)
    (hV : ∀ ω m t, t ∈ Ioc (0 : ℝ) (T ω) →
      HasDerivWithinAt ((d ω).V m) (2 / ((d ω).V m t - (d ω).W t)) (Ioc 0 (T ω)) t)
    (hVc : ∀ ω m, ContinuousOn ((d ω).V m) (Icc 0 (T ω)))
    (hD : ∀ ω t, t ∈ Ioc (0 : ℝ) (T ω) →
      HasDerivWithinAt (fun s : ℝ => D s.toNNReal ω)
        ((d ω).drift t) (Ioc 0 (T ω)) t)
    (hVm : ∀ (q : ℝ≥0) m,
      Measurable[𝓕 q] ({ω | q ≤ T ω}.indicator fun ω => (d ω).V m q))
    (hV₀m : ∀ q : ℝ≥0,
      Measurable[𝓕 q] ({ω | q ≤ T ω}.indicator fun ω => (d ω).V₀ q))
    (hG₀m : ∀ q : ℝ≥0,
      Measurable[𝓕 q] ({ω | q ≤ T ω}.indicator fun ω => (d ω).G₀ q))
    (hgc : ∀ ω i, ContinuousOn ((d ω).gapVal i) (Icc 0 (T ω)))
    (hgn : ∀ ω i t, t ∈ Ioc (0 : ℝ) (T ω) → (d ω).gapVal i t ≠ 0)
    (hp : IsStronglyProgressive 𝓕 (seedNoise κ d T))
    {C : ℝ} (hC : 0 ≤ C) (hb : ∀ u ω, |seedNoise κ d T u ω| ≤ C)
    (hreg : Girsanov.IsRiemannRegular P (seedNoise κ d T)) :
    SeedPositiveLogIto P 𝓕 B (seedNoise κ d T) d T := by
  let X : ℝ≥0 → Ω → ℝ := fun u ω => Real.sqrt κ * B u ω + D u ω
  have hXm : ∀ u, Measurable[𝓕 u] (X u) := fun u =>
    ((hB.2.1 u).const_mul _).add (hDm u)
  have hXc : ∀ ω, Continuous (X · ω) := fun ω =>
    ((hBc ω).const_mul _).add (hDc ω)
  have hdX : ∀ ω, (d ω).W = Ito.rpath (X · ω) := by
    intro ω
    rw [hdW ω, driftDriver_eq_rpath]
  have hmeas : ∀ q : ℝ≥0,
      (∀ i, Measurable[𝓕 q] ({ω | q ≤ T ω}.indicator fun ω => (d ω).gapVal i q)) ∧
      Measurable[𝓕 q] ({ω | q ≤ T ω}.indicator fun ω => (d ω).normEll q) := by
    intro q
    exact measurable_seed_norm_and_gaps hXm hXc hdX hdφ hdζ q
      (measurableSet_ge_of_isStoppingTime hT q)
      (fun ω hω => NNReal.coe_le_coe.2 hω)
      (fun ω _ => h ω) (fun ω _ => hv₀ ω)
      (fun ω hω m => ⟨ρm, hρm, hmclr ω m q ⟨q.coe_nonneg, NNReal.coe_le_coe.2 hω⟩⟩)
      (hVm q) hdκ hdr (hV₀m q) (hG₀m q)
  obtain ⟨Y, hYc, hYm, hYv⟩ := exists_continuous_adapted_stopped_versions hT
    (fun i q => (hmeas q).1 i) (fun i ω => hgc ω i)
  intro ε t hε hεt
  let R := Tm.toNNReal
  have hTR : ∀ ω, T ω ≤ ε + R := by
    intro ω
    have hle : T ω ≤ R := by
      rw [← NNReal.coe_le_coe]
      exact (hTm ω).trans (Real.le_coe_toNNReal Tm)
    exact hle.trans (le_add_of_nonneg_left (zero_le (a := ε)))
  apply seed_logIto_at_of_actual_bands hκ hε hεt hB hBc hdW hT hTR hYc hYm
    (fun ω i u _ hu => hYv i ω u hu) hgn hp hC hb hreg
  intro k
  have subε : ∀ ω, Icc (ε : ℝ) (T ω) ⊆ Ioc (0 : ℝ) (T ω) :=
    fun ω u hu => ⟨(NNReal.coe_pos.2 hε).trans_le hu.1, hu.2⟩
  exact exists_seedBand_localized_fields 𝓕 hκ rr hB hBc hDm hDc hdW hdκ hdr hdφ hdζ
    hε hT hTm hr ha₀ hρm (fun ω _ => h ω) (fun ω _ => hv₀ ω)
    (fun ω _ => hclr ω) (fun ω _ => hA1 ω) (fun ω _ => hmclr ω)
    (fun ω _ u hu => (hV₀ ω u (subε ω hu)).mono (subε ω))
    (fun ω _ u hu => (hG₀ ω u (subε ω hu)).mono (subε ω))
    (fun ω _ m u hu => (hV ω m u (subε ω hu)).mono (subε ω))
    (fun ω _ => hVc ω)
    (fun ω _ u hu => (hD ω u (subε ω hu)).mono (subε ω))
    (fun q m _ => hVm q m) (fun q _ => hV₀m q) (fun q _ => hG₀m q)
    hYc hYm (fun ω i u _ hu => hYv i ω u hu) k R

end InteractingSLE.ZhanGT4
