/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.R5OutCollarInf

/-!
# The source incident reference cover for outer pockets

The countable original-time family covers every nonexceptional current
prime end. At an interior physical landing the selected reference hull
contains that landing, a property of the constructed reference.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

open Set Filter Topology Metric MeasureTheory
open QuantumZipper (H fwdHull)
open scoped NNReal ENNReal

namespace InteractingSLE.Sec7.R5Out

open Sec6 PocketMarks PocketCoord PocketJordan PocketTraversal PocketAdapt Lemma71C PocketCoupling
  PocketWordAssembly PocketSeedOpen PocketUnionPt PocketStop PocketStopSide PocketStopMarked
  PocketStopWallsFin R5Phase R5Ref
open Wire.Current.SideTest (rationalOriginalTime)

variable {Ω : Type*} {R L : Ω → ℝ≥0 → ℂ} {r : ℝ≥0} {W : Ω → ℝ → ℝ}
  {η : Ω → ℝ → ℂ} {ψ : Ω → ℂ → ℂ} {c : Ω → Chart} {A : Set Ω}

/-- The pathwise source incident reference cover for bounded outer pockets. -/
theorem refCover {ω : Ω} (hω : ω ∈ A) (hcfg : HOuter.IsOuterCfg (R ω) (L ω) r (W ω) (η ω))
    (hψ : IsCfJordan (R ω) (L ω) r (ψ ω)) (hc : (c ω).IsConformal)
    (hdom : ((c ω).dom : Set ℂ) = cfPocket (R ω) (L ω) r) (heq : EqOn (c ω).1 (ψ ω) (cfPocket (R ω) (L ω) r))
    {F : ℕ → Ω → Set ℂ} (hHull : ∀ i, F i ω = fwdHull (W ω) (rationalOriginalTime i)) {q : ℝ≥0}
    (hq : (q : ℝ≥0∞) < capLife (travAll R L r η ψ ω)) (ξ : ℝ)
    (hX : extendFrom H (relChart c (travAll R L r η ψ) q ω).2.1 ξ ∉ refExc R L r η ψ q ω) :
    ∃ (i : ℕ) (x ε : ℝ), ω ∈ refEvent A R L r W η ψ F q i ∧
        (η ω (rationalOriginalTime i) ∈ cfPocket (R ω) (L ω) r ∨ q = 0) ∧
      (extendFrom H (relChart c (travAll R L r η ψ) q ω).2.1 ξ ∈ cfPocket (R ω) (L ω) r →
        extendFrom H (relChart c (travAll R L r η ψ) q ω).2.1 ξ ∈ F i ω) ∧
      IsRefCollar (refChart c R L r η ψ i ω) (relChart c (travAll R L r η ψ) q ω) ξ
        (extendFrom H (relChart c (travAll R L r η ψ) q ω).2.1 ξ) x ε := by
  have hγ := (hcfg.props hψ).1
  have hNow := isConformal_relChart_of_driven (c := c) (γ := travAll R L r η ψ) hγ hq hc
  obtain ⟨hLanding, -, -⟩ := current_landing hcfg hψ hc hdom heq hq ξ
  rcases (show (0 : ℝ≥0) ≤ q from zero_le).eq_or_lt with hq0 | hq0
  · subst hq0
    have h0 : (visitCap R L r η ψ ω (rationalOriginalTime (Denumerable.eqv ℚ 0))).toNNReal = 0 := by
      rw [rationalOriginalTime_eqv_zero, NNReal.coe_zero, visitCap_zero hcfg hψ, Real.toNNReal_zero]
    refine ⟨Denumerable.eqv ℚ 0, ξ, 1, ⟨hω, hq, Or.inr rationalOriginalTime_eqv_zero, h0.le, hHull _⟩,
      Or.inr rfl, ?_, ?_⟩
    · intro hpC
      have hn := inverse_real_landing_notMem_dom hNow hLanding
      apply False.elim (hn ?_)
      change _ ∈ ((relChart c (travAll R L r η ψ) 0 ω).dom : Set ℂ)
      rwa [relChart_zero_dom (c := c) (γ := travAll R L r η ψ) hγ, hdom]
    · simp only [refChart, h0]
      exact isRefCollar_self hNow hLanding
  · simp only [refExc, mem_insert_iff, mem_singleton_iff, not_or] at hX
    obtain ⟨s, hs0, hv, hQ, -, hpHull, x, ε, hcol⟩ := exists_visit_collar hω hcfg hψ hc hdom heq hq0 hq ξ hX.1 hX.2
    have hti := coe_rationalOriginalTime_eqv hs0
    refine ⟨Denumerable.eqv ℚ s, x, ε, ⟨hω, hq, Or.inl (by rw [hti]; exact hv), by rw [hti]; exact hQ,
      hHull _⟩, Or.inl (by rw [hti]; exact hv), ?_, ?_⟩
    · rw [hHull _, hti]
      exact hpHull
    · simp only [refChart, hti]
      exact hcol


/-- The countable comparison events are intersected before reference selection. -/
theorem ae_refCover {_ : MeasurableSpace Ω} {P : Measure Ω}
    (hcfg : ∀ ω ∈ A, HOuter.IsOuterCfg (R ω) (L ω) r (W ω) (η ω))
    (hψ : ∀ ω ∈ A, IsCfJordan (R ω) (L ω) r (ψ ω)) (hc : ∀ ω ∈ A, (c ω).IsConformal)
    (hdom : ∀ ω ∈ A, ((c ω).dom : Set ℂ) = cfPocket (R ω) (L ω) r)
    (heq : ∀ ω ∈ A, EqOn (c ω).1 (ψ ω) (cfPocket (R ω) (L ω) r)) {F : ℕ → Ω → Set ℂ}
    (hHull : ∀ᵐ ω ∂P, ω ∈ A → ∀ i, F i ω = fwdHull (W ω) (rationalOriginalTime i)) (q : ℝ≥0) :
    ∀ᵐ ω ∂P, ω ∈ A → (q : ℝ≥0∞) < capLife (travAll R L r η ψ ω) → ∀ ξ : ℝ,
      extendFrom H (relChart c (travAll R L r η ψ) q ω).2.1 ξ ∉ refExc R L r η ψ q ω →
      ∃ (i : ℕ) (x ε : ℝ), ω ∈ refEvent A R L r W η ψ F q i ∧
          (η ω (rationalOriginalTime i) ∈ cfPocket (R ω) (L ω) r ∨ q = 0) ∧
        (extendFrom H (relChart c (travAll R L r η ψ) q ω).2.1 ξ ∈ cfPocket (R ω) (L ω) r →
          extendFrom H (relChart c (travAll R L r η ψ) q ω).2.1 ξ ∈ F i ω) ∧
        IsRefCollar (refChart c R L r η ψ i ω) (relChart c (travAll R L r η ψ) q ω) ξ
          (extendFrom H (relChart c (travAll R L r η ψ) q ω).2.1 ξ) x ε := by
  filter_upwards [hHull] with ω hH hω hq ξ hX
  exact refCover hω (hcfg ω hω) (hψ ω hω) (hc ω hω) (hdom ω hω) (heq ω hω) (hH hω) hq ξ hX


/-- The pathwise source incident reference cover for seed-opening outer pockets. -/
theorem refCoverInf {ω : Ω} (hω : ω ∈ A) (hcfg : HOuter.IsOuterCfgInf (R ω) (L ω) r (W ω) (η ω))
    (hψ : IsCfJordanInf (R ω) (L ω) r (ψ ω)) (hc : (c ω).IsConformal)
    (hdom : ((c ω).dom : Set ℂ) = cfPocket (R ω) (L ω) r) (heq : EqOn (c ω).1 (ψ ω) (cfPocket (R ω) (L ω) r))
    {F : ℕ → Ω → Set ℂ} (hHull : ∀ i, F i ω = fwdHull (W ω) (rationalOriginalTime i)) {q : ℝ≥0}
    (hq : (q : ℝ≥0∞) < capLife (travAllInf R L r η ψ ω)) (ξ : ℝ)
    (hX : extendFrom H (relChart c (travAllInf R L r η ψ) q ω).2.1 ξ ∉ refExcInf R L r η ψ q ω) :
    ∃ (i : ℕ) (x ε : ℝ), ω ∈ refEventInf A R L r W η ψ F q i ∧
        (η ω (rationalOriginalTime i) ∈ cfPocket (R ω) (L ω) r ∨ q = 0) ∧
      (extendFrom H (relChart c (travAllInf R L r η ψ) q ω).2.1 ξ ∈ cfPocket (R ω) (L ω) r →
        extendFrom H (relChart c (travAllInf R L r η ψ) q ω).2.1 ξ ∈ F i ω) ∧
      IsRefCollar (refChartInf c R L r η ψ i ω) (relChart c (travAllInf R L r η ψ) q ω) ξ
        (extendFrom H (relChart c (travAllInf R L r η ψ) q ω).2.1 ξ) x ε := by
  have hγ := (hcfg.props hψ).1
  have hNow := isConformal_relChart_of_driven (c := c) (γ := travAllInf R L r η ψ) hγ hq hc
  obtain ⟨hLanding, -, -⟩ := current_landingInf hcfg hψ hc hdom heq hq ξ
  rcases (show (0 : ℝ≥0) ≤ q from zero_le).eq_or_lt with hq0 | hq0
  · subst hq0
    have h0 : (visitCapInf R L r η ψ ω (rationalOriginalTime (Denumerable.eqv ℚ 0))).toNNReal = 0 := by
      rw [rationalOriginalTime_eqv_zero, NNReal.coe_zero, visitCapInf_zero hcfg hψ, Real.toNNReal_zero]
    refine ⟨Denumerable.eqv ℚ 0, ξ, 1, ⟨hω, hq, Or.inr rationalOriginalTime_eqv_zero, h0.le, hHull _⟩,
      Or.inr rfl, ?_, ?_⟩
    · intro hpC
      have hn := inverse_real_landing_notMem_dom hNow hLanding
      apply False.elim (hn ?_)
      change _ ∈ ((relChart c (travAllInf R L r η ψ) 0 ω).dom : Set ℂ)
      rwa [relChart_zero_dom (c := c) (γ := travAllInf R L r η ψ) hγ, hdom]
    · simp only [refChartInf, h0]
      exact isRefCollar_self hNow hLanding
  · simp only [refExcInf, mem_singleton_iff] at hX
    obtain ⟨s, hs0, hv, hQ, -, hpHull, x, ε, hcol⟩ := exists_visit_collarInf hω hcfg hψ hc hdom heq hq0 hq ξ hX
    have hti := coe_rationalOriginalTime_eqv hs0
    refine ⟨Denumerable.eqv ℚ s, x, ε, ⟨hω, hq, Or.inl (by rw [hti]; exact hv), by rw [hti]; exact hQ,
      hHull _⟩, Or.inl (by rw [hti]; exact hv), ?_, ?_⟩
    · rw [hHull _, hti]
      exact hpHull
    · simp only [refChartInf, hti]
      exact hcol


/-- The countable comparison events are intersected before reference selection. -/
theorem ae_refCoverInf {_ : MeasurableSpace Ω} {P : Measure Ω}
    (hcfg : ∀ ω ∈ A, HOuter.IsOuterCfgInf (R ω) (L ω) r (W ω) (η ω))
    (hψ : ∀ ω ∈ A, IsCfJordanInf (R ω) (L ω) r (ψ ω)) (hc : ∀ ω ∈ A, (c ω).IsConformal)
    (hdom : ∀ ω ∈ A, ((c ω).dom : Set ℂ) = cfPocket (R ω) (L ω) r)
    (heq : ∀ ω ∈ A, EqOn (c ω).1 (ψ ω) (cfPocket (R ω) (L ω) r)) {F : ℕ → Ω → Set ℂ}
    (hHull : ∀ᵐ ω ∂P, ω ∈ A → ∀ i, F i ω = fwdHull (W ω) (rationalOriginalTime i)) (q : ℝ≥0) :
    ∀ᵐ ω ∂P, ω ∈ A → (q : ℝ≥0∞) < capLife (travAllInf R L r η ψ ω) → ∀ ξ : ℝ,
      extendFrom H (relChart c (travAllInf R L r η ψ) q ω).2.1 ξ ∉ refExcInf R L r η ψ q ω →
      ∃ (i : ℕ) (x ε : ℝ), ω ∈ refEventInf A R L r W η ψ F q i ∧
          (η ω (rationalOriginalTime i) ∈ cfPocket (R ω) (L ω) r ∨ q = 0) ∧
        (extendFrom H (relChart c (travAllInf R L r η ψ) q ω).2.1 ξ ∈ cfPocket (R ω) (L ω) r →
          extendFrom H (relChart c (travAllInf R L r η ψ) q ω).2.1 ξ ∈ F i ω) ∧
        IsRefCollar (refChartInf c R L r η ψ i ω) (relChart c (travAllInf R L r η ψ) q ω) ξ
          (extendFrom H (relChart c (travAllInf R L r η ψ) q ω).2.1 ξ) x ε := by
  filter_upwards [hHull] with ω hH hω hq ξ hX
  exact refCoverInf hω (hcfg ω hω) (hψ ω hω) (hc ω hω) (hdom ω hω) (heq ω hω) (hH hω) hq ξ hX


end InteractingSLE.Sec7.R5Out
