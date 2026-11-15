/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.R5OutFrontier

/-!
# Physical landings and old incident accesses for outer pockets

The Jordan inverse extension and nested relative charts give the same
incident-access construction for either outer pocket shape.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

open Set Filter Topology Metric
open QuantumZipper (H Hbar)
open scoped NNReal ENNReal

namespace InteractingSLE.Sec7.R5Out

open WangWu Lemma71I Sec6 PocketMarks PocketCoord PocketJordan PocketTraversal PocketAdapt Lemma71C PocketCoupling
  PocketWordAssembly PocketSeedOpen PocketUnionPt PocketStop PocketStopSide PocketStopMarked PocketStopWallsFin R5Phase R5Ref

variable {Ω : Type*} {R L : Ω → ℝ≥0 → ℂ} {r : ℝ≥0} {W : Ω → ℝ → ℝ}
  {η : Ω → ℝ → ℂ} {ψ : Ω → ℂ → ℂ} {c : Ω → Chart} {ω : Ω}

/-- The bounded change pocket's Jordan alternative (pole at the outgoing corner). -/
theorem jordan_of_cfg (hcfg : HOuter.IsOuterCfg (R ω) (L ω) r (W ω) (η ω))
    (hψ : IsCfJordan (R ω) (L ω) r (ψ ω)) :
    (∃ pole : ℂ, Bornology.IsBounded (cfPocket (R ω) (L ω) r) ∧ pole ∉ cfPocket (R ω) (L ω) r ∧
      IsJordanCoord (cfPocket (R ω) (L ω) r) pole (cfPt (closePt (R ω) (L ω) r)) (ψ ω)) ∨
      IsJordanCoordInf (cfPocket (R ω) (L ω) r) (cfPt (closePt (R ω) (L ω) r)) (ψ ω) :=
  Or.inl ⟨cfPt (openPt (R ω) (L ω) r),
    (hcfg.conf.isCfPocket (zero_notMem_closure_of_rightLo_pos hcfg.conf hcfg.bounded)).isBounded,
    hcfg.conf.cfPt_openPt_notMem, hψ⟩

/-- **The physical landing of a real current coordinate** (bounded change pocket): the current inverse tends to
`extendFrom ℍ inv ξ`, which lies in `C̄` and on the frontier of the current domain. -/
theorem current_landing (hcfg : HOuter.IsOuterCfg (R ω) (L ω) r (W ω) (η ω))
    (hψ : IsCfJordan (R ω) (L ω) r (ψ ω)) (hc : (c ω).IsConformal)
    (hdom : ((c ω).dom : Set ℂ) = cfPocket (R ω) (L ω) r) (heq : EqOn (c ω).1 (ψ ω) (cfPocket (R ω) (L ω) r))
    {q : ℝ≥0} (hq : (q : ℝ≥0∞) < capLife (travAll R L r η ψ ω)) (ξ : ℝ) :
    Tendsto (relChart c (travAll R L r η ψ) q ω).2.1 (𝓝[H] (ξ : ℂ))
        (𝓝 (extendFrom H (relChart c (travAll R L r η ψ) q ω).2.1 ξ)) ∧
      extendFrom H (relChart c (travAll R L r η ψ) q ω).2.1 ξ ∈ closure (cfPocket (R ω) (L ω) r) ∧
      extendFrom H (relChart c (travAll R L r η ψ) q ω).2.1 ξ ∈
        frontier ((relChart c (travAll R L r η ψ) q ω).dom : Set ℂ) := by
  have hγ := (hcfg.props hψ).1
  obtain ⟨E, hE, hEc, hED⟩ := exists_inverse_extension_of_jordan_cases (jordan_of_cfg hcfg hψ) hc hdom heq
  obtain ⟨F, hF, hFc, hFD⟩ :=
    exists_relative_inverse_extension (c := c) (γ := travAll R L r η ψ) hγ hq hE hEc
  have hξ : (ξ : ℂ) ∈ Hbar := mem_Hbar_of_im_eq_zero (by simp)
  have hlim : Tendsto (relChart c (travAll R L r η ψ) q ω).2.1 (𝓝[H] (ξ : ℂ)) (𝓝 (F ξ)) :=
    (((hFc _ hξ).mono QuantumZipper.H_subset_Hbar).tendsto).congr'
      (eventually_nhdsWithin_of_forall fun _ hw => hF hw)
  have hcl : (ξ : ℂ) ∈ closure H := by
    rw [QuantumZipper.CA.Car.closure_H_eq_Hbar]
    exact hξ
  have hext : extendFrom H (relChart c (travAll R L r η ψ) q ω).2.1 ξ = F ξ := extendFrom_eq hcl hlim
  rw [hext]
  refine ⟨hlim, ?_, ?_⟩
  · obtain ⟨y, hy, hFy⟩ := hFD hξ
    exact hFy ▸ hED hy
  · have hf := inverse_real_landing_mem_frontier
      (isConformal_relChart_of_driven (c := c) (γ := travAll R L r η ψ) hγ hq hc) hlim
    exact hf

/-- **The physical landing of a real current coordinate** (pocket opening at the flow seed). -/
theorem current_landingInf (hcfg : HOuter.IsOuterCfgInf (R ω) (L ω) r (W ω) (η ω))
    (hψ : IsCfJordanInf (R ω) (L ω) r (ψ ω)) (hc : (c ω).IsConformal)
    (hdom : ((c ω).dom : Set ℂ) = cfPocket (R ω) (L ω) r) (heq : EqOn (c ω).1 (ψ ω) (cfPocket (R ω) (L ω) r))
    {q : ℝ≥0} (hq : (q : ℝ≥0∞) < capLife (travAllInf R L r η ψ ω)) (ξ : ℝ) :
    Tendsto (relChart c (travAllInf R L r η ψ) q ω).2.1 (𝓝[H] (ξ : ℂ))
        (𝓝 (extendFrom H (relChart c (travAllInf R L r η ψ) q ω).2.1 ξ)) ∧
      extendFrom H (relChart c (travAllInf R L r η ψ) q ω).2.1 ξ ∈ closure (cfPocket (R ω) (L ω) r) ∧
      extendFrom H (relChart c (travAllInf R L r η ψ) q ω).2.1 ξ ∈
        frontier ((relChart c (travAllInf R L r η ψ) q ω).dom : Set ℂ) := by
  have hγ := (hcfg.props hψ).1
  obtain ⟨E, hE, hEc, hED⟩ := exists_inverse_extension_of_jordan_cases (Or.inr hψ) hc hdom heq
  obtain ⟨F, hF, hFc, hFD⟩ :=
    exists_relative_inverse_extension (c := c) (γ := travAllInf R L r η ψ) hγ hq hE hEc
  have hξ : (ξ : ℂ) ∈ Hbar := mem_Hbar_of_im_eq_zero (by simp)
  have hlim : Tendsto (relChart c (travAllInf R L r η ψ) q ω).2.1 (𝓝[H] (ξ : ℂ)) (𝓝 (F ξ)) :=
    (((hFc _ hξ).mono QuantumZipper.H_subset_Hbar).tendsto).congr'
      (eventually_nhdsWithin_of_forall fun _ hw => hF hw)
  have hcl : (ξ : ℂ) ∈ closure H := by
    rw [QuantumZipper.CA.Car.closure_H_eq_Hbar]
    exact hξ
  have hext : extendFrom H (relChart c (travAllInf R L r η ψ) q ω).2.1 ξ = F ξ := extendFrom_eq hcl hlim
  rw [hext]
  refine ⟨hlim, ?_, ?_⟩
  · obtain ⟨y, hy, hFy⟩ := hFD hξ
    exact hFy ▸ hED hy
  · have hf := inverse_real_landing_mem_frontier
      (isConformal_relChart_of_driven (c := c) (γ := travAllInf R L r η ψ) hγ hq hc) hlim
    exact hf

/-- **The correct incident old access** (bounded change pocket; port of the late
`exists_actual_old_incident_access` to an arbitrary live current capacity): a current landing outside the domain of
an earlier visit reference, away from the outgoing corner, is reached in the old chart from a real coordinate `x`
along the current approach. -/
theorem exists_old_access (hcfg : HOuter.IsOuterCfg (R ω) (L ω) r (W ω) (η ω))
    (hψ : IsCfJordan (R ω) (L ω) r (ψ ω)) (hc : (c ω).IsConformal)
    (hdom : ((c ω).dom : Set ℂ) = cfPocket (R ω) (L ω) r) (heq : EqOn (c ω).1 (ψ ω) (cfPocket (R ω) (L ω) r))
    {q : ℝ≥0} (hq : (q : ℝ≥0∞) < capLife (travAll R L r η ψ ω)) {s : ℝ} (hs : 0 ≤ s)
    (hQ : (visitCap R L r η ψ ω s).toNNReal ≤ q) (hvisit : η ω s ∈ cfPocket (R ω) (L ω) r) {ξ : ℝ}
    (hBoundary : extendFrom H (relChart c (travAll R L r η ψ) q ω).2.1 ξ ∉
      (relChart c (travAll R L r η ψ) (visitCap R L r η ψ ω s).toNNReal ω).dom)
    (hNotExit : extendFrom H (relChart c (travAll R L r η ψ) q ω).2.1 ξ ≠ cfPt (openPt (R ω) (L ω) r)) :
    ∃ x : ℝ,
      Tendsto (fun z => (relChart c (travAll R L r η ψ) (visitCap R L r η ψ ω s).toNNReal ω).1
        ((relChart c (travAll R L r η ψ) q ω).2.1 z)) (𝓝[H] (ξ : ℂ)) (𝓝 (x : ℂ)) ∧
      Tendsto (relChart c (travAll R L r η ψ) (visitCap R L r η ψ ω s).toNNReal ω).2.1 (𝓝[H] (x : ℂ))
        (𝓝 (extendFrom H (relChart c (travAll R L r η ψ) q ω).2.1 ξ)) := by
  have hγ := (hcfg.props hψ).1
  obtain ⟨hlive, hOld, -⟩ := visit_chart_subset (A := Set.univ) (mem_univ ω) hcfg hψ hc hdom heq hs hvisit
  have hNow := isConformal_relChart_of_driven (c := c) (γ := travAll R L r η ψ) hγ hq hc
  have hIncl := relChart_dom_antitone (c := c) (γ := travAll R L r η ψ) hc hγ hq hQ
  obtain ⟨hLanding, hpcl, -⟩ := current_landing hcfg hψ hc hdom heq hq ξ
  obtain ⟨E₀, hE₀, hE₀c, -⟩ := exists_inverse_extension_of_jordan_cases (jordan_of_cfg hcfg hψ) hc hdom heq
  obtain ⟨E, hE, hEc, -⟩ := exists_relative_inverse_extension (c := c) (γ := travAll R L r η ψ)
    hγ hlive hE₀ hE₀c
  apply exists_old_incident_access_of_inverse_extension hOld hNow hIncl hE hEc hLanding hBoundary
  obtain ⟨W₁, hW₁, hW₁0, -, -, -, hOldEq⟩ := exists_relChart_eq_loewner (c := c) hγ hlive
  have hpole : cfPt (openPt (R ω) (L ω) r) ∉ cfPocket (R ω) (L ω) r := hcfg.conf.cfPt_openPt_notMem
  have hψc : ContinuousWithinAt (ψ ω) ((c ω).dom : Set ℂ)
      (extendFrom H (relChart c (travAll R L r η ψ) q ω).2.1 ξ) := by
    rw [hdom]
    exact (hψ.1 _ ⟨hpcl, hNotExit⟩).mono fun z hz =>
      ⟨subset_closure hz, fun h => hpole (mem_singleton_iff.1 h ▸ hz)⟩
  rw [hOldEq] at hIncl ⊢
  exact eventually_norm_bounded_old_coordinate hc hNow hW₁ hW₁0
    (visitCap R L r η ψ ω s).toNNReal.coe_nonneg hIncl hLanding
    (fun z hz => (heq (hdom ▸ hz)).symm) hψc
/-- The incident old access in a seed-opening outer pocket. -/
theorem exists_old_accessInf (hcfg : HOuter.IsOuterCfgInf (R ω) (L ω) r (W ω) (η ω))
    (hψ : IsCfJordanInf (R ω) (L ω) r (ψ ω)) (hc : (c ω).IsConformal)
    (hdom : ((c ω).dom : Set ℂ) = cfPocket (R ω) (L ω) r) (heq : EqOn (c ω).1 (ψ ω) (cfPocket (R ω) (L ω) r))
    {q : ℝ≥0} (hq : (q : ℝ≥0∞) < capLife (travAllInf R L r η ψ ω)) {s : ℝ} (hs : 0 ≤ s)
    (hQ : (visitCapInf R L r η ψ ω s).toNNReal ≤ q) (hvisit : η ω s ∈ cfPocket (R ω) (L ω) r) {ξ : ℝ}
    (hBoundary : extendFrom H (relChart c (travAllInf R L r η ψ) q ω).2.1 ξ ∉
      (relChart c (travAllInf R L r η ψ) (visitCapInf R L r η ψ ω s).toNNReal ω).dom) :
    ∃ x : ℝ,
      Tendsto (fun z => (relChart c (travAllInf R L r η ψ) (visitCapInf R L r η ψ ω s).toNNReal ω).1
        ((relChart c (travAllInf R L r η ψ) q ω).2.1 z)) (𝓝[H] (ξ : ℂ)) (𝓝 (x : ℂ)) ∧
      Tendsto (relChart c (travAllInf R L r η ψ) (visitCapInf R L r η ψ ω s).toNNReal ω).2.1 (𝓝[H] (x : ℂ))
        (𝓝 (extendFrom H (relChart c (travAllInf R L r η ψ) q ω).2.1 ξ)) := by
  have hγ := (hcfg.props hψ).1
  obtain ⟨hlive, hOld, -⟩ := visit_chart_subsetInf (A := Set.univ) (mem_univ ω) hcfg hψ hc hdom heq hs hvisit
  have hNow := isConformal_relChart_of_driven (c := c) (γ := travAllInf R L r η ψ) hγ hq hc
  have hIncl := relChart_dom_antitone (c := c) (γ := travAllInf R L r η ψ) hc hγ hq hQ
  obtain ⟨hLanding, hpcl, -⟩ := current_landingInf hcfg hψ hc hdom heq hq ξ
  obtain ⟨E₀, hE₀, hE₀c, -⟩ := exists_inverse_extension_of_jordan_cases (Or.inr hψ) hc hdom heq
  obtain ⟨E, hE, hEc, -⟩ := exists_relative_inverse_extension (c := c) (γ := travAllInf R L r η ψ)
    hγ hlive hE₀ hE₀c
  apply exists_old_incident_access_of_inverse_extension hOld hNow hIncl hE hEc hLanding hBoundary
  obtain ⟨W₁, hW₁, hW₁0, -, -, -, hOldEq⟩ := exists_relChart_eq_loewner (c := c) hγ hlive
  have hψc : ContinuousWithinAt (ψ ω) ((c ω).dom : Set ℂ)
      (extendFrom H (relChart c (travAllInf R L r η ψ) q ω).2.1 ξ) := by
    rw [hdom]
    exact (hψ.1 _ hpcl).mono subset_closure
  rw [hOldEq] at hIncl ⊢
  exact eventually_norm_bounded_old_coordinate hc hNow hW₁ hW₁0
    (visitCapInf R L r η ψ ω s).toNNReal.coe_nonneg hIncl hLanding
    (fun z hz => (heq (hdom ▸ hz)).symm) hψc

end InteractingSLE.Sec7.R5Out
