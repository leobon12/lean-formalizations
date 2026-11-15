/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.R5RefStop
import InteractingSLE.Spec.Sec7.R5PhaseVisit
import InteractingSLE.Spec.Sec7.PocketSideInTailCanonical
import InteractingSLE.Spec.Sec7.PocketSideInTailActual

/-!
# Lemma R.5 on an R.7 test: the current chart at a relative capacity and the visit references

Packet PROVE-R5-REFCHART. The pathwise chart facts of Lemma R.5's proof (spec p. 475) for the change pocket
`C = cfPocket R L r` of two walls traversed by the counterflow `η` (`travAll R L r η ψ`, Jordan coordinate `ψ`, base
chart `c` with `c = ψ` on `C`), at an ARBITRARY live relative capacity `q` (the late `SideTest` lemmas of
POCKET-SIDEIN are stated at original visit times only):

* `leftStop` (def): the left end `T⁰(q)` of the erasure fibre (ruling R67);
* **`current_dom_eq`**: the current relative chart has domain `C ∩ (ℍ ∖ fill η([0, T⁰(q)]))` ((GC2) at both fibre
  ends, `inter_domain_ambTime0`);
* **`current_landing`**: every real current coordinate `ξ` has its physical landing `extendFrom ℍ inv ξ`, in `C̄`
  and on the frontier of the current domain;
* **`visit_chart`**: at an original interior visit `s` the relative chart at the capacity reached at `s` is
  conformal, live, with domain `C ∩ (ℍ ∖ fill η([0, s]))`; **`visitCap_le_of_lt_leftStop`**: visits before `T⁰(q)`
  have capacity at most `q`;
* **`exists_old_access`**: the correct incident old access of a current landing outside an earlier visit domain
  (port of the late `exists_actual_old_incident_access`; the bounded pocket excludes its outgoing corner);
* the same for the pocket opening at the flow seed (`…Inf`; no corner exclusion).

Ruling R48: nothing here uses Theorem 1.2/1.3.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Filter Set Topology Metric
open QuantumZipper (H Hbar fwdHull)
open scoped NNReal ENNReal

namespace InteractingSLE.Sec7.R5Ref

open WangWu Lemma71I PocketCoord PocketJordan PocketMarks PocketTraversal PocketAdapt Lemma71C PocketCoupling
  PocketWordAssembly PocketSeedOpen PocketUnionPt PocketStop PocketStopField PocketStopSide PocketStopMarked
  PocketStopWallsFin Sec6 R5Phase

variable {Ω : Type*}

/-- **The left stop `T⁰(q)`** of the traversal of a bounded change pocket (ruling R67). -/
def leftStop (R L : Ω → ℝ≥0 → ℂ) (r : ℝ≥0) (η : Ω → ℝ → ℂ) (ψ : Ω → ℂ → ℂ) (q : ℝ≥0) (ω : Ω) : ℝ :=
  ambTime0 (η ω) (cfPocket (R ω) (L ω) r) (firstHit (η ω) (cfArcR (R ω) (L ω) r 1))
    (firstHit (η ω) (cfArcR (R ω) (L ω) r 0)) (ψ ω) q

/-- **The left stop `T⁰(q)`** of the traversal of a change pocket opening at the flow seed. -/
def leftStopInf (R L : Ω → ℝ≥0 → ℂ) (r : ℝ≥0) (η : Ω → ℝ → ℂ) (ψ : Ω → ℂ → ℂ) (q : ℝ≥0) (ω : Ω) : ℝ :=
  ambTime0Inf (η ω) (cfPocket (R ω) (L ω) r) (firstHit (η ω) (cfArcRInf (R ω) (L ω) r 0)) (ψ ω) q

section Bounded

variable {R L : Ω → ℝ≥0 → ℂ} {r : ℝ≥0} {W : Ω → ℝ → ℝ} {η : Ω → ℝ → ℂ} {ψ : Ω → ℂ → ℂ}
  {A : Set Ω} {c : Ω → Chart} {ω : Ω}

/-- The reverse pocket and its Jordan coordinate behind a bounded counterflow pocket configuration. -/
theorem pocket_of_cfg (hcfg : IsCfPocketConfig (R ω) (L ω) r (W ω) (η ω))
    (hψ : IsCfJordan (R ω) (L ω) r (ψ ω)) :
    IsReversePocket (W ω) (η ω) (cfPocket (R ω) (L ω) r) (cfArcR (R ω) (L ω) r) (cfArcL (R ω) (L ω) r)
        (cfBeta (R ω) (L ω) r) (firstHit (η ω) (cfArcR (R ω) (L ω) r 1))
        (firstHit (η ω) (cfArcR (R ω) (L ω) r 0)) ∧
      IsJordanCoord (cfPocket (R ω) (L ω) r) (cfArcR (R ω) (L ω) r 0) (cfArcR (R ω) (L ω) r 1) (ψ ω) := by
  refine ⟨hcfg.conf.isReversePocket_of_counterflow
    (zero_notMem_closure_of_rightLo_pos hcfg.conf hcfg.bounded)
    hcfg.trace hcfg.continuous_W hcfg.W_zero hcfg.revR hcfg.revL hcfg.visR, ?_⟩
  rw [PocketCoord.IsChangeConfigInc.cfArcR_zero, PocketCoord.IsChangeConfigInc.cfArcR_one]
  exact hψ

/-- The bounded change pocket's Jordan alternative (pole at the outgoing corner). -/
theorem jordan_of_cfg (hcfg : IsCfPocketConfig (R ω) (L ω) r (W ω) (η ω))
    (hψ : IsCfJordan (R ω) (L ω) r (ψ ω)) :
    (∃ pole : ℂ, Bornology.IsBounded (cfPocket (R ω) (L ω) r) ∧ pole ∉ cfPocket (R ω) (L ω) r ∧
      IsJordanCoord (cfPocket (R ω) (L ω) r) pole (cfPt (closePt (R ω) (L ω) r)) (ψ ω)) ∨
      IsJordanCoordInf (cfPocket (R ω) (L ω) r) (cfPt (closePt (R ω) (L ω) r)) (ψ ω) :=
  Or.inl ⟨cfPt (openPt (R ω) (L ω) r),
    (hcfg.conf.isCfPocket (zero_notMem_closure_of_rightLo_pos hcfg.conf hcfg.bounded)).isBounded,
    hcfg.conf.cfPt_openPt_notMem, hψ⟩

/-- `T⁰(q) ≥ 0`. -/
theorem leftStop_nonneg (hcfg : IsCfPocketConfig (R ω) (L ω) r (W ω) (η ω))
    (hψ : IsCfJordan (R ω) (L ω) r (ψ ω)) (q : ℝ≥0) : 0 ≤ leftStop R L r η ψ q ω :=
  (pocket_of_cfg hcfg hψ).1.nonneg.trans (ambTime0_mem (pocket_of_cfg hcfg hψ).1 (ψ ω) q).1

/-- **The current domain at a live relative capacity** (bounded change pocket):
`C ∩ (ℍ ∖ fill η([0, T⁰(q)]))`. -/
theorem current_dom_eq (hω : ω ∈ A) (hcfg : IsCfPocketConfig (R ω) (L ω) r (W ω) (η ω))
    (hψ : IsCfJordan (R ω) (L ω) r (ψ ω)) (hc : (c ω).IsConformal)
    (hdom : ((c ω).dom : Set ℂ) = cfPocket (R ω) (L ω) r) (heq : EqOn (c ω).1 (ψ ω) (cfPocket (R ω) (L ω) r))
    {q : ℝ≥0} (hq : (q : ℝ≥0∞) < capLife (travAll R L r η ψ ω)) :
    ((relChart c (travAll R L r η ψ) q ω).dom : Set ℂ) =
      cfPocket (R ω) (L ω) r ∩ (H \ fillH (η ω '' Icc 0 (leftStop R L r η ψ q ω))) := by
  obtain ⟨hP, -⟩ := pocket_of_cfg hcfg hψ
  rw [← activeDom_eq_relChart_dom hω hq (hcfg.isDrivenCurve hψ).1 hc,
    activeDom_cfPocket_eq_stopHull hω hcfg hψ hc hdom heq hq, stopHull,
    ← inter_domain_ambTime0 hP hcfg.attach (ψ ω) (q : ℝ), ← hcfg.trace.2.2 _ (leftStop_nonneg hcfg hψ q)]
  rfl

/-- **The physical landing of a real current coordinate** (bounded change pocket): the current inverse tends to
`extendFrom ℍ inv ξ`, which lies in `C̄` and on the frontier of the current domain. -/
theorem current_landing (hω : ω ∈ A) (hcfg : IsCfPocketConfig (R ω) (L ω) r (W ω) (η ω))
    (hψ : IsCfJordan (R ω) (L ω) r (ψ ω)) (hc : (c ω).IsConformal)
    (hdom : ((c ω).dom : Set ℂ) = cfPocket (R ω) (L ω) r) (heq : EqOn (c ω).1 (ψ ω) (cfPocket (R ω) (L ω) r))
    {q : ℝ≥0} (hq : (q : ℝ≥0∞) < capLife (travAll R L r η ψ ω)) (ξ : ℝ) :
    Tendsto (relChart c (travAll R L r η ψ) q ω).2.1 (𝓝[H] (ξ : ℂ))
        (𝓝 (extendFrom H (relChart c (travAll R L r η ψ) q ω).2.1 ξ)) ∧
      extendFrom H (relChart c (travAll R L r η ψ) q ω).2.1 ξ ∈ closure (cfPocket (R ω) (L ω) r) ∧
      extendFrom H (relChart c (travAll R L r η ψ) q ω).2.1 ξ ∈
        frontier (cfPocket (R ω) (L ω) r ∩ (H \ fillH (η ω '' Icc 0 (leftStop R L r η ψ q ω)))) := by
  have hγ := (hcfg.isDrivenCurve hψ).1
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
    rwa [current_dom_eq hω hcfg hψ hc hdom heq hq] at hf

/-- **The relative chart at an original interior visit** (bounded change pocket): live, conformal, with domain
`C ∩ (ℍ ∖ fill η([0, s]))`. -/
theorem visit_chart (hω : ω ∈ A) (hcfg : IsCfPocketConfig (R ω) (L ω) r (W ω) (η ω))
    (hψ : IsCfJordan (R ω) (L ω) r (ψ ω)) (hc : (c ω).IsConformal)
    (hdom : ((c ω).dom : Set ℂ) = cfPocket (R ω) (L ω) r) (heq : EqOn (c ω).1 (ψ ω) (cfPocket (R ω) (L ω) r))
    {s : ℝ} (hs : 0 ≤ s) (hvisit : η ω s ∈ cfPocket (R ω) (L ω) r) :
    ((visitCap R L r η ψ ω s).toNNReal : ℝ≥0∞) < capLife (travAll R L r η ψ ω) ∧
      (relChart c (travAll R L r η ψ) (visitCap R L r η ψ ω s).toNNReal ω).IsConformal ∧
      ((relChart c (travAll R L r η ψ) (visitCap R L r η ψ ω s).toNNReal ω).dom : Set ℂ) =
        cfPocket (R ω) (L ω) r ∩ (H \ fillH (η ω '' Icc 0 s)) := by
  obtain ⟨-, hlive, hdomS⟩ := visitCap_spec hω hcfg hψ hc hdom heq hs hvisit
  refine ⟨hlive, isConformal_relChart_of_driven (c := c) (γ := travAll R L r η ψ)
    (hcfg.isDrivenCurve hψ).1 hlive hc, ?_⟩
  rw [hdomS, hcfg.trace.2.2 s hs]

/-- **Visits before `T⁰(q)` have relative capacity at most `q`** (bounded change pocket). -/
theorem visitCap_le_of_lt_leftStop (hcfg : IsCfPocketConfig (R ω) (L ω) r (W ω) (η ω))
    (hψ : IsCfJordan (R ω) (L ω) r (ψ ω)) {q : ℝ≥0} (hq : (q : ℝ≥0∞) < capLife (travAll R L r η ψ ω))
    {s : ℝ} (hs : s ∈ visitSet (η ω) (cfPocket (R ω) (L ω) r) (firstHit (η ω) (cfArcR (R ω) (L ω) r 1))
      (firstHit (η ω) (cfArcR (R ω) (L ω) r 0)))
    (hsT : s < leftStop R L r η ψ q ω) : (visitCap R L r η ψ ω s).toNNReal ≤ q := by
  obtain ⟨hP, hψ'⟩ := pocket_of_cfg hcfg hψ
  have hq' : ENNReal.ofReal (q : ℝ) < capLife (trav (η ω) (cfPocket (R ω) (L ω) r)
      (firstHit (η ω) (cfArcR (R ω) (L ω) r 1)) (firstHit (η ω) (cfArcR (R ω) (L ω) r 0)) (ψ ω)) := by
    rw [ENNReal.ofReal_coe_nnreal]
    exact hq
  have hlt := relCap_lt_of_lt_ambTime0 hP hcfg.attach hψ' q.coe_nonneg hq' ⟨hs.1.1.le, hs.1.2⟩ hsT
  exact Real.toNNReal_le_iff_le_coe.2 hlt.le

/-- **The correct incident old access** (bounded change pocket; port of the late
`exists_actual_old_incident_access` to an arbitrary live current capacity): a current landing outside the domain of
an earlier visit reference, away from the outgoing corner, is reached in the old chart from a real coordinate `x`
along the current approach. -/
theorem exists_old_access (hω : ω ∈ A) (hcfg : IsCfPocketConfig (R ω) (L ω) r (W ω) (η ω))
    (hψ : IsCfJordan (R ω) (L ω) r (ψ ω)) (hc : (c ω).IsConformal)
    (hdom : ((c ω).dom : Set ℂ) = cfPocket (R ω) (L ω) r) (heq : EqOn (c ω).1 (ψ ω) (cfPocket (R ω) (L ω) r))
    {q : ℝ≥0} (hq : (q : ℝ≥0∞) < capLife (travAll R L r η ψ ω)) {s : ℝ} (hs : 0 ≤ s)
    (hsT : s ≤ leftStop R L r η ψ q ω) (hvisit : η ω s ∈ cfPocket (R ω) (L ω) r) {ξ : ℝ}
    (hBoundary : extendFrom H (relChart c (travAll R L r η ψ) q ω).2.1 ξ ∉
      (relChart c (travAll R L r η ψ) (visitCap R L r η ψ ω s).toNNReal ω).dom)
    (hNotExit : extendFrom H (relChart c (travAll R L r η ψ) q ω).2.1 ξ ≠ cfPt (openPt (R ω) (L ω) r)) :
    ∃ x : ℝ,
      Tendsto (fun z => (relChart c (travAll R L r η ψ) (visitCap R L r η ψ ω s).toNNReal ω).1
        ((relChart c (travAll R L r η ψ) q ω).2.1 z)) (𝓝[H] (ξ : ℂ)) (𝓝 (x : ℂ)) ∧
      Tendsto (relChart c (travAll R L r η ψ) (visitCap R L r η ψ ω s).toNNReal ω).2.1 (𝓝[H] (x : ℂ))
        (𝓝 (extendFrom H (relChart c (travAll R L r η ψ) q ω).2.1 ξ)) := by
  have hγ := (hcfg.isDrivenCurve hψ).1
  obtain ⟨hlive, hOld, hOldDom⟩ := visit_chart hω hcfg hψ hc hdom heq hs hvisit
  have hNow := isConformal_relChart_of_driven (c := c) (γ := travAll R L r η ψ) hγ hq hc
  have hIncl : ((relChart c (travAll R L r η ψ) q ω).dom : Set ℂ) ⊆
      (relChart c (travAll R L r η ψ) (visitCap R L r η ψ ω s).toNNReal ω).dom := by
    rw [current_dom_eq hω hcfg hψ hc hdom heq hq, hOldDom]
    exact fun z hz => ⟨hz.1, hz.2.1, fun h => hz.2.2 (fillH_mono (image_mono (Icc_subset_Icc_right hsT)) h)⟩
  obtain ⟨hLanding, hpcl, -⟩ := current_landing hω hcfg hψ hc hdom heq hq ξ
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

end Bounded

section Inf

variable {R L : Ω → ℝ≥0 → ℂ} {r : ℝ≥0} {W : Ω → ℝ → ℝ} {η : Ω → ℝ → ℂ} {ψ : Ω → ℂ → ℂ}
  {A : Set Ω} {c : Ω → Chart} {ω : Ω}

/-- The reverse pocket and its Jordan coordinate behind a seed-opening counterflow pocket configuration. -/
theorem pocket_of_cfgInf (hcfg : IsCfPocketConfigInf (R ω) (L ω) r (W ω) (η ω))
    (hψ : IsCfJordanInf (R ω) (L ω) r (ψ ω)) :
    IsReversePocketInf (W ω) (η ω) (cfPocket (R ω) (L ω) r) (cfArcRInf (R ω) (L ω) r)
        (cfArcLInf (R ω) (L ω) r) (firstHit (η ω) (cfArcRInf (R ω) (L ω) r 0)) ∧
      IsJordanCoordInf (cfPocket (R ω) (L ω) r) (cfArcRInf (R ω) (L ω) r 0) (ψ ω) := by
  refine ⟨hcfg.isReversePocketInf, ?_⟩
  rw [PocketCoord.IsChangeConfigInc.cfArcRInf_zero]
  exact hψ

/-- `T⁰(q) ≥ 0` (pocket opening at the flow seed). -/
theorem leftStopInf_nonneg (hcfg : IsCfPocketConfigInf (R ω) (L ω) r (W ω) (η ω))
    (hψ : IsCfJordanInf (R ω) (L ω) r (ψ ω)) (q : ℝ≥0) : 0 ≤ leftStopInf R L r η ψ q ω :=
  (pocket_of_cfgInf hcfg hψ).1.nonneg.trans
    (le_ambTime0Inf (pocket_of_cfgInf hcfg hψ).1 hcfg.attach (ψ ω) q)

/-- **The current domain at a live relative capacity** (pocket opening at the flow seed). -/
theorem current_dom_eqInf (hω : ω ∈ A) (hcfg : IsCfPocketConfigInf (R ω) (L ω) r (W ω) (η ω))
    (hψ : IsCfJordanInf (R ω) (L ω) r (ψ ω)) (hc : (c ω).IsConformal)
    (hdom : ((c ω).dom : Set ℂ) = cfPocket (R ω) (L ω) r) (heq : EqOn (c ω).1 (ψ ω) (cfPocket (R ω) (L ω) r))
    {q : ℝ≥0} (hq : (q : ℝ≥0∞) < capLife (travAllInf R L r η ψ ω)) :
    ((relChart c (travAllInf R L r η ψ) q ω).dom : Set ℂ) =
      cfPocket (R ω) (L ω) r ∩ (H \ fillH (η ω '' Icc 0 (leftStopInf R L r η ψ q ω))) := by
  obtain ⟨hP, -⟩ := pocket_of_cfgInf hcfg hψ
  rw [← activeDom_eq_relChart_dom hω hq (hcfg.isDrivenCurve hψ).1 hc,
    activeDom_cfPocketInf_eq_stopHull hω hcfg hψ hc hdom heq hq, stopHullInf,
    ← inter_domain_ambTime0Inf hP hcfg.attach (ψ ω) (q : ℝ), ← hcfg.trace.2.2 _ (leftStopInf_nonneg hcfg hψ q)]
  rfl

/-- **The physical landing of a real current coordinate** (pocket opening at the flow seed). -/
theorem current_landingInf (hω : ω ∈ A) (hcfg : IsCfPocketConfigInf (R ω) (L ω) r (W ω) (η ω))
    (hψ : IsCfJordanInf (R ω) (L ω) r (ψ ω)) (hc : (c ω).IsConformal)
    (hdom : ((c ω).dom : Set ℂ) = cfPocket (R ω) (L ω) r) (heq : EqOn (c ω).1 (ψ ω) (cfPocket (R ω) (L ω) r))
    {q : ℝ≥0} (hq : (q : ℝ≥0∞) < capLife (travAllInf R L r η ψ ω)) (ξ : ℝ) :
    Tendsto (relChart c (travAllInf R L r η ψ) q ω).2.1 (𝓝[H] (ξ : ℂ))
        (𝓝 (extendFrom H (relChart c (travAllInf R L r η ψ) q ω).2.1 ξ)) ∧
      extendFrom H (relChart c (travAllInf R L r η ψ) q ω).2.1 ξ ∈ closure (cfPocket (R ω) (L ω) r) ∧
      extendFrom H (relChart c (travAllInf R L r η ψ) q ω).2.1 ξ ∈
        frontier (cfPocket (R ω) (L ω) r ∩ (H \ fillH (η ω '' Icc 0 (leftStopInf R L r η ψ q ω)))) := by
  have hγ := (hcfg.isDrivenCurve hψ).1
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
    rwa [current_dom_eqInf hω hcfg hψ hc hdom heq hq] at hf

/-- **The relative chart at an original interior visit** (pocket opening at the flow seed). -/
theorem visit_chartInf (hω : ω ∈ A) (hcfg : IsCfPocketConfigInf (R ω) (L ω) r (W ω) (η ω))
    (hψ : IsCfJordanInf (R ω) (L ω) r (ψ ω)) (hc : (c ω).IsConformal)
    (hdom : ((c ω).dom : Set ℂ) = cfPocket (R ω) (L ω) r) (heq : EqOn (c ω).1 (ψ ω) (cfPocket (R ω) (L ω) r))
    {s : ℝ} (hs : 0 ≤ s) (hvisit : η ω s ∈ cfPocket (R ω) (L ω) r) :
    ((visitCapInf R L r η ψ ω s).toNNReal : ℝ≥0∞) < capLife (travAllInf R L r η ψ ω) ∧
      (relChart c (travAllInf R L r η ψ) (visitCapInf R L r η ψ ω s).toNNReal ω).IsConformal ∧
      ((relChart c (travAllInf R L r η ψ) (visitCapInf R L r η ψ ω s).toNNReal ω).dom : Set ℂ) =
        cfPocket (R ω) (L ω) r ∩ (H \ fillH (η ω '' Icc 0 s)) := by
  obtain ⟨-, hlive, hdomS⟩ := visitCapInf_spec hω hcfg hψ hc hdom heq hs hvisit
  refine ⟨hlive, isConformal_relChart_of_driven (c := c) (γ := travAllInf R L r η ψ)
    (hcfg.isDrivenCurve hψ).1 hlive hc, ?_⟩
  rw [hdomS, hcfg.trace.2.2 s hs]

/-- **Visits before `T⁰(q)` have relative capacity at most `q`** (pocket opening at the flow seed). -/
theorem visitCapInf_le_of_lt_leftStopInf (hcfg : IsCfPocketConfigInf (R ω) (L ω) r (W ω) (η ω))
    (hψ : IsCfJordanInf (R ω) (L ω) r (ψ ω)) {q : ℝ≥0} (hq : (q : ℝ≥0∞) < capLife (travAllInf R L r η ψ ω))
    {s : ℝ} (hs : s ∈ visitSetInf (η ω) (cfPocket (R ω) (L ω) r) (firstHit (η ω) (cfArcRInf (R ω) (L ω) r 0)))
    (hsT : s < leftStopInf R L r η ψ q ω) : (visitCapInf R L r η ψ ω s).toNNReal ≤ q := by
  obtain ⟨hP, hψ'⟩ := pocket_of_cfgInf hcfg hψ
  have hq' : ENNReal.ofReal (q : ℝ) < capLife (travInf (η ω) (cfPocket (R ω) (L ω) r)
      (firstHit (η ω) (cfArcRInf (R ω) (L ω) r 0)) (ψ ω)) := by
    rw [ENNReal.ofReal_coe_nnreal]
    exact hq
  have hlt := relCapInf_lt_of_lt_ambTime0Inf hP hcfg.attach hψ' q.coe_nonneg hq' hs.1.le hsT
  exact Real.toNNReal_le_iff_le_coe.2 hlt.le

/-- **The correct incident old access** (pocket opening at the flow seed; no corner exclusion). -/
theorem exists_old_accessInf (hω : ω ∈ A) (hcfg : IsCfPocketConfigInf (R ω) (L ω) r (W ω) (η ω))
    (hψ : IsCfJordanInf (R ω) (L ω) r (ψ ω)) (hc : (c ω).IsConformal)
    (hdom : ((c ω).dom : Set ℂ) = cfPocket (R ω) (L ω) r) (heq : EqOn (c ω).1 (ψ ω) (cfPocket (R ω) (L ω) r))
    {q : ℝ≥0} (hq : (q : ℝ≥0∞) < capLife (travAllInf R L r η ψ ω)) {s : ℝ} (hs : 0 ≤ s)
    (hsT : s ≤ leftStopInf R L r η ψ q ω) (hvisit : η ω s ∈ cfPocket (R ω) (L ω) r) {ξ : ℝ}
    (hBoundary : extendFrom H (relChart c (travAllInf R L r η ψ) q ω).2.1 ξ ∉
      (relChart c (travAllInf R L r η ψ) (visitCapInf R L r η ψ ω s).toNNReal ω).dom) :
    ∃ x : ℝ,
      Tendsto (fun z => (relChart c (travAllInf R L r η ψ) (visitCapInf R L r η ψ ω s).toNNReal ω).1
        ((relChart c (travAllInf R L r η ψ) q ω).2.1 z)) (𝓝[H] (ξ : ℂ)) (𝓝 (x : ℂ)) ∧
      Tendsto (relChart c (travAllInf R L r η ψ) (visitCapInf R L r η ψ ω s).toNNReal ω).2.1 (𝓝[H] (x : ℂ))
        (𝓝 (extendFrom H (relChart c (travAllInf R L r η ψ) q ω).2.1 ξ)) := by
  have hγ := (hcfg.isDrivenCurve hψ).1
  obtain ⟨hlive, hOld, hOldDom⟩ := visit_chartInf hω hcfg hψ hc hdom heq hs hvisit
  have hNow := isConformal_relChart_of_driven (c := c) (γ := travAllInf R L r η ψ) hγ hq hc
  have hIncl : ((relChart c (travAllInf R L r η ψ) q ω).dom : Set ℂ) ⊆
      (relChart c (travAllInf R L r η ψ) (visitCapInf R L r η ψ ω s).toNNReal ω).dom := by
    rw [current_dom_eqInf hω hcfg hψ hc hdom heq hq, hOldDom]
    exact fun z hz => ⟨hz.1, hz.2.1, fun h => hz.2.2 (fillH_mono (image_mono (Icc_subset_Icc_right hsT)) h)⟩
  obtain ⟨hLanding, hpcl, -⟩ := current_landingInf hω hcfg hψ hc hdom heq hq ξ
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

end Inf

end InteractingSLE.Sec7.R5Ref
