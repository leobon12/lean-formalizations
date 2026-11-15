/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.R5RefCurrent

/-!
# Lemma R.5 on an R.7 test: the unfilled collar of an earlier visit reference

Packet PROVE-R5-REFCHART. Proof of Lemma R.5 (spec p. 475): "Since `p ≠ η(T)`, choose an original rational time
`s < T`, after the first visit to `p`, such that the final ambient range `η([s, T])` avoids a physical ball
`B(p, ε)`. The continuous inverse of the own increment sends `v` to some `u ∈ ℝ` … a smaller such half-disc has not
been filled by the increment." For the change pocket of an R.7 test this file constructs, at EVERY positive live
relative capacity `q` and every real current coordinate `ξ` whose landing `p` is neither the current tip `η(T⁰(q))`
nor (bounded pocket) the outgoing corner, a rational interior visit `s < T⁰(q)` of capacity at most `q` and an
unfilled half-disc of its relative chart:

* `IsRefCollar` (def): the collar data consumed by R.5's cover (`R5Phase.R5Clauses`, clause 5) and by the height and
  lift transport (`pocketTransitionChart`, `currentPocketContacts`);
* `isRefCollar_self`: a chart is its own collar (the reference at relative capacity `0`);
* **`exists_visit_collar`**, **`exists_visit_collarInf`**.

The reference time is taken at the LEFT stop `T⁰(q)` (ruling R67): interior visits accumulate at `T⁰(q)` from below
(`R5Ref.exists_rat_visit_lt_ambTime0`), and the current domain is `C ∩ (ℍ ∖ fill η([0, T⁰(q)]))`
(`R5Ref.current_dom_eq`). Port of the late `SideTest.exists_rat_unfilled_collar_at_current_landing` (stated there
at original visit times only). Ruling R48: nothing here uses Theorem 1.2/1.3.
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

/-- **An unfilled R.5 collar** of the current chart `now` at its real coordinate `ξ`, read in the old chart `old`:
the old inverse maps the half-disc `ℍ ∩ B(x, ε)` into the current domain, the transition `old ∘ now⁻¹` tends to the
real old coordinate `x` at `ξ`, the old inverse tends to the current landing `p` within the current domain, and the
half-disc avoids the current pocket contacts and lies in the transition chart's domain. -/
def IsRefCollar (old now : Chart) (ξ : ℝ) (p : ℂ) (x ε : ℝ) : Prop :=
  0 < ε ∧ old.2.1 '' (H ∩ ball (x : ℂ) ε) ⊆ (now.dom : Set ℂ) ∧
    Tendsto (fun z => old.1 (now.2.1 z)) (𝓝[H] (ξ : ℂ)) (𝓝 (x : ℂ)) ∧
    Tendsto old.2.1 (𝓝[H] (x : ℂ)) (𝓝[(now.dom : Set ℂ)] p) ∧
    Disjoint (ball (x : ℂ) ε) (currentPocketContacts old now) ∧
    H ∩ ball (x : ℂ) ε ⊆ ((pocketTransitionChart old now).dom : Set ℂ)

/-- **A conformal chart is its own collar** at every real coordinate with a landing. -/
theorem isRefCollar_self {now : Chart} (hNow : now.IsConformal) {ξ : ℝ} {p : ℂ}
    (hLanding : Tendsto now.2.1 (𝓝[H] (ξ : ℂ)) (𝓝 p)) : IsRefCollar now now ξ p ξ 1 := by
  have hCur : now.2.1 '' (H ∩ ball (ξ : ℂ) 1) ⊆ (now.dom : Set ℂ) := by
    rintro _ ⟨z, hz, rfl⟩
    exact hNow.inv_mem_dom hz.1
  have hCollar := halfDisc_subset_transition_of_inverse_image hNow hNow subset_rfl hCur
  refine ⟨one_pos, hCur, ?_, ?_, disjoint_currentPocketContacts_of_halfDisc hNow hNow subset_rfl hCollar, hCollar⟩
  · exact (show Tendsto (fun z : ℂ => z) (𝓝[H] (ξ : ℂ)) (𝓝 (ξ : ℂ)) from nhdsWithin_le_nhds).congr'
      (eventually_nhdsWithin_of_forall fun z hz => (hNow.2.2 z hz).symm)
  · exact tendsto_nhdsWithin_iff.2 ⟨hLanding, eventually_nhdsWithin_of_forall fun z hz => hNow.inv_mem_dom hz⟩

/-- **The landing of a collar is a boundary point of the old domain.** -/
theorem IsRefCollar.notMem_dom {old now : Chart} {ξ : ℝ} {p : ℂ} {x ε : ℝ} (h : IsRefCollar old now ξ p x ε)
    (hOld : old.IsConformal) : p ∉ old.dom :=
  inverse_real_landing_notMem_dom hOld (tendsto_nhdsWithin_iff.1 h.2.2.2.1).1

variable {Ω : Type*}

section Bounded

variable {R L : Ω → ℝ≥0 → ℂ} {r : ℝ≥0} {W : Ω → ℝ → ℝ} {η : Ω → ℝ → ℂ} {ψ : Ω → ℂ → ℂ}
  {A : Set Ω} {c : Ω → Chart} {ω : Ω}

/-- **Lemma R.5's unfilled visit collar** (bounded change pocket): at a positive live relative capacity `q`, every
real current coordinate `ξ` whose landing is neither the current tip `η(T⁰(q))` nor the outgoing corner has a
rational interior visit `s < T⁰(q)` of capacity at most `q` whose relative chart carries an unfilled collar. -/
theorem exists_visit_collar (hω : ω ∈ A) (hcfg : IsCfPocketConfig (R ω) (L ω) r (W ω) (η ω))
    (hψ : IsCfJordan (R ω) (L ω) r (ψ ω)) (hc : (c ω).IsConformal)
    (hdom : ((c ω).dom : Set ℂ) = cfPocket (R ω) (L ω) r) (heq : EqOn (c ω).1 (ψ ω) (cfPocket (R ω) (L ω) r))
    {q : ℝ≥0} (hq0 : 0 < q) (hq : (q : ℝ≥0∞) < capLife (travAll R L r η ψ ω)) (ξ : ℝ)
    (hNotTip : extendFrom H (relChart c (travAll R L r η ψ) q ω).2.1 ξ ≠ η ω (leftStop R L r η ψ q ω))
    (hNotExit : extendFrom H (relChart c (travAll R L r η ψ) q ω).2.1 ξ ≠ cfPt (openPt (R ω) (L ω) r)) :
    ∃ s : ℚ, 0 ≤ (s : ℝ) ∧ η ω s ∈ cfPocket (R ω) (L ω) r ∧ (visitCap R L r η ψ ω s).toNNReal ≤ q ∧
      η ω s ≠ extendFrom H (relChart c (travAll R L r η ψ) q ω).2.1 ξ ∧
      ∃ x ε : ℝ, IsRefCollar (relChart c (travAll R L r η ψ) (visitCap R L r η ψ ω s).toNNReal ω)
        (relChart c (travAll R L r η ψ) q ω) ξ (extendFrom H (relChart c (travAll R L r η ψ) q ω).2.1 ξ) x ε := by
  obtain ⟨hP, hψ'⟩ := pocket_of_cfg hcfg hψ
  have hq' : ENNReal.ofReal (q : ℝ) < capLife (trav (η ω) (cfPocket (R ω) (L ω) r)
      (firstHit (η ω) (cfArcR (R ω) (L ω) r 1)) (firstHit (η ω) (cfArcR (R ω) (L ω) r 0)) (ψ ω)) := by
    rw [ENNReal.ofReal_coe_nnreal]
    exact hq
  have hγ := (hcfg.isDrivenCurve hψ).1
  have hT0 : 0 < leftStop R L r η ψ q ω :=
    hP.nonneg.trans_lt (lt_ambTime0 hP hcfg.attach hψ' (NNReal.coe_pos.2 hq0) hq')
  have hCH : cfPocket (R ω) (L ω) r ⊆ H := by
    rw [← hdom, hc.coe_dom]
    exact hc.2.1.image_subset
  obtain ⟨-, -, hFrontier⟩ := current_landing hω hcfg hψ hc hdom heq hq ξ
  obtain ⟨a, ha0, -, haT, hAway⟩ := exists_old_interval_excluding_current_frontier hcfg.trace.2.1 hP.isOpen hCH
    le_rfl hT0 hFrontier hNotTip
  obtain ⟨s₁, has₁, hs₁T, ρ, hρ, hTail₁⟩ := exists_rat_terminal_trace_avoids hcfg.trace.2.1 ha0 haT hNotTip
  obtain ⟨s, hs₁s, hsT, hsv⟩ :=
    exists_rat_visit_lt_ambTime0 hP hcfg.attach hψ' (NNReal.coe_pos.2 hq0) hq' hs₁T
  have hs0 : 0 ≤ (s : ℝ) := ha0.trans (has₁.le.trans hs₁s.le)
  replace hsT : (s : ℝ) < leftStop R L r η ψ q ω := hsT
  have hTail : Disjoint (η ω '' Icc (s : ℝ) (leftStop R L r η ψ q ω))
      (closedBall (extendFrom H (relChart c (travAll R L r η ψ) q ω).2.1 ξ) ρ) :=
    hTail₁.mono_left (image_mono (Icc_subset_Icc_left hs₁s.le))
  have hQ := visitCap_le_of_lt_leftStop hcfg hψ hq hsv hsT
  obtain ⟨-, hOld, hOldDom⟩ := visit_chart hω hcfg hψ hc hdom heq hs0 hsv.2
  have hNow := isConformal_relChart_of_driven (c := c) (γ := travAll R L r η ψ) hγ hq hc
  have hNowDom := current_dom_eq hω hcfg hψ hc hdom heq hq
  have hBoundary : extendFrom H (relChart c (travAll R L r η ψ) q ω).2.1 ξ ∉
      (relChart c (travAll R L r η ψ) (visitCap R L r η ψ ω s).toNNReal ω).dom := fun h =>
    hAway s (has₁.trans hs₁s) (by rw [← hOldDom]; exact h)
  obtain ⟨x, hTransition, hOldLanding⟩ :=
    exists_old_access hω hcfg hψ hc hdom heq hq hs0 hsT.le hsv.2 hBoundary hNotExit
  have hIncident := old_access_mem_closure_of_current_transition hNow hTransition
  rw [hNowDom] at hIncident
  obtain ⟨ε, hε, -, hCur, -⟩ := exists_old_trace_halfDisc_in_current_domain hcfg.trace.2.1 hs0 hsT.le hOld
    hOldDom hOldLanding hIncident hρ hTail
  rw [← hNowDom] at hCur
  have hIncl : ((relChart c (travAll R L r η ψ) q ω).dom : Set ℂ) ⊆
      (relChart c (travAll R L r η ψ) (visitCap R L r η ψ ω s).toNNReal ω).dom := by
    rw [hNowDom, hOldDom]
    exact fun z hz => ⟨hz.1, hz.2.1, fun h => hz.2.2 (fillH_mono (image_mono (Icc_subset_Icc_right hsT.le)) h)⟩
  have hCollar := halfDisc_subset_transition_of_inverse_image hOld hNow hIncl hCur
  have hne : η ω s ≠ extendFrom H (relChart c (travAll R L r η ψ) q ω).2.1 ξ := fun h =>
    disjoint_left.1 hTail ⟨(s : ℝ), ⟨le_rfl, hsT.le⟩, rfl⟩ (h ▸ mem_closedBall_self hρ.le)
  exact ⟨s, hs0, hsv.2, hQ, hne, x, ε, hε, hCur, hTransition,
    tendsto_old_inverse_within_current_of_halfDisc hOldLanding hε hCur,
    disjoint_currentPocketContacts_of_halfDisc hOld hNow hIncl hCollar, hCollar⟩

end Bounded

section Inf

variable {R L : Ω → ℝ≥0 → ℂ} {r : ℝ≥0} {W : Ω → ℝ → ℝ} {η : Ω → ℝ → ℂ} {ψ : Ω → ℂ → ℂ}
  {A : Set Ω} {c : Ω → Chart} {ω : Ω}

/-- **Lemma R.5's unfilled visit collar** (change pocket opening at the flow seed): at a positive live relative
capacity `q`, every real current coordinate `ξ` whose landing is not the current tip `η(T⁰(q))` has a rational
interior visit `s < T⁰(q)` of capacity at most `q` whose relative chart carries an unfilled collar. -/
theorem exists_visit_collarInf (hω : ω ∈ A) (hcfg : IsCfPocketConfigInf (R ω) (L ω) r (W ω) (η ω))
    (hψ : IsCfJordanInf (R ω) (L ω) r (ψ ω)) (hc : (c ω).IsConformal)
    (hdom : ((c ω).dom : Set ℂ) = cfPocket (R ω) (L ω) r) (heq : EqOn (c ω).1 (ψ ω) (cfPocket (R ω) (L ω) r))
    {q : ℝ≥0} (hq0 : 0 < q) (hq : (q : ℝ≥0∞) < capLife (travAllInf R L r η ψ ω)) (ξ : ℝ)
    (hNotTip : extendFrom H (relChart c (travAllInf R L r η ψ) q ω).2.1 ξ ≠ η ω (leftStopInf R L r η ψ q ω)) :
    ∃ s : ℚ, 0 ≤ (s : ℝ) ∧ η ω s ∈ cfPocket (R ω) (L ω) r ∧ (visitCapInf R L r η ψ ω s).toNNReal ≤ q ∧
      η ω s ≠ extendFrom H (relChart c (travAllInf R L r η ψ) q ω).2.1 ξ ∧
      ∃ x ε : ℝ, IsRefCollar (relChart c (travAllInf R L r η ψ) (visitCapInf R L r η ψ ω s).toNNReal ω)
        (relChart c (travAllInf R L r η ψ) q ω) ξ
        (extendFrom H (relChart c (travAllInf R L r η ψ) q ω).2.1 ξ) x ε := by
  obtain ⟨hP, hψ'⟩ := pocket_of_cfgInf hcfg hψ
  have hq' : ENNReal.ofReal (q : ℝ) < capLife (travInf (η ω) (cfPocket (R ω) (L ω) r)
      (firstHit (η ω) (cfArcRInf (R ω) (L ω) r 0)) (ψ ω)) := by
    rw [ENNReal.ofReal_coe_nnreal]
    exact hq
  have hγ := (hcfg.isDrivenCurve hψ).1
  have hT0 : 0 < leftStopInf R L r η ψ q ω :=
    hP.nonneg.trans_lt (lt_ambTime0Inf hP hcfg.attach hψ' (NNReal.coe_pos.2 hq0) hq')
  have hCH : cfPocket (R ω) (L ω) r ⊆ H := by
    rw [← hdom, hc.coe_dom]
    exact hc.2.1.image_subset
  obtain ⟨-, -, hFrontier⟩ := current_landingInf hω hcfg hψ hc hdom heq hq ξ
  obtain ⟨a, ha0, -, haT, hAway⟩ := exists_old_interval_excluding_current_frontier hcfg.trace.2.1 hP.isOpen hCH
    le_rfl hT0 hFrontier hNotTip
  obtain ⟨s₁, has₁, hs₁T, ρ, hρ, hTail₁⟩ := exists_rat_terminal_trace_avoids hcfg.trace.2.1 ha0 haT hNotTip
  obtain ⟨s, hs₁s, hsT, hsv⟩ :=
    exists_rat_visitInf_lt_ambTime0Inf hP hcfg.attach hψ' (NNReal.coe_pos.2 hq0) hq' hs₁T
  have hs0 : 0 ≤ (s : ℝ) := ha0.trans (has₁.le.trans hs₁s.le)
  replace hsT : (s : ℝ) < leftStopInf R L r η ψ q ω := hsT
  have hTail : Disjoint (η ω '' Icc (s : ℝ) (leftStopInf R L r η ψ q ω))
      (closedBall (extendFrom H (relChart c (travAllInf R L r η ψ) q ω).2.1 ξ) ρ) :=
    hTail₁.mono_left (image_mono (Icc_subset_Icc_left hs₁s.le))
  have hQ := visitCapInf_le_of_lt_leftStopInf hcfg hψ hq hsv hsT
  obtain ⟨-, hOld, hOldDom⟩ := visit_chartInf hω hcfg hψ hc hdom heq hs0 hsv.2
  have hNow := isConformal_relChart_of_driven (c := c) (γ := travAllInf R L r η ψ) hγ hq hc
  have hNowDom := current_dom_eqInf hω hcfg hψ hc hdom heq hq
  have hBoundary : extendFrom H (relChart c (travAllInf R L r η ψ) q ω).2.1 ξ ∉
      (relChart c (travAllInf R L r η ψ) (visitCapInf R L r η ψ ω s).toNNReal ω).dom := fun h =>
    hAway s (has₁.trans hs₁s) (by rw [← hOldDom]; exact h)
  obtain ⟨x, hTransition, hOldLanding⟩ :=
    exists_old_accessInf hω hcfg hψ hc hdom heq hq hs0 hsT.le hsv.2 hBoundary
  have hIncident := old_access_mem_closure_of_current_transition hNow hTransition
  rw [hNowDom] at hIncident
  obtain ⟨ε, hε, -, hCur, -⟩ := exists_old_trace_halfDisc_in_current_domain hcfg.trace.2.1 hs0 hsT.le hOld
    hOldDom hOldLanding hIncident hρ hTail
  rw [← hNowDom] at hCur
  have hIncl : ((relChart c (travAllInf R L r η ψ) q ω).dom : Set ℂ) ⊆
      (relChart c (travAllInf R L r η ψ) (visitCapInf R L r η ψ ω s).toNNReal ω).dom := by
    rw [hNowDom, hOldDom]
    exact fun z hz => ⟨hz.1, hz.2.1, fun h => hz.2.2 (fillH_mono (image_mono (Icc_subset_Icc_right hsT.le)) h)⟩
  have hCollar := halfDisc_subset_transition_of_inverse_image hOld hNow hIncl hCur
  have hne : η ω s ≠ extendFrom H (relChart c (travAllInf R L r η ψ) q ω).2.1 ξ := fun h =>
    disjoint_left.1 hTail ⟨(s : ℝ), ⟨le_rfl, hsT.le⟩, rfl⟩ (h ▸ mem_closedBall_self hρ.le)
  exact ⟨s, hs0, hsv.2, hQ, hne, x, ε, hε, hCur, hTransition,
    tendsto_old_inverse_within_current_of_halfDisc hOldLanding hε hCur,
    disjoint_currentPocketContacts_of_halfDisc hOld hNow hIncl hCollar, hCollar⟩

end Inf

end InteractingSLE.Sec7.R5Ref
