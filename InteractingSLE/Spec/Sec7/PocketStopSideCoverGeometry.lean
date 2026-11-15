/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.PocketStopSideComparison
import InteractingSLE.Spec.Sec7.PocketStopFieldAssembly
import InteractingSLE.Foundations.Topology.PathComplement

/-!
# Filled boundary references and the relative chart

PROVE-STRIPSYS38, continuation. References include the pocket exterior: a thin wall
alone cannot locally agree with `activeCompl`. The two incoming-side labels and the
nonnegative rational old counterflow times form a countable reference family.
The geometric lemmas below prove local agreement whenever the added hull stays away,
the inverse-chart approach, and the unbounded-complement condition for the active set.
No Theorem 1.2/1.3 is used (R48).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology Metric Bornology
open QuantumZipper (H fwdHull chiC)
open scoped NNReal ENNReal Real

namespace InteractingSLE.Sec7.PocketStopSide

open LocalSets PocketTraversal PocketAdapt Lemma71C PocketStop PocketUnionPt
  PocketStopField PocketCoupling

/-- Two incoming wall-side labels, followed by rational old counterflow times. -/
abbrev CoverRef := (Fin 2) ⊕ ℚ≥0

/-- Incoming-side references contain no counterflow hull; old references contain the
counterflow hull at their rational original time. The pocket exterior is added below. -/
def referenceHull {Ω : Type*} (F : ℚ≥0 → Ω → Set ℂ) : CoverRef → Ω → Set ℂ :=
  Sum.elim (fun _ _ => ∅) F

/-- A reference set includes the pocket exterior, on both incoming-side labels. -/
def referenceSet {Ω : Type*} (C : Ω → Set ℂ) (F : ℚ≥0 → Ω → Set ℂ)
    (i : CoverRef) (ω : Ω) : Set ℂ := extHullSet (C ω) (referenceHull F i ω)

/-- The only discrepancy between two filled references comes from the added hull. -/
theorem extHullSet_inter_ball_eq {C F G : Set ℂ} {p : ℂ} {r : ℝ}
    (hGF : G ⊆ F) (haway : Disjoint (F \ G) (ball p r)) :
    extHullSet C F ∩ ball p r = extHullSet C G ∩ ball p r := by
  ext z
  simp only [extHullSet, mem_inter_iff, mem_union, mem_compl_iff]
  constructor
  · rintro ⟨⟨hzH, hzC | hzF⟩, hzr⟩
    · exact ⟨⟨hzH, Or.inl hzC⟩, hzr⟩
    · refine ⟨⟨hzH, Or.inr ?_⟩, hzr⟩
      by_contra hzG
      exact disjoint_left.1 haway ⟨hzF, hzG⟩ hzr
  · rintro ⟨⟨hzH, hzC | hzG⟩, hzr⟩
    · exact ⟨⟨hzH, Or.inl hzC⟩, hzr⟩
    · exact ⟨⟨hzH, Or.inr (hGF hzG)⟩, hzr⟩

/-- Local equality supplies both containments required by Proposition 3.8. -/
theorem local_agreement_of_inter_ball_eq {K B : Set ℂ} {p : ℂ} {r : ℝ}
    (hr : 0 < r) (heq : K ∩ ball p r = B ∩ ball p r) :
    (∃ s > 0, B ∩ ball p s ⊆ K) ∧ (∃ s > 0, K ∩ ball p s ⊆ B) := by
  refine ⟨⟨r, hr, ?_⟩, ⟨r, hr, ?_⟩⟩
  · intro z hz
    exact ((heq.symm ▸ hz : z ∈ K ∩ ball p r)).1
  · intro z hz
    exact ((heq ▸ hz : z ∈ B ∩ ball p r)).1

/-- A physical landing from the active domain also approaches the common complement
when the reference and active closed sets agree locally at the landing point. -/
theorem tendsto_common_compl {f : ℂ → ℂ} {K B : Set ℂ} {p : ℂ} {ξ : ℝ}
    (hland : Tendsto f (𝓝[H] (ξ : ℂ)) (𝓝 p))
    (hmap : ∀ y ∈ H, f y ∈ H \ K) {r : ℝ} (hr : 0 < r)
    (heq : K ∩ ball p r = B ∩ ball p r) :
    Tendsto f (𝓝[H] (ξ : ℂ)) (𝓝[H \ (K ∪ B)] p) := by
  refine tendsto_nhdsWithin_iff.2 ⟨hland, ?_⟩
  filter_upwards [hland.eventually (isOpen_ball.mem_nhds (mem_ball_self hr)),
    self_mem_nhdsWithin] with y hyr hyH
  obtain ⟨hyH', hyK⟩ := hmap y hyH
  refine ⟨hyH', fun hy => hy.elim hyK fun hyB => ?_⟩
  exact hyK ((heq.symm ▸ (show f y ∈ B ∩ ball p r from ⟨hyB, hyr⟩) :
    f y ∈ K ∩ ball p r)).1

/-- The relative chart domain is exactly the active domain before its lifetime. -/
theorem activeDom_eq_relChart_dom {Ω : Type*} {A : Set Ω} {γ : Ω → ℝ → ℂ}
    {c : Ω → Chart} {q : ℝ≥0} {ω : Ω} (hω : ω ∈ A)
    (hq : (q : ℝ≥0∞) < capLife (γ ω)) (hγ : IsDrivenCurve (γ ω))
    (hc : (c ω).IsConformal) :
    activeDom A γ c q ω = ((relChart c γ q ω).dom : Set ℂ) := by
  obtain ⟨W, hW, hW0, q', hqq', hWeq, hrel⟩ := exists_relChart_eq_loewner (c := c) hγ hq
  have hconf := hc.loewner hW hW0 q.coe_nonneg
  rw [activeDom_eq hω hq, hrel, hconf.coe_dom]
  change (c ω).2.1 '' (H \ fwdHull _ q) = ((c ω).2.1 ∘ QuantumZipper.fwdMapInv W q) '' H
  rw [image_comp, QuantumZipper.RS.image_fwdMapInv_H hW hW0 q.coe_nonneg,
    fwdHull_eq_of_eqOn q.coe_nonneg hqq' hWeq]

/-- The inverse relative chart maps the upper half-plane into the actual active set. -/
theorem relChart_inv_mem_active {Ω : Type*} {A : Set Ω} {γ : Ω → ℝ → ℂ}
    {c : Ω → Chart} {q : ℝ≥0} {ω : Ω} (hω : ω ∈ A)
    (hq : (q : ℝ≥0∞) < capLife (γ ω)) (hγ : IsDrivenCurve (γ ω))
    (hc : (c ω).IsConformal) {y : ℂ} (hy : y ∈ H) :
    (relChart c γ q ω).2.1 y ∈ H \ activeCompl A γ c q ω := by
  obtain ⟨W, hW, hW0, -, -, -, hrel⟩ := exists_relChart_eq_loewner (c := c) hγ hq
  have hconf : (relChart c γ q ω).IsConformal := hrel ▸ hc.loewner hW hW0 q.coe_nonneg
  have hmem := hconf.inv_mem_dom hy
  have hact := activeDom_eq_relChart_dom hω hq hγ hc
  have hzA : (relChart c γ q ω).2.1 y ∈ activeDom A γ c q ω := hact ▸ hmem
  exact ⟨hconf.dom_subset hmem, fun hz => hz.2 hzA⟩

/-- A chart domain has no bounded complementary component. -/
theorem not_isBounded_lowerUnion_of_chart {K : Set ℂ} {c : Chart}
    (hc : c.IsConformal) (hdom : H \ K = (c.dom : Set ℂ)) :
    ∀ p ∈ lowerUnion K, ¬ IsBounded (connectedComponentIn (lowerUnion K) p) := by
  have hsc := isSimplyConnected_of_isConformalBijection QuantumZipper.isOpen_H
    hc.isConformalBijection isSimplyConnected_H
  have heq : lowerUnion K = (c.dom : Set ℂ)ᶜ := by
    rw [← compl_H_diff_eq, hdom]
  intro p hp
  rw [heq] at hp ⊢
  exact not_isBounded_connectedComponentIn_compl_of_isSimplyConnected c.dom.isOpen hsc hp

/-- The active complement satisfies the unbounded-component hypothesis of the
comparison theorem, including samples outside the live event. -/
theorem not_isBounded_lowerUnion_activeCompl {Ω : Type*} {A : Set Ω}
    {γ : Ω → ℝ → ℂ} {c : Ω → Chart} {q : ℝ≥0}
    (hγ : ∀ ω ∈ A, IsDrivenCurve (γ ω)) (hc : ∀ ω ∈ A, (c ω).IsConformal)
    (ω : Ω) : ∀ p ∈ lowerUnion (activeCompl A γ c q ω),
      ¬ IsBounded (connectedComponentIn (lowerUnion (activeCompl A γ c q ω)) p) := by
  by_cases hl : ω ∈ A ∧ (q : ℝ≥0∞) < capLife (γ ω)
  · obtain ⟨W, hW, hW0, -, -, -, hrel⟩ := exists_relChart_eq_loewner (c := c) (hγ ω hl.1) hl.2
    have hconf : (relChart c γ q ω).IsConformal :=
      hrel ▸ (hc ω hl.1).loewner hW hW0 q.coe_nonneg
    apply not_isBounded_lowerUnion_of_chart hconf
    have hdom := activeDom_eq_relChart_dom hl.1 hl.2 (hγ ω hl.1) (hc ω hl.1)
    rw [activeCompl, sdiff_sdiff_cancel_left, hdom]
    exact hdom ▸ hconf.dom_subset
  · have hH : lowerUnion H = univ := by
      ext z
      simp only [lowerUnion, H, mem_union, mem_ofPred_eq, mem_univ, iff_true]
      exact lt_or_ge 0 z.im
    rw [activeCompl, activeDom_eq_empty hl, sdiff_empty, hH]
    intro p _
    rw [connectedComponentIn_univ, PreconnectedSpace.connectedComponent_eq_univ]
    exact NormedSpace.unbounded_univ ℝ ℂ

/-- Integer branch shifts preserve the relative inverse map. -/
theorem relChart_shift_inv {Ω : Type*} (c : Ω → Chart) (n : Ω → ℤ)
    (γ : Ω → ℝ → ℂ) (q : ℝ≥0) (ω : Ω) :
    (relChart (fun ω => shiftChart (c ω) (n ω)) γ q ω).2.1 =
      (relChart c γ q ω).2.1 := rfl

/-- The active set is independent of the integer branch of the derivative logarithm. -/
theorem activeCompl_shift {Ω : Type*} (A : Set Ω) (c : Ω → Chart) (n : Ω → ℤ)
    (γ : Ω → ℝ → ℂ) (q : ℝ≥0) :
    activeCompl A γ (fun ω => shiftChart (c ω) (n ω)) q = activeCompl A γ c q := rfl

/-- The same integer shift persists after the relative Loewner map. -/
theorem relChart_shift_lift {Ω : Type*} (c : Ω → Chart) (n : Ω → ℤ)
    (γ : Ω → ℝ → ℂ) (q : ℝ≥0) (ω : Ω) (z : ℂ) :
    (relChart (fun ω => shiftChart (c ω) (n ω)) γ q ω).2.2 z =
      (relChart c γ q ω).2.2 z - 2 * Real.pi * n ω := by
  dsimp only [relChart, shiftChart, Chart.loewner]
  ring

/-- A finite landing of the inverse chart over a real coordinate lies on the
physical frontier of its domain; no boundary extension injectivity is required. -/
theorem mem_frontier_of_inv_land {c : Chart} (hc : c.IsConformal) {ξ : ℝ} {p : ℂ}
    (hland : Tendsto c.2.1 (𝓝[H] (ξ : ℂ)) (𝓝 p)) : p ∈ frontier (c.dom : Set ℂ) := by
  have hcl : (ξ : ℂ) ∈ closure H := by
    rw [QuantumZipper.CA.Car.closure_H_eq_Hbar]
    change 0 ≤ (ξ : ℂ).im
    simp only [Complex.ofReal_im, le_refl]
  have : (𝓝[H] (ξ : ℂ)).NeBot := mem_closure_iff_nhdsWithin_neBot.1 hcl
  have hyH : ∀ᶠ y : ℂ in 𝓝[H] (ξ : ℂ), y ∈ H := self_mem_nhdsWithin
  have hpcl : p ∈ closure (c.dom : Set ℂ) :=
    mem_closure_of_tendsto hland (hyH.mono fun y hy => hc.inv_mem_dom hy)
  rw [c.dom.isOpen.frontier_eq]
  refine ⟨hpcl, fun hp => ?_⟩
  have hcont : ContinuousAt c.1 p :=
    (hc.differentiableOn_fwd.continuousOn p hp).continuousAt (c.dom.isOpen.mem_nhds hp)
  have hid : Tendsto (fun y => c.1 (c.2.1 y)) (𝓝[H] (ξ : ℂ)) (𝓝 (ξ : ℂ)) :=
    (tendsto_id.mono_left nhdsWithin_le_nhds).congr'
      (hyH.mono fun y hy => (hc.2.2 y hy).symm)
  have heq := tendsto_nhds_unique (hcont.tendsto.comp hland) hid
  have hpH := hc.fwd_mem hp
  rw [heq] at hpH
  exact (lt_irrefl (0 : ℝ)) (by simpa only [H, mem_ofPred_eq, Complex.ofReal_im] using hpH)

/-- The physical boundary of the active pocket is on an incoming wall or on the
counterflow hull. This only assumes a finite landing inside the ambient half-plane. -/
theorem active_landing_on_wall_or_hull {Ω : Type*} {A : Set Ω} {γ : Ω → ℝ → ℂ}
    {c : Ω → Chart} {q : ℝ≥0} {ω : Ω} (hω : ω ∈ A)
    (hq : (q : ℝ≥0∞) < capLife (γ ω)) (hγ : IsDrivenCurve (γ ω))
    (hc : (c ω).IsConformal) {C F : Set ℂ}
    (hact : activeDom A γ c q ω = C ∩ (H \ F)) (hFo : IsOpen (H \ F))
    {ξ : ℝ} {p : ℂ} (hpH : p ∈ H)
    (hland : Tendsto (relChart c γ q ω).2.1 (𝓝[H] (ξ : ℂ)) (𝓝 p)) :
    p ∈ frontier C ∪ F := by
  obtain ⟨W, hW, hW0, -, -, -, hrel⟩ := exists_relChart_eq_loewner (c := c) hγ hq
  have hconf : (relChart c γ q ω).IsConformal := hrel ▸ hc.loewner hW hW0 q.coe_nonneg
  have hp := mem_frontier_of_inv_land hconf hland
  rw [← activeDom_eq_relChart_dom hω hq hγ hc, hact] at hp
  rcases frontier_inter_subset C (H \ F) hp with hp | hp
  · exact Or.inl hp.1
  · right
    by_contra hpF
    rw [hFo.frontier_eq] at hp
    exact hp.2.2 ⟨hpH, hpF⟩

end InteractingSLE.Sec7.PocketStopSide
