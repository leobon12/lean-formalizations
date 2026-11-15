/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GB11GateBoundary

/-!
# GB11: selected gate arms and the part of the frontier above the real line

This file records the precise remaining joint planar construction. Individual
global cuts and their finite/infinite lifts are already proved. Selecting and
compactifying both arms simultaneously, with their contact order, is distinguished
from the additional assertion that they enclose the incident real frontier.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Filter Topology Metric Bornology
open scoped NNReal ENNReal
open QuantumZipper (H Hbar fwdHull fwdMap)
open InteractingSLE.YuanSimpleApprox (trMap)

namespace InteractingSLE.Theorem14.GB11Chart

open GW4Traverse GW4Reg GB11Conn

/-- The unchanged hypotheses of the current-gate statement, collected for the
two remaining internal planar propositions. -/
structure GateSetup where
  W' : ℝ≥0 → ℝ
  γ : ℝ≥0 → ℂ
  continuous_driver : Continuous W'
  driver_zero : W' 0 = 0
  generating : IsGeneratingTrace W' ⊤ γ
  no_simple_interval : GB10.NoSimpleArcInterval γ ⊤
  αR : ℝ≥0 → ℂ
  αL : ℝ≥0 → ℂ
  barrier : GB11.IsGB11Barrier αR αL γ
  pocket_shape : WalkPocketShape αR αL
  C : Set ℂ
  component : C ∈ betweenComponents (range αR) (range αL)
  s₁ : ℝ≥0
  t₁ : ℝ≥0
  s₂ : ℝ≥0∞
  t₂ : ℝ≥0∞
  shape : IsPocketShape αR αL C s₁ t₁ s₂ t₂
  c : Chart
  chart : IsComponentChart (range αR) (range αL) C c
  exit_limit : Tendsto c.2.1 (𝓝[H] 0) (𝓝 (αR s₁))
  before_entry : ∀ t : ℝ≥0, t < entryTime γ αR s₂ → γ t ≠ 0 →
    -(γ t)⁻¹ ∉ closure C
  confined : ∀ t : ℝ≥0, entryTime γ αR s₂ ≤ t →
    (t : ℝ≥0∞) < GB11.firstVisit γ (αR s₁) → γ t ≠ 0 → -(γ t)⁻¹ ∈ closure C
  dense_visits : ∀ a b : ℝ≥0, entryTime γ αR s₂ ≤ a → a < b →
    (b : ℝ≥0∞) < GB11.firstVisit γ (αR s₁) →
    ∃ t ∈ Ioo a b, γ t ≠ 0 ∧ -(γ t)⁻¹ ∈ C
  t : ℝ≥0
  entry_le : entryTime γ αR s₂ ≤ t
  before_exit : (t : ℝ≥0∞) < GB11.firstVisit γ (αR s₁)

/-- The real-time ambient driver of a gate setup. -/
def GateSetup.driver (d : GateSetup) : ℝ → ℝ := fun r => d.W' r.toNNReal

/-- The exact global cut property, including an unattained cut at infinity. -/
def IsWallVisitCut (γ α : ℝ≥0 → ℂ) (t : ℝ≥0) (cut : ℝ≥0∞) : Prop :=
  0 < cut ∧ ∀ r : ℝ≥0, r ∈ wallHitParameters γ α t ↔ cut ≤ (r : ℝ≥0∞)

/-- Both wall cuts exist, and both exits are strictly before them. -/
theorem GateSetup.exists_cuts (d : GateSetup) :
    ∃ cutR cutL : ℝ≥0∞, IsWallVisitCut d.γ d.αR d.t cutR ∧
      IsWallVisitCut d.γ d.αL d.t cutL ∧ (d.s₁ : ℝ≥0∞) < cutR ∧
      (d.t₁ : ℝ≥0∞) < cutL := by
  have hγc := Sec5.continuous_of_isGeneratingTrace_top d.generating
  obtain ⟨cutR, hR0, hR, hRa⟩ := exists_wall_visit_cut hγc d.barrier.1.1
    d.barrier.1.2.2.1 d.barrier.2.2.2.2.2.1 d.t
  obtain ⟨cutL, hL0, hL, hLa⟩ := exists_wall_visit_cut hγc d.barrier.2.1.1
    d.barrier.2.1.2.2.1 d.barrier.2.2.2.2.2.2 d.t
  refine ⟨cutR, cutL, ⟨hR0, hR⟩, ⟨hL0, hL⟩, hRa _ d.before_exit, hLa _ ?_⟩
  rw [← d.shape.contact]
  exact d.before_exit

/-- The original target can be adherent to this pocket only when it is the
selected exit. This uses the exact wall frontier and simplicity of both walls. -/
theorem GateSetup.exit_eq_zero_of_zero_mem_closure (d : GateSetup)
    (h0 : (0 : ℂ) ∈ closure d.C) : d.s₁ = 0 := by
  have hCH : d.C ⊆ H := subset_H_of_mem_betweenComponents d.component
  have h0not : (0 : ℂ) ∉ d.C := fun hz => lt_irrefl (0 : ℝ) (hCH hz)
  have hfr : (0 : ℂ) ∈ frontier d.C :=
    ⟨h0, fun hi => h0not (interior_subset hi)⟩
  rcases d.shape.frontier_subset hfr with ⟨r, hr, he⟩ | ⟨r, hr, he⟩
  · have hr0 : r = 0 := d.barrier.1.2.1 (he.trans d.barrier.1.2.2.1.symm)
    exact le_antisymm (hr0 ▸ hr.1) zero_le
  · have hr0 : r = 0 := d.barrier.2.1.2.1 (he.trans d.barrier.2.1.2.2.1.symm)
    have ht0 : d.t₁ = 0 := le_antisymm (hr0 ▸ hr.1) zero_le
    apply d.barrier.1.2.1
    rw [d.shape.contact, ht0, d.barrier.2.1.2.2.1, d.barrier.1.2.2.1]

/-- The exact compactified image of one selected wall: its gate, all positive
unvisited parameters from the exit onwards, and the point at infinity when the
exit is the original target. The finite formula is never evaluated at parameter zero. -/
def selectedPrefixImage (d : GateSetup) (α : ℝ≥0 → ℂ) (exit : ℝ≥0)
    (cut : ℝ≥0∞) (q : ℝ) : Set ℂ :=
  {mu q} ∪ (fun r : ℝ≥0 => mu (forwardExt d.driver d.t (-(α r)⁻¹))) ''
    {r | 0 < r ∧ exit ≤ r ∧ (r : ℝ≥0∞) < cut} ∪ if exit = 0 then {0} else ∅

/-- Joint compactified realizations of the selected unvisited prefixes.
The exact image fields retain their actual physical wall parametrizations.
There is no base-intersection or frontier-enclosure assumption in this structure. -/
structure SelectedGateArms (d : GateSetup) (cutR cutL : ℝ≥0∞) where
  qR : ℝ
  qL : ℝ
  junction : ℂ
  rightWall : ℝ → ℂ
  leftWall : ℝ → ℂ
  gates_le : qR ≤ qL
  right_continuous : ContinuousOn rightWall (Icc 0 1)
  left_continuous : ContinuousOn leftWall (Icc 0 1)
  right_injective : InjOn rightWall (Icc 0 1)
  left_injective : InjOn leftWall (Icc 0 1)
  right_zero : rightWall 0 = mu qR
  left_zero : leftWall 0 = mu qL
  right_one : rightWall 1 = junction
  left_one : leftWall 1 = junction
  wall_inter : rightWall '' Icc 0 1 ∩ leftWall '' Icc 0 1 ⊆ {rightWall 0, junction}
  right_gate_old : qR ∈ oldRealBase d.driver d.γ d.t
  left_gate_old : qL ∈ oldRealBase d.driver d.γ d.t
  right_free : ∀ u ∈ Ioc (0 : ℝ) 1, rightWall u ≠ 0 →
    trMap d.driver 0 d.t (muInv (rightWall u)) ∉ d.γ '' Icc 0 d.t
  left_free : ∀ u ∈ Ioc (0 : ℝ) 1, leftWall u ≠ 0 →
    trMap d.driver 0 d.t (muInv (leftWall u)) ∉ d.γ '' Icc 0 d.t
  right_physical_outside : ∀ u ∈ Icc (0 : ℝ) 1, rightWall u ≠ 0 →
    trMap d.driver 0 d.t (muInv (rightWall u)) ∉ relDom d.C
  left_physical_outside : ∀ u ∈ Icc (0 : ℝ) 1, leftWall u ≠ 0 →
    trMap d.driver 0 d.t (muInv (leftWall u)) ∉ relDom d.C
  right_image : rightWall '' Icc 0 1 = selectedPrefixImage d d.αR d.s₁ cutR qR
  left_image : leftWall '' Icc 0 1 = selectedPrefixImage d d.αL d.t₁ cutL qL

/-- Every positive unvisited right-wall parameter is on the selected right arm. -/
theorem SelectedGateArms.cover_right {d : GateSetup} {cutR cutL : ℝ≥0∞}
    (a : SelectedGateArms d cutR cutL) (r : ℝ≥0) (hr0 : 0 < r)
    (hr : d.s₁ ≤ r) (hc : (r : ℝ≥0∞) < cutR) :
    mu (forwardExt d.driver d.t (-(d.αR r)⁻¹)) ∈ a.rightWall '' Icc 0 1 := by
  rw [a.right_image]
  exact Or.inl (Or.inr ⟨r, ⟨hr0, hr, hc⟩, rfl⟩)

/-- Every positive unvisited left-wall parameter is on the selected left arm. -/
theorem SelectedGateArms.cover_left {d : GateSetup} {cutR cutL : ℝ≥0∞}
    (a : SelectedGateArms d cutR cutL) (r : ℝ≥0) (hr0 : 0 < r)
    (hr : d.t₁ ≤ r) (hc : (r : ℝ≥0∞) < cutL) :
    mu (forwardExt d.driver d.t (-(d.αL r)⁻¹)) ∈ a.leftWall '' Icc 0 1 := by
  rw [a.left_image]
  exact Or.inl (Or.inr ⟨r, ⟨hr0, hr, hc⟩, rfl⟩)

/-- The compactification point of the current frontier is already on the
selected arms. No separate enclosure hypothesis at infinity is necessary. -/
theorem SelectedGateArms.zero_mem_of_frontier {d : GateSetup} {cutR cutL : ℝ≥0∞}
    (a : SelectedGateArms d cutR cutL)
    (h0 : (0 : ℂ) ∈ frontier (mu '' ownDomain d.driver d.C d.t)) :
    (0 : ℂ) ∈ a.rightWall '' Icc 0 1 := by
  by_cases hs : d.s₁ = 0
  · rw [a.right_image]
    exact Or.inr (by simp only [hs, ite_true, mem_singleton_iff])
  · have hC0 : (0 : ℂ) ∉ closure d.C :=
      fun hc => hs (d.exit_eq_zero_of_zero_mem_closure hc)
    have hW : Continuous d.driver := d.continuous_driver.comp continuous_real_toNNReal
    have hW0 : d.driver 0 = 0 := by
      simpa only [GateSetup.driver, Real.toNNReal_zero] using d.driver_zero
    have hb := isBounded_ownDomain_of_isBounded_relDom
      (isLoewnerTrace_of_isGeneratingTrace d.generating) hW hW0 d.t.2
      (isBounded_relDom_of_zero_notMem_closure hC0)
    exact False.elim ((zero_notMem_closure_mu_ownDomain_of_isBounded hb) h0.1)

/-- **Remaining joint planar input:** choose the two actual compactified arms,
with their gate order and common contacts, for the already proved global cuts.
The case of an exit at the original target is included explicitly by `GateSetup`. -/
def GB11SelectedGateArmsStatement : Prop :=
  ∀ (d : GateSetup) (cutR cutL : ℝ≥0∞), IsWallVisitCut d.γ d.αR d.t cutR →
    IsWallVisitCut d.γ d.αL d.t cutL → Nonempty (SelectedGateArms d cutR cutL)

/-- The selected prefixes cover every non-real point of the current frontier.
The physical pocket frontier and the global cuts suffice; no enclosure premise
at the real line is used here. -/
theorem SelectedGateArms.frontier_inter_H_subset {d : GateSetup} {cutR cutL : ℝ≥0∞}
    (a : SelectedGateArms d cutR cutL) (hR : IsWallVisitCut d.γ d.αR d.t cutR)
    (hL : IsWallVisitCut d.γ d.αL d.t cutL) {w : ℂ}
    (hw : w ∈ frontier (ownDomain d.driver d.C d.t)) (hwH : w ∈ H) :
    mu w ∈ a.rightWall '' Icc 0 1 ∪ a.leftWall '' Icc 0 1 := by
  have hW : Continuous d.driver := d.continuous_driver.comp continuous_real_toNNReal
  have hW0 : d.driver 0 = 0 := by
    simpa only [GateSetup.driver, Real.toNNReal_zero] using d.driver_zero
  have hη := isLoewnerTrace_of_isGeneratingTrace d.generating
  have hCo : IsOpen d.C := isOpen_of_mem_betweenComponents
    (isClosed_range_of_isCompleteSimpleFlow d.barrier.1)
    (isClosed_range_of_isCompleteSimpleFlow d.barrier.2.1) d.component
  have hCH : d.C ⊆ H := subset_H_of_mem_betweenComponents d.component
  have hz := frontier_ownDomain_inter_H hη hW hW0 hCo hCH d.t.2 hw hwH
  have hz0 : trMap d.driver 0 d.t w ≠ 0 := by
    intro he
    have hpos : (0 : ℝ) < (trMap d.driver 0 d.t w).im := hz.2.1
    rw [he, Complex.zero_im] at hpos
    exact lt_irrefl _ hpos
  have hp := negInv_mem_frontier_of_mem_frontier_relDom hCo hCH hz.1 hz0
  have htrace : trMap d.driver 0 d.t w ∉ d.γ '' Icc 0 d.t :=
    fun he => (trace_image_disjoint_domain d.generating d.t).le_bot ⟨he, hz.2⟩
  have hext : forwardExt d.driver d.t (trMap d.driver 0 d.t w) = w := by
    have heq : EqOn (forwardExt d.driver d.t) (fwdMap d.driver d.t)
        (H \ fwdHull d.driver d.t) :=
      extendFrom_extends (QuantumZipper.FwdHolo.differentiableOn_fwdMap hW d.t.2).continuousOn
    exact (heq hz.2).trans (Sec6.fwdMap_trMap_zero hW hW0 d.t.2 hwH)
  have key : ∀ (α : ℝ≥0 → ℂ) (cut : ℝ≥0∞), α 0 = 0 → IsWallVisitCut d.γ α d.t cut →
      ∀ r : ℝ≥0, α r = -(trMap d.driver 0 d.t w)⁻¹ → 0 < r ∧ (r : ℝ≥0∞) < cut ∧
        -(α r)⁻¹ = trMap d.driver 0 d.t w := by
    intro α cut hα0 hcut r hr
    have he : -(α r)⁻¹ = trMap d.driver 0 d.t w := by rw [hr, negInv_negInv']
    have hr0 : 0 < r := pos_iff_ne_zero.2 (fun hrzero => hz0 (by
      rw [← he, hrzero, hα0, inv_zero, neg_zero]))
    refine ⟨hr0, lt_of_not_ge (fun hle => ?_), he⟩
    have hv := (mem_wallHitParameters_iff (Sec5.continuous_of_isGeneratingTrace_top d.generating)).1
      ((hcut.2 r).2 hle)
    have hm := negInv_mem_image_of_firstVisit_le
      (Sec5.continuous_of_isGeneratingTrace_top d.generating)
      (lt_of_le_of_lt hv ENNReal.coe_lt_top) hv
    exact htrace (he ▸ hm)
  rcases d.shape.frontier_subset hp with ⟨r, hr, he⟩ | ⟨r, hr, he⟩
  · obtain ⟨hr0, hlt, he'⟩ := key d.αR cutR d.barrier.1.2.2.1 hR r he
    have hc := a.cover_right r hr0 hr.1 hlt
    rw [he', hext] at hc
    exact Or.inl hc
  · obtain ⟨hr0, hlt, he'⟩ := key d.αL cutL d.barrier.2.1.2.2.1 hL r he
    have hc := a.cover_left r hr0 hr.1 hlt
    rw [he', hext] at hc
    exact Or.inr hc

end InteractingSLE.Theorem14.GB11Chart
