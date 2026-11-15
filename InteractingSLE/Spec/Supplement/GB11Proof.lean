/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW4FillDetProof
import InteractingSLE.Spec.Sec5.Lemma57Visit

/-!
# Lemma GB11 from the pocket shape: the entry, traversal and density clauses

Packet PROVE-T14-GW4T2. Lemma GB11 (supplement pp. 556–557, `source/spec/p529-576.md` L651–L679) for an extreme pocket
`C` with flow-oriented endpoints `x_C`, `y_C`, `τ = T(y_C)`, `σ = T(x_C)`: "`η([τ, σ]) ⊂ C̄`, `η([0, τ]) ∩ C̄ = {y_C}`
(GB11.1). Every nontrivial subinterval of `(τ, σ)` contains an open-`C` visit. In a fixed Jordan chart […] this actual
segment has a continuous relative Loewner parametrization with strictly increasing capacity."

GB11's barrier input takes the `C_j` to be "the Jordan interiors bounded by their two arcs between successive common
contacts". That pocket structure is not part of `GB11.IsGB11Barrier`; it is stated here as a property of the two walks
(`WalkPocketShape`): every between-component `C` has parameters `s₁ < s₂ ≤ ∞`, `t₁, t₂` with `α_R(s₁) = α_L(t₁) ∈ C̄`
(the exit, the boundary value of every component chart at `0`), `α_R(s₂) = α_L(t₂) ∈ C̄` (the entry) when `C` is
bounded, `s₂ = ∞` when it is not, and `∂C ⊆ α_R([s₁, s₂]) ∪ α_L([t₁, t₂])`; distinct pockets have non-overlapping
parameter intervals.

With the shape, GB10's pathwise conclusion and the barrier input, the clauses of GB11 other than the relative Loewner
parametrization are **proved** here (deterministic):

* `not_forall_walls`: the trace spends no nontrivial time interval on the two walls (GB10 and Baire,
  `GB10.NoSimpleArcInterval.not_image_subset_union_range`);
* `notMem_closure_of_lt_entry`: before its entry time the counterflow avoids `C̄` (the boundary arcs are first visited
  after the entry, by reverse first visits, and the initial range is connected; GB11's "`η([0, τ]) ∩ C̄ = {y_C}`");
* `notMem_relDom_of_exit_lt`: after its exit time the counterflow never re-enters `C` (the pocket is filled,
  `fill_of_frontier_subset`, and a generating trace never visits the interior of an earlier hull);
* **`mem_closure_of_traversal`** (GB11.1): between `τ` and `σ` the counterflow stays in `C̄` — off `C̄` it would be in
  another pocket (excluded by the two previous facts and the pocket order: "the only available open pocket") or on the
  walls, which it cannot occupy on a time interval;
* **`exists_mem_of_traversal`**: every nontrivial subinterval of `(τ, σ)` contains an open-`C` visit.

What remains of GB11 is the relative Loewner parametrization (`GB11RelParamStatement`, named input: the continuous-trace
criterion for a curve confined to a Jordan pocket with dense interior visits, Aux. lemma 41 / Proposition 6.12), and
**`gb11ShapeStatement_of_relParam`** proves GB11 (`GB11ShapeStatement`: `GB11.GB11Statement` for walks with the pocket
shape) from it. The barrier input of Theorem GW4's chain carries the pocket shape (`GW4BarrierPocketRegStatement`), and
`gw4RelativeChainRegStatement_of_relParam` is the R51 relative chain from these inputs.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal
open QuantumZipper (H fwdHull)

universe u

namespace InteractingSLE

namespace Theorem14

namespace GW4Reg

open GW4Traverse GW4Ident

/-! ### The pocket shape -/

/-- **The two-arc shape of a pocket** `C` between the walks `α_R`, `α_L` (GB11's barrier input, p. 555): the exit
`α_R(s₁) = α_L(t₁)` lies on `C̄`; if `C` is bounded, the entry `α_R(s₂) = α_L(t₂)`, `s₂ < ∞`, lies on `C̄`; if not,
`s₂ = t₂ = ∞`; and the frontier of `C` lies on the two walks between these parameters. -/
structure IsPocketShape (αR αL : ℝ≥0 → ℂ) (C : Set ℂ) (s₁ t₁ : ℝ≥0) (s₂ t₂ : ℝ≥0∞) : Prop where
  contact : αR s₁ = αL t₁
  mem_closure_exit : αR s₁ ∈ closure C
  lt : (s₁ : ℝ≥0∞) < s₂
  top_iff : s₂ = ⊤ ↔ t₂ = ⊤
  unbounded : s₂ = ⊤ → ¬ Bornology.IsBounded C
  entry : s₂ ≠ ⊤ → αR s₂.toNNReal = αL t₂.toNNReal ∧ αR s₂.toNNReal ∈ closure C ∧ Bornology.IsBounded C
  frontier_subset : frontier C ⊆ αR '' {r | s₁ ≤ r ∧ (r : ℝ≥0∞) ≤ s₂} ∪ αL '' {r | t₁ ≤ r ∧ (r : ℝ≥0∞) ≤ t₂}

/-- **The pocket shape of the walks** (GB11's barrier input: "Let `C_j` be the Jordan interiors bounded by their two
arcs between successive common contacts"; "write its flow-oriented endpoints as `x_C, y_C`"): every between-component
has a two-arc shape; its exit is the boundary value at `0` of each of its component charts; distinct pockets have
non-overlapping parameter intervals along `α_R`. -/
def WalkPocketShape (αR αL : ℝ≥0 → ℂ) : Prop :=
  (∀ C ∈ betweenComponents (range αR) (range αL), ∃ (s₁ t₁ : ℝ≥0) (s₂ t₂ : ℝ≥0∞),
    IsPocketShape αR αL C s₁ t₁ s₂ t₂) ∧
  (∀ C ∈ betweenComponents (range αR) (range αL), ∀ (s₁ t₁ : ℝ≥0) (s₂ t₂ : ℝ≥0∞),
    IsPocketShape αR αL C s₁ t₁ s₂ t₂ → ∀ c : Chart, IsComponentChart (range αR) (range αL) C c →
      ∀ xC : ℂ, Tendsto c.2.1 (𝓝[H] 0) (𝓝 xC) → xC = αR s₁) ∧
  ∀ C ∈ betweenComponents (range αR) (range αL), ∀ C' ∈ betweenComponents (range αR) (range αL), C ≠ C' →
    ∀ (s₁ t₁ : ℝ≥0) (s₂ t₂ : ℝ≥0∞) (s₁' t₁' : ℝ≥0) (s₂' t₂' : ℝ≥0∞),
      IsPocketShape αR αL C s₁ t₁ s₂ t₂ → IsPocketShape αR αL C' s₁' t₁' s₂' t₂' →
        s₂' ≤ (s₁ : ℝ≥0∞) ∨ s₂ ≤ (s₁' : ℝ≥0∞)

/-- The frontier of a shaped pocket lies on the walks beyond its exit. -/
theorem IsPocketShape.frontier_subset_Ici {αR αL : ℝ≥0 → ℂ} {C : Set ℂ} {s₁ t₁ : ℝ≥0} {s₂ t₂ : ℝ≥0∞}
    (h : IsPocketShape αR αL C s₁ t₁ s₂ t₂) : frontier C ⊆ αR '' Ici s₁ ∪ αL '' Ici t₁ :=
  h.frontier_subset.trans (union_subset_union (image_mono fun _ hr => hr.1) (image_mono fun _ hr => hr.1))

/-- The pocket shape gives the exit shape. -/
theorem WalkPocketShape.walkExitShape {αR αL : ℝ≥0 → ℂ} (h : WalkPocketShape αR αL) : WalkExitShape αR αL := by
  intro C hC c hc xC hxC
  obtain ⟨s₁, t₁, s₂, t₂, hs⟩ := h.1 C hC
  have hx := h.2.1 C hC s₁ t₁ s₂ t₂ hs c hc xC hxC
  exact ⟨s₁, t₁, hx.symm, (hs.contact.symm.trans hx.symm), hs.frontier_subset_Ici⟩

/-! ### First visits along a wall -/

theorem firstVisit_zero_eq_top (γ : ℝ≥0 → ℂ) : GB11.firstVisit γ 0 = ⊤ := by
  by_contra h
  exact ne_zero_of_firstVisit_lt_top (lt_top_iff_ne_top.2 h) rfl

/-- Along a complete simple flow visited in strict reverse order, first visits are antitone. -/
theorem firstVisit_anti {γ α : ℝ≥0 → ℂ} (hα0 : α 0 = 0)
    (hrev : ∀ a a' : ℝ≥0, 0 < a → a < a' → GB11.firstVisit γ (α a') < GB11.firstVisit γ (α a)) {r r' : ℝ≥0}
    (hrr : r ≤ r') : GB11.firstVisit γ (α r') ≤ GB11.firstVisit γ (α r) := by
  rcases eq_or_lt_of_le hrr with rfl | hlt
  · exact le_rfl
  rcases eq_or_ne r 0 with rfl | hr0
  · rw [hα0, firstVisit_zero_eq_top]; exact le_top
  · exact (hrev r r' (pos_iff_ne_zero.2 hr0) hlt).le

theorem negInv_injective : Function.Injective fun z : ℂ => -z⁻¹ := fun z w h => by
  have := congrArg (fun z : ℂ => -z⁻¹) h
  simpa only [negInv_negInv'] using this

/-- A continuous curve from `0` stays in a small ball near time `0`. -/
theorem exists_pos_forall_norm_lt {α : ℝ≥0 → ℂ} (hα : Continuous α) (hα0 : α 0 = 0) {e : ℝ} (he : 0 < e) :
    ∃ ε : ℝ≥0, 0 < ε ∧ ∀ r : ℝ≥0, r < ε → ‖α r‖ < e := by
  obtain ⟨δ, hδ, hball⟩ := Metric.continuousAt_iff.1 hα.continuousAt e he
  refine ⟨δ.toNNReal, Real.toNNReal_pos.2 hδ, fun r hr => ?_⟩
  have h1 : dist r 0 < δ := by
    rw [NNReal.dist_eq, NNReal.coe_zero, sub_zero, abs_of_nonneg r.coe_nonneg]
    exact (Real.lt_toNNReal_iff_coe_lt.1 hr)
  have h2 := hball h1
  rwa [hα0, dist_zero_right] at h2

/-- The tail `v ↦ −1/α(ε + v)` of a complete simple flow read in the counterflow chart is continuous and injective. -/
theorem continuous_injective_tail {α : ℝ≥0 → ℂ} (hf : GB11.IsCompleteSimpleFlow α) {ε : ℝ≥0} (hε : 0 < ε) :
    Continuous (fun v : ℝ≥0 => -(α (ε + v))⁻¹) ∧ Function.Injective (fun v : ℝ≥0 => -(α (ε + v))⁻¹) := by
  have hne : ∀ v : ℝ≥0, α (ε + v) ≠ 0 := fun v h => by
    have := hf.2.1 (h.trans hf.2.2.1.symm)
    exact (ne_of_gt (lt_of_lt_of_le hε le_self_add)) this
  refine ⟨((hf.1.comp (continuous_const.add continuous_id)).inv₀ hne).neg, fun v w hvw => ?_⟩
  have := hf.2.1 (inv_injective (neg_injective hvw))
  exact add_left_cancel this

/-- **The trace spends no nontrivial time interval on the two walls** (GB10 with Baire,
`GB10.NoSimpleArcInterval.not_image_subset_union_range`): read in the counterflow chart, the walls are two continuous
injective tails (away from the original target, which a compact piece of the trace avoids) and the point `0` (the
original source), which the trace occupies on no interval. -/
theorem not_forall_walls {γ : ℝ≥0 → ℂ} (hγc : Continuous γ) (hno : GB10.NoSimpleArcInterval γ ⊤)
    {αR αL : ℝ≥0 → ℂ} (hfR : GB11.IsCompleteSimpleFlow αR) (hfL : GB11.IsCompleteSimpleFlow αL) {a b : ℝ≥0}
    (hab : a < b) : ¬ ∀ u ∈ Icc a b, γ u = 0 ∨ -(γ u)⁻¹ ∈ range αR ∪ range αL := by
  intro hall
  obtain ⟨M₀, hM₀⟩ := (isCompact_Icc.image hγc).isBounded.exists_norm_le
  set M : ℝ := max M₀ 0 + 1 with hM
  have hMpos : 0 < M := by positivity
  obtain ⟨εR, hεR, hR⟩ := exists_pos_forall_norm_lt hfR.1 hfR.2.2.1 (inv_pos.2 hMpos)
  obtain ⟨εL, hεL, hL⟩ := exists_pos_forall_norm_lt hfL.1 hfL.2.2.1 (inv_pos.2 hMpos)
  obtain ⟨hβRc, hβRi⟩ := continuous_injective_tail hfR hεR
  obtain ⟨hβLc, hβLi⟩ := continuous_injective_tail hfL hεL
  have hFno : ∀ a' b' : ℝ≥0, a ≤ a' → a' < b' → b' ≤ b → ¬ γ '' Icc a' b' ⊆ {0} := by
    intro a' b' _ hab' _ hsub
    refine hno a' b' hab' ENNReal.coe_lt_top ((fun x : ℝ => (x : ℂ)) '' Icc 0 1)
      ⟨fun x : ℝ => (x : ℂ), Complex.continuous_ofReal.continuousOn,
        Complex.ofReal_injective.injOn, rfl⟩ (hsub.trans ?_)
    rintro z rfl
    exact ⟨0, ⟨le_rfl, zero_le_one⟩, Complex.ofReal_zero⟩
  refine GB10.NoSimpleArcInterval.not_image_subset_union_range hno hab ENNReal.coe_lt_top hγc.continuousOn
    hβRc hβRi hβLc hβLi isClosed_singleton hFno ?_
  rintro _ ⟨u, hu, rfl⟩
  by_cases h0 : γ u = 0
  · exact Or.inl (Or.inl h0)
  have hnorm : M⁻¹ < ‖-(γ u)⁻¹‖ := by
    rw [norm_neg, norm_inv]
    have h1 : ‖γ u‖ ≤ M₀ := hM₀ _ ⟨u, hu, rfl⟩
    have h2 : ‖γ u‖ < M := by rw [hM]; linarith [le_max_left M₀ 0]
    exact inv_strictAnti₀ (norm_pos_iff.2 h0) h2
  have key : ∀ (α : ℝ≥0 → ℂ) (ε : ℝ≥0), (∀ r : ℝ≥0, r < ε → ‖α r‖ < M⁻¹) → ∀ r : ℝ≥0, α r = -(γ u)⁻¹ →
      γ u ∈ range (fun v : ℝ≥0 => -(α (ε + v))⁻¹) := by
    intro α ε hsm r hr
    have hεr : ε ≤ r := by
      by_contra hlt
      push Not at hlt
      have := hsm r hlt
      rw [hr] at this
      exact lt_asymm this hnorm
    refine ⟨r - ε, ?_⟩
    simp only [add_tsub_cancel_of_le hεr, hr, negInv_negInv']
  rcases (hall u hu).resolve_left h0 with ⟨r, hr⟩ | ⟨r, hr⟩
  · exact Or.inl (Or.inr (key αR εR hR r hr))
  · exact Or.inr (key αL εL hL r hr)

/-! ### Before the entry and after the exit -/

section Visits

variable {γ : ℝ≥0 → ℂ} {αR αL : ℝ≥0 → ℂ}

theorem le_toNNReal_of_coe_le {r : ℝ≥0} {s : ℝ≥0∞} (hs : s ≠ ⊤) (h : (r : ℝ≥0∞) ≤ s) : r ≤ s.toNNReal := by
  simpa using ENNReal.toNNReal_mono hs h

/-- **Before its entry time the counterflow avoids a bounded shaped pocket and its closure** (GB11.1: "`η([0, τ]) ∩
C̄ = {y_C}`"). The boundary arcs are first visited at or after the entry (reverse first visits); a visit to `C` itself
before the entry would, by connectedness of the initial range (which contains the original source, `0` in the chart),
cross the frontier earlier. -/
theorem notMem_closure_of_lt_entry (hγc : Continuous γ) (hγ0 : γ 0 = 0) (hfR : GB11.IsCompleteSimpleFlow αR)
    (hfL : GB11.IsCompleteSimpleFlow αL)
    (hrevR : ∀ a a' : ℝ≥0, 0 < a → a < a' → GB11.firstVisit γ (αR a') < GB11.firstVisit γ (αR a))
    (hrevL : ∀ a a' : ℝ≥0, 0 < a → a < a' → GB11.firstVisit γ (αL a') < GB11.firstVisit γ (αL a))
    {C : Set ℂ} (hCo : IsOpen C) (hCH : C ⊆ H) {s₁ t₁ : ℝ≥0} {s₂ t₂ : ℝ≥0∞}
    (hs : IsPocketShape αR αL C s₁ t₁ s₂ t₂) (hs₂ : s₂ ≠ ⊤) {t : ℝ≥0}
    (ht : (t : ℝ≥0∞) < GB11.firstVisit γ (αR s₂.toNNReal)) (hγt : γ t ≠ 0) : -(γ t)⁻¹ ∉ closure C := by
  obtain ⟨hct, -, hbdd⟩ := hs.entry hs₂
  have ht₂ : t₂ ≠ ⊤ := fun h => hs₂ (hs.top_iff.2 h)
  have hlate : ∀ p ∈ frontier C, GB11.firstVisit γ (αR s₂.toNNReal) ≤ GB11.firstVisit γ p := by
    intro p hp
    rcases hs.frontier_subset hp with ⟨r, ⟨-, hr⟩, rfl⟩ | ⟨r, ⟨-, hr⟩, rfl⟩
    · exact firstVisit_anti hfR.2.2.1 hrevR (le_toNNReal_of_coe_le hs₂ hr)
    · rw [hct]
      exact firstVisit_anti hfL.2.2.1 hrevL (le_toNNReal_of_coe_le ht₂ hr)
  have hfr : ∀ u : ℝ≥0, u ≤ t → γ u ≠ 0 → -(γ u)⁻¹ ∉ frontier C := by
    intro u hu hγu hp
    have h1 := (hlate _ hp).trans (GB11.firstVisit_le hγu)
    have h2 : (u : ℝ≥0∞) < GB11.firstVisit γ (αR s₂.toNNReal) :=
      lt_of_le_of_lt (by exact_mod_cast hu) ht
    exact lt_irrefl _ (lt_of_le_of_lt h1 h2)
  intro hmem
  rw [closure_eq_self_union_frontier] at hmem
  rcases hmem with hC | hF
  · have hDo : IsOpen (relDom C) := isOpen_relDom hCo hCH
    have hSpc : IsPreconnected (γ '' Icc 0 t) := isPreconnected_Icc.image _ hγc.continuousOn
    obtain ⟨M, hM⟩ := hbdd.exists_norm_le
    set K : ℝ := max M 1 with hK
    have hKpos : 0 < K := lt_of_lt_of_le one_pos (le_max_right M 1)
    have hDfar : closure (relDom C) ⊆ {w : ℂ | K⁻¹ ≤ ‖w‖} := by
      refine closure_minimal (fun w hw => ?_) (isClosed_le continuous_const continuous_norm)
      have hw0 : w ≠ 0 := ne_zero_of_mem_H' (relDom_subset_H hCH hw)
      have h1 : ‖w‖⁻¹ ≤ K := by
        have := hM _ hw
        rw [norm_neg, norm_inv] at this
        exact this.trans (le_max_left M 1)
      exact (inv_le_comm₀ (norm_pos_iff.2 hw0) hKpos).1 h1
    have hex : ∃ u ∈ Icc 0 t, γ u ∈ closure (relDom C) ∧ γ u ∉ relDom C := by
      by_contra hcon
      push Not at hcon
      have hsub : γ '' Icc 0 t ⊆ relDom C :=
        hSpc.subset_of_closure_inter_subset hDo ⟨γ t, ⟨t, ⟨zero_le, le_rfl⟩, rfl⟩, hC⟩
          (by rintro _ ⟨hcl, ⟨u, hu, rfl⟩⟩; exact hcon u hu hcl)
      have h0D : γ 0 ∈ relDom C := hsub ⟨0, ⟨le_rfl, zero_le⟩, rfl⟩
      rw [hγ0] at h0D
      exact ne_zero_of_mem_H' (relDom_subset_H hCH h0D) rfl
    obtain ⟨u, hu, hcl, hnD⟩ := hex
    have hγu : γ u ≠ 0 := fun h => by
      have h1 : K⁻¹ ≤ ‖γ u‖ := hDfar hcl
      rw [h, norm_zero] at h1
      exact absurd h1 (not_le.2 (inv_pos.2 hKpos))
    have hmc : -(γ u)⁻¹ ∈ closure C := by
      have h1 := mem_closure_image (continuousAt_negInv hγu) hcl
      exact closure_mono (image_subset_iff.2 fun w hw => hw) h1
    exact hfr u hu.2 hγu ⟨hmc, by rw [hCo.interior_eq]; exact hnD⟩
  · exact hfr t le_rfl hγt hF

/-- **After its exit time the counterflow never re-enters a shaped pocket**: the pocket is filled at the exit
(`fill_of_frontier_subset`) and a generating trace never visits the interior of an earlier hull
(`Sec5.notMem_interior_fwdHull_of_lt`). -/
theorem notMem_relDom_of_exit_lt {W' : ℝ≥0 → ℝ} (hW' : Continuous W') (hW'0 : W' 0 = 0)
    (hγ : IsGeneratingTrace W' ⊤ γ) (hfR : GB11.IsCompleteSimpleFlow αR) (hfL : GB11.IsCompleteSimpleFlow αL)
    (hrevR : ∀ a a' : ℝ≥0, 0 < a → a < a' → GB11.firstVisit γ (αR a') < GB11.firstVisit γ (αR a))
    (hrevL : ∀ a a' : ℝ≥0, 0 < a → a < a' → GB11.firstVisit γ (αL a') < GB11.firstVisit γ (αL a))
    {C : Set ℂ} (hCo : IsOpen C) (hCH : C ⊆ H) {s₁ t₁ : ℝ≥0} {s₂ t₂ : ℝ≥0∞}
    (hs : IsPocketShape αR αL C s₁ t₁ s₂ t₂) {t : ℝ≥0} (ht : GB11.firstVisit γ (αR s₁) < t) :
    γ t ∉ relDom C := by
  have hσ : GB11.firstVisit γ (αR s₁) < ⊤ := ht.trans ENNReal.coe_lt_top
  have hfill := fill_of_frontier_subset hγ hfR hfL hrevR hrevL hCo hCH rfl hs.contact.symm
    hs.frontier_subset_Ici hσ
  intro hin
  have hint : relDom C ⊆ interior (fwdHull (fun r : ℝ => W' r.toNNReal)
      (GB11.firstVisit γ (αR s₁)).toNNReal) :=
    interior_maximal hfill (isOpen_relDom hCo hCH)
  have hlt : (GB11.firstVisit γ (αR s₁)).toNNReal < t := by
    have := ENNReal.toNNReal_strict_mono ENNReal.coe_ne_top ht
    simpa using this
  exact Sec5.notMem_interior_fwdHull_of_lt hW' hW'0 hγ hlt (hint hin)

end Visits

/-! ### The traversal of a pocket -/

/-- The entry time of a shaped pocket: the first visit of its entry `α_R(s₂)` (`0` for the unbounded pocket, which
contains the original source in its closure at infinity). -/
def entryTime (γ αR : ℝ≥0 → ℂ) (s₂ : ℝ≥0∞) : ℝ≥0 :=
  if s₂ = ⊤ then 0 else (GB11.firstVisit γ (αR s₂.toNNReal)).toNNReal

section Traversal

variable {W' : ℝ≥0 → ℝ} {γ : ℝ≥0 → ℂ} {αR αL : ℝ≥0 → ℂ} {C : Set ℂ} {s₁ t₁ : ℝ≥0} {s₂ t₂ : ℝ≥0∞}

theorem continuous_of_isGeneratingTrace_top (hγ : IsGeneratingTrace W' ⊤ γ) : Continuous γ := by
  have h := hγ.2.1
  have hU : {t : ℝ≥0 | (t : ℝ≥0∞) ≤ ⊤} = univ := eq_univ_of_forall fun x => show (x : ℝ≥0∞) ≤ ⊤ from le_top
  rw [hU] at h
  exact continuousOn_univ.1 h

/-- The entry of a bounded shaped pocket is visited, at the entry time. -/
theorem entryTime_spec (hγc : Continuous γ) (hB : GB11.IsGB11Barrier αR αL γ)
    (hs : IsPocketShape αR αL C s₁ t₁ s₂ t₂) (hs₂ : s₂ ≠ ⊤) :
    (entryTime γ αR s₂ : ℝ≥0∞) = GB11.firstVisit γ (αR s₂.toNNReal) ∧ γ (entryTime γ αR s₂) ≠ 0 ∧
      -(γ (entryTime γ αR s₂))⁻¹ = αR s₂.toNNReal := by
  have hpos : 0 < s₂.toNNReal := by
    have h1 : (s₁ : ℝ≥0∞) < s₂ := hs.lt
    have h2 : (0 : ℝ≥0∞) < s₂ := lt_of_le_of_lt zero_le h1
    exact ENNReal.toNNReal_pos (ne_of_gt h2) hs₂
  obtain ⟨t, ht, hγt, hty⟩ := exists_eq_firstVisit hγc (hB.firstVisit_lt_top_R hpos)
  have he : entryTime γ αR s₂ = t := by
    rw [entryTime, ite_eq_right_of_eq_false _ _ (eq_false hs₂), ← ht, ENNReal.toNNReal_coe]
  rw [he]
  exact ⟨ht, hγt, hty⟩

/-- **(GB11.1), second half: before its entry time the counterflow avoids `C̄`.** -/
theorem notMem_closure_before_entry (hγ : IsGeneratingTrace W' ⊤ γ) (hB : GB11.IsGB11Barrier αR αL γ)
    (hC : C ∈ betweenComponents (range αR) (range αL)) (hs : IsPocketShape αR αL C s₁ t₁ s₂ t₂) :
    ∀ t : ℝ≥0, t < entryTime γ αR s₂ → γ t ≠ 0 → -(γ t)⁻¹ ∉ closure C := by
  intro t ht hγt
  have hγc := continuous_of_isGeneratingTrace_top hγ
  by_cases hs₂ : s₂ = ⊤
  · rw [entryTime, ite_eq_left_of_eq_true _ _ (eq_true hs₂)] at ht
    exact absurd ht (not_lt.2 zero_le)
  have he := (entryTime_spec hγc hB hs hs₂).1
  obtain ⟨hfR, hfL, -, -, -, hrevR, hrevL⟩ := hB
  have hCo := isOpen_of_mem_betweenComponents (isClosed_range_of_isCompleteSimpleFlow hfR)
    (isClosed_range_of_isCompleteSimpleFlow hfL) hC
  refine notMem_closure_of_lt_entry hγc hγ.1 hfR hfL hrevR hrevL hCo (subset_H_of_mem_betweenComponents hC) hs
    hs₂ ?_ hγt
  rw [← he]
  exact_mod_cast ht

/-- **(GB11.1), first half: between its entry and exit times the counterflow stays in `C̄`** ("the only available
open pocket"). Off `C̄`, near such a time, the counterflow would be (by (GB11.B)) in another pocket — one before `C`,
whose entry comes after the exit of `C` (`notMem_closure_of_lt_entry`), or one beyond `C`, already filled before the
entry of `C` (`notMem_relDom_of_exit_lt`) — or on the walls, on a whole time interval (`not_forall_walls`). -/
theorem mem_closure_of_traversal (hW' : Continuous W') (hW'0 : W' 0 = 0) (hγ : IsGeneratingTrace W' ⊤ γ)
    (hno : GB10.NoSimpleArcInterval γ ⊤) (hB : GB11.IsGB11Barrier αR αL γ) (hP : WalkPocketShape αR αL)
    (hC : C ∈ betweenComponents (range αR) (range αL)) (hs : IsPocketShape αR αL C s₁ t₁ s₂ t₂) :
    ∀ t : ℝ≥0, entryTime γ αR s₂ ≤ t → (t : ℝ≥0∞) < GB11.firstVisit γ (αR s₁) → γ t ≠ 0 →
      -(γ t)⁻¹ ∈ closure C := by
  intro t₀ hτ hσ hγ0
  by_contra hnot
  have hγc := continuous_of_isGeneratingTrace_top hγ
  have hBsave := hB
  obtain ⟨hfR, hfL, -, -, hBB, hrevR, hrevL⟩ := hB
  have hRc := isClosed_range_of_isCompleteSimpleFlow hfR
  have hLc := isClosed_range_of_isCompleteSimpleFlow hfL
  set τ := entryTime γ αR s₂ with hτdef
  -- the entry time itself is in `C̄`
  have hτlt : τ < t₀ := by
    refine lt_of_le_of_ne hτ fun heq => ?_
    by_cases hs₂ : s₂ = ⊤
    · have h0 : τ = 0 := by rw [hτdef, entryTime, ite_eq_left_of_eq_true _ _ (eq_true hs₂)]
      rw [← heq, h0, hγ.1] at hγ0
      exact hγ0 rfl
    · obtain ⟨-, -, hy⟩ := entryTime_spec hγc hBsave hs hs₂
      rw [← hτdef, heq] at hy
      exact hnot (hy ▸ (hs.entry hs₂).2.1)
  -- a neighbourhood of `t₀` off `C̄`
  have h1 : ∀ᶠ u in 𝓝 t₀, γ u ≠ 0 := hγc.continuousAt.eventually_ne hγ0
  have h2 : ∀ᶠ u in 𝓝 t₀, -(γ u)⁻¹ ∉ closure C :=
    ((continuousAt_negInv hγ0).comp hγc.continuousAt).preimage_mem_nhds
      (isClosed_closure.isOpen_compl.mem_nhds hnot)
  have h3 : ∀ᶠ u in 𝓝 t₀, τ < u := lt_mem_nhds hτlt
  have h4 : ∀ᶠ u : ℝ≥0 in 𝓝 t₀, (u : ℝ≥0∞) < GB11.firstVisit γ (αR s₁) :=
    (ENNReal.continuous_coe.tendsto t₀).eventually (gt_mem_nhds hσ)
  obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff.1 (h1.and (h2.and (h3.and h4)))
  set δ : ℝ≥0 := (ε / 2).toNNReal with hδ
  have hδpos : 0 < δ := Real.toNNReal_pos.2 (half_pos hε)
  have hin : ∀ u ∈ Icc t₀ (t₀ + δ), γ u ≠ 0 ∧ -(γ u)⁻¹ ∉ closure C ∧ τ < u ∧
      (u : ℝ≥0∞) < GB11.firstVisit γ (αR s₁) := by
    intro u hu
    refine hball ?_
    rw [NNReal.dist_eq]
    have hu1 : (t₀ : ℝ) ≤ u := by exact_mod_cast hu.1
    have hu2 : (u : ℝ) ≤ t₀ + δ := by exact_mod_cast hu.2
    have hδr : (δ : ℝ) = ε / 2 := Real.coe_toNNReal _ (half_pos hε).le
    rw [abs_of_nonneg (by linarith)]
    linarith
  refine not_forall_walls hγc hno hfR hfL (lt_add_of_pos_right t₀ hδpos) fun u hu => Or.inr ?_
  obtain ⟨hγu, hnotC, hτu, hσu⟩ := hin u hu
  rcases hBB u hγu with hRL | ⟨C', hC', hmem⟩
  · exact hRL
  exfalso
  have hne : C ≠ C' := fun h => hnotC (subset_closure (h ▸ hmem))
  have hC'o := isOpen_of_mem_betweenComponents hRc hLc hC'
  have hC'H := subset_H_of_mem_betweenComponents hC'
  obtain ⟨s₁', t₁', s₂', t₂', hs'⟩ := hP.1 C' hC'
  rcases hP.2.2 C hC C' hC' hne s₁ t₁ s₂ t₂ s₁' t₁' s₂' t₂' hs hs' with hbef | haft
  · -- `C'` lies before `C`: its entry comes after the exit of `C`
    have hs₂' : s₂' ≠ ⊤ := ne_top_of_le_ne_top ENNReal.coe_ne_top hbef
    have hle : s₂'.toNNReal ≤ s₁ := by simpa using ENNReal.toNNReal_mono ENNReal.coe_ne_top hbef
    have hlt : (u : ℝ≥0∞) < GB11.firstVisit γ (αR s₂'.toNNReal) :=
      lt_of_lt_of_le hσu (firstVisit_anti hfR.2.2.1 hrevR hle)
    exact notMem_closure_of_lt_entry hγc hγ.1 hfR hfL hrevR hrevL hC'o hC'H hs' hs₂' hlt hγu
      (subset_closure hmem)
  · -- `C'` lies beyond `C`: it was filled before the entry of `C`
    have hs₂ : s₂ ≠ ⊤ := ne_top_of_le_ne_top ENNReal.coe_ne_top haft
    have hle : s₂.toNNReal ≤ s₁' := by simpa using ENNReal.toNNReal_mono ENNReal.coe_ne_top haft
    have he := (entryTime_spec hγc hBsave hs hs₂).1
    have hlt : GB11.firstVisit γ (αR s₁') < u := by
      refine lt_of_le_of_lt (firstVisit_anti hfR.2.2.1 hrevR hle) ?_
      rw [← he, ← hτdef]
      exact_mod_cast hτu
    exact notMem_relDom_of_exit_lt hW' hW'0 hγ hfR hfL hrevR hrevL hC'o hC'H hs' hlt hmem

/-- **Every nontrivial subinterval of `(τ, σ)` contains an open-`C` visit** (GB11). Otherwise, on a smaller interval,
the counterflow would stay in `C̄ \ C = ∂C`, on the walls (`not_forall_walls`). -/
theorem exists_mem_of_traversal (hW' : Continuous W') (hW'0 : W' 0 = 0) (hγ : IsGeneratingTrace W' ⊤ γ)
    (hno : GB10.NoSimpleArcInterval γ ⊤) (hB : GB11.IsGB11Barrier αR αL γ) (hP : WalkPocketShape αR αL)
    (hC : C ∈ betweenComponents (range αR) (range αL)) (hs : IsPocketShape αR αL C s₁ t₁ s₂ t₂) :
    ∀ a b : ℝ≥0, entryTime γ αR s₂ ≤ a → a < b → (b : ℝ≥0∞) < GB11.firstVisit γ (αR s₁) →
      ∃ t ∈ Ioo a b, γ t ≠ 0 ∧ -(γ t)⁻¹ ∈ C := by
  intro a b ha hab hb
  by_contra hcon
  push Not at hcon
  have hγc := continuous_of_isGeneratingTrace_top hγ
  have hTr := mem_closure_of_traversal hW' hW'0 hγ hno hB hP hC hs
  obtain ⟨hfR, hfL, -⟩ := hB
  have hCo := isOpen_of_mem_betweenComponents (isClosed_range_of_isCompleteSimpleFlow hfR)
    (isClosed_range_of_isCompleteSimpleFlow hfL) hC
  obtain ⟨c, hac, hcb⟩ := exists_between hab
  obtain ⟨d, hcd, hdb⟩ := exists_between hcb
  refine not_forall_walls hγc hno hfR hfL hcd fun u hu => ?_
  by_cases hγu : γ u = 0
  · exact Or.inl hγu
  refine Or.inr ?_
  have huσ : (u : ℝ≥0∞) < GB11.firstVisit γ (αR s₁) :=
    lt_of_lt_of_le (by exact_mod_cast hu.2.trans_lt hdb) hb.le
  have hcl := hTr u (ha.trans (hac.le.trans hu.1)) huσ hγu
  have hnC := hcon u ⟨hac.trans_le hu.1, hu.2.trans_lt hdb⟩ hγu
  rcases hs.frontier_subset ⟨hcl, by rw [hCo.interior_eq]; exact hnC⟩ with ⟨r, -, hr⟩ | ⟨r, -, hr⟩
  · exact Or.inl ⟨r, hr⟩
  · exact Or.inr ⟨r, hr⟩

end Traversal

/-! ### Lemma GB11 from its relative parametrization -/

/-- **Lemma GB11 for walks with the pocket shape** (`GB11.GB11Statement` with the added hypothesis
`WalkPocketShape αR αL`, which GB11's source barrier input contains). -/
def GB11ShapeStatement : Prop :=
  ∀ (W' : ℝ≥0 → ℝ) (γ : ℝ≥0 → ℂ), Continuous W' → W' 0 = 0 → IsGeneratingTrace W' ⊤ γ →
    GB10.NoSimpleArcInterval γ ⊤ →
    ∀ αR αL : ℝ≥0 → ℂ, GB11.IsGB11Barrier αR αL γ → WalkPocketShape αR αL →
    ∀ C ∈ betweenComponents (range αR) (range αL), ∀ c : Chart, IsComponentChart (range αR) (range αL) C c →
    ∀ xC : ℂ, Tendsto c.2.1 (𝓝[H] 0) (𝓝 xC) →
      ∃ (S : ℝ≥0∞) (Wrel : ℝ≥0 → ℝ) (T : ℝ≥0 → ℝ≥0), GB11.IsGB11RelParam W' γ c C xC S Wrel T ∧
        (∀ t : ℝ≥0, t < T 0 → γ t ≠ 0 → -(γ t)⁻¹ ∉ closure C) ∧
        (∀ t : ℝ≥0, T 0 ≤ t → (t : ℝ≥0∞) < GB11.firstVisit γ xC → γ t ≠ 0 → -(γ t)⁻¹ ∈ closure C) ∧
        ∀ a b : ℝ≥0, T 0 ≤ a → a < b → (b : ℝ≥0∞) < GB11.firstVisit γ xC →
          ∃ t ∈ Ioo a b, γ t ≠ 0 ∧ -(γ t)⁻¹ ∈ C

/-- **Named input: the relative Loewner parametrization of a pocket traversal** (Lemma GB11's last two sentences, "In
a fixed Jordan chart `ψ_C : (C; y_C, x_C) → (ℍ; 0, ∞)`, this actual segment has a continuous relative Loewner
parametrization with strictly increasing capacity. Its relative active component is exactly the original active
component intersected with `C`"; source proof: the active component `D_s ∩ C = E_s` (GB11.2), the current Jordan face,
relative continuity by the continuous-trace criterion of Aux. lemma 41 / Proposition 6.12, strict growth by Baire and
GB10). Deterministic. For a shaped pocket `C` of walks with GB11's barrier input and the pocket shape, given the
clauses proved in this file — before the entry the counterflow avoids `C̄`, between the entry and the exit it stays in
`C̄`, every subinterval contains an open-`C` visit — there is a maximal continuous relative parametrization of the
traversal starting at the entry time. -/
def GB11RelParamStatement : Prop :=
  ∀ (W' : ℝ≥0 → ℝ) (γ : ℝ≥0 → ℂ), Continuous W' → W' 0 = 0 → IsGeneratingTrace W' ⊤ γ →
    GB10.NoSimpleArcInterval γ ⊤ →
    ∀ αR αL : ℝ≥0 → ℂ, GB11.IsGB11Barrier αR αL γ → WalkPocketShape αR αL →
    ∀ C ∈ betweenComponents (range αR) (range αL), ∀ (s₁ t₁ : ℝ≥0) (s₂ t₂ : ℝ≥0∞),
    IsPocketShape αR αL C s₁ t₁ s₂ t₂ →
    ∀ c : Chart, IsComponentChart (range αR) (range αL) C c → Tendsto c.2.1 (𝓝[H] 0) (𝓝 (αR s₁)) →
    (∀ t : ℝ≥0, t < entryTime γ αR s₂ → γ t ≠ 0 → -(γ t)⁻¹ ∉ closure C) →
    (∀ t : ℝ≥0, entryTime γ αR s₂ ≤ t → (t : ℝ≥0∞) < GB11.firstVisit γ (αR s₁) → γ t ≠ 0 →
      -(γ t)⁻¹ ∈ closure C) →
    (∀ a b : ℝ≥0, entryTime γ αR s₂ ≤ a → a < b → (b : ℝ≥0∞) < GB11.firstVisit γ (αR s₁) →
      ∃ t ∈ Ioo a b, γ t ≠ 0 ∧ -(γ t)⁻¹ ∈ C) →
    ∃ (S : ℝ≥0∞) (Wrel : ℝ≥0 → ℝ) (T : ℝ≥0 → ℝ≥0), GB11.IsGB11RelParam W' γ c C (αR s₁) S Wrel T ∧
      T 0 = entryTime γ αR s₂

/-- **Lemma GB11 (pocket-shape form) from the relative parametrization** (conditional helper): the exit is the shape's
`α_R(s₁)`; the entry clause, the traversal clause and the density of open-`C` visits are
`notMem_closure_before_entry`, `mem_closure_of_traversal` and `exists_mem_of_traversal`. -/
theorem gb11ShapeStatement_of_relParam (hR : GB11RelParamStatement) : GB11ShapeStatement := by
  intro W' γ hW' hW'0 hγ hno αR αL hB hP C hC c hc xC hxC
  obtain ⟨s₁, t₁, s₂, t₂, hs⟩ := hP.1 C hC
  have hx : xC = αR s₁ := hP.2.1 C hC s₁ t₁ s₂ t₂ hs c hc xC hxC
  subst hx
  have hE := notMem_closure_before_entry hγ hB hC hs
  have hTr := mem_closure_of_traversal hW' hW'0 hγ hno hB hP hC hs
  have hD := exists_mem_of_traversal hW' hW'0 hγ hno hB hP hC hs
  obtain ⟨S, Wrel, T, hpar, hT0⟩ := hR W' γ hW' hW'0 hγ hno αR αL hB hP C hC s₁ t₁ s₂ t₂ hs c hc hxC hE hTr hD
  exact ⟨S, Wrel, T, hpar, hT0 ▸ hE, hT0 ▸ hTr, hT0 ▸ hD⟩

/-! ### Theorem GW4's chain with the pocket shape -/

/-- **Named input: the barrier input of GB11 for the actual sewn walks with their pocket shape, R51 form**:
`GW4BarrierRegStatement` together with `WalkPocketShape` of the two walks of `ω₀` (GB11's source barrier input: the
between-components are the two-arc Jordan pockets between successive common contacts, with flow-oriented endpoints). -/
def GW4BarrierPocketRegStatement : Prop :=
  ∀ κ : ℝ, 0 < κ → κ < 4 → ∀ (b : ℝ → ℝ) (jumps : Finset ℝ), IsPiecewiseConstantBoundaryData b jumps →
    ∀ {Ω : Type u} [MeasurableSpace Ω] [StandardBorelSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
      (h : Ω → LQGMetric.DistOn upperHalfPlaneOpens), IsGFFWithBoundaryData P h b jumps →
    ∀ (W' : ℝ≥0 → Ω → ℝ) (ζ' : Ω → ℝ≥0∞), IsCenteredCounterflowDriver κ P h W' ζ' →
      (∀ᵐ ω ∂P, ζ' ω = ⊤) →
    ∀ E : ExplSpec → ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞,
      (∀ spec : ExplSpec, IsBoundaryContinuedProgram spec.2.2 →
        IsStagedHistory κ b jumps P h spec (E spec)) →
      (∀ spec : ExplSpec, IsBoundaryContinuedProgram spec.2.2 →
        StagedPiecesRegular κ b jumps P spec (E spec)) →
      let wR := boundaryWalkSpec b jumps (-(Real.pi / 2)) true
      let wL := boundaryWalkSpec b jumps (Real.pi / 2) false
      ∀ᵐ ω₀ ∂P,
        let R := ExplState.physSet κ b jumps wR (fun k => E wR k ω₀)
        let L := ExplState.physSet κ b jumps wL (fun k => E wL k ω₀)
        let ν := condExpKernel P
          (pastSigma κ b jumps wR (E wR) wR.2.2.length ⊔ pastSigma κ b jumps wL (E wL) wL.2.2.length) ω₀
        ∃ αR αL : ℝ≥0 → ℂ, range αR = R ∧ range αL = L ∧ WalkPocketShape αR αL ∧
          ∀ᵐ ω ∂ν, ∀ γ : ℝ≥0 → ℂ, IsGeneratingTrace (fun t => W' t ω) ⊤ γ → GB11.IsGB11Barrier αR αL γ

/-- The barrier input with the pocket shape gives the barrier input with the exit shape. -/
theorem gw4BarrierShapeRegStatement_of_pocket (hB : GW4BarrierPocketRegStatement.{u}) :
    GW4BarrierShapeRegStatement.{u} := by
  intro κ hκ hκ4 b jumps hb Ω _ _ P _ h hh W' ζ' hcf hζ' E hE hreg wR wL
  filter_upwards [hB κ hκ hκ4 b jumps hb P h hh W' ζ' hcf hζ' E hE hreg] with ω₀ hω
  obtain ⟨αR, αL, hR, hL, hP, hbar⟩ := hω
  exact ⟨αR, αL, hR, hL, hP.walkExitShape, hbar⟩

/-- **Theorem GW4's pathwise relative chain, R51 form, from the relative parametrization input**
(`gw4RelativeChainRegStatement_of_gb11` with Lemma GB11 replaced by `gb11ShapeStatement_of_relParam` and the barrier
input carrying the pocket shape). -/
theorem gw4RelativeChainRegStatement_of_relParam (h13 : Exist.Theorem13Statement.{u})
    (hR : GB11RelParamStatement) (hB : GW4BarrierPocketRegStatement.{u}) (hComp : GW4CompletionRegStatement.{u}) :
    GW4RelativeChainRegStatement.{u} := by
  intro κ hκ hκ4 b jumps hb Ω _ _ P _ h hh W' ζ' hcf hζ' E hE hreg wR wL
  have hamb := ae_ae_condExpKernel
    (m := pastSigma κ b jumps wR (E wR) wR.2.2.length ⊔ pastSigma κ b jumps wL (E wL) wL.2.2.length)
    (ae_trace_noSimpleArcInterval GB10.gb10Statement h13 hκ hκ4 hcf hζ')
  filter_upwards [hamb, hB κ hκ hκ4 b jumps hb P h hh W' ζ' hcf hζ' E hE hreg,
    hComp κ hκ hκ4 b jumps hb P h hh W' ζ' hcf hζ' E hE hreg] with ω₀ hambω hBω hCω
  intro R L ν C hCm c hC bC jumpsC hch htr hpc hbd hgff
  obtain ⟨αR, αL, hαR, hαL, hP, hbar⟩ := hBω
  filter_upwards [hambω, hbar, hCω C hCm c hC bC jumpsC hch htr hpc hbd hgff] with ω hambω' hbarω hcompω
  obtain ⟨hW'c, hW'0, γ, hγ, hno⟩ := hambω'
  have hCm' : C ∈ betweenComponents (range αR) (range αL) := by rw [hαR, hαL]; exact hCm
  have hch' : IsComponentChart (range αR) (range αL) C c := by rw [hαR, hαL]; exact hch
  obtain ⟨xC, hxC, -, -⟩ := hch.2.2.2.2.1 0
  have hxC' : Tendsto c.2.1 (𝓝[H] 0) (𝓝 xC) := by simpa only [Complex.ofReal_zero] using hxC
  obtain ⟨S, Wrel, T, hpar, hent, -, -⟩ := gb11ShapeStatement_of_relParam hR (fun t => W' t ω) γ hW'c hW'0 hγ
    hno αR αL (hbarω γ hγ) hP C hCm' c hch' xC hxC'
  obtain ⟨hS, htips⟩ := hcompω γ hγ xC hxC' S Wrel T hpar
  subst hS
  obtain ⟨hWc, hW0, hTm, hTc, hK⟩ := hpar.global
  have := neBot_nhdsWithin_H_zero
  refine ⟨Wrel, T, hWc, hW0, hTm, hTc, fun t ht p hp hp0 => ?_, hK, htips⟩
  have htip := IsGeneratingTrace.tendsto_fwdMapInv_tip hγ hW'c.continuousOn hW'0
    (ENNReal.coe_lt_top (r := t))
  have e : p = γ t := tendsto_nhds_unique hp htip
  subst e
  exact hent t ht hp0

/-- **Theorem GW4's relative hulls, R51 form, from the relative parametrization input** (conditional helper): the
relative parametrization of a pocket traversal, the barrier input with the pocket shape, the R51 component law
input, no return and Theorems 1.2–1.3 (GB10, the rest of GB11 and the filled pocket are proved). -/
theorem gw4RelativeHullRegStatement_of_relParam (h12 : Exist.Theorem12Statement.{u})
    (h13 : Exist.Theorem13Statement.{u}) (hR : GB11RelParamStatement) (hB : GW4BarrierPocketRegStatement.{u})
    (hL : GW4RelativeLawRegStatement.{u}) (hNR : CounterflowNoReturnStatement.{u}) :
    GW4RelativeHullRegStatement.{u} :=
  gw4RelativeHullRegStatement_of_chain_ident
    (gw4RelativeChainRegStatement_of_relParam h13 hR hB
      (gw4CompletionRegStatement_of_law h13 hL
        (gw4FillRegStatement_of_barrierShape (gw4BarrierShapeRegStatement_of_pocket hB)) hNR))
    (gw4RelativeIdentRegStatement_of_law h12 h13 hL)

end GW4Reg

end Theorem14

end InteractingSLE
