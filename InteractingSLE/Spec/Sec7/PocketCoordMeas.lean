/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.PocketCoordJordan

/-!
# Aux. lemma 130's change pocket as a random object, under increasing contact order

Packet PROVE-STRIPSYS8. Specification §7.4.1, Aux. lemma 130 (`source/spec/p385-432.md` L401–L489): "The event and
the selected component are measurable from their complete labeled incoming paths alone. […] Compact contact sets and
continuous inverse path parametrizations make this a measurable event and make its preceding-contact selection
measurable. For instance, the endpoints are the infimum and supremum of their closed contact-parameter sets,
obtainable from rational interval tests."

For random walls `R ω`, `L ω` (continuous for every `ω`, measurable coordinates) and a measurable event `Good` on
which they satisfy `IsChangeConfigInc` (increasing contact order, no global order), this file proves:

* `le_gapLo_iff`, `gapHi_le_iff`, `contactMap_le_iff`, `mem_closedBall_of_isDiscCrosscut`: the gap ends and
  their parameters along `α` through interval tests;
* `measurableSet_inter_exists_le`: a minimum test through countably many points is measurable;
* **`measurable_gapLo`, `measurable_gapHi`, `measurable_gapLoα`, `measurable_gapHiα`**: the parameters of the two
  corners of the change pocket along both walls (in the disc parametrization) are measurable;
* **`measurableSet_mem_changeGap`**: membership of a fixed point in the change gap is measurable;
* **`exists_measurable_changePocketInc`**: the change pocket is a random open, connected, simply connected subset
  of `ℍ` observed through closed balls, through a measurably selected rational point.
-/

set_option autoImplicit false

noncomputable section

open Set Metric Filter Topology Complex Bornology Function MeasureTheory
open QuantumZipper (H Hbar)
open QuantumZipper.CA (cayley cayleyInv)
open scoped NNReal

namespace InteractingSLE.Sec7.PocketCoord

open WangWu

/-! ### Interval tests for the gap ends -/

section Iff

variable {α β : ℝ → ℂ}

/-- The lower gap end through an interval test. -/
theorem le_gapLo_iff (hα : IsDiscCrosscut α) (hβ : IsDiscCrosscut β) {c : ℝ} (hc : c ∈ Icc (0 : ℝ) 1) (t : ℝ) :
    t ≤ gapLo β α c ↔ ∃ s ∈ Icc (max t 0) c, β s ∈ α '' Icc 0 1 := by
  have hS : IsCompact (Sec7.pocketContactSet β α ∩ Icc 0 c) :=
    isCompact_Icc.inter_left (isClosed_pocketContactSet hβ hα)
  have h0 : (0 : ℝ) ∈ Sec7.pocketContactSet β α ∩ Icc 0 c := ⟨zero_mem_pocketContactSet hβ hα, le_rfl, hc.1⟩
  have hmem := hS.sSup_mem ⟨0, h0⟩
  constructor
  · intro ht
    exact ⟨_, ⟨max_le ht hmem.2.1, hmem.2.2⟩, hmem.1.2⟩
  · rintro ⟨s, hs, hsα⟩
    have hs0 : 0 ≤ s := (le_max_right _ _).trans hs.1
    have hsS : s ∈ Sec7.pocketContactSet β α ∩ Icc 0 c := ⟨⟨⟨hs0, hs.2.trans hc.2⟩, hsα⟩, hs0, hs.2⟩
    exact (le_max_left _ _).trans (hs.1.trans (le_csSup hS.bddAbove hsS))

/-- The upper gap end through an interval test. -/
theorem gapHi_le_iff (hα : IsDiscCrosscut α) (hβ : IsDiscCrosscut β) {c : ℝ} (hc : c ∈ Icc (0 : ℝ) 1) (t : ℝ) :
    gapHi β α c ≤ t ↔ ∃ s ∈ Icc c (min t 1), β s ∈ α '' Icc 0 1 := by
  have hS : IsCompact (Sec7.pocketContactSet β α ∩ Icc c 1) :=
    isCompact_Icc.inter_left (isClosed_pocketContactSet hβ hα)
  have h1 : (1 : ℝ) ∈ Sec7.pocketContactSet β α ∩ Icc c 1 := ⟨one_mem_pocketContactSet hβ hα, hc.2, le_rfl⟩
  have hmem := hS.sInf_mem ⟨1, h1⟩
  constructor
  · intro ht
    exact ⟨_, ⟨hmem.2.1, le_min ht hmem.2.2⟩, hmem.1.2⟩
  · rintro ⟨s, hs, hsα⟩
    have hs1 : s ≤ 1 := hs.2.trans (min_le_right _ _)
    have hsS : s ∈ Sec7.pocketContactSet β α ∩ Icc c 1 := ⟨⟨⟨hc.1.trans hs.1, hs1⟩, hsα⟩, hs.1, hs1⟩
    exact (csInf_le hS.bddBelow hsS).trans (hs.2.trans (min_le_left _ _))

/-- The parameter along `α` of a contact through an interval test. -/
theorem contactMap_le_iff (hα : IsDiscCrosscut α) {a : ℝ} (ha : a ∈ Sec7.pocketContactSet β α) (t : ℝ) :
    contactMap β α a ≤ t ↔ ∃ x ∈ Icc 0 (min t 1), α x = β a := by
  constructor
  · intro h
    obtain ⟨hx, hαx⟩ := contactMap_mem hα ha
    exact ⟨_, ⟨hx.1, le_min h hx.2⟩, hαx⟩
  · rintro ⟨x, hx, hαx⟩
    rw [contactMap_eq hα ⟨hx.1, hx.2.trans (min_le_right _ _)⟩ hαx.symm]
    exact hx.2.trans (min_le_left _ _)

/-- A crosscut lies in the closed unit disc. -/
theorem mem_closedBall_of_isDiscCrosscut (hα : IsDiscCrosscut α) {s : ℝ} (hs : s ∈ Icc (0 : ℝ) 1) :
    α s ∈ closedBall (0 : ℂ) 1 := by
  rcases eq_or_lt_of_le hs.1 with rfl | h0
  · rw [hα.zero]; simp
  rcases eq_or_lt_of_le hs.2 with rfl | h1
  · rw [hα.one]; simp
  exact ball_subset_closedBall (hα.mem_disc s ⟨h0, h1⟩)

end Iff

/-! ### A measurable minimum test -/

section Test

variable {Ω : Type*} [MeasurableSpace Ω]

/-- **A minimum test through countably many points is measurable**: on a measurable event `G` on which `F ω` is
continuous on the nonempty compact `K ω` and the points `d q ω` lie in `K ω` densely, the event "`F ω` takes a value
`≤ a ω` on `K ω`" is measurable once each `ω ↦ F ω (d q ω)` and `a` are. -/
theorem measurableSet_inter_exists_le {ι : Type*} [Countable ι] {G : Set Ω} (hG : MeasurableSet G) {X : Type*}
    [TopologicalSpace X] {K : Ω → Set X} {F : Ω → X → ℝ} {a : Ω → ℝ} {d : ι → Ω → X}
    (hK : ∀ ω ∈ G, IsCompact (K ω) ∧ (K ω).Nonempty ∧ ContinuousOn (F ω) (K ω) ∧
      range (fun q => d q ω) ⊆ K ω ∧ K ω ⊆ closure (range fun q => d q ω))
    (hm : ∀ q, Measurable fun ω => F ω (d q ω)) (ha : Measurable a) :
    MeasurableSet (G ∩ {ω | ∃ x ∈ K ω, F ω x ≤ a ω}) := by
  have e : G ∩ {ω | ∃ x ∈ K ω, F ω x ≤ a ω} =
      G ∩ ⋂ n : ℕ, ⋃ q : ι, {ω | F ω (d q ω) < a ω + 1 / ((n : ℝ) + 1)} := by
    ext ω
    simp only [mem_inter_iff, mem_ofPred_eq, mem_iInter, mem_iUnion, and_congr_right_iff]
    intro hω
    obtain ⟨hKc, hKne, hF, hdK, hKd⟩ := hK ω hω
    rw [exists_le_iff_dense hKc hKne hF hdK hKd]
    simp only [mem_range, exists_exists_eq_and]
  rw [e]
  exact hG.inter (MeasurableSet.iInter fun n => MeasurableSet.iUnion fun q =>
    measurableSet_lt (hm q) (ha.add measurable_const))

end Test

/-! ### The random walls in the disc -/

section Random

open Lemma71I

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {R L : Ω → ℝ≥0 → ℂ} {r : ℝ≥0} {G : Set Ω}

theorem measurable_cayley : Measurable cayley := by
  have : cayley = fun z => (z - I) / (z + I) := rfl
  rw [this]
  exact (measurable_id.sub_const _).div (measurable_id.add_const _)

/-- The disc crosscut of a random wall is measurable at each parameter. -/
theorem measurable_toDisc_apply (hRm : ∀ t, Measurable fun ω => R ω t) (s : ℝ) :
    Measurable fun ω => toDisc (realPath (R ω)) s := by
  by_cases hs : s < 1
  · simp only [toDisc_of_lt hs]
    exact measurable_cayley.comp (hRm _)
  · simp only [toDisc, hs, ↓reduceIte]
    exact measurable_const

/-- The wall in the disc, clamped to `[0, 1]` and set to `0` off `G`: continuous in the parameter for every `ω`. -/
def discPath (G : Set Ω) (R : Ω → ℝ≥0 → ℂ) (x : ℝ) (ω : Ω) : ℂ :=
  by classical exact if ω ∈ G then toDisc (realPath (R ω)) (clamp 0 1 x) else 0

omit mΩ in
theorem discPath_of_mem {x : ℝ} (hx : x ∈ Icc (0 : ℝ) 1) {ω : Ω} (hω : ω ∈ G) :
    discPath G R x ω = toDisc (realPath (R ω)) x := by
  simp only [discPath, hω, ↓reduceIte, clamp_of_mem hx]

omit mΩ in
theorem continuous_discPath (hG : ∀ ω ∈ G, IsSimpleProper (R ω)) (ω : Ω) :
    Continuous fun x => discPath G R x ω := by
  by_cases hω : ω ∈ G
  · simp only [discPath, hω, ↓reduceIte]
    exact (hG ω hω).isProperArc.isDiscCrosscut_toDisc.cont.comp_continuous (continuous_clamp 0 1)
      (clamp_mem zero_le_one)
  · simp only [discPath, hω, ↓reduceIte]
    exact continuous_const

theorem measurable_discPath (hGm : MeasurableSet G) (hRm : ∀ t, Measurable fun ω => R ω t) (x : ℝ) :
    Measurable (discPath G R x) := by
  classical
  exact Measurable.ite hGm (measurable_toDisc_apply hRm _) measurable_const

/-- **Joint measurability** of the clamped disc wall in the parameter and `ω`. -/
theorem measurable_uncurry_discPath (hGm : MeasurableSet G) (hG : ∀ ω ∈ G, IsSimpleProper (R ω))
    (hRm : ∀ t, Measurable fun ω => R ω t) : Measurable (uncurry (discPath G R)) :=
  measurable_uncurry_of_continuous_of_measurable (continuous_discPath hG) (measurable_discPath hGm hRm)

theorem measurable_discPath_comp (hGm : MeasurableSet G) (hG : ∀ ω ∈ G, IsSimpleProper (R ω))
    (hRm : ∀ t, Measurable fun ω => R ω t) {y : Ω → ℝ} (hy : Measurable y) :
    Measurable fun ω => discPath G R (y ω) ω :=
  (measurable_uncurry_discPath hGm hG hRm).comp (hy.prodMk measurable_id)

/-- The lower end of the change gap along the left wall (`0` off `G`). -/
def gapLoR (G : Set Ω) (R L : Ω → ℝ≥0 → ℂ) (r : ℝ≥0) (ω : Ω) : ℝ :=
  by classical exact if ω ∈ G then gapLo (toDisc (realPath (L ω))) (toDisc (realPath (R ω))) (discTime r) else 0

/-- The upper end of the change gap along the left wall (`1` off `G`). -/
def gapHiR (G : Set Ω) (R L : Ω → ℝ≥0 → ℂ) (r : ℝ≥0) (ω : Ω) : ℝ :=
  by classical exact if ω ∈ G then gapHi (toDisc (realPath (L ω))) (toDisc (realPath (R ω))) (discTime r) else 1

/-- The parameter along the right wall of the contact point of the left wall at `g ω` (`0` off `G`). -/
def cornerα (G : Set Ω) (R L : Ω → ℝ≥0 → ℂ) (g : Ω → ℝ) (ω : Ω) : ℝ :=
  by classical exact if ω ∈ G then contactMap (toDisc (realPath (L ω))) (toDisc (realPath (R ω))) (g ω) else 0

/-- The ends of the change gap along the right wall. -/
def gapLoα (G : Set Ω) (R L : Ω → ℝ≥0 → ℂ) (r : ℝ≥0) : Ω → ℝ := cornerα G R L (gapLoR G R L r)

def gapHiα (G : Set Ω) (R L : Ω → ℝ≥0 → ℂ) (r : ℝ≥0) : Ω → ℝ := cornerα G R L (gapHiR G R L r)

/-- Closure of clamped rational pairs. -/
theorem prod_subset_closure_clamp {a b a' b' : ℝ} :
    Icc a b ×ˢ Icc a' b' ⊆ closure (range fun q : ℚ × ℚ => (clamp a b q.1, clamp a' b' q.2)) := by
  have : (range fun q : ℚ × ℚ => (clamp a b q.1, clamp a' b' q.2)) =
      (range fun q : ℚ => clamp a b q) ×ˢ (range fun q : ℚ => clamp a' b' q) := by
    rw [← range_prodMap]
    rfl
  rw [this, closure_prod_eq]
  exact prod_mono (fun x hx => mem_closure_clamp_rat hx) (fun x hx => mem_closure_clamp_rat hx)

variable
  (hRm : ∀ t, Measurable fun ω => R ω t) (hLm : ∀ t, Measurable fun ω => L ω t)
  (hGm : MeasurableSet G) (hG : ∀ ω ∈ G, IsChangeConfigInc (R ω) (L ω) r)
include hRm hLm hGm hG

theorem measurable_gapLoR : Measurable (gapLoR G R L r) := by
  classical
  have hGR : ∀ ω ∈ G, IsSimpleProper (R ω) := fun ω hω => (hG ω hω).right
  have hGL : ∀ ω ∈ G, IsSimpleProper (L ω) := fun ω hω => (hG ω hω).left
  have hc := discTime_mem_Icc r
  refine measurable_of_Ici fun t => ?_
  have e : gapLoR G R L r ⁻¹' Ici t = (G ∩ {ω | ∃ p ∈ Icc (max t 0) (discTime r) ×ˢ Icc (0 : ℝ) 1,
      dist (discPath G L p.1 ω) (discPath G R p.2 ω) ≤ 0}) ∪ (Gᶜ ∩ {_ω | t ≤ 0}) := by
    ext ω
    by_cases hω : ω ∈ G
    · simp only [gapLoR, hω, ↓reduceIte, mem_preimage, mem_Ici, mem_union, mem_inter_iff, mem_ofPred_eq,
        true_and, mem_compl_iff, not_true_eq_false, false_and, or_false]
      rw [le_gapLo_iff (hG ω hω).isDiscCrosscut_right (hG ω hω).isDiscCrosscut_left hc]
      constructor
      · rintro ⟨s, hs, x, hx, hxs⟩
        refine ⟨(s, x), ⟨hs, hx⟩, ?_⟩
        have hs01 : s ∈ Icc (0 : ℝ) 1 := ⟨(le_max_right _ _).trans hs.1, hs.2.trans hc.2⟩
        rw [discPath_of_mem hs01 hω, discPath_of_mem hx hω, hxs, dist_self]
      · rintro ⟨⟨s, x⟩, ⟨hs, hx⟩, hd⟩
        have hs01 : s ∈ Icc (0 : ℝ) 1 := ⟨(le_max_right _ _).trans hs.1, hs.2.trans hc.2⟩
        rw [discPath_of_mem hs01 hω, discPath_of_mem hx hω] at hd
        exact ⟨s, hs, x, hx, (dist_le_zero.1 hd).symm⟩
    · simp only [gapLoR, hω, ↓reduceIte, mem_preimage, mem_Ici, mem_union, mem_inter_iff, mem_ofPred_eq,
        false_and, mem_compl_iff, not_false_eq_true, true_and, false_or]
  rw [e]
  refine MeasurableSet.union ?_ (hGm.compl.inter (MeasurableSet.const _))
  by_cases hK : max t 0 ≤ discTime r
  · refine measurableSet_inter_exists_le (d := fun (q : ℚ × ℚ) (_ : Ω) => (clamp (max t 0) (discTime r) q.1,
      clamp 0 1 q.2)) hGm (fun ω _ => ⟨isCompact_Icc.prod isCompact_Icc, ⟨(max t 0, 0), ⟨le_rfl, hK⟩,
        le_rfl, zero_le_one⟩, ((continuous_discPath hGL ω).comp continuous_fst).dist
        ((continuous_discPath hGR ω).comp continuous_snd) |>.continuousOn, ?_, prod_subset_closure_clamp⟩)
      (fun q => (measurable_discPath hGm hLm _).dist (measurable_discPath hGm hRm _)) measurable_const
    rintro _ ⟨q, rfl⟩
    exact ⟨clamp_mem hK _, clamp_mem zero_le_one _⟩
  · have : G ∩ {ω | ∃ p ∈ Icc (max t 0) (discTime r) ×ˢ Icc (0 : ℝ) 1,
        dist (discPath G L p.1 ω) (discPath G R p.2 ω) ≤ 0} = ∅ := by
      ext ω
      simp only [mem_inter_iff, mem_ofPred_eq, mem_empty_iff_false, iff_false, not_and, not_exists]
      exact fun _ p hp => absurd (hp.1.1.trans hp.1.2) hK
    rw [this]
    exact MeasurableSet.empty

theorem measurable_gapHiR : Measurable (gapHiR G R L r) := by
  classical
  have hGR : ∀ ω ∈ G, IsSimpleProper (R ω) := fun ω hω => (hG ω hω).right
  have hGL : ∀ ω ∈ G, IsSimpleProper (L ω) := fun ω hω => (hG ω hω).left
  have hc := discTime_mem_Icc r
  refine measurable_of_Iic fun t => ?_
  have e : gapHiR G R L r ⁻¹' Iic t = (G ∩ {ω | ∃ p ∈ Icc (discTime r) (min t 1) ×ˢ Icc (0 : ℝ) 1,
      dist (discPath G L p.1 ω) (discPath G R p.2 ω) ≤ 0}) ∪ (Gᶜ ∩ {_ω | 1 ≤ t}) := by
    ext ω
    by_cases hω : ω ∈ G
    · simp only [gapHiR, hω, ↓reduceIte, mem_preimage, mem_Iic, mem_union, mem_inter_iff, mem_ofPred_eq,
        true_and, mem_compl_iff, not_true_eq_false, false_and, or_false]
      rw [gapHi_le_iff (hG ω hω).isDiscCrosscut_right (hG ω hω).isDiscCrosscut_left hc]
      constructor
      · rintro ⟨s, hs, x, hx, hxs⟩
        refine ⟨(s, x), ⟨hs, hx⟩, ?_⟩
        have hs01 : s ∈ Icc (0 : ℝ) 1 := ⟨hc.1.trans hs.1, hs.2.trans (min_le_right _ _)⟩
        rw [discPath_of_mem hs01 hω, discPath_of_mem hx hω, hxs, dist_self]
      · rintro ⟨⟨s, x⟩, ⟨hs, hx⟩, hd⟩
        have hs01 : s ∈ Icc (0 : ℝ) 1 := ⟨hc.1.trans hs.1, hs.2.trans (min_le_right _ _)⟩
        rw [discPath_of_mem hs01 hω, discPath_of_mem hx hω] at hd
        exact ⟨s, hs, x, hx, (dist_le_zero.1 hd).symm⟩
    · simp only [gapHiR, hω, ↓reduceIte, mem_preimage, mem_Iic, mem_union, mem_inter_iff, mem_ofPred_eq,
        false_and, mem_compl_iff, not_false_eq_true, true_and, false_or]
  rw [e]
  refine MeasurableSet.union ?_ (hGm.compl.inter (MeasurableSet.const _))
  by_cases hK : discTime r ≤ min t 1
  · refine measurableSet_inter_exists_le (d := fun (q : ℚ × ℚ) (_ : Ω) => (clamp (discTime r) (min t 1) q.1,
      clamp 0 1 q.2)) hGm (fun ω _ => ⟨isCompact_Icc.prod isCompact_Icc, ⟨(discTime r, 0), ⟨le_rfl, hK⟩,
        le_rfl, zero_le_one⟩, ((continuous_discPath hGL ω).comp continuous_fst).dist
        ((continuous_discPath hGR ω).comp continuous_snd) |>.continuousOn, ?_, prod_subset_closure_clamp⟩)
      (fun q => (measurable_discPath hGm hLm _).dist (measurable_discPath hGm hRm _)) measurable_const
    rintro _ ⟨q, rfl⟩
    exact ⟨clamp_mem hK _, clamp_mem zero_le_one _⟩
  · have : G ∩ {ω | ∃ p ∈ Icc (discTime r) (min t 1) ×ˢ Icc (0 : ℝ) 1,
        dist (discPath G L p.1 ω) (discPath G R p.2 ω) ≤ 0} = ∅ := by
      ext ω
      simp only [mem_inter_iff, mem_ofPred_eq, mem_empty_iff_false, iff_false, not_and, not_exists]
      exact fun _ p hp => absurd (hp.1.1.trans hp.1.2) hK
    rw [this]
    exact MeasurableSet.empty

omit mΩ hRm hLm hGm in
/-- On `G`, the gap ends along the left wall form the change gap. -/
theorem gap_of_mem {ω : Ω} (hω : ω ∈ G) :
    IsContactGap (toDisc (realPath (L ω))) (toDisc (realPath (R ω))) (gapLoR G R L r ω) (gapHiR G R L r ω) ∧
      discTime r ∈ Ioo (gapLoR G R L r ω) (gapHiR G R L r ω) := by
  classical
  simp only [gapLoR, gapHiR, hω, ↓reduceIte]
  exact isContactGap_gapLo_gapHi (hG ω hω).isDiscCrosscut_right (hG ω hω).isDiscCrosscut_left
    (discTime_mem_Icc r) (hG ω hω).notMem_crossRange

/-- The parameter along the right wall of a corner, measurably (generic form). -/
theorem measurable_contactMap_corner {g : Ω → ℝ} (hg : Measurable g)
    (hgS : ∀ ω ∈ G, g ω ∈ Sec7.pocketContactSet (toDisc (realPath (L ω))) (toDisc (realPath (R ω)))) :
    Measurable (cornerα G R L g) := by
  classical
  have hGR : ∀ ω ∈ G, IsSimpleProper (R ω) := fun ω hω => (hG ω hω).right
  have hGL : ∀ ω ∈ G, IsSimpleProper (L ω) := fun ω hω => (hG ω hω).left
  refine measurable_of_Iic fun t => ?_
  have e : cornerα G R L g ⁻¹' Iic t = (G ∩ {ω | ∃ x ∈ Icc (0 : ℝ) (min t 1),
        dist (discPath G R x ω) (discPath G L (g ω) ω) ≤ 0}) ∪ (Gᶜ ∩ {_ω | 0 ≤ t}) := by
    ext ω
    by_cases hω : ω ∈ G
    · simp only [cornerα, hω, ↓reduceIte, mem_preimage, mem_Iic, mem_union, mem_inter_iff, mem_ofPred_eq,
        true_and, mem_compl_iff, not_true_eq_false, false_and, or_false]
      rw [contactMap_le_iff (hG ω hω).isDiscCrosscut_right (hgS ω hω)]
      have hg01 : g ω ∈ Icc (0 : ℝ) 1 := (hgS ω hω).1
      constructor
      · rintro ⟨x, hx, hxg⟩
        have hx01 : x ∈ Icc (0 : ℝ) 1 := ⟨hx.1, hx.2.trans (min_le_right _ _)⟩
        exact ⟨x, hx, by rw [discPath_of_mem hx01 hω, discPath_of_mem hg01 hω, hxg, dist_self]⟩
      · rintro ⟨x, hx, hd⟩
        have hx01 : x ∈ Icc (0 : ℝ) 1 := ⟨hx.1, hx.2.trans (min_le_right _ _)⟩
        rw [discPath_of_mem hx01 hω, discPath_of_mem hg01 hω] at hd
        exact ⟨x, hx, dist_le_zero.1 hd⟩
    · simp only [cornerα, hω, ↓reduceIte, mem_preimage, mem_Iic, mem_union, mem_inter_iff, mem_ofPred_eq,
        false_and, mem_compl_iff, not_false_eq_true, true_and, false_or]
  rw [e]
  refine MeasurableSet.union ?_ (hGm.compl.inter (MeasurableSet.const _))
  by_cases hK : (0 : ℝ) ≤ min t 1
  · refine measurableSet_inter_exists_le (d := fun (q : ℚ) (_ : Ω) => clamp 0 (min t 1) q) hGm
      (fun ω _ => ⟨isCompact_Icc, ⟨0, le_rfl, hK⟩, ((continuous_discPath hGR ω).dist continuous_const).continuousOn,
        ?_, fun x hx => mem_closure_clamp_rat hx⟩)
      (fun q => (measurable_discPath hGm hRm _).dist (measurable_discPath_comp hGm hGL hLm hg)) measurable_const
    rintro _ ⟨q, rfl⟩
    exact clamp_mem hK _
  · have : G ∩ {ω | ∃ x ∈ Icc (0 : ℝ) (min t 1), dist (discPath G R x ω) (discPath G L (g ω) ω) ≤ 0} = ∅ := by
      ext ω
      simp only [mem_inter_iff, mem_ofPred_eq, mem_empty_iff_false, iff_false, not_and, not_exists]
      exact fun _ x hx => absurd (hx.1.trans hx.2) hK
    rw [this]
    exact MeasurableSet.empty

theorem measurable_gapLoα : Measurable (gapLoα G R L r) :=
  measurable_contactMap_corner hRm hLm hGm hG (measurable_gapLoR hRm hLm hGm hG)
    (fun _ hω => (gap_of_mem hG hω).1.1)

theorem measurable_gapHiα : Measurable (gapHiα G R L r) :=
  measurable_contactMap_corner hRm hLm hGm hG (measurable_gapHiR hRm hLm hGm hG)
    (fun _ hω => (gap_of_mem hG hω).1.2.1)

/-- The boundary curve of the change gap in the disc (empty off `G`). -/
def gapCurve (G : Set Ω) (R L : Ω → ℝ≥0 → ℂ) (r : ℝ≥0) (ω : Ω) : Set ℂ :=
  by classical exact (if ω ∈ G then (toDisc (realPath (R ω)) '' Icc (gapLoα G R L r ω) (gapHiα G R L r ω) ∪
      toDisc (realPath (L ω)) '' Icc (gapLoR G R L r ω) (gapHiR G R L r ω)) else ∅)

omit mΩ hRm hLm hGm in
/-- On `G` the boundary curve is the pocket curve of the change gap, and the change gap is its inside. -/
theorem gapCurve_props {ω : Ω} (hω : ω ∈ G) :
    IsContactGap (toDisc (realPath (R ω))) (toDisc (realPath (L ω))) (gapLoα G R L r ω) (gapHiα G R L r ω) ∧
      gapCurve G R L r ω = pocketCurve (toDisc (realPath (R ω))) (toDisc (realPath (L ω))) (gapLoα G R L r ω)
        (gapHiα G R L r ω) ∧
      changeGap (toDisc (realPath (R ω))) (toDisc (realPath (L ω))) (discTime r) = jordanIn (gapCurve G R L r ω) ∧
      Icc (gapLoα G R L r ω) (gapHiα G R L r ω) ⊆ Icc 0 1 ∧ Icc (gapLoR G R L r ω) (gapHiR G R L r ω) ⊆ Icc 0 1 := by
  classical
  have h := hG ω hω
  obtain ⟨hg, h1, h2, heq⟩ := PocketCoord.changeGap_eq h.isDiscCrosscut_right h.isDiscCrosscut_left h.inc
    (discTime_mem_Icc r) h.notMem_crossRange
  have eLo : gapLoα G R L r ω = contactMap (toDisc (realPath (L ω))) (toDisc (realPath (R ω)))
      (gapLo (toDisc (realPath (L ω))) (toDisc (realPath (R ω))) (discTime r)) := by
    simp only [gapLoα, cornerα, gapLoR, hω, ↓reduceIte]
  have eHi : gapHiα G R L r ω = contactMap (toDisc (realPath (L ω))) (toDisc (realPath (R ω)))
      (gapHi (toDisc (realPath (L ω))) (toDisc (realPath (R ω))) (discTime r)) := by
    simp only [gapHiα, cornerα, gapHiR, hω, ↓reduceIte]
  have eLoR : gapLoR G R L r ω = gapLo (toDisc (realPath (L ω))) (toDisc (realPath (R ω))) (discTime r) := by
    simp only [gapLoR, hω, ↓reduceIte]
  have eHiR : gapHiR G R L r ω = gapHi (toDisc (realPath (L ω))) (toDisc (realPath (R ω))) (discTime r) := by
    simp only [gapHiR, hω, ↓reduceIte]
  have hcurve : gapCurve G R L r ω = pocketCurve (toDisc (realPath (R ω))) (toDisc (realPath (L ω)))
      (gapLoα G R L r ω) (gapHiα G R L r ω) := by
    simp only [gapCurve, hω, ↓reduceIte, pocketCurve]
    rw [eLo, eHi, h1, h2, eLoR, eHiR]
  rw [← eLo, ← eHi] at hg heq
  refine ⟨hg, hcurve, by rw [heq, hcurve], fun x hx => ⟨hg.1.1.1.trans hx.1, hx.2.trans hg.2.1.1.2⟩, ?_⟩
  obtain ⟨hgL, -⟩ := gap_of_mem (r := r) hG hω
  exact fun x hx => ⟨hgL.1.1.1.trans hx.1, hx.2.trans hgL.2.1.1.2⟩

omit mΩ hRm hLm hGm in
theorem isClosed_gapCurve (ω : Ω) : IsClosed (gapCurve G R L r ω) := by
  classical
  by_cases hω : ω ∈ G
  · obtain ⟨-, -, -, hI, hIR⟩ := gapCurve_props hG hω
    simp only [gapCurve, hω, ↓reduceIte]
    exact ((isCompact_Icc.image_of_continuousOn ((hG ω hω).isDiscCrosscut_right.cont.mono hI)).union
      (isCompact_Icc.image_of_continuousOn ((hG ω hω).isDiscCrosscut_left.cont.mono hIR))).isClosed
  · simp only [gapCurve, hω, ↓reduceIte]
    exact isClosed_empty

omit mΩ hRm hLm hGm in
theorem gapCurve_subset_closedBall (ω : Ω) : gapCurve G R L r ω ⊆ closedBall 0 1 := by
  classical
  by_cases hω : ω ∈ G
  · obtain ⟨-, -, -, hI, hIR⟩ := gapCurve_props hG hω
    simp only [gapCurve, hω, ↓reduceIte]
    rintro _ (⟨x, hx, rfl⟩ | ⟨x, hx, rfl⟩)
    · exact mem_closedBall_of_isDiscCrosscut (hG ω hω).isDiscCrosscut_right (hI hx)
    · exact mem_closedBall_of_isDiscCrosscut (hG ω hω).isDiscCrosscut_left (hIR hx)
  · simp only [gapCurve, hω, ↓reduceIte]
    exact empty_subset _

/-- **Closed balls off the boundary curve of the change gap: measurable events.** -/
theorem measurableSet_closedBall_subset_compl_gapCurve (p : ℂ) (ρ : ℝ) :
    MeasurableSet {ω | closedBall p ρ ⊆ (gapCurve G R L r ω)ᶜ} := by
  classical
  have hGR : ∀ ω ∈ G, IsSimpleProper (R ω) := fun ω hω => (hG ω hω).right
  have hGL : ∀ ω ∈ G, IsSimpleProper (L ω) := fun ω hω => (hG ω hω).left
  have hA := measurableSet_inter_exists_le (d := fun (q : ℚ) ω => clamp (gapLoα G R L r ω) (gapHiα G R L r ω) q)
    (K := fun ω => Icc (gapLoα G R L r ω) (gapHiα G R L r ω)) (F := fun ω x => dist (discPath G R x ω) p)
    (a := fun _ => ρ) hGm (fun ω hω => ⟨isCompact_Icc, nonempty_Icc.2 (gapCurve_props hG hω).1.2.2.1.le,
      ((continuous_discPath hGR ω).dist continuous_const).continuousOn,
      by rintro _ ⟨q, rfl⟩; exact clamp_mem (gapCurve_props hG hω).1.2.2.1.le _,
      fun x hx => mem_closure_clamp_rat hx⟩)
    (fun q => (measurable_discPath_comp hGm hGR hRm ((measurable_gapLoα hRm hLm hGm hG).max
      ((measurable_gapHiα hRm hLm hGm hG).min measurable_const))).dist measurable_const) measurable_const
  have hB := measurableSet_inter_exists_le (d := fun (q : ℚ) ω => clamp (gapLoR G R L r ω) (gapHiR G R L r ω) q)
    (K := fun ω => Icc (gapLoR G R L r ω) (gapHiR G R L r ω)) (F := fun ω x => dist (discPath G L x ω) p)
    (a := fun _ => ρ) hGm (fun ω hω => ⟨isCompact_Icc, nonempty_Icc.2 (gap_of_mem hG hω).1.2.2.1.le,
      ((continuous_discPath hGL ω).dist continuous_const).continuousOn,
      by rintro _ ⟨q, rfl⟩; exact clamp_mem (gap_of_mem hG hω).1.2.2.1.le _,
      fun x hx => mem_closure_clamp_rat hx⟩)
    (fun q => (measurable_discPath_comp hGm hGL hLm ((measurable_gapLoR hRm hLm hGm hG).max
      ((measurable_gapHiR hRm hLm hGm hG).min measurable_const))).dist measurable_const) measurable_const
  have e : {ω | closedBall p ρ ⊆ (gapCurve G R L r ω)ᶜ} =
      Gᶜ ∪ (G \ ((G ∩ {ω | ∃ x ∈ Icc (gapLoα G R L r ω) (gapHiα G R L r ω), dist (discPath G R x ω) p ≤ ρ}) ∪
        (G ∩ {ω | ∃ x ∈ Icc (gapLoR G R L r ω) (gapHiR G R L r ω), dist (discPath G L x ω) p ≤ ρ}))) := by
    ext ω
    by_cases hω : ω ∈ G
    · obtain ⟨-, -, -, hI, hIR⟩ := gapCurve_props hG hω
      simp only [mem_ofPred_eq, mem_union, mem_compl_iff, hω, not_true_eq_false, false_or, Set.mem_sdiff, true_and,
        mem_inter_iff, not_or, not_exists, not_and]
      simp only [gapCurve, hω, ↓reduceIte, subset_compl_iff_disjoint_right, disjoint_union_right]
      constructor
      · rintro ⟨h1, h2⟩
        refine ⟨fun x hx hd => Set.disjoint_left.1 h1 ?_ ⟨x, hx, rfl⟩, fun x hx hd => Set.disjoint_left.1 h2 ?_
          ⟨x, hx, rfl⟩⟩
        · rw [discPath_of_mem (hI hx) hω] at hd
          exact mem_closedBall.2 hd
        · rw [discPath_of_mem (hIR hx) hω] at hd
          exact mem_closedBall.2 hd
      · rintro ⟨h1, h2⟩
        refine ⟨Set.disjoint_left.2 ?_, Set.disjoint_left.2 ?_⟩
        · rintro _ hz ⟨x, hx, rfl⟩
          exact h1 x hx (by rw [discPath_of_mem (hI hx) hω]; exact mem_closedBall.1 hz)
        · rintro _ hz ⟨x, hx, rfl⟩
          exact h2 x hx (by rw [discPath_of_mem (hIR hx) hω]; exact mem_closedBall.1 hz)
    · simp only [mem_ofPred_eq, mem_union, mem_compl_iff, hω, not_false_eq_true, true_or, iff_true]
      simp only [gapCurve, hω, ↓reduceIte, compl_empty, subset_univ]
  rw [e]
  exact hGm.compl.union (hGm.diff (hA.union hB))

/-- **Membership of a fixed point in the change gap is a measurable event** (on `G`). -/
theorem measurableSet_mem_changeGap (w : ℂ) :
    MeasurableSet (G ∩ {ω | w ∈ changeGap (toDisc (realPath (R ω))) (toDisc (realPath (L ω))) (discTime r)}) := by
  have hUo : ∀ ω, IsOpen (gapCurve G R L r ω)ᶜ := fun ω => (isClosed_gapCurve hG ω).isOpen_compl
  have h2 : ∀ ω, (fun _ : ℕ => (2 : ℂ)) ((fun _ : Ω => 0) ω) ∈ (gapCurve G R L r ω)ᶜ := fun ω h => by
    have := gapCurve_subset_closedBall hG ω h
    rw [mem_closedBall, dist_zero_right] at this
    norm_num at this
  have hcomp := Lemma71E.measurableSet_closedBall_subset_component (e := fun _ : ℕ => (2 : ℂ))
    (Np := fun _ : Ω => 0) hUo (measurableSet_closedBall_subset_compl_gapCurve hRm hLm hGm hG) measurable_const h2
    w 0
  have e : G ∩ {ω | w ∈ changeGap (toDisc (realPath (R ω))) (toDisc (realPath (L ω))) (discTime r)} =
      G ∩ ({ω | closedBall w 0 ⊆ (gapCurve G R L r ω)ᶜ} \
        {ω | closedBall w 0 ⊆ connectedComponentIn (gapCurve G R L r ω)ᶜ 2}) := by
    ext ω
    simp only [mem_inter_iff, mem_ofPred_eq, Set.mem_sdiff, and_congr_right_iff, closedBall_zero, singleton_subset_iff]
    intro hω
    obtain ⟨hg, hcurve, heq, -, -⟩ := gapCurve_props hG hω
    have hJ : LQGMetric.JordanMap.IsJordanCurve (gapCurve G R L r ω) := by
      rw [hcurve]
      exact (pocket_props_of_strictMono (hG ω hω).isDiscCrosscut_right (hG ω hω).isDiscCrosscut_left
        (hG ω hω).inc hg).1
    rw [heq, mem_jordanIn_iff hJ (gapCurve_subset_closedBall hG ω)]
    rfl
  rw [e]
  exact hGm.inter ((measurableSet_closedBall_subset_compl_gapCurve hRm hLm hGm hG w 0).diff hcomp)

omit mΩ hRm hLm hGm in
/-- On `G`, membership in the change pocket through its Cayley image. -/
theorem mem_changePocket_iff {ω : Ω} (hω : ω ∈ G) (z : ℂ) :
    z ∈ changePocket (R ω) (L ω) r ↔
      z ∈ H ∧ cayley z ∈ changeGap (toDisc (realPath (R ω))) (toDisc (realPath (L ω))) (discTime r) := by
  have h := hG ω hω
  obtain ⟨hg, heq⟩ := h.changeGap_eq
  have hball : changeGap (toDisc (realPath (R ω))) (toDisc (realPath (L ω))) (discTime r) ⊆ ball 0 1 := by
    rw [heq]
    exact (pocket_props_of_strictMono h.isDiscCrosscut_right h.isDiscCrosscut_left h.inc hg).2.1
  constructor
  · rintro ⟨w, hw, rfl⟩
    exact ⟨QuantumZipper.CA.cayleyInv_mem_H (hball hw), by rwa [cayley_cayleyInv_of_mem_ball (hball hw)]⟩
  · rintro ⟨hz, hw⟩
    exact ⟨cayley z, hw, cayleyInv_cayley_of_mem_Hbar (le_of_lt (show (0 : ℝ) < z.im from hz))⟩

/-- **Aux. lemma 130's change pocket as a random object, under increasing contact order** ("The event and the
selected component are measurable from their complete labeled incoming paths alone", p. 409): for random walls with
measurable coordinates and a measurable event `G` on which they satisfy `IsChangeConfigInc` (Aux. lemma 130's event
`F_r` with the increasing contact order of the incoming paths), there are a measurable index `Np` (into a dense
sequence `e`) and a random open, connected, simply connected `C ω ⊆ ℍ` with measurable closed-ball events and
`e (Np ω) ∈ C ω`, which is the change pocket on `G` and the default disc off `G`. -/
theorem exists_measurable_changePocketInc {e : ℕ → ℂ} (he : DenseRange e) :
    ∃ (C : Ω → Set ℂ) (Np : Ω → ℕ), Measurable Np ∧
      (∀ ω, IsOpen (C ω) ∧ IsConnected (C ω) ∧ IsSimplyConnected (C ω) ∧ C ω ⊆ H) ∧
      (∀ (c : ℂ) (ρ : ℝ), MeasurableSet {ω | closedBall c ρ ⊆ C ω}) ∧ (∀ ω, e (Np ω) ∈ C ω) ∧
      (∀ ω ∈ G, C ω = changePocket (R ω) (L ω) r) ∧ (∀ ω, ω ∉ G → C ω = Lemma71Pin.defaultPocket) := by
  classical
  -- the test at a rational point
  set B : ℕ → Set Ω := fun k => G ∩ {ω | e k ∈ H ∧
      cayley (e k) ∈ changeGap (toDisc (realPath (R ω))) (toDisc (realPath (L ω))) (discTime r)} with hBdef
  have hBm : ∀ k, MeasurableSet (B k) := fun k => by
    by_cases hk : e k ∈ H
    · have e' : B k = G ∩ {ω | cayley (e k) ∈
          changeGap (toDisc (realPath (R ω))) (toDisc (realPath (L ω))) (discTime r)} := by
        ext ω
        simp only [hBdef, mem_inter_iff, mem_ofPred_eq, hk, true_and]
      rw [e']
      exact measurableSet_mem_changeGap hRm hLm hGm hG _
    · have e' : B k = ∅ := by
        ext ω
        simp only [hBdef, mem_inter_iff, mem_ofPred_eq, hk, false_and, and_false, mem_empty_iff_false]
      rw [e']
      exact MeasurableSet.empty
  set p : Ω → ℕ → Prop := fun ω k => ω ∈ B k ∨ ∀ j, ω ∉ B j with hpdef
  have hp : ∀ ω, ∃ k, p ω k := fun ω => by
    by_cases h : ∃ j, ω ∈ B j
    · obtain ⟨j, hj⟩ := h
      exact ⟨j, Or.inl hj⟩
    · push Not at h
      exact ⟨0, Or.inr h⟩
  have hpm : ∀ k, MeasurableSet {ω | p ω k} := fun k => by
    have e' : {ω | p ω k} = B k ∪ ⋂ j, (B j)ᶜ := by
      ext ω
      simp only [hpdef, mem_ofPred_eq, mem_union, mem_iInter, mem_compl_iff]
    rw [e']
    exact (hBm k).union (MeasurableSet.iInter fun j => (hBm j).compl)
  set Nf : Ω → ℕ := fun ω => Nat.find (hp ω) with hNfdef
  have hNf : Measurable Nf := measurable_find hp hpm
  obtain ⟨k₀, hk₀⟩ := he.exists_mem_open isOpen_ball ⟨2 * I, mem_ball_self one_pos⟩
  set Np : Ω → ℕ := fun ω => if ω ∈ G then Nf ω else k₀ with hNpdef
  have hNp : Measurable Np := Measurable.ite hGm hNf measurable_const
  -- on `G` the selected point lies in the change pocket
  have hGB : ∀ ω ∈ G, e (Nf ω) ∈ changePocket (R ω) (L ω) r := by
    intro ω hω
    have hne : ∃ j, ω ∈ B j := by
      obtain ⟨hO, hC, -⟩ := (hG ω hω).isOpen_isConnected_isSimplyConnected
      obtain ⟨j, hj⟩ := he.exists_mem_open hO hC.nonempty
      exact ⟨j, hω, (mem_changePocket_iff hG hω _).1 hj⟩
    have hspec : ω ∈ B (Nf ω) := by
      rcases Nat.find_spec (hp ω) with h | h
      · exact h
      · obtain ⟨j, hj⟩ := hne
        exact absurd hj (h j)
    exact (mem_changePocket_iff hG hω _).2 hspec.2
  -- the random open domain, through walls continuous for every `ω`
  set R' : Ω → ℝ≥0 → ℂ := fun ω => if ω ∈ G then R ω else fun _ => 0 with hR'def
  set L' : Ω → ℝ≥0 → ℂ := fun ω => if ω ∈ G then L ω else fun _ => 0 with hL'def
  have hR'c : ∀ ω, Continuous (R' ω) := fun ω => by
    by_cases hω : ω ∈ G
    · simp only [hR'def, hω, ↓reduceIte]; exact (hG ω hω).right.1
    · simp only [hR'def, hω, ↓reduceIte]; exact continuous_const
  have hL'c : ∀ ω, Continuous (L' ω) := fun ω => by
    by_cases hω : ω ∈ G
    · simp only [hL'def, hω, ↓reduceIte]; exact (hG ω hω).left.1
    · simp only [hL'def, hω, ↓reduceIte]; exact continuous_const
  have hR'm : ∀ t, Measurable fun ω => R' ω t := fun t => by
    have : (fun ω => R' ω t) = fun ω => if ω ∈ G then R ω t else 0 := by
      ext ω; by_cases hω : ω ∈ G <;> simp [hR'def, hω]
    rw [this]; exact Measurable.ite hGm (hRm t) measurable_const
  have hL'm : ∀ t, Measurable fun ω => L' ω t := fun t => by
    have : (fun ω => L' ω t) = fun ω => if ω ∈ G then L ω t else 0 := by
      ext ω; by_cases hω : ω ∈ G <;> simp [hL'def, hω]
    rw [this]; exact Measurable.ite hGm (hLm t) measurable_const
  set U : Ω → Set ℂ := fun ω => if ω ∈ G then H \ (range (R ω) ∪ range (L ω)) else univ with hUdef
  have hUo : ∀ ω, IsOpen (U ω) := fun ω => by
    by_cases hω : ω ∈ G
    · simp only [hUdef, hω, ↓reduceIte]
      exact QuantumZipper.isOpen_H.sdiff ((Lemma71Pin.IsSimpleProper.isClosed_range (hG ω hω).right).union
        (Lemma71Pin.IsSimpleProper.isClosed_range (hG ω hω).left))
    · simp only [hUdef, hω, ↓reduceIte]
      exact isOpen_univ
  have hUm : ∀ (c : ℂ) (ρ : ℝ), MeasurableSet {ω | closedBall c ρ ⊆ U ω} := by
    intro c ρ
    have e' : {ω | closedBall c ρ ⊆ U ω} =
        (G ∩ {ω | closedBall c ρ ⊆ H \ (range (R' ω) ∪ range (L' ω))}) ∪ Gᶜ := by
      ext ω
      by_cases hω : ω ∈ G <;> simp [hUdef, hR'def, hL'def, hω]
    rw [e']
    exact (hGm.inter (measurableSet_closedBall_subset_diff hR'c hL'c hR'm hL'm c ρ)).union hGm.compl
  have hpU : ∀ ω, e (Np ω) ∈ U ω := fun ω => by
    by_cases hω : ω ∈ G
    · simp only [hUdef, hNpdef, hω, ↓reduceIte]
      exact (hG ω hω).changePocket_subset (hGB ω hω)
    · simp only [hUdef, hω, ↓reduceIte, mem_univ]
  set C : Ω → Set ℂ := fun ω => if ω ∈ G then connectedComponentIn (U ω) (e (Np ω)) else
    Lemma71Pin.defaultPocket with hCdef
  have hCG : ∀ ω ∈ G, C ω = changePocket (R ω) (L ω) r := by
    intro ω hω
    obtain ⟨z, -, hz, -⟩ := (hG ω hω).changePocket_eq
    have hmem := hGB ω hω
    rw [hz] at hmem ⊢
    simp only [hCdef, hUdef, hNpdef, hω, ↓reduceIte]
    exact (connectedComponentIn_eq hmem).symm
  refine ⟨C, Np, hNp, fun ω => ?_, fun c ρ => ?_, fun ω => ?_, hCG, fun ω hω => ?_⟩
  · by_cases hω : ω ∈ G
    · rw [hCG ω hω]
      obtain ⟨h1, h2, h3⟩ := (hG ω hω).isOpen_isConnected_isSimplyConnected
      exact ⟨h1, h2, h3, fun z hz => ((hG ω hω).changePocket_subset hz).1⟩
    · simp only [hCdef, hω, ↓reduceIte]
      exact ⟨isOpen_ball, Lemma71Pin.isConnected_defaultPocket, isSimplyConnected_ball _ one_pos,
        Lemma71Pin.defaultPocket_subset_H⟩
  · have hc := Lemma71E.measurableSet_closedBall_subset_component hUo hUm hNp hpU c ρ
    have e' : {ω | closedBall c ρ ⊆ C ω} =
        (G ∩ {ω | closedBall c ρ ⊆ connectedComponentIn (U ω) (e (Np ω))}) ∪
          (Gᶜ ∩ {_ω | closedBall c ρ ⊆ Lemma71Pin.defaultPocket}) := by
      ext ω
      by_cases hω : ω ∈ G <;> simp [hCdef, hω]
    rw [e']
    exact (hGm.inter hc).union (hGm.compl.inter (MeasurableSet.const _))
  · by_cases hω : ω ∈ G
    · simp only [hCdef, hω, ↓reduceIte]
      exact mem_connectedComponentIn (hpU ω)
    · simp only [hCdef, hNpdef, hω, ↓reduceIte]
      exact hk₀
  · simp only [hCdef, hω, ↓reduceIte]

end Random

end InteractingSLE.Sec7.PocketCoord
