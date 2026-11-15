/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.Lemma71JPocket
import InteractingSLE.Spec.Sec7.Aux130
import InteractingSLE.WangWu.ChamberArcs

/-!
# Aux. lemma 130's selected Jordan pocket as a random object: the change pocket

Packet PROVE-STRIPSYS8, item 1 of `planning/handoffs/PROVE-STRIPSYS6.md` §5 ("Aux. 130's selected Jordan pocket, as
random objects"). Specification §7.4.1, Aux. lemma 130 and its proof (`source/spec/p385-432.md` L401–L489,
pp. 408–413): "The gap in the second path's contact set containing its change point has `y₀` as its upper endpoint.
Its lower endpoint `x₀` and the corresponding gap of the first path give exactly the Jordan pocket asserted there. In
particular the second change lies strictly inside its selected open arc […] The event and the selected component are
measurable from their complete labeled incoming paths alone."

The incoming paths are a right wall `R` (the first path `α` of (RS13.1)) and a left wall `L` (the second path
`β^{(r)}`), simple proper curves of `ℍ` from the common flow seed `0` to the counterflow seed `∞`, `L` avoiding the
right side of `R`, with the change point `L r` (`r > 0`) off `R`. The **change pocket** is the component between the
walls whose closure contains `L r`.

## Main results

* Disc form (crosscuts `α` lower, `β` upper), under the **increasing contact order** of the source (`hjm`; "Their
  common-contact order is increasing, by their reverse containment in the same counterflow"; global order is not
  needed):
  * `strictMonoOn_contactMap_of_firstVisit`: the increasing contact order from reverse first-visit order;
  * `isContactGap_swap`: a contact gap read in the parameters of `β` is a contact gap in the parameters of `α`;
  * `contactMap_lt_contactMap`, `notMem_pocketContactSet_of_mem_Ioo`: the `β`-parameters of a gap `(u, v)` form an
    interval `(j u, j v)` free of contacts;
  * `pocket_props_of_strictMono`: Aux. lemma 33 in the disc (WangWu's `pocket_props` without its order hypothesis);
  * `exists_isContactGap_mem_Ioo`, `isContactGap_eq_of_mem_Ioo`, `mem_Ioo_of_mem_closure_pocket`: the gap whose
    `β`-arc contains a non-contact parameter `c` exists, is unique, and is the only one whose pocket has `β c` in its
    closure;
  * `pocket_subset_crossSide` (globally ordered crosscuts): the pocket lies above `α` and below `β`.
* Half-plane form for globally ordered walls (`IsChangeConfig`): **`existsUnique_changePocket`** (the change pocket
  exists and is the unique component between the walls with the change point in its closure), `changePocket_cayley`
  (its Cayley image is the pocket of the gap containing the change parameter), `mem_changePocket_iff` (a countable
  membership test), **`changePocket_closing_after`** (on `F_r` the pocket closes after the first change of the right
  wall, (RS13.5)).
* **`exists_measurable_changePocket`**: for random walls continuous for every `ω` with measurable coordinates and a
  measurable event on which the configuration holds, a random open simply connected `C ω ⊆ ℍ` observed through closed
  balls, through a measurably selected rational point, which is the change pocket on the event.

The general case (increasing contact order only, the walls may cross after the pocket) is in
`PocketCoordJordan.lean` (deterministic) and `PocketCoordMeas.lean` (random).
-/

set_option autoImplicit false

noncomputable section

open Set Metric Filter Topology Complex Bornology Function
open QuantumZipper (H Hbar)
open QuantumZipper.CA (cayley cayleyInv)
open scoped NNReal

namespace InteractingSLE.Sec7.PocketCoord

open WangWu

/-! ### Contact gaps of two ordered crosscuts -/

section Disc

variable {α β : ℝ → ℂ}

/-- **A gap of the contacts read in the upper crosscut is a gap read in the lower one.** For crosscuts `α` (lower)
and `β` (upper, avoiding the lower side of `α`), a gap `(a, b)` of the parameters of `β` at which `β` meets `α`
corresponds, through the contact map `β ↦ α`, to a gap `(u, v)` of the parameters of `α`, with `j u = a`, `j v = b`
for the contact map `j = contactMap α β`. -/
theorem isContactGap_swap (hα : IsDiscCrosscut α) (hβ : IsDiscCrosscut β)
    (hjm : StrictMonoOn (contactMap α β) (Sec7.pocketContactSet α β)) {a b : ℝ} (hg : IsContactGap β α a b) :
    IsContactGap α β (contactMap β α a) (contactMap β α b) ∧
      contactMap α β (contactMap β α a) = a ∧ contactMap α β (contactMap β α b) = b := by
  obtain ⟨ha, hb, hab, hgap⟩ := hg
  obtain ⟨hu, hαu⟩ := contactMap_mem hα ha
  obtain ⟨hv, hαv⟩ := contactMap_mem hα hb
  set u := contactMap β α a
  set v := contactMap β α b
  have hu' : u ∈ Sec7.pocketContactSet α β := ⟨hu, a, ha.1, hαu.symm⟩
  have hv' : v ∈ Sec7.pocketContactSet α β := ⟨hv, b, hb.1, hαv.symm⟩
  have hju : contactMap α β u = a := contactMap_eq hβ ha.1 hαu
  have hjv : contactMap α β v = b := contactMap_eq hβ hb.1 hαv
  have hmono := hjm
  refine ⟨⟨hu', hv', ?_, fun s hs hsC => ?_⟩, hju, hjv⟩
  · by_contra h
    rcases eq_or_lt_of_le (not_lt.1 h) with h' | h'
    · rw [← h', hjv] at hju
      exact hab.ne hju.symm
    · have := hmono hv' hu' h'
      rw [hju, hjv] at this
      exact lt_asymm hab this
  · have h1 := hmono hu' hsC hs.1
    have h2 := hmono hsC hv' hs.2
    rw [hju] at h1
    rw [hjv] at h2
    obtain ⟨hjs, hβjs⟩ := contactMap_mem hβ hsC
    exact hgap _ ⟨h1, h2⟩ ⟨hjs, s, hsC.1, hβjs.symm⟩

/-- **Increasing contact order from reverse first visits** (proof of Aux. lemma 130, p. 412: "Their common-contact
order is increasing, by their reverse containment in the same counterflow"; p. 410: "Distinct points of an incoming
path have strictly decreasing `T` in its incoming order"): if a first-visit function `T` is strictly decreasing along
`α` and nonincreasing along `β` on `[0, 1]`, the contact map of `α` and `β` is strictly increasing. -/
theorem strictMonoOn_contactMap_of_firstVisit {X : Type*} [LinearOrder X] (hβ : IsDiscCrosscut β) {T : ℂ → X}
    (hα : StrictAntiOn (fun s => T (α s)) (Icc 0 1)) (hβT : AntitoneOn (fun s => T (β s)) (Icc 0 1)) :
    StrictMonoOn (contactMap α β) (Sec7.pocketContactSet α β) := by
  intro s hs s' hs' hss'
  obtain ⟨hj, hβj⟩ := contactMap_mem hβ hs
  obtain ⟨hj', hβj'⟩ := contactMap_mem hβ hs'
  by_contra h
  push Not at h
  have h1 := hβT hj' hj h
  simp only [hβj, hβj'] at h1
  exact absurd (hα hs.1 hs'.1 hss') (not_lt.2 h1)

/-- The contact map is monotone on the contact set. -/
theorem contactMap_le_contactMap
    (hjm : StrictMonoOn (contactMap α β) (Sec7.pocketContactSet α β)) {s s' : ℝ} (hs : s ∈ Sec7.pocketContactSet α β)
    (hs' : s' ∈ Sec7.pocketContactSet α β) (h : s ≤ s') : contactMap α β s ≤ contactMap α β s' := by
  rcases eq_or_lt_of_le h with h | h
  · rw [h]
  · exact (hjm hs hs' h).le

/-- The `β`-parameters of the ends of a gap are in order. -/
theorem contactMap_lt_contactMap
    (hjm : StrictMonoOn (contactMap α β) (Sec7.pocketContactSet α β)) {u v : ℝ} (hg : IsContactGap α β u v) :
    contactMap α β u < contactMap α β v :=
  hjm hg.1 hg.2.1 hg.2.2.1

/-- **The `β`-arc of a pocket is free of contacts**: a parameter of `β` strictly between the `β`-parameters of the
ends of a gap is not a contact parameter. -/
theorem notMem_pocketContactSet_of_mem_Ioo (hα : IsDiscCrosscut α) (hβ : IsDiscCrosscut β)
    (hjm : StrictMonoOn (contactMap α β) (Sec7.pocketContactSet α β)) {u v : ℝ} (hg : IsContactGap α β u v) {s' : ℝ}
    (hs' : s' ∈ Ioo (contactMap α β u) (contactMap α β v)) : s' ∉ Sec7.pocketContactSet β α := by
  intro hC
  obtain ⟨hs, hαs⟩ := contactMap_mem hα hC
  set s := contactMap β α s'
  have hsC : s ∈ Sec7.pocketContactSet α β := ⟨hs, s', hC.1, hαs.symm⟩
  have hjs : contactMap α β s = s' := contactMap_eq hβ hC.1 hαs
  obtain ⟨hu, hv, -, hgap⟩ := hg
  rcases lt_or_ge u s with hus | hsu
  · rcases lt_or_ge s v with hsv | hvs
    · exact hgap s ⟨hus, hsv⟩ hsC
    · have := contactMap_le_contactMap hjm hv hsC hvs
      rw [hjs] at this
      exact absurd hs'.2 (not_lt.2 this)
  · have := contactMap_le_contactMap hjm hsC hu hsu
    rw [hjs] at this
    exact absurd hs'.1 (not_lt.2 this)

/-- The `β`-parameters of a gap lie in `[0, 1]`. -/
theorem contactMap_mem_Icc (hβ : IsDiscCrosscut β) {u v : ℝ} (hg : IsContactGap α β u v) :
    contactMap α β u ∈ Icc (0 : ℝ) 1 ∧ contactMap α β v ∈ Icc (0 : ℝ) 1 :=
  ⟨(contactMap_mem hβ hg.1).1, (contactMap_mem hβ hg.2.1).1⟩

/-- **Aux. lemma 33 in the disc under increasing contact order** (WangWu's `pocket_props` with its order hypothesis
replaced by what its proof uses, the increasing contact order; specification, proof of Aux. lemma 130, p. 412: "Their
common-contact order is increasing, by their reverse containment in the same counterflow […] This argument does not
require the two complete paths to be globally ordered"): the pocket of a gap is the inside of a Jordan curve, lies in
the disc off both crosscuts, has frontier `α[u, v] ∪ β[j u, j v]`, and is a component of `𝔻 \ (α ∪ β)`. -/
theorem pocket_props_of_strictMono (hα : IsDiscCrosscut α) (hβ : IsDiscCrosscut β)
    (hjm : StrictMonoOn (contactMap α β) (Sec7.pocketContactSet α β)) {a b : ℝ} (hg : IsContactGap α β a b) :
    LQGMetric.JordanMap.IsJordanCurve (pocketCurve α β a b) ∧
      jordanIn (pocketCurve α β a b) ⊆ ball 0 1 ∧
      Disjoint (jordanIn (pocketCurve α β a b)) (crossRange α ∪ crossRange β) ∧
      frontier (jordanIn (pocketCurve α β a b)) = pocketCurve α β a b ∧
      ∃ w ∈ jordanIn (pocketCurve α β a b),
        connectedComponentIn (ball 0 1 \ (crossRange α ∪ crossRange β)) w = jordanIn (pocketCurve α β a b) := by
  obtain ⟨ha, hb, hab, hgap⟩ := hg
  have h0 : (0 : ℂ) ∈ (sphere (0 : ℂ) 1)ᶜ := by simp
  have hD := connectedComponentIn_compl_sphere
  have hDb : IsBounded (connectedComponentIn (sphere (0 : ℂ) 1)ᶜ 0) := by rw [hD]; exact isBounded_ball
  obtain ⟨hJ, U, ⟨x₁, hx₁, rfl⟩, -, hUb, -, hUD, hUfr, hUαβ, w, hwU, hwc⟩ :=
    Sec7.aux33_pocket_of_isJordanCurve isJordanCurve_sphere h0 hDb hα.cont hβ.cont hα.inj hβ.inj
      (by rw [hα.zero, hβ.zero]) (by rw [hα.one, hβ.one])
      (by rw [hα.zero, mem_sphere_zero_iff_norm]; simp) (by rw [hα.one, mem_sphere_zero_iff_norm]; simp)
      (fun s hs => by rw [hD]; exact hα.mem_disc s hs) (fun s hs => by rw [hD]; exact hβ.mem_disc s hs)
      (fun s _ r hr h => contactMap_eq hβ hr h) hjm ha hb hab hgap
  have hU := connectedComponentIn_eq_jordanIn hJ hx₁ hUb
  rw [hD] at hUD hwc
  refine ⟨hJ, hU ▸ hUD, hU ▸ hUαβ, hU ▸ hUfr, w, hU ▸ hwU, hU ▸ hwc⟩

/-- `β` at a parameter strictly inside the `β`-arc of a gap is a point of the open disc off `α`. -/
theorem mem_ball_notMem_of_mem_Ioo (hα : IsDiscCrosscut α) (hβ : IsDiscCrosscut β)
    (hjm : StrictMonoOn (contactMap α β) (Sec7.pocketContactSet α β)) {u v : ℝ} (hg : IsContactGap α β u v) {s' : ℝ}
    (hs' : s' ∈ Ioo (contactMap α β u) (contactMap α β v)) :
    β s' ∈ ball (0 : ℂ) 1 ∧ β s' ∉ crossRange α := by
  obtain ⟨hju, hjv⟩ := contactMap_mem_Icc hβ hg
  have hs01 : s' ∈ Icc (0 : ℝ) 1 := ⟨hju.1.trans hs'.1.le, hs'.2.le.trans hjv.2⟩
  refine ⟨hβ.mem_disc s' ⟨hju.1.trans_lt hs'.1, hs'.2.trans_le hjv.2⟩, fun h => ?_⟩
  exact notMem_pocketContactSet_of_mem_Ioo hα hβ hjm hg hs' ⟨hs01, h⟩

/-- The `β`-arc of a gap lies in the frontier of its pocket. -/
theorem image_subset_frontier_pocket (hα : IsDiscCrosscut α) (hβ : IsDiscCrosscut β)
    (hjm : StrictMonoOn (contactMap α β) (Sec7.pocketContactSet α β)) {u v : ℝ} (hg : IsContactGap α β u v) :
    β '' Icc (contactMap α β u) (contactMap α β v) ⊆ frontier (jordanIn (pocketCurve α β u v)) := by
  rw [(pocket_props_of_strictMono hα hβ hjm hg).2.2.2.1]
  exact subset_union_right

/-- The `α`-arc of a gap lies in the frontier of its pocket. -/
theorem image_subset_frontier_pocket_left (hα : IsDiscCrosscut α) (hβ : IsDiscCrosscut β)
    (hjm : StrictMonoOn (contactMap α β) (Sec7.pocketContactSet α β)) {u v : ℝ} (hg : IsContactGap α β u v) :
    α '' Icc u v ⊆ frontier (jordanIn (pocketCurve α β u v)) := by
  rw [(pocket_props_of_strictMono hα hβ hjm hg).2.2.2.1]
  exact subset_union_left

/-- An open set containing a point of the closure of `S` meets `S`. -/
theorem inter_nonempty_of_mem_closure {S U : Set ℂ} (hU : IsOpen U) {x : ℂ} (hxU : x ∈ U) (hx : x ∈ closure S) :
    (S ∩ U).Nonempty := by
  obtain ⟨y, hyU, hyS⟩ := mem_closure_iff.1 hx U hU hxU
  exact ⟨y, hyS, hyU⟩

/-- **The pocket of a gap lies above the lower crosscut and below the upper one.** -/
theorem pocket_subset_crossSide (hα : IsDiscCrosscut α) (hβ : IsDiscCrosscut β)
    (hord : Disjoint (crossRange β) (crossSide α (-1))) {u v : ℝ} (hg : IsContactGap α β u v) :
    jordanIn (pocketCurve α β u v) ⊆ crossSide α 1 ∩ crossSide β (-1) := by
  obtain ⟨-, hPball, hPdisj, hPfr, w, -, hPcc⟩ := pocket_props hα hβ hord hg
  set P := jordanIn (pocketCurve α β u v)
  have hPpc : IsPreconnected P := by rw [← hPcc]; exact isPreconnected_connectedComponentIn
  have hPα : P ⊆ ball 0 1 \ crossRange α := fun z hz =>
    ⟨hPball hz, fun h => Set.disjoint_left.1 hPdisj hz (Or.inl h)⟩
  have hPβ : P ⊆ ball 0 1 \ crossRange β := fun z hz =>
    ⟨hPball hz, fun h => Set.disjoint_left.1 hPdisj hz (Or.inr h)⟩
  have hfrcl : frontier P ⊆ closure P := frontier_subset_closure
  -- a point of the `β`-arc lies above `α`
  have hlt := contactMap_lt_contactMap (strictMonoOn_contactMap hα hβ hord) hg
  obtain ⟨s', hs'⟩ := exists_between hlt
  obtain ⟨hβball, hβα⟩ := mem_ball_notMem_of_mem_Ioo hα hβ (strictMonoOn_contactMap hα hβ hord) hg hs'
  have hβs : β s' ∈ crossSide α 1 :=
    hα.mem_crossSide_one_of hβball hβα fun h => Set.disjoint_left.1 hord ⟨s', ⟨(contactMap_mem_Icc hβ hg).1.1.trans
      hs'.1.le, hs'.2.le.trans (contactMap_mem_Icc hβ hg).2.2⟩, rfl⟩ h
  have hβcl : β s' ∈ closure P :=
    hfrcl (image_subset_frontier_pocket hα hβ (strictMonoOn_contactMap hα hβ hord) hg ⟨s', ⟨hs'.1.le, hs'.2.le⟩, rfl⟩)
  -- a point of the `α`-arc lies below `β`
  obtain ⟨hu, hv, huv, hgap⟩ := hg
  obtain ⟨s, hs⟩ := exists_between huv
  have hs01 : s ∈ Ioo (0 : ℝ) 1 := ⟨hu.1.1.trans_lt hs.1, hs.2.trans_le hv.1.2⟩
  have hαball : α s ∈ ball (0 : ℂ) 1 := hα.mem_disc s hs01
  have hαβ : α s ∉ crossRange β := fun h => hgap s hs ⟨⟨hs01.1.le, hs01.2.le⟩, h⟩
  have hαs : α s ∈ crossSide β (-1) := by
    rcases hβ.subset_crossSide_union ⟨hαball, hαβ⟩ with h | h
    · exact absurd h (Set.disjoint_left.1 (IsDiscCrosscut.disjoint_crossRange_crossSide_swap hα hβ hord)
        ⟨s, ⟨hs01.1.le, hs01.2.le⟩, rfl⟩)
    · exact h
  have hαcl : α s ∈ closure P :=
    hfrcl (image_subset_frontier_pocket_left hα hβ (strictMonoOn_contactMap hα hβ hord) ⟨hu, hv, huv, hgap⟩
      ⟨s, ⟨hs.1.le, hs.2.le⟩, rfl⟩)
  refine fun z hz => ⟨?_, ?_⟩
  · exact hα.subset_crossSide_of_isPreconnected (Or.inl rfl) hPpc hPα
      (inter_nonempty_of_mem_closure (hα.isOpen_crossSide (Or.inl rfl)) hβs hβcl) hz
  · exact hβ.subset_crossSide_of_isPreconnected (Or.inr rfl) hPpc hPβ
      (inter_nonempty_of_mem_closure (hβ.isOpen_crossSide (Or.inr rfl)) hαs hαcl) hz

/-- **The gap whose `β`-arc contains a given non-contact parameter** (Aux. lemma 130's proof, p. 412: "The gap in
the second path's contact set containing its change point"): it exists, read in the parameters of `α`. -/
theorem exists_isContactGap_mem_Ioo (hα : IsDiscCrosscut α) (hβ : IsDiscCrosscut β)
    (hjm : StrictMonoOn (contactMap α β) (Sec7.pocketContactSet α β)) {c : ℝ} (hc : c ∈ Icc (0 : ℝ) 1)
    (hcα : β c ∉ crossRange α) :
    ∃ u v, IsContactGap α β u v ∧ c ∈ Ioo (contactMap α β u) (contactMap α β v) := by
  have hcS : c ∉ Sec7.pocketContactSet β α := fun h => hcα h.2
  obtain ⟨a, b, hg, hcab⟩ := Aux130.exists_isContactGap_of_notMem hβ hα hc hcS
  obtain ⟨hg', hja, hjb⟩ := isContactGap_swap hα hβ hjm hg
  exact ⟨_, _, hg', by rw [hja, hjb]; exact hcab⟩

/-- **Uniqueness of that gap**: two gaps whose `β`-arcs contain a common parameter coincide. -/
theorem isContactGap_eq_of_mem_Ioo
    (hjm : StrictMonoOn (contactMap α β) (Sec7.pocketContactSet α β)) {u v u' v' c : ℝ} (hg : IsContactGap α β u v)
    (hg' : IsContactGap α β u' v') (hc : c ∈ Ioo (contactMap α β u) (contactMap α β v))
    (hc' : c ∈ Ioo (contactMap α β u') (contactMap α β v')) : u = u' ∧ v = v' := by
  -- a contact end of one gap cannot lie strictly inside the other
  have key : ∀ {u₁ v₁ u₂ v₂ : ℝ}, IsContactGap α β u₁ v₁ → IsContactGap α β u₂ v₂ →
      c ∈ Ioo (contactMap α β u₁) (contactMap α β v₁) → c ∈ Ioo (contactMap α β u₂) (contactMap α β v₂) →
      u₁ ≤ u₂ ∧ v₂ ≤ v₁ := by
    intro u₁ v₁ u₂ v₂ h₁ h₂ hc₁ hc₂
    constructor
    · by_contra h
      push Not at h
      -- `u₁ ∈ (u₂, v₂)`
      have hlt : u₁ < v₂ := by
        by_contra h'
        push Not at h'
        have := contactMap_le_contactMap hjm h₂.2.1 h₁.1 h'
        exact absurd (hc₁.1.trans hc₂.2) (not_lt.2 this)
      exact h₂.2.2.2 u₁ ⟨h, hlt⟩ h₁.1
    · by_contra h
      push Not at h
      -- `v₁ ∈ (u₂, v₂)`
      have hlt : u₂ < v₁ := by
        by_contra h'
        push Not at h'
        have := contactMap_le_contactMap hjm h₁.2.1 h₂.1 h'
        exact absurd (hc₂.1.trans hc₁.2) (not_lt.2 this)
      exact h₂.2.2.2 v₁ ⟨hlt, h⟩ h₁.2.1
  obtain ⟨h1, h2⟩ := key hg hg' hc hc'
  obtain ⟨h3, h4⟩ := key hg' hg hc' hc
  exact ⟨le_antisymm h1 h3, le_antisymm h4 h2⟩

/-- **Only the pocket of the gap containing `c` has `β c` in its closure.** If `β c` is off `α` and lies in the
closure of the pocket of a gap `(u, v)`, then `c` is strictly inside the `β`-arc of that gap. -/
theorem mem_Ioo_of_mem_closure_pocket (hα : IsDiscCrosscut α) (hβ : IsDiscCrosscut β)
    (hjm : StrictMonoOn (contactMap α β) (Sec7.pocketContactSet α β)) {u v : ℝ} (hg : IsContactGap α β u v) {c : ℝ}
    (hc : c ∈ Icc (0 : ℝ) 1) (hcα : β c ∉ crossRange α)
    (hcl : β c ∈ closure (jordanIn (pocketCurve α β u v))) :
    c ∈ Ioo (contactMap α β u) (contactMap α β v) := by
  obtain ⟨hJ, -, hPdisj, hPfr, w, -, hPcc⟩ := pocket_props_of_strictMono hα hβ hjm hg
  have hPo : IsOpen (jordanIn (pocketCurve α β u v)) := by
    rw [← hPcc]
    exact (isOpen_ball.sdiff (hα.isCompact_crossRange.union hβ.isCompact_crossRange).isClosed).connectedComponentIn
  have hcP : β c ∉ jordanIn (pocketCurve α β u v) :=
    fun h => Set.disjoint_left.1 hPdisj h (Or.inr ⟨c, hc, rfl⟩)
  have hfr : β c ∈ frontier (jordanIn (pocketCurve α β u v)) := ⟨hcl, by rwa [hPo.interior_eq]⟩
  rw [hPfr] at hfr
  obtain ⟨hju, hjv⟩ := contactMap_mem_Icc hβ hg
  rcases hfr with ⟨s, hs, hsc⟩ | ⟨s, hs, hsc⟩
  · exact absurd ⟨s, ⟨hg.1.1.1.trans hs.1, hs.2.trans hg.2.1.1.2⟩, hsc⟩ hcα
  · have hs01 : s ∈ Icc (0 : ℝ) 1 := ⟨hju.1.trans hs.1, hs.2.trans hjv.2⟩
    have hsc' : s = c := hβ.inj hs01 hc hsc
    subst hsc'
    refine ⟨lt_of_le_of_ne hs.1 fun h => hcα ?_, lt_of_le_of_ne hs.2 fun h => hcα ?_⟩
    · rw [← h, (contactMap_mem hβ hg.1).2]
      exact ⟨u, hg.1.1, rfl⟩
    · rw [h, (contactMap_mem hβ hg.2.1).2]
      exact ⟨v, hg.2.1.1, rfl⟩

end Disc

/-! ### The change pocket in the half-plane -/

section HalfPlane

open Lemma71I

/-- **The pathwise configuration of Aux. lemma 130's walls with a change point** (p. 412): the right wall `R` (the
first path `α`) and the left wall `L` (the second path `β^{(r)}`) are simple proper curves of `ℍ` from `0` to `∞`,
`L` avoids the right side of `R` (reverse containment in the same counterflow orders the two paths), the change time
`r` is positive, and the change point `L r` is off `R` (the event `F_r`: "the second change point is off the first
path"). -/
structure IsChangeConfig (R L : ℝ≥0 → ℂ) (r : ℝ≥0) : Prop where
  right : IsSimpleProper R
  left : IsSimpleProper L
  ord : Disjoint (range L) (rightSideOf (range R))
  pos : 0 < r
  off : L r ∉ range R

variable {R L : ℝ≥0 → ℂ} {r : ℝ≥0}

theorem toDisc_realPath_discTime (L : ℝ≥0 → ℂ) (r : ℝ≥0) :
    toDisc (realPath L) (discTime r) = cayley (L r) := by
  rw [toDisc_discTime _ r.coe_nonneg, realPath_coe]

theorem discTime_mem_Icc (r : ℝ≥0) : discTime r ∈ Icc (0 : ℝ) 1 :=
  ⟨(discTime_mem_Ico r.coe_nonneg).1, (discTime_mem_Ico r.coe_nonneg).2.le⟩

namespace IsChangeConfig

theorem isDiscCrosscut_right (h : IsChangeConfig R L r) : IsDiscCrosscut (toDisc (realPath R)) :=
  h.right.isProperArc.isDiscCrosscut_toDisc

theorem isDiscCrosscut_left (h : IsChangeConfig R L r) : IsDiscCrosscut (toDisc (realPath L)) :=
  h.left.isProperArc.isDiscCrosscut_toDisc

theorem ord_arc (h : IsChangeConfig R L r) :
    Disjoint (arcRange (realPath L)) (rightSideOf (arcRange (realPath R))) := by
  rw [arcRange_realPath, arcRange_realPath]
  exact h.ord

theorem ord_disc (h : IsChangeConfig R L r) :
    Disjoint (crossRange (toDisc (realPath L))) (crossSide (toDisc (realPath R)) (-1)) :=
  (disjoint_rightSideOf_iff h.right.isProperArc h.left.isProperArc).1 h.ord_arc

theorem mem_H (h : IsChangeConfig R L r) : L r ∈ H := h.left.2.2.2.1 r h.pos

/-- The contacts of the walls occur in the same order. -/
theorem strictMono (h : IsChangeConfig R L r) :
    StrictMonoOn (contactMap (toDisc (realPath R)) (toDisc (realPath L)))
      (Sec7.pocketContactSet (toDisc (realPath R)) (toDisc (realPath L))) :=
  strictMonoOn_contactMap h.isDiscCrosscut_right h.isDiscCrosscut_left h.ord_disc

theorem mem_Hbar (h : IsChangeConfig R L r) : L r ∈ Hbar := le_of_lt (show (0 : ℝ) < (L r).im from h.mem_H)

/-- The change point in the disc is off the right crosscut. -/
theorem notMem_crossRange (h : IsChangeConfig R L r) :
    toDisc (realPath L) (discTime r) ∉ crossRange (toDisc (realPath R)) := by
  rw [toDisc_realPath_discTime, h.right.isProperArc.cayley_mem_crossRange_iff h.mem_Hbar, arcRange_realPath]
  exact h.off

/-- A component between the walls lies in `ℍ`. -/
theorem subset_H_of_mem_betweenComponents {A B C : Set ℂ} (hC : C ∈ betweenComponents A B) : C ⊆ H := by
  obtain ⟨z, -, -, -, rfl⟩ := hC
  exact (connectedComponentIn_subset _ _).trans sdiff_subset

/-- **The Cayley image of a change pocket** is the pocket of the gap whose `L`-arc contains the change parameter. -/
theorem changePocket_cayley (h : IsChangeConfig R L r) {C : Set ℂ}
    (hC : C ∈ betweenComponents (range R) (range L)) (hcl : L r ∈ closure C) :
    ∃ u v, IsContactGap (toDisc (realPath R)) (toDisc (realPath L)) u v ∧
      discTime r ∈ Ioo (contactMap (toDisc (realPath R)) (toDisc (realPath L)) u)
        (contactMap (toDisc (realPath R)) (toDisc (realPath L)) v) ∧
      cayley '' C = jordanIn (pocketCurve (toDisc (realPath R)) (toDisc (realPath L)) u v) := by
  have hC' : C ∈ betweenComponents (arcRange (realPath R)) (arcRange (realPath L)) := by
    rwa [arcRange_realPath, arcRange_realPath]
  obtain ⟨u, v, hg, hCeq⟩ :=
    exists_contactGap_of_mem_betweenComponents h.right.isProperArc h.left.isProperArc h.ord_arc hC'
  refine ⟨u, v, hg, mem_Ioo_of_mem_closure_pocket h.isDiscCrosscut_right h.isDiscCrosscut_left h.strictMono hg
    (discTime_mem_Icc r) h.notMem_crossRange ?_, hCeq⟩
  rw [← hCeq, toDisc_realPath_discTime]
  exact mem_closure_image (continuousAt_cayley_of_mem_Hbar h.mem_Hbar) hcl

/-- **The change pocket exists** (Aux. lemma 130's proof, p. 412). -/
theorem exists_changePocket (h : IsChangeConfig R L r) :
    ∃ C ∈ betweenComponents (range R) (range L), L r ∈ closure C := by
  have hα := h.isDiscCrosscut_right
  have hβ := h.isDiscCrosscut_left
  have hord := h.ord_disc
  obtain ⟨u, v, hg, hc⟩ := exists_isContactGap_mem_Ioo hα hβ h.strictMono (discTime_mem_Icc r) h.notMem_crossRange
  obtain ⟨-, hPball, hPdisj, -, w, hwP, hPcc⟩ := pocket_props hα hβ hord hg
  have hside := pocket_subset_crossSide hα hβ hord hg hwP
  have hwball := hPball hwP
  set z := cayleyInv w
  have hzH : z ∈ H := QuantumZipper.CA.cayleyInv_mem_H hwball
  have hzHbar : z ∈ Hbar := le_of_lt (show (0 : ℝ) < z.im from hzH)
  have hcz : cayley z = w := cayley_cayleyInv_of_mem_ball hwball
  have hzR : z ∉ range R := by
    rw [← arcRange_realPath, ← h.right.isProperArc.cayley_mem_crossRange_iff hzHbar, hcz]
    exact fun h' => Set.disjoint_left.1 hPdisj hwP (Or.inl h')
  have hzL : z ∉ range L := by
    rw [← arcRange_realPath, ← h.left.isProperArc.cayley_mem_crossRange_iff hzHbar, hcz]
    exact fun h' => Set.disjoint_left.1 hPdisj hwP (Or.inr h')
  have hzU : z ∈ H \ (range R ∪ range L) := ⟨hzH, fun h' => h'.elim hzR hzL⟩
  have hzright : z ∉ rightSideOf (range R) := by
    rw [← arcRange_realPath, h.right.isProperArc.mem_rightSideOf_iff hzH, hcz]
    exact fun h' => Set.disjoint_left.1 h.isDiscCrosscut_right.disjoint_crossSide hside.1 h'
  have hzleft : z ∉ leftSideOf (range L) := by
    rw [← arcRange_realPath, h.left.isProperArc.mem_leftSideOf_iff hzH, hcz]
    exact fun h' => Set.disjoint_left.1 h.isDiscCrosscut_left.disjoint_crossSide h' hside.2
  set C := connectedComponentIn (H \ (range R ∪ range L)) z
  have hCeq : cayley '' C = jordanIn (pocketCurve (toDisc (realPath R)) (toDisc (realPath L)) u v) := by
    have himg := image_cayley_H_diff h.right.isProperArc h.left.isProperArc
    rw [arcRange_realPath, arcRange_realPath] at himg
    rw [image_cayley_connectedComponentIn sdiff_subset hzU, himg, hcz, hPcc]
  refine ⟨C, ⟨z, hzU, hzright, hzleft, rfl⟩, ?_⟩
  -- the change point is in the closure
  have hβc : cayley (L r) ∈ closure (cayley '' C) := by
    rw [hCeq, ← toDisc_realPath_discTime]
    exact frontier_subset_closure (image_subset_frontier_pocket hα hβ h.strictMono hg ⟨_, ⟨hc.1.le, hc.2.le⟩, rfl⟩)
  have hne : cayley (L r) ≠ 1 := cayley_ne_one_of_Hbar h.mem_Hbar
  have := mem_closure_image (continuousAt_cayleyInv hne) hβc
  rwa [cayleyInv_cayley_of_mem_Hbar h.mem_Hbar, image_image,
    image_congr (fun y hy => cayleyInv_cayley_of_mem_Hbar
      (le_of_lt (show (0 : ℝ) < y.im from (connectedComponentIn_subset _ _ hy : y ∈ H \ _).1))), image_id'] at this

/-- **The change pocket is unique.** -/
theorem changePocket_unique (h : IsChangeConfig R L r) {C C' : Set ℂ}
    (hC : C ∈ betweenComponents (range R) (range L)) (hcl : L r ∈ closure C)
    (hC' : C' ∈ betweenComponents (range R) (range L)) (hcl' : L r ∈ closure C') : C = C' := by
  obtain ⟨u, v, hg, hc, hCeq⟩ := h.changePocket_cayley hC hcl
  obtain ⟨u', v', hg', hc', hCeq'⟩ := h.changePocket_cayley hC' hcl'
  obtain ⟨rfl, rfl⟩ := isContactGap_eq_of_mem_Ioo h.strictMono hg hg'
    hc hc'
  have hinj : InjOn cayley H := fun z hz w hw hzw =>
    cayley_injOn_Hbar (le_of_lt (show (0 : ℝ) < z.im from hz)) (le_of_lt (show (0 : ℝ) < w.im from hw)) hzw
  exact (hinj.image_eq_image_iff (subset_H_of_mem_betweenComponents hC)
    (subset_H_of_mem_betweenComponents hC')).1 (hCeq.trans hCeq'.symm)

/-- **Aux. lemma 130's change pocket exists and is unique**: exactly one component between the walls has the change
point `L r` in its closure. -/
theorem existsUnique_changePocket (h : IsChangeConfig R L r) :
    ∃! C, C ∈ betweenComponents (range R) (range L) ∧ L r ∈ closure C := by
  obtain ⟨C, hC, hcl⟩ := h.exists_changePocket
  exact ⟨C, ⟨hC, hcl⟩, fun C' hC' => (h.changePocket_unique hC hcl hC'.1 hC'.2).symm⟩

/-- **A countable membership test for the change pocket**: a point lies in it iff it is between the walls and the
change point is in the closure of its component of `ℍ \ (R ∪ L)`. -/
theorem mem_changePocket_iff (h : IsChangeConfig R L r) {C : Set ℂ}
    (hC : C ∈ betweenComponents (range R) (range L)) (hcl : L r ∈ closure C) (z : ℂ) :
    z ∈ C ↔ Lemma71Pin.IsBetweenPt (range R) (range L) z ∧
      L r ∈ closure (connectedComponentIn (H \ (range R ∪ range L)) z) := by
  constructor
  · intro hz
    refine ⟨Lemma71Pin.isBetweenPt_of_mem h.right h.left hC hz, ?_⟩
    obtain ⟨z₀, -, -, -, rfl⟩ := hC
    rwa [← connectedComponentIn_eq hz]
  · rintro ⟨hb, hcl'⟩
    obtain ⟨hzU, hzR, hzL⟩ := (Lemma71Pin.isBetweenPt_iff h.right h.left).1 hb
    have hC' : connectedComponentIn (H \ (range R ∪ range L)) z ∈ betweenComponents (range R) (range L) :=
      ⟨z, hzU, hzR, hzL, rfl⟩
    rw [h.changePocket_unique hC hcl hC' hcl']
    exact mem_connectedComponentIn hzU

/-- **On Aux. lemma 130's event `F_r` the change pocket closes after the first change of the right wall** ((RS13.5),
p. 412: "If `y₀ = α(b)`, reverse first-visit order gives […] hence `b > 1`, with the terminal case `b = ∞` allowed").
`hF` is the contact clause of `F_r` (`StripSys.IsContactPoint` in the half-plane): every visit of `L` after `r` to the
first prefix `R([0, 1])` is preceded, after `r`, by a visit of the range of `R`. Then the gap `(u, v)` of the change
pocket has its closing parameter `v` strictly after the disc parameter `discTime 1` of the first change of `R`. -/
theorem changePocket_closing_after (h : IsChangeConfig R L r)
    (hF : ∀ s : ℝ≥0, r ≤ s → L s ∈ R '' Icc 0 1 → ∃ u : ℝ≥0, r ≤ u ∧ u < s ∧ L u ∈ range R) {C : Set ℂ}
    (hC : C ∈ betweenComponents (range R) (range L)) (hcl : L r ∈ closure C) :
    ∃ u v, IsContactGap (toDisc (realPath R)) (toDisc (realPath L)) u v ∧
      discTime r ∈ Ioo (contactMap (toDisc (realPath R)) (toDisc (realPath L)) u)
        (contactMap (toDisc (realPath R)) (toDisc (realPath L)) v) ∧
      cayley '' C = jordanIn (pocketCurve (toDisc (realPath R)) (toDisc (realPath L)) u v) ∧
      discTime 1 < v := by
  have hα := h.isDiscCrosscut_right
  have hβ := h.isDiscCrosscut_left
  obtain ⟨u, v, hg, hc, hCeq⟩ := h.changePocket_cayley hC hcl
  refine ⟨u, v, hg, hc, hCeq, ?_⟩
  by_contra hv
  push Not at hv
  have hp : discTime 1 < 1 := (discTime_mem_Ico zero_le_one).2
  have hv1 : v < 1 := hv.trans_lt hp
  have hv0 : 0 ≤ v := hg.2.1.1.1
  obtain ⟨hjvI, hβjv⟩ := contactMap_mem hβ hg.2.1
  set jv := contactMap (toDisc (realPath R)) (toDisc (realPath L)) v
  have hjv1 : jv < 1 := by
    refine lt_of_le_of_ne hjvI.2 fun hj => ?_
    rw [hj, hβ.one, ← hα.one] at hβjv
    exact hv1.ne (hα.inj hg.2.1.1 ⟨zero_le_one, le_rfl⟩ hβjv.symm)
  -- the closing point in the half-plane
  set s : ℝ≥0 := (arcTime jv).toNNReal
  set t : ℝ≥0 := (arcTime v).toNNReal
  have hs : ((s : ℝ≥0) : ℝ) = arcTime jv := Real.coe_toNNReal _ (arcTime_nonneg ⟨hjvI.1, hjv1⟩)
  have hLR : L s = R t := by
    have h1 : toDisc (realPath L) jv = cayley (L s) := by rw [toDisc_of_lt hjv1]; rfl
    have h2 : toDisc (realPath R) v = cayley (R t) := by rw [toDisc_of_lt hv1]; rfl
    rw [h1, h2] at hβjv
    have hLs : L s ∈ Hbar := by
      have := h.left.isProperArc.mem_Hbar s.coe_nonneg
      rwa [realPath_coe] at this
    have hRt : R t ∈ Hbar := by
      have := h.right.isProperArc.mem_Hbar t.coe_nonneg
      rwa [realPath_coe] at this
    exact cayley_injOn_Hbar hLs hRt hβjv
  have ht1 : t ≤ 1 := by
    have : arcTime v ≤ arcTime (discTime 1) :=
      strictMonoOn_arcTime.monotoneOn ⟨hv0, hv1⟩ (discTime_mem_Ico zero_le_one) hv
    rw [arcTime_discTime zero_le_one] at this
    exact Real.toNNReal_le_one.2 this
  have hrs : r < s := by
    have hcj : discTime r < jv := hc.2
    have := strictMonoOn_arcTime (discTime_mem_Ico r.coe_nonneg) ⟨hjvI.1, hjv1⟩ hcj
    rw [arcTime_discTime r.coe_nonneg, ← hs] at this
    exact_mod_cast this
  obtain ⟨u', hru', hu's, hu'R⟩ := hF s hrs.le ⟨t, ⟨zero_le, ht1⟩, hLR.symm⟩
  have hru'' : r < u' := lt_of_le_of_ne hru' fun h' => h.off (h' ▸ hu'R)
  -- `discTime u'` is a contact parameter of `L` strictly inside the arc of the gap
  have hmem : discTime u' ∈ Ioo (contactMap (toDisc (realPath R)) (toDisc (realPath L)) u) jv := by
    refine ⟨hc.1.trans (discTime_lt_discTime r.coe_nonneg (by exact_mod_cast hru'')), ?_⟩
    have := discTime_lt_discTime u'.coe_nonneg (show (u' : ℝ) < arcTime jv by rw [← hs]; exact_mod_cast hu's)
    rwa [discTime_arcTime hjv1] at this
  have hC' : discTime u' ∈ Sec7.pocketContactSet (toDisc (realPath L)) (toDisc (realPath R)) := by
    refine ⟨discTime_mem_Icc u', ?_⟩
    have hLu' : L u' ∈ Hbar := by
      have := h.left.isProperArc.mem_Hbar u'.coe_nonneg
      rwa [realPath_coe] at this
    show toDisc (realPath L) (discTime u') ∈ crossRange (toDisc (realPath R))
    rw [toDisc_realPath_discTime, h.right.isProperArc.cayley_mem_crossRange_iff hLu', arcRange_realPath]
    exact hu'R
  exact notMem_pocketContactSet_of_mem_Ioo hα hβ h.strictMono hg hmem hC'

end IsChangeConfig

end HalfPlane

/-! ### The change pocket as a random object -/

section Random

open Lemma71I Lemma71Pin MeasureTheory

variable {Ω : Type*} {m : MeasurableSpace Ω}

/-- A point lies in the closure of an open set iff points of a dense sequence inside the set approach it. -/
theorem mem_closure_iff_denseSeq {K : Set ℂ} (hK : IsOpen K) {e : ℕ → ℂ} (he : DenseRange e) (p : ℂ) :
    p ∈ closure K ↔ ∀ n : ℕ, ∃ j, e j ∈ K ∧ dist (e j) p < 1 / ((n : ℝ) + 1) := by
  constructor
  · intro hp n
    have hr : (0 : ℝ) < 1 / ((n : ℝ) + 1) := Nat.one_div_pos_of_nat
    obtain ⟨y, hyK, hyp⟩ := inter_nonempty_of_mem_closure isOpen_ball (mem_ball_self hr) hp
    obtain ⟨j, hj⟩ := he.exists_mem_open (hK.inter isOpen_ball) ⟨y, hyK, hyp⟩
    exact ⟨j, hj.1, hj.2⟩
  · intro h
    refine Metric.mem_closure_iff.2 fun ε hε => ?_
    obtain ⟨n, hn⟩ := exists_nat_one_div_lt hε
    obtain ⟨j, hjK, hjd⟩ := h n
    exact ⟨e j, hjK, by rw [dist_comm]; exact hjd.trans hn⟩

/-- Closed balls inside the complement of two random curves in `ℍ`: measurable events. -/
theorem measurableSet_closedBall_subset_diff {R L : Ω → ℝ≥0 → ℂ} (hRc : ∀ ω, Continuous (R ω))
    (hLc : ∀ ω, Continuous (L ω)) (hRm : ∀ t, Measurable[m] fun ω => R ω t)
    (hLm : ∀ t, Measurable[m] fun ω => L ω t) (c : ℂ) (ρ : ℝ) :
    MeasurableSet[m] {ω | closedBall c ρ ⊆ H \ (range (R ω) ∪ range (L ω))} := by
  let _ : MeasurableSpace Ω := m
  have hcomp := Lemma71E.measurableSet_closedBall_subset_complement (η₁ := fun ω => realPath (R ω))
    (η₂ := fun ω => realPath (L ω)) (fun ω => ((hRc ω).comp continuous_real_toNNReal).continuousOn)
    (fun ω => ((hLc ω).comp continuous_real_toNNReal).continuousOn)
    (fun t _ => hRm t.toNNReal) (fun t _ => hLm t.toNNReal) c ρ
  have e : ∀ η : ℝ≥0 → ℂ, realPath η '' Ici 0 = range η := fun η => arcRange_realPath η
  simpa only [e] using hcomp

/-- **The change test at a fixed rational point is a measurable event** (on a measurable event `Good` on which the
walls are simple proper curves): `e k` is between the walls and the change point `L r` lies in the closure of its
component. -/
theorem measurableSet_changeTest {R L : Ω → ℝ≥0 → ℂ} (hRc : ∀ ω, Continuous (R ω))
    (hLc : ∀ ω, Continuous (L ω)) (hRm : ∀ t, Measurable[m] fun ω => R ω t)
    (hLm : ∀ t, Measurable[m] fun ω => L ω t) {Good : Set Ω} (hGm : MeasurableSet[m] Good)
    (hG : ∀ ω ∈ Good, IsSimpleProper (R ω) ∧ IsSimpleProper (L ω)) (r : ℝ≥0) {e : ℕ → ℂ} (he : DenseRange e)
    (k : ℕ) :
    MeasurableSet[m] {ω | ω ∈ Good ∧ IsBetweenPt (range (R ω)) (range (L ω)) (e k) ∧
      L ω r ∈ closure (connectedComponentIn (H \ (range (R ω) ∪ range (L ω))) (e k))} := by
  classical
  let _ : MeasurableSpace Ω := m
  set G' : Set Ω := Good ∩ {ω | IsBetweenPt (range (R ω)) (range (L ω)) (e k)} with hG'def
  have hG'm : MeasurableSet G' := hGm.inter (measurableSet_isBetweenPt hRc hLc hRm hLm (e k))
  set U : Ω → Set ℂ := fun ω => if ω ∈ G' then H \ (range (R ω) ∪ range (L ω)) else univ with hUdef
  have hUo : ∀ ω, IsOpen (U ω) := fun ω => by
    by_cases hω : ω ∈ G'
    · simp only [hUdef, hω, ↓reduceIte]
      exact QuantumZipper.isOpen_H.sdiff ((IsSimpleProper.isClosed_range (hG ω hω.1).1).union
        (IsSimpleProper.isClosed_range (hG ω hω.1).2))
    · simp only [hUdef, hω, ↓reduceIte]
      exact isOpen_univ
  have hUm : ∀ (c : ℂ) (ρ : ℝ), MeasurableSet {ω | closedBall c ρ ⊆ U ω} := by
    intro c ρ
    have e' : {ω | closedBall c ρ ⊆ U ω} =
        (G' ∩ {ω | closedBall c ρ ⊆ H \ (range (R ω) ∪ range (L ω))}) ∪ G'ᶜ := by
      ext ω
      by_cases hω : ω ∈ G' <;> simp [hUdef, hω]
    rw [e']
    exact (hG'm.inter (measurableSet_closedBall_subset_diff hRc hLc hRm hLm c ρ)).union hG'm.compl
  have hpU : ∀ ω, e ((fun _ => k) ω) ∈ U ω := fun ω => by
    by_cases hω : ω ∈ G'
    · simp only [hUdef, hω, ↓reduceIte]
      exact ((isBetweenPt_iff (hG ω hω.1).1 (hG ω hω.1).2).1 hω.2).1
    · simp only [hUdef, hω, ↓reduceIte, mem_univ]
  have hball : ∀ (c : ℂ) (ρ : ℝ), MeasurableSet {ω | closedBall c ρ ⊆ connectedComponentIn (U ω) (e k)} :=
    fun c ρ => Lemma71E.measurableSet_closedBall_subset_component hUo hUm (Np := fun _ => k) measurable_const
      hpU c ρ
  have hcl : MeasurableSet {ω | L ω r ∈ closure (connectedComponentIn (U ω) (e k))} := by
    have e' : {ω | L ω r ∈ closure (connectedComponentIn (U ω) (e k))} =
        ⋂ n : ℕ, ⋃ j : ℕ, ({ω | closedBall (e j) 0 ⊆ connectedComponentIn (U ω) (e k)} ∩
          {ω | dist (e j) (L ω r) < 1 / ((n : ℝ) + 1)}) := by
      ext ω
      simp only [mem_ofPred_eq, mem_iInter, mem_iUnion, mem_inter_iff, closedBall_zero, singleton_subset_iff]
      exact mem_closure_iff_denseSeq (hUo ω).connectedComponentIn he _
    rw [e']
    exact MeasurableSet.iInter fun n => MeasurableSet.iUnion fun j => (hball _ _).inter
      (measurableSet_lt (measurable_const.dist (hLm r)) measurable_const)
  have e' : {ω | ω ∈ Good ∧ IsBetweenPt (range (R ω)) (range (L ω)) (e k) ∧
      L ω r ∈ closure (connectedComponentIn (H \ (range (R ω) ∪ range (L ω))) (e k))} =
      G' ∩ {ω | L ω r ∈ closure (connectedComponentIn (U ω) (e k))} := by
    ext ω
    by_cases hω : ω ∈ G'
    · simp only [hUdef, hω, ↓reduceIte, mem_ofPred_eq, mem_inter_iff, true_and]
      exact ⟨fun h => h.2.2, fun h => ⟨hω.1, hω.2, h⟩⟩
    · simp only [mem_ofPred_eq, mem_inter_iff, hω, false_and, iff_false, not_and]
      exact fun h1 h2 _ => hω ⟨h1, h2⟩
  rw [e']
  exact hG'm.inter hcl

/-- **Aux. lemma 130's change pocket as a random object** ("The event and the selected component are measurable from
their complete labeled incoming paths alone", p. 409). Let the walls `R ω`, `L ω` be continuous for every `ω`, with
`m`-measurable coordinates (`m` = the σ-algebra of the labelled incoming paths), and let `Good` be an `m`-measurable
event on which they form the change configuration of `IsChangeConfig` (Aux. lemma 130's event `F_r`). Then there are
an `m`-measurable index `Np` (into a dense sequence `e`) and a random open, connected, simply connected `C ω ⊆ ℍ` with
`m`-measurable closed-ball events and `e (Np ω) ∈ C ω`, which on `Good` is the change pocket — the unique component
between the walls whose closure contains the change point `L ω r` — and the default disc off `Good`. -/
theorem exists_measurable_changePocket {R L : Ω → ℝ≥0 → ℂ} (hRc : ∀ ω, Continuous (R ω))
    (hLc : ∀ ω, Continuous (L ω)) (hRm : ∀ t, Measurable[m] fun ω => R ω t)
    (hLm : ∀ t, Measurable[m] fun ω => L ω t) {r : ℝ≥0} {Good : Set Ω} (hGm : MeasurableSet[m] Good)
    (hG : ∀ ω ∈ Good, IsChangeConfig (R ω) (L ω) r) {e : ℕ → ℂ} (he : DenseRange e) :
    ∃ (C : Ω → Set ℂ) (Np : Ω → ℕ), Measurable[m] Np ∧
      (∀ ω, IsOpen (C ω) ∧ IsConnected (C ω) ∧ IsSimplyConnected (C ω) ∧ C ω ⊆ H) ∧
      (∀ (c : ℂ) (ρ : ℝ), MeasurableSet[m] {ω | closedBall c ρ ⊆ C ω}) ∧ (∀ ω, e (Np ω) ∈ C ω) ∧
      (∀ ω ∈ Good, C ω ∈ betweenComponents (range (R ω)) (range (L ω)) ∧ L ω r ∈ closure (C ω)) ∧
      (∀ ω, ω ∉ Good → C ω = defaultPocket) := by
  classical
  let _ : MeasurableSpace Ω := m
  have hG2 : ∀ ω ∈ Good, IsSimpleProper (R ω) ∧ IsSimpleProper (L ω) := fun ω hω => ⟨(hG ω hω).right, (hG ω hω).left⟩
  -- the change test
  set B : ℕ → Set Ω := fun k => {ω | ω ∈ Good ∧ IsBetweenPt (range (R ω)) (range (L ω)) (e k) ∧
      L ω r ∈ closure (connectedComponentIn (H \ (range (R ω) ∪ range (L ω))) (e k))} with hBdef
  have hBm : ∀ k, MeasurableSet (B k) := fun k => measurableSet_changeTest hRc hLc hRm hLm hGm hG2 r he k
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
  set Np : Ω → ℕ := fun ω => if ω ∈ Good then Nf ω else k₀ with hNpdef
  have hNp : Measurable Np := Measurable.ite hGm hNf measurable_const
  -- on `Good` the selected point passes the test
  have hGB : ∀ ω ∈ Good, ω ∈ B (Nf ω) := by
    intro ω hω
    obtain ⟨C₀, hC₀, hcl₀⟩ := (hG ω hω).exists_changePocket
    have hC₀o : IsOpen C₀ := by
      obtain ⟨z₀, -, -, -, rfl⟩ := hC₀
      exact (QuantumZipper.isOpen_H.sdiff ((IsSimpleProper.isClosed_range (hG ω hω).right).union
        (IsSimpleProper.isClosed_range (hG ω hω).left))).connectedComponentIn
    have hC₀ne : C₀.Nonempty := by
      obtain ⟨z₀, hz₀, -, -, rfl⟩ := hC₀
      exact ⟨z₀, mem_connectedComponentIn hz₀⟩
    obtain ⟨j, hj⟩ := he.exists_mem_open hC₀o hC₀ne
    have hjB : ω ∈ B j := ⟨hω, ((hG ω hω).mem_changePocket_iff hC₀ hcl₀ (e j)).1 hj⟩
    rcases Nat.find_spec (hp ω) with h | h
    · exact h
    · exact absurd hjB (h j)
  -- the random open domain
  set U : Ω → Set ℂ := fun ω => if ω ∈ Good then H \ (range (R ω) ∪ range (L ω)) else univ with hUdef
  have hUo : ∀ ω, IsOpen (U ω) := fun ω => by
    by_cases hω : ω ∈ Good
    · simp only [hUdef, hω, ↓reduceIte]
      exact QuantumZipper.isOpen_H.sdiff ((IsSimpleProper.isClosed_range (hG ω hω).right).union
        (IsSimpleProper.isClosed_range (hG ω hω).left))
    · simp only [hUdef, hω, ↓reduceIte]
      exact isOpen_univ
  have hUm : ∀ (c : ℂ) (ρ : ℝ), MeasurableSet {ω | closedBall c ρ ⊆ U ω} := by
    intro c ρ
    have e' : {ω | closedBall c ρ ⊆ U ω} =
        (Good ∩ {ω | closedBall c ρ ⊆ H \ (range (R ω) ∪ range (L ω))}) ∪ Goodᶜ := by
      ext ω
      by_cases hω : ω ∈ Good <;> simp [hUdef, hω]
    rw [e']
    exact (hGm.inter (measurableSet_closedBall_subset_diff hRc hLc hRm hLm c ρ)).union hGm.compl
  have hpU : ∀ ω, e (Np ω) ∈ U ω := fun ω => by
    by_cases hω : ω ∈ Good
    · simp only [hUdef, hNpdef, hω, ↓reduceIte]
      exact ((isBetweenPt_iff (hG ω hω).right (hG ω hω).left).1 (hGB ω hω).2.1).1
    · simp only [hUdef, hω, ↓reduceIte, mem_univ]
  -- the pocket
  set C : Ω → Set ℂ := fun ω => if ω ∈ Good then connectedComponentIn (U ω) (e (Np ω)) else defaultPocket
    with hCdef
  refine ⟨C, Np, hNp, fun ω => ?_, fun c ρ => ?_, fun ω => ?_, fun ω hω => ?_, fun ω hω => ?_⟩
  · by_cases hω : ω ∈ Good
    · simp only [hCdef, hω, ↓reduceIte]
      refine ⟨(hUo ω).connectedComponentIn, isConnected_connectedComponentIn_iff.2 (hpU ω), ?_, ?_⟩
      · have hpU' := hpU ω
        simp only [hUdef, hNpdef, hω, ↓reduceIte] at hpU' ⊢
        exact isSimplyConnected_connectedComponentIn_range (hG ω hω).right (hG ω hω).left hpU'
      · refine (connectedComponentIn_subset _ _).trans ?_
        simp only [hUdef, hω, ↓reduceIte]
        exact sdiff_subset
    · simp only [hCdef, hω, ↓reduceIte]
      exact ⟨isOpen_ball, isConnected_defaultPocket, isSimplyConnected_ball _ one_pos, defaultPocket_subset_H⟩
  · have hc := Lemma71E.measurableSet_closedBall_subset_component hUo hUm hNp hpU c ρ
    have e' : {ω | closedBall c ρ ⊆ C ω} =
        (Good ∩ {ω | closedBall c ρ ⊆ connectedComponentIn (U ω) (e (Np ω))}) ∪
          (Goodᶜ ∩ {_ω | closedBall c ρ ⊆ defaultPocket}) := by
      ext ω
      by_cases hω : ω ∈ Good <;> simp [hCdef, hω]
    rw [e']
    exact (hGm.inter hc).union (hGm.compl.inter (MeasurableSet.const _))
  · by_cases hω : ω ∈ Good
    · simp only [hCdef, hω, ↓reduceIte]
      exact mem_connectedComponentIn (hpU ω)
    · simp only [hCdef, hNpdef, hω, ↓reduceIte]
      exact hk₀
  · obtain ⟨-, hb, hcl⟩ := hGB ω hω
    obtain ⟨hzU, hzR, hzL⟩ := (isBetweenPt_iff (hG ω hω).right (hG ω hω).left).1 hb
    simp only [hCdef, hUdef, hNpdef, hω, ↓reduceIte]
    exact ⟨⟨e (Nf ω), hzU, hzR, hzL, rfl⟩, hcl⟩
  · simp only [hCdef, hω, ↓reduceIte]

end Random

end InteractingSLE.Sec7.PocketCoord
