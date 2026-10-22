import HigherDimLQGMetric.Collapse.Lemma32
import HigherDimLQGMetric.Coord.Lemma25b

/-!
# Confinement by a collar ([S] Lemma 4.2, MA1 A17 (C))

Packet S3. Generic facts about curves, weights equal to `1` off an open set `V`, and a collar
around `closure V` inside an open set `A`. Everything is stated for an arbitrary distance function
`E : X → X → ℝ≥0∞` on a topological space, so that it applies both to a metric space (`E = edist`)
and to a coordinate `E = ofReal ∘ ρ` on a Euclidean domain.

* `trap_weightedLengthWith_mono_interval`: weighted lengths over subintervals are smaller.
* `trap_exists_frontier`: a curve that leaves an open set meets its frontier.
* `trap_last_visit` (MA1 A17 (C), first half): every point of a curve that starts in
  `closure V` is within weighted cost of its last preceding visit to `closure V`.
* `trap_confine` (MA1 A17 (C), second half): a curve from `closure V` of weighted cost below
  the collar width stays in `A`.
-/

set_option autoImplicit false

noncomputable section

open Set Filter Topology
open scoped ENNReal

namespace HigherDimLQGMetric

open LQGMetric.MetricGeometry

/-- Weighted lengths over subintervals are smaller (superadditivity of partition suprema), for
any distance function. -/
theorem trap_weightedLengthWith_mono_interval {X : Type*} {E : X → X → ℝ≥0∞} {w : X → ℝ}
    {P : ℝ → X} {a b s t : ℝ} (has : a ≤ s) (hst : s ≤ t) (htb : t ≤ b) :
    weightedLengthWith E w P s t ≤ weightedLengthWith E w P a b := by
  unfold weightedLengthWith
  set g : ℝ → ℝ → ℝ≥0∞ := fun u v => infAlong w P u v * curveLengthWith E P u v
  calc partitionSup g s t ≤ partitionSup g a s + partitionSup g s t := le_add_self
    _ ≤ partitionSup g a s + partitionSup g s t + partitionSup g t b := le_self_add
    _ ≤ partitionSup g a t + partitionSup g t b :=
      add_le_add (partitionSup_add_le has hst) le_rfl
    _ ≤ partitionSup g a b := partitionSup_add_le (has.trans hst) htb

/-- A curve that starts in an open set `A` and ends outside it meets `frontier A` (first exit). -/
theorem trap_exists_frontier {X : Type*} [TopologicalSpace X] {A : Set X} (hA : IsOpen A)
    {Q : ℝ → X} {a t : ℝ} (hat : a ≤ t) (hQ : ContinuousOn Q (Icc a t)) (ha : Q a ∈ A)
    (ht : Q t ∉ A) : ∃ τ ∈ Icc a t, Q τ ∈ frontier A := by
  set S : Set ℝ := Icc a t ∩ Q ⁻¹' Aᶜ with hSdef
  have hSc : IsClosed S := hQ.preimage_isClosed_of_isClosed isClosed_Icc hA.isClosed_compl
  have hSne : S.Nonempty := ⟨t, ⟨⟨hat, le_rfl⟩, ht⟩⟩
  have hSbdd : BddBelow S := ⟨a, fun x hx => hx.1.1⟩
  have hτS : sInf S ∈ S := hSc.csInf_mem hSne hSbdd
  refine ⟨sInf S, hτS.1, ?_⟩
  rw [hA.frontier_eq]
  refine ⟨?_, hτS.2⟩
  have haτ : a < sInf S := by
    rcases hτS.1.1.lt_or_eq with h | h
    · exact h
    · exfalso
      exact hτS.2 (h ▸ ha)
  have hbefore : Q '' Ico a (sInf S) ⊆ A := by
    rintro _ ⟨s, hs, rfl⟩
    by_contra hns
    have hle : sInf S ≤ s := csInf_le hSbdd ⟨⟨hs.1, hs.2.le.trans hτS.1.2⟩, hns⟩
    exact absurd hs.2 (not_lt.2 hle)
  have hcont : ContinuousWithinAt Q (Ico a (sInf S)) (sInf S) :=
    (hQ (sInf S) hτS.1).mono (fun s hs => ⟨hs.1, hs.2.le.trans hτS.1.2⟩)
  have hmem : sInf S ∈ closure (Ico a (sInf S)) := by
    rw [closure_Ico haτ.ne]
    exact ⟨haτ.le, le_rfl⟩
  exact closure_mono hbefore (hcont.mem_closure_image hmem)

/-- **(C), first half** (MA1 A17): for a weight equal to `1` off the open set `V` and a curve
starting in `closure V`, every point `Q t` has a preceding visit `Q s ∈ closure V` with
`E (Q s) (Q t)` at most the weighted length of the whole curve (the part after the last visit runs
outside `V`, where the weight is `1`). -/
theorem trap_last_visit {X : Type*} [TopologicalSpace X] {E : X → X → ℝ≥0∞} {w : X → ℝ}
    {V : Set X} (hV : IsOpen V) (hE0 : ∀ x, E x x = 0) (hw1 : ∀ x, x ∉ V → w x = 1)
    {Q : ℝ → X} {a b : ℝ} (hQ : ContinuousOn Q (Icc a b)) (ha : Q a ∈ closure V)
    {t : ℝ} (ht : t ∈ Icc a b) :
    ∃ s ∈ Icc a t, Q s ∈ closure V ∧ E (Q s) (Q t) ≤ weightedLengthWith E w Q a b := by
  set S : Set ℝ := Icc a t ∩ Q ⁻¹' closure V with hSdef
  have hsub : Icc a t ⊆ Icc a b := Icc_subset_Icc le_rfl ht.2
  have hSc : IsClosed S :=
    (hQ.mono hsub).preimage_isClosed_of_isClosed isClosed_Icc isClosed_closure
  have hSne : S.Nonempty := ⟨a, ⟨⟨le_rfl, ht.1⟩, ha⟩⟩
  have hSbdd : BddAbove S := ⟨t, fun x hx => hx.1.2⟩
  have hsS : sSup S ∈ S := hSc.csSup_mem hSne hSbdd
  set s := sSup S with hs_def
  refine ⟨s, hsS.1, hsS.2, ?_⟩
  rcases hsS.1.2.lt_or_eq with hst | hst
  · -- the curve stays outside `V` on `[s, t]`
    have hafter : ∀ τ ∈ Icc s t, Q τ ∉ V := by
      intro τ hτ hτV
      rcases hτ.1.lt_or_eq with hsτ | hsτ
      · have hτS : τ ∈ S := ⟨⟨hsS.1.1.trans hτ.1, hτ.2⟩, subset_closure hτV⟩
        exact absurd (le_csSup hSbdd hτS) (not_le.2 hsτ)
      · -- `Q s ∈ V`: then points just after `s` are in `V`, contradicting maximality
        subst hsτ
        have hsab : s ∈ Icc a b := hsub hsS.1
        have hnhds : Q ⁻¹' V ∈ 𝓝[Icc a b] s := hQ s hsab (hV.mem_nhds hτV)
        obtain ⟨ε, hε, hball⟩ := Metric.mem_nhdsWithin_iff.1 hnhds
        set τ := min (s + ε / 2) t with hτdef
        have hsτ' : s < τ := lt_min (by linarith) hst
        have hτt : τ ≤ t := min_le_right _ _
        have hτmem : τ ∈ Metric.ball s ε ∩ Icc a b := by
          refine ⟨?_, ⟨hsS.1.1.trans hsτ'.le, hτt.trans ht.2⟩⟩
          rw [Metric.mem_ball, Real.dist_eq, abs_of_pos (by linarith)]
          have := min_le_left (s + ε / 2) t
          linarith
        have hτV' : Q τ ∈ V := hball hτmem
        have hτS : τ ∈ S := ⟨⟨hsS.1.1.trans hsτ'.le, hτt⟩, subset_closure hτV'⟩
        exact absurd (le_csSup hSbdd hτS) (not_le.2 hsτ')
    have hw : ∀ τ ∈ Icc s t, (1 : ℝ) ≤ w (Q τ) := fun τ hτ => (hw1 _ (hafter τ hτ)).ge
    calc E (Q s) (Q t) ≤ curveLengthWith E Q s t := le_curveLengthWith hst.le
      _ = ENNReal.ofReal 1 * curveLengthWith E Q s t := by rw [ENNReal.ofReal_one, one_mul]
      _ ≤ weightedLengthWith E w Q s t :=
        ofReal_mul_curveLengthWith_le_weightedLengthWith hst.le hw
      _ ≤ weightedLengthWith E w Q a b :=
        trap_weightedLengthWith_mono_interval hsS.1.1 hst.le ht.2
  · rw [hst, hE0]
    exact bot_le

/-- **(C), second half** (MA1 A17): a curve that starts in `closure V` and has weighted cost
below the collar width `κ` between `closure V` and `frontier A` stays in `A`. -/
theorem trap_confine {X : Type*} [TopologicalSpace X] {E : X → X → ℝ≥0∞} {w : X → ℝ}
    {A V : Set X} (hA : IsOpen A) (hV : IsOpen V) (hVA : closure V ⊆ A) (hE0 : ∀ x, E x x = 0)
    (hw1 : ∀ x, x ∉ V → w x = 1) {κ : ℝ≥0∞}
    (hcol : ∀ x ∈ closure V, ∀ y ∈ frontier A, κ ≤ E x y)
    {Q : ℝ → X} {a b : ℝ} (hQ : ContinuousOn Q (Icc a b)) (ha : Q a ∈ closure V)
    (hcost : weightedLengthWith E w Q a b < κ) : MapsTo Q (Icc a b) A := by
  intro t ht
  by_contra hQt
  obtain ⟨τ, hτ, hτfr⟩ := trap_exists_frontier hA ht.1
    (hQ.mono (Icc_subset_Icc le_rfl ht.2)) (hVA ha) hQt
  obtain ⟨s, -, hsV, hsτ⟩ := trap_last_visit hV hE0 hw1 hQ ha ⟨hτ.1, hτ.2.trans ht.2⟩
  exact absurd ((hcol _ hsV _ hτfr).trans hsτ) (not_le.2 hcost)

end HigherDimLQGMetric
