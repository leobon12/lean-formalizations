import HigherDimLQGMetric.Trap.Reparam

/-!
# Confinement sets of the trap ([S] Lemma 4.2, MA1 A17)

Packet S3. In a metric space `Z` with an open set `A` (the annulus `A_{1,3}`) and an open
collector `V` with `closure V ⊆ A`, MA1 A17 names the confinement sets
`Y_r = {p ∈ closure A : dist(p, closure V) ≤ r}` (`Y₀ = Y_{a_col/2}`, `Y′ = Y_{a_col}`).
Here they are `trapSet A V r`; `trapOpen A V r` is the open set `{p ∈ A : dist(p, closure V) < r}`
used as the collar neighbourhood in Lemmas 2.4 and 2.5′.

* compactness, inclusions, and `trapSet ⊆ A` under the collar bound;
* `trap_mapsTo_trapSet`: (C) in metric form — a curve from `closure V` of weighted length `< r`
  (weight `1` off `V`) stays in `trapSet A V r` when `r` is at most the collar width.
-/

set_option autoImplicit false

noncomputable section

open Set Filter Topology
open scoped ENNReal

namespace HigherDimLQGMetric

open LQGMetric.MetricGeometry

section Sets

variable {Z : Type*} [MetricSpace Z]

/-- `Y_r = {p ∈ closure A : dist(p, closure V) ≤ r}` (MA1 A17). -/
def trapSet (A V : Set Z) (r : ℝ) : Set Z :=
  closure A ∩ {p | Metric.infDist p (closure V) ≤ r}

/-- `{p ∈ A : dist(p, closure V) < r}`. -/
def trapOpen (A V : Set Z) (r : ℝ) : Set Z :=
  A ∩ {p | Metric.infDist p (closure V) < r}

variable {A V : Set Z} {r r' : ℝ}

theorem isClosed_trapSet : IsClosed (trapSet A V r) :=
  isClosed_closure.inter (isClosed_le (Metric.continuous_infDist_pt _) continuous_const)

theorem isCompact_trapSet (hAc : IsCompact (closure A)) : IsCompact (trapSet A V r) :=
  hAc.of_isClosed_subset isClosed_trapSet inter_subset_left

theorem isOpen_trapOpen (hA : IsOpen A) : IsOpen (trapOpen A V r) :=
  hA.inter (isOpen_lt (Metric.continuous_infDist_pt _) continuous_const)

theorem trapSet_mono (h : r ≤ r') : trapSet A V r ⊆ trapSet A V r' :=
  fun _ hp => ⟨hp.1, hp.2.trans h⟩

theorem closure_trapOpen_subset : closure (trapOpen A V r) ⊆ trapSet A V r :=
  closure_minimal (fun p hp => ⟨subset_closure hp.1,
    show Metric.infDist p (closure V) ≤ r from (show Metric.infDist p (closure V) < r from hp.2).le⟩)
    isClosed_trapSet

theorem closure_subset_trapSet (hVA : closure V ⊆ A) (hr : 0 ≤ r) :
    closure V ⊆ trapSet A V r := fun p hp =>
  ⟨subset_closure (hVA hp), show Metric.infDist p (closure V) ≤ r by
    rw [Metric.infDist_zero_of_mem hp]; exact hr⟩

/-- Under the collar bound `κ ≤ dist(closure V, frontier A)`, every `Y_r` with `r < κ` lies
in `A`. -/
theorem trapSet_subset (hA : IsOpen A) (hVne : (closure V).Nonempty) {κ : ℝ}
    (hcol : ∀ x ∈ closure V, ∀ y ∈ frontier A, κ ≤ dist x y) (hr : r < κ) :
    trapSet A V r ⊆ A := by
  intro p hp
  by_contra hpA
  have hfr : p ∈ frontier A := by
    rw [hA.frontier_eq]
    exact ⟨hp.1, hpA⟩
  have hle : κ ≤ Metric.infDist p (closure V) :=
    (Metric.le_infDist hVne).2 fun y hy => by rw [dist_comm]; exact hcol y hy p hfr
  exact absurd (hp.2.trans_lt hr) (not_lt.2 hle)

theorem trapSet_subset_trapOpen (hA : IsOpen A) (hVne : (closure V).Nonempty) {κ : ℝ}
    (hcol : ∀ x ∈ closure V, ∀ y ∈ frontier A, κ ≤ dist x y) (hr : r < κ) (hrr' : r < r') :
    trapSet A V r ⊆ trapOpen A V r' :=
  fun _ hp => ⟨trapSet_subset hA hVne hcol hr hp, hp.2.trans_lt hrr'⟩

/-- **(C), metric form.** A curve starting in `closure V`, with weight `1` off `V` and weighted
length `< r`, stays in `Y_r`, provided `r` does not exceed the collar width. -/
theorem trap_mapsTo_trapSet (hA : IsOpen A) (hV : IsOpen V) (hVA : closure V ⊆ A)
    {w : Z → ℝ} (hw1 : ∀ x, x ∉ V → w x = 1)
    (hcol : ∀ x ∈ closure V, ∀ y ∈ frontier A, r ≤ dist x y)
    {Q : ℝ → Z} {a b : ℝ} (hQ : ContinuousOn Q (Icc a b)) (ha : Q a ∈ closure V)
    (hcost : weightedLength w Q a b < ENNReal.ofReal r) :
    MapsTo Q (Icc a b) (trapSet A V r) := by
  have hcost' : weightedLengthWith edist w Q a b < ENNReal.ofReal r := by
    rwa [weightedLengthWith_edist]
  have hcolE : ∀ x ∈ closure V, ∀ y ∈ frontier A, ENNReal.ofReal r ≤ edist x y := by
    intro x hx y hy
    rw [edist_dist]
    exact ENNReal.ofReal_le_ofReal (hcol x hx y hy)
  have hmapsA := trap_confine hA hV hVA (fun x => edist_self x) hw1 hcolE hQ ha hcost'
  intro t ht
  refine ⟨subset_closure (hmapsA ht), ?_⟩
  obtain ⟨s, -, hsV, hst⟩ := trap_last_visit hV (fun x => edist_self x) hw1 hQ ha ht
  have hfin : weightedLengthWith edist w Q a b ≠ ⊤ := ne_top_of_lt hcost'
  have hdist : dist (Q s) (Q t) ≤ r := by
    have h1 : edist (Q s) (Q t) ≤ ENNReal.ofReal r := hst.trans hcost'.le
    rw [edist_dist] at h1
    have hr : 0 ≤ r := by
      by_contra hneg
      push Not at hneg
      rw [ENNReal.ofReal_of_nonpos hneg.le] at hcost'
      exact absurd hcost' (not_lt.2 bot_le)
    exact (ENNReal.ofReal_le_ofReal_iff hr).1 h1
  calc Metric.infDist (Q t) (closure V) ≤ dist (Q t) (Q s) := Metric.infDist_le_dist_of_mem hsV
    _ = dist (Q s) (Q t) := dist_comm _ _
    _ ≤ r := hdist

end Sets

end HigherDimLQGMetric
