/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.WalkWdPair

/-!
# The component chart maps into the prefix chart's domain (activeness of a controlled prefix)

Packet PROVE-WALK-WORDS2, toward `WalkTouchMatchStatement`. At a central landing (a trace point in `ℍ`) the domain
condition `hdom` of a prefix match came from the local hull near the landing
(`WalkWords.exists_ball_mem_loewner_image`),
which needs fresh trace points in `ℍ` and fails at real touch points. Here it comes globally from activeness of the
component with respect to the prefix:

* **`subset_H_diff_fillH_raw_of_bounded`**: if the prefix raw set is an initial segment `⊆ α([0, a])` of the right wall
  and the closing contact `α U = β V ∈ C̄` comes later (`a < U`, `0 < V`), then `C ⊆ ℍ \ fill(raw)`
  (`WalkIntActive.active_of_later_common_contact` with the empty left part);
* **`subset_H_diff_fillH_raw_of_unbounded`**: for an unbounded component, with no exit data
  (`subset_H_diff_fillH_of_isPreconnected`);
* **`mem_prefix_dom_of_subset`**: then every point of the component lies in the prefix chart's domain
  `ℍ \ hull = ℍ \ fill(raw)`, so the component chart maps `ℍ` into it.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Filter Topology Metric Complex
open scoped NNReal ENNReal
open QuantumZipper (H Hbar)

namespace InteractingSLE.Theorem14.WalkWd

open WalkBdry WalkMean WalkIntFill WalkIntActive

/-- **The prefix chart's domain contains every component disjoint from the filled prefix.** -/
theorem mem_prefix_dom_of_subset {s : ExplState} (R : WalkPrefix s) {C : Set ℂ} (hC : C ⊆ H \ fillH R.raw)
    {c : Chart} (hcC : MapsTo c.2.1 H C) : ∀ w ∈ H, c.2.1 w ∈ (prefixChart R.piece R.time).dom := by
  intro w hw
  have hd : ((prefixChart R.piece R.time).dom : Set ℂ) = H \ fillH R.raw := by
    rw [R.model.dom_eq, R.filled]; rfl
  show c.2.1 w ∈ ((prefixChart R.piece R.time).dom : Set ℂ)
  rw [hd]
  exact hC (hcC hw)

/-- **A bounded component is active for a prefix stopped before its closing contact.** -/
theorem subset_H_diff_fillH_raw_of_bounded {s : ExplState} (R : WalkPrefix s) {α β : ℝ≥0 → ℂ}
    (hα : Supp9B.IsProperCurve α) (hβ : Supp9B.IsProperCurve β)
    (horder : ∀ u u' v v' : ℝ≥0, α u = β v → α u' = β v' → (u < u' ↔ v < v'))
    {C : Set ℂ} (hC : C ∈ betweenComponents (range α) (range β)) {a U V : ℝ≥0}
    (hraw : R.raw ⊆ α '' Icc 0 a) (haU : a < U) (hV : 0 < V) (hUV : α U = β V) (hUC : α U ∈ closure C) :
    C ⊆ H \ fillH R.raw :=
  active_of_later_common_contact hα hβ horder hC (b := 0) (hraw.trans subset_union_left) haU hV hUV hUC

/-- **An unbounded component is active for every prefix.** -/
theorem subset_H_diff_fillH_raw_of_unbounded {s : ExplState} (R : WalkPrefix s) {wR wL : ExplSpec}
    {sR sL : ExplState} {C : Set ℂ} (hC : C ∈ betweenComponents (physOf wR sR) (physOf wL sL))
    (hCo : IsOpen C) (hCu : ¬ Bornology.IsBounded C)
    (hraw : R.raw ⊆ physOf wR sR ∪ physOf wL sL) : C ⊆ H \ fillH R.raw := by
  obtain ⟨z, -, -, -, hCeq⟩ := hC
  have hCp : IsPreconnected C := by rw [hCeq]; exact isPreconnected_connectedComponentIn
  have hCsub : C ⊆ H \ (physOf wR sR ∪ physOf wL sL) := by rw [hCeq]; exact connectedComponentIn_subset _ _
  have hdis : Disjoint C R.raw := Set.disjoint_left.2 fun p hp hr => (hCsub hp).2 (hraw hr)
  have hdisCl := hdis.closure_right hCo
  have hRb : Bornology.IsBounded R.raw := by
    apply R.model.isHull.2.1.subset
    intro w hw
    rw [R.filled]
    exact mem_fillH_of_mem_closure (R.raw_subset_H hw) (subset_closure hw)
  exact Sec6.subset_H_diff_fillH_of_isPreconnected hRb hCp
    (fun p hp => ⟨(hCsub hp).1, fun hr => Set.disjoint_left.1 hdisCl hp hr⟩) hCu

end InteractingSLE.Theorem14.WalkWd
