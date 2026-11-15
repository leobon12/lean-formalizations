/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW2BuReidx
import InteractingSLE.Spec.Supplement.GW2BhKill

/-!
# Good versions at one sample: the exit before the cap

Packet PROVE-GW2-BUF (round 18; the instance layer, deterministic part). At one sample, the versions `R j` of a
candidate equal one canonical driver `Wc` below their caps `V j`. The stage records and starts of the versions with
caps past the start are one record `y` and one start `S`. The exit `E` is a path rule. Then:

* `stgDrv_agree`, **`pathRule_stgDrv_eq`**: the exit read on two drivers that agree below a cap past the exit is the
  same;
* **`eventually_good`**: if the exit on the canonical stage path plus the start is below `Λ`, and the caps exhaust
  every value below `Λ`, then eventually every version's exit plus its start is below its cap;
* **`good_transfer`**: the goodness at a version `j₁` gives the near slot's goodness at any version `j₂` that agrees
  below `V j₁`: the exit on version `j₂`'s stage path is below the lower cap `V j₁ − S`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Filter MeasureTheory Topology
open scoped NNReal ENNReal

namespace InteractingSLE.Theorem14.GW2Bh

open Exist.StagedLaw Supp8.GB6.HullId GW2Rd

/-- Two drivers that agree below a cap past `S + u` have the same stage path at `u`. -/
theorem stgDrv_agree {R R' : ℝ≥0 → ℝ} {S : ℝ≥0} {Vc : ℝ≥0∞} (h : ∀ q : ℝ≥0, (q : ℝ≥0∞) < Vc → R q = R' q)
    {u : ℝ≥0} (hu : (S : ℝ≥0∞) + u < Vc) : stgDrv R S u = stgDrv R' S u := by
  have hS : (S : ℝ≥0∞) < Vc := lt_of_le_of_lt le_self_add hu
  have hSu : ((S + u : ℝ≥0) : ℝ≥0∞) < Vc := by rw [ENNReal.coe_add]; exact hu
  simp only [stgDrv, h _ hSu, h _ hS]

/-- **The exit read on two drivers that agree below a cap past the exit is the same.** -/
theorem pathRule_stgDrv_eq {E : RecData × (ℝ≥0 → ℝ) → ℝ≥0∞} (hE : IsPathRule E) (y : RecData)
    {R R' : ℝ≥0 → ℝ} {S : ℝ≥0} {Vc : ℝ≥0∞} (hag : ∀ q : ℝ≥0, (q : ℝ≥0∞) < Vc → R q = R' q)
    (hlt : E (y, stgDrv R' S) + S < Vc) : E (y, stgDrv R S) = E (y, stgDrv R' S) :=
  hE y (stgDrv R' S) (stgDrv R S) fun u hu => (stgDrv_agree hag (lt_of_le_of_lt
    (by rw [add_comm]; exact add_le_add_left hu _) hlt)).symm

/-- **Eventually every version is good**: the exit on the canonical stage path plus the start is below `Λ`, and the
caps exhaust every value below `Λ`. -/
theorem eventually_good {E : RecData × (ℝ≥0 → ℝ) → ℝ≥0∞} (hE : IsPathRule E) {Wc : ℝ≥0 → ℝ} {y : RecData}
    {S : ℝ≥0} {R : ℕ → ℝ≥0 → ℝ} {V : ℕ → ℝ≥0∞} {recs : ℕ → RecData} {starts : ℕ → ℝ≥0}
    (hag : ∀ j (q : ℝ≥0), (q : ℝ≥0∞) < V j → R j q = Wc q)
    (hrec : ∀ j, (S : ℝ≥0∞) < V j → recs j = y) (hst : ∀ j, (S : ℝ≥0∞) < V j → starts j = S) {Λ : ℝ≥0∞}
    (hlife : E (y, stgDrv Wc S) + S < Λ) (hexh : ∀ q : ℝ≥0∞, q < Λ → ∀ᶠ j in atTop, q < V j) :
    ∀ᶠ j in atTop, E (recs j, stgDrv (R j) (starts j)) + starts j < V j := by
  filter_upwards [hexh _ hlife] with j hj
  have hS : (S : ℝ≥0∞) < V j := lt_of_le_of_lt le_add_self hj
  rw [hrec j hS, hst j hS, pathRule_stgDrv_eq hE y (hag j) hj]
  exact hj

/-- **The goodness at version `j₁` gives the near slot's goodness at a version `j₂` agreeing below `V j₁`.** -/
theorem good_transfer {E : RecData × (ℝ≥0 → ℝ) → ℝ≥0∞} (hE : IsPathRule E) {y : RecData} {S : ℝ≥0}
    {R₁ R₂ : ℝ≥0 → ℝ} {V₁ : ℝ≥0∞} (hag : ∀ q : ℝ≥0, (q : ℝ≥0∞) < V₁ → R₂ q = R₁ q)
    (hgood : E (y, stgDrv R₁ S) + S < V₁) : E (y, stgDrv R₂ S) < V₁ - S := by
  rw [pathRule_stgDrv_eq hE y hag hgood]
  exact lt_tsub_iff_right.2 hgood

end InteractingSLE.Theorem14.GW2Bh
