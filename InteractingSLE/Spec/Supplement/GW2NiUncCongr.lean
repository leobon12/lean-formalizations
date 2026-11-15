/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW2NiCap

/-!
# Root-`x` readings of two curves agreeing up to a time

Packet PROVE-GW2-NEARIMG2 (D50). The root-`x` clock, hull, contact and relative life read the explored curve only up
to the time (the contact up to the contact time), so a capped candidate and the uncapped driver have the same
readings below `T + cap`; if the contact comes before `T + cap`, the same contact and relative life.

* `hullX_congr`; **`contactX_eq_of_agree`** (contacts agree when one comes before the agreement time);
* **`contactLifeX_eq_of_agree`**; `clockX_congr` is in `GW2NiCap`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Filter Topology MeasureTheory
open scoped NNReal ENNReal

namespace InteractingSLE.Theorem14.GW2Ni

open Exist StagedLaw GW2TipSystem GW2Rz

variable {Ω : Type*} (x : ℝ) (s : ℝ≥0) (W : ℝ≥0 → Ω → ℝ) (ζ : Ω → ℝ≥0∞)

/-- The root-`x` first contact of one curve with a counterflow prefix (`GW2Rz.contactX` at one sample). -/
abbrev fct (γ α : ℝ≥0 → ℂ) : ℝ≥0∞ :=
  Supp8.GB6.firstContactTime (fun t => Supp8.GB6.sphereInv (((x : ℂ) + γ t : ℂ) : OnePoint ℂ))
    ((fun u => (α u : OnePoint ℂ)) '' Icc 0 s)

/-- The re-centred relative hull at `t` reads the explored driver only up to `t`. -/
theorem hullX_congr {w w' : ℝ≥0 → Ω → ℝ} {ω : Ω} {t : ℝ≥0} (h : ∀ u ≤ t, w u ω = w' u ω) :
    hullX x s W ζ w t ω = hullX x s W ζ w' t ω := by
  unfold hullX recPair
  rw [GW2Wm.recOf_congr_top (f := fun u => w u ω) (g := fun u => w' u ω) h]

/-- **Two continuous traces agreeing up to `τ` have the same contact when one contact is at most `τ`.** -/
theorem contactX_eq_of_agree {γ γ' α : Ω → ℝ≥0 → ℂ} {ω : Ω} (hγ : Continuous (γ ω)) (hγ' : Continuous (γ' ω))
    (hα : Continuous (α ω)) {τ : ℝ≥0} (h : ∀ u ≤ τ, γ ω u = γ' ω u)
    (hc : contactX x s γ α ω ≤ (τ : ℝ≥0∞)) : contactX x s γ' α ω = contactX x s γ α ω := by
  have hiff : ∀ t : ℝ≥0, t ≤ τ → ((t : ℝ≥0∞) < contactX x s γ α ω ↔ (t : ℝ≥0∞) < contactX x s γ' α ω) :=
    fun t ht => ⟨lt_contactX_congr x s hγ hγ' hα (fun u hu => h u (hu.trans ht)),
      lt_contactX_congr x s hγ' hγ hα (fun u hu => (h u (hu.trans ht)).symm)⟩
  have hfin : contactX x s γ α ω ≠ ⊤ := ne_top_of_le_ne_top ENNReal.coe_ne_top hc
  set A := contactX x s γ α ω with hA
  have hAτ : A.toNNReal ≤ τ := by
    rw [← ENNReal.coe_le_coe, ENNReal.coe_toNNReal hfin]; exact hc
  refine le_antisymm ?_ ?_
  · by_contra hlt
    rw [not_le] at hlt
    have h1 : ((A.toNNReal : ℝ≥0) : ℝ≥0∞) < contactX x s γ' α ω := by rwa [ENNReal.coe_toNNReal hfin]
    have h2 := (hiff _ hAτ).2 h1
    rw [ENNReal.coe_toNNReal hfin] at h2
    exact lt_irrefl _ h2
  · refine le_of_forall_lt fun b hb => ?_
    have hbfin : b ≠ ⊤ := ne_top_of_lt hb
    have hbτ : b.toNNReal ≤ τ := by
      rw [← ENNReal.coe_le_coe, ENNReal.coe_toNNReal hbfin]; exact hb.le.trans hc
    have := (hiff _ hbτ).1 (by rwa [ENNReal.coe_toNNReal hbfin])
    rwa [ENNReal.coe_toNNReal hbfin] at this

/-- **The root-`x` relative life is read before the contact.** -/
theorem contactLifeX_eq_of_agree (cf : RecData) {w w' : ℝ≥0 → ℝ} {γ γ' α : ℝ≥0 → ℂ}
    (hc : fct x s γ' α = fct x s γ α) (hw : ∀ t : ℝ≥0, (t : ℝ≥0∞) < fct x s γ α → ∀ u ≤ t, w u = w' u) :
    GW2Bh.contactLifeX x s cf w γ α = GW2Bh.contactLifeX x s cf w' γ' α := by
  unfold GW2Bh.contactLifeX
  congr 1
  change _ '' {t : ℝ≥0 | (t : ℝ≥0∞) < fct x s γ α} = _ '' {t : ℝ≥0 | (t : ℝ≥0∞) < fct x s γ' α}
  rw [hc]
  refine image_congr fun t ht => ?_
  rw [GW2Wm.recOf_congr_top (f := w) (g := w') (hw t ht)]

end InteractingSLE.Theorem14.GW2Ni
