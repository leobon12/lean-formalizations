/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GB6HullIdRule

/-!
# Uncapped first hitting rules after a path-rule time, at a level read at that time (S3, ruling R115)

Packet PROVE-GW2-BUF (S3). Ruling R115 fixes GW2's version cap and slow stop strictly before contact. They are first
times after the relative time `A` of the physical history end at which GB6's causal separation readout `G` drops to a
level read at `A` (J31's level `min(G(A)/2, 1/(m+1))`, and half of it). GB6's `HullId.hitRule G ε c` is the
attained first time of a causal readout below a record level, capped at a constant `c`. This file builds, from any
causal measurable readout and any measurable path rule `A`:

* `levelAt G A p := ⨅ q ≤ A p, G q p` (rational `q`): a causal Borel reading of the readout at `A` (along an antitone
  continuous readout it is `G (A p)`);
* `afterRead G A lev`: the normalized readout `2` before `A` and `min 2 (G t / lev (levelAt …))` from `A` on;
  **`isCausal_afterRead`**, **`measurable_afterRead`**;
* `afterRule G A lev := ⨆ n, hitRule (afterRead G A lev) 1 n`: the UNCAPPED attained first hitting time;
  **`isPathRule_afterRule`**, **`measurable_afterRule`**.
-/

set_option autoImplicit false
noncomputable section

open MeasureTheory Set Filter Topology
open scoped NNReal ENNReal

namespace InteractingSLE.Theorem14.GW2Bh

open Exist.StagedLaw Supp8.GB6 Supp8.GB6.HullId Supp8.GB6.RelDrv Supp8.GB6.RelDrv.Version

variable (G : GaugeReadout) (A : RecData × (ℝ≥0 → ℝ) → ℝ≥0∞) (lev : ℝ → ℝ)

/-- **The readout read at the path-rule time `A`**: the infimum of its rational values up to `A` (capped by `1`). -/
def levelAt (p : RecData × (ℝ≥0 → ℝ)) : ℝ :=
  ⨅ q : ℚ≥0, if ((q : ℝ≥0) : ℝ≥0∞) ≤ A p then min 1 (G q p) else 1

/-- **The normalized readout after `A`**: `2` before `A`, `min 2 (G t / lev ℓ)` from `A` on, with `ℓ` read at `A`. -/
def afterRead : GaugeReadout := fun t p =>
  if A p ≤ (t : ℝ≥0∞) then min 2 (G t p / lev (levelAt G A p)) else 2

/-- **The uncapped attained first time** the normalized readout drops to `1`. -/
def afterRule (p : RecData × (ℝ≥0 → ℝ)) : ℝ≥0∞ :=
  ⨆ n : ℕ, hitRule (afterRead G A lev) (fun _ => 1) (n : ℝ≥0) p

variable {G A lev}

/-- A path rule's time is decided by the path up to any later time. -/
theorem pathRule_le_iff (hA : IsPathRule A) {r : RecData} {w w' : ℝ≥0 → ℝ} {t : ℝ≥0}
    (h : ∀ u ≤ t, w u = w' u) : A (r, w) ≤ t ↔ A (r, w') ≤ t := by
  constructor
  · intro hle
    rw [hA r w w' fun u hu => h u (ENNReal.coe_le_coe.1 (hu.trans hle))]
    exact hle
  · intro hle
    rw [hA r w' w fun u hu => (h u (ENNReal.coe_le_coe.1 (hu.trans hle))).symm]
    exact hle

/-- Agreement up to `t ≥ A` fixes `A`. -/
theorem pathRule_eq_of_le (hA : IsPathRule A) {r : RecData} {w w' : ℝ≥0 → ℝ} {t : ℝ≥0}
    (h : ∀ u ≤ t, w u = w' u) (hle : A (r, w) ≤ t) : A (r, w') = A (r, w) :=
  hA r w w' fun u hu => h u (ENNReal.coe_le_coe.1 (hu.trans hle))

theorem levelAt_congr (hG : IsCausal G) (hA : IsPathRule A) {r : RecData} {w w' : ℝ≥0 → ℝ} {t : ℝ≥0}
    (h : ∀ u ≤ t, w u = w' u) (hle : A (r, w) ≤ t) : levelAt G A (r, w') = levelAt G A (r, w) := by
  have hAe := pathRule_eq_of_le hA h hle
  unfold levelAt
  refine iInf_congr fun q => ?_
  rw [hAe]
  by_cases hq : ((q : ℝ≥0) : ℝ≥0∞) ≤ A (r, w)
  · rw [ite_eq_left hq, ite_eq_left hq, hG q r w' w fun u hu =>
      (h u (hu.trans (ENNReal.coe_le_coe.1 (hq.trans hle)))).symm]
  · rw [ite_eq_right hq, ite_eq_right hq]

/-- **The normalized readout is causal.** -/
theorem isCausal_afterRead (hG : IsCausal G) (hA : IsPathRule A) : IsCausal (afterRead G A lev) := by
  intro t r w w' h
  unfold afterRead
  by_cases hle : A (r, w) ≤ (t : ℝ≥0∞)
  · have hle' : A (r, w') ≤ (t : ℝ≥0∞) := (pathRule_le_iff hA h).1 hle
    rw [ite_eq_left hle, ite_eq_left hle', levelAt_congr hG hA h hle, hG t r w w' h]
  · have hle' : ¬ A (r, w') ≤ (t : ℝ≥0∞) := fun h' => hle ((pathRule_le_iff hA h).2 h')
    rw [ite_eq_right hle, ite_eq_right hle']

theorem measurable_levelAt (hG : ∀ t, Measurable (G t)) (hAm : Measurable A) : Measurable (levelAt G A) := by
  refine Measurable.iInf fun q => Measurable.ite ?_ (measurable_const.min (hG _)) measurable_const
  exact measurableSet_le measurable_const hAm

/-- **The normalized readout is Borel.** -/
theorem measurable_afterRead (hG : ∀ t, Measurable (G t)) (hAm : Measurable A) (hlev : Measurable lev)
    (t : ℝ≥0) : Measurable (afterRead G A lev t) := by
  refine Measurable.ite (measurableSet_le hAm measurable_const) ?_ measurable_const
  exact measurable_const.min ((hG t).div (hlev.comp (measurable_levelAt hG hAm)))

/-- **The uncapped attained first time is a path rule.** -/
theorem isPathRule_afterRule (hG : IsCausal G) (hA : IsPathRule A) : IsPathRule (afterRule G A lev) := by
  intro r w w' hag
  unfold afterRule
  refine iSup_congr fun n => ?_
  refine isPathRule_hitRule (isCausal_afterRead hG hA) r w w' fun u hu => hag u ?_
  exact hu.trans (le_iSup (fun n : ℕ => hitRule (afterRead G A lev) (fun _ => 1) (n : ℝ≥0) (r, w)) n)

/-- **The uncapped attained first time is Borel.** -/
theorem measurable_afterRule (hG : ∀ t, Measurable (G t)) (hAm : Measurable A) (hlev : Measurable lev) :
    Measurable (afterRule G A lev) :=
  Measurable.iSup fun _ => measurable_hitRule (measurable_afterRead hG hAm hlev) measurable_const

end InteractingSLE.Theorem14.GW2Bh
