/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW2BwZ
import InteractingSLE.Spec.Supplement.GW2BvCmp
import InteractingSLE.Spec.Supplement.GW2NiFin

/-!
# A good slot's exit is the uncapped exit

Packet PROVE-GW2-BUF (round 20; `hsrc`). One sample, deterministic.

* **`exit_eq_of_agree_below`**: two stage paths that agree below `min (V, B)` have the same exit, when the first
  exit plus the start is below `V` and the second is below `B`;
* **`exit_eq_of_agree_cap`**: the same when they agree below `V` alone (the second exit is then automatically below);
* **`agree_capped_unc`**: a version `(R, V)` of a candidate whose explored driver and trace agree with the uncapped
  ones (`GW2Ni.uncW`, `GW2Ni.uncTr`) on `[0, t₁]` agrees with a canonical driver of the uncapped curve (the hull
  identity below the death clock `d`, `GW2Ni.IsCanonUX`) on `[0, clock t]`, for `t < t₁` before the uncapped contact
  with the clock below `V` and `d` (`eqOn_of_agree_hulls`, read in the uncapped clock).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology
open scoped NNReal ENNReal
open QuantumZipper (fwdHull)

universe u

namespace InteractingSLE.Theorem14.GW2Bh

open Exist.StagedLaw Supp8.GB6.HullId GW2TipSystem GW2Rz GW2Rd

/-- **Two stage paths agreeing below `min (V, B)` have one exit** (first exit below `V`, second below `B`). -/
theorem exit_eq_of_agree_below {E : RecData × (ℝ≥0 → ℝ) → ℝ≥0∞} (hE : IsPathRule E) (y : RecData)
    {R₁ R₂ : ℝ≥0 → ℝ} {S : ℝ≥0} {V B : ℝ≥0∞} (hag : ∀ q : ℝ≥0, (q : ℝ≥0∞) < min V B → R₁ q = R₂ q)
    (h₁ : E (y, stgDrv R₁ S) + S < V) (h₂ : E (y, stgDrv R₂ S) + S < B) :
    E (y, stgDrv R₁ S) = E (y, stgDrv R₂ S) := by
  by_cases h : E (y, stgDrv R₁ S) + S < min V B
  · exact (pathRule_stgDrv_eq hE y (fun q hq => (hag q hq).symm) h).symm
  · rw [not_lt] at h
    have hmin : min V B = B := by
      rcases min_choice V B with hm | hm
      · rw [hm] at h; exact absurd h (not_le.2 h₁)
      · exact hm
    have h₂' : E (y, stgDrv R₂ S) + S < min V B := by rw [hmin]; exact h₂
    have heq := pathRule_stgDrv_eq hE y hag h₂'
    rw [heq] at h
    exact absurd h (not_le.2 h₂')

/-- **Two stage paths agreeing below `V` have one exit** when the first exit plus the start is below `V`. -/
theorem exit_eq_of_agree_cap {E : RecData × (ℝ≥0 → ℝ) → ℝ≥0∞} (hE : IsPathRule E) (y : RecData)
    {R₁ R₂ : ℝ≥0 → ℝ} {S : ℝ≥0} {V : ℝ≥0∞} (hag : ∀ q : ℝ≥0, (q : ℝ≥0∞) < V → R₁ q = R₂ q)
    (h₁ : E (y, stgDrv R₁ S) + S < V) : E (y, stgDrv R₁ S) = E (y, stgDrv R₂ S) :=
  (pathRule_stgDrv_eq hE y (fun q hq => (hag q hq).symm) h₁).symm

section Sample

variable {Ω : Type*} (W : ℝ≥0 → Ω → ℝ) (ζ : Ω → ℝ≥0∞) (ω : Ω) {α : Ω → ℝ≥0 → ℂ}
  (hα : IsGeneratingTrace (W · ω) ⊤ (α ω)) (hW : Continuous (W · ω)) (hW0 : W 0 ω = 0) (hζ : ζ ω = ⊤)
  {s : ℝ≥0} (hs : 0 < s) {x : ℝ} (hx : 0 ≤ x) (harc : ∀ u ∈ Icc 0 s, x * ‖α ω u‖ < 1)

include hα hW hW0 hζ hs hx harc

/-- **A capped version agrees with the uncapped canonical driver** below the uncapped clock at `t`. -/
theorem agree_capped_unc {w₁ w₂ : ℝ≥0 → Ω → ℝ} {γ₁ γ₂ : Ω → ℝ≥0 → ℂ}
    (hwc₁ : Continuous (w₁ · ω)) (hw0₁ : w₁ 0 ω = 0) (hγ₁ : IsGeneratingTrace (w₁ · ω) ⊤ (γ₁ ω))
    {t₁ : ℝ≥0} (hw : ∀ u ≤ t₁, w₁ u ω = w₂ u ω) (hγ : ∀ u ≤ t₁, γ₁ ω u = γ₂ ω u)
    {R : ℝ≥0 → ℝ} (hRc : Continuous R) (hR0 : R 0 = 0) {V : ℝ≥0∞}
    (hR : ∀ t : ℝ≥0, (t : ℝ≥0∞) < contactX x s γ₁ α ω → ENNReal.ofReal (clockX x s W ζ w₁ t ω) ≤ V →
      fwdHull (fun q : ℝ => R q.toNNReal) (clockX x s W ζ w₁ t ω) = hullX x s W ζ w₁ t ω)
    {Wc : ℝ≥0 → ℝ} (hWc : Continuous Wc) (hWc0 : Wc 0 = 0) {d : ℝ≥0∞}
    (hK : ∀ t : ℝ≥0, (t : ℝ≥0∞) < contactX x s γ₂ α ω → ENNReal.ofReal (clockX x s W ζ w₂ t ω) < d →
      fwdHull (fun q : ℝ => Wc q.toNNReal) (clockX x s W ζ w₂ t ω) = hullX x s W ζ w₂ t ω)
    {t : ℝ≥0} (htt : t < t₁) (htc : (t : ℝ≥0∞) < contactX x s γ₂ α ω)
    (htV : ENNReal.ofReal (clockX x s W ζ w₂ t ω) ≤ V) (htd : ENNReal.ofReal (clockX x s W ζ w₂ t ω) < d) :
    ∀ q : ℝ≥0, (q : ℝ) ≤ clockX x s W ζ w₂ t ω → R q = Wc q := by
  have hceq : clockX x s W ζ w₁ t ω = clockX x s W ζ w₂ t ω := clockX_eq_of_agree fun u hu => hw u (hu.trans htt.le)
  have htc₁ : (t : ℝ≥0∞) < contactX x s γ₁ α ω :=
    lt_contactX_of_agree (fun u hu => (hγ u hu).symm) htt htc
  intro q hq
  exact eqOn_of_agree_hulls W ζ ω hα hW hW0 hζ hs hx harc hwc₁ hw0₁ hγ₁ hw hγ hRc hR0 hR hWc hWc0 hK htt htc₁
    (by rw [hceq]; exact htV) (by rw [hceq]; exact htd) q (by rw [hceq]; exact hq)

end Sample

end InteractingSLE.Theorem14.GW2Bh
