/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW2BwSlot

/-!
# A capped version agrees with the uncapped canonical driver below an uncapped clock value

Packet PROVE-GW2-BUF (round 20; `hsrc`). One sample. Every value below the uncapped clock at a time `t₂` before the
cap and the uncapped contact is a clock value before `t₂` (intermediate values). So `agree_capped_unc` gives
agreement below `min (V, clock t₂)` when `clock t₂ ≤ d`.

* **`agree_below_clock`**.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology
open scoped NNReal ENNReal
open QuantumZipper (fwdHull)

namespace InteractingSLE.Theorem14.GW2Bh

open Exist.StagedLaw GW2TipSystem GW2Rz GW2Rd

section Sample

variable {Ω : Type*} (W : ℝ≥0 → Ω → ℝ) (ζ : Ω → ℝ≥0∞) (ω : Ω) {α : Ω → ℝ≥0 → ℂ}
  (hα : IsGeneratingTrace (W · ω) ⊤ (α ω)) (hW : Continuous (W · ω)) (hW0 : W 0 ω = 0) (hζ : ζ ω = ⊤)
  {s : ℝ≥0} (hs : 0 < s) {x : ℝ} (hx : 0 ≤ x) (harc : ∀ u ∈ Icc 0 s, x * ‖α ω u‖ < 1)

include hα hW hW0 hζ hs hx harc

/-- **Agreement below `min (V, clock t₂)`** for a time `t₂` before the cap and the uncapped contact, with
`clock t₂ ≤ d`. -/
theorem agree_below_clock {w₁ w₂ : ℝ≥0 → Ω → ℝ} {γ₁ γ₂ : Ω → ℝ≥0 → ℂ}
    (hwc₁ : Continuous (w₁ · ω)) (hw0₁ : w₁ 0 ω = 0) (hγ₁ : IsGeneratingTrace (w₁ · ω) ⊤ (γ₁ ω))
    (hwc₂ : Continuous (w₂ · ω)) (hw0₂ : w₂ 0 ω = 0) (hγ₂ : IsGeneratingTrace (w₂ · ω) ⊤ (γ₂ ω))
    {t₁ : ℝ≥0} (hw : ∀ u ≤ t₁, w₁ u ω = w₂ u ω) (hγ : ∀ u ≤ t₁, γ₁ ω u = γ₂ ω u)
    {R : ℝ≥0 → ℝ} (hRc : Continuous R) (hR0 : R 0 = 0) {V : ℝ≥0∞}
    (hR : ∀ t : ℝ≥0, (t : ℝ≥0∞) < contactX x s γ₁ α ω → ENNReal.ofReal (clockX x s W ζ w₁ t ω) ≤ V →
      fwdHull (fun q : ℝ => R q.toNNReal) (clockX x s W ζ w₁ t ω) = hullX x s W ζ w₁ t ω)
    {Wc : ℝ≥0 → ℝ} (hWc : Continuous Wc) (hWc0 : Wc 0 = 0) {d : ℝ≥0∞}
    (hK : ∀ t : ℝ≥0, (t : ℝ≥0∞) < contactX x s γ₂ α ω → ENNReal.ofReal (clockX x s W ζ w₂ t ω) < d →
      fwdHull (fun q : ℝ => Wc q.toNNReal) (clockX x s W ζ w₂ t ω) = hullX x s W ζ w₂ t ω)
    {t₂ : ℝ≥0} (ht₂ : t₂ < t₁) (ht₂c : (t₂ : ℝ≥0∞) < contactX x s γ₂ α ω)
    (ht₂d : ENNReal.ofReal (clockX x s W ζ w₂ t₂ ω) ≤ d) :
    ∀ q : ℝ≥0, (q : ℝ≥0∞) < min V (ENNReal.ofReal (clockX x s W ζ w₂ t₂ ω)) → R q = Wc q := by
  intro q hq
  obtain ⟨h0, hsm, hac⟩ := GW2Rz.clock_props W ζ ω hα hW hW0 hζ hs hx harc hwc₂ hw0₂ hγ₂
  have hqV : (q : ℝ≥0∞) < V := hq.trans_le (min_le_left _ _)
  have hqc : (q : ℝ≥0∞) < ENNReal.ofReal (clockX x s W ζ w₂ t₂ ω) := hq.trans_le (min_le_right _ _)
  have hqr : (q : ℝ) < clockX x s W ζ w₂ t₂ ω := by
    rw [← ENNReal.ofReal_coe_nnreal] at hqc
    exact (ENNReal.ofReal_lt_ofReal_iff_of_nonneg q.2).1 hqc
  -- `q` is a clock value before `t₂`
  have hcont : ContinuousOn (fun t => clockX x s W ζ w₂ t ω) (Icc 0 t₂) :=
    hac.mono fun t ht => lt_of_le_of_lt (ENNReal.coe_le_coe.2 ht.2) ht₂c
  obtain ⟨t, ht, hteq'⟩ := intermediate_value_Icc (zero_le : (0 : ℝ≥0) ≤ t₂) hcont
    ⟨by rw [show clockX x s W ζ w₂ 0 ω = 0 from h0]; exact q.2, hqr.le⟩
  have hteq : clockX x s W ζ w₂ t ω = (q : ℝ) := hteq'
  have htc : (t : ℝ≥0∞) < contactX x s γ₂ α ω := lt_of_le_of_lt (ENNReal.coe_le_coe.2 ht.2) ht₂c
  have htq : ENNReal.ofReal (clockX x s W ζ w₂ t ω) = (q : ℝ≥0∞) := by
    rw [hteq, ENNReal.ofReal_coe_nnreal]
  exact agree_capped_unc W ζ ω hα hW hW0 hζ hs hx harc hwc₁ hw0₁ hγ₁ hw hγ hRc hR0 hR hWc hWc0 hK
    (lt_of_le_of_lt ht.2 ht₂) htc (by rw [htq]; exact hqV.le) (by rw [htq]; exact hqc.trans_le ht₂d) q
    (by rw [hteq])

end Sample

end InteractingSLE.Theorem14.GW2Bh
