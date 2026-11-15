/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW2RootB23Actual

/-!
# Retained driver and tip observations use only their trace prefix

Packet PROVE-T14-GW2ROOT2. Both explicit readers are unchanged by
extending a protected recording horizon. The proof uses the already
proved equality of the actual relative traces through the shorter clock.
-/

set_option autoImplicit false
noncomputable section

open Set Filter Topology MeasureTheory
open scoped NNReal ENNReal
open QuantumZipper (H)

namespace InteractingSLE.Theorem14.GW2TipSystem.RootB23

open Exist Staged StagedLaw Restart Supp8.GB6

theorem traceHullRead_congr_prefix {γ γ' : ℝ≥0 → ℂ} {u t : ℝ≥0}
    (hγ : EqOn γ γ' (Icc 0 u)) (htu : t ≤ u) :
    traceHullRead γ t = traceHullRead γ' t := by
  have he : (fun j : ℕ × ℕ => γ (min (LawUnique.dyadicTime j) t)) =
      fun j : ℕ × ℕ => γ' (min (LawUnique.dyadicTime j) t) := by
    funext j
    exact hγ ⟨zero_le, (min_le_right _ _).trans htu⟩
  simp only [traceHullRead, he]

/-- The Borel driver reader only uses the curve through the queried time. -/
theorem traceDriverRead_congr_prefix {γ γ' : ℝ≥0 → ℂ} {u : ℝ≥0}
    (hγ : EqOn γ γ' (Icc 0 u)) : traceDriverRead γ u = traceDriverRead γ' u := by
  classical
  have hh : ∀ r ≤ u, traceHullRead γ r = traceHullRead γ' r :=
    fun _ hr => traceHullRead_congr_prefix hγ hr
  have hr : ∀ k : ℕ, ((u : ℝ) - 1 / ((k : ℝ) + 1)).toNNReal ≤ u := by
    intro k
    apply Real.toNNReal_le_iff_le_coe.mpr
    have : 0 ≤ 1 / ((k : ℝ) + 1) := by positivity
    linarith
  simp only [traceDriverRead, GW2JDetR4.hullDriverRead, hh u le_rfl, hh _ (hr _)]

/-- Extending the physical cutoff preserves both the relative driver and
the tip at every capacity time attained by the shorter record. -/
theorem relativeObservationRead_prefix_eq_before_contact {Ω : Type*}
    (W : ℝ≥0 → Ω → ℝ) (ζ : Ω → ℝ≥0∞) (ω : Ω)
    {α : ℝ≥0 → ℂ} (hα : IsGeneratingTrace (W · ω) (ζ ω) α)
    (hW : ContinuousOn (W · ω) {t | (t : ℝ≥0∞) < ζ ω}) (hW0 : W 0 ω = 0)
    {s : ℝ≥0} (hs : (s : ℝ≥0∞) < ζ ω) (hsH : α s ∈ H)
    {e : (ℝ≥0 → ℝ) × ℝ≥0∞} (he : IsRegularDriver e) {γ : ℝ≥0 → ℂ}
    (hγ : IsGeneratingTrace e.1 e.2 γ) {v V : ℝ≥0} (hvV : v ≤ V)
    (hV : (V : ℝ≥0∞) < min
      (firstContactTime (fun q => sphereInv (γ q : OnePoint ℂ))
        ((fun q => (α q : OnePoint ℂ)) '' Icc 0 s)) e.2)
    (u : ℝ≥0)
    (hu : (u : ℝ) ≤ RootZ21.forwardCapacity s v
      (cfRec s W ζ ω, recOf (v : ℝ≥0∞) e)) :
    relativeObservationRead s v u (cfRec s W ζ ω, recOf (v : ℝ≥0∞) e) =
      relativeObservationRead s V u (cfRec s W ζ ω, recOf (V : ℝ≥0∞) e) := by
  have htip := RootA22.relativeTipRead_prefix_eq_before_contact
    W ζ ω hα hW hW0 hs hsH he hγ hvV hV
  apply Prod.ext
  · apply traceDriverRead_congr_prefix
    intro q hq
    exact htip q ((NNReal.coe_le_coe.mpr hq.2).trans hu)
  · exact htip u hu

end InteractingSLE.Theorem14.GW2TipSystem.RootB23
