/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Foundations.Loewner.FiniteEndpointState
import InteractingSLE.Spec.Supplement.GW6Reduction

/-!
# A finite positive lifetime ends the first piece at a new original record

Packet PROVE-ENDPOINT: the finite-positive-lifetime half of `Theorem14.GW1FirstThresholdStatement`
(`planning/handoffs/PROVE-T14-IN.md` §5, obstruction (ii): "finite positive lifetime ⇒ a new real
record is swallowed exactly at the stop"). In the frozen `ExplState.launch`, a piece launched from
the root state `ExplState.init 0` and run to its end, with a finite positive lifetime, ends with the
status *threshold at a new right record* (`some true`) or *at a new left record* (`some false`) as
soon as some original real point `x ≠ 0` is alive before the stop and not at it.

* `Theorem14.isThresholdEnd_launch_init_of_hit`: the deterministic unfolding of `ExplState.launch`.
* `IsIntegratedSLEEvolution.ae_isThresholdEnd_launch_init`: if the piece's driver and lifetime form an
  integrated `SLE_a(ρ)` evolution (`a > 0`; for instance the first piece of a staged history, whose
  `IsFlowLineDriver` contains one under the conditional law), then almost surely a finite positive
  lifetime gives `IsThresholdEnd`. The real point is a colliding force point
  (`IsIntegratedSLEEvolution.ae_exists_hit`, Aux. lemma 3).

What this does not cover is the zero-lifetime case of `GW1FirstThresholdStatement` (obstruction (i):
identifying the conditional boundary data of the first piece with `b`).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped NNReal ENNReal

open QuantumZipper (IsForwardSol)

namespace InteractingSLE

namespace Theorem14

/-- **A hit real point ends the first piece at a new record.** For a piece `D` with a finite positive
lifetime launched from the root state and run to its end, if some real point `x ≠ 0` is alive on every
`[0, r]`, `r < T`, and not on `[0, T]` for the stopped driver of `ExplState.launch`, then the end state
is a continuation threshold with a bad side. -/
theorem isThresholdEnd_launch_init_of_hit (κ : ℝ) (b : ℝ → ℝ) {D : (ℝ≥0 → ℝ) × ℝ≥0∞} (θ : ℝ)
    (hD : D.2 ≠ ⊤) (hpos : D.2 ≠ 0)
    (hhit : ∃ x : ℝ, (0 < x ∨ x < 0) ∧
      (∀ r : ℝ, r < (D.2.toNNReal : ℝ) → ∃ u, IsForwardSol
        (fun r : ℝ => D.1 (min ((r.toNNReal : ℝ≥0) : ℝ≥0∞) D.2).toNNReal) (x : ℂ) r u) ∧
      ¬ ∃ u, IsForwardSol (fun r : ℝ => D.1 (min ((r.toNNReal : ℝ≥0) : ℝ≥0∞) D.2).toNNReal)
        (x : ℂ) (D.2.toNNReal : ℝ) u) :
    IsThresholdEnd κ b (ExplState.launch (ExplState.init 0) 0 D θ ⊤) := by
  obtain ⟨x, hx, halive, hdead⟩ := hhit
  have hstop : min (⊤ : ℝ≥0∞) D.2 = D.2 := min_eq_right le_top
  have hc : ∀ y : ℝ, (Chart.id.recenter 0).1 (y : ℂ) = (y : ℂ) := fun y => by
    simp [Chart.recenter, Chart.id]
  have hhit : (∀ r < ((D.2.toNNReal : ℝ≥0) : ℝ), ∃ u, IsForwardSol
      (fun r => D.1 (min ((r.toNNReal : ℝ≥0) : ℝ≥0∞) D.2).toNNReal)
        ((Chart.id.recenter 0).1 (x : ℂ)) r u) ∧
      ¬ ∃ u, IsForwardSol (fun r => D.1 (min ((r.toNNReal : ℝ≥0) : ℝ≥0∞) D.2).toNNReal)
        ((Chart.id.recenter 0).1 (x : ℂ)) ((D.2.toNNReal : ℝ≥0) : ℝ) u := by
    rw [hc]; exact ⟨halive, hdead⟩
  unfold ExplState.launch ExplState.init
  dsimp only
  rw [hstop]
  rw [ite_eq_right hD, ite_eq_right not_top_lt, ite_eq_right hpos]
  split_ifs with h1 h2
  · exact Or.inl rfl
  · exact Or.inr (Or.inl rfl)
  · exfalso
    rcases hx with hx | hx
    · exact h1 ⟨x, hx, hhit⟩
    · exact h2 ⟨x, hx, hhit⟩

end Theorem14

namespace IsIntegratedSLEEvolution

variable {a : ℝ} {nL nR : ℕ} {xL : Fin nL → ℝ} {xR : Fin nR → ℝ} {ρL : Fin nL → ℝ}
  {ρR : Fin nR → ℝ} {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P]
  {𝓕 : Filtration ℝ≥0 mΩ} {VL : Fin nL → ℝ≥0 → Ω → ℝ} {VR : Fin nR → ℝ≥0 → Ω → ℝ}
  {B : ℝ≥0 → Ω → ℝ}

/-- **A finite positive lifetime of the first piece is a threshold at a new record** (almost surely):
if the driver and lifetime of the piece `D ω` form an integrated `SLE_a(ρ)` evolution (`a > 0`), then
almost surely, when `(D ω).2` is finite and positive, the piece launched from the root state and run
to its end ends with `IsThresholdEnd`. -/
theorem ae_isThresholdEnd_launch_init {D : Ω → (ℝ≥0 → ℝ) × ℝ≥0∞}
    (h : IsIntegratedSLEEvolution a xL xR ρL ρR P 𝓕 (fun t ω => (D ω).1 t) VL VR B
      (fun ω => (D ω).2))
    (ha : 0 < a) (κ : ℝ) (b : ℝ → ℝ) (θ : ℝ) :
    ∀ᵐ ω ∂P, (D ω).2 ≠ ⊤ → (D ω).2 ≠ 0 →
      Theorem14.IsThresholdEnd κ b (ExplState.launch (ExplState.init 0) 0 (D ω) θ ⊤) := by
  filter_upwards [h.ae_exists_hit ha] with ω hω hD hpos
  set T : ℝ≥0 := (D ω).2.toNNReal with hTdef
  have hTζ : (T : ℝ≥0∞) = (D ω).2 := ENNReal.coe_toNNReal hD
  have hT : 0 < T := by
    rw [pos_iff_ne_zero]
    intro h0
    rw [h0, ENNReal.coe_zero] at hTζ
    exact hpos hTζ.symm
  refine Theorem14.isThresholdEnd_launch_init_of_hit κ b θ hD hpos (hω T hT hTζ _ fun r hr hrT => ?_)
  have hlt : ((r.toNNReal : ℝ≥0) : ℝ≥0∞) < (D ω).2 := by
    rw [← hTζ, ENNReal.coe_lt_coe, Real.toNNReal_lt_iff_lt_coe hr]
    exact hrT
  simp only [min_eq_left hlt.le, ENNReal.toNNReal_coe]

end IsIntegratedSLEEvolution

end InteractingSLE
