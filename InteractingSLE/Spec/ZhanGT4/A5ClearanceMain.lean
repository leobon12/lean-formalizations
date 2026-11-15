/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.ZhanGT4.A5ClearanceGeom
import InteractingSLE.Spec.ZhanGT4.A5Det
import InteractingSLE.Spec.Sec4.RepulsionNoncollision
import QuantumZipper.Proofs.Loewner.Algebra

/-!
# Protected-ray clearance, VII: `SeparatedClearanceStatement κ` for `κ > 4`

Packet PROVE-ZHAN-CLEAR. **`separatedClearanceStatement`**: for every `κ > 4`, the separated two-force law
`SLE_κ(ρ_L; ρ_R)` (marks `p_L < 0 < p_R`, weights `≥ κ/2 − 2`) almost surely lives forever and its terminal hull keeps
a positive distance from every compact subset of `(−∞, p_L] ∪ [p_R, ∞)` — Astra's interface (B.3) (*Follow-up A–E*,
L400–L447), which B.5 records as not established in the source. The proof (added here) is one-curve:

* infinite lifetime and noncollision: Aux. lemma 6 (`exists_good_clr`);
* right side (`ae_clearance_right`): the probabilistic estimate `ae_exists_clearTime` (a polynomial Lyapunov
  function of the force gaps and the gap-ratio angle, `A5ClearanceJacobi`–`A5ClearanceProb`) and the deterministic
  fence `exists_clearance_right` (`A5ClearanceGeom`);
* left side: the same for the reflected evolution (`IsIntegratedSLEEvolution.reflect`, `mem_fwdHull_reflect_iff`).

Nothing here uses Aux. 7, Theorem 1.2/1.3 or any of their parametrized forms (R48, B.5).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology Complex
open scoped NNReal ENNReal

universe u

namespace InteractingSLE.ZhanGT4.A5Clear

open QuantumZipper

section Right

variable {κ : ℝ} {xL xR ρL ρR : Fin 1 → ℝ} {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}
  {𝓕 : Filtration ℝ≥0 mΩ} {W : ℝ≥0 → Ω → ℝ} {VL VR : Fin 1 → ℝ≥0 → Ω → ℝ} {B : ℝ≥0 → Ω → ℝ}
  {ζ : Ω → ℝ≥0∞}

/-- **Right clearance for the separated two-force law** (`κ > 0`): almost surely the lifetime is infinite and, for
every `M`, the hulls keep a positive distance from `[x_R, M]`. -/
theorem ae_clearance_right [IsProbabilityMeasure P] (hκ : 0 < κ) (hxL : xL 0 < 0) (hxR : 0 < xR 0)
    (hwL : κ / 2 - 2 ≤ ρL 0) (hwR : κ / 2 - 2 ≤ ρR 0)
    (hE : IsIntegratedSLEEvolution κ xL xR ρL ρR P 𝓕 W VL VR B ζ) :
    ∀ᵐ ω ∂P, ζ ω = ⊤ ∧ ∀ M : ℝ, ∃ δ > (0 : ℝ), ∀ t : ℝ,
      ∀ z ∈ fwdHull (fun s : ℝ => W s.toNNReal ω) t, ∀ x ∈ Icc (xR 0) M, δ ≤ ‖z - x‖ := by
  obtain ⟨G, -, hGc, hgood⟩ := exists_good_clr hκ hxL hxR hwL hwR hE
  filter_upwards [ae_exists_clearTime hκ hxL hxR hwL hwR hE, (ae_iff.2 hGc : ∀ᵐ ω ∂P, ω ∈ G)]
    with ω hclear hωG
  have h := hgood ω hωG
  refine ⟨h.2.1, fun M => ?_⟩
  have hveq : ∀ t : ℝ≥0, VR 0 t ω = xR 0 + ∫ s in (0 : ℝ)..t, 2 / (VR 0 s.toNNReal ω - W s.toNNReal ω) :=
    fun t => h.1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 t (h.lt_top t) 0
  exact exists_clearance_right (w := fun t => W t ω) (vR := fun t => VR 0 t ω) h.continuous_w h.1.1
    h.continuous_vR hxR (fun t => (h.2.2.1 t).2) hveq hclear M

end Right

/-! ### The clearance statement -/

/-- **`SeparatedClearanceStatement κ` for every `κ > 4`** (Astra B.3/B.4, R53; proof added here). -/
theorem separatedClearanceStatement (κ : ℝ) : SeparatedClearanceStatement.{u} κ := by
  intro hκ pL pR ρL ρR hpL hpR hρL hρR Ω mΩ P _ 𝓕 W VL VR B ζ hE
  have hκ0 : 0 < κ := by linarith
  have hR := ae_clearance_right (xL := ![pL]) (xR := ![pR]) (ρL := ![ρL]) (ρR := ![ρR]) hκ0
    (by simpa using hpL) (by simpa using hpR) (by simpa using hρL) (by simpa using hρR) hE
  have hE' := IsIntegratedSLEEvolution.reflect hE
  have hL := ae_clearance_right (xL := -![pR]) (xR := -![pL]) (ρL := ![ρR]) (ρR := ![ρL]) hκ0
    (by simpa using hpR) (by simpa using hpL) (by simpa using hρR) (by simpa using hρL) hE'
  filter_upwards [hR, hL] with ω hRω' hLω'
  obtain ⟨hζ, hRω⟩ := hRω'
  obtain ⟨-, hLω⟩ := hLω'
  refine ⟨hζ, fun C hC hCsub => ?_⟩
  obtain ⟨M, hM⟩ := hC.isBounded.exists_norm_le
  obtain ⟨δR, hδR, hRδ⟩ := hRω M
  obtain ⟨δL, hδL, hLδ⟩ := hLω M
  refine ⟨min δR δL, lt_min hδR hδL, fun z hz x hx => ?_⟩
  obtain ⟨t, -, hzt⟩ := mem_iUnion₂.1 hz
  have hxM := hM x hx
  rw [Real.norm_eq_abs, abs_le] at hxM
  rcases hCsub hx with hxL | hxR
  · -- the left ray, through the reflection `z ↦ −z̄`
    have hz' : -(starRingEnd ℂ) z ∈ fwdHull (fun s : ℝ => (-W) s.toNNReal ω) (t : ℝ) := by
      have e : (fun s : ℝ => (-W) s.toNNReal ω) = -(fun s : ℝ => W s.toNNReal ω) := by
        funext s; simp
      rw [e, LoewnerAlgebra.mem_fwdHull_reflect_iff _ t.coe_nonneg]
      exact hzt
    have hxmem : -x ∈ Icc ((-![pL]) 0) M := by
      simp only [Pi.neg_apply, Matrix.cons_val_zero, mem_Icc]
      exact ⟨by simpa using neg_le_neg (show x ≤ pL from hxL), by linarith⟩
    have h1 := hLδ t _ hz' (-x) hxmem
    have h2 : ‖-(starRingEnd ℂ) z - ((-x : ℝ) : ℂ)‖ = ‖z - x‖ := by
      rw [show -(starRingEnd ℂ) z - ((-x : ℝ) : ℂ) = -(starRingEnd ℂ) (z - x) by simp [map_sub]; ring,
        norm_neg, Complex.norm_conj]
    rw [h2] at h1
    exact (min_le_right _ _).trans h1
  · have hxmem : x ∈ Icc ((![pR] : Fin 1 → ℝ) 0) M := ⟨by simpa using hxR, hxM.2⟩
    exact (min_le_left _ _).trans (hRδ t z hzt x hxmem)

end InteractingSLE.ZhanGT4.A5Clear
