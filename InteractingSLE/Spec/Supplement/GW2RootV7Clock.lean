/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW2RootV7Record
import InteractingSLE.Spec.Sec7.LocalExtNRef

/-!
# A slow driver record delays the actual capacity clock

Continuation of PROVE-T14-GW2ROOT2. Rational record observations suffice to
exclude a successful continuous crossing before time one. The source's
actual normalized capacity comparison remains an explicit geometric input.
No raw regularity is inferred from a conditional path-law equality.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped ENNReal NNReal

universe u

namespace InteractingSLE.Theorem14.GW2TipSystem.RootV7

/-- A slow record and its actual rational readings force every continuous
crossing of the target band to occur at time at least one. -/
theorem one_le_of_slow_record {z : DriverRecord} (hz : z ∈ slowSet)
    {Y : ℝ≥0 → ℝ} {t : ℝ≥0}
    (hread : ∀ q : ℚ≥0, ((q : ℝ≥0) : ℝ≥0∞) < z.1 → z.2 q = Y q)
    (hc : ContinuousAt Y t) (ht : (t : ℝ≥0∞) < z.1) (hband : 7 / 4 < Y t) :
    1 ≤ t := by
  refine RootS5.one_le_of_dense_samples LocalExt.dense_range_coe_nnrat hc ht hband ?_
  rintro q ⟨p, rfl⟩ hp1 hpζ
  have hp1' : ((p : ℝ≥0) : ℝ) < 1 := by exact_mod_cast hp1
  have h := hz p hp1' hpζ
  rw [hread p hpζ] at h
  exact h

open Exist Staged StagedLaw Restart LQGMetric RootK3

variable {κ : ℝ} {hκ : 0 < κ} {h12p : Theorem12ParamStatement.{u}}
  {βA : BoundaryWord × ℝ × RecData → BoundaryWord}
  {b : ℝ → ℝ} {jumps : Finset ℝ} {c₀ : BoundaryWord}
  {Ω : Type u} [mΩ : MeasurableSpace Ω]
  {h : Ω → DistOn upperHalfPlaneOpens} {W' : ℝ≥0 → Ω → ℝ}
  {ζ' : Ω → ℝ≥0∞} {Θ : Set ℝ} {Q : Set ℝ≥0} {s : ℝ≥0}
  {P : Measure Ω} {r : ScaledRootIdx Θ Q} {G : Set Ω}
  {d : StageModelData Ω Θ Q DriverRecord (rootSigma hκ h12p βA c₀ h W' ζ' s r)}

/-- The capacity-unit clause follows from the actual record readings and
clock. These raw path assertions are retained as hypotheses; a marginal
model law does not imply them. -/
theorem ae_unit_of_record_clock
    (hSlow : ∀ l a, d.slow l a = slowSet)
    (Y : List (EntryIdx Θ Q) → ℕ → Ω → ℝ≥0 → ℝ)
    (clock : List (EntryIdx Θ Q) → ℕ → Q → Ω → ℝ≥0)
    (hRead : ∀ l a, ∀ᵐ ω ∂P, ω ∈ d.alive G l →
      ∀ q : ℚ≥0, ((q : ℝ≥0) : ℝ≥0∞) < (d.sample l a ω).1 →
        (d.sample l a ω).2 q = Y l a ω q)
    (hClock : ∀ l a, ∀ᵐ ω ∂P, ω ∈ d.alive G l → ∀ q : Q,
      ω ∈ d.tests l a q →
        ContinuousAt (Y l a ω) (clock l a q ω) ∧
        (clock l a q ω : ℝ≥0∞) < (d.sample l a ω).1 ∧
        7 / 4 < Y l a ω (clock l a q ω) ∧
        capR hκ h12p βA b jumps c₀ h W' ζ' s r l ω + clock l a q ω ≤
          capR hκ h12p βA b jumps c₀ h W' ζ' s r ((d.ang a, q) :: l) ω) :
    ∀ l a, ∀ᵐ ω ∂P, ω ∈ d.alive G l →
      d.sample l a ω ∈ d.slow l a → ∀ q : Q, ω ∈ d.tests l a q →
        capR hκ h12p βA b jumps c₀ h W' ζ' s r l ω + 1 ≤
          capR hκ h12p βA b jumps c₀ h W' ζ' s r ((d.ang a, q) :: l) ω := by
  intro l a
  filter_upwards [hRead l a, hClock l a] with ω hr hc hωA hωslow q hωT
  rw [hSlow l a] at hωslow
  obtain ⟨hcont, ht, hband, hcap⟩ := hc hωA q hωT
  have hunit := one_le_of_slow_record hωslow (hr hωA) hcont ht hband
  have hunitR : (1 : ℝ) ≤ clock l a q ω := by exact_mod_cast hunit
  exact (add_le_add le_rfl hunitR).trans hcap

end InteractingSLE.Theorem14.GW2TipSystem.RootV7
