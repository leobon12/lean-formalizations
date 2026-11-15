/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.SB2VjJoint
import InteractingSLE.Spec.Supplement.SB2VjEnt

/-!
# SB2(1)'s version half: the relative lift, measurable at every relative time

Packet PROVE-AUX61-NOJUMP (Theorem 1.4, SB2(1)'s version half, ruling R108).

* **`exists_measurable_relLift`**: for every clock `a` measurable at each time and a.s. equal to
  `Vc.clockOf (flowLift)`, there is `ρ : Ω → ℝ≥0 → ℂ` measurable at every relative time `s` with, almost surely at a
  launch on the entrance event, `ρ ω s = flowLift ω s` for every `s` before the remaining lifetime.

`ρ ω s` is the jointly measurable absolute lift (`Vj.exists_joint_absLift`) read at the measurable entrance
(`Vj.entMeas a`, a.s. `T_L`, `Vj.ae_entMeas_eq`) plus `s`. This is the measurability input of
`Lk.exists_measurable_driver_of_drivenCurves` for the version's driver. Theorem 1.3 and the named S3 input as before
(R48).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped NNReal ENNReal
open LQGMetric (DistOn)

universe u

namespace InteractingSLE.Theorem14.SB.Vj

open Lv Exist.Staged Exist.StagedLaw

variable {κ : ℝ} {b : ℝ → ℝ} {jumps : Finset ℝ} {Ω : Type u} [MeasurableSpace Ω] [StandardBorelSpace Ω]
  {P : Measure Ω} [IsProbabilityMeasure P] {h : Ω → DistOn upperHalfPlaneOpens}
  {E : ExplSpec → ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞} {k : ℕ} {u ψ : ℝ} {η : Ω → ℝ≥0 → ℂ} {ζ : Ω → ℝ≥0∞}
  {u₀ : ℂ → ℝ}

/-- **The relative lift, measurable at every relative time.** -/
theorem exists_measurable_relLift (h13 : Exist.Theorem13Statement.{u})
    (hS3 : Tc.SB2EntranceNoCommonArcStatement.{u}) (HP : SB2LaunchProblem κ b jumps P h E k u ψ η ζ)
    (I : K2LaunchInputs κ b jumps P h E k u ψ) (D : EntranceUnion κ b jumps P h E k u η ζ u₀)
    {a : ℝ≥0 → Ω → ℝ≥0∞} (ha : ∀ t, Measurable (a t))
    (hae : ∀ᵐ ω ∂P, ω ∈ launchSet κ b jumps E (k + 1) → Ve.entT κ b jumps E k u η ζ ω < ζ ω →
      ∀ t, a t ω = Vc.clockOf (Ve.flowLift κ b jumps E k u η ζ ω) (Ve.entT κ b jumps E k u η ζ ω).toNNReal
        (ζ ω) t) :
    ∃ ρ : Ω → ℝ≥0 → ℂ, (∀ s, Measurable fun ω => ρ ω s) ∧
      ∀ᵐ ω ∂P, ω ∈ launchSet κ b jumps E (k + 1) → Ve.entT κ b jumps E k u η ζ ω < ζ ω →
        ∀ s : ℝ≥0, (((Ve.entT κ b jumps E k u η ζ ω).toNNReal + s : ℝ≥0) : ℝ≥0∞) < ζ ω →
          ρ ω s = Ve.flowLift κ b jumps E k u η ζ ω s := by
  obtain ⟨G, F, hGm, hGn, hFm, hF⟩ := exists_joint_absLift h13 hS3 HP I D
  refine ⟨fun ω s => F (ω, (entMeas a ω).toNNReal + s), fun s =>
    hFm.comp (measurable_id.prodMk ((measurable_entMeas ha).ennreal_toNNReal.add_const s)), ?_⟩
  have hGae : ∀ᵐ ω ∂P, ω ∈ G := by rw [ae_iff]; exact hGn
  filter_upwards [ae_entMeas_eq h13 hS3 HP hae, D.ae_mem_event_iff, hGae] with ω hent hev hωG hF' hT s hs
  have hωE : ω ∈ D.event := (hev hF').2 hT
  show F (ω, (entMeas a ω).toNNReal + s) = _
  rw [hent hF' hT, hF ω ⟨hωG, hωE⟩ _ hs]
  unfold Vi.absLift
  rw [add_tsub_cancel_left]

end InteractingSLE.Theorem14.SB.Vj
