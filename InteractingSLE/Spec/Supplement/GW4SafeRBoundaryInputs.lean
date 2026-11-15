/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW4SafeRBoundaryChart

/-!
# GW4: the remaining incident boundary germs

Only boundary limits of the actual local-set mean are recorded here. The
harmonic representative is the existing `harmRep`, and the bounded extension,
growth estimate and full-fiber uniqueness are proved by the consumer.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Filter Topology Metric MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal
open QuantumZipper (H Hbar chiC fwdMapInv fwdHull logDerivFwd)
open LQGMetric (DistOn)

namespace InteractingSLE.Theorem14.GW4Fix

open Restart Exist.StagedLaw Sec7.PhaseSel Sec7.Aux119Heights
  Supp8.Q3Stop LocalSets WholeField MartChar

/-- **Open boundary input.** At every live physical line, the current inverse
extends continuously and the corrected harmonic mean has the phase word's
germs away from finitely many physical exceptions. Every fiber over an
exception is excluded; no prime-end finiteness or Poisson identity is assumed. -/
def ComponentIncidentGerms {Ω : Type*} [MeasurableSpace Ω]
    (k : ℝ) (c₀ : BoundaryWord) (F : Frame) (ν : Measure Ω)
    (X : Ω → DistOn upperHalfPlaneOpens) (Wd : ℝ≥0 → Ω → ℝ) (GT : Set Ω)
    (R : ℝ≥0 → Ω → ℝ) (V : Ω → ℝ≥0∞) (u₀ : ℂ → ℝ)
    (B : ℝ≥0 → Ω → Set ℂ) (d : ℝ≥0 → Ω → ℝ) : Prop :=
  ∀ t (g : Ω → DistOn upperHalfPlaneOpens), IsLocalSetMean (B t) (centredField X u₀) ν g →
    ∀ᵐ ω ∂ν, lineClock F Wd GT V t ω < V ω →
      let q := (lineClock F Wd GT V t ω).toNNReal
      let inv := fwdMapInv (wpath R ω) q
      let vL := fun i => componentVL k c₀ X R V i q ω - R q ω
      let vR := fun j => componentVR k c₀ X R V j q ω - R q ω
      ∃ (Fb : ℂ → ℂ) (E : Set ℂ), EqOn Fb inv H ∧ ContinuousOn Fb Hbar ∧ E.Finite ∧
        ∀ x : ℝ, x ∉ forceJumpSet vL vR → Fb x ∉ E →
          Tendsto (fun y => harmRep (g ω) (H \ B t ω) (inv y) + u₀ (inv y) +
              chiC k * (logDerivFwd (wpath R ω) q (inv y)).im)
            (𝓝[H] (x : ℂ))
            (𝓝 (phaseData k (typedRhoL (wordType k c₀)) (typedRhoR (wordType k c₀))
              vL vR (d q ω) x))

/-- Adding the bounded initial mean preserves the global logarithmic growth
bound used by the physical-exception uniqueness theorem. -/
theorem log_growth_add_bounded {S : Set ℂ} {v u : ℂ → ℝ} {K M : ℝ}
    (hv : ∀ z ∈ S, |v z| ≤ K * (1 + Real.log (1 + ‖z‖) +
      Real.log (1 + 1 / infDist z Sᶜ))) (hu : ∀ z ∈ S, |u z| ≤ M) :
    ∀ z ∈ S, |v z + u z| ≤ (max K 0 + max M 0) *
      (1 + Real.log (1 + ‖z‖) + Real.log (1 + 1 / infDist z Sᶜ)) := by
  intro z hz
  let b := 1 + Real.log (1 + ‖z‖) + Real.log (1 + 1 / infDist z Sᶜ)
  have hb : 1 ≤ b := by
    have h₁ := Real.log_nonneg (show 1 ≤ 1 + ‖z‖ by linarith only [norm_nonneg z])
    have h₂ := Real.log_nonneg (show 1 ≤ 1 + 1 / infDist z Sᶜ by
      linarith only [one_div_nonneg.2 (infDist_nonneg (x := z) (s := Sᶜ))])
    linarith only [h₁, h₂]
  have hv' : |v z| ≤ max K 0 * b :=
    (hv z hz).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (zero_le_one.trans hb))
  have hu' : |u z| ≤ max M 0 * b :=
    ((hu z hz).trans (le_max_left _ _)).trans
      (le_mul_of_one_le_right (le_max_right _ _) hb)
  exact (abs_add_le _ _).trans (by rw [add_mul]; exact add_le_add hv' hu')

/-- The actual component seed coordinates are on their own sides of the
driver, so the phase-word bounded extension exists at every relative time. -/
theorem component_seed_sides {Ω : Type*} {k : ℝ} {c₀ : BoundaryWord}
    {X : Ω → DistOn upperHalfPlaneOpens} {R : ℝ≥0 → Ω → ℝ} {V : Ω → ℝ≥0∞}
    (hR0 : ∀ ω, R 0 ω = 0) (hRc : ∀ ω, Continuous (R · ω)) (ω : Ω) (q : ℝ≥0) :
    componentVL k c₀ X R V (componentSeedL k c₀) q ω - R q ω ≤ 0 ∧
      0 ≤ componentVR k c₀ X R V (componentSeedR k c₀) q ω - R q ω := by
  rw [componentVL_eq_geom k c₀ X R V (hRc ω) (hR0 ω),
    componentVR_eq_geom k c₀ X R V (hRc ω) (hR0 ω)]
  exact ⟨sub_nonpos.2 (Sec7.PocketTraversal.geomLW_le hRc _ ω q _),
    sub_nonneg.2 (Sec7.PocketTraversal.le_geomRW hRc _ ω q _)⟩

end InteractingSLE.Theorem14.GW4Fix
