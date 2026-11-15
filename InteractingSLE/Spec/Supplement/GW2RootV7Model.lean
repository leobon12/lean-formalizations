/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW2RootV7Record

/-!
# Finite-force laws on GW2's common driver-record space

Continuation of PROVE-T14-GW2ROOT2. A model contains a varying-angle
integrated evolution, its separated start and a measurable buffer time.
Its law is an actual measurable pushforward. The uniform slow estimate is
proved. Identifying these laws with retained root kernels remains the
explicit named mathematical input `HasAngleDriverModels`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped ENNReal NNReal

universe u

namespace InteractingSLE.Theorem14.GW2TipSystem.RootV7

open Sec5 RootN4 RootL6

/-- Qualitative finite-force model data. Its sample is killed at the
minimum of the buffer time and continuation lifetime. No probability
estimate or full-lifetime trace is a field. -/
structure AngleModel (κ : ℝ) {nL₀ nR₀ : ℕ}
    (ρL₀ : Fin nL₀ → ℝ) (ρR₀ : Fin nR₀ → ℝ) where
  mL : ℕ
  mR : ℕ
  φ : ℕ → ℝ
  hφ : ∀ i, φ i ∈ Icc (-(Real.pi / 2)) (Real.pi / 2)
  xL : Fin (mL + nL₀) → ℝ
  xR : Fin (mR + nR₀ + 1) → ℝ
  a : ℝ
  hy : (a, xL, xR) ∈ Prop59Stage.startsU
  e : EvolutionData.{u} (mL + nL₀) (mR + nR₀ + 1)
  hE : e.IsEvolution κ xL (angleWordL κ φ mL ρL₀) xR (angleWordR κ φ mR ρR₀)
  buffer : e.Ω → ℝ≥0∞
  bufferMeas : @Measurable _ _ e.mΩ _ buffer

/-- The measurable driver sample of this particular model. -/
theorem AngleModel.measurable_sample {κ : ℝ} {nL₀ nR₀ : ℕ}
    {ρL₀ : Fin nL₀ → ℝ} {ρR₀ : Fin nR₀ → ℝ} (m : AngleModel.{u} κ ρL₀ ρR₀) :
    @Measurable _ _ m.e.mΩ _ (modelSample m.e m.a m.buffer) :=
  measurable_modelSample m.e m.hE m.a m.bufferMeas

/-- The actual driver-record law of the finite-force model. -/
def AngleModel.law {κ : ℝ} {nL₀ nR₀ : ℕ}
    {ρL₀ : Fin nL₀ → ℝ} {ρR₀ : Fin nR₀ → ℝ}
    (m : AngleModel.{u} κ ρL₀ ρR₀) : Measure DriverRecord :=
  let _ : MeasurableSpace m.e.Ω := m.e.mΩ
  m.e.P.map (modelSample m.e m.a m.buffer)

/-- One positive slow probability works for all model lengths, angles,
positions, probability spaces and buffer times. -/
theorem exists_uniform_model_bound {κ : ℝ} (hκ : 0 < κ) (hκ4 : κ < 4)
    {nL₀ nR₀ : ℕ} (ρL₀ : Fin nL₀ → ℝ) (ρR₀ : Fin nR₀ → ℝ) :
    ∃ p₀ : ℝ, 0 < p₀ ∧ p₀ ≤ 1 ∧ ∀ m : AngleModel.{u} κ ρL₀ ρR₀,
      ENNReal.ofReal p₀ ≤ m.law slowSet := by
  obtain ⟨p₀, hp₀, hp₀1, hbound⟩ := exists_uniform_unit_bound.{u} hκ hκ4 ρL₀ ρR₀
  refine ⟨p₀, hp₀, hp₀1, fun m => ?_⟩
  let : MeasurableSpace m.e.Ω := m.e.mΩ
  rw [AngleModel.law, Measure.map_apply m.measurable_sample measurableSet_slowSet]
  refine (hbound m.mL m.mR m.φ m.hφ m.xL m.xR m.a m.hy m.e m.hE).trans
    (measure_mono fun ω hω => ?_)
  exact cutRecord_mem_slowSet (driverRecord_mem_slowSet_of_unit hω) (m.buffer ω)

/-- **Unproved retained-model identification input.** At the required even
stages the given kernel law is the driver-record law of an actual model.
No lower probability bound or restart estimate is part of this assertion. -/
def HasAngleDriverModels {Ω Node : Type*} [MeasurableSpace Ω]
    (κ : ℝ) {nL₀ nR₀ : ℕ} (ρL₀ : Fin nL₀ → ℝ) (ρR₀ : Fin nR₀ → ℝ)
    (P : Measure Ω) (A : Node → Set Ω) (depth : Node → ℕ)
    (K : Node → ℕ → Ω → Measure DriverRecord) : Prop :=
  ∀ (k : ℕ) l, depth l = 2 * k + 4 → ∀ a, ∀ᵐ ω ∂P, ω ∈ A l →
    ∃ m : AngleModel.{u} κ ρL₀ ρR₀, m.law = K l a ω

/-- The law-identification input implies the model slow bound with a
constant chosen before all retained states. No measurable selection of
reference models is needed. -/
theorem HasAngleDriverModels.exists_modelSlow
    {Ω Node : Type*} [MeasurableSpace Ω] {κ : ℝ} {nL₀ nR₀ : ℕ}
    {ρL₀ : Fin nL₀ → ℝ} {ρR₀ : Fin nR₀ → ℝ}
    {P : Measure Ω} {A : Node → Set Ω} {depth : Node → ℕ}
    {K : Node → ℕ → Ω → Measure DriverRecord}
    (hModels : HasAngleDriverModels.{u} κ ρL₀ ρR₀ P A depth K)
    (hκ : 0 < κ) (hκ4 : κ < 4) :
    ∃ p₀ : ℝ, 0 < p₀ ∧ p₀ ≤ 1 ∧
      ∀ (k : ℕ) l, depth l = 2 * k + 4 → ∀ a, ∀ᵐ ω ∂P,
        ω ∈ A l → ENNReal.ofReal p₀ ≤ K l a ω slowSet := by
  obtain ⟨p₀, hp₀, hp₀1, hbound⟩ := exists_uniform_model_bound.{u} hκ hκ4 ρL₀ ρR₀
  refine ⟨p₀, hp₀, hp₀1, ?_⟩
  intro k l hl a
  filter_upwards [hModels k l hl a] with ω hω hωA
  obtain ⟨m, hm⟩ := hω hωA
  rw [← hm]
  exact hbound m

end InteractingSLE.Theorem14.GW2TipSystem.RootV7
