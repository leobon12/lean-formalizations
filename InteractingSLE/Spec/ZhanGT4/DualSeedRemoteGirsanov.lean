/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.ZhanGT4.DualSeedRemoteD10
import MathFin.Probability.Brownian.Girsanov.GirsanovPredictableTheta

/-!
# Girsanov for the seeded density from its Doléans identification

Packet PROVE-ZHAN-GT4-A22. Reuse the bounded predictable Girsanov theorem.
The missing stochastic-calculus identification is a named, exact hypothesis;
it is not replaced by a hypothesis asserting the desired image law.
-/

set_option autoImplicit false

noncomputable section

open Set Filter Topology MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal
open MathFin.ItoIntegralL2

namespace InteractingSLE.ZhanGT4

variable {Ω : Type*} {mΩ : MeasurableSpace Ω}

/-- The normalized terminal density for the seeded change of measure. -/
def seedDensity {n : ℕ} (d : Ω → SeedData n) (S : Ω → ℝ≥0) (ω : Ω) : ℝ :=
  Real.exp ((d ω).normEll (S ω) - (d ω).normEll 0)

/-- The seeded change of measure, with its actual normalized terminal density. -/
def seedMeasure {n : ℕ} (P : Measure Ω) (d : Ω → SeedData n) (S : Ω → ℝ≥0) : Measure Ω :=
  P.withDensity (fun ω => ENNReal.ofReal (seedDensity d S ω))

/-- The candidate market price of risk is the negative logarithmic noise
coefficient before the horizon and vanishes afterwards. Its entrance value
is supplied by a predictable version rather than by the singular formula. -/
def SeedNoiseCoordinate {n : ℕ} (κ : ℝ) (d : Ω → SeedData n) (S : Ω → ℝ≥0)
    (θ : ℝ≥0 → Ω → ℝ) : Prop :=
  (∀ ω u, 0 < u → u ≤ S ω →
    θ u ω = -Real.sqrt κ * (d ω).ellX u ((d ω).W u)) ∧
  (∀ ω u, S ω < u → θ u ω = 0)

/-- The precise remaining Doléans identification for the seeded density.
The deterministic horizon `U` bounds the stopped noise coordinate. -/
def SeedDoleansIdentity {n : ℕ} {P : Measure Ω} [IsProbabilityMeasure P]
    {B : ℝ≥0 → Ω → ℝ} (hB : IsPreBrownianReal B P)
    (hBm : ∀ u, Measurable (B u)) {θ : ℝ≥0 → Ω → ℝ}
    (hpred : IsStronglyPredictable (natFiltration hBm) θ) {C : ℝ}
    (hb : ∀ u ω, |θ u ω| ≤ C) (U : ℝ≥0) (d : Ω → SeedData n) (S : Ω → ℝ≥0) : Prop :=
  seedDensity d S =ᵐ[P] MathFin.ZTpred hB U hBm hpred hb

/-- The seeded density gives the Brownian change of measure once its
explicit Doléans identity has been established. No approximation sequence
or Girsanov theorem is assumed: the existing predictable theorem supplies it. -/
theorem seed_brownianOn_of_doleans {n : ℕ} {P : Measure Ω} [IsProbabilityMeasure P]
    {B : ℝ≥0 → Ω → ℝ} (hB : IsPreBrownianReal B P)
    (hBm : ∀ u, Measurable (B u)) {θ : ℝ≥0 → Ω → ℝ}
    (hpred : IsStronglyPredictable (natFiltration hBm) θ) {C : ℝ}
    (hb : ∀ u ω, |θ u ω| ≤ C) (U : ℝ≥0) (d : Ω → SeedData n) (S : Ω → ℝ≥0)
    (hZ : SeedDoleansIdentity hB hBm hpred hb U d S) :
    MathFin.IsBrownianOn (seedMeasure P d S) U
      (MathFin.BthetaPred (μ := P) U hBm hpred hb) ∧ IsProbabilityMeasure (seedMeasure P d S) := by
  have he : seedMeasure P d S = P.withDensity
      (fun ω => ENNReal.ofReal (MathFin.ZTpred hB U hBm hpred hb ω)) :=
    withDensity_congr_ae (hZ.mono (fun _ hh => congrArg ENNReal.ofReal hh))
  have hBr : MathFin.IsBrownianOn (seedMeasure P d S) U
      (MathFin.BthetaPred (μ := P) U hBm hpred hb) := by
    rw [he]
    exact MathFin.Btheta_isQBrownianMotion_predictable_of_bdd hB hBm hpred hb U
  refine ⟨hBr, ?_⟩
  have hm : (seedMeasure P d S).map (fun _ : Ω => (0 : ℝ)) = gaussianReal 0 0 := by
    simpa using hBr.2.1 (s := 0) (t := 0) le_rfl (zero_le (a := U))
  have hprob : IsProbabilityMeasure ((seedMeasure P d S).map (fun _ : Ω => (0 : ℝ))) := by
    rw [hm]
    infer_instance
  exact Measure.isProbabilityMeasure_of_map (f := fun _ : Ω => (0 : ℝ)) measurable_const.aemeasurable

/-- The predictable noise coordinate gives exactly the seeded Girsanov
drift that enters the already checked (D10) cancellation. -/
theorem SeedNoiseCoordinate.drift_eq_dualQ {n : ℕ} {κ : ℝ} {d : Ω → SeedData n}
    {S : Ω → ℝ≥0} {θ : ℝ≥0 → Ω → ℝ} (hθ : SeedNoiseCoordinate κ d S θ)
    (hκ : 0 ≤ κ) (hdκ : ∀ ω, (d ω).κ = κ) (ω : Ω) {u : ℝ≥0}
    (hu : 0 < u) (huS : u ≤ S ω) :
    (d ω).drift u - Real.sqrt κ * θ u ω =
      κ * dualQ κ ((d ω).A 1 u) ((d ω).A 2 u) ((d ω).A 0 u - (d ω).A20 u)
        (d ω).r (fun m => (d ω).A 0 u - (d ω).B0 u m) := by
  rw [hθ.1 ω u hu huS]
  have he := (d ω).drift_add_kappa_mul_ellX u
  rw [hdκ ω] at he
  calc (d ω).drift u - Real.sqrt κ * (-Real.sqrt κ * (d ω).ellX u ((d ω).W u)) =
      (d ω).drift u + (Real.sqrt κ) ^ 2 * (d ω).ellX u ((d ω).W u) := by ring
    _ = (d ω).drift u + κ * (d ω).ellX u ((d ω).W u) := by rw [Real.sq_sqrt hκ]
    _ = _ := he

end InteractingSLE.ZhanGT4
