/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec5.TwoMarkNoise10Obs

/-!
# Normalized local first-mark noise martingales

The capped observable identities turn the existing inverse-time observable
martingales into the noise, its quadratic correction and its exponentials.
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory Set Filter Topology
open scoped NNReal ENNReal Classical

namespace InteractingSLE.Sec5.TwoMark.Noise10

open Zhan.Retarget

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} {𝓘 : Filtration ℝ≥0 mΩ}
  {κ a b : ℝ} {xL ρL : Fin 0 → ℝ} {ρR : Fin 2 → ℝ}
  {W B : ℝ≥0 → Ω → ℝ} {VL : Fin 0 → ℝ≥0 → Ω → ℝ} {VR : Fin 2 → ℝ≥0 → Ω → ℝ}
  {e : Ω → ℝ≥0∞} {S : ℕ → Ω → ℝ≥0} {G : Set Ω}

variable (hκ : 0 < κ) (ha : 0 < a) (hab : a < b)
  (hgood : ∀ ω ∈ G, Mart9.IsGood κ a b xL ρL ρR W B VL VR e S ω)

include hκ ha hab hgood in
/-- Center and rescale the transported observable martingale. -/
theorem martingale_localNoise_stopped [IsFiniteMeasure P]
    (hObs : ∀ n, Martingale (fun u ω => obs κ xL ![a, b] ρL ρR 0
      (cappedPoint xL a b G S W B VL VR e n u ω)) 𝓘 P) (n : ℕ) :
    Martingale (fun u ω => localNoise κ a b xL ρL ρR G W B VL VR
      (min u (imageStops a G S W B VL VR e n ω)) ω) 𝓘 P := by
  let c := obs κ xL ![a, b] ρL ρR 0 (rInit xL ![a, b] a)
  have h := Martingale.smul (1 / Real.sqrt κ) ((hObs n).sub (martingale_const 𝓘 P c))
  convert h using 1
  funext u ω
  simp only [Pi.smul_apply, smul_eq_mul, Pi.sub_apply]
  rw [localNoise_min_eq hκ ha hab hgood]
  simp only [c, div_eq_mul_inv, one_mul, mul_comm]

include hκ ha hab hgood in
/-- Rescaling the transported quadratic observable gives the unit quadratic clock. -/
theorem martingale_localNoise_sq_stopped
    (hObs2 : ∀ c n, Martingale (fun u ω => obs2 κ xL ![a, b] ρL ρR 0 c
      (cappedPoint xL a b G S W B VL VR e n u ω)) 𝓘 P) (n : ℕ) :
    Martingale (fun u ω => localNoise κ a b xL ρL ρR G W B VL VR
      (min u (imageStops a G S W B VL VR e n ω)) ω ^ 2 -
      ((min u (imageStops a G S W B VL VR e n ω) : ℝ≥0) : ℝ)) 𝓘 P := by
  let c := obs κ xL ![a, b] ρL ρR 0 (rInit xL ![a, b] a)
  have h := Martingale.smul (1 / κ) (hObs2 c n)
  convert h using 1
  funext u ω
  simp only [Pi.smul_apply, smul_eq_mul, obs2]
  rw [obs_cappedPoint hκ ha hab hgood, clock_cappedPoint_all ha hab hgood]
  dsimp only [c]
  rw [add_sub_cancel_right, mul_pow, Real.sq_sqrt hκ.le]
  field_simp

include hκ ha hab hgood in
/-- Removing the initial exponential factor gives the normalized exponential martingale. -/
theorem martingale_exp_localNoise_stopped
    (hExp : ∀ θ n, Martingale (fun u ω => expObs κ xL ![a, b] ρL ρR 0 θ
      (cappedPoint xL a b G S W B VL VR e n u ω)) 𝓘 P) (θ : ℝ) (n : ℕ) :
    Martingale (fun u ω => Real.exp (θ * localNoise κ a b xL ρL ρR G W B VL VR
      (min u (imageStops a G S W B VL VR e n ω)) ω -
      θ ^ 2 * ((min u (imageStops a G S W B VL VR e n ω) : ℝ≥0) : ℝ) / 2)) 𝓘 P := by
  let c := obs κ xL ![a, b] ρL ρR 0 (rInit xL ![a, b] a)
  have h := Martingale.smul (Real.exp (-(θ / Real.sqrt κ * c))) (hExp θ n)
  convert h using 1
  funext u ω
  simp only [Pi.smul_apply, smul_eq_mul, expObs]
  rw [obs_cappedPoint hκ ha hab hgood, clock_cappedPoint_all ha hab hgood, ← Real.exp_add]
  dsimp only [c]
  congr 1
  field_simp
  ring

end InteractingSLE.Sec5.TwoMark.Noise10
