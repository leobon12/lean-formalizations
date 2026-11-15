/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec2.OneForceExists
import InteractingSLE.Spec.ZhanGT4.MixtureA32Strip

/-!
# A.3.2: ordinary chordal `SLE_κ` as a strip evolution on a given Brownian motion

Packet PROVE-ZHAN-A34. Source: Astra, *Follow-up proofs and dependency audit*, §A.3.2
(`source/external/AstraIG1/ig1_followup_proofs.txt` L657–L697, ruling R38): "By the target-change identity, ordinary
SLE stopped at `T_x` becomes the strip chain `ξ_t = √κ B_t + σ t`".

In the R36 form (`Strip.IsStripSLEEvolution`) a strip chain is the chordal evolution of the exponential image with an
end mark at `−1`. For ordinary `SLE_κ` the end mark has weight `τ₋ = 0`: it is the reflecting Bessel mark of the
one-force construction (2.3) with `ρ = 0` (PROVE-SEC2-ONE's `OneForce.isIntegratedSLEEvolution_left`). Its lifetime is
`∞` (the Bessel case `c = 2/κ > 0`), and since its weight is `0`, the driver is `√κ B` at every time.

## Main results

* `ordW`, `ordV`: the driver and the end mark of the construction;
* `isStripSLEEvolution_ord`: **ordinary `SLE_κ` is the R36 strip evolution with no lower marks and `τ₋ = 0`**, on
  any filtered probability space carrying a Brownian motion with continuous paths started at `0`, with lifetime `∞`;
* `ae_ordW_eq`: almost surely `ordW κ B t = √κ B_t` for every `t`;
* `exists_map_stripDriver_ord_eq_mixLaw`: for `4 < κ < 8`, the strip driver law of this evolution is the
  `f(u) du`-mixture of the forced laws (PROVE-ZHAN-A32's `exists_map_stripDriver_eq_mixLaw` applied to it).
-/

set_option autoImplicit false

noncomputable section

open Set Filter Topology MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace InteractingSLE.ZhanGT4.A34

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
  {B : ℝ≥0 → Ω → ℝ} {κ : ℝ}

/-- The driver of ordinary `SLE_κ` in the one-force construction with the zero-weight mark at `−1`. -/
def ordW (κ : ℝ) (B : ℝ≥0 → Ω → ℝ) : ℝ≥0 → Ω → ℝ := OneForce.leftWProc κ (-1) 0 B

/-- The zero-weight end mark at `−1` (the reflecting Bessel mark of (2.3) with `ρ = 0`). -/
def ordV (κ : ℝ) (B : ℝ≥0 → Ω → ℝ) : ℝ≥0 → Ω → ℝ := OneForce.leftVProc κ (-1) 0 B

/-- The lifetime of the one-force construction with `ρ = 0` is `∞` (the Bessel case). -/
theorem leftζ_eq_top (hκ : 0 < κ) (ω : Ω) : OneForce.leftζ κ (-1) 0 B ω = ⊤ := by
  have hc : 0 < (0 + 2) / κ := by positivity
  simp only [OneForce.leftζ, OneForce.oneζ, hc, ↓reduceIte]

theorem wordXL_nil : Strip.wordXL (![] : Fin 0 → ℝ) = ![-1] := by
  funext i
  fin_cases i
  exact Strip.wordXL_last _

theorem wordXR_nil : Strip.wordXR (![] : Fin 0 → ℝ) = ![] := funext fun i => i.elim0

theorem wordRhoL_nil : Strip.wordRhoL (![] : Fin 0 → ℝ) 0 = ![0] := by
  funext i
  fin_cases i
  simp [Strip.wordRhoL]

/-- **Ordinary `SLE_κ` as the R36 strip evolution** with no lower marks and end weight `τ₋ = 0`, on any filtered
probability space carrying a Brownian motion with continuous paths started at `0`; its lifetime is `∞`. -/
theorem isStripSLEEvolution_ord (hκ : 0 < κ) (hB : IsFilteredBrownianReal 𝓕 B P)
    (hBc : ∀ ω, Continuous (B · ω)) (hB0 : ∀ ω, B 0 ω = 0) :
    Strip.IsStripSLEEvolution κ (![] : Fin 0 → ℝ) (![] : Fin 0 → ℝ) ![] ![] 0 P 𝓕 (ordW κ B)
      (fun _ => ordV κ B) (fun i => i.elim0) B (fun _ => ⊤) := by
  have h := OneForce.isIntegratedSLEEvolution_left (P := P) hκ (xL := ![-1]) (xR := ![]) (ρL := ![0])
    (ρR := ![]) (by norm_num) hB hBc hB0 (fun i => i.elim0)
  have hζ : OneForce.leftζ κ (![-1] 0) (![0] 0) B = fun _ => ⊤ := funext fun ω => leftζ_eq_top hκ ω
  simp only [Matrix.cons_val_fin_one] at h hζ
  rw [hζ] at h
  unfold Strip.IsStripSLEEvolution
  rw [wordXL_nil, wordXR_nil, wordRhoL_nil]
  exact h

/-- **The driver is `√κ B` at every time**, almost surely (the zero weight removes the drift). -/
theorem ae_ordW_eq (hκ : 0 < κ) (hB : IsFilteredBrownianReal 𝓕 B P) (hBc : ∀ ω, Continuous (B · ω))
    (hB0 : ∀ ω, B 0 ω = 0) : ∀ᵐ ω ∂P, ∀ t, ordW κ B t ω = Real.sqrt κ * B t ω := by
  have hE := isStripSLEEvolution_ord hκ hB hBc hB0
  filter_upwards [hE.2.2.2.2] with ω hp t
  have hw := hp.2.2.2.2.2.2.2.2.2.2.2.2.1 t (by simp)
  beta_reduce at hw
  have h0 : ∀ i : Fin 1, Strip.wordRhoL (![] : Fin 0 → ℝ) 0 i = 0 := by
    intro i; fin_cases i; exact Strip.wordRhoL_last _ _
  simp only [h0, zero_div, intervalIntegral.integral_zero, Finset.sum_const_zero, Finset.univ_eq_empty,
    Finset.sum_empty, add_zero] at hw
  exact hw

/-- **(G3) for ordinary `SLE_κ` on a given Brownian motion**, `4 < κ < 8`: the strip driver law of the construction
is the `f(u) du`-mixture of the forced laws `mixLaw P κ (3 − κ/2) B'`, for a Brownian motion `B'` (every path
continuous, `B'₀ = 0`). -/
theorem exists_map_stripDriver_ord_eq_mixLaw (hκ4 : 4 < κ) (hκ8 : κ < 8) (hB : IsFilteredBrownianReal 𝓕 B P)
    (hBc : ∀ ω, Continuous (B · ω)) (hB0 : ∀ ω, B 0 ω = 0) :
    ∃ (𝓗 : Filtration ℝ≥0 mΩ) (B' : ℝ≥0 → Ω → ℝ), IsFilteredBrownianReal 𝓗 B' P ∧ (∀ ω, Continuous (B' · ω)) ∧
      (∀ ω, B' 0 ω = 0) ∧
      P.map (fun ω (t : ℝ≥0) => Strip.stripDriver (Strip.extPath (ordW κ B · ω)) (Strip.extPath (ordV κ B · ω)) t) =
        Mix.mixLaw P κ (3 - κ / 2) B' := by
  have hE := isStripSLEEvolution_ord (by linarith) hB hBc hB0
  exact Mix.exists_map_stripDriver_eq_mixLaw (VL := fun _ => ordV κ B) (VR := fun i => i.elim0) hκ4 hκ8 hE

end InteractingSLE.ZhanGT4.A34
