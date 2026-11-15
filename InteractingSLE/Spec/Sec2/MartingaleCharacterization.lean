import InteractingSLE.Spec.Sec2.MartingaleCoupling

/-!
# Theorem 2.4, converse implication: the martingale hypothesis gives a Brownian driver

Packet PROVE-SEC2-MART. Specification, Theorem 2.4 (`source/spec/p001-048.md`, anchors `thm-2.4`,
`thm-2.4-proof`, L819–L898). Suppose the driver `W` and the force-point coordinates `V^{i,q}` are
continuous adapted processes with the deterministic properties of geometric force-point images
(ordered, `IsForcePath`: monotone, `dV = 2/(V − W) dt` away from collisions, null collision sets),
and that for every `z ∈ ℍ` the coupling mean `𝔥_t(z)` of Theorem 1.1 — for every choice of the
bounded harmonic extensions — is a local martingale before `z` is swallowed. Then

  `B = M/√κ`,  `M_t = W_t + ½ ∑ⱼ ρⱼ (Vʲ_t − xʲ)`,

is a Brownian motion in the filtration (`isFilteredBrownianReal_of_couplingMean`), so that
`W_t = √κ B_t − ½ ∑ⱼ ρⱼ (Vʲ_t − xʲ)` (`driver_eq_sqrt_mul_sub`). This is the content of the proof
steps "the driving function is a semimartingale", "identification of the quadratic variation and
drift" ((2.6)–(2.7): `d⟨M⟩ = κ dt`) and "`B = M/√κ` is a Brownian motion by Lévy's
characterization" (graph nodes `SPEC.thm-2.4#driver-semimartingale`, `#identify-qv-drift`, and the
Lévy part of `#forward`). The proof route replaces the semimartingale Itô calculus of the source by
the two lowest Laurent coefficients of `𝔥_t(z)` at `∞` (see `MartingaleLaurent`,
`MartingaleCoupling`, `MartingaleLevy`).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter Topology
open QuantumZipper (H)
open scoped NNReal ENNReal

namespace InteractingSLE

namespace MartChar

variable {nL nR : ℕ} {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}
  {𝓕 : Filtration ℝ≥0 mΩ}

/-- **Theorem 2.4, converse implication — the Brownian motion.** If every coupling mean `𝔥_t(z)`
(`z ∈ ℍ`, any bounded harmonic extensions of the force-word data at the centred force points) is a
local martingale before `z` is swallowed, and the coordinates are continuous, adapted, ordered force
paths started at `(0; xL; xR)`, then `M/√κ` is an `𝓕`-Brownian motion,
`M = W − W₀ + ½ ∑ⱼ ρⱼ (Vʲ − Vʲ₀)`. -/
theorem isFilteredBrownianReal_of_couplingMean [IsProbabilityMeasure P] {κ : ℝ} (hκ : 0 < κ)
    {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ} {W : ℝ≥0 → Ω → ℝ} {VL : Fin nL → ℝ≥0 → Ω → ℝ}
    {VR : Fin nR → ℝ≥0 → Ω → ℝ} {xL : Fin nL → ℝ} {xR : Fin nR → ℝ}
    (hW0 : ∀ ω, W 0 ω = 0) (hVL0 : ∀ i ω, VL i 0 ω = xL i) (hVR0 : ∀ i ω, VR i 0 ω = xR i)
    (hWc : ∀ ω, Continuous fun t => W t ω) (hWa : StronglyAdapted 𝓕 W)
    (hVLa : ∀ i, StronglyAdapted 𝓕 (VL i)) (hVRa : ∀ i, StronglyAdapted 𝓕 (VR i))
    (hordL : ∀ ω t i, VL i t ω ≤ W t ω) (hordR : ∀ ω t i, W t ω ≤ VR i t ω)
    (hpathL : ∀ ω i, IsForcePath (fun t => W t ω) (fun t => VL i t ω))
    (hpathR : ∀ ω i, IsForcePath (fun t => W t ω) (fun t => VR i t ω))
    (hmart : ∀ u : Ω → ℝ≥0 → ℂ → ℝ,
      (∀ ω t, IsBoundedHarmonicExtension
        (forceBoundaryData κ ρL ρR (fun i => VL i t ω - W t ω) (fun i => VR i t ω - W t ω))
        (forceJumpSet (fun i => VL i t ω - W t ω) (fun i => VR i t ω - W t ω)) (u ω t)) →
      ∀ z ∈ H, IsLocalMartingaleBefore 𝓕 P
        (fun ω => (QuantumZipper.swallowTime (fun s : ℝ => W s.toNNReal ω) z : WithTop ℝ≥0))
        (fun t ω => couplingMean κ (fun s : ℝ => W s.toNNReal ω) t (u ω t) z)) :
    IsFilteredBrownianReal 𝓕
      (fun t ω => martProc (jointρ ρL ρR) W (jointV VL VR) t ω / Real.sqrt κ) P := by
  have hVLc : ∀ i ω, Continuous fun t => VL i t ω := fun i ω => (hpathL ω i).1
  have hVRc : ∀ i ω, Continuous fun t => VR i t ω := fun i ω => (hpathR ω i).1
  have hmart' : ∀ z ∈ H, IsLocalMartingaleBefore 𝓕 P
      (fun ω => (QuantumZipper.swallowTime (wpath W ω) z : WithTop ℝ≥0))
      (coupProc κ ρL ρR W VL VR z) := fun z hz =>
    hmart (fun ω t => meanExt κ ρL ρR (W t ω) (fun i => VL i t ω) (fun i => VR i t ω))
      (fun ω t => isBoundedHarmonicExtension_meanExt κ ρL ρR (W t ω) _ _) z hz
  have hV0 : ∀ j ω, jointV VL VR j 0 ω = jointV xL xR j := fun j ω => by
    cases j with
    | inl i => exact hVL0 i ω
    | inr i => exact hVR0 i ω
  have hVa : ∀ j, StronglyAdapted 𝓕 (jointV VL VR j) := fun j => by
    cases j with
    | inl i => exact hVLa i
    | inr i => exact hVRa i
  have hpath : ∀ ω j, IsForcePath (fun t => W t ω) (fun t => jointV VL VR j t ω) := fun ω j => by
    cases j with
    | inl i => exact hpathL ω i
    | inr i => exact hpathR ω i
  have hNQ := martingale_driftProc_quadProc_of_couplingMean hκ hW0 hVL0 hVR0 hWc hVLc hVRc hWa
    hVLa hVRa hordL hordR hmart'
  exact isFilteredBrownianReal_martProc_div_sqrt hκ hW0 hV0 hWc hWa hVa hpath
    (fun T N => (hNQ T N).1) (fun T N => (hNQ T N).2)

/-- The semimartingale decomposition of the driver: with `B = M/√κ`,
`W_t = √κ B_t − ½ ∑ⱼ ρⱼ (Vʲ_t − xʲ)`. -/
theorem driver_eq_sqrt_mul_sub {κ : ℝ} (hκ : 0 < κ) {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ}
    {W : ℝ≥0 → Ω → ℝ} {VL : Fin nL → ℝ≥0 → Ω → ℝ} {VR : Fin nR → ℝ≥0 → Ω → ℝ}
    {xL : Fin nL → ℝ} {xR : Fin nR → ℝ} (hW0 : ∀ ω, W 0 ω = 0)
    (hVL0 : ∀ i ω, VL i 0 ω = xL i) (hVR0 : ∀ i ω, VR i 0 ω = xR i) (t : ℝ≥0) (ω : Ω) :
    W t ω = Real.sqrt κ * (martProc (jointρ ρL ρR) W (jointV VL VR) t ω / Real.sqrt κ)
      - (1 / 2) * ((∑ i, ρL i * (VL i t ω - xL i)) + ∑ i, ρR i * (VR i t ω - xR i)) := by
  have hsk : Real.sqrt κ ≠ 0 := (Real.sqrt_pos.2 hκ).ne'
  rw [mul_div_cancel₀ _ hsk]
  simp only [martProc, martValue, jointρ, jointV, Fintype.sum_sum_type, Sum.elim_inl,
    Sum.elim_inr, hW0, hVL0, hVR0]
  ring

end MartChar

end InteractingSLE
