import InteractingSLE.WangWu.CouplingFrozenTwo
import InteractingSLE.Spec.Coupling.Fubini
import QuantumZipper.Proofs.Thm11.FieldMartingales

/-!
# Wang–Wu at `κ = 4`: the tested frozen mean (Lemma 3.6, integrated form), conditional on a measurable version

Packet PROVE-WW-A. Source: `source/external/WW17LP/wang_wu_lean_preprocessed.pdf`, §3, Lemma 3.6
("`M_t(p) = ∫ p(z)(η_t(z) − η_0(z)) dz` … Conditional Fubini applied to the stopped pointwise martingales gives the
martingale property … Fubini implies that `M_t(p)² + E_t(p)` is a martingale"), ruling R31.

The pointwise martingales are proved (`exists_martingale_frozenMean`,
`exists_martingale_frozenMean_mul_add_retainedGreen`). Integrating them against a test function needs a version of
the frozen mean that is jointly measurable in `(z, ω)` for `Borel(ℂ) ⊗ 𝓖_t` (the landed
`Coupling.martingale_integral_of_forall`). That version is the one missing input; it is taken here as an explicit
hypothesis of conditional helpers with distinct names:

* `martingale_integral_frozenMean_of_version`: if `Yv` is a jointly measurable, bounded version of
  `(t, z, ω) ↦ η̄_{t∧σ₀}(z)` (for each `z ∈ ℍ`, almost surely for all `t`), then `t ↦ ∫ φ(z) Yv_t(z) dz` is a martingale
  for every integrable `φ` vanishing off `ℍ`.
* `martingale_integral_frozenMean_two_of_version`: the same for the two-point process
  `η̄(y) η̄(z) + G_U(y, z)` against `φ ⊗ φ`, whose integral is `M_t(φ)² + E_t(φ)` up to the diagonal.

**Missing proposition (obstruction M of the handoff).** For a marked chain and a bounded stopping time `σ₀ < T` of
the usual augmentation: there is `Yv : ℝ≥0 → ℂ → Ω → ℝ`, `Measurable[borel ℂ ⊗ 𝓖_t] (p ↦ Yv t p.1 p.2)` for every `t`,
`|Yv| ≤ meanBound`, with `∀ z ∈ ℍ, ∀ᵐ ω, ∀ t, Yv t z ω = frozenMean … (t ∧ σ₀ ω) z` (and the analogue for the
two-point process).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology QuantumZipper
open scoped NNReal ENNReal

namespace InteractingSLE

namespace WangWu

variable {nL nR : ℕ}

section Tested

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
  {xL : Fin nL → ℝ} {xR : Fin nR → ℝ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ} {W : ℝ≥0 → Ω → ℝ}
  {VL : Fin nL → ℝ≥0 → Ω → ℝ} {VR : Fin nR → ℝ≥0 → Ω → ℝ} {B : ℝ≥0 → Ω → ℝ} {ζ : Ω → ℝ≥0∞}

/-- Constant set integrals for a process that agrees almost surely with a martingale. -/
theorem setIntegral_eq_of_ae_eq_martingale [IsFiniteMeasure P] {𝓖 : Filtration ℝ≥0 mΩ}
    {M X : ℝ≥0 → Ω → ℝ} (hM : Martingale M 𝓖 P) (hX : ∀ᵐ ω ∂P, ∀ t, M t ω = X t ω) {s t : ℝ≥0}
    (hst : s ≤ t) {S : Set Ω} (hS : MeasurableSet[𝓖 s] S) :
    ∫ ω in S, X s ω ∂P = ∫ ω in S, X t ω ∂P := by
  have e : ∀ u, ∫ ω in S, X u ω ∂P = ∫ ω in S, M u ω ∂P := fun u =>
    setIntegral_congr_ae (𝓖.le s _ hS) (hX.mono fun ω h _ => (h u).symm)
  rw [e s, e t]
  exact hM.setIntegral_eq hst hS

/-- **Lemma 3.6, the tested mean, conditional on a jointly measurable version** (distinct name: the version is the
missing input M). For an integrable `φ` vanishing off `ℍ`, `t ↦ ∫ φ(z) Yv_t(z) dz` is a martingale. -/
theorem martingale_integral_frozenMean_of_version [IsProbabilityMeasure P]
    (hE : IsMarkedChain xL xR ρL ρR P 𝓕 W VL VR B ζ) {σ₀ : Ω → ℝ≥0}
    (hσ₀ : IsStoppingTime (usualAugmentation 𝓕 P) fun ω => (σ₀ ω : WithTop ℝ≥0))
    (hσ₀ζ : ∀ᵐ ω ∂P, (σ₀ ω : ℝ≥0∞) < ζ ω) {N : ℝ≥0} (hσ₀N : ∀ ω, σ₀ ω ≤ N)
    {φ : ℂ → ℝ} (hφm : Measurable φ) (hφi : Integrable φ) (hφH : ∀ z, z ∉ H → φ z = 0)
    {Yv : ℝ≥0 → ℂ → Ω → ℝ}
    (hYvm : ∀ t, Measurable[(borel ℂ).prod (usualAugmentation 𝓕 P t)] (fun p : ℂ × Ω => Yv t p.1 p.2))
    (hYvb : ∀ t z ω, |Yv t z ω| ≤ meanBound ρL ρR)
    (hYv : ∀ z ∈ H, ∀ᵐ ω ∂P, ∀ t, Yv t z ω =
      frozenMean ρL ρR (W · ω) (fun i => (VL i · ω)) (fun i => (VR i · ω)) (min t (σ₀ ω)) z) :
    Martingale (fun t ω => ∫ z, φ z * Yv t z ω) (usualAugmentation 𝓕 P) P := by
  set C := meanBound ρL ρR
  refine Coupling.martingale_integral_of_forall (μ := (volume : Measure ℂ))
    (Y := fun t z ω => φ z * Yv t z ω) (fun t => (hφm.comp measurable_fst).mul (hYvm t))
    (g := fun z => |φ z| * C) (hφi.abs.mul_const C)
    (Eventually.of_forall fun z t ω => by
      rw [abs_mul]; exact mul_le_mul_of_nonneg_left (hYvb t z ω) (abs_nonneg _))
    (Eventually.of_forall fun z s t hst S hS => ?_)
  by_cases hz : z ∈ H
  · obtain ⟨-, M, hM, hMe⟩ := exists_martingale_frozenMean (ρL := ρL) (ρR := ρR) hE hz hσ₀ hσ₀ζ hσ₀N
    have hMY : ∀ᵐ ω ∂P, ∀ t, M t ω = Yv t z ω := by
      filter_upwards [hMe, hYv z hz] with ω h1 h2 t
      rw [h1 t, h2 t]
    simp only [integral_const_mul]
    rw [setIntegral_eq_of_ae_eq_martingale (X := fun t ω => Yv t z ω) hM hMY hst hS]
  · simp [hφH z hz]

/-- **Lemma 3.6, the two-point identity integrated, conditional on a jointly measurable version** (distinct name:
the version is the missing input M). For a continuous `φ` with compact support at height `≥ δ > 0`,
`t ↦ ∬ φ(y) φ(z) Y2_t(y, z)` is a martingale, where `Y2` is a version of `η̄(y) η̄(z) + G_U(y, z)`; its value is
`M_t(φ)² + E_t(φ)` (the integral of the product of frozen means is the square of the tested mean). -/
theorem martingale_integral_frozenMean_two_of_version [IsProbabilityMeasure P]
    (hE : IsMarkedChain xL xR ρL ρR P 𝓕 W VL VR B ζ) {σ₀ : Ω → ℝ≥0}
    (hσ₀ : IsStoppingTime (usualAugmentation 𝓕 P) fun ω => (σ₀ ω : WithTop ℝ≥0))
    (hσ₀ζ : ∀ᵐ ω ∂P, (σ₀ ω : ℝ≥0∞) < ζ ω) {N : ℝ≥0} (hσ₀N : ∀ ω, σ₀ ω ≤ N)
    {φ : ℂ → ℝ} (hφc : Continuous φ) (hφs : HasCompactSupport φ) {δ : ℝ} (hδ : 0 < δ)
    (hφδ : ∀ a : ℂ, a.im < δ → φ a = 0)
    {Y2 : ℝ≥0 → ℂ × ℂ → Ω → ℝ}
    (hY2m : ∀ t, Measurable[MeasurableSpace.prod inferInstance (usualAugmentation 𝓕 P t)]
      (fun q : (ℂ × ℂ) × Ω => Y2 t q.1 q.2))
    (hY2b : ∀ t (p : ℂ × ℂ) ω, p.1 ∈ H → p.2 ∈ H → p.1 ≠ p.2 →
      |Y2 t p ω| ≤ meanBound ρL ρR ^ 2 + greenH p.1 p.2)
    (hY2 : ∀ y ∈ H, ∀ z ∈ H, y ≠ z → ∀ᵐ ω ∂P, ∀ t, Y2 t (y, z) ω =
      frozenMean ρL ρR (W · ω) (fun i => (VL i · ω)) (fun i => (VR i · ω)) (min t (σ₀ ω)) y *
        frozenMean ρL ρR (W · ω) (fun i => (VL i · ω)) (fun i => (VR i · ω)) (min t (σ₀ ω)) z +
      retainedGreen (W · ω) (min t (σ₀ ω)) y z) :
    Martingale (fun t ω => ∫ p, φ p.1 * φ p.2 * Y2 t p ω ∂((volume : Measure ℂ).prod volume))
      (usualAugmentation 𝓕 P) P := by
  set C := meanBound ρL ρR
  have hφi : Integrable φ := hφc.integrable_of_hasCompactSupport hφs
  have hH : ∀ a : ℂ, φ a ≠ 0 → a ∈ H := fun a ha => by
    by_contra h
    exact ha (hφδ a (lt_of_le_of_lt (not_lt.1 h) hδ))
  have hg : Integrable (fun p : ℂ × ℂ => |φ p.1| * |φ p.2| * (C ^ 2 + greenH p.1 p.2))
      ((volume : Measure ℂ).prod volume) := by
    have h1 : Integrable (fun p : ℂ × ℂ => |φ p.1| * |φ p.2| * C ^ 2)
        ((volume : Measure ℂ).prod volume) :=
      (hφi.abs.mul_prod hφi.abs).mul_const _
    have h2 := FieldMart.integrable_rho_rho_greenH hφc hφs hδ hφδ
    refine (h1.add h2).congr (Eventually.of_forall fun p => ?_)
    show |φ p.1| * |φ p.2| * C ^ 2 + |φ p.1| * |φ p.2| * greenH p.1 p.2 =
      |φ p.1| * |φ p.2| * (C ^ 2 + greenH p.1 p.2)
    ring
  refine Coupling.martingale_integral_of_forall (μ := (volume : Measure ℂ).prod volume)
    (Y := fun t p ω => φ p.1 * φ p.2 * Y2 t p ω)
    (fun t => ((hφc.measurable.comp (measurable_fst.comp measurable_fst)).mul
      (hφc.measurable.comp (measurable_snd.comp measurable_fst))).mul (hY2m t)) hg ?_ ?_
  · filter_upwards [FieldMart.ae_ne_diag] with p hp t ω
    by_cases h0 : φ p.1 = 0 ∨ φ p.2 = 0
    · rcases h0 with h0 | h0 <;> simp only [h0, zero_mul, mul_zero, abs_zero] <;> positivity
    · push Not at h0
      have hb := hY2b t p ω (hH _ h0.1) (hH _ h0.2) hp
      rw [abs_mul, abs_mul]
      exact mul_le_mul_of_nonneg_left hb (mul_nonneg (abs_nonneg _) (abs_nonneg _))
  · filter_upwards [FieldMart.ae_ne_diag] with p hp s t hst S hS
    by_cases h0 : φ p.1 = 0 ∨ φ p.2 = 0
    · rcases h0 with h0 | h0 <;> simp [h0]
    · push Not at h0
      obtain ⟨M, hM, hMe⟩ := exists_martingale_frozenMean_mul_add_retainedGreen (ρL := ρL) (ρR := ρR)
        hE (hH _ h0.1) (hH _ h0.2) hp hσ₀ hσ₀ζ hσ₀N
      have hMY : ∀ᵐ ω ∂P, ∀ t, M t ω = Y2 t p ω := by
        filter_upwards [hMe, hY2 p.1 (hH _ h0.1) p.2 (hH _ h0.2) hp] with ω h1 h2 t
        rw [h1 t, h2 t]
      simp only [integral_const_mul]
      rw [setIntegral_eq_of_ae_eq_martingale (X := fun t ω => Y2 t p ω) hM hMY hst hS]

end Tested

end WangWu

end InteractingSLE
