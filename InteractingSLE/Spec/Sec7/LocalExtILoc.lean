/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.LocalExtGStmt
import InteractingSLE.Spec.Coupling.MartMeans2Announce

/-!
# The frozen conditional-law clause at every stopping time, on the event `{τ < ζ}`

Packet PROVE-LOCEXT-I. The frozen `IsOptionalHullCoupling` states the conditional Gaussian law of the field only at
stopping times `τ` of the driving filtration with `τ < ζ` **almost surely**. At a restart conditionally on an event
`D ∈ 𝓓_T` (Aux. lemma 53) the relevant stopping times `T + τ'` are below `ζ` only on `D`; when `P(T ≥ ζ) > 0` the frozen
clause says nothing about them (PROVE-LOCEXT-G's caveat). This file removes the almost-sure hypothesis:

* **`IsOptionalHullCoupling.ae_condExp_cexp_eq_of_lt`**: for **every** stopping time `τ` of the driving filtration, almost
  surely on `{τ < ζ} ∩ {supp φ ∩ K_τ = ∅}`, `E[e^{i(h,φ)} | 𝓓_τ] = exp(i (𝔥_τ, φ) − ½ E_τ(φ))`.

The proof stops `τ` at an announcing sequence `ρ_n < ζ` of the lifetime (`τ ∧ ρ_n < ζ` almost surely), uses the frozen
clause there, and identifies `E[· | 𝓓_{τ∧ρ_n}] = E[· | 𝓓_τ]` on `{τ ≤ ρ_n}` (Mathlib's
`condExp_min_stopping_time_ae_eq_restrict_le`); the events `{τ ≤ ρ_n}` exhaust `{τ < ζ}` almost surely. For an
inadmissible seed `ζ = 0` almost surely and the statement is empty.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal

universe u

namespace InteractingSLE

namespace LocalExt

open Coupling

section Localized

variable {κ : ℝ} {nL nR : ℕ} {xL : Fin nL → ℝ} {xR : Fin nR → ℝ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ}
  {Ω : Type u} {mΩ : MeasurableSpace Ω} {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ} {W : ℝ≥0 → Ω → ℝ}
  {VL : Fin nL → ℝ≥0 → Ω → ℝ} {VR : Fin nR → ℝ≥0 → Ω → ℝ} {B : ℝ≥0 → Ω → ℝ} {ζ : Ω → ℝ≥0∞}
  {h : Ω → LQGMetric.DistOn upperHalfPlaneOpens}

/-- The kernel of the frozen clause at the time `t` along the path of `ω`, for the harmonic extension `u`:
`exp(i (𝔥_t, φ) − ½ E_t(φ))`. -/
def clauseKernel (κ : ℝ) (W : ℝ≥0 → Ω → ℝ) (u : ℂ → ℝ) (φ : LQGMetric.TestOn upperHalfPlaneOpens) (t : ℝ≥0)
    (ω : Ω) : ℂ :=
  Complex.exp (Complex.I * ((∫ z, couplingMean κ (fun s : ℝ => W s.toNNReal ω) (t : ℝ≥0) u z * φ z : ℝ) : ℂ) -
    (((1 / 2 : ℝ) * loewnerGreenEnergy (fun s : ℝ => W s.toNNReal ω) (t : ℝ≥0) φ : ℝ) : ℂ))

/-- An inadmissible seed kills the evolution at time `0` almost surely. -/
theorem ae_zeta_eq_zero_of_thresholdCondition [IsProbabilityMeasure P]
    (hE : IsIntegratedSLEEvolution κ xL xR ρL ρR P 𝓕 W VL VR B ζ) (hκ : 0 < κ)
    (hth : ForceWord.ThresholdCondition ρL ρR 0 xL xR) : ∀ᵐ ω ∂P, ζ ω = 0 := by
  filter_upwards [ae_isGoodPath hE hκ] with ω hg
  exact zeta_eq_zero_of_thresholdCondition hg hth

/-- **The frozen conditional-law clause at every stopping time, on `{τ < ζ}`.** For every stopping time `τ` of the
frozen driving filtration (no almost-sure bound by the lifetime), every choice `u` of the bounded harmonic extensions
at the centred positions at `τ`, and every test function `φ`: almost surely, if `τ < ζ` and `supp φ` misses `K_τ`, then
`E[e^{i(h, φ)} | 𝓓_τ] = exp(i (𝔥_τ, φ) − ½ E_τ(φ))`. -/
theorem _root_.InteractingSLE.IsOptionalHullCoupling.ae_condExp_cexp_eq_of_lt [IsProbabilityMeasure P]
    (hC : IsOptionalHullCoupling κ xL xR ρL ρR P 𝓕 W VL VR B ζ h) (hκ : 0 < κ)
    (hX : IsMeasurableKilledDriving W VL VR ζ) {τ : Ω → WithTop ℝ≥0}
    (hτ : IsStoppingTime (drivingFiltration P hX) τ) (u : Ω → ℂ → ℝ)
    (hu : ∀ ω, IsBoundedHarmonicExtension
      (forceBoundaryData κ ρL ρR (fun i => VL i ((τ ω).untopD 0) ω - W ((τ ω).untopD 0) ω)
        (fun i => VR i ((τ ω).untopD 0) ω - W ((τ ω).untopD 0) ω))
      (forceJumpSet (fun i => VL i ((τ ω).untopD 0) ω - W ((τ ω).untopD 0) ω)
        (fun i => VR i ((τ ω).untopD 0) ω - W ((τ ω).untopD 0) ω)) (u ω))
    (φ : LQGMetric.TestOn upperHalfPlaneOpens) :
    ∀ᵐ ω ∂P, (τ ω : ℝ≥0∞) < ζ ω →
      Disjoint (tsupport φ) (QuantumZipper.fwdHull (fun s : ℝ => W s.toNNReal ω) ((τ ω).untopD 0 : ℝ≥0)) →
        P[fun ω' => Complex.exp (Complex.I * (h ω' φ : ℂ)) | hτ.measurableSpace] ω =
          clauseKernel κ W (u ω) φ ((τ ω).untopD 0) ω := by
  classical
  by_cases hth : ForceWord.ThresholdCondition ρL ρR 0 xL xR
  · filter_upwards [ae_zeta_eq_zero_of_thresholdCondition hC.1 hκ hth] with ω hω hlt
    rw [hω] at hlt
    exact absurd hlt ENNReal.not_lt_zero
  obtain ⟨ρ, hρ, -⟩ := hC.1.exists_isAnnouncingSeq_drivingFiltration hκ hth hX
  obtain ⟨hρst, hρmono, hρζ, hρex⟩ := hρ
  obtain ⟨-, -, -, hX', hcl⟩ := hC
  -- the clause at `τ ∧ ρ_n`, transported to `τ` on `{τ ≤ ρ_n}`
  have hn : ∀ n : ℕ, ∀ᵐ ω ∂P, τ ω ≤ (ρ n ω : WithTop ℝ≥0) →
      Disjoint (tsupport φ) (QuantumZipper.fwdHull (fun s : ℝ => W s.toNNReal ω) ((τ ω).untopD 0 : ℝ≥0)) →
        P[fun ω' => Complex.exp (Complex.I * (h ω' φ : ℂ)) | hτ.measurableSpace] ω =
          clauseKernel κ W (u ω) φ ((τ ω).untopD 0) ω := by
    intro n
    have hσ : IsStoppingTime (drivingFiltration P hX) fun ω => min (τ ω) (ρ n ω : WithTop ℝ≥0) :=
      hτ.min (hρst n)
    have hσζ : ∀ᵐ ω ∂P, ((min (τ ω) (ρ n ω : WithTop ℝ≥0) : WithTop ℝ≥0) : ℝ≥0∞) < ζ ω := by
      filter_upwards [hρζ n] with ω hω
      refine lt_of_le_of_lt ?_ hω
      exact_mod_cast min_le_right (τ ω) (ρ n ω : WithTop ℝ≥0)
    have hX'eq : hX' = hX := rfl
    subst hX'eq
    -- the harmonic extensions at `τ ∧ ρ_n`
    set un : Ω → ℂ → ℝ := fun ω => if τ ω ≤ (ρ n ω : WithTop ℝ≥0) then u ω else
      bheAt κ ρL ρR
        (fun i => VL i ((min (τ ω) (ρ n ω : WithTop ℝ≥0)).untopD 0) ω -
          W ((min (τ ω) (ρ n ω : WithTop ℝ≥0)).untopD 0) ω)
        (fun i => VR i ((min (τ ω) (ρ n ω : WithTop ℝ≥0)).untopD 0) ω -
          W ((min (τ ω) (ρ n ω : WithTop ℝ≥0)).untopD 0) ω) with hun
    have hun' : ∀ ω, IsBoundedHarmonicExtension
        (forceBoundaryData κ ρL ρR
          (fun i => VL i ((min (τ ω) (ρ n ω : WithTop ℝ≥0)).untopD 0) ω -
            W ((min (τ ω) (ρ n ω : WithTop ℝ≥0)).untopD 0) ω)
          (fun i => VR i ((min (τ ω) (ρ n ω : WithTop ℝ≥0)).untopD 0) ω -
            W ((min (τ ω) (ρ n ω : WithTop ℝ≥0)).untopD 0) ω))
        (forceJumpSet
          (fun i => VL i ((min (τ ω) (ρ n ω : WithTop ℝ≥0)).untopD 0) ω -
            W ((min (τ ω) (ρ n ω : WithTop ℝ≥0)).untopD 0) ω)
          (fun i => VR i ((min (τ ω) (ρ n ω : WithTop ℝ≥0)).untopD 0) ω -
            W ((min (τ ω) (ρ n ω : WithTop ℝ≥0)).untopD 0) ω)) (un ω) := by
      intro ω
      by_cases hle : τ ω ≤ (ρ n ω : WithTop ℝ≥0)
      · simp only [hun, hle, ↓reduceIte, min_eq_left hle]
        exact hu ω
      · simp only [hun, hle, ↓reduceIte]
        exact isBoundedHarmonicExtension_bheAt κ ρL ρR _ _
    have hmain := (hcl _ hσ hσζ).2 un hun' φ
    have hce := condExp_min_stopping_time_ae_eq_restrict_le (μ := P)
      (f := fun ω' => Complex.exp (Complex.I * (h ω' φ : ℂ))) hτ (hρst n)
    rw [EventuallyEq, ae_restrict_iff' (hτ.measurableSpace_le _ (hτ.measurableSet_le_stopping_time (hρst n)))] at hce
    filter_upwards [hmain, hce] with ω h1 h2 hle hdisj
    have e : min (τ ω) (ρ n ω : WithTop ℝ≥0) = τ ω := min_eq_left hle
    rw [← h2 hle]
    have h1' := h1 (by rw [e]; exact hdisj)
    simp only [e, hun, hle, ↓reduceIte] at h1'
    exact h1'
  filter_upwards [ae_all_iff.2 hn, hρex] with ω hall hex hlt hdisj
  -- `τ ω` is finite and some `ρ_n ω` is above it
  have hfin : τ ω ≠ ⊤ := by
    intro htop
    rw [htop] at hlt
    exact not_top_lt hlt
  obtain ⟨t, ht⟩ := WithTop.ne_top_iff_exists.1 hfin
  have htζ : (t : ℝ≥0∞) < ζ ω := by
    rw [← ht] at hlt
    exact_mod_cast hlt
  obtain ⟨n, hn'⟩ := hex t htζ
  refine hall n ?_ hdisj
  rw [← ht]
  exact_mod_cast hn'

end Localized

end LocalExt

end InteractingSLE
