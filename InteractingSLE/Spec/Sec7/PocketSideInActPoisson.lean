/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.PocketSideInRefPhase
import InteractingSLE.Spec.Sec6.CutoffUniqueness

/-!
# The full finite phase word from incident germs

PROVE-POCKET-SIDEIN, R73 §3.1. Construct the bounded extension of the phase
word and apply Aux. 29 to the actual physical mean. The exceptional set is a
finite set of physical boundary points; every disk fibre over it is excluded.
The subpower estimate and the incident boundary germs remain named inputs.
Neither boundedness of the actual transformed mean nor equality with a
Poisson extension is assumed.
-/

set_option autoImplicit false
noncomputable section

open MeasureTheory Set Filter Topology Metric
open QuantumZipper (H chiC)
open scoped NNReal ENNReal

namespace InteractingSLE.Sec7.PocketStopSide

open Aux117 MartChar PhaseSel SupercriticalConformalCovariance

/-- The finite phase word's bounded extension, constructed from shifted seed
weights. Coordinates here are already centred at the current driver. -/
def phaseWordExt {nL nR : ℕ} (κ : ℝ) (ρL : Fin (nL + 1) → ℝ)
    (ρR : Fin (nR + 1) → ℝ) (vL : Fin (nL + 1) → ℝ)
    (vR : Fin (nR + 1) → ℝ) (d : ℝ) (z : ℂ) : ℝ :=
  meanExt κ (shiftL κ ρL d) (shiftR κ ρR d) 0 vL vR z + d

theorem isBoundedHarmonicExtension_phaseWordExt {nL nR : ℕ} {κ : ℝ} (hκ : 0 < κ)
    (ρL : Fin (nL + 1) → ℝ) (ρR : Fin (nR + 1) → ℝ)
    {vL : Fin (nL + 1) → ℝ} {vR : Fin (nR + 1) → ℝ}
    (hL : vL 0 ≤ 0) (hR : 0 ≤ vR 0) (d : ℝ) :
    IsBoundedHarmonicExtension (phaseData κ ρL ρR vL vR d) (forceJumpSet vL vR)
      (phaseWordExt κ ρL ρR vL vR d) := by
  have he := isBoundedHarmonicExtension_meanExt κ (shiftL κ ρL d)
    (shiftR κ ρR d) 0 vL vR
  simp only [sub_zero] at he
  exact isBoundedHarmonicExtension_unshift hκ hL hR he

/-- The constructed full word differs from the canonical extension by the
phase times the positive harmonic measure of the exposed interval. -/
theorem phaseWordExt_sub_meanExt {nL nR : ℕ} {κ : ℝ} (hκ : 0 < κ)
    (ρL : Fin (nL + 1) → ℝ) (ρR : Fin (nR + 1) → ℝ)
    {vL : Fin (nL + 1) → ℝ} {vR : Fin (nR + 1) → ℝ}
    (hL : vL 0 ≤ 0) (hR : 0 ≤ vR 0) (hsep : vL 0 < vR 0) (d : ℝ) :
    EqOn (fun z => phaseWordExt κ ρL ρR vL vR d z - meanExt κ ρL ρR 0 vL vR z)
      (fun z => d * phaseWindow (vL 0) (vR 0) z) H := by
  have hbase := isBoundedHarmonicExtension_meanExt κ ρL ρR 0 vL vR
  simp only [sub_zero] at hbase
  exact eqOn_sub_eq_mul_phaseWindow
    (((finite_range vL).union (finite_range vR)).insert 0) hsep
    (Or.inr (Or.inl ⟨0, rfl⟩)) (Or.inr (Or.inr ⟨0, rfl⟩))
    (isBoundedHarmonicExtension_phaseWordExt hκ ρL ρR hL hR d) hbase
    (fun _ _ => rfl)

/-- Aux. 29 removes all singular summands from the actual physical mean.
The boundary premise gives corrected physical germs and their own current
real coordinates, rather than a full Poisson-word identity. -/
theorem mean_eq_phaseWordExt_of_incident_germs {nL nR : ℕ} {κ : ℝ} (hκ : 0 < κ)
    (ρL : Fin (nL + 1) → ℝ) (ρR : Fin (nR + 1) → ℝ)
    {vL : Fin (nL + 1) → ℝ} {vR : Fin (nR + 1) → ℝ}
    (hL : vL 0 ≤ 0) (hR : 0 ≤ vR 0) (d : ℝ)
    {O : Set ℂ} (hOo : IsOpen O) {f : ℂ → ℂ}
    (hf : IsConformalBijection f (ball 0 1) O)
    (hfc : ContinuousOn f (closedBall 0 1)) {P : Set ℂ}
    (hP : P.Finite) (hPO : P ⊆ frontier O) {V : ℂ → ℝ}
    (hV : InnerProductSpace.HarmonicOnNhd V O)
    (hSubpower : ∀ ε : ℝ, 0 < ε → ∃ Cε : ℝ, ∀ z ∈ O,
      |V z| ≤ Cε * (1 + infDist z (frontier O) ^ (-ε)))
    {φ : ℂ → ℂ} (hφ : IsConformalBijection φ O H) {A : ℂ → ℝ}
    (hAc : ContinuousOn A O)
    (hA : ∀ z ∈ O, deriv φ z = ‖deriv φ z‖ * Complex.exp (A z * Complex.I))
    (hIncident : ∀ q ∈ sphere (0 : ℂ) 1, f q ∉ P →
      ∃ x : ℝ, x ∉ forceJumpSet vL vR ∧
        Tendsto (fun ζ => φ (f ζ)) (𝓝[ball 0 1] q) (𝓝[H] (x : ℂ)) ∧
        Tendsto (fun ζ => V (f ζ) + chiC κ * A (f ζ))
          (𝓝[ball 0 1] q) (𝓝 (phaseData κ ρL ρR vL vR d x))) :
    ∀ z ∈ O, V z = phaseWordExt κ ρL ρR vL vR d (φ z) - chiC κ * A z := by
  have he := isBoundedHarmonicExtension_phaseWordExt hκ ρL ρR hL hR d
  apply Sec6.aux29_eqOn_of_tendsto hOo hf hfc hP hPO hV hSubpower hφ
    he.1 he.2.1 (chiC κ) hAc hA
  intro q hq hqP
  obtain ⟨x, hx, hland, hlim⟩ := hIncident q hq hqP
  have hzero := hlim.sub ((he.2.2 x hx).comp hland)
  rw [sub_self] at hzero
  exact hzero.congr fun ζ => by
    dsimp only [Function.comp_def]
    ring

end InteractingSLE.Sec7.PocketStopSide
