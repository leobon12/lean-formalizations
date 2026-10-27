import MatedCRTHarmonic.GMS4c.PrimedObservables
import MatedCRTHarmonic.GMS4c.LocalQuantumCurveBorel
import MatedCRTHarmonic.Frozen.IsMatingOfTreesCoupling
import MatedCRTHarmonic.MoTInput.CurveAdapters

/-! The frozen Lebesgue-time visit bound passes to the quantum-time curve. -/

set_option autoImplicit false
noncomputable section

open MeasureTheory Set Metric
open scoped NNReal ENNReal

namespace MatedCRTHarmonic.GMS4c

open MatedCRTHarmonic.MatedCRT
open MatedCRTHarmonic.MoTInput

theorem finite_quantum_visits_of_reparam
    {cL c : ℝ → ℂ} (φ : ℝ ≃o ℝ)
    (hc : ∀ t, c t = cL (φ t)) {z : ℂ}
    (hfinite : (cL ⁻¹' {z}).Finite) :
    (c ⁻¹' {z}).Finite := by
  have hset : c ⁻¹' {z} = φ ⁻¹' (cL ⁻¹' {z}) := by
    ext t
    simp only [mem_preimage, mem_singleton_iff, hc]
  rw [hset]
  exact hfinite.preimage φ.injective.injOn

/-- Simultaneously at every point, the area-parametrized bundle curve has
finitely many visits, hence its primed observables are genuine maxima. -/
theorem ae_bundle_finite_quantum_visits
    {γ : ℝ} {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
    {X X₀ hIG₀ : Ω → Field}
    {B B' B₀ B₀' : ℝ≥0 → Ω → ℝ} {U : Ω → ℝ}
    {ηL η η₀ : Ω → C(ℝ, ℂ)} {bm : Ω → Path2}
    (D : IsMatingOfTreesCoupling γ P X X₀ hIG₀ B B' B₀ B₀' U ηL η η₀ bm) :
    ∀ᵐ ω ∂P, ∀ z : ℂ, ((η ω) ⁻¹' {z}).Finite := by
  obtain ⟨k, hk⟩ := D.visitBound
  filter_upwards [D.areaParam, hk] with ω hparam hvisit z
  obtain ⟨φ, -, hφ⟩ := hparam.1
  exact finite_quantum_visits_of_reparam φ hφ
    (Set.finite_of_encard_le_coe (hvisit z))

/-- A spatial maximum of the primed inner degree is exactly the all-time
threshold event when point fibers are finite. -/
theorem prime_inner_bad_iff_allVisit
    {c : ℝ → ℂ} (hfinite : ∀ z, (c ⁻¹' {z}).Finite)
    (hsurj : Function.Surjective c) (ε ρ : ℝ) (N : ℕ∞) :
    (∃ z ∈ ball (0 : ℂ) ρ, N ≤ degreeInPrime ε c z) ↔
      ∃ t : ℝ, c t ∈ ball (0 : ℂ) ρ ∧ N ≤ GMS4b.locDegIn ε c t := by
  constructor
  · rintro ⟨z, hz, hdeg⟩
    obtain ⟨t, ht, hN⟩ :=
      (degreeInPrime_ge_iff_exists_visit (hfinite z)
        ⟨(hsurj z).choose, by simpa using (hsurj z).choose_spec⟩ N).mp hdeg
    exact ⟨t, ht ▸ hz, hN⟩
  · rintro ⟨t, ht, hN⟩
    exact ⟨c t, ht, (degreeInPrime_ge_iff_exists_visit (hfinite (c t))
      ⟨t, by simp⟩ N).mpr ⟨t, rfl, hN⟩⟩

theorem prime_outer_bad_iff_allVisit
    {c : ℝ → ℂ} (hfinite : ∀ z, (c ⁻¹' {z}).Finite)
    (hsurj : Function.Surjective c) (ε ρ : ℝ) (N : ℕ∞) :
    (∃ z ∈ ball (0 : ℂ) ρ, N ≤ degreeOutPrime ε c z) ↔
      ∃ t : ℝ, c t ∈ ball (0 : ℂ) ρ ∧ N ≤ GMS4b.locDegOut ε c t := by
  constructor
  · rintro ⟨z, hz, hdeg⟩
    obtain ⟨t, ht, hN⟩ :=
      (degreeOutPrime_ge_iff_exists_visit (hfinite z)
        ⟨(hsurj z).choose, by simpa using (hsurj z).choose_spec⟩ N).mp hdeg
    exact ⟨t, ht ▸ hz, hN⟩
  · rintro ⟨t, ht, hN⟩
    exact ⟨c t, ht, (degreeOutPrime_ge_iff_exists_visit (hfinite (c t))
      ⟨t, by simp⟩ N).mpr ⟨t, rfl, hN⟩⟩

theorem prime_DA_bad_iff_allVisit
    {c : ℝ → ℂ} (hfinite : ∀ z, (c ⁻¹' {z}).Finite)
    (hsurj : Function.Surjective c) (ε ρ : ℝ) (a : ℝ≥0∞) :
    (∃ z ∈ ball (0 : ℂ) ρ, a < areaRatioPrime ε c z) ↔
      ∃ t : ℝ, c t ∈ ball (0 : ℂ) ρ ∧ a < GMS4b.locDA ε c t := by
  constructor
  · rintro ⟨z, hz, hDA⟩
    obtain ⟨t, ht, ha⟩ :=
      (areaRatioPrime_gt_iff_exists_visit (hfinite z)
        ⟨(hsurj z).choose, by simpa using (hsurj z).choose_spec⟩ a).mp hDA
    exact ⟨t, ht ▸ hz, ha⟩
  · rintro ⟨t, ht, ha⟩
    exact ⟨c t, ht, (areaRatioPrime_gt_iff_exists_visit (hfinite (c t))
      ⟨t, by simp⟩ a).mpr ⟨t, rfl, ha⟩⟩

/-- Under the bundle law, each global primed threshold is the Borel
all-time event on the area-parametrized continuous curve. -/
theorem ae_bundle_prime_inner_iff_allVisit
    {γ : ℝ} {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
    {X X₀ hIG₀ : Ω → Field}
    {B B' B₀ B₀' : ℝ≥0 → Ω → ℝ} {U : Ω → ℝ}
    {ηL η η₀ : Ω → C(ℝ, ℂ)} {bm : Ω → Path2}
    (D : IsMatingOfTreesCoupling γ P X X₀ hIG₀ B B' B₀ B₀' U ηL η η₀ bm) :
    ∀ᵐ ω ∂P, ∀ ε ρ : ℝ, ∀ N : ℕ∞,
      (∃ z ∈ ball (0 : ℂ) ρ, N ≤ degreeInPrime ε (η ω) z) ↔
        ∃ t : ℝ, η ω t ∈ ball (0 : ℂ) ρ ∧
          N ≤ GMS4b.locDegIn ε (η ω) t := by
  filter_upwards [ae_bundle_finite_quantum_visits D, ae_peanosphere D]
    with ω hfinite hp ε ρ N
  exact prime_inner_bad_iff_allVisit hfinite hp.surj ε ρ N

theorem ae_bundle_prime_outer_iff_allVisit
    {γ : ℝ} {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
    {X X₀ hIG₀ : Ω → Field}
    {B B' B₀ B₀' : ℝ≥0 → Ω → ℝ} {U : Ω → ℝ}
    {ηL η η₀ : Ω → C(ℝ, ℂ)} {bm : Ω → Path2}
    (D : IsMatingOfTreesCoupling γ P X X₀ hIG₀ B B' B₀ B₀' U ηL η η₀ bm) :
    ∀ᵐ ω ∂P, ∀ ε ρ : ℝ, ∀ N : ℕ∞,
      (∃ z ∈ ball (0 : ℂ) ρ, N ≤ degreeOutPrime ε (η ω) z) ↔
        ∃ t : ℝ, η ω t ∈ ball (0 : ℂ) ρ ∧
          N ≤ GMS4b.locDegOut ε (η ω) t := by
  filter_upwards [ae_bundle_finite_quantum_visits D, ae_peanosphere D]
    with ω hfinite hp ε ρ N
  exact prime_outer_bad_iff_allVisit hfinite hp.surj ε ρ N

theorem ae_bundle_prime_DA_iff_allVisit
    {γ : ℝ} {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
    {X X₀ hIG₀ : Ω → Field}
    {B B' B₀ B₀' : ℝ≥0 → Ω → ℝ} {U : Ω → ℝ}
    {ηL η η₀ : Ω → C(ℝ, ℂ)} {bm : Ω → Path2}
    (D : IsMatingOfTreesCoupling γ P X X₀ hIG₀ B B' B₀ B₀' U ηL η η₀ bm) :
    ∀ᵐ ω ∂P, ∀ ε ρ : ℝ, ∀ a : ℝ≥0∞,
      (∃ z ∈ ball (0 : ℂ) ρ, a < areaRatioPrime ε (η ω) z) ↔
        ∃ t : ℝ, η ω t ∈ ball (0 : ℂ) ρ ∧
          a < GMS4b.locDA ε (η ω) t := by
  filter_upwards [ae_bundle_finite_quantum_visits D, ae_peanosphere D]
    with ω hfinite hp ε ρ a
  exact prime_DA_bad_iff_allVisit hfinite hp.surj ε ρ a

end MatedCRTHarmonic.GMS4c

