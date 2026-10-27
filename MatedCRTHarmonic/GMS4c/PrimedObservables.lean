import MatedCRTHarmonic.GMS4c.Defs

/-!
# All-visit observables

The excursion data on an open set records every visit to a point, but not
which excursion was visited first globally. These observables take the
supremum over those visits. The frozen `visitBound` makes the supremum a
maximum on bundle samples; the order-theoretic definitions also work on
arbitrary curves.
-/

set_option autoImplicit false
noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace MatedCRTHarmonic.GMS4c

open MatedCRTHarmonic.GMS4b

/-- The largest local area ratio at any visit to `z`. -/
def areaRatioPrime (ε : ℝ) (c : ℝ → ℂ) (z : ℂ) : ℝ≥0∞ :=
  ⨆ (t : ℝ) (_ : c t = z), locDA ε c t

/-- The largest inner degree at any visit to `z`. -/
def degreeInPrime (ε : ℝ) (c : ℝ → ℂ) (z : ℂ) : ℕ∞ :=
  ⨆ (t : ℝ) (_ : c t = z), locDegIn ε c t

/-- The largest outer degree at any visit to `z`. -/
def degreeOutPrime (ε : ℝ) (c : ℝ → ℂ) (z : ℂ) : ℕ∞ :=
  ⨆ (t : ℝ) (_ : c t = z), locDegOut ε c t

/-- On a finite, nonempty fiber, the primed inner degree is attained at a visit. -/
theorem degreeInPrime_eq_some_visit {ε : ℝ} {c : ℝ → ℂ} {z : ℂ}
    (hfinite : (c ⁻¹' {z}).Finite) (hne : (c ⁻¹' {z}).Nonempty) :
    ∃ t : ℝ, c t = z ∧ degreeInPrime ε c z = locDegIn ε c t := by
  obtain ⟨t, ht, heq⟩ := hne.ciSup_mem_image hfinite
    (f := fun t => locDegIn ε c t)
  refine ⟨t, ht, ?_⟩
  simpa only [degreeInPrime, mem_preimage, mem_singleton_iff] using heq.symm

/-- On a finite, nonempty fiber, the primed outer degree is attained at a visit. -/
theorem degreeOutPrime_eq_some_visit {ε : ℝ} {c : ℝ → ℂ} {z : ℂ}
    (hfinite : (c ⁻¹' {z}).Finite) (hne : (c ⁻¹' {z}).Nonempty) :
    ∃ t : ℝ, c t = z ∧ degreeOutPrime ε c z = locDegOut ε c t := by
  obtain ⟨t, ht, heq⟩ := hne.ciSup_mem_image hfinite
    (f := fun t => locDegOut ε c t)
  refine ⟨t, ht, ?_⟩
  simpa only [degreeOutPrime, mem_preimage, mem_singleton_iff] using heq.symm

/-- On a finite, nonempty fiber, the primed area ratio is attained at a visit. -/
theorem areaRatioPrime_eq_some_visit {ε : ℝ} {c : ℝ → ℂ} {z : ℂ}
    (hfinite : (c ⁻¹' {z}).Finite) (hne : (c ⁻¹' {z}).Nonempty) :
    ∃ t : ℝ, c t = z ∧ areaRatioPrime ε c z = locDA ε c t := by
  obtain ⟨t, ht, heq⟩ := hne.ciSup_mem_image hfinite
    (f := fun t => locDA ε c t)
  refine ⟨t, ht, ?_⟩
  simpa only [areaRatioPrime, mem_preimage, mem_singleton_iff] using heq.symm

theorem degreeInPrime_ge_iff_exists_visit {ε : ℝ} {c : ℝ → ℂ} {z : ℂ}
    (hfinite : (c ⁻¹' {z}).Finite) (hne : (c ⁻¹' {z}).Nonempty)
    (N : ℕ∞) :
    N ≤ degreeInPrime ε c z ↔
      ∃ t : ℝ, c t = z ∧ N ≤ locDegIn ε c t := by
  constructor
  · intro hN
    obtain ⟨t, ht, hmax⟩ := degreeInPrime_eq_some_visit hfinite hne
    exact ⟨t, ht, hmax ▸ hN⟩
  · rintro ⟨t, ht, hN⟩
    exact hN.trans (le_iSup_of_le t (le_iSup_of_le ht le_rfl))

theorem degreeOutPrime_ge_iff_exists_visit {ε : ℝ} {c : ℝ → ℂ} {z : ℂ}
    (hfinite : (c ⁻¹' {z}).Finite) (hne : (c ⁻¹' {z}).Nonempty)
    (N : ℕ∞) :
    N ≤ degreeOutPrime ε c z ↔
      ∃ t : ℝ, c t = z ∧ N ≤ locDegOut ε c t := by
  constructor
  · intro hN
    obtain ⟨t, ht, hmax⟩ := degreeOutPrime_eq_some_visit hfinite hne
    exact ⟨t, ht, hmax ▸ hN⟩
  · rintro ⟨t, ht, hN⟩
    exact hN.trans (le_iSup_of_le t (le_iSup_of_le ht le_rfl))

theorem areaRatioPrime_gt_iff_exists_visit {ε : ℝ} {c : ℝ → ℂ} {z : ℂ}
    (hfinite : (c ⁻¹' {z}).Finite) (hne : (c ⁻¹' {z}).Nonempty)
    (a : ℝ≥0∞) :
    a < areaRatioPrime ε c z ↔
      ∃ t : ℝ, c t = z ∧ a < locDA ε c t := by
  constructor
  · intro ha
    obtain ⟨t, ht, hmax⟩ := areaRatioPrime_eq_some_visit hfinite hne
    exact ⟨t, ht, hmax ▸ ha⟩
  · rintro ⟨t, ht, ha⟩
    exact ha.trans_le (le_iSup_of_le t (le_iSup_of_le ht le_rfl))

theorem areaRatio_le_prime {ε : ℝ} {c : ℝ → ℂ} {z : ℂ}
    (hhit : c (hitTime c z) = z) :
    areaRatio ε c z ≤ areaRatioPrime ε c z := by
  exact le_iSup_of_le (hitTime c z) (le_iSup_of_le hhit le_rfl)

theorem degreeIn_le_prime {ε : ℝ} {c : ℝ → ℂ} {z : ℂ}
    (hhit : c (hitTime c z) = z) :
    degreeIn ε c z ≤ degreeInPrime ε c z := by
  exact le_iSup_of_le (hitTime c z) (le_iSup_of_le hhit le_rfl)

theorem degreeOut_le_prime {ε : ℝ} {c : ℝ → ℂ} {z : ℂ}
    (hhit : c (hitTime c z) = z) :
    degreeOut ε c z ≤ degreeOutPrime ε c z := by
  exact le_iSup_of_le (hitTime c z) (le_iSup_of_le hhit le_rfl)

/-- The all-visit point observable is bounded by the local spatial supremum
whenever every visit to the point has its degree ball inside `V`. -/
theorem degreeInPrime_le_supLocDegIn {ε : ℝ} {V S : Set ℂ}
    {c : ℝ → ℂ} {z : ℂ} (hz : z ∈ S)
    (hball : ∀ t, c t = z → locBall ε c t ⊆ V) :
    degreeInPrime ε c z ≤ supLocDegIn ε V S c := by
  unfold degreeInPrime
  refine iSup_le fun t => iSup_le fun ht => ?_
  exact le_iSup_of_le t
    (le_iSup_of_le (ht ▸ hz)
      (le_iSup_of_le (hball t ht) le_rfl))

theorem areaRatioPrime_le_supLocDA {ε : ℝ} {V S : Set ℂ}
    {c : ℝ → ℂ} {z : ℂ} (hz : z ∈ S)
    (hball : ∀ t, c t = z → locBall ε c t ⊆ V) :
    areaRatioPrime ε c z ≤ supLocDA ε V S c := by
  unfold areaRatioPrime
  refine iSup_le fun t => iSup_le fun ht => ?_
  exact le_iSup_of_le t
    (le_iSup_of_le (ht ▸ hz)
      (le_iSup_of_le (hball t ht) le_rfl))

theorem degreeOutPrime_le_supLocDegOut {ε : ℝ} {V S : Set ℂ}
    {c : ℝ → ℂ} {z : ℂ} (hz : z ∈ S)
    (hball : ∀ t, c t = z → locBall ε c t ⊆ V) :
    degreeOutPrime ε c z ≤ supLocDegOut ε V S c := by
  unfold degreeOutPrime
  refine iSup_le fun t => iSup_le fun ht => ?_
  exact le_iSup_of_le t
    (le_iSup_of_le (ht ▸ hz)
      (le_iSup_of_le (hball t ht) le_rfl))

/-- The first-hit inner-degree failure is contained in the all-visit failure
on curves whose first-hit time actually hits each tested point. -/
theorem firstHit_innerBad_subset_prime {ε ζ : ℝ} {k : ℕ}
    {c : ℝ → ℂ} {S : Set ℂ}
    (hhit : ∀ z ∈ S, c (hitTime c z) = z) :
    {z ∈ S | ENNReal.ofReal
      (Real.log ε⁻¹ ^ ((k : ℝ) * (1 + ζ) + 1)) <
        ((degreeIn ε c z : ℕ∞) : ℝ≥0∞)} ⊆
    {z ∈ S | ENNReal.ofReal
      (Real.log ε⁻¹ ^ ((k : ℝ) * (1 + ζ) + 1)) <
        ((degreeInPrime ε c z : ℕ∞) : ℝ≥0∞)} := by
  intro z hz
  exact ⟨hz.1, lt_of_lt_of_le hz.2 (by
    exact_mod_cast degreeIn_le_prime (hhit z hz.1))⟩

end MatedCRTHarmonic.GMS4c

