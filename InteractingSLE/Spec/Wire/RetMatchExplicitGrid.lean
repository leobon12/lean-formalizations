/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Wire.RetMatchExplicitMin

/-!
# Raw dyadic approximations of augmented stopping times

Represent each event that an augmented time rounds to one grid point by an
actual raw event at that grid point. The attained minimum of the corresponding
masked constant times is raw stopping and equals the dyadic approximation a.s.
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal

namespace InteractingSLE.Wire.RetMatchExplicit

open Sec2.Assembly

/-- Identify the two landed upper-dyadic APIs. -/
theorem dyadUp_eq_dyadicUp (m : ℕ) (t : ℝ≥0) :
    Exist.Param12.dyadUp m t = dyadicUp m t := by
  simp only [Exist.Param12.dyadUp, dyad, flr, dyadicUp, mul_comm t]

/-- Each finite augmented stopping time has a raw stopping version of every
strict upper-dyadic approximation. -/
theorem exists_raw_dyadicApprox {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ} {s : Ω → ℝ≥0}
    (hs : IsStoppingTime (usualAugmentation 𝓕 P) (fun ω => (s ω : WithTop ℝ≥0)))
    (m : ℕ) : ∃ R : Ω → WithTop ℝ≥0, IsStoppingTime 𝓕 R ∧
      ∀ᵐ ω ∂P, R ω = (dyadicUp m (s ω) : WithTop ℝ≥0) := by
  classical
  have hex : ∀ k, ∃ E : Set Ω, MeasurableSet[𝓕 (dyad m k)] E ∧
      E =ᵐ[P] {ω | flr m (s ω) + 1 = k} := by
    intro k
    obtain ⟨E, hE, he⟩ := Exist.Param12.exists_ae_eq_inter_flr hs
      (@MeasurableSet.univ _ hs.measurableSpace) m k
    exact ⟨E, hE, by simpa only [univ_inter] using he⟩
  choose E hE he using hex
  let T : ℕ → Ω → WithTop ℝ≥0 := fun k =>
    (E k).piecewise (fun _ => (dyad m k : WithTop ℝ≥0)) (fun _ => ⊤)
  have hT : ∀ k, IsStoppingTime 𝓕 (T k) := by
    intro k
    exact (isStoppingTime_const 𝓕 (dyad m k)).piecewise_of_le
      (fun _ => MeasurableSet.const _) (fun _ => le_rfl) (fun _ => le_top) (hE k)
  refine ⟨fun ω => attainedMin (fun k => T k ω), isStoppingTime_attainedMin hT, ?_⟩
  filter_upwards [ae_all_iff.2 he] with ω hω
  let k := flr m (s ω) + 1
  have hmem : ∀ j, ω ∈ E j ↔ k = j := fun j => Iff.of_eq (hω j)
  have hTk : T k ω = (dyad m k : WithTop ℝ≥0) := by
    exact Set.piecewise_eq_of_mem _ _ _ ((hmem k).2 rfl)
  have hmin : ∀ j, T k ω ≤ T j ω := by
    intro j
    by_cases hj : ω ∈ E j
    · rw [← (hmem j).1 hj]
    · have hj' : T j ω = ⊤ := Set.piecewise_eq_of_notMem _ _ _ hj
      exact hj' ▸ le_top
  calc
    attainedMin (fun j => T j ω) = T k ω := attainedMin_eq_of_min hmin
    _ = (dyad m k : WithTop ℝ≥0) := hTk
    _ = (dyadicUp m (s ω) : WithTop ℝ≥0) :=
      congrArg (fun x : ℝ≥0 => (x : WithTop ℝ≥0)) (dyadUp_eq_dyadicUp m (s ω))

end InteractingSLE.Wire.RetMatchExplicit
