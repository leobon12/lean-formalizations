/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW2RootC11Clock
import InteractingSLE.Spec.Restart.RetPlumbProofInputsClock

/-!
# Capacity measurability from the actual filled prefix geometry

Packet PROVE-T14-GW2ROOT2. The grid-capacity theorem supplies the
measurable value on bounded attached sets. The defining geometric event
is kept measurable explicitly, so the zero fallback on exceptional
samples is respected. This does not assume measurability of `capR`.
-/

set_option autoImplicit false

noncomputable section

open Set Filter Topology MeasureTheory
open scoped NNReal ENNReal

universe u

namespace InteractingSLE.Theorem14.GW2TipSystem.RootC11

open GW2Schedule GW2Tip Exist Staged StagedLaw Restart LQGMetric

variable {Ω : Type u} [mΩ : MeasurableSpace Ω]

/-- The two geometric measurability questions for the literal set used by `capOf`.
The second clause concerns the filled set, with the existing hitting sigma-algebra. -/
structure MeasurableCapacityGeometry (A : Ω → Set ℂ) : Prop where
  attached_event : MeasurableSet {ω | Bornology.IsBounded (A ω) ∧
    IsPreconnected (A ω ∪ {z : ℂ | z.im ≤ 0})}
  filling : Measurable[mΩ, hittingSigma] (fun ω => fillH (A ω))

/-- The literal half capacity is measurable, including its exceptional zero branch. -/
theorem MeasurableCapacityGeometry.measurable_capOf {A : Ω → Set ℂ}
    (hG : MeasurableCapacityGeometry A) : Measurable (fun ω => capOf (A ω)) := by
  classical
  have hgrid := ((WholeField.measurable_hcapHit.comp hG.filling).ennreal_toReal).div_const 2
  have heq : (fun ω => capOf (A ω)) = fun ω =>
      if Bornology.IsBounded (A ω) ∧ IsPreconnected (A ω ∪ {z : ℂ | z.im ≤ 0})
      then (WholeField.hcapHit (fillH (A ω))).toReal / 2 else 0 := by
    funext ω
    by_cases hω : Bornology.IsBounded (A ω) ∧ IsPreconnected (A ω ∪ {z : ℂ | z.im ≤ 0})
    · rw [capOf, dite_eq_left hω, ite_eq_left hω,
        WholeField.IsHPHull.hcapHit_eq (isHPHull_fillH_of_isPreconnected hω.1 hω.2)]
      change hcapFill (A ω) hω.1 hω.2 / 2 =
        (ENNReal.ofReal (hcapFill (A ω) hω.1 hω.2)).toReal / 2
      rw [ENNReal.toReal_ofReal (show 0 ≤ hcapFill (A ω) hω.1 hω.2 from HPHull.hcap_nonneg _)]
    · rw [capOf, dite_eq_right hω, ite_eq_right hω]
  rw [heq]
  exact Measurable.ite hG.attached_event hgrid measurable_const

/-- A continuous measurable parametrization of a representative filling supplies
the geometric measurability input whenever the literal sets are bounded and attached. -/
theorem MeasurableCapacityGeometry.of_continuous_prefix {A : Ω → Set ℂ}
    (hA : ∀ ω, Bornology.IsBounded (A ω))
    (hcA : ∀ ω, IsPreconnected (A ω ∪ {z : ℂ | z.im ≤ 0}))
    {Γ : Ω → ℝ≥0 → ℂ} {t : ℝ≥0} (hc : ∀ ω, Continuous (Γ ω))
    (hm : ∀ q ≤ t, Measurable fun ω => Γ ω q)
    (hfill : ∀ ω, fillH (A ω) = fillH (Γ ω '' Icc 0 t)) :
    MeasurableCapacityGeometry A := by
  refine ⟨?_, ?_⟩
  · have heq : {ω | Bornology.IsBounded (A ω) ∧
        IsPreconnected (A ω ∪ {z : ℂ | z.im ≤ 0})} = univ :=
      Set.eq_univ_of_forall fun ω => ⟨hA ω, hcA ω⟩
    rw [heq]
    exact MeasurableSet.univ
  · have heq : (fun ω => fillH (A ω)) = fun ω => fillH (Γ ω '' Icc 0 t) := funext hfill
    rw [heq]
    exact RetAux79.measurable_fillH_image_Icc_of_prefix hc hm

section Schedule

variable {κ : ℝ} (hκ : 0 < κ) (h12p : Theorem12ParamStatement.{u})
  (βA : BoundaryWord × ℝ × RecData → BoundaryWord) (b : ℝ → ℝ)
  (jumps : Finset ℝ) (c₀ : BoundaryWord) (h : Ω → DistOn upperHalfPlaneOpens)
  (W' : ℝ≥0 → Ω → ℝ) (s : ℝ≥0) (Θ : Set ℝ) (Q : Set ℝ≥0)

/-- Ambient schedule capacity measurability follows from the measurable geometric
events and fillings of its admissible prefixes. Inadmissible schedules are constant zero. -/
theorem measurable_schedCap_of_geometry (x : ℝ) (e₀ : ℝ × ℝ≥0)
    (hGeom : ∀ xs, SchedAdm b jumps Θ Q (κ := κ) x e₀ xs →
      MeasurableCapacityGeometry (fun ω =>
        prefixImage hκ h12p βA b jumps c₀ h W' s x (schedOf e₀ xs) ω))
    (xs : List (ℝ × ℝ≥0)) :
    Measurable (schedCap hκ h12p βA b jumps c₀ h W' s Θ Q x e₀ xs) := by
  classical
  have hcap : ∀ ys, Measurable (capV hκ h12p βA b jumps c₀ h W' s Θ Q x e₀ ys) := by
    intro ys
    change Measurable (fun ω => capV hκ h12p βA b jumps c₀ h W' s Θ Q x e₀ ys ω)
    by_cases hadm : SchedAdm b jumps Θ Q (κ := κ) x e₀ ys
    · simpa only [capV, ite_eq_left hadm] using (hGeom ys hadm).measurable_capOf
    · simpa only [capV, ite_eq_right hadm] using (measurable_const : Measurable (fun _ : Ω => (0 : ℝ)))
  induction xs with
  | nil => exact hcap []
  | cons y xs ih => exact ih.max (hcap (y :: xs))

variable (ζ' : Ω → ℝ≥0∞)

/-- Ambient measurability of the actual regularized and scaled root capacity. -/
theorem measurable_capR_of_geometry (r : ScaledRootIdx Θ Q)
    (hGeom : ∀ xs, SchedAdm b jumps Θ Q (κ := κ) (rootPt r.1) (rootEntry r.1) xs →
      MeasurableCapacityGeometry (fun ω => prefixImage hκ h12p βA b jumps c₀ h
        (regW s W' ζ') s (rootPt r.1) (schedOf (rootEntry r.1) xs) ω))
    (l : List (EntryIdx Θ Q)) :
    Measurable (capR hκ h12p βA b jumps c₀ h W' ζ' s r l) :=
  measurable_const.mul (measurable_schedCap_of_geometry hκ h12p βA b jumps c₀ h
    (regW s W' ζ') s Θ Q (rootPt r.1) (rootEntry r.1) hGeom (entryList l))

/-- Full retained-stage measurability follows by the already proved fibre descent. -/
theorem measurable_rootSigma_capR_of_geometry [StandardBorelSpace Ω]
    (hβA : Measurable βA) (hh : Measurable h) {P : Measure Ω}
    (hcf : IsCenteredCounterflowDriver κ P h W' ζ') (r : ScaledRootIdx Θ Q)
    (hGeom : ∀ xs, SchedAdm b jumps Θ Q (κ := κ) (rootPt r.1) (rootEntry r.1) xs →
      MeasurableCapacityGeometry (fun ω => prefixImage hκ h12p βA b jumps c₀ h
        (regW s W' ζ') s (rootPt r.1) (schedOf (rootEntry r.1) xs) ω))
    (l : List (EntryIdx Θ Q)) :
    Measurable[rootSigma hκ h12p βA c₀ h W' ζ' s r l]
      (capR hκ h12p βA b jumps c₀ h W' ζ' s r l) :=
  (measurable_capR_iff hκ h12p βA c₀ h b jumps hβA hh s W' ζ' hcf r l).2
    (measurable_capR_of_geometry hκ h12p βA b jumps c₀ h W' s Θ Q ζ' r hGeom l)

end Schedule

end InteractingSLE.Theorem14.GW2TipSystem.RootC11
