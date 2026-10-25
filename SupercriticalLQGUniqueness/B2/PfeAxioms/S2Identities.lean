import SupercriticalLQGUniqueness.B2.PfeAxioms.S2NormalizedPatch
import SupercriticalLQGUniqueness.B2.PfeWeyl.S3Assembly
import LQGMetric.Papers.GM.S1.FieldAux

 

















set_option autoImplicit false
noncomputable section

open Set Filter Topology MeasureTheory
open scoped ENNReal
open LQGMetric

namespace SupercriticalLQGUniqueness.B2.PfeAxioms

variable (ξ : Set.Ioi (0 : ℝ)) (m : Set.Ioi (0 : ℝ) → Set.Ioi (0 : ℝ))
  (ε : ℕ → Set.Ioi (0 : ℝ)) (hε : Tendsto (fun n => (ε n : ℝ)) atTop (𝓝 0))
  (Φ : DistC → LSCMetric)
  (hlsc : PfeWeyl.NormalizedLscLimit ξ m ε Φ)
  (hgeo : PfeWeyl.NormalizedLimitGeometry Φ)
  (htail : PfeWeyl.NormalizedAcrossTails Φ)
  (hsmall : PfeWeyl.NormalizedSmallAnnuli ξ m ε Φ)

include hε hlsc hgeo htail hsmall in
 
theorem ae_patchWitness_eq_of_normalized
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (h : Ω → DistC) (hh : IsNormalizedWholePlaneGFF h P) :
    ∀ᵐ ω ∂P, patchWitness ξ m ε (h ω) = Φ (h ω) := by
  filter_upwards [ae_patchWitness_weyl_of_normalized ξ m ε hε Φ hlsc hgeo htail hsmall P h hh,
    (hgeo P h hh).1] with ω hω hlen
  obtain ⟨-, hW⟩ := hω 0
  rw [GM.addFun_zero_eq] at hW
  apply LSCMetric.ext
  intro p
  rw [hW p]
  have h0 : (0 : C(ℂ, ℝ)) = ContinuousMap.const ℂ 0 := rfl
  rw [h0, weylScale_const (ξ : ℝ) 0 (Φ (h ω)) hlen p, mul_zero, Real.exp_zero,
    ENNReal.ofReal_one, one_mul]

include hε hlsc hgeo htail hsmall in
 

theorem ae_patchWitness_weyl_all_of_normalized
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (h : Ω → DistC) (hh : IsNormalizedWholePlaneGFF h P) :
    ∀ᵐ ω ∂P, ∀ F : C(ℂ, ℝ),
      (patchWitness ξ m ε (addFun (h ω) F)).1 = weylScale (ξ : ℝ) F (patchWitness ξ m ε (h ω)) := by
  filter_upwards [ae_patchWitness_weyl_of_normalized ξ m ε hε Φ hlsc hgeo htail hsmall P h hh,
    ae_patchWitness_eq_of_normalized ξ m ε hε Φ hlsc hgeo htail hsmall P h hh] with ω hω hD
  intro F
  rw [hD]
  funext p
  exact (hω F).2 p

include hε hlsc hgeo htail hsmall in
 
theorem boundedShiftWeyl_patchWitness :
    PfeWeyl.BoundedShiftWeyl ξ (patchWitness ξ m ε) := by
  intro Ω _ P _ h hh F _ _
  filter_upwards [ae_patchWitness_weyl_all_of_normalized ξ m ε hε Φ hlsc hgeo htail hsmall
    P h hh] with ω hω
  exact hω (F ω)

include hε hlsc hgeo htail hsmall in
theorem normalizedLscLimit_patchWitness :
    PfeWeyl.NormalizedLscLimit ξ m ε (patchWitness ξ m ε) :=
  PfeWeyl.normalizedLscLimit_congr hlsc
    fun P _ hf hh => ae_patchWitness_eq_of_normalized ξ m ε hε Φ hlsc hgeo htail hsmall P hf hh

include hε hlsc hgeo htail hsmall in
theorem normalizedLimitGeometry_patchWitness :
    PfeWeyl.NormalizedLimitGeometry (patchWitness ξ m ε) := by
  intro Ω _ P _ h hh
  have hD := ae_patchWitness_eq_of_normalized ξ m ε hε Φ hlsc hgeo htail hsmall P h hh
  obtain ⟨h1, h2⟩ := hgeo P h hh
  refine ⟨?_, ?_⟩
  · filter_upwards [hD, h1] with ω hω h; rw [hω]; exact h
  · filter_upwards [hD, h2] with ω hω h; rw [hω]; exact h

include hε hlsc hgeo htail hsmall in
theorem normalizedAcrossTails_patchWitness :
    PfeWeyl.NormalizedAcrossTails (patchWitness ξ m ε) := by
  intro Ω _ P _ h hh k T hT η hη
  have hD := ae_patchWitness_eq_of_normalized ξ m ε hε Φ hlsc hgeo htail hsmall P h hh
  filter_upwards [htail P h hh k T hT η hη] with R hR
  refine le_trans (le_of_eq (measure_congr ?_)) hR
  filter_upwards [hD] with ω hω
  simp only [hω]

include hε hlsc hgeo htail hsmall in
theorem normalizedSmallAnnuli_patchWitness :
    PfeWeyl.NormalizedSmallAnnuli ξ m ε (patchWitness ξ m ε) := by
  intro Ω _ P _ h hh X hX k
  have hD := ae_patchWitness_eq_of_normalized ξ m ε hε Φ hlsc hgeo htail hsmall P h hh
  filter_upwards [hD, hsmall P h hh X hX k] with ω hω h
  rw [hω]; exact h

include hε hlsc hgeo htail hsmall in
theorem normalizedPointCircles_patchWitness
    (hpts : PfeWeyl.NormalizedPointCircles ξ m ε Φ) :
    PfeWeyl.NormalizedPointCircles ξ m ε (patchWitness ξ m ε) := by
  intro Ω _ P _ h hh X hX x y r x' y' r' hr hr' h0
  have hD := ae_patchWitness_eq_of_normalized ξ m ε hε Φ hlsc hgeo htail hsmall P h hh
  filter_upwards [hD, hpts P h hh X hX x y r x' y' r' hr hr' h0] with ω hω h
  rw [hω]; exact h

end SupercriticalLQGUniqueness.B2.PfeAxioms
