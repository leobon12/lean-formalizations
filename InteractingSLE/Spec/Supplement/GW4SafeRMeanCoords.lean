/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW4SafeRMeanPairing

/-! # GW4: the typed finite word and its geometric seeds -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set MeasureTheory ProbabilityTheory Topology
open scoped NNReal ENNReal
open LQGMetric (DistOn)

namespace InteractingSLE.Theorem14.GW4Fix

open Restart Exist.StagedLaw Supp8.Q3Stop Supp8.GB6.RelDrv Sec7.PocketTraversal MartChar

/-- The left seed index of the component's typed finite word. -/
abbrev componentSeedL (k : ℝ) (c₀ : BoundaryWord) : Fin (wordType k c₀).1 :=
  ⟨0, Nat.zero_lt_succ _⟩

/-- The right seed index of the component's typed finite word. -/
abbrev componentSeedR (k : ℝ) (c₀ : BoundaryWord) : Fin (wordType k c₀).2.1 :=
  ⟨0, Nat.zero_lt_succ _⟩

/-- The seed lower bound is already contained in the side partial-sum bounds. -/
theorem seed_lower_of_partialSums {n : ℕ} {ρ : Fin (n + 1) → ℝ}
    (hs : ∀ i, -2 < ∑ j ∈ Finset.univ.filter (fun j => j ≤ i), ρ j) : -2 < ρ 0 := by
  simpa only [Fin.le_zero_iff, Finset.filter_eq', Finset.mem_univ, ite_true,
    Finset.sum_singleton] using hs 0

/-- The self-typed positions are the finite flow-line positions. -/
theorem typedXL_self_eq (k : ℝ) (c₀ : BoundaryWord) :
    typedXL k (wordType k c₀) c₀ = flowLineXL c₀.fn c₀.jumps 0 := by
  funext i
  simp only [typedXL, ↓reduceIte]
  exact padFL_fst_fst_fin c₀.fn c₀.jumps i

/-- The self-typed positions are the finite flow-line positions. -/
theorem typedXR_self_eq (k : ℝ) (c₀ : BoundaryWord) :
    typedXR k (wordType k c₀) c₀ = flowLineXR c₀.fn c₀.jumps 0 := by
  funext i
  simp only [typedXR, ↓reduceIte]
  exact padFL_fst_snd_fin c₀.fn c₀.jumps i

/-- Canonical-path encoding does not change the geometric left coordinates. -/
theorem componentVL_eq_geom {Ω : Type*} (k : ℝ) (c₀ : BoundaryWord)
    (X : Ω → DistOn upperHalfPlaneOpens) (R : ℝ≥0 → Ω → ℝ) (V : Ω → ℝ≥0∞)
    {ω : Ω} (hRc : Continuous (R · ω)) (hR0 : R 0 ω = 0) (i) (q : ℝ≥0) :
    componentVL k c₀ X R V i q ω =
      geomLW R (fun _ => typedXL k (wordType k c₀) c₀) i q ω := by
  have he : ∀ s, canonDrv s (componentPoint X R V ω) = R s ω :=
    fun s => relDrv_relVar hRc hR0 s
  change -MartChar.RealFlow.rightImg
      (fun s : ℝ => -canonDrv s.toNNReal (componentPoint X R V ω))
      (-typedXL k (wordType k c₀) c₀ i) q =
    -MartChar.RealFlow.rightImg (fun s : ℝ => -R s.toNNReal ω)
      (-typedXL k (wordType k c₀) c₀ i) q
  simp only [he]

/-- Canonical-path encoding does not change the geometric right coordinates. -/
theorem componentVR_eq_geom {Ω : Type*} (k : ℝ) (c₀ : BoundaryWord)
    (X : Ω → DistOn upperHalfPlaneOpens) (R : ℝ≥0 → Ω → ℝ) (V : Ω → ℝ≥0∞)
    {ω : Ω} (hRc : Continuous (R · ω)) (hR0 : R 0 ω = 0) (j) (q : ℝ≥0) :
    componentVR k c₀ X R V j q ω =
      geomRW R (fun _ => typedXR k (wordType k c₀) c₀) j q ω := by
  have he : ∀ s, canonDrv s (componentPoint X R V ω) = R s ω :=
    fun s => relDrv_relVar hRc hR0 s
  change MartChar.RealFlow.rightImg
      (fun s : ℝ => canonDrv s.toNNReal (componentPoint X R V ω))
      (typedXR k (wordType k c₀) c₀ j) q =
    MartChar.RealFlow.rightImg (fun s : ℝ => R s.toNNReal ω)
      (typedXR k (wordType k c₀) c₀ j) q
  simp only [he]

/-- At time zero both component seeds coincide, regardless of the encoded
driver version. Thus the phase correction has empty support at that time. -/
theorem component_seeds_zero {Ω : Type*} (k : ℝ) (c₀ : BoundaryWord)
    (X : Ω → DistOn upperHalfPlaneOpens) (R : ℝ≥0 → Ω → ℝ) (V : Ω → ℝ≥0∞)
    (ω : Ω) :
    componentVL k c₀ X R V (componentSeedL k c₀) 0 ω = 0 ∧
      componentVR k c₀ X R V (componentSeedR k c₀) 0 ω = 0 := by
  constructor
  · rw [componentVL, geomLW_zero continuous_canonDrv canonDrv_zero
      (typedXL_nonpos k (wordType k c₀) c₀ (componentSeedL k c₀)), typedXL_self_eq]
    exact Sec4.flowLineXL_zero _ _
  · rw [componentVR, geomRW_zero continuous_canonDrv canonDrv_zero
      (typedXR_nonneg k (wordType k c₀) c₀ (componentSeedR k c₀)), typedXR_self_eq]
    exact Sec4.flowLineXR_zero _ _

end InteractingSLE.Theorem14.GW4Fix
