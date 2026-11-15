/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW2RootE26Read

/-!
# Extending a physical record preserves earlier crossing gates

Packet PROVE-T14-GW2ROOT2. The gate uses only earlier rational physical
times. The landed two-coordinate prefix identity therefore preserves
the gate and the gated driver-tip observation, including the endpoint.
-/

set_option autoImplicit false
noncomputable section

open Set Filter Topology MeasureTheory
open scoped NNReal ENNReal
open QuantumZipper (H)

namespace InteractingSLE.Theorem14.GW2TipSystem.RootE26

open Exist Staged StagedLaw Restart Supp8.GB6 RootD25

variable {Ω : Type*} (W : ℝ≥0 → Ω → ℝ) (ζ : Ω → ℝ≥0∞) (ω : Ω)
  {α : ℝ≥0 → ℂ} (hα : IsGeneratingTrace (W · ω) (ζ ω) α)
  (hW : ContinuousOn (W · ω) {t | (t : ℝ≥0∞) < ζ ω}) (hW0 : W 0 ω = 0)
  {s : ℝ≥0} (hs : (s : ℝ≥0∞) < ζ ω) (hsH : α s ∈ H)
  {e : (ℝ≥0 → ℝ) × ℝ≥0∞} (he : IsRegularDriver e) {γ : ℝ≥0 → ℂ}
  (hγ : IsGeneratingTrace e.1 e.2 γ) {v : ℝ≥0}
  (hv : (v : ℝ≥0∞) < min
    (firstContactTime (fun q => sphereInv (γ q : OnePoint ℂ))
      ((fun q => (α q : OnePoint ℂ)) '' Icc 0 s)) e.2)
  {a : ℝ≥0} (ha : 0 < a)

include hα hW hW0 hs hsH he hγ hv ha

/-- Recording beyond the query preserves every earlier crossing test. -/
theorem crossedBefore_prefix_iff {q V : ℝ≥0} (hq : q ≤ V) (hVv : V ≤ v) :
    (cfRec s W ζ ω, recOf (V : ℝ≥0∞) e) ∈ crossedBefore a s V q ↔
      (cfRec s W ζ ω, recOf (v : ℝ≥0∞) e) ∈ crossedBefore a s v q := by
  have hpref : ∀ t ≤ V,
      physicalObservationRead a s V t (cfRec s W ζ ω, recOf (V : ℝ≥0∞) e) =
        physicalObservationRead a s v t (cfRec s W ζ ω, recOf (v : ℝ≥0∞) e) :=
    fun _ ht => physicalObservationRead_prefix_eq
      W ζ ω hα hW hW0 hs hsH he hγ hv ha ht hVv
  constructor
  · rintro ⟨r, hrq, hrV, hcross⟩
    refine ⟨r, hrq, hrV.trans_le hVv, ?_⟩
    rw [← hpref r hrV.le]
    exact hcross
  · rintro ⟨r, hrq, _, hcross⟩
    have hrV : (r : ℝ≥0) < V := hrq.trans_le hq
    refine ⟨r, hrq, hrV, ?_⟩
    rw [hpref r hrV.le]
    exact hcross

/-- The entire gated observation at the query is independent of a later
protected recording cutoff. The query may equal the earlier cutoff. -/
theorem cutoffObservationRead_prefix_eq {q V : ℝ≥0} (hq : q ≤ V) (hVv : V ≤ v)
    (F : ℝ≥0) :
    cutoffObservationRead a s V F q (cfRec s W ζ ω, recOf (V : ℝ≥0∞) e) =
      cutoffObservationRead a s v F q (cfRec s W ζ ω, recOf (v : ℝ≥0∞) e) := by
  have hgate := crossedBefore_prefix_iff W ζ ω hα hW hW0 hs hsH he hγ hv ha hq hVv
  have hpref := physicalObservationRead_prefix_eq
    W ζ ω hα hW hW0 hs hsH he hγ hv ha hq hVv
  by_cases hg : (cfRec s W ζ ω, recOf (V : ℝ≥0∞) e) ∈ crossedBefore a s V q
  · have hg' := hgate.mp hg
    simp only [cutoffObservationRead, crossedObservationRead, hg, hg', ↓reduceIte, hpref]
  · have hg' := mt hgate.mpr hg
    simp only [cutoffObservationRead, crossedObservationRead, hg, hg', ↓reduceIte]

end InteractingSLE.Theorem14.GW2TipSystem.RootE26
