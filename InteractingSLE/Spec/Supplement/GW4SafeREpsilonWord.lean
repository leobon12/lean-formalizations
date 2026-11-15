/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW4SafeRGermLine
import InteractingSLE.Spec.Sec7.SideC8NativeWord
import InteractingSLE.Spec.Restart.RetPlumbLine

/-!
# GW4: surviving real accesses carry the actual component word

The initial word and the surviving force marks are the literal typed ones.
No matching-height premise is required, and the phase is arbitrary: these
accesses lie outside its exposed seed interval.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Filter Topology MeasureTheory
open scoped NNReal ENNReal
open QuantumZipper (H chiC fwdMapInv logDerivFwd)
open LQGMetric (DistOn)

namespace InteractingSLE.Theorem14.GW4Fix

open Restart Exist.StagedLaw Supp8.Q3Stop Sec7.PhaseSel Sec7.PocketTraversal
  Sec7.PocketStopSide Sec7.Aux119Heights LocalSets WholeField MartChar

/-- A surviving real coordinate has exactly its initial boundary height
in the full typed component word, for every phase value. -/
theorem component_phaseData_of_surviving_real {Ω : Type*} {k : ℝ} (hk : 0 < k)
    (c₀ : BoundaryWord) (X : Ω → DistOn upperHalfPlaneOpens)
    (R : ℝ≥0 → Ω → ℝ) (V : Ω → ℝ≥0∞) {ω : Ω}
    (hRc : Continuous (R · ω)) (hR0 : R 0 ω = 0) {q : ℝ≥0} {x : ℝ}
    (hx : x ∉ c₀.jumps) {a : ℝ → ℂ}
    (ha : QuantumZipper.IsForwardSol (wpath R ω) x q a)
    (hy : (a q).re ∉ forceJumpSet
      (fun i => componentVL k c₀ X R V i q ω - R q ω)
      (fun j => componentVR k c₀ X R V j q ω - R q ω)) (δ : ℝ) :
    phaseData k (typedRhoL (wordType k c₀)) (typedRhoR (wordType k c₀))
      (fun i => componentVL k c₀ X R V i q ω - R q ω)
      (fun j => componentVR k c₀ X R V j q ω - R q ω) δ (a q).re = c₀.fn x := by
  have hW : Continuous (wpath R ω) := hRc.comp continuous_real_toNNReal
  have hW0 : wpath R ω 0 = 0 := by simpa only [wpath, Real.toNNReal_zero] using hR0
  have hx0 : x ≠ 0 := by
    have h := (ha.2 0 ⟨le_rfl, q.coe_nonneg⟩)
    intro he
    apply h.1
    simpa only [he, hW0, Complex.ofReal_zero, sub_self,
      intervalIntegral.integral_same, add_zero] using h.2
  have hxF : x ∉ forceJumpSet (typedXL k (wordType k c₀) c₀)
      (typedXR k (wordType k c₀) c₀) := by
    rw [typedXL_self_eq, typedXR_self_eq]
    rintro (he | ⟨i, hi⟩ | ⟨i, hi⟩)
    · exact hx0 he
    · rcases Supp8.flowLineXL_cases (b := c₀.fn) (J := c₀.jumps) 0 i with
        h0 | ⟨z, hz, -, he⟩
      · exact hx0 (hi.symm.trans h0)
      · have hzx : z = x := by simpa only [sub_zero] using he.symm.trans hi
        exact hx (hzx ▸ (Finset.mem_filter.1 hz).1)
    · rcases Supp8.flowLineXR_cases (b := c₀.fn) (J := c₀.jumps) 0 i with
        h0 | ⟨z, hz, -, he⟩
      · exact hx0 (hi.symm.trans h0)
      · have hzx : z = x := by simpa only [sub_zero] using he.symm.trans hi
        exact hx (hzx ▸ (Finset.mem_filter.1 hz).1)
  have hL : typedXL k (wordType k c₀) c₀ (componentSeedL k c₀) = 0 := by
    rw [typedXL_self_eq]
    exact Sec4.flowLineXL_zero _ _
  have hR : typedXR k (wordType k c₀) c₀ (componentSeedR k c₀) = 0 := by
    rw [typedXR_self_eq]
    exact Sec4.flowLineXR_zero _ _
  have hCoords := Sec7.PocketTraversal.geom_positions_eq_of_driver_eqOn (ω := ω) (q := q)
    R (fun _ => typedXL k (wordType k c₀) c₀)
    (fun _ => typedXR k (wordType k c₀) c₀) hW (fun _ _ => rfl)
  have hVL : (fun i => componentVL k c₀ X R V i q ω - R q ω) =
      (fun i => -RealFlow.rightImg (fun s => -wpath R ω s)
        (-typedXL k (wordType k c₀) c₀ i) q - wpath R ω q) := by
    simpa only [componentVL_eq_geom k c₀ X R V hRc hR0] using hCoords.1
  have hVR : (fun j => componentVR k c₀ X R V j q ω - R q ω) =
      (fun j => RealFlow.rightImg (wpath R ω)
        (typedXR k (wordType k c₀) c₀ j) q - wpath R ω q) := by
    simpa only [componentVR_eq_geom k c₀ X R V hRc hR0] using hCoords.2
  change forceBoundaryData k (typedRhoL (wordType k c₀)) (typedRhoR (wordType k c₀))
      (fun i => componentVL k c₀ X R V i q ω - R q ω)
      (fun j => componentVR k c₀ X R V j q ω - R q ω) (a q).re +
    δ * (Ioo (componentVL k c₀ X R V (componentSeedL k c₀) q ω - R q ω)
      (componentVR k c₀ X R V (componentSeedR k c₀) q ω - R q ω)).indicator 1 (a q).re = c₀.fn x
  rw [hVL, hVR] at hy ⊢
  rw [congrFun hVL (componentSeedL k c₀), congrFun hVR (componentSeedR k c₀)]
  have hWord := force_word_of_surviving_real (κ := k) hW hW0 q.coe_nonneg ha
    (typedRhoL (wordType k c₀)) (typedRhoR (wordType k c₀))
    (typedXL k (wordType k c₀) c₀) (typedXR k (wordType k c₀) c₀)
    (componentSeedL k c₀) (componentSeedR k c₀) hL hR hxF hy δ
  have hInitial := RetAux79.forceBoundaryData_zero_of_isFlowType
    (isFlowType_typed (κ := k) (c := c₀) rfl) x
  exact hWord.trans (hInitial.trans
    (Sec4.forceBoundaryData_flowLine hk c₀.isPiecewiseConstantBoundaryData hx0 hx))

/-- The word-matching conjunct in `ComponentRealAccess` is automatic for
a surviving real characteristic away from the actual current jumps. -/
theorem componentRealAccess_of_surviving_real {Ω : Type*} {k : ℝ} (hk : 0 < k)
    {c₀ : BoundaryWord} {F : Frame} {X : Ω → DistOn upperHalfPlaneOpens}
    {Wd R : ℝ≥0 → Ω → ℝ} {GT : Set Ω} {V : Ω → ℝ≥0∞}
    (d : ℝ≥0 → Ω → ℝ) (t : ℝ≥0) {ω : Ω}
    (hRc : Continuous (R · ω)) (hR0 : R 0 ω = 0) {x : ℝ} (hx : x ∉ c₀.jumps)
    {a : ℝ → ℂ} (ha : QuantumZipper.IsForwardSol (wpath R ω) x
      (lineClock F Wd GT V t ω).toNNReal a)
    (hy : (a (lineClock F Wd GT V t ω).toNNReal).re ∉
      componentLineJumps k c₀ F X Wd GT R V t ω) :
    ComponentRealAccess k c₀ F X Wd GT R V d t ω
      (a (lineClock F Wd GT V t ω).toNNReal).re := by
  refine ⟨x, a, hx, ha, rfl, ?_⟩
  exact (component_phaseData_of_surviving_real hk c₀ X R V hRc hR0 hx ha hy _).symm

end InteractingSLE.Theorem14.GW4Fix
