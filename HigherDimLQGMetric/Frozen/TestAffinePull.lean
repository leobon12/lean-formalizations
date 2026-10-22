import HigherDimLQGMetric.Frozen.TestRd
import Mathlib.Analysis.Distribution.Distribution
import Mathlib.Analysis.Calculus.ContDiff.Operations

/-!
# Frozen definition: `testAffinePull`

Anchor of the statement surface of the higher-dimensional LQG metric formalization (manifest
`HigherDimLQGMetric/Frozen/frozen-anchors.json`; rulings `planning/RULINGS.md`, M1, M13).
Source: `source/higher-dimensional-lqg-metric.pdf` ([S], cited by line of the text extraction `.txt`):
[S] l. 76–78 (Axiom (IV)), translation covariance of Definition 1.3 (l. 99): the pullback of test
functions `φ ↦ φ((· - z)/r)`, a continuous linear map on `𝓓(ℝ^d)` (written `φ (r⁻¹ • (x + -z))`).
Port of LQGMetric's `testAffinePull` (`lqg_metric/LQGMetric/Statement/Field.lean`) from `ℂ` to `ℝ^d`, with
the helper lemmas inlined (one declaration per file). The zero branch `r = 0` is never used: the frozen
statements use `affineComp r z` only with `r > 0` (Axiom (IV)) and `r = 1` (translation covariance).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set
open scoped Distributions

namespace HigherDimLQGMetric

open HigherDimLFPP (Rd)

/-- `φ ↦ φ((· - z)/r)` on `𝓓(ℝ^d)` (the zero map for `r = 0`, a value never used). -/
def testAffinePull {d : ℕ} (r : ℝ) (z : Rd d) : TestRd d →L[ℝ] TestRd d :=
  if hr : r = 0 then 0 else
  TestFunction.mkCLM ℝ
    (fun φ : TestRd d => (⟨fun x => φ (r⁻¹ • (x + -z)),
      φ.contDiff.comp ((contDiff_id.add contDiff_const).const_smul r⁻¹),
      (by
        refine HasCompactSupport.intro (K := (fun y => r • y + z) '' tsupport φ)
          (φ.hasCompactSupport.isCompact.image (by fun_prop)) fun x hx => ?_
        have hx' : r⁻¹ • (x + -z) ∉ tsupport φ := fun h =>
          hx ⟨r⁻¹ • (x + -z), h, by simp [hr]⟩
        exact image_eq_zero_of_notMem_tsupport (f := φ) hx'),
      subset_univ _⟩ : TestRd d))
    (fun _ _ => rfl) (fun _ _ => rfl) (fun K _ => by
      have hA : Continuous (fun x : Rd d => r⁻¹ • (x + -z)) := by fun_prop
      have hiter : ∀ (φ : Rd d → ℝ), ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) φ → ∀ (i : ℕ) (x : Rd d),
          iteratedFDeriv ℝ i (fun y => φ (r⁻¹ • (y + -z))) x =
            (iteratedFDeriv ℝ i φ (r⁻¹ • (x + -z))).compContinuousLinearMap
              fun _ => (r⁻¹ • ContinuousLinearMap.id ℝ (Rd d)) := by
        intro φ hφ i x
        have hE : (fun y => φ (r⁻¹ • (y + -z))) =
            fun y => (φ ∘ (r⁻¹ • ContinuousLinearMap.id ℝ (Rd d))) (y + -z) := by
          ext y; simp
        rw [hE, iteratedFDeriv_comp_add_right,
          (r⁻¹ • ContinuousLinearMap.id ℝ (Rd d)).iteratedFDeriv_comp_right hφ _
            (by exact_mod_cast le_top)]
        rfl
      let K' : TopologicalSpace.Compacts (Rd d) := K.map (fun y => r • y + z) (by fun_prop)
      have hmem : ∀ x, r⁻¹ • (x + -z) ∈ (K : Set (Rd d)) → x ∈ (K' : Set (Rd d)) :=
        fun x hx => ⟨r⁻¹ • (x + -z), hx, by simp [hr]⟩
      let pull : 𝓓^{⊤}_{K}(Rd d, ℝ) →ₗ[ℝ] 𝓓^{⊤}_{K'}(Rd d, ℝ) :=
        { toFun := fun φ =>
            { toFun := fun x => φ (r⁻¹ • (x + -z))
              contDiff' := φ.contDiff.comp ((contDiff_id.add contDiff_const).const_smul r⁻¹)
              zero_on_compl' := fun x hx => φ.zero_on_compl (fun hK => hx (hmem x hK)) }
          map_add' := fun _ _ => rfl
          map_smul' := fun _ _ => rfl }
      have hpull : Continuous pull := by
        rw [ContDiffMapSupportedIn.continuous_iff_comp]
        intro i
        let Ψ := (ContinuousMultilinearMap.compContinuousLinearMapL (𝕜 := ℝ)
            (E := fun _ : Fin i => Rd d) (E₁ := fun _ : Fin i => Rd d) (F := ℝ)
            (fun _ => r⁻¹ • ContinuousLinearMap.id ℝ (Rd d))).compLeftContinuousBounded (Rd d)
        have key : (ContDiffMapSupportedIn.structureMapCLM ℝ ⊤ i ∘ pull) =
            (fun g => (Ψ g).compContinuous ⟨fun x : Rd d => r⁻¹ • (x + -z), hA⟩) ∘
              ContDiffMapSupportedIn.structureMapCLM ℝ ⊤ i := by
          funext φ
          ext x : 1
          simp only [Function.comp_apply, ContDiffMapSupportedIn.structureMapCLM_top_apply]
          rw [BoundedContinuousFunction.compContinuous_apply,
            ContinuousLinearMap.compLeftContinuousBounded_apply,
            ContDiffMapSupportedIn.structureMapCLM_top_apply]
          exact hiter φ φ.contDiff i x
        rw [key]
        exact ((BoundedContinuousFunction.continuous_compContinuous _).comp Ψ.continuous).comp
          (ContDiffMapSupportedIn.structureMapCLM ℝ ⊤ i).continuous
      refine Continuous.congr
        ((TestFunction.ofSupportedInCLM ℝ (subset_univ (K' : Set (Rd d)))).continuous.comp hpull)
        (fun φ => ?_)
      ext x
      rfl)

end HigherDimLQGMetric
