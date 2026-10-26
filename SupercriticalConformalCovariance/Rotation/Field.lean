import GaussianLQG.LQG.Bridge.LFPPRotBdd
import GaussianLQG.LQG.Bridge.Affine
import SupercriticalLQGUniqueness.Frozen.IsStrongLQGMetric

/-!
Rotation field bridge for DG Proposition 1.9. The distribution
`GaussianLQG.rotDist a h` pairs with `φ` as `h (φ ∘ (a⁻¹ ·))`.
-/

set_option autoImplicit false
noncomputable section

open MeasureTheory
open LQGMetric

namespace SupercriticalConformalCovariance.Rotation

theorem isGFFPlusCont_rotDist {Ω : Type} [MeasurableSpace Ω]
    {P : Measure Ω} {h : Ω → DistC} (hh : IsGFFPlusCont h P)
    {a : ℂ} (ha : ‖a‖ = 1) :
    IsGFFPlusCont (fun ω => GaussianLQG.rotDist a (h ω)) P := by
  obtain ⟨hm, f, hf, hg⟩ := hh
  refine ⟨(GaussianLQG.measurable_rotDist a).comp hm,
    fun ω => (f ω).comp (GaussianLQG.mulCM a),
    (ContinuousMap.continuous_precomp (GaussianLQG.mulCM a)).measurable.comp hf, ?_⟩
  have e : (fun ω => GaussianLQG.rotDist a (h ω) -
      ofCont ((f ω).comp (GaussianLQG.mulCM a))) =
      fun ω => GaussianLQG.rotDist a (h ω - ofCont (f ω)) := by
    funext ω
    rw [GaussianLQG.rotDist_sub, GaussianLQG.rotDist_ofCont ha]
  rw [e]
  exact GaussianLQG.isWholePlaneGFF_rotDist hg ha

theorem rotDist_addConst {a : ℂ} (ha : ‖a‖ = 1)
    (h : DistC) (c : ℝ) :
    GaussianLQG.rotDist a (addConst h c) =
      addConst (GaussianLQG.rotDist a h) c :=
  GaussianLQG.rotDist_addConst ha h c

theorem rotDist_addFun {a : ℂ} (ha : ‖a‖ = 1)
    (h : DistC) (f : C(ℂ, ℝ)) :
    GaussianLQG.rotDist a (addFun h f) =
      addFun (GaussianLQG.rotDist a h) (f.comp (GaussianLQG.mulCM a)) := by
  rw [addFun, addFun, GaussianLQG.rotDist_add, GaussianLQG.rotDist_ofCont ha]

theorem rotDist_affineComp {a : ℂ} (ha : ‖a‖ = 1)
    {r : ℝ} (hr : 0 < r) (z : ℂ) (h : DistC) :
    GaussianLQG.rotDist a (affineComp r z h) =
      affineComp r (a⁻¹ * z) (GaussianLQG.rotDist a h) := by
  have ha0 := GaussianLQG.ne_zero_of_norm_eq_one ha
  ext φ
  rw [GaussianLQG.rotDist_apply, GFFInv.affineComp_apply,
    GFFInv.affineComp_apply, GaussianLQG.rotDist_apply]
  apply congrArg (fun t : ℝ => (r ^ 2)⁻¹ * t)
  apply congrArg h
  apply TestFunction.ext
  intro x
  rw [testAffinePull_apply r z hr.ne', GaussianLQG.testRot_apply ha0,
    GaussianLQG.testRot_apply ha0,
    testAffinePull_apply r (a⁻¹ * z) hr.ne']
  congr 1
  field_simp


end SupercriticalConformalCovariance.Rotation
