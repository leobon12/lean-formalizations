import GaussianLQG.LQG.Bridge.RotNormalized
import GaussianLQG.Metric.LFPPRotation
import LQGMetric.LFPP.WeylField

/-!
# Rotation covariance of LFPP for a whole-plane GFF plus a bounded continuous function

Extension of `GaussianLQG.ae_lfppDistE_rotDist` (whole-plane GFF) to the class of fields on which
the canonical γ-LQG metric is characterized. Let `h = h₀ + f` with `h₀` a whole-plane GFF and `f` a
random bounded continuous function (`LQGMetric.IsGFFPlusBddCont`), and let `‖a‖ = 1`.

* `rotDist_ofCont`: `f(a·)` as a distribution is the rotation of `f`;
* `heatMollify_ofCont_comp_mulCM`: `(f(a·))*_ε = f*_ε(a ·)` (the heat kernel is rotation
  invariant);
* `ae_heatMollify_rotDist_of_isGFFPlusBddCont`: almost surely `(h(a·))*_ε = h*_ε(a ·)`, from the
  GFF case `GaussianLQG.ae_heatMollify_rotDist` and additivity of the heat mollification where the
  defining limits exist (`LQGMetric.LFPP.heatMollify_add_of_tendsto`);
* `ae_lfppDistE_rotDist_of_isGFFPlusBddCont`: almost surely, for all `z, w`,
  `D^ε_{h(a·)}(z, w) = D^ε_h(a z, a w)`;
* `isGFFPlusBddCont_rotDist`: `h(a·)` is again a whole-plane GFF plus a bounded continuous
  function.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Filter Topology Set

namespace GaussianLQG

open LQGMetric

/-- multiplication by `a`, as a continuous map of `ℂ` -/
def mulCM (a : ℂ) : C(ℂ, ℂ) := ⟨fun x => a * x, continuous_const.mul continuous_id⟩

@[simp] lemma mulCM_apply (a x : ℂ) : mulCM a x = a * x := rfl

lemma rotDist_add (a : ℂ) (g k : DistC) : rotDist a (g + k) = rotDist a g + rotDist a k := rfl

lemma rotDist_sub (a : ℂ) (g k : DistC) : rotDist a (g - k) = rotDist a g - rotDist a k := rfl

/-- The rotation of the distribution of a continuous function `f` is the distribution of
`f(a·)`, for `‖a‖ = 1`. -/
lemma rotDist_ofCont {a : ℂ} (ha : ‖a‖ = 1) (f : C(ℂ, ℝ)) :
    rotDist a (ofCont f) = ofCont (f.comp (mulCM a)) := by
  have ha0 : a ≠ 0 := ne_zero_of_norm_eq_one ha
  ext φ
  rw [rotDist_apply, ofCont_apply, ofCont_apply]
  simp only [testRot_apply ha0]
  rw [← integral_comp_mul_of_norm_eq_one ha]
  refine integral_congr_ae (Eventually.of_forall fun x => ?_)
  simp only [ContinuousMap.comp_apply, mulCM_apply, inv_mul_cancel_left₀ ha0]

/-- `(f(a·))*_ε = f*_ε(a ·)` for a bounded continuous `f` and `‖a‖ = 1`. -/
lemma heatMollify_ofCont_comp_mulCM {a : ℂ} (ha : ‖a‖ = 1) (f : C(ℂ, ℝ)) {M : ℝ}
    (hM : ∀ w, |f w| ≤ M) {ε : ℝ} (hε : ε ≠ 0) (x : ℂ) :
    heatMollify ε (ofCont (f.comp (mulCM a))) x = heatMollify ε (ofCont f) (a * x) := by
  have ha0 : a ≠ 0 := ne_zero_of_norm_eq_one ha
  have hM' : ∀ w, |f.comp (mulCM a) w| ≤ M := fun w => hM _
  rw [heatMollify_ofCont _ M hM' ε hε, heatMollify_ofCont f M hM ε hε,
    ← integral_comp_mul_of_norm_eq_one ha (fun u => f u * heatKernel (ε ^ 2 / 2) (a * x) u)]
  refine integral_congr_ae (Eventually.of_forall fun w => ?_)
  simp only [ContinuousMap.comp_apply, mulCM_apply]
  rw [← heatKernel_rot ha, inv_mul_cancel_left₀ ha0]

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {h : Ω → DistC}

/-- **The heat-kernel rotation identity for a whole-plane GFF plus a bounded continuous
function**: almost surely, for all `x`, `(h(a·))*_ε(x) = h*_ε(a x)`. -/
theorem ae_heatMollify_rotDist_of_isGFFPlusBddCont (hh : IsGFFPlusBddCont h P) {ε : ℝ}
    (hε : ε ≠ 0) {a : ℂ} (ha : ‖a‖ = 1) :
    ∀ᵐ ω ∂P, ∀ x, heatMollify ε (rotDist a (h ω)) x = heatMollify ε (h ω) (a * x) := by
  obtain ⟨-, f, -, hfb, hg⟩ := hh
  filter_upwards [ae_heatMollify_rotDist hg hε ha, hg.ae_tendstoLocallyUniformly_heatMollify ε hε,
    (isWholePlaneGFF_rotDist hg ha).ae_tendstoLocallyUniformly_heatMollify ε hε]
    with ω hrot h1 h2 x
  obtain ⟨M, hM⟩ := hfb ω
  have hM' : ∀ w, |(f ω).comp (mulCM a) w| ≤ M := fun w => hM _
  have e1 : h ω = (h ω - ofCont (f ω)) + ofCont (f ω) := (sub_add_cancel _ _).symm
  have e2 : rotDist a (h ω) =
      rotDist a (h ω - ofCont (f ω)) + ofCont ((f ω).comp (mulCM a)) := by
    rw [← rotDist_ofCont ha, ← rotDist_add, sub_add_cancel]
  have t1 := (tendstoLocallyUniformlyOn_univ.2 h1.1).tendsto_at (mem_univ (a * x))
  have t2 := (tendstoLocallyUniformlyOn_univ.2 h2.1).tendsto_at (mem_univ x)
  calc heatMollify ε (rotDist a (h ω)) x
      = heatMollify ε (rotDist a (h ω - ofCont (f ω)) + ofCont ((f ω).comp (mulCM a))) x := by
        rw [← e2]
    _ = heatMollify ε (rotDist a (h ω - ofCont (f ω))) x +
          heatMollify ε (ofCont ((f ω).comp (mulCM a))) x :=
        LFPP.heatMollify_add_of_tendsto t2 (LFPP.tendsto_heatMollify_ofCont _ M hM' hε x)
    _ = heatMollify ε (h ω - ofCont (f ω)) (a * x) + heatMollify ε (ofCont (f ω)) (a * x) := by
        rw [hrot x, heatMollify_ofCont_comp_mulCM ha (f ω) hM hε x]
    _ = heatMollify ε ((h ω - ofCont (f ω)) + ofCont (f ω)) (a * x) :=
        (LFPP.heatMollify_add_of_tendsto t1
          (LFPP.tendsto_heatMollify_ofCont _ M hM hε (a * x))).symm
    _ = heatMollify ε (h ω) (a * x) := by rw [← e1]

/-- **Exact rotation covariance of LFPP for a whole-plane GFF plus a bounded continuous
function**: for `‖a‖ = 1`, almost surely, for all `z, w`,
`D^ε_{h(a·)}(z, w) = D^ε_h(a z, a w)`. -/
theorem ae_lfppDistE_rotDist_of_isGFFPlusBddCont (hh : IsGFFPlusBddCont h P) (ξ : ℝ) {ε : ℝ}
    (hε : ε ≠ 0) {a : ℂ} (ha : ‖a‖ = 1) :
    ∀ᵐ ω ∂P, ∀ z w : ℂ,
      lfppDistE ξ ε (rotDist a (h ω)) z w = lfppDistE ξ ε (h ω) (a * z) (a * w) := by
  filter_upwards [ae_heatMollify_rotDist_of_isGFFPlusBddCont hh hε ha] with ω hω z w
  exact lfppDistE_rotDist_of_heatMollify ha ξ ε (h ω) hω z w

/-- A rotated whole-plane GFF plus a bounded continuous function is again one. -/
theorem isGFFPlusBddCont_rotDist (hh : IsGFFPlusBddCont h P) {a : ℂ} (ha : ‖a‖ = 1) :
    IsGFFPlusBddCont (fun ω => rotDist a (h ω)) P := by
  obtain ⟨hm, f, hf, hfb, hg⟩ := hh
  refine ⟨(measurable_rotDist a).comp hm, fun ω => (f ω).comp (mulCM a),
    (ContinuousMap.continuous_precomp (mulCM a)).measurable.comp hf, fun ω => ?_, ?_⟩
  · obtain ⟨M, hM⟩ := hfb ω
    exact ⟨M, fun z => hM _⟩
  · have e : (fun ω => rotDist a (h ω) - ofCont ((f ω).comp (mulCM a))) =
        fun ω => rotDist a (h ω - ofCont (f ω)) := by
      funext ω
      rw [rotDist_sub, rotDist_ofCont ha]
    rw [e]
    exact isWholePlaneGFF_rotDist hg ha

end GaussianLQG
