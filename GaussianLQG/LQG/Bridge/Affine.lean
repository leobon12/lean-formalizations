import GaussianLQG.LQG.Bridge.RotMetric
import GaussianLQG.LQG.Bridge.RotNormalized
import LQGMetric.Metric.WeylLQG
import LQGMetric.Field.MeasurableAvg

/-!
# Affine covariance in law of the canonical γ-LQG metric (blueprint (S4))

Let `D` be a canonical γ-LQG metric (`GaussianLQG.IsCanonicalLQGMetric`), `ξ = ξ_γ`, `Q = Q_γ`,
and let `h` be a whole-plane GFF normalized by `h_1(0) = 0`. Blueprint property (S4): for `z ∈ ℂ`
and `a ∈ ℂ ∖ {0}`, with `r = |a|`, the random function

  `(u, v) ↦ r^{-ξQ} e^{-ξ h_r(z)} D_h(z + a u, z + a v)`

has the same finite-dimensional distributions as `D_h`. We prove more: the two random continuous
functions have the same law on `C(ℂ × ℂ, ℝ)` (`IsCanonicalLQGMetric.map_affine_eq`), hence the
same law on `ℂ × ℂ → ℝ` with the product σ-algebra and the same finite-dimensional distributions
(`IsCanonicalLQGMetric.map_affine_eval_eq`, for any family of points `p : ι → ℂ × ℂ`).

Proof (blueprint Proposition `prop:S2-S5`). Write `a = r b` with `|b| = 1`, and let
`g = h(r·+z) − h_r(z)`. Then almost surely, for all `u, v`
(`IsCanonicalLQGMetric.ae_affine_eq`):

* Axiom IV (`LQGMetric.IsStrongLQGMetric.coord`) at scale `r > 0` and centre `z`:
  `D_h(r u' + z, r v' + z) = D_{h(r·+z) + Q log r}(u', v')`;
* Weyl scaling by constants (`LQGMetric.IsStrongLQGMetric.ae_dist_addConst`) for the field
  `h(r·+z)`: `D_{h(r·+z) + c} = e^{ξ c} D_{h(r·+z)}` for all `c`, used with `c = Q log r` and
  `c = −h_r(z)`;
* rotation covariance (`IsCanonicalLQGMetric.ae_rotDist`) for the whole-plane GFF `g`:
  `D_g(b u, b v) = D_{g(b·)}(u, v)`.

Together: `r^{-ξQ} e^{-ξ h_r(z)} D_h(z + a u, z + a v) = D_{g(b·)}(u, v)`. The same ingredients
give blueprint (F3) for complex `a` (`IsCanonicalLQGMetric.ae_coord`):
`D_h(z + a u, z + a v) = D_{h(z + a·) + Q log |a|}(u, v)`. Finally `g(b·)` has the
law of `h`: `g =ᵈ h` (`LQGMetric.CircleAvg.map_affine_sub_circleAvg`) and `h(b·) =ᵈ h`
(`GaussianLQG.map_rotDist_eq`). Since `h ↦ D_h` is measurable, `D_{g(b·)} =ᵈ D_h`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Filter Topology

namespace GaussianLQG

open LQGMetric

/-- `(u, v) ↦ (z + a u, z + a v)` -/
def affArgs (z a : ℂ) : C(ℂ × ℂ, ℂ × ℂ) :=
  ⟨fun p => (z + a * p.1, z + a * p.2), by fun_prop⟩

@[simp] lemma affArgs_apply (z a : ℂ) (p : ℂ × ℂ) :
    affArgs z a p = (z + a * p.1, z + a * p.2) := rfl

/-- `a / |a|` is a unit complex number. -/
lemma norm_div_norm_eq_one {a : ℂ} (ha : a ≠ 0) : ‖a / (‖a‖ : ℂ)‖ = 1 := by
  rw [norm_div, Complex.norm_real, Real.norm_of_nonneg (norm_nonneg a),
    div_self (norm_ne_zero_iff.2 ha)]

/-- `|a| (a / |a|) = a` -/
lemma norm_mul_div_norm {a : ℂ} (ha : a ≠ 0) : (‖a‖ : ℂ) * (a / (‖a‖ : ℂ)) = a :=
  mul_div_cancel₀ a (Complex.ofReal_ne_zero.2 (norm_ne_zero_iff.2 ha))

/-- `r^{-ξQ} e^{-ξ c} e^{ξ Q log r} = e^{ξ (-c)}` for `r > 0`. -/
lemma rpow_mul_exp_mul_exp {r : ℝ} (hr : 0 < r) (ξ q c : ℝ) :
    r ^ (-(ξ * q)) * Real.exp (-(ξ * c)) * Real.exp (ξ * (q * Real.log r)) =
      Real.exp (ξ * -c) := by
  rw [Real.rpow_def_of_pos hr, ← Real.exp_add, ← Real.exp_add]
  congr 1
  ring

/-- `(g + c)(b·) = g(b·) + c` for `‖b‖ = 1`. -/
lemma rotDist_addConst {b : ℂ} (hb : ‖b‖ = 1) (g : DistC) (c : ℝ) :
    rotDist b (addConst g c) = addConst (rotDist b g) c := by
  ext φ
  rw [rotDist_apply, GFFInv.addConst_apply, GFFInv.addConst_apply, rotDist_apply,
    integral_testRot hb]

variable {γ : ℝ} {D : DistC → ContMetric}

namespace IsCanonicalLQGMetric

/-- **Blueprint Proposition `prop:metric-facts` (F3), complex `a`.** For a canonical γ-LQG metric
`D`, a whole-plane GFF `h`, `z ∈ ℂ` and `a ≠ 0` with `r = |a|`, `b = a / r`, almost surely, for
all `u, v`, `D_h(z + a u, z + a v) = D_{h(z + a·) + Q log r}(u, v)`, where
`h(z + a·) = (h(r·+z))(b·) = rotDist b (affineComp r z h)`. -/
theorem ae_coord (hD : IsCanonicalLQGMetric γ D) {Ω : Type} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] {h : Ω → DistC} (hh : IsWholePlaneGFF h P) (z : ℂ)
    {a : ℂ} (ha : a ≠ 0) :
    ∀ᵐ ω ∂P, ∀ u v : ℂ, (D (h ω)).1 (z + a * u, z + a * v) =
      (D (addConst (rotDist (a / (‖a‖ : ℂ)) (affineComp ‖a‖ z (h ω)))
        (Q γ * Real.log ‖a‖))).1 (u, v) := by
  set r := ‖a‖ with hr_def
  have hr : 0 < r := norm_pos_iff.2 ha
  set b : ℂ := a / (r : ℂ) with hb_def
  have hb : ‖b‖ = 1 := norm_div_norm_eq_one ha
  have hab : (r : ℂ) * b = a := norm_mul_div_norm ha
  have hk : IsWholePlaneGFF (fun ω => addConst (affineComp r z (h ω)) (Q γ * Real.log r)) P :=
    (hh.affineComp hr z).addConst (c := fun _ => Q γ * Real.log r) measurable_const
  filter_upwards [hD.1.coord P h (isGFFPlusCont_of_isWholePlaneGFF hh) r hr z,
    hD.ae_rotDist hk hb] with ω hcoord hrot u v
  have e : ∀ x : ℂ, z + a * x = (r : ℂ) * (b * x) + z := fun x => by
    rw [← mul_assoc, hab, add_comm]
  rw [← rotDist_addConst hb, hrot u v, e u, e v, hcoord]

/-- **(S4), pathwise form.** For a canonical γ-LQG metric `D`, a whole-plane GFF `h`, `z ∈ ℂ` and
`a ≠ 0` with `r = |a|`, almost surely, for all `u, v`,
`r^{-ξQ} e^{-ξ h_r(z)} D_h(z + a u, z + a v) = D_{g(b·)}(u, v)`, where `b = a / r` and
`g = h(r·+z) − h_r(z)`. -/
theorem ae_affine_eq (hD : IsCanonicalLQGMetric γ D) {Ω : Type} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] {h : Ω → DistC} (hh : IsWholePlaneGFF h P) (z : ℂ)
    {a : ℂ} (ha : a ≠ 0) :
    ∀ᵐ ω ∂P, ∀ u v : ℂ,
      ‖a‖ ^ (-(xiGamma γ * Q γ)) * Real.exp (-(xiGamma γ * circleAvg (h ω) ‖a‖ z)) *
          (D (h ω)).1 (z + a * u, z + a * v) =
        (D (rotDist (a / (‖a‖ : ℂ))
          (addConst (affineComp ‖a‖ z (h ω)) (-circleAvg (h ω) ‖a‖ z)))).1 (u, v) := by
  set r := ‖a‖ with hr_def
  have hr : 0 < r := norm_pos_iff.2 ha
  set b : ℂ := a / (r : ℂ) with hb_def
  have hb : ‖b‖ = 1 := norm_div_norm_eq_one ha
  have hab : (r : ℂ) * b = a := norm_mul_div_norm ha
  have hf : IsWholePlaneGFF (fun ω => affineComp r z (h ω)) P := hh.affineComp hr z
  have hg : IsWholePlaneGFF
      (fun ω => addConst (affineComp r z (h ω)) (-circleAvg (h ω) r z)) P :=
    hf.addConst ((measurable_circleAvg_left r z).comp hh.measurable).neg
  filter_upwards [hD.1.coord P h (isGFFPlusCont_of_isWholePlaneGFF hh) r hr z,
    hD.1.ae_dist_addConst (isGFFPlusCont_of_isWholePlaneGFF hf), hD.ae_rotDist hg hb]
    with ω hcoord hweyl hrot u v
  have e : ∀ x : ℂ, z + a * x = (r : ℂ) * (b * x) + z := fun x => by
    rw [← mul_assoc, hab, add_comm]
  rw [hrot u v, e u, e v, hcoord (b * u) (b * v), hweyl, hweyl,
    ← rpow_mul_exp_mul_exp hr (xiGamma γ) (Q γ) (circleAvg (h ω) r z)]
  ring

variable {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} {h : Ω → DistC}

/-- The random continuous function `(u, v) ↦ r^{-ξQ} e^{-ξ h_r(z)} D_h(z + a u, z + a v)` of
(S4) is measurable. -/
theorem measurable_affine (hD : IsCanonicalLQGMetric γ D) (hh : Measurable h) (z a : ℂ) :
    Measurable fun ω => (‖a‖ ^ (-(xiGamma γ * Q γ)) *
      Real.exp (-(xiGamma γ * circleAvg (h ω) ‖a‖ z))) • (D (h ω)).1.comp (affArgs z a) := by
  refine ContinuousMap.measurable_iff_eval.2 fun p => ?_
  simp only [ContinuousMap.smul_apply, ContinuousMap.comp_apply, smul_eq_mul]
  exact (measurable_const.mul (((measurable_circleAvg_left ‖a‖ z).comp hh).const_mul
    (xiGamma γ)).neg.exp).mul (hD.measurable_dist hh _ _)

/-- **Blueprint (S4): affine covariance in law of the canonical γ-LQG metric.** For a canonical
γ-LQG metric `D`, a whole-plane GFF `h` normalized by `h_1(0) = 0`, `z ∈ ℂ` and `a ≠ 0` with
`r = |a|`, the random continuous function
`(u, v) ↦ r^{-ξQ} e^{-ξ h_r(z)} D_h(z + a u, z + a v)` has the law of `D_h` on `C(ℂ × ℂ, ℝ)`. -/
theorem map_affine_eq (hD : IsCanonicalLQGMetric γ D) [IsProbabilityMeasure P]
    (hh : IsNormalizedWPGFF h P) (z : ℂ) {a : ℂ} (ha : a ≠ 0) :
    P.map (fun ω => (‖a‖ ^ (-(xiGamma γ * Q γ)) *
        Real.exp (-(xiGamma γ * circleAvg (h ω) ‖a‖ z))) • (D (h ω)).1.comp (affArgs z a)) =
      P.map (fun ω => (D (h ω)).1) := by
  set r := ‖a‖ with hr_def
  have hr : 0 < r := norm_pos_iff.2 ha
  set b : ℂ := a / (r : ℂ) with hb_def
  have hb : ‖b‖ = 1 := norm_div_norm_eq_one ha
  set g : Ω → DistC := fun ω => addConst (affineComp r z (h ω)) (-circleAvg (h ω) r z)
    with hg_def
  have hgm : Measurable g := ((hh.1.affineComp hr z).addConst
    ((measurable_circleAvg_left r z).comp hh.1.measurable).neg).measurable
  have hlaw : P.map (fun ω => rotDist b (g ω)) = P.map h := by
    calc P.map (fun ω => rotDist b (g ω)) = (P.map g).map (rotDist b) :=
          (Measure.map_map (measurable_rotDist b) hgm).symm
      _ = (P.map h).map (rotDist b) := by rw [CircleAvg.map_affine_sub_circleAvg hh hr z]
      _ = P.map (fun ω => rotDist b (h ω)) := Measure.map_map (measurable_rotDist b) hh.1.measurable
      _ = P.map h := map_rotDist_eq hh hb
  have hae : (fun ω => (r ^ (-(xiGamma γ * Q γ)) *
      Real.exp (-(xiGamma γ * circleAvg (h ω) r z))) • (D (h ω)).1.comp (affArgs z a)) =ᵐ[P]
      fun ω => (D (rotDist b (g ω))).1 := by
    filter_upwards [hD.ae_affine_eq hh.1 z ha] with ω hω
    ext p
    simp only [ContinuousMap.smul_apply, ContinuousMap.comp_apply, affArgs_apply, smul_eq_mul]
    exact hω p.1 p.2
  rw [Measure.map_congr hae]
  calc P.map (fun ω => (D (rotDist b (g ω))).1)
      = (P.map fun ω => rotDist b (g ω)).map fun g' => (D g').1 :=
        (Measure.map_map hD.measurable_coe_comp ((measurable_rotDist b).comp hgm)).symm
    _ = (P.map h).map fun g' => (D g').1 := by rw [hlaw]
    _ = P.map (fun ω => (D (h ω)).1) := Measure.map_map hD.measurable_coe_comp hh.1.measurable

/-- **Blueprint (S4), finite-dimensional distributions.** Under the hypotheses of
`map_affine_eq`, for every family of points `p : ι → ℂ × ℂ` (e.g. `ι = Fin n`), the vectors
`(r^{-ξQ} e^{-ξ h_r(z)} D_h(z + a u_i, z + a v_i))_i` and `(D_h(u_i, v_i))_i`, `p i = (u_i, v_i)`,
have the same law on `ι → ℝ` (product σ-algebra). For `ι = ℂ × ℂ` and `p = id` this is the
equality of the laws of the two random functions on `ℂ × ℂ → ℝ`. -/
theorem map_affine_eval_eq (hD : IsCanonicalLQGMetric γ D) [IsProbabilityMeasure P]
    (hh : IsNormalizedWPGFF h P) (z : ℂ) {a : ℂ} (ha : a ≠ 0) {ι : Type*} (p : ι → ℂ × ℂ) :
    P.map (fun ω i => ‖a‖ ^ (-(xiGamma γ * Q γ)) *
        Real.exp (-(xiGamma γ * circleAvg (h ω) ‖a‖ z)) *
          (D (h ω)).1 (z + a * (p i).1, z + a * (p i).2)) =
      P.map (fun ω i => (D (h ω)).1 (p i)) := by
  set E : C(ℂ × ℂ, ℝ) → ι → ℝ := fun d i => d (p i) with hE_def
  have hE : Measurable E := measurable_pi_iff.2 fun i => ContinuousMap.measurable_eval (p i)
  have e1 : (fun ω i => ‖a‖ ^ (-(xiGamma γ * Q γ)) *
      Real.exp (-(xiGamma γ * circleAvg (h ω) ‖a‖ z)) *
        (D (h ω)).1 (z + a * (p i).1, z + a * (p i).2)) =
      E ∘ fun ω => (‖a‖ ^ (-(xiGamma γ * Q γ)) *
        Real.exp (-(xiGamma γ * circleAvg (h ω) ‖a‖ z))) • (D (h ω)).1.comp (affArgs z a) := by
    funext ω i
    simp only [hE_def, Function.comp_apply, ContinuousMap.smul_apply, ContinuousMap.comp_apply,
      affArgs_apply, smul_eq_mul]
  have e2 : (fun ω i => (D (h ω)).1 (p i)) = E ∘ fun ω => (D (h ω)).1 := rfl
  rw [e1, e2, ← Measure.map_map hE (hD.measurable_affine hh.1.measurable z a),
    ← Measure.map_map hE (hD.measurable_coe hh.1.measurable), hD.map_affine_eq hh z ha]

end IsCanonicalLQGMetric

end GaussianLQG
