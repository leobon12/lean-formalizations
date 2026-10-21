import SmallGammaGeodesics.CC.ConfMetric
import SmallGammaGeodesics.CC.Coupling
import LQGMetric.Papers.GM.S1.Dilate
import LQGMetric.Metric.InternalOps
import LQGMetric.Field.MeasurableAvg

/-!
# [3] Lemma 2.6, corrected (ER2): the zoom identities under real scaling (track CC, packet CC6a, T1)

Source: `planning/audits/CC0-conformal-covariance-plan.md`, Details (a) **D8** (Gwynne–Miller,
arXiv:1905.00384, Lemma 2.6, with erratum ER2: the codomain is translated by `ϕ(z)`, not by `z`).

For `z ∈ ℂ` and `r > 0`, the zoom of D1.6 (CC1, `IsConfCoupling.zoom`) with constant `c = −h_r(z)`
is
* `ϕ̃ = zoomMap ϕ z r` (`w ↦ r⁻¹(ϕ(z + r w) − ϕ(z))`) on `W̃ = zoomSet z r W`, `Ṽ = zoomSet z r V`;
* `h̃ = h(z + r·) − h_r(z)` (`addConst (affineComp r z h) (−circleAvg h r z)`);
* `h̄̃ = h̄(ϕ(z) + r·)` (`affineComp r (ϕ z) h̄`);
* `f̃ = f(ϕ(z) + r·) − h_r(z)` (`zoomCont f (ϕ z) r (−circleAvg h r z)`).

**Lemma 2.6** (`lemma26`): `(h̃, h̄̃, f̃)` is again a coupling for `ϕ̃`, and a.s., for all `u, v`,
* `D^{ϕ̃}(u, v) = r^{−ξQ} e^{−ξ h_r(z)} D^ϕ(z + r u, z + r v)` (`ae_confMetric_lemma26`);
* `D_{h̃}(u, v) = r^{−ξQ} e^{−ξ h_r(z)} D_h(z + r u, z + r v)` (`ae_dist_lemma26`);
* `D_{h̃}(u, v; r⁻¹(A − z)) = r^{−ξQ} e^{−ξ h_r(z)} D_h(z + r u, z + r v; A)` for every set `A`
  (`ae_internal_lemma26`).

Only real scaling enters (Axiom IV, `IsStrongLQGMetric.coord`). The identities hold for **every**
additive constant `c` at once (`ae_dist_zoom`, `ae_internal_zoom`, `ae_confMetric_zoom`): the factor
is then `e^{ξ(c − Q log r)}`; the circle average enters only through `c = −h_r(z)`.

Proof (D8): Axiom IV at centre `a` and scale `r` for the GFF-plus-continuous field `X` (`X = h`,
resp. `X = h̄ + f`) gives `D_X(a + r·, a + r·) = D_{X(a + r·) + Q log r}`; Weyl scaling by constants
(`IsStrongLQGMetric.ae_dist_addConst`, a.s. for all constants simultaneously, hence also for a
random one) turns `Q log r` into `c`. Internal metrics transform in the same way, because
`w ↦ a + r w` is then a bijection multiplying all distances by one factor
(`MetricGeometry.internalEDist_image_of_edist_eq`, LM S-int (d)): `internal_zoomAff_eq`, the real
case of `internal_affineC_eq` (any complex `w ↦ a + c w`, `c ≠ 0`, for the rotations of D10;
preimage form `internal_affineC_preimage_eq`). Finally `ϕ(z) + r ϕ̃(u) = ϕ(z + r u)`
(`zoomAff_zoomMap`) and `ϕ̃(Ṽ) = r⁻¹(ϕ(V) − ϕ(z))` (`image_zoomMap_zoomSet`).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Filter Topology Set Function
open scoped ENNReal

namespace SmallGammaGeodesics.CC

open LQGMetric LQGMetric.MetricGeometry

/-! ## 1. Internal metrics under an affine similarity (deterministic) -/

/-- the complex affine bijection `w ↦ a + c w` of `ℂ`, for `c ≠ 0` -/
def affEquivC {c : ℂ} (hc : c ≠ 0) (a : ℂ) : ℂ ≃ ℂ where
  toFun w := a + c * w
  invFun x := (x - a) / c
  left_inv w := by
    show (a + c * w - a) / c = w
    rw [add_sub_cancel_left, mul_div_cancel_left₀ w hc]
  right_inv x := by
    show a + c * ((x - a) / c) = x
    rw [mul_div_cancel₀ (x - a) hc, add_sub_cancel]

theorem affEquivC_apply {c : ℂ} (hc : c ≠ 0) (a w : ℂ) : affEquivC hc a w = a + c * w :=
  rfl

/-- **Internal metrics under a complex affine similarity** (deterministic): if `w ↦ a + c w`
(`c ∈ ℂ ∖ {0}`) multiplies the `X`-distances by `k > 0` into `Y`-distances, it multiplies internal
metrics by `k`: `Y(a + c u, a + c v; a + c A) = k X(u, v; A)` for every set `A` and all `u, v`
(LM S-int (d), `MetricGeometry.internalEDist_image_of_edist_eq`). -/
theorem internal_affineC_eq {X Y : ContMetric} {c : ℂ} (hc : c ≠ 0) (a : ℂ) {k : ℝ} (hk : 0 < k)
    (hXY : ∀ x y : ℂ, Y.1 (a + c * x, a + c * y) = k * X.1 (x, y)) (A : Set ℂ) (u v : ℂ) :
    Y.internal ((fun w : ℂ => a + c * w) '' A) (a + c * u) (a + c * v) =
      ENNReal.ofReal k * X.internal A u v := by
  let e : X.Space ≃ Y.Space := affEquivC hc a
  have he : ∀ x y : X.Space, edist (e x) (e y) = ENNReal.ofReal k * edist x y := fun x y => by
    rw [edist_dist, edist_dist, ← ENNReal.ofReal_mul hk.le]
    congr 1
    exact hXY x y
  have hk0 : ENNReal.ofReal k ≠ 0 := (ENNReal.ofReal_pos.2 hk).ne'
  have h := internalEDist_image_of_edist_eq e hk0 ENNReal.ofReal_ne_top he (X.pt '' A) u v
  unfold ContMetric.internal
  have hs : Y.pt '' ((fun w : ℂ => a + c * w) '' A) = e '' (X.pt '' A) := by
    rw [image_image, image_image]
    rfl
  rw [hs]
  exact h

/-- **The preimage form**: `Y(a + c u, a + c v; A) = k X(u, v; {w | a + c w ∈ A})`. -/
theorem internal_affineC_preimage_eq {X Y : ContMetric} {c : ℂ} (hc : c ≠ 0) (a : ℂ) {k : ℝ}
    (hk : 0 < k) (hXY : ∀ x y : ℂ, Y.1 (a + c * x, a + c * y) = k * X.1 (x, y)) (A : Set ℂ)
    (u v : ℂ) :
    Y.internal A (a + c * u) (a + c * v) =
      ENNReal.ofReal k * X.internal ((fun w : ℂ => a + c * w) ⁻¹' A) u v := by
  rw [← internal_affineC_eq hc a hk hXY]
  congr 1
  exact (image_preimage_eq A (affEquivC hc a).surjective).symm

/-- the real affine bijection `w ↦ a + r w` of `ℂ`, for `r ≠ 0` -/
def zoomAffEquiv {r : ℝ} (hr : r ≠ 0) (a : ℂ) : ℂ ≃ ℂ where
  toFun w := a + (r : ℂ) * w
  invFun x := (x - a) / r
  left_inv w := div_zoomAff hr a w
  right_inv x := zoomAff_div hr a x

theorem zoomAffEquiv_apply {r : ℝ} (hr : r ≠ 0) (a w : ℂ) :
    zoomAffEquiv hr a w = a + (r : ℂ) * w :=
  rfl

/-- `w ↦ a + r w` maps `r⁻¹(A − a)` onto `A`. -/
theorem image_zoomAff_zoomSet {r : ℝ} (hr : r ≠ 0) (a : ℂ) (A : Set ℂ) :
    (fun w : ℂ => a + (r : ℂ) * w) '' zoomSet a r A = A :=
  image_preimage_eq A (zoomAffEquiv hr a).surjective

/-- **Internal metrics under a real affine similarity** (the case `c = r ∈ ℝ` of
`internal_affineC_eq`). -/
theorem internal_zoomAff_eq {X Y : ContMetric} {r : ℝ} (hr : r ≠ 0) (a : ℂ) {k : ℝ} (hk : 0 < k)
    (hXY : ∀ x y : ℂ, Y.1 (a + (r : ℂ) * x, a + (r : ℂ) * y) = k * X.1 (x, y)) (A : Set ℂ)
    (u v : ℂ) :
    Y.internal ((fun w : ℂ => a + (r : ℂ) * w) '' A) (a + (r : ℂ) * u) (a + (r : ℂ) * v) =
      ENNReal.ofReal k * X.internal A u v :=
  internal_affineC_eq (Complex.ofReal_ne_zero.2 hr) a hk hXY A u v

/-! ## 2. Field identities -/

private theorem ofCont_add_zoom (f g : C(ℂ, ℝ)) : ofCont (f + g) = ofCont f + ofCont g := by
  unfold ofCont
  rw [ContinuousMap.coe_add]
  exact Distribution.ofFun_add (f.continuous.locallyIntegrable.locallyIntegrableOn _)
    (g.continuous.locallyIntegrable.locallyIntegrableOn _)

/-- `(X + f) + c = X + (f + c)` -/
theorem addConst_addFun_eq (X : DistC) (f : C(ℂ, ℝ)) (c : ℝ) :
    addConst (addFun X f) c = addFun X (f + ContinuousMap.const ℂ c) := by
  simp only [addConst, addFun, ofCont_add_zoom, add_assoc]

/-- `f(a + r·) + c = f ∘ (r · + a) + c` as continuous functions -/
theorem zoomCont_eq_comp_add (f : C(ℂ, ℝ)) (a : ℂ) (r c : ℝ) :
    zoomCont f a r c = f.comp (affinePt r a) + ContinuousMap.const ℂ c := by
  ext y
  simp only [zoomCont_apply, ContinuousMap.add_apply, ContinuousMap.comp_apply, affinePt_apply,
    ContinuousMap.const_apply, add_comm a]

/-- **The zoomed coupled field** (D1.6): `h̄(a + r·) + (f(a + r·) + c) = (h̄ + f)(a + r·) + c`. -/
theorem addFun_affineComp_zoomCont {r : ℝ} (hr : 0 < r) (a : ℂ) (hbar : DistC) (f : C(ℂ, ℝ))
    (c : ℝ) :
    addFun (affineComp r a hbar) (zoomCont f a r c) =
      addConst (affineComp r a (addFun hbar f)) c := by
  rw [GM.affineComp_addFun hr, addConst_addFun_eq, zoomCont_eq_comp_add]

/-! ## 3. The zoom identities for every additive constant -/

section Zoom

variable {γ : ℝ} {D : DistC → ContMetric} {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
  [IsProbabilityMeasure P]

/-- **The zoom identity for the metric** (Axiom IV + Weyl by constants): for a GFF plus a continuous
function `X`, a.s., for every constant `c` and all `u, v`,
`D_{X(a + r·) + c}(u, v) = e^{ξ(c − Q log r)} D_X(a + r u, a + r v)`. -/
theorem ae_dist_zoom (hD : IsStrongLQGMetric γ D) {X : Ω → DistC} (hX : IsGFFPlusCont X P)
    {r : ℝ} (hr : 0 < r) (a : ℂ) :
    ∀ᵐ ω ∂P, ∀ (c : ℝ) (u v : ℂ),
      (D (addConst (affineComp r a (X ω)) c)).1 (u, v) =
        Real.exp (xiGamma γ * (c - Q γ * Real.log r)) *
          (D (X ω)).1 (a + (r : ℂ) * u, a + (r : ℂ) * v) := by
  filter_upwards [hD.coord P X hX r hr a,
    hD.ae_dist_addConst (GM.isGFFPlusCont_affineComp hX hr a)] with ω h1 h2 c u v
  have e1 : (D (X ω)).1 (a + (r : ℂ) * u, a + (r : ℂ) * v) =
      Real.exp (xiGamma γ * (Q γ * Real.log r)) * (D (affineComp r a (X ω))).1 (u, v) := by
    rw [add_comm a, add_comm a, h1 u v, h2]
  rw [h2 c u v, e1, ← mul_assoc, ← Real.exp_add]
  congr 2
  ring

/-- **The zoom identity for internal metrics**: a.s., for every constant `c`, every set `A` and all
`u, v`, `D_{X(a + r·) + c}(u, v; r⁻¹(A − a)) = e^{ξ(c − Q log r)} D_X(a + r u, a + r v; A)`. -/
theorem ae_internal_zoom (hD : IsStrongLQGMetric γ D) {X : Ω → DistC} (hX : IsGFFPlusCont X P)
    {r : ℝ} (hr : 0 < r) (a : ℂ) :
    ∀ᵐ ω ∂P, ∀ (c : ℝ) (A : Set ℂ) (u v : ℂ),
      (D (addConst (affineComp r a (X ω)) c)).internal (zoomSet a r A) u v =
        ENNReal.ofReal (Real.exp (xiGamma γ * (c - Q γ * Real.log r))) *
          (D (X ω)).internal A (a + (r : ℂ) * u) (a + (r : ℂ) * v) := by
  filter_upwards [ae_dist_zoom hD hX hr a] with ω hω c A u v
  set k : ℝ := Real.exp (xiGamma γ * (c - Q γ * Real.log r)) with hk
  have hk0 : 0 < k := Real.exp_pos _
  have hXY : ∀ x y : ℂ, (D (X ω)).1 (a + (r : ℂ) * x, a + (r : ℂ) * y) =
      k⁻¹ * (D (addConst (affineComp r a (X ω)) c)).1 (x, y) := fun x y => by
    rw [hω c x y, ← mul_assoc, inv_mul_cancel₀ hk0.ne', one_mul]
  have h := internal_zoomAff_eq (X := D (addConst (affineComp r a (X ω)) c)) (Y := D (X ω))
    hr.ne' a (inv_pos.2 hk0) hXY (zoomSet a r A) u v
  rw [image_zoomAff_zoomSet hr.ne' a A] at h
  rw [h, ← mul_assoc, ← ENNReal.ofReal_mul hk0.le, mul_inv_cancel₀ hk0.ne', ENNReal.ofReal_one,
    one_mul]

/-- **The zoom identity for the transported metric** (D8 with any constant `c`): for a whole-plane
GFF `h̄` and a measurable random continuous `f`, a.s., for every constant `c`, every `V` and all
`u, v`: `D^{ϕ̃}(u, v) = e^{ξ(c − Q log r)} D^ϕ(z + r u, z + r v)`, where `D^{ϕ̃}` is the transported
metric of the zoomed data `(ϕ̃, Ṽ, h̄(ϕ(z) + r·), f(ϕ(z) + r·) + c)`. -/
theorem ae_confMetric_zoom (hD : IsStrongLQGMetric γ D) {hbar : Ω → DistC} {f : Ω → C(ℂ, ℝ)}
    (hhb : IsWholePlaneGFF hbar P) (hf : Measurable f) (ϕ : ℂ → ℂ) (z : ℂ) {r : ℝ} (hr : 0 < r) :
    ∀ᵐ ω ∂P, ∀ (c : ℝ) (V : Set ℂ) (u v : ℂ),
      confMetric D (zoomMap ϕ z r) (zoomSet z r V) (affineComp r (ϕ z) (hbar ω))
          (zoomCont (f ω) (ϕ z) r c) u v =
        ENNReal.ofReal (Real.exp (xiGamma γ * (c - Q γ * Real.log r))) *
          confMetric D ϕ V (hbar ω) (f ω) (z + (r : ℂ) * u) (z + (r : ℂ) * v) := by
  filter_upwards [ae_internal_zoom hD (isGFFPlusCont_addFun_of_wp hhb hf) hr (ϕ z)]
    with ω hω c V u v
  rw [confMetric_def, confMetric_def, addFun_affineComp_zoomCont hr, image_zoomMap_zoomSet hr.ne',
    hω c (ϕ '' V) _ _, zoomAff_zoomMap hr.ne', zoomAff_zoomMap hr.ne']

end Zoom

/-! ## 4. Lemma 2.6 (`c = −h_r(z)`) -/

section Lemma26

variable {γ : ℝ} {D : DistC → ContMetric} {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
  [IsProbabilityMeasure P]

/-- `e^{ξ(−h − Q log r)} = r^{−ξQ} e^{−ξ h}` for `r > 0` -/
theorem exp_zoom_factor (ξ Qγ hr' : ℝ) {r : ℝ} (hr : 0 < r) :
    Real.exp (ξ * (-hr' - Qγ * Real.log r)) = r ^ (-(ξ * Qγ)) * Real.exp (-(ξ * hr')) := by
  rw [Real.rpow_def_of_pos hr, ← Real.exp_add]
  congr 1
  ring

/-- **[3] Lemma 2.6, metric part** (D8): with `h̃ = h(z + r·) − h_r(z)`, a.s. for all `u, v`,
`D_{h̃}(u, v) = r^{−ξQ} e^{−ξ h_r(z)} D_h(z + r u, z + r v)`. -/
theorem ae_dist_lemma26 (hD : IsStrongLQGMetric γ D) {h : Ω → DistC} (hh : IsGFFPlusCont h P)
    (z : ℂ) {r : ℝ} (hr : 0 < r) :
    ∀ᵐ ω ∂P, ∀ u v : ℂ,
      (D (addConst (affineComp r z (h ω)) (-circleAvg (h ω) r z))).1 (u, v) =
        r ^ (-(xiGamma γ * Q γ)) * Real.exp (-(xiGamma γ * circleAvg (h ω) r z)) *
          (D (h ω)).1 (z + (r : ℂ) * u, z + (r : ℂ) * v) := by
  filter_upwards [ae_dist_zoom hD hh hr z] with ω hω u v
  rw [hω, exp_zoom_factor _ _ _ hr]

/-- **[3] Lemma 2.6, internal-metric part**: a.s., for every set `A` and all `u, v`,
`D_{h̃}(u, v; r⁻¹(A − z)) = r^{−ξQ} e^{−ξ h_r(z)} D_h(z + r u, z + r v; A)`. -/
theorem ae_internal_lemma26 (hD : IsStrongLQGMetric γ D) {h : Ω → DistC} (hh : IsGFFPlusCont h P)
    (z : ℂ) {r : ℝ} (hr : 0 < r) :
    ∀ᵐ ω ∂P, ∀ (A : Set ℂ) (u v : ℂ),
      (D (addConst (affineComp r z (h ω)) (-circleAvg (h ω) r z))).internal (zoomSet z r A) u v =
        ENNReal.ofReal (r ^ (-(xiGamma γ * Q γ)) * Real.exp (-(xiGamma γ * circleAvg (h ω) r z))) *
          (D (h ω)).internal A (z + (r : ℂ) * u) (z + (r : ℂ) * v) := by
  filter_upwards [ae_internal_zoom hD hh hr z] with ω hω A u v
  rw [hω, exp_zoom_factor _ _ _ hr]

/-- **[3] Lemma 2.6, transported-metric part** (D8, erratum ER2): for the zoomed data
`(ϕ̃, Ṽ, h̄̃, f̃) = (zoomMap ϕ z r, zoomSet z r V, h̄(ϕ(z) + r·), f(ϕ(z) + r·) − h_r(z))`, a.s. for
every `V` and all `u, v`, `D^{ϕ̃}(u, v) = r^{−ξQ} e^{−ξ h_r(z)} D^ϕ(z + r u, z + r v)`. -/
theorem ae_confMetric_lemma26 (hD : IsStrongLQGMetric γ D) {h hbar : Ω → DistC}
    {f : Ω → C(ℂ, ℝ)} (hhb : IsWholePlaneGFF hbar P) (hf : Measurable f) (ϕ : ℂ → ℂ) (z : ℂ)
    {r : ℝ} (hr : 0 < r) :
    ∀ᵐ ω ∂P, ∀ (V : Set ℂ) (u v : ℂ),
      confMetric D (zoomMap ϕ z r) (zoomSet z r V) (affineComp r (ϕ z) (hbar ω))
          (zoomCont (f ω) (ϕ z) r (-circleAvg (h ω) r z)) u v =
        ENNReal.ofReal (r ^ (-(xiGamma γ * Q γ)) * Real.exp (-(xiGamma γ * circleAvg (h ω) r z))) *
          confMetric D ϕ V (hbar ω) (f ω) (z + (r : ℂ) * u) (z + (r : ℂ) * v) := by
  filter_upwards [ae_confMetric_zoom hD hhb hf ϕ z hr] with ω hω V u v
  rw [hω, exp_zoom_factor _ _ _ hr]

/-- **[3] Lemma 2.6, corrected (ER2), bundled** (packet CC6a, T1; CC0 D8). Let `(h, h̄, f)` be a
coupling for `IsConfNbhd ϕ W V`, `z ∈ ℂ` and `r > 0`. Put `h̃ = h(z + r·) − h_r(z)`,
`h̄̃ = h̄(ϕ(z) + r·)` and `f̃ = f(ϕ(z) + r·) − h_r(z)`. Then
1. `(zoomMap ϕ z r, zoomSet z r W, zoomSet z r V)` is a conformal neighbourhood;
2. `h̃` and `h̄̃` are whole-plane GFFs and `f̃` is measurable;
3. a.s. `(h̃, h̄̃, f̃)` is a coupling for the zoomed map;
4. a.s. for all `u, v`: `D^{ϕ̃}(u, v) = r^{−ξQ} e^{−ξ h_r(z)} D^ϕ(z + r u, z + r v)`;
5. a.s. for all `u, v`: `D_{h̃}(u, v) = r^{−ξQ} e^{−ξ h_r(z)} D_h(z + r u, z + r v)`. -/
theorem lemma26 (hD : IsStrongLQGMetric γ D) {ϕ : ℂ → ℂ} {W V : Set ℂ} (hϕ : IsConfNbhd ϕ W V)
    {h hbar : Ω → DistC} {f : Ω → C(ℂ, ℝ)} (hh : IsWholePlaneGFF h P)
    (hhb : IsWholePlaneGFF hbar P) (hf : Measurable f)
    (hc : ∀ᵐ ω ∂P, IsConfCoupling γ ϕ W V (h ω) (hbar ω) (f ω)) (z : ℂ) {r : ℝ} (hr : 0 < r) :
    IsConfNbhd (zoomMap ϕ z r) (zoomSet z r W) (zoomSet z r V) ∧
    IsWholePlaneGFF (fun ω => addConst (affineComp r z (h ω)) (-circleAvg (h ω) r z)) P ∧
    IsWholePlaneGFF (fun ω => affineComp r (ϕ z) (hbar ω)) P ∧
    Measurable (fun ω => zoomCont (f ω) (ϕ z) r (-circleAvg (h ω) r z)) ∧
    (∀ᵐ ω ∂P, IsConfCoupling γ (zoomMap ϕ z r) (zoomSet z r W) (zoomSet z r V)
      (addConst (affineComp r z (h ω)) (-circleAvg (h ω) r z)) (affineComp r (ϕ z) (hbar ω))
      (zoomCont (f ω) (ϕ z) r (-circleAvg (h ω) r z))) ∧
    (∀ᵐ ω ∂P, ∀ u v : ℂ,
      confMetric D (zoomMap ϕ z r) (zoomSet z r V) (affineComp r (ϕ z) (hbar ω))
          (zoomCont (f ω) (ϕ z) r (-circleAvg (h ω) r z)) u v =
        ENNReal.ofReal (r ^ (-(xiGamma γ * Q γ)) * Real.exp (-(xiGamma γ * circleAvg (h ω) r z))) *
          confMetric D ϕ V (hbar ω) (f ω) (z + (r : ℂ) * u) (z + (r : ℂ) * v)) ∧
    (∀ᵐ ω ∂P, ∀ u v : ℂ,
      (D (addConst (affineComp r z (h ω)) (-circleAvg (h ω) r z))).1 (u, v) =
        r ^ (-(xiGamma γ * Q γ)) * Real.exp (-(xiGamma γ * circleAvg (h ω) r z)) *
          (D (h ω)).1 (z + (r : ℂ) * u, z + (r : ℂ) * v)) := by
  have hcm : Measurable fun ω => -circleAvg (h ω) r z :=
    ((measurable_circleAvg_left r z).comp hh.measurable).neg
  refine ⟨hϕ.zoom z hr.ne', (hh.affineComp hr z).addConst hcm, hhb.affineComp hr (ϕ z),
    measurable_zoomCont hf hcm (ϕ z) r, ?_, ?_, ?_⟩
  · filter_upwards [hc] with ω hω
    exact IsConfCoupling.zoom hϕ hω z hr _
  · filter_upwards [ae_confMetric_lemma26 (h := h) hD hhb hf ϕ z hr] with ω hω u v
    exact hω V u v
  · exact ae_dist_lemma26 hD (isGFFPlusCont_of_wp hh) z hr

/-- **Lemma 2.6 in the `𝔰_r(z)` form** used by `ConfSmallScale` (D10): a.s. for all `u, v`,
`D^ϕ(z + r u, z + r v) = 𝔰_r(z) D^{ϕ̃}(u, v)` and `D_h(z + r u, z + r v) = 𝔰_r(z) D_{h̃}(u, v)`,
with
`𝔰_r(z) = r^{ξQ} e^{ξ h_r(z)}`. -/
theorem ae_lemma26_scale (hD : IsStrongLQGMetric γ D) {h hbar : Ω → DistC} {f : Ω → C(ℂ, ℝ)}
    (hh : IsWholePlaneGFF h P) (hhb : IsWholePlaneGFF hbar P) (hf : Measurable f) (ϕ : ℂ → ℂ)
    (z : ℂ) {r : ℝ} (hr : 0 < r) :
    ∀ᵐ ω ∂P, ∀ (V : Set ℂ) (u v : ℂ),
      confMetric D ϕ V (hbar ω) (f ω) (z + (r : ℂ) * u) (z + (r : ℂ) * v) =
          ENNReal.ofReal (r ^ (xiGamma γ * Q γ) * Real.exp (xiGamma γ * circleAvg (h ω) r z)) *
            confMetric D (zoomMap ϕ z r) (zoomSet z r V) (affineComp r (ϕ z) (hbar ω))
              (zoomCont (f ω) (ϕ z) r (-circleAvg (h ω) r z)) u v ∧
        (D (h ω)).1 (z + (r : ℂ) * u, z + (r : ℂ) * v) =
          r ^ (xiGamma γ * Q γ) * Real.exp (xiGamma γ * circleAvg (h ω) r z) *
            (D (addConst (affineComp r z (h ω)) (-circleAvg (h ω) r z))).1 (u, v) := by
  filter_upwards [ae_confMetric_lemma26 (h := h) hD hhb hf ϕ z hr,
    ae_dist_lemma26 hD (isGFFPlusCont_of_wp hh) z hr] with ω h1 h2 V u v
  set s : ℝ := r ^ (xiGamma γ * Q γ) * Real.exp (xiGamma γ * circleAvg (h ω) r z) with hs
  have hs0 : 0 < s := mul_pos (Real.rpow_pos_of_pos hr _) (Real.exp_pos _)
  have hinv : r ^ (-(xiGamma γ * Q γ)) * Real.exp (-(xiGamma γ * circleAvg (h ω) r z)) = s⁻¹ := by
    rw [hs, mul_inv, Real.rpow_neg hr.le, Real.exp_neg]
  rw [hinv] at h1 h2
  constructor
  · rw [h1 V u v, ← mul_assoc, ← ENNReal.ofReal_mul hs0.le, mul_inv_cancel₀ hs0.ne',
      ENNReal.ofReal_one, one_mul]
  · rw [h2 u v, ← mul_assoc, mul_inv_cancel₀ hs0.ne', one_mul]

end Lemma26

end SmallGammaGeodesics.CC
