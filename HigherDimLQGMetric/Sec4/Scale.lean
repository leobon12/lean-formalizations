import HigherDimLQGMetric.Sec4.Lemma41Uniform
import HigherDimLQGMetric.ConvField.Scaling
import HigherDimLQGMetric.Sphere.Scaling
import HigherDimLQGMetric.Core.Defs

/-!
# Scaling of the convolution LFPP (packet L9b; [1] (3.6)/(3.13) as used in Lemma 4.3)

For a normalized LGF `h`, a centre `u` and a scale `r > 0`, with the recentred rescaled field
`h' = h(u + r ·) - (h(u + r ·))_1(0)` (`recentAff r u h`, again a normalized LGF):

* `h*_ε(u + r x) = (h')*_{ε/r}(x) + h_r(u)` for all `ε > 0`, `x`, almost surely (`l9b_ae_convMollify_affine`);
* deterministically, internal LFPP distances, set distances and internal diameters transform by the factor
  `r e^{ξ c}` under `x ↦ u + r x` when the field shifts by the constant `c` (`l9b_lfppDistOn_affine`,
  `l9b_lfppSetDist_affine`, `l9b_lfppDiam_affine`), and spheres/annuli/space map to spheres/annuli/space.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology Metric
open scoped ENNReal

namespace HigherDimLQGMetric

open HigherDimLFPP (Rd e₁ lfppDistOn)

variable {d : ℕ}

/-! ## Affine images of sets -/

theorem l9b_image_affine_univ {r : ℝ} (hr : 0 < r) (u : Rd d) :
    (fun x : Rd d => u + r • x) '' univ = univ := by
  refine eq_univ_of_forall fun y => ⟨r⁻¹ • (y - u), mem_univ _, ?_⟩
  simp only [smul_smul, mul_inv_cancel₀ hr.ne', one_smul, add_sub_cancel]

theorem l9b_norm_affine_sub {r : ℝ} (hr : 0 < r) (u x : Rd d) : ‖u + r • x - u‖ = r * ‖x‖ := by
  rw [add_sub_cancel_left, norm_smul, Real.norm_eq_abs, abs_of_pos hr]

theorem l9b_image_affine_sphere {r : ℝ} (hr : 0 < r) (u : Rd d) (a : ℝ) :
    (fun x : Rd d => u + r • x) '' sphere 0 a = sphere u (r * a) := by
  ext y
  simp only [mem_image, mem_sphere, dist_eq_norm, sub_zero]
  constructor
  · rintro ⟨x, hx, rfl⟩
    rw [l9b_norm_affine_sub hr, hx]
  · intro hy
    refine ⟨r⁻¹ • (y - u), ?_, ?_⟩
    · rw [norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos hr, hy]
      field_simp
    · simp only [smul_smul, mul_inv_cancel₀ hr.ne', one_smul, add_sub_cancel]

theorem l9b_image_affine_ann {r : ℝ} (hr : 0 < r) (u : Rd d) (a b : ℝ) :
    (fun x : Rd d => u + r • x) '' ann 0 a b = ann u (r * a) (r * b) := by
  ext y
  simp only [mem_image, ann, mem_ofPred_eq, sub_zero]
  constructor
  · rintro ⟨x, ⟨hxa, hxb⟩, rfl⟩
    rw [l9b_norm_affine_sub hr]
    exact ⟨mul_lt_mul_of_pos_left hxa hr, mul_lt_mul_of_pos_left hxb hr⟩
  · rintro ⟨hya, hyb⟩
    have hn : ‖r⁻¹ • (y - u)‖ = r⁻¹ * ‖y - u‖ := by
      rw [norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos hr]
    refine ⟨r⁻¹ • (y - u), ⟨?_, ?_⟩, ?_⟩
    · rw [hn, lt_inv_mul_iff₀ hr]; exact hya
    · rw [hn, inv_mul_lt_iff₀ hr]; exact hyb
    · simp only [smul_smul, mul_inv_cancel₀ hr.ne', one_smul, add_sub_cancel]

/-! ## Deterministic scaling of LFPP functionals -/

section Det

variable {ξ : ℝ} {φ ψ : Rd d → ℝ} {r c : ℝ} {u : Rd d}

theorem l9b_lfppDistOn_affine (hr : 0 < r) (hφψ : ∀ x, φ (u + r • x) = ψ x + c)
    (V : Set (Rd d)) (x y : Rd d) :
    lfppDistOn ξ φ ((fun z => u + r • z) '' V) (u + r • x) (u + r • y) =
      r * Real.exp (ξ * c) * lfppDistOn ξ ψ V x y := by
  have h := HigherDimLFPP.lfppDistOn_sim_image (LinearIsometryEquiv.refl ℝ (Rd d)) u hr ξ φ V x y
  simp only [LinearIsometryEquiv.coe_refl, id] at h
  rw [h, show (fun z => φ (u + r • z)) = fun z => ψ z + c from funext hφψ,
    HigherDimLFPP.lfppDistOn_add_const]
  ring

theorem l9b_lfppSetDist_affine (hr : 0 < r) (hφψ : ∀ x, φ (u + r • x) = ψ x + c)
    (V A B : Set (Rd d)) :
    DGZ.lfppSetDist ξ φ ((fun z => u + r • z) '' V) ((fun z => u + r • z) '' A)
        ((fun z => u + r • z) '' B) = r * Real.exp (ξ * c) * DGZ.lfppSetDist ξ ψ V A B := by
  have hk : 0 ≤ r * Real.exp (ξ * c) := by positivity
  unfold DGZ.lfppSetDist
  rw [prod_image_image_eq, image_image, ← smul_eq_mul, ← Real.sInf_smul_of_nonneg hk,
    ← image_smul, image_image]
  congr 1
  refine image_congr fun p _ => ?_
  simp only [smul_eq_mul]
  exact l9b_lfppDistOn_affine hr hφψ V p.1 p.2

theorem l9b_lfppDiam_affine (hr : 0 < r) (hφψ : ∀ x, φ (u + r • x) = ψ x + c)
    (U V : Set (Rd d)) :
    DGZ.lfppDiam ξ φ ((fun z => u + r • z) '' U) ((fun z => u + r • z) '' V) =
      r * Real.exp (ξ * c) * DGZ.lfppDiam ξ ψ U V := by
  have hk : 0 ≤ r * Real.exp (ξ * c) := by positivity
  unfold DGZ.lfppDiam
  rw [prod_image_image_eq, image_image, ← smul_eq_mul, ← Real.sSup_smul_of_nonneg hk,
    ← image_smul, image_image]
  congr 1
  refine image_congr fun p _ => ?_
  simp only [smul_eq_mul]
  exact l9b_lfppDistOn_affine hr hφψ V p.1 p.2

end Det

/-! ## Scaling of the convolution field -/

/-- **The convolution field under `x ↦ u + r x`** (a.s.): `h*_ε(u + r x) = (h')*_{ε/r}(x) + c` with
`h' = recentAff r u h` and `c = (h(u + r·))_1(0)`, simultaneously for all `ε > 0` and `x`; and `c = h_r(u)`. -/
theorem l9b_ae_convMollify_affine (hd : 2 ≤ d) {κ : Rd d → ℝ} (hκ : HigherDimLFPP.IsLFPPKernel κ)
    {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P] {h : Ω → DistRd d}
    (hh : IsNormalizedLGF h P) (u : Rd d) {r : ℝ} (hr : 0 < r) :
    ∀ᵐ ω ∂P, (∀ ε : ℝ, 0 < ε → ∀ x : Rd d,
      convMollify κ ε (h ω) (u + r • x) =
        convMollify κ (ε / r) (recentAff r u (h ω)) x + sphereAvg (affineComp r u (h ω)) 1 0) ∧
      sphereAvg (affineComp r u (h ω)) 1 0 = sphereAvg (h ω) r u := by
  have hu := hh.1.affineComp one_pos u
  have hN := isNormalizedLGF_recentAff hd hh.1 hr u
  filter_upwards [l2b_ae_convMollify_scale d hd κ hκ P _ hu hr,
    l2b_ae_convMollify_addConst d hd κ hκ P _ hN,
    hh.1.ae_sphereAvg_affineComp hd hr u one_pos 0] with ω hsc hadd hsph
  refine ⟨fun ε hε x => ?_, ?_⟩
  · have e1 : affineComp r 0 (affineComp 1 u (h ω)) = affineComp r u (h ω) := by
      rw [affineComp_affineComp, one_mul, smul_zero, zero_add]
    calc convMollify κ ε (h ω) (u + r • x)
        = convMollify κ ε (affineComp 1 u (h ω)) (r • x) := by
          rw [l2b_convMollify_translate d hd κ hκ ε (h ω) u (r • x), add_comm]
      _ = convMollify κ (ε / r) (affineComp r u (h ω)) x := by rw [← e1, hsc ε hε x]
      _ = convMollify κ (ε / r) (addConst (recentAff r u (h ω))
            (sphereAvg (affineComp r u (h ω)) 1 0)) x := by rw [addConst_recentAff]
      _ = _ := hadd (ε / r) (div_pos hε hr) x _
  · rw [hsph, mul_one, smul_zero, zero_add]

end HigherDimLQGMetric
