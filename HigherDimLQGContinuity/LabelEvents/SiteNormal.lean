import HigherDimLQGContinuity.LabelEvents.SourceBorel
import HigherDimLQGContinuity.Norm.Scaling
import HigherDimLQGContinuity.Events.Profile
import HigherDimLQGMetric.Metric.WeylAxioms

/-!
# Site normalization and local modifications (packet Q5; Part B `b:lem-site-normal`)

Source: blueprint Part B `b:lem-site-normal` (statement and proof); [C] p. 15, l. 782–787; p. 18–19, l. 929–931,
976–985; planning audit NA2, items 14, 22, R13; ruling N21 (`scaleS` uses `phiXi`; the scaling identities need
`ξ > 0`). Inputs: Part A's exact scaling `rho_scaling_of` (packet P2), the Weyl property (III) in the internal form
`IsStrongExpMetric.ae_internal_eq_weylScaleOn` (HDLM `Metric/WeylAxioms.lean`), the coordinate changes
`weylScaleOn_affine`, `weylScaleOn_smul` (HDLM `Metric/WeylBasic.lean`), `sphereAvg_addFun_of_tendsto`
(HDLM `Field/SphereAvgBasic.lean`), and the pattern of `lemma82_internal` (HDLM `Sec8/Perturb.lean`).

For a field `g` and a site `(z, s)`, `s > 0`, the **site-normalized metric** of an assignment `G` in the primary unit
of parameter `ξ` is `siteNorm ξ G z hs g (x, y) = ρ^G_g(z + s x, z + s y) / S^D`, with the primary site unit
`S^D = scaleS d ξ 1 s z g = s^{ϕ(ξ)} e^{ξ g_s(z)}` (Part A `a:def-pin`). Part B's `D̂^{z,s}_g` is
`siteNorm ξ D z hs g` and `Ê^{z,s}_g` is `siteNorm ξ E z hs g` (both in primary site units).

* (a) `siteNormal_scaling`: under every pin `s₀ > 0`, almost surely `D̂ = ρ^D_{g'}` and `Ê = (S^E/S^D) ρ^E_{g'}` with
  `g' = recentre 1 s z g`, and both are continuous length metrics.
* (b) `siteNormal_weyl` (with the deterministic `scaleS_addFun_of_eq_zero`, `siteNorm_weyl_of`): almost surely,
  simultaneously for all continuous `f` vanishing on `∂B_s(z)`: `S^D(g - f) = S^D(g)` and
  `IsWeylInternal ξ (-f̂) D̂_g D̂_{g-f}`, `IsWeylInternal η (-f̂) Ê_g Ê_{g-f}`, `f̂ = f ∘ (x ↦ s x + z)`.
* (c) `siteNormal_local`: almost surely, for all such `f, f'` with `f = f'` on `B_{4s}(z)`, the site-normalized metrics
  of `g - f` and `g - f'` have the same internal metric on every open `W ⊆ B = B₄`.

Measurability: `measurable_siteNorm`. The blueprint's "simultaneously for all sites of a fixed countable set":
`siteNormal_scaling_countable`, `siteNormal_weyl_countable`, `siteNormal_local_countable` (`ae_all_iff`).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set Metric Filter Topology
open scoped ENNReal
open HigherDimLFPP (Rd)

namespace HigherDimLQGContinuity

open HigherDimLQGMetric

variable {d : ℕ}

/-! ## The site-normalized metric -/

/-- The site-normalized metric of an assignment `G` at the site `(z, s)` in the primary site unit of parameter `ξ`:
`(x, y) ↦ ρ^G_g(s x + z, s y + z) / scaleS d ξ 1 s z g` (Part B `b:lem-site-normal`; `D̂ = siteNorm ξ D`,
`Ê = siteNorm ξ E`). -/
def siteNorm (ξ : ℝ) (G : DistRd d → ContMetric d) (z : Rd d) {s : ℝ} (hs : 0 < s) (g : DistRd d) :
    ContMetric d :=
  ((rho G g).affine s hs.ne' z).smul (scaleS d ξ 1 s z g)⁻¹ (inv_pos.2 (scaleS_pos d ξ 1 hs z g))

theorem siteNorm_apply (ξ : ℝ) (G : DistRd d → ContMetric d) (z : Rd d) {s : ℝ} (hs : 0 < s) (g : DistRd d)
    (p : Rd d × Rd d) :
    (siteNorm ξ G z hs g).1 p = (scaleS d ξ 1 s z g)⁻¹ * (rho G g).1 (s • p.1 + z, s • p.2 + z) :=
  rfl

/-- The internal metrics of the site-normalized metric. -/
theorem siteNorm_internal (ξ : ℝ) (G : DistRd d → ContMetric d) (z : Rd d) {s : ℝ} (hs : 0 < s)
    (g : DistRd d) (U : Set (Rd d)) (x y : Rd d) :
    (siteNorm ξ G z hs g).internal U x y =
      ENNReal.ofReal (scaleS d ξ 1 s z g)⁻¹ *
        (rho G g).internal ((fun u => s • u + z) '' U) (s • x + z) (s • y + z) := by
  rw [siteNorm, ContMetric.internal_smul, ContMetric.internal_affine]

/-- The site-normalized metric of a length metric is a length metric. -/
theorem isLength_siteNorm {ξ : ℝ} {G : DistRd d → ContMetric d} {z : Rd d} {s : ℝ} (hs : 0 < s)
    {g : DistRd d} (h : (rho G g).IsLength) : (siteNorm ξ G z hs g).IsLength :=
  ContMetric.isLength_smul _ (ContMetric.isLength_affine _ _ h)

/-- The site-normalized metric is a measurable function of the field. -/
theorem measurable_siteNorm {G : DistRd d → ContMetric d} (hG : Measurable G) (ξ : ℝ) (z : Rd d) {s : ℝ}
    (hs : 0 < s) : Measurable (siteNorm ξ G z hs) := by
  have hS : Measurable fun g : DistRd d => (scaleS d ξ 1 s z g)⁻¹ := by
    unfold scaleS
    exact (measurable_const.mul (Real.measurable_exp.comp
      (measurable_const.mul (measurable_sphereAvg_left _ _)))).inv
  let Af : C(Rd d × Rd d, Rd d × Rd d) := ⟨fun p => (s • p.1 + z, s • p.2 + z), by fun_prop⟩
  have hρ : Measurable fun g => (rho G g).1.comp Af :=
    (ContinuousMap.continuous_precomp Af).measurable.comp (measurable_subtype_coe.comp (measurable_rho hG))
  have h : Measurable fun g => (scaleS d ξ 1 s z g)⁻¹ • (rho G g).1.comp Af :=
    continuous_smul.measurable.comp (hS.prodMk hρ)
  exact h.subtype_mk

/-- Under every pin `s₀ > 0`, the site-normalized metric is almost surely a length metric. -/
theorem ae_isLength_siteNorm (hd : 2 ≤ d) {ζ Q : ℝ} {G : DistRd d → ContMetric d}
    (hG : IsStrongExpMetric d ζ Q G) {s₀ : ℝ} (hs₀ : 0 < s₀) (ξ : ℝ) (z : Rd d) {s : ℝ} (hs : 0 < s) :
    ∀ᵐ g ∂(pinLaw d s₀), (siteNorm ξ G z hs g).IsLength := by
  filter_upwards [p5b_ae_isLength_rho hd hG hs₀] with g hg
  exact isLength_siteNorm hs hg

/-! ## (a) Scaling -/

/-- **Site normalization** (`b:lem-site-normal`(a)): under every pin `s₀ > 0`, almost surely
`D̂^{z,s}_g = ρ^D_{g'}` and `Ê^{z,s}_g = (S^E/S^D) ρ^E_{g'}` with `g' = recentre 1 s z g`; both are length metrics. -/
theorem siteNormal_scaling (hd : 2 ≤ d) {ξ η : ℝ} (hξ : 0 < ξ) (hη : 0 < η) {D E : DistRd d → ContMetric d}
    (hD : IsStrongExpMetric d ξ (distExp d ξ) D) (hE : IsStrongExpMetric d η (distExp d η) E) {s₀ : ℝ}
    (hs₀ : 0 < s₀) (z : Rd d) {s : ℝ} (hs : 0 < s) :
    ∀ᵐ g ∂(pinLaw d s₀),
      siteNorm ξ D z hs g = rho D (recentre 1 s z g) ∧
      siteNorm ξ E z hs g = (rho E (recentre 1 s z g)).smul (scaleS d η 1 s z g / scaleS d ξ 1 s z g)
        (div_pos (scaleS_pos d η 1 hs z g) (scaleS_pos d ξ 1 hs z g)) ∧
      (siteNorm ξ D z hs g).IsLength ∧ (siteNorm ξ E z hs g).IsLength := by
  filter_upwards [rho_scaling_of hd hξ hD (s := 1) hs₀ hs z, rho_scaling_of hd hη hE (s := 1) hs₀ hs z,
    ae_isLength_siteNorm hd hD hs₀ ξ z hs, ae_isLength_siteNorm hd hE hs₀ ξ z hs] with g h1 h2 h3 h4
  have hSD := scaleS_pos d ξ 1 hs z g
  refine ⟨Subtype.ext (ContinuousMap.ext fun p => ?_), Subtype.ext (ContinuousMap.ext fun p => ?_), h3, h4⟩
  · change (scaleS d ξ 1 s z g)⁻¹ * (rho D g).1 (s • p.1 + z, s • p.2 + z) = (rho D (recentre 1 s z g)).1 p
    rw [h1.1 p.1 p.2, ← mul_assoc, inv_mul_cancel₀ hSD.ne', one_mul]
  · change (scaleS d ξ 1 s z g)⁻¹ * (rho E g).1 (s • p.1 + z, s • p.2 + z) =
      scaleS d η 1 s z g / scaleS d ξ 1 s z g * (rho E (recentre 1 s z g)).1 p
    rw [h2.1 p.1 p.2, ← mul_assoc, div_eq_inv_mul]

/-! ## (b) Local modifications: the deterministic identities -/

/-- The site unit is unchanged by a continuous function vanishing on the site sphere `∂B_s(z)` (wherever the
defining limit of the sphere average exists). -/
theorem scaleS_addFun_of_eq_zero {g : DistRd d} {s : ℝ} {z : Rd d} {a : ℝ}
    (ha : Tendsto (sphereAvgSeq g (1 * s) z) atTop (𝓝 a)) (hs : 0 < s) {f : C(Rd d, ℝ)}
    (hf : ∀ x ∈ sphere z s, f x = 0) (ξ : ℝ) :
    scaleS d ξ 1 s z (addFun g f) = scaleS d ξ 1 s z g := by
  unfold scaleS
  rw [sphereAvg_addFun_of_tendsto ha f]
  have hzero : ∀ᵐ u ∂(unitSphereProb d), f (z + (1 * s) • u) = 0 := by
    filter_upwards [ae_unitSphereProb_norm_eq_one d] with u hu
    apply hf
    rw [mem_sphere, dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_eq_abs, one_mul, abs_of_pos hs, hu,
      mul_one]
  rw [integral_eq_zero_of_ae hzero, add_zero]

/-- **Weyl modification of the site-normalized metric**, deterministic form: if `g` satisfies the Weyl property (III) in
internal form for the assignment `G` (parameter `ζ`) and the sphere average of `g` at `(z, s)` is a limit, then for
every continuous `f` vanishing on `∂B_s(z)`, the site-normalized metric of `g - f` is the Weyl modification of that
of `g` by `-f̂`, `f̂ = f(s · + z)` (the primary unit of parameter `ξ` is unchanged). -/
theorem siteNorm_weyl_of {ξ ζ : ℝ} {G : DistRd d → ContMetric d} {z : Rd d} {s : ℝ} (hs : 0 < s)
    {g : DistRd d}
    (hw : ∀ (F : C(Rd d, ℝ)) (U : Set (Rd d)), IsOpen U → ∀ x y : Rd d,
      (G (addFun g F)).internal U x y = weylScaleOn ζ F (G g) U x y)
    {a : ℝ} (ha : Tendsto (sphereAvgSeq g (1 * s) z) atTop (𝓝 a)) {f : C(Rd d, ℝ)}
    (hf : ∀ x ∈ sphere z s, f x = 0) :
    IsWeylInternal ζ (-(f.comp (ContMetric.affineMap s z))) (siteNorm ξ G z hs g)
      (siteNorm ξ G z hs (addFun g (-f))) := by
  intro U hU x y
  set V : Set (Rd d) := (fun u => s • u + z) '' U with hVdef
  have hVo : IsOpen V := q5_isOpen_affine_image hs.ne' z hU
  have hS : scaleS d ξ 1 s z (addFun g (-f)) = scaleS d ξ 1 s z g :=
    scaleS_addFun_of_eq_zero ha hs (f := -f) (fun x hx => by simp [hf x hx]) ξ
  have hpre : ⇑(ContMetric.affineMap s z) ⁻¹' V = U := preimage_image_eq U (q5_affine_injective hs.ne' z)
  have hcomp : -(f.comp (ContMetric.affineMap s z)) = (-f).comp (ContMetric.affineMap s z) := by
    ext u
    simp
  calc (siteNorm ξ G z hs (addFun g (-f))).internal U x y
      = ENNReal.ofReal (scaleS d ξ 1 s z g)⁻¹ * (rho G (addFun g (-f))).internal V (s • x + z) (s • y + z) := by
        rw [siteNorm_internal, hS]
    _ = ENNReal.ofReal (scaleS d ξ 1 s z g)⁻¹ *
          (ENNReal.ofReal (Real.exp (-logMean G)) * weylScaleOn ζ (-f) (G g) V (s • x + z) (s • y + z)) := by
        rw [p5b_internal_rho, hw (-f) V hVo]
    _ = ENNReal.ofReal (scaleS d ξ 1 s z g)⁻¹ * weylScaleOn ζ (-f) (rho G g) V (s • x + z) (s • y + z) := by
        rw [rho, weylScaleOn_smul]
    _ = ENNReal.ofReal (scaleS d ξ 1 s z g)⁻¹ *
          weylScaleOn ζ ((-f).comp (ContMetric.affineMap s z)) ((rho G g).affine s hs.ne' z)
            (⇑(ContMetric.affineMap s z) ⁻¹' V) x y := by
        rw [weylScaleOn_affine]
        rfl
    _ = ENNReal.ofReal (scaleS d ξ 1 s z g)⁻¹ *
          weylScaleOn ζ (-(f.comp (ContMetric.affineMap s z))) ((rho G g).affine s hs.ne' z) U x y := by
        rw [hpre, hcomp]
    _ = weylScaleOn ζ (-(f.comp (ContMetric.affineMap s z))) (siteNorm ξ G z hs g) U x y := by
        rw [siteNorm, weylScaleOn_smul]

/-- **Locality of the modified site-normalized metric**, deterministic form: under the hypotheses of
`siteNorm_weyl_of`, if `f = f'` on `B_{4s}(z)`, then the site-normalized metrics of `g - f` and `g - f'` have the same
internal metric on every open `W ⊆ B₄`. -/
theorem siteNorm_local_of {ξ ζ : ℝ} {G : DistRd d → ContMetric d} {z : Rd d} {s : ℝ} (hs : 0 < s)
    {g : DistRd d}
    (hw : ∀ (F : C(Rd d, ℝ)) (U : Set (Rd d)), IsOpen U → ∀ x y : Rd d,
      (G (addFun g F)).internal U x y = weylScaleOn ζ F (G g) U x y)
    {a : ℝ} (ha : Tendsto (sphereAvgSeq g (1 * s) z) atTop (𝓝 a)) {f f' : C(Rd d, ℝ)}
    (hf : ∀ x ∈ sphere z s, f x = 0) (hff' : ∀ x ∈ ball z (4 * s), f x = f' x)
    {W : Set (Rd d)} (hW : IsOpen W) (hWB : W ⊆ siteB d) (x y : Rd d) :
    (siteNorm ξ G z hs (addFun g (-f))).internal W x y =
      (siteNorm ξ G z hs (addFun g (-f'))).internal W x y := by
  have hsph : sphere z s ⊆ ball z (4 * s) := by
    intro u hu
    rw [mem_sphere] at hu
    rw [mem_ball, hu]
    linarith
  have hf' : ∀ u ∈ sphere z s, f' u = 0 := fun u hu => by rw [← hff' u (hsph hu)]; exact hf u hu
  rw [siteNorm_weyl_of hs hw ha hf W hW, siteNorm_weyl_of hs hw ha hf' W hW]
  refine weylScaleOn_congr fun u hu => ?_
  have hu' : s • u + z ∈ ball z (4 * s) := by
    have := hWB hu
    rw [siteB, mem_ball, dist_zero_right] at this
    rw [mem_ball, dist_eq_norm, add_sub_cancel_right, norm_smul, Real.norm_eq_abs, abs_of_pos hs]
    nlinarith
  simp only [ContinuousMap.neg_apply, ContinuousMap.comp_apply, ContMetric.affineMap_apply, hff' _ hu']

/-! ## (b), (c): the almost-sure statements -/

/-- **Site modifications** (`b:lem-site-normal`(b)): under every pin `s₀ > 0`, almost surely, simultaneously for all
continuous `f` vanishing on `∂B_s(z)`: the primary site unit is unchanged, and the site-normalized metrics of
`g - f` are the Weyl modifications by `-f̂` of those of `g` (parameter `ξ` for `D̂`, `η` for `Ê`). -/
theorem siteNormal_weyl (hd : 2 ≤ d) {ξ η Q Q' : ℝ} {D E : DistRd d → ContMetric d}
    (hD : IsStrongExpMetric d ξ Q D) (hE : IsStrongExpMetric d η Q' E) {s₀ : ℝ} (hs₀ : 0 < s₀) (z : Rd d)
    {s : ℝ} (hs : 0 < s) :
    ∀ᵐ g ∂(pinLaw d s₀), ∀ f : C(Rd d, ℝ), (∀ x ∈ sphere z s, f x = 0) →
      scaleS d ξ 1 s z (addFun g (-f)) = scaleS d ξ 1 s z g ∧
      IsWeylInternal ξ (-(f.comp (ContMetric.affineMap s z))) (siteNorm ξ D z hs g)
        (siteNorm ξ D z hs (addFun g (-f))) ∧
      IsWeylInternal η (-(f.comp (ContMetric.affineMap s z))) (siteNorm ξ E z hs g)
        (siteNorm ξ E z hs (addFun g (-f))) := by
  have := isProbabilityMeasure_pinLaw hd s₀
  have hlgf := (isWholeSpaceLGF_pinLaw hd hs₀).1
  filter_upwards [hD.ae_internal_eq_weylScaleOn (h := id) hlgf.isLGFPlusCont,
    hE.ae_internal_eq_weylScaleOn (h := id) hlgf.isLGFPlusCont,
    hlgf.ae_exists_tendsto_sphereAvgSeq hd (r := 1 * s) (by positivity) z] with g hwD hwE hlim
  obtain ⟨a, ha⟩ := hlim
  intro f hf
  exact ⟨scaleS_addFun_of_eq_zero ha hs (f := -f) (fun x hx => by simp [hf x hx]) ξ,
    siteNorm_weyl_of hs hwD ha hf, siteNorm_weyl_of hs hwE ha hf⟩

/-- **Locality of site modifications** (`b:lem-site-normal`(c)): under every pin `s₀ > 0`, almost surely, for all
continuous `f, f'` with `f = 0` on `∂B_s(z)` and `f = f'` on `B_{4s}(z)`, the site-normalized metrics (`D̂` and `Ê`) of
`g - f` and `g - f'` have the same internal metric on every open `W ⊆ B₄`. -/
theorem siteNormal_local (hd : 2 ≤ d) {ξ η Q Q' : ℝ} {D E : DistRd d → ContMetric d}
    (hD : IsStrongExpMetric d ξ Q D) (hE : IsStrongExpMetric d η Q' E) {s₀ : ℝ} (hs₀ : 0 < s₀) (z : Rd d)
    {s : ℝ} (hs : 0 < s) :
    ∀ᵐ g ∂(pinLaw d s₀), ∀ f f' : C(Rd d, ℝ), (∀ x ∈ sphere z s, f x = 0) →
      (∀ x ∈ ball z (4 * s), f x = f' x) → ∀ W : Set (Rd d), IsOpen W → W ⊆ siteB d → ∀ x y : Rd d,
        (siteNorm ξ D z hs (addFun g (-f))).internal W x y =
            (siteNorm ξ D z hs (addFun g (-f'))).internal W x y ∧
          (siteNorm ξ E z hs (addFun g (-f))).internal W x y =
            (siteNorm ξ E z hs (addFun g (-f'))).internal W x y := by
  have := isProbabilityMeasure_pinLaw hd s₀
  have hlgf := (isWholeSpaceLGF_pinLaw hd hs₀).1
  filter_upwards [hD.ae_internal_eq_weylScaleOn (h := id) hlgf.isLGFPlusCont,
    hE.ae_internal_eq_weylScaleOn (h := id) hlgf.isLGFPlusCont,
    hlgf.ae_exists_tendsto_sphereAvgSeq hd (r := 1 * s) (by positivity) z] with g hwD hwE hlim
  obtain ⟨a, ha⟩ := hlim
  intro f f' hf hff' W hW hWB x y
  exact ⟨siteNorm_local_of hs hwD ha hf hff' hW hWB x y, siteNorm_local_of hs hwE ha hf hff' hW hWB x y⟩

/-! ## Countably many sites -/

/-- `b:lem-site-normal`(b) simultaneously for a countable family of sites. -/
theorem siteNormal_weyl_countable (hd : 2 ≤ d) {ξ η Q Q' : ℝ} {D E : DistRd d → ContMetric d}
    (hD : IsStrongExpMetric d ξ Q D) (hE : IsStrongExpMetric d η Q' E) {s₀ : ℝ} (hs₀ : 0 < s₀)
    {ι : Type*} [Countable ι] (z : ι → Rd d) {s : ι → ℝ} (hs : ∀ i, 0 < s i) :
    ∀ᵐ g ∂(pinLaw d s₀), ∀ i, ∀ f : C(Rd d, ℝ), (∀ x ∈ sphere (z i) (s i), f x = 0) →
      scaleS d ξ 1 (s i) (z i) (addFun g (-f)) = scaleS d ξ 1 (s i) (z i) g ∧
      IsWeylInternal ξ (-(f.comp (ContMetric.affineMap (s i) (z i)))) (siteNorm ξ D (z i) (hs i) g)
        (siteNorm ξ D (z i) (hs i) (addFun g (-f))) ∧
      IsWeylInternal η (-(f.comp (ContMetric.affineMap (s i) (z i)))) (siteNorm ξ E (z i) (hs i) g)
        (siteNorm ξ E (z i) (hs i) (addFun g (-f))) :=
  ae_all_iff.2 fun i => siteNormal_weyl hd hD hE hs₀ (z i) (hs i)

/-- `b:lem-site-normal`(c) simultaneously for a countable family of sites. -/
theorem siteNormal_local_countable (hd : 2 ≤ d) {ξ η Q Q' : ℝ} {D E : DistRd d → ContMetric d}
    (hD : IsStrongExpMetric d ξ Q D) (hE : IsStrongExpMetric d η Q' E) {s₀ : ℝ} (hs₀ : 0 < s₀)
    {ι : Type*} [Countable ι] (z : ι → Rd d) {s : ι → ℝ} (hs : ∀ i, 0 < s i) :
    ∀ᵐ g ∂(pinLaw d s₀), ∀ i, ∀ f f' : C(Rd d, ℝ), (∀ x ∈ sphere (z i) (s i), f x = 0) →
      (∀ x ∈ ball (z i) (4 * s i), f x = f' x) → ∀ W : Set (Rd d), IsOpen W → W ⊆ siteB d →
        ∀ x y : Rd d,
          (siteNorm ξ D (z i) (hs i) (addFun g (-f))).internal W x y =
              (siteNorm ξ D (z i) (hs i) (addFun g (-f'))).internal W x y ∧
            (siteNorm ξ E (z i) (hs i) (addFun g (-f))).internal W x y =
              (siteNorm ξ E (z i) (hs i) (addFun g (-f'))).internal W x y :=
  ae_all_iff.2 fun i => siteNormal_local hd hD hE hs₀ (z i) (hs i)

/-- `b:lem-site-normal`(a) simultaneously for a countable family of sites. -/
theorem siteNormal_scaling_countable (hd : 2 ≤ d) {ξ η : ℝ} (hξ : 0 < ξ) (hη : 0 < η)
    {D E : DistRd d → ContMetric d} (hD : IsStrongExpMetric d ξ (distExp d ξ) D)
    (hE : IsStrongExpMetric d η (distExp d η) E) {s₀ : ℝ} (hs₀ : 0 < s₀)
    {ι : Type*} [Countable ι] (z : ι → Rd d) {s : ι → ℝ} (hs : ∀ i, 0 < s i) :
    ∀ᵐ g ∂(pinLaw d s₀), ∀ i,
      siteNorm ξ D (z i) (hs i) g = rho D (recentre 1 (s i) (z i) g) ∧
      siteNorm ξ E (z i) (hs i) g = (rho E (recentre 1 (s i) (z i) g)).smul
        (scaleS d η 1 (s i) (z i) g / scaleS d ξ 1 (s i) (z i) g)
        (div_pos (scaleS_pos d η 1 (hs i) (z i) g) (scaleS_pos d ξ 1 (hs i) (z i) g)) ∧
      (siteNorm ξ D (z i) (hs i) g).IsLength ∧ (siteNorm ξ E (z i) (hs i) g).IsLength :=
  ae_all_iff.2 fun i => siteNormal_scaling hd hξ hη hD hE hs₀ (z i) (hs i)

end HigherDimLQGContinuity
