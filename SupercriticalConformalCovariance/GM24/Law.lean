import SupercriticalConformalCovariance.GM24.AsConv
import SupercriticalConformalCovariance.GM24.TVReduce
import GaussianLQG.Metric.Rotation
import LQGMetric.Field.GFFLaw

/-!
# The limit law in GM (2.6) and the modulo-constant data processing

* `dilDist_eq_rotDist_affineComp`: `h(α ·) = rot_{α/|α|} (h(|α| ·))`;
* `isWholePlaneGFF_dilDist`: `h(α ·)` is a whole-plane GFF (modulo constants) when `h` is;
* `map_nrm_restrict_eq`: for `h` normalized by `(h, 𝐟) = 0` (radial `𝐟`, `∫ 𝐟 = 1`), the law of
  `(h − (h, f_r))|_B` with `r = |α|⁻¹` is the law of `h(α ·)|_B` (GM l. 549–553, repaired scale);
* `tvDist_eq_map_of_comap`: TV is unchanged by a map inducing the σ-algebra;
* `tvDist_nrm_le`: TV of normalized laws on `B` is at most TV of the modulo-constant laws (pairings
  with mean-zero tests supported in `B`), the carrier of IG4 Prop 2.10(i).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Filter Topology Set TopologicalSpace
open scoped ENNReal

namespace SupercriticalConformalCovariance.GM24

open LQGMetric QuantumZipper
open SmallGammaGeodesics.CC (intDist intDist_apply linPull confPullFun_mul_left integral_confPullFun
  testOnOfSupp restrictTo_testOnOfSupp)

/-! ## `h(α ·)` is a whole-plane GFF -/

theorem dilDist_eq_rotDist_affineComp {α : ℂ} (hα : α ≠ 0) (h : DistC) :
    dilDist hα h = GaussianLQG.rotDist (((‖α‖ : ℝ) : ℂ)⁻¹ * α) (affineComp ‖α‖ 0 h) := by
  have hn : (0 : ℝ) < ‖α‖ := norm_pos_iff.2 hα
  have hαc : ((‖α‖ : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hn.ne'
  have hu : ((‖α‖ : ℝ) : ℂ)⁻¹ * α ≠ 0 := mul_ne_zero (inv_ne_zero hαc) hα
  ext φ
  rw [dilDist_apply, GaussianLQG.rotDist_apply, GFFInv.affineComp_apply, ← smul_eq_mul,
    ← map_smul]
  congr 1
  ext x
  have hr0 : (‖α‖ : ℝ) ≠ 0 := hn.ne'
  simp only [FunLike.coe_smul, Pi.smul_apply, smul_eq_mul, coe_linPullCLM, linPull,
    testAffinePull_apply _ _ hr0, GaussianLQG.testRot_apply hu]
  have harg : ((((‖α‖ : ℝ) : ℂ))⁻¹ * α)⁻¹ * ((x - 0) / ((‖α‖ : ℝ) : ℂ)) = α⁻¹ * x := by
    rw [sub_zero]; field_simp
  rw [harg, norm_inv, inv_pow]

theorem norm_unit_of_ne {α : ℂ} (hα : α ≠ 0) : ‖((‖α‖ : ℝ) : ℂ)⁻¹ * α‖ = 1 := by
  have hn : (0 : ℝ) < ‖α‖ := norm_pos_iff.2 hα
  rw [norm_mul, norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hn, inv_mul_cancel₀ hn.ne']

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}

/-- **`h(α ·)` is a whole-plane GFF** (scale invariance `IsWholePlaneGFF.affineComp` and rotation
invariance `GaussianLQG.isWholePlaneGFF_rotDist`). -/
theorem isWholePlaneGFF_dilDist {h : Ω → DistC} (hh : IsWholePlaneGFF h P) {α : ℂ} (hα : α ≠ 0) :
    IsWholePlaneGFF (fun ω => dilDist hα (h ω)) P := by
  simp_rw [dilDist_eq_rotDist_affineComp hα]
  exact GaussianLQG.isWholePlaneGFF_rotDist (hh.affineComp (norm_pos_iff.2 hα) 0)
    (norm_unit_of_ne hα)

/-! ## The limit law -/

theorem integral_linPullCLM {a : ℂ} (ha : a ≠ 0) (f : TestC) :
    ∫ x, linPullCLM ha f x = ∫ x, f x := by
  rw [linPullCLM, SmallGammaGeodesics.CC.coe_confPullOnCLM]
  exact integral_confPullFun isOpen_univ (differentiableOn_mul_left a) (injOn_mul_left ha)
    (fun y hy => absurd (by rw [image_mul_left_univ ha]; exact mem_univ y) hy)

theorem integral_smoothTest {r : ℝ} (hr : 0 < r) (f : TestC) :
    ∫ x, smoothTest hr f x = ∫ x, f x := integral_linPullCLM _ f

/-- On `B ⊇ supp ρ`, the normalized restriction is the restriction of `h − (h, ρ)`. -/
theorem nrm_restrictTo_eq {B : Opens ℂ} {ρ : TestC} (hρ : tsupport (ρ : ℂ → ℝ) ⊆ B) (u : DistC) :
    nrm (testOnOfSupp B ρ hρ) (restrictTo B u) = restrictTo B (addConst u (-(u ρ))) := by
  ext g
  rw [nrm_apply, restrictTo_testOnOfSupp]
  change u (TestFunction.monoCLM ℝ (n₁ := ⊤) (n₂ := ⊤) (Ω₁ := B) (Ω₂ := ⊤) g) - _ =
    addConst u (-(u ρ)) (TestFunction.monoCLM ℝ (n₁ := ⊤) (n₂ := ⊤) (Ω₁ := B) (Ω₂ := ⊤) g)
  rw [GFFInv.addConst_apply, SmallGammaGeodesics.CC.coe_monoCLM_top]
  ring

/-- **The limit law** (GM l. 549–553, with the repaired scale `r = |α|⁻¹`): if `h` is a whole-plane GFF
normalized by `(h, 𝐟) = 0` (`𝐟` rotation invariant, `∫ 𝐟 = 1`), then for every open `B ⊇ supp f_r`
the normalized field `(h − (h, f_r))|_B` has the law of `h(α ·)|_B`. -/
theorem map_nrm_restrict_eq {h : Ω → DistC} (hh : IsWholePlaneGFF h P) {α : ℂ} (hα : α ≠ 0)
    {f : TestC} (hf1 : ∫ x, f x = 1) (hrot : ∀ u : ℂ, ‖u‖ = 1 → ∀ z : ℂ, f (u * z) = f z)
    (hnorm : ∀ᵐ ω ∂P, h ω f = 0) {B : Opens ℂ}
    (hFB : tsupport (smoothTest (inv_pos.2 (norm_pos_iff.2 hα)) f : ℂ → ℝ) ⊆ B) :
    P.map (fun ω => nrm (testOnOfSupp B _ hFB) (restrictTo B (h ω))) =
      P.map (fun ω => restrictTo B (dilDist hα (h ω))) := by
  set F : TestC := smoothTest (inv_pos.2 (norm_pos_iff.2 hα)) f with hFdef
  have hF1 : ∫ x, F x = 1 := by rw [hFdef, integral_smoothTest, hf1]
  let N : DistC → ℝ := fun g => g F
  have hNm : Measurable N := GFFInv.measurable_pair F
  have hN : ∀ g c, N (addConst g c) = N g + c := by
    intro g c
    simp only [N, GFFInv.addConst_apply, hF1, one_mul]
  have hcm : Measurable fun ω => -(h ω F) := ((GFFInv.measurable_pair F).comp hh.measurable).neg
  have h1 := hh.addConst hcm
  have h2 := isWholePlaneGFF_dilDist hh hα
  have hn1 : ∀ᵐ ω ∂P, N (addConst (h ω) (-(h ω F))) = 0 :=
    ae_of_all _ fun ω => by rw [hN]; exact add_neg_cancel _
  have hn2 : ∀ᵐ ω ∂P, N (dilDist hα (h ω)) = 0 := by
    filter_upwards [hnorm] with ω hω
    have e1 : N (dilDist hα (h ω)) = smoothAvg (dilDist hα (h ω)) f
        (inv_pos.2 (norm_pos_iff.2 hα)) := rfl
    rw [e1, dilDist_smoothAvg_inv_norm hα (h ω) hrot, smoothAvg_one, hω]
  have key := GFFLaw.map_eq_of_normalized hF1 hNm hN h1 h2 hn1 hn2
  calc P.map (fun ω => nrm (testOnOfSupp B _ hFB) (restrictTo B (h ω)))
      = P.map (restrictTo B ∘ fun ω => addConst (h ω) (-(h ω F))) := by
        congr 1; funext ω; exact nrm_restrictTo_eq hFB (h ω)
    _ = (P.map fun ω => addConst (h ω) (-(h ω F))).map (restrictTo B) :=
        (Measure.map_map (measurable_restrictTo B) h1.measurable).symm
    _ = (P.map fun ω => dilDist hα (h ω)).map (restrictTo B) := by rw [key]
    _ = P.map (fun ω => restrictTo B (dilDist hα (h ω))) :=
        Measure.map_map (measurable_restrictTo B) h2.measurable

/-! ## TV through the pairing embedding, and the modulo-constant carrier -/

/-- TV is unchanged by a map that induces the σ-algebra. -/
theorem tvDist_eq_map_of_comap {α β : Type*} [mα : MeasurableSpace α] [mβ : MeasurableSpace β]
    {ι : α → β} (hm : mα = mβ.comap ι) (μ ν : Measure α) :
    TV.tvDist μ ν = TV.tvDist (μ.map ι) (ν.map ι) := by
  have hι : Measurable ι := by
    intro t ht
    rw [hm]
    exact ⟨t, ht, rfl⟩
  refine le_antisymm ?_ (TV.tvDist_map_le hι)
  refine iSup₂_le fun s hs => ?_
  have hs' : MeasurableSet[mβ.comap ι] s := hm ▸ hs
  obtain ⟨t, ht, rfl⟩ := hs'
  rw [← Measure.map_apply hι ht, ← Measure.map_apply hι ht]
  exact le_iSup₂_of_le t ht le_rfl

/-- The pairing embedding of `𝒟'(B)`. -/
def distEval (B : Opens ℂ) (u : DistOn B) : TestOn B → ℝ := fun g => u g

theorem tvDist_distOn_eq (B : Opens ℂ) (μ ν : Measure (DistOn B)) :
    TV.tvDist μ ν = TV.tvDist (μ.map (distEval B)) (ν.map (distEval B)) :=
  tvDist_eq_map_of_comap rfl μ ν

/-- The modulo-constant observation on `B`: pairings with mean-zero tests supported in `B`
(IG4 Prop 2.10(i): "restricting `φ ↦ (h, φ)` to `φ ∈ 𝓗_0(B)`"). -/
def mzObs (B : Opens ℂ) (u : DistOn B) : SmallGammaGeodesics.TestC0On B → ℝ :=
  fun ψ => u (testOnOfSupp B ψ.1.1 ψ.2)

theorem measurable_mzObs (B : Opens ℂ) : Measurable (mzObs B) :=
  measurable_pi_iff.2 fun _ => measurable_distOn_apply _

/-- `g − (∫ g) ρ` as a mean-zero test supported in `B`. -/
def recenterB {B : Opens ℂ} {ρ : TestC} (hρ : tsupport (ρ : ℂ → ℝ) ⊆ B) (hρ1 : ∫ x, ρ x = 1)
    (g : TestOn B) : SmallGammaGeodesics.TestC0On B :=
  ⟨⟨SmallGammaGeodesics.CC.recTest B ρ g, SmallGammaGeodesics.CC.integral_recTest B hρ1 g⟩,
    SmallGammaGeodesics.CC.tsupport_recTest_subset B hρ g⟩

theorem distEval_nrm {B : Opens ℂ} {ρ : TestC} (hρ : tsupport (ρ : ℂ → ℝ) ⊆ B)
    (hρ1 : ∫ x, ρ x = 1) (u : DistOn B) :
    distEval B (nrm (testOnOfSupp B ρ hρ) u) = fun g => mzObs B u (recenterB hρ hρ1 g) := by
  funext g
  simp only [distEval, mzObs, recenterB, nrm_apply]
  have e : testOnOfSupp B (SmallGammaGeodesics.CC.recTest B ρ g)
      (SmallGammaGeodesics.CC.tsupport_recTest_subset B hρ g) =
      g - (∫ x, g x) • testOnOfSupp B ρ hρ := by
    ext z
    change SmallGammaGeodesics.CC.recTest B ρ g z = _
    rw [SmallGammaGeodesics.CC.coe_recTest]
    rfl
  rw [e, map_sub, map_smul, smul_eq_mul]
  ring

/-- **Data processing to the modulo-constant carrier.** TV of the normalized laws on `B` is at most
the TV of the modulo-constant laws (the IG4 carrier). -/
theorem tvDist_nrm_le {B : Opens ℂ} {ρ : TestC} (hρ : tsupport (ρ : ℂ → ℝ) ⊆ B)
    (hρ1 : ∫ x, ρ x = 1) (μ ν : Measure (DistOn B)) :
    TV.tvDist (μ.map (nrm (testOnOfSupp B ρ hρ))) (ν.map (nrm (testOnOfSupp B ρ hρ))) ≤
      TV.tvDist (μ.map (mzObs B)) (ν.map (mzObs B)) := by
  have hn := measurable_nrm (testOnOfSupp B ρ hρ)
  have hΨ : Measurable fun (x : SmallGammaGeodesics.TestC0On B → ℝ) (g : TestOn B) =>
      x (recenterB hρ hρ1 g) := measurable_pi_iff.2 fun g => measurable_pi_apply _
  have hE : Measurable (distEval B) := measurable_pi_iff.2 fun g => measurable_distOn_apply g
  rw [tvDist_distOn_eq, Measure.map_map hE hn, Measure.map_map hE hn]
  have e : distEval B ∘ nrm (testOnOfSupp B ρ hρ) =
      (fun (x : SmallGammaGeodesics.TestC0On B → ℝ) (g : TestOn B) => x (recenterB hρ hρ1 g)) ∘
        mzObs B := by
    funext u
    exact distEval_nrm hρ hρ1 u
  rw [e, ← Measure.map_map hΨ (measurable_mzObs B), ← Measure.map_map hΨ (measurable_mzObs B)]
  exact TV.tvDist_map_le hΨ

end SupercriticalConformalCovariance.GM24
