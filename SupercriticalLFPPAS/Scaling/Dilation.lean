import SupercriticalLFPPAS.Core.Interfaces
import SupercriticalLQGUniqueness.B2.Polylog.P1LocalizedCont
import SupercriticalLQGUniqueness.B2.Polylog.P4Event
import SupercriticalLQGUniqueness.B2.Strong.Bridge
import LQGMetric.Field.CircleAvgAffine

/-! # Dilation covariance of localized LFPP

This proves the deterministic identities in (2.4) by scaling the localized test function and
then applying the existing affine LFPP metric formula. -/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set
open scoped ENNReal
open LQGMetric (DistC addConst)
open SupercriticalLFPPAS.Core
open SupercriticalLQGUniqueness.B2.Polylog

namespace SupercriticalLFPPAS.Scaling

private theorem ad_plBump_scale (q q' δ δ' s : ℝ)
    (hδ : δ ∈ Ioo (0 : ℝ) 1) (hδ' : δ' ∈ Ioo (0 : ℝ) 1) (hs : 0 < s)
    (hR : plRad q δ = s * plRad q' δ') (y : ℂ) :
    plBump q δ hδ (s • y) = plBump q' δ' hδ' y := by
  unfold plBump
  rw [LQGMetric.LFPP.locBump, LQGMetric.LFPP.locBump,
    Real.sqrt_sq (plRad_pos q hδ).le, Real.sqrt_sq (plRad_pos q' hδ').le]
  apply congrArg ((ContDiffBumpBase.ofInnerProductSpace ℂ).toFun 2)
  rw [smul_smul]
  congr 1
  rw [hR]
  have hpos : 0 < plRad q' δ' := plRad_pos q' hδ'
  field_simp [hs.ne', hpos.ne']

private theorem ad_heatKernel_scale (δ δ' s : ℝ) (hs : 0 < s) (hδ'pos : 0 < δ')
    (hδ : δ = s * δ') (z u y : ℂ) :
    LQGMetric.heatKernel (δ ^ 2 / 2) (z + s • u) (z + s • y) =
      s⁻¹ ^ 2 * LQGMetric.heatKernel (δ' ^ 2 / 2) u y := by
  have hnorm : ‖s • (u - y)‖ = s * ‖u - y‖ := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos hs]
  have hdist : z + s • u - (z + s • y) = s • (u - y) := by
    rw [add_sub_add_left_eq_sub, smul_sub]
  have hpref : (2 * Real.pi * (δ ^ 2 / 2))⁻¹ =
      s⁻¹ ^ 2 * (2 * Real.pi * (δ' ^ 2 / 2))⁻¹ := by
    rw [hδ]
    field_simp [hs.ne', hδ'pos.ne']
  have harg : -(s * ‖u - y‖) ^ 2 / (2 * ((s * δ') ^ 2 / 2)) =
      -‖u - y‖ ^ 2 / (2 * (δ' ^ 2 / 2)) := by
    field_simp [hs.ne', hδ'pos.ne']
  unfold LQGMetric.heatKernel
  rw [hdist, hnorm, hpref, hδ, harg]
  ring

private theorem ad_plTest_scale (q q' δ δ' s : ℝ)
    (hδ : δ ∈ Ioo (0 : ℝ) 1) (hδ' : δ' ∈ Ioo (0 : ℝ) 1) (hs : 0 < s)
    (hδs : δ = s * δ') (hR : plRad q δ = s * plRad q' δ')
    (z u y : ℂ) :
    plTest q δ hδ (z + s • u) (z + s • y) =
      s⁻¹ ^ 2 * plTest q' δ' hδ' u y := by
  rw [plTest_apply, plTest_apply]
  have harg : z + s • u - (z + s • y) = s • (u - y) := by
    rw [add_sub_add_left_eq_sub, smul_sub]
  rw [harg, ad_plBump_scale q q' δ δ' s hδ hδ' hs hR (u - y),
    ad_heatKernel_scale δ δ' s hs hδ'.1 hδs z u y]
  ring

private theorem ad_plZ_scale (q q' δ δ' s : ℝ)
    (hδ : δ ∈ Ioo (0 : ℝ) 1) (hδ' : δ' ∈ Ioo (0 : ℝ) 1) (hs : 0 < s)
    (hδs : δ = s * δ') (hR : plRad q δ = s * plRad q' δ') :
    plZ q δ hδ = plZ q' δ' hδ' := by
  have hsub (w : ℂ) :
      plTest q δ hδ 0 (s • w) = s⁻¹ ^ 2 * plTest q' δ' hδ' 0 w := by
    simpa only [smul_zero, zero_add] using
      ad_plTest_scale q q' δ δ' s hδ hδ' hs hδs hR 0 0 w
  unfold plZ
  calc
    (∫ w, plTest q δ hδ 0 w) =
        s ^ 2 * ∫ w, plTest q δ hδ 0 (s • w) := by
          simpa only [smul_zero, add_zero] using
            (LQGMetric.CircleAvg.integral_eq_affine
              (fun w => plTest q δ hδ 0 w) hs 0)
    _ = s ^ 2 * ∫ w, s⁻¹ ^ 2 * plTest q' δ' hδ' 0 w := by
          congr 1
          apply integral_congr_ae
          filter_upwards with w
          exact hsub w
    _ = ∫ w, plTest q' δ' hδ' 0 w := by
          rw [integral_const_mul]
          have hsimp : s ^ 2 * s⁻¹ ^ 2 = 1 := by
            field_simp [hs.ne']
          rw [← mul_assoc, hsimp, one_mul]

private theorem ad_testDilate_plTest (q q' δ δ' s : ℝ)
    (hδ : δ ∈ Ioo (0 : ℝ) 1) (hδ' : δ' ∈ Ioo (0 : ℝ) 1) (hs : 0 < s)
    (hδs : δ = s * δ') (hR : plRad q δ = s * plRad q' δ')
    (z u : ℂ) :
    SupercriticalLQGUniqueness.testDilate ⟨s, hs⟩ z (plTest q' δ' hδ' u) =
      s ^ 2 • plTest q δ hδ (z + s • u) := by
  rw [SupercriticalLQGUniqueness.B2.Strong.testDilate_eq_testAffinePull]
  ext x
  rw [LQGMetric.testAffinePull_apply s z hs.ne']
  change plTest q' δ' hδ' u ((x - z) / s) =
    s ^ 2 * plTest q δ hδ (z + s • u) x
  have hx : z + s • ((x - z) / s) = x := by
    simp only [Complex.real_smul, div_eq_mul_inv]
    field_simp [hs.ne']
    ring
  have hscale := ad_plTest_scale q q' δ δ' s hδ hδ' hs hδs hR z u ((x - z) / s)
  rw [hx] at hscale
  calc
    plTest q' δ' hδ' u ((x - z) / s) =
        s ^ 2 * (s⁻¹ ^ 2 * plTest q' δ' hδ' u ((x - z) / s)) := by
          field_simp [hs.ne']
    _ = s ^ 2 * plTest q δ hδ (z + s • u) x := by rw [← hscale]

private theorem ad_plMollify_scale (q q' δ δ' s : ℝ)
    (hδ : δ ∈ Ioo (0 : ℝ) 1) (hδ' : δ' ∈ Ioo (0 : ℝ) 1) (hs : 0 < s)
    (hδs : δ = s * δ') (hR : plRad q δ = s * plRad q' δ') (z u : ℂ) (g : DistC) :
    plMollify q δ hδ g (z + s • u) =
      plMollify q' δ' hδ' (SupercriticalLQGUniqueness.scaleTranslateDist ⟨s, hs⟩ z g) u := by
  have htest := ad_testDilate_plTest q q' δ δ' s hδ hδ' hs hδs hR z u
  have hpair :
      SupercriticalLQGUniqueness.scaleTranslateDist ⟨s, hs⟩ z g (plTest q' δ' hδ' u) =
        g (plTest q δ hδ (z + s • u)) := by
    rw [SupercriticalLQGUniqueness.B2.Strong.scaleTranslateDist_eq_affineComp,
      LQGMetric.GFFInv.affineComp_apply,
      ← SupercriticalLQGUniqueness.B2.Strong.testDilate_eq_testAffinePull, htest,
      map_smul, smul_eq_mul]
    field_simp [hs.ne']
  unfold plMollify
  rw [ad_plZ_scale q q' δ δ' s hδ hδ' hs hδs hR, hpair]

private theorem ad_locField_scale (δ L : ℝ) (hδ : δ ∈ Ioo (0 : ℝ) 1)
    (s : Set.Ioi (0 : ℝ)) (hδs : δ / s ∈ Ioo (0 : ℝ) 1)
    (hδlog : 1 < Real.log δ⁻¹) (hL : Real.log δ⁻¹ ≤ L)
    (hδslog : 1 < Real.log (δ / s)⁻¹) (hLs : Real.log (δ / s)⁻¹ ≤ L)
    (z : ℂ) (c : ℝ) (g : DistC) (u : ℂ) :
    locFieldC δ L hδ g (z + (s : ℝ) • u) =
      locFieldC (δ / s) L hδs
        (addConst (SupercriticalLQGUniqueness.scaleTranslateDist s z g) (-c)) u + c := by
  have hspos : (0 : ℝ) < (s : ℝ) := Set.mem_Ioi.mp s.2
  have hδscale : δ = (s : ℝ) * (δ / s) := by
    field_simp [hspos.ne']
  have hRad :
      plRad (Field.uniformLocalizationExponent δ L) δ =
        (s : ℝ) * plRad (Field.uniformLocalizationExponent (δ / s) L) (δ / s) := by
    rw [Field.plRad_uniform_eq δ L hδlog hL,
      Field.plRad_uniform_eq (δ / s) L hδslog hLs]
    field_simp [hspos.ne']
  change plMollify (Field.uniformLocalizationExponent δ L) δ hδ g
      (z + (s : ℝ) • u) =
    plMollify (Field.uniformLocalizationExponent (δ / s) L) (δ / s) hδs
      (addConst (SupercriticalLQGUniqueness.scaleTranslateDist s z g) (-c)) u + c
  rw [plMollify_addConst (Field.uniformLocalizationExponent (δ / s) L) (δ / s) hδs
    (SupercriticalLQGUniqueness.scaleTranslateDist s z g) (-c) u]
  rw [ad_plMollify_scale (Field.uniformLocalizationExponent δ L)
    (Field.uniformLocalizationExponent (δ / s) L) δ (δ / s) (s : ℝ)
    hδ hδs s.2 hδscale hRad z u g]
  ring

theorem dilation_holds (S : Core.Setup) : Core.DilationStmt S := by
  constructor
  · intro ε hε hlog g
    have hq : Field.uniformLocalizationExponent ε (Real.log ε⁻¹) = 1 := by
      unfold Field.uniformLocalizationExponent
      have hden : Real.log (Real.log ε⁻¹) ≠ 0 := (Real.log_pos hlog).ne'
      have hden' : Real.log (Real.log (1 / ε)) ≠ 0 := by
        simpa only [one_div] using hden
      field_simp [hden']
    rw [Core.locMetric, Core.locMetricY, hq]
  · intro δ L hδ s hδs hδlog hL hδslog hLs z c g
    constructor
    · intro u
      exact ad_locField_scale δ L hδ s hδs hδlog hL hδslog hLs z c g u
    · intro u v
      let b : ℂ := -((s : ℝ)⁻¹ : ℂ) * z
      let cInv : ℂ := ((s : ℝ)⁻¹ : ℂ)
      let g' : DistC := addConst (SupercriticalLQGUniqueness.scaleTranslateDist s z g) (-c)
      have hspos : (0 : ℝ) < (s : ℝ) := Set.mem_Ioi.mp s.2
      have hφ : ∀ x : ℂ,
          locFieldC δ L hδ g x = locFieldC (δ / s) L hδs g' (b + cInv * x) + c := by
        intro x
        have hx : z + (s : ℝ) • ((x - z) / s) = x := by
          simp only [Complex.real_smul, div_eq_mul_inv]
          field_simp [hspos.ne']
          ring
        have hb : b + cInv * x = (x - z) / s := by
          dsimp [b, cInv]
          simp only [div_eq_mul_inv]
          field_simp [hspos.ne']
          ring
        calc
          locFieldC δ L hδ g x = locFieldC δ L hδ g
              (z + (s : ℝ) • ((x - z) / s)) := by rw [hx]
          _ = locFieldC (δ / s) L hδs g' ((x - z) / s) + c :=
            ad_locField_scale δ L hδ s hδs hδlog hL hδslog hLs z c g ((x - z) / s)
          _ = locFieldC (δ / s) L hδs g' (b + cInv * x) + c := by rw [← hb]
      have hcInv : cInv ≠ 0 := by
        dsimp [cInv]
        exact_mod_cast inv_ne_zero hspos.ne'
      have hnorm : ‖cInv‖ = (s : ℝ)⁻¹ := by
        change ‖((s : ℝ)⁻¹ : ℂ)‖ = (s : ℝ)⁻¹
        rw [norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hspos]
      have hcoord (x : ℂ) : b + cInv * (z + (s : ℝ) • x) = x := by
        dsimp [b, cInv]
        field_simp [hspos.ne']
        ring
      have hfactor :
          ((S.m ⟨δ / s, hδs.1⟩ : ℝ) * Real.exp ((S.ξ : ℝ) * c)) /
              ((S.m ⟨δ, hδ.1⟩ : ℝ) * ‖cInv‖) =
            ((s : ℝ) * (S.m ⟨δ / s, hδs.1⟩ : ℝ) /
              (S.m ⟨δ, hδ.1⟩ : ℝ)) * Real.exp ((S.ξ : ℝ) * c) := by
        rw [hnorm]
        have hsM : (S.m ⟨δ, hδ.1⟩ : ℝ) ≠ 0 :=
          (Set.mem_Ioi.mp (S.m ⟨δ, hδ.1⟩).2).ne'
        field_simp [hspos.ne', hsM]
      have hmetric :=
        SupercriticalLQGUniqueness.B2.Polylog.lfppMetric_affine (S.ξ : ℝ)
          (S.m ⟨δ / s, hδs.1⟩) (S.m ⟨δ, hδ.1⟩)
          (φ := locFieldC (δ / s) L hδs g') (φ' := locFieldC δ L hδ g)
          (b := b) (c := cInv) hcInv c hφ (z + (s : ℝ) • u) (z + (s : ℝ) • v)
      rw [hcoord u, hcoord v, hfactor] at hmetric
      change
        SupercriticalLQGUniqueness.B2.Median.lfppMetric (S.ξ : ℝ) (S.m ⟨δ, hδ.1⟩)
            (locFieldC δ L hδ g) (z + (s : ℝ) • u, z + (s : ℝ) • v) =
          ENNReal.ofReal (((s : ℝ) * (S.m ⟨δ / s, hδs.1⟩ : ℝ) /
              (S.m ⟨δ, hδ.1⟩ : ℝ)) * Real.exp ((S.ξ : ℝ) * c)) *
            SupercriticalLQGUniqueness.B2.Median.lfppMetric (S.ξ : ℝ)
              (S.m ⟨δ / s, hδs.1⟩) (locFieldC (δ / s) L hδs g') (u, v)
      exact hmetric

end SupercriticalLFPPAS.Scaling
