import QuantumZipper.Proofs.Section5.Prop16LocCoupleAnnAsm
import QuantumZipper.Proofs.GFF.K3.MixedM6Kernel

/-!
# DOM-a by annulus features (decision D34), AN5: the main assembly

`domMarkovCurveAnn_holds : DomMarkovCurveAnnStmt` — the general DOM-a `DomMarkovCurveEStmt D c d`
from AN2 (`FreeAnnRepStmt`), AN3 (`FreeAnnLipStmt`) and AN4 (`Prop16UnifLocalStmt`); and
`theorem1_6_of_annNodes`: Proposition 1.6 from AN2–AN4 and the masked Palm nodes B′, C′.
The construction is described in `Prop16LocCoupleAnnNodes.lean` and `Prop16LocCoupleAnnAsm.lean`.
Own argument (Hilbert-space bookkeeping around the proved M5 results).
-/

noncomputable section

open MeasureTheory Set Metric
open scoped RealInnerProductSpace NNReal

namespace QuantumZipper

namespace Prop16Asm

open GFFExist K3

theorem inner_toLp_an {D : Set ℂ} (u : HkE) (v : GradSpace D)
    (x : WithLp 2 (HkE × GradSpace D)) :
    ⟪(WithLp.toLp 2 (u, v) : WithLp 2 (HkE × GradSpace D)), x⟫ =
      ⟪u, (WithLp.ofLp x).1⟫ + ⟪v, (WithLp.ofLp x).2⟫ := by
  simp [WithLp.prod_inner_apply]

/-- **AN5: the general DOM-a from AN2–AN4.** -/
theorem domMarkovCurveAnn_holds : DomMarkovCurveAnnStmt := by
  intro hU hRep hLip D c d hgeo
  set S := realSet (Icc c d) with hSdef
  have hG : AnnGeom D S := ⟨hgeo.1, hgeo.2.2.2.1, hgeo.2.2.1,
    fun _ ⟨t, _, ht⟩ => by rw [← ht]; simp, exists_pos_energy_mixedSpace hgeo.1 hgeo.2.1.nonempty⟩
  obtain ⟨J, hJ, hJr⟩ := exists_annJ hG
  -- the reference measure
  obtain ⟨Mb, hMb⟩ := hgeo.2.2.1.subset_closedBall 0
  set p : ℂ := ((|Mb| + 2 : ℝ) : ℂ) * Complex.I with hpdef
  have hpim : p.im = |Mb| + 2 := by simp [hpdef]
  have hp : p ∈ Hbar := by
    show 0 ≤ p.im
    rw [hpim]; positivity
  have hpn : ‖p‖ = |Mb| + 2 := by
    rw [hpdef, norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (by positivity)]
  set ρ₀ : AdmT := ⟨foldedCircle p 1, isAdmissibleH_foldedCircle hp one_pos⟩ with hρdef
  set L := closedBall p 1 ∩ Hbar with hLdef
  have hLc : IsCompact L := (isCompact_closedBall p 1).inter_right isClosed_Hbar
  have hρL : ρ₀.1 Lᶜ = 0 := K3.foldedCircle_compl_eq_zero hp zero_le_one
  have hLD : L ⊆ Hbar \ closure D := by
    rintro x ⟨hx1, hx2⟩
    refine ⟨hx2, fun hxD => ?_⟩
    have hxM := closure_minimal hMb isClosed_closedBall hxD
    rw [mem_closedBall, dist_zero_right] at hxM
    rw [mem_closedBall, dist_eq_norm] at hx1
    have := norm_sub_norm_le p x
    rw [norm_sub_rev] at hx1
    linarith [le_abs_self Mb]
  have hρ1 : ρ₀.1 univ = 1 := measure_univ
  refine ⟨WithLp 2 (HkE × GradSpace D), inferInstance, inferInstance, inferInstance,
    inferInstance, inlL2 D, annE J, ρ₀, annH D S ρ₀, hρ1, fun μ ν hμ hν => inner_annE J hμ hν,
    ?_, ?_⟩
  · -- Lipschitz on compacts
    intro K hK hKV
    obtain ⟨R, hR, hyp⟩ := hU D c d hgeo K hK hKV
    obtain ⟨Lf, hLf⟩ := hLip D S K R hyp
    obtain ⟨Kl, hKl⟩ := exists_abs_inner_remVec_sub_le hyp hG.pos
    refine ⟨(max Lf 0 + max Kl 0).toNNReal,
      lipschitzOnWith_iff_dist_le_mul.2 fun z hz z' hz' => ?_⟩
    have hz2 := hyp.local_ z hz
    have hz2' := hyp.local_ z' hz'
    rw [dist_eq_norm, dist_eq_norm, annH, annH, ← WithLp.toLp_sub, Prod.mk_sub_mk,
      annHf_eq hR hz2, annHf_eq hR hz2', annHm_eq hG hR hz2, annHm_eq hG hR hz2', ← map_sub,
      sub_sub_sub_cancel_right, neg_sub_neg]
    refine (norm_toLp_le_an _ _).trans ?_
    set w := freeFold z R - freeFold z' R with hw
    set u := (freeAnnSpan D S)ᗮ.starProjection w with hu
    have huM : u ∈ (freeAnnSpan D S)ᗮ := (freeAnnSpan D S)ᗮ.starProjection_apply_mem w
    have hu2 : ‖u‖ ^ 2 = ⟪w, u⟫ := by
      rw [← real_inner_self_eq_norm_sq, hu, (freeAnnSpan D S)ᗮ.inner_starProjection_left_eq_right,
        Submodule.starProjection_eq_self_iff.2 ((freeAnnSpan D S)ᗮ.starProjection_apply_mem w)]
    have hb1 : ‖u‖ ≤ max Lf 0 * ‖z - z'‖ := by
      refine norm_le_of_sq_le_an (norm_nonneg _) (by positivity) ?_
      have h1 := hLf z hz z' hz' u huM
      rw [hu2]
      calc ⟪w, u⟫ ≤ |⟪w, u⟫| := le_abs_self _
        _ ≤ Lf * ‖z - z'‖ * ‖u‖ := h1
        _ ≤ max Lf 0 * ‖z - z'‖ * ‖u‖ := by
          gcongr
          exact le_max_left _ _
    set v := remVec D S (foldedCircle z' R) - remVec D S (foldedCircle z R) with hv
    have hvG : v ∈ gradClosure D (mixedSpace D S) := sub_mem (remVec_mem_gradClosure hG.bounded _)
      (remVec_mem_gradClosure hG.bounded _)
    have hvM : v ∈ (annulusSpan D S)ᗮ := sub_mem ((annulusSpan D S)ᗮ.starProjection_apply_mem _) ((annulusSpan D S)ᗮ.starProjection_apply_mem _)
    have hb2 : ‖v‖ ≤ max Kl 0 * ‖z - z'‖ := by
      refine norm_le_of_sq_le_an (norm_nonneg _) (by positivity) ?_
      have h1 := hKl z' hz' z hz v hvG hvM
      rw [← real_inner_self_eq_norm_sq]
      calc ⟪v, v⟫ ≤ |⟪v, v⟫| := le_abs_self _
        _ ≤ Kl * ‖z' - z‖ * ‖v‖ := h1
        _ ≤ max Kl 0 * ‖z - z'‖ * ‖v‖ := by
          rw [norm_sub_rev z' z]
          gcongr
          exact le_max_left _ _
    rw [Real.coe_toNNReal _ (by positivity)]
    linarith
  · -- the weak curve identity
    intro μ hμD hμ1 ⟨K, hK, hKV, hμK⟩ x
    have : IsProbabilityMeasure μ.1 := ⟨hμ1⟩
    obtain ⟨R, hR, hyp⟩ := hU D c d hgeo K hK hKV
    obtain ⟨Lf, hLf⟩ := hLip D S K R hyp
    obtain ⟨Kl, hKl⟩ := exists_abs_inner_remVec_sub_le hyp hG.pos
    set x1 := (WithLp.ofLp x).1 with hx1
    set x2 := (WithLp.ofLp x).2 with hx2
    set u := (freeAnnSpan D S)ᗮ.starProjection x1 with hu
    have huM : u ∈ (freeAnnSpan D S)ᗮ := (freeAnnSpan D S)ᗮ.starProjection_apply_mem x1
    set u₂ := (annulusSpan D S)ᗮ.starProjection ((gradClosure D (mixedSpace D S)).starProjection x2) with hu₂
    have hu₂M : u₂ ∈ (annulusSpan D S)ᗮ := (annulusSpan D S)ᗮ.starProjection_apply_mem _
    have hu₂G : u₂ ∈ gradClosure D (mixedSpace D S) := by
      rw [hu₂, Submodule.starProjection_orthogonal_val]
      exact sub_mem ((gradClosure D (mixedSpace D S)).starProjection_apply_mem _)
        (annulusSpan_le_gradClosure hG.bounded ((annulusSpan D S).starProjection_apply_mem _))
    have hrem : ∀ ν : Measure ℂ, ⟪remVec D S ν, x2⟫ = ⟪remVec D S ν, u₂⟫ := fun ν => by
      rw [inner_eq_inner_starProjection_an (remVec_mem_gradClosure hG.bounded ν) x2,
        inner_eq_inner_starProjection_an (K := (annulusSpan D S)ᗮ) (g := remVec D S ν)
          ((annulusSpan D S)ᗮ.starProjection_apply_mem _)]
    -- the two scalar functions and their integrability
    set F : ℂ → ℝ := fun z => ⟪freeFold z R, u⟫ with hF
    set Gm : ℂ → ℝ := fun z => ⟪remVec D S (foldedCircle z R), u₂⟫ with hGm
    have hFc : ContinuousOn F K := by
      refine ((lipschitzOnWith_iff_dist_le_mul (K := (max Lf 0 * ‖u‖).toNNReal)
        (s := K) (f := F)).2 fun z hz z' hz' => ?_).continuousOn
      rw [Real.dist_eq, hF]
      rw [Real.coe_toNNReal _ (by positivity), ← inner_sub_left, dist_eq_norm]
      calc |⟪freeFold z R - freeFold z' R, u⟫| ≤ Lf * ‖z - z'‖ * ‖u‖ := hLf z hz z' hz' u huM
        _ ≤ max Lf 0 * ‖z - z'‖ * ‖u‖ := by gcongr; exact le_max_left _ _
        _ = max Lf 0 * ‖u‖ * ‖z - z'‖ := by ring
    have hGc' : ContinuousOn Gm K := by
      refine ((lipschitzOnWith_iff_dist_le_mul (K := (max Kl 0 * ‖u₂‖).toNNReal)
        (s := K) (f := Gm)).2 fun z hz z' hz' => ?_).continuousOn
      rw [Real.dist_eq, hGm]
      rw [Real.coe_toNNReal _ (by positivity), ← inner_sub_left, dist_eq_norm]
      calc |⟪remVec D S (foldedCircle z R) - remVec D S (foldedCircle z' R), u₂⟫|
          ≤ Kl * ‖z - z'‖ * ‖u₂‖ := hKl z hz z' hz' u₂ hu₂G hu₂M
        _ ≤ max Kl 0 * ‖z - z'‖ * ‖u₂‖ := by gcongr; exact le_max_left _ _
        _ = max Kl 0 * ‖u₂‖ * ‖z - z'‖ := by ring
    have hFi : Integrable F μ.1 := integrable_of_continuousOn_carrier hK hFc hμK
    have hGi : Integrable Gm μ.1 := integrable_of_continuousOn_carrier hK hGc' hμK
    -- right side
    have hae : ∀ᵐ z ∂μ.1, z ∈ K := mem_ae_iff.2 hμK
    have hRHS : ∫ z, ⟪annH D S ρ₀ z, x⟫ ∂μ.1 =
        (∫ z, F z ∂μ.1) - ⟪freeVec ρ₀, u⟫ - ∫ z, Gm z ∂μ.1 := by
      rw [integral_congr_ae (g := fun z => F z - ⟪freeVec ρ₀, u⟫ - Gm z) ?_,
        integral_sub (f := fun z => F z - ⟪freeVec ρ₀, u⟫) (hFi.sub (integrable_const _)) hGi, integral_sub hFi (integrable_const _),
        integral_const, probReal_univ, one_smul]
      filter_upwards [hae] with z hz
      have hz2 := hyp.local_ z hz
      rw [annH, inner_toLp_an, annHf_eq hR hz2, annHm_eq hG hR hz2, ← hx1, ← hx2,
        (freeAnnSpan D S)ᗮ.inner_starProjection_left_eq_right, ← hu, inner_sub_left, inner_neg_left, hrem]
      simp only [hF, hGm]
      ring
    -- left side
    have hy := sub_annJ_mem_orthogonal hG hJ μ ρ₀ hμD (by rw [hμ1, hρ1]) hK hμK hLc hρL hLD
    have hJu : ⟪J (annP D S (rieszVec D (mixedSpace D S) μ.1)), u⟫ = 0 :=
      Submodule.inner_right_of_mem_orthogonal (hJr _) huM
    have hfree : ⟪freeVec μ, u⟫ = ∫ z, F z ∂μ.1 :=
      hRep D S K R hyp μ hμK R hR (by linarith) u huM
    have hmix : ⟪remVec D S μ.1, x2⟫ = ∫ z, Gm z ∂μ.1 := by
      rw [hrem, inner_remVec_of_mem_orthogonal μ.1 hu₂M,
        inner_rieszVec_eq_integral_of_mem_orthogonal hyp hG.pos μ.2 hμK hR (by linarith)
          hu₂G hu₂M]
      refine integral_congr_ae (ae_of_all _ fun z => ?_)
      show _ = ⟪remVec D S (foldedCircle z R), u₂⟫
      rw [inner_remVec_of_mem_orthogonal _ hu₂M]
    have hLHS : ⟪inlL2 D (freeVec μ - freeVec ρ₀) - annE J μ.1, x⟫ =
        ⟪freeVec μ - freeVec ρ₀ - J (annP D S (rieszVec D (mixedSpace D S) μ.1)), x1⟫ -
          ⟪remVec D S μ.1, x2⟫ := by
      rw [inner_sub_left, annE, inner_toLp_an]
      show ⟪(WithLp.toLp 2 (freeVec μ - freeVec ρ₀, 0) : WithLp 2 (HkE × GradSpace D)), x⟫ - _ = _
      rw [inner_toLp_an, ← hx1, ← hx2, inner_zero_left, add_zero, inner_sub_left
        (freeVec μ - freeVec ρ₀)]
      rw [inner_toLp_an, ← hx1, ← hx2]
      ring
    rw [hLHS, hRHS, inner_eq_inner_starProjection_an hy x1, ← hu, inner_sub_left, hJu,
      inner_sub_left, hfree, hmix]
    ring

/-- **Proposition 1.6 from the annulus nodes AN2–AN4 and the masked Palm nodes B′, C′.** -/
theorem theorem1_6_of_annNodes (hU : Prop16UnifLocalStmt)
    (hRep : ∀ D S : Set ℂ, FreeAnnRepStmt D S) (hLip : ∀ D S : Set ℂ, FreeAnnLipStmt D S)
    (hId : Prop16PalmIdMaskStmt) (hFix : Prop16FixedZoomMaskStmt) : theorem1_6 :=
  theorem1_6_of_ann domMarkovCurveAnn_holds hU hRep hLip hId hFix

end Prop16Asm

end QuantumZipper
