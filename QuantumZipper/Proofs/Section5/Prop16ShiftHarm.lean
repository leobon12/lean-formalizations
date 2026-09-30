import QuantumZipper.Proofs.Section5.Prop16MarkovMask2Final
import QuantumZipper.Proofs.GFF.K3.MixedM7AsmXi

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# Proposition 1.6, node C′: the Palm shift is `−2 log|· − x|` plus a Neumann-harmonic function

This file proves `Prop16PalmShiftHarmStmt` (`Prop16MarkovMask2.lean`), hence (with
`theorem1_6_of_palmHarm`) Proposition 1.6 from node B′ and D3⁺(i) in N2 form.

**Route.** Take a half-disc `B = ball x R ∩ H ⊆ D` on the free arc and `0 < ρ < R`. For an
admissible `μ` carried by `closedBall x ρ` and the shrinking folded circles `ν_k = fc(x, 2^{-k})`,
the half-disc Markov decomposition of the mixed covariance (`mixedHalfDiscMarkovCov_holds`, M7-a)
gives

`Cov_D(μ, ν_k) = Cov_D(bal μ, bal ν_k) + kernelCov G_B μ ν_k`,

where `G_B = neumannH − (balayage part)` is the Neumann/Dirichlet Green function of the half-disc.
Here `bal ν_k = P_x` exactly (mean value of the Poisson kernel, `bind_foldedCircle_halfDiscPoisson`),
`Cov_D(bal μ, P_x) = ∫ ⟪v_{P_y}, v_{P_x}⟫ dμ(y)` (weak Bochner identity,
`inner_rieszVec_bind_eq_integral_mixCurve`), the `neumannH` pairing of `bal μ` (carried by the
semicircle `|u − x| = R`) with `ν_k` is the constant `−2 log R · μ(ℂ)`, and
`kernelCov neumannH μ ν_k → ∫ neumannH(x, ·) dμ`. Hence

`G_D(x, μ) = ∫ (neumannH(x, ·) + ⟪v_{P_·}, v_{P_x}⟫ + 2 log R) dμ`,

and `z ↦ ⟪v_{P_{foldH z}}, v_{P_x}⟫` is harmonic on `ball x ρ` (`harmonicOnNhd_inner_mixCurve`,
Weyl's lemma). With `neumannH(x, x + w) = −2 log‖w‖` this is the statement.

Source: Sheffield, arXiv:1012.4797, proof of Prop. 1.6 (p. 25): `G_D(x,·) + 2 log|· − x|` is
harmonic across the free arc near `x`; the Markov decomposition is Sheffield, *Gaussian free fields
for mathematicians*, PTRF 139 (2007), Thm 2.17 (here the mixed version M7-a). The assembly of the
limit is own bookkeeping.
-/

noncomputable section

open MeasureTheory Filter Set Metric
open scoped Topology ENNReal ComplexConjugate RealInnerProductSpace

namespace QuantumZipper

namespace Prop16Asm

open K3

/-- `fcPot` of a small circle about `x` is constant on the semicircle `|u − x| = R`. -/
theorem fcPot_of_mem_sphere_sh {x R s : ℝ} (hsR : s ≤ R) {u : ℂ} (hu : u ∈ sphere (x : ℂ) R) :
    KernelId.fcPot s (x : ℂ) u = -2 * Real.log R := by
  have h1 : ‖(x : ℂ) - u‖ = R := by rw [norm_sub_rev]; exact mem_sphere_iff_norm.1 hu
  have h2 : ‖(x : ℂ) - conj u‖ = R := by
    rw [← h1, ← Complex.norm_conj ((x : ℂ) - u), map_sub, Complex.conj_ofReal]
  unfold KernelId.fcPot
  rw [h1, h2, max_eq_right hsR]
  ring

theorem subset_ballH_sh {x ρ R : ℝ} (hρR : ρ ≤ R) :
    closedBall (x : ℂ) ρ ∩ Hbar ⊆ CircleFubini.ballH (|x| + R) := by
  intro y hy
  refine ⟨?_, hy.2⟩
  rw [mem_closedBall_iff_norm, sub_zero]
  have h1 := mem_closedBall_iff_norm.1 hy.1
  calc ‖y‖ = ‖(y - x) + (x : ℂ)‖ := by ring_nf
    _ ≤ ‖y - x‖ + ‖(x : ℂ)‖ := norm_add_le _ _
    _ ≤ |x| + R := by rw [Complex.norm_real, Real.norm_eq_abs]; linarith

theorem compl_null_of_sub_sh {μ : Measure ℂ} {A B : Set ℂ} (hAB : A ⊆ B) (h : μ Aᶜ = 0) :
    μ Bᶜ = 0 :=
  measure_mono_null (compl_subset_compl.2 hAB) h

/-- **The Palm shift on measures carried by a small half-disc about the free-arc point `x`.** -/
theorem mixedGreenSample_halfDisc_sh {D : Set ℂ} {c d x R ρ : ℝ} (hgeo : Prop16Geometry D c d)
    (hx : x ∈ Ioo c d) (hρ : 0 < ρ) (hρR : ρ < R) (hsub : ball (x : ℂ) R ∩ H ⊆ D)
    {μ : Measure ℂ} (hμ : IsAdmissibleH μ) (hμB : μ (closedBall (x : ℂ) ρ)ᶜ = 0) :
    mixedGreenSample D (realSet (Icc c d)) x μ =
      ∫ y, ⟪mixCurve D c d x R ρ y, rieszVec D (mixedSpace D (realSet (Icc c d)))
          (halfDiscPoisson x R x)⟫ ∂μ +
        (∫ y, neumannH (x : ℂ) y ∂μ + 2 * Real.log R * (μ univ).toReal) := by
  set V := mixedSpace D (realSet (Icc c d)) with hVdef
  set e := rieszVec D V (halfDiscPoisson x R x) with hedef
  have hR : 0 < R := hρ.trans hρR
  have := hμ.1
  obtain ⟨hPadm, hM⟩ := mixedHalfDiscMarkovCov_holds D c d x R ρ hgeo hx hρ hρR hsub
  obtain ⟨-, hbA, -, hcov⟩ := hM μ hμ hμB
  have hV : IsDNSpace D V := isDNSpace_mixedSpace D _
  have hxH : (x : ℂ) ∈ Hbar := show (0 : ℝ) ≤ ((x : ℂ)).im by simp
  have hxK : (x : ℂ) ∈ closedBall (x : ℂ) ρ ∩ Hbar := ⟨mem_closedBall_self hρ.le, hxH⟩
  have hμK : μ (closedBall (x : ℂ) ρ ∩ Hbar)ᶜ = 0 := by
    obtain ⟨K, -, hKH, hμK⟩ := hμ.2.1
    rw [compl_inter]
    exact measure_union_null hμB (compl_null_of_sub_sh hKH hμK)
  have hharm : dualCov D V (bal x R μ) (halfDiscPoisson x R x) =
      ∫ y, ⟪mixCurve D c d x R ρ y, e⟫ ∂μ := by
    rw [dualCov_eq_inner_rieszVec hV hbA (hPadm _ hxK)]
    exact inner_rieszVec_bind_eq_integral_mixCurve hgeo hx hρ hρR hsub hμK hbA e
  have hμS : μ (CircleFubini.ballH (|x| + R))ᶜ = 0 :=
    compl_null_of_sub_sh (subset_ballH_sh hρR.le) hμK
  -- the balayage lives on the semicircle
  have := isFiniteMeasure_bal (t := x) (μ := μ) hR hρR hμB
  have hbalS : ∀ᵐ u ∂(bal x R μ), u ∈ sphere (x : ℂ) R ∩ Hbar := by
    refine mem_ae_iff.2 (bal_null_of_forall ?_ fun z => ?_)
    · exact (isClosed_sphere.measurableSet.inter isClosed_Hbar.measurableSet).compl
    · exact mem_ae_iff.1 (ae_halfDiscPoisson_mem hR z)
  have hbuniv : (bal x R μ univ).toReal = (μ univ).toReal := by rw [bal_univ hR hρR hμB]
  have hev : ∀ᶠ k in atTop, radius k < ρ :=
    tendsto_radius_zero_nodeB.eventually (gt_mem_nhds hρ)
  have hstep : ∀ k, radius k < ρ →
      dualCov D V μ (foldedCircle (x : ℂ) (radius k)) =
        dualCov D V (bal x R μ) (halfDiscPoisson x R x) +
          (∫ y, KernelId.fcPot (radius k) (x : ℂ) y ∂μ + 2 * Real.log R * (μ univ).toReal) := by
    intro k hk
    have hν : IsAdmissibleH (foldedCircle (x : ℂ) (radius k)) := isAdmissibleH_fcK x k
    have := hν.1
    have hνK : foldedCircle (x : ℂ) (radius k) (closedBall (x : ℂ) ρ ∩ Hbar)ᶜ = 0 :=
      compl_null_of_sub_sh (fun y hy => ⟨closedBall_subset_closedBall hk.le hy.1, hy.2⟩)
        (foldedCircle_compl_eq_zero hxH (radius_pos k).le)
    have hνB : foldedCircle (x : ℂ) (radius k) (closedBall (x : ℂ) ρ)ᶜ = 0 :=
      compl_null_of_sub_sh inter_subset_left hνK
    have hνS : foldedCircle (x : ℂ) (radius k) (CircleFubini.ballH (|x| + R))ᶜ = 0 :=
      compl_null_of_sub_sh (subset_ballH_sh hρR.le) hνK
    obtain ⟨C, hC, hνP⟩ := hν.2.2
    have hbalν : bal x R (foldedCircle (x : ℂ) (radius k)) = halfDiscPoisson x R x :=
      bind_foldedCircle_halfDiscPoisson hR (radius_pos k) (by simp; linarith)
    rw [hcov _ hν hνB, hbalν,
      kernelCov_halfDiscGreen hR hρR hμB le_rfl hμS hνS hC.ne hνP,
      PalmFree.kernelCov_fc_right' μ _ (radius_pos k),
      PalmFree.kernelCov_fc_right' _ _ (radius_pos k)]
    have hc : ∫ y, KernelId.fcPot (radius k) (x : ℂ) y ∂(bal x R μ) =
        ∫ _y, (-2 * Real.log R) ∂(bal x R μ) := by
      refine integral_congr_ae ?_
      filter_upwards [hbalS] with u hu
      exact fcPot_of_mem_sphere_sh (hk.trans hρR).le hu.1
    rw [hc, integral_const, smul_eq_mul, measureReal_def, hbuniv]
    ring
  have hlim : Tendsto (fun k => dualCov D V μ (foldedCircle (x : ℂ) (radius k))) atTop
      (𝓝 (dualCov D V (bal x R μ) (halfDiscPoisson x R x) +
        (∫ y, neumannH (x : ℂ) y ∂μ + 2 * Real.log R * (μ univ).toReal))) := by
    refine (tendsto_const_nhds.add
      ((PalmFree.tendsto_integral_fcPot hμ x).add_const _)).congr' ?_
    filter_upwards [hev] with k hk
    exact (hstep k hk).symm
  rw [← hharm]
  exact hlim.limUnder_eq

theorem neumannH_ofReal_add_sh (x : ℝ) (w : ℂ) :
    neumannH (x : ℂ) (w + x) = 2 * -Real.log ‖w‖ := by
  have h := S5.FieldLaw.Raw.neumannH_add_real 0 w x
  rw [zero_add] at h
  rw [h]
  simp only [neumannH, zero_sub, norm_neg, Complex.norm_conj]
  ring

/-- **`Prop16PalmShiftHarmStmt`**: near the free-arc point `x`, the Palm shift is
`γ(−log‖· − x‖)` plus a function whose `foldH`-composition is harmonic. -/
theorem prop16PalmShiftHarmStmt_holds : Prop16PalmShiftHarmStmt := by
  intro γ D c d x _ _ hgeo hx
  obtain ⟨R, hR, hsub⟩ := hgeo.2.2.2.2.2.2 x hx
  have hρ : 0 < R / 2 := half_pos hR
  have hρR : R / 2 < R := half_lt_self hR
  set e := rieszVec D (mixedSpace D (realSet (Icc c d))) (halfDiscPoisson x R x) with hedef
  set f : ℂ → ℝ := fun y => ⟪mixCurve D c d x R (R / 2) y, e⟫ with hfdef
  have hfc : Continuous f :=
    (continuous_mixCurve hgeo hx hρ hρR hsub).inner continuous_const
  obtain ⟨L, B, -, hB0, -, hB⟩ := exists_lip_mixCurve hgeo hx hρ hρR hsub
  refine ⟨R / 2, hρ, fun z hz => hsub ⟨ball_subset_ball hρR.le hz.1, hz.2⟩,
    fun w => (γ / 2) * (f (w + x) + 2 * Real.log R), ?_, ?_⟩
  · intro z hz
    have hzx : z + (x : ℂ) ∈ ball (x : ℂ) (R / 2) := by
      rw [mem_ball, dist_eq_norm, add_sub_cancel_right]
      simpa [mem_ball, dist_eq_norm] using hz
    have h1 : InnerProductSpace.HarmonicAt (fun w => f (foldH w)) (z + x) :=
      harmonicOnNhd_inner_mixCurve hgeo hx hρ hρR hsub e (z + x) hzx
    have h2 := harmonicAt_comp_add_const_mm h1
    have h3 := (h2.add (InnerProductSpace.harmonicAt_const (2 * Real.log R))).const_smul (c := γ / 2)
    convert h3 using 1
    funext w
    simp only [Pi.smul_apply, Pi.add_apply, smul_eq_mul, foldH_add_real_mm]
  · intro μ hμ hμB
    have := hμ.1
    have hμ' := S5.FieldLaw.Raw.isAdmissibleH_map_add_real hμ x
    have hμ'B : μ.map (· + (x : ℂ)) (closedBall (x : ℂ) (R / 2))ᶜ = 0 := by
      rw [map_add_real_apply_mm μ x isClosed_closedBall.measurableSet.compl, preimage_compl,
        preimage_closedBall_add_mm]
      exact hμB
    have hemb := measurableEmbedding_addRight (x : ℂ)
    rw [mixedGreenSample_halfDisc_sh hgeo hx hρ hρR hsub hμ' hμ'B, hemb.integral_map,
      hemb.integral_map, Measure.map_apply (measurable_add_const _) MeasurableSet.univ,
      preimage_univ]
    simp only [neumannH_ofReal_add_sh]
    have hL : Integrable (fun w : ℂ => Real.log ‖w‖) μ := by
      simpa using PalmFree.integrable_log_norm_sub hμ 0
    have hF : Integrable (fun w => f (w + x)) μ := by
      refine Integrable.mono' (integrable_const (B * ‖e‖))
        (hfc.comp (continuous_id.add continuous_const)).aestronglyMeasurable
        (ae_of_all _ fun w => ?_)
      rw [Real.norm_eq_abs]
      exact (abs_real_inner_le_norm _ _).trans
        (mul_le_mul_of_nonneg_right (hB _) (norm_nonneg _))
    have e1 : ∫ w, (2 * -Real.log ‖w‖) ∂μ = -(2 * ∫ w, Real.log ‖w‖ ∂μ) := by
      rw [integral_const_mul, integral_neg]; ring
    have e2 : ∫ w, (γ * -Real.log ‖w‖ + (γ / 2) * (f (w + x) + 2 * Real.log R)) ∂μ =
        -(γ * ∫ w, Real.log ‖w‖ ∂μ) +
          (γ / 2) * (∫ w, f (w + x) ∂μ + (μ univ).toReal * (2 * Real.log R)) := by
      have i1 : Integrable (fun w : ℂ => γ * -Real.log ‖w‖) μ := hL.neg.const_mul γ
      have i2 : Integrable (fun w => (γ / 2) * (f (w + x) + 2 * Real.log R)) μ :=
        (hF.add (integrable_const _)).const_mul _
      have i3 : Integrable (fun _ : ℂ => 2 * Real.log R) μ := integrable_const _
      rw [integral_add i1 i2,
        integral_const_mul, integral_const_mul, integral_neg,
        integral_add hF i3, integral_const, smul_eq_mul, measureReal_def]
      ring
    rw [e1, e2]
    ring

end Prop16Asm

end QuantumZipper
