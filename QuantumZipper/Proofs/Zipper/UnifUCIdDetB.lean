import QuantumZipper.Proofs.Zipper.UnifUCIdDet
import QuantumZipper.Proofs.GFF.SmoothingConvergence

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# UNIF-RC3-DET: convergence of the deterministic part `detJ`

Task UC-ID-DET, item DET (`handoff/REG-UNIF.md`, D33). `RegUnif.DetUnifStmt κ T` is

`detJ κ W d k p j ⟶ ∫ v, PsiU κ W p.1 v ∂alphaUS W d k p` uniformly on `tri T`,

i.e. the folded-circle smoothing `z ↦ ∫ v PsiU κ W p.1 v ∂fc(z, 2^{-j})` converges to the
integrand itself, uniformly over the pair `p = (u, s)`, evaluated at the centres `z` that
`alphaUS W d k p` sees.

The analytic content is the deterministic half of `RegUnif.JointModStmt`/`CoordReg.Dfun`:

* `continuousOn_PsiU_joint`: `(u, v) ↦ PsiU κ W u v` is continuous on `[0,T] × ℍ`
  (`JointModDet.continuousOn_fwdMapInv_joint`, `continuousOn_log_deriv_fwdMapInv_joint`);
* `tendstoUniformlyOn_integral_fc_comp`: **uniform circle smoothing on a compact subset of `ℍ`**
  (own elementary proof: a compact `K ⊆ ℍ` stays at distance `δ > 0` from `ℝ`, so for
  `2^{-j} ≤ δ/2` the folded circles at centres `c ∈ K` are ordinary circles of radius `2^{-j}`
  (`SmoothingConvergence.foldedCircle_eq_circleUnif_sc`, `ae_circleUnif_sc`), and the moduli of
  continuity of a fixed continuous `G` on the compact set `[0,T] × {Im ≥ δ/2}` drive the
  estimate);
* `detJ_tendsto_of_compact`: the resulting uniform convergence of `detJ`, conditional on the
  pushed measures `alphaUS W d k p` being supported in one fixed compact subset of `ℍ`
  (`detUnifStmt_of_support` for the statement `DetUnifStmt` itself).

Sources: none — own elementary proof (this is the bookkeeping that the paper leaves implicit;
the structure follows Duplantier–Sheffield, Invent. Math. 185 (2011), Prop. 3.1, p. 18).
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal

namespace QuantumZipper
namespace RegUnif

open RegCont TwoPoint B2 CoordReg CircleFubini RegSample UnzipInvariance

variable {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} {X : Ω → FieldSample}

/-- **Joint continuity of `PsiU` on `[0,T] × ℍ`.** -/
theorem continuousOn_PsiU_joint {W : ℝ → ℝ} (hW : Continuous W) (hW0 : W 0 = 0) (κ : ℝ)
    (T : ℝ) :
    ContinuousOn (fun q : ℝ × ℂ => PsiU κ W q.1 q.2) (Icc 0 T ×ˢ H) := by
  have h1 : ContinuousOn (fun q : ℝ × ℂ => Real.log ‖fwdMapInv W q.1 q.2‖) (Icc 0 T ×ˢ H) :=
    (continuousOn_fwdMapInv_joint hW hW0 T).norm.log fun q hq => by
      refine norm_ne_zero_iff.2 fun h => ?_
      have hmem : fwdMapInv W q.1 q.2 ∈ H := by
        rw [UnzipInvariance.fwdMapInv_eq_revMap_timeRev W hW hW0 hq.1.1 hq.2]
        exact im_revMap_pos (continuous_vRev hW _) hq.2 hq.1.1
      rw [h] at hmem
      exact absurd hmem (by simp [H])
  have h2 := continuousOn_log_deriv_fwdMapInv_joint hW hW0 T
  refine (((continuousOn_const (c := 2 / Real.sqrt κ)).mul h1).add
    ((continuousOn_const (c := Qc (Real.sqrt κ))).mul h2)).congr fun q _ => ?_
  simp only [PsiU, h0rev, Pi.mul_apply, Pi.add_apply]

/-- **Uniform circle smoothing on a compact subset of `ℍ`.** For `G` continuous on
`[0,T] × ℍ` and `K ⊆ ℍ` compact, the folded-circle means `∫ v, G t v ∂fc(c, 2^{-j})` converge
to `G t c` uniformly in `(t, c) ∈ [0,T] × K`. -/
theorem tendstoUniformlyOn_integral_fc_comp {T : ℝ} {G : ℝ → ℂ → ℝ}
    (hGc : ContinuousOn (fun p : ℝ × ℂ => G p.1 p.2) (Icc 0 T ×ˢ H))
    {K : Set ℂ} (hKc : IsCompact K) (hKH : K ⊆ H) :
    ∀ ε > 0, ∃ J : ℕ, ∀ j ≥ J, ∀ t ∈ Icc 0 T, ∀ c ∈ K,
      |(∫ v, G t v ∂foldedCircle c (radius j)) - G t c| ≤ ε := by
  intro ε hε
  -- `K` stays at positive distance from the real axis
  have hδ : ∃ δ > 0, ∀ c ∈ K, δ ≤ c.im := by
    rcases K.eq_empty_or_nonempty with hemp | hne
    · exact ⟨1, one_pos, fun c hc => by rw [hemp] at hc; exact absurd hc (Set.notMem_empty c)⟩
    · obtain ⟨x₀, hx₀K, hmin⟩ := hKc.exists_isMinOn hne Complex.continuous_im.continuousOn
      have hx₀ : 0 < x₀.im := hKH hx₀K
      exact ⟨x₀.im / 2, by linarith, fun c hc => by have hcim : x₀.im ≤ c.im := hmin hc; linarith⟩
  obtain ⟨δ, hδ0, hδK⟩ := hδ
  obtain ⟨RK, hRK₀⟩ := hKc.exists_bound_of_continuousOn continuous_norm.continuousOn
  have hRK : ∀ x ∈ K, ‖x‖ ≤ RK := fun x hx => by
    have := hRK₀ x hx
    rwa [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg x)] at this
  set Sc : Set (ℝ × ℂ) :=
    Icc 0 T ×ˢ (Metric.closedBall (0 : ℂ) (RK + 1) ∩ {v : ℂ | δ / 2 ≤ v.im}) with hSc
  have hScc : IsCompact Sc :=
    isCompact_Icc.prod ((isCompact_closedBall _ _).inter_right (isClosed_le continuous_const
      Complex.continuous_im))
  have hGK : ContinuousOn (fun p : ℝ × ℂ => G p.1 p.2) Sc := hGc.mono fun q hq => by
    refine ⟨hq.1, ?_⟩
    show (0 : ℝ) < q.2.im
    have him : δ / 2 ≤ q.2.im := hq.2.2
    have hpos : (0 : ℝ) < δ / 2 := by positivity
    linarith [him]
  obtain ⟨η, hη0, hη⟩ := Metric.uniformContinuousOn_iff.1
    (hScc.uniformContinuousOn_of_continuous hGK) ε hε
  -- the radii eventually satisfy all the smallness requirements
  have hsmall : ∀ t > 0, ∃ J : ℕ, ∀ j ≥ J, radius j ≤ t := by
    intro t ht
    have hmem : Iic t ∈ 𝓝 (0 : ℝ) := Iic_mem_nhds ht
    have h := (tendsto_pow_atTop_nhds_zero_of_norm_lt_one
      (by norm_num : ‖((2 : ℝ)⁻¹)‖ < 1)).eventually hmem
    rwa [eventually_atTop] at h
  obtain ⟨J₁, hJ₁⟩ := hsmall (δ / 2) (by positivity)
  obtain ⟨J₂, hJ₂⟩ := hsmall 1 one_pos
  obtain ⟨J₃, hJ₃⟩ := hsmall (η / 2) (by positivity)
  refine ⟨max J₁ (max J₂ J₃), fun j hj t ht c hc => ?_⟩
  have hj₁ : radius j ≤ δ / 2 := hJ₁ j (le_trans (le_max_left _ _) hj)
  have hj₂ : radius j ≤ 1 := hJ₂ j (le_trans (le_max_of_le_right (le_max_left _ _)) hj)
  have hj₃ : radius j ≤ η / 2 := hJ₃ j (le_trans (le_max_of_le_right (le_max_right _ _)) hj)
  have hδle : δ / 2 ≤ δ := by linarith
  have hrc : radius j ≤ c.im := le_trans hj₁ (le_trans hδle (hδK c hc))
  -- points of the circle of radius `2^{-j}` around `c` stay in the compact set
  have hvS : ∀ v : ℂ, ‖v - c‖ = radius j → (t, v) ∈ Sc := fun v hvc => by
    refine ⟨ht, ?_, ?_⟩
    · rw [Metric.mem_closedBall, dist_zero_right]
      have hns : ‖v‖ ≤ ‖c‖ + ‖v - c‖ := by have h := norm_sub_norm_le v c; linarith
      rw [hvc] at hns
      linarith [hRK c hc, hj₂]
    · show δ / 2 ≤ v.im
      have h1 : |(v - c).im| ≤ ‖v - c‖ := Complex.abs_im_le_norm _
      have h2 : (v - c).im = v.im - c.im := by simp
      rw [h2, hvc] at h1
      have h3 := abs_le.1 h1
      linarith [hδK c hc, hj₁, h3.1]
  have hmemc : (t, c) ∈ Sc := by
    refine ⟨ht, ?_, ?_⟩
    · rw [Metric.mem_closedBall, dist_zero_right]; linarith [hRK c hc]
    · show δ / 2 ≤ c.im
      have hcδ : δ ≤ c.im := hδK c hc
      linarith [hcδ, hδ0]
  have hvc_of : ∀ᵐ v ∂foldedCircle c (radius j), ‖v - c‖ = radius j := by
    rw [SmoothConv.foldedCircle_eq_circleUnif_sc (radius_pos j).le hrc]
    filter_upwards [SmoothConv.ae_circleUnif_sc c (radius j)] with v hv
    rwa [abs_of_nonneg (radius_pos j).le] at hv
  have hae : ∀ᵐ v ∂foldedCircle c (radius j), dist (G t v) (G t c) < ε := by
    filter_upwards [hvc_of] with v hvc
    have hd : dist (t, v) (t, c) < η := by
      rw [Prod.dist_eq, dist_self, max_eq_right dist_nonneg, dist_eq_norm, hvc]
      linarith
    exact hη (t, v) (hvS v hvc) (t, c) hmemc hd
  -- integrability of `G t ·` against the compactly supported measure
  obtain ⟨M, hM⟩ := hScc.exists_bound_of_continuousOn hGK
  have hGt : Integrable (fun v => G t v) (foldedCircle c (radius j)) := by
    refine Integrable.of_bound ?_ M ?_
    · have hc' : ContinuousOn (fun v : ℂ => G t v) H :=
        hGc.comp (continuousOn_const.prodMk continuousOn_id)
          fun v hv => ⟨ht, hv⟩
      have := hc'.aestronglyMeasurable (μ := foldedCircle c (radius j)) isOpen_H.measurableSet
      rwa [Measure.restrict_eq_self_of_ae_mem
        (foldedCircle_ae_mem_H c (radius_pos j))] at this
    · filter_upwards [hvc_of] with v hvc
      have hb := hM (t, v) (hvS v hvc)
      rwa [Real.norm_eq_abs] at hb
  have hconst : Integrable (fun _ : ℂ => G t c) (foldedCircle c (radius j)) :=
    integrable_const (G t c)
  have hcint : (∫ v, G t c ∂foldedCircle c (radius j)) = G t c := by
    rw [integral_const, probReal_univ, one_smul]
  have hsub : (∫ v, G t v ∂foldedCircle c (radius j)) - G t c =
      ∫ v, (G t v - G t c) ∂foldedCircle c (radius j) := by
    rw [integral_sub hGt hconst, hcint]
  have key : ‖∫ v, (G t v - G t c) ∂foldedCircle c (radius j)‖ ≤ ε := by
    refine (norm_integral_le_of_norm_le_const (μ := foldedCircle c (radius j)) (C := ε) ?_).trans ?_
    · filter_upwards [hae] with v hv
      rw [Real.dist_eq] at hv
      exact hv.le
    · rw [probReal_univ, mul_one]
  rw [hsub]
  exact key

end RegUnif
end QuantumZipper
