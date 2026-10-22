import HigherDimLQGContinuity.Fatou.Envelope

/-!
# Fatou passage for the buffered upper modulus

The smaller cutoff domain gives a bound in the larger continuum domain by lower
semicontinuity of internal metrics.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 800000

noncomputable section

open MeasureTheory Filter Topology Set Metric
open scoped ENNReal

namespace HigherDimLQGContinuity

open HigherDimLQGMetric
open HigherDimLFPP (Rd)

/-- Convert a real LFPP path bound into an internal-metric bound after median scaling. -/
theorem fatou_scaled_internal_le {d : ℕ} (ξ : ℝ) (φ : C(Rd d, ℝ))
    {a H s σ : ℝ} (ha : 0 < a)
    {V : Set (Rd d)} (hVopen : IsOpen V) (hVconn : IsPreconnected V)
    {u v : Rd d} (hu : u ∈ V) (hv : v ∈ V)
    (hcost : HigherDimLFPP.lfppDistOn ξ φ V u v ≤ a * H * s ^ σ) :
    ((fieldLfppMetric ξ φ).smul a⁻¹ (inv_pos.mpr ha)).internal V u v ≤
      ENNReal.ofReal (H * s ^ σ) := by
  calc
    ((fieldLfppMetric ξ φ).smul a⁻¹ (inv_pos.mpr ha)).internal V u v =
        ENNReal.ofReal a⁻¹ * (fieldLfppMetric ξ φ).internal V u v :=
      ContMetric.internal_smul (inv_pos.mpr ha) _ _ _ _
    _ ≤ ENNReal.ofReal a⁻¹ *
        ENNReal.ofReal (HigherDimLFPP.lfppDistOn ξ φ V u v) := by
      gcongr
      exact fatou_field_internal_le_lfppDistOn ξ φ hVopen hVconn hu hv
    _ ≤ ENNReal.ofReal a⁻¹ * ENNReal.ofReal (a * H * s ^ σ) := by
      gcongr
    _ = ENNReal.ofReal (H * s ^ σ) := by
      rw [← ENNReal.ofReal_mul (inv_nonneg.mpr ha.le)]
      congr 1
      field_simp

theorem fatou_internalDiam_smul {d : ℕ} (D : ContMetric d) {a : ℝ} (ha : 0 < a)
    (A U : Set (Rd d)) :
    internalDiamRd (D.smul a ha) A U = ENNReal.ofReal a * internalDiamRd D A U := by
  unfold internalDiamRd
  simp_rw [ContMetric.internal_smul ha]
  simp only [ENNReal.mul_iSup]

/-- The convolution upper-moment input passes to a canonical metric before the
mean-log renormalization. The `3s/2` cutoff domain provides the necessary buffer. -/
theorem fatou_upper_of_conv {d : ℕ} (hd : 3 ≤ d) {κ : Rd d → ℝ}
    (hκ : HigherDimLFPP.IsLFPPKernel κ) (hC1 : ConvUpperMomentShape d κ)
    {b μ σ p : ℝ} (hb : 0 < b) (hμ : 0 < μ) (hμ1 : μ ≤ 1)
    (hσ : 0 < σ) (hσμ : σ < μ) (hp : 0 < p)
    (hpb : 32 * p * b ≤ Real.sqrt (2 * d)) :
    ∃ C A : ℝ, ∀ ξ : ℝ, UHyp d κ b μ ξ → ∀ D : DistRd d → ContMetric d,
      IsStrongExpMetric d ξ (distExp d ξ) D →
      TendstoInProbLU (normLGFLaw d)
        (fun ε g => (aEps κ ξ ε)⁻¹ • lfppDist κ ξ ε g) (𝓝[>] 0)
        (fun g => (D g).1) →
      ∀ R : ℝ, 1 ≤ R → ∃ H : DistRd d → ℝ,
        Measurable H ∧ (∀ g, 1 ≤ H g) ∧
        (∫⁻ g, ENNReal.ofReal (H g ^ p) ∂(normLGFLaw d) ≤
          ENNReal.ofReal (C * (1 + R) ^ A)) ∧
        ∀ᵐ g ∂(normLGFLaw d), ∀ z ∈ closedBall (0 : Rd d) R,
          ∀ s ∈ Ioc (0 : ℝ) 1,
            internalDiamRd (D g) (ball z s) (ball z (2 * s)) ≤
              ENNReal.ofReal (H g * s ^ σ) := by
  let _ : IsProbabilityMeasure (normLGFLaw d) :=
    (normLGFLaw_spec_holds d (by omega : 2 ≤ d)).1
  have hn : IsNormalizedLGF id (normLGFLaw d) :=
    (normLGFLaw_spec_holds d (by omega : 2 ≤ d)).2.1
  obtain ⟨C, A, hC⟩ := hC1 b μ hb hμ hμ1 σ hσ hσμ p hp hpb
  refine ⟨C, A, fun ξ hξ D hD hconv R hR => ?_⟩
  obtain ⟨ns, _, hae⟩ := fatou_exists_subseq hd hκ D hconv
  have happrox (k : ℕ) : ∃ Hr : DistRd d → ℝ,
      Measurable Hr ∧ (∀ g, 1 ≤ Hr g) ∧
      (∫⁻ g, ENNReal.ofReal (Hr g ^ p) ∂(normLGFLaw d) ≤
        ENNReal.ofReal (C * (1 + R) ^ A)) ∧
      ∀ᵐ g ∂(normLGFLaw d), ∀ z ∈ closedBall (0 : Rd d) R,
        ∀ s ∈ Ioc (0 : ℝ) 1, ∀ u ∈ ball z s, ∀ v ∈ ball z s,
          HigherDimLFPP.lfppDistOn ξ (convMollify κ (fatouEps (ns k)) g)
            (ball z (3 / 2 * s)) u v ≤
              aEps κ ξ (fatouEps (ns k)) * Hr g * s ^ σ := by
    exact hC ξ hξ (fatouEps (ns k)) ⟨fatouEps_pos _, fatouEps_lt_one _⟩
      (normLGFLaw d) id hn R hR
  choose Hk hkm hk1 hkmom hkpt using happrox
  obtain ⟨H, hHm, hH1, hHmom, hHlim⟩ :=
    fatou_real_envelope (normLGFLaw d) hp Hk hkm hk1 hkmom
  refine ⟨H, hHm, hH1, hHmom, ?_⟩
  have hlen : ∀ᵐ g ∂(normLGFLaw d), (D g).IsLength :=
    hD.length (normLGFLaw d) id hn.1.isLGFPlusCont
  have hcont : ∀ᵐ g ∂(normLGFLaw d),
      ∀ k, Continuous (convMollify κ (fatouEps (ns k)) g) := by
    exact ae_all_iff.mpr fun k => l10a_ae_continuous_convMollify
      (by omega : 2 ≤ d) κ hκ (normLGFLaw d) id hn (fatouEps_pos (ns k))
  have hpt : ∀ᵐ g ∂(normLGFLaw d),
      ∀ k, ∀ z ∈ closedBall (0 : Rd d) R, ∀ s ∈ Ioc (0 : ℝ) 1,
        ∀ u ∈ ball z s, ∀ v ∈ ball z s,
          HigherDimLFPP.lfppDistOn ξ (convMollify κ (fatouEps (ns k)) g)
            (ball z (3 / 2 * s)) u v ≤
              aEps κ ξ (fatouEps (ns k)) * Hk k g * s ^ σ :=
    ae_all_iff.mpr hkpt
  filter_upwards [hae, hlen, hcont, hpt, hHlim] with g hg hgl hc hpnt hlim
  intro z hz s hs
  unfold internalDiamRd
  refine iSup_le fun u => iSup_le fun hu => iSup_le fun v => iSup_le fun hv => ?_
  let W : TopologicalSpace.Opens (Rd d) := ⟨ball z (3 / 2 * s), isOpen_ball⟩
  let U : TopologicalSpace.Opens (Rd d) := ⟨ball z (2 * s), isOpen_ball⟩
  have hs0 : 0 < s := hs.1
  have hrad : 3 / 2 * s < 2 * s := by nlinarith
  have hsu : s ≤ 3 / 2 * s := by nlinarith
  have huW : u ∈ W := (ball_subset_ball hsu) hu
  have hvW : v ∈ W := (ball_subset_ball hsu) hv
  have hWc : IsPreconnected (W : Set (Rd d)) := (convex_ball z _).isPreconnected
  have hK : IsCompact (closure (W : Set (Rd d))) :=
    IsCompact.of_isClosed_subset (isCompact_closedBall z _) isClosed_closure
      closure_ball_subset_closedBall
  have hKU : closure (W : Set (Rd d)) ⊆ U :=
    closure_ball_subset_closedBall.trans (closedBall_subset_ball hrad)
  let Dn : ℕ → ContMetric d := fun k =>
    (fieldLfppMetric ξ ⟨convMollify κ (fatouEps (ns k)) g, hc k⟩).smul
      (aEps κ ξ (fatouEps (ns k)))⁻¹
      (inv_pos.mpr (l6a_aEps_pos (by omega : 2 ≤ d) κ hκ ξ (fatouEps_pos (ns k))))
  have hEq (k : ℕ) : (Dn k).1 =
      toCMapRd ((aEps κ ξ (fatouEps (ns k)))⁻¹ •
        lfppDist κ ξ (fatouEps (ns k)) g) := by
    ext t
    have hf : lfppDist κ ξ (fatouEps (ns k)) g =
        fieldLfpp ξ (convMollify κ (fatouEps (ns k)) g) := by
      funext q
      exact (fieldLfpp_eq_lfppDistOn (hc k) q).symm
    have hscaled : Continuous ((aEps κ ξ (fatouEps (ns k)))⁻¹ •
        lfppDist κ ξ (fatouEps (ns k)) g) := by
      rw [hf]
      exact (continuous_fieldLfpp (hc k)).const_smul _
    rw [toCMapRd_apply_of_continuous hscaled, ContMetric.smul_apply]
    simp only [Pi.smul_apply, smul_eq_mul, fieldLfppMetric_apply, hf]
    rfl
  have hconvDn : Tendsto (fun k => (Dn k).1) atTop (𝓝 (D g).1) := by
    have he : (fun k => (Dn k).1) = fun k => toCMapRd
        ((aEps κ ξ (fatouEps (ns k)))⁻¹ • lfppDist κ ξ (fatouEps (ns k)) g) :=
      funext hEq
    rw [he]
    exact hg
  have hls := l8_internal_liminf_ge_enlarged_domain Dn (D g) hgl
    hconvDn W U hWc hK hKU u v huW hvW
  have hpre (k : ℕ) : (Dn k).internal W u v ≤
      ENNReal.ofReal (Hk k g * s ^ σ) := by
    exact fatou_scaled_internal_le ξ
      (⟨convMollify κ (fatouEps (ns k)) g, hc k⟩ : C(Rd d, ℝ))
      (l6a_aEps_pos (by omega : 2 ≤ d) κ hκ ξ (fatouEps_pos (ns k)))
      isOpen_ball (convex_ball z _).isPreconnected huW hvW
      (hpnt k z hz s hs u hu v hv)
  have hspow : 0 ≤ s ^ σ := Real.rpow_nonneg hs0.le _
  calc
    (D g).internal U u v ≤ liminf (fun k => (Dn k).internal W u v) atTop := hls
    _ ≤ liminf (fun k => ENNReal.ofReal (Hk k g * s ^ σ)) atTop :=
      liminf_le_liminf (Eventually.of_forall hpre)
    _ = liminf (fun k => ENNReal.ofReal (Hk k g) * ENNReal.ofReal (s ^ σ)) atTop := by
      congr 1
      funext k
      exact ENNReal.ofReal_mul (by linarith [hk1 k g])
    _ = (liminf (fun k => ENNReal.ofReal (Hk k g)) atTop) * ENNReal.ofReal (s ^ σ) := by
      rw [ENNReal.liminf_mul_const_of_ne_top ENNReal.ofReal_ne_top]
      exact mul_comm _ _
    _ = ENNReal.ofReal (H g * s ^ σ) := by
      rw [← hlim, ENNReal.ofReal_mul (zero_le_one.trans (hH1 g))]

end HigherDimLQGContinuity
