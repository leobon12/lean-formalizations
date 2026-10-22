import HigherDimLQGMetric.Trunc.Main
import HigherDimLQGMetric.ConvField.JointMain
import HigherDimLQGMetric.Weak.DetLFPPWeylUpper
import HigherDimLQGMetric.Weak.DetLFPPMetric
import HigherDimLFPP.Paths.Compare

/-!
# LFPP comparison for the truncated field

The Weyl identity is exact whenever the full convolution is continuous.  On a
fixed internal domain the uniform field error gives a two-sided comparison.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set Metric Filter Topology

namespace HigherDimLQGMetric

open HigherDimLFPP (Rd)

variable {d : ℕ} {κ : Rd d → ℝ}

theorem l2c_continuous_truncMollify (hd : 2 ≤ d)
    (hκ : HigherDimLFPP.IsLFPPKernel κ) {ε : ℝ} (hε : 0 < ε)
    (h : DistRd d) : Continuous (truncMollify κ ε h) := by
  have hjoint := l2c_continuousOn_truncMollify hd hκ h
  have hmap : Continuous (fun z : Rd d => (ε, z)) :=
    continuous_const.prodMk continuous_id
  have hmem : ∀ z : Rd d, (ε, z) ∈ Ioi (0 : ℝ) ×ˢ univ :=
    fun _ => ⟨hε, mem_univ _⟩
  exact continuousOn_univ.mp
    (hjoint.comp hmap.continuousOn (fun z _ => hmem z))

theorem l2c_fieldLfpp_eq_lfppDist (ξ : ℝ) (ε : ℝ) (h : DistRd d)
    (hc : Continuous (convMollify κ ε h)) (z w : Rd d) :
    fieldLfpp ξ (convMollify κ ε h) (z, w) = lfppDist κ ξ ε h (z, w) := by
  rw [fieldLfpp_eq_lfppDistOn hc]
  rfl

theorem l2c_weylLfpp (hd : 2 ≤ d)
    (hκ : HigherDimLFPP.IsLFPPKernel κ) (ξ : ℝ) {ε : ℝ} (hε : 0 < ε)
    (h : DistRd d) (hc : Continuous (convMollify κ ε h))
    (z w : Rd d) :
    weylScale ξ
        ⟨fun x => truncMollify κ ε h x - convMollify κ ε h x,
          (l2c_continuous_truncMollify hd hκ hε h).sub hc⟩
        (fieldLfppMetric ξ ⟨_, hc⟩) z w =
      fieldLfppE ξ (truncMollify κ ε h) z w := by
  let φ : C(Rd d, ℝ) := ⟨_, hc⟩
  let g : C(Rd d, ℝ) :=
    ⟨fun x => truncMollify κ ε h x - convMollify κ ε h x,
      (l2c_continuous_truncMollify hd hκ hε h).sub hc⟩
  have hsum : ((⇑φ : Rd d → ℝ) + ⇑g) = truncMollify κ ε h := by
    funext x
    simp only [Pi.add_apply]
    dsimp [φ, g]
    ring
  change weylScale ξ g (fieldLfppMetric ξ φ) z w = _
  rw [← hsum]
  exact le_antisymm (weylScale_le_fieldLfppE φ.continuous g z w)
    (fieldLfppE_le_weylScale φ.continuous g z w)

theorem l2c_internalLfpp_le_exp_mul (hd : 2 ≤ d)
    (hκ : HigherDimLFPP.IsLFPPKernel κ) (ξ : ℝ) {ε : ℝ} (hε : 0 < ε)
    (h : DistRd d) (hc : Continuous (convMollify κ ε h))
    (V : Set (Rd d)) (M : ℝ)
    (hM : ∀ z ∈ V, |convMollify κ ε h z - truncMollify κ ε h z| ≤ M)
    (z w : Rd d) :
    HigherDimLFPP.lfppDistOn ξ (truncMollify κ ε h) V z w ≤
      Real.exp (|ξ| * M) * HigherDimLFPP.lfppDistOn ξ (convMollify κ ε h) V z w ∧
    HigherDimLFPP.lfppDistOn ξ (convMollify κ ε h) V z w ≤
      Real.exp (|ξ| * M) * HigherDimLFPP.lfppDistOn ξ (truncMollify κ ε h) V z w := by
  have ht := l2c_continuous_truncMollify hd hκ hε h
  constructor
  · apply HigherDimLFPP.lfppDistOn_le_exp_mul ht hc
    intro x hx
    rw [abs_sub_comm]
    exact hM x hx
  · exact HigherDimLFPP.lfppDistOn_le_exp_mul hc ht hM

theorem l2c_internalLfpp_log_comparison (hd : 2 ≤ d)
    (hκ : HigherDimLFPP.IsLFPPKernel κ) (ξ : ℝ) {ε : ℝ} (hε : 0 < ε)
    (h : DistRd d) (hc : Continuous (convMollify κ ε h))
    (V : Set (Rd d)) (M : ℝ)
    (hM : ∀ z ∈ V, |convMollify κ ε h z - truncMollify κ ε h z| ≤ M)
    (z w : Rd d) (hz : z ∈ V) :
    |Real.log (HigherDimLFPP.lfppDistOn ξ (convMollify κ ε h) V z w) -
      Real.log (HigherDimLFPP.lfppDistOn ξ (truncMollify κ ε h) V z w)| ≤
        |ξ| * M := by
  exact HigherDimLFPP.abs_log_lfppDistOn_sub_le hc
    (l2c_continuous_truncMollify hd hκ hε h) hz hM

set_option maxHeartbeats 1000000 in
theorem l2c_ae_internalLfpp_log_ratio (d : ℕ) (hd : 2 ≤ d)
    (κ : Rd d → ℝ) (hκ : HigherDimLFPP.IsLFPPKernel κ) (ξ : ℝ)
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (h : Ω → DistRd d) (hh : IsNormalizedLGF h P) :
    ∀ᵐ ω ∂P, ∀ R : ℝ, 0 < R →
      TendstoUniformlyOn
        (fun ε (p : Rd d × Rd d) =>
          Real.log (HigherDimLFPP.lfppDistOn ξ (convMollify κ ε (h ω))
            (closedBall (0 : Rd d) R) p.1 p.2) -
          Real.log (HigherDimLFPP.lfppDistOn ξ (truncMollify κ ε (h ω))
            (closedBall (0 : Rd d) R) p.1 p.2))
        0 (𝓝[>] 0)
        (closedBall (0 : Rd d) R ×ˢ closedBall (0 : Rd d) R) := by
  have hmain := l2c_trunc d hd κ hκ P h hh
  filter_upwards [l2b_ae_convMollify_continuousOn d hd κ hκ P h hh,
    hmain] with ω hjoint hfield
  intro R hR
  rw [Metric.tendstoUniformlyOn_iff]
  intro δ hδ
  have hη : 0 < δ / (|ξ| + 1) :=
    div_pos hδ (by positivity)
  have hev := (Metric.tendstoUniformlyOn_iff.1 (hfield R hR))
    (δ / (|ξ| + 1)) hη
  have hscale : |ξ| * (δ / (|ξ| + 1)) < δ := by
    have hp : 0 < |ξ| + 1 := by positivity
    apply (mul_lt_mul_iff_of_pos_right hp).mp
    field_simp
    nlinarith [abs_nonneg ξ]
  filter_upwards [hev, Ioo_mem_nhdsGT (by norm_num : (0 : ℝ) < 1)]
    with ε hε hεrange p hp
  have hc : Continuous (convMollify κ ε (h ω)) := by
    have hmap : Continuous (fun z : Rd d => (ε, z)) :=
      continuous_const.prodMk continuous_id
    have hf := hjoint.comp_continuous hmap (fun _ => ⟨hεrange.1, mem_univ _⟩)
    simpa only [Function.comp_def, Prod.fst, Prod.snd] using hf
  have hM : ∀ z ∈ closedBall (0 : Rd d) R,
      |convMollify κ ε (h ω) z - truncMollify κ ε (h ω) z| ≤
        δ / (|ξ| + 1) := by
    intro z hz
    simpa only [Real.dist_eq, Pi.zero_apply, abs_sub_comm, sub_zero] using
      (hε z hz).le
  have hb := l2c_internalLfpp_log_comparison hd hκ ξ hεrange.1 (h ω) hc
    (closedBall (0 : Rd d) R) (δ / (|ξ| + 1)) hM p.1 p.2 hp.1
  simpa only [Real.dist_eq, Pi.zero_apply, zero_sub, abs_neg] using
    lt_of_le_of_lt hb hscale

set_option maxHeartbeats 1000000 in
/-- DFGPS Lemma 2.1's two-sided multiplicative form for internal LFPP distances. -/
theorem l2c_ae_internalLfpp_mul_ratio (d : ℕ) (hd : 2 ≤ d)
    (κ : Rd d → ℝ) (hκ : HigherDimLFPP.IsLFPPKernel κ) (ξ : ℝ)
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (h : Ω → DistRd d) (hh : IsNormalizedLGF h P) :
    ∀ᵐ ω ∂P, ∀ R : ℝ, 0 < R → ∀ c : ℝ, 1 < c →
      ∀ᶠ ε in 𝓝[>] (0 : ℝ), ∀ z w : Rd d,
        HigherDimLFPP.lfppDistOn ξ (truncMollify κ ε (h ω))
          (closedBall (0 : Rd d) R) z w ≤
          c * HigherDimLFPP.lfppDistOn ξ (convMollify κ ε (h ω))
            (closedBall (0 : Rd d) R) z w ∧
        HigherDimLFPP.lfppDistOn ξ (convMollify κ ε (h ω))
          (closedBall (0 : Rd d) R) z w ≤
          c * HigherDimLFPP.lfppDistOn ξ (truncMollify κ ε (h ω))
            (closedBall (0 : Rd d) R) z w := by
  have hmain := l2c_trunc d hd κ hκ P h hh
  filter_upwards [l2b_ae_convMollify_continuousOn d hd κ hκ P h hh,
    hmain] with ω hjoint hfield
  intro R hR c hc
  let δ : ℝ := Real.log c / (|ξ| + 1)
  have hδ : 0 < δ := div_pos (Real.log_pos hc) (by positivity)
  have hle : Real.exp (|ξ| * δ) ≤ c := by
    have haux : |ξ| * δ ≤ Real.log c := by
      dsimp [δ]
      rw [mul_div_assoc', div_le_iff₀ (by positivity)]
      nlinarith [abs_nonneg ξ, Real.log_pos hc]
    exact (Real.exp_le_exp.mpr haux).trans_eq (Real.exp_log (by linarith))
  have hev := (Metric.tendstoUniformlyOn_iff.1 (hfield R hR)) δ hδ
  filter_upwards [hev, Ioo_mem_nhdsGT (by norm_num : (0 : ℝ) < 1)]
    with ε hε hεrange z w
  have hcconv : Continuous (convMollify κ ε (h ω)) := by
    have hmap : Continuous (fun x : Rd d => (ε, x)) :=
      continuous_const.prodMk continuous_id
    have hf := hjoint.comp_continuous hmap (fun _ => ⟨hεrange.1, mem_univ _⟩)
    simpa only [Function.comp_def, Prod.fst, Prod.snd] using hf
  have hM : ∀ x ∈ closedBall (0 : Rd d) R,
      |convMollify κ ε (h ω) x - truncMollify κ ε (h ω) x| ≤ δ := by
    intro x hx
    simpa only [Real.dist_eq, Pi.zero_apply, abs_sub_comm, sub_zero] using (hε x hx).le
  obtain ⟨h1, h2⟩ := l2c_internalLfpp_le_exp_mul hd hκ ξ hεrange.1
    (h ω) hcconv (closedBall (0 : Rd d) R) δ hM z w
  constructor
  · exact h1.trans (mul_le_mul_of_nonneg_right hle
      (HigherDimLFPP.lfppDistOn_nonneg ξ _ _ _ _))
  · exact h2.trans (mul_le_mul_of_nonneg_right hle
      (HigherDimLFPP.lfppDistOn_nonneg ξ _ _ _ _))

end HigherDimLQGMetric
