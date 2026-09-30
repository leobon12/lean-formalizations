import QuantumZipper.Proofs.GFF.K3.MixedM7D2
import QuantumZipper.Proofs.GFF.K3.MixedM7C2
import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls

/-!
# K3-mixed M7-a3, half-disc covariance, step D3: cutting off the endpoints

Every `f` in the half-disc mixed space `V₀ = mixedSpace U (realSet (Icc (t − r) (t + r)))`
vanishes on a neighbourhood of the *open* semicircle and at its endpoints `t ± r`. Multiplying
by `η_δ = 1 − b_δ(· − (t − r)) − b_δ(· − (t + r))` (scaled bumps of radius `δ`) gives a test
function vanishing near the *closed* semicircle, equal to `f` on `closedBall t r'`, whose energy
exceeds `E_U(f)` by `O(δ²)`: `|f| ≤ L δ` on the `δ`-balls at the endpoints (`f(t ± r) = 0`,
`f` Lipschitz) while `‖∇b_δ‖ ≤ M/δ`. Letting `δ → 0` in D2 gives the reflection upper bound
for all of `V₀` (`sq_integral_le_halfDisc_m7d`).

Own elementary argument (a Lipschitz function vanishing at a point is cut off there at energy
cost `O(δ²)`; no capacity argument is needed).
-/

noncomputable section

open MeasureTheory Set Metric Filter
open scoped Real Topology ComplexConjugate

namespace QuantumZipper.K3

/-- The unit bump: `1` on `closedBall 0 (1/2)`, `0` off `ball 0 1`. -/
def bump1M7d : ContDiffBump (0 : ℂ) := ⟨1 / 2, 1, by norm_num, by norm_num⟩

/-- The bump at `p` of radius `δ`. -/
def sBump (p : ℂ) (δ : ℝ) (z : ℂ) : ℝ := bump1M7d (δ⁻¹ • (z - p))

theorem contDiff_sBump_m7d (p : ℂ) (δ : ℝ) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (sBump p δ) :=
  bump1M7d.contDiff.comp ((contDiff_id.sub contDiff_const).const_smul δ⁻¹)

theorem norm_smul_sub_m7d {δ : ℝ} (hδ : 0 < δ) (z p : ℂ) :
    ‖δ⁻¹ • (z - p)‖ = ‖z - p‖ / δ := by
  rw [norm_smul, Real.norm_of_nonneg (inv_nonneg.2 hδ.le), inv_mul_eq_div]

theorem sBump_eq_one_m7d {δ : ℝ} (hδ : 0 < δ) {p z : ℂ} (h : ‖z - p‖ ≤ δ / 2) :
    sBump p δ z = 1 := by
  refine bump1M7d.one_of_mem_closedBall ?_
  show δ⁻¹ • (z - p) ∈ closedBall (0 : ℂ) (1 / 2)
  rw [mem_closedBall_zero_iff, norm_smul_sub_m7d hδ, div_le_iff₀ hδ]; linarith

theorem sBump_eq_zero_m7d {δ : ℝ} (hδ : 0 < δ) {p z : ℂ} (h : δ ≤ ‖z - p‖) :
    sBump p δ z = 0 := by
  refine bump1M7d.zero_of_le_dist ?_
  show (1 : ℝ) ≤ dist (δ⁻¹ • (z - p)) 0
  rw [dist_zero_right, norm_smul_sub_m7d hδ, le_div_iff₀ hδ]; linarith

theorem sBump_nonneg_m7d (p : ℂ) (δ : ℝ) (z : ℂ) : 0 ≤ sBump p δ z := bump1M7d.nonneg

theorem sBump_le_one_m7d (p : ℂ) (δ : ℝ) (z : ℂ) : sBump p δ z ≤ 1 := bump1M7d.le_one

theorem exists_fderiv_sBump_le_m7d :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ p : ℂ, ∀ δ : ℝ, 0 < δ → ∀ z, ‖fderiv ℝ (sBump p δ) z‖ ≤ M / δ := by
  have hc : Continuous (fderiv ℝ (bump1M7d : ℂ → ℝ)) :=
    (bump1M7d.contDiff (n := (⊤ : ℕ∞))).continuous_fderiv (by simp)
  obtain ⟨M, hM⟩ := hc.bounded_above_of_compact_support
    (bump1M7d.hasCompactSupport.fderiv (𝕜 := ℝ))
  refine ⟨max M 0, le_max_right _ _, fun p δ hδ z => ?_⟩
  have hd : HasFDerivAt (sBump p δ) ((fderiv ℝ (bump1M7d : ℂ → ℝ) (δ⁻¹ • (z - p))).comp
      (δ⁻¹ • ContinuousLinearMap.id ℝ ℂ)) z :=
    ((bump1M7d.contDiff (n := 1)).differentiable (by simp) _).hasFDerivAt.comp z
      (((hasFDerivAt_id z).sub_const p).const_smul δ⁻¹)
  rw [hd.fderiv]
  refine (ContinuousLinearMap.opNorm_comp_le _ _).trans ?_
  have h1 : ‖δ⁻¹ • ContinuousLinearMap.id ℝ ℂ‖ ≤ δ⁻¹ := by
    rw [norm_smul, Real.norm_of_nonneg (inv_nonneg.2 hδ.le)]
    exact mul_le_of_le_one_right (inv_nonneg.2 hδ.le) (ContinuousLinearMap.norm_id_le)
  calc _ ≤ max M 0 * δ⁻¹ := mul_le_mul ((hM _).trans (le_max_left _ _)) h1 (norm_nonneg _)
        (le_max_right _ _)
    _ = max M 0 / δ := by rw [div_eq_mul_inv]

theorem fderiv_sBump_eq_zero_m7d {δ : ℝ} (hδ : 0 < δ) {p z : ℂ} (h : δ < ‖z - p‖) :
    fderiv ℝ (sBump p δ) z = 0 := by
  refine fderiv_of_notMem_tsupport ℝ fun hz => ?_
  have hsub : Function.support (sBump p δ) ⊆ ball p δ := by
    intro w hw
    rw [mem_ball, dist_eq_norm]
    by_contra hc
    exact hw (sBump_eq_zero_m7d hδ (not_lt.1 hc))
  have := (closure_mono hsub).trans closure_ball_subset_closedBall hz
  rw [mem_closedBall, dist_eq_norm] at this
  linarith

theorem norm_ofReal_sub_ofReal_m7d (a b : ℝ) : ‖(a : ℂ) - (b : ℂ)‖ = |a - b| := by
  rw [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]

/-- The cut-off function vanishes at one bump if it is at the other one. -/
theorem sBump_or_m7d {t r δ : ℝ} (hδ : 0 < δ) (hδr : δ ≤ r) (z : ℂ) :
    sBump ((t - r : ℝ) : ℂ) δ z = 0 ∨ sBump ((t + r : ℝ) : ℂ) δ z = 0 := by
  have hpq : ‖((t - r : ℝ) : ℂ) - ((t + r : ℝ) : ℂ)‖ = 2 * r := by
    rw [norm_ofReal_sub_ofReal_m7d, show t - r - (t + r) = -(2 * r) by ring, abs_neg,
      abs_of_nonneg (by linarith)]
  have htri := norm_sub_le_norm_sub_add_norm_sub ((t - r : ℝ) : ℂ) z ((t + r : ℝ) : ℂ)
  rw [norm_sub_rev ((t - r : ℝ) : ℂ) z] at htri
  by_cases h : δ ≤ ‖z - ((t - r : ℝ) : ℂ)‖
  · exact Or.inl (sBump_eq_zero_m7d hδ h)
  · exact Or.inr (sBump_eq_zero_m7d hδ (by linarith))

/-- **Energy of the endpoint cut-off.** -/
theorem energy_cut_le_m7d {t r δ L M : ℝ} (hr : 0 < r) (hδ : 0 < δ) (hδr : δ ≤ r) {f : ℂ → ℝ}
    (hfs : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) f)
    (hL : ∀ w ∈ closedBall (t : ℂ) (2 * r), ‖fderiv ℝ f w‖ ≤ L) (hL0 : 0 ≤ L) (hM0 : 0 ≤ M)
    (hM : ∀ p : ℂ, ∀ δ : ℝ, 0 < δ → ∀ z, ‖fderiv ℝ (sBump p δ) z‖ ≤ M / δ)
    (hfp : f ((t - r : ℝ) : ℂ) = 0) (hfq : f ((t + r : ℝ) : ℂ) = 0) :
    dirichletEnergyOn (ball (t : ℂ) r ∩ H)
        (fun z => f z * (1 - sBump ((t - r : ℝ) : ℂ) δ z - sBump ((t + r : ℝ) : ℂ) δ z)) ≤
      dirichletEnergyOn (ball (t : ℂ) r ∩ H) f +
        (2 * π)⁻¹ * ((4 * L ^ 2 * M + 4 * L ^ 2 * M ^ 2) * (2 * (δ ^ 2 * π))) := by
  set p : ℂ := ((t - r : ℝ) : ℂ) with hp
  set q : ℂ := ((t + r : ℝ) : ℂ) with hq
  set U := ball (t : ℂ) r ∩ H with hU
  set K := 4 * L ^ 2 * M + 4 * L ^ 2 * M ^ 2 with hK
  set S := closedBall p δ ∪ closedBall q δ with hS
  set η : ℂ → ℝ := fun z => 1 - sBump p δ z - sBump q δ z with hη
  have hpt : ‖p - t‖ = r := by
    rw [hp, norm_ofReal_sub_ofReal_m7d, show t - r - t = -r by ring, abs_neg, abs_of_pos hr]
  have hqt : ‖q - t‖ = r := by
    rw [hq, norm_ofReal_sub_ofReal_m7d, show t + r - t = r by ring, abs_of_pos hr]
  have hfd : Differentiable ℝ f := hfs.differentiable (by simp)
  have hbd : ∀ c : ℂ, Differentiable ℝ (sBump c δ) := fun c =>
    (contDiff_sBump_m7d c δ).differentiable (by simp)
  have hηd : ∀ z, HasFDerivAt η (0 - fderiv ℝ (sBump p δ) z - fderiv ℝ (sBump q δ) z) z :=
    fun z => ((hasFDerivAt_const (1 : ℝ) z).sub (hbd p z).hasFDerivAt).sub (hbd q z).hasFDerivAt
  have hη01 : ∀ z, |η z| ≤ 1 := by
    intro z
    rw [abs_le]
    rcases sBump_or_m7d (t := t) hδ hδr z with h | h <;>
      simp only [hη, h] <;>
      constructor <;> linarith [sBump_nonneg_m7d p δ z, sBump_le_one_m7d p δ z,
        sBump_nonneg_m7d q δ z, sBump_le_one_m7d q δ z]
  -- the pointwise bound
  have hlipc : ∀ c : ℂ, ‖c - t‖ = r → ∀ z, ‖z - c‖ ≤ δ → f c = 0 → |f z| ≤ L * δ := by
    intro c hc z hz hfc
    have hcB : c ∈ closedBall (t : ℂ) (2 * r) := by
      rw [mem_closedBall, dist_eq_norm, hc]; linarith
    have hzB : z ∈ closedBall (t : ℂ) (2 * r) := by
      rw [mem_closedBall, dist_eq_norm]
      linarith [norm_sub_le_norm_sub_add_norm_sub z c (t : ℂ)]
    have := (convex_closedBall (t : ℂ) (2 * r)).norm_image_sub_le_of_norm_fderiv_le
      (fun w _ => hfd w) hL hcB hzB
    rw [hfc, sub_zero, Real.norm_eq_abs] at this
    exact this.trans (mul_le_mul_of_nonneg_left hz hL0)
  have hs : ∀ z, |f z| * ‖fderiv ℝ η z‖ ≤ 2 * L * M * S.indicator 1 z := by
    intro z
    rw [(hηd z).fderiv]
    by_cases hzS : z ∈ S
    · rw [indicator_of_mem hzS, Pi.one_apply, mul_one]
      have hfz : |f z| ≤ L * δ := by
        rcases hzS with h | h <;> rw [mem_closedBall, dist_eq_norm] at h
        · exact hlipc p hpt z h hfp
        · exact hlipc q hqt z h hfq
      have hD : ‖0 - fderiv ℝ (sBump p δ) z - fderiv ℝ (sBump q δ) z‖ ≤ 2 * (M / δ) := by
        rw [zero_sub]
        refine (norm_sub_le _ _).trans ?_
        rw [norm_neg]; linarith [hM p δ hδ z, hM q δ hδ z]
      calc |f z| * ‖0 - fderiv ℝ (sBump p δ) z - fderiv ℝ (sBump q δ) z‖
          ≤ (L * δ) * (2 * (M / δ)) :=
            mul_le_mul hfz hD (norm_nonneg _) (by positivity)
        _ = 2 * L * M := by field_simp
    · rw [indicator_of_notMem hzS, mul_zero]
      simp only [hS, mem_union, mem_closedBall, dist_eq_norm, not_or, not_le] at hzS
      rw [fderiv_sBump_eq_zero_m7d hδ hzS.1, fderiv_sBump_eq_zero_m7d hδ hzS.2]; simp
  have hpt' : ∀ z ∈ U, ‖fderiv ℝ (fun z => f z * η z) z‖ ^ 2 ≤
      ‖fderiv ℝ f z‖ ^ 2 + K * S.indicator 1 z := by
    intro z hz
    have hzB : z ∈ closedBall (t : ℂ) (2 * r) := by
      have := hz.1; rw [mem_ball, dist_eq_norm] at this
      rw [mem_closedBall, dist_eq_norm]; linarith
    have hLz := hL z hzB
    have hFd : fderiv ℝ (fun z => f z * η z) z = f z • fderiv ℝ η z + η z • fderiv ℝ f z := by
      rw [(hηd z).fderiv]; exact ((hfd z).hasFDerivAt.mul (hηd z)).fderiv
    rw [hFd]
    have h1 : ‖f z • fderiv ℝ η z + η z • fderiv ℝ f z‖ ≤
        |f z| * ‖fderiv ℝ η z‖ + ‖fderiv ℝ f z‖ := by
      refine (norm_add_le _ _).trans ?_
      rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs]
      have := mul_le_mul_of_nonneg_right (hη01 z) (norm_nonneg (fderiv ℝ f z))
      linarith
    have hs' := hs z
    have hsn : 0 ≤ |f z| * ‖fderiv ℝ η z‖ := by positivity
    have hsq : ‖f z • fderiv ℝ η z + η z • fderiv ℝ f z‖ ^ 2 ≤
        (|f z| * ‖fderiv ℝ η z‖ + ‖fderiv ℝ f z‖) ^ 2 :=
      pow_le_pow_left₀ (norm_nonneg _) h1 2
    have hind : S.indicator (1 : ℂ → ℝ) z = 0 ∨ S.indicator (1 : ℂ → ℝ) z = 1 := by
      by_cases h : z ∈ S
      · right; rw [indicator_of_mem h, Pi.one_apply]
      · left; rw [indicator_of_notMem h]
    rcases hind with h | h <;> rw [h] at hs' ⊢
    · have : |f z| * ‖fderiv ℝ η z‖ = 0 := le_antisymm (by linarith) hsn
      rw [this, zero_add] at hsq; linarith
    · have hfn := norm_nonneg (fderiv ℝ f z)
      have e1 : 2 * (|f z| * ‖fderiv ℝ η z‖) * ‖fderiv ℝ f z‖ ≤ 2 * (2 * L * M) * L :=
        mul_le_mul (by linarith) hLz hfn (by positivity)
      have e2 : (|f z| * ‖fderiv ℝ η z‖) ^ 2 ≤ (2 * L * M) ^ 2 :=
        pow_le_pow_left₀ hsn (by linarith) 2
      nlinarith
  -- integrate
  have hUm : MeasurableSet U := isOpen_ball.measurableSet.inter measurableSet_H_k3
  have hSm : MeasurableSet S :=
    isClosed_closedBall.measurableSet.union isClosed_closedBall.measurableSet
  have hUfin : volume U < ⊤ := (measure_mono inter_subset_left).trans_lt measure_ball_lt_top
  have hint : ∀ g : ℂ → ℝ, Continuous g → IntegrableOn g U := fun g hg =>
    (hg.continuousOn.integrableOn_compact (isCompact_closedBall (t : ℂ) r)).mono_set
      (inter_subset_left.trans ball_subset_closedBall)
  have hFs : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun z => f z * η z) :=
    hfs.mul ((contDiff_const.sub (contDiff_sBump_m7d p δ)).sub (contDiff_sBump_m7d q δ))
  have hi1 : IntegrableOn (fun x => ‖fderiv ℝ (fun z => f z * η z) x‖ ^ 2) U :=
    hint _ ((hFs.continuous_fderiv (by simp)).norm.pow 2)
  have hi2 : IntegrableOn (fun x => ‖fderiv ℝ f x‖ ^ 2) U :=
    hint _ ((hfs.continuous_fderiv (by simp)).norm.pow 2)
  have hi3 : IntegrableOn (S.indicator (1 : ℂ → ℝ)) U :=
    (integrableOn_const hUfin.ne).indicator hSm
  have hmono : ∫ x in U, ‖fderiv ℝ (fun z => f z * η z) x‖ ^ 2 ≤
      ∫ x in U, (‖fderiv ℝ f x‖ ^ 2 + K * S.indicator 1 x) :=
    setIntegral_mono_on hi1 (hi2.add (hi3.const_mul K)) hUm hpt'
  have e : ∫ x in U, (‖fderiv ℝ f x‖ ^ 2 + K * S.indicator 1 x) =
      (∫ x in U, ‖fderiv ℝ f x‖ ^ 2) + K * ∫ x in U ∩ S, (1 : ℂ → ℝ) x := by
    rw [← setIntegral_indicator hSm, ← integral_const_mul]
    exact integral_add hi2 (hi3.const_mul K)
  have hvol : ∫ z in U ∩ S, (1 : ℂ → ℝ) z ≤ 2 * (δ ^ 2 * π) := by
    simp only [Pi.one_apply, setIntegral_const, smul_eq_mul, mul_one]
    have hball : ∀ c : ℂ, volume.real (closedBall c δ) = δ ^ 2 * π := by
      intro c
      rw [Measure.real, Complex.volume_closedBall, ENNReal.toReal_mul, ENNReal.toReal_pow,
        ENNReal.toReal_ofReal hδ.le, ENNReal.coe_toReal, NNReal.coe_real_pi]
    calc volume.real (U ∩ S) ≤ volume.real S :=
          measureReal_mono inter_subset_right (measure_union_lt_top
            measure_closedBall_lt_top measure_closedBall_lt_top).ne
      _ ≤ volume.real (closedBall p δ) + volume.real (closedBall q δ) := measureReal_union_le _ _
      _ = 2 * (δ ^ 2 * π) := by rw [hball, hball]; ring
  have hK0 : 0 ≤ K := by positivity
  have hfin : ∫ x in U, ‖fderiv ℝ (fun z => f z * η z) x‖ ^ 2 ≤
      (∫ x in U, ‖fderiv ℝ f x‖ ^ 2) + K * (2 * (δ ^ 2 * π)) := by
    rw [e] at hmono
    linarith [mul_le_mul_of_nonneg_left hvol hK0]
  simp only [hη] at hfin
  unfold dirichletEnergyOn
  rw [← mul_add]
  exact mul_le_mul_of_nonneg_left hfin (by positivity)

/-- **D3 (reflection upper bound on the half-disc mixed space).** -/
theorem sq_integral_le_halfDisc_m7d {t r r' : ℝ} (hr' : 0 < r') (hr'r : r' < r)
    {μ : Measure ℂ} [IsFiniteMeasure μ] (hμH : ∀ᵐ z ∂μ, z ∈ Hbar)
    (hμK : μ (closedBall (t : ℂ) r')ᶜ = 0)
    (hfin : dualNormSq (ball (t : ℂ) r) (zeroSpace (ball (t : ℂ) r)) (μ + μ.map conj) < ⊤)
    {f : ℂ → ℝ} (hf : f ∈ mixedSpace (ball (t : ℂ) r ∩ H) (realSet (Icc (t - r) (t + r)))) :
    (∫ x, f x ∂μ) ^ 2 ≤ (dualNormSq (ball (t : ℂ) r) (zeroSpace (ball (t : ℂ) r))
      (μ + μ.map conj)).toReal / 2 * dirichletEnergyOn (ball (t : ℂ) r ∩ H) f := by
  have hr : 0 < r := hr'.trans hr'r
  set c := (dualNormSq (ball (t : ℂ) r) (zeroSpace (ball (t : ℂ) r)) (μ + μ.map conj)).toReal / 2
    with hcdef
  set p : ℂ := ((t - r : ℝ) : ℂ) with hp
  set q : ℂ := ((t + r : ℝ) : ℂ) with hq
  have hpt : ‖p - t‖ = r := by
    rw [hp, norm_ofReal_sub_ofReal_m7d, show t - r - t = -r by ring, abs_neg, abs_of_pos hr]
  have hqt : ‖q - t‖ = r := by
    rw [hq, norm_ofReal_sub_ofReal_m7d, show t + r - t = r by ring, abs_of_pos hr]
  have hpS : p ∈ sphere (t : ℂ) r ∩ Hbar :=
    ⟨by rw [mem_sphere, dist_eq_norm, hpt], show (0 : ℝ) ≤ p.im by simp [hp]⟩
  have hqS : q ∈ sphere (t : ℂ) r ∩ Hbar :=
    ⟨by rw [mem_sphere, dist_eq_norm, hqt], show (0 : ℝ) ≤ q.im by simp [hq]⟩
  have hfp := eq_zero_of_mem_sphere_halfDisc_m7c hr hf hpS
  have hfq := eq_zero_of_mem_sphere_halfDisc_m7c hr hf hqS
  obtain ⟨hfs, -, N₀, hN₀, hN₀f, hf0⟩ := hf
  have hopen : IsOpen (ball (t : ℂ) r ∩ H) := isOpen_ball.inter isOpen_H
  have hSN : sphere (t : ℂ) r ∩ H ⊆ N₀ := by
    rintro w ⟨hw, hwH⟩
    refine hN₀f ⟨?_, ?_⟩
    · rw [hopen.frontier_eq]
      refine ⟨closedBall_inter_Hbar_subset_closure_m7a hr
        ⟨sphere_subset_closedBall hw, le_of_lt (show 0 < w.im from hwH)⟩, fun h => ?_⟩
      have := h.1
      rw [mem_ball, ← mem_sphere.1 hw] at this
      exact lt_irrefl _ this
    · rintro ⟨s, -, rfl⟩
      simp [H] at hwH
  obtain ⟨L, hL⟩ := (isCompact_closedBall (t : ℂ) (2 * r)).exists_bound_of_continuousOn
    (hfs.continuous_fderiv (by simp)).continuousOn
  have hL0 : 0 ≤ L := (norm_nonneg _).trans (hL t (mem_closedBall_self (by positivity)))
  obtain ⟨M, hM0, hM⟩ := exists_fderiv_sBump_le_m7d
  set K := 4 * L ^ 2 * M + 4 * L ^ 2 * M ^ 2 with hK
  set A := dirichletEnergyOn (ball (t : ℂ) r ∩ H) f with hA
  have key : ∀ δ, 0 < δ → δ ≤ r - r' →
      (∫ x, f x ∂μ) ^ 2 ≤ c * (A + (2 * π)⁻¹ * (K * (2 * (δ ^ 2 * π)))) := by
    intro δ hδ hδr
    have hδr2 : δ ≤ r := by linarith
    have hpq : ‖p - q‖ = 2 * r := by
      rw [hp, hq, norm_ofReal_sub_ofReal_m7d, show t - r - (t + r) = -(2 * r) by ring, abs_neg,
        abs_of_nonneg (by linarith)]
    set F : ℂ → ℝ := fun z => f z * (1 - sBump p δ z - sBump q δ z) with hF
    have hFs : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) F :=
      hfs.mul ((contDiff_const.sub (contDiff_sBump_m7d p δ)).sub (contDiff_sBump_m7d q δ))
    -- vanishing near the closed semicircle
    have hFp : ∀ z ∈ ball p (δ / 2), F z = 0 := by
      intro z hz
      rw [mem_ball, dist_eq_norm] at hz
      have h1 := sBump_eq_one_m7d hδ hz.le
      have h2 : sBump q δ z = 0 := sBump_eq_zero_m7d hδ (by
        have := norm_sub_le_norm_sub_add_norm_sub p z q
        rw [norm_sub_rev p z] at this; linarith)
      simp [hF, h1, h2]
    have hFq : ∀ z ∈ ball q (δ / 2), F z = 0 := by
      intro z hz
      rw [mem_ball, dist_eq_norm] at hz
      have h1 := sBump_eq_one_m7d hδ hz.le
      have h2 : sBump p δ z = 0 := sBump_eq_zero_m7d hδ (by
        have := norm_sub_le_norm_sub_add_norm_sub q z p
        rw [norm_sub_rev q z, norm_sub_rev q p] at this; linarith)
      simp [hF, h1, h2]
    have hNo : IsOpen (N₀ ∪ ball p (δ / 2) ∪ ball q (δ / 2)) :=
      (hN₀.union isOpen_ball).union isOpen_ball
    have hFN : ∀ z ∈ N₀ ∪ ball p (δ / 2) ∪ ball q (δ / 2), F z = 0 := by
      rintro z ((h | h) | h)
      · simp [hF, hf0 z h]
      · exact hFp z h
      · exact hFq z h
    have hsN : sphere (t : ℂ) r ∩ Hbar ⊆ N₀ ∪ ball p (δ / 2) ∪ ball q (δ / 2) := by
      rintro z ⟨hz, hzH⟩
      rcases lt_or_eq_of_le (show (0 : ℝ) ≤ z.im from hzH) with h | h
      · exact Or.inl (Or.inl (hSN ⟨hz, h⟩))
      · have hzr : z = (z.re : ℂ) := Complex.ext (by simp) (by simp [← h])
        rw [mem_sphere, dist_eq_norm, hzr, norm_ofReal_sub_ofReal_m7d] at hz
        rcases (abs_eq hr.le).1 hz with h1 | h1
        · refine Or.inr ?_
          rw [hzr, show z.re = t + r by linarith]
          exact mem_ball_self (by positivity)
        · refine Or.inl (Or.inr ?_)
          rw [hzr, show z.re = t - r by linarith]
          exact mem_ball_self (by positivity)
    have hD2 := sq_integral_le_of_vanish_m7d hr' hr'r hμH hμK hfin hFs hNo hsN hFN
    -- the pairing is unchanged
    have hFμ : ∫ x, F x ∂μ = ∫ x, f x ∂μ := by
      refine integral_congr_ae ?_
      filter_upwards [mem_ae_iff.2 hμK] with z hz
      rw [mem_closedBall, dist_eq_norm] at hz
      have h1 : sBump p δ z = 0 := sBump_eq_zero_m7d hδ (by
        have := norm_sub_le_norm_sub_add_norm_sub p z (t : ℂ)
        rw [norm_sub_rev p z] at this; linarith)
      have h2 : sBump q δ z = 0 := sBump_eq_zero_m7d hδ (by
        have := norm_sub_le_norm_sub_add_norm_sub q z (t : ℂ)
        rw [norm_sub_rev q z] at this; linarith)
      simp [hF, h1, h2]
    have hE := energy_cut_le_m7d hr hδ hδr2 hfs hL hL0 hM0 hM hfp hfq
    rw [hFμ] at hD2
    have hc0 : 0 ≤ c := by rw [hcdef]; positivity
    exact hD2.trans (mul_le_mul_of_nonneg_left hE hc0)
  have hcont : Continuous fun δ : ℝ => c * (A + (2 * π)⁻¹ * (K * (2 * (δ ^ 2 * π)))) := by
    fun_prop
  have ht : Tendsto (fun δ : ℝ => c * (A + (2 * π)⁻¹ * (K * (2 * (δ ^ 2 * π))))) (𝓝[>] 0)
      (𝓝 (c * A)) := by
    have h := (hcont.tendsto 0).mono_left (nhdsWithin_le_nhds (s := Ioi (0 : ℝ)))
    simpa using h
  refine ge_of_tendsto ht ?_
  filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < r - r' by linarith)] with δ hδ
  exact key δ hδ.1 hδ.2.le

end QuantumZipper.K3
