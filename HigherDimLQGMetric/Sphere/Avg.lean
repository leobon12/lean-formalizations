import HigherDimLQGMetric.Sphere.Cov

/-!
# Sphere averages of the LGF: Gaussianity, covariances, `L²` identification

Packet F3 (Phase A, block A1), target 2, stated for the sphere averages `h_r(z) = sphereAvg h r z`
themselves (the points `(0, r, z)` of `Sphere/Cov.lean`; `sphLaw r z 0 = sphMeas r z = σ_{r,z}`).
For an LGF `h` on any probability space and `d ≥ 2`, all radii positive:

* `IsWholeSpaceLGF.isGaussianProcess_sphereAvg_sub`: the differences `h_r(z) - h_ρ(w)` together with
  all mean-zero pairings `⟨h, φ⟩` form a centred Gaussian process;
* `IsWholeSpaceLGF.covariance_sphereAvg_sub`:
  `Cov(h_r(z) - h_ρ(w), h_{r'}(z') - h_{ρ'}(w')) = logCov(σ_{r,z}, σ_{ρ,w}, σ_{r',z'}, σ_{ρ',w'})`
  `= ∫∫ log|u - v|⁻¹ (σ_{r,z} - σ_{ρ,w})(du) (σ_{r',z'} - σ_{ρ',w'})(dv)`;
* `IsWholeSpaceLGF.covariance_sphereAvg_sub_apply`: for mean-zero `φ`,
  `Cov(h_r(z) - h_ρ(w), ⟨h, φ⟩) = logCov(σ_{r,z}, σ_{ρ,w}, φ⁺ dz, φ⁻ dz)`;
* `IsWholeSpaceLGF.ae_tendsto_sphDiff`, `IsWholeSpaceLGF.tendsto_integral_sq_sphDiff_sub`:
  `h_r(z) - h_ρ(w)` is the a.s. and `L²` limit of the mean-zero pairings
  `⟨h, sphDiff n z r n w ρ⟩ = ⟨h, σ_{r,z} * ψ_n - σ_{ρ,w} * ψ_n⟩`, with
  `E[(⟨h, sphDiff n z r n w ρ⟩ - (h_r(z) - h_ρ(w)))²] ≤ 2 C 2^{-n} (1/r + 1/ρ)`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set Metric Filter Topology
open scoped ENNReal

namespace HigherDimLQGMetric

open HigherDimLFPP (Rd)

variable {d : ℕ}

/-- The point `(0, r, z)`: the sphere average `h_r(z)`. -/
def sphPt0 {r : ℝ} (hr : 0 < r) (z : Rd d) : SphPt d := ⟨0, r, z, le_rfl, hr⟩

/-- The point `(2^{-n}, r, z)`: the `n`-th mollified sphere average. -/
def sphPtN (n : ℕ) {r : ℝ} (hr : 0 < r) (z : Rd d) : SphPt d :=
  ⟨((2 : ℝ) ^ n)⁻¹, r, z, by positivity, hr⟩

theorem sphPt0_law {r : ℝ} (hr : 0 < r) (z : Rd d) : (sphPt0 hr z).law = sphMeas r z :=
  sphLaw_zero r z

/-- Pairs of spheres with positive radii. -/
def SphPair (d : ℕ) : Type := {q : (ℝ × Rd d) × (ℝ × Rd d) // 0 < q.1.1 ∧ 0 < q.2.1}

/-- The corresponding pair of points `(0, r, z)`, `(0, ρ, w)`. -/
def SphPair.toPts (q : SphPair d) : SphPt d × SphPt d :=
  (sphPt0 q.2.1 q.1.1.2, sphPt0 q.2.2 q.1.2.2)

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {h : Ω → DistRd d}

omit [MeasurableSpace Ω] in
theorem sphIncProc_sphPt0 {r ρ : ℝ} (hr : 0 < r) (hρ : 0 < ρ) (z w : Rd d) (ω : Ω) :
    sphIncProc h (.inl (sphPt0 hr z, sphPt0 hρ w)) ω = sphereAvg (h ω) r z - sphereAvg (h ω) ρ w :=
  by simp only [sphIncProc, sphPt0, sphProc_zero]

/-- **Joint Gaussianity**: the sphere-average differences `h_r(z) - h_ρ(w)` (positive radii) and the
mean-zero pairings form a centred Gaussian process (`d ≥ 2`). -/
theorem IsWholeSpaceLGF.isGaussianProcess_sphereAvg_sub (hd : 2 ≤ d) (hh : IsWholeSpaceLGF h P) :
    IsGaussianProcess (Sum.elim
      (fun (q : SphPair d) ω => sphereAvg (h ω) q.1.1.1 q.1.1.2 - sphereAvg (h ω) q.1.2.1 q.1.2.2)
      (fun (φ : TestRd0 d) ω => h ω φ.1)) P := by
  have hG := (hh.isGaussianProcess_sphIncProc hd).comp_right
    (Sum.map (fun q : SphPair d => q.toPts) id)
  refine hG.congr fun t => ?_
  rcases t with q | φ
  · exact ae_of_all _ fun ω => sphIncProc_sphPt0 q.2.1 q.2.2 _ _ ω
  · exact ae_of_all _ fun ω => rfl

/-- `h_r(z) - h_ρ(w)` is centred Gaussian. -/
theorem IsWholeSpaceLGF.hasGaussianLaw_sphereAvg_sub (hd : 2 ≤ d) (hh : IsWholeSpaceLGF h P)
    {r ρ : ℝ} (hr : 0 < r) (hρ : 0 < ρ) (z w : Rd d) :
    HasGaussianLaw (fun ω => sphereAvg (h ω) r z - sphereAvg (h ω) ρ w) P ∧
      ∫ ω, (sphereAvg (h ω) r z - sphereAvg (h ω) ρ w) ∂P = 0 := by
  have hG := (hh.isGaussianProcess_sphIncProc hd).hasGaussianLaw_eval
    (.inl (sphPt0 hr z, sphPt0 hρ w))
  have h0 := hh.integral_sphIncProc hd (.inl (sphPt0 hr z, sphPt0 hρ w))
  have e : sphIncProc h (.inl (sphPt0 hr z, sphPt0 hρ w)) =
      fun ω => sphereAvg (h ω) r z - sphereAvg (h ω) ρ w :=
    funext fun ω => sphIncProc_sphPt0 hr hρ z w ω
  rw [e] at hG h0
  exact ⟨hG, h0⟩

/-- **Covariance of sphere-average differences** (`d ≥ 2`, positive radii):
`Cov(h_r(z) - h_ρ(w), h_{r'}(z') - h_{ρ'}(w')) = logCov(σ_{r,z}, σ_{ρ,w}, σ_{r',z'}, σ_{ρ',w'})`. -/
theorem IsWholeSpaceLGF.covariance_sphereAvg_sub (hd : 2 ≤ d) (hh : IsWholeSpaceLGF h P)
    {r ρ r' ρ' : ℝ} (hr : 0 < r) (hρ : 0 < ρ) (hr' : 0 < r') (hρ' : 0 < ρ') (z w z' w' : Rd d) :
    cov[fun ω => sphereAvg (h ω) r z - sphereAvg (h ω) ρ w,
      fun ω => sphereAvg (h ω) r' z' - sphereAvg (h ω) ρ' w'; P] =
      HigherDimLFPP.logCov (sphMeas r z) (sphMeas ρ w) (sphMeas r' z') (sphMeas ρ' w') := by
  have hc := hh.covariance_sphIncProc hd (sphPt0 hr z) (sphPt0 hρ w) (sphPt0 hr' z')
    (sphPt0 hρ' w')
  rw [sphPt0_law, sphPt0_law, sphPt0_law, sphPt0_law] at hc
  rw [← hc]
  congr 1
  · exact funext fun ω => (sphIncProc_sphPt0 hr hρ z w ω).symm
  · exact funext fun ω => (sphIncProc_sphPt0 hr' hρ' z' w' ω).symm

/-- **Covariance of a sphere-average difference with a mean-zero pairing** (`d ≥ 2`):
`Cov(h_r(z) - h_ρ(w), ⟨h, φ⟩) = logCov(σ_{r,z}, σ_{ρ,w}, φ⁺ dz, φ⁻ dz)`. -/
theorem IsWholeSpaceLGF.covariance_sphereAvg_sub_apply (hd : 2 ≤ d) (hh : IsWholeSpaceLGF h P)
    {r ρ : ℝ} (hr : 0 < r) (hρ : 0 < ρ) (z w : Rd d) (φ : TestRd0 d) :
    cov[fun ω => sphereAvg (h ω) r z - sphereAvg (h ω) ρ w, fun ω => h ω φ.1; P] =
      HigherDimLFPP.logCov (sphMeas r z) (sphMeas ρ w) (posM φ.1) (posM (-φ.1)) := by
  have hc := hh.covariance_sphIncProc_apply hd (sphPt0 hr z) (sphPt0 hρ w) φ
  rw [sphPt0_law, sphPt0_law] at hc
  rw [← hc]
  congr 1
  exact funext fun ω => (sphIncProc_sphPt0 hr hρ z w ω).symm

/-- `Var(h_r(z) - h_ρ(w)) = logCov(σ_{r,z}, σ_{ρ,w}, σ_{r,z}, σ_{ρ,w})`. -/
theorem IsWholeSpaceLGF.variance_sphereAvg_sub (hd : 2 ≤ d) (hh : IsWholeSpaceLGF h P)
    {r ρ : ℝ} (hr : 0 < r) (hρ : 0 < ρ) (z w : Rd d) :
    Var[fun ω => sphereAvg (h ω) r z - sphereAvg (h ω) ρ w; P] =
      HigherDimLFPP.logCov (sphMeas r z) (sphMeas ρ w) (sphMeas r z) (sphMeas ρ w) := by
  rw [← covariance_self (hh.hasGaussianLaw_sphereAvg_sub hd hr hρ z w).1.aemeasurable,
    hh.covariance_sphereAvg_sub hd hr hρ hr hρ z w z w]

/-- The `n`-th mollified difference is a difference of two values of `sphProc`. -/
theorem apply_sphDiff_eq (g : DistRd d) (n : ℕ) (r ρ : ℝ) (z w : Rd d) :
    g (sphDiff n z r n w ρ) = sphProc g ((2 : ℝ) ^ n)⁻¹ r z - sphProc g ((2 : ℝ) ^ n)⁻¹ ρ w := by
  rw [sphProc_of_ne _ (by positivity), sphProc_of_ne _ (by positivity), sphMol_two_pow_inv,
    sphMol_two_pow_inv, sphDiff, map_sub]

/-- **A.s. identification**: `⟨h, sphDiff n z r n w ρ⟩ → h_r(z) - h_ρ(w)` almost surely. -/
theorem IsWholeSpaceLGF.ae_tendsto_sphDiff (hd : 2 ≤ d) (hh : IsWholeSpaceLGF h P) {r ρ : ℝ}
    (hr : 0 < r) (hρ : 0 < ρ) (z w : Rd d) :
    ∀ᵐ ω ∂P, Tendsto (fun n => h ω (sphDiff n z r n w ρ)) atTop
      (𝓝 (sphereAvg (h ω) r z - sphereAvg (h ω) ρ w)) := by
  filter_upwards [hh.ae_exists_tendsto_sphereAvgSeq hd hr z,
    hh.ae_exists_tendsto_sphereAvgSeq hd hρ w] with ω h1 h2
  refine ((tendsto_sphereAvgSeq_sphereAvg h1).sub (tendsto_sphereAvgSeq_sphereAvg h2)).congr
    fun n => ?_
  rw [sphereAvgSeq_sub_eq_apply_sphDiff]

/-- **`L²` identification** (`d ≥ 2`): there is `C = C(d)` with
`E[(⟨h, sphDiff n z r n w ρ⟩ - (h_r(z) - h_ρ(w)))²] ≤ 2 C 2^{-n} (1/r + 1/ρ)` for every LGF; in
particular the mean-zero pairings converge in `L²` to `h_r(z) - h_ρ(w)`. -/
theorem exists_integral_sq_sphDiff_sub_le (hd : 2 ≤ d) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {h : Ω → DistRd d},
      IsWholeSpaceLGF h P → ∀ {r ρ : ℝ}, 0 < r → 0 < ρ → ∀ (z w : Rd d) (n : ℕ),
        Integrable (fun ω => (h ω (sphDiff n z r n w ρ) -
          (sphereAvg (h ω) r z - sphereAvg (h ω) ρ w)) ^ 2) P ∧
        ∫ ω, (h ω (sphDiff n z r n w ρ) - (sphereAvg (h ω) r z - sphereAvg (h ω) ρ w)) ^ 2 ∂P ≤
          2 * C * ((2 : ℝ) ^ n)⁻¹ * (1 / r + 1 / ρ) := by
  obtain ⟨C, hC0, hC⟩ := exists_integral_sq_sphIncProc_le hd
  refine ⟨C, hC0, fun {Ω} _ {P} {h} hh {r ρ} hr hρ z w n => ?_⟩
  set A := sphIncProc h (.inl (sphPtN n hr z, sphPt0 hr z)) with hA
  set B := sphIncProc h (.inl (sphPtN n hρ w, sphPt0 hρ w)) with hB
  have e : (fun ω => (h ω (sphDiff n z r n w ρ) -
      (sphereAvg (h ω) r z - sphereAvg (h ω) ρ w)) ^ 2) = fun ω => (A ω - B ω) ^ 2 := by
    funext ω
    rw [apply_sphDiff_eq, hA, hB]
    simp only [sphIncProc, sphPtN, sphPt0, sphProc_zero]
    ring
  obtain ⟨gA, -, iA, bA⟩ := hC hh (sphPtN n hr z) (sphPt0 hr z)
  obtain ⟨gB, -, iB, bB⟩ := hC hh (sphPtN n hρ w) (sphPt0 hρ w)
  have hdist : ∀ {s : ℝ} (hs : 0 < s) (x : Rd d),
      (sphPtN n hs x).dist (sphPt0 hs x) / min (sphPtN n hs x).r (sphPt0 hs x).r =
        ((2 : ℝ) ^ n)⁻¹ * (1 / s) := by
    intro s hs x
    simp only [SphPt.dist, sphPtN, sphPt0, sub_self, norm_zero, abs_zero, sub_zero, zero_add,
      min_self]
    rw [abs_of_pos (by positivity), div_eq_mul_one_div]
  rw [mul_div_assoc, hdist] at bA bB
  have iA' : Integrable (fun ω => A ω ^ 2) P := gA.memLp_two.integrable_sq
  have iB' : Integrable (fun ω => B ω ^ 2) P := gB.memLp_two.integrable_sq
  have hle : ∀ ω, (A ω - B ω) ^ 2 ≤ 2 * A ω ^ 2 + 2 * B ω ^ 2 := fun ω => by
    nlinarith [sq_nonneg (A ω + B ω)]
  rw [e]
  refine ⟨(gA.memLp_two.sub gB.memLp_two).integrable_sq, ?_⟩
  calc ∫ ω, (A ω - B ω) ^ 2 ∂P ≤ ∫ ω, (2 * A ω ^ 2 + 2 * B ω ^ 2) ∂P :=
        integral_mono (gA.memLp_two.sub gB.memLp_two).integrable_sq
          ((iA'.const_mul 2).add (iB'.const_mul 2)) hle
    _ = 2 * ∫ ω, A ω ^ 2 ∂P + 2 * ∫ ω, B ω ^ 2 ∂P := by
        rw [integral_add (iA'.const_mul 2) (iB'.const_mul 2), integral_const_mul,
          integral_const_mul]
    _ ≤ 2 * (C * (((2 : ℝ) ^ n)⁻¹ * (1 / r))) + 2 * (C * (((2 : ℝ) ^ n)⁻¹ * (1 / ρ))) := by
        rw [iA, iB]
        exact add_le_add (mul_le_mul_of_nonneg_left bA (by norm_num))
          (mul_le_mul_of_nonneg_left bB (by norm_num))
    _ = 2 * C * ((2 : ℝ) ^ n)⁻¹ * (1 / r + 1 / ρ) := by ring

/-- **`L²` convergence** of the mean-zero pairings `⟨h, sphDiff n z r n w ρ⟩` to
`h_r(z) - h_ρ(w)` (`d ≥ 2`, `r, ρ > 0`). -/
theorem IsWholeSpaceLGF.tendsto_integral_sq_sphDiff_sub (hd : 2 ≤ d) (hh : IsWholeSpaceLGF h P)
    {r ρ : ℝ} (hr : 0 < r) (hρ : 0 < ρ) (z w : Rd d) :
    Tendsto (fun n => ∫ ω, (h ω (sphDiff n z r n w ρ) -
      (sphereAvg (h ω) r z - sphereAvg (h ω) ρ w)) ^ 2 ∂P) atTop (𝓝 0) := by
  obtain ⟨C, hC0, hC⟩ := exists_integral_sq_sphDiff_sub_le hd
  have hb : Tendsto (fun n : ℕ => 2 * C * ((2 : ℝ) ^ n)⁻¹ * (1 / r + 1 / ρ)) atTop (𝓝 0) := by
    have h1 : Tendsto (fun n : ℕ => ((2 : ℝ) ^ n)⁻¹) atTop (𝓝 0) := by
      simp_rw [← inv_pow]
      exact tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
    have := (h1.const_mul (2 * C)).mul_const (1 / r + 1 / ρ)
    simpa only [mul_zero, zero_mul] using this
  refine squeeze_zero (fun n => integral_nonneg fun ω => sq_nonneg _) (fun n => ?_) hb
  exact (hC hh hr hρ z w n).2

end HigherDimLQGMetric
