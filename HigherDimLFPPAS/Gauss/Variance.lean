import HigherDimLFPPAS.Gauss.L2Fubini
import HigherDimLFPPAS.Gauss.SphereL2
import HigherDimLFPPAS.Gauss.Weight

/-!
# The variance (A.4) and the increment bound P4.1′ (packet F2b)

Write `H_t(x) := h ∗ K_{e^{-t}}(x)` (`convMollify κ (exp (-t)) h x`) for a normalized LGF `h` and an
admissible (signed) seed `κ`. By the radial formula, `H_t(x) = ∫_0^∞ w(u) h_{e^{-t}u}(x) du`, and the
`L²` Fubini lemmas of `Gauss/L2Fubini.lean` reduce second moments of `H` to sphere-average second
moments (planning audit MA3, Details P3 proof 2 and P4.1′):

* `integral_convMollify_F2b`: `E H_t(x) = 0`;
* `exists_abs_variance_convMollify_sub_le_F2b` (**(A.4)**): `|Var H_t(x) - t| ≤ C_R` for `t ≥ 0`,
  `‖x‖ ≤ R`;
* `exists_integral_sq_convMollify_sub_le_F2b` (**P4.1′**): for `|t - t'| ≤ 1`,
  `E (H_t(x) - H_{t'}(x'))² ≤ C₃ (|t - t'| + e^{max(t,t')} ‖x - x'‖)`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter

namespace HigherDimLFPPAS.Gauss

open HigherDimLQGMetric
open HigherDimLFPP (Rd e₁)

variable {d : ℕ} {κ : Rd d → ℝ}

/-- The radial integrand `(ω, u) ↦ h_{εu}(z)`. -/
def sphScaleF2b {Ω : Type} (h : Ω → DistRd d) (ε : ℝ) (z : Rd d) : Ω → ℝ → ℝ :=
  fun ω u => sphereAvg (h ω) (ε * u) z

lemma sqrt_add_le_F2b {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) : √(a + b) ≤ √a + √b := by
  rw [show √a + √b = √((√a + √b) ^ 2) from (Real.sqrt_sq (by positivity)).symm]
  refine Real.sqrt_le_sqrt ?_
  nlinarith [Real.sq_sqrt ha, Real.sq_sqrt hb, Real.sqrt_nonneg a, Real.sqrt_nonneg b]

variable {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {h : Ω → DistRd d}

omit [IsProbabilityMeasure P] in
lemma measurable_sphScaleF2b (hh : IsNormalizedLGF h P) (ε : ℝ) (z : Rd d) :
    Measurable fun q : Ω × ℝ => sphScaleF2b h ε z q.1 q.2 :=
  measurable_sphereAvg_scale_F2b hh ε z

omit [IsProbabilityMeasure P] in
lemma ae_memLp_sphScaleF2b (hd : 2 ≤ d) (hh : IsNormalizedLGF h P) {ε : ℝ} (hε : 0 < ε)
    (z : Rd d) :
    ∀ᵐ u ∂(volume.restrict (Ioi (0 : ℝ))), MemLp (fun ω => sphScaleF2b h ε z ω u) 2 P :=
  (ae_restrict_iff' measurableSet_Ioi).2
    (Eventually.of_forall fun _ hu => memLp_sphereAvg_F2b hd hh (mul_pos hε hu) z)

/-- `∫ |w(u)| ‖h_{εu}(z)‖_{L²} du < ∞`. -/
lemma integrable_radWeight_l2Sec_F2b (hd : 2 ≤ d) (hκ : HigherDimLFPPAS.IsAdmissibleSeed κ)
    (hh : IsNormalizedLGF h P) {ε : ℝ} (hε : 0 < ε) (z : Rd d) :
    Integrable (fun u => |radWeightF2b κ u| * l2SecF2b P (sphScaleF2b h ε z) u)
      (volume.restrict (Ioi (0 : ℝ))) := by
  obtain ⟨K, hK⟩ := exists_abs_integral_sq_sphereAvg_sub_abs_log_le_F2b hd ‖z‖
  have hdom := integrableOn_radWeightF2b_log hd hκ (1 + |K| + |Real.log ε|) 1
  refine Integrable.mono' hdom ?_ ?_
  · exact (((continuous_radWeightF2b hd hκ).abs.measurable).mul
      (measurable_l2SecF2b (measurable_sphScaleF2b hh ε z))).aestronglyMeasurable
  · refine (ae_restrict_iff' measurableSet_Ioi).2 (Eventually.of_forall fun u hu => ?_)
    have hu0 : (0 : ℝ) < u := hu
    have hm := hK hh (mul_pos hε hu0) z le_rfl
    have hm2 : ∫ ω, sphScaleF2b h ε z ω u ^ 2 ∂P ≤ |K| + |Real.log ε| + |Real.log u| := by
      have hl : Real.log (ε * u) = Real.log ε + Real.log u := Real.log_mul hε.ne' hu0.ne'
      have habs : |Real.log (ε * u)| ≤ |Real.log ε| + |Real.log u| := by
        rw [hl]; exact abs_add_le _ _
      have := (abs_le.mp hm).2
      have hK0 := le_abs_self K
      simp only [sphScaleF2b]
      linarith
    have hsq : l2SecF2b P (sphScaleF2b h ε z) u ≤ 1 + |K| + |Real.log ε| + 1 * |Real.log u| := by
      unfold l2SecF2b
      have h0 : 0 ≤ |K| + |Real.log ε| + |Real.log u| := by positivity
      refine (Real.sqrt_le_sqrt hm2).trans ?_
      rw [Real.sqrt_le_left (by positivity)]
      nlinarith
    rw [Real.norm_eq_abs, abs_mul, abs_abs,
      abs_of_nonneg (l2SecF2b_nonneg P (sphScaleF2b h ε z) u)]
    exact mul_le_mul_of_nonneg_left hsq (abs_nonneg _)

/-- The convolution field as the radial integral, almost surely for fixed `(ε, z)`. -/
lemma ae_convMollify_eq_radial_F2b (hd : 2 ≤ d) (hκ : HigherDimLFPPAS.IsAdmissibleSeed κ)
    (hh : IsNormalizedLGF h P) {ε : ℝ} (hε : 0 < ε) (z : Rd d) :
    (fun ω => convMollify κ ε (h ω) z) =ᵐ[P]
      fun ω => ∫ u, radWeightF2b κ u * sphScaleF2b h ε z ω u ∂(volume.restrict (Ioi (0 : ℝ))) := by
  filter_upwards [ae_convMollify_eq_integral_radWeightF2b hd hκ hh] with ω hω
  exact hω ε hε z

/-- The convolution field is centred. -/
theorem integral_convMollify_F2b (hd : 2 ≤ d) (hκ : HigherDimLFPPAS.IsAdmissibleSeed κ)
    (hh : IsNormalizedLGF h P) {ε : ℝ} (hε : 0 < ε) (z : Rd d) :
    ∫ ω, convMollify κ ε (h ω) z ∂P = 0 := by
  rw [integral_congr_ae (ae_convMollify_eq_radial_F2b hd hκ hh hε z),
    integral_integral_eq_F2b (measurable_radWeightF2b hd hκ) (measurable_sphScaleF2b hh ε z)
      (ae_memLp_sphScaleF2b hd hh hε z) (integrable_radWeight_l2Sec_F2b hd hκ hh hε z)]
  have h0 : (fun u => radWeightF2b κ u * ∫ ω, sphScaleF2b h ε z ω u ∂P) =ᵐ[volume.restrict
      (Ioi (0 : ℝ))] fun _ => 0 := by
    refine (ae_restrict_iff' measurableSet_Ioi).2 (Eventually.of_forall fun u hu => ?_)
    simp only [sphScaleF2b, integral_sphereAvg_F2b hd hh (mul_pos hε hu) z, mul_zero]
  rw [integral_congr_ae h0, integral_zero]

/-- The second mixed moment of the convolution field in terms of sphere averages. -/
theorem integral_mul_convMollify_F2b (hd : 2 ≤ d) (hκ : HigherDimLFPPAS.IsAdmissibleSeed κ)
    (hh : IsNormalizedLGF h P) {ε ε' : ℝ} (hε : 0 < ε) (hε' : 0 < ε') (z z' : Rd d) :
    ∫ ω, convMollify κ ε (h ω) z * convMollify κ ε' (h ω) z' ∂P =
      ∫ q, radWeightF2b κ q.1 * radWeightF2b κ q.2 *
        ∫ ω, sphScaleF2b h ε z ω q.1 * sphScaleF2b h ε' z' ω q.2 ∂P
        ∂((volume.restrict (Ioi (0 : ℝ))).prod (volume.restrict (Ioi (0 : ℝ)))) := by
  have he : (fun ω => convMollify κ ε (h ω) z * convMollify κ ε' (h ω) z') =ᵐ[P]
      fun ω => (∫ u, radWeightF2b κ u * sphScaleF2b h ε z ω u ∂(volume.restrict (Ioi (0 : ℝ)))) *
        ∫ v, radWeightF2b κ v * sphScaleF2b h ε' z' ω v ∂(volume.restrict (Ioi (0 : ℝ))) := by
    filter_upwards [ae_convMollify_eq_radial_F2b hd hκ hh hε z,
      ae_convMollify_eq_radial_F2b hd hκ hh hε' z'] with ω h1 h2
    rw [h1, h2]
  rw [integral_congr_ae he]
  exact integral_mul_integral_eq_F2b (measurable_radWeightF2b hd hκ)
    (measurable_radWeightF2b hd hκ) (measurable_sphScaleF2b hh ε z)
    (measurable_sphScaleF2b hh ε' z') (ae_memLp_sphScaleF2b hd hh hε z)
    (ae_memLp_sphScaleF2b hd hh hε' z') (integrable_radWeight_l2Sec_F2b hd hκ hh hε z)
    (integrable_radWeight_l2Sec_F2b hd hκ hh hε' z')

/-- The elementary logarithmic estimate behind (A.4). -/
lemma abs_half_sub_le_F2b {A B D α β t K₁ K₂ : ℝ} (ht : 0 ≤ t)
    (hA : |A - (|α - t|)| ≤ K₁) (hB : |B - (|β - t|)| ≤ K₁) (hD : |D - (|α - β|)| ≤ K₂) :
    |(A + B - D) / 2 - t| ≤ (2 * K₁ + K₂) / 2 + |α| + |β| := by
  have hA' := abs_le.mp hA
  have hB' := abs_le.mp hB
  have hD' := abs_le.mp hD
  have h1 : |α - t| ≤ |α| + t := by
    calc |α - t| ≤ |α| + |t| := abs_sub _ _
      _ = |α| + t := by rw [abs_of_nonneg ht]
  have h2 : |β - t| ≤ |β| + t := by
    calc |β - t| ≤ |β| + |t| := abs_sub _ _
      _ = |β| + t := by rw [abs_of_nonneg ht]
  have h3 : t - |α| ≤ |α - t| := by
    have := abs_sub_abs_le_abs_sub t α
    rw [abs_of_nonneg ht, abs_sub_comm] at this
    exact this
  have h4 : t - |β| ≤ |β - t| := by
    have := abs_sub_abs_le_abs_sub t β
    rw [abs_of_nonneg ht, abs_sub_comm] at this
    exact this
  have h5 : |α - β| ≤ |α| + |β| := abs_sub _ _
  have h6 : 0 ≤ |α - β| := abs_nonneg _
  rw [abs_le]
  constructor <;> linarith

omit [IsProbabilityMeasure P] in
/-- The pathwise convolution field is measurable in `ω`. -/
lemma measurable_convMollify_F2b (hh : IsNormalizedLGF h P) (ε : ℝ) (z : Rd d) :
    Measurable fun ω => convMollify κ ε (h ω) z := by
  have hm' (n : ℕ) : StronglyMeasurable fun ω : Ω => h ω (convTrunc κ ε z n) :=
    ((measurable_distOn_apply _).comp hh.1.measurable).stronglyMeasurable
  exact (StronglyMeasurable.limUnder (l := atTop) hm').measurable

/-- **(A.4)** (planning audit MA3, Details P3): `|Var H_t(x) - t| ≤ C_R` for all `t ≥ 0` and
`‖x‖ ≤ R`, with `H_t(x) = h ∗ K_{e^{-t}}(x)`. The constant depends only on `d`, `κ`, `R`. -/
theorem exists_abs_variance_convMollify_sub_le_F2b (hd : 2 ≤ d)
    (hκ : HigherDimLFPPAS.IsAdmissibleSeed κ) (R : ℝ) :
    ∃ C : ℝ, ∀ {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
      {h : Ω → DistRd d}, IsNormalizedLGF h P → ∀ t : ℝ, 0 ≤ t → ∀ x : Rd d, ‖x‖ ≤ R →
        |Var[fun ω => convMollify κ (Real.exp (-t)) (h ω) x; P] - t| ≤ C := by
  obtain ⟨K₁, hK₁⟩ := exists_abs_integral_sq_sphereAvg_sub_abs_log_le_F2b hd R
  obtain ⟨K₂, hK₂⟩ := exists_abs_integral_sq_sphereAvg_sub_sub_le_F2b hd
  set μp : Measure ℝ := volume.restrict (Ioi (0 : ℝ)) with hμp
  set c : ℝ := (2 * K₁ + K₂) / 2 with hc
  let B : ℝ × ℝ → ℝ := fun q => |radWeightF2b κ q.1| * |radWeightF2b κ q.2| *
    (c + |Real.log q.1| + |Real.log q.2|)
  have hw1 : Integrable (fun u => |radWeightF2b κ u|) μp := integrableOn_abs_radWeightF2b hd hκ
  have hw2 : Integrable (fun u => |radWeightF2b κ u| * |Real.log u|) μp := by
    have h : IntegrableOn (fun u => |radWeightF2b κ u| * |Real.log u|) (Ioi 0) := by
      simpa only [zero_add, one_mul] using integrableOn_radWeightF2b_log hd hκ 0 1
    exact h
  have hBint : Integrable B (μp.prod μp) := by
    have h1 := (hw1.mul_prod hw1).const_mul c
    have h2 := hw2.mul_prod hw1
    have h3 := hw1.mul_prod hw2
    refine ((h1.add h2).add h3).congr (Eventually.of_forall fun q => ?_)
    simp only [B, Pi.add_apply]
    ring
  refine ⟨∫ q, B q ∂(μp.prod μp), fun {Ω} _ {P} _ {h} hh t ht x hx => ?_⟩
  set ε : ℝ := Real.exp (-t) with hεdef
  have hε : 0 < ε := Real.exp_pos _
  set Y := sphScaleF2b h ε x with hY
  let Γ : ℝ × ℝ → ℝ := fun q => ∫ ω, Y ω q.1 * Y ω q.2 ∂P
  have hvar : Var[fun ω => convMollify κ ε (h ω) x; P] =
      ∫ q, radWeightF2b κ q.1 * radWeightF2b κ q.2 * Γ q ∂(μp.prod μp) := by
    rw [variance_of_integral_eq_zero (measurable_convMollify_F2b hh ε x).aemeasurable
      (integral_convMollify_F2b hd hκ hh hε x)]
    rw [← integral_mul_convMollify_F2b hd hκ hh hε hε x x]
    refine integral_congr_ae (Eventually.of_forall fun ω => ?_)
    simp only
    ring
  have h1 : ∀ᵐ q ∂(μp.prod μp), q.1 ∈ Ioi (0 : ℝ) :=
    Measure.quasiMeasurePreserving_fst.ae (ae_restrict_mem measurableSet_Ioi)
  have h2 : ∀ᵐ q ∂(μp.prod μp), q.2 ∈ Ioi (0 : ℝ) :=
    Measure.quasiMeasurePreserving_snd.ae (ae_restrict_mem measurableSet_Ioi)
  have hpt : ∀ᵐ q ∂(μp.prod μp), |Γ q - t| ≤ c + |Real.log q.1| + |Real.log q.2| := by
    filter_upwards [h1, h2] with q hq1 hq2
    have ha : (0 : ℝ) < q.1 := hq1
    have hb : (0 : ℝ) < q.2 := hq2
    have hra := hK₁ hh (mul_pos hε ha) x hx
    have hrb := hK₁ hh (mul_pos hε hb) x hx
    have hrd := hK₂ hh.1 (mul_pos hε ha) (mul_pos hε hb) x
    have hma := memLp_sphereAvg_F2b hd hh (mul_pos hε ha) x
    have hmb := memLp_sphereAvg_F2b hd hh (mul_pos hε hb) x
    have hΓ : Γ q = ((∫ ω, sphereAvg (h ω) (ε * q.1) x ^ 2 ∂P) +
        (∫ ω, sphereAvg (h ω) (ε * q.2) x ^ 2 ∂P) -
        ∫ ω, (sphereAvg (h ω) (ε * q.1) x - sphereAvg (h ω) (ε * q.2) x) ^ 2 ∂P) / 2 := by
      have hpt : ∀ ω, Y ω q.1 * Y ω q.2 = (sphereAvg (h ω) (ε * q.1) x ^ 2 +
          sphereAvg (h ω) (ε * q.2) x ^ 2 -
          (sphereAvg (h ω) (ε * q.1) x - sphereAvg (h ω) (ε * q.2) x) ^ 2) / 2 := by
        intro ω
        simp only [hY, sphScaleF2b]
        ring
      have i1 : Integrable (fun ω => sphereAvg (h ω) (ε * q.1) x ^ 2) P := hma.integrable_sq
      have i2 : Integrable (fun ω => sphereAvg (h ω) (ε * q.2) x ^ 2) P := hmb.integrable_sq
      have i12 : Integrable (fun ω => sphereAvg (h ω) (ε * q.1) x ^ 2 +
          sphereAvg (h ω) (ε * q.2) x ^ 2) P := i1.add i2
      have i3 : Integrable (fun ω => (sphereAvg (h ω) (ε * q.1) x -
          sphereAvg (h ω) (ε * q.2) x) ^ 2) P := (hma.sub hmb).integrable_sq
      simp only [Γ, hpt]
      rw [integral_div, integral_sub i12 i3, integral_add i1 i2]
    have hla : Real.log (ε * q.1) = Real.log q.1 - t := by
      rw [Real.log_mul hε.ne' ha.ne', hεdef, Real.log_exp]
      ring
    have hlb : Real.log (ε * q.2) = Real.log q.2 - t := by
      rw [Real.log_mul hε.ne' hb.ne', hεdef, Real.log_exp]
      ring
    have hlab : Real.log (ε * q.1 / (ε * q.2)) = Real.log q.1 - Real.log q.2 := by
      rw [mul_div_mul_left _ _ hε.ne', Real.log_div ha.ne' hb.ne']
    rw [hla] at hra
    rw [hlb] at hrb
    rw [hlab] at hrd
    rw [hΓ]
    exact abs_half_sub_le_F2b ht hra hrb hrd
  have hΓm : StronglyMeasurable Γ := by
    have hm : Measurable fun x' : Ω × (ℝ × ℝ) => Y x'.1 x'.2.1 * Y x'.1 x'.2.2 := by
      have hYm : Measurable fun q : Ω × ℝ => Y q.1 q.2 := measurable_sphScaleF2b hh ε x
      have hA : Measurable fun x' : Ω × (ℝ × ℝ) => Y x'.1 x'.2.1 :=
        Measurable.comp (g := fun q : Ω × ℝ => Y q.1 q.2)
          (f := fun x' : Ω × (ℝ × ℝ) => (x'.1, x'.2.1)) hYm
          (measurable_fst.prodMk measurable_snd.fst)
      have hB : Measurable fun x' : Ω × (ℝ × ℝ) => Y x'.1 x'.2.2 :=
        Measurable.comp (g := fun q : Ω × ℝ => Y q.1 q.2)
          (f := fun x' : Ω × (ℝ × ℝ) => (x'.1, x'.2.2)) hYm
          (measurable_fst.prodMk measurable_snd.snd)
      exact hA.mul hB
    exact hm.stronglyMeasurable.integral_prod_left' (μ := P)
  have hwm := measurable_radWeightF2b hd hκ
  have hF : Integrable (fun q => radWeightF2b κ q.1 * radWeightF2b κ q.2 * (Γ q - t))
      (μp.prod μp) := by
    refine hBint.mono' ?_ ?_
    · exact (((hwm.comp measurable_fst).mul (hwm.comp measurable_snd)).mul
        (hΓm.measurable.sub measurable_const)).aestronglyMeasurable
    · filter_upwards [hpt] with q hq
      rw [Real.norm_eq_abs, abs_mul, abs_mul]
      exact mul_le_mul_of_nonneg_left hq (by positivity)
  have hww : Integrable (fun q : ℝ × ℝ => radWeightF2b κ q.1 * radWeightF2b κ q.2)
      (μp.prod μp) :=
    (integrableOn_radWeightF2b hd hκ).mul_prod (integrableOn_radWeightF2b hd hκ)
  have hww1 : ∫ q, radWeightF2b κ q.1 * radWeightF2b κ q.2 ∂(μp.prod μp) = 1 := by
    rw [integral_prod_mul (μ := μp) (ν := μp), hμp, integral_radWeightF2b hd hκ, one_mul]
  have hsplit : ∫ q, radWeightF2b κ q.1 * radWeightF2b κ q.2 * Γ q ∂(μp.prod μp) =
      (∫ q, radWeightF2b κ q.1 * radWeightF2b κ q.2 * (Γ q - t) ∂(μp.prod μp)) + t := by
    have he : ∫ q, radWeightF2b κ q.1 * radWeightF2b κ q.2 * Γ q ∂(μp.prod μp) =
        ∫ q, (radWeightF2b κ q.1 * radWeightF2b κ q.2 * (Γ q - t) +
          t * (radWeightF2b κ q.1 * radWeightF2b κ q.2)) ∂(μp.prod μp) := by
      refine integral_congr_ae (Eventually.of_forall fun q => ?_)
      simp only
      ring
    rw [he, integral_add hF (hww.const_mul t), integral_const_mul, hww1, mul_one]
  rw [hvar, hsplit, add_sub_cancel_right, ← Real.norm_eq_abs]
  refine norm_integral_le_of_norm_le hBint ?_
  filter_upwards [hpt] with q hq
  rw [Real.norm_eq_abs, abs_mul, abs_mul]
  exact mul_le_mul_of_nonneg_left hq (by positivity)

end HigherDimLFPPAS.Gauss
