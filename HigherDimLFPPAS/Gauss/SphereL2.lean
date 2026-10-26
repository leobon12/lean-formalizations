import HigherDimLQGMetric.Sphere.Var
import HigherDimLQGMetric.Sphere.Cov
import HigherDimLQGMetric.Sphere.Cont
import HigherDimLQGMetric.Frozen.IsNormalizedLGF

/-!
# Second moments of sphere averages of a normalized LGF (packet F2b)

For a whole-space LGF `h` normalized by `h₁(0) = 0`, the sphere averages `h_r(z)` (`r > 0`) are
centred, square integrable, and

* `E (h_r(z) - h_s(w))² ≤ C (‖z - w‖ + |r - s|) / min(r, s)` (`integral_sq_sphereAvg_sub_le_F2b`);
* `|E h_r(z)² - |log r|| ≤ K` for `‖z‖ ≤ L` (`abs_integral_sq_sphereAvg_sub_abs_log_le_F2b`);
* `|E (h_r(z) - h_s(z))² - |log (r/s)|| ≤ K` (`abs_integral_sq_sphereAvg_sub_sub_le_F2b`).

They are the sphere-average inputs of the planning audit MA3, Details P3 (proof 2) and P4.1′, taken
from the host's `exists_integral_sq_sphIncProc_le` and `exists_abs_variance_sphereAvg_sub_sub_log_le`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory

namespace HigherDimLFPPAS.Gauss

open HigherDimLQGMetric
open HigherDimLFPP (Rd)

variable {d : ℕ}

/-- The point `(0, r, z)` of the sphere-average process (no mollification). -/
def sphPt0F2b (r : ℝ) (hr : 0 < r) (z : Rd d) : SphPt d := ⟨0, r, z, le_rfl, hr⟩

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {h : Ω → DistRd d}

omit [MeasurableSpace Ω] in
lemma sphIncProc_sphPt0F2b {r s : ℝ} (hr : 0 < r) (hs : 0 < s) (z w : Rd d) :
    sphIncProc h (.inl (sphPt0F2b r hr z, sphPt0F2b s hs w)) =
      fun ω => sphereAvg (h ω) r z - sphereAvg (h ω) s w := by
  funext ω
  simp only [sphIncProc, sphPt0F2b, sphProc_zero]

/-- Differences of sphere averages are centred Gaussian with the host's `L²` increment bound. -/
theorem exists_sphereAvg_sub_facts_F2b (hd : 2 ≤ d) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {h : Ω → DistRd d},
      IsWholeSpaceLGF h P → ∀ {r s : ℝ}, 0 < r → 0 < s → ∀ z w : Rd d,
        HasGaussianLaw (fun ω => sphereAvg (h ω) r z - sphereAvg (h ω) s w) P ∧
        ∫ ω, (sphereAvg (h ω) r z - sphereAvg (h ω) s w) ∂P = 0 ∧
        ∫ ω, (sphereAvg (h ω) r z - sphereAvg (h ω) s w) ^ 2 ∂P ≤
          C * (‖z - w‖ + |r - s|) / min r s := by
  obtain ⟨C, hC0, hC⟩ := HigherDimLQGMetric.exists_integral_sq_sphIncProc_le hd
  refine ⟨C, hC0, fun {Ω} _ {P} {h} hh {r s} hr hs z w => ?_⟩
  obtain ⟨hG, h0, h2, hle⟩ := hC hh (sphPt0F2b r hr z) (sphPt0F2b s hs w)
  rw [sphIncProc_sphPt0F2b hr hs z w] at hG h0 h2
  refine ⟨hG, h0, ?_⟩
  rw [h2]
  refine hle.trans (le_of_eq ?_)
  simp only [SphPt.dist, sphPt0F2b, sub_self, abs_zero, add_zero]

section Normalized

variable [IsProbabilityMeasure P]

omit [IsProbabilityMeasure P] in
lemma ae_sphereAvg_eq_sub_F2b (hh : IsNormalizedLGF h P) (r : ℝ) (z : Rd d) :
    (fun ω => sphereAvg (h ω) r z) =ᵐ[P] fun ω => sphereAvg (h ω) r z - sphereAvg (h ω) 1 0 := by
  filter_upwards [hh.2] with ω hω
  rw [hω, sub_zero]

omit [IsProbabilityMeasure P] in
/-- Sphere averages of a normalized LGF are centred Gaussian. -/
theorem sphereAvg_facts_F2b (hd : 2 ≤ d) (hh : IsNormalizedLGF h P) {r : ℝ} (hr : 0 < r)
    (z : Rd d) :
    HasGaussianLaw (fun ω => sphereAvg (h ω) r z) P ∧
      ∫ ω, sphereAvg (h ω) r z ∂P = 0 ∧
      ∫ ω, sphereAvg (h ω) r z ^ 2 ∂P =
        Var[fun ω => sphereAvg (h ω) r z - sphereAvg (h ω) 1 0; P] := by
  obtain ⟨C, -, hC⟩ := exists_sphereAvg_sub_facts_F2b hd
  obtain ⟨hG, h0, -⟩ := hC hh.1 hr one_pos z 0
  have he := ae_sphereAvg_eq_sub_F2b hh r z
  refine ⟨hG.congr he.symm, ?_, ?_⟩
  · rw [integral_congr_ae he, h0]
  · rw [variance_of_integral_eq_zero hG.aemeasurable h0]
    refine integral_congr_ae ?_
    filter_upwards [hh.2] with ω hω
    rw [hω, sub_zero]

omit [IsProbabilityMeasure P] in
lemma memLp_sphereAvg_F2b (hd : 2 ≤ d) (hh : IsNormalizedLGF h P) {r : ℝ} (hr : 0 < r)
    (z : Rd d) : MemLp (fun ω => sphereAvg (h ω) r z) 2 P :=
  (sphereAvg_facts_F2b hd hh hr z).1.memLp_two

omit [IsProbabilityMeasure P] in
lemma integral_sphereAvg_F2b (hd : 2 ≤ d) (hh : IsNormalizedLGF h P) {r : ℝ} (hr : 0 < r)
    (z : Rd d) : ∫ ω, sphereAvg (h ω) r z ∂P = 0 :=
  (sphereAvg_facts_F2b hd hh hr z).2.1

/-- The `L²` increment bound for sphere averages. -/
theorem exists_integral_sq_sphereAvg_sub_le_F2b (hd : 2 ≤ d) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {h : Ω → DistRd d},
      IsWholeSpaceLGF h P → ∀ {r s : ℝ}, 0 < r → 0 < s → ∀ z w : Rd d,
        ∫ ω, (sphereAvg (h ω) r z - sphereAvg (h ω) s w) ^ 2 ∂P ≤
          C * (‖z - w‖ + |r - s|) / min r s := by
  obtain ⟨C, hC0, hC⟩ := exists_sphereAvg_sub_facts_F2b hd
  exact ⟨C, hC0, fun {Ω} _ {P} {h} hh {r s} hr hs z w => (hC hh hr hs z w).2.2⟩

/-- Logarithmic second moment of a normalized sphere average (both small and large radii). -/
theorem exists_abs_integral_sq_sphereAvg_sub_abs_log_le_F2b (hd : 2 ≤ d) (L : ℝ) :
    ∃ K : ℝ, ∀ {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
      {h : Ω → DistRd d}, IsNormalizedLGF h P → ∀ {r : ℝ}, 0 < r → ∀ z : Rd d, ‖z‖ ≤ L →
        |∫ ω, sphereAvg (h ω) r z ^ 2 ∂P - (|Real.log r|)| ≤ K := by
  obtain ⟨K, hK⟩ := HigherDimLQGMetric.exists_abs_variance_sphereAvg_sub_sub_log_le hd L
  refine ⟨K, fun {Ω} _ {P} _ {h} hh {r} hr z hz => ?_⟩
  rw [(sphereAvg_facts_F2b hd hh hr z).2.2]
  rcases le_total r 1 with hr1 | hr1
  · have hzw : ‖z - 0‖ ≤ L * 1 := by simpa using hz
    have h1 := hK hh.1 hr hr1 z 0 hzw
    have hlog : Real.log (1 / r) = |Real.log r| := by
      rw [one_div, Real.log_inv, abs_of_nonpos (Real.log_nonpos hr.le hr1)]
    rwa [hlog] at h1
  · have hzw : ‖(0 : Rd d) - z‖ ≤ L * r := by
      rw [zero_sub, norm_neg]
      rcases le_total 0 L with hL | hL
      · nlinarith [norm_nonneg z]
      · nlinarith [norm_nonneg z]
    have h1 := hK hh.1 one_pos hr1 0 z hzw
    have hneg : Var[fun ω => sphereAvg (h ω) 1 0 - sphereAvg (h ω) r z; P] =
        Var[fun ω => sphereAvg (h ω) r z - sphereAvg (h ω) 1 0; P] := by
      rw [← variance_fun_neg]
      congr 1
      funext ω
      ring
    have hlog : Real.log (r / 1) = |Real.log r| := by
      rw [div_one, abs_of_nonneg (Real.log_nonneg hr1)]
    rwa [hneg, hlog] at h1

/-- Logarithmic second moment of a radial increment of sphere averages. -/
theorem exists_abs_integral_sq_sphereAvg_sub_sub_le_F2b (hd : 2 ≤ d) :
    ∃ K : ℝ, ∀ {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
      {h : Ω → DistRd d}, IsWholeSpaceLGF h P → ∀ {r s : ℝ}, 0 < r → 0 < s → ∀ z : Rd d,
        |∫ ω, (sphereAvg (h ω) r z - sphereAvg (h ω) s z) ^ 2 ∂P - (|Real.log (r / s)|)| ≤ K := by
  obtain ⟨K, hK⟩ := HigherDimLQGMetric.exists_abs_variance_sphereAvg_sub_sub_log_le hd 0
  obtain ⟨C, -, hC⟩ := exists_sphereAvg_sub_facts_F2b hd
  refine ⟨K, fun {Ω} _ {P} _ {h} hh {r s} hr hs z => ?_⟩
  have hvar : ∀ {a b : ℝ}, 0 < a → 0 < b →
      ∫ ω, (sphereAvg (h ω) a z - sphereAvg (h ω) b z) ^ 2 ∂P =
        Var[fun ω => sphereAvg (h ω) a z - sphereAvg (h ω) b z; P] := by
    intro a b ha hb
    obtain ⟨hG, h0, -⟩ := hC hh ha hb z z
    rw [variance_of_integral_eq_zero hG.aemeasurable h0]
  have hzz : ‖z - z‖ ≤ 0 * s := by simp
  rcases le_total r s with hrs | hrs
  · have h1 := hK hh hr hrs z z (by simp)
    have hlog : Real.log (s / r) = |Real.log (r / s)| := by
      rw [abs_of_nonpos (Real.log_nonpos (div_pos hr hs).le ((div_le_one hs).2 hrs)),
        ← Real.log_inv, inv_div]
    rw [hvar hr hs]
    rwa [hlog] at h1
  · have h1 := hK hh hs hrs z z (by simp)
    have hlog : Real.log (r / s) = |Real.log (r / s)| :=
      (abs_of_nonneg (Real.log_nonneg ((one_le_div hs).2 hrs))).symm
    have hneg : Var[fun ω => sphereAvg (h ω) s z - sphereAvg (h ω) r z; P] =
        Var[fun ω => sphereAvg (h ω) r z - sphereAvg (h ω) s z; P] := by
      rw [← variance_fun_neg]
      congr 1
      funext ω
      ring
    rw [hvar hr hs, ← hneg]
    rw [hlog] at h1
    exact h1

end Normalized

end HigherDimLFPPAS.Gauss
