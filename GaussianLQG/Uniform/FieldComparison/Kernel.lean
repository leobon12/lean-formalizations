import LQGMetric.Papers.DG.L3_1C3
import LQGMetric.Field.HeatKernelSquareCK
import LQGMetric.Field.HeatMollifyUnif

/-!
# The white-noise kernel of the heat-mollified field (Route U, U14; OP-4, kernel part)

`LQGMetric` builds the whole-plane GFF from a white noise `W` by `h₀(φ) = W(kerFun φ)` with
`kerFun g (t, y) = √π 1_{t>0} ∫ g(u) (p_{t/2}(u, y) − 1_{t>1} p_{t/2}(0, y)) du`
(`LQGMetric.GFFExist`), and defines the heat mollification as the limit of truncated pairings,
`h*_ε(z) = lim_m h(p_{ε²/2}(z, ·) χ_m)` (`LQGMetric.heatMollify`). For `g = p_{ε²/2}(z, ·)` the
Chapman–Kolmogorov identity gives the kernel

  `molKer ε z (t, y) = √π 1_{t>0} (p_{ε²/2 + t/2}(z, y) − 1_{t>1} p_{t/2}(0, y))`,

i.e. the semigroup form `p_{(t+ε²)/2}` of blueprint A.6 / audit A5, Lemma A6.2.

* `tendsto_kerFun_heatTrunc`: pointwise convergence `kerFun (p_{ε²/2}(z,·) χ_m) → molKer ε z`
  (dominated convergence, `HeatSq.integral_heatKernel_mul_heatKernel_ck`);
* `norm_testL2_heatDiff_le`: `‖testL2 (heatDiff ε²/2 z m)‖ ≤ 2π K (m+3)³ e^{−m}` (the `L²` bound
  `BddSupp.memLp_kerFun` for the truncation differences);
* `memLp_molKer`, `molKerL2`, `tendsto_testL2_heatTrunc`: the truncated kernels converge in
  `L²(ℝ × ℂ)` to `molKer ε z`, for every `ε ≠ 0`;
* `circKerL2`, `tendsto_testL2_circBump`: the `L²` class of the circle-average kernel
  `DG.circKerLim 0 1` (`√π 1_{t>0} (∫ p_{t/2}(u, y) σ(du) − 1_{t>1} p_{t/2}(0, y))`, `σ` uniform
  on the unit circle) and the convergence of the mollified circle kernels to it.

Own elementary arguments (routine measure theory).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped ENNReal

namespace GaussianLQG
namespace FieldCmp

open LQGMetric LQGMetric.WhiteNoise LQGMetric.GFFExist

/-! ### The kernel -/

/-- The white-noise kernel of `h*_ε(z)` for `LQGMetric`'s white-noise GFF:
`√π 1_{t>0} (p_{ε²/2 + t/2}(z, y) − 1_{t>1} p_{t/2}(0, y))`. -/
def molKer (ε : ℝ) (z : ℂ) (q : ℝ × ℂ) : ℝ :=
  Real.sqrt Real.pi * (Ioi (0 : ℝ)).indicator (fun t => heatKernel (ε ^ 2 / 2 + t / 2) z q.2 -
    (Ioi (1 : ℝ)).indicator (fun _ => heatKernel (t / 2) 0 q.2) t) q.1

/-- **Pointwise limit of the truncated kernels.** -/
lemma tendsto_kerFun_heatTrunc {ε : ℝ} (hε : ε ≠ 0) (z : ℂ) (q : ℝ × ℂ) :
    Tendsto (fun m : ℕ => kerFun (heatTrunc (ε ^ 2 / 2) z m) q) atTop (𝓝 (molKer ε z q)) := by
  set s := ε ^ 2 / 2 with hs_def
  have hs : 0 < s := by positivity
  unfold kerFun molKer
  by_cases hq : q.1 ∈ Ioi (0 : ℝ)
  · simp only [indicator_of_mem hq]
    refine Tendsto.const_mul _ ?_
    have ht : 0 < q.1 := hq
    have ht2 : 0 < q.1 / 2 := by linarith
    set c := (Ioi (1 : ℝ)).indicator (fun _ => heatKernel (q.1 / 2) 0 q.2) q.1 with hc
    set F : C(ℂ, ℝ) := ⟨fun u => heatKernel (q.1 / 2) u q.2 - c,
      (DG.continuous_heatKernel_left q.2).sub continuous_const⟩ with hF
    have e : ∀ m : ℕ, kerInner (heatTrunc s z m) q.1 q.2 = ofCont F (heatTrunc s z m) :=
      fun m => by rw [ofCont_apply_heat]; rfl
    simp_rw [e]
    have hM : ∀ w, |F w| ≤ (2 * Real.pi * (q.1 / 2))⁻¹ + |c| := fun w => by
      show |heatKernel (q.1 / 2) w q.2 - c| ≤ _
      refine (abs_sub _ _).trans (add_le_add ?_ le_rfl)
      rw [abs_of_nonneg (heatKernel_nonneg _ ht2.le _ _)]
      exact GFFExist.heatKernel_le _ ht2 _ _
    have hi := integrable_heatKernel_mul_of_bdd F _ hM s hs z
    have hl := tendsto_ofCont_heatTrunc F s hs z hi
    convert hl using 2
    show heatKernel (s + q.1 / 2) z q.2 - c = ∫ w, heatKernel s z w * (heatKernel (q.1 / 2) w q.2 - c)
    simp_rw [mul_sub]
    rw [integral_sub (HeatSq.integrable_heatKernel_mul_heatKernel_ck s (q.1 / 2) hs ht2 z q.2)
      ((integrable_heatKernel s hs z).mul_const c),
      HeatSq.integral_heatKernel_mul_heatKernel_ck s (q.1 / 2) hs ht2 z q.2, integral_mul_const,
      integral_heatKernel s hs z, one_mul]
  · simp only [indicator_of_notMem hq, mul_zero]
    exact tendsto_const_nhds

/-! ### `testL2` is additive, and the `L²` bound for the truncation differences -/

lemma testL2_sub (φ ψ : TestC) : testL2 (φ - ψ) = testL2 φ - testL2 ψ := by
  obtain ⟨M, R, -, hφ⟩ := testC_bddSupp φ
  obtain ⟨M', R', -, hψ⟩ := testC_bddSupp ψ
  refine Lp.ext ?_
  filter_upwards [(memLp_kerFun_test (φ - ψ)).coeFn_toLp, (memLp_kerFun_test φ).coeFn_toLp,
    (memLp_kerFun_test ψ).coeFn_toLp, Lp.coeFn_sub (testL2 φ) (testL2 ψ)] with q h1 h2 h3 h4
  have e1 : (testL2 (φ - ψ) : ℝ × ℂ → ℝ) q = kerFun (⇑(φ - ψ)) q := h1
  have e2 : (testL2 φ : ℝ × ℂ → ℝ) q = kerFun φ q := h2
  have e3 : (testL2 ψ : ℝ × ℂ → ℝ) q = kerFun ψ q := h3
  rw [e1, h4, Pi.sub_apply, e2, e3]
  exact kerFun_sub hφ hψ q

lemma norm_testL2_sq_le (φ : TestC) {M R : ℝ} (hφ : BddSupp φ M R) :
    ‖testL2 φ‖ ^ 2 ≤ Real.pi * (∫ u, φ u ^ 2) + (∫ u, |φ u|) * (∫ u, |φ u| * ‖u‖ ^ 2) / 2 := by
  rw [DG.norm_sq_eq_integral]
  have e : (fun q => ((testL2 φ : ℝ × ℂ → ℝ) q) ^ 2) =ᵐ[volume] fun q => kerFun φ q ^ 2 := by
    filter_upwards [(memLp_kerFun_test φ).coeFn_toLp] with q hq
    have e2 : (testL2 φ : ℝ × ℂ → ℝ) q = kerFun φ q := hq
    rw [e2]
  rw [integral_congr_ae e]
  exact hφ.memLp_kerFun.2

/-- The constant `K = (2πs)⁻¹ e^{s/2 + |z|}` of the truncation differences. -/
def truncConst (s : ℝ) (z : ℂ) : ℝ := (2 * Real.pi * s)⁻¹ * Real.exp (s / 2 + ‖z‖)

lemma truncConst_nonneg {s : ℝ} (hs : 0 < s) (z : ℂ) : 0 ≤ truncConst s z := by
  unfold truncConst; positivity

lemma bddSupp_heatDiff {s : ℝ} (hs : 0 < s) (z : ℂ) (m : ℕ) :
    BddSupp (heatDiff s z m) (truncConst s z * Real.exp (-(m : ℝ))) ((m : ℝ) + 3) where
  meas := (heatDiff s z m).continuous.measurable
  bdd u := abs_heatTrunc_succ_sub_le s hs z ‖z‖ le_rfl m u
  supp u hu := heatTrunc_succ_sub_eq_zero' s z m u hu.le

/-- `|∫ φ| ≤ M π R²` for a function bounded by `M` vanishing outside `B̄_R`; specialized to the
three integrals of `BddSupp.memLp_kerFun`. -/
lemma integrals_le_of_bddSupp {g : ℂ → ℝ} {M R : ℝ} (hg : BddSupp g M R) (hR : 0 ≤ R) :
    (∫ u, g u ^ 2) ≤ M ^ 2 * (Real.pi * R ^ 2) ∧ (∫ u, |g u|) ≤ M * (Real.pi * R ^ 2) ∧
      (∫ u, |g u| * ‖u‖ ^ 2) ≤ (M * R ^ 2) * (Real.pi * R ^ 2) := by
  have hM : 0 ≤ M := (abs_nonneg _).trans (hg.bdd 0)
  refine ⟨?_, ?_, ?_⟩
  · refine (le_abs_self _).trans (abs_integral_le_of_bound hR (fun x => ?_) (fun x hx => ?_))
    · rw [abs_pow]; exact pow_le_pow_left₀ (abs_nonneg _) (hg.bdd x) 2
    · rw [hg.supp x hx]; ring
  · refine (le_abs_self _).trans (abs_integral_le_of_bound hR (fun x => ?_) (fun x hx => ?_))
    · rw [abs_abs]; exact hg.bdd x
    · rw [hg.supp x hx, abs_zero]
  · refine (le_abs_self _).trans (abs_integral_le_of_bound hR (fun x => ?_) (fun x hx => ?_))
    · rw [abs_mul, abs_abs, abs_pow, abs_norm]
      by_cases hx : ‖x‖ ≤ R
      · exact mul_le_mul (hg.bdd x) (pow_le_pow_left₀ (norm_nonneg _) hx 2) (by positivity) hM
      · rw [hg.supp x (lt_of_not_ge hx), abs_zero, zero_mul]; positivity
    · rw [hg.supp x hx, abs_zero, zero_mul]

/-- **`L²` bound for the truncation differences**: `‖testL2 D_m‖ ≤ 2π K (m+3)³ e^{−m}`. -/
lemma norm_testL2_heatDiff_le {s : ℝ} (hs : 0 < s) (z : ℂ) (m : ℕ) :
    ‖testL2 (heatDiff s z m)‖ ≤
      2 * Real.pi * truncConst s z * (((m : ℝ) + 3) ^ 3 * Real.exp (-(m : ℝ))) := by
  set M := truncConst s z * Real.exp (-(m : ℝ)) with hMdef
  set R : ℝ := (m : ℝ) + 3 with hRdef
  have hM : 0 ≤ M := mul_nonneg (truncConst_nonneg hs z) (Real.exp_pos _).le
  have hR1 : 1 ≤ R := by simp only [hRdef]; have := Nat.cast_nonneg (α := ℝ) m; linarith
  have hR0 : 0 ≤ R := by linarith
  have hg := bddSupp_heatDiff hs z m
  obtain ⟨h1, h2, h3⟩ := integrals_le_of_bddSupp hg hR0
  have hb := norm_testL2_sq_le (heatDiff s z m) hg
  have hpi := Real.pi_pos
  have hA : 0 ≤ ∫ u, |(heatDiff s z m : ℂ → ℝ) u| := integral_nonneg fun _ => abs_nonneg _
  have hR26 : R ^ 2 ≤ R ^ 6 := pow_le_pow_right₀ hR1 (by norm_num)
  have key : ‖testL2 (heatDiff s z m)‖ ^ 2 ≤ (2 * Real.pi * M * R ^ 3) ^ 2 := by
    refine hb.trans ?_
    have t1 : Real.pi * (∫ u, (heatDiff s z m : ℂ → ℝ) u ^ 2) ≤
        Real.pi * (M ^ 2 * (Real.pi * R ^ 2)) := mul_le_mul_of_nonneg_left h1 hpi.le
    have t2 : (∫ u, |(heatDiff s z m : ℂ → ℝ) u|) *
        (∫ u, |(heatDiff s z m : ℂ → ℝ) u| * ‖u‖ ^ 2) ≤
        (M * (Real.pi * R ^ 2)) * ((M * R ^ 2) * (Real.pi * R ^ 2)) :=
      mul_le_mul h2 h3 (integral_nonneg fun _ => by positivity) (by positivity)
    have t3 : Real.pi * (M ^ 2 * (Real.pi * R ^ 2)) ≤ Real.pi ^ 2 * M ^ 2 * R ^ 6 := by
      have : Real.pi * (M ^ 2 * (Real.pi * R ^ 2)) = Real.pi ^ 2 * M ^ 2 * R ^ 2 := by ring
      rw [this]
      exact mul_le_mul_of_nonneg_left hR26 (by positivity)
    have t4 : (M * (Real.pi * R ^ 2)) * ((M * R ^ 2) * (Real.pi * R ^ 2)) / 2 =
        Real.pi ^ 2 * M ^ 2 * R ^ 6 / 2 := by ring
    have t5 : (2 * Real.pi * M * R ^ 3) ^ 2 = 4 * (Real.pi ^ 2 * M ^ 2 * R ^ 6) := by ring
    have hX : 0 ≤ Real.pi ^ 2 * M ^ 2 * R ^ 6 := by positivity
    rw [t5]
    have := div_le_div_of_nonneg_right t2 (by norm_num : (0 : ℝ) ≤ 2)
    rw [t4] at this
    linarith
  have hpos : 0 ≤ 2 * Real.pi * M * R ^ 3 := by positivity
  have hle := (pow_le_pow_iff_left₀ (norm_nonneg _) hpos two_ne_zero).1 key
  refine hle.trans (le_of_eq ?_)
  simp only [hMdef, hRdef]
  ring

lemma summable_heatDiff_bound {s : ℝ} (z : ℂ) :
    Summable fun m : ℕ =>
      2 * Real.pi * truncConst s z * (((m : ℝ) + 3) ^ 3 * Real.exp (-(m : ℝ))) :=
  (summable_shift_pow_mul_exp 3).mul_left _

/-! ### `L²` convergence of the truncated kernels -/

lemma cauchySeq_testL2_heatTrunc {s : ℝ} (hs : 0 < s) (z : ℂ) :
    CauchySeq fun m : ℕ => testL2 (heatTrunc s z m) := by
  refine cauchySeq_of_dist_le_of_summable _ (fun m => ?_) (summable_heatDiff_bound (s := s) z)
  rw [dist_comm, dist_eq_norm, ← testL2_sub]
  exact norm_testL2_heatDiff_le hs z m

lemma exists_tendsto_testL2_heatTrunc {ε : ℝ} (hε : ε ≠ 0) (z : ℂ) :
    ∃ K : WNSpace, Tendsto (fun m : ℕ => testL2 (heatTrunc (ε ^ 2 / 2) z m)) atTop (𝓝 K) ∧
      (K : ℝ × ℂ → ℝ) =ᵐ[volume] molKer ε z := by
  obtain ⟨K, hK⟩ := cauchySeq_tendsto_of_complete
    (cauchySeq_testL2_heatTrunc (s := ε ^ 2 / 2) (by positivity) z)
  refine ⟨K, hK, ?_⟩
  obtain ⟨ns, hns, hae'⟩ := (tendstoInMeasure_of_tendsto_Lp hK).exists_seq_tendsto_ae
  have hc : ∀ᵐ q ∂(volume : Measure (ℝ × ℂ)), ∀ m : ℕ,
      (testL2 (heatTrunc (ε ^ 2 / 2) z m) : ℝ × ℂ → ℝ) q =
        kerFun (heatTrunc (ε ^ 2 / 2) z m) q :=
    ae_all_iff.2 fun m => (memLp_kerFun_test _).coeFn_toLp
  filter_upwards [hae', hc] with q h1 h2
  simp_rw [h2] at h1
  exact tendsto_nhds_unique h1 ((tendsto_kerFun_heatTrunc hε z q).comp hns.tendsto_atTop)

/-- `molKer ε z ∈ L²(ℝ × ℂ)` for `ε ≠ 0`. -/
theorem memLp_molKer {ε : ℝ} (hε : ε ≠ 0) (z : ℂ) :
    MemLp (molKer ε z) 2 (volume : Measure (ℝ × ℂ)) := by
  obtain ⟨K, -, hK⟩ := exists_tendsto_testL2_heatTrunc hε z
  exact (Lp.memLp K).ae_eq hK

/-- The `L²` class of `molKer ε z` (junk `0` for `ε = 0`, where it is not square integrable). -/
def molKerL2 (ε : ℝ) (z : ℂ) : WNSpace :=
  if hε : ε ≠ 0 then (memLp_molKer hε z).toLp _ else 0

lemma coeFn_molKerL2 {ε : ℝ} (hε : ε ≠ 0) (z : ℂ) :
    (molKerL2 ε z : ℝ × ℂ → ℝ) =ᵐ[volume] molKer ε z := by
  rw [molKerL2, dite_eq_left_of_eq_true (eq_true hε)]
  exact (memLp_molKer hε z).coeFn_toLp

/-- **`L²` convergence**: `testL2 (p_{ε²/2}(z, ·) χ_m) → molKerL2 ε z`. -/
theorem tendsto_testL2_heatTrunc {ε : ℝ} (hε : ε ≠ 0) (z : ℂ) :
    Tendsto (fun m : ℕ => testL2 (heatTrunc (ε ^ 2 / 2) z m)) atTop (𝓝 (molKerL2 ε z)) := by
  obtain ⟨K, hK, hKe⟩ := exists_tendsto_testL2_heatTrunc hε z
  have e : K = molKerL2 ε z := Lp.ext (hKe.trans (coeFn_molKerL2 hε z).symm)
  rwa [← e]

/-! ### The circle-average kernel -/

/-- The circle-average kernel `DG.circKerLim 0 1` is square integrable (the `L²` limit of the
mollified circle kernels; deterministic, obtained from any white-noise GFF). -/
theorem memLp_circKerLim : MemLp (DG.circKerLim 0 1) 2 (volume : Measure (ℝ × ℂ)) := by
  obtain ⟨W, h₀, hW, hh, hae⟩ := DG.exists_wn_wholePlaneGFF
  obtain ⟨K, hK⟩ := cauchySeq_tendsto_of_complete
    (DG.cauchySeq_testL2_circBump hW hh hae 0 one_pos)
  exact (Lp.memLp K).ae_eq (DG.ae_eq_circKerLim 0 one_pos hK)

/-- The `L²` class of the unit-circle-average kernel
`√π 1_{t>0} (∫ p_{t/2}(u, y) σ(du) − 1_{t>1} p_{t/2}(0, y))`. -/
def circKerL2 : WNSpace := memLp_circKerLim.toLp _

lemma coeFn_circKerL2 : (circKerL2 : ℝ × ℂ → ℝ) =ᵐ[volume] DG.circKerLim 0 1 :=
  memLp_circKerLim.coeFn_toLp

/-- The mollified unit-circle kernels converge to `circKerL2` in `L²`. -/
theorem tendsto_testL2_circBump :
    Tendsto (fun n => testL2 (CircleAvg.circBump n 0 1)) atTop (𝓝 circKerL2) := by
  obtain ⟨W, h₀, hW, hh, hae⟩ := DG.exists_wn_wholePlaneGFF
  obtain ⟨K, hK⟩ := cauchySeq_tendsto_of_complete
    (DG.cauchySeq_testL2_circBump hW hh hae 0 one_pos)
  have e : K = circKerL2 := Lp.ext ((DG.ae_eq_circKerLim 0 one_pos hK).trans coeFn_circKerL2.symm)
  rwa [← e]

end FieldCmp
end GaussianLQG
