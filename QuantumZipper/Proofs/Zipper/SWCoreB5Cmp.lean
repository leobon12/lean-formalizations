import QuantumZipper.Proofs.Zipper.SWCoreB5Data

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# SWC-B5 (2): the per-map comparison, fine partitions, window indices

Task SWC-B5 (`handoff/SW-CORE.md`). Deterministic tools for the uniform transport:

* `cmp_of_dist` — for one map and one scale, if the distortion `Δ_k` is `≤ 2η/γ` on `[a',b']`,
  the `f`-mass of the approximation of `x ∘ ψ + Q log|ψ'|` is within a factor `e^η` of
  `A = ∫_{[a',b']} |ψ'| f · bdryDens(x, 2^{-k}|ψ'|, ψ)` (the density identity `F1.dens_split`,
  exactly as in `F1.tendsto_lintegral_coordChange_of_good`, SW proof of Thm 4.3, p. 19 / p. 12);
* `exists_fine_partition` — a finite continuous partition of unity of `[-M,M]` with pieces of
  radius `h`;
* `exists_win_index` — a scale piece of logarithmic width `≤ log 2 / N` lies in one window of two
  lattice steps (the window arithmetic of `E6.mem_win_of_scale`).

Own elementary bookkeeping.
-/

noncomputable section

open MeasureTheory Filter Set Metric
open scoped Topology ENNReal

namespace QuantumZipper
namespace SWCore

/-- The comparison integral `A = ∫_{[a',b']} |ψ'| f · bdryDens(x, 2^{-k}|ψ'|, Re ψ)`. -/
def cmpInt (γ : ℝ) (x : FieldSample) (ψ : ℂ → ℂ) (f : ℝ → ℝ) (a' b' : ℝ) (k : ℕ) : ℝ≥0∞ :=
  ∫⁻ t in Icc a' b', ENNReal.ofReal
    (‖deriv ψ t‖ * f t * bdryDens γ x (radius k * ‖deriv ψ t‖) (ψ t).re)

/-- **Per-map comparison** under a distortion bound. -/
theorem cmp_of_dist {γ η : ℝ} (hγ : 0 < γ) {x : FieldSample} {ψ : ℂ → ℂ} {k : ℕ}
    {f : ℝ → ℝ} {a' b' : ℝ} (hf : Continuous f) (hf0 : ∀ t, 0 ≤ f t)
    (hfs : ∀ t, f t ≠ 0 → t ∈ Icc a' b') (hd : ∀ t ∈ Icc a' b', 0 < ‖deriv ψ t‖)
    (hΔ : ∀ t ∈ Icc a' b', |avgReg (coordChange x ψ (Qc γ)) k (t : ℂ) -
      Qc γ * Real.log ‖deriv ψ t‖ -
        evalReg x (foldedCircle (((ψ t).re : ℝ) : ℂ) (radius k * ‖deriv ψ t‖))| ≤ 2 * η / γ) :
    ∫⁻ t, ENNReal.ofReal (f t) ∂(bdryApprox γ (coordChange x ψ (Qc γ)) k) ≤
        ENNReal.ofReal (Real.exp η) * cmpInt γ x ψ f a' b' k ∧
      cmpInt γ x ψ f a' b' k ≤ ENNReal.ofReal (Real.exp η) *
        ∫⁻ t, ENNReal.ofReal (f t) ∂(bdryApprox γ (coordChange x ψ (Qc γ)) k) := by
  set y := coordChange x ψ (Qc γ) with hy
  set D : ℝ → ℝ := fun t => radius k ^ (γ ^ 2 / 4) * Real.exp (γ / 2 * avgReg y k (t : ℂ))
    with hD
  set Bt : ℝ → ℝ := fun t => bdryDens γ x (radius k * ‖deriv ψ t‖) (ψ t).re with hBt
  have ha : ∫⁻ t, ENNReal.ofReal (f t) ∂(bdryApprox γ y k) =
      ∫⁻ t in Icc a' b', ENNReal.ofReal (D t) * ENNReal.ofReal (f t) := by
    unfold bdryApprox
    have hm : Measurable fun t => ENNReal.ofReal (f t) :=
      ENNReal.measurable_ofReal.comp hf.measurable
    rw [lintegral_withDensity_eq_lintegral_mul _ (F1.measurable_bdryApprox_dens γ y k) hm]
    refine (setLIntegral_eq_of_support_subset ?_).symm
    intro t ht
    by_contra hct
    apply ht
    have : f t = 0 := by
      by_contra h0; exact hct (hfs t h0)
    simp [this]
  have hpt : ∀ t ∈ Icc a' b',
      ENNReal.ofReal (D t) * ENNReal.ofReal (f t) ≤ ENNReal.ofReal (Real.exp η) *
        ENNReal.ofReal (‖deriv ψ t‖ * f t * Bt t) ∧
      ENNReal.ofReal (‖deriv ψ t‖ * f t * Bt t) ≤
        ENNReal.ofReal (Real.exp η) * (ENNReal.ofReal (D t) * ENNReal.ofReal (f t)) := by
    intro t ht
    have hdpos := hd t ht
    set d := ‖deriv ψ t‖ with hdd
    set Δ := avgReg y k (t : ℂ) - Qc γ * Real.log d -
      evalReg x (foldedCircle (((ψ t).re : ℝ) : ℂ) (radius k * d)) with hΔd
    have hΔle : |Δ| ≤ 2 * η / γ := hΔ t ht
    have hsplit : D t = d * Bt t * Real.exp (γ / 2 * Δ) :=
      F1.dens_split hγ.ne' (radius_pos k) hdpos
    have hBnn : 0 ≤ Bt t := GoodSample.bdryDens_nonneg γ x (mul_pos (radius_pos k) hdpos) _
    have hP : 0 ≤ d * Bt t * f t := mul_nonneg (mul_nonneg hdpos.le hBnn) (hf0 t)
    have hγΔ : |γ / 2 * Δ| ≤ η := by
      rw [abs_mul, abs_of_pos (by positivity : (0 : ℝ) < γ / 2)]
      calc γ / 2 * |Δ| ≤ γ / 2 * (2 * η / γ) := by gcongr
        _ = η := by field_simp
    have hDnn : 0 ≤ D t := by
      rw [hsplit]; exact mul_nonneg (mul_nonneg hdpos.le hBnn) (Real.exp_pos _).le
    rw [← ENNReal.ofReal_mul hDnn, ← ENNReal.ofReal_mul (Real.exp_pos _).le,
      ← ENNReal.ofReal_mul (Real.exp_pos _).le]
    constructor
    · apply ENNReal.ofReal_le_ofReal
      rw [hsplit]
      have he : Real.exp (γ / 2 * Δ) ≤ Real.exp η := Real.exp_le_exp.2 (le_of_abs_le hγΔ)
      calc d * Bt t * Real.exp (γ / 2 * Δ) * f t = (d * Bt t * f t) * Real.exp (γ / 2 * Δ)
            := by ring
        _ ≤ (d * Bt t * f t) * Real.exp η := by gcongr
        _ = Real.exp η * (d * f t * Bt t) := by ring
    · apply ENNReal.ofReal_le_ofReal
      rw [hsplit]
      have he : 1 ≤ Real.exp η * Real.exp (γ / 2 * Δ) := by
        rw [← Real.exp_add]; exact Real.one_le_exp (by linarith [neg_abs_le (γ / 2 * Δ)])
      calc d * f t * Bt t = (d * Bt t * f t) * 1 := by ring
        _ ≤ (d * Bt t * f t) * (Real.exp η * Real.exp (γ / 2 * Δ)) := by gcongr
        _ = Real.exp η * (d * Bt t * Real.exp (γ / 2 * Δ) * f t) := by ring
  unfold cmpInt
  rw [ha]
  constructor
  · rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    exact setLIntegral_mono' measurableSet_Icc fun t ht => (hpt t ht).1
  · rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    exact setLIntegral_mono' measurableSet_Icc fun t ht => (hpt t ht).2

/-- **A fine partition of unity** of `[-M, M]` with pieces of radius `h` centred at `n h`. -/
theorem exists_fine_partition (M : ℝ) {h : ℝ} (hh : 0 < h) :
    ∃ (T : Finset ℤ) (ρ : T → ℝ → ℝ), (∀ i, Continuous (ρ i)) ∧
      (∀ i, HasCompactSupport (ρ i)) ∧ (∀ i u, 0 ≤ ρ i u) ∧
      (∀ u ∈ Icc (-M) M, ∑ i, ρ i u = 1) ∧ (∀ u, ∑ i, ρ i u ≤ 1) ∧
      ∀ i u, ρ i u ≠ 0 → |u - ((i : ℤ) : ℝ) * h| < h := by
  set V : ℤ → Set ℝ := fun n => ball ((n : ℝ) * h) h with hV
  have hVo : ∀ n, IsOpen (V n) := fun n => isOpen_ball
  have hK : IsCompact (Icc (-M) M) := isCompact_Icc
  have hcov : Icc (-M) M ⊆ ⋃ n, V n := by
    intro u _
    refine mem_iUnion.2 ⟨round (u / h), ?_⟩
    rw [hV, mem_ball, Real.dist_eq]
    have h1 := abs_sub_round (u / h)
    have h2 : u - (round (u / h) : ℝ) * h = (u / h - round (u / h)) * h := by
      field_simp
    rw [h2, abs_mul, abs_of_pos hh]
    nlinarith
  obtain ⟨t, ht⟩ := hK.elim_finite_subcover V hVo hcov
  have hcov' : Icc (-M) M ⊆ ⋃ i : t, V i := by
    intro w hw
    obtain ⟨m, hm⟩ := mem_iUnion.1 (ht hw)
    obtain ⟨hmt, hwm⟩ := mem_iUnion.1 hm
    exact mem_iUnion.2 ⟨⟨m, hmt⟩, hwm⟩
  obtain ⟨f, hf⟩ := PartitionOfUnity.exists_isSubordinate hK.isClosed (fun i : t => V i)
    (fun i => hVo i) hcov'
  refine ⟨t, fun i => f i, fun i => (f i).continuous, fun i => ?_, fun i w => f.nonneg i w,
    fun w hw => ?_, fun w => ?_, fun i w hw => ?_⟩
  · exact (isCompact_closedBall ((i : ℤ) * h) h).of_isClosed_subset (isClosed_tsupport _)
      ((hf i).trans ball_subset_closedBall)
  · rw [← finsum_eq_sum_of_fintype]
    exact f.sum_eq_one hw
  · rw [← finsum_eq_sum_of_fintype]
    exact f.sum_le_one w
  · have := hf i (subset_tsupport _ hw)
    rw [mem_ball, Real.dist_eq] at this
    exact this

/-- `2^y = exp(y log 2)`. -/
theorem two_rpow_eq_exp (y : ℝ) : (2 : ℝ) ^ y = Real.exp (Real.log 2 * y) := by
  rw [Real.rpow_def_of_pos (by norm_num)]

/-- **Window index** of a scale piece: if `|log s − log s₀| ≤ log 2/(2N)`, then `s` lies in the
lattice window `[2^{-i/N}, 2^{-(i-2)/N}]` of `i = ⌈−N log₂ s₀ + 1/2⌉`. -/
theorem mem_win_index {N : ℕ} (hN : 1 ≤ N) {s₀ s : ℝ} (hs : 0 < s)
    (hl : |Real.log s - Real.log s₀| ≤ Real.log 2 / (2 * N)) :
    (2 : ℝ) ^ (-((⌈-Real.log s₀ / (Real.log 2 / N) + 1 / 2⌉ : ℤ) : ℝ) / N) ≤ s ∧
      s ≤ (2 : ℝ) ^ (-(((⌈-Real.log s₀ / (Real.log 2 / N) + 1 / 2⌉ : ℤ) : ℝ) - 2) / N) := by
  set lam := Real.log 2 / N with hlam
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlam0 : 0 < lam := div_pos hl2 hNpos
  set i := ⌈-Real.log s₀ / lam + 1 / 2⌉ with hi
  have hi1 : -Real.log s₀ / lam + 1 / 2 ≤ i := Int.le_ceil _
  have hi2 : (i : ℝ) < -Real.log s₀ / lam + 1 / 2 + 1 := Int.ceil_lt_add_one _
  have e1 : -Real.log s₀ / lam * lam = -Real.log s₀ := div_mul_cancel₀ _ hlam0.ne'
  have hl' : Real.log 2 / (2 * N) = lam / 2 := by rw [hlam]; field_simp
  rw [hl'] at hl
  have hab := abs_le.1 hl
  constructor
  · rw [two_rpow_eq_exp, ← Real.le_log_iff_exp_le hs]
    have : Real.log 2 * (-(i : ℝ) / N) = -(i : ℝ) * lam := by rw [hlam]; field_simp
    rw [this]
    nlinarith
  · rw [two_rpow_eq_exp, ← Real.log_le_iff_le_exp hs]
    have : Real.log 2 * (-((i : ℝ) - 2) / N) = -((i : ℝ) - 2) * lam := by rw [hlam]; field_simp
    rw [this]
    nlinarith

end SWCore
end QuantumZipper
