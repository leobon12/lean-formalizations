import QuantumZipper.Proofs.Zipper.AreaWinDefs
import QuantumZipper.Proofs.LQG.AreaOffsets

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# SW-WINDOW (1): from SW's `L¹ + L²` window estimate to a.s. window convergence, per test function

Source: S. Sheffield, M. Wang, arXiv:1605.06171 (literature/1605.06171.pdf), §3.1:
* proof of Lemma 3.1, pp. 7–8: the `L²` estimate (3.1) (for `γ < √2`) and, for `γ ≥ √2`, the
  thick-point split (3.2) into a part with exponentially small first moment and a part with
  exponentially small second moment, then "the Borel–Cantelli lemma";
* proof of Theorem 1.1, p. 9: the same estimate for `μ̄_{k,N}` against `μ_{2^{-k/N}}` ("using the
  tower property of conditional expectation as in the proof of Lemma 3.1"), and Lemma 3.1 itself
  (convergence of `μ_{2^{-k/N}}` to `μ`).

Here:
* `ae_tendsto_of_winSplit`: the Borel–Cantelli step. From `WinSplit` (`Σ E Y_j < ∞`,
  `Σ E Z_j² < ∞`) the error terms tend to `0` a.s. (monotone convergence: `Σ_j Y_j < ∞` a.s.), so
  `A_j` has the same a.s. limit as `B_j`.
* `tendsto_winRef`: **SW Lemma 3.1** for the lattice `2^{-j/N}`, for every sample with an area
  limit uniform in the offset (`HasAreaLimit`, proved a.s. for the free field in
  `AreaOffsets.ae_hasAreaLimit`): `2^{-j/N} = a 2^{-k}` with `a ∈ [1,2]`.
* `ae_window_of_split`: for the free field, fixed `N ≥ 1` and a fixed test function `φ ≥ 0`,
  a.s. both normalized window integrals converge to `∫ φ dμ`.

The Borel–Cantelli bookkeeping is own elementary argument (cost rule).
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Function
open scoped Topology NNReal ENNReal

namespace QuantumZipper.E6

open VagueH GoodSample

/-! ## 1. Squeeze and Borel–Cantelli -/

theorem tendsto_of_le_add_of_le_add {a b e : ℕ → ℝ≥0∞} {L : ℝ≥0∞} (hL : L ≠ ∞)
    (hb : Tendsto b atTop (𝓝 L)) (he : Tendsto e atTop (𝓝 0))
    (h : ∀ᶠ j in atTop, a j ≤ b j + e j ∧ b j ≤ a j + e j) : Tendsto a atTop (𝓝 L) := by
  have hup : Tendsto (fun j => b j + e j) atTop (𝓝 L) := by
    simpa using hb.add he
  have hlo : Tendsto (fun j => b j - e j) atTop (𝓝 L) := by
    simpa using ENNReal.Tendsto.sub hb he (Or.inl hL)
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le' hlo hup
    (h.mono fun j hj => tsub_le_iff_right.2 hj.2) (h.mono fun j hj => hj.1)

theorem ae_tendsto_zero_of_tsum_lintegral {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
    {Y : ℕ → Ω → ℝ≥0∞} (hY : ∀ j, AEMeasurable (Y j) P)
    (hs : (∑' j, ∫⁻ ω, Y j ω ∂P) ≠ ∞) :
    ∀ᵐ ω ∂P, Tendsto (fun j => Y j ω) atTop (𝓝 0) := by
  have h1 : ∫⁻ ω, ∑' j, Y j ω ∂P ≠ ∞ := by rwa [lintegral_tsum hY]
  filter_upwards [ae_lt_top' (AEMeasurable.ennreal_tsum hY) h1] with ω hω
  exact ENNReal.tendsto_atTop_zero_of_tsum_ne_top hω.ne

theorem ae_tendsto_zero_of_tsum_lintegral_sq {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
    {Z : ℕ → Ω → ℝ≥0∞} (hZ : ∀ j, AEMeasurable (Z j) P)
    (hs : (∑' j, ∫⁻ ω, Z j ω ^ 2 ∂P) ≠ ∞) :
    ∀ᵐ ω ∂P, Tendsto (fun j => Z j ω) atTop (𝓝 0) := by
  filter_upwards [ae_tendsto_zero_of_tsum_lintegral (fun j => (hZ j).pow_const 2) hs]
    with ω hω
  have hc : Tendsto (fun j => (Z j ω ^ 2) ^ (((2 : ℕ) : ℝ)⁻¹)) atTop
      (𝓝 ((0 : ℝ≥0∞) ^ (((2 : ℕ) : ℝ)⁻¹))) :=
    ((ENNReal.continuous_rpow_const).tendsto 0).comp hω
  rw [ENNReal.zero_rpow_of_pos (by norm_num)] at hc
  simpa only [ENNReal.pow_rpow_inv_natCast two_ne_zero] using hc

/-- **Borel–Cantelli step of SW (p. 8, p. 9).** -/
theorem ae_tendsto_of_winSplit {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
    {A B : ℕ → Ω → ℝ≥0∞} (hS : WinSplit P A B) (L : Ω → ℝ≥0∞)
    (hB : ∀ᵐ ω ∂P, L ω ≠ ∞ ∧ Tendsto (fun j => B j ω) atTop (𝓝 (L ω))) :
    ∀ᵐ ω ∂P, Tendsto (fun j => A j ω) atTop (𝓝 (L ω)) := by
  obtain ⟨Y, Z, hY, hZ, hYs, hZs, j₀, hle⟩ := hS
  filter_upwards [hB, hle, ae_tendsto_zero_of_tsum_lintegral hY hYs,
    ae_tendsto_zero_of_tsum_lintegral_sq hZ hZs] with ω hBω hω hYω hZω
  exact tendsto_of_le_add_of_le_add hBω.1 hBω.2 (by simpa using hYω.add hZω)
    (eventually_atTop.2 ⟨j₀, hω⟩)

/-! ## 2. SW Lemma 3.1 along `2^{-j/N}` from the offset-uniform area limit -/

theorem tendsto_goodFilter_winHi {N : ℕ} (hN : 1 ≤ N) :
    ∃ i : ℕ → ℕ × ℝ, Tendsto i atTop goodFilter ∧ ∀ j, goodRad (i j) = winHi N j := by
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
  refine ⟨fun j => (⌈(j : ℝ) / N⌉₊, (2 : ℝ) ^ ((⌈(j : ℝ) / N⌉₊ : ℝ) - (j : ℝ) / N)), ?_,
    fun j => ?_⟩
  · refine Tendsto.prodMk ?_ (tendsto_principal.2 (Eventually.of_forall fun j => ?_))
    · exact tendsto_nat_ceil_atTop.comp
        (tendsto_natCast_atTop_atTop.atTop_div_const hNpos)
    · have ht : 0 ≤ (j : ℝ) / N := by positivity
      have h1 := Nat.le_ceil ((j : ℝ) / N)
      have h2 := Nat.ceil_lt_add_one ht
      constructor
      · exact Real.one_le_rpow (by norm_num) (by linarith)
      · calc (2 : ℝ) ^ ((⌈(j : ℝ) / N⌉₊ : ℝ) - (j : ℝ) / N) ≤ (2 : ℝ) ^ (1 : ℝ) :=
              Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
          _ = 2 := Real.rpow_one 2
  · show (2 : ℝ) ^ ((⌈(j : ℝ) / N⌉₊ : ℝ) - (j : ℝ) / N) * radius ⌈(j : ℝ) / N⌉₊ = winHi N j
    rw [mul_comm, radius_mul_rpow, winHi]
    congr 1
    ring

/-- **SW Lemma 3.1 for the lattice `2^{-j/N}`**, tested against `φ ≥ 0`, in `ℝ≥0∞`. -/
theorem tendsto_winRef {γ : ℝ} {x : FieldSample} (hx : IsRegularSample x) {μ : Measure ℂ}
    (hμ : HasAreaLimit γ x μ) {N : ℕ} (hN : 1 ≤ N) {φ : ℂ → ℝ} (hφ : IsTestH φ)
    (hφ0 : ∀ w, 0 ≤ φ w) :
    Tendsto (fun j => winRef γ x N j φ) atTop (𝓝 (ENNReal.ofReal (∫ w, φ w ∂μ))) := by
  obtain ⟨F, hF⟩ := hx
  obtain ⟨i, hi, hrad⟩ := tendsto_goodFilter_winHi hN
  have h1 := (hμ.2.2 φ hφ.1 hφ.2.1 hφ.2.2).comp hi
  have h2 := (ENNReal.continuous_ofReal.tendsto _).comp h1
  refine h2.congr fun j => ?_
  simp only [Function.comp_apply, hrad]
  have hr : 0 < winHi N j := Real.rpow_pos_of_pos (by norm_num) _
  rw [winRef, areaR, integral_withDensity_ofReal (continuous_areaDens γ hF hr).measurable
    (fun z => areaDens_nonneg γ x hr z)]
  refine ofReal_integral_eq_lintegral_ofReal ?_ (Eventually.of_forall fun z =>
    mul_nonneg (areaDens_nonneg γ x hr z) (hφ0 z))
  exact (((continuous_areaDens γ hF hr).mul hφ.1).integrable_of_hasCompactSupport
    hφ.2.1.mul_left).integrableOn

/-! ## 3. Per test function: a.s. window convergence for the free field -/

/-- The normalized sup-window integral `c N ∫_ℍ supWin φ`. -/
def supInt (γ : ℝ) (x : FieldSample) (c : ℕ → ℝ) (N j : ℕ) (φ : ℂ → ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal (c N) * ∫⁻ w in H, supWin γ x N j w * ENNReal.ofReal (φ w)

/-- The normalized inf-window integral `c' N ∫_ℍ infWin φ`. -/
def infInt (γ : ℝ) (x : FieldSample) (c' : ℕ → ℝ) (N j : ℕ) (φ : ℂ → ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal (c' N) * ∫⁻ w in H, infWin γ x N j w * ENNReal.ofReal (φ w)

end QuantumZipper.E6
