import QuantumZipper.Proofs.Zipper.AreaVarSand

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# SWC-A5 (1): variable-scale window limits, uniformly over an equicontinuous family

Task SWC-A5 (`handoff/SW-CORE.md`). The uniform-in-the-map step of Sheffield–Wang's change of
variables: S. Sheffield, M. Wang, arXiv:1605.06171, Cor. 3.2 (p. 11) and the proof of Thm 1.4
(pp. 11–13, (3.5)–(3.7)), where the approximating measures at the variable radius
`2^{-k} |φ'(φ⁻¹ w)|` are compared with the window measures `μ̄` (display on p. 9, Thm 1.1).
SW state the uniformity over all maps at once; we prove the deterministic form needed here:
if the window limits hold for `x` (`E6.WindowLimits`), then for any family of nonnegative weights
`g i` (uniformly bounded, uniformly equicontinuous, supported in one compact `C ⊆ ℍ`) and scale
functions `s i` (bounded above, positive and with equicontinuous `log₂` on the support of
`g i`), the variable-scale integrals `∫_ℍ g_i(w) μ_{2^{-k}s_i(w)}(dw)` converge to
`∫ g_i dμ` **uniformly in `i`**.

Proof: one finite partition of unity `θ_p` of mesh `δ` (independent of `i`), SW's window sandwich
on each `θ_p` with the centre value `g_i(p)` (the scale index is fixed on the piece by the
equicontinuity of `log₂ s_i`), and the finitely many window limits of the fixed `θ_p`. Own
bookkeeping around SW's window argument (the per-function version is `E6.tendsto_lintegral_varScale`).
-/

noncomputable section

open MeasureTheory Filter Set Function Metric
open scoped Topology ENNReal

namespace QuantumZipper
namespace SWCore

open E6

/-- The integer scale index of a positive number `v` at resolution `N`. -/
def scaleIdx (N : ℕ) (v : ℝ) : ℤ := ⌈-((N : ℝ) * Real.logb 2 v) + 1 / 2⌉

theorem scaleIdx_mem {N : ℕ} (hN : 1 ≤ N) {u v : ℝ} (hu : 0 < u)
    (h : |Real.logb 2 u - Real.logb 2 v| ≤ 1 / (2 * N)) :
    (2 : ℝ) ^ (-((scaleIdx N v : ℤ) : ℝ) / N) ≤ u ∧
      u ≤ (2 : ℝ) ^ (-(((scaleIdx N v : ℤ) : ℝ) - 2) / N) := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have hu' : (2 : ℝ) ^ Real.logb 2 u = u := Real.rpow_logb (by norm_num) (by norm_num) hu
  have hk : (1 / (2 * (N : ℝ))) * N = 1 / 2 := by field_simp
  have h1 : -(1 / 2) ≤ (Real.logb 2 u - Real.logb 2 v) * N := by
    have := mul_le_mul_of_nonneg_right (abs_le.1 h).1 hN0.le
    linarith
  have h2 : (Real.logb 2 u - Real.logb 2 v) * N ≤ 1 / 2 := by
    have := mul_le_mul_of_nonneg_right (abs_le.1 h).2 hN0.le
    linarith
  have hc1 := Int.le_ceil (-((N : ℝ) * Real.logb 2 v) + 1 / 2)
  have hc2 := Int.ceil_lt_add_one (-((N : ℝ) * Real.logb 2 v) + 1 / 2)
  unfold scaleIdx
  constructor
  · conv_rhs => rw [← hu']
    refine Real.rpow_le_rpow_of_exponent_le (by norm_num) ?_
    rw [div_le_iff₀ hN0]
    nlinarith
  · conv_lhs => rw [← hu']
    refine Real.rpow_le_rpow_of_exponent_le (by norm_num) ?_
    rw [le_div_iff₀ hN0]
    nlinarith

theorem scaleIdx_anti {N : ℕ} {v A : ℝ} (hv : 0 < v) (hvA : v ≤ A) :
    scaleIdx N A ≤ scaleIdx N v := by
  unfold scaleIdx
  refine Int.ceil_mono ?_
  have := Real.logb_le_logb_of_le (by norm_num : (1 : ℝ) < 2) hv hvA
  have hN : (0 : ℝ) ≤ N := Nat.cast_nonneg N
  nlinarith

/-- The variable-scale integral `∫_ℍ g(w) μ_{2^{-k} s(w)}(dw)` (in `ℝ≥0∞`). -/
def vsInt (γ : ℝ) (x : FieldSample) (g s : ℂ → ℝ) (k : ℕ) : ℝ≥0∞ :=
  ∫⁻ w in H, ENNReal.ofReal (g w) * ENNReal.ofReal (areaDens γ x (radius k * s w) w)

theorem ofReal_sum_le_sum_ofReal {α : Type*} (t : Finset α) (f : α → ℝ) :
    ENNReal.ofReal (∑ p ∈ t, f p) ≤ ∑ p ∈ t, ENNReal.ofReal (f p) := by
  classical
  induction t using Finset.induction_on with
  | empty => simp
  | insert a t ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha]
    exact ENNReal.ofReal_add_le.trans (add_le_add le_rfl ih)

variable {γ : ℝ} {x : FieldSample} {c c' : ℕ → ℝ}

/-- **Fixed resolution `N`, error `e`**: the window sandwich, uniformly over the family. -/
theorem unifWin_fixedN (hWin : WindowLimits γ x c c')
    (hμK : ∀ K, IsCompact K → K ⊆ H → qAreaMeasure γ x K < ⊤)
    (hsupm : ∀ N j, Measurable (supWin γ x N j)) (hinfm : ∀ N j, Measurable (infWin γ x N j))
    {ι : Type*} {C : Set ℂ} (hC : IsCompact C) (hCH : C ⊆ H) {g s : ι → ℂ → ℝ} {B A : ℝ}
    (hB : 0 ≤ B) (hg0 : ∀ i w, 0 ≤ g i w) (hgB : ∀ i w, g i w ≤ B)
    (hgC : ∀ i w, g i w ≠ 0 → w ∈ C)
    (hgeq : ∀ ε > 0, ∃ δ > 0, ∀ i w w', dist w w' < δ → |g i w - g i w'| ≤ ε)
    (hspos : ∀ i w, g i w ≠ 0 → 0 < s i w ∧ s i w ≤ A)
    (hseq : ∀ ε > 0, ∃ δ > 0, ∀ i w w', g i w ≠ 0 → g i w' ≠ 0 → dist w w' < δ →
      |Real.logb 2 (s i w) - Real.logb 2 (s i w')| ≤ ε)
    {N : ℕ} (hN : 1 ≤ N) {e : ℝ} (he : 0 < e) :
    ∀ᶠ k in atTop, ∀ i, ENNReal.ofReal (c N) * vsInt γ x (g i) (s i) k ≤
        ENNReal.ofReal (∫ w, g i w ∂qAreaMeasure γ x + e) ∧
      ENNReal.ofReal (∫ w, g i w ∂qAreaMeasure γ x - e) ≤
        ENNReal.ofReal (c' N) * vsInt γ x (g i) (s i) k := by
  classical
  set μ := qAreaMeasure γ x with hμ
  obtain ⟨δ₀, hδ₀, hC₁H⟩ := hC.exists_cthickening_subset_open isOpen_H hCH
  have hC₁ : IsCompact (cthickening δ₀ C) := hC.cthickening
  set Mμ := (μ (cthickening δ₀ C)).toReal with hMμdef
  have hMμ : 0 ≤ Mμ := ENNReal.toReal_nonneg
  set ε := e / (4 * (Mμ + 1)) with hεdef
  have hε : 0 < ε := by positivity
  have hεM : 2 * ε * Mμ ≤ e / 2 := by
    rw [hεdef]
    have h4 : 0 < 4 * (Mμ + 1) := by positivity
    rw [div_eq_mul_inv]
    have : Mμ * (4 * (Mμ + 1))⁻¹ ≤ 1 / 4 := by
      rw [← div_eq_mul_inv, div_le_iff₀ h4]; linarith
    nlinarith
  obtain ⟨δ₁, hδ₁, hg1⟩ := hgeq ε hε
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  obtain ⟨δ₂, hδ₂, hs2⟩ := hseq (1 / (2 * N)) (by positivity)
  set δ := min δ₁ (min (δ₂ / 2) δ₀) with hδdef
  have hδ : 0 < δ := lt_min hδ₁ (lt_min (half_pos hδ₂) hδ₀)
  have hδ1 : δ ≤ δ₁ := min_le_left _ _
  have hδ2 : δ ≤ δ₂ / 2 := (min_le_right _ _).trans (min_le_left _ _)
  have hδ0 : δ ≤ δ₀ := (min_le_right _ _).trans (min_le_right _ _)
  obtain ⟨t, htC, hcov⟩ := hC.elim_nhds_subcover (fun p => ball p δ)
    (fun p _ => ball_mem_nhds p hδ)
  have hcov' : C ⊆ ⋃ p : t, ball (p : ℂ) δ := by
    intro w hw
    obtain ⟨p, hp⟩ := mem_iUnion.1 (hcov hw)
    obtain ⟨hpt, hwp⟩ := mem_iUnion.1 hp
    exact mem_iUnion.2 ⟨⟨p, hpt⟩, hwp⟩
  obtain ⟨θ, hθ⟩ := PartitionOfUnity.exists_isSubordinate hC.isClosed
    (fun p : t => ball (p : ℂ) δ) (fun _ => isOpen_ball) hcov'
  have hθ0 : ∀ p w, 0 ≤ θ p w := fun p w => θ.nonneg p w
  have hθball : ∀ p w, θ p w ≠ 0 → dist w p < δ := fun p w h =>
    mem_ball.1 (hθ p (subset_tsupport _ h))
  have hball : ∀ p : t, ball (p : ℂ) δ ⊆ cthickening δ₀ C := fun p w hw =>
    mem_cthickening_of_dist_le w p δ₀ C (htC p p.2) ((mem_ball.1 hw).le.trans hδ0)
  have hθT : ∀ p, Continuous (θ p) ∧ HasCompactSupport (θ p) ∧ tsupport (θ p) ⊆ H := by
    intro p
    refine ⟨(θ p).continuous, ?_, (hθ p).trans ((hball p).trans hC₁H)⟩
    exact IsCompact.of_isClosed_subset (isCompact_closedBall (p : ℂ) δ) (isClosed_tsupport _)
      ((hθ p).trans ball_subset_closedBall)
  have hsum1 : ∀ w ∈ C, ∑ p, θ p w = 1 := by
    intro w hw
    rw [← finsum_eq_sum_of_fintype]
    exact θ.sum_eq_one hw
  have hsumle : ∀ w, ∑ p, θ p w ≤ 1 := by
    intro w
    rw [← finsum_eq_sum_of_fintype]
    exact θ.sum_le_one w
  have hgdec : ∀ i w, g i w = ∑ p, θ p w * g i w := by
    intro i w
    by_cases h : g i w = 0
    · simp [h]
    · rw [← Finset.sum_mul, hsum1 w (hgC i w h), one_mul]
  have hgc : ∀ i, Continuous (g i) := by
    intro i
    refine Metric.continuous_iff.2 fun w ε' hε' => ?_
    obtain ⟨δ', hδ', h'⟩ := hgeq (ε' / 2) (half_pos hε')
    refine ⟨δ', hδ', fun w' hw' => ?_⟩
    rw [Real.dist_eq]
    exact (h' i w' w hw').trans_lt (half_lt_self hε')
  have hgT : ∀ i p, Continuous (fun w => θ p w * g i w) ∧
      HasCompactSupport (fun w => θ p w * g i w) ∧ tsupport (fun w => θ p w * g i w) ⊆ H :=
    fun i p => ⟨(θ p).continuous.mul (hgc i), (hθT p).2.1.mul_right,
      tsupport_mul_subset_left.trans (hθT p).2.2⟩
  have hgi : ∀ i p, Integrable (fun w => θ p w * g i w) μ := fun i p =>
    integrable_of_areaTest hμK (hgT i p)
  have hθi : ∀ p, Integrable (θ p) μ := fun p => integrable_of_areaTest hμK (hθT p)
  have hI : ∀ i, ∫ w, g i w ∂μ = ∑ p, ∫ w, θ p w * g i w ∂μ := by
    intro i
    rw [← integral_finset_sum _ (fun p _ => hgi i p)]
    exact integral_congr_ae (ae_of_all _ fun w => hgdec i w)
  have hmsum : ∑ p, ∫ w, θ p w ∂μ ≤ Mμ := by
    rw [← integral_finset_sum _ (fun p _ => hθi p)]
    have hind : Integrable ((cthickening δ₀ C).indicator (fun _ => (1 : ℝ))) μ :=
      (integrable_indicator_iff isClosed_cthickening.measurableSet).2
        (integrableOn_const ((hμK _ hC₁ hC₁H).ne))
    calc ∫ w, ∑ p, θ p w ∂μ ≤ ∫ w, (cthickening δ₀ C).indicator (fun _ => (1 : ℝ)) w ∂μ := by
          refine integral_mono (integrable_finset_sum _ fun p _ => hθi p) hind fun w => ?_
          by_cases hw : w ∈ cthickening δ₀ C
          · rw [indicator_of_mem hw]
            exact hsumle w
          · rw [indicator_of_notMem hw]
            refine le_of_eq (Finset.sum_eq_zero fun p _ => ?_)
            by_contra h
            exact hw (hball p (mem_ball.2 (hθball p w h)))
      _ = Mμ := by
          rw [integral_indicator_const _ isClosed_cthickening.measurableSet, smul_eq_mul,
            mul_one]
          rfl
  set m : t → ℝ := fun p => ∫ w, θ p w ∂μ with hmdef
  have hm' : ∀ p : t, m p = ∫ w, θ p w ∂μ := fun p => rfl
  have hm0 : ∀ p : t, 0 ≤ m p := fun p => integral_nonneg (hθ0 p)
  have hmsum' : ∑ p : t, m p ≤ Mμ := hmsum
  set ε₁ := e / (4 * ((Fintype.card t : ℝ) + 1) * (B + ε + 1)) with hε₁def
  have hε₁ : 0 < ε₁ := by positivity
  have hcardε : (Fintype.card t : ℝ) * (B + ε) * ε₁ ≤ e / 4 := by
    have hc0 : (0 : ℝ) ≤ Fintype.card t := Nat.cast_nonneg _
    have hD : 0 < ((Fintype.card t : ℝ) + 1) * (B + ε + 1) := by positivity
    have heq : (Fintype.card t : ℝ) * (B + ε) * ε₁ =
        e / 4 * (((Fintype.card t : ℝ) * (B + ε)) / (((Fintype.card t : ℝ) + 1) * (B + ε + 1))) := by
      rw [hε₁def]; field_simp
    rw [heq]
    refine mul_le_of_le_one_right (by positivity) ?_
    rw [div_le_one hD]
    nlinarith
  have hWp : ∀ p : t, ∀ᶠ j in atTop,
      ENNReal.ofReal (c N) * ∫⁻ w in H, supWin γ x N j w * ENNReal.ofReal (θ p w) ≤
        ENNReal.ofReal (m p + ε₁) ∧
      ENNReal.ofReal (m p - ε₁) ≤
        ENNReal.ofReal (c' N) * ∫⁻ w in H, infWin γ x N j w * ENNReal.ofReal (θ p w) := by
    intro p
    obtain ⟨h1, h2⟩ := hWin N hN (θ p) (hθT p).1 (hθT p).2.1 (hθT p).2.2 (hθ0 p)
    have hmp := hm0 p
    refine (((tendsto_order.1 h1).2 _ ?_).mono fun j hj => hj.le).and ?_
    · exact (ENNReal.ofReal_lt_ofReal_iff (by linarith)).2 (by rw [hm']; linarith)
    · by_cases hmp' : ε₁ < m p
      · refine ((tendsto_order.1 h2).1 _ ?_).mono fun j hj => hj.le
        exact (ENNReal.ofReal_lt_ofReal_iff (by rw [← hm']; linarith)).2
          (by rw [hm']; linarith)
      · exact Eventually.of_forall fun j => by
          rw [ENNReal.ofReal_of_nonpos (by linarith)]; exact bot_le
  obtain ⟨J₀, hJ₀⟩ := eventually_atTop.1 (eventually_all.2 hWp)
  set ref : t → ι → ℝ := fun p i =>
    if h : ∃ w, dist w (p : ℂ) < δ ∧ g i w ≠ 0 then s i h.choose else A with hrefdef
  have hwin : ∀ (p : t) (i : ι) (w : ℂ), dist w (p : ℂ) < δ → g i w ≠ 0 →
      (2 : ℝ) ^ (-((scaleIdx N (ref p i) : ℤ) : ℝ) / N) ≤ s i w ∧
        s i w ≤ (2 : ℝ) ^ (-(((scaleIdx N (ref p i) : ℤ) : ℝ) - 2) / N) := by
    intro p i w hw hg
    have h : ∃ w, dist w (p : ℂ) < δ ∧ g i w ≠ 0 := ⟨w, hw, hg⟩
    have hr : ref p i = s i h.choose := by simp only [hrefdef, dif_pos h]
    rw [hr]
    refine scaleIdx_mem hN (hspos i w hg).1 (hs2 i w h.choose hg h.choose_spec.2 ?_)
    calc dist w h.choose ≤ dist w p + dist h.choose p := dist_triangle_right _ _ _
      _ < δ + δ := add_lt_add hw h.choose_spec.1
      _ ≤ δ₂ := by linarith
  have hidx : ∀ (p : t) (i : ι), scaleIdx N A ≤ scaleIdx N (ref p i) := by
    intro p i
    by_cases h : ∃ w, dist w (p : ℂ) < δ ∧ g i w ≠ 0
    · have hr : ref p i = s i h.choose := by simp only [hrefdef, dif_pos h]
      rw [hr]
      exact scaleIdx_anti (hspos i _ h.choose_spec.2).1 (hspos i _ h.choose_spec.2).2
    · have hr : ref p i = A := by simp only [hrefdef, dif_neg h]
      rw [hr]
  set jj : t → ι → ℕ → ℕ := fun p i k =>
    Int.toNat ((k : ℤ) * N + scaleIdx N (ref p i) - 2) with hjjdef
  refine (eventually_ge_atTop (Int.toNat ((J₀ : ℤ) + 2 - scaleIdx N A))).mono fun k hk i => ?_
  have hjj : ∀ p : t, ((jj p i k : ℕ) : ℤ) = (k : ℤ) * N + scaleIdx N (ref p i) - 2 ∧
      J₀ ≤ jj p i k := by
    intro p
    have h1 := hidx p i
    have h2 := Int.self_le_toNat ((J₀ : ℤ) + 2 - scaleIdx N A)
    have hk' : ((Int.toNat ((J₀ : ℤ) + 2 - scaleIdx N A) : ℕ) : ℤ) ≤ k := by exact_mod_cast hk
    have hkN : (k : ℤ) ≤ (k : ℤ) * N := by
      have : (1 : ℤ) ≤ N := by exact_mod_cast hN
      nlinarith
    obtain ⟨P, hP⟩ : ∃ P : ℤ, P = (k : ℤ) * N := ⟨_, rfl⟩
    rw [← hP] at hkN
    have hnn : 0 ≤ P + scaleIdx N (ref p i) - 2 := by omega
    have e1 : ((jj p i k : ℕ) : ℤ) = P + scaleIdx N (ref p i) - 2 := by
      simp only [hjjdef, hP]
      exact Int.toNat_of_nonneg (hP ▸ hnn)
    refine ⟨hP ▸ e1, ?_⟩
    omega
  set I := ∫ w, g i w ∂μ with hIdef
  have hpU : ∀ p : t, (g i (p : ℂ) + ε) * m p ≤ ∫ w, θ p w * g i w ∂μ + 2 * ε * m p := by
    intro p
    have h := integral_mono (f := fun w => (g i (p : ℂ) + ε) * θ p w)
      (g := fun w => θ p w * g i w + 2 * ε * θ p w) ((hθi p).const_mul (g i (p : ℂ) + ε))
      ((hgi i p).add ((hθi p).const_mul (2 * ε))) (fun w => by
        show (g i (p : ℂ) + ε) * θ p w ≤ θ p w * g i w + 2 * ε * θ p w
        by_cases h0 : θ p w = 0
        · simp [h0]
        · have := abs_le.1 (hg1 i w p ((hθball p w h0).trans_le hδ1))
          nlinarith [hθ0 p w])
    rw [integral_const_mul, integral_add (hgi i p) ((hθi p).const_mul _),
      integral_const_mul] at h
    exact h
  have hpL : ∀ p : t, ∫ w, θ p w * g i w ∂μ - 2 * ε * m p ≤ max (g i (p : ℂ) - ε) 0 * m p := by
    intro p
    have h := integral_mono (f := fun w => θ p w * g i w - 2 * ε * θ p w)
      (g := fun w => max (g i (p : ℂ) - ε) 0 * θ p w) ((hgi i p).sub ((hθi p).const_mul (2 * ε)))
      ((hθi p).const_mul (max (g i (p : ℂ) - ε) 0)) (fun w => by
        show θ p w * g i w - 2 * ε * θ p w ≤ max (g i (p : ℂ) - ε) 0 * θ p w
        by_cases h0 : θ p w = 0
        · simp [h0]
        · have := abs_le.1 (hg1 i w p ((hθball p w h0).trans_le hδ1))
          have hmx := le_max_left (g i (p : ℂ) - ε) 0
          nlinarith [hθ0 p w])
    rw [integral_const_mul, integral_sub (hgi i p) ((hθi p).const_mul _),
      integral_const_mul] at h
    exact h
  have hgp : ∀ p : t, g i (p : ℂ) + ε ≤ B + ε := fun p => by linarith [hgB i p]
  have hU : ∑ p : t, (g i (p : ℂ) + ε) * (m p + ε₁) ≤ I + e := by
    have h1 : ∑ p : t, (g i (p : ℂ) + ε) * m p ≤ I + 2 * ε * ∑ p : t, m p := by
      rw [hIdef, hI i, Finset.mul_sum, ← Finset.sum_add_distrib]
      exact Finset.sum_le_sum fun p _ => hpU p
    have h2 : ∑ p : t, (g i (p : ℂ) + ε) * ε₁ ≤ (Fintype.card t : ℝ) * (B + ε) * ε₁ := by
      rw [← Finset.sum_mul]
      refine mul_le_mul_of_nonneg_right ?_ hε₁.le
      calc ∑ p : t, (g i (p : ℂ) + ε) ≤ ∑ _p : t, (B + ε) := Finset.sum_le_sum fun p _ => hgp p
        _ = _ := by rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    have h3 : 2 * ε * ∑ p : t, m p ≤ e / 2 := by
      have := mul_le_mul_of_nonneg_left hmsum' (by positivity : (0 : ℝ) ≤ 2 * ε)
      linarith
    have h4 : ∑ p : t, (g i (p : ℂ) + ε) * (m p + ε₁) =
        ∑ p : t, (g i (p : ℂ) + ε) * m p + ∑ p : t, (g i (p : ℂ) + ε) * ε₁ := by
      rw [← Finset.sum_add_distrib]; exact Finset.sum_congr rfl fun p _ => by ring
    linarith
  have hL : I - e ≤ ∑ p : t, max (g i (p : ℂ) - ε) 0 * (m p - ε₁) := by
    have h1 : I - 2 * ε * ∑ p : t, m p ≤ ∑ p : t, max (g i (p : ℂ) - ε) 0 * m p := by
      rw [hIdef, hI i, Finset.mul_sum, ← Finset.sum_sub_distrib]
      exact Finset.sum_le_sum fun p _ => hpL p
    have h2 : ∑ p : t, max (g i (p : ℂ) - ε) 0 * ε₁ ≤ (Fintype.card t : ℝ) * (B + ε) * ε₁ := by
      rw [← Finset.sum_mul]
      refine mul_le_mul_of_nonneg_right ?_ hε₁.le
      calc ∑ p : t, max (g i (p : ℂ) - ε) 0 ≤ ∑ _p : t, (B + ε) :=
            Finset.sum_le_sum fun p _ => max_le (by linarith [hgB i p]) (by linarith)
        _ = _ := by rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    have h3 : 2 * ε * ∑ p : t, m p ≤ e / 2 := by
      have := mul_le_mul_of_nonneg_left hmsum' (by positivity : (0 : ℝ) ≤ 2 * ε)
      linarith
    have h4 : ∑ p : t, max (g i (p : ℂ) - ε) 0 * (m p - ε₁) =
        ∑ p : t, max (g i (p : ℂ) - ε) 0 * m p - ∑ p : t, max (g i (p : ℂ) - ε) 0 * ε₁ := by
      rw [← Finset.sum_sub_distrib]; exact Finset.sum_congr rfl fun p _ => by ring
    linarith
  have hθm : ∀ p : t, Measurable fun w => ENNReal.ofReal (θ p w) :=
    fun p => ENNReal.measurable_ofReal.comp (θ p).continuous.measurable
  have hup_pt : ∀ w, ENNReal.ofReal (g i w) *
      ENNReal.ofReal (areaDens γ x (radius k * s i w) w) ≤ ∑ p : t,
        ENNReal.ofReal (g i (p : ℂ) + ε) * (supWin γ x N (jj p i k) w * ENNReal.ofReal (θ p w)) := by
    intro w
    rw [hgdec i w, ENNReal.ofReal_sum_of_nonneg (fun p _ => mul_nonneg (hθ0 p w) (hg0 i w)),
      Finset.sum_mul]
    refine Finset.sum_le_sum fun p _ => ?_
    by_cases h0 : θ p w * g i w = 0
    · simp [h0]
    · have hθne : θ p w ≠ 0 := left_ne_zero_of_mul h0
      have hgne : g i w ≠ 0 := right_ne_zero_of_mul h0
      have hd := hθball p w hθne
      have hgle : g i w ≤ g i (p : ℂ) + ε := by
        have := abs_le.1 (hg1 i w p (hd.trans_le hδ1)); linarith
      have hmem := mem_win_of_scale hN (hjj p).1 (hwin p i w hd hgne)
      have hA : ENNReal.ofReal (areaDens γ x (radius k * s i w) w) ≤
          supWin γ x N (jj p i k) w := le_iSup₂_of_le (radius k * s i w) hmem le_rfl
      rw [ENNReal.ofReal_mul (hθ0 p w)]
      calc ENNReal.ofReal (θ p w) * ENNReal.ofReal (g i w) *
            ENNReal.ofReal (areaDens γ x (radius k * s i w) w)
          = ENNReal.ofReal (g i w) * (ENNReal.ofReal (areaDens γ x (radius k * s i w) w) *
            ENNReal.ofReal (θ p w)) := by ring
        _ ≤ ENNReal.ofReal (g i (p : ℂ) + ε) *
            (supWin γ x N (jj p i k) w * ENNReal.ofReal (θ p w)) := by
          gcongr
  have hlo_pt : ∀ w, ∑ p : t, ENNReal.ofReal (g i (p : ℂ) - ε) *
      (infWin γ x N (jj p i k) w * ENNReal.ofReal (θ p w)) ≤
        ENNReal.ofReal (g i w) * ENNReal.ofReal (areaDens γ x (radius k * s i w) w) := by
    intro w
    calc ∑ p : t, ENNReal.ofReal (g i (p : ℂ) - ε) *
          (infWin γ x N (jj p i k) w * ENNReal.ofReal (θ p w))
        ≤ ∑ p : t, ENNReal.ofReal (θ p w * g i w) *
            ENNReal.ofReal (areaDens γ x (radius k * s i w) w) := by
          refine Finset.sum_le_sum fun p _ => ?_
          by_cases hθz : θ p w = 0
          · simp [hθz]
          by_cases hgp0 : g i (p : ℂ) - ε ≤ 0
          · simp [ENNReal.ofReal_of_nonpos hgp0]
          have hd := hθball p w hθz
          have hgw : g i (p : ℂ) - ε ≤ g i w := by
            have := abs_le.1 (hg1 i w p (hd.trans_le hδ1)); linarith
          have hgne : g i w ≠ 0 := by
            intro h; rw [h] at hgw; exact hgp0 hgw
          have hmem := mem_win_of_scale hN (hjj p).1 (hwin p i w hd hgne)
          have hA : infWin γ x N (jj p i k) w ≤
              ENNReal.ofReal (areaDens γ x (radius k * s i w) w) :=
            iInf₂_le_of_le (radius k * s i w) hmem le_rfl
          rw [ENNReal.ofReal_mul (hθ0 p w)]
          calc ENNReal.ofReal (g i (p : ℂ) - ε) *
                (infWin γ x N (jj p i k) w * ENNReal.ofReal (θ p w))
              ≤ ENNReal.ofReal (g i w) * (ENNReal.ofReal (areaDens γ x (radius k * s i w) w) *
                ENNReal.ofReal (θ p w)) := by gcongr
            _ = _ := by ring
      _ = ENNReal.ofReal (∑ p : t, θ p w * g i w) *
            ENNReal.ofReal (areaDens γ x (radius k * s i w) w) := by
          rw [ENNReal.ofReal_sum_of_nonneg (fun p _ => mul_nonneg (hθ0 p w) (hg0 i w)),
            Finset.sum_mul]
      _ ≤ ENNReal.ofReal (g i w) * ENNReal.ofReal (areaDens γ x (radius k * s i w) w) := by
          gcongr
          rw [← Finset.sum_mul]
          exact mul_le_of_le_one_left (hg0 i w) (hsumle w)
  have hupI : vsInt γ x (g i) (s i) k ≤ ∑ p : t, ENNReal.ofReal (g i (p : ℂ) + ε) *
      ∫⁻ w in H, supWin γ x N (jj p i k) w * ENNReal.ofReal (θ p w) := by
    calc vsInt γ x (g i) (s i) k ≤ ∫⁻ w in H, ∑ p : t, ENNReal.ofReal (g i (p : ℂ) + ε) *
          (supWin γ x N (jj p i k) w * ENNReal.ofReal (θ p w)) := lintegral_mono fun w => hup_pt w
      _ = _ := by
        rw [lintegral_finset_sum (s := Finset.univ) (f := fun (p : t) w =>
          ENNReal.ofReal (g i (p : ℂ) + ε) * (supWin γ x N (jj p i k) w * ENNReal.ofReal (θ p w)))
          (fun p _ => ((hsupm N _).mul (hθm p)).const_mul _)]
        exact Finset.sum_congr rfl fun p _ => lintegral_const_mul _ ((hsupm N _).mul (hθm p))
  have hloI : ∑ p : t, ENNReal.ofReal (g i (p : ℂ) - ε) *
      ∫⁻ w in H, infWin γ x N (jj p i k) w * ENNReal.ofReal (θ p w) ≤ vsInt γ x (g i) (s i) k := by
    calc ∑ p : t, ENNReal.ofReal (g i (p : ℂ) - ε) *
          ∫⁻ w in H, infWin γ x N (jj p i k) w * ENNReal.ofReal (θ p w)
        = ∫⁻ w in H, ∑ p : t, ENNReal.ofReal (g i (p : ℂ) - ε) *
          (infWin γ x N (jj p i k) w * ENNReal.ofReal (θ p w)) := by
          rw [lintegral_finset_sum (s := Finset.univ) (f := fun (p : t) w =>
            ENNReal.ofReal (g i (p : ℂ) - ε) * (infWin γ x N (jj p i k) w * ENNReal.ofReal (θ p w)))
            (fun p _ => ((hinfm N _).mul (hθm p)).const_mul _)]
          exact Finset.sum_congr rfl fun p _ =>
            (lintegral_const_mul _ ((hinfm N _).mul (hθm p))).symm
      _ ≤ vsInt γ x (g i) (s i) k := lintegral_mono fun w => hlo_pt w
  have hmax : ∀ a : ℝ, ENNReal.ofReal (max a 0) = ENNReal.ofReal a := fun a => by
    rcases le_total a 0 with h | h
    · rw [max_eq_right h, ENNReal.ofReal_zero, ENNReal.ofReal_of_nonpos h]
    · rw [max_eq_left h]
  constructor
  · calc ENNReal.ofReal (c N) * vsInt γ x (g i) (s i) k
        ≤ ENNReal.ofReal (c N) * ∑ p : t, ENNReal.ofReal (g i (p : ℂ) + ε) *
            ∫⁻ w in H, supWin γ x N (jj p i k) w * ENNReal.ofReal (θ p w) := by gcongr
      _ = ∑ p : t, ENNReal.ofReal (g i (p : ℂ) + ε) * (ENNReal.ofReal (c N) *
            ∫⁻ w in H, supWin γ x N (jj p i k) w * ENNReal.ofReal (θ p w)) := by
          rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun p _ => by ring
      _ ≤ ∑ p : t, ENNReal.ofReal (g i (p : ℂ) + ε) * ENNReal.ofReal (m p + ε₁) :=
          Finset.sum_le_sum fun p _ => by gcongr; exact (hJ₀ _ (hjj p).2 p).1
      _ = ENNReal.ofReal (∑ p : t, (g i (p : ℂ) + ε) * (m p + ε₁)) := by
          rw [ENNReal.ofReal_sum_of_nonneg (fun p _ => mul_nonneg (by linarith [hg0 i p])
            (by linarith [hm0 p]))]
          exact Finset.sum_congr rfl fun p _ =>
            (ENNReal.ofReal_mul (by linarith [hg0 i p])).symm
      _ ≤ ENNReal.ofReal (I + e) := ENNReal.ofReal_le_ofReal hU
  · calc ENNReal.ofReal (I - e)
        ≤ ENNReal.ofReal (∑ p : t, max (g i (p : ℂ) - ε) 0 * (m p - ε₁)) :=
          ENNReal.ofReal_le_ofReal hL
      _ ≤ ∑ p : t, ENNReal.ofReal (max (g i (p : ℂ) - ε) 0 * (m p - ε₁)) :=
          ofReal_sum_le_sum_ofReal _ _
      _ = ∑ p : t, ENNReal.ofReal (g i (p : ℂ) - ε) * ENNReal.ofReal (m p - ε₁) :=
          Finset.sum_congr rfl fun p _ => by rw [ENNReal.ofReal_mul (le_max_right _ _), hmax]
      _ ≤ ∑ p : t, ENNReal.ofReal (g i (p : ℂ) - ε) * (ENNReal.ofReal (c' N) *
            ∫⁻ w in H, infWin γ x N (jj p i k) w * ENNReal.ofReal (θ p w)) :=
          Finset.sum_le_sum fun p _ => by gcongr; exact (hJ₀ _ (hjj p).2 p).2
      _ = ENNReal.ofReal (c' N) * ∑ p : t, ENNReal.ofReal (g i (p : ℂ) - ε) *
            ∫⁻ w in H, infWin γ x N (jj p i k) w * ENNReal.ofReal (θ p w) := by
          rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun p _ => by ring
      _ ≤ ENNReal.ofReal (c' N) * vsInt γ x (g i) (s i) k := by gcongr

end SWCore
end QuantumZipper
