import GaussianLQG.LQG.Euclid.Pair
import GaussianLQG.LQG.Euclid.Grid
import GaussianLQG.LQG.Euclid.Union
import GaussianLQG.LQG.Euclid.Measurability

/-!
# Euclidean approximation (blueprint Lemma `lem:euclidean`)

For `R ≥ 1` and `p ≥ 1` there are `γ_* > 0` and `C` such that
`E[𝖤_γ(R)^p] ≤ C ξ_γ^{p/2}` for `γ ∈ (0, γ_*]`, where
`𝖤_γ(R) = sup_{z,w ∈ B̄_R(0)} |e^{-b_γ} D^γ(z,w) - |z - w||`
(`Setup.euclidApprox : S.EuclidApprox`). `𝖤_γ(R)` is measurable (`Setup.measurable_euclidErr`).

Proof (blueprint).
* Steps 1–2 (`Setup.exists_eLpNorm_pair_le`): for fixed `z, w ∈ B̄_{2R+4}(0)` and `P₀ = max(p, 8)`,
  `‖e^{-b} D(z,w) - |z - w|‖_{P₀} ≤ K ξ`.
* Step 3: on the grid `Λ = ξ(ℤ + iℤ) ∩ {|m|, |n| ≤ N}` (`gridIdx`, `#Λ ≤ ((2R+5)/ξ)²`), the variable
  `M = (∑_{z',w' ∈ Λ} |e^{-b} D(z',w') - |z' - w'||^{P₀})^{1/P₀}` dominates the maximum over grid
  pairs and `‖M‖_p ≤ ‖M‖_{P₀} ≤ (#Λ)^{2/P₀} K ξ ≤ (2R+5) K ξ^{1/2}` (union bound, `P₀ ≥ 8`).
* Step 4 (`Setup.euclidErr_le_grid`): for `z, w ∈ B̄_R(0)` pick grid points `z', w'` within `ξ`;
  then `|e^{-b} D(z,w) - |z-w|| ≤ M + 2 e^{-b} A_γ(B̄_{R+1}(0)) ξ^{1/2} + 2ξ`, and (S6) and
  Lemma `lem:scaling`(a) bound the `L^p` norms. Minkowski's inequality concludes.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal

namespace GaussianLQG

namespace Setup

variable (S : Setup)

/-- **Blueprint Lemma `lem:euclidean`, Step 4 (filling the grid), pathwise.** For a mesh
`s ∈ (0, 1]`, `P₀ > 0` and every `ω`,
`𝖤_γ(R) ≤ (∑_{z',w' ∈ Λ} |e^{-b} D(z',w') - |z' - w'||^{P₀})^{1/P₀}
  + 2 e^{-b} s^{1/2} A_γ(B̄_{R+1}(0)) + 2s`. -/
theorem euclidErr_le_grid (γ : ℝ) {R s P0 : ℝ} (hs : 0 < s) (hs1 : s ≤ 1) (hP0 : 0 < P0)
    (ω : Coord) :
    S.euclidErr γ R ω ≤
      (∑ ij ∈ gridIdx s R ×ˢ gridIdx s R,
        ‖Real.exp (-S.b γ) * (S.D γ ω).1 (gridPt s ij.1, gridPt s ij.2) -
          ‖gridPt s ij.1 - gridPt s ij.2‖‖ₑ ^ P0) ^ (1 / P0) +
      ENNReal.ofReal (2 * Real.exp (-S.b γ) * Real.sqrt s) *
        holderConst (S.D γ ω).1 (Metric.closedBall 0 (R + 1)) +
      ENNReal.ofReal (2 * s) := by
  refine iSup₂_le fun z hz => iSup₂_le fun w hw => ?_
  rw [mem_closedBall_zero_iff] at hz hw
  obtain ⟨i, hi, hzi⟩ := exists_gridPt_near hs hz
  obtain ⟨j, hj, hwj⟩ := exists_gridPt_near hs hw
  set D := S.D γ ω with hD
  set e : ℝ := Real.exp (-S.b γ) with he_def
  set A := holderConst D.1 (Metric.closedBall 0 (R + 1)) with hA_def
  have he : 0 ≤ e := (Real.exp_pos _).le
  have hball : ∀ {x y : ℂ}, ‖x‖ ≤ R → ‖x - y‖ ≤ s →
      x ∈ Metric.closedBall (0 : ℂ) (R + 1) ∧ y ∈ Metric.closedBall (0 : ℂ) (R + 1) := by
    intro x y hx hxy
    refine ⟨mem_closedBall_zero_iff.2 (by linarith), mem_closedBall_zero_iff.2 ?_⟩
    have := norm_sub_norm_le y x
    rw [norm_sub_rev] at this
    linarith
  have hHol : ∀ {x y : ℂ}, ‖x‖ ≤ R → ‖x - y‖ ≤ s →
      ENNReal.ofReal (D.1 (x, y)) ≤ A * ENNReal.ofReal (Real.sqrt s) := by
    intro x y hx hxy
    obtain ⟨hx1, hy1⟩ := hball hx hxy
    refine (ofReal_le_holderConst_mul D hx1 hy1).trans ?_
    gcongr
    rw [Real.sqrt_eq_rpow]
    exact Real.rpow_le_rpow (norm_nonneg _) hxy (by norm_num)
  have hM := le_rpow_sum_rpow (gridIdx s R ×ˢ gridIdx s R)
    (fun ij : (ℤ × ℤ) × (ℤ × ℤ) => ‖e * D.1 (gridPt s ij.1, gridPt s ij.2) -
      ‖gridPt s ij.1 - gridPt s ij.2‖‖ₑ) hP0 (i := (i, j)) (Finset.mem_product.2 ⟨hi, hj⟩)
  have hreal := abs_euclid_sub_le D he z w (gridPt s i) (gridPt s j)
  have hn : ‖z - gridPt s i‖ + ‖w - gridPt s j‖ ≤ 2 * s := by linarith
  calc ENNReal.ofReal |e * D.1 (z, w) - ‖z - w‖|
      ≤ ENNReal.ofReal (|e * D.1 (gridPt s i, gridPt s j) - ‖gridPt s i - gridPt s j‖| +
          e * (D.1 (z, gridPt s i) + D.1 (w, gridPt s j)) +
          (‖z - gridPt s i‖ + ‖w - gridPt s j‖)) := ENNReal.ofReal_le_ofReal hreal
    _ ≤ ENNReal.ofReal |e * D.1 (gridPt s i, gridPt s j) - ‖gridPt s i - gridPt s j‖| +
          ENNReal.ofReal e * (ENNReal.ofReal (D.1 (z, gridPt s i)) +
            ENNReal.ofReal (D.1 (w, gridPt s j))) + ENNReal.ofReal (2 * s) := by
        refine ENNReal.ofReal_add_le.trans (add_le_add (ENNReal.ofReal_add_le.trans
          (add_le_add le_rfl ?_)) (ENNReal.ofReal_le_ofReal hn))
        rw [ENNReal.ofReal_mul he]
        exact mul_le_mul' le_rfl ENNReal.ofReal_add_le
    _ ≤ (∑ ij ∈ gridIdx s R ×ˢ gridIdx s R,
          ‖e * D.1 (gridPt s ij.1, gridPt s ij.2) - ‖gridPt s ij.1 - gridPt s ij.2‖‖ₑ ^ P0) ^
            (1 / P0) +
          ENNReal.ofReal e * (A * ENNReal.ofReal (Real.sqrt s) +
            A * ENNReal.ofReal (Real.sqrt s)) + ENNReal.ofReal (2 * s) := by
        gcongr
        · rw [← Real.enorm_eq_ofReal_abs]
          exact hM
        · exact hHol hz hzi
        · exact hHol hw hwj
    _ = (∑ ij ∈ gridIdx s R ×ˢ gridIdx s R,
          ‖e * D.1 (gridPt s ij.1, gridPt s ij.2) - ‖gridPt s ij.1 - gridPt s ij.2‖‖ₑ ^ P0) ^
            (1 / P0) +
          ENNReal.ofReal (2 * e * Real.sqrt s) * A + ENNReal.ofReal (2 * s) := by
        rw [ENNReal.ofReal_mul (p := 2 * e) (q := Real.sqrt s) (mul_nonneg zero_le_two he),
          ENNReal.ofReal_mul (p := 2) (q := e) zero_le_two, ENNReal.ofReal_ofNat]
        ring

/-- **Blueprint Lemma `lem:euclidean`.** For `R ≥ 1` and `p ≥ 1` there are `γ_* > 0` and `C` with
`E[𝖤_γ(R)^p] ≤ C ξ_γ^{p/2}` for all `γ ∈ (0, γ_*]`. -/
theorem euclidApprox : S.EuclidApprox := by
  intro R hR p hp
  have hp0 : 0 < p := by linarith
  have hR0 : 0 ≤ R := by linarith
  set P0 : ℝ := max p 8 with hP0_def
  have hP0 : 8 ≤ P0 := le_max_right _ _
  have hpP0 : p ≤ P0 := le_max_left _ _
  have hP0pos : 0 < P0 := by linarith
  obtain ⟨γ1, K, hγ1, hpair⟩ := S.exists_eLpNorm_pair_le (2 * R + 4) (P0 := P0) (by linarith)
  obtain ⟨γe, C1, hγe, hγe2, hexp⟩ := S.exists_exponents
  obtain ⟨γb, Cb, hγb, hb⟩ := S.abs_b_le
  obtain ⟨γ6, hγ6, h6⟩ := S.S6 p hp
  obtain ⟨C6, hC6, hC6b⟩ := h6 (Metric.closedBall 0 (R + 1)) (isCompact_closedBall _ _) 1 one_pos
  set K' : ℝ := max K 0 with hK'_def
  have hK' : 0 ≤ K' := le_max_right _ _
  have hC6p : C6 ^ (1 / p) ≠ ⊤ := ENNReal.rpow_ne_top_of_nonneg (by positivity) hC6
  set CA : ℝ := (C6 ^ (1 / p)).toReal with hCA_def
  have hCA : 0 ≤ CA := ENNReal.toReal_nonneg
  set C' : ℝ := (2 * R + 5) * K' + 2 * Real.exp Cb * CA + 2 with hC'_def
  have hC' : 0 ≤ C' := by positivity
  refine ⟨min (min γ1 γe) (min γb γ6), C' ^ p, lt_min (lt_min hγ1 hγe) (lt_min hγb hγ6),
    fun γ hγ => ?_⟩
  obtain ⟨hγ0, hγle⟩ := hγ
  have hγ1' : γ ≤ γ1 := hγle.trans ((min_le_left _ _).trans (min_le_left _ _))
  have hγe' : γ ≤ γe := hγle.trans ((min_le_left _ _).trans (min_le_right _ _))
  have hγb' : γ ≤ γb := hγle.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hγ6' : γ ≤ γ6 := hγle.trans ((min_le_right _ _).trans (min_le_right _ _))
  have hγ2 : γ < 2 := lt_of_le_of_lt hγe' hγe2
  have hξ : 0 < S.ξ γ := S.ξ_pos γ hγ0 hγ2
  have hξ1 : S.ξ γ ≤ 1 := (hexp γ ⟨hγ0, hγe'⟩).2.2.1.trans (by norm_num)
  set ξ : ℝ := S.ξ γ with hξ_def
  -- the grid variable `M` (Step 3)
  set s := gridIdx ξ R ×ˢ gridIdx ξ R with hs_def
  set F : (ℤ × ℤ) × (ℤ × ℤ) → Coord → ℝ := fun ij ω =>
    Real.exp (-S.b γ) * (S.D γ ω).1 (gridPt ξ ij.1, gridPt ξ ij.2) -
      ‖gridPt ξ ij.1 - gridPt ξ ij.2‖ with hF_def
  set M : Coord → ℝ≥0∞ := fun ω => (∑ ij ∈ s, ‖F ij ω‖ₑ ^ P0) ^ (1 / P0) with hM_def
  set A : Coord → ℝ≥0∞ := fun ω => holderConst (S.D γ ω).1 (Metric.closedBall 0 (R + 1))
    with hA_def
  set c : ℝ≥0∞ := ENNReal.ofReal (2 * Real.exp (-S.b γ) * Real.sqrt ξ) with hc_def
  have hpt : ∀ ω, S.euclidErr γ R ω ≤ M ω + c * A ω + ENNReal.ofReal (2 * ξ) :=
    fun ω => S.euclidErr_le_grid γ hξ hξ1 hP0pos ω
  have hFm : ∀ ij, Measurable (F ij) := fun ij =>
    ((S.measurable_D_apply γ _).const_mul _).sub_const _
  have hMm : Measurable M :=
    (Finset.measurable_sum _ fun ij _ => (hFm ij).enorm.pow_const _).pow_const _
  have hAm : Measurable A := S.measurable_holderConst γ _
  have hgrid : ∀ ij ∈ s, eLpNorm (fun ω => ‖F ij ω‖ₑ) (ENNReal.ofReal P0) stdP ≤
      ENNReal.ofReal (K' * ξ) := by
    intro ij hij
    rw [eLpNorm_enorm]
    obtain ⟨hi, hj⟩ := Finset.mem_product.1 hij
    refine (hpair γ ⟨hγ0, hγ1'⟩ _ _ (norm_gridPt_le hξ hξ1 hR0 hi)
      (norm_gridPt_le hξ hξ1 hR0 hj)).trans ?_
    exact ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right (le_max_left _ _) hξ.le)
  have hMP0 := eLpNorm_rpow_sum_rpow_le (μ := stdP) s (fun ij _ => (hFm ij).enorm) hP0pos hgrid
  have hcard : (s.card : ℝ) ≤ ((2 * R + 5) / ξ) ^ 4 := by
    rw [hs_def, Finset.card_product, Nat.cast_mul]
    have h := card_gridIdx_le hξ hξ1 hR0
    calc ((gridIdx ξ R).card : ℝ) * (gridIdx ξ R).card
        ≤ ((2 * R + 5) / ξ) ^ 2 * ((2 * R + 5) / ξ) ^ 2 :=
          mul_le_mul h h (Nat.cast_nonneg _) (by positivity)
      _ = ((2 * R + 5) / ξ) ^ 4 := by ring
  have hM : eLpNorm M (ENNReal.ofReal p) stdP ≤
      ENNReal.ofReal ((2 * R + 5) * K' * Real.sqrt ξ) := by
    calc eLpNorm M (ENNReal.ofReal p) stdP ≤ eLpNorm M (ENNReal.ofReal P0) stdP :=
          eLpNorm_le_eLpNorm_of_exponent_le (ENNReal.ofReal_le_ofReal hpP0)
            hMm.aestronglyMeasurable
      _ ≤ (s.card : ℝ≥0∞) ^ (1 / P0) * ENNReal.ofReal (K' * ξ) := hMP0
      _ = ENNReal.ofReal ((s.card : ℝ) ^ (1 / P0) * (K' * ξ)) := by
          rw [ENNReal.ofReal_mul (Real.rpow_nonneg (Nat.cast_nonneg s.card) (1 / P0)),
            ← ENNReal.ofReal_rpow_of_nonneg (Nat.cast_nonneg _) (by positivity),
            ENNReal.ofReal_natCast]
      _ ≤ ENNReal.ofReal ((2 * R + 5) * K' * Real.sqrt ξ) :=
          ENNReal.ofReal_le_ofReal
            (rpow_card_mul_le (Nat.cast_nonneg _) hcard hP0 hξ hξ1 hR0 hK')
  -- the Hölder term (Step 4)
  have hA : eLpNorm (fun ω => c * A ω) (ENNReal.ofReal p) stdP ≤ c * C6 ^ (1 / p) :=
    eLpNorm_le_of_enorm_le_mul hp0 ENNReal.ofReal_ne_top (fun ω => le_of_eq (enorm_eq_self _))
      (hC6b γ ⟨hγ0, hγ6'⟩).1
  have hexpb : Real.exp (-S.b γ) ≤ Real.exp Cb :=
    Real.exp_le_exp.2 ((neg_le_abs _).trans (hb γ ⟨hγ0, hγb'⟩))
  have hsq : ξ ≤ Real.sqrt ξ := by
    rw [Real.le_sqrt' hξ]
    nlinarith
  have hp1 : (1 : ℝ≥0∞) ≤ ENNReal.ofReal p := by
    rw [← ENNReal.ofReal_one]
    exact ENNReal.ofReal_le_ofReal hp
  -- Minkowski
  have hkey : eLpNorm (S.euclidErr γ R) (ENNReal.ofReal p) stdP ≤
      ENNReal.ofReal (C' * Real.sqrt ξ) := by
    calc eLpNorm (S.euclidErr γ R) (ENNReal.ofReal p) stdP
        ≤ eLpNorm (M + (fun ω => c * A ω) + fun _ => ENNReal.ofReal (2 * ξ))
            (ENNReal.ofReal p) stdP := by
          refine eLpNorm_mono_enorm fun ω => ?_
          simp only [enorm_eq_self, Pi.add_apply]
          exact hpt ω
      _ ≤ eLpNorm M (ENNReal.ofReal p) stdP +
            eLpNorm (fun ω => c * A ω) (ENNReal.ofReal p) stdP +
            eLpNorm (fun _ : Coord => ENNReal.ofReal (2 * ξ)) (ENNReal.ofReal p) stdP := by
          refine (eLpNorm_add_le (hMm.add (hAm.const_mul c)).aestronglyMeasurable
            aestronglyMeasurable_const hp1).trans ?_
          gcongr
          exact eLpNorm_add_le hMm.aestronglyMeasurable (hAm.const_mul c).aestronglyMeasurable hp1
      _ ≤ ENNReal.ofReal ((2 * R + 5) * K' * Real.sqrt ξ) + c * C6 ^ (1 / p) +
            ENNReal.ofReal (2 * ξ) := by
          rw [eLpNorm_const_prob _ (ENNReal.ofReal_pos.2 hp0).ne', enorm_eq_self]
          gcongr
      _ ≤ ENNReal.ofReal ((2 * R + 5) * K' * Real.sqrt ξ) +
            ENNReal.ofReal (2 * Real.exp Cb * CA * Real.sqrt ξ) +
            ENNReal.ofReal (2 * Real.sqrt ξ) := by
          gcongr
          · rw [hc_def, hCA_def, ← ENNReal.ofReal_toReal hC6p, ← ENNReal.ofReal_mul (by positivity),
              ENNReal.toReal_ofReal ENNReal.toReal_nonneg]
            refine ENNReal.ofReal_le_ofReal ?_
            have hs0 : 0 ≤ Real.sqrt ξ := Real.sqrt_nonneg _
            have : 2 * Real.exp (-S.b γ) * Real.sqrt ξ * (C6 ^ (1 / p)).toReal =
                2 * (C6 ^ (1 / p)).toReal * Real.sqrt ξ * Real.exp (-S.b γ) := by ring
            rw [this, show 2 * Real.exp Cb * (C6 ^ (1 / p)).toReal * Real.sqrt ξ =
              2 * (C6 ^ (1 / p)).toReal * Real.sqrt ξ * Real.exp Cb by ring]
            exact mul_le_mul_of_nonneg_left hexpb (by positivity)
      _ = ENNReal.ofReal (C' * Real.sqrt ξ) := by
          rw [← ENNReal.ofReal_add (by positivity) (by positivity),
            ← ENNReal.ofReal_add (by positivity) (by positivity), hC'_def]
          congr 1
          ring
  -- conclusion: `E[𝖤^p] = ‖𝖤‖_p^p ≤ (C' ξ^{1/2})^p`
  have hint := lintegral_enorm_rpow_eq (μ := stdP) hp0 (S.euclidErr γ R)
  simp_rw [enorm_eq_self] at hint
  rw [hint]
  calc eLpNorm (S.euclidErr γ R) (ENNReal.ofReal p) stdP ^ p
      ≤ ENNReal.ofReal (C' * Real.sqrt ξ) ^ p := ENNReal.rpow_le_rpow hkey hp0.le
    _ = ENNReal.ofReal (C' ^ p * ξ ^ (p / 2)) := by
        rw [ENNReal.ofReal_rpow_of_nonneg (by positivity) hp0.le,
          Real.mul_rpow hC' (Real.sqrt_nonneg _), Real.sqrt_eq_rpow, ← Real.rpow_mul hξ.le]
        congr 3
        ring

end Setup

end GaussianLQG
