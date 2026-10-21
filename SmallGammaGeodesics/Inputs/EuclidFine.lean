import GaussianLQG.LQG.Euclid

/-!
# Lemma 2.2′ (Route F): Euclidean approximation at fixed moments (source §2.3)

Source: `source/small-parameter-lqg-geodesics.pdf`, Lemma 2.2 and (2.12)–(2.14). Under ruling G7
(Route F) the source's growing-moment Lemma 2.2 is replaced by Lemma 2.2′ (planning audit GA5,
"Details for later use" (a3); GA3 A2; blueprint Lemma `lem:euclid-fine`), which uses fixed moments only.
Ruling G16 records how Lemma 3.2 consumes the `L²` form.

Notation: `Δ_R = sup_{z,w ∈ B̄_R(0)} |e^{-b_γ} D(z,w) − |z − w||` is `S.euclidErr γ R` (normalization
`e^{-b_γ}`, ruling G8), and `ξ = S.ξ γ`.

* `euclidFine` (Lemma 2.2′ (a)): for `R ≥ 1`, `ε > 0`, `p ≥ 1`, `E[Δ_R^p] ≤ C ξ^{p(1−ε)}` for small `γ`;
* `euclidFine_tail` (Lemma 2.2′ (b)): for `K > 0`, `P[Δ_R > ξ^{1−ε}] ≤ C ξ^K` for small `γ`;
* `euclidFine_L2` (Lemma 2.2′ (c), the form used by Lemma 3.2): `‖Δ_R‖₂ ≤ C ξ^{1−ε}` and `Δ_R < ∞` a.s.

Proof (GA5 (a3)). Let `P₀ = max(p, 16, 16/ε)` and `s = ξ⁴`. Pathwise
(`Setup.euclidErr_le_grid` at mesh `s`, so `√s = ξ²`):
`Δ_R ≤ M + 2 e^{-b} ξ² A_γ(B̄_{R+1}(0)) + 2ξ⁴`, with
`M = (∑_{(z',w') ∈ Λ²} |e^{-b} D(z',w') − |z'−w'||^{P₀})^{1/P₀}` and `#Λ² ≤ ((2R+5)/ξ⁴)⁴`.
By `Setup.exists_eLpNorm_pair_le` (`ρ₀ = 2R + 4`, order `P₀`) and the union bound,
`‖M‖_p ≤ ‖M‖_{P₀} ≤ (#Λ²)^{1/P₀} K ξ ≤ (2R+5) K ξ^{1−16/P₀} ≤ (2R+5) K ξ^{1−ε}`
(`rpow_card_mul_le_fine`); (S6) and `|b_γ| ≤ C_b` bound the Hölder term by `C ξ² ≤ C ξ^{1−ε}`.
Minkowski's inequality gives `‖Δ_R‖_p ≤ C ξ^{1−ε}` (`exists_eLpNorm_euclidErr_le`). Markov's inequality at
order `p = max(1, 2K/ε)` with `ε/2` gives (b).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal

namespace SmallGammaGeodesics

open GaussianLQG

/-- `Δ_R` is nondecreasing in `R`. -/
theorem euclidErr_mono (S : Setup) (γ : ℝ) {R R' : ℝ} (hRR' : R ≤ R') (ω : Coord) :
    S.euclidErr γ R ω ≤ S.euclidErr γ R' ω :=
  iSup₂_le fun z hz => iSup₂_le fun w hw =>
    le_iSup₂_of_le (f := fun z (_ : z ∈ Metric.closedBall (0 : ℂ) R') =>
        ⨆ w ∈ Metric.closedBall (0 : ℂ) R',
          ENNReal.ofReal |Real.exp (-S.b γ) * (S.D γ ω).1 (z, w) - ‖z - w‖|)
      z (Metric.closedBall_subset_closedBall hRR' hz)
      (le_iSup₂_of_le (f := fun w (_ : w ∈ Metric.closedBall (0 : ℂ) R') =>
          ENNReal.ofReal |Real.exp (-S.b γ) * (S.D γ ω).1 (z, w) - ‖z - w‖|)
        w (Metric.closedBall_subset_closedBall hRR' hw) le_rfl)

/-- Exponent bookkeeping for the union bound at mesh `ξ⁴`: if `n ≤ ((2R+5)/ξ⁴)⁴`, `P₀ ≥ 4`,
`ε P₀ ≥ 16`, `0 < ξ ≤ 1`, `R ≥ 0` and `K ≥ 0`, then `n^{1/P₀} (K ξ) ≤ (2R+5) K ξ^{1−ε}`. -/
theorem rpow_card_mul_le_fine {n R ξ K P0 ε : ℝ} (hn0 : 0 ≤ n)
    (hn : n ≤ ((2 * R + 5) / ξ ^ 4) ^ 4) (hP0 : 4 ≤ P0) (hεP0 : 16 ≤ ε * P0) (hξ : 0 < ξ)
    (hξ1 : ξ ≤ 1) (hR : 0 ≤ R) (hK : 0 ≤ K) :
    n ^ (1 / P0) * (K * ξ) ≤ (2 * R + 5) * K * ξ ^ (1 - ε) := by
  have hP0' : 0 < P0 := by linarith
  have hA : 1 ≤ 2 * R + 5 := by linarith
  have hξ4 : 0 < ξ ^ 4 := by positivity
  have hx0 : 0 ≤ (2 * R + 5) / ξ ^ 4 := by positivity
  have h1 : n ^ (1 / P0) ≤ (2 * R + 5) ^ (4 / P0) / ξ ^ (16 / P0) := by
    calc n ^ (1 / P0) ≤ (((2 * R + 5) / ξ ^ 4) ^ 4) ^ (1 / P0) :=
          Real.rpow_le_rpow hn0 hn (by positivity)
      _ = ((2 * R + 5) / ξ ^ 4) ^ (4 / P0) := by
          rw [← Real.rpow_natCast, ← Real.rpow_mul hx0]
          congr 1
          push_cast
          ring
      _ = (2 * R + 5) ^ (4 / P0) / (ξ ^ 4) ^ (4 / P0) := Real.div_rpow (by linarith) hξ4.le _
      _ = (2 * R + 5) ^ (4 / P0) / ξ ^ (16 / P0) := by
          rw [← Real.rpow_natCast ξ 4, ← Real.rpow_mul hξ.le]
          congr 2
          push_cast
          ring
  have h2 : (2 * R + 5) ^ (4 / P0) ≤ 2 * R + 5 := by
    calc (2 * R + 5) ^ (4 / P0) ≤ (2 * R + 5) ^ (1 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le hA (by rw [div_le_one hP0']; linarith)
      _ = 2 * R + 5 := Real.rpow_one _
  have h16 : 16 / P0 ≤ ε := by rw [div_le_iff₀ hP0']; linarith
  have h3 : ξ / ξ ^ (16 / P0) ≤ ξ ^ (1 - ε) := by
    calc ξ / ξ ^ (16 / P0) = ξ ^ (1 - 16 / P0) := by rw [Real.rpow_sub hξ, Real.rpow_one]
      _ ≤ ξ ^ (1 - ε) := Real.rpow_le_rpow_of_exponent_ge hξ hξ1 (by linarith)
  have hξp : 0 < ξ ^ (16 / P0) := Real.rpow_pos_of_pos hξ _
  calc n ^ (1 / P0) * (K * ξ) ≤ (2 * R + 5) ^ (4 / P0) / ξ ^ (16 / P0) * (K * ξ) :=
        mul_le_mul_of_nonneg_right h1 (by positivity)
    _ = (2 * R + 5) ^ (4 / P0) * K * (ξ / ξ ^ (16 / P0)) := by ring
    _ ≤ (2 * R + 5) * K * ξ ^ (1 - ε) := by gcongr

/-- **Lemma 2.2′ (a), `L^p`-norm form** (GA5 (a3), steps 1–4). For `R ≥ 1`, `ε > 0` and `p ≥ 1` there
are `γs > 0` and `C ≥ 0` such that for `γ ∈ (0, γs]`: `0 < ξ_γ ≤ 1` and `‖Δ_R‖_p ≤ C ξ_γ^{1−ε}`. -/
theorem exists_eLpNorm_euclidErr_le (S : Setup) {R : ℝ} (hR : 1 ≤ R) {ε : ℝ} (hε : 0 < ε)
    {p : ℝ} (hp : 1 ≤ p) : ∃ γs C : ℝ, 0 < γs ∧ 0 ≤ C ∧ ∀ γ ∈ Ioc (0 : ℝ) γs,
      0 < S.ξ γ ∧ S.ξ γ ≤ 1 ∧
      eLpNorm (S.euclidErr γ R) (ENNReal.ofReal p) stdP ≤
        ENNReal.ofReal (C * S.ξ γ ^ (1 - ε)) := by
  have hp0 : 0 < p := by linarith
  have hR0 : 0 ≤ R := by linarith
  set P0 : ℝ := max (max p 16) (16 / ε) with hP0_def
  have hpP0 : p ≤ P0 := (le_max_left _ _).trans (le_max_left _ _)
  have h16 : 16 ≤ P0 := (le_max_right _ _).trans (le_max_left _ _)
  have hεP0 : 16 ≤ ε * P0 := by
    have h := (le_max_right _ _ : 16 / ε ≤ P0)
    rw [div_le_iff₀ hε] at h
    linarith
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
  refine ⟨min (min γ1 γe) (min γb γ6), C', lt_min (lt_min hγ1 hγe) (lt_min hγb hγ6), hC',
    fun γ hγ => ?_⟩
  obtain ⟨hγ0, hγle⟩ := hγ
  have hγ1' : γ ≤ γ1 := hγle.trans ((min_le_left _ _).trans (min_le_left _ _))
  have hγe' : γ ≤ γe := hγle.trans ((min_le_left _ _).trans (min_le_right _ _))
  have hγb' : γ ≤ γb := hγle.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hγ6' : γ ≤ γ6 := hγle.trans ((min_le_right _ _).trans (min_le_right _ _))
  have hγ2 : γ < 2 := lt_of_le_of_lt hγe' hγe2
  have hξ : 0 < S.ξ γ := S.ξ_pos γ hγ0 hγ2
  have hξ1 : S.ξ γ ≤ 1 := (hexp γ ⟨hγ0, hγe'⟩).2.2.1.trans (by norm_num)
  refine ⟨hξ, hξ1, ?_⟩
  set ξ : ℝ := S.ξ γ with hξ_def
  set s : ℝ := ξ ^ 4 with hs_def
  have hs : 0 < s := by positivity
  have hs1 : s ≤ 1 := pow_le_one₀ hξ.le hξ1
  have hsqrt : Real.sqrt s = ξ ^ 2 := by
    rw [hs_def, show ξ ^ 4 = (ξ ^ 2) ^ 2 by ring, Real.sqrt_sq (by positivity)]
  -- exponent comparisons: `ξ², ξ⁴ ≤ ξ^{1-ε}`
  have hξ2 : ξ ^ 2 ≤ ξ ^ (1 - ε) := by
    have h := Real.rpow_le_rpow_of_exponent_ge hξ hξ1 (show 1 - ε ≤ ((2 : ℕ) : ℝ) by
      push_cast; linarith)
    rwa [Real.rpow_natCast] at h
  have hξ4 : ξ ^ 4 ≤ ξ ^ (1 - ε) := by
    have h := Real.rpow_le_rpow_of_exponent_ge hξ hξ1 (show 1 - ε ≤ ((4 : ℕ) : ℝ) by
      push_cast; linarith)
    rwa [Real.rpow_natCast] at h
  have hξε : 0 ≤ ξ ^ (1 - ε) := Real.rpow_nonneg hξ.le _
  -- the grid variable `M` (step 1)
  set G := gridIdx s R ×ˢ gridIdx s R with hG_def
  set F : (ℤ × ℤ) × (ℤ × ℤ) → Coord → ℝ := fun ij ω =>
    Real.exp (-S.b γ) * (S.D γ ω).1 (gridPt s ij.1, gridPt s ij.2) -
      ‖gridPt s ij.1 - gridPt s ij.2‖ with hF_def
  set M : Coord → ℝ≥0∞ := fun ω => (∑ ij ∈ G, ‖F ij ω‖ₑ ^ P0) ^ (1 / P0) with hM_def
  set A : Coord → ℝ≥0∞ := fun ω => holderConst (S.D γ ω).1 (Metric.closedBall 0 (R + 1))
    with hA_def
  set c : ℝ≥0∞ := ENNReal.ofReal (2 * Real.exp (-S.b γ) * Real.sqrt s) with hc_def
  have hpt : ∀ ω, S.euclidErr γ R ω ≤ M ω + c * A ω + ENNReal.ofReal (2 * s) :=
    fun ω => S.euclidErr_le_grid γ hs hs1 hP0pos ω
  have hFm : ∀ ij, Measurable (F ij) := fun ij =>
    ((S.measurable_D_apply γ _).const_mul _).sub_const _
  have hMm : Measurable M :=
    (Finset.measurable_sum _ fun ij _ => (hFm ij).enorm.pow_const _).pow_const _
  have hAm : Measurable A := S.measurable_holderConst γ _
  -- the grid term (step 2)
  have hgrid : ∀ ij ∈ G, eLpNorm (fun ω => ‖F ij ω‖ₑ) (ENNReal.ofReal P0) stdP ≤
      ENNReal.ofReal (K' * ξ) := by
    intro ij hij
    rw [eLpNorm_enorm]
    obtain ⟨hi, hj⟩ := Finset.mem_product.1 hij
    refine (hpair γ ⟨hγ0, hγ1'⟩ _ _ (norm_gridPt_le hs hs1 hR0 hi)
      (norm_gridPt_le hs hs1 hR0 hj)).trans ?_
    exact ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right (le_max_left _ _) hξ.le)
  have hMP0 := eLpNorm_rpow_sum_rpow_le (μ := stdP) G (fun ij _ => (hFm ij).enorm) hP0pos hgrid
  have hcard : (G.card : ℝ) ≤ ((2 * R + 5) / ξ ^ 4) ^ 4 := by
    rw [hG_def, Finset.card_product, Nat.cast_mul]
    have h := card_gridIdx_le hs hs1 hR0
    calc ((gridIdx s R).card : ℝ) * (gridIdx s R).card
        ≤ ((2 * R + 5) / s) ^ 2 * ((2 * R + 5) / s) ^ 2 :=
          mul_le_mul h h (Nat.cast_nonneg _) (by positivity)
      _ = ((2 * R + 5) / ξ ^ 4) ^ 4 := by rw [hs_def]; ring
  have hM : eLpNorm M (ENNReal.ofReal p) stdP ≤
      ENNReal.ofReal ((2 * R + 5) * K' * ξ ^ (1 - ε)) := by
    calc eLpNorm M (ENNReal.ofReal p) stdP ≤ eLpNorm M (ENNReal.ofReal P0) stdP :=
          eLpNorm_le_eLpNorm_of_exponent_le (ENNReal.ofReal_le_ofReal hpP0)
            hMm.aestronglyMeasurable
      _ ≤ (G.card : ℝ≥0∞) ^ (1 / P0) * ENNReal.ofReal (K' * ξ) := hMP0
      _ = ENNReal.ofReal ((G.card : ℝ) ^ (1 / P0) * (K' * ξ)) := by
          rw [ENNReal.ofReal_mul (Real.rpow_nonneg (Nat.cast_nonneg G.card) (1 / P0)),
            ← ENNReal.ofReal_rpow_of_nonneg (Nat.cast_nonneg _) (by positivity),
            ENNReal.ofReal_natCast]
      _ ≤ ENNReal.ofReal ((2 * R + 5) * K' * ξ ^ (1 - ε)) :=
          ENNReal.ofReal_le_ofReal
            (rpow_card_mul_le_fine (Nat.cast_nonneg _) hcard (by linarith) hεP0 hξ hξ1 hR0 hK')
  -- the Hölder term (step 3)
  have hAterm : eLpNorm (fun ω => c * A ω) (ENNReal.ofReal p) stdP ≤ c * C6 ^ (1 / p) :=
    eLpNorm_le_of_enorm_le_mul hp0 ENNReal.ofReal_ne_top (fun ω => le_of_eq (enorm_eq_self _))
      (hC6b γ ⟨hγ0, hγ6'⟩).1
  have hexpb : Real.exp (-S.b γ) ≤ Real.exp Cb :=
    Real.exp_le_exp.2 ((neg_le_abs _).trans (hb γ ⟨hγ0, hγb'⟩))
  have hcA : c * C6 ^ (1 / p) ≤ ENNReal.ofReal (2 * Real.exp Cb * CA * ξ ^ (1 - ε)) := by
    rw [hc_def, ← ENNReal.ofReal_toReal hC6p, ← ENNReal.ofReal_mul (by positivity), hsqrt]
    refine ENNReal.ofReal_le_ofReal ?_
    calc 2 * Real.exp (-S.b γ) * ξ ^ 2 * (C6 ^ (1 / p)).toReal
        ≤ 2 * Real.exp Cb * ξ ^ (1 - ε) * CA := by gcongr
      _ = 2 * Real.exp Cb * CA * ξ ^ (1 - ε) := by ring
  -- Minkowski (step 4)
  have hp1 : (1 : ℝ≥0∞) ≤ ENNReal.ofReal p := by
    rw [← ENNReal.ofReal_one]
    exact ENNReal.ofReal_le_ofReal hp
  calc eLpNorm (S.euclidErr γ R) (ENNReal.ofReal p) stdP
      ≤ eLpNorm (M + (fun ω => c * A ω) + fun _ => ENNReal.ofReal (2 * s))
          (ENNReal.ofReal p) stdP := by
        refine eLpNorm_mono_enorm fun ω => ?_
        simp only [enorm_eq_self, Pi.add_apply]
        exact hpt ω
    _ ≤ eLpNorm M (ENNReal.ofReal p) stdP +
          eLpNorm (fun ω => c * A ω) (ENNReal.ofReal p) stdP +
          eLpNorm (fun _ : Coord => ENNReal.ofReal (2 * s)) (ENNReal.ofReal p) stdP := by
        refine (eLpNorm_add_le (hMm.add (hAm.const_mul c)).aestronglyMeasurable
          aestronglyMeasurable_const hp1).trans ?_
        gcongr
        exact eLpNorm_add_le hMm.aestronglyMeasurable (hAm.const_mul c).aestronglyMeasurable hp1
    _ ≤ ENNReal.ofReal ((2 * R + 5) * K' * ξ ^ (1 - ε)) +
          ENNReal.ofReal (2 * Real.exp Cb * CA * ξ ^ (1 - ε)) +
          ENNReal.ofReal (2 * ξ ^ (1 - ε)) := by
        rw [eLpNorm_const_prob _ (ENNReal.ofReal_pos.2 hp0).ne', enorm_eq_self]
        refine add_le_add (add_le_add hM (hAterm.trans hcA)) (ENNReal.ofReal_le_ofReal ?_)
        rw [hs_def]
        linarith
    _ = ENNReal.ofReal (C' * ξ ^ (1 - ε)) := by
        rw [← ENNReal.ofReal_add (by positivity) (by positivity),
          ← ENNReal.ofReal_add (by positivity) (by positivity), hC'_def]
        congr 1
        ring

/-- **Lemma 2.2′ (a)**, with the facts used downstream: for `R ≥ 1`, `ε > 0` and `p ≥ 1` there are
`γs > 0` and `C ≥ 0` such that for `γ ∈ (0, γs]`: `0 < ξ_γ ≤ 1` and `E[Δ_R^p] ≤ C ξ_γ^{p(1−ε)}`. -/
theorem exists_lintegral_euclidErr_rpow_le (S : Setup) {R : ℝ} (hR : 1 ≤ R) {ε : ℝ} (hε : 0 < ε)
    {p : ℝ} (hp : 1 ≤ p) : ∃ γs C : ℝ, 0 < γs ∧ 0 ≤ C ∧ ∀ γ ∈ Ioc (0 : ℝ) γs,
      0 < S.ξ γ ∧ S.ξ γ ≤ 1 ∧
      (∫⁻ ω, S.euclidErr γ R ω ^ p ∂stdP) ≤ ENNReal.ofReal (C * S.ξ γ ^ (p * (1 - ε))) := by
  have hp0 : 0 < p := by linarith
  obtain ⟨γs, C, hγs, hC, h⟩ := exists_eLpNorm_euclidErr_le S hR hε hp
  refine ⟨γs, C ^ p, hγs, Real.rpow_nonneg hC _, fun γ hγ => ?_⟩
  obtain ⟨hξ, hξ1, hnorm⟩ := h γ hγ
  refine ⟨hξ, hξ1, ?_⟩
  have hint := lintegral_enorm_rpow_eq (μ := stdP) hp0 (S.euclidErr γ R)
  simp_rw [enorm_eq_self] at hint
  rw [hint]
  calc eLpNorm (S.euclidErr γ R) (ENNReal.ofReal p) stdP ^ p
      ≤ ENNReal.ofReal (C * S.ξ γ ^ (1 - ε)) ^ p := ENNReal.rpow_le_rpow hnorm hp0.le
    _ = ENNReal.ofReal (C ^ p * S.ξ γ ^ (p * (1 - ε))) := by
        rw [ENNReal.ofReal_rpow_of_nonneg (mul_nonneg hC (Real.rpow_nonneg hξ.le _)) hp0.le,
          Real.mul_rpow hC (Real.rpow_nonneg hξ.le _), ← Real.rpow_mul hξ.le, mul_comm (1 - ε) p]

/-- **Lemma 2.2′ (a)** (Route F, ruling G7; GA5 (a3), GA3 A2): for `R ≥ 1`, `ε > 0` and `p ≥ 1` there
are `γs > 0` and `C` with `E[Δ_R^p] ≤ C ξ_γ^{p(1−ε)}` for all `γ ∈ (0, γs]`. -/
theorem euclidFine (S : Setup) : ∀ R : ℝ, 1 ≤ R → ∀ ε : ℝ, 0 < ε → ∀ p : ℝ, 1 ≤ p →
    ∃ γs C : ℝ, 0 < γs ∧
    ∀ γ ∈ Ioc (0 : ℝ) γs,
      (∫⁻ ω, S.euclidErr γ R ω ^ p ∂stdP) ≤ ENNReal.ofReal (C * S.ξ γ ^ (p * (1 - ε))) := by
  intro R hR ε hε p hp
  obtain ⟨γs, C, hγs, -, h⟩ := exists_lintegral_euclidErr_rpow_le S hR hε hp
  exact ⟨γs, C, hγs, fun γ hγ => (h γ hγ).2.2⟩

/-- **Lemma 2.2′ (b)** (GA5 (a3), step 4): for `R ≥ 1`, `ε > 0` and `K > 0` there are `γs > 0` and `C`
with `P[Δ_R > ξ_γ^{1−ε}] ≤ C ξ_γ^K` for all `γ ∈ (0, γs]`. Proof: (a) with `ε/2` at order
`p = max(1, 2K/ε)` and Markov's inequality. -/
theorem euclidFine_tail (S : Setup) : ∀ R : ℝ, 1 ≤ R → ∀ ε : ℝ, 0 < ε → ∀ K : ℝ, 0 < K →
    ∃ γs C : ℝ, 0 < γs ∧
    ∀ γ ∈ Ioc (0 : ℝ) γs,
      stdP {ω | ENNReal.ofReal (S.ξ γ ^ (1 - ε)) < S.euclidErr γ R ω} ≤
        ENNReal.ofReal (C * S.ξ γ ^ K) := by
  intro R hR ε hε K hK
  set p : ℝ := max 1 (2 * K / ε) with hp_def
  have hp : 1 ≤ p := le_max_left _ _
  have hp0 : 0 < p := by linarith
  have hpK : K ≤ p * (ε / 2) := by
    have h : 2 * K / ε ≤ p := le_max_right _ _
    rw [div_le_iff₀ hε] at h
    linarith
  obtain ⟨γs, C, hγs, hC, h⟩ := exists_lintegral_euclidErr_rpow_le S hR (half_pos hε) hp
  refine ⟨γs, C, hγs, fun γ hγ => ?_⟩
  obtain ⟨hξ, hξ1, hint⟩ := h γ hγ
  set ξ : ℝ := S.ξ γ with hξ_def
  set t : ℝ≥0∞ := ENNReal.ofReal (ξ ^ (1 - ε)) ^ p with ht_def
  have ht0 : t ≠ 0 :=
    (ENNReal.rpow_pos (ENNReal.ofReal_pos.2 (Real.rpow_pos_of_pos hξ _))
      ENNReal.ofReal_ne_top).ne'
  have httop : t ≠ ⊤ := ENNReal.rpow_ne_top_of_nonneg hp0.le ENNReal.ofReal_ne_top
  have ht : t = ENNReal.ofReal (ξ ^ (p * (1 - ε))) := by
    rw [ht_def, ENNReal.ofReal_rpow_of_nonneg (Real.rpow_nonneg hξ.le _) hp0.le,
      ← Real.rpow_mul hξ.le, mul_comm (1 - ε) p]
  have hsub : {ω | ENNReal.ofReal (ξ ^ (1 - ε)) < S.euclidErr γ R ω} ⊆
      {ω | t ≤ S.euclidErr γ R ω ^ p} :=
    fun ω hω => ENNReal.rpow_le_rpow (le_of_lt hω) hp0.le
  have hexp : p * (1 - ε / 2) - p * (1 - ε) = p * (ε / 2) := by ring
  calc stdP {ω | ENNReal.ofReal (ξ ^ (1 - ε)) < S.euclidErr γ R ω}
      ≤ stdP {ω | t ≤ S.euclidErr γ R ω ^ p} := measure_mono hsub
    _ ≤ (∫⁻ ω, S.euclidErr γ R ω ^ p ∂stdP) / t :=
        meas_ge_le_lintegral_div ((S.measurable_euclidErr γ R).pow_const p).aemeasurable ht0
          httop
    _ ≤ ENNReal.ofReal (C * ξ ^ (p * (1 - ε / 2))) / t := by gcongr
    _ = ENNReal.ofReal (C * ξ ^ (p * (ε / 2))) := by
        rw [ht, ← ENNReal.ofReal_div_of_pos (Real.rpow_pos_of_pos hξ _), mul_div_assoc,
          ← Real.rpow_sub hξ, hexp]
    _ ≤ ENNReal.ofReal (C * ξ ^ K) :=
        ENNReal.ofReal_le_ofReal
          (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_ge hξ hξ1 hpK) hC)

/-- **Lemma 2.2′ (b) at a fixed level** (the complement bound of Lemma 3.2, GA2-07 and ruling G16): for
`R ≥ 1`, `d₀ > 0` and `K > 0` there are `γs > 0` and `C` with `P[Δ_R > d₀] ≤ C ξ_γ^K` for all
`γ ∈ (0, γs]`. Proof: `euclidFine_tail` with `ε = 1/2`, and `ξ_γ^{1/2} ≤ γ^{1/2} ≤ d₀` for `γ ≤ d₀²`. -/
theorem euclidFine_tail_const (S : Setup) : ∀ R : ℝ, 1 ≤ R → ∀ d₀ : ℝ, 0 < d₀ → ∀ K : ℝ, 0 < K →
    ∃ γs C : ℝ, 0 < γs ∧ ∀ γ ∈ Ioc (0 : ℝ) γs,
      stdP {ω | ENNReal.ofReal d₀ < S.euclidErr γ R ω} ≤ ENNReal.ofReal (C * S.ξ γ ^ K) := by
  intro R hR d₀ hd₀ K hK
  obtain ⟨γs, C, hγs, h⟩ := euclidFine_tail S R hR (1 / 2) one_half_pos K hK
  obtain ⟨γe, C1, hγe, hγe2, hexp⟩ := S.exists_exponents
  refine ⟨min (min γs γe) (d₀ ^ 2), C, lt_min (lt_min hγs hγe) (by positivity), fun γ hγ => ?_⟩
  obtain ⟨hγ0, hγle⟩ := hγ
  have hγs' : γ ≤ γs := hγle.trans ((min_le_left _ _).trans (min_le_left _ _))
  have hγe' : γ ≤ γe := hγle.trans ((min_le_left _ _).trans (min_le_right _ _))
  have hγd : γ ≤ d₀ ^ 2 := hγle.trans (min_le_right _ _)
  have hξγ : S.ξ γ ≤ γ := (hexp γ ⟨hγ0, hγe'⟩).2.1
  have hsq : S.ξ γ ^ (1 - 1 / 2 : ℝ) ≤ d₀ := by
    rw [show (1 - 1 / 2 : ℝ) = 1 / 2 by norm_num, ← Real.sqrt_eq_rpow]
    calc Real.sqrt (S.ξ γ) ≤ Real.sqrt (d₀ ^ 2) := Real.sqrt_le_sqrt (hξγ.trans hγd)
      _ = d₀ := Real.sqrt_sq hd₀.le
  refine (measure_mono fun ω hω => ?_).trans (h γ ⟨hγ0, hγs'⟩)
  exact lt_of_le_of_lt (ENNReal.ofReal_le_ofReal hsq) hω

/-- **Lemma 2.2′ (c)**, the `L²` form used by Lemma 3.2 (ruling G16): for `R ≥ 1` and `ε > 0` there are
`γs > 0` and `C` such that for `γ ∈ (0, γs]`, `‖Δ_R‖₂ ≤ C ξ_γ^{1−ε}` (for the real-valued
`Δ_R.toReal`) and `Δ_R < ∞` almost surely. -/
theorem euclidFine_L2 (S : Setup) : ∀ R : ℝ, 1 ≤ R → ∀ ε : ℝ, 0 < ε → ∃ γs C : ℝ, 0 < γs ∧
    ∀ γ ∈ Ioc (0 : ℝ) γs,
      eLpNorm (fun ω => (S.euclidErr γ R ω).toReal) 2 stdP ≤
        ENNReal.ofReal (C * S.ξ γ ^ (1 - ε)) ∧
      ∀ᵐ ω ∂stdP, S.euclidErr γ R ω ≠ ⊤ := by
  intro R hR ε hε
  obtain ⟨γs, C, hγs, -, h⟩ := exists_eLpNorm_euclidErr_le S hR hε (p := 2) one_le_two
  refine ⟨γs, C, hγs, fun γ hγ => ?_⟩
  obtain ⟨-, -, hnorm⟩ := h γ hγ
  rw [ENNReal.ofReal_ofNat] at hnorm
  refine ⟨(eLpNorm_mono_enorm fun ω => ?_).trans hnorm, ?_⟩
  · rw [enorm_eq_self, Real.enorm_eq_ofReal ENNReal.toReal_nonneg]
    exact ENNReal.ofReal_toReal_le
  · have hlt : eLpNorm (S.euclidErr γ R) 2 stdP ≠ ⊤ := (hnorm.trans_lt ENNReal.ofReal_lt_top).ne
    have hint : ∫⁻ ω, S.euclidErr γ R ω ^ (2 : ℝ) ∂stdP ≠ ⊤ := by
      have h2 := lintegral_enorm_rpow_eq (μ := stdP) (two_pos : (0 : ℝ) < 2) (S.euclidErr γ R)
      simp_rw [enorm_eq_self] at h2
      rw [h2, ENNReal.ofReal_ofNat]
      exact ENNReal.rpow_ne_top_of_nonneg zero_le_two hlt
    filter_upwards [ae_lt_top ((S.measurable_euclidErr γ R).pow_const _) hint] with ω hω htop
    rw [htop, ENNReal.top_rpow_of_pos two_pos] at hω
    exact lt_irrefl _ hω

end SmallGammaGeodesics
