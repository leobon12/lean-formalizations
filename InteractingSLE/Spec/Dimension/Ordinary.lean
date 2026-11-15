import InteractingSLE.Spec.Dimension.OnePoint
import InteractingSLE.Spec.Dimension.BoxCounting

/-!
# Aux. lemma 14: a strict interior dimension bound for ordinary chordal SLE_κ, `0 < κ < 8`

Specification, Aux. lemma 14 (`source/spec/p049-096.md`, lines 794–854, p. 86–88): for each
`0 < κ < 8` there is a deterministic `d_κ < 2` such that almost surely the ordinary chordal SLE_κ
trace has interior Hausdorff dimension at most `d_κ`, and on every compact `K ⋐ ℍ` the number
`N_δ` of dyadic squares of side `δ` meeting the trace in `K` satisfies `N_δ ≤ C_K δ^{-d_κ}` for all
small dyadic `δ`.

Proof (as in the specification, from (DU6) of `OnePoint.lean`, with `β_κ = 1 − κ/8`): a square
of side `δ = 2^{-n}` meeting the trace in `K` has its center within `2δ` of the trace, so
`E N_δ ≤ C_K δ^{-2+β_κ}`; Markov's inequality gives `P[N_δ > δ^{-2+β_κ/2}] ≤ C_K δ^{β_κ/2}`, which is
summable over dyadic scales; Borel–Cantelli gives the box-counting bound with
`d_κ = 2 − β_κ/2 = 3/2 + κ/16`, and a countable compact exhaustion of `ℍ` gives the dimension
bound. No measurability of the trace is needed: the events are replaced by measurable hulls
(`toMeasurable`) of the same probability.
-/

noncomputable section

open Set Filter Topology Metric MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace InteractingSLE.Dimension

open QuantumZipper

/-- The deterministic interior dimension bound `d_κ = 2 − β_κ / 2` of Aux. lemma 14. -/
def interiorDimBound (κ : ℝ) : ℝ := 2 - onePointExponent κ / 2

theorem interiorDimBound_lt_two {κ : ℝ} (hκ8 : κ < 8) : interiorDimBound κ < 2 := by
  have := onePointExponent_pos hκ8
  unfold interiorDimBound; linarith

theorem interiorDimBound_nonneg {κ : ℝ} (hκ : 0 < κ) : 0 ≤ interiorDimBound κ := by
  have := onePointExponent_le_one hκ
  unfold interiorDimBound; linarith

/-- **The support-removal margin** (specification p. 89, "Consequence for joint-coupling
comparisons"): for `0 < ε < β_κ / 4`, `d_κ = 2 − β_κ/2 < 2 − 2ε`, so (DU7) supplies (SR3). -/
theorem interiorDimBound_lt_two_sub {κ ε : ℝ} (hε : ε < onePointExponent κ / 4) :
    interiorDimBound κ < 2 - 2 * ε := by
  unfold interiorDimBound; linarith

/-- `4^n (2^n)^{-β} / (2^n)^{2 − β/2} = ((2^{β/2})⁻¹)^n`. -/
theorem pow_div_rpow_eq (n : ℕ) (β : ℝ) :
    ((2 : ℝ) ^ n) ^ 2 * (((2 : ℝ) ^ n) ^ β)⁻¹ / ((2 : ℝ) ^ n) ^ (2 - β / 2)
      = (((2 : ℝ) ^ (β / 2))⁻¹) ^ n := by
  have h2 : (0 : ℝ) ≤ 2 := by norm_num
  have hv : (0 : ℝ) < 2 ^ n := two_pow_pos n
  have e : ∀ x : ℝ, ((2 : ℝ) ^ n) ^ x = ((2 : ℝ) ^ x) ^ n := fun x => by
    rw [← Real.rpow_natCast, ← Real.rpow_mul h2, mul_comm, Real.rpow_mul_natCast h2]
  rw [inv_pow, ← e (β / 2), ← Real.rpow_two]
  simp only [← Real.rpow_neg hv.le]
  rw [← Real.rpow_add hv, ← Real.rpow_sub hv]
  congr 1
  ring

/-- **Box counting on one compact set** (proof of Aux. lemma 14, p. 88). For `0 < κ < 8` and a
set `K ⊆ closedBall 0 R` on which `Im ≥ h > 0`, almost surely for all large `n` the number of
dyadic squares of side `2^{-n}` meeting `γ ∩ K` is at most `(2^n)^{d_κ}`. -/
theorem ae_eventually_dyadicCount_le {κ : ℝ} (hκ : 0 < κ) (hκ8 : κ < 8) {Ω : Type}
    [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P] (B : ℝ≥0 → Ω → ℝ)
    (hB : IsBrownianReal B P) {K : Set ℂ} {R h : ℝ} (hR : 0 ≤ R) (hKR : K ⊆ closedBall 0 R)
    (hh : 0 < h) (hKh : ∀ x ∈ K, h ≤ x.im) :
    ∀ᵐ ω ∂P, ∀ᶠ n in atTop, (dyadicCount n (sleTrace κ B ω '' Ici 0 ∩ K) : ℝ)
      ≤ ((2 : ℝ) ^ n) ^ interiorDimBound κ := by
  classical
  obtain ⟨C, hC0, hC⟩ := prob_infDist_sleTrace_lt hκ hκ8
  set β := onePointExponent κ with hβ
  have hβ0 : 0 < β := onePointExponent_pos hκ8
  set d := interiorDimBound κ with hd
  set A : Ω → Set ℂ := fun ω => sleTrace κ B ω '' Ici 0 ∩ K with hA
  set E : ℕ → ℤ × ℤ → Set Ω := fun n k => {ω | k ∈ dyadicHits n (A ω)} with hE
  set Bad : ℕ → Set Ω := fun n => {ω | ((2 : ℝ) ^ n) ^ d < (dyadicCount n (A ω) : ℝ)} with hBad
  -- the one-point estimate for each square
  set a : ℝ := C * (4 / h) ^ β with ha
  have ha0 : 0 ≤ a := by positivity
  obtain ⟨n₀, hn₀⟩ : ∃ n₀ : ℕ, ∀ n ≥ n₀, 1 / (2 : ℝ) ^ n ≤ h / 2 := by
    obtain ⟨n₀, hn⟩ := exists_pow_lt_of_lt_one (by positivity : (0 : ℝ) < h / 2)
      (by norm_num : (1 / 2 : ℝ) < 1)
    refine ⟨n₀, fun n hn' => ?_⟩
    rw [one_div, ← inv_pow]
    calc (2 : ℝ)⁻¹ ^ n ≤ (2 : ℝ)⁻¹ ^ n₀ :=
          pow_le_pow_of_le_one (by norm_num) (by norm_num) hn'
      _ = (1 / 2) ^ n₀ := by rw [one_div]
      _ ≤ h / 2 := hn.le
  have hE_le : ∀ n ≥ n₀, ∀ k, P (E n k) ≤ ENNReal.ofReal (a * (((2 : ℝ) ^ n) ^ β)⁻¹) := by
    intro n hn k
    by_cases hk : k ∈ dyadicHits n K
    · obtain ⟨x, hxS, hxK⟩ := hk
      set c := dyadicCenter n k
      have hv := two_pow_pos n
      have hxc : dist x c ≤ 1 / 2 ^ n := dist_dyadicCenter_le hxS
      have hcim : h / 2 ≤ c.im := by
        have h1 : |x.im - c.im| ≤ dist x c := by
          rw [dist_eq_norm, ← Complex.sub_im]; exact Complex.abs_im_le_norm _
        have := (abs_le.1 (h1.trans hxc)).2
        have := hKh x hxK
        have := hn₀ n hn
        linarith
      have hcH : c ∈ H := show 0 < c.im by linarith
      have hr : (0 : ℝ) < 2 / 2 ^ n := by positivity
      have hsub : E n k ⊆ {ω | infDist c (sleTrace κ B ω '' Ici 0) < 2 / 2 ^ n} := by
        rintro ω ⟨y, hyS, hyγ, _⟩
        have hyc : dist y c ≤ 1 / 2 ^ n := dist_dyadicCenter_le hyS
        calc infDist c (sleTrace κ B ω '' Ici 0) ≤ dist c y := infDist_le_dist_of_mem hyγ
          _ ≤ 1 / 2 ^ n := by rw [dist_comm]; exact hyc
          _ < 2 / 2 ^ n := by gcongr; norm_num
      refine (measure_mono hsub).trans ((hC P B hB c hcH _ hr).trans (ENNReal.ofReal_le_ofReal ?_))
      -- `C (2/2^n / Im c)^β ≤ C (4/h)^β (2^n)^{-β}`
      have hq : 2 / 2 ^ n / c.im ≤ 4 / h / 2 ^ n := by
        rw [div_le_iff₀ (by linarith : (0 : ℝ) < c.im)]
        have : 4 / h / 2 ^ n * c.im ≥ 4 / h / 2 ^ n * (h / 2) :=
          mul_le_mul_of_nonneg_left hcim (by positivity)
        have e : 4 / h / 2 ^ n * (h / 2) = 2 / 2 ^ n := by field_simp; ring
        linarith
      have hq0 : 0 ≤ 2 / 2 ^ n / c.im := by
        have : 0 < c.im := hcH
        positivity
      calc C * (2 / 2 ^ n / c.im) ^ β ≤ C * (4 / h / 2 ^ n) ^ β :=
            mul_le_mul_of_nonneg_left (Real.rpow_le_rpow hq0 hq hβ0.le) hC0
        _ = a * (((2 : ℝ) ^ n) ^ β)⁻¹ := by
            rw [ha, Real.div_rpow (by positivity) hv.le, div_eq_mul_inv, mul_assoc]
    · have : E n k = ∅ := by
        ext ω
        simp only [hE, mem_ofPred_eq, mem_empty_iff_false, iff_false]
        exact fun hω => hk (dyadicHits_mono inter_subset_right hω)
      rw [this, measure_empty]; exact zero_le
  -- Markov's inequality on measurable hulls of the hit events
  set box : ℕ → Finset (ℤ × ℤ) := fun n => dyadicBox n R with hbox
  have hhits_box : ∀ n ω, dyadicHits n (A ω) ⊆ box n := fun n ω =>
    (dyadicHits_mono inter_subset_right).trans (dyadicHits_subset_box hKR)
  have hmarkov : ∀ n, P (Bad n)
      ≤ (∑ k ∈ box n, P (E n k)) / ENNReal.ofReal (((2 : ℝ) ^ n) ^ d) := by
    intro n
    set f : Ω → ℝ≥0∞ := fun ω => ∑ k ∈ box n, (toMeasurable P (E n k)).indicator 1 ω with hf
    have hfk : ∀ k, Measurable ((toMeasurable P (E n k)).indicator (1 : Ω → ℝ≥0∞)) := fun k =>
      measurable_one.indicator (measurableSet_toMeasurable _ _)
    have hfm : Measurable f := Finset.measurable_fun_sum _ fun k _ => hfk k
    have hpos : (0 : ℝ) < ((2 : ℝ) ^ n) ^ d := Real.rpow_pos_of_pos (two_pow_pos n) _
    have hsub : Bad n ⊆ {ω | ENNReal.ofReal (((2 : ℝ) ^ n) ^ d) ≤ f ω} := by
      intro ω hω
      have hcnt : (dyadicCount n (A ω) : ℝ≥0∞) ≤ f ω := by
        have hfω : f ω = (((box n).filter (fun k => ω ∈ toMeasurable P (E n k))).card : ℝ≥0∞) := by
          simp only [hf, Set.indicator_apply, Pi.one_apply]
          rw [Finset.sum_boole]
        rw [hfω]
        have hsub' : dyadicHits n (A ω)
            ⊆ ↑((box n).filter (fun k => ω ∈ toMeasurable P (E n k))) := by
          intro k hk
          rw [Finset.coe_filter]
          exact ⟨hhits_box n ω hk, subset_toMeasurable P (E n k) hk⟩
        have := Set.ncard_le_ncard hsub' (Finset.finite_toSet _)
        rw [Set.ncard_coe_finset] at this
        exact_mod_cast this
      refine le_trans ?_ hcnt
      rw [← ENNReal.ofReal_natCast]
      exact ENNReal.ofReal_le_ofReal (le_of_lt hω)
    calc P (Bad n) ≤ P {ω | ENNReal.ofReal (((2 : ℝ) ^ n) ^ d) ≤ f ω} := measure_mono hsub
      _ ≤ (∫⁻ ω, f ω ∂P) / ENNReal.ofReal (((2 : ℝ) ^ n) ^ d) :=
        meas_ge_le_lintegral_div hfm.aemeasurable (by simpa using hpos) ENNReal.ofReal_ne_top
      _ = (∑ k ∈ box n, P (E n k)) / ENNReal.ofReal (((2 : ℝ) ^ n) ^ d) := by
        congr 1
        rw [hf, lintegral_finsetSum _ fun k _ => hfk k]
        refine Finset.sum_congr rfl fun k _ => ?_
        rw [lintegral_indicator_one (measurableSet_toMeasurable _ _), measure_toMeasurable]
  -- the geometric bound
  have hd' : d = 2 - β / 2 := by rw [hd, interiorDimBound, hβ]
  set q : ℝ := ((2 : ℝ) ^ (β / 2))⁻¹ with hq
  have hq0 : 0 < q := by positivity
  have hq1 : q < 1 := inv_lt_one_of_one_lt₀ (Real.one_lt_rpow (by norm_num) (by positivity))
  set M : ℝ := (2 * R + 4) ^ 2 * a with hM
  have hM0 : 0 ≤ M := by positivity
  have hbig : ∀ n ≥ n₀, P (Bad n) ≤ ENNReal.ofReal (M * q ^ n) := by
    intro n hn
    have hv := two_pow_pos n
    have hpos : (0 : ℝ) < ((2 : ℝ) ^ n) ^ d := Real.rpow_pos_of_pos hv _
    refine (hmarkov n).trans ?_
    have hs : ∑ k ∈ box n, P (E n k) ≤ ENNReal.ofReal
        ((2 * R + 4) ^ 2 * ((2 : ℝ) ^ n) ^ 2 * (a * (((2 : ℝ) ^ n) ^ β)⁻¹)) := by
      refine (Finset.sum_le_card_nsmul _ _ _ fun k _ => hE_le n hn k).trans ?_
      rw [nsmul_eq_mul, ← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (Nat.cast_nonneg _)]
      refine ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right ?_ (by positivity))
      have := card_dyadicBox_le hR n
      have h4 : (4 : ℝ) ^ n = ((2 : ℝ) ^ n) ^ 2 := by
        rw [← pow_mul, mul_comm, pow_mul]; norm_num
      rw [h4] at this
      exact this
    calc (∑ k ∈ box n, P (E n k)) / ENNReal.ofReal (((2 : ℝ) ^ n) ^ d)
        ≤ ENNReal.ofReal ((2 * R + 4) ^ 2 * ((2 : ℝ) ^ n) ^ 2 * (a * (((2 : ℝ) ^ n) ^ β)⁻¹))
          / ENNReal.ofReal (((2 : ℝ) ^ n) ^ d) := by gcongr
      _ = ENNReal.ofReal ((2 * R + 4) ^ 2 * ((2 : ℝ) ^ n) ^ 2 * (a * (((2 : ℝ) ^ n) ^ β)⁻¹)
          / ((2 : ℝ) ^ n) ^ d) := (ENNReal.ofReal_div_of_pos hpos).symm
      _ = ENNReal.ofReal (M * q ^ n) := by
        congr 1
        rw [hM, hq, ← pow_div_rpow_eq n β, hd']
        ring
  set M' : ℝ := M + (q ^ n₀)⁻¹ with hM'
  have hM'0 : 0 ≤ M' := by positivity
  have hall : ∀ n, P (Bad n) ≤ ENNReal.ofReal (M' * q ^ n) := by
    intro n
    rcases le_or_gt n₀ n with hn | hn
    · refine (hbig n hn).trans (ENNReal.ofReal_le_ofReal ?_)
      have hqn : 0 ≤ (q ^ n₀)⁻¹ := by positivity
      have : M ≤ M' := by rw [hM']; linarith
      exact mul_le_mul_of_nonneg_right this (pow_nonneg hq0.le n)
    · refine prob_le_one.trans ?_
      rw [← ENNReal.ofReal_one]
      refine ENNReal.ofReal_le_ofReal ?_
      have h1 : q ^ n₀ ≤ q ^ n := pow_le_pow_of_le_one hq0.le hq1.le hn.le
      have h2 : 0 < q ^ n₀ := pow_pos hq0 _
      have h3 : 1 ≤ (q ^ n₀)⁻¹ * q ^ n := by
        rw [← div_eq_inv_mul, one_le_div h2]; exact h1
      have h4 : 0 ≤ M * q ^ n := mul_nonneg hM0 (pow_nonneg hq0.le n)
      rw [hM', add_mul]
      linarith
  have hsum : ∑' n, P (Bad n) ≠ ∞ := by
    refine ne_top_of_le_ne_top ?_ (ENNReal.tsum_le_tsum hall)
    simp_rw [ENNReal.ofReal_mul hM'0, ENNReal.ofReal_pow hq0.le]
    rw [ENNReal.tsum_mul_left, ENNReal.tsum_geometric]
    refine ENNReal.mul_ne_top ENNReal.ofReal_ne_top ?_
    rw [ENNReal.inv_ne_top]
    exact (tsub_pos_of_lt (by rwa [ENNReal.ofReal_lt_one])).ne'
  filter_upwards [ae_eventually_notMem hsum] with ω hω
  filter_upwards [hω] with n hn
  simpa only [hBad, mem_ofPred_eq, not_lt] using hn

/-- The compact exhaustion `K_m = {|Re x| ≤ m + 1, 1/(m + 1) ≤ Im x ≤ m + 1}` of `ℍ`. -/
def exhaustSet (m : ℕ) : Set ℂ :=
  {x | |x.re| ≤ (m : ℝ) + 1 ∧ 1 / ((m : ℝ) + 1) ≤ x.im ∧ x.im ≤ (m : ℝ) + 1}

theorem exhaustSet_im (m : ℕ) : ∀ x ∈ exhaustSet m, 1 / ((m : ℝ) + 1) ≤ x.im :=
  fun _ hx => hx.2.1

theorem exhaustSet_subset_closedBall (m : ℕ) :
    exhaustSet m ⊆ closedBall 0 (2 * ((m : ℝ) + 1)) := by
  rintro x ⟨h1, h2, h3⟩
  have hpos : (0 : ℝ) < 1 / ((m : ℝ) + 1) := by positivity
  have him : |x.im| = x.im := abs_of_pos (hpos.trans_le h2)
  rw [mem_closedBall, dist_zero_right]
  calc ‖x‖ ≤ |x.re| + |x.im| := Complex.norm_le_abs_re_add_abs_im x
    _ ≤ 2 * ((m : ℝ) + 1) := by rw [him]; linarith

theorem exists_nat_exhaust {a b c : ℝ} (hc : 0 < c) :
    ∃ m : ℕ, a ≤ (m : ℝ) + 1 ∧ b ≤ (m : ℝ) + 1 ∧ 1 / ((m : ℝ) + 1) ≤ c := by
  refine ⟨⌈max (max a b) (1 / c)⌉₊, ?_, ?_, ?_⟩
  · have := Nat.le_ceil (max (max a b) (1 / c))
    have := le_max_left (max a b) (1 / c)
    have := le_max_left a b
    linarith
  · have := Nat.le_ceil (max (max a b) (1 / c))
    have := le_max_left (max a b) (1 / c)
    have := le_max_right a b
    linarith
  · have h1 := Nat.le_ceil (max (max a b) (1 / c))
    have h2 := le_max_right (max a b) (1 / c)
    have h3 : 1 / c ≤ (⌈max (max a b) (1 / c)⌉₊ : ℝ) + 1 := by linarith
    rw [div_le_iff₀ (by positivity)]
    rw [div_le_iff₀ hc] at h3
    linarith

/-- Every compact subset of `ℍ` lies in some `K_m`. -/
theorem exists_subset_exhaustSet {K : Set ℂ} (hK : IsCompact K) (hKH : K ⊆ H) :
    ∃ m, K ⊆ exhaustSet m := by
  rcases K.eq_empty_or_nonempty with h | hne
  · exact ⟨0, h ▸ empty_subset _⟩
  obtain ⟨R, hR⟩ := hK.isBounded.subset_closedBall 0
  obtain ⟨x₀, hx₀K, hmin⟩ := hK.exists_isMinOn hne Complex.continuous_im.continuousOn
  have hx₀ : 0 < x₀.im := hKH hx₀K
  obtain ⟨m, hm1, -, hm3⟩ := exists_nat_exhaust (a := R) (b := R) hx₀
  refine ⟨m, fun x hx => ?_⟩
  have hxR : ‖x‖ ≤ R := by simpa using hR hx
  refine ⟨(Complex.abs_re_le_norm x).trans (hxR.trans hm1), hm3.trans (hmin hx), ?_⟩
  exact (Complex.im_le_norm x).trans (hxR.trans hm1)

theorem iUnion_exhaustSet : ⋃ m, exhaustSet m = H := by
  ext x
  simp only [mem_iUnion]
  constructor
  · rintro ⟨m, hm⟩
    show 0 < x.im
    exact lt_of_lt_of_le (by positivity) (exhaustSet_im m x hm)
  · intro hx
    obtain ⟨m, h1, h2, h3⟩ := exists_nat_exhaust (a := |x.re|) (b := x.im) (show 0 < x.im from hx)
    exact ⟨m, h1, h3, h2⟩

/-- **Aux. lemma 14** (specification p. 86, "A direct strict dimension bound below parameter
eight"). For `0 < κ < 8` and every Brownian motion `B`, almost surely the ordinary chordal SLE_κ
trace `γ = sleTrace κ B` has interior Hausdorff dimension at most the deterministic
`d_κ = 2 − β_κ / 2 < 2` (`interiorDimBound`, `interiorDimBound_lt_two`), and on every compact
`K ⊆ ℍ`, for every sufficiently small dyadic `δ = 2^{-n}`, only finitely many dyadic squares of side
`δ` meet `γ ∩ K`, and their number is at most `δ^{-d_κ}`. -/
theorem ae_dimH_sleTrace_inter_H_le {κ : ℝ} (hκ : 0 < κ) (hκ8 : κ < 8) {Ω : Type}
    [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P] (B : ℝ≥0 → Ω → ℝ)
    (hB : IsBrownianReal B P) :
    ∀ᵐ ω ∂P, dimH (sleTrace κ B ω '' Ici 0 ∩ H) ≤ ENNReal.ofReal (interiorDimBound κ) ∧
      ∀ K : Set ℂ, IsCompact K → K ⊆ H → ∀ᶠ n in atTop,
        (dyadicHits n (sleTrace κ B ω '' Ici 0 ∩ K)).Finite ∧
        (dyadicCount n (sleTrace κ B ω '' Ici 0 ∩ K) : ℝ) ≤ ((2 : ℝ) ^ n) ^ interiorDimBound κ := by
  have hm : ∀ m : ℕ, ∀ᵐ ω ∂P, ∀ᶠ n in atTop,
      (dyadicCount n (sleTrace κ B ω '' Ici 0 ∩ exhaustSet m) : ℝ)
        ≤ ((2 : ℝ) ^ n) ^ interiorDimBound κ := fun m =>
    ae_eventually_dyadicCount_le hκ hκ8 P B hB (by positivity) (exhaustSet_subset_closedBall m)
      (by positivity) (exhaustSet_im m)
  filter_upwards [ae_all_iff.2 hm] with ω hω
  set γ := sleTrace κ B ω '' Ici 0 with hγ
  have hbd : ∀ m, Bornology.IsBounded (γ ∩ exhaustSet m) := fun m =>
    isBounded_closedBall.subset (inter_subset_right.trans (exhaustSet_subset_closedBall m))
  refine ⟨?_, fun K hKc hKH => ?_⟩
  · have hU : γ ∩ H = ⋃ m, γ ∩ exhaustSet m := by rw [← inter_iUnion, iUnion_exhaustSet]
    rw [hU, dimH_iUnion]
    refine iSup_le fun m => dimH_le_of_eventually_dyadicCount_le (interiorDimBound_nonneg hκ) ?_
    filter_upwards [hω m] with n hn
    exact ⟨dyadicHits_finite (hbd m), hn⟩
  · obtain ⟨m, hmK⟩ := exists_subset_exhaustSet hKc hKH
    filter_upwards [hω m] with n hn
    have hsub : dyadicHits n (γ ∩ K) ⊆ dyadicHits n (γ ∩ exhaustSet m) :=
      dyadicHits_mono (inter_subset_inter_right _ hmK)
    have hfin := dyadicHits_finite (n := n) (hbd m)
    refine ⟨hfin.subset hsub, le_trans ?_ hn⟩
    exact_mod_cast Set.ncard_le_ncard hsub hfin

end InteractingSLE.Dimension
