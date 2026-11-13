import InteractingSLE.SLE8.Counting.Sums
import InteractingSLE.SLE8.Counting.DriverBound
import InteractingSLE.SLE8.TwoPoint
import InteractingSLE.SLE8.Occupation

/-!
# Proposition 4.1 of the SLE₈ note (number of large scales)

SLE₈ note `source/sle8-continuity.pdf`, §4, pp. 7–10 (transcription `source/sle8/sle8-continuity.md`,
anchors `prop-4.1`, `prop-4.1-proof`).

**Proposition 4.1.** Fix `δ ∈ (0, 1/10)`. For `n ≥ 1` put `N = 2ⁿ`, `r = N^δ`, `a = exp(-r/n²)` (4.1) and
`𝓘_n(t) = {k : N < k ≤ 2N, A_k(t_k) ≥ a}`, `t_k = 4^{-k} ⌊4^k t⌋` (4.2), with `A_k(t) = y_k |F_t'(iy_k)|`.
Almost surely there is a finite random `n₀` such that `sup_{t ∈ [0,1]} |𝓘_n(t)| ≤ r⁷` for `n ≥ n₀` (4.3).

The proof uses Lemmas 3.1, 3.2 and 3.3 of the note, proved by other packets; they are the hypotheses
`Lemma31Statement`, `Lemma32Statement` and `Lemma33Statement` of `prop41_of_lemmas` (Lemmas 2.2 and (2.7)
are imported from `ReverseFlow.lean`). Lemmas 3.2 and 3.3 have landed (`TwoPoint.lean`, `Occupation.lean`)
and are discharged (`lemma32Statement_holds`, `lemma33Statement_holds`), so `prop41_of_lemma31` and
`scaleCount_of_lemma31` (the form of the hypothesis `hP41` of `ae_exists_continuous_trace_of_scale_count`)
take only Lemma 3.1. Everything else is proved here and in `Counting/`:

* Step 1 (selection of a terminal time) and Step 3 (many scales force many visits): `selection`
  (`Counting/Selection.lean`);
* Step 2 (small image heights, (4.13)): `measure_smallImageSet_le`;
* Step 4 (probability of many visits, (4.23)–(4.25)): `measure_trialEventAt_le`
  (`Counting/ChangeOfMeasure.lean`, with the strong Markov iteration in `Counting/TrialBM.lean`) and
  `measure_manyTrialSet_le`;
* Borel–Cantelli and the countable union over `M`: `prop41_of_lemmas`.
-/

noncomputable section

open Set Filter MeasureTheory ProbabilityTheory Complex
open scoped Topology ENNReal NNReal

namespace InteractingSLE.SLE8

open QuantumZipper

/-! ## Measure-theoretic helpers -/

theorem measure_biUnion_le_card_mul {Ω ι : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    (s : Finset ι) (S : ι → Set Ω) {x : ℝ} (h : ∀ i ∈ s, μ (S i) ≤ ENNReal.ofReal x) :
    μ (⋃ i ∈ s, S i) ≤ ENNReal.ofReal (s.card * x) := by
  calc μ (⋃ i ∈ s, S i) ≤ ∑ i ∈ s, μ (S i) := measure_biUnion_finset_le s S
    _ ≤ ∑ _i ∈ s, ENNReal.ofReal x := Finset.sum_le_sum h
    _ = ENNReal.ofReal (s.card * x) := by
        rw [Finset.sum_const, nsmul_eq_mul, ENNReal.ofReal_mul (by positivity),
          ENNReal.ofReal_natCast]

/-- **Borel–Cantelli** with an eventual summable real bound. -/
theorem ae_eventually_notMem_of_le {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {s : ℕ → Set Ω} {b : ℕ → ℝ} (hb0 : ∀ n, 0 ≤ b n) (hb : Summable b)
    (h : ∀ᶠ n in atTop, μ (s n) ≤ ENNReal.ofReal (b n)) :
    ∀ᵐ ω ∂μ, ∀ᶠ n in atTop, ω ∉ s n := by
  obtain ⟨n₀, hn₀⟩ := eventually_atTop.1 h
  have hs : ∑' n, μ (s (n + n₀)) ≠ ∞ := by
    refine ne_top_of_le_ne_top (ENNReal.ofReal_ne_top (r := ∑' n, b (n + n₀))) ?_
    rw [ENNReal.ofReal_tsum_of_nonneg (fun n => hb0 _) ((summable_nat_add_iff n₀).2 hb)]
    exact ENNReal.tsum_le_tsum fun n => hn₀ _ (by omega)
  filter_upwards [ae_eventually_notMem hs] with ω hω
  rw [eventually_atTop] at hω ⊢
  obtain ⟨m, hm⟩ := hω
  refine ⟨m + n₀, fun n hn => ?_⟩
  have := hm (n - n₀) (by omega)
  rwa [Nat.sub_add_cancel (by omega)] at this

theorem dyadicHeight_sq_mul_le (k : ℕ) : ((4 ^ k + 1 : ℕ) : ℝ) * dyadicHeight k ^ 2 ≤ 2 := by
  rw [dyadicHeight_sq]
  have h4 : (0 : ℝ) < 4 ^ k := by positivity
  have h1 : (1 : ℝ) ≤ 4 ^ k := one_le_pow₀ (by norm_num)
  push_cast
  rw [← div_eq_mul_inv, div_le_iff₀ h4]
  linarith

theorem card_Ioc_two_pow (n : ℕ) : (((Finset.Ioc (2 ^ n) (2 * 2 ^ n)).card : ℕ) : ℝ) = bigN n := by
  rw [Nat.card_Ioc, show 2 * 2 ^ n - 2 ^ n = 2 ^ n by omega, cast_two_pow]

/-! ## Step 2: the small-image events ((4.12)–(4.13)) -/

/-- The half-width `⌊4M√N 2^{ℓ-k} + 1⌋` of the range of horizontal indices `m` in (4.9). -/
def boxR (M : ℝ) (n k ℓ : ℕ) : ℤ := ⌊4 * M * Real.sqrt (bigN n) * 2 ^ (ℓ - k) + 1⌋

/-- The union, over coarse scales `k`, grid times `j/4^k`, dyadic heights `ℓ` with `(ℓ - k) log 2 ≥ r`
and horizontal indices `|m| ≤ boxR`, of the two-point events of Lemma 3.2 (with `c₀ = 1/(2K)`). -/
def smallImageSet {Ω : Type*} (B : ℝ≥0 → Ω → ℝ) (M : ℕ) (K δ : ℝ) (n : ℕ) : Set Ω :=
  ⋃ k ∈ (Finset.Ioc (2 ^ n) (2 * 2 ^ n) : Finset ℕ), ⋃ j ∈ Finset.range (4 ^ k + 1),
    ⋃ ℓ ∈ (Finset.Ioc k (2 * 2 ^ n + 1)).filter (fun ℓ : ℕ => scaleR δ n ≤ ((ℓ : ℝ) - k) * Real.log 2),
      ⋃ m ∈ Finset.Icc (-boxR M n k ℓ) (boxR M n k ℓ),
        {ω | DriverBound M (drive 8 B ω) ∧
          levelA δ n ≤ dyadicHeight k *
            ‖deriv (fwdMapInv (drive 8 B ω) ((j : ℝ) / 4 ^ k)) ((dyadicHeight k : ℂ) * I)‖ ∧
          1 / (2 * K) * levelA δ n ≤ dyadicHeight ℓ *
            ‖deriv (fwdMapInv (drive 8 B ω) ((j : ℝ) / 4 ^ k))
              (((m : ℂ) + I) * (dyadicHeight ℓ : ℂ))‖}

theorem div_four_pow_mem {k j : ℕ} (hj : j ∈ Finset.range (4 ^ k + 1)) :
    (j : ℝ) / 4 ^ k ∈ Icc (0 : ℝ) 1 := by
  have hj' : (j : ℝ) ≤ 4 ^ k := by
    have := Finset.mem_range.1 hj
    exact_mod_cast (show j ≤ 4 ^ k by omega)
  exact ⟨by positivity, (div_le_one (by positivity)).2 hj'⟩

/-- **(4.13).** If Lemma 3.2 holds at `M` and `c₀ = 1/(2K)` with constant `C`, then for `n ≥ 8` with
`(4M√N + 1) y_N ≤ 1`: `ℙ(small-image events) ≤ 36 C⁺ (4M+1)³ N⁵ e^{-r/18}`. -/
theorem measure_smallImageSet_le {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {B : ℝ≥0 → Ω → ℝ} {M : ℕ} {K δ C : ℝ}
    (hC : ∀ t ∈ Icc (0 : ℝ) 1, ∀ a ∈ Ioo (0 : ℝ) 1, ∀ y ∈ Ioc (0 : ℝ) 1, ∀ v ∈ Ioc (0 : ℝ) (y / 2),
      ∀ m : ℤ, |(m : ℝ)| * v ≤ 1 →
        P {ω | DriverBound M (drive 8 B ω) ∧
            a ≤ y * ‖deriv (fwdMapInv (drive 8 B ω) t) ((y : ℂ) * I)‖ ∧
            1 / (2 * K) * a ≤ v * ‖deriv (fwdMapInv (drive 8 B ω) t) (((m : ℂ) + I) * (v : ℂ))‖} ≤
          ENNReal.ofReal (C * a ^ (-(26 / 9 : ℝ)) * y ^ 2 * (v / y) ^ (16 / 9 : ℝ) *
            (1 + (m : ℝ) ^ 2) ^ (1 / 3 : ℝ)))
    {n : ℕ} (hn8 : 8 ≤ n) (hδr : 0 < scaleR δ n)
    (hbox : (4 * M * Real.sqrt (bigN n) + 1) * dyadicHeight (2 ^ n) ≤ 1) :
    P (smallImageSet B M K δ n) ≤ ENNReal.ofReal (36 * max C 0 * (4 * M + 1) ^ 3 * bigN n ^ 5 *
      Real.exp (-(scaleR δ n / 18))) := by
  set N := bigN n with hN
  set r := scaleR δ n with hr
  set a := levelA δ n with ha
  set C' := max C 0 with hC'
  have hC'0 : 0 ≤ C' := le_max_right _ _
  have hN1 : 1 ≤ N := one_le_bigN n
  have hM0 : (0 : ℝ) ≤ M := Nat.cast_nonneg M
  set ρ := 4 * M * Real.sqrt N + 1 with hρ
  have hρ1 : 1 ≤ ρ := by rw [hρ]; have := Real.sqrt_nonneg N; nlinarith
  have hamem : a ∈ Ioo (0 : ℝ) 1 := levelA_mem δ n hδr (by omega)
  set Z := C' * a ^ (-(26 / 9 : ℝ)) * (6 * ρ ^ 3 * Real.exp (-(r / 9))) with hZ
  have hZ0 : 0 ≤ Z := by rw [hZ]; have := hamem.1; positivity
  -- level `m`
  have hlevm : ∀ k ∈ (Finset.Ioc (2 ^ n) (2 * 2 ^ n) : Finset ℕ), ∀ j ∈ Finset.range (4 ^ k + 1),
      ∀ ℓ ∈ (Finset.Ioc k (2 * 2 ^ n + 1)).filter
        (fun ℓ : ℕ => r ≤ ((ℓ : ℝ) - k) * Real.log 2),
      P (⋃ m ∈ Finset.Icc (-boxR M n k ℓ) (boxR M n k ℓ),
        {ω | DriverBound M (drive 8 B ω) ∧
          a ≤ dyadicHeight k *
            ‖deriv (fwdMapInv (drive 8 B ω) ((j : ℝ) / 4 ^ k)) ((dyadicHeight k : ℂ) * I)‖ ∧
          1 / (2 * K) * a ≤ dyadicHeight ℓ *
            ‖deriv (fwdMapInv (drive 8 B ω) ((j : ℝ) / 4 ^ k))
              (((m : ℂ) + I) * (dyadicHeight ℓ : ℂ))‖}) ≤
        ENNReal.ofReal (dyadicHeight k ^ 2 * Z) := by
    intro k hk j hj ℓ hℓ
    obtain ⟨hℓ1, hℓr⟩ := Finset.mem_filter.1 hℓ
    obtain ⟨hkℓ, -⟩ := Finset.mem_Ioc.1 hℓ1
    obtain ⟨hk1, -⟩ := Finset.mem_Ioc.1 hk
    set d := ℓ - k with hd
    have hyk := dyadicHeight_pos k
    have hratio : dyadicHeight ℓ / dyadicHeight k = (2 : ℝ) ^ (-(d : ℝ)) := by
      rw [← inv_div, dyadicHeight_div hkℓ.le, Real.rpow_neg (by norm_num), Real.rpow_natCast]
    have hR0 : 0 ≤ boxR M n k ℓ := Int.floor_nonneg.2 (by positivity)
    have hRle : (boxR M n k ℓ : ℝ) ≤ ρ * 2 ^ d := by
      have h1 := Int.floor_le (4 * M * Real.sqrt N * 2 ^ (ℓ - k) + 1)
      have h2 : (1 : ℝ) ≤ 2 ^ d := one_le_pow₀ (by norm_num)
      rw [boxR, ← hN]
      rw [hρ]; nlinarith
    -- each event is bounded by Lemma 3.2
    have hterm : ∀ m ∈ Finset.Icc (-boxR M n k ℓ) (boxR M n k ℓ),
        P {ω | DriverBound M (drive 8 B ω) ∧
          a ≤ dyadicHeight k *
            ‖deriv (fwdMapInv (drive 8 B ω) ((j : ℝ) / 4 ^ k)) ((dyadicHeight k : ℂ) * I)‖ ∧
          1 / (2 * K) * a ≤ dyadicHeight ℓ *
            ‖deriv (fwdMapInv (drive 8 B ω) ((j : ℝ) / 4 ^ k))
              (((m : ℂ) + I) * (dyadicHeight ℓ : ℂ))‖} ≤
        ENNReal.ofReal (C' * a ^ (-(26 / 9 : ℝ)) * dyadicHeight k ^ 2 *
          (((2 : ℝ) ^ (-(d : ℝ))) ^ (16 / 9 : ℝ) * (1 + (m : ℝ) ^ 2) ^ (1 / 3 : ℝ))) := by
      intro m hm
      have hmR : |(m : ℝ)| ≤ boxR M n k ℓ := by
        obtain ⟨h1, h2⟩ := Finset.mem_Icc.1 hm
        rw [abs_le]; constructor
        · have : -(boxR M n k ℓ : ℝ) ≤ m := by exact_mod_cast h1
          linarith
        · exact_mod_cast h2
      have hv : dyadicHeight ℓ ∈ Ioc (0 : ℝ) (dyadicHeight k / 2) := by
        refine ⟨dyadicHeight_pos ℓ, ?_⟩
        have := dyadicHeight_anti (show k + 1 ≤ ℓ from hkℓ)
        have e : dyadicHeight (k + 1) = dyadicHeight k / 2 := by
          unfold dyadicHeight; rw [pow_succ]; field_simp
        linarith
      have hmv : |(m : ℝ)| * dyadicHeight ℓ ≤ 1 := by
        have hyl : dyadicHeight ℓ = dyadicHeight k * (2 : ℝ) ^ (-(d : ℝ)) := by
          rw [← hratio]; field_simp
        have h2d : (2 : ℝ) ^ (-(d : ℝ)) * 2 ^ d = 1 := by
          rw [Real.rpow_neg (by norm_num), Real.rpow_natCast, inv_mul_cancel₀ (by positivity)]
        have hyN : dyadicHeight k ≤ dyadicHeight (2 ^ n) := dyadicHeight_anti hk1.le
        calc |(m : ℝ)| * dyadicHeight ℓ ≤ (ρ * 2 ^ d) * (dyadicHeight k * (2 : ℝ) ^ (-(d : ℝ))) := by
              rw [hyl]; gcongr; exact hmR.trans hRle
          _ = ρ * dyadicHeight k * ((2 : ℝ) ^ (-(d : ℝ)) * 2 ^ d) := by ring
          _ = ρ * dyadicHeight k := by rw [h2d, mul_one]
          _ ≤ ρ * dyadicHeight (2 ^ n) := by gcongr
          _ ≤ 1 := hbox
      refine (hC _ (div_four_pow_mem hj) a hamem (dyadicHeight k)
        ⟨hyk, dyadicHeight_le_one k⟩ (dyadicHeight ℓ) hv m hmv).trans
        (ENNReal.ofReal_le_ofReal ?_)
      rw [hratio]
      have h1 : 0 ≤ (2 : ℝ) ^ (-(d : ℝ)) := by positivity
      have h2 : 0 ≤ a ^ (-(26 / 9 : ℝ)) := by have := hamem.1; positivity
      have h3 : 0 ≤ ((2 : ℝ) ^ (-(d : ℝ))) ^ (16 / 9 : ℝ) * (1 + (m : ℝ) ^ 2) ^ (1 / 3 : ℝ) := by
        positivity
      have h4 : C ≤ C' := le_max_left _ _
      calc C * a ^ (-(26 / 9 : ℝ)) * dyadicHeight k ^ 2 * ((2 : ℝ) ^ (-(d : ℝ))) ^ (16 / 9 : ℝ) *
            (1 + (m : ℝ) ^ 2) ^ (1 / 3 : ℝ)
          = C * (a ^ (-(26 / 9 : ℝ)) * dyadicHeight k ^ 2 * (((2 : ℝ) ^ (-(d : ℝ))) ^ (16 / 9 : ℝ) *
            (1 + (m : ℝ) ^ 2) ^ (1 / 3 : ℝ))) := by ring
        _ ≤ C' * (a ^ (-(26 / 9 : ℝ)) * dyadicHeight k ^ 2 * (((2 : ℝ) ^ (-(d : ℝ))) ^ (16 / 9 : ℝ) *
            (1 + (m : ℝ) ^ 2) ^ (1 / 3 : ℝ))) := by gcongr
        _ = _ := by ring
    calc _ ≤ ∑ m ∈ Finset.Icc (-boxR M n k ℓ) (boxR M n k ℓ), P _ := measure_biUnion_finset_le _ _
      _ ≤ ∑ m ∈ Finset.Icc (-boxR M n k ℓ) (boxR M n k ℓ),
            ENNReal.ofReal (C' * a ^ (-(26 / 9 : ℝ)) * dyadicHeight k ^ 2 *
              (((2 : ℝ) ^ (-(d : ℝ))) ^ (16 / 9 : ℝ) * (1 + (m : ℝ) ^ 2) ^ (1 / 3 : ℝ))) :=
          Finset.sum_le_sum hterm
      _ = ENNReal.ofReal (C' * a ^ (-(26 / 9 : ℝ)) * dyadicHeight k ^ 2 *
            ∑ m ∈ Finset.Icc (-boxR M n k ℓ) (boxR M n k ℓ),
              (((2 : ℝ) ^ (-(d : ℝ))) ^ (16 / 9 : ℝ) * (1 + (m : ℝ) ^ 2) ^ (1 / 3 : ℝ))) := by
          rw [Finset.mul_sum, ENNReal.ofReal_sum_of_nonneg]
          intro m _; have := hamem.1; positivity
      _ ≤ ENNReal.ofReal (dyadicHeight k ^ 2 * Z) := by
          refine ENNReal.ofReal_le_ofReal ?_
          have hbox' := sum_box_le hρ1 hR0 hRle
          have hexp : (2 : ℝ) ^ (-(d : ℝ) / 9) ≤ Real.exp (-(r / 9)) := by
            rw [Real.rpow_def_of_pos (by norm_num), Real.exp_le_exp]
            have : r ≤ ((ℓ : ℝ) - k) * Real.log 2 := hℓr
            have hdℓ : ((d : ℕ) : ℝ) = (ℓ : ℝ) - k := by rw [hd, Nat.cast_sub hkℓ.le]
            rw [hdℓ]; nlinarith
          have hA : 0 ≤ C' * a ^ (-(26 / 9 : ℝ)) * dyadicHeight k ^ 2 := by
            have := hamem.1; positivity
          calc C' * a ^ (-(26 / 9 : ℝ)) * dyadicHeight k ^ 2 * ∑ m ∈ Finset.Icc (-boxR M n k ℓ)
                (boxR M n k ℓ), (((2 : ℝ) ^ (-(d : ℝ))) ^ (16 / 9 : ℝ) * (1 + (m : ℝ) ^ 2) ^
                (1 / 3 : ℝ))
              ≤ C' * a ^ (-(26 / 9 : ℝ)) * dyadicHeight k ^ 2 * (6 * ρ ^ 3 *
                  (2 : ℝ) ^ (-(d : ℝ) / 9)) := mul_le_mul_of_nonneg_left hbox' hA
            _ ≤ C' * a ^ (-(26 / 9 : ℝ)) * dyadicHeight k ^ 2 * (6 * ρ ^ 3 *
                  Real.exp (-(r / 9))) := by gcongr
            _ = dyadicHeight k ^ 2 * Z := by rw [hZ]; ring
  -- level `ℓ`
  have hlevl : ∀ k ∈ (Finset.Ioc (2 ^ n) (2 * 2 ^ n) : Finset ℕ), ∀ j ∈ Finset.range (4 ^ k + 1),
      P (⋃ ℓ ∈ (Finset.Ioc k (2 * 2 ^ n + 1)).filter
          (fun ℓ : ℕ => r ≤ ((ℓ : ℝ) - k) * Real.log 2),
        ⋃ m ∈ Finset.Icc (-boxR M n k ℓ) (boxR M n k ℓ),
        {ω | DriverBound M (drive 8 B ω) ∧
          a ≤ dyadicHeight k *
            ‖deriv (fwdMapInv (drive 8 B ω) ((j : ℝ) / 4 ^ k)) ((dyadicHeight k : ℂ) * I)‖ ∧
          1 / (2 * K) * a ≤ dyadicHeight ℓ *
            ‖deriv (fwdMapInv (drive 8 B ω) ((j : ℝ) / 4 ^ k))
              (((m : ℂ) + I) * (dyadicHeight ℓ : ℂ))‖}) ≤
        ENNReal.ofReal (3 * N * (dyadicHeight k ^ 2 * Z)) := by
    intro k hk j hj
    refine (measure_biUnion_le_card_mul _ _ (hlevm k hk j hj)).trans
      (ENNReal.ofReal_le_ofReal ?_)
    have hcard : (((Finset.Ioc k (2 * 2 ^ n + 1)).filter
        (fun ℓ : ℕ => r ≤ ((ℓ : ℝ) - k) * Real.log 2)).card : ℝ) ≤ 3 * N := by
      have h1 := Finset.card_filter_le (Finset.Ioc k (2 * 2 ^ n + 1))
        (fun ℓ : ℕ => r ≤ ((ℓ : ℝ) - k) * Real.log 2)
      rw [Nat.card_Ioc] at h1
      have h2 : 2 * 2 ^ n + 1 - k ≤ 3 * 2 ^ n := by
        have : 1 ≤ 2 ^ n := Nat.one_le_two_pow; omega
      have h3 : ((3 * 2 ^ n : ℕ) : ℝ) = 3 * N := by rw [hN, ← cast_two_pow]; push_cast; ring
      calc _ ≤ ((2 * 2 ^ n + 1 - k : ℕ) : ℝ) := by exact_mod_cast h1
        _ ≤ ((3 * 2 ^ n : ℕ) : ℝ) := by exact_mod_cast h2
        _ = 3 * N := h3
    exact mul_le_mul_of_nonneg_right hcard (by positivity)
  -- level `j`
  have hlevj : ∀ k ∈ (Finset.Ioc (2 ^ n) (2 * 2 ^ n) : Finset ℕ),
      P (⋃ j ∈ Finset.range (4 ^ k + 1),
        ⋃ ℓ ∈ (Finset.Ioc k (2 * 2 ^ n + 1)).filter
          (fun ℓ : ℕ => r ≤ ((ℓ : ℝ) - k) * Real.log 2),
        ⋃ m ∈ Finset.Icc (-boxR M n k ℓ) (boxR M n k ℓ),
        {ω | DriverBound M (drive 8 B ω) ∧
          a ≤ dyadicHeight k *
            ‖deriv (fwdMapInv (drive 8 B ω) ((j : ℝ) / 4 ^ k)) ((dyadicHeight k : ℂ) * I)‖ ∧
          1 / (2 * K) * a ≤ dyadicHeight ℓ *
            ‖deriv (fwdMapInv (drive 8 B ω) ((j : ℝ) / 4 ^ k))
              (((m : ℂ) + I) * (dyadicHeight ℓ : ℂ))‖}) ≤
        ENNReal.ofReal (6 * N * Z) := by
    intro k hk
    refine (measure_biUnion_le_card_mul _ _ (hlevl k hk)).trans
      (ENNReal.ofReal_le_ofReal ?_)
    rw [Finset.card_range]
    have h := dyadicHeight_sq_mul_le k
    calc ((4 ^ k + 1 : ℕ) : ℝ) * (3 * N * (dyadicHeight k ^ 2 * Z))
        = 3 * N * Z * (((4 ^ k + 1 : ℕ) : ℝ) * dyadicHeight k ^ 2) := by ring
      _ ≤ 3 * N * Z * 2 := by gcongr
      _ = 6 * N * Z := by ring
  -- level `k`
  refine (measure_biUnion_le_card_mul _ _ hlevj).trans
    (ENNReal.ofReal_le_ofReal ?_)
  rw [card_Ioc_two_pow, ← hN]
  -- the arithmetic
  have hsq : Real.sqrt N ≤ N := sqrt_bigN_le n
  have hρN : ρ ≤ (4 * M + 1) * N := by rw [hρ]; nlinarith
  have hρ3 : ρ ^ 3 ≤ ((4 * M + 1) * N) ^ 3 := pow_le_pow_left₀ (by linarith) hρN 3
  have haexp : a ^ (-(26 / 9 : ℝ)) * Real.exp (-(r / 9)) ≤ Real.exp (-(r / 18)) := by
    rw [ha, levelA, ← Real.exp_mul, ← Real.exp_add, Real.exp_le_exp]
    have hn' : (8 : ℝ) ≤ n := by exact_mod_cast hn8
    have hr0 : 0 ≤ r := hδr.le
    have h64 : (64 : ℝ) ≤ (n : ℝ) ^ 2 := by nlinarith
    have : r / (n : ℝ) ^ 2 * (26 / 9) ≤ r / 18 := by
      rw [div_mul_eq_mul_div, div_le_div_iff₀ (by positivity) (by norm_num)]
      nlinarith
    linarith
  have ha0 : 0 ≤ a ^ (-(26 / 9 : ℝ)) := by have := hamem.1; positivity
  calc N * (6 * N * Z)
      = 36 * C' * ρ ^ 3 * N ^ 2 * (a ^ (-(26 / 9 : ℝ)) * Real.exp (-(r / 9))) := by
        rw [hZ]; ring
    _ ≤ 36 * C' * ((4 * M + 1) * N) ^ 3 * N ^ 2 * Real.exp (-(r / 18)) := by
        gcongr
    _ = 36 * C' * (4 * M + 1) ^ 3 * N ^ 5 * Real.exp (-(r / 18)) := by ring

/-! ## Step 4: many trial events ((4.24)–(4.25)) -/

/-- The union, over deterministic pairs `(k_*, T = j/4^{k_*})`, of the trial events `E_{k_*,T}` (4.22)
for the reverse flow driven by the Brownian extension `√8 · revBM B T` of the reversed driver. -/
def manyTrialSet {Ω : Type*} (B : ℝ≥0 → Ω → ℝ) (δ : ℝ) (n : ℕ) : Set Ω :=
  ⋃ k ∈ (Finset.Ioc (2 ^ n) (2 * 2 ^ n) : Finset ℕ), ⋃ j ∈ Finset.range (4 ^ k + 1),
    {ω | trialEventAt (drive 8 (UnzipInvariance.revBM B ((j : ℝ) / 4 ^ k).toNNReal) ω)
      (dyadicHeight k) ((j : ℝ) / 4 ^ k) (levelA δ n) (scaleR δ n) ⌈scaleR δ n⌉₊}

section RevBM

variable {Ω : Type*} {B : ℝ≥0 → Ω → ℝ}

theorem continuous_revBM (hBc : ∀ ω, Continuous fun t => B t ω) (τ : ℝ≥0) (ω : Ω) :
    Continuous fun t => UnzipInvariance.revBM B τ t ω := by
  simp only [UnzipInvariance.revBM_apply]
  exact (((hBc ω).comp (continuous_const.sub continuous_id)).add
    ((hBc ω).comp (continuous_id.max continuous_const))).sub continuous_const

theorem measurable_revBM [MeasurableSpace Ω] (hBm : ∀ t, Measurable (B t)) (τ t : ℝ≥0) :
    Measurable (UnzipInvariance.revBM B τ t) := by
  have : UnzipInvariance.revBM B τ t = fun ω => B (τ - t) ω + B (max t τ) ω - 2 * B τ ω := by
    funext ω; exact UnzipInvariance.revBM_apply B τ t ω
  rw [this]
  exact ((hBm _).add (hBm _)).sub (measurable_const.mul (hBm _))

theorem revBM_zero (τ : ℝ≥0) (ω : Ω) : UnzipInvariance.revBM B τ 0 ω = 0 := by
  simp only [UnzipInvariance.revBM_apply, tsub_zero, zero_le, max_eq_right]; ring

end RevBM

/-- **(4.24)–(4.25).** If Lemma 3.1 holds and Lemma 3.3 holds with constant `C`, then for `n ≥ 2` with
`r ≥ 2` and `r ≥ e · max C 1`: `ℙ(many-trial events) ≤ 2 N e^{-r/2}`. -/
theorem measure_manyTrialSet_le {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {B : ℝ≥0 → Ω → ℝ} (hB : IsBrownianReal B P) (hBc : ∀ ω, Continuous fun t => B t ω)
    (hBm : ∀ t, Measurable (B t)) {Cocc : ℝ}
    (h31 : ∀ β : ℝ≥0 → Ω → ℝ, IsBrownianReal β P → (∀ ω, Continuous fun t => β t ω) →
      (∀ t, Measurable (β t)) → (∀ ω, β 0 ω = 0) →
      ∀ T ∈ Icc (0 : ℝ) 1, ∀ y ∈ Ioc (0 : ℝ) 1,
        (∃ Q : Measure Ω, IsProbabilityMeasure Q ∧
          (∃ β' : ℝ≥0 → Ω → ℝ, IsBrownianReal β' Q ∧
            ∀ᵐ ω ∂Q, ∀ v : ℝ≥0, (v : ℝ) ≤ heightTau (drive 8 β ω) y T - Real.log y →
              heightJ (drive 8 β ω) y (Real.log y + v) = 2 * β' v ω) ∧
          ∀ a ∈ Ioo (0 : ℝ) 1, ∀ E : Set Ω,
            MeasurableSet[heightStoppedSigma (fun ω => drive 8 β ω) y T] E →
            E ⊆ {ω | a ≤ y * rfPhi (drive 8 β ω) y T} →
            P E ≤ ENNReal.ofReal (y ^ 2 / a ^ 2) * Q E) ∧
        ∀ a ∈ Ioo (0 : ℝ) 1, ∀ ω, a ≤ y * rfPhi (drive 8 β ω) y T →
          Real.log a ≤ heightTau (drive 8 β ω) y T ∧
          volume {u | u ∈ Icc (Real.log y) (heightTau (drive 8 β ω) y T) ∧
              |heightJ (drive 8 β ω) y u| ≤ 1} ≤ ENNReal.ofReal (Cocc * (1 + Real.log (1 / a))))
    {C : ℝ}
    (hC : ∀ (Q : Measure Ω) (β : ℝ≥0 → Ω → ℝ), IsBrownianReal β Q →
      (∀ ω, Continuous fun t => β t ω) → (∀ t, Measurable (β t)) →
      ∀ r : ℝ, 2 ≤ r → ∀ x : ℝ, |x| ≤ 2 * r →
        Q {ω | volume {u : ℝ | u ∈ Icc 0 (2 * r ^ 5) ∧ |x + 2 * β u.toNNReal ω| ≤ 1} ≤
          ENNReal.ofReal r} ≤ ENNReal.ofReal (C / r))
    {δ : ℝ} {n : ℕ} (hn2 : 2 ≤ n) (hr2 : 2 ≤ scaleR δ n)
    (hrC : Real.exp 1 * max C 1 ≤ scaleR δ n) :
    P (manyTrialSet B δ n) ≤ ENNReal.ofReal (2 * bigN n * Real.exp (-(scaleR δ n / 2))) := by
  set N := bigN n with hN
  set r := scaleR δ n with hr
  set a := levelA δ n with ha
  set C' := max C 1 with hC'
  have hC'1 : 1 ≤ C' := le_max_right _ _
  have hr0 : 0 < r := by linarith
  have hamem : a ∈ Ioo (0 : ℝ) 1 := levelA_mem δ n hr0 (by omega)
  set Z := a ^ (-(2 : ℝ)) * Real.exp (-r) with hZ
  have hZ0 : 0 ≤ Z := by rw [hZ]; have := hamem.1; positivity
  -- one pair
  have hpair : ∀ k ∈ (Finset.Ioc (2 ^ n) (2 * 2 ^ n) : Finset ℕ), ∀ j ∈ Finset.range (4 ^ k + 1),
      P {ω | trialEventAt (drive 8 (UnzipInvariance.revBM B ((j : ℝ) / 4 ^ k).toNNReal) ω)
        (dyadicHeight k) ((j : ℝ) / 4 ^ k) a r ⌈r⌉₊} ≤
        ENNReal.ofReal (dyadicHeight k ^ 2 * Z) := by
    intro k hk j hj
    set T := (j : ℝ) / 4 ^ k with hT
    have hTm : T ∈ Icc (0 : ℝ) 1 := div_four_pow_mem hj
    set β := UnzipInvariance.revBM B T.toNNReal with hβ
    have hβB : IsBrownianReal β P :=
      UnzipInvariance.isBrownianReal_revBM hB.toIsPreBrownianReal hBc T.toNNReal
    have hβc : ∀ ω, Continuous fun t => β t ω := continuous_revBM hBc T.toNNReal
    have hβm : ∀ t, Measurable (β t) := measurable_revBM hBm T.toNNReal
    have hy : dyadicHeight k ∈ Ioc (0 : ℝ) 1 := ⟨dyadicHeight_pos k, dyadicHeight_le_one k⟩
    obtain ⟨⟨Q, hQ, ⟨β', hβ', hJ⟩, hPQ⟩, -⟩ :=
      h31 β hβB hβc hβm (revBM_zero T.toNNReal) T hTm (dyadicHeight k) hy
    have hCQ : ∀ β'' : ℝ≥0 → Ω → ℝ, IsBrownianReal β'' Q → (∀ ω, Continuous fun t => β'' t ω) →
        (∀ t, Measurable (β'' t)) → ∀ x : ℝ, |x| ≤ 2 * r →
          Q {ω | occRestart r x (fun t => β'' t ω) ≤ ENNReal.ofReal r} ≤
            ENNReal.ofReal (C' / r) := by
      intro β'' h1 h2 h3 x hx
      refine (hC Q β'' h1 h2 h3 r hr2 x hx).trans (ENNReal.ofReal_le_ofReal ?_)
      exact div_le_div_of_nonneg_right (le_max_left _ _) hr0.le
    have hbound := measure_trialEventAt_le hβc hTm hy hβ' hJ hPQ hCQ hamem hr2 ⌈r⌉₊
    refine hbound.trans ?_
    have hCr : C' / r ≤ Real.exp (-1) := by
      rw [div_le_iff₀ hr0, Real.exp_neg, inv_mul_eq_div, le_div_iff₀ (Real.exp_pos 1)]
      linarith
    have hpow : (C' / r) ^ ⌈r⌉₊ ≤ Real.exp (-r) := by
      calc (C' / r) ^ ⌈r⌉₊ ≤ Real.exp (-1) ^ ⌈r⌉₊ :=
            pow_le_pow_left₀ (by positivity) hCr _
        _ = Real.exp (-(⌈r⌉₊ : ℝ)) := by rw [← Real.exp_nat_mul]; ring_nf
        _ ≤ Real.exp (-r) := Real.exp_le_exp.2 (neg_le_neg (Nat.le_ceil r))
    rw [← ENNReal.ofReal_pow (by positivity), ← ENNReal.ofReal_mul (by positivity)]
    refine ENNReal.ofReal_le_ofReal ?_
    have ha2 : dyadicHeight k ^ 2 / a ^ 2 = dyadicHeight k ^ 2 * a ^ (-(2 : ℝ)) := by
      rw [Real.rpow_neg hamem.1.le, div_eq_mul_inv, Real.rpow_two]
    rw [ha2, hZ]
    have : 0 ≤ dyadicHeight k ^ 2 * a ^ (-(2 : ℝ)) := by have := hamem.1; positivity
    calc dyadicHeight k ^ 2 * a ^ (-(2 : ℝ)) * (C' / r) ^ ⌈r⌉₊
        ≤ dyadicHeight k ^ 2 * a ^ (-(2 : ℝ)) * Real.exp (-r) := by gcongr
      _ = dyadicHeight k ^ 2 * (a ^ (-(2 : ℝ)) * Real.exp (-r)) := by ring
  -- level `j`
  have hlevj : ∀ k ∈ (Finset.Ioc (2 ^ n) (2 * 2 ^ n) : Finset ℕ),
      P (⋃ j ∈ Finset.range (4 ^ k + 1),
        {ω | trialEventAt (drive 8 (UnzipInvariance.revBM B ((j : ℝ) / 4 ^ k).toNNReal) ω)
          (dyadicHeight k) ((j : ℝ) / 4 ^ k) a r ⌈r⌉₊}) ≤ ENNReal.ofReal (2 * Z) := by
    intro k hk
    refine (measure_biUnion_le_card_mul _ _ (hpair k hk)).trans (ENNReal.ofReal_le_ofReal ?_)
    rw [Finset.card_range]
    have h := dyadicHeight_sq_mul_le k
    calc ((4 ^ k + 1 : ℕ) : ℝ) * (dyadicHeight k ^ 2 * Z)
        = Z * (((4 ^ k + 1 : ℕ) : ℝ) * dyadicHeight k ^ 2) := by ring
      _ ≤ Z * 2 := by gcongr
      _ = 2 * Z := by ring
  refine (measure_biUnion_le_card_mul _ _ hlevj).trans (ENNReal.ofReal_le_ofReal ?_)
  rw [card_Ioc_two_pow, ← hN]
  have haexp : Z ≤ Real.exp (-(r / 2)) := by
    rw [hZ, ha, levelA, ← Real.exp_mul, ← Real.exp_add, Real.exp_le_exp]
    have hn' : (2 : ℝ) ≤ n := by exact_mod_cast hn2
    have h4 : (4 : ℝ) ≤ (n : ℝ) ^ 2 := by nlinarith
    have : r / (n : ℝ) ^ 2 * 2 ≤ r / 2 := by
      rw [div_mul_eq_mul_div, div_le_div_iff₀ (by positivity) (by norm_num)]
      nlinarith
    linarith
  have hN0 : 0 ≤ N := (bigN_pos n).le
  calc N * (2 * Z) ≤ N * (2 * Real.exp (-(r / 2))) := by gcongr
    _ = 2 * N * Real.exp (-(r / 2)) := by ring

/-! ## Proposition 4.1 -/

theorem two_mul_le_two_pow {n : ℕ} (hn : 2 ≤ n) : 2 * n ≤ 2 ^ n := by
  induction n, hn using Nat.le_induction with
  | base => norm_num
  | succ n hn ih => rw [pow_succ]; omega

/-- `(4M√N + 1) y_N ≤ 1` for all large `n` (so that `|m| v ≤ 1` in (4.9)). -/
theorem eventually_hbox {M : ℝ} (hM : 0 ≤ M) :
    ∀ᶠ n : ℕ in atTop, (4 * M * Real.sqrt (bigN n) + 1) * dyadicHeight (2 ^ n) ≤ 1 := by
  filter_upwards [eventually_ge_atTop (⌈4 * M + 1⌉₊ + 2)] with n hn
  have hn2 : 2 ≤ n := by omega
  have hN1 := one_le_bigN n
  have hsq := sqrt_bigN_le n
  have h1 : 4 * M + 1 ≤ bigN n := by
    have : 4 * M + 1 ≤ n := (Nat.le_ceil _).trans (by exact_mod_cast (show ⌈4 * M + 1⌉₊ ≤ n by omega))
    have h2 : (n : ℝ) < 2 ^ n := by exact_mod_cast Nat.lt_two_pow_self
    rw [bigN]; linarith
  have h2 : bigN n * bigN n ≤ (2 : ℝ) ^ (2 ^ n) := by
    rw [bigN, ← pow_add]
    exact pow_le_pow_right₀ (by norm_num) (by have := two_mul_le_two_pow hn2; omega)
  rw [dyadicHeight, ← div_eq_mul_inv, div_le_one (by positivity)]
  calc 4 * M * Real.sqrt (bigN n) + 1 ≤ (4 * M + 1) * bigN n := by nlinarith
    _ ≤ bigN n * bigN n := by gcongr
    _ ≤ _ := h2

/-- **Proposition 4.1 of the SLE₈ note (number of large scales), from Lemmas 3.1–3.3.**
Fix `δ ∈ (0, 1/10)`. Let `B` be a standard Brownian motion, `W = √8 B` (`drive 8 B ω`), `F_t` the centred
inverse Loewner maps, `A_k(t) = y_k |F_t'(iy_k)|` (`normalizedDeriv`), and for `n ≥ 1` put `N = 2ⁿ`,
`r = N^δ`, `a = exp(-r/n²)` (4.1) and `𝓘_n(t) = {k : N < k ≤ 2N, A_k(t_k) ≥ a}`,
`t_k = 4^{-k} ⌊4^k t⌋` (4.2). Almost surely there is a finite random `n₀` such that `|𝓘_n(t)| ≤ r⁷` for
every `n ≥ n₀` and every `t ∈ [0, 1]` (4.3).

The hypotheses are Lemmas 3.1, 3.2 and 3.3 of the note (`Lemma31Statement`, `Lemma32Statement`,
`Lemma33Statement`), which are proved by other packets. -/
theorem prop41_of_lemmas {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {B : ℝ≥0 → Ω → ℝ}
    (hB : IsBrownianReal B P) (h31 : Lemma31Statement P) (h32 : Lemma32Statement P)
    (h33 : Lemma33Statement Ω) {δ : ℝ} (hδ0 : 0 < δ) (hδ1 : δ < 1 / 10) :
    ∀ᵐ ω ∂P, ∃ n₀ : ℕ, ∀ n ≥ n₀, ∀ t ∈ Icc (0 : ℝ) 1,
      (((Finset.Ioc (2 ^ n) (2 * 2 ^ n)).filter fun k =>
          Real.exp (-(((2 : ℝ) ^ n) ^ δ / (n : ℝ) ^ 2)) ≤
            normalizedDeriv (drive 8 B ω) k (((4 : ℝ) ^ k)⁻¹ * ⌊(4 : ℝ) ^ k * t⌋)).card : ℝ) ≤
        (((2 : ℝ) ^ n) ^ δ) ^ 7 := by
  have : IsProbabilityMeasure P := hB.toIsPreBrownianReal.isGaussianProcess.isProbabilityMeasure
  obtain ⟨B'', hm'', hc'', h0'', hB'', hae''⟩ := RS.exists_good_version0 hB
  obtain ⟨K, hK1, hKb⟩ := exists_koebe_box
  obtain ⟨Cocc, h31'⟩ := h31
  obtain ⟨Ctr, hCtr⟩ := h33
  set Bad : ℕ → Set Ω := fun n => {ω | ∃ t ∈ Icc (0 : ℝ) 1,
    scaleR δ n ^ 7 < ((scaleSet (drive 8 B'' ω) δ n t).card : ℝ)} with hBad
  have hbN : ∀ n, 0 ≤ bigN n := fun n => (bigN_pos n).le
  -- for each `M`, Borel–Cantelli on `Ω_M`
  have hMae : ∀ M : ℕ, ∀ᵐ ω ∂P, ∀ᶠ n in atTop,
      ω ∉ {ω | DriverBound M (drive 8 B'' ω)} ∩ Bad n := by
    intro M
    obtain ⟨C32, hC32⟩ := h32 B'' hB'' hc'' hm'' h0'' M (1 / (2 * K)) (by positivity)
    have hM0 : (0 : ℝ) ≤ M := Nat.cast_nonneg M
    set b : ℕ → ℝ := fun n => 36 * max C32 0 * (4 * M + 1) ^ 3 * bigN n ^ 5 *
      Real.exp (-(scaleR δ n / 18)) + 2 * bigN n * Real.exp (-(scaleR δ n / 2)) with hb
    have hb0 : ∀ n, 0 ≤ b n := by
      intro n
      have := hbN n
      have : 0 ≤ max C32 0 := le_max_right _ _
      positivity
    have hbs : Summable b := by
      have h1 := (summable_bigN_pow_mul_exp 5 (by norm_num : (0 : ℝ) < 1 / 18) hδ0).mul_left
        (36 * max C32 0 * (4 * M + 1) ^ 3)
      have h2 := (summable_bigN_pow_mul_exp 1 (by norm_num : (0 : ℝ) < 1 / 2) hδ0).mul_left 2
      refine (h1.add h2).congr fun n => ?_
      simp only [hb, pow_one]
      ring_nf
    refine ae_eventually_notMem_of_le hb0 hbs ?_
    filter_upwards [eventually_selectionParams (Cocc := Cocc) hM0 hδ0 hδ1, eventually_ge_atTop 8,
      eventually_hbox hM0, eventually_linear_le_scaleR hδ0 0 (Real.exp 1 * max Ctr 1)]
      with n hpar hn8 hbox hrC
    simp only [zero_mul, zero_add] at hrC
    have hr2 : 2 ≤ scaleR δ n := hpar.two_le_r
    have hsub : {ω | DriverBound M (drive 8 B'' ω)} ∩ Bad n ⊆
        smallImageSet B'' M K δ n ∪ manyTrialSet B'' δ n := by
      rintro ω ⟨hMω, t, ht, hbad⟩
      have hW : Continuous (drive 8 B'' ω) := drive_continuous (hc'' ω)
      have hW0 : drive 8 B'' ω 0 = 0 := drive_zero (h0'' ω)
      have hsel := selection hW hW0 hMω
        (V := fun T => drive 8 (UnzipInvariance.revBM B'' T.toNNReal) ω)
        (fun T hT => ⟨drive_continuous (continuous_revBM hc'' _ ω),
          isRevExt_drive_revBM B'' ω hT.1⟩)
        (fun T hT y hy a ha hphi =>
          (h31' (UnzipInvariance.revBM B'' T.toNNReal)
            (UnzipInvariance.isBrownianReal_revBM hB''.toIsPreBrownianReal hc'' T.toNNReal)
            (continuous_revBM hc'' T.toNNReal) (measurable_revBM hm'' T.toNNReal)
            (revBM_zero T.toNNReal) T hT y hy).2 a ha ω hphi)
        hK1 (hKb (drive 8 B'' ω) hW hW0) (by omega) hpar ht hbad
      rcases hsel with ⟨k, hk, j, hj, ℓ, hℓ, hlog, m, hm, hA, hB2⟩ | ⟨k, hk, j, hj, hE⟩
      · left
        simp only [smallImageSet, mem_iUnion, mem_ofPred_eq, exists_prop]
        refine ⟨k, hk, j, hj, ℓ, Finset.mem_filter.2 ⟨hℓ, hlog⟩, m, ?_, hMω, hA, ?_⟩
        · have hm' := abs_le.1 hm
          refine Finset.mem_Icc.2 ⟨?_, ?_⟩
          · have : -m ≤ boxR M n k ℓ := Int.le_floor.2 (by push_cast; linarith)
            omega
          · exact Int.le_floor.2 (by linarith)
        · rw [show 1 / (2 * K) * levelA δ n = levelA δ n / (2 * K) by ring]; exact hB2
      · right
        simp only [manyTrialSet, mem_iUnion, mem_ofPred_eq, exists_prop]
        exact ⟨k, hk, j, hj, hE⟩
    have hnn1 : 0 ≤ 36 * max C32 0 * (4 * M + 1) ^ 3 * bigN n ^ 5 *
        Real.exp (-(scaleR δ n / 18)) := by
      have := hbN n; have : 0 ≤ max C32 0 := le_max_right _ _
      positivity
    have hnn2 : 0 ≤ 2 * bigN n * Real.exp (-(scaleR δ n / 2)) := by
      have := hbN n; positivity
    calc P ({ω | DriverBound M (drive 8 B'' ω)} ∩ Bad n)
        ≤ P (smallImageSet B'' M K δ n ∪ manyTrialSet B'' δ n) := measure_mono hsub
      _ ≤ P (smallImageSet B'' M K δ n) + P (manyTrialSet B'' δ n) := measure_union_le _ _
      _ ≤ ENNReal.ofReal (36 * max C32 0 * (4 * M + 1) ^ 3 * bigN n ^ 5 *
            Real.exp (-(scaleR δ n / 18))) +
          ENNReal.ofReal (2 * bigN n * Real.exp (-(scaleR δ n / 2))) :=
          add_le_add (measure_smallImageSet_le hC32 hn8 (scaleR_pos δ n) hbox)
            (measure_manyTrialSet_le hB'' hc'' hm'' h31' hCtr (by omega) hr2 hrC)
      _ = ENNReal.ofReal (b n) := by rw [← ENNReal.ofReal_add hnn1 hnn2]
  -- the countable union over `M`
  have hall : ∀ᵐ ω ∂P, ∀ M : ℕ, ∀ᶠ n in atTop,
      ω ∉ {ω | DriverBound M (drive 8 B'' ω)} ∩ Bad n := ae_all_iff.2 hMae
  filter_upwards [hall, ae_exists_nat_driverBound hB'' hc'', hae''] with ω hω ⟨M, hMω⟩ hgood
  obtain ⟨n₀, hn₀⟩ := eventually_atTop.1 (hω M)
  refine ⟨n₀, fun n hn t ht => ?_⟩
  have hWeq : drive 8 B ω = drive 8 B'' ω := funext fun s => by simp only [drive, hgood]
  by_contra hlt
  refine hn₀ n hn ⟨hMω, t, ht, ?_⟩
  rw [← hWeq]
  exact not_le.1 hlt

/-! ## Discharging Lemmas 3.2 and 3.3 -/

/-- **Lemma 3.2** in the form `Lemma32Statement`, from the landed `exists_measure_twoPoint_deriv_le`
(`TwoPoint.lean`, packet PROVE-S8-L32). -/
theorem lemma32Statement_holds {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) :
    Lemma32Statement P := by
  intro B hB _ _ _ M c₀ hc₀
  obtain ⟨C, hC⟩ := exists_measure_twoPoint_deriv_le (M : ℝ) hc₀
  exact ⟨C, fun t ht a ha y hy v hv m hmv => hC hB t ht a ha y hy v hv m hmv⟩

/-- **Lemma 3.3** in the form `Lemma33Statement` (constant `C_tr = 38`), from the landed
`measure_occupation_le` (`Occupation.lean`, packet PROVE-S8-OCC). -/
theorem lemma33Statement_holds (Ω : Type*) [MeasurableSpace Ω] : Lemma33Statement Ω := by
  refine ⟨38, fun Q β hβ hβc _ r hr x hx => ?_⟩
  refine (measure_mono fun ω hω => ?_).trans (measure_occupation_le hβ hr hx)
  simp only [mem_ofPred_eq] at hω ⊢
  set g : ℝ → ℝ := fun u => x + 2 * β u.toNNReal ω with hgdef
  have hg : Continuous g :=
    continuous_const.add (continuous_const.mul ((hβc ω).comp continuous_real_toNNReal))
  have hS : MeasurableSet (g ⁻¹' {y : ℝ | |y| ≤ 1}) :=
    (isClosed_le (continuous_abs.comp hg) continuous_const).measurableSet
  have hL : (0 : ℝ) ≤ 2 * r ^ 5 := by positivity
  have heq : (fun u => {y : ℝ | |y| ≤ 1}.indicator (fun _ => (1 : ℝ)) (g u)) =
      (g ⁻¹' {y : ℝ | |y| ≤ 1}).indicator 1 := by
    funext u
    by_cases h : |g u| ≤ 1 <;> simp [Set.indicator, h]
  show ∫ u in (0 : ℝ)..(2 * r ^ 5), {y : ℝ | |y| ≤ 1}.indicator (fun _ => (1 : ℝ)) (g u) ≤ r
  rw [intervalIntegral.integral_of_le hL, heq, integral_indicator_one hS, measureReal_def,
    Measure.restrict_apply hS]
  have hsub : g ⁻¹' {y : ℝ | |y| ≤ 1} ∩ Ioc 0 (2 * r ^ 5) ⊆
      {u : ℝ | u ∈ Icc 0 (2 * r ^ 5) ∧ |x + 2 * β u.toNNReal ω| ≤ 1} :=
    fun u hu => ⟨Ioc_subset_Icc_self hu.2, hu.1⟩
  exact ENNReal.toReal_le_of_le_ofReal (by linarith) ((measure_mono hsub).trans hω)

/-- **Proposition 4.1 of the SLE₈ note from Lemma 3.1** (Lemmas 3.2 and 3.3 are discharged). -/
theorem prop41_of_lemma31 {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {B : ℝ≥0 → Ω → ℝ}
    (hB : IsBrownianReal B P) (h31 : Lemma31Statement P) {δ : ℝ} (hδ0 : 0 < δ)
    (hδ1 : δ < 1 / 10) :
    ∀ᵐ ω ∂P, ∃ n₀ : ℕ, ∀ n ≥ n₀, ∀ t ∈ Icc (0 : ℝ) 1,
      (((Finset.Ioc (2 ^ n) (2 * 2 ^ n)).filter fun k =>
          Real.exp (-(((2 : ℝ) ^ n) ^ δ / (n : ℝ) ^ 2)) ≤
            normalizedDeriv (drive 8 B ω) k (((4 : ℝ) ^ k)⁻¹ * ⌊(4 : ℝ) ^ k * t⌋)).card : ℝ) ≤
        (((2 : ℝ) ^ n) ^ δ) ^ 7 :=
  prop41_of_lemmas hB h31 (lemma32Statement_holds P) (lemma33Statement_holds Ω) hδ0 hδ1

theorem gridTime_eq_gridT (k : ℕ) (t : ℝ) : gridTime k t = gridT k t := by
  unfold gridTime gridT
  rw [dyadicHeight_sq, div_inv_eq_mul, mul_comm t]

/-- **Proposition 4.1 from Lemma 3.1, in the form of the hypothesis `hP41` of
`ae_exists_continuous_trace_of_scale_count`** (`Radial.lean`; `t_k = gridTime k t`): for every standard
Brownian motion on `(Ω, ℙ)` and every `δ ∈ (0, 1/10)`, almost surely `|𝓘_n(t)| ≤ r⁷` for all large `n`
and all `t ∈ [0, 1]`. -/
theorem scaleCount_of_lemma31 {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    (h31 : Lemma31Statement P) :
    ∀ B : ℝ≥0 → Ω → ℝ, IsBrownianReal B P → ∀ δ : ℝ, 0 < δ → δ < 1 / 10 →
      ∀ᵐ ω ∂P, ∃ n₀ : ℕ, ∀ n ≥ n₀, ∀ t ∈ Icc (0 : ℝ) 1,
        (((Finset.Ioc (2 ^ n) (2 * 2 ^ n)).filter fun k =>
            Real.exp (-(((2 : ℝ) ^ n) ^ δ / (n : ℝ) ^ 2)) ≤
              normalizedDeriv (drive 8 B ω) k (gridTime k t)).card : ℝ) ≤
          (((2 : ℝ) ^ n) ^ δ) ^ 7 := by
  intro B hB δ hδ0 hδ1
  filter_upwards [prop41_of_lemma31 hB h31 hδ0 hδ1] with ω hω
  obtain ⟨n₀, h⟩ := hω
  refine ⟨n₀, fun n hn t ht => ?_⟩
  simp only [gridTime_eq_gridT]
  exact h n hn t ht

end InteractingSLE.SLE8
