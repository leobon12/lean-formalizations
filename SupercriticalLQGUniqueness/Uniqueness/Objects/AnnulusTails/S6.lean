import SupercriticalLQGUniqueness.Uniqueness.Objects.AnnulusTails.Tail
import SupercriticalLQGUniqueness.Uniqueness.Objects.AnnulusTails.Grid




 





















set_option autoImplicit false

noncomputable section

open Set Filter Topology MeasureTheory ProbabilityTheory Metric
open scoped ENNReal

namespace SupercriticalLQGUniqueness.Uniqueness.Objects.AnnulusTails

open LQGMetric (DistC)

 
theorem two_rpow_neg_sub_four (n : ℕ) :
    (2 : ℝ) ^ (-(n : ℝ) - 4) = ((16 : ℝ) * 2 ^ n)⁻¹ := by
  rw [show -(n : ℝ) - 4 = -((n : ℝ) + 4) by ring, Real.rpow_neg (by norm_num),
    Real.rpow_add (by norm_num), Real.rpow_natCast, mul_inv, mul_inv]
  norm_num
  exact mul_comm _ _

 
def narrowFinset (C : Objects.CorrectedEvent.Constants) (n : ℕ) : Finset ℂ := by
  classical
  exact (gridBoxFinset ((2 : ℝ) ^ (-(n : ℝ) - 4) * C.r)
    ⌈(3 * C.r + (2 : ℝ) ^ (-(n : ℝ) - 4) * C.r) / ((2 : ℝ) ^ (-(n : ℝ) - 4) * C.r)⌉₊).filter
      (· ∈ Objects.CorrectedEvent.narrowSites C n)

theorem narrowSites_subset (C : Objects.CorrectedEvent.Constants) (n : ℕ) :
    Objects.CorrectedEvent.narrowSites C n ⊆ ↑(narrowFinset C n) := by
  classical
  intro z hz
  have ha : 0 < (2 : ℝ) ^ (-(n : ℝ) - 4) * C.r := mul_pos (Real.rpow_pos_of_pos two_pos _) C.rPos
  have hnorm : ‖z‖ ≤ 3 * C.r + (2 : ℝ) ^ (-(n : ℝ) - 4) * C.r :=
    norm_le_of_infDist_cann_le (by linarith [C.rPos]) (by linarith [C.rPos]) hz.2
  have hmem := grid_inter_closedBall_subset (ρ := 3 * C.r + (2 : ℝ) ^ (-(n : ℝ) - 4) * C.r) ha
    ⟨hz.1, by
    rw [mem_closedBall, dist_zero_right]
    exact hnorm⟩
  unfold narrowFinset
  rw [Finset.coe_filter]
  exact ⟨hmem, hz⟩

theorem narrowSites_norm_le (C : Objects.CorrectedEvent.Constants) (n : ℕ) {v : ℂ}
    (hv : v ∈ Objects.CorrectedEvent.narrowSites C n) : ‖v‖ ≤ 4 * C.r := by
  have hnorm : ‖v‖ ≤ 3 * C.r + (2 : ℝ) ^ (-(n : ℝ) - 4) * C.r :=
    norm_le_of_infDist_cann_le (by linarith [C.rPos]) (by linarith [C.rPos]) hv.2
  have h1 : (2 : ℝ) ^ (-(n : ℝ) - 4) ≤ 1 := by
    rw [two_rpow_neg_sub_four]
    apply inv_le_one_of_one_le₀
    have : (1 : ℝ) ≤ 2 ^ n := one_le_pow₀ (by norm_num)
    nlinarith
  nlinarith [C.rPos]

theorem card_narrowFinset_le (C : Objects.CorrectedEvent.Constants) (n : ℕ) :
    ((narrowFinset C n).card : ℝ) ≤ 12544 * 4 ^ n := by
  classical
  set x : ℝ := (16 : ℝ) * 2 ^ n with hxdef
  have hx16 : 16 ≤ x := by
    have : (1 : ℝ) ≤ 2 ^ n := one_le_pow₀ (by norm_num)
    rw [hxdef]; linarith
  have hr : 0 < C.r := C.rPos
  have hratio : (3 * C.r + (2 : ℝ) ^ (-(n : ℝ) - 4) * C.r) / ((2 : ℝ) ^ (-(n : ℝ) - 4) * C.r) =
      3 * x + 1 := by
    rw [two_rpow_neg_sub_four, ← hxdef]
    have hx0 : 0 < x := by linarith
    field_simp
  set N : ℕ := ⌈(3 * C.r + (2 : ℝ) ^ (-(n : ℝ) - 4) * C.r) /
    ((2 : ℝ) ^ (-(n : ℝ) - 4) * C.r)⌉₊ with hNdef
  have hN : (N : ℝ) ≤ 3 * x + 2 := by
    have := Nat.ceil_lt_add_one (show 0 ≤ (3 * C.r + (2 : ℝ) ^ (-(n : ℝ) - 4) * C.r) /
      ((2 : ℝ) ^ (-(n : ℝ) - 4) * C.r) by rw [hratio]; linarith)
    rw [hratio] at this
    rw [hNdef, hratio]
    linarith
  have hcard : (narrowFinset C n).card ≤ (2 * N + 1) ^ 2 := by
    unfold narrowFinset
    exact (Finset.card_filter_le _ _).trans (card_gridBoxFinset_le _ _)
  have hcardR : ((narrowFinset C n).card : ℝ) ≤ (2 * (N : ℝ) + 1) ^ 2 := by exact_mod_cast hcard
  have h4 : (4 : ℝ) ^ n = (2 ^ n) ^ 2 := by rw [← pow_mul, mul_comm, pow_mul]; norm_num
  have hx2 : x ^ 2 = 256 * 4 ^ n := by rw [hxdef, mul_pow, h4]; norm_num
  have hN0 : (0 : ℝ) ≤ N := Nat.cast_nonneg N
  calc ((narrowFinset C n).card : ℝ) ≤ (2 * (N : ℝ) + 1) ^ 2 := hcardR
    _ ≤ (7 * x) ^ 2 := by
        have : 2 * (N : ℝ) + 1 ≤ 7 * x := by linarith
        exact pow_le_pow_left₀ (by positivity) this 2
    _ = 12544 * 4 ^ n := by rw [mul_pow, hx2]; ring

 
def narrowScaleIoi (C : Objects.CorrectedEvent.Constants) (n : ℕ) : Ioi (0 : ℝ) :=
  ⟨Objects.CorrectedEvent.narrowScale C n, mem_Ioi.mpr (mul_pos (Real.rpow_pos_of_pos two_pos _) C.rPos)⟩

 
theorem s6_acr_bound (ξ : Ioi (0 : ℝ)) (Q : ℝ) (hQ : 0 < Q) (D : DistC → LSCMetric)
    (hD : IsWeakLQGMetric ξ Q D) :
    ∃ (nR : ℕ) (C₆ : ℝ), 0 < C₆ ∧ ∀ (μ : Measure DistC) [IsProbabilityMeasure μ],
      IsNormalizedWholePlaneGFF (id : DistC → DistC) μ →
      ∀ C : Objects.CorrectedEvent.Constants, C.ξ = ξ → C.Q = Q → ∀ n : ℕ, nR ≤ n → ∀ v : ℂ,
        μ {g | Objects.CorrectedEvent.acr (D g) v (Objects.CorrectedEvent.narrowScale C n / 4) (Objects.CorrectedEvent.narrowScale C n) <
            ENNReal.ofReal ((2 : ℝ) ^ (-(Objects.CorrectedEvent.zeta C) * (n : ℝ))) *
              Objects.CorrectedEvent.normalizer C g (Objects.CorrectedEvent.narrowScale C n) v} ≤
          ENNReal.ofReal (C₆ * (2 : ℝ) ^ (-(3 : ℝ) * n)) := by
  have hξ : (0 : ℝ) < ξ := ξ.2
  set ζ : ℝ := (ξ : ℝ) / (4 * (1 + ξ)) with hζdef
  have hζ : 0 < ζ := by rw [hζdef]; positivity
  obtain ⟨R₀, C₆, hR₀, hC₆, htail⟩ :=
    acr_lower_tail ξ Q hQ D hD (a := 1 / 4) (b := 1) (by norm_num) (by norm_num) (3 / ζ)
      (by positivity)
  
  have hev : ∀ᶠ n : ℕ in atTop, R₀ ≤ (2 : ℝ) ^ (ζ * n) := by
    have ht : Tendsto (fun n : ℕ => (2 : ℝ) ^ (ζ * n)) atTop atTop := by
      have h1 : Tendsto (fun n : ℕ => Real.log 2 * (ζ * (n : ℝ))) atTop atTop :=
        (tendsto_natCast_atTop_atTop.const_mul_atTop hζ).const_mul_atTop
          (Real.log_pos (by norm_num))
      have he : (fun n : ℕ => (2 : ℝ) ^ (ζ * n)) =
          fun n : ℕ => Real.exp (Real.log 2 * (ζ * (n : ℝ))) := by
        funext n
        rw [Real.rpow_def_of_pos (by norm_num)]
      rw [he]
      exact Real.tendsto_exp_atTop.comp h1
    exact ht.eventually_ge_atTop R₀
  obtain ⟨nR, hnR⟩ := eventually_atTop.1 hev
  refine ⟨nR, C₆, hC₆, ?_⟩
  intro μ _ hμ C hCξ hCQ n hn v
  have hz : Objects.CorrectedEvent.zeta C = ζ := by rw [Objects.CorrectedEvent.zeta, hCξ]
  set s : Ioi (0 : ℝ) := narrowScaleIoi C n with hsdef
  have hR := hnR n hn
  have hb := htail μ id hμ ((2 : ℝ) ^ (ζ * n)) hR s v
  have hset : {g | Objects.CorrectedEvent.acr (D g) v (Objects.CorrectedEvent.narrowScale C n / 4) (Objects.CorrectedEvent.narrowScale C n) <
      ENNReal.ofReal ((2 : ℝ) ^ (-(Objects.CorrectedEvent.zeta C) * (n : ℝ))) *
        Objects.CorrectedEvent.normalizer C g (Objects.CorrectedEvent.narrowScale C n) v} =
      {g | Objects.CorrectedEvent.acr (D (id g)) v (1 / 4 * s) (1 * s) <
        ENNReal.ofReal ((2 : ℝ) ^ (ζ * n))⁻¹ * nrm ξ Q (id g) s v} := by
    ext g
    simp only [mem_ofPred_eq, id]
    have h1 : Objects.CorrectedEvent.narrowScale C n / 4 = 1 / 4 * (s : ℝ) := by
      change Objects.CorrectedEvent.narrowScale C n / 4 = 1 / 4 * Objects.CorrectedEvent.narrowScale C n
      ring
    have h2 : Objects.CorrectedEvent.narrowScale C n = 1 * (s : ℝ) := by
      change Objects.CorrectedEvent.narrowScale C n = 1 * Objects.CorrectedEvent.narrowScale C n
      ring
    have h3 : (2 : ℝ) ^ (-(Objects.CorrectedEvent.zeta C) * (n : ℝ)) = ((2 : ℝ) ^ (ζ * n))⁻¹ := by
      rw [hz, ← Real.rpow_neg (by norm_num)]
      ring_nf
    have h4 : Objects.CorrectedEvent.normalizer C g (Objects.CorrectedEvent.narrowScale C n) v = nrm ξ Q g s v := by
      rw [← nrm_eq_normalizer, hCξ, hCQ]
      rfl
    rw [h3, h4, h1, h2]
  rw [hset]
  refine hb.trans (ENNReal.ofReal_le_ofReal ?_)
  have hpow : ((2 : ℝ) ^ (ζ * n)) ^ (-(3 / ζ)) = (2 : ℝ) ^ (-(3 : ℝ) * n) := by
    rw [← Real.rpow_mul (by norm_num)]
    congr 1
    field_simp
  rw [hpow]

 

theorem s6_gauss_bound (μ : Measure DistC) [IsProbabilityMeasure μ]
    (hμ : IsNormalizedWholePlaneGFF (id : DistC → DistC) μ) (C : Objects.CorrectedEvent.Constants) {n : ℕ}
    (hn1 : 1 ≤ n) (hnζ : 2 * Real.log 2 + 4 * Real.log 5 ≤ Objects.CorrectedEvent.zeta C * n * Real.log 2)
    {v : ℂ} (hv : v ∈ Objects.CorrectedEvent.narrowSites C n) :
    μ {g | (2 + Objects.CorrectedEvent.zeta C) * (n : ℝ) * Real.log 2 <
        |LQGMetric.circleAvg g (Objects.CorrectedEvent.narrowScale C n) v - LQGMetric.circleAvg g C.r 0|} ≤
      ENNReal.ofReal (2 * Real.exp (-((2 + Objects.CorrectedEvent.zeta C) * n * Real.log 2))) := by
  have hr : 0 < C.r := C.rPos
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hl5 : 0 < Real.log 5 := Real.log_pos (by norm_num)
  have hζ : 0 ≤ Objects.CorrectedEvent.zeta C := by
    unfold Objects.CorrectedEvent.zeta
    have := C.ξPos
    positivity
  have hsn : Objects.CorrectedEvent.narrowScale C n = (2 : ℝ) ^ (-(n : ℝ) - 1) * C.r := rfl
  have hspos : 0 < Objects.CorrectedEvent.narrowScale C n := by rw [hsn]; positivity
  have hsle : Objects.CorrectedEvent.narrowScale C n ≤ C.r := by
    rw [hsn]
    have : (2 : ℝ) ^ (-(n : ℝ) - 1) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos (by norm_num)
      (by have : (0 : ℝ) ≤ n := Nat.cast_nonneg n; linarith)
    nlinarith
  have hlog : Real.log (C.r / Objects.CorrectedEvent.narrowScale C n) = (n + 1) * Real.log 2 := by
    rw [hsn, div_mul_eq_div_div_swap, div_self hr.ne', one_div, ← Real.rpow_neg (by norm_num),
      Real.log_rpow (by norm_num)]
    ring
  have hnpos : (1 : ℝ) ≤ n := by exact_mod_cast hn1
  have hV : 0 < Real.log (C.r / Objects.CorrectedEvent.narrowScale C n) + 2 * Real.log (4 + 1) := by
    rw [hlog]
    have : 0 < (n + 1 : ℝ) * Real.log 2 := by positivity
    have : 0 ≤ Real.log (4 + 1 : ℝ) := Real.log_nonneg (by norm_num)
    linarith
  have hx : 0 < (2 + Objects.CorrectedEvent.zeta C) * (n : ℝ) * Real.log 2 := by positivity
  have hwy : ‖v - 0‖ ≤ 4 * C.r := by rw [sub_zero]; exact narrowSites_norm_le C n hv
  have hT := circleAvg_inc_tail (a := Objects.CorrectedEvent.narrowScale C n) (s := C.r) (R := 4) hμ.1 hspos hsle
    (by norm_num) v 0 hwy hV hx
  have hsub : {g : DistC | (2 + Objects.CorrectedEvent.zeta C) * (n : ℝ) * Real.log 2 <
      |LQGMetric.circleAvg g (Objects.CorrectedEvent.narrowScale C n) v - LQGMetric.circleAvg g C.r 0|} ⊆
      {ω : DistC | (2 + Objects.CorrectedEvent.zeta C) * (n : ℝ) * Real.log 2 ≤
        |LQGMetric.circleAvg (id ω) (Objects.CorrectedEvent.narrowScale C n) v -
          LQGMetric.circleAvg (id ω) C.r 0|} := fun g hg => by
    simp only [mem_ofPred_eq, id] at hg ⊢
    exact le_of_lt hg
  refine (measure_mono hsub).trans (hT.trans (ENNReal.ofReal_le_ofReal ?_))
  have hV2 : 2 * (Real.log (C.r / Objects.CorrectedEvent.narrowScale C n) + 2 * Real.log (4 + 1)) ≤
      (2 + Objects.CorrectedEvent.zeta C) * (n : ℝ) * Real.log 2 := by
    rw [hlog, show (4 + 1 : ℝ) = 5 by norm_num]
    nlinarith
  have hexp : -((2 + Objects.CorrectedEvent.zeta C) * (n : ℝ) * Real.log 2) ^ 2 /
      (2 * (Real.log (C.r / Objects.CorrectedEvent.narrowScale C n) + 2 * Real.log (4 + 1))) ≤
      -((2 + Objects.CorrectedEvent.zeta C) * n * Real.log 2) := by
    rw [neg_div, neg_le_neg_iff, le_div_iff₀ (by positivity), sq]
    exact mul_le_mul_of_nonneg_left hV2 hx.le
  have := Real.exp_le_exp.mpr hexp
  linarith

 
theorem summable_s6_level {C₆ ζ : ℝ} (hζ : 0 < ζ) :
    Summable fun n : ℕ => 12544 * (C₆ * (1 / 2 : ℝ) ^ n + 2 * Real.exp (-(ζ * Real.log 2)) ^ n) := by
  have h1 : Summable fun n : ℕ => (1 / 2 : ℝ) ^ n :=
    summable_geometric_of_lt_one (by norm_num) (by norm_num)
  have h2 : Summable fun n : ℕ => Real.exp (-(ζ * Real.log 2)) ^ n :=
    summable_geometric_of_lt_one (Real.exp_pos _).le
      (Real.exp_lt_one_iff.mpr (by have := Real.log_pos (by norm_num : (1 : ℝ) < 2); nlinarith))
  exact ((h1.mul_left C₆).add (h2.mul_left 2)).mul_left 12544

 
theorem s6_level_arith (C₆ ζ : ℝ) (n : ℕ) :
    12544 * 4 ^ n * (C₆ * (2 : ℝ) ^ (-(3 : ℝ) * n) +
        2 * Real.exp (-((2 + ζ) * n * Real.log 2))) =
      12544 * (C₆ * (1 / 2 : ℝ) ^ n + 2 * Real.exp (-(ζ * Real.log 2)) ^ n) := by
  have h4 : (4 : ℝ) ^ n = Real.exp (2 * n * Real.log 2) := by
    rw [show (2 : ℝ) * n * Real.log 2 = n * Real.log 4 by
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; push_cast; ring,
      ← Real.log_rpow (by norm_num), Real.exp_log (by positivity), Real.rpow_natCast]
  have h3 : (2 : ℝ) ^ (-(3 : ℝ) * n) = Real.exp (-(3 * n * Real.log 2)) := by
    rw [Real.rpow_def_of_pos (by norm_num)]
    ring_nf
  have hhalf : (1 / 2 : ℝ) ^ n = Real.exp (-(n * Real.log 2)) := by
    rw [one_div, inv_pow, ← Real.exp_log (by positivity : (0 : ℝ) < 2 ^ n), Real.log_pow,
      ← Real.exp_neg]
  have hz : Real.exp (-(ζ * Real.log 2)) ^ n = Real.exp (-(ζ * n * Real.log 2)) := by
    rw [← Real.exp_nat_mul]
    ring_nf
  rw [h4, h3, hhalf, hz, mul_add, mul_add]
  have e1 : Real.exp (2 * n * Real.log 2) * Real.exp (-(3 * n * Real.log 2)) =
      Real.exp (-(n * Real.log 2)) := by
    rw [← Real.exp_add]; ring_nf
  have e2 : Real.exp (2 * n * Real.log 2) * Real.exp (-((2 + ζ) * n * Real.log 2)) =
      Real.exp (-(ζ * n * Real.log 2)) := by
    rw [← Real.exp_add]; ring_nf
  calc 12544 * Real.exp (2 * n * Real.log 2) * (C₆ * Real.exp (-(3 * n * Real.log 2))) +
        12544 * Real.exp (2 * n * Real.log 2) * (2 * Real.exp (-((2 + ζ) * n * Real.log 2)))
      = 12544 * (C₆ * (Real.exp (2 * n * Real.log 2) * Real.exp (-(3 * n * Real.log 2)))) +
          12544 * (2 * (Real.exp (2 * n * Real.log 2) *
            Real.exp (-((2 + ζ) * n * Real.log 2)))) := by ring
    _ = 12544 * (C₆ * Real.exp (-(n * Real.log 2))) +
          12544 * (2 * Real.exp (-(ζ * n * Real.log 2))) := by rw [e1, e2]

 


theorem exists_s6_budget (μ : Measure DistC) [IsProbabilityMeasure μ]
    (hμ : IsNormalizedWholePlaneGFF (id : DistC → DistC) μ)
    (ξ : Ioi (0 : ℝ)) (Q : ℝ) (D : DistC → LSCMetric) (hD : IsWeakLQGMetric ξ Q D)
    (pbar : Ioo (0 : ℝ) 1) :
    ∃ n₁ : ℕ, ∀ C : Objects.CorrectedEvent.Constants, C.ξ = ξ → C.Q = Q → n₁ ≤ Objects.CorrectedEvent.narrowStart C →
      μ {g | ¬ Objects.CorrectedEvent.S6 C (D g) g} ≤ ENNReal.ofReal ((1 - (pbar : ℝ)) / 10) := by
  by_cases hQ : 0 < Q
  swap
  · refine ⟨0, fun C _ hCQ _ => absurd (hCQ ▸ C.QPos) hQ⟩
  have hξ : (0 : ℝ) < ξ := ξ.2
  set ζ : ℝ := (ξ : ℝ) / (4 * (1 + ξ)) with hζdef
  have hζ : 0 < ζ := by rw [hζdef]; positivity
  obtain ⟨nR, C₆, hC₆, hacr⟩ := s6_acr_bound ξ Q hQ D hD
  set b : ℕ → ℝ := fun n => 12544 * (C₆ * (1 / 2 : ℝ) ^ n +
    2 * Real.exp (-(ζ * Real.log 2)) ^ n) with hbdef
  have hb0 : ∀ n, 0 ≤ b n := fun n => by positivity
  have hbs : Summable b := summable_s6_level hζ
  have hε : 0 < (1 - (pbar : ℝ)) / 10 := by linarith [pbar.2.2]
  
  have htail : ∀ᶠ k : ℕ in atTop, ∑' n, b (n + k) < (1 - (pbar : ℝ)) / 10 :=
    (tendsto_sum_nat_add b).eventually (gt_mem_nhds hε)
  have hgauss : ∀ᶠ n : ℕ in atTop, 2 * Real.log 2 + 4 * Real.log 5 ≤ ζ * n * Real.log 2 := by
    have : Tendsto (fun n : ℕ => ζ * n * Real.log 2) atTop atTop := by
      have := (tendsto_natCast_atTop_atTop.const_mul_atTop hζ).atTop_mul_const
        (Real.log_pos (by norm_num : (1 : ℝ) < 2))
      simpa only [mul_assoc] using this
    exact this.eventually_ge_atTop _
  obtain ⟨n₁, hn₁⟩ := eventually_atTop.1 ((htail.and hgauss).and
    ((eventually_ge_atTop nR).and (eventually_ge_atTop 1)))
  refine ⟨n₁, fun C hCξ hCQ hC => ?_⟩
  have hz : Objects.CorrectedEvent.zeta C = ζ := by rw [Objects.CorrectedEvent.zeta, hCξ]
  obtain ⟨⟨hsum, -⟩, -, -⟩ := hn₁ n₁ le_rfl
  
  let A : ℕ → ℂ → Set DistC := fun n v =>
    {g | Objects.CorrectedEvent.acr (D g) v (Objects.CorrectedEvent.narrowScale C n / 4) (Objects.CorrectedEvent.narrowScale C n) <
      ENNReal.ofReal ((2 : ℝ) ^ (-(Objects.CorrectedEvent.zeta C) * (n : ℝ))) *
        Objects.CorrectedEvent.normalizer C g (Objects.CorrectedEvent.narrowScale C n) v}
  let G : ℕ → ℂ → Set DistC := fun n v =>
    {g | (2 + Objects.CorrectedEvent.zeta C) * (n : ℝ) * Real.log 2 <
      |LQGMetric.circleAvg g (Objects.CorrectedEvent.narrowScale C n) v - LQGMetric.circleAvg g C.r 0|}
  have hsub : {g | ¬ Objects.CorrectedEvent.S6 C (D g) g} ⊆
      ⋃ k : ℕ, ⋃ v ∈ narrowFinset C (k + n₁), (A (k + n₁) v ∪ G (k + n₁) v) := by
    intro g hg
    simp only [Objects.CorrectedEvent.S6, not_forall, not_and_or, not_le] at hg
    obtain ⟨n, hn, v, hv, hfail⟩ := hg
    have hn' : n₁ ≤ n := hC.trans hn
    refine mem_iUnion.2 ⟨n - n₁, ?_⟩
    rw [Nat.sub_add_cancel hn']
    refine mem_iUnion₂.2 ⟨v, Finset.mem_coe.1 (narrowSites_subset C n hv), ?_⟩
    rcases hfail with h | h
    · exact Or.inl h
    · exact Or.inr h
  have hlevel : ∀ k : ℕ, μ (⋃ v ∈ narrowFinset C (k + n₁), (A (k + n₁) v ∪ G (k + n₁) v)) ≤
      ENNReal.ofReal (b (k + n₁)) := by
    intro k
    set n := k + n₁ with hndef
    obtain ⟨⟨-, hgn⟩, hnR, hn1⟩ := hn₁ n (by omega)
    have hgn' : 2 * Real.log 2 + 4 * Real.log 5 ≤ Objects.CorrectedEvent.zeta C * n * Real.log 2 := by
      rw [hz]; exact hgn
    have hsite : ∀ v ∈ narrowFinset C n, μ (A n v ∪ G n v) ≤
        ENNReal.ofReal (C₆ * (2 : ℝ) ^ (-(3 : ℝ) * n) +
          2 * Real.exp (-((2 + ζ) * n * Real.log 2))) := by
      intro v hv
      have hvS : v ∈ Objects.CorrectedEvent.narrowSites C n := by
        classical
        unfold narrowFinset at hv
        exact (Finset.mem_filter.1 hv).2
      have hA := hacr μ hμ C hCξ hCQ n hnR v
      have hG := s6_gauss_bound μ hμ C hn1 hgn' hvS
      rw [hz] at hG
      calc μ (A n v ∪ G n v) ≤ μ (A n v) + μ (G n v) := measure_union_le _ _
        _ ≤ ENNReal.ofReal (C₆ * (2 : ℝ) ^ (-(3 : ℝ) * n)) +
            ENNReal.ofReal (2 * Real.exp (-((2 + ζ) * n * Real.log 2))) := add_le_add hA (by
              have : G n v = {g | (2 + ζ) * (n : ℝ) * Real.log 2 <
                  |LQGMetric.circleAvg g (Objects.CorrectedEvent.narrowScale C n) v -
                    LQGMetric.circleAvg g C.r 0|} := by
                simp only [G, hz]
              rw [this]
              exact hG)
        _ = ENNReal.ofReal (C₆ * (2 : ℝ) ^ (-(3 : ℝ) * n) +
            2 * Real.exp (-((2 + ζ) * n * Real.log 2))) :=
            (ENNReal.ofReal_add (by positivity) (by positivity)).symm
    calc μ (⋃ v ∈ narrowFinset C n, (A n v ∪ G n v))
        ≤ ∑ v ∈ narrowFinset C n, μ (A n v ∪ G n v) := measure_biUnion_finset_le _ _
      _ ≤ ∑ _v ∈ narrowFinset C n, ENNReal.ofReal (C₆ * (2 : ℝ) ^ (-(3 : ℝ) * n) +
            2 * Real.exp (-((2 + ζ) * n * Real.log 2))) := Finset.sum_le_sum hsite
      _ = ENNReal.ofReal ((narrowFinset C n).card * (C₆ * (2 : ℝ) ^ (-(3 : ℝ) * n) +
            2 * Real.exp (-((2 + ζ) * n * Real.log 2)))) := sum_const_ofReal _ _
      _ ≤ ENNReal.ofReal (12544 * 4 ^ n * (C₆ * (2 : ℝ) ^ (-(3 : ℝ) * n) +
            2 * Real.exp (-((2 + ζ) * n * Real.log 2)))) := by
          apply ENNReal.ofReal_le_ofReal
          exact mul_le_mul_of_nonneg_right (card_narrowFinset_le C n) (by positivity)
      _ = ENNReal.ofReal (b n) := by rw [s6_level_arith]
  calc μ {g | ¬ Objects.CorrectedEvent.S6 C (D g) g}
      ≤ μ (⋃ k : ℕ, ⋃ v ∈ narrowFinset C (k + n₁), (A (k + n₁) v ∪ G (k + n₁) v)) :=
        measure_mono hsub
    _ ≤ ∑' k : ℕ, μ (⋃ v ∈ narrowFinset C (k + n₁), (A (k + n₁) v ∪ G (k + n₁) v)) :=
        measure_iUnion_le _
    _ ≤ ∑' k : ℕ, ENNReal.ofReal (b (k + n₁)) := ENNReal.tsum_le_tsum hlevel
    _ = ENNReal.ofReal (∑' k : ℕ, b (k + n₁)) :=
        (ENNReal.ofReal_tsum_of_nonneg (fun k => hb0 _)
          ((summable_nat_add_iff n₁).2 hbs)).symm
    _ ≤ ENNReal.ofReal ((1 - (pbar : ℝ)) / 10) := ENNReal.ofReal_le_ofReal hsum.le

 

theorem exists_s6_budget_nar (μ : Measure DistC) [IsProbabilityMeasure μ]
    (hμ : IsNormalizedWholePlaneGFF (id : DistC → DistC) μ)
    (ξ : Ioi (0 : ℝ)) (Q : ℝ) (D : DistC → LSCMetric) (hD : IsWeakLQGMetric ξ Q D)
    (pbar : Ioo (0 : ℝ) 1) :
    ∃ K : ℝ, 0 < K ∧ ∀ C : Objects.CorrectedEvent.Constants, C.ξ = ξ → C.Q = Q → K * C.A_nar ≤ C.lamConst →
      μ {g | ¬ Objects.CorrectedEvent.S6 C (D g) g} ≤ ENNReal.ofReal ((1 - (pbar : ℝ)) / 10) := by
  obtain ⟨n₁, hn₁⟩ := exists_s6_budget μ hμ ξ Q D hD pbar
  refine ⟨(2 : ℝ) ^ n₁, by positivity, fun C hCξ hCQ hK => hn₁ C hCξ hCQ ?_⟩
  have hnar := C.narPos
  have hlam : (2 : ℝ) ^ n₁ ≤ C.lamConst / C.A_nar := by rw [le_div_iff₀ hnar]; exact hK
  have hlog : (n₁ : ℝ) ≤ Real.logb 2 (C.lamConst / C.A_nar) := by
    rw [Real.le_logb_iff_rpow_le (by norm_num) (lt_of_lt_of_le (by positivity) hlam),
      Real.rpow_natCast]
    exact hlam
  unfold Objects.CorrectedEvent.narrowStart
  have : n₁ ≤ ⌊Real.logb 2 (C.lamConst / C.A_nar)⌋₊ := Nat.le_floor hlog
  omega

end SupercriticalLQGUniqueness.Uniqueness.Objects.AnnulusTails
