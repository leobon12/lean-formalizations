import HigherDimLQGMetric.Sharp.W2Gaussian
import HigherDimLQGMetric.Core.Interfaces

/-!
# Gaussian estimates for sharp metric diameter moments

The completed-square estimate is the dimension-`d` version of
`LQGMetric.DFGPS.L311.l311_exponent`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace HigherDimLQGMetric

open MeasureTheory ProbabilityTheory Set
open HigherDimLFPP (Rd)
open scoped ENNReal

variable {d : ℕ}

/-- The algebraic completed-square bound behind the all-scales Gaussian estimate. -/
private theorem w3_exponent {ℓ t c q σ δ D : ℝ} (ht : 0 ≤ t) (hc : 0 < c)
    (hD : 0 ≤ D)
    (hδ : 0 ≤ δ) (hσ : σ ^ 2 = q ^ 2 - 2 * D - 2 * δ) :
    D * t - (ℓ + q * t) ^ 2 / (2 * (t + c)) ≤
      -(q + σ) * ℓ + (q + σ) * q * c - δ * t := by
  have hu : 0 < 2 * (t + c) := by positivity
  have key : 0 ≤ (ℓ + q * t) ^ 2 -
      2 * (t + c) * (D * t + (q + σ) * ℓ - (q + σ) * q * c + δ * t) := by
    have e : (ℓ + q * t) ^ 2 -
        2 * (t + c) * (D * t + (q + σ) * ℓ - (q + σ) * q * c + δ * t) =
        (ℓ - q * c - σ * (t + c)) ^ 2 +
          (q ^ 2 - 2 * D - 2 * δ - σ ^ 2) * (t + c) ^ 2 +
          2 * (D + δ) * (t + c) * c := by ring
    have hzero : q ^ 2 - 2 * D - 2 * δ - σ ^ 2 = 0 := by linarith
    rw [e, hzero, zero_mul, add_zero]
    positivity
  have hdiv : D * t + (q + σ) * ℓ - (q + σ) * q * c + δ * t ≤
      (ℓ + q * t) ^ 2 / (2 * (t + c)) := by
    rw [le_div_iff₀ hu]
    nlinarith only [key]
  linarith only [hdiv]

private theorem w3_log_max_le {R x : ℝ} (_hR : 0 < R) (hx : 0 ≤ x)
    (hxR : x ≤ R) : max 0 (Real.log x) ≤ max 0 (Real.log R) := by
  by_cases hx0 : x = 0
  · rw [hx0, Real.log_zero, max_self]
    exact le_max_left _ _
  · have hxpos : 0 < x := lt_of_le_of_ne hx (Ne.symm hx0)
    exact max_le (le_max_left _ _) ((Real.log_le_log hxpos hxR).trans (le_max_right _ _))

/-- Variance of a sphere-average difference on a dyadic grid is at most
`n log 2` plus a constant independent of the LGF, scale, and grid point. -/
theorem w3_variance_dyadic (hd : 2 ≤ d) {R c : ℝ} (hR : 0 < R) (hc : 0 < c) :
    ∃ K : ℝ, 0 < K ∧ ∀ {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
      {h : Ω → DistRd d}, IsWholeSpaceLGF h P → ∀ {𝕣 : ℝ}, 0 < 𝕣 →
      ∀ n : ℕ, ∀ w : Rd d, ‖w‖ ≤ R * 𝕣 →
      Var[fun ω => sphereAvg (h ω) (c * 𝕣 / 2 ^ n) w - sphereAvg (h ω) 𝕣 0; P] ≤
        n * Real.log 2 + K := by
  obtain ⟨K₀, hK₀⟩ := exists_variance_sphereAvg_sub_le hd
  let K : ℝ := |Real.log c| + 2 * max 0 (Real.log R) + max 0 K₀ + 1
  have hK : 0 < K := by dsimp [K]; positivity
  refine ⟨K, hK, ?_⟩
  intro Ω _ P h hh 𝕣 h𝕣 n w hw
  let s : ℝ := c * 𝕣 / 2 ^ n
  have hs : 0 < s := by dsimp [s]; positivity
  have hlog₁ : Real.log (𝕣 / s) = n * Real.log 2 - Real.log c := by
    have he : 𝕣 / s = (2 : ℝ) ^ n / c := by dsimp [s]; field_simp
    rw [he, Real.log_div (by positivity) hc.ne', Real.log_pow]
  have hlog₂ : Real.log (s / 𝕣) = Real.log c - n * Real.log 2 := by
    have he : s / 𝕣 = c / (2 : ℝ) ^ n := by dsimp [s]; field_simp
    rw [he, Real.log_div hc.ne' (by positivity), Real.log_pow]
  have hKn : K₀ ≤ max 0 K₀ := le_max_right _ _
  have hLn : 0 ≤ n * Real.log 2 := by positivity
  rcases le_total s 𝕣 with hle | hle
  · have hv := (hK₀ hh hs h𝕣 w 0).1 hle
    simp only [sub_zero] at hv
    have hratio : ‖w‖ / 𝕣 ≤ R := (div_le_iff₀ h𝕣).2 (by simpa [mul_comm] using hw)
    have hlog := w3_log_max_le hR (by positivity) hratio
    rw [hlog₁] at hv
    dsimp [K]
    linarith only [hv, hlog, hKn, neg_le_abs (Real.log c), hLn]
  · have hv := (hK₀ hh hs h𝕣 w 0).2 hle
    simp only [sub_zero] at hv
    have hratio : ‖w‖ / s ≤ R := by
      apply (div_le_iff₀ hs).2
      calc ‖w‖ ≤ R * 𝕣 := hw
        _ ≤ R * s := mul_le_mul_of_nonneg_left hle hR.le
    have hlog := w3_log_max_le hR (by positivity) hratio
    rw [hlog₂] at hv
    dsimp [K]
    linarith only [hv, hlog, hKn, le_abs_self (Real.log c), hLn]

/-- Gaussian union bound for one dyadic level, with the optimized Chernoff parameter. -/
theorem w3_dyadic_level (hd : 2 ≤ d) {q c CG K C 𝕣 : ℝ}
    (hq : 0 < q) (hc : 0 < c) (hK : 0 < K) (hC : 1 < C) (h𝕣 : 0 < 𝕣)
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (h : Ω → DistRd d) (hh : IsWholeSpaceLGF h P) (G : ℕ → Finset (Rd d))
    (hcard : ∀ n, ((G n).card : ℝ) ≤ CG * 2 ^ (d * n))
    (hvar : ∀ n, ∀ w ∈ G n,
      Var[fun ω => sphereAvg (h ω) (c * 𝕣 / 2 ^ n) w - sphereAvg (h ω) 𝕣 0; P] ≤
        n * Real.log 2 + K) (n : ℕ) :
    P {ω | ∃ w ∈ G n, Real.log C + q * n * Real.log 2 <
        |sphereAvg (h ω) (c * 𝕣 / 2 ^ n) w - sphereAvg (h ω) 𝕣 0|} ≤
      ENNReal.ofReal (2 * CG * 2 ^ (d * n) *
        Real.exp (-(Real.log C + q * n * Real.log 2) ^ 2 /
          (2 * (n * Real.log 2 + K)))) := by
  let T : ℝ := Real.log C + q * n * Real.log 2
  let V : ℝ := n * Real.log 2 + K
  have hlog2 : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  have hlogC : 0 ≤ Real.log C := (Real.log_pos hC).le
  have hT : 0 ≤ T := by
    dsimp [T]
    exact add_nonneg hlogC (mul_nonneg (mul_nonneg hq.le (Nat.cast_nonneg _)) hlog2)
  have hV : 0 < V := by dsimp [V]; positivity
  let s : ℝ := T / V
  have hs : 0 ≤ s := div_nonneg hT hV.le
  have hX : ∀ w ∈ G n, HasGaussianLaw
      (fun ω => sphereAvg (h ω) (c * 𝕣 / 2 ^ n) w - sphereAvg (h ω) 𝕣 0) P := by
    intro w _
    exact (hh.hasGaussianLaw_sphereAvg_sub hd (by positivity) h𝕣 w 0).1
  have h0 : ∀ w ∈ G n, ∫ ω,
      (sphereAvg (h ω) (c * 𝕣 / 2 ^ n) w - sphereAvg (h ω) 𝕣 0) ∂P = 0 := by
    intro w _
    exact (hh.hasGaussianLaw_sphereAvg_sub hd (by positivity) h𝕣 w 0).2
  have hraw := w2_gaussian_finset_union (G n)
    (fun w ω => sphereAvg (h ω) (c * 𝕣 / 2 ^ n) w - sphereAvg (h ω) 𝕣 0)
    hX h0 (fun w hw => hvar n w hw) hs (V := V) (T := T)
  have he : -s * T + s ^ 2 * V / 2 = -T ^ 2 / (2 * V) := by
    dsimp [s]
    field_simp
    ring
  rw [he] at hraw
  calc
    _ ≤ ENNReal.ofReal (((G n).card : ℝ) *
        (2 * Real.exp (-T ^ 2 / (2 * V)))) := hraw
    _ ≤ ENNReal.ofReal ((CG * 2 ^ (d * n)) *
        (2 * Real.exp (-T ^ 2 / (2 * V)))) := by
          exact ENNReal.ofReal_le_ofReal
            (mul_le_mul_of_nonneg_right (hcard n) (by positivity))
    _ = _ := by congr 1; dsimp [T, V]; ring

/-- The level estimate has geometric decay after completing the square. -/
theorem w3_dyadic_level_geom (hd : 2 ≤ d) {q c CG K C 𝕣 σ δ : ℝ}
    (hq : 0 < q) (hc : 0 < c) (hK : 0 < K) (hC : 1 < C) (h𝕣 : 0 < 𝕣)
    (hδ : 0 ≤ δ) (hσ : σ ^ 2 = q ^ 2 - 2 * d - 2 * δ)
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (h : Ω → DistRd d) (hh : IsWholeSpaceLGF h P) (G : ℕ → Finset (Rd d))
    (hcard : ∀ n, ((G n).card : ℝ) ≤ CG * 2 ^ (d * n))
    (hvar : ∀ n, ∀ w ∈ G n,
      Var[fun ω => sphereAvg (h ω) (c * 𝕣 / 2 ^ n) w - sphereAvg (h ω) 𝕣 0; P] ≤
        n * Real.log 2 + K) (n : ℕ) :
    P {ω | ∃ w ∈ G n, Real.log C + q * n * Real.log 2 <
        |sphereAvg (h ω) (c * 𝕣 / 2 ^ n) w - sphereAvg (h ω) 𝕣 0|} ≤
      ENNReal.ofReal (2 * CG * Real.exp ((q + σ) * q * K) * C ^ (-(q + σ)) *
        Real.exp (-δ * Real.log 2) ^ n) := by
  have hCG : 0 ≤ CG := by
    by_contra hn
    have h := hcard 0
    norm_num at h
    linarith
  have ht : 0 ≤ (n : ℝ) * Real.log 2 := by positivity
  have he := w3_exponent ht hK (Nat.cast_nonneg d) hδ hσ (ℓ := Real.log C)
  have hpow : (2 : ℝ) ^ (d * n) = Real.exp ((d : ℝ) * (n * Real.log 2)) := by
    rw [show (d : ℝ) * (n * Real.log 2) = (d * n : ℕ) * Real.log 2 by push_cast; ring,
      Real.exp_nat_mul, Real.exp_log (by norm_num : (0 : ℝ) < 2)]
  have hr : Real.exp (-δ * Real.log 2) ^ n =
      Real.exp (-δ * (n * Real.log 2)) := by
    rw [← Real.exp_nat_mul]
    congr 1
    ring
  have hCp : C ^ (-(q + σ)) = Real.exp (-(q + σ) * Real.log C) := by
    rw [Real.rpow_def_of_pos (by linarith : 0 < C)]
    congr 1
    ac_rfl
  refine (w3_dyadic_level hd hq hc hK hC h𝕣 P h hh G hcard hvar n).trans
    (ENNReal.ofReal_le_ofReal ?_)
  rw [hpow, hr, hCp]
  calc
    2 * CG * Real.exp ((d : ℝ) * (n * Real.log 2)) *
        Real.exp (-(Real.log C + q * n * Real.log 2) ^ 2 /
          (2 * (n * Real.log 2 + K))) =
      2 * CG * Real.exp ((d : ℝ) * (n * Real.log 2) -
        (Real.log C + q * n * Real.log 2) ^ 2 /
          (2 * (n * Real.log 2 + K))) := by
            rw [sub_eq_add_neg, Real.exp_add]
            ring_nf
    _ ≤ 2 * CG * Real.exp (-(q + σ) * Real.log C +
        (q + σ) * q * K - δ * (n * Real.log 2)) := by
          have he' : (d : ℝ) * (n * Real.log 2) -
              (Real.log C + q * n * Real.log 2) ^ 2 /
                (2 * (n * Real.log 2 + K)) ≤
              -(q + σ) * Real.log C + (q + σ) * q * K - δ * (n * Real.log 2) := by
                convert he using 1
                ring_nf
          exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr he') (by positivity)
    _ = _ := by
      rw [show -(q + σ) * Real.log C + (q + σ) * q * K - δ * (n * Real.log 2) =
        (q + σ) * q * K + -(q + σ) * Real.log C + -δ * (n * Real.log 2) by ring,
        Real.exp_add, Real.exp_add]
      ring

/-- Corrected [1] Lemma 4.14: uniform Gaussian control on any family of dyadic grids
whose cardinalities grow at most like `2^(dn)`. -/
theorem sphereAvg_allScales (hd : 2 ≤ d) {q : ℝ}
    (hq : Real.sqrt (2 * d) < q) {R c CG : ℝ}
    (hR : 0 < R) (hc : 0 < c) (hCG : 0 < CG) {a : ℝ}
    (ha : a < q + Real.sqrt (q ^ 2 - 2 * d)) :
    ∃ C₀ K : ℝ, ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
      [IsProbabilityMeasure P] (h : Ω → DistRd d), IsWholeSpaceLGF h P →
      ∀ 𝕣 : ℝ, 0 < 𝕣 → ∀ G : ℕ → Finset (Rd d),
      (∀ n, ((G n).card : ℝ) ≤ CG * 2 ^ (d * n)) →
      (∀ n, ∀ w ∈ G n, ‖w‖ ≤ R * 𝕣) →
      ∀ C : ℝ, C₀ ≤ C →
      P {ω | ∃ n : ℕ, ∃ w ∈ G n, Real.log C + q * n * Real.log 2 <
        |sphereAvg (h ω) (c * 𝕣 / 2 ^ n) w - sphereAvg (h ω) 𝕣 0|} ≤
        ENNReal.ofReal (K * C ^ (-a)) := by
  obtain ⟨V, hV0, hV⟩ := w3_variance_dyadic hd hR hc
  have hq0 : 0 < q := (Real.sqrt_nonneg _).trans_lt hq
  have hd0 : (0 : ℝ) ≤ 2 * d := by positivity
  have hroot2 : (Real.sqrt (2 * d)) ^ 2 = 2 * d := Real.sq_sqrt hd0
  have hdisc : 0 < q ^ 2 - 2 * d := by
    nlinarith only [hq, hq0, Real.sqrt_nonneg (2 * d), hroot2]
  let s₀ := Real.sqrt (q ^ 2 - 2 * d)
  have hs₀ : 0 < s₀ := Real.sqrt_pos.2 hdisc
  have hs₀sq : s₀ ^ 2 = q ^ 2 - 2 * d := Real.sq_sqrt hdisc.le
  let z₀ := max 0 (a - q)
  have hz₀ : 0 ≤ z₀ := le_max_left _ _
  have hza : a - q ≤ z₀ := le_max_right _ _
  have hzlt : z₀ < s₀ := max_lt hs₀ (by dsimp [s₀] at ha ⊢; linarith only [ha])
  let σ := (z₀ + s₀) / 2
  have hσ0 : 0 ≤ σ := by dsimp [σ]; linarith only [hz₀, hs₀.le]
  have hσlt : σ < s₀ := by dsimp [σ]; linarith only [hzlt]
  have hzaσ : a < q + σ := by dsimp [σ]; linarith only [hza, hzlt]
  let δ := (s₀ ^ 2 - σ ^ 2) / 2
  have hδ : 0 < δ := by
    dsimp [δ]
    nlinarith only [hs₀, hσ0, hσlt]
  have hσsq : σ ^ 2 = q ^ 2 - 2 * d - 2 * δ := by
    dsimp [δ]
    nlinarith only [hs₀sq]
  let r := Real.exp (-δ * Real.log 2)
  have hr0 : 0 ≤ r := (Real.exp_pos _).le
  have hr1 : r < 1 := Real.exp_lt_one_iff.2 (by
    have hlog2 := Real.log_pos (by norm_num : (1 : ℝ) < 2)
    nlinarith only [hδ, hlog2])
  let B := 2 * CG * Real.exp ((q + σ) * q * V)
  have hB : 0 ≤ B := by dsimp [B]; positivity
  let K := B / (1 - r)
  have hK : 0 ≤ K := by dsimp [K]; positivity
  refine ⟨2, K, ?_⟩
  intro Ω _ P _ h hh 𝕣 h𝕣 G hcard hgrid C hC
  have hC1 : 1 < C := by linarith
  have hvar : ∀ n, ∀ w ∈ G n,
      Var[fun ω => sphereAvg (h ω) (c * 𝕣 / 2 ^ n) w - sphereAvg (h ω) 𝕣 0; P] ≤
        n * Real.log 2 + V := by
    intro n w hw
    exact hV hh h𝕣 n w (hgrid n w hw)
  let E : ℕ → Set Ω := fun n => {ω | ∃ w ∈ G n,
    Real.log C + q * n * Real.log 2 <
      |sphereAvg (h ω) (c * 𝕣 / 2 ^ n) w - sphereAvg (h ω) 𝕣 0|}
  have hE : {ω | ∃ n : ℕ, ∃ w ∈ G n,
      Real.log C + q * n * Real.log 2 <
        |sphereAvg (h ω) (c * 𝕣 / 2 ^ n) w - sphereAvg (h ω) 𝕣 0|} =
      ⋃ n, E n := by ext ω; simp only [mem_iUnion, E, mem_ofPred_eq]
  have hterm : ∀ n, P (E n) ≤ ENNReal.ofReal (B * C ^ (-(q + σ)) * r ^ n) := by
    intro n
    exact w3_dyadic_level_geom hd hq0 hc hV0 hC1 h𝕣 hδ.le hσsq
      P h hh G hcard hvar n
  have hsum : Summable (fun n : ℕ => B * C ^ (-(q + σ)) * r ^ n) :=
    (summable_geometric_of_lt_one hr0 hr1).mul_left _
  have hpow : C ^ (-(q + σ)) ≤ C ^ (-a) :=
    Real.rpow_le_rpow_of_exponent_le hC1.le (by linarith only [hzaσ])
  rw [hE]
  calc
    P (⋃ n, E n) ≤ ∑' n, P (E n) := measure_iUnion_le _
    _ ≤ ∑' n, ENNReal.ofReal (B * C ^ (-(q + σ)) * r ^ n) :=
      ENNReal.tsum_le_tsum hterm
    _ = ENNReal.ofReal (∑' n, B * C ^ (-(q + σ)) * r ^ n) :=
      (ENNReal.ofReal_tsum_of_nonneg (fun n => by positivity) hsum).symm
    _ ≤ ENNReal.ofReal (K * C ^ (-a)) := by
      refine ENNReal.ofReal_le_ofReal ?_
      rw [tsum_mul_left, tsum_geometric_of_lt_one hr0 hr1]
      have he : B * C ^ (-(q + σ)) * (1 - r)⁻¹ = K * C ^ (-(q + σ)) := by
        dsimp [K]
        ring
      rw [he]
      exact mul_le_mul_of_nonneg_left hpow hK

/-- Translation-invariant form of the all-scales Gaussian bound. The grids
are offsets from the chosen center, as in the sharp-moment argument. -/
theorem w3_sphereAvg_allScales_shifted (hd : 2 ≤ d) {q : ℝ}
    (hq : Real.sqrt (2 * d) < q) {R c CG : ℝ}
    (hR : 0 < R) (hc : 0 < c) (hCG : 0 < CG) {a : ℝ}
    (ha : a < q + Real.sqrt (q ^ 2 - 2 * d)) :
    ∃ C₀ K : ℝ, ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
      [IsProbabilityMeasure P] (h : Ω → DistRd d), IsWholeSpaceLGF h P →
      ∀ r : ℝ, 0 < r → ∀ z : Rd d, ∀ G : ℕ → Finset (Rd d),
      (∀ n, ((G n).card : ℝ) ≤ CG * 2 ^ (d * n)) →
      (∀ n, ∀ w ∈ G n, ‖w‖ ≤ R * r) →
      ∀ C : ℝ, C₀ ≤ C →
      P {ω | ∃ n : ℕ, ∃ w ∈ G n, Real.log C + q * n * Real.log 2 <
        |sphereAvg (h ω) (c * r / 2 ^ n) (z + w) - sphereAvg (h ω) r z|} ≤
        ENNReal.ofReal (K * C ^ (-a)) := by
  obtain ⟨C₀, K, hK⟩ := sphereAvg_allScales hd hq hR hc hCG ha
  refine ⟨C₀, K, ?_⟩
  intro Ω _ P _ h hh r hr z G hcard hbound C hC
  let g : Ω → DistRd d := fun ω => affineComp 1 z (h ω)
  have hg : IsWholeSpaceLGF g P := hh.affineComp one_pos z
  have hbase := hK P g hg r hr G hcard hbound C hC
  have hevent : {ω | ∃ n : ℕ, ∃ w ∈ G n, Real.log C + q * n * Real.log 2 <
        |sphereAvg (h ω) (c * r / 2 ^ n) (z + w) - sphereAvg (h ω) r z|} =
      {ω | ∃ n : ℕ, ∃ w ∈ G n, Real.log C + q * n * Real.log 2 <
        |sphereAvg (g ω) (c * r / 2 ^ n) w - sphereAvg (g ω) r 0|} := by
    ext ω
    simp only [Set.mem_ofPred_eq, g, sphereAvg_affineComp_one, zero_add]
    simp_rw [add_comm z]
  rw [hevent]
  exact hbase

end HigherDimLQGMetric
