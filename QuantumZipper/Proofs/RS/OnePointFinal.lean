import QuantumZipper.Proofs.RS.OnePointFinalWhitney
import QuantumZipper.Blueprint.External3

/-!
# EXT-RS S1-5 and S1-6: Beffara's one-point estimate `Blueprint.SLEOnePointBound`

`blueprint/EXT_RS_BLUEPRINT.md` §5, nodes S1-5, S1-6.

* `prob_logCR_lt_unif`: S1-3 (`prob_logCR_lt`, Lawler–Zhou arXiv:1006.4936 Prop 2.3, upper bound)
  with the constant chosen before the probability space (the proof of `prob_logCR_lt` is repeated
  verbatim; its constant depends on `κ` only).
* **S1-5** `prob_infDist_lt_im` (**own argument**, DEVIATIONS L-S1): for `8 Im z ≤ |z|`,
  `P(dist(z, η) < Im z) ≤ C (Im z/|z|)^{8/κ−1}`, by the union bound over the Whitney cover of
  `OnePointFinalWhitney` and S1-4 at each cover point. The layer sums are
  `Σ_k σ^{−k} σ^{2kβ} < ∞`, which needs `β = 8/κ − 1 > 1/2` (here `κ ≤ 4`, so `β ≥ 1`).
* **S1-6** `sleOnePointBound : Blueprint.SLEOnePointBound` (Beffara, *The dimension of the SLE
  curves*, Ann. Probab. 36 (2008), Prop 4 (p. 6), upper half; range `ε ≤ Im z` as in Lawler,
  *Conformally Invariant Processes in the Plane*, Thm 7.9, p. 159): S1-4 for `ε ≤ c₁ Im z`, S1-5
  for `c₁ Im z < ε ≤ Im z` and `8 Im z ≤ |z|`, and the trivial bound `P ≤ 1` otherwise.
-/

noncomputable section

open Set Filter Topology Metric MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace QuantumZipper.RS

open FrozenMart FwdHolo FwdClock

/-- **S1-3 with a uniform constant.** Same statement and proof as `prob_logCR_lt`, with `∃ C`
moved in front of the probability space. -/
theorem prob_logCR_lt_unif {κ : ℝ} (hκ : 0 < κ) (hκ8 : κ < 8) : ∃ C : ℝ,
    ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
      (B : ℝ≥0 → Ω → ℝ), IsBrownianReal B P → ∀ z ∈ H, ∀ r : ℝ, 0 < r → r ≤ z.im / 2 →
      P {ω | ∃ t ≥ (0 : ℝ), z ∉ fwdHull (drive κ B ω) t ∧
        Real.exp (fwdLogCR (drive κ B ω) t z) < r}
      ≤ ENNReal.ofReal (C * (r / z.im) ^ (1 - κ / 8) * (z.im / ‖z‖) ^ (8 / κ - 1)) := by
  have hp : 0 < 8 / κ - 1 := by rw [sub_pos, lt_div_iff₀ hκ]; linarith
  obtain ⟨K, hK0, hK⟩ := exists_barK hp
  obtain ⟨CW, hCW⟩ := barW_le_rpow hp
  have hW1 : 0 < barW (8 / κ - 1) 1 := by
    rw [barW_eq]; exact div_pos (barNum_pos hp one_pos) (barDen_pos hp)
  have hCW0 : 0 ≤ CW := by
    have h1 := hCW 1 zero_le_one
    rw [Real.one_rpow, mul_one] at h1
    exact (barW_mem_Icc hp zero_le_one).1.trans h1
  set A : ℝ := Real.exp (2 * K) * CW * (1 / Real.sqrt (min (κ / 4 * Real.log 2) 1)) ^ (8 / κ - 1)
    with hA
  have hA0 : 0 ≤ A := by positivity
  refine ⟨A / barW (8 / κ - 1) 1 * Real.exp ((1 - κ / 8) * (4 / κ)), ?_⟩
  intro Ω _ P _ B hB z hz r hr hrz
  have hz' : 0 < z.im := hz
  obtain ⟨B', hB'm, hB'c, hB'eq⟩ := WedgeRes.exists_good_version hB
  set B'' : ℝ≥0 → Ω → ℝ := fun t ω => B' t ω - B' 0 ω with hB''
  have hB0 : ∀ᵐ ω ∂P, B 0 ω = 0 := hB.toIsPreBrownianReal.eval_zero_ae_eq_zero
  have hB''eq : ∀ᵐ ω ∂P, ∀ t, B'' t ω = B t ω := by
    filter_upwards [hB'eq, hB0] with ω h1 h2
    intro t
    simp only [hB'', h1, h2, sub_zero]
  have hB''pre : IsPreBrownianReal B'' P :=
    hB.toIsPreBrownianReal.congr fun t => hB''eq.mono fun ω h => (h t).symm
  have hB''m : ∀ t, Measurable (B'' t) := fun t =>
    (hB'm.comp measurable_prodMk_left).sub (hB'm.comp measurable_prodMk_left)
  have hB''c : ∀ ω, Continuous (B'' · ω) := fun ω => (hB'c ω).sub continuous_const
  have hB''0 : ∀ ω, B'' 0 ω = 0 := fun ω => sub_self _
  have hcore := opw_prob_good hB''pre hB''c hB''m hB''0 hκ hκ8 hK0 hK hCW hz' hr hrz
  refine le_trans (measure_mono_ae ?_) (hcore.trans (ENNReal.ofReal_le_ofReal ?_))
  · filter_upwards [hB''eq] with ω hω
    have hdr : drive κ B'' ω = drive κ B ω := funext fun t => by simp only [drive, hω]
    intro h
    simpa only [mem_ofPred_eq, hdr] using h
  · have h := opw_rhs_le hκ8 hz' hr
    have e : A * Real.exp ((1 - κ / 8) * min (Real.log z.im) (Real.log r + 4 / κ))
        * phiMF κ (z, Real.log z.im) / barW (8 / κ - 1) 1
        = A / barW (8 / κ - 1) 1 * (Real.exp ((1 - κ / 8) * min (Real.log z.im)
          (Real.log r + 4 / κ)) * phiMF κ (z, Real.log z.im)) := by ring
    rw [e]
    calc A / barW (8 / κ - 1) 1 * (Real.exp ((1 - κ / 8) * min (Real.log z.im)
          (Real.log r + 4 / κ)) * phiMF κ (z, Real.log z.im))
        ≤ A / barW (8 / κ - 1) 1 * (Real.exp ((1 - κ / 8) * (4 / κ)) * ((r / z.im) ^ (1 - κ / 8)
          * (z.im / ‖z‖) ^ (8 / κ - 1))) :=
          mul_le_mul_of_nonneg_left h (div_nonneg hA0 hW1.le)
      _ = _ := by ring

/-- `(σ^k)⁻¹ (σ^{2k})^β = (σ^{2β−1})^k`. -/
theorem wSig_pow_identity (β : ℝ) (k : ℕ) :
    (wSig ^ k)⁻¹ * (wSig ^ (2 * k)) ^ β = (wSig ^ (2 * β - 1)) ^ k := by
  have hσ := wSig_pos
  rw [← Real.rpow_natCast wSig k, ← Real.rpow_neg hσ.le, ← Real.rpow_natCast wSig (2 * k),
    ← Real.rpow_mul hσ.le, ← Real.rpow_add hσ, ← Real.rpow_natCast (wSig ^ (2 * β - 1)) k,
    ← Real.rpow_mul hσ.le]
  congr 1; push_cast; ring

/-- Number of cover points in layer `k`. -/
theorem card_Icc_wM (k : ℕ) :
    ((Finset.Icc (-(wM k : ℤ)) (wM k)).card : ℝ) ≤ (2 / wDel + 4) * (wSig ^ k)⁻¹ := by
  have hc : (Finset.Icc (-(wM k : ℤ)) (wM k)).card = 2 * wM k + 1 := by
    rw [Int.card_Icc]; omega
  rw [hc]; push_cast
  have h1 := wM_le k
  have hX : 1 ≤ (wSig ^ k)⁻¹ :=
    (one_le_inv₀ (pow_pos wSig_pos k)).2 (pow_le_one₀ wSig_pos.le wSig_lt_one.le)
  have hδ := wDel_pos
  generalize (wSig ^ k)⁻¹ = X at h1 hX
  have e : (2 / wDel + 4) * X = 2 * (X / wDel) + 4 * X := by ring
  rw [e]; linarith

/-- The constant of S1-5. -/
def onePointC5 (κ C₄ : ℝ) : ℝ :=
  (2 / wDel + 4) * (max C₄ 0 * onePointC1 ^ (1 - κ / 8) * 4 ^ (8 / κ - 1))
    / (1 - wSig ^ (2 * (8 / κ - 1) - 1))

theorem onePointC5_nonneg {κ : ℝ} (hκ : 0 < κ) (hκ4 : κ ≤ 4) (C₄ : ℝ) :
    0 ≤ onePointC5 κ C₄ := by
  have hβ : 1 ≤ 8 / κ - 1 := by rw [le_sub_iff_add_le, le_div_iff₀ hκ]; linarith
  have hr1 : wSig ^ (2 * (8 / κ - 1) - 1) < 1 :=
    Real.rpow_lt_one wSig_pos.le wSig_lt_one (by linarith)
  have := wDel_pos
  have := onePointC1_pos
  unfold onePointC5
  refine div_nonneg ?_ (by linarith)
  have h1 : 0 ≤ onePointC1 ^ (1 - κ / 8) := Real.rpow_nonneg onePointC1_pos.le _
  have h2 : 0 ≤ (4 : ℝ) ^ (8 / κ - 1) := Real.rpow_nonneg (by norm_num) _
  have h3 : 0 ≤ max C₄ 0 := le_max_right _ _
  positivity

variable {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}

/-- **S1-5 (Whitney extension; own argument).** If S1-4 holds with constant `C₄`, then for
`8 Im z ≤ |z|`, `P(dist(z, η[0,∞)) < Im z) ≤ C₅ (Im z/|z|)^{8/κ−1}`. -/
theorem prob_infDist_lt_im {B : ℝ≥0 → Ω → ℝ} {κ : ℝ} (hκ : 0 < κ) (hκ4 : κ ≤ 4) {C₄ : ℝ}
    (hC₄ : ∀ z ∈ H, ∀ ε : ℝ, 0 < ε → ε ≤ onePointC1 * z.im →
      P {ω | infDist z (sleTrace κ B ω '' Ici 0) < ε}
        ≤ ENNReal.ofReal (C₄ * (ε / z.im) ^ (1 - κ / 8) * (z.im / ‖z‖) ^ (8 / κ - 1))) :
    ∀ z ∈ H, 8 * z.im ≤ ‖z‖ →
      P {ω | infDist z (sleTrace κ B ω '' Ici 0) < z.im}
        ≤ ENNReal.ofReal (onePointC5 κ C₄ * (z.im / ‖z‖) ^ (8 / κ - 1)) := by
  intro z hz h8
  have hβ : 1 ≤ 8 / κ - 1 := by rw [le_sub_iff_add_le, le_div_iff₀ hκ]; linarith
  have hr0 : 0 ≤ wSig ^ (2 * (8 / κ - 1) - 1) := Real.rpow_nonneg wSig_pos.le _
  have hr1 : wSig ^ (2 * (8 / κ - 1) - 1) < 1 :=
    Real.rpow_lt_one wSig_pos.le wSig_lt_one (by linarith)
  have hy : 0 < z.im := hz
  have hzn : 0 < ‖z‖ := by linarith
  have hs : 0 ≤ z.im / ‖z‖ := div_nonneg hy.le hzn.le
  have hsβ : 0 ≤ (z.im / ‖z‖) ^ (8 / κ - 1) := Real.rpow_nonneg hs _
  have hc1 : 0 ≤ onePointC1 ^ (1 - κ / 8) := Real.rpow_nonneg onePointC1_pos.le _
  have h4 : 0 ≤ (4 : ℝ) ^ (8 / κ - 1) := Real.rpow_nonneg (by norm_num) _
  set β := 8 / κ - 1 with hβdef
  set r := wSig ^ (2 * β - 1) with hrdef
  set s := z.im / ‖z‖ with hsdef
  set A := max C₄ 0 * onePointC1 ^ (1 - κ / 8) * 4 ^ β with hAdef
  have hA : 0 ≤ A := mul_nonneg (mul_nonneg (le_max_right _ _) hc1) h4
  set D := (2 / wDel + 4) * A with hDdef
  have hD : 0 ≤ D := mul_nonneg (by have := wDel_pos; positivity) hA
  set E : ℕ → ℤ → Set Ω := fun k m => {ω | infDist (wPt z.re z.im k m)
    (sleTrace κ B ω '' Ici 0) < onePointC1 * (wPt z.re z.im k m).im} with hEdef
  have hcov : {ω | infDist z (sleTrace κ B ω '' Ici 0) < z.im}
      ⊆ ⋃ k, ⋃ m ∈ Finset.Icc (-(wM k : ℤ)) (wM k), E k m := by
    intro ω hω
    have hne : (sleTrace κ B ω '' Ici 0).Nonempty := ⟨_, mem_image_of_mem _ (mem_Ici.2 le_rfl)⟩
    obtain ⟨q, hqK, hq⟩ := (infDist_lt_iff hne).1 hω
    obtain ⟨k, m, hm, hd⟩ := whitney_cover hy (by rwa [dist_comm] at hq)
    refine mem_iUnion.2 ⟨k, mem_iUnion₂.2 ⟨m, hm, ?_⟩⟩
    show infDist _ _ < _
    exact lt_of_le_of_lt (infDist_le_dist_of_mem hqK) (by rwa [dist_comm] at hd)
  have hpt : ∀ k : ℕ, ∀ m ∈ Finset.Icc (-(wM k : ℤ)) (wM k),
      P (E k m) ≤ ENNReal.ofReal (A * s ^ β * (wSig ^ (2 * k)) ^ β) := by
    intro k m hm
    have hwim : (wPt z.re z.im k m).im = wHeight z.im k := rfl
    have hh0 := wHeight_pos hy k
    have hw0 : 0 < (wPt z.re z.im k m).im := by rw [hwim]; exact hh0
    have hε : 0 < onePointC1 * (wPt z.re z.im k m).im := mul_pos onePointC1_pos hw0
    refine (hC₄ _ hw0 _ hε le_rfl).trans (ENNReal.ofReal_le_ofReal ?_)
    rw [mul_div_cancel_right₀ _ hw0.ne']
    have hwn := norm_wPt_ge hy h8 hm
    set w := wPt z.re z.im k m
    have hwn0 : 0 < ‖w‖ := by linarith
    have hq : w.im / ‖w‖ ≤ 4 * s * wSig ^ (2 * k) := by
      calc w.im / ‖w‖ ≤ w.im / (‖z‖ / 2) :=
            div_le_div_of_nonneg_left hw0.le (by positivity) hwn
        _ = 4 * s * wSig ^ (2 * k) := by
            rw [hwim, wHeight, hsdef]; field_simp; ring
    have hb0 : 0 ≤ (w.im / ‖w‖) ^ β := Real.rpow_nonneg (div_nonneg hw0.le hwn0.le) _
    have hpow : (w.im / ‖w‖) ^ β ≤ 4 ^ β * s ^ β * (wSig ^ (2 * k)) ^ β := by
      rw [← Real.mul_rpow (by norm_num) hs, ← Real.mul_rpow (by positivity)
        (pow_nonneg wSig_pos.le _)]
      exact Real.rpow_le_rpow (div_nonneg hw0.le hwn0.le) hq (by linarith)
    calc C₄ * onePointC1 ^ (1 - κ / 8) * (w.im / ‖w‖) ^ β
        ≤ max C₄ 0 * onePointC1 ^ (1 - κ / 8) * (w.im / ‖w‖) ^ β := by
          gcongr; exact le_max_left _ _
      _ ≤ max C₄ 0 * onePointC1 ^ (1 - κ / 8) * (4 ^ β * s ^ β * (wSig ^ (2 * k)) ^ β) :=
          mul_le_mul_of_nonneg_left hpow (mul_nonneg (le_max_right _ _) hc1)
      _ = A * s ^ β * (wSig ^ (2 * k)) ^ β := by rw [hAdef]; ring
  have hlayer : ∀ k : ℕ, P (⋃ m ∈ Finset.Icc (-(wM k : ℤ)) (wM k), E k m)
      ≤ ENNReal.ofReal (D * s ^ β * r ^ k) := by
    intro k
    refine (measure_biUnion_finset_le _ _).trans ?_
    refine (Finset.sum_le_sum (hpt k)).trans ?_
    rw [Finset.sum_const, nsmul_eq_mul, ← ENNReal.ofReal_natCast,
      ← ENNReal.ofReal_mul (Nat.cast_nonneg _)]
    apply ENNReal.ofReal_le_ofReal
    have hX : 0 ≤ A * s ^ β * (wSig ^ (2 * k)) ^ β :=
      mul_nonneg (mul_nonneg hA hsβ) (Real.rpow_nonneg (pow_nonneg wSig_pos.le _) _)
    calc ((Finset.Icc (-(wM k : ℤ)) (wM k)).card : ℝ) * (A * s ^ β * (wSig ^ (2 * k)) ^ β)
        ≤ (2 / wDel + 4) * (wSig ^ k)⁻¹ * (A * s ^ β * (wSig ^ (2 * k)) ^ β) :=
          mul_le_mul_of_nonneg_right (card_Icc_wM k) hX
      _ = D * s ^ β * ((wSig ^ k)⁻¹ * (wSig ^ (2 * k)) ^ β) := by rw [hDdef]; ring
      _ = D * s ^ β * r ^ k := by rw [wSig_pow_identity]
  calc P {ω | infDist z (sleTrace κ B ω '' Ici 0) < z.im}
      ≤ P (⋃ k, ⋃ m ∈ Finset.Icc (-(wM k : ℤ)) (wM k), E k m) := measure_mono hcov
    _ ≤ ∑' k, P (⋃ m ∈ Finset.Icc (-(wM k : ℤ)) (wM k), E k m) := measure_iUnion_le _
    _ ≤ ∑' k, ENNReal.ofReal (D * s ^ β * r ^ k) := ENNReal.tsum_le_tsum hlayer
    _ = ENNReal.ofReal (∑' k, D * s ^ β * r ^ k) :=
        (ENNReal.ofReal_tsum_of_nonneg (fun k => mul_nonneg (mul_nonneg hD hsβ) (pow_nonneg hr0 k))
          ((summable_geometric_of_lt_one hr0 hr1).mul_left _)).symm
    _ = ENNReal.ofReal (onePointC5 κ C₄ * s ^ β) := by
        congr 1
        rw [tsum_mul_left, tsum_geometric_of_lt_one hr0 hr1, onePointC5]
        ring

/-- **S1-6: Beffara's one-point estimate** (Beffara 2008, Prop 4, p. 6, upper half; range
`ε ≤ Im z` as in Lawler 2005, Thm 7.9, p. 159, and Lawler–Zhou, Prop 2.3), for `κ ∈ (0,4)`. -/
theorem sleOnePointBound : Blueprint.SLEOnePointBound := by
  intro κ hκ hκ4
  obtain ⟨C3, hC3⟩ := prob_logCR_lt_unif hκ (by linarith)
  set a := 1 - κ / 8 with hadef
  set β := 8 / κ - 1 with hβdef
  have ha : 0 < a := by rw [hadef]; linarith
  have hβ0 : 0 ≤ β := by rw [hβdef, sub_nonneg, le_div_iff₀ hκ]; linarith
  set C4 := C3 / CA.Koebe.koebeCovConst ^ a with hC4def
  set C5 := onePointC5 κ C4 with hC5def
  have hC5 : 0 ≤ C5 := onePointC5_nonneg hκ hκ4.le C4
  have hc1a : 0 < onePointC1 ^ a := Real.rpow_pos_of_pos onePointC1_pos _
  have h8β : 0 < (1 / 8 : ℝ) ^ β := Real.rpow_pos_of_pos (by norm_num) _
  set C6 := 1 / (onePointC1 ^ a * (1 / 8) ^ β) with hC6def
  refine ⟨max (max C4 0) (max (C5 / onePointC1 ^ a) C6), ?_⟩
  intro Ω _ P _ B hB z hz ε hε hεz
  have hy : 0 < z.im := hz
  have hzn : 0 < ‖z‖ := lt_of_lt_of_le hy (Complex.abs_im_le_norm z |>.trans' (le_abs_self _))
  have hX : 0 ≤ (ε / z.im) ^ a := Real.rpow_nonneg (div_nonneg hε.le hy.le) _
  have hY : 0 ≤ (z.im / ‖z‖) ^ β := Real.rpow_nonneg (div_nonneg hy.le hzn.le) _
  have hmax4 : C4 ≤ max (max C4 0) (max (C5 / onePointC1 ^ a) C6) :=
    (le_max_left _ _).trans (le_max_left _ _)
  have hmax5 : C5 / onePointC1 ^ a ≤ max (max C4 0) (max (C5 / onePointC1 ^ a) C6) :=
    (le_max_left _ _).trans (le_max_right _ _)
  have hmax6 : C6 ≤ max (max C4 0) (max (C5 / onePointC1 ^ a) C6) :=
    (le_max_right _ _).trans (le_max_right _ _)
  set Cm := max (max C4 0) (max (C5 / onePointC1 ^ a) C6)
  have h4 := prob_infDist_lt_small hB hκ hκ4.le (hC3 P B hB)
  by_cases hsmall : ε ≤ onePointC1 * z.im
  · refine (h4 z hz ε hε hsmall).trans (ENNReal.ofReal_le_ofReal ?_)
    gcongr
  · rw [not_le] at hsmall
    have hXa : onePointC1 ^ a ≤ (ε / z.im) ^ a := by
      refine Real.rpow_le_rpow onePointC1_pos.le ?_ ha.le
      rw [le_div_iff₀ hy]; exact hsmall.le
    by_cases h8 : 8 * z.im ≤ ‖z‖
    · have h5 := prob_infDist_lt_im hκ hκ4.le h4 z hz h8
      calc P {ω | infDist z (sleTrace κ B ω '' Ici 0) < ε}
          ≤ P {ω | infDist z (sleTrace κ B ω '' Ici 0) < z.im} :=
            measure_mono fun ω h => lt_of_lt_of_le h hεz
        _ ≤ ENNReal.ofReal (C5 * (z.im / ‖z‖) ^ β) := h5
        _ ≤ ENNReal.ofReal (Cm * (ε / z.im) ^ a * (z.im / ‖z‖) ^ β) := by
            apply ENNReal.ofReal_le_ofReal
            calc C5 * (z.im / ‖z‖) ^ β = C5 / onePointC1 ^ a * onePointC1 ^ a * (z.im / ‖z‖) ^ β := by
                  field_simp
              _ ≤ Cm * (ε / z.im) ^ a * (z.im / ‖z‖) ^ β := by
                  gcongr
    · rw [not_le] at h8
      have hYb : (1 / 8 : ℝ) ^ β ≤ (z.im / ‖z‖) ^ β := by
        refine Real.rpow_le_rpow (by norm_num) ?_ hβ0
        rw [le_div_iff₀ hzn]; linarith
      refine prob_le_one.trans ?_
      rw [← ENNReal.ofReal_one]
      apply ENNReal.ofReal_le_ofReal
      calc (1 : ℝ) = C6 * onePointC1 ^ a * (1 / 8) ^ β := by rw [hC6def]; field_simp
        _ ≤ Cm * (ε / z.im) ^ a * (z.im / ‖z‖) ^ β := by
            gcongr

end QuantumZipper.RS
