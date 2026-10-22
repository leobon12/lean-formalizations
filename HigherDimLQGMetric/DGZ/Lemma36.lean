import HigherDimLQGMetric.DGZ.Lemma36Chain
import HigherDimLQGMetric.DGZ.ConcentrationFunctionals
import HigherDimLQGMetric.DGZ.FieldTails
import HigherDimLFPP.Exist.Lemma35

/-!
# DGZ Lemma 3.6, lower half, in tail form (packet L3b3, MA7 D-3.6L)

Source: Ding–Gwynne–Zhuang, arXiv:2310.03996v5 ([2]), Lemma 3.6 (TeX l. 1153–1214), lower half;
planning audit `planning/audits/MA7-ref2-sections-4-6.md`, Details (a) D-3.6L (needed by D-4.8, the
lower half of Prop 4.8).

**Statement (`lemma36_lower`).** Let `d ≥ 2`, `κ` an admissible kernel, `ξ > 0`, and `Q` the DGZ
exponent of `κ` at `ξ` (`log λ_n / n → -(1 - ξQ) log 2` for every realization, where `λ_n` is the
median (lower `1/2`-quantile) of `D_n(0, e₁; B₂(0))`; this is `IsDGZExponent` of MA7 Details (c) §D
with `IsDyadicRealization` unfolded). For every `δ > 0` there is `C > 0` such that for every white
noise with continuous versions `H n` of `h_n = H_{2^{-n},1}`, all `x, y ∈ B̄₂(0)` with
`|x - y|_∞ ≥ 1/2` and all `n`:
`P[D_n(x, y; B₃(0)) < 2^{-(1-ξQ+δ)n}] ≤ C e^{-n/C}`.

**Proof** (MA7 D-3.6L).
1. *Chain* (`Lemma36Chain.lean`): with `L = 2^m`, `9√d < L`, the zigzag `z_0 = 0, …, z_{2L} = L e₁`
   with steps of length `ϱ = |y - x|` and rigid motions `T_i` (`T_i x = z_i`, `T_i y = z_{i+1}`,
   `T_i B₃(0) ⊆ 2^m (-2,2)^d`) give
   `D_n(0, 2^m e₁; 2^m (-2,2)^d) ≤ Σ_i D_n(T_i x, T_i y; T_i B₃(0))`;
   each summand has the law of `D_n(x, y; B₃(0))` (`map_lfppDistOn_sim_eq`, `r = 1`).
2. *Left side*: `D_n(0, 2^m e₁; 2^m (-2,2)^d)` has the law of `2^m D_{(-2,2)^d}(0, e₁)(H')`, `H'` a
   version of `h_{m,n+m}` (`map_lfppDistOn_sim_eq`, `r = 2^m`); on the space of `h_{n+m}` take
   `H' = h_{n+m} - G` with `G` a version of `h_m` (`SupB.sub_isBandVersion`); on
   `{sup_{B̄₂} |G| ≤ M}` (probability `≥ 9/10`, `exists_sup_cbox_gaussian_tail`) we have
   `D(H') ≥ e^{-ξM} D_{n+m}`, and `P[D_{n+m} ≥ λ_{n+m}] ≥ 1/2`. Hence
   `P[D_n(x, y; B₃(0)) ≥ t] ≥ 2/(5J)` with `t = 2^m e^{-ξM} λ_{n+m} / J`, `J = 2L` (union bound over
   the chain) — `prob_chain_ge`.
3. *Exponent*: `λ_N` does not depend on the realization (law transfer); for `N ≥ N₀`,
   `log λ_N ≥ -(1 - ξQ + δ/4) N log 2`.
4. *Concentration* (D-4.6, L3b2): `E log D_n(x,y;B₃) > log t - ξ √(n log 2) q(2/(5J))`, and then
   `P[D_n(x,y;B₃) < 2^{-(1-ξQ+δ)n}] ≤ 2 exp(-u²/(2ξ² n log 2))` with `u ≥ (δ/2) n log 2` for large
   `n`, i.e. `≤ 2 e^{-cn}`, `c = δ² log 2/(8ξ²)`. All constants depend only on `d, κ, ξ, Q, δ`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped ENNReal

namespace HigherDimLQGMetric.DGZ

open HigherDimLFPP
open HigherDimLFPP.DGZ (cbox obox)

variable {d : ℕ}

/-! ### Auxiliary facts -/

/-- The image of an open set under a similarity `z ↦ x₀ + r O z` (`r > 0`) is open. -/
theorem isOpen_image_sim (O : Rd d ≃ₗᵢ[ℝ] Rd d) (x₀ : Rd d) {r : ℝ} (hr : 0 < r)
    {V : Set (Rd d)} (hV : IsOpen V) : IsOpen ((fun z => x₀ + r • O z) '' V) := by
  have e : (fun z => x₀ + r • O z) '' V = (fun w => O.symm (r⁻¹ • (w - x₀))) ⁻¹' V := by
    refine congrFun (Set.image_eq_preimage_of_inverse (f := fun z => x₀ + r • O z)
      (g := fun w => O.symm (r⁻¹ • (w - x₀))) (fun z => ?_) fun w => sim_symm_apply O x₀ hr w) V
    simp only [add_sub_cancel_left, smul_smul, inv_mul_cancel₀ hr.ne', one_smul,
      LinearIsometryEquiv.symm_apply_apply]
  rw [e]
  have hc : Continuous fun w : Rd d => O.symm (r⁻¹ • (w - x₀)) :=
    O.symm.continuous.comp ((continuous_id.sub continuous_const).const_smul r⁻¹)
  exact hV.preimage hc

/-- **Evaluating an identity in law at one coordinate**: if two random functions `F`, `G` (with
measurable coordinates) have the same law on `ι → ℝ`, then `P[F(·) q ∈ S] = P'[G(·) q ∈ S]` for
every measurable `S ⊆ ℝ`. -/
theorem measure_apply_mem_eq_of_map_eq {Ω Ω' ι : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    {P : Measure Ω} {P' : Measure Ω'} {F : Ω → ι → ℝ} {G : Ω' → ι → ℝ}
    (hF : ∀ q, Measurable fun ω => F ω q) (hG : ∀ q, Measurable fun ω => G ω q)
    (h : P.map F = P'.map G) (q : ι) {S : Set ℝ} (hS : MeasurableSet S) :
    P {ω | F ω q ∈ S} = P' {ω | G ω q ∈ S} := by
  have hFm : Measurable F := measurable_pi_iff.2 hF
  have hGm : Measurable G := measurable_pi_iff.2 hG
  have hS' : MeasurableSet {f : ι → ℝ | f q ∈ S} := measurable_pi_apply q hS
  have h1 : (P.map F) {f : ι → ℝ | f q ∈ S} = (P'.map G) {f : ι → ℝ | f q ∈ S} := by rw [h]
  rwa [Measure.map_apply hFm hS', Measure.map_apply hGm hS'] at h1

/-- The events `{s ≤ F(·) q}` of two random functions with the same law have equal probability. -/
theorem measure_le_apply_eq_of_map_eq {Ω Ω' ι : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    {P : Measure Ω} {P' : Measure Ω'} {F : Ω → ι → ℝ} {G : Ω' → ι → ℝ}
    (hF : ∀ q, Measurable fun ω => F ω q) (hG : ∀ q, Measurable fun ω => G ω q)
    (h : P.map F = P'.map G) (q : ι) (s : ℝ) :
    P {ω | s ≤ F ω q} = P' {ω | s ≤ G ω q} :=
  measure_apply_mem_eq_of_map_eq hF hG h q (S := Ici s) measurableSet_Ici

/-- The events `{F(·) q ≤ s}` of two random functions with the same law have equal probability
(the form used with decreasing events, DGZ Lemma 6.5). -/
theorem measure_apply_le_eq_of_map_eq {Ω Ω' ι : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    {P : Measure Ω} {P' : Measure Ω'} {F : Ω → ι → ℝ} {G : Ω' → ι → ℝ}
    (hF : ∀ q, Measurable fun ω => F ω q) (hG : ∀ q, Measurable fun ω => G ω q)
    (h : P.map F = P'.map G) (q : ι) (s : ℝ) :
    P {ω | F ω q ≤ s} = P' {ω | G ω q ≤ s} :=
  measure_apply_mem_eq_of_map_eq hF hG h q (S := Iic s) measurableSet_Iic

/-- `(-2, 2)^d ⊆ B̄₂(0)`. -/
theorem cube_subset_cbox_two : cube d ⊆ cbox (0 : Rd d) 2 := fun z hz =>
  mem_cbox.2 fun i => by
    simp only [PiLp.zero_apply, sub_zero]
    exact (hz i).le

/-- `9 √d < 2^(d+4)`. -/
theorem nine_mul_sqrt_lt_two_pow (d : ℕ) : 9 * √(d : ℝ) < 2 ^ (d + 4) := by
  have h1 : √(d : ℝ) ≤ d + 1 := by
    rw [Real.sqrt_le_left (by positivity)]
    nlinarith
  have h2 : ((d : ℝ) + 1) ≤ 2 ^ d := by
    have := Nat.lt_two_pow_self (n := d)
    exact_mod_cast this
  have h3 : (2 : ℝ) ^ (d + 4) = 16 * 2 ^ d := by rw [pow_add]; norm_num; ring
  rw [h3]
  nlinarith

/-- `|x - y|_∞ ≥ 1/2` implies `|x - y|₂ ≥ 1/2`. -/
theorem half_le_norm_sub_of_exists {x y : Rd d} (h : ∃ i, (1 : ℝ) / 2 ≤ |x i - y i|) :
    1 / 2 ≤ ‖y - x‖ := by
  obtain ⟨i, hi⟩ := h
  calc (1 : ℝ) / 2 ≤ |x i - y i| := hi
    _ = |(y - x) i| := by rw [PiLp.sub_apply, abs_sub_comm]
    _ ≤ ‖y - x‖ := HigherDimLFPP.DGZ.abs_apply_le_norm _ i

/-- `x ≠ y` when `|x - y|_∞ ≥ 1/2`. -/
theorem ne_of_exists_half_le {x y : Rd d} (h : ∃ i, (1 : ℝ) / 2 ≤ |x i - y i|) : x ≠ y := by
  rintro rfl
  obtain ⟨i, hi⟩ := h
  rw [sub_self, abs_zero] at hi
  norm_num at hi

/-! ### The probabilistic core: a lower bound on `P[D_n(x, y; B₃(0)) ≥ t]` -/

section Core

variable {κ : Rd d → ℝ} {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {W : WN d → Ω → ℝ}

/-- **Step 2 of D-3.6L**: let `d ≥ 2`, `9√d < 2^m`, `G` a version of `h_m` with
`P[sup_{B̄₂} |G| > M] ≤ 1/10`, `Hn`, `HN` versions of `h_n`, `h_{n+m}` over the same white noise,
and
`x, y ∈ B̄₂(0)` with `|y - x| ≥ 1/2`. Then, with `J = 2·2^m` and `λ_{n+m}` the median of
`D_{n+m}(0, e₁; B₂(0))`,
`P[D_n(x, y; B₃(0)) ≥ 2^m e^{-|ξ| M} λ_{n+m} / J] ≥ 2/(5J)`. -/
theorem prob_chain_ge (hd : 2 ≤ d) (hκ : IsLFPPKernel κ) (hW : IsWhiteNoise P W) (ξ : ℝ)
    {m : ℕ} (hm : 9 * √(d : ℝ) < 2 ^ m) {M : ℝ} {G : Rd d → Ω → ℝ}
    (hG : IsBandVersion P W κ ((2 : ℝ)⁻¹ ^ m) 1 G)
    (hGM : P {ω | ∃ z ∈ cbox (0 : Rd d) 2, M < |G z ω|} ≤ ENNReal.ofReal (1 / 10))
    {n : ℕ} {Hn HN : Rd d → Ω → ℝ} (hHn : IsBandVersion P W κ ((2 : ℝ)⁻¹ ^ n) 1 Hn)
    (hHN : IsBandVersion P W κ ((2 : ℝ)⁻¹ ^ (n + m)) 1 HN) {x y : Rd d} (hx : x ∈ cbox 0 2)
    (hy : y ∈ cbox 0 2) (hϱ : 1 / 2 ≤ ‖y - x‖) :
    ENNReal.ofReal (2 / (5 * (2 * 2 ^ m))) ≤
      P {ω | (2 : ℝ) ^ m * Real.exp (-(|ξ| * M)) *
          LQGMetric.lowerQuantile (P.map fun ω => lfppDistance d ξ fun z => HN z ω) 2⁻¹ /
            (2 * 2 ^ m) ≤ lfppDistOn ξ (fun z => Hn z ω) (obox 0 3) x y} := by
  have := hW.isProbabilityMeasure
  set J : ℕ := 2 * 2 ^ m with hJ
  have hJpos : (0 : ℝ) < J := by positivity
  have hJcast : ((J : ℕ) : ℝ) = 2 * 2 ^ m := by rw [hJ]; push_cast; ring
  set lam := LQGMetric.lowerQuantile (P.map fun ω => lfppDistance d ξ fun z => HN z ω) 2⁻¹
    with hlam
  set s : ℝ := (2 : ℝ) ^ m * Real.exp (-(|ξ| * M)) * lam with hs
  have h2m : (0 : ℝ) < 2 ^ m := by positivity
  have hpow : ∀ k : ℕ, (0 : ℝ) < (2 : ℝ)⁻¹ ^ k := fun k => by positivity
  -- the version `H' = HN - G` of `h_{m,n+m}`
  have hle1 : (2 : ℝ)⁻¹ ^ (n + m) ≤ (2 : ℝ)⁻¹ ^ m :=
    pow_le_pow_of_le_one (by norm_num) (by norm_num) (Nat.le_add_left m n)
  have hle2 : (2 : ℝ)⁻¹ ^ m ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
  have hH' := HigherDimLFPP.SupB.sub_isBandVersion hκ hW (hpow (n + m)) hle1 hle2 hHN hG
  set H' : Rd d → Ω → ℝ := fun z ω => HN z ω - G z ω with hH'def
  -- (i) `P[λ ≤ D_{n+m}] ≥ 1/2`
  have hDm : Measurable fun ω => lfppDistance d ξ fun z => HN z ω :=
    hHN.measurable_comp (measurable_lfppDistance_continuousMap ξ)
  have hhalf : (2⁻¹ : ℝ≥0∞) ≤ P {ω | lam ≤ lfppDistance d ξ fun z => HN z ω} := by
    have h := LQGMetric.le_measure_Ici_lowerQuantile
      (μ := P.map fun ω => lfppDistance d ξ fun z => HN z ω)
      (ENNReal.inv_pos.2 ENNReal.ofNat_ne_top) (ENNReal.inv_lt_one.2 ENNReal.one_lt_two)
    rw [Measure.map_apply hDm measurableSet_Ici, ENNReal.one_sub_inv_two] at h
    exact h
  -- (ii) on `{sup_{B̄₂} |G| ≤ M}`, `e^{-|ξ|M} λ ≤ D(H')`
  have hincl : {ω | lam ≤ lfppDistance d ξ fun z => HN z ω} ⊆
      {ω | Real.exp (-(|ξ| * M)) * lam ≤ lfppDistOn ξ (fun z => H' z ω) (cube d) 0 (e₁ d)} ∪
        {ω | ∃ z ∈ cbox (0 : Rd d) 2, M < |G z ω|} := by
    intro ω hω
    by_cases hω' : ∃ z ∈ cbox (0 : Rd d) 2, M < |G z ω|
    · exact Or.inr hω'
    · left
      push Not at hω'
      have hcmp := lfppDistOn_le_exp_mul (ζ := ξ) (V := cube d) (x := 0) (y := e₁ d)
        (hHN.continuous ω) (hH'.continuous ω) (M := M) fun z hz => by
          simp only [hH'def, sub_sub_cancel]
          exact hω' z (cube_subset_cbox_two hz)
      simp only [mem_ofPred_eq] at hω ⊢
      rw [lfppDistance_eq_lfppDistOn] at hω
      rw [Real.exp_neg, inv_mul_le_iff₀ (Real.exp_pos _)]
      exact hω.trans hcmp
  have hA : (2⁻¹ : ℝ≥0∞) ≤
      P {ω | Real.exp (-(|ξ| * M)) * lam ≤ lfppDistOn ξ (fun z => H' z ω) (cube d) 0 (e₁ d)} +
        ENNReal.ofReal (1 / 10) :=
    hhalf.trans ((measure_mono hincl).trans ((measure_union_le _ _).trans (add_le_add le_rfl hGM)))
  -- (iii) scaling: `D_n(0, 2^m e₁; 2^m (-2,2)^d)` has the law of `2^m D(H')(0, e₁)`
  have hH'' : IsBandVersion P W κ ((2 : ℝ)⁻¹ ^ n / 2 ^ m) (1 / 2 ^ m) H' :=
    hH'.congr_band (by rw [pow_add, div_eq_mul_inv, ← inv_pow]) (by rw [one_div, inv_pow])
  have hBigOpen : IsOpen ((fun z => (0 : Rd d) + (2 : ℝ) ^ m •
      (LinearIsometryEquiv.refl ℝ (Rd d)) z) '' cube d) :=
    isOpen_image_sim _ _ h2m (isOpen_cube d)
  have hlaw1 := hHn.map_lfppDistOn_sim_eq hH'' hW hW hκ (LinearIsometryEquiv.refl ℝ (Rd d)) 0 h2m
    (hpow n) ξ (isOpen_cube d)
  have hev1 := measure_le_apply_eq_of_map_eq
    (fun q => measurable_lfppDistOn hHn.continuous hHn.measurable hBigOpen ξ _ _)
    (fun q => (measurable_lfppDistOn hH'.continuous hH'.measurable (isOpen_cube d) ξ q.1
      q.2).const_mul _) hlaw1 ((0 : Rd d), e₁ d) s
  simp only at hev1
  have hevA : P {ω | s ≤ (2 : ℝ) ^ m * lfppDistOn ξ (fun z => H' z ω) (cube d) 0 (e₁ d)} =
      P {ω | Real.exp (-(|ξ| * M)) * lam ≤ lfppDistOn ξ (fun z => H' z ω) (cube d) 0 (e₁ d)} := by
    congr 1
    ext ω
    simp only [mem_ofPred_eq, hs, mul_assoc]
    exact mul_le_mul_iff_of_pos_left h2m
  -- (iv) the chain and the union bound
  set Wi : ℕ → Set (Rd d) := fun i =>
    (fun z => chainBase d x y i + (1 : ℝ) • chainRefl d x y i z) '' obox 0 3 with hWi
  have hunion : {ω | s ≤ lfppDistOn ξ (fun z => Hn z ω)
      ((fun z => (0 : Rd d) + (2 : ℝ) ^ m • (LinearIsometryEquiv.refl ℝ (Rd d)) z) '' cube d)
      ((0 : Rd d) + (2 : ℝ) ^ m • (LinearIsometryEquiv.refl ℝ (Rd d)) 0)
      ((0 : Rd d) + (2 : ℝ) ^ m • (LinearIsometryEquiv.refl ℝ (Rd d)) (e₁ d))} ⊆
      ⋃ i ∈ Finset.range J, {ω | s / J ≤ lfppDistOn ξ (fun z => Hn z ω) (Wi i)
        (chainBase d x y i + (1 : ℝ) • chainRefl d x y i x)
        (chainBase d x y i + (1 : ℝ) • chainRefl d x y i y)} := by
    intro ω hω
    by_contra hc
    simp only [mem_iUnion, mem_ofPred_eq, not_exists, not_le] at hc
    have hsum := Finset.sum_lt_sum_of_nonempty (Finset.nonempty_range_iff.2 (by positivity))
      fun i hi => hc i hi
    rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_div_cancel₀ _ hJpos.ne'] at hsum
    have hch := lfppDistOn_le_sum_chain hd ξ (hHn.continuous ω) hx hy hϱ hm
    exact absurd hω (not_le.2 (hch.trans_lt hsum))
  -- each summand has the law of `D_n(x, y; B₃(0))`
  have hHn1 : IsBandVersion P W κ ((2 : ℝ)⁻¹ ^ n / 1) (1 / 1) Hn :=
    hHn.congr_band (div_one _).symm (div_one _).symm
  have hterm : ∀ i, P {ω | s / J ≤ lfppDistOn ξ (fun z => Hn z ω) (Wi i)
      (chainBase d x y i + (1 : ℝ) • chainRefl d x y i x)
      (chainBase d x y i + (1 : ℝ) • chainRefl d x y i y)} =
      P {ω | s / J ≤ lfppDistOn ξ (fun z => Hn z ω) (obox 0 3) x y} := by
    intro i
    have hlaw := hHn.map_lfppDistOn_sim_eq hHn1 hW hW hκ (chainRefl d x y i) (chainBase d x y i)
      one_pos (hpow n) ξ (HigherDimLFPP.DGZ.isOpen_obox 0 3)
    have hev := measure_le_apply_eq_of_map_eq
      (fun q => measurable_lfppDistOn hHn.continuous hHn.measurable
        (isOpen_image_sim _ _ one_pos (HigherDimLFPP.DGZ.isOpen_obox 0 3)) ξ _ _)
      (fun q => (measurable_lfppDistOn hHn.continuous hHn.measurable
        (HigherDimLFPP.DGZ.isOpen_obox 0 3) ξ q.1 q.2).const_mul _) hlaw (x, y) (s / J)
    simp only [one_mul] at hev
    exact hev
  have hB : P {ω | s ≤ (2 : ℝ) ^ m * lfppDistOn ξ (fun z => H' z ω) (cube d) 0 (e₁ d)} ≤
      (J : ℝ≥0∞) * P {ω | s / J ≤ lfppDistOn ξ (fun z => Hn z ω) (obox 0 3) x y} := by
    rw [← hev1]
    refine (measure_mono hunion).trans ((measure_biUnion_finset_le _ _).trans ?_)
    simp only [hterm, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    exact le_rfl
  -- (v) conclusion: `1/2 ≤ J p + 1/10`
  rw [hevA] at hB
  set r := P.real {ω | s / J ≤ lfppDistOn ξ (fun z => Hn z ω) (obox 0 3) x y} with hr
  have hPr : P {ω | s / J ≤ lfppDistOn ξ (fun z => Hn z ω) (obox 0 3) x y} = ENNReal.ofReal r :=
    (ofReal_measureReal (measure_ne_top _ _)).symm
  have hr0 : 0 ≤ r := measureReal_nonneg
  have hJr0 : 0 ≤ (J : ℝ) * r := mul_nonneg (Nat.cast_nonneg _) hr0
  have hkey : (2⁻¹ : ℝ≥0∞) ≤ ENNReal.ofReal (J * r + 1 / 10) := by
    rw [ENNReal.ofReal_add hJr0 (by norm_num),
      ENNReal.ofReal_mul (Nat.cast_nonneg _), ENNReal.ofReal_natCast, ← hPr]
    exact hA.trans (add_le_add_left hB _)
  have hkey' : (1 : ℝ) / 2 ≤ J * r + 1 / 10 := by
    rw [show (2⁻¹ : ℝ≥0∞) = ENNReal.ofReal (1 / 2) by
      rw [one_div, ENNReal.ofReal_inv_of_pos two_pos, ENNReal.ofReal_ofNat]] at hkey
    exact (ENNReal.ofReal_le_ofReal_iff (add_nonneg hJr0 (by norm_num))).1 hkey
  have hrge : 2 / (5 * (2 * 2 ^ m)) ≤ r := by
    rw [← hJcast, div_le_iff₀ (by positivity)]
    nlinarith
  have hset : {ω | s / J ≤ lfppDistOn ξ (fun z => Hn z ω) (obox 0 3) x y} =
      {ω | (2 : ℝ) ^ m * Real.exp (-(|ξ| * M)) * lam / (2 * 2 ^ m) ≤
        lfppDistOn ξ (fun z => Hn z ω) (obox 0 3) x y} := by
    rw [hJcast]
  rw [← hset, hPr]
  exact ENNReal.ofReal_le_ofReal hrge

end Core

/-! ### Final arithmetic -/

/-- For `c > 0` and `n₂ : ℕ` there is `C > 0` with `1 ≤ C e^{-n/C}` for `n < n₂` and
`2 e^{-cn} ≤ C e^{-n/C}` for every `n`. -/
theorem exists_const_exp_bound {c : ℝ} (hc : 0 < c) (n₂ : ℕ) :
    ∃ C > 0, (∀ n : ℕ, n < n₂ → 1 ≤ C * Real.exp (-(n : ℝ) / C)) ∧
      ∀ n : ℕ, 2 * Real.exp (-(c * n)) ≤ C * Real.exp (-(n : ℝ) / C) := by
  set C : ℝ := max (max 2 (1 / c)) (2 * n₂ + 2) with hC
  have hC2 : 2 ≤ C := le_trans (le_max_left _ _) (le_max_left _ _)
  have hCc : 1 / c ≤ C := le_trans (le_max_right _ _) (le_max_left _ _)
  have hCn : 2 * (n₂ : ℝ) + 2 ≤ C := le_max_right _ _
  have hC0 : 0 < C := by linarith
  refine ⟨C, hC0, fun n hn => ?_, fun n => ?_⟩
  · have hn' : (n : ℝ) / C ≤ 1 / 2 := by
      rw [div_le_iff₀ hC0]
      have : (n : ℝ) + 1 ≤ n₂ := by exact_mod_cast hn
      linarith
    have h1 := Real.add_one_le_exp (-((n : ℝ) / C))
    rw [neg_div]
    nlinarith
  · have h1 : 1 / C ≤ c := by
      rw [one_div_le hC0 hc]
      exact hCc
    have h2 : (n : ℝ) / C ≤ c * n := by
      rw [div_eq_mul_one_div, mul_comm c]
      exact mul_le_mul_of_nonneg_left h1 (Nat.cast_nonneg n)
    have h3 : -(c * n) ≤ -(n : ℝ) / C := by
      rw [neg_div]
      exact neg_le_neg h2
    calc 2 * Real.exp (-(c * n)) ≤ C * Real.exp (-(c * n)) :=
          mul_le_mul_of_nonneg_right hC2 (Real.exp_pos _).le
      _ ≤ C * Real.exp (-(n : ℝ) / C) := mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 h3) hC0.le

/-! ### DGZ Lemma 3.6, lower half -/

/-- **DGZ Lemma 3.6, lower half, in tail form** (MA7 D-3.6L; needed by D-4.8). Let `d ≥ 2`, `κ`
an admissible (nonnegative) kernel, `ξ > 0`, and `Q` the DGZ exponent of `κ` at `ξ`, i.e.
`log λ_n / n → -(1 - ξQ) log 2` for every white noise with continuous versions `H n` of
`h_n = H_{2^{-n},1}`, where `λ_n` is the lower `1/2`-quantile of `D_n(0, e₁; (-2,2)^d)` (MA7's
`IsDGZExponent d κ ξ Q`, with `IsDyadicRealization` unfolded). Then for every `δ > 0` there is
`C > 0` such that for every such realization, all `x, y ∈ B̄₂(0)` with `|x - y|_∞ ≥ 1/2` and all
`n`: `P[D_n(x, y; B₃(0)) < 2^{-(1-ξQ+δ)n}] ≤ C e^{-n/C}` (outer measure). -/
theorem lemma36_lower (hd : 2 ≤ d) {κ : Rd d → ℝ} (hκ : IsLFPPKernel κ) {ξ Q : ℝ} (hξ : 0 < ξ)
    (hQ : ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) (W : WN d → Ω → ℝ)
      (H : ℕ → Rd d → Ω → ℝ), IsWhiteNoise P W →
        (∀ n, IsBandVersion P W κ ((2 : ℝ)⁻¹ ^ n) 1 (H n)) →
        Tendsto (fun n : ℕ => Real.log (LQGMetric.lowerQuantile
          (P.map fun ω => lfppDistance d ξ fun z => H n z ω) 2⁻¹) / n) atTop
          (𝓝 (-(1 - ξ * Q) * Real.log 2)))
    {δ : ℝ} (hδ : 0 < δ) :
    ∃ C > 0, ∀ {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {W : WN d → Ω → ℝ}
      {H : ℕ → Rd d → Ω → ℝ}, IsWhiteNoise P W →
        (∀ n, IsBandVersion P W κ ((2 : ℝ)⁻¹ ^ n) 1 (H n)) →
        ∀ x y : Rd d, x ∈ cbox 0 2 → y ∈ cbox 0 2 → (∃ i, (1 : ℝ) / 2 ≤ |x i - y i|) →
        ∀ n : ℕ, P {ω | lfppDistOn ξ (fun z => H n z ω) (obox 0 3) x y <
          (2 : ℝ) ^ (-(1 - ξ * Q + δ) * n)} ≤ ENNReal.ofReal (C * Real.exp (-(n : ℝ) / C)) := by
  have hd0 : 0 < d := by omega
  have hlog2 : 0 < Real.log 2 := Real.log_pos one_lt_two
  have hpow : ∀ k : ℕ, (0 : ℝ) < (2 : ℝ)⁻¹ ^ k := fun k => by positivity
  -- the scale `m` and the chain length `J = 2·2^m`
  set m : ℕ := d + 4 with hmdef
  have hm : 9 * √(d : ℝ) < 2 ^ m := nine_mul_sqrt_lt_two_pow d
  set J : ℝ := 2 * 2 ^ m with hJ
  have hJ1 : 1 ≤ J := by
    have : (1 : ℝ) ≤ 2 ^ m := one_le_pow₀ (by norm_num)
    linarith
  -- the supremum of `h_m` on `B̄₂(0)`: `P[sup |h_m| > M] ≤ 1/10`
  obtain ⟨CG, -, hCG⟩ := exists_sup_cbox_gaussian_tail hκ (R := 2) (by norm_num)
  set v : ℝ := Real.log (1 / (2 : ℝ)⁻¹ ^ m) with hv
  have hvpos : 0 < v := by
    rw [hv, log_one_div_inv_two_pow]
    have : (0 : ℝ) < m := by rw [hmdef]; positivity
    positivity
  set u₀ : ℝ := √(2 * v * Real.log 20) with hu₀
  set M : ℝ := √(2 * d) * v + CG * √v + CG + u₀ with hMdef
  have htail : 2 * Real.exp (-u₀ ^ 2 / (2 * v)) = 1 / 10 := by
    have h20 : 0 < Real.log 20 := Real.log_pos (by norm_num)
    rw [hu₀, Real.sq_sqrt (by positivity),
      show -(2 * v * Real.log 20) / (2 * v) = -Real.log 20 by field_simp, Real.exp_neg,
      Real.exp_log (by norm_num)]
    norm_num
  -- the probability level `p = 2/(5J)` and its quantile constant
  set p : ℝ := 2 / (5 * J) with hp
  have hp0 : 0 < p := by positivity
  have hp1 : p < 1 := by
    rw [hp, div_lt_one (by positivity)]
    linarith
  set q₀ : ℝ := Conc.quantileConst p with hq₀def
  have hq₀ : 0 ≤ q₀ := Real.sqrt_nonneg _
  -- a reference realization and the exponent
  obtain ⟨W₀, hW₀⟩ := exists_isWhiteNoise d
  have hex : ∀ N : ℕ, ∃ H : Rd d → (ℕ → ℝ) → ℝ,
      IsBandVersion LQGDimension.ExistAsm.stdP W₀ κ ((2 : ℝ)⁻¹ ^ N) 1 H :=
    fun N => exists_isBandVersion hκ hW₀ (hpow N) 1
  choose H₀ hH₀ using hex
  set lamStar : ℕ → ℝ := fun N => LQGMetric.lowerQuantile
    (LQGDimension.ExistAsm.stdP.map fun ω => lfppDistance d ξ fun z => H₀ N z ω) 2⁻¹
    with hlamStar
  have hlim := hQ (ℕ → ℝ) LQGDimension.ExistAsm.stdP W₀ H₀ hW₀ hH₀
  obtain ⟨N₀, hN₀⟩ := eventually_atTop.1 (hlim.eventually (lt_mem_nhds
    (show -(1 - ξ * Q) * Real.log 2 - δ / 4 * Real.log 2 < -(1 - ξ * Q) * Real.log 2 by
      nlinarith)))
  have hlogStar : ∀ N : ℕ, N₀ ≤ N → 1 ≤ N →
      -(1 - ξ * Q + δ / 4) * N * Real.log 2 ≤ Real.log (lamStar N) := by
    intro N hN hN1
    have h := hN₀ N hN
    have hNpos : (0 : ℝ) < N := by exact_mod_cast hN1
    rw [lt_div_iff₀ hNpos] at h
    nlinarith
  -- the constants of the final bound
  set K₀ : ℝ := |ξ| * M + Real.log J + (δ / 4 - ξ * Q) * m * Real.log 2 with hK₀
  set c₀ : ℝ := |K₀| with hc₀
  set c₁ : ℝ := |ξ| * q₀ * √(Real.log 2) with hc₁def
  have hc₁ : 0 ≤ c₁ := by positivity
  set n₁ : ℕ := ⌈(4 * (c₀ + c₁) / (δ * Real.log 2)) ^ 2⌉₊ with hn₁
  set c : ℝ := δ ^ 2 * Real.log 2 / (8 * ξ ^ 2) with hcdef
  have hc : 0 < c := by positivity
  obtain ⟨C, hC0, hCsmall, hCbig⟩ := exists_const_exp_bound hc (max (max N₀ n₁) 1)
  refine ⟨C, hC0, ?_⟩
  intro Ω _ P W H hW hH x y hx hy hxy n
  have := hW.isProbabilityMeasure
  -- small `n`
  by_cases hn : n < max (max N₀ n₁) 1
  · exact prob_le_one.trans (ENNReal.one_le_ofReal.2 (hCsmall n hn))
  push Not at hn
  have hnN₀ : N₀ ≤ n := le_trans (le_max_left _ _) (le_trans (le_max_left _ _) hn)
  have hnn₁ : n₁ ≤ n := le_trans (le_max_right _ _) (le_trans (le_max_left _ _) hn)
  have hn1 : 1 ≤ n := le_trans (le_max_right _ _) hn
  -- the realization's median `λ_{n+m}` equals the reference one
  have hlamEq : LQGMetric.lowerQuantile
      (P.map fun ω => lfppDistance d ξ fun z => H (n + m) z ω) 2⁻¹ = lamStar (n + m) :=
    (hH (n + m)).lowerQuantile_lfppDistance_eq (hH₀ (n + m)) hW hW₀ ξ 2⁻¹
  set lam := LQGMetric.lowerQuantile
    (P.map fun ω => lfppDistance d ξ fun z => H (n + m) z ω) 2⁻¹ with hlam
  have hlampos : 0 < lam := Conc.lowerQuantile_map_pos
    ((hH (n + m)).measurable_comp (measurable_lfppDistance_continuousMap ξ)).aemeasurable
    (ae_of_all _ fun ω => lfppDistance_pos hd0 ((hH (n + m)).continuous ω))
    (ENNReal.inv_pos.2 ENNReal.ofNat_ne_top) (ENNReal.inv_lt_one.2 ENNReal.one_lt_two)
  have hloglam : -(1 - ξ * Q + δ / 4) * ((n : ℝ) + m) * Real.log 2 ≤ Real.log lam := by
    rw [hlamEq]
    have h := hlogStar (n + m) (by omega) (by omega)
    push_cast at h
    exact h
  -- a version of `h_m` and the probability lower bound of the chain argument
  obtain ⟨G, hG⟩ := exists_isBandVersion hκ hW (hpow m) 1
  have hGM : P {ω | ∃ z ∈ cbox (0 : Rd d) 2, M < |G z ω|} ≤ ENNReal.ofReal (1 / 10) := by
    have h := hCG hW (hpow m) (pow_le_one₀ (by norm_num) (by norm_num)) hG 0
      (Real.sqrt_nonneg (2 * v * Real.log 20))
    rw [mul_one, ← hv, ← hu₀, ← hMdef, htail] at h
    exact h
  have hxy' := half_le_norm_sub_of_exists hxy
  have hge := prob_chain_ge hd hκ hW ξ hm hG hGM (hH n) (hH (n + m)) hx hy hxy'
  set t : ℝ := (2 : ℝ) ^ m * Real.exp (-(|ξ| * M)) * lam / (2 * 2 ^ m) with htdef
  have ht : 0 < t := by positivity
  -- concentration (D-4.6): `E log D_n(x, y; B₃) > log t - |ξ| √(n log 2) q₀`
  have hab : (2 : ℝ)⁻¹ ^ n < 1 := pow_lt_one₀ (by norm_num) (by norm_num) (by omega)
  have hx3 : x ∈ obox (0 : Rd d) 3 := cbox_subset_obox (by norm_num) hx
  have hy3 : y ∈ obox (0 : Rd d) 3 := cbox_subset_obox (by norm_num) hy
  have hΦ := isSupLipschitzOn_log_lfppDistOn ξ hx3 y (HigherDimLFPP.DGZ.obox_subset_cbox 0 3)
  have hpos : ∀ φ : Rd d → ℝ, Continuous φ → 0 < lfppDistOn ξ φ (obox 0 3) x y := fun φ hφ =>
    lfppDistOn_pos hφ (ne_of_exists_half_le hxy)
      (PcwJoined.of_convex (HigherDimLFPP.DGZ.convex_obox 0 3) hx3 hy3)
  have hconc := log_sub_lt_integral_log_of_le_measure_ge
    (Φ := fun φ => lfppDistOn ξ φ (obox 0 3) x y)
    hκ hW (hpow n) hab (hH n) (isCompact_cbox 0 3) hξ.ne' hΦ hpos ht hp0 hp1 hge
  -- the threshold `T' = 2^{-(1-ξQ+δ)n}` and the margin `u`
  set T' : ℝ := (2 : ℝ) ^ (-(1 - ξ * Q + δ) * n) with hT'
  set u : ℝ := Real.log t - |ξ| * √(Real.log (1 / (2 : ℝ)⁻¹ ^ n)) * q₀ - Real.log T' with hudef
  have hlogT' : Real.log T' = -(1 - ξ * Q + δ) * n * Real.log 2 := Real.log_rpow two_pos _
  have hlogt : Real.log t = m * Real.log 2 - |ξ| * M + Real.log lam - Real.log J := by
    rw [htdef, Real.log_div (by positivity) (by positivity),
      Real.log_mul (by positivity) hlampos.ne', Real.log_mul (by positivity) (Real.exp_pos _).ne',
      Real.log_pow, Real.log_exp, hJ]
    ring
  have hsqrt : √(Real.log (1 / (2 : ℝ)⁻¹ ^ n)) = √(n : ℝ) * √(Real.log 2) := by
    rw [log_one_div_inv_two_pow, Real.sqrt_mul (Nat.cast_nonneg n)]
  have hu_eq : u = m * Real.log 2 - |ξ| * M + Real.log lam - Real.log J - c₁ * √(n : ℝ) +
      (1 - ξ * Q + δ) * n * Real.log 2 := by
    rw [hudef, hlogt, hlogT', hsqrt, hc₁def]
    ring
  -- `c₀ + c₁ √n ≤ (δ/4) n log 2` for `n ≥ n₁`
  have hsqrtn1 : 1 ≤ √(n : ℝ) := by
    rw [show (1 : ℝ) = √1 from Real.sqrt_one.symm]
    exact Real.sqrt_le_sqrt (by exact_mod_cast hn1)
  have hsqrtn : 4 * (c₀ + c₁) / (δ * Real.log 2) ≤ √(n : ℝ) := by
    have h1 : (4 * (c₀ + c₁) / (δ * Real.log 2)) ^ 2 ≤ n :=
      (Nat.le_ceil _).trans (by exact_mod_cast hnn₁)
    have hc₀0 : 0 ≤ c₀ := abs_nonneg _
    calc 4 * (c₀ + c₁) / (δ * Real.log 2) = √((4 * (c₀ + c₁) / (δ * Real.log 2)) ^ 2) :=
          (Real.sqrt_sq (by positivity)).symm
      _ ≤ √(n : ℝ) := Real.sqrt_le_sqrt h1
  have hkey : c₀ + c₁ * √(n : ℝ) ≤ δ / 4 * n * Real.log 2 := by
    have hc₀0 : 0 ≤ c₀ := abs_nonneg _
    have h2 : c₀ + c₁ ≤ δ / 4 * Real.log 2 * √(n : ℝ) := by
      rw [div_le_iff₀ (by positivity)] at hsqrtn
      linarith
    have hnsq : (n : ℝ) = √(n : ℝ) * √(n : ℝ) := (Real.mul_self_sqrt (Nat.cast_nonneg n)).symm
    calc c₀ + c₁ * √(n : ℝ) ≤ c₀ * √(n : ℝ) + c₁ * √(n : ℝ) :=
          add_le_add_left (le_mul_of_one_le_right hc₀0 hsqrtn1) _
      _ = (c₀ + c₁) * √(n : ℝ) := by ring
      _ ≤ (δ / 4 * Real.log 2 * √(n : ℝ)) * √(n : ℝ) :=
          mul_le_mul_of_nonneg_right h2 (Real.sqrt_nonneg _)
      _ = δ / 4 * (√(n : ℝ) * √(n : ℝ)) * Real.log 2 := by ring
      _ = δ / 4 * n * Real.log 2 := by rw [← hnsq]
  -- `u ≥ (δ/2) n log 2`
  have hu : δ / 2 * n * Real.log 2 ≤ u := by
    have hK : K₀ ≤ c₀ := le_abs_self K₀
    have hdecomp : u - δ / 2 * n * Real.log 2 =
        (Real.log lam + (1 - ξ * Q + δ / 4) * ((n : ℝ) + m) * Real.log 2) +
          (δ / 4 * n * Real.log 2 - (c₀ + c₁ * √(n : ℝ))) + (c₀ - K₀) := by
      rw [hu_eq, hK₀]
      ring
    have h1 : 0 ≤ Real.log lam + (1 - ξ * Q + δ / 4) * ((n : ℝ) + m) * Real.log 2 := by
      have := hloglam
      linarith
    linarith
  have hu0 : 0 ≤ u := le_trans (by positivity) hu
  have hle : Real.log T' + u ≤
      ∫ ω, Real.log (lfppDistOn ξ (fun z => H n z ω) (obox 0 3) x y) ∂P := by
    rw [hudef]
    linarith
  -- the tail bound
  have htail2 := measure_lt_le_of_log_add_le_integral
    (Φ := fun φ => lfppDistOn ξ φ (obox 0 3) x y) hκ hW (hpow n) hab.le (hH n)
    (isCompact_cbox 0 3) hΦ hpos hu0 hle
  rw [log_one_div_inv_two_pow] at htail2
  have hexp : -u ^ 2 / (2 * ξ ^ 2 * (n * Real.log 2)) ≤ -(c * n) := by
    rw [neg_div, neg_le_neg_iff, le_div_iff₀ (by positivity)]
    have h1 : (δ / 2 * n * Real.log 2) ^ 2 ≤ u ^ 2 := pow_le_pow_left₀ (by positivity) hu 2
    have h2 : c * n * (2 * ξ ^ 2 * (n * Real.log 2)) = (δ / 2 * n * Real.log 2) ^ 2 := by
      rw [hcdef]
      field_simp
      ring
    linarith
  exact htail2.trans (ENNReal.ofReal_le_ofReal
    ((mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 hexp) (by norm_num)).trans (hCbig n)))

end HigherDimLQGMetric.DGZ
