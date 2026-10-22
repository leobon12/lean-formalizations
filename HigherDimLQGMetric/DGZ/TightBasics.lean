import HigherDimLQGMetric.DGZ.Interfaces
import HigherDimLQGMetric.DGZ.AcrossAroundTools
import HigherDimLQGMetric.DGZ.Sec41Prob
import HigherDimLFPP.Field.Symmetry
import HigherDimLFPP.Field.BandFacts
import HigherDimLFPP.Field.BandVec
import HigherDimLFPP.Exist.Scaling

/-!
# DGZ §6 (packet L5a): basic tools for the tightness section

Source: Ding–Gwynne–Zhuang, arXiv:2310.03996v5 ([2]), §6; planning audit
`planning/audits/MA7-ref2-sections-4-6.md`, §5 row L5a, Details (a) D-6.1–6.3; blueprint Part C
(`blueprint/sections/ref2.tex`, Lemma `r2:lem:xiq`; `blueprint/sections/ref2-tightness.tex`).

* **`xi_mul_sub_sqrt_le_one`** (blueprint Lemma `r2:lem:xiq`, ruling M23 (v)): under `DGZHyp`,
  `ξ (Q - √(2d)) ≤ 1`; hence every Hölder exponent `β < ξ(Q - √(2d))` satisfies `β < 1`. [2] takes
  this from its Lemma 3.7, which is not sealed. Proof: the segment from `0` to `e₁` gives
  `D_n(0, e₁; B₂(0)) ≤ exp(ξ sup_{B̄₃(0)} h_n)`, so `λ_n ≤ 2^{ξ(√(2d) + g/(4ξ)) n}` for large `n`
  (sharp supremum tail, L3b2), while `λ_n ≥ c 2^{-(1 - ξQ + g/4) n}` (L3c2); with
  `g := ξ(Q - √(2d)) - 1 > 0` the two bounds are incompatible.
* Transformed realizations (the *realization-uniformity* device used throughout §6): every
  statement of the form "`∃` constants, `∀` dyadic realization" applies to the shifted and rescaled
  fields `j ↦ h_{j+m}(c + 2^{-m} ·) - h_m(c + 2^{-m} ·)` (`isDyadicRealization_shiftScale`), to
  translates (`isDyadicRealization_translate_tight`) and to realizations with one level replaced by
  another version (`isDyadicRealization_update_tight`); the quantiles `a^{(p)}_N` are the same for
  all realizations (`aQ_eq_of_isDyadicRealization`, L3c2).
* Versions of the empty band `H_{a,a}` vanish almost surely everywhere
  (`ae_forall_eq_zero_of_isBandVersion_self`); this covers the level `n = 0` (`h_0 = H_{1,1}`).
* Uniform tails of `sup_{B̄_R(c)} |h_n|` for each fixed level (`exists_sup_tail_level_tight`).
* Quantile facts: positivity and monotonicity of `p ↦ a^{(p)}_n`, and `P[D_n < a^{(p)}_n] ≤ p`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal

namespace HigherDimLQGMetric

namespace DGZ

open HigherDimLFPP HigherDimLFPP.Perc
open HigherDimLFPP.DGZ (latPt cbox obox)

variable {d : ℕ}

/-! ### Small real-analysis facts -/

/-- `2⁻¹ ^ m > 0`. -/
lemma tb_inv_two_pow_pos (m : ℕ) : (0 : ℝ) < (2 : ℝ)⁻¹ ^ m := by positivity

/-- `(2 : ℝ) ^ (a * k) = (2 ^ a) ^ k` for natural `k`. -/
lemma tb_two_rpow_mul_nat (a : ℝ) (k : ℕ) : (2 : ℝ) ^ (a * (k : ℝ)) = ((2 : ℝ) ^ a) ^ k := by
  rw [Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2), Real.rpow_natCast]

/-- `exp (-x) ≤ 1 / x` for `x > 0`. -/
lemma tb_exp_neg_le_inv {x : ℝ} (hx : 0 < x) : Real.exp (-x) ≤ 1 / x := by
  rw [Real.exp_neg, ← one_div]
  exact one_div_le_one_div_of_le hx (by linarith [Real.add_one_le_exp x])

/-! ### The subcritical window is at most `1` -/

/-- **Blueprint Lemma `r2:lem:xiq`** (ruling M23 (v); replaces [2]'s use of its unsealed Lemma 3.7
at TeX l. 2868): under the DGZ hypotheses, `ξ (Q - √(2d)) ≤ 1`. In particular every
`β ∈ (0, ξ(Q - √(2d)))` satisfies `β < 1`. -/
theorem xi_mul_sub_sqrt_le_one {κ : Rd d → ℝ} {ξ Q : ℝ} (h : DGZHyp d κ ξ Q) :
    ξ * (Q - Real.sqrt (2 * d)) ≤ 1 := by
  by_contra hcon
  push Not at hcon
  have hξ := h.xi_pos
  have hd0 : 0 < d := by have := h.dim; omega
  have hlog2 : 0 < Real.log 2 := Real.log_pos one_lt_two
  set g : ℝ := ξ * (Q - Real.sqrt (2 * d)) - 1 with hg
  have hg0 : 0 < g := by rw [hg]; linarith
  -- the reference realization
  obtain ⟨W₀, hW₀⟩ := exists_isWhiteNoise d
  obtain ⟨H₀, hH₀⟩ := exists_isDyadicRealization h.kernel hW₀
  have hP := hW₀.isProbabilityMeasure
  -- lower bound `c 2^{-(1-ξQ+g/4)N} ≤ λ_N`
  have hhalf0 : (0 : ℝ≥0∞) < 2⁻¹ := ENNReal.inv_pos.2 ENNReal.ofNat_ne_top
  have hhalf1 : (2⁻¹ : ℝ≥0∞) < 1 := ENNReal.inv_lt_one.2 ENNReal.one_lt_two
  obtain ⟨c, hc, hlow⟩ := exists_le_aQ h hhalf0 hhalf1 (ε := g / 4) (by positivity)
  -- upper bound on large scales: `λ_N ≤ 2^{ξ A N}` with `A = √(2d) + g/(4ξ)`
  set A : ℝ := Real.sqrt (2 * d) + g / (4 * ξ) with hA
  have hA0 : Real.sqrt (2 * d) < A := by
    rw [hA]; have : 0 < g / (4 * ξ) := by positivity
    linarith
  obtain ⟨C, hC, hCt⟩ := exists_sup_cbox_tail h.kernel hA0 (R := 3) (by norm_num)
  have hev : ∀ᶠ N : ℕ in atTop, C * Real.exp (-((N : ℝ) * Real.log 2) / C) < 1 / 2 := by
    have ht : Tendsto (fun N : ℕ => C * Real.exp (-((N : ℝ) * Real.log 2) / C)) atTop (𝓝 0) := by
      have h1 : Tendsto (fun N : ℕ => (N : ℝ) * Real.log 2 / C) atTop atTop :=
        (tendsto_natCast_atTop_atTop.atTop_mul_const hlog2).atTop_div_const hC
      have h2 := (Real.tendsto_exp_neg_atTop_nhds_zero.comp h1).const_mul C
      simp only [mul_zero] at h2
      refine h2.congr fun N => ?_
      simp only [Function.comp_apply, neg_div]
    exact ht.eventually (gt_mem_nhds (by norm_num))
  obtain ⟨N₁, hN₁⟩ := eventually_atTop.1 hev
  have hup : ∀ N : ℕ, N₁ ≤ N →
      aQ (LQGDimension.ExistAsm.stdP) H₀ ξ N 2⁻¹ ≤ (2 : ℝ) ^ (ξ * A * N) := by
    intro N hN
    set X := H₀ N with hXdef
    have hX := hH₀.band N
    set T : ℝ := (2 : ℝ) ^ (ξ * A * N) with hT
    have hDm : Measurable fun ω => lfppDistance d ξ (fun z => X z ω) :=
      hX.measurable_lfppDistance ξ
    -- the bad event
    have hbad := hCt hW₀ (a := (2 : ℝ)⁻¹ ^ N) (b := 1) (tb_inv_two_pow_pos N)
      (pow_le_one₀ (by norm_num) (by norm_num)) hX 0
    rw [log_one_div_inv_two_pow, mul_one] at hbad
    -- on the good event, `D_N ≤ T`
    have hsub : {ω | ¬ lfppDistance d ξ (fun z => X z ω) ≤ T} ⊆
        {ω | ∃ z ∈ cbox (0 : Rd d) 3, A * (N * Real.log 2) < |X z ω|} := by
      intro ω hω
      by_contra hgood
      simp only [mem_ofPred_eq, not_exists, not_and, not_lt] at hgood hω
      apply hω
      rw [lfppDistance_eq_lfppDistOn]
      have hle := lfppDistOn_le_exp_mul_norm_of_convex (ξ := ξ) (hX.continuous ω)
        (convex_cube d) (zero_mem_cube d) (e₁_mem_cube d) (M := ξ * (A * (N * Real.log 2)))
        (fun z hz => by
          have hz3 : z ∈ cbox (0 : Rd d) 3 := fun i => by
            simp only [PiLp.zero_apply, sub_zero]
            exact (hz i).le.trans (by norm_num)
          have h1 := hgood z hz3
          have h2 : X z ω ≤ |X z ω| := le_abs_self _
          nlinarith)
      rw [sub_zero, norm_e₁ hd0, mul_one] at hle
      refine hle.trans (le_of_eq ?_)
      rw [hT, Real.rpow_def_of_pos two_pos]
      congr 1
      ring
    have hge : (2⁻¹ : ℝ≥0∞) ≤
        LQGDimension.ExistAsm.stdP {ω | lfppDistance d ξ (fun z => X z ω) ≤ T} := by
      have h1 : (1 : ℝ≥0∞) ≤
          LQGDimension.ExistAsm.stdP {ω | lfppDistance d ξ (fun z => X z ω) ≤ T} +
            LQGDimension.ExistAsm.stdP {ω | ¬ lfppDistance d ξ (fun z => X z ω) ≤ T} := by
        rw [← measure_univ (μ := LQGDimension.ExistAsm.stdP)]
        refine (measure_mono fun ω _ => ?_).trans (measure_union_le _ _)
        by_cases hω : lfppDistance d ξ (fun z => X z ω) ≤ T
        · exact Or.inl hω
        · exact Or.inr hω
      have h2 : LQGDimension.ExistAsm.stdP {ω | ¬ lfppDistance d ξ (fun z => X z ω) ≤ T} ≤
          2⁻¹ := by
        refine (measure_mono hsub).trans (hbad.trans ?_)
        rw [← ENNReal.ofReal_ofNat 2, ← ENNReal.ofReal_inv_of_pos two_pos]
        refine ENNReal.ofReal_le_ofReal ?_
        have := (hN₁ N hN).le
        rw [neg_div] at this ⊢
        linarith
      rw [← ENNReal.one_sub_inv_two]
      exact tsub_le_iff_right.2 (h1.trans (add_le_add le_rfl h2))
    refine (LQGMetric.le_measure_Iic_iff_lowerQuantile_le hhalf0 hhalf1).1 ?_
    rw [Measure.map_apply hDm measurableSet_Iic]
    exact hge
  -- the two bounds are incompatible
  have hb1 : (2 : ℝ) ^ (-(g / 2)) < 1 :=
    Real.rpow_lt_one_of_one_lt_of_neg one_lt_two (by linarith)
  obtain ⟨n₀, hn₀⟩ := exists_pow_lt_of_lt_one hc hb1
  set N := max N₁ n₀ with hN
  have hlowN := hlow (ℕ → ℝ) LQGDimension.ExistAsm.stdP W₀ H₀ hH₀ N
  have hupN := hup N (le_max_left _ _)
  have hcomb : c * (2 : ℝ) ^ (-(1 - ξ * Q + g / 4) * N) ≤ (2 : ℝ) ^ (ξ * A * N) :=
    hlowN.trans hupN
  have hpos : (0 : ℝ) < (2 : ℝ) ^ (-(1 - ξ * Q + g / 4) * N) := Real.rpow_pos_of_pos two_pos _
  have hc' : c ≤ (2 : ℝ) ^ (-(g / 2) * N) := by
    have e : (2 : ℝ) ^ (-(g / 2) * N) =
        (2 : ℝ) ^ (ξ * A * N) / (2 : ℝ) ^ (-(1 - ξ * Q + g / 4) * N) := by
      rw [← Real.rpow_sub two_pos]
      congr 1
      rw [hA, hg]
      field_simp
      ring
    rw [e, le_div_iff₀ hpos]
    exact hcomb
  rw [tb_two_rpow_mul_nat] at hc'
  have hmono : ((2 : ℝ) ^ (-(g / 2))) ^ N ≤ ((2 : ℝ) ^ (-(g / 2))) ^ n₀ :=
    pow_le_pow_of_le_one (Real.rpow_nonneg (by norm_num) _) hb1.le (le_max_right _ _)
  linarith

/-! ### Transformed realizations -/

section Realizations

variable {κ : Rd d → ℝ} {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {W : WN d → Ω → ℝ}
  {H : ℕ → Rd d → Ω → ℝ}

/-- **Shifted and rescaled realization**: for a dyadic realization `(P, W, H)`, a level `m` and a
centre `c`, the fields `j ↦ h_{j+m}(c + 2^{-m} ·) - h_m(c + 2^{-m} ·)` (versions of
`h_{m, j+m}` seen at scale `2^{-m}` around `c`) form a dyadic realization over the white noise
`W ∘ V_T` (`T z = c + 2^{-m} z`; HigherDimLFPP `IsBandVersion.comp_sim`). -/
theorem isDyadicRealization_shiftScale (hκ : IsLFPPKernel κ) (hH : IsDyadicRealization κ P W H)
    (m : ℕ) (c : Rd d) :
    IsDyadicRealization κ P
      (fun f => W (simL2 (LinearIsometryEquiv.refl ℝ (Rd d)) c (tb_inv_two_pow_pos m) f))
      (fun j z ω => H (j + m) (c + (2 : ℝ)⁻¹ ^ m • z) ω - H m (c + (2 : ℝ)⁻¹ ^ m • z) ω) where
  whiteNoise := hH.whiteNoise.comp_simL2 _ c _
  band j := by
    have h1 := isBandVersion_sub_of_realization hκ hH (Nat.le_add_left m j)
    have h2 := h1.comp_sim hκ (LinearIsometryEquiv.refl ℝ (Rd d)) c (tb_inv_two_pow_pos m)
      (tb_inv_two_pow_pos (j + m))
    have e1 : (2 : ℝ)⁻¹ ^ (j + m) / (2 : ℝ)⁻¹ ^ m = (2 : ℝ)⁻¹ ^ j := by
      rw [pow_add, mul_div_assoc, div_self (tb_inv_two_pow_pos m).ne', mul_one]
    have e2 : (2 : ℝ)⁻¹ ^ m / (2 : ℝ)⁻¹ ^ m = 1 := div_self (tb_inv_two_pow_pos m).ne'
    have h3 := h2.congr_band e1 e2
    simpa only [LinearIsometryEquiv.coe_refl, id] using h3

/-- **Translated realization**: `j ↦ h_j(c + ·)` is a dyadic realization over `W ∘ V_T`
(`T z = c + z`). -/
theorem isDyadicRealization_translate_tight (hκ : IsLFPPKernel κ) (hH : IsDyadicRealization κ P W H)
    (c : Rd d) :
    IsDyadicRealization κ P
      (fun f => W (simL2 (LinearIsometryEquiv.refl ℝ (Rd d)) c one_pos f))
      (fun j z ω => H j (c + z) ω) where
  whiteNoise := hH.whiteNoise.comp_simL2 _ c _
  band j := by
    have h2 := (hH.band j).comp_sim hκ (LinearIsometryEquiv.refl ℝ (Rd d)) c one_pos
      (tb_inv_two_pow_pos j)
    have h3 := h2.congr_band (div_one _) (div_one _)
    simpa only [LinearIsometryEquiv.coe_refl, id, one_smul] using h3

/-- **Replacing one level**: if `Y` is a version of `h_N` over the same white noise, then
`Function.update H N Y` is again a dyadic realization. -/
theorem isDyadicRealization_update_tight (hH : IsDyadicRealization κ P W H) (N : ℕ)
    {Y : Rd d → Ω → ℝ} (hY : IsBandVersion P W κ ((2 : ℝ)⁻¹ ^ N) 1 Y) :
    IsDyadicRealization κ P W (Function.update H N Y) where
  whiteNoise := hH.whiteNoise
  band j := by
    by_cases hj : j = N
    · subst hj
      simpa only [Function.update_self] using hY
    · simpa only [Function.update_of_ne hj] using hH.band j

/-- **Every version of a band is part of a dyadic realization**: if `Y` is a version of `h_N` over
a white noise `W`, there is a dyadic realization over `W` whose level `N` is `Y`. -/
theorem exists_isDyadicRealization_eq_tight (hκ : IsLFPPKernel κ) (hW : IsWhiteNoise P W) (N : ℕ)
    {Y : Rd d → Ω → ℝ} (hY : IsBandVersion P W κ ((2 : ℝ)⁻¹ ^ N) 1 Y) :
    ∃ H' : ℕ → Rd d → Ω → ℝ, IsDyadicRealization κ P W H' ∧ H' N = Y := by
  obtain ⟨H₀, hH₀⟩ := exists_isDyadicRealization hκ hW
  exact ⟨Function.update H₀ N Y, isDyadicRealization_update_tight hH₀ N hY,
    Function.update_self _ _ _⟩

end Realizations

/-! ### Versions of the empty band -/

/-- **The zero field is a version of the empty band** `H_{a,a}` (`a > 0`):
`‖k_{a,a,z}‖² = log(a/a) = 0`, so `W(k_{a,a,z}) = 0` almost surely. -/
theorem isBandVersion_zero_self {κ : Rd d → ℝ} (hκ : IsLFPPKernel κ)
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {W : WN d → Ω → ℝ} (hW : IsWhiteNoise P W)
    {a : ℝ} (ha : 0 < a) : IsBandVersion P W κ a a (fun _ _ => (0 : ℝ)) where
  continuous _ := continuous_const
  measurable _ := measurable_const
  ae_eq z := by
    have hn : ‖bandVec κ a a z‖ = 0 := by
      have h := norm_bandVec_sq hκ ha le_rfl z
      rw [div_self ha.ne', Real.log_one] at h
      exact pow_eq_zero_iff two_ne_zero |>.1 h
    have h := hW.ae_eq_zero_of_norm_eq_zero ![bandVec κ a a z] ![1] (by
      simp only [Finset.univ_unique, Fin.default_eq_zero, Fin.isValue, Matrix.cons_val_fin_one,
        one_smul, Finset.sum_singleton, hn])
    filter_upwards [h] with ω hω
    simp only [Finset.univ_unique, Fin.default_eq_zero, Fin.isValue, Matrix.cons_val_fin_one,
      one_mul, Finset.sum_singleton, Pi.zero_apply] at hω
    exact hω.symm

/-- **Versions of `H_{a,a}` vanish**: a continuous version of the empty band `H_{a,a}` (`a > 0`)
is almost surely identically `0` (`‖k_{a,a,z}‖² = log(a/a) = 0`; two versions agree a.s.
everywhere). For `a = 1` this is the level `h_0` of a dyadic realization. -/
theorem ae_forall_eq_zero_of_isBandVersion_self {κ : Rd d → ℝ} (hκ : IsLFPPKernel κ)
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {W : WN d → Ω → ℝ} (hW : IsWhiteNoise P W)
    {a : ℝ} (ha : 0 < a) {X : Rd d → Ω → ℝ} (hX : IsBandVersion P W κ a a X) :
    ∀ᵐ ω ∂P, ∀ z, X z ω = 0 := by
  filter_upwards [hX.ae_eq_forall (isBandVersion_zero_self hκ hW ha)] with ω hω z
  exact hω z

/-! ### Uniform tails of suprema at a fixed level -/

/-- **Fixed-level supremum tails, uniform over realizations and centres**: for each level `n`, each
`R ≥ 0` and `θ > 0` there is `L ≥ 0` with `P[∃ z ∈ B̄_R(c), |X z| > L] ≤ θ` for every version `X`
of `h_n = H_{2^{-n},1}` over any white noise and every centre `c`. (For `n ≥ 1` from the sharp
Gaussian tail of L3b2 with `u = 2 √(v/θ)`, `v = n log 2`, using `e^{-x} ≤ 1/x`; for `n = 0` the
version vanishes a.s.) -/
theorem exists_sup_tail_level_tight {κ : Rd d → ℝ} (hκ : IsLFPPKernel κ) (n : ℕ) {R : ℝ}
    (hR : 0 ≤ R) {θ : ℝ} (hθ : 0 < θ) :
    ∃ L : ℝ, 0 ≤ L ∧ ∀ {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {W : WN d → Ω → ℝ},
      IsWhiteNoise P W → ∀ {X : Rd d → Ω → ℝ}, IsBandVersion P W κ ((2 : ℝ)⁻¹ ^ n) 1 X →
        ∀ c : Rd d, P {ω | ∃ z ∈ cbox c R, L < |X z ω|} ≤ ENNReal.ofReal θ := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · refine ⟨0, le_rfl, fun {Ω} _ {P} {W} hW {X} hX c => ?_⟩
    have hX' : IsBandVersion P W κ 1 1 X := hX.congr_band (pow_zero _) rfl
    have h0 := ae_forall_eq_zero_of_isBandVersion_self hκ hW one_pos hX'
    have hnull : P {ω | ∃ z ∈ cbox c R, 0 < |X z ω|} = 0 := by
      refine measure_mono_null (fun ω hω => ?_) (ae_iff.1 h0)
      obtain ⟨z, -, hz⟩ := hω
      intro hall
      rw [hall z, abs_zero] at hz
      exact lt_irrefl _ hz
    rw [hnull]
    exact zero_le
  · obtain ⟨C, hC0, hC⟩ := exists_sup_cbox_gaussian_tail hκ hR
    have hlog2 : 0 < Real.log 2 := Real.log_pos one_lt_two
    set v : ℝ := n * Real.log 2 with hv
    have hv0 : 0 < v := by rw [hv]; have : (0 : ℝ) < n := by exact_mod_cast hn
                           positivity
    set u : ℝ := 2 * Real.sqrt (v / θ) with hu
    have hu0 : 0 ≤ u := by positivity
    refine ⟨Real.sqrt (2 * d) * v + C * Real.sqrt v + C + u, by positivity,
      fun {Ω} _ {P} {W} hW {X} hX c => ?_⟩
    have h := hC hW (tb_inv_two_pow_pos n) (pow_le_one₀ (by norm_num) (by norm_num)) hX c hu0
    simp only [log_one_div_inv_two_pow, mul_one] at h
    refine h.trans (ENNReal.ofReal_le_ofReal ?_)
    have hu2 : u ^ 2 = 4 * (v / θ) := by
      rw [hu, mul_pow, Real.sq_sqrt (by positivity)]
      norm_num
    have hx : 0 < u ^ 2 / (2 * v) := by rw [hu2]; positivity
    have he := tb_exp_neg_le_inv hx
    rw [neg_div]
    calc 2 * Real.exp (-(u ^ 2 / (2 * v))) ≤ 2 * (1 / (u ^ 2 / (2 * v))) := by linarith
      _ = θ := by rw [hu2]; field_simp; ring

/-! ### Quantiles -/

section Quantiles

variable {κ : Rd d → ℝ} {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {W : WN d → Ω → ℝ}
  {H : ℕ → Rd d → Ω → ℝ}

/-- `a^{(p)}_N > 0` for `p ∈ (0, 1)` (`d ≥ 1`). -/
theorem tight_aQ_pos (hd : 0 < d) (hH : IsDyadicRealization κ P W H) (ξ : ℝ) (N : ℕ) {p : ℝ≥0∞}
    (hp0 : 0 < p) (hp1 : p < 1) : 0 < aQ P H ξ N p := by
  unfold aQ
  rw [(hH.band N).lowerQuantile_lfppDistance_eq_exp hd hH.whiteNoise ξ hp0 hp1]
  exact Real.exp_pos _

/-- `p ↦ a^{(p)}_N` is monotone on `(0, 1)`. -/
theorem tight_aQ_mono (hH : IsDyadicRealization κ P W H) (ξ : ℝ) (N : ℕ) {p p' : ℝ≥0∞} (hp0 : 0 < p)
    (hpp' : p ≤ p') (hp'1 : p' < 1) : aQ P H ξ N p ≤ aQ P H ξ N p' := by
  have := hH.whiteNoise.isProbabilityMeasure
  unfold aQ
  have h1 := (LQGMetric.le_measure_Iic_iff_lowerQuantile_le
    (μ := P.map fun ω => lfppDistance d ξ (fun z => H N z ω)) (hp0.trans_le hpp') hp'1).2 le_rfl
  exact (LQGMetric.le_measure_Iic_iff_lowerQuantile_le hp0 (hpp'.trans_lt hp'1)).1 (hpp'.trans h1)

/-- Below the lower quantile: `P[D_N ≤ x] < p` for `x < a^{(p)}_N`. -/
theorem tight_measure_le_lt_of_lt_aQ (hH : IsDyadicRealization κ P W H) (ξ : ℝ) (N : ℕ) {p : ℝ≥0∞}
    (hp0 : 0 < p) (hp1 : p < 1) {x : ℝ} (hx : x < aQ P H ξ N p) :
    P {ω | lfppDistance d ξ (fun z => H N z ω) ≤ x} < p := by
  have := hH.whiteNoise.isProbabilityMeasure
  have hDm := (hH.band N).measurable_lfppDistance ξ
  have h := LQGMetric.measure_Iic_lt_of_lt_lowerQuantile hp0 hp1 hx
  rwa [Measure.map_apply hDm measurableSet_Iic] at h

/-- At and above the lower quantile: `P[a^{(p)}_N ≤ D_N] ≥ 1 - p`. -/
theorem tight_one_sub_le_measure_aQ_le (hH : IsDyadicRealization κ P W H) (ξ : ℝ) (N : ℕ)
    {p : ℝ≥0∞} (hp0 : 0 < p) (hp1 : p < 1) :
    1 - p ≤ P {ω | aQ P H ξ N p ≤ lfppDistance d ξ (fun z => H N z ω)} := by
  have := hH.whiteNoise.isProbabilityMeasure
  have hDm := (hH.band N).measurable_lfppDistance ξ
  have h := LQGMetric.le_measure_Ici_lowerQuantile
    (μ := P.map fun ω => lfppDistance d ξ (fun z => H N z ω)) hp0 hp1
  rwa [Measure.map_apply hDm measurableSet_Ici] at h

end Quantiles

end DGZ

end HigherDimLQGMetric
