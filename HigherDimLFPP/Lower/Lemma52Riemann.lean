import HigherDimLFPP.Lower.Lemma52
import HigherDimLFPP.Lower.Iteration

/-!
# Lemma 5.2, the Riemann version (HA4 D5 step 6), and the selector of P-L2a's construction

Packet P-L3, target T2 (ruling H6; audit HA4, "Details for later use" D5 step 6, D6 Step 4).

* `lemma52_riemann`: `sup_{N ≥ δ^{-2}} |w^N_{n,d,δ} - w_{n,d,δ}| → 0` as `δ ↓ 0`, where
  `w^N` (`LowerData.wR`) is `w` with `ν_j`, `ν₀` replaced by their left Riemann measures
  `ν_j^N = (KN)⁻¹ Σ_{i,l} δ_{T_i^j(l/N e₁)}`, `ν₀^N = N⁻¹ Σ_l δ_{(l/N) e₁}`.  Proof: on the band
  `(ρq, ρ)` pairings are linear in the measure (`bandVecM_Ioo_sub`); each Riemann measure is
  coupled with its continuum measure within `q/N`, resp. `1/N` (`coupledWithin_riemann_polyM`,
  `coupledWithin_riemann_ref`), both `≤ ρq` for `N ≥ δ^{-2}`; Lemma 3.4(c) (`bandLemma34c`) then
  gives `δ⁻¹ Var ≤ C δ²(q + 1/q)/L`, and the finite maximum (`abs_gEM_gram_sub_le`) gives the
  bound.
* `LowerData.ae_selStat_eq`, `LowerData.integral_iSup_selStat`: for every white noise `W`, the
  selector statistics (5.7) of P-L4's construction (`selStat`, read on the root band
  `z ↦ W(k_{ρq,ρ,z})`) are a.s. the white-noise pairings of the vectors `selVecR`, so
  `E max_j stat_j = w^N`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology
open scoped RealInnerProductSpace ENNReal

namespace HigherDimLFPP.Lower

open LQGDimension (gaussianExpectedMax)

variable {d : ℕ} {κ : Rd d → ℝ}

/-! ## The Riemann measures -/

instance isFiniteMeasure_polyM (K : ℕ) (V : ℕ → Rd d) : IsFiniteMeasure (polyM K V) :=
  ⟨by
    rw [polyM, Upper.segSum_univ V fun _ _ => by positivity]
    exact ENNReal.ofReal_lt_top⟩

instance isFiniteMeasure_refM (N : ℕ) : IsFiniteMeasure (refM d N) := by
  unfold refM
  infer_instance

instance LowerData.isFiniteMeasure_ν (D : LowerData d) (δ : ℝ) (j : Fin (D.J + 1)) :
    IsFiniteMeasure (D.ν δ j) := by
  unfold LowerData.ν
  infer_instance

instance LowerData.isFiniteMeasure_νR (D : LowerData d) (δ : ℝ) (N : ℕ) (j : Fin (D.J + 1)) :
    IsFiniteMeasure (D.νR δ N j) := by
  unfold LowerData.νR
  infer_instance

theorem isProbabilityMeasure_refM (N : ℕ) (hN : 0 < N) : IsProbabilityMeasure (refM d N) := by
  have hN' : (0 : ℝ) < N := by exact_mod_cast hN
  refine isProbabilityMeasure_atomM _ (fun _ _ => by positivity) ?_ _
  rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one_div_cancel hN'.ne']

namespace LowerData

variable (D : LowerData d)

theorem isProbabilityMeasure_νR (δ : ℝ) {N : ℕ} (hN : 0 < N) (j : Fin (D.J + 1)) :
    IsProbabilityMeasure (D.νR δ N j) := by
  have hN' : (0 : ℝ) < N := by exact_mod_cast hN
  have hK := D.K_cast_pos
  refine isProbabilityMeasure_atomM _ (fun _ _ => by positivity) ?_ _
  rw [Finset.sum_const, Finset.card_product, Finset.card_range, Finset.card_range, nsmul_eq_mul]
  push_cast
  field_simp

/-- On the band `(ρq, ρ)` the Riemann and continuum selector vectors differ by the pairings of
`ν_j^N - ν_j` and `ν₀^N - ν₀`. -/
theorem selVecR_sub_selVec (hκ : IsLFPPKernel κ) {δ : ℝ} (hρq : 0 < D.ρ δ * D.q δ) (N : ℕ)
    (j : Fin (D.J + 1)) :
    D.selVecR κ δ N j - D.selVec κ δ j =
      -((Real.sqrt δ)⁻¹ • (bandVecM κ (D.band δ) (D.νR δ N j) (D.ν δ j) -
        bandVecM κ (D.band δ) (refM d N) (Upper.segMeasure 0 (e₁ d)))) := by
  simp only [selVecR, selVec, band]
  rw [bandVecM_Ioo_sub hκ hρq (D.νR δ N j) (refM d N),
    bandVecM_Ioo_sub hκ hρq (D.ν δ j) (Upper.segMeasure 0 (e₁ d)),
    bandVecM_Ioo_sub hκ hρq (D.νR δ N j) (D.ν δ j),
    bandVecM_Ioo_sub hκ hρq (refM d N) (Upper.segMeasure 0 (e₁ d))]
  module

end LowerData

theorem riemann_arith₁ {Cc q q₀ N δ L : ℝ} (hCc : 0 ≤ Cc) (hq : 0 < q) (hN : 0 < N) (hδ : 0 < δ)
    (hL : 0 < L) (hNδ : 1 / N ≤ δ ^ 2) (hqq₀ : q ≤ q₀) :
    Cc * (q / N) ^ 2 / (δ * L * q) / δ ≤ δ ^ 2 * (Cc * q₀ / L) := by
  have e : Cc * (q / N) ^ 2 / (δ * L * q) / δ = Cc * q * (1 / N) ^ 2 / (δ ^ 2 * L) := by
    field_simp
  rw [e]
  have h4 : (1 / N) ^ 2 ≤ (δ ^ 2) ^ 2 := pow_le_pow_left₀ (by positivity) hNδ 2
  have hq₀ : 0 ≤ q₀ := hq.le.trans hqq₀
  calc Cc * q * (1 / N) ^ 2 / (δ ^ 2 * L) ≤ Cc * q₀ * (δ ^ 2) ^ 2 / (δ ^ 2 * L) := by
        gcongr
    _ = δ ^ 2 * (Cc * q₀ / L) := by field_simp

theorem riemann_arith₂ {Cc q K N δ L : ℝ} (hCc : 0 ≤ Cc) (hK : 0 < K) (hq : 1 / K ≤ q)
    (hN : 0 < N) (hδ : 0 < δ) (hL : 0 < L) (hNδ : 1 / N ≤ δ ^ 2) :
    Cc * (1 / N) ^ 2 / (δ * L * q) / δ ≤ δ ^ 2 * (Cc * K / L) := by
  have hq0 : 0 < q := lt_of_lt_of_le (by positivity) hq
  have e : Cc * (1 / N) ^ 2 / (δ * L * q) / δ = Cc * (1 / N) ^ 2 / (δ ^ 2 * L * q) := by
    field_simp
  rw [e]
  have h4 : (1 / N) ^ 2 ≤ (δ ^ 2) ^ 2 := pow_le_pow_left₀ (by positivity) hNδ 2
  have hqK : 1 ≤ K * q := by rw [div_le_iff₀ hK] at hq; linarith
  calc Cc * (1 / N) ^ 2 / (δ ^ 2 * L * q) ≤ Cc * (δ ^ 2) ^ 2 / (δ ^ 2 * L * q) := by gcongr
    _ = δ ^ 2 * (Cc * (1 / (L * q))) := by field_simp
    _ ≤ δ ^ 2 * (Cc * (K / L)) := by
        have h1 : 1 / (L * q) ≤ K / L := by
          rw [div_le_div_iff₀ (by positivity) hL]
          nlinarith
        gcongr
    _ = δ ^ 2 * (Cc * K / L) := by ring

theorem sqrt_sq_mul {δ : ℝ} (hδ : 0 ≤ δ) (X : ℝ) :
    Real.sqrt (δ ^ 2 * X) = δ * Real.sqrt X := by
  rw [Real.sqrt_mul (sq_nonneg δ), Real.sqrt_sq hδ]

/-- **Lemma 5.2, the Riemann version** (HA4 D5, step 6): for every `C` there is `N₀` such that
for all data `D` with the standing hypotheses and `n ≥ N₀`,
`sup_{N ≥ δ^{-2}} |w^N_{n,d,δ} - w_{n,d,δ}| → 0` as `δ ↓ 0`. -/
theorem lemma52_riemann (hd : 2 ≤ d) (hκ : IsLFPPKernel κ) (C : ℝ) :
    ∃ N₀ : ℕ, ∀ D : LowerData d, D.Hyp C → N₀ ≤ D.n →
      ∀ ε > 0, ∀ᶠ δ in 𝓝[>] (0 : ℝ), ∀ N : ℕ, δ ^ (-2 : ℤ) ≤ (N : ℝ) →
        |D.wR κ δ N - D.w κ δ| ≤ ε := by
  obtain ⟨Cc, hCc0, hCc⟩ := bandLemma34c hκ 4
  refine ⟨⌈2 * C + 4⌉₊, fun D hD hN ε hε => ?_⟩
  have hd0 : 0 < d := by omega
  have hC := hD.C_nonneg
  have he := hD.e_nonneg
  have hx : 2 * C + 4 ≤ (D.n : ℝ) + 2 := by
    have h1 := Nat.le_ceil (2 * C + 4)
    have h2 : (⌈2 * C + 4⌉₊ : ℝ) ≤ D.n := by exact_mod_cast hN
    linarith
  have hK51 := hD.sqrt_le_K hx
  have hspec := fun j => ampl_spec hd0 hD.one_le_g (hD.mem j) (hD.energy_le j) hD.v_norm hK51
  choose hamp hδ₁ using hspec
  choose δ₁ hδ₁pos hδ₁spec using hδ₁
  have hK := D.K_cast_pos
  have hL := D.L_pos
  set S₂ := Real.sqrt (2 * Real.log (2 * ((D.J : ℝ) + 1))) with hS₂
  set Λ : ℝ := (Real.sqrt (Cc * (2 / D.K) / D.L) + Real.sqrt (Cc * D.K / D.L)) * S₂ with hΛ
  have hΛ0 : 0 ≤ Λ := by positivity
  -- eventual smallness
  have ev1 : ∀ᶠ δ in 𝓝[>] (0 : ℝ), ∀ j, δ ∈ Ioo 0 (δ₁ j) :=
    eventually_all.2 fun j => Ioo_mem_nhdsGT (hδ₁pos j)
  have ev2 : ∀ᶠ δ in 𝓝[>] (0 : ℝ), √2 * incrConst D.n D.e * δ < 1 / 2 :=
    (tendsto_zero_of_continuous (continuous_const.mul continuous_id) (by simp)).eventually
      (gt_mem_nhds (by norm_num))
  have ev3 : ∀ᶠ δ in 𝓝[>] (0 : ℝ), δ ^ 2 * D.E₀ < 1 :=
    (tendsto_zero_of_continuous ((continuous_pow 2).mul continuous_const) (by simp)).eventually
      (gt_mem_nhds (by norm_num))
  have ev4 : ∀ᶠ δ in 𝓝[>] (0 : ℝ), δ * Λ < ε :=
    (tendsto_zero_of_continuous (continuous_id.mul continuous_const) (by simp)).eventually
      (gt_mem_nhds hε)
  have ev5 : ∀ᶠ δ in 𝓝[>] (0 : ℝ), δ < 1 / (D.K : ℝ) * D.L ∧ δ < 1 := by
    have hpos : 0 < min (1 / (D.K : ℝ) * D.L) 1 := lt_min (mul_pos (div_pos one_pos hK) hL) one_pos
    filter_upwards [Ioo_mem_nhdsGT hpos] with δ hδ
    exact ⟨lt_of_lt_of_le hδ.2 (min_le_left _ _), lt_of_lt_of_le hδ.2 (min_le_right _ _)⟩
  filter_upwards [ev1, ev2, ev3, ev4, ev5, self_mem_nhdsWithin] with δ h1 h2 h3 h4 h5 hδ N hNδ
  have hδ' : (0 : ℝ) < δ := hδ
  have hE : ∀ j, EqualEdgeData D.K δ (D.q δ) D.E₀ (√D.e + 1) (√2 * incrConst D.n D.e)
      (D.vert δ j) := fun j => ((hδ₁spec j) δ (h1 j)).2
  have hq0 : 0 < D.q δ := D.q_pos he δ
  have hqK : 1 / (D.K : ℝ) ≤ D.q δ := D.one_div_K_le_q he δ
  have hq2 : D.q δ ≤ 2 / D.K := D.q_le_two_div_K h3.le
  have hq1 : D.q δ < 1 := D.q_lt_one hD.one_le_n hD.one_le_g h3.le
  have hρ : 0 < D.ρ δ := mul_pos hδ' hL
  have hρq : 0 < D.ρ δ * D.q δ := mul_pos hρ hq0
  -- `N ≥ δ^{-2}`
  have hNpos : (0 : ℝ) < N := lt_of_lt_of_le (zpow_pos hδ' _) hNδ
  have hN : 0 < N := by exact_mod_cast hNpos
  have hinvN : 1 / (N : ℝ) ≤ δ ^ 2 := by
    rw [div_le_iff₀ hNpos]
    have : δ ^ (-2 : ℤ) * δ ^ 2 = 1 := by
      rw [zpow_neg, zpow_two, ← pow_two, inv_mul_cancel₀ (pow_ne_zero 2 hδ'.ne')]
    nlinarith [pow_pos hδ' 2]
  -- the two Riemann couplings
  have hpν : ∀ j, IsProbabilityMeasure (D.ν δ j) := fun j => isProbabilityMeasure_polyM D.K_pos _
  have hgν : ∀ j, GrowthBound (D.ν δ j) 4 1 := fun j =>
    growthBound_polyM hd0 D.K_pos hqK fun i hi => half_le_horiz_edge hd0 (hE j) hq0 h2.le hi
  have hgν₀ : GrowthBound (Upper.segMeasure 0 (e₁ d)) 4 1 := by
    rw [← graphMeasure_zero (d := d) δ]
    exact (graphMeasure_growthBound hd0 measurable_const).mono_const one_pos (by norm_num)
  have hpR : ∀ j, IsProbabilityMeasure (D.νR δ N j) := fun j => D.isProbabilityMeasure_νR δ hN j
  have hpR₀ := isProbabilityMeasure_refM (d := d) N hN
  have hL1 : (1 : ℝ) ≤ D.L := one_le_pow₀ (by have := Nat.cast_nonneg (α := ℝ) D.n; linarith)
  have hδ2ρ : δ ^ 2 ≤ D.ρ δ := by
    simp only [LowerData.ρ]
    nlinarith
  have hδ2ρq : δ ^ 2 ≤ D.ρ δ * D.q δ := by
    have h51 : δ ≤ D.L * D.q δ := by
      have := h5.1
      calc δ ≤ 1 / (D.K : ℝ) * D.L := this.le
        _ ≤ D.q δ * D.L := mul_le_mul_of_nonneg_right hqK hL.le
        _ = D.L * D.q δ := mul_comm _ _
    simp only [LowerData.ρ]
    nlinarith
  have hu1 : D.q δ / N ≤ D.ρ δ * D.q δ := by
    rw [div_eq_mul_one_div, mul_comm (D.ρ δ)]
    exact mul_le_mul_of_nonneg_left (hinvN.trans hδ2ρ) hq0.le
  have hu2 : 1 / (N : ℝ) ≤ D.ρ δ * D.q δ := hinvN.trans hδ2ρq
  have hS : D.band δ ⊆ Ioi (D.ρ δ * D.q δ) := Ioo_subset_Ioi_self
  have hb1 : ∀ j, scaleCov κ (D.band δ) (D.νR δ N j) (D.ν δ j) (D.νR δ N j) (D.ν δ j) ≤
      Cc * (D.q δ / N) ^ 2 / (D.ρ δ * D.q δ) := fun j =>
    (hCc (D.ρ δ * D.q δ) (D.q δ / N) (D.band δ) hρq (by positivity) hu1 measurableSet_Ioo hS
      (D.νR δ N j) (D.ν δ j) (hgν j)
      (coupledWithin_riemann_polyM hd0 hN hq0 (hE j).edge_len)).2
  have hb2 : scaleCov κ (D.band δ) (refM d N) (Upper.segMeasure 0 (e₁ d)) (refM d N)
      (Upper.segMeasure 0 (e₁ d)) ≤ Cc * (1 / (N : ℝ)) ^ 2 / (D.ρ δ * D.q δ) :=
    (hCc (D.ρ δ * D.q δ) (1 / N) (D.band δ) hρq (by positivity) hu2 measurableSet_Ioo hS
      (refM d N) (Upper.segMeasure 0 (e₁ d)) hgν₀ (coupledWithin_riemann_ref hd0 hN)).2
  have hn1 : ∀ j, ‖(Real.sqrt δ)⁻¹ • bandVecM κ (D.band δ) (D.νR δ N j) (D.ν δ j)‖ ≤
      δ * Real.sqrt (Cc * (2 / D.K) / D.L) := by
    intro j
    refine (norm_inv_sqrt_smul_bandVecM_le hδ' (hb1 j)).trans ?_
    rw [← sqrt_sq_mul hδ'.le]
    refine Real.sqrt_le_sqrt ?_
    have := riemann_arith₁ (q₀ := 2 / D.K) hCc0 hq0 hNpos hδ' hL hinvN hq2
    simp only [LowerData.ρ] at this ⊢
    rw [mul_div_assoc] at this
    rwa [mul_div_assoc]
  have hn2 : ‖(Real.sqrt δ)⁻¹ • bandVecM κ (D.band δ) (refM d N) (Upper.segMeasure 0 (e₁ d))‖ ≤
      δ * Real.sqrt (Cc * D.K / D.L) := by
    refine (norm_inv_sqrt_smul_bandVecM_le hδ' hb2).trans ?_
    rw [← sqrt_sq_mul hδ'.le]
    refine Real.sqrt_le_sqrt ?_
    have := riemann_arith₂ hCc0 hK hqK hNpos hδ' hL hinvN
    simp only [LowerData.ρ] at this ⊢
    exact this
  have hdiff : ∀ j, ‖D.selVecR κ δ N j - D.selVec κ δ j‖ ≤
      δ * (Real.sqrt (Cc * (2 / D.K) / D.L) + Real.sqrt (Cc * D.K / D.L)) := by
    intro j
    rw [D.selVecR_sub_selVec hκ hρq N j, norm_neg, smul_sub]
    refine (norm_sub_le _ _).trans ?_
    rw [mul_add]
    exact add_le_add (hn1 j) hn2
  have h := abs_gEM_gram_sub_le (D.selVecR κ δ N) (D.selVec κ δ) (by positivity) hdiff
  rw [Fintype.card_fin] at h
  have hw : |D.wR κ δ N - D.w κ δ| ≤ δ * Λ := by
    refine h.trans (le_of_eq ?_)
    rw [hΛ, hS₂]
    push_cast
    ring_nf
  exact hw.trans h4.le

/-! ## The selector statistics as white-noise pairings -/

section WN

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {W : WN d → Ω → ℝ}

/-- a.s. linearity of the white noise over a finite index set. -/
theorem ae_W_finsetSum (hW : IsWhiteNoise P W) {α : Type*} (A : Finset α) (a : α → ℝ)
    (f : α → WN d) :
    W (∑ x ∈ A, a x • f x) =ᵐ[P] fun ω => ∑ x ∈ A, a x * W (f x) ω := by
  have h := hW.sum_smul_ae (ι := A) (fun x => f x) (fun x => a x)
  rw [Finset.sum_coe_sort A (fun x => a x • f x)] at h
  filter_upwards [h] with ω hω
  rw [hω]
  exact Finset.sum_coe_sort A (fun x => a x * W (f x) ω)

/-- The white-noise pairing of an atomic measure on a band `(a, b)`, `a > 0`. -/
theorem ae_W_atomM (hκ : IsLFPPKernel κ) (hW : IsWhiteNoise P W) {a b : ℝ} (ha : 0 < a)
    {α : Type*} (A : Finset α) {c : α → ℝ} (hc : ∀ x ∈ A, 0 ≤ c x) (p : α → Rd d) :
    W (bandVecM κ (Ioo a b) (atomM A c p) 0) =ᵐ[P]
      fun ω => ∑ x ∈ A, c x * W (bandVec κ a b (p x)) ω := by
  rw [bandVecM_atomM hκ ha A hc p]
  exact ae_W_finsetSum hW A c _

namespace LowerData

variable (D : LowerData d)

theorem rpow_neg_half {δ : ℝ} (hδ : 0 ≤ δ) : δ ^ (-(1 / 2 : ℝ)) = (Real.sqrt δ)⁻¹ := by
  rw [Real.rpow_neg hδ, Real.sqrt_eq_rpow]

/-- **The selector statistics are white-noise pairings**: for every white noise `W`, a.s. for
all `j`, the selector statistic (5.7) of P-L4's construction, read on the root band
`z ↦ W(k_{ρq,ρ,z})`, is `W(selVecR j)`. -/
theorem ae_selStat_eq (hκ : IsLFPPKernel κ) (hW : IsWhiteNoise P W) {δ : ℝ} (hδ : 0 < δ)
    (hρq : 0 < D.ρ δ * D.q δ) (N : ℕ) :
    ∀ᵐ ω ∂P, ∀ j, selStat D.K N δ (D.q δ) (D.vert δ) j
        (fun z => W (bandVec κ (D.ρ δ * D.q δ) (D.ρ δ) z) ω) = W (D.selVecR κ δ N j) ω := by
  rw [ae_all_iff]
  intro j
  have hK := D.K_cast_pos
  set c : ℝ := (Real.sqrt δ)⁻¹ with hc
  have e1 : W (bandVecM κ (Ioo (D.ρ δ * D.q δ) (D.ρ δ)) (D.νR δ N j) 0) =ᵐ[P]
      fun ω => ∑ x ∈ Finset.range D.K ×ˢ Finset.range N, 1 / ((D.K : ℝ) * N) *
        W (bandVec κ (D.ρ δ * D.q δ) (D.ρ δ)
          ((edgeSim (D.q δ) (D.vert δ j) x.1).app (refPt N x.2))) ω :=
    ae_W_atomM (P := P) hκ hW (b := D.ρ δ) hρq
      (Finset.range D.K ×ˢ Finset.range N) (c := fun _ => 1 / ((D.K : ℝ) * N))
      (fun _ _ => by positivity) (fun x => (edgeSim (D.q δ) (D.vert δ j) x.1).app (refPt N x.2))
  have e2 : W (bandVecM κ (Ioo (D.ρ δ * D.q δ) (D.ρ δ)) (refM d N) 0) =ᵐ[P]
      fun ω => ∑ l ∈ Finset.range N, 1 / (N : ℝ) *
        W (bandVec κ (D.ρ δ * D.q δ) (D.ρ δ) (refPt N l)) ω :=
    ae_W_atomM (P := P) hκ hW (b := D.ρ δ) hρq (Finset.range N)
      (c := fun _ => 1 / (N : ℝ)) (fun _ _ => by positivity) (refPt N)
  have e3 := hW.smul_ae (-c) (bandVecM κ (Ioo (D.ρ δ * D.q δ) (D.ρ δ)) (D.νR δ N j) 0 -
    bandVecM κ (Ioo (D.ρ δ * D.q δ) (D.ρ δ)) (refM d N) 0)
  have e4 := hW.sub_ae (bandVecM κ (Ioo (D.ρ δ * D.q δ) (D.ρ δ)) (D.νR δ N j) 0)
    (bandVecM κ (Ioo (D.ρ δ * D.q δ) (D.ρ δ)) (refM d N) 0)
  have hsel : D.selVecR κ δ N j = -c • (bandVecM κ (Ioo (D.ρ δ * D.q δ) (D.ρ δ)) (D.νR δ N j) 0 -
      bandVecM κ (Ioo (D.ρ δ * D.q δ) (D.ρ δ)) (refM d N) 0) := by
    rw [selVecR, band, bandVecM_Ioo_sub hκ hρq, neg_smul]
  filter_upwards [e1, e2, e3, e4] with ω h1 h2 h3 h4
  rw [hsel, h3, h4, h1, h2, selStat, rpow_neg_half hδ.le, Finset.sum_product, Finset.mul_sum,
    Finset.mul_sum]
  congr 1
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.mul_sum]

/-- **`E max_j stat_j = w^N`** for every white noise. -/
theorem integral_iSup_selStat (hκ : IsLFPPKernel κ) (hW : IsWhiteNoise P W) {δ : ℝ}
    (hδ : 0 < δ) (hρq : 0 < D.ρ δ * D.q δ) (N : ℕ) :
    ∫ ω, (⨆ j, selStat D.K N δ (D.q δ) (D.vert δ) j
        (fun z => W (bandVec κ (D.ρ δ * D.q δ) (D.ρ δ) z) ω)) ∂P = D.wR κ δ N := by
  rw [wR, ← integral_iSup_W_eq_gEM hW]
  refine integral_congr_ae ?_
  filter_upwards [D.ae_selStat_eq hκ hW hδ hρq N] with ω hω
  simp only [hω]

end LowerData

end WN

end HigherDimLFPP.Lower
