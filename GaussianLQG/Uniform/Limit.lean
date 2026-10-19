import GaussianLQG.Core.InterfacesS6
import GaussianLQG.LQG.Bridge.Median
import GaussianLQG.Uniform.Limit.Normalization

/-!
# Passage to the limit (blueprint A.7): (★) implies (S6)

Route U steps U16–U17 of `planning/audits/B1-S6-feasibility.md`; blueprint
`appA-uniform.tex` §A.7 as corrected by audit A5 (A5-02). The main result,
`uniformMomentInput_of_lfppUniformMoments`, turns uniform LFPP moment bounds (★)
(`GaussianLQG.LFPPUniformMoments c`, for dyadic scales `ε = 2⁻ⁿ`, `n ≥ 1`, and any positive
deterministic normalization `c γ n`) into the input (S6) (`GaussianLQG.UniformMomentInput D`) for
every family of canonical γ-LQG metrics `D γ`, `γ ∈ (0, 2)`.

## Proof (all on the canonical space `(𝒟'(ℂ), normGFFLaw)`)

Fix `p ≥ 1`; let `γ_p`, `γ_1` be the exponents of (★) at `p` and at `1`, and `C₁` the constant of
(★) at `p = 1`, `K = B̄(0, 2)`, `δ = 1`. Put `B := C₁.toReal + 1`, `s₀ := (4B)⁻¹`, `t₀ := 2B` and
`γ'_p := min(γ_p, γ_1, 1)`. For `γ ∈ (0, γ'_p]` (so `γ < 2`) and `n ≥ 1`:

1. *Normalization* (`UniformLimit.aEps_bounds`, blueprint A.7 item 3): Markov's inequality for
   `A_X(B̄(0,2))` and `I_X(B̄(0,2), 1)⁻¹`, `X = (c γ n)⁻¹ D^{2⁻ⁿ}_h`, gives
   `s₀ c γ n ≤ 𝔞_{2⁻ⁿ} ≤ t₀ c γ n`. Hence `Y^{(n)} := 𝔞_{2⁻ⁿ}⁻¹ D^{2⁻ⁿ}_h` satisfies
   `Y^{(n)} ≤ s₀⁻¹ X^{(n)}` and `X^{(n)} ≤ t₀ Y^{(n)}` pointwise.
2. *Convergence* (blueprint A.7 items 2 and 4): by `IsCanonicalLQGMetric`, `Y^{(n)} → D^γ_h` in
   probability for the local uniform topology, so along a subsequence `Y^{(n_k)} → D^γ_h`
   pointwise almost surely (`UniformLimit.exists_subseq_ae_tendsto`).
3. *Fatou* (blueprint A.7 item 4; `UniformLimit.lintegral_le_of_canonical`):
   `A_{D^γ_h}(K) ≤ liminf_k s₀⁻¹ A_{X^{(n_k)}}(K)` and
   `I_{D^γ_h}(K, δ)⁻¹ ≤ liminf_k t₀ I_{X^{(n_k)}}(K, δ)⁻¹` pointwise
   (`UniformLimit.holderConst_le_liminf`, `UniformLimit.sepInf_inv_le_liminf`), and Fatou's lemma
   gives `E[A_{D^γ}(K)^p] ≤ s₀^{-p} C_{K,δ}` and `E[I_{D^γ}(K, δ)^{-p}] ≤ t₀^p C_{K,δ}`.

The constants depend only on `(p, K, δ)`, not on `γ ∈ (0, γ'_p]`. This argument needs neither the
uniqueness of the median of the limiting crossing distance nor any identification of the
normalization `𝔞_ε` (blueprint A.7, final remark).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal

namespace GaussianLQG

open LQGMetric

namespace UniformLimit

/-! ## Elementary comparisons of normalizations -/

/-- If `s c ≤ a` then `a⁻¹ L ≤ s⁻¹ (c⁻¹ L)` (for `s, c > 0`, `L ≥ 0`). -/
theorem inv_mul_le_inv_mul_inv_mul {a c s L : ℝ} (hs : 0 < s) (hc : 0 < c) (hL : 0 ≤ L)
    (h : s * c ≤ a) : a⁻¹ * L ≤ s⁻¹ * (c⁻¹ * L) := by
  calc a⁻¹ * L ≤ (s * c)⁻¹ * L := mul_le_mul_of_nonneg_right (inv_anti₀ (mul_pos hs hc) h) hL
    _ = s⁻¹ * (c⁻¹ * L) := by rw [mul_inv, mul_assoc]

/-- If `a ≤ t c` then `c⁻¹ L ≤ t (a⁻¹ L)` (for `t, c, a > 0`, `L ≥ 0`). -/
theorem inv_mul_le_mul_inv_mul {a c t L : ℝ} (ht : 0 < t) (hc : 0 < c) (hL : 0 ≤ L) (ha : 0 < a)
    (h : a ≤ t * c) : c⁻¹ * L ≤ t * (a⁻¹ * L) := by
  have h1 : c⁻¹ = t * (t * c)⁻¹ := by field_simp
  calc c⁻¹ * L = t * (t * c)⁻¹ * L := by rw [← h1]
    _ ≤ t * a⁻¹ * L :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (inv_anti₀ ha h) ht.le) hL
    _ = t * (a⁻¹ * L) := mul_assoc _ _ _

/-- The dyadic scales `2^{-(n+1)}` tend to `0⁺`. -/
theorem tendsto_two_inv_pow_succ :
    Tendsto (fun n : ℕ => (2 : ℝ)⁻¹ ^ (n + 1)) atTop (𝓝[>] 0) :=
  tendsto_nhdsWithin_iff.2 ⟨(tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)).comp
    (tendsto_add_atTop_nat 1), Eventually.of_forall fun n => mem_Ioi.2 (by positivity)⟩

/-! ## The passage to the limit at a fixed γ -/

/-- **Blueprint A.7, items 2–5, at a fixed γ.** Let `D_γ` be a canonical γ-LQG metric and `c n > 0`
normalizations with `s₀ c n ≤ 𝔞_{2⁻ⁿ} ≤ t₀ c n` for `n ≥ 1`. If the `p`-th moments of
`A_X(K)` and `I_X(K, δ)⁻¹` for `X = (c n)⁻¹ D^{2⁻ⁿ}_h` are at most `C_K` for every `n ≥ 1`, then
`E[A_{D_γ}(K)^p] ≤ s₀^{-p} C_K` and `E[I_{D_γ}(K, δ)^{-p}] ≤ t₀^p C_K`. -/
theorem lintegral_le_of_canonical {γ : ℝ} {Dγ : DistC → ContMetric}
    (hD : IsCanonicalLQGMetric γ Dγ) {c : ℕ → ℝ} (hc : ∀ n, 0 < c n) {s₀ t₀ : ℝ} (hs₀ : 0 < s₀)
    (ht₀ : 0 < t₀)
    (hr : ∀ n, 1 ≤ n → s₀ * c n ≤ aEps (xiGamma γ) ((2 : ℝ)⁻¹ ^ n) ∧
      aEps (xiGamma γ) ((2 : ℝ)⁻¹ ^ n) ≤ t₀ * c n)
    {p : ℝ} (hp : 0 < p) {K : Set ℂ} {δ : ℝ} {CK : ℝ≥0∞}
    (HK : ∀ n, 1 ≤ n →
      (∫⁻ g, holderConst (fun q => (c n)⁻¹ * lfppDist (xiGamma γ) ((2 : ℝ)⁻¹ ^ n) g q) K ^ p
        ∂normGFFLaw) ≤ CK ∧
      (∫⁻ g, (sepInf (fun q => (c n)⁻¹ * lfppDist (xiGamma γ) ((2 : ℝ)⁻¹ ^ n) g q) K δ)⁻¹ ^ p
        ∂normGFFLaw) ≤ CK) :
    (∫⁻ g, holderConst (Dγ g).1 K ^ p ∂normGFFLaw) ≤ ENNReal.ofReal s₀⁻¹ ^ p * CK ∧
      (∫⁻ g, (sepInf (Dγ g).1 K δ)⁻¹ ^ p ∂normGFFLaw) ≤ ENNReal.ofReal t₀ ^ p * CK := by
  have := isProbabilityMeasure_normGFFLaw
  -- convergence in probability along `ε = 2^{-(n+1)}`, then a.s. along a subsequence
  have hconv := tendstoInProbLU_comp (hD.2 normGFFLaw id
    (isGFFPlusBddCont_of_isWholePlaneGFF isWholePlaneGFF_id_normGFFLaw)) tendsto_two_inv_pow_succ
  obtain ⟨ns, -, hae⟩ := exists_subseq_ae_tendsto hconv
  set ξ := xiGamma γ
  set m : ℕ → ℕ := fun k => ns k + 1
  have hm1 : ∀ k, 1 ≤ m k := fun k => Nat.le_add_left 1 (ns k)
  set ε : ℕ → ℝ := fun k => (2 : ℝ)⁻¹ ^ m k
  have hε0 : ∀ k, ε k ≠ 0 := fun k => pow_ne_zero _ (by norm_num)
  set a : ℕ → ℝ := fun k => aEps ξ (ε k)
  have ha : ∀ k, 0 < a k := fun k =>
    lt_of_lt_of_le (mul_pos hs₀ (hc (m k))) (hr (m k) (hm1 k)).1
  -- `X^{(n_k)}` (normalized by `c`) and `Y^{(n_k)}` (normalized by `𝔞`)
  set X : ℕ → DistC → ℂ × ℂ → ℝ := fun k g q => (c (m k))⁻¹ * lfppDist ξ (ε k) g q
  set Y : ℕ → DistC → ℂ × ℂ → ℝ := fun k g q => (a k)⁻¹ * lfppDist ξ (ε k) g q
  have hYD : ∀ᵐ g ∂normGFFLaw, ∀ q, Tendsto (fun k => Y k g q) atTop (𝓝 ((Dγ g).1 q)) := hae
  have hYX : ∀ k g q, Y k g q ≤ s₀⁻¹ * X k g q := fun k g q =>
    inv_mul_le_inv_mul_inv_mul hs₀ (hc (m k)) ENNReal.toReal_nonneg (hr (m k) (hm1 k)).1
  have hXY : ∀ k g q, X k g q ≤ t₀ * Y k g q := fun k g q =>
    inv_mul_le_mul_inv_mul ht₀ (hc (m k)) ENNReal.toReal_nonneg (ha k) (hr (m k) (hm1 k)).2
  have hAk : ∀ k, ∫⁻ g, holderConst (X k g) K ^ p ∂normGFFLaw ≤ CK := fun k =>
    (HK (m k) (hm1 k)).1
  have hIk : ∀ k, ∫⁻ g, (sepInf (X k g) K δ)⁻¹ ^ p ∂normGFFLaw ≤ CK := fun k =>
    (HK (m k) (hm1 k)).2
  have hpow : Monotone fun x : ℝ≥0∞ => x ^ p := ENNReal.monotone_rpow_of_nonneg hp.le
  constructor
  · -- the Hölder constant
    set u : ℕ → DistC → ℝ≥0∞ := fun k g => ENNReal.ofReal s₀⁻¹ * holderConst (X k g) K with hu
    have hpt : ∀ᵐ g ∂normGFFLaw,
        holderConst (Dγ g).1 K ^ p ≤ liminf (fun k => u k g ^ p) atTop := by
      filter_upwards [hYD] with g hg
      have h1 : holderConst (Dγ g).1 K ≤ liminf (fun k => u k g) atTop :=
        holderConst_le_liminf hg fun k =>
          holderConst_le_ofReal_mul (inv_nonneg.2 hs₀.le) fun z _ w _ => hYX k g (z, w)
      calc holderConst (Dγ g).1 K ^ p ≤ (liminf (fun k => u k g) atTop) ^ p :=
            ENNReal.rpow_le_rpow h1 hp.le
        _ = liminf (fun k => u k g ^ p) atTop :=
            hpow.map_liminf_of_continuousAt _ ENNReal.continuous_rpow_const.continuousAt
    have hmeas : ∀ k, AEMeasurable (fun g => u k g ^ p) normGFFLaw := fun k =>
      ((aemeasurable_holderConst_lfppDist (hε0 k) _ K).const_mul _).pow_const p
    calc ∫⁻ g, holderConst (Dγ g).1 K ^ p ∂normGFFLaw
        ≤ ∫⁻ g, liminf (fun k => u k g ^ p) atTop ∂normGFFLaw := lintegral_mono_ae hpt
      _ ≤ liminf (fun k => ∫⁻ g, u k g ^ p ∂normGFFLaw) atTop := lintegral_liminf_le' hmeas
      _ ≤ ENNReal.ofReal s₀⁻¹ ^ p * CK := by
          refine liminf_le_of_frequently_le' (Frequently.of_forall fun k => ?_)
          simp only [hu, ENNReal.mul_rpow_of_nonneg _ _ hp.le]
          rw [lintegral_const_mul' _ _ (ENNReal.rpow_ne_top_of_nonneg hp.le ENNReal.ofReal_ne_top)]
          gcongr
          exact hAk k
  · -- the inverse separated infimum
    set v : ℕ → DistC → ℝ≥0∞ := fun k g => ENNReal.ofReal t₀ * (sepInf (X k g) K δ)⁻¹ with hv
    have hpt : ∀ᵐ g ∂normGFFLaw,
        (sepInf (Dγ g).1 K δ)⁻¹ ^ p ≤ liminf (fun k => v k g ^ p) atTop := by
      filter_upwards [hYD] with g hg
      have h1 : (sepInf (Dγ g).1 K δ)⁻¹ ≤ liminf (fun k => v k g) atTop :=
        sepInf_inv_le_liminf hg fun k =>
          sepInf_inv_le_ofReal_mul ht₀ fun z _ w _ _ => hXY k g (z, w)
      calc (sepInf (Dγ g).1 K δ)⁻¹ ^ p ≤ (liminf (fun k => v k g) atTop) ^ p :=
            ENNReal.rpow_le_rpow h1 hp.le
        _ = liminf (fun k => v k g ^ p) atTop :=
            hpow.map_liminf_of_continuousAt _ ENNReal.continuous_rpow_const.continuousAt
    have hmeas : ∀ k, AEMeasurable (fun g => v k g ^ p) normGFFLaw := fun k =>
      ((aemeasurable_sepInf_lfppDist (hε0 k) _ K δ).inv.const_mul _).pow_const p
    calc ∫⁻ g, (sepInf (Dγ g).1 K δ)⁻¹ ^ p ∂normGFFLaw
        ≤ ∫⁻ g, liminf (fun k => v k g ^ p) atTop ∂normGFFLaw := lintegral_mono_ae hpt
      _ ≤ liminf (fun k => ∫⁻ g, v k g ^ p ∂normGFFLaw) atTop := lintegral_liminf_le' hmeas
      _ ≤ ENNReal.ofReal t₀ ^ p * CK := by
          refine liminf_le_of_frequently_le' (Frequently.of_forall fun k => ?_)
          simp only [hv, ENNReal.mul_rpow_of_nonneg _ _ hp.le]
          rw [lintegral_const_mul' _ _ (ENNReal.rpow_ne_top_of_nonneg hp.le ENNReal.ofReal_ne_top)]
          gcongr
          exact hIk k

end UniformLimit

open UniformLimit in
/-- **(★) implies (S6)** (Route U steps U16–U17; blueprint A.7 as corrected by audit A5): uniform
LFPP moment bounds at the dyadic scales `2⁻ⁿ`, `n ≥ 1`, normalized by any positive deterministic
constants `c γ n`, give the uniform moment input (S6) for every family of canonical γ-LQG
metrics. -/
theorem uniformMomentInput_of_lfppUniformMoments (c : ℝ → ℕ → ℝ) (hc : ∀ γ n, 0 < c γ n)
    (hstar : LFPPUniformMoments c) (D : ℝ → LQGMetric.DistC → LQGMetric.ContMetric)
    (hD : ∀ γ, 0 < γ → γ < 2 → IsCanonicalLQGMetric γ (D γ)) : UniformMomentInput D := by
  intro p hp
  obtain ⟨γp, hγp, Hp⟩ := hstar p hp
  obtain ⟨γ₁, hγ₁, H₁⟩ := hstar 1 le_rfl
  obtain ⟨C₁, hC₁, H₁'⟩ := H₁ normDisk isCompact_normDisk 1 one_pos
  set B : ℝ := C₁.toReal + 1
  have hB0 : 0 < B := by positivity
  have hp0 : 0 < p := by linarith
  refine ⟨min (min γp γ₁) 1, lt_min (lt_min hγp hγ₁) one_pos, fun K hK δ hδ => ?_⟩
  obtain ⟨CK, hCK, HK⟩ := Hp K hK δ hδ
  refine ⟨ENNReal.ofReal ((4 * B)⁻¹)⁻¹ ^ p * CK + ENNReal.ofReal (2 * B) ^ p * CK, ?_,
    fun γ hγ => ?_⟩
  · exact ENNReal.add_ne_top.2
      ⟨ENNReal.mul_ne_top (ENNReal.rpow_ne_top_of_nonneg hp0.le ENNReal.ofReal_ne_top) hCK,
        ENNReal.mul_ne_top (ENNReal.rpow_ne_top_of_nonneg hp0.le ENNReal.ofReal_ne_top) hCK⟩
  obtain ⟨hγ0, hγle⟩ := hγ
  have hγp' : γ ≤ γp := hγle.trans ((min_le_left _ _).trans (min_le_left _ _))
  have hγ₁' : γ ≤ γ₁ := hγle.trans ((min_le_left _ _).trans (min_le_right _ _))
  have hγ2 : γ < 2 := by
    have := hγle.trans (min_le_right _ _)
    linarith
  have hr : ∀ n, 1 ≤ n → (4 * B)⁻¹ * c γ n ≤ aEps (xiGamma γ) ((2 : ℝ)⁻¹ ^ n) ∧
      aEps (xiGamma γ) ((2 : ℝ)⁻¹ ^ n) ≤ 2 * B * c γ n := by
    intro n hn
    obtain ⟨hA, hI⟩ := H₁' γ ⟨hγ0, hγ₁'⟩ n hn
    simp only [ENNReal.rpow_one] at hA hI
    exact aEps_bounds (by positivity) (hc γ n) hC₁ hA hI
  obtain ⟨h1, h2⟩ := lintegral_le_of_canonical (hD γ hγ0 hγ2) (hc γ) (by positivity)
    (by positivity) hr hp0 (HK γ ⟨hγ0, hγp'⟩)
  exact ⟨h1.trans le_self_add, h2.trans le_add_self⟩

end GaussianLQG
