import GaussianLQG.Uniform.Holder.Level

/-!
# U12: the `q`-th moment of the Hölder constant for one noise, one `ξ` and one `n`

Phase B, packet PB-U12 (ledger U12; Finding `fd:U12`). Given the inputs of the ledger as explicit
bounds (the exponential moment `hexp` of the coarse field, the U10 moments `hmom` of
`L_m(R_{2,1})`, the U11 scale relations (a) `hsc` and (c) `hlow`), with constants that do not depend
on the noise, on `ξ` or on `n`:

* `lintegral_holder_small` (`n ≤ 1`): straight segments only (`holderConst_le_straight`);
* `lintegral_holder_large` (`n ≥ 2`): the pathwise majorant of `holderConst_le_chain` at `m = n − 1`
  with the decoupled level bounds (`ae_len21_le_Xdec`, a.s.), `x^q ≤ 1 + x^p` for `q ≤ p`,
  Minkowski (`lpN_sum_le`), the level bounds `level_bound`, the finest link `link_bound`, and the
  dyadic series (`sum_exp_sqrt_le`). No measurability of the Hölder constant itself is needed: it is
  bounded pointwise (a.s.) by a measurable majorant.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

namespace GaussianLQG
namespace Uniform
namespace Holder

open LQGMetric LQGMetric.DDDF LQGMetric.WhiteNoise

/-- the bound of the dyadic series `Σ_k e^{-(L/4) k + D √k}`, `L = log 2`, `D = 2 L K₀ / p + C_s` -/
def holderSb (p : ℕ) (K₀ Cs : ℝ) : ℝ :=
  Real.exp ((2 * Real.log 2 * K₀ / p + Cs) ^ 2 / (2 * (Real.log 2 / 4))) /
    (1 - Real.exp (-(Real.log 2 / 4 / 2)))

lemma holderSb_nonneg (p : ℕ) (K₀ Cs : ℝ) : 0 ≤ holderSb p K₀ Cs := by
  have hL : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have h1 : Real.exp (-(Real.log 2 / 4 / 2)) < 1 := Real.exp_lt_one_iff.2 (by linarith)
  unfold holderSb
  exact div_nonneg (Real.exp_pos _).le (by linarith)

/-- the bound of `‖λ_n^{-1} G‖_p`: finest link, shifted squares and halves -/
def holderB (a : ℝ) (p : ℕ) (K₀ C₁ Cs : ℝ) : ℝ :=
  (a * Real.exp (p * (Cs / 32 + Real.log 2))) ^ ((p : ℝ)⁻¹) * holderSb p K₀ Cs +
    2 * ((4 * a ^ 2 * C₁ * Cs ^ p) ^ ((p : ℝ)⁻¹) * holderSb p K₀ Cs)

lemma holderB_nonneg {a C₁ Cs : ℝ} (ha : 0 ≤ a) (hC₁ : 0 ≤ C₁) (hCs : 0 ≤ Cs) (p : ℕ)
    (K₀ : ℝ) : 0 ≤ holderB a p K₀ C₁ Cs := by
  have := holderSb_nonneg p K₀ Cs
  unfold holderB
  have h1 : 0 ≤ (a * Real.exp (p * (Cs / 32 + Real.log 2))) ^ ((p : ℝ)⁻¹) :=
    Real.rpow_nonneg (by positivity) _
  have h2 : 0 ≤ (4 * a ^ 2 * C₁ * Cs ^ p) ^ ((p : ℝ)⁻¹) := Real.rpow_nonneg (by positivity) _
  positivity

/-- `x^q ≤ 1 + x^p` for `0 ≤ q ≤ p` -/
lemma rpow_le_one_add_pow {x : ℝ≥0∞} {q : ℝ} {p : ℕ} (hq0 : 0 ≤ q) (hqp : q ≤ p) :
    x ^ q ≤ 1 + x ^ p := by
  rcases le_total x 1 with h | h
  · exact (ENNReal.rpow_le_one h hq0).trans le_self_add
  · calc x ^ q ≤ x ^ (p : ℝ) := ENNReal.rpow_le_rpow_of_exponent_le h hqp
      _ = x ^ p := ENNReal.rpow_natCast x p
      _ ≤ 1 + x ^ p := le_add_self

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {W : WNSpace → Ω → ℝ}

/-- **Small `n`**: straight segments only. -/
theorem lintegral_holder_small (hW : IsWhiteNoise P W) {ξ q : ℝ} (hξ0 : 0 < ξ)
    (hξ1 : ξ ≤ 1 / 32) (hq0 : 0 ≤ q) (hqξ : q * ξ ≤ 1) {A : Finset ℂ} {Q T : Set ℂ} {Pn : ℕ}
    (G : ChainGeom A Q T Pn) {S : Set ℂ} (hQS : Q ⊆ S) {K₀ : ℝ} (hK₀ : 0 ≤ K₀)
    (hexp : ∀ (K : ℕ) (γ : ℝ), 0 ≤ γ → γ ≤ 3 / 2 →
      ∫⁻ ω, ENNReal.ofReal (Real.exp (γ * supQ Q (fun z => phiMN W P 0 K z ω))) ∂P ≤
        ENNReal.ofReal (A.card * (4 : ℝ) ^ (γ * K + K₀ * √(K : ℝ))))
    {Cs : ℝ} (hCs : 0 < Cs) {n : ℕ} (hn : n ≤ 1) (hlam : 0 < lambdaN ξ W P n)
    (hlow : Real.exp (-(ξ * (Cs + 2 * (n + 1) * Real.log 2))) ≤ lambdaN ξ W P n) :
    ∫⁻ ω, holderConst (fun z => (lambdaN ξ W P n)⁻¹ *
        (LFPP.lfppDOn ξ (fun x => phiMN W P 0 n x ω) S z.1 z.2).toReal) T ^ q ∂P ≤
      ENNReal.ofReal ((Real.exp (Cs + 4 * Real.log 2) * √(Pn : ℝ)) ^ q *
        (A.card * (4 : ℝ) ^ (1 + K₀))) := by
  have hφ := isPhiVersion_phiMN (P := P) hW (Nat.zero_le n)
  set lam := lambdaN ξ W P n
  set L := Real.log 2 with hL
  have hL0 : 0 < L := Real.log_pos (by norm_num)
  have hc0 : 0 ≤ lam⁻¹ * √(Pn : ℝ) := by positivity
  set γ := q * ξ with hγ
  have hγ0 : 0 ≤ γ := by positivity
  -- pathwise
  have hpt : ∀ ω, holderConst (fun z => lam⁻¹ *
      (LFPP.lfppDOn ξ (fun x => phiMN W P 0 n x ω) S z.1 z.2).toReal) T ^ q ≤
      ENNReal.ofReal ((lam⁻¹ * √(Pn : ℝ)) ^ q) *
        ENNReal.ofReal (Real.exp (γ * supQ Q (fun z => phiMN W P 0 n z ω))) := by
    intro ω
    have h := holderConst_le_straight hξ0.le (f := fun x => phiMN W P 0 n x ω) G.convex_Q
      G.T_sub hQS (Dm := Pn) (fun z hz w hw => G.norm_sub_le hz hw)
      (fun z hz => abs_le_supQ G.compact_Q (hφ.cont ω) hz) (inv_nonneg.2 hlam.le)
    refine (ENNReal.rpow_le_rpow h hq0).trans (le_of_eq ?_)
    set e := Real.exp (ξ * supQ Q (fun z => phiMN W P 0 n z ω))
    rw [← ENNReal.ofReal_mul (inv_nonneg.2 hlam.le),
      ENNReal.ofReal_rpow_of_nonneg (by positivity) hq0, ← ENNReal.ofReal_mul (by positivity)]
    congr 1
    rw [show lam⁻¹ * (e * √(Pn : ℝ)) = (lam⁻¹ * √(Pn : ℝ)) * e by ring,
      Real.mul_rpow hc0 (Real.exp_pos _).le, ← Real.exp_mul]
    congr 2
    rw [hγ]; ring
  refine (lintegral_mono hpt).trans ?_
  rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  calc ENNReal.ofReal ((lam⁻¹ * √(Pn : ℝ)) ^ q) *
        ∫⁻ ω, ENNReal.ofReal (Real.exp (γ * supQ Q (fun z => phiMN W P 0 n z ω))) ∂P
      ≤ ENNReal.ofReal ((lam⁻¹ * √(Pn : ℝ)) ^ q) *
          ENNReal.ofReal (A.card * (4 : ℝ) ^ (γ * n + K₀ * √(n : ℝ))) := by
        gcongr
        exact hexp n γ hγ0 (by linarith)
    _ = ENNReal.ofReal ((lam⁻¹ * √(Pn : ℝ)) ^ q *
          (A.card * (4 : ℝ) ^ (γ * n + K₀ * √(n : ℝ)))) :=
        (ENNReal.ofReal_mul (by positivity)).symm
    _ ≤ _ := by
        refine ENNReal.ofReal_le_ofReal ?_
        have hn' : (n : ℝ) ≤ 1 := by exact_mod_cast hn
        have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
        have hinv : lam⁻¹ ≤ Real.exp (Cs + 4 * L) := by
          have h1 : lam⁻¹ ≤ Real.exp (ξ * (Cs + 2 * (n + 1) * L)) := by
            rw [show Real.exp (ξ * (Cs + 2 * (n + 1) * L)) =
              (Real.exp (-(ξ * (Cs + 2 * (n + 1) * L))))⁻¹ by rw [Real.exp_neg, inv_inv]]
            exact inv_anti₀ (Real.exp_pos _) hlow
          refine h1.trans (Real.exp_le_exp.2 ?_)
          have h2 : Cs + 2 * (n + 1) * L ≤ Cs + 4 * L := by nlinarith
          have h3 : 0 ≤ Cs + 2 * (n + 1) * L := by positivity
          calc ξ * (Cs + 2 * (n + 1) * L) ≤ 1 * (Cs + 4 * L) :=
                mul_le_mul (by linarith) h2 h3 (by norm_num)
            _ = Cs + 4 * L := one_mul _
        have hb : (4 : ℝ) ^ (γ * n + K₀ * √(n : ℝ)) ≤ (4 : ℝ) ^ (1 + K₀) := by
          refine Real.rpow_le_rpow_of_exponent_le (by norm_num) ?_
          have h1 : γ * n ≤ 1 := by
            calc γ * n ≤ 1 * 1 := mul_le_mul (by linarith) hn' hn0 (by norm_num)
              _ = 1 := one_mul _
          have h2 : √(n : ℝ) ≤ 1 := Real.sqrt_le_one.2 hn'
          have h3 : K₀ * √(n : ℝ) ≤ K₀ := by nlinarith [Real.sqrt_nonneg (n : ℝ)]
          linarith
        have ha : (lam⁻¹ * √(Pn : ℝ)) ^ q ≤ (Real.exp (Cs + 4 * L) * √(Pn : ℝ)) ^ q :=
          Real.rpow_le_rpow hc0 (mul_le_mul_of_nonneg_right hinv (Real.sqrt_nonneg _)) hq0
        have hA0 : (0 : ℝ) ≤ A.card := Nat.cast_nonneg _
        have := Real.rpow_nonneg hc0 q
        calc (lam⁻¹ * √(Pn : ℝ)) ^ q * (A.card * (4 : ℝ) ^ (γ * n + K₀ * √(n : ℝ)))
            ≤ (Real.exp (Cs + 4 * L) * √(Pn : ℝ)) ^ q * (A.card * (4 : ℝ) ^ (1 + K₀)) := by
              gcongr

/-- **Large `n`**: the chaining majorant, Minkowski and the level bounds. -/
theorem lintegral_holder_large (hW : IsWhiteNoise P W) {ξ q : ℝ} (hξ0 : 0 < ξ)
    (hξ1 : ξ ≤ 1 / 32) (hq1 : 1 ≤ q) {p : ℕ} (hp16 : 16 ≤ p) (hqp : q ≤ p)
    (hpξ : (p : ℝ) * ξ ≤ 3 / 2) {A : Finset ℂ} {Q T : Set ℂ} {Pn : ℕ} (G : ChainGeom A Q T Pn)
    (hne : Q.Nonempty) {S : Set ℂ} (hQS : Q ⊆ S) {K₀ : ℝ}
    (hexp : ∀ (K : ℕ) (γ : ℝ), 0 ≤ γ → γ ≤ 3 / 2 →
      ∫⁻ ω, ENNReal.ofReal (Real.exp (γ * supQ Q (fun z => phiMN W P 0 K z ω))) ∂P ≤
        ENNReal.ofReal (A.card * (4 : ℝ) ^ (γ * K + K₀ * √(K : ℝ))))
    {C₁ : ℝ} (hC₁ : 0 ≤ C₁)
    (hmom : ∀ m : ℕ, ∫⁻ ω, rectLen ξ (fun x => phiMN W P 0 m x ω) (rectAB 2 1) ^ p ∂P ≤
      ENNReal.ofReal (C₁ * lambdaN ξ W P m ^ p))
    {Cs : ℝ} (hCs : 0 < Cs) (hlam : ∀ m, 0 < lambdaN ξ W P m) {n : ℕ} (hn : 2 ≤ n)
    (hsc : ∀ k : ℕ, k ≤ n → lambdaN ξ W P (n - k) ≤
      Cs * (2 : ℝ) ^ (2 * ξ * k) * Real.exp (Cs * √(k : ℝ)) * lambdaN ξ W P n)
    (hlow : Real.exp (-(ξ * (Cs + 2 * (n + 1) * Real.log 2))) ≤ lambdaN ξ W P n) :
    ∫⁻ ω, holderConst (fun z => (lambdaN ξ W P n)⁻¹ *
        (LFPP.lfppDOn ξ (fun x => phiMN W P 0 n x ω) S z.1 z.2).toReal) T ^ q ∂P ≤
      1 + ENNReal.ofReal ((48 * Pn * holderB A.card p K₀ C₁ Cs) ^ p) := by
  have hP := hW.isProbabilityMeasure
  have hp0 : p ≠ 0 := by omega
  have hp1 : (1 : ℝ) ≤ p := by exact_mod_cast (show 1 ≤ p by omega)
  have hpR : (0 : ℝ) < p := by linarith
  set lam := lambdaN ξ W P n with hlam_def
  have hlamn : 0 < lam := hlam n
  have hlinv : 0 ≤ lam⁻¹ := inv_nonneg.2 hlamn.le
  have hφ := isPhiVersion_phiMN (P := P) hW (Nat.zero_le n)
  set m := n - 1 with hm_def
  have hm1 : 1 ≤ m := by omega
  set L := Real.log 2 with hL
  have hL0 : 0 < L := Real.log_pos (by norm_num)
  set D := 2 * L * K₀ / p + Cs with hD
  set Sb := holderSb p K₀ Cs with hSb
  have hSb0 : 0 ≤ Sb := holderSb_nonneg p K₀ Cs
  set c₀ := 4 * (A.card : ℝ) ^ 2 * C₁ * Cs ^ p with hc₀
  have hc₀0 : 0 ≤ c₀ := by positivity
  set c₁ := (A.card : ℝ) * Real.exp (p * (Cs / 32 + L)) with hc₁
  have hc₁0 : 0 ≤ c₁ := by positivity
  -- the decoupled level bounds and their a.s. domination
  set XH : ℕ → Ω → ℝ≥0∞ := fun k => Xdec ξ W P Q n p (k + 1) (famH A k) (jH k) with hXH
  set XS : ℕ → Ω → ℝ≥0∞ := fun K => Xdec ξ W P Q n p K (famS A K) (jS K) with hXS
  have hH : ∀ᵐ ω ∂P, ∀ k, k + 1 ≤ n → ∀ r ∈ famH A k,
      S6D.len21 ξ (fun x => phiMN W P 0 n x ω) (k + 1) (jH k r) ≤ XH k ω := by
    refine ae_all_iff.2 fun k => ?_
    by_cases hk : k + 1 ≤ n
    · filter_upwards [ae_len21_le_Xdec hW hξ0.le G.compact_Q hk hp0 (famH A k) (jH k)
        fun r hr => jH_sub G hr] with ω hω _ r hr using hω r hr
    · exact Filter.Eventually.of_forall fun ω h => absurd h hk
  have hS : ∀ᵐ ω ∂P, ∀ K, K ≤ n → ∀ r ∈ famS A K,
      S6D.len21 ξ (fun x => phiMN W P 0 n x ω) K (jS K r) ≤ XS K ω := by
    refine ae_all_iff.2 fun K => ?_
    by_cases hK : K ≤ n
    · filter_upwards [ae_len21_le_Xdec hW hξ0.le G.compact_Q hK hp0 (famS A K) (jS K)
        fun r hr => jS_sub G hr] with ω hω _ r hr using hω r hr
    · exact Filter.Eventually.of_forall fun ω h => absurd h hK
  -- the measurable majorant
  set T1 : Ω → ℝ≥0∞ := fun ω => ENNReal.ofReal (lam⁻¹ *
    (Real.exp (ξ * supQ Q (fun z => phiMN W P 0 n z ω)) * √((2 : ℝ)⁻¹ ^ m))) with hT1
  set FS : ℕ → Ω → ℝ≥0∞ := fun K ω => ENNReal.ofReal (lam⁻¹ * √2 ^ K) * XS K ω with hFS
  set FH : ℕ → Ω → ℝ≥0∞ := fun k ω => ENNReal.ofReal (lam⁻¹ * √2 ^ k) * XH k ω with hFH
  set Y : Ω → ℝ≥0∞ := fun ω =>
    T1 ω + ∑ K ∈ Finset.Icc 1 m, FS K ω + ∑ k ∈ Finset.Icc 1 m, FH k ω with hY
  have hpt : ∀ᵐ ω ∂P, holderConst (fun z => lam⁻¹ *
      (LFPP.lfppDOn ξ (fun x => phiMN W P 0 n x ω) S z.1 z.2).toReal) T ≤
      ENNReal.ofReal (48 * Pn) * Y ω := by
    filter_upwards [hH, hS] with ω hωH hωS
    have h := holderConst_le_chain hξ0.le (hφ.cont ω) G hQS hm1 (fun k => XH k ω)
      (fun K => XS K ω) (fun k _ hk2 r hr => hωH k (by omega) r hr)
      (fun K _ hK2 r hr => hωS K (by omega) r hr)
      (fun z hz => abs_le_supQ G.compact_Q (hφ.cont ω) hz) hlinv
    refine h.trans (le_of_eq ?_)
    rw [mul_left_comm]
    congr 1
    simp only [chainG, hY, hT1, hFS, hFH, mul_add, Finset.mul_sum]
    congr 1
    · congr 1
      · rw [← ENNReal.ofReal_mul hlinv]
      · exact Finset.sum_congr rfl fun K _ => by rw [← mul_assoc, ← ENNReal.ofReal_mul hlinv]
    · exact Finset.sum_congr rfl fun k _ => by rw [← mul_assoc, ← ENNReal.ofReal_mul hlinv]
  -- measurability
  have hT1m : Measurable T1 :=
    ENNReal.measurable_ofReal.comp (((Real.measurable_exp.comp
      ((measurable_supQ G.compact_Q hne hφ.cont hφ.meas).const_mul ξ)).mul_const _).const_mul _)
  have hFSm : ∀ K ∈ Finset.Icc 1 m, AEMeasurable (FS K) P := fun K hK =>
    ((measurable_Xdec hW G.compact_Q hne (by rw [Finset.mem_Icc] at hK; omega) p _ _).const_mul
      _).aemeasurable
  have hFHm : ∀ k ∈ Finset.Icc 1 m, AEMeasurable (FH k) P := fun k hk =>
    ((measurable_Xdec hW G.compact_Q hne (by rw [Finset.mem_Icc] at hk; omega) p _ _).const_mul
      _).aemeasurable
  have hFSs : AEMeasurable (fun ω => ∑ K ∈ Finset.Icc 1 m, FS K ω) P :=
    (Finset.aemeasurable_sum _ hFSm).congr
      (Filter.Eventually.of_forall fun ω => Finset.sum_apply ω _ FS)
  have hFHs : AEMeasurable (fun ω => ∑ k ∈ Finset.Icc 1 m, FH k ω) P :=
    (Finset.aemeasurable_sum _ hFHm).congr
      (Filter.Eventually.of_forall fun ω => Finset.sum_apply ω _ FH)
  -- the three groups in `L^p`
  have hlT1 : lpN P p T1 ≤ ENNReal.ofReal (c₁ ^ ((p : ℝ)⁻¹) * Sb) := by
    refine (lpN_le_of_lintegral_le hp0 hc₁0
      (link_bound hξ0.le hξ1 hp16 hpξ hexp hCs (by omega) hlamn hlow)).trans ?_
    exact ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left
      (exp_sqrt_le_sum_bound (a := L / 4) (by positivity) D (Nat.cast_nonneg n))
      (Real.rpow_nonneg hc₁0 _))
  have hlFS : lpN P p (fun ω => ∑ K ∈ Finset.Icc 1 m, FS K ω) ≤
      ENNReal.ofReal (c₀ ^ ((p : ℝ)⁻¹) * Sb) := by
    refine (lpN_sum_le hp1 _ hFSm).trans ?_
    calc ∑ K ∈ Finset.Icc 1 m, lpN P p (FS K)
        ≤ ∑ K ∈ Finset.Icc 1 m, ENNReal.ofReal (c₀ ^ ((p : ℝ)⁻¹) *
            Real.exp (-(L / 4) * K + D * √(K : ℝ))) := by
          refine Finset.sum_le_sum fun K hK => ?_
          rw [Finset.mem_Icc] at hK
          refine lpN_le_of_lintegral_le hp0 hc₀0 ?_
          refine level_bound hW hξ0.le hξ1 hp16 hpξ G.compact_Q hne hexp hC₁ hmom hCs hlam hsc
            (K := K) (κ := K) (by omega) le_rfl (famS A K) (jS K) ?_
          have h := card_famS_le A K
          rw [pow_succ] at h
          linarith
      _ = ENNReal.ofReal (c₀ ^ ((p : ℝ)⁻¹) *
            ∑ K ∈ Finset.Icc 1 m, Real.exp (-(L / 4) * K + D * √(K : ℝ))) := by
          rw [Finset.mul_sum, ENNReal.ofReal_sum_of_nonneg fun K _ =>
            mul_nonneg (Real.rpow_nonneg hc₀0 _) (Real.exp_pos _).le]
      _ ≤ ENNReal.ofReal (c₀ ^ ((p : ℝ)⁻¹) * Sb) :=
          ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left
            (sum_exp_sqrt_le (a := L / 4) (by positivity) D _) (Real.rpow_nonneg hc₀0 _))
  have hlFH : lpN P p (fun ω => ∑ k ∈ Finset.Icc 1 m, FH k ω) ≤
      ENNReal.ofReal (c₀ ^ ((p : ℝ)⁻¹) * Sb) := by
    refine (lpN_sum_le hp1 _ hFHm).trans ?_
    calc ∑ k ∈ Finset.Icc 1 m, lpN P p (FH k)
        ≤ ∑ k ∈ Finset.Icc 1 m, ENNReal.ofReal (c₀ ^ ((p : ℝ)⁻¹) *
            Real.exp (-(L / 4) * ((k + 1 : ℕ) : ℝ) + D * √((k + 1 : ℕ) : ℝ))) := by
          refine Finset.sum_le_sum fun k hk => ?_
          rw [Finset.mem_Icc] at hk
          refine lpN_le_of_lintegral_le hp0 hc₀0 ?_
          refine level_bound hW hξ0.le hξ1 hp16 hpξ G.compact_Q hne hexp hC₁ hmom hCs hlam hsc
            (K := k + 1) (κ := k) (by omega) (Nat.le_succ k) (famH A k) (jH k) ?_
          rw [card_famH]
          have : (0 : ℝ) ≤ A.card * 4 ^ (k + 1) := by positivity
          linarith
      _ = ENNReal.ofReal (c₀ ^ ((p : ℝ)⁻¹) * ∑ k ∈ Finset.Icc 1 m,
            Real.exp (-(L / 4) * ((k + 1 : ℕ) : ℝ) + D * √((k + 1 : ℕ) : ℝ))) := by
          rw [Finset.mul_sum, ENNReal.ofReal_sum_of_nonneg fun K _ =>
            mul_nonneg (Real.rpow_nonneg hc₀0 _) (Real.exp_pos _).le]
      _ ≤ ENNReal.ofReal (c₀ ^ ((p : ℝ)⁻¹) * Sb) := by
          refine ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left ?_ (Real.rpow_nonneg hc₀0 _))
          have h := sum_exp_sqrt_le (a := L / 4) (by positivity) D
            ((Finset.Icc 1 m).map (addRightEmbedding 1))
          rw [Finset.sum_map] at h
          simp only [addRightEmbedding_apply] at h
          exact h
  have hlY : lpN P p Y ≤ ENNReal.ofReal (holderB A.card p K₀ C₁ Cs) := by
    calc lpN P p Y ≤ lpN P p (fun ω => T1 ω + ∑ K ∈ Finset.Icc 1 m, FS K ω) +
          lpN P p (fun ω => ∑ k ∈ Finset.Icc 1 m, FH k ω) :=
          lpN_add_le hp1 (hT1m.aemeasurable.add hFSs) hFHs
      _ ≤ lpN P p T1 + lpN P p (fun ω => ∑ K ∈ Finset.Icc 1 m, FS K ω) +
          lpN P p (fun ω => ∑ k ∈ Finset.Icc 1 m, FH k ω) := by
          gcongr
          exact lpN_add_le hp1 hT1m.aemeasurable hFSs
      _ ≤ ENNReal.ofReal (c₁ ^ ((p : ℝ)⁻¹) * Sb) + ENNReal.ofReal (c₀ ^ ((p : ℝ)⁻¹) * Sb) +
          ENNReal.ofReal (c₀ ^ ((p : ℝ)⁻¹) * Sb) := by gcongr
      _ = ENNReal.ofReal (holderB A.card p K₀ C₁ Cs) := by
          have h1 : 0 ≤ c₁ ^ ((p : ℝ)⁻¹) * Sb := mul_nonneg (Real.rpow_nonneg hc₁0 _) hSb0
          have h2 : 0 ≤ c₀ ^ ((p : ℝ)⁻¹) * Sb := mul_nonneg (Real.rpow_nonneg hc₀0 _) hSb0
          rw [← ENNReal.ofReal_add h1 h2, ← ENNReal.ofReal_add (by positivity) h2]
          congr 1
          simp only [holderB, hc₀, hc₁, hSb]
          ring
  -- assembly
  have hB0 : 0 ≤ holderB A.card p K₀ C₁ Cs :=
    holderB_nonneg (Nat.cast_nonneg _) hC₁ hCs.le p K₀
  calc ∫⁻ ω, holderConst (fun z => lam⁻¹ *
        (LFPP.lfppDOn ξ (fun x => phiMN W P 0 n x ω) S z.1 z.2).toReal) T ^ q ∂P
      ≤ ∫⁻ ω, (1 + (ENNReal.ofReal (48 * Pn) * Y ω) ^ p) ∂P := by
        refine lintegral_mono_ae ?_
        filter_upwards [hpt] with ω hω
        exact (ENNReal.rpow_le_rpow hω (by linarith)).trans
          (rpow_le_one_add_pow (by linarith) hqp)
    _ = 1 + ∫⁻ ω, (ENNReal.ofReal (48 * Pn) * Y ω) ^ p ∂P := by
        rw [lintegral_add_left measurable_const, lintegral_const, measure_univ, mul_one]
    _ ≤ 1 + ENNReal.ofReal ((48 * Pn * holderB A.card p K₀ C₁ Cs) ^ p) := by
        gcongr
        have e1 : ∫⁻ ω, (ENNReal.ofReal (48 * Pn) * Y ω) ^ p ∂P =
            lpN P p (fun ω => ENNReal.ofReal (48 * Pn) * Y ω) ^ (p : ℝ) := by
          rw [← lintegral_eq_lpN_rpow hpR]
          simp_rw [ENNReal.rpow_natCast]
        rw [e1, lpN_const_mul hpR ENNReal.ofReal_ne_top]
        calc (ENNReal.ofReal (48 * Pn) * lpN P p Y) ^ (p : ℝ)
            ≤ (ENNReal.ofReal (48 * Pn) * ENNReal.ofReal (holderB A.card p K₀ C₁ Cs)) ^
                (p : ℝ) := by
              gcongr
          _ = ENNReal.ofReal ((48 * Pn * holderB A.card p K₀ C₁ Cs) ^ p) := by
              rw [← ENNReal.ofReal_mul (by positivity), ENNReal.rpow_natCast,
                ← ENNReal.ofReal_pow (by positivity)]

end Holder
end Uniform
end GaussianLQG
