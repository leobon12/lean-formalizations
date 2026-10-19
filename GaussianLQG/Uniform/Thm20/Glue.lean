import GaussianLQG.Uniform.Thm20.Defs

/-!
# The circuit gluing and the numerator bound of DDDF Theorem 20, Step 4, with explicit constants

Phase B, packet PB-U9 (ledger U9, row `t20Step4Num_of_glue` and `dddf_t20_circuit_glue` of
§`subsec:ledger-T20`). The templates `dddf_t20_circuit_glue`
(`LQGMetric/Papers/DDDF/T20EMain.lean`) and `t20Step4Num_of_glue`
(`LQGMetric/Papers/DDDF/T20DNum.lean`) hide their witnesses behind an `∃` placed after `ξ` and
the white noise. Here the same proofs are stated with the witnesses as parameters
(`T20CircuitGlueAt`, `T20Step4NumAt`, `GaussianLQG/Uniform/Thm20/Defs.lean`):

* `t20CircuitGlueAt_of`: the circuit gluing (DDDF (5.61)–(5.62), l. 1097–1123) with
  `C₁ = 40A + 100`, `d₁ = 1`, `K₀ = max K₁ 2`, where `A = r₀(1+2ε₀)^{ε₀} 4^{ε₀}` and `K₁` is any
  index with `4AK + 9 ≤ 2^K` for `K ≥ K₁`: no dependence on `ξ` or on the noise;
* `t20Step4NumAt_of_glueAt`: the numerator bound with any `C₃ ≥ 72 + C₁ + 2ξ + ξC₁` (the template
  takes equality), so that `C₃ = 72 + C₁ + 2ξs + ξs C₁` serves every `ξ ≤ ξs` (ledger Recipe M);
* `t20CircuitGlueU`, `t20Step4NumU`: the uniform predicates of ledger U0.

The proofs are those of the templates, with the witnesses moved to the statement.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal

namespace GaussianLQG
namespace Uniform

open LQGMetric LQGMetric.DDDF LQGMetric.WhiteNoise LQGMetric.SupTail LQGMetric.LFPP

universe u

section Glue

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {W : WNSpace → Ω → ℝ}

open T20E in
/-- **The circuit gluing with explicit constants** (DDDF (5.61)–(5.62), `tightness.tex`
l. 1097–1123, D-DDDF-22; the proof of `dddf_t20_circuit_glue`,
`LQGMetric/Papers/DDDF/T20EMain.lean`, with its witnesses exposed). The constants depend on
`Q` only. -/
theorem t20CircuitGlueAt_of (hW : IsWhiteNoise P W) (Q : PsiParams) (hε : Q.ε₀ ≤ 1) (ξ : ℝ)
    {A : ℝ} (hA : A = Q.r₀ * (1 + 2 * Q.ε₀) ^ Q.ε₀ * 4 ^ Q.ε₀) {K₁ : ℕ}
    (hK₁ : ∀ K : ℕ, K₁ ≤ K → 4 * A * K + 9 ≤ 2 ^ K) :
    T20CircuitGlueAt ξ Q W P (40 * A + 100) 1 (max K₁ 2) := by
  classical
  have := hW.isProbabilityMeasure
  have hε0 := Q.ε₀_pos
  have hA0 : 0 < A := by have := Q.r₀_pos; rw [hA]; positivity
  set C₁ : ℝ := 40 * A + 100
  have hC₁ : 0 < C₁ := by positivity
  intro K hK n hKn
  have hK2 : 2 ≤ K := le_of_max_le_right hK
  have hKr : (1 : ℝ) ≤ K := by exact_mod_cast (by omega : 1 ≤ K)
  set h : ℝ := (2 : ℝ)⁻¹ ^ K
  have hp : 0 < h := by positivity
  have e1 : (2 : ℝ) ^ K * h = 1 := by simp only [h]; rw [← mul_pow]; norm_num
  set S : ℝ := Q.r₀ * (1 + 2 * Q.ε₀) ^ Q.ε₀ * (1 + K * Real.log 4) ^ Q.ε₀
  set s : ℝ := S * h
  -- `S ≤ A K^{ε₀} ≤ A K`
  have hlog : Real.log 4 ≤ 3 := by
    have := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 4); linarith
  have hKe1 : (1 : ℝ) ≤ (K : ℝ) ^ Q.ε₀ := Real.one_le_rpow hKr hε0.le
  have hKeK : (K : ℝ) ^ Q.ε₀ ≤ K := Real.rpow_le_self_of_one_le hKr hε
  have hS : S ≤ A * (K : ℝ) ^ Q.ε₀ := by
    have h1 : (1 + K * Real.log 4) ^ Q.ε₀ ≤ (4 * K) ^ Q.ε₀ :=
      Real.rpow_le_rpow (by positivity) (by
        have := mul_le_mul_of_nonneg_left hlog (by positivity : (0 : ℝ) ≤ K); linarith) hε0.le
    rw [Real.mul_rpow (by norm_num) (by positivity)] at h1
    have := Q.r₀_pos
    simp only [S, hA]
    have h2 : 0 ≤ Q.r₀ * (1 + 2 * Q.ε₀) ^ Q.ε₀ := by positivity
    calc Q.r₀ * (1 + 2 * Q.ε₀) ^ Q.ε₀ * (1 + K * Real.log 4) ^ Q.ε₀
        ≤ Q.r₀ * (1 + 2 * Q.ε₀) ^ Q.ε₀ * (4 ^ Q.ε₀ * (K : ℝ) ^ Q.ε₀) :=
          mul_le_mul_of_nonneg_left h1 h2
      _ = _ := by ring
  have hS0 : 0 ≤ S := by have := Q.r₀_pos; positivity
  set m : ℕ := ⌈2 * S⌉₊
  have hm1 : 2 * S ≤ m := Nat.le_ceil _
  have hm2 : (m : ℝ) < 2 * S + 1 := Nat.ceil_lt_add_one (by positivity)
  have hmK : (m : ℝ) ≤ 2 * A * (K : ℝ) ^ Q.ε₀ + 1 := by linarith
  have hAKe : 0 ≤ A * (K : ℝ) ^ Q.ε₀ := by positivity
  have hAK : 0 ≤ A * (K : ℝ) := by positivity
  have hmK' : (m : ℝ) ≤ 2 * A * K + 1 := by
    have := mul_le_mul_of_nonneg_left hKeK (by positivity : (0 : ℝ) ≤ 2 * A); linarith
  have h2K : (2 * m + 7 : ℝ) ≤ 2 ^ K := by
    have := hK₁ K (le_of_max_le_left hK); linarith
  have hsm : 2 * s * 2 ^ K ≤ m := by
    simp only [s]; rw [mul_assoc, mul_assoc, mul_comm h, e1, mul_one]; exact hm1
  refine ⟨s, fun t ht => ?_, fun η hη hη1 γ hγ => ?_⟩
  · exact T20D.sigma_le_range Q K (lt_of_lt_of_le (by positivity) ht.1) ht.2
  -- the resampled block fields vanish off the `2s`-neighbourhood, for all blocks
  have hσ : ∀ t ∈ Icc (((2 : ℝ)⁻¹ ^ n) ^ 2) (((2 : ℝ)⁻¹ ^ K) ^ 2), Q.sigma t ≤ s := fun t ht =>
    T20D.sigma_le_range Q K (lt_of_lt_of_le (by positivity) ht.1) ht.2
  have hzero : ∀ᵐ ω ∂P, ∀ b ∈ T20B.nearIdx K, ∀ x ∈ T20B.farSet (T20B.hoBlock K b) s,
      T20B.blkKn Q W P K n b x ω = 0 := by
    rw [eventually_all_finset]
    intro b _
    exact T20B.blkVer_eq_zero_far hW Q (by positivity)
      (pow_le_pow_of_le_one (by norm_num) (by norm_num) hKn) (T20B.measurableSet_hoBlock K b) hσ
  have h1 := (measurePreserving_fst (μ := P) (ν := P)).quasiMeasurePreserving.ae hzero
  have h2 := (measurePreserving_snd (μ := P) (ν := P)).quasiMeasurePreserving.ae hzero
  filter_upwards [h1, h2] with z hz1 hz2 b hb hvis
  obtain ⟨t, ht, hnf⟩ := hvis
  simp only [T20B.farSet, mem_ofPred_eq, not_forall, not_le] at hnf
  obtain ⟨y, hy, hxy⟩ := hnf
  set x := γ n z.1 t
  obtain ⟨_, _, _, _, _, hγU⟩ := hγ.adm n z.1
  have hxsq := mem_sq.1 (hγU t ht)
  -- the floors
  have hp2 : (0 : ℝ) < 2 ^ K := by positivity
  have hre : |x.re * 2 ^ K - y.re * 2 ^ K| < m := by
    rw [← sub_mul, abs_mul, abs_of_pos hp2]
    have := Complex.abs_re_le_norm (x - y)
    rw [Complex.sub_re] at this
    have := mul_lt_mul_of_pos_right (this.trans_lt hxy) hp2
    linarith
  have him : |x.im * 2 ^ K - y.im * 2 ^ K| < m := by
    rw [← sub_mul, abs_mul, abs_of_pos hp2]
    have := Complex.abs_im_le_norm (x - y)
    rw [Complex.sub_im] at this
    have := mul_lt_mul_of_pos_right (this.trans_lt hxy) hp2
    linarith
  have q1 : 0 ≤ x.re * 2 ^ K := mul_nonneg hxsq.1.1 hp2.le
  have q2 : x.re * 2 ^ K ≤ 2 ^ K := by
    have := mul_le_mul_of_nonneg_right hxsq.1.2 hp2.le; linarith
  have q3 : 0 ≤ x.im * 2 ^ K := mul_nonneg hxsq.2.1 hp2.le
  have q4 : x.im * 2 ^ K ≤ 2 ^ K := by
    have := mul_le_mul_of_nonneg_right hxsq.2.2 hp2.le; linarith
  obtain ⟨fa1, fa2, fa3, fa4⟩ := floor_facts (N := 2 ^ K) q1 q2 hy.1 hre
  obtain ⟨fb1, fb2, fb3, fb4⟩ := floor_facts (N := 2 ^ K) q3 q4 hy.2 him
  have h2K' : (2 * m + 7 : ℤ) ≤ 2 ^ K := by exact_mod_cast h2K
  have hbx : BoxOK K (b.1 - m) (b.1 + 1 + m) := ⟨by omega, by omega,
    by have : ((b.1 - m : ℤ) : ℝ) < ((2 ^ K : ℤ) : ℝ) := by push_cast; linarith
       exact_mod_cast this.le, by omega⟩
  have hby : BoxOK K (b.2 - m) (b.2 + 1 + m) := ⟨by omega, by omega,
    by have : ((b.2 - m : ℤ) : ℝ) < ((2 ^ K : ℤ) : ℝ) := by push_cast; linarith
       exact_mod_cast this.le, by omega⟩
  set P' : ℤ × ℤ := (⌊x.re * 2 ^ K⌋, ⌊x.im * 2 ^ K⌋)
  obtain ⟨g1, g2, g3, g4⟩ := floor_block K hxsq.1.1 hxsq.1.2
  obtain ⟨g5, g6, g7, g8⟩ := floor_block K hxsq.2.1 hxsq.2.2
  have hP' : P' ∈ T20.coarseBlocks K (γ n z.1) := by
    simp only [T20.coarseBlocks, Finset.mem_filter, T20.blkIdx, Finset.mem_product,
      Finset.mem_Icc]
    refine ⟨⟨⟨g1, g2⟩, g5, g6⟩, t, ht, ?_⟩
    simp only [T20.dyBlock, Complex.mem_reProdIm, mem_Icc]
    exact ⟨⟨g3, g4⟩, g7, g8⟩
  have hC1e : C₁ * ((K : ℝ) + 1) = 40 * (A * K) + 40 * A + 100 * K + 100 := by
    simp only [C₁]; ring
  have hmC : (m : ℝ) ≤ C₁ * ((K : ℝ) + 1) := by rw [hC1e]; linarith
  refine ⟨P', hP', ?_, ?_, circR K (b.1 - m) (b.1 + 1 + m) (b.2 - m) (b.2 + 1 + m),
    circR_sub_longFam hbx hby, ?_, ?_, ?_⟩
  · refine le_trans ?_ hmC
    rw [abs_le]; constructor <;> push_cast <;>
    · have := fa3; have := fa4
      have c1 : ((b.1 - m : ℤ) : ℝ) ≤ (P'.1 : ℝ) := Int.cast_le.2 fa3
      have c2 : (P'.1 : ℝ) ≤ ((b.1 + m : ℤ) : ℝ) := Int.cast_le.2 fa4
      push_cast at c1 c2; linarith
  · refine le_trans ?_ hmC
    rw [abs_le]; constructor <;> push_cast <;>
    · have c1 : ((b.2 - m : ℤ) : ℝ) ≤ (P'.2 : ℝ) := Int.cast_le.2 fb3
      have c2 : (P'.2 : ℝ) ≤ ((b.2 + m : ℤ) : ℝ) := Int.cast_le.2 fb4
      push_cast at c1 c2; linarith
  · have hc := card_circR_le hbx hby
    have hc' : ((circR K (b.1 - m) (b.1 + 1 + m) (b.2 - m) (b.2 + 1 + m)).card : ℝ) ≤
        16 * m + 64 := by
      have : ((circR K (b.1 - m) (b.1 + 1 + m) (b.2 - m) (b.2 + 1 + m)).card : ℤ) ≤
          16 * m + 64 := by omega
      exact_mod_cast this
    rw [pow_one, hC1e]; linarith
  · intro j hj x' hx'
    obtain ⟨⟨hsq', hbox'⟩, -⟩ := circR_props hbx hby hj hx'
    refine ⟨?_, ?_⟩
    · obtain ⟨⟨a5, a6⟩, ⟨a7, a8⟩⟩ := hsq'
      have e2 : (2 : ℝ) ^ K * (2 : ℝ)⁻¹ ^ K = 1 := e1
      push_cast at a5 a6 a7 a8
      simp only [zero_mul] at a5 a7
      simp only [T20D.bigBox, Complex.mem_reProdIm, mem_Icc]
      exact ⟨⟨by linarith, by linarith⟩, by linarith, by linarith⟩
    · have hn := elem_near (P' := P') fa3 fa4 fb3 fb4 hbox'
      have : (4 * m + 8 : ℝ) ≤ C₁ * (K : ℝ) ^ Q.ε₀ := by
        have e3 : C₁ * (K : ℝ) ^ Q.ε₀ = 40 * (A * (K : ℝ) ^ Q.ε₀) + 100 * (K : ℝ) ^ Q.ε₀ := by
          simp only [C₁]; ring
        have e4 : 2 * A * (K : ℝ) ^ Q.ε₀ = 2 * (A * (K : ℝ) ^ Q.ε₀) := by ring
        rw [e3]; rw [e4] at hmK; linarith
      calc _ ≤ _ := hn
        _ ≤ C₁ * (K : ℝ) ^ Q.ε₀ * h := mul_le_mul_of_nonneg_right this hp.le
  · -- the pathwise bound
    set f : ℂ → ℝ := fun x => psiMN Q W P 0 n x z.1
    have hf : Continuous f := (isPsiVersion_psiMN (Q := Q) hW (Nat.zero_le n)).cont z.1
    have hfg : ∀ x ∈ T20B.farSet (T20B.hoBlock K b) s,
        (fun x => psiMN Q W P 0 n x z.1 - T20B.blkKn Q W P K n b x z.1 +
          T20B.blkKn Q W P K n b x z.2) x = f x := fun x hx => by
      simp only [f, hz1 b hb x hx, hz2 b hb x hx, sub_zero, add_zero]
    have hfin : rectLen ξ f (rectAB 1 1) ≠ ⊤ :=
      rectLen_ne_top _ (by norm_num [rectAB]) (by norm_num [rectAB]) hf
    have hnear := hγ.near n z.1
    have hγf : lfppLen ξ f (γ n z.1) ≠ ⊤ :=
      ne_top_of_le_ne_top (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hfin) hnear
    have hglue := glue_rect (ξ := ξ) hf hfg hbx hby (fun x' _ hx' => outBox_far hsm hx')
      (hγ.adm n z.1) hγf
    have hL : (lfppLen ξ f (γ n z.1)).toReal ≤ (1 + η) * T20C.lenPsi ξ Q W P n z.1 := by
      have := ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hfin) hnear
      rwa [ENNReal.toReal_mul, ENNReal.toReal_ofReal (by linarith)] at this
    linarith

open T20C T20D in
/-- **DDDF (5.61)–(5.62) with explicit constants**: the proof of `t20Step4Num_of_glue`
(`LQGMetric/Papers/DDDF/T20DNum.lean`, `tightness.tex` l. 1106–1123) from the circuit gluing with
constants `C₁, d₁, K₀`, for every `C₃ ≥ 72 + C₁ + 2ξ + ξC₁`. -/
theorem t20Step4NumAt_of_glueAt (hW : IsWhiteNoise P W) (Q : PsiParams) {ξ : ℝ} (hξ : 0 < ξ)
    {C₁ : ℝ} (hC₁ : 0 < C₁) {d₁ K₀ : ℕ} (hG : T20CircuitGlueAt ξ Q W P C₁ d₁ K₀) {C₃ : ℝ}
    (hC₃ : 72 + C₁ + 2 * ξ + ξ * C₁ ≤ C₃) : T20Step4NumAt ξ Q W P C₃ d₁ (max K₀ 2) := by
  classical
  have := hW.isProbabilityMeasure
  have hξC : 0 < ξ * C₁ := mul_pos hξ hC₁
  have hC₃0 : 0 < C₃ := by linarith
  intro K hK n hKn
  obtain ⟨s, hσ, hG'⟩ := hG K (le_of_max_le_left hK) n hKn
  have hK2 : 2 ≤ K := le_of_max_le_right hK
  refine ⟨s, hσ, longFam K, longFam_nonempty K, ?_, fun η hη hη1 γ hγ Y hY hYc => ?_⟩
  · refine (card_longFam_le K).trans ?_
    have h4 : (0 : ℝ) ≤ 4 ^ K := by positivity
    have h72 : (72 : ℝ) ≤ C₃ := by
      nlinarith [mul_pos hξ hC₁]
    exact mul_le_mul_of_nonneg_right h72 h4
  have hφK := isPhiVersion_phiMN hW (Nat.zero_le K)
  have hφKn := isPhiVersion_phiMN hW hKn
  have hYeq : ∀ᵐ ω ∂P, ∀ x, Y x ω = phiMN W P 0 K x ω := by
    refine T20C.ae_forall_eq_of_cont (fun ω => (hYc ω).continuous) hφK.cont fun x => ?_
    have e : phi W ((2 : ℝ)⁻¹ ^ K) ((2 : ℝ)⁻¹ ^ 0) x = phi W ((2 : ℝ) ^ K)⁻¹ 1 x := by
      rw [inv_pow, pow_zero]
    exact (hY x).trans (by rw [← e]; exact (hφK.ae_eq x).symm)
  have hω : ∀ᵐ ω ∂P, (XAB (fun n y => phiMN W P 0 n (y + cBig) ω)
      (fun n y => psiMN Q W P 0 n (y + cBig) ω) 5 5 ≠ ⊤) ∧
      (∀ x : ℂ, phiMN W P 0 n x ω = phiMN W P 0 K x ω + phiMN W P K n x ω) ∧
      ∀ x, Y x ω = phiMN W P 0 K x ω := by
    filter_upwards [ae_XAB_shift_ne_top hW Q cBig 5 5, ae_phiMN_add hW hKn, hYeq]
      with ω h1 h2 h3
    exact ⟨h1, h2, h3⟩
  have hlift := (measurePreserving_fst (μ := P) (ν := P)).quasiMeasurePreserving.ae hω
  filter_upwards [hlift, hG' η hη hη1 γ hγ] with z hz hzG b hb hvis
  obtain ⟨hfin, hadd, hYω⟩ := hz
  obtain ⟨P', hP', hd1, hd2, R, hRJ, hRc, hRgeo, hlen⟩ := hzG b hb hvis
  have hCC : C₁ * ((K : ℝ) + 1) ≤ C₃ * ((K : ℝ) + 1) :=
    mul_le_mul_of_nonneg_right (by nlinarith) (by positivity)
  refine ⟨P', hP', hd1.trans hCC, hd2.trans hCC, ?_⟩
  set X := Xbig Q W P z.1
  set O := Obig K Y z.1
  set c := T20.dyCenter K P'
  let MM := maxLong ξ W P K n (longFam K) (longFam_nonempty K) z.1
  have hX0 : 0 ≤ X := ENNReal.toReal_nonneg
  have hO0 : 0 ≤ O := Obig_nonneg K Y z.1
  have hM0 : 0 ≤ MM := maxLong_nonneg ξ K n _ _ z.1
  have hKe : 0 ≤ (K : ℝ) ^ Q.ε₀ := by positivity
  have hp := h_pos K
  have hq := h_le_quarter hK2
  have hcB : c ∈ bigBox := by
    obtain ⟨c1, c2, c3, c4⟩ := center_near hK2 (Finset.mem_filter.1 hP').1
    simp only [bigBox, Complex.mem_reProdIm, mem_Icc]
    exact ⟨⟨by nlinarith, by nlinarith⟩, by nlinarith, by nlinarith⟩
  set A : ℝ := ξ * psiMN Q W P 0 K c z.1 + 2 * ξ * X + ξ * (C₁ * (K : ℝ) ^ Q.ε₀ * O)
  have hj : ∀ j ∈ R, T20B.mrectLen ξ (fun x => psiMN Q W P 0 n x z.1) K j.1 j.2 3 1 ≤
      Real.exp A * MM := by
    intro j hjR
    have hMj : T20B.mrectLen ξ (fun x => phiMN W P K n x z.1) K j.1 j.2 3 1 ≤ MM := by
      exact le_maxLong (P := P) (W := W) (hRJ hjR)
    refine (mrectLen_le_of (K := K) (j := j) (f := fun x => psiMN Q W P 0 n x z.1)
      (g := fun x => phiMN W P K n x z.1) (a := A) (hφKn.cont z.1) fun x hx => ?_).trans
      (mul_le_mul_of_nonneg_left hMj (Real.exp_pos _).le)
    obtain ⟨hxB, hxc⟩ := hRgeo j hjR x hx
    have h1 := abs_le.1 (abs_sub_le_Xbig Q hfin n hxB)
    have h2 := abs_le.1 (abs_sub_le_Xbig Q hfin K hcB)
    have h3 := osc_bigBox_le K (hYc z.1) hxB hcB
    rw [hYω, hYω] at h3
    have h3' : (2 : ℝ) ^ K * O * ‖x - c‖ ≤ C₁ * (K : ℝ) ^ Q.ε₀ * O := by
      have e : (2 : ℝ) ^ K * (2 : ℝ)⁻¹ ^ K = 1 := by rw [inv_pow, mul_inv_cancel₀ (by positivity)]
      calc (2 : ℝ) ^ K * O * ‖x - c‖ ≤ (2 : ℝ) ^ K * O * (C₁ * (K : ℝ) ^ Q.ε₀ * (2 : ℝ)⁻¹ ^ K) :=
            mul_le_mul_of_nonneg_left hxc (by positivity)
        _ = C₁ * (K : ℝ) ^ Q.ε₀ * O * ((2 : ℝ) ^ K * (2 : ℝ)⁻¹ ^ K) := by ring
        _ = _ := by rw [e, mul_one]
    have h4 := hadd x
    have h5 := abs_le.1 (h3.trans h3')
    have : psiMN Q W P 0 n x z.1 ≤
        phiMN W P K n x z.1 + (psiMN Q W P 0 K c z.1 + 2 * X + C₁ * (K : ℝ) ^ Q.ε₀ * O) := by
      linarith [h1.1, h1.2, h2.1, h2.2, h5.1, h5.2]
    have := mul_le_mul_of_nonneg_left this hξ.le
    simp only [A]; nlinarith
  have hS0 : 0 ≤ ∑ j ∈ R, T20B.mrectLen ξ (fun x => psiMN Q W P 0 n x z.1) K j.1 j.2 3 1 :=
    Finset.sum_nonneg fun j _ => ENNReal.toReal_nonneg
  have hψc := (isPsiVersion_psiMN (Q := Q) hW (Nat.zero_le n)).cont z.1
  have hB := T20B.blkKn_spec hW Q hKn b
  have hinc := incr_le_of (ξ := ξ) hψc (((hψc.sub (hB.1 z.1)).add (hB.1 z.2))) hη.le hS0 hlen
  have hL0 : 0 ≤ lenPsi ξ Q W P n z.1 := ENNReal.toReal_nonneg
  have hsum : ∑ j ∈ R, T20B.mrectLen ξ (fun x => psiMN Q W P 0 n x z.1) K j.1 j.2 3 1 ≤
      C₃ * ((K : ℝ) + 1) ^ d₁ * Real.exp (C₃ * X) * Real.exp (C₃ * (K : ℝ) ^ Q.ε₀ * O) *
        Real.exp (ξ * psiMN Q W P 0 K c z.1) * MM := by
    have h1 := Finset.sum_le_card_nsmul R _ _ hj
    rw [nsmul_eq_mul] at h1
    have hA : Real.exp A ≤ Real.exp (C₃ * X) * Real.exp (C₃ * (K : ℝ) ^ Q.ε₀ * O) *
        Real.exp (ξ * psiMN Q W P 0 K c z.1) := by
      rw [← Real.exp_add, ← Real.exp_add]
      refine Real.exp_le_exp.2 ?_
      have a1 : 2 * ξ * X ≤ C₃ * X := mul_le_mul_of_nonneg_right (by nlinarith) hX0
      have a2 : ξ * (C₁ * (K : ℝ) ^ Q.ε₀ * O) ≤ C₃ * (K : ℝ) ^ Q.ε₀ * O := by
        have : ξ * C₁ ≤ C₃ := by nlinarith
        have := mul_le_mul_of_nonneg_right this (mul_nonneg hKe hO0)
        nlinarith
      simp only [A]; linarith
    have hEM : 0 ≤ Real.exp A * MM := mul_nonneg (Real.exp_pos _).le hM0
    have hk1 : (0 : ℝ) ≤ ((K : ℝ) + 1) ^ d₁ := by positivity
    calc _ ≤ (R.card : ℝ) * (Real.exp A * MM) := h1
      _ ≤ C₃ * ((K : ℝ) + 1) ^ d₁ * (Real.exp A * MM) := by
          refine mul_le_mul_of_nonneg_right (hRc.trans ?_) hEM
          exact mul_le_mul_of_nonneg_right (by nlinarith) hk1
      _ ≤ C₃ * ((K : ℝ) + 1) ^ d₁ * ((Real.exp (C₃ * X) * Real.exp (C₃ * (K : ℝ) ^ Q.ε₀ * O) *
            Real.exp (ξ * psiMN Q W P 0 K c z.1)) * MM) := by
          gcongr
      _ = _ := by ring
  refine hinc.trans ?_
  unfold lenPsi
  gcongr

end Glue

/-- **The circuit gluing, uniform** (`T20CircuitGlueU`): `C₁ = 40A + 100`, `d₁ = 1`,
`K₀ = max K₁ 2` serve every `ξ` and every white noise (`ε₀ ≤ 1`). -/
theorem t20CircuitGlueU (Q : PsiParams) (hε : Q.ε₀ ≤ 1) (ξs : ℝ) :
    T20CircuitGlueU.{u} ξs Q := by
  set A : ℝ := Q.r₀ * (1 + 2 * Q.ε₀) ^ Q.ε₀ * 4 ^ Q.ε₀ with hA
  have hA0 : 0 < A := by have := Q.r₀_pos; have := Q.ε₀_pos; positivity
  obtain ⟨K₁, hK₁⟩ := T20E.exists_lin_le_two_pow (4 * A) 9
  exact ⟨40 * A + 100, by positivity, 1, max K₁ 2, fun {Ω} _ {P} {W} hW ξ _ =>
    t20CircuitGlueAt_of hW Q hε ξ hA hK₁⟩

/-- **DDDF (5.61)–(5.62), uniform** (ledger U0, `T20Step4NumU`): from the uniform circuit gluing
with `C₃ = 72 + C₁ + 2ξs + ξs C₁` (ledger U9, row `t20Step4Num_of_glue`: affine in `ξ`,
Recipe M). -/
theorem t20Step4NumU_of_glueU {ξs : ℝ} (hξs : 0 < ξs) {Q : PsiParams}
    (hG : T20CircuitGlueU.{u} ξs Q) : T20Step4NumU.{u} ξs Q := by
  obtain ⟨C₁, hC₁, d₁, K₀, hG⟩ := hG
  refine ⟨72 + C₁ + 2 * ξs + ξs * C₁, by positivity, d₁, max K₀ 2,
    fun {Ω} _ {P} {W} hW ξ hξ => ?_⟩
  refine t20Step4NumAt_of_glueAt hW Q hξ.1 hC₁ (hG hW ξ hξ) ?_
  have := mul_le_mul_of_nonneg_right hξ.2 hC₁.le
  linarith [hξ.2]

/-- **DDDF (5.61)–(5.62), uniform in `ξ ∈ (0, ξs]` and in the white noise** (ledger U0,
`T20Step4NumU`), for `ε₀ ≤ 1`. -/
theorem t20Step4NumU (Q : PsiParams) (hε : Q.ε₀ ≤ 1) {ξs : ℝ} (hξs : 0 < ξs) :
    T20Step4NumU.{u} ξs Q :=
  t20Step4NumU_of_glueU hξs (t20CircuitGlueU Q hε ξs)

end Uniform
end GaussianLQG
