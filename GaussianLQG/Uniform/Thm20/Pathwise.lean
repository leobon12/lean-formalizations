import GaussianLQG.Uniform.Thm20.Glue

/-!
# The denominator bound and the pathwise bound of DDDF Theorem 20, Step 4, uniform in `ξ`

Phase B, packet PB-U9 (ledger U9, rows `dddf_t20_step4_den` and `t20Step4Pathwise_of_num_den`
of §`subsec:ledger-T20`). As in `GaussianLQG/Uniform/Thm20/Glue.lean`, the template proofs are
restated with their witnesses as parameters:

* `t20Step4DenAt_of`: DDDF (5.63)–(5.64) (`dddf_t20_step4_den`,
  `LQGMetric/Papers/DDDF/T20DDen.lean`, `tightness.tex` l. 1131–1149) with any constant
  `C ≥ 36 + 3ξ` (the template takes equality) and `K₀ = 2`;
* `t20Step4PathwiseAt_of`: DDDF l. 1150–1155 (`t20Step4Pathwise_of_num_den`,
  `LQGMetric/Papers/DDDF/T20CGather.lean`): from (5.61)–(5.62) with `(C₁, d₁, K₁)` and
  (5.63)–(5.64) with `(C₂, K₂)`, the pathwise bound holds with
  `C₀ = 32 + 2(C₁+C₂) + C₁ + C₂ + 2(2C₁+3)²(C₁C₂)²`, `d = 2d₁ + 2`, `K₀ = max K₁ K₂`;
* `t20Step4DenU`, `t20Step4PathwiseU`: the uniform predicates of ledger U0 (constants before the
  probability space and before `ξ`; the ledger rows: affine, resp. polynomial, in `ξ`, Recipe M).
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

section Pathwise

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {W : WNSpace → Ω → ℝ}

open T20C T20D in
/-- **DDDF (5.63)–(5.64) with explicit constants** (`eq:Denum`, `tightness.tex` l. 1131–1149):
the proof of `dddf_t20_step4_den` (`LQGMetric/Papers/DDDF/T20DDen.lean`) for every constant
`C ≥ 36 + 3ξ`, with `K₀ = 2`. -/
theorem t20Step4DenAt_of (hW : IsWhiteNoise P W) (Q : PsiParams) {ξ : ℝ} (hξ : 0 < ξ) {C : ℝ}
    (hC : 36 + 3 * ξ ≤ C) : T20Step4DenAt ξ Q W P C 2 := by
  classical
  intro K hK n hKn
  set J' : Finset (Circle × ℂ) := (T20.blkIdx K).biUnion (shortJ K) with hJ'def
  have hJ' : J'.Nonempty := by
    refine Finset.biUnion_nonempty.2 ⟨(0, 0), ?_, ?_⟩
    · simp [T20.blkIdx]
    · simp [shortJ]
  refine ⟨J', hJ', ?_, fun η hη hη1 γ hγ Y hY hYc => ?_⟩
  · calc (J'.card : ℝ) ≤ ∑ b ∈ T20.blkIdx K, ((shortJ K b).card : ℝ) := by
          exact_mod_cast Finset.card_biUnion_le
      _ ≤ ∑ _b ∈ T20.blkIdx K, (4 : ℝ) :=
          Finset.sum_le_sum fun b _ => by exact_mod_cast card_shortJ_le K b
      _ = 4 * (T20.blkIdx K).card := by rw [Finset.sum_const, nsmul_eq_mul]; ring
      _ ≤ 4 * (9 * 4 ^ K) := by gcongr; exact card_blkIdx_le K
      _ ≤ C * 4 ^ K := by
          have h4 : (0 : ℝ) < 4 ^ K := pow_pos (by norm_num) K
          nlinarith [mul_pos hξ h4]
  have hφK := isPhiVersion_phiMN hW (Nat.zero_le K)
  have hYeq : ∀ᵐ ω ∂P, ∀ x, Y x ω = phiMN W P 0 K x ω := by
    refine T20C.ae_forall_eq_of_cont (fun ω => (hYc ω).continuous) hφK.cont fun x => ?_
    have e : phi W ((2 : ℝ)⁻¹ ^ K) ((2 : ℝ)⁻¹ ^ 0) x = phi W ((2 : ℝ) ^ K)⁻¹ 1 x := by
      rw [inv_pow, pow_zero]
    exact (hY x).trans (by rw [← e]; exact (hφK.ae_eq x).symm)
  filter_upwards [ae_XAB_shift_ne_top hW Q cBig 5 5, ae_phiMN_add hW hKn, hYeq]
    with ω hfin hadd hYω
  have hK2 : 2 ≤ K := hK
  have hq := h_le_quarter hK2
  have hp := h_pos K
  set X := Xbig Q W P ω
  set O := Obig K Y ω
  set m := minShort ξ W P K n J' hJ' ω
  have hX0 : 0 ≤ X := ENNReal.toReal_nonneg
  have hO0 : 0 ≤ O := Obig_nonneg K Y ω
  have hm0 : 0 ≤ m := Finset.le_inf' _ _ fun j _ => ENNReal.toReal_nonneg
  set E : ℤ × ℤ → ℝ := fun b => Real.exp (ξ * psiMN Q W P 0 K (T20.dyCenter K b) ω) *
    Real.exp (-(ξ * (2 * X + 3 * O)))
  have hγadm := hγ.adm n ω
  -- the pieces
  have hpiece : ∀ b ∈ T20.coarseBlocks K (γ n ω), ∃ a c, Icc a c ⊆ Icc (0 : ℝ) 1 ∧
      (∀ r ∈ Icc a c, γ n ω r ∈ hatBox K b) ∧ ENNReal.ofReal (E b * m) ≤
        ∫⁻ r in Icc a c, lenDens ξ (fun x => psiMN Q W P 0 n x ω) (γ n ω) r := by
    intro b hb
    have hbI : b ∈ T20.blkIdx K := (Finset.mem_filter.1 hb).1
    obtain ⟨c1, c2, c3, c4⟩ := center_near hK2 hbI
    have hcB : T20.dyCenter K b ∈ bigBox := by
      simp only [bigBox, Complex.mem_reProdIm, mem_Icc]
      exact ⟨⟨by nlinarith, by nlinarith⟩, by nlinarith, by nlinarith⟩
    refine piece_lower hK2 hγadm hb (by positivity) (fun x hx hxb => ?_) fun j hj =>
      Finset.inf'_le _ (Finset.mem_biUnion.2 ⟨b, hbI, hj⟩)
    have hxB : x ∈ bigBox := by
      simp only [MarkedRect.toSet, rectAB, Complex.mem_reProdIm, mem_Icc, zero_add] at hx
      simp only [bigBox, Complex.mem_reProdIm, mem_Icc]
      exact ⟨⟨by linarith [hx.1.1], by linarith [hx.1.2]⟩, by linarith [hx.2.1],
        by linarith [hx.2.2]⟩
    have h1 := abs_le.1 (abs_sub_le_Xbig Q hfin n hxB)
    have h2 := abs_le.1 (abs_sub_le_Xbig Q hfin K hcB)
    have h3 := abs_le.1 (osc_hatBox_le hK2 (hYc ω) hbI hxb)
    rw [hYω, hYω] at h3
    have h4 := hadd x
    simp only [E]
    rw [← Real.exp_add, ← Real.exp_add]
    refine Real.exp_le_exp.2 ?_
    have : psiMN Q W P 0 K (T20.dyCenter K b) ω - 2 * X - 3 * O + phiMN W P K n x ω ≤
        psiMN Q W P 0 n x ω := by
      linarith [h1.1, h1.2, h2.1, h2.2, h3.1, h3.2]
    nlinarith
  have hsum := sum_pieces_le (K := K) (γ := γ n ω) (T20.coarseBlocks K (γ n ω))
    (lenDens ξ (fun x => psiMN Q W P 0 n x ω) (γ n ω)) (fun b => ENNReal.ofReal (E b * m)) hpiece
  rw [← lfppLen_eq] at hsum
  have hψc := (isPsiVersion_psiMN (Q := Q) hW (Nat.zero_le n)).cont ω
  have hfinL : rectLen ξ (fun x => psiMN Q W P 0 n x ω) (rectAB 1 1) ≠ ⊤ :=
    rectLen_ne_top _ (by norm_num [rectAB]) (by norm_num [rectAB]) hψc
  have hbound : ∑ b ∈ T20.coarseBlocks K (γ n ω), ENNReal.ofReal (E b * m) ≤
      ENNReal.ofReal (16 * (1 + η)) * rectLen ξ (fun x => psiMN Q W P 0 n x ω) (rectAB 1 1) := by
    refine hsum.trans ?_
    rw [ENNReal.ofReal_mul (by norm_num), mul_assoc]
    gcongr
    · norm_num
    · exact hγ.near n ω
  have hreal := ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hfinL) hbound
  rw [ENNReal.toReal_sum (fun b _ => ENNReal.ofReal_ne_top), ENNReal.toReal_mul,
    ENNReal.toReal_ofReal (by positivity)] at hreal
  have hL0 : 0 ≤ lenPsi ξ Q W P n ω := ENNReal.toReal_nonneg
  have hKe : (1 : ℝ) ≤ (K : ℝ) ^ Q.ε₀ :=
    Real.one_le_rpow (by exact_mod_cast (by omega : 1 ≤ K)) Q.ε₀_pos.le
  have hfac : Real.exp (-(C * X)) * Real.exp (-(C * (K : ℝ) ^ Q.ε₀ * O)) ≤
      Real.exp (-(ξ * (2 * X + 3 * O))) := by
    rw [← Real.exp_add]
    refine Real.exp_le_exp.2 ?_
    have : 3 * ξ * O ≤ C * (K : ℝ) ^ Q.ε₀ * O := by
      have : 3 * ξ ≤ C * (K : ℝ) ^ Q.ε₀ := by nlinarith
      exact mul_le_mul_of_nonneg_right this hO0
    nlinarith
  calc Real.exp (-(C * X)) * Real.exp (-(C * (K : ℝ) ^ Q.ε₀ * O)) * m *
        ∑ P' ∈ T20.coarseBlocks K (γ n ω), Real.exp (ξ * psiMN Q W P 0 K (T20.dyCenter K P') ω)
      = ∑ b ∈ T20.coarseBlocks K (γ n ω), Real.exp (-(C * X)) *
          Real.exp (-(C * (K : ℝ) ^ Q.ε₀ * O)) * m *
          Real.exp (ξ * psiMN Q W P 0 K (T20.dyCenter K b) ω) := by rw [Finset.mul_sum]
    _ ≤ ∑ b ∈ T20.coarseBlocks K (γ n ω), (E b * m) := by
        refine Finset.sum_le_sum fun b _ => ?_
        simp only [E]
        have := mul_le_mul_of_nonneg_right hfac
          (mul_nonneg hm0 (Real.exp_pos (ξ * psiMN Q W P 0 K (T20.dyCenter K b) ω)).le)
        nlinarith [this]
    _ = ∑ b ∈ T20.coarseBlocks K (γ n ω), (ENNReal.ofReal (E b * m)).toReal := by
        refine Finset.sum_congr rfl fun b _ => ?_
        rw [ENNReal.toReal_ofReal (by positivity)]
    _ ≤ 16 * (1 + η) * lenPsi ξ Q W P n ω := hreal
    _ ≤ C * lenPsi ξ Q W P n ω := by
        refine mul_le_mul_of_nonneg_right ?_ hL0; nlinarith

open T20C in
/-- **DDDF l. 1150–1155 with explicit constants**: the proof of `t20Step4Pathwise_of_num_den`
(`LQGMetric/Papers/DDDF/T20CGather.lean`) from (5.61)–(5.62) with `(C₁, d₁, K₁)` and
(5.63)–(5.64) with `(C₂, K₂)`. -/
theorem t20Step4PathwiseAt_of (hW : IsWhiteNoise P W) (Q : PsiParams) {ξ : ℝ} {C₁ C₂ : ℝ}
    (hC₁ : 0 < C₁) (hC₂ : 0 < C₂) {d₁ K₁ K₂ : ℕ} (hN : T20Step4NumAt ξ Q W P C₁ d₁ K₁)
    (hD : T20Step4DenAt ξ Q W P C₂ K₂) :
    T20Step4PathwiseAt ξ Q W P
      (32 + 2 * (C₁ + C₂) + C₁ + C₂ + 2 * (2 * C₁ + 3) ^ 2 * (C₁ * C₂) ^ 2) (2 * d₁ + 2)
      (max K₁ K₂) := by
  classical
  have := hW.isProbabilityMeasure
  set C₀ : ℝ := 32 + 2 * (C₁ + C₂) + C₁ + C₂ + 2 * (2 * C₁ + 3) ^ 2 * (C₁ * C₂) ^ 2 with hC₀
  intro K hK n hn
  have hKn : K ≤ n := hn
  obtain ⟨s, hσ, J, hJ, hJc, hNK⟩ := hN K (le_of_max_le_left hK) n hn
  obtain ⟨J', hJ', hJ'c, hDK⟩ := hD K (le_of_max_le_right hK) n hn
  have h4K : (0 : ℝ) < 4 ^ K := by positivity
  have hlast : 0 ≤ 2 * (2 * C₁ + 3) ^ 2 * (C₁ * C₂) ^ 2 := by positivity
  have hcard : ((J.card : ℝ) + J'.card) ≤ C₀ * 4 ^ K := by
    have : (C₁ + C₂) * 4 ^ K ≤ C₀ * 4 ^ K :=
      mul_le_mul_of_nonneg_right (by rw [hC₀]; linarith) h4K.le
    linarith
  refine ⟨s, hσ, J, J', hJ, hJ', hcard, fun η hη hη1 γ hγ Y hY hYc => ?_⟩
  have hm : ∀ᵐ ω ∂P, 0 < minShort ξ W P K n J' hJ' ω := by
    have h := (Filter.eventually_all_finset J').2 fun j _ =>
      T20B.ae_mrectLen_pos (ξ := ξ) hW hKn j.1 j.2 (a := 1) (b := 3) one_pos (by norm_num)
    filter_upwards [h] with ω hω
    exact (Finset.lt_inf'_iff _).2 hω
  have hmp := measurePreserving_fst (μ := P) (ν := P)
  filter_upwards [hNK η hη hη1 γ hγ Y hY hYc,
    hmp.quasiMeasurePreserving.ae (hDK η hη hη1 γ hγ Y hY hYc),
    hmp.quasiMeasurePreserving.ae hm] with z hNz hDz hmz
  set V := (T20B.nearIdx K).filter (fun b => z ∈ visSet γ n K b s) with hV
  have hL : ∑ b ∈ T20B.nearIdx K, (visSet γ n K b s).indicator
      (fun z => ENNReal.ofReal (incr ξ Q W P K n b z ^ 2)) z =
      ENNReal.ofReal (∑ b ∈ V, incr ξ Q W P K n b z ^ 2) := by
    rw [ENNReal.ofReal_sum_of_nonneg (fun b _ => sq_nonneg _), hV, Finset.sum_filter]
    refine Finset.sum_congr rfl fun b _ => ?_
    by_cases h : z ∈ visSet γ n K b s
    · rw [indicator_of_mem h, ite_eq_left h]
    · rw [indicator_of_notMem h, ite_eq_right h]
  rw [hL]
  refine le_trans (ENNReal.ofReal_le_ofReal ?_) ENNReal.ofReal_add_le
  set X := Xbig Q W P z.1 with hXd
  set O := Obig K Y z.1 with hOd
  set M := maxLong ξ W P K n J hJ z.1 with hMd
  set m := minShort ξ W P K n J' hJ' z.1 with hmd
  set L := lenPsi ξ Q W P n z.1 with hLd
  set R := T20.condTRatio ξ K (fun x => psiMN Q W P 0 K x z.1) (γ n z.1) with hRd
  set S := lsRatio ξ W P K n J J' hJ hJ' z.1 with hSd
  have hR0 : 0 ≤ R := condTRatio_nonneg _ _ _ _
  have hX0 : 0 ≤ X := ENNReal.toReal_nonneg
  have hO0 : 0 ≤ O := Obig_nonneg K Y z.1
  have hmain0 : 0 ≤ C₀ * ((K : ℝ) + 1) ^ (2 * d₁ + 2) * Real.exp (C₀ * X) *
      Real.exp (C₀ * (K : ℝ) ^ Q.ε₀ * O) * S ^ 2 * R := mul_nonneg (by positivity) hR0
  rcases V.eq_empty_or_nonempty with hVe | ⟨b₀, hb₀⟩
  · rw [hVe, Finset.sum_empty]; positivity
  have hspec : ∀ b ∈ V, ∃ P' ∈ T20.coarseBlocks K (γ n z.1),
      |((b.1 - P'.1 : ℤ) : ℝ)| ≤ C₁ * ((K : ℝ) + 1) ∧
      |((b.2 - P'.2 : ℤ) : ℝ)| ≤ C₁ * ((K : ℝ) + 1) ∧
      incr ξ Q W P K n b z ≤ η + C₁ * ((K : ℝ) + 1) ^ d₁ * Real.exp (C₁ * X) *
        Real.exp (C₁ * (K : ℝ) ^ Q.ε₀ * O) *
        Real.exp (ξ * psiMN Q W P 0 K (T20.dyCenter K P') z.1) * M / L :=
    fun b hb => hNz b (Finset.mem_filter.1 hb).1 (Finset.mem_filter.1 hb).2
  set g : ℤ × ℤ → ℤ × ℤ := fun b => if h : b ∈ V then Classical.choose (hspec b h) else 0
  have hg : ∀ b ∈ V, g b ∈ T20.coarseBlocks K (γ n z.1) ∧
      |((b.1 - (g b).1 : ℤ) : ℝ)| ≤ C₁ * ((K : ℝ) + 1) ∧
      |((b.2 - (g b).2 : ℤ) : ℝ)| ≤ C₁ * ((K : ℝ) + 1) ∧
      incr ξ Q W P K n b z ≤ η + C₁ * ((K : ℝ) + 1) ^ d₁ * Real.exp (C₁ * X) *
        Real.exp (C₁ * (K : ℝ) ^ Q.ε₀ * O) *
        Real.exp (ξ * psiMN Q W P 0 K (T20.dyCenter K (g b)) z.1) * M / L := by
    intro b hb
    have := Classical.choose_spec (hspec b hb)
    simp only [g, dite_eq_left hb]
    exact this
  set S1 := ∑ P' ∈ T20.coarseBlocks K (γ n z.1),
    Real.exp (ξ * psiMN Q W P 0 K (T20.dyCenter K P') z.1)
  set S2 := ∑ P' ∈ T20.coarseBlocks K (γ n z.1),
    Real.exp (2 * ξ * psiMN Q W P 0 K (T20.dyCenter K P') z.1)
  set A := C₁ * ((K : ℝ) + 1) ^ d₁ * Real.exp (C₁ * X) * Real.exp (C₁ * (K : ℝ) ^ Q.ε₀ * O)
  set H := Real.exp (-(C₂ * X)) * Real.exp (-(C₂ * (K : ℝ) ^ Q.ε₀ * O))
  have hS1 : 0 < S1 := Finset.sum_pos (fun _ _ => Real.exp_pos _) ⟨g b₀, (hg b₀ hb₀).1⟩
  have hH : 0 < H := by positivity
  have hM0 : 0 ≤ M := maxLong_nonneg ξ K n J hJ z.1
  have hden : H * m * S1 ≤ C₂ * L := hDz
  have hpos : 0 < H * m * S1 := by positivity
  have hL0 : 0 < L := by nlinarith
  set T : ℤ × ℤ → ℝ := fun b => Real.exp (ξ * psiMN Q W P 0 K (T20.dyCenter K (g b)) z.1)
  have hinc : ∀ b ∈ V, 0 ≤ incr ξ Q W P K n b z ∧
      incr ξ Q W P K n b z ≤ η + A * T b * M * C₂ / (H * m * S1) := by
    intro b hb
    refine ⟨le_max_right _ _, (hg b hb).2.2.2.trans ?_⟩
    have hnum : 0 ≤ A * T b * M := by positivity
    rw [add_le_add_iff_left, div_le_div_iff₀ hL0 hpos]
    nlinarith [mul_le_mul_of_nonneg_left hden hnum]
  set m₀ : ℕ := ⌈C₁ * ((K : ℝ) + 1)⌉₊
  have hsq : ∑ b ∈ V, T b ^ 2 ≤ ((2 * m₀ + 1 : ℕ) : ℝ) ^ 2 * S2 := by
    have e : ∀ b, T b ^ 2 = Real.exp (2 * ξ * psiMN Q W P 0 K (T20.dyCenter K (g b)) z.1) :=
      fun b => by rw [sq, ← Real.exp_add]; ring_nf
    simp_rw [e]
    exact sum_fiber_le g (fun b hb => (hg b hb).1) m₀
      (fun b hb => ⟨(hg b hb).2.1.trans (Nat.le_ceil _), (hg b hb).2.2.1.trans (Nat.le_ceil _)⟩)
      (fun j => Real.exp (2 * ξ * psiMN Q W P 0 K (T20.dyCenter K j) z.1))
      fun j => (Real.exp_pos _).le
  have hVc : (V.card : ℝ) ≤ 16 * 4 ^ K :=
    (Nat.cast_le.2 (Finset.card_le_card (Finset.filter_subset _ _))).trans (card_nearIdx_le K)
  have hG := gather_real V (inc := fun b => incr ξ Q W P K n b z) (T := T) (A := A) (C₂ := C₂)
    (M := M) (H := H) (m := m) (S1 := S1) (S2 := S2) (η := η) (by positivity) hC₂ hM0 hH hmz hS1
    hinc (fun b => (Real.exp_pos _).le) hVc hsq
  -- the constants
  have hAH : A * C₂ / H = C₁ * C₂ * ((K : ℝ) + 1) ^ d₁ * Real.exp ((C₁ + C₂) * X) *
      Real.exp ((C₁ + C₂) * ((K : ℝ) ^ Q.ε₀ * O)) := AH_eq C₁ C₂ K X ((K : ℝ) ^ Q.ε₀) O d₁
  have hSe : S = M / m := rfl
  have hRe : R = S2 / S1 ^ 2 := rfl
  have hS2 : 0 ≤ S2 := Finset.sum_nonneg fun _ _ => (Real.exp_pos _).le
  have hKe : (0 : ℝ) ≤ (K : ℝ) ^ Q.ε₀ := Real.rpow_nonneg (Nat.cast_nonneg K) _
  have hK0 : (0 : ℝ) ≤ C₁ * ((K : ℝ) + 1) :=
    mul_nonneg hC₁.le (add_nonneg (Nat.cast_nonneg K) zero_le_one)
  have hfin := final_gather (η := η) (X := X) (O := O) (e := (K : ℝ) ^ Q.ε₀) (F := 4 ^ K)
    (W0 := (M / m) ^ 2 * (S2 / S1 ^ 2)) d₁ hC₁ hC₂ (Nat.cast_nonneg K) hX0 hO0 hKe h4K.le
    (mul_nonneg (sq_nonneg _) (div_nonneg hS2 (sq_nonneg _))) m₀ (Nat.ceil_lt_add_one hK0)
  rw [hSe, hRe]
  refine hG.trans (le_of_eq_of_le ?_ (hfin.trans (le_of_eq ?_)))
  · rw [hAH]; ring
  · rw [hC₀]; ring

end Pathwise

/-- **DDDF (5.63)–(5.64), uniform in `ξ ∈ (0, ξs]` and in the white noise** (ledger U0,
`T20Step4DenU`): `C = 36 + 3ξs`, `K₀ = 2`. -/
theorem t20Step4DenU (Q : PsiParams) {ξs : ℝ} (hξs : 0 < ξs) : T20Step4DenU.{u} ξs Q :=
  ⟨36 + 3 * ξs, by positivity, 2, fun {Ω} _ {P} {W} hW ξ hξ =>
    t20Step4DenAt_of hW Q hξ.1 (by linarith [hξ.2])⟩

/-- **The pathwise bound of Step 4, uniform**, from the uniform (5.61)–(5.62) and (5.63)–(5.64)
(ledger U0, `T20Step4PathwiseU`; the constant `C₀` is the polynomial of
`t20Step4Pathwise_of_num_den` in the uniform constants). -/
theorem t20Step4PathwiseU_of_numU_denU {ξs : ℝ} {Q : PsiParams} (hN : T20Step4NumU.{u} ξs Q)
    (hD : T20Step4DenU.{u} ξs Q) : T20Step4PathwiseU.{u} ξs Q := by
  obtain ⟨C₁, hC₁, d₁, K₁, hN⟩ := hN
  obtain ⟨C₂, hC₂, K₂, hD⟩ := hD
  exact ⟨32 + 2 * (C₁ + C₂) + C₁ + C₂ + 2 * (2 * C₁ + 3) ^ 2 * (C₁ * C₂) ^ 2, by positivity,
    2 * d₁ + 2, max K₁ K₂, fun {Ω} _ {P} {W} hW ξ hξ =>
      t20Step4PathwiseAt_of hW Q hC₁ hC₂ (hN hW ξ hξ) (hD hW ξ hξ)⟩

/-- **The pathwise bound of DDDF Theorem 20, Step 4, uniform in `ξ ∈ (0, ξs]` and in the white
noise** (ledger U0, `T20Step4PathwiseU`), for `ε₀ ≤ 1`. -/
theorem t20Step4PathwiseU (Q : PsiParams) (hε : Q.ε₀ ≤ 1) {ξs : ℝ} (hξs : 0 < ξs) :
    T20Step4PathwiseU.{u} ξs Q :=
  t20Step4PathwiseU_of_numU_denU (t20Step4NumU Q hε hξs) (t20Step4DenU Q hξs)

end Uniform
end GaussianLQG
