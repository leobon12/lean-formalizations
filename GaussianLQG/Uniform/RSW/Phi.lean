import GaussianLQG.Uniform.RSW.P10
import LQGMetric.Papers.DDDF.RSWUnifQ

/-!
# RSW estimates for `φ` with constants uniform in `ξ` (Route U, item U4, part 1)

Phase B, packet PB-RSW. Uniform-constants ledger `blueprint/phaseB/uniform-ledger.tex`, U4;
feasibility study `planning/audits/B1-S6-feasibility.md`, §3b row 16 and §4 U4. Templates (not
edited): `rsw_low` (`LQGMetric/Papers/DDDF/RSWLow.lean`), `rsw_high` (`RSWHigh.lean`),
`rsw_low_unif`, `rsw_high_unif` (`RSWUnif.lean`), `rsw_low_quantile`, `rsw_high_quantile`
(`RSWUnifQ.lean`): DDDF Prop 14 (= Prop 7) and its quantile forms (3.36)–(3.37).

The template proofs build their constant `C = Σ_τ T_τ + 4N + 1` from the ξ-free RSW geometry
(`rsw_geom`: the number `N` of crossings and the derivative bounds `‖F_τ'‖`) and from the Prop 10
constants `C_τ`. With the uniform constants of `prop10_unif` the same proofs give one `C ≥ 1` for
every white noise and every `ξ ∈ (0, ξs]` (a binder move; the geometry is reused unchanged):

* `rsw_low_xi`, `rsw_high_xi`: Prop 14 items 1–2 for fixed shapes (`rsw_low`, `rsw_high`);
* `rsw_low_unif_xi`, `rsw_high_unif_xi`: uniformly over shapes in `[A, B]²` (`rsw_low_unif`,
  `rsw_high_unif`, via `lenObs_rectAB_mono`);
* `rsw_low_quantile_unif`, `rsw_high_quantile_unif`: the quantile forms (3.36)–(3.37) (ledger
  U4 statements; `rsw_low_quantile`, `rsw_high_quantile`).

Each is stated in the ledger's U-form (a fixed white noise `hW`, then the constants, then
`∀ ξ ∈ Ioc 0 ξs`) and is a corollary of the stronger form with suffix `_all`, whose constant is
chosen before the probability space (`∀ {Ω} [MeasurableSpace Ω] {P} {W}, IsWhiteNoise P W → …`
after the existential).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

namespace GaussianLQG
namespace Uniform

open LQGMetric LQGMetric.DDDF LQGMetric.WhiteNoise

universe u

/-- **DDDF Proposition 14 (= Prop 7), item 1, uniform in `ξ`** (template `rsw_low`; small
quantiles): one `C ≥ 1` for all white noises and all `ξ ∈ (0, ξs]`. -/
theorem rsw_low_xi_all {ξs : ℝ} (hξs : 0 < ξs) {a b a' b' : ℝ} (ha : 0 < a) (hab : a < b)
    (ha' : 0 < a') (hb' : 0 < b') :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω}
      {W : WNSpace → Ω → ℝ}, IsWhiteNoise P W → ∀ ξ ∈ Ioc (0 : ℝ) ξs,
      ∀ (n : ℕ) (l ε : ℝ), 0 < ε → ε < 1 / 2 →
      ENNReal.ofReal ε ≤ P {ω | lenObs ξ (phiMN W P 0 n) (rectAB a b) ω ≤ l} →
      ENNReal.ofReal (ε / C) ≤ P {ω | lenObs ξ (phiMN W P 0 n) (rectAB a' b') ω ≤
        C * l * Real.exp (C * Real.sqrt |Real.log (ε / C)|)} := by
  obtain ⟨κ, _, K, A, B, U, F, hgeo, hlow, hup⟩ := rsw_geom ha hab ha' hb'
  have hC := fun τ => prop10_unif_all.{u} hξs (K τ) (A τ) (B τ) (U τ) (F τ) (hgeo τ).1
    (hgeo τ).2.1 (hgeo τ).2.2.1 (hgeo τ).2.2.2.1 (hgeo τ).2.2.2.2.1 (hgeo τ).2.2.2.2.2
  choose Cτ hCτ1 hCτ using hC
  have hCτ0 : ∀ τ, 0 < Cτ τ := fun τ => lt_of_lt_of_le one_pos (hCτ1 τ)
  set N : ℝ := (Fintype.card κ : ℝ) with hNdef
  set S : κ → ℝ := fun τ => derivSup (F τ) (K τ) with hSdef
  set T : κ → ℝ := fun τ => Cτ τ * S τ + Cτ τ * Real.sqrt (1 + 2 * |Real.log (2 * Cτ τ * N)|)
    with hTdef
  have hT0 : ∀ τ, 0 ≤ T τ := fun τ => by
    have := derivSup_nonneg (F τ) (K τ)
    have := hCτ0 τ
    positivity
  have hTle : ∀ τ, T τ ≤ ∑ τ', T τ' := fun τ =>
    Finset.single_le_sum (fun i _ => hT0 i) (Finset.mem_univ τ)
  have hN0 : 0 ≤ N := Nat.cast_nonneg _
  set C : ℝ := ∑ τ, T τ + 4 * N + 1 with hCdef
  have hsum0 : 0 ≤ ∑ τ, T τ := Finset.sum_nonneg fun i _ => hT0 i
  have hC1 : 1 ≤ C := by linarith
  refine ⟨C, hC1, fun {Ω} _ {P} {W} hW ξ hξ n l ε hε hε2 hP => ?_⟩
  have := hW.isProbabilityMeasure
  have hφ := isPhiVersion_phiMN hW (Nat.zero_le n)
  have hR : ∀ {x y : ℝ}, 0 < x → 0 < y → 0 < (rectAB x y).crossWidth := fun hx _ => by
    simpa [MarkedRect.crossWidth, rectAB] using hx
  obtain ⟨ω₀, hω₀⟩ : {ω | lenObs ξ (phiMN W P 0 n) (rectAB a b) ω ≤ l}.Nonempty :=
    nonempty_of_measure_ne_zero (lt_of_lt_of_le (ENNReal.ofReal_pos.2 hε) hP).ne'
  have hb : 0 < b := ha.trans hab
  have hl : 0 < l :=
    (lenObs_pos hφ.cont (rectAB a b) ha.le hb.le (hR ha hb) ω₀).trans_le hω₀
  have hκ : Nonempty κ := by
    by_contra hne
    rw [not_nonempty_iff] at hne
    have h := hlow ξ (fun x => phiMN W P 0 n x ω₀)
    rw [iInf_of_empty, top_le_iff] at h
    exact rectLen_ne_top _ ha.le hb.le (hφ.cont ω₀) h
  have hN1 : 1 ≤ N := by
    rw [hNdef]; exact_mod_cast Fintype.card_pos
  -- the union bound over the crossings `τ` (DDDF l. 794)
  have hsub : {ω | lenObs ξ (phiMN W P 0 n) (rectAB a b) ω ≤ l} ⊆
      ⋃ τ, {ω | crossLenIn ξ (fun x => phiMN W P 0 n x ω) (K τ) (A τ) (B τ) ≤
        ENNReal.ofReal l} := by
    intro ω hω
    obtain ⟨τ, hτ⟩ := Finite.exists_min
      (fun τ => crossLenIn ξ (fun x => phiMN W P 0 n x ω) (K τ) (A τ) (B τ))
    refine mem_iUnion.2 ⟨τ, ?_⟩
    calc _ ≤ ⨅ τ', crossLenIn ξ (fun x => phiMN W P 0 n x ω) (K τ') (A τ') (B τ') :=
          le_iInf hτ
      _ ≤ rectLen ξ (fun x => phiMN W P 0 n x ω) (rectAB a b) := hlow ξ _
      _ = ENNReal.ofReal (lenObs ξ (phiMN W P 0 n) (rectAB a b) ω) :=
          (ofReal_lenObs hφ.cont _ ha.le hb.le ω).symm
      _ ≤ ENNReal.ofReal l := ENNReal.ofReal_le_ofReal hω
  obtain ⟨τ, hτ⟩ : ∃ τ, ENNReal.ofReal (ε / N) ≤
      P {ω | crossLenIn ξ (fun x => phiMN W P 0 n x ω) (K τ) (A τ) (B τ) ≤
        ENNReal.ofReal l} := by
    by_contra hcon
    push Not at hcon
    have h1 := (hP.trans (measure_mono hsub)).trans (measure_iUnion_fintype_le P _)
    have h2 := ENNReal.sum_lt_sum_of_nonempty Finset.univ_nonempty fun τ (_ : τ ∈ Finset.univ) =>
      hcon τ
    rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, ← ENNReal.ofReal_natCast,
      ← ENNReal.ofReal_mul (Nat.cast_nonneg _), ← hNdef,
      mul_div_cancel₀ _ (by linarith : N ≠ 0)] at h2
    exact lt_irrefl _ (h1.trans_lt h2)
  have hε₁ : 0 < ε / N := div_pos hε (by linarith)
  have hε₁2 : ε / N < 1 / 2 := lt_of_le_of_lt (div_le_self hε.le hN1) hε2
  have h3 := (hCτ τ hW ξ hξ n l (ε / N) hl hε₁ hε₁2).1 hτ
  refine le_trans ?_ (h3.trans (measure_mono fun ω hω => ?_))
  · refine ENNReal.ofReal_le_ofReal ?_
    rw [div_div]
    exact div_le_div_of_nonneg_left hε.le (by positivity) (by linarith)
  · simp only [mem_ofPred_eq] at hω ⊢
    have h4 := (hup ξ (fun x => phiMN W P 0 n x ω) τ).trans hω
    rw [← ofReal_lenObs hφ.cont _ ha'.le hb'.le ω] at h4
    have h5 := (ENNReal.ofReal_le_ofReal_iff (by
      unfold p10Len; have := derivSup_nonneg (F τ) (K τ); have := hCτ0 τ
      positivity)).1 h4
    refine h5.trans (p10Len_le (hCτ0 τ) hl
      (c := 2 * Cτ τ * N) (by have := hCτ0 τ; positivity) (by field_simp) hC1 ?_ ?_ hε hε2)
    · have := hTle τ
      have : 0 ≤ Cτ τ * Real.sqrt (1 + 2 * |Real.log (2 * Cτ τ * N)|) :=
        mul_nonneg (hCτ0 τ).le (Real.sqrt_nonneg _)
      simp only [hTdef] at *
      linarith
    · have := hTle τ
      have : 0 ≤ Cτ τ * S τ := mul_nonneg (hCτ0 τ).le (derivSup_nonneg _ _)
      simp only [hTdef] at *
      linarith

/-- **DDDF Proposition 14 (= Prop 7), item 2, uniform in `ξ`** (template `rsw_high`; high
quantiles): one `C ≥ 1` for all white noises and all `ξ ∈ (0, ξs]`. -/
theorem rsw_high_xi_all {ξs : ℝ} (hξs : 0 < ξs) {a b a' b' : ℝ} (ha : 0 < a) (hab : a < b)
    (ha' : 0 < a') (hb' : 0 < b') :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω}
      {W : WNSpace → Ω → ℝ}, IsWhiteNoise P W → ∀ ξ ∈ Ioc (0 : ℝ) ξs,
      ∀ (n : ℕ) (l ε : ℝ), 0 < ε → ε < 1 / 2 →
      ENNReal.ofReal (1 - ε) ≤ P {ω | lenObs ξ (phiMN W P 0 n) (rectAB a b) ω ≤ l} →
      ENNReal.ofReal (1 - 3 * ε ^ (1 / C)) ≤ P {ω | lenObs ξ (phiMN W P 0 n) (rectAB a' b') ω ≤
        C * l * Real.exp (C * Real.sqrt |Real.log (ε / C)|)} := by
  classical
  obtain ⟨κ, _, K, A, B, U, F, hgeo, hlow, hup⟩ := rsw_geom ha hab ha' hb'
  have hC := fun τ => prop10_unif_all.{u} hξs (K τ) (A τ) (B τ) (U τ) (F τ) (hgeo τ).1
    (hgeo τ).2.1 (hgeo τ).2.2.1 (hgeo τ).2.2.2.1 (hgeo τ).2.2.2.2.1 (hgeo τ).2.2.2.2.2
  choose Cτ hCτ1 hCτ using hC
  have hCτ0 : ∀ τ, 0 < Cτ τ := fun τ => lt_of_lt_of_le one_pos (hCτ1 τ)
  set N : ℝ := (Fintype.card κ : ℝ) with hNdef
  set S : κ → ℝ := fun τ => derivSup (F τ) (K τ) with hSdef
  set T : κ → ℝ := fun τ => Cτ τ * S τ + Cτ τ * Real.sqrt (1 + 2 * |Real.log (2 * Cτ τ)|)
    with hTdef
  have hT0 : ∀ τ, 0 ≤ T τ := fun τ => by
    have := derivSup_nonneg (F τ) (K τ)
    have := hCτ0 τ
    positivity
  have hTle : ∀ τ, T τ ≤ ∑ τ', T τ' := fun τ =>
    Finset.single_le_sum (fun i _ => hT0 i) (Finset.mem_univ τ)
  have hN0 : 0 ≤ N := Nat.cast_nonneg _
  set C : ℝ := ∑ τ, T τ + 4 * N + 1 with hCdef
  have hsum0 : 0 ≤ ∑ τ, T τ := Finset.sum_nonneg fun i _ => hT0 i
  have hC1 : 1 ≤ C := by linarith
  have hC0 : 0 < C := by linarith
  refine ⟨C, hC1, fun {Ω} _ {P} {W} hW ξ hξ n l ε hε hε2 hP => ?_⟩
  have := hW.isProbabilityMeasure
  have hξ0 : 0 ≤ ξ := hξ.1.le
  have hφ := isPhiVersion_phiMN hW (Nat.zero_le n)
  set Y := phiMN W P 0 n with hYdef
  have hR : ∀ {x y : ℝ}, 0 < x → 0 < y → 0 < (rectAB x y).crossWidth := fun hx _ => by
    simpa [MarkedRect.crossWidth, rectAB] using hx
  obtain ⟨ω₀, hω₀⟩ : {ω | lenObs ξ Y (rectAB a b) ω ≤ l}.Nonempty :=
    nonempty_of_measure_ne_zero (lt_of_lt_of_le (ENNReal.ofReal_pos.2 (by linarith)) hP).ne'
  have hb : 0 < b := ha.trans hab
  have hl : 0 < l :=
    (lenObs_pos hφ.cont (rectAB a b) ha.le hb.le (hR ha hb) ω₀).trans_le hω₀
  have hκ : Nonempty κ := by
    by_contra hne
    rw [not_nonempty_iff] at hne
    have h := hlow ξ (fun x => Y x ω₀)
    rw [iInf_of_empty, top_le_iff] at h
    exact rectLen_ne_top _ ha.le hb.le (hφ.cont ω₀) h
  -- the crossings with an admissible path
  set κ' := {τ : κ // crossLenIn ξ 0 (K τ) (A τ) (B τ) ≠ ⊤}
  have hfin' : ∀ τ : κ', ∀ ω, crossLenIn ξ (fun x => Y x ω) (K τ.1) (A τ.1) (B τ.1) ≠ ⊤ :=
    fun τ ω => crossLenIn_ne_top_of_cont (hgeo τ.1).1 τ.2 (hφ.cont ω)
  -- on `{L_{a,b} ≤ l}` some crossing has length `≤ l` (DDDF l. 801–803)
  have hsub : ∀ ω, lenObs ξ Y (rectAB a b) ω ≤ l → ∃ τ : κ',
      (crossLenIn ξ (fun x => Y x ω) (K τ.1) (A τ.1) (B τ.1)).toReal ≤ l := by
    intro ω hω
    obtain ⟨τ, hτ⟩ := Finite.exists_min
      (fun τ => crossLenIn ξ (fun x => Y x ω) (K τ) (A τ) (B τ))
    have h1 : crossLenIn ξ (fun x => Y x ω) (K τ) (A τ) (B τ) ≤ ENNReal.ofReal l :=
      calc _ ≤ ⨅ τ', crossLenIn ξ (fun x => Y x ω) (K τ') (A τ') (B τ') := le_iInf hτ
        _ ≤ rectLen ξ (fun x => Y x ω) (rectAB a b) := hlow ξ _
        _ = ENNReal.ofReal (lenObs ξ Y (rectAB a b) ω) :=
            (ofReal_lenObs hφ.cont _ ha.le hb.le ω).symm
        _ ≤ ENNReal.ofReal l := ENNReal.ofReal_le_ofReal hω
    have hne := ne_top_of_le_ne_top ENNReal.ofReal_ne_top h1
    exact ⟨⟨τ, crossLenIn_zero_ne_top_of_cont (hgeo τ).1 (hφ.cont ω) hne⟩,
      ENNReal.toReal_le_of_le_ofReal hl.le h1⟩
  have : Nonempty κ' := (hsub ω₀ hω₀).nonempty
  -- the square-root trick (DDDF l. 803)
  obtain ⟨τ, hτ⟩ := lemma13_cross_sqrt hξ0 hφ.cont hφ.meas
    (hasGaussianLaw_phiMN hW (Nat.zero_le n)) (cov_phiMN_nonneg hW (Nat.zero_le n))
    (fun τ : κ' => K τ.1) (fun τ => A τ.1) (fun τ => B τ.1) (fun τ => (hgeo τ.1).1)
    (fun τ => τ.2) (fun _ => l)
  set N' : ℝ := (Fintype.card κ' : ℝ) with hN'def
  have hN'1 : 1 ≤ N' := by rw [hN'def]; exact_mod_cast Fintype.card_pos
  have hN'N : N' ≤ N := by
    rw [hN'def, hNdef]; exact_mod_cast Fintype.card_subtype_le _
  set Ev := ⋃ τ : κ', {ω | (crossLenIn ξ (fun x => Y x ω) (K τ.1) (A τ.1) (B τ.1)).toReal ≤ l}
  have hEv : 1 - ε ≤ P.real Ev := by
    have h1 : ENNReal.ofReal (1 - ε) ≤ P Ev :=
      hP.trans (measure_mono fun ω hω => mem_iUnion.2 (hsub ω hω))
    rwa [← ofReal_measureReal, ENNReal.ofReal_le_ofReal_iff measureReal_nonneg] at h1
  set ε₁ := ε ^ (1 / N') with hε₁def
  have hε1 : ε < 1 := by linarith
  have hroot : (1 - P.real Ev) ^ (1 / N') ≤ ε₁ :=
    Real.rpow_le_rpow (by linarith [measureReal_le_one (μ := P) (s := Ev)]) (by linarith)
      (by positivity)
  have hτ' : 1 - ε₁ ≤
      P.real {ω | (crossLenIn ξ (fun x => Y x ω) (K τ.1) (A τ.1) (B τ.1)).toReal ≤ l} := by
    linarith
  have hεε₁ : ε ≤ ε₁ := by
    calc ε = ε ^ (1 : ℝ) := (Real.rpow_one ε).symm
      _ ≤ ε₁ := Real.rpow_le_rpow_of_exponent_ge hε hε1.le
          (by rw [div_le_one (by linarith)]; exact hN'1)
  have hε₁C : ε₁ ≤ ε ^ (1 / C) :=
    Real.rpow_le_rpow_of_exponent_ge hε hε1.le
      (one_div_le_one_div_of_le (by linarith) (by linarith))
  by_cases h3 : 1 / 3 ≤ ε₁
  · rw [ENNReal.ofReal_of_nonpos (by linarith)]; exact zero_le
  push Not at h3
  have hε₁0 : 0 < ε₁ := hε.trans_le hεε₁
  have hP₁ : ENNReal.ofReal (1 - ε₁) ≤ P {ω | crossLenIn ξ (fun x => Y x ω) (K τ.1) (A τ.1)
      (B τ.1) ≤ ENNReal.ofReal l} := by
    refine le_trans ?_ (measure_mono (s := {ω | (crossLenIn ξ (fun x => Y x ω) (K τ.1) (A τ.1)
      (B τ.1)).toReal ≤ l}) fun ω hω =>
      (ENNReal.le_ofReal_iff_toReal_le (hfin' τ ω) hl.le).2 hω)
    exact (ENNReal.ofReal_le_iff_le_toReal (measure_ne_top _ _)).2 hτ'
  have h4 := (hCτ τ.1 hW ξ hξ n l ε₁ hl hε₁0 (by linarith)).2 hP₁
  refine le_trans (ENNReal.ofReal_le_ofReal (by linarith)) (h4.trans (measure_mono fun ω hω => ?_))
  simp only [mem_ofPred_eq] at hω ⊢
  have h5 := (hup ξ (fun x => Y x ω) τ.1).trans hω
  rw [← ofReal_lenObs hφ.cont _ ha'.le hb'.le ω] at h5
  have h6 := (ENNReal.ofReal_le_ofReal_iff (by
    unfold p10Len; have := derivSup_nonneg (F τ.1) (K τ.1); have := hCτ0 τ.1
    positivity)).1 h5
  have h7 : p10Len (Cτ τ.1) l ε₁ (S τ.1) ≤
      C * l * Real.exp (C * Real.sqrt |Real.log (ε₁ / C)|) := by
    refine p10Len_le (hCτ0 τ.1) hl (c := 2 * Cτ τ.1) (by have := hCτ0 τ.1; positivity) rfl hC1
      ?_ ?_ hε₁0 (by linarith)
    · have := hTle τ.1
      have : 0 ≤ Cτ τ.1 * Real.sqrt (1 + 2 * |Real.log (2 * Cτ τ.1)|) :=
        mul_nonneg (hCτ0 τ.1).le (Real.sqrt_nonneg _)
      simp only [hTdef] at *
      linarith
    · have := hTle τ.1
      have : 0 ≤ Cτ τ.1 * S τ.1 := mul_nonneg (hCτ0 τ.1).le (derivSup_nonneg _ _)
      simp only [hTdef] at *
      linarith
  have h8 : Real.exp (C * Real.sqrt |Real.log (ε₁ / C)|) ≤
      Real.exp (C * Real.sqrt |Real.log (ε / C)|) :=
    Real.exp_le_exp.2 (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt
      (abs_log_div_mono hε hεε₁ (by linarith) hC1)) hC0.le)
  calc _ ≤ _ := h6
    _ ≤ _ := h7
    _ ≤ _ := mul_le_mul_of_nonneg_left h8 (by positivity)

/-- **DDDF Proposition 7, small quantiles, uniform over shapes in `[A, B]²` and in `ξ`**
(template `rsw_low_unif`). -/
theorem rsw_low_unif_xi_all {ξs : ℝ} (hξs : 0 < ξs) {A B : ℝ} (hA : 0 < A) (hAB : A < B) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω}
      {W : WNSpace → Ω → ℝ}, IsWhiteNoise P W → ∀ ξ ∈ Ioc (0 : ℝ) ξs,
      ∀ a b a' b' : ℝ, a ∈ Icc A B → b ∈ Icc A B → a' ∈ Icc A B → b' ∈ Icc A B →
      ∀ (n : ℕ) (l ε : ℝ), 0 < ε → ε < 1 / 2 →
      ENNReal.ofReal ε ≤ P {ω | lenObs ξ (phiMN W P 0 n) (rectAB a b) ω ≤ l} →
      ENNReal.ofReal (ε / C) ≤ P {ω | lenObs ξ (phiMN W P 0 n) (rectAB a' b') ω ≤
        C * l * Real.exp (C * Real.sqrt |Real.log (ε / C)|)} := by
  obtain ⟨C, hC1, hC⟩ := rsw_low_xi_all.{u} hξs hA hAB (hA.trans hAB) hA
  refine ⟨C, hC1, fun {Ω} _ {P} {W} hW ξ hξ a b a' b' ha hb ha' hb' n l ε hε hε2 hP => ?_⟩
  have hc := (isPhiVersion_phiMN hW (Nat.zero_le n)).cont
  refine (hC hW ξ hξ n l ε hε hε2 (hP.trans (measure_mono fun ω hω => ?_))).trans
    (measure_mono fun ω hω => ?_)
  · exact (lenObs_rectAB_mono hc hA.le ha.1 (hA.le.trans hb.1) hb.2 ω).trans hω
  · exact (lenObs_rectAB_mono hc (hA.le.trans ha'.1) ha'.2 hA.le hb'.1 ω).trans hω

/-- **DDDF Proposition 7, high quantiles, uniform over shapes in `[A, B]²` and in `ξ`**
(template `rsw_high_unif`). -/
theorem rsw_high_unif_xi_all {ξs : ℝ} (hξs : 0 < ξs) {A B : ℝ} (hA : 0 < A) (hAB : A < B) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω}
      {W : WNSpace → Ω → ℝ}, IsWhiteNoise P W → ∀ ξ ∈ Ioc (0 : ℝ) ξs,
      ∀ a b a' b' : ℝ, a ∈ Icc A B → b ∈ Icc A B → a' ∈ Icc A B → b' ∈ Icc A B →
      ∀ (n : ℕ) (l ε : ℝ), 0 < ε → ε < 1 / 2 →
      ENNReal.ofReal (1 - ε) ≤ P {ω | lenObs ξ (phiMN W P 0 n) (rectAB a b) ω ≤ l} →
      ENNReal.ofReal (1 - 3 * ε ^ (1 / C)) ≤ P {ω | lenObs ξ (phiMN W P 0 n) (rectAB a' b') ω ≤
        C * l * Real.exp (C * Real.sqrt |Real.log (ε / C)|)} := by
  obtain ⟨C, hC1, hC⟩ := rsw_high_xi_all.{u} hξs hA hAB (hA.trans hAB) hA
  refine ⟨C, hC1, fun {Ω} _ {P} {W} hW ξ hξ a b a' b' ha hb ha' hb' n l ε hε hε2 hP => ?_⟩
  have hc := (isPhiVersion_phiMN hW (Nat.zero_le n)).cont
  refine (hC hW ξ hξ n l ε hε hε2 (hP.trans (measure_mono fun ω hω => ?_))).trans
    (measure_mono fun ω hω => ?_)
  · exact (lenObs_rectAB_mono hc hA.le ha.1 (hA.le.trans hb.1) hb.2 ω).trans hω
  · exact (lenObs_rectAB_mono hc (hA.le.trans ha'.1) ha'.2 hA.le hb'.1 ω).trans hω

/-- **DDDF (3.36), uniform in `ξ`** (ledger U4, `rsw_low_quantile_unif`; template
`rsw_low_quantile`): small quantiles, uniformly over shapes in `[A, B]²`, with one `C ≥ 1` for
all white noises and all `ξ ∈ (0, ξs]`. -/
theorem rsw_low_quantile_unif_all {ξs : ℝ} (hξs : 0 < ξs) {A B : ℝ} (hA : 0 < A) (hAB : A < B) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω}
      {W : WNSpace → Ω → ℝ}, IsWhiteNoise P W → ∀ ξ ∈ Ioc (0 : ℝ) ξs,
      ∀ a b a' b' : ℝ, a ∈ Icc A B → b ∈ Icc A B → a' ∈ Icc A B → b' ∈ Icc A B →
      ∀ (n : ℕ) (ε : ℝ), 0 < ε → ε < 1 / 2 →
      ellQ ξ P (phiMN W P 0 n) (rectAB a' b') (ENNReal.ofReal (ε / C)) ≤
        C * ellQ ξ P (phiMN W P 0 n) (rectAB a b) (ENNReal.ofReal ε) *
          Real.exp (C * Real.sqrt |Real.log (ε / C)|) := by
  obtain ⟨C, hC1, hC⟩ := rsw_low_unif_xi_all.{u} hξs hA hAB
  have hC0 : 0 < C := by linarith
  refine ⟨C, hC1, fun {Ω} _ {P} {W} hW ξ hξ a b a' b' ha hb ha' hb' n ε hε hε2 => ?_⟩
  have := hW.isProbabilityMeasure
  have hφ := isPhiVersion_phiMN hW (Nat.zero_le n)
  have hp0 : 0 < ENNReal.ofReal ε := ENNReal.ofReal_pos.2 hε
  have hp1 : ENNReal.ofReal ε < 1 := by rw [ENNReal.ofReal_lt_one]; linarith
  have h1 := prob_le_ellQ (ξ := ξ) (P := P) hφ.cont hφ.meas (rectAB a b) hp0 hp1
  have h2 := hC hW ξ hξ a b a' b' ha hb ha' hb' n _ ε hε hε2 h1
  unfold ellQ
  refine (le_measure_Iic_iff_lowerQuantile_le (ENNReal.ofReal_pos.2 (div_pos hε hC0))
    (by rw [ENNReal.ofReal_lt_one, div_lt_one hC0]; linarith)).1 ?_
  rw [Measure.map_apply (measurable_lenObs hφ.cont hφ.meas _) measurableSet_Iic]
  exact h2

/-- **DDDF (3.37), uniform in `ξ`** (ledger U4, `rsw_high_quantile_unif`; template
`rsw_high_quantile`, reading D-DDDF-8): high quantiles, uniformly over shapes in `[A, B]²`, with
one `C ≥ 1` for all white noises and all `ξ ∈ (0, ξs]`, for `3 ε^{1/C} < 1`. -/
theorem rsw_high_quantile_unif_all {ξs : ℝ} (hξs : 0 < ξs) {A B : ℝ} (hA : 0 < A) (hAB : A < B) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω}
      {W : WNSpace → Ω → ℝ}, IsWhiteNoise P W → ∀ ξ ∈ Ioc (0 : ℝ) ξs,
      ∀ a b a' b' : ℝ, a ∈ Icc A B → b ∈ Icc A B → a' ∈ Icc A B → b' ∈ Icc A B →
      ∀ (n : ℕ) (ε : ℝ), 0 < ε → ε < 1 / 2 → 3 * ε ^ (1 / C) < 1 →
      ellBarQ ξ P (phiMN W P 0 n) (rectAB a' b') (ENNReal.ofReal (3 * ε ^ (1 / C))) ≤
        C * ellBarQ ξ P (phiMN W P 0 n) (rectAB a b) (ENNReal.ofReal ε) *
          Real.exp (C * Real.sqrt |Real.log (ε / C)|) := by
  obtain ⟨C, hC1, hC⟩ := rsw_high_unif_xi_all.{u} hξs hA hAB
  refine ⟨C, hC1, fun {Ω} _ {P} {W} hW ξ hξ a b a' b' ha hb ha' hb' n ε hε hε2 h3 => ?_⟩
  have := hW.isProbabilityMeasure
  have hφ := isPhiVersion_phiMN hW (Nat.zero_le n)
  have hp0 : 0 < ENNReal.ofReal ε := ENNReal.ofReal_pos.2 hε
  have hp1 : ENNReal.ofReal ε < 1 := by rw [ENNReal.ofReal_lt_one]; linarith
  have hq0 : 0 < 1 - ENNReal.ofReal ε := tsub_pos_of_lt hp1
  have hq1 : 1 - ENNReal.ofReal ε < 1 :=
    ENNReal.sub_lt_self ENNReal.one_ne_top one_ne_zero hp0.ne'
  have h1 := prob_le_ellQ (ξ := ξ) (P := P) hφ.cont hφ.meas (rectAB a b) hq0 hq1
  have e1 : (1 : ℝ≥0∞) - ENNReal.ofReal ε = ENNReal.ofReal (1 - ε) := by
    rw [ENNReal.ofReal_sub _ hε.le, ENNReal.ofReal_one]
  rw [e1] at h1
  have h2 := hC hW ξ hξ a b a' b' ha hb ha' hb' n _ ε hε hε2 h1
  have hr0 : 0 < 3 * ε ^ (1 / C) := by have := Real.rpow_pos_of_pos hε (1 / C); positivity
  unfold ellBarQ ellQ
  have e3 : (1 : ℝ≥0∞) - ENNReal.ofReal (3 * ε ^ (1 / C)) =
      ENNReal.ofReal (1 - 3 * ε ^ (1 / C)) := by
    rw [ENNReal.ofReal_sub _ hr0.le, ENNReal.ofReal_one]
  rw [e1, e3]
  refine (le_measure_Iic_iff_lowerQuantile_le (ENNReal.ofReal_pos.2 (by linarith))
    (by rw [ENNReal.ofReal_lt_one]; linarith)).1 ?_
  rw [Measure.map_apply (measurable_lenObs hφ.cont hφ.meas _) measurableSet_Iic]
  exact h2

/-! ### The per-noise forms (ledger U-form: the white noise first, the constants before `ξ`) -/

section PerNoise

variable {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} {W : WNSpace → Ω → ℝ}

/-- **DDDF Proposition 14, item 1, uniform in `ξ`**, per noise (template `rsw_low`; strong form
`rsw_low_xi_all`) -/
theorem rsw_low_xi (hW : IsWhiteNoise P W) (ξs : ℝ) (hξs : 0 < ξs) {a b a' b' : ℝ}
    (ha : 0 < a) (hab : a < b) (ha' : 0 < a') (hb' : 0 < b') :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ ξ ∈ Ioc (0 : ℝ) ξs, ∀ (n : ℕ) (l ε : ℝ), 0 < ε → ε < 1 / 2 →
      ENNReal.ofReal ε ≤ P {ω | lenObs ξ (phiMN W P 0 n) (rectAB a b) ω ≤ l} →
      ENNReal.ofReal (ε / C) ≤ P {ω | lenObs ξ (phiMN W P 0 n) (rectAB a' b') ω ≤
        C * l * Real.exp (C * Real.sqrt |Real.log (ε / C)|)} := by
  obtain ⟨C, hC1, hC⟩ := rsw_low_xi_all.{u} hξs ha hab ha' hb'
  exact ⟨C, hC1, hC hW⟩

/-- **DDDF Proposition 14, item 2, uniform in `ξ`**, per noise (template `rsw_high`; strong form
`rsw_high_xi_all`) -/
theorem rsw_high_xi (hW : IsWhiteNoise P W) (ξs : ℝ) (hξs : 0 < ξs) {a b a' b' : ℝ}
    (ha : 0 < a) (hab : a < b) (ha' : 0 < a') (hb' : 0 < b') :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ ξ ∈ Ioc (0 : ℝ) ξs, ∀ (n : ℕ) (l ε : ℝ), 0 < ε → ε < 1 / 2 →
      ENNReal.ofReal (1 - ε) ≤ P {ω | lenObs ξ (phiMN W P 0 n) (rectAB a b) ω ≤ l} →
      ENNReal.ofReal (1 - 3 * ε ^ (1 / C)) ≤ P {ω | lenObs ξ (phiMN W P 0 n) (rectAB a' b') ω ≤
        C * l * Real.exp (C * Real.sqrt |Real.log (ε / C)|)} := by
  obtain ⟨C, hC1, hC⟩ := rsw_high_xi_all.{u} hξs ha hab ha' hb'
  exact ⟨C, hC1, hC hW⟩

/-- **DDDF Proposition 7, small quantiles, uniform over `[A, B]²` and in `ξ`**, per noise
(template `rsw_low_unif`; strong form `rsw_low_unif_xi_all`) -/
theorem rsw_low_unif_xi (hW : IsWhiteNoise P W) (ξs : ℝ) (hξs : 0 < ξs) {A B : ℝ}
    (hA : 0 < A) (hAB : A < B) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ ξ ∈ Ioc (0 : ℝ) ξs,
      ∀ a b a' b' : ℝ, a ∈ Icc A B → b ∈ Icc A B → a' ∈ Icc A B → b' ∈ Icc A B →
      ∀ (n : ℕ) (l ε : ℝ), 0 < ε → ε < 1 / 2 →
      ENNReal.ofReal ε ≤ P {ω | lenObs ξ (phiMN W P 0 n) (rectAB a b) ω ≤ l} →
      ENNReal.ofReal (ε / C) ≤ P {ω | lenObs ξ (phiMN W P 0 n) (rectAB a' b') ω ≤
        C * l * Real.exp (C * Real.sqrt |Real.log (ε / C)|)} := by
  obtain ⟨C, hC1, hC⟩ := rsw_low_unif_xi_all.{u} hξs hA hAB
  exact ⟨C, hC1, hC hW⟩

/-- **DDDF Proposition 7, high quantiles, uniform over `[A, B]²` and in `ξ`**, per noise
(template `rsw_high_unif`; strong form `rsw_high_unif_xi_all`) -/
theorem rsw_high_unif_xi (hW : IsWhiteNoise P W) (ξs : ℝ) (hξs : 0 < ξs) {A B : ℝ}
    (hA : 0 < A) (hAB : A < B) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ ξ ∈ Ioc (0 : ℝ) ξs,
      ∀ a b a' b' : ℝ, a ∈ Icc A B → b ∈ Icc A B → a' ∈ Icc A B → b' ∈ Icc A B →
      ∀ (n : ℕ) (l ε : ℝ), 0 < ε → ε < 1 / 2 →
      ENNReal.ofReal (1 - ε) ≤ P {ω | lenObs ξ (phiMN W P 0 n) (rectAB a b) ω ≤ l} →
      ENNReal.ofReal (1 - 3 * ε ^ (1 / C)) ≤ P {ω | lenObs ξ (phiMN W P 0 n) (rectAB a' b') ω ≤
        C * l * Real.exp (C * Real.sqrt |Real.log (ε / C)|)} := by
  obtain ⟨C, hC1, hC⟩ := rsw_high_unif_xi_all.{u} hξs hA hAB
  exact ⟨C, hC1, hC hW⟩

/-- **DDDF (3.36), uniform in `ξ`** (ledger U4, `rsw_low_quantile_unif`; template
`rsw_low_quantile`; strong form `rsw_low_quantile_unif_all`) -/
theorem rsw_low_quantile_unif (hW : IsWhiteNoise P W) (ξs : ℝ) (hξs : 0 < ξs) {A B : ℝ}
    (hA : 0 < A) (hAB : A < B) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ ξ ∈ Ioc (0 : ℝ) ξs,
      ∀ a b a' b' : ℝ, a ∈ Icc A B → b ∈ Icc A B → a' ∈ Icc A B → b' ∈ Icc A B →
      ∀ (n : ℕ) (ε : ℝ), 0 < ε → ε < 1 / 2 →
      ellQ ξ P (phiMN W P 0 n) (rectAB a' b') (ENNReal.ofReal (ε / C)) ≤
        C * ellQ ξ P (phiMN W P 0 n) (rectAB a b) (ENNReal.ofReal ε) *
          Real.exp (C * Real.sqrt |Real.log (ε / C)|) := by
  obtain ⟨C, hC1, hC⟩ := rsw_low_quantile_unif_all.{u} hξs hA hAB
  exact ⟨C, hC1, hC hW⟩

/-- **DDDF (3.37), uniform in `ξ`** (ledger U4, `rsw_high_quantile_unif`; template
`rsw_high_quantile`; strong form `rsw_high_quantile_unif_all`) -/
theorem rsw_high_quantile_unif (hW : IsWhiteNoise P W) (ξs : ℝ) (hξs : 0 < ξs) {A B : ℝ}
    (hA : 0 < A) (hAB : A < B) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ ξ ∈ Ioc (0 : ℝ) ξs,
      ∀ a b a' b' : ℝ, a ∈ Icc A B → b ∈ Icc A B → a' ∈ Icc A B → b' ∈ Icc A B →
      ∀ (n : ℕ) (ε : ℝ), 0 < ε → ε < 1 / 2 → 3 * ε ^ (1 / C) < 1 →
      ellBarQ ξ P (phiMN W P 0 n) (rectAB a' b') (ENNReal.ofReal (3 * ε ^ (1 / C))) ≤
        C * ellBarQ ξ P (phiMN W P 0 n) (rectAB a b) (ENNReal.ofReal ε) *
          Real.exp (C * Real.sqrt |Real.log (ε / C)|) := by
  obtain ⟨C, hC1, hC⟩ := rsw_high_quantile_unif_all.{u} hξs hA hAB
  exact ⟨C, hC1, hC hW⟩

end PerNoise

end Uniform
end GaussianLQG
