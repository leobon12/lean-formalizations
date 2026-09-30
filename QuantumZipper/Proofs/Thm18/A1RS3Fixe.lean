import QuantumZipper.Proofs.Thm18.A1RS3ZCe

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# A1RS3 (8): the fixed-driver estimate in a positively rescaled parametrization

`ae_smear_fixed_all_e`: the fixed-driver free-field inputs of `ratCauchy_Z_of_X_e` for the family
`p ↦ ν_{parScale e p, ρ}` (`e > 0`), for a good driver that is Hölder on every `[0, T]`. The
proofs of `ae_smear_cauchy_fixed`, `ae_smear_conv_fixed`, `ae_smear_fixed_all`
(A1RS2Fix/FixB/ZC; Duplantier–Sheffield, Invent. Math. 185 (2011), Prop. 3.1), with the `GenFam`
bounds transported along the Lipschitz map `parScale e` (`genFam_parScale`).
Own bookkeeping.
-/

noncomputable section

open MeasureTheory Set Filter Metric
open scoped Topology ENNReal

namespace QuantumZipper
namespace R18
namespace A1RS

open Thm18Asm

theorem dist_parScale_le {e : Fin 4 → ℝ} (he : ∀ i, 0 < e i) (p p' : Fin 4 → ℝ) :
    dist (parScale e p) (parScale e p') ≤ (1 + ∑ i, e i) * dist p p' := by
  have hL : 0 ≤ 1 + ∑ i, e i := by
    have := Finset.sum_nonneg fun i (_ : i ∈ Finset.univ) => (he i).le
    linarith
  refine (dist_pi_le_iff (mul_nonneg hL dist_nonneg)).2 fun i => ?_
  simp only [parScale]
  rw [Real.dist_eq, ← mul_sub, abs_mul, abs_of_pos (he i)]
  have h1 : |p i - p' i| ≤ dist p p' := by rw [← Real.dist_eq]; exact dist_le_pi_dist p p' i
  have h2 : e i ≤ 1 + ∑ j, e j := by
    have := Finset.single_le_sum (f := e) (fun j _ => (he j).le) (Finset.mem_univ i)
    linarith
  exact mul_le_mul h2 h1 (abs_nonneg _) hL

/-- **`GenFam` along a positive rescaling of the parameters.** -/
theorem genFam_parScale {S S' : Set (Fin 4 → ℝ)} {μ : (Fin 4 → ℝ) → ℝ → Measure ℂ} {M : ℝ≥0∞}
    {K c : ℝ} (hF : GenUC.GenFam S μ M K c) {e : Fin 4 → ℝ} (he : ∀ i, 0 < e i)
    (hS : ∀ p ∈ S', parScale e p ∈ S) :
    ∃ K' c' : ℝ, GenUC.GenFam S' (fun p ρ => μ (parScale e p) ρ) M K' c' := by
  set L : ℝ := 1 + ∑ i, e i with hLdef
  have hL1 : 1 ≤ L := by
    have := Finset.sum_nonneg fun i (_ : i ∈ Finset.univ) => (he i).le
    linarith
  refine ⟨K * L ^ c, c, ⟨fun p hp ρ hρ => hF.adm _ (hS p hp) ρ hρ,
    fun p hp ρ hρ => hF.mass _ (hS p hp) ρ hρ,
    mul_nonneg hF.K_nonneg (Real.rpow_nonneg (by linarith) _), hF.c_pos, ?_⟩⟩
  intro p hp p' hp' ρ hρ ρ' hρ'
  refine (hF.energy _ (hS p hp) _ (hS p' hp') ρ hρ ρ' hρ').trans ?_
  have hd := dist_parScale_le he p p'
  have h1 : dist (parScale e p) (parScale e p') + |ρ - ρ'| ≤ L * (dist p p' + |ρ - ρ'|) := by
    have := abs_nonneg (ρ - ρ')
    nlinarith [dist_nonneg (x := p) (y := p')]
  have h2 := Real.rpow_le_rpow (by positivity) h1 hF.c_pos.le
  rw [Real.mul_rpow (by linarith) (by positivity)] at h2
  calc K * (dist (parScale e p) (parScale e p') + |ρ - ρ'|) ^ c
      ≤ K * (L ^ c * (dist p p' + |ρ - ρ'|) ^ c) := mul_le_mul_of_nonneg_left h2 hF.K_nonneg
    _ = K * L ^ c * (dist p p' + |ρ - ρ'|) ^ c := by ring

/-- **Fixed-driver continuum limit at rational parameters** (Duplantier–Sheffield 2011,
Prop. 3.1 for the smeared-loop family). -/
theorem ae_smear_cauchy_fixed_e {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {X : Ω → FieldSample} (hX : IsFreeGFFModConstH X P) {W : ℝ → ℝ}
    (hG : G1zDrvGood W) (left : Bool) {e : Fin 4 → ℝ} (he : ∀ i, 0 < e i) {a b : Fin 4 → ℚ}
    (hsub : GenUC.ratBox a b ⊆ smearU)
    (hHol : ∀ T : ℝ, ∃ CH aH : ℝ, 0 ≤ CH ∧ 0 < aH ∧ aH ≤ 1 ∧
      ∀ x ∈ Icc (0 : ℝ) T, ∀ y ∈ Icc (0 : ℝ) T, |W x - W y| ≤ CH * |x - y| ^ aH) :
    ∀ᵐ ω ∂P, ∀ n : ℕ, ∃ N : ℕ, ∀ r : ℚ, 0 < r → (r : ℝ) < 1 / ((N : ℝ) + 1) →
      ∀ q : Fin 4 → ℚ, ratPt q ∈ GenUC.ratBox a b →
        |evalReg (X ω) (smearFam W left (parScale e (ratPt q)) r) -
          evalReg (X ω) (smearFam W left (parScale e (ratPt q)) 0)| < 1 / ((n : ℝ) + 1) := by
  rcases (GenUC.ratBox a b).eq_empty_or_nonempty with hemp | ⟨p₀, hp₀⟩
  · refine ae_of_all _ fun ω n => ⟨0, fun r _ _ q hq => ?_⟩
    rw [hemp] at hq; exact hq.elim
  have hab : ∀ i, (a i : ℝ) ≤ b i := fun i => (hp₀ i (mem_univ i)).1.trans (hp₀ i (mem_univ i)).2
  have heU : MapsTo (parScale e) smearU smearU := parScale_mapsTo (he 0) (he 3)
  obtain ⟨t₀, T, ha0, hab0, R, hbox'⟩ := exists_smearBox_of_compact
    ((GenUC.isCompact_ratBox a b).image (continuous_parScale e))
    (by rintro _ ⟨p, hp, rfl⟩; exact heU (hsub hp)) ⟨_, p₀, hp₀, rfl⟩
  have hbox : ∀ {p : Fin 4 → ℝ}, p ∈ GenUC.ratBox a b → parScale e p ∈ smearBox t₀ T R :=
    fun hp => hbox' ⟨_, hp, rfl⟩
  obtain ⟨CH, aH, hCH, haH, haH1, hH⟩ := hHol T
  obtain ⟨K₀, c₀, hF₀⟩ := genFam_smearFam hG left ha0 hab0 R hCH haH haH1 hH
  obtain ⟨K, c, hF⟩ := genFam_parScale hF₀ he (fun p hp => hbox hp)
  set D : Set (Fin 4 → ℝ) := ratPt '' {q | ratPt q ∈ GenUC.ratBox a b} with hD
  have hDc : D.Countable := (Set.to_countable _).image _
  have hDS : D ⊆ GenUC.ratBox a b := by rintro _ ⟨q, hq, rfl⟩; exact hq
  set Rs : Set ℝ := ((↑) : ℚ → ℝ) '' {r : ℚ | 0 ≤ r ∧ r ≤ 1} with hRs
  have hRc : Rs.Countable := (Set.to_countable _).image _
  have hRI : Rs ⊆ Icc 0 1 := by
    rintro _ ⟨r, hr, rfl⟩; exact ⟨by exact_mod_cast hr.1, by exact_mod_cast hr.2⟩
  set Φ : ℝ → (Fin 4 → ℝ) → Ω → ℝ := fun ρ p ω => evalReg (X ω) (smearFam W left (parScale e p) ρ)
    with hΦ
  have hid : ∀ ρ ∈ Rs, ∀ p ∈ D, ∀ᵐ ω ∂P,
      Φ ρ p ω = X ω (smearFam W left (parScale e p) ρ) + (fun _ _ => (0 : ℝ)) ρ p := by
    intro ρ hρ p hp
    filter_upwards [ae_evalReg_eq_smearFam hX hG left ha0 hab0 R (hbox (hDS hp)) (hRI hρ)]
      with ω h
    simp only [hΦ, h, add_zero]
  obtain ⟨Lim, -, hLe, hconv⟩ := GenUC.ae_unifConv_countable hX hF
    (GenUC.isLipRetr_ratBox hab) (GenUC.isCompact_ratBox a b) hDc hDS hRc hRI Φ
    (fun _ _ => 0) (fun _ => 0) continuousOn_const hid
    (fun ε hε => ⟨1, one_pos, fun _ _ _ _ _ => by simpa using hε⟩)
  have hq : ∀ᵐ ω ∂P, ∀ q : Fin 4 → ℚ, ratPt q ∈ GenUC.ratBox a b →
      Lim (ratPt q) ω = evalReg (X ω) (smearFam W left (parScale e (ratPt q)) 0) := by
    refine ae_all_iff.2 fun q => ?_
    by_cases hqb : ratPt q ∈ GenUC.ratBox a b
    · filter_upwards [hLe _ hqb, ae_evalReg_eq_smearFam hX hG left ha0 hab0 R (hbox hqb)
        ⟨le_rfl, zero_le_one⟩] with ω h1 h2
      intro _
      rw [h1, h2, add_zero]
    · exact ae_of_all _ fun ω h => absurd h hqb
  filter_upwards [hconv, hq] with ω hc hqω n
  obtain ⟨δ, hδ, hδc⟩ := hc (1 / ((n : ℝ) + 1)) (by positivity)
  obtain ⟨N, hN⟩ := exists_nat_one_div_lt (lt_min hδ one_pos)
  refine ⟨N, fun r hr0 hrN q hqb => ?_⟩
  have hrm : (r : ℝ) < min δ 1 := hrN.trans hN
  have hrR : (r : ℝ) ∈ Rs := ⟨r, ⟨hr0.le, by exact_mod_cast (hrm.trans_le (min_le_right _ _)).le⟩,
    rfl⟩
  have h := hδc r hrR (hrm.trans_le (min_le_left _ _)) (ratPt q) ⟨q, hqb, rfl⟩
  rw [hqω q hqb] at h
  exact h

/-- **Fixed-driver convergence of the dyadic pairings at rational parameters.** -/
theorem ae_smear_conv_fixed_e {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {X : Ω → FieldSample} (hX : IsFreeGFFModConstH X P) {W : ℝ → ℝ}
    (hG : G1zDrvGood W) (left : Bool) (e : Fin 4 → ℝ) :
    ∀ᵐ ω ∂P, ∀ q : Fin 4 → ℚ, parScale e (ratPt q) ∈ smearU → ∀ r : ℚ, 0 ≤ r → r ≤ 1 →
      Tendsto (fun k : ℕ => ∫ w, avgReg (X ω) k w ∂(smearFam W left (parScale e (ratPt q)) r)) atTop
        (𝓝 (evalReg (X ω) (smearFam W left (parScale e (ratPt q)) r))) := by
  have hqr : ∀ (q : Fin 4 → ℚ) (r : ℚ), ∀ᵐ ω ∂P, parScale e (ratPt q) ∈ smearU → 0 ≤ r → r ≤ 1 →
      Tendsto (fun k : ℕ => ∫ w, avgReg (X ω) k w ∂(smearFam W left (parScale e (ratPt q)) r)) atTop
        (𝓝 (evalReg (X ω) (smearFam W left (parScale e (ratPt q)) r))) := by
    intro q r
    by_cases hq : parScale e (ratPt q) ∈ smearU
    · by_cases hr : (0 : ℚ) ≤ r ∧ r ≤ 1
      · obtain ⟨R, hR⟩ := exists_smearBox_mem hq
        have hr' : (r : ℝ) ∈ Icc (0 : ℝ) 1 := ⟨by exact_mod_cast hr.1, by exact_mod_cast hr.2⟩
        obtain ⟨α, CF, Rs, hα, hfacts⟩ := smearFam_box_facts hG left hq.1 le_rfl R
        obtain ⟨hP, hsupp, hF⟩ := hfacts _ hR _ hr'
        filter_upwards [FrostmanReg.ae_tendsto_integral_avgReg_frostman hX hsupp hF hα,
          ae_evalReg_eq_smearFam hX hG left hq.1 le_rfl R hR hr'] with ω h1 h2
        intro _ _ _
        rw [h2]; exact h1
      · exact ae_of_all _ fun ω _ h1 h2 => absurd ⟨h1, h2⟩ hr
    · exact ae_of_all _ fun ω h => absurd h hq
  filter_upwards [ae_all_iff.2 fun q => ae_all_iff.2 fun r => hqr q r] with ω h q hq r h0 h1
  exact h q r hq h0 h1

/-- **The fixed-driver free-field inputs of `ratCauchy_Z_of_X`, on all rational boxes at once**
(countably many applications of `ae_smear_cauchy_fixed`, and `ae_smear_conv_fixed`), for a good
driver that is Hölder on every `[0, T]`. -/
theorem ae_smear_fixed_all_e {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {X : Ω → FieldSample} (hX : IsFreeGFFModConstH X P) {W : ℝ → ℝ}
    (hG : G1zDrvGood W) (left : Bool) {e : Fin 4 → ℝ} (he : ∀ i, 0 < e i)
    (hHol : ∀ T : ℝ, ∃ CH aH : ℝ, 0 ≤ CH ∧ 0 < aH ∧ aH ≤ 1 ∧
      ∀ x ∈ Icc (0 : ℝ) T, ∀ y ∈ Icc (0 : ℝ) T, |W x - W y| ≤ CH * |x - y| ^ aH) :
    ∀ᵐ ω ∂P, (∀ a b : Fin 4 → ℚ, GenUC.ratBox a b ⊆ smearU → ∀ n : ℕ, ∃ N : ℕ, ∀ r : ℚ,
        0 < r → (r : ℝ) < 1 / ((N : ℝ) + 1) → ∀ q : Fin 4 → ℚ, ratPt q ∈ GenUC.ratBox a b →
          |evalReg (X ω) (smearFam W left (parScale e (ratPt q)) r) -
            evalReg (X ω) (smearFam W left (parScale e (ratPt q)) 0)| < 1 / ((n : ℝ) + 1)) ∧
      ∀ q : Fin 4 → ℚ, parScale e (ratPt q) ∈ smearU → ∀ r : ℚ, 0 ≤ r → r ≤ 1 →
        Tendsto (fun k : ℕ => ∫ w, avgReg (X ω) k w ∂(smearFam W left (parScale e (ratPt q)) r)) atTop
          (𝓝 (evalReg (X ω) (smearFam W left (parScale e (ratPt q)) r))) := by
  have h1 : ∀ᵐ ω ∂P, ∀ ab : (Fin 4 → ℚ) × (Fin 4 → ℚ), GenUC.ratBox ab.1 ab.2 ⊆ smearU →
      ∀ n : ℕ, ∃ N : ℕ, ∀ r : ℚ, 0 < r → (r : ℝ) < 1 / ((N : ℝ) + 1) →
        ∀ q : Fin 4 → ℚ, ratPt q ∈ GenUC.ratBox ab.1 ab.2 →
          |evalReg (X ω) (smearFam W left (parScale e (ratPt q)) r) -
            evalReg (X ω) (smearFam W left (parScale e (ratPt q)) 0)| < 1 / ((n : ℝ) + 1) := by
    refine ae_all_iff.2 fun ab => ?_
    by_cases hsub : GenUC.ratBox ab.1 ab.2 ⊆ smearU
    · filter_upwards [ae_smear_cauchy_fixed_e hX hG left he hsub hHol] with ω hω
      exact fun _ => hω
    · exact ae_of_all _ fun ω h => absurd h hsub
  filter_upwards [h1, ae_smear_conv_fixed_e hX hG left e] with ω h1 h2
  exact ⟨fun a b hsub => h1 (a, b) hsub, h2⟩

end A1RS
end R18
end QuantumZipper
