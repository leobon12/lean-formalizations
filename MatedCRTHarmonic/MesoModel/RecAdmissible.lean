import MatedCRTHarmonic.GMS4.Prop210
import MatedCRTHarmonic.GMS3.Lemma34
import MatedCRTHarmonic.GMSLemma27.Consumers

/-!
# Deterministic test-pair admissibility for the recurrence adapter

The tests are the three functions in GMS3's Theorem 1.4 input. The inequalities below expose the
numerical margins needed by GMS4's Proposition 2.10 admissibility predicate.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Metric Real
open scoped ENNReal

namespace MatedCRTHarmonic.MesoModel

open MatedCRTHarmonic.GMS3

private theorem recAnnulusConnected {s ρ : ℝ} (hs : 0 < s) (hsρ : s < ρ) :
    IsConnected (annulusSet 0 s ρ) := by
  let S : Set (ℝ × ℂ) := Ioo s ρ ×ˢ sphere (0 : ℂ) 1
  let f : ℝ × ℂ → ℂ := fun p => (p.1 : ℂ) * p.2
  have hRank : 1 < Module.rank ℝ ℂ := by
    rw [Complex.rank_real_complex]
    norm_num
  have hS : IsConnected S :=
    (isConnected_Ioo hsρ).prod
      (isConnected_sphere hRank 0 (by norm_num : 0 ≤ (1 : ℝ)))
  have hf : Continuous f := by fun_prop
  have himage : f '' S = annulusSet 0 s ρ := by
    ext z
    constructor
    · rintro ⟨⟨t, u⟩, ⟨ht, hu⟩, rfl⟩
      have huNorm : ‖u‖ = 1 := mem_sphere_zero_iff_norm.mp hu
      have htNorm : ‖(t : ℂ)‖ = t := by
        rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (lt_trans hs ht.1)]
      change s < ‖(t : ℂ) * u - 0‖ ∧ ‖(t : ℂ) * u - 0‖ < ρ
      simpa only [sub_zero, norm_mul, htNorm, huNorm, mul_one, mem_Ioo] using ht
    · intro hz
      have hzne : z ≠ 0 := by
        intro h
        subst z
        have : s < 0 := by simpa only [sub_zero, norm_zero] using hz.1
        linarith
      let t : ℝ := ‖z‖
      have htpos : 0 < t := norm_pos_iff.mpr hzne
      let u : ℂ := (t : ℂ)⁻¹ * z
      have hu : u ∈ sphere (0 : ℂ) 1 := by
        rw [mem_sphere_zero_iff_norm]
        dsimp [u]
        rw [norm_mul, norm_inv, Complex.norm_real, Real.norm_eq_abs,
          abs_of_pos htpos]
        exact inv_mul_cancel₀ htpos.ne'
      refine ⟨(t, u), ⟨⟨?_, ?_⟩, hu⟩, ?_⟩
      · simpa only [t, sub_zero] using hz.1
      · simpa only [t, sub_zero] using hz.2
      · dsimp [f, u, t]
        rw [← mul_assoc, mul_inv_cancel₀]
        · simp
        · exact_mod_cast (norm_ne_zero_iff.mpr hzne)
  rw [← himage]
  exact hS.image f hf.continuousOn

private theorem recAnnulusFrontierVolume {s ρ C : ℝ}
    (hs : 0 ≤ s) (hsρ : s ≤ ρ) (hρ : ρ < 1)
    (hC : 16 * π ≤ C) (r : ℝ) (hr : r ∈ Ioo (0 : ℝ) 1) :
    volume (thickening r (frontier (annulusSet 0 s ρ))) ≤
      ENNReal.ofReal (C * r) := by
  have hsub : thickening r (frontier (annulusSet 0 s ρ)) ⊆
      {u : ℂ | |‖u‖ - s| < r} ∪ {u : ℂ | |‖u‖ - ρ| < r} := by
    intro u hu
    obtain ⟨v, hv, huv⟩ := mem_thickening_iff.mp hu
    rcases frontier_annulusSet_subset 0 s ρ hv with h | h
    · left
      have hv' : ‖v‖ = s := by simpa only [sub_zero] using h
      have hn := abs_norm_sub_norm_le u v
      have hd : ‖u - v‖ < r := by simpa only [dist_eq_norm] using huv
      simpa only [mem_ofPred_eq, hv'] using lt_of_le_of_lt hn hd
    · right
      have hv' : ‖v‖ = ρ := by simpa only [sub_zero] using h
      have hn := abs_norm_sub_norm_le u v
      have hd : ‖u - v‖ < r := by simpa only [dist_eq_norm] using huv
      simpa only [mem_ofPred_eq, hv'] using lt_of_le_of_lt hn hd
  calc
    volume (thickening r (frontier (annulusSet 0 s ρ))) ≤
        volume ({u : ℂ | |‖u‖ - s| < r} ∪ {u : ℂ | |‖u‖ - ρ| < r}) :=
      measure_mono hsub
    _ ≤ volume {u : ℂ | |‖u‖ - s| < r} +
        volume {u : ℂ | |‖u‖ - ρ| < r} := measure_union_le _ _
    _ ≤ ENNReal.ofReal (4 * π * r * (s + r)) +
        ENNReal.ofReal (4 * π * r * (ρ + r)) := by
      have h1 := volume_radialShell_le (z := (0 : ℂ)) (a := s) (r := r) hs hr.1.le
      have h2 := volume_radialShell_le (z := (0 : ℂ)) (a := ρ) (r := r)
        (hs.trans hsρ) hr.1.le
      exact add_le_add (by simpa only [sub_zero] using h1)
        (by simpa only [sub_zero] using h2)
    _ ≤ ENNReal.ofReal (C * r) := by
      have hr0 : 0 ≤ r := hr.1.le
      have hs0 : 0 ≤ s + r := add_nonneg hs hr0
      have hρ0 : 0 ≤ ρ + r := add_nonneg (hs.trans hsρ) hr0
      have hp0 : 0 ≤ 4 * π * r * (s + r) := by positivity
      have hp1 : 0 ≤ 4 * π * r * (ρ + r) := by positivity
      rw [← ENNReal.ofReal_add hp0] <;> try exact hp1
      apply ENNReal.ofReal_le_ofReal
      have hfac : 0 ≤ 4 * π * r := by positivity
      have hr1 : r < 1 := hr.2
      calc
        4 * π * r * (s + r) + 4 * π * r * (ρ + r) ≤
            4 * π * r * 2 + 4 * π * r * 2 := by
          exact add_le_add
            (mul_le_mul_of_nonneg_left (by linarith) hfac)
            (mul_le_mul_of_nonneg_left (by linarith) hfac)
        _ = 16 * π * r := by ring
        _ ≤ C * r := mul_le_mul_of_nonneg_right hC hr.1.le

private theorem recBallFrontierVolume {ρ C : ℝ} (hρ : 0 ≤ ρ) (hρ1 : ρ < 1)
    (hC : 16 * π ≤ C) (r : ℝ) (hr : r ∈ Ioo (0 : ℝ) 1) :
    volume (thickening r (frontier (ball (0 : ℂ) ρ))) ≤ ENNReal.ofReal (C * r) := by
  have hsub : thickening r (frontier (ball (0 : ℂ) ρ)) ⊆
      {u : ℂ | |‖u‖ - ρ| < r} := by
    intro u hu
    obtain ⟨v, hv, huv⟩ := mem_thickening_iff.mp hu
    have hv' : ‖v‖ = ρ := by
      simpa only [mem_sphere_iff_norm, sub_zero] using
        (frontier_ball_subset_sphere hv)
    have hn := abs_norm_sub_norm_le u v
    have hd : ‖u - v‖ < r := by simpa only [dist_eq_norm] using huv
    simpa only [mem_ofPred_eq, hv'] using lt_of_le_of_lt hn hd
  calc
    volume (thickening r (frontier (ball (0 : ℂ) ρ))) ≤
      volume {u : ℂ | |‖u‖ - ρ| < r} := measure_mono hsub
    _ ≤ ENNReal.ofReal (4 * π * r * (ρ + r)) := by
      simpa only [sub_zero] using
        (volume_radialShell_le (z := (0 : ℂ)) (a := ρ) (r := r) hρ hr.1.le)
    _ ≤ ENNReal.ofReal (C * r) := by
      apply ENNReal.ofReal_le_ofReal
      have hr0 : 0 ≤ r := hr.1.le
      have hr1 : r < 1 := hr.2
      have hfac : 0 ≤ 4 * π * r := by positivity
      calc
        4 * π * r * (ρ + r) ≤ 4 * π * r * 2 :=
          mul_le_mul_of_nonneg_left (by linarith) hfac
        _ = 8 * π * r := by ring
        _ ≤ C * r := mul_le_mul_of_nonneg_right (by nlinarith [Real.pi_pos]) hr.1.le

/-- Proposition 2.10 admissibility for the squared gradient test on the recurrence annulus.
The two scale inequalities are the direct numerical bounds for this test and its Lipschitz
constant; they can be specialized using the intended exponents. -/
theorem recAnnulusSqGrad_admissible {ε s ρ rho C beta : ℝ}
    (hε : 0 < ε) (hε1 : ε < 1) (hs : 0 < s) (hsρ : s < ρ)
    (hρrho : ρ ≤ rho) (hrho1 : rho < 1) (hC : 16 * π ≤ C) (hbeta : 0 < beta)
    (hM : ((Real.log (s / ρ)) ^ 2 * s ^ 2)⁻¹ ≤ C * ε ^ (-beta))
    (hL : 2 * ((Real.log (s / ρ)) ^ 2 * s ^ 3)⁻¹ ≤ C * ε ^ (-beta)) :
    MatedCRTHarmonic.GMS4.Prop210Admissible ε rho C beta
      (annulusSet 0 s ρ)
      (fun u => ‖fderiv ℝ (logRad 0 ρ s) u‖ ^ 2) := by
  have hρ : 0 < ρ := hs.trans hsρ
  have hrho : 0 < rho := hρ.trans_le hρrho
  have hC1 : 1 < C := by nlinarith [Real.pi_gt_three]
  refine ⟨hε, hε1, hrho, hrho1, hC1, hbeta,
    isOpen_annulusSet 0 s ρ, recAnnulusConnected hs hsρ,
    (annulusSet_subset_ball 0 s ρ).trans (ball_subset_ball hρrho),
    ?_, ?_, ?_⟩
  · intro r hr
    exact recAnnulusFrontierVolume hs.le hsρ.le (hρrho.trans_lt hrho1) hC r hr
  · intro z hz
    have hz' : s ≤ ‖z - 0‖ := hz.1.le
    have hbound := sqGrad_le (z := (0 : ℂ)) (a := ρ) (b := s)
      (c := s) hs hz'
    exact ⟨by positivity, hbound.trans hM⟩
  · intro z hz w hw
    have hz' : s ≤ ‖z - 0‖ := hz.1.le
    have hw' : s ≤ ‖w - 0‖ := hw.1.le
    have hcoef :
        2 * ((Real.log (s / ρ)) ^ 2 * s ^ 3)⁻¹ * dist z w ≤
          (C * ε ^ (-beta)) * dist z w :=
      mul_le_mul_of_nonneg_right hL dist_nonneg
    have hzw := sqGrad_le_add (z := (0 : ℂ)) (a := ρ) (b := s)
      (c := s) hs hz' hw'
    have hwz := sqGrad_le_add (z := (0 : ℂ)) (a := ρ) (b := s)
      (c := s) hs hw' hz'
    rw [dist_comm] at hwz
    apply abs_le.mpr
    constructor <;> linarith

/-- Proposition 2.10 admissibility for the constant test on the recurrence annulus. -/
theorem recAnnulusOne_admissible {ε s ρ rho C beta : ℝ}
    (hε : 0 < ε) (hε1 : ε < 1) (hs : 0 < s) (hsρ : s < ρ)
    (hρrho : ρ ≤ rho) (hrho1 : rho < 1) (hC : 16 * π ≤ C) (hbeta : 0 < beta)
    (hOne : 1 ≤ C * ε ^ (-beta)) :
    MatedCRTHarmonic.GMS4.Prop210Admissible ε rho C beta
      (annulusSet 0 s ρ) (fun _ => 1) := by
  have hρ : 0 < ρ := hs.trans hsρ
  have hrho : 0 < rho := hρ.trans_le hρrho
  have hC1 : 1 < C := by nlinarith [Real.pi_gt_three]
  refine ⟨hε, hε1, hrho, hrho1, hC1, hbeta,
    isOpen_annulusSet 0 s ρ, recAnnulusConnected hs hsρ,
    (annulusSet_subset_ball 0 s ρ).trans (ball_subset_ball hρrho),
    ?_, ?_, ?_⟩
  · intro r hr
    exact recAnnulusFrontierVolume hs.le hsρ.le (hρrho.trans_lt hrho1) hC r hr
  · intro z hz
    exact ⟨by norm_num, hOne⟩
  · intro z hz w hw
    simp only [sub_self, abs_zero]
    positivity

/-- Proposition 2.10 admissibility for the two-circle boundary layer on the outer ball. -/
theorem recBallLayer_admissible {ε s ρ ρ₁ w rho C beta : ℝ}
    (hε : 0 < ε) (hε1 : ε < 1) (hρ₁ : 0 < ρ₁)
    (hρ₁rho : ρ₁ ≤ rho) (hrho1 : rho < 1) (hC : 16 * π ≤ C)
    (hbeta : 0 < beta) (hw : 0 < w)
    (hOne : 1 ≤ C * ε ^ (-beta)) (hLip : w⁻¹ ≤ C * ε ^ (-beta)) :
    MatedCRTHarmonic.GMS4.Prop210Admissible ε rho C beta
      (ball 0 ρ₁) (lemma34Layer s ρ w) := by
  have hrho : 0 < rho := hρ₁.trans_le hρ₁rho
  have hC1 : 1 < C := by nlinarith [Real.pi_gt_three]
  have hLips : LipschitzWith (Real.toNNReal w⁻¹) (lemma34Layer s ρ w) := by
    unfold lemma34Layer
    simpa only [max_self] using
      (lipschitzWith_radialBump 0 s hw).max (lipschitzWith_radialBump 0 ρ hw)
  refine ⟨hε, hε1, hrho, hrho1, hC1, hbeta,
    isOpen_ball, isConnected_ball hρ₁, ball_subset_ball hρ₁rho,
    ?_, ?_, ?_⟩
  · intro r hr
    exact recBallFrontierVolume hρ₁.le (hρ₁rho.trans_lt hrho1) hC r hr
  · intro z hz
    have hnonneg : 0 ≤ lemma34Layer s ρ w z := by
      unfold lemma34Layer
      exact le_trans (radialBump_nonneg 0 s w z) (le_max_left _ _)
    have hle : lemma34Layer s ρ w z ≤ 1 := by
      unfold lemma34Layer
      exact max_le (radialBump_le_one 0 s w z) (radialBump_le_one 0 ρ w z)
    exact ⟨hnonneg, hle.trans hOne⟩
  · intro z hz v hv
    have hdist := hLips.dist_le_mul z v
    rw [Real.dist_eq, Real.coe_toNNReal _ (inv_nonneg.mpr hw.le)] at hdist
    exact hdist.trans (mul_le_mul_of_nonneg_right hLip dist_nonneg)

/-- The constant and boundary-layer growth inequalities follow from the selected exponent. -/
theorem recMeshOneAndLayer {β' betaG4 C : ℝ}
    (hC : 1 ≤ C) (hbeta : 0 ≤ betaG4) (hβ' : β' ≤ betaG4) :
    (∀ k : ℕ, 1 ≤ k → 1 ≤ C * CellFamily.mesh k ^ (-betaG4)) ∧
    (∀ k : ℕ, 1 ≤ k →
      (CellFamily.mesh k ^ β')⁻¹ ≤ C * CellFamily.mesh k ^ (-betaG4)) := by
  constructor
  · intro k hk
    have hε := GMSLemma27.mesh_pos k
    have hε1 := (GMSLemma27.mesh_lt_one (by omega : k ≠ 0)).le
    have hpow : 1 ≤ CellFamily.mesh k ^ (-betaG4) :=
      Real.one_le_rpow_of_pos_of_le_one_of_nonpos hε hε1 (neg_nonpos.mpr hbeta)
    calc
      (1 : ℝ) ≤ CellFamily.mesh k ^ (-betaG4) := hpow
      _ = 1 * CellFamily.mesh k ^ (-betaG4) := by ring
      _ ≤ C * CellFamily.mesh k ^ (-betaG4) :=
        mul_le_mul_of_nonneg_right hC (Real.rpow_nonneg hε.le _)

  · intro k hk
    have hε := GMSLemma27.mesh_pos k
    have hε1 := (GMSLemma27.mesh_lt_one (by omega : k ≠ 0)).le
    calc
      (CellFamily.mesh k ^ β')⁻¹ = CellFamily.mesh k ^ (-β') :=
        (Real.rpow_neg hε.le β').symm
      _ ≤ CellFamily.mesh k ^ (-betaG4) :=
        Real.rpow_le_rpow_of_exponent_ge hε hε1 (by linarith)
      _ = 1 * CellFamily.mesh k ^ (-betaG4) := by ring
      _ ≤ C * CellFamily.mesh k ^ (-betaG4) :=
        mul_le_mul_of_nonneg_right hC (Real.rpow_nonneg hε.le _)

end MatedCRTHarmonic.MesoModel
