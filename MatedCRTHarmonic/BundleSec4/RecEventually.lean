import MatedCRTHarmonic.GMS4.Prop210
import MatedCRTHarmonic.GMS4.CellGraphInterface
import MatedCRTHarmonic.MesoModel.RecAdmissible
import MatedCRTHarmonic.MesoModel.RecBridge
import MatedCRTHarmonic.Lemma38Source.Numerics
import MatedCRTHarmonic.BundleSec4.Prop210Source

/-!
# the recurrence input from ONE fixed-parameter Proposition 2.10 instance

HADM's `MesoModel.matedCRTRecurrencePathScaleInput_of_L27_G4_numeric` asks every positive dyadic index to make the three
recurrence tests admissible, which forces the margin `(1/2)^β < ρ ≤ rhoG4` and `C₀ ≥ 2(log((1/2)^β/ρ))^{-2}`. Since
`3β < q < 2/(2+γ)² ≤ 1/2`, this needs `rhoG4 > 2^{-1/6}` and a large `C₀`: a single G4 producer at the
recommended parameters `(rhoG4, C₀) = (3/4, 100)` (the one-scale estimate instance) cannot feed it.

Here the finitely many coarse scales are absorbed into the Lemma 2.7 constant instead (as the one-scale estimate's `OneScale` does for
Lemma 3.8): admissibility is only needed for `k ≥ k₀`, where `mesh k ^ β ≤ ρ e^{-2}`. Then **any** fixed
`rhoG4 ∈ (0, 1)` and `C₀ ≥ 16π` suffice:

* `bundle_recThreeAdmissible_of_small` — the three recurrence tests are admissible at one index `k ≥ 1` once
  `mesh k ^ β ≤ ρ e^{-2}`, from `16π ≤ C₀`, `3β ≤ betaG4`, `β' ≤ betaG4`;
* `bundle_matedCRTRecurrenceScaleInput_of_eventually` — HADM's `matedCRTRecurrenceScaleInput_of_L27_G4_fixed` with
  admissibility only for `k ≥ k₀` (constant `C27 + (mesh k₀ ^ α)⁻¹`);
* `bundle_matedCRTRecurrencePathScaleInput_of_fixed` — the recurrence path-scale input from L27 and ONE Proposition 2.10
  instance at arbitrary fixed `(rhoG4, C₀, betaG4)`, `rhoG4 ∈ (0, 1)`, `16π ≤ C₀`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Metric Filter Real
open scoped ENNReal NNReal

namespace MatedCRTHarmonic.BundleSec4

open MatedCRTHarmonic

/-- Dyadic meshes decrease with the index. -/
theorem bundle_mesh_anti {k j : ℕ} (h : k ≤ j) : CellFamily.mesh j ≤ CellFamily.mesh k := by
  unfold CellFamily.mesh
  exact zpow_le_zpow_right₀ (by norm_num : (1 : ℝ) ≤ 2) (by omega)

/-- `((ε^β)^n)⁻¹ ≤ ε^{-b}` when `nβ ≤ b` and `0 < ε ≤ 1`. -/
theorem bundle_invPower_le {ε β b : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) (n : ℕ) (hβ : (n : ℝ) * β ≤ b) :
    ((ε ^ β) ^ n)⁻¹ ≤ ε ^ (-b) := by
  have heq : ((ε ^ β) ^ n)⁻¹ = ε ^ (-(n : ℝ) * β) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hε.le, ← Real.rpow_neg hε.le]
    congr 1
    ring
  rw [heq]
  exact Real.rpow_le_rpow_of_exponent_ge hε hε1 (by linarith)

/-- **The three recurrence tests at one fine index.** With fixed Proposition 2.10 parameters
`(rho, C, betaG4)`, `ρ < ρ₁ ≤ rho < 1`, `16π ≤ C`, `3β ≤ betaG4`, `β' ≤ betaG4`, every index `k ≥ 1` with
`mesh k ^ β ≤ ρ e^{-2}` makes the three tests of `GMS3.Theorem14Inputs` admissible. -/
theorem bundle_recThreeAdmissible_of_small {k : ℕ} (hk : 1 ≤ k)
    {ρ ρ₁ β β' rho C betaG4 : ℝ}
    (hρ : 0 < ρ) (hρ₁ : ρ < ρ₁) (hρ₁rho : ρ₁ ≤ rho) (hrho1 : rho < 1) (hC : 16 * π ≤ C)
    (hbetaG4 : 0 < betaG4) (hβ : 0 < β) (hbeta3 : 3 * β ≤ betaG4) (hbetaPrime : β' ≤ betaG4)
    (hsmall : CellFamily.mesh k ^ β ≤ ρ * Real.exp (-2)) :
    GMS4.Prop210Admissible (CellFamily.mesh k) rho C betaG4
        (GMS3.annulusSet 0 (CellFamily.mesh k ^ β) ρ)
        (fun u => ‖fderiv ℝ (GMS3.logRad 0 ρ (CellFamily.mesh k ^ β)) u‖ ^ 2) ∧
      GMS4.Prop210Admissible (CellFamily.mesh k) rho C betaG4
        (GMS3.annulusSet 0 (CellFamily.mesh k ^ β) ρ) (fun _ => 1) ∧
      GMS4.Prop210Admissible (CellFamily.mesh k) rho C betaG4
        (ball 0 ρ₁) (GMS3.lemma34Layer (CellFamily.mesh k ^ β) ρ (CellFamily.mesh k ^ β')) := by
  have hε := GMSLemma27.mesh_pos k
  have hε1 := GMSLemma27.mesh_lt_one (by omega : k ≠ 0)
  have hs := Real.rpow_pos_of_pos hε β
  have hw := Real.rpow_pos_of_pos hε β'
  have hexp : Real.exp (-2) < 1 := Real.exp_lt_one_iff.mpr (by norm_num)
  have hsρ : CellFamily.mesh k ^ β < ρ := by
    calc
      CellFamily.mesh k ^ β ≤ ρ * Real.exp (-2) := hsmall
      _ < ρ * 1 := mul_lt_mul_of_pos_left hexp hρ
      _ = ρ := mul_one ρ
  -- `log (s/ρ) ≤ -2`, hence `(log (s/ρ))² ≥ 4`
  have hratio : 0 < CellFamily.mesh k ^ β / ρ := div_pos hs hρ
  have hratio_le : CellFamily.mesh k ^ β / ρ ≤ Real.exp (-2) := by
    rw [div_le_iff₀ hρ]
    linarith [mul_comm ρ (Real.exp (-2))]
  have hlog : Real.log (CellFamily.mesh k ^ β / ρ) ≤ -2 := by
    calc
      Real.log (CellFamily.mesh k ^ β / ρ) ≤ Real.log (Real.exp (-2)) := Real.log_le_log hratio hratio_le
      _ = -2 := Real.log_exp (-2)
  have hsq : 4 ≤ (Real.log (CellFamily.mesh k ^ β / ρ)) ^ 2 := by nlinarith
  have hsq0 : 0 < (Real.log (CellFamily.mesh k ^ β / ρ)) ^ 2 := by linarith
  have hlinv : ((Real.log (CellFamily.mesh k ^ β / ρ)) ^ 2)⁻¹ ≤ 1 / 4 := by
    rw [one_div]
    exact inv_anti₀ (by norm_num) hsq
  have hlinv0 : 0 ≤ ((Real.log (CellFamily.mesh k ^ β / ρ)) ^ 2)⁻¹ := by positivity
  have hC1 : 1 ≤ C := by nlinarith [Real.pi_gt_three]
  have hpowpos : 0 < CellFamily.mesh k ^ (-betaG4) := Real.rpow_pos_of_pos hε _
  have hOneAndLayer := MesoModel.recMeshOneAndLayer hC1 hbetaG4.le hbetaPrime
  have hM : ((Real.log (CellFamily.mesh k ^ β / ρ)) ^ 2 * (CellFamily.mesh k ^ β) ^ 2)⁻¹ ≤
      C * CellFamily.mesh k ^ (-betaG4) := by
    have hp2 : ((CellFamily.mesh k ^ β) ^ 2)⁻¹ ≤ CellFamily.mesh k ^ (-betaG4) :=
      bundle_invPower_le hε hε1.le 2 (by norm_num; linarith)
    calc
      ((Real.log (CellFamily.mesh k ^ β / ρ)) ^ 2 * (CellFamily.mesh k ^ β) ^ 2)⁻¹ =
          ((Real.log (CellFamily.mesh k ^ β / ρ)) ^ 2)⁻¹ * ((CellFamily.mesh k ^ β) ^ 2)⁻¹ := by
        rw [mul_inv_rev]; ring
      _ ≤ (1 / 4) * CellFamily.mesh k ^ (-betaG4) := mul_le_mul hlinv hp2 (by positivity) (by norm_num)
      _ ≤ C * CellFamily.mesh k ^ (-betaG4) := mul_le_mul_of_nonneg_right (by linarith) hpowpos.le
  have hL : 2 * ((Real.log (CellFamily.mesh k ^ β / ρ)) ^ 2 * (CellFamily.mesh k ^ β) ^ 3)⁻¹ ≤
      C * CellFamily.mesh k ^ (-betaG4) := by
    have hp3 : ((CellFamily.mesh k ^ β) ^ 3)⁻¹ ≤ CellFamily.mesh k ^ (-betaG4) :=
      bundle_invPower_le hε hε1.le 3 (by norm_num; linarith)
    calc
      2 * ((Real.log (CellFamily.mesh k ^ β / ρ)) ^ 2 * (CellFamily.mesh k ^ β) ^ 3)⁻¹ =
          2 * (((Real.log (CellFamily.mesh k ^ β / ρ)) ^ 2)⁻¹ * ((CellFamily.mesh k ^ β) ^ 3)⁻¹) := by
        rw [mul_inv_rev]; ring
      _ ≤ 2 * ((1 / 4) * CellFamily.mesh k ^ (-betaG4)) :=
        mul_le_mul_of_nonneg_left (mul_le_mul hlinv hp3 (by positivity) (by norm_num)) (by norm_num)
      _ ≤ C * CellFamily.mesh k ^ (-betaG4) := by nlinarith
  exact ⟨MesoModel.recAnnulusSqGrad_admissible hε hε1 hs hsρ (le_trans hρ₁.le hρ₁rho) hrho1 hC
      hbetaG4 hM hL,
    MesoModel.recAnnulusOne_admissible hε hε1 hs hsρ (le_trans hρ₁.le hρ₁rho) hrho1 hC hbetaG4
      (hOneAndLayer.1 k hk),
    MesoModel.recBallLayer_admissible hε hε1 (hρ.trans hρ₁) hρ₁rho hrho1 hC hbetaG4 hw
      (hOneAndLayer.1 k hk) (hOneAndLayer.2 k hk)⟩

/-- **HADM's recurrence scale input with admissibility only at fine scales.** As
`MesoModel.matedCRTRecurrenceScaleInput_of_L27_G4_fixed`, but the three tests need to be admissible only for
`k ≥ max k₀ 1`; the coarse scales are charged to probability `≤ 1` and absorbed into the Lemma 2.7 constant
`C27 + (mesh k₀ ^ α)⁻¹`. -/
theorem bundle_matedCRTRecurrenceScaleInput_of_eventually
    {γ : ℝ} (M : GMSLemma27.CellModel γ)
    (S : GMS4.MoTAdapter.CellModelGraphCoupling M)
    (hstd : StandardBorelSpace S.family.Ω)
    {ρ ρ₁ q β β' α A₀ Cfail rhoG4 C0 betaG4 : ℝ} (k₀ : ℕ)
    (hρ : 0 < ρ) (hρ₁ : ρ < ρ₁)
    (hβ : 0 < β) (hq : 3 * β < q) (hβ' : 2 * β < β') (hβ'q : β' ≤ q)
    (hα : 2 * β < α) (hA₀ : 0 ≤ A₀)
    (h27 : ∃ C27 : ℝ, 0 ≤ C27 ∧ ∀ k : ℕ,
      S.toRandomCellFamily.P
        {ω | GMS3.CellDiamBound (S.toRandomCellFamily.H k ω) ρ₁
          (CellFamily.mesh k ^ q)}ᶜ ≤ ENNReal.ofReal (C27 * CellFamily.mesh k ^ α))
    (h210 : ∀ k (D : Set ℂ) (f : ℂ → ℝ),
      GMS4.Prop210Admissible (CellFamily.mesh k) rhoG4 C0 betaG4 D f →
        S.toRandomCellFamily.P
          (GMS4.Prop210Bad S.toRandomCellFamily k D f (2 * A₀)
            (CellFamily.mesh k ^ α)) ≤
          ENNReal.ofReal (Cfail * CellFamily.mesh k ^ α))
    (hCfail : 0 ≤ Cfail)
    (hAdm : ∀ k : ℕ, k₀ ≤ k → 1 ≤ k →
      GMS4.Prop210Admissible (CellFamily.mesh k) rhoG4 C0 betaG4
        (GMS3.annulusSet 0 (CellFamily.mesh k ^ β) ρ)
        (fun u => ‖fderiv ℝ (GMS3.logRad 0 ρ (CellFamily.mesh k ^ β)) u‖ ^ 2) ∧
      GMS4.Prop210Admissible (CellFamily.mesh k) rhoG4 C0 betaG4
        (GMS3.annulusSet 0 (CellFamily.mesh k ^ β) ρ) (fun _ => 1) ∧
      GMS4.Prop210Admissible (CellFamily.mesh k) rhoG4 C0 betaG4
        (ball 0 ρ₁)
        (GMS3.lemma34Layer (CellFamily.mesh k ^ β) ρ (CellFamily.mesh k ^ β'))) :
    MesoModel.MatedCRTRecurrenceScaleInput γ := by
  rcases h27 with ⟨C27, hC27, h27⟩
  have hα0 : 0 < α := by linarith
  have hK0 : 0 < CellFamily.mesh k₀ ^ α := Real.rpow_pos_of_pos (bundle_mesh_pos k₀) α
  let K : ℝ := (CellFamily.mesh k₀ ^ α)⁻¹
  have hK : 0 ≤ K := inv_nonneg.mpr hK0.le
  let C : CellFamily.MultigraphCoupledRandomFamily γ :=
    CellFamily.MultigraphCoupledRandomFamily.ofMultigraph S.family S.bm
      (fun ω x => M.cell 1 (S.modelMap ω) x) S.coupling S.meshGraph_eq
  refine ⟨C, hstd, ρ, ρ₁, q, β, β', α, 2 * A₀, C27 + K, Cfail,
    hρ, hρ₁, hβ, hq, hβ', hβ'q, hα, by positivity, by positivity, hCfail, ?_⟩
  intro k
  let F := S.toRandomCellFamily
  change F.P {ω | ¬ GMS3.Theorem14Inputs (F.H k ω) (CellFamily.mesh k) ρ ρ₁ q β β' α (2 * A₀)} ≤
    ENNReal.ofReal ((C27 + K) * CellFamily.mesh k ^ α) + ENNReal.ofReal (Cfail * CellFamily.mesh k ^ α) +
      ENNReal.ofReal (Cfail * CellFamily.mesh k ^ α) + ENNReal.ofReal (Cfail * CellFamily.mesh k ^ α)
  have hmeshα0 : 0 ≤ CellFamily.mesh k ^ α := Real.rpow_nonneg (bundle_mesh_pos k).le α
  by_cases hk : k₀ ≤ k ∧ 1 ≤ k
  · -- fine scales: the four-event union bound
    obtain ⟨hk₀, hk1⟩ := hk
    let B27 : Set F.Ω := {ω | GMS3.CellDiamBound (F.H k ω) ρ₁ (CellFamily.mesh k ^ q)}ᶜ
    let Bf : Set F.Ω := {ω | GMS3.Prop210Bound (F.H k ω)
      (GMS3.annulusSet 0 (CellFamily.mesh k ^ β) ρ)
      (fun u => ‖fderiv ℝ (GMS3.logRad 0 ρ (CellFamily.mesh k ^ β)) u‖ ^ 2)
      (2 * A₀) (CellFamily.mesh k ^ α)}ᶜ
    let B1 : Set F.Ω := {ω | GMS3.Prop210Bound (F.H k ω)
      (GMS3.annulusSet 0 (CellFamily.mesh k ^ β) ρ) (fun _ => 1)
      (2 * A₀) (CellFamily.mesh k ^ α)}ᶜ
    let Bg : Set F.Ω := {ω | GMS3.Prop210Bound (F.H k ω)
      (ball 0 ρ₁) (GMS3.lemma34Layer (CellFamily.mesh k ^ β) ρ
        (CellFamily.mesh k ^ β')) (2 * A₀) (CellFamily.mesh k ^ α)}ᶜ
    have hbadSubset :
        {ω | ¬ GMS3.Theorem14Inputs (F.H k ω) (CellFamily.mesh k) ρ ρ₁ q β β' α (2 * A₀)} ⊆
          B27 ∪ Bf ∪ B1 ∪ Bg := by
      intro ω hω
      have hparts :
          ¬ GMS3.CellDiamBound (F.H k ω) ρ₁ (CellFamily.mesh k ^ q) ∨
          ¬ GMS3.Prop210Bound (F.H k ω)
            (GMS3.annulusSet 0 (CellFamily.mesh k ^ β) ρ)
            (fun u => ‖fderiv ℝ (GMS3.logRad 0 ρ (CellFamily.mesh k ^ β)) u‖ ^ 2)
            (2 * A₀) (CellFamily.mesh k ^ α) ∨
          ¬ GMS3.Prop210Bound (F.H k ω)
            (GMS3.annulusSet 0 (CellFamily.mesh k ^ β) ρ) (fun _ => 1)
            (2 * A₀) (CellFamily.mesh k ^ α) ∨
          ¬ GMS3.Prop210Bound (F.H k ω)
            (ball 0 ρ₁) (GMS3.lemma34Layer (CellFamily.mesh k ^ β) ρ
              (CellFamily.mesh k ^ β')) (2 * A₀) (CellFamily.mesh k ^ α) := by
        by_contra hparts
        push Not at hparts
        apply hω
        simpa only [GMS3.Theorem14Inputs] using hparts
      rcases hparts with h | h | h | h
      · exact Or.inl (Or.inl (Or.inl (by simpa [B27] using h)))
      · exact Or.inl (Or.inl (Or.inr (by simpa [Bf] using h)))
      · exact Or.inl (Or.inr (by simpa [B1] using h))
      · exact Or.inr (by simpa [Bg] using h)
    have hbad27 : F.P B27 ≤ ENNReal.ofReal (C27 * CellFamily.mesh k ^ α) := by
      simpa [B27, F] using h27 k
    have hbadf : F.P Bf ≤ ENNReal.ofReal (Cfail * CellFamily.mesh k ^ α) := by
      simpa [Bf, F, GMS4.Prop210Bad, GMS4.Prop210Good] using
        h210 k (GMS3.annulusSet 0 (CellFamily.mesh k ^ β) ρ)
          (fun u => ‖fderiv ℝ (GMS3.logRad 0 ρ (CellFamily.mesh k ^ β)) u‖ ^ 2)
          (hAdm k hk₀ hk1).1
    have hbad1 : F.P B1 ≤ ENNReal.ofReal (Cfail * CellFamily.mesh k ^ α) := by
      simpa [B1, F, GMS4.Prop210Bad, GMS4.Prop210Good] using
        h210 k (GMS3.annulusSet 0 (CellFamily.mesh k ^ β) ρ) (fun _ => 1)
          (hAdm k hk₀ hk1).2.1
    have hbadg : F.P Bg ≤ ENNReal.ofReal (Cfail * CellFamily.mesh k ^ α) := by
      simpa [Bg, F, GMS4.Prop210Bad, GMS4.Prop210Good] using
        h210 k (ball 0 ρ₁)
          (GMS3.lemma34Layer (CellFamily.mesh k ^ β) ρ (CellFamily.mesh k ^ β'))
          (hAdm k hk₀ hk1).2.2
    have hmono27 : ENNReal.ofReal (C27 * CellFamily.mesh k ^ α) ≤
        ENNReal.ofReal ((C27 + K) * CellFamily.mesh k ^ α) :=
      ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right (by linarith) hmeshα0)
    calc
      F.P {ω | ¬ GMS3.Theorem14Inputs (F.H k ω) (CellFamily.mesh k) ρ ρ₁ q β β' α (2 * A₀)} ≤
          F.P (B27 ∪ Bf ∪ B1 ∪ Bg) := measure_mono hbadSubset
      _ ≤ ((F.P B27 + F.P Bf) + F.P B1) + F.P Bg := by
        calc
          F.P (B27 ∪ Bf ∪ B1 ∪ Bg) ≤ F.P (B27 ∪ Bf ∪ B1) + F.P Bg := measure_union_le _ _
          _ ≤ (F.P (B27 ∪ Bf) + F.P B1) + F.P Bg :=
            add_le_add (measure_union_le _ _) le_rfl
          _ ≤ ((F.P B27 + F.P Bf) + F.P B1) + F.P Bg :=
            add_le_add (add_le_add (measure_union_le _ _) le_rfl) le_rfl
      _ ≤ _ := add_le_add (add_le_add (add_le_add (hbad27.trans hmono27) hbadf) hbad1) hbadg
  · -- coarse scales: probability `≤ 1 ≤ K · mesh k ^ α`
    have hkk₀ : k ≤ k₀ ∨ k = 0 := by
      by_contra hcon
      push Not at hcon
      exact hk ⟨hcon.1.le, Nat.one_le_iff_ne_zero.mpr hcon.2⟩
    have hmesh : CellFamily.mesh k₀ ^ α ≤ CellFamily.mesh k ^ α := by
      rcases hkk₀ with h | h
      · exact Real.rpow_le_rpow (bundle_mesh_pos k₀).le (bundle_mesh_anti h) hα0.le
      · subst h
        exact Real.rpow_le_rpow (bundle_mesh_pos k₀).le (bundle_mesh_anti (Nat.zero_le k₀)) hα0.le
    have hone : (1 : ℝ) ≤ (C27 + K) * CellFamily.mesh k ^ α := by
      have h1 : 1 ≤ K * CellFamily.mesh k ^ α := by
        calc
          (1 : ℝ) = K * CellFamily.mesh k₀ ^ α := (inv_mul_cancel₀ hK0.ne').symm
          _ ≤ K * CellFamily.mesh k ^ α := mul_le_mul_of_nonneg_left hmesh hK
      nlinarith
    calc
      F.P {ω | ¬ GMS3.Theorem14Inputs (F.H k ω) (CellFamily.mesh k) ρ ρ₁ q β β' α (2 * A₀)} ≤ 1 :=
        prob_le_one
      _ = ENNReal.ofReal 1 := ENNReal.ofReal_one.symm
      _ ≤ ENNReal.ofReal ((C27 + K) * CellFamily.mesh k ^ α) := ENNReal.ofReal_le_ofReal hone
      _ ≤ _ := le_add_of_le_of_nonneg (le_add_of_le_of_nonneg
          (le_add_of_le_of_nonneg le_rfl bot_le) bot_le) bot_le

end MatedCRTHarmonic.BundleSec4
