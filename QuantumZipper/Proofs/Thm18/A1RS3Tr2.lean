import QuantumZipper.Proofs.Thm18.A1RS3Tr
import QuantumZipper.Proofs.Thm18.A1RS3Main

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# A1RS3 (10): `A1RSFreeBrownStmt` from the measurability of the `Ψ`-smeared pairings

**`a1rsFreeBrownStmt_of_meas : A1RSSmearMeasStmt → A1RSFreeBrownStmt`**, hence
`a1rfSmearContStmt_of_meas : A1RSSmearMeasStmt → A1RFSmearContStmt`. See A1RS3Tr.lean.
Own bookkeeping (Fubini for the independent pair `CharFunRhs.ae_indep_ae`).
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Metric
open scoped Topology NNReal

namespace QuantumZipper
namespace R18
namespace A1RS

open Thm18Asm

theorem measurable_prop_lt {α : Type*} [MeasurableSpace α] {f : α → ℝ} (hf : Measurable f)
    (c : ℝ) : Measurable fun a => f a < c :=
  measurableSet_setOfPred.1 (measurableSet_lt hf measurable_const)

/-- **The free-field estimate along an independent Brownian driver, from measurability.** -/
theorem a1rsFreeBrownStmt_of_meas (hM : A1RSSmearMeasStmt) : A1RSFreeBrownStmt := by
  intro κ hκ hκ4 Ω _ P _ B X hB hX hind left
  obtain ⟨γ, hγ, hγ2, rfl⟩ : ∃ γ : ℝ, 0 < γ ∧ γ < 2 ∧ γ ^ 2 = κ :=
    ⟨Real.sqrt κ, Real.sqrt_pos.2 hκ, F2.sqrt_lt_two_of' hκ hκ4, Real.sq_sqrt hκ.le⟩
  obtain ⟨Ψ, hΨ⟩ := g1PsiSelStmt γ hγ hγ2
  choose F hFm hFeq using fun (p : Fin 4 → ℝ) (ρ : ℝ) (k : ℕ) => hM γ hγ hγ2 Ψ hΨ left p ρ k
  set Ev : (Fin 4 → ℚ) → ℚ → (ℝ≥0 → ℝ) × FieldSample → ℝ :=
    fun q r z => limUnder atTop fun k => F (ratPt q) r k z with hEv
  have hEvm : ∀ q r, Measurable (Ev q r) := fun q r =>
    (StronglyMeasurable.limUnder (l := atTop) (f := fun k z => F (ratPt q) r k z)
      fun k => (hFm _ _ k).stronglyMeasurable).measurable
  set E : Set ((ℝ≥0 → ℝ) × FieldSample) := {z |
    (∀ a b : Fin 4 → ℚ, GenUC.ratBox a b ⊆ smearU → ∀ n : ℕ, ∃ N : ℕ, ∀ r : ℚ, 0 < r →
      (r : ℝ) < 1 / ((N : ℝ) + 1) → ∀ q : Fin 4 → ℚ, ratPt q ∈ GenUC.ratBox a b →
        |Ev q r z - Ev q 0 z| < 1 / ((n : ℝ) + 1)) ∧
    ∀ q : Fin 4 → ℚ, ratPt q ∈ smearU → ∀ r : ℚ, 0 ≤ r → r ≤ 1 → ∀ n : ℕ, ∃ N : ℕ, ∀ k : ℕ,
      N ≤ k → |F (ratPt q) r k z - Ev q r z| < 1 / ((n : ℝ) + 1)} with hEdef
  have hE : MeasurableSet E := by
    refine measurableSet_setOfPred.2 (Measurable.and ?_ ?_)
    · refine Measurable.forall fun a => Measurable.forall fun b => DrvGood.measurable_imp_const
        fun _ => Measurable.forall fun n => Measurable.exists fun N => Measurable.forall fun r =>
          DrvGood.measurable_imp_const fun _ => DrvGood.measurable_imp_const fun _ =>
            Measurable.forall fun q => DrvGood.measurable_imp_const fun _ => ?_
      exact measurable_prop_lt (f := fun z => |Ev q r z - Ev q 0 z|)
        (continuous_abs.measurable.comp ((hEvm q r).sub (hEvm q 0))) _
    · refine Measurable.forall fun q => DrvGood.measurable_imp_const fun _ =>
        Measurable.forall fun r => DrvGood.measurable_imp_const fun _ =>
          DrvGood.measurable_imp_const fun _ => Measurable.forall fun n =>
            Measurable.exists fun N => Measurable.forall fun k =>
              DrvGood.measurable_imp_const fun _ => ?_
      exact measurable_prop_lt (f := fun z => |F (ratPt q) r k z - Ev q r z|)
        (continuous_abs.measurable.comp ((hFm _ _ k).sub (hEvm q r))) _
  -- the bridge on good paths
  have hbridge : ∀ a : ℝ≥0 → ℝ, Continuous a → G1zDrvGood (pathDrive (γ ^ 2) a) →
      ∃ e : Fin 4 → ℝ, (∀ i, 0 < e i) ∧ ∀ y : FieldSample, ∀ q : Fin 4 → ℚ, ratPt q ∈ smearU →
        ∀ r : ℚ, 0 ≤ r → r ≤ 1 → (∀ k : ℕ, F (ratPt q) r k (a, y) =
          ∫ w, avgReg y k w ∂(smearFam (pathDrive (γ ^ 2) a) left (parScale e (ratPt q)) r)) ∧
          Ev q r (a, y) = evalReg y (smearFam (pathDrive (γ ^ 2) a) left (parScale e (ratPt q)) r)
          := by
    intro a hc hG
    have hs : IsSimpleChord (pathTrace (γ ^ 2) a) := hG.2.2.2.1
    obtain ⟨φ, hφ, hΨa⟩ := hΨ.2.2 a hc hs left
    have hUn := G1ZA1a.isNormalizedUniformizer_sideDom hs left
    obtain ⟨β, hβ, hdil⟩ := g1z2_invFunOn_eq_dilate hs left hφ hUn
    have hdil' : EqOn (g1zSideMap left (pathDrive (γ ^ 2) a))
        (fun w => Ψ left a ((β : ℂ) * w)) H := fun w hw => by
      rw [hΨa]; exact hdil hw
    refine ⟨![1, β⁻¹, β⁻¹, β⁻¹], fun i => ?_, fun y q hq r hr0 hr1 => ?_⟩
    · fin_cases i
      · exact one_pos
      all_goals exact inv_pos.2 hβ
    have hrI : ((r : ℚ) : ℝ) ∈ Icc (0 : ℝ) 1 := ⟨by exact_mod_cast hr0, by exact_mod_cast hr1⟩
    have hk : ∀ k : ℕ, F (ratPt q) r k (a, y) =
        ∫ w, avgReg y k w ∂(smearFam (pathDrive (γ ^ 2) a) left
          (parScale ![1, β⁻¹, β⁻¹, β⁻¹] (ratPt q)) r) := by
      intro k
      rw [hFeq _ _ k hq hrI a hc hG y, smearPsi_eq hG hβ hdil' hq]
    refine ⟨hk, ?_⟩
    simp only [hEv, hk]
    rfl
  -- the fixed-path statement
  have hfix : ∀ a : ℝ≥0 → ℝ, Continuous a → G1zDrvGood (pathDrive (γ ^ 2) a) →
      (∀ T : ℝ, ∃ CH aH : ℝ, 0 ≤ CH ∧ 0 < aH ∧ aH ≤ 1 ∧ ∀ x ∈ Icc (0 : ℝ) T,
        ∀ y ∈ Icc (0 : ℝ) T, |pathDrive (γ ^ 2) a x - pathDrive (γ ^ 2) a y| ≤ CH * |x - y| ^ aH) →
      ∀ᵐ ω' ∂P, (a, X ω') ∈ E := by
    intro a hc hG hH
    obtain ⟨e, he, hbr⟩ := hbridge a hc hG
    filter_upwards [ae_smear_fixed_all_e hX hG left he hH] with ω' ⟨h1, h2⟩
    refine ⟨fun a' b' hsub n => ?_, fun q hq r hr0 hr1 n => ?_⟩
    · obtain ⟨N, hN⟩ := h1 a' b' hsub n
      refine ⟨N, fun r hr hrN q hq => ?_⟩
      have hqU : ratPt q ∈ smearU := hsub hq
      have hr1 : r ≤ 1 := by
        have : (r : ℝ) < 1 := hrN.trans_le (by
          rw [div_le_one (by positivity)]; linarith [(Nat.cast_nonneg N : (0 : ℝ) ≤ N)])
        exact_mod_cast this.le
      rw [(hbr (X ω') q hqU r hr.le hr1).2, (hbr (X ω') q hqU 0 le_rfl zero_le_one).2]
      simpa using hN r hr hrN q hq
    · have hqe : parScale e (ratPt q) ∈ smearU := parScale_mapsTo (he 0) (he 3) hq
      have ht := h2 q hqe r hr0 hr1
      rw [Metric.tendsto_atTop] at ht
      obtain ⟨N, hN⟩ := ht (1 / ((n : ℝ) + 1)) (by positivity)
      refine ⟨N, fun k hk => ?_⟩
      have := hN k hk
      rw [Real.dist_eq] at this
      rw [(hbr (X ω') q hq r hr0 hr1).1 k, (hbr (X ω') q hq r hr0 hr1).2]
      exact this
  -- Fubini along the independent driver
  have hgm : AEMeasurable (pathOf B) P := IsBrownianReal.aemeasurable_pathOf hB
  have hXm : Measurable X := measurable_pi_iff.2 hX.measurable_coord
  have hind' : IndepFun (hgm.mk _) X P := hind.congr hgm.ae_eq_mk (ae_eq_refl _)
  have hgood : ∀ᵐ ω ∂P, Continuous (pathOf B ω) ∧ G1zDrvGood (drive (γ ^ 2) B ω) ∧
      ∀ T : ℝ, ∃ CH aH : ℝ, 0 ≤ CH ∧ 0 < aH ∧ aH ≤ 1 ∧ ∀ x ∈ Icc (0 : ℝ) T,
        ∀ y ∈ Icc (0 : ℝ) T, |drive (γ ^ 2) B ω x - drive (γ ^ 2) B ω y| ≤ CH * |x - y| ^ aH := by
    filter_upwards [hB.cont, ae_g1zDrvGood_of_brownian hγ hγ2 hB, ASep.ae_drvGood_drive hγ hγ2 hB]
      with ω hc hG hD
    exact ⟨hc, hG, holder_global hD.1 hD.2.2.1⟩
  have h1 : ∀ᵐ ω ∂P, ∀ᵐ ω' ∂P, (hgm.mk _ ω, X ω') ∈ E := by
    filter_upwards [hgm.ae_eq_mk, hgood] with ω hω hg
    rw [← hω]
    exact hfix _ hg.1 hg.2.1 hg.2.2
  filter_upwards [CharFunRhs.ae_indep_ae hgm.measurable_mk hXm hind' hE h1, hgm.ae_eq_mk, hgood]
    with ω hω he hg
  rw [← he] at hω
  obtain ⟨e, hepos, hbr⟩ := hbridge _ hg.1 hg.2.1
  obtain ⟨hC, hT⟩ := hω
  refine ⟨e, hepos, fun a' b' hsub n => ?_, fun q hq r hr0 hr1 => ?_⟩
  · obtain ⟨N, hN⟩ := hC a' b' hsub n
    refine ⟨N, fun r hr hrN q hq => ?_⟩
    have hqU : ratPt q ∈ smearU := hsub hq
    have hr1 : r ≤ 1 := by
      have : (r : ℝ) < 1 := hrN.trans_le (by
        rw [div_le_one (by positivity)]; linarith [(Nat.cast_nonneg N : (0 : ℝ) ≤ N)])
      exact_mod_cast this.le
    have e1 := (hbr (X ω) q hqU r hr.le hr1).2
    have e0 := (hbr (X ω) q hqU 0 le_rfl zero_le_one).2
    have := hN r hr hrN q hq
    rw [e1, e0] at this
    push_cast at this
    exact this
  · have hqU : ratPt q ∈ smearU := by
      have h := parScale_mapsTo (c := fun i => (e i)⁻¹) (inv_pos.2 (hepos 0)) (inv_pos.2 (hepos 3)) hq
      rw [parScale_parScale] at h
      convert h using 1
      funext i
      simp [parScale, inv_mul_cancel₀ (hepos i).ne']
    rw [Metric.tendsto_atTop]
    intro ε hε
    obtain ⟨n, hn⟩ := exists_nat_one_div_lt hε
    obtain ⟨N, hN⟩ := hT q hqU r hr0 hr1 n
    refine ⟨N, fun k hk => ?_⟩
    have := hN k hk
    rw [(hbr (X ω) q hqU r hr0 hr1).1 k, (hbr (X ω) q hqU r hr0 hr1).2] at this
    rw [Real.dist_eq]
    exact this.trans hn

end A1RS
end R18
end QuantumZipper
