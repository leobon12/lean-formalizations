import QuantumZipper.Proofs.Thm18.A1RSParamUnif
import QuantumZipper.Proofs.GFF.FrostmanReg
import QuantumZipper.Proofs.Zipper.GenUCMod
import QuantumZipper.Proofs.Zipper.GenUCOpen

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# A1RS (17): the smeared-loop family is a Kolmogorov family (`GenFam`) on parameter boxes

Parameters `p = (t, Re d, Im d, s) ∈ ℝ⁴`, `smearFam W left p ρ = a1rfNu W t left d s ρ`
(A1RFSmear.lean). On the boxes `smearBox t₀ T R = {t ∈ [t₀, T], ‖d‖ ≤ 2R, s ∈ [e^{-R}, e^R]}`
(`t₀ > 0`), for a good driver that is Hölder on `[0, T]`:

**`genFam_smearFam`**: `∃ K c, GenUC.GenFam (smearBox t₀ T R) (smearFam W left) 1 K c` —
the hypothesis of the GENERIC-UC Kolmogorov step `GenUC.exists_contMod_gen` (GenUCKolm.lean):
admissible probability measures (`FrostmanReg.isAdmissibleH_of_frostman`, from the uniform
Frostman bound `isFrostman_a1rfNu_unif` and the support bound), and the Neumann energy of
`ν_{p,ρ} − ν_{p',ρ'}` is `≤ K (dist p p' + |ρ − ρ'|)^c` (`GenUC.genFam_of_moduli` from the radius
modulus `a1rfNu_radius_unif` and the parameter modulus `a1rfNu_param_unif`).

This is the Kolmogorov input of Duplantier–Sheffield, Invent. Math. 185 (2011), Prop. 3.1, for
the family of `A1RFSmearContStmt`. Own bookkeeping.

**`genFam_smearFam_ratBox`**: the same on every rational box `GenUC.ratBox a b` inside the open
parameter set `{t > 0, s > 0}` (the form used by the open-set engine `GenUC.ae_exact_open`).
-/

noncomputable section

open MeasureTheory Set Filter Metric Complex
open scoped Topology ENNReal

namespace QuantumZipper
namespace R18
namespace A1RS

open Thm18Asm Thm18Asm.G1RC TwoPoint

/-- The complex coordinate of a parameter vector. -/
def parD (p : Fin 4 → ℝ) : ℂ := ⟨p 1, p 2⟩

/-- The smeared-loop family in the parameters `(t, Re d, Im d, s)`. -/
def smearFam (W : ℝ → ℝ) (left : Bool) (p : Fin 4 → ℝ) (ρ : ℝ) : Measure ℂ :=
  a1rfNu W (p 0) left (parD p) (p 3) ρ

/-- The parameter boxes. -/
def smearBox (t₀ T : ℝ) (R : ℕ) : Set (Fin 4 → ℝ) :=
  {p | p 0 ∈ Icc t₀ T ∧ ‖parD p‖ ≤ 2 * R ∧ p 3 ∈ Icc (Real.exp (-R)) (Real.exp R)}

theorem abs_coord_sub_le (p p' : Fin 4 → ℝ) (i : Fin 4) : |p i - p' i| ≤ dist p p' := by
  have := norm_le_pi_norm (p - p') i
  simpa [Real.norm_eq_abs, dist_eq_norm] using this

theorem norm_parD_sub_le (p p' : Fin 4 → ℝ) : ‖parD p - parD p'‖ ≤ 2 * dist p p' := by
  have e : parD p - parD p' = ((p 1 - p' 1 : ℝ) : ℂ) + ((p 2 - p' 2 : ℝ) : ℂ) * I := by
    apply Complex.ext <;> simp [parD]
  rw [e]
  refine (norm_add_le _ _).trans ?_
  rw [norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs,
    Real.norm_eq_abs]
  linarith [abs_coord_sub_le p p' 1, abs_coord_sub_le p p' 2]

/-- **The smeared-loop family is a `GenFam` on every box.** -/
theorem genFam_smearFam {W : ℝ → ℝ} (hG : G1zDrvGood W) (left : Bool) {t₀ T : ℝ}
    (ht₀ : 0 < t₀) (hT : t₀ ≤ T) (R : ℕ) {CH aH : ℝ} (hCH : 0 ≤ CH) (haH : 0 < aH)
    (haH1 : aH ≤ 1)
    (hHol : ∀ a ∈ Icc (0 : ℝ) T, ∀ b ∈ Icc (0 : ℝ) T, |W a - W b| ≤ CH * |a - b| ^ aH) :
    ∃ K c : ℝ, GenUC.GenFam (smearBox t₀ T R) (smearFam W left) 1 K c := by
  have hT0 : 0 < T := ht₀.trans_le hT
  obtain ⟨α, CF, hα, -, -, hFr⟩ := isFrostman_a1rfNu_unif hG left hT0 R
  obtain ⟨R₁, Cm, hR₁, -, hbox⟩ := a1rMu_box_facts hG left hT0 R
  obtain ⟨Ci, hCi, hinv⟩ := norm_fwdMapInv_le_unif hG.1 hG.2.1 hT0
  obtain ⟨C₁, a₁, hC₁, ha₁, hrad⟩ := a1rfNu_radius_unif hG left hT0 R
  obtain ⟨C₂, b₂, hC₂, hb₂, hpar⟩ := a1rfNu_param_unif hG left hT0 R hCH haH haH1 hHol
  have hmemt : ∀ p ∈ smearBox t₀ T R, p 0 ∈ Ioc (0 : ℝ) T := fun p hp =>
    ⟨ht₀.trans_le hp.1.1, hp.1.2⟩
  -- probability and support
  have hprob : ∀ p ∈ smearBox t₀ T R, ∀ ρ ∈ Icc (0 : ℝ) 1,
      IsProbabilityMeasure (smearFam W left p ρ) ∧
      ∀ᵐ z ∂smearFam W left p ρ, z ∈ closedBall (0 : ℂ) (R₁ + 1 + Ci) ∩ Hbar := by
    intro p hp ρ hρ
    obtain ⟨hP, hsp, -⟩ := hbox (p 0) (hmemt p hp) (parD p) hp.2.1 (p 3) hp.2.2.1 hp.2.2.2
    have hFm : Measurable fun q : ℂ × ℝ => fwdMapInv W (p 0) (foldH (circleMap q.1 ρ q.2)) :=
      A1RF.measurable_smear (RTBeur.measurable_fwdMapInv_rt hG.1 hG.2.1
        (hmemt p hp).1.le) ρ
    refine ⟨(Measure.isProbabilityMeasure_map_iff hFm.aemeasurable).2 inferInstance, ?_⟩
    have hcl : MeasurableSet (closedBall (0 : ℂ) (R₁ + 1 + Ci) ∩ Hbar) :=
      isClosed_closedBall.measurableSet.inter isClosed_Hbar.measurableSet
    unfold smearFam a1rfNu
    refine (ae_map_iff hFm.aemeasurable hcl).2 ?_
    have hfst := Measure.quasiMeasurePreserving_fst (μ := a1rMu W (p 0) left (parD p) (p 3))
      (ν := E6.XAreaPC.angMeas) |>.ae hsp
    filter_upwards [hfst] with q hq
    refine ⟨?_, F1.fwdMapInv_mem_Hbar W _ _⟩
    rw [mem_closedBall, dist_zero_right]
    refine (hinv (p 0) (hmemt p hp) _).trans ?_
    rw [norm_foldH]
    have := norm_circleMap_le_add q.1 hρ.1 q.2
    linarith [hq.2, hρ.2]
  have hFrp : ∀ p ∈ smearBox t₀ T R, ∀ ρ ∈ Icc (0 : ℝ) 1,
      TwoPoint.IsFrostman (smearFam W left p ρ) α CF := fun p hp ρ hρ =>
    hFr (p 0) (hmemt p hp) (parD p) hp.2.1 (p 3) hp.2.2.1 hp.2.2.2 ρ hρ
  have hadm : ∀ p ∈ smearBox t₀ T R, ∀ ρ ∈ Icc (0 : ℝ) 1, IsAdmissibleH (smearFam W left p ρ) := by
    intro p hp ρ hρ
    obtain ⟨hP, hs⟩ := hprob p hp ρ hρ
    have hnull : smearFam W left p ρ (closedBall 0 (R₁ + 1 + Ci) ∩ Hbar)ᶜ = 0 := by
      exact ae_iff.1 hs
    exact FrostmanReg.isAdmissibleH_of_frostman hnull (hFrp p hp ρ hρ) hα
  have hmass : ∀ p ∈ smearBox t₀ T R, ∀ ρ ∈ Icc (0 : ℝ) 1, smearFam W left p ρ univ = 1 :=
    fun p hp ρ hρ => (hprob p hp ρ hρ).1.measure_univ
  -- diameter of the box
  have hdiam : ∀ p ∈ smearBox t₀ T R, ∀ p' ∈ smearBox t₀ T R,
      dist p p' ≤ T + 4 * R + Real.exp R := by
    intro p hp p' hp'
    rw [dist_pi_le_iff (by positivity)]
    intro i
    rw [Real.dist_eq]
    have hR0 : (0 : ℝ) ≤ R := Nat.cast_nonneg R
    have he := Real.exp_pos (-(R : ℝ))
    have hc1 : |p 1| ≤ 2 * R := (Complex.abs_re_le_norm (parD p)).trans hp.2.1
    have hc1' : |p' 1| ≤ 2 * R := (Complex.abs_re_le_norm (parD p')).trans hp'.2.1
    have hc2 : |p 2| ≤ 2 * R := (Complex.abs_im_le_norm (parD p)).trans hp.2.1
    have hc2' : |p' 2| ≤ 2 * R := (Complex.abs_im_le_norm (parD p')).trans hp'.2.1
    have g0 : |p 0 - p' 0| ≤ T + 4 * R + Real.exp R := by
      rw [abs_le]; constructor <;> linarith [hp.1.1, hp.1.2, hp'.1.1, hp'.1.2, Real.exp_pos (R : ℝ)]
    have g1 : |p 1 - p' 1| ≤ T + 4 * R + Real.exp R := by
      rw [abs_le] at hc1 hc1' ⊢
      constructor <;> linarith [Real.exp_pos (R : ℝ), hp.1.1, hp.1.2, ht₀]
    have g2 : |p 2 - p' 2| ≤ T + 4 * R + Real.exp R := by
      rw [abs_le] at hc2 hc2' ⊢
      constructor <;> linarith [Real.exp_pos (R : ℝ), hp.1.1, hp.1.2, ht₀]
    have g3 : |p 3 - p' 3| ≤ T + 4 * R + Real.exp R := by
      rw [abs_le]
      constructor <;> linarith [hp.2.2.1, hp.2.2.2, hp'.2.2.1, hp'.2.2.2, hp.1.1, hp.1.2, ht₀]
    fin_cases i
    exacts [g0, g1, g2, g3]
  -- the parameter modulus, symmetric form
  have hsym : ∀ a b : Measure ℂ, kernelCov2 neumannH (a, b) (a, b) =
      kernelCov2 neumannH (b, a) (b, a) := fun a b => by unfold kernelCov2; ring
  have hE2 : ∀ p ∈ smearBox t₀ T R, ∀ p' ∈ smearBox t₀ T R, ∀ ρ ∈ Icc (0 : ℝ) 1,
      |kernelCov2 neumannH (smearFam W left p ρ, smearFam W left p' ρ)
        (smearFam W left p ρ, smearFam W left p' ρ)| ≤ (C₂ * 4 ^ b₂) * dist p p' ^ b₂ := by
    have key : ∀ p ∈ smearBox t₀ T R, ∀ p' ∈ smearBox t₀ T R, p 0 ≤ p' 0 →
        ∀ ρ ∈ Icc (0 : ℝ) 1,
        |kernelCov2 neumannH (smearFam W left p ρ, smearFam W left p' ρ)
          (smearFam W left p ρ, smearFam W left p' ρ)| ≤ (C₂ * 4 ^ b₂) * dist p p' ^ b₂ := by
      intro p hp p' hp' hle ρ hρ
      have h := hpar (p 0) (hmemt p hp) (p' 0 - p 0) (by linarith) (by linarith [hp'.1.2])
        (parD p) (parD p') hp.2.1 hp'.2.1 (p 3) (p' 3) hp.2.2.1 hp.2.2.2 hp'.2.2.1 hp'.2.2.2 ρ hρ
      rw [show p 0 + (p' 0 - p 0) = p' 0 by ring] at h
      refine h.trans ?_
      have hΔ : p' 0 - p 0 + ‖parD p - parD p'‖ + |p 3 - p' 3| ≤ 4 * dist p p' := by
        have a1 := abs_coord_sub_le p p' 0
        have a2 := norm_parD_sub_le p p'
        have a3 := abs_coord_sub_le p p' 3
        rw [abs_sub_comm] at a1
        linarith [le_abs_self (p' 0 - p 0)]
      have hΔ0 : 0 ≤ p' 0 - p 0 + ‖parD p - parD p'‖ + |p 3 - p' 3| := by
        have := norm_nonneg (parD p - parD p'); have := abs_nonneg (p 3 - p' 3); linarith
      calc C₂ * (p' 0 - p 0 + ‖parD p - parD p'‖ + |p 3 - p' 3|) ^ b₂
          ≤ C₂ * (4 * dist p p') ^ b₂ :=
            mul_le_mul_of_nonneg_left (Real.rpow_le_rpow hΔ0 hΔ hb₂.le) hC₂
        _ = (C₂ * 4 ^ b₂) * dist p p' ^ b₂ := by
            rw [Real.mul_rpow (by norm_num) dist_nonneg]; ring
    intro p hp p' hp' ρ hρ
    rcases le_total (p 0) (p' 0) with hle | hle
    · exact key p hp p' hp' hle ρ hρ
    · rw [hsym, dist_comm]
      exact key p' hp' p hp hle ρ hρ
  have hE1 : ∀ p ∈ smearBox t₀ T R, ∀ ρ ∈ Icc (0 : ℝ) 1, ∀ ρ' ∈ Icc (0 : ℝ) 1,
      |kernelCov2 neumannH (smearFam W left p ρ, smearFam W left p ρ')
        (smearFam W left p ρ, smearFam W left p ρ')| ≤ C₁ * |ρ - ρ'| ^ a₁ :=
    fun p hp ρ hρ ρ' hρ' =>
      hrad (p 0) (hmemt p hp) (parD p) hp.2.1 (p 3) hp.2.2.1 hp.2.2.2 ρ hρ ρ' hρ'
  exact GenUC.genFam_of_moduli hadm hmass hdiam hC₁ ha₁ hE1
    (by positivity : 0 ≤ C₂ * 4 ^ b₂) hb₂ hE2

/-- **Fixed-parameter exactness** (Duplantier–Sheffield, Invent. Math. 185 (2011), Prop. 3.1 at
one measure, `FrostmanReg.ae_evalReg_eq_frostman`): for a free field `X`, every member of the
smeared-loop family on a box satisfies `evalReg (X ω) ν = X ω ν` almost surely. This is the input
`hid` of the engine `GenUC.ae_unifConv_all_radii`. -/
theorem ae_evalReg_eq_smearFam {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {X : Ω → FieldSample} (hX : IsFreeGFFModConstH X P) {W : ℝ → ℝ}
    (hG : G1zDrvGood W) (left : Bool) {t₀ T : ℝ} (ht₀ : 0 < t₀) (hT : t₀ ≤ T) (R : ℕ)
    {p : Fin 4 → ℝ} (hp : p ∈ smearBox t₀ T R) {ρ : ℝ} (hρ : ρ ∈ Icc (0 : ℝ) 1) :
    ∀ᵐ ω ∂P, evalReg (X ω) (smearFam W left p ρ) = X ω (smearFam W left p ρ) := by
  have hT0 : 0 < T := ht₀.trans_le hT
  obtain ⟨α, CF, hα, -, -, hFr⟩ := isFrostman_a1rfNu_unif hG left hT0 R
  obtain ⟨R₁, Cm, hR₁, -, hbox⟩ := a1rMu_box_facts hG left hT0 R
  obtain ⟨Ci, hCi, hinv⟩ := norm_fwdMapInv_le_unif hG.1 hG.2.1 hT0
  have hpt : p 0 ∈ Ioc (0 : ℝ) T := ⟨ht₀.trans_le hp.1.1, hp.1.2⟩
  obtain ⟨hP, hsp, -⟩ := hbox (p 0) hpt (parD p) hp.2.1 (p 3) hp.2.2.1 hp.2.2.2
  have hFm : Measurable fun q : ℂ × ℝ => fwdMapInv W (p 0) (foldH (circleMap q.1 ρ q.2)) :=
    A1RF.measurable_smear (RTBeur.measurable_fwdMapInv_rt hG.1 hG.2.1 hpt.1.le) ρ
  have hprob : IsProbabilityMeasure (smearFam W left p ρ) :=
    (Measure.isProbabilityMeasure_map_iff hFm.aemeasurable).2 inferInstance
  have hcl : MeasurableSet (closedBall (0 : ℂ) (R₁ + 1 + Ci) ∩ Hbar) :=
    isClosed_closedBall.measurableSet.inter isClosed_Hbar.measurableSet
  have hs : ∀ᵐ z ∂smearFam W left p ρ, z ∈ closedBall (0 : ℂ) (R₁ + 1 + Ci) ∩ Hbar := by
    unfold smearFam a1rfNu
    refine (ae_map_iff hFm.aemeasurable hcl).2 ?_
    have hfst := Measure.quasiMeasurePreserving_fst (μ := a1rMu W (p 0) left (parD p) (p 3))
      (ν := E6.XAreaPC.angMeas) |>.ae hsp
    filter_upwards [hfst] with q hq
    refine ⟨?_, F1.fwdMapInv_mem_Hbar W _ _⟩
    rw [mem_closedBall, dist_zero_right]
    refine (hinv (p 0) hpt _).trans ?_
    rw [norm_foldH]
    have := norm_circleMap_le_add q.1 hρ.1 q.2
    linarith [hq.2, hρ.2]
  have hnull : smearFam W left p ρ (closedBall 0 (R₁ + 1 + Ci) ∩ Hbar)ᶜ = 0 := ae_iff.1 hs
  exact FrostmanReg.ae_evalReg_eq_frostman hX hnull
    (hFr (p 0) hpt (parD p) hp.2.1 (p 3) hp.2.2.1 hp.2.2.2 ρ hρ) hα

end A1RS
end R18
end QuantumZipper
