import QuantumZipper.Proofs.Thm18.R18G3TCM
import QuantumZipper.Proofs.Thm18.G2PalmIdCoords
import QuantumZipper.Proofs.Thm18.G3PalmR

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# R18-G3 (R-a) groundwork, part 2: Palm integrals of the shifted field are tilted ones

Berestycki–Powell, arXiv:2004.04720, Lemma 3.12 (Cameron–Martin), in `lintegral` form, and its
consequence for the Palm integrals of the shifted scheme (Sheffield arXiv:1012.4797, p. 72,
Remark 5.7): if `φ` vanishes on the unit circle, then `normField γ X + ofFun φ` is exactly
`normField γ (X + ofFun φ)` (the normalization `X(refS)` does not see `φ`), and every functional
`Φ(x, s)` that reads the field `x` only on admissible probability measures is a measurable function
of the balanced increments. Hence
`∫⁻ Φ(g3pField γ φ ω, s) d(P ⊗ L₀) = ∫⁻ Φ(normField γ X ω, s) · cmTilt X φ ω d(P ⊗ L₀)`.
The reconstruction map `g3recon` is our own bookkeeping.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology ENNReal NNReal ComplexConjugate

namespace QuantumZipper
namespace R18

open Thm18Asm

/-! ## The Cameron–Martin identity in `lintegral` form -/

theorem lintegral_incr_shift_eq {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {X : Ω → FieldSample} {φ : ℂ → ℝ} (hX : IsFreeGFFModConstH X P) (hφ : ContDiff ℝ 2 φ)
    (hc : HasCompactSupport φ) (heven : ∀ z, φ (conj z) = φ z)
    {G : (K3.BalIdx → ℝ) → ℝ≥0∞} (hG : Measurable G) :
    ∫⁻ ω, G (CMTV.incr (X ω + ofFun φ)) ∂P =
      ∫⁻ ω, G (CMTV.incr (X ω)) * ENNReal.ofReal (cmTilt X φ ω) ∂P := by
  set A : K3.BalIdx → Ω → ℝ := fun j ω => X ω j.1.1 - X ω j.1.2 with hAdef
  have hmeas : ∀ j, Measurable (A j) := fun j =>
    (hX.measurable_coord _).sub (hX.measurable_coord _)
  have hcent : ∀ j, P[A j] = 0 := fun j => hX.centered _ _ j.2.1 j.2.2.1 j.2.2.2
  set σ : K3.BalIdx →₀ ℝ := Finsupp.single (CMTV.cmIdx hφ hc heven) 1 with hσ
  have hp : Measurable fun ω j => A j ω := measurable_pi_iff.mpr hmeas
  have hp' : Measurable fun ω j => A j ω + CameronMartin.covShift A P σ j :=
    measurable_pi_iff.mpr fun j => (hmeas j).add_const _
  have e : ∀ ω, CMTV.incr (X ω + ofFun φ) =
      fun j => A j ω + CameronMartin.covShift A P σ j :=
    fun ω => funext fun j => by rw [CMTV.incr_add_ofFun, covShift_cm hX]; rfl
  have hD : Measurable fun ω => ((cmTilt X φ ω).toNNReal : ℝ≥0∞) :=
    (Real.measurable_exp.comp (((hX.measurable_coord _).sub
      (hX.measurable_coord _)).sub_const _)).real_toNNReal.coe_nnreal_ennreal
  simp only [e]
  rw [← lintegral_map hG hp', ← CameronMartin.map_tiltMeasure_path hX.gaussian hmeas hcent σ,
    lintegral_map hG hp, CameronMartin.tiltMeasure, ← cmTilt_eq_tiltDensity hX hφ hc heven]
  have hw := lintegral_withDensity_eq_lintegral_mul P hD (hG.comp hp)
  simp only [Function.comp_def] at hw
  rw [hw]
  refine lintegral_congr fun ω => ?_
  simp only [Pi.mul_apply]
  rw [mul_comm]
  rfl

/-! ## Reconstruction of the normalized field from the increments -/

open Classical in
/-- The field `𝔥₀ + y(·, refS)` on admissible probability measures (junk `0` elsewhere). -/
def g3recon (γ : ℝ) (y : K3.BalIdx → ℝ) : FieldSample := fun μ =>
  if h : IsAdmissibleH μ ∧ μ univ = 1 then
    ofFun (h0rev (γ ^ 2)) μ + y ⟨(μ, refS), h.1, isAdmissibleH_refS, by rw [h.2]; exact measure_univ.symm⟩
  else 0

theorem measurable_g3recon (γ : ℝ) : Measurable (g3recon γ) := by
  refine measurable_pi_iff.2 fun μ => ?_
  by_cases h : IsAdmissibleH μ ∧ μ univ = 1
  · simp only [g3recon, dif_pos h]
    exact measurable_const.add (measurable_pi_apply _)
  · simp only [g3recon, dif_neg h]
    exact measurable_const

theorem normField_eq_g3recon (γ : ℝ) {Ω : Type*} (Y : Ω → FieldSample) (ω : Ω) {μ : Measure ℂ}
    (h1 : IsAdmissibleH μ) (h2 : μ univ = 1) :
    normField γ Y ω μ = g3recon γ (CMTV.incr (Y ω)) μ := by
  simp only [normField, g3recon, dif_pos (And.intro h1 h2)]
  rfl

theorem g3pField_eq_normField_shift (γ : ℝ) {φ : ℂ → ℝ} (hφS : ∀ z : ℂ, ‖z‖ = 1 → φ z = 0)
    (ω : gffBase.Ω) :
    g3pField γ φ ω = normField γ (fun ω => gffBase.X ω + ofFun φ) ω := by
  have h0 : ofFun φ refS = 0 := by
    show ∫ z, φ z ∂refS = 0
    refine integral_eq_zero_of_ae ?_
    filter_upwards [ae_norm_refS] with u hu
    simp [hφS u hu]
  funext μ
  simp only [g3pField, normField, Pi.add_apply, h0]
  ring

/-! ## Palm integrals of the shifted field -/

/-- **The shifted Palm integrals are tilted free ones.** For `φ` a Cameron–Martin shift vanishing
on the unit circle and a measurable `Φ` reading the field only on admissible probability
measures, `∫⁻ Φ(h + φ, s) = ∫⁻ Φ(h, s) · cmTilt X φ` over `P ⊗ L₀`. -/
theorem lintegral_g3pField_eq_tilt (γ : ℝ) {φ : ℂ → ℝ} (hφ : ContDiff ℝ 2 φ)
    (hc : HasCompactSupport φ) (heven : ∀ z, φ (conj z) = φ z)
    (hφS : ∀ z : ℂ, ‖z‖ = 1 → φ z = 0) {Φ : FieldSample × ℝ → ℝ≥0∞} (hΦ : Measurable Φ)
    (hloc : ∀ (x x' : FieldSample) (s : ℝ),
      (∀ μ : Measure ℂ, IsAdmissibleH μ → μ univ = 1 → x μ = x' μ) → Φ (x, s) = Φ (x', s)) :
    ∫⁻ p, Φ (g3pField γ φ p.1, p.2) ∂(gffBase.P.prod L₀) =
      ∫⁻ p, Φ (normField γ gffBase.X p.1, p.2) * ENNReal.ofReal (cmTilt gffBase.X φ p.1)
        ∂(gffBase.P.prod L₀) := by
  set Ψ : (K3.BalIdx → ℝ) × ℝ → ℝ≥0∞ := fun q => Φ (g3recon γ q.1, q.2) with hΨdef
  have hΨ : Measurable Ψ :=
    hΦ.comp (((measurable_g3recon γ).comp measurable_fst).prodMk measurable_snd)
  have hred : ∀ (Y : gffBase.Ω → FieldSample) (ω : gffBase.Ω) (s : ℝ),
      Φ (normField γ Y ω, s) = Ψ (CMTV.incr (Y ω), s) := fun Y ω s =>
    hloc _ _ s fun μ h1 h2 => normField_eq_g3recon γ Y ω h1 h2
  have hL : ∀ p : gffBase.Ω × ℝ, Φ (g3pField γ φ p.1, p.2) =
      Ψ (CMTV.incr (gffBase.X p.1 + ofFun φ), p.2) := fun p => by
    rw [g3pField_eq_normField_shift γ hφS, hred]
  have hR : ∀ p : gffBase.Ω × ℝ, Φ (normField γ gffBase.X p.1, p.2) =
      Ψ (CMTV.incr (gffBase.X p.1), p.2) := fun p => hred _ _ _
  simp only [hL, hR]
  have hmX : Measurable fun ω => CMTV.incr (gffBase.X ω) :=
    measurable_pi_iff.2 fun j =>
      (gffBase.gff.measurable_coord _).sub (gffBase.gff.measurable_coord _)
  have hmX' : Measurable fun ω => CMTV.incr (gffBase.X ω + ofFun φ) :=
    measurable_pi_iff.2 fun j => ((gffBase.gff.measurable_coord _).add_const _).sub
      ((gffBase.gff.measurable_coord _).add_const _)
  have hD : Measurable fun ω => ENNReal.ofReal (cmTilt gffBase.X φ ω) :=
    ENNReal.measurable_ofReal.comp (Real.measurable_exp.comp
      (((gffBase.gff.measurable_coord _).sub (gffBase.gff.measurable_coord _)).sub_const _))
  have h1 : Measurable fun p : gffBase.Ω × ℝ => Ψ (CMTV.incr (gffBase.X p.1 + ofFun φ), p.2) :=
    hΨ.comp ((hmX'.comp measurable_fst).prodMk measurable_snd)
  have h2 : Measurable fun p : gffBase.Ω × ℝ =>
      Ψ (CMTV.incr (gffBase.X p.1), p.2) * ENNReal.ofReal (cmTilt gffBase.X φ p.1) :=
    (hΨ.comp ((hmX.comp measurable_fst).prodMk measurable_snd)).mul (hD.comp measurable_fst)
  rw [lintegral_prod _ h1.aemeasurable, lintegral_prod _ h2.aemeasurable]
  have hG : Measurable fun y => ∫⁻ s, Ψ (y, s) ∂L₀ := hΨ.lintegral_prod_right'
  rw [lintegral_incr_shift_eq gffBase.gff hφ hc heven hG]
  refine lintegral_congr fun ω => ?_
  have h3 : Measurable fun s : ℝ => Ψ (CMTV.incr (gffBase.X ω), s) :=
    hΨ.comp (measurable_const.prodMk measurable_id)
  exact (lintegral_mul_const _ h3).symm

end R18
end QuantumZipper
