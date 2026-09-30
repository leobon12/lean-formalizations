import QuantumZipper.Proofs.Thm18.R18G3TCM3
import QuantumZipper.Proofs.Thm18.G3GeoHonest

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# R18-G3 (R-a), part 4: the Cameron–Martin transfer of Palm probabilities `A → B`

Berestycki–Powell, arXiv:2004.04720, Lemma 3.12; Sheffield arXiv:1012.4797, p. 72,
Remark 5.7. For an outside event `G` there is an outside event `G'` such that for every local
event `S` of `(field, length)`:
`P_B(S_B ∩ G) = (Z_A / Z_B) ∫_{S_A ∩ G'} cmTilt dP_A` (`g3pPalmLaw_cut_eq`). Own bookkeeping.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Metric
open scoped Topology ENNReal NNReal ComplexConjugate

namespace QuantumZipper
namespace R18

open Thm18Asm

local notation "Ω₀" => gffBase.Ω
local notation "X₀" => gffBase.X

/-! ## The joint Cameron–Martin identity on `Ω₀ × ℝ` -/

theorem lintegral_prod_incr_shift {φ : ℂ → ℝ} (hφ : ContDiff ℝ 2 φ) (hc : HasCompactSupport φ)
    (heven : ∀ z, φ (conj z) = φ z) {Ψ : (K3.BalIdx → ℝ) × ℝ → ℝ≥0∞} (hΨ : Measurable Ψ) :
    ∫⁻ p, Ψ (CMTV.incr (X₀ p.1 + ofFun φ), p.2) ∂(gffBase.P.prod L₀) =
      ∫⁻ p, Ψ (CMTV.incr (X₀ p.1), p.2) * ENNReal.ofReal (cmTilt X₀ φ p.1)
        ∂(gffBase.P.prod L₀) := by
  have hmX : Measurable fun ω => CMTV.incr (X₀ ω) :=
    measurable_pi_iff.2 fun j =>
      (gffBase.gff.measurable_coord _).sub (gffBase.gff.measurable_coord _)
  have hmX' : Measurable fun ω => CMTV.incr (X₀ ω + ofFun φ) :=
    measurable_pi_iff.2 fun j => ((gffBase.gff.measurable_coord _).add_const _).sub
      ((gffBase.gff.measurable_coord _).add_const _)
  have hD : Measurable fun ω => ENNReal.ofReal (cmTilt X₀ φ ω) :=
    ENNReal.measurable_ofReal.comp (Real.measurable_exp.comp
      (((gffBase.gff.measurable_coord _).sub (gffBase.gff.measurable_coord _)).sub_const _))
  have h1 : Measurable fun p : Ω₀ × ℝ => Ψ (CMTV.incr (X₀ p.1 + ofFun φ), p.2) :=
    hΨ.comp ((hmX'.comp measurable_fst).prodMk measurable_snd)
  have h2 : Measurable fun p : Ω₀ × ℝ =>
      Ψ (CMTV.incr (X₀ p.1), p.2) * ENNReal.ofReal (cmTilt X₀ φ p.1) :=
    (hΨ.comp ((hmX.comp measurable_fst).prodMk measurable_snd)).mul (hD.comp measurable_fst)
  rw [lintegral_prod _ h1.aemeasurable, lintegral_prod _ h2.aemeasurable]
  have hG : Measurable fun y => ∫⁻ s, Ψ (y, s) ∂L₀ := hΨ.lintegral_prod_right'
  rw [lintegral_incr_shift_eq gffBase.gff hφ hc heven hG]
  refine lintegral_congr fun ω => ?_
  have h3 : Measurable fun s : ℝ => Ψ (CMTV.incr (X₀ ω), s) :=
    hΨ.comp (measurable_const.prodMk measurable_id)
  exact (lintegral_mul_const _ h3).symm

/-! ## The transfer of Palm integrals with an outside event -/

theorem measurable_oInc (i : G3Idx) : Measurable (oInc i) :=
  measurable_pi_iff.2 fun _ => measurable_pi_apply _

theorem fcEq_g3pField_cut (γ : ℝ) (i : G3Idx) (ω : Ω₀) :
    FcEq (g3pField γ (g3wCut γ i.η) ω)
      (g3recon γ (CMTV.incr (X₀ ω + ofFun (g3wCut γ i.η)))) := by
  rw [g3pField_eq_normField_shift γ (g3wCut_unit γ i.η) ω]
  exact fcEq_normField_recon γ (fun ω => X₀ ω + ofFun (g3wCut γ i.η)) ω

/-- **Transfer of Palm integrals from scheme `B` to scheme `A`.** -/
theorem lintegral_B_eq_tilt (γ : ℝ) (i : G3Idx) {G : Set (Ω₀ × ℝ)}
    (hG : MeasurableSet[outsideSigmaPalm ℝ X₀ i.t₁ i.r₁ i.t₂ i.r₂] G) :
    ∃ G' : Set (Ω₀ × ℝ), MeasurableSet[outsideSigmaPalm ℝ X₀ i.t₁ i.r₁ i.t₂ i.r₂] G' ∧
      ∀ S : Set (FieldSample × ℝ), MeasurableSet S → IsLocS S →
        ∫⁻ p, ({p : Ω₀ × ℝ | (g3pField γ (g3wCut γ i.η) p.1, p.2) ∈ S} ∩ G).indicator
            (g3pW0 γ (g3wCut γ i.η) i) p ∂(gffBase.P.prod L₀) =
          ∫⁻ p, ({p : Ω₀ × ℝ | (normField γ X₀ p.1, p.2) ∈ S} ∩ G').indicator
            (fun p => g3W0 γ i p * ENNReal.ofReal (cmTilt X₀ (g3wCut γ i.η) p.1)) p
            ∂(gffBase.P.prod L₀) := by
  set φ := g3wCut γ i.η with hφdef
  obtain ⟨G₀, hG₀, rfl⟩ := outside_repr i hG
  set c : OutIdx2 i.t₁ i.r₁ i.t₂ i.r₂ → ℝ :=
    oInc i (fun j => ∫ z, φ z ∂j.1.1 - ∫ z, φ z ∂j.1.2) with hc
  refine ⟨(fun p : Ω₀ × ℝ => (oInc i (CMTV.incr (X₀ p.1)) - c, p.2)) ⁻¹' G₀,
    measurable_oInc_shift i c hG₀, fun S hS hSl => ?_⟩
  set Ψ : (K3.BalIdx → ℝ) × ℝ → ℝ≥0∞ := fun q =>
    S.indicator (sW0 γ i) (g3recon γ q.1, q.2) *
      G₀.indicator (fun _ => (1 : ℝ≥0∞)) (oInc i q.1 - c, q.2) with hΨdef
  have hΨ : Measurable Ψ :=
    (((measurable_sW0 γ i).indicator hS).comp
      (((measurable_g3recon γ).comp measurable_fst).prodMk measurable_snd)).mul
    ((measurable_const.indicator hG₀).comp
      ((((measurable_oInc i).sub_const c).comp measurable_fst).prodMk measurable_snd))
  have hoff : ∀ ω : Ω₀, oInc i (CMTV.incr (X₀ ω + ofFun φ)) - c = oInc i (CMTV.incr (X₀ ω)) := by
    intro ω
    funext q
    simp only [oInc, Pi.sub_apply, hc, CMTV.incr_add_ofFun]
    ring
  have hL : ∀ p : Ω₀ × ℝ,
      ({p : Ω₀ × ℝ | (g3pField γ φ p.1, p.2) ∈ S} ∩
        (fun p : Ω₀ × ℝ => (oInc i (CMTV.incr (X₀ p.1)), p.2)) ⁻¹' G₀).indicator
          (g3pW0 γ φ i) p = Ψ (CMTV.incr (X₀ p.1 + ofFun φ), p.2) := by
    intro p
    have fc := fcEq_g3pField_cut γ i p.1
    have hmS := hSl _ _ fc p.2
    have hW : g3pW0 γ φ i p = sW0 γ i (g3recon γ (CMTV.incr (X₀ p.1 + ofFun φ)), p.2) :=
      (g3pW0_eq γ i φ p).trans (sW0_fc fc γ i p.2)
    simp only [hΨdef, hoff]
    by_cases h1 : (g3pField γ φ p.1, p.2) ∈ S <;>
      by_cases h2 : (oInc i (CMTV.incr (X₀ p.1)), p.2) ∈ G₀ <;>
      simp [indicator, h1, h2, hmS.1, hW, hmS.not.1, mem_inter_iff] <;> simp_all
  have hR : ∀ p : Ω₀ × ℝ,
      ({p : Ω₀ × ℝ | (normField γ X₀ p.1, p.2) ∈ S} ∩
        (fun p : Ω₀ × ℝ => (oInc i (CMTV.incr (X₀ p.1)) - c, p.2)) ⁻¹' G₀).indicator
          (fun p => g3W0 γ i p * ENNReal.ofReal (cmTilt X₀ φ p.1)) p =
        Ψ (CMTV.incr (X₀ p.1), p.2) * ENNReal.ofReal (cmTilt X₀ φ p.1) := by
    intro p
    have fc := fcEq_normField_recon γ X₀ p.1
    have hmS := hSl _ _ fc p.2
    have hW : g3W0 γ i p = sW0 γ i (g3recon γ (CMTV.incr (X₀ p.1)), p.2) :=
      (g3W0_eq γ i p).trans (sW0_fc fc γ i p.2)
    simp only [hΨdef]
    by_cases h1 : (normField γ X₀ p.1, p.2) ∈ S <;>
      by_cases h2 : (oInc i (CMTV.incr (X₀ p.1)) - c, p.2) ∈ G₀ <;>
      simp [indicator, h1, h2, hmS.1, hW, hmS.not.1, mem_inter_iff] <;> simp_all
  rw [lintegral_congr hL, lintegral_congr hR]
  exact lintegral_prod_incr_shift (contDiff_g3wCut γ i.η i.hη) (hasCompactSupport_g3wCut γ i.η)
    (g3wCut_conj γ i.η) hΨ

/-! ## Palm laws as normalized integrals -/

theorem g3pPalmLaw_apply {γ : ℝ} {g : ℂ → ℝ} {i : G3Idx}
    (hZ : 0 < g3pZ γ g i ∧ g3pZ γ g i < ⊤) {E : Set (Ω₀ × ℝ)} (hE : MeasurableSet E) :
    g3pPalmLaw γ g i E = (g3pZ γ g i)⁻¹ * ∫⁻ p, E.indicator (g3pW0 γ g i) p ∂(gffBase.P.prod L₀) := by
  rw [g3pPalmLaw, withDensity_apply _ hE, ← lintegral_indicator hE,
    ← lintegral_const_mul' _ _ (ENNReal.inv_ne_top.2 hZ.1.ne')]
  refine lintegral_congr fun p => ?_
  simp only [g3pW, if_pos hZ]
  by_cases hp : p ∈ E
  · simp only [indicator, hp, if_true]
    exact ENNReal.coe_toNNReal (ENNReal.mul_ne_top (ENNReal.inv_ne_top.2 hZ.1.ne')
      (g3pW0_ne_top γ g i p))
  · simp [indicator, hp]

theorem g3pW0_zero (γ : ℝ) (i : G3Idx) : g3pW0 γ 0 i = g3W0 γ i :=
  funext fun p => by rw [g3pW0_eq, g3W0_eq, g3pField_zero]

theorem g3pZ_zero (γ : ℝ) (i : G3Idx) : g3pZ γ 0 i = g3Z γ i := by
  unfold g3pZ g3Z; rw [g3pW0_zero]

end R18
end QuantumZipper
