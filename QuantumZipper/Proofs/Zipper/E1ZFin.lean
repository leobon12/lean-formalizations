import QuantumZipper.Proofs.Zipper.E1ZFinBasic
import QuantumZipper.Proofs.Zipper.E1Main

/-!
# Z-FIN: the Palm normalizer lies in `(0, ⊤)` (conditional on E1-TR)

`handoff/E1-PLAN.md`, node **Z-FIN** (TASKS R24); `blueprint/E_BRANCH_BLUEPRINT.md` §4 Z-FIN.
Paper: Sheffield, arXiv:1012.4797, proof of Lemma 5.6 (pp. 66–68), where the Palm law is the
`ν[−δ,0]`-weighted law normalized by `Z = E ν[−δ,0]`; this node proves `0 < Z < ⊤` and computes
`Z = ∫_{[−δ,0)} ρ_ϖ` (so `palmLaw` is never the junk `0`, AUDIT7 Z1).

`zfin_of_tr`: E1 (`E1.e1_main_of_tr`) at `t = 0` with `Ψ = Φ = 1`, taking the E1-TR conclusion
for these data as the hypothesis `hTR` (exactly the `hTR` of `e1_main_of_tr`); at `t = 0` the
Palm-zip density is `ρ_ϖ` (`rhoT_zero`), the live points of `[−δ,0]` are `[−δ,0)`, `ν{0} = 0`
under B3(a) (`ae_nuPalm_singleton_zero`), and ZF-2 (`lintegral_rhoNorm_pos_lt_top`) concludes.
Once E1-TR is proved, `Z-FIN = zfin_of_tr … (e1_tr …)`. Own bookkeeping.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal ENNReal

namespace QuantumZipper
namespace E1

open B2 PalmNorm CoordsFull

theorem Iio_inter_Icc_eq_Ico {δ : ℝ} : Iio (0 : ℝ) ∩ Icc (-δ) 0 = Ico (-δ) 0 := by
  ext x
  simp only [mem_inter_iff, mem_Iio, mem_Icc, mem_Ico]
  constructor
  · rintro ⟨h1, h2, -⟩; exact ⟨h2, h1⟩
  · rintro ⟨h1, h2⟩; exact ⟨h2, h1, h2.le⟩

/-- At time `0`, integrating the live indicator over `[−δ,0]` is integrating over `[−δ,0)`. -/
theorem setLIntegral_Icc_isLive_zero {v : ℝ → ℝ} (hv : Continuous v) (hv0 : v 0 = 0) (δ : ℝ)
    (μ : Measure ℝ) {f g : ℝ → ℝ≥0∞} (hfg : ∀ x < 0, f x = g x) :
    ∫⁻ x in Icc (-δ) 0, {x | IsLive v 0 x}.indicator f x ∂μ = ∫⁻ x in Ico (-δ) 0, g x ∂μ := by
  calc ∫⁻ x in Icc (-δ) 0, {x | IsLive v 0 x}.indicator f x ∂μ
      = ∫⁻ x in Icc (-δ) 0, (Iio 0).indicator g x ∂μ := by
        refine setLIntegral_congr_fun measurableSet_Icc fun x hx => ?_
        by_cases hx0 : x < 0
        · rw [indicator_of_mem (show x ∈ {x | IsLive v 0 x} from isLive_zero_of_neg hv hv0 hx0),
            indicator_of_mem (show x ∈ Iio (0 : ℝ) from hx0), hfg x hx0]
        · have : x = 0 := le_antisymm hx.2 (not_lt.1 hx0)
          subst this
          rw [indicator_of_notMem (show (0 : ℝ) ∉ {x | IsLive v 0 x} from not_isLive_zero hv0 0),
            indicator_of_notMem (show (0 : ℝ) ∉ Iio (0 : ℝ) by simp)]
    _ = ∫⁻ x in Ico (-δ) 0, g x ∂μ := by
        rw [lintegral_indicator measurableSet_Iio, Measure.restrict_restrict measurableSet_Iio,
          Iio_inter_Icc_eq_Ico]

variable {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {κ T δ : ℝ} {B : ℝ≥0 → Ω → ℝ} {X : Ω → FieldSample} {ϖ : Measure ℂ}

/-- **Z-FIN, conditional on E1-TR** (`handoff/E1-PLAN.md`, TASKS R24). The hypothesis `hTR` is
the E1-TR conclusion at `t = 0` with `Ψ = Φ = 1`. -/
theorem zfin_of_tr (hReg : Blueprint.RevCouplingBoundaryMeasureRegular) (hκ : 0 < κ)
    (hκ4 : κ < 4) (hT : 0 < T) (hδ : 0 < δ) (hB : IsBrownianReal B P)
    (hX : IsFreeGFFModConstH X P) (hind : IndepFun (pathOf B) X P) (hϖ : IsNormalizer ϖ)
    (hTR : ∫⁻ ω, ∫⁻ x in Icc (-δ) 0, {x | IsLive (Vr κ T B ω) 0 x}.indicator (fun _ =>
        (1 : ℝ≥0∞) * 1) x ∂nuPalm κ T B X ϖ ω ∂P =
      ∫⁻ ω, ∫⁻ ω', ∫⁻ _ in Icc (-δ) 0, (1 : ℝ≥0∞) * 1
        ∂qBoundaryMeasureOn (Real.sqrt κ) (addConst (hFix κ (Vr κ T B ω) 0 (X ω'))
            (-(mFix κ (Vr κ T B ω) 0 ϖ (X ω')))) (liveNeg (Vr κ T B ω) 0) ∂P ∂P) :
    (∫⁻ ω, nuPalm κ T B X ϖ ω (Icc (-δ) 0) ∂P =
        ∫⁻ x in Ico (-δ) 0, ENNReal.ofReal (rhoNorm (Real.sqrt κ) (h0rev κ) ϖ x)) ∧
      0 < ∫⁻ ω, nuPalm κ T B X ϖ ω (Icc (-δ) 0) ∂P ∧
      ∫⁻ ω, nuPalm κ T B X ϖ ω (Icc (-δ) 0) ∂P < ⊤ := by
  have hE := e1_main_of_tr (P' := P) (X' := X) (Ψ := fun _ _ => 1) (Φ := fun _ => 1)
    hκ hκ4 le_rfl hT hB hX hX hϖ δ measurable_const measurable_const hTR
  set C := ∫⁻ x in Ico (-δ) 0, ENNReal.ofReal (rhoNorm (Real.sqrt κ) (h0rev κ) ϖ x) with hC
  have hmain : ∫⁻ ω, nuPalm κ T B X ϖ ω (Icc (-δ) 0) ∂P = C := by
    have hL : ∫⁻ ω, nuPalm κ T B X ϖ ω (Icc (-δ) 0) ∂P =
        ∫⁻ ω, ∫⁻ x in Icc (-δ) 0, {x | IsLive (Vr κ T B ω) 0 x}.indicator (fun _ =>
          (1 : ℝ≥0∞) * 1) x ∂nuPalm κ T B X ϖ ω ∂P := by
      refine lintegral_congr_ae ?_
      filter_upwards [hB.cont, ae_nuPalm_singleton_zero hReg hκ hκ4 hT hB hX hind ϖ]
        with ω hc h0
      have hv : Continuous (Vr κ T B ω) := continuous_vrev (drive_continuous hc) T
      have hv0 : Vr κ T B ω 0 = 0 := vrev_zero hT.le
      rw [setLIntegral_Icc_isLive_zero hv hv0 δ _ (g := fun _ => 1) (fun _ _ => one_mul 1),
        setLIntegral_const, one_mul]
      refine le_antisymm ?_ (measure_mono Ico_subset_Icc_self)
      calc nuPalm κ T B X ϖ ω (Icc (-δ) 0)
          = nuPalm κ T B X ϖ ω (Ico (-δ) 0 ∪ {0}) := by
            rw [Ico_union_right (by linarith : -δ ≤ 0)]
        _ ≤ nuPalm κ T B X ϖ ω (Ico (-δ) 0) + nuPalm κ T B X ϖ ω {0} := measure_union_le _ _
        _ = nuPalm κ T B X ϖ ω (Ico (-δ) 0) := by rw [h0, add_zero]
    rw [hL, hE]
    have hR : ∀ᵐ ω ∂P, ∫⁻ x in Icc (-δ) 0, {x | IsLive (Vr κ T B ω) 0 x}.indicator (fun x =>
        ENNReal.ofReal (rhoT κ (Vr κ T B ω) 0 ϖ x) * (fun _ _ => (1 : ℝ≥0∞)) x
          (Vstop κ T 0 B ω, W0p κ T B ω) *
          ∫⁻ ω', (fun _ => (1 : ℝ≥0∞)) (coordsFull (targetField κ (Vr κ T B ω) 0 ϖ x (X ω'))) ∂P)
        x ∂volume = C := by
      filter_upwards [hB.cont] with ω hc
      have hv : Continuous (Vr κ T B ω) := continuous_vrev (drive_continuous hc) T
      have hv0 : Vr κ T B ω 0 = 0 := vrev_zero hT.le
      refine setLIntegral_Icc_isLive_zero hv hv0 δ _ fun x hx => ?_
      simp only [lintegral_const, measure_univ, mul_one, rhoT_zero hv hv0 hϖ hx.ne]
    rw [lintegral_congr_ae hR, lintegral_const, measure_univ, mul_one]
  obtain ⟨hpos, htop⟩ := lintegral_rhoNorm_pos_lt_top hκ hϖ hδ
  exact ⟨hmain, hmain ▸ hpos, hmain ▸ htop⟩

end E1
end QuantumZipper
