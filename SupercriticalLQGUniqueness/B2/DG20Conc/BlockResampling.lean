import SupercriticalLQGUniqueness.B2.DG20Conc.BlockReconstruction
import LQGMetric.Prob.EfronSteinCopy

 








set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory

namespace SupercriticalLQGUniqueness.B2.DG20Conc

open LQGMetric.DDDF LQGMetric.WhiteNoise

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
  {W : WNSpace → Ω → ℝ}

private def pieceRead (Q : PsiParams) (W : WNSpace → Ω → ℝ) (P : Measure Ω)
    (K n : ℕ) (o : Option (T20B.nearIdx K)) : Ω → T20B.dyD → ℝ :=
  fun ω => T20B.restrD (fun x => psiPiece Q W P K n o x ω)

private lemma measurable_pieceRead (hW : IsWhiteNoise P W) (Q : PsiParams)
    {K n : ℕ} (hKn : K ≤ n) (o : Option (T20B.nearIdx K)) :
    Measurable (pieceRead Q W P K n o) := by
  apply measurable_pi_iff.mpr
  intro c
  cases o with
  | none => exact (isPsiVersion_psiMN (Q := Q) hW (Nat.zero_le K)).meas c
  | some b => exact ((T20B.blkKn_spec hW Q hKn b.1).2.1 c)

private def pieceFirst (Q : PsiParams) (W : WNSpace → Ω → ℝ) (P : Measure Ω)
    (K n : ℕ) (o : Option (T20B.nearIdx K)) : Ω × Ω → T20B.dyD → ℝ :=
  fun z => pieceRead Q W P K n o z.1

private def pieceSecond (Q : PsiParams) (W : WNSpace → Ω → ℝ) (P : Measure Ω)
    (K n : ℕ) (o : Option (T20B.nearIdx K)) : Ω × Ω → T20B.dyD → ℝ :=
  fun z => pieceRead Q W P K n o z.2

 

theorem iIndep_esCopySigma_psi_piece (hW : IsWhiteNoise P W) (Q : PsiParams)
    {K n : ℕ} (hKn : K ≤ n) :
    iIndep (LQGMetric.esCopySigma (pieceFirst Q W P K n)
      (pieceSecond Q W P K n)) (P.prod P) := by
  haveI : IsProbabilityMeasure P := hW.isProbabilityMeasure
  have hm : ∀ o, Measurable (pieceRead Q W P K n o) :=
    measurable_pieceRead hW Q hKn
  have hind := iIndepFun_psi_piece hW Q hKn
  have h := (iIndepFun_iff_iIndep _ _ _).1
    (T20B.iIndepFun_sumElim_prod hm hind)
  convert h using 2 with k
  rcases k with i | i <;> rfl

 
theorem psi_piece_copy_same_law (hW : IsWhiteNoise P W) (Q : PsiParams)
    {K n : ℕ} (hKn : K ≤ n) (o : Option (T20B.nearIdx K)) :
    (P.prod P).map (pieceSecond Q W P K n o) =
      (P.prod P).map (pieceFirst Q W P K n o) := by
  haveI : IsProbabilityMeasure P := hW.isProbabilityMeasure
  exact (T20B.map_comp_snd (measurable_pieceRead hW Q hKn o)).trans
    (T20B.map_comp_fst (measurable_pieceRead hW Q hKn o)).symm


end SupercriticalLQGUniqueness.B2.DG20Conc
