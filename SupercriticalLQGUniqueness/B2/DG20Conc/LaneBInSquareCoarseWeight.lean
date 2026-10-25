import SupercriticalLQGUniqueness.B2.DG20Conc.LaneBInSquareChosenGlue

 

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

open MeasureTheory Set

namespace SupercriticalLQGUniqueness.B2.DG20Conc

open LQGMetric LQGMetric.DDDF LQGMetric.WhiteNoise

theorem laneB_chosen_coarse_glueBox_weight
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (W : WNSpace → Ω → ℝ) (Q : PsiParams)
    (ξ : ℝ) {K : ℕ} (hK : 2 ≤ K) (ω : Ω)
    {γ : ℝ → ℂ} (M : ℝ)
    (hosc : ∀ b ∈ T20.coarseBlocks K γ,
      ∀ x ∈ S6U.glueBox K b,
        |phiMN W P 0 K x ω -
          phiMN W P 0 K (T20.dyCenter K b) ω| ≤ M)
    (hfin : XAB (fun n y => phiMN W P 0 n (y + T20C.cBig) ω)
      (fun n y => psiMN Q W P 0 n (y + T20C.cBig) ω) 5 5 ≠ ⊤) :
    ∀ b ∈ T20.coarseBlocks K γ,
      ∀ x ∈ S6U.glueBox K b,
        Real.exp (ξ * psiMN Q W P 0 K x ω) ≤
          Real.exp (|ξ| * (M + T20C.Xbig Q W P ω)) *
            Real.exp (ξ * phiMN W P 0 K (T20.dyCenter K b) ω) := by
  classical
  intro b hb x hx
  have hbI : b ∈ T20.blkIdx K := (Finset.mem_filter.1 hb).1
  have hxB := (S6U.glueBox_near hK hbI hx).1
  have hcut := T20D.abs_sub_le_Xbig (P := P) (W := W) Q hfin K hxB
  have hosc' := hosc b hb x hx
  have hcut' := abs_le.mp hcut
  have hosc'' := abs_le.mp hosc'
  have hd : |psiMN Q W P 0 K x ω -
      phiMN W P 0 K (T20.dyCenter K b) ω| ≤
        M + T20C.Xbig Q W P ω := by
    apply abs_le.mpr
    constructor <;> nlinarith [hcut'.1, hcut'.2, hosc''.1, hosc''.2]
  have hmul : ξ * (psiMN Q W P 0 K x ω -
      phiMN W P 0 K (T20.dyCenter K b) ω) ≤
      |ξ| * (M + T20C.Xbig Q W P ω) := by
    calc
      _ ≤ |ξ * (psiMN Q W P 0 K x ω -
          phiMN W P 0 K (T20.dyCenter K b) ω)| := le_abs_self _
      _ = |ξ| * |psiMN Q W P 0 K x ω -
          phiMN W P 0 K (T20.dyCenter K b) ω| := abs_mul _ _
      _ ≤ _ := mul_le_mul_of_nonneg_left hd (abs_nonneg _)
  rw [← Real.exp_add]
  exact Real.exp_le_exp.mpr (by nlinarith [hmul])

end SupercriticalLQGUniqueness.B2.DG20Conc
