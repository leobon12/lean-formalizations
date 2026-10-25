import SupercriticalLQGUniqueness.B2.DG20Conc.LaneBTailTransfer
import LQGMetric.LFPP.WeylUpper
import LQGMetric.Metric.WeylPathLength
import LQGMetric.Topo.Disconnect

 









set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set Metric
open scoped ENNReal

namespace SupercriticalLQGUniqueness.B2.DG20Conc

open LQGMetric LQGMetric.DDDF LQGMetric.LFPP LQGMetric.WhiteNoise

private theorem laneB_len_le_of_field_bound
    (ξ : ℝ) {f g : ℂ → ℝ} (hf : Continuous f) (hg : Continuous g)
    {U : Set ℂ} {P : ℝ → ℂ} {a b M : ℝ}
    (hab : a ≤ b) (hP : ContinuousOn P (Icc a b))
    (hPU : P '' Icc a b ⊆ U)
    (hfg : ∀ z ∈ U, ξ * (f z - g z) ≤ M) :
    (lfppContMetric ξ f hf).len P a b ≤
      ENNReal.ofReal (Real.exp M) * (lfppContMetric ξ g hg).len P a b := by
  let ψ : C(ℂ, ℝ) := ⟨fun z => f z - g z, hf.sub hg⟩
  have hW : ∀ x y : ℂ,
      ENNReal.ofReal ((lfppContMetric ξ f hf).1 (x, y)) =
        weylScale ξ ψ (lfppContMetric ξ g hg) x y := by
    intro x y
    rw [lfppContMetric_apply, ENNReal.ofReal_toReal (lfppD_ne_top hf x y)]
    convert lfppD_add_eq_weylScale hg ψ x y using 1
    congr 1
    funext z
    simp [ψ]
  exact curveLength_weyl_le (lfppContMetric ξ f hf) hW hab
    ((lfppContMetric ξ g hg).continuous_pt.comp_continuousOn hP)
    (fun t ht => hPU ⟨t, ht, rfl⟩) (fun z hz => hfg z hz)

 

theorem laneB_aroundDist_compare_of_abs_sub_le
    (ξ : ℝ) {f g : ℂ → ℝ} (hf : Continuous f) (hg : Continuous g)
    (U E F : Set ℂ) {M : ℝ}
    (hfg : ∀ z ∈ U, |f z - g z| ≤ M) :
    (lfppContMetric ξ f hf).aroundDist U E F ≤
        ENNReal.ofReal (Real.exp (|ξ| * M)) *
          (lfppContMetric ξ g hg).aroundDist U E F ∧
    (lfppContMetric ξ g hg).aroundDist U E F ≤
        ENNReal.ofReal (Real.exp (|ξ| * M)) *
          (lfppContMetric ξ f hf).aroundDist U E F := by
  let e : ℝ≥0∞ := ENNReal.ofReal (Real.exp (|ξ| * M))
  have he0 : e ≠ 0 := (ENNReal.ofReal_pos.mpr (Real.exp_pos _)).ne'
  have heTop : e ≠ ⊤ := ENNReal.ofReal_ne_top
  have hbound : ∀ z ∈ U, ξ * (f z - g z) ≤ |ξ| * M := by
    intro z hz
    calc
      ξ * (f z - g z) ≤ |ξ * (f z - g z)| := le_abs_self _
      _ = |ξ| * |f z - g z| := abs_mul _ _
      _ ≤ |ξ| * M := mul_le_mul_of_nonneg_left (hfg z hz) (abs_nonneg ξ)
  have hbound' : ∀ z ∈ U, ξ * (g z - f z) ≤ |ξ| * M := by
    intro z hz
    have h := hfg z hz
    rw [abs_sub_comm] at h
    calc
      ξ * (g z - f z) ≤ |ξ * (g z - f z)| := le_abs_self _
      _ = |ξ| * |g z - f z| := abs_mul _ _
      _ ≤ |ξ| * M := mul_le_mul_of_nonneg_left h (abs_nonneg ξ)
  have around_le (u v : ℂ → ℝ) (hu : Continuous u) (hv : Continuous v)
      (hb : ∀ z ∈ U, ξ * (u z - v z) ≤ |ξ| * M) :
      (lfppContMetric ξ u hu).aroundDist U E F ≤
        e * (lfppContMetric ξ v hv).aroundDist U E F := by
    unfold ContMetric.aroundDist
    rw [ENNReal.mul_iInf_of_ne he0 heTop]
    refine iInf_mono fun a => ?_
    rw [ENNReal.mul_iInf_of_ne he0 heTop]
    refine iInf_mono fun b => ?_
    rw [ENNReal.mul_iInf_of_ne he0 heTop]
    refine iInf_mono fun P => ?_
    rw [ENNReal.mul_iInf_of_ne he0 heTop]
    refine iInf_mono fun hab => ?_
    rw [ENNReal.mul_iInf_of_ne he0 heTop]
    refine iInf_mono fun hP => ?_
    rw [ENNReal.mul_iInf_of_ne he0 heTop]
    refine iInf_mono fun hPU => ?_
    rw [ENNReal.mul_iInf_of_ne he0 heTop]
    refine iInf_mono fun _hD => ?_
    exact laneB_len_le_of_field_bound ξ hu hv hab hP hPU hb
  exact ⟨around_le f g hf hg hbound, around_le g f hg hf hbound'⟩

 


theorem laneB_aroundDist_compare_cutoff
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (W : WNSpace → Ω → ℝ) (Q : PsiParams) (ξ : ℝ)
    (ω : Ω) (m : ℕ) (U E F : Set ℂ) (hU : U ⊆ T20D.bigBox)
    (hf : Continuous fun x => phiMN W P 0 m x ω)
    (hg : Continuous fun x => psiMN Q W P 0 m x ω)
    (hfin : XAB (fun n y => phiMN W P 0 n (y + T20C.cBig) ω)
      (fun n y => psiMN Q W P 0 n (y + T20C.cBig) ω) 5 5 ≠ ⊤) :
    let e := ENNReal.ofReal (Real.exp (|ξ| * T20C.Xbig Q W P ω))
    let full := (lfppContMetric ξ (fun x => phiMN W P 0 m x ω) hf).aroundDist U E F
    let cut := (lfppContMetric ξ (fun x => psiMN Q W P 0 m x ω) hg).aroundDist U E F
    full ≤ e * cut ∧ cut ≤ e * full := by
  dsimp
  exact laneB_aroundDist_compare_of_abs_sub_le ξ hf hg U E F
    (fun z hz => T20D.abs_sub_le_Xbig Q hfin m (hU hz))

 

theorem laneB_aroundDist_four_tail_implications
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (W : WNSpace → Ω → ℝ) (Q : PsiParams) (ξ : ℝ)
    (ω : Ω) (m : ℕ) (U E F : Set ℂ) (t : ℝ≥0∞) (hU : U ⊆ T20D.bigBox)
    (hf : Continuous fun x => phiMN W P 0 m x ω)
    (hg : Continuous fun x => psiMN Q W P 0 m x ω)
    (hfin : XAB (fun n y => phiMN W P 0 n (y + T20C.cBig) ω)
      (fun n y => psiMN Q W P 0 n (y + T20C.cBig) ω) 5 5 ≠ ⊤) :
    let e := ENNReal.ofReal (Real.exp (|ξ| * T20C.Xbig Q W P ω))
    let full := (lfppContMetric ξ (fun x => phiMN W P 0 m x ω) hf).aroundDist U E F
    let cut := (lfppContMetric ξ (fun x => psiMN Q W P 0 m x ω) hg).aroundDist U E F
    (full < t → cut < e * t) ∧
    (cut < t → full < e * t) ∧
    (e * t < full → t < cut) ∧
    (e * t < cut → t < full) := by
  dsimp
  have hcmp := laneB_aroundDist_compare_cutoff P W Q ξ ω m U E F hU hf hg hfin
  exact laneB_four_tail_implications
    (ENNReal.ofReal_pos.mpr (Real.exp_pos _)).ne'
    ENNReal.ofReal_ne_top hcmp.1 hcmp.2

 

theorem laneB_ae_aroundDist_compare_cutoff
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (W : WNSpace → Ω → ℝ) (hW : IsWhiteNoise P W)
    (Q : PsiParams) (ξ : ℝ) :
    ∀ᵐ ω ∂P, ∀ m : ℕ, ∀ U E F : Set ℂ, U ⊆ T20D.bigBox →
      let e := ENNReal.ofReal (Real.exp (|ξ| * T20C.Xbig Q W P ω))
      let full := (lfppContMetric ξ (fun x => phiMN W P 0 m x ω)
        ((isPhiVersion_phiMN hW (Nat.zero_le m)).cont ω)).aroundDist U E F
      let cut := (lfppContMetric ξ (fun x => psiMN Q W P 0 m x ω)
        ((isPsiVersion_psiMN hW (Nat.zero_le m)).cont ω)).aroundDist U E F
      full ≤ e * cut ∧ cut ≤ e * full := by
  filter_upwards [T20D.ae_XAB_shift_ne_top hW Q T20C.cBig 5 5] with ω hfin
  intro m U E F hU
  exact laneB_aroundDist_compare_cutoff P W Q ξ ω m U E F hU
    ((isPhiVersion_phiMN hW (Nat.zero_le m)).cont ω)
    ((isPsiVersion_psiMN hW (Nat.zero_le m)).cont ω) hfin

end SupercriticalLQGUniqueness.B2.DG20Conc
