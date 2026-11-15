/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec5.Aux61CptLandAccess
import InteractingSLE.Spec.Sec5.Aux61NjTarget
import InteractingSLE.Spec.Sec5.Aux61NjGerm

/-!
# The landing part with the fixed eastern height `eastHeight S 1`

Packet PROVE-AUX61-CAPTURE (rulings R103, R103a; NOJUMP's branch round). On the landing part the per-outcome word
carries the fixed height `Aux61Nj.eastHeight S 1`. At a produced collar point `ξ₀ > 0` whose physical point is in `ℍ`,
`ξ₀` lies east of the right junction (`junR_lt_of_extendFrom_mem_H`), the returned value is NOJUMP's
`λ(16/κ) − πχ`, and the inherited phase is `2π` (NOJUMP's `ae_height_eq_eastHeight_one`, no input). Hence the height
clause holds (`ae_collarHeight`), and the landing test gives pinch-free counterflow accesses `Aux61Nj.CfAccessNP` on the
whole landing interval (`ae_cfAccessNP_of_landRecords`).

R48/R77 respected; nothing here replaces a source theorem.
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory Set Filter Topology Metric
open QuantumZipper (H Hbar chiC fwdHull fwdMap fwdMapInv)
open scoped NNReal ENNReal Real

namespace InteractingSLE.Sec5.Aux61Cpt
open WangWu GlueCond Cond44Ref Aux61GWord Aux61Cmp LawUnique Aux61Restart MartChar.RealFlow
open Aux61SlitW Aux61SlitW.SourceSetting Aux61GAlign Aux61R1C Aux61Asm2 Aux61SlitWX Aux61GWindow17
open CrossCond.Word49
universe u

variable {S : SourceSetting.{u}} {F : SourceRestartData S.Ω S.nL S.nR}

/-- A component access is a pinch-free access. -/
theorem CfAccessC.toNP {i : F.ι} {p : S.Ω × HistorySpace 0 0} {b : ℝ} (h : CfAccessC S F i p b) :
    Aux61Nj.CfAccessNP S F i p b := by
  obtain ⟨ξ₀, δ, x, hδ, hx, hcol, hfin, -, hxb, hb0, hbJ, hξ, hword⟩ := h
  exact ⟨ξ₀, δ, x, hδ, hx, hcol, hfin, hxb, hb0, hbJ, hξ, hword⟩

/-- **A positive counterflow-chart point with physical point in `ℍ` lies east of the right junction.** -/
theorem junR_lt_of_extendFrom_mem_H {w : ℝ → ℝ} {γ : ℝ → ℂ} (hw : Continuous w) (hw0 : w 0 = 0)
    (hγ : IsLoewnerTrace w γ) {s : ℝ} (hs : 0 ≤ s) {x : ℝ} (hx : 0 < x)
    (hF : extendFrom H (fwdMapInv w s) (negInv (x : ℂ)) ∈ H) : junR w s < x := by
  rw [Aux61Nj.negInv_ofReal] at hF
  have h1 := neg_rightImg_sub_lt_of_extendFrom_mem_H hγ hw hw0 hs hF
  set L := -rightImg (fun r => -w r) 0 s - w s with hL
  have hL0 : L ≤ 0 := by
    have := le_rightImg_zero (w := fun r => -w r) hw.neg hs
    linarith
  have hjR : junR w s = -1 / L := rfl
  rw [hjR]
  rcases hL0.lt_or_eq with hlt | heq
  · rw [div_lt_iff_of_neg hlt]
    have h2 := mul_lt_mul_of_pos_right h1 hx
    rw [neg_mul, inv_mul_cancel₀ hx.ne'] at h2
    linarith
  · rw [heq, div_zero]
    exact hx

variable (C : RestartChoices S) (R : ReaderFacts C.toR1Restart)

include R in
/-- **The height clause along produced collars**, almost surely on the selected records of the normalized source,
for chart points carrying the eastern height `eastHeight S 1`. -/
theorem ae_collarHeight (hTip : OwnTipForwardLimit S) (V : WindowData C.toR1Restart C.hasChart)
    (hExit : PhysicalExit C.toR1Restart C.hasChart) (i : C.Idx) :
    ∀ᵐ p ∂S.μ, (S.marksData (normSource C.toR1Restart C.hasChart)).Z i p ∈
        (S.marksData (normSource C.toR1Restart C.hasChart)).B i →
      ∀ (b : ℝ) (z : ℂ), z ∈ H →
        ((normSource C.toR1Restart C.hasChart).data i).bR b = Aux61Nj.eastHeight S 1 →
        CollarHeight S (normSource C.toR1Restart C.hasChart) i p z b := by
  set F := normSource C.toR1Restart C.hasChart with hFdef
  have hR := Aux61GCaptureNext.normalized_cut_restart C.toR1Restart C.hasChart R hTip V hExit
  have hgeo : ∀ᵐ p ∂S.μ, p ∈ F.event i →
      SourceChartGeometry (fun t : ℝ => S.own.W t.toNNReal p.1)
        (fun t => S.path p.1 t.toNNReal) (cfHullQ (rationalTime S.s) p.2) (F.start i)
        (sourceChart F (rationalTime S.s) S.own.W S.own.VL S.own.VR S.life i p) := by
    filter_upwards [R.ae_geometry C.hasChart i] with p hp he
    exact hp he.1
  filter_upwards [Aux61Nj.ae_height_eq_eastHeight_one hR i hgeo (ae_cfW_trace S), ae_cfW_trace S]
    with p hph hcfp hB b z hzH hbR ξ₀ δ hξ hδ hcol hfin hxb hcz phase hphase
  obtain ⟨hw0, γ, hγ⟩ := hcfp
  have hw : Continuous (cfW S p) := Sec4.continuous_rpath_regPath _
  have hs : (0 : ℝ) ≤ (rationalTime S.s : ℝ) := NNReal.coe_nonneg _
  have hF : extendFrom H (fwdMapInv (cfW S p) (rationalTime S.s)) (negInv (ξ₀ : ℂ)) ∈ H := by
    have h := congrArg negInv hcz
    rw [cfBdry, negInv_negInv'] at h
    rw [h]
    exact negInv_mem_H hzH
  have hjun := junR_lt_of_extendFrom_mem_H hw hw0 hγ hs hξ hF
  have h2π := (hph hB b ξ₀ δ ξ₀ hδ (mem_ball_self hδ) hcol hfin hxb hjun hF).1
  have := GlueImg.nhdsWithin_H_neBot b
  have hphase' : phase = 2 * π := tendsto_nhds_unique hphase h2π
  have hret := Aux61Nj.returnedCfData_eq_of_extendFrom_mem_H S p hγ hw0 hξ hF
  have h := Aux61Nj.returned_add_eq_eastHeight S 1 hret
  rw [Int.cast_one, mul_one] at h
  rw [hbR, hphase', ← h, hret]

include R in
/-- **Pinch-free counterflow accesses on the whole landing interval**, from the landing test and the fixed eastern
height. -/
theorem ae_cfAccessNP_of_landRecords (hTip : OwnTipForwardLimit S)
    (V : WindowData C.toR1Restart C.hasChart) (hExit : PhysicalExit C.toR1Restart C.hasChart)
    (i : C.Idx) (L : LandParam)
    (hL : ∀ y ∈ (normSource C.toR1Restart C.hasChart).selected i, y ∈ landRecords S (idxTime C i) L)
    (hword : ∀ b : ℝ, |b - L.1.1| < L.1.2.1 →
      ((normSource C.toR1Restart C.hasChart).data i).bR b = Aux61Nj.eastHeight S 1) :
    ∀ᵐ p ∂S.μ, (S.marksData (normSource C.toR1Restart C.hasChart)).Z i p ∈
        (S.marksData (normSource C.toR1Restart C.hasChart)).B i →
      ∀ b : ℝ, |b - L.1.1| < L.1.2.1 → b ≠ 0 →
        b ∉ ((normSource C.toR1Restart C.hasChart).data i).JR →
        Aux61Nj.CfAccessNP S (normSource C.toR1Restart C.hasChart) i p b := by
  filter_upwards [ae_cfAccessC_of_landRecords C R hTip V hExit i L hL,
    ae_collarHeight C R hTip V hExit i] with p hacc hht hB b hb hb0 hbJ
  have hsel : sourceRecord (normSource C.toR1Restart C.hasChart) (rationalTime S.s)
      S.own.W S.own.VL S.own.VR S.life i p ∈ (normSource C.toR1Restart C.hasChart).selected i := hB
  have hyL := hL _ hsel
  have hzH := lt_of_lt_of_le (by exact_mod_cast L.2.2 : (0 : ℝ) < L.1.2.2.2)
    (landTest_phys S (idxTime C i) L hyL hb).2.1
  exact (hacc hB b hb hb0 hbJ (hht hB b _ hzH (hword b hb))).toNP

end InteractingSLE.Sec5.Aux61Cpt
