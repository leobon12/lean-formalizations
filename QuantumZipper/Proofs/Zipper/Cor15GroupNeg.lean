import QuantumZipper.Proofs.Zipper.B2Uncond
import QuantumZipper.Proofs.GFF.CoordRegFwd
import QuantumZipper.Statements.Thm15
import QuantumZipper.Proofs.Zipper.Cor15Partial

/-!
# Corollary 1.5 (b) for two unzipping times

Sheffield, *Conformal weldings of random surfaces*, arXiv:1012.4797, Corollary 1.5 (p. 17): the
capacity zipper satisfies `Z^CAP_{s+t} = Z^CAP_s Z^CAP_t` almost surely. Here: the case `s, t < 0`
(two unzippings), unconditionally (`theorem1_5b_neg_neg`), and the case `s = 0`, `t < 0`
(`theorem1_5b_zero_neg`: `Z^CAP_0` fixes an unzipped configuration up to `ConfigEq`).

Route (the paper calls the group property "immediate"; for unzipping it is the semigroup property
of the forward Loewner flow, blueprint A1(a), plus the composition law for coordinate changes):
with `a = −s`, `b = −t`, `T = a + b`,

* drivers: `u ↦ W(b + a + u) − W(b + a)` on both sides (pathwise algebra);
* fields: `B2.b2_regEq` (RC3 composition law, `CoordRegComp.ae_evalReg_Yf_fc`) gives a.s.
  `RegEq (h⁰_T) (coordChange Y_a (revMap V a) Q)` where `h⁰_T` is the field unzipped by `T` and
  `Y_a` the field unzipped by `b`; the map `revMap V a` agrees on `ℍ` with the unzipping map
  `fwdMapInv (W(b + ·) − W b) a` of the second step (A1(c) and locality of the reverse flow in
  the driver), so the regularized averages agree (`CoordReg.avgReg_coordChange_congr`).
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal ENNReal

namespace QuantumZipper
namespace Cor15Group

open B2

/-- The unzipping map of the second step agrees on `ℍ` with the reverse flow of the
time-reversed driver of the composite unzipping. -/
theorem fwdMapInv_wfut_eqOn {W : ℝ → ℝ} (hW : Continuous W) {a b : ℝ} (ha : 0 ≤ a)
    (hb : 0 ≤ b) :
    EqOn (fwdMapInv (fun u => W (b + max u 0) - W b) a) (revMap (vrev W (a + b)) a) H := by
  intro z hz
  have hc : Continuous fun u => W (b + max u 0) - W b := by fun_prop
  rw [fwdMapInv_eq_revMap_vrev hc (by simp) ha hz]
  refine ReverseFlow.revMap_congr_drive z fun r hr => ?_
  rw [vrev_of_mem hr, vrev_of_mem ⟨hr.1, by linarith [hr.2]⟩, max_eq_left (by linarith [hr.2]),
    max_eq_left ha]
  ring_nf

/-- **Corollary 1.5 (b) for `s, t < 0`** (unconditional). -/
theorem theorem1_5b_neg_neg (κ : ℝ) {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (B : ℝ≥0 → Ω → ℝ) (X : Ω → FieldSample)
    (hB : IsBrownianReal B P) (hX : IsFreeGFFModConstH X P) (hind : IndepFun (pathOf B) X P)
    {s t : ℝ} (hs : s < 0) (ht : t < 0) :
    ∀ᵐ ω ∂P, ConfigEq
      (zipCap (Real.sqrt κ) (s + t) (ofFun (h0rev κ) + X ω, drive κ B ω))
      (zipCap (Real.sqrt κ) s (zipCap (Real.sqrt κ) t (ofFun (h0rev κ) + X ω, drive κ B ω))) := by
  set a := -s with ha_def
  set b := -t with hb_def
  have ha : 0 ≤ a := by linarith
  have hb : 0 ≤ b := by linarith
  have hst : -(s + t) = a + b := by ring
  rw [zipCap_of_neg (by linarith : s + t < 0), zipCap_of_neg ht, zipCap_of_neg hs, hst]
  filter_upwards [b2_regEq (κ := κ) (T := a + b) (t := a) hB hX hind ha (by linarith),
    hB.cont] with ω hreg hc
  have hW : Continuous (drive κ B ω) := drive_continuous hc
  refine ⟨fun k z => ?_, fun u hu => ?_⟩
  · have e1 : h0f κ (a + b) B X ω =
        (zipCapDown (Real.sqrt κ) (a + b) (ofFun (h0rev κ) + X ω, drive κ B ω)).1 := by
      simp only [h0f, Yf, zipped, cfg, sub_zero]
    have e2 : Yf κ (a + b) a B X ω =
        (zipCapDown (Real.sqrt κ) b (ofFun (h0rev κ) + X ω, drive κ B ω)).1 := by
      simp only [Yf, zipped, cfg, show a + b - a = b by ring]
    rw [← e1, hreg k z, e2]
    exact (CoordReg.avgReg_coordChange_congr _ (fwdMapInv_wfut_eqOn hW ha hb) _ k z).symm
  · simp only [zipCapDown, max_eq_left hu]
    rw [max_eq_left (show (0 : ℝ) ≤ -s + u by linarith), max_eq_left (show (0 : ℝ) ≤ -s by linarith),
      show -t + (-s + u) = a + b + u by rw [ha_def, hb_def]; ring,
      show -t + -s = a + b by rw [ha_def, hb_def]; ring]
    ring

/-- `Z^CAP_0` fixes, up to `ConfigEq`, every configuration whose field is regular at the dyadic
folded circles and whose driver vanishes at `0`: at time `0` the welding driver's reverse map is
the identity on `ℍ`, so the zipped field's raw values are the regularized values of the old one. -/
theorem configEq_zipCapUp_zero (γ : ℝ) (y : FieldSample × (ℝ → ℝ))
    (hreg : ∀ i : ℕ, evalReg y.1 (foldedCircle (CoordsFull.fullIndex i).1
      (CoordsFull.fullIndex i).2) = y.1 (foldedCircle (CoordsFull.fullIndex i).1
      (CoordsFull.fullIndex i).2))
    (h0 : y.2 0 = 0) : ConfigEq y (zipCapUp γ 0 y) := by
  obtain ⟨hWc, hW0, -, -⟩ := weldDriver_spec ⟨_, Cor15Partial.isWeldingDriver_zero γ y.1⟩
  refine ⟨UnzipFull.regEq_of_coordsFull (funext fun i => ?_), fun u hu => ?_⟩
  · have hr := UnzipFull.fullIndex_radius_pos i
    show y.1 _ = coordChange y.1 (revMapInv (weldDriver γ y.1 0) 0) (Qc γ) _
    rw [CoordReg.coordChange_fc_congr y.1 (Cor15Partial.revMapInv_zero_eqOn hWc hW0) _ _ hr,
      Cor15Partial.coordChange_id_apply, hreg i]
  · show y.2 u = if u ≤ 0 then weldDriver γ y.1 0 (0 - max u 0) - weldDriver γ y.1 0 0
      else y.2 (u - 0) - weldDriver γ y.1 0 0
    split_ifs with h
    · have hu0 : u = 0 := le_antisymm h hu
      subst hu0
      simp [h0]
    · simp [hW0]

/-- **Corollary 1.5 (b) for `s = 0`, `t < 0`** (unconditional). -/
theorem theorem1_5b_zero_neg (κ : ℝ) {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (B : ℝ≥0 → Ω → ℝ) (X : Ω → FieldSample)
    (hB : IsBrownianReal B P) (hX : IsFreeGFFModConstH X P) (hind : IndepFun (pathOf B) X P)
    {t : ℝ} (ht : t < 0) :
    ∀ᵐ ω ∂P, ConfigEq
      (zipCap (Real.sqrt κ) (0 + t) (ofFun (h0rev κ) + X ω, drive κ B ω))
      (zipCap (Real.sqrt κ) 0 (zipCap (Real.sqrt κ) t (ofFun (h0rev κ) + X ω, drive κ B ω))) := by
  have hb : 0 ≤ -t := by linarith
  rw [zero_add, zipCap_of_nonneg le_rfl, zipCap_of_neg ht]
  filter_upwards [ae_all_iff.2 (CoordRegComp.ae_evalReg_Yf_fc (κ := κ) (T := -t) (t := 0) hB hX
    hind le_rfl hb), hB.cont] with ω hreg hc
  refine configEq_zipCapUp_zero _ _ (fun i => ?_) (by simp [zipCapDown])
  have h := hreg i
  rw [map_revMap_Vr_zero hc hb
    (TwoPoint.foldedCircle_ae_mem_H _ (UnzipFull.fullIndex_radius_pos i))] at h
  simpa only [Yf, zipped, cfg, sub_zero] using h

end Cor15Group
end QuantumZipper
