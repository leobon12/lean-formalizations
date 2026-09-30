import QuantumZipper.Proofs.Zipper.XFlowEnergyDefs
import QuantumZipper.Proofs.Zipper.UnifUC1Rad

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# XFLOW-E1, step 1: the D33 radius-modulus lemmas with a general circle

The D33 lemmas `RegUnif.alphaUS_ae_facts`, `muUS_eq_map`, `muUS_zero_eq`, `admissible_muUS_zero`,
`admissible_muUS`, `abs_kernelCov2_muUS_rad_le` (`UnifUC1Push.lean`, `UnifUC1RadBasic.lean`,
`UnifUC1Rad.lean`), restated for `flowMu W (u, s, d, r)` (the D33 `muUS` with `radius k ↦ r`).
The circle enters only through `r > 0` and the bound `‖d‖ + r`; all constants are stated in
terms of a lower bound `rl ≤ r` and an upper bound `‖d‖ + r ≤ R₀` (the predicate `FBox`), so
they are uniform over `flowBox m`. No step uses `r ≤ 1`.

New here: the uniform bound `∫ |log Im| d fc(d, r) ≤ 200/√rl + |log R₀|`
(`integral_abs_log_im_fc_unif`, own elementary proof from the strip bound
`CoordRegComp.stripBound_foldedCircle` at height `1`), and `flowAdmStmt_holds_E1 : FlowAdmStmt`.

Sources: as the D33 files (Hu–Miller–Peres, Ann. Probab. 38 (2010), Prop. 2.1;
Duplantier–Sheffield, Invent. Math. 185 (2011), Prop. 3.1); the bookkeeping is own elementary.
-/

noncomputable section

open MeasureTheory Filter Metric Set
open scoped ENNReal Real Topology

namespace QuantumZipper
namespace F1

open RegCont B2 RegUnif

variable {W : ℝ → ℝ}

/-- Parameters `p = (u, s, d, r)` with `u, s ≥ 0`, `u + s ≤ T`, `rl ≤ r`, `‖d‖ + r ≤ R₀`. -/
def FBox (T rl R₀ : ℝ) (p : ℝ × ℝ × ℂ × ℝ) : Prop :=
  0 ≤ p.1 ∧ 0 ≤ p.2.1 ∧ p.1 + p.2.1 ≤ T ∧ rl ≤ p.2.2.2 ∧ ‖p.2.2.1‖ + p.2.2.2 ≤ R₀

theorem fBox_of_mem_flowBox {m : ℕ} {p : ℝ × ℝ × ℂ × ℝ} (hp : p ∈ flowBox m) :
    FBox (2 * (m : ℝ) + 2) (1 / ((m : ℝ) + 2)) (3 * ((m : ℝ) + 2)) p := by
  obtain ⟨⟨hu0, hu1⟩, ⟨hs0, hs1⟩, ⟨hre0, hre1⟩, ⟨him0, him1⟩, ⟨hr0, hr1⟩⟩ := hp
  have hn := Complex.norm_le_abs_re_add_abs_im p.2.2.1
  have h1 : |p.2.2.1.re| ≤ (m : ℝ) + 1 := abs_le.2 ⟨hre0, hre1⟩
  have h2 : |p.2.2.1.im| ≤ (m : ℝ) + 1 := abs_le.2 ⟨by linarith, him1⟩
  exact ⟨hu0, hs0, by linarith, hr0, by linarith⟩

/-- Uniform bound of the folded-circle average of `|log Im|` (own elementary proof). -/
theorem integral_abs_log_im_fc_unif {d : ℂ} {r rl R₀ : ℝ} (hrl : 0 < rl) (hr : rl ≤ r)
    (hR : ‖d‖ + r ≤ R₀) :
    ∫ z, |Real.log z.im| ∂foldedCircle d r ≤ 200 / Real.sqrt rl + |Real.log R₀| := by
  have hr0 : 0 < r := hrl.trans_le hr
  have hS := CoordRegComp.stripBound_foldedCircle d hr0 1 one_pos le_rfl
  rw [Real.one_rpow, mul_one] at hS
  have hl0 : Integrable (fun z : ℂ => |Real.log z.im|) (foldedCircle d r) :=
    (TwoPoint.integrable_log_im_foldedCircle d hr0).abs
  have hm : MeasurableSet {z : ℂ | z.im ≤ 1} :=
    measurableSet_le Complex.measurable_im measurable_const
  have hind : Integrable ({z : ℂ | z.im ≤ 1}.indicator (fun z => 1 + |Real.log z.im|))
      (foldedCircle d r) := ((integrable_const 1).add hl0).indicator hm
  have hpt : ∀ᵐ z ∂foldedCircle d r, |Real.log z.im| ≤
      {z : ℂ | z.im ≤ 1}.indicator (fun z => 1 + |Real.log z.im|) z + |Real.log R₀| := by
    filter_upwards [TwoPoint.foldedCircle_ae_norm_le d hr0.le] with z hzn
    by_cases h1 : z.im ≤ 1
    · rw [indicator_of_mem (show z ∈ {z : ℂ | z.im ≤ 1} from h1)]
      linarith [abs_nonneg (Real.log R₀)]
    · rw [indicator_of_notMem (show z ∉ {z : ℂ | z.im ≤ 1} from h1), zero_add]
      have h1' : 1 < z.im := not_le.1 h1
      have hl : 0 ≤ Real.log z.im := Real.log_nonneg h1'.le
      have hzR : z.im ≤ R₀ := (Complex.im_le_norm z).trans (hzn.trans hR)
      rw [abs_of_nonneg hl]
      exact (Real.log_le_log (by linarith) hzR).trans (le_abs_self _)
  have hsq : 200 / Real.sqrt r ≤ 200 / Real.sqrt rl :=
    div_le_div_of_nonneg_left (by norm_num) (Real.sqrt_pos.2 hrl) (Real.sqrt_le_sqrt hr)
  calc ∫ z, |Real.log z.im| ∂foldedCircle d r
      ≤ ∫ z, ({z : ℂ | z.im ≤ 1}.indicator (fun z => 1 + |Real.log z.im|) z + |Real.log R₀|)
          ∂foldedCircle d r := integral_mono_ae hl0 (hind.add (integrable_const _)) hpt
    _ = ∫ z, {z : ℂ | z.im ≤ 1}.indicator (fun z => 1 + |Real.log z.im|) z ∂foldedCircle d r +
          |Real.log R₀| := by
        rw [integral_add hind (integrable_const _)]; simp
    _ ≤ 200 / Real.sqrt rl + |Real.log R₀| := by linarith

/-- Pointwise facts of the second unzip map along `fc(d, r)` (`alphaUS_ae_facts`). -/
theorem e1_flowNu_ae_facts (hW : Continuous W) {T Mw rl R₀ : ℝ}
    (hM : ∀ t ∈ Icc (0 : ℝ) T, |W t| ≤ Mw) (hrl : 0 < rl) {p : ℝ × ℝ × ℂ × ℝ}
    (hp : FBox T rl R₀ p) :
    ∀ᵐ z ∂foldedCircle p.2.2.1 p.2.2.2, z ∈ H ∧ ‖z‖ ≤ R₀ ∧
      z.im ≤ (revMap (vrev W (p.1 + p.2.1)) p.2.1 z).im ∧
      revMap (vrev W (p.1 + p.2.1)) p.2.1 z ∈ H ∧
      ‖revMap (vrev W (p.1 + p.2.1)) p.2.1 z‖ ≤ revBound (2 * Mw) T R₀ := by
  obtain ⟨hu, hs, hus, hr, hR⟩ := hp
  have hr0 : 0 < p.2.2.2 := hrl.trans_le hr
  filter_upwards [TwoPoint.foldedCircle_ae_mem_H p.2.2.1 hr0,
    TwoPoint.foldedCircle_ae_norm_le p.2.2.1 hr0.le] with z hz hzn
  have hV := continuous_vrev hW (p.1 + p.2.1)
  refine ⟨hz, hzn.trans hR, im_le_im_revMap _ hV z hz hs, TwoPoint.im_revMap_pos hV hz hs, ?_⟩
  exact (norm_revMap_le_revBound hV hs
    (fun r _ => abs_vrev_le hM ⟨add_nonneg hu hs, hus⟩ r) _ (hzn.trans hR)).trans
    (revBound_mono (by linarith))

theorem e1_isProbabilityMeasure_flowNu (hW : Continuous W) {p : ℝ × ℝ × ℂ × ℝ} (hs : 0 ≤ p.2.1) :
    IsProbabilityMeasure (flowNu W p) := by
  have hRm := TwoPoint.measurable_revMap (continuous_vrev hW (p.1 + p.2.1)) hs
  unfold flowNu; infer_instance

theorem e1_flowNu_ae_H_norm (hW : Continuous W) {T Mw rl R₀ : ℝ}
    (hM : ∀ t ∈ Icc (0 : ℝ) T, |W t| ≤ Mw) (hrl : 0 < rl) {p : ℝ × ℝ × ℂ × ℝ}
    (hp : FBox T rl R₀ p) :
    ∀ᵐ x ∂flowNu W p, x ∈ H ∧ ‖x‖ ≤ revBound (2 * Mw) T R₀ := by
  have hRm := TwoPoint.measurable_revMap (continuous_vrev hW (p.1 + p.2.1)) hp.2.1
  exact (ae_map_iff hRm.aemeasurable (measurableSet_H_norm_le _)).2
    ((e1_flowNu_ae_facts hW hM hrl hp).mono fun z hz => ⟨hz.2.2.2.1, hz.2.2.2.2⟩)

theorem e1_flowMu_eq_map (hW : Continuous W) (hW0 : W 0 = 0) {T Mw rl R₀ : ℝ}
    (hM : ∀ t ∈ Icc (0 : ℝ) T, |W t| ≤ Mw) (hrl : 0 < rl) {p : ℝ × ℝ × ℂ × ℝ}
    (hp : FBox T rl R₀ p) {ρ : ℝ} (hρ : 0 < ρ) :
    flowMu W p ρ = (bindFc (flowNu W p) ρ).map (revMap (vrev W p.1) p.1) := by
  have := e1_isProbabilityMeasure_flowNu hW hp.2.1
  refine Measure.map_congr ?_
  filter_upwards [CoordReg.bind_fc_mem_H_norm _ hρ
    ((e1_flowNu_ae_H_norm hW hM hrl hp).mono fun x hx => hx.2)] with x hx
  exact fwdMapInv_eq_revMap_vrev hW hW0 hp.1 hx.1

/-- `flowMu p 0 = (ψ_{u+s})_* fc(d, r)` (`muUS_zero_eq`). -/
theorem e1_flowMu_zero_eq (hW : Continuous W) (hW0 : W 0 = 0) {T Mw rl R₀ : ℝ}
    (hM : ∀ t ∈ Icc (0 : ℝ) T, |W t| ≤ Mw) (hrl : 0 < rl) {p : ℝ × ℝ × ℂ × ℝ}
    (hp : FBox T rl R₀ p) :
    flowMu W p 0 =
      (foldedCircle p.2.2.1 p.2.2.2).map (revMap (vrev W (p.1 + p.2.1)) (p.1 + p.2.1)) := by
  have := e1_isProbabilityMeasure_flowNu hW hp.2.1
  have hαH := (e1_flowNu_ae_H_norm hW hM hrl hp).mono fun x hx => hx.1
  have hRm := TwoPoint.measurable_revMap (continuous_vrev hW (p.1 + p.2.1)) hp.2.1
  have hψm := TwoPoint.measurable_revMap (continuous_vrev hW p.1) hp.1
  show (bindFc (flowNu W p) 0).map (fwdMapInv W p.1) = _
  rw [bindFc_zero_of_ae_H hαH]
  have e1 : (flowNu W p).map (fwdMapInv W p.1) =
      (flowNu W p).map (revMap (vrev W p.1) p.1) := by
    refine Measure.map_congr ?_
    filter_upwards [hαH] with x hx
    exact fwdMapInv_eq_revMap_vrev hW hW0 hp.1 hx
  rw [e1]
  unfold flowNu
  rw [Measure.map_map hψm hRm]
  refine Measure.map_congr ?_
  filter_upwards [TwoPoint.foldedCircle_ae_mem_H p.2.2.1 (hrl.trans_le hp.2.2.2.1)] with z hz
  exact (revMap_vrev_split hW hp.1 hp.1 hp.2.1 le_rfl hz).symm

theorem admissible_flowMu_zero (hW : Continuous W) (hW0 : W 0 = 0) {T Mw rl R₀ : ℝ}
    (hM : ∀ t ∈ Icc (0 : ℝ) T, |W t| ≤ Mw) (hrl : 0 < rl) {p : ℝ × ℝ × ℂ × ℝ}
    (hp : FBox T rl R₀ p) :
    IsAdmissibleH (flowMu W p 0) ∧ flowMu W p 0 univ = 1 := by
  rw [e1_flowMu_zero_eq hW hW0 hM hrl hp]
  obtain ⟨hu, hs, hus, hr, hR⟩ := hp
  have hV := continuous_vrev hW (p.1 + p.2.1)
  have ht : 0 ≤ p.1 + p.2.1 := add_nonneg hu hs
  have hRm := TwoPoint.measurable_revMap hV ht
  have hr0 : 0 < p.2.2.2 := hrl.trans_le hr
  have hG : GoodM ((foldedCircle p.2.2.1 p.2.2.2).map (revMap (vrev W (p.1 + p.2.1))
      (p.1 + p.2.1))) (1 / 3) (frostC T rl R₀) (revBound (2 * Mw) T R₀) := by
    refine ⟨by infer_instance, isFrostman_pfc_frostC hV ht hus hrl hr hR, ?_⟩
    refine ae_iff.1 ((ae_map_iff hRm.aemeasurable (measurableSet_closedBall_inter_Hbar _)).2 ?_)
    filter_upwards [TwoPoint.foldedCircle_ae_mem_H _ hr0,
      TwoPoint.foldedCircle_ae_norm_le _ hr0.le] with z hz hzn
    refine ⟨mem_closedBall_zero_iff.2 ((norm_revMap_le_revBound hV ht
      (fun r _ => abs_vrev_le hM ⟨ht, hus⟩ r) _ (hzn.trans hR)).trans (revBound_mono hus)),
      show (0 : ℝ) ≤ _ from le_of_lt (TwoPoint.im_revMap_pos hV hz ht)⟩
  exact ⟨hG.admissible (by norm_num), hG.prob.measure_univ⟩

/-- Every `flowMu p σ`, `σ ∈ [0,1]`, is an admissible probability measure (`admissible_muUS`). -/
theorem admissible_flowMu (hW : Continuous W) (hW0 : W 0 = 0) {T Mw rl R₀ : ℝ}
    (hM : ∀ t ∈ Icc (0 : ℝ) T, |W t| ≤ Mw) (hrl : 0 < rl) {p : ℝ × ℝ × ℂ × ℝ}
    (hp : FBox T rl R₀ p) {σ : ℝ} (hσ : 0 ≤ σ) (hσ1 : σ ≤ 1) :
    IsAdmissibleH (flowMu W p σ) ∧ flowMu W p σ univ = 1 := by
  rcases hσ.eq_or_lt with h | h
  · subst h; exact admissible_flowMu_zero hW hW0 hM hrl hp
  have hu : p.1 ∈ Icc (0 : ℝ) T := ⟨hp.1, by linarith [hp.2.1, hp.2.2.1]⟩
  have := e1_isProbabilityMeasure_flowNu hW hp.2.1
  have hψm := TwoPoint.measurable_revMap (continuous_vrev hW p.1) hp.1
  have hα := e1_flowNu_ae_H_norm hW hM hrl hp
  rw [e1_flowMu_eq_map hW hW0 hM hrl hp h]
  have hG := goodM_map_bindFc hψm (ρ := σ) (α := 1 / 3)
    (C := frostC T σ (revBound (2 * Mw) T R₀ + 1))
    (B := revBound (2 * Mw) T (revBound (2 * Mw) T R₀ + 1))
    (by unfold frostC; positivity)
    (hα.mono fun z hz => (goodM_pushed_circle hW hW0 hM hu h le_rfl (by linarith [hz.2])).2)
  exact ⟨hG.admissible (by norm_num), hG.prob.measure_univ⟩

/-- **The admissibility node `FlowAdmStmt` holds.** -/
theorem flowAdmStmt_holds_E1 : FlowAdmStmt := by
  intro W hW hW0 p hp ρ hρ
  obtain ⟨hu, hs, -, hr⟩ := hp
  obtain ⟨Mw, hMw'⟩ := isCompact_Icc.exists_bound_of_continuousOn
    (hW.continuousOn (s := Icc 0 (p.1 + p.2.1)))
  have hMw : ∀ t ∈ Icc (0 : ℝ) (p.1 + p.2.1), |W t| ≤ Mw := fun t ht => by
    simpa [Real.norm_eq_abs] using hMw' t ht
  exact admissible_flowMu hW hW0 hMw hr (rl := p.2.2.2) (R₀ := ‖p.2.2.1‖ + p.2.2.2)
    ⟨hu, hs, le_rfl, le_rfl, le_rfl⟩ hρ.1 hρ.2

/-- **Radius modulus at radii `≥ r₀`, uniform over `FBox`** (`abs_kernelCov2_muUS_rad_le`). -/
theorem abs_kernelCov2_flowMu_rad_le (hW : Continuous W) (hW0 : W 0 = 0) {T Mw rl R₀ : ℝ}
    (hM : ∀ t ∈ Icc (0 : ℝ) T, |W t| ≤ Mw) (hrl : 0 < rl) {p : ℝ × ℝ × ℂ × ℝ}
    (hp : FBox T rl R₀ p) {r₀ ρ ρ' : ℝ} (hr₀ : 0 < r₀) (hρ : r₀ ≤ ρ) (hρ' : r₀ ≤ ρ')
    (hρ1 : ρ ≤ 1) (hρ1' : ρ' ≤ 1) :
    |kernelCov2 neumannH (flowMu W p ρ, flowMu W p ρ') (flowMu W p ρ, flowMu W p ρ')| ≤
      spaceK Mw T r₀ (revBound (2 * Mw) T R₀ + 1) * |ρ - ρ'| ^ (1 / 12 : ℝ) := by
  have hT : 0 ≤ T := hp.1.trans (by linarith [hp.2.1, hp.2.2.1])
  have hMw0 : 0 ≤ Mw := (abs_nonneg _).trans (hM 0 ⟨le_rfl, hT⟩)
  set Ra := revBound (2 * Mw) T R₀ with hRa
  have hu : p.1 ∈ Icc (0 : ℝ) T := ⟨hp.1, by linarith [hp.2.1, hp.2.2.1]⟩
  have := e1_isProbabilityMeasure_flowNu hW hp.2.1
  have hψm := TwoPoint.measurable_revMap (continuous_vrev hW p.1) hp.1
  rw [e1_flowMu_eq_map hW hW0 hM hrl hp (hr₀.trans_le hρ),
    e1_flowMu_eq_map hW hW0 hM hrl hp (hr₀.trans_le hρ')]
  have hα := e1_flowNu_ae_H_norm hW hM hrl hp
  refine abs_kernelCov2_mix_le hψm (α := 1 / 3) (C := frostC T r₀ (Ra + 1))
    (B := revBound (2 * Mw) T (Ra + 1)) (by norm_num) (by unfold frostC; positivity)
    (revBound_nonneg (by linarith) hT) ?_ ?_
  · filter_upwards [hα] with z hz
    exact ⟨(goodM_pushed_circle hW hW0 hM hu hr₀ hρ (by linarith [hz.2])).2,
      (goodM_pushed_circle hW hW0 hM hu hr₀ hρ' (by linarith [hz.2])).2⟩
  · filter_upwards [hα] with z hz
    obtain ⟨e, -⟩ := goodM_pushed_circle hW hW0 hM hu hr₀ hρ (R := Ra + 1) (by linarith [hz.2])
    obtain ⟨e', -⟩ := goodM_pushed_circle hW hW0 hM hu hr₀ hρ' (R := Ra + 1)
      (by linarith [hz.2])
    have h := abs_kernelCov2_νT_space_unif hW hW0 hr₀ hM (β := 1 / 12) (by norm_num) le_rfl hu
      hρ hρ' (w := z) (w' := z) (R := Ra + 1) (by linarith [hz.2]) (by linarith [hz.2])
    rw [e, e', sub_self, norm_zero, zero_add] at h
    exact (le_abs_self _).trans h

end F1
end QuantumZipper
