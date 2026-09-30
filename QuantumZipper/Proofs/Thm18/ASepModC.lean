import QuantumZipper.Proofs.Thm18.ASepModA
import QuantumZipper.Proofs.Zipper.XFlowEnergyE3
import QuantumZipper.Proofs.Zipper.XFlowMechAdm
import QuantumZipper.Proofs.Zipper.XFlowEnergyE1
import QuantumZipper.Proofs.Thm12.CharFun
import QuantumZipper.Proofs.RS.GenerationBasic
import QuantumZipper.Proofs.Loewner.CoreArc1
import QuantumZipper.Proofs.Thm18.G4PushRegScale
import QuantumZipper.Proofs.Zipper.D3PlusN1Model

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# ASEP (mod C): the A-sep family at radius `0`

* `mem_compl_fwdHull_of_lower`: a point of `ℍ` with a forward solution on `[0,T]` staying at
  distance `≥ m` from `0` is not swallowed by any time `τ ≤ T`;
* `muA0_zero`: `muA0 p 0 = fc(a d, a r)` (`f_τ⁻¹ ∘ f_τ = id` off the hull, and the scaling of the
  folded circle, `foldedCircle_map_mul`);
* `energy_muA0_zero_le`: the parameter modulus at radius `0`, from the circle modulus
  `F1.FlowE3Stmt` (XFLOW-E3, `flowE3Stmt_of_E1`) at the zero driver, where `flowMu 0 (0,0,c,s) 0`
  is the folded circle `fc(c, s)`.

Own bookkeeping (the analytic input is XFLOW-E3: Hu–Miller–Peres, Ann. Probab. 38 (2010),
Prop. 2.1; Duplantier–Sheffield, Invent. Math. 185 (2011), Prop. 3.1).
-/

noncomputable section

open MeasureTheory Set Metric
open scoped ENNReal

namespace QuantumZipper
namespace ASep

open RegCont RegUnif

theorem mem_compl_fwdHull_of_lower {W : ℝ → ℝ} (hW : Continuous W) {z : ℂ} (hz : 0 < z.im)
    {T m : ℝ} (hm : 0 < m) (hsol : ∃ u, IsForwardSol W z T u)
    (hlow : ∀ s ∈ Icc (0 : ℝ) T, m ≤ ‖fwdMap W s z‖) {τ : ℝ} (hτ : τ ∈ Icc (0 : ℝ) T) :
    z ∈ H \ fwdHull W τ := by
  rw [FwdHolo.mem_compl_fwdHull_iff hτ.1]
  refine ⟨hz, ?_⟩
  rcases hτ.2.lt_or_eq with hlt | heq
  · exact ⟨T, hlt, hsol⟩
  · subst heq
    rcases hτ.1.lt_or_eq with hpos | hzero
    · obtain ⟨u, hu⟩ := hsol
      exact CoreArc.exists_isForwardSol_beyond hW hz hpos hm
        (fun s hs => ⟨u, isForwardSol_restrict hu hs.1 hs.2.le⟩)
        (fun s hs => hlow s ⟨hs.1, hs.2.le⟩)
    · rw [← hzero]
      obtain ⟨S, hS, u, hu⟩ := exists_isForwardSol_small hW hz
      exact ⟨S, hS, u, hu⟩

/-- **`muA0` at radius `0` is the scaled folded circle.** -/
theorem muA0_zero {W : ℝ → ℝ} (hW : Continuous W) (hW0 : W 0 = 0) {d : ℂ} {r a₀ a₁ T m : ℝ}
    (hr : 0 < r) (ha₀ : 0 < a₀) (hm : 0 < m)
    (hgood0 : ∀ a ∈ Icc a₀ a₁, ∀ w ∈ foldSph d r, ∃ u, IsForwardSol W ((a : ℂ) * w) T u)
    (hlow : ∀ z ∈ scaledSph d r a₀ a₁, ∀ s ∈ Icc (0 : ℝ) T, m ≤ ‖fwdMap W s z‖)
    {p : Fin 2 → ℝ} (hp0 : p 0 ∈ Icc (0 : ℝ) T) (hp1 : p 1 ∈ Icc a₀ a₁) :
    muA0 W d r p 0 = foldedCircle ((p 1 : ℂ) * d) (p 1 * r) := by
  have ha : 0 < p 1 := ha₀.trans_le hp1.1
  have hae := (ae_mem_foldSph d hr.le).and (TwoPoint.foldedCircle_ae_mem_H d hr)
  -- the points `a w` are not swallowed by time `τ`
  have hnot : ∀ w ∈ foldSph d r, w ∈ H → ((p 1 : ℂ) * w) ∈ H \ fwdHull W (p 0) := by
    intro w hw hwH
    have hawH : 0 < ((p 1 : ℂ) * w).im := by
      simp only [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, zero_mul, add_zero]
      exact mul_pos ha hwH
    exact mem_compl_fwdHull_of_lower hW hawH hm (hgood0 _ hp1 w hw)
      (hlow _ (mem_scaledSph hp1 hw)) hp0
  set g := gA W d r (p 0) (p 1) with hg
  have hgm : Measurable g := measurable_gA hW hW0 hm hgood0 hlow hp0 hp1
  set σ := foldedCircle d r with hσ
  have hα : σ.map (fun w => fwdMap W (p 0) ((p 1 : ℂ) * w)) = σ.map g :=
    Measure.map_congr (hae.mono fun x hx => (gA_of_mem hx.1).symm)
  have hαH : ∀ᵐ z ∂σ.map g, z ∈ H := by
    refine (ae_map_iff hgm.aemeasurable isOpen_H.measurableSet).2 (hae.mono fun x hx => ?_)
    rw [hg, gA_of_mem hx.1]
    exact FwdHolo.mapsTo_fwdMap hW hp0.1 (hnot x hx.1 hx.2)
  have hRm := TwoPoint.measurable_revMap (B2.continuous_vrev hW (p 0)) hp0.1
  unfold muA0
  rw [hα, bindFc_zero_of_ae_H hαH]
  rw [Measure.map_congr (μ := σ.map g) (g := revMap (B2.vrev W (p 0)) (p 0))
    (hαH.mono fun z hz => B2.fwdMapInv_eq_revMap_vrev hW hW0 hp0.1 hz)]
  rw [Measure.map_map hRm hgm, ← Thm18Asm.foldedCircle_map_mul ha]
  refine Measure.map_congr (hae.mono fun x hx => ?_)
  simp only [Function.comp_apply]
  rw [hg, gA_of_mem hx.1, ← B2.fwdMapInv_eq_revMap_vrev hW hW0 hp0.1
    (FwdHolo.mapsTo_fwdMap hW hp0.1 (hnot x hx.1 hx.2))]
  exact RS.fwdMapInv_fwdMap hW hW0 hp0.1 (hnot x hx.1 hx.2)

/-- At the zero driver and zero times, `flowMu` is the folded circle. -/
theorem flowMu_zero_circle (c : ℂ) {s : ℝ} (hs : 0 < s) :
    F1.flowMu (fun _ => 0) (0, 0, c, s) 0 = foldedCircle c s := by
  have hW : Continuous fun _ : ℝ => (0 : ℝ) := continuous_const
  have hV : Continuous (B2.vrev (fun _ : ℝ => (0 : ℝ)) (0 + 0)) := B2.continuous_vrev hW _
  have hV0 : B2.vrev (fun _ : ℝ => (0 : ℝ)) (0 + 0) 0 = 0 := B2.vrev_zero (by norm_num)
  have hH := TwoPoint.foldedCircle_ae_mem_H c hs
  have h1 : (foldedCircle c s).map (revMap (B2.vrev (fun _ : ℝ => (0 : ℝ)) (0 + 0)) 0) =
      foldedCircle c s := by
    exact (Measure.map_congr (g := id)
      (hH.mono fun z hz => (CharFun.revMap_zero_eq hV hV0 hz : _ = id z))).trans Measure.map_id
  unfold F1.flowMu F1.flowNu
  simp only
  rw [h1, bindFc_zero_of_ae_H hH]
  refine (Measure.map_congr (g := id) (hH.mono fun z hz => ?_)).trans Measure.map_id
  show fwdMapInv (fun _ => 0) 0 z = z
  rw [B2.fwdMapInv_eq_revMap_vrev hW rfl le_rfl hz]
  exact CharFun.revMap_zero_eq (B2.continuous_vrev hW _) (B2.vrev_zero le_rfl) hz

/-- **Parameter modulus of `muA0` at radius `0`** (XFLOW-E3 at the zero driver). -/
theorem energy_muA0_zero_le {W : ℝ → ℝ} (hW : Continuous W) (hW0 : W 0 = 0) {d : ℂ}
    (hd : 0 ≤ d.im) {r a₀ a₁ T m : ℝ} (hr : 0 < r) (ha₀ : 0 < a₀) (hm : 0 < m)
    (hgood0 : ∀ a ∈ Icc a₀ a₁, ∀ w ∈ foldSph d r, ∃ u, IsForwardSol W ((a : ℂ) * w) T u)
    (hlow : ∀ z ∈ scaledSph d r a₀ a₁, ∀ s ∈ Icc (0 : ℝ) T, m ≤ ‖fwdMap W s z‖) :
    ∃ C b : ℝ, 0 ≤ C ∧ 0 < b ∧ ∀ p p' : Fin 2 → ℝ, p 0 ∈ Icc (0 : ℝ) T → p 1 ∈ Icc a₀ a₁ →
      p' 0 ∈ Icc (0 : ℝ) T → p' 1 ∈ Icc a₀ a₁ →
      |kernelCov2 neumannH (muA0 W d r p 0, muA0 W d r p' 0) (muA0 W d r p 0, muA0 W d r p' 0)| ≤
        C * (|p 1 - p' 1| * (‖d‖ + r)) ^ b := by
  obtain ⟨N, hN⟩ := exists_nat_gt (a₁ * ‖d‖ + a₁ * r + 1 / (a₀ * r))
  have hHD : HolderDrv (fun _ : ℝ => (0 : ℝ)) (2 * (N : ℝ) + 2) 1 0 :=
    ⟨continuous_const, rfl, one_pos, le_rfl, le_rfl, fun t _ t' _ _ => by simp⟩
  obtain ⟨C, b, hC, hb, h⟩ :=
    F1.flowE3Stmt_of_E1 F1.flowAdmStmt_holds F1.flowE1Stmt_holds N _ 1 0 hHD
  refine ⟨C, b, hC, hb, fun p p' hp0 hp1 hp0' hp1' => ?_⟩
  have hdn : 0 ≤ ‖d‖ := norm_nonneg _
  have har : 0 < a₀ * r := mul_pos ha₀ hr
  have hinv : 0 < 1 / (a₀ * r) := by positivity
  have hmem : ∀ a ∈ Icc a₀ a₁, ((0 : ℝ), (0 : ℝ), (a : ℂ) * d, a * r) ∈ F1.flowBox N := by
    intro a ha
    have ha0 : 0 < a := ha₀.trans_le ha.1
    have ha1 : 0 ≤ a₁ := ha0.le.trans ha.2
    have hq1 : 0 ≤ a₁ * ‖d‖ := mul_nonneg ha1 hdn
    have hq2 : 0 ≤ a₁ * r := mul_nonneg ha1 hr.le
    have h1 : a * ‖d‖ ≤ a₁ * ‖d‖ := mul_le_mul_of_nonneg_right ha.2 hdn
    have h2 : a * r ≤ a₁ * r := mul_le_mul_of_nonneg_right ha.2 hr.le
    have h3 : a₀ * r ≤ a * r := mul_le_mul_of_nonneg_right ha.1 hr.le
    have hre : |a * d.re| ≤ a * ‖d‖ := by
      rw [abs_mul, abs_of_pos ha0]
      exact mul_le_mul_of_nonneg_left (Complex.abs_re_le_norm d) ha0.le
    have him : a * d.im ≤ a * ‖d‖ :=
      mul_le_mul_of_nonneg_left (Complex.im_le_norm d) ha0.le
    have hN2 : 1 / (a₀ * r) < (N : ℝ) + 2 := by linarith [mul_nonneg ha0.le hdn]
    have hinvle : 1 / ((N : ℝ) + 2) ≤ a₀ * r := by
      rw [div_le_iff₀ (by positivity)]
      rw [div_lt_iff₀ har] at hN2
      linarith
    refine ⟨⟨le_rfl, by positivity⟩, ⟨le_rfl, by positivity⟩, ?_, ?_, ?_⟩
    · simp only [Complex.re_ofReal_mul]
      constructor <;> linarith [abs_le.1 hre]
    · simp only [Complex.im_ofReal_mul]
      exact ⟨mul_nonneg ha0.le hd, by linarith⟩
    · exact ⟨hinvle.trans h3, by linarith⟩
  have hE := h _ (hmem _ hp1) _ (hmem _ hp1') rfl rfl 0 ⟨le_rfl, zero_le_one⟩
  have hr1 : 0 < p 1 * r := mul_pos (ha₀.trans_le hp1.1) hr
  have hr1' : 0 < p' 1 * r := mul_pos (ha₀.trans_le hp1'.1) hr
  rw [flowMu_zero_circle _ hr1, flowMu_zero_circle _ hr1'] at hE
  rw [muA0_zero hW hW0 hr ha₀ hm hgood0 hlow hp0 hp1,
    muA0_zero hW hW0 hr ha₀ hm hgood0 hlow hp0' hp1']
  refine hE.trans (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow dist_nonneg ?_ hb.le) hC)
  have e1 : dist ((p 1 : ℂ) * d) ((p' 1 : ℂ) * d) = |p 1 - p' 1| * ‖d‖ := by
    rw [dist_eq_norm, ← sub_mul, norm_mul, ← Complex.ofReal_sub, Complex.norm_real,
      Real.norm_eq_abs]
  have e2 : dist (p 1 * r) (p' 1 * r) = |p 1 - p' 1| * r := by
    rw [Real.dist_eq, ← sub_mul, abs_mul, abs_of_pos hr]
  have hx : 0 ≤ |p 1 - p' 1| := abs_nonneg _
  simp only [Prod.dist_eq, dist_self, e1, e2]
  refine max_le (by positivity) (max_le (by positivity) (max_le ?_ ?_))
  · nlinarith
  · nlinarith

end ASep
end QuantumZipper
