import QuantumZipper.Proofs.Zipper.ZipLenMain
import QuantumZipper.Proofs.Zipper.XFlowClose
import QuantumZipper.Proofs.Zipper.XFlowRC3Raw
import QuantumZipper.Proofs.Zipper.XFlowUCSplit

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# ZIPLEN-2: the `Γ⁰` flow RC3 node `YFlowRC3Stmt` from the free-field flow chain

Sheffield, *Conformal weldings of random surfaces*, arXiv:1012.4797, §5.1 rule (5.1);
Duplantier–Sheffield, *Liouville quantum gravity and KPZ*, Invent. Math. 185 (2011), Prop. 3.1.
Own bookkeeping on top of the proved free-field flow nodes (`F1.xFlowUCStmt_holds`,
`F1.xFlowRC3Stmt_holds`, `F1.xFlowLogUCStmt_holds`).

With `y = 𝔥₀ + X` (the `Γ⁰` field) and `x = X + α₀(−log|·|)`, at a parameter
`p = (u, s, d, r)` of the flow node and `q = (0, u + s, d, r)`, `Λ(p) = ∫ log|f_u⁻¹| dν_p`:

* regularized sides (`evalReg_unzY_flowNu`): by the split `Φ_j = Φ^y_j − √κ L_j`
  (`F1.flowPhi_eq_split`) and the convergence of `Φ_j` (X-flow UC) and `L_j` (log UC),
  `evalReg y_u ν_p = evalReg x_u ν_p + √κ Λ(p)`, at `p` and at `q`;
* raw sides (`unzip_flowNu_eq`, as `F1.flowRawSide_eq` for an arbitrary field):
  `y_u(ν_p) = evalReg y ν_q + Q D(p)`, `x_u(ν_p) = evalReg x ν_q + Q D(p)`, and `evalReg y ν_q`,
  `evalReg x ν_q` are the regularized sides at `q` (both fields are exact at the enumerated
  circles, Duplantier–Sheffield Prop. 3.1 via `CoordReg.ae_evalReg_logAdd_eq_frostman`);
* `Λ(p) = Λ(q)` (`logInt_flowNu_eq`: `f_u⁻¹ ∘ R_{u,s} = f_{u+s}⁻¹` on `ℍ`).

Combined with X-flow RC3 at `p` this gives RC3 of `y_u` at `ν_p`: `yFlowRC3Stmt_holds`.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal ENNReal

namespace QuantumZipper
namespace B3d
namespace ZipLen

open F1

/-! ## Deterministic lemmas -/

/-- **Raw side for an arbitrary field** (the computation of `F1.flowRawSide_eq`). -/
theorem unzip_flowNu_eq (γ : ℝ) (y : FieldSample) {W : ℝ → ℝ} (hW : Continuous W)
    (hW0 : W 0 = 0) {p : ℝ × ℝ × ℂ × ℝ} (hp : p ∈ flowPar) :
    unzippedField γ (y, W) p.1 (flowNu W p) =
      evalReg y (flowNu W (0, p.1 + p.2.1, p.2.2.1, p.2.2.2)) +
        Qc γ * ∫ z, Real.log ‖deriv (fwdMapInv W p.1) z‖ ∂flowNu W p := by
  obtain ⟨u, s, d, r⟩ := p
  obtain ⟨hu, hs, -, hr⟩ := hp
  simp only at hu hs hr ⊢
  have hV : Continuous (B2.vrev W (u + s)) := B2.continuous_vrev hW _
  have hRm : Measurable (revMap (B2.vrev W (u + s)) s) := TwoPoint.measurable_revMap hV hs
  set V' : ℝ → ℝ := fun q => W (u - q) - W u with hV'
  have hV'c : Continuous V' := by rw [hV']; fun_prop
  have hEu : EqOn (fwdMapInv W u) (revMap V' u) H := CoordReg.eqOn_fwdMapInv hW hW0 hu
  have hνH : ∀ᵐ z ∂flowNu W (u, s, d, r), z ∈ H :=
    (ae_map_iff hRm.aemeasurable isOpen_H.measurableSet).2
      ((TwoPoint.foldedCircle_ae_mem_H d hr).mono fun z hz => TwoPoint.im_revMap_pos hV hz hs)
  have hmap : (flowNu W (u, s, d, r)).map (revMap V' u) =
      (foldedCircle d r).map (revMap (B2.vrev W (0 + (u + s))) (u + s)) := by
    unfold flowNu
    simp only
    rw [Measure.map_map (TwoPoint.measurable_revMap hV'c hu) hRm]
    refine Measure.map_congr ((TwoPoint.foldedCircle_ae_mem_H d hr).mono fun z hz => ?_)
    have hRz : revMap (B2.vrev W (u + s)) s z ∈ H := TwoPoint.im_revMap_pos hV hz hs
    simp only [Function.comp_apply]
    rw [← hEu hRz, fwdMapInv_revMap_comp hW hW0 hu hs hz]
  have h1 : unzippedField γ (y, W) u (flowNu W (u, s, d, r)) =
      coordChange y (fwdMapInv W u) (Qc γ) (flowNu W (u, s, d, r)) := rfl
  have h2 : coordChange y (revMap V' u) (Qc γ) (flowNu W (u, s, d, r)) =
      evalReg y ((flowNu W (u, s, d, r)).map (revMap V' u)) +
        Qc γ * ∫ z, Real.log ‖deriv (revMap V' u) z‖ ∂flowNu W (u, s, d, r) := rfl
  have hder : ∫ z, Real.log ‖deriv (revMap V' u) z‖ ∂flowNu W (u, s, d, r) =
      ∫ z, Real.log ‖deriv (fwdMapInv W u) z‖ ∂flowNu W (u, s, d, r) := by
    refine integral_congr_ae (hνH.mono fun z hz => ?_)
    have := Filter.EventuallyEq.deriv_eq
      (Filter.eventuallyEq_of_mem (isOpen_H.mem_nhds hz) hEu)
    simp only [this]
  rw [h1, CoordReg.coordChange_congr_of_eqOn_H y hEu _ hνH, h2, hmap, hder]
  rfl

/-- A field exact at the enumerated circles has the same regularized values as its unzipping at
time `0`. -/
theorem evalReg_unzip_zero (γ : ℝ) {y : FieldSample} {W : ℝ → ℝ} (hW : Continuous W)
    (hW0 : W 0 = 0)
    (hfix : ∀ i : ℕ, evalReg y (foldedCircle (CoordsFull.fullIndex i).1
        (CoordsFull.fullIndex i).2) =
      y (foldedCircle (CoordsFull.fullIndex i).1 (CoordsFull.fullIndex i).2))
    (ν : Measure ℂ) : evalReg (unzippedField γ (y, W) 0) ν = evalReg y ν := by
  have havg : ∀ k z, avgReg (unzippedField γ (y, W) 0) k z = avgReg y k z := by
    intro k z
    unfold avgReg
    congr 1
    funext n
    exact (RegUnif.raw_unzip_zero_eq γ hW hW0 hfix n k z).symm
  exact WedgeUnzip.evalReg_congr_avgReg havg _

/-- `log|f_t⁻¹|` is continuous on `ℍ`. -/
theorem continuousOn_log_fwdMapInv {W : ℝ → ℝ} (hW : Continuous W) (hW0 : W 0 = 0) {t : ℝ}
    (ht : 0 ≤ t) : ContinuousOn (fun w => Real.log ‖fwdMapInv W t w‖) H := by
  refine ((WedgeUnzip.fwdMapInv_props hW hW0 ht).1.continuousOn.norm).log fun w hw => ?_
  have h : 0 < (fwdMapInv W t w).im := RS.fwdMapInv_mem_H hW hW0 ht hw
  exact (norm_pos_iff.2 fun h0 => by rw [h0, Complex.zero_im] at h; exact lt_irrefl _ h).ne'

/-- **`Λ(p) = Λ(0, u + s, d, r)`.** -/
theorem logInt_flowNu_eq {W : ℝ → ℝ} (hW : Continuous W) (hW0 : W 0 = 0)
    {p : ℝ × ℝ × ℂ × ℝ} (hp : p ∈ flowPar) :
    ∫ w, Real.log ‖fwdMapInv W p.1 w‖ ∂flowNu W p =
      ∫ w, Real.log ‖fwdMapInv W 0 w‖ ∂flowNu W (0, p.1 + p.2.1, p.2.2.1, p.2.2.2) := by
  obtain ⟨u, s, d, r⟩ := p
  obtain ⟨hu, hs, -, hr⟩ := hp
  simp only at hu hs hr ⊢
  have hae := TwoPoint.foldedCircle_ae_mem_H d hr
  have key : ∀ {t σ : ℝ}, 0 ≤ t → 0 ≤ σ →
      ∫ w, Real.log ‖fwdMapInv W t w‖ ∂(foldedCircle d r).map (revMap (B2.vrev W (t + σ)) σ) =
        ∫ z, Real.log ‖fwdMapInv W t (revMap (B2.vrev W (t + σ)) σ z)‖ ∂foldedCircle d r := by
    intro t σ ht hσ
    have hV : Continuous (B2.vrev W (t + σ)) := B2.continuous_vrev hW _
    have hRm : Measurable (revMap (B2.vrev W (t + σ)) σ) := TwoPoint.measurable_revMap hV hσ
    have hνH : ∀ᵐ z ∂(foldedCircle d r).map (revMap (B2.vrev W (t + σ)) σ), z ∈ H :=
      (ae_map_iff hRm.aemeasurable isOpen_H.measurableSet).2
        (hae.mono fun z hz => TwoPoint.im_revMap_pos hV hz hσ)
    have hsm : AEStronglyMeasurable (fun w => Real.log ‖fwdMapInv W t w‖)
        ((foldedCircle d r).map (revMap (B2.vrev W (t + σ)) σ)) := by
      have := (continuousOn_log_fwdMapInv hW hW0 ht).aestronglyMeasurable
        isOpen_H.measurableSet (μ := (foldedCircle d r).map (revMap (B2.vrev W (t + σ)) σ))
      rwa [Measure.restrict_eq_self_of_ae_mem hνH] at this
    exact integral_map hRm.aemeasurable hsm
  show ∫ w, Real.log ‖fwdMapInv W u w‖ ∂(foldedCircle d r).map (revMap (B2.vrev W (u + s)) s) =
    ∫ w, Real.log ‖fwdMapInv W 0 w‖ ∂(foldedCircle d r).map
      (revMap (B2.vrev W (0 + (u + s))) (u + s))
  rw [key hu hs, key le_rfl (add_nonneg hu hs)]
  refine integral_congr_ae (hae.mono fun z hz => ?_)
  have hV' : Continuous (B2.vrev W (0 + (u + s))) := B2.continuous_vrev hW _
  have hRz : 0 < (revMap (B2.vrev W (0 + (u + s))) (u + s) z).im :=
    TwoPoint.im_revMap_pos hV' hz (add_nonneg hu hs)
  simp only
  rw [fwdMapInv_revMap_comp hW hW0 hu hs hz, Thm18Asm.G1Pkg.fwdMapInv_zero_time hW hRz, hW0,
    Complex.ofReal_zero,
    add_zero]

/-- **Regularized side of the `Γ⁰` field at a pushed circle** from the split. -/
theorem evalReg_unzY_flowNu (κ : ℝ) {x : FieldSample} {W : ℝ → ℝ} (hW : Continuous W)
    (hW0 : W 0 = 0) {p : ℝ × ℝ × ℂ × ℝ} (hp : p ∈ flowPar)
    (hR : ∀ k : ℕ, ∀ d ∈ RegUnif.Dy, E1.RegShift (ofFun (h0rev κ) + x)
      ((foldedCircle d (radius k)).map (fwdMapInv W p.1)))
    {F : ℂ × ℝ → ℝ}
    (hF : IsRegularWith (unzippedField (Real.sqrt κ) (ofFun (h0rev κ) + x, W) p.1) F)
    {Lx Λ : ℝ} (hΦ : Tendsto (fun j => flowPhi κ x W j p) atTop (𝓝 Lx))
    (hL : Tendsto (fun j => flowLogJ W j p) atTop (𝓝 Λ)) :
    evalReg (unzippedField (Real.sqrt κ) (ofFun (h0rev κ) + x, W) p.1) (flowNu W p) =
      Lx + Real.sqrt κ * Λ := by
  obtain ⟨u, s, d, r⟩ := p
  obtain ⟨hu, hs, -, hr⟩ := hp
  have hsplit : ∀ j : ℕ, flowPhiY κ x W j (u, s, d, r) =
      flowPhi κ x W j (u, s, d, r) + Real.sqrt κ * flowLogJ W j (u, s, d, r) := fun j => by
    rw [flowPhi_eq_split κ hW hW0 d hu hs hr hR hF j]
    ring
  have ht : Tendsto (fun j => flowPhiY κ x W j (u, s, d, r)) atTop
      (𝓝 (Lx + Real.sqrt κ * Λ)) := by
    simp_rw [hsplit]
    exact hΦ.add (hL.const_mul _)
  exact ht.limUnder_eq

/-! ## The node -/

/-- **`YFlowRC3Stmt` holds.** -/
theorem yFlowRC3Stmt_holds : YFlowRC3Stmt := by
  intro κ hκ hκ4 Ω _ P _ B X hB hX hind
  have hfx : ∀ᵐ ω ∂P, ∀ i : ℕ, evalReg (X ω + F2.logSingField κ)
      (foldedCircle (CoordsFull.fullIndex i).1 (CoordsFull.fullIndex i).2) =
      (X ω + F2.logSingField κ) (foldedCircle (CoordsFull.fullIndex i).1
        (CoordsFull.fullIndex i).2) := by
    refine ae_all_iff.2 fun i => ?_
    have hr := UnzipFull.fullIndex_radius_pos i
    have h := CoordReg.ae_evalReg_logAdd_eq_frostman hX
      (ν := foldedCircle (CoordsFull.fullIndex i).1 (CoordsFull.fullIndex i).2)
      (CircleFubini.foldedCircle_support hr.le le_rfl)
      (Cor15Group.isFrostman_fc _ hr) one_pos (-(Real.sqrt κ - 2 / Real.sqrt κ))
      (g₁ := fun _ => (0 : ℝ)) continuousOn_const
    refine h.mono fun ω hω => ?_
    rw [logSing_eq_logAdd]
    exact hω
  have hfy : ∀ᵐ ω ∂P, ∀ i : ℕ, evalReg (ofFun (h0rev κ) + X ω)
      (foldedCircle (CoordsFull.fullIndex i).1 (CoordsFull.fullIndex i).2) =
      (ofFun (h0rev κ) + X ω) (foldedCircle (CoordsFull.fullIndex i).1
        (CoordsFull.fullIndex i).2) := by
    refine ae_all_iff.2 fun i => ?_
    have hr := UnzipFull.fullIndex_radius_pos i
    have h := CoordReg.ae_evalReg_logAdd_eq_frostman hX
      (ν := foldedCircle (CoordsFull.fullIndex i).1 (CoordsFull.fullIndex i).2)
      (CircleFubini.foldedCircle_support hr.le le_rfl)
      (Cor15Group.isFrostman_fc _ hr) one_pos (2 / Real.sqrt κ)
      (g₁ := fun _ => (0 : ℝ)) continuousOn_const
    refine h.mono fun ω hω => ?_
    rw [CoordReg.h0rev_eq_logAdd]
    exact hω
  filter_upwards [RegUnif.ae_drive_good hB κ,
    RegUnif.ae_forall_isRegularSample (κ := κ) (γ := Real.sqrt κ) hB hX hind,
    ae_all_iff.2 fun n : ℕ => RegUnif.gaugeRegDyStmt_holds (κ := κ) (T := (n : ℝ) + 1)
      hB hX hind (by positivity),
    xFlowUCStmt_holds κ hκ hκ4 P B X hB hX hind, xFlowRC3Stmt_holds κ hκ hκ4 P B X hB hX hind,
    hfx, hfy] with ω hdr hreg hgau hUC hXR hfxω hfyω
  intro u s hu hs d hd r hr
  obtain ⟨hW, hW0⟩ := hdr
  set W := drive κ B ω with hWdef
  obtain ⟨Lx, hLx⟩ := hUC
  set p : ℝ × ℝ × ℂ × ℝ := (u, s, d, r) with hpdef
  set q : ℝ × ℝ × ℂ × ℝ := (0, u + s, d, r) with hqdef
  have hp : p ∈ flowPar := ⟨hu, hs, hd, hr⟩
  have hq : q ∈ flowPar := ⟨le_rfl, add_nonneg hu hs, hd, hr⟩
  -- the regularized identity at a parameter
  have hRY : ∀ p' ∈ flowPar,
      evalReg (unzippedField (Real.sqrt κ) (ofFun (h0rev κ) + X ω, W) p'.1) (flowNu W p') =
        evalReg (F2.unzX κ (X ω) W p'.1) (flowNu W p') +
          Real.sqrt κ * ∫ w, Real.log ‖fwdMapInv W p'.1 w‖ ∂flowNu W p' := by
    intro p' hp'
    obtain ⟨F, hF⟩ := (hreg p'.1 hp'.1).1
    have hR := (hgau ⌈p'.1⌉₊ p'.1 ⟨hp'.1, by linarith [Nat.le_ceil p'.1]⟩).1
    have hΦ := hLx.tendsto_at hp'
    obtain ⟨m, hm⟩ := flowBox_mem_nhdsWithin hp'
    have hL := (xFlowLogUCStmt_holds W hW hW0 m).tendsto_at (mem_of_mem_nhdsWithin hp' hm)
    rw [evalReg_unzY_flowNu κ hW hW0 hp' hR hF hΦ hL]
    congr 1
    exact hΦ.limUnder_eq.symm
  -- raw sides
  have hYraw := unzip_flowNu_eq (Real.sqrt κ) (ofFun (h0rev κ) + X ω) hW hW0 hp
  have hXraw := unzip_flowNu_eq (Real.sqrt κ) (X ω + F2.logSingField κ) hW hW0 hp
  have hY0 := evalReg_unzip_zero (Real.sqrt κ) hW hW0 hfyω (flowNu W q)
  have hX0 := evalReg_unzip_zero (Real.sqrt κ) hW hW0 hfxω (flowNu W q)
  have hΛ := logInt_flowNu_eq hW hW0 hp
  have hRYp := hRY p hp
  have hRYq := hRY q hq
  have hXRp := hXR u s hu hs d hd r hr
  rw [← unzippedField_cfg_eq]
  change evalReg (unzippedField (Real.sqrt κ) (ofFun (h0rev κ) + X ω, W) p.1) (flowNu W p) =
    unzippedField (Real.sqrt κ) (ofFun (h0rev κ) + X ω, W) p.1 (flowNu W p)
  change evalReg (unzippedField (Real.sqrt κ) (X ω + F2.logSingField κ, W) p.1) (flowNu W p) =
    unzippedField (Real.sqrt κ) (X ω + F2.logSingField κ, W) p.1 (flowNu W p) at hXRp
  change evalReg (unzippedField (Real.sqrt κ) (ofFun (h0rev κ) + X ω, W) 0) (flowNu W q) =
    evalReg (unzippedField (Real.sqrt κ) (X ω + F2.logSingField κ, W) 0) (flowNu W q) +
      Real.sqrt κ * ∫ w, Real.log ‖fwdMapInv W 0 w‖ ∂flowNu W q at hRYq
  change evalReg (unzippedField (Real.sqrt κ) (ofFun (h0rev κ) + X ω, W) p.1) (flowNu W p) =
    evalReg (unzippedField (Real.sqrt κ) (X ω + F2.logSingField κ, W) p.1) (flowNu W p) +
      Real.sqrt κ * ∫ w, Real.log ‖fwdMapInv W p.1 w‖ ∂flowNu W p at hRYp
  rw [hRYp, hXRp, hXraw, hYraw, ← hX0, ← hY0, hRYq, hΛ]
  ring

end ZipLen
end B3d
end QuantumZipper
