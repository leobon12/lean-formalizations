import QuantumZipper.Proofs.Zipper.WedgeCocycleCore
import QuantumZipper.Proofs.Zipper.WedgeUnzipXC

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# WEDGE-FLOW-WD (part 1): deterministic transport of the flow nodes along `z = x + G`

Sheffield, *Conformal weldings of random surfaces*, arXiv:1012.4797, §5.1 rule (5.1) and §5.4;
Duplantier–Sheffield, *Liouville quantum gravity and KPZ*, Invent. Math. 185 (2011), Prop. 3.1.

For a field `z` agreeing on every folded circle with `x + g` (`g = G` continuous; the wedge
decomposition W-D, `WedgeUnzip.WDec.wedgeDecompStmt_holds`), the unzipped field `z_u` agrees on
every folded circle with `x_u + g ∘ E_u` (`WedgeUnzip.unzipAddFun`). Unzipping once more by `s`
along the shifted driver and comparing with unzipping by `u + s` (flow property of the Loewner
maps, `RegCont.fwdMapInv_add`) shows:

* `rc3_of_flow_raw_cocycle`: RC3 at the pushed circle is *equivalent* to the raw cocycle (converse
  of `flow_raw_cocycle_of_rc3`);
* `flow_rc3_transfer`: RC3 of `z_u` at `R_* fc(d, r)` follows from RC3 of `x_u` there, given the
  continuum inputs of `unzipAddFun` for `x` (times `u`, `u + s`) and for `x_u` (time `s` along the
  shifted driver);
* `flow_cont_transfer`: the flow continuum limit of `z_u` follows from that of `x_u`.

Own elementary bookkeeping (affinity of `coordChange`, dominated convergence), as in
`WedgeUnzipXC.lean`.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal ENNReal

namespace QuantumZipper
namespace F1

open B2 TwoPoint

/-- The continuum input of `unzipAddFun` for the field `x` along the driver `W` at time `t`. -/
def ContAlong (x : FieldSample) (W : ℝ → ℝ) (t : ℝ) : Prop :=
  ∀ d ∈ Hbar, ∀ r : ℝ, 0 < r →
    (∀ ρ : ℝ, 0 < ρ → Integrable (fun v => evalReg x (foldedCircle v ρ))
      ((foldedCircle d r).map (fwdMapInv W t))) ∧
    ∃ L : ℝ, Tendsto (fun ρ => ∫ v, evalReg x (foldedCircle v ρ)
      ∂((foldedCircle d r).map (fwdMapInv W t))) (𝓝[>] 0) (𝓝 L)

/-- The driver after unzipping by `u`. -/
abbrev shiftDrv (W : ℝ → ℝ) (u : ℝ) : ℝ → ℝ := fun r => W (u + max r 0) - W u

theorem shiftDrv_continuous {W : ℝ → ℝ} (hW : Continuous W) (u : ℝ) :
    Continuous (shiftDrv W u) := by
  unfold shiftDrv; fun_prop

theorem shiftDrv_zero (W : ℝ → ℝ) (u : ℝ) : shiftDrv W u 0 = 0 := by simp [shiftDrv]

/-- **RC3 at the pushed circle from the raw cocycle** (converse of `flow_raw_cocycle_of_rc3`). -/
theorem rc3_of_flow_raw_cocycle (γ : ℝ) (x : FieldSample) {W : ℝ → ℝ} (hW : Continuous W)
    (hW0 : W 0 = 0) {u s : ℝ} (hu : 0 ≤ u) (hs : 0 ≤ s) (w : ℂ) {r : ℝ} (hr : 0 < r)
    (h : unzippedField γ (zipCapDown γ u (x, W)) s (foldedCircle w r) =
      unzippedField γ (x, W) (u + s) (foldedCircle w r)) :
    evalReg (unzippedField γ (x, W) u)
        ((foldedCircle w r).map (revMap (B2.vrev W (u + s)) s)) =
      unzippedField γ (x, W) u ((foldedCircle w r).map (revMap (B2.vrev W (u + s)) s)) := by
  have h1 := RegUnif.double_apply_fc γ x hW hu hs w hr
  have h2 := RegUnif.single_apply_fc γ x hW hW0 hu hs w hr
  have h' : (zipCapDown γ s (zipCapDown γ u (x, W))).1 (foldedCircle w r) =
      (zipCapDown γ (u + s) (x, W)).1 (foldedCircle w r) := h
  rw [h1, h2] at h'
  linarith

/-- **Flow of the inverse forward maps**: on `ℍ`, `f_u⁻¹ ∘ (f^{(u)}_s)⁻¹ = f_{u+s}⁻¹`, and
`(f^{(u)}_s)⁻¹` maps `ℍ` into `ℍ` (`RegCont.fwdMapInv_add`). -/
theorem fwdMapInv_shiftDrv_comp {W : ℝ → ℝ} (hW : Continuous W) (hW0 : W 0 = 0) {u s : ℝ}
    (hu : 0 ≤ u) (hs : 0 ≤ s) {z : ℂ} (hz : z ∈ H) :
    fwdMapInv (shiftDrv W u) s z ∈ H ∧
      fwdMapInv W u (fwdMapInv (shiftDrv W u) s z) = fwdMapInv W (u + s) z := by
  have hE := RegUnif.eqOn_fwdMapInv_shift hW hu hs hz
  refine ⟨?_, ?_⟩
  · rw [show fwdMapInv (shiftDrv W u) s z = revMap (vrev W (u + s)) s z from hE]
    exact im_revMap_pos (continuous_vrev hW _) hz hs
  · rw [show fwdMapInv (shiftDrv W u) s z = revMap (vrev W (u + s)) s z from hE,
      RegCont.fwdMapInv_add hW hW0 hu hs hz]
    congr 1
    refine ReverseFlow.revMap_congr_drive z fun q hq => ?_
    rw [vrev_of_mem ⟨hq.1, hq.2.trans (le_add_of_nonneg_left hu)⟩]

/-- `G ∘ E_u ∘ foldH`: a globally continuous extension of `G ∘ E_u` from `ℍ̄`. -/
def gExt (G : ℂ → ℝ) (W : ℝ → ℝ) (u : ℝ) : ℂ → ℝ := G ∘ F2.extInv W u ∘ foldH

theorem gExt_continuous {G : ℂ → ℝ} (hG : Continuous G) {W : ℝ → ℝ} {u : ℝ}
    (hC : ContinuousOn (F2.extInv W u) Hbar) : Continuous (gExt G W u) := by
  unfold gExt
  refine hG.comp (hC.comp_continuous CircleFubini.continuous_foldH' fun w => ?_)
  exact CircleFubini.foldH_mem_Hbar' w

theorem gExt_eq {G : ℂ → ℝ} {W : ℝ → ℝ} {u : ℝ} {w : ℂ} (hw : w ∈ Hbar) :
    gExt G W u w = G (F2.extInv W u w) := by
  simp [gExt, CircleFubini.foldH_of_mem' hw]

theorem mem_Hbar_of_H {w : ℂ} (hw : w ∈ H) : w ∈ Hbar :=
  (show 0 ≤ w.im from le_of_lt (show 0 < w.im from hw))

/-- Two functions agreeing on `ℍ̄` have the same folded-circle integrals. -/
theorem ofFun_fc_congr {φ φ' : ℂ → ℝ} (h : ∀ w ∈ Hbar, φ w = φ' w) (d : ℂ) {r : ℝ}
    (hr : 0 < r) : ofFun φ (foldedCircle d r) = ofFun φ' (foldedCircle d r) := by
  unfold ofFun
  exact integral_congr_ae ((foldedCircle_ae_mem_H d hr).mono fun w hw => h w (mem_Hbar_of_H hw))

/-- **`z_u` agrees on folded circles with `x_u + gExt`** (from `z ≈ x + G` and `unzipAddFun`). -/
theorem unz_fc_split (γ : ℝ) {z x : FieldSample} {G : ℂ → ℝ} {W : ℝ → ℝ} (hW : Continuous W)
    (hW0 : W 0 = 0) (hG : Continuous G) (hx : IsRegularSample x)
    (hz : ∀ d ∈ Hbar, ∀ r : ℝ, 0 < r → z (foldedCircle d r) = (x + ofFun G) (foldedCircle d r))
    {u : ℝ} (hu : 0 ≤ u) (hxu : ContAlong x W u) :
    ∀ d ∈ Hbar, ∀ r : ℝ, 0 < r → unzippedField γ (z, W) u (foldedCircle d r) =
      (unzippedField γ (x, W) u + ofFun (gExt G W u)) (foldedCircle d r) := by
  intro d hd r hr
  have e1 : unzippedField γ (z, W) u = unzippedField γ (x + ofFun G, W) u :=
    Factorization.coordChange_congr
      (funext fun k => funext fun w => regEq_of_fc_Hbar hz k w) _ _
  rw [e1, WedgeUnzip.unzipAddFun γ x G W u hu hW hW0 hG hx hxu d hd r hr]
  simp only [Pi.add_apply]
  congr 1
  exact ofFun_fc_congr (fun w hw => (gExt_eq hw).symm) d hr

theorem extInv_of_mem_H (W : ℝ → ℝ) (t : ℝ) {w : ℂ} (hw : w ∈ H) :
    F2.extInv W t w = fwdMapInv W t w := by
  simp [F2.extInv, show 0 < w.im from hw]

/-- **RC3 of `z_u` at the pushed circle from RC3 of `x_u` there** (deterministic transfer along
`z ≈ x + G`). -/
theorem flow_rc3_transfer (γ : ℝ) {z x : FieldSample} {G : ℂ → ℝ} {W : ℝ → ℝ}
    (hW : Continuous W) (hW0 : W 0 = 0) (hG : Continuous G) (hx : IsRegularSample x)
    (hz : ∀ d ∈ Hbar, ∀ r : ℝ, 0 < r → z (foldedCircle d r) = (x + ofFun G) (foldedCircle d r))
    {u s : ℝ} (hu : 0 ≤ u) (hs : 0 ≤ s) (hCu : ContinuousOn (F2.extInv W u) Hbar)
    (hxu : ContAlong x W u) (hxus : ContAlong x W (u + s))
    (hxuR : IsRegularSample (unzippedField γ (x, W) u))
    (hxuC : ContAlong (unzippedField γ (x, W) u) (shiftDrv W u) s)
    {d : ℂ} (hd : d ∈ Hbar) {r : ℝ} (hr : 0 < r)
    (hX : evalReg (unzippedField γ (x, W) u)
        ((foldedCircle d r).map (revMap (B2.vrev W (u + s)) s)) =
      unzippedField γ (x, W) u ((foldedCircle d r).map (revMap (B2.vrev W (u + s)) s))) :
    evalReg (unzippedField γ (z, W) u)
        ((foldedCircle d r).map (revMap (B2.vrev W (u + s)) s)) =
      unzippedField γ (z, W) u ((foldedCircle d r).map (revMap (B2.vrev W (u + s)) s)) := by
  refine rc3_of_flow_raw_cocycle γ z hW hW0 hu hs d hr ?_
  have hsplit := unz_fc_split γ hW hW0 hG hx hz hu hxu
  have e2 : unzippedField γ (zipCapDown γ u (z, W)) s =
      unzippedField γ (unzippedField γ (x, W) u + ofFun (gExt G W u), shiftDrv W u) s :=
    Factorization.coordChange_congr
      (funext fun k => funext fun w => regEq_of_fc_Hbar hsplit k w) _ _
  have e3 : unzippedField γ (z, W) (u + s) = unzippedField γ (x + ofFun G, W) (u + s) :=
    Factorization.coordChange_congr
      (funext fun k => funext fun w => regEq_of_fc_Hbar hz k w) _ _
  rw [e2, e3, WedgeUnzip.unzipAddFun γ _ (gExt G W u) (shiftDrv W u) s hs
      (shiftDrv_continuous hW u) (shiftDrv_zero W u) (gExt_continuous hG hCu) hxuR hxuC d hd r hr,
    WedgeUnzip.unzipAddFun γ x G W (u + s) (add_nonneg hu hs) hW hW0 hG hx hxus d hd r hr]
  have hE := flow_raw_cocycle_of_rc3 γ x hW hW0 hu hs d hr hX
  show unzippedField γ (unzippedField γ (x, W) u, shiftDrv W u) s (foldedCircle d r) +
      ofFun (gExt G W u ∘ F2.extInv (shiftDrv W u) s) (foldedCircle d r) =
    unzippedField γ (x, W) (u + s) (foldedCircle d r) +
      ofFun (G ∘ F2.extInv W (u + s)) (foldedCircle d r)
  congr 1
  unfold ofFun
  refine integral_congr_ae ((foldedCircle_ae_mem_H d hr).mono fun w hw => ?_)
  obtain ⟨hm, hcomp⟩ := fwdMapInv_shiftDrv_comp hW hW0 hu hs hw
  simp only [Function.comp_apply]
  rw [extInv_of_mem_H _ _ hw, extInv_of_mem_H _ _ hw, gExt_eq (mem_Hbar_of_H hm),
    extInv_of_mem_H _ _ hm, hcomp]

/-- **Flow continuum limit of `z_u` from that of `x_u`** (deterministic transfer along
`z ≈ x + G`; the flow form of `WedgeUnzip.wedgeContinuum_of_x`). -/
theorem flow_cont_transfer (γ : ℝ) {z x : FieldSample} {G : ℂ → ℝ} {W : ℝ → ℝ}
    (hW : Continuous W) (hW0 : W 0 = 0) (hG : Continuous G) (hx : IsRegularSample x)
    (hz : ∀ d ∈ Hbar, ∀ r : ℝ, 0 < r → z (foldedCircle d r) = (x + ofFun G) (foldedCircle d r))
    {u : ℝ} (hu : 0 ≤ u) (hCu : ContinuousOn (F2.extInv W u) Hbar) (hxu : ContAlong x W u)
    (hxuR : IsRegularSample (unzippedField γ (x, W) u)) {t : ℝ} (ht : 0 ≤ t) (c : ℂ) {r : ℝ}
    (hr : 0 < r)
    (hxC : (∀ ρ : ℝ, 0 < ρ → Integrable (fun v => evalReg (unzippedField γ (x, W) u)
        (foldedCircle v ρ)) ((foldedCircle c r).map (fwdMapInv (shiftDrv W u) t))) ∧
      ∃ L : ℝ, Tendsto (fun ρ => ∫ v, evalReg (unzippedField γ (x, W) u) (foldedCircle v ρ)
        ∂((foldedCircle c r).map (fwdMapInv (shiftDrv W u) t))) (𝓝[>] 0) (𝓝 L)) :
    (∀ ρ : ℝ, 0 < ρ → Integrable (fun v => evalReg (unzippedField γ (z, W) u)
        (foldedCircle v ρ)) ((foldedCircle c r).map (fwdMapInv (shiftDrv W u) t))) ∧
      ∃ L : ℝ, Tendsto (fun ρ => ∫ v, evalReg (unzippedField γ (z, W) u) (foldedCircle v ρ)
        ∂((foldedCircle c r).map (fwdMapInv (shiftDrv W u) t))) (𝓝[>] 0) (𝓝 L) := by
  have hsplit := unz_fc_split γ hW hW0 hG hx hz hu hxu
  obtain ⟨F, hF⟩ := hxuR
  have hgc := gExt_continuous hG hCu
  have hev : ∀ v ∈ Hbar, ∀ ρ : ℝ, 0 < ρ →
      evalReg (unzippedField γ (z, W) u) (foldedCircle v ρ) =
        evalReg (unzippedField γ (x, W) u) (foldedCircle v ρ) +
          GoodSample.smoothFun (gExt G W u) v ρ := fun v hv ρ hρ => by
    rw [Factorization.evalReg_congr
      (funext fun k => funext fun w => regEq_of_fc_Hbar hsplit k w)]
    exact GoodSample.evalReg_add_ofFun_fc hF hgc.continuousOn hv hρ
  obtain ⟨_C, B, _hC, _hB, hfacts⟩ :=
    RegCont.νT_facts (shiftDrv_continuous hW u) (shiftDrv_zero W u) t c hr
  obtain ⟨hνP, -, hνB⟩ := hfacts t ⟨ht, le_rfl⟩
  have : IsProbabilityMeasure ((foldedCircle c r).map (fwdMapInv (shiftDrv W u) t)) := hνP
  obtain ⟨hint, L, hL⟩ := hxC
  obtain ⟨hsi, hst⟩ := WedgeUnzip.tendsto_integral_smoothFun hgc hνB
  have hcongr : ∀ ρ : ℝ, 0 < ρ →
      (fun v => evalReg (unzippedField γ (z, W) u) (foldedCircle v ρ)) =ᵐ[
        (foldedCircle c r).map (fwdMapInv (shiftDrv W u) t)]
        fun v => evalReg (unzippedField γ (x, W) u) (foldedCircle v ρ) +
          GoodSample.smoothFun (gExt G W u) v ρ := fun ρ hρ =>
    hνB.mono fun v hv => hev v (mem_Hbar_of_H hv.1) ρ hρ
  refine ⟨fun ρ hρ => ((hint ρ hρ).add (hsi ρ hρ)).congr (hcongr ρ hρ).symm, _,
    (hL.add hst).congr' ?_⟩
  filter_upwards [self_mem_nhdsWithin] with ρ (hρ : 0 < ρ)
  exact (integral_add (hint ρ hρ) (hsi ρ hρ)).symm.trans (integral_congr_ae (hcongr ρ hρ)).symm

end F1
end QuantumZipper
