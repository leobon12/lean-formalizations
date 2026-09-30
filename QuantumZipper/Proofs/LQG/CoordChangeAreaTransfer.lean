import QuantumZipper.Proofs.LQG.CoordChangeAreaPrimed
import QuantumZipper.Proofs.Zipper.AreaCoordCov
import QuantumZipper.Proofs.Thm18.ASep2Loc
import QuantumZipper.Proofs.Thm18.G1Z3AddFun
import QuantumZipper.Proofs.Section5.Prop16LocalAgree
import QuantumZipper.Proofs.Thm18.G1Side3SC
import Mathlib.Topology.TietzeExtension

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# Coordinate change of the area measure (COORD-CHANGE, D98): local transfer, deterministic part

A field sample `x` that agrees, on the dyadic circles inside an open set `W`, with `y + φ`
(`y` a regular sample, `φ` continuous on `W`; `Prop16Area.G.CircAgree`) has, at every pushed
circle `ψ_* fc(d, r)` carried by a compact subset of `W`, the regularized value
`⟨x, ψ_* fc⟩ = ⟨y, ψ_* fc⟩ + ∫ φ d(ψ_* fc)`, provided the dyadic smoothings of `y` converge
there (`CoordChangeArea.evalReg_eq_add_of_circAgree`). Consequently the regularized circle
averages of the coordinate changes `x ∘ ψ + Q log|ψ'|` and `y ∘ ψ + Q log|ψ'|` differ by the
circle average of `φ ∘ ψ` (`CoordChangeArea.avgReg_coordChange_eq_add`).

This is the locality of the field used by Duplantier–Sheffield (Invent. Math. 185 (2011),
Prop. 2.1 and §6: the measure of `h + φ` is `e^{γφ} dμ_h`); the formal argument is own
bookkeeping around `Thm18Asm.G1Z3.evalReg_add_ofFun_of_ae_z3` and `SWCore.a7_avgReg_eq`.
-/

noncomputable section

open MeasureTheory Filter Set Function Metric
open scoped Topology ENNReal

namespace QuantumZipper
namespace CoordChangeArea

open SWCore GoodSample

/-- Tietze extension of a function continuous on a closed set of `ℂ`. -/
theorem exists_continuous_extension {φ : ℂ → ℝ} {C : Set ℂ} (hC : IsClosed C)
    (hφ : ContinuousOn φ C) : ∃ g : ℂ → ℝ, Continuous g ∧ EqOn g φ C := by
  obtain ⟨G, hG⟩ := ContinuousMap.exists_restrict_eq hC ⟨C.restrict φ, hφ.restrict⟩
  refine ⟨G, G.continuous, fun z hz => ?_⟩
  have := congrArg (fun F : C(C, ℝ) => F ⟨z, hz⟩) hG
  exact this

/-- **Regularized values transfer through local agreement.** -/
theorem evalReg_eq_add_of_circAgree {W : Set ℂ} (hWo : IsOpen W) {x y : FieldSample}
    {F : ℂ × ℝ → ℝ} (hF : IsRegularWith y F) {φ : ℂ → ℝ} (hφ : ContinuousOn φ W)
    (h : Prop16Area.G.CircAgree W x (y + ofFun φ)) {Kψ : Set ℂ} (hK : IsCompact Kψ)
    (hKW : Kψ ⊆ W) (hKH : Kψ ⊆ Hbar) {ν : Measure ℂ} [IsProbabilityMeasure ν]
    (hν : ∀ᵐ w ∂ν, w ∈ Kψ) {L : ℝ}
    (hL : Tendsto (fun j => ∫ w, avgReg y j w ∂ν) atTop (𝓝 L)) :
    evalReg x ν = evalReg y ν + ∫ w, φ w ∂ν := by
  obtain ⟨δ, hδ, hδW⟩ := hK.exists_cthickening_subset_open hWo hKW
  have hδ2 : (0 : ℝ) < δ / 2 := by linarith
  have hC : IsClosed (cthickening (δ / 2) Kψ) := isClosed_cthickening
  have hCW : cthickening (δ / 2) Kψ ⊆ W :=
    (cthickening_mono (by linarith) Kψ).trans hδW
  obtain ⟨g, hgc, hgφ⟩ := exists_continuous_extension hC (hφ.mono hCW)
  -- `x` and `y + φ` have the same regularized value at `ν`
  have e1 : evalReg x ν = evalReg (y + ofFun φ) ν := by
    refine ASep.evalReg_congr_of_eventually ?_
    have hr : ∀ᶠ j in atTop, 2 * radius j ≤ δ :=
      (RegClosure.tendsto_radius_nhdsGT.mono_right nhdsWithin_le_nhds).eventually
        (ge_mem_nhds (by linarith : (0 : ℝ) < δ / 2)) |>.mono fun j hj => by linarith
    filter_upwards [hr] with j hj
    refine integral_congr_ae (hν.mono fun v hv => ?_)
    refine Prop16Area.G.avgReg_eq_of_circAgree h (hKH hv) fun u hu => hδW ?_
    exact mem_cthickening_of_dist_le u v δ Kψ hv ((mem_closedBall.1 hu.1).trans hj)
  -- additivity for the continuous profile
  have e2 := Thm18Asm.G1Z3.evalReg_add_ofFun_of_ae_z3 hF hgc.continuousOn hK hKH hδ2 hgφ hν hL
  have e3 : ∫ w, g w ∂ν = ∫ w, φ w ∂ν :=
    integral_congr_ae (hν.mono fun w hw => hgφ (self_subset_cthickening Kψ hw))
  rw [e1, e2, e3]

/-- A pushed circle is carried by the image of the closed disc. -/
theorem ae_map_fc_mem {ψ : ℂ → ℂ} (hψm : Measurable ψ) {d : ℂ} (hd : d ∈ Hbar) {r : ℝ}
    (hr : 0 ≤ r) {S : Set ℂ} (hS : MeasurableSet S) (h : MapsTo ψ (closedBall d r) S) :
    ∀ᵐ w ∂((foldedCircle d r).map ψ), w ∈ S :=
  (ae_map_iff hψm.aemeasurable hS).2
    ((G1Side.ae_fc_mem_closedBall hd hr).mono fun u hu => h hu)

/-- **The pushed value of `x` is that of `y` plus the circle average of `g = φ ∘ ψ`.** -/
theorem evalReg_push_eq {W : Set ℂ} (hWo : IsOpen W) {x y : FieldSample}
    {F : ℂ × ℝ → ℝ} (hF : IsRegularWith y F) {φ : ℂ → ℝ} (hφ : ContinuousOn φ W)
    (h : Prop16Area.G.CircAgree W x (y + ofFun φ)) {ψ : ℂ → ℂ} (hψm : Measurable ψ)
    {K₂ : Set ℂ} (hK₂ : IsCompact K₂) (hψc : ContinuousOn ψ K₂) (hK₂W : MapsTo ψ K₂ W)
    (hK₂H : MapsTo ψ K₂ Hbar) {g : ℂ → ℝ} (hg : EqOn g (fun u => φ (ψ u)) K₂)
    {d : ℂ} (hd : d ∈ Hbar) {r : ℝ} (hr : 0 < r) (hdK : closedBall d r ⊆ K₂) {L : ℝ}
    (hL : Tendsto (fun j => ∫ w, avgReg y j w ∂((foldedCircle d r).map ψ)) atTop (𝓝 L)) :
    evalReg x ((foldedCircle d r).map ψ) =
      evalReg y ((foldedCircle d r).map ψ) + smoothFun g d r := by
  set Kψ := ψ '' K₂ with hKψdef
  have hKψ : IsCompact Kψ := hK₂.image_of_continuousOn hψc
  have hKψW : Kψ ⊆ W := image_subset_iff.2 hK₂W
  have hKψH : Kψ ⊆ Hbar := image_subset_iff.2 hK₂H
  haveI : IsProbabilityMeasure ((foldedCircle d r).map ψ) :=
    (Measure.isProbabilityMeasure_map_iff hψm.aemeasurable).2 inferInstance
  have hν : ∀ᵐ w ∂((foldedCircle d r).map ψ), w ∈ Kψ :=
    ae_map_fc_mem hψm hd hr.le hKψ.isClosed.measurableSet fun u hu => mem_image_of_mem ψ (hdK hu)
  rw [evalReg_eq_add_of_circAgree hWo hF hφ h hKψ hKψW hKψH hν hL]
  congr 1
  obtain ⟨φ₁, hφ₁c, hφ₁⟩ := exists_continuous_extension hKψ.isClosed (hφ.mono hKψW)
  calc ∫ w, φ w ∂((foldedCircle d r).map ψ) = ∫ w, φ₁ w ∂((foldedCircle d r).map ψ) :=
        integral_congr_ae (hν.mono fun w hw => (hφ₁ hw).symm)
    _ = ∫ u, φ₁ (ψ u) ∂foldedCircle d r :=
        integral_map hψm.aemeasurable hφ₁c.aestronglyMeasurable
    _ = smoothFun g d r := by
        unfold smoothFun
        refine integral_congr_ae ((G1Side.ae_fc_mem_closedBall hd hr.le).mono fun u hu => ?_)
        rw [hg (hdK hu)]
        exact hφ₁ (mem_image_of_mem ψ (hdK hu))

/-- `2r ≤ Im z` when the closed disc of radius `2r` about `z` lies in `ℍ`. -/
theorem two_mul_le_im_of_closedBall_subset {z : ℂ} {r : ℝ} (hr : 0 ≤ r)
    (h : closedBall z (2 * r) ⊆ H) : 2 * r ≤ z.im := by
  have hmem : z - ((2 * r : ℝ) : ℂ) * Complex.I ∈ closedBall z (2 * r) := by
    rw [mem_closedBall, dist_eq_norm]
    have e : z - ((2 * r : ℝ) : ℂ) * Complex.I - z = -(((2 * r : ℝ) : ℂ) * Complex.I) := by ring
    rw [e, norm_neg, norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (by linarith)]
  have h1 : (0 : ℝ) < (z - ((2 * r : ℝ) : ℂ) * Complex.I).im := h hmem
  simp at h1
  linarith

/-- **The circle averages of the two coordinate changes differ by the average of `φ ∘ ψ`.** -/
theorem avgReg_coordChange_eq_add {W : Set ℂ} (hWo : IsOpen W) {x y : FieldSample}
    {F : ℂ × ℝ → ℝ} (hF : IsRegularWith y F) {φ : ℂ → ℝ} (hφ : ContinuousOn φ W)
    (h : Prop16Area.G.CircAgree W x (y + ofFun φ)) {ψ : ℂ → ℂ} (hψm : Measurable ψ)
    (hψd : DifferentiableOn ℂ ψ H) (hψ0 : ∀ u ∈ H, deriv ψ u ≠ 0)
    {K₂ : Set ℂ} (hK₂ : IsCompact K₂) (hK₂H' : K₂ ⊆ H) (hK₂W : MapsTo ψ K₂ W)
    (hK₂H : MapsTo ψ K₂ Hbar) {g : ℂ → ℝ} (hgc : Continuous g)
    (hg : EqOn g (fun u => φ (ψ u)) K₂) (Q : ℝ) {k : ℕ}
    (hT : ∀ d ∈ K₂, Tendsto (fun j => ∫ u, avgReg y j u ∂((foldedCircle d (radius k)).map ψ))
      atTop (𝓝 (evalReg y ((foldedCircle d (radius k)).map ψ))))
    (hC : ContinuousOn (fun d => evalReg y ((foldedCircle d (radius k)).map ψ)) K₂)
    {z : ℂ} (hB : closedBall z (2 * radius k) ⊆ K₂) :
    avgReg (coordChange x ψ Q) k z =
      avgReg (coordChange y ψ Q) k z + smoothFun g z (radius k) := by
  have hr := radius_pos k
  have hψc : ContinuousOn ψ K₂ := hψd.continuousOn.mono hK₂H'
  have hzK : z ∈ K₂ := hB (mem_closedBall_self (by positivity))
  have hzH : z ∈ H := hK₂H' hzK
  have him := two_mul_le_im_of_closedBall_subset hr.le (hB.trans hK₂H')
  have hdyK : ∀ᶠ n in atTop, closedBall (dyadicRoundC n z) (radius k) ⊆ K₂ :=
    (a7_dyadic_small hr).mono fun n hn => hn.1.trans hB
  have hdyMem : ∀ᶠ n in atTop, dyadicRoundC n z ∈ K₂ :=
    hdyK.mono fun n hn => hn (mem_closedBall_self hr.le)
  have hdz : Tendsto (fun n => dyadicRoundC n z) atTop (𝓝[K₂] z) :=
    tendsto_nhdsWithin_iff.2 ⟨RegClosure.tendsto_dyadicRoundC z, hdyMem⟩
  have h1y : Tendsto (fun n => evalReg y ((foldedCircle (dyadicRoundC n z) (radius k)).map ψ))
      atTop (𝓝 (evalReg y ((foldedCircle z (radius k)).map ψ))) :=
    ((hC z hzK).tendsto).comp hdz
  have hsm : Tendsto (fun n => smoothFun g (dyadicRoundC n z) (radius k)) atTop
      (𝓝 (smoothFun g z (radius k))) :=
    ((continuous_smoothFun hgc.continuousOn _).tendsto z).comp (RegClosure.tendsto_dyadicRoundC z)
  have hP : ∀ d ∈ Hbar, closedBall d (radius k) ⊆ K₂ →
      evalReg x ((foldedCircle d (radius k)).map ψ) =
        evalReg y ((foldedCircle d (radius k)).map ψ) + smoothFun g d (radius k) :=
    fun d hd hdK => evalReg_push_eq hWo hF hφ h hψm hK₂ hψc hK₂W hK₂H hg hd hr hdK
      (hT d (hdK (mem_closedBall_self hr.le)))
  have hzB : closedBall z (radius k) ⊆ K₂ :=
    (closedBall_subset_closedBall (by linarith)).trans hB
  have h1x : Tendsto (fun n => evalReg x ((foldedCircle (dyadicRoundC n z) (radius k)).map ψ))
      atTop (𝓝 (evalReg x ((foldedCircle z (radius k)).map ψ))) := by
    rw [hP z (H_subset_Hbar hzH) hzB]
    refine (h1y.add hsm).congr' ?_
    filter_upwards [hdyK] with n hn
    exact (hP _ (CircleCont.dyadicRoundC_mem_Hbar (H_subset_Hbar hzH) n) hn).symm
  rw [a7_avgReg_eq isOpen_H hψd hψ0 (hB.trans hK₂H') him h1x,
    a7_avgReg_eq isOpen_H hψd hψ0 (hB.trans hK₂H') him h1y, hP z (H_subset_Hbar hzH) hzB]
  ring

end CoordChangeArea
end QuantumZipper
