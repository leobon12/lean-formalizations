/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.R5LiftLate
import InteractingSLE.Spec.Sec7.SideC8NativeWord
import InteractingSLE.Spec.ZhanGT4.A2Part3PC

/-!
# Lemma R.5's common phase: the exposed-side positions

Packet PROVE-R5-LIFT (round 3). The word identity of R.5's cover needs the position data of `R7LiftGeom` (d): the
current coordinate `ξ` of a hull landing lies strictly between the current seed images, and the ambient image `x′` of
the landing lies strictly inside the ambient seed images. Both follow from one fact about Loewner charts: a real
coordinate whose inverse boundary value is a point of `ℍ` lies strictly between the centred images of `0⁻` and `0⁺`
(`SideHeight.lt_rightImg_sub_of_extendFrom_mem_H'`, `SideHeight.neg_rightImg_sub_lt_of_extendFrom_mem_H'`).

* **`hasBdryLimits_relChart_driver`**: the local driver of a relative chart has an inverse with boundary limits;
* **`base_landing_mem_H`**: if the current inverse lands at a point `p` of the base chart's domain, the inverse of the
  relative Loewner map lands at `c.fwd p ∈ ℍ`;
* **`mem_seed_interval_of_landing`**: then `ξ` lies strictly between the current geometric seed positions (seeds at
  `0`);
* **`mem_ambient_seed_interval`**: if the current inverse lands at a point of `ℍ` and the ambient chart `f_s` of a
  continuous traced driver converges along it to `x′`, then `x′` lies strictly between the centred ambient images of
  `0⁻` and `0⁺`; with force processes equal to the geometric images of ordered marks (`xL ≤ 0 ≤ xR`) every left force
  point is at or left of `x′` and every right one strictly right of it (**`ambient_force_positions`**).

Ruling R48: nothing here uses Theorem 1.2/1.3, `Theorem12ParamStatement`, `Theorem13Statement` or any result taking
them as hypotheses.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology Metric Complex
open QuantumZipper (H Hbar fwdHull fwdMap fwdMapInv logDerivFwd chiC)
open scoped NNReal ENNReal

namespace InteractingSLE.Sec7.R5Lift

open PocketStop PocketTraversal Lemma71C PocketStopSide MartChar.RealFlow

variable {Ω : Type*} {c : Ω → Chart} {γ : Ω → ℝ → ℂ} {ω : Ω}

/-- **Boundary limits of the local driver's inverse** at a live relative capacity. -/
theorem hasBdryLimits_relChart_driver {q : ℝ≥0} (hγ : IsDrivenCurve (γ ω)) (hq : (q : ℝ≥0∞) < capLife (γ ω))
    {W : ℝ → ℝ} (hW : Continuous W) (hW0 : W 0 = 0) {q' : ℝ} (hqq' : (q : ℝ) < q')
    (hWeq : ∀ r ∈ Icc (0 : ℝ) q', segDriver (γ ω) r.toNNReal = W r) : HasBdryLimits (fwdMapInv W q) := by
  have hq' : ENNReal.ofReal (q : ℝ) < capLife (γ ω) := by rwa [ENNReal.ofReal_coe_nnreal]
  have hfill : fwdHull W q = fillH (γ ω '' Icc 0 (capInv (γ ω) q)) := by
    rw [← fwdHull_eq_of_eqOn q.coe_nonneg hqq' hWeq]
    exact hγ.fwdHull_segDriver q.coe_nonneg hq'
  obtain ⟨F, hF, hFc, -⟩ := exists_inverse_extension_of_filling hW hW0
    (hγ.continuousOn.mono Icc_subset_Ici_self) hfill
  intro x hx
  exact ⟨F x, ((hFc x hx).mono QuantumZipper.H_subset_Hbar).tendsto.congr'
    (eventually_nhdsWithin_of_forall fun y hy => hF hy)⟩

/-- **The base landing of a current coordinate whose landing lies in the base chart's domain** is a point of `ℍ`:
`f_q⁻¹ → c.fwd p`. -/
theorem base_landing_mem_H (hc : (c ω).IsConformal) {W : ℝ → ℝ} (hW : Continuous W) (hW0 : W 0 = 0) {q : ℝ≥0}
    (hrel : relChart c γ q ω = (c ω).loewner W q) (hB : HasBdryLimits (fwdMapInv W q)) {ξ : ℝ} {p : ℂ}
    (hland : Tendsto (relChart c γ q ω).2.1 (𝓝[H] (ξ : ℂ)) (𝓝 p)) (hp : p ∈ (c ω).dom) :
    extendFrom H (fwdMapInv W q) ξ = (c ω).1 p ∧ (c ω).1 p ∈ H := by
  have hcont : ContinuousAt (c ω).1 p :=
    (hc.differentiableOn_fwd.continuousOn).continuousAt ((c ω).dom.isOpen.mem_nhds hp)
  have h1 : Tendsto (fun y => (c ω).1 ((relChart c γ q ω).2.1 y)) (𝓝[H] (ξ : ℂ)) (𝓝 ((c ω).1 p)) :=
    hcont.tendsto.comp hland
  have h2 : Tendsto (fwdMapInv W q) (𝓝[H] (ξ : ℂ)) (𝓝 ((c ω).1 p)) := by
    refine h1.congr' (eventually_nhdsWithin_of_forall fun y hy => ?_)
    rw [hrel]
    exact hc.2.2 _ (QuantumZipper.RS.fwdMapInv_mem_H hW hW0 q.coe_nonneg hy)
  have hξ : (ξ : ℂ) ∈ Hbar := show (0 : ℝ) ≤ (ξ : ℂ).im by rw [ofReal_im]
  have := nhdsWithin_H_neBot ξ
  exact ⟨tendsto_nhds_unique (hB.tendsto hξ) h2, hc.fwd_mem hp⟩

/-- **A current coordinate landing in the base chart's domain lies strictly between the current seeds** (left and
right seeds at `0`, i.e. `0⁻` and `0⁺`). -/
theorem mem_seed_interval_of_landing {nL nR : ℕ} {xL : Ω → Fin nL → ℝ} {xR : Ω → Fin nR → ℝ} {iL : Fin nL}
    {iR : Fin nR} (hxL : xL ω iL = 0) (hxR : xR ω iR = 0) (hc : (c ω).IsConformal) (hγ : IsDrivenCurve (γ ω))
    {q : ℝ≥0} (hq : (q : ℝ≥0∞) < capLife (γ ω)) {ξ : ℝ} {p : ℂ}
    (hland : Tendsto (relChart c γ q ω).2.1 (𝓝[H] (ξ : ℂ)) (𝓝 p)) (hp : p ∈ (c ω).dom) :
    ξ ∈ Ioo (geomLW (fun t ω => segDriver (γ ω) t) xL iL q ω - segDriver (γ ω) q)
      (geomRW (fun t ω => segDriver (γ ω) t) xR iR q ω - segDriver (γ ω) q) := by
  obtain ⟨W, hW, hW0, q', hqq', hWeq, hrel⟩ := exists_relChart_eq_loewner (c := c) hγ hq
  have hB := hasBdryLimits_relChart_driver hγ hq hW hW0 hqq' hWeq
  obtain ⟨hext, hmem⟩ := base_landing_mem_H hc hW hW0 hrel hB hland hp
  rw [← hext] at hmem
  have hR := SideHeight.lt_rightImg_sub_of_extendFrom_mem_H' hB hW hW0 q.coe_nonneg hmem
  have hL := SideHeight.neg_rightImg_sub_lt_of_extendFrom_mem_H' hB hW hW0 q.coe_nonneg hmem
  have hEq : EqOn (fun r : ℝ => (fun t ω => segDriver (γ ω) t) r.toNNReal ω) W (Icc 0 (q : ℝ)) :=
    fun r hr => hWeq r ⟨hr.1, hr.2.trans hqq'.le⟩
  obtain ⟨hLeq, hReq⟩ := geom_positions_eq_of_driver_eqOn (fun t ω => segDriver (γ ω) t) xL xR hW hEq
  have hL' := congrFun hLeq iL
  have hR' := congrFun hReq iR
  simp only [hxL, hxR, neg_zero] at hL' hR'
  exact ⟨by rw [hL']; exact hL, by rw [hR']; exact hR⟩

/-- **The ambient image of a landing in `ℍ` lies strictly between the centred ambient seed images**: if the current
inverse lands at `z₀ ∈ ℍ`, stays off the ambient hull at `s`, and `f_s` converges along it to `x′`, then
`−rightImg(−W)(0) s − W s < x′ < rightImg W 0 s − W s`. -/
theorem mem_ambient_seed_interval {cur : Chart} {W : ℝ → ℝ} {η : ℝ → ℂ} (hη : IsLoewnerTrace W η)
    (hW : Continuous W) (hW0 : W 0 = 0) {s : ℝ} (hs : 0 ≤ s) {ξ : ℝ} {z₀ : ℂ} (hz₀ : z₀ ∈ H)
    (hland : Tendsto cur.2.1 (𝓝[H] (ξ : ℂ)) (𝓝 z₀)) (hK : ∀ᶠ y in 𝓝[H] (ξ : ℂ), cur.2.1 y ∈ H \ fwdHull W s)
    {x' : ℝ} (hx' : Tendsto (fun y => fwdMap W s (cur.2.1 y)) (𝓝[H] (ξ : ℂ)) (𝓝 (x' : ℂ))) :
    -rightImg (fun t => -W t) 0 s - W s < x' ∧ x' < rightImg W 0 s - W s := by
  have hB := hη.hasBdryLimits hW hW0 hs
  have hx'H : Tendsto (fun y => fwdMap W s (cur.2.1 y)) (𝓝[H] (ξ : ℂ)) (𝓝[H] (x' : ℂ)) :=
    tendsto_nhdsWithin_iff.2 ⟨hx', hK.mono fun y hy => QuantumZipper.FwdHolo.mapsTo_fwdMap hW hs hy⟩
  have hx'bar : (x' : ℂ) ∈ Hbar := show (0 : ℝ) ≤ (x' : ℂ).im by rw [ofReal_im]
  have h1 := (hB.tendsto hx'bar).comp hx'H
  have h2 : Tendsto (fun y => fwdMapInv W s (fwdMap W s (cur.2.1 y))) (𝓝[H] (ξ : ℂ)) (𝓝 z₀) :=
    hland.congr' (hK.mono fun y hy => (QuantumZipper.RS.fwdMapInv_fwdMap hW hW0 hs hy).symm)
  have := nhdsWithin_H_neBot ξ
  have hext : extendFrom H (fwdMapInv W s) x' = z₀ := tendsto_nhds_unique h1 h2
  have hmem : extendFrom H (fwdMapInv W s) x' ∈ H := hext ▸ hz₀
  exact ⟨SideHeight.neg_rightImg_sub_lt_of_extendFrom_mem_H' hB hW hW0 hs hmem,
    SideHeight.lt_rightImg_sub_of_extendFrom_mem_H' hB hW hW0 hs hmem⟩

/-- **The ambient force positions around the ambient image** (force processes equal to the geometric images of ordered
marks): every left force point is at or left of `x′`, every right one strictly right of it. -/
theorem ambient_force_positions {mL mR : ℕ} {W : ℝ → ℝ} (hW : Continuous W) {s : ℝ} (hs : 0 ≤ s)
    {xL : Fin mL → ℝ} {xR : Fin mR → ℝ} (hxL : ∀ i, xL i ≤ 0) (hxR : ∀ j, 0 ≤ xR j) {VL : Fin mL → ℝ}
    {VR : Fin mR → ℝ} (hVL : ∀ i, VL i = -rightImg (fun t => -W t) (-xL i) s)
    (hVR : ∀ j, VR j = rightImg W (xR j) s) {x' : ℝ}
    (hx' : -rightImg (fun t => -W t) 0 s - W s < x' ∧ x' < rightImg W 0 s - W s) :
    (∀ i, VL i - W s ≤ x') ∧ ∀ j, x' < VR j - W s := by
  refine ⟨fun i => ?_, fun j => ?_⟩
  · have hm : rightImg (fun t => -W t) 0 s ≤ rightImg (fun t => -W t) (-xL i) s :=
      rightImg_mono_index hW.neg hs (show (0 : ℝ) ≤ -xL i by linarith [hxL i])
    rw [hVL i]
    linarith [hx'.1]
  · have hm : rightImg W 0 s ≤ rightImg W (xR j) s := rightImg_mono_index hW hs (hxR j)
    rw [hVR j]
    linarith [hx'.2]

end InteractingSLE.Sec7.R5Lift
