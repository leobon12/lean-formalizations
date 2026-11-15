/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.Lemma71PTrace
import InteractingSLE.Spec.Sec7.LocalExtGChart

/-!
# Lemma 7.1's (CS), geometric half: the time-`t` chart of the active component and its landing points

Packet PROVE-LEMMA71P (specification Remark 6.7, `source/spec/p145-192.md` L566–L590; Lemma 7.1,
`source/spec/p193-240.md` L576–L606). Pathwise, on the pocket frame of PROVE-LEMMA71N/O with the mapped segment `γ'`
of the middle curve `γ` and its visit clock `κ` (`IsPocketSeg`):

* `IsPocketSeg.land_seg`: the pocket chart lands at `γ'(u)` on the middle-curve point `γ(κ u)`;
* `IsPocketSeg.mem_image_of_le`: a point `γ(s)` of the closed pocket with `s ≤ κ U` is mapped into `γ'([0, U])`;
* `tChart`: the chart `(f_t ∘ ψ, ψ⁻¹ ∘ f_t⁻¹, arg f_t′ ∘ ψ + lift + 2πn)` of the active component at capacity time
  `t` (`Chart.loewner` of the shifted chart for a continuous driver agreeing with the canonical one on `[0, t]`), with
  `tChart_facts`: it is conformal, its domain is `Lemma71M.pocketDom`, its inverse is `Lemma71M.pocketInv` and its lift
  is `Lemma71M.pocketLift`; `exists_isDerivLog_tChart`: its lift is the imaginary part of a logarithm of its
  derivative;
* `tendsto_tChart_inv`: at every point `x ∈ ℍ̄` the inverse lands at `land c (F̄_t x)`;
* **`exists_land_mid`** (CS-a): at every middle chart point `x ≠ 0` (strictly between the images of `0⁻` and `0⁺`)
  the inverse lands at `γ(κ u)` for a segment time `u < capInv γ' t`, i.e. strictly before the capacity stop.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Filter Topology Metric Complex
open scoped NNReal ENNReal Real

namespace InteractingSLE.Sec7.Lemma71P

open QuantumZipper (H Hbar fwdMap fwdMapInv fwdHull logDerivFwd)
open QuantumZipper.CA (cayley cayleyInv)
open Lemma71K (IsMarkedPocket wallPt segPt)
open Lemma71N (IsPocketFrame IsPocketBranch)
open Lemma71O (land)
open Lemma71C (IsSegCurve capLife capInv segDriver)
open MartChar.RealFlow

/-- **The pathwise data of the middle curve in the pocket**: the pocket frame, the middle curve `γ` simple proper and
left of the right wall `α`, a logarithm `L` of the chart derivative with `lift = Im L`, the mapped segment `γ'` (a
segment curve, the boundary values `Ψ` at the segment points, the range identity), and the visit clock `κ` (strictly
increasing from `κ 0 ≥ 0`, with `cayley (γ (κ u)) = segPt u`). All of it holds almost surely on a pocket construction
over a three-curve space (`Lemma71L.PocketGood.visit`). -/
structure IsPocketSeg (β α γ : ℝ≥0 → ℂ) (C : Set ℂ) (c : Chart) (Ψ : ℂ → ℂ) (a b : ℝ) (γ' : ℝ → ℂ)
    (κ : ℝ → ℝ) : Prop where
  frame : IsPocketFrame β α C c Ψ a b
  hγ : Lemma71I.IsSimpleProper γ
  hγα : Disjoint (range γ) (rightSideOf (range α))
  log : ∃ L : ℂ → ℂ, IsDerivLog c.1 L C ∧ ∀ z ∈ C, c.2.2 z = (L z).im
  seg : IsSegCurve γ'
  hseg : ∀ u, 0 ≤ u → segPt γ (closure (cayley '' C)) u ∈ closure (cayley '' C) \ {wallPt α b} ∧
    γ' u = Ψ (segPt γ (closure (cayley '' C)) u)
  hrange : γ' '' Ici 0 = Ψ '' (cayley '' range γ ∩ (closure (cayley '' C) \ {wallPt α b}))
  hκ : StrictMonoOn κ (Ici 0)
  hκ0 : 0 ≤ κ 0
  hcay : ∀ u, 0 ≤ u → cayley (γ (κ u).toNNReal) = segPt γ (closure (cayley '' C)) u

namespace IsPocketSeg

variable {β α γ : ℝ≥0 → ℂ} {C : Set ℂ} {c : Chart} {Ψ : ℂ → ℂ} {a b : ℝ} {γ' : ℝ → ℂ} {κ : ℝ → ℝ}

theorem mem_Hbar (hP : IsPocketSeg β α γ C c Ψ a b γ' κ) (s : ℝ≥0) : γ s ∈ Hbar := by
  rcases eq_zero_or_pos s with rfl | hs
  · rw [hP.hγ.2.2.1]; exact mem_Hbar_of_im_eq_zero (by simp)
  · exact H_subset_Hbar (hP.hγ.2.2.2.1 s hs)

theorem κ_nonneg (hP : IsPocketSeg β α γ C c Ψ a b γ' κ) {u : ℝ} (hu : 0 ≤ u) : 0 ≤ κ u :=
  hP.hκ0.trans (hP.hκ.monotoneOn self_mem_Ici hu hu)

/-- **The pocket chart lands at the mapped segment point `γ'(u)` on the middle-curve point `γ(κ u)`.** -/
theorem land_seg (hP : IsPocketSeg β α γ C c Ψ a b γ' κ) {u : ℝ} (hu : 0 ≤ u) :
    land c (γ' u) = γ (κ u).toNNReal := by
  obtain ⟨hK, he⟩ := hP.hseg u hu
  rw [he, Lemma71O.PocketFrame.land_eq hP.frame (hP.frame.hΨH hK) hK rfl, ← hP.hcay u hu,
    WangWu.cayleyInv_cayley_of_mem_Hbar (hP.mem_Hbar _)]

/-- **A point of the stopped middle prefix in the closed pocket is on the mapped prefix**: if `γ(s)` lies in the
closed pocket (minus the closing point) and `s ≤ κ U`, then `Ψ(cayley γ(s)) ∈ γ'([0, U])` (the visit clock is
strictly increasing; `Lemma71N.mem_image_of_mem_prefix` at a clock value). -/
theorem mem_image_of_le (hP : IsPocketSeg β α γ C c Ψ a b γ' κ) {s : ℝ≥0}
    (hsK : cayley (γ s) ∈ closure (cayley '' C) \ {wallPt α b}) {U : ℝ} (hU : 0 ≤ U) (hsU : (s : ℝ) ≤ κ U) :
    Ψ (cayley (γ s)) ∈ γ' '' Icc 0 U := by
  have hmem : Ψ (cayley (γ s)) ∈ γ' '' Ici 0 := by
    rw [hP.hrange]; exact ⟨cayley (γ s), ⟨⟨γ s, ⟨s, rfl⟩, rfl⟩, hsK⟩, rfl⟩
  obtain ⟨v, hv0, hvz⟩ := hmem
  obtain ⟨hsegK, hsegΨ⟩ := hP.hseg v hv0
  have hsegz : segPt γ (closure (cayley '' C)) v = cayley (γ s) :=
    hP.frame.hΨi hsegK hsK (by rw [← hsegΨ, hvz])
  have hγeq : γ (κ v).toNNReal = γ s := by
    have h1 := hP.hcay v hv0
    rw [hsegz] at h1
    exact WangWu.cayley_injOn_Hbar (hP.mem_Hbar _) (hP.mem_Hbar _) h1
  have hκvs : (κ v).toNNReal = s := hP.hγ.2.1 hγeq
  have hκv : κ v = s := by rw [← hκvs, Real.coe_toNNReal _ (hP.κ_nonneg hv0)]
  refine ⟨v, ⟨hv0, (hP.hκ.le_iff_le hv0 hU).1 (by rw [hκv]; exact hsU)⟩, hvz⟩

end IsPocketSeg

/-! ### The time-`t` chart -/

/-- **The chart of the active component at capacity time `t`**: `Chart.loewner` of the shifted pocket chart for the
driver `W`, i.e. `(f_t ∘ ψ, ψ⁻¹ ∘ f_t⁻¹, arg f_t′ ∘ ψ + lift + 2πn)`. -/
def tChart (c : Chart) (n : ℤ) (W : ℝ → ℝ) (t : ℝ) : Chart := (Lemma71E.shiftLift c n).loewner W t

section TChart

variable {β α γ : ℝ≥0 → ℂ} {C : Set ℂ} {c : Chart} {Ψ : ℂ → ℂ} {a b : ℝ} {γ' : ℝ → ℂ} {κ : ℝ → ℝ}
  {W : ℝ → ℝ} {t : ℝ≥0}

/-- **The time-`t` chart is the chart of the active component** (`Lemma71M.pocketDom`, `pocketInv`, `pocketLift`). -/
theorem tChart_facts (hc : c.IsConformal) {γ' : ℝ → ℂ} (hΓ : IsSegCurve γ') (ht : (t : ℝ≥0∞) < capLife γ')
    (hW : Continuous W) (hW0 : W 0 = 0) (hWe : EqOn W (Ito.rpath fun s => segDriver γ' s) (Icc 0 t)) (n : ℤ) :
    (tChart c n W t).IsConformal ∧
      ((tChart c n W t).dom : Set ℂ) = Lemma71M.pocketDom c (fun s => segDriver γ' s) t ∧
      (∀ y ∈ H, Lemma71M.pocketInv (Lemma71E.shiftLift c n) (fun s => segDriver γ' s) t y =
        (tChart c n W t).2.1 y) ∧
      ∀ z, Lemma71M.pocketLift (Lemma71E.shiftLift c n) (fun s => segDriver γ' s) t z = (tChart c n W t).2.2 z := by
  set w : ℝ≥0 → ℝ := fun s => segDriver γ' s with hwdef
  have hw : ContinuousOn w {s | (s : ℝ≥0∞) < capLife γ'} := hΓ.segDriver_spec.2.1
  have hw0 : w 0 = 0 := hΓ.segDriver_spec.1
  have ht0 : (0 : ℝ) ≤ t := t.coe_nonneg
  have hc' : (tChart c n W t).IsConformal := (Lemma71E.isConformal_shiftLift hc n).loewner hW hW0 ht0
  obtain ⟨t₂, htt₂, ht₂ζ⟩ := ENNReal.lt_iff_exists_nnreal_btwn.1 ht
  have htt₂' : (t : ℝ) < t₂ := by exact_mod_cast htt₂
  have hK : fwdHull W t = fwdHull (Ito.rpath w) t :=
    LocalExt.fwdHull_congr_of_continuousOn (hW.continuousOn) (Ito.continuousOn_rpath hw ht₂ζ) ht0 htt₂' hWe
  have h1c : (tChart c n W t).1 = Lemma71M.pocketFwd (Lemma71E.shiftLift c n) w t :=
    funext fun z => Ito.fwdMap_congr_of_eqOn hWe
  have hdomc : ((tChart c n W t).dom : Set ℂ) = Lemma71M.pocketDom (Lemma71E.shiftLift c n) w t := by
    rw [hc'.coe_dom]
    show (fun z => c.2.1 (fwdMapInv W t z)) '' H = c.2.1 '' (H \ fwdHull (Ito.rpath w) t)
    rw [← image_image c.2.1 (fwdMapInv W t), QuantumZipper.RS.image_fwdMapInv_H hW hW0 ht0, hK]
  refine ⟨hc', hdomc, fun y hy => ?_, fun z => ?_⟩
  · exact Lemma71M.pocketInv_eq (Lemma71E.isConformal_shiftLift hc n) hw hw0 ht hc' h1c hdomc hy
  · show (logDerivFwd (Ito.rpath w) t (c.1 z)).im + (c.2.2 z + 2 * π * n) =
      (logDerivFwd W t (c.1 z)).im + (c.2.2 z + 2 * π * n)
    rw [Ito.logDerivFwd_congr_of_eqOn hWe ht0 le_rfl]

/-- **The lift of the time-`t` chart is the imaginary part of a logarithm of its derivative**:
`L_t = log f_t′ ∘ ψ + L + 2πin` on the active component. -/
theorem exists_isDerivLog_tChart (hc : c.IsConformal) {C : Set ℂ} (hdom : (c.dom : Set ℂ) = C) {L : ℂ → ℂ}
    (hL : IsDerivLog c.1 L C) (hlift : ∀ z ∈ C, c.2.2 z = (L z).im) (hW : Continuous W) (hW0 : W 0 = 0) (n : ℤ) :
    ∃ Lt : ℂ → ℂ, IsDerivLog (tChart c n W t).1 Lt (tChart c n W t).dom ∧
      ∀ z ∈ (tChart c n W t).dom, (tChart c n W t).2.2 z = (Lt z).im := by
  have ht0 : (0 : ℝ) ≤ t := t.coe_nonneg
  have hc' : (tChart c n W t).IsConformal := (Lemma71E.isConformal_shiftLift hc n).loewner hW hW0 ht0
  set D : Set ℂ := ((tChart c n W t).dom : Set ℂ) with hD
  have hDo : IsOpen D := (tChart c n W t).dom.isOpen
  have hDsub : ∀ z ∈ D, z ∈ C ∧ c.1 z ∈ H \ fwdHull W t := by
    intro z hz
    rw [hD, hc'.coe_dom] at hz
    obtain ⟨y, hy, rfl⟩ := hz
    have hF := QuantumZipper.RS.fwdMapInv_mem_compl_fwdHull hW hW0 ht0 hy
    refine ⟨?_, ?_⟩
    · rw [← hdom]; exact hc.inv_mem_dom hF.1
    · show c.1 (c.2.1 (fwdMapInv W t y)) ∈ H \ fwdHull W t
      rw [hc.2.2 _ hF.1]; exact hF
  have hCo : IsOpen C := hdom ▸ c.dom.isOpen
  have hc1 : DifferentiableOn ℂ c.1 C := hdom ▸ hc.differentiableOn_fwd
  have hcomp := IsDerivLog.comp hDo (QuantumZipper.FwdHolo.isOpen_compl_fwdHull hW ht0)
    (QuantumZipper.FwdHolo.differentiableOn_fwdMap hW ht0) (hc1.mono fun z hz => (hDsub z hz).1)
    (fun z hz => (hDsub z hz).2) (isDerivLog_fwdMap hW ht0) (hL.mono fun z hz => (hDsub z hz).1)
  refine ⟨fun z => logDerivFwd W t (c.1 z) + L z + 2 * π * n * Complex.I, ⟨hcomp.1.add_const _, fun z hz => ?_⟩,
    fun z hz => ?_⟩
  · rw [Complex.exp_add, hcomp.2 z hz]
    have : Complex.exp (2 * π * n * Complex.I) = 1 := by
      rw [← Complex.exp_int_mul_two_pi_mul_I n]; ring_nf
    rw [this, mul_one]
    rfl
  · show (logDerivFwd W t (c.1 z)).im + (c.2.2 z + 2 * π * n) = _
    rw [hlift z (hDsub z hz).1]
    simp only [Complex.add_im, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im,
      Complex.intCast_re, Complex.intCast_im, mul_zero, mul_one, zero_mul, sub_zero, add_zero, Complex.re_ofNat,
      Complex.im_ofNat, Complex.mul_re]
    ring

/-- **The inverse of the time-`t` chart lands at `land c (F̄_t x)`** at every `x ∈ ℍ̄`. -/
theorem tendsto_tChart_inv (hF : IsPocketFrame β α C c Ψ a b) {η : ℝ → ℂ} (hη : IsLoewnerTrace W η)
    (hW : Continuous W) (hW0 : W 0 = 0) (n : ℤ) {x : ℂ} (hx : x ∈ Hbar) :
    Tendsto (tChart c n W t).2.1 (𝓝[H] x) (𝓝 (land c (extendFrom H (fwdMapInv W t) x))) := by
  have ht0 : (0 : ℝ) ≤ t := t.coe_nonneg
  have hFx := extendFrom_mem_Hbar hη hW hW0 ht0 hx
  have h1 : Tendsto (fwdMapInv W t) (𝓝[H] x) (𝓝[Hbar] (extendFrom H (fwdMapInv W t) x)) :=
    tendsto_nhdsWithin_iff.2 ⟨(hη.hasBdryLimits hW hW0 ht0).tendsto hx,
      eventually_nhdsWithin_of_forall fun y hy => H_subset_Hbar (QuantumZipper.RS.fwdMapInv_mem_H hW hW0 ht0 hy)⟩
  have h2 := ((Lemma71O.PocketFrame.continuousOn_land hF) _ hFx).tendsto.comp h1
  refine h2.congr' (eventually_nhdsWithin_of_forall fun y hy => ?_)
  show land c (fwdMapInv W t y) = c.2.1 (fwdMapInv W t y)
  exact extendFrom_extends hF.hc.1.continuousOn _ (QuantumZipper.RS.fwdMapInv_mem_H hW hW0 ht0 hy)

end TChart

/-! ### The landing points at the middle chart points -/

section Mid

variable {β α γ : ℝ≥0 → ℂ} {C : Set ℂ} {c : Chart} {Ψ : ℂ → ℂ} {a b : ℝ} {γ' : ℝ → ℂ} {κ : ℝ → ℝ}
  {W : ℝ → ℝ} {t : ℝ≥0}

/-- **CS-a, in the time-`t` boundary map**: at a middle chart point `x ≠ 0`, `F̄_t(x) = γ'(u)` for a segment time
`0 ≤ u < capInv γ' t` (`mem_image_of_mid`, and `x ≠ 0` is not the tip: `eq_zero_of_extendFrom_eq_tip`). -/
theorem exists_seg_mid (hΓ : IsSegCurve γ') (ht : (t : ℝ≥0∞) < capLife γ') {η : ℝ → ℂ} (hη : IsLoewnerTrace W η)
    (hW : Continuous W) (hW0 : W 0 = 0) (hηe : ∀ s : ℝ, 0 ≤ s → s ≤ t → η s = γ' (capInv γ' s)) {x : ℝ}
    (hxL : -rightImg (fun s => -W s) 0 t - W t < x) (hxR : x < rightImg W 0 t - W t) (hx0 : x ≠ 0) :
    ∃ u : ℝ, 0 ≤ u ∧ u < capInv γ' t ∧ extendFrom H (fwdMapInv W t) x = γ' u ∧
      ∃ v : ℝ, 0 ≤ v ∧ v < t ∧ u = capInv γ' v := by
  have ht0 : (0 : ℝ) ≤ t := t.coe_nonneg
  obtain ⟨v, hv, hve⟩ := mem_image_of_mid hη hW hW0 ht0 hxL hxR
  have hvt : v < t := by
    refine lt_of_le_of_ne hv.2 fun h => hx0 ?_
    refine eq_zero_of_extendFrom_eq_tip hη hW hW0 ht0 ?_ (by rw [← hve, h])
    intro s hs s' hs' he
    rw [hηe s hs.1 hs.2, hηe s' hs'.1 hs'.2] at he
    exact injOn_capInv hΓ ht hs hs' he
  refine ⟨capInv γ' v, Lemma71C.capInv_nonneg γ' v, capInv_lt_capInv hΓ hv.1 hvt (by
    rw [← ENNReal.ofReal_coe_nnreal] at ht; exact ht), by rw [← hve, hηe v hv.1 hv.2], v, hv.1, hvt, rfl⟩

/-- **CS-a (landing at the middle curve)**: at a middle chart point `x ≠ 0` the inverse of the time-`t` chart lands
at `γ(κ u)` for a segment time `0 ≤ u < capInv γ' t`. -/
theorem exists_land_mid (hP : IsPocketSeg β α γ C c Ψ a b γ' κ) (ht : (t : ℝ≥0∞) < capLife γ') {η : ℝ → ℂ}
    (hη : IsLoewnerTrace W η) (hW : Continuous W) (hW0 : W 0 = 0)
    (hηe : ∀ s : ℝ, 0 ≤ s → s ≤ t → η s = γ' (capInv γ' s)) (n : ℤ) {x : ℝ}
    (hxL : -rightImg (fun s => -W s) 0 t - W t < x) (hxR : x < rightImg W 0 t - W t) (hx0 : x ≠ 0) :
    ∃ u : ℝ, 0 ≤ u ∧ u < capInv γ' t ∧ extendFrom H (fwdMapInv W t) x = γ' u ∧
      Tendsto (tChart c n W t).2.1 (𝓝[H] (x : ℂ)) (𝓝 (γ (κ u).toNNReal)) := by
  obtain ⟨u, hu0, hut, hue, -⟩ := exists_seg_mid hP.seg ht hη hW hW0 hηe hxL hxR hx0
  refine ⟨u, hu0, hut, hue, ?_⟩
  have h := tendsto_tChart_inv (t := t) hP.frame hη hW hW0 n (mem_Hbar_of_im_eq_zero (z := ((x : ℝ) : ℂ)) (by simp))
  rwa [hue, hP.land_seg hu0] at h

end Mid

end InteractingSLE.Sec7.Lemma71P
