/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.Q3ChainUnion

/-!
# The retained-set mean of GB6: the deterministic identities

Packet PROVE-Q3-REL3, input `hind₁` of `Q3Chain.ae_eqOn_unionMean_gb6` (the local-set mean of the retained flow prefix
`A = −1/K^α_s` in the counterflow frame is the chart field's word read through GB6's retained chart). The
probabilistic part is the flow's own hull mean (`Sec7.SideHeight.ae_apply_eq_of_isLocalSetMean_flowHull`) reflected by
`R(z) = −1/z`; this file proves the deterministic identities that turn it into `hind₁`'s form:

* `eqOn_bhe_cfData_retWord`: a bounded harmonic extension of the counterflow data of a returned word `retWord a l c`
  is the return transform `z ↦ −F(−1/z) + a + l·Im(−2 Log z)` of a bounded harmonic extension `F` of `c`;
* `eqOn_bhe_stopWord`: a bounded harmonic extension of the flow's stop word is the extension of the flow's force data
  at the record's flowed marks, minus `θχ`;
* `eqOn_bhe_cfData_return`: the counterflow's initial extension is the return transform of the original one (the
  counterflow data is the returned flow data, `GB6.data_eq_returnData`);
* **`retained_mean_identity`**: the pointwise identity
  `−(𝔥_s(Rz) − θχ − 𝔥⁰(Rz)) + 𝔥⁰′(z) = G₀(Ψ z) − χ(16/κ) Im relLog(z)` (`R z = −1/z`, `Ψ = relMap U s`), with
  `arg(−1/ξ) = π − arg ξ` on `ℍ` and `χ(16/κ) = −χ(κ)`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Filter Set Topology
open scoped NNReal ENNReal
open QuantumZipper (H fwdMap fwdMapInv fwdHull logDerivFwd chiC)

namespace InteractingSLE.Supp8.Q3Chain

open Restart Sec7.StripSysField

/-- The return transform `z ↦ −F(−1/z) + a + l·Im(−2 Log z)` of a function on `ℍ`. -/
def retFn (a l : ℝ) (F : ℂ → ℝ) (z : ℂ) : ℝ := -F (-z⁻¹) + a + l * infinitySourceChart.2.2 z

/-- A bounded harmonic extension of `g − c` is one of `g` minus the constant. -/
theorem bhe_sub_const {g : ℝ → ℝ} {S : Set ℝ} {u : ℂ → ℝ} (hu : IsBoundedHarmonicExtension g S u) (c : ℝ) :
    IsBoundedHarmonicExtension (fun x => g x - c) S (fun z => u z - c) := by
  obtain ⟨hh, ⟨C, hC⟩, hl⟩ := hu
  refine ⟨fun z hz => (hh z hz).sub (InnerProductSpace.harmonicAt_const c), ⟨C + |c|, fun z hz => ?_⟩,
    fun x hx => (hl x hx).sub_const c⟩
  calc |u z - c| ≤ |u z| + |c| := abs_sub _ _
    _ ≤ C + |c| := by linarith [hC z hz]

/-! ### Returned words -/

/-- **The counterflow extension of a returned word is the return transform** (`0 < k`). -/
theorem eqOn_bhe_cfData_retWord {k : ℝ} (hk : 0 < k) {c : BoundaryWord} (hc : c.IsSorted) (a l : ℝ)
    {F G : ℂ → ℝ} (hF : IsBoundedHarmonicExtension c.fn c.jumps F)
    (hG : IsBoundedHarmonicExtension (cfData k (Theorem14.GW2JointKernel.retWord a l c).fn
      (Theorem14.GW2JointKernel.retWord a l c).jumps)
      (cfJumps (Theorem14.GW2JointKernel.retWord a l c).fn (Theorem14.GW2JointKernel.retWord a l c).jumps) G) :
    EqOn G (retFn a l F) H := by
  set β := Theorem14.GW2JointKernel.retWord a l c with hβ
  have hR := isBoundedHarmonicExtension_return a l (S := c.jumps) hF
  set S' : Finset ℝ := insert 0 (cfJumps β.fn β.jumps ∪ β.jumps ∪ returnExcept c.jumps) with hS'
  have hR' : IsBoundedHarmonicExtension (returnData a l c.fn) (S' : Set ℝ) (retFn a l F) := by
    refine LocalExt.IsBoundedHarmonicExtension.mono_set hR fun x hx => ?_
    simp only [hS', Finset.coe_insert, Finset.coe_union, mem_insert_iff, mem_union, Finset.mem_coe]
    exact Or.inr (Or.inr hx)
  have hG' : IsBoundedHarmonicExtension (returnData a l c.fn) (S' : Set ℝ) G := by
    have h1 := LocalExt.IsBoundedHarmonicExtension.mono_set hG (S' := (S' : Set ℝ)) fun x hx => by
      simp only [hS', Finset.coe_insert, Finset.coe_union, mem_insert_iff, mem_union, Finset.mem_coe]
      exact Or.inr (Or.inl (Or.inl hx))
    refine (Restart.isBoundedHarmonicExtension_congr (fun x hx => ?_) G).1 h1
    simp only [hS', Finset.coe_insert, Finset.coe_union, mem_insert_iff, mem_union, Finset.mem_coe, not_or] at hx
    obtain ⟨hx0, ⟨-, hxβ⟩, -⟩ := hx
    rw [cfData, Sec4.forceBoundaryData_flowLine hk (BoundaryWord.isPiecewiseConstantBoundaryData β) hx0 hxβ]
    exact Theorem14.GW2JointKernel.fn_retWord hc a l hxβ
  exact Impl.eqOn_of_isBoundedHarmonicExtension (Finset.finite_toSet S') hR' hG'


/-! ### The stop word -/

open Exist.Staged Exist.StagedLaw in
/-- **The extension of the flow's stop word is the extension of the force data at the record's flowed marks, minus
`θχ`** (`Exist.StagedLaw.stopWord`: the word of the field read in the flow's own Loewner chart at the record time). -/
theorem eqOn_bhe_stopWord (κ θ : ℝ) (c : BoundaryWord) (r : RecData) {F u : ℂ → ℝ}
    (hF : IsBoundedHarmonicExtension (stopWord κ (c, θ, r)).fn (stopWord κ (c, θ, r)).jumps F)
    (hu : IsBoundedHarmonicExtension
      (forceBoundaryData κ (flowLineRhoL κ c.fn c.jumps 0 θ) (flowLineRhoR κ c.fn c.jumps 0 θ)
        (fun i => markPosL (rdrv r) (rtime r) (flowLineXL c.fn c.jumps 0 i))
        (fun j => markPos (rdrv r) (rtime r) (flowLineXR c.fn c.jumps 0 j)))
      (forceJumpSet (fun i => markPosL (rdrv r) (rtime r) (flowLineXL c.fn c.jumps 0 i))
        (fun j => markPos (rdrv r) (rtime r) (flowLineXR c.fn c.jumps 0 j))) u) :
    EqOn F (fun z => u z - θ * chiC κ) H := by
  have hmo := Theorem14.GW1W.isMarkOrder_stopWord c r
  set S' : Finset ℝ := insert 0 ((stopWord κ (c, θ, r)).jumps ∪
    initJumps (fun i => markPosL (rdrv r) (rtime r) (flowLineXL c.fn c.jumps 0 i))
      (fun j => markPos (rdrv r) (rtime r) (flowLineXR c.fn c.jumps 0 j))) with hS'
  have hF' : IsBoundedHarmonicExtension (stopWord κ (c, θ, r)).fn (S' : Set ℝ) F := by
    refine LocalExt.IsBoundedHarmonicExtension.mono_set hF fun x hx => ?_
    simp only [hS', Finset.coe_insert, Finset.coe_union, mem_insert_iff, mem_union, Finset.mem_coe]
    exact Or.inr (Or.inl hx)
  have hu' := bhe_sub_const hu (θ * chiC κ)
  rw [← coe_initJumps] at hu'
  have hu'' := LocalExt.IsBoundedHarmonicExtension.mono_set hu' (S' := (S' : Set ℝ)) fun x hx => by
    simp only [hS', Finset.coe_insert, Finset.coe_union, mem_insert_iff, mem_union, Finset.mem_coe]
    exact Or.inr (Or.inr hx)
  have hdata : ∀ x ∉ (S' : Set ℝ), (stopWord κ (c, θ, r)).fn x =
      forceBoundaryData κ (flowLineRhoL κ c.fn c.jumps 0 θ) (flowLineRhoR κ c.fn c.jumps 0 θ)
        (fun i => markPosL (rdrv r) (rtime r) (flowLineXL c.fn c.jumps 0 i))
        (fun j => markPos (rdrv r) (rtime r) (flowLineXR c.fn c.jumps 0 j)) x - θ * chiC κ := by
    intro x hx
    have hxJ : x ∉ (stopWord κ (c, θ, r)).jumps := fun h =>
      hx (Finset.mem_coe.2 (Finset.mem_insert_of_mem (Finset.mem_union_left _ h)))
    have hx0 : x ≠ 0 := fun h => hx (Finset.mem_coe.2 (h ▸ Finset.mem_insert_self _ _))
    refine (fn_forceWord κ (padFL κ θ c.fn c.jumps).2.1 (padFL κ θ c.fn c.jumps).2.2 (θ * chiC κ) hmo hxJ
      hx0).trans ?_
    have eL : (fun i : Fin (flowLineNL c.fn c.jumps 0) => (padFL κ θ c.fn c.jumps).2.1 i) =
        flowLineRhoL κ c.fn c.jumps 0 θ := funext fun i => padFL_snd_fst_fin κ θ c.fn c.jumps i
    have eR : (fun j : Fin (flowLineNR c.fn c.jumps 0) => (padFL κ θ c.fn c.jumps).2.2 j) =
        flowLineRhoR κ c.fn c.jumps 0 θ := funext fun j => padFL_snd_snd_fin κ θ c.fn c.jumps j
    have pL : (fun i : Fin (flowLineNL c.fn c.jumps 0) =>
        markPosL (rdrv r) (rtime r) ((padFL 0 0 c.fn c.jumps).1.1 i)) =
        fun i => markPosL (rdrv r) (rtime r) (flowLineXL c.fn c.jumps 0 i) :=
      funext fun i => by rw [padFL_fst_fst_fin]
    have pR : (fun j : Fin (flowLineNR c.fn c.jumps 0) =>
        markPos (rdrv r) (rtime r) ((padFL 0 0 c.fn c.jumps).1.2 j)) =
        fun j => markPos (rdrv r) (rtime r) (flowLineXR c.fn c.jumps 0 j) :=
      funext fun j => by rw [padFL_fst_snd_fin]
    rw [eL, eR, pL, pR]
  have hv : IsBoundedHarmonicExtension (stopWord κ (c, θ, r)).fn (S' : Set ℝ) (fun z => u z - θ * chiC κ) :=
    (Restart.isBoundedHarmonicExtension_congr (S := (S' : Set ℝ)) (g := fun x =>
      forceBoundaryData κ (flowLineRhoL κ c.fn c.jumps 0 θ) (flowLineRhoR κ c.fn c.jumps 0 θ)
        (fun i => markPosL (rdrv r) (rtime r) (flowLineXL c.fn c.jumps 0 i))
        (fun j => markPos (rdrv r) (rtime r) (flowLineXR c.fn c.jumps 0 j)) x - θ * chiC κ)
      (g' := (stopWord κ (c, θ, r)).fn) hdata _).2 hu''
  exact Impl.eqOn_of_isBoundedHarmonicExtension (Finset.finite_toSet S') hv hF'

/-! ### The counterflow's initial extension -/

/-- **The counterflow's initial extension is the return transform of the original one** (GB6's frames: `h'` is `h`
read through `R(z) = −1/z` with the counterflow coefficients). -/
theorem eqOn_bhe_cfData_return {κ : ℝ} (hκ : 0 < κ) {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {h h' : Ω → LQGMetric.DistOn upperHalfPlaneOpens} {b b' : ℝ → ℝ} {J J' : Finset ℝ}
    (hb : IsPiecewiseConstantBoundaryData b J) (hG : IsGFFWithBoundaryData P h b J)
    (hb' : IsPiecewiseConstantBoundaryData b' J') (hG' : IsGFFWithBoundaryData P h' b' J')
    (hT : ∀ ω, IsChartTransport infinitySourceChart (-1) (-(Real.pi * chiC κ)) (chiC (16 / κ)) (h ω) (h' ω))
    {u₀ u₀' : ℂ → ℝ} (hu₀ : IsBoundedHarmonicExtension b J u₀)
    (hu₀' : IsBoundedHarmonicExtension (cfData (16 / κ) b' J')
      (forceJumpSet (flowLineXL b' J' 0) (flowLineXR b' J' 0)) u₀') :
    EqOn u₀' (retFn (Real.pi * chiC κ) (chiC κ) u₀) H := by
  have hR := isBoundedHarmonicExtension_return (Real.pi * chiC κ) (chiC κ) (S := J) hu₀
  set S' : Finset ℝ := insert 0 (cfJumps b' J' ∪ J' ∪ returnExcept J) with hS'
  have hR' : IsBoundedHarmonicExtension (returnData (Real.pi * chiC κ) (chiC κ) b) (S' : Set ℝ)
      (retFn (Real.pi * chiC κ) (chiC κ) u₀) := by
    refine LocalExt.IsBoundedHarmonicExtension.mono_set hR fun x hx => ?_
    simp only [hS', Finset.coe_insert, Finset.coe_union, mem_insert_iff, mem_union, Finset.mem_coe]
    exact Or.inr (Or.inr hx)
  have hk : (0 : ℝ) < 16 / κ := by positivity
  have h1 := LocalExt.IsBoundedHarmonicExtension.mono_set hu₀' (S' := (S' : Set ℝ)) fun x hx => by
    simp only [hS', Finset.coe_insert, Finset.coe_union, mem_insert_iff, mem_union, Finset.mem_coe]
    rw [← coe_cfJumps] at hx
    exact Or.inr (Or.inl (Or.inl hx))
  refine Impl.eqOn_of_isBoundedHarmonicExtension (Finset.finite_toSet S') hR'
    ((Restart.isBoundedHarmonicExtension_congr (fun x hx => ?_) _).1 h1)
  simp only [hS', Finset.coe_insert, Finset.coe_union, mem_insert_iff, mem_union, Finset.mem_coe, not_or] at hx
  obtain ⟨hx0, ⟨-, hxJ'⟩, hxR⟩ := hx
  have hxJ : -x⁻¹ ∉ J := fun h => hxR (Finset.mem_insert_of_mem (Finset.mem_image.2 ⟨-x⁻¹, h, by
    rw [inv_neg, inv_inv, neg_neg]⟩))
  rw [cfData, Sec4.forceBoundaryData_flowLine hk hb' hx0 hxJ']
  exact GB6.data_eq_returnData hκ hb hG hb' hG' hT hxJ' hx0 hxJ

/-! ### The pointwise identity -/

/-- **The retained-set mean identity** (deterministic). For `z ∈ ℍ` with `ξ = f_s(−1/z) ∈ ℍ`: if the stop-word
extension is the flow's force-data extension minus `θχ` at `ξ`, the chart field's extension is the return transform
of the stop-word extension at `Ψ z`, and the counterflow's initial extension is the return transform of the original
one at `z`, then the reflected flow mean plus the counterflow's initial extension is GB6's chart candidate:
`−(𝔥_s(−1/z) − θχ − 𝔥⁰(−1/z)) + 𝔥⁰′(z) = G₀(Ψ z) − χ(16/κ) Im relLog(z)`. -/
theorem retained_mean_identity {κ : ℝ} (hκ : 0 < κ) {U : ℝ → ℝ} {s : ℝ} {z : ℂ} (hz : z ∈ H)
    (hξ : fwdMap U s (-z⁻¹) ∈ H) (θ : ℝ) {u u₀ u₀' F G₀ : ℂ → ℝ}
    (hF : F (fwdMap U s (-z⁻¹)) = u (fwdMap U s (-z⁻¹)) - θ * chiC κ)
    (hG₀ : G₀ (GB6.relMap U s z) = retFn (Real.pi * chiC κ) (chiC κ) F (GB6.relMap U s z))
    (hu₀' : u₀' z = retFn (Real.pi * chiC κ) (chiC κ) u₀ z) :
    -(couplingMean κ U s u (-z⁻¹) - θ * chiC κ - u₀ (-z⁻¹)) + u₀' z =
      G₀ (GB6.relMap U s z) - chiC (16 / κ) * (Q3Rel.relLog U s z).im := by
  set ξ := fwdMap U s (-z⁻¹) with hξdef
  have hR : -(GB6.relMap U s z)⁻¹ = ξ := by
    simp only [GB6.relMap, hξdef, inv_neg, inv_inv, neg_neg]
  have hargΨ : Complex.arg (GB6.relMap U s z) = Real.pi - Complex.arg ξ := by
    have e : GB6.relMap U s z = WangWu.negInv ξ := rfl
    rw [e]
    exact Sec5.GlueImg.arg_negInv_of_mem_H hξ
  have hargz : Complex.arg (-z⁻¹) = Real.pi - Complex.arg z := Sec5.GlueImg.arg_negInv_of_mem_H hz
  rw [hG₀, hu₀', Q3Rel.im_relLog, Sec4.chiC_sixteen_div hκ]
  simp only [retFn, couplingMean, infinitySourceChart_lift, hR, hargΨ, hargz, hF]
  ring

end InteractingSLE.Supp8.Q3Chain
