/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.R5EnlCond

/-!
# The conditioned old-chart increment law from retained kernels, with the reference chart on an event

Packet PROVE-R5-ENLARGED. PROVE-POCKET-SIDEIN's `hasOldChartIncrementLaw_of_retained_kernels` needs the old chart
conformal at **every** sample and the current domain nested in it everywhere. R.5's reference chart exists only on
the reference event `G` (an event of the reference record `ℋ₀`). Here the chart is extended off `G` by the identity
(`oldOn`), the current domain by `ℍ` (`curOn`, whose chart `domChart` only records a domain), the kernels are moved to
`P[· | G]` (`isCondZeroBoundaryGFF_cond`), the landed reduction is applied under `P[· | G]`, and the result is read
back on `M ⊆ G` (`HasOldChartIncrementLaw.congr_on`).

## Main results

* `domChart`, `dom_domChart` — a chart with a prescribed open domain in `ℍ`;
* `oldOn`, `curOn` and their API (conformality, measurability of the domain and forward map);
* **`hasOldChartIncrementLawOn_of_retained_kernels`** — the conditioned law from the two retained physical kernels,
  with the reference chart only on `G`; the record-transport inputs `hAdded`, `hGerm` are those of the landed
  reduction for the extended charts.

Conditional helpers with distinct names; nothing here uses Theorem 1.2/1.3 or any `*_of_param` (R43, R48).
-/

set_option autoImplicit false
noncomputable section

open MeasureTheory ProbabilityTheory Set Filter Topology Metric
open QuantumZipper (H)
open LQGMetric (DistOn TestOn IsZeroBoundaryGFF)

namespace InteractingSLE.Sec7.R5Enl

open LocalSets PocketStopSide

/-! ### A chart recording an open domain -/

section DomChart

open Classical

/-- A chart whose domain is a prescribed set (only `dom` of this chart is ever used): the inverse is the identity
on `U` and a fixed point of `U` (or `i` when `U = ∅`) elsewhere. -/
def domChart (U : Set ℂ) : Chart :=
  (fun z => z, fun w => if w ∈ U then w else if hU : U.Nonempty then hU.some else Complex.I, fun _ => 0)

theorem image_domChart_of_nonempty {U : Set ℂ} (hUH : U ⊆ H) (hU : U.Nonempty) :
    (domChart U).2.1 '' H = U := by
  ext w
  constructor
  · rintro ⟨v, -, rfl⟩
    change (if v ∈ U then v else if hU : U.Nonempty then hU.some else Complex.I) ∈ U
    by_cases hv : v ∈ U
    · simp only [hv, ↓reduceIte]
    · simp only [hv, ↓reduceIte, hU, ↓reduceDIte]
      exact hU.some_mem
  · intro hw
    refine ⟨w, hUH hw, ?_⟩
    change (if w ∈ U then w else if hU : U.Nonempty then hU.some else Complex.I) = w
    simp only [hw, ↓reduceIte]

theorem I_mem_H : Complex.I ∈ H := by
  change 0 < Complex.I.im
  rw [Complex.I_im]
  exact one_pos

/-- **The domain of `domChart U` is `U`** for an open `U ⊆ ℍ`. -/
theorem dom_domChart {U : Set ℂ} (hUo : IsOpen U) (hUH : U ⊆ H) :
    ((domChart U).dom : Set ℂ) = U := by
  change interior ((domChart U).2.1 '' H) = U
  by_cases hU : U.Nonempty
  · rw [image_domChart_of_nonempty hUH hU, hUo.interior_eq]
  · rw [not_nonempty_iff_eq_empty] at hU
    subst hU
    have hinv : (domChart (∅ : Set ℂ)).2.1 = fun _ => Complex.I := by
      funext v
      simp only [domChart, mem_empty_iff_false, ↓reduceIte, Set.not_nonempty_empty, ↓reduceDIte]
    have e : (domChart (∅ : Set ℂ)).2.1 '' H = {Complex.I} := by
      rw [hinv]
      exact (Set.Nonempty.image_const ⟨Complex.I, I_mem_H⟩ _)
    rw [e, interior_singleton]

/-- The identity chart has domain `ℍ`. -/
theorem dom_chart_id : ((Chart.id.dom : TopologicalSpace.Opens ℂ) : Set ℂ) = H := by
  change interior ((fun z : ℂ => z) '' H) = H
  rw [image_id', QuantumZipper.isOpen_H.interior_eq]

end DomChart

/-! ### Charts extended off the reference event -/

section Extend

variable {Ω : Type*}

open Classical in
/-- The reference chart on `G`, the identity chart off `G`. -/
def oldOn (G : Set Ω) (old : Ω → Chart) (ω : Ω) : Chart :=
  if ω ∈ G then old ω else Chart.id

open Classical in
/-- A chart with domain `U ω` on `G`, the identity chart (domain `ℍ`) off `G`. -/
def curOn (G : Set Ω) (U : Ω → Set ℂ) (ω : Ω) : Chart :=
  if ω ∈ G then domChart (U ω) else Chart.id

theorem oldOn_of_mem {G : Set Ω} {old : Ω → Chart} {ω : Ω} (hω : ω ∈ G) : oldOn G old ω = old ω := by
  simp only [oldOn, hω, ↓reduceIte]

theorem oldOn_of_notMem {G : Set Ω} {old : Ω → Chart} {ω : Ω} (hω : ω ∉ G) : oldOn G old ω = Chart.id := by
  simp only [oldOn, hω, ↓reduceIte]

theorem isConformal_oldOn {G : Set Ω} {old : Ω → Chart} (hOld : ∀ ω ∈ G, (old ω).IsConformal) (ω : Ω) :
    (oldOn G old ω).IsConformal := by
  by_cases hω : ω ∈ G
  · rw [oldOn_of_mem hω]
    exact hOld ω hω
  · rw [oldOn_of_notMem hω]
    exact Chart.isConformal_id

theorem dom_curOn_of_mem {G : Set Ω} {U : Ω → Set ℂ} {ω : Ω} (hω : ω ∈ G) (hUo : IsOpen (U ω))
    (hUH : U ω ⊆ H) : ((curOn G U ω).dom : Set ℂ) = U ω := by
  simp only [curOn, hω, ↓reduceIte]
  exact dom_domChart hUo hUH

theorem dom_curOn_of_notMem {G : Set Ω} {U : Ω → Set ℂ} {ω : Ω} (hω : ω ∉ G) :
    ((curOn G U ω).dom : Set ℂ) = H := by
  simp only [curOn, hω, ↓reduceIte]
  exact dom_chart_id

variable {ℳ : MeasurableSpace Ω}

theorem measurableSet_mem_dom_oldOn {G : Set Ω} (hG : MeasurableSet[ℳ] G) {old : Ω → Chart}
    {z : ℂ} (hdom : MeasurableSet[ℳ] (G ∩ {ω | z ∈ (old ω).dom})) :
    MeasurableSet[ℳ] {ω | z ∈ (oldOn G old ω).dom} := by
  have e : {ω | z ∈ (oldOn G old ω).dom} = (G ∩ {ω | z ∈ (old ω).dom}) ∪ (Gᶜ ∩ {_ω | z ∈ H}) := by
    ext ω
    by_cases hω : ω ∈ G
    · simp only [mem_ofPred_eq, oldOn_of_mem hω, mem_union, mem_inter_iff, hω, true_and,
        mem_compl_iff, not_true_eq_false, false_and, or_false]
    · have hd := dom_chart_id
      simp only [mem_ofPred_eq, oldOn_of_notMem hω, mem_union, mem_inter_iff, hω, false_and,
        mem_compl_iff, not_false_eq_true, true_and, false_or]
      rw [← SetLike.mem_coe, hd]
  rw [e]
  exact hdom.union (hG.compl.inter (MeasurableSet.const _))

theorem measurable_indicator_fwd_oldOn {G : Set Ω} (hG : MeasurableSet[ℳ] G) {old : Ω → Chart} {z : ℂ}
    (hfwd : Measurable[ℳ] ((G ∩ {ω | z ∈ (old ω).dom}).indicator fun ω => (old ω).1 z)) :
    Measurable[ℳ] ({ω | z ∈ (oldOn G old ω).dom}.indicator fun ω => (oldOn G old ω).1 z) := by
  have e : ({ω | z ∈ (oldOn G old ω).dom}.indicator fun ω => (oldOn G old ω).1 z) =
      fun ω => (G ∩ {ω | z ∈ (old ω).dom}).indicator (fun ω => (old ω).1 z) ω +
        (Gᶜ ∩ {_ω | z ∈ H}).indicator (fun _ => z) ω := by
    funext ω
    by_cases hω : ω ∈ G
    · have h2 : ω ∉ Gᶜ ∩ {_ω | z ∈ H} := fun h => h.1 hω
      rw [indicator_of_notMem h2, add_zero]
      by_cases hz : z ∈ (old ω).dom
      · rw [indicator_of_mem (show ω ∈ {ω | z ∈ (oldOn G old ω).dom} by
            change z ∈ (oldOn G old ω).dom; rw [oldOn_of_mem hω]; exact hz),
          indicator_of_mem (show ω ∈ G ∩ {ω | z ∈ (old ω).dom} from ⟨hω, hz⟩), oldOn_of_mem hω]
      · rw [indicator_of_notMem (show ω ∉ {ω | z ∈ (oldOn G old ω).dom} by
            change z ∉ (oldOn G old ω).dom; rw [oldOn_of_mem hω]; exact hz),
          indicator_of_notMem (show ω ∉ G ∩ {ω | z ∈ (old ω).dom} from fun h => hz h.2)]
    · have h1 : ω ∉ G ∩ {ω | z ∈ (old ω).dom} := fun h => hω h.1
      rw [indicator_of_notMem h1, zero_add]
      have hd := dom_chart_id
      by_cases hz : z ∈ H
      · rw [indicator_of_mem (show ω ∈ {ω | z ∈ (oldOn G old ω).dom} by
            change z ∈ (oldOn G old ω).dom; rw [oldOn_of_notMem hω, ← SetLike.mem_coe, hd]; exact hz),
          indicator_of_mem (show ω ∈ Gᶜ ∩ {_ω | z ∈ H} from ⟨hω, hz⟩), oldOn_of_notMem hω]
        rfl
      · rw [indicator_of_notMem (show ω ∉ {ω | z ∈ (oldOn G old ω).dom} by
            change z ∉ (oldOn G old ω).dom; rw [oldOn_of_notMem hω, ← SetLike.mem_coe, hd]; exact hz),
          indicator_of_notMem (show ω ∉ Gᶜ ∩ {_ω | z ∈ H} from fun h => hz h.2)]
  rw [e]
  exact hfwd.add (measurable_const.indicator (hG.compl.inter (MeasurableSet.const _)))

end Extend

/-! ### The conditioned law from retained kernels -/

section Kernel

variable {Ω : Type*} {ℋ₀ ℋ₁ : MeasurableSpace Ω} [mΩ : MeasurableSpace Ω] {P : Measure Ω}

/-- `h − g` is measurable when both are (the second for a sub-σ-algebra). -/
theorem measurable_sub_of_le (hℋ : ℋ₁ ≤ mΩ) {h g : Ω → DistOn upperHalfPlaneOpens}
    (hh : Measurable h) (hg : Measurable[ℋ₁] g) : Measurable fun ω => h ω - g ω :=
  LQGMetric.measurable_distOn_iff.2 fun φ =>
    ((LQGMetric.measurable_distOn_apply φ).comp hh).sub
      ((LQGMetric.measurable_distOn_apply φ).comp (hg.mono hℋ le_rfl))

/-- **The conditioned old-chart increment law from the retained kernels, with the reference chart only on the
reference event `G ∈ ℋ₀`.** The old physical kernel is retained by `ℋ₀` on the domain `Uold` (equal to the reference
chart's domain on `G`), the current physical kernel by `ℋ₁ ≥ ℋ₀` on `U` (nested in the reference domain on `G`); the
added set and the residual germ of the extended charts are retained by `ℋ₁` (`hAdded`, `hGerm`). On every `M ⊆ G`
where the current chart's domain is `U`, the increment law holds under `P[· | G]`. -/
theorem hasOldChartIncrementLawOn_of_retained_kernels [IsProbabilityMeasure P]
    (hInfo : ℋ₀ ≤ ℋ₁) (hℋ₁ : ℋ₁ ≤ mΩ) {G : Set Ω} (hG : MeasurableSet[ℋ₀] G)
    {old : Ω → Chart} (hOld : ∀ ω ∈ G, (old ω).IsConformal)
    (hdom : ∀ z, MeasurableSet[ℋ₀] (G ∩ {ω | z ∈ (old ω).dom}))
    (hfwd : ∀ z, Measurable[ℋ₀] ((G ∩ {ω | z ∈ (old ω).dom}).indicator fun ω => (old ω).1 z))
    {U : Ω → Set ℂ} (hUo : ∀ ω ∈ G, IsOpen (U ω)) (hNested : ∀ ω ∈ G, U ω ⊆ (old ω).dom)
    {h gOld gNow : Ω → DistOn upperHalfPlaneOpens} (hh : Measurable h)
    (hMeanOld : Measurable[ℋ₁] gOld) (hMeanNow : Measurable[ℋ₁] gNow)
    (hHarmOld : ∀ᵐ ω ∂P, ω ∈ G → IsHarmonicDistOn (gOld ω) (old ω).dom)
    (hHarmNow : ∀ᵐ ω ∂P, ω ∈ G → IsHarmonicDistOn (gNow ω) (U ω))
    {Uold : Ω → Set ℂ} (hUold : ∀ᵐ ω ∂P, ω ∈ G → Uold ω = (old ω).dom)
    (hOldKernel : IsCondZeroBoundaryGFF P ℋ₀ Uold (fun ω => h ω - gOld ω))
    (hCurrentKernel : IsCondZeroBoundaryGFF P ℋ₁ U (fun ω => h ω - gNow ω))
    (hAdded : Measurable[ℋ₁, hittingSigma] (globalOldChartAddedSet (oldOn G old) (curOn G U)))
    (hGerm : germSigma (globalOldChartAddedSet (oldOn G old) (curOn G U))
      (fun ω => Chart.pullField (isConformal_oldOn hOld ω) (h ω - gOld ω)) ≤ ℋ₁)
    {M : Set Ω} (hMG : M ⊆ G) {current : Ω → Chart}
    (hcur : ∀ ω ∈ M, ((current ω).dom : Set ℂ) = U ω) :
    HasOldChartIncrementLawOn P M old current gOld gNow := by
  have hℋ₀ : ℋ₀ ≤ mΩ := hInfo.trans hℋ₁
  have hGm : MeasurableSet G := hℋ₀ _ hG
  have hUH : ∀ ω ∈ G, U ω ⊆ H := fun ω hω => (hNested ω hω).trans (hOld ω hω).dom_subset
  have hcurG : ∀ ω ∈ G, ((curOn G U ω).dom : Set ℂ) = U ω := fun ω hω =>
    dom_curOn_of_mem hω (hUo ω hω) (hUH ω hω)
  refine ⟨G, hGm, hMG, fun hP => ?_⟩
  have hNested' : ∀ ω, ((curOn G U ω).dom : Set ℂ) ⊆ (oldOn G old ω).dom := by
    intro ω
    by_cases hω : ω ∈ G
    · rw [hcurG ω hω, oldOn_of_mem hω]
      exact hNested ω hω
    · rw [dom_curOn_of_notMem hω, oldOn_of_notMem hω, dom_chart_id]
  have hHarmOld' : ∀ᵐ ω ∂P[|G], IsHarmonicDistOn (gOld ω) (oldOn G old ω).dom := by
    refine ae_cond_of_ae hGm ?_
    filter_upwards [hHarmOld] with ω hω hG'
    rw [oldOn_of_mem hG']
    exact hω hG'
  have hHarmNow' : ∀ᵐ ω ∂P[|G], IsHarmonicDistOn (gNow ω) (curOn G U ω).dom := by
    refine ae_cond_of_ae hGm ?_
    filter_upwards [hHarmNow] with ω hω hG'
    rw [hcurG ω hG']
    exact hω hG'
  have hOldKernel' : IsCondZeroBoundaryGFF (P[|G]) ℋ₀ (fun ω => ((oldOn G old ω).dom : Set ℂ))
      (fun ω => h ω - gOld ω) := by
    refine isCondZeroBoundaryGFF_cond hℋ₀ hG (measurable_sub_of_le hℋ₁ hh hMeanOld) hOldKernel ?_
    filter_upwards [hUold] with ω hω hG'
    rw [oldOn_of_mem hG']
    exact hω hG'
  have hCurrentKernel' : IsCondZeroBoundaryGFF (P[|G]) ℋ₁ (fun ω => ((curOn G U ω).dom : Set ℂ))
      (fun ω => h ω - gNow ω) :=
    isCondZeroBoundaryGFF_cond hℋ₁ (hInfo _ hG) (measurable_sub_of_le hℋ₁ hh hMeanNow) hCurrentKernel
      (Eventually.of_forall fun ω hG' => (hcurG ω hG').symm)
  have hlaw := @hasOldChartIncrementLaw_of_retained_kernels Ω ℋ₀ ℋ₁ mΩ (P[|G]) hP hInfo hℋ₁
    (oldOn G old) (curOn G U) (isConformal_oldOn hOld)
    (fun z => measurableSet_mem_dom_oldOn hG (hdom z))
    (fun z => measurable_indicator_fwd_oldOn hG (hfwd z)) hNested' h gOld gNow hh hMeanOld hMeanNow
    hHarmOld' hHarmNow' hOldKernel' hCurrentKernel' hAdded hGerm M
  refine HasOldChartIncrementLaw.congr_on hlaw (Eventually.of_forall fun ω hM => ?_)
  exact ⟨oldOn_of_mem (hMG hM), by rw [hcurG ω (hMG hM), hcur ω hM], rfl, rfl⟩

end Kernel

end InteractingSLE.Sec7.R5Enl
