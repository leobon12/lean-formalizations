/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec5.Aux61ChLocMeas
import InteractingSLE.Spec.Sec7.LocalExtOChart

/-!
# The chart leaf from the physical marked local set (Astra's follow-up 4 §1.1, read in the restart chart)

Packet PROVE-AUX61-CHARTLOC. The fibre side of (E1) was reduced (PROVE-AUX61-FIBK) to one analytic leaf,
`Aux61UnionK.IsChartLocalAt μ Z B Y q M h₁`: at the fibre time `q`, on `{Z ∈ B, q < life}`, the chart field of the
code `Y` minus a harmonic part `h₁` is, given the marks `σ(Z) ∨ σ(raw code at q) ∨ σ(h₁)`, a zero-boundary GFF on
`ℍ ∖ K_q` (`K_q` the chart hull), and `h₁` pairs like `M` off `K_q`. This file splits that leaf into its two
mathematical parts and proves the first one from the physical statement Astra §1.1 gives (ruling R71: "the field in
each selected complementary component has the form `h_D = h⁰_D + M_D` conditionally, where `h⁰_D` is a zero-boundary
GFF and `M_D` is the retained harmonic mean"):

* **`IsChartGaussAt μ Z B Y q 𝒢 h₁`** — (K-a), the conditional Gaussian decomposition in the chart given a σ-algebra
  `𝒢` containing the history and the raw code at `q`, with `h₁` measurable for `𝒢`;
  **`IsChartGaussAt.isChartLocalAt`**: (K-a) together with the identification of the mean (K-b: `h₁` pairs like `M`
  off the chart hull) is `IsChartLocalAt` (the tower property; the kernel's covariance is measurable for the marks by
  `Aux61ChLoc.measurable_cov_aliveHull`);
* **`isHistoryAvoidanceLocal_liveSet`**: the history-marked avoidance criterion passes from `A` to the set `A` on a
  mark `S` and `ℍ` off it;
* **`exists_isChartGaussAt_of_marked`** — (K-a) from the physical statement: if the field `h` (centred by a harmonic
  `u₀`) is a zero-boundary GFF, the chart `c` and the marks `ℋ ⊇ σ(Z) ∨ σ(raw code at q)` are as in
  `LocalExt.exists_condDecomp_chart`, the physical set `A` (the explored union read in the original domain, together
  with the outside of the selected component) satisfies the history-marked avoidance criterion for `ℋ` (Aux. lemmas
  18–19, Proposition 3.7 with retained records), and on the live event `ℍ ∖ A = c⁻¹(ℍ ∖ K_q)` with the code's field the
  chart transport of `h`, then (K-a) holds with `𝒢 = 𝒜_{A'} ∨ ℋ` (germs of the live version `A'` of `A`, and the marks).

Conditional helpers with distinct names; they replace no source theorem. R48/R77: nothing here uses Theorem 1.2/1.3,
`Theorem12ParamStatement`, `Theorem13Statement`, any `*_of_param` result, or Astra's post-contact kernel.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter Topology Function
open QuantumZipper (H fwdHull zeroGFFTestCov)
open LQGMetric (DistOn TestOn IsZeroBoundaryGFF)
open scoped NNReal ENNReal

namespace InteractingSLE.Sec5.Aux61ChLoc

open Aux61Fib (FibCode)
open Aux61FibK (codeFiltration)
open Aux61UnionK (chartHull chartMarks IsChartLocalAt norm_cexp_I_mul_ofReal_le measurable_field_apply
  measurable_apply_of_measurable)
open LocalSets (relClosureH germSigma)
open WholeField (IsHistoryAvoidanceLocal centredField)

universe u

/-! ### Conditional expectations that agree on a conditioning event -/

section CondExp

variable {Ω : Type*} {m mΩ : MeasurableSpace Ω} {μ : Measure Ω}

/-- If two integrable functions agree on an event `S` of the conditioning σ-algebra, their conditional expectations
agree almost everywhere on `S`. -/
theorem ae_condExp_eq_of_eqOn {S : Set Ω} (hS : MeasurableSet[m] S) {f f' : Ω → ℂ} (hf : Integrable f μ)
    (hf' : Integrable f' μ) (h : ∀ x ∈ S, f x = f' x) : ∀ᵐ x ∂μ, x ∈ S → μ[f | m] x = μ[f' | m] x := by
  have e : S.indicator f = S.indicator f' := indicator_congr h
  filter_upwards [condExp_indicator hf hS, condExp_indicator hf' hS] with x h1 h2 hx
  have h3 : S.indicator (μ[f | m]) x = S.indicator (μ[f' | m]) x := by rw [← h1, ← h2, e]
  rwa [indicator_of_mem hx, indicator_of_mem hx] at h3

end CondExp

/-! ### (K-a) in the chart, and the leaf from (K-a) and (K-b) -/

section Gauss

variable {X : Type u} {𝒢 : MeasurableSpace X} [mX : MeasurableSpace X] {β : Type*} [mβ : MeasurableSpace β]

/-- **The live event** at fibre time `q`: the history lies in `B` and `q` is before the code's lifetime. -/
def liveEv (Z : X → β) (B : Set β) (Y : X → FibCode) (q : ℝ≥0) : Set X :=
  {x | Z x ∈ B ∧ (q : ℝ≥0∞) < (Y x).life}

/-- **(K-a): the conditional Gaussian decomposition of the chart field at fibre time `q`** given a σ-algebra `𝒢`
containing the history and the raw code at `q`: on `{Z ∈ B, q < life}`, `h₁` (measurable for `𝒢`) is harmonic off the
chart hull `K_q`, and given `𝒢` the chart field minus `h₁` is a zero-boundary GFF on `ℍ ∖ K_q`. -/
structure IsChartGaussAt (μ : Measure X) (Z : X → β) (B : Set β) (Y : X → FibCode) (q : ℝ≥0)
    (𝒢 : MeasurableSpace X) (h₁ : X → DistOn upperHalfPlaneOpens) : Prop where
  le : 𝒢 ≤ mX
  marksZ : mβ.comap Z ≤ 𝒢
  marksY : (codeFiltration.{u} q).comap (fun x => ULift.up.{u} (Y x)) ≤ 𝒢
  measurable : Measurable[𝒢] h₁
  harmonic : ∀ᵐ x ∂μ, Z x ∈ B → (q : ℝ≥0∞) < (Y x).life → IsHarmonicDistOn (h₁ x) (H \ chartHull Y q x)
  gff : ∀ φ : TestOn upperHalfPlaneOpens, ∀ᵐ x ∂μ, Z x ∈ B → (q : ℝ≥0∞) < (Y x).life →
    μ[fun x' => Complex.exp (Complex.I * (((Y x').field φ - h₁ x' φ : ℝ) : ℂ)) | 𝒢] x =
      ((Real.exp (-(1 / 2) * zeroGFFTestCov (H \ chartHull Y q x) φ φ) : ℝ) : ℂ)

variable {μ : Measure X} {Z : X → β} {B : Set β} {Y : X → FibCode} {q : ℝ≥0}
  {h₁ : X → DistOn upperHalfPlaneOpens}

/-- The marks of the leaf are contained in the conditioning σ-algebra of (K-a). -/
theorem IsChartGaussAt.chartMarks_le (hG : IsChartGaussAt μ Z B Y q 𝒢 h₁) : chartMarks Z Y q h₁ ≤ 𝒢 :=
  sup_le (sup_le hG.marksZ hG.marksY) hG.measurable.comap_le

/-- **(K-a) gives the leaf's Gaussian clause** for the smaller marks `σ(Z) ∨ σ(raw code at q) ∨ σ(h₁)` (tower
property; on the live event the kernel `exp(−½ ‖φ‖²_{H⁻¹(ℍ∖K_q)})` is measurable for the marks). -/
theorem IsChartGaussAt.gff_marks [IsFiniteMeasure μ] (hY : Measurable Y) (hB : MeasurableSet B)
    (hG : IsChartGaussAt μ Z B Y q 𝒢 h₁) (φ : TestOn upperHalfPlaneOpens) :
    ∀ᵐ x ∂μ, Z x ∈ B → (q : ℝ≥0∞) < (Y x).life →
      μ[fun x' => Complex.exp (Complex.I * (((Y x').field φ - h₁ x' φ : ℝ) : ℂ)) | chartMarks Z Y q h₁] x =
        ((Real.exp (-(1 / 2) * zeroGFFTestCov (H \ chartHull Y q x) φ φ) : ℝ) : ℂ) := by
  have hm𝒢 : chartMarks Z Y q h₁ ≤ 𝒢 := hG.chartMarks_le
  have hm : chartMarks Z Y q h₁ ≤ mX := hm𝒢.trans hG.le
  have hS : MeasurableSet[chartMarks Z Y q h₁] (liveEv Z B Y q) :=
    measurableSet_live (le_sup_left.trans le_sup_left) (le_sup_right.trans le_sup_left) hB
  have hh₁ : Measurable h₁ := hG.measurable.mono hG.le le_rfl
  set f : X → ℂ := fun x' => Complex.exp (Complex.I * (((Y x').field φ - h₁ x' φ : ℝ) : ℂ)) with hf
  set g : X → ℂ := fun x =>
    ((Real.exp (-(1 / 2) * zeroGFFTestCov (H \ relClosureH (aliveHull.{u} q (ULift.up (Y x)))) φ φ) : ℝ) : ℂ)
    with hg
  have hfm : Measurable f := Complex.measurable_exp.comp (measurable_const.mul (Complex.measurable_ofReal.comp
    ((measurable_field_apply hY φ).sub (measurable_apply_of_measurable hh₁ φ))))
  have hfi : Integrable f μ :=
    Integrable.of_bound hfm.aestronglyMeasurable 1 (ae_of_all _ fun x => norm_cexp_I_mul_ofReal_le _)
  have hgm : StronglyMeasurable[chartMarks Z Y q h₁] ((liveEv Z B Y q).indicator g) := by
    refine Measurable.stronglyMeasurable (Measurable.indicator ?_ hS)
    exact Complex.measurable_ofReal.comp (Real.measurable_exp.comp
      ((measurable_cov_aliveHull (le_sup_right.trans le_sup_left) φ φ).const_mul _))
  have h1 : μ[μ[f | 𝒢] | chartMarks Z Y q h₁] =ᵐ[μ] μ[f | chartMarks Z Y q h₁] :=
    condExp_condExp_of_le hm𝒢 hG.le
  have h2 := condExp_indicator (m := chartMarks Z Y q h₁) (μ := μ) (integrable_condExp (f := f) (m := 𝒢)) hS
  have h3 : (liveEv Z B Y q).indicator (μ[f | 𝒢]) =ᵐ[μ] (liveEv Z B Y q).indicator g := by
    filter_upwards [hG.gff φ] with x hx
    by_cases hxS : x ∈ liveEv Z B Y q
    · rw [indicator_of_mem hxS, indicator_of_mem hxS, hx hxS.1 hxS.2]
      simp only [hg, relClosureH_aliveHull hxS.2]
    · rw [indicator_of_notMem hxS, indicator_of_notMem hxS]
  have h4 := condExp_congr_ae (m := chartMarks Z Y q h₁) h3
  have hgi : Integrable ((liveEv Z B Y q).indicator g) μ :=
    (integrable_condExp.indicator (hm _ hS)).congr h3
  have h5 : μ[(liveEv Z B Y q).indicator g | chartMarks Z Y q h₁] = (liveEv Z B Y q).indicator g :=
    condExp_of_stronglyMeasurable hm hgm hgi
  filter_upwards [h1, h2, h4] with x e1 e2 e4 hxB hxq
  have hxS : x ∈ liveEv Z B Y q := ⟨hxB, hxq⟩
  have e5 : (liveEv Z B Y q).indicator (μ[μ[f | 𝒢] | chartMarks Z Y q h₁]) x = (liveEv Z B Y q).indicator g x := by
    rw [← e2, e4, h5]
  rw [indicator_of_mem hxS, indicator_of_mem hxS, e1] at e5
  rw [e5]
  simp only [hg, relClosureH_aliveHull hxq]

/-- **The leaf from (K-a) and (K-b)**: the conditional Gaussian decomposition in the chart and the identification of
its harmonic part with `M` off the chart hull give `Aux61UnionK.IsChartLocalAt`. -/
theorem IsChartGaussAt.isChartLocalAt [IsFiniteMeasure μ] (hY : Measurable Y) (hB : MeasurableSet B)
    (hG : IsChartGaussAt μ Z B Y q 𝒢 h₁) {M : X → ℂ → ℝ}
    (hmean : ∀ᵐ x ∂μ, Z x ∈ B → (q : ℝ≥0∞) < (Y x).life → ∀ ψ : TestOn upperHalfPlaneOpens,
      Disjoint (tsupport ψ) (chartHull Y q x) → h₁ x ψ = ∫ z, M x z * ψ z) :
    IsChartLocalAt μ Z B Y q M h₁ :=
  ⟨hG.measurable.mono hG.le le_rfl, hG.harmonic, hmean, fun φ => hG.gff_marks hY hB φ⟩

end Gauss

/-! ### The live version of a marked local set -/

section Live

variable {Ω : Type*} {ℋ : MeasurableSpace Ω} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
  {h : Ω → DistOn upperHalfPlaneOpens}

open scoped Classical in
/-- **The live version** of a random set `A` on an event `S`: `A` on `S`, all of `ℍ` off it. -/
def liveSet (S : Set Ω) (A : Ω → Set ℂ) : Ω → Set ℂ := S.piecewise A fun _ => H

omit mΩ in
theorem liveSet_of_mem {S : Set Ω} {A : Ω → Set ℂ} {x : Ω} (hx : x ∈ S) : liveSet S A x = A x := by
  classical
  simp [liveSet, hx]

omit mΩ in
theorem liveSet_of_notMem {S : Set Ω} {A : Ω → Set ℂ} {x : Ω} (hx : x ∉ S) : liveSet S A x = H := by
  classical
  simp [liveSet, hx]

/-- **The history-marked avoidance criterion passes to the live version on a mark.** For an open `U ⊆ ℍ` and a mark
`F`: if `U = ∅` the avoidance events of `A` and of its live version agree; otherwise `ℍ` meets `U`, so the live
version avoids `U` only on `S`, and the event is `{A ∩ U = ∅} ∩ (F ∩ S)`, `F ∩ S` a mark. -/
theorem isHistoryAvoidanceLocal_liveSet {A : Ω → Set ℂ} (hloc : IsHistoryAvoidanceLocal ℋ A h P) {S : Set Ω}
    (hS : MeasurableSet[ℋ] S) : IsHistoryAvoidanceLocal ℋ (liveSet S A) h P := by
  intro U G hUH hG hd F hF
  by_cases hU : (U : Set ℂ) = ∅
  · have e : {ω | Disjoint (liveSet S A ω) (U : Set ℂ)} ∩ F = {ω | Disjoint (A ω) (U : Set ℂ)} ∩ F := by
      simp only [hU, disjoint_empty, Set.ofPred_true]
    rw [e]
    exact hloc U G hUH hG hd F hF
  · obtain ⟨z, hz⟩ := nonempty_iff_ne_empty.2 hU
    have e : {ω | Disjoint (liveSet S A ω) (U : Set ℂ)} ∩ F = {ω | Disjoint (A ω) (U : Set ℂ)} ∩ (F ∩ S) := by
      ext ω
      by_cases hω : ω ∈ S
      · simp only [mem_inter_iff, mem_ofPred_eq, liveSet_of_mem hω, hω, and_true]
      · simp only [mem_inter_iff, mem_ofPred_eq, liveSet_of_notMem hω, hω, and_false, iff_false, not_and]
        exact fun hd _ => Set.disjoint_left.1 hd (hUH hz) hz
    rw [e]
    exact hloc U G hUH hG hd (F ∩ S) (hF.inter hS)

end Live

/-! ### (K-a) from the physical marked local set -/

section Marked

variable {X : Type u} {ℋ : MeasurableSpace X} [mX : MeasurableSpace X] {β : Type*} [mβ : MeasurableSpace β]

/-- **(K-a) from the physical marked local set** (Astra's follow-up 4 §1.1, Lemma 3.6 (iii) with the history retained,
transported by the restart chart). Data on the glued space `X`: the field `h` with `h − u₀` a zero-boundary GFF
(`u₀` harmonic), a code `Y` whose field component is, on the live event, the chart transport
`h ∘ c⁻¹ + a + k ℓ ∘ c⁻¹` of `h` by a random conformal chart `c` (measurable for the marks `ℋ`, lifts continuous and
harmonic), marks `ℋ` containing the history and the raw code at `q`, and a hitting-measurable relatively closed
physical set `A` satisfying the history-marked avoidance criterion for `ℋ`, with `ℍ ∖ A = c⁻¹(ℍ ∖ K_q)` on the live
event. Then the chart field has the conditional Gaussian decomposition (K-a) at `q`, given
`𝒢 = 𝒜_{A'} ∨ ℋ` (`A'` the live version of `A`). -/
theorem exists_isChartGaussAt_of_marked {μ : Measure X} [IsProbabilityMeasure μ] {Z : X → β} {B : Set β}
    (hB : MeasurableSet B) {Y : X → FibCode} (hY : Measurable Y) (q : ℝ≥0)
    {h : X → DistOn upperHalfPlaneOpens} (hhm : Measurable h) {u₀ : ℂ → ℝ}
    (hu₀ : InnerProductSpace.HarmonicOnNhd u₀ H)
    (hh0 : IsZeroBoundaryGFF upperHalfPlaneOpens (centredField h u₀) μ)
    {c : X → Chart} (hc : ∀ x, (c x).IsConformal) (a k : ℝ)
    (hfield : ∀ x, Z x ∈ B → (q : ℝ≥0∞) < (Y x).life → (Y x).field = Chart.chartTransport (hc x) 1 a k (h x))
    (hℋ : ℋ ≤ mX) (hZℋ : mβ.comap Z ≤ ℋ)
    (hYℋ : (codeFiltration.{u} q).comap (fun x => ULift.up.{u} (Y x)) ≤ ℋ)
    (hdom : ∀ z, MeasurableSet[ℋ] {x | z ∈ (c x).dom})
    (hfwd : ∀ z, Measurable[ℋ] ({x | z ∈ (c x).dom}.indicator fun x => (c x).1 z))
    (hliftm : ∀ z, Measurable[ℋ] ({x | z ∈ (c x).dom}.indicator fun x => (c x).2.2 z))
    (hliftc : ∀ x, ContinuousOn (c x).2.2 (c x).dom)
    (hlift : ∀ x, InnerProductSpace.HarmonicOnNhd (c x).2.2 (c x).dom)
    {A : X → Set ℂ} (hAm : Measurable[mX, hittingSigma] A) (hAc : ∀ x, A x ⊆ H ∧ IsOpen (H \ A x))
    (hloc : IsHistoryAvoidanceLocal ℋ A (centredField h u₀) μ)
    (hgeo : ∀ᵐ x ∂μ, Z x ∈ B → (q : ℝ≥0∞) < (Y x).life → H \ A x = (c x).2.1 '' (H \ chartHull Y q x)) :
    ∃ h₁ : X → DistOn upperHalfPlaneOpens,
      IsChartGaussAt μ Z B Y q (germSigma (liveSet (liveEv Z B Y q) A) (centredField h u₀) ⊔ ℋ) h₁ := by
  classical
  set S := liveEv Z B Y q with hSdef
  have hSℋ : MeasurableSet[ℋ] S := measurableSet_live hZℋ hYℋ hB
  have hS : MeasurableSet S := hℋ _ hSℋ
  have hB'm : Measurable[mX, hittingSigma] (liveSet S A) :=
    Measurable.piecewise hS hAm measurable_const
  have hB'c : ∀ x, liveSet S A x ⊆ H ∧ IsOpen (H \ liveSet S A x) := by
    intro x
    by_cases hx : x ∈ S
    · rw [liveSet_of_mem hx]; exact hAc x
    · rw [liveSet_of_notMem hx, Set.sdiff_self]; exact ⟨subset_rfl, isOpen_empty⟩
  have hK' : ∀ x, liveSet S (chartHull Y q) x ⊆ H ∧ IsOpen (H \ liveSet S (chartHull Y q) x) := by
    intro x
    by_cases hx : x ∈ S
    · rw [liveSet_of_mem hx]
      exact ⟨fun _ hz => hz.1, Aux61UnionK.isOpen_H_diff_chartHull Y hx.2⟩
    · rw [liveSet_of_notMem hx, Set.sdiff_self]; exact ⟨subset_rfl, isOpen_empty⟩
  have hloc' := isHistoryAvoidanceLocal_liveSet hloc hSℋ
  have hBK : ∀ᵐ x ∂(μ[|univ]), H \ liveSet S A x = (c x).2.1 '' (H \ liveSet S (chartHull Y q) x) := by
    rw [cond_univ]
    filter_upwards [hgeo] with x hx
    by_cases hxS : x ∈ S
    · rw [liveSet_of_mem hxS, liveSet_of_mem hxS]; exact hx hxS.1 hxS.2
    · rw [liveSet_of_notMem hxS, liveSet_of_notMem hxS, Set.sdiff_self, image_empty]
  obtain ⟨M, hMm, hMh, hMc⟩ := LocalExt.exists_condDecomp_chart hhm hu₀ hh0 hc hdom hfwd hliftm hliftc hlift hℋ
    hB'm hB'c hloc' hK' (@MeasurableSet.univ _ ℋ) (by simp) hBK a k
  rw [cond_univ] at hMh hMc
  have h𝒢 : germSigma (liveSet S A) (centredField h u₀) ⊔ ℋ ≤ mX :=
    sup_le (LocalSets.germSigma_le hB'm (WholeField.measurable_centredField hhm u₀)) hℋ
  have hMm' : Measurable M := hMm.mono h𝒢 le_rfl
  refine ⟨M, ⟨h𝒢, hZℋ.trans le_sup_right, hYℋ.trans le_sup_right, hMm, ?_, fun φ => ?_⟩⟩
  · filter_upwards [hMh] with x hx hxB hxq
    have hxS : x ∈ S := ⟨hxB, hxq⟩
    rwa [liveSet_of_mem hxS] at hx
  · -- the two characteristic functionals agree on the live event, a mark
    have hSG : MeasurableSet[germSigma (liveSet S A) (centredField h u₀) ⊔ ℋ] S :=
      (le_sup_right : ℋ ≤ germSigma (liveSet S A) (centredField h u₀) ⊔ ℋ) _ hSℋ
    have hT : Measurable fun x => Chart.chartTransport (hc x) 1 a k (h x) :=
      Chart.measurable_chartTransport_random' hc (fun z => hℋ _ (hdom z)) (fun z => (hfwd z).mono hℋ le_rfl)
        (fun z => (hliftm z).mono hℋ le_rfl) hliftc hhm 1 a k
    have hfm : Measurable fun x' => Complex.exp (Complex.I * (((Y x').field φ - M x' φ : ℝ) : ℂ)) :=
      Complex.measurable_exp.comp (measurable_const.mul (Complex.measurable_ofReal.comp
        ((measurable_field_apply hY φ).sub (measurable_apply_of_measurable hMm' φ))))
    have hf'm : Measurable fun x' => Complex.exp (Complex.I *
        ((Chart.chartTransport (hc x') 1 a k (h x') φ - M x' φ : ℝ) : ℂ)) :=
      Complex.measurable_exp.comp (measurable_const.mul (Complex.measurable_ofReal.comp
        ((measurable_apply_of_measurable hT φ).sub (measurable_apply_of_measurable hMm' φ))))
    have heq := ae_condExp_eq_of_eqOn (μ := μ) hSG
      (Integrable.of_bound hfm.aestronglyMeasurable 1 (ae_of_all _ fun x => norm_cexp_I_mul_ofReal_le _))
      (Integrable.of_bound hf'm.aestronglyMeasurable 1 (ae_of_all _ fun x => norm_cexp_I_mul_ofReal_le _))
      (fun x hx => by rw [hfield x hx.1 hx.2])
    have e : (fun x' => Complex.exp (Complex.I *
        ((Chart.chartTransport (hc x') 1 a k (h x') φ - M x' φ : ℝ) : ℂ))) =
        fun x' => Complex.exp (Complex.I * (((Chart.chartTransport (hc x') 1 a k (h x') - M x') φ : ℝ) : ℂ)) := by
      funext x'
      rfl
    filter_upwards [heq, hMc φ] with x h1 h2 hxB hxq
    have hxS : x ∈ S := ⟨hxB, hxq⟩
    rw [h1 hxS, e, h2, liveSet_of_mem hxS]

end Marked

end InteractingSLE.Sec5.Aux61ChLoc
