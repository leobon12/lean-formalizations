/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec5.Aux61OldBTriv
import InteractingSLE.Spec.Sec5.Aux61MeanIdUniq
import InteractingSLE.Spec.Sec5.Aux61MeanIdSlit
import InteractingSLE.Spec.Sec5.Aux61FibKTilt

/-!
# Aux. 61's old boundary, II: the relative chart field under the time-`0` conditional measure

Packet PROVE-AUX61-OLDB. MEAN's route for (c1) (`planning/handoffs/PROVE-AUX61-MEAN.md`, "What remains"): work in the
restart chart under the conditional measure `μ₀ = μ[· | S₀]`, `S₀ = {Z ∈ B, 0 < life}` the live event at fibre time
`0`. With `h₀` a chart decomposition at time `0` given `𝒢₀` (`IsChartGaussAt … 0 𝒢₀ h₀`) and `h₁` one at time `q`
given `𝒢 ⊇ 𝒢₀`:

* **`isZeroBoundaryGFF_relField`**: the relative chart field `h' = field − h₀` is a zero-boundary GFF on `ℍ` under
  `μ₀` (at time `0` the chart hull is empty, so its conditional law given `𝒢₀` is the constant zero-boundary law);
* **`isCondZeroBoundaryGFF_relMean`**: given the time-`q` marks enlarged by the field OFF the live event
  (`oldMarks = 𝒢 ∨ σ(1_{S_q^c} h')`), the relative field minus the relative mean
  `relMean = h₁ − h₀` (on `S_q`; `h'` off it) is a conditional zero-boundary GFF on `ℍ ∖ relHull`, `relHull` the
  chart hull on `S_q` and `ℍ` off it. On `S_q` the trace σ-algebras of `𝒢` and `oldMarks` agree, so the conditional
  law is the one of (K-a) at time `q`; off `S_q` both sides are trivial (`zeroGFFTestCov_empty`).

Conditional helpers with distinct names; no source statement is replaced. R48/R77: nothing here uses Theorem 1.2/1.3,
`Theorem12ParamStatement`, `Theorem13Statement`, any `*_of_param`, or Astra's post-contact kernel.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter Topology Complex
open QuantumZipper (H fwdHull zeroGFFTestCov)
open LQGMetric (DistOn TestOn IsZeroBoundaryGFF)
open scoped NNReal ENNReal

namespace InteractingSLE.Sec5.Aux61OldB

open Aux61Fib (FibCode)
open Aux61FibK (codeFiltration)
open Aux61ChLoc (IsChartGaussAt liveEv liveSet liveSet_of_mem liveSet_of_notMem aliveHull measurable_aliveHull
  chartHull_eq_aliveHull measurableSet_live ae_condExp_eq_of_eqOn)
open Aux61UnionK (chartHull measurable_field_apply isOpen_H_diff_chartHull norm_cexp_I_mul_ofReal_le)

universe u

/-! ### Definitions -/

section Defs

variable {X : Type u}

/-- **The relative chart field** `h' = field − h₀`. -/
def relField (Y : X → FibCode) (h₀ : X → DistOn upperHalfPlaneOpens) (x : X) : DistOn upperHalfPlaneOpens :=
  (Y x).field - h₀ x

/-- **The old-boundary marks**: the time-`q` σ-algebra `𝒢` and the relative field off the live event `S`. -/
@[instance_reducible]
def oldMarks (𝒢 : MeasurableSpace X) (S : Set X) (h' : X → DistOn upperHalfPlaneOpens) : MeasurableSpace X :=
  𝒢 ⊔ MeasurableSpace.comap (Sᶜ.indicator h') inferInstance

open scoped Classical in
/-- **The relative mean**: `h₁ − h₀` on the live event `S`, the relative field `h'` off it. -/
def relMean (S : Set X) (h₁ h₀ h' : X → DistOn upperHalfPlaneOpens) : X → DistOn upperHalfPlaneOpens :=
  S.piecewise (fun x => h₁ x - h₀ x) h'

/-- **The relative hull**: the chart hull at time `q` on the live event, `ℍ` off it. -/
def relHull {β : Type*} (Z : X → β) (B : Set β) (Y : X → FibCode) (q : ℝ≥0) : X → Set ℂ :=
  liveSet (liveEv Z B Y q) fun x => aliveHull.{u} q (ULift.up (Y x))

end Defs

/-! ### Basic facts -/

section Basic

variable {X : Type u} {𝒢₀ 𝒢 : MeasurableSpace X} [mX : MeasurableSpace X] {β : Type*} [mβ : MeasurableSpace β]
  {μ : Measure X} {Z : X → β} {B : Set β} {Y : X → FibCode} {q : ℝ≥0}
  {h₁ h₀ : X → DistOn upperHalfPlaneOpens}

omit mX in
theorem relField_apply (Y : X → FibCode) (h₀ : X → DistOn upperHalfPlaneOpens) (x : X)
    (φ : TestOn upperHalfPlaneOpens) : relField Y h₀ x φ = (Y x).field φ - h₀ x φ := rfl

theorem measurable_relField (hY : Measurable Y) (hm : Measurable h₀) : Measurable (relField Y h₀) :=
  LQGMetric.measurable_distOn_iff.2 fun φ =>
    (measurable_field_apply hY φ).sub ((LQGMetric.measurable_distOn_apply φ).comp hm)

omit mX in
/-- The chart hull at fibre time `0` is empty. -/
theorem chartHull_zero (Y : X → FibCode) (x : X) : chartHull Y 0 x = ∅ := by
  simp only [chartHull, NNReal.coe_zero]
  exact QuantumZipper.RS.fwdHull_zero_eq_empty (Aux61MeanId.continuous_chartDriver (Y x))

omit mX mβ in
theorem relHull_of_mem {x : X} (hx : x ∈ liveEv Z B Y q) : relHull Z B Y q x = chartHull Y q x := by
  rw [relHull, liveSet_of_mem hx, chartHull_eq_aliveHull hx.2]

omit mX mβ in
theorem relHull_of_notMem {x : X} (hx : x ∉ liveEv Z B Y q) : relHull Z B Y q x = H := by
  rw [relHull, liveSet_of_notMem hx]

omit mX mβ in
theorem relHull_props (x : X) : relHull Z B Y q x ⊆ H ∧ IsOpen (H \ relHull Z B Y q x) := by
  by_cases hx : x ∈ liveEv Z B Y q
  · rw [relHull_of_mem hx]
    exact ⟨fun _ hz => hz.1, isOpen_H_diff_chartHull Y hx.2⟩
  · rw [relHull_of_notMem hx, Set.sdiff_self]
    exact ⟨subset_rfl, isOpen_empty⟩

omit mX in
/-- The relative hull is hitting-measurable for every σ-algebra containing the history and the raw code at `q`. -/
theorem measurable_relHull {m : MeasurableSpace X} (hZ : mβ.comap Z ≤ m)
    (hYm : (codeFiltration.{u} q).comap (fun x => ULift.up.{u} (Y x)) ≤ m) (hB : MeasurableSet B) :
    Measurable[m, hittingSigma] (relHull Z B Y q) := by
  have hS : MeasurableSet[m] (liveEv Z B Y q) := measurableSet_live hZ hYm hB
  have hA : Measurable[m, hittingSigma] fun x => aliveHull.{u} q (ULift.up (Y x)) :=
    ((measurable_aliveHull q).comp (comap_measurable (fun x => ULift.up.{u} (Y x)))).mono hYm le_rfl
  exact Measurable.piecewise hS hA measurable_const

/-- The bounded phase of a real measurable function is integrable for a finite measure. -/
theorem integrable_cexp {ν : Measure X} [IsFiniteMeasure ν] {F : X → ℝ} (hF : Measurable F) :
    Integrable (fun x => Complex.exp (Complex.I * (F x : ℂ))) ν :=
  Integrable.of_bound (Complex.measurable_exp.comp (measurable_const.mul
    (Complex.measurable_ofReal.comp hF))).aestronglyMeasurable 1
    (Eventually.of_forall fun x => norm_cexp_I_mul_ofReal_le (F x))

/-- An `μ`-almost-sure statement on a measurable event `S` holds `μ[· | S]`-almost surely. -/
theorem ae_cond_of_ae_mem {S : Set X} (hS : MeasurableSet S) {p : X → Prop} (h : ∀ᵐ x ∂μ, x ∈ S → p x) :
    ∀ᵐ x ∂μ[|S], p x := by
  filter_upwards [cond_absolutelyContinuous.ae_le h, ae_cond_mem hS] with x hx hxS
  exact hx hxS

/-- Conversely, a `μ[· | S]`-almost-sure statement holds `μ`-almost surely on `S`. -/
theorem ae_mem_of_ae_cond [IsFiniteMeasure μ] {S : Set X} (hS : MeasurableSet S) {p : X → Prop}
    (h : ∀ᵐ x ∂μ[|S], p x) : ∀ᵐ x ∂μ, x ∈ S → p x := by
  by_cases h0 : μ S = 0
  · exact (measure_eq_zero_iff_ae_notMem.1 h0).mono fun x hx hxS => absurd hxS hx
  · have hc : (μ S)⁻¹ ≠ 0 := ENNReal.inv_ne_zero.2 (measure_ne_top μ S)
    have h' : ∀ᵐ x ∂μ.restrict S, p x := (Measure.absolutelyContinuous_smul hc).ae_le h
    exact (ae_restrict_iff' hS).1 h'

end Basic

/-! ### The relative field and the extended decomposition -/

section Main

variable {X : Type u} {𝒢₀ 𝒢 : MeasurableSpace X} [mX : MeasurableSpace X] {β : Type*} [mβ : MeasurableSpace β]
  {μ : Measure X} {Z : X → β} {B : Set β} {Y : X → FibCode} {q : ℝ≥0}
  {h₁ h₀ : X → DistOn upperHalfPlaneOpens}

omit mX mβ in
theorem measurable_distOn_sub {m : MeasurableSpace X} {f g : X → DistOn upperHalfPlaneOpens} (hf : Measurable[m] f)
    (hg : Measurable[m] g) : Measurable[m] fun x => f x - g x :=
  (@LQGMetric.measurable_distOn_iff upperHalfPlaneOpens X m _).2 fun φ =>
    ((LQGMetric.measurable_distOn_apply φ).comp hf).sub ((LQGMetric.measurable_distOn_apply φ).comp hg)

omit mX mβ in
/-- The live event at time `q` is contained in the live event at time `0`. -/
theorem liveEv_subset_zero : liveEv Z B Y q ⊆ liveEv Z B Y 0 := fun _ hx =>
  ⟨hx.1, lt_of_le_of_lt (by simp) hx.2⟩

/-- **The relative chart field is a zero-boundary GFF under the time-`0` conditional measure.** At fibre time `0` the
chart hull is empty, so (K-a) says that given `𝒢₀` the relative field `field − h₀` has the constant zero-boundary law
on the live event `S₀`; conditioning on `S₀ ∈ 𝒢₀` keeps this, and the tower property forgets `𝒢₀`. -/
theorem isZeroBoundaryGFF_relField [IsFiniteMeasure μ] (hY : Measurable Y) (hB : MeasurableSet B)
    (hG0 : IsChartGaussAt μ Z B Y 0 𝒢₀ h₀) (hS : μ (liveEv Z B Y 0) ≠ 0) :
    IsZeroBoundaryGFF upperHalfPlaneOpens (relField Y h₀) (μ[|liveEv Z B Y 0]) := by
  have := cond_isProbabilityMeasure (μ := μ) hS
  have hS0 : MeasurableSet[𝒢₀] (liveEv Z B Y 0) := measurableSet_live hG0.marksZ hG0.marksY hB
  have hh₀ : Measurable h₀ := hG0.measurable.mono hG0.le le_rfl
  refine isZeroBoundaryGFF_of_isCondZeroBoundaryGFF_H hG0.le (measurable_relField hY hh₀) fun φ => ?_
  have hF : Measurable fun x => (Y x).field φ - h₀ x φ :=
    (measurable_field_apply hY φ).sub ((LQGMetric.measurable_distOn_apply φ).comp hh₀)
  have h1 := Aux61FibK.condExp_cond_ae_eq hG0.le hS0 (integrable_cexp (ν := μ) hF)
  have h2 := ae_cond_of_ae_mem (hG0.le _ hS0) ((hG0.gff φ).mono fun x hx hxS => hx hxS.1 hxS.2)
  filter_upwards [h1, h2] with x hx1 hx2
  rw [chartHull_zero Y x, sdiff_empty] at hx2
  exact hx1.trans hx2

/-- The relative mean is measurable for the old-boundary marks. -/
theorem measurable_relMean (hB : MeasurableSet B) (hG0 : IsChartGaussAt μ Z B Y 0 𝒢₀ h₀)
    (hG : IsChartGaussAt μ Z B Y q 𝒢 h₁) (h𝒢 : 𝒢₀ ≤ 𝒢) :
    Measurable[oldMarks 𝒢 (liveEv Z B Y q) (relField Y h₀)]
      (relMean (liveEv Z B Y q) h₁ h₀ (relField Y h₀)) := by
  classical
  set S := liveEv Z B Y q
  have hS𝒢 : MeasurableSet[𝒢] S := measurableSet_live hG.marksZ hG.marksY hB
  have hd : Measurable[𝒢] fun x => h₁ x - h₀ x := measurable_distOn_sub hG.measurable (hG0.measurable.mono h𝒢 le_rfl)
  have e : relMean S h₁ h₀ (relField Y h₀) = S.piecewise (fun x => h₁ x - h₀ x) (Sᶜ.indicator (relField Y h₀)) := by
    funext x
    by_cases hx : x ∈ S
    · simp only [relMean, piecewise_eq_of_mem _ _ _ hx]
    · simp only [relMean, piecewise_eq_of_notMem _ _ _ hx, indicator_of_mem (mem_compl hx)]
  rw [e]
  exact Measurable.piecewise ((le_sup_left : 𝒢 ≤ oldMarks 𝒢 S (relField Y h₀)) _ hS𝒢)
    (hd.mono le_sup_left le_rfl) ((comap_measurable _).mono le_sup_right le_rfl)

/-- The relative mean is harmonic off the relative hull, almost surely. -/
theorem ae_isHarmonicDistOn_relMean (hG0 : IsChartGaussAt μ Z B Y 0 𝒢₀ h₀) (hG : IsChartGaussAt μ Z B Y q 𝒢 h₁) :
    ∀ᵐ x ∂μ, IsHarmonicDistOn (relMean (liveEv Z B Y q) h₁ h₀ (relField Y h₀) x) (H \ relHull Z B Y q x) := by
  classical
  filter_upwards [hG0.harmonic, hG.harmonic] with x hx0 hx
  by_cases hxS : x ∈ liveEv Z B Y q
  · have hx0' := hx0 hxS.1 (liveEv_subset_zero hxS).2
    rw [chartHull_zero Y x, sdiff_empty] at hx0'
    rw [relMean, piecewise_eq_of_mem _ _ _ hxS, relHull_of_mem hxS]
    exact LocalSets.IsHarmonicDistOn.sub' (isOpen_H_diff_chartHull Y hxS.2) (hx hxS.1 hxS.2)
      (LocalSets.IsHarmonicDistOn.mono hx0' sdiff_subset)
  · rw [relHull_of_notMem hxS, Set.sdiff_self]
    exact Aux61MeanId.isHarmonicDistOn_empty _

/-- **The extended decomposition at fibre time `q` under the time-`0` conditional measure.** Given the old-boundary
marks `𝒢 ∨ σ(1_{S_q^c} h')`, the relative field minus the relative mean is a conditional zero-boundary GFF on
`ℍ ∖ relHull`: on the live event `S_q` this is (K-a) at time `q` (the trace σ-algebras of `𝒢` and of the enlarged marks
agree there, and conditioning on `S₀ ∈ 𝒢` does not change conditional expectations on `S₀`); off `S_q` the field
minus the mean is `0` and the domain is empty. -/
theorem isCondZeroBoundaryGFF_relMean [IsFiniteMeasure μ] (hY : Measurable Y) (hB : MeasurableSet B)
    (hG0 : IsChartGaussAt μ Z B Y 0 𝒢₀ h₀) (hG : IsChartGaussAt μ Z B Y q 𝒢 h₁) (h𝒢 : 𝒢₀ ≤ 𝒢) :
    IsCondZeroBoundaryGFF (μ[|liveEv Z B Y 0]) (oldMarks 𝒢 (liveEv Z B Y q) (relField Y h₀))
      (fun x => H \ relHull Z B Y q x)
      (fun x => relField Y h₀ x - relMean (liveEv Z B Y q) h₁ h₀ (relField Y h₀) x) := by
  classical
  intro φ
  set S₀ := liveEv Z B Y 0 with hS₀def
  set S := liveEv Z B Y q with hSdef
  have hh₀ : Measurable h₀ := hG0.measurable.mono hG0.le le_rfl
  have hh₁ : Measurable h₁ := hG.measurable.mono hG.le le_rfl
  have hh' : Measurable (relField Y h₀) := measurable_relField hY hh₀
  have hS𝒢 : MeasurableSet[𝒢] S := measurableSet_live hG.marksZ hG.marksY hB
  have hS₀𝒢 : MeasurableSet[𝒢] S₀ := h𝒢 _ (measurableSet_live hG0.marksZ hG0.marksY hB)
  have hSm : MeasurableSet S := hG.le _ hS𝒢
  have hS₀m : MeasurableSet S₀ := hG.le _ hS₀𝒢
  have h𝒥 : oldMarks 𝒢 S (relField Y h₀) ≤ mX := sup_le hG.le (hh'.indicator hSm.compl).comap_le
  have hS𝒥 : MeasurableSet[oldMarks 𝒢 S (relField Y h₀)] S :=
    (le_sup_left : 𝒢 ≤ oldMarks 𝒢 S (relField Y h₀)) _ hS𝒢
  by_cases h0 : μ S₀ = 0
  · rw [cond_eq_zero_of_meas_eq_zero h0, EventuallyEq, ae_zero]
    exact eventually_bot
  have := cond_isProbabilityMeasure (μ := μ) h0
  have hgm : Measurable (relMean S h₁ h₀ (relField Y h₀)) :=
    (measurable_relMean hB hG0 hG h𝒢).mono h𝒥 le_rfl
  have hfm : Measurable fun x => (relField Y h₀ x - relMean S h₁ h₀ (relField Y h₀) x) φ :=
    (LQGMetric.measurable_distOn_apply φ).comp (measurable_distOn_sub hh' hgm)
  have hf₁m : Measurable fun x => (Y x).field φ - h₁ x φ :=
    (measurable_field_apply hY φ).sub ((LQGMetric.measurable_distOn_apply φ).comp hh₁)
  have hfS : ∀ x ∈ S, cexp (I * (((relField Y h₀ x - relMean S h₁ h₀ (relField Y h₀) x) φ : ℝ) : ℂ)) =
      cexp (I * (((Y x).field φ - h₁ x φ : ℝ) : ℂ)) := by
    intro x hx
    rw [relMean, piecewise_eq_of_mem _ _ _ hx]
    simp only [relField, sub_apply]
    ring_nf
  have hfSc : ∀ x ∈ Sᶜ, cexp (I * (((relField Y h₀ x - relMean S h₁ h₀ (relField Y h₀) x) φ : ℝ) : ℂ)) =
      (fun _ => (1 : ℂ)) x := by
    intro x hx
    rw [relMean, piecewise_eq_of_notMem _ _ _ hx, sub_self]
    simp
  -- off the live event
  have hoff := ae_condExp_eq_of_eqOn (m := oldMarks 𝒢 S (relField Y h₀)) (μ := μ[|S₀]) hS𝒥.compl
    (integrable_cexp hfm) (integrable_const (1 : ℂ)) hfSc
  -- on the live event
  have hon := ae_condExp_eq_of_eqOn (m := oldMarks 𝒢 S (relField Y h₀)) (μ := μ[|S₀]) hS𝒥
    (integrable_cexp hfm) (integrable_cexp hf₁m) hfS
  have htr : ∀ t, MeasurableSet[𝒢] (S ∩ t) ↔ MeasurableSet[oldMarks 𝒢 S (relField Y h₀)] (S ∩ t) := fun t =>
    ⟨fun h => (le_sup_left : 𝒢 ≤ oldMarks 𝒢 S (relField Y h₀)) _ h, fun h => by
      have := measurableSet_inter_of_sup_comap hS𝒢 (G := Sᶜ.indicator (relField Y h₀)) (c := 0)
        (fun x hx => indicator_of_notMem (notMem_compl_iff.2 hx) _) h
      rwa [← inter_assoc, inter_self] at this⟩
  have hres := (ae_restrict_iff' hSm).1
    (condExp_ae_eq_restrict_of_measurableSpace_eq_on (μ := μ[|S₀])
      (f := fun x => cexp (I * (((Y x).field φ - h₁ x φ : ℝ) : ℂ))) hG.le h𝒥 hS𝒢 htr)
  have hcond := Aux61FibK.condExp_cond_ae_eq hG.le hS₀𝒢 (integrable_cexp (ν := μ) hf₁m)
  have hgff := ae_cond_of_ae_mem hS₀m ((hG.gff φ).mono fun x hx _ => hx)
  filter_upwards [hoff, hon, hres, hcond, hgff] with x hxoff hxon hxres hxcond hxgff
  by_cases hxS : x ∈ S
  · rw [hxon hxS, ← hxres hxS, hxcond, hxgff hxS.1 hxS.2, relHull_of_mem hxS]
  · rw [hxoff hxS, condExp_const h𝒥, relHull_of_notMem hxS, Set.sdiff_self, zeroGFFTestCov_empty]
    simp

end Main

end InteractingSLE.Sec5.Aux61OldB
