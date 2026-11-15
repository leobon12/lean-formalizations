/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW3LawChart
import InteractingSLE.Spec.Jordan.Transport
import InteractingSLE.GFF.PushforwardLaw

/-!
# Lemma GW3's field law for every choice of component charts, from one choice

Packet PROVE-T14-GW5. The named input `GW4.GW3FieldLawStatement` (Lemma GW3, `source/spec/p625-671.md` L204–L225,
p. 636) asserts the component field law "for every choice of component charts `cs`": there are lifts for which the
fields read in the charts are, conditionally on the walks, independent GFFs with the GW3.1 words. This file reduces it
to the law in **one** choice of charts (named input `GW3FieldLawOneChartStatement`), given open components
(`GW3Word.BetweenComponentsOpenStatement`) and no common continuum of the walks (`WalkNoCommonContinuumStatement`;
GW4, proof, p. 637: "An interior common open subarc is impossible … A common original-real interval is also
impossible").

## Proof

* Any other component chart `c` of `C` has `fwd = r fwd₀` on `C`, `inv = inv₀(· / r)` on `ℍ` (`GW3LawChart`,
  `inv_eq_of_isComponentChart`). With the lift `lift₀` it is a component chart (`isComponentChart_lift`: the
  derivatives differ by the positive factor `r`).
* The field read in `(fwd, inv, lift₀)` is the given component field read in the dilation chart `w ↦ r w`
  (`IsChartTransport.trans` for `c₀.trans (dilation r)`, which agrees with `(fwd, inv, lift₀)` on `C`:
  `isChartTransport_congr`).
* Dilation covariance: the field read in the dilation chart is a GFF with the data `x ↦ bC(x/r)` off `r · jumpsC`
  (`isGFFWithBoundaryData_dilation`, by `Chart.isZBGFFProcess_chartTransport` and the bounded harmonic extension
  `u₀(r ·)`); the dilated data are the GW3.1 word of `inv` (`isComponentBoundaryData_dilation`).
* Independence: each new field is a fixed measurable function of the old one (`iIndepFun.comp`).

## Main results

* `gw3FieldLawStatement_of_oneChart` : `GW4.GW3FieldLawStatement` from `GW3Word.BetweenComponentsOpenStatement`,
  `WalkNoCommonContinuumStatement` and `GW3FieldLawOneChartStatement`;
* `componentKernels_of_oneChart` : the frozen component-kernel anchor's conclusion from the geometry, the one-chart
  field law, no common continuum, Lemma GW0's forward implication, the sides of the walks' connectors, GW4's traversal
  core and Theorems 1.2–1.3;
* tools: `isGFFWithBoundaryData_dilation`, `isChartTransport_congr`, `isConformal_of_isComponentChart`,
  `isComponentChart_lift`, `isComponentBoundaryData_dilation`, `isPiecewiseConstant_dilation`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology Metric
open scoped NNReal ENNReal
open QuantumZipper (H Hbar)
open LQGMetric (TestOn DistOn)

universe u

namespace InteractingSLE

namespace Theorem14

namespace GW3Law

/-- The dilation chart's domain is `ℍ`. -/
theorem dilation_dom {r : ℝ} (hr : 0 < r) : (Chart.dilation r).dom = upperHalfPlaneOpens :=
  SetLike.coe_injective ((Chart.isConformal_dilation hr).coe_dom.trans (Chart.dilation_image_H hr))

/-- **Dilation covariance of a GFF with boundary data**: the field read in the dilation chart `w ↦ r w` (lift `0`) is
a GFF with the dilated data `x ↦ g(x/r)` off `r S`. -/
theorem isGFFWithBoundaryData_dilation {r : ℝ} (hr : 0 < r) (k : ℝ) {Ω : Type*} [MeasurableSpace Ω]
    {Q : Measure Ω} {X : Ω → DistOn upperHalfPlaneOpens} {g : ℝ → ℝ} {S : Finset ℝ}
    (hX : IsGFFWithBoundaryData Q X g S) :
    IsGFFWithBoundaryData Q (fun ω => Chart.chartTransport (Chart.isConformal_dilation hr) 1 0 k (X ω))
      (fun x => g (x / r)) (S.image fun y => r * y) := by
  have hc := Chart.isConformal_dilation hr
  have hr0 : (r : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hr.ne'
  refine ⟨(Chart.measurable_chartTransport hc 1 0 k).comp hX.1, fun u₀ hu₀ => ?_⟩
  -- `u₀ (r ·)` is the bounded harmonic extension of `g`
  set u : ℂ → ℝ := fun z => u₀ ((r : ℂ) * z) with hu
  have hmul : MapsTo (fun z : ℂ => (r : ℂ) * z) H H := fun z hz => Chart.dilation_mem_H hr hz
  have hu' : IsBoundedHarmonicExtension g S u := by
    obtain ⟨hharm, ⟨C, hC⟩, hlim⟩ := hu₀
    refine ⟨LQGMetric.harmonicOnNhd_comp_holo QuantumZipper.isOpen_H QuantumZipper.isOpen_H hharm
      ((differentiable_id.const_mul (r : ℂ)).differentiableOn) hmul, ⟨C, fun z hz => hC _ (hmul hz)⟩,
      fun x hx => ?_⟩
    have hrx : r * x ∉ ((S.image fun y => r * y : Finset ℝ) : Set ℝ) := by
      intro hm
      obtain ⟨y, hy, hyx⟩ := Finset.mem_image.1 (Finset.mem_coe.1 hm)
      have : y = x := mul_left_cancel₀ hr.ne' hyx
      exact hx (this ▸ Finset.mem_coe.2 hy)
    have h1 := hlim (r * x) hrx
    have h2 : Tendsto (fun z : ℂ => (r : ℂ) * z) (𝓝[H] (x : ℂ)) (𝓝[H] ((r * x : ℝ) : ℂ)) := by
      refine tendsto_nhdsWithin_iff.2 ⟨?_, eventually_nhdsWithin_of_forall fun z hz => hmul hz⟩
      have hcm : Continuous fun z : ℂ => (r : ℂ) * z := continuous_const.mul continuous_id
      have := (hcm.tendsto (x : ℂ)).mono_left (nhdsWithin_le_nhds (s := H))
      simpa [Complex.ofReal_mul] using this
    have e : r * x / r = x := by field_simp
    simp only [e] at h1
    exact h1.comp h2
  have key : ∀ U : TopologicalSpace.Opens ℂ, U = upperHalfPlaneOpens → LQGMetric.IsZBGFFProcess U
      (fun ψ ω => X ω (GFF.testIncl U upperHalfPlaneOpens ψ) - ∫ z, u z * ψ z) Q := by
    rintro U rfl
    have hid : ∀ ψ : TestOn upperHalfPlaneOpens,
        GFF.testIncl upperHalfPlaneOpens upperHalfPlaneOpens ψ = ψ := fun ψ => by
      ext z
      exact congrFun (GFF.coe_testIncl le_rfl ψ) z
    simp only [hid]
    exact hX.2 u hu'
  have hℓ : LocallyIntegrableOn (fun w => (Chart.dilation r).2.2 ((Chart.dilation r).2.1 w)) H :=
    locallyIntegrableOn_const 0
  have hZ := Chart.isZBGFFProcess_chartTransport hc hℓ (m := u) k (key _ (dilation_dom hr))
  convert hZ using 2 with φ
  funext ω
  have e1 : ∀ w : ℂ, u ((Chart.dilation r).2.1 w) = u₀ w := fun w => by
    simp only [hu, Chart.dilation_inv]
    rw [mul_div_cancel₀ w hr0]
  simp only [e1, Chart.dilation_lift, zero_mul, integral_zero, mul_zero, add_zero]

/-- **A chart transport only sees the chart on its domain**: if `c'` has the inverse of `c` on `ℍ`, and the forward
map and the lift of `c` on an open set `U ⊇ inv '' ℍ`, then a transport in `c` is a transport in `c'`. -/
theorem isChartTransport_congr {c c' : Chart} {U : Set ℂ} (hUo : IsOpen U) (hcU : MapsTo c.2.1 H U)
    (hinv : EqOn c'.2.1 c.2.1 H) (hfwd : EqOn c'.1 c.1 U) (hlift : EqOn c'.2.2 c.2.2 U)
    {σ a k : ℝ} {h h' : DistOn upperHalfPlaneOpens} (ht : IsChartTransport c σ a k h h') :
    IsChartTransport c' σ a k h h' := by
  intro φ φ' hsupp hφ
  have himg : c'.2.1 '' H = c.2.1 '' H := image_congr hinv
  rw [himg] at hsupp hφ
  have hφ' : ∀ z ∈ c.2.1 '' H, φ z = φ' (c.1 z) * ‖deriv c.1 z‖ ^ 2 := by
    intro z hz
    have hzU : z ∈ U := by obtain ⟨w, hw, rfl⟩ := hz; exact hcU hw
    have hev : c'.1 =ᶠ[𝓝 z] c.1 := Filter.eventuallyEq_of_mem (hUo.mem_nhds hzU) hfwd
    rw [hφ z hz, hfwd hzU, hev.deriv_eq]
  have hint : (∫ w, c'.2.2 (c'.2.1 w) * φ' w) = ∫ w, c.2.2 (c.2.1 w) * φ' w := by
    congr 1
    funext w
    by_cases hw : w ∈ H
    · rw [hinv hw, hlift (hcU hw)]
    · have h0 : φ' w = 0 := φ'.zero_on_compl (show w ∈ ((upperHalfPlaneOpens : Set ℂ))ᶜ from hw)
      rw [h0, mul_zero, mul_zero]
  rw [hint]
  exact ht φ φ' hsupp hφ'

/-- A component chart of an open component in `ℍ` is a conformal chart. -/
theorem isConformal_of_isComponentChart {R L C : Set ℂ} {c : Chart} (hc : IsComponentChart R L C c)
    (hCo : IsOpen C) (hCH : C ⊆ H) : c.IsConformal :=
  ⟨GW3Word.differentiableOn_inv_of_isComponentChart hc hCo, fun _ hw => hCH (hc.2.2.1 hw),
    fun _ hw => hc.2.2.2.1.2 hw⟩

/-- **The lift of one component chart serves a dilated one**: if `fwd = r · fwd₀` on the open component, the chart
`(fwd, inv, lift₀)` is a component chart (the derivative arguments agree). -/
theorem isComponentChart_lift {R L C : Set ℂ} {c₀ c : Chart} (hc₀ : IsComponentChart R L C c₀)
    (hc : IsComponentChart R L C c) (hCo : IsOpen C) {r : ℝ} (hr : 0 < r)
    (hfwd : EqOn c.1 (fun z => (r : ℂ) * c₀.1 z) C) : IsComponentChart R L C (c.1, c.2.1, c₀.2.2) := by
  refine ⟨hc.1, hc.2.1, hc.2.2.1, hc.2.2.2.1, hc.2.2.2.2.1, hc₀.2.2.2.2.2.1, fun z hz => ?_⟩
  have hev : c.1 =ᶠ[𝓝 z] (fun z => (r : ℂ) * c₀.1 z) := Filter.eventuallyEq_of_mem (hCo.mem_nhds hz) hfwd
  have hd₀ : DifferentiableAt ℂ c₀.1 z := (hc₀.1 z hz).differentiableAt (hCo.mem_nhds hz)
  have hD : deriv c.1 z = (r : ℂ) * deriv c₀.1 z := by rw [hev.deriv_eq, deriv_const_mul _ hd₀]
  show deriv c.1 z = (‖deriv c.1 z‖ : ℂ) * Complex.exp ((c₀.2.2 z : ℂ) * Complex.I)
  rw [hD, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr]
  have h0 := hc₀.2.2.2.2.2.2 z hz
  push_cast
  rw [mul_assoc, ← h0]

/-- **Dilation of the GW3.1 word**: if `inv = inv₀ (· / r)` on `ℍ`, the word of `inv₀` read at `x / r` is a word of
`inv`. -/
theorem isComponentBoundaryData_dilation {κ : ℝ} {b : ℝ → ℝ} {ordR ordL : Set ℂ} {inv₀ inv : ℂ → ℂ} {r : ℝ}
    (hr : 0 < r) (hinv : ∀ w ∈ H, inv w = inv₀ (w / r)) {bC : ℝ → ℝ} {jumpsC : Finset ℝ}
    (hbd : IsComponentBoundaryData κ b ordR ordL inv₀ bC jumpsC) :
    IsComponentBoundaryData κ b ordR ordL inv (fun x => bC (x / r)) (jumpsC.image fun y => r * y) := by
  intro x hx p hp
  have hr0 : (r : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hr.ne'
  have hx' : x / r ∉ jumpsC := fun hm => hx (Finset.mem_image.2 ⟨x / r, hm, by field_simp⟩)
  have hmul : MapsTo (fun z : ℂ => (r : ℂ) * z) H H := fun z hz => Chart.dilation_mem_H hr hz
  have h2 : Tendsto (fun z : ℂ => (r : ℂ) * z) (𝓝[H] ((x / r : ℝ) : ℂ)) (𝓝[H] (x : ℂ)) := by
    refine tendsto_nhdsWithin_iff.2 ⟨?_, eventually_nhdsWithin_of_forall fun z hz => hmul hz⟩
    have hcm : Continuous fun z : ℂ => (r : ℂ) * z := continuous_const.mul continuous_id
    have := (hcm.tendsto ((x / r : ℝ) : ℂ)).mono_left (nhdsWithin_le_nhds (s := H))
    have e : (r : ℂ) * ((x / r : ℝ) : ℂ) = (x : ℂ) := by push_cast; field_simp
    rwa [e] at this
  have hp' : Tendsto inv₀ (𝓝[H] ((x / r : ℝ) : ℂ)) (𝓝 p) := by
    refine (hp.comp h2).congr' (eventually_nhdsWithin_of_forall fun v hv => ?_)
    simp only [Function.comp_apply]
    rw [hinv _ (hmul hv), mul_div_cancel_left₀ v hr0]
  obtain ⟨h1, h3⟩ := hbd (x / r) hx' p hp'
  exact ⟨fun hx0 => h1 (div_pos hx0 hr), fun hx0 => h3 (div_neg_of_neg_of_pos hx0 hr)⟩

/-- Dilated piecewise-constant data. -/
theorem isPiecewiseConstant_dilation {r : ℝ} (hr : 0 < r) {g : ℝ → ℝ} {J : Finset ℝ}
    (hg : IsPiecewiseConstantBoundaryData g J) :
    IsPiecewiseConstantBoundaryData (fun x => g (x / r)) (J.image fun y => r * y) := by
  intro y hy
  have hy' : y / r ∉ J := fun hm => hy (Finset.mem_image.2 ⟨y / r, hm, by field_simp⟩)
  have hc : Tendsto (fun z : ℝ => z / r) (𝓝 y) (𝓝 (y / r)) := (continuous_id.div_const r).tendsto y
  exact hc.eventually (hg _ hy')

/-! ### Lemma GW3's field law for every choice of charts, from one choice -/

/-- **Named input: Lemma GW3's field law in one choice of component charts** (`GW4.GW3FieldLawStatement` with "for
every choice of component charts `cs`, there are lifts" replaced by "there is a choice of component charts, with
their lifts"; GW3, p. 636: "in a common-lift chart `(C; x_C, y_C) → (ℍ; 0, ∞)`, its conditional flow-oriented
boundary values are (GW3.1) … The zero-boundary fields in the countably many selected components are conditionally
independent"). Binders of `GW4.GW3FieldLawStatement` (verbatim). -/
def GW3FieldLawOneChartStatement : Prop :=
  ∀ κ : ℝ, 0 < κ → κ < 4 → ∀ (b : ℝ → ℝ) (jumps : Finset ℝ), IsPiecewiseConstantBoundaryData b jumps →
    ∀ {Ω : Type u} [MeasurableSpace Ω] [StandardBorelSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
      (h : Ω → LQGMetric.DistOn upperHalfPlaneOpens), IsGFFWithBoundaryData P h b jumps →
    ∀ (W' : ℝ≥0 → Ω → ℝ) (ζ' : Ω → ℝ≥0∞), IsCenteredCounterflowDriver κ P h W' ζ' →
      (∀ᵐ ω ∂P, ζ' ω = ⊤) →
    ∀ E : ExplSpec → ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞,
      (∀ spec : ExplSpec, IsBoundaryContinuedProgram spec.2.2 →
        IsStagedHistory κ b jumps P h spec (E spec)) →
      let wR := boundaryWalkSpec b jumps (-(Real.pi / 2)) true
      let wL := boundaryWalkSpec b jumps (Real.pi / 2) false
      ∀ᵐ ω₀ ∂P,
        let R := ExplState.physSet κ b jumps wR (fun k => E wR k ω₀)
        let L := ExplState.physSet κ b jumps wL (fun k => E wL k ω₀)
        let ν := condExpKernel P
          (pastSigma κ b jumps wR (E wR) wR.2.2.length ⊔ pastSigma κ b jumps wL (E wL) wL.2.2.length) ω₀
        ∃ (cs : Set ℂ → Chart) (hC : Set ℂ → Ω → LQGMetric.DistOn upperHalfPlaneOpens),
          (∀ C ∈ betweenComponents R L,
            IsComponentChart R L C (cs C) ∧
            (∀ ω, IsChartTransport (cs C) 1 0 (QuantumZipper.chiC κ) (h ω) (hC C ω)) ∧
            ∃ (bC : ℝ → ℝ) (jumpsC : Finset ℝ), IsPiecewiseConstantBoundaryData bC jumpsC ∧
              IsComponentBoundaryData κ b (ExplState.ordinarySet κ b jumps wR (fun k => E wR k ω₀))
                (ExplState.ordinarySet κ b jumps wL (fun k => E wL k ω₀)) (cs C).2.1 bC jumpsC ∧
              IsGFFWithBoundaryData ν (hC C) bC jumpsC) ∧
          iIndepFun (fun (C : betweenComponents R L) ω => hC C ω) ν

/-- **Named input: the walks share no nondegenerate connected set** (Theorem GW4, proof, p. 637: "An interior common
open subarc is impossible … A common original-real interval is also impossible"; the walks are simple curves, Lemma
GW1, so a common continuum would be a common subarc). Binders of `GW3.GW3GeometryStatement`: almost surely every
connected subset of `R ∩ L` is at most a point. -/
def WalkNoCommonContinuumStatement : Prop :=
  ∀ κ : ℝ, 0 < κ → κ < 4 → ∀ (b : ℝ → ℝ) (jumps : Finset ℝ), IsPiecewiseConstantBoundaryData b jumps →
    ∀ {Ω : Type u} [MeasurableSpace Ω] [StandardBorelSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
      (h : Ω → LQGMetric.DistOn upperHalfPlaneOpens), IsGFFWithBoundaryData P h b jumps →
    ∀ (W' : ℝ≥0 → Ω → ℝ) (ζ' : Ω → ℝ≥0∞), IsCenteredCounterflowDriver κ P h W' ζ' →
      (∀ᵐ ω ∂P, ζ' ω = ⊤) →
    ∀ E : ExplSpec → ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞,
      (∀ spec : ExplSpec, IsBoundaryContinuedProgram spec.2.2 →
        IsStagedHistory κ b jumps P h spec (E spec)) →
      ∀ᵐ ω₀ ∂P,
        ∀ S ⊆ ExplState.physSet κ b jumps (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)
              (fun k => E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) k ω₀) ∩
            ExplState.physSet κ b jumps (boundaryWalkSpec b jumps (Real.pi / 2) false)
              (fun k => E (boundaryWalkSpec b jumps (Real.pi / 2) false) k ω₀),
          IsPreconnected S → S.Subsingleton

/-- **Lemma GW3's field law for every choice of component charts** (`GW4.GW3FieldLawStatement`), from the law in one
choice of charts, open components and no common continuum of the walks. Any other chart of a component is
`fwd = r fwd₀` (`exists_dilation_of_isComponentChart`); with the lift of the given chart it is a component chart
(`isComponentChart_lift`), the field read in it is the given component field read in the dilation chart
(`IsChartTransport.trans`, `isChartTransport_congr`), which is a GFF with the dilated GW3.1 word
(`isGFFWithBoundaryData_dilation`, `isComponentBoundaryData_dilation`), and independence is preserved (each new field
is a measurable function of the old one). -/
theorem gw3FieldLawStatement_of_oneChart (hO : GW3Word.BetweenComponentsOpenStatement.{u})
    (hN : WalkNoCommonContinuumStatement.{u}) (h1 : GW3FieldLawOneChartStatement.{u}) :
    GW4.GW3FieldLawStatement.{u} := by
  intro κ hκ hκ4 b jumps hb Ω _ _ P _ h hh W' ζ' hcf hζ' E hE wR wL
  filter_upwards [hO κ hκ hκ4 b jumps hb P h hh W' ζ' hcf hζ' E hE,
    hN κ hκ hκ4 b jumps hb P h hh W' ζ' hcf hζ' E hE,
    h1 κ hκ hκ4 b jumps hb P h hh W' ζ' hcf hζ' E hE] with ω₀ hOω hNω h1ω
  intro R L ν cs hcs
  obtain ⟨cs₀, hC₀, hC₀p, hind⟩ := h1ω
  have hCH : ∀ C ∈ betweenComponents R L, C ⊆ H := by
    rintro C ⟨z, -, -, -, rfl⟩
    exact (connectedComponentIn_subset _ _).trans sdiff_subset
  have hdil : ∀ C ∈ betweenComponents R L, ∃ r : ℝ, 0 < r ∧ (∀ w ∈ H, (cs C).1 ((cs₀ C).2.1 w) = (r : ℂ) * w) ∧
      ∀ w ∈ H, (cs C).2.1 w = (cs₀ C).2.1 (w / r) := fun C hC =>
    inv_eq_of_isComponentChart (hC₀p C hC).1 (hcs C hC) (hOω C hC) hNω
  choose! r hr hfwd hinv using hdil
  set χ := QuantumZipper.chiC κ with hχ
  set T : Set ℂ → LQGMetric.DistOn upperHalfPlaneOpens → LQGMetric.DistOn upperHalfPlaneOpens := fun C x =>
    if hrC : 0 < r C then Chart.chartTransport (Chart.isConformal_dilation hrC) 1 0 χ x else x with hT
  have hTm : ∀ C, Measurable (T C) := fun C => by
    by_cases hrC : 0 < r C
    · simp only [hT, hrC, ↓reduceDIte]; exact Chart.measurable_chartTransport _ 1 0 χ
    · simp only [hT, hrC, ↓reduceDIte]; exact measurable_id
  refine ⟨fun C => (cs₀ C).2.2, fun C ω => T C (hC₀ C ω), fun C hC => ?_, ?_⟩
  · obtain ⟨hch₀, htr₀, bC, jumpsC, hpc, hbd, hgff⟩ := hC₀p C hC
    have hCo := hOω C hC
    have hrC := hr C hC
    have hTC : T C = Chart.chartTransport (Chart.isConformal_dilation hrC) 1 0 χ := by
      funext x; simp only [hT, hrC, ↓reduceDIte]
    -- the forward maps differ by the dilation on `C`
    have hfwdC : EqOn (cs C).1 (fun z => (r C : ℂ) * (cs₀ C).1 z) C := by
      intro z hz
      have hw : (cs₀ C).1 z ∈ H := hch₀.2.1 hz
      have := hfwd C hC _ hw
      rwa [hch₀.2.2.2.1.1 hz] at this
    have hc₀ := isConformal_of_isComponentChart hch₀ hCo (hCH C hC)
    have hcD := Chart.isConformal_dilation hrC
    have hℓ₀ : ContinuousOn (fun w => (cs₀ C).2.2 ((cs₀ C).2.1 w)) H :=
      hch₀.2.2.2.2.2.1.comp hc₀.1.continuousOn hch₀.2.2.1
    have hℓD : ContinuousOn (fun w => (Chart.dilation (r C)).2.2 ((Chart.dilation (r C)).2.1 w)) H :=
      continuousOn_const
    refine ⟨isComponentChart_lift hch₀ (hcs C hC) hCo hrC hfwdC, fun ω => ?_, ?_⟩
    · -- the field read in the new chart
      have ht₂ := Chart.isChartTransport_chartTransport hcD (Chart.locallyIntegrableOn_of_continuousOn hℓD) 1 0 χ
        (hC₀ C ω)
      have ht := IsChartTransport.trans hc₀ hcD hℓ₀ hℓD (htr₀ ω) ht₂
      show IsChartTransport ((cs C).1, (cs C).2.1, (cs₀ C).2.2) 1 0 χ (h ω) (T C (hC₀ C ω))
      rw [hTC]
      refine isChartTransport_congr (c := (cs₀ C).trans (Chart.dilation (r C)))
        (c' := ((cs C).1, (cs C).2.1, (cs₀ C).2.2)) hCo
        (fun w hw => hch₀.2.2.1 (Chart.div_mem_H hrC hw)) (fun w hw => hinv C hC w hw)
        (fun z hz => hfwdC hz) (fun z _ => ?_) ht
      simp only [Chart.trans_lift, Chart.dilation_lift, zero_add]
    · refine ⟨fun x => bC (x / r C), jumpsC.image fun y => r C * y, isPiecewiseConstant_dilation hrC hpc,
        isComponentBoundaryData_dilation hrC (hinv C hC) hbd, ?_⟩
      show IsGFFWithBoundaryData ν (fun ω => T C (hC₀ C ω)) _ _
      rw [show (fun ω => T C (hC₀ C ω)) = fun ω => Chart.chartTransport hcD 1 0 χ (hC₀ C ω) from by rw [hTC]]
      exact_mod_cast isGFFWithBoundaryData_dilation hrC χ hgff
  · exact hind.comp (fun C => T C.1) fun C => hTm C.1

/-- **Theorem 1.4, component kernels** (Specification p. 5), with exactly the binders and conclusion of the frozen
`IsCenteredCounterflowDriver.componentKernels`, from the between-region geometry, GW3's field law in one choice of
component charts, no common continuum of the walks, Lemma GW0's forward implication, the sides of the walks' real
connectors, GW4's traversal core and Theorems 1.2–1.3. -/
theorem componentKernels_of_oneChart (hG : GW3.GW3GeometryStatement.{u}) (hF1 : GW3FieldLawOneChartStatement.{u})
    (hN : WalkNoCommonContinuumStatement.{u}) (hGW0 : GW0.GW0ForwardStatement.{u})
    (hS : GW3Word.WalkConnectorSideStatement.{u})
    (hT : GW4.GW4TraversalCoreStatement.{u}) (h12 : Exist.Theorem12Statement.{u})
    (h13 : Exist.Theorem13Statement.{u})
    {κ : ℝ} (hκ : 0 < κ) (hκ4 : κ < 4)
    (b : ℝ → ℝ) (jumps : Finset ℝ) (hb : IsPiecewiseConstantBoundaryData b jumps)
    {Ω : Type u} [MeasurableSpace Ω] [StandardBorelSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {h : Ω → LQGMetric.DistOn upperHalfPlaneOpens} (hh : IsGFFWithBoundaryData P h b jumps)
    {W' : ℝ≥0 → Ω → ℝ} {ζ' : Ω → ℝ≥0∞}
    (hcf : IsCenteredCounterflowDriver κ P h W' ζ') (hζ' : ∀ᵐ ω ∂P, ζ' ω = ⊤)
    (E : ExplSpec → ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞)
    (hE : ∀ spec : ExplSpec, IsBoundaryContinuedProgram spec.2.2 →
      IsStagedHistory κ b jumps P h spec (E spec)) :
    let wR := boundaryWalkSpec b jumps (-(Real.pi / 2)) true
    let wL := boundaryWalkSpec b jumps (Real.pi / 2) false
    ∀ᵐ ω₀ ∂P,
      let R := ExplState.physSet κ b jumps wR (fun k => E wR k ω₀)
      let L := ExplState.physSet κ b jumps wL (fun k => E wL k ω₀)
      let ν := condExpKernel P
        (pastSigma κ b jumps wR (E wR) wR.2.2.length ⊔ pastSigma κ b jumps wL (E wL) wL.2.2.length) ω₀
      (∀ C ∈ betweenComponents R L, ∃ c : Chart, IsComponentChart R L C c) ∧
      ∀ cs : Set ℂ → Chart, (∀ C ∈ betweenComponents R L, IsComponentChart R L C (cs C)) →
        ∃ (ℓ : Set ℂ → ℂ → ℝ) (hC : Set ℂ → Ω → LQGMetric.DistOn upperHalfPlaneOpens)
          (WC : Set ℂ → ℝ≥0 → Ω → ℝ) (ζC : Set ℂ → Ω → ℝ≥0∞),
          (∀ C ∈ betweenComponents R L,
            IsComponentChart R L C ((cs C).1, (cs C).2.1, ℓ C) ∧
            (∀ ω, IsChartTransport ((cs C).1, (cs C).2.1, ℓ C) 1 0 (QuantumZipper.chiC κ) (h ω)
              (hC C ω)) ∧
            (∃ (bC : ℝ → ℝ) (jumpsC : Finset ℝ), IsPiecewiseConstantBoundaryData bC jumpsC ∧
              IsComponentBoundaryData κ b (ExplState.ordinarySet κ b jumps wR (fun k => E wR k ω₀))
                (ExplState.ordinarySet κ b jumps wL (fun k => E wL k ω₀)) (cs C).2.1 bC jumpsC ∧
              IsGFFWithBoundaryData ν (hC C) bC jumpsC) ∧
            IsCenteredCounterflowDriver κ ν (hC C) (WC C) (ζC C) ∧
            ∀ᵐ ω ∂ν, ζC C ω = ⊤ ∧
              IsComponentTraversal (cs C).2.1 (fun t => W' t ω) (fun t => WC C t ω)) ∧
          iIndepFun (fun (C : betweenComponents R L) ω => (hC C ω, fun t => WC C t ω)) ν :=
  GW3Word.componentKernels_of_gw3Inputs hG
    (gw3FieldLawStatement_of_oneChart (GW3Word.betweenComponentsOpenStatement_of_geometry hG) hN hF1) hGW0 hS hT h12
    h13 hκ hκ4 b jumps hb hh hcf hζ' E hE

end GW3Law

end Theorem14

end InteractingSLE
