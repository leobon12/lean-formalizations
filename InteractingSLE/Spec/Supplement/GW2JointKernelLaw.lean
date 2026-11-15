/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW2JointKernel
import InteractingSLE.Spec.Supplement.GB6Meas
import InteractingSLE.Spec.Sec7.Aux122Disint

/-!
# GW2's tip exhaustion: the law of the next piece in the joint chart, from the pre-contact kernel

Packet PROVE-T14-TIP9. Follow-up note A.4 (ruling R53): "The actual piece is identified through the outer buffer by the
precontact kernel". This file turns the (R1)/(Det) form of the pre-contact kernel (`GW2JointKernelStatement`) into
the form in which follow-up note A.3 uses it: **under the regular conditional law given the retained counterflow
history, the field read in the joint chart is the GFF of the conditional word `β`, and the decoded canonical driver is
that word's flow-line driver**; by (Det) it generates the joint-chart images of the actual flow hulls before the first
contact. So every event of the relative driver before the first contact has, conditionally on the retained history, the
probability it has for the canonical flow line of the word `β` (whose driving process is the integrated evolution of
the word's flow-line force word, `IsFlowLineDriver`).

## Main results

* `ae_map_condExpKernel_eq_gffLaw`: (R1) on an event `M` makes the regular conditional law of the field the word's GFF
  law (`BoundaryWord.gffLaw`) at almost every point of `M`;
* `ae_map_condExpKernel_pair_eq`: the pair (field, canonical code) has, under the regular conditional law, the law of
  `(H, F (β ω₀, H))` with `H` the word's GFF;
* `isFlowLineDriver_gffLaw`: for a sorted word `c` and a canonical driver code `F` that is good for almost every sample
  of the word's GFF, the decoded code is a flow-line driver of `c` under the GFF law (the canonical flow line of `c`);
* **`exists_condExpKernel_jointFlowLine`**: the pre-contact kernel in conditional-law form.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped NNReal ENNReal
open QuantumZipper (H)

universe u

namespace InteractingSLE

namespace Theorem14

namespace GW2JointKernel

open Restart Sec2.Assembly LQGMetric Supp8.GB6

/-! ### The regular conditional law of a field with Gaussian conditional characteristic functional -/

section Law

variable {Ω : Type*} {𝒢 : MeasurableSpace Ω} [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω] {P : Measure Ω}
  [IsProbabilityMeasure P]

/-- **(R1) gives the regular conditional law of the field.** If, on the event `M`, `E[exp(i (Y, φ)) | 𝒢] = gaussCF
(β ω) φ` for every test function `φ`, then at almost every `ω₀ ∈ M` the regular conditional law of `Y` given `𝒢` is the
GFF law of the word `β ω₀`. -/
theorem ae_map_condExpKernel_eq_gffLaw (h𝒢 : 𝒢 ≤ mΩ) {M : Set Ω} {β : Ω → BoundaryWord}
    {Y : Ω → DistOn upperHalfPlaneOpens} (hY : Measurable Y)
    (hG : ∀ φ : TestOn upperHalfPlaneOpens, ∀ᵐ ω ∂P, ω ∈ M →
      P[fun ω' => Complex.exp (Complex.I * (Y ω' φ : ℂ)) | 𝒢] ω = gaussCF (β ω) φ) :
    ∀ᵐ ω₀ ∂P, ω₀ ∈ M → (condExpKernel P 𝒢 ω₀).map Y = (β ω₀).gffLaw := by
  have hk : ∀ k : RatComb, ∀ᵐ ω₀ ∂P, ω₀ ∈ M →
      ∫ ω, Complex.exp (Complex.I * (Y ω (ratComb upperHalfPlaneOpens k) : ℂ)) ∂(condExpKernel P 𝒢 ω₀) =
        gaussCF (β ω₀) (ratComb upperHalfPlaneOpens k) := by
    intro k
    filter_upwards [hG (ratComb upperHalfPlaneOpens k), condExp_ae_eq_integral_condExpKernel h𝒢
      (GFF.integrable_exp_I_mul (P := P) ((measurable_distOn_apply (ratComb upperHalfPlaneOpens k)).comp hY))]
      with ω₀ h1 h2 hM
    exact h2.symm.trans (h1 hM)
  filter_upwards [ae_all_iff.2 hk] with ω₀ hk' hM
  refine ext_of_integral_cexp_ratComb fun k => ?_
  rw [integral_map hY.aemeasurable (GFF.measurable_exp_I_mul (measurable_distOn_apply _)).aestronglyMeasurable,
    hk' k hM, gaussCF_eq_integral]

/-- **The pair (field, canonical code) under the regular conditional law.** With `β` measurable for `𝒢`, at almost
every `ω₀ ∈ M` the regular conditional law of `(Y, F (β, Y))` given `𝒢` is the law of `(H, F (β ω₀, H))` with `H` the
GFF of the word `β ω₀`. -/
theorem ae_map_condExpKernel_pair_eq (h𝒢 : 𝒢 ≤ mΩ) {M : Set Ω} {β : Ω → BoundaryWord} (hβ : Measurable[𝒢] β)
    {Y : Ω → DistOn upperHalfPlaneOpens} (hY : Measurable Y)
    (hG : ∀ φ : TestOn upperHalfPlaneOpens, ∀ᵐ ω ∂P, ω ∈ M →
      P[fun ω' => Complex.exp (Complex.I * (Y ω' φ : ℂ)) | 𝒢] ω = gaussCF (β ω) φ)
    {E : Type*} [MeasurableSpace E] {F : BoundaryWord × DistOn upperHalfPlaneOpens → E} (hF : Measurable F) :
    ∀ᵐ ω₀ ∂P, ω₀ ∈ M → (condExpKernel P 𝒢 ω₀).map (fun ω => (Y ω, F (β ω, Y ω))) =
      (β ω₀).gffLaw.map (fun g => (g, F (β ω₀, g))) := by
  filter_upwards [ae_map_condExpKernel_eq_gffLaw h𝒢 hY hG, Sec7.Aux122Disint.ae_ae_condExpKernel_eq h𝒢 hβ]
    with ω₀ hmap hβeq hM
  have hβm : Measurable β := hβ.mono h𝒢 le_rfl
  have hg : Measurable fun g : DistOn upperHalfPlaneOpens => (g, F (β ω₀, g)) :=
    measurable_id.prodMk (hF.comp (measurable_const.prodMk measurable_id))
  have hcongr : (condExpKernel P 𝒢 ω₀).map (fun ω => (Y ω, F (β ω, Y ω))) =
      (condExpKernel P 𝒢 ω₀).map (fun ω => (Y ω, F (β ω₀, Y ω))) := by
    refine Measure.map_congr ?_
    filter_upwards [hβeq] with ω hω
    rw [hω]
  rw [hcongr, ← hmap hM, Measure.map_map hg hY]
  rfl

end Law

/-! ### The canonical flow line of a word -/

/-- **The decoded canonical driver code is the flow-line driver of the word's GFF.** For a sorted word `c` and a
canonical driver code `F` at angle `θ` that is good for almost every sample of the GFF of `c`, the decoded code
`drvDec (F (c, ·))` is, under the GFF law of `c`, a flow-line driver of `c` with lifetime the code's lifetime. -/
theorem isFlowLineDriver_gffLaw {κ θ : ℝ} {F : BoundaryWord × DistOn upperHalfPlaneOpens → PCode × ℝ≥0∞}
    (hF : IsCanonicalDriverCode κ θ F) {c : BoundaryWord} (hc : c.IsSorted)
    (hgood : ∀ᵐ g ∂c.gffLaw, IsGoodDrvCode (F (c, g))) :
    IsFlowLineDriver κ c.fn c.jumps θ c.gffLaw id (fun t g => drvDec (F (c, g)) t) (fun g => (F (c, g)).2) := by
  have hFc : Measurable fun g : DistOn upperHalfPlaneOpens => F (c, g) :=
    hF.1.comp (measurable_const.prodMk measurable_id)
  refine hF.2.1 c hc c.gffLaw id _ _ (c.isGFFWithBoundaryData_gffLaw hc)
    (fun t => (measurable_drvDec t).comp hFc) (measurable_snd.comp hFc) (fun g => continuousOn_drvDec _) ?_
  filter_upwards [hgood] with g hg
  exact isDriverCodeMatch_drvDec hg

/-- **The canonical flow line of a word is an integrated evolution of its flow-line force word** (the form consumed by
the driver-level crossing estimates of follow-up note A.3, `Theorem14.CS3Cross.exists_lt_measure_reachEvent_left` and
`Theorem14.GW2TipNear.exists_buffer_eventually_lt_left`): under the GFF law of a sorted word `c`, the decoded canonical
driver code at angle `θ` drives an integrated `SLE_κ(ρ)` evolution of the flow-line word of `c` at angle `θ`
(positions `flowLineXL/XR c.fn c.jumps 0`, weights `flowLineRhoL/RhoR κ c.fn c.jumps 0 θ`), with lifetime the code's
lifetime. -/
theorem exists_isIntegratedSLEEvolution_gffLaw {κ θ : ℝ}
    {F : BoundaryWord × DistOn upperHalfPlaneOpens → PCode × ℝ≥0∞} (hF : IsCanonicalDriverCode κ θ F)
    {c : BoundaryWord} (hc : c.IsSorted) (hgood : ∀ᵐ g ∂c.gffLaw, IsGoodDrvCode (F (c, g))) :
    ∃ (𝓕 : Filtration ℝ≥0 (inferInstance : MeasurableSpace (DistOn upperHalfPlaneOpens)))
      (VL : Fin (flowLineNL c.fn c.jumps 0) → ℝ≥0 → DistOn upperHalfPlaneOpens → ℝ)
      (VR : Fin (flowLineNR c.fn c.jumps 0) → ℝ≥0 → DistOn upperHalfPlaneOpens → ℝ)
      (B : ℝ≥0 → DistOn upperHalfPlaneOpens → ℝ),
      IsIntegratedSLEEvolution κ (flowLineXL c.fn c.jumps 0) (flowLineXR c.fn c.jumps 0)
        (flowLineRhoL κ c.fn c.jumps 0 θ) (flowLineRhoR κ c.fn c.jumps 0 θ) c.gffLaw 𝓕
        (fun t g => drvDec (F (c, g)) t) VL VR B (fun g => (F (c, g)).2) := by
  obtain ⟨_h', 𝓕, VL, VR, B, -, hC⟩ := isFlowLineDriver_gffLaw hF hc hgood
  exact ⟨𝓕, VL, VR, B, hC.1⟩

/-! ### The pre-contact kernel in conditional-law form -/

/-- **The pre-contact kernel at a counterflow stop, conditional-law form** (follow-up note A.4: "The actual piece is
identified through the outer buffer by the precontact kernel"). From `GW2JointKernelStatement` (binders verbatim, on a
standard Borel space): there are a sub-σ-algebra `𝒢` (the retained counterflow history), a `𝒢`-event `M` and a
`𝒢`-measurable sorted word `β` such that

* at almost every `ω₀ ∈ M`, under the regular conditional law given `𝒢`, the pair (joint-chart field, canonical code)
  has the law of `(H, F (β ω₀, H))` with `H` the GFF of the word `β ω₀`, under which the decoded code is the
  flow-line driver of `β ω₀` at angle `θ` (`isFlowLineDriver_gffLaw`);
* almost surely on `{γ(s) ∈ ℍ}`: `ω ∈ M`, and before the flow's first contact with the physical counterflow prefix the
  decoded code generates the joint-chart images of the physical flow hulls in the relative clock. -/
theorem exists_condExpKernel_jointFlowLine (hD : GW2JointKernelStatement.{u}) {κ θ : ℝ} (hκ : 0 < κ)
    (hκ4 : κ < 4) (hθ₁ : -(Real.pi / 2) ≤ θ) (hθ₂ : θ ≤ Real.pi / 2) {Ω : Type u} [mΩ : MeasurableSpace Ω]
    [StandardBorelSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P] {h : Ω → LQGMetric.DistOn upperHalfPlaneOpens}
    {b : ℝ → ℝ} {J : Finset ℝ} {W Wα : ℝ≥0 → Ω → ℝ} {ζ ζα : Ω → ℝ≥0∞} {γ α : Ω → ℝ≥0 → ℂ} {b' : ℝ → ℝ}
    {J' : Finset ℝ} {h' : Ω → LQGMetric.DistOn upperHalfPlaneOpens}
    (hb : IsPiecewiseConstantBoundaryData b J) (hG : IsGFFWithBoundaryData P h b J)
    (hb' : IsPiecewiseConstantBoundaryData b' J')
    (htr : ∀ ω, IsChartTransport infinitySourceChart (-1) (-(Real.pi * QuantumZipper.chiC κ))
      (QuantumZipper.chiC (16 / κ)) (h ω) (h' ω))
    (hcf : IsFlowLineDriver (16 / κ) b' J' 0 P h' W ζ)
    (hadmL : ∀ i : Fin (flowLineNL b' J' 0),
      -2 < ∑ l ∈ Finset.univ.filter (fun l => l ≤ i), flowLineRhoL (16 / κ) b' J' 0 0 l)
    (hadmR : ∀ i : Fin (flowLineNR b' J' 0),
      -2 < ∑ l ∈ Finset.univ.filter (fun l => l ≤ i), flowLineRhoR (16 / κ) b' J' 0 0 l)
    (hcomp : ∀ᵐ ω ∂P, ζ ω = ⊤ ∧ IsGeneratingTrace (fun t => W t ω) ⊤ (γ ω) ∧
      Tendsto (fun t => ‖γ ω t‖) atTop atTop)
    (hfl : IsFlowLineDriver κ b J θ P h Wα ζα)
    (hα : ∀ᵐ ω ∂P, IsGeneratingTrace (fun t => Wα t ω) (ζα ω) (α ω)) (s : ℝ≥0)
    {Hc : Ω → LQGMetric.DistOn upperHalfPlaneOpens} (hHcm : Measurable Hc)
    (hHc : ∀ᵐ ω ∂P, γ ω s ∈ H →
      IsChartTransport (jointChart (fun r : ℝ => W r.toNNReal ω) s) 1 0 (QuantumZipper.chiC κ) (h ω) (Hc ω))
    {F : BoundaryWord × LQGMetric.DistOn upperHalfPlaneOpens → PCode × ℝ≥0∞} (hF : IsCanonicalDriverCode κ θ F) :
    ∃ (𝒢 : {m : MeasurableSpace Ω // m ≤ mΩ}) (M : Set Ω) (β : Ω → BoundaryWord),
      MeasurableSet[𝒢.1] M ∧ Measurable[𝒢.1] β ∧
      (∀ᵐ ω₀ ∂P, ω₀ ∈ M → (β ω₀).IsSorted ∧
        (condExpKernel P 𝒢.1 ω₀).map (fun ω => (Hc ω, F (β ω, Hc ω))) =
          (β ω₀).gffLaw.map (fun g => (g, F (β ω₀, g))) ∧
        IsFlowLineDriver κ (β ω₀).fn (β ω₀).jumps θ (β ω₀).gffLaw id
          (fun t g => drvDec (F (β ω₀, g)) t) (fun g => (F (β ω₀, g)).2)) ∧
      ∀ᵐ ω ∂P, γ ω s ∈ H →
        ω ∈ M ∧
        ∀ t : ℝ≥0, (t : ℝ≥0∞) < firstContactTime (fun t => (α ω t : OnePoint ℂ))
            ((fun r => sphereInv (γ ω r : OnePoint ℂ)) '' Icc 0 s) →
          QuantumZipper.fwdHull (fun r : ℝ => drvDec (F (β ω, Hc ω)) r.toNNReal)
              (relClock (fun r : ℝ => W r.toNNReal ω) s (fun r : ℝ => Wα r.toNNReal ω) t) =
            relMap (fun r : ℝ => W r.toNNReal ω) s '' QuantumZipper.fwdHull (fun r : ℝ => Wα r.toNNReal ω) t := by
  obtain ⟨𝒢, M, β, hM, hβ, hword, hR1, hdet⟩ :=
    hD κ θ hκ hκ4 hθ₁ hθ₂ Ω mΩ P inferInstance h b J W Wα ζ ζα γ α b' J' h' hb hG hb' htr hcf hadmL hadmR hcomp
      hfl hα s Hc hHcm hHc F hF
  refine ⟨𝒢, M, β, hM, hβ, ?_, hdet⟩
  have hβm : Measurable β := hβ.mono 𝒢.2 le_rfl
  have hpair := ae_map_condExpKernel_pair_eq (P := P) 𝒢.2 hβ hHcm hR1 hF.1
  -- the sorted word and the good code, carried to almost every conditional law
  have hgoodK : ∀ᵐ ω₀ ∂P, ∀ᵐ ω ∂(condExpKernel P 𝒢.1 ω₀), ω ∈ M → (β ω).IsSorted ∧
      IsGoodDrvCode (F (β ω, Hc ω)) :=
    Sec7.Aux122Disint.ae_ae_condExpKernel 𝒢.2 hword
  filter_upwards [hpair, hgoodK, Sec7.Aux122Disint.ae_ae_condExpKernel_mem 𝒢.2 hM,
    Sec7.Aux122Disint.ae_ae_condExpKernel_eq 𝒢.2 hβ, hword] with ω₀ hp hgω₀ hMω₀ hβeq hw₀ hω₀M
  have hsort : (β ω₀).IsSorted := (hw₀ hω₀M).1
  refine ⟨hsort, hp hω₀M, isFlowLineDriver_gffLaw hF hsort ?_⟩
  -- the good code under the word's GFF law, pushed forward from the conditional law
  have hFc : Measurable fun g : DistOn upperHalfPlaneOpens => F (β ω₀, g) :=
    hF.1.comp (measurable_const.prodMk measurable_id)
  have hmeas : MeasurableSet {g : DistOn upperHalfPlaneOpens | IsGoodDrvCode (F (β ω₀, g))} :=
    hFc measurableSet_isGoodDrvCode
  have hmap : (condExpKernel P 𝒢.1 ω₀).map Hc = (β ω₀).gffLaw := by
    have h1 : ((condExpKernel P 𝒢.1 ω₀).map (fun ω => (Hc ω, F (β ω, Hc ω)))).map Prod.fst =
        ((β ω₀).gffLaw.map (fun g => (g, F (β ω₀, g)))).map Prod.fst := by
      rw [hp hω₀M]
    have hm1 : Measurable fun ω => (Hc ω, F (β ω, Hc ω)) := hHcm.prodMk (hF.1.comp (hβm.prodMk hHcm))
    have hm2 : Measurable fun g : DistOn upperHalfPlaneOpens => (g, F (β ω₀, g)) := measurable_id.prodMk hFc
    rw [Measure.map_map measurable_fst hm1, Measure.map_map measurable_fst hm2] at h1
    have e1 : (Prod.fst ∘ fun ω => (Hc ω, F (β ω, Hc ω))) = Hc := rfl
    have e2 : (Prod.fst ∘ fun g : DistOn upperHalfPlaneOpens => (g, F (β ω₀, g))) = id := rfl
    rw [e1, e2, Measure.map_id] at h1
    exact h1
  rw [← hmap, ae_map_iff hHcm.aemeasurable hmeas]
  filter_upwards [hgω₀, hMω₀ hω₀M, hβeq] with ω hω hωM hωβ
  have h2 := (hω hωM).2
  rwa [hωβ] at h2

end GW2JointKernel

end Theorem14

end InteractingSLE
