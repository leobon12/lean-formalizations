/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.KernelTower2
import InteractingSLE.Spec.Exist.StagedLawKernel
import InteractingSLE.Spec.Supplement.GB6RestartProof

/-!
# GB6's conditional law given an arbitrary measurable version of the flow prefix record

Packet PROVE-T14-BR (for `Theorem14.GW2Later.GB6PrefixPairStatement`). PROVE-GB6-RESTART proved (R1) of GB6's step (d)
for the σ-algebra of the regularized record `gb6Rec` (`Supp8.GB6.gb6_condDet_r1`). `GB6PrefixPairStatement`
conditions on the σ-algebra of an arbitrary measurable version `g` of the raw record `recOf s (Wα, ζα)`. The two
records agree on the interior-tip event `{gb6Rec ∈ gb6TS s}` (and the event is the same for both), but not off it.

* `ae_condExp_eq_on_of_ae_eq`: conditional expectations given two random elements that agree almost surely on the
  event where one of them lies in a fixed measurable set `T` (and that event is almost surely the same for both)
  agree almost surely on the event (`T` must miss some point `r₀`).
* **`ae_isGFF_condExpKernel_prefix`**: for almost every sample whose record lies in `gb6TS s`, under the regular
  conditional law given `σ(g)`, the chart field is a GFF with the conditional word `gb6WordOfRec κ θ c (g ω₀)`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open LQGMetric (DistOn TestOn)
open QuantumZipper (H)
open scoped NNReal ENNReal

universe u

namespace InteractingSLE

namespace Theorem14

namespace BRLeaf

section Restrict

variable {Ω R : Type*} [mΩ : MeasurableSpace Ω] [MeasurableSpace R] {P : Measure Ω} [IsFiniteMeasure P]

/-- The random element sent to a fixed point `r₀` off the event `f ∈ T`. -/
def cutOff (T : Set R) (r₀ : R) (f : Ω → R) (ω : Ω) : R := by
  classical exact if f ω ∈ T then f ω else r₀

theorem measurable_cutOff {T : Set R} (hT : MeasurableSet T) (r₀ : R) {f : Ω → R} (hf : Measurable f) :
    Measurable (cutOff T r₀ f) := by
  classical
  exact Measurable.ite (hf hT) hf measurable_const

/-- On the event `f ∈ T`, the conditional expectation given `f` is the one given the cut-off `cutOff T r₀ f`. -/
theorem condExp_ae_eq_restrict_cutOff {T : Set R} (hT : MeasurableSet T) {r₀ : R} (hr₀ : r₀ ∉ T) {f : Ω → R}
    (hf : Measurable f) (X : Ω → ℂ) :
    P[X | MeasurableSpace.comap f inferInstance] =ᵐ[P.restrict (f ⁻¹' T)]
      P[X | MeasurableSpace.comap (cutOff T r₀ f) inferInstance] := by
  classical
  have hc := measurable_cutOff hT r₀ hf
  have hTc : cutOff T r₀ f ⁻¹' T = f ⁻¹' T := by
    ext ω
    simp only [mem_preimage, cutOff]
    by_cases h : f ω ∈ T
    · simp only [h, ↓reduceIte]
    · simp only [h, ↓reduceIte, hr₀]
  have hpre : ∀ D : Set R, cutOff T r₀ f ⁻¹' (T ∩ D) = f ⁻¹' (T ∩ D) := fun D => by
    ext ω
    simp only [mem_inter_iff, mem_preimage, cutOff]
    by_cases h : f ω ∈ T
    · simp only [h, ↓reduceIte]
    · simp only [h, ↓reduceIte, hr₀, false_and]
  refine condExp_ae_eq_restrict_of_measurableSpace_eq_on hf.comap_le hc.comap_le ⟨T, hT, rfl⟩ fun t => ?_
  constructor
  · rintro ⟨D, hD, hDt⟩
    refine ⟨T ∩ D, hT.inter hD, ?_⟩
    rw [hpre, preimage_inter, hDt, ← inter_assoc, inter_self]
  · rintro ⟨D, hD, hDt⟩
    refine ⟨T ∩ D, hT.inter hD, ?_⟩
    rw [← hpre, preimage_inter, hDt, hTc, ← inter_assoc, inter_self]

/-- **Conditional expectations given two random elements that agree on an event `{f₁ ∈ T}`** (which is almost surely
`{f₂ ∈ T}`) agree almost surely on the event. -/
theorem ae_condExp_eq_on_of_ae_eq [StandardBorelSpace Ω] {T : Set R} (hT : MeasurableSet T) {r₀ : R}
    (hr₀ : r₀ ∉ T) {f₁ f₂ : Ω → R} (hf₁ : Measurable f₁) (hf₂ : Measurable f₂)
    (hTT : ∀ᵐ ω ∂P, (f₁ ω ∈ T ↔ f₂ ω ∈ T)) (heq : ∀ᵐ ω ∂P, f₁ ω ∈ T → f₁ ω = f₂ ω) {X : Ω → ℂ}
    (hX : Integrable X P) :
    ∀ᵐ ω ∂P, f₁ ω ∈ T → P[X | MeasurableSpace.comap f₁ inferInstance] ω =
      P[X | MeasurableSpace.comap f₂ inferInstance] ω := by
  classical
  have hc₁ := measurable_cutOff hT r₀ hf₁
  have hc₂ := measurable_cutOff hT r₀ hf₂
  have hcc : ∀ᵐ ω ∂P, cutOff T r₀ f₁ ω = cutOff T r₀ f₂ ω := by
    filter_upwards [hTT, heq] with ω h1 h2
    simp only [cutOff]
    by_cases h : f₁ ω ∈ T
    · simp only [↓reduceIte, h1.1 h, h2 h]
    · have h' : f₂ ω ∉ T := fun h' => h (h1.2 h')
      simp only [h, h', ↓reduceIte]
  have hk := KernelTower.ae_condExpKernel_comap_eq (P := P) hc₁ hc₂ measurable_id measurable_id hcc
    (hcc.mono fun ω h => h.symm)
  have hm₁ : MeasurableSpace.comap (cutOff T r₀ f₁) inferInstance ≤ mΩ := hc₁.comap_le
  have hm₂ : MeasurableSpace.comap (cutOff T r₀ f₂) inferInstance ≤ mΩ := hc₂.comap_le
  have hk₁ := condExp_ae_eq_integral_condExpKernel hm₁ hX
  have hk₂ := condExp_ae_eq_integral_condExpKernel hm₂ hX
  have hr₁ := (ae_restrict_iff' (hf₁ hT)).1 (condExp_ae_eq_restrict_cutOff (P := P) hT hr₀ hf₁ X)
  have hr₂ := (ae_restrict_iff' (hf₂ hT)).1 (condExp_ae_eq_restrict_cutOff (P := P) hT hr₀ hf₂ X)
  filter_upwards [hk, hk₁, hk₂, hr₁, hr₂, hTT] with ω hkω h1 h2 hr1 hr2 hT' hω
  rw [hr1 hω, hr2 (hT'.1 hω), h1, h2]
  rw [hkω]

end Restrict

/-! ### The record of the flow prefix -/

section Prefix

open Exist.StagedLaw Supp8.GB6 Restart

/-- Before the lifetime, the raw record does not see the lifetime. -/
theorem recOf_eq_recOf_top {s : ℝ≥0∞} (hs : s ≠ ⊤) {w : ℝ≥0 → ℝ} {ζ : ℝ≥0∞} (hsζ : s < ζ) :
    recOf s (w, ζ) = recOf s (w, ⊤) := by
  have h1 : min s ζ = s := min_eq_left hsζ.le
  have h2 : min s (⊤ : ℝ≥0∞) = s := min_eq_left le_top
  have h3 : decide (ζ ≤ s) = decide ((⊤ : ℝ≥0∞) ≤ s) := by
    rw [decide_eq_false (not_le.2 hsζ), decide_eq_false (not_le.2 (lt_top_iff_ne_top.2 hs))]
  simp only [recOf, retOf, h1, h2, h3]

/-- After the lifetime the raw record carries the flag `true`. -/
theorem recOf_flag_of_le {s : ℝ≥0∞} {w : ℝ≥0 → ℝ} {ζ : ℝ≥0∞} (hζs : ζ ≤ s) : (recOf s (w, ζ)).2.2 = true := by
  show decide (ζ ≤ s) = true
  exact decide_eq_true hζs

/-- A record with the flag `true` (off `gb6TS`). -/
def recOff : RecData := (fun _ => 0, 0, true)

theorem recOff_notMem (s : ℝ≥0) : recOff ∉ gb6TS s := fun h => by
  have : (true : Bool) = false := h.1
  exact Bool.noConfusion this

/-- **(R1) for any measurable version of the raw prefix record**: for almost every sample whose record lies in
`gb6TS s` (the record is before the lifetime, with an interior tip and nondegenerate seed images), under the regular
conditional law given `σ(g)`, the chart field is a GFF with the conditional word of the record. -/
theorem ae_isGFF_condExpKernel_prefix {κ θ : ℝ} (hκ : 0 < κ) {Ω : Type u} [mΩ : MeasurableSpace Ω]
    [StandardBorelSpace Ω] {Q : Measure Ω} [IsProbabilityMeasure Q] {h : Ω → DistOn upperHalfPlaneOpens}
    {b : ℝ → ℝ} {J : Finset ℝ} (hG : IsGFFWithBoundaryData Q h b J) {Wα : ℝ≥0 → Ω → ℝ} {ζα : Ω → ℝ≥0∞}
    {α : Ω → ℝ≥0 → ℂ} {c : BoundaryWord} (hflc : IsFlowLineDriver κ c.fn c.jumps θ Q h Wα ζα)
    (hα : ∀ᵐ ω ∂Q, IsGeneratingTrace (fun t => Wα t ω) (ζα ω) (α ω)) (s : ℝ≥0)
    {Hc : Ω → DistOn upperHalfPlaneOpens} (hHcm : Measurable Hc)
    (hHc : ∀ᵐ ω ∂Q, (s : ℝ≥0∞) < ζα ω → α ω s ∈ H →
      IsChartTransport (ownComponentChart (fun r : ℝ => Wα r.toNNReal ω) s) (-1)
        (-(Real.pi * QuantumZipper.chiC κ)) (QuantumZipper.chiC (16 / κ)) (h ω) (Hc ω))
    {g : Ω → RecData} (hg : Measurable g) (hgeq : ∀ᵐ ω ∂Q, g ω = recOf (s : ℝ≥0∞) ((fun t => Wα t ω), ζα ω)) :
    ∀ᵐ ω₀ ∂Q, g ω₀ ∈ gb6TS s →
      IsGFFWithBoundaryData (condExpKernel Q (MeasurableSpace.comap g inferInstance) ω₀) Hc
        (gb6WordOfRec κ θ c (g ω₀)).fn (gb6WordOfRec κ θ c (g ω₀)).jumps := by
  have hrecm : Measurable (gb6Rec s Wα ζα) := (measurable_recOf_cfE hflc s).2
  have hboth : ∀ᵐ ω ∂Q, (g ω ∈ gb6TS s ↔ gb6Rec s Wα ζα ω ∈ gb6TS s) ∧
      (g ω ∈ gb6TS s → g ω = gb6Rec s Wα ζα ω) := by
    filter_upwards [hgeq, ae_gb6RecGood hflc hα s] with ω hgω hrec
    by_cases hs : (s : ℝ≥0∞) < ζα ω
    · have e : g ω = gb6Rec s Wα ζα ω := by
        rw [hgω, recOf_eq_recOf_top ENNReal.coe_ne_top hs, (hrec hs).2.1]
      exact ⟨by rw [e], fun _ => e⟩
    · have h1 : g ω ∉ gb6TS s := fun hm => by
        have hf := hm.1
        rw [hgω, recOf_flag_of_le (not_lt.1 hs)] at hf
        exact Bool.noConfusion hf
      have h2 : gb6Rec s Wα ζα ω ∉ gb6TS s := fun hm => hs ((flag_recOf_cfE s).1 hm.1)
      exact ⟨⟨fun hm => absurd hm h1, fun hm => absurd hm h2⟩, fun hm => absurd hm h1⟩
  have hcf : ∀ φ : TestOn upperHalfPlaneOpens, ∀ᵐ ω ∂Q, ω ∈ g ⁻¹' gb6TS s →
      Q[fun ω' => Complex.exp (Complex.I * (Hc ω' φ : ℂ)) | MeasurableSpace.comap g inferInstance] ω =
        gaussCF (gb6WordOfRec κ θ c (g ω)) φ := by
    intro φ
    have hint : Integrable (fun ω => Complex.exp (Complex.I * (Hc ω φ : ℂ))) Q :=
      GFF.integrable_exp_I_mul ((LQGMetric.measurable_distOn_apply φ).comp hHcm)
    have h1 := ae_condExp_eq_on_of_ae_eq (measurableSet_gb6TS s) (recOff_notMem s) hg hrecm
      (hboth.mono fun ω h => h.1) (hboth.mono fun ω h => h.2) hint
    have h2 := gb6_condDet_r1 (θ := θ) hκ hG hflc hα s hHcm hHc φ
    filter_upwards [h1, h2, hboth] with ω e1 e2 hb hω
    have hω' : gb6Rec s Wα ζα ω ∈ gb6TS s := hb.1.1 hω
    rw [e1 hω, e2 hω', ← hb.2 hω]
  exact ae_isGFFWithBoundaryData_condExpKernel hg.comap_le
    (Eventually.of_forall fun ω _ => isSorted_gb6WordOfRec κ θ c (g ω)) hHcm hcf

end Prefix

end BRLeaf

end Theorem14

end InteractingSLE
