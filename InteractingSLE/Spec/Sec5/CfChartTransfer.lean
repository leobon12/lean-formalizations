/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec5.CfChartCoarse
import InteractingSLE.Spec.Sec5.CfGivenTransfer

/-!
# Lemma 4.7's chart clause moved from the glued space to the given space

Packet PROVE-CFCHART (PROVE-CFGIVEN §3, step 4). The glued space `Ω × 𝓗` carries the chart coupling clause of the
counterflow's killed image word for its raw image filtration (`isChartCouplingCharFunConst_q_E`, any good set `E`).
Here the clause is moved to the given space `Ω`, on which the counterflow history `Y` has the conditional law `k`
given the field:

1. the clause at the canonical extensions (`CfGiven.IsChartCanon`) on the glued space;
2. the tower property down to the raw image filtration computed on the **coarse** copy `Coarse m × 𝓗`
   (`IsChartCanon.of_le`; the event and the right-hand side are measurable there, `measurable_chartCanon_q`);
3. equal laws on the coarse product (`map_glue_coarse_eq`) and `IsChartCanon.of_map_eq`.

## Main results

* `measurable_chartCanon_q`: the event and the right-hand side of the clause at image time `r` are measurable for the
  raw image filtration at `r` (any base space);
* **`isChartCanon_coarse`**: the clause on the given space `Ω` for the pulled-back raw image filtration, with the
  image processes, the killing time and the chart read through `ω ↦ (ω, Y ω)`.

R48: nothing here uses Theorem 1.2/1.3, `Theorem12ParamStatement`, `Theorem13Statement` or any `*_of_param`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped NNReal ENNReal Real
open QuantumZipper (H fwdHull chiC)
open LQGMetric (DistOn TestOn)

universe u

namespace InteractingSLE.Sec5.CfChart

open WangWu hiding ratPt exists_ratPt_dist_lt
open LawUnique GlueCond Cond44Ref CfRegQ Prop411Q CrossCond.Theta
open CrossRestart.KernelQ CrossRestart.KernelQ.Kill47
open Lemma47Angle
open CfGiven
open Restart.DomainMarkov (bheProc isBoundedHarmonicExtension_bheProc)

/-! ### Measurability of the clause for the raw image filtration -/

section Meas

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {nL nR mL mR : ℕ} {W : ℝ≥0 → Ω → ℝ}
  {VL : Fin nL → ℝ≥0 → Ω → ℝ} {VR : Fin nR → ℝ≥0 → Ω → ℝ} {ζ : Ω → ℝ≥0∞} {s : ℝ≥0}
  {E : Set (Ω × HistorySpace 0 0)} {xL' : Fin mL → ℝ} {xR' : Fin mR → ℝ}

/-- **The event and the right-hand side of the chart clause at image time `r` are known at `r`** (raw image
filtration, canonical extensions). -/
theorem measurable_chartCanon_q (a : ℝ) (ρL' : Fin (mL + 1) → ℝ) (ρR' : Fin (mR + 1) → ℝ) (aC kC : ℝ)
    (hxo : IsOrderedForceWord xL' xR') (hX : IsMeasurableKilledDriving W VL VR ζ) (hE : MeasurableSet E)
    (hEg : ∀ p ∈ E, IsGood47 W VL VR ζ p) (hs : 0 < s) (r : ℝ≥0) (φ : TestOn upperHalfPlaneOpens) :
    MeasurableSet[qRaw xL' xR' W VL VR ζ s E r]
        (chartEv (fun p => (qT W VL VR ζ s E p : ℝ≥0∞)) (qW W VL VR ζ s E) (fChart W VL VR ζ s) r φ) ∧
      Measurable[qRaw xL' xR' W VL VR ζ s E r]
        ((chartEv (fun p => (qT W VL VR ζ s E p : ℝ≥0∞)) (qW W VL VR ζ s E) (fChart W VL VR ζ s) r φ).indicator
          (chartRhs a (qW W VL VR ζ s E) (fChart W VL VR ζ s) aC kC
            (canonU a ρL' ρR' (qW W VL VR ζ s E) (qVL xL' W VL VR ζ s E) (qVR xR' W VL VR ζ s E) r) r φ)) := by
  obtain ⟨hErm, hmeanm, hvarm⟩ := measurable_fChartAvoid_raw a ρL' ρR' aC kC hxo hX hE hEg hs r φ
  have hkw := isKilledWord_q_of_ordered hxo hEg hs
  set Ev := chartEv (fun p => (qT W VL VR ζ s E p : ℝ≥0∞)) (qW W VL VR ζ s E) (fChart W VL VR ζ s) r φ
    with hEv
  have hEvm : MeasurableSet[qRaw xL' xR' W VL VR ζ s E r] Ev := hErm
  refine ⟨hEvm, ?_⟩
  have e : Ev.indicator (chartRhs a (qW W VL VR ζ s E) (fChart W VL VR ζ s) aC kC
      (canonU a ρL' ρR' (qW W VL VR ζ s E) (qVL xL' W VL VR ζ s E) (qVR xR' W VL VR ζ s E) r) r φ) =
      Ev.indicator (fun p => Complex.exp (Complex.I *
        ((Ev.indicator (fun p => Sec7.Lemma71D.chartMean a ρL' ρR' (fun t => qW W VL VR ζ s E t p)
          (fun i t => qVL xL' W VL VR ζ s E i t p) (fun j t => qVR xR' W VL VR ζ s E j t p) (fChart W VL VR ζ s p)
          aC kC φ r) p : ℝ) : ℂ) -
        (((1 / 2 : ℝ) * Ev.indicator (fun p => Sec7.Lemma71D.chartVar (fun t => qW W VL VR ζ s E t p)
          (fChart W VL VR ζ s p) φ r) p : ℝ) : ℂ))) := by
    refine Set.indicator_congr fun p hp => ?_
    rw [indicator_of_mem hp, indicator_of_mem hp]
    have hav : Sec7.Lemma71D.IsChartAvoid (fun t => qW W VL VR ζ s E t p) (qT W VL VR ζ s E p : ℝ≥0∞)
        (fChart W VL VR ζ s p) φ r := hp
    have hint : (∫ z, (couplingMean a (fun s' : ℝ => qW W VL VR ζ s E s'.toNNReal p) (r : ℝ)
        (bheProc a ρL' ρR' (qW W VL VR ζ s E) (qVL xL' W VL VR ζ s E) (qVR xR' W VL VR ζ s E) p r)
        ((fChart W VL VR ζ s p).1 z) - aC - kC * (fChart W VL VR ζ s p).2.2 z) * φ z) =
        Sec7.Lemma71D.chartMean a ρL' ρR' (fun t => qW W VL VR ζ s E t p) (fun i t => qVL xL' W VL VR ζ s E i t p)
          (fun j t => qVR xR' W VL VR ζ s E j t p) (fChart W VL VR ζ s p) aC kC φ r :=
      Sec7.Lemma71D.integral_couplingMean_eq_chartMean (κ := a) (ρL := ρL') (ρR := ρR') (a := aC)
        (k := kC) (w := fun t => qW W VL VR ζ s E t p) (vL := fun i t => qVL xL' W VL VR ζ s E i t p)
        (vR := fun j t => qVR xR' W VL VR ζ s E j t p) (isConformal_fChart p) (hkw.contW p) hav
        (fun i => hkw.ordL p r i hav.1) (fun j => hkw.ordR p r j hav.1)
        (isBoundedHarmonicExtension_bheProc (κ := a) (ρL := ρL') (ρR := ρR')
          (W := qW W VL VR ζ s E) (VL := qVL xL' W VL VR ζ s E) (VR := qVR xR' W VL VR ζ s E) p r)
    unfold chartRhs canonU
    rw [hint]
    rfl
  rw [e]
  refine Measurable.indicator ?_ hEvm
  exact Complex.measurable_exp.comp ((Complex.measurable_ofReal.comp hmeanm).const_mul _ |>.sub
    (Complex.measurable_ofReal.comp (hvarm.const_mul _)))

end Meas

/-! ### From the glued space to the given space -/

section Transfer

variable {κ θ : ℝ} {nL nR : ℕ} {xL : Fin nL → ℝ} {xR : Fin nR → ℝ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ}
  {Ω : Type u} {m : MeasurableSpace Ω} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {𝓕 : Filtration ℝ≥0 mΩ} {W : ℝ≥0 → Ω → ℝ} {VL : Fin nL → ℝ≥0 → Ω → ℝ} {VR : Fin nR → ℝ≥0 → Ω → ℝ}
  {B : ℝ≥0 → Ω → ℝ} {ζ : Ω → ℝ≥0∞} {h : Ω → DistOn upperHalfPlaneOpens} {W₂ : ℝ≥0 → Ω → ℝ} {ζ₂ : Ω → ℝ≥0∞}

/-- **Lemma 4.7's chart clause on the given space.** Let the flow coupling (field `h`, angle `θ`) and the centred
counterflow of the field `cfFieldT κ θ h` live on the same space `Ω`, `k` the conditional law of the counterflow history
given that field, `m` a coarse σ-algebra (events of the field up to null sets) for which the field and the killed flow
data are measurable, and `E` a coarse-measurable set of good glued samples of full glued measure. Then on `Ω`, for the
pulled-back raw image filtration, the field `−h` has the chart coupling clause of the counterflow's killed image word
(canonical extensions, fixed image times), the image processes, the killing time and the chart being read through
`ω ↦ (ω, cfHistory W₂ ζ₂ ω)`. -/
theorem isChartCanon_coarse (hκ : 0 < κ) (hκ4 : κ < 4) (hF : IsOrderedForceWord xL xR)
    (h44 : Sec4.Cond44 κ ρL ρR) (hθb : CfThetaBounds κ θ ρL ρR xL xR)
    (hC : IsOptionalHullCoupling κ xL xR ρL ρR P 𝓕 W VL VR B ζ h)
    (hcf : IsCenteredCounterflowDriver κ P (fun ω => cfFieldT κ θ (h ω)) W₂ ζ₂)
    (k : Kernel (DistOn upperHalfPlaneOpens) (HistorySpace 0 0)) [IsMarkovKernel k]
    (hk : P.map (fun ω => (cfFieldT κ θ (h ω), cfHistory W₂ ζ₂ ω)) = P.map (fun ω => cfFieldT κ θ (h ω)) ⊗ₘ k)
    (hY : Measurable (cfHistory W₂ ζ₂))
    (hm : m ≤ mΩ) (hmX : m ≤ fieldNullSigma P (fun ω => cfFieldT κ θ (h ω)))
    (hXm : @IsMeasurableKilledDriving Ω m nL nR W VL VR ζ) (hhm : Measurable[m] h)
    (E : Set (Coarse m × HistorySpace 0 0)) (hE : MeasurableSet E) (hEg : ∀ p ∈ E, IsGood47 W VL VR ζ p)
    (hEae : ∀ᵐ p ∂(glueMeasure P k (fun ω => cfFieldT κ θ (h ω)) ((measurable_cfFieldT κ θ).comp hC.2.1)),
      p ∈ E)
    {s : ℝ≥0} (hs : 0 < s) :
    IsChartCanon (16 / κ) (iwLT κ θ ρL ρR xL xR) (iwRT κ θ ρL ρR xL xR) P
      (Coupling.filtrationComap (qRaw (Ω := Coarse m) (qxLT κ θ ρL ρR xL xR) (qxRT κ θ ρL ρR xL xR) W VL VR ζ s E)
        ((measurable_toCoarse hm).prodMk hY))
      (fun t ω => qW (Ω := Coarse m) W VL VR ζ s E t (toCoarse m ω, cfHistory W₂ ζ₂ ω))
      (fun i t ω => qVL (Ω := Coarse m) (qxLT κ θ ρL ρR xL xR) W VL VR ζ s E i t (toCoarse m ω, cfHistory W₂ ζ₂ ω))
      (fun j t ω => qVR (Ω := Coarse m) (qxRT κ θ ρL ρR xL xR) W VL VR ζ s E j t (toCoarse m ω, cfHistory W₂ ζ₂ ω))
      (fun ω => (qT (Ω := Coarse m) W VL VR ζ s E (toCoarse m ω, cfHistory W₂ ζ₂ ω) : ℝ≥0∞))
      (fun ω => fChart (Ω := Coarse m) W VL VR ζ s (toCoarse m ω, cfHistory W₂ ζ₂ ω))
      (-((π - θ) * chiC κ)) (-chiC κ) (fun ω => -h ω) := by
  set μ := glueMeasure P k (fun ω => cfFieldT κ θ (h ω)) ((measurable_cfFieldT κ θ).comp hC.2.1) with hμ
  have hg₁ : Measurable fun p : Ω × HistorySpace 0 0 => (toCoarse m p.1, p.2) :=
    ((measurable_toCoarse hm).comp measurable_fst).prodMk measurable_snd
  have hg₂ : Measurable fun ω => (toCoarse m ω, cfHistory W₂ ζ₂ ω) := (measurable_toCoarse hm).prodMk hY
  have hE' : MeasurableSet (show Set (Ω × HistorySpace 0 0) from E) := hg₁ hE
  have hxo := isOrderedForceWord_qx_angle κ θ ρL ρR xL xR
  -- 1. the clause on the glued space, for the full raw image filtration
  have hcl := isChartCouplingCharFunConst_q_E hκ hκ4 hF h44 hθb hC hcf rfl k hk E hE' hEg hEae hs
    (fun r _ _ ht'0 ht't ht _ hA => marks47_inter (Ω := Ω) _ _ ht hEg hEae r ht'0 ht't hA)
    (fun _ ht φ => marks47_avoid (Ω := Ω) ht hEg hEae φ)
  have hcan : IsChartCanon (16 / κ) (iwLT κ θ ρL ρR xL xR) (iwRT κ θ ρL ρR xL xR) μ
      (qRaw (qxLT κ θ ρL ρR xL xR) (qxRT κ θ ρL ρR xL xR) W VL VR ζ s E) (qW W VL VR ζ s E)
      (qVL (qxLT κ θ ρL ρR xL xR) W VL VR ζ s E) (qVR (qxRT κ θ ρL ρR xL xR) W VL VR ζ s E)
      (fun p => (qT W VL VR ζ s E p : ℝ≥0∞)) (fun p => fChart W VL VR ζ s p) (-((π - θ) * chiC κ)) (-chiC κ)
      (fun p => -h p.1) := fun t φ => by
    filter_upwards [hcl t (canonU (16 / κ) (iwLT κ θ ρL ρR xL xR) (iwRT κ θ ρL ρR xL xR) (qW W VL VR ζ s E)
        (qVL (qxLT κ θ ρL ρR xL xR) W VL VR ζ s E) (qVR (qxRT κ θ ρL ρR xL xR) W VL VR ζ s E) t)
        (fun ω => isBoundedHarmonicExtension_bheProc ω t) φ] with ω hω hωE
    exact hω hωE.1 hωE.2
  -- the measurability on the coarse copy
  have hmeas := fun r φ => measurable_chartCanon_q (Ω := Coarse m) (16 / κ) (iwLT κ θ ρL ρR xL xR)
    (iwRT κ θ ρL ρR xL xR) (-((π - θ) * chiC κ)) (-chiC κ) hxo hXm hE hEg hs r φ
  -- 2. the tower property down to the pulled-back coarse raw filtration
  have hhm' : Measurable h := hhm.mono hm le_rfl
  have hneg : Measurable fun p : Ω × HistorySpace 0 0 => -h p.1 :=
    LQGMetric.measurable_distOn_iff.2 fun φ => ((LQGMetric.measurable_distOn_apply φ).comp
      (hhm'.comp measurable_fst)).neg
  have hle : ∀ t, Coupling.filtrationComap (qRaw (Ω := Coarse m) (qxLT κ θ ρL ρR xL xR) (qxRT κ θ ρL ρR xL xR)
      W VL VR ζ s E) hg₁ t ≤ qRaw (qxLT κ θ ρL ρR xL xR) (qxRT κ θ ρL ρR xL xR) W VL VR ζ s E t := by
    intro t S hS
    obtain ⟨A, hA, rfl⟩ := hS
    refine ⟨?_, hg₁ ((qRaw (Ω := Coarse m) (qxLT κ θ ρL ρR xL xR) (qxRT κ θ ρL ρR xL xR) W VL VR ζ s E).le t _ hA)⟩
    have key : MeasurableSpace.comap (fun p : Ω × HistorySpace 0 0 => (toCoarse m p.1, p.2))
        (MeasurableSpace.generateFrom (qGen (Ω := Coarse m) (qxLT κ θ ρL ρR xL xR) (qxRT κ θ ρL ρR xL xR)
          W VL VR ζ s E t)) ≤
        MeasurableSpace.generateFrom (qGen (qxLT κ θ ρL ρR xL xR) (qxRT κ θ ρL ρR xL xR) W VL VR ζ s E t) := by
      rw [MeasurableSpace.comap_generateFrom]
      refine MeasurableSpace.generateFrom_mono ?_
      rintro _ ⟨A, ⟨r', hr', hcase⟩, rfl⟩
      refine ⟨r', hr', ?_⟩
      rcases hcase with ⟨B, hB, h1 | ⟨i, h1⟩ | ⟨j, h1⟩⟩ | h1 | ⟨n, h1⟩ | ⟨B, hB, h1⟩ <;> subst h1
      · exact Or.inl ⟨B, hB, Or.inl rfl⟩
      · exact Or.inl ⟨B, hB, Or.inr (Or.inl ⟨i, rfl⟩)⟩
      · exact Or.inl ⟨B, hB, Or.inr (Or.inr ⟨j, rfl⟩)⟩
      · exact Or.inr (Or.inl rfl)
      · exact Or.inr (Or.inr (Or.inl ⟨n, rfl⟩))
      · exact Or.inr (Or.inr (Or.inr ⟨B, hB, rfl⟩))
    exact key _ ⟨A, hA.1, rfl⟩
  have hcan₁ := hcan.of_le hneg hle (fun t φ => ⟨_, (hmeas t φ).1, rfl⟩)
    (fun t φ => ((hmeas t φ).2.comp (comap_measurable _)).stronglyMeasurable)
  -- 3. equal laws on the coarse product
  have hlaw := map_glue_coarse_eq ((measurable_cfFieldT κ θ).comp hC.2.1) hY k hk hm hmX
  have hnegZ : Measurable fun z : Coarse m × HistorySpace 0 0 => -h z.1 :=
    LQGMetric.measurable_distOn_iff.2 fun φ => ((LQGMetric.measurable_distOn_apply φ).comp
      (hhm.comp measurable_fst)).neg
  exact IsChartCanon.of_map_eq (𝓩 := qRaw (Ω := Coarse m) (qxLT κ θ ρL ρR xL xR) (qxRT κ θ ρL ρR xL xR)
      W VL VR ζ s E) (W := qW (Ω := Coarse m) W VL VR ζ s E)
    (VL := qVL (Ω := Coarse m) (qxLT κ θ ρL ρR xL xR) W VL VR ζ s E)
    (VR := qVR (Ω := Coarse m) (qxRT κ θ ρL ρR xL xR) W VL VR ζ s E)
    (ζ := fun z => (qT (Ω := Coarse m) W VL VR ζ s E z : ℝ≥0∞)) (c := fun z => fChart (Ω := Coarse m) W VL VR ζ s z)
    (h := fun z : Coarse m × HistorySpace 0 0 => -h z.1) hg₁ hg₂ hlaw hnegZ
    (fun t φ => (qRaw (Ω := Coarse m) (qxLT κ θ ρL ρR xL xR) (qxRT κ θ ρL ρR xL xR) W VL VR ζ s E).le t _
      (hmeas t φ).1)
    (fun t φ => (hmeas t φ).2.mono ((qRaw (Ω := Coarse m) (qxLT κ θ ρL ρR xL xR) (qxRT κ θ ρL ρR xL xR)
      W VL VR ζ s E).le t) le_rfl) hcan₁

end Transfer

end InteractingSLE.Sec5.CfChart
