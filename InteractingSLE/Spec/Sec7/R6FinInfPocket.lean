/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.R6CertNestGerm
import InteractingSLE.Spec.Sec7.HOuterMarkedInf
import InteractingSLE.Spec.Sec7.PocketStopMarkedInf
import InteractingSLE.Spec.Sec7.HOuterGeo

/-!
# R.6's stop pockets opening at the flow seed

PROVE-R6-CERT2. The pockets opening at the flow seed (`rightLo = 0`, the `…Inf` shapes) as stop pockets
(`R6Cert.IsStopPocket`) for `T⁰(q)` (`PocketStopMarked.stopTimeMInf`), the walls `m(R ∪ L)` and the regularized
hull, exactly as PROVE-R6-CERT's bounded `isStopPocket_outer`, `isStopPocket_cf`:

* `isStopPocket_outerInf` (`HOuter.IsOuterCfgInf`; `PocketStopMarked.Outer.isMarkedStop_stopTimeMInf`,
  `HOuter.relDomain_subset_domain_ambTime0Inf`);
* `isStopPocket_cfInf` (`IsCfPocketConfigInf`; `PocketStopMarked.isMarkedStop_stopTimeMInf`,
  `PocketUnionPt.image_inter_domain_ambTimeInf`, `inter_domain_ambTime0Inf`).

R48: nothing here uses Theorem 1.2/1.3, `Theorem12ParamStatement`, `Theorem13Statement` or any `*_of_param`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology Metric Bornology
open QuantumZipper (H fwdHull)
open LQGMetric (DistOn)
open InteractingSLE.WangWu (negInv)
open scoped NNReal ENNReal

namespace InteractingSLE.Sec7.R6Fin

open R6Cert PocketStopWallsFin PocketStopWalls PocketStop PocketCoupling PocketUnionPt LocalSets WholeField
  PocketTraversal Lemma71C Lemma71I PocketCoord PocketJordan PocketMarks PocketWordAssembly PocketStopField R7StopIn
  PocketSeedOpen

variable {Ω 𝒳 : Type*} [MeasurableSpace 𝒳]

/-- **The outer pocket opening at the flow seed: its active complement at relative time `q` is a stop pocket** for
`T⁰(q)` (`PocketStopMarked.stopTimeMInf`), the walls `m(R ∪ L)` and the regularized hull, for any information `X`
with `𝓦 ≤ σ(X) ∨ 𝓕_0`. -/
theorem isStopPocket_outerInf {𝓦 : MeasurableSpace Ω} [mΩ : MeasurableSpace Ω] {𝓕 : Filtration ℝ≥0 mΩ}
    {X : Ω → 𝒳} {W' : ℝ≥0 → Ω → ℝ} {ζ' : Ω → ℝ≥0∞} {R L : Ω → ℝ≥0 → ℂ} {r : ℝ≥0} {G A : Set Ω}
    {η : Ω → ℝ → ℂ} {ψ : Ω → ℂ → ℂ} {n : Ω → ℤ}
    (h𝓦m : 𝓦 ≤ mΩ) (h𝓦 : 𝓦 ≤ MeasurableSpace.comap X inferInstance ⊔ 𝓕 0)
    (hWad : AdaptedBefore 𝓕 ζ' W') (hRm : ∀ t, Measurable[𝓦] fun ω => R ω t)
    (hLm : ∀ t, Measurable[𝓦] fun ω => L ω t) (hGm : MeasurableSet[𝓦] G)
    (hcfg : ∀ ω ∈ G, HOuter.IsOuterCfgInf (R ω) (L ω) r (fun s : ℝ => W' s.toNNReal ω) (η ω))
    (hA : MeasurableSet[𝓦] A) (hAG : A ⊆ G) (hζA : ∀ ω ∈ A, ζ' ω = ⊤)
    (hψ : ∀ ω ∈ A, IsCfJordanInf (R ω) (L ω) r (ψ ω)) (hψm : @IsPointMeasurableInf Ω 𝓦 R L r G ψ)
    (hηm : ∀ u, 0 ≤ u → Measurable fun ω => η ω u) (hn : Measurable[𝓦] n) (q : ℝ≥0) :
    IsStopPocket 𝓕 X (regHull W' ζ') (fun ω => negInv '' (range (R ω) ∪ range (L ω)))
      (locPrefixSigma 𝓦 A (travAllInf R L r η ψ) q) (PocketStopMarked.stopTimeMInf A R L r η ψ q)
      (activeCompl A (travAllInf R L r η ψ)
        (fun ω => shiftChart (pChart A (fun ω => cfPocket (R ω) (L ω) r) ψ ω) (n ω)) q) := by
  have hG : ∀ ω ∈ G, IsChangeConfigInc (R ω) (L ω) r := fun ω hω => (hcfg ω hω).conf
  have hcfgA : ∀ ω ∈ A, HOuter.IsOuterCfgInf (R ω) (L ω) r (fun s : ℝ => W' s.toNNReal ω) (η ω) :=
    fun ω hω => hcfg ω (hAG hω)
  have hCm : ∀ z, MeasurableSet[𝓦] {ω | ω ∈ A ∧ z ∈ cfPocket (R ω) (L ω) r} := fun z =>
    measurableSet_mem_cfPocket_of_subset hRm hLm hGm hG hA hAG z
  have hψm' : ∀ z, Measurable[𝓦] ({ω | ω ∈ A ∧ z ∈ cfPocket (R ω) (L ω) r}.indicator fun ω => ψ ω z) := fun z =>
    hψm _ (hCm z) (fun ω hω => hAG hω.1) (fun _ => z) measurable_const fun ω hω => subset_closure hω.2
  have hCo : ∀ ω ∈ A, IsOpen (cfPocket (R ω) (L ω) r) := fun ω hω =>
    isOpen_image_negInv' (hG ω (hAG hω)).isOpen_changePocket (hG ω (hAG hω)).changePocket_subset_H
  have hCH : ∀ ω ∈ A, cfPocket (R ω) (L ω) r ⊆ H := fun ω hω =>
    PocketJordan.image_negInv_subset_H (hG ω (hAG hω)).changePocket_subset_H
  have hψc : ∀ ω ∈ A, SupercriticalConformalCovariance.IsConformalBijection (ψ ω) (cfPocket (R ω) (L ω) r) H :=
    fun ω hω => (hψ ω hω).2.2.2.1
  have hCin : ∀ U : Set ℂ, IsOpen U → U ⊆ H → MeasurableSet[𝓦] {ω | ω ∈ A ∧ U ⊆ cfPocket (R ω) (L ω) r} :=
    fun U hUo hUH => Lemma725RefMarks.measurableSet_subset_cfPocket hRm hLm hGm hG hA hAG hUo hUH
  have hpch := isPocketChartOn_pChart (mΩ := 𝓦) hA hCo hCH hψc hCm hψm'
  have hcOn := isPocketChartOn_shift hpch.1 hCm hn
  have hγ : ∀ ω ∈ A, IsDrivenCurve (travAllInf R L r η ψ ω) := fun ω hω => ((hcfgA ω hω).props (hψ ω hω)).1
  have hγm : ∀ u, 0 ≤ u → Measurable fun ω : A => travAllInf R L r η ψ ω u :=
    fun u hu => HOuter.measurable_travAllInf_outer h𝓦m hRm hLm hGm hcfg hηm hAG hψ hψm hu
  have hlive : ∀ ω, ω ∈ A ∧ (q : ℝ≥0∞) < capLife (travAllInf R L r η ψ ω) →
      PocketStopMarked.stopTimeMInf A R L r η ψ q ω = stopTime0Inf R L r η ψ q ω := fun ω hl => by
    unfold PocketStopMarked.stopTimeMInf
    exact ite_eq_left hl
  refine isStopPocket_activeCompl h𝓦m hA hγ hγm hCo hCH hψc hCm hψm' hCin
    (fun ω hω => ⟨(hcOn.1 ω hω).1, (hcOn.1 ω hω).2.1, (hcOn.1 ω hω).2.2.1⟩)
    (PocketStopMarked.Outer.isMarkedStop_stopTimeMInf h𝓦 hWad hRm hLm hGm hG hA hAG hcfgA hζA hψ hψm q)
    (PocketStopMarked.Outer.measurableSet_sup_iSup_of_locPrefixSigmaInf h𝓦 hWad hRm hLm hGm hG hA hAG hcfgA hζA hψ
      hψm q) (fun ω hT => ?_) (fun ω hω hq => ?_) (fun ω hω _ => (cfPocket_walls_props (hG ω (hAG hω))).1)
    (fun ω hω hq => ?_)
  · by_contra hl
    unfold PocketStopMarked.stopTimeMInf at hT
    rw [ite_eq_right hl] at hT
    exact lt_irrefl _ hT
  · rw [hlive ω ⟨hω, hq⟩]
    exact ENNReal.ofReal_lt_top
  · have hc := hcfgA ω hω
    have hψ' : Sec6.IsJordanCoordInf (cfPocket (R ω) (L ω) r) (cfArcRInf (R ω) (L ω) r 0) (ψ ω) := by
      rw [IsChangeConfigInc.cfArcRInf_zero]
      exact hψ ω hω
    rw [hlive ω ⟨hω, hq⟩, ← PocketStopMarked.Outer.stopHull0Inf_eq_regHull' hc (hζA ω hω) q]
    exact HOuter.relDomain_subset_domain_ambTime0Inf hc.erase hc.trace (hCH ω hω) hψ' (hc.props (hψ ω hω)).1
      q.coe_nonneg (by rw [ENNReal.ofReal_coe_nnreal]; exact hq)

/-- **A contained pocket opening at the flow seed: its active complement at relative time `q` is a stop pocket**
for `T⁰(q)` (`PocketStopMarked.stopTimeMInf`), the walls `m(R ∪ L)` and the regularized hull. -/
theorem isStopPocket_cfInf {𝓦 : MeasurableSpace Ω} [mΩ : MeasurableSpace Ω] {𝓕 : Filtration ℝ≥0 mΩ}
    {X : Ω → 𝒳} {W' : ℝ≥0 → Ω → ℝ} {ζ' : Ω → ℝ≥0∞} {R L : Ω → ℝ≥0 → ℂ} {r : ℝ≥0} {G A : Set Ω}
    {η : Ω → ℝ → ℂ} {ψ : Ω → ℂ → ℂ} {n : Ω → ℤ}
    (h𝓦m : 𝓦 ≤ mΩ) (h𝓦 : 𝓦 ≤ MeasurableSpace.comap X inferInstance ⊔ 𝓕 0)
    (hWad : AdaptedBefore 𝓕 ζ' W') (hRm : ∀ t, Measurable[𝓦] fun ω => R ω t)
    (hLm : ∀ t, Measurable[𝓦] fun ω => L ω t) (hGm : MeasurableSet[𝓦] G)
    (hcfg : ∀ ω ∈ G, IsCfPocketConfigInf (R ω) (L ω) r (fun s : ℝ => W' s.toNNReal ω) (η ω))
    (hA : MeasurableSet[𝓦] A) (hAG : A ⊆ G) (hζA : ∀ ω ∈ A, ζ' ω = ⊤)
    (hψ : ∀ ω ∈ A, IsCfJordanInf (R ω) (L ω) r (ψ ω)) (hψm : @IsPointMeasurableInf Ω 𝓦 R L r G ψ)
    (hηm : ∀ u, 0 ≤ u → Measurable fun ω => η ω u) (hn : Measurable[𝓦] n) (q : ℝ≥0) :
    IsStopPocket 𝓕 X (regHull W' ζ') (fun ω => negInv '' (range (R ω) ∪ range (L ω)))
      (locPrefixSigma 𝓦 A (travAllInf R L r η ψ) q) (PocketStopMarked.stopTimeMInf A R L r η ψ q)
      (activeCompl A (travAllInf R L r η ψ)
        (fun ω => shiftChart (pChart A (fun ω => cfPocket (R ω) (L ω) r) ψ ω) (n ω)) q) := by
  have hG : ∀ ω ∈ G, IsChangeConfigInc (R ω) (L ω) r := fun ω hω => (hcfg ω hω).conf
  have hcfgA : ∀ ω ∈ A, IsCfPocketConfigInf (R ω) (L ω) r (fun s : ℝ => W' s.toNNReal ω) (η ω) :=
    fun ω hω => hcfg ω (hAG hω)
  have hCm : ∀ z, MeasurableSet[𝓦] {ω | ω ∈ A ∧ z ∈ cfPocket (R ω) (L ω) r} := fun z =>
    measurableSet_mem_cfPocket_of_subset hRm hLm hGm hG hA hAG z
  have hψm' : ∀ z, Measurable[𝓦] ({ω | ω ∈ A ∧ z ∈ cfPocket (R ω) (L ω) r}.indicator fun ω => ψ ω z) := fun z =>
    hψm _ (hCm z) (fun ω hω => hAG hω.1) (fun _ => z) measurable_const fun ω hω => subset_closure hω.2
  have hCo : ∀ ω ∈ A, IsOpen (cfPocket (R ω) (L ω) r) := fun ω hω =>
    isOpen_image_negInv' (hG ω (hAG hω)).isOpen_changePocket (hG ω (hAG hω)).changePocket_subset_H
  have hCH : ∀ ω ∈ A, cfPocket (R ω) (L ω) r ⊆ H := fun ω hω =>
    PocketJordan.image_negInv_subset_H (hG ω (hAG hω)).changePocket_subset_H
  have hψc : ∀ ω ∈ A, SupercriticalConformalCovariance.IsConformalBijection (ψ ω) (cfPocket (R ω) (L ω) r) H :=
    fun ω hω => (hψ ω hω).2.2.2.1
  have hCin : ∀ U : Set ℂ, IsOpen U → U ⊆ H → MeasurableSet[𝓦] {ω | ω ∈ A ∧ U ⊆ cfPocket (R ω) (L ω) r} :=
    fun U hUo hUH => Lemma725RefMarks.measurableSet_subset_cfPocket hRm hLm hGm hG hA hAG hUo hUH
  have hpch := isPocketChartOn_pChart (mΩ := 𝓦) hA hCo hCH hψc hCm hψm'
  have hcOn := isPocketChartOn_shift hpch.1 hCm hn
  have hγ : ∀ ω ∈ A, IsDrivenCurve (travAllInf R L r η ψ ω) := fun ω hω =>
    ((hcfgA ω hω).isDrivenCurve (hψ ω hω)).1
  have hγm : ∀ u, 0 ≤ u → Measurable fun ω : A => travAllInf R L r η ψ ω u :=
    fun u hu => measurable_travSubInf h𝓦m hRm hLm hGm hcfg hηm hAG hψ hψm hu
  have hlive : ∀ ω, ω ∈ A ∧ (q : ℝ≥0∞) < capLife (travAllInf R L r η ψ ω) →
      PocketStopMarked.stopTimeMInf A R L r η ψ q ω = stopTime0Inf R L r η ψ q ω := fun ω hl => by
    unfold PocketStopMarked.stopTimeMInf
    exact ite_eq_left hl
  refine isStopPocket_activeCompl h𝓦m hA hγ hγm hCo hCH hψc hCm hψm' hCin
    (fun ω hω => ⟨(hcOn.1 ω hω).1, (hcOn.1 ω hω).2.1, (hcOn.1 ω hω).2.2.1⟩)
    (PocketStopMarked.isMarkedStop_stopTimeMInf h𝓦 hWad hRm hLm hGm hG hA hAG hcfgA hζA hψ hψm q)
    (PocketStopMarked.measurableSet_sup_iSup_of_locPrefixSigmaInf h𝓦 hWad hRm hLm hGm hG hA hAG hcfgA hζA hψ
      hψm q) (fun ω hT => ?_) (fun ω hω hq => ?_) (fun ω hω _ => (cfPocket_walls_props (hG ω (hAG hω))).1)
    (fun ω hω hq => ?_)
  · by_contra hl
    unfold PocketStopMarked.stopTimeMInf at hT
    rw [ite_eq_right hl] at hT
    exact lt_irrefl _ hT
  · rw [hlive ω ⟨hω, hq⟩]
    exact ENNReal.ofReal_lt_top
  · have hc := hcfgA ω hω
    have hP := hc.isReversePocketInf
    have hψ' : Sec6.IsJordanCoordInf (cfPocket (R ω) (L ω) r) (cfArcRInf (R ω) (L ω) r 0) (ψ ω) := by
      rw [IsChangeConfigInc.cfArcRInf_zero]
      exact hψ ω hω
    have himg := PocketUnionPt.image_inter_domain_ambTimeInf hP hc.attach hψ' q.coe_nonneg
      (by rw [ENNReal.ofReal_coe_nnreal]; exact hq)
    rintro z ⟨hzC, hzD⟩
    have hz' : ψ ω z ∈ ψ ω '' (cfPocket (R ω) (L ω) r ∩ (H \ fwdHull (fun s : ℝ => W' s.toNNReal ω)
        (PocketUnionPt.ambTimeInf (η ω) (cfPocket (R ω) (L ω) r) (firstHit (η ω) (cfArcRInf (R ω) (L ω) r 0))
          (ψ ω) q))) := by
      rw [himg]; exact hzD
    obtain ⟨z', ⟨hz'C, hz'D⟩, hz'eq⟩ := hz'
    have hzz : z' = z := (hψc ω hω).2.injOn hz'C hzC hz'eq
    subst hzz
    have h0 := inter_domain_ambTime0Inf hP hc.attach (ψ ω) q
    have hmem : z' ∈ cfPocket (R ω) (L ω) r ∩ (H \ fwdHull (fun s : ℝ => W' s.toNNReal ω)
        (ambTime0Inf (η ω) (cfPocket (R ω) (L ω) r) (firstHit (η ω) (cfArcRInf (R ω) (L ω) r 0)) (ψ ω) q)) :=
      h0 ▸ ⟨hz'C, hz'D⟩
    rw [hlive ω ⟨hω, hq⟩, ← stopHull0Inf_eq_regHull hc (hζA ω hω) q]
    exact hmem.2

end InteractingSLE.Sec7.R6Fin
