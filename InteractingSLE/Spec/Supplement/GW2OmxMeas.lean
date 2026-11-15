/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.WalkInfMeas
import InteractingSLE.Spec.Sec7.LocalExtKJoint

/-!
# GW2's open lines: measurability of a chart mean paired with a test function

Packet PROVE-GW2-STAGEMEAN, R120 round (item 4 of the per-stage plan). The kernel chain
(`GW2Omx.ae_of_kernel_curX`) needs a MEASURABLE event, so the stage-mean pairing `ω ↦ ∫ M ω · φ` must be measurable
where it is read. The stage mean is a chart mean: the bounded harmonic extension of a random word read through a
random measurable chart `C` (the stage chart moved to the clock), minus `χ` times the chart's own Loewner lift, minus
`u₀`, the offset and `kc` times the stage chart's lift. Masked by the domain of `C`:

* **`measurable_integral_masked`**: a function measurable at each point on the domain events and continuous on the
  (open) domains, masked by the domain of a measurable random chart, paired with a test function, is measurable
  (Carathéodory, `WalkInf.measurable_masked_prod`, then `StronglyMeasurable.integral_prod_right'`);
* `integral_masked_eq`: off the domain the test function vanishes, so the masked pairing is the pairing;
* `chartMeanFn` and **`measurable_integral_chartMeanFn`**: the chart mean of a measurable random word (positions
  `v`) satisfies both hypotheses.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Filter Set Topology
open scoped NNReal ENNReal
open LQGMetric (DistOn TestOn)
open QuantumZipper (H chiC)

namespace InteractingSLE.Theorem14.GW2Omx

/-- **The pairing of a masked function with a test function is measurable** (Carathéodory on the random domain of a
measurable chart). -/
theorem measurable_integral_masked {Ω : Type*} {m : MeasurableSpace Ω} {C : Ω → Chart}
    (hC : WalkInf.IsMeasChart m C) {F : Ω → ℂ → ℝ}
    (hFm : ∀ z, Measurable[m] ({ω | z ∈ (C ω).dom}.indicator fun ω => F ω z))
    (hFc : ∀ ω, ContinuousOn (F ω) (C ω).dom) (φ : TestOn upperHalfPlaneOpens) :
    Measurable[m] fun ω =>
      ∫ z, ({p : Ω × ℂ | p.2 ∈ (C p.1).dom}.indicator (fun p => F p.1 p.2)) (ω, z) * φ z := by
  let _ : MeasurableSpace Ω := m
  have h := WalkInf.measurable_masked_prod hC hFm hFc
  have h2 : Measurable fun p : Ω × ℂ =>
      ({p : Ω × ℂ | p.2 ∈ (C p.1).dom}.indicator (fun p => F p.1 p.2)) p * φ p.2 :=
    h.mul (φ.continuous.measurable.comp measurable_snd)
  exact (h2.stronglyMeasurable.integral_prod_right' (ν := volume)).measurable

/-- **Off the domain the test function vanishes**: the masked pairing is the pairing. -/
theorem integral_masked_eq {Ω : Type*} {C : Ω → Chart} {F : Ω → ℂ → ℝ} {φ : TestOn upperHalfPlaneOpens} {ω : Ω}
    (hsupp : tsupport φ ⊆ (C ω).dom) :
    ∫ z, ({p : Ω × ℂ | p.2 ∈ (C p.1).dom}.indicator (fun p => F p.1 p.2)) (ω, z) * φ z =
      ∫ z, F ω z * φ z := by
  refine integral_congr_ae (Eventually.of_forall fun z => ?_)
  by_cases hz : z ∈ tsupport φ
  · have hd : (ω, z) ∈ {p : Ω × ℂ | p.2 ∈ (C p.1).dom} := hsupp hz
    simp only [indicator_of_mem hd]
  · simp only [image_eq_zero_of_notMem_tsupport hz, mul_zero]

/-- **The chart mean** of positions `v` read through the chart `C`, with the reference chart `cs`. -/
def chartMeanFn {Ω : Type*} {nL nR : ℕ} (κ : ℝ) (ρL : Fin nL → ℝ) (ρR : Fin nR → ℝ)
    (v : Ω → (Fin nL → ℝ) × (Fin nR → ℝ)) (C cs : Ω → Chart) (u₀ : ℂ → ℝ) (σa kc : ℝ) (ω : Ω) (z : ℂ) : ℝ :=
  LocalExt.bheAt κ ρL ρR (v ω).1 (v ω).2 ((C ω).1 z) - chiC κ * ((C ω).2.2 z - (cs ω).2.2 z) - u₀ z - σa -
    kc * (cs ω).2.2 z

/-- The masked chart mean at one point is measurable. -/
theorem measurable_indicator_chartMeanFn {Ω : Type*} {m : MeasurableSpace Ω} {nL nR : ℕ} (κ : ℝ)
    (ρL : Fin nL → ℝ) (ρR : Fin nR → ℝ) {v : Ω → (Fin nL → ℝ) × (Fin nR → ℝ)} (hv : Measurable[m] v)
    {C cs : Ω → Chart} (hC : WalkInf.IsMeasChart m C) (hcs : WalkInf.IsMeasChart m cs)
    (hsub : ∀ ω, ((C ω).dom : Set ℂ) ⊆ (cs ω).dom) (u₀ : ℂ → ℝ) (σa kc : ℝ) (z : ℂ) :
    Measurable[m] ({ω | z ∈ (C ω).dom}.indicator fun ω => chartMeanFn κ ρL ρR v C cs u₀ σa kc ω z) := by
  have hDm : MeasurableSet[m] {ω | z ∈ (C ω).dom} := hC.2.2.2.1 z
  have h1 : Measurable[m] ({ω | z ∈ (C ω).dom}.indicator fun ω => (C ω).1 z) := hC.2.2.2.2.1 z
  have h2 : Measurable[m] ({ω | z ∈ (C ω).dom}.indicator fun ω => (C ω).2.2 z) := hC.2.2.2.2.2.2 z
  have hcs3 : Measurable[m] ({ω | z ∈ (cs ω).dom}.indicator fun ω => (cs ω).2.2 z) := hcs.2.2.2.2.2.2 z
  have e3 : {ω | z ∈ (C ω).dom}.indicator (fun ω => (cs ω).2.2 z) =
      {ω | z ∈ (C ω).dom}.indicator ({ω | z ∈ (cs ω).dom}.indicator fun ω => (cs ω).2.2 z) := by
    funext ω
    by_cases hω : z ∈ (C ω).dom
    · have hω' : z ∈ (cs ω).dom := hsub ω hω
      simp only [indicator, mem_ofPred_eq, hω, hω', ↓reduceIte]
    · simp only [indicator, mem_ofPred_eq, hω, ↓reduceIte]
  have h3 : Measurable[m] ({ω | z ∈ (C ω).dom}.indicator fun ω => (cs ω).2.2 z) := by
    rw [e3]
    exact Measurable.indicator hcs3 hDm
  have hB : Measurable[m] ((fun p : ((Fin nL → ℝ) × (Fin nR → ℝ)) × ℂ => LocalExt.bheAt κ ρL ρR p.1.1 p.1.2 p.2) ∘
      fun ω => (v ω, {ω | z ∈ (C ω).dom}.indicator (fun ω => (C ω).1 z) ω)) :=
    @Measurable.comp Ω _ _ m _ _ _ _ (LocalExt.measurable_bheAt_word κ ρL ρR) (hv.prodMk h1)
  have e : {ω | z ∈ (C ω).dom}.indicator (fun ω => chartMeanFn κ ρL ρR v C cs u₀ σa kc ω z) =
      {ω | z ∈ (C ω).dom}.indicator (fun ω => ((fun p : ((Fin nL → ℝ) × (Fin nR → ℝ)) × ℂ =>
          LocalExt.bheAt κ ρL ρR p.1.1 p.1.2 p.2) ∘
            fun ω => (v ω, {ω | z ∈ (C ω).dom}.indicator (fun ω => (C ω).1 z) ω)) ω -
        chiC κ * ({ω | z ∈ (C ω).dom}.indicator (fun ω => (C ω).2.2 z) ω -
          {ω | z ∈ (C ω).dom}.indicator (fun ω => (cs ω).2.2 z) ω) - u₀ z - σa -
        kc * {ω | z ∈ (C ω).dom}.indicator (fun ω => (cs ω).2.2 z) ω) := by
    funext ω
    by_cases hω : z ∈ (C ω).dom
    · simp only [indicator, mem_ofPred_eq, hω, ↓reduceIte, chartMeanFn, Function.comp_apply]
    · simp only [indicator, mem_ofPred_eq, hω, ↓reduceIte]
  rw [e]
  refine Measurable.indicator ?_ hDm
  exact (((hB.sub (measurable_const.mul (h2.sub h3))).sub measurable_const).sub measurable_const).sub
    (measurable_const.mul h3)

/-- The chart mean is continuous on the domain of `C`. -/
theorem continuousOn_chartMeanFn {Ω : Type*} {m : MeasurableSpace Ω} {nL nR : ℕ} (κ : ℝ)
    (ρL : Fin nL → ℝ) (ρR : Fin nR → ℝ) (v : Ω → (Fin nL → ℝ) × (Fin nR → ℝ))
    {C cs : Ω → Chart} (hC : WalkInf.IsMeasChart m C) (hcs : WalkInf.IsMeasChart m cs)
    (hsub : ∀ ω, ((C ω).dom : Set ℂ) ⊆ (cs ω).dom) {u₀ : ℂ → ℝ} (hu₀ : ContinuousOn u₀ H) (σa kc : ℝ) (ω : Ω) :
    ContinuousOn (chartMeanFn κ ρL ρR v C cs u₀ σa kc ω) (C ω).dom := by
  have hcf := hC.1 ω
  have hdomH : ((C ω).dom : Set ℂ) ⊆ H := hcf.dom_subset
  have hfwd : ContinuousOn (C ω).1 (C ω).dom := hcf.differentiableOn_fwd.continuousOn
  have hmaps : MapsTo (C ω).1 (C ω).dom H := fun z hz => hcf.fwd_mem hz
  have hU : ContinuousOn (LocalExt.bheAt κ ρL ρR (v ω).1 (v ω).2) H := fun y hy =>
    ((LocalExt.isBoundedHarmonicExtension_bheAt κ ρL ρR (v ω).1 (v ω).2).1 y hy).1.continuousAt.continuousWithinAt
  have hcs2 : ContinuousOn (cs ω).2.2 (C ω).dom := (hcs.2.1 ω).mono (hsub ω)
  exact ((((hU.comp hfwd hmaps).sub (continuousOn_const.mul ((hC.2.1 ω).sub hcs2))).sub
    (hu₀.mono hdomH)).sub continuousOn_const).sub (continuousOn_const.mul hcs2)

/-- **The chart mean of a measurable random word paired with a test function is measurable** (masked by the domain
of `C`). -/
theorem measurable_integral_chartMeanFn {Ω : Type*} {m : MeasurableSpace Ω} {nL nR : ℕ} (κ : ℝ)
    (ρL : Fin nL → ℝ) (ρR : Fin nR → ℝ) {v : Ω → (Fin nL → ℝ) × (Fin nR → ℝ)} (hv : Measurable[m] v)
    {C cs : Ω → Chart} (hC : WalkInf.IsMeasChart m C) (hcs : WalkInf.IsMeasChart m cs)
    (hsub : ∀ ω, ((C ω).dom : Set ℂ) ⊆ (cs ω).dom) {u₀ : ℂ → ℝ} (hu₀ : ContinuousOn u₀ H) (σa kc : ℝ)
    (φ : TestOn upperHalfPlaneOpens) :
    Measurable[m] fun ω => ∫ z, ({p : Ω × ℂ | p.2 ∈ (C p.1).dom}.indicator
      (fun p => chartMeanFn κ ρL ρR v C cs u₀ σa kc p.1 p.2)) (ω, z) * φ z :=
  measurable_integral_masked hC (measurable_indicator_chartMeanFn κ ρL ρR hv hC hcs hsub u₀ σa kc)
    (continuousOn_chartMeanFn κ ρL ρR v hC hcs hsub hu₀ σa kc) φ

end InteractingSLE.Theorem14.GW2Omx
