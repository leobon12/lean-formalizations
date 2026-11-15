/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.R5EnlTrace
import InteractingSLE.Spec.Sec7.Lemma72CLocal

/-!
# The enlarged-stop increment law: reference → current (R.5, generic)

Packet PROVE-R5-ENLARGED. Lemma R.5's proof (`source/spec/p433-480.md` L1014, p. 475): "For each `s`, apply the
nested marked local-set law to the enlarged stop `T ∨ s`, exactly as in Aux. 35. In the `s` chart, the subsequently
added local set avoids the selected half-disc; zero-boundary decay therefore preserves the old boundary germ there.
Intersect these countably many probability-one statements before choosing the suitable member from the realized
geometry." Aux. 35's proof (`p145-192.md` L955–L960, `p193-240.md` L5–L32, pp. 192–194) gives the three steps:

1. **two-step construction** — given the earlier record `𝒢 ⊆ 𝒥`, the reference residual `h − 𝒞_B` is a zero-boundary
   GFF in `D ∖ B`, and the increment `A ∖ B` is a local-set reveal of it with mean `𝒞_A − 𝒞_B`
   (`hasOldChartIncrementLawOn_of_retained_kernels`, read in the reference chart, conditioned on the reference event);
2. **the enlarged stop** — the marked law at `T ∨ s` retains the reference record (the stopped history at `s` and the
   reference germ), so `𝒢 ⊆ 𝒥` holds globally even where `s > T`;
3. **restriction** — on `{s ≤ T}` the enlarged stop is `T` itself: the sets agree and the retained records have the
   same trace (`measurableSet_inter_germSigma_sup_iff`), so the means agree there
   (`ae_eq_of_isCondZeroBoundaryGFF_of_trace`); every version of the local-set means is the retained one
   (`ae_eq_of_isLocalSetMean_of_retained`).

## Main results

* **`hasOldChartIncrementLawOn_of_enlarged_kernels`** — the conditioned increment law for **every** version of the
  reference and current local-set means, from the three retained kernels (reference at `ℋ₀`, enlarged stop at
  `ℋ₁ ≥ ℋ₀`, current at `ℋK`), the trace agreement of `ℋK` and `ℋ₁` on `E`, the reference chart on `G`, and the
  record-transport inputs `hAdded`, `hGerm` for the explicit reference mean `g₀`;
* **`hasOldChartIncrementLawOn_of_enlarged_marked`** — the same from the **marked laws** (history-marked locality,
  Aux. 18) of the enlarged and current sets: their kernels are built (`exists_germLaw_of_isHistoryAvoidanceLocal`)
  and the trace agreement is reduced to the agreement of the sets and of the marks on `E`.

Conditional helpers with distinct names; nothing here uses Theorem 1.2/1.3 or any `*_of_param` (R43, R48).
-/

set_option autoImplicit false
noncomputable section

open MeasureTheory ProbabilityTheory Set Filter Topology Metric
open QuantumZipper (H)
open LQGMetric (DistOn TestOn IsZeroBoundaryGFF)

namespace InteractingSLE.Sec7.R5Enl

open LocalSets PocketStopSide WholeField

section Law

variable {Ω : Type*} {ℋ₀ ℋ₁ ℋK ℋ' ℋc : MeasurableSpace Ω} [mΩ : MeasurableSpace Ω] {P : Measure Ω}

/-- **R.5's enlarged-stop increment law (reference → current), from retained kernels.**

* reference `B`: a germ-measurable mean `g₀`, harmonic off `B`, with `h = g₀ + GFF_{ℍ∖B}` given `ℋ₀ ⊇ germSigma B h`;
* enlarged stop `K'`: an `ℋ₁`-measurable mean `g₁` (`ℋ₀ ≤ ℋ₁`), harmonic off `K'`, `h = g₁ + GFF_{ℍ∖K'}` given `ℋ₁`;
* current `K`: a germ-measurable mean `gK` with `h = gK + GFF_{ℍ∖K}` given `ℋK ⊇ germSigma K h`;
* on `E ∈ ℋK`: `K = K'` almost surely and `ℋK`, `ℋ₁` have the same trace;
* the reference chart `old` on `G ∈ ℋ₀`, conformal with domain `ℍ ∖ B` containing `ℍ ∖ K'`, measurable for `ℋ₀`;
* the added set and the residual germ of the extended charts are retained by `ℋ₁` (`hAdded`, `hGerm`).

Then for every `M ⊆ G ∩ E` on which the current chart's domain is `ℍ ∖ K`, and every version of the two local-set
means, the conditioned increment law holds. -/
theorem hasOldChartIncrementLawOn_of_enlarged_kernels [IsProbabilityMeasure P]
    {h : Ω → DistOn upperHalfPlaneOpens} (hh : Measurable h)
    {B K K' : Ω → Set ℂ} {g₀ g₁ gK : Ω → DistOn upperHalfPlaneOpens}
    (hB₀ : germSigma B h ≤ ℋ₀) (hg₀ : Measurable[germSigma B h] g₀)
    (hHarm₀ : ∀ᵐ ω ∂P, IsHarmonicDistOn (g₀ ω) (H \ B ω))
    (hK₀ : IsCondZeroBoundaryGFF P ℋ₀ (fun ω => H \ B ω) fun ω => h ω - g₀ ω)
    (hInfo : ℋ₀ ≤ ℋ₁) (hℋ₁ : ℋ₁ ≤ mΩ) (hg₁ : Measurable[ℋ₁] g₁)
    (hHarm₁ : ∀ᵐ ω ∂P, IsHarmonicDistOn (g₁ ω) (H \ K' ω))
    (hK₁ : IsCondZeroBoundaryGFF P ℋ₁ (fun ω => H \ K' ω) fun ω => h ω - g₁ ω)
    (hKK : germSigma K h ≤ ℋK) (hℋK : ℋK ≤ mΩ) (hgK : Measurable[germSigma K h] gK)
    (hKKer : IsCondZeroBoundaryGFF P ℋK (fun ω => H \ K ω) fun ω => h ω - gK ω)
    {E : Set Ω} (hE : MeasurableSet[ℋK] E)
    (htrace : ∀ t, MeasurableSet[ℋK] (E ∩ t) ↔ MeasurableSet[ℋ₁] (E ∩ t))
    (hKE : ∀ᵐ ω ∂P, ω ∈ E → K ω = K' ω)
    {G : Set Ω} (hG : MeasurableSet[ℋ₀] G) {old : Ω → Chart} (hOld : ∀ ω ∈ G, (old ω).IsConformal)
    (hdom : ∀ z, MeasurableSet[ℋ₀] (G ∩ {ω | z ∈ (old ω).dom}))
    (hfwd : ∀ z, Measurable[ℋ₀] ((G ∩ {ω | z ∈ (old ω).dom}).indicator fun ω => (old ω).1 z))
    (hOldDom : ∀ ω ∈ G, ((old ω).dom : Set ℂ) = H \ B ω)
    (hK'o : ∀ ω ∈ G, IsOpen (H \ K' ω)) (hNest : ∀ ω ∈ G, H \ K' ω ⊆ H \ B ω)
    (hAdded : Measurable[ℋ₁, hittingSigma]
      (globalOldChartAddedSet (oldOn G old) (curOn G fun ω => H \ K' ω)))
    (hGerm : germSigma (globalOldChartAddedSet (oldOn G old) (curOn G fun ω => H \ K' ω))
      (fun ω => Chart.pullField (isConformal_oldOn hOld ω) (h ω - g₀ ω)) ≤ ℋ₁)
    {M : Set Ω} (hMG : M ⊆ G) (hME : M ⊆ E) {current : Ω → Chart}
    (hcur : ∀ ω ∈ M, ((current ω).dom : Set ℂ) = H \ K ω) :
    ∀ gOld : Ω → DistOn upperHalfPlaneOpens, IsLocalSetMean B h P gOld →
      ∀ gNow : Ω → DistOn upperHalfPlaneOpens, IsLocalSetMean K h P gNow →
        HasOldChartIncrementLawOn P M old current gOld gNow := by
  intro gOld hgOld gNow hgNow
  have hℋ₀ : ℋ₀ ≤ mΩ := hInfo.trans hℋ₁
  -- step 1: the two-step construction in the reference chart, conditioned on `G`
  have hL := hasOldChartIncrementLawOn_of_retained_kernels (P := P) hInfo hℋ₁ hG hOld hdom hfwd
    (U := fun ω => H \ K' ω) hK'o (fun ω hω => (hNest ω hω).trans (hOldDom ω hω).symm.subset) hh
    ((hg₀.mono hB₀ le_rfl).mono hInfo le_rfl) hg₁
    (by filter_upwards [hHarm₀] with ω hω hG'; rwa [hOldDom ω hG'])
    (hHarm₁.mono fun ω hω _ => hω) (Uold := fun ω => H \ B ω)
    (Eventually.of_forall fun ω hG' => (hOldDom ω hG').symm) hK₀ hK₁ hAdded hGerm hMG
    (current := curOn G fun ω => H \ K' ω)
    (fun ω hM => dom_curOn_of_mem (hMG hM) (hK'o ω (hMG hM))
      ((hNest ω (hMG hM)).trans sdiff_subset))
  -- step 3: every version of the means is the retained one, and the enlarged mean is the current one on `E`
  have hOldEq : gOld =ᵐ[P] g₀ := ae_eq_of_isLocalSetMean_of_retained hh hgOld hB₀ hℋ₀ hg₀ hK₀
  have hNowEq : gNow =ᵐ[P] gK := ae_eq_of_isLocalSetMean_of_retained hh hgNow hKK hℋK hgK hKKer
  have hEnl : ∀ᵐ ω ∂P, ω ∈ E → gK ω = g₁ ω :=
    ae_eq_of_isCondZeroBoundaryGFF_of_trace hℋK hℋ₁ hE htrace hh (hgK.mono hKK le_rfl) hg₁ hKKer hK₁
      (by filter_upwards [hKE] with ω hω hωE; rw [hω hωE])
  refine hL.congr_on ?_
  filter_upwards [hOldEq, hNowEq, hEnl, hKE] with ω e0 eN eE eK hM
  refine ⟨rfl, ?_, e0.symm, ?_⟩
  · rw [dom_curOn_of_mem (hMG hM) (hK'o ω (hMG hM)) ((hNest ω (hMG hM)).trans sdiff_subset),
      hcur ω hM, eK (hME hM)]
  · rw [eN, eE (hME hM)]

/-- **R.5's enlarged-stop increment law from the marked laws.** The enlarged set `K'` and the current set `K` satisfy
the history-marked avoidance criterion (Aux. 18) for the marks `ℋ'` and `ℋc`; their kernels are retained by
`germSigma K' h ⊔ ℋ'` and `germSigma K h ⊔ ℋc`. The enlarged record retains the reference record (`hInfo`). On `E`
(measurable for both records) the sets agree and the marks have the same trace. The reference mean `g₀` is explicit
(e.g. from `Lemma72C.exists_germLaw_of_isHistoryAvoidanceLocal` for the reference's marked law), since the
record-transport input `hGerm` is a statement about its residual. -/
theorem hasOldChartIncrementLawOn_of_enlarged_marked [IsProbabilityMeasure P]
    {h : Ω → DistOn upperHalfPlaneOpens} (hh : IsZeroBoundaryGFF upperHalfPlaneOpens h P)
    {B K K' : Ω → Set ℂ} {g₀ : Ω → DistOn upperHalfPlaneOpens}
    (hB₀ : germSigma B h ≤ ℋ₀) (hg₀ : Measurable[germSigma B h] g₀)
    (hHarm₀ : ∀ᵐ ω ∂P, IsHarmonicDistOn (g₀ ω) (H \ B ω))
    (hK₀ : IsCondZeroBoundaryGFF P ℋ₀ (fun ω => H \ B ω) fun ω => h ω - g₀ ω)
    (hℋ' : ℋ' ≤ mΩ) (hℋc : ℋc ≤ mΩ)
    (hK'm : Measurable[mΩ, hittingSigma] K') (hK'reg : ∀ᵐ ω ∂P, K' ω ⊆ H ∧ IsOpen (H \ K' ω))
    (hK'loc : IsHistoryAvoidanceLocal ℋ' K' h P)
    (hKm : Measurable[mΩ, hittingSigma] K) (hKreg : ∀ᵐ ω ∂P, K ω ⊆ H ∧ IsOpen (H \ K ω))
    (hKloc : IsHistoryAvoidanceLocal ℋc K h P)
    (hInfo : ℋ₀ ≤ germSigma K' h ⊔ ℋ')
    {E : Set Ω} (hE : MeasurableSet[germSigma K h ⊔ ℋc] E) (hE' : MeasurableSet[germSigma K' h ⊔ ℋ'] E)
    (hKE : ∀ ω ∈ E, K ω = K' ω)
    (hmarks : MeasurableSpace.comap ((↑) : E → Ω) ℋc = MeasurableSpace.comap ((↑) : E → Ω) ℋ')
    {G : Set Ω} (hG : MeasurableSet[ℋ₀] G) {old : Ω → Chart} (hOld : ∀ ω ∈ G, (old ω).IsConformal)
    (hdom : ∀ z, MeasurableSet[ℋ₀] (G ∩ {ω | z ∈ (old ω).dom}))
    (hfwd : ∀ z, Measurable[ℋ₀] ((G ∩ {ω | z ∈ (old ω).dom}).indicator fun ω => (old ω).1 z))
    (hOldDom : ∀ ω ∈ G, ((old ω).dom : Set ℂ) = H \ B ω)
    (hK'o : ∀ ω ∈ G, IsOpen (H \ K' ω)) (hNest : ∀ ω ∈ G, H \ K' ω ⊆ H \ B ω)
    (hAdded : Measurable[germSigma K' h ⊔ ℋ', hittingSigma]
      (globalOldChartAddedSet (oldOn G old) (curOn G fun ω => H \ K' ω)))
    (hGerm : germSigma (globalOldChartAddedSet (oldOn G old) (curOn G fun ω => H \ K' ω))
      (fun ω => Chart.pullField (isConformal_oldOn hOld ω) (h ω - g₀ ω)) ≤ germSigma K' h ⊔ ℋ')
    {M : Set Ω} (hMG : M ⊆ G) (hME : M ⊆ E) {current : Ω → Chart}
    (hcur : ∀ ω ∈ M, ((current ω).dom : Set ℂ) = H \ K ω) :
    ∀ gOld : Ω → DistOn upperHalfPlaneOpens, IsLocalSetMean B h P gOld →
      ∀ gNow : Ω → DistOn upperHalfPlaneOpens, IsLocalSetMean K h P gNow →
        HasOldChartIncrementLawOn P M old current gOld gNow := by
  obtain ⟨g₁, hg₁, hHarm₁, hK₁⟩ := Lemma72C.exists_germLaw_of_isHistoryAvoidanceLocal hh hK'm hℋ' hK'loc hK'reg
  obtain ⟨gK, hgK, -, hKKer⟩ := Lemma72C.exists_germLaw_of_isHistoryAvoidanceLocal hh hKm hℋc hKloc hKreg
  exact hasOldChartIncrementLawOn_of_enlarged_kernels hh.measurable hB₀ hg₀ hHarm₀ hK₀ hInfo
    (sup_le (germSigma_le hK'm hh.measurable) hℋ') (hg₁.mono le_sup_left le_rfl) hHarm₁ hK₁ le_sup_left
    (sup_le (germSigma_le hKm hh.measurable) hℋc) hgK hKKer hE
    (measurableSet_inter_germSigma_sup_iff hKE hmarks hE hE')
    (Eventually.of_forall hKE) hG hOld hdom hfwd hOldDom hK'o hNest hAdded hGerm hMG hME hcur

end Law

end InteractingSLE.Sec7.R5Enl
