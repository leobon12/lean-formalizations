/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.PocketCouplingLaw

/-!
# Theorem 1.3's pocket word: the mean identification in pointwise form

Packet PROVE-STRIPSYS26. Specification §7.4, Aux. lemma 119's proof (`source/spec/p385-432.md` L50–L52, p. 387: "The
mean is therefore the bounded finite-piece Poisson extension of (PW13.1)") and Lemma 7.25's proof (pp. 413–414: "The
contained two-arc mean theorem applies at all enlarged stopping times with the exact inherited lifts").

`PocketCoupling.PocketMeanIdent` states the mean identification distributionally (the chart transport of the kernel mean
against test functions off the relative hull). The source, and the landed Aux. 27/28 step
(`Aux2728Pocket.ae_eqOn_of_sideLimit`: `v + u₀ = G ∘ c.1 − χ (c.2.2 + 2πn)` on the component), produce it **pointwise**:
a continuous representative `v` of the mean on the active domain `inv(ℍ ∖ K_q)` with

`v ∘ inv + a + k (lift ∘ inv) = 𝔥_q` on `ℍ ∖ K_q`, `𝔥_q = u_q ∘ f_q − χ(κ′) arg f_q′` the coupling mean (frozen
`couplingMean`).

This file proves the distributional form from the pointwise one (change of variables `Chart.integral_mul_pushTest`) and
restates the inputs and hPW with it.

## Main results

* `tsupport_pushTest_subset_image`, `continuous_mul_of_tsupport_subset`, **`chartTransport_eq_of_pointwise`**;
* `PocketMeanPt` (the pointwise mean identification, as an input), **`pocketMeanIdent_of_pt`**;
* `PocketUnionPtChartLaw`, `PocketUnionPtInput`, `PocketUnionPtInputInf`, `pocketUnionChartLaw_of_pt`,
  `pocketUnionInput_of_ptInput`, `pocketUnionInputInf_of_ptInputInf`;
* **`pocketWordEvolution_of_unionPtInput'`**: hPW from the pocket inputs in local-set and pointwise form.

Conditional helpers; they replace no source theorem. Ruling R48 respected (as in `PocketCoupling`).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter Topology
open QuantumZipper (H fwdHull zeroGFFTestCov)
open LQGMetric (DistOn TestOn IsZeroBoundaryGFF)
open scoped NNReal ENNReal

namespace InteractingSLE.Sec7.PocketCoupling

open PocketTraversal PocketAdapt PhaseSel Lemma71C

section Chart

variable {c : Chart}

/-- The support of a transported test function lies in the chart image of its support. -/
theorem tsupport_pushTest_subset_image (hc : c.IsConformal) (φ : TestOn upperHalfPlaneOpens) :
    tsupport (Chart.pushTest hc φ) ⊆ c.2.1 '' tsupport φ := by
  have hK : IsCompact (c.2.1 '' tsupport φ) :=
    φ.hasCompactSupport.isCompact.image_of_continuousOn (hc.1.continuousOn.mono φ.tsupport_subset)
  refine closure_minimal (fun z hz => ?_) hK.isClosed
  by_cases hd : z ∈ c.dom
  · have hz' : Chart.pushTest hc φ z ≠ 0 := hz
    rw [Chart.pushTest_apply_of_mem hc φ hd] at hz'
    exact ⟨c.1 z, subset_tsupport _ (right_ne_zero_of_mul hz'), hc.inv_fwd hd⟩
  · exact absurd (Chart.pushTest_apply_of_notMem hc φ hd) hz

/-- A function continuous on an open set times a test function supported in it is continuous. -/
theorem continuous_mul_of_tsupport_subset {f : ℂ → ℝ} {V : Set ℂ} (hVo : IsOpen V) (hf : ContinuousOn f V)
    (ψ : TestOn upperHalfPlaneOpens) (hψ : tsupport ψ ⊆ V) : Continuous fun w => f w * ψ w := by
  rw [continuous_iff_continuousAt]
  intro w
  by_cases hw : w ∈ V
  · exact ((hf w hw).continuousAt (hVo.mem_nhds hw)).mul ψ.continuous.continuousAt
  · have h0 : (fun y => ψ y) =ᶠ[𝓝 w] fun _ => 0 :=
      notMem_tsupport_iff_eventuallyEq.1 fun h => hw (hψ h)
    refine (continuousAt_const (y := (0 : ℝ))).congr ?_
    filter_upwards [h0] with y hy
    rw [hy, mul_zero]

/-- **The chart transport of a distribution given by a function on a chart subdomain**: if `M` is given on
`inv(V)` by a continuous `v`, and `v ∘ inv + a + k (lift ∘ inv) = F` on `V`, then the chart transport of `M` tested
against `ψ` supported in `V` is `∫ F ψ`. -/
theorem chartTransport_eq_of_pointwise (hc : c.IsConformal) (hℓ : ContinuousOn c.2.2 c.dom) (a k : ℝ)
    {M : DistOn upperHalfPlaneOpens} {V : Set ℂ} (hVo : IsOpen V) (hVH : V ⊆ H) {v : ℂ → ℝ}
    (hvc : ContinuousOn v (c.2.1 '' V))
    (hM : ∀ φ : TestOn upperHalfPlaneOpens, tsupport φ ⊆ c.2.1 '' V → M φ = ∫ z, v z * φ z) {F : ℂ → ℝ}
    (hpt : ∀ w ∈ V, v (c.2.1 w) + a + k * c.2.2 (c.2.1 w) = F w) (ψ : TestOn upperHalfPlaneOpens)
    (hψ : tsupport ψ ⊆ V) : Chart.chartTransport hc 1 a k M ψ = ∫ w, F w * ψ w := by
  have hlc : ContinuousOn (fun w => c.2.2 (c.2.1 w)) H := hc.continuousOn_lift_inv hℓ
  rw [Chart.chartTransport_apply', Chart.oneDist_apply,
    Chart.liftDist_apply (Chart.locallyIntegrableOn_of_continuousOn hlc),
    hM _ ((tsupport_pushTest_subset_image hc ψ).trans (image_mono hψ)), Chart.integral_mul_pushTest]
  have hvi : ContinuousOn (fun w => v (c.2.1 w)) V :=
    hvc.comp (hc.1.continuousOn.mono hVH) fun w hw => mem_image_of_mem _ hw
  have hi1 : Integrable (fun w => v (c.2.1 w) * ψ w) :=
    (continuous_mul_of_tsupport_subset hVo hvi ψ hψ).integrable_of_hasCompactSupport
      ψ.hasCompactSupport.mul_left
  have hi2 : Integrable (fun w => c.2.2 (c.2.1 w) * ψ w) :=
    (continuous_mul_of_tsupport_subset hVo (hlc.mono hVH) ψ hψ).integrable_of_hasCompactSupport
      ψ.hasCompactSupport.mul_left
  have hi3 : Integrable fun w => ψ w := ψ.continuous.integrable_of_hasCompactSupport ψ.hasCompactSupport
  have e : (fun w => F w * ψ w) =
      fun w => (v (c.2.1 w) * ψ w + a * ψ w) + k * (c.2.2 (c.2.1 w) * ψ w) := by
    funext w
    by_cases hw : w ∈ tsupport ψ
    · rw [← hpt w (hψ hw)]
      ring
    · rw [image_eq_zero_of_notMem_tsupport hw]
      ring
  have hi13 : Integrable (fun w => v (c.2.1 w) * ψ w + a * ψ w) := hi1.add (hi3.const_mul a)
  have hi2k : Integrable (fun w => k * (c.2.2 (c.2.1 w) * ψ w)) := hi2.const_mul k
  have hi3a : Integrable (fun w => a * ψ w) := hi3.const_mul a
  rw [e, integral_add hi13 hi2k, integral_add hi1 hi3a, integral_const_mul, integral_const_mul]
  ring

end Chart

/-! ### The pointwise mean identification -/

section Pt

variable {Ω : Type*}

/-- **The pointwise pocket mean identification** (Aux. lemmas 119–122 at every relative capacity time): almost surely on
`A ∩ {q < capLife γ}`, the kernel mean `M_q` has a continuous representative `v` on the active domain
`inv(ℍ ∖ K_q)`, and `v ∘ inv + a + k (lift ∘ inv)` is the canonical coupling mean of the word at the geometric force
coordinates of the marks on `ℍ ∖ K_q`. -/
def PocketMeanPt (κ : ℝ) {nL nR : ℕ} (ρL : Fin nL → ℝ) (ρR : Fin nR → ℝ) [MeasurableSpace Ω] (P : Measure Ω)
    (A : Set Ω) (γ : Ω → ℝ → ℂ) (xL : Ω → Fin nL → ℝ) (xR : Ω → Fin nR → ℝ) (c : Ω → Chart) (a k : ℝ)
    (M : ℝ≥0 → Ω → DistOn upperHalfPlaneOpens) : Prop :=
  ∀ q : ℝ≥0, ∀ᵐ ω ∂P, ω ∈ A → (q : ℝ≥0∞) < capLife (γ ω) → ∃ v : ℂ → ℝ,
    ContinuousOn v ((c ω).2.1 '' (H \ fwdHull (fun s : ℝ => segDriver (γ ω) s.toNNReal) q)) ∧
    (∀ φ : TestOn upperHalfPlaneOpens,
      tsupport φ ⊆ (c ω).2.1 '' (H \ fwdHull (fun s : ℝ => segDriver (γ ω) s.toNNReal) q) →
        M q ω φ = ∫ z, v z * φ z) ∧
    ∀ w ∈ H \ fwdHull (fun s : ℝ => segDriver (γ ω) s.toNNReal) q,
      v ((c ω).2.1 w) + a + k * (c ω).2.2 ((c ω).2.1 w) =
        couplingMean κ (fun s : ℝ => segDriver (γ ω) s.toNNReal) q
          (Restart.DomainMarkov.bheProc κ ρL ρR (fun t ω => segDriver (γ ω) t)
            (PocketTraversal.geomLW (fun t ω => segDriver (γ ω) t) xL)
            (PocketTraversal.geomRW (fun t ω => segDriver (γ ω) t) xR) ω q) w

/-- **The pocket mean identification from its pointwise form.** -/
theorem pocketMeanIdent_of_pt [MeasurableSpace Ω] {P : Measure Ω} {κ : ℝ} {nL nR : ℕ} {ρL : Fin nL → ℝ}
    {ρR : Fin nR → ℝ} {A : Set Ω} {γ : Ω → ℝ → ℂ} (hγ : ∀ ω ∈ A, IsDrivenCurve (γ ω)) {xL : Ω → Fin nL → ℝ}
    {xR : Ω → Fin nR → ℝ} {c : Ω → Chart} (hℓ : ∀ ω ∈ A, ContinuousOn (c ω).2.2 (c ω).dom) {a k : ℝ}
    {M : ℝ≥0 → Ω → DistOn upperHalfPlaneOpens} (hpt : PocketMeanPt κ ρL ρR P A γ xL xR c a k M) :
    PocketMeanIdent κ ρL ρR P A γ xL xR c a k M := by
  intro q ψ
  filter_upwards [hpt q] with ω hω hωA hav hc
  obtain ⟨hq, hdisj⟩ := hav
  obtain ⟨v, hvc, hM, hid⟩ := hω hωA hq
  have hVo : IsOpen (H \ fwdHull (fun s : ℝ => segDriver (γ ω) s.toNNReal) q) :=
    Coupling.MartMeans2.isOpen_H_diff_fwdHull_rpath (hγ ω hωA).segDriver_spec.2.1 hq
  exact chartTransport_eq_of_pointwise hc (hℓ ω hωA) a k hVo sdiff_subset hvc hM hid ψ
    fun z hz => ⟨ψ.tsupport_subset hz, fun h => hdisj.notMem_of_mem_left hz h⟩

end Pt

/-! ### The pocket inputs in local-set and pointwise form -/

section PtInputs

open WangWu Lemma71I PocketCoord PocketJordan PocketMarks

variable {Ω : Type*}

/-- **The pocket chart law in local-set and pointwise form**: a pocket chart, the marked union law, and the pointwise
mean identification for the local-set means shifted by `𝔥`. -/
def PocketUnionPtChartLaw (κ : ℝ) {nL nR : ℕ} (ρL : Fin nL → ℝ) (ρR : Fin nR → ℝ) (𝓦 : MeasurableSpace Ω)
    [mΩ : MeasurableSpace Ω] (P : Measure Ω) (A : Set Ω) (γ : Ω → ℝ → ℂ) (xL : Ω → Fin nL → ℝ)
    (xR : Ω → Fin nR → ℝ) (C : Ω → Set ℂ) (ψ : Ω → ℂ → ℂ) (h₀ : Ω → DistOn upperHalfPlaneOpens)
    (𝔥 : DistOn upperHalfPlaneOpens) : Prop :=
  ∃ (c : Ω → Chart) (a k : ℝ) (K : ℝ≥0 → Ω → Set ℂ) (ℋ : ℝ≥0 → MeasurableSpace Ω)
    (g : ℝ≥0 → Ω → DistOn upperHalfPlaneOpens),
    IsPocketChartOn 𝓦 A C ψ c ∧ PocketUnionLaw 𝓦 P A γ c h₀ K ℋ g ∧
      PocketMeanPt κ ρL ρR P A γ xL xR c a k fun q ω => g q ω + 𝔥

/-- **The pocket inputs in local-set and pointwise form on every word-shape event** (bounded change pocket):
`PocketUnionInput` with the pointwise mean identification. -/
def PocketUnionPtInput (κ rL rR : ℝ) (𝓦 : MeasurableSpace Ω) [mΩ : MeasurableSpace Ω] (P : Measure Ω)
    (R L : Ω → ℝ≥0 → ℂ) (r : ℝ≥0) (η : Ω → ℝ → ℂ) (G : Set Ω) (h₀ : Ω → DistOn upperHalfPlaneOpens)
    (𝔥 : DistOn upperHalfPlaneOpens) : Prop :=
  ∀ A : Set Ω, MeasurableSet[𝓦] A → A ⊆ G → 0 < P A → ∀ ψ : Ω → ℂ → ℂ,
    (∀ ω ∈ A, PocketWordAssembly.IsCfJordan (R ω) (L ω) r (ψ ω)) →
    @PocketWordAssembly.IsPointMeasurable Ω 𝓦 R L r G ψ →
    ((∀ ω ∈ A, discTime 1 ∈ Ioo (rightLo (R ω) (L ω) r) (rightHi (R ω) (L ω) r)) →
      PocketUnionPtChartLaw (16 / κ) (wordL2 κ (rs136Theta1 κ rL)) (wordR2 κ (rs136Theta2 κ rR)) 𝓦 P A
        (travAll R L r η ψ) (marksL2All R ψ) (marksRAll L r ψ) (fun ω => cfPocket (R ω) (L ω) r) ψ h₀ 𝔥) ∧
    ((∀ ω ∈ A, discTime 1 ∉ Ioo (rightLo (R ω) (L ω) r) (rightHi (R ω) (L ω) r)) →
      PocketUnionPtChartLaw (16 / κ) (wordL1 κ (rs136Theta1 κ rL)) (wordR2 κ (rs136Theta2 κ rR)) 𝓦 P A
        (travAll R L r η ψ) marksL1All (marksRAll L r ψ) (fun ω => cfPocket (R ω) (L ω) r) ψ h₀ 𝔥)

/-- **The pocket inputs in local-set and pointwise form, pocket opening at the flow seed** (`PocketUnionInputInf`
with the pointwise mean identification). -/
def PocketUnionPtInputInf (κ rL rR : ℝ) (𝓦 : MeasurableSpace Ω) [mΩ : MeasurableSpace Ω] (P : Measure Ω)
    (R L : Ω → ℝ≥0 → ℂ) (r : ℝ≥0) (η : Ω → ℝ → ℂ) (G : Set Ω) (h₀ : Ω → DistOn upperHalfPlaneOpens)
    (𝔥 : DistOn upperHalfPlaneOpens) : Prop :=
  ∀ A : Set Ω, MeasurableSet[𝓦] A → A ⊆ G → 0 < P A → ∀ ψ : Ω → ℂ → ℂ,
    (∀ ω ∈ A, PocketSeedOpen.IsCfJordanInf (R ω) (L ω) r (ψ ω)) →
    @PocketSeedOpen.IsPointMeasurableInf Ω 𝓦 R L r G ψ →
    ((∀ ω ∈ A, discTime 1 ∈ Ioo (rightLo (R ω) (L ω) r) (rightHi (R ω) (L ω) r)) →
      PocketUnionPtChartLaw (16 / κ) (wordL2 κ (rs136Theta1 κ rL)) (wordR2 κ (rs136Theta2 κ rR)) 𝓦 P A
        (travAllInf R L r η ψ) (marksL2All R ψ) (marksRAll L r ψ) (fun ω => cfPocket (R ω) (L ω) r) ψ h₀ 𝔥) ∧
    ((∀ ω ∈ A, discTime 1 ∉ Ioo (rightLo (R ω) (L ω) r) (rightHi (R ω) (L ω) r)) →
      PocketUnionPtChartLaw (16 / κ) (wordL1 κ (rs136Theta1 κ rL)) (wordR2 κ (rs136Theta2 κ rR)) 𝓦 P A
        (travAllInf R L r η ψ) marksL1All (marksRAll L r ψ) (fun ω => cfPocket (R ω) (L ω) r) ψ h₀ 𝔥)

end PtInputs

section PtThms

open WangWu Lemma71I PocketCoord PocketJordan PocketMarks

variable {Ω : Type*} {𝓦 : MeasurableSpace Ω} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
  {h₀ : Ω → DistOn upperHalfPlaneOpens} {𝔥 : DistOn upperHalfPlaneOpens}

/-- **The local-set form of the pocket chart law from its pointwise form.** -/
theorem pocketUnionChartLaw_of_pt {κ : ℝ} {nL nR : ℕ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ} {A : Set Ω}
    {γ : Ω → ℝ → ℂ} (hγ : ∀ ω ∈ A, IsDrivenCurve (γ ω)) {xL : Ω → Fin nL → ℝ} {xR : Ω → Fin nR → ℝ}
    {C : Ω → Set ℂ} {ψ : Ω → ℂ → ℂ} (hU : PocketUnionPtChartLaw κ ρL ρR 𝓦 P A γ xL xR C ψ h₀ 𝔥) :
    PocketUnionChartLaw κ ρL ρR 𝓦 P A γ xL xR C ψ h₀ 𝔥 := by
  obtain ⟨c, a, k, K, ℋ, g, hc, hL, hM⟩ := hU
  exact ⟨c, a, k, K, ℋ, g, hc, hL, pocketMeanIdent_of_pt hγ (fun ω hω => (hc.1 ω hω).2.2.2) hM⟩

/-- **The pocket inputs in local-set form from their pointwise form** (bounded change pocket). -/
theorem pocketUnionInput_of_ptInput {κ rL rR : ℝ} {R L : Ω → ℝ≥0 → ℂ} {r : ℝ≥0} {W : Ω → ℝ → ℝ}
    {η : Ω → ℝ → ℂ} {G : Set Ω} (hcfg : ∀ ω ∈ G, PocketWordAssembly.IsCfPocketConfig (R ω) (L ω) r (W ω) (η ω))
    (hin : PocketUnionPtInput κ rL rR 𝓦 P R L r η G h₀ 𝔥) : PocketUnionInput κ rL rR 𝓦 P R L r η G h₀ 𝔥 :=
  fun A hA hAG hPA ψ hψ hψm =>
    have hγ : ∀ ω ∈ A, IsDrivenCurve (travAll R L r η ψ ω) := fun ω hω =>
      ((hcfg ω (hAG hω)).isDrivenCurve (hψ ω hω)).1
    ⟨fun hs => pocketUnionChartLaw_of_pt hγ ((hin A hA hAG hPA ψ hψ hψm).1 hs),
      fun hs => pocketUnionChartLaw_of_pt hγ ((hin A hA hAG hPA ψ hψ hψm).2 hs)⟩

/-- **The pocket inputs in local-set form from their pointwise form, pocket opening at the flow seed.** -/
theorem pocketUnionInputInf_of_ptInputInf {κ rL rR : ℝ} {R L : Ω → ℝ≥0 → ℂ} {r : ℝ≥0} {W : Ω → ℝ → ℝ}
    {η : Ω → ℝ → ℂ} {G : Set Ω} (hcfg : ∀ ω ∈ G, PocketSeedOpen.IsCfPocketConfigInf (R ω) (L ω) r (W ω) (η ω))
    (hin : PocketUnionPtInputInf κ rL rR 𝓦 P R L r η G h₀ 𝔥) : PocketUnionInputInf κ rL rR 𝓦 P R L r η G h₀ 𝔥 :=
  fun A hA hAG hPA ψ hψ hψm =>
    have hγ : ∀ ω ∈ A, IsDrivenCurve (travAllInf R L r η ψ ω) := fun ω hω =>
      ((hcfg ω (hAG hω)).isDrivenCurve (hψ ω hω)).1
    ⟨fun hs => pocketUnionChartLaw_of_pt hγ ((hin A hA hAG hPA ψ hψ hψm).1 hs),
      fun hs => pocketUnionChartLaw_of_pt hγ ((hin A hA hAG hPA ψ hψ hψm).2 hs)⟩

end PtThms

open WangWu Lemma71I PocketCoord PocketJordan PocketMarks in
/-- **hPW from the pocket inputs in local-set and pointwise form** (`κ′ > 4`, both-low seed weights; Lemma 7.25's proof
with Aux. lemmas 119–125 and 130). -/
theorem pocketWordEvolution_of_unionPtInput'.{v} {κ' rL rR : ℝ} (hκ' : 4 < κ') (hL : -2 < rL)
    (hLd : rL < κ' / 2 - 4) (hR : -2 < rR) (hRd : rR < κ' / 2 - 4)
    {Ω : Type v} {𝓦 : MeasurableSpace Ω} [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] (h𝓦 : 𝓦 ≤ mΩ) {R L : Ω → ℝ≥0 → ℂ} {r : ℝ≥0}
    (hRm : ∀ t, Measurable[𝓦] fun ω => R ω t) (hLm : ∀ t, Measurable[𝓦] fun ω => L ω t)
    {G : Set Ω} (hGm : MeasurableSet[𝓦] G) (hPG : 0 < P G) {W : Ω → ℝ → ℝ} {η : Ω → ℝ → ℂ}
    (hconf : ∀ ω ∈ G, IsChangeConfigInc (R ω) (L ω) r)
    (hcfg : ∀ ω ∈ G, 0 < rightLo (R ω) (L ω) r → PocketWordAssembly.IsCfPocketConfig (R ω) (L ω) r (W ω) (η ω))
    (hcfgI : ∀ ω ∈ G, rightLo (R ω) (L ω) r = 0 → PocketSeedOpen.IsCfPocketConfigInf (R ω) (L ω) r (W ω) (η ω))
    (hηm : ∀ u, 0 ≤ u → Measurable fun ω => η ω u) {h₀ : Ω → DistOn upperHalfPlaneOpens}
    (hh₀ : IsZeroBoundaryGFF upperHalfPlaneOpens h₀ P) (𝔥 : DistOn upperHalfPlaneOpens)
    (hin : PocketUnionPtInput (16 / κ') rL rR 𝓦 P R L r η {ω | ω ∈ G ∧ 0 < rightLo (R ω) (L ω) r} h₀ 𝔥)
    (hinI : PocketUnionPtInputInf (16 / κ') rL rR 𝓦 P R L r η {ω | ω ∈ G ∧ ¬ 0 < rightLo (R ω) (L ω) r} h₀ 𝔥) :
    Lemma725Ref.PocketWordEvolution.{v} κ' rL rR :=
  pocketWordEvolution_of_unionInput' hκ' hL hLd hR hRd h𝓦 hRm hLm hGm hPG hconf hcfg hcfgI hηm hh₀ 𝔥
    (pocketUnionInput_of_ptInput (fun ω hω => hcfg ω hω.1 hω.2) hin)
    (pocketUnionInputInf_of_ptInputInf (fun ω hω => hcfgI ω hω.1
      (le_antisymm (not_lt.1 hω.2) (hconf ω hω.1).changeCorner_props.1.1)) hinI)

end InteractingSLE.Sec7.PocketCoupling
