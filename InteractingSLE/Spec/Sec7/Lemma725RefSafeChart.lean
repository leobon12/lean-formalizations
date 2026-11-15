/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.Lemma725RefSafeWord
import InteractingSLE.Spec.Sec7.PocketStopActive
import InteractingSLE.Spec.Restart.DomainMarkovMeanLoc

/-!
# The pocket's (S) and (L) from the field on the ambient space

Packet PROVE-LEMMA725REF3. Specification §7.4: Aux. lemma 124 (`source/spec/p385-432.md` L171–L196, pp. 393–394),
Aux. lemma 125's proof (L213–L250, pp. 396–397: "The canonical law survives the exterior reveal … To justify the
raw-range input first, project the full marked decomposition of `B ∪ R_{T(S)}` onto `H(C)` in (ER1) … This proves
marked relative raw-range locality") and Lemma 7.25's proof (pp. 413–414).

On the ambient probability space, with the walls' σ-algebra `𝓦`, a walls-event `A` of positive probability, the erased
counterflow traversal `γ` of the pocket, the pocket chart `c` and the ambient field `h` (a zero-boundary GFF plus a
harmonic function `u₀`):

* (S) — the coupling clause of the pocket field `X = chartTransport c 1 a k h` on the conditional law given `A` — is the
  landed `PocketCoupling.isCouplingCharFun_chartTransport` from the physical kernel (`PocketKernel`, Aux. lemma 124 at
  the relative capacity times) and the mean identification (`PocketMeanIdent`, Aux. lemmas 119–122);
* **(L)** — K2's member identities of the relative hulls — follows from the history-marked locality of the canonical set
  `K_s = ℍ ∖ activeDom` (`PocketStop.activeCompl`, the marked union law of Aux. lemma 124's `B ∪ R_{T(s)}`, which is
  what `PocketStop.pocketStopLaw_activeCompl` delivers) through the retained-chart decomposition
  (`Restart.DomainMarkov.Mean.hasSafeMembers_chartTransport`), on the ambient space, and is then restricted to `A`;
* **`pocketWordFieldStatement_of_chart`**: with the determination of the killed relative history by the walls' record
  and the pocket field (the named input `hdet`: Proposition 5.13 and the measurable pocket erasure, p. 398), the pocket
  word field statement `Lemma725RefK2.PocketWordFieldStatement` holds (`pocketWordFieldStatement_of_charFun`).

Conditional helpers; no source theorem is replaced. Ruling R48: nothing here uses Theorem 1.2/1.3,
`Theorem12ParamStatement`, `Theorem13Statement` or a result taking them as hypotheses.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open QuantumZipper (H fwdHull zeroGFFTestCov)
open LQGMetric (DistOn TestOn IsZeroBoundaryGFF)
open scoped NNReal ENNReal

namespace InteractingSLE.Sec7.Lemma725RefSafe

open Restart.DomainMarkov Restart.DomainMarkov.K2 Aux122Disint PhaseSel PocketMartLife PocketCoupling LocalSets
  Coupling MartChar PocketTraversal Lemma71C PocketAdapt PocketWordLife LawUnique PocketStop WholeField

/-! ### The localized relative history filtration on the ambient space -/

section Filt

variable {Ω : Type*} {𝓦 : MeasurableSpace Ω} [mΩ : MeasurableSpace Ω]

omit mΩ in
theorem locPrefixSigma_mono (𝓦 : MeasurableSpace Ω) (A : Set Ω) (γ : Ω → ℝ → ℂ) :
    Monotone (locPrefixSigma 𝓦 A γ) := by
  intro s t hst
  refine sup_le_sup_left (MeasurableSpace.generateFrom_mono ?_) _
  rintro E ⟨r, hr, n, k, rfl⟩
  exact ⟨r, hr.trans hst, n, k, rfl⟩

/-- **The localized relative history filtration** `s ↦ 𝓦 ∨ σ(A ∩ prefix events up to s)` on the ambient space. -/
def locPrefixFilt (𝓦 : MeasurableSpace Ω) (A : Set Ω) (γ : Ω → ℝ → ℂ)
    (hle : ∀ q, locPrefixSigma 𝓦 A γ q ≤ mΩ) : Filtration ℝ≥0 mΩ where
  seq := locPrefixSigma 𝓦 A γ
  mono' := locPrefixSigma_mono 𝓦 A γ
  le' := hle

/-- (L) for a smaller filtration. -/
theorem hasSafeMembers_mono_filt {P : Measure Ω} {𝓗 𝓗' : Filtration ℝ≥0 mΩ} (h𝓗 : ∀ s, 𝓗' s ≤ 𝓗 s) {F : Set Ω}
    {ζ : Ω → ℝ≥0∞} {W : ℝ≥0 → Ω → ℝ} {X : Ω → DistOn upperHalfPlaneOpens} (h : HasSafeMembers P 𝓗 F ζ W X) :
    HasSafeMembers P 𝓗' F ζ W X := fun s Fb hFb D hD => h s Fb hFb D (h𝓗 s _ hD)

end Filt

/-! ### The pocket word field statement from the field on the ambient space -/

section Chart

universe u

/-- **The pocket field on the walls-event `A`, from the field on the ambient space** (Aux. lemmas 124–125, Lemma 7.25's
proof). On a standard Borel probability space with the walls' σ-algebra `𝓦` and a walls-event `A` of positive
probability: the erased traversal `γ` (driven on `A`, measurable at fixed own times), walls-measurable marks, a
conformal chart `c` (the pocket chart) measurable for `𝓦` with a continuous harmonic lift, and the ambient field `h`
with `h − u₀` a zero-boundary GFF for a harmonic `u₀`. If

* the physical kernel `PocketKernel` and the mean identification `PocketMeanIdent` hold (as in `PocketChartLaw`), and
* the canonical set `ℍ ∖ activeDom` is hitting-measurable and history-local for `h − u₀` with the relative history
  `𝓦 ∨ σ(A ∩ prefix events up to s)` as marks, at every relative capacity time `s`
  (`PocketStop.pocketStopLaw_activeCompl`),

then under the conditional law given `A` the pocket field `X = chartTransport c 1 a k h` is measurable with integrable
pairings, satisfies the coupling clause of the word in the usual augmentation of the relative history filtration (the
landed `isCouplingCharFun_chartTransport`), and has K2's (L) in the relative history filtration
(`Mean.hasSafeMembers_chartTransport` on the ambient space, restricted to `A`). -/
theorem pocketChart_levelOne {κ : ℝ} {nL nR : ℕ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ}
    {Ω : Type u} {𝓦 : MeasurableSpace Ω} [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] (h𝓦 : 𝓦 ≤ mΩ) {A : Set Ω} (hA : MeasurableSet[𝓦] A) (hPA : 0 < P A)
    {γ : Ω → ℝ → ℂ} (hγ : ∀ ω ∈ A, IsDrivenCurve (γ ω)) (hγm : ∀ u, 0 ≤ u → Measurable fun ω : A => γ ω u)
    {xL : Ω → Fin nL → ℝ} {xR : Ω → Fin nR → ℝ}
    (hxLm : Measurable[MeasurableSpace.comap Subtype.val 𝓦] fun ω : A => xL ω)
    (hxRm : Measurable[MeasurableSpace.comap Subtype.val 𝓦] fun ω : A => xR ω)
    {c : Ω → Chart} (hc : ∀ ω, (c ω).IsConformal) (hdom : ∀ z, MeasurableSet[𝓦] {ω | z ∈ (c ω).dom})
    (hfwd : ∀ z, Measurable[𝓦] ({ω | z ∈ (c ω).dom}.indicator fun ω => (c ω).1 z))
    (hliftm : ∀ z, Measurable[𝓦] ({ω | z ∈ (c ω).dom}.indicator fun ω => (c ω).2.2 z))
    (hliftc : ∀ ω, ContinuousOn (c ω).2.2 (c ω).dom)
    (hlift : ∀ ω, InnerProductSpace.HarmonicOnNhd (c ω).2.2 (c ω).dom) (a k : ℝ)
    {h : Ω → DistOn upperHalfPlaneOpens} (hhm : Measurable h) {u₀ : ℂ → ℝ}
    (hu₀ : InnerProductSpace.HarmonicOnNhd u₀ H)
    (hh0 : IsZeroBoundaryGFF upperHalfPlaneOpens (centredField h u₀) P)
    {𝓜 : ℝ≥0 → MeasurableSpace Ω} {M : ℝ≥0 → Ω → DistOn upperHalfPlaneOpens}
    (hker : PocketKernel 𝓦 P A γ c h 𝓜 M) (hmean : PocketMeanIdent κ ρL ρR P A γ xL xR c a k M)
    (hKm : ∀ s, Measurable[mΩ, hittingSigma] (activeCompl A γ c s))
    (hKloc : ∀ s, IsHistoryAvoidanceLocal (locPrefixSigma 𝓦 A γ s) (activeCompl A γ c s) (centredField h u₀) P) :
    Measurable (fun ω : A => Chart.chartTransport (hc ω) 1 a k (h ω)) ∧
    (∀ φ : TestOn upperHalfPlaneOpens,
      Integrable (fun ω : A => Chart.chartTransport (hc ω) 1 a k (h ω) φ) (condSub P A)) ∧
    MartMeans.IsCouplingCharFun κ ρL ρR (condSub P A)
      (usualAugmentation (prefixFilt (MeasurableSpace.comap Subtype.val 𝓦) (MeasurableSpace.comap_mono h𝓦)
        (fun ω : A => γ ω) fun r n k => PocketMeas.measurableSet_prefixEvent (fun ω : A => hγ ω ω.2) hγm r n k)
        (condSub P A))
      (fun t (ω : A) => segDriver (γ ω) t) (geomLW (fun t (ω : A) => segDriver (γ ω) t) fun ω : A => xL ω)
      (geomRW (fun t (ω : A) => segDriver (γ ω) t) fun ω : A => xR ω) (fun ω : A => capLife (γ ω))
      (fun ω : A => Chart.chartTransport (hc ω) 1 a k (h ω)) ∧
    HasSafeMembers (condSub P A)
      (prefixFilt (MeasurableSpace.comap Subtype.val 𝓦) (MeasurableSpace.comap_mono h𝓦) (fun ω : A => γ ω)
        fun r n k => PocketMeas.measurableSet_prefixEvent (fun ω : A => hγ ω ω.2) hγm r n k)
      univ (fun ω : A => capLife (γ ω)) (fun t (ω : A) => segDriver (γ ω) t)
      (fun ω : A => Chart.chartTransport (hc ω) 1 a k (h ω)) := by
  have hAm : MeasurableSet A := h𝓦 _ hA
  have : StandardBorelSpace A := hAm.standardBorel
  have : IsProbabilityMeasure (condSub P A) := isProbabilityMeasure_condSub hAm hPA.ne'
  obtain ⟨h𝓜, h𝓜pre, hK⟩ := hker
  have hle : ∀ q, locPrefixSigma 𝓦 A γ q ≤ mΩ := PocketUnionPt.locPrefixSigma_le h𝓦 hA hγ hγm
  -- the relative history filtration on `A`
  have h𝓔 : MeasurableSpace.comap Subtype.val 𝓦 ≤ (inferInstance : MeasurableSpace A) :=
    MeasurableSpace.comap_mono h𝓦
  have hdrive : ∀ ω : A, IsDrivenCurve (γ ω) := fun ω => hγ ω ω.2
  have hm : ∀ r n k, MeasurableSet (prefixEvent (fun ω : A => γ ω) r n k) := fun r n k =>
    PocketMeas.measurableSet_prefixEvent hdrive hγm r n k
  set 𝓗 := prefixFilt (MeasurableSpace.comap Subtype.val 𝓦) h𝓔 (fun ω : A => γ ω) hm with h𝓗def
  have hpre : IsPrefixAdapted 𝓗 (fun ω : A => γ ω) := isPrefixAdapted_prefixFilt h𝓔 hm
  have h0 : MeasurableSpace.comap Subtype.val 𝓦 ≤ 𝓗 0 := le_prefixFilt_zero h𝓔 hm
  have h𝓗𝓜 : ∀ q, 𝓗 q ≤ MeasurableSpace.comap Subtype.val (𝓜 q) := fun q => by
    show prefixSigma _ (fun ω : A => γ ω) q ≤ _
    rw [← comap_locPrefixSigma]
    exact MeasurableSpace.comap_mono (h𝓜pre q)
  have h𝓜' : ∀ q, MeasurableSpace.comap (Subtype.val : A → Ω) (𝓜 q) ≤ (inferInstance : MeasurableSpace A) :=
    fun q => MeasurableSpace.comap_mono (h𝓜 q)
  have hA𝓜 : ∀ q, MeasurableSet[𝓜 q] A := fun q =>
    h𝓜pre q _ ((le_sup_left : 𝓦 ≤ locPrefixSigma 𝓦 A γ q) _ hA)
  -- the chart on `A`
  have hind : ∀ {β : Type} [Zero β] [MeasurableSpace β] (z : ℂ) (f : Ω → ℂ → β),
      Measurable[𝓦] ({ω | z ∈ (c ω).dom}.indicator fun ω => f ω z) →
      Measurable[𝓗 0] ({ω : A | z ∈ (c ω).dom}.indicator fun ω => f ω z) := fun z f hf => by
    have e : ({ω : A | z ∈ (c ω).dom}.indicator fun ω => f ω z) =
        ({ω | z ∈ (c ω).dom}.indicator fun ω => f ω z) ∘ Subtype.val := by
      funext ω
      by_cases hz : z ∈ (c ω).dom
      · simp only [Function.comp_apply, indicator_of_mem (show ω ∈ {ω : A | z ∈ (c ω).dom} from hz),
          indicator_of_mem (show (ω : Ω) ∈ {ω | z ∈ (c ω).dom} from hz)]
      · simp only [Function.comp_apply, indicator_of_notMem (show ω ∉ {ω : A | z ∈ (c ω).dom} from hz),
          indicator_of_notMem (show (ω : Ω) ∉ {ω | z ∈ (c ω).dom} from hz)]
    rw [e]
    exact (hf.comp (comap_measurable (Subtype.val : A → Ω))).mono h0 le_rfl
  have hdomA : ∀ z, MeasurableSet[𝓗 0] {ω : A | z ∈ (c ω).dom} := fun z => h0 _ ⟨_, hdom z, rfl⟩
  have hh' : Measurable fun ω : A => h ω := hhm.comp measurable_subtype_coe
  -- (S): the coupling clause on `A`
  have hcond : ∀ (q : ℝ≥0) (φ : TestOn upperHalfPlaneOpens), ∀ᵐ (ω : A) ∂(condSub P A),
      (q : ℝ≥0∞) < capLife (γ ω) →
      tsupport φ ⊆ (c ω).2.1 '' (H \ fwdHull (fun s : ℝ => segDriver (γ ω) s.toNNReal) q) →
      condExp (MeasurableSpace.comap Subtype.val (𝓜 q)) (condSub P A)
          (fun ω : A => Complex.exp (Complex.I * (h ω φ : ℂ))) ω =
        Complex.exp (Complex.I * (M q ω φ : ℂ) -
          (((1 / 2 : ℝ) * zeroGFFTestCov ((c ω).2.1 '' (H \ fwdHull (fun s : ℝ => segDriver (γ ω) s.toNNReal) q))
            φ φ : ℝ) : ℂ)) := fun q φ => by
    have hint : Integrable (fun ω => Complex.exp (Complex.I * (h ω φ : ℂ))) P :=
      GFF.integrable_exp_I_mul ((LQGMetric.measurable_distOn_apply φ).comp hhm)
    filter_upwards [condExp_condSub_ae_eq (h𝓜 q) (hA𝓜 q) hPA.ne' hint, ae_condSub_of_ae hAm (hK q φ)]
      with ω h1 h2 hq hs
    rw [h1]
    exact h2 ω.2 hq hs
  have hmean' : ∀ (q : ℝ≥0) (ψ' : TestOn upperHalfPlaneOpens), ∀ᵐ (ω : A) ∂(condSub P A),
      ω ∈ Restart.DomainMarkov.avoidSet (fun t (ω : A) => segDriver (γ ω) t) (fun ω : A => capLife (γ ω)) ψ' q →
      Chart.chartTransport (hc ω) 1 a k (M q ω) ψ' =
        ∫ z, couplingMean κ (fun s : ℝ => segDriver (γ ω) s.toNNReal) q
          (Restart.DomainMarkov.bheProc κ ρL ρR (fun t (ω : A) => segDriver (γ ω) t)
            (PocketTraversal.geomLW (fun t (ω : A) => segDriver (γ ω) t) fun ω : A => xL ω)
            (PocketTraversal.geomRW (fun t (ω : A) => segDriver (γ ω) t) fun ω : A => xR ω) ω q) z * ψ' z :=
    fun q ψ' => by
      filter_upwards [ae_condSub_of_ae hAm (hmean q ψ')] with ω hω hav
      exact hω ω.2 hav (hc ω)
  have hcf := isCouplingCharFun_chartTransport κ ρL ρR hdrive hpre (hxLm.mono h0 le_rfl) (hxRm.mono h0 le_rfl)
    (fun ω : A => hc ω) hdomA (fun z => hind z (fun ω => (c ω).1) (hfwd z))
    (fun z => hind z (fun ω => (c ω).2.2) (hliftm z)) (fun ω : A => hliftc ω) hh' a k
    (fun q => MeasurableSpace.comap Subtype.val (𝓜 q)) h𝓗𝓜 h𝓜' (fun q ω => M q ω) hcond hmean'
  have hX : Measurable fun ω : A => Chart.chartTransport (hc ω) 1 a k (h ω) :=
    Chart.measurable_chartTransport_random' (fun ω : A => hc ω) (fun z => 𝓗.le 0 _ (hdomA z))
      (fun z => (hind z (fun ω => (c ω).1) (hfwd z)).mono (𝓗.le 0) le_rfl)
      (fun z => (hind z (fun ω => (c ω).2.2) (hliftm z)).mono (𝓗.le 0) le_rfl) (fun ω : A => hliftc ω) hh' 1 a k
  have hint : ∀ φ : TestOn upperHalfPlaneOpens,
      Integrable (fun ω : A => Chart.chartTransport (hc ω) 1 a k (h ω) φ) (condSub P A) := fun φ =>
    WangWu.integrable_apply_of_isCouplingCharFun_of_bounded hcf
      (ae_of_all _ fun ω => ⟨PocketPhaseMeans.capLife_pos (hdrive ω), (hdrive ω).segDriver_spec.2.1,
        (hdrive ω).segDriver_spec.1⟩) φ ((LQGMetric.measurable_distOn_apply φ).comp hX)
  -- (L) on the ambient space, then on `A`
  have hmemΩ : HasSafeMembers P (locPrefixFilt 𝓦 A γ hle) A (fun ω => capLife (γ ω))
      (fun t ω => segDriver (γ ω) t) fun ω => Chart.chartTransport (hc ω) 1 a k (h ω) := by
    refine Mean.hasSafeMembers_chartTransport (𝒢 := 𝓦) (le_sup_left : 𝓦 ≤ locPrefixSigma 𝓦 A γ 0) hhm hu₀ hh0 hc
      hdom hfwd hliftm hliftc hlift a k (fun s => locPrefixSigma 𝓦 A γ s) (fun _ => le_rfl) hle
      (fun s => activeCompl A γ c s) hKm (fun s ω => ⟨sdiff_subset, ?_⟩) hKloc (fun s => ?_) ?_
    · have hsub : activeDom A γ c s ω ⊆ H := fun z hz => by
        obtain ⟨w, hw, rfl⟩ := hz.2.2
        exact (hc ω).2.1 hw.1
      rw [activeCompl, sdiff_sdiff_cancel_left hsub]
      by_cases hl : ω ∈ A ∧ (s : ℝ≥0∞) < capLife (γ ω)
      · rw [activeDom_eq hl.1 hl.2]
        exact Mean.isOpen_image_inv (hc ω)
          (Coupling.MartMeans2.isOpen_H_diff_fwdHull_rpath (hγ ω hl.1).segDriver_spec.2.1 hl.2) sdiff_subset
      · rw [PocketUnionPt.activeDom_eq_empty hl]
        exact isOpen_empty
    · refine ae_of_all _ fun ω hωA hs => ?_
      have hsub : activeDom A γ c s ω ⊆ H := fun z hz => by
        obtain ⟨w, hw, rfl⟩ := hz.2.2
        exact (hc ω).2.1 hw.1
      rw [activeCompl, sdiff_sdiff_cancel_left hsub, activeDom_eq hωA hs]
    · exact ae_of_all _ fun ω hωA => ⟨(hγ ω hωA).segDriver_spec.2.1, (hγ ω hωA).segDriver_spec.1⟩
  have hA0 : MeasurableSet[locPrefixFilt 𝓦 A γ hle 0] A := (le_sup_left : 𝓦 ≤ locPrefixSigma 𝓦 A γ 0) _ hA
  have hmemA := hasSafeMembers_subtype hAm (subtype_cond_of_measurableSet_zero hA0) hmemΩ
  have hpreA : (Subtype.val ⁻¹' A : Set A) = univ := by
    ext ω
    simp only [mem_preimage, ω.2, mem_univ]
  rw [hpreA] at hmemA
  have hmem1 : HasSafeMembers (condSub P A) 𝓗 univ (fun ω : A => capLife (γ ω))
      (fun t (ω : A) => segDriver (γ ω) t) fun ω : A => Chart.chartTransport (hc ω) 1 a k (h ω) :=
    hasSafeMembers_mono_filt (fun s => (comap_locPrefixSigma 𝓦 A γ s).ge) hmemA
  exact ⟨hX, hint, hcf, hmem1⟩

/-- **Lemma 7.25's pocket with its field, from the field on the ambient space**: `pocketChart_levelOne` and
`pocketWordFieldStatement_of_charFun`. Besides the inputs of `pocketChart_levelOne`: the word shape of the marks on `A`,
weights with seed weights `r_L, r_R < κ/2 − 4` and all side partial sums `> −2`, the traversal unbounded in `ℍ`, and
`hdet`: on `A` the killed relative history is a Borel function of the walls' record `E` and the pocket field
(Proposition 5.13 and the measurable selected-pocket erasure, p. 398). -/
theorem pocketWordFieldStatement_of_chart {κ rL rR : ℝ} (hκ : 4 < κ) (hLd : rL < κ / 2 - 4)
    (hRd : rR < κ / 2 - 4) {nL nR : ℕ} {ρL : Fin (nL + 1) → ℝ} {ρR : Fin (nR + 1) → ℝ} (hρL : ρL 0 = rL)
    (hρR : ρR 0 = rR) (hsL : ∀ m : Fin (nL + 1), -2 < ∑ i ∈ Finset.univ.filter (fun i => i ≤ m), ρL i)
    (hsR : ∀ m : Fin (nR + 1), -2 < ∑ i ∈ Finset.univ.filter (fun i => i ≤ m), ρR i)
    {Ω : Type u} {𝓦 : MeasurableSpace Ω} [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] (h𝓦 : 𝓦 ≤ mΩ) {A : Set Ω} (hA : MeasurableSet[𝓦] A) (hPA : 0 < P A)
    {γ : Ω → ℝ → ℂ} (hγ : ∀ ω ∈ A, IsDrivenCurve (γ ω)) (hγm : ∀ u, 0 ≤ u → Measurable fun ω : A => γ ω u)
    (hunb : ∀ ω ∈ A, ∀ M : ℝ, ∃ u, 0 ≤ u ∧ γ ω u ∈ H ∧ M < ‖γ ω u‖)
    {xL : Ω → Fin (nL + 1) → ℝ} {xR : Ω → Fin (nR + 1) → ℝ}
    (hxLm : Measurable[MeasurableSpace.comap Subtype.val 𝓦] fun ω : A => xL ω)
    (hxRm : Measurable[MeasurableSpace.comap Subtype.val 𝓦] fun ω : A => xR ω)
    (hseedL : ∀ ω ∈ A, xL ω 0 = 0) (hseedR : ∀ ω ∈ A, xR ω 0 = 0)
    (hxLd : ∀ ω ∈ A, ∀ i : Fin nL, xL ω i.succ < 0) (hxRd : ∀ ω ∈ A, ∀ j : Fin nR, 0 < xR ω j.succ)
    (hxLi : ∀ ω ∈ A, Antitone (xL ω)) (hxRi : ∀ ω ∈ A, Monotone (xR ω))
    {c : Ω → Chart} (hc : ∀ ω, (c ω).IsConformal) (hdom : ∀ z, MeasurableSet[𝓦] {ω | z ∈ (c ω).dom})
    (hfwd : ∀ z, Measurable[𝓦] ({ω | z ∈ (c ω).dom}.indicator fun ω => (c ω).1 z))
    (hliftm : ∀ z, Measurable[𝓦] ({ω | z ∈ (c ω).dom}.indicator fun ω => (c ω).2.2 z))
    (hliftc : ∀ ω, ContinuousOn (c ω).2.2 (c ω).dom)
    (hlift : ∀ ω, InnerProductSpace.HarmonicOnNhd (c ω).2.2 (c ω).dom) (a k : ℝ)
    {h : Ω → DistOn upperHalfPlaneOpens} (hhm : Measurable h) {u₀ : ℂ → ℝ}
    (hu₀ : InnerProductSpace.HarmonicOnNhd u₀ H)
    (hh0 : IsZeroBoundaryGFF upperHalfPlaneOpens (centredField h u₀) P)
    {𝓜 : ℝ≥0 → MeasurableSpace Ω} {M : ℝ≥0 → Ω → DistOn upperHalfPlaneOpens}
    (hker : PocketKernel 𝓦 P A γ c h 𝓜 M) (hmean : PocketMeanIdent κ ρL ρR P A γ xL xR c a k M)
    (hKm : ∀ s, Measurable[mΩ, hittingSigma] (activeCompl A γ c s))
    (hKloc : ∀ s, IsHistoryAvoidanceLocal (locPrefixSigma 𝓦 A γ s) (activeCompl A γ c s) (centredField h u₀) P)
    {ε : Type u} [MeasurableSpace ε] [StandardBorelSpace ε] {E : Ω → ε} (hEm : Measurable[𝓦] E)
    {g : ε × DistOn upperHalfPlaneOpens → HistorySpace (nL + 1) (nR + 1)} (hg : Measurable g)
    (hdet : ∀ᵐ ω ∂P, ω ∈ A → killedHistory (fun t ω => segDriver (γ ω) t)
      (geomLW (fun t ω => segDriver (γ ω) t) xL) (geomRW (fun t ω => segDriver (γ ω) t) xR)
      (fun ω => capLife (γ ω)) ω = g (E ω, Chart.chartTransport (hc ω) 1 a k (h ω))) :
    Lemma725RefK2.PocketWordFieldStatement.{u} κ rL rR := by
  have hAm : MeasurableSet A := h𝓦 _ hA
  have : StandardBorelSpace A := hAm.standardBorel
  have : IsProbabilityMeasure (condSub P A) := isProbabilityMeasure_condSub hAm hPA.ne'
  obtain ⟨hX, hint, hcf, hmem⟩ := pocketChart_levelOne h𝓦 hA hPA hγ hγm hxLm hxRm hc hdom hfwd hliftm hliftc hlift
    a k hhm hu₀ hh0 hker hmean hKm hKloc
  have hdet1 : ∀ᵐ ω ∂(condSub P A), killedHistory (fun t (ω : A) => segDriver (γ ω) t)
      (geomLW (fun t (ω : A) => segDriver (γ ω) t) fun ω : A => xL ω)
      (geomRW (fun t (ω : A) => segDriver (γ ω) t) fun ω : A => xR ω) (fun ω : A => capLife (γ ω)) ω =
        g (E ω, Chart.chartTransport (hc ω) 1 a k (h ω)) := by
    filter_upwards [ae_condSub_of_ae hAm hdet] with ω hω
    exact hω ω.2
  exact pocketWordFieldStatement_of_charFun hκ hLd hRd hρL hρR hsL hsR (MeasurableSpace.comap_mono h𝓦)
    (fun ω : A => hγ ω ω.2) hγm (fun ω => hunb ω ω.2) hxLm hxRm (fun ω => hseedL ω ω.2) (fun ω => hseedR ω ω.2)
    (fun ω => hxLd ω ω.2) (fun ω => hxRd ω ω.2) (fun ω => hxLi ω ω.2) (fun ω => hxRi ω ω.2) hX hint hcf hmem
    (fun s hs => ⟨_, hEm hs, rfl⟩) hg hdet1

/-- **The `P`-side pocket of a two-seed word with its field, from the field on the ambient space**
(`pocketChart_levelOne` and `pocketTwoSeedPSideStatement_of_charFun`), for seed weights in Aux. lemma 122's range
`(−2, κ − 6)`: besides the inputs of `pocketChart_levelOne` for the constant two-seed word, the traversal unbounded in
`ℍ`, the pathwise property `Good` of the relative driver with infinite lifetime, and the determination `hdet`. -/
theorem pocketTwoSeedPSideStatement_of_chart {κ rL rR : ℝ} (hκ : 4 < κ) (hL : -2 < rL) (hLd : rL < κ - 6)
    (hR : -2 < rR) (hRd : rR < κ - 6) {Good : (ℝ≥0 → ℝ) → ℝ≥0∞ → Prop}
    {Ω : Type u} {𝓦 : MeasurableSpace Ω} [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] (h𝓦 : 𝓦 ≤ mΩ) {A : Set Ω} (hA : MeasurableSet[𝓦] A) (hPA : 0 < P A)
    {γ : Ω → ℝ → ℂ} (hγ : ∀ ω ∈ A, IsDrivenCurve (γ ω)) (hγm : ∀ u, 0 ≤ u → Measurable fun ω : A => γ ω u)
    (hunb : ∀ ω ∈ A, ∀ M : ℝ, ∃ u, 0 ≤ u ∧ γ ω u ∈ H ∧ M < ‖γ ω u‖)
    {c : Ω → Chart} (hc : ∀ ω, (c ω).IsConformal) (hdom : ∀ z, MeasurableSet[𝓦] {ω | z ∈ (c ω).dom})
    (hfwd : ∀ z, Measurable[𝓦] ({ω | z ∈ (c ω).dom}.indicator fun ω => (c ω).1 z))
    (hliftm : ∀ z, Measurable[𝓦] ({ω | z ∈ (c ω).dom}.indicator fun ω => (c ω).2.2 z))
    (hliftc : ∀ ω, ContinuousOn (c ω).2.2 (c ω).dom)
    (hlift : ∀ ω, InnerProductSpace.HarmonicOnNhd (c ω).2.2 (c ω).dom) (a k : ℝ)
    {h : Ω → DistOn upperHalfPlaneOpens} (hhm : Measurable h) {u₀ : ℂ → ℝ}
    (hu₀ : InnerProductSpace.HarmonicOnNhd u₀ H)
    (hh0 : IsZeroBoundaryGFF upperHalfPlaneOpens (centredField h u₀) P)
    {𝓜 : ℝ≥0 → MeasurableSpace Ω} {M : ℝ≥0 → Ω → DistOn upperHalfPlaneOpens}
    (hker : PocketKernel 𝓦 P A γ c h 𝓜 M)
    (hmean : PocketMeanIdent κ (fun _ : Fin 1 => rL) (fun _ : Fin 1 => rR) P A γ (fun _ => LP.twoSeedXL)
      (fun _ => LP.twoSeedXR) c a k M)
    (hKm : ∀ s, Measurable[mΩ, hittingSigma] (activeCompl A γ c s))
    (hKloc : ∀ s, IsHistoryAvoidanceLocal (locPrefixSigma 𝓦 A γ s) (activeCompl A γ c s) (centredField h u₀) P)
    (hGood : ∀ᵐ ω ∂P, ω ∈ A → capLife (γ ω) = ⊤ → Good (fun t => segDriver (γ ω) t) ⊤)
    {ε : Type u} [MeasurableSpace ε] {E : Ω → ε} (hEm : Measurable[𝓦] E)
    {g : ε × DistOn upperHalfPlaneOpens → HistorySpace 1 1} (hg : Measurable g)
    (hdet : ∀ᵐ ω ∂P, ω ∈ A → killedHistory (fun t ω => segDriver (γ ω) t)
      (geomLW (fun t ω => segDriver (γ ω) t) fun _ => LP.twoSeedXL)
      (geomRW (fun t ω => segDriver (γ ω) t) fun _ => LP.twoSeedXR)
      (fun ω => capLife (γ ω)) ω = g (E ω, Chart.chartTransport (hc ω) 1 a k (h ω))) :
    Lemma725RefK2.PocketTwoSeedPSideStatement.{u} κ rL rR Good := by
  have hAm : MeasurableSet A := h𝓦 _ hA
  have : StandardBorelSpace A := hAm.standardBorel
  have : IsProbabilityMeasure (condSub P A) := isProbabilityMeasure_condSub hAm hPA.ne'
  obtain ⟨hX, hint, hcf, hmem⟩ := pocketChart_levelOne h𝓦 hA hPA hγ hγm (measurable_const (a := LP.twoSeedXL))
    (measurable_const (a := LP.twoSeedXR)) hc hdom hfwd hliftm hliftc hlift a k hhm hu₀ hh0 hker hmean hKm hKloc
  refine pocketTwoSeedPSideStatement_of_charFun hκ hL hLd hR hRd (MeasurableSpace.comap_mono h𝓦)
    (fun ω : A => hγ ω ω.2) hγm (fun ω => hunb ω ω.2) hX hint hcf hmem ?_ (fun s hs => ⟨_, hEm hs, rfl⟩) hg ?_
  · filter_upwards [ae_condSub_of_ae hAm hGood] with ω hω
    exact hω ω.2
  · filter_upwards [ae_condSub_of_ae hAm hdet] with ω hω
    exact hω ω.2

end Chart

end InteractingSLE.Sec7.Lemma725RefSafe
