/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Restart.StoppedK2Wire
import InteractingSLE.Spec.Supplement.Disintegrate
import InteractingSLE.Spec.Supplement.GB6Meas

/-!
# Determination through a stop, in driver form

Packet PROVE-GB6-RELDRV. GB6's (Det) (`GB6RelDrvDetStatement`) is a statement about the decoded canonical **driver**
code of the conditional field. PROVE-DOMAINMARKOV9's lift (`StoppedExtend.ae_stoppedCodeMatch_of_ae_condExpKernel`)
and PROVE-STOPPEDK2's generic chain (`StoppedK2.ae_stoppedCodeMatch_of_hasSafeLaw`) conclude with the decoded
**path** of a canonical flow code, through Theorem 1.3. This file gives the driver form of the same chain; it needs
neither Theorem 1.3 nor a trace of the continuation, only Aux. lemma 54 (specification p. 295: "For a stopped
portion, the same conclusion follows by appending the canonical future in its active residual field and applying that
uniqueness, then restricting back to the recorded stop") and the determination clause of a canonical driver code.

* `IsStopDrvMatch p W e`: `e` is at most the code's lifetime and `W` is the code at every dyadic time before `e`;
  `eqOn_drvDec_of_isStopDrvMatch`: for a good code, the decoded driver is `W` before `e`;
* `ae_isStopDrvMatch_on_extension`: on an extension (a full optional hull coupling on `Ω × C` agreeing with the
  stopped driver through `e`), the determination clause of `F` gives the stopped driver match;
* **`ae_isStopDrvMatch_of_isStoppedHullCoupling`**: a coupling through a stop of the flow-line word of a fixed word
  `c` (Aux. lemma 54, `StoppedExtend.StoppedHullExtendStatement`) has the stopped driver match;
* `ae_isStopDrvMatch_of_ae_condExpKernel`: the same under the regular conditional law, lifted to `P`;
* **`ae_isStopDrvMatch_of_k`** and the generic chain **`ae_isStopDrvMatch_of_hasSafeLaw`** (the driver forms of
  `StoppedK2.ae_stoppedCodeMatch_of_k` and `StoppedK2.ae_stoppedCodeMatch_of_hasSafeLaw`).

**R48.** Canonical driver codes exist only through Theorems 1.2–1.3 (`Restart.canonicalDriverCodeStatement_of_param`),
so these results serve Theorem 1.4 (GB6) only; they take neither theorem as a hypothesis.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open QuantumZipper (H fwdHull)
open LQGMetric (TestOn DistOn)
open scoped NNReal ENNReal

namespace InteractingSLE.Supp8.GB6.RelDrv

open Restart Restart.StoppedExtend Restart.StoppedK2 Restart.DomainMarkov Restart.DomainMarkov.K2
  Restart.ConverseBefore Restart.FCDet Sec2.Assembly Sec7.PocketTraversal

/-! ### The stopped driver match -/

/-- **The stopped driver match**: the stop `e` is at most the lifetime of the driver code `p`, and the driver `W` is
the code at every dyadic time before `e`. -/
def IsStopDrvMatch (p : PCode × ℝ≥0∞) (W : ℝ≥0 → ℝ) (e : ℝ≥0∞) : Prop :=
  e ≤ p.2 ∧ ∀ n k : ℕ, (dyad n k : ℝ≥0∞) < e → W (dyad n k) = p.1 n k

/-- The stopped driver match is a measurable event. -/
theorem measurableSet_isStopDrvMatch {S : Type*} [MeasurableSpace S] {G : S → PCode × ℝ≥0∞} (hG : Measurable G)
    {W : ℝ≥0 → S → ℝ} (hW : ∀ t, Measurable (W t)) {e : S → ℝ≥0∞} (he : Measurable e) :
    MeasurableSet {s | IsStopDrvMatch (G s) (fun t => W t s) (e s)} := by
  have hl : MeasurableSet {s | e s ≤ (G s).2} := measurableSet_le he (measurable_snd.comp hG)
  have hcode : ∀ n k : ℕ, Measurable fun s => (G s).1 n k := fun n k =>
    (measurable_pi_apply k).comp ((measurable_pi_apply n).comp (measurable_fst.comp hG))
  have hd : ∀ n k : ℕ, MeasurableSet {s | (dyad n k : ℝ≥0∞) < e s → W (dyad n k) s = (G s).1 n k} := by
    intro n k
    have h1 : MeasurableSet {s | (dyad n k : ℝ≥0∞) < e s} := measurableSet_lt measurable_const he
    have h2 : MeasurableSet {s | W (dyad n k) s = (G s).1 n k} := measurableSet_eq_fun (hW _) (hcode n k)
    have e1 : {s | (dyad n k : ℝ≥0∞) < e s → W (dyad n k) s = (G s).1 n k} =
        {s | (dyad n k : ℝ≥0∞) < e s}ᶜ ∪ {s | W (dyad n k) s = (G s).1 n k} := by
      ext s
      simp only [mem_ofPred_eq, mem_union, mem_compl_iff, imp_iff_not_or]
    rw [e1]
    exact h1.compl.union h2
  have e2 : {s | IsStopDrvMatch (G s) (fun t => W t s) (e s)} = {s | e s ≤ (G s).2} ∩
      ⋂ n : ℕ, ⋂ k : ℕ, {s | (dyad n k : ℝ≥0∞) < e s → W (dyad n k) s = (G s).1 n k} := by
    ext s
    simp only [IsStopDrvMatch, mem_ofPred_eq, mem_inter_iff, mem_iInter]
  rw [e2]
  exact hl.inter (MeasurableSet.iInter fun n => MeasurableSet.iInter fun k => hd n k)

/-- Two functions continuous before `e` that agree at the dyadic times before `e` agree before `e`. -/
theorem eqOn_of_dyad_lt {f g : ℝ≥0 → ℝ} {e : ℝ≥0∞} (hf : ContinuousOn f {t | (t : ℝ≥0∞) < e})
    (hg : ContinuousOn g {t | (t : ℝ≥0∞) < e})
    (hd : ∀ n k : ℕ, (dyad n k : ℝ≥0∞) < e → f (dyad n k) = g (dyad n k)) :
    ∀ t : ℝ≥0, (t : ℝ≥0∞) < e → f t = g t := by
  intro t ht
  have hopen : IsOpen {t : ℝ≥0 | (t : ℝ≥0∞) < e} := isOpen_lt ENNReal.continuous_coe continuous_const
  have hnhds : {t : ℝ≥0 | (t : ℝ≥0∞) < e} ∈ 𝓝 t := hopen.mem_nhds ht
  have hfa : ContinuousAt f t := hf.continuousAt hnhds
  have hga : ContinuousAt g t := hg.continuousAt hnhds
  have hlim := tendsto_dyad_flr t
  have hlt : ∀ n, (dyad n (flr n t) : ℝ≥0∞) < e := fun n =>
    lt_of_le_of_lt (ENNReal.coe_le_coe.2 (dyad_flr_le n t)) ht
  have h1 : Tendsto (fun n => f (dyad n (flr n t))) atTop (𝓝 (g t)) := by
    have := hga.tendsto.comp hlim
    refine this.congr fun n => ?_
    simp only [Function.comp_apply]
    exact (hd n (flr n t) (hlt n)).symm
  exact tendsto_nhds_unique (hfa.tendsto.comp hlim) h1

/-- **The decoded driver of a good code is the matched driver before the stop.** If `p` is a good driver code,
`W` is continuous before `e` and `W` matches `p` at the dyadic times before `e ≤ p.2`, then `drvDec p = W` before
`e`. -/
theorem eqOn_drvDec_of_isStopDrvMatch {p : PCode × ℝ≥0∞} (hp : IsGoodDrvCode p) {W : ℝ≥0 → ℝ} {e : ℝ≥0∞}
    (hW : ContinuousOn W {t | (t : ℝ≥0∞) < e}) (hm : IsStopDrvMatch p W e) :
    ∀ t : ℝ≥0, (t : ℝ≥0∞) < e → drvDec p t = W t := by
  obtain ⟨hle, hd⟩ := hm
  refine eqOn_of_dyad_lt ((continuousOn_drvDec p).mono fun t ht => lt_of_lt_of_le ht hle) hW fun n k hnk => ?_
  have hnk' : (dyad n k : ℝ≥0∞) < p.2 := lt_of_lt_of_le hnk hle
  have hp0 : 0 < p.2 := lt_of_le_of_lt (zero_le : (0 : ℝ≥0∞) ≤ _) hnk'
  rw [drvDec_of_good hp hp0, (hp n k hnk').dec_dyad le_rfl, hd n k hnk]

/-! ### The stopped driver match on an extension -/

/-- **The stopped driver match on an extension.** If the field `X = Hc + θχ` of a word `c` has, on `Ω × C`, a full
optional hull coupling of the flow-line word of `c` at the angle `θ` whose driver agrees with `W` through `e`, the
determination clause of a canonical driver code `F` makes `W` the code of `(c, Hc)` before `e`. -/
theorem ae_isStopDrvMatch_on_extension {κ θ : ℝ} {F : BoundaryWord × DistOn upperHalfPlaneOpens → PCode × ℝ≥0∞}
    (hF : IsCanonicalDriverCode κ θ F) (c : BoundaryWord) {Ω : Type} [MeasurableSpace Ω]
    {Hc X : Ω → DistOn upperHalfPlaneOpens}
    (hX : ∀ ω, IsTranslateAddConst 0 (θ * QuantumZipper.chiC κ) (Hc ω) (X ω)) {W : ℝ≥0 → Ω → ℝ}
    {VL : Fin (flowLineNL c.fn c.jumps 0) → ℝ≥0 → Ω → ℝ} {VR : Fin (flowLineNR c.fn c.jumps 0) → ℝ≥0 → Ω → ℝ}
    {e : Ω → ℝ≥0∞} {C : Type} [MeasurableSpace C] {E : Measure (Ω × C)} [IsProbabilityMeasure E]
    {𝓕' : Filtration ℝ≥0 (inferInstance : MeasurableSpace (Ω × C))} {W' : ℝ≥0 → Ω × C → ℝ}
    {VL' : Fin (flowLineNL c.fn c.jumps 0) → ℝ≥0 → Ω × C → ℝ}
    {VR' : Fin (flowLineNR c.fn c.jumps 0) → ℝ≥0 → Ω × C → ℝ} {B' : ℝ≥0 → Ω × C → ℝ} {ζ' : Ω × C → ℝ≥0∞}
    (hC : IsOptionalHullCoupling κ (flowLineXL c.fn c.jumps 0) (flowLineXR c.fn c.jumps 0)
      (flowLineRhoL κ c.fn c.jumps 0 θ) (flowLineRhoR κ c.fn c.jumps 0 θ) E 𝓕' W' VL' VR' B' ζ' (fun p => X p.1))
    (hag : ∀ᵐ p ∂E, e p.1 ≤ ζ' p ∧ ∀ t : ℝ≥0, (t : ℝ≥0∞) ≤ e p.1 → (t : ℝ≥0∞) < ζ' p →
      W' t p = W t p.1 ∧ (∀ i, VL' i t p = VL i t p.1) ∧ ∀ j, VR' j t p = VR j t p.1) :
    ∀ᵐ p ∂E, IsStopDrvMatch (F (c, Hc p.1)) (fun t => W t p.1) (e p.1) := by
  have hfld : IsFlowLineDriver κ c.fn c.jumps θ E (fun p => Hc p.1) W' ζ' :=
    ⟨fun p => X p.1, 𝓕', VL', VR', B', fun p => hX p.1, hC⟩
  have hm := hF.2.2 c E (fun p => Hc p.1) W' ζ' hfld
  filter_upwards [hm, hag] with p hmp hagp
  obtain ⟨hL, -, hd⟩ := hmp
  refine ⟨hL ▸ hagp.1, fun n k hnk => ?_⟩
  have hlt : (dyad n k : ℝ≥0∞) < ζ' p := lt_of_lt_of_le hnk hagp.1
  show W (dyad n k) p.1 = (F (c, Hc p.1)).1 n k
  rw [← (hagp.2 _ hnk.le hlt).1]
  exact hd n k hlt

/-- **A coupling through a stop of a flow-line word has the stopped driver match** (Aux. lemma 54 and the
determination clause of a canonical driver code). The coupling's processes need not be measurable: a measurable
process `W̄` agreeing with the coupling's driver through `e` carries the conclusion. -/
theorem ae_isStopDrvMatch_of_isStoppedHullCoupling {κ θ : ℝ} (hext : StoppedHullExtendStatement.{0} κ)
    {F : BoundaryWord × DistOn upperHalfPlaneOpens → PCode × ℝ≥0∞} (hF : IsCanonicalDriverCode κ θ F)
    (c : BoundaryWord) {Ω : Type} [mΩ : MeasurableSpace Ω] {Q : Measure Ω} [IsProbabilityMeasure Q]
    {Hc X : Ω → DistOn upperHalfPlaneOpens}
    (hX : ∀ ω, IsTranslateAddConst 0 (θ * QuantumZipper.chiC κ) (Hc ω) (X ω)) {𝓕 : Filtration ℝ≥0 mΩ}
    {W : ℝ≥0 → Ω → ℝ} {VL : Fin (flowLineNL c.fn c.jumps 0) → ℝ≥0 → Ω → ℝ}
    {VR : Fin (flowLineNR c.fn c.jumps 0) → ℝ≥0 → Ω → ℝ} {B : ℝ≥0 → Ω → ℝ} {e : Ω → ℝ≥0∞}
    (hSC : IsStoppedHullCoupling κ (flowLineXL c.fn c.jumps 0) (flowLineXR c.fn c.jumps 0)
      (flowLineRhoL κ c.fn c.jumps 0 θ) (flowLineRhoR κ c.fn c.jumps 0 θ) Q 𝓕 W VL VR B e X)
    {Wb : ℝ≥0 → Ω → ℝ} (hWb : ∀ t, Measurable (Wb t)) (hHc : Measurable Hc) (he : Measurable e)
    (hagb : ∀ᵐ ω ∂Q, ∀ t : ℝ≥0, (t : ℝ≥0∞) ≤ e ω → W t ω = Wb t ω) :
    ∀ᵐ ω ∂Q, IsStopDrvMatch (F (c, Hc ω)) (fun t => Wb t ω) (e ω) := by
  obtain ⟨C, mC, E, hE, 𝓕', W', VL', VR', B', ζ', hmap, hC, hag⟩ :=
    hext _ _ _ _ (Theorem15.isOrderedForceWord_flowLine c.fn c.jumps 0) Q 𝓕 W VL VR B e X hSC
  have hA := ae_isStopDrvMatch_on_extension hF c hX hC hag
  have hSm : MeasurableSet {ω | IsStopDrvMatch (F (c, Hc ω)) (fun t => Wb t ω) (e ω)} :=
    measurableSet_isStopDrvMatch (hF.1.comp (measurable_const.prodMk hHc)) hWb he
  have hmapE : AEMeasurable (Prod.fst : Ω × C → Ω) E := measurable_fst.aemeasurable
  have hagbE : ∀ᵐ p ∂E, ∀ t : ℝ≥0, (t : ℝ≥0∞) ≤ e p.1 → W t p.1 = Wb t p.1 :=
    ae_of_ae_map hmapE (by rw [hmap]; exact hagb)
  rw [← hmap]
  refine (ae_map_iff hmapE hSm).2 ?_
  filter_upwards [hA, hagbE] with p hp hbp
  refine ⟨hp.1, fun n k hnk => ?_⟩
  show Wb (dyad n k) p.1 = (F (c, Hc p.1)).1 n k
  rw [← hbp _ hnk.le]
  exact hp.2 n k hnk

/-- **The stopped driver match under the regular conditional law, lifted to `P`.** -/
theorem ae_isStopDrvMatch_of_ae_condExpKernel {F : BoundaryWord × DistOn upperHalfPlaneOpens → PCode × ℝ≥0∞}
    (hFm : Measurable F) {Ω : Type} {𝒢 : MeasurableSpace Ω} [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] (h𝒢 : 𝒢 ≤ mΩ) {M : Set Ω} (hM : MeasurableSet[𝒢] M)
    {β : Ω → BoundaryWord} (hβ : Measurable[𝒢] β) {Hc : Ω → DistOn upperHalfPlaneOpens} (hH : Measurable Hc)
    {W : ℝ≥0 → Ω → ℝ} (hW : ∀ t, Measurable (W t)) {e : Ω → ℝ≥0∞} (he : Measurable e)
    (hK : ∀ᵐ ω₀ ∂P, ω₀ ∈ M → ∀ᵐ ω ∂(condExpKernel P 𝒢 ω₀),
      IsStopDrvMatch (F (β ω₀, Hc ω)) (fun t => W t ω) (e ω)) :
    ∀ᵐ ω ∂P, ω ∈ M → IsStopDrvMatch (F (β ω, Hc ω)) (fun t => W t ω) (e ω) := by
  set A : Set (BoundaryWord × Ω) := {q | IsStopDrvMatch (F (q.1, Hc q.2)) (fun t => W t q.2) (e q.2)} with hAdef
  have hA : MeasurableSet A :=
    measurableSet_isStopDrvMatch (S := BoundaryWord × Ω) (G := fun q => F (q.1, Hc q.2))
      (hFm.comp (measurable_fst.prodMk (hH.comp measurable_snd))) (fun t => (hW t).comp measurable_snd)
      (he.comp measurable_snd)
  exact Theorem14.Disintegrate.ae_imp_of_ae_condExpKernel_param h𝒢 hβ hA hM hK

/-! ### The stopped driver match from the stopped K2 -/

section K2

variable {Ω : Type} {𝒢 : MeasurableSpace Ω} [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω] {Ω₀ : Type}
  [m₀ : MeasurableSpace Ω₀] [StandardBorelSpace Ω₀] {P : Measure Ω} [IsProbabilityMeasure P] {P₀ : Measure Ω₀}
  [IsProbabilityMeasure P₀] {nL nR : ℕ} {κ θ : ℝ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ} {L : Set Ω}
  {ΘL : Ω → Fin nL → ℝ} {ΘR : Ω → Fin nR → ℝ} {W : ℝ≥0 → Ω → ℝ} {VL : Fin nL → ℝ≥0 → Ω → ℝ}
  {VR : Fin nR → ℝ≥0 → Ω → ℝ} {V : Ω → ℝ≥0∞} {X Hc : Ω → DistOn upperHalfPlaneOpens} {c : Ω → BoundaryWord}

/-- **The stopped (Det) clause in driver form, from the stopped K2** (the driver form of
`StoppedK2.ae_stoppedCodeMatch_of_k`; no Theorem 1.3, no trace): almost surely on the live event `L`, the stop `V`
is at most the lifetime of the canonical driver code of `(c, Hc)` and `W` is that code at the dyadic times before
`V`. -/
theorem ae_isStopDrvMatch_of_k (hext : StoppedHullExtendStatement.{0} κ)
    {Fd : BoundaryWord × DistOn upperHalfPlaneOpens → PCode × ℝ≥0∞} (hFd : IsCanonicalDriverCode κ θ Fd)
    {𝓕 : Filtration ℝ≥0 (inferInstance : MeasurableSpace (Ω × Ω₀))} {B : ℝ≥0 → Ω × Ω₀ → ℝ}
    (hE : IsRandomWordEvolutionUpTo κ (P.prod P₀) (𝒢.comap Prod.fst) (Prod.fst ⁻¹' L) (fun p => ΘL p.1)
      (fun p => ΘR p.1) ρL ρR 𝓕 (fun t p => W t p.1) (fun i t p => VL i t p.1) (fun j t p => VR j t p.1) B
      (fun p => V p.1))
    (hcont : ∀ᵐ ω ∂P, ω ∈ L → V ω ≠ ⊤ → ContinuousOn (W · ω) (Iic (V ω).toNNReal) ∧
      (∀ i, ContinuousOn (VL i · ω) (Iic (V ω).toNNReal)) ∧ ∀ j, ContinuousOn (VR j · ω) (Iic (V ω).toNNReal))
    (hX : Measurable X) (hV0 : ∀ᵐ ω ∂P, ω ∈ L → 0 < V ω) {𝓗' : Filtration ℝ≥0 mΩ} (h𝒢' : 𝒢 ≤ 𝓗' 0)
    (hW' : AdaptedBefore 𝓗' V W) (hVL' : ∀ i, AdaptedBefore 𝓗' V (VL i))
    (hVR' : ∀ j, AdaptedBefore 𝓗' V (VR j))
    (hlaw : HasSafeLaw κ ρL ρR P 𝓗' L V W VL VR X) (hmem : HasSafeMembers P 𝓗' L V W X)
    (hXP : IsMeasurableKilledDriving W VL VR V)
    {σ : ℕ → Ω → WithTop ℝ≥0} (hσ : ∀ n, IsStoppingTime (drivingFiltration P hXP) (σ n))
    (hσm : ∀ ω, Monotone fun n => σ n ω) (hσV : ∀ᵐ ω ∂P, ω ∈ L → ∀ n, (σ n ω : ℝ≥0∞) < V ω)
    (hσlim : ∀ᵐ ω ∂P, ω ∈ L → Tendsto (fun n => (σ n ω : ℝ≥0∞)) atTop (𝓝 (V ω)))
    (htype : ∀ᵐ ω ∂P, ω ∈ L → IsFlowType κ θ (c ω) (ΘL ω) (ΘR ω) ρL ρR)
    (hXH : ∀ ω, IsTranslateAddConst 0 (θ * QuantumZipper.chiC κ) (Hc ω) (X ω)) (h𝒢m : 𝒢 ≤ mΩ)
    (hL : MeasurableSet[𝒢] L) (hc : Measurable[𝒢] c) (hH : Measurable Hc) (hWm : ∀ t, Measurable (W t))
    (hVm : Measurable V) :
    ∀ᵐ ω ∂P, ω ∈ L → IsStopDrvMatch (Fd (c ω, Hc ω)) (fun t => W t ω) (V ω) := by
  have hfst : Measurable[𝒢.comap Prod.fst, 𝒢] (Prod.fst : Ω × Ω₀ → Ω) := Measurable.of_comap_le le_rfl
  have h𝒢f : 𝒢.comap Prod.fst ≤ (inferInstance : MeasurableSpace (Ω × Ω₀)) :=
    (MeasurableSpace.comap_mono h𝒢m).trans measurable_fst.comap_le
  have hK := ae_isStoppedHullCoupling_k_prod (P₀ := P₀) hE hcont hX hV0 h𝒢' hW' hVL' hVR' hlaw hmem hXP hσ hσm
    hσV hσlim
  have htype' : ∀ᵐ p₀ ∂(P.prod P₀), p₀.1 ∈ L → IsFlowType κ θ (c p₀.1) (ΘL p₀.1) (ΘR p₀.1) ρL ρR :=
    ae_fst_of_ae (P₀ := P₀) htype
  have h : ∀ᵐ p₀ ∂(P.prod P₀), p₀ ∈ Prod.fst ⁻¹' L →
      ∀ᵐ p ∂(condExpKernel (P.prod P₀) (𝒢.comap Prod.fst) p₀),
        IsStopDrvMatch (Fd (c p₀.1, Hc p.1)) (fun t => W t p.1) (V p.1) := by
    filter_upwards [hK, htype'] with p₀ hp₀ hty hp₀L
    obtain ⟨𝓕', W', VL', VR', B', hcpl, hag⟩ := hp₀ hp₀L
    obtain ⟨eL, eR, hxL, hxR, hρL, hρR⟩ := hty hp₀L
    have h' := isStoppedHullCoupling_cast eL eR hcpl
    rw [hxL, hxR, hρL, hρR] at h'
    exact ae_isStopDrvMatch_of_isStoppedHullCoupling hext hFd (c p₀.1) (fun p : Ω × Ω₀ => hXH p.1) h'
      (fun t => (hWm t).comp measurable_fst) (hH.comp measurable_fst) (hVm.comp measurable_fst)
      (hag.mono fun p hp t ht => (hp t ht).1)
  have h2 := ae_isStopDrvMatch_of_ae_condExpKernel (P := P.prod P₀) (𝒢 := 𝒢.comap Prod.fst) hFd.1 h𝒢f
    ⟨L, hL, rfl⟩ (hc.comp hfst) (hH.comp measurable_fst) (fun t => (hWm t).comp measurable_fst)
    (hVm.comp measurable_fst) h
  exact ae_of_ae_fst (P₀ := P₀) (q := fun ω => ω ∈ L → IsStopDrvMatch (Fd (c ω, Hc ω)) (fun t => W t ω) (V ω)) h2

end K2

/-! ### The generic chain -/

section Generic

variable {Ω : Type} {𝒢 : MeasurableSpace Ω} [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω] {P : Measure Ω}
  [IsProbabilityMeasure P] {nL nR : ℕ} {κ θ : ℝ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ}

/-- **The stopped (Det) from (S) and (L), driver form** (the driver form of
`StoppedK2.ae_stoppedCodeMatch_of_hasSafeLaw`, with Aux. lemma 54 and a canonical driver code; no Theorem 1.3 and
no trace of the continuation). The continuation is a globally continuous adapted driver `W` from `0` with the
geometric images of a sorted random word `(xL, xR)` of the flow-line type of `c`, stopped at a stopping time `V` of
`𝓗` with `0 < V ≤ thr`, with (S) and (L) with lifetime `V`, an announcing sequence of `V` in the usual augmentation of
`𝓗` and announcing stopping times of the killed driving filtration. Then almost surely `V` is at most the lifetime of
the canonical driver code `Fd (c, Hc)` and `W` is that code at the dyadic times before `V`. -/
theorem ae_isStopDrvMatch_of_hasSafeLaw (hext : StoppedHullExtendStatement.{0} κ) (hκ : 0 < κ)
    {Fd : BoundaryWord × DistOn upperHalfPlaneOpens → PCode × ℝ≥0∞} (hFd : IsCanonicalDriverCode κ θ Fd)
    {𝓗 : Filtration ℝ≥0 mΩ} (h𝒢 : 𝒢 ≤ 𝓗 0) {c : Ω → BoundaryWord} (hc : Measurable[𝒢] c)
    {xL : Ω → Fin nL → ℝ} {xR : Ω → Fin nR → ℝ} (hxL : Measurable[𝒢] xL) (hxR : Measurable[𝒢] xR)
    (hxL0 : ∀ ω i, xL ω i ≤ 0) (hxR0 : ∀ ω j, 0 ≤ xR ω j) (hxLa : ∀ ω, Antitone (xL ω))
    (hxRm : ∀ ω, Monotone (xR ω)) (htype : ∀ᵐ ω ∂P, IsFlowType κ θ (c ω) (xL ω) (xR ω) ρL ρR)
    {W : ℝ≥0 → Ω → ℝ} (hW0 : ∀ ω, W 0 ω = 0) (hWc : ∀ ω, Continuous fun t => W t ω)
    (hWa : StronglyAdapted 𝓗 W) {Hc X : Ω → DistOn upperHalfPlaneOpens} (hHc : Measurable Hc)
    (hX : Measurable X) (hXH : ∀ ω, IsTranslateAddConst 0 (θ * QuantumZipper.chiC κ) (Hc ω) (X ω))
    (hint : ∀ φ : TestOn upperHalfPlaneOpens, Integrable (fun ω => X ω φ) P)
    {V : Ω → ℝ≥0∞} (hVst : ∀ t : ℝ≥0, MeasurableSet[𝓗 t] {ω | V ω ≤ t}) (hV0 : ∀ᵐ ω ∂P, 0 < V ω)
    (hVthr : ∀ᵐ ω ∂P, V ω ≤ thr ρL ρR W xL xR ω)
    {T : ℕ → Ω → ℝ≥0} (hT : Coupling.IsAnnouncingSeq (usualAugmentation 𝓗 P) P V T)
    (hXP : IsMeasurableKilledDriving W (geomLW W xL) (geomRW W xR) V)
    {σ : ℕ → Ω → WithTop ℝ≥0} (hσ : ∀ n, IsStoppingTime (drivingFiltration P hXP) (σ n))
    (hσm : ∀ ω, Monotone fun n => σ n ω) (hσV : ∀ᵐ ω ∂P, ∀ n, (σ n ω : ℝ≥0∞) < V ω)
    (hσlim : ∀ᵐ ω ∂P, Tendsto (fun n => (σ n ω : ℝ≥0∞)) atTop (𝓝 (V ω)))
    (hlaw : HasSafeLaw κ ρL ρR P 𝓗 univ V W (geomLW W xL) (geomRW W xR) X)
    (hmem : HasSafeMembers P 𝓗 univ V W X) :
    ∀ᵐ ω ∂P, IsStopDrvMatch (Fd (c ω, Hc ω)) (fun t => W t ω) (V ω) := by
  have h𝒢m : 𝒢 ≤ mΩ := h𝒢.trans (𝓗.le 0)
  have hxL₀ : Measurable[𝓗 0] xL := hxL.mono h𝒢 le_rfl
  have hxR₀ : Measurable[𝓗 0] xR := hxR.mono h𝒢 le_rfl
  have hWa₀ : AdaptedBefore 𝓗 V W := MartChar.adaptedBefore_of_stronglyAdapted hVst hWa
  have hVLa₀ : ∀ i, AdaptedBefore 𝓗 V (geomLW W xL i) := fun i =>
    MartChar.adaptedBefore_of_stronglyAdapted hVst (stronglyAdapted_geomLW hWa hWc hxL₀ i)
  have hVRa₀ : ∀ j, AdaptedBefore 𝓗 V (geomRW W xR j) := fun j =>
    MartChar.adaptedBefore_of_stronglyAdapted hVst (stronglyAdapted_geomRW hWa hWc hxR₀ j)
  have hXψ : ∀ ψ : TestOn upperHalfPlaneOpens, Measurable fun ω => X ω ψ := fun ψ =>
    ((measurable_pi_apply ψ).comp (Measurable.of_comap_le le_rfl)).comp hX
  have hcf := DomainMarkov.Aux79.isCouplingCharFun_of_hasSafeLaw X hXψ hlaw
    (ae_of_all _ (isForceReg_thr hW0 hWc xL xR V)) (ae_of_all _ fun ω h => absurd (mem_univ ω) h) hWa₀ hVLa₀
    hVRa₀
  have hWaU : StronglyAdapted (usualAugmentation 𝓗 P) W := fun t =>
    (hWa t).mono (Ito.le_usualAugmentation 𝓗 P t)
  have hVU : IsStoppingTime (usualAugmentation 𝓗 P) fun ω => (V ω : WithTop ℝ≥0) := fun t =>
    Ito.le_usualAugmentation 𝓗 P t _ (hVst t)
  obtain ⟨P₀, hP₀, 𝓦, B, hE, -, -⟩ := isRandomWordEvolutionUpTo_prod_of_isCouplingCharFun
    (𝒢 := 𝒢) hκ (fun s hs h0 => Ito.measurableSet_usualAugmentation_of_null hs h0 0)
    (h𝒢.trans (Ito.le_usualAugmentation 𝓗 P 0)) MeasurableSet.univ hxL hxR hxL0 hxR0 hxLa hxRm hW0 hWc hWaU
    hVU hT hint hcf (hVthr.mono fun ω h _ => h)
  have hVm : Measurable V := by
    refine measurable_of_Iic fun t => ?_
    induction t using ENNReal.recTopCoe with
    | top => simp only [Iic_top, preimage_univ, MeasurableSet.univ]
    | coe t => exact 𝓗.le t _ (hVst t)
  have hcont : ∀ᵐ ω ∂P, ω ∈ (univ : Set Ω) → V ω ≠ ⊤ → ContinuousOn (W · ω) (Iic (V ω).toNNReal) ∧
      (∀ i, ContinuousOn (geomLW W xL i · ω) (Iic (V ω).toNNReal)) ∧
        ∀ j, ContinuousOn (geomRW W xR j · ω) (Iic (V ω).toNNReal) :=
    ae_of_all _ fun ω _ _ => ⟨(hWc ω).continuousOn, fun i => (isForcePath_geomLW hWc xL ω i).1.continuousOn,
      fun j => (isForcePath_geomRW hWc xR ω j).1.continuousOn⟩
  have hWm : ∀ t, Measurable (W t) := fun t => (hWa t).measurable.mono (𝓗.le t) le_rfl
  have h := ae_isStopDrvMatch_of_k (P₀ := P₀) (L := univ) (ΘL := xL) (ΘR := xR) hext hFd hE hcont hX
    (hV0.mono fun ω h _ => h) h𝒢 hWa₀ hVLa₀ hVRa₀ hlaw hmem hXP hσ hσm (hσV.mono fun ω h _ => h)
    (hσlim.mono fun ω h _ => h) (htype.mono fun ω h _ => h) hXH h𝒢m MeasurableSet.univ hc hHc hWm hVm
  filter_upwards [h] with ω hω using hω (mem_univ ω)

end Generic

end InteractingSLE.Supp8.GB6.RelDrv
