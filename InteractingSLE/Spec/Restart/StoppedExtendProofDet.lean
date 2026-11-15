/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Restart.StoppedExtend
import InteractingSLE.Spec.Restart.DomainMarkovK2Det
import InteractingSLE.Spec.Exist.DetField
import InteractingSLE.Spec.Theorem15Inputs

/-!
# Aux. lemma 54 for general words, consumed: determination of a stopped flow line by its field

Packet PROVE-DOMAINMARKOV9. Specification p. 295 (Lemma 7.8's restart, used by Lemma G7, Lemma 7.6 and GB6): "For a
stopped portion, the same conclusion follows by appending the canonical future in its active residual field and
applying that uniqueness, then restricting back to the recorded stop"; p. 327 (Aux. lemma 97, used by Lemma G3):
"a stopped flow-line coupling with these laws extends to a full one (Aux. 54) so that Theorem 1.2 identifies its path
with the field-determined reference path".

* `IsStoppedFlowLine κ b jumps x θ P h η e`: **a flow line through the stop `e`** — the frozen `IsFlowLine` with the
  optional hull coupling replaced by PROVE-DOMAINMARKOV7's coupling through a stop (`IsStoppedHullCoupling`), and
  `η − x` the generating trace of its driver through `e`;
* `trace_eq_of_driver_eq` (pathwise): two generating traces of drivers that agree before `e` agree on `[0, e]`;
* `IsFlowDet κ b jumps x θ G`: a determination clause (every flow line of the data matches the code `G` of its field);
  canonical flow codes give one (`IsCanonicalFlowCode.isFlowDet`);
* **`ae_stopMatch_on_extension`**: on an extension of a stopped flow line (a full coupling of the same field on `Ω × C`
  agreeing with the stopped driver through `e`), with Theorem 1.3 and a determination clause, the stopped path is a.s.
  the decoded code on `[0, e]` (`IsStopMatch`);
* `StoppedHullExtendKStatement` (**named input**, the kernel form `E = P ⊗ K` of PROVE-DOMAINMARKOV7's
  `StoppedHullExtendStatement`, which it implies: `stoppedHullExtendStatement_of_kernel`) and `ae_of_ae_compProd_fst`
  (a.s. properties of the first factor pass to `P` without measurability);
* **`IsStoppedFlowLine.ae_stopMatch_of_extend`** (DM7's form; measurable field, path and stop) and
  **`IsStoppedFlowLine.ae_stopMatch_of_extendK`** (kernel form; no measurability), and the canonical-code instance
  **`IsStoppedFlowLine.ae_codeMatch_le`**;
* **`ae_stoppedCodeMatch_of_ae_condExpKernel`**: the same under the regular conditional law, lifted to `P` (the stopped
  form of `K2.ae_codeMatch_of_ae_condExpKernel_isFlowLine`: the (Det) clause of `RetainedCanonCondDetStatement`,
  `Lemma76DetStatement` and `GB6CondDetStatement`, whose continuations are known only up to a stop).

**R43/R48.** The canonical flow codes exist only through Theorems 1.2–1.3; these results serve Theorems 1.4–1.5 only.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open LQGMetric (DistOn)
open scoped NNReal ENNReal

universe u

namespace InteractingSLE

namespace Restart

namespace StoppedExtend

open Sec2.Assembly

/-! ### Stopped flow lines -/

/-- **A flow line through the stop `e`** (the frozen `IsFlowLine`, with the optional hull coupling replaced by a
coupling through `e`, `IsStoppedHullCoupling`): `h' = h(· + x) + θχ` is coupled through `e` with a driving process of
the flow-line word of `(b, jumps)` from `x` at the angle `θ`, and almost surely `η − x` is the generating trace of the
driver through `e`. -/
def IsStoppedFlowLine (κ : ℝ) (b : ℝ → ℝ) (jumps : Finset ℝ) (x θ : ℝ) {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (P : Measure Ω) (h : Ω → DistOn upperHalfPlaneOpens) (η : Ω → ℝ≥0 → ℂ) (e : Ω → ℝ≥0∞) : Prop :=
  ∃ (h' : Ω → DistOn upperHalfPlaneOpens) (𝓕 : Filtration ℝ≥0 mΩ) (W : ℝ≥0 → Ω → ℝ)
    (VL : Fin (flowLineNL b jumps x) → ℝ≥0 → Ω → ℝ) (VR : Fin (flowLineNR b jumps x) → ℝ≥0 → Ω → ℝ)
    (B : ℝ≥0 → Ω → ℝ),
    (∀ ω, IsTranslateAddConst x (θ * QuantumZipper.chiC κ) (h ω) (h' ω)) ∧
    IsStoppedHullCoupling κ (flowLineXL b jumps x) (flowLineXR b jumps x) (flowLineRhoL κ b jumps x θ)
      (flowLineRhoR κ b jumps x θ) P 𝓕 W VL VR B e h' ∧
    ∀ᵐ ω ∂P, IsGeneratingTrace (fun t => W t ω) (e ω) (fun t => η ω t - x)

/-! ### Traces of agreeing drivers -/

/-- **Two generating traces of drivers that agree before `e` agree on `[0, e]`** (`e` at most both lifetimes; the
drivers continuous before their lifetimes and `0` at `0`). Before `e` both are the trace at that time of the common
driver (`LP.traceAt`); at `e` itself by continuity. -/
theorem trace_eq_of_driver_eq {w w' : ℝ≥0 → ℝ} {T T' e : ℝ≥0∞} {η η' : ℝ≥0 → ℂ}
    (hη : IsGeneratingTrace w T η) (hw : ContinuousOn w {s | (s : ℝ≥0∞) < T}) (hw0 : w 0 = 0)
    (hη' : IsGeneratingTrace w' T' η') (hw' : ContinuousOn w' {s | (s : ℝ≥0∞) < T'}) (hw0' : w' 0 = 0)
    (heT : e ≤ T) (heT' : e ≤ T') (hag : ∀ s : ℝ≥0, (s : ℝ≥0∞) < e → w s = w' s) :
    ∀ t : ℝ≥0, (t : ℝ≥0∞) ≤ e → η t = η' t := by
  have hlt : ∀ t : ℝ≥0, (t : ℝ≥0∞) < e → η t = η' t := fun t ht => by
    rw [← LP.traceAt_eq_of_isGeneratingTrace hη hw hw0 (ht.trans_le heT),
      ← LP.traceAt_eq_of_isGeneratingTrace hη' hw' hw0' (ht.trans_le heT'),
      LP.traceAt_congr fun r hr => hag r ((ENNReal.coe_le_coe.2 hr).trans_lt ht)]
  intro t ht
  rcases lt_or_eq_of_le ht with h1 | h1
  · exact hlt t h1
  · rcases eq_or_ne t 0 with h0 | h0
    · rw [h0, hη.1, hη'.1]
    · have hIic : Iic t ⊆ {s : ℝ≥0 | (s : ℝ≥0∞) ≤ T} := fun s hs =>
        (ENNReal.coe_le_coe.2 hs).trans (h1 ▸ heT)
      have hIic' : Iic t ⊆ {s : ℝ≥0 | (s : ℝ≥0∞) ≤ T'} := fun s hs =>
        (ENNReal.coe_le_coe.2 hs).trans (h1 ▸ heT')
      have hpos : (Iio t).Nonempty := ⟨0, pos_iff_ne_zero.2 h0⟩
      refine EqOn.of_subset_closure (s := Iio t) (fun s hs => hlt s ?_) (hη.2.1.mono hIic) (hη'.2.1.mono hIic')
        Iio_subset_Iic_self (by rw [closure_Iio' hpos]) (mem_Iic.2 le_rfl)
      rw [← h1]
      exact ENNReal.coe_lt_coe.2 hs

/-! ### The stopped code match -/

/-- The dyadic form of the stopped match of a path `η` stopped at `e` with a code depending on the point. -/
def stopMatchSet {C S : Type*} (G : C × S → (PCode × PCode) × ℝ≥0∞) (η : S → ℝ≥0 → ℂ) (e : S → ℝ≥0∞) :
    Set (C × S) :=
  {p | e p.2 ≤ (G p).2 ∧ ∀ n k : ℕ, (dyad n k : ℝ≥0∞) ≤ e p.2 → η p.2 (dyad n k) = decPath (G p) (dyad n k)}

theorem measurableSet_stopMatchSet {C S : Type*} [MeasurableSpace C] [MeasurableSpace S]
    {G : C × S → (PCode × PCode) × ℝ≥0∞} (hG : Measurable G) {η : S → ℝ≥0 → ℂ}
    (hη : ∀ t, Measurable fun s => η s t) {e : S → ℝ≥0∞} (he : Measurable e) :
    MeasurableSet (stopMatchSet G η e) := by
  have he' : Measurable fun p : C × S => e p.2 := he.comp measurable_snd
  have hl : MeasurableSet {p : C × S | e p.2 ≤ (G p).2} := measurableSet_le he' (measurable_snd.comp hG)
  have hd : ∀ n k : ℕ, MeasurableSet {p : C × S | (dyad n k : ℝ≥0∞) ≤ e p.2 →
      η p.2 (dyad n k) = decPath (G p) (dyad n k)} := fun n k => by
    have h1 : MeasurableSet {p : C × S | (dyad n k : ℝ≥0∞) ≤ e p.2} := measurableSet_le measurable_const he'
    have h2 : MeasurableSet {p : C × S | η p.2 (dyad n k) = decPath (G p) (dyad n k)} :=
      measurableSet_eq_fun ((hη _).comp measurable_snd) ((measurable_decPath _).comp hG)
    have e : {p : C × S | (dyad n k : ℝ≥0∞) ≤ e p.2 → η p.2 (dyad n k) = decPath (G p) (dyad n k)} =
        {p : C × S | (dyad n k : ℝ≥0∞) ≤ e p.2}ᶜ ∪ {p : C × S | η p.2 (dyad n k) = decPath (G p) (dyad n k)} := by
      ext p
      simp only [mem_ofPred_eq, mem_union, mem_compl_iff, imp_iff_not_or]
    rw [e]
    exact h1.compl.union h2
  have e : stopMatchSet G η e = {p : C × S | e p.2 ≤ (G p).2} ∩ ⋂ n : ℕ, ⋂ k : ℕ,
      {p : C × S | (dyad n k : ℝ≥0∞) ≤ e p.2 → η p.2 (dyad n k) = decPath (G p) (dyad n k)} := by
    ext p
    simp only [stopMatchSet, mem_ofPred_eq, mem_inter_iff, mem_iInter]
  rw [e]
  exact hl.inter (MeasurableSet.iInter fun n => MeasurableSet.iInter fun k => hd n k)

/-- On the dyadic stopped match set, a path continuous on `[0, e]` agrees with the decoded code on `[0, e]`. -/
theorem stopMatch_of_mem {C S : Type*} {G : C × S → (PCode × PCode) × ℝ≥0∞} {η : S → ℝ≥0 → ℂ}
    {e : S → ℝ≥0∞} {p : C × S} (hc : ContinuousOn (η p.2) {t | (t : ℝ≥0∞) ≤ e p.2})
    (hp : p ∈ stopMatchSet G η e) :
    e p.2 ≤ (G p).2 ∧ ∀ t : ℝ≥0, (t : ℝ≥0∞) ≤ e p.2 → η p.2 t = decPath (G p) t := by
  obtain ⟨hle, hd⟩ := hp
  exact ⟨hle, eqOn_of_dyad hc ((continuousOn_decPath (G p)).mono fun t ht => le_trans ht hle) hd⟩

/-- **The stopped match**: `e` precedes the lifetime of the path code `p`, and the path `η` is the decoded code on
`[0, e]`. -/
def IsStopMatch (p : (PCode × PCode) × ℝ≥0∞) (η : ℝ≥0 → ℂ) (e : ℝ≥0∞) : Prop :=
  e ≤ p.2 ∧ ∀ t : ℝ≥0, (t : ℝ≥0∞) ≤ e → η t = decPath p t

/-- **A determination clause for flow lines of fixed data** (Theorem 1.2, read through a path code): every angle-`θ`
flow line of `(b, jumps)` from `x`, on every probability space of universe `u`, almost surely matches the code `G` of
its field (`IsCodeMatch`: lifetimes equal, paths equal on the lifetime). -/
def IsFlowDet (κ : ℝ) (b : ℝ → ℝ) (jumps : Finset ℝ) (x θ : ℝ)
    (G : DistOn upperHalfPlaneOpens → (PCode × PCode) × ℝ≥0∞) : Prop :=
  ∀ {Ω : Type u} [MeasurableSpace Ω] (Q : Measure Ω) [IsProbabilityMeasure Q] (h : Ω → DistOn upperHalfPlaneOpens)
    (η : Ω → ℝ≥0 → ℂ) (ζ : Ω → ℝ≥0∞), IsFlowLine κ b jumps x θ Q h η ζ →
      ∀ᵐ ω ∂Q, IsCodeMatch (G (h ω)) (η ω) (ζ ω)

/-- A canonical flow code gives the determination clause for every word and seed (universe `0`). -/
theorem IsCanonicalFlowCode.isFlowDet {κ θ : ℝ}
    {F : (BoundaryWord × ℝ) × DistOn upperHalfPlaneOpens → (PCode × PCode) × ℝ≥0∞}
    (hF : IsCanonicalFlowCode κ θ F) (c : BoundaryWord) (x : ℝ) :
    IsFlowDet.{0} κ c.fn c.jumps x θ fun f => F ((c, x), f) :=
  fun Q _ h η ζ hfl => hF.2.2 c x Q h η ζ hfl

/-- **The stopped match on an extension.** Let a stopped flow line (field `h`, its translate `h'`, driver `W` through
`e`, `η − x` its generating trace) have an extension `E` on `Ω × C` (first marginal `P`): a full optional hull
coupling of `h' ∘ fst` whose driver agrees with `W` through `e`. With Theorem 1.3 and a determination clause `G`,
almost surely on `E` the first factor's stopped path is the decoded code of its field on `[0, e]`. The extension's
driver has a generating trace (Theorem 1.3), which is a flow line of `h ∘ fst`, hence matches `G` (determination); the
two traces agree on `[0, e]` (`trace_eq_of_driver_eq`). -/
theorem ae_stopMatch_on_extension {κ θ : ℝ} {b : ℝ → ℝ} {jumps : Finset ℝ} {x : ℝ}
    (h13 : Exist.Theorem13Statement.{u}) (hκ : 0 < κ) {G : DistOn upperHalfPlaneOpens → (PCode × PCode) × ℝ≥0∞}
    (hdet : IsFlowDet.{u} κ b jumps x θ G) {Ω : Type u} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {h h' : Ω → DistOn upperHalfPlaneOpens} {η : Ω → ℝ≥0 → ℂ} {e : Ω → ℝ≥0∞} {W : ℝ≥0 → Ω → ℝ}
    {VL : Fin (flowLineNL b jumps x) → ℝ≥0 → Ω → ℝ} {VR : Fin (flowLineNR b jumps x) → ℝ≥0 → Ω → ℝ}
    {B : ℝ≥0 → Ω → ℝ} (htr : ∀ ω, IsTranslateAddConst x (θ * QuantumZipper.chiC κ) (h ω) (h' ω))
    (hpath : ∀ᵐ ω ∂P, Sec2.IsSLEPathUpTo κ (flowLineXL b jumps x) (flowLineXR b jumps x)
      (flowLineRhoL κ b jumps x θ) (flowLineRhoR κ b jumps x θ) (fun t => W t ω) (fun i t => VL i t ω)
      (fun i t => VR i t ω) (fun t => B t ω) (e ω))
    (hgen : ∀ᵐ ω ∂P, IsGeneratingTrace (fun t => W t ω) (e ω) (fun t => η ω t - x))
    {C : Type u} [MeasurableSpace C] {E : Measure (Ω × C)} [IsProbabilityMeasure E]
    (hmap : E.map Prod.fst = P) {𝓕' : Filtration ℝ≥0 (inferInstance : MeasurableSpace (Ω × C))}
    {W' : ℝ≥0 → Ω × C → ℝ} {VL' : Fin (flowLineNL b jumps x) → ℝ≥0 → Ω × C → ℝ}
    {VR' : Fin (flowLineNR b jumps x) → ℝ≥0 → Ω × C → ℝ} {B' : ℝ≥0 → Ω × C → ℝ} {ζ' : Ω × C → ℝ≥0∞}
    (hC : IsOptionalHullCoupling κ (flowLineXL b jumps x) (flowLineXR b jumps x) (flowLineRhoL κ b jumps x θ)
      (flowLineRhoR κ b jumps x θ) E 𝓕' W' VL' VR' B' ζ' (fun p => h' p.1))
    (hag : ∀ᵐ p ∂E, e p.1 ≤ ζ' p ∧ ∀ t : ℝ≥0, (t : ℝ≥0∞) ≤ e p.1 → (t : ℝ≥0∞) < ζ' p →
      W' t p = W t p.1 ∧ (∀ i, VL' i t p = VL i t p.1) ∧ ∀ j, VR' j t p = VR j t p.1) :
    ∀ᵐ p ∂E, IsStopMatch (G (h p.1)) (η p.1) (e p.1) := by
  classical
  have hord := Theorem15.isOrderedForceWord_flowLine b jumps x
  -- the extension's trace (Theorem 1.3)
  have htr' := h13 hκ hord hC.1
  set Γ : Ω × C → ℝ≥0 → ℂ := fun p t =>
    if hp : ∃ η' : ℝ≥0 → ℂ, IsGeneratingTrace (fun s => W' s p) (ζ' p) η' then hp.choose t + x else x with hΓdef
  have hΓ : ∀ᵐ p ∂E, IsGeneratingTrace (fun t => W' t p) (ζ' p) (fun t => Γ p t - x) := by
    filter_upwards [htr'] with p hp
    obtain ⟨η', hη', -⟩ := hp.2
    have hp' : ∃ η' : ℝ≥0 → ℂ, IsGeneratingTrace (fun s => W' s p) (ζ' p) η' := ⟨η', hη'⟩
    have e1 : (fun t => Γ p t - x) = hp'.choose := funext fun t => by
      simp only [hΓdef, hp', ↓reduceDIte, add_sub_cancel_right]
    rw [e1]
    exact hp'.choose_spec
  -- the extension carries a flow line of the field read through the first factor
  have hfl' : IsFlowLine κ b jumps x θ E (fun p => h p.1) Γ ζ' :=
    ⟨fun p => h' p.1, 𝓕', W', VL', VR', B', fun p => htr p.1, hC, hΓ⟩
  have hcm := hdet E (fun p => h p.1) Γ ζ' hfl'
  -- the stopped coupling's paths, read on the extension
  have hmapE : AEMeasurable (Prod.fst : Ω × C → Ω) E := measurable_fst.aemeasurable
  have hgenE : ∀ᵐ p ∂E, IsGeneratingTrace (fun t => W t p.1) (e p.1) (fun t => η p.1 t - x) :=
    ae_of_ae_map hmapE (by rw [hmap]; exact hgen)
  have hpathE := ae_of_ae_map hmapE (by rw [hmap]; exact hpath)
  filter_upwards [hag, hcm, hΓ, hC.1.2.2.2.2, hgenE, hpathE] with p hagp hcmp hΓp hpp hgp hsp
  obtain ⟨heζ, hagr⟩ := hagp
  obtain ⟨hζF, hmatch⟩ := hcmp
  have heq : ∀ t : ℝ≥0, (t : ℝ≥0∞) ≤ e p.1 → η p.1 t - x = Γ p t - x :=
    trace_eq_of_driver_eq hgp hsp.continuousOn_w hsp.w_zero hΓp hpp.2.2.2.1 hpp.1 le_rfl heζ
      fun s hs => (hagr s hs.le (hs.trans_le heζ)).1.symm
  refine ⟨hζF ▸ heζ, fun t ht => ?_⟩
  rw [sub_left_inj.1 (heq _ ht)]
  exact hmatch _ (ht.trans heζ)

/-- **A property of the first factor holding almost surely under `P ⊗ K` holds `P`-almost surely** (`K` Markov), with
no measurability of the property: a measurable null set `N` containing the bad pairs has `K ω (N_ω) = 0` for
`P`-almost every `ω`, and `N_ω` is everything at a bad `ω`. -/
theorem ae_of_ae_compProd_fst {Ω C : Type*} [MeasurableSpace Ω] [MeasurableSpace C] {P : Measure Ω} [SFinite P]
    {K : Kernel Ω C} [IsMarkovKernel K] {A : Ω → Prop} (h : ∀ᵐ p ∂(P ⊗ₘ K), A p.1) : ∀ᵐ ω ∂P, A ω := by
  obtain ⟨N, hsub, hNm, hN0⟩ := exists_measurable_superset_of_null (ae_iff.1 h)
  rw [Measure.compProd_apply hNm] at hN0
  have h0 := (lintegral_eq_zero_iff (Kernel.measurable_kernel_prodMk_left hNm)).1 hN0
  filter_upwards [h0] with ω hω
  by_contra hA
  have huniv : Prod.mk ω ⁻¹' N = univ := eq_univ_of_forall fun c => hsub (show ¬A (ω, c).1 from hA)
  rw [Pi.zero_apply, huniv, measure_univ] at hω
  exact one_ne_zero hω

/-- **Named input: Aux. lemma 54 for general words, kernel form.** `StoppedHullExtendStatement` with the extension
sampled by a Markov kernel from the first factor, `E = P ⊗ K` (Aux. lemma 54, p. 246: "Use that kernel at
`(𝓗_S, H_S)` to sample the new future"; the record-law construction of the seed case, `LocalExt.IsRecordExtension`,
has this form with `K = κ₀ ∘ record`). It gives the general statement (`stoppedHullExtendStatement_of_kernel`) and lets
almost sure properties of the first factor pass to `P` without measurability (`ae_of_ae_compProd_fst`). -/
def StoppedHullExtendKStatement (κ : ℝ) : Prop :=
  ∀ {nL nR : ℕ} (xL : Fin nL → ℝ) (xR : Fin nR → ℝ) (ρL : Fin nL → ℝ) (ρR : Fin nR → ℝ),
    IsOrderedForceWord xL xR →
    ∀ {Ω : Type u} {mΩ : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P] (𝓕 : Filtration ℝ≥0 mΩ)
      (W : ℝ≥0 → Ω → ℝ) (VL : Fin nL → ℝ≥0 → Ω → ℝ) (VR : Fin nR → ℝ≥0 → Ω → ℝ) (B : ℝ≥0 → Ω → ℝ)
      (V : Ω → ℝ≥0∞) (h : Ω → LQGMetric.DistOn upperHalfPlaneOpens),
      IsStoppedHullCoupling κ xL xR ρL ρR P 𝓕 W VL VR B V h →
      ∃ (C : Type u) (_ : MeasurableSpace C) (K : Kernel Ω C) (_ : IsMarkovKernel K)
        (𝓕' : Filtration ℝ≥0 (inferInstance : MeasurableSpace (Ω × C))) (W' : ℝ≥0 → Ω × C → ℝ)
        (VL' : Fin nL → ℝ≥0 → Ω × C → ℝ) (VR' : Fin nR → ℝ≥0 → Ω × C → ℝ) (B' : ℝ≥0 → Ω × C → ℝ)
        (ζ' : Ω × C → ℝ≥0∞),
        IsOptionalHullCoupling κ xL xR ρL ρR (P ⊗ₘ K) 𝓕' W' VL' VR' B' ζ' (fun p => h p.1) ∧
        ∀ᵐ p ∂(P ⊗ₘ K), V p.1 ≤ ζ' p ∧ ∀ t : ℝ≥0, (t : ℝ≥0∞) ≤ V p.1 → (t : ℝ≥0∞) < ζ' p →
          W' t p = W t p.1 ∧ (∀ i, VL' i t p = VL i t p.1) ∧ ∀ j, VR' j t p = VR j t p.1

/-- The kernel form gives PROVE-DOMAINMARKOV7's `StoppedHullExtendStatement` (`E = P ⊗ K` has first marginal `P`). -/
theorem stoppedHullExtendStatement_of_kernel {κ : ℝ} (hK : StoppedHullExtendKStatement.{u} κ) :
    StoppedHullExtendStatement.{u} κ := by
  intro nL nR xL xR ρL ρR hF Ω mΩ P _ 𝓕 W VL VR B V h hSC
  obtain ⟨C, mC, K, hKm, 𝓕', W', VL', VR', B', ζ', hC, hag⟩ := hK xL xR ρL ρR hF P 𝓕 W VL VR B V h hSC
  exact ⟨C, mC, P ⊗ₘ K, inferInstance, 𝓕', W', VL', VR', B', ζ', Measure.fst_compProd P K, hC, hag⟩

/-- **A stopped flow line matches a determination code on `[0, e]`**, given Aux. lemma 54 for general words
(PROVE-DOMAINMARKOV7's `StoppedHullExtendStatement`) and Theorem 1.3 (measurable field, path and stop). The extension
gives the match on `Ω × C` (`ae_stopMatch_on_extension`); it is a measurable event of the first factor (dyadic times),
so it passes to the first marginal `P`, and the continuity of both paths on `[0, e]` gives it at all times. -/
theorem IsStoppedFlowLine.ae_stopMatch_of_extend {κ θ : ℝ} {b : ℝ → ℝ} {jumps : Finset ℝ} {x : ℝ}
    (hext : StoppedHullExtendStatement.{u} κ) (h13 : Exist.Theorem13Statement.{u}) (hκ : 0 < κ)
    {G : DistOn upperHalfPlaneOpens → (PCode × PCode) × ℝ≥0∞} (hG : Measurable G)
    (hdet : IsFlowDet.{u} κ b jumps x θ G) {Ω : Type u} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {h : Ω → DistOn upperHalfPlaneOpens} {η : Ω → ℝ≥0 → ℂ} {e : Ω → ℝ≥0∞}
    (hh : Measurable h) (hηm : ∀ t, Measurable fun ω => η ω t) (hem : Measurable e)
    (hfl : IsStoppedFlowLine κ b jumps x θ P h η e) :
    ∀ᵐ ω ∂P, IsStopMatch (G (h ω)) (η ω) (e ω) := by
  obtain ⟨h', 𝓕, W, VL, VR, B, htr, hSC, hgen⟩ := hfl
  obtain ⟨C, mC, E, hE, 𝓕', W', VL', VR', B', ζ', hmap, hC, hag⟩ :=
    hext _ _ _ _ (Theorem15.isOrderedForceWord_flowLine b jumps x) P 𝓕 W VL VR B e h' hSC
  have hA := ae_stopMatch_on_extension h13 hκ hdet htr hSC.1.ae_path hgen hmap hC hag
  -- back to `P` through a measurable (dyadic) event
  set G' : Unit × Ω → (PCode × PCode) × ℝ≥0∞ := fun q => G (h q.2) with hG'def
  have hG'm : Measurable G' := hG.comp (hh.comp measurable_snd)
  have hSm : MeasurableSet {ω | ((), ω) ∈ stopMatchSet G' η e} :=
    measurable_prodMk_left (measurableSet_stopMatchSet hG'm hηm hem)
  have hP : ∀ᵐ ω ∂P, ω ∈ {ω | ((), ω) ∈ stopMatchSet G' η e} := by
    rw [← hmap]
    refine (ae_map_iff measurable_fst.aemeasurable hSm).2 ?_
    filter_upwards [hA] with p hp
    exact ⟨hp.1, fun n k hnk => hp.2 _ hnk⟩
  filter_upwards [hP, hgen] with ω hω hgω
  have hc : ContinuousOn (η ω) {t | (t : ℝ≥0∞) ≤ e ω} :=
    (hgω.2.1.add (continuousOn_const (c := (x : ℂ)))).congr fun t _ => by simp
  exact stopMatch_of_mem (G := G') (p := ((), ω)) hc hω

/-- **A stopped flow line matches a determination code on `[0, e]`, kernel form of Aux. lemma 54** (no measurability
of the field, the path or the stop is needed: `ae_of_ae_compProd_fst`). -/
theorem IsStoppedFlowLine.ae_stopMatch_of_extendK {κ θ : ℝ} {b : ℝ → ℝ} {jumps : Finset ℝ} {x : ℝ}
    (hext : StoppedHullExtendKStatement.{u} κ) (h13 : Exist.Theorem13Statement.{u}) (hκ : 0 < κ)
    {G : DistOn upperHalfPlaneOpens → (PCode × PCode) × ℝ≥0∞} (hdet : IsFlowDet.{u} κ b jumps x θ G)
    {Ω : Type u} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {h : Ω → DistOn upperHalfPlaneOpens} {η : Ω → ℝ≥0 → ℂ} {e : Ω → ℝ≥0∞}
    (hfl : IsStoppedFlowLine κ b jumps x θ P h η e) :
    ∀ᵐ ω ∂P, IsStopMatch (G (h ω)) (η ω) (e ω) := by
  obtain ⟨h', 𝓕, W, VL, VR, B, htr, hSC, hgen⟩ := hfl
  obtain ⟨C, mC, K, hK, 𝓕', W', VL', VR', B', ζ', hC, hag⟩ :=
    hext _ _ _ _ (Theorem15.isOrderedForceWord_flowLine b jumps x) P 𝓕 W VL VR B e h' hSC
  exact ae_of_ae_compProd_fst
    (ae_stopMatch_on_extension h13 hκ hdet htr hSC.1.ae_path hgen (Measure.fst_compProd P K) hC hag)

/-- **A stopped flow line is the decoded canonical flow code on `[0, e]`** (Aux. lemma 54 for general words, Theorem
1.3, and a canonical flow code `F`, i.e. Theorem 1.2). -/
theorem IsStoppedFlowLine.ae_codeMatch_le {κ θ : ℝ} (hext : StoppedHullExtendStatement.{0} κ)
    (h13 : Exist.Theorem13Statement.{0}) (hκ : 0 < κ)
    {F : (BoundaryWord × ℝ) × DistOn upperHalfPlaneOpens → (PCode × PCode) × ℝ≥0∞}
    (hF : IsCanonicalFlowCode κ θ F) (c : BoundaryWord) (x : ℝ) {Ω : Type} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] {h : Ω → DistOn upperHalfPlaneOpens} {η : Ω → ℝ≥0 → ℂ}
    {e : Ω → ℝ≥0∞} (hh : Measurable h) (hηm : ∀ t, Measurable fun ω => η ω t) (hem : Measurable e)
    (hfl : IsStoppedFlowLine κ c.fn c.jumps x θ P h η e) :
    ∀ᵐ ω ∂P, e ω ≤ (F ((c, x), h ω)).2 ∧
      ∀ t : ℝ≥0, (t : ℝ≥0∞) ≤ e ω → η ω t = decPath (F ((c, x), h ω)) t :=
  hfl.ae_stopMatch_of_extend hext h13 hκ (hF.1.comp (measurable_const.prodMk measurable_id))
    (IsCanonicalFlowCode.isFlowDet hF c x) hh hηm hem

/-- **(Det) through a stop, from stopped flow lines under the regular conditional law** (the stopped form of
`K2.ae_codeMatch_of_ae_condExpKernel_isFlowLine`). If, for `P`-almost every `ω₀` in a `𝒢`-event `M`, the path `γ`
stopped at `e` is, under `condExpKernel P 𝒢 ω₀`, a stopped angle-`θ` flow line from `(β ω₀).2` of the field `Hc` with
the boundary word `(β ω₀).1` (`β` is `𝒢`-measurable), then `P`-almost surely on `M` the stop precedes the lifetime of
the canonical code of `(β, Hc)` and `γ` is its decoded path on `[0, e]`. -/
theorem ae_stoppedCodeMatch_of_ae_condExpKernel {κ θ : ℝ} (hext : StoppedHullExtendStatement.{0} κ)
    (h13 : Exist.Theorem13Statement.{0}) (hκ : 0 < κ)
    {F : (BoundaryWord × ℝ) × DistOn upperHalfPlaneOpens → (PCode × PCode) × ℝ≥0∞}
    (hF : IsCanonicalFlowCode κ θ F) {Ω : Type} {𝒢 : MeasurableSpace Ω} [mΩ : MeasurableSpace Ω]
    [StandardBorelSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P] (h𝒢 : 𝒢 ≤ mΩ) {M : Set Ω}
    (hM : MeasurableSet[𝒢] M) {β : Ω → BoundaryWord × ℝ} (hβ : Measurable[𝒢] β)
    {Hc : Ω → DistOn upperHalfPlaneOpens} (hH : Measurable Hc) {γ : Ω → ℝ≥0 → ℂ}
    (hγ : ∀ t, Measurable fun ω => γ ω t) {e : Ω → ℝ≥0∞} (he : Measurable e)
    (hγc : ∀ ω, ContinuousOn (γ ω) {t | (t : ℝ≥0∞) ≤ e ω})
    (hfl : ∀ᵐ ω₀ ∂P, ω₀ ∈ M →
      IsStoppedFlowLine κ (β ω₀).1.fn (β ω₀).1.jumps (β ω₀).2 θ (condExpKernel P 𝒢 ω₀) Hc γ e) :
    ∀ᵐ ω ∂P, ω ∈ M → e ω ≤ (F (β ω, Hc ω)).2 ∧
      ∀ t : ℝ≥0, (t : ℝ≥0∞) ≤ e ω → γ ω t = decPath (F (β ω, Hc ω)) t := by
  set G : (BoundaryWord × ℝ) × Ω → (PCode × PCode) × ℝ≥0∞ := fun p => F (p.1, Hc p.2) with hGdef
  have hGm : Measurable G := hF.1.comp (measurable_fst.prodMk (hH.comp measurable_snd))
  have hA : MeasurableSet (stopMatchSet G γ e) := measurableSet_stopMatchSet hGm hγ he
  have h : ∀ᵐ ω₀ ∂P, ω₀ ∈ M → ∀ᵐ ω ∂(condExpKernel P 𝒢 ω₀), (β ω₀, ω) ∈ stopMatchSet G γ e := by
    filter_upwards [hfl] with ω₀ hfl₀ hω₀
    have hd := (hfl₀ hω₀).ae_codeMatch_le hext h13 hκ hF (β ω₀).1 (β ω₀).2 hH hγ he
    filter_upwards [hd] with ω hω
    exact ⟨hω.1, fun n k hnk => hω.2 _ hnk⟩
  filter_upwards [Theorem14.Disintegrate.ae_imp_of_ae_condExpKernel_param h𝒢 hβ hA hM h] with ω hω hωM
  exact stopMatch_of_mem (G := G) (p := (β ω, ω)) (hγc ω) (hω hωM)

end StoppedExtend

end Restart

end InteractingSLE
