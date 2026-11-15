/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.Q3StopCanon

/-!
# GB6's relative chain by word type, read on the canonical space

Packet PROVE-Q3-REL4 (step (D)). The stopped K2 runs with fixed numbers of marks and fixed weights, while GB6's
conditional word `β(r) = gb6WordOfRec κ θ c r` depends on the record. On the record event of one **word type**
(numbers of left and right marks of the flow-line word of `β(r)` and its padded weights) the word has fixed weights,
and its mark positions are a measurable function of the record (`typedXL`, `typedXR`; zero off the type, so that they
are ordered for every record, as the K2 asks).

* `WordType`, `wordType`, `typedXL`, `typedXR`, `typedRhoL`, `typedRhoR`, **`isFlowType_typed`**;
* **`HasRelSafe`**: K2's inputs (S), (L), the threshold bound and integrability of the chart field, for the decoded
  relative driver with the flowed marks of the typed word, under a law on the canonical space conditioned on a record
  event of one type — Astra's follow-up 3, Q3 (Q3.3) at deterministic relative times and relative locality (§3.5),
  in the canonical filtration (Q3.2);
* `ae_cond_of_ae_comp`, `ae_comp_of_ae_cond`: almost sure statements between a probability space and the conditioned
  image law;
* **`ae_isStopDrvMatch_of_hasRelSafe`**: on any probability space with a record, a chart field and a measurable
  version `(R, V)` of a relative driver through a stop given by a path rule and announced by finite path rules,
  `HasRelSafe` for the image law gives, almost surely on the record event of the type, the stopped driver match with
  the canonical driver code of `(β(record), field)` (the canonical-space theorem `ae_isStopDrvMatch_canon`).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Filter MeasureTheory ProbabilityTheory Topology
open scoped NNReal ENNReal
open LQGMetric (TestOn DistOn)

namespace InteractingSLE.Supp8.Q3Stop

open Restart Restart.DomainMarkov Restart.DomainMarkov.K2 Restart.FCDet Exist.Staged Exist.StagedLaw Supp8.GB6.RelDrv
  Supp8.GB6.HullId Sec7.PocketTraversal

/-! ### Word types -/

/-- **The type of a word**: the numbers of left and right marks of its flow-line word at `0` and the padded weights
(angle `0`, parameter `κ`). -/
abbrev WordType : Type := ℕ × ℕ × (ℕ → ℝ) × (ℕ → ℝ)

/-- The type of a word. -/
def wordType (κ : ℝ) (c : BoundaryWord) : WordType :=
  (flowLineNL c.fn c.jumps 0, flowLineNR c.fn c.jumps 0, (padFL κ 0 c.fn c.jumps).2.1, (padFL κ 0 c.fn c.jumps).2.2)

theorem measurable_wordType (κ : ℝ) : Measurable (wordType κ) :=
  wordMeasStatement.1.prodMk (wordMeasStatement.2.1.prodMk
    (((measurable_fst.comp measurable_snd).comp (wordMeasStatement.2.2 κ 0)).prodMk
      ((measurable_snd.comp measurable_snd).comp (wordMeasStatement.2.2 κ 0))))

open Classical in
/-- The left mark positions of a word of type `w` (zero if the word is not of type `w`). -/
def typedXL (κ : ℝ) (w : WordType) (c : BoundaryWord) : Fin w.1 → ℝ :=
  if wordType κ c = w then fun i => (padFL 0 0 c.fn c.jumps).1.1 i else 0

open Classical in
/-- The right mark positions of a word of type `w` (zero if the word is not of type `w`). -/
def typedXR (κ : ℝ) (w : WordType) (c : BoundaryWord) : Fin w.2.1 → ℝ :=
  if wordType κ c = w then fun j => (padFL 0 0 c.fn c.jumps).1.2 j else 0

/-- The left weights of the type `w`. -/
def typedRhoL (w : WordType) : Fin w.1 → ℝ := fun i => w.2.2.1 i

/-- The right weights of the type `w`. -/
def typedRhoR (w : WordType) : Fin w.2.1 → ℝ := fun j => w.2.2.2 j

theorem typedXL_nonpos (κ : ℝ) (w : WordType) (c : BoundaryWord) (i : Fin w.1) : typedXL κ w c i ≤ 0 := by
  by_cases h : wordType κ c = w
  · subst h
    simp only [typedXL, ↓reduceIte]
    exact (padFL_fst_fst_fin c.fn c.jumps i).symm ▸ Theorem14.GW3Word.flowLineXL_nonpos _ _ i
  · simp only [typedXL, h, ↓reduceIte, Pi.zero_apply, le_refl]

theorem typedXR_nonneg (κ : ℝ) (w : WordType) (c : BoundaryWord) (j : Fin w.2.1) : 0 ≤ typedXR κ w c j := by
  by_cases h : wordType κ c = w
  · subst h
    simp only [typedXR, ↓reduceIte]
    exact (padFL_fst_snd_fin c.fn c.jumps j).symm ▸ Theorem14.GW3Word.flowLineXR_nonneg _ _ j
  · simp only [typedXR, h, ↓reduceIte, Pi.zero_apply, le_refl]

theorem antitone_typedXL (κ : ℝ) (w : WordType) (c : BoundaryWord) : Antitone (typedXL κ w c) := by
  by_cases h : wordType κ c = w
  · subst h
    have e : typedXL κ (wordType κ c) c = flowLineXL c.fn c.jumps 0 := by
      funext i
      simp only [typedXL, ↓reduceIte]
      exact padFL_fst_fst_fin c.fn c.jumps i
    rw [e]
    exact (Theorem15.isOrderedForceWord_flowLine c.fn c.jumps 0).1
  · simp only [typedXL, h, ↓reduceIte]
    exact fun _ _ _ => le_rfl

theorem monotone_typedXR (κ : ℝ) (w : WordType) (c : BoundaryWord) : Monotone (typedXR κ w c) := by
  by_cases h : wordType κ c = w
  · subst h
    have e : typedXR κ (wordType κ c) c = flowLineXR c.fn c.jumps 0 := by
      funext j
      simp only [typedXR, ↓reduceIte]
      exact padFL_fst_snd_fin c.fn c.jumps j
    rw [e]
    exact (Theorem15.isOrderedForceWord_flowLine c.fn c.jumps 0).2.2.1
  · simp only [typedXR, h, ↓reduceIte]
    exact fun _ _ _ => le_rfl

open Classical in
theorem measurable_typedXL (κ : ℝ) (w : WordType) : Measurable (typedXL κ w) := by
  have hS : MeasurableSet {c : BoundaryWord | wordType κ c = w} :=
    measurable_wordType κ (measurableSet_singleton w)
  have hp : Measurable fun c : BoundaryWord => (padFL 0 0 c.fn c.jumps).1.1 :=
    (measurable_fst.comp measurable_fst).comp (wordMeasStatement.2.2 0 0)
  refine measurable_pi_iff.2 fun i => ?_
  have e : (fun c : BoundaryWord => typedXL κ w c i) =
      fun c => if wordType κ c = w then (padFL 0 0 c.fn c.jumps).1.1 i else 0 := by
    funext c
    by_cases h : wordType κ c = w <;> simp only [typedXL, h, ↓reduceIte, Pi.zero_apply]
  rw [e]
  exact Measurable.ite hS ((measurable_pi_apply (i : ℕ)).comp hp) measurable_const

open Classical in
theorem measurable_typedXR (κ : ℝ) (w : WordType) : Measurable (typedXR κ w) := by
  have hS : MeasurableSet {c : BoundaryWord | wordType κ c = w} :=
    measurable_wordType κ (measurableSet_singleton w)
  have hp : Measurable fun c : BoundaryWord => (padFL 0 0 c.fn c.jumps).1.2 :=
    (measurable_snd.comp measurable_fst).comp (wordMeasStatement.2.2 0 0)
  refine measurable_pi_iff.2 fun j => ?_
  have e : (fun c : BoundaryWord => typedXR κ w c j) =
      fun c => if wordType κ c = w then (padFL 0 0 c.fn c.jumps).1.2 j else 0 := by
    funext c
    by_cases h : wordType κ c = w <;> simp only [typedXR, h, ↓reduceIte, Pi.zero_apply]
  rw [e]
  exact Measurable.ite hS ((measurable_pi_apply (j : ℕ)).comp hp) measurable_const

/-- **A word of type `w` is of flow-line type at angle `0`** with the typed positions and weights. -/
theorem isFlowType_typed {κ : ℝ} {w : WordType} {c : BoundaryWord} (h : wordType κ c = w) :
    IsFlowType κ 0 c (typedXL κ w c) (typedXR κ w c) (typedRhoL w) (typedRhoR w) := by
  subst h
  refine ⟨rfl, rfl, funext fun i => ?_, funext fun j => ?_, funext fun i => ?_, funext fun j => ?_⟩
  · simp only [typedXL, ↓reduceIte]
    exact padFL_fst_fst_fin c.fn c.jumps i
  · simp only [typedXR, ↓reduceIte]
    exact padFL_fst_snd_fin c.fn c.jumps j
  · simp only [Fin.cast_eq_self, typedRhoL, wordType]
    exact padFL_snd_fst_fin κ 0 c.fn c.jumps i
  · simp only [Fin.cast_eq_self, typedRhoR, wordType]
    exact padFL_snd_snd_fin κ 0 c.fn c.jumps j

/-! ### The relative safe law of one type -/

/-- The record event `E` of word type `w`, on the canonical space. -/
def typeEvent (k : ℝ) (w : WordType) (β : RecData → BoundaryWord) (E : Set RecData) : Set CanonSpace :=
  Prod.fst ⁻¹' (E ∩ {r | wordType k (β r) = w})

theorem measurableSet_typeEvent {k : ℝ} {w : WordType} {β : RecData → BoundaryWord} (hβ : Measurable β)
    {E : Set RecData} (hE : MeasurableSet E) : MeasurableSet (typeEvent k w β E) :=
  measurable_fst (hE.inter ((measurable_wordType k).comp hβ (measurableSet_singleton w)))

/-- **K2's inputs for GB6's relative chain of word type `w`** (Astra's follow-up 3, Q3: (Q3.3) at deterministic
relative times, relative locality (§3.5), in the filtration (Q3.2) of the record and the relative path), on the
canonical space under the law `μ` conditioned on the record event `E` of type `w`: (S) and (L) for the decoded
relative driver with the flowed marks of the typed word and lifetime the stop, the stop is before the continuation
threshold, and the chart field is integrable. -/
def HasRelSafe (k : ℝ) (w : WordType) (β : RecData → BoundaryWord) (E : Set RecData) (μ : Measure CanonSpace) :
    Prop :=
  HasSafeLaw k (typedRhoL w) (typedRhoR w) (μ[|typeEvent k w β E]) canonFilt univ canonStp canonDrv
      (geomLW canonDrv fun y => typedXL k w (β y.1)) (geomRW canonDrv fun y => typedXR k w (β y.1)) canonFld ∧
    HasSafeMembers (μ[|typeEvent k w β E]) canonFilt univ canonStp canonDrv canonFld ∧
    (∀ᵐ y ∂(μ[|typeEvent k w β E]), canonStp y ≤ thr (typedRhoL w) (typedRhoR w) canonDrv
      (fun y => typedXL k w (β y.1)) (fun y => typedXR k w (β y.1)) y) ∧
    ∀ φ : TestOn upperHalfPlaneOpens, Integrable (fun y => canonFld y φ) (μ[|typeEvent k w β E])

/-! ### Almost sure statements between a space and the conditioned image law -/

section Transfer

variable {Ω Y : Type*} [MeasurableSpace Ω] [MeasurableSpace Y] {P : Measure Ω} {Φ : Ω → Y} {S : Set Y}
  {p : Y → Prop}

theorem measurableSet_imp (hS : MeasurableSet S) (hp : MeasurableSet {y | p y}) :
    MeasurableSet {y | y ∈ S → p y} := by
  have e : {y | y ∈ S → p y} = Sᶜ ∪ {y | p y} := by
    ext y
    simp only [mem_ofPred_eq, mem_union, mem_compl_iff]
    tauto
  rw [e]
  exact hS.compl.union hp

/-- From the space to the conditioned image law. -/
theorem ae_cond_of_ae_comp (hΦ : Measurable Φ) (hS : MeasurableSet S) (hp : MeasurableSet {y | p y})
    (h : ∀ᵐ ω ∂P, Φ ω ∈ S → p (Φ ω)) : ∀ᵐ y ∂(P.map Φ)[|S], p y := by
  have h1 : ∀ᵐ y ∂(P.map Φ), y ∈ S → p y :=
    (ae_map_iff hΦ.aemeasurable (measurableSet_imp hS hp)).2 h
  filter_upwards [ae_cond_mem (μ := P.map Φ) hS, cond_absolutelyContinuous.ae_le h1] with y hyS hy using hy hyS

/-- From the conditioned image law back to the space. -/
theorem ae_comp_of_ae_cond [IsFiniteMeasure P] (hΦ : Measurable Φ) (hS : MeasurableSet S)
    (hp : MeasurableSet {y | p y}) (h : ∀ᵐ y ∂(P.map Φ)[|S], p y) : ∀ᵐ ω ∂P, Φ ω ∈ S → p (Φ ω) := by
  refine (ae_map_iff hΦ.aemeasurable (measurableSet_imp hS hp)).1 ?_
  have hc : (P.map Φ)[|S] {y | ¬p y} = 0 := ae_iff.1 h
  rw [cond_apply hS] at hc
  have h2 : (P.map Φ) (S ∩ {y | ¬p y}) = 0 := by
    rcases mul_eq_zero.1 hc with h0 | h0
    · exact absurd h0 (ENNReal.inv_ne_zero.2 (measure_ne_top _ _))
    · exact h0
  rw [ae_iff]
  refine measure_mono_null (fun y hy => ?_) h2
  simp only [mem_ofPred_eq, not_imp] at hy
  exact ⟨hy.1, hy.2⟩

end Transfer

/-! ### The stopped driver match on a probability space, by type -/

/-- **The relative stopped driver match of one word type, from the relative safe law of the image law.** On a
probability space with a measurable record, a measurable chart field and a measurable version `(R, V)` of a relative
driver (continuous from `0`) through a stop: if the image law of `(record, relVar Hc R V)` has `HasRelSafe` for the
record event `E` and type `w`, the stop is positive on `E`, given by a measurable path rule `ρ`, and announced on `E`
by measurable finite path rules `ρs k` (nondecreasing, below the stop, with supremum the stop), then almost surely on
the record event of type `w` the relative driver matches the canonical driver code of `(β(record), Hc)` at every
dyadic time before the stop. -/
theorem ae_isStopDrvMatch_of_hasRelSafe {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {k : ℝ} (hk : 0 < k) {Fd : BoundaryWord × DistOn upperHalfPlaneOpens → Sec2.Assembly.PCode × ℝ≥0∞}
    (hFd : IsCanonicalDriverCode k 0 Fd) {β : RecData → BoundaryWord} (hβ : Measurable β) {E : Set RecData}
    (hE : MeasurableSet E) (w : WordType) {rec : Ω → RecData} (hrec : Measurable rec)
    {Hc : Ω → DistOn upperHalfPlaneOpens} (hHc : Measurable Hc) {R : ℝ≥0 → Ω → ℝ} (hRm : ∀ t, Measurable (R t))
    (hRc : ∀ ω, Continuous fun t => R t ω) (hR0 : ∀ ω, R 0 ω = 0) {V : Ω → ℝ≥0∞} (hVm : Measurable V)
    (hS : HasRelSafe k w β E (P.map fun ω => (rec ω, relVar Hc R V ω)))
    (hV0 : ∀ᵐ ω ∂P, rec ω ∈ E → 0 < V ω)
    {ρ : RecData × (ℝ≥0 → ℝ) → ℝ≥0∞} (hρm : Measurable ρ) (hρ : IsPathRule ρ)
    (hVρ : ∀ᵐ ω ∂P, V ω = ρ (rec ω, fun u => R u ω))
    {ρs : ℕ → RecData × (ℝ≥0 → ℝ) → ℝ≥0∞} (hρsm : ∀ n, Measurable (ρs n)) (hρs : ∀ n, IsPathRule (ρs n))
    (hρsfin : ∀ n x, ρs n x ≠ ⊤) (hρsmono : ∀ x, Monotone fun n => ρs n x)
    (hρslt : ∀ᵐ ω ∂P, rec ω ∈ E → ∀ n, ρs n (rec ω, fun u => R u ω) < V ω)
    (hρssup : ∀ᵐ ω ∂P, rec ω ∈ E → ⨆ n, ρs n (rec ω, fun u => R u ω) = V ω) :
    ∀ᵐ ω ∂P, rec ω ∈ E → wordType k (β (rec ω)) = w →
      IsStopDrvMatch (Fd (β (rec ω), Hc ω)) (fun t => R t ω) (V ω) := by
  set Φ : Ω → CanonSpace := fun ω => (rec ω, relVar Hc R V ω) with hΦdef
  have hΦ : Measurable Φ := hrec.prodMk (measurable_relVar hHc hRm hVm)
  set S : Set CanonSpace := typeEvent k w β E with hSdef
  have hSm : MeasurableSet S := measurableSet_typeEvent hβ hE
  have hpath : ∀ ω, (fun t => canonDrv t (Φ ω)) = fun t => R t ω := fun ω =>
    funext fun t => relDrv_relVar (hRc ω) (hR0 ω) t
  have hpm : Measurable fun y : CanonSpace => (y.1, fun t => canonDrv t y) :=
    measurable_fst.prodMk (measurable_pi_iff.2 measurable_canonDrv)
  set M : Set CanonSpace :=
    {y | IsStopDrvMatch (Fd (β y.1, canonFld y)) (fun t => canonDrv t y) (canonStp y)} with hMdef
  have hMm : MeasurableSet M :=
    measurableSet_isStopDrvMatch (G := fun y : CanonSpace => Fd (β y.1, canonFld y))
      (hFd.1.comp ((hβ.comp measurable_fst).prodMk measurable_canonFld)) measurable_canonDrv measurable_canonStp
  set μ : Measure CanonSpace := P.map Φ with hμ
  by_cases h0 : μ S = 0
  · have hP0 : P (Φ ⁻¹' S) = 0 := by rw [← Measure.map_apply hΦ hSm]; exact h0
    filter_upwards [measure_eq_zero_iff_ae_notMem.1 hP0] with ω hω h1 h2 using absurd ⟨h1, h2⟩ hω
  have : IsProbabilityMeasure (μ[|S]) := cond_isProbabilityMeasure h0
  obtain ⟨hlaw, hmem, hthr, hint⟩ := hS
  have hV0' : ∀ᵐ y ∂μ[|S], 0 < canonStp y :=
    ae_cond_of_ae_comp hΦ hSm (measurableSet_lt measurable_const measurable_canonStp) (by
      filter_upwards [hV0] with ω hω hS using hω hS.1)
  have hVρ' : ∀ᵐ y ∂μ[|S], canonStp y = ρ (y.1, fun t => canonDrv t y) :=
    ae_cond_of_ae_comp hΦ hSm (measurableSet_eq_fun measurable_canonStp (hρm.comp hpm)) (by
      filter_upwards [hVρ] with ω hω _
      change V ω = ρ (rec ω, fun t => canonDrv t (Φ ω))
      rw [hpath]
      exact hω)
  have hρslt' : ∀ᵐ y ∂μ[|S], ∀ n, ρs n (y.1, fun t => canonDrv t y) < canonStp y :=
    ae_cond_of_ae_comp hΦ hSm (by
      simp only [ofPred_forall]
      exact MeasurableSet.iInter fun n => measurableSet_lt ((hρsm n).comp hpm) measurable_canonStp) (by
      filter_upwards [hρslt] with ω hω hS n
      change ρs n (rec ω, fun t => canonDrv t (Φ ω)) < V ω
      rw [hpath]
      exact hω hS.1 n)
  have hρssup' : ∀ᵐ y ∂μ[|S], ⨆ n, ρs n (y.1, fun t => canonDrv t y) = canonStp y :=
    ae_cond_of_ae_comp hΦ hSm (measurableSet_eq_fun (Measurable.iSup fun n => (hρsm n).comp hpm)
      measurable_canonStp) (by
      filter_upwards [hρssup] with ω hω hS
      change ⨆ n, ρs n (rec ω, fun t => canonDrv t (Φ ω)) = V ω
      rw [hpath]
      exact hω hS.1)
  have hρslim' : ∀ᵐ y ∂μ[|S], Tendsto (fun n => ρs n (y.1, fun t => canonDrv t y)) atTop (𝓝 (canonStp y)) := by
    filter_upwards [hρssup'] with y hy
    rw [← hy]
    exact tendsto_atTop_iSup fun a b hab => hρsmono _ hab
  have htype : ∀ᵐ y ∂μ[|S],
      IsFlowType k 0 (β y.1) (typedXL k w (β y.1)) (typedXR k w (β y.1)) (typedRhoL w) (typedRhoR w) := by
    filter_upwards [ae_cond_mem (μ := μ) hSm] with y hy using isFlowType_typed hy.2
  have hcore := ae_isStopDrvMatch_canon (Q := μ[|S]) hk hFd hβ (xL := fun r => typedXL k w (β r))
    (xR := fun r => typedXR k w (β r)) ((measurable_typedXL k w).comp hβ) ((measurable_typedXR k w).comp hβ)
    (fun r i => typedXL_nonpos k w _ i) (fun r j => typedXR_nonneg k w _ j) (fun r => antitone_typedXL k w _)
    (fun r => monotone_typedXR k w _) htype hint hV0' hthr hρm hρ hVρ' hρsm hρs hρsfin hρsmono hρslt' hρslim'
    hlaw hmem
  have hback := ae_comp_of_ae_cond hΦ hSm hMm hcore
  filter_upwards [hback] with ω hω h1 h2
  have h3 := hω ⟨h1, h2⟩
  change IsStopDrvMatch (Fd (β (rec ω), Hc ω)) (fun t => canonDrv t (Φ ω)) (V ω) at h3
  rw [hpath] at h3
  exact h3

end InteractingSLE.Supp8.Q3Stop
