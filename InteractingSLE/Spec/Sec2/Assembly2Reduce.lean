/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec2.Assembly2Pathwise
import InteractingSLE.Spec.Sec2.AssemblyUnique
import InteractingSLE.Spec.Sec2.AddMarksUnique

/-!
# Theorem 2.2 assembly: the law of an evolution is determined by its law up to a positive time

Packet PROVE-SEC2-PATCH2. For every ordered force word (admissible entrances included) and every
random time `τ` with `0 < τ ≤ ζ`, the finite-dimensional killed laws of an integrated
`SLE_a(ρ)` evolution are a fixed function of the law of the *observation up to `τ`*
(PROVE-SEC2-GIR2's `observe τ W VL VR B`: driver and marks killed at `τ`, the Brownian motion at
all times, and `τ`):

* `Assembly2.ORel`: pairs (dyadic code of an observation, canonical solution code) that are
  compatible (same driving path, same state at the dyadic times before `τ`, `0 < τ ≤ ζ`, the
  solution separated at `τ` if alive there);
* `Assembly2.injOn_fst_oRel`: the observation determines the solution, by pathwise uniqueness
  after a separated time (`IsIntegratedSLEPath.eq_of_agree_of_separated`); so by Lusin–Souslin the
  set `oLawSet` of observation codes whose solution has its killed state in given sets is Borel;
* `Assembly2.ae_mem_oRel`: almost surely an evolution and its observation are compatible
  (separation at `τ` is `IsIntegratedSLEPath.vL_lt_vR_of_pos`);
* **`IsIntegratedSLEEvolution.measure_killedState_eq_of_map_observe_eq`**: two evolutions of the
  same ordered word whose observations up to positive random times `τ₁`, `τ₂` have the same law
  have the same killed finite-dimensional laws.

With PROVE-SEC2-GIR2's reverse Girsanov theorem (`IsSLEEvolutionUpTo.map_observe_brownian_eq`)
this reduces uniqueness in law for the admissible entrances (marks on both sides at `0`) to the
uniqueness of the law of the local evolution of the seed marks up to the first time another mark
comes close (`Assembly2Entrance`). No measure extension, no conditioning at `τ` and no strong
Markov property is needed: the observation contains the whole Brownian path.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped NNReal ENNReal

namespace InteractingSLE

namespace Sec2

namespace Assembly2

open Assembly

variable {nL nR : ℕ}

/-! ### Dyadic codes of observations -/

/-- The dyadic code of an observation: the time `τ`, the Brownian path, the killed driver and the
killed marks at the dyadic times. -/
abbrev OCode (nL nR : ℕ) : Type := ℝ≥0∞ × PCode × PCode × (Fin nL → PCode) × (Fin nR → PCode)

instance instStandardBorelSpaceOMarks :
    StandardBorelSpace (PCode × PCode × (Fin nL → PCode) × (Fin nR → PCode)) :=
  StandardBorelSpace.prod
instance instStandardBorelSpaceOCode : StandardBorelSpace (OCode nL nR) := StandardBorelSpace.prod
instance instStandardBorelSpaceOXCode : StandardBorelSpace (OCode nL nR × XCode nL nR) :=
  StandardBorelSpace.prod
instance instCountablyGeneratedOMarks1 :
    MeasurableSpace.CountablyGenerated ((Fin nL → PCode) × (Fin nR → PCode)) := inferInstance
instance instCountablyGeneratedOMarks2 :
    MeasurableSpace.CountablyGenerated (PCode × (Fin nL → PCode) × (Fin nR → PCode)) :=
  inferInstance
instance instCountablyGeneratedOMarks3 :
    MeasurableSpace.CountablyGenerated (PCode × PCode × (Fin nL → PCode) × (Fin nR → PCode)) :=
  inferInstance
instance instCountablyGeneratedOCode : MeasurableSpace.CountablyGenerated (OCode nL nR) :=
  inferInstance
instance instMeasurableSingletonClassOMarks1 :
    MeasurableSingletonClass ((Fin nL → PCode) × (Fin nR → PCode)) := inferInstance
instance instMeasurableSingletonClassOMarks2 :
    MeasurableSingletonClass (PCode × (Fin nL → PCode) × (Fin nR → PCode)) := inferInstance
instance instMeasurableSingletonClassOMarks3 :
    MeasurableSingletonClass (PCode × PCode × (Fin nL → PCode) × (Fin nR → PCode)) := inferInstance
instance instMeasurableSingletonClassOCode : MeasurableSingletonClass (OCode nL nR) :=
  inferInstance
instance instCountablySeparatedOCode : MeasurableSpace.CountablySeparated (OCode nL nR) :=
  MeasurableSpace.countablySeparated_of_separatesPoints

/-- The dyadic code of an observation. -/
def ocodeOf (e : ObsSpace nL nR) : OCode nL nR :=
  (e.2, fun n k => (e.1 (dyad n k)).2.2.2, fun n k => (e.1 (dyad n k)).1,
    fun i n k => (e.1 (dyad n k)).2.1 i, fun j n k => (e.1 (dyad n k)).2.2.1 j)

theorem measurable_ocodeOf : Measurable (ocodeOf (nL := nL) (nR := nR)) := by
  have hev : ∀ t : ℝ≥0, Measurable fun e : ObsSpace nL nR => e.1 t := fun t =>
    (measurable_pi_apply t).comp measurable_fst
  refine measurable_snd.prodMk (Measurable.prodMk ?_ (Measurable.prodMk ?_ (Measurable.prodMk ?_ ?_)))
  · exact measurable_pi_iff.2 fun n => measurable_pi_iff.2 fun k =>
      measurable_snd.comp (measurable_snd.comp (measurable_snd.comp (hev _)))
  · exact measurable_pi_iff.2 fun n => measurable_pi_iff.2 fun k => measurable_fst.comp (hev _)
  · exact measurable_pi_iff.2 fun i => measurable_pi_iff.2 fun n => measurable_pi_iff.2 fun k =>
      (measurable_pi_apply i).comp (measurable_fst.comp (measurable_snd.comp (hev _)))
  · exact measurable_pi_iff.2 fun j => measurable_pi_iff.2 fun n => measurable_pi_iff.2 fun k =>
      (measurable_pi_apply j).comp
        (measurable_fst.comp (measurable_snd.comp (measurable_snd.comp (hev _))))

/-! ### The compatibility relation -/

/-- Compatible pairs (observation code, canonical solution code). -/
def ORel (a : ℝ) (xL : Fin nL → ℝ) (xR : Fin nR → ℝ) (ρL : Fin nL → ℝ) (ρR : Fin nR → ℝ) :
    Set (OCode nL nR × XCode nL nR) :=
  {p | p.2 ∈ CRel a xL xR ρL ρR ∧ p.2.1 = p.1.2.1 ∧ 0 < p.1.1 ∧ p.1.1 ≤ cζ p.2 ∧
    (∀ n k, (dyad n k : ℝ≥0∞) < p.1.1 → cw p.2 (dyad n k) = p.1.2.2.1 n k ∧
      (∀ i, cvL p.2 i (dyad n k) = p.1.2.2.2.1 i n k) ∧
      ∀ j, cvR p.2 j (dyad n k) = p.1.2.2.2.2 j n k) ∧
    (p.1.1 < cζ p.2 → ∀ i j, cvL p.2 i p.1.1.toNNReal < cvR p.2 j p.1.1.toNNReal)}

theorem measurableSet_oRel (a : ℝ) (xL : Fin nL → ℝ) (xR : Fin nR → ℝ) (ρL : Fin nL → ℝ)
    (ρR : Fin nR → ℝ) : MeasurableSet (ORel a xL xR ρL ρR) := by
  have hτ : Measurable fun p : OCode nL nR × XCode nL nR => p.1.1 := measurable_fst.fst
  have hζ : Measurable fun p : OCode nL nR × XCode nL nR => cζ p.2 :=
    measurable_cζ.comp measurable_snd
  have hcode : ∀ {f : OCode nL nR × XCode nL nR → PCode}, Measurable f → ∀ n k,
      Measurable fun p => f p n k := fun hf n k => (measurable_code n k).comp hf
  have htn : Measurable fun p : OCode nL nR × XCode nL nR => p.1.1.toNNReal :=
    ENNReal.measurable_toNNReal.comp hτ
  have hdecL : ∀ i, Measurable fun p : OCode nL nR × XCode nL nR => cvL p.2 i p.1.1.toNNReal :=
    fun i => measurable_dec.comp (((measurable_code_vL i).comp measurable_snd).prodMk htn)
  have hdecR : ∀ j, Measurable fun p : OCode nL nR × XCode nL nR => cvR p.2 j p.1.1.toNNReal :=
    fun j => measurable_dec.comp (((measurable_code_vR j).comp measurable_snd).prodMk htn)
  refine measurableSet_setOfPred.2 ?_
  refine Measurable.and ?_ (Measurable.and ?_ (Measurable.and ?_ (Measurable.and ?_
    (Measurable.and ?_ ?_))))
  · exact measurableSet_setOfPred.1
      ((measurableSet_cRel a xL xR ρL ρR).preimage measurable_snd)
  · exact measurableSet_setOfPred.1 (measurableSet_eq_fun measurable_snd.fst
      measurable_fst.snd.fst)
  · exact measurableSet_setOfPred.1 (measurableSet_lt measurable_const hτ)
  · exact measurableSet_setOfPred.1 (measurableSet_le hτ hζ)
  · refine Measurable.forall fun n => Measurable.forall fun k => ?_
    refine (measurableSet_setOfPred.1 (measurableSet_lt measurable_const hτ)).imp ?_
    refine (measurable_eq_real ((measurable_cw_at _).comp measurable_snd)
      (hcode measurable_fst.snd.snd.fst n k)).and ((Measurable.forall fun i =>
        measurable_eq_real ((measurable_cvL_at i _).comp measurable_snd)
          (hcode ((measurable_pi_apply i).comp measurable_fst.snd.snd.snd.fst) n k)).and
      (Measurable.forall fun j => measurable_eq_real ((measurable_cvR_at j _).comp measurable_snd)
          (hcode ((measurable_pi_apply j).comp measurable_fst.snd.snd.snd.snd) n k)))
  · exact (measurableSet_setOfPred.1 (measurableSet_lt hτ hζ)).imp
      (Measurable.forall fun i => Measurable.forall fun j => measurable_lt' (hdecL i) (hdecR j))

variable {a : ℝ} {xL : Fin nL → ℝ} {xR : Fin nR → ℝ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ}

/-- **The observation determines the solution** (pathwise uniqueness after a separated time). -/
theorem injOn_fst_oRel : InjOn Prod.fst (ORel a xL xR ρL ρR) := by
  rintro ⟨o, c⟩ ⟨⟨⟨hg, -, hp⟩, hcan⟩, hb, hτ0, hτζ, hag, hsep⟩ ⟨o', c'⟩
    ⟨⟨⟨hg', -, hp'⟩, hcan'⟩, hb', hτ0', hτζ', hag', -⟩ (hoo : o = o')
  subst hoo
  have hbd : cb c' = cb c := by unfold cb; rw [hb, hb']
  rw [hbd] at hp'
  -- agreement before `τ`
  have hpf := hp.isForcePath
  have hpf' := hp'.isForcePath
  have hsub : ∀ {ξ : ℝ≥0∞}, o.1 ≤ ξ → {t : ℝ≥0 | (t : ℝ≥0∞) < o.1} ⊆ {t | (t : ℝ≥0∞) < ξ} :=
    fun hξ t ht => lt_of_lt_of_le ht hξ
  have hcont : ContinuousOn (fun t => ((cw c t, fun i => cvL c i t, fun j => cvR c j t),
      (cw c' t, fun i => cvL c' i t, fun j => cvR c' j t))) {t : ℝ≥0 | (t : ℝ≥0∞) < o.1} := by
    refine ContinuousOn.prodMk (ContinuousOn.prodMk (hpf.continuousOn_w.mono (hsub hτζ))
      (ContinuousOn.prodMk (continuousOn_pi.2 fun i => (hpf.continuousOn_vL i).mono (hsub hτζ))
        (continuousOn_pi.2 fun j => (hpf.continuousOn_vR j).mono (hsub hτζ))))
      (ContinuousOn.prodMk (hpf'.continuousOn_w.mono (hsub hτζ'))
      (ContinuousOn.prodMk (continuousOn_pi.2 fun i => (hpf'.continuousOn_vL i).mono (hsub hτζ'))
        (continuousOn_pi.2 fun j => (hpf'.continuousOn_vR j).mono (hsub hτζ'))))
  have hagr : ∀ t : ℝ≥0, (t : ℝ≥0∞) < o.1 →
      cw c t = cw c' t ∧ (∀ i, cvL c i t = cvL c' i t) ∧ ∀ j, cvR c j t = cvR c' j t := by
    intro t ht
    have := forall_lt_of_forall_dyad hcont isClosed_diagonal (fun n k hk => by
      obtain ⟨e1, e2, e3⟩ := hag n k hk
      obtain ⟨f1, f2, f3⟩ := hag' n k hk
      show _ = _
      simp only [Prod.mk.injEq]
      exact ⟨e1.trans f1.symm, funext fun i => (e2 i).trans (f2 i).symm,
        funext fun j => (e3 j).trans (f3 j).symm⟩) ht
    simp only [mem_diagonal_iff, Prod.mk.injEq] at this
    obtain ⟨h1, h2, h3⟩ := this
    exact ⟨h1, fun i => congrFun h2 i, fun j => congrFun h3 j⟩
  -- pathwise uniqueness after `τ`
  have key : cζ c = cζ c' ∧ ∀ t : ℝ≥0, (t : ℝ≥0∞) < cζ c →
      cw c t = cw c' t ∧ (∀ i, cvL c i t = cvL c' i t) ∧ ∀ j, cvR c j t = cvR c' j t := by
    rcases eq_top_or_lt_top o.1 with htop | hfin
    · have e1 : cζ c = ⊤ := top_le_iff.1 (htop ▸ hτζ)
      have e2 : cζ c' = ⊤ := top_le_iff.1 (htop ▸ hτζ')
      exact ⟨e1.trans e2.symm, fun t _ => hagr t (by rw [htop]; exact ENNReal.coe_lt_top)⟩
    · set σ := o.1.toNNReal
      have hσ : (σ : ℝ≥0∞) = o.1 := ENNReal.coe_toNNReal hfin.ne
      have hσ0 : 0 < σ := by
        have : (0 : ℝ≥0∞) < σ := by rw [hσ]; exact hτ0
        exact_mod_cast this
      refine hp.eq_of_agree_of_separated hp' hσ0 (hσ ▸ hτζ) (hσ ▸ hτζ')
        (fun t ht => hagr t (by rw [← hσ]; exact_mod_cast ht)) fun hlt => ?_
      exact hsep (by rw [← hσ]; exact hlt)
  refine Prod.ext rfl (code_eq hg hg' hcan hcan' (hb.trans hb'.symm) key.1
    (fun t ht => (key.2 t ht).1) (fun t ht => (key.2 t ht).2.1) fun t ht => (key.2 t ht).2.2)

/-- The Borel set of observation codes whose solution has its killed state in `A`. -/
def oLawSet (a : ℝ) (xL : Fin nL → ℝ) (xR : Fin nR → ℝ) (ρL : Fin nL → ℝ) (ρR : Fin nR → ℝ)
    {n : ℕ} (ts : Fin n → ℝ≥0) (A : Fin n → Set (ℝ × (Fin nL → ℝ) × (Fin nR → ℝ) × ℝ)) :
    Set (OCode nL nR) :=
  Prod.fst '' (ORel a xL xR ρL ρR ∩ Prod.snd ⁻¹' KSet ts A)

/-- **Lusin–Souslin**: `oLawSet` is Borel. -/
theorem measurableSet_oLawSet {n : ℕ} (ts : Fin n → ℝ≥0)
    {A : Fin n → Set (ℝ × (Fin nL → ℝ) × (Fin nR → ℝ) × ℝ)} (hA : ∀ j, MeasurableSet (A j)) :
    MeasurableSet (oLawSet a xL xR ρL ρR ts A) :=
  ((measurableSet_oRel a xL xR ρL ρR).inter ((measurableSet_kSet ts hA).preimage
    measurable_snd)).image_of_measurable_injOn measurable_fst
    (injOn_fst_oRel.mono inter_subset_left)

/-! ### Evolutions and their observations -/

section Evolution

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P]
  {𝓕 : Filtration ℝ≥0 mΩ} {W : ℝ≥0 → Ω → ℝ} {VL : Fin nL → ℝ≥0 → Ω → ℝ}
  {VR : Fin nR → ℝ≥0 → Ω → ℝ} {B : ℝ≥0 → Ω → ℝ} {ζ τ : Ω → ℝ≥0∞}

/-- Killing at a measurable time `τ ≤ ζ` keeps measurability. -/
theorem measurable_killed_of_le {X : ℝ≥0 → Ω → ℝ} (hX : AdaptedBefore 𝓕 ζ X)
    (hτ : Measurable τ) (hτζ : ∀ ω, τ ω ≤ ζ ω) (t : ℝ≥0) : Measurable (Girsanov.killed τ X t) := by
  have hk := measurable_killedAt hX t
  have hlt : MeasurableSet {ω | (t : ℝ≥0∞) < τ ω} := measurableSet_lt measurable_const hτ
  have e : Girsanov.killed τ X t = fun ω => if (t : ℝ≥0∞) < τ ω then
      (if (t : ℝ≥0∞) < ζ ω then X t ω else 0) else 0 := by
    funext ω
    by_cases h : (t : ℝ≥0∞) < τ ω
    · simp [Girsanov.killed, h, lt_of_lt_of_le h (hτζ ω)]
    · simp [Girsanov.killed, h]
  rw [e]
  exact Measurable.ite hlt hk measurable_const

/-- Measurability of the observation at a measurable time `τ ≤ ζ`. -/
theorem measurable_observe_of_le (hW : AdaptedBefore 𝓕 ζ W) (hVL : ∀ i, AdaptedBefore 𝓕 ζ (VL i))
    (hVR : ∀ j, AdaptedBefore 𝓕 ζ (VR j)) (hB : ∀ t, Measurable (B t)) (hτ : Measurable τ)
    (hτζ : ∀ ω, τ ω ≤ ζ ω) : Measurable (Sec2.observe τ W VL VR B) := by
  refine Measurable.prodMk (measurable_pi_iff.2 fun t => ?_) hτ
  exact (measurable_killed_of_le hW hτ hτζ t).prodMk
    ((measurable_pi_iff.2 fun i => measurable_killed_of_le (hVL i) hτ hτζ t).prodMk
      ((measurable_pi_iff.2 fun j => measurable_killed_of_le (hVR j) hτ hτζ t).prodMk (hB t)))

/-- **Almost surely, an evolution of an ordered word and its observation at a positive time are
compatible.** -/
theorem ae_mem_oRel (ha : 0 < a) (hF : IsOrderedForceWord xL xR)
    (h : IsIntegratedSLEEvolution a xL xR ρL ρR P 𝓕 W VL VR B ζ) {B' : ℝ≥0 → Ω → ℝ}
    (hB'c : ∀ ω, Continuous (B' · ω)) (hae : ∀ᵐ ω ∂P, ∀ t, B' t ω = B t ω)
    (hτ0 : ∀ᵐ ω ∂P, 0 < τ ω) (hτζ : ∀ ω, τ ω ≤ ζ ω) :
    ∀ᵐ ω ∂P, (ocodeOf (Sec2.observe τ W VL VR B ω), codeOf xL xR B' W VL VR ζ ω) ∈
      ORel a xL xR ρL ρR ∧
      ∀ t : ℝ≥0, (t : ℝ≥0∞) < ζ ω →
        cw (codeOf xL xR B' W VL VR ζ ω) t = W t ω ∧
        (∀ i, cvL (codeOf xL xR B' W VL VR ζ ω) i t = VL i t ω) ∧
        (∀ j, cvR (codeOf xL xR B' W VL VR ζ ω) j t = VR j t ω) ∧
        cb (codeOf xL xR B' W VL VR ζ ω) t = B t ω := by
  filter_upwards [ae_codeOf_mem ha h hB'c hae, hae, hτ0, h.2.2.2.2] with ω ⟨hmem, hdec⟩ hB hτ hpath
  refine ⟨⟨hmem, ?_, hτ, hτζ ω, fun n k hk => ?_, fun hlt i j => ?_⟩, hdec⟩
  · funext n k
    show B' (dyad n k) ω = ((Sec2.observe τ W VL VR B ω).1 (dyad n k)).2.2.2
    rw [hB]; rfl
  · have hkζ : (dyad n k : ℝ≥0∞) < ζ ω := lt_of_lt_of_le hk (hτζ ω)
    obtain ⟨e1, e2, e3, -⟩ := hdec _ hkζ
    refine ⟨?_, fun i => ?_, fun j => ?_⟩
    · rw [e1]; exact (Girsanov.killed_of_lt (ζ := τ) (X := W) (ω := ω) hk).symm
    · rw [e2 i]; exact (Girsanov.killed_of_lt (ζ := τ) (X := VL i) (ω := ω) hk).symm
    · rw [e3 j]; exact (Girsanov.killed_of_lt (ζ := τ) (X := VR j) (ω := ω) hk).symm
  · have hfin : τ ω ≠ ⊤ := (lt_of_lt_of_le hlt le_top).ne
    have hσ : ((τ ω).toNNReal : ℝ≥0∞) = τ ω := ENNReal.coe_toNNReal hfin
    have hlt' : (((τ ω).toNNReal : ℝ≥0) : ℝ≥0∞) < ζ ω := by rw [hσ]; exact hlt
    have hσ0 : 0 < (τ ω).toNNReal := by
      have : (0 : ℝ≥0∞) < (τ ω).toNNReal := by rw [hσ]; exact hτ
      exact_mod_cast this
    obtain ⟨-, e2, e3, -⟩ := hdec _ hlt'
    show cvL (codeOf xL xR B' W VL VR ζ ω) i (τ ω).toNNReal <
      cvR (codeOf xL xR B' W VL VR ζ ω) j (τ ω).toNNReal
    rw [e2 i, e3 j]
    exact hpath.vL_lt_vR_of_pos hF hσ0 hlt' i j

/-- **The killed-state probabilities of an evolution of an ordered word are a fixed function of
the law of its observation up to a positive time `τ ≤ ζ`.** -/
theorem measure_killedState_eq_map_observe (ha : 0 < a) (hF : IsOrderedForceWord xL xR)
    (h : IsIntegratedSLEEvolution a xL xR ρL ρR P 𝓕 W VL VR B ζ) (hτ : Measurable τ)
    (hτ0 : ∀ᵐ ω ∂P, 0 < τ ω) (hτζ : ∀ ω, τ ω ≤ ζ ω) {n : ℕ} (ts : Fin n → ℝ≥0)
    (A : Fin n → Set (ℝ × (Fin nL → ℝ) × (Fin nR → ℝ) × ℝ)) (hA : ∀ j, MeasurableSet (A j)) :
    P {ω | ∀ j, (ts j : ℝ≥0∞) < ζ ω ∧
        (W (ts j) ω, (fun i => VL i (ts j) ω), (fun i => VR i (ts j) ω), B (ts j) ω) ∈ A j} =
      (P.map (Sec2.observe τ W VL VR B)) (ocodeOf ⁻¹' oLawSet a xL xR ρL ρR ts A) := by
  obtain ⟨B', -, hc, -, -, hae⟩ := QuantumZipper.RS.exists_good_version0 h.1.1
  have hBm : ∀ t, Measurable (B t) := fun t => (h.1.2.1 t).mono (𝓕.le t) le_rfl
  have hobs := measurable_observe_of_le h.2.1 h.2.2.1 h.2.2.2.1 hBm hτ hτζ
  rw [Measure.map_apply hobs ((measurableSet_oLawSet ts hA).preimage measurable_ocodeOf)]
  refine measure_congr ?_
  filter_upwards [ae_mem_oRel ha hF h hc hae hτ0 hτζ] with ω ⟨hrel, hdec⟩
  set x := codeOf xL xR B' W VL VR ζ ω with hx
  have hK : (∀ j, (ts j : ℝ≥0∞) < ζ ω ∧
      (W (ts j) ω, (fun i => VL i (ts j) ω), (fun i => VR i (ts j) ω), B (ts j) ω) ∈ A j) ↔
      x ∈ KSet ts A := by
    refine forall_congr' fun j => ?_
    refine ⟨fun ⟨hlt, hmemA⟩ => ⟨hlt, ?_⟩, fun ⟨hlt, hmemA⟩ => ⟨hlt, ?_⟩⟩
    · obtain ⟨e1, e2, e3, e4⟩ := hdec (ts j) hlt
      rw [e1, funext e2, funext e3, e4]; exact hmemA
    · obtain ⟨e1, e2, e3, e4⟩ := hdec (ts j) hlt
      rw [e1, funext e2, funext e3, e4] at hmemA; exact hmemA
  refine propext ?_
  show (∀ j, (ts j : ℝ≥0∞) < ζ ω ∧
      (W (ts j) ω, (fun i => VL i (ts j) ω), (fun i => VR i (ts j) ω), B (ts j) ω) ∈ A j) ↔
    ocodeOf (Sec2.observe τ W VL VR B ω) ∈ oLawSet a xL xR ρL ρR ts A
  rw [hK]
  constructor
  · intro hk
    exact ⟨_, ⟨hrel, hk⟩, rfl⟩
  · rintro ⟨y, ⟨hy, hyK⟩, hy1⟩
    have : y = (ocodeOf (Sec2.observe τ W VL VR B ω), x) := injOn_fst_oRel hy hrel hy1
    rw [this] at hyK; exact hyK

end Evolution

end Assembly2

end Sec2

open Sec2.Assembly2

/-- **Theorem 2.2, uniqueness in law, reduced to a positive random time.** Two integrated
`SLE_a(ρ)` evolutions of the same ordered force word whose observations up to positive random
times `τ_k ≤ ζ_k` (driver and marks killed at `τ_k`, the Brownian motion, `τ_k`) have the same law
have the same killed finite-dimensional laws. -/
theorem IsIntegratedSLEEvolution.measure_killedState_eq_of_map_observe_eq {a : ℝ} (ha : 0 < a)
    {nL nR : ℕ} {xL : Fin nL → ℝ} {xR : Fin nR → ℝ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ}
    (hF : IsOrderedForceWord xL xR)
    {Ω₁ : Type*} {m₁ : MeasurableSpace Ω₁} {P₁ : Measure Ω₁} [IsProbabilityMeasure P₁]
    {𝓕₁ : Filtration ℝ≥0 m₁} {W₁ : ℝ≥0 → Ω₁ → ℝ} {VL₁ : Fin nL → ℝ≥0 → Ω₁ → ℝ}
    {VR₁ : Fin nR → ℝ≥0 → Ω₁ → ℝ} {B₁ : ℝ≥0 → Ω₁ → ℝ} {ζ₁ : Ω₁ → ℝ≥0∞}
    (h₁ : IsIntegratedSLEEvolution a xL xR ρL ρR P₁ 𝓕₁ W₁ VL₁ VR₁ B₁ ζ₁)
    {Ω₂ : Type*} {m₂ : MeasurableSpace Ω₂} {P₂ : Measure Ω₂} [IsProbabilityMeasure P₂]
    {𝓕₂ : Filtration ℝ≥0 m₂} {W₂ : ℝ≥0 → Ω₂ → ℝ} {VL₂ : Fin nL → ℝ≥0 → Ω₂ → ℝ}
    {VR₂ : Fin nR → ℝ≥0 → Ω₂ → ℝ} {B₂ : ℝ≥0 → Ω₂ → ℝ} {ζ₂ : Ω₂ → ℝ≥0∞}
    (h₂ : IsIntegratedSLEEvolution a xL xR ρL ρR P₂ 𝓕₂ W₂ VL₂ VR₂ B₂ ζ₂)
    {τ₁ : Ω₁ → ℝ≥0∞} {τ₂ : Ω₂ → ℝ≥0∞} (hτ₁ : Measurable τ₁) (hτ₂ : Measurable τ₂)
    (hτ₁0 : ∀ᵐ ω ∂P₁, 0 < τ₁ ω) (hτ₂0 : ∀ᵐ ω ∂P₂, 0 < τ₂ ω) (hτ₁ζ : ∀ ω, τ₁ ω ≤ ζ₁ ω)
    (hτ₂ζ : ∀ ω, τ₂ ω ≤ ζ₂ ω)
    (hlaw : P₁.map (Sec2.observe τ₁ W₁ VL₁ VR₁ B₁) = P₂.map (Sec2.observe τ₂ W₂ VL₂ VR₂ B₂))
    (n : ℕ) (ts : Fin n → ℝ≥0) (A : Fin n → Set (ℝ × (Fin nL → ℝ) × (Fin nR → ℝ) × ℝ))
    (hA : ∀ j, MeasurableSet (A j)) :
    P₁ {ω | ∀ j, (ts j : ℝ≥0∞) < ζ₁ ω ∧
        (W₁ (ts j) ω, (fun i => VL₁ i (ts j) ω), (fun i => VR₁ i (ts j) ω), B₁ (ts j) ω) ∈ A j} =
      P₂ {ω | ∀ j, (ts j : ℝ≥0∞) < ζ₂ ω ∧
        (W₂ (ts j) ω, (fun i => VL₂ i (ts j) ω), (fun i => VR₂ i (ts j) ω), B₂ (ts j) ω) ∈ A j} := by
  rw [measure_killedState_eq_map_observe ha hF h₁ hτ₁ hτ₁0 hτ₁ζ ts A hA,
    measure_killedState_eq_map_observe ha hF h₂ hτ₂ hτ₂0 hτ₂ζ ts A hA, hlaw]

end InteractingSLE
