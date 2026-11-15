/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec2.Assembly2Conv
import InteractingSLE.Spec.Sec2.Assembly2Close
import InteractingSLE.Spec.Sec2.RestartMarkov
import Mathlib.Probability.Process.FiniteDimensionalLaws

/-!
# Theorem 2.2, existence: the maximal local solution is a solution (strong Markov restart)

Packet PROVE-SEC2-PATCH3. Let `B` be a Brownian motion of a right-continuous filtration `𝓕` with
every path continuous, and `s` a separated, ordered, non-threshold word. The maximal local solution
from `s` driven by the path of `B` (`codeProc`, horizon `lifeProc`; PROVE-SEC2-PATCH3's
`Assembly2Max`) is an integrated `SLE_a(ρ)` evolution (`isIntegratedSLEEvolution_codeProc`),
provided every such word has local solutions with a positive horizon along almost every path
(`HasPosLife`, proved by Girsanov in `Assembly2Girs`):

* *locality*: the maximal horizon and the maximal solution before it only see the path up to any
  later time (`Assembly2Max`), so `{lifeProc < u}` and every event of the maximal solution before
  `u` belong to `𝓕 u` (`measurable_of_local`): `lifeProc` is a stopping time and the solution is
  adapted;
* *restart*: if the state converged at a finite horizon to a non-threshold state, the strong Markov
  property at the horizon (`ae_mem_of_strongMarkov`) and `HasPosLife` at the restart word would give
  a local solution after it, and the concatenation (`IsSLEPathUpTo.concat_of_tendsto`) a local
  solution beyond the maximal horizon, which is impossible. So almost surely the maximal solution
  satisfies the maximality clauses of Definition 2.1 (`ae_isIntegratedSLEPath_codeProc`).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped NNReal ENNReal

namespace InteractingSLE

namespace Sec2

namespace Assembly2

open Assembly QuantumZipper.StrongMarkov

/-! ### Path laws and the strong Markov property with a parameter -/

/-- The law of the path of a pre-Brownian motion does not depend on the probability space. -/
theorem map_path_eq_map_path {Ω₁ Ω₂ : Type*} {m₁ : MeasurableSpace Ω₁} {m₂ : MeasurableSpace Ω₂}
    {P₁ : Measure Ω₁} {P₂ : Measure Ω₂} {B₁ : ℝ≥0 → Ω₁ → ℝ} {B₂ : ℝ≥0 → Ω₂ → ℝ}
    (h₁ : IsPreBrownianReal B₁ P₁) (h₂ : IsPreBrownianReal B₂ P₂)
    (hm₁ : Measurable fun ω (s : ℝ≥0) => B₁ s ω) (hm₂ : Measurable fun ω (s : ℝ≥0) => B₂ s ω) :
    P₁.map (fun ω s => B₁ s ω) = P₂.map (fun ω s => B₂ s ω) := by
  have k₁ := isProjectiveLimit_map (P := P₁) (X := B₁) hm₁.aemeasurable
  have k₂ := isProjectiveLimit_map (P := P₂) (X := B₂) hm₂.aemeasurable
  have e₁ : (fun I : Finset ℝ≥0 => P₁.map fun ω => I.restrict fun s => B₁ s ω) =
      BrownianReal.projectiveFamily := funext fun I => (h₁.hasLaw I).map_eq
  have e₂ : (fun I : Finset ℝ≥0 => P₂.map fun ω => I.restrict fun s => B₂ s ω) =
      BrownianReal.projectiveFamily := funext fun I => (h₂.hasLaw I).map_eq
  rw [e₁] at k₁
  rw [e₂] at k₂
  exact k₁.unique k₂

section Markov

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P]
  {𝓕 : Filtration ℝ≥0 mΩ} {B : ℝ≥0 → Ω → ℝ}

/-- **Strong Markov property with a parameter.** Let `T` be a finite stopping time, `ξ` an
`𝓕_T`-measurable random element and `S` a measurable set such that for every fixed `e`, almost
surely `(e, path of B) ∈ S`. Then almost surely `(ξ, path of B restarted at T) ∈ S`. -/
theorem ae_mem_of_strongMarkov {E : Type*} [MeasurableSpace E]
    (hB : IsFilteredBrownianReal 𝓕 B P) (hBc : ∀ ω, Continuous (B · ω)) {T : Ω → ℝ≥0}
    (hT : IsStoppingTime 𝓕 fun ω => (T ω : WithTop ℝ≥0)) {ξ : Ω → E}
    (hξ : Measurable[hT.measurableSpace] ξ) {S : Set (E × (ℝ≥0 → ℝ))} (hS : MeasurableSet S)
    (hfull : ∀ e, ∀ᵐ ω ∂P, (e, fun s => B s ω) ∈ S) :
    ∀ᵐ ω ∂P, (ξ ω, smPath B T ω) ∈ S := by
  have hBm : ∀ t, Measurable (B t) := fun t => (hB.2.1 t).mono (𝓕.le t) le_rfl
  have hind := Restart.indep_future hB
  have hpre := hB.1.toIsPreBrownianReal
  have hsm := measurable_smPath hBc hBm (measurable_of_isStoppingTime hT)
  have hpm : Measurable fun ω (s : ℝ≥0) => B s ω := measurable_pi_iff.2 hBm
  have hξm : Measurable ξ := hξ.mono hT.measurableSpace_le le_rfl
  have hindep := indepFun_smPath hpre hBc hBm hind hT hξ
  have hlaw : P.map (smPath B T) = P.map (fun ω s => B s ω) := by
    have := map_restrict_smPath_eq hpre hBc hBm hind hT (@MeasurableSet.univ Ω hT.measurableSpace)
    rwa [Measure.restrict_univ, measure_univ, one_smul] at this
  have hprod := (indepFun_iff_map_prod_eq_prod_map_map hξm.aemeasurable hsm.aemeasurable).1 hindep
  rw [hlaw] at hprod
  have hmeas : Measurable fun ω => (ξ ω, smPath B T ω) := hξm.prodMk hsm
  rw [ae_iff]
  have e : P {ω | ¬ (ξ ω, smPath B T ω) ∈ S} =
      (P.map fun ω => (ξ ω, smPath B T ω)) Sᶜ := by
    rw [Measure.map_apply hmeas hS.compl]; rfl
  rw [e, hprod, Measure.prod_apply hS.compl]
  have hzero : ∀ x, (P.map fun ω (s : ℝ≥0) => B s ω) (Prod.mk x ⁻¹' Sᶜ) = 0 := fun x => by
    rw [Measure.map_apply hpm (hS.compl.preimage measurable_prodMk_left)]
    exact ae_iff.1 (hfull x)
  simp only [hzero, lintegral_zero]

end Markov

/-! ### Right-continuous filtrations -/

section RightCont

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {𝓕 : Filtration ℝ≥0 mΩ} [𝓕.IsRightContinuous]

theorem measurableSet_of_forall_gt {t : ℝ≥0} {S : Set Ω}
    (h : ∀ u : ℝ≥0, t < u → MeasurableSet[𝓕 u] S) : MeasurableSet[𝓕 t] S := by
  apply Filtration.IsRightContinuous.measurableSet
  rw [Filtration.rightCont_eq, MeasurableSpace.measurableSet_iInf]
  intro u
  rw [MeasurableSpace.measurableSet_iInf]
  exact fun hu => h u hu

/-- With a right-continuous filtration and a random time `ℓ` with `{ℓ < u} ∈ 𝓕 u`, an event `S`
with `S ∩ {ℓ < u} ∈ 𝓕 u` for all `u` satisfies `S ∩ {ℓ ≤ t} ∈ 𝓕 t`. -/
theorem measurableSet_inter_le {ℓ : Ω → ℝ≥0∞} (hℓ : ∀ u : ℝ≥0, MeasurableSet[𝓕 u] {ω | ℓ ω < u})
    {S : Set Ω} (hS : ∀ u : ℝ≥0, MeasurableSet[𝓕 u] (S ∩ {ω | ℓ ω < u})) (t : ℝ≥0) :
    MeasurableSet[𝓕 t] (S ∩ {ω | ℓ ω ≤ t}) := by
  have hst : IsStoppingTime 𝓕 (fun ω => (ℓ ω : WithTop ℝ≥0)) :=
    isStoppingTime_of_measurableSet_lt_of_isRightContinuous fun u => hℓ u
  refine measurableSet_of_forall_gt fun u hu => ?_
  have e : S ∩ {ω | ℓ ω ≤ t} = (S ∩ {ω | ℓ ω < u}) ∩ {ω | ℓ ω ≤ t} := by
    ext ω
    simp only [mem_inter_iff, mem_ofPred_eq]
    refine ⟨fun ⟨h1, h2⟩ => ⟨⟨h1, lt_of_le_of_lt h2 (by exact_mod_cast hu)⟩, h2⟩,
      fun ⟨⟨h1, _⟩, h2⟩ => ⟨h1, h2⟩⟩
  rw [e]
  exact (hS u).inter (𝓕.mono hu.le _ (hst.measurableSet_le t))

end RightCont

/-! ### The maximal solution driven by a path of `B` -/

section Process

variable {nL nR : ℕ} {a : ℝ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ}

/-- Separated, ordered words that do not satisfy the threshold condition at the driver: the words
from which the construction starts and restarts. -/
def GoodWord (ρL : Fin nL → ℝ) (ρR : Fin nR → ℝ) (s : MWord nL nR) : Prop :=
  (∀ i j, s.1 i < s.2 j) ∧ IsOrderedForceWord s.1 s.2 ∧
    ¬ ForceWord.ThresholdCondition ρL ρR 0 s.1 s.2

theorem measurableSet_goodWord : MeasurableSet {s : MWord nL nR | GoodWord ρL ρR s} := by
  have e : {s : MWord nL nR | IsOrderedForceWord s.1 s.2} =
      {s : MWord nL nR | (∀ i j : Fin nL, i ≤ j → s.1 j ≤ s.1 i) ∧ (∀ i, s.1 i ≤ 0) ∧
        (∀ i j : Fin nR, i ≤ j → s.2 i ≤ s.2 j) ∧ ∀ j, 0 ≤ s.2 j} := rfl
  have hL : ∀ i, Measurable fun s : MWord nL nR => s.1 i := fun i =>
    (measurable_pi_apply i).comp measurable_fst
  have hR : ∀ j, Measurable fun s : MWord nL nR => s.2 j := fun j =>
    (measurable_pi_apply j).comp measurable_snd
  have h1 : MeasurableSet {s : MWord nL nR | ∀ i j, s.1 i < s.2 j} :=
    measurableSet_setOfPred.2 (Measurable.forall fun i => Measurable.forall fun j =>
      measurable_lt' (hL i) (hR j))
  have h2 : MeasurableSet {s : MWord nL nR | IsOrderedForceWord s.1 s.2} := by
    rw [e]
    refine measurableSet_setOfPred.2 ((Measurable.forall fun i => Measurable.forall fun j =>
      measurable_const_imp _ (measurable_le' (hL j) (hL i))).and
      ((Measurable.forall fun i => measurable_le' (hL i) measurable_const).and
      ((Measurable.forall fun i => Measurable.forall fun j =>
        measurable_const_imp _ (measurable_le' (hR i) (hR j))).and
      (Measurable.forall fun j => measurable_le' measurable_const (hR j)))))
  have h3 : MeasurableSet {s : MWord nL nR | ForceWord.ThresholdCondition ρL ρR 0 s.1 s.2} :=
    (measurable_const.prodMk measurable_id) (measurableSet_thr ρL ρR)
  exact h1.inter (h2.inter h3.compl)

variable (a ρL ρR) in
/-- **Positive horizons along almost every path**: from every good word, the local solutions
driven by almost every path of `B` reach a positive horizon. (Proved in `Assembly2Girs`.) -/
def HasPosLife {Ω : Type*} {mΩ : MeasurableSpace Ω} (P : Measure Ω) (B : ℝ≥0 → Ω → ℝ) : Prop :=
  ∀ s : MWord nL nR, GoodWord ρL ρR s → ∀ᵐ ω ∂P, 0 < lifeMax a ρL ρR s (enc (B · ω))

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
  {B : ℝ≥0 → Ω → ℝ} {s : MWord nL nR}

variable (a ρL ρR) in
/-- The maximal horizon of the local solutions from `s` driven by the path of `B`. -/
def lifeProc (s : MWord nL nR) (B : ℝ≥0 → Ω → ℝ) (ω : Ω) : ℝ≥0∞ :=
  lifeMax a ρL ρR s (enc (B · ω))

variable (a ρL ρR) in
/-- The maximal local solution from `s` driven by the path of `B`. -/
def codeProc (s : MWord nL nR) (B : ℝ≥0 → Ω → ℝ) (ω : Ω) : XCode nL nR :=
  maxCode a ρL ρR s (enc (B · ω))

theorem uc_enc_of_continuous {f : ℝ≥0 → ℝ} (hf : Continuous f) : ∀ T : ℕ, UC (enc f) T :=
  fun _ => uc_enc hf.continuousOn

theorem dec_enc_of_continuous {f : ℝ≥0 → ℝ} (hf : Continuous f) : dec (enc f) = f :=
  funext fun _ => dec_enc hf.continuousWithinAt

/-- The code of the path stopped at `r` is `𝓕 r`-measurable. -/
theorem measurable_enc_stop (hB : Adapted 𝓕 B) (r : ℝ≥0) :
    Measurable[𝓕 r] fun ω => enc fun t => B (min t r) ω := by
  let _ : MeasurableSpace Ω := 𝓕 r
  refine measurable_pi_iff.2 fun n => measurable_pi_iff.2 fun k => ?_
  exact (hB (min (dyad n k) r)).mono (𝓕.mono (min_le_right _ _)) le_rfl

/-- **A functional of the code of the path that only sees the path up to `r` is `𝓕 r`-measurable.** -/
theorem measurable_of_local {β : Type*} [MeasurableSpace β] {Φ : PCode → β} (hΦ : Measurable Φ)
    (hB : Adapted 𝓕 B) (hBc : ∀ ω, Continuous (B · ω)) {r : ℝ≥0}
    (hloc : ∀ f g : ℝ≥0 → ℝ, Continuous f → Continuous g → (∀ t ≤ r, g t = f t) →
      Φ (enc g) = Φ (enc f)) :
    Measurable[𝓕 r] fun ω => Φ (enc (B · ω)) := by
  have e : (fun ω => Φ (enc (B · ω))) = fun ω => Φ (enc fun t => B (min t r) ω) :=
    funext fun ω => (hloc (fun t => B t ω) (fun t => B (min t r) ω) (hBc ω)
      ((hBc ω).comp (continuous_id.min continuous_const)) fun t ht => by
        show B (min t r) ω = B t ω
        rw [min_eq_left ht]).symm
  rw [e]
  exact hΦ.comp (measurable_enc_stop hB r)

theorem measurableSet_of_measurable_prop {m : MeasurableSpace Ω} {p : Ω → Prop}
    (hp : Measurable[m] p) : MeasurableSet[m] {ω | p ω} := by
  let _ : MeasurableSpace Ω := m
  exact measurableSet_setOfPred.2 hp

theorem measurable_lifeMax_left : Measurable fun c : PCode => lifeMax a ρL ρR s c := by
  have h := (measurable_lifeMax (a := a) (ρL := ρL) (ρR := ρR)).comp
    (f := fun c : PCode => (s, c)) (measurable_const.prodMk measurable_id)
  simpa only [Function.comp_def] using h

theorem measurable_maxCode_left : Measurable fun c : PCode => maxCode a ρL ρR s c := by
  have h := (measurable_maxCode (a := a) (ρL := ρL) (ρR := ρR)).comp
    (f := fun c : PCode => (s, c)) (measurable_const.prodMk measurable_id)
  simpa only [Function.comp_def] using h

/-- Locality of the maximal horizon for codes of continuous paths. -/
theorem lifeMax_local (hs : ∀ i j, s.1 i < s.2 j) {f g : ℝ≥0 → ℝ} (hf : Continuous f)
    (hg : Continuous g) {r : ℝ≥0} (h : ∀ t ≤ r, g t = f t) :
    (lifeMax a ρL ρR s (enc g) < r ↔ lifeMax a ρL ρR s (enc f) < r) ∧
      (lifeMax a ρL ρR s (enc f) < r → lifeMax a ρL ρR s (enc g) = lifeMax a ρL ρR s (enc f) ∧
        (maxCode a ρL ρR s (enc g)).2 = (maxCode a ρL ρR s (enc f)).2) := by
  have heq : ∀ t ≤ r, dec (enc g) t = dec (enc f) t := fun t ht => by
    rw [dec_enc_of_continuous hf, dec_enc_of_continuous hg]; exact h t ht
  have key := lifeMax_eq_of_eqOn (a := a) (ρL := ρL) (ρR := ρR) hs (uc_enc_of_continuous hf)
    (uc_enc_of_continuous hg) heq
  have key' := lifeMax_eq_of_eqOn (a := a) (ρL := ρL) (ρR := ρR) hs (uc_enc_of_continuous hg)
    (uc_enc_of_continuous hf) fun t ht => (heq t ht).symm
  refine ⟨⟨fun hgr => ?_, fun hfr => ?_⟩, key⟩
  · rw [(key' hgr).1]; exact hgr
  · rw [(key hfr).1]; exact hfr

/-- Events of the maximal solution before `u` belong to `𝓕 u`. -/
theorem measurableSet_lifeProc_lt (hs : ∀ i j, s.1 i < s.2 j) (hB : Adapted 𝓕 B)
    (hBc : ∀ ω, Continuous (B · ω)) (u : ℝ≥0) {Q : Set (SCode nL nR)} (hQ : MeasurableSet Q) :
    MeasurableSet[𝓕 u] {ω | lifeProc a ρL ρR s B ω < u ∧ (codeProc a ρL ρR s B ω).2 ∈ Q} := by
  have hΦ : Measurable fun c : PCode =>
      lifeMax a ρL ρR s c < u ∧ (maxCode a ρL ρR s c).2 ∈ Q :=
    (measurableSet_setOfPred.1 (measurableSet_lt measurable_lifeMax_left measurable_const)).and
      (measurableSet_setOfPred.1 ((measurable_snd.comp measurable_maxCode_left) hQ))
  refine measurableSet_of_measurable_prop (measurable_of_local hΦ hB hBc fun f g hf hg h => ?_)
  obtain ⟨hiff, hk⟩ := lifeMax_local (a := a) (ρL := ρL) (ρR := ρR) hs hf hg h
  refine propext ⟨fun ⟨h1, h2⟩ => ⟨hiff.1 h1, ?_⟩, fun ⟨h1, h2⟩ => ⟨hiff.2 h1, ?_⟩⟩
  · rw [← (hk (hiff.1 h1)).2]; exact h2
  · rw [(hk h1).2]; exact h2

theorem measurableSet_lifeProc_lt' (hs : ∀ i j, s.1 i < s.2 j) (hB : Adapted 𝓕 B)
    (hBc : ∀ ω, Continuous (B · ω)) (u : ℝ≥0) :
    MeasurableSet[𝓕 u] {ω | lifeProc a ρL ρR s B ω < u} := by
  have := measurableSet_lifeProc_lt (a := a) (ρL := ρL) (ρR := ρR) hs hB hBc u
    MeasurableSet.univ
  simpa only [mem_univ, and_true] using this

/-- **The maximal solution is adapted** (with a right-continuous filtration). -/
theorem measurableSet_stateAt_codeProc [𝓕.IsRightContinuous] (hs : ∀ i j, s.1 i < s.2 j)
    (hB : Adapted 𝓕 B) (hBc : ∀ ω, Continuous (B · ω)) (t : ℝ≥0)
    {D : Set (ℝ × (Fin nL → ℝ) × (Fin nR → ℝ))} (hD : MeasurableSet D) :
    MeasurableSet[𝓕 t] {ω | (t : ℝ≥0∞) < lifeProc a ρL ρR s B ω ∧
      stateAt (codeProc a ρL ρR s B ω) t ∈ D} := by
  have hΦ : Measurable fun c : PCode =>
      (t : ℝ≥0∞) < lifeMax a ρL ρR s c ∧ stateAt (maxCode a ρL ρR s c) t ∈ D :=
    (measurableSet_setOfPred.1 (measurableSet_lt measurable_const measurable_lifeMax_left)).and
      (measurableSet_setOfPred.1 (((measurable_stateAt t).comp measurable_maxCode_left) hD))
  refine measurableSet_of_forall_gt fun u htu => measurableSet_of_measurable_prop
    (measurable_of_local hΦ hB hBc fun f g hf hg h => ?_)
  have heq : ∀ t' ≤ u, dec (enc g) t' = dec (enc f) t' := fun t' ht' => by
    rw [dec_enc_of_continuous hf, dec_enc_of_continuous hg]; exact h t' ht'
  obtain ⟨hiff, hk⟩ := lt_lifeMax_iff_of_eqOn (a := a) (ρL := ρL) (ρR := ρR) hs
    (uc_enc_of_continuous hf) (uc_enc_of_continuous hg) heq htu
  refine propext ⟨fun ⟨h1, h2⟩ => ⟨hiff.1 h1, ?_⟩, fun ⟨h1, h2⟩ => ⟨hiff.2 h1, ?_⟩⟩
  · rw [← hk (hiff.1 h1)]; exact h2
  · rw [hk h1]; exact h2

end Process

/-! ### The restart word at the horizon -/

section RestartWord

variable {nL nR : ℕ} {a : ℝ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ}

/-- The restart word at the horizon: the dyadic limit state seen from the limit of the driver. -/
def restartWord (x : XCode nL nR) : MWord nL nR :=
  (fun i => limVL x i - limW x, fun j => limVR x j - limW x)

theorem measurable_restartWord : Measurable (restartWord (nL := nL) (nR := nR)) := by
  have h := measurable_limState (nL := nL) (nR := nR)
  refine (measurable_pi_iff.2 fun i => ?_).prodMk (measurable_pi_iff.2 fun j => ?_)
  · exact ((measurable_pi_apply i).comp (measurable_fst.comp (measurable_snd.comp h))).sub
      (measurable_fst.comp h)
  · exact ((measurable_pi_apply j).comp (measurable_snd.comp (measurable_snd.comp h))).sub
      (measurable_fst.comp h)

theorem thresholdCondition_sub_self_iff (w : ℝ) (vL : Fin nL → ℝ) (vR : Fin nR → ℝ) :
    ForceWord.ThresholdCondition ρL ρR 0 (fun i => vL i - w) (fun j => vR j - w) ↔
      ForceWord.ThresholdCondition ρL ρR w vL vR := by
  have e : (0 : ℝ) = w - w := (sub_self w).symm
  rw [e]
  unfold ForceWord.ThresholdCondition
  simp only [sub_left_inj]

/-- **The restart word at a horizon where the state converges to a non-threshold state is good.** -/
theorem goodWord_restartWord {s : MWord nL nR} (hs : GoodWord ρL ρR s) {x : XCode nL nR}
    {b : ℝ≥0 → ℝ} (hp : IsSLEPathUpTo a s.1 s.2 ρL ρR (cw x) (cvL x) (cvR x) b (cζ x))
    {σ : ℝ≥0} (hσ : (σ : ℝ≥0∞) = cζ x) (hσ0 : 0 < σ)
    (hlim : Tendsto (stateAt x) (𝓝[<] σ) (𝓝 (limState x)))
    (hthr : ¬ ForceWord.ThresholdCondition ρL ρR (limW x) (limVL x) (limVR x)) :
    GoodWord ρL ρR (restartWord x) := by
  have : NeBot (𝓝[<] σ) := nhdsLT_neBot_of_exists_lt ⟨0, hσ0⟩
  set C : Set (ℝ × (Fin nL → ℝ) × (Fin nR → ℝ)) :=
    ordSet ∩ ((⋂ i, {q | q.2.1 i ≤ s.1 i}) ∩ ⋂ j, {q | s.2 j ≤ q.2.2 j}) with hC
  have hCc : IsClosed C := by
    refine isClosed_ordSet.inter ((isClosed_iInter fun i => ?_).inter (isClosed_iInter fun j => ?_))
    · exact isClosed_le ((continuous_apply i).comp continuous_snd.fst) continuous_const
    · exact isClosed_le continuous_const ((continuous_apply j).comp continuous_snd.snd)
  have hmem : limState x ∈ C := by
    refine hCc.mem_of_tendsto hlim ?_
    filter_upwards [self_mem_nhdsWithin] with t ht
    have ht' : (t : ℝ≥0∞) < cζ x := by rw [← hσ]; exact_mod_cast ht
    refine ⟨⟨fun i j hij => hp.antitone_vL ht' hij, hp.vL_le_w ht', hp.w_le_vR ht',
      fun i j hij => hp.monotone_vR ht' hij⟩, mem_iInter.2 fun i => hp.vL_le_xL ht' i,
      mem_iInter.2 fun j => hp.xR_le_vR ht' j⟩
  obtain ⟨⟨h1, h2, h3, h4⟩, hL, hR⟩ := hmem
  simp only [limState] at h1 h2 h3 h4
  have hL' : ∀ i, limVL x i ≤ s.1 i := fun i => mem_iInter.1 hL i
  have hR' : ∀ j, s.2 j ≤ limVR x j := fun j => mem_iInter.1 hR j
  refine ⟨fun i j => ?_, ⟨fun i j hij => ?_, fun i => ?_, fun i j hij => ?_, fun j => ?_⟩, ?_⟩
  · show limVL x i - limW x < limVR x j - limW x
    linarith [hL' i, hR' j, hs.1 i j]
  · show limVL x j - limW x ≤ limVL x i - limW x
    linarith [h1 i j hij]
  · show limVL x i - limW x ≤ 0
    linarith [h2 i]
  · show limVR x i - limW x ≤ limVR x j - limW x
    linarith [h4 i j hij]
  · show 0 ≤ limVR x j - limW x
    linarith [h3 j]
  · exact fun h => hthr ((thresholdCondition_sub_self_iff (limW x) (limVL x) (limVR x)).1 h)

end RestartWord

/-! ### Almost surely, the maximal solution is a solution -/

section Main

variable {nL nR : ℕ} {a : ℝ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ}
  {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P]
  {𝓕 : Filtration ℝ≥0 mΩ} [𝓕.IsRightContinuous] {B : ℝ≥0 → Ω → ℝ} {s : MWord nL nR}

variable (ρL ρR) in
/-- The state codes that converge at a positive horizon `< N` to a non-threshold state. -/
def BadSet (N : ℕ) : Set (SCode nL nR) :=
  {y | 0 < y.1 ∧ y.1 < N ∧ Conv ((0 : PCode), y) ∧
    ¬ ForceWord.ThresholdCondition ρL ρR (limW ((0 : PCode), y)) (limVL ((0 : PCode), y))
      (limVR ((0 : PCode), y))}

theorem measurableSet_badSet (N : ℕ) : MeasurableSet (BadSet (nL := nL) (nR := nR) ρL ρR N) := by
  have hg : Measurable fun y : SCode nL nR => ((0 : PCode), y) := measurable_const.prodMk measurable_id
  refine measurableSet_setOfPred.2 ((measurableSet_setOfPred.1
    (measurableSet_lt measurable_const measurable_fst)).and ((measurableSet_setOfPred.1
    (measurableSet_lt measurable_fst measurable_const)).and ((measurable_conv.comp hg).and ?_)))
  exact (measurableSet_setOfPred.1 ((measurable_limState.comp hg) (measurableSet_thr ρL ρR))).not

theorem measurable_enc : Measurable (enc : (ℝ≥0 → ℝ) → PCode) :=
  measurable_pi_iff.2 fun n => measurable_pi_iff.2 fun k => measurable_pi_apply (dyad n k)

/-- `(min ℓ N).toNNReal < i` iff `ℓ < i` or `N < i`. -/
theorem toNNReal_min_lt_iff {ℓ : ℝ≥0∞} {N : ℕ} {i : ℝ≥0} :
    (min ℓ (N : ℝ≥0∞)).toNNReal < i ↔ ℓ < i ∨ (N : ℝ≥0∞) < i := by
  have hfin : min ℓ (N : ℝ≥0∞) ≠ ⊤ :=
    (lt_of_le_of_lt (min_le_right _ _) (ENNReal.natCast_lt_top N)).ne
  rw [← ENNReal.coe_lt_coe, ENNReal.coe_toNNReal hfin, min_lt_iff]

/-- **Restart at the horizon** (the core of the maximal-solution argument): almost surely the
maximal solution does not converge, at a finite positive horizon `< N`, to a non-threshold state. -/
theorem measure_badSet_eq_zero (hpos : HasPosLife a ρL ρR P B) (hs : GoodWord ρL ρR s)
    (hB : IsFilteredBrownianReal 𝓕 B P) (hBc : ∀ ω, Continuous (B · ω)) (N : ℕ) :
    P {ω | (codeProc a ρL ρR s B ω).2 ∈ BadSet ρL ρR N} = 0 := by
  classical
  have hsep := hs.1
  have hBa : Adapted 𝓕 B := hB.2.1
  set A := {ω | (codeProc a ρL ρR s B ω).2 ∈ BadSet ρL ρR N} with hAdef
  have hmem : ∀ ω, codeProc a ρL ρR s B ω ∈ LRel a ρL ρR ∧
      lProj (codeProc a ρL ρR s B ω) = (s, enc (B · ω), lifeProc a ρL ρR s B ω) :=
    fun ω => maxCode_mem hsep (uc_enc_of_continuous (hBc ω))
  have hζ : ∀ ω, cζ (codeProc a ρL ρR s B ω) = lifeProc a ρL ρR s B ω := fun ω =>
    congrArg (fun p => p.2.2) (hmem ω).2
  have hpath : ∀ ω, IsSLEPathUpTo a s.1 s.2 ρL ρR (cw (codeProc a ρL ρR s B ω))
      (cvL (codeProc a ρL ρR s B ω)) (cvR (codeProc a ρL ρR s B ω)) (fun t => B t ω)
      (lifeProc a ρL ρR s B ω) := fun ω => by
    have := isSLEPathUpTo_maxCode (a := a) (ρL := ρL) (ρR := ρR) hsep
      (uc_enc_of_continuous (hBc ω))
    rwa [dec_enc_of_continuous (hBc ω)] at this
  -- the stopping time `T = min ℓ N`
  set T : Ω → ℝ≥0 := fun ω => (min (lifeProc a ρL ρR s B ω) (N : ℝ≥0∞)).toNNReal with hTdef
  have hℓlt : ∀ u : ℝ≥0, MeasurableSet[𝓕 u] {ω | lifeProc a ρL ρR s B ω < u} :=
    measurableSet_lifeProc_lt' hsep hBa hBc
  have hT : IsStoppingTime 𝓕 fun ω => (T ω : WithTop ℝ≥0) := by
    refine isStoppingTime_of_measurableSet_lt_of_isRightContinuous fun i => ?_
    have e : {ω | (T ω : WithTop ℝ≥0) < i} =
        {ω | lifeProc a ρL ρR s B ω < i} ∪ {_ω | (N : ℝ≥0∞) < i} := by
      ext ω
      simp only [mem_ofPred_eq, mem_union, hTdef, WithTop.coe_lt_coe]
      exact toNNReal_min_lt_iff
    rw [e]
    exact (hℓlt i).union (MeasurableSet.const _)
  -- events of the stopped σ-algebra
  have hQms : ∀ {Q : Set (SCode nL nR)}, MeasurableSet Q → Q ⊆ BadSet ρL ρR N →
      MeasurableSet[hT.measurableSpace] {ω | (codeProc a ρL ρR s B ω).2 ∈ Q} := by
    intro Q hQ hQB
    have hlt : ∀ ω, (codeProc a ρL ρR s B ω).2 ∈ Q → lifeProc a ρL ρR s B ω < N := fun ω hω => by
      rw [← hζ ω]; exact (hQB hω).2.1
    have hu : ∀ u : ℝ≥0, MeasurableSet[𝓕 u] ({ω | (codeProc a ρL ρR s B ω).2 ∈ Q} ∩
        {ω | lifeProc a ρL ρR s B ω < u}) := fun u => by
      have e : {ω | (codeProc a ρL ρR s B ω).2 ∈ Q} ∩ {ω | lifeProc a ρL ρR s B ω < u} =
          {ω | lifeProc a ρL ρR s B ω < u ∧ (codeProc a ρL ρR s B ω).2 ∈ Q} := by
        ext ω; simp only [mem_inter_iff, mem_ofPred_eq]; exact and_comm
      rw [e]
      exact measurableSet_lifeProc_lt hsep hBa hBc u hQ
    refine ⟨?_, fun i => ?_⟩
    · have e : {ω | (codeProc a ρL ρR s B ω).2 ∈ Q} = {ω | (codeProc a ρL ρR s B ω).2 ∈ Q} ∩
          {ω | lifeProc a ρL ρR s B ω < (N : ℝ≥0)} := by
        ext ω
        refine ⟨fun h => ⟨h, by exact_mod_cast hlt ω h⟩, fun h => h.1⟩
      rw [e]
      exact le_iSup (fun t => 𝓕 t) (N : ℝ≥0) _ (hu N)
    · have e : {ω | (codeProc a ρL ρR s B ω).2 ∈ Q} ∩ {ω | (T ω : WithTop ℝ≥0) ≤ i} =
          {ω | (codeProc a ρL ρR s B ω).2 ∈ Q} ∩ {ω | lifeProc a ρL ρR s B ω ≤ i} := by
        ext ω
        simp only [mem_inter_iff, mem_ofPred_eq]
        refine and_congr_right fun h => ?_
        have hmin : min (lifeProc a ρL ρR s B ω) (N : ℝ≥0∞) = lifeProc a ρL ρR s B ω :=
          min_eq_left (hlt ω h).le
        have hfin : lifeProc a ρL ρR s B ω ≠ ⊤ :=
          (lt_of_lt_of_le (hlt ω h) le_top).ne
        simp only [hTdef, hmin]
        rw [← ENNReal.coe_toNNReal hfin]
        exact WithTop.coe_le_coe.trans ENNReal.coe_le_coe.symm
      rw [e]
      exact measurableSet_inter_le hℓlt hu i
  have hA : MeasurableSet[hT.measurableSpace] A := hQms (measurableSet_badSet N) subset_rfl
  -- the restart word
  set ξ : Ω → MWord nL nR := fun ω => if ω ∈ A then restartWord (codeProc a ρL ρR s B ω) else s
    with hξdef
  have hξ : Measurable[hT.measurableSpace] ξ := by
    intro D hD
    have e : ξ ⁻¹' D = {ω | (codeProc a ρL ρR s B ω).2 ∈ BadSet ρL ρR N ∩
        {y | restartWord ((0 : PCode), y) ∈ D}} ∪ (Aᶜ ∩ {_ω | s ∈ D}) := by
      ext ω
      simp only [mem_preimage, hξdef, mem_union, mem_inter_iff, mem_ofPred_eq, mem_compl_iff]
      by_cases hω : ω ∈ A
      · simp only [hω, ↓reduceIte, not_true_eq_false, false_and, or_false]
        exact ⟨fun h => ⟨hω, h⟩, fun h => h.2⟩
      · simp only [hω, ↓reduceIte, not_false_eq_true, true_and]
        exact ⟨fun h => Or.inr h, fun h => h.elim (fun h' => absurd h'.1 hω) id⟩
    rw [e]
    refine (hQms ((measurableSet_badSet N).inter ((measurable_restartWord.comp
      (measurable_const.prodMk measurable_id)) hD)) inter_subset_left).union
      (hA.compl.inter (MeasurableSet.const _))
  -- the strong Markov property at `T`
  set Sg : Set (MWord nL nR × (ℝ≥0 → ℝ)) :=
    {p | GoodWord ρL ρR p.1 → 0 < lifeMax a ρL ρR p.1 (enc p.2)} with hSg
  have hSm : MeasurableSet Sg := by
    have e : Sg = (Prod.fst ⁻¹' {s' : MWord nL nR | GoodWord ρL ρR s'})ᶜ ∪
        {p | 0 < lifeMax a ρL ρR p.1 (enc p.2)} := by
      ext p; simp only [hSg, mem_ofPred_eq, mem_union, mem_compl_iff, mem_preimage]; tauto
    have hl : Measurable fun p : MWord nL nR × (ℝ≥0 → ℝ) => lifeMax a ρL ρR p.1 (enc p.2) := by
      have h := (measurable_lifeMax (a := a) (ρL := ρL) (ρR := ρR)).comp
        (f := fun p : MWord nL nR × (ℝ≥0 → ℝ) => (p.1, enc p.2))
        (measurable_fst.prodMk (measurable_enc.comp measurable_snd))
      simpa only [Function.comp_def] using h
    rw [e]
    exact (measurableSet_goodWord.preimage measurable_fst).compl.union
      (measurableSet_lt measurable_const hl)
  have hfull : ∀ e, ∀ᵐ ω ∂P, (e, fun t => B t ω) ∈ Sg := by
    intro e
    by_cases he : GoodWord ρL ρR e
    · filter_upwards [hpos e he] with ω hω using fun _ => hω
    · exact ae_of_all _ fun ω h => absurd h he
  have hsm := ae_mem_of_strongMarkov hB hBc hT hξ hSm hfull
  refine measure_mono_null (fun ω hωA => ?_) (ae_iff.1 hsm)
  simp only [mem_ofPred_eq]
  intro hS
  -- a local solution after the horizon contradicts maximality
  set x := codeProc a ρL ρR s B ω with hx
  obtain ⟨hℓ0, hℓN, hconv, hthr⟩ : x.2 ∈ BadSet ρL ρR N := id hωA
  have hℓ0' : 0 < cζ x := hℓ0
  have hℓN' : cζ x < N := hℓN
  have hconv' : Conv x := hconv
  have hthr' : ¬ ForceWord.ThresholdCondition ρL ρR (limW x) (limVL x) (limVR x) := hthr
  have hfin : cζ x ≠ ⊤ := (lt_of_lt_of_le hℓN' le_top).ne
  set σ := (cζ x).toNNReal with hσdef
  have hσ : (σ : ℝ≥0∞) = cζ x := ENNReal.coe_toNNReal hfin
  have hσ0 : 0 < σ := by
    have : (0 : ℝ≥0∞) < σ := by rw [hσ]; exact hℓ0'
    exact_mod_cast this
  have hTσ : T ω = σ := by
    simp only [hTdef, hσdef]
    rw [← hζ ω, min_eq_left hℓN'.le]
  have hξω : ξ ω = restartWord x := by simp only [hξdef, hωA, ↓reduceIte, hx]
  have hgood : GoodWord ρL ρR (restartWord x) := by
    have hp := hpath ω
    rw [← hζ ω] at hp
    exact goodWord_restartWord hs hp hσ hσ0 (tendsto_of_conv (hmem ω).1.1.continuousOn_stateAt
      hσ hconv') hthr'
  rw [hξω] at hS
  have hq := hS hgood
  set g : ℝ≥0 → ℝ := smPath B T ω with hg
  have hgc : Continuous g := ((hBc ω).comp (continuous_const.add continuous_id)).sub continuous_const
  have h₂ := isSLEPathUpTo_maxCode (a := a) (ρL := ρL) (ρR := ρR) hgood.1
    (uc_enc_of_continuous hgc)
  rw [dec_enc_of_continuous hgc] at h₂
  have h₁ := hpath ω
  rw [← hζ ω, ← hσ] at h₁
  have hlim := tendsto_of_conv (hmem ω).1.1.continuousOn_stateAt hσ hconv'
  have key := h₁.concat_of_tendsto hσ0 (hBc ω).continuousAt hlim h₂ fun t => by
    rw [hg]; simp only [smPath, smShift, hTσ]
  have hL := le_lifeMax (mem_lSet_of_isSLEPathUpTo hsep (hBc ω) key le_rfl)
  have e1 : lifeMax a ρL ρR s (enc fun t => B t ω) = (σ : ℝ≥0∞) := by
    rw [hσ, hζ ω]; rfl
  rw [e1] at hL
  exact absurd hL (not_le.2 (ENNReal.lt_add_right ENNReal.coe_ne_top hq.ne'))

/-- **Almost surely, the maximal local solution driven by `B` is a solution of Definition 2.1.** -/
theorem ae_isIntegratedSLEPath_codeProc (hpos : HasPosLife a ρL ρR P B) (hs : GoodWord ρL ρR s)
    (hB : IsFilteredBrownianReal 𝓕 B P) (hBc : ∀ ω, Continuous (B · ω)) :
    ∀ᵐ ω ∂P, IsIntegratedSLEPath a s.1 s.2 ρL ρR (cw (codeProc a ρL ρR s B ω))
      (cvL (codeProc a ρL ρR s B ω)) (cvR (codeProc a ρL ρR s B ω)) (fun t => B t ω)
      (lifeProc a ρL ρR s B ω) := by
  have hsep := hs.1
  have hnot : ∀ᵐ ω ∂P, ∀ N : ℕ, (codeProc a ρL ρR s B ω).2 ∉ BadSet ρL ρR N := by
    rw [ae_all_iff]
    intro N
    exact measure_eq_zero_iff_ae_notMem.1 (measure_badSet_eq_zero hpos hs hB hBc N)
  filter_upwards [hpos s hs, hnot] with ω h0 hN
  have hx : codeProc a ρL ρR s B ω ∈ LRel a ρL ρR :=
    (maxCode_mem (a := a) (ρL := ρL) (ρR := ρR) hsep (uc_enc_of_continuous (hBc ω))).1
  have hproj : lProj (codeProc a ρL ρR s B ω) = (s, enc (B · ω), lifeProc a ρL ρR s B ω) :=
    (maxCode_mem (a := a) (ρL := ρL) (ρR := ρR) hsep (uc_enc_of_continuous (hBc ω))).2
  simp only [lProj, Prod.mk.injEq] at hproj
  obtain ⟨hw, hb, hζ⟩ := hproj
  have key := isIntegratedSLEPath_of_lRel hx (fun h => absurd (hζ.symm.trans h) h0.ne')
    fun h1 h2 hc => by
      by_contra hthr
      obtain ⟨N, hN'⟩ := ENNReal.exists_nat_gt h2.ne
      exact hN N ⟨h1, hN', hc, hthr⟩
  have hwL : wordL (codeProc a ρL ρR s B ω) = s.1 := congrArg Prod.fst hw
  have hwR : wordR (codeProc a ρL ρR s B ω) = s.2 := congrArg Prod.snd hw
  have hcb : cb (codeProc a ρL ρR s B ω) = fun t => B t ω := by
    unfold cb
    rw [hb, dec_enc_of_continuous (hBc ω)]
  rw [hwL, hwR, hcb, hζ] at key
  exact key

/-- **The maximal local solution driven by `B` is an integrated `SLE_a(ρ)` evolution** (frozen
Definition 2.1), on the right-continuous filtration of `B`. -/
theorem isIntegratedSLEEvolution_codeProc (hpos : HasPosLife a ρL ρR P B)
    (hs : GoodWord ρL ρR s) (hB : IsFilteredBrownianReal 𝓕 B P) (hBc : ∀ ω, Continuous (B · ω)) :
    IsIntegratedSLEEvolution a s.1 s.2 ρL ρR P 𝓕 (fun t ω => cw (codeProc a ρL ρR s B ω) t)
      (fun i t ω => cvL (codeProc a ρL ρR s B ω) i t)
      (fun j t ω => cvR (codeProc a ρL ρR s B ω) j t) B (lifeProc a ρL ρR s B) := by
  have hsep := hs.1
  have hBa : Adapted 𝓕 B := hB.2.1
  refine ⟨hB, fun t D hD => ?_, fun i t D hD => ?_, fun j t D hD => ?_,
    ae_isIntegratedSLEPath_codeProc hpos hs hB hBc⟩
  · exact measurableSet_stateAt_codeProc hsep hBa hBc t (measurable_fst hD)
  · exact measurableSet_stateAt_codeProc hsep hBa hBc t
      (((measurable_pi_apply i).comp (measurable_fst.comp measurable_snd)) hD)
  · exact measurableSet_stateAt_codeProc hsep hBa hBc t
      (((measurable_pi_apply j).comp (measurable_snd.comp measurable_snd)) hD)

end Main

end Assembly2

end Sec2

end InteractingSLE
