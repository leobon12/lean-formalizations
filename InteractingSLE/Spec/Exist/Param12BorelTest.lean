/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Exist.Param12LimitCanon
import InteractingSLE.Spec.Exist.Param12FamilyRel
import InteractingSLE.Spec.Sec2.RestartMarkov
import QuantumZipper.Proofs.Probability.BMExistence

/-!
# A Borel test for evolution laws on the code space (S3)

Packet PROVE-PARAM12C (step S3 of `planning/handoffs/PROVE-PARAM12B.md` §5). On the code space `XCode nL nR`:

* `codeObs t`: the observation up to time `t` (the codes at the dyadic times `≤ t`, aliveness at those times and at
  `t`), and the filtration `codeFilt` it generates; the decoded driving path, driver and marks are adapted to it
  (`adapted_cb`, `adaptedBefore_cw`, …) for every code;
* `wienerCode`: the law of the dyadic code of a Brownian motion (the same for every Brownian motion,
  `map_enc_eq_wienerCode`);
* `IsEvoLaw κ w ν`: the code is almost surely a canonical solution code of the word, the driving code has the law
  `wienerCode`, and at dyadic times `s ≤ t` the increment `b_t − b_s` is a centred Gaussian of variance `t − s`
  independent of the observation up to `s` (one product-law identity per pair). Countably many measure identities;
* `isIntegratedSLEEvolution_canon`: under an evolution law the canonical processes form an integrated evolution for
  `codeFilt`; `isEvoLaw_map_codeOf`: the code law of every evolution is an evolution law.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal

namespace InteractingSLE

namespace Exist

namespace Param12

open Sec2.Assembly Staged

variable {nL nR : ℕ}

/-! ### The observation up to a time and the code filtration -/

/-- The code values at the dyadic time `dyad n k`: driving code, driver and marks. -/
def obsD (n k : ℕ) (x : XCode nL nR) : ℝ × ℝ × (Fin nL → ℝ) × (Fin nR → ℝ) :=
  (x.1 n k, x.2.2.1 n k, fun i => x.2.2.2.1 i n k, fun j => x.2.2.2.2 j n k)

/-- The type of observations up to a time. -/
abbrev ObsY (nL nR : ℕ) : Type := (ℕ × ℕ → ℝ × ℝ × (Fin nL → ℝ) × (Fin nR → ℝ)) × (ℕ × ℕ → ℝ) × ℝ

/-- **The observation up to time `t`**: the code values at the dyadic times `≤ t`, aliveness at those times, and
aliveness at `t`. -/
def codeObs (t : ℝ≥0) (x : XCode nL nR) : ObsY nL nR :=
  (fun p => if dyad p.1 p.2 ≤ t then obsD p.1 p.2 x else 0,
    fun p => if dyad p.1 p.2 ≤ t ∧ (dyad p.1 p.2 : ℝ≥0∞) < cζ x then 1 else 0,
    if (t : ℝ≥0∞) < cζ x then 1 else 0)

theorem measurable_obsD (n k : ℕ) : Measurable (obsD (nL := nL) (nR := nR) n k) :=
  ((measurable_code n k).comp measurable_code_b).prodMk (((measurable_code n k).comp measurable_code_w).prodMk
    ((measurable_pi_iff.2 fun i => (measurable_code n k).comp (measurable_code_vL i)).prodMk
      (measurable_pi_iff.2 fun j => (measurable_code n k).comp (measurable_code_vR j))))

theorem measurableSet_lt_cζ (r : ℝ≥0) : MeasurableSet {x : XCode nL nR | (r : ℝ≥0∞) < cζ x} :=
  measurableSet_lt measurable_const measurable_cζ

theorem measurable_codeObs (t : ℝ≥0) : Measurable (codeObs (nL := nL) (nR := nR) t) := by
  refine (measurable_pi_iff.2 fun p => ?_).prodMk ((measurable_pi_iff.2 fun p => ?_).prodMk ?_)
  · by_cases h : dyad p.1 p.2 ≤ t
    · simp only [h, ↓reduceIte]; exact measurable_obsD _ _
    · simp only [h, ↓reduceIte]; exact measurable_const
  · by_cases h : dyad p.1 p.2 ≤ t
    · simp only [h, true_and]
      exact Measurable.ite (measurableSet_lt_cζ _) measurable_const measurable_const
    · simp only [h, false_and, ↓reduceIte]; exact measurable_const
  · exact Measurable.ite (measurableSet_lt_cζ _) measurable_const measurable_const

/-- Aliveness at `t < t'` is read from the aliveness at the dyadic times in `(t, t')`. -/
theorem lt_cζ_iff_exists_dyad {t t' : ℝ≥0} (htt' : t < t') (x : XCode nL nR) :
    (t : ℝ≥0∞) < cζ x ↔ ∃ p : ℕ × ℕ, t < dyad p.1 p.2 ∧ dyad p.1 p.2 ≤ t' ∧
      (dyad p.1 p.2 : ℝ≥0∞) < cζ x := by
  constructor
  · intro h
    have h' : (t : ℝ≥0∞) < min (cζ x) (t' : ℝ≥0∞) := lt_min h (by exact_mod_cast htt')
    obtain ⟨n, k, h1, h2⟩ := exists_dyad_btwn h'
    refine ⟨(n, k), h1, ?_, h2.trans_le (min_le_left _ _)⟩
    exact_mod_cast (h2.trans_le (min_le_right _ _)).le
  · rintro ⟨p, h1, -, h3⟩
    exact lt_trans (by exact_mod_cast h1) h3

theorem measurable_codeObs_of_le {t t' : ℝ≥0} (htt' : t ≤ t') :
    Measurable[MeasurableSpace.comap (codeObs (nL := nL) (nR := nR) t') inferInstance]
      (codeObs (nL := nL) (nR := nR) t) := by
  set m := MeasurableSpace.comap (codeObs (nL := nL) (nR := nR) t') inferInstance
  have hc : Measurable[m] (codeObs (nL := nL) (nR := nR) t') := comap_measurable _
  have h1 : Measurable[m] fun x : XCode nL nR => (codeObs t' x).1 := measurable_fst.comp hc
  have h2 : Measurable[m] fun x : XCode nL nR => (codeObs t' x).2.1 := measurable_fst.comp (measurable_snd.comp hc)
  refine Measurable.prodMk (m := m) (@measurable_pi_iff _ _ _ m _ _ |>.2 fun p => ?_)
    (Measurable.prodMk (m := m) (@measurable_pi_iff _ _ _ m _ _ |>.2 fun p => ?_) ?_)
  · by_cases h : dyad p.1 p.2 ≤ t
    · have e : (fun x : XCode nL nR => (codeObs t x).1 p) = fun x => (codeObs t' x).1 p := by
        funext x; simp [codeObs, h, h.trans htt']
      show Measurable[m] (fun x => (codeObs t x).1 p); rw [e]; exact (measurable_pi_apply p).comp h1
    · have e : (fun x : XCode nL nR => (codeObs t x).1 p) = fun _ => 0 := by
        funext x; simp [codeObs, h]
      show Measurable[m] (fun x => (codeObs t x).1 p); rw [e]; exact @measurable_const _ _ _ m _
  · by_cases h : dyad p.1 p.2 ≤ t
    · have e : (fun x : XCode nL nR => (codeObs t x).2.1 p) = fun x => (codeObs t' x).2.1 p := by
        funext x; simp [codeObs, h, h.trans htt']
      show Measurable[m] (fun x => (codeObs t x).2.1 p); rw [e]; exact (measurable_pi_apply p).comp h2
    · have e : (fun x : XCode nL nR => (codeObs t x).2.1 p) = fun _ => 0 := by
        funext x; simp [codeObs, h]
      show Measurable[m] (fun x => (codeObs t x).2.1 p); rw [e]; exact @measurable_const _ _ _ m _
  · rcases htt'.lt_or_eq with hlt | heq
    · have hS : MeasurableSet[m] {x : XCode nL nR | (t : ℝ≥0∞) < cζ x} := by
        have e : {x : XCode nL nR | (t : ℝ≥0∞) < cζ x} = ⋃ p : ℕ × ℕ,
            {x | t < dyad p.1 p.2 ∧ (codeObs t' x).2.1 p = 1} := by
          ext x
          simp only [mem_ofPred_eq, mem_iUnion, codeObs]
          rw [lt_cζ_iff_exists_dyad hlt]
          constructor
          · rintro ⟨p, h1, h2, h3⟩; exact ⟨p, h1, by simp [h2, h3]⟩
          · rintro ⟨p, h1, h2⟩
            by_cases hp : dyad p.1 p.2 ≤ t' ∧ (dyad p.1 p.2 : ℝ≥0∞) < cζ x
            · exact ⟨p, h1, hp.1, hp.2⟩
            · simp [hp] at h2
        rw [e]
        refine @MeasurableSet.iUnion _ _ m _ _ fun p => ?_
        by_cases hp : t < dyad p.1 p.2
        · simp only [hp, true_and]
          exact (measurableSet_singleton (1 : ℝ)).preimage ((measurable_pi_apply p).comp h2)
        · simp only [hp, false_and, ofPred_false]; exact @MeasurableSet.empty _ m
      exact Measurable.ite (m := m) hS (@measurable_const _ _ _ m _) (@measurable_const _ _ _ m _)
    · subst heq
      exact measurable_snd.comp (measurable_snd.comp hc)

/-- **The code filtration**: generated by the observations up to each time. -/
def codeFilt : Filtration ℝ≥0 (inferInstance : MeasurableSpace (XCode nL nR)) where
  seq t := MeasurableSpace.comap (codeObs t) inferInstance
  mono' _ _ hst := (measurable_codeObs_of_le hst).comap_le
  le' t := (measurable_codeObs t).comap_le

theorem codeFilt_apply (t : ℝ≥0) :
    (codeFilt (nL := nL) (nR := nR) : ℝ≥0 → MeasurableSpace (XCode nL nR)) t =
      MeasurableSpace.comap (codeObs t) inferInstance := rfl

theorem measurable_codeObs_filt (t : ℝ≥0) :
    Measurable[(codeFilt (nL := nL) (nR := nR)) t] (codeObs t) := comap_measurable _

/-! ### Adaptedness of the decoded coordinates -/

/-- Decoding from an observation up to `t`, through a coordinate `sel` of the dyadic values. -/
def decObs (sel : ℝ × ℝ × (Fin nL → ℝ) × (Fin nR → ℝ) → ℝ) (t : ℝ≥0) (y : ObsY nL nR) : ℝ :=
  limsup (fun n => sel (y.1 (n, flr n t))) atTop

theorem measurable_decObs {sel : ℝ × ℝ × (Fin nL → ℝ) × (Fin nR → ℝ) → ℝ} (hsel : Measurable sel)
    (t : ℝ≥0) : Measurable (decObs sel t) :=
  Measurable.limsup fun _ => hsel.comp ((measurable_pi_apply _).comp measurable_fst)

theorem dec_eq_decObs {sel : ℝ × ℝ × (Fin nL → ℝ) × (Fin nR → ℝ) → ℝ} {c : XCode nL nR → PCode}
    (hc : ∀ x n k, c x n k = sel (obsD n k x)) (t : ℝ≥0) (x : XCode nL nR) :
    dec (c x) t = decObs sel t (codeObs t x) := by
  unfold dec decObs
  congr 1
  funext n
  simp [codeObs, dyad_flr_le n t, hc]

theorem measurable_dec_filt {sel : ℝ × ℝ × (Fin nL → ℝ) × (Fin nR → ℝ) → ℝ} (hsel : Measurable sel)
    {c : XCode nL nR → PCode} (hc : ∀ x n k, c x n k = sel (obsD n k x)) (t : ℝ≥0) :
    Measurable[(codeFilt (nL := nL) (nR := nR)) t] fun x => dec (c x) t := by
  have e : (fun x => dec (c x) t) = decObs sel t ∘ codeObs t := funext fun x => dec_eq_decObs hc t x
  rw [e]
  exact (measurable_decObs hsel t).comp (measurable_codeObs_filt t)

theorem measurableSet_lt_cζ_filt (t : ℝ≥0) :
    MeasurableSet[(codeFilt (nL := nL) (nR := nR)) t] {x : XCode nL nR | (t : ℝ≥0∞) < cζ x} := by
  have e : {x : XCode nL nR | (t : ℝ≥0∞) < cζ x} = (fun x => (codeObs t x).2.2) ⁻¹' {1} := by
    ext x
    simp only [mem_ofPred_eq, mem_preimage, mem_singleton_iff, codeObs]
    split_ifs with h <;> simp [h]
  rw [e]
  exact (measurableSet_singleton 1).preimage (measurable_snd.comp (measurable_snd.comp (measurable_codeObs_filt t)))

theorem adaptedBefore_dec {sel : ℝ × ℝ × (Fin nL → ℝ) × (Fin nR → ℝ) → ℝ} (hsel : Measurable sel)
    {c : XCode nL nR → PCode} (hc : ∀ x n k, c x n k = sel (obsD n k x)) :
    AdaptedBefore (codeFilt (nL := nL) (nR := nR)) cζ fun t x => dec (c x) t := by
  intro t A hA
  have e : {x : XCode nL nR | (t : ℝ≥0∞) < cζ x ∧ dec (c x) t ∈ A} =
      {x | (t : ℝ≥0∞) < cζ x} ∩ (fun x => dec (c x) t) ⁻¹' A := rfl
  rw [e]
  exact (measurableSet_lt_cζ_filt t).inter (measurable_dec_filt hsel hc t hA)

/-- The decoded driving path is adapted to the code filtration. -/
theorem adapted_cb : Adapted (codeFilt (nL := nL) (nR := nR)) fun t x => cb x t :=
  fun t => measurable_dec_filt (sel := fun v => v.1) measurable_fst (c := fun x => x.1)
    (fun _ _ _ => rfl) t

theorem adaptedBefore_cw : AdaptedBefore (codeFilt (nL := nL) (nR := nR)) cζ fun t x => cw x t :=
  adaptedBefore_dec (sel := fun v => v.2.1) measurable_snd.fst (c := fun x => x.2.2.1)
    fun _ _ _ => rfl

theorem adaptedBefore_cvL (i : Fin nL) :
    AdaptedBefore (codeFilt (nL := nL) (nR := nR)) cζ fun t x => cvL x i t :=
  adaptedBefore_dec (sel := fun v => v.2.2.1 i) ((measurable_pi_apply i).comp measurable_snd.snd.fst)
    (c := fun x => x.2.2.2.1 i) fun _ _ _ => rfl

theorem adaptedBefore_cvR (j : Fin nR) :
    AdaptedBefore (codeFilt (nL := nL) (nR := nR)) cζ fun t x => cvR x j t :=
  adaptedBefore_dec (sel := fun v => v.2.2.2 j) ((measurable_pi_apply j).comp measurable_snd.snd.snd)
    (c := fun x => x.2.2.2.2 j) fun _ _ _ => rfl

/-! ### Equality of measures as a measurable condition -/

/-- In a countably generated space, a countable π-system generating the σ-algebra. -/
theorem exists_countable_isPiSystem_generate (Z : Type*) [mZ : MeasurableSpace Z]
    [MeasurableSpace.CountablyGenerated Z] :
    ∃ Cp : Set (Set Z), Cp.Countable ∧ IsPiSystem Cp ∧ mZ = MeasurableSpace.generateFrom Cp := by
  set S := MeasurableSpace.countableGeneratingSet Z
  have hS : S.Countable := MeasurableSpace.countable_countableGeneratingSet
  have : Countable S := hS.to_subtype
  refine ⟨range fun T : Finset S => ⋂ s ∈ T, (s : Set Z), countable_range _, ?_, ?_⟩
  · rintro _ ⟨T, rfl⟩ _ ⟨T', rfl⟩ -
    classical
    refine ⟨T ∪ T', ?_⟩
    ext z
    simp only [mem_iInter, mem_inter_iff, Finset.mem_union]
    constructor
    · intro h; exact ⟨fun s hs => h s (Or.inl hs), fun s hs => h s (Or.inr hs)⟩
    · rintro ⟨h1, h2⟩ s (hs | hs)
      · exact h1 s hs
      · exact h2 s hs
  · refine le_antisymm ?_ ?_
    · rw [← MeasurableSpace.generateFrom_countableGeneratingSet (α := Z)]
      refine MeasurableSpace.generateFrom_le fun s hs => MeasurableSpace.measurableSet_generateFrom ?_
      refine ⟨{⟨s, hs⟩}, ?_⟩
      simp
    · refine MeasurableSpace.generateFrom_le ?_
      rintro _ ⟨T, rfl⟩
      exact Finset.measurableSet_biInter T fun s _ => MeasurableSpace.measurableSet_countableGeneratingSet s.2

/-- **Equality of two measurable families of finite measures on a countably generated space is a measurable
condition.** -/
theorem measurableSet_eq_measure {X Z : Type*} [MeasurableSpace X] [MeasurableSpace Z]
    [StandardBorelSpace Z] {F G : X → Measure Z} (hF : Measurable F) (hG : Measurable G)
    (hFf : ∀ x, IsFiniteMeasure (F x)) :
    MeasurableSet {x | F x = G x} := by
  have : MeasurableSpace.CountablyGenerated Z := by
    let := upgradeStandardBorel Z; infer_instance
  obtain ⟨Cp, hc, hpi, hgen⟩ := exists_countable_isPiSystem_generate Z
  have e : {x | F x = G x} = {x | F x univ = G x univ} ∩ ⋂ A ∈ Cp, {x | F x A = G x A} := by
    ext x
    simp only [mem_ofPred_eq, mem_inter_iff, mem_iInter]
    constructor
    · rintro h; exact ⟨by rw [h], fun A _ => by rw [h]⟩
    · rintro ⟨h1, h2⟩
      exact ext_of_generate_finite Cp hgen hpi h2 h1
  rw [e]
  refine (measurableSet_eq_fun (Measure.measurable_coe MeasurableSet.univ |>.comp hF)
    (Measure.measurable_coe MeasurableSet.univ |>.comp hG)).inter
    (MeasurableSet.biInter hc fun A hA => measurableSet_eq_fun ?_ ?_)
  · have hA : MeasurableSet A := hgen ▸ MeasurableSpace.measurableSet_generateFrom hA
    exact (Measure.measurable_coe hA).comp hF
  · have hA : MeasurableSet A := hgen ▸ MeasurableSpace.measurableSet_generateFrom hA
    exact (Measure.measurable_coe hA).comp hG


/-! ### The law of the dyadic code of a Brownian motion -/

/-- A reference Brownian motion (on the i.i.d. Gaussian sequence space). -/
def refBM : ℝ≥0 → (ℕ → ℝ) → ℝ := QuantumZipper.BMExist.exists_isBrownianReal_stdP.choose

theorem isBrownianReal_refBM : IsBrownianReal refBM LQGDimension.ExistAsm.stdP :=
  QuantumZipper.BMExist.exists_isBrownianReal_stdP.choose_spec

/-- **The law of the dyadic code of a Brownian motion.** -/
def wienerCode : Measure PCode :=
  LQGDimension.ExistAsm.stdP.map fun ω => enc fun t => refBM t ω

theorem aemeasurable_enc {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} {B : ℝ≥0 → Ω → ℝ}
    (hB : ∀ t, AEMeasurable (B t) P) : AEMeasurable (fun ω => enc fun t => B t ω) P :=
  AEMeasurable.of_eval fun n => AEMeasurable.of_eval fun k => hB (dyad n k)

open ProbabilityTheory.BrownianReal in
/-- The finite-dimensional dyadic laws of a pre-Brownian motion. -/
theorem map_dyad_restrict_eq {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} {B : ℝ≥0 → Ω → ℝ}
    (hB : IsPreBrownianReal B P) (I : Finset (ℕ × ℕ)) :
    P.map (fun ω (p : I) => B (dyad p.1.1 p.1.2) ω) =
      (projectiveFamily (I.image fun p => dyad p.1 p.2)).map
        (fun y (p : I) => y ⟨dyad p.1.1 p.1.2, Finset.mem_image_of_mem _ p.2⟩) := by
  set J := I.image fun p => dyad p.1 p.2
  set g : (J → ℝ) → I → ℝ := fun y p => y ⟨dyad p.1.1 p.1.2, Finset.mem_image_of_mem _ p.2⟩ with hg
  have hgm : Measurable g := measurable_pi_iff.2 fun p => measurable_pi_apply _
  have hJ := hB.hasLaw J
  rw [← hJ.map_eq, AEMeasurable.map_map_of_aemeasurable hgm.aemeasurable hJ.aemeasurable]
  rfl

open ProbabilityTheory.BrownianReal in
/-- The dyadic code law of a pre-Brownian motion, as a projective limit. -/
theorem isProjectiveLimit_enc {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}
    {B : ℝ≥0 → Ω → ℝ} (hB : IsPreBrownianReal B P) :
    IsProjectiveLimit ((P.map fun ω => enc fun t => B t ω).map (MeasurableEquiv.curry ℕ ℕ ℝ).symm)
      (fun I : Finset (ℕ × ℕ) => (projectiveFamily (I.image fun p => dyad p.1 p.2)).map
        (fun y (p : I) => y ⟨dyad p.1.1 p.1.2, Finset.mem_image_of_mem _ p.2⟩)) := by
  intro I
  set e := MeasurableEquiv.curry ℕ ℕ ℝ
  show _ = (projectiveFamily _).map _
  rw [← map_dyad_restrict_eq hB I, Measure.map_map (Finset.measurable_restrict _) e.symm.measurable,
    AEMeasurable.map_map_of_aemeasurable ((Finset.measurable_restrict _).comp e.symm.measurable).aemeasurable
      (aemeasurable_enc hB.aemeasurable)]
  rfl

/-- **Every Brownian motion has the same dyadic code law.** -/
theorem map_enc_eq_wienerCode {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P]
    {B : ℝ≥0 → Ω → ℝ} (hB : IsPreBrownianReal B P) :
    P.map (fun ω => enc fun t => B t ω) = wienerCode := by
  set e := MeasurableEquiv.curry ℕ ℕ ℝ
  have := (isProjectiveLimit_enc hB).unique (isProjectiveLimit_enc isBrownianReal_refBM.toIsPreBrownianReal)
  have h3 := congrArg (Measure.map e) this
  rw [Measure.map_map e.measurable e.symm.measurable, Measure.map_map e.measurable e.symm.measurable,
    MeasurableEquiv.self_comp_symm, Measure.map_id, Measure.map_id] at h3
  exact h3

/-! ### Evolution laws -/

instance instStandardBorelSpaceObsD1 : StandardBorelSpace ((Fin nL → ℝ) × (Fin nR → ℝ)) :=
  StandardBorelSpace.prod
instance instStandardBorelSpaceObsD2 : StandardBorelSpace (ℝ × (Fin nL → ℝ) × (Fin nR → ℝ)) :=
  StandardBorelSpace.prod
instance instStandardBorelSpaceObsD : StandardBorelSpace (ℝ × ℝ × (Fin nL → ℝ) × (Fin nR → ℝ)) :=
  StandardBorelSpace.prod
instance instStandardBorelSpaceObsPi : StandardBorelSpace (ℕ × ℕ → ℝ × ℝ × (Fin nL → ℝ) × (Fin nR → ℝ)) :=
  StandardBorelSpace.pi_countable
instance instStandardBorelSpaceObsY2 : StandardBorelSpace ((ℕ × ℕ → ℝ) × ℝ) := StandardBorelSpace.prod
instance instStandardBorelSpaceObsY : StandardBorelSpace (ObsY nL nR) := StandardBorelSpace.prod
instance instStandardBorelSpaceObsYR : StandardBorelSpace (ObsY nL nR × ℝ) := StandardBorelSpace.prod

/-- **Evolution laws on the code space.** The code is almost surely a canonical solution code of the word `w`, the
driving code has the law `wienerCode`, and for dyadic times `s ≤ t` the observation up to `s` and the increment
`b_t − b_s` have the joint law (law of the observation) ⊗ `N(0, t − s)`. -/
def IsEvoLaw (κ : ℝ) (w : WordData nL nR) (ν : Measure (XCode nL nR)) : Prop :=
  ν (CRel κ w.1.1 w.1.2 w.2.1 w.2.2)ᶜ = 0 ∧ ν.map (fun x => x.1) = wienerCode ∧
    ∀ n k n' k' : ℕ, dyad n k ≤ dyad n' k' →
      ν.map (fun x => (codeObs (dyad n k) x, cb x (dyad n' k') - cb x (dyad n k))) =
        (ν.map (codeObs (dyad n k))).prod (gaussianReal 0 (dyad n' k' - dyad n k))

theorem measurable_cb_at (t : ℝ≥0) : Measurable fun x : XCode nL nR => cb x t :=
  (adapted_cb t).mono ((codeFilt (nL := nL) (nR := nR)).le t) le_rfl

/-- The product with a fixed s-finite measure is measurable in the first factor. -/
theorem measurable_prod_const {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y] (γ : Measure Y)
    [SFinite γ] : Measurable fun m : Measure X => m.prod γ := by
  refine Measure.measurable_of_measurable_coe _ fun A hA => ?_
  simp_rw [Measure.prod_apply hA]
  exact Measure.measurable_lintegral (measurable_measure_prodMk_left hA)

theorem measurable_coe_map {Ω' X : Type*} [MeasurableSpace Ω'] [MeasurableSpace X] {g : Ω' → X}
    (hg : Measurable g) : Measurable fun π : ProbabilityMeasure Ω' => (π : Measure Ω').map g :=
  (Measure.measurable_map g hg).comp measurable_subtype_coe

/-- **Evolution laws form a measurable set**, read through a measurable projection `g` onto the code space. -/
theorem measurableSet_isEvoLaw (κ : ℝ) {Ω' : Type*} [MeasurableSpace Ω'] {g : Ω' → XCode nL nR}
    (hg : Measurable g) :
    MeasurableSet {p : WordData nL nR × ProbabilityMeasure Ω' | IsEvoLaw κ p.1 ((p.2 : Measure Ω').map g)} := by
  set S : Set (WordData nL nR × Ω') := {q | g q.2 ∈ CRel κ q.1.1.1 q.1.1.2 q.1.2.1 q.1.2.2} with hS
  have hSm : MeasurableSet S :=
    (measurable_fst.prodMk (hg.comp measurable_snd)) (measurableSet_paramCRel (nL := nL) (nR := nR) κ)
  have h1 : MeasurableSet {p : WordData nL nR × ProbabilityMeasure Ω' |
      ((p.2 : Measure Ω').map g) (CRel κ p.1.1.1 p.1.1.2 p.1.2.1 p.1.2.2)ᶜ = 0} := by
    have e : {p : WordData nL nR × ProbabilityMeasure Ω' |
        ((p.2 : Measure Ω').map g) (CRel κ p.1.1.1 p.1.1.2 p.1.2.1 p.1.2.2)ᶜ = 0} =
        {p | (p.2 : Measure Ω') {y | (p.1, y) ∉ S} = 0} := by
      ext p
      simp only [mem_ofPred_eq]
      rw [Measure.map_apply hg (measurableSet_cRel _ _ _ _ _).compl]
      rfl
    rw [e]
    exact measurableSet_ae_mem_section hSm
  have h2 : MeasurableSet {p : WordData nL nR × ProbabilityMeasure Ω' |
      ((p.2 : Measure Ω').map g).map (fun x => x.1) = wienerCode} := by
    have e : ∀ p : WordData nL nR × ProbabilityMeasure Ω',
        ((p.2 : Measure Ω').map g).map (fun x => x.1) = (p.2 : Measure Ω').map (fun y => (g y).1) := fun p =>
      Measure.map_map measurable_fst hg
    simp_rw [e]
    have : IsProbabilityMeasure wienerCode := by
      rw [wienerCode]; infer_instance
    exact measurableSet_eq_measure ((measurable_coe_map (measurable_fst.comp hg)).comp measurable_snd)
      measurable_const fun p => inferInstance
  have h3 : ∀ n k n' k' : ℕ, MeasurableSet {p : WordData nL nR × ProbabilityMeasure Ω' |
      dyad n k ≤ dyad n' k' →
        ((p.2 : Measure Ω').map g).map (fun x => (codeObs (dyad n k) x, cb x (dyad n' k') - cb x (dyad n k))) =
          (((p.2 : Measure Ω').map g).map (codeObs (dyad n k))).prod
            (gaussianReal 0 (dyad n' k' - dyad n k))} := by
    intro n k n' k'
    by_cases hle : dyad n k ≤ dyad n' k'
    swap
    · simp only [hle, false_imp_iff, ofPred_true, MeasurableSet.univ]
    simp only [hle, true_imp_iff]
    have hΦ : Measurable fun x : XCode nL nR =>
        (codeObs (dyad n k) x, cb x (dyad n' k') - cb x (dyad n k)) :=
      (measurable_codeObs _).prodMk ((measurable_cb_at _).sub (measurable_cb_at _))
    have e1 : ∀ p : WordData nL nR × ProbabilityMeasure Ω',
        ((p.2 : Measure Ω').map g).map (fun x => (codeObs (dyad n k) x, cb x (dyad n' k') - cb x (dyad n k))) =
          (p.2 : Measure Ω').map ((fun x => (codeObs (dyad n k) x, cb x (dyad n' k') - cb x (dyad n k))) ∘ g) :=
      fun p => Measure.map_map hΦ hg
    have e2 : ∀ p : WordData nL nR × ProbabilityMeasure Ω',
        ((p.2 : Measure Ω').map g).map (codeObs (dyad n k)) = (p.2 : Measure Ω').map (codeObs (dyad n k) ∘ g) :=
      fun p => Measure.map_map (measurable_codeObs _) hg
    simp_rw [e1, e2]
    exact measurableSet_eq_measure ((measurable_coe_map (hΦ.comp hg)).comp measurable_snd)
      ((measurable_prod_const _).comp ((measurable_coe_map ((measurable_codeObs _).comp hg)).comp measurable_snd))
      fun p => inferInstance
  have e : {p : WordData nL nR × ProbabilityMeasure Ω' | IsEvoLaw κ p.1 ((p.2 : Measure Ω').map g)} =
      {p : WordData nL nR × ProbabilityMeasure Ω' |
        ((p.2 : Measure Ω').map g) (CRel κ p.1.1.1 p.1.1.2 p.1.2.1 p.1.2.2)ᶜ = 0} ∩
      {p | ((p.2 : Measure Ω').map g).map (fun x => x.1) = wienerCode} ∩
      ⋂ n, ⋂ k, ⋂ n', ⋂ k', {p : WordData nL nR × ProbabilityMeasure Ω' | dyad n k ≤ dyad n' k' →
        ((p.2 : Measure Ω').map g).map (fun x => (codeObs (dyad n k) x, cb x (dyad n' k') - cb x (dyad n k))) =
          (((p.2 : Measure Ω').map g).map (codeObs (dyad n k))).prod
            (gaussianReal 0 (dyad n' k' - dyad n k))} := by
    ext p
    simp only [IsEvoLaw, mem_ofPred_eq, mem_inter_iff, mem_iInter, and_assoc]
  rw [e]
  exact (h1.inter h2).inter (MeasurableSet.iInter fun n => MeasurableSet.iInter fun k =>
    MeasurableSet.iInter fun n' => MeasurableSet.iInter fun k' => h3 n k n' k')

/-! ### Independence passes to almost sure limits -/

/-- If `ν = P(A) · law(Y)` on `A`, as measures on `ℝ`: the restricted law of an independent variable. -/
theorem map_restrict_eq_smul_of_indep {Ω : Type*} {𝓜 : MeasurableSpace Ω} {mΩ : MeasurableSpace Ω}
    {P : Measure Ω} {Y : Ω → ℝ} (hY : Measurable Y)
    (hind : Indep (MeasurableSpace.comap Y inferInstance) 𝓜 P) {A : Set Ω} (hA : MeasurableSet[𝓜] A) :
    (P.restrict A).map Y = P A • P.map Y := by
  refine Measure.ext fun B hB => ?_
  rw [Measure.map_apply hY hB, Measure.restrict_apply (hY hB), Measure.smul_apply, Measure.map_apply hY hB,
    (Indep_iff _ _ _).1 hind _ _ ⟨B, hB, rfl⟩ hA, smul_eq_mul, mul_comm]

/-- **Independence of an almost sure limit.** If `X m → Y` almost surely and every `X m` is independent of `𝓜`,
then `Y` is independent of `𝓜` (characteristic functions on each event of `𝓜`). -/
theorem indep_comap_of_tendsto {Ω : Type*} {𝓜 : MeasurableSpace Ω} {mΩ : MeasurableSpace Ω} {P : Measure Ω}
    [IsProbabilityMeasure P] (h𝓜 : 𝓜 ≤ mΩ) {X : ℕ → Ω → ℝ} {Y : Ω → ℝ} (hX : ∀ m, Measurable (X m))
    (hY : Measurable Y) (hlim : ∀ᵐ ω ∂P, Tendsto (fun m => X m ω) atTop (𝓝 (Y ω)))
    (hind : ∀ m, Indep (MeasurableSpace.comap (X m) inferInstance) 𝓜 P) :
    Indep (MeasurableSpace.comap Y inferInstance) 𝓜 P := by
  rw [Indep_iff]
  rintro _ A ⟨B, hB, rfl⟩ hA
  have hAm : MeasurableSet A := h𝓜 _ hA
  have : IsFiniteMeasure (P A • P.map Y) := Measure.smul_finite _ (measure_ne_top P A)
  have key : (P.restrict A).map Y = P A • P.map Y := by
    refine Measure.ext_of_charFun (funext fun t => ?_)
    rw [charFun_apply_real, charFun_apply_real, integral_map hY.aemeasurable (by fun_prop),
      integral_smul_measure, integral_map hY.aemeasurable (by fun_prop)]
    have hc : Continuous fun x : ℝ => Complex.exp (t * x * Complex.I) := by fun_prop
    have hb : ∀ (μ : Measure Ω) (Z : Ω → ℝ), ∀ ω, ‖Complex.exp (t * Z ω * Complex.I)‖ ≤ 1 := by
      intro μ Z ω
      rw [Complex.norm_exp]
      simp
    have h1 : Tendsto (fun m => ∫ ω, Complex.exp (t * X m ω * Complex.I) ∂P.restrict A) atTop
        (𝓝 (∫ ω, Complex.exp (t * Y ω * Complex.I) ∂P.restrict A)) :=
      tendsto_integral_of_dominated_convergence (fun _ => 1)
        (fun m => (hc.measurable.comp (hX m)).aestronglyMeasurable) (integrable_const 1)
        (fun m => ae_of_all _ fun ω => hb P (X m) ω)
        (ae_restrict_of_ae (hlim.mono fun ω h => (hc.tendsto _).comp h))
    have h2 : Tendsto (fun m => ∫ ω, Complex.exp (t * X m ω * Complex.I) ∂P) atTop
        (𝓝 (∫ ω, Complex.exp (t * Y ω * Complex.I) ∂P)) :=
      tendsto_integral_of_dominated_convergence (fun _ => 1)
        (fun m => (hc.measurable.comp (hX m)).aestronglyMeasurable) (integrable_const 1)
        (fun m => ae_of_all _ fun ω => hb P (X m) ω) (hlim.mono fun ω h => (hc.tendsto _).comp h)
    have heq : ∀ m, ∫ ω, Complex.exp (t * X m ω * Complex.I) ∂P.restrict A =
        (P A).toReal • ∫ ω, Complex.exp (t * X m ω * Complex.I) ∂P := by
      intro m
      have hm := map_restrict_eq_smul_of_indep (hX m) (hind m) hA
      have := congrArg (fun μ : Measure ℝ => ∫ x : ℝ, Complex.exp (t * x * Complex.I) ∂μ) hm
      rwa [integral_map (hX m).aemeasurable (by fun_prop), integral_smul_measure,
        integral_map (hX m).aemeasurable (by fun_prop)] at this
    exact tendsto_nhds_unique (h1.congr heq) (h2.const_smul _)
  have := congrArg (fun μ => μ B) key
  rw [Measure.map_apply hY hB, Measure.restrict_apply (hY hB), Measure.smul_apply,
    Measure.map_apply hY hB, smul_eq_mul] at this
  rw [this, mul_comm]

/-! ### Sufficiency: an evolution law gives an integrated evolution on the code space -/

section Canon

variable {κ : ℝ} {w : WordData nL nR} {ν : Measure (XCode nL nR)}

theorem IsEvoLaw.ae_mem (h : IsEvoLaw κ w ν) : ∀ᵐ x ∂ν, x ∈ CRel κ w.1.1 w.1.2 w.2.1 w.2.2 :=
  measure_eq_zero_iff_ae_notMem.1 h.1 |>.mono fun _ hx => not_not.1 hx

theorem IsEvoLaw.ae_continuous_cb (h : IsEvoLaw κ w ν) : ∀ᵐ x ∂ν, Continuous fun t => cb x t :=
  h.ae_mem.mono fun _ hx => hx.1.1.continuous_b

open ProbabilityTheory.BrownianReal in
theorem IsEvoLaw.isPreBrownianReal [IsProbabilityMeasure ν] (h : IsEvoLaw κ w ν) :
    IsPreBrownianReal (fun t x => cb x t) ν := by
  refine ⟨fun I => ⟨(show Measurable (fun x : XCode nL nR => I.restrict fun t => cb x t) from
    measurable_pi_iff.2 fun i => measurable_cb_at _).aemeasurable, ?_⟩⟩
  set R : PCode → I → ℝ := fun c i => dec c i with hR
  have hRm : Measurable R := measurable_pi_iff.2 fun i => measurable_dec.comp (measurable_id.prodMk measurable_const)
  have e1 : (fun x : XCode nL nR => I.restrict fun t => cb x t) = R ∘ fun x => x.1 := rfl
  have hB := isBrownianReal_refBM
  rw [e1, ← Measure.map_map hRm measurable_fst, h.2.1, wienerCode,
    AEMeasurable.map_map_of_aemeasurable hRm.aemeasurable (aemeasurable_enc hB.toIsPreBrownianReal.aemeasurable)]
  have e2 : (R ∘ fun ω => enc fun t => refBM t ω) =ᵐ[LQGDimension.ExistAsm.stdP] fun ω => I.restrict (refBM · ω) := by
    filter_upwards [hB.cont] with ω hω
    funext i
    exact dec_enc hω.continuousWithinAt
  rw [Measure.map_congr e2]
  exact (hB.hasLaw I).map_eq

/-- Dyadic times above `t` at level `m`. -/
def dyadUp (m : ℕ) (t : ℝ≥0) : ℝ≥0 := dyad m (flr m t + 1)

theorem lt_dyadUp (m : ℕ) (t : ℝ≥0) : t < dyadUp m t := by
  have h := sub_lt_dyad_flr m t
  have hd : (dyad m (flr m t + 1) : ℝ) = dyad m (flr m t) + 1 / 2 ^ m := by unfold dyad; push_cast; ring
  have : (t : ℝ) < dyad m (flr m t + 1) := by rw [hd]; linarith
  exact_mod_cast this

theorem dyadUp_mono {s t : ℝ≥0} (hst : s ≤ t) (m : ℕ) : dyadUp m s ≤ dyadUp m t := by
  unfold dyadUp dyad flr
  gcongr

theorem tendsto_dyadUp (t : ℝ≥0) : Tendsto (fun m => dyadUp m t) atTop (𝓝 t) := by
  have h1 := tendsto_dyad_flr t
  have h2 : Tendsto (fun m : ℕ => (1 / 2 ^ m : ℝ≥0)) atTop (𝓝 0) := by
    simp_rw [one_div, ← inv_pow]
    exact tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
  have h3 := h1.add h2
  rw [add_zero] at h3
  refine h3.congr fun m => ?_
  unfold dyadUp dyad
  push_cast
  ring

theorem IsEvoLaw.indepFun_dyad [IsProbabilityMeasure ν] (h : IsEvoLaw κ w ν) {n k n' k' : ℕ}
    (hle : dyad n k ≤ dyad n' k') :
    Indep (MeasurableSpace.comap (fun x : XCode nL nR => cb x (dyad n' k') - cb x (dyad n k)) inferInstance)
      ((codeFilt (nL := nL) (nR := nR)) (dyad n k)) ν := by
  have hO := measurable_codeObs (nL := nL) (nR := nR) (dyad n k)
  have hI : Measurable fun x : XCode nL nR => cb x (dyad n' k') - cb x (dyad n k) :=
    (measurable_cb_at _).sub (measurable_cb_at _)
  have h3 := h.2.2 n k n' k' hle
  have hlaw : ν.map (fun x : XCode nL nR => cb x (dyad n' k') - cb x (dyad n k)) =
      gaussianReal 0 (dyad n' k' - dyad n k) := by
    have := congrArg (Measure.map Prod.snd) h3
    rw [Measure.map_map measurable_snd (hO.prodMk hI), Measure.map_snd_prod,
      Measure.map_apply hO MeasurableSet.univ, preimage_univ, measure_univ, one_smul] at this
    exact this
  have hind : IndepFun (codeObs (dyad n k)) (fun x : XCode nL nR => cb x (dyad n' k') - cb x (dyad n k)) ν := by
    rw [indepFun_iff_map_prod_eq_prod_map_map hO.aemeasurable hI.aemeasurable, hlaw]
    exact h3
  exact ((IndepFun_iff_Indep _ _ _).1 hind).symm

theorem IsEvoLaw.indep [IsProbabilityMeasure ν] (h : IsEvoLaw κ w ν) {s t : ℝ≥0} (hst : s ≤ t) :
    Indep (MeasurableSpace.comap (fun x : XCode nL nR => cb x t - cb x s) inferInstance)
      ((codeFilt (nL := nL) (nR := nR)) s) ν := by
  refine indep_comap_of_tendsto ((codeFilt (nL := nL) (nR := nR)).le s)
    (X := fun m x => cb x (dyadUp m t) - cb x (dyadUp m s))
    (fun m => (measurable_cb_at _).sub (measurable_cb_at _)) ((measurable_cb_at _).sub (measurable_cb_at _))
    ?_ fun m => ?_
  · filter_upwards [h.ae_continuous_cb] with x hx
    exact ((hx.tendsto t).comp (tendsto_dyadUp t)).sub ((hx.tendsto s).comp (tendsto_dyadUp s))
  · have := h.indepFun_dyad (n := m) (k := flr m s + 1) (n' := m) (k' := flr m t + 1) (dyadUp_mono hst m)
    exact indep_of_indep_of_le_right this ((codeFilt (nL := nL) (nR := nR)).mono (lt_dyadUp m s).le)

/-- **Sufficiency (S3).** Under an evolution law of the word `w`, the canonical processes on the code space form an
integrated `SLE_κ(ρ)` evolution for the code filtration. -/
theorem isIntegratedSLEEvolution_canon [IsProbabilityMeasure ν] (h : IsEvoLaw κ w ν) :
    IsIntegratedSLEEvolution κ w.1.1 w.1.2 w.2.1 w.2.2 ν codeFilt (fun t x => cw x t)
      (fun i t x => cvL x i t) (fun j t x => cvR x j t) (fun t x => cb x t) cζ :=
  ⟨⟨{ toIsPreBrownianReal := h.isPreBrownianReal, cont := h.ae_continuous_cb }, adapted_cb,
    fun _ _ hst => h.indep hst⟩, adaptedBefore_cw, adaptedBefore_cvL, adaptedBefore_cvR,
    h.ae_mem.mono fun _ hx => hx.1.2.2⟩

end Canon

/-! ### Necessity: the code law of an evolution is an evolution law -/

section Necessity

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {𝓖 : Filtration ℝ≥0 mΩ} {ζ : Ω → ℝ≥0∞}

theorem measurableSet_lt_zeta_of_adaptedBefore {X : ℝ≥0 → Ω → ℝ} (hX : AdaptedBefore 𝓖 ζ X) (t : ℝ≥0) :
    MeasurableSet[𝓖 t] {ω | (t : ℝ≥0∞) < ζ ω} := by
  simpa using hX t univ MeasurableSet.univ

theorem measurable_killedCode_at {X : ℝ≥0 → Ω → ℝ} (hX : AdaptedBefore 𝓖 ζ X) (x₀ : ℝ) {n k : ℕ}
    {t : ℝ≥0} (ht : dyad n k ≤ t) : Measurable[𝓖 t] fun ω => killedCode X x₀ ζ ω n k := by
  unfold killedCode
  by_cases h0 : dyad n k = 0
  · simp only [h0, ↓reduceIte]; exact @measurable_const _ _ _ (𝓖 t) _
  · simp only [h0, ↓reduceIte]
    have h := (Girsanov.measurable_killed hX (dyad n k)).mono (𝓖.mono ht) le_rfl
    exact h

theorem measurable_codeObs_codeOf {xL : Fin nL → ℝ} {xR : Fin nR → ℝ} {B' : ℝ≥0 → Ω → ℝ}
    {W : ℝ≥0 → Ω → ℝ} {VL : Fin nL → ℝ≥0 → Ω → ℝ} {VR : Fin nR → ℝ≥0 → Ω → ℝ}
    (hB' : ∀ t, Measurable[𝓖 t] (B' t)) (hW : AdaptedBefore 𝓖 ζ W) (hVL : ∀ i, AdaptedBefore 𝓖 ζ (VL i))
    (hVR : ∀ j, AdaptedBefore 𝓖 ζ (VR j)) (s : ℝ≥0) :
    Measurable[𝓖 s] fun ω => codeObs s (codeOf xL xR B' W VL VR ζ ω) := by
  set m := 𝓖 s
  refine Measurable.prodMk (m := m) (@measurable_pi_iff _ _ _ m _ _ |>.2 fun p => ?_)
    (Measurable.prodMk (m := m) (@measurable_pi_iff _ _ _ m _ _ |>.2 fun p => ?_) ?_)
  · by_cases h : dyad p.1 p.2 ≤ s
    · simp only [h, ↓reduceIte, obsD, codeOf]
      refine Measurable.prodMk (m := m) (((hB' _).mono (𝓖.mono h) le_rfl)) (Measurable.prodMk (m := m)
        (measurable_killedCode_at hW 0 h) (Measurable.prodMk (m := m) ?_ ?_))
      · exact @measurable_pi_iff _ _ _ m _ _ |>.2 fun i => measurable_killedCode_at (hVL i) _ h
      · exact @measurable_pi_iff _ _ _ m _ _ |>.2 fun j => measurable_killedCode_at (hVR j) _ h
    · simp only [h, ↓reduceIte]; exact @measurable_const _ _ _ m _
  · by_cases h : dyad p.1 p.2 ≤ s
    · simp only [h, true_and, codeOf, cζ]
      exact Measurable.ite (m := m) (𝓖.mono h _ (measurableSet_lt_zeta_of_adaptedBefore hW _))
        (@measurable_const _ _ _ m _) (@measurable_const _ _ _ m _)
    · simp only [h, false_and, ↓reduceIte]; exact @measurable_const _ _ _ m _
  · simp only [codeOf, cζ]
    exact Measurable.ite (m := m) (measurableSet_lt_zeta_of_adaptedBefore hW s)
      (@measurable_const _ _ _ m _) (@measurable_const _ _ _ m _)

/-- **Necessity (S3).** The code law of an integrated evolution (with a continuous version `B'` of its Brownian
motion that is a Brownian motion of the usual augmentation) is an evolution law of its word. -/
theorem isEvoLaw_map_codeOf {P : Measure Ω} [IsProbabilityMeasure P] {𝓕 : Filtration ℝ≥0 mΩ} {κ : ℝ}
    (hκ : 0 < κ) {xL : Fin nL → ℝ} {xR : Fin nR → ℝ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ}
    {W : ℝ≥0 → Ω → ℝ} {VL : Fin nL → ℝ≥0 → Ω → ℝ} {VR : Fin nR → ℝ≥0 → Ω → ℝ} {B : ℝ≥0 → Ω → ℝ}
    (hE : IsIntegratedSLEEvolution κ xL xR ρL ρR P 𝓕 W VL VR B ζ) {B' : ℝ≥0 → Ω → ℝ}
    (hB'm : ∀ t, Measurable (B' t)) (hB'c : ∀ ω, Continuous (B' · ω))
    (hB' : IsFilteredBrownianReal (usualAugmentation 𝓕 P) B' P) (hae : ∀ᵐ ω ∂P, ∀ t, B' t ω = B t ω) :
    IsEvoLaw κ ((xL, xR), (ρL, ρR)) (P.map (codeOf xL xR B' W VL VR ζ)) := by
  obtain ⟨-, hWa, hVLa, hVRa, -⟩ := id hE
  set c := codeOf xL xR B' W VL VR ζ with hcdef
  have hc : Measurable c := measurable_codeOf hB'm hWa hVLa hVRa
  set 𝓖 := usualAugmentation 𝓕 P
  have hle : 𝓕 ≤ 𝓖 := Ito.le_usualAugmentation 𝓕 P
  have hWa' : AdaptedBefore 𝓖 ζ W := fun t A hA => hle t _ (hWa t A hA)
  have hVLa' : ∀ i, AdaptedBefore 𝓖 ζ (VL i) := fun i t A hA => hle t _ (hVLa i t A hA)
  have hVRa' : ∀ j, AdaptedBefore 𝓖 ζ (VR j) := fun j t A hA => hle t _ (hVRa j t A hA)
  have hcb : ∀ ω r, cb (c ω) r = B' r ω := fun ω r => dec_enc (hB'c ω).continuousWithinAt
  refine ⟨?_, ?_, fun n k n' k' hst => ?_⟩
  · rw [Measure.map_apply hc (measurableSet_cRel _ _ _ _ _).compl]
    have := ae_codeOf_mem hκ hE hB'c hae
    exact measure_eq_zero_iff_ae_notMem.2 (this.mono fun ω h hω => hω h.1)
  · rw [Measure.map_map measurable_fst hc]
    exact map_enc_eq_wienerCode hB'.1.toIsPreBrownianReal
  · set s := dyad n k
    set t := dyad n' k'
    have hO : Measurable[𝓖 s] fun ω => codeObs s (c ω) :=
      measurable_codeObs_codeOf (fun r => hB'.2.1 r) hWa' hVLa' hVRa' s
    have hOm : Measurable fun ω => codeObs s (c ω) := hO.mono (𝓖.le s) le_rfl
    have hI : Measurable fun ω => B' t ω - B' s ω := (hB'm t).sub (hB'm s)
    have hind : IndepFun (fun ω => codeObs s (c ω)) (fun ω => B' t ω - B' s ω) P := by
      rw [IndepFun_iff_Indep]
      exact indep_of_indep_of_le_left (hB'.2.2 s t hst).symm hO.comap_le
    have hlaw : P.map (fun ω => B' t ω - B' s ω) = gaussianReal 0 (t - s) := by
      have h := (hB'.1.toIsPreBrownianReal.hasLaw_sub t s).map_eq
      rw [show (B' t - B' s) = fun ω => B' t ω - B' s ω from rfl] at h
      rw [h]
      congr 1
      apply NNReal.eq
      rw [coe_nndist, Real.dist_eq, NNReal.coe_sub hst]
      exact abs_of_nonneg (sub_nonneg.2 (NNReal.coe_le_coe.2 hst))
    have e1 : (P.map c).map (fun x => (codeObs s x, cb x t - cb x s)) =
        P.map fun ω => (codeObs s (c ω), B' t ω - B' s ω) := by
      rw [Measure.map_map (show Measurable fun x : XCode nL nR => (codeObs s x, cb x t - cb x s) from
        (measurable_codeObs s).prodMk ((measurable_cb_at t).sub (measurable_cb_at s))) hc]
      congr 1
      funext ω
      simp only [Function.comp_apply, hcb]
    rw [e1, Measure.map_map (measurable_codeObs s) hc, (indepFun_iff_map_prod_eq_prod_map_map hOm.aemeasurable
      hI.aemeasurable).1 hind, hlaw]
    rfl

end Necessity

end Param12

end Exist

end InteractingSLE
