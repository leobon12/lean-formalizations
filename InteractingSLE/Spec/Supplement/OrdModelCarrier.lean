/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.OrdModelCode
import InteractingSLE.Spec.Restart.RetLeafModelCtor

/-!
# The carrier of an A-stopped model and its good event

Packet PROVE-T15-ASTOP2. An A-stopped model (Theorem 1.5's leaf 3) lives on PROVE-RETPLUMB's canonical carrier
`RetCanonSpace` (word, field, driver, lifetime, closed trace) extended by the four chart end points of the A-set and
one more initial real coordinate (the seed of a recentred continuation, PROVE-T15-ORDDET4):
`OrdCanonSpace = RetCanonSpace × Ends × ℝ`. Its initial code is `ordCode s = codeEquiv (word, end points)`.

The pathwise facts that the A-stop announcement needs (`OrdAStop.exists_isAnnouncingSeq_aStop`) are pushed from the
source to the model law through one Borel event of the carrier, `ordGood κ θ a`: the trace generates the driver up to
the lifetime, the lifetime is positive and at most the threshold of the typed word, the trace stays at positive
distance from the A-set at positive times before the lifetime, and a finite lifetime is the threshold or a point of the
A-set (`measurableSet_ordGood`, through the countable rational form `forall_pos_iff_rat`).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Filter Topology MeasureTheory Metric
open scoped NNReal ENNReal NNRat

namespace InteractingSLE.RLC.OrdModel

open Restart Restart.RetAux79 Restart.RetLeaf Sec7.PocketTraversal Restart.FCDet Sec7.Coding

/-! ### The carrier and the code -/

/-- **The carrier of an A-stopped model**: the canonical retained coordinates, the four chart end points of the
A-set, and a seed. -/
abbrev OrdCanonSpace : Type := RetCanonSpace × Ends × ℝ

instance : StandardBorelSpace OrdCanonSpace := StandardBorelSpace.prod

/-- **The initial code** on the carrier: the word and the end points. -/
def ordCode (s : OrdCanonSpace) : ℝ := codeEquiv (RetCanonSpace.word s.1, s.2.1)

theorem measurable_ordCode : Measurable ordCode :=
  codeEquiv.measurable.comp ((RetCanonSpace.measurable_word.comp measurable_fst).prodMk
    (measurable_fst.comp measurable_snd))

theorem codeJ_ordCode (s : OrdCanonSpace) : codeJ (ordCode s) = aStopSet s.2.1 := codeJ_codeEquiv _ _

theorem codeWord_ordCode (s : OrdCanonSpace) : codeWord (ordCode s) = RetCanonSpace.word s.1 :=
  codeWord_codeEquiv _ _

/-- The seed coordinate on the carrier. -/
def ordSeed (s : OrdCanonSpace) : ℝ := s.2.2

theorem measurable_ordSeed : Measurable ordSeed := measurable_snd.comp measurable_snd

/-! ### Countable form of positivity on an open time interval -/

/-- Positivity of a continuous function at the positive times before `L`, as countably many rational conditions
(the proof of `RetLeaf.retCanonical_interior_iff`, for any continuous function). -/
theorem forall_pos_iff_rat {f : ℝ≥0 → ℝ} (hfc : Continuous f) (L : ℝ≥0∞) :
    (∀ t : ℝ≥0, 0 < t → (t : ℝ≥0∞) < L → 0 < f t) ↔
      ∀ a b : ℚ≥0, 0 < a → ((b : ℝ≥0) : ℝ≥0∞) < L → ∃ m : ℕ, ∀ r : ℚ≥0, a ≤ r → r ≤ b →
        1 / ((m : ℝ) + 1) ≤ f r := by
  constructor
  · intro h a b ha hb
    rcases le_or_gt a b with hab | hab
    · have hab' : (a : ℝ≥0) ≤ b := by exact_mod_cast hab
      obtain ⟨t₀, ht₀, hmin⟩ := isCompact_Icc.exists_isMinOn (nonempty_Icc.2 hab') hfc.continuousOn
      have ht₀pos : 0 < f t₀ := h t₀ (lt_of_lt_of_le (by exact_mod_cast ha) ht₀.1)
        (lt_of_le_of_lt (ENNReal.coe_le_coe.2 ht₀.2) hb)
      obtain ⟨m, hm⟩ := exists_nat_one_div_lt ht₀pos
      refine ⟨m, fun r har hrb => ?_⟩
      exact hm.le.trans (isMinOn_iff.1 hmin _ ⟨by exact_mod_cast har, by exact_mod_cast hrb⟩)
    · exact ⟨0, fun r har hrb => absurd (har.trans hrb) (not_le.2 hab)⟩
  · intro h t ht0 ht
    obtain ⟨a, ha0, hat⟩ := exists_nnrat_btwn ht0
    obtain ⟨b, htb, hb, -⟩ := exists_nnrat_gt_lt ht one_pos
    have ha0' : 0 < a := by exact_mod_cast ha0
    obtain ⟨m, hm⟩ := h a b ha0' hb
    have hlim : Tendsto (fun n => f (apxQ t n)) atTop (𝓝 (f t)) :=
      (hfc.tendsto t).comp (tendsto_apxQ t)
    have hev : ∀ᶠ n in atTop, 1 / ((m : ℝ) + 1) ≤ f (apxQ t n) := by
      have hIoo : Ioo (a : ℝ≥0) (b : ℝ≥0) ∈ 𝓝 t := Ioo_mem_nhds hat htb
      filter_upwards [tendsto_apxQ t hIoo] with n hn
      have hn' : ((apxQ t n : ℚ≥0) : ℝ≥0) ∈ Ioo (a : ℝ≥0) (b : ℝ≥0) := hn
      exact hm (apxQ t n) (by exact_mod_cast hn'.1.le) (by exact_mod_cast hn'.2.le)
    exact lt_of_lt_of_le (by positivity) (ge_of_tendsto hlim hev)

/-! ### The good event -/

/-- The fixed-type left positions on the carrier. -/
def ordXL (κ θ : ℝ) (a : ForceWordType) (s : OrdCanonSpace) : Fin a.nL → ℝ := retCanonicalXL κ θ a s.1

/-- The fixed-type right positions on the carrier. -/
def ordXR (κ θ : ℝ) (a : ForceWordType) (s : OrdCanonSpace) : Fin a.nR → ℝ := retCanonicalXR κ θ a s.1

/-- The driver on the carrier. -/
def ordDrv (t : ℝ≥0) (s : OrdCanonSpace) : ℝ := RetCanonSpace.driver t s.1

/-- The threshold of the typed word on the carrier. -/
def ordThr (κ θ : ℝ) (a : ForceWordType) : OrdCanonSpace → ℝ≥0∞ :=
  thr a.rhoL a.rhoR ordDrv (ordXL κ θ a) (ordXR κ θ a)

theorem measurable_ordXL (κ θ : ℝ) (a : ForceWordType) : Measurable (ordXL κ θ a) :=
  (measurable_typeXL κ θ a.nL a.nR a.rhoL a.rhoR).comp (RetCanonSpace.measurable_word.comp measurable_fst)

theorem measurable_ordXR (κ θ : ℝ) (a : ForceWordType) : Measurable (ordXR κ θ a) :=
  (measurable_typeXR κ θ a.nL a.nR a.rhoL a.rhoR).comp (RetCanonSpace.measurable_word.comp measurable_fst)

theorem continuous_ordDrv (s : OrdCanonSpace) : Continuous (ordDrv · s) := RetCanonSpace.continuous_driver s.1

theorem measurable_ordThr (κ θ : ℝ) (a : ForceWordType) : Measurable (ordThr κ θ a) := by
  let 𝓒 : Filtration ℝ≥0 (inferInstance : MeasurableSpace OrdCanonSpace) :=
    Filtration.const ℝ≥0 inferInstance le_rfl
  exact measurable_thr (𝓗 := 𝓒) continuous_ordDrv
    (fun t => ((RetCanonSpace.measurable_driver t).comp measurable_fst).stronglyMeasurable)
    (measurable_ordXL κ θ a) (measurable_ordXR κ θ a)

/-- **The good event of an A-stopped model** on the carrier (distance form of the A-set conditions). -/
def ordGood (κ θ : ℝ) (a : ForceWordType) : Set OrdCanonSpace :=
  {s | IsGeneratingTrace (ordDrv · s) (RetCanonSpace.life s.1) (RetCanonSpace.trace s.1) ∧
    0 < RetCanonSpace.life s.1 ∧ RetCanonSpace.life s.1 ≤ ordThr κ θ a s ∧
    (∀ t : ℝ≥0, 0 < t → (t : ℝ≥0∞) < RetCanonSpace.life s.1 →
      0 < infDist (RetCanonSpace.trace s.1 t) (aStopSet s.2.1)) ∧
    (RetCanonSpace.life s.1 ≠ ⊤ → RetCanonSpace.life s.1 = ordThr κ θ a s ∨
      infDist (RetCanonSpace.trace s.1 (RetCanonSpace.life s.1).toNNReal) (aStopSet s.2.1) = 0)}

/-- **The good event is Borel.** -/
theorem measurableSet_ordGood (κ θ : ℝ) (a : ForceWordType) : MeasurableSet (ordGood κ θ a) := by
  have hlife : Measurable fun s : OrdCanonSpace => RetCanonSpace.life s.1 :=
    RetCanonSpace.measurable_life.comp measurable_fst
  have hgen : MeasurableSet {s : OrdCanonSpace | IsGeneratingTrace (ordDrv · s) (RetCanonSpace.life s.1)
      (RetCanonSpace.trace s.1)} :=
    measurable_fst retCanonicalGeneratingTraceBorel
  have hd : ∀ r : ℝ≥0, Measurable fun s : OrdCanonSpace =>
      infDist (RetCanonSpace.trace s.1 r) (aStopSet s.2.1) := fun r => by
    have hq : Measurable fun s : OrdCanonSpace => (RetCanonSpace.trace s.1 r, s.2.1) :=
      ((RetCanonSpace.measurable_trace r).comp measurable_fst).prodMk (measurable_fst.comp measurable_snd)
    have h := continuous_infDist_aStopSet.measurable.comp hq
    exact h
  have hoff : MeasurableSet {s : OrdCanonSpace | ∀ t : ℝ≥0, 0 < t → (t : ℝ≥0∞) < RetCanonSpace.life s.1 →
      0 < infDist (RetCanonSpace.trace s.1 t) (aStopSet s.2.1)} := by
    have e : {s : OrdCanonSpace | ∀ t : ℝ≥0, 0 < t → (t : ℝ≥0∞) < RetCanonSpace.life s.1 →
        0 < infDist (RetCanonSpace.trace s.1 t) (aStopSet s.2.1)} =
        {s | ∀ a b : ℚ≥0, 0 < a → ((b : ℝ≥0) : ℝ≥0∞) < RetCanonSpace.life s.1 → ∃ m : ℕ, ∀ r : ℚ≥0, a ≤ r →
          r ≤ b → 1 / ((m : ℝ) + 1) ≤ infDist (RetCanonSpace.trace s.1 r) (aStopSet s.2.1)} := by
      ext s
      exact forall_pos_iff_rat ((continuous_infDist_pt _).comp (RetCanonSpace.continuous_trace s.1)) _
    rw [e]
    refine measurableSet_setOfPred.2 (Measurable.forall fun a => Measurable.forall fun b =>
      measurable_imp_const fun _ => ?_)
    refine (measurableSet_setOfPred.1 (measurableSet_lt measurable_const hlife)).imp
      (Measurable.exists fun m => Measurable.forall fun r => measurable_imp_const fun _ =>
        measurable_imp_const fun _ => ?_)
    exact measurableSet_setOfPred.1 (measurableSet_le measurable_const (hd _))
  have hend : MeasurableSet {s : OrdCanonSpace | RetCanonSpace.life s.1 ≠ ⊤ →
      RetCanonSpace.life s.1 = ordThr κ θ a s ∨
        infDist (RetCanonSpace.trace s.1 (RetCanonSpace.life s.1).toNNReal) (aStopSet s.2.1) = 0} := by
    have hj : Measurable fun s : OrdCanonSpace =>
        RetCanonSpace.trace s.1 (RetCanonSpace.life s.1).toNNReal := by
      have hu := measurable_uncurry_of_continuous_of_measurable
        (u := fun (t : ℝ≥0) (s : RetCanonSpace) => RetCanonSpace.trace s t)
        (fun s => RetCanonSpace.continuous_trace s) (fun t => RetCanonSpace.measurable_trace t)
      exact (hu.comp ((ENNReal.measurable_toNNReal.comp RetCanonSpace.measurable_life).prodMk
        measurable_id)).comp measurable_fst
    have hk : Measurable fun s : OrdCanonSpace =>
        infDist (RetCanonSpace.trace s.1 (RetCanonSpace.life s.1).toNNReal) (aStopSet s.2.1) := by
      have hq : Measurable fun s : OrdCanonSpace =>
          (RetCanonSpace.trace s.1 (RetCanonSpace.life s.1).toNNReal, s.2.1) :=
        hj.prodMk (measurable_fst.comp measurable_snd)
      have h := continuous_infDist_aStopSet.measurable.comp hq
      exact h
    exact measurableSet_setOfPred.2 ((measurableSet_setOfPred.1 (measurableSet_eq_fun hlife
      measurable_const)).not.imp ((measurableSet_setOfPred.1 (measurableSet_eq_fun hlife
        (measurable_ordThr κ θ a))).or (measurableSet_setOfPred.1 (measurableSet_eq_fun hk measurable_const))))
  exact hgen.inter ((measurableSet_lt measurable_const hlife).inter
    ((measurableSet_le hlife (measurable_ordThr κ θ a)).inter (hoff.inter hend)))

end InteractingSLE.RLC.OrdModel
