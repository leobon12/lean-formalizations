/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec5.Prop49QExitRestart
import InteractingSLE.Spec.Sec5.GlueCondHit

/-!
# Aux. lemma 22's left strip end as a Borel event of solution codes

Packet PROVE-GLUECOND9. To restart the killed image word of Proposition 4.9's direction (`Prop49QExitRestart`), the
conclusion of Aux. lemma 22 for a left span (`(−∞, e)`, `e` the last left mark) must be a Borel event of solution
codes. Its natural form, "for some finite `S > 0` the trace generates the chain before `S`, avoids `ℝ ∖ {0}` before
`S` and converges to a real point `y < e` at `S`", quantifies over the time `S` and the point `y`. Both are unique on
canonical solution codes, so the event is the injective projection of a Borel set of (code, `S`, `y`) and is Borel by
Lusin–Souslin (the code space is standard Borel).

* `TrQ w S`, `AvoidQ w S`, `LimQ w S y`: the countable forms (through PROVE-SEC7's measurable trace evaluation
  `LP.traceAt` and its trace set `traceSet`) of "a generating trace on every `[0, r]`, `r < S`", "the trace avoids every
  far real set `{x : |x| ≥ 1/(n + 1)}` (PROVE-GLUECOND3's `farReal`) with a uniform margin on `[0, r]`", and "the trace
  converges to `y` at `S`";
* `EndCond e w ζ S y`, `LeftEnd e w ζ = ∃ S y, EndCond e w ζ S y`;
* `endCode a ρL ρR eOf`: the codes satisfying `LeftEnd` with the bound `e = eOf (start)`; **`measurableSet_endCode`**;
  `mem_endCode_iff` (the coding on canonical codes from a start); `leftEnd_congr` (it only sees the driver before
  the horizon).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter Topology Metric
open scoped NNReal ENNReal

namespace InteractingSLE.Sec5.Prop49Exit

open Sec2 Sec2.Assembly Sec2.Restart Sec7.RandRestart

variable {nL nR : ℕ}

/-! ### The countable conditions -/

section Cond

/-- A generating trace on every `[0, r]`, `r < S` rational (through `traceSet`). -/
def TrQ (w : ℝ≥0 → ℝ) (S : ℝ≥0) : Prop :=
  ∀ r : ℚ≥0, (r : ℝ≥0) < S → (w, (((r : ℝ≥0)) : ℝ≥0∞)) ∈ traceSet

/-- The trace evaluations avoid every far real set with a uniform margin on `[0, r]`, `r < S` rational. -/
def AvoidQ (w : ℝ≥0 → ℝ) (S : ℝ≥0) : Prop :=
  ∀ n : ℕ, ∀ r : ℚ≥0, (r : ℝ≥0) < S → ∃ m : ℕ, ∀ p : ℚ≥0, p ≤ r →
    1 / ((m : ℝ) + 1) ≤ infDist (LP.traceAt p w) (GlueCond.farReal n)

/-- The trace evaluations at rational times converge to `y` at `S` from the left. -/
def LimQ (w : ℝ≥0 → ℝ) (S : ℝ≥0) (y : ℝ) : Prop :=
  ∀ k : ℕ, ∃ m : ℕ, ∀ p : ℚ≥0, (S : ℝ) - 1 / ((m : ℝ) + 1) < ((p : ℝ≥0) : ℝ) → (p : ℝ≥0) < S →
    ‖LP.traceAt p w - (y : ℂ)‖ ≤ 1 / ((k : ℝ) + 1)

/-- **The left strip end at `S`, `y`** with the bound `e`: `0 < S ≤ ζ`, `y < min 0 e`, and the three countable
conditions. -/
def EndCond (e : ℝ) (w : ℝ≥0 → ℝ) (ζ : ℝ≥0∞) (S : ℝ≥0) (y : ℝ) : Prop :=
  0 < S ∧ (S : ℝ≥0∞) ≤ ζ ∧ y < 0 ∧ y < e ∧ TrQ w S ∧ AvoidQ w S ∧ LimQ w S y

/-- **The left strip end** (Aux. lemma 22's conclusion for the span `(−∞, e)`). -/
def LeftEnd (e : ℝ) (w : ℝ≥0 → ℝ) (ζ : ℝ≥0∞) : Prop := ∃ (S : ℝ≥0) (y : ℝ), EndCond e w ζ S y

theorem finCond_congr {w w' : ℝ≥0 → ℝ} {r : ℝ≥0∞} (hww' : ∀ t : ℝ≥0, (t : ℝ≥0∞) < r → w t = w' t)
    (h : FinCond w r) : FinCond w' r := by
  have htr : ∀ p : ℚ≥0, ((p : ℝ≥0) : ℝ≥0∞) < r → LP.traceAt p w = LP.traceAt p w' := fun p hp =>
    LP.traceAt_congr fun s hs => hww' s (lt_of_le_of_lt (by exact_mod_cast hs) hp)
  have hhull : ∀ q : ℚ≥0, ((q : ℝ≥0) : ℝ≥0∞) < r → hullQ q w = hullQ q w' := fun q hq => by
    have : frzQ q w = frzQ q w' := by
      funext p
      simp only [frzQ]
      rw [LP.freezeAt_congr fun s hs => hww' s (lt_of_le_of_lt (by exact_mod_cast hs) hq)]
    simp only [hullQ, this]
  obtain ⟨h1, h2⟩ := h
  refine ⟨fun m => ?_, fun q hq => ?_⟩
  · obtain ⟨k, hk⟩ := h1 m
    exact ⟨k, fun p p' hp hp' hd => by rw [← htr p hp, ← htr p' hp']; exact hk p p' hp hp' hd⟩
  · obtain ⟨h2a, h2b⟩ := h2 q hq
    have hpq : ∀ p : ℚ≥0, p ≤ q → ((p : ℝ≥0) : ℝ≥0∞) < r := fun p hp =>
      lt_of_le_of_lt (by exact_mod_cast hp) hq
    refine ⟨fun p hp hpH => ?_, fun ε c hε hc hfar => ?_⟩
    · rw [← hhull q hq, ← htr p (hpq p hp)]
      exact h2a p hp (by rw [htr p (hpq p hp)]; exact hpH)
    · rw [← hhull q hq]
      exact h2b ε c hε hc fun p hp => by rw [htr p (hpq p hp)]; exact hfar p hp

/-- Membership of a finite horizon in `traceSet` only sees the driver before the horizon. -/
theorem mem_traceSet_congr {w w' : ℝ≥0 → ℝ} {r : ℝ≥0} (hww' : ∀ t : ℝ≥0, t < r → w t = w' t)
    (h : (w, (r : ℝ≥0∞)) ∈ traceSet) : (w', (r : ℝ≥0∞)) ∈ traceSet := by
  rcases h with ⟨htop, -⟩ | ⟨hne, hfin⟩
  · exact absurd htop ENNReal.coe_ne_top
  · have hfin' : FinCond w (r : ℝ≥0∞) := hfin
    exact Or.inr ⟨hne, finCond_congr (r := (r : ℝ≥0∞))
      (fun t (ht : (t : ℝ≥0∞) < (r : ℝ≥0∞)) => hww' t (by exact_mod_cast ht)) hfin'⟩

/-- **The left strip end only sees the driver before the horizon.** -/
theorem leftEnd_congr {e : ℝ} (w w' : ℝ≥0 → ℝ) (τ : ℝ≥0∞) (hww' : ∀ t : ℝ≥0, (t : ℝ≥0∞) < τ → w t = w' t)
    (h : LeftEnd e w τ) : LeftEnd e w' τ := by
  obtain ⟨S, y, hS0, hSτ, hy0, hye, htr, hav, hlim⟩ := h
  have hlt : ∀ t : ℝ≥0, t < S → w t = w' t := fun t ht =>
    hww' t (lt_of_lt_of_le (by exact_mod_cast ht) hSτ)
  have hta : ∀ p : ℝ≥0, p < S → LP.traceAt p w = LP.traceAt p w' := fun p hp =>
    LP.traceAt_congr fun s hs => hlt s (lt_of_le_of_lt hs hp)
  refine ⟨S, y, hS0, hSτ, hy0, hye, fun r hr => mem_traceSet_congr (fun t ht => hlt t (ht.trans hr)) (htr r hr),
    fun n r hr => ?_, fun k => ?_⟩
  · obtain ⟨m, hm⟩ := hav n r hr
    exact ⟨m, fun p hp => by rw [← hta p (lt_of_le_of_lt (by exact_mod_cast hp) hr)]; exact hm p hp⟩
  · obtain ⟨m, hm⟩ := hlim k
    exact ⟨m, fun p hp hpS => by rw [← hta p hpS]; exact hm p hp hpS⟩

end Cond

/-! ### Measurability -/

section Meas

/-- The joint condition on (code, `S`, `y`) behind `endCode`. -/
def EndSet (a : ℝ) (ρL : Fin nL → ℝ) (ρR : Fin nR → ℝ) (eOf : (Fin nL → ℝ) × (Fin nR → ℝ) → ℝ) :
    Set (XCode nL nR × (ℝ≥0 × ℝ)) :=
  {p | p.1 ∈ CRelF a ρL ρR ∧ EndCond (eOf (startOf p.1)) (cw p.1) (cζ p.1) p.2.1 p.2.2}

/-- **The codes with a left strip end** (bound `eOf` of the start), among the canonical solution codes. -/
def endCode (a : ℝ) (ρL : Fin nL → ℝ) (ρR : Fin nR → ℝ) (eOf : (Fin nL → ℝ) × (Fin nR → ℝ) → ℝ) :
    Set (XCode nL nR) :=
  Prod.fst '' EndSet a ρL ρR eOf

theorem measurableSet_endSet (a : ℝ) (ρL : Fin nL → ℝ) (ρR : Fin nR → ℝ)
    {eOf : (Fin nL → ℝ) × (Fin nR → ℝ) → ℝ} (he : Measurable eOf) :
    MeasurableSet (EndSet a ρL ρR eOf) := by
  have hx : Measurable fun p : XCode nL nR × (ℝ≥0 × ℝ) => p.1 := measurable_fst
  have hS : Measurable fun p : XCode nL nR × (ℝ≥0 × ℝ) => p.2.1 := measurable_fst.comp measurable_snd
  have hy : Measurable fun p : XCode nL nR × (ℝ≥0 × ℝ) => p.2.2 := measurable_snd.comp measurable_snd
  have hw : Measurable fun p : XCode nL nR × (ℝ≥0 × ℝ) => cw p.1 := Exist.measurable_cw.comp hx
  have htr : ∀ s : ℝ≥0, Measurable fun p : XCode nL nR × (ℝ≥0 × ℝ) => LP.traceAt s (cw p.1) := fun s =>
    (LP.measurable_traceAt s).comp hw
  have hlt : ∀ r : ℝ≥0, Measurable fun p : XCode nL nR × (ℝ≥0 × ℝ) => r < p.2.1 := fun r =>
    measurableSet_setOfPred.1 (measurableSet_lt measurable_const hS)
  refine measurableSet_setOfPred.2 (Measurable.and ?_ ?_)
  · exact measurableSet_setOfPred.1 ((measurableSet_cRelF a ρL ρR).preimage hx)
  refine Measurable.and (measurableSet_setOfPred.1 (measurableSet_lt measurable_const hS)) ?_
  refine Measurable.and (measurableSet_setOfPred.1 (measurableSet_le (measurable_coe_nnreal_ennreal.comp hS)
    (measurable_cζ.comp hx))) ?_
  refine Measurable.and (measurableSet_setOfPred.1 (measurableSet_lt hy measurable_const)) ?_
  refine Measurable.and (measurableSet_setOfPred.1 (measurableSet_lt hy
    (he.comp (measurable_startOf.comp hx)))) ?_
  refine Measurable.and ?_ (Measurable.and ?_ ?_)
  · refine Measurable.forall fun r => (hlt _).imp ?_
    exact measurableSet_setOfPred.1 ((hw.prodMk measurable_const) measurableSet_traceSet)
  · refine Measurable.forall fun n => Measurable.forall fun r => (hlt _).imp ?_
    refine Measurable.exists fun m => Measurable.forall fun p => Measurable.imp measurable_const ?_
    exact measurableSet_setOfPred.1 (measurableSet_le measurable_const
      ((continuous_infDist_pt (GlueCond.farReal n)).measurable.comp (htr _)))
  · refine Measurable.forall fun k => Measurable.exists fun m => Measurable.forall fun p => ?_
    refine Measurable.imp ?_ ((hlt _).imp ?_)
    · exact measurableSet_setOfPred.1 (measurableSet_lt
        ((measurable_coe_nnreal_real.comp hS).sub measurable_const) measurable_const)
    · exact measurableSet_setOfPred.1 (measurableSet_le
        (((htr _).sub (Complex.measurable_ofReal.comp hy)).norm) measurable_const)

end Meas

/-! ### Uniqueness of the end time and point on canonical codes -/

section Unique

/-- A nonnegative rational strictly between two reals `0 ≤ a < b` (as `Sec7.Lemma71L.exists_nnrat_btwn`, whose file
is outside this import closure). -/
theorem exists_nnrat_btwn' {a b : ℝ} (ha : 0 ≤ a) (hab : a < b) :
    ∃ q : ℚ≥0, a < ((q : ℝ≥0) : ℝ) ∧ ((q : ℝ≥0) : ℝ) < b := by
  obtain ⟨q, hq1, hq2⟩ := exists_rat_btwn hab
  have hq0 : (0 : ℚ) ≤ q := by exact_mod_cast (ha.trans hq1.le)
  have hq'r : (((q.toNNRat : ℚ≥0) : ℝ≥0) : ℝ) = q := by
    have : (((q.toNNRat : ℚ≥0) : ℝ≥0) : ℝ) = ((q.toNNRat : ℚ) : ℝ) := rfl
    rw [this, Rat.coe_toNNRat q hq0]
  exact ⟨q.toNNRat, by rw [hq'r]; exact hq1, by rw [hq'r]; exact hq2⟩

variable {w : ℝ≥0 → ℝ} {ζ : ℝ≥0∞}

/-- **A generating trace on `[0, r]` from `TrQ`**, for a driver continuous before its lifetime. -/
theorem exists_trace_of_trQ (hw : ContinuousOn w {t | (t : ℝ≥0∞) < ζ}) (hw0 : w 0 = 0) {S : ℝ≥0}
    (hSζ : (S : ℝ≥0∞) ≤ ζ) (h : TrQ w S) {r : ℚ≥0} (hr : (r : ℝ≥0) < S) :
    ∃ η : ℝ≥0 → ℂ, IsGeneratingTrace w ((r : ℝ≥0) : ℝ≥0∞) η := by
  have hrζ : (((r : ℝ≥0)) : ℝ≥0∞) < ζ := lt_of_lt_of_le (by exact_mod_cast hr) hSζ
  have hwr : ContinuousOn w {t | (t : ℝ≥0∞) < ((r : ℝ≥0) : ℝ≥0∞)} :=
    hw.mono fun t ht => lt_trans ht hrζ
  have hlim : 0 < (((r : ℝ≥0)) : ℝ≥0∞) → (((r : ℝ≥0)) : ℝ≥0∞) < ⊤ →
      ∃ w₀ : ℝ, Tendsto w (𝓝[<] (((r : ℝ≥0)) : ℝ≥0∞).toNNReal) (𝓝 w₀) := fun _ _ => by
    refine ⟨w r, ?_⟩
    rw [ENNReal.toNNReal_coe]
    have hopen : IsOpen {t : ℝ≥0 | (t : ℝ≥0∞) < ζ} :=
      isOpen_lt ENNReal.continuous_coe continuous_const
    exact ((hw.continuousAt (hopen.mem_nhds hrζ)).tendsto).mono_left nhdsWithin_le_nhds
  obtain ⟨η, hη, -⟩ := (mem_traceSet_iff hwr hw0 hlim).1 (h r hr)
  exact ⟨η, hη⟩

/-- On `[0, r)` the measurable trace evaluation is the generating trace. -/
theorem traceAt_eq_of_trace {r : ℝ≥0} {η : ℝ≥0 → ℂ} (hη : IsGeneratingTrace w (r : ℝ≥0∞) η)
    (hw : ContinuousOn w {t | (t : ℝ≥0∞) < ζ}) (hw0 : w 0 = 0) (hrζ : (r : ℝ≥0∞) ≤ ζ) {p : ℝ≥0}
    (hp : p < r) : LP.traceAt p w = η p :=
  LP.traceAt_eq_of_isGeneratingTrace hη (hw.mono fun t ht => lt_of_lt_of_le ht hrζ) hw0
    (by exact_mod_cast hp)

/-- **The end point is the value of the trace at the end time**: if the trace on `[0, r]`, `S ≤ r`, continues the
rational evaluations, `LimQ w S y` forces `η S = y`. -/
theorem eq_of_limQ {S r : ℝ≥0} (hS : 0 < S) (hSr : S ≤ r) {η : ℝ≥0 → ℂ}
    (hηc : ContinuousOn η (Icc 0 r)) (hη : ∀ p : ℝ≥0, p < S → LP.traceAt p w = η p) {y : ℝ}
    (hlim : LimQ w S y) : η S = y := by
  -- rational times `p_k ↑ S`
  have hseq : ∀ k : ℕ, ∃ p : ℚ≥0, (S : ℝ) - 1 / ((k : ℝ) + 1) < ((p : ℝ≥0) : ℝ) ∧ ((p : ℝ≥0) : ℝ) < S ∧
      ‖LP.traceAt p w - (y : ℂ)‖ ≤ 1 / ((k : ℝ) + 1) := by
    intro k
    obtain ⟨m, hm⟩ := hlim k
    have hlo : max 0 (max ((S : ℝ) - 1 / ((k : ℝ) + 1)) ((S : ℝ) - 1 / ((m : ℝ) + 1))) < S := by
      have h1 : (0 : ℝ) < 1 / ((k : ℝ) + 1) := by positivity
      have h2 : (0 : ℝ) < 1 / ((m : ℝ) + 1) := by positivity
      exact max_lt (by exact_mod_cast hS) (max_lt (by linarith) (by linarith))
    obtain ⟨p, hp1, hp2⟩ := exists_nnrat_btwn' (le_max_left _ _) hlo
    have hpk : (S : ℝ) - 1 / ((k : ℝ) + 1) < ((p : ℝ≥0) : ℝ) :=
      lt_of_le_of_lt ((le_max_left _ _).trans (le_max_right _ _)) hp1
    have hpm : (S : ℝ) - 1 / ((m : ℝ) + 1) < ((p : ℝ≥0) : ℝ) :=
      lt_of_le_of_lt ((le_max_right _ _).trans (le_max_right _ _)) hp1
    exact ⟨p, hpk, hp2, hm p hpm (by exact_mod_cast hp2)⟩
  choose p hp1 hp2 hp3 using hseq
  have hpS : Tendsto (fun k => ((p k : ℚ≥0) : ℝ≥0)) atTop (𝓝 S) := by
    rw [← NNReal.tendsto_coe]
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le (g := fun k : ℕ => (S : ℝ) - 1 / ((k : ℝ) + 1))
      (h := fun _ => (S : ℝ)) ?_ tendsto_const_nhds (fun k => (hp1 k).le) (fun k => (hp2 k).le)
    simpa using tendsto_const_nhds.sub (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
  have hpI : ∀ k, ((p k : ℚ≥0) : ℝ≥0) ∈ Icc 0 r := fun k =>
    ⟨zero_le, (show ((p k : ℚ≥0) : ℝ≥0) ≤ S from by exact_mod_cast (hp2 k).le).trans hSr⟩
  have hc : Tendsto (fun k => η ((p k : ℚ≥0) : ℝ≥0)) atTop (𝓝 (η S)) :=
    (hηc S ⟨zero_le, hSr⟩).tendsto.comp (tendsto_nhdsWithin_iff.2 ⟨hpS, Eventually.of_forall hpI⟩)
  have hy : Tendsto (fun k => η ((p k : ℚ≥0) : ℝ≥0)) atTop (𝓝 (y : ℂ)) := by
    rw [tendsto_iff_norm_sub_tendsto_zero]
    refine squeeze_zero (fun _ => norm_nonneg _) (fun k => ?_) tendsto_one_div_add_atTop_nhds_zero_nat
    rw [← hη _ (by exact_mod_cast hp2 k)]
    exact hp3 k
  exact tendsto_nhds_unique hc hy

/-- **The trace avoids the far real sets before `S`**: from `AvoidQ`, a trace on `[0, r]`, `r < S` rational, that
continues the rational evaluations stays off `ℝ \ {0}` on `[0, u]` for every `u < r'`, `r' ≤ r` rational with
`AvoidQ` at `r'` … stated at one time `u ≤ r'` approached by rationals `≤ r'`. -/
theorem notMem_farReal_of_avoidQ {S r : ℝ≥0} {r' : ℚ≥0} (hr' : (r' : ℝ≥0) < S) {η : ℝ≥0 → ℂ}
    (hηc : ContinuousOn η (Icc 0 r)) (hrr : (r' : ℝ≥0) ≤ r)
    (hη : ∀ p : ℚ≥0, p ≤ r' → LP.traceAt p w = η p) (havoid : AvoidQ w S) (n : ℕ) {u : ℝ≥0}
    (hu0 : 0 < u) (hu : u ≤ r') : η u ∉ GlueCond.farReal n := by
  obtain ⟨m, hm⟩ := havoid n r' hr'
  -- rational times `p_k ↑ u` in `(0, u)`
  have hseq : ∀ k : ℕ, ∃ p : ℚ≥0, (u : ℝ) - 1 / ((k : ℝ) + 1) < ((p : ℝ≥0) : ℝ) ∧ ((p : ℝ≥0) : ℝ) < u := by
    intro k
    have hlo : max 0 ((u : ℝ) - 1 / ((k : ℝ) + 1)) < u := by
      refine max_lt (by exact_mod_cast hu0) ?_
      have : (0 : ℝ) < 1 / ((k : ℝ) + 1) := by positivity
      linarith
    obtain ⟨p, hp1, hp2⟩ := exists_nnrat_btwn' (le_max_left _ _) hlo
    exact ⟨p, lt_of_le_of_lt (le_max_right _ _) hp1, hp2⟩
  choose p hp1 hp2 using hseq
  have hpu : Tendsto (fun k => ((p k : ℚ≥0) : ℝ≥0)) atTop (𝓝 u) := by
    rw [← NNReal.tendsto_coe]
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le (g := fun k : ℕ => (u : ℝ) - 1 / ((k : ℝ) + 1))
      (h := fun _ => (u : ℝ)) ?_ tendsto_const_nhds (fun k => (hp1 k).le) (fun k => (hp2 k).le)
    simpa using tendsto_const_nhds.sub (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
  have hpr' : ∀ k, p k ≤ r' := fun k => by
    have : ((p k : ℚ≥0) : ℝ≥0) ≤ (r' : ℝ≥0) := (show ((p k : ℚ≥0) : ℝ≥0) ≤ u from by
      exact_mod_cast (hp2 k).le).trans hu
    exact_mod_cast this
  have hpI : ∀ k, ((p k : ℚ≥0) : ℝ≥0) ∈ Icc 0 r := fun k =>
    ⟨zero_le, (show ((p k : ℚ≥0) : ℝ≥0) ≤ (r' : ℝ≥0) from by exact_mod_cast hpr' k).trans hrr⟩
  have hc : Tendsto (fun k => η ((p k : ℚ≥0) : ℝ≥0)) atTop (𝓝 (η u)) :=
    (hηc u ⟨zero_le, hu.trans hrr⟩).tendsto.comp (tendsto_nhdsWithin_iff.2 ⟨hpu, Eventually.of_forall hpI⟩)
  have hle : 1 / ((m : ℝ) + 1) ≤ infDist (η u) (GlueCond.farReal n) :=
    ge_of_tendsto (((continuous_infDist_pt (GlueCond.farReal n)).tendsto _).comp hc)
      (Eventually.of_forall fun k => by rw [Function.comp_apply, ← hη _ (hpr' k)]; exact hm _ (hpr' k))
  intro hmem
  have h0 : infDist (η u) (GlueCond.farReal n) = 0 := infDist_zero_of_mem hmem
  have : (0 : ℝ) < 1 / ((m : ℝ) + 1) := by positivity
  linarith

/-- A nonzero real point lies in some far real set. -/
theorem exists_mem_farReal {y : ℝ} (hy : y ≠ 0) : ∃ n : ℕ, ((y : ℂ)) ∈ GlueCond.farReal n := by
  obtain ⟨n, hn⟩ := exists_nat_one_div_lt (abs_pos.2 hy)
  exact ⟨n, by simp, by simpa using hn.le⟩

/-- **The end time is unique** on a driver continuous before its lifetime. -/
theorem not_endCond_of_lt {e : ℝ} (hw : ContinuousOn w {t | (t : ℝ≥0∞) < ζ}) (hw0 : w 0 = 0) {S₁ S₂ : ℝ≥0}
    {y₁ y₂ : ℝ} (h₁ : EndCond e w ζ S₁ y₁) (h₂ : EndCond e w ζ S₂ y₂) (hlt : S₁ < S₂) : False := by
  obtain ⟨hS₁, -, hy₁, -, -, -, hlim₁⟩ := h₁
  obtain ⟨-, hS₂ζ, -, -, htr₂, hav₂, -⟩ := h₂
  -- rationals `S₁ < r < r₂ < S₂` and a trace on `[0, r₂]`
  obtain ⟨r, hr1, hr2⟩ := exists_nnrat_btwn' S₁.coe_nonneg (show (S₁ : ℝ) < S₂ from hlt)
  obtain ⟨r₂, hr₂1, hr₂2⟩ := exists_nnrat_btwn' (r : ℝ≥0).coe_nonneg hr2
  have hr1' : S₁ < (r : ℝ≥0) := by exact_mod_cast hr1
  have hr2' : (r : ℝ≥0) < S₂ := by exact_mod_cast hr2
  have hrr₂ : (r : ℝ≥0) < (r₂ : ℝ≥0) := by exact_mod_cast hr₂1
  have hr₂2' : (r₂ : ℝ≥0) < S₂ := by exact_mod_cast hr₂2
  obtain ⟨η, hη⟩ := exists_trace_of_trQ hw hw0 hS₂ζ htr₂ hr₂2'
  have hr₂ζ : (((r₂ : ℝ≥0)) : ℝ≥0∞) ≤ ζ := (lt_of_lt_of_le (by exact_mod_cast hr₂2') hS₂ζ).le
  have hηc : ContinuousOn η (Icc 0 (r : ℝ≥0)) :=
    hη.2.1.mono fun t ht => by exact_mod_cast ht.2.trans hrr₂.le
  have hηS : η S₁ = y₁ := eq_of_limQ hS₁ hr1'.le hηc
    (fun p hp => traceAt_eq_of_trace hη hw hw0 hr₂ζ ((hp.trans hr1').trans hrr₂)) hlim₁
  obtain ⟨n, hn⟩ := exists_mem_farReal hy₁.ne
  refine notMem_farReal_of_avoidQ (S := S₂) (r := r) (r' := r) hr2' hηc le_rfl
    (fun p hp => traceAt_eq_of_trace hη hw hw0 hr₂ζ
      (lt_of_le_of_lt (show (p : ℝ≥0) ≤ r from by exact_mod_cast hp) hrr₂)) hav₂ n hS₁ hr1'.le
    (by rw [hηS]; exact hn)

/-- **The end point is unique.** -/
theorem eq_of_limQ_limQ {S : ℝ≥0} (hS : 0 < S) {y₁ y₂ : ℝ} (h₁ : LimQ w S y₁) (h₂ : LimQ w S y₂) : y₁ = y₂ := by
  have hk : ∀ k : ℕ, |y₁ - y₂| ≤ 2 * (1 / ((k : ℝ) + 1)) := by
    intro k
    obtain ⟨m₁, hm₁⟩ := h₁ k
    obtain ⟨m₂, hm₂⟩ := h₂ k
    have hlo : max 0 (max ((S : ℝ) - 1 / ((m₁ : ℝ) + 1)) ((S : ℝ) - 1 / ((m₂ : ℝ) + 1))) < S := by
      have e1 : (0 : ℝ) < 1 / ((m₁ : ℝ) + 1) := by positivity
      have e2 : (0 : ℝ) < 1 / ((m₂ : ℝ) + 1) := by positivity
      exact max_lt (by exact_mod_cast hS) (max_lt (by linarith) (by linarith))
    obtain ⟨p, hp1, hp2⟩ := exists_nnrat_btwn' (le_max_left _ _) hlo
    have hpS : (p : ℝ≥0) < S := by exact_mod_cast hp2
    have a1 := hm₁ p (lt_of_le_of_lt ((le_max_left _ _).trans (le_max_right _ _)) hp1) hpS
    have a2 := hm₂ p (lt_of_le_of_lt ((le_max_right _ _).trans (le_max_right _ _)) hp1) hpS
    have : ‖((y₁ : ℂ)) - (y₂ : ℂ)‖ ≤ 2 * (1 / ((k : ℝ) + 1)) := by
      calc ‖((y₁ : ℂ)) - (y₂ : ℂ)‖ = ‖(LP.traceAt p w - (y₂ : ℂ)) - (LP.traceAt p w - (y₁ : ℂ))‖ := by
            congr 1; ring
        _ ≤ ‖LP.traceAt p w - (y₂ : ℂ)‖ + ‖LP.traceAt p w - (y₁ : ℂ)‖ := norm_sub_le _ _
        _ ≤ 1 / ((k : ℝ) + 1) + 1 / ((k : ℝ) + 1) := add_le_add a2 a1
        _ = 2 * (1 / ((k : ℝ) + 1)) := by ring
    rwa [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs] at this
  have hlim : Tendsto (fun k : ℕ => 2 * (1 / ((k : ℝ) + 1))) atTop (𝓝 (2 * 0)) :=
    tendsto_const_nhds.mul tendsto_one_div_add_atTop_nhds_zero_nat
  rw [mul_zero] at hlim
  have h0 : |y₁ - y₂| ≤ 0 := ge_of_tendsto hlim (Eventually.of_forall hk)
  have := abs_nonpos_iff.1 h0
  linarith

end Unique

/-! ### The code event -/

section CodeEvent

variable {a : ℝ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ} {eOf : (Fin nL → ℝ) × (Fin nR → ℝ) → ℝ}

/-- The driver of a canonical solution code is continuous before the lifetime and starts at `0`. -/
theorem cw_props_of_mem_cRelF {x : XCode nL nR} (hx : x ∈ CRelF a ρL ρR) :
    ContinuousOn (cw x) {t | (t : ℝ≥0∞) < cζ x} ∧ cw x 0 = 0 := by
  have hx' : x ∈ CRel a (startOf x).1 (startOf x).2 ρL ρR := mem_cRelF_iff.1 ⟨hx, rfl⟩
  have hp := hx'.1.2.2
  exact ⟨hp.isForcePath.continuousOn_w, hp.1⟩

theorem injOn_fst_endSet : InjOn Prod.fst (EndSet a ρL ρR eOf) := by
  rintro ⟨x, S₁, y₁⟩ ⟨hx, h₁⟩ ⟨x', S₂, y₂⟩ ⟨-, h₂⟩ hxx
  simp only at hxx
  subst hxx
  obtain ⟨hwc, hw0⟩ := cw_props_of_mem_cRelF hx
  have hS : S₁ = S₂ := by
    rcases lt_trichotomy S₁ S₂ with h | h | h
    · exact (not_endCond_of_lt hwc hw0 h₁ h₂ h).elim
    · exact h
    · exact (not_endCond_of_lt hwc hw0 h₂ h₁ h).elim
  subst hS
  have hy := eq_of_limQ_limQ h₁.1 h₁.2.2.2.2.2.2 h₂.2.2.2.2.2.2
  simp only at hy
  rw [hy]

/-- **The left strip end is a Borel event of solution codes** (Lusin–Souslin). -/
theorem measurableSet_endCode (he : Measurable eOf) : MeasurableSet (endCode a ρL ρR eOf) :=
  (measurableSet_endSet a ρL ρR he).image_of_measurable_injOn measurable_fst injOn_fst_endSet

/-- **The coding on canonical codes from a start.** -/
theorem mem_endCode_iff {s : (Fin nL → ℝ) × (Fin nR → ℝ)} {x : XCode nL nR} (hx : x ∈ CRel a s.1 s.2 ρL ρR) :
    x ∈ endCode a ρL ρR eOf ↔ LeftEnd (eOf s) (cw x) (cζ x) := by
  obtain ⟨hxF, hst⟩ := mem_cRelF_iff.2 hx
  constructor
  · rintro ⟨⟨x', S, y⟩, ⟨-, h⟩, rfl⟩
    rw [hst] at h
    exact ⟨S, y, h⟩
  · rintro ⟨S, y, h⟩
    exact ⟨(x, S, y), ⟨hxF, by rw [hst]; exact h⟩, rfl⟩

/-- A strictly ordered separated start: every left mark negative and strictly ordered, every right mark positive
and strictly ordered. -/
def StrictStart (s : (Fin nL → ℝ) × (Fin nR → ℝ)) : Prop :=
  StrictAnti s.1 ∧ (∀ i, s.1 i < 0) ∧ StrictMono s.2 ∧ ∀ j, 0 < s.2 j

theorem measurableSet_strictStart : MeasurableSet {s : (Fin nL → ℝ) × (Fin nR → ℝ) | StrictStart s} := by
  have h1 : ∀ i : Fin nL, Measurable fun s : (Fin nL → ℝ) × (Fin nR → ℝ) => s.1 i := fun i =>
    (measurable_pi_apply i).comp measurable_fst
  have h2 : ∀ j : Fin nR, Measurable fun s : (Fin nL → ℝ) × (Fin nR → ℝ) => s.2 j := fun j =>
    (measurable_pi_apply j).comp measurable_snd
  refine measurableSet_setOfPred.2 (Measurable.and ?_ (Measurable.and ?_ (Measurable.and ?_ ?_)))
  · refine Measurable.forall fun i => Measurable.forall fun j => Measurable.imp measurable_const ?_
    exact measurableSet_setOfPred.1 (measurableSet_lt (h1 j) (h1 i))
  · exact Measurable.forall fun i => measurableSet_setOfPred.1 (measurableSet_lt (h1 i) measurable_const)
  · refine Measurable.forall fun i => Measurable.forall fun j => Measurable.imp measurable_const ?_
    exact measurableSet_setOfPred.1 (measurableSet_lt (h2 i) (h2 j))
  · exact Measurable.forall fun j => measurableSet_setOfPred.1 (measurableSet_lt measurable_const (h2 j))

/-- **The restart event**: a code whose start is strictly ordered has a left strip end. -/
def exitCode (a : ℝ) (ρL : Fin nL → ℝ) (ρR : Fin nR → ℝ) (eOf : (Fin nL → ℝ) × (Fin nR → ℝ) → ℝ) :
    Set (XCode nL nR) :=
  {x | StrictStart (startOf x)}ᶜ ∪ endCode a ρL ρR eOf

theorem measurableSet_exitCode (he : Measurable eOf) : MeasurableSet (exitCode a ρL ρR eOf) :=
  (measurableSet_strictStart.preimage measurable_startOf).compl.union (measurableSet_endCode he)

/-- On a start that is not strictly ordered, the canonical law of the complement of the restart event vanishes. -/
theorem codeLaw_compl_exitCode_of_not {s : (Fin nL → ℝ) × (Fin nR → ℝ)} (hs : ¬ StrictStart s) :
    codeLaw a ρL ρR (exitCode a ρL ρR eOf)ᶜ s = 0 := by
  refine measure_mono_null (fun f hf => ?_) measure_empty
  obtain ⟨x, ⟨⟨hxF, -⟩, hxS⟩, hxe⟩ := hf
  simp only [Prod.mk.injEq] at hxe
  exact hxS (Or.inl (show ¬ StrictStart (startOf x) by rw [hxe.1]; exact hs))

/-- The coding of the restart event on canonical codes from a strictly ordered start. -/
theorem mem_exitCode_iff {s : (Fin nL → ℝ) × (Fin nR → ℝ)} (hs : StrictStart s) {x : XCode nL nR}
    (hx : x ∈ CRel a s.1 s.2 ρL ρR) : x ∈ exitCode a ρL ρR eOf ↔ LeftEnd (eOf s) (cw x) (cζ x) := by
  rw [← mem_endCode_iff hx]
  have hst := (mem_cRelF_iff.2 hx).2
  constructor
  · rintro (h | h)
    · exact absurd (show StrictStart (startOf x) by rw [hst]; exact hs) h
    · exact h
  · exact Or.inr

end CodeEvent

end InteractingSLE.Sec5.Prop49Exit
