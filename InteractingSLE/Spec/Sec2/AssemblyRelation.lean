/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec2.AssemblyCode
import InteractingSLE.Frozen.Spec.IsIntegratedSLEPath

/-!
# Theorem 2.2 assembly: the code space and its good set

Packet PROVE-SEC2-PATCH. The code space `XCode nL nR = PCode × (ℝ≥0∞ × PCode × (Fin nL → PCode) ×
(Fin nR → PCode))` carries a driving-path code and the code of a killed state path (lifetime and
the codes of `w`, `v^{i,L}`, `v^{i,R}`). It is a standard Borel space. `Good x` (a measurable,
countable condition) says that the driving code is uniformly continuous on every bounded dyadic
set and the state codes on the dyadic times of every `[0, T]`, `T < ζ` dyadic; then the decoded
paths are continuous (`Good.continuous_b`, `Good.continuousOn`). Closed conditions and
integrability before `ζ` reduce to dyadic times (`forall_lt_of_forall_dyad`,
`forall_lt_intervalIntegrable`).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology
open scoped NNReal ENNReal

namespace InteractingSLE

namespace Sec2

namespace Assembly

/-- Code of a killed state path: lifetime and codes of `w`, `v^{i,L}`, `v^{i,R}`. -/
abbrev SCode (nL nR : ℕ) : Type := ℝ≥0∞ × PCode × (Fin nL → PCode) × (Fin nR → PCode)

/-- The code space: driving-path code and killed-state code. -/
abbrev XCode (nL nR : ℕ) : Type := PCode × SCode nL nR

variable {nL nR : ℕ}

/-- Lifetime of a code. -/
def cζ (x : XCode nL nR) : ℝ≥0∞ := x.2.1
/-- Decoded driving path. -/
def cb (x : XCode nL nR) : ℝ≥0 → ℝ := dec x.1
/-- Decoded driver. -/
def cw (x : XCode nL nR) : ℝ≥0 → ℝ := dec x.2.2.1
/-- Decoded left force points. -/
def cvL (x : XCode nL nR) : Fin nL → ℝ≥0 → ℝ := fun i => dec (x.2.2.2.1 i)
/-- Decoded right force points. -/
def cvR (x : XCode nL nR) : Fin nR → ℝ≥0 → ℝ := fun j => dec (x.2.2.2.2 j)

instance instStandardBorelSpaceMarks :
    StandardBorelSpace ((Fin nL → PCode) × (Fin nR → PCode)) := StandardBorelSpace.prod
instance instStandardBorelSpaceState :
    StandardBorelSpace (PCode × (Fin nL → PCode) × (Fin nR → PCode)) := StandardBorelSpace.prod
instance instStandardBorelSpaceSCode : StandardBorelSpace (SCode nL nR) := StandardBorelSpace.prod
instance instStandardBorelSpaceXCode : StandardBorelSpace (XCode nL nR) := StandardBorelSpace.prod

theorem measurable_cζ : Measurable (cζ : XCode nL nR → ℝ≥0∞) := measurable_snd.fst

/-- Joint measurability of a decoded coordinate in `(code, real time)`. -/
theorem measurable_dec_real {α : Type*} [MeasurableSpace α] {f : α → PCode} (hf : Measurable f) :
    Measurable fun p : α × ℝ => dec (f p.1) p.2.toNNReal := by
  have h1 : Measurable fun p : α × ℝ => (f p.1, p.2.toNNReal) :=
    (hf.comp measurable_fst).prodMk (measurable_real_toNNReal.comp measurable_snd)
  have := measurable_dec.comp h1
  rwa [Function.comp_def] at this

theorem measurable_dec_at {α : Type*} [MeasurableSpace α] {f : α → PCode} (hf : Measurable f)
    (t : ℝ≥0) : Measurable fun x => dec (f x) t := by
  have := measurable_dec.comp (hf.prodMk (measurable_const (a := t)))
  rwa [Function.comp_def] at this

theorem measurable_code_b : Measurable fun x : XCode nL nR => x.1 := measurable_fst
theorem measurable_code_w : Measurable fun x : XCode nL nR => x.2.2.1 := measurable_snd.snd.fst
theorem measurable_code_vL (i : Fin nL) : Measurable fun x : XCode nL nR => x.2.2.2.1 i :=
  (measurable_pi_apply i).comp measurable_snd.snd.snd.fst
theorem measurable_code_vR (j : Fin nR) : Measurable fun x : XCode nL nR => x.2.2.2.2 j :=
  (measurable_pi_apply j).comp measurable_snd.snd.snd.snd

/-! ### The good set -/

/-- The codes are uniformly continuous on bounded dyadic sets (driving path) and on the dyadic
times of `[0, T]` for dyadic `T < ζ` (state). -/
def Good (x : XCode nL nR) : Prop :=
  (∀ T : ℕ, UC x.1 T) ∧ ∀ n k, (dyad n k : ℝ≥0∞) < x.2.1 →
    UC x.2.2.1 (dyad n k) ∧ (∀ i, UC (x.2.2.2.1 i) (dyad n k)) ∧
      ∀ j, UC (x.2.2.2.2 j) (dyad n k)

theorem measurableSet_good : MeasurableSet {x : XCode nL nR | Good x} := by
  have hU : ∀ {f : XCode nL nR → PCode}, Measurable f → ∀ T, MeasurableSet {x | UC (f x) T} :=
    fun hf T => hf (measurableSet_UC T)
  have e : {x : XCode nL nR | Good x} = (⋂ T : ℕ, {x | UC x.1 T}) ∩
      ⋂ n : ℕ, ⋂ k : ℕ, ({x : XCode nL nR | (dyad n k : ℝ≥0∞) < x.2.1}ᶜ ∪
        ({x | UC x.2.2.1 (dyad n k)} ∩ (⋂ i, {x | UC (x.2.2.2.1 i) (dyad n k)}) ∩
          ⋂ j, {x | UC (x.2.2.2.2 j) (dyad n k)})) := by
    ext x
    simp only [Good, mem_inter_iff, mem_iInter, mem_union, mem_compl_iff]
    refine and_congr Iff.rfl (forall_congr' fun n => forall_congr' fun k => ?_)
    constructor
    · intro h
      by_cases hlt : (dyad n k : ℝ≥0∞) < x.2.1
      · exact Or.inr ⟨⟨(h hlt).1, (h hlt).2.1⟩, (h hlt).2.2⟩
      · exact Or.inl hlt
    · rintro (h | ⟨⟨h1, h2⟩, h3⟩) hlt
      · exact absurd hlt h
      · exact ⟨h1, h2, h3⟩
  rw [e]
  refine (MeasurableSet.iInter fun T => hU measurable_code_b _).inter
    (MeasurableSet.iInter fun n => MeasurableSet.iInter fun k => ?_)
  refine (measurableSet_lt measurable_const measurable_cζ).compl.union ?_
  exact ((hU measurable_code_w _).inter (MeasurableSet.iInter fun i => hU (measurable_code_vL i) _))
    |>.inter (MeasurableSet.iInter fun j => hU (measurable_code_vR j) _)

/-- A code that is `UC` below every dyadic time `< ζ` decodes to a path continuous before `ζ`. -/
theorem continuousOn_dec_of_UC {c : PCode} {ζ : ℝ≥0∞}
    (h : ∀ n k, (dyad n k : ℝ≥0∞) < ζ → UC c (dyad n k)) :
    ContinuousOn (dec c) {t | (t : ℝ≥0∞) < ζ} := by
  intro t ht
  obtain ⟨n, k, htd, hdζ⟩ := exists_dyad_btwn ht
  have hc := (h n k hdζ).continuousOn
  exact (hc.continuousAt (Iic_mem_nhds htd)).continuousWithinAt

theorem Good.continuous_b {x : XCode nL nR} (hx : Good x) : Continuous (cb x) := by
  rw [continuous_iff_continuousAt]
  intro t
  have ht : t < ((⌈(t : ℝ)⌉₊ + 1 : ℕ) : ℝ≥0) := by
    have : (t : ℝ) < ⌈(t : ℝ)⌉₊ + 1 := lt_of_le_of_lt (Nat.le_ceil _) (lt_add_one _)
    exact_mod_cast this
  exact (hx.1 (⌈(t : ℝ)⌉₊ + 1)).continuousOn.continuousAt (Iic_mem_nhds ht)

theorem Good.continuousOn_w {x : XCode nL nR} (hx : Good x) :
    ContinuousOn (cw x) {t | (t : ℝ≥0∞) < cζ x} :=
  continuousOn_dec_of_UC fun n k h => (hx.2 n k h).1

theorem Good.continuousOn_vL {x : XCode nL nR} (hx : Good x) (i : Fin nL) :
    ContinuousOn (cvL x i) {t | (t : ℝ≥0∞) < cζ x} :=
  continuousOn_dec_of_UC fun n k h => (hx.2 n k h).2.1 i

theorem Good.continuousOn_vR {x : XCode nL nR} (hx : Good x) (j : Fin nR) :
    ContinuousOn (cvR x j) {t | (t : ℝ≥0∞) < cζ x} :=
  continuousOn_dec_of_UC fun n k h => (hx.2 n k h).2.2 j

/-! ### Reduction to dyadic times -/

/-- A closed condition holding at the dyadic times before `ζ` holds before `ζ`, for a path
continuous before `ζ`. -/
theorem forall_lt_of_forall_dyad {E : Type*} [TopologicalSpace E] {F : ℝ≥0 → E} {ζ : ℝ≥0∞}
    (hF : ContinuousOn F {t | (t : ℝ≥0∞) < ζ}) {C : Set E} (hC : IsClosed C)
    (h : ∀ n k, (dyad n k : ℝ≥0∞) < ζ → F (dyad n k) ∈ C) {t : ℝ≥0} (ht : (t : ℝ≥0∞) < ζ) :
    F t ∈ C := by
  have hFt : ContinuousAt F t :=
    hF.continuousAt ((isOpen_lt ENNReal.continuous_coe continuous_const).mem_nhds ht)
  refine hC.mem_of_tendsto (hFt.tendsto.comp (tendsto_dyad_flr t)) (Eventually.of_forall
    fun n => h n _ (lt_of_le_of_lt (by exact_mod_cast dyad_flr_le n t) ht))

/-- Interval integrability on `[0, t]` for all `t < ζ` reduces to dyadic `t`. -/
theorem forall_lt_intervalIntegrable {g : ℝ → ℝ} {ζ : ℝ≥0∞}
    (h : ∀ n k, (dyad n k : ℝ≥0∞) < ζ → IntervalIntegrable g volume 0 (dyad n k))
    {t : ℝ≥0} (ht : (t : ℝ≥0∞) < ζ) : IntervalIntegrable g volume 0 t := by
  obtain ⟨n, k, htd, hdζ⟩ := exists_dyad_btwn ht
  refine (h n k hdζ).mono_set ?_
  rw [uIcc_of_le t.coe_nonneg, uIcc_of_le (dyad n k).coe_nonneg]
  exact Icc_subset_Icc le_rfl (by exact_mod_cast htd.le)

/-- A primitive of a function integrable on every `[0, t]`, `t < ζ`, is continuous before `ζ`. -/
theorem continuousOn_primitive {g : ℝ → ℝ} {ζ : ℝ≥0∞}
    (h : ∀ t : ℝ≥0, (t : ℝ≥0∞) < ζ → IntervalIntegrable g volume 0 t) :
    ContinuousOn (fun t : ℝ≥0 => ∫ s in (0 : ℝ)..t, g s) {t | (t : ℝ≥0∞) < ζ} := by
  intro t ht
  obtain ⟨n, k, htd, hdζ⟩ := exists_dyad_btwn ht
  have hI : IntegrableOn g (uIcc 0 (dyad n k : ℝ)) volume := by
    rw [uIcc_of_le (dyad n k).coe_nonneg]
    exact (intervalIntegrable_iff_integrableOn_Icc_of_le (dyad n k).coe_nonneg).1 (h _ hdζ)
  have hc := intervalIntegral.continuousOn_primitive_interval hI
  rw [uIcc_of_le (dyad n k).coe_nonneg] at hc
  have hcomp : ContinuousOn (fun t : ℝ≥0 => ∫ s in (0 : ℝ)..t, g s) (Iic (dyad n k)) :=
    hc.comp NNReal.continuous_coe.continuousOn fun s hs => ⟨s.coe_nonneg, by exact_mod_cast hs⟩
  exact (hcomp.continuousAt (Iic_mem_nhds htd)).continuousWithinAt

end Assembly

end Sec2

end InteractingSLE
