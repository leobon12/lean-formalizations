/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec5.CrossCondStagedGlueHull
import InteractingSLE.Spec.Sec5.GlueCondTopo
import InteractingSLE.Foundations.Loewner.Capacity

/-!
# One event for all fixed extreme-angle schedules (R73, Astra follow-up 5 §2.1–§2.2)

Packet PROVE-STAGED5. Ruling R73 adopts Astra's follow-up 5 §2 (`source/external/AstraIG1/ig1_followup5.txt`
L239–L401) for Proposition 5.9: every fixed extreme-angle schedule is determined by the field (§2.1, here
`ae_pastMap_eq_codePast`, `ae_drivers_eq_codeDriver`), and "finite induction followed by countable intersection gives
one event for all allowed fixed finite schedules. This is a joint statement, not a choice of unrelated determining
functions on individual realizations" (§2.2, L307–L309). The determining maps here are the explicit Borel maps
`codePast … s k` and `codeDriver …` (the §4.2 codes of the successive stage words), one for each schedule, so §2.2's
measurable graph lemma is not needed for fixed schedules:

* **`ae_forall_pastMap_eq_codePast`**: one event of full probability on which, for every schedule `s` and every
  instruction count `k`, the retained past of the staged history `E s` is `codePast … s k (h ω)`;
* **`ae_forall_drivers_eq_codeDriver`**: one event on which every launched piece of every schedule is its code driver,
  with infinite lifetime;
* **`ae_forall_isGoodSched`**: one event on which every schedule's history is good (`IsGoodSched`);
* **`recHull_eq_fwdHull`**, **`isHPHull_recHull`**, **`not_isBounded_lowerUnion_recHull`**: the hull of the records is
  the forward hull of the joined record driver, an `ℍ`-hull, so its lower union has only unbounded components (the
  input `hunb` of the staged glued law, at every sample).

Not covered (R73's correction, L8–L14, and §2.3): for an ADAPTIVE schedule (switching index depending on the retained
counterflow), the identification of each realized adaptive prefix with the canonical path of its realized schedule
(`X_j = Φ_{I_j}(h)` a.s., (2.2)) needs the restricted joint field–record law; it is not proved here.

R48: nothing here uses Theorem 1.2/1.3; the only named input is `AdmCode.Theorem12ParamCond44Statement`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal
open LQGMetric (DistOn)

universe u

namespace InteractingSLE.Sec5.CrossCond.StagedGlue

open Exist.Staged Exist.StagedLaw Sec7.AdmCode Prop513TreeExtract Prop513Schedule
open Restart (BoundaryWord)

variable (h44 : Theorem12ParamCond44Statement.{u}) {κ : ℝ} (hκ : 0 < κ) (hκ4 : κ < 4)
  {Ω : Type u} [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {h : Ω → DistOn upperHalfPlaneOpens} {E : Schedule → ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞}

include h44 hκ hκ4

/-- **One event for all fixed schedules** (R73, follow-up 5 §2.2): almost surely, for every extreme-angle schedule `s`
and every instruction count `k`, the retained past of `E s` is the Borel map `codePast … s k` of the field. -/
theorem ae_forall_pastMap_eq_codePast (c₀ : BoundaryWord) (hc₀ : ExtremeHeights κ c₀)
    (hh : IsGFFWithBoundaryData P h c₀.fn c₀.jumps)
    (hE : ∀ s, IsStagedHistory κ c₀.fn c₀.jumps P h (scheduleSpec s) (E s))
    (hreg : ∀ s j ω, IsRegularDriver (E s j ω)) :
    ∀ᵐ ω ∂P, ∀ s k, pastMap κ c₀.fn c₀.jumps (scheduleSpec s) (E s) k ω = codePast h44 hκ hκ4 c₀ s k (h ω) :=
  ae_all_iff.2 fun s => ae_pastMap_eq_codePast h44 hκ hκ4 c₀ hc₀ hh s (hE s) (hreg s)

/-- **One event on which every launched piece of every fixed schedule is its code driver** (with infinite lifetime). -/
theorem ae_forall_drivers_eq_codeDriver (c₀ : BoundaryWord) (hc₀ : ExtremeHeights κ c₀)
    (hh : IsGFFWithBoundaryData P h c₀.fn c₀.jumps)
    (hE : ∀ s, IsStagedHistory κ c₀.fn c₀.jumps P h (scheduleSpec s) (E s))
    (hreg : ∀ s j ω, IsRegularDriver (E s j ω)) :
    ∀ᵐ ω ∂P, ∀ s, ∀ j < (scheduleSpec s).2.2.length, (E s j ω).2 = ⊤ ∧
      E s j ω = codeDriver h44 hκ hκ4 c₀ (scheduleSpec s) j (h ω) :=
  ae_all_iff.2 fun s => ae_schedule_drivers h44 hκ hκ4 c₀ hc₀ hh s (hE s) (hreg s)

/-- **One event on which the history of every fixed schedule is good.** -/
theorem ae_forall_isGoodSched (c₀ : BoundaryWord) (hc₀ : ExtremeHeights κ c₀)
    (hh : IsGFFWithBoundaryData P h c₀.fn c₀.jumps)
    (hE : ∀ s, IsStagedHistory κ c₀.fn c₀.jumps P h (scheduleSpec s) (E s))
    (hreg : ∀ s j ω, IsRegularDriver (E s j ω)) :
    ∀ᵐ ω ∂P, ∀ s, IsGoodSched s (E s) ω :=
  ae_all_iff.2 fun s => ae_isGoodSched h44 hκ hκ4 c₀ hc₀ hh s (hE s) (hreg s)

omit h44 hκ hκ4 in
/-- **The hull of the records is the forward hull of the joined record driver.** -/
theorem recHull_eq_fwdHull (s : Schedule) (n : ℕ) (u : PastData (n + 1)) :
    recHull s n u = QuantumZipper.fwdHull (Ito.rpath (Staged.catN (recDrvOf u) (schedD s) n))
      (Staged.cumT (schedD s) n) := by
  have hW := Staged.continuous_rpath_of (Staged.continuous_catN (T := schedD s) (fun j => recDrvOf_continuous u j)
    (fun j => recDrvOf_zero u j) n)
  have hW0 := Staged.rpath_zero_of_zero (Staged.catN_zero (T := schedD s) (fun j => recDrvOf_zero u j) n)
  have hK := isHPHull_fwdHull hW (Staged.cumT (schedD s) n).coe_nonneg
  ext z
  unfold recHull Staged.catChartN
  rw [Set.mem_sdiff, SetLike.mem_coe,
    Staged.mem_dom_recenter_loewner_iff 0 hW hW0 (Staged.cumT (schedD s) n).coe_nonneg,
    Complex.ofReal_zero, sub_zero, Staged.mem_dom_loewner_iff_mem_diff_hull hW hW0
      (Staged.cumT (schedD s) n).coe_nonneg, Set.mem_sdiff]
  exact ⟨fun ⟨hz, hn⟩ => by by_contra hk; exact hn ⟨hz, hk⟩, fun hk => ⟨hK.1 hk, fun h' => h'.2 hk⟩⟩

omit h44 hκ hκ4 in
/-- **The hull of the records is an `ℍ`-hull.** -/
theorem isHPHull_recHull (s : Schedule) (n : ℕ) (u : PastData (n + 1)) : IsHPHull (recHull s n u) := by
  rw [recHull_eq_fwdHull]
  exact isHPHull_fwdHull (Staged.continuous_rpath_of (Staged.continuous_catN (T := schedD s)
    (fun j => recDrvOf_continuous u j) (fun j => recDrvOf_zero u j) n)) (Staged.cumT (schedD s) n).coe_nonneg

omit h44 hκ hκ4 in
/-- **`hunb` for the hull of the records**: every component of its lower union is unbounded (at every sample). -/
theorem not_isBounded_lowerUnion_recHull (s : Schedule) (n : ℕ) (u : PastData (n + 1)) :
    ∀ z ∈ LocalSets.lowerUnion (recHull s n u),
      ¬ Bornology.IsBounded (connectedComponentIn (LocalSets.lowerUnion (recHull s n u)) z) :=
  GlueCond.not_isBounded_lowerUnion_of_isHPHull (isHPHull_recHull s n u)

end InteractingSLE.Sec5.CrossCond.StagedGlue
