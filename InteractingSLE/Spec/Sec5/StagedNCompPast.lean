/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec5.StagedNCompClause
import InteractingSLE.Spec.Sec5.StagedS4Past

/-!
# The flag candidate's stopped data are events of DEPTH's σ-algebras

Packet PROVE-STAGED-NODECOMP. PROVE-STAGED-S4's `StagedS4Past` (candidate part) for the flag candidate of arbitrary
angle flags `fl`; the generic part (`pastRec`, `pastDrv`, `pastHist`, `stopHistory_killedHistory_joinProc`,
`cfGlueMarks_eq_comap_stopD`) is reused from S4.

* **`ae_stopD_candF_eq`**: the stopped data of the flag candidate at the own time `q` are read off the retained past;
* **`exists_candSigmaF_ae_eq_stopD`**, **`exists_candSigmaF_ae_eq_of_cfGlueMarks`**: every stopped-data (marks) event
  is almost surely an event of DEPTH's σ-algebra for `mkSchedF fl ℓ t q`.

R48: only `h44` (R74) is used.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped NNReal ENNReal Real
open LQGMetric (DistOn TestOn)

namespace InteractingSLE.Sec5.CrossCond.StagedNComp

open WangWu hiding ratPt exists_ratPt_dist_lt
open WangWu.ImgWord LawUnique GlueCond Cond44Ref Word49 Theta StagedFinal LocalSets
open Restart Exist.StagedLaw Exist.Staged Theorem14.GW2Schedule
open Sec7.AdmCode Prop513TreeExtract Prop513Schedule Prop513Target StagedGlue StagedDepth StagedS3
open Prop59Pieces StagedRepLater StagedS4 Prop59NodeTree
open Sec4 (IsStripGFF IsStripCounterflowDriver)
open CrossCond.Staged (catN cumT stageDrv)

/-! ### The candidate's stopped data are events of DEPTH's σ-algebras -/

section Cand

variable (x₀ : ℝ) (h44 : Theorem12ParamCond44Statement.{0}) {κ a b a' b' : ℝ} (hκ : 0 < κ) (hκ4 : κ < 4)
  (hb : IsFig51Bounds κ a b a' b') {Ω : Type} [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω]
  (P : Measure Ω) [IsProbabilityMeasure P] (h : Ω → DistOn upperHalfPlaneOpens) (W : ℝ≥0 → Ω → ℝ)
  (ζ : Ω → ℝ≥0∞) (fl : ℕ → Bool)

include hκ4 in
/-- **The stopped data of the candidate at the own time `q` are read off the retained past**, almost surely on the
glued space. -/
theorem ae_stopD_candF_eq (hG : IsStripGFF κ P h (fig51Lower a b) (fig51Upper x₀ a' b') {0} {x₀})
    {ℓ : ℕ} {t : Fin ℓ → ℝ≥0} (hv : IsValid ℓ t) {q : ℚ} (hq : lastO ℓ t < q) (s : ℝ≥0) :
    ∀ᵐ p ∂(candMu x₀ (κ := κ) P h W ζ hG.1),
      stopD (candWF x₀ h44 hκ hκ4 hb h fl ℓ t) (Fin.elim0 : Fin 0 → ℝ≥0 → Ω → ℝ) (Fin.elim0 : Fin 0 → ℝ≥0 → Ω → ℝ)
          (fun _ => ⊤) q s p =
        (pastHist (mkSchedF fl ℓ t q) (q : ℝ).toNNReal (pastMap κ (sourceWord (x₀ := x₀) hκ hb).fn
          (sourceWord (x₀ := x₀) hκ hb).jumps (scheduleSpec (mkSchedF fl ℓ t q))
          (Prop59Sched.schedDrivers h44 hκ hκ4 (sourceWord (x₀ := x₀) hκ hb) (mkSchedF fl ℓ t q) (qField x₀ κ h))
          (ℓ + 1) p.1), cfStop s p.2) := by
  set c := sourceWord (x₀ := x₀) hκ hb with hc
  have hh : IsGFFWithBoundaryData P (qField x₀ κ h) c.fn c.jumps := sourceWord_gff hκ hb hG
  have hE := Prop59Sched.isStagedHistory_schedDrivers h44 hκ hκ4 c (sourceWord_extreme hκ hb) hh (mkSchedF fl ℓ t q)
  have hreg := Prop59Sched.schedDrivers_regular h44 hκ hκ4 c (mkSchedF fl ℓ t q) (qField x₀ κ h)
  have hgs := ae_isGoodSched h44 hκ hκ4 c (sourceWord_extreme hκ hb) hh (mkSchedF fl ℓ t q) hE hreg
  have hgs' : ∀ᵐ p ∂(candMu x₀ (κ := κ) P h W ζ hG.1),
      IsGoodSched (mkSchedF fl ℓ t q) (Prop59Sched.schedDrivers h44 hκ hκ4 c (mkSchedF fl ℓ t q) (qField x₀ κ h)) p.1 :=
    WangWu.ae_glue_fst (X := fun ω => cfFieldT κ (π / 2) (rootField (κ := κ) (x₀ := x₀) h ω))
      (candK x₀ (κ := κ) P h W ζ)
      ((measurable_cfFieldT κ (π / 2)).comp (measurable_rootField (κ := κ) (x₀ := x₀) hG.1)) hgs
  have hW : candWF x₀ h44 hκ hκ4 hb h fl ℓ t =
      joinProc (mkSchedF fl ℓ t q) (Prop59Sched.schedDrivers h44 hκ hκ4 c (mkSchedF fl ℓ t q) (qField x₀ κ h)) :=
    (joinProc_mkSchedF_eq_qDrvF h44 hκ hκ4 c (qField x₀ κ h) fl hv hq).symm
  filter_upwards [hgs'] with p hp
  have hcum := cumT_schedD_mkSchedF (fl := fl) hv hq
  have key := stopHistory_killedHistory_joinProc (κ := κ) (c₀ := c) hp hreg (schedL_mkSchedF (fl := fl) hv hq).ge
  rw [hcum] at key
  rw [stopD, hW, key]

include hκ4 in
/-- **Every event of the candidate's stopped data at the own time `q` is, almost surely, an event of DEPTH's
σ-algebra for `mkSchedF fl ℓ t q`.** -/
theorem exists_candSigmaF_ae_eq_stopD (hG : IsStripGFF κ P h (fig51Lower a b) (fig51Upper x₀ a' b') {0} {x₀})
    (us : ℂ → ℝ) {ℓ : ℕ} {t : Fin ℓ → ℝ≥0} (hv : IsValid ℓ t) {q : ℚ} (hq : lastO ℓ t < q) (s : ℝ≥0)
    {C : Set (Y49 0 0)} (hC : MeasurableSet C) :
    ∃ B, MeasurableSet[candSigmaF x₀ h44 hκ hκ4 hb h fl us ℓ t q s] B ∧
      B =ᵐ[candMu x₀ (κ := κ) P h W ζ hG.1]
        stopD (candWF x₀ h44 hκ hκ4 hb h fl ℓ t) (Fin.elim0 : Fin 0 → ℝ≥0 → Ω → ℝ)
          (Fin.elim0 : Fin 0 → ℝ≥0 → Ω → ℝ) (fun _ => ⊤) q s ⁻¹' C := by
  set c := sourceWord (x₀ := x₀) hκ hb with hc
  set Z : PastData (ℓ + 1) × HistorySpace 0 0 → Y49 0 0 := fun z => (pastHist (mkSchedF fl ℓ t q) (q : ℝ).toNNReal z.1,
    cfStop s z.2) with hZ
  have hZm : Measurable[(inferInstance : MeasurableSpace (PastData (ℓ + 1))).prod (stopSigma s)] Z := by
    refine Measurable.prodMk ((measurable_pastHist _ _ ℓ).comp ?_) ?_
    · exact measurable_fst
    · have h2 : Measurable[stopSigma s] fun y : HistorySpace 0 0 => cfStop s y :=
        fun B hB => ⟨B, hB, rfl⟩
      exact h2.comp measurable_snd
  refine ⟨(fun p : Ω × HistorySpace 0 0 => (pastMap κ c.fn c.jumps (scheduleSpec (mkSchedF fl ℓ t q))
      (Prop59Sched.schedDrivers h44 hκ hκ4 c (mkSchedF fl ℓ t q) (qField x₀ κ h)) (ℓ + 1) p.1, p.2)) ⁻¹' (Z ⁻¹' C),
    le_sup_right (a := germSigma _ _) _ ⟨Z ⁻¹' C, hZm hC, rfl⟩, ?_⟩
  filter_upwards [ae_stopD_candF_eq x₀ h44 hκ hκ4 hb P h W ζ fl hG hv hq s] with p hp
  show (Z (_, p.2) ∈ C) = (stopD _ _ _ _ q s p ∈ C)
  rw [hp]

include hκ4 in
/-- **Every event of Word49's marks σ-algebra of the candidate at the own time `q` is, almost surely, an event of
DEPTH's σ-algebra for `mkSchedF fl ℓ t q`.** This transfers the template's `exists_marks_ae_eq_inter` and
`exists_marks_ae_eq_avoid` (stated for `cfGlueMarks`) to the conditioning σ-algebras of (SW3). -/
theorem exists_candSigmaF_ae_eq_of_cfGlueMarks (hG : IsStripGFF κ P h (fig51Lower a b) (fig51Upper x₀ a' b') {0} {x₀})
    (us : ℂ → ℝ) {ℓ : ℕ} {t : Fin ℓ → ℝ≥0} (hv : IsValid ℓ t) {q : ℚ} (hq : lastO ℓ t < q) (s : ℝ≥0)
    {A : Set (Ω × HistorySpace 0 0)}
    (hA : MeasurableSet[cfGlueMarks (candWF x₀ h44 hκ hκ4 hb h fl ℓ t) (Fin.elim0 : Fin 0 → ℝ≥0 → Ω → ℝ)
      (Fin.elim0 : Fin 0 → ℝ≥0 → Ω → ℝ) (fun _ => ⊤) (q : ℝ).toNNReal s] A) :
    ∃ B, MeasurableSet[candSigmaF x₀ h44 hκ hκ4 hb h fl us ℓ t q s] B ∧ B =ᵐ[candMu x₀ (κ := κ) P h W ζ hG.1] A := by
  rw [cfGlueMarks_eq_comap_stopD] at hA
  obtain ⟨C, hC, rfl⟩ := hA
  exact exists_candSigmaF_ae_eq_stopD x₀ h44 hκ hκ4 hb P h W ζ fl hG us hv hq s hC

end Cand

end InteractingSLE.Sec5.CrossCond.StagedNComp
