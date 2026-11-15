/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec5.StagedS4Clause

/-!
# The stopped data of the staged path are read off the retained past

Packet PROVE-STAGED-S4 (§5.2 (M1) of `planning/handoffs/PROVE-STAGED-S3.md`). On the good schedule event the joined
driver of a schedule agrees, up to the end `cumT … ℓ` of piece `ℓ`, with the concatenation of the record drivers read
off the retained past (`IsGoodSched.joinW_eq_catN_stageDrv`). Hence the flow history stopped at that time is a Borel
function `pastHist` of the retained past (`stopHistory_killedHistory_joinProc`), and for PIECES' candidate every
event of Word49's stopped data `stopD` at the own time `q` is almost surely an event of DEPTH's σ-algebra
`candSigma … q s` (**`exists_candSigma_ae_eq_stopD`**). This is what transfers Word49's stopped-data descriptions
of the image word (template `exists_measurableSet_stopD_iff`) into the conditioning σ-algebras of (SW3).

R48: only `h44` (R74) is used.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped NNReal ENNReal Real
open LQGMetric (DistOn TestOn)

namespace InteractingSLE.Sec5.CrossCond.StagedS4

open WangWu hiding ratPt exists_ratPt_dist_lt
open WangWu.ImgWord LawUnique GlueCond Cond44Ref Word49 Theta StagedFinal LocalSets
open Restart Exist.StagedLaw Exist.Staged Theorem14.GW2Schedule
open Sec7.AdmCode Prop513TreeExtract Prop513Schedule Prop513Target StagedGlue StagedDepth StagedS3
open Prop59Pieces StagedRepLater
open Sec4 (IsStripGFF IsStripCounterflowDriver)
open CrossCond.Staged (catN cumT stageDrv)

/-! ### Reading the staged driver off the retained past -/

section Past

/-- The record drivers of the pieces `0, …, ℓ` read off a retained past (`Staged.stageDrv` as a function of it). -/
def pastRec {ℓ : ℕ} (u : PastData (ℓ + 1)) (j : ℕ) : ℝ≥0 → ℝ :=
  if hj : j < ℓ + 1 then Sec7.StripSideHeightProb.recW (u ⟨j, hj⟩) else fun _ => 0

theorem stageDrv_eq_pastRec {Ω : Type*} (κ : ℝ) (b : ℝ → ℝ) (J : Finset ℝ) (spec : ExplSpec)
    (E : ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞) (ℓ : ℕ) (ω : Ω) :
    stageDrv κ b J spec E ℓ ω = pastRec (pastMap κ b J spec E (ℓ + 1) ω) := rfl

theorem measurable_pastRec_apply (ℓ j : ℕ) (t : ℝ≥0) : Measurable fun u : PastData (ℓ + 1) => pastRec u j t := by
  unfold pastRec
  split_ifs with hj
  · exact (LocalExt.measurable_histDrv_apply (nL := 0) (nR := 0) t).comp
      (measurable_recHist.comp (measurable_pi_apply _))
  · exact measurable_const

/-- **The staged driver through the end of piece `ℓ`, read off a retained past.** -/
def pastDrv (sc : Schedule) {ℓ : ℕ} (u : PastData (ℓ + 1)) : ℝ≥0 → ℝ := catN (pastRec u) (schedD sc) ℓ

theorem measurable_pastDrv (sc : Schedule) (ℓ : ℕ) : Measurable fun u : PastData (ℓ + 1) => pastDrv sc u :=
  measurable_catN_family (fun j => measurable_pi_iff.2 fun t => measurable_pastRec_apply ℓ j t) _ ℓ

/-- **The flow history stopped at `q`, read off a retained past.** -/
def pastHist (sc : Schedule) (q : ℝ≥0) {ℓ : ℕ} (u : PastData (ℓ + 1)) : HistorySpace 0 0 :=
  ((q : ℝ≥0∞), fun p => if dyadicTime p ≤ q then (pastDrv sc u (dyadicTime p), Fin.elim0, Fin.elim0) else 0)

theorem measurable_pastHist (sc : Schedule) (q : ℝ≥0) (ℓ : ℕ) :
    Measurable fun u : PastData (ℓ + 1) => pastHist sc q u := by
  refine measurable_const.prodMk (measurable_pi_iff.2 fun p => ?_)
  by_cases hp : dyadicTime p ≤ q
  · simp only [hp, ↓reduceIte]
    refine Measurable.prodMk ((measurable_pi_apply _).comp (measurable_pastDrv sc ℓ)) ?_
    exact measurable_const.prodMk measurable_const
  · simp only [hp, ↓reduceIte]
    exact measurable_const

variable {κ : ℝ} {c₀ : BoundaryWord} {Ω : Type*} {E : ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞} {sc : Schedule} {ω : Ω}

/-- **On the good schedule event, the flow history of the joined driver stopped at the end of piece `ℓ` is the
history read off the retained past.** -/
theorem stopHistory_killedHistory_joinProc (hg : IsGoodSched sc E ω) (hreg : ∀ j ω, IsRegularDriver (E j ω))
    {ℓ : ℕ} (hn : ℓ + 1 ≤ schedL sc) :
    Sec4.stopHistory (fun _ => cumT (schedD sc) ℓ)
        (killedHistory (joinProc sc E) (Fin.elim0 : Fin 0 → ℝ≥0 → Ω → ℝ) (Fin.elim0 : Fin 0 → ℝ≥0 → Ω → ℝ)
          (fun _ => ⊤) ω) =
      pastHist sc (cumT (schedD sc) ℓ) (pastMap κ c₀.fn c₀.jumps (scheduleSpec sc) E (ℓ + 1) ω) := by
  refine Prod.ext rfl (funext fun p => ?_)
  simp only [Sec4.stopHistory, killedHistory, pastHist]
  by_cases hp : dyadicTime p ≤ cumT (schedD sc) ℓ
  · simp only [hp, ↓reduceIte, ENNReal.coe_lt_top]
    refine Prod.ext ?_ (Prod.ext (funext fun i => i.elim0) (funext fun i => i.elim0))
    show joinW sc E ω (dyadicTime p) = pastDrv sc (pastMap κ c₀.fn c₀.jumps (scheduleSpec sc) E (ℓ + 1) ω)
      (dyadicTime p)
    rw [IsGoodSched.joinW_eq_catN_stageDrv (κ := κ) (c₀ := c₀) hg hreg hn hp]
    rfl
  · simp only [hp, ↓reduceIte]

end Past

/-! ### The candidate's stopped data are events of DEPTH's σ-algebras -/

section Cand

variable (x₀ : ℝ) (h44 : Theorem12ParamCond44Statement.{0}) {κ a b a' b' : ℝ} (hκ : 0 < κ) (hκ4 : κ < 4)
  (hb : IsFig51Bounds κ a b a' b') {Ω : Type} [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω]
  (P : Measure Ω) [IsProbabilityMeasure P] (h : Ω → DistOn upperHalfPlaneOpens) (W : ℝ≥0 → Ω → ℝ)
  (ζ : Ω → ℝ≥0∞)

include hκ4 in
/-- **The stopped data of the candidate at the own time `q` are read off the retained past**, almost surely on the
glued space. -/
theorem ae_stopD_cand_eq (hG : IsStripGFF κ P h (fig51Lower a b) (fig51Upper x₀ a' b') {0} {x₀})
    {ℓ : ℕ} {t : Fin ℓ → ℝ≥0} (hv : IsValid ℓ t) {q : ℚ} (hq : lastO ℓ t < q) (s : ℝ≥0) :
    ∀ᵐ p ∂(candMu x₀ (κ := κ) P h W ζ hG.1),
      stopD (candW x₀ h44 hκ hκ4 hb h ℓ t) (Fin.elim0 : Fin 0 → ℝ≥0 → Ω → ℝ) (Fin.elim0 : Fin 0 → ℝ≥0 → Ω → ℝ)
          (fun _ => ⊤) q s p =
        (pastHist (mkSched ℓ t q) (q : ℝ).toNNReal (pastMap κ (sourceWord (x₀ := x₀) hκ hb).fn
          (sourceWord (x₀ := x₀) hκ hb).jumps (scheduleSpec (mkSched ℓ t q))
          (Prop59Sched.schedDrivers h44 hκ hκ4 (sourceWord (x₀ := x₀) hκ hb) (mkSched ℓ t q) (qField x₀ κ h))
          (ℓ + 1) p.1), cfStop s p.2) := by
  set c := sourceWord (x₀ := x₀) hκ hb with hc
  have hh : IsGFFWithBoundaryData P (qField x₀ κ h) c.fn c.jumps := sourceWord_gff hκ hb hG
  have hE := Prop59Sched.isStagedHistory_schedDrivers h44 hκ hκ4 c (sourceWord_extreme hκ hb) hh (mkSched ℓ t q)
  have hreg := Prop59Sched.schedDrivers_regular h44 hκ hκ4 c (mkSched ℓ t q) (qField x₀ κ h)
  have hgs := ae_isGoodSched h44 hκ hκ4 c (sourceWord_extreme hκ hb) hh (mkSched ℓ t q) hE hreg
  have hgs' : ∀ᵐ p ∂(candMu x₀ (κ := κ) P h W ζ hG.1),
      IsGoodSched (mkSched ℓ t q) (Prop59Sched.schedDrivers h44 hκ hκ4 c (mkSched ℓ t q) (qField x₀ κ h)) p.1 :=
    WangWu.ae_glue_fst (X := fun ω => cfFieldT κ (π / 2) (rootField (κ := κ) (x₀ := x₀) h ω))
      (candK x₀ (κ := κ) P h W ζ)
      ((measurable_cfFieldT κ (π / 2)).comp (measurable_rootField (κ := κ) (x₀ := x₀) hG.1)) hgs
  have hW : candW x₀ h44 hκ hκ4 hb h ℓ t =
      joinProc (mkSched ℓ t q) (Prop59Sched.schedDrivers h44 hκ hκ4 c (mkSched ℓ t q) (qField x₀ κ h)) :=
    (joinProc_mkSched_eq_qDrv h44 hκ hκ4 c (qField x₀ κ h) hv hq).symm
  filter_upwards [hgs'] with p hp
  have hcum := cumT_schedD_mkSched hv hq
  have key := stopHistory_killedHistory_joinProc (κ := κ) (c₀ := c) hp hreg (schedL_mkSched hv hq).ge
  rw [hcum] at key
  rw [stopD, hW, key]

include hκ4 in
/-- **Every event of the candidate's stopped data at the own time `q` is, almost surely, an event of DEPTH's
σ-algebra for `mkSched ℓ t q`.** -/
theorem exists_candSigma_ae_eq_stopD (hG : IsStripGFF κ P h (fig51Lower a b) (fig51Upper x₀ a' b') {0} {x₀})
    (us : ℂ → ℝ) {ℓ : ℕ} {t : Fin ℓ → ℝ≥0} (hv : IsValid ℓ t) {q : ℚ} (hq : lastO ℓ t < q) (s : ℝ≥0)
    {C : Set (Y49 0 0)} (hC : MeasurableSet C) :
    ∃ B, MeasurableSet[candSigma x₀ h44 hκ hκ4 hb h us ℓ t q s] B ∧
      B =ᵐ[candMu x₀ (κ := κ) P h W ζ hG.1]
        stopD (candW x₀ h44 hκ hκ4 hb h ℓ t) (Fin.elim0 : Fin 0 → ℝ≥0 → Ω → ℝ)
          (Fin.elim0 : Fin 0 → ℝ≥0 → Ω → ℝ) (fun _ => ⊤) q s ⁻¹' C := by
  set c := sourceWord (x₀ := x₀) hκ hb with hc
  set Z : PastData (ℓ + 1) × HistorySpace 0 0 → Y49 0 0 := fun z => (pastHist (mkSched ℓ t q) (q : ℝ).toNNReal z.1,
    cfStop s z.2) with hZ
  have hZm : Measurable[(inferInstance : MeasurableSpace (PastData (ℓ + 1))).prod (stopSigma s)] Z := by
    refine Measurable.prodMk ((measurable_pastHist _ _ ℓ).comp ?_) ?_
    · exact measurable_fst
    · have h2 : Measurable[stopSigma s] fun y : HistorySpace 0 0 => cfStop s y :=
        fun B hB => ⟨B, hB, rfl⟩
      exact h2.comp measurable_snd
  refine ⟨(fun p : Ω × HistorySpace 0 0 => (pastMap κ c.fn c.jumps (scheduleSpec (mkSched ℓ t q))
      (Prop59Sched.schedDrivers h44 hκ hκ4 c (mkSched ℓ t q) (qField x₀ κ h)) (ℓ + 1) p.1, p.2)) ⁻¹' (Z ⁻¹' C),
    le_sup_right (a := germSigma _ _) _ ⟨Z ⁻¹' C, hZm hC, rfl⟩, ?_⟩
  filter_upwards [ae_stopD_cand_eq x₀ h44 hκ hκ4 hb P h W ζ hG hv hq s] with p hp
  show (Z (_, p.2) ∈ C) = (stopD _ _ _ _ q s p ∈ C)
  rw [hp]

/-- Word49's marks σ-algebra is the σ-algebra of the stopped data. -/
theorem cfGlueMarks_eq_comap_stopD {Ω' : Type*} [MeasurableSpace Ω'] (Wj : ℝ≥0 → Ω' → ℝ) (q : ℚ) (s : ℝ≥0) :
    cfGlueMarks Wj (Fin.elim0 : Fin 0 → ℝ≥0 → Ω' → ℝ) (Fin.elim0 : Fin 0 → ℝ≥0 → Ω' → ℝ) (fun _ => ⊤)
        (q : ℝ).toNNReal s =
      MeasurableSpace.comap (stopD Wj (Fin.elim0 : Fin 0 → ℝ≥0 → Ω' → ℝ) (Fin.elim0 : Fin 0 → ℝ≥0 → Ω' → ℝ)
        (fun _ => ⊤) q s) inferInstance := by
  have e : stopD Wj (Fin.elim0 : Fin 0 → ℝ≥0 → Ω' → ℝ) (Fin.elim0 : Fin 0 → ℝ≥0 → Ω' → ℝ) (fun _ => ⊤) q s =
      fun p => (Sec4.stopHistory (fun _ => (q : ℝ).toNNReal) (killedHistory Wj (Fin.elim0 : Fin 0 → ℝ≥0 → Ω' → ℝ)
        (Fin.elim0 : Fin 0 → ℝ≥0 → Ω' → ℝ) (fun _ => ⊤) p.1), Sec4.stopHistory (fun _ => s) p.2) := rfl
  rw [e]
  change _ = MeasurableSpace.comap _ ((inferInstance : MeasurableSpace (HistorySpace 0 0)).prod inferInstance)
  rw [MeasurableSpace.comap_prodMk, cfGlueMarks, stopSigma, stopSigma, MeasurableSpace.comap_comp,
    MeasurableSpace.comap_comp]
  rfl

include hκ4 in
/-- **Every event of Word49's marks σ-algebra of the candidate at the own time `q` is, almost surely, an event of
DEPTH's σ-algebra for `mkSched ℓ t q`.** This transfers the template's `exists_marks_ae_eq_inter` and
`exists_marks_ae_eq_avoid` (stated for `cfGlueMarks`) to the conditioning σ-algebras of (SW3). -/
theorem exists_candSigma_ae_eq_of_cfGlueMarks (hG : IsStripGFF κ P h (fig51Lower a b) (fig51Upper x₀ a' b') {0} {x₀})
    (us : ℂ → ℝ) {ℓ : ℕ} {t : Fin ℓ → ℝ≥0} (hv : IsValid ℓ t) {q : ℚ} (hq : lastO ℓ t < q) (s : ℝ≥0)
    {A : Set (Ω × HistorySpace 0 0)}
    (hA : MeasurableSet[cfGlueMarks (candW x₀ h44 hκ hκ4 hb h ℓ t) (Fin.elim0 : Fin 0 → ℝ≥0 → Ω → ℝ)
      (Fin.elim0 : Fin 0 → ℝ≥0 → Ω → ℝ) (fun _ => ⊤) (q : ℝ).toNNReal s] A) :
    ∃ B, MeasurableSet[candSigma x₀ h44 hκ hκ4 hb h us ℓ t q s] B ∧ B =ᵐ[candMu x₀ (κ := κ) P h W ζ hG.1] A := by
  rw [cfGlueMarks_eq_comap_stopD] at hA
  obtain ⟨C, hC, rfl⟩ := hA
  exact exists_candSigma_ae_eq_stopD x₀ h44 hκ hκ4 hb P h W ζ hG us hv hq s hC

end Cand

end InteractingSLE.Sec5.CrossCond.StagedS4
