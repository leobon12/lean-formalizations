/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec5.StagedS4Gal

/-!
# Almost every glued sample is good for the candidate's driver

Packet PROVE-STAGED-S4. On the glued space of the root coupling (`candMu`), almost surely the candidate's staged path
is a proper arc and a good path (continuous driver from `0`, `ζ = ⊤`) and the counterflow history is good at the
counterflow time `s`; hence the sample lies in the good glued set `candEg` (**`ae_good_cand`**). This is the input of
Word49's stopped-data descriptions (`isGoodD_stopD`, `mem_PcD_stopD_iff`, `gammaD_stopD`, which need
`p ∈ E ∧ Aux50Hit.IsGoodPath …`) and of the filtration clauses (`filtClauses`) for the candidate.

R48: only `h44` (R74) is used.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped NNReal ENNReal Real
open QuantumZipper (chiC)
open LQGMetric (DistOn TestOn)

namespace InteractingSLE.Sec5.CrossCond.StagedS4

open WangWu hiding ratPt exists_ratPt_dist_lt
open WangWu.ImgWord LawUnique GlueCond Cond44Ref CfRegQ Prop411Q Word49 Theta StagedS3
open Restart Exist.StagedLaw Exist.Staged
open Sec7.AdmCode Prop513TreeExtract Prop513Schedule Prop513Target StagedGlue StagedDepth Prop59Pieces StagedRepLater
open Sec4 (IsStripGFF IsStripCounterflowDriver)

section Cand

variable (x₀ : ℝ) (h44 : Theorem12ParamCond44Statement.{0}) {κ a b a' b' : ℝ} (hκ : 0 < κ) (hκ4 : κ < 4)
  (hb : IsFig51Bounds κ a b a' b') {Ω : Type} [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω]
  (P : Measure Ω) [IsProbabilityMeasure P] (h : Ω → DistOn upperHalfPlaneOpens) (W : ℝ≥0 → Ω → ℝ)
  (ζ : Ω → ℝ≥0∞)

include hκ4 in
/-- **Almost every glued sample is good for the candidate's driver**: it lies in `candEg`, the candidate's driver is a
good path (`ζ = ⊤`, continuous from `0`), and the staged trace is a proper arc. -/
theorem ae_good_cand (hG : IsStripGFF κ P h (fig51Lower a b) (fig51Upper x₀ a' b') {0} {x₀})
    (hcf : IsStripCounterflowDriver κ 0 (Real.exp (π * x₀)) P h W ζ) (ℓ : ℕ) (t : Fin ℓ → ℝ≥0) (hv : IsValid ℓ t)
    {s : ℝ≥0} (hs : 0 < s) :
    ∀ᵐ p ∂(candMu x₀ (κ := κ) P h W ζ hG.1), p ∈ candEg x₀ h44 hκ hκ4 hb P h W ζ hG.1 ℓ t s ∧
      Aux50Hit.IsGoodPath (candW x₀ h44 hκ hκ4 hb h ℓ t) (Fin.elim0 : Fin 0 → ℝ≥0 → Ω → ℝ)
        (Fin.elim0 : Fin 0 → ℝ≥0 → Ω → ℝ) (fun _ => ⊤) p.1 ∧
      IsProperArc (seedLine (fun _ => ⊤) (candW x₀ h44 hκ hκ4 hb h ℓ t) p.1) := by
  set c := sourceWord (x₀ := x₀) hκ hb with hc
  have hhm : Measurable h := hG.1
  obtain ⟨_, 𝓕, VL, VR, B, hC⟩ := exists_rootCoupling h44 hκ hκ4 hb (P := P) hhm hG
  have hcfc := isCenteredCounterflowDriver_of_strip hκ hcf
  have hcfm := measurable_cfHistory_of_strip hcf
  have hqm : Measurable (qField x₀ κ h) := (measurable_targetField κ (Real.exp (π * x₀)) (Real.exp_pos _)).comp hhm
  have hk : P.map (fun ω => (qField x₀ κ h ω, Cond44Ref.cfHistory W ζ ω)) =
      P.map (qField x₀ κ h) ⊗ₘ candK x₀ (κ := κ) P h W ζ :=
    (compProd_map_condDistrib hqm.aemeasurable hcfm.aemeasurable).symm
  have hlaw : P.map (fun ω => cfFieldT κ (π / 2) (rootField (κ := κ) (x₀ := x₀) h ω)) = P.map (qField x₀ κ h) := by
    congr 1
    funext ω
    rw [cfFieldT_pi_div_two]
    exact cfField_rootField ω
  have hF := Theorem15.isOrderedForceWord_flowLine c.fn c.jumps 0
  have h44' : Sec4.Cond44 κ (flowLineRhoL κ c.fn c.jumps 0 (π / 2)) (flowLineRhoR κ c.fn c.jumps 0 (π / 2)) :=
    cond44_upper hκ (sourceWord_extreme hκ hb)
  have hθb := cfThetaBounds_of_cond44 hκ hκ4 hF h44'
  have hh : IsGFFWithBoundaryData P (qField x₀ κ h) c.fn c.jumps := sourceWord_gff hκ hb hG
  set sc := candSched ℓ t with hsc
  have hlt : lastO ℓ t < lastO ℓ t + 1 := lt_add_one _
  have hE := Prop59Sched.isStagedHistory_schedDrivers h44 hκ hκ4 c (sourceWord_extreme hκ hb) hh sc
  have hreg := Prop59Sched.schedDrivers_regular h44 hκ hκ4 c sc (qField x₀ κ h)
  have hXm : Measurable fun ω => cfFieldT κ (π / 2) (rootField (κ := κ) (x₀ := x₀) h ω) :=
    (measurable_cfFieldT κ (π / 2)).comp (measurable_rootField (κ := κ) (x₀ := x₀) hhm)
  have hGg := WangWu.ae_glue_fst (X := fun ω => cfFieldT κ (π / 2) (rootField (κ := κ) (x₀ := x₀) h ω))
    (candK x₀ (κ := κ) P h W ζ) hXm (ae_schedule_goodPath h44 hκ hκ4 c (sourceWord_extreme hκ hb) hh sc hE hreg)
  have hcfg := ae_cfGood_glueT hκ hC hθb hcfc hlaw (candK x₀ (κ := κ) P h W ζ) hk hs
  have hW : candW x₀ h44 hκ hκ4 hb h ℓ t = joinProc sc (Prop59Sched.schedDrivers h44 hκ hκ4 c sc (qField x₀ κ h)) :=
    (joinProc_mkSched_eq_qDrv h44 hκ hκ4 c (qField x₀ κ h) hv hlt).symm
  have hgood : ∀ᵐ p ∂(candMu x₀ (κ := κ) P h W ζ hG.1),
      IsGood49 s (fun _ => ⊤) (candW x₀ h44 hκ hκ4 hb h ℓ t) p ∧
      Aux50Hit.IsGoodPath (candW x₀ h44 hκ hκ4 hb h ℓ t) (Fin.elim0 : Fin 0 → ℝ≥0 → Ω → ℝ)
        (Fin.elim0 : Fin 0 → ℝ≥0 → Ω → ℝ) (fun _ => ⊤) p.1 ∧
      IsProperArc (seedLine (fun _ => ⊤) (candW x₀ h44 hκ hκ4 hb h ℓ t) p.1) := by
    filter_upwards [hGg, hcfg] with p hgp ⟨_, hy⟩
    obtain ⟨hjc, hj0, hαp, -⟩ := properArc_seedLine_joinProc sc (fun j => hreg j p.1) hgp
    rw [hW]
    refine ⟨isGood49_of_mem hαp hy, ⟨rfl, hj0, ?_, fun i => i.elim0, fun i => i.elim0⟩, hαp⟩
    exact hjc.continuousOn
  filter_upwards [hgood, ae_mem_glueGood (hgood.mono fun p hp => hp.1)] with p hp hpE
  exact ⟨hpE, hp.2⟩

end Cand

end InteractingSLE.Sec5.CrossCond.StagedS4
