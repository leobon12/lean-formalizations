/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW2RqBad
import InteractingSLE.Spec.Supplement.GW2SdeRecord
import InteractingSLE.Spec.Supplement.GW4SafeRNextWord
import InteractingSLE.Spec.Supplement.GW4RelMatch
import InteractingSLE.Spec.Seal.PrepStatements
import InteractingSLE.Spec.Supplement.GW2RdHitSet
import InteractingSLE.Spec.Sec5.Lemma56Stages

/-!
# A safe relative piece never visits the avoided set of its word (decision D33)

PROVE-GW2-ROOTX round 8. For the inputs of SDE's `GW2Sde.ae_exists_isStopped_of_relSafe` (K2's safe law on every word
type, the engine's stop rules, the conditional Gaussian law of the relative field given the record), almost surely on the
record event the relative driver `R` has no bad visit of `avoidQ κ 0 (β rec)` before `V`
(**`ae_not_badQ_of_relSafe`**). No announcing sequence is needed:

* under `condExpKernel P (comap rec) ω₀` the relative field is a GFF with the data of `β₀ = β (rec ω₀)`
  (`Exist.StagedLaw.ae_isGFFWithBoundaryData_condExpKernel`); its field-determined driver `BRLeaf.cfDrv` is the
  driver of the FULL angle-`0` flow line (`GW4Fix.isFlowLineDriver_cfDrv_word`), which has a generating trace
  (`Seal.Prep.ae_exists_isGeneratingTrace_of_statement`) and avoids `avoidQ κ 0 β₀` up to its lifetime
  (`GW2Rq.ae_avoidQ`);
* `R` is that driver before `V` (`GW2Rd.ae_isStopDrvMatch_rec`, `GW4Rel.ae_cfDrv_eq_of_match`), so `LP.traceAt t R`
  is the flow line's trace for `t < V` (`LP.traceAt_congr`, `LP.traceAt_eq_of_isGeneratingTrace`);
* the event is measurable (`measurableSet_badQ`), so it holds `P`-almost surely
  (`Sec5.Lemma56Stages.ae_of_ae_condExpKernel`).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal
open QuantumZipper (chiC)
open LQGMetric (DistOn TestOn)

universe u

namespace InteractingSLE.Theorem14.GW2Rq

open GW2KM2 Restart Exist Exist.StagedLaw Supp8.GB6 Supp8.GB6.RelDrv Supp8.Q3Stop Supp8.GB6.HullId

/-- **A safe relative piece never visits the avoided set of its word before `V`.** -/
theorem ae_not_badQ_of_relSafe (h12p : Exist.Staged.Theorem12ParamStatement.{u})
    (h13 : Exist.Theorem13Statement.{u}) {κ : ℝ} (hκ : 0 < κ) (hκ4 : κ < 4)
    {Fd : BoundaryWord × DistOn upperHalfPlaneOpens → Sec2.Assembly.PCode × ℝ≥0∞}
    (hFd : IsCanonicalDriverCode κ 0 Fd)
    {Ω : Type u} [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {β : RecData → BoundaryWord} (hβ : Measurable β) {E : Set RecData} (hE : MeasurableSet E)
    (hcount : (range fun r : RecData => wordType κ (β r)).Countable) (hsort : ∀ r ∈ E, (β r).IsSorted)
    {rec : Ω → RecData} (hrecm : Measurable rec) {Hr : Ω → DistOn upperHalfPlaneOpens} (hHr : Measurable Hr)
    {R : ℝ≥0 → Ω → ℝ} (hRm : ∀ t, Measurable (R t)) (hRc : ∀ ω, Continuous fun t => R t ω)
    (hR0 : ∀ ω, R 0 ω = 0) {V : Ω → ℝ≥0∞} (hVm : Measurable V)
    (hS : ∀ w : WordType, HasRelSafe κ w β E (P.map fun ω => (rec ω, relVar Hr R V ω)))
    (hV0 : ∀ᵐ ω ∂P, rec ω ∈ E → 0 < V ω)
    {ρ : RecData × (ℝ≥0 → ℝ) → ℝ≥0∞} (hρm : Measurable ρ) (hρ : IsPathRule ρ)
    (hVρ : ∀ᵐ ω ∂P, V ω = ρ (rec ω, fun u => R u ω))
    {ρs : ℕ → RecData × (ℝ≥0 → ℝ) → ℝ≥0∞} (hρsm : ∀ n, Measurable (ρs n)) (hρs : ∀ n, IsPathRule (ρs n))
    (hρsfin : ∀ n x, ρs n x ≠ ⊤) (hρsmono : ∀ x, Monotone fun n => ρs n x)
    (hρslt : ∀ᵐ ω ∂P, rec ω ∈ E → ∀ n, ρs n (rec ω, fun u => R u ω) < V ω)
    (hρssup : ∀ᵐ ω ∂P, rec ω ∈ E → ⨆ n, ρs n (rec ω, fun u => R u ω) = V ω)
    (hG : ∀ φ : TestOn upperHalfPlaneOpens, ∀ᵐ ω ∂P, rec ω ∈ E →
      P[fun ω' => Complex.exp (Complex.I * (Hr ω' φ : ℂ)) | MeasurableSpace.comap rec inferInstance] ω =
        gaussCF (β (rec ω)) φ) :
    ∀ᵐ ω ∂P, rec ω ∈ E → ¬ BadQ κ 0 (β (rec ω)) (fun q => LP.traceAt q (fun u => R u ω)) (V ω) := by
  classical
  have h𝒢 : MeasurableSpace.comap rec inferInstance ≤ mΩ := hrecm.comap_le
  have hmatch := GW2Rd.ae_isStopDrvMatch_rec hκ hFd hβ hE hcount hrecm hHr hRm hRc hR0 hVm hS hV0 hρm hρ hVρ
    hρsm hρs hρsfin hρsmono hρslt hρssup
  have hker := Sec7.Aux122Disint.ae_ae_condExpKernel h𝒢 hmatch
  have hconst := Exist.Staged.ae_ae_eq_of_comap (P := P) hrecm
  have hgff := ae_isGFFWithBoundaryData_condExpKernel (P := P) h𝒢 (M := rec ⁻¹' E) (β := fun ω => β (rec ω))
    (Eventually.of_forall fun ω hω => hsort _ hω) hHr hG
  -- the measurable good event
  have hRpm : Measurable fun ω => (fun u => R u ω) := measurable_pi_iff.2 hRm
  have hΓm : ∀ q : ℝ≥0, Measurable fun ω => LP.traceAt q (fun u => R u ω) := fun q =>
    (LP.measurable_traceAt q).comp hRpm
  set G : Set Ω := {ω | rec ω ∈ E → ¬ BadQ κ 0 (β (rec ω)) (fun q => LP.traceAt q (fun u => R u ω)) (V ω)}
    with hGdef
  have hGm : MeasurableSet G := by
    have h1 := (measurableSet_badQ κ 0 (hβ.comp hrecm) hΓm hVm).compl
    exact ((hrecm hE).compl.union h1).congr (by
      ext ω; simp only [hGdef, mem_union, mem_compl_iff, mem_preimage, mem_ofPred_eq, Function.comp_apply]; tauto)
  refine Sec5.Lemma56Stages.ae_of_ae_condExpKernel h𝒢 hGm ?_
  filter_upwards [hker, hconst, hgff] with ω₀ hk hc hX
  by_cases hω₀ : rec ω₀ ∈ E
  swap
  · filter_upwards [hc] with ω hcω hωE
    exact absurd (hcω ▸ hωE) hω₀
  set ν := condExpKernel P (MeasurableSpace.comap rec inferInstance) ω₀ with hν
  set β₀ := β (rec ω₀) with hβ₀
  have hX' : IsGFFWithBoundaryData ν Hr β₀.fn β₀.jumps := hX hω₀
  have hmatchν : ∀ᵐ ω ∂ν, IsStopDrvMatch (Fd (β₀, Hr ω)) (fun t => R t ω) (V ω) := by
    filter_upwards [hk, hc] with ξ h1 h2
    rw [hβ₀, ← h2]
    exact h1 (h2 ▸ hω₀)
  have hcmp := GW4Rel.ae_cfDrv_eq_of_match h12p h13 hκ hFd (hsort _ hω₀) hX' hRc hmatchν
  set D : Ω → (ℝ≥0 → ℝ) × ℝ≥0∞ := fun ω => BRLeaf.cfDrv h12p hκ β₀ (Hr ω) with hD
  have hFL := GW4Fix.isFlowLineDriver_cfDrv_word h12p h13 hκ β₀ hX'
  have hFL' := hFL
  obtain ⟨_, _, _, _, _, _, hcpl⟩ := hFL'
  have hEv := hcpl.1
  have htr := Seal.Prep.ae_exists_isGeneratingTrace_of_statement h13 hκ
    (Theorem15.isOrderedForceWord_flowLine β₀.fn β₀.jumps 0) hEv
  -- the chosen trace
  set η : Ω → ℝ≥0 → ℂ := fun ω =>
    if h : ∃ η', IsGeneratingTrace (fun t => (D ω).1 t) (D ω).2 η' then h.choose else fun _ => 0 with hηdef
  have hgen : ∀ᵐ ω ∂ν, IsGeneratingTrace (fun t => (D ω).1 t) (D ω).2 (η ω) := by
    filter_upwards [htr] with ω hω
    have hex : ∃ η', IsGeneratingTrace (fun t => (D ω).1 t) (D ω).2 η' := by
      obtain ⟨-, η', h', -⟩ := hω
      exact ⟨η', h'⟩
    simp only [hηdef, hex, ↓reduceDIte]
    exact hex.choose_spec
  have hfl := GW2Rd.isFlowLine_of_driver hFL hgen
  have hav := ae_avoidQ hκ hκ4 β₀.isPiecewiseConstantBoundaryData hX' hfl (β := β₀) (F := ∅) fun _ _ => rfl
  filter_upwards [hav, hcmp, hgen, hc] with ω hav' hcm hg hcω hωE hbad
  rw [hcω, ← hβ₀] at hbad
  have hreg := Exist.Staged.drvOf_regular (Exist.Staged.detCode
    (Exist.Staged.paramΦ h12p hκ (flowLineNL β₀.fn β₀.jumps 0) (flowLineNR β₀.fn β₀.jumps 0))
      (((flowLineXL β₀.fn β₀.jumps 0, flowLineXR β₀.fn β₀.jumps 0),
        (flowLineRhoL κ β₀.fn β₀.jumps 0 0, flowLineRhoR κ β₀.fn β₀.jumps 0 0)), Hr ω))
  have hΓeq : ∀ t : ℝ≥0, (t : ℝ≥0∞) < V ω → LP.traceAt t (fun u => R u ω) = η ω t := by
    intro t ht
    have hcong : LP.traceAt t (fun u => R u ω) = LP.traceAt t (fun u => (D ω).1 u) :=
      LP.traceAt_congr fun r hr => (hcm.2 r (lt_of_le_of_lt (ENNReal.coe_le_coe.2 hr) ht)).symm
    rw [hcong]
    exact LP.traceAt_eq_of_isGeneratingTrace hg hreg.1 hreg.2.1 (lt_of_lt_of_le ht hcm.1)
  have hcont : ContinuousOn (fun t => LP.traceAt t (fun u => R u ω)) {t | (t : ℝ≥0∞) < V ω} := by
    refine (hg.2.1.mono fun t (ht : (t : ℝ≥0∞) < V ω) => ?_).congr fun t ht => hΓeq t ht
    exact (lt_of_lt_of_le ht hcm.1).le
  obtain ⟨t, ht, hm⟩ := exists_mem_avoidQ_of_badQ hcont hbad
  rw [hΓeq t ht] at hm
  exact hav' t (lt_of_lt_of_le ht hcm.1).le hm

/-- **A safe stage variable never visits the avoided set of its word before its cap** (the conditional Gaussian law is
part of K2's safe law, `GW2Sde.ae_condExp_eq_gaussCF_of_relSafe`). -/
theorem _root_.InteractingSLE.Theorem14.GW2Sde.StageVar.IsSafe.ae_not_badQ
    (h12p : Exist.Staged.Theorem12ParamStatement.{u}) (h13 : Exist.Theorem13Statement.{u}) {κ : ℝ} (hκ : 0 < κ)
    (hκ4 : κ < 4) {Fd : BoundaryWord × DistOn upperHalfPlaneOpens → Sec2.Assembly.PCode × ℝ≥0∞}
    (hFd : IsCanonicalDriverCode κ 0 Fd) {Ω : Type u} [MeasurableSpace Ω] [StandardBorelSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {rec : Ω → RecData} (hrecm : Measurable rec) {v : GW2Sde.StageVar Ω}
    (hv : v.IsSafe κ P rec) :
    ∀ᵐ ω ∂P, rec ω ∈ v.E → ¬ BadQ κ 0 (v.β (rec ω)) (fun q => LP.traceAt q (fun u => v.R u ω)) (v.V ω) :=
  ae_not_badQ_of_relSafe h12p h13 hκ hκ4 hFd hv.measurable_β hv.measurableSet_E hv.countable_wordType
    hv.isSorted hrecm hv.measurable_Hr hv.measurable_R hv.continuous_R hv.R_zero hv.measurable_V hv.relSafe
    hv.V_pos hv.measurable_ρ hv.isPathRule_ρ hv.V_eq hv.measurable_ρs hv.isPathRule_ρs hv.ρs_ne_top hv.ρs_mono
    hv.ρs_lt hv.ρs_iSup fun φ => GW2Sde.ae_condExp_eq_gaussCF_of_relSafe hκ hv.measurable_β hv.measurableSet_E
      hv.countable_wordType hv.isSorted hrecm hv.measurable_Hr hv.measurable_R hv.measurable_V hv.relSafe hv.V_pos φ

end InteractingSLE.Theorem14.GW2Rq
