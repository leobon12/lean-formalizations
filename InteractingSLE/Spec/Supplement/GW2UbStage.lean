/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW2UbNull
import InteractingSLE.Spec.Supplement.GW2UbStmt
import InteractingSLE.Spec.Supplement.GW2RvInst
import InteractingSLE.Spec.Supplement.GW2RuRead
import InteractingSLE.Spec.Supplement.GW2PsmVer
import InteractingSLE.Spec.Supplement.GW2WmDec
import InteractingSLE.Spec.Supplement.GW2RjBd

/-!
# The tip exclusion at the stage: one stage code for all versions

Packet PROVE-GW2-RELDET (round 38, decisions D73 route (ii) and D81). The tip exclusion reads the stage's canonical
driver code `Fd (β (srecX), Hr)` through every version of the stop family: each version matches it below its cap
(`Q3Stop.ae_isStopDrvMatch_of_hasRelSafe`), and at a tip contact the caps exhaust the relative clock. This needs one
code for all versions.

* (D81's angle check is STAGEMEAN's `GW2Pq.candAngle_mem_Ioo`: the candidate's angle lies in `Θ ⊆ Ioo (−π/2) (π/2)`,
  so `θa = ±π/2` does not occur.)
* **`stgStart_eq_and_agree`**: two root-`x` versions alive at the stage start (`physClockX T < V`) at a sample of the
  good set, with the history time before the contact, have the same stage start and agree up to it
  (`GW2Ru.version_eq_of_drv_eq`).
* **`stgPreRecX_eq_of_versions`**, **`schedChartX_eq_of_versions`**: hence the same stage prefix record and stage
  chart (`GW2Wm.recOf_congr_top`, `GW2Psm.stgChart_congr`), so the same stage record and stage field.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Filter MeasureTheory Topology
open scoped NNReal ENNReal
open LQGMetric (DistOn TestOn)

universe u

namespace InteractingSLE.Theorem14.GW2Rd

open Exist Staged StagedLaw Restart GW2TipSystem GW2TipSystem.RootC24 GW2Rz GW2Rv GW2Sde

section Versions

variable {Ω : Type u} [MeasurableSpace Ω]

/-- **Two versions alive at the stage start have the same stage start and agree up to it** (one sample). -/
theorem stgStart_eq_and_agree (c : SourceData Ω) (r : ScaledRootIdx c.Θ c.Q) (l : List (EntryIdx c.Θ c.Q)) (a : ℕ)
    {GT : Set Ω} (hGT : ∀ ω ∈ GT, PhysGoodX (rootPt r.1) c.s c.W c.ζ (schedW c r l a) (schedTr c r l a) c.α ω)
    (hs : 0 < c.s) (hx : 0 ≤ rootPt r.1) {R R' : ℝ≥0 → Ω → ℝ} {V V' : Ω → ℝ≥0∞} {ξ : Ω} (hξ : ξ ∈ GT)
    (hR : VersionAtX (rootPt r.1) c.s c.W c.ζ (schedW c r l a) (schedTr c r l a) c.α R V ξ)
    (hR' : VersionAtX (rootPt r.1) c.s c.W c.ζ (schedW c r l a) (schedTr c r l a) c.α R' V' ξ)
    (hTc : (RootJ31.historyTime c r l : ℝ≥0∞) < contactX (rootPt r.1) c.s (schedTr c r l a) c.α ξ)
    (hV : stgStartMX (rootPt r.1) c.s c.W c.ζ (schedW c r l a) GT V (RootJ31.historyTime c r l) ξ < V ξ)
    (hV' : stgStartMX (rootPt r.1) c.s c.W c.ζ (schedW c r l a) GT V' (RootJ31.historyTime c r l) ξ < V' ξ) :
    stgStartX (rootPt r.1) c.s c.W c.ζ (schedW c r l a) GT V (RootJ31.historyTime c r l) ξ =
        stgStartX (rootPt r.1) c.s c.W c.ζ (schedW c r l a) GT V' (RootJ31.historyTime c r l) ξ ∧
      ∀ u ≤ stgStartX (rootPt r.1) c.s c.W c.ζ (schedW c r l a) GT V (RootJ31.historyTime c r l) ξ,
        R u ξ = R' u ξ := by
  set T := RootJ31.historyTime c r l with hTdef
  set P := physClockX (rootPt r.1) c.s c.W c.ζ (schedW c r l a) GT T ξ with hPdef
  have hPV : P < V ξ := by
    by_contra h
    rw [not_lt] at h
    have : stgStartMX (rootPt r.1) c.s c.W c.ζ (schedW c r l a) GT V T ξ = V ξ := min_eq_right h
    exact absurd hV (by rw [this]; exact lt_irrefl _)
  have hPV' : P < V' ξ := by
    by_contra h
    rw [not_lt] at h
    have : stgStartMX (rootPt r.1) c.s c.W c.ζ (schedW c r l a) GT V' T ξ = V' ξ := min_eq_right h
    exact absurd hV' (by rw [this]; exact lt_irrefl _)
  have hM : stgStartMX (rootPt r.1) c.s c.W c.ζ (schedW c r l a) GT V T ξ = P := min_eq_left hPV.le
  have hM' : stgStartMX (rootPt r.1) c.s c.W c.ζ (schedW c r l a) GT V' T ξ = P := min_eq_left hPV'.le
  have hstart : stgStartX (rootPt r.1) c.s c.W c.ζ (schedW c r l a) GT V T ξ =
      stgStartX (rootPt r.1) c.s c.W c.ζ (schedW c r l a) GT V' T ξ := by
    show (stgStartMX (rootPt r.1) c.s c.W c.ζ (schedW c r l a) GT V T ξ).toNNReal =
      (stgStartMX (rootPt r.1) c.s c.W c.ζ (schedW c r l a) GT V' T ξ).toNNReal
    rw [hM, hM']
  refine ⟨hstart, fun u hu => ?_⟩
  have hPc : P = ENNReal.ofReal (clockX (rootPt r.1) c.s c.W c.ζ (schedW c r l a) T ξ) :=
    physClockX_eq_clockX hGT hs hx hξ hTc
  have hu' : u ≤ (clockX (rootPt r.1) c.s c.W c.ζ (schedW c r l a) T ξ).toNNReal := by
    have e : stgStartX (rootPt r.1) c.s c.W c.ζ (schedW c r l a) GT V T ξ =
        (clockX (rootPt r.1) c.s c.W c.ζ (schedW c r l a) T ξ).toNNReal := by
      show (stgStartMX (rootPt r.1) c.s c.W c.ζ (schedW c r l a) GT V T ξ).toNNReal = _
      rw [hM, hPc, ENNReal.ofReal, ENNReal.toNNReal_coe]
    rwa [e] at hu
  rcases eq_or_lt_of_le (zero_le : (0 : ℝ≥0) ≤ T) with hT0 | hT0
  · -- the history time is `0`: the clock is `0` there
    obtain ⟨-, -, h0⟩ := clockX_props hGT hs hx hξ
    rw [← hT0] at hu'
    have hc0 : clockX (rootPt r.1) c.s c.W c.ζ (schedW c r l a) 0 ξ ≤ 0 := ENNReal.ofReal_eq_zero.1 h0
    rw [Real.toNNReal_of_nonpos hc0] at hu'
    have hu0 : u = 0 := le_antisymm hu' zero_le
    rw [hu0, hR.2.1, hR'.2.1]
  · exact GW2Ru.version_eq_of_drv_eq hGT hGT hs hx hξ hξ hR hR' hT0 hTc hTc (fun t _ => rfl)
      (hPc ▸ hPV) (hPc ▸ hPV') u hu'

/-- **Two versions alive at the stage start have the same stage prefix record.** -/
theorem stgPreRecX_eq_of_versions (c : SourceData Ω) (r : ScaledRootIdx c.Θ c.Q) (l : List (EntryIdx c.Θ c.Q))
    (a : ℕ) {GT : Set Ω}
    (hGT : ∀ ω ∈ GT, PhysGoodX (rootPt r.1) c.s c.W c.ζ (schedW c r l a) (schedTr c r l a) c.α ω)
    (hs : 0 < c.s) (hx : 0 ≤ rootPt r.1) {R R' : ℝ≥0 → Ω → ℝ} {V V' : Ω → ℝ≥0∞} {ξ : Ω} (hξ : ξ ∈ GT)
    (hR : VersionAtX (rootPt r.1) c.s c.W c.ζ (schedW c r l a) (schedTr c r l a) c.α R V ξ)
    (hR' : VersionAtX (rootPt r.1) c.s c.W c.ζ (schedW c r l a) (schedTr c r l a) c.α R' V' ξ)
    (hTc : (RootJ31.historyTime c r l : ℝ≥0∞) < contactX (rootPt r.1) c.s (schedTr c r l a) c.α ξ)
    (hV : stgStartMX (rootPt r.1) c.s c.W c.ζ (schedW c r l a) GT V (RootJ31.historyTime c r l) ξ < V ξ)
    (hV' : stgStartMX (rootPt r.1) c.s c.W c.ζ (schedW c r l a) GT V' (RootJ31.historyTime c r l) ξ < V' ξ) :
    stgPreRecX (rootPt r.1) c.s c.W c.ζ (schedW c r l a) GT V (RootJ31.historyTime c r l) R ξ =
      stgPreRecX (rootPt r.1) c.s c.W c.ζ (schedW c r l a) GT V' (RootJ31.historyTime c r l) R' ξ := by
  obtain ⟨hstart, hag⟩ := stgStart_eq_and_agree c r l a hGT hs hx hξ hR hR' hTc hV hV'
  unfold stgPreRecX
  rw [← hstart]
  exact GW2Wm.recOf_congr_top hag

/-- **Two versions alive at the stage start have the same stage chart.** -/
theorem schedChartX_eq_of_versions (c : SourceData Ω) (r : ScaledRootIdx c.Θ c.Q) (l : List (EntryIdx c.Θ c.Q))
    (a : ℕ) {GT : Set Ω}
    (hGT : ∀ ω ∈ GT, PhysGoodX (rootPt r.1) c.s c.W c.ζ (schedW c r l a) (schedTr c r l a) c.α ω)
    (hs : 0 < c.s) (hx : 0 ≤ rootPt r.1) {R R' : ℝ≥0 → Ω → ℝ} {V V' : Ω → ℝ≥0∞} {ξ : Ω} (hξ : ξ ∈ GT)
    (hR : VersionAtX (rootPt r.1) c.s c.W c.ζ (schedW c r l a) (schedTr c r l a) c.α R V ξ)
    (hR' : VersionAtX (rootPt r.1) c.s c.W c.ζ (schedW c r l a) (schedTr c r l a) c.α R' V' ξ)
    (hTc : (RootJ31.historyTime c r l : ℝ≥0∞) < contactX (rootPt r.1) c.s (schedTr c r l a) c.α ξ)
    (hV : stgStartMX (rootPt r.1) c.s c.W c.ζ (schedW c r l a) GT V (RootJ31.historyTime c r l) ξ < V ξ)
    (hV' : stgStartMX (rootPt r.1) c.s c.W c.ζ (schedW c r l a) GT V' (RootJ31.historyTime c r l) ξ < V' ξ) :
    schedChartX c r l a GT R V ξ = schedChartX c r l a GT R' V' ξ := by
  obtain ⟨hstart, hag⟩ := stgStart_eq_and_agree c r l a hGT hs hx hξ hR hR' hTc hV hV'
  unfold schedChartX
  rw [← hstart]
  exact GW2Psm.stgChart_congr _ hR.1 hR'.1 hag

end Versions

section Match

variable {Ω : Type u} [MeasurableSpace Ω]

/-- **The zero stop** (a stage stop that is always `0`). -/
def zeroStop (Ω : Type u) : StageStop Ω := ⟨fun _ => 0, fun _ _ => 0⟩

/-- The zero stop is a good stop of every good instance (it is below the positive cap on the record event). -/
theorem zeroStop_goodX {I : StageInst Ω} {c : SourceData Ω} {r : ScaledRootIdx c.Θ c.Q}
    {l : List (EntryIdx c.Θ c.Q)} {x₀ : ℝ} (hI : I.GoodX c r l x₀) : (zeroStop Ω).GoodX I c r l x₀ where
  rule_meas := fun y t => by
    have e : {e : (ℝ≥0 → ℝ) × ℝ≥0∞ | (zeroStop Ω).rule y e ≤ (t : ℝ≥0∞)} = univ := by
      ext e
      simp [zeroStop]
    rw [e]
    exact MeasurableSet.univ
  measurable_stop := measurable_const
  stop_eq := Eventually.of_forall fun _ => rfl
  stop_le := Eventually.of_forall fun _ _ => zero_le
  stop_lt := hI.E_good.mono fun ω h hm _ => by
    obtain ⟨-, hlt⟩ := h hm
    have hne : stgStartMX x₀ c.s c.W c.ζ I.W I.GT I.V I.T ω ≠ ⊤ := ne_top_of_lt hlt
    show (0 : ℝ≥0∞) < I.V ω - (stgStartMX x₀ c.s c.W c.ζ I.W I.GT I.V I.T ω).toNNReal
    rw [ENNReal.coe_toNNReal hne]
    exact tsub_pos_of_lt hlt

/-- **GB6's engine at a good instance**: almost surely on the record event, the stage driver matches the canonical
driver code of the stage word and the stage field below the stage cap. -/
theorem ae_isStopDrvMatch_inst {I : StageInst Ω} {c : SourceData Ω} {r : ScaledRootIdx c.Θ c.Q}
    {l : List (EntryIdx c.Θ c.Q)} {x₀ : ℝ} [IsProbabilityMeasure c.P] (hI : I.GoodX c r l x₀)
    {Fd : BoundaryWord × DistOn upperHalfPlaneOpens → Sec2.Assembly.PCode × ℝ≥0∞}
    (hFd : IsCanonicalDriverCode c.κ 0 Fd) :
    ∀ᵐ ω ∂c.P, I.srecX c r l x₀ ω ∈ I.E →
      Supp8.GB6.RelDrv.IsStopDrvMatch (Fd (I.β (I.srecX c r l x₀ ω), I.Hr ω)) (fun t => I.drvX c x₀ t ω)
        (I.capX c x₀ ω) := by
  have hv := hI.isSafe (zeroStop_goodX hI)
  have hrec : Measurable (I.srecX c r l x₀) := measurable_augRec (measurable_stageEncRec c r l) hI.measurable_pre
  exact ae_isStopDrvMatch_rec c.hκ hFd hv.measurable_β hv.measurableSet_E hv.countable_wordType hrec
    hv.measurable_Hr hv.measurable_R hv.continuous_R hv.R_zero hv.measurable_V hv.relSafe hv.V_pos hv.measurable_ρ
    hv.isPathRule_ρ hv.V_eq hv.measurable_ρs hv.isPathRule_ρs hv.ρs_ne_top hv.ρs_mono hv.ρs_lt hv.ρs_iSup

end Match

section Tip

open Supp8.GB6 Sec2.Assembly

/-- **The tip event is null on the stage's record event** (the stage field law in the relative chart,
`StageFieldLawXStatement`, at `A = {(b, g) | TipCode κ b (F (b, g))}`). -/
theorem ae_not_tipCode_stage (h13₀ : Exist.Theorem13Statement.{0}) (hsw : FlowSwallowStatement.{0})
    (hfield : StageFieldLawXStatement.{u}) {Ω : Type u} [MeasurableSpace Ω] [StandardBorelSpace Ω]
    (I : StageInst Ω) (c : SourceData Ω) (r : ScaledRootIdx c.Θ c.Q)
    (l : List (EntryIdx c.Θ c.Q)) (x₀ : ℝ) (hWm : ∀ t, Measurable (I.W t))
    (hopen : OpenLinesX I c r l x₀ hWm) (hβ : Measurable I.β) (hsort : ∀ y ∈ I.E, (I.β y).IsSorted)
    (hHr : Measurable I.Hr) {F : BoundaryWord × DistOn upperHalfPlaneOpens → PCode × ℝ≥0∞}
    (hF : IsCanonicalDriverCode c.κ 0 F) :
    ∀ᵐ ω ∂c.P, I.srecX c r l x₀ ω ∈ I.E →
      ¬ TipCode c.κ (I.β (I.srecX c r l x₀ ω)) (F (I.β (I.srecX c r l x₀ ω), I.Hr ω)) := by
  have hA : MeasurableSet {x : BoundaryWord × DistOn upperHalfPlaneOpens | TipCode c.κ x.1 (F (x.1, x.2))} :=
    (measurable_fst.prodMk hF.1) (measurableSet_tipCode c.κ)
  exact hfield I c r l x₀ hWm hopen hβ hsort hHr _ hA fun b hb μ hμ hgff =>
    ae_not_tipCode_of_isGFF h13₀ hsw c.hκ c.hκ4 hF hb hgff

end Tip

end InteractingSLE.Theorem14.GW2Rd
