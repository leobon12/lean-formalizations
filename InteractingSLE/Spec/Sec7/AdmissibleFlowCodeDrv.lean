/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.AdmissibleFlowCode
import InteractingSLE.Spec.Exist.StagedLaw3Main
import InteractingSLE.Spec.Supplement.Disintegrate

/-!
# The field-determined flow-line driver for (4.4) words, and its lift from the regular conditional law

Packet PROVE-STRIPSYS21, item (i) (ruling R48). From the word-measurable Theorem 1.2 on (4.4) words
(`AdmCode.Theorem12ParamCond44Statement`, proved from the §4.2 reference in `AdmissibleFlowCode.lean`):

* **`ae_detCode_eq_of_trace`**: PROVE-STAGED's `Exist.Staged.ae_detCode_eq` with the generating trace supplied as a
  hypothesis (instead of Theorem 1.3); for (4.4) words the trace exists by Remark 2.3 for `κ ≤ 4`
  (`Zhan.IsIntegratedSLEEvolution.ae_simple_trace`);
* **`admDrv`**: the field-determined driver of the angle-`θ` flow line from `0` of a field with boundary word `c`
  (PROVE-STAGED's `stagedDrv` with the restricted map), jointly Borel in `(c, f)` (`measurable_admDrv`) and regular at
  every sample (`admDrv_regular`);
* **`ae_admDrv_eq_of_isFlowLineDriver`** (determination): every angle-`θ` flow-line driver of a field with a boundary
  word whose flow-line word satisfies (4.4) agrees almost surely with `admDrv` (lifetime and path before it);
* **`ae_admDrv_eq_of_ae_condExpKernel`** (the lift): if, for `P`-a.e. `ω₀` in a `𝒢`-event `M`, the driver `W` is,
  under `condExpKernel P 𝒢 ω₀`, the flow-line driver of the field `Y` for the `𝒢`-measurable word `β ω₀`, and that
  word's flow-line word satisfies (4.4), then `P`-almost surely on `M`, `W` and its lifetime are `admDrv (β, Y)` — the
  R48-safe form of `Restart.DomainMarkov.K2.ae_codeMatch_of_ae_condExpKernel_isFlowLine` for drivers.

No result here takes Theorem 1.2, Theorem 1.3, `Theorem12ParamStatement` or `Theorem13Statement` as a hypothesis.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal

universe u

namespace InteractingSLE

namespace Sec7

namespace AdmCode

open Sec2.Assembly LQGMetric Exist Exist.Staged Exist.Param12 Exist.StagedLaw Restart

/-! ### Driver-code determination with the trace supplied -/

/-- **`Exist.Staged.ae_detCode_eq` with the generating trace as a hypothesis** (no Theorem 1.3): on every coupling of
the word with an almost surely existing generating trace, the determined driver code is almost surely the killed
driver code of a good history code. -/
theorem ae_detCode_eq_of_trace {κ : ℝ} (hκ : 0 < κ) {nL nR : ℕ}
    {Φ : WordData nL nR × DistOn upperHalfPlaneOpens → ℝ≥0∞ × (ℝ≥0 → ℂ)}
    {xL : Fin nL → ℝ} {xR : Fin nR → ℝ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ}
    {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P]
    {𝓕 : Filtration ℝ≥0 mΩ} {W : ℝ≥0 → Ω → ℝ} {VL : Fin nL → ℝ≥0 → Ω → ℝ}
    {VR : Fin nR → ℝ≥0 → Ω → ℝ} {B : ℝ≥0 → Ω → ℝ} {ζ : Ω → ℝ≥0∞}
    {h : Ω → DistOn upperHalfPlaneOpens}
    (hC : IsOptionalHullCoupling κ xL xR ρL ρR P 𝓕 W VL VR B ζ h)
    (htr : ∀ᵐ ω ∂P, ∃ η : ℝ≥0 → ℂ, IsGeneratingTrace (fun t => W t ω) (ζ ω) η)
    (hΦ : ∀ᵐ ω ∂P, (Φ (((xL, xR), (ρL, ρR)), h ω)).1 = ζ ω ∧
          ∀ η : ℝ≥0 → ℂ, IsGeneratingTrace (fun t => W t ω) (ζ ω) η →
            ∀ t : ℝ≥0, (Φ (((xL, xR), (ρL, ρR)), h ω)).2 t = η (min (t : ℝ≥0∞) (ζ ω)).toNNReal) :
    ∀ᵐ ω ∂P, ∃ x₀ : XCode nL nR, x₀ ∈ DetSet κ xL xR ρL ρR ∧ cζ x₀ = ζ ω ∧
      (∀ t : ℝ≥0, (t : ℝ≥0∞) < ζ ω → cw x₀ t = W t ω ∧ (∀ i, cvL x₀ i t = VL i t ω) ∧
        ∀ j, cvR x₀ j t = VR j t ω) ∧
      detCode Φ (((xL, xR), (ρL, ρR)), h ω) = dOf x₀ := by
  have hE := hC.1
  obtain ⟨B', -, hB'c, -, -, hB'ae⟩ := QuantumZipper.RS.exists_good_version0 hE.1.1
  filter_upwards [hΦ, htr, ae_codeOf_mem hκ hE hB'c hB'ae] with ω hΦω htrω hcode
  obtain ⟨η, hη⟩ := htrω
  obtain ⟨hx₁, hdec⟩ := hcode
  set x₀ := frz (codeOf xL xR B' W VL VR ζ ω) with hx₀def
  have hζx : cζ x₀ = ζ ω := rfl
  have hcwx : ∀ t : ℝ≥0, (t : ℝ≥0∞) < ζ ω → cw x₀ t = W t ω := fun t ht => (hdec t ht).1
  have hηx : IsGeneratingTrace (cw x₀) (ζ ω) η := Sec7.IsGeneratingTrace.congr_lt hη hcwx
  have hcrel : x₀ ∈ CRel κ xL xR ρL ρR := frz_mem_cRel hx₁
  have hmem : x₀ ∈ DetSet κ xL xR ρL ρR :=
    ⟨⟨hcrel, frozenB_frz hx₁.1.1⟩, fun n k hT => mem_traceSet_of_isGeneratingTrace hcrel hT hηx hT.le⟩
  have hcode : traceOfCode x₀ = outCode (Φ (((xL, xR), (ρL, ρR)), h ω)) := by
    refine Prod.ext hΦω.1.symm (funext fun n => funext fun k => ?_)
    simp only [traceOfCode, outCode, hζx, hΦω.1]
    by_cases hlt : ((dyad n k : ℝ≥0) : ℝ≥0∞) < ζ ω
    · simp only [hlt, ↓reduceIte]
      rw [hΦω.2 η hη, min_eq_left hlt.le, ENNReal.toNNReal_coe]
      exact LP.traceAt_eq_of_isGeneratingTrace hηx hcrel.1.1.continuousOn_w hcrel.1.2.2.1 hlt
    · simp only [hlt, ↓reduceIte]
  refine ⟨x₀, hmem, hζx, fun t ht => (hdec t ht).1.symm ▸ ⟨rfl, ?_, ?_⟩, ?_⟩
  · exact fun i => (hdec t ht).2.1 i
  · exact fun j => (hdec t ht).2.2.1 j
  · rw [detCode, ← hcode, ← dTrace_dOf]
    exact dInv_dTrace (dOf_mem_DSet hmem)

/-- **The generating trace of a (4.4) word** (Remark 2.3 for `κ ≤ 4`, `Zhan.IsIntegratedSLEEvolution.ae_simple_trace`):
almost surely the lifetime is infinite and the driver has a generating trace. -/
theorem ae_trace_of_cond44 {κ : ℝ} (hκ : 0 < κ) (hκ4 : κ < 4) {nL nR : ℕ} {xL : Fin nL → ℝ} {xR : Fin nR → ℝ}
    {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ} (hF : IsOrderedForceWord xL xR) (h44 : Sec4.Cond44 κ ρL ρR)
    {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ} {W : ℝ≥0 → Ω → ℝ}
    {VL : Fin nL → ℝ≥0 → Ω → ℝ} {VR : Fin nR → ℝ≥0 → Ω → ℝ} {B : ℝ≥0 → Ω → ℝ} {ζ : Ω → ℝ≥0∞}
    (hE : IsIntegratedSLEEvolution κ xL xR ρL ρR P 𝓕 W VL VR B ζ) :
    ∀ᵐ ω ∂P, ζ ω = ⊤ ∧ ∃ η : ℝ≥0 → ℂ, IsGeneratingTrace (fun t => W t ω) (ζ ω) η := by
  filter_upwards [Zhan.IsIntegratedSLEEvolution.ae_simple_trace hκ hκ4.le hF
    (Sec4.hasAdmissiblePartialSums_of_cond44 hκ4 hF h44) hE] with ω hω
  obtain ⟨hζ, -, η, hη, -⟩ := hω
  exact ⟨hζ, η, by rw [hζ]; exact hη⟩

/-! ### The field-determined flow-line driver -/

section Drv

variable (h44 : Theorem12ParamCond44Statement.{u}) {κ : ℝ} (hκ : 0 < κ) (hκ4 : κ < 4)

/-- The determination map of `Theorem12ParamCond44Statement` at word sizes `nL nR` (chosen). -/
def admΦ (nL nR : ℕ) : WordData nL nR × DistOn upperHalfPlaneOpens → ℝ≥0∞ × (ℝ≥0 → ℂ) :=
  (h44 κ hκ hκ4 nL nR).choose

theorem measurable_admΦ (nL nR : ℕ) : Measurable (admΦ h44 hκ hκ4 nL nR) :=
  (h44 κ hκ hκ4 nL nR).choose_spec.1

/-- **The field-determined flow-line driver**: for a boundary word `c` and a field `f`, the driver determined by the
flow field `f + θχ` for the angle-`θ` flow-line word of `c` from `0`. -/
def admDrv (θ : ℝ) (q : BoundaryWord × DistOn upperHalfPlaneOpens) : (ℝ≥0 → ℝ) × ℝ≥0∞ :=
  drvOf (detCode (admΦ h44 hκ hκ4 (flowLineNL q.1.fn q.1.jumps 0) (flowLineNR q.1.fn q.1.jumps 0))
    (truncWord (flowLineNL q.1.fn q.1.jumps 0) (flowLineNR q.1.fn q.1.jumps 0) (padFL κ θ q.1.fn q.1.jumps),
      flowField 0 (θ * QuantumZipper.chiC κ) q.2))

theorem admDrv_eq (θ : ℝ) (c : BoundaryWord) (f : DistOn upperHalfPlaneOpens) :
    admDrv h44 hκ hκ4 θ (c, f) =
      drvOf (detCode (admΦ h44 hκ hκ4 (flowLineNL c.fn c.jumps 0) (flowLineNR c.fn c.jumps 0))
        (((flowLineXL c.fn c.jumps 0, flowLineXR c.fn c.jumps 0),
          (flowLineRhoL κ c.fn c.jumps 0 θ, flowLineRhoR κ c.fn c.jumps 0 θ)),
          flowField 0 (θ * QuantumZipper.chiC κ) f)) := by
  simp only [admDrv]
  rw [truncWord_padFL]

/-- **The field-determined flow-line driver is jointly Borel** in the boundary word and the field. -/
theorem measurable_admDrv (θ : ℝ) : Measurable (admDrv h44 hκ hκ4 θ) := by
  set F : (BoundaryWord × DistOn upperHalfPlaneOpens) × (ℕ × ℕ) → (ℝ≥0 → ℝ) × ℝ≥0∞ := fun q =>
    drvOf (detCode (admΦ h44 hκ hκ4 q.2.1 q.2.2) (truncWord q.2.1 q.2.2 (padFL κ θ q.1.1.fn q.1.1.jumps),
      flowField 0 (θ * QuantumZipper.chiC κ) q.1.2)) with hF
  have hFm : Measurable F := by
    refine measurable_from_prod_countable_left fun mn => ?_
    exact measurable_drvOf.comp ((measurable_detCode (measurable_admΦ h44 hκ hκ4 mn.1 mn.2)).comp
      (((measurable_truncWord mn.1 mn.2).comp ((wordMeasStatement.2.2 κ θ).comp measurable_fst)).prodMk
        ((measurable_flowField 0 _).comp measurable_snd)))
  have e : admDrv h44 hκ hκ4 θ = fun q => F (q, (flowLineNL q.1.fn q.1.jumps 0, flowLineNR q.1.fn q.1.jumps 0)) :=
    rfl
  rw [e]
  exact hFm.comp (measurable_id.prodMk ((wordMeasStatement.1.comp measurable_fst).prodMk
    (wordMeasStatement.2.1.comp measurable_fst)))

/-- **The field-determined flow-line driver is regular at every sample** (`drvOf_regular`). -/
theorem admDrv_regular (θ : ℝ) (q : BoundaryWord × DistOn upperHalfPlaneOpens) :
    IsRegularDriver (admDrv h44 hκ hκ4 θ q) :=
  drvOf_regular _

/-- **Determination of a flow-line driver for a (4.4) word.** If `W` with lifetime `L` drives the angle-`θ` flow line
from `0` of a field `Y` with the data of a boundary word `c` whose flow-line word satisfies (4.4), then almost surely
`L = ∞` and `admDrv (c, Y)` has lifetime `L` and agrees with `W` before it. -/
theorem ae_admDrv_eq_of_isFlowLineDriver (θ : ℝ) (c : BoundaryWord)
    (hc44 : Sec4.Cond44 κ (flowLineRhoL κ c.fn c.jumps 0 θ) (flowLineRhoR κ c.fn c.jumps 0 θ))
    {Ω : Type u} [MeasurableSpace Ω] {Q : Measure Ω} [IsProbabilityMeasure Q]
    {Y : Ω → DistOn upperHalfPlaneOpens} {W : ℝ≥0 → Ω → ℝ} {L : Ω → ℝ≥0∞}
    (hfl : IsFlowLineDriver κ c.fn c.jumps θ Q Y W L) :
    ∀ᵐ ω ∂Q, L ω = ⊤ ∧ (admDrv h44 hκ hκ4 θ (c, Y ω)).2 = L ω ∧
      ∀ t : ℝ≥0, (t : ℝ≥0∞) < L ω → (admDrv h44 hκ hκ4 θ (c, Y ω)).1 t = W t ω := by
  obtain ⟨h'', 𝓕, VL, VR, B, htr, hC⟩ := hfl
  have hh'' : h'' = fun ω => flowField 0 (θ * QuantumZipper.chiC κ) (Y ω) := by
    funext ω
    ext φ
    have e1 := htr ω φ φ (fun z => by rw [Complex.ofReal_zero, add_zero])
    have e2 := isTranslateAddConst_flowField 0 (θ * QuantumZipper.chiC κ) (Y ω) φ φ
      (fun z => by rw [Complex.ofReal_zero, add_zero])
    rw [e1, e2]
  have hF := Theorem15.isOrderedForceWord_flowLine c.fn c.jumps 0
  have hΦ := (h44 κ hκ hκ4 (flowLineNL c.fn c.jumps 0) (flowLineNR c.fn c.jumps 0)).choose_spec.2
    _ _ _ _ hF hc44 hC
  have htrace : ∀ᵐ ω ∂Q, ∃ η : ℝ≥0 → ℂ, IsGeneratingTrace (fun t => W t ω) (L ω) η :=
    (ae_trace_of_cond44 hκ hκ4 hF hc44 hC.1).mono fun ω hω => hω.2
  have hdet := ae_detCode_eq_of_trace hκ hC htrace hΦ
  filter_upwards [hdet, ae_trace_of_cond44 hκ hκ4 hF hc44 hC.1] with ω hω hLω
  obtain ⟨x₀, hx₀, hζx, hagx, hdx⟩ := hω
  have hdx' : detCode (admΦ h44 hκ hκ4 (flowLineNL c.fn c.jumps 0) (flowLineNR c.fn c.jumps 0))
      (((flowLineXL c.fn c.jumps 0, flowLineXR c.fn c.jumps 0),
        (flowLineRhoL κ c.fn c.jumps 0 θ, flowLineRhoR κ c.fn c.jumps 0 θ)),
        flowField 0 (θ * QuantumZipper.chiC κ) (Y ω)) = dOf x₀ := by
    rw [← congrFun hh'' ω]; exact hdx
  have hD : admDrv h44 hκ hκ4 θ (c, Y ω) = (drvPath (dOf x₀), (dOf x₀).1) := by
    rw [admDrv_eq, hdx', drvOf_of_mem (dOf_mem_DSet hx₀)]
  rw [hD]
  exact ⟨hLω.1, hζx, fun t ht => ((drvPath_dOf_agree x₀).2 t (hζx ▸ ht)).trans (hagx t ht).1⟩

end Drv

/-! ### The lift from the regular conditional law -/

section Lift

/-- The dyadic rational `k / 2ⁿ`. -/
def dyadQ' (n k : ℕ) : ℚ≥0 := (k : ℚ≥0) / 2 ^ n

theorem coe_dyadQ' (n k : ℕ) : ((dyadQ' n k : ℚ≥0) : ℝ≥0) = dyad n k := by
  simp [dyadQ', dyad]

variable (h44 : Theorem12ParamCond44Statement.{u}) {κ : ℝ} (hκ : 0 < κ) (hκ4 : κ < 4)

/-- The pairs (boundary word, sample) at which the field-determined driver matches `W` at the rational times before
the lifetime. -/
def matchSet (θ : ℝ) {Ω : Type*} (Y : Ω → DistOn upperHalfPlaneOpens) (W : ℝ≥0 → Ω → ℝ) (L : Ω → ℝ≥0∞) :
    Set (BoundaryWord × Ω) :=
  {p | L p.2 = ⊤ ∧ (admDrv h44 hκ hκ4 θ (p.1, Y p.2)).2 = L p.2 ∧
    ∀ q : ℚ≥0, ((q : ℝ≥0) : ℝ≥0∞) < L p.2 → (admDrv h44 hκ hκ4 θ (p.1, Y p.2)).1 q = W q p.2}

theorem measurableSet_matchSet (θ : ℝ) {Ω : Type*} [MeasurableSpace Ω] {Y : Ω → DistOn upperHalfPlaneOpens}
    (hY : Measurable Y) {W : ℝ≥0 → Ω → ℝ} (hW : ∀ t, Measurable (W t)) {L : Ω → ℝ≥0∞} (hL : Measurable L) :
    MeasurableSet (matchSet h44 hκ hκ4 θ Y W L) := by
  have hD : Measurable fun p : BoundaryWord × Ω => admDrv h44 hκ hκ4 θ (p.1, Y p.2) :=
    (measurable_admDrv h44 hκ hκ4 θ).comp (measurable_fst.prodMk (hY.comp measurable_snd))
  have hLs : Measurable fun p : BoundaryWord × Ω => L p.2 := hL.comp measurable_snd
  refine (measurableSet_eq_fun hLs measurable_const).inter <| (measurableSet_eq_fun (measurable_snd.comp hD) hLs).inter
    (measurableSet_setOfPred.2 (Measurable.forall fun q => Measurable.imp ?_ ?_))
  · exact measurableSet_setOfPred.1 (measurableSet_lt measurable_const hLs)
  · exact measurableSet_setOfPred.1 (measurableSet_eq_fun ((measurable_pi_apply _).comp (measurable_fst.comp hD))
      ((hW q).comp measurable_snd))

/-- **(Det) for flow-line drivers from the regular conditional law, (4.4) words** (R48-safe). If, for `P`-almost every
`ω₀` in a `𝒢`-event `M`, the `𝒢`-measurable boundary word `β ω₀` has a flow-line word satisfying (4.4) and `W` with
lifetime `L` is, under `condExpKernel P 𝒢 ω₀`, the angle-`θ` flow-line driver of the measurable field `Y` for the data
of `β ω₀` (read through any field `Y'` equal to `Y` almost surely under the kernel), then `P`-almost surely on `M`,
`admDrv (β, Y)` has lifetime `L` and agrees with `W` before it (for drivers continuous before their lifetimes). -/
theorem ae_admDrv_eq_of_ae_condExpKernel (θ : ℝ) {Ω : Type u} {𝒢 : MeasurableSpace Ω} [mΩ : MeasurableSpace Ω]
    [StandardBorelSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P] (h𝒢 : 𝒢 ≤ mΩ) {M : Set Ω}
    (hM : MeasurableSet[𝒢] M) {β : Ω → BoundaryWord} (hβ : Measurable[𝒢] β)
    {Y : Ω → DistOn upperHalfPlaneOpens} (hY : Measurable Y) {W : ℝ≥0 → Ω → ℝ} (hW : ∀ t, Measurable (W t))
    {L : Ω → ℝ≥0∞} (hL : Measurable L) (hWc : ∀ ω, ContinuousOn (fun t => W t ω) {t | (t : ℝ≥0∞) < L ω})
    (hfl : ∀ᵐ ω₀ ∂P, ω₀ ∈ M →
      Sec4.Cond44 κ (flowLineRhoL κ (β ω₀).fn (β ω₀).jumps 0 θ) (flowLineRhoR κ (β ω₀).fn (β ω₀).jumps 0 θ) ∧
        ∃ Y' : Ω → DistOn upperHalfPlaneOpens, (∀ᵐ ω ∂(condExpKernel P 𝒢 ω₀), Y' ω = Y ω) ∧
          IsFlowLineDriver κ (β ω₀).fn (β ω₀).jumps θ (condExpKernel P 𝒢 ω₀) Y' W L) :
    ∀ᵐ ω ∂P, ω ∈ M → L ω = ⊤ ∧ (admDrv h44 hκ hκ4 θ (β ω, Y ω)).2 = L ω ∧
      ∀ t : ℝ≥0, (t : ℝ≥0∞) < L ω → (admDrv h44 hκ hκ4 θ (β ω, Y ω)).1 t = W t ω := by
  have hA := measurableSet_matchSet h44 hκ hκ4 θ hY hW hL
  have h : ∀ᵐ ω₀ ∂P, ω₀ ∈ M → ∀ᵐ ω ∂(condExpKernel P 𝒢 ω₀), (β ω₀, ω) ∈ matchSet h44 hκ hκ4 θ Y W L := by
    filter_upwards [hfl] with ω₀ hfl₀ hω₀
    obtain ⟨hc44, Y', hY', hd⟩ := hfl₀ hω₀
    filter_upwards [ae_admDrv_eq_of_isFlowLineDriver h44 hκ hκ4 θ (β ω₀) hc44 hd, hY'] with ω hω hYω
    rw [hYω] at hω
    exact ⟨hω.1, hω.2.1, fun q hq => hω.2.2 q hq⟩
  filter_upwards [Theorem14.Disintegrate.ae_imp_of_ae_condExpKernel_param h𝒢 hβ hA hM h] with ω hω hωM
  obtain ⟨htop, hζ, hq⟩ := hω hωM
  refine ⟨htop, hζ, fun t ht => ?_⟩
  have hDc : ContinuousOn (admDrv h44 hκ hκ4 θ (β ω, Y ω)).1 {s | (s : ℝ≥0∞) < L ω} := by
    rw [← hζ]; exact (admDrv_regular h44 hκ hκ4 θ _).1
  exact Restart.eq_of_eq_dyad_lt hDc (hWc ω) (fun n k hk => by
    have := hq (dyadQ' n k) (by rw [coe_dyadQ']; exact hk)
    rwa [coe_dyadQ'] at this) ht

end Lift

end AdmCode

end Sec7

end InteractingSLE
