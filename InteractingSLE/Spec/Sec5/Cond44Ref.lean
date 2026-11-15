/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec5.Cond44RefCode
import InteractingSLE.Spec.Sec7.Lemma71HInputs
import InteractingSLE.Spec.Sec7.StripSysBorel
import InteractingSLE.WangWu.Prop418RangeMain
import InteractingSLE.Spec.Zhan.TransienceTrace

/-!
# §4.2, Theorem 1.2 under (4.4): the reference coupling from Proposition 4.11

Packet PROVE-SEC5-N. Specification §4.2, proof of Theorem 1.2 for `κ ∈ (0, 4)` assuming (4.4)
(`source/spec/p097-144.md` L582–L586, p. 122): "Proposition 4.11 implies that the flow line `η` of `h` starting at
`0` is equal to the left boundary of the counterflow line `η′` starting at `z₀` of `h − π/2 χ`, where `η, η′, h` are
coupled together so that `η` is conditionally independent of `η′` given `h`. Since `η` and `η′` are conditionally
independent given `h`, it follows that `η` is almost surely determined by `h`."

**The chart.** In Lemma 4.5's chart `Q` (`z₀ ↦ ∞`) the strip data of Proposition 4.11 (lower data `≤ −λ + πχ` left of
`0` and `≥ λ` right of `0`; upper data `≤ −λ` left of `z₀` and `≥ λ + πχ` right of `z₀`) become half-plane data
`≤ −λ + πχ` on `ℝ₋` and `≥ λ` on `ℝ₊` (the upper heights move by `±πχ`, as in `Sec5.Prop55Half.stripQHData_prop74Data`),
i.e. exactly the data of a flow line whose word satisfies (4.4) (`Sec4.Cond44`). The flow line runs from `0` to `∞`,
and the counterflow line of `h − π/2 χ` runs from `∞` to `0`: it is the frozen centred counterflow
(`IsCenteredCounterflowDriver κ P (h − π/2 χ)`), whose curve is `R ∘ β`, `R(z) = −1/z`, for the trace `β` of its
driver (`WangWu.revLine`).

**The coupling.** As in Wang–Wu's Proposition 4.18 (`WangWu.Prop418DetGlue`), the triple `(h, η, η′)` with `η ⟂ η′ | h`
is realized by gluing: the flow-line coupling `P` on `Ω`, and a sample of the regular conditional law `k` of the
counterflow's killed driving history given its field, taken at `h − π/2 χ` (`WangWu.glueMeasure`).

**The named input** `Prop411QStatement` is Proposition 4.11 on this glued space, in the two halves of its proof:
(a) Lemma 4.7, the counterflow contains the flow line (at positive rational flow times); (b) Proposition 4.9's
per-time half, the counterflow point at each alive positive rational time is not on the left of the flow line.

**Proved here** (`hasFieldDeterminedHistories_of_prop411Q`, `cond44ReferenceStatement_of_prop411Q`): from the named
input, the killed driving history of *every* optional hull coupling of a (4.4) word is field-determined, hence
`Sec7.Lemma71H.Cond44ReferenceStatement`. Steps:

* regularity of the flow line (`ae_seedLine_of_admissible`): infinite lifetime, a simple transient trace in `ℍ`
  (Zhan's Aux. 7 and the simple-trace theorem), so the seed line is a proper arc;
* the counterflow coupling (`StripSysBorel.exists_isCenteredCounterflowDriver_standardBorel`) for the shifted data,
  whose field has the law of `h − π/2 χ` (`isGFFWithBoundaryData_flowField_zero`, `isPiecewiseConstant_forceData`);
* on the glued space, the rational-disc hitting code of the flow line equals `lbCode` of the completed counterflow
  range (`Cond44RefSide.hitCode_eq_lbCode`), a measurable function of the glued sample (`Cond44RefCode`);
* Lemma 4.1 for a glued sample (`WangWu.aeDeterminedBy_of_glue_ae_eq`) and the range-to-history step
  (`WangWu.isFieldDeterminedHistory_of_aeDeterminedBy_hitCode`, Lusin–Souslin).

No Aux. lemma 23 transfer is needed: the argument applies to every coupling directly.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal Real
open QuantumZipper (H chiC)
open LQGMetric (DistOn TestOn)

universe u

namespace InteractingSLE.Sec5.Cond44Ref

open WangWu hiding ratPt exists_ratPt_dist_lt
open LawUnique

/-! ### The counterflow field, history and range -/

/-- The field `h − (π/2)χ` of the counterflow line of Lemma 4.7, Proposition 4.9 and Proposition 4.11. -/
def cfField (κ : ℝ) (f : DistOn upperHalfPlaneOpens) : DistOn upperHalfPlaneOpens :=
  Exist.flowField 0 (-(π / 2 * chiC κ)) f

theorem measurable_cfField (κ : ℝ) : Measurable (cfField κ) := Exist.measurable_flowField 0 _

/-- The dyadic killed history of a counterflow driver (lifetime and driver; no force coordinates). -/
def cfHistory {Ω : Type*} (W : ℝ≥0 → Ω → ℝ) (ζ : Ω → ℝ≥0∞) (ω : Ω) : HistorySpace 0 0 :=
  killedHistory W (Fin.elim0 : Fin 0 → ℝ≥0 → Ω → ℝ) (Fin.elim0 : Fin 0 → ℝ≥0 → Ω → ℝ) ζ ω

/-- **The counterflow line at rational times**, read from a history `y`: the point `R(β(q)) = −1/β(q)` at a positive
rational time `q` before the lifetime `y.1`, and `0` (the endpoint of the counterflow) otherwise. -/
def cfPts {nL nR : ℕ} (y : HistorySpace nL nR) (q : ℚ) : ℂ :=
  if 0 < q ∧ (((q : ℝ).toNNReal : ℝ≥0) : ℝ≥0∞) < y.1 then revLine y q else 0

theorem measurable_cfPts {nL nR : ℕ} (q : ℚ) : Measurable fun y : HistorySpace nL nR => cfPts y q := by
  have hS : MeasurableSet {y : HistorySpace nL nR | 0 < q ∧ (((q : ℝ).toNNReal : ℝ≥0) : ℝ≥0∞) < y.1} :=
    (MeasurableSet.const _).inter (measurableSet_lt measurable_const measurable_fst)
  exact Measurable.ite hS (measurable_revLine _) measurable_const

/-- **The completed counterflow range** read from a history: the closure of its points at alive positive rational
times together with its endpoint `0`. -/
def cfRange {nL nR : ℕ} (y : HistorySpace nL nR) : Set ℂ := closure (range (cfPts y))

/-! ### The named input: Proposition 4.11 in the chart `Q`, on the glued space -/

/-- **Named input: Proposition 4.11 in the chart `Q`, for the conditionally independent triple realized by gluing**
(specification §4.2, Lemma 4.7, Proposition 4.9 and Proposition 4.11, pp. 117–122, as used in the proof of
Theorem 1.2 under (4.4), p. 122). Let `0 < κ < 4` and let the ordered force word satisfy (4.4). Let `(h, W, …)` be an
optional hull coupling of the word on `Ω`; let `(h₂, W₂, ζ₂)` be a centred counterflow coupling (frozen
`IsCenteredCounterflowDriver`) whose field has the law of `h − π/2 χ`, and `k` a regular conditional law of its killed
history given its field. Almost surely on the glued space `P ⊗ k(h − π/2 χ)` (the flow line and the counterflow line
of `h − π/2 χ` from `∞`, conditionally independent given `h`):

* (Lemma 4.7, containment) every point of the flow line at a positive rational time lies in the completed range of
  the counterflow line;
* (Proposition 4.9, "`η′(τ′)` is to the right of `η`") no point of the counterflow line at an alive positive rational
  time lies on the left side of the flow line.

Together these say that the flow line is the left boundary of the counterflow line (`Cond44RefSide`). -/
def Prop411QStatement : Prop :=
  ∀ κ : ℝ, 0 < κ → κ < 4 → ∀ {nL nR : ℕ} (xL : Fin nL → ℝ) (xR : Fin nR → ℝ) (ρL : Fin nL → ℝ)
    (ρR : Fin nR → ℝ), IsOrderedForceWord xL xR → Sec4.Cond44 κ ρL ρR →
    ∀ {Ω : Type u} {mΩ : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P]
      (𝓕 : Filtration ℝ≥0 mΩ) (W : ℝ≥0 → Ω → ℝ) (VL : Fin nL → ℝ≥0 → Ω → ℝ) (VR : Fin nR → ℝ≥0 → Ω → ℝ)
      (B : ℝ≥0 → Ω → ℝ) (ζ : Ω → ℝ≥0∞) (h : Ω → DistOn upperHalfPlaneOpens)
      (hC : IsOptionalHullCoupling κ xL xR ρL ρR P 𝓕 W VL VR B ζ h)
      {Ω₂ : Type u} {_mΩ₂ : MeasurableSpace Ω₂} (P₂ : Measure Ω₂) [IsProbabilityMeasure P₂]
      (h₂ : Ω₂ → DistOn upperHalfPlaneOpens) (W₂ : ℝ≥0 → Ω₂ → ℝ) (ζ₂ : Ω₂ → ℝ≥0∞),
      IsCenteredCounterflowDriver κ P₂ h₂ W₂ ζ₂ →
      P.map (fun ω => cfField κ (h ω)) = P₂.map h₂ →
      ∀ (k : Kernel (DistOn upperHalfPlaneOpens) (HistorySpace 0 0)) [IsMarkovKernel k],
        P₂.map (fun ω => (h₂ ω, cfHistory W₂ ζ₂ ω)) = P₂.map h₂ ⊗ₘ k →
        ∀ᵐ p ∂(glueMeasure P k (fun ω => cfField κ (h ω)) ((measurable_cfField κ).comp hC.2.1)),
          (∀ t : ℚ, 0 < t → seedLine ζ W p.1 t ∈ cfRange p.2) ∧
            ∀ s : ℚ, cfPts p.2 s ∉ leftSideOf (arcRange (seedLine ζ W p.1))

/-! ### Regularity of the flow line -/

/-- **The seed line of an admissible word is a proper arc** (`0 < κ ≤ 4`): almost surely the lifetime is infinite,
the seed line is the continuous generating trace, and it is a simple proper arc of `ℍ` from `0` to `∞` (Zhan's simple
trace theorem and Aux. lemma 7). -/
theorem ae_seedLine_of_admissible {κ : ℝ} (hκ : 0 < κ) (hκ4 : κ ≤ 4) {nL nR : ℕ} {xL : Fin nL → ℝ}
    {xR : Fin nR → ℝ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ} (hF : IsOrderedForceWord xL xR)
    (hadm : Sec4.HasAdmissiblePartialSums κ ρL ρR xL xR) {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ} {W : ℝ≥0 → Ω → ℝ} {VL : Fin nL → ℝ≥0 → Ω → ℝ} {VR : Fin nR → ℝ≥0 → Ω → ℝ}
    {B : ℝ≥0 → Ω → ℝ} {ζ : Ω → ℝ≥0∞} (hE : IsIntegratedSLEEvolution κ xL xR ρL ρR P 𝓕 W VL VR B ζ) :
    ∀ᵐ ω ∂P, ζ ω = ⊤ ∧ (∃ η : ℝ≥0 → ℂ, IsGeneratingTrace (fun t => W t ω) ⊤ η ∧
      seedLine ζ W ω = fun s : ℝ => η s.toNNReal) ∧ IsProperArc (seedLine ζ W ω) := by
  filter_upwards [Zhan.IsIntegratedSLEEvolution.ae_simple_trace hκ hκ4 hF hadm hE,
    Zhan.aux7Statement hκ hκ4 xL xR ρL ρR P 𝓕 W VL VR B ζ hF hadm hE, hE.2.2.2.2] with ω hω h7 hp
  obtain ⟨hζ, -, η, hη, hinj, hH, -⟩ := hω
  have hwc : Continuous fun t => W t ω := by
    have h := hp.2.2.2.1
    rw [hζ] at h
    exact continuousOn_univ.1 (h.mono fun t _ => show (t : ℝ≥0∞) < ⊤ from ENNReal.coe_lt_top)
  have hk : (fun t => killedProc ζ W t ω) = fun t => W t ω := funext (killedProc_of_eq_top hζ)
  have hline : seedLine ζ W ω = fun s : ℝ => η s.toNNReal := by
    funext s
    simp only [seedLine, hk]
    exact LP.traceAt_eq_of_isGeneratingTrace hη hwc.continuousOn hp.1 ENNReal.coe_lt_top
  have hηc : Continuous η :=
    continuousOn_univ.1 (hη.2.1.mono fun t _ => show (t : ℝ≥0∞) ≤ ⊤ from le_top)
  refine ⟨hζ, ⟨η, hη, hline⟩, ?_⟩
  rw [hline]
  exact isProperArc_of_injective hηc hη.1 hinj hH (h7.2.2 η hη)

/-! ### The counterflow coupling -/

/-- The killed driving of a coupling is measurable with no force coordinates recorded. -/
theorem isMeasurableKilledDriving_elim0 {Ω : Type*} [MeasurableSpace Ω] {nL nR : ℕ} {W : ℝ≥0 → Ω → ℝ}
    {VL : Fin nL → ℝ≥0 → Ω → ℝ} {VR : Fin nR → ℝ≥0 → Ω → ℝ} {ζ : Ω → ℝ≥0∞}
    (hX : IsMeasurableKilledDriving W VL VR ζ) :
    IsMeasurableKilledDriving W (Fin.elim0 : Fin 0 → ℝ≥0 → Ω → ℝ) (Fin.elim0 : Fin 0 → ℝ≥0 → Ω → ℝ) ζ := by
  intro r A hA
  set g : ℝ × (Fin nL → ℝ) × (Fin nR → ℝ) → ℝ × (Fin 0 → ℝ) × (Fin 0 → ℝ) :=
    fun v => (v.1, (Fin.elim0 : Fin 0 → ℝ), (Fin.elim0 : Fin 0 → ℝ)) with hg
  have hgm : Measurable g := measurable_fst.prodMk measurable_const
  convert hX r (g ⁻¹' A) (hgm hA) using 1
  ext ω
  simp only [Set.mem_ofPred_eq, Set.mem_preimage, hg]
  have e : ∀ f : Fin 0 → ℝ, f = Fin.elim0 := fun f => Subsingleton.elim _ _
  rw [e (fun i => (Fin.elim0 i : ℝ≥0 → Ω → ℝ) r ω)]

/-- The killed driving of a centred counterflow driver is measurable. -/
theorem isMeasurableKilledDriving_of_isCenteredCounterflowDriver {κ : ℝ} {Ω : Type u} [MeasurableSpace Ω]
    {P : Measure Ω} {h : Ω → DistOn upperHalfPlaneOpens} {W : ℝ≥0 → Ω → ℝ} {ζ : Ω → ℝ≥0∞}
    (hcf : IsCenteredCounterflowDriver κ P h W ζ) :
    IsMeasurableKilledDriving W (Fin.elim0 : Fin 0 → ℝ≥0 → Ω → ℝ) (Fin.elim0 : Fin 0 → ℝ≥0 → Ω → ℝ) ζ := by
  obtain ⟨b', J', h', -, -, h'', 𝓕, VL, VR, B, -, hC⟩ := hcf
  obtain ⟨hX, -⟩ := hC.2.2.2
  exact isMeasurableKilledDriving_elim0 hX

theorem measurable_cfHistory {Ω : Type*} [MeasurableSpace Ω] {W : ℝ≥0 → Ω → ℝ} {ζ : Ω → ℝ≥0∞}
    (hX : IsMeasurableKilledDriving W (Fin.elim0 : Fin 0 → ℝ≥0 → Ω → ℝ) (Fin.elim0 : Fin 0 → ℝ≥0 → Ω → ℝ) ζ) :
    Measurable (cfHistory W ζ) :=
  measurable_killedHistory hX

/-- The marks of a force word together with the seed, as a finite set. -/
def forceJumpFinset {nL nR : ℕ} (vL : Fin nL → ℝ) (vR : Fin nR → ℝ) : Finset ℝ :=
  insert 0 (Finset.univ.image vL ∪ Finset.univ.image vR)

theorem coe_forceJumpFinset {nL nR : ℕ} (vL : Fin nL → ℝ) (vR : Fin nR → ℝ) :
    (forceJumpFinset vL vR : Set ℝ) = forceJumpSet vL vR := by
  simp [forceJumpFinset, forceJumpSet, Finset.coe_insert, Finset.coe_union, Finset.coe_image, Set.image_univ]

theorem eventually_lt_iff_of_ne {a y : ℝ} (h : y ≠ a) : ∀ᶠ z in 𝓝 y, (z < a ↔ y < a) := by
  rcases lt_or_gt_of_ne h with hya | hay
  · exact (eventually_lt_nhds hya).mono fun z hz => iff_of_true hz hya
  · exact (eventually_gt_nhds hay).mono fun z hz => iff_of_false (not_lt.2 hz.le) (not_lt.2 hay.le)

theorem eventually_le_iff_of_ne {a y : ℝ} (h : y ≠ a) : ∀ᶠ z in 𝓝 y, (a ≤ z ↔ a ≤ y) := by
  rcases lt_or_gt_of_ne h with hya | hay
  · exact (eventually_lt_nhds hya).mono fun z hz => iff_of_false (not_le.2 hz) (not_le.2 hya)
  · exact (eventually_gt_nhds hay).mono fun z hz => iff_of_true hz.le hay.le

/-- **Shifted force boundary data are piecewise constant off the marks.** -/
theorem isPiecewiseConstant_forceData (κ : ℝ) {nL nR : ℕ} (ρL : Fin nL → ℝ) (ρR : Fin nR → ℝ)
    (vL : Fin nL → ℝ) (vR : Fin nR → ℝ) (c : ℝ) :
    IsPiecewiseConstantBoundaryData (fun x => forceBoundaryData κ ρL ρR vL vR x + c) (forceJumpFinset vL vR) := by
  intro y hy
  simp only [forceJumpFinset, Finset.mem_insert, Finset.mem_union, Finset.mem_image, Finset.mem_univ, true_and,
    not_or, not_exists] at hy
  obtain ⟨hy0, hyL, hyR⟩ := hy
  have hs := eventually_lt_iff_of_ne hy0
  have hL : ∀ᶠ z in 𝓝 y, ∀ i, (z < vL i ↔ y < vL i) :=
    Filter.eventually_all.2 fun i => eventually_lt_iff_of_ne fun h => hyL i h.symm
  have hR : ∀ᶠ z in 𝓝 y, ∀ i, (vR i ≤ z ↔ vR i ≤ y) :=
    Filter.eventually_all.2 fun i => eventually_le_iff_of_ne fun h => hyR i h.symm
  filter_upwards [hs, hL, hR] with z hz1 hz2 hz3
  have eL : Finset.univ.filter (fun i => z < vL i) = Finset.univ.filter (fun i => y < vL i) :=
    Finset.filter_congr fun i _ => hz2 i
  have eR : Finset.univ.filter (fun i => vR i ≤ z) = Finset.univ.filter (fun i => vR i ≤ y) :=
    Finset.filter_congr fun i _ => hz3 i
  simp only [forceBoundaryData, eL, eR]
  by_cases hy' : y < 0
  · simp only [hy', hz1.2 hy', ↓reduceIte]
  · simp only [hy', show ¬ z < 0 from fun h => hy' (hz1.1 h), ↓reduceIte]

/-- **The shifted field `h + c` of a GFF with data `g` is a GFF with data `g + c`.** -/
theorem isGFFWithBoundaryData_flowField_zero {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {h : Ω → DistOn upperHalfPlaneOpens} {g : ℝ → ℝ} {S : Set ℝ} (hh : IsGFFWithBoundaryData P h g S) (c : ℝ) :
    IsGFFWithBoundaryData P (fun ω => Exist.flowField 0 c (h ω)) (fun x => g x + c) S := by
  refine ⟨(Exist.measurable_flowField 0 c).comp hh.1, fun u hu => ?_⟩
  have hu' : IsBoundedHarmonicExtension g S (fun z => u z + -c) := by
    obtain ⟨hharm, ⟨C, hC⟩, hlim⟩ := hu
    refine ⟨fun z hz => (hharm z hz).add (InnerProductSpace.harmonicAt_const _), ⟨C + |c|, fun z hz => ?_⟩,
      fun x hx => ?_⟩
    · exact (abs_add_le _ _).trans (by rw [abs_neg]; linarith [hC z hz])
    · have := (hlim x hx).add_const (-c)
      rwa [add_neg_cancel_right] at this
  have hmi : ∀ φ : TestOn upperHalfPlaneOpens,
      Integrable (fun w => (fun z => u z + -c) (w + ((0 : ℝ) : ℂ)) * φ w) := fun φ =>
    Coupling.MartMeans2.integrable_mul_test_of_continuousOn (S := H)
      (((hu.1.continuousOn).comp (continuousOn_id.add continuousOn_const)
        fun z hz => Exist.add_real_mem_H hz 0).add continuousOn_const) φ φ.tsupport_subset
  have hX := Exist.isZBGFFProcess_flowField (hh.2 _ hu') 0 c hmi
  have e : ∀ w : ℂ, (fun z => u z + -c) (w + ((0 : ℝ) : ℂ)) + c = u w := fun w => by
    simp only [Complex.ofReal_zero, add_zero, neg_add_cancel_right]
  simp only [e] at hX
  exact hX

/-- **The counterflow coupling of `h − π/2 χ`**: a centred counterflow on a standard Borel space whose field has the
law of `h − π/2 χ` for the field `h` of any optional hull coupling. -/
theorem exists_cfCoupling {κ : ℝ} (hκ : 0 < κ) {nL nR : ℕ} {xL : Fin nL → ℝ} {xR : Fin nR → ℝ}
    {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ} {Ω : Type u} {mΩ : MeasurableSpace Ω} {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ} {W : ℝ≥0 → Ω → ℝ} {VL : Fin nL → ℝ≥0 → Ω → ℝ} {VR : Fin nR → ℝ≥0 → Ω → ℝ}
    {B : ℝ≥0 → Ω → ℝ} {ζ : Ω → ℝ≥0∞} {h : Ω → DistOn upperHalfPlaneOpens}
    (hC : IsOptionalHullCoupling κ xL xR ρL ρR P 𝓕 W VL VR B ζ h) :
    ∃ (Ω₂ : Type u) (_ : MeasurableSpace Ω₂) (_ : StandardBorelSpace Ω₂) (P₂ : Measure Ω₂)
      (_ : IsProbabilityMeasure P₂) (h₂ : Ω₂ → DistOn upperHalfPlaneOpens) (W₂ : ℝ≥0 → Ω₂ → ℝ)
      (ζ₂ : Ω₂ → ℝ≥0∞), IsCenteredCounterflowDriver κ P₂ h₂ W₂ ζ₂ ∧ Measurable h₂ ∧
        P.map (fun ω => cfField κ (h ω)) = P₂.map h₂ := by
  set c : ℝ := -(π / 2 * chiC κ) with hc
  have hb := isPiecewiseConstant_forceData κ ρL ρR xL xR c
  obtain ⟨Ω₂, mΩ₂, hSB, P₂, hP₂, h₂, W₂, ζ₂, hh₂, hcf, -⟩ :=
    Sec7.StripSysBorel.exists_isCenteredCounterflowDriver_standardBorel.{u} hκ hb
  have hh : IsGFFWithBoundaryData P h (forceBoundaryData κ ρL ρR xL xR) (forceJumpSet xL xR) :=
    ⟨hC.2.1, hC.2.2.1⟩
  have hh' := isGFFWithBoundaryData_flowField_zero hh c
  rw [← coe_forceJumpFinset] at hh'
  obtain ⟨u₀, hu₀, -⟩ := PiecewiseConstant.existsUnique_isBoundedHarmonicExtension hb
  exact ⟨Ω₂, mΩ₂, hSB, P₂, hP₂, h₂, W₂, ζ₂, hcf, hh₂.1, Exist.map_eq_of_isGFFWithBoundaryData hh' hh₂ hu₀⟩

/-! ### Determination from Proposition 4.11 -/

/-- **Theorem 1.2 under (4.4), every coupling, from Proposition 4.11** (named input `Prop411QStatement`): the killed
driving history of every optional hull coupling of an ordered (4.4) word, `0 < κ < 4`, is field-determined. -/
theorem isFieldDeterminedHistory_of_prop411Q (h411 : Prop411QStatement.{u}) {κ : ℝ} (hκ : 0 < κ) (hκ4 : κ < 4)
    {nL nR : ℕ} {xL : Fin nL → ℝ} {xR : Fin nR → ℝ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ}
    (hF : IsOrderedForceWord xL xR) (h44 : Sec4.Cond44 κ ρL ρR) {Ω : Type u} {mΩ : MeasurableSpace Ω}
    {P : Measure Ω} [IsProbabilityMeasure P] {𝓕 : Filtration ℝ≥0 mΩ} {W : ℝ≥0 → Ω → ℝ}
    {VL : Fin nL → ℝ≥0 → Ω → ℝ} {VR : Fin nR → ℝ≥0 → Ω → ℝ} {B : ℝ≥0 → Ω → ℝ} {ζ : Ω → ℝ≥0∞}
    {h : Ω → DistOn upperHalfPlaneOpens} (hC : IsOptionalHullCoupling κ xL xR ρL ρR P 𝓕 W VL VR B ζ h) :
    LP.IsFieldDeterminedHistory P h W VL VR ζ := by
  have hadm := Sec4.hasAdmissiblePartialSums_of_cond44 hκ4 hF h44
  have hline := ae_seedLine_of_admissible hκ hκ4.le hF hadm hC.1
  obtain ⟨Ω₂, mΩ₂, hSB, P₂, hP₂, h₂, W₂, ζ₂, hcf, hh₂, hlaw⟩ := exists_cfCoupling hκ hC
  have hX₂ := isMeasurableKilledDriving_of_isCenteredCounterflowDriver hcf
  set k := condDistrib (cfHistory W₂ ζ₂) h₂ P₂ with hkdef
  have hk : P₂.map (fun ω => (h₂ ω, cfHistory W₂ ζ₂ ω)) = P₂.map h₂ ⊗ₘ k :=
    (compProd_map_condDistrib hh₂.aemeasurable (measurable_cfHistory hX₂).aemeasurable).symm
  have hXm : Measurable fun ω => cfField κ (h ω) := (measurable_cfField κ).comp hC.2.1
  have hglue := h411 κ hκ hκ4 xL xR ρL ρR hF h44 P 𝓕 W VL VR B ζ h hC P₂ h₂ W₂ ζ₂ hcf hlaw k hk
  have hline' := ae_glue_fst (μ := P) k hXm hline
  -- the hitting code of the flow line is read from the glued counterflow sample
  have heq : ∀ᵐ p ∂(glueMeasure P k (fun ω => cfField κ (h ω)) hXm),
      hitCode (seedLine ζ W p.1) = lbCode (closure (range (cfPts p.2))) := by
    filter_upwards [hglue, hline'] with p hp hq
    obtain ⟨-, -, hγ⟩ := hq
    refine hitCode_eq_lbCode hγ (arcRange_subset_closure_of_forall_rat hγ hp.1)
      (disjoint_closure_leftSideOf hγ ?_)
    rintro _ ⟨s, rfl⟩
    exact hp.2 s
  have hD : Measurable fun ω => hitCode (seedLine ζ W ω) :=
    measurable_hitCode.comp (measurable_pi_iff.2 fun s => measurable_seedLine hC.1.2.1 s)
  have hL : Measurable fun y : HistorySpace 0 0 => lbCode (closure (range (cfPts y))) :=
    measurable_lbCode fun q => measurable_cfPts q
  obtain ⟨Φ, hΦ, hΦe⟩ := aeDeterminedBy_of_glue_ae_eq k hXm hD hL heq
  exact isFieldDeterminedHistory_of_aeDeterminedBy_hitCode hκ hC.1 hline
    ⟨Φ ∘ cfField κ, hΦ.comp (measurable_cfField κ), hΦe⟩

/-- **Theorem 1.2 under (4.4), all couplings, from Proposition 4.11.** -/
theorem hasFieldDeterminedHistories_of_prop411Q (h411 : Prop411QStatement.{u}) {κ : ℝ} (hκ : 0 < κ)
    (hκ4 : κ < 4) {nL nR : ℕ} {xL : Fin nL → ℝ} {xR : Fin nR → ℝ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ}
    (hF : IsOrderedForceWord xL xR) (h44 : Sec4.Cond44 κ ρL ρR) :
    LP.HasFieldDeterminedHistories.{u} κ xL xR ρL ρR := by
  intro Ω mΩ P _ 𝓕 W VL VR B ζ h hC
  exact isFieldDeterminedHistory_of_prop411Q h411 hκ hκ4 hF h44 hC

/-- **The §4.2 reference coupling (`Sec7.Lemma71H.Cond44ReferenceStatement`) from Proposition 4.11**: Theorem 1.1's
coupling of the word, whose killed history is field-determined by `isFieldDeterminedHistory_of_prop411Q`. -/
theorem cond44ReferenceStatement_of_prop411Q (h411 : Prop411QStatement.{u}) :
    Sec7.Lemma71H.Cond44ReferenceStatement.{u} := by
  intro κ hκ hκ4 nL nR xL xR ρL ρR hF h44
  obtain ⟨Ω, mΩ, P, hP, 𝓕, W, VL, VR, B, ζ, h, hC⟩ :=
    Coupling.exists_isOptionalHullCoupling_of_thm22.{u} hκ hF (exists_isIntegratedSLEEvolution_assembled hκ hF)
  exact ⟨Ω, mΩ, P, hP, 𝓕, W, VL, VR, B, ζ, h, hC, isFieldDeterminedHistory_of_prop411Q h411 hκ hκ4 hF h44 hC⟩

end InteractingSLE.Sec5.Cond44Ref
