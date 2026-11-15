/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.StripMarks513K
import InteractingSLE.Spec.Sec7.StripSafeWire

/-!
# Theorem R.7's `hsd.det`: Proposition 5.13 for the counterflow of every R.7 configuration

Packet PROVE-HSD. The determination input `R7Leaves.R7ExtremalSideDet.det` (the counterflow trace of the R.7 field is
almost surely a Borel function of the coupling field `h″`) is Proposition 5.13 for the counterflow, once the counterflow
word is read as a Figure 5.1 strip word.

* **The frame** (`r7Frame`): the counterflow word of the R.7 data `prop74Data A B` is `−B − πχ` on `ℝ₋` and `A + πχ` on
  `ℝ₊` (`counterflowData_prop74Data_of_neg/pos`), which is the Figure 5.1 word in the chart `M_1` (`x₀ = 0`) of the
  degenerate frame `a = A`, `b = B`, `a′ = A + πχ`, `b′ = B + πχ` (`r7_hword`: the upper heights continue the lower
  ones across the two strip ends). The bounds `a, b ≥ λ(k)`, `a′, b′ ≥ λ(k) + πχ` hold for every `c, c′ ≥ 0`
  (`isFig51Bounds_r7Frame`; `λ(k) = λ − πχ/2`, `A ≥ λ + πχ/2`, `B ≥ λ + πχ/2`).
* **The named input** `Fig51CandLawsStatement`: Proposition 5.9's per-candidate killed laws (`IsStageLawFarK`, R78) of
  the concrete root and node candidates, for every Figure 5.1 strip counterflow — exactly the `hlaw₀`, `hlaw` of
  `StripMarks.prop513_path_of_candLaws`, with their noise and past data. It is a hypothesis of the theorems below only.
* `prop513_path_of_fig51CandLaws`: Proposition 5.13 for every Figure 5.1 strip counterflow from the named input
  (`prop513_path_of_candLaws`).
* **`r7_det`**: the `det` field for every R.7 configuration, decomposition and version.

R48: the inputs are `Theorem12ParamCond44Statement` (R74), Zhan's Part A (`PartAInputsSixteenDivOfClearance`), the
staged prefix first-hit statement and the per-candidate laws; nothing uses Theorem 1.2/1.3, `Theorem12ParamStatement`,
`Theorem13Statement` or any `*_of_param`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter Topology Function
open LQGMetric (DistOn)
open QuantumZipper (H Hbar chiC)
open SupercriticalConformalCovariance.GM24 (smoothDist)
open scoped NNReal ENNReal Real

namespace InteractingSLE.Sec7.Hsd

open WholeField PocketWordIn StripSysField StripMarks R7Outer R7Leaves
open Sec5 Sec5.Prop513TreeExtract Sec5.Prop513Schedule Sec5.Prop513Target Exist.StagedLaw Exist.Staged
  Sec7.AdmCode Restart Sec4 Theorem14.StagedReg Sec5.GlueCond Sec5.CrossCond.Word49 LawUnique
  Sec5.Prop59System Sec5.Prop59Stage Sec5.Prop59Pieces Sec5.Prop59Nodes Sec5.Prop59NodeTree Sec5.Prop59Tips
  Sec5.CrossCond.StagedK2 Sec5.CrossCond.StagedKill Sec5.CrossCond.StagedCand Sec5.Prop59Sched Sec5.StripRevVisit
  Sec5.Prop513Asm Sec5.Prop513Bridge

/-! ### The named input: Proposition 5.9's per-candidate killed laws for a Figure 5.1 counterflow -/

/-- **Proposition 5.9's per-candidate killed laws for every Figure 5.1 strip counterflow** (named input, not proved
here): for every Figure 5.1 field `h` (frame `x₀ a b a′ b′` with the bounds of §5.2) and every strip counterflow
driver `W` (lifetime `ζ`, a generating trace `γ`), there are an extension space `(Ωa, Pa)` (standard Borel,
probability), noise and past data `noise₀, base₀, noise, base` such that the concrete root candidates
(`rootCand`) and node candidates (`nodeCand`) of the canonical schedules satisfy the killed stage law
`IsStageLawFarK` (R78) on their canonical pasts — the `hlaw₀`, `hlaw` of `StripMarks.prop513_path_of_candLaws`
(PROVE-STAGEDK-CAND / PROVE-STAGED-REP's target, R71 Part (3), R73 §2). -/
def Fig51CandLawsStatement (h44 : Theorem12ParamCond44Statement.{0}) : Prop :=
  ∀ {κ x₀ a b a' b' : ℝ} (hκ : 0 < κ) (hκ4 : κ < 4) (hb : IsFig51Bounds κ a b a' b')
    {Ω : Type} [MeasurableSpace Ω] [StandardBorelSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (h : Ω → DistOn upperHalfPlaneOpens) (W : ℝ≥0 → Ω → ℝ) (ζ : Ω → ℝ≥0∞) (γ : Ω → ℝ≥0 → ℂ),
    IsStripGFF κ P h (fig51Lower a b) (fig51Upper x₀ a' b') {0} {x₀} →
    IsStripCounterflowDriver κ 0 (Real.exp (π * x₀)) P h W ζ →
    (∀ᵐ ω ∂P, IsGeneratingTrace (fun t => W t ω) (ζ ω) (γ ω)) →
    ∃ (Ωa : Type) (_ : MeasurableSpace Ωa) (_ : StandardBorelSpace Ωa) (Pa : Measure Ωa)
      (_ : IsProbabilityMeasure Pa)
      (noise₀ : ℚ → (j : ℕ) → (Fin j → ℝ≥0) → ℝ≥0 → Ω → ℝ) (base₀ : ℚ → MeasurableSpace (Ω × Ωa))
      (noise : ℕ → ℚ → (j : ℕ) → (Fin j → ℝ≥0) → ℝ≥0 → Ω → ℝ) (base : ℕ → ℚ → MeasurableSpace (Ω × Ωa)),
      (∀ q, base₀ q ≤ (inferInstance : MeasurableSpace (Ω × Ωa))) ∧
      (∀ q : ℚ, 0 < q → ∀ j t, IsStageLawFarK κ (P.prod Pa)
        (canonQ (base₀ q) (rootCand x₀ h44 hκ hκ4 hb P h W ζ (canonLam W ζ) (canonXL x₀ hκ hb W ζ)
          (canonXR x₀ hκ hb W ζ) noise₀ (Ωa := Ωa) q) ratGrid (rootNL_pos _) (rootNR_pos _)
          (rootStart x₀ hκ hb (canonXL x₀ hκ hb W ζ) (canonXR x₀ hκ hb W ζ) q) j t)
        (canonR (rootCand x₀ h44 hκ hκ4 hb P h W ζ (canonLam W ζ) (canonXL x₀ hκ hb W ζ)
          (canonXR x₀ hκ hb W ζ) noise₀ (Ωa := Ωa) q) ratGrid (rootNL_pos _) (rootNR_pos _)
          (rootStart x₀ hκ hb (canonXL x₀ hκ hb W ζ) (canonXR x₀ hκ hb W ζ) q) univ j t)
        (stageρL κ (rootρL κ (sourceWord (x₀ := x₀) hκ hb)) j)
        (stageρR κ (rootρR κ (sourceWord (x₀ := x₀) hκ hb)) j)
        (farL (Nat.lt_of_lt_of_le (rootNL_pos _) (Nat.le_add_right _ j)))
        (farR (Nat.lt_of_lt_of_le (rootNR_pos _) (Nat.le_add_right _ j)))
        (canonY (rootCand x₀ h44 hκ hκ4 hb P h W ζ (canonLam W ζ) (canonXL x₀ hκ hb W ζ)
          (canonXR x₀ hκ hb W ζ) noise₀ (Ωa := Ωa) q) (rootStart x₀ hκ hb (canonXL x₀ hκ hb W ζ)
            (canonXR x₀ hκ hb W ζ) q) j t)
        (rootCand x₀ h44 hκ hκ4 hb P h W ζ (canonLam W ζ) (canonXL x₀ hκ hb W ζ) (canonXR x₀ hκ hb W ζ)
          noise₀ (Ωa := Ωa) q j t).W
        (rootCand x₀ h44 hκ hκ4 hb P h W ζ (canonLam W ζ) (canonXL x₀ hκ hb W ζ) (canonXR x₀ hκ hb W ζ)
          noise₀ (Ωa := Ωa) q j t).VL
        (rootCand x₀ h44 hκ hκ4 hb P h W ζ (canonLam W ζ) (canonXL x₀ hκ hb W ζ) (canonXR x₀ hκ hb W ζ)
          noise₀ (Ωa := Ωa) q j t).VR
        (rootCand x₀ h44 hκ hκ4 hb P h W ζ (canonLam W ζ) (canonXL x₀ hκ hb W ζ) (canonXR x₀ hκ hb W ζ)
          noise₀ (Ωa := Ωa) q j t).B
        (rootCand x₀ h44 hκ hκ4 hb P h W ζ (canonLam W ζ) (canonXL x₀ hκ hb W ζ) (canonXR x₀ hκ hb W ζ)
          noise₀ (Ωa := Ωa) q j t).ζ) ∧
      (∀ n q, base n q ≤ (inferInstance : MeasurableSpace (Ω × Ωa))) ∧
      (∀ (n : ℕ) (q : ℚ), 0 < q → ∀ j t, IsStageLawFarK κ (P.prod Pa)
        (canonQ (nodeBase x₀ h44 hκ hκ4 hb P h W ζ noise base n q)
          (nodeCand (Ωa := Ωa) x₀ h44 hκ hκ4 hb P h W ζ noise n q) ratGrid
          (nodeNL_pos x₀ hκ hb n) (nodeNR_pos x₀ hκ hb n) (nodeStart x₀ h44 hκ hκ4 hb P h W ζ noise n q) j t)
        (canonR (nodeCand (Ωa := Ωa) x₀ h44 hκ hκ4 hb P h W ζ noise n q) ratGrid (nodeNL_pos x₀ hκ hb n)
          (nodeNR_pos x₀ hκ hb n) (nodeStart x₀ h44 hκ hκ4 hb P h W ζ noise n q)
          (nodeR0 x₀ h44 hκ hκ4 hb P h W ζ noise n q) j t)
        (stageρL κ (nodeρL κ (sourceWord (x₀ := x₀) hκ hb) (scheduleAt n)) j)
        (stageρR κ (nodeρR κ (sourceWord (x₀ := x₀) hκ hb) (scheduleAt n)) j)
        (farL (Nat.lt_of_lt_of_le (nodeNL_pos x₀ hκ hb n) (Nat.le_add_right _ j)))
        (farR (Nat.lt_of_lt_of_le (nodeNR_pos x₀ hκ hb n) (Nat.le_add_right _ j)))
        (canonY (nodeCand (Ωa := Ωa) x₀ h44 hκ hκ4 hb P h W ζ noise n q)
          (nodeStart x₀ h44 hκ hκ4 hb P h W ζ noise n q) j t)
        (nodeCand (Ωa := Ωa) x₀ h44 hκ hκ4 hb P h W ζ noise n q j t).W
        (nodeCand (Ωa := Ωa) x₀ h44 hκ hκ4 hb P h W ζ noise n q j t).VL
        (nodeCand (Ωa := Ωa) x₀ h44 hκ hκ4 hb P h W ζ noise n q j t).VR
        (nodeCand (Ωa := Ωa) x₀ h44 hκ hκ4 hb P h W ζ noise n q j t).B
        (nodeCand (Ωa := Ωa) x₀ h44 hκ hκ4 hb P h W ζ noise n q j t).ζ)

/-- **Proposition 5.13 for every Figure 5.1 strip counterflow from Proposition 5.9's per-candidate laws**: a version of
the counterflow trace measurable for any σ-algebra `𝒢` making the field measurable
(`StripMarks.prop513_path_of_candLaws` with the laws of `Fig51CandLawsStatement`). -/
theorem prop513_path_of_fig51CandLaws
    (h44 : Theorem12ParamCond44Statement.{0}) (hA : PartAInputsSixteenDivOfClearance)
    (hFH : StagedPrefixFirstHitStatement.{0}) (hlaws : Fig51CandLawsStatement h44)
    {κ x₀ a b a' b' : ℝ} (hκ : 0 < κ) (hκ4 : κ < 4) (hb : IsFig51Bounds κ a b a' b')
    {Ω : Type} {𝒢 : MeasurableSpace Ω} [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P]
    {h : Ω → DistOn upperHalfPlaneOpens} (hh𝒢 : Measurable[𝒢] h)
    (hG : IsStripGFF κ P h (fig51Lower a b) (fig51Upper x₀ a' b') {0} {x₀})
    {W : ℝ≥0 → Ω → ℝ} {ζ : Ω → ℝ≥0∞} {γ : Ω → ℝ≥0 → ℂ}
    (hcf : IsStripCounterflowDriver κ 0 (Real.exp (π * x₀)) P h W ζ)
    (htr : ∀ᵐ ω ∂P, IsGeneratingTrace (fun t => W t ω) (ζ ω) (γ ω)) :
    ∃ Γ' : Ω → ℝ≥0 → ℂ, (∀ t, StronglyMeasurable[𝒢] fun ω => Γ' ω t) ∧ ∀ᵐ ω ∂P, Γ' ω = γ ω := by
  obtain ⟨Ωa, _, _, Pa, _, noise₀, base₀, noise, base, hbase₀, hlaw₀, hbase, hlaw⟩ :=
    hlaws hκ hκ4 hb P h W ζ γ hG hcf htr
  exact prop513_path_of_candLaws h44 hA hFH hκ hκ4 hb hh𝒢 hG hcf htr noise₀ base₀ hbase₀ hlaw₀ noise base
    hbase hlaw

/-! ### The Figure 5.1 frame of the R.7 counterflow word -/

section Frame

variable {κ k rL rR c c' : ℝ}

/-- The counterflow word of the data `prop74Data A B` on `ℝ₋`: `−B − πχ`. -/
theorem counterflowData_prop74Data_of_neg (hκ : 0 < κ) (A B : ℝ) {x : ℝ} (hx : x < 0) :
    counterflowData κ (prop74Data A B) x = -B - π * chiC κ := by
  have hx' : ¬ (-x⁻¹ < 0) := not_lt.2 (neg_nonneg.2 (inv_nonpos.2 hx.le))
  simp only [counterflowData, inverseData, returnData, cfOffset, cfCoeff, liftBoundary, prop74Data, hx, hx',
    ↓reduceIte, Sec4.chiC_sixteen_div hκ]
  ring

/-- The counterflow word of the data `prop74Data A B` on `ℝ₊`: `A + πχ`. -/
theorem counterflowData_prop74Data_of_pos (hκ : 0 < κ) (A B : ℝ) {x : ℝ} (hx : 0 < x) :
    counterflowData κ (prop74Data A B) x = A + π * chiC κ := by
  have hx' : -x⁻¹ < 0 := neg_neg_iff_pos.2 (inv_pos.2 hx)
  have hx'' : ¬ (x < 0) := not_lt.2 hx.le
  simp only [counterflowData, inverseData, returnData, cfOffset, cfCoeff, liftBoundary, prop74Data, hx', hx'',
    ↓reduceIte, Sec4.chiC_sixteen_div hκ]
  ring

/-- **The Figure 5.1 frame of the R.7 counterflow word** (heights `c`, `c′`): `x₀ = 0`, lower heights `−a = −A`,
`b = B`, upper heights `−a′ = −(A + πχ)`, `b′ = B + πχ`, where `A = r7A + c`, `B = r7B + c′`, `χ = χ(16/k)`. -/
def r7Frame (k rL rR c c' : ℝ) : StripMarks.Frame :=
  ⟨0, r7A k rR + c, r7B k rL + c', r7A k rR + c + π * chiC (16 / k), r7B k rL + c' + π * chiC (16 / k)⟩

/-- **The bounds of §5.2 for the R.7 frame** (`a, b ≥ λ(k)`, `a′, b′ ≥ λ(k) + πχ`, `λ(k) = λ − πχ/2`). -/
theorem isFig51Bounds_r7Frame (hk4 : 4 < k) (hc : 0 ≤ c) (hc' : 0 ≤ c') :
    IsFig51Bounds (16 / k) (r7A k rR + c) (r7B k rL + c') (r7A k rR + c + π * chiC (16 / k))
      (r7B k rL + c' + π * chiC (16 / k)) := by
  have hκ : 0 < 16 / k := R7.sixteen_div_pos (by linarith)
  have hκ4 : 16 / k < 4 := R7.sixteen_div_lt_four hk4
  have hχ := Sec4.chiC_pos hκ hκ4
  have hlam := Sec4.sleLambda_sixteen_div_eq_sub hκ
  have h1 : π / 2 * chiC (16 / k) ≤ r7ThetaHi k rR * chiC (16 / k) :=
    mul_le_mul_of_nonneg_right (le_max_right _ _) hχ.le
  have h2 : r7ThetaLo k rL * chiC (16 / k) ≤ -(π / 2) * chiC (16 / k) :=
    mul_le_mul_of_nonneg_right (min_le_right _ _) hχ.le
  have hp : 0 ≤ π * chiC (16 / k) := mul_nonneg Real.pi_pos.le hχ.le
  simp only [IsFig51Bounds, r7A, r7B]
  rw [hlam]
  refine ⟨by linarith, by linarith, by linarith, by linarith⟩

/-- **The R.7 counterflow word is the Figure 5.1 word of `r7Frame`** off `{−1, 0, 1}` (the identity `hword` of
`StripMarks.h513_of_stripSystem_candLaws`, for the chart `M_1`, `x₀ = 0`). -/
theorem r7_hword (hk4 : 4 < k) :
    ∀ x ∉ counterflowJumps ({0} : Finset ℝ) ∪ Prop513Field.jumps (Real.exp (π * 0)) (stripHJumps {0} {0}),
      counterflowData (16 / k) (prop74Data (r7A k rR + c) (r7B k rL + c')) x =
        stripCounterflowData (16 / k) 0 (Real.exp (π * 0)) (fig51Lower (r7A k rR + c) (r7B k rL + c'))
          (fig51Upper 0 (r7A k rR + c + π * chiC (16 / k)) (r7B k rL + c' + π * chiC (16 / k))) x := by
  intro x hx
  have hκ : 0 < 16 / k := R7.sixteen_div_pos (by linarith)
  have hq : Real.exp (π * 0) = 1 := by rw [mul_zero, Real.exp_zero]
  rw [hq] at hx ⊢
  have hm0 : (0 : ℝ) ∈ counterflowJumps ({0} : Finset ℝ) := Finset.mem_insert_self 0 _
  have hmm : (-1 : ℝ) ∈ Prop513Field.jumps 1 (stripHJumps {0} {0}) := Finset.mem_insert_self (-1) _
  have hx0 : x ≠ 0 := fun h0 => hx (Finset.mem_union_left _ (h0 ▸ hm0))
  have hxm : x ≠ -1 := fun h0 => hx (Finset.mem_union_right _ (h0 ▸ hmm))
  have hx1 : x ≠ 1 := by
    intro h0
    apply hx
    refine Finset.mem_union_right _ (Finset.mem_insert_of_mem (Finset.mem_image.2 ⟨-1, ?_, ?_⟩))
    · exact Finset.mem_insert_self (-1) _
    · rw [h0]; norm_num
  have hpi := Real.pi_pos
  rcases lt_or_gt_of_ne hx0 with hneg | hpos
  · rw [counterflowData_prop74Data_of_neg hκ _ _ hneg]
    rcases lt_or_gt_of_ne hxm with hlt | hgt
    · have hd : x + 1 < 0 := by linarith
      have hr : 1 < (x - 1) / (x + 1) := (one_lt_div_of_neg hd).2 (by linarith)
      have hy : 0 ≤ Real.log ((x - 1) / (x + 1)) / π := div_nonneg (Real.log_pos hr).le hpi.le
      rw [stripCounterflowData_of_lt_neg_one one_pos hlt, fig51Lower, ite_eq_right (not_lt.2 hy)]
      ring
    · have hd : 0 < x + 1 := by linarith
      have hr : 1 < (1 - x) / (x + 1) := (one_lt_div hd).2 (by linarith)
      have hy : 0 ≤ Real.log ((1 - x) / (x + 1)) / π := div_nonneg (Real.log_pos hr).le hpi.le
      rw [stripCounterflowData_of_mem_Ioo_neg_one_zero one_pos ⟨hgt, hneg⟩, fig51Upper, ite_eq_right (not_lt.2 hy)]
      ring
  · rw [counterflowData_prop74Data_of_pos hκ _ _ hpos]
    rcases lt_or_gt_of_ne hx1 with hlt | hgt
    · have hd : 0 < x + 1 := by linarith
      have hr0 : 0 < (1 - x) / (x + 1) := div_pos (by linarith) hd
      have hr : (1 - x) / (x + 1) < 1 := (div_lt_one hd).2 (by linarith)
      have hy : Real.log ((1 - x) / (x + 1)) / π < 0 := div_neg_of_neg_of_pos (Real.log_neg hr0 hr) hpi
      rw [stripCounterflowData_of_mem_Ioo_zero ⟨hpos, hlt⟩, fig51Upper, ite_eq_left hy]
      ring
    · have hd : 0 < x + 1 := by linarith
      have hr0 : 0 < (x - 1) / (x + 1) := div_pos (by linarith) hd
      have hr : (x - 1) / (x + 1) < 1 := (div_lt_one hd).2 (by linarith)
      have hy : Real.log ((x - 1) / (x + 1)) / π < 0 := div_neg_of_neg_of_pos (Real.log_neg hr0 hr) hpi
      rw [stripCounterflowData_of_lt one_pos hgt, fig51Lower, ite_eq_left hy]
      ring

end Frame

/-! ### `hsd.det` for every R.7 configuration -/

section Det

/-- **Proposition 5.13 for the counterflow of an R.7 configuration** (the `det` field of
`R7Leaves.R7ExtremalSideDet`): for every R.7 configuration (heights `c, c′ ≥ 0`), every decomposition of its centred
counterflow driver (`IsCfDecomp`, coupling field `h″`) and every version `η` of the counterflow trace, `η` agrees almost
surely with a process whose coordinates are measurable for `σ(h″)`. The counterflow is the angle-0 flow line of `h″`
for the word `counterflowData (16/k) (prop74Data A B)` (`GW2Cone.isFlowLineDriver_counterflowData` and uniqueness of the
transport), which is the Figure 5.1 word of `r7Frame` (`r7_hword`); Proposition 5.13 then holds in the chart `M_1` from
Proposition 5.9's per-candidate laws (`prop513_path_of_fig51CandLaws`) and transfers to `σ(h″)`
(`comap_eq_strip_parameter`). -/
theorem r7_det (h44 : Theorem12ParamCond44Statement.{0}) (hA : PartAInputsSixteenDivOfClearance)
    (hFH : StagedPrefixFirstHitStatement.{0}) (hlaws : Fig51CandLawsStatement h44)
    {k rL rR c c' : ℝ} (hk4 : 4 < k) (hc : 0 ≤ c) (hc' : 0 ≤ c')
    {Ω : Type} [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {h : Ω → DistOn upperHalfPlaneOpens} {W' : ℝ≥0 → Ω → ℝ} {ζ' : Ω → ℝ≥0∞}
    (hh : IsGFFWithBoundaryData P h (prop74Data (r7A k rR + c) (r7B k rL + c')) ((({0} : Finset ℝ)) : Set ℝ))
    (hcf : IsCenteredCounterflowDriver (16 / k) P h W' ζ')
    {b' : ℝ → ℝ} {J' : Finset ℝ} {h' h'' : Ω → DistOn upperHalfPlaneOpens} {𝓕 : Filtration ℝ≥0 mΩ}
    {VL : Fin (flowLineNL b' J' 0) → ℝ≥0 → Ω → ℝ} {VR : Fin (flowLineNR b' J' 0) → ℝ≥0 → Ω → ℝ}
    {B : ℝ≥0 → Ω → ℝ} (hD : IsCfDecomp k P h W' ζ' b' J' h' h'' 𝓕 VL VR B) {η : Ω → ℝ → ℂ}
    (hηtr : ∀ᵐ ω ∂P, IsGeneratingTrace (fun t => W' t ω) ⊤ (fun t : ℝ≥0 => η ω t)) :
    ∃ Γ' : Ω → ℝ≥0 → ℂ, (∀ t, StronglyMeasurable[MeasurableSpace.comap h'' inferInstance]
      fun ω => Γ' ω t) ∧ ∀ᵐ ω ∂P, Γ' ω = fun t : ℝ≥0 => η ω t := by
  have hκ : 0 < 16 / k := R7.sixteen_div_pos (by linarith)
  have hκ4 : 16 / k < 4 := R7.sixteen_div_lt_four hk4
  have e : 16 / (16 / k) = k := by field_simp
  have hb := isPiecewiseConstant_prop74Data (r7A k rR + c) (r7B k rL + c')
  obtain ⟨h₀, htr₀, hfl₀⟩ := Theorem14.GW2Cone.isFlowLineDriver_counterflowData hκ hb hh hcf
  obtain ⟨-, hT, hTr, -⟩ := hD
  rw [e] at htr₀
  have e₀ : h₀ = h'' := by
    funext ω
    rw [IsChartTransport.unique Chart.isConformal_infinitySourceChart (htr₀ ω) (hT ω)]
    exact (Theorem14.GW2Cone.eq_of_isTranslateAddConst_zero (zero_mul _) (hTr ω)).symm
  rw [e₀] at hfl₀
  have hbP := isPiecewiseConstant_counterflowData (16 / k) hb
  have hG := Theorem14.GW2aPiece.isGFFWithBoundaryData_of_isFlowLineDriver (div_pos (by norm_num) hκ) hbP hfl₀
  have hGF := isStripGFF_parameterSource_of_word hκ hbP hG (r7_hword (rL := rL) (rR := rR) (c := c) (c' := c') hk4)
  have hTF : ∀ ω, IsChartTransport (stripCounterflowChart (Real.exp (π * 0))) (-1) (-(π * chiC (16 / k)))
      (chiC (16 / (16 / k))) (fig51Source (16 / k) 0 h'' ω) (h'' ω) :=
    fun ω => isChartTransport_parameterSource (Real.exp_pos _) _ _ (h'' ω)
  have hcfS : IsStripCounterflowDriver (16 / k) 0 (Real.exp (π * 0)) P (fig51Source (16 / k) 0 h'') W' ζ' := by
    refine ⟨counterflowData (16 / k) (prop74Data (r7A k rR + c) (r7B k rL + c')), counterflowJumps {0}, h'', hbP,
      ?_, hfl₀⟩
    simpa only [zero_add] using hTF
  have htr : ∀ᵐ ω ∂P, IsGeneratingTrace (fun t => W' t ω) (ζ' ω) (fun t : ℝ≥0 => η ω t) := by
    filter_upwards [hηtr, ae_counterflow_trace_r7 hk4 hc hc' hh hcf] with ω hω hζ
    rw [hζ.1]
    exact hω
  obtain ⟨Γ', hm, he⟩ := prop513_path_of_fig51CandLaws h44 hA hFH hlaws hκ hκ4 (isFig51Bounds_r7Frame hk4 hc hc')
    (𝒢 := MeasurableSpace.comap (fig51Source (16 / k) 0 h'') inferInstance) (comap_measurable _) hGF hcfS htr
  refine ⟨Γ', fun t => ?_, he⟩
  rw [← comap_eq_strip_parameter (Real.exp_pos _) hTF]
  exact hm t

end Det

end InteractingSLE.Sec7.Hsd
