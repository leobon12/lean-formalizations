/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Exist.StagedLawStruct
import InteractingSLE.Spec.Exist.StagedLawData

/-!
# The staged conditional law: the named inputs and the retained past

Packet PROVE-STAGEDLAW.

## The named inputs

* **`StopLawStatement`** (single stage; Lemma GW1, p. 618: "every finite completed stage … and every available
  ordinary prefix have their full marked local-set kernel"; Theorem 1.1 at the stop `min t ζ`, with GW1's terminal
  marked convergence when the piece ends at its continuation threshold). For one angle-`θ` flow-line driver `E` of a GFF
  `g` with a word datum `c` under a probability `Q` on a standard Borel space, run for own time `t`: almost surely
  the stopped driver is continuous (its record is `IsDrvGood`) when the stop is finite, and, conditionally on the
  record,
  on `{stop < ⊤}` the field read in the record chart (`recField`) has the Gaussian characteristic functional of the word
  `β (c, θ, record)`; `β` is jointly measurable with sorted values.
* **`RunMeasStatement`** (deterministic): for measurable drivers regular at every sample, the event "instruction `k`
  launches" and the forward chart map at every point after `k` instructions are measurable.
* **`WordMeasStatement`** (deterministic): the flow-line word of a boundary word is a measurable function of the word.

## Main results

* `truncE`: the drivers of the instructions `j < k`, completed by the constant driver;
* `pastMap_succ`, **`measurable_pastMap`**: the retained past is measurable;
* `pastSigma_mono`;
* **`measurableSet_pastSigma_of_run`**, `measurable_pastSigma_of_run`: events and maps determined by the state after
  `k` instructions are measurable for the retained past (fibre argument, `run_eq_of_readRec_eq`).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal

universe u

namespace InteractingSLE

namespace Exist

namespace StagedLaw

open LQGMetric Restart Staged

/-! ### The named inputs -/

/-- **Named input (single stage): the conditional law at the stop of one flow-line piece.** -/
def StopLawStatement : Prop :=
  ∀ κ : ℝ, 0 < κ → κ < 4 →
    ∃ β : BoundaryWord × ℝ × RecData → BoundaryWord, Measurable β ∧ (∀ x, (β x).IsSorted) ∧
      ∀ (c : BoundaryWord) (θ : ℝ) (t : ℝ≥0∞) {Ω : Type u} [MeasurableSpace Ω]
        [StandardBorelSpace Ω] (Q : Measure Ω) [IsProbabilityMeasure Q] (g : Ω → DistOn upperHalfPlaneOpens)
        (E : Ω → (ℝ≥0 → ℝ) × ℝ≥0∞), Measurable E → (∀ ω, IsRegularDriver (E ω)) →
        IsFlowLineDriver κ c.fn c.jumps θ Q g (fun s ω => (E ω).1 s) (fun ω => (E ω).2) →
        (∀ᵐ ω ∂Q, min t (E ω).2 ≠ ⊤ → LocalExt.IsDrvGood (recHist (recOf t (E ω)))) ∧
        ∀ φ : TestOn upperHalfPlaneOpens, ∀ᵐ ω ∂Q, min t (E ω).2 ≠ ⊤ →
          Q[fun ω' => Complex.exp (Complex.I * (recField κ (recOf t (E ω')) (g ω') φ : ℂ)) |
              MeasurableSpace.comap (fun ω' => recOf t (E ω')) inferInstance] ω =
            gaussCF (β (c, θ, recOf t (E ω))) φ

/-- **Named input (deterministic): the run is Borel.** -/
def RunMeasStatement : Prop :=
  ∀ (κ : ℝ) (b : ℝ → ℝ) (jumps : Finset ℝ), IsPiecewiseConstantBoundaryData b jumps → ∀ (spec : ExplSpec)
    {Ω : Type u} [MeasurableSpace Ω] (E : ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞), (∀ j, Measurable (E j)) →
    (∀ j ω, IsRegularDriver (E j ω)) → ∀ k : ℕ,
      MeasurableSet {ω | (ExplState.run κ b jumps spec (fun j => E j ω) (k + 1)).2.2.2.1 k ≠ none} ∧
      ∀ z : ℂ, Measurable fun ω => (ExplState.run κ b jumps spec (fun j => E j ω) k).2.2.2.2.1.1 z

/-- **Named input (deterministic): the flow-line word of a boundary word is measurable in the word.** -/
def WordMeasStatement : Prop :=
  Measurable (fun c : BoundaryWord => flowLineNL c.fn c.jumps 0) ∧
    Measurable (fun c : BoundaryWord => flowLineNR c.fn c.jumps 0) ∧
    ∀ κ θ : ℝ, Measurable fun c : BoundaryWord => padFL κ θ c.fn c.jumps

/-! ### Truncated driver families -/

/-- The constant driver (`0`, infinite lifetime), regular at every sample. -/
def zeroDrv : (ℝ≥0 → ℝ) × ℝ≥0∞ := (fun _ => 0, ⊤)

theorem isRegularDriver_zeroDrv : IsRegularDriver zeroDrv :=
  ⟨continuous_const.continuousOn, rfl, fun _ _ => rfl, fun h => absurd rfl h⟩

/-- The drivers of the instructions `j < k`, completed by the constant driver. -/
def truncE {Ω : Type*} (k : ℕ) (E : ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞) : ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞ :=
  fun j ω => if j < k then E j ω else zeroDrv

theorem truncE_of_lt {Ω : Type*} {k j : ℕ} (E : ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞) (hj : j < k) : truncE k E j = E j := by
  funext ω
  simp only [truncE, hj, ↓reduceIte]

theorem measurable_truncE {Ω : Type*} [MeasurableSpace Ω] {k : ℕ} {E : ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞}
    (hE : ∀ j < k, Measurable (E j)) (j : ℕ) : Measurable (truncE k E j) := by
  by_cases hj : j < k
  · rw [truncE_of_lt E hj]; exact hE j hj
  · have : truncE k E j = fun _ => zeroDrv := by funext ω; simp only [truncE, hj, ↓reduceIte]
    rw [this]; exact measurable_const

theorem isRegularDriver_truncE {Ω : Type*} {k : ℕ} {E : ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞}
    (hE : ∀ j < k, ∀ ω, IsRegularDriver (E j ω)) (j : ℕ) (ω : Ω) : IsRegularDriver (truncE k E j ω) := by
  by_cases hj : j < k
  · rw [truncE_of_lt E hj]; exact hE j hj ω
  · simp only [truncE, hj, ↓reduceIte]; exact isRegularDriver_zeroDrv

section Past

variable {κ : ℝ} {b : ℝ → ℝ} {jumps : Finset ℝ}

theorem run_truncE {Ω : Type*} (spec : ExplSpec) (E : ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞) {n k : ℕ} (hn : n ≤ k)
    (ω : Ω) : ExplState.run κ b jumps spec (fun j => truncE k E j ω) n =
      ExplState.run κ b jumps spec (fun j => E j ω) n :=
  run_congr spec fun j hj => by rw [truncE_of_lt E (lt_of_lt_of_le hj hn)]

/-- Records of earlier instructions are never changed. -/
theorem retained_run_of_lt (spec : ExplSpec) (D : ℕ → (ℝ≥0 → ℝ) × ℝ≥0∞) {i : ℕ} :
    ∀ {n : ℕ}, i < n → (ExplState.run κ b jumps spec D n).2.2.1 i =
      (ExplState.run κ b jumps spec D (i + 1)).2.2.1 i
  | 0, h => absurd h (Nat.not_lt_zero i)
  | n + 1, h => by
    rcases Nat.lt_succ_iff_lt_or_eq.1 h with h | h
    · rw [retained_run_succ_of_lt spec D h, retained_run_of_lt spec D h]
    · rw [h]

/-- The retained past before `j + 1` extends the retained past before `j` by the record of instruction `j`. -/
theorem pastMap_succ {Ω : Type*} (spec : ExplSpec) (E : ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞) (j : ℕ) (ω : Ω) :
    pastMap κ b jumps spec E (j + 1) ω =
      Fin.snoc (α := fun _ => RecData) (pastMap κ b jumps spec E j ω)
        (readRec ((ExplState.run κ b jumps spec (fun i => E i ω) (j + 1)).2.2.1 j)) := by
  funext i
  refine Fin.lastCases ?_ (fun i => ?_) i
  · rw [Fin.snoc_last]
    rfl
  · rw [Fin.snoc_castSucc]
    change readRec ((ExplState.run κ b jumps spec (fun i => E i ω) (j + 1)).2.2.1 i) =
      readRec ((ExplState.run κ b jumps spec (fun i => E i ω) j).2.2.1 i)
    rw [retained_run_succ_of_lt spec _ i.2]

/-- The retained past before `j ≤ k` is read from the retained past before `k`. -/
theorem pastMap_castLE {Ω : Type*} (spec : ExplSpec) (E : ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞) {j k : ℕ} (hjk : j ≤ k)
    (ω : Ω) (i : Fin j) : pastMap κ b jumps spec E j ω i = pastMap κ b jumps spec E k ω (Fin.castLE hjk i) := by
  change readRec ((ExplState.run κ b jumps spec (fun i => E i ω) j).2.2.1 i) =
    readRec ((ExplState.run κ b jumps spec (fun i => E i ω) k).2.2.1 i)
  rw [retained_run_of_lt spec _ i.2, retained_run_of_lt spec _ (lt_of_lt_of_le i.2 hjk)]

theorem pastSigma_mono {Ω : Type*} (spec : ExplSpec) (E : ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞) {j k : ℕ} (hjk : j ≤ k) :
    pastSigma κ b jumps spec E j ≤ pastSigma κ b jumps spec E k := by
  rw [pastSigma_eq_comap, pastSigma_eq_comap]
  have e : pastMap κ b jumps spec E j = (fun u : PastData k => fun i : Fin j => u (Fin.castLE hjk i)) ∘
      pastMap κ b jumps spec E k := by
    funext ω i
    exact pastMap_castLE spec E hjk ω i
  rw [e, ← MeasurableSpace.comap_comp]
  have hm : Measurable fun u : PastData k => fun i : Fin j => u (Fin.castLE hjk i) :=
    measurable_pi_iff.2 fun i => measurable_pi_apply _
  exact MeasurableSpace.comap_mono hm.comap_le

/-- The record of instruction `j` in the retained past. -/
theorem readRec_retained_succ {Ω : Type*} (spec : ExplSpec) (E : ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞) (j : ℕ) (ω : Ω) :
    readRec ((ExplState.run κ b jumps spec (fun i => E i ω) (j + 1)).2.2.1 j) =
      if (ExplState.run κ b jumps spec (fun i => E i ω) (j + 1)).2.2.2.1 j = none then
        readRec (fun _ => 0, 0, false) else recOf (instrTime spec j) (E j ω) := by
  rw [retained_run_succ_self]
  split_ifs <;> rfl

end Past

section Meas

variable {κ : ℝ} {b : ℝ → ℝ} {jumps : Finset ℝ} {Ω : Type u} [mΩ : MeasurableSpace Ω]

theorem measurable_snoc {n : ℕ} {f : Ω → Fin n → RecData} (hf : Measurable f) {g : Ω → RecData}
    (hg : Measurable g) : Measurable fun ω => Fin.snoc (α := fun _ => RecData) (f ω) (g ω) := by
  refine measurable_pi_iff.2 fun i => ?_
  induction i using Fin.lastCases with
  | last => simp only [Fin.snoc_last]; exact hg
  | cast j => simp only [Fin.snoc_castSucc]; exact (measurable_pi_apply j).comp hf

/-- The launch event of instruction `n < k` is measurable (from `RunMeasStatement`). -/
theorem measurableSet_launch (hB : RunMeasStatement.{u}) (hb : IsPiecewiseConstantBoundaryData b jumps)
    (spec : ExplSpec) {E : ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞} {k : ℕ} (hEm : ∀ j < k, Measurable (E j))
    (hreg : ∀ j < k, ∀ ω, IsRegularDriver (E j ω)) {n : ℕ} (hn : n < k) :
    MeasurableSet {ω | (ExplState.run κ b jumps spec (fun j => E j ω) (n + 1)).2.2.2.1 n ≠ none} := by
  have h := (hB κ b jumps hb spec (truncE k E) (measurable_truncE hEm) (isRegularDriver_truncE hreg) n).1
  simp only [run_truncE spec E (Nat.succ_le_of_lt hn)] at h
  exact h

/-- The forward chart map after `n ≤ k` instructions is measurable at every point (from `RunMeasStatement`). -/
theorem measurable_chart_apply (hB : RunMeasStatement.{u}) (hb : IsPiecewiseConstantBoundaryData b jumps)
    (spec : ExplSpec) {E : ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞} {k : ℕ} (hEm : ∀ j < k, Measurable (E j))
    (hreg : ∀ j < k, ∀ ω, IsRegularDriver (E j ω)) {n : ℕ} (hn : n ≤ k) (z : ℂ) :
    Measurable fun ω => (ExplState.run κ b jumps spec (fun j => E j ω) n).2.2.2.2.1.1 z := by
  have h := (hB κ b jumps hb spec (truncE k E) (measurable_truncE hEm) (isRegularDriver_truncE hreg) n).2 z
  simp only [run_truncE spec E hn] at h
  exact h

/-- **The retained past is measurable** (from `RunMeasStatement`). -/
theorem measurable_pastMap (hB : RunMeasStatement.{u}) (hb : IsPiecewiseConstantBoundaryData b jumps)
    (spec : ExplSpec) {E : ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞} {k : ℕ} (hEm : ∀ j < k, Measurable (E j))
    (hreg : ∀ j < k, ∀ ω, IsRegularDriver (E j ω)) : ∀ n ≤ k, Measurable (pastMap κ b jumps spec E n)
  | 0, _ => measurable_pi_iff.2 fun i => i.elim0
  | n + 1, hn => by
    have ih := measurable_pastMap hB hb spec hEm hreg n (Nat.le_of_succ_le hn)
    have hfun : pastMap κ b jumps spec E (n + 1) = fun ω => Fin.snoc (α := fun _ => RecData)
        (pastMap κ b jumps spec E n ω)
        (if (ExplState.run κ b jumps spec (fun i => E i ω) (n + 1)).2.2.2.1 n = none then
          readRec (fun _ => 0, 0, false) else recOf (instrTime spec n) (E n ω)) := by
      funext ω
      rw [pastMap_succ, readRec_retained_succ]
    rw [hfun]
    refine measurable_snoc ih ?_
    have hL := measurableSet_launch (κ := κ) hB hb spec hEm hreg (Nat.lt_of_succ_le hn)
    have e : (fun ω => if (ExplState.run κ b jumps spec (fun i => E i ω) (n + 1)).2.2.2.1 n = none then
        readRec (fun _ => 0, 0, false) else recOf (instrTime spec n) (E n ω)) =
        {ω | (ExplState.run κ b jumps spec (fun j => E j ω) (n + 1)).2.2.2.1 n ≠ none}.piecewise
          (fun ω => recOf (instrTime spec n) (E n ω)) fun _ => readRec (fun _ => 0, 0, false) := by
      funext ω
      by_cases h : (ExplState.run κ b jumps spec (fun i => E i ω) (n + 1)).2.2.2.1 n = none
      · have hn' : ω ∉ {ω | (ExplState.run κ b jumps spec (fun j => E j ω) (n + 1)).2.2.2.1 n ≠ none} := by
          simpa using h
        simp only [h, ↓reduceIte, piecewise_eq_of_notMem _ _ _ hn']
      · have hn' : ω ∈ {ω | (ExplState.run κ b jumps spec (fun j => E j ω) (n + 1)).2.2.2.1 n ≠ none} := h
        simp only [h, ↓reduceIte, piecewise_eq_of_mem _ _ _ hn']
    rw [e]
    exact Measurable.piecewise hL (measurable_recOf (hEm n (Nat.lt_of_succ_le hn))
      (hreg n (Nat.lt_of_succ_le hn)) _) measurable_const

omit mΩ in
/-- Equal retained pasts give equal states (drivers regular before `k`). -/
theorem run_eq_of_pastMap_eq (spec : ExplSpec) {E : ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞} {k : ℕ}
    (hreg : ∀ j < k, ∀ ω, IsRegularDriver (E j ω)) {ω ω' : Ω}
    (h : pastMap κ b jumps spec E k ω = pastMap κ b jumps spec E k ω') :
    ExplState.run κ b jumps spec (fun j => E j ω) k = ExplState.run κ b jumps spec (fun j => E j ω') k :=
  run_eq_of_readRec_eq spec (fun j hj => hreg j hj ω) (fun j hj => hreg j hj ω') fun i hi =>
    congrFun h ⟨i, hi⟩

variable [StandardBorelSpace Ω]

/-- **Events determined by the state after `k` instructions are events of the retained past.** -/
theorem measurableSet_pastSigma_of_run (hB : RunMeasStatement.{u}) (hb : IsPiecewiseConstantBoundaryData b jumps)
    (spec : ExplSpec) {E : ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞} {k : ℕ} (hEm : ∀ j < k, Measurable (E j))
    (hreg : ∀ j < k, ∀ ω, IsRegularDriver (E j ω)) {S : Set Ω} (hS : MeasurableSet S)
    (hsat : ∀ ω ω', ExplState.run κ b jumps spec (fun j => E j ω) k =
      ExplState.run κ b jumps spec (fun j => E j ω') k → ω ∈ S → ω' ∈ S) :
    MeasurableSet[pastSigma κ b jumps spec E k] S := by
  rw [pastSigma_eq_comap]
  exact measurableSet_comap_of_saturated (measurable_pastMap hB hb spec hEm hreg k le_rfl) hS
    fun ω ω' h hω => hsat ω ω' (run_eq_of_pastMap_eq spec hreg h) hω

/-- **Maps determined by the state after `k` instructions are measurable for the retained past.** -/
theorem measurable_pastSigma_of_run (hB : RunMeasStatement.{u}) (hb : IsPiecewiseConstantBoundaryData b jumps)
    (spec : ExplSpec) {E : ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞} {k : ℕ} (hEm : ∀ j < k, Measurable (E j))
    (hreg : ∀ j < k, ∀ ω, IsRegularDriver (E j ω)) {Y : Type*} [MeasurableSpace Y] {g : Ω → Y}
    (hg : Measurable g) (hsat : ∀ ω ω', ExplState.run κ b jumps spec (fun j => E j ω) k =
      ExplState.run κ b jumps spec (fun j => E j ω') k → g ω = g ω') :
    Measurable[pastSigma κ b jumps spec E k] g := by
  rw [pastSigma_eq_comap]
  exact measurable_comap_of_saturated (measurable_pastMap hB hb spec hEm hreg k le_rfl) hg
    fun ω ω' h => hsat ω ω' (run_eq_of_pastMap_eq spec hreg h)

/-- **Under the regular conditional law given the retained past, the state is that of `ω₀`.** -/
theorem ae_ae_run_eq (hB : RunMeasStatement.{u}) (hb : IsPiecewiseConstantBoundaryData b jumps)
    (spec : ExplSpec) {E : ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞} {k : ℕ} (hEm : ∀ j < k, Measurable (E j))
    (hreg : ∀ j < k, ∀ ω, IsRegularDriver (E j ω)) {P : Measure Ω} [IsProbabilityMeasure P] :
    ∀ᵐ ω₀ ∂P, ∀ᵐ ω ∂(condExpKernel P (pastSigma κ b jumps spec E k) ω₀),
      ExplState.run κ b jumps spec (fun j => E j ω) k = ExplState.run κ b jumps spec (fun j => E j ω₀) k := by
  let := upgradeStandardBorel (PastData k)
  have hm := measurable_pastMap (κ := κ) hB hb spec hEm hreg k le_rfl
  have h := Sec7.Aux122Disint.ae_ae_condExpKernel_eq (P := P) (𝓔 := pastSigma κ b jumps spec E k)
    (by rw [pastSigma_eq_comap]; exact hm.comap_le) (f := pastMap κ b jumps spec E k)
    (by rw [pastSigma_eq_comap]; exact comap_measurable _)
  filter_upwards [h] with ω₀ hω₀
  filter_upwards [hω₀] with ω hω
  exact run_eq_of_pastMap_eq spec hreg hω

end Meas

end StagedLaw

end Exist

end InteractingSLE
