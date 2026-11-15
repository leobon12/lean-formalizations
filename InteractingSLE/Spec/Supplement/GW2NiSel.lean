/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW2BnLoss
import InteractingSLE.Spec.Sec7.Aux122Disint

/-!
# The cap and buffer selection: the kernel bound of a moving source buffer

Packet PROVE-GW2-NEARIMG2 (layer 1, the selection half). A candidate of J31/J32 is `Nat.pair i (Nat.pair q b)`:
an angle index `i`, a cap index `q` (cap value `capv q`) and a buffer index `b`. Clause (iii) of `VNearImgOn` needs
the near stop below the J31 sample's source buffer, which holds only for large caps and buffers. Here the
selection `kSel` is chosen at the conditioning sample `ω₀`: if almost surely, for every `n` and angle, all caps past
some value and then all buffers past some index avoid the bad set `Z n i q b`, then for `P`-a.e. `ω₀` the selected
pair has conditional measure at most `1/(m+1)`.

* `measurableSet_eventually_notMem`, `measurableSet_capGood`, `monotone_capGood`;
* **`exists_pair_measure_le`**: for one finite measure, two-level dominated convergence (first the cap, then the
  buffer; no uniformity of the buffer threshold in the cap is needed);
* **`exists_kSel`**: the selection, for `P`-a.e. conditioning sample and all `n`, angles and `m`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped NNReal ENNReal

namespace InteractingSLE.Theorem14.GW2Ni

section Measure

variable {Ω : Type*} [MeasurableSpace Ω]

/-- Eventually avoiding a measurable sequence of sets is a measurable event. -/
theorem measurableSet_eventually_notMem {Z : ℕ → Set Ω} (hZ : ∀ b, MeasurableSet (Z b)) :
    MeasurableSet {ξ | ∀ᶠ b in atTop, ξ ∉ Z b} := by
  have e : {ξ | ∀ᶠ b in atTop, ξ ∉ Z b} = ⋃ B : ℕ, ⋂ b : ℕ, ⋂ (_ : B ≤ b), (Z b)ᶜ := by
    ext ξ
    simp only [mem_ofPred_eq, eventually_atTop, mem_iUnion, mem_iInter, mem_compl_iff]
  rw [e]
  exact MeasurableSet.iUnion fun B => MeasurableSet.iInter fun b =>
    MeasurableSet.iInter fun _ => (hZ b).compl

/-- **The cap-good event**: every cap of value at least `N` is eventually (in the buffer) good. -/
def capGood (Z : ℕ → ℕ → Set Ω) (capv : ℕ → ℝ≥0) (N : ℕ) : Set Ω :=
  {ξ | ∀ q, (N : ℝ≥0) ≤ capv q → ∀ᶠ b in atTop, ξ ∉ Z q b}

theorem measurableSet_capGood {Z : ℕ → ℕ → Set Ω} (hZ : ∀ q b, MeasurableSet (Z q b)) (capv : ℕ → ℝ≥0)
    (N : ℕ) : MeasurableSet (capGood Z capv N) := by
  have e : capGood Z capv N = ⋂ q : ℕ, ⋂ (_ : (N : ℝ≥0) ≤ capv q), {ξ | ∀ᶠ b in atTop, ξ ∉ Z q b} := by
    ext ξ
    simp only [capGood, mem_ofPred_eq, mem_iInter]
  rw [e]
  exact MeasurableSet.iInter fun q => MeasurableSet.iInter fun _ => measurableSet_eventually_notMem (hZ q)

omit [MeasurableSpace Ω] in
theorem monotone_capGood (Z : ℕ → ℕ → Set Ω) (capv : ℕ → ℝ≥0) : Monotone (capGood Z capv) :=
  fun N N' hNN' _ hξ q hq => hξ q (le_trans (by exact_mod_cast hNN') hq)

/-- **Two-level dominated convergence.** If almost every `ξ` has a cap value past which every cap is eventually
(in the buffer) good, then some pair `(q, b)` has a bad set of measure at most `ε`. -/
theorem exists_pair_measure_le {μ : Measure Ω} [IsFiniteMeasure μ] {Z : ℕ → ℕ → Set Ω}
    (hZ : ∀ q b, MeasurableSet (Z q b)) {capv : ℕ → ℝ≥0} (hcap : ∀ Q : ℝ≥0, ∃ q, Q ≤ capv q)
    (hgood : ∀ᵐ ξ ∂μ, ∃ Q : ℝ≥0, ∀ q, Q ≤ capv q → ∀ᶠ b in atTop, ξ ∉ Z q b) {ε : ℝ≥0∞} (hε : 0 < ε) :
    ∃ q b, μ (Z q b) ≤ ε := by
  have hε2 : 0 < ε / 2 := ENNReal.half_pos hε.ne'
  -- the cap level
  have hev : ∀ᵐ ξ ∂μ, ∀ᶠ N in atTop, ξ ∉ (capGood Z capv N)ᶜ := by
    filter_upwards [hgood] with ξ ⟨Q, hQ⟩
    filter_upwards [eventually_ge_atTop ⌈(Q : ℝ)⌉₊] with N hN
    rw [Set.notMem_compl_iff]
    intro q hq
    refine hQ q (le_trans ?_ hq)
    rw [← NNReal.coe_le_coe, NNReal.coe_natCast]
    exact (Nat.le_ceil _).trans (by exact_mod_cast hN)
  obtain ⟨N, hN⟩ := (GW2Bh.eventually_measure_le (fun N => (measurableSet_capGood hZ capv N).compl) hev hε2).exists
  obtain ⟨q, hq⟩ := hcap N
  -- the buffer
  have hev' : ∀ᵐ ξ ∂μ, ∀ᶠ b in atTop, ξ ∉ Z q b ∩ capGood Z capv N :=
    Eventually.of_forall fun ξ => by
      by_cases h : ξ ∈ capGood Z capv N
      · exact (h q hq).mono fun b hb hmem => hb hmem.1
      · exact Eventually.of_forall fun b hmem => h hmem.2
  obtain ⟨b, hb⟩ := (GW2Bh.eventually_measure_le (fun b => (hZ q b).inter (measurableSet_capGood hZ capv N)) hev'
    hε2).exists
  refine ⟨q, b, ?_⟩
  calc μ (Z q b) ≤ μ (Z q b ∩ capGood Z capv N) + μ (capGood Z capv N)ᶜ := by
        refine le_trans (measure_mono fun ξ hξ => ?_) (measure_union_le _ _)
        by_cases h : ξ ∈ capGood Z capv N
        · exact Or.inl ⟨hξ, h⟩
        · exact Or.inr h
    _ ≤ ε / 2 + ε / 2 := add_le_add hb hN
    _ = ε := ENNReal.add_halves ε

end Measure

section Kernel

variable {Ω : Type*} {𝒢 : MeasurableSpace Ω} [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω] {P : Measure Ω}
  [IsProbabilityMeasure P]

/-- **The cap and buffer selection.** If almost surely, for every `n` and angle index `i`, every cap past some value
and then every buffer past some index avoids the bad set `Z n i q b`, then there is a selection `kSel ω₀ n i m`
(a pair `Nat.pair q b`, chosen at the conditioning sample) whose bad set has conditional measure at most
`1/(m+1)`, for `P`-a.e. `ω₀` and all `n`, `i`, `m`. -/
theorem exists_kSel (h𝒢 : 𝒢 ≤ mΩ) {Z : ℕ → ℕ → ℕ → ℕ → Set Ω} (hZ : ∀ n i q b, MeasurableSet (Z n i q b))
    {capv : ℕ → ℝ≥0} (hcap : ∀ Q : ℝ≥0, ∃ q, Q ≤ capv q)
    (hgood : ∀ᵐ ξ ∂P, ∀ n i, ∃ Q : ℝ≥0, ∀ q, Q ≤ capv q → ∀ᶠ b in atTop, ξ ∉ Z n i q b) :
    ∃ kSel : Ω → ℕ → ℕ → ℕ → ℕ, ∀ᵐ ω₀ ∂P, ∀ n i m,
      condExpKernel P 𝒢 ω₀ (Z n i (Nat.unpair (kSel ω₀ n i m)).1 (Nat.unpair (kSel ω₀ n i m)).2) ≤
        ((m : ℝ≥0∞) + 1)⁻¹ := by
  classical
  set E : Ω → ℕ → ℕ → ℕ → Prop := fun ω₀ n i m =>
    ∃ k : ℕ, condExpKernel P 𝒢 ω₀ (Z n i (Nat.unpair k).1 (Nat.unpair k).2) ≤ ((m : ℝ≥0∞) + 1)⁻¹ with hEdef
  refine ⟨fun ω₀ n i m => if h : E ω₀ n i m then h.choose else 0, ?_⟩
  filter_upwards [Sec7.Aux122Disint.ae_ae_condExpKernel h𝒢 hgood] with ω₀ hω₀ n i m
  have hm : (0 : ℝ≥0∞) < ((m : ℝ≥0∞) + 1)⁻¹ := ENNReal.inv_pos.2 (by simp)
  have hgi : ∀ᵐ ξ ∂(condExpKernel P 𝒢 ω₀), ∃ Q : ℝ≥0, ∀ q, Q ≤ capv q → ∀ᶠ b in atTop, ξ ∉ Z n i q b :=
    hω₀.mono fun ξ h => h n i
  obtain ⟨q, b, hqb⟩ := exists_pair_measure_le (μ := condExpKernel P 𝒢 ω₀) (hZ n i) hcap hgi hm
  have hE : E ω₀ n i m := ⟨Nat.pair q b, by rw [Nat.unpair_pair]; exact hqb⟩
  simp only [hE, ↓reduceDIte]
  exact hE.choose_spec

end Kernel

end InteractingSLE.Theorem14.GW2Ni
