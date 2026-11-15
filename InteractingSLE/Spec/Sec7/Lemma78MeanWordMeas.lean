/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.Lemma78MeanSide
import InteractingSLE.Spec.Restart.R1GlueChart

/-!
# Measurability of Lemma 7.8's boundary word

Packet PROVE-PRIMEEND2, item 2 of the handoff (`FirstContactWordKernelStatement` asks for a datum measurable for the
retained σ-algebra). For pair data with `IsMeasGood`:

* the real base `a = baseL`, `b = baseR` is measurable (hits of the closed half-lines `(−∞, c]`, `[c, ∞)` by the two
  prefixes, `measurableSet_inter_exists_mem`);
* the boundary correspondence `ℓ` read at a measurable untouched point is measurable (limits of the mapping-out
  function along the domain, `measurable_of_tendsto_nhdsWithin`);
* `L = sup_n ℓ(a − 1/(n+1))` and `R = inf_n ℓ(b + 1/(n+1))` are measurable on the contact event;
* the word truncated to its length (`BoundaryWord.trunc`; same index, datum, jumps and mean) on the contact event,
  `PairData.wordE`, is measurable (`PairData.IsMeasGood.measurable_wordE`);
* the stopped data have the same word on the good event (`wordE_stopData_eq`), so the word of `stopData d` is
  measurable for the retained σ-algebra;
* **`exists_word_isBoxMeanIdentification`**: the mean part of `FirstContactWordKernelStatement` (a `retSigma`-
  measurable datum, sorted on the meeting branch, with Lemma 7.8's mean identification on every box) from the
  exposed-side heights `IsBoxSideLimit`.
-/

set_option autoImplicit false

noncomputable section

open Complex Set Metric Filter Topology MeasureTheory
open scoped NNReal ENNReal

open QuantumZipper (H Hbar)

namespace InteractingSLE

namespace Restart

section Meas

variable {Ω : Type*} [MeasurableSpace Ω] {d : PairData Ω}

omit [MeasurableSpace Ω] in
theorem PairData.baseL_of_notMem {ω : Ω} (hω : ω ∉ d.E) : d.baseL ω = 0 := by
  simp [PairData.baseL, PairData.realK, K_of_notMem hω]

omit [MeasurableSpace Ω] in
theorem PairData.baseR_of_notMem {ω : Ω} (hω : ω ∉ d.E) : d.baseR ω = 0 := by
  simp [PairData.baseR, PairData.realK, K_of_notMem hω]

/-- A real complex number of `K` on the contact event comes from one of the two prefixes. -/
theorem PairData.IsMeasGood.mem_K_iff (hd : d.IsMeasGood) {ω : Ω} (hE : ω ∈ d.E) {z : ℂ} :
    z ∈ d.K ω ↔ (∃ s ≤ d.s₀ ω, d.η₁ ω s = z) ∨ ∃ t ≤ d.t₀ ω, d.η₂ ω t = z := by
  have _ := hd
  rw [K_of_mem hE, prefixSet]
  simp only [mem_union, mem_image, mem_Icc, zero_le, true_and]

/-- On the contact event, `a ≤ c` iff a prefix hits the closed real half-line `(−∞, c]`. -/
theorem PairData.IsMeasGood.baseL_le_iff (hd : d.IsMeasGood) {ω : Ω} (hE : ω ∈ d.E) (c : ℝ) :
    d.baseL ω ≤ c ↔ (∃ s ≤ d.s₀ ω, d.η₁ ω s ∈ {z : ℂ | z.im = 0 ∧ z.re ≤ c}) ∨
      ∃ t ≤ d.t₀ ω, d.η₂ ω t ∈ {z : ℂ | z.im = 0 ∧ z.re ≤ c} := by
  constructor
  · intro h
    rcases (hd.mem_K_iff hE).1 (hd.baseL_mem hE) with ⟨s, hs, he⟩ | ⟨t, ht, he⟩
    · exact Or.inl ⟨s, hs, by rw [he]; simpa using h⟩
    · exact Or.inr ⟨t, ht, by rw [he]; simpa using h⟩
  · rintro (⟨s, hs, h0, hre⟩ | ⟨t, ht, h0, hre⟩)
    · refine (hd.baseL_le ?_).trans hre
      rw [ofReal_re_eq h0]
      exact (hd.mem_K_iff hE).2 (Or.inl ⟨s, hs, rfl⟩)
    · refine (hd.baseL_le ?_).trans hre
      rw [ofReal_re_eq h0]
      exact (hd.mem_K_iff hE).2 (Or.inr ⟨t, ht, rfl⟩)

/-- On the contact event, `c ≤ b` iff a prefix hits the closed real half-line `[c, ∞)`. -/
theorem PairData.IsMeasGood.le_baseR_iff (hd : d.IsMeasGood) {ω : Ω} (hE : ω ∈ d.E) (c : ℝ) :
    c ≤ d.baseR ω ↔ (∃ s ≤ d.s₀ ω, d.η₁ ω s ∈ {z : ℂ | z.im = 0 ∧ c ≤ z.re}) ∨
      ∃ t ≤ d.t₀ ω, d.η₂ ω t ∈ {z : ℂ | z.im = 0 ∧ c ≤ z.re} := by
  constructor
  · intro h
    rcases (hd.mem_K_iff hE).1 (hd.baseR_mem hE) with ⟨s, hs, he⟩ | ⟨t, ht, he⟩
    · exact Or.inl ⟨s, hs, by rw [he]; simpa using h⟩
    · exact Or.inr ⟨t, ht, by rw [he]; simpa using h⟩
  · rintro (⟨s, hs, h0, hre⟩ | ⟨t, ht, h0, hre⟩)
    · refine hre.trans (hd.le_baseR ?_)
      rw [ofReal_re_eq h0]
      exact (hd.mem_K_iff hE).2 (Or.inl ⟨s, hs, rfl⟩)
    · refine hre.trans (hd.le_baseR ?_)
      rw [ofReal_re_eq h0]
      exact (hd.mem_K_iff hE).2 (Or.inr ⟨t, ht, rfl⟩)

theorem PairData.IsMeasGood.measurable_baseL (hd : d.IsMeasGood) : Measurable d.baseL := by
  refine measurable_of_Iic fun c => ?_
  set Q : Set ℂ := {z : ℂ | z.im = 0 ∧ z.re ≤ c} with hQdef
  have hQ : IsClosed Q :=
    (isClosed_eq Complex.continuous_im continuous_const).inter (isClosed_le Complex.continuous_re continuous_const)
  have hQne : Q.Nonempty := ⟨(c : ℂ), by simp [hQdef]⟩
  have heq : d.baseL ⁻¹' Iic c = (d.E ∩ {ω | ∃ s ≤ d.s₀ ω, d.η₁ ω s ∈ Q}) ∪
      (d.E ∩ {ω | ∃ t ≤ d.t₀ ω, d.η₂ ω t ∈ Q}) ∪ (d.Eᶜ ∩ {_ω | (0 : ℝ) ≤ c}) := by
    ext ω
    by_cases hω : ω ∈ d.E
    · simp only [mem_preimage, mem_Iic, hd.baseL_le_iff hω c, mem_union, mem_inter_iff, hω, true_and,
        mem_ofPred_eq, mem_compl_iff, not_true_eq_false, false_and, or_false, hQdef]
    · simp only [mem_preimage, mem_Iic, PairData.baseL_of_notMem hω, mem_union, mem_inter_iff, hω, false_and,
        mem_compl_iff, not_false_eq_true, true_and, mem_ofPred_eq, false_or]
  rw [heq]
  exact ((measurableSet_inter_exists_mem hd.measurableSet_E hd.meas₁ hd.measurable_s₀
    (fun ω hω => hd.continuousOn₁ hω) hQ hQne).union (measurableSet_inter_exists_mem hd.measurableSet_E hd.meas₂
      hd.measurable_t₀ (fun ω hω => hd.continuousOn₂ hω) hQ hQne)).union
    (hd.measurableSet_E.compl.inter (MeasurableSet.const _))

theorem PairData.IsMeasGood.measurable_baseR (hd : d.IsMeasGood) : Measurable d.baseR := by
  refine measurable_of_Ici fun c => ?_
  set Q : Set ℂ := {z : ℂ | z.im = 0 ∧ c ≤ z.re} with hQdef
  have hQ : IsClosed Q :=
    (isClosed_eq Complex.continuous_im continuous_const).inter (isClosed_le continuous_const Complex.continuous_re)
  have hQne : Q.Nonempty := ⟨(c : ℂ), by simp [hQdef]⟩
  have heq : d.baseR ⁻¹' Ici c = (d.E ∩ {ω | ∃ s ≤ d.s₀ ω, d.η₁ ω s ∈ Q}) ∪
      (d.E ∩ {ω | ∃ t ≤ d.t₀ ω, d.η₂ ω t ∈ Q}) ∪ (d.Eᶜ ∩ {_ω | c ≤ (0 : ℝ)}) := by
    ext ω
    by_cases hω : ω ∈ d.E
    · simp only [mem_preimage, mem_Ici, hd.le_baseR_iff hω c, mem_union, mem_inter_iff, hω, true_and,
        mem_ofPred_eq, mem_compl_iff, not_true_eq_false, false_and, or_false, hQdef]
    · simp only [mem_preimage, mem_Ici, PairData.baseR_of_notMem hω, mem_union, mem_inter_iff, hω, false_and,
        mem_compl_iff, not_false_eq_true, true_and, mem_ofPred_eq, false_or]
  rw [heq]
  exact ((measurableSet_inter_exists_mem hd.measurableSet_E hd.meas₁ hd.measurable_s₀
    (fun ω hω => hd.continuousOn₁ hω) hQ hQne).union (measurableSet_inter_exists_mem hd.measurableSet_E hd.meas₂
      hd.measurable_t₀ (fun ω hω => hd.continuousOn₂ hω) hQ hQne)).union
    (hd.measurableSet_E.compl.inter (MeasurableSet.const _))

/-- The untouched event of a random real point: the contact event, and the point is off the base. -/
def PairData.offBase (d : PairData Ω) (x : Ω → ℝ) : Set Ω :=
  d.E ∩ ({ω | x ω < d.baseL ω} ∪ {ω | d.baseR ω < x ω})

theorem PairData.IsMeasGood.measurableSet_offBase (hd : d.IsMeasGood) {x : Ω → ℝ} (hx : Measurable x) :
    MeasurableSet (d.offBase x) :=
  hd.measurableSet_E.inter ((measurableSet_lt hx hd.measurable_baseL).union (measurableSet_lt hd.measurable_baseR hx))

/-- The boundary correspondence on the untouched event. -/
theorem PairData.IsMeasGood.bdry_spec_offBase (hd : d.IsMeasGood) {x : Ω → ℝ} {ω : Ω} (hω : ω ∈ d.offBase x) :
    Tendsto (d.fwd ω) (𝓝[d.D ω] (x ω : ℂ)) (𝓝 (d.bdry ω (x ω) : ℂ)) ∧ (x ω : ℂ) ∈ closure (d.D ω) := by
  rcases hω.2 with h | h
  · obtain ⟨ρ, hρ, -, hF⟩ := hd.exists_ball_of_lt_baseL h
    exact ⟨(hd.bdry_spec_lt hω.1 h).1, PairData.mem_closure_D_of_disjoint hρ hF⟩
  · obtain ⟨ρ, hρ, -, hF⟩ := hd.exists_ball_of_baseR_lt h
    exact ⟨(hd.bdry_spec_gt hω.1 h).1, PairData.mem_closure_D_of_disjoint hρ hF⟩

/-- **The boundary correspondence at a measurable untouched point is measurable.** -/
theorem PairData.IsMeasGood.measurable_indicator_bdry (hd : d.IsMeasGood) {x : Ω → ℝ} (hx : Measurable x) :
    Measurable ((d.offBase x).indicator fun ω => d.bdry ω (x ω)) := by
  classical
  set C := d.offBase x with hCdef
  have hC : MeasurableSet C := hd.measurableSet_offBase hx
  set q : Ω → ℂ := fun ω => if ω ∈ C then (x ω : ℂ) else d.p ω with hqdef
  have hq : Measurable q := Measurable.ite hC (Complex.measurable_ofReal.comp hx) hd.measurable_p
  have hqD : ∀ ω, q ω ∈ closure (d.D ω) := fun ω => by
    by_cases hω : ω ∈ C
    · simp only [hqdef, hω, ↓reduceIte]; exact (hd.bdry_spec_offBase hω).2
    · simp only [hqdef, hω, ↓reduceIte]; exact hd.p_mem_closure ω
  have hfg : ∀ ω, d.g ω = fun z => d.fwd ω z + d.shift ω := fun ω => by
    funext z; simp [PairData.fwd]
  have hex : ∀ ω, ∃ y, Tendsto (d.g ω) (𝓝[d.D ω] (q ω)) (𝓝 y) := fun ω => by
    by_cases hω : ω ∈ C
    · simp only [hqdef, hω, ↓reduceIte]
      rw [hfg ω]
      exact ⟨_, (hd.bdry_spec_offBase hω).1.add_const _⟩
    · simp only [hqdef, hω, ↓reduceIte]
      exact ⟨_, hd.tendsto_shift ω⟩
  set w : Ω → ℂ := fun ω => limUnder (𝓝[d.D ω] (q ω)) (d.g ω) with hwdef
  have hw : Measurable w := measurable_of_tendsto_nhdsWithin hd.isOpen_D hd.measurableSet_mem_D
    hd.measurable_indicator_g hq hqD fun ω => tendsto_nhds_limUnder (hex ω)
  have heq : C.indicator (fun ω => d.bdry ω (x ω)) = C.indicator fun ω => (w ω - d.shift ω).re := by
    refine Set.indicator_congr fun ω hω => ?_
    obtain ⟨hT, hcl⟩ := hd.bdry_spec_offBase hω
    have hNe : (𝓝[d.D ω] (x ω : ℂ)).NeBot := mem_closure_iff_nhdsWithin_neBot.1 hcl
    have hT' : Tendsto (d.g ω) (𝓝[d.D ω] (x ω : ℂ)) (𝓝 (w ω)) := by
      have hqω : q ω = (x ω : ℂ) := by simp only [hqdef, hω, ↓reduceIte]
      show Tendsto (d.g ω) (𝓝[d.D ω] (x ω : ℂ)) (𝓝 (limUnder (𝓝[d.D ω] (q ω)) (d.g ω)))
      rw [hqω]
      exact tendsto_nhds_limUnder ⟨_, by rw [hfg ω]; exact hT.add_const _⟩
    rw [hfg ω] at hT'
    have := tendsto_nhds_unique (hT.add_const (d.shift ω)) hT'
    rw [← this]
    simp
  rw [heq]
  exact (Complex.measurable_re.comp (hw.sub hd.measurable_shift)).indicator hC

/-- `L = sup_n ℓ(a − 1/(n+1))` on the contact event. -/
theorem PairData.IsMeasGood.wordL_eq_iSup (hd : d.IsMeasGood) {ω : Ω} (hE : ω ∈ d.E) :
    d.wordL ω = ⨆ n : ℕ, d.bdry ω (d.baseL ω - 1 / ((n : ℝ) + 1)) := by
  have hlt : ∀ n : ℕ, d.baseL ω - 1 / ((n : ℝ) + 1) < d.baseL ω := fun n => by
    have : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
    linarith
  have hbdd : BddAbove (range fun n : ℕ => d.bdry ω (d.baseL ω - 1 / ((n : ℝ) + 1))) := by
    refine ⟨d.wordL ω, ?_⟩
    rintro _ ⟨n, rfl⟩
    exact le_csSup (hd.bddAbove_bdry_Iio hE) ⟨_, hlt n, rfl⟩
  refine le_antisymm (csSup_le ⟨_, ⟨_, hlt 0, rfl⟩⟩ ?_) (ciSup_le fun n =>
    le_csSup (hd.bddAbove_bdry_Iio hE) ⟨_, hlt n, rfl⟩)
  rintro _ ⟨x, hx, rfl⟩
  have hx' : x < d.baseL ω := hx
  obtain ⟨n, hn⟩ := exists_nat_one_div_lt (sub_pos.2 hx')
  have hxn : x < d.baseL ω - 1 / ((n : ℝ) + 1) := by linarith
  exact ((hd.strictMonoOn_bdry_Iio hE) hx' (hlt n) hxn).le.trans (le_ciSup hbdd n)

/-- `R = inf_n ℓ(b + 1/(n+1))` on the contact event. -/
theorem PairData.IsMeasGood.wordR_eq_iInf (hd : d.IsMeasGood) {ω : Ω} (hE : ω ∈ d.E) :
    d.wordR ω = ⨅ n : ℕ, d.bdry ω (d.baseR ω + 1 / ((n : ℝ) + 1)) := by
  have hgt : ∀ n : ℕ, d.baseR ω < d.baseR ω + 1 / ((n : ℝ) + 1) := fun n => by
    have : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
    linarith
  have hbdd : BddBelow (range fun n : ℕ => d.bdry ω (d.baseR ω + 1 / ((n : ℝ) + 1))) := by
    refine ⟨d.wordR ω, ?_⟩
    rintro _ ⟨n, rfl⟩
    exact csInf_le (hd.bddBelow_bdry_Ioi hE) ⟨_, hgt n, rfl⟩
  refine le_antisymm (le_ciInf fun n => csInf_le (hd.bddBelow_bdry_Ioi hE) ⟨_, hgt n, rfl⟩)
    (le_csInf ⟨_, ⟨_, hgt 0, rfl⟩⟩ ?_)
  rintro _ ⟨x, hx, rfl⟩
  have hx' : d.baseR ω < x := hx
  obtain ⟨n, hn⟩ := exists_nat_one_div_lt (sub_pos.2 hx')
  have hxn : d.baseR ω + 1 / ((n : ℝ) + 1) < x := by linarith
  exact (ciInf_le hbdd n).trans ((hd.strictMonoOn_bdry_Ioi hE) (hgt n) hx' hxn).le

theorem PairData.IsMeasGood.measurable_indicator_wordL (hd : d.IsMeasGood) : Measurable (d.E.indicator d.wordL) := by
  set x : ℕ → Ω → ℝ := fun n ω => d.baseL ω - 1 / ((n : ℝ) + 1) with hx
  have hxm : ∀ n, Measurable (x n) := fun n => hd.measurable_baseL.sub_const _
  have heq : d.E.indicator d.wordL =
      d.E.indicator fun ω => ⨆ n : ℕ, (d.offBase (x n)).indicator (fun ω => d.bdry ω (x n ω)) ω := by
    refine Set.indicator_congr fun ω hω => ?_
    rw [hd.wordL_eq_iSup hω]
    refine iSup_congr fun n => ?_
    have hmem : ω ∈ d.offBase (x n) := ⟨hω, Or.inl (by
      show d.baseL ω - 1 / ((n : ℝ) + 1) < d.baseL ω
      have : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
      linarith)⟩
    rw [indicator_of_mem hmem]
  rw [heq]
  exact (Measurable.iSup fun n => hd.measurable_indicator_bdry (hxm n)).indicator hd.measurableSet_E

theorem PairData.IsMeasGood.measurable_indicator_wordR (hd : d.IsMeasGood) : Measurable (d.E.indicator d.wordR) := by
  set x : ℕ → Ω → ℝ := fun n ω => d.baseR ω + 1 / ((n : ℝ) + 1) with hx
  have hxm : ∀ n, Measurable (x n) := fun n => hd.measurable_baseR.add_const _
  have heq : d.E.indicator d.wordR =
      d.E.indicator fun ω => ⨅ n : ℕ, (d.offBase (x n)).indicator (fun ω => d.bdry ω (x n ω)) ω := by
    refine Set.indicator_congr fun ω hω => ?_
    rw [hd.wordR_eq_iInf hω]
    refine iInf_congr fun n => ?_
    have hmem : ω ∈ d.offBase (x n) := ⟨hω, Or.inr (by
      show d.baseR ω < d.baseR ω + 1 / ((n : ℝ) + 1)
      have : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
      linarith)⟩
    rw [indicator_of_mem hmem]
  rw [heq]
  exact (Measurable.iInf fun n => hd.measurable_indicator_bdry (hxm n)).indicator hd.measurableSet_E

theorem PairData.IsMeasGood.measurable_wordK (hd : d.IsMeasGood) (c₀ : BoundaryWord) : Measurable (d.wordK c₀) := by
  classical
  have e : d.wordK c₀ = fun ω => ∑ i ∈ Finset.range c₀.1, if c₀.2.1 i < d.baseL ω then 1 else 0 := by
    funext ω; unfold PairData.wordK; rw [Finset.card_filter]
  rw [e]
  exact Finset.measurable_sum _ fun i _ =>
    Measurable.ite (measurableSet_lt measurable_const hd.measurable_baseL) measurable_const measurable_const

theorem PairData.IsMeasGood.measurable_wordLe (hd : d.IsMeasGood) (c₀ : BoundaryWord) :
    Measurable (d.wordLe c₀) := by
  classical
  have e : d.wordLe c₀ = fun ω => ∑ i ∈ Finset.range c₀.1, if c₀.2.1 i ≤ d.baseR ω then 1 else 0 := by
    funext ω; unfold PairData.wordLe; rw [Finset.card_filter]
  rw [e]
  exact Finset.measurable_sum _ fun i _ =>
    Measurable.ite (measurableSet_le measurable_const hd.measurable_baseR) measurable_const measurable_const

end Meas

/-! ### The truncated word -/

namespace BoundaryWord

/-- The word with its positions beyond the length replaced by `0` (they are not part of its meaning). -/
def trunc (c : BoundaryWord) : BoundaryWord := (c.1, fun i => if i < c.1 then c.2.1 i else 0, c.2.2)

theorem trunc_index (c : BoundaryWord) (y : ℝ) : c.trunc.index y = c.index y := by
  unfold index trunc
  congr 1
  refine Finset.filter_congr fun i hi => ?_
  have hi' : i < c.1 := Finset.mem_range.1 hi
  simp only [hi', ↓reduceIte]

theorem trunc_fn (c : BoundaryWord) (y : ℝ) : c.trunc.fn y = c.fn y := by
  unfold fn
  rw [trunc_index]
  rfl

theorem trunc_jumps (c : BoundaryWord) : c.trunc.jumps = c.jumps := by
  unfold jumps trunc
  refine Finset.image_congr fun i hi => ?_
  have hi' : i < c.1 := Finset.mem_range.1 hi
  simp only [hi', ↓reduceIte]

theorem trunc_mean (c : BoundaryWord) : c.trunc.mean = c.mean := by
  funext z
  unfold mean trunc
  simp only
  congr 1
  refine Finset.sum_congr rfl fun j hj => ?_
  have hj' : j < c.1 := Finset.mem_range.1 hj
  simp only [hj', ↓reduceIte]

theorem IsSorted.trunc {c : BoundaryWord} (hc : c.IsSorted) : c.trunc.IsSorted := by
  intro i j hij hj
  have hj' : j < c.1 := hj
  have hi' : i < c.1 := lt_of_le_of_lt hij hj'
  simp only [BoundaryWord.trunc, hi', hj', ↓reduceIte]
  exact hc i j hij hj'

end BoundaryWord

section MeasWord

variable {Ω : Type*} [MeasurableSpace Ω] {d : PairData Ω}

open scoped Classical in
/-- **Lemma 7.8's word on the contact event, truncated** (the empty word off it). -/
def PairData.wordE (d : PairData Ω) (c₀ : BoundaryWord) (hL hR : ℝ) (ω : Ω) : BoundaryWord :=
  if ω ∈ d.E then (d.word c₀ hL hR ω).trunc else (0, fun _ => 0, fun _ => 0)

omit [MeasurableSpace Ω] in
theorem PairData.wordE_of_mem {c₀ : BoundaryWord} {hL hR : ℝ} {ω : Ω} (hω : ω ∈ d.E) :
    d.wordE c₀ hL hR ω = (d.word c₀ hL hR ω).trunc := by
  simp [PairData.wordE, hω]

omit [MeasurableSpace Ω] in
theorem PairData.wordE_of_notMem {c₀ : BoundaryWord} {hL hR : ℝ} {ω : Ω} (hω : ω ∉ d.E) :
    d.wordE c₀ hL hR ω = (0, fun _ => 0, fun _ => 0) := by
  simp [PairData.wordE, hω]

open scoped Classical in
/-- The position of index `i` for given counts `a = k`, `b = l`, with measurable readings of `ℓ`, `L`, `R`. -/
def PairData.posAux (d : PairData Ω) (c₀ : BoundaryWord) (a b i : ℕ) (ω : Ω) : ℝ :=
  if i < a + 3 + (c₀.1 - b) then
    (if i < a then (d.offBase fun _ => c₀.2.1 i).indicator (fun ω => d.bdry ω (c₀.2.1 i)) ω
      else if i = a then d.E.indicator d.wordL ω else if i = a + 1 then 0
      else if i = a + 2 then d.E.indicator d.wordR ω
      else (d.offBase fun _ => c₀.2.1 (i - (a + 3) + b)).indicator
        (fun ω => d.bdry ω (c₀.2.1 (i - (a + 3) + b))) ω)
  else 0

open scoped Classical in
/-- The height of index `i` for given counts `a = k`, `b = l`. -/
def PairData.htAux (c₀ : BoundaryWord) (hL hR : ℝ) (a b i : ℕ) : ℝ :=
  if i ≤ a then c₀.2.2 i else if i = a + 1 then hL else if i = a + 2 then hR else c₀.2.2 (i - (a + 3) + b)

theorem PairData.IsMeasGood.measurable_posAux (hd : d.IsMeasGood) (c₀ : BoundaryWord) (a b i : ℕ) :
    Measurable (d.posAux c₀ a b i) := by
  unfold PairData.posAux
  split_ifs
  · exact hd.measurable_indicator_bdry measurable_const
  · exact hd.measurable_indicator_wordL
  · exact measurable_const
  · exact hd.measurable_indicator_wordR
  · exact hd.measurable_indicator_bdry measurable_const
  · exact measurable_const

/-- **The truncated word is measurable.** -/
theorem PairData.IsMeasGood.measurable_wordE (hd : d.IsMeasGood) {c₀ : BoundaryWord}
    (hc₀ : StrictMonoOn c₀.2.1 (Iio c₀.1)) (hL hR : ℝ) : Measurable (d.wordE c₀ hL hR) := by
  classical
  have hk := hd.measurable_wordK c₀
  have hl := hd.measurable_wordLe c₀
  have hkl : Measurable fun ω => (d.wordK c₀ ω, d.wordLe c₀ ω) := hk.prodMk hl
  -- the length
  have h1 : Measurable fun ω => (d.wordE c₀ hL hR ω).1 := by
    have e : (fun ω => (d.wordE c₀ hL hR ω).1) =
        fun ω => if ω ∈ d.E then d.wordK c₀ ω + 3 + (c₀.1 - d.wordLe c₀ ω) else 0 := by
      funext ω
      by_cases hω : ω ∈ d.E
      · rw [PairData.wordE_of_mem hω]; simp only [hω, ↓reduceIte]; rfl
      · rw [PairData.wordE_of_notMem hω]; simp only [hω, ↓reduceIte]
    rw [e]
    exact Measurable.ite hd.measurableSet_E
      ((measurable_of_countable fun p : ℕ × ℕ => p.1 + 3 + (c₀.1 - p.2)).comp hkl) measurable_const
  -- the positions
  have h2 : Measurable fun ω => (d.wordE c₀ hL hR ω).2.1 := by
    refine measurable_pi_iff.2 fun i => ?_
    have hF : Measurable fun p : Ω × (ℕ × ℕ) => d.posAux c₀ p.2.1 p.2.2 i p.1 :=
      measurable_from_prod_countable_left fun ab => hd.measurable_posAux c₀ ab.1 ab.2 i
    have e : (fun ω => (d.wordE c₀ hL hR ω).2.1 i) =
        d.E.indicator fun ω => d.posAux c₀ (d.wordK c₀ ω) (d.wordLe c₀ ω) i ω := by
      funext ω
      by_cases hω : ω ∈ d.E
      · rw [PairData.wordE_of_mem hω, indicator_of_mem hω]
        simp only [BoundaryWord.trunc, PairData.word_fst, PairData.posAux]
        by_cases hin : i < d.wordK c₀ ω + 3 + (c₀.1 - d.wordLe c₀ ω)
        · simp only [hin, ↓reduceIte]
          have hkN : d.wordK c₀ ω ≤ c₀.1 := card_filter_le_range _
          have hlN : d.wordLe c₀ ω ≤ c₀.1 := card_filter_le_range _
          rcases Nat.lt_or_ge i (d.wordK c₀ ω) with hik | hik
          · have hiN : i < c₀.1 := lt_of_lt_of_le hik hkN
            have hmem : ω ∈ d.offBase fun _ => c₀.2.1 i :=
              ⟨hω, Or.inl ((PairData.lt_wordK_iff hc₀ hiN).1 hik)⟩
            rw [PairData.word_pos_of_lt hL hR hik, indicator_of_mem hmem]
            simp only [hik, ↓reduceIte]
          rcases hik.lt_or_eq with hik | hik
          · have hn1 : ¬ i < d.wordK c₀ ω := by omega
            have hn2 : i ≠ d.wordK c₀ ω := by omega
            rcases Nat.lt_or_ge i (d.wordK c₀ ω + 3) with h3 | h3
            · obtain rfl | rfl : i = d.wordK c₀ ω + 1 ∨ i = d.wordK c₀ ω + 2 := by omega
              · rw [PairData.word_pos_k1]
                simp only [hn1, hn2, ↓reduceIte]
              · have hn3 : d.wordK c₀ ω + 2 ≠ d.wordK c₀ ω + 1 := by omega
                rw [PairData.word_pos_k2]
                simp only [hn1, hn2, hn3, ↓reduceIte, indicator_of_mem hω]
            · have hmN : i - (d.wordK c₀ ω + 3) + d.wordLe c₀ ω < c₀.1 := by omega
              have hgt : d.baseR ω < c₀.2.1 (i - (d.wordK c₀ ω + 3) + d.wordLe c₀ ω) :=
                not_le.1 fun h => by have := (PairData.lt_wordLe_iff hc₀ hmN).2 h; omega
              have hn3 : i ≠ d.wordK c₀ ω + 1 := by omega
              have hn4 : i ≠ d.wordK c₀ ω + 2 := by omega
              rw [PairData.word_pos_of_ge hL hR h3]
              simp only [hn1, hn2, hn3, hn4, ↓reduceIte]
              rw [indicator_of_mem (show ω ∈ d.offBase fun _ =>
                  c₀.2.1 (i - (d.wordK c₀ ω + 3) + d.wordLe c₀ ω) from ⟨hω, Or.inr hgt⟩)]
          · subst hik
            rw [PairData.word_pos_k]
            simp only [lt_irrefl, ↓reduceIte, indicator_of_mem hω]
        · simp only [hin, ↓reduceIte]
      · rw [PairData.wordE_of_notMem hω, indicator_of_notMem hω]
    rw [e]
    exact (hF.comp (measurable_id.prodMk hkl)).indicator hd.measurableSet_E
  -- the heights
  have h3 : Measurable fun ω => (d.wordE c₀ hL hR ω).2.2 := by
    refine measurable_pi_iff.2 fun i => ?_
    have e : (fun ω => (d.wordE c₀ hL hR ω).2.2 i) =
        d.E.indicator fun ω => PairData.htAux c₀ hL hR (d.wordK c₀ ω) (d.wordLe c₀ ω) i := by
      funext ω
      by_cases hω : ω ∈ d.E
      · rw [PairData.wordE_of_mem hω, indicator_of_mem hω]
        simp only [BoundaryWord.trunc, PairData.htAux]
        rcases Nat.lt_or_ge (d.wordK c₀ ω) i with hik | hik
        · have hn1 : ¬ i ≤ d.wordK c₀ ω := by omega
          rcases Nat.lt_or_ge i (d.wordK c₀ ω + 3) with h3 | h3
          · obtain rfl | rfl : i = d.wordK c₀ ω + 1 ∨ i = d.wordK c₀ ω + 2 := by omega
            · rw [PairData.word_ht_k1]
              simp only [hn1, ↓reduceIte]
            · have hn3 : d.wordK c₀ ω + 2 ≠ d.wordK c₀ ω + 1 := by omega
              rw [PairData.word_ht_k2]
              simp only [hn1, hn3, ↓reduceIte]
          · have hn3 : i ≠ d.wordK c₀ ω + 1 := by omega
            have hn4 : i ≠ d.wordK c₀ ω + 2 := by omega
            rw [PairData.word_ht_of_ge hL hR h3]
            simp only [hn1, hn3, hn4, ↓reduceIte]
        · rw [PairData.word_ht_of_le hL hR hik]
          simp only [hik, ↓reduceIte]
      · rw [PairData.wordE_of_notMem hω, indicator_of_notMem hω]
    rw [e]
    exact ((measurable_of_countable fun p : ℕ × ℕ => PairData.htAux c₀ hL hR p.1 p.2 i).comp hkl).indicator
      hd.measurableSet_E
  exact h1.prodMk (h2.prodMk h3)

end MeasWord

end Restart

end InteractingSLE

namespace InteractingSLE

namespace Restart

/-! ### The word of the stopped data: measurable for the retained σ-algebra -/

section Stopped

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {d : PairData Ω}

/-- The stopped data have the same first-contact compact on the good event. -/
theorem K_stopData_eq (hd : d.IsMeasGood) {ω : Ω} (hω : ω ∈ d.G) : (stopData d).K ω = d.K ω := by
  by_cases hE : ω ∈ d.E
  · have hE' : ω ∈ (stopData d).E := (stopData_E_iff hd hω).2 hE
    obtain ⟨es, et⟩ := stopData_s₀_t₀ hd hE
    have ha₁ := fun (s : ℝ≥0) (hs : (s : ℝ≥0∞) ≤ (stopData d).ζ₁ ω) => stopData_η₁_eq hd hω hs
    have ha₂ := fun (t : ℝ≥0) (ht : (t : ℝ≥0∞) ≤ (stopData d).ζ₂ ω) => stopData_η₂_eq hd hω ht
    rw [PairData.K_of_mem hE', PairData.K_of_mem hE, es, et,
      prefixSet_congr ha₁ ha₂ (stopData_ζ₁_of_mem hd hE).ge (stopData_ζ₂_of_mem hd hE).ge]
  · have hE' : ω ∉ (stopData d).E := fun h => hE ((stopData_E_iff hd hω).1 h)
    rw [PairData.K_of_notMem hE', PairData.K_of_notMem hE]

/-- **The stopped data have the same word on the good event.** -/
theorem wordE_stopData_eq (hd : d.IsMeasGood) {ω : Ω} (hω : ω ∈ d.G) (c₀ : BoundaryWord) (hL hR : ℝ) :
    (stopData d).wordE c₀ hL hR ω = d.wordE c₀ hL hR ω := by
  by_cases hE : ω ∈ d.E
  · have hE' : ω ∈ (stopData d).E := (stopData_E_iff hd hω).2 hE
    have hK := K_stopData_eq hd hω
    have hD := D_stopData_eq hd hω
    have hch := chart_stopData_eq hd hω
    rw [PairData.chart_of_mem hE', PairData.chart_of_mem hE] at hch
    have hfwd : (stopData d).fwd ω = d.fwd ω := congrArg Prod.fst hch
    rw [PairData.wordE_of_mem hE', PairData.wordE_of_mem hE]
    have hrealK : (stopData d).realK ω = d.realK ω := by simp only [PairData.realK, hK]
    have hbL : (stopData d).baseL ω = d.baseL ω := by simp only [PairData.baseL, hrealK]
    have hbR : (stopData d).baseR ω = d.baseR ω := by simp only [PairData.baseR, hrealK]
    have hbdry : (stopData d).bdry ω = d.bdry ω := by
      funext x; simp only [PairData.bdry, hD, hfwd]
    have hwL : (stopData d).wordL ω = d.wordL ω := by simp only [PairData.wordL, hbdry, hbL]
    have hwR : (stopData d).wordR ω = d.wordR ω := by simp only [PairData.wordR, hbdry, hbR]
    have hk : (stopData d).wordK c₀ ω = d.wordK c₀ ω := by simp only [PairData.wordK, hbL]
    have hl : (stopData d).wordLe c₀ ω = d.wordLe c₀ ω := by simp only [PairData.wordLe, hbR]
    simp only [PairData.word, hk, hl, hbdry, hwL, hwR]
  · have hE' : ω ∉ (stopData d).E := fun h => hE ((stopData_E_iff hd hω).1 h)
    rw [PairData.wordE_of_notMem hE', PairData.wordE_of_notMem hE]

end Stopped

section Main

universe u

variable {κ : ℝ} {b : ℝ → ℝ} {jumps : Finset ℝ} {x₁ x₂ θ₁ θ₂ : ℝ} {Ω : Type u} [mΩ : MeasurableSpace Ω]
  {P : Measure Ω} [IsProbabilityMeasure P] {h : Ω → LQGMetric.DistOn upperHalfPlaneOpens} {η₁ η₂ : Ω → ℝ≥0 → ℂ}
  {ζ₁ ζ₂ : Ω → ℝ≥0∞}

/-- **The mean part of `FirstContactWordKernelStatement` from the exposed-side heights**: in its setting, given a
strictly sorted word `c₀` representing the original data and the exposed-side heights `IsBoxSideLimit` (for the side
heights `hL`, `hR`), there is a datum `β` (the explicit word of the stopped data, `wordE`), measurable for the retained
σ-algebra `retSigma d P`, sorted on the meeting branch, satisfying Lemma 7.8's mean identification on every box. -/
theorem exists_word_isBoxMeanIdentification (hL75 : Theorem15.Lemma75Statement.{u})
    (hL77 : Supp10.Lemma77Statement.{u}) (hA56 : RetainedRangeEntranceStatement.{u}) (hκ : 0 < κ) (hκ4 : κ < 4)
    (hb : IsPiecewiseConstantBoundaryData b jumps) (hx : x₂ < x₁) (hθ : θ₁ < θ₂ + Real.pi)
    (hh : IsGFFWithBoundaryData P h b jumps) (hη₁ : IsFlowLine κ b jumps x₁ θ₁ P h η₁ ζ₁)
    (hη₂ : IsFlowLine κ b jumps x₂ θ₂ P h η₂ ζ₂) {d : PairData Ω} (hd : d.IsMeasGood) (hζ₁ : d.ζ₁ = ζ₁)
    (hζ₂ : d.ζ₂ = ζ₂)
    (hae : ∀ᵐ ω ∂P, ω ∈ d.G ∧ (∀ s : ℝ≥0, (s : ℝ≥0∞) ≤ ζ₁ ω → d.η₁ ω s = η₁ ω s) ∧
      ∀ t : ℝ≥0, (t : ℝ≥0∞) ≤ ζ₂ ω → d.η₂ ω t = η₂ ω t)
    {u₀ : ℂ → ℝ} (hu₀ : IsBoundedHarmonicExtension b jumps u₀) {c₀ : BoundaryWord}
    (hc₀ : StrictMonoOn c₀.2.1 (Iio c₀.1)) (hc₀J : c₀.jumps = jumps) (hc₀b : ∀ y ∉ jumps, c₀.fn y = b y)
    {hL hR : ℝ} (hside : IsBoxSideLimit κ P h η₁ η₂ ζ₁ ζ₂ u₀ d hL hR) :
    ∃ β : Ω → BoundaryWord, Measurable[retSigma d P] β ∧ (∀ᵐ ω ∂P, ω ∈ meetSet d → (β ω).IsSorted) ∧
      IsBoxMeanIdentification κ P h η₁ η₂ ζ₁ ζ₂ u₀ hd β := by
  have hG : ∀ᵐ ω ∂P, ω ∈ d.G := hae.mono fun ω h => h.1
  have hdS := hd.isMeasGood_stopData hG
  refine ⟨(stopData d).wordE c₀ hL hR, @PairData.IsMeasGood.measurable_wordE Ω (retSigma d P) (stopData d) hdS c₀
    hc₀ hL hR, ?_, ?_⟩
  · filter_upwards [hG] with ω hωG hω
    obtain ⟨m, hm⟩ := mem_iUnion.1 hω
    have hE : ω ∈ d.E := (mem_meetBox_iff.1 hm).1
    rw [wordE_stopData_eq hd hωG, PairData.wordE_of_mem hE]
    exact (hd.word_isSorted hE hc₀ hL hR).trunc
  · intro m ηc₁ ηc₂ g hc₁ hc₂ hm₁ hm₂ hag₁ hag₂ hg
    filter_upwards [isBoxMeanIdentification_word hL75 hL77 hA56 hκ hκ4 hb hx hθ hh hη₁ hη₂ hd hζ₁ hζ₂ hae hu₀ hc₀
      hc₀J hc₀b hside m ηc₁ ηc₂ g hc₁ hc₂ hm₁ hm₂ hag₁ hag₂ hg, hG] with ω hω hωG hbox φ
    have hE : ω ∈ d.E := (mem_meetBox_iff.1 hbox).1
    rw [hω hbox φ, wordE_stopData_eq hd hωG, PairData.wordE_of_mem hE, BoundaryWord.trunc_mean]

end Main

end Restart

end InteractingSLE

namespace InteractingSLE

namespace Restart

namespace BoundaryWord

/-- **A strictly sorted word representing piecewise-constant data** (the original word `c₀` of Lemma 7.8's word):
`BoundaryWord.exists_fn_eq` (`Spec/Restart/Datum.lean`) with the strict monotonicity of its positions, which its
construction (`orderEmbOfFin`) provides but its statement does not export. The proof is that of `exists_fn_eq`. -/
theorem exists_fn_eq_strictMonoOn {b : ℝ → ℝ} {J : Finset ℝ} (hb : IsPiecewiseConstantBoundaryData b J) :
    ∃ c : BoundaryWord, StrictMonoOn c.2.1 (Iio c.1) ∧ c.jumps = J ∧ ∀ y ∉ J, c.fn y = b y := by
  set n := J.card with hn
  set e := J.orderEmbOfFin rfl with he
  let p : ℕ → ℝ := fun i => if h : i < n then e ⟨i, h⟩ else 0
  have hp : ∀ i (hi : i < n), p i = e ⟨i, hi⟩ := fun i hi => by simp only [p, hi, ↓reduceDIte]
  have hpJ : ∀ i < n, p i ∈ J := fun i hi => by rw [hp i hi]; exact J.orderEmbOfFin_mem rfl _
  have hJp : ∀ z ∈ J, ∃ i < n, p i = z := by
    intro z hz
    obtain ⟨⟨i, hi⟩, rfl⟩ : z ∈ Set.range e := by rw [he, Finset.range_orderEmbOfFin]; exact hz
    exact ⟨i, hi, hp i hi⟩
  have hmono : StrictMonoOn p (Iio n) := by
    intro i hi j hj hij
    rw [hp i hi, hp j hj]
    exact e.strictMono (Fin.mk_lt_mk.2 hij)
  let s : ℕ → ℝ := fun k =>
    if k = 0 then p 0 - 1 else if k < n then (p (k - 1) + p k) / 2 else p (n - 1) + 1
  let c : BoundaryWord := (n, p, fun k => b (s k))
  refine ⟨c, hmono, ?_, ?_⟩
  · ext y
    simp only [c, jumps, Finset.mem_image, Finset.mem_range]
    constructor
    · rintro ⟨i, hi, rfl⟩
      exact hpJ i hi
    · intro hy
      exact hJp y hy
  · intro y hy
    have hmono' : StrictMonoOn c.2.1 (Iio c.1) := hmono
    set k := c.index y with hk
    have hkn : k ≤ n := c.index_le y
    let I : Set ℝ := {z | (0 < k → p (k - 1) < z) ∧ (k < n → z < p k)}
    have hyI : y ∈ I := by
      refine ⟨fun hk0 => ?_, fun hkn' => ?_⟩
      · exact (lt_index_iff hmono' (show k - 1 < c.1 by simp only [c]; omega)).1 (by omega)
      · have hnot : ¬ c.2.1 k < y := fun hlt =>
          (lt_irrefl k) ((lt_index_iff hmono' (show k < c.1 from hkn')).2 hlt)
        have hne : y ≠ p k := fun he' => hy (he' ▸ hpJ k hkn')
        exact lt_of_le_of_ne (not_lt.1 hnot) hne
    have hsI : s k ∈ I := by
      by_cases hk0 : k = 0
      · refine ⟨fun h => absurd hk0 (Nat.pos_iff_ne_zero.1 h), fun _ => ?_⟩
        simp only [s, hk0, ↓reduceIte]
        linarith
      · by_cases hkn' : k < n
        · have hlt : p (k - 1) < p k := hmono (show k - 1 < n by omega) hkn' (by omega)
          simp only [s, hk0, hkn', ↓reduceIte]
          exact ⟨fun _ => by linarith, fun _ => by linarith⟩
        · have hkeq : k = n := le_antisymm hkn (not_lt.1 hkn')
          simp only [s, hk0, hkn', ↓reduceIte]
          refine ⟨fun _ => ?_, fun h => absurd h hkn'⟩
          rw [hkeq]
          linarith
    have hIJ : ∀ z ∈ I, z ∉ J := by
      intro z hz hzJ
      obtain ⟨i, hi, rfl⟩ := hJp z hzJ
      by_cases hik : i < k
      · have hle : p i ≤ p (k - 1) := hmono.monotoneOn hi (show k - 1 < n by omega) (by omega)
        exact absurd (lt_of_le_of_lt hle (hz.1 (by omega))) (lt_irrefl _)
      · have hkn' : k < n := lt_of_le_of_lt (not_lt.1 hik) hi
        have hle : p k ≤ p i := hmono.monotoneOn hkn' hi (not_lt.1 hik)
        exact absurd (lt_of_lt_of_le (hz.2 hkn') hle) (lt_irrefl _)
    have hIc : IsPreconnected I := by
      refine OrdConnected.isPreconnected ⟨fun a ha a' ha' z hz => ?_⟩
      exact ⟨fun h => lt_of_lt_of_le (ha.1 h) hz.1, fun h => lt_of_le_of_lt hz.2 (ha'.2 h)⟩
    have hconst : b (s k) = b y :=
      eq_of_germ_isConstant_on (fun z hz => ⟨b z, hb z (hIJ z hz)⟩) hIc hsI hyI
    exact hconst

end BoundaryWord

section MainFinal

universe v

variable {κ : ℝ} {b : ℝ → ℝ} {jumps : Finset ℝ} {x₁ x₂ θ₁ θ₂ : ℝ} {Ω : Type v} [mΩ : MeasurableSpace Ω]
  {P : Measure Ω} [IsProbabilityMeasure P] {h : Ω → LQGMetric.DistOn upperHalfPlaneOpens} {η₁ η₂ : Ω → ℝ≥0 → ℂ}
  {ζ₁ ζ₂ : Ω → ℝ≥0∞}

/-- **The mean part of `FirstContactWordKernelStatement` from the exposed-side heights alone** (the original word
`c₀` chosen by `exists_fn_eq_strictMonoOn`): in its setting there is a `retSigma d P`-measurable datum, sorted on the
meeting branch, with Lemma 7.8's mean identification on every box, as soon as `IsBoxSideLimit` holds for the side
heights `hL`, `hR`. -/
theorem exists_isBoxMeanIdentification_of_sideLimit (hL75 : Theorem15.Lemma75Statement.{v})
    (hL77 : Supp10.Lemma77Statement.{v}) (hA56 : RetainedRangeEntranceStatement.{v}) (hκ : 0 < κ) (hκ4 : κ < 4)
    (hb : IsPiecewiseConstantBoundaryData b jumps) (hx : x₂ < x₁) (hθ : θ₁ < θ₂ + Real.pi)
    (hh : IsGFFWithBoundaryData P h b jumps) (hη₁ : IsFlowLine κ b jumps x₁ θ₁ P h η₁ ζ₁)
    (hη₂ : IsFlowLine κ b jumps x₂ θ₂ P h η₂ ζ₂) {d : PairData Ω} (hd : d.IsMeasGood) (hζ₁ : d.ζ₁ = ζ₁)
    (hζ₂ : d.ζ₂ = ζ₂)
    (hae : ∀ᵐ ω ∂P, ω ∈ d.G ∧ (∀ s : ℝ≥0, (s : ℝ≥0∞) ≤ ζ₁ ω → d.η₁ ω s = η₁ ω s) ∧
      ∀ t : ℝ≥0, (t : ℝ≥0∞) ≤ ζ₂ ω → d.η₂ ω t = η₂ ω t)
    {u₀ : ℂ → ℝ} (hu₀ : IsBoundedHarmonicExtension b jumps u₀) {hL hR : ℝ}
    (hside : IsBoxSideLimit κ P h η₁ η₂ ζ₁ ζ₂ u₀ d hL hR) :
    ∃ β : Ω → BoundaryWord, Measurable[retSigma d P] β ∧ (∀ᵐ ω ∂P, ω ∈ meetSet d → (β ω).IsSorted) ∧
      IsBoxMeanIdentification κ P h η₁ η₂ ζ₁ ζ₂ u₀ hd β := by
  obtain ⟨c₀, hc₀, hJ, hfn⟩ := BoundaryWord.exists_fn_eq_strictMonoOn hb
  exact exists_word_isBoxMeanIdentification hL75 hL77 hA56 hκ hκ4 hb hx hθ hh hη₁ hη₂ hd hζ₁ hζ₂ hae hu₀ hc₀ hJ
    hfn hside

end MainFinal

end Restart

end InteractingSLE
