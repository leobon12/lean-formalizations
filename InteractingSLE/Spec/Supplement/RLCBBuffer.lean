/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.RLCBCode
import InteractingSLE.Spec.Supplement.G7Measurable

/-!
# The chart interior completion property at one datum, from G2, G2b and G3 (buffer selection)

Packet PROVE-RLC-B, step (i) of `planning/handoffs/PROVE-RLC-A.md` ("buffer selection"). Source: Lemma G3's
hypotheses 2 and 4 (supplement §7.3, pp. 492–493: "Near `wᵢ` its boundary germs are `−λ − θᵢχ` on the left and
`λ − θᵢχ` on the right […] `U₀` is bounded and buffered in a bounded relatively open set `U` […] The closure of `U`
meets the real line only in two disjoint intervals on which the respective canonical seed germs just stated hold. The
remaining part of its closure is in `ℍ`") and W5's proof (p. 535: "In the old joint chart the entire selected fresh
portions therefore fit in a bounded buffer of the relevant comparison theorem").

* `SeedGerm κ θ₁ θ₂ q q₁ q₂ c w`: the word `c` has the canonical seed germs at the chart seeds `0` (angle `θ₂`) and
  `w` (angle `θ₁`), certified on `[−q, 0)`, `(0, q]`, `[q₁, w)`, `(w, q₂]`; `HasSeedGerms` (rational certificates) is a
  measurable set of data (`measurableSet_hasSeedGerms`);
* `bufferSet w ε' ε R = {‖z‖ < R ∧ (ε' < Im z ∨ ‖z‖ < ε ∨ ‖z − w‖ < ε)}`: the countable buffer family;
* **`ae_chartInteriorCompletion_of_hasSeedGerms`**: for a datum with the canonical seed germs, the chart pair (the
  angle-`θ₁` flow from `w` and the angle-`θ₂` flow from `0` of the GFF with that datum) has the interior local
  completion property almost surely — `RLC.ae_isChartCompletable_of_buffer` for every rational buffer (G3 with the G2
  reference `g2Data κ θ₁ θ₂ 0 (w/2) w`) and a pathwise choice of a buffer containing two interior prefixes.
-/

set_option autoImplicit false

noncomputable section

open Complex Set Metric Filter Topology MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

open QuantumZipper (H Hbar)

universe u

namespace InteractingSLE

namespace RLC

open Restart

/-! ### Words with canonical seed germs -/

/-- Two points of a word with no jump position in `[y, y')` have the same boundary value. -/
theorem fn_eq_of_noPos {c : BoundaryWord} {y y' : ℝ} (hyy : y ≤ y')
    (h : ∀ i < c.1, c.2.1 i < y ∨ y' ≤ c.2.1 i) : c.fn y = c.fn y' := by
  have hidx : c.index y = c.index y' := by
    unfold BoundaryWord.index
    refine congrArg Finset.card (Finset.filter_congr fun i hi => ?_)
    rcases h i (Finset.mem_range.1 hi) with h' | h'
    · exact iff_of_true h' (h'.trans_le hyy)
    · exact iff_of_false (fun h'' => absurd (h''.trans_le hyy) (not_lt.2 h'))
        (fun h'' => absurd h'' (not_lt.2 h'))
  unfold BoundaryWord.fn
  rw [hidx]

/-- A word with different values at `y < y'` has a jump position in `[y, y')`. -/
theorem exists_pos_of_fn_ne {c : BoundaryWord} {y y' : ℝ} (hyy : y ≤ y') (hne : c.fn y ≠ c.fn y') :
    ∃ i < c.1, y ≤ c.2.1 i ∧ c.2.1 i < y' := by
  by_contra hno
  push Not at hno
  refine hne (fn_eq_of_noPos hyy fun i hi => ?_)
  by_cases h : c.2.1 i < y
  · exact Or.inl h
  · exact Or.inr (hno i hi (not_lt.1 h))

/-- **Canonical seed germs of a word** at the chart seeds `0` (angle `θ₂`) and `w` (angle `θ₁`), certified on
`[−q, 0)`, `(0, q]`, `[q₁, w)`, `(w, q₂]`: no jump positions there, and the heights `−λ − θ₂χ`, `λ − θ₂χ`,
`−λ − θ₁χ`, `λ − θ₁χ` (G3's hypothesis 2, p. 492). -/
def SeedGerm (κ θ₁ θ₂ q q₁ q₂ : ℝ) (c : BoundaryWord) (w : ℝ) : Prop :=
  0 < q ∧ q < q₁ ∧ q₁ < w ∧ w < q₂ ∧
    (∀ i < c.1, c.2.1 i < -q ∨ c.2.1 i = 0 ∨ (q < c.2.1 i ∧ c.2.1 i < q₁) ∨ c.2.1 i = w ∨ q₂ < c.2.1 i) ∧
    c.fn (-q) = -sleLambda κ - θ₂ * QuantumZipper.chiC κ ∧ c.fn q = sleLambda κ - θ₂ * QuantumZipper.chiC κ ∧
    c.fn q₁ = -sleLambda κ - θ₁ * QuantumZipper.chiC κ ∧ c.fn q₂ = sleLambda κ - θ₁ * QuantumZipper.chiC κ

/-- The data `(c, w)` with canonical seed germs certified at rational points. -/
def HasSeedGerms (κ θ₁ θ₂ : ℝ) : Set (BoundaryWord × ℝ) :=
  {c | ∃ q q₁ q₂ : ℚ, SeedGerm κ θ₁ θ₂ q q₁ q₂ c.1 c.2}

/-- **The data with canonical seed germs form a measurable set.** -/
theorem measurableSet_hasSeedGerms (κ θ₁ θ₂ : ℝ) : MeasurableSet (HasSeedGerms κ θ₁ θ₂) := by
  have hset : HasSeedGerms κ θ₁ θ₂ = ⋃ q : ℚ, ⋃ q₁ : ℚ, ⋃ q₂ : ℚ, {c | SeedGerm κ θ₁ θ₂ q q₁ q₂ c.1 c.2} := by
    ext c; simp [HasSeedGerms]
  rw [hset]
  refine MeasurableSet.iUnion fun q => MeasurableSet.iUnion fun q₁ => MeasurableSet.iUnion fun q₂ => ?_
  have hp : ∀ i : ℕ, Measurable fun c : BoundaryWord × ℝ => c.1.2.1 i :=
    fun i => (measurable_pi_apply i).comp (measurable_fst.comp (measurable_snd.comp measurable_fst))
  have hn : Measurable fun c : BoundaryWord × ℝ => c.1.1 := measurable_fst.comp measurable_fst
  have hfn : ∀ y : ℝ, Measurable fun c : BoundaryWord × ℝ => c.1.fn y :=
    fun y => (Supp7.measurable_boundaryWord_fn y).comp measurable_fst
  have hpos : MeasurableSet {c : BoundaryWord × ℝ | ∀ i < c.1.1, c.1.2.1 i < -(q : ℝ) ∨ c.1.2.1 i = 0 ∨
      ((q : ℝ) < c.1.2.1 i ∧ c.1.2.1 i < q₁) ∨ c.1.2.1 i = c.2 ∨ (q₂ : ℝ) < c.1.2.1 i} := by
    have : {c : BoundaryWord × ℝ | ∀ i < c.1.1, c.1.2.1 i < -(q : ℝ) ∨ c.1.2.1 i = 0 ∨
        ((q : ℝ) < c.1.2.1 i ∧ c.1.2.1 i < q₁) ∨ c.1.2.1 i = c.2 ∨ (q₂ : ℝ) < c.1.2.1 i} =
        ⋂ i : ℕ, ({c : BoundaryWord × ℝ | c.1.1 ≤ i} ∪ {c | c.1.2.1 i < -(q : ℝ) ∨ c.1.2.1 i = 0 ∨
          ((q : ℝ) < c.1.2.1 i ∧ c.1.2.1 i < q₁) ∨ c.1.2.1 i = c.2 ∨ (q₂ : ℝ) < c.1.2.1 i}) := by
      ext c
      simp only [mem_ofPred_eq, mem_iInter, mem_union]
      refine ⟨fun h i => ?_, fun h i hi => ?_⟩
      · by_cases hi : i < c.1.1
        · exact Or.inr (h i hi)
        · exact Or.inl (not_lt.1 hi)
      · rcases h i with h' | h'
        · exact absurd hi (not_lt.2 h')
        · exact h'
    rw [this]
    refine MeasurableSet.iInter fun i => (hn (measurableSet_Iic (a := i))).union ?_
    exact (measurableSet_lt (hp i) measurable_const).union ((measurableSet_eq_fun (hp i) measurable_const).union
      (((measurableSet_lt measurable_const (hp i)).inter (measurableSet_lt (hp i) measurable_const)).union
        ((measurableSet_eq_fun (hp i) measurable_snd).union (measurableSet_lt measurable_const (hp i)))))
  have : {c : BoundaryWord × ℝ | SeedGerm κ θ₁ θ₂ q q₁ q₂ c.1 c.2} =
      {_c : BoundaryWord × ℝ | (0 : ℝ) < q ∧ (q : ℝ) < q₁} ∩ {c | (q₁ : ℝ) < c.2} ∩ {c | c.2 < (q₂ : ℝ)} ∩
        {c : BoundaryWord × ℝ | ∀ i < c.1.1, c.1.2.1 i < -(q : ℝ) ∨ c.1.2.1 i = 0 ∨
          ((q : ℝ) < c.1.2.1 i ∧ c.1.2.1 i < q₁) ∨ c.1.2.1 i = c.2 ∨ (q₂ : ℝ) < c.1.2.1 i} ∩
        {c | c.1.fn (-(q : ℝ)) = -sleLambda κ - θ₂ * QuantumZipper.chiC κ} ∩
        {c | c.1.fn q = sleLambda κ - θ₂ * QuantumZipper.chiC κ} ∩
        {c | c.1.fn q₁ = -sleLambda κ - θ₁ * QuantumZipper.chiC κ} ∩
        {c | c.1.fn q₂ = sleLambda κ - θ₁ * QuantumZipper.chiC κ} := by
    ext c
    simp only [SeedGerm, mem_ofPred_eq, mem_inter_iff]
    tauto
  rw [this]
  exact (((((((MeasurableSet.const _).inter (measurableSet_lt measurable_const measurable_snd)).inter
    (measurableSet_lt measurable_snd measurable_const)).inter hpos).inter
    (measurableSet_eq_fun (hfn _) measurable_const)).inter (measurableSet_eq_fun (hfn _) measurable_const)).inter
    (measurableSet_eq_fun (hfn _) measurable_const)).inter (measurableSet_eq_fun (hfn _) measurable_const)

/-! ### The datum seen by the G2 reference near the seeds -/

section Germ

variable {κ θ₁ θ₂ q q₁ q₂ : ℝ} {c : BoundaryWord} {w : ℝ}

theorem SeedGerm.w_pos (h : SeedGerm κ θ₁ θ₂ q q₁ q₂ c w) : 0 < w := by
  obtain ⟨h0, h1, h2, -⟩ := h; linarith

theorem SeedGerm.fn_neg (h : SeedGerm κ θ₁ θ₂ q q₁ q₂ c w) {y : ℝ} (hy₁ : -q ≤ y) (hy₂ : y < 0) :
    c.fn y = -sleLambda κ - θ₂ * QuantumZipper.chiC κ := by
  obtain ⟨h0, h1, h2, h3, hpos, e1, -⟩ := h
  rw [← e1]
  refine (fn_eq_of_noPos hy₁ fun i hi => ?_).symm
  rcases hpos i hi with h' | h' | h' | h' | h'
  · exact Or.inl h'
  · exact Or.inr (by rw [h']; exact hy₂.le)
  · exact Or.inr (by linarith [h'.1])
  · exact Or.inr (by rw [h']; linarith)
  · exact Or.inr (by linarith)

theorem SeedGerm.fn_pos (h : SeedGerm κ θ₁ θ₂ q q₁ q₂ c w) {y : ℝ} (hy₁ : 0 < y) (hy₂ : y ≤ q) :
    c.fn y = sleLambda κ - θ₂ * QuantumZipper.chiC κ := by
  obtain ⟨h0, h1, h2, h3, hpos, -, e2, -⟩ := h
  rw [← e2]
  refine fn_eq_of_noPos hy₂ fun i hi => ?_
  rcases hpos i hi with h' | h' | h' | h' | h'
  · exact Or.inl (by linarith)
  · exact Or.inl (by rw [h']; exact hy₁)
  · exact Or.inr h'.1.le
  · exact Or.inr (by rw [h']; linarith)
  · exact Or.inr (by linarith)

theorem SeedGerm.fn_left (h : SeedGerm κ θ₁ θ₂ q q₁ q₂ c w) {y : ℝ} (hy₁ : q₁ ≤ y) (hy₂ : y < w) :
    c.fn y = -sleLambda κ - θ₁ * QuantumZipper.chiC κ := by
  obtain ⟨h0, h1, h2, h3, hpos, -, -, e3, -⟩ := h
  rw [← e3]
  refine (fn_eq_of_noPos hy₁ fun i hi => ?_).symm
  rcases hpos i hi with h' | h' | h' | h' | h'
  · exact Or.inl (by linarith)
  · exact Or.inl (by rw [h']; linarith)
  · exact Or.inl (by linarith [h'.2])
  · exact Or.inr (by rw [h']; exact hy₂.le)
  · exact Or.inr (by linarith)

theorem SeedGerm.fn_right (h : SeedGerm κ θ₁ θ₂ q q₁ q₂ c w) {y : ℝ} (hy₁ : w < y) (hy₂ : y ≤ q₂) :
    c.fn y = sleLambda κ - θ₁ * QuantumZipper.chiC κ := by
  obtain ⟨h0, h1, h2, h3, hpos, -, -, -, e4⟩ := h
  rw [← e4]
  refine fn_eq_of_noPos hy₂ fun i hi => ?_
  rcases hpos i hi with h' | h' | h' | h' | h'
  · exact Or.inl (by linarith)
  · exact Or.inl (by rw [h']; linarith)
  · exact Or.inl (by linarith [h'.2])
  · exact Or.inl (by rw [h']; exact hy₁)
  · exact Or.inr h'.le

/-- The jump positions of a word with seed germs near the seeds are the two seeds. -/
theorem SeedGerm.mem_jumps_iff (h : SeedGerm κ θ₁ θ₂ q q₁ q₂ c w) (hκ : 0 < κ) {x : ℝ}
    (hx : (-q < x ∧ x < q) ∨ (q₁ < x ∧ x < q₂)) : x ∈ c.jumps ↔ x = 0 ∨ x = w := by
  have hlam := Sec4.sleLambda_pos hκ
  have hw := h.w_pos
  obtain ⟨h0, h1, h2, h3, hpos, e1, e2, e3, e4⟩ := h
  constructor
  · intro hxJ
    obtain ⟨i, hi, rfl⟩ := BoundaryWord.mem_jumps.1 hxJ
    rcases hx with hx | hx <;> rcases hpos i hi with h' | h' | h' | h' | h'
    all_goals first
      | exact Or.inl h' | exact Or.inr h'
      | (exfalso; linarith [h'.1, h'.2]) | (exfalso; linarith)
  · rintro (rfl | rfl)
    · obtain ⟨i, hi, hi₁, hi₂⟩ := exists_pos_of_fn_ne (show -q ≤ q by linarith)
        (by rw [e1, e2]; intro he; linarith)
      refine BoundaryWord.mem_jumps.2 ⟨i, hi, ?_⟩
      rcases hpos i hi with h' | h' | h' | h' | h'
      · linarith
      · exact h'
      · linarith [h'.1]
      · linarith
      · linarith
    · obtain ⟨i, hi, hi₁, hi₂⟩ := exists_pos_of_fn_ne (show q₁ ≤ q₂ by linarith)
        (by rw [e3, e4]; intro he; linarith)
      refine BoundaryWord.mem_jumps.2 ⟨i, hi, ?_⟩
      rcases hpos i hi with h' | h' | h' | h' | h'
      · linarith
      · linarith
      · linarith [h'.2]
      · exact h'
      · linarith

end Germ

/-! ### The countable buffer family -/

/-- The buffer `{‖z‖ < R ∧ (ε' < Im z ∨ ‖z‖ < ε ∨ ‖z − w‖ < ε)}` around two chart prefixes from the seeds `w` and
`0`. -/
def bufferSet (w ε' ε R : ℝ) : Set ℂ := {z | ‖z‖ < R ∧ (ε' < z.im ∨ ‖z‖ < ε ∨ ‖z - w‖ < ε)}

theorem isOpen_bufferSet (w ε' ε R : ℝ) : IsOpen (bufferSet w ε' ε R) :=
  (isOpen_lt continuous_norm continuous_const).inter ((isOpen_lt continuous_const Complex.continuous_im).union
    ((isOpen_lt continuous_norm continuous_const).union
      (isOpen_lt (continuous_norm.comp (continuous_id.sub continuous_const)) continuous_const)))

theorem isBounded_bufferSet (w ε' ε R : ℝ) : Bornology.IsBounded (bufferSet w ε' ε R) :=
  (Metric.isBounded_ball (x := (0 : ℂ)) (r := R)).subset fun z hz => by
    rw [mem_ball, dist_zero_right]; exact hz.1

/-- The real points of the closure of a buffer lie within `ε` of a seed. -/
theorem re_mem_of_mem_closure_bufferSet {w ε' ε R : ℝ} (hε' : 0 < ε') {z : ℂ}
    (hz : z ∈ closure (bufferSet w ε' ε R)) (hz0 : z.im = 0) : |z.re| ≤ ε ∨ |z.re - w| ≤ ε := by
  have hF : IsClosed {z : ℂ | ε' ≤ z.im ∨ ‖z‖ ≤ ε ∨ ‖z - w‖ ≤ ε} :=
    (isClosed_le continuous_const Complex.continuous_im).union ((isClosed_le continuous_norm continuous_const).union
      (isClosed_le (continuous_norm.comp (continuous_id.sub continuous_const)) continuous_const))
  have hsub : bufferSet w ε' ε R ⊆ {z : ℂ | ε' ≤ z.im ∨ ‖z‖ ≤ ε ∨ ‖z - w‖ ≤ ε} := by
    rintro z ⟨-, h | h | h⟩
    · exact Or.inl h.le
    · exact Or.inr (Or.inl h.le)
    · exact Or.inr (Or.inr h.le)
  rcases closure_minimal hsub hF hz with h | h | h
  · linarith
  · left
    have := Complex.abs_re_le_norm z
    linarith
  · right
    have h' := Complex.abs_re_le_norm (z - w)
    simp only [Complex.sub_re, Complex.ofReal_re] at h'
    linarith

/-- **A prefix from a real seed which is interior after it lies in `{‖z − a‖ < ε} ∪ {Im z > ε'}`** for some
rational `ε' > 0`, and in a ball. -/
theorem exists_rat_im_of_prefix {g : ℝ≥0 → ℂ} {s : ℝ≥0} {a : ℝ} (hg : ContinuousOn g (Iic s)) (h0 : g 0 = a)
    (hin : ∀ t, 0 < t → t ≤ s → g t ∈ H) {ε : ℝ} (hε : 0 < ε) :
    ∃ ε' : ℚ, 0 < (ε' : ℝ) ∧ ∀ t ≤ s, ‖g t - a‖ < ε ∨ (ε' : ℝ) < (g t).im := by
  have hc0 : ContinuousWithinAt g (Iic s) 0 := hg 0 (show (0 : ℝ≥0) ≤ s from zero_le)
  rw [Metric.continuousWithinAt_iff] at hc0
  obtain ⟨δ, hδ, hδg⟩ := hc0 ε hε
  have hdist : ∀ t : ℝ≥0, (t : ℝ) < δ → dist t 0 < δ := fun t ht => by
    rw [NNReal.dist_eq, NNReal.coe_zero, sub_zero, abs_of_nonneg t.coe_nonneg]; exact ht
  set C : Set ℝ≥0 := Icc ⟨δ / 2, by positivity⟩ s with hC
  rcases C.eq_empty_or_nonempty with hCe | hCne
  · refine ⟨1, by norm_num, fun t ht => Or.inl ?_⟩
    have htδ : (t : ℝ) < δ / 2 := by
      by_contra hge
      have : t ∈ C := ⟨by show (δ / 2 : ℝ) ≤ t; linarith, ht⟩
      rw [hCe] at this; exact this
    have := hδg (show t ∈ Iic s from ht) (hdist t (by linarith))
    rw [dist_eq_norm, h0] at this
    exact this
  have hcont : ContinuousOn (fun t => (g t).im) C :=
    Complex.continuous_im.comp_continuousOn (hg.mono fun t ht => ht.2)
  obtain ⟨t₀, ht₀, hmin⟩ := isCompact_Icc.exists_isMinOn hCne hcont
  have ht₀pos : 0 < t₀ := by
    have h1 : (δ / 2 : ℝ) ≤ t₀ := ht₀.1
    exact NNReal.coe_pos.1 (by linarith)
  have hpos : 0 < (g t₀).im := hin t₀ ht₀pos ht₀.2
  obtain ⟨ε', hε'0, hε't⟩ := exists_rat_btwn hpos
  refine ⟨ε', hε'0, fun t ht => ?_⟩
  by_cases htδ : (t : ℝ) < δ / 2
  · left
    have := hδg (show t ∈ Iic s from ht) (hdist t (by linarith))
    rw [dist_eq_norm, h0] at this
    exact this
  · right
    have htC : t ∈ C := ⟨by show (δ / 2 : ℝ) ≤ t; linarith, ht⟩
    exact lt_of_lt_of_le hε't (hmin htC)

/-- A prefix continuous on `[0, s]` is bounded by a rational. -/
theorem exists_rat_norm_lt_of_prefix {g : ℝ≥0 → ℂ} {s : ℝ≥0} (hg : ContinuousOn g (Iic s)) :
    ∃ R : ℚ, ∀ t ≤ s, ‖g t‖ < R := by
  have hK : IsCompact (Iic s) := by rw [← Set.Icc_bot]; exact isCompact_Icc
  obtain ⟨M, hM⟩ := (hK.image_of_continuousOn hg).isBounded.exists_norm_le
  obtain ⟨R, hR⟩ := exists_rat_gt M
  exact ⟨R, fun t ht => lt_of_le_of_lt (hM _ ⟨t, ht, rfl⟩) hR⟩

/-- A path inside a set up to `s < U` exits it no earlier than `s`. -/
theorem le_exitTime {V : Set ℂ} {g : ℝ≥0 → ℂ} {U : ℝ≥0∞} {s : ℝ≥0} (hsU : (s : ℝ≥0∞) < U)
    (hV : ∀ t ≤ s, g t ∈ V) : (s : ℝ≥0∞) ≤ exitTime V g U := by
  unfold exitTime
  refine le_min hsU.le (le_iInf₂ fun t ht => ?_)
  by_contra hlt
  exact ht (hV t (by exact_mod_cast (not_le.1 hlt).le))

/-! ### The chart interior completion property at one datum -/

/-- **The chart interior completion property at a datum with canonical seed germs** (Lemma G3 with the G2 reference
and G2b, through `ae_isChartCompletable_of_buffer`, for the countable family of buffers; W5, p. 535: "the entire
selected fresh portions therefore fit in a bounded buffer of the relevant comparison theorem"). For the GFF with the
datum's word and its angle-`θ₁` flow from `w > 0` and angle-`θ₂` flow from `0`, almost surely every pair of available
prefixes which stay in `ℍ` after their seeds is completable. -/
theorem ae_chartInteriorCompletion_of_hasSeedGerms (hG2 : G2ReferenceStatement.{u})
    (hG3 : G3ChartComparisonStatement.{u}) {κ θ₁ θ₂ : ℝ} (hκ : 0 < κ) (hκ4 : κ < 4) (hθ : θ₁ < θ₂)
    {c : BoundaryWord × ℝ} (hc : c ∈ HasSeedGerms κ θ₁ θ₂) {S : Type u} [MeasurableSpace S] (Q₀ : Measure S)
    [IsProbabilityMeasure Q₀] (H₀ : S → LQGMetric.DistOn upperHalfPlaneOpens)
    (hH : IsGFFWithBoundaryData Q₀ H₀ c.1.fn c.1.jumps) (Γ₁ Γ₂ : S → ℝ≥0 → ℂ) (U₁ U₂ : S → ℝ≥0∞)
    (h₁ : IsFlowLine κ c.1.fn c.1.jumps c.2 θ₁ Q₀ H₀ Γ₁ U₁) (h₂ : IsFlowLine κ c.1.fn c.1.jumps 0 θ₂ Q₀ H₀ Γ₂ U₂) :
    ∀ᵐ x ∂Q₀, ChartInteriorCompletion (Γ₁ x) (U₁ x) (Γ₂ x) (U₂ x) := by
  obtain ⟨q, q₁, q₂, hS⟩ := hc
  set w : ℝ := c.2 with hwdef
  have hw : 0 < w := hS.w_pos
  have hq : (0 : ℝ) < q := hS.1
  have hqq₁ : (q : ℝ) < q₁ := hS.2.1
  have hq₁w : (q₁ : ℝ) < w := hS.2.2.1
  have hwq₂ : w < (q₂ : ℝ) := hS.2.2.2.1
  have hlam := Sec4.sleLambda_pos hκ
  set ε₀ : ℝ := min (min (q : ℝ) (w - q₁)) (min ((q₂ : ℝ) - w) (w / 4)) with hε₀
  have hε₀q : ε₀ ≤ q := (min_le_left _ _).trans (min_le_left _ _)
  have hε₀1 : ε₀ ≤ w - q₁ := (min_le_left _ _).trans (min_le_right _ _)
  have hε₀2 : ε₀ ≤ q₂ - w := (min_le_right _ _).trans (min_le_left _ _)
  have hε₀4 : ε₀ ≤ w / 4 := (min_le_right _ _).trans (min_le_right _ _)
  have hε₀pos : 0 < ε₀ := lt_min (lt_min hq (by linarith)) (lt_min (by linarith) (by linarith))
  set O : Set ℝ := {x | |x| < ε₀ ∨ |x - w| < ε₀} with hOdef
  have hO : IsOpen O := (isOpen_lt (continuous_abs.comp continuous_id) continuous_const).union
    (isOpen_lt (continuous_abs.comp (continuous_id.sub continuous_const)) continuous_const)
  have hOmem : ∀ x ∈ O, (-(q : ℝ) < x ∧ x < q) ∨ ((q₁ : ℝ) < x ∧ x < q₂) := by
    rintro x (hx | hx) <;> rw [abs_lt] at hx
    · exact Or.inl ⟨by linarith, by linarith⟩
    · exact Or.inr ⟨by linarith, by linarith⟩
  set J : Finset ℝ := c.1.jumps with hJ
  have h0J : (0 : ℝ) ∈ J := (hS.mem_jumps_iff hκ (Or.inl ⟨by linarith, hq⟩)).2 (Or.inl rfl)
  have hwJ : w ∈ J := (hS.mem_jumps_iff hκ (Or.inr ⟨hq₁w, hwq₂⟩)).2 (Or.inr rfl)
  -- the datum with the reference values at the two seeds (values at jump points are immaterial)
  set c' : ℝ → ℝ := fun x => if x = 0 ∨ x = w then g2Data κ θ₁ θ₂ 0 (w / 2) w x else c.1.fn x with hc'
  have hoff : ∀ y ∉ J, c' y = c.1.fn y := fun y hy => by
    have : ¬ (y = 0 ∨ y = w) := by rintro (rfl | rfl) <;> contradiction
    simp only [hc', this, ite_false]
  have hoff' : ∀ y ∉ (J : Set ℝ), c' y = c.1.fn y := fun y hy => hoff y hy
  have hpc : IsPiecewiseConstantBoundaryData c' J := by
    intro y hy
    have hy0 : y ≠ 0 := fun h => hy (h ▸ h0J)
    have hyw : y ≠ w := fun h => hy (h ▸ hwJ)
    filter_upwards [c.1.isPiecewiseConstantBoundaryData y hy, eventually_ne_nhds hy0, eventually_ne_nhds hyw]
      with z hz hz0 hzw
    have : ¬ (z = 0 ∨ z = w) := by rintro (h | h) <;> contradiction
    rw [hoff y hy]
    simp only [hc', this, ite_false]
    exact hz
  have hcO : ∀ x ∈ O, c' x = g2Data κ θ₁ θ₂ 0 (w / 2) w x := by
    intro x hx
    by_cases hx0w : x = 0 ∨ x = w
    · simp only [hc', hx0w, ite_true]
    simp only [hc', hx0w, ite_false]
    push Not at hx0w
    rcases hx with hx | hx <;> rw [abs_lt] at hx
    · rcases lt_or_gt_of_ne hx0w.1 with hneg | hpos
      · rw [hS.fn_neg (by linarith) hneg]; simp [g2Data, hneg]
      · rw [hS.fn_pos hpos (by linarith)]
        have h1 : ¬ x < 0 := not_lt.2 hpos.le
        have h2 : x < w / 2 := by linarith
        simp [g2Data, h1, h2]
    · rcases lt_or_gt_of_ne hx0w.2 with hlt | hgt
      · rw [hS.fn_left (by linarith) hlt]
        have h1 : ¬ x < 0 := by linarith
        have h2 : ¬ x < w / 2 := by linarith
        simp [g2Data, h1, h2, hlt]
      · rw [hS.fn_right hgt (by linarith)]
        have h1 : ¬ x < 0 := by linarith
        have h2 : ¬ x < w / 2 := by linarith
        have h3 : ¬ x < w := not_lt.2 hgt.le
        simp [g2Data, h1, h2, h3]
  have hJO : ∀ x ∈ O, x ∈ J ↔ x ∈ ({0, w / 2, w} : Finset ℝ) := by
    intro x hx
    rw [hS.mem_jumps_iff hκ (hOmem x hx)]
    simp only [Finset.mem_insert, Finset.mem_singleton]
    constructor
    · rintro (h | h)
      · exact Or.inl h
      · exact Or.inr (Or.inr h)
    · rintro (h | h | h)
      · exact Or.inl h
      · exfalso
        rcases hx with hx | hx <;> rw [abs_lt, h] at hx <;> linarith [hx.1, hx.2]
      · exact Or.inr h
  have hH' : IsGFFWithBoundaryData Q₀ H₀ c' J := (isGFFWithBoundaryData_congr Q₀ H₀ hoff').2 hH
  have h₁' : IsFlowLine κ c' J w θ₁ Q₀ H₀ Γ₁ U₁ := (isFlowLine_congr_of_eqOn hoff).2 h₁
  have h₂' : IsFlowLine κ c' J 0 θ₂ Q₀ H₀ Γ₂ U₂ := (isFlowLine_congr_of_eqOn hoff).2 h₂
  -- the comparison on every rational buffer
  have hall : ∀ᵐ x ∂Q₀, ∀ r : ℚ × ℚ × ℚ, 0 < (r.1 : ℝ) → 0 < (r.2.1 : ℝ) → (r.2.1 : ℝ) < ε₀ →
      ∀ s₁ s₂ : ℝ≥0, (s₁ : ℝ≥0∞) ≤ exitTime (bufferSet w r.1 r.2.1 r.2.2) (Γ₁ x) (U₁ x) →
        (s₂ : ℝ≥0∞) ≤ exitTime (bufferSet w r.1 r.2.1 r.2.2) (Γ₂ x) (U₂ x) →
        IsChartCompletable (Γ₁ x) s₁ (Γ₂ x) s₂ := by
    refine ae_all_iff.2 fun r => ?_
    by_cases hr : 0 < (r.1 : ℝ) ∧ 0 < (r.2.1 : ℝ) ∧ (r.2.1 : ℝ) < ε₀
    · have hVO : ∀ z ∈ closure (bufferSet w r.1 r.2.1 r.2.2), z.im = 0 → z.re ∈ O := fun z hz hz0 => by
        rcases re_mem_of_mem_closure_bufferSet hr.1 hz hz0 with h | h
        · exact Or.inl (lt_of_le_of_lt h hr.2.2)
        · exact Or.inr (lt_of_le_of_lt h hr.2.2)
      filter_upwards [ae_isChartCompletable_of_buffer hG2 hG3 hκ hκ4 hθ (half_pos hw) (half_lt_self hw) hpc hO hcO
        hJO (isOpen_bufferSet _ _ _ _) (isBounded_bufferSet _ _ _ _) hVO Q₀ H₀ hH' Γ₁ Γ₂ U₁ U₂ h₁' h₂']
        with x hx _ _ _
      exact hx
    · exact Eventually.of_forall fun x h1 h2 h3 => absurd ⟨h1, h2, h3⟩ hr
  filter_upwards [hall, Supp9.ae_apply_zero_of_isFlowLine h₁, Supp9.ae_apply_zero_of_isFlowLine h₂,
    Sec7.ae_continuousOn_of_isFlowLine h₁, Sec7.ae_continuousOn_of_isFlowLine h₂] with x hx z₁ z₂ k₁ k₂
  intro s₁ s₂ hs₁ hs₂ i₁ i₂
  have cont₁ : ContinuousOn (Γ₁ x) (Iic s₁) := k₁.mono fun t ht => (ENNReal.coe_le_coe.2 ht).trans hs₁.le
  have cont₂ : ContinuousOn (Γ₂ x) (Iic s₂) := k₂.mono fun t ht => (ENNReal.coe_le_coe.2 ht).trans hs₂.le
  obtain ⟨ε, hε0, hεε₀⟩ := exists_rat_btwn hε₀pos
  obtain ⟨e₁, he₁, hp₁⟩ := exists_rat_im_of_prefix cont₁ z₁ i₁ hε0
  obtain ⟨e₂, he₂, hp₂⟩ := exists_rat_im_of_prefix cont₂ z₂ i₂ hε0
  obtain ⟨R₁, hR₁⟩ := exists_rat_norm_lt_of_prefix cont₁
  obtain ⟨R₂, hR₂⟩ := exists_rat_norm_lt_of_prefix cont₂
  have he : (0 : ℝ) < ((min e₁ e₂ : ℚ) : ℝ) := by push_cast; exact lt_min he₁ he₂
  have mem₁ : ∀ t ≤ s₁, Γ₁ x t ∈ bufferSet w (min e₁ e₂ : ℚ) ε (max R₁ R₂ : ℚ) := by
    intro t ht
    refine ⟨lt_of_lt_of_le (hR₁ t ht) (by push_cast; exact le_max_left _ _), ?_⟩
    rcases hp₁ t ht with h | h
    · exact Or.inr (Or.inr h)
    · exact Or.inl (lt_of_le_of_lt (by push_cast; exact min_le_left _ _) h)
  have mem₂ : ∀ t ≤ s₂, Γ₂ x t ∈ bufferSet w (min e₁ e₂ : ℚ) ε (max R₁ R₂ : ℚ) := by
    intro t ht
    refine ⟨lt_of_lt_of_le (hR₂ t ht) (by push_cast; exact le_max_right _ _), ?_⟩
    rcases hp₂ t ht with h | h
    · refine Or.inr (Or.inl ?_)
      simpa using h
    · exact Or.inl (lt_of_le_of_lt (by push_cast; exact min_le_right _ _) h)
  exact hx (min e₁ e₂, ε, max R₁ R₂) he hε0 hεε₀ s₁ s₂ (le_exitTime hs₁ mem₁) (le_exitTime hs₂ mem₂)

end RLC

end InteractingSLE
