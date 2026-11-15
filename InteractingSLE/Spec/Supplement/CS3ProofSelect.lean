/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GB9CapStages

/-!
# Lemma A.1 of the follow-up note: the finite-candidate rule with a possible failed crossing

Packet PROVE-T14-TIP7, ruling R53 (`source/external/AstraIG1/ig1_followup_a_e_audited.txt`, A.2, lines 78–116):

> **Lemma A.1.** Retain a canonical stage-start history and its conditional next-piece kernel. Let `F` be a finite
> stopping time in original flow capacity, strictly before old-counterflow contact and any continuation threshold. Let
> `X` be the continuous joint-chart driver in that clock, and let `γ` be the physical trace. Fix `e ∈ {−1, 1}`, and
> let `S` be its first crossing of `2e` before `F`, with `S = ∞` when there is no such crossing. Put
> `I₊ = (7/4, 9/4)`, `I₋ = (−9/4, −7/4)`. Suppose, conditionally on the stage-start history, that `P(S < F) > 1 − ε/2`.
> There is a rule selected before exploring the stage which succeeds with conditional probability greater than
> `1 − ε`, stops on success at a time `q ∈ Q` with `S < q < F`, `γ(q) ∈ ℍ`, `X_q ∈ I_e`, and otherwise aborts at `F`.

The proof has a deterministic part and a selection part:

* **`exists_mem_cand_of_lt`** (deterministic): "On `{S < F}`, continuity gives a nonempty open interval just after
  `S`, before `F`, on which `X ∈ I_e`. Lemma 2.5 […] makes interior physical times dense in that interval. Those times
  form an open set by continuity of the trace. Hence an open subinterval satisfies all the required tests and meets
  `Q`." Here `X_S = 2e ∈ I_e`, `X` and `γ` are continuous on `[S, F]`, and interior times are dense in `[S, F]` (the
  consequence of Lemma 2.5 the note uses; `exists_interior_of_volume_eq_zero` derives it from Lebesgue-nullity of the
  boundary times).
* **`iUnion_candEvent_eq`** ("Conversely, any successful test implies `S < F`. Thus `E_m ↑ {S < F}`"), pathwise:
  `E_m = ⋃_{n ≤ m} {S < q_n < F, γ(q_n) ∈ ℍ, X_{q_n} ∈ I_e}` exhaust `{S < F}` on every path with the deterministic
  hypotheses, for an enumeration `q` of a dense `Q`.
* **`le_measure_inter_selected_gen`**: TIP6's `GB9Cap.le_measure_inter_selected` for any family of events, assuming
  only that almost every stage-start state has an index of conditional probability `≥ 1 − ε` (this covers the
  least-index selection of A.4 over buffer, angle index and candidate count, encoded in `ℕ`);
* **`le_measure_inter_selected_of_lt`** (A.1's conclusion): increasing events with `K_z(⋃ E_m) > 1 − ε` (the strict
  margin `P(S < F) > 1 − ε/2 > 1 − ε`) give the selected rule success probability `≥ (1 − ε) P(Z⁻¹C)`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped NNReal ENNReal
open QuantumZipper (H)

namespace InteractingSLE

namespace Theorem14

namespace CS3Select

open Supp8.GB9Stop

/-! ### The bands -/

/-- The central bands `I₊ = (7/4, 9/4)` (for `e = 1`) and `I₋ = (−9/4, −7/4)` (for `e = −1`): `I_e = e·(7/4, 9/4)`. -/
def band (e : ℝ) : Set ℝ := {x | 7 / 4 < e * x ∧ e * x < 9 / 4}

theorem isOpen_band (e : ℝ) : IsOpen (band e) :=
  (isOpen_lt continuous_const (continuous_const.mul continuous_id)).inter
    (isOpen_lt (continuous_const.mul continuous_id) continuous_const)

theorem two_mul_mem_band {e : ℝ} (he : e = 1 ∨ e = -1) : 2 * e ∈ band e := by
  rcases he with rfl | rfl <;> norm_num [band]

/-! ### The deterministic part -/

section Path

variable {X : ℝ≥0 → ℝ} {γ : ℝ≥0 → ℂ} {S F : ℝ≥0} {e : ℝ}

/-- **A candidate time after the crossing** (A.1, deterministic). If `S < F`, `X` and `γ` are continuous on `[S, F]`,
`X_S = 2e` (`e = ±1`), interior times are dense in `[S, F]` and `Q` is dense, then some `q ∈ Q` satisfies
`S < q < F`, `γ(q) ∈ ℍ`, `X_q ∈ I_e`. -/
theorem exists_mem_cand_of_lt (hSF : S < F) (hX : ContinuousOn X (Icc S F)) (hγ : ContinuousOn γ (Icc S F))
    (he : e = 1 ∨ e = -1) (hXS : X S = 2 * e)
    (hint : ∀ a b : ℝ≥0, S ≤ a → a < b → b ≤ F → ∃ u, a < u ∧ u < b ∧ γ u ∈ H) {Q : Set ℝ≥0} (hQ : Dense Q) :
    ∃ q ∈ Q, S < q ∧ q < F ∧ γ q ∈ H ∧ X q ∈ band e := by
  -- `X ∈ I_e` on `[S, S + δ)` within `[S, F]`
  have hXS' : X S ∈ band e := hXS ▸ two_mul_mem_band he
  have hev : ∀ᶠ u in 𝓝[Icc S F] S, X u ∈ band e :=
    (hX S ⟨le_rfl, hSF.le⟩).eventually ((isOpen_band e).mem_nhds hXS')
  obtain ⟨b, hSb, hb⟩ : ∃ b, S < b ∧ ∀ u ∈ Icc S F, u < b → X u ∈ band e := by
    rcases (mem_nhdsWithin.1 hev) with ⟨U, hU, hSU, hUsub⟩
    obtain ⟨b, hSb, hbU⟩ := exists_Ico_subset_of_mem_nhds (hU.mem_nhds hSU) ⟨F, hSF⟩
    exact ⟨b, hSb, fun u hu hub => hUsub ⟨hbU ⟨hu.1, hub⟩, hu⟩⟩
  set b' := min b F with hb'
  have hSb' : S < b' := lt_min hSb hSF
  obtain ⟨u, hSu, hub', hγu⟩ := hint S b' le_rfl hSb' (min_le_right _ _)
  have huI : u ∈ Icc S F := ⟨hSu.le, hub'.le.trans (min_le_right _ _)⟩
  have hXu : X u ∈ band e := hb u huI (hub'.trans_le (min_le_left _ _))
  -- an open neighbourhood of `u` inside `(S, b')` where `γ ∈ ℍ` and `X ∈ I_e`
  have hHopen : IsOpen H := isOpen_lt continuous_const Complex.continuous_im
  have hu_int : Icc S F ∈ 𝓝 u := Icc_mem_nhds hSu (hub'.trans_le (min_le_right _ _))
  have hγev : ∀ᶠ v in 𝓝 u, γ v ∈ H :=
    ((hγ.continuousAt hu_int).eventually (hHopen.mem_nhds hγu))
  have hXev : ∀ᶠ v in 𝓝 u, X v ∈ band e :=
    ((hX.continuousAt hu_int).eventually ((isOpen_band e).mem_nhds hXu))
  have hIoo : ∀ᶠ v in 𝓝 u, v ∈ Ioo S b' := Ioo_mem_nhds hSu hub'
  obtain ⟨V, hV, hVo, huV⟩ := mem_nhds_iff.1 ((hγev.and hXev).and hIoo)
  obtain ⟨q, hqV, hqQ⟩ := hQ.inter_open_nonempty V hVo ⟨u, huV⟩
  obtain ⟨⟨hγq, hXq⟩, hq⟩ := hV hqV
  exact ⟨q, hqQ, hq.1, hq.2.trans_le (min_le_right _ _), hγq, hXq⟩

/-- **Interior times are dense when the boundary times are Lebesgue-null** (the form in which A.1 uses Lemma 2.5): if
the times `s ∈ [S, F]` with `γ(s) ∉ ℍ` form a null set, every nondegenerate subinterval of `[S, F]` contains an
interior time. -/
theorem exists_interior_of_volume_eq_zero
    (hnull : volume {s : ℝ | (S : ℝ) ≤ s ∧ s ≤ F ∧ γ s.toNNReal ∉ H} = 0) :
    ∀ a b : ℝ≥0, S ≤ a → a < b → b ≤ F → ∃ u, a < u ∧ u < b ∧ γ u ∈ H := by
  intro a b hSa hab hbF
  by_contra hno
  push Not at hno
  have hsub : Ioo (a : ℝ) b ⊆ {s : ℝ | (S : ℝ) ≤ s ∧ s ≤ F ∧ γ s.toNNReal ∉ H} := by
    intro s hs
    have hs0 : (0 : ℝ) ≤ s := (NNReal.coe_nonneg a).trans hs.1.le
    have hlt1 : a < s.toNNReal := by
      rw [← NNReal.coe_lt_coe, Real.coe_toNNReal _ hs0]; exact hs.1
    have hlt2 : s.toNNReal < b := by
      rw [← NNReal.coe_lt_coe, Real.coe_toNNReal _ hs0]; exact hs.2
    exact ⟨(NNReal.coe_le_coe.2 hSa).trans hs.1.le, hs.2.le.trans (NNReal.coe_le_coe.2 hbF),
      hno _ hlt1 hlt2⟩
  have hpos : 0 < volume (Ioo (a : ℝ) b) := by
    rw [Real.volume_Ioo]
    exact ENNReal.ofReal_pos.2 (sub_pos.2 (NNReal.coe_lt_coe.2 hab))
  exact absurd (measure_mono_null hsub hnull) hpos.ne'

/-- The candidate event at the `n`-th point `q n`: `S < q n < F`, `γ(q n) ∈ ℍ`, `X_{q n} ∈ I_e`. -/
def CandAt (X : ℝ≥0 → ℝ) (γ : ℝ≥0 → ℂ) (S F : ℝ≥0∞) (e : ℝ) (q : ℕ → ℝ≥0) (n : ℕ) : Prop :=
  S < (q n : ℝ≥0∞) ∧ (q n : ℝ≥0∞) < F ∧ γ (q n) ∈ H ∧ X (q n) ∈ band e

/-- **`E_m ↑ {S < F}`, pathwise** (A.1): with an enumeration `q` of a dense set, the candidate events up to `m` are
increasing in `m` and their union is `S < F`, for a path with the deterministic hypotheses at its (finite) crossing
time. -/
theorem exists_candAt_iff {q : ℕ → ℝ≥0} (hQ : Dense (range q)) {S' F' : ℝ≥0∞}
    (hdet : S' < F' → ∃ S F : ℝ≥0, S' = S ∧ F' = F ∧ ContinuousOn X (Icc S F) ∧ ContinuousOn γ (Icc S F) ∧
      X S = 2 * e ∧ ∀ a b : ℝ≥0, S ≤ a → a < b → b ≤ F → ∃ u, a < u ∧ u < b ∧ γ u ∈ H)
    (he : e = 1 ∨ e = -1) :
    (∃ n, CandAt X γ S' F' e q n) ↔ S' < F' := by
  constructor
  · rintro ⟨n, h1, h2, -, -⟩
    exact h1.trans h2
  · intro hlt
    obtain ⟨S, F, rfl, rfl, hX, hγ, hXS, hint⟩ := hdet hlt
    obtain ⟨r, ⟨n, rfl⟩, h1, h2, h3, h4⟩ :=
      exists_mem_cand_of_lt (ENNReal.coe_lt_coe.1 hlt) hX hγ he hXS hint hQ
    exact ⟨n, ENNReal.coe_lt_coe.2 h1, ENNReal.coe_lt_coe.2 h2, h3, h4⟩

end Path

/-! ### The selected rule -/

section Selected

variable {𝒵 Ω : Type*} [MeasurableSpace 𝒵] [MeasurableSpace Ω] {P : Measure Ω}

/-- **An index with conditional probability `≥ 1 − ε` from a strict margin** on the union of increasing events. -/
theorem exists_index_of_lt (K : Kernel 𝒵 Ω) {E : ℕ → Set Ω} (hmono : Monotone E) {z : 𝒵} {ε : ℝ≥0∞}
    (hlt : 1 - ε < K z (⋃ m, E m)) : ∃ m, 1 - ε ≤ K z (E m) := by
  have hlim := tendsto_measure_iUnion_atTop (μ := K z) hmono
  obtain ⟨m, hm⟩ := (hlim.eventually (lt_mem_nhds hlt)).exists
  exact ⟨m, hm.le⟩

/-- **The selected rule succeeds with conditional probability at least `1 − ε`, for any family of events**: if
almost every stage-start state has an index with conditional probability `≥ 1 − ε`, the selected event
`E_{m(Z)}` (`GB9Stop.selIndex`, the least such index) has probability at least `(1 − ε) P(Z⁻¹C)` on every event
`Z⁻¹C` of the stage-start state. -/
theorem le_measure_inter_selected_gen {K : Kernel 𝒵 Ω} {Z : Ω → 𝒵} (hZ : Measurable Z) {E : ℕ → Set Ω}
    (hE : ∀ m, MeasurableSet (E m)) {ε : ℝ≥0∞}
    (hK : ∀ C B, MeasurableSet C → MeasurableSet B → P (Z ⁻¹' C ∩ B) = ∫⁻ ω in Z ⁻¹' C, K (Z ω) B ∂P)
    (hex : ∀ᵐ ω ∂P, ∃ m, 1 - ε ≤ K (Z ω) (E m)) {C : Set 𝒵} (hC : MeasurableSet C) :
    (1 - ε) * P (Z ⁻¹' C) ≤ P (Z ⁻¹' C ∩ {ω | ω ∈ E (selIndex K E ε (Z ω))}) := by
  classical
  set sel : 𝒵 → ℕ := selIndex K E ε with hsel
  have hselm : Measurable sel := measurable_selIndex K hE ε
  set A : ℕ → Set Ω := fun m => Z ⁻¹' (C ∩ sel ⁻¹' {m}) with hA
  have hAm : ∀ m, MeasurableSet (A m) := fun m => hZ (hC.inter (hselm (measurableSet_singleton m)))
  have hAd : Pairwise (Function.onFun Disjoint A) := by
    intro m n hmn
    refine Set.disjoint_left.2 fun ω h1 h2 => hmn ?_
    have e1 : sel (Z ω) = m := h1.2
    have e2 : sel (Z ω) = n := h2.2
    rw [← e1, ← e2]
  have hUA : (⋃ m, A m) = Z ⁻¹' C := by
    ext ω
    simp only [hA, mem_iUnion, mem_preimage, mem_inter_iff, mem_singleton_iff]
    exact ⟨fun ⟨_, h, _⟩ => h, fun h => ⟨sel (Z ω), h, rfl⟩⟩
  have hset : Z ⁻¹' C ∩ {ω | ω ∈ E (sel (Z ω))} = ⋃ m, (A m ∩ E m) := by
    ext ω
    simp only [hA, mem_inter_iff, mem_preimage, mem_ofPred_eq, mem_iUnion, mem_singleton_iff]
    exact ⟨fun ⟨h1, h2⟩ => ⟨sel (Z ω), ⟨h1, rfl⟩, h2⟩, fun ⟨m, ⟨h1, h2⟩, h3⟩ => ⟨h1, by rw [h2]; exact h3⟩⟩
  have hdisj : Pairwise (Function.onFun Disjoint fun m => A m ∩ E m) := fun m n hmn =>
    (hAd hmn).mono inter_subset_left inter_subset_left
  have hterm : ∀ m, P (A m ∩ E m) = ∫⁻ ω in A m, K (Z ω) (E (sel (Z ω))) ∂P := by
    intro m
    rw [show A m = Z ⁻¹' (C ∩ sel ⁻¹' {m}) from rfl, hK _ _ (hC.inter (hselm (measurableSet_singleton m))) (hE m)]
    refine setLIntegral_congr_fun (hAm m) fun ω hω => ?_
    have : sel (Z ω) = m := hω.2
    rw [this]
  have hsel_ae : ∀ᵐ ω ∂P, 1 - ε ≤ K (Z ω) (E (sel (Z ω))) := by
    filter_upwards [hex] with ω hω
    exact selIndex_spec K E ε hω
  calc (1 - ε) * P (Z ⁻¹' C) = ∫⁻ _ in Z ⁻¹' C, (1 - ε) ∂P := by
        rw [setLIntegral_const, mul_comm]
    _ ≤ ∫⁻ ω in Z ⁻¹' C, K (Z ω) (E (sel (Z ω))) ∂P := setLIntegral_mono_ae' (hZ hC) (hsel_ae.mono
        fun ω hω _ => hω)
    _ = ∑' m, ∫⁻ ω in A m, K (Z ω) (E (sel (Z ω))) ∂P := by
        rw [← hUA, lintegral_iUnion hAm hAd]
    _ = ∑' m, P (A m ∩ E m) := by simp only [hterm]
    _ = P (Z ⁻¹' C ∩ {ω | ω ∈ E (sel (Z ω))}) := by
        rw [hset, measure_iUnion hdisj fun m => (hAm m).inter (hE m)]

/-- **Lemma A.1, the success bound**: increasing events whose union has conditional probability `> 1 − ε` for almost
every stage-start state (`E_m ↑ {S < F}` and `P(S < F) > 1 − ε/2`) give the selected rule success probability at
least `(1 − ε) P(Z⁻¹C)` on every event of the stage-start state. -/
theorem le_measure_inter_selected_of_lt {K : Kernel 𝒵 Ω} {Z : Ω → 𝒵} (hZ : Measurable Z) {E : ℕ → Set Ω}
    (hE : ∀ m, MeasurableSet (E m)) (hmono : Monotone E) {ε : ℝ≥0∞}
    (hK : ∀ C B, MeasurableSet C → MeasurableSet B → P (Z ⁻¹' C ∩ B) = ∫⁻ ω in Z ⁻¹' C, K (Z ω) B ∂P)
    (hlt : ∀ᵐ ω ∂P, 1 - ε < K (Z ω) (⋃ m, E m)) {C : Set 𝒵} (hC : MeasurableSet C) :
    (1 - ε) * P (Z ⁻¹' C) ≤ P (Z ⁻¹' C ∩ {ω | ω ∈ E (selIndex K E ε (Z ω))}) :=
  le_measure_inter_selected_gen hZ hE hK (hlt.mono fun _ h => exists_index_of_lt K hmono h) hC

omit [MeasurableSpace Ω] in
/-- The candidate events up to `m` increase with `m`. -/
theorem monotone_accumulate (E : ℕ → Set Ω) : Monotone fun m => ⋃ n ≤ m, E n := by
  intro m m' h ω hω
  simp only [mem_iUnion, exists_prop] at hω ⊢
  obtain ⟨n, hn, hω⟩ := hω
  exact ⟨n, hn.trans h, hω⟩

omit [MeasurableSpace Ω] in
/-- `⋃_m ⋃_{n ≤ m} E n = ⋃_n E n`. -/
theorem iUnion_accumulate (E : ℕ → Set Ω) : (⋃ m, ⋃ n ≤ m, E n) = ⋃ n, E n := by
  ext ω
  simp only [mem_iUnion, exists_prop]
  exact ⟨fun ⟨_, n, _, h⟩ => ⟨n, h⟩, fun ⟨n, h⟩ => ⟨n, n, le_rfl, h⟩⟩

end Selected

/-! ### The rule is a stopping time -/

section Rule

variable {Ω : Type*} {mΩ : MeasurableSpace Ω}

/-- **The finite-candidate rule** (A.1): with the candidate times `q`, the selected count `M` (fixed at the stage
start) and the test events `T n` (`S < q n < F`, `γ(q n) ∈ ℍ`, `X_{q n} ∈ I_e`), stop at the first qualifying candidate
among `q 0, …, q (M ω)` in chronological order, or at `F` if none qualifies. -/
def ruleTime (q : ℕ → ℝ≥0) (M : Ω → ℕ) (T : ℕ → Set Ω) (F : Ω → ℝ≥0∞) (ω : Ω) : ℝ≥0∞ :=
  min (F ω) (⨅ n ∈ {n | n ≤ M ω ∧ ω ∈ T n}, (q n : ℝ≥0∞))

theorem ruleTime_le_coe_iff (q : ℕ → ℝ≥0) (M : Ω → ℕ) (T : ℕ → Set Ω) (F : Ω → ℝ≥0∞) (ω : Ω) (t : ℝ≥0) :
    ruleTime q M T F ω ≤ t ↔ F ω ≤ t ∨ ∃ n, n ≤ M ω ∧ ω ∈ T n ∧ q n ≤ t := by
  have hfin : {n | n ≤ M ω ∧ ω ∈ T n}.Finite := (Set.finite_Iic (M ω)).subset fun n hn => hn.1
  unfold ruleTime
  rw [min_le_iff]
  refine or_congr Iff.rfl ⟨fun h => ?_, fun ⟨n, hn, hT, hq⟩ =>
    (biInf_le (fun n => (q n : ℝ≥0∞)) (show n ∈ {n | n ≤ M ω ∧ ω ∈ T n} from ⟨hn, hT⟩)).trans
      (by exact_mod_cast hq)⟩
  by_cases hne : {n | n ≤ M ω ∧ ω ∈ T n}.Nonempty
  · obtain ⟨n, hn, hmin⟩ := hfin.exists_minimalFor (fun n => (q n : ℝ≥0∞)) _ hne
    have hle : (q n : ℝ≥0∞) ≤ ⨅ n ∈ {n | n ≤ M ω ∧ ω ∈ T n}, (q n : ℝ≥0∞) :=
      le_iInf₂ fun m hm => by
        rcases le_total (q n : ℝ≥0∞) (q m) with h' | h'
        · exact h'
        · exact hmin hm h'
    exact ⟨n, hn.1, hn.2, by exact_mod_cast hle.trans h⟩
  · rw [Set.not_nonempty_iff_eq_empty] at hne
    rw [hne] at h
    simp only [Set.mem_empty_iff_false, iInf_false, iInf_top, top_le_iff] at h
    exact absurd h ENNReal.coe_ne_top

/-- **The finite-candidate rule is a stopping time** ("Each test at `q` is measurable at `q`, including `S < q` and
`q < F`. On `S < q` the stage has started and the selected integer is already known. The rule is therefore a stopping
time"): if `F` is a stopping time and `{n ≤ M} ∩ T n` is an event at time `q n` for every `n`. -/
theorem isStoppingTime_ruleTime {𝓕 : Filtration ℝ≥0 mΩ} {q : ℕ → ℝ≥0} {M : Ω → ℕ} {T : ℕ → Set Ω}
    {F : Ω → ℝ≥0∞} (hF : IsStoppingTime 𝓕 F) (hT : ∀ n, MeasurableSet[𝓕 (q n)] ({ω | n ≤ M ω} ∩ T n)) :
    IsStoppingTime 𝓕 (ruleTime q M T F) := by
  intro t
  change MeasurableSet[𝓕 t] {ω | ruleTime q M T F ω ≤ (t : ℝ≥0∞)}
  have e : {ω | ruleTime q M T F ω ≤ (t : ℝ≥0∞)} =
      {ω | F ω ≤ t} ∪ ⋃ n ∈ {n | q n ≤ t}, ({ω | n ≤ M ω} ∩ T n) := by
    ext ω
    simp only [mem_ofPred_eq, mem_union, mem_iUnion, mem_inter_iff, exists_prop]
    rw [ruleTime_le_coe_iff]
    exact or_congr Iff.rfl ⟨fun ⟨n, h1, h2, h3⟩ => ⟨n, h3, h1, h2⟩, fun ⟨n, h3, h1, h2⟩ => ⟨n, h1, h2, h3⟩⟩
  rw [e]
  have hFt : MeasurableSet[𝓕 t] {ω | F ω ≤ (t : ℝ≥0∞)} := hF t
  exact hFt.union (MeasurableSet.biUnion (Set.to_countable _) fun n hn => 𝓕.mono hn _ (hT n))

/-- **The rule succeeds exactly on the selected candidate event** `E_M = ⋃_{n ≤ M} T n`, when every test event lies
before `F`. -/
theorem ruleTime_lt_iff {q : ℕ → ℝ≥0} {M : Ω → ℕ} {T : ℕ → Set Ω} {F : Ω → ℝ≥0∞}
    (hTF : ∀ n ω, ω ∈ T n → (q n : ℝ≥0∞) < F ω) (ω : Ω) :
    ruleTime q M T F ω < F ω ↔ ∃ n, n ≤ M ω ∧ ω ∈ T n := by
  unfold ruleTime
  rw [min_lt_iff]
  constructor
  · rintro (h | h)
    · exact absurd h (lt_irrefl _)
    · by_contra hno
      push Not at hno
      have hemp : {n | n ≤ M ω ∧ ω ∈ T n} = ∅ := Set.eq_empty_iff_forall_notMem.2 fun n hn => hno n hn.1 hn.2
      rw [hemp] at h
      simp only [Set.mem_empty_iff_false, iInf_false, iInf_top] at h
      exact absurd h (not_lt.2 le_top)
  · rintro ⟨n, hn, hT⟩
    exact Or.inr ((biInf_le (fun n => (q n : ℝ≥0∞))
      (show n ∈ {n | n ≤ M ω ∧ ω ∈ T n} from ⟨hn, hT⟩)).trans_lt (hTF n ω hT))

end Rule

end CS3Select

end Theorem14

end InteractingSLE
