/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.SB2NeRead
import InteractingSLE.Spec.Supplement.SB2WfPs
import InteractingSLE.Spec.Supplement.GW2TlBad
import InteractingSLE.Spec.Supplement.G12Low
import InteractingSLE.Spec.Supplement.SB2VrRad

/-!
# B's launched piece at its lifetime, in launch coordinates (almost surely)

Packet PROVE-AUX61-NOJUMP (round 22, component F). At a launch `ℓ` of the right walk (angle `θ`) with a stage witness
`β` (launch word), almost surely, at a positive finite lifetime `ζ`:

* the tip `trOf ζ` lies in the closed bad set of the launch word (`GW2Rd.badDist … = 0`; D10 step 1,
  `Vr.ae_tip_bad_of_isFlowLine`, under the stage kernel);
* no positive mark of the word of non-bad right weight is visited up to `ζ` (Lemma G12 at the frozen mark).

Both are read at rational times (`TipCl`, `MarkFree`), so they transfer from the stage kernel to `P`
(`ae_stage_tip`), as in SB2WORD's `Wf.ae_stage_avoid`.

* `RBadW`, `rBadW_iff`, `measurableSet_rBadW`: right-bad points of a word, jointly measurable;
* `TipCl`, `MarkFree` and their deterministic readings `tipCl_iff`, `markFree_iff`;
* **`ae_stage_tip`**.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology Metric
open scoped NNReal ENNReal
open QuantumZipper (H chiC)

universe u

namespace InteractingSLE.Theorem14.SB.Ne

open Exist Exist.StagedLaw Exist.Staged Restart GW1W
open PiecewiseConstantBoundaryData (rightLim leftLim)

/-! ### Right-bad points of a word -/

section Word

/-- **A right-bad point of a word** for the flow at angle `θ`. -/
def RBadW (κ θ : ℝ) (c : BoundaryWord) (y : ℝ) : Prop :=
  0 < y ∧ Sec4.cumWeightRight κ (rightLim c.fn y + θ * chiC κ) ≤ -2

theorem rightLim_eq_of_noPos {c : BoundaryWord} {y q : ℝ} (hq : y < q)
    (hno : ∀ j < c.1, ¬ (y < c.2.1 j ∧ c.2.1 j < q)) : rightLim c.fn y = c.fn q := by
  refine Sec4.rightLim_eq_of_forall (a := q) hq fun t ht => ?_
  have hidx : c.index t = c.index q :=
    Wf.index_eq_of_noPos ht.2.le fun j hj hj' => hno j hj ⟨lt_of_lt_of_le ht.1 hj'.1, hj'.2⟩
  unfold BoundaryWord.fn
  rw [hidx]

theorem rBadW_iff {κ θ : ℝ} {c : BoundaryWord} {y : ℝ} : RBadW κ θ c y ↔ 0 < y ∧ ∃ q : ℚ, y < q ∧
    (∀ j < c.1, ¬ (y < c.2.1 j ∧ c.2.1 j < q)) ∧ Sec4.cumWeightRight κ (c.fn q + θ * chiC κ) ≤ -2 := by
  constructor
  · rintro ⟨hy, hw⟩
    obtain ⟨δ, hδ, hδJ⟩ := Supp7.exists_pos_forall_notMem c.jumps y
    obtain ⟨q, hq1, hq2⟩ := exists_rat_btwn (show y < y + δ by linarith)
    have hno : ∀ j < c.1, ¬ (y < c.2.1 j ∧ c.2.1 j < q) := fun j hj hj' =>
      (hδJ _ (BoundaryWord.mem_jumps.2 ⟨j, hj, rfl⟩)).1 ⟨hj'.1, by linarith [hj'.2]⟩
    refine ⟨hy, q, hq1, hno, ?_⟩
    rw [← rightLim_eq_of_noPos hq1 hno]
    exact hw
  · rintro ⟨hy, q, hq, hno, hw⟩
    refine ⟨hy, ?_⟩
    rw [rightLim_eq_of_noPos hq hno]
    exact hw

theorem measurableSet_rBadW (κ θ : ℝ) : MeasurableSet {p : BoundaryWord × ℝ | RBadW κ θ p.1 p.2} := by
  have hno : ∀ q : ℚ, MeasurableSet {p : BoundaryWord × ℝ | ∀ j < p.1.1, ¬ (p.2 < p.1.2.1 j ∧ p.1.2.1 j < q)} := by
    intro q
    have : {p : BoundaryWord × ℝ | ∀ j < p.1.1, ¬ (p.2 < p.1.2.1 j ∧ p.1.2.1 j < q)} =
        ⋂ j : ℕ, ({p : BoundaryWord × ℝ | p.1.1 ≤ j} ∪ ({p | p.1.2.1 j ≤ p.2} ∪ {p | (q : ℝ) ≤ p.1.2.1 j})) := by
      ext p
      simp only [mem_ofPred_eq, mem_iInter, mem_union, not_and, not_lt]
      refine ⟨fun h j => ?_, fun h j hj h1 => ?_⟩
      · by_cases hj : j < p.1.1
        · by_cases h1 : p.2 < p.1.2.1 j
          · exact Or.inr (Or.inr (h j hj h1))
          · exact Or.inr (Or.inl (not_lt.1 h1))
        · exact Or.inl (not_lt.1 hj)
      · rcases h j with h' | h' | h'
        · exact absurd hj (not_lt.2 h')
        · exact absurd h1 (not_lt.2 h')
        · exact h'
    rw [this]
    refine MeasurableSet.iInter fun j => ((measurable_fst.comp measurable_fst) (measurableSet_Iic (a := j))).union
      ((measurableSet_le ((Wf.measurable_position j).comp measurable_fst) measurable_snd).union
        (measurableSet_le measurable_const ((Wf.measurable_position j).comp measurable_fst)))
  have hR : ∀ q : ℚ, Measurable fun p : BoundaryWord × ℝ => Sec4.cumWeightRight κ (p.1.fn q + θ * chiC κ) := by
    intro q
    unfold Sec4.cumWeightRight
    exact ((((Supp7.measurable_boundaryWord_fn _).comp measurable_fst).add_const _).div_const _).sub_const _
  have : {p : BoundaryWord × ℝ | RBadW κ θ p.1 p.2} = {p : BoundaryWord × ℝ | 0 < p.2} ∩
      ⋃ q : ℚ, ({p : BoundaryWord × ℝ | p.2 < q} ∩ ({p | ∀ j < p.1.1, ¬ (p.2 < p.1.2.1 j ∧ p.1.2.1 j < q)} ∩
        {p | Sec4.cumWeightRight κ (p.1.fn q + θ * chiC κ) ≤ -2})) := by
    ext p
    simp only [mem_ofPred_eq, mem_inter_iff, mem_iUnion]
    exact rBadW_iff
  rw [this]
  exact (measurableSet_lt measurable_const measurable_snd).inter (MeasurableSet.iUnion fun q =>
    (measurableSet_lt measurable_snd measurable_const).inter ((hno q).inter (measurableSet_le (hR q) measurable_const)))

end Word


/-! ### Rational readings of a continuous path -/

section Read

/-- **The path stays off a point up to `T`**, read at rational times below `T` (bounded horizons). -/
def MarkFree (Γ : ℝ≥0 → ℂ) (T : ℝ≥0∞) (m : ℂ) : Prop :=
  ∀ N : ℕ, ∃ n : ℕ, ∀ q : ℚ, (0 : ℝ) ≤ q → (((q : ℝ).toNNReal : ℝ≥0∞)) < T → (q : ℝ) ≤ N →
    (1 : ℝ) / (n + 1) ≤ ‖Γ (q : ℝ).toNNReal - m‖

theorem markFree_iff {f Γ : ℝ≥0 → ℂ} {T : ℝ≥0∞} (hT : 0 < T) (hf : ContinuousOn f {t | (t : ℝ≥0∞) ≤ T})
    (hfg : ∀ q : ℝ≥0, (q : ℝ≥0∞) < T → Γ q = f q) {m : ℂ} :
    MarkFree Γ T m ↔ ∀ t : ℝ≥0, (t : ℝ≥0∞) ≤ T → f t ≠ m := by
  set φ : ℝ≥0 → ℝ := fun t => ‖f t - m‖ with hφ
  have hφc : ContinuousOn φ {t | (t : ℝ≥0∞) ≤ T} := (hf.sub continuousOn_const).norm
  have hcl : IsClosed {t : ℝ≥0 | (t : ℝ≥0∞) ≤ T} := isClosed_le ENNReal.continuous_coe continuous_const
  have hoT : IsOpen {t : ℝ≥0 | (t : ℝ≥0∞) < T} := isOpen_lt ENNReal.continuous_coe continuous_const
  constructor
  · intro hM t ht heq
    obtain ⟨N, hN⟩ := exists_nat_gt (t : ℝ)
    obtain ⟨n, hn⟩ := hM N
    have hc0 : (0 : ℝ) < 1 / (n + 1) := by positivity
    have hSge : ∀ s : ℝ≥0, (s : ℝ≥0∞) < T → (s : ℝ) < N → (1 : ℝ) / (n + 1) ≤ φ s := by
      intro s hs1 hs2
      by_contra hlt
      rw [not_le] at hlt
      have hnhd : {t : ℝ≥0 | (t : ℝ≥0∞) ≤ T} ∈ 𝓝 s :=
        Filter.mem_of_superset (hoT.mem_nhds hs1) fun x (hx : (x : ℝ≥0∞) < T) => show (x : ℝ≥0∞) ≤ T from hx.le
      have hca : ContinuousAt φ s := (hφc s hs1.le).continuousAt hnhd
      have hU : {x : ℝ≥0 | φ x < 1 / (n + 1)} ∩ ({x : ℝ≥0 | (x : ℝ≥0∞) < T} ∩ {x : ℝ≥0 | (x : ℝ) < N}) ∈ 𝓝 s :=
        inter_mem (hca.preimage_mem_nhds (Iio_mem_nhds hlt))
          (inter_mem (hoT.mem_nhds hs1) ((isOpen_lt NNReal.continuous_coe continuous_const).mem_nhds hs2))
      obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.1 hU
      obtain ⟨q, hq1, hq2⟩ := exists_rat_btwn (show (s : ℝ) < s + ε by linarith)
      have hq0 : (0 : ℝ) ≤ q := (NNReal.coe_nonneg s).trans hq1.le
      have hmem : (q : ℝ).toNNReal ∈ ball s ε := by
        rw [mem_ball, NNReal.dist_eq, Real.coe_toNNReal _ hq0, abs_lt]
        constructor <;> linarith
      obtain ⟨h1, h2, h3⟩ := hball hmem
      have h3' : (q : ℝ) ≤ N := by
        have := h3
        simp only [mem_ofPred_eq, Real.coe_toNNReal _ hq0] at this
        exact this.le
      have := hn q hq0 h2 h3'
      rw [hfg _ h2] at this
      exact absurd this (not_le.2 h1)
    have hφt : (1 : ℝ) / (n + 1) ≤ φ t := by
      rcases ht.lt_or_eq with hlt | heqT
      · exact hSge t hlt hN
      · have ht0 : 0 < t := by
          have : (0 : ℝ≥0∞) < t := heqT ▸ hT
          exact_mod_cast this
        have : (𝓝[<] t).NeBot := nhdsLT_neBot_of_exists_lt ⟨0, ht0⟩
        have htend : Tendsto φ (𝓝[<] t) (𝓝 (φ t)) :=
          (hφc t ht).tendsto.mono_left (nhdsWithin_mono _ fun x (hx : x < t) =>
            show (x : ℝ≥0∞) ≤ T from (ENNReal.coe_le_coe.2 hx.le).trans ht)
        refine ge_of_tendsto htend ?_
        filter_upwards [self_mem_nhdsWithin] with x (hx : x < t)
        exact hSge x (by rw [← heqT]; exact_mod_cast hx) (lt_trans (by exact_mod_cast hx) hN)
    simp only [hφ, heq, sub_self, norm_zero] at hφt
    linarith
  · intro hne N
    set K : Set ℝ≥0 := Icc 0 (N : ℝ≥0) ∩ {t | (t : ℝ≥0∞) ≤ T} with hKdef
    have hK : IsCompact K := isCompact_Icc.inter_right hcl
    have hKne : K.Nonempty := ⟨0, ⟨⟨le_rfl, zero_le⟩, by simp⟩⟩
    obtain ⟨t₀, ht₀K, hmin⟩ := hK.exists_isMinOn hKne (hφc.mono inter_subset_right)
    have hpos : 0 < φ t₀ := norm_pos_iff.2 (sub_ne_zero.2 (hne t₀ ht₀K.2))
    obtain ⟨n, hn⟩ := exists_nat_one_div_lt hpos
    refine ⟨n, fun q hq0 hqT hqN => ?_⟩
    have hqK : (q : ℝ).toNNReal ∈ K := by
      refine ⟨⟨zero_le, ?_⟩, hqT.le⟩
      rw [← NNReal.coe_le_coe, Real.coe_toNNReal _ hq0]
      simpa using hqN
    rw [hfg _ hqT]
    exact hn.le.trans (hmin hqK)

/-- **The tip at `T` is in the closed bad set of `β`**, read at rational times below `T`. -/
def TipCl (κ θ : ℝ) (β : BoundaryWord) (Γ : ℝ≥0 → ℂ) (T : ℝ≥0) : Prop :=
  ∀ n : ℕ, ∃ q : ℚ, (0 : ℝ) ≤ q ∧ (q : ℝ) < T ∧ (T : ℝ) < q + 1 / (n + 1) ∧
    GW2Rd.badDist κ θ β (Γ (q : ℝ).toNNReal) < 1 / (n + 1)

theorem tipCl_iff {κ θ : ℝ} {β : BoundaryWord} {f Γ : ℝ≥0 → ℂ} {T : ℝ≥0} (hT : 0 < T)
    (hf : ContinuousOn f {t | t ≤ T}) (hfg : ∀ q : ℝ≥0, q < T → Γ q = f q) :
    TipCl κ θ β Γ T ↔ GW2Rd.badDist κ θ β (f T) = 0 := by
  set d : ℝ≥0 → ℝ := fun t => GW2Rd.badDist κ θ β (f t) with hd
  have hdc : ContinuousOn d {t | t ≤ T} := (GW2Rd.continuous_badDist β).comp_continuousOn hf
  constructor
  · intro hTC
    choose q hq0 hqT hqT' hqd using hTC
    have hlim : Tendsto (fun n => (q n : ℝ).toNNReal) atTop (𝓝 T) := by
      rw [← NNReal.tendsto_coe]
      simp only [Real.coe_toNNReal _ (hq0 _)]
      have h1 : Tendsto (fun n : ℕ => (T : ℝ) - 1 / ((n : ℝ) + 1)) atTop (𝓝 (T : ℝ)) := by
        simpa using (tendsto_one_div_add_atTop_nhds_zero_nat).const_sub (T : ℝ)
      exact tendsto_of_tendsto_of_tendsto_of_le_of_le h1 tendsto_const_nhds
        (fun n => by have := hqT' n; linarith) fun n => (hqT n).le
    have hmem : ∀ n, (q n : ℝ).toNNReal ∈ {t : ℝ≥0 | t ≤ T} := fun n => by
      show (q n : ℝ).toNNReal ≤ T
      rw [← NNReal.coe_le_coe, Real.coe_toNNReal _ (hq0 n)]
      exact (hqT n).le
    have h1 : Tendsto (fun n => d (q n : ℝ).toNNReal) atTop (𝓝 (d T)) :=
      (hdc T (show T ≤ T from le_rfl)).tendsto.comp (tendsto_nhdsWithin_iff.2 ⟨hlim, Eventually.of_forall hmem⟩)
    have hlt : ∀ n, (q n : ℝ).toNNReal < T := fun n => by
      rw [← NNReal.coe_lt_coe, Real.coe_toNNReal _ (hq0 n)]
      exact hqT n
    have h2 : Tendsto (fun n => d (q n : ℝ).toNNReal) atTop (𝓝 0) := by
      refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds tendsto_one_div_add_atTop_nhds_zero_nat
        (fun n => GW2Rd.badDist_nonneg _ _) fun n => ?_
      have := hqd n
      rw [hfg _ (hlt n)] at this
      exact this.le
    exact tendsto_nhds_unique h1 h2
  · intro hd0 n
    have hU : {t : ℝ≥0 | d t < 1 / (n + 1)} ∈ 𝓝[{t | t ≤ T}] T :=
      (hdc T (show T ≤ T from le_rfl)) (Iio_mem_nhds (by rw [hd]; simp only; rw [hd0]; positivity))
    obtain ⟨ε, hε, hball⟩ := Metric.mem_nhdsWithin_iff.1 hU
    have hm : max (max ((T : ℝ) - ε) ((T : ℝ) - 1 / (n + 1))) 0 < T := by
      refine max_lt (max_lt (by linarith) (by have : (0 : ℝ) < 1 / (n + 1) := (by positivity); linarith)) ?_
      exact_mod_cast hT
    obtain ⟨q, hq1, hq2⟩ := exists_rat_btwn hm
    have hq0 : (0 : ℝ) ≤ q := (le_max_right _ _).trans hq1.le
    have hqa : (T : ℝ) - ε < q := lt_of_le_of_lt ((le_max_left _ _).trans (le_max_left _ _)) hq1
    have hqb : (T : ℝ) - 1 / (n + 1) < q := lt_of_le_of_lt ((le_max_right _ _).trans (le_max_left _ _)) hq1
    have hqlt : (q : ℝ).toNNReal < T := by
      rw [← NNReal.coe_lt_coe, Real.coe_toNNReal _ hq0]
      exact hq2
    have hmem : (q : ℝ).toNNReal ∈ ball T ε ∩ {t : ℝ≥0 | t ≤ T} := by
      refine ⟨?_, hqlt.le⟩
      rw [mem_ball, NNReal.dist_eq, Real.coe_toNNReal _ hq0, abs_lt]
      constructor <;> linarith
    refine ⟨q, hq0, hq2, by linarith, ?_⟩
    rw [hfg _ hqlt]
    exact hball hmem

end Read


/-! ### The transfer from the stage kernel -/

section Stage

variable {κ : ℝ} {b : ℝ → ℝ} {jumps : Finset ℝ} {Ω : Type u} [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω]
  {P : Measure Ω} [IsProbabilityMeasure P] {h : Ω → LQGMetric.DistOn upperHalfPlaneOpens}
  {E : ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞}

/-- **B's launched piece at its lifetime** (almost surely, launch coordinates): at a positive finite lifetime the
tip is in the closed bad set of the launch word, and no positive non-bad mark of the word is visited up to the
lifetime. -/
theorem ae_stage_tip (hκ : 0 < κ) (hκ4 : κ < 4) (hb : IsPiecewiseConstantBoundaryData b jumps)
    (hh : IsGFFWithBoundaryData P h b jumps) {θ : ℝ}
    (hE : IsStagedHistory κ b jumps P h (boundaryWalkSpec b jumps θ true) E) (hreg : ∀ j ω, IsRegularDriver (E j ω))
    (hRS : StagedPiecesRegular κ b jumps P (boundaryWalkSpec b jumps θ true) E)
    {ℓ : ℕ} {β : Ω → BoundaryWord} {Y : Ω → LQGMetric.DistOn upperHalfPlaneOpens}
    (hW : IsStageWitness κ b jumps P h (boundaryWalkSpec b jumps θ true) E ℓ β Y) :
    ∀ᵐ ω ∂P, (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) (fun j => E j ω) (ℓ + 1)).2.2.2.1 ℓ ≠
        none → 0 < (E ℓ ω).2 →
      ((E ℓ ω).2 ≠ ⊤ → GW2Rd.badDist κ θ (β ω) (LuM.trOf (E ℓ ω) (E ℓ ω).2.toNNReal) = 0) ∧
      ∀ i, i < (β ω).1 → 0 < (β ω).2.1 i → ¬ RBadW κ θ (β ω) ((β ω).2.1 i) →
        ∀ t : ℝ≥0, (t : ℝ≥0∞) ≤ (E ℓ ω).2 → LuM.trOf (E ℓ ω) t ≠ (((β ω).2.1 i : ℝ) : ℂ) := by
  classical
  set spec := boundaryWalkSpec b jumps θ true with hspec
  have h𝒢 : pastSigma κ b jumps spec E ℓ ≤ mΩ := hE.2.1 ℓ
  have hLp := measurableSet_pastSigma_launch (κ := κ) hb spec hE.1 hreg ℓ
  have hβm : Measurable β := hW.1.mono h𝒢 le_rfl
  have hζm : Measurable fun ω => (E ℓ ω).2 := measurable_snd.comp (hE.1 ℓ)
  have hΓm : ∀ q : ℝ≥0, Measurable fun ω => LP.traceAt q (E ℓ ω).1 := fun q =>
    (LP.measurable_traceAt q).comp (measurable_fst.comp (hE.1 ℓ))
  have hPR : ∀ᵐ ω ∂P, (ExplState.run κ b jumps spec (fun j => E j ω) (ℓ + 1)).2.2.2.1 ℓ ≠ none →
      GW1P.PieceRegular (E ℓ ω).1 (E ℓ ω).2 := by
    filter_upwards [regLaunches_of_stagedPiecesRegular hRS] with ω hRLω hl
    obtain ⟨⟨c, θ'⟩, hcθ⟩ := Option.ne_none_iff_exists'.1 hl
    have := hRLω ℓ c θ' hcθ
    rwa [instrTime_walk hl, min_eq_right le_top] at this
  set Γ : Ω → ℝ≥0 → ℂ := fun ω q => LP.traceAt q (E ℓ ω).1 with hΓdef
  have hposm : ∀ i, Measurable fun ω => (β ω).2.1 i := fun i => (Wf.measurable_position i).comp hβm
  set L : Set Ω := {ω | (ExplState.run κ b jumps spec (fun j => E j ω) (ℓ + 1)).2.2.2.1 ℓ ≠ none} with hL
  set TS : Set Ω := {ω | TipCl κ θ (β ω) (Γ ω) (E ℓ ω).2.toNNReal} with hTS
  set MS : ℕ → Set Ω := fun i => {ω | MarkFree (Γ ω) (E ℓ ω).2 (((β ω).2.1 i : ℝ) : ℂ)} with hMS
  set G : Set Ω := Lᶜ ∪ ({ω | ¬ 0 < (E ℓ ω).2} ∪ (({ω | (E ℓ ω).2 = ⊤} ∪ TS) ∩
      ⋂ i : ℕ, ({ω | ¬ i < (β ω).1} ∪ ({ω | ¬ 0 < (β ω).2.1 i} ∪
        ({ω | RBadW κ θ (β ω) ((β ω).2.1 i)} ∪ MS i))))) with hGdef
  have hGm : MeasurableSet G := by
    have hTm : Measurable fun ω => (((E ℓ ω).2.toNNReal : ℝ≥0) : ℝ) :=
      measurable_coe_nnreal_real.comp (ENNReal.measurable_toNNReal.comp hζm)
    have hTip : MeasurableSet TS := by
      have : TS = ⋂ n : ℕ, ⋃ q : ℚ,
          ({_ω : Ω | (0 : ℝ) ≤ q} ∩ ({ω | (q : ℝ) < (((E ℓ ω).2.toNNReal : ℝ≥0) : ℝ)} ∩
            ({ω | (((E ℓ ω).2.toNNReal : ℝ≥0) : ℝ) < q + 1 / (n + 1)} ∩
              {ω | GW2Rd.badDist κ θ (β ω) (Γ ω (q : ℝ).toNNReal) < 1 / (n + 1)}))) := by
        ext ω
        simp only [hTS, TipCl, mem_ofPred_eq, mem_iInter, mem_iUnion, mem_inter_iff]
      rw [this]
      exact MeasurableSet.iInter fun n => MeasurableSet.iUnion fun q => (MeasurableSet.const _).inter
        ((measurableSet_lt measurable_const hTm).inter ((measurableSet_lt hTm measurable_const).inter
          (measurableSet_lt (GW2Rd.measurable_badDist_comp κ θ hβm (hΓm _)) measurable_const)))
    have hMark : ∀ i, MeasurableSet (MS i) := by
      intro i
      have : MS i = ⋂ N : ℕ, ⋃ n : ℕ, ⋂ q : ℚ,
          ({_ω : Ω | ¬ (0 : ℝ) ≤ q} ∪ ({ω | ¬ ((((q : ℝ).toNNReal : ℝ≥0∞)) < (E ℓ ω).2)} ∪
            ({_ω : Ω | ¬ (q : ℝ) ≤ N} ∪
              {ω | (1 : ℝ) / (n + 1) ≤ ‖Γ ω (q : ℝ).toNNReal - (((β ω).2.1 i : ℝ) : ℂ)‖}))) := by
        ext ω
        simp only [hMS, MarkFree, mem_ofPred_eq, mem_iInter, mem_iUnion, mem_union]
        refine ⟨fun hM N => ?_, fun hM N => ?_⟩
        · obtain ⟨n, hn⟩ := hM N
          refine ⟨n, fun q => ?_⟩
          by_cases h1 : (0 : ℝ) ≤ q
          · by_cases h2 : (((q : ℝ).toNNReal : ℝ≥0∞)) < (E ℓ ω).2
            · by_cases h3 : (q : ℝ) ≤ N
              · exact Or.inr (Or.inr (Or.inr (hn q h1 h2 h3)))
              · exact Or.inr (Or.inr (Or.inl h3))
            · exact Or.inr (Or.inl h2)
          · exact Or.inl h1
        · obtain ⟨n, hn⟩ := hM N
          refine ⟨n, fun q h1 h2 h3 => ?_⟩
          rcases hn q with h' | h' | h' | h'
          · exact absurd h1 h'
          · exact absurd h2 h'
          · exact absurd h3 h'
          · exact h'
      rw [this]
      refine MeasurableSet.iInter fun N => MeasurableSet.iUnion fun n => MeasurableSet.iInter fun q =>
        (MeasurableSet.const _).union ((measurableSet_lt measurable_const hζm).compl.union
          ((MeasurableSet.const _).union (measurableSet_le measurable_const ?_)))
      exact ((hΓm _).sub (Complex.measurable_ofReal.comp (hposm i))).norm
    have hBad : ∀ i, MeasurableSet {ω | RBadW κ θ (β ω) ((β ω).2.1 i)} := fun i =>
      (measurableSet_rBadW κ θ).preimage (hβm.prodMk (hposm i))
    have hlen : ∀ i, MeasurableSet {ω | ¬ i < (β ω).1} := fun i =>
      ((measurable_fst.comp hβm) (measurableSet_Ioi (a := i))).compl
    exact (h𝒢 _ hLp).compl.union ((measurableSet_lt measurable_const hζm).compl.union
      (((hζm (measurableSet_singleton ⊤)).union hTip).inter (MeasurableSet.iInter fun i => (hlen i).union
        ((measurableSet_lt measurable_const (hposm i)).compl.union ((hBad i).union (hMark i))))))
  have hGiff : ∀ ω, ω ∈ G ↔ (ω ∈ L → 0 < (E ℓ ω).2 → ((E ℓ ω).2 ≠ ⊤ → ω ∈ TS) ∧
      ∀ i, i < (β ω).1 → 0 < (β ω).2.1 i → ¬ RBadW κ θ (β ω) ((β ω).2.1 i) → ω ∈ MS i) := by
    intro ω
    simp only [hGdef, mem_union, mem_compl_iff, mem_inter_iff, mem_iInter, mem_ofPred_eq]
    constructor
    · rintro (h | h | ⟨h1, h2⟩) hl hz
      · exact absurd hl h
      · exact absurd hz h
      · refine ⟨fun ht => h1.resolve_left ht, fun i hi hp hnb => ?_⟩
        rcases h2 i with h' | h' | h' | h'
        · exact absurd hi h'
        · exact absurd hp h'
        · exact absurd h' hnb
        · exact h'
    · intro h
      by_cases hl : ω ∈ L
      · by_cases hz : 0 < (E ℓ ω).2
        · obtain ⟨h1, h2⟩ := h hl hz
          refine Or.inr (Or.inr ⟨?_, fun i => ?_⟩)
          · by_cases ht : (E ℓ ω).2 = ⊤
            · exact Or.inl ht
            · exact Or.inr (h1 ht)
          · by_cases hi : i < (β ω).1
            · by_cases hp : 0 < (β ω).2.1 i
              · by_cases hnb : RBadW κ θ (β ω) ((β ω).2.1 i)
                · exact Or.inr (Or.inr (Or.inl hnb))
                · exact Or.inr (Or.inr (Or.inr (h2 i hi hp hnb)))
              · exact Or.inr (Or.inl hp)
            · exact Or.inl hi
        · exact Or.inr (Or.inl hz)
      · exact Or.inl hl
  -- the readings on a regular piece
  have hread : ∀ ω, GW1P.PieceRegular (E ℓ ω).1 (E ℓ ω).2 →
      ContinuousOn (LuM.trOf (E ℓ ω)) {t | (t : ℝ≥0∞) ≤ (E ℓ ω).2} ∧
        ∀ q : ℝ≥0, (q : ℝ≥0∞) < (E ℓ ω).2 → Γ ω q = LuM.trOf (E ℓ ω) q := fun ω hP =>
    ⟨(LuM.isGeneratingTrace_trOf hP).2.1, fun q hq => LuM.traceAt_eq_trOf (hreg ℓ ω) hP hq⟩
  have htipR : ∀ ω, GW1P.PieceRegular (E ℓ ω).1 (E ℓ ω).2 → (E ℓ ω).2 ≠ ⊤ → 0 < (E ℓ ω).2 →
      (ω ∈ TS ↔ GW2Rd.badDist κ θ (β ω) (LuM.trOf (E ℓ ω) (E ℓ ω).2.toNNReal) = 0) := by
    intro ω hP htop hz
    obtain ⟨hc, hfg⟩ := hread ω hP
    have hT0 : 0 < (E ℓ ω).2.toNNReal := ENNReal.toNNReal_pos hz.ne' htop
    refine tipCl_iff hT0 (hc.mono fun t (ht : t ≤ (E ℓ ω).2.toNNReal) =>
      show (t : ℝ≥0∞) ≤ (E ℓ ω).2 from (ENNReal.coe_le_coe.2 ht).trans_eq (ENNReal.coe_toNNReal htop)) ?_
    intro q hq
    exact hfg q ((ENNReal.coe_lt_coe.2 hq).trans_eq (ENNReal.coe_toNNReal htop))
  have hGae : ∀ᵐ ω ∂P, ω ∈ G := by
    refine Sec5.Lemma56Stages.ae_of_ae_condExpKernel h𝒢 hGm ?_
    filter_upwards [Wf.ae_isFlowLineDriver_stage_gff hκ hb hh hE hreg hW,
      Sec7.Aux122Disint.ae_ae_condExpKernel_mem h𝒢 hLp, Sec7.Aux122Disint.ae_ae_condExpKernel_mem h𝒢 hLp.compl,
      Sec7.Aux122Disint.ae_ae_condExpKernel (P := P) h𝒢 hPR,
      Sec7.Lemma725RefK2.ae_ae_condExpKernel_eq_self (P := P) h𝒢 hW.1] with ω₀ hfl₀ hLK hLKc hPRK hβK
    by_cases hl₀ : (ExplState.run κ b jumps spec (fun j => E j ω₀) (ℓ + 1)).2.2.2.1 ℓ ≠ none
    swap
    · filter_upwards [hLKc hl₀] with ω hω
      exact (hGiff ω).2 fun hlω => absurd hlω hω
    obtain ⟨h', hG', hfl⟩ := hfl₀ hl₀
    rw [instrAngle_walk hl₀] at hfl
    have htr : ∀ᵐ ω ∂(condExpKernel P (pastSigma κ b jumps spec E ℓ) ω₀),
        IsGeneratingTrace (fun t => (E ℓ ω).1 t) (E ℓ ω).2 (LuM.trOf (E ℓ ω)) := by
      filter_upwards [hLK hl₀, hPRK] with ω hlω hPω using LuM.isGeneratingTrace_trOf (hPω hlω)
    have hη := GW2Rd.isFlowLine_of_driver hfl htr
    have hpc := (β ω₀).isPiecewiseConstantBoundaryData
    have htip := SB.Vr.ae_tip_bad_of_isFlowLine hη
    have hg12 : ∀ i : ℕ, ∀ᵐ ω ∂(condExpKernel P (pastSigma κ b jumps spec E ℓ) ω₀),
        0 < (β ω₀).2.1 i → ¬ RBadW κ θ (β ω₀) ((β ω₀).2.1 i) →
          ∀ t : ℝ≥0, (t : ℝ≥0∞) ≤ (E ℓ ω).2 → LuM.trOf (E ℓ ω) t ≠ (((β ω₀).2.1 i : ℝ) : ℂ) := by
      intro i
      by_cases hc : 0 < (β ω₀).2.1 i ∧ ¬ RBadW κ θ (β ω₀) ((β ω₀).2.1 i)
      · have hS : κ / 2 - 4 < Sec4.cumWeightRight κ (rightLim (β ω₀).fn ((β ω₀).2.1 i) + θ * chiC κ) := by
          have : -2 < Sec4.cumWeightRight κ (rightLim (β ω₀).fn ((β ω₀).2.1 i) + θ * chiC κ) := by
            by_contra hn
            exact hc.2 ⟨hc.1, not_lt.1 hn⟩
          linarith
        filter_upwards [(Supp7.g12FlowStatement κ hκ hκ4 (β ω₀).fn (β ω₀).jumps hpc 0 θ ((β ω₀).2.1 i) _ h'
          hG' _ _ hη).1 hc.1 hS] with ω hω _ _ using hω
      · exact Eventually.of_forall fun ω h1 h2 => absurd ⟨h1, h2⟩ hc
    filter_upwards [htip, ae_all_iff.2 hg12, hLK hl₀, hPRK, hβK] with ω htipω hg12ω hlω hPω hβω
    refine (hGiff ω).2 fun _ hz => ?_
    have hP := hPω hlω
    obtain ⟨hc, hfg⟩ := hread ω hP
    refine ⟨fun htop => ?_, fun i _ hp hnb => ?_⟩
    · have hb' := htipω hz htop
      simp only [Complex.ofReal_zero, sub_zero] at hb'
      have hcl : LuM.trOf (E ℓ ω) (E ℓ ω).2.toNNReal ∈ GW2Sdn.badSetC κ (β ω₀).fn θ 0 := by
        rw [← GW2Rd.closure_badSet_flowLine hκ hpc θ]
        exact subset_closure hb'
      exact (htipR ω hP htop hz).2 (by rw [hβω]; exact (GW2Rd.badDist_eq_zero_iff _ _).2 hcl)
    · rw [hβω] at hp hnb
      show MarkFree (Γ ω) (E ℓ ω).2 (((β ω).2.1 i : ℝ) : ℂ)
      rw [hβω]
      exact (markFree_iff hz hc hfg).2 (hg12ω i hp hnb)
  filter_upwards [hGae, hPR] with ω hGω hPω hl hz
  obtain ⟨h1, h2⟩ := (hGiff ω).1 hGω hl hz
  have hP := hPω hl
  obtain ⟨hc, hfg⟩ := hread ω hP
  exact ⟨fun htop => (htipR ω hP htop hz).1 (h1 htop),
    fun i hi hp hnb => (markFree_iff hz hc hfg).1 (h2 i hi hp hnb)⟩

end Stage

end InteractingSLE.Theorem14.SB.Ne
