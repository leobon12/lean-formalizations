/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec5.Prop59StageLaw

/-!
# Proposition 5.9's stage crossing as a sampled event

Packet PROVE-PROP59T2. Specification §5.2, proof of Proposition 5.9, p. 144: "If we use the extreme angle `−e_j π/2`,
the full-span case of Aux. lemma 22 and the boundary calculation below show that the driver reaches `e_j(2 + 1/8)`
before the trajectory hits the revealed counterflow or its continuation threshold."

For the stage law (`IsStageLaw`, comparison form) the event must be a Borel event of the rational-time samples. This
file:

* defines the sampled crossing events `crossL`, `crossR` (the absolute driver passes `∓(2 + 1/8)` strictly before the
  first contact with the far mark) and proves they are Borel;
* translates them to and from the paths (`crossL_of_path`, `path_of_crossL`, and the right versions), using
  continuity before the lifetime and compactness;
* proves the crossing **for every integrated evolution of a stage word from an admissible start**, at any offset of
  the absolute driver (`ae_cross_left_level`, from PROVE-PROP59T's `ae_stage_cross_left` and a general-level version of
  GB8's crossing from the first far contact), and by reflection for the rightward stage;
* packages both as premises of the comparison form (`compPremise_crossL`, `compPremise_crossR`).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal

namespace InteractingSLE

namespace Sec5

namespace Prop59Stage

open Supp8.GB8 Prop59Tips

/-! ### Stage words of variable size -/

/-- **A stage word of any size** (`IsStageWord` after writing the number of left marks as `m + 1`). -/
def IsStageWordN (κ : ℝ) {nL nR : ℕ} (ρL : Fin nL → ℝ) (ρR : Fin nR → ℝ) : Prop :=
  ∃ (m : ℕ) (h : nL = m + 1), IsStageWord κ (fun i : Fin (m + 1) => ρL (Fin.cast h.symm i)) ρR

/-! ### Borel sets of words -/

section Borel

variable {n : ℕ}

theorem measurableSet_forall_lt_imp {p : ℝ → ℝ → Prop} (hp : MeasurableSet {q : ℝ × ℝ | p q.1 q.2}) :
    MeasurableSet {x : Fin n → ℝ | ∀ i j, i < j → p (x i) (x j)} := by
  have e : {x : Fin n → ℝ | ∀ i j, i < j → p (x i) (x j)} =
      ⋂ i, ⋂ j, {x : Fin n → ℝ | i < j → p (x i) (x j)} := by
    ext x; simp only [mem_ofPred_eq, mem_iInter]
  rw [e]
  refine MeasurableSet.iInter fun i => MeasurableSet.iInter fun j => ?_
  by_cases hij : i < j
  · simp only [hij, true_imp_iff]
    have hm : Measurable fun x : Fin n → ℝ => (x i, x j) := (measurable_pi_apply i).prodMk (measurable_pi_apply j)
    exact hm hp
  · simp only [hij, false_imp_iff, ofPred_true, MeasurableSet.univ]

theorem measurableSet_strictAnti : MeasurableSet {x : Fin n → ℝ | StrictAnti x} :=
  measurableSet_forall_lt_imp (p := fun a b => b < a) (measurableSet_lt measurable_snd measurable_fst)

theorem measurableSet_strictMono : MeasurableSet {x : Fin n → ℝ | StrictMono x} :=
  measurableSet_forall_lt_imp (p := fun a b => a < b) (measurableSet_lt measurable_fst measurable_snd)

theorem measurableSet_isOrderedForceWord {nL nR : ℕ} :
    MeasurableSet {p : (Fin nL → ℝ) × (Fin nR → ℝ) | IsOrderedForceWord p.1 p.2} := by
  have hA : MeasurableSet {x : Fin nL → ℝ | Antitone x} := by
    have e : {x : Fin nL → ℝ | Antitone x} = {x | ∀ i j, i < j → x j ≤ x i} := by
      ext x
      simp only [mem_ofPred_eq]
      exact ⟨fun h i j hij => h hij.le, fun h i j hij => by
        rcases hij.lt_or_eq with hlt | rfl
        · exact h i j hlt
        · exact le_rfl⟩
    rw [e]
    exact measurableSet_forall_lt_imp (p := fun a b => b ≤ a) (measurableSet_le measurable_snd measurable_fst)
  have hM : MeasurableSet {x : Fin nR → ℝ | Monotone x} := by
    have e : {x : Fin nR → ℝ | Monotone x} = {x | ∀ i j, i < j → x i ≤ x j} := by
      ext x
      simp only [mem_ofPred_eq]
      exact ⟨fun h i j hij => h hij.le, fun h i j hij => by
        rcases hij.lt_or_eq with hlt | rfl
        · exact h i j hlt
        · exact le_rfl⟩
    rw [e]
    exact measurableSet_forall_lt_imp (p := fun a b => a ≤ b) (measurableSet_le measurable_fst measurable_snd)
  have hL0 : MeasurableSet {x : Fin nL → ℝ | ∀ i, x i ≤ 0} := by
    rw [ofPred_forall]
    exact MeasurableSet.iInter fun i => measurableSet_le (measurable_pi_apply i) measurable_const
  have hR0 : MeasurableSet {x : Fin nR → ℝ | ∀ i, 0 ≤ x i} := by
    rw [ofPred_forall]
    exact MeasurableSet.iInter fun i => measurableSet_le measurable_const (measurable_pi_apply i)
  exact (measurable_fst hA).inter ((measurable_fst hL0).inter ((measurable_snd hM).inter (measurable_snd hR0)))

end Borel

/-! ### The sampled crossing events -/

section Events

variable {nL nR : ℕ}

/-- **The leftward sampled crossing** (absolute level `ℓ`, far left mark `iL`): at some rational time before the
lifetime the absolute driver is below `ℓ`, and up to that time the far gap `W − V^L_{iL}` stays above a positive
rational. -/
def crossL (ℓ : ℝ) (iL : Fin nL) : Set (Start nL nR × Samp nL nR) :=
  {p | ∃ t : ℚ≥0, ((t : ℝ≥0) : ℝ≥0∞) < p.2.1 ∧ p.1.1 + (p.2.2 t).1 < ℓ ∧
    ∃ δ : ℚ, 0 < (δ : ℝ) ∧ ∀ u : ℚ≥0, u ≤ t → (δ : ℝ) ≤ (p.2.2 u).1 - (p.2.2 u).2.1 iL}

/-- **The rightward sampled crossing** (absolute level `ℓ`, far right mark `iR`). -/
def crossR (ℓ : ℝ) (iR : Fin nR) : Set (Start nL nR × Samp nL nR) :=
  {p | ∃ t : ℚ≥0, ((t : ℝ≥0) : ℝ≥0∞) < p.2.1 ∧ ℓ < p.1.1 + (p.2.2 t).1 ∧
    ∃ δ : ℚ, 0 < (δ : ℝ) ∧ ∀ u : ℚ≥0, u ≤ t → (δ : ℝ) ≤ (p.2.2 u).2.2 iR - (p.2.2 u).1}

theorem measurable_sampAt (q : ℚ≥0) :
    Measurable fun p : Start nL nR × Samp nL nR => p.2.2 q :=
  (measurable_pi_apply q).comp (measurable_snd.comp measurable_snd)

theorem measurableSet_crossL (ℓ : ℝ) (iL : Fin nL) : MeasurableSet (crossL (nR := nR) ℓ iL) := by
  have hW : ∀ q : ℚ≥0, Measurable fun p : Start nL nR × Samp nL nR => (p.2.2 q).1 := fun q =>
    measurable_fst.comp (measurable_sampAt q)
  have hV : ∀ q : ℚ≥0, Measurable fun p : Start nL nR × Samp nL nR => (p.2.2 q).2.1 iL := fun q =>
    (measurable_pi_apply iL).comp (measurable_fst.comp (measurable_snd.comp (measurable_sampAt q)))
  have e : crossL (nR := nR) ℓ iL = ⋃ t : ℚ≥0, ({p : Start nL nR × Samp nL nR | ((t : ℝ≥0) : ℝ≥0∞) < p.2.1} ∩
      {p | p.1.1 + (p.2.2 t).1 < ℓ} ∩ ⋃ δ : ℚ, ({_p : Start nL nR × Samp nL nR | 0 < (δ : ℝ)} ∩
        ⋂ u : ℚ≥0, {p | u ≤ t → (δ : ℝ) ≤ (p.2.2 u).1 - (p.2.2 u).2.1 iL})) := by
    ext p
    simp only [crossL, mem_ofPred_eq, mem_iUnion, mem_inter_iff, mem_iInter]
    constructor
    · rintro ⟨t, h1, h2, δ, h3, h4⟩; exact ⟨t, ⟨h1, h2⟩, δ, h3, h4⟩
    · rintro ⟨t, ⟨h1, h2⟩, δ, h3, h4⟩; exact ⟨t, h1, h2, δ, h3, h4⟩
  rw [e]
  refine MeasurableSet.iUnion fun t => ((measurableSet_lt measurable_const
    (measurable_fst.comp measurable_snd)).inter (measurableSet_lt
      ((measurable_fst.comp measurable_fst).add (hW t)) measurable_const)).inter
    (MeasurableSet.iUnion fun δ => (MeasurableSet.const _).inter
      (MeasurableSet.iInter fun u => ?_))
  by_cases hu : u ≤ t
  · simp only [hu, true_imp_iff]
    exact measurableSet_le measurable_const ((hW u).sub (hV u))
  · simp only [hu, false_imp_iff, ofPred_true, MeasurableSet.univ]

theorem measurableSet_crossR (ℓ : ℝ) (iR : Fin nR) : MeasurableSet (crossR (nL := nL) ℓ iR) := by
  have hW : ∀ q : ℚ≥0, Measurable fun p : Start nL nR × Samp nL nR => (p.2.2 q).1 := fun q =>
    measurable_fst.comp (measurable_sampAt q)
  have hV : ∀ q : ℚ≥0, Measurable fun p : Start nL nR × Samp nL nR => (p.2.2 q).2.2 iR := fun q =>
    (measurable_pi_apply iR).comp (measurable_snd.comp (measurable_snd.comp (measurable_sampAt q)))
  have e : crossR (nL := nL) ℓ iR = ⋃ t : ℚ≥0, ({p : Start nL nR × Samp nL nR | ((t : ℝ≥0) : ℝ≥0∞) < p.2.1} ∩
      {p | ℓ < p.1.1 + (p.2.2 t).1} ∩ ⋃ δ : ℚ, ({_p : Start nL nR × Samp nL nR | 0 < (δ : ℝ)} ∩
        ⋂ u : ℚ≥0, {p | u ≤ t → (δ : ℝ) ≤ (p.2.2 u).2.2 iR - (p.2.2 u).1})) := by
    ext p
    simp only [crossR, mem_ofPred_eq, mem_iUnion, mem_inter_iff, mem_iInter]
    constructor
    · rintro ⟨t, h1, h2, δ, h3, h4⟩; exact ⟨t, ⟨h1, h2⟩, δ, h3, h4⟩
    · rintro ⟨t, ⟨h1, h2⟩, δ, h3, h4⟩; exact ⟨t, h1, h2, δ, h3, h4⟩
  rw [e]
  refine MeasurableSet.iUnion fun t => ((measurableSet_lt measurable_const
    (measurable_fst.comp measurable_snd)).inter (measurableSet_lt measurable_const
      ((measurable_fst.comp measurable_fst).add (hW t)))).inter
    (MeasurableSet.iUnion fun δ => (MeasurableSet.const _).inter
      (MeasurableSet.iInter fun u => ?_))
  by_cases hu : u ≤ t
  · simp only [hu, true_imp_iff]
    exact measurableSet_le measurable_const ((hV u).sub (hW u))
  · simp only [hu, false_imp_iff, ofPred_true, MeasurableSet.univ]

end Events

/-! ### Paths and samples -/

section Paths

/-- A rational strictly between two nonnegative reals. -/
theorem exists_nnrat_btwn₀ {a b : ℝ≥0} (h : a < b) : ∃ q : ℚ≥0, a < (q : ℝ≥0) ∧ (q : ℝ≥0) < b := by
  obtain ⟨q, hq0, h1, h2⟩ := (NNReal.lt_iff_exists_rat_btwn a b).1 h
  have e : ((q.toNNRat : ℚ≥0) : ℝ≥0) = Real.toNNReal q := by
    ext
    rw [Real.coe_toNNReal _ (Rat.cast_nonneg.2 hq0)]
    have h3 : (((q.toNNRat : ℚ≥0) : ℝ≥0) : ℝ) = ((q.toNNRat : ℚ) : ℝ) := by norm_cast
    rw [h3, Rat.coe_toNNRat q hq0]
  exact ⟨q.toNNRat, by rw [e]; exact h1, by rw [e]; exact h2⟩

/-- A real time before a lifetime is approximated from below by rationals (the time itself if `0`). -/
theorem exists_rat_le_near {f : ℝ≥0 → ℝ} {t : ℝ≥0} {ζ : ℝ≥0∞} (ht : (t : ℝ≥0∞) < ζ)
    (hf : ContinuousOn f {s | (s : ℝ≥0∞) < ζ}) {ℓ : ℝ} (hft : f t < ℓ) :
    ∃ q : ℚ≥0, (q : ℝ≥0) ≤ t ∧ f q < ℓ := by
  have hc : ContinuousAt f t := hf.continuousAt ((isOpen_lt ENNReal.continuous_coe continuous_const).mem_nhds ht)
  have hev : ∀ᶠ s in 𝓝 t, f s < ℓ := hc.eventually (gt_mem_nhds hft)
  rcases eq_or_lt_of_le (zero_le : (0 : ℝ≥0) ≤ t) with h0 | hpos
  · subst h0
    exact ⟨0, by simp, by simpa using hft⟩
  · have hU : {s | f s < ℓ} ∈ 𝓝[<] t := nhdsWithin_le_nhds hev
    obtain ⟨c, hc, hsub⟩ := (mem_nhdsLT_iff_exists_Ioo_subset' hpos).1 hU
    obtain ⟨q, hq1, hq2⟩ := exists_nnrat_btwn₀ (show c < t from hc)
    exact ⟨q, hq2.le, hsub ⟨hq1, hq2⟩⟩

/-- A positive continuous function on `[0, t]` has a positive rational lower bound there. -/
theorem exists_rat_lower {g : ℝ≥0 → ℝ} {t : ℝ≥0} (hg : ContinuousOn g (Icc 0 t))
    (hpos : ∀ u ≤ t, 0 < g u) : ∃ δ : ℚ, 0 < (δ : ℝ) ∧ ∀ u ≤ t, (δ : ℝ) ≤ g u := by
  obtain ⟨u₀, hu₀, hmin⟩ := (isCompact_Icc : IsCompact (Icc (0 : ℝ≥0) t)).exists_isMinOn
    (nonempty_Icc.2 (zero_le : (0 : ℝ≥0) ≤ t)) hg
  obtain ⟨δ, hδ0, hδ⟩ := exists_rat_btwn (hpos u₀ hu₀.2)
  exact ⟨δ, hδ0, fun u hu => hδ.le.trans (hmin ⟨zero_le, hu⟩)⟩

variable {nL nR : ℕ}

/-- **Path to samples (left)**: a real crossing of the relative level `ℓ − a` strictly before the first far contact
gives the sampled crossing. -/
theorem crossL_of_path {a ℓ : ℝ} {w : ℝ≥0 → ℝ} {vL : Fin nL → ℝ≥0 → ℝ} {vR : Fin nR → ℝ≥0 → ℝ} {ζ : ℝ≥0∞}
    {x : (Fin nL → ℝ) × (Fin nR → ℝ)} {iL : Fin nL} (hw : ContinuousOn w {s | (s : ℝ≥0∞) < ζ})
    (hv : ContinuousOn (vL iL) {s | (s : ℝ≥0∞) < ζ}) {t : ℝ≥0} (ht : (t : ℝ≥0∞) < ζ) (hwt : a + w t < ℓ)
    (hgap : ∀ u ≤ t, vL iL u < w u) : ((a, x), samp w vL vR ζ) ∈ crossL ℓ iL := by
  obtain ⟨q, hqt, hq⟩ := exists_rat_le_near (f := fun s => a + w s) ht (continuousOn_const.add hw) hwt
  have hqζ : ((q : ℝ≥0) : ℝ≥0∞) < ζ := lt_of_le_of_lt (by exact_mod_cast hqt) ht
  have hsub : Icc (0 : ℝ≥0) q ⊆ {s | (s : ℝ≥0∞) < ζ} := fun s hs =>
    lt_of_le_of_lt (by exact_mod_cast hs.2) hqζ
  obtain ⟨δ, hδ0, hδ⟩ := exists_rat_lower (g := fun s => w s - vL iL s) (t := q)
    ((hw.mono hsub).sub (hv.mono hsub)) fun u hu => sub_pos.2 (hgap u (hu.trans hqt))
  refine ⟨q, hqζ, ?_, δ, hδ0, fun u hu => ?_⟩
  · rw [samp_snd_of_lt _ _ _ hqζ]; exact hq
  · have huζ : ((u : ℝ≥0) : ℝ≥0∞) < ζ := lt_of_le_of_lt (by exact_mod_cast hu) hqζ
    rw [samp_snd_of_lt _ _ _ huζ]
    exact hδ u (by exact_mod_cast hu)

/-- **Path to samples (right).** -/
theorem crossR_of_path {a ℓ : ℝ} {w : ℝ≥0 → ℝ} {vL : Fin nL → ℝ≥0 → ℝ} {vR : Fin nR → ℝ≥0 → ℝ} {ζ : ℝ≥0∞}
    {x : (Fin nL → ℝ) × (Fin nR → ℝ)} {iR : Fin nR} (hw : ContinuousOn w {s | (s : ℝ≥0∞) < ζ})
    (hv : ContinuousOn (vR iR) {s | (s : ℝ≥0∞) < ζ}) {t : ℝ≥0} (ht : (t : ℝ≥0∞) < ζ) (hwt : ℓ < a + w t)
    (hgap : ∀ u ≤ t, w u < vR iR u) : ((a, x), samp w vL vR ζ) ∈ crossR ℓ iR := by
  obtain ⟨q, hqt, hq⟩ := exists_rat_le_near (f := fun s => -(a + w s)) ht (continuousOn_const.add hw).neg
    (neg_lt_neg hwt)
  have hqζ : ((q : ℝ≥0) : ℝ≥0∞) < ζ := lt_of_le_of_lt (by exact_mod_cast hqt) ht
  have hsub : Icc (0 : ℝ≥0) q ⊆ {s | (s : ℝ≥0∞) < ζ} := fun s hs =>
    lt_of_le_of_lt (by exact_mod_cast hs.2) hqζ
  obtain ⟨δ, hδ0, hδ⟩ := exists_rat_lower (g := fun s => vR iR s - w s) (t := q)
    ((hv.mono hsub).sub (hw.mono hsub)) fun u hu => sub_pos.2 (hgap u (hu.trans hqt))
  refine ⟨q, hqζ, ?_, δ, hδ0, fun u hu => ?_⟩
  · rw [samp_snd_of_lt _ _ _ hqζ]; simp only at hq ⊢; linarith
  · have huζ : ((u : ℝ≥0) : ℝ≥0∞) < ζ := lt_of_le_of_lt (by exact_mod_cast hu) hqζ
    rw [samp_snd_of_lt _ _ _ huζ]
    exact hδ u (by exact_mod_cast hu)

/-- A continuous function on `[0, t]` that is at least `δ` at the rational points of `[0, t]` is at least `δ` on
`[0, t]`. -/
theorem le_of_le_rat {g : ℝ≥0 → ℝ} {t : ℝ≥0} (hg : ContinuousOn g (Icc 0 t)) {δ : ℝ}
    (h : ∀ u : ℚ≥0, (u : ℝ≥0) ≤ t → δ ≤ g u) : ∀ u ≤ t, δ ≤ g u := by
  intro u hu
  by_contra hlt
  push Not at hlt
  have hev : ∀ᶠ s in 𝓝[Icc 0 t] u, g s < δ :=
    (hg u ⟨zero_le, hu⟩).eventually (gt_mem_nhds hlt)
  obtain ⟨V, hV, hVsub⟩ := mem_nhdsWithin_iff_exists_mem_nhds_inter.1 hev
  rcases eq_or_lt_of_le hu with heq | hut
  · subst heq
    rcases eq_or_lt_of_le (zero_le : (0 : ℝ≥0) ≤ u) with h0 | hpos
    · subst h0
      have := h 0 (by simp)
      simp only [NNRat.cast_zero] at this
      linarith
    · obtain ⟨l, hl, hlsub⟩ := exists_Ioc_subset_of_mem_nhds hV ⟨0, hpos⟩
      obtain ⟨q, hq1, hq2⟩ := exists_nnrat_btwn₀ hl
      have hqV : (q : ℝ≥0) ∈ V ∩ Icc 0 u := ⟨hlsub ⟨hq1, hq2.le⟩, zero_le, hq2.le⟩
      have := h q hq2.le
      have := hVsub hqV
      simp only [mem_ofPred_eq] at this
      linarith
  · obtain ⟨c, hc, hcsub⟩ := exists_Ico_subset_of_mem_nhds hV (show ∃ c, u < c from ⟨t, hut⟩)
    obtain ⟨q, hq1, hq2⟩ := exists_nnrat_btwn₀ (show u < min c t from lt_min hc hut)
    have hqt : (q : ℝ≥0) ≤ t := hq2.le.trans (min_le_right _ _)
    have hqV : (q : ℝ≥0) ∈ V ∩ Icc 0 t :=
      ⟨hcsub ⟨hq1.le, hq2.trans_le (min_le_left _ _)⟩, zero_le, hqt⟩
    have := h q hqt
    have := hVsub hqV
    simp only [mem_ofPred_eq] at this
    linarith

/-- **Samples to path (left)**: the sampled crossing gives a real time before the lifetime at which the absolute driver
is below `ℓ`, with the far gap positive up to it. -/
theorem path_of_crossL {a ℓ : ℝ} {w : ℝ≥0 → ℝ} {vL : Fin nL → ℝ≥0 → ℝ} {vR : Fin nR → ℝ≥0 → ℝ} {ζ : ℝ≥0∞}
    {x : (Fin nL → ℝ) × (Fin nR → ℝ)} {iL : Fin nL} (hw : ContinuousOn w {s | (s : ℝ≥0∞) < ζ})
    (hv : ContinuousOn (vL iL) {s | (s : ℝ≥0∞) < ζ}) (h : ((a, x), samp w vL vR ζ) ∈ crossL ℓ iL) :
    ∃ t : ℝ≥0, (t : ℝ≥0∞) < ζ ∧ a + w t < ℓ ∧ ∀ u ≤ t, vL iL u < w u := by
  obtain ⟨q, hqζ, hq, δ, hδ0, hδ⟩ := h
  change ((q : ℝ≥0) : ℝ≥0∞) < ζ at hqζ
  change a + ((samp w vL vR ζ).2 q).1 < ℓ at hq
  change ∀ u : ℚ≥0, u ≤ q → (δ : ℝ) ≤ ((samp w vL vR ζ).2 u).1 - ((samp w vL vR ζ).2 u).2.1 iL at hδ
  have hsub : Icc (0 : ℝ≥0) q ⊆ {s | (s : ℝ≥0∞) < ζ} := fun s hs =>
    lt_of_le_of_lt (by exact_mod_cast hs.2) hqζ
  have hle := le_of_le_rat (g := fun s => w s - vL iL s) (t := q) ((hw.mono hsub).sub (hv.mono hsub))
    (δ := δ) fun u hu => by
      have huζ : ((u : ℝ≥0) : ℝ≥0∞) < ζ := lt_of_le_of_lt (by exact_mod_cast hu) hqζ
      have := hδ u (by exact_mod_cast hu)
      rwa [samp_snd_of_lt _ _ _ huζ] at this
  refine ⟨q, hqζ, ?_, fun u hu => ?_⟩
  · rwa [samp_snd_of_lt _ _ _ hqζ] at hq
  · have := hle u hu; linarith

/-- **Samples to path (right).** -/
theorem path_of_crossR {a ℓ : ℝ} {w : ℝ≥0 → ℝ} {vL : Fin nL → ℝ≥0 → ℝ} {vR : Fin nR → ℝ≥0 → ℝ} {ζ : ℝ≥0∞}
    {x : (Fin nL → ℝ) × (Fin nR → ℝ)} {iR : Fin nR} (hw : ContinuousOn w {s | (s : ℝ≥0∞) < ζ})
    (hv : ContinuousOn (vR iR) {s | (s : ℝ≥0∞) < ζ}) (h : ((a, x), samp w vL vR ζ) ∈ crossR ℓ iR) :
    ∃ t : ℝ≥0, (t : ℝ≥0∞) < ζ ∧ ℓ < a + w t ∧ ∀ u ≤ t, w u < vR iR u := by
  obtain ⟨q, hqζ, hq, δ, hδ0, hδ⟩ := h
  change ((q : ℝ≥0) : ℝ≥0∞) < ζ at hqζ
  change ℓ < a + ((samp w vL vR ζ).2 q).1 at hq
  change ∀ u : ℚ≥0, u ≤ q → (δ : ℝ) ≤ ((samp w vL vR ζ).2 u).2.2 iR - ((samp w vL vR ζ).2 u).1 at hδ
  have hsub : Icc (0 : ℝ≥0) q ⊆ {s | (s : ℝ≥0∞) < ζ} := fun s hs =>
    lt_of_le_of_lt (by exact_mod_cast hs.2) hqζ
  have hle := le_of_le_rat (g := fun s => vR iR s - w s) (t := q) ((hv.mono hsub).sub (hw.mono hsub))
    (δ := δ) fun u hu => by
      have huζ : ((u : ℝ≥0) : ℝ≥0∞) < ζ := lt_of_le_of_lt (by exact_mod_cast hu) hqζ
      have := hδ u (by exact_mod_cast hu)
      rwa [samp_snd_of_lt _ _ _ huζ] at this
  refine ⟨q, hqζ, ?_, fun u hu => ?_⟩
  · rwa [samp_snd_of_lt _ _ _ hqζ] at hq
  · have := hle u hu; linarith

end Paths

/-! ### The crossing for every evolution of a stage word -/

section Premise

/-- **GB8's crossing at a general level**: before the first far-left contact `τ` of a label starting at `x_m < ℓ`, the
driver crosses `ℓ` (strictly before the contact and the lifetime). -/
theorem exists_crossing_of_contact_level {w vl : ℝ≥0 → ℝ} {ζ : ℝ≥0∞}
    (hw : ContinuousOn w {t | (t : ℝ≥0∞) < ζ}) (hvl : ∀ s t : ℝ≥0, s ≤ t → (t : ℝ≥0∞) < ζ → vl t ≤ vl s)
    {xm ℓ : ℝ} (hvl0 : vl 0 = xm) (hxm : xm < ℓ) {τ : ℝ≥0} (hτ : IsFirstFarContact w vl ζ τ) :
    ∃ t : ℝ≥0, (t : ℝ≥0∞) < ζ ∧ w t < ℓ ∧ ∀ u ≤ t, vl u < w u := by
  obtain ⟨hτ0, hbefore, hcon⟩ := hτ
  have hlt : ∀ u : ℝ≥0, u < τ → (u : ℝ≥0∞) < ζ := fun u hu => by
    rcases hcon with ⟨hτζ, -⟩ | ⟨hτζ, -⟩
    · exact lt_trans (by exact_mod_cast hu) hτζ
    · rw [← hτζ]; exact_mod_cast hu
  have hne : (𝓝[<] τ).NeBot := nhdsLT_neBot_of_exists_lt ⟨0, hτ0⟩
  have hev : ∀ᶠ u in 𝓝[<] τ, w u < ℓ := by
    rcases hcon with ⟨hτζ, heq⟩ | ⟨-, h⟩
    · have hc : ContinuousAt w τ :=
        hw.continuousAt ((isOpen_lt ENNReal.continuous_coe continuous_const).mem_nhds hτζ)
      have hwτ : w τ < ℓ := by
        have := hvl 0 τ bot_le hτζ
        rw [hvl0] at this
        linarith
      exact (hc.eventually (gt_mem_nhds hwτ)).filter_mono nhdsWithin_le_nhds
    · filter_upwards [h.eventually (gt_mem_nhds (show (0 : ℝ) < ℓ - xm by linarith)), self_mem_nhdsWithin]
        with u hu hut
      have := hvl 0 u bot_le (hlt u hut)
      rw [hvl0] at this
      linarith
  obtain ⟨t, ht, htτ⟩ := (hev.and self_mem_nhdsWithin).exists
  exact ⟨t, hlt t htτ, ht, fun u hu => hbefore u (lt_of_le_of_lt hu htτ)⟩

variable {κ : ℝ} {nL nR : ℕ}

/-- The far left index `nL − 1`. -/
def farL (hnL : 0 < nL) : Fin nL := ⟨nL - 1, Nat.sub_lt hnL one_pos⟩

/-- The far right index `nR − 1`. -/
def farR (hnR : 0 < nR) : Fin nR := ⟨nR - 1, Nat.sub_lt hnR one_pos⟩

/-- **The admissible starts of a leftward stage**: an ordered force word with distinct positions on each side, the
far left mark at absolute position at most `−3` and strictly left of the driver, the far right mark strictly right. -/
def startsL (hnL : 0 < nL) (hnR : 0 < nR) : Set (Start nL nR) :=
  {y | IsOrderedForceWord y.2.1 y.2.2 ∧ StrictAnti y.2.1 ∧ StrictMono y.2.2 ∧ y.1 + y.2.1 (farL hnL) ≤ -3 ∧
    y.2.1 (farL hnL) < 0 ∧ 0 < y.2.2 (farR hnR)}

/-- **The admissible starts of a rightward stage**: the mirror image (far right mark at absolute position at least
`3`). -/
def startsR (hnL : 0 < nL) (hnR : 0 < nR) : Set (Start nL nR) :=
  {y | IsOrderedForceWord y.2.1 y.2.2 ∧ StrictAnti y.2.1 ∧ StrictMono y.2.2 ∧ 3 ≤ y.1 + y.2.2 (farR hnR) ∧
    y.2.1 (farL hnL) < 0 ∧ 0 < y.2.2 (farR hnR)}

theorem measurableSet_startsL (hnL : 0 < nL) (hnR : 0 < nR) : MeasurableSet (startsL hnL hnR) := by
  have h1 : Measurable fun y : Start nL nR => (y.2.1, y.2.2) := measurable_snd
  have hW : Measurable fun y : Start nL nR => y.2.1 := measurable_fst.comp measurable_snd
  have hV : Measurable fun y : Start nL nR => y.2.2 := measurable_snd.comp measurable_snd
  exact (h1 measurableSet_isOrderedForceWord).inter ((hW measurableSet_strictAnti).inter
    ((hV measurableSet_strictMono).inter ((measurableSet_le (measurable_fst.add
      ((measurable_pi_apply _).comp hW)) measurable_const).inter
      ((measurableSet_lt ((measurable_pi_apply _).comp hW) measurable_const).inter
        (measurableSet_lt measurable_const ((measurable_pi_apply _).comp hV))))))

theorem measurableSet_startsR (hnL : 0 < nL) (hnR : 0 < nR) : MeasurableSet (startsR hnL hnR) := by
  have h1 : Measurable fun y : Start nL nR => (y.2.1, y.2.2) := measurable_snd
  have hW : Measurable fun y : Start nL nR => y.2.1 := measurable_fst.comp measurable_snd
  have hV : Measurable fun y : Start nL nR => y.2.2 := measurable_snd.comp measurable_snd
  exact (h1 measurableSet_isOrderedForceWord).inter ((hW measurableSet_strictAnti).inter
    ((hV measurableSet_strictMono).inter ((measurableSet_le measurable_const (measurable_fst.add
      ((measurable_pi_apply _).comp hV))).inter
      ((measurableSet_lt ((measurable_pi_apply _).comp hW) measurable_const).inter
        (measurableSet_lt measurable_const ((measurable_pi_apply _).comp hV))))))

/-- An almost sure event has probability one (no measurability needed). -/
theorem one_le_measure_of_ae {Ω' : Type*} {m : MeasurableSpace Ω'} {P' : Measure Ω'} [IsProbabilityMeasure P']
    {E : Set Ω'} (h : ∀ᵐ ω ∂P', ω ∈ E) : 1 ≤ P' E := by
  have h0 : P' Eᶜ = 0 := measure_mono_null (fun ω hω => hω) (ae_iff.1 h)
  calc (1 : ℝ≥0∞) = P' univ := measure_univ.symm
    _ = P' (E ∪ Eᶜ) := by rw [union_compl_self]
    _ ≤ P' E + P' Eᶜ := measure_union_le _ _
    _ = P' E := by rw [h0, add_zero]

/-- **The leftward crossing premise**: every integrated evolution of a stage word from an admissible start
(`startsL`), with an almost surely existing trace, crosses the absolute level `−(2 + 1/8)` before its first far-left
contact almost surely (PROVE-PROP59T's `ae_stage_cross_left`, i.e. Aux. lemma 22 full span). -/
theorem compPremise_crossL (hκ : 0 < κ) (hκ4 : κ < 4) (hnL : 0 < nL) (hnR : 0 < nR) {ρL : Fin nL → ℝ}
    {ρR : Fin nR → ℝ} (hw : IsStageWordN κ ρL ρR) :
    CompPremise κ ρL ρR (startsL hnL hnR) (crossL (-(2 + 1 / 8)) (farL hnL)) 1 := by
  intro y₀ hy Ω' mΩ' P' _ 𝓕' W' VL' VR' B' ζ' hE htr
  obtain ⟨m, hm, hw'⟩ := hw
  subst hm
  have hw'' : IsStageWord κ ρL ρR := by
    have e : (fun i : Fin (m + 1) => ρL (Fin.cast rfl i)) = ρL := funext fun i => rfl
    rw [e] at hw'; exact hw'
  obtain ⟨hF, hxL, hxR, hfar, hxm, hxp⟩ := hy
  have hlast : farL hnL = Fin.last m := last_eq_mk m hnL
  rw [hlast] at hfar hxm
  have h8 := ae_stage_cross_left hκ hκ4 hnR hE hF hxL hxR hxm hxp hw'' htr
  refine one_le_measure_of_ae ?_
  filter_upwards [h8, hE.2.2.2.2] with ω hω hp
  obtain ⟨⟨τ, hτ, -⟩, -, -⟩ := hω
  have hfp := hp.isForcePath
  obtain ⟨t, htζ, hwt, hgap⟩ := exists_crossing_of_contact_level (ℓ := -(2 + 1 / 8) - y₀.1)
    hfp.continuousOn_w (fun s t hst ht => hfp.vL_le_of_le hst ht (Fin.last m)) (hfp.vL_zero (Fin.last m))
    (by linarith) hτ
  show (y₀, samp (W' · ω) (fun i t => VL' i t ω) (fun k t => VR' k t ω) (ζ' ω)) ∈ _
  rw [hlast]
  exact crossL_of_path (x := y₀.2) hfp.continuousOn_w (hfp.continuousOn_vL (Fin.last m)) htζ
    (by linarith) hgap

/-- **The rightward crossing premise** (by reflection): every integrated evolution whose reflected word is a stage
word, from an admissible start (`startsR`), crosses the absolute level `2 + 1/8` before its first far-right contact
almost surely. -/
theorem compPremise_crossR (hκ : 0 < κ) (hκ4 : κ < 4) (hnL : 0 < nL) (hnR : 0 < nR) {ρL : Fin nL → ℝ}
    {ρR : Fin nR → ℝ} (hw : IsStageWordN κ ρR ρL) :
    CompPremise κ ρL ρR (startsR hnL hnR) (crossR (2 + 1 / 8) (farR hnR)) 1 := by
  intro y₀ hy Ω' mΩ' P' _ 𝓕' W' VL' VR' B' ζ' hE htr
  obtain ⟨m, hm, hw'⟩ := hw
  subst hm
  have hw'' : IsStageWord κ ρR ρL := by
    have e : (fun i : Fin (m + 1) => ρR (Fin.cast rfl i)) = ρR := funext fun i => rfl
    rw [e] at hw'; exact hw'
  obtain ⟨hF, hxL, hxR, hfar, hxm, hxp⟩ := hy
  have hlast : farR hnR = Fin.last m := last_eq_mk m hnR
  rw [hlast] at hfar hxp
  have hEr := IsIntegratedSLEEvolution.reflect hE
  have htr' : ∀ᵐ ω ∂P', ∃ γ : ℝ≥0 → ℂ, IsGeneratingTrace (fun t => (-W') t ω) (ζ' ω) γ := by
    filter_upwards [htr] with ω ⟨γ, hγ⟩
    exact ⟨fun t => LP.reflectC (γ t), LP.isGeneratingTrace_reflect hγ⟩
  have hxm' : (-y₀.2.2) (Fin.last m) < 0 := by simp only [Pi.neg_apply]; linarith
  have hxp' : 0 < (-y₀.2.1) (farL hnL) := by simp only [Pi.neg_apply]; linarith
  have h8 := ae_stage_cross_left hκ hκ4 hnL hEr (Theorem14.CS3Cross.isOrderedForceWord_reflect hF)
    (fun a b hab => neg_lt_neg (hxR hab)) (fun a b hab => neg_lt_neg (hxL hab)) hxm' hxp' hw'' htr'
  refine one_le_measure_of_ae ?_
  filter_upwards [h8, hEr.2.2.2.2, hE.2.2.2.2] with ω hω hpr hp
  obtain ⟨⟨τ, hτ, -⟩, -, -⟩ := hω
  have hfr := hpr.isForcePath
  obtain ⟨t, htζ, hwt, hgap⟩ := exists_crossing_of_contact_level (ℓ := y₀.1 - (2 + 1 / 8))
    hfr.continuousOn_w (fun s t hst ht => hfr.vL_le_of_le hst ht (Fin.last m)) (hfr.vL_zero (Fin.last m))
    (by simp only [Pi.neg_apply]; linarith) hτ
  have hfp := hp.isForcePath
  show (y₀, samp (W' · ω) (fun i t => VL' i t ω) (fun k t => VR' k t ω) (ζ' ω)) ∈ _
  rw [hlast]
  refine crossR_of_path (x := y₀.2) hfp.continuousOn_w (hfp.continuousOn_vR (Fin.last m)) htζ ?_ fun u hu => ?_
  · simp only [Pi.neg_apply] at hwt; linarith
  · have := hgap u hu; simp only [Pi.neg_apply] at this; linarith

end Premise

end Prop59Stage

end Sec5

end InteractingSLE
