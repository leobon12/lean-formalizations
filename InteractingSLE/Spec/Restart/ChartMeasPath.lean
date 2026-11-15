/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Restart.ChartMeasLift
import InteractingSLE.Frozen.Spec.IsFirstContact

/-!
# Measurable events of continuous paths: hits, contacts, first-contact times

Packet PROVE-RESTART-CPL4. For paths `f ω` that are continuous on a closed time interval `[0, c ω]` (on a measurable
event `G`) and measurable at every fixed time, the events "`f ω([0, c ω])` meets a closed set" and "`f₁ ω([0, c₁ ω])`
meets `f₂ ω([0, c₂ ω])`" are measurable: by compactness and continuity they are countable conditions at dyadic times
(`exists_mem_iff_dyTime`, `infDist_image_lt_iff`). Consequently the first-contact times of two paths
(`IsFirstContact`) are measurable when the first contact exists on `G` (`measurable_fcTime₁`), and a path evaluated
at a measurable random time is measurable (`measurable_piecewise_eval`).

## Main results

* `dyTime`, `dyFloor`, `exists_dyTime_dist_lt`;
* `exists_mem_iff_dyTime`, `infDist_image_lt_iff`;
* `capT`, `le_capT_iff`;
* `measurableSet_inter_exists_mem`, `measurableSet_inter_exists_eq`;
* `fcPair`, `measurable_piecewise_fcTime₁`, `measurable_piecewise_fcTime₂`;
* `measurable_piecewise_eval`.
-/

set_option autoImplicit false

noncomputable section

open Complex Set Metric Filter Topology MeasureTheory
open scoped NNReal ENNReal

namespace InteractingSLE

namespace Restart

/-! ### Dyadic times -/

/-- The dyadic time `k / 2ʲ`. -/
def dyTime (j k : ℕ) : ℝ≥0 := (k : ℝ≥0) / 2 ^ j

/-- The level-`j` dyadic time below `x`. -/
def dyFloor (j : ℕ) (x : ℝ≥0) : ℝ≥0 := dyTime j ⌊(2 : ℝ) ^ j * (x : ℝ)⌋₊

theorem coe_dyFloor (j : ℕ) (x : ℝ≥0) : (dyFloor j x : ℝ) = (⌊(2 : ℝ) ^ j * (x : ℝ)⌋₊ : ℝ) / 2 ^ j := by
  simp [dyFloor, dyTime]

theorem dyFloor_le (j : ℕ) (x : ℝ≥0) : dyFloor j x ≤ x := by
  rw [← NNReal.coe_le_coe, coe_dyFloor, div_le_iff₀ (by positivity), mul_comm]
  exact Nat.floor_le (by positivity)

theorem sub_dyFloor_lt (j : ℕ) (x : ℝ≥0) : (x : ℝ) - dyFloor j x < 1 / 2 ^ j := by
  rw [coe_dyFloor]
  have hp : (0 : ℝ) < 2 ^ j := by positivity
  have h := Nat.lt_floor_add_one ((2 : ℝ) ^ j * (x : ℝ))
  rw [sub_lt_iff_lt_add, ← add_div, lt_div_iff₀ hp]
  linarith

theorem dist_dyFloor_lt (j : ℕ) (x : ℝ≥0) : dist (dyFloor j x) x < 1 / 2 ^ j := by
  rw [NNReal.dist_eq, abs_sub_comm, abs_of_nonneg (by linarith [NNReal.coe_le_coe.2 (dyFloor_le j x)])]
  exact sub_dyFloor_lt j x

theorem exists_one_div_pow_lt {δ : ℝ} (hδ : 0 < δ) : ∃ j : ℕ, 1 / (2 : ℝ) ^ j < δ := by
  obtain ⟨j, hj⟩ := exists_pow_lt_of_lt_one hδ (show (1 / 2 : ℝ) < 1 by norm_num)
  exact ⟨j, by rwa [one_div_pow] at hj⟩

theorem tendsto_dyFloor (x : ℝ≥0) : Tendsto (fun j => dyFloor j x) atTop (𝓝 x) := by
  refine tendsto_iff_dist_tendsto_zero.2 (squeeze_zero (fun j => dist_nonneg) (fun j => (dist_dyFloor_lt j x).le) ?_)
  simp_rw [one_div, ← inv_pow]
  exact tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)

/-- Values of a path continuous on `[0, c]` at times `s ≤ c` are approximated by values at dyadic times below `s`. -/
theorem exists_dyTime_dist_lt {f : ℝ≥0 → ℂ} {c : ℝ≥0} (hf : ContinuousOn f (Iic c)) {s : ℝ≥0} (hs : s ≤ c)
    {ε : ℝ} (hε : 0 < ε) : ∃ j k, dyTime j k ≤ s ∧ dist (f (dyTime j k)) (f s) < ε := by
  obtain ⟨δ, hδ, hδf⟩ := Metric.continuousWithinAt_iff.1 (hf s hs) ε hε
  obtain ⟨j, hj⟩ := exists_one_div_pow_lt hδ
  exact ⟨j, _, dyFloor_le j s, hδf ((dyFloor_le j s).trans hs) ((dist_dyFloor_lt j s).trans hj)⟩

/-! ### Hits of closed sets and contacts at dyadic times -/

theorem isCompact_Iic_nnreal (c : ℝ≥0) : IsCompact (Iic c) := by
  rw [← Set.Icc_bot]; exact isCompact_Icc

/-- **Hitting a closed set is a countable condition**: a path continuous on `[0, c]` hits the nonempty closed set `Q`
iff dyadic times `≤ c` come arbitrarily close to `Q`. -/
theorem exists_mem_iff_dyTime {f : ℝ≥0 → ℂ} {c : ℝ≥0} (hf : ContinuousOn f (Iic c)) {Q : Set ℂ}
    (hQ : IsClosed Q) (hQne : Q.Nonempty) :
    (∃ s ≤ c, f s ∈ Q) ↔ ∀ m : ℕ, ∃ j k, dyTime j k ≤ c ∧ infDist (f (dyTime j k)) Q < 1 / ((m : ℝ) + 1) := by
  constructor
  · rintro ⟨s, hs, hsQ⟩ m
    obtain ⟨j, k, hjk, hd⟩ := exists_dyTime_dist_lt hf hs (show (0 : ℝ) < 1 / ((m : ℝ) + 1) by positivity)
    exact ⟨j, k, hjk.trans hs, (infDist_le_dist_of_mem hsQ).trans_lt hd⟩
  · intro h
    by_contra hno
    push Not at hno
    have hcpt : IsCompact (f '' Iic c) := (isCompact_Iic_nnreal _).image_of_continuousOn hf
    obtain ⟨y, ⟨s₀, hs₀, rfl⟩, hmin⟩ := hcpt.exists_isMinOn ⟨f 0, 0, mem_Iic.2 zero_le, rfl⟩
      (continuous_infDist_pt Q).continuousOn
    have hδ : 0 < infDist (f s₀) Q := (hQ.notMem_iff_infDist_pos hQne).1 (hno s₀ hs₀)
    obtain ⟨m, hm⟩ := exists_nat_one_div_lt hδ
    obtain ⟨j, k, hjk, hd⟩ := h m
    have := isMinOn_iff.1 hmin (f (dyTime j k)) ⟨_, hjk, rfl⟩
    linarith

/-- The distance to the image of `[0, c]` is approached at dyadic times. -/
theorem infDist_image_lt_iff {f : ℝ≥0 → ℂ} {c : ℝ≥0} (hf : ContinuousOn f (Iic c)) (x : ℂ) {ε : ℝ} :
    infDist x (f '' Iic c) < ε ↔ ∃ j k, dyTime j k ≤ c ∧ dist x (f (dyTime j k)) < ε := by
  constructor
  · intro h
    have hne : (f '' Iic c).Nonempty := ⟨f 0, 0, mem_Iic.2 zero_le, rfl⟩
    obtain ⟨_, ⟨s, hs, rfl⟩, hxy⟩ := (infDist_lt_iff hne).1 h
    obtain ⟨j, k, hjk, hd⟩ := exists_dyTime_dist_lt hf hs (show 0 < ε - dist x (f s) by linarith)
    refine ⟨j, k, hjk.trans hs, ?_⟩
    calc dist x (f (dyTime j k)) ≤ dist x (f s) + dist (f s) (f (dyTime j k)) := dist_triangle _ _ _
      _ < ε := by rw [dist_comm (f s)]; linarith
  · rintro ⟨j, k, hjk, hd⟩
    exact (infDist_le_dist_of_mem (mem_image_of_mem f (mem_Iic.2 hjk))).trans_lt hd

/-! ### Finite caps of `ℝ≥0∞` times -/

/-- The finite cap `min(N, u)` of a time `u ∈ [0, ∞]`. -/
def capT (N : ℝ≥0) (u : ℝ≥0∞) : ℝ≥0 := (min (N : ℝ≥0∞) u).toNNReal

theorem le_capT_iff {N : ℝ≥0} {u : ℝ≥0∞} {s : ℝ≥0} : s ≤ capT N u ↔ s ≤ N ∧ (s : ℝ≥0∞) ≤ u := by
  have hne : min (N : ℝ≥0∞) u ≠ ⊤ := ne_top_of_le_ne_top ENNReal.coe_ne_top (min_le_left _ _)
  rw [capT, ← ENNReal.coe_le_coe, ENNReal.coe_toNNReal hne, le_min_iff, ENNReal.coe_le_coe]

theorem measurable_capT (N : ℝ≥0) {Ω : Type*} [MeasurableSpace Ω] {u : Ω → ℝ≥0∞} (hu : Measurable u) :
    Measurable fun ω => capT N (u ω) :=
  ENNReal.measurable_toNNReal.comp (measurable_const.min hu)

theorem continuousOn_Iic_capT {f : ℝ≥0 → ℂ} {u : ℝ≥0∞} (hf : ContinuousOn f {s | (s : ℝ≥0∞) ≤ u}) (N : ℝ≥0) :
    ContinuousOn f (Iic (capT N u)) :=
  hf.mono fun _ hs => (le_capT_iff.1 hs).2

/-! ### Measurable events of random paths -/

section Random

variable {Ω : Type*} [MeasurableSpace Ω]

/-- **Hits of a closed set are measurable** on an event where the paths are continuous on `[0, c ω]`. -/
theorem measurableSet_inter_exists_mem {G : Set Ω} (hG : MeasurableSet G) {f : Ω → ℝ≥0 → ℂ}
    (hf : ∀ t, Measurable fun ω => f ω t) {c : Ω → ℝ≥0} (hc : Measurable c)
    (hcont : ∀ ω ∈ G, ContinuousOn (f ω) (Iic (c ω))) {Q : Set ℂ} (hQ : IsClosed Q) (hQne : Q.Nonempty) :
    MeasurableSet (G ∩ {ω | ∃ s ≤ c ω, f ω s ∈ Q}) := by
  have heq : G ∩ {ω | ∃ s ≤ c ω, f ω s ∈ Q} = G ∩ ⋂ m : ℕ, ⋃ j : ℕ, ⋃ k : ℕ,
      ({ω | dyTime j k ≤ c ω} ∩ {ω | infDist (f ω (dyTime j k)) Q < 1 / ((m : ℝ) + 1)}) := by
    ext ω
    simp only [mem_inter_iff, mem_ofPred_eq, mem_iInter, mem_iUnion]
    exact ⟨fun ⟨hω, h⟩ => ⟨hω, (exists_mem_iff_dyTime (hcont ω hω) hQ hQne).1 h⟩,
      fun ⟨hω, h⟩ => ⟨hω, (exists_mem_iff_dyTime (hcont ω hω) hQ hQne).2 h⟩⟩
  rw [heq]
  refine hG.inter (MeasurableSet.iInter fun m => MeasurableSet.iUnion fun j => MeasurableSet.iUnion fun k => ?_)
  exact (measurableSet_le measurable_const hc).inter
    (measurableSet_lt ((continuous_infDist_pt Q).measurable.comp (hf _)) measurable_const)

/-- **Contacts of two paths are measurable** on an event where both are continuous on their closed intervals. -/
theorem measurableSet_inter_exists_eq {G : Set Ω} (hG : MeasurableSet G) {f₁ f₂ : Ω → ℝ≥0 → ℂ}
    (hf₁ : ∀ t, Measurable fun ω => f₁ ω t) (hf₂ : ∀ t, Measurable fun ω => f₂ ω t) {c₁ c₂ : Ω → ℝ≥0}
    (hc₁ : Measurable c₁) (hc₂ : Measurable c₂) (hcont₁ : ∀ ω ∈ G, ContinuousOn (f₁ ω) (Iic (c₁ ω)))
    (hcont₂ : ∀ ω ∈ G, ContinuousOn (f₂ ω) (Iic (c₂ ω))) :
    MeasurableSet (G ∩ {ω | ∃ s ≤ c₁ ω, ∃ t ≤ c₂ ω, f₁ ω s = f₂ ω t}) := by
  have heq : G ∩ {ω | ∃ s ≤ c₁ ω, ∃ t ≤ c₂ ω, f₁ ω s = f₂ ω t} = G ∩ ⋂ m : ℕ, ⋃ j : ℕ, ⋃ k : ℕ,
      ({ω | dyTime j k ≤ c₁ ω} ∩ ⋃ j' : ℕ, ⋃ l : ℕ, ({ω | dyTime j' l ≤ c₂ ω} ∩
        {ω | dist (f₁ ω (dyTime j k)) (f₂ ω (dyTime j' l)) < 1 / ((m : ℝ) + 1)})) := by
    ext ω
    simp only [mem_inter_iff, mem_ofPred_eq, mem_iInter, mem_iUnion]
    constructor
    · rintro ⟨hω, h⟩
      refine ⟨hω, ?_⟩
      have h' : ∃ s ≤ c₁ ω, f₁ ω s ∈ f₂ ω '' Iic (c₂ ω) := by
        obtain ⟨s, hs, t, ht, he⟩ := h
        exact ⟨s, hs, t, ht, he.symm⟩
      intro m
      obtain ⟨j, k, hjk, hd⟩ := (exists_mem_iff_dyTime (hcont₁ ω hω)
        ((isCompact_Iic_nnreal _).image_of_continuousOn (hcont₂ ω hω)).isClosed
        ⟨f₂ ω 0, 0, mem_Iic.2 zero_le, rfl⟩).1 h' m
      obtain ⟨j', l, hjl, hd'⟩ := (infDist_image_lt_iff (hcont₂ ω hω) _).1 hd
      exact ⟨j, k, hjk, j', l, hjl, hd'⟩
    · rintro ⟨hω, h⟩
      refine ⟨hω, ?_⟩
      have h' : ∃ s ≤ c₁ ω, f₁ ω s ∈ f₂ ω '' Iic (c₂ ω) := by
        refine (exists_mem_iff_dyTime (hcont₁ ω hω)
          ((isCompact_Iic_nnreal _).image_of_continuousOn (hcont₂ ω hω)).isClosed
          ⟨f₂ ω 0, 0, mem_Iic.2 zero_le, rfl⟩).2 fun m => ?_
        obtain ⟨j, k, hjk, j', l, hjl, hd⟩ := h m
        exact ⟨j, k, hjk, (infDist_image_lt_iff (hcont₂ ω hω) _).2 ⟨j', l, hjl, hd⟩⟩
      obtain ⟨s, hs, t, ht, he⟩ := h'
      exact ⟨s, hs, t, ht, he.symm⟩
  rw [heq]
  refine hG.inter (MeasurableSet.iInter fun m => MeasurableSet.iUnion fun j => MeasurableSet.iUnion fun k => ?_)
  refine (measurableSet_le measurable_const hc₁).inter
    (MeasurableSet.iUnion fun j' => MeasurableSet.iUnion fun l => ?_)
  exact (measurableSet_le measurable_const hc₂).inter
    (measurableSet_lt ((hf₁ _).dist (hf₂ _)) measurable_const)

open scoped Classical in
/-- **A path evaluated at a measurable random time is measurable** on an event where the path is continuous on
`[0, s ω]` (`0` off the event). -/
theorem measurable_piecewise_eval {G : Set Ω} (hG : MeasurableSet G) {f : Ω → ℝ≥0 → ℂ}
    (hf : ∀ t, Measurable fun ω => f ω t) {s : Ω → ℝ≥0} (hs : Measurable s)
    (hcont : ∀ ω ∈ G, ContinuousOn (f ω) (Iic (s ω))) :
    Measurable fun ω => if ω ∈ G then f ω (s ω) else 0 := by
  classical
  have hF : ∀ j, Measurable fun ω => f ω (dyFloor j (s ω)) := by
    intro j
    have hp : Measurable fun q : Ω × ℕ => f q.1 (dyTime j q.2) :=
      measurable_from_prod_countable_left fun k => hf (dyTime j k)
    exact hp.comp (measurable_id.prodMk (Nat.measurable_floor.comp
      (measurable_const.mul (measurable_coe_nnreal_real.comp hs))))
  refine measurable_of_tendsto_metrizable (f := fun j ω => if ω ∈ G then f ω (dyFloor j (s ω)) else 0)
    (fun j => Measurable.ite hG (hF j) measurable_const) ?_
  rw [tendsto_pi_nhds]
  intro ω
  by_cases hω : ω ∈ G
  · simp only [hω, ↓reduceIte]
    have hc := hcont ω hω (s ω) (le_refl (s ω))
    refine hc.tendsto.comp (tendsto_nhdsWithin_iff.2 ⟨tendsto_dyFloor _, Eventually.of_forall fun j => ?_⟩)
    exact dyFloor_le j (s ω)
  · simp only [hω, ↓reduceIte]
    exact tendsto_const_nhds

end Random

/-! ### First-contact times -/

section FirstContact

/-- The two available paths meet (at finite parameters). -/
def HasContact (η₁ : ℝ≥0 → ℂ) (ζ₁ : ℝ≥0∞) (η₂ : ℝ≥0 → ℂ) (ζ₂ : ℝ≥0∞) : Prop :=
  ∃ s t : ℝ≥0, (s : ℝ≥0∞) ≤ ζ₁ ∧ (t : ℝ≥0∞) ≤ ζ₂ ∧ η₁ s = η₂ t

/-- The first contact of the two available paths (`0` if there is none). -/
def fcPair (η₁ : ℝ≥0 → ℂ) (ζ₁ : ℝ≥0∞) (η₂ : ℝ≥0 → ℂ) (ζ₂ : ℝ≥0∞) : ℝ≥0 × ℝ≥0 :=
  open scoped Classical in
  if h : ∃ p : ℝ≥0 × ℝ≥0, IsFirstContact η₁ ζ₁ η₂ ζ₂ p.1 p.2 then h.choose else 0

variable {η₁ η₂ : ℝ≥0 → ℂ} {ζ₁ ζ₂ : ℝ≥0∞}

theorem isFirstContact_fcPair {s₀ t₀ : ℝ≥0} (h : IsFirstContact η₁ ζ₁ η₂ ζ₂ s₀ t₀) :
    IsFirstContact η₁ ζ₁ η₂ ζ₂ (fcPair η₁ ζ₁ η₂ ζ₂).1 (fcPair η₁ ζ₁ η₂ ζ₂).2 := by
  have h' : ∃ p : ℝ≥0 × ℝ≥0, IsFirstContact η₁ ζ₁ η₂ ζ₂ p.1 p.2 := ⟨(s₀, t₀), h⟩
  unfold fcPair
  rw [dite_eq_left_of_eq_true (eq_true h')]
  exact h'.choose_spec

theorem fcPair_eq {s₀ t₀ : ℝ≥0} (h : IsFirstContact η₁ ζ₁ η₂ ζ₂ s₀ t₀) : fcPair η₁ ζ₁ η₂ ζ₂ = (s₀, t₀) := by
  have h₁ := isFirstContact_fcPair h
  have a := h.2.2.2 _ _ h₁.1 h₁.2.1 h₁.2.2.1
  have b := h₁.2.2.2 s₀ t₀ h.1 h.2.1 h.2.2.1
  exact Prod.ext (le_antisymm b.1 a.1) (le_antisymm b.2 a.2)

theorem hasContact_iff_exists_nat :
    HasContact η₁ ζ₁ η₂ ζ₂ ↔ ∃ N : ℕ, ∃ s ≤ capT N ζ₁, ∃ t ≤ capT N ζ₂, η₁ s = η₂ t := by
  constructor
  · rintro ⟨s, t, hs, ht, he⟩
    obtain ⟨N, hN⟩ := exists_nat_ge (max (s : ℝ) t)
    have hsN : s ≤ (N : ℝ≥0) := by
      rw [← NNReal.coe_le_coe]; push_cast; exact (le_max_left _ _).trans hN
    have htN : t ≤ (N : ℝ≥0) := by
      rw [← NNReal.coe_le_coe]; push_cast; exact (le_max_right _ _).trans hN
    exact ⟨N, s, le_capT_iff.2 ⟨hsN, hs⟩, t, le_capT_iff.2 ⟨htN, ht⟩, he⟩
  · rintro ⟨N, s, hs, t, ht, he⟩
    exact ⟨s, t, (le_capT_iff.1 hs).2, (le_capT_iff.1 ht).2, he⟩

/-- At a first contact, `s₀ ≤ a` iff some contact has first coordinate `≤ a`. -/
theorem fst_le_iff_of_isFirstContact {s₀ t₀ : ℝ≥0} (h : IsFirstContact η₁ ζ₁ η₂ ζ₂ s₀ t₀) (a : ℝ≥0) :
    s₀ ≤ a ↔ ∃ N : ℕ, ∃ s ≤ capT a ζ₁, ∃ t ≤ capT N ζ₂, η₁ s = η₂ t := by
  constructor
  · intro ha
    obtain ⟨N, hN⟩ := exists_nat_ge (t₀ : ℝ)
    have htN : t₀ ≤ (N : ℝ≥0) := by rw [← NNReal.coe_le_coe]; push_cast; exact hN
    exact ⟨N, s₀, le_capT_iff.2 ⟨ha, h.1⟩, t₀, le_capT_iff.2 ⟨htN, h.2.1⟩, h.2.2.1⟩
  · rintro ⟨N, s, hs, t, ht, he⟩
    exact ((h.2.2.2 s t (le_capT_iff.1 hs).2 (le_capT_iff.1 ht).2 he).1).trans (le_capT_iff.1 hs).1

theorem snd_le_iff_of_isFirstContact {s₀ t₀ : ℝ≥0} (h : IsFirstContact η₁ ζ₁ η₂ ζ₂ s₀ t₀) (a : ℝ≥0) :
    t₀ ≤ a ↔ ∃ N : ℕ, ∃ s ≤ capT N ζ₁, ∃ t ≤ capT a ζ₂, η₁ s = η₂ t := by
  constructor
  · intro ha
    obtain ⟨N, hN⟩ := exists_nat_ge (s₀ : ℝ)
    have hsN : s₀ ≤ (N : ℝ≥0) := by rw [← NNReal.coe_le_coe]; push_cast; exact hN
    exact ⟨N, s₀, le_capT_iff.2 ⟨hsN, h.1⟩, t₀, le_capT_iff.2 ⟨ha, h.2.1⟩, h.2.2.1⟩
  · rintro ⟨N, s, hs, t, ht, he⟩
    exact ((h.2.2.2 s t (le_capT_iff.1 hs).2 (le_capT_iff.1 ht).2 he).2).trans (le_capT_iff.1 ht).1

end FirstContact

section RandomFirstContact

variable {Ω : Type*} [MeasurableSpace Ω] {G : Set Ω} {η₁ η₂ : Ω → ℝ≥0 → ℂ} {ζ₁ ζ₂ : Ω → ℝ≥0∞}
  (hG : MeasurableSet G) (hη₁ : ∀ t, Measurable fun ω => η₁ ω t) (hη₂ : ∀ t, Measurable fun ω => η₂ ω t)
  (hζ₁ : Measurable ζ₁) (hζ₂ : Measurable ζ₂)
  (hc₁ : ∀ ω ∈ G, ContinuousOn (η₁ ω) {s | (s : ℝ≥0∞) ≤ ζ₁ ω})
  (hc₂ : ∀ ω ∈ G, ContinuousOn (η₂ ω) {t | (t : ℝ≥0∞) ≤ ζ₂ ω})
include hG hη₁ hη₂ hζ₁ hζ₂ hc₁ hc₂

theorem measurableSet_inter_contact_capT (a b : ℝ≥0) :
    MeasurableSet (G ∩ {ω | ∃ s ≤ capT a (ζ₁ ω), ∃ t ≤ capT b (ζ₂ ω), η₁ ω s = η₂ ω t}) :=
  measurableSet_inter_exists_eq hG hη₁ hη₂ (measurable_capT a hζ₁) (measurable_capT b hζ₂)
    (fun ω hω => continuousOn_Iic_capT (hc₁ ω hω) a) (fun ω hω => continuousOn_Iic_capT (hc₂ ω hω) b)

/-- The contact event is measurable on `G`. -/
theorem measurableSet_inter_hasContact :
    MeasurableSet (G ∩ {ω | HasContact (η₁ ω) (ζ₁ ω) (η₂ ω) (ζ₂ ω)}) := by
  have heq : G ∩ {ω | HasContact (η₁ ω) (ζ₁ ω) (η₂ ω) (ζ₂ ω)} =
      ⋃ N : ℕ, G ∩ {ω | ∃ s ≤ capT N (ζ₁ ω), ∃ t ≤ capT N (ζ₂ ω), η₁ ω s = η₂ ω t} := by
    ext ω
    simp only [mem_inter_iff, mem_ofPred_eq, mem_iUnion, hasContact_iff_exists_nat]
    exact ⟨fun ⟨hω, N, h⟩ => ⟨N, hω, h⟩, fun ⟨N, hω, h⟩ => ⟨hω, N, h⟩⟩
  rw [heq]
  exact MeasurableSet.iUnion fun N : ℕ =>
    measurableSet_inter_contact_capT hG hη₁ hη₂ hζ₁ hζ₂ hc₁ hc₂ (N : ℝ≥0) (N : ℝ≥0)

open scoped Classical in
/-- **The first-contact times are measurable** on the contact event, when the first contact exists there. -/
theorem measurable_piecewise_fcTime
    (hfc : ∀ ω ∈ G, HasContact (η₁ ω) (ζ₁ ω) (η₂ ω) (ζ₂ ω) →
      ∃ s₀ t₀, IsFirstContact (η₁ ω) (ζ₁ ω) (η₂ ω) (ζ₂ ω) s₀ t₀) :
    Measurable (fun ω => if ω ∈ G ∩ {ω | HasContact (η₁ ω) (ζ₁ ω) (η₂ ω) (ζ₂ ω)} then
        (fcPair (η₁ ω) (ζ₁ ω) (η₂ ω) (ζ₂ ω)).1 else 0) ∧
      Measurable (fun ω => if ω ∈ G ∩ {ω | HasContact (η₁ ω) (ζ₁ ω) (η₂ ω) (ζ₂ ω)} then
        (fcPair (η₁ ω) (ζ₁ ω) (η₂ ω) (ζ₂ ω)).2 else 0) := by
  set E := G ∩ {ω | HasContact (η₁ ω) (ζ₁ ω) (η₂ ω) (ζ₂ ω)} with hE
  have hEm : MeasurableSet E := measurableSet_inter_hasContact hG hη₁ hη₂ hζ₁ hζ₂ hc₁ hc₂
  have hfcE : ∀ ω ∈ E, IsFirstContact (η₁ ω) (ζ₁ ω) (η₂ ω) (ζ₂ ω) (fcPair (η₁ ω) (ζ₁ ω) (η₂ ω) (ζ₂ ω)).1
      (fcPair (η₁ ω) (ζ₁ ω) (η₂ ω) (ζ₂ ω)).2 := fun ω hω => by
    obtain ⟨s₀, t₀, h⟩ := hfc ω hω.1 hω.2
    exact isFirstContact_fcPair h
  constructor
  · refine measurable_of_Iic fun a => ?_
    have heq : (fun ω => if ω ∈ E then (fcPair (η₁ ω) (ζ₁ ω) (η₂ ω) (ζ₂ ω)).1 else 0) ⁻¹' Iic a =
        (E ∩ ⋃ N : ℕ, G ∩ {ω | ∃ s ≤ capT a (ζ₁ ω), ∃ t ≤ capT N (ζ₂ ω), η₁ ω s = η₂ ω t}) ∪ Eᶜ := by
      ext ω
      by_cases hω : ω ∈ E
      · simp only [mem_preimage, hω, ↓reduceIte, mem_Iic, mem_union, mem_inter_iff, mem_iUnion, mem_ofPred_eq,
          true_and, mem_compl_iff, not_true_eq_false, or_false]
        rw [fst_le_iff_of_isFirstContact (hfcE ω hω) a]
        exact ⟨fun ⟨N, h⟩ => ⟨N, hω.1, h⟩, fun ⟨N, _, h⟩ => ⟨N, h⟩⟩
      · simp only [mem_preimage, hω, ↓reduceIte, mem_Iic, zero_le, mem_union, mem_compl_iff, not_false_eq_true,
          or_true]
    rw [heq]
    exact (hEm.inter (MeasurableSet.iUnion fun N : ℕ =>
      measurableSet_inter_contact_capT hG hη₁ hη₂ hζ₁ hζ₂ hc₁ hc₂ a (N : ℝ≥0))).union hEm.compl
  · refine measurable_of_Iic fun a => ?_
    have heq : (fun ω => if ω ∈ E then (fcPair (η₁ ω) (ζ₁ ω) (η₂ ω) (ζ₂ ω)).2 else 0) ⁻¹' Iic a =
        (E ∩ ⋃ N : ℕ, G ∩ {ω | ∃ s ≤ capT N (ζ₁ ω), ∃ t ≤ capT a (ζ₂ ω), η₁ ω s = η₂ ω t}) ∪ Eᶜ := by
      ext ω
      by_cases hω : ω ∈ E
      · simp only [mem_preimage, hω, ↓reduceIte, mem_Iic, mem_union, mem_inter_iff, mem_iUnion, mem_ofPred_eq,
          true_and, mem_compl_iff, not_true_eq_false, or_false]
        rw [snd_le_iff_of_isFirstContact (hfcE ω hω) a]
        exact ⟨fun ⟨N, h⟩ => ⟨N, hω.1, h⟩, fun ⟨N, _, h⟩ => ⟨N, h⟩⟩
      · simp only [mem_preimage, hω, ↓reduceIte, mem_Iic, zero_le, mem_union, mem_compl_iff, not_false_eq_true,
          or_true]
    rw [heq]
    exact (hEm.inter (MeasurableSet.iUnion fun N : ℕ =>
      measurableSet_inter_contact_capT hG hη₁ hη₂ hζ₁ hζ₂ hc₁ hc₂ (N : ℝ≥0) a)).union hEm.compl

end RandomFirstContact

end Restart

end InteractingSLE
