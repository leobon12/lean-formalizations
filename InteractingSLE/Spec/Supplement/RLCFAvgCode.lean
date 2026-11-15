/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.RLCBBuffer

/-!
# Countable forms of the prefix conditions of the real completion event

Packet PROVE-RLC-F, piece (iv) (integration over the retained datum, as in PROVE-RLC-B's `RLCBCode.lean`). The event
integrated over the datum must be universally measurable, so every prefix condition in it is written through the dyadic
code `encC g` of the path, with countably many quantifiers:

* `AvoidC q a F` (the path avoids a closed set `F` on `(0, a]`), `InC q a F` (on `[0, a]`), `HitC q a F` (it meets `F`
  at some time in `(0, a]`), `CommonC q₁ a₁ q₂ a₂` (two paths have a common point after time `0`);
* for paths continuous on `[0, a]` each is equivalent to its pathwise form (`avoidC_encC_iff`, `inC_encC_iff`,
  `hitC_encC_iff`, `commonC_encC_iff`), and each is a measurable condition on codes.
-/

set_option autoImplicit false

noncomputable section

open Complex Set Metric Filter Topology MeasureTheory
open scoped NNReal ENNReal

namespace InteractingSLE

namespace RLC

open Theorem15D5 Sec2.Assembly Restart

/-! ### Dyadic approximation from below -/

/-- A time `t > 1/(m+1)` is approached from below by dyadic times in `[1/(m+1), t]`. -/
theorem eventually_dyad_flr_mem {m : ℕ} {t : ℝ≥0} (ht : 1 / ((m : ℝ≥0) + 1) < t) :
    ∀ᶠ n in atTop, 1 / ((m : ℝ≥0) + 1) ≤ dyad n (flr n t) ∧ dyad n (flr n t) ≤ t := by
  filter_upwards [(tendsto_dyad_flr t).eventually (lt_mem_nhds ht)] with n hn
  exact ⟨hn.le, dyad_flr_le n t⟩

/-- A positive time is above some `1/(m+1)`. -/
theorem exists_one_div_lt {t : ℝ≥0} (ht : 0 < t) : ∃ m : ℕ, 1 / ((m : ℝ≥0) + 1) < t := by
  obtain ⟨m, hm⟩ := exists_nat_one_div_lt (show (0 : ℝ) < t from ht)
  exact ⟨m, by rw [← NNReal.coe_lt_coe]; push_cast; exact hm⟩

/-- The dyadic floors of `t ≤ a` converge to `t` within `[0, a]`, so a path continuous on `[0, a]` converges along
them. -/
theorem tendsto_comp_dyad_flr {g : ℝ≥0 → ℂ} {a t : ℝ≥0} (hg : ContinuousOn g (Iic a)) (hta : t ≤ a) :
    Tendsto (fun n => g (dyad n (flr n t))) atTop (𝓝 (g t)) :=
  (hg t hta).tendsto.comp (tendsto_nhdsWithin_iff.2 ⟨tendsto_dyad_flr t,
    Eventually.of_forall fun n => (dyad_flr_le n t).trans hta⟩)

/-! ### Avoiding a closed set after time `0` -/

/-- **The path avoids `F` on `(0, a]`, in countable form**: on every `[1/(m+1), a]` the dyadic values keep a positive
distance from `F`. -/
def AvoidC (q : CCode) (a : ℝ≥0) (F : Set ℂ) : Prop :=
  ∀ m : ℕ, ∃ j : ℕ, ∀ n k : ℕ, 1 / ((m : ℝ≥0) + 1) ≤ dyad n k → dyad n k ≤ a →
    1 / ((j : ℝ) + 1) ≤ infDist (q n k) F

theorem measurable_avoidC (a : ℝ≥0) (F : Set ℂ) : Measurable fun q : CCode => AvoidC q a F :=
  Measurable.forall fun _ => Measurable.exists fun _ => Measurable.forall fun n => Measurable.forall fun k =>
    measurable_const.imp <| measurable_const.imp <| measurableSet_setOfPred.mp
      (measurableSet_le measurable_const ((continuous_infDist_pt F).measurable.comp (measurable_coord n k)))

theorem avoidC_encC_iff {g : ℝ≥0 → ℂ} {a : ℝ≥0} {F : Set ℂ} (hg : ContinuousOn g (Iic a)) (hF : IsClosed F)
    (hFne : F.Nonempty) : AvoidC (encC g) a F ↔ ∀ t : ℝ≥0, 0 < t → t ≤ a → g t ∉ F := by
  constructor
  · intro hA t ht hta hgF
    obtain ⟨m, hm⟩ := exists_one_div_lt ht
    obtain ⟨j, hj⟩ := hA m
    have hev : ∀ᶠ n in atTop, 1 / ((j : ℝ) + 1) ≤ infDist (g (dyad n (flr n t))) F := by
      filter_upwards [eventually_dyad_flr_mem hm] with n hn
      exact hj n (flr n t) hn.1 (hn.2.trans hta)
    have hle : 1 / ((j : ℝ) + 1) ≤ infDist (g t) F :=
      ge_of_tendsto (((continuous_infDist_pt F).tendsto _).comp (tendsto_comp_dyad_flr hg hta)) hev
    rw [infDist_zero_of_mem hgF] at hle
    exact absurd hle (not_le.2 (by positivity))
  · intro hav m
    set C : Set ℝ≥0 := Icc (1 / ((m : ℝ≥0) + 1)) a with hC
    rcases C.eq_empty_or_nonempty with hCe | hCne
    · refine ⟨0, fun n k h1 h2 => ?_⟩
      exact absurd (show dyad n k ∈ C from ⟨h1, h2⟩) (by rw [hCe]; exact notMem_empty _)
    have hcont : ContinuousOn (fun t => infDist (g t) F) C :=
      (continuous_infDist_pt F).comp_continuousOn (hg.mono fun t ht => ht.2)
    obtain ⟨t₀, ht₀, hmin⟩ := isCompact_Icc.exists_isMinOn hCne hcont
    have ht₀pos : 0 < t₀ := lt_of_lt_of_le (by positivity) ht₀.1
    have hpos : 0 < infDist (g t₀) F := (hF.notMem_iff_infDist_pos hFne).1 (hav t₀ ht₀pos ht₀.2)
    obtain ⟨j, hj⟩ := exists_nat_one_div_lt hpos
    exact ⟨j, fun n k h1 h2 => hj.le.trans (hmin ⟨h1, h2⟩)⟩

/-! ### Staying off a closed set on `[0, a]` -/

/-- **The path avoids `F` on `[0, a]`, in countable form.** -/
def InC (q : CCode) (a : ℝ≥0) (F : Set ℂ) : Prop :=
  ∃ j : ℕ, ∀ n k : ℕ, dyad n k ≤ a → 1 / ((j : ℝ) + 1) ≤ infDist (q n k) F

theorem measurable_inC (a : ℝ≥0) (F : Set ℂ) : Measurable fun q : CCode => InC q a F :=
  Measurable.exists fun _ => Measurable.forall fun n => Measurable.forall fun k =>
    measurable_const.imp <| measurableSet_setOfPred.mp
      (measurableSet_le measurable_const ((continuous_infDist_pt F).measurable.comp (measurable_coord n k)))

theorem inC_encC_iff {g : ℝ≥0 → ℂ} {a : ℝ≥0} {F : Set ℂ} (hg : ContinuousOn g (Iic a)) (hF : IsClosed F)
    (hFne : F.Nonempty) : InC (encC g) a F ↔ ∀ t : ℝ≥0, t ≤ a → g t ∉ F := by
  constructor
  · rintro ⟨j, hj⟩ t hta hgF
    have hev : ∀ᶠ n in atTop, 1 / ((j : ℝ) + 1) ≤ infDist (g (dyad n (flr n t))) F :=
      Eventually.of_forall fun n => hj n (flr n t) ((dyad_flr_le n t).trans hta)
    have hle : 1 / ((j : ℝ) + 1) ≤ infDist (g t) F :=
      ge_of_tendsto (((continuous_infDist_pt F).tendsto _).comp (tendsto_comp_dyad_flr hg hta)) hev
    rw [infDist_zero_of_mem hgF] at hle
    exact absurd hle (not_le.2 (by positivity))
  · intro hav
    have hcont : ContinuousOn (fun t => infDist (g t) F) (Icc 0 a) :=
      (continuous_infDist_pt F).comp_continuousOn (hg.mono fun t ht => ht.2)
    obtain ⟨t₀, ht₀, hmin⟩ := isCompact_Icc.exists_isMinOn ⟨0, le_rfl, zero_le⟩ hcont
    have hpos : 0 < infDist (g t₀) F := (hF.notMem_iff_infDist_pos hFne).1 (hav t₀ ht₀.2)
    obtain ⟨j, hj⟩ := exists_nat_one_div_lt hpos
    exact ⟨j, fun n k h => hj.le.trans (hmin ⟨zero_le, h⟩)⟩

/-! ### Meeting a closed set after time `0` -/

/-- **The path meets `F` at some time in `(0, a]`, in countable form.** -/
def HitC (q : CCode) (a : ℝ≥0) (F : Set ℂ) : Prop :=
  ∃ m : ℕ, ∀ j : ℕ, ∃ n k : ℕ, 1 / ((m : ℝ≥0) + 1) ≤ dyad n k ∧ dyad n k ≤ a ∧
    infDist (q n k) F < 1 / ((j : ℝ) + 1)

theorem measurable_hitC (a : ℝ≥0) (F : Set ℂ) : Measurable fun q : CCode => HitC q a F :=
  Measurable.exists fun _ => Measurable.forall fun _ => Measurable.exists fun n => Measurable.exists fun k =>
    measurable_const.and <| measurable_const.and <| measurableSet_setOfPred.mp
      (measurableSet_lt ((continuous_infDist_pt F).measurable.comp (measurable_coord n k)) measurable_const)

theorem hitC_encC_iff {g : ℝ≥0 → ℂ} {a : ℝ≥0} {F : Set ℂ} (hg : ContinuousOn g (Iic a)) (hF : IsClosed F)
    (hFne : F.Nonempty) : HitC (encC g) a F ↔ ∃ t : ℝ≥0, 0 < t ∧ t ≤ a ∧ g t ∈ F := by
  constructor
  · rintro ⟨m, hm⟩
    choose n k hnk using hm
    have hK : IsCompact (Icc (1 / ((m : ℝ≥0) + 1)) a) := isCompact_Icc
    obtain ⟨t, ht, φ, hφ, hlim⟩ := hK.tendsto_subseq (x := fun j => dyad (n j) (k j))
      fun j => ⟨(hnk j).1, (hnk j).2.1⟩
    refine ⟨t, lt_of_lt_of_le (by positivity) ht.1, ht.2, ?_⟩
    have hc : Tendsto (fun j => g (dyad (n (φ j)) (k (φ j)))) atTop (𝓝 (g t)) :=
      (hg t ht.2).tendsto.comp (tendsto_nhdsWithin_iff.2 ⟨hlim, Eventually.of_forall fun j => (hnk (φ j)).2.1⟩)
    have hd : Tendsto (fun j => infDist (g (dyad (n (φ j)) (k (φ j)))) F) atTop (𝓝 (infDist (g t) F)) :=
      ((continuous_infDist_pt F).tendsto _).comp hc
    have h0 : Tendsto (fun j => infDist (g (dyad (n (φ j)) (k (φ j)))) F) atTop (𝓝 0) := by
      refine squeeze_zero (fun j => infDist_nonneg) (fun j => (hnk (φ j)).2.2.le) ?_
      exact tendsto_one_div_add_atTop_nhds_zero_nat.comp hφ.tendsto_atTop
    have := tendsto_nhds_unique hd h0
    exact (hF.mem_iff_infDist_zero hFne).2 this
  · rintro ⟨t, ht, hta, hgF⟩
    obtain ⟨m, hm⟩ := exists_one_div_lt ht
    refine ⟨m, fun j => ?_⟩
    have hd : Tendsto (fun n => infDist (g (dyad n (flr n t))) F) atTop (𝓝 0) := by
      have := ((continuous_infDist_pt F).tendsto _).comp (tendsto_comp_dyad_flr hg hta)
      rwa [infDist_zero_of_mem hgF] at this
    obtain ⟨n, hn⟩ := ((hd.eventually (gt_mem_nhds (show (0 : ℝ) < 1 / ((j : ℝ) + 1) by positivity))).and
      (eventually_dyad_flr_mem hm)).exists
    exact ⟨n, flr n t, hn.2.1, hn.2.2.trans hta, hn.1⟩

/-! ### A common point after time `0` -/

/-- **Two paths have a common point after time `0`, in countable form.** -/
def CommonC (q₁ : CCode) (a₁ : ℝ≥0) (q₂ : CCode) (a₂ : ℝ≥0) : Prop :=
  ∃ m : ℕ, ∀ j : ℕ, ∃ n₁ k₁ n₂ k₂ : ℕ, 1 / ((m : ℝ≥0) + 1) ≤ dyad n₁ k₁ ∧ dyad n₁ k₁ ≤ a₁ ∧
    1 / ((m : ℝ≥0) + 1) ≤ dyad n₂ k₂ ∧ dyad n₂ k₂ ≤ a₂ ∧ ‖q₁ n₁ k₁ - q₂ n₂ k₂‖ < 1 / ((j : ℝ) + 1)

theorem measurable_commonC (a₁ a₂ : ℝ≥0) : Measurable fun x : CCode × CCode => CommonC x.1 a₁ x.2 a₂ :=
  Measurable.exists fun _ => Measurable.forall fun _ => Measurable.exists fun n₁ => Measurable.exists fun k₁ =>
    Measurable.exists fun n₂ => Measurable.exists fun k₂ =>
      measurable_const.and <| measurable_const.and <| measurable_const.and <| measurable_const.and <|
        measurableSet_setOfPred.mp (measurableSet_lt (((measurable_coord n₁ k₁).comp measurable_fst).sub
          ((measurable_coord n₂ k₂).comp measurable_snd)).norm measurable_const)

theorem commonC_encC_iff {g₁ g₂ : ℝ≥0 → ℂ} {a₁ a₂ : ℝ≥0} (hg₁ : ContinuousOn g₁ (Iic a₁))
    (hg₂ : ContinuousOn g₂ (Iic a₂)) :
    CommonC (encC g₁) a₁ (encC g₂) a₂ ↔
      ∃ t₁ t₂ : ℝ≥0, 0 < t₁ ∧ t₁ ≤ a₁ ∧ 0 < t₂ ∧ t₂ ≤ a₂ ∧ g₁ t₁ = g₂ t₂ := by
  constructor
  · rintro ⟨m, hm⟩
    choose n₁ k₁ n₂ k₂ hnk using hm
    have hK : IsCompact (Icc (1 / ((m : ℝ≥0) + 1)) a₁ ×ˢ Icc (1 / ((m : ℝ≥0) + 1)) a₂) :=
      isCompact_Icc.prod isCompact_Icc
    obtain ⟨⟨t₁, t₂⟩, ht, φ, hφ, hlim⟩ := hK.tendsto_subseq
      (x := fun j => (dyad (n₁ j) (k₁ j), dyad (n₂ j) (k₂ j)))
      fun j => ⟨⟨(hnk j).1, (hnk j).2.1⟩, ⟨(hnk j).2.2.1, (hnk j).2.2.2.1⟩⟩
    have hl₁ : Tendsto (fun j => dyad (n₁ (φ j)) (k₁ (φ j))) atTop (𝓝 t₁) := (continuous_fst.tendsto _).comp hlim
    have hl₂ : Tendsto (fun j => dyad (n₂ (φ j)) (k₂ (φ j))) atTop (𝓝 t₂) := (continuous_snd.tendsto _).comp hlim
    have hc₁ : Tendsto (fun j => g₁ (dyad (n₁ (φ j)) (k₁ (φ j)))) atTop (𝓝 (g₁ t₁)) :=
      (hg₁ t₁ ht.1.2).tendsto.comp (tendsto_nhdsWithin_iff.2 ⟨hl₁, Eventually.of_forall fun j =>
        (hnk (φ j)).2.1⟩)
    have hc₂ : Tendsto (fun j => g₂ (dyad (n₂ (φ j)) (k₂ (φ j)))) atTop (𝓝 (g₂ t₂)) :=
      (hg₂ t₂ ht.2.2).tendsto.comp (tendsto_nhdsWithin_iff.2 ⟨hl₂, Eventually.of_forall fun j =>
        (hnk (φ j)).2.2.2.1⟩)
    have hd : Tendsto (fun j => ‖g₁ (dyad (n₁ (φ j)) (k₁ (φ j))) - g₂ (dyad (n₂ (φ j)) (k₂ (φ j)))‖) atTop
        (𝓝 ‖g₁ t₁ - g₂ t₂‖) := (hc₁.sub hc₂).norm
    have h0 : Tendsto (fun j => ‖g₁ (dyad (n₁ (φ j)) (k₁ (φ j))) - g₂ (dyad (n₂ (φ j)) (k₂ (φ j)))‖) atTop
        (𝓝 0) := by
      refine squeeze_zero (fun j => norm_nonneg _) (fun j => (hnk (φ j)).2.2.2.2.le) ?_
      exact tendsto_one_div_add_atTop_nhds_zero_nat.comp hφ.tendsto_atTop
    have := tendsto_nhds_unique hd h0
    refine ⟨t₁, t₂, lt_of_lt_of_le (by positivity) ht.1.1, ht.1.2, lt_of_lt_of_le (by positivity) ht.2.1, ht.2.2,
      ?_⟩
    exact sub_eq_zero.1 (norm_eq_zero.1 this)
  · rintro ⟨t₁, t₂, ht₁, ht₁a, ht₂, ht₂a, he⟩
    obtain ⟨m₁, hm₁⟩ := exists_one_div_lt ht₁
    obtain ⟨m₂, hm₂⟩ := exists_one_div_lt ht₂
    set m := max m₁ m₂ with hmdef
    have hmono : ∀ i : ℕ, i ≤ m → 1 / ((m : ℝ≥0) + 1) ≤ 1 / ((i : ℝ≥0) + 1) := fun i hi => by
      gcongr
    have hm₁' : 1 / ((m : ℝ≥0) + 1) < t₁ := lt_of_le_of_lt (hmono m₁ (le_max_left _ _)) hm₁
    have hm₂' : 1 / ((m : ℝ≥0) + 1) < t₂ := lt_of_le_of_lt (hmono m₂ (le_max_right _ _)) hm₂
    refine ⟨m, fun j => ?_⟩
    have hd : Tendsto (fun n => ‖g₁ (dyad n (flr n t₁)) - g₂ (dyad n (flr n t₂))‖) atTop (𝓝 0) := by
      have := ((tendsto_comp_dyad_flr hg₁ ht₁a).sub (tendsto_comp_dyad_flr hg₂ ht₂a)).norm
      rwa [he, sub_self, norm_zero] at this
    obtain ⟨n, hn⟩ := (((hd.eventually (gt_mem_nhds (show (0 : ℝ) < 1 / ((j : ℝ) + 1) by positivity))).and
      (eventually_dyad_flr_mem hm₁')).and (eventually_dyad_flr_mem hm₂')).exists
    exact ⟨n, flr n t₁, n, flr n t₂, hn.1.2.1, hn.1.2.2.trans ht₁a, hn.2.1, hn.2.2.trans ht₂a, hn.1.1⟩

/-! ### Rational strips and the strip buffer -/

/-- The union of the open rational strips `(a, b)`, `(a, b) ∈ S`. -/
def StripSet (S : List (ℚ × ℚ)) : Set ℝ := {x | ∃ ab ∈ S, (ab.1 : ℝ) < x ∧ x < ab.2}

/-- The union of the closed rational strips `[a, b]`, `(a, b) ∈ S`. -/
def ClStripSet (S : List (ℚ × ℚ)) : Set ℝ := {x | ∃ ab ∈ S, (ab.1 : ℝ) ≤ x ∧ x ≤ ab.2}

theorem isOpen_stripSet (S : List (ℚ × ℚ)) : IsOpen (StripSet S) := by
  have : StripSet S = ⋃ ab ∈ S, Ioo (ab.1 : ℝ) ab.2 := by
    ext x; constructor
    · rintro ⟨ab, hab, h1, h2⟩; exact mem_biUnion hab ⟨h1, h2⟩
    · intro hx; obtain ⟨ab, hab, hx⟩ := mem_iUnion₂.1 hx; exact ⟨ab, hab, hx.1, hx.2⟩
  rw [this]; exact isOpen_biUnion fun _ _ => isOpen_Ioo

theorem isClosed_clStripSet (S : List (ℚ × ℚ)) : IsClosed (ClStripSet S) := by
  have : ClStripSet S = ⋃ ab ∈ {ab | ab ∈ S}, Icc (ab.1 : ℝ) ab.2 := by
    ext x; constructor
    · rintro ⟨ab, hab, h1, h2⟩; exact mem_biUnion hab ⟨h1, h2⟩
    · intro hx; obtain ⟨ab, hab, hx⟩ := mem_iUnion₂.1 hx; exact ⟨ab, hab, hx.1, hx.2⟩
  rw [this]; exact Set.Finite.isClosed_biUnion S.finite_toSet fun _ _ => isClosed_Icc

theorem stripSet_subset_clStripSet (S : List (ℚ × ℚ)) : StripSet S ⊆ ClStripSet S :=
  fun _ ⟨ab, hab, h1, h2⟩ => ⟨ab, hab, h1.le, h2.le⟩

theorem exists_bound_stripSet (S : List (ℚ × ℚ)) : ∃ B : ℝ, ∀ x ∈ StripSet S, x < B := by
  induction S with
  | nil => exact ⟨0, fun x ⟨ab, hab, _⟩ => absurd hab List.not_mem_nil⟩
  | cons ab S ih =>
    obtain ⟨B, hB⟩ := ih
    refine ⟨max B ab.2, fun x ⟨ab', hab', h1, h2⟩ => ?_⟩
    rcases List.mem_cons.1 hab' with rfl | h
    · exact lt_of_lt_of_le h2 (le_max_right _ _)
    · exact lt_of_lt_of_le (hB x ⟨ab', h, h1, h2⟩) (le_max_left _ _)

/-- The real points off the open strips. -/
def offStrips (S : List (ℚ × ℚ)) : Set ℂ := {z | z.im = 0 ∧ z.re ∉ StripSet S}

theorem isClosed_offStrips (S : List (ℚ × ℚ)) : IsClosed (offStrips S) :=
  (isClosed_eq Complex.continuous_im continuous_const).inter
    ((isOpen_stripSet S).isClosed_compl.preimage Complex.continuous_re)

theorem offStrips_nonempty (S : List (ℚ × ℚ)) : (offStrips S).Nonempty := by
  obtain ⟨B, hB⟩ := exists_bound_stripSet S
  exact ⟨(B : ℂ), by simp, fun h => lt_irrefl _ (hB B (by simpa using h))⟩

/-- The real axis. -/
def realAxis : Set ℂ := {z | z.im = 0}

theorem isClosed_realAxis : IsClosed realAxis := isClosed_eq Complex.continuous_im continuous_const

theorem realAxis_nonempty : realAxis.Nonempty := ⟨0, by simp [realAxis]⟩

/-- **The strip buffer** around two chart prefixes from the seeds `0` and (a rational point `ω` near) `w`:
`{‖z‖ < R ∧ (ε' < Im z ∨ ‖z‖ < ε ∨ ‖z − ω‖ < ε ∨ (Im z < 2ε' ∧ Re z ∈ ⋃ (a, b)))}`. -/
def stripBuffer (S : List (ℚ × ℚ)) (ε' ε R ω : ℝ) : Set ℂ :=
  {z | ‖z‖ < R ∧ (ε' < z.im ∨ ‖z‖ < ε ∨ ‖z - ω‖ < ε ∨ (z.im < 2 * ε' ∧ z.re ∈ StripSet S))}

theorem isOpen_stripBuffer (S : List (ℚ × ℚ)) (ε' ε R ω : ℝ) : IsOpen (stripBuffer S ε' ε R ω) :=
  (isOpen_lt continuous_norm continuous_const).inter ((isOpen_lt continuous_const Complex.continuous_im).union
    ((isOpen_lt continuous_norm continuous_const).union
      ((isOpen_lt (continuous_norm.comp (continuous_id.sub continuous_const)) continuous_const).union
        ((isOpen_lt Complex.continuous_im continuous_const).inter
          ((isOpen_stripSet S).preimage Complex.continuous_re)))))

theorem isBounded_stripBuffer (S : List (ℚ × ℚ)) (ε' ε R ω : ℝ) : Bornology.IsBounded (stripBuffer S ε' ε R ω) :=
  (Metric.isBounded_ball (x := (0 : ℂ)) (r := R)).subset fun z hz => by
    rw [mem_ball, dist_zero_right]; exact hz.1

theorem isClosed_compl_stripBuffer (S : List (ℚ × ℚ)) (ε' ε R ω : ℝ) : IsClosed (stripBuffer S ε' ε R ω)ᶜ :=
  (isOpen_stripBuffer S ε' ε R ω).isClosed_compl

theorem compl_stripBuffer_nonempty (S : List (ℚ × ℚ)) (ε' ε R ω : ℝ) : (stripBuffer S ε' ε R ω)ᶜ.Nonempty :=
  ⟨((|R| + 1 : ℝ) : ℂ), fun h => by
    have h1 := h.1
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by positivity)] at h1
    linarith [le_abs_self R]⟩

/-- The real points of the closure of a strip buffer lie within `ε` of `0` or `ω`, or in a closed strip. -/
theorem re_mem_of_mem_closure_stripBuffer {S : List (ℚ × ℚ)} {ε' ε R ω : ℝ} (hε' : 0 < ε') {z : ℂ}
    (hz : z ∈ closure (stripBuffer S ε' ε R ω)) (hz0 : z.im = 0) :
    |z.re| ≤ ε ∨ |z.re - ω| ≤ ε ∨ z.re ∈ ClStripSet S := by
  have hF : IsClosed {z : ℂ | ε' ≤ z.im ∨ ‖z‖ ≤ ε ∨ ‖z - ω‖ ≤ ε ∨ (z.im ≤ 2 * ε' ∧ z.re ∈ ClStripSet S)} :=
    (isClosed_le continuous_const Complex.continuous_im).union ((isClosed_le continuous_norm continuous_const).union
      ((isClosed_le (continuous_norm.comp (continuous_id.sub continuous_const)) continuous_const).union
        ((isClosed_le Complex.continuous_im continuous_const).inter
          ((isClosed_clStripSet S).preimage Complex.continuous_re))))
  have hsub : stripBuffer S ε' ε R ω ⊆
      {z : ℂ | ε' ≤ z.im ∨ ‖z‖ ≤ ε ∨ ‖z - ω‖ ≤ ε ∨ (z.im ≤ 2 * ε' ∧ z.re ∈ ClStripSet S)} := by
    rintro z ⟨-, h | h | h | h⟩
    · exact Or.inl h.le
    · exact Or.inr (Or.inl h.le)
    · exact Or.inr (Or.inr (Or.inl h.le))
    · exact Or.inr (Or.inr (Or.inr ⟨h.1.le, stripSet_subset_clStripSet S h.2⟩))
  rcases closure_minimal hsub hF hz with h | h | h | h
  · linarith
  · left
    have := Complex.abs_re_le_norm z
    linarith
  · right; left
    have h' := Complex.abs_re_le_norm (z - ω)
    simp only [Complex.sub_re, Complex.ofReal_re] at h'
    linarith
  · exact Or.inr (Or.inr h.2)

/-! ### The datum condition for a strip family -/

/-- **The datum condition for a strip family**: all strips lie in one chart region (left of `0`, between `0` and `w`,
right of `w`), contain no jump position of the word in their closures, and carry one common height. -/
def StripCond (c : BoundaryWord) (w : ℝ) (S : List (ℚ × ℚ)) : Prop :=
  ((∀ ab ∈ S, (ab.2 : ℝ) < 0) ∨ (∀ ab ∈ S, 0 < (ab.1 : ℝ) ∧ (ab.2 : ℝ) < w) ∨ (∀ ab ∈ S, w < (ab.1 : ℝ))) ∧
    (∀ ab ∈ S, ∀ i < c.1, c.2.1 i < ab.1 ∨ (ab.2 : ℝ) < c.2.1 i) ∧ (∀ ab ∈ S, ∀ ab' ∈ S, c.fn ab.1 = c.fn ab'.1)

theorem measurableSet_stripCond (S : List (ℚ × ℚ)) :
    MeasurableSet {p : BoundaryWord × ℝ | StripCond p.1 p.2 S} := by
  have hp : ∀ i : ℕ, Measurable fun c : BoundaryWord × ℝ => c.1.2.1 i :=
    fun i => (measurable_pi_apply i).comp (measurable_fst.comp (measurable_snd.comp measurable_fst))
  have hn : Measurable fun c : BoundaryWord × ℝ => c.1.1 := measurable_fst.comp measurable_fst
  have hfn : ∀ y : ℝ, Measurable fun c : BoundaryWord × ℝ => c.1.fn y :=
    fun y => (Supp7.measurable_boundaryWord_fn y).comp measurable_fst
  refine measurableSet_setOfPred.mpr (Measurable.and ?_ (Measurable.and ?_ ?_))
  · refine Measurable.or ?_ (Measurable.or ?_ ?_)
    · exact Measurable.forall fun _ => measurable_const.imp measurable_const
    · exact Measurable.forall fun _ => measurable_const.imp (measurable_const.and
        (measurableSet_setOfPred.mp (measurableSet_lt measurable_const measurable_snd)))
    · exact Measurable.forall fun _ => measurable_const.imp
        (measurableSet_setOfPred.mp (measurableSet_lt measurable_snd measurable_const))
  · refine Measurable.forall fun _ => measurable_const.imp (Measurable.forall fun i => ?_)
    exact (measurableSet_setOfPred.mp (measurableSet_lt measurable_const hn)).imp
      ((measurableSet_setOfPred.mp (measurableSet_lt (hp i) measurable_const)).or
        (measurableSet_setOfPred.mp (measurableSet_lt measurable_const (hp i))))
  · exact Measurable.forall fun _ => measurable_const.imp (Measurable.forall fun _ => measurable_const.imp
      (measurableSet_setOfPred.mp (measurableSet_eq_fun (hfn _) (hfn _))))

/-- Under the datum condition, the word has no jump on a closed strip, and its height there is the common one. -/
theorem StripCond.fn_eq {c : BoundaryWord} {w : ℝ} {S : List (ℚ × ℚ)} (h : StripCond c w S) {ab : ℚ × ℚ}
    (hab : ab ∈ S) {x : ℝ} (hx : (ab.1 : ℝ) ≤ x ∧ x ≤ ab.2) : x ∉ c.jumps ∧ c.fn x = c.fn ab.1 := by
  refine ⟨fun hJ => ?_, (fn_eq_of_noPos hx.1 fun i hi => ?_).symm⟩
  · obtain ⟨i, hi, rfl⟩ := BoundaryWord.mem_jumps.1 hJ
    rcases h.2.1 ab hab i hi with h' | h'
    · linarith [hx.1]
    · linarith [hx.2]
  · rcases h.2.1 ab hab i hi with h' | h'
    · exact Or.inl h'
    · exact Or.inr (by linarith [hx.2])

/-! ### The jump part -/

/-- **The path avoids the point `y` on `(0, a]`, in countable form** (`AvoidC` for `{y}`, with the distance written
out, so that it is measurable jointly in the code and the point). -/
def AvoidPtC (q : CCode) (a : ℝ≥0) (y : ℝ) : Prop :=
  ∀ m : ℕ, ∃ j : ℕ, ∀ n k : ℕ, 1 / ((m : ℝ≥0) + 1) ≤ dyad n k → dyad n k ≤ a → 1 / ((j : ℝ) + 1) ≤ ‖q n k - y‖

theorem avoidPtC_iff (q : CCode) (a : ℝ≥0) (y : ℝ) : AvoidPtC q a y ↔ AvoidC q a {(y : ℂ)} := by
  simp only [AvoidPtC, AvoidC, infDist_singleton, dist_eq_norm]

/-- **No jump position of the word other than `w` is met by the first chart path at a dyadic-bounded time before its
lifetime**, in countable form. -/
def JumpFreeC (c : BoundaryWord) (w : ℝ) (q : CCode) (U : ℝ≥0∞) : Prop :=
  ∀ i < c.1, c.2.1 i ≠ w → ∀ p : ℕ × ℕ, (dyad p.1 p.2 : ℝ≥0∞) < U → AvoidPtC q (dyad p.1 p.2) (c.2.1 i)

theorem measurable_jumpFreeC :
    Measurable fun x : (BoundaryWord × ℝ) × (CCode × ℝ≥0∞) => JumpFreeC x.1.1 x.1.2 x.2.1 x.2.2 := by
  have hp : ∀ i : ℕ, Measurable fun x : (BoundaryWord × ℝ) × (CCode × ℝ≥0∞) => x.1.1.2.1 i :=
    fun i => (measurable_pi_apply i).comp (measurable_fst.comp (measurable_snd.comp (measurable_fst.comp
      measurable_fst)))
  have hn : Measurable fun x : (BoundaryWord × ℝ) × (CCode × ℝ≥0∞) => x.1.1.1 :=
    measurable_fst.comp (measurable_fst.comp measurable_fst)
  have hq : ∀ n k, Measurable fun x : (BoundaryWord × ℝ) × (CCode × ℝ≥0∞) => x.2.1 n k :=
    fun n k => (measurable_coord n k).comp (measurable_fst.comp measurable_snd)
  refine Measurable.forall fun i => ?_
  refine (measurableSet_setOfPred.mp (measurableSet_lt measurable_const hn)).imp ?_
  refine (measurableSet_setOfPred.mp (measurableSet_eq_fun (hp i) (measurable_snd.comp measurable_fst))).not.imp ?_
  refine Measurable.forall fun pp => ?_
  refine (measurableSet_setOfPred.mp (measurableSet_lt measurable_const
    (measurable_snd.comp measurable_snd))).imp ?_
  refine Measurable.forall fun _ => Measurable.exists fun _ => Measurable.forall fun n => Measurable.forall fun k =>
    measurable_const.imp <| measurable_const.imp <| measurableSet_setOfPred.mp
      (measurableSet_le measurable_const ((hq n k).sub (Complex.measurable_ofReal.comp (hp i))).norm)

/-! ### The per-datum event -/

/-- **The real completion event at one datum, in countable form**: the jump part, and for every strip family which
satisfies the datum condition there is a collar threshold `1/(k+1)` such that for every rational strip buffer with
collar radius below it (centred at `0` and at a rational `ω` within the radius of `w`) and every pair of dyadic times
before the lifetimes: if both prefixes lie in the buffer, have their real points after time `0` in the open strips,
meet `ℝ` after time `0`, and have a common point after time `0`, then their codes are completable. -/
def RealEventC (c : BoundaryWord) (w : ℝ) (q₁ : CCode) (U₁ : ℝ≥0∞) (q₂ : CCode) (U₂ : ℝ≥0∞) : Prop :=
  JumpFreeC c w q₁ U₁ ∧
  ∀ S : List (ℚ × ℚ), StripCond c w S → ∃ k : ℕ, ∀ ε' ε R ω : ℚ, 0 < (ε' : ℝ) → 0 < (ε : ℝ) →
    (ε : ℝ) < 1 / ((k : ℝ) + 1) → |w - ω| < ε → ∀ p₁ p₂ : ℕ × ℕ,
      (dyad p₁.1 p₁.2 : ℝ≥0∞) < U₁ → (dyad p₂.1 p₂.2 : ℝ≥0∞) < U₂ →
      InC q₁ (dyad p₁.1 p₁.2) (stripBuffer S ε' ε R ω)ᶜ → InC q₂ (dyad p₂.1 p₂.2) (stripBuffer S ε' ε R ω)ᶜ →
      AvoidC q₁ (dyad p₁.1 p₁.2) (offStrips S) → AvoidC q₂ (dyad p₂.1 p₂.2) (offStrips S) →
      HitC q₁ (dyad p₁.1 p₁.2) realAxis → HitC q₂ (dyad p₂.1 p₂.2) realAxis →
      CommonC q₁ (dyad p₁.1 p₁.2) q₂ (dyad p₂.1 p₂.2) →
      ∃ y, ((q₁, q₂), y) ∈ CompRelS (dyad p₁.1 p₁.2) (dyad p₂.1 p₂.2)

section UMeas

variable {α : Type*} [MeasurableSpace α]

theorem uMeasurableSet_setOf_forall {ι : Sort*} [Countable ι] {P : ι → α → Prop}
    (h : ∀ i, LQGMetric.UMeasurableSet {x | P i x}) : LQGMetric.UMeasurableSet {x | ∀ i, P i x} := by
  rw [Set.ofPred_forall]; exact LQGMetric.UMeasurableSet.iInter h

theorem uMeasurableSet_setOf_exists {ι : Sort*} [Countable ι] {P : ι → α → Prop}
    (h : ∀ i, LQGMetric.UMeasurableSet {x | P i x}) : LQGMetric.UMeasurableSet {x | ∃ i, P i x} := by
  rw [Set.ofPred_exists]; exact LQGMetric.UMeasurableSet.iUnion h

theorem uMeasurableSet_setOf_imp {P Q : α → Prop} (hP : MeasurableSet {x | P x})
    (hQ : LQGMetric.UMeasurableSet {x | Q x}) : LQGMetric.UMeasurableSet {x | P x → Q x} := by
  have : {x | P x → Q x} = {x | P x}ᶜ ∪ {x | Q x} := by
    ext x; simp only [mem_ofPred_eq, mem_union, mem_compl_iff]; tauto
  rw [this]; exact (LQGMetric.UMeasurableSet.of_measurableSet hP).compl.union hQ

theorem uMeasurableSet_setOf_and {P Q : α → Prop} (hP : LQGMetric.UMeasurableSet {x | P x})
    (hQ : LQGMetric.UMeasurableSet {x | Q x}) : LQGMetric.UMeasurableSet {x | P x ∧ Q x} := by
  rw [Set.ofPred_and]; exact hP.inter hQ

end UMeas

/-- **The per-datum event is universally measurable** in `(datum, (code₁, lifetime₁), (code₂, lifetime₂))`. -/
theorem uMeasurableSet_realEventC : LQGMetric.UMeasurableSet
    {x : (BoundaryWord × ℝ) × ((CCode × ℝ≥0∞) × (CCode × ℝ≥0∞)) |
      RealEventC x.1.1 x.1.2 x.2.1.1 x.2.1.2 x.2.2.1 x.2.2.2} := by
  set X := (BoundaryWord × ℝ) × ((CCode × ℝ≥0∞) × (CCode × ℝ≥0∞))
  have mq₁ : Measurable fun x : X => x.2.1.1 := measurable_fst.comp (measurable_fst.comp measurable_snd)
  have mq₂ : Measurable fun x : X => x.2.2.1 := measurable_fst.comp (measurable_snd.comp measurable_snd)
  have mU₁ : Measurable fun x : X => x.2.1.2 := measurable_snd.comp (measurable_fst.comp measurable_snd)
  have mU₂ : Measurable fun x : X => x.2.2.2 := measurable_snd.comp (measurable_snd.comp measurable_snd)
  have mw : Measurable fun x : X => x.1.2 := measurable_snd.comp measurable_fst
  refine uMeasurableSet_setOf_and (LQGMetric.UMeasurableSet.of_measurableSet ?_) ?_
  · exact measurableSet_setOfPred.mpr (measurable_jumpFreeC.comp (measurable_fst.prodMk
      (mq₁.prodMk mU₁)))
  refine uMeasurableSet_setOf_forall fun S => uMeasurableSet_setOf_imp ?_ ?_
  · exact (measurableSet_stripCond S).preimage measurable_fst
  refine uMeasurableSet_setOf_exists fun k => uMeasurableSet_setOf_forall fun ε' =>
    uMeasurableSet_setOf_forall fun ε => uMeasurableSet_setOf_forall fun R => uMeasurableSet_setOf_forall fun ω =>
    uMeasurableSet_setOf_imp (MeasurableSet.const _) <| uMeasurableSet_setOf_imp (MeasurableSet.const _) <|
    uMeasurableSet_setOf_imp (MeasurableSet.const _) <| uMeasurableSet_setOf_imp ?_ <|
    uMeasurableSet_setOf_forall fun p₁ => uMeasurableSet_setOf_forall fun p₂ => ?_
  · exact measurableSet_lt ((mw.sub measurable_const).abs) measurable_const
  refine uMeasurableSet_setOf_imp (measurableSet_lt measurable_const mU₁) <|
    uMeasurableSet_setOf_imp (measurableSet_lt measurable_const mU₂) <|
    uMeasurableSet_setOf_imp ((measurable_inC _ _).comp mq₁).setOf <|
    uMeasurableSet_setOf_imp ((measurable_inC _ _).comp mq₂).setOf <|
    uMeasurableSet_setOf_imp ((measurable_avoidC _ _).comp mq₁).setOf <|
    uMeasurableSet_setOf_imp ((measurable_avoidC _ _).comp mq₂).setOf <|
    uMeasurableSet_setOf_imp ((measurable_hitC _ _).comp mq₁).setOf <|
    uMeasurableSet_setOf_imp ((measurable_hitC _ _).comp mq₂).setOf <|
    uMeasurableSet_setOf_imp ((measurable_commonC _ _).comp (mq₁.prodMk mq₂)).setOf ?_
  exact (uMeasurableSet_completableCode _ _).preimage (mq₁.prodMk mq₂)

end RLC

end InteractingSLE
