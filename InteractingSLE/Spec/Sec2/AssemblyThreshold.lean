/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec2.AssemblyRelation

/-!
# Theorem 2.2 assembly: measurable forms of the threshold conditions

Packet PROVE-SEC2-PATCH. The threshold condition of Definition 2.1 at a state is a Borel condition
(`measurableSet_thr`). For a path continuous on `[0, T]`, "some time `t ≤ T` has exactly the
marks `S` of one side at the driver" is equivalent to a countable condition at dyadic times
(`exists_at_iff`, by continuity and compactness of `[0, T]`); this makes "the threshold condition
fails before `ζ`" a measurable condition on codes (`AssemblyMeasurable`). The state's limit at
`ζ⁻`, whenever it exists, is the limit along the dyadic times `dyad n (⌈ζ 2ⁿ⌉₊ − 1) ↑ ζ`
(`lim_eq_of_tendsto`), whose `limsup` is measurable in the code (`measurable_limState`).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology
open scoped NNReal ENNReal

namespace InteractingSLE

namespace Sec2

namespace Assembly

/-! ### One side at the driver -/

/-- Finitely many positive numbers have a common positive lower bound. -/
theorem exists_pos_forall_lt' {ι : Type*} [Fintype ι] (f : ι → ℝ) (hf : ∀ i, 0 < f i) :
    ∃ ε > 0, ∀ i, ε < f i := by
  rcases isEmpty_or_nonempty ι with hι | hι
  · exact ⟨1, one_pos, fun i => isEmptyElim i⟩
  · set m := Finset.univ.inf' Finset.univ_nonempty f
    have hm : 0 < m := (Finset.lt_inf'_iff _).2 fun i _ => hf i
    refine ⟨m / 2, by positivity, fun i => ?_⟩
    have : m ≤ f i := Finset.inf'_le _ (Finset.mem_univ i)
    linarith

/-- Exactly the marks of `S` sit at the driver `w` (positions `u`). -/
def AtSide {n : ℕ} (S : Finset (Fin n)) (w : ℝ) (u : Fin n → ℝ) : Prop :=
  (∀ i ∈ S, u i = w) ∧ ∀ i ∉ S, u i ≠ w

/-- The marks of `S` are within `1/(m+1)` of the driver and the others farther than `1/(p+1)`. -/
def NearSide {n : ℕ} (S : Finset (Fin n)) (p m : ℕ) (w : ℝ) (u : Fin n → ℝ) : Prop :=
  (∀ i ∈ S, |u i - w| < 1 / (m + 1)) ∧ ∀ i ∉ S, 1 / (p + 1) < |u i - w|

/-- The sum over the marks at the driver is the sum over `S` when exactly `S` is at the driver. -/
theorem sum_filter_eq_of_atSide {n : ℕ} {S : Finset (Fin n)} {w : ℝ} {u : Fin n → ℝ}
    (ρ : Fin n → ℝ) (h : AtSide S w u) :
    (∑ i ∈ Finset.univ.filter (fun i => u i = w), ρ i) = ∑ i ∈ S, ρ i := by
  congr 1
  ext i
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  exact ⟨fun hi => by_contra fun hS => h.2 i hS hi, fun hi => h.1 i hi⟩

theorem atSide_filter {n : ℕ} (w : ℝ) (u : Fin n → ℝ) :
    AtSide (Finset.univ.filter fun i => u i = w) w u :=
  ⟨fun _ hi => (Finset.mem_filter.1 hi).2, fun _ hi he =>
    hi (Finset.mem_filter.2 ⟨Finset.mem_univ _, he⟩)⟩

/-- **Dyadic characterization** of "at some time `t ≤ T` exactly the marks `S` are at the
driver", for a path continuous on `[0, T]`. -/
theorem exists_atSide_iff {n : ℕ} {S : Finset (Fin n)} {w : ℝ≥0 → ℝ} {u : Fin n → ℝ≥0 → ℝ}
    {T : ℝ≥0} (hw : ContinuousOn w (Iic T)) (hu : ∀ i, ContinuousOn (u i) (Iic T)) :
    (∃ t ≤ T, AtSide S (w t) fun i => u i t) ↔
      ∃ p : ℕ, ∀ m : ℕ, ∃ n' k, dyad n' k ≤ T ∧
        NearSide S p m (w (dyad n' k)) fun i => u i (dyad n' k) := by
  constructor
  · rintro ⟨t, htT, hS, hnS⟩
    have hpos : ∀ i, 0 < if i ∈ S then (1 : ℝ) else |u i t - w t| := by
      intro i
      split_ifs with hi
      · exact one_pos
      · exact abs_pos.2 (sub_ne_zero.2 (show u i t ≠ w t from hnS i hi))
    obtain ⟨ε, hε, hε'⟩ := Assembly.exists_pos_forall_lt' _ hpos
    obtain ⟨p, hp⟩ := exists_nat_one_div_lt hε
    refine ⟨p, fun m => ?_⟩
    have hd : Tendsto (fun n' => dyad n' (flr n' t)) atTop (𝓝[Iic T] t) :=
      tendsto_nhdsWithin_iff.2 ⟨tendsto_dyad_flr t,
        Eventually.of_forall fun n' => (dyad_flr_le n' t).trans htT⟩
    have hcw := (hw t htT).tendsto.comp hd
    have hcu : ∀ i, Tendsto (fun n' => u i (dyad n' (flr n' t))) atTop (𝓝 (u i t)) :=
      fun i => ((hu i) t htT).tendsto.comp hd
    have hgap : ∀ i, Tendsto (fun n' => |u i (dyad n' (flr n' t)) - w (dyad n' (flr n' t))|)
        atTop (𝓝 |u i t - w t|) := fun i => ((hcu i).sub hcw).abs
    have hev : ∀ᶠ n' in atTop, NearSide S p m (w (dyad n' (flr n' t)))
        fun i => u i (dyad n' (flr n' t)) := by
      refine (Filter.eventually_all.2 fun i => ?_).and (Filter.eventually_all.2 fun i => ?_)
      · by_cases hi : i ∈ S
        · have e : u i t = w t := hS i hi
          have h0 : |u i t - w t| = 0 := by rw [e, sub_self, abs_zero]
          have := hgap i
          rw [h0] at this
          filter_upwards [this.eventually (gt_mem_nhds (by positivity :
            (0 : ℝ) < 1 / (m + 1)))] with n' hn' _ using hn'
        · exact Eventually.of_forall fun n' h => absurd h hi
      · by_cases hi : i ∈ S
        · exact Eventually.of_forall fun n' h => absurd hi h
        · have hlt : 1 / ((p : ℝ) + 1) < |u i t - w t| := by
            have := hε' i
            simp only [hi, ↓reduceIte] at this
            exact lt_trans hp this
          filter_upwards [(hgap i).eventually (lt_mem_nhds hlt)] with n' hn' _ using hn'
    obtain ⟨n', hn'⟩ := hev.exists
    exact ⟨n', flr n' t, (dyad_flr_le n' t).trans htT, hn'⟩
  · rintro ⟨p, hp⟩
    choose nn kk hle hnear using hp
    have hcpt : IsCompact (Iic T) := by rw [← Icc_bot]; exact isCompact_Icc
    obtain ⟨t, htT, φ, hφ, htend⟩ := hcpt.tendsto_subseq (x := fun m => dyad (nn m) (kk m)) hle
    have htend' : Tendsto (fun j => dyad (nn (φ j)) (kk (φ j))) atTop (𝓝[Iic T] t) :=
      tendsto_nhdsWithin_iff.2 ⟨htend, Eventually.of_forall fun j => hle (φ j)⟩
    have hcw := (hw t htT).tendsto.comp htend'
    have hgap : ∀ i, Tendsto (fun j => |u i (dyad (nn (φ j)) (kk (φ j))) -
        w (dyad (nn (φ j)) (kk (φ j)))|) atTop (𝓝 |u i t - w t|) :=
      fun i => (((hu i) t htT).tendsto.comp htend' |>.sub hcw).abs
    refine ⟨t, htT, fun i hi => ?_, fun i hi => ?_⟩
    · have hbd : Tendsto (fun j : ℕ => (1 : ℝ) / ((φ j : ℝ) + 1)) atTop (𝓝 0) :=
        tendsto_one_div_add_atTop_nhds_zero_nat.comp hφ.tendsto_atTop
      have hle0 : |u i t - w t| ≤ 0 := le_of_tendsto_of_tendsto' (hgap i) hbd
        fun j => ((hnear (φ j)).1 i hi).le
      have := abs_nonpos_iff.1 hle0
      linarith
    · have hge : 1 / ((p : ℝ) + 1) ≤ |u i t - w t| :=
        ge_of_tendsto' (hgap i) fun j => ((hnear (φ j)).2 i hi).le
      intro he
      have he' : u i t = w t := he
      rw [he', sub_self, abs_zero] at hge
      have : (0 : ℝ) < 1 / ((p : ℝ) + 1) := by positivity
      linarith

/-! ### The threshold condition is Borel -/

theorem measurable_sum_at {n : ℕ} (ρ : Fin n → ℝ) :
    Measurable fun q : ℝ × (Fin n → ℝ) =>
      ∑ i ∈ Finset.univ.filter (fun i => q.2 i = q.1), ρ i := by
  have e : (fun q : ℝ × (Fin n → ℝ) => ∑ i ∈ Finset.univ.filter (fun i => q.2 i = q.1), ρ i) =
      fun q => ∑ i, if q.2 i = q.1 then ρ i else 0 := by
    funext q; rw [Finset.sum_filter]
  rw [e]
  refine Finset.measurable_sum _ fun i _ => Measurable.ite ?_ measurable_const measurable_const
  exact measurableSet_eq_fun ((measurable_pi_apply i).comp measurable_snd) measurable_fst

/-- The threshold condition is a Borel condition on the state. -/
theorem measurableSet_thr {nL nR : ℕ} (ρL : Fin nL → ℝ) (ρR : Fin nR → ℝ) :
    MeasurableSet {q : ℝ × (Fin nL → ℝ) × (Fin nR → ℝ) |
      ForceWord.ThresholdCondition ρL ρR q.1 q.2.1 q.2.2} := by
  unfold ForceWord.ThresholdCondition
  refine MeasurableSet.union ?_ ?_
  · exact measurableSet_le ((measurable_sum_at ρL).comp (measurable_fst.prodMk
      measurable_snd.fst)) measurable_const
  · exact measurableSet_le ((measurable_sum_at ρR).comp (measurable_fst.prodMk
      measurable_snd.snd)) measurable_const

/-! ### The limit at `ζ⁻` along dyadic times -/

/-- Index of the last dyadic time of level `n` strictly before `T`. -/
def ldy (n : ℕ) (T : ℝ≥0) : ℕ := ⌈T * 2 ^ n⌉₊ - 1

theorem dyad_ldy_lt {T : ℝ≥0} (hT : 0 < T) (n : ℕ) : dyad n (ldy n T) < T := by
  have h2 : (0 : ℝ) < 2 ^ n := by positivity
  have hy : 0 < T * 2 ^ n := by positivity
  have h1 : 1 ≤ ⌈T * 2 ^ n⌉₊ := Nat.one_le_iff_ne_zero.2 (Nat.ceil_pos.2 hy).ne'
  have hc : (⌈T * 2 ^ n⌉₊ : ℝ) < (T : ℝ) * 2 ^ n + 1 := by
    have := Nat.ceil_lt_add_one (le_of_lt hy)
    have e : ((T * 2 ^ n : ℝ≥0) : ℝ) = (T : ℝ) * 2 ^ n := by push_cast; ring
    rw [← e]; exact_mod_cast this
  have hd : (dyad n (ldy n T) : ℝ) = ((⌈T * 2 ^ n⌉₊ : ℝ) - 1) / 2 ^ n := by
    have hl : ((ldy n T : ℕ) : ℝ) = (⌈T * 2 ^ n⌉₊ : ℝ) - 1 := by
      unfold ldy; rw [Nat.cast_sub h1, Nat.cast_one]
    unfold dyad
    rw [NNReal.coe_div, NNReal.coe_natCast, NNReal.coe_pow, NNReal.coe_ofNat, hl]
  have : (dyad n (ldy n T) : ℝ) < T := by
    rw [hd, div_lt_iff₀ h2]; linarith
  exact_mod_cast this

theorem tendsto_dyad_ldy {T : ℝ≥0} (hT : 0 < T) :
    Tendsto (fun n => dyad n (ldy n T)) atTop (𝓝[<] T) := by
  refine tendsto_nhdsWithin_iff.2 ⟨?_, Eventually.of_forall fun n => dyad_ldy_lt hT n⟩
  rw [← NNReal.tendsto_coe]
  have hlow : ∀ n : ℕ, (T : ℝ) - 1 / 2 ^ n ≤ dyad n (ldy n T) := by
    intro n
    have h2 : (0 : ℝ) < 2 ^ n := by positivity
    have hy : 0 < T * 2 ^ n := by positivity
    have h1 : 1 ≤ ⌈T * 2 ^ n⌉₊ := Nat.one_le_iff_ne_zero.2 (Nat.ceil_pos.2 hy).ne'
    have hc : (T : ℝ) * 2 ^ n ≤ (⌈T * 2 ^ n⌉₊ : ℝ) := by
      have := Nat.le_ceil (T * 2 ^ n)
      have e : ((T * 2 ^ n : ℝ≥0) : ℝ) = (T : ℝ) * 2 ^ n := by push_cast; ring
      rw [← e]; exact_mod_cast this
    have hd : (dyad n (ldy n T) : ℝ) = ((⌈T * 2 ^ n⌉₊ : ℝ) - 1) / 2 ^ n := by
      have hl : ((ldy n T : ℕ) : ℝ) = (⌈T * 2 ^ n⌉₊ : ℝ) - 1 := by
        unfold ldy; rw [Nat.cast_sub h1, Nat.cast_one]
      unfold dyad
      rw [NNReal.coe_div, NNReal.coe_natCast, NNReal.coe_pow, NNReal.coe_ofNat, hl]
    rw [hd, sub_le_iff_le_add, ← add_div, le_div_iff₀ h2]
    linarith
  have h1 : Tendsto (fun n : ℕ => (T : ℝ) - 1 / 2 ^ n) atTop (𝓝 T) := by
    have : Tendsto (fun n : ℕ => (1 : ℝ) / 2 ^ n) atTop (𝓝 0) := by
      simp only [one_div]
      exact tendsto_inv_atTop_zero.comp (tendsto_pow_atTop_atTop_of_one_lt one_lt_two)
    simpa using tendsto_const_nhds.sub this
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le h1 tendsto_const_nhds hlow
    fun n => by exact_mod_cast (dyad_ldy_lt hT n).le

theorem measurable_ldy_time (n : ℕ) :
    Measurable fun T : ℝ≥0 => dyad n (ldy n T) := by
  have h1 : Measurable fun T : ℝ≥0 => ldy n T := by
    unfold ldy
    exact (Nat.measurable_ceil.comp (measurable_id.mul_const _)).sub_const 1
  exact (measurable_from_nat (f := fun k => dyad n k)).comp h1

variable {nL nR : ℕ}

/-- The dyadic limit of the decoded state at `ζ⁻` (a `limsup` along `dyad n (ldy n ζ)`). -/
def limW (x : XCode nL nR) : ℝ :=
  limsup (fun n => cw x (dyad n (ldy n (cζ x).toNNReal))) atTop
def limVL (x : XCode nL nR) : Fin nL → ℝ := fun i =>
  limsup (fun n => cvL x i (dyad n (ldy n (cζ x).toNNReal))) atTop
def limVR (x : XCode nL nR) : Fin nR → ℝ := fun j =>
  limsup (fun n => cvR x j (dyad n (ldy n (cζ x).toNNReal))) atTop

theorem measurable_dec_ldy {f : XCode nL nR → PCode} (hf : Measurable f) (n : ℕ) :
    Measurable fun x => dec (f x) (dyad n (ldy n (cζ x).toNNReal)) := by
  have h1 : Measurable fun x : XCode nL nR => (f x, dyad n (ldy n (cζ x).toNNReal)) :=
    hf.prodMk ((measurable_ldy_time n).comp (measurable_cζ.ennreal_toNNReal))
  have := measurable_dec.comp h1
  rwa [Function.comp_def] at this

theorem measurable_limState :
    Measurable fun x : XCode nL nR => (limW x, limVL x, limVR x) := by
  refine (Measurable.limsup fun n => measurable_dec_ldy measurable_code_w n).prodMk
    ((measurable_pi_iff.2 fun i => Measurable.limsup fun n =>
      measurable_dec_ldy (measurable_code_vL i) n).prodMk
    (measurable_pi_iff.2 fun j => Measurable.limsup fun n =>
      measurable_dec_ldy (measurable_code_vR j) n))

/-- The limit at `ζ⁻`, if it exists, is the dyadic limit. -/
theorem lim_eq_of_tendsto {x : XCode nL nR} {T : ℝ≥0} (hT : 0 < T) (hζ : (T : ℝ≥0∞) = cζ x)
    {q : ℝ × (Fin nL → ℝ) × (Fin nR → ℝ)}
    (h : Tendsto (fun t => (cw x t, fun i => cvL x i t, fun j => cvR x j t)) (𝓝[<] T) (𝓝 q)) :
    (limW x, limVL x, limVR x) = q := by
  have hT' : (cζ x).toNNReal = T := by rw [← hζ]; rfl
  have hs := h.comp (tendsto_dyad_ldy hT)
  have h1 := (continuous_fst.tendsto q).comp hs
  have h2 := (continuous_snd.fst.tendsto q).comp hs
  have h3 := (continuous_snd.snd.tendsto q).comp hs
  ext
  · show limsup _ atTop = q.1
    rw [hT']; exact h1.limsup_eq
  · rename_i i
    show limsup _ atTop = q.2.1 i
    rw [hT']; exact ((continuous_apply i).tendsto _ |>.comp h2).limsup_eq
  · rename_i j
    show limsup _ atTop = q.2.2 j
    rw [hT']; exact ((continuous_apply j).tendsto _ |>.comp h3).limsup_eq

end Assembly

end Sec2

end InteractingSLE
