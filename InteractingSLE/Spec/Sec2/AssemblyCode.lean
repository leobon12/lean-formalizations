/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import Mathlib.MeasureTheory.Constructions.Polish.Basic
import Mathlib.MeasureTheory.Function.Floor
import Mathlib.Topology.UniformSpace.HeineCantor

/-!
# Theorem 2.2 assembly: dyadic codes of paths

Packet PROVE-SEC2-PATCH. A real path on `ℝ≥0` is coded by its values at the dyadic times
`k / 2ⁿ` (`PCode = ℕ → ℕ → ℝ`, a countable product, hence a standard Borel space), and decoded by
`dec c t = limsup_n c n ⌊t 2ⁿ⌋₊` (values at the dyadic floors of `t`). Decoding is jointly
measurable (`measurable_dec`); it inverts coding at every point of left continuity
(`dec_enc`). The countable condition `UC c T` (uniform continuity of the code on the dyadic times
of `[0, T]`) makes the decoded path continuous on `[0, T]` and equal to the code at its dyadic
times (`UC.continuousOn`, `UC.dec_dyad`); every path continuous on `[0, T]` has such a code
(`uc_enc`, Heine–Cantor). These are the tools that make the solution relation of Definition 2.1 a
measurable set (`AssemblyRelation`).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology
open scoped NNReal ENNReal

namespace InteractingSLE

namespace Sec2

namespace Assembly

/-- Codes of real paths on `ℝ≥0`: `c n k` is the value at the dyadic time `k / 2ⁿ`. -/
abbrev PCode : Type := ℕ → ℕ → ℝ

/-- The dyadic time `k / 2ⁿ`. -/
def dyad (n k : ℕ) : ℝ≥0 := (k : ℝ≥0) / 2 ^ n

/-- The level-`n` dyadic floor index of `t`: `⌊t 2ⁿ⌋₊`. -/
def flr (n : ℕ) (t : ℝ≥0) : ℕ := ⌊t * 2 ^ n⌋₊

/-- The code of a path. -/
def enc (f : ℝ≥0 → ℝ) : PCode := fun n k => f (dyad n k)

/-- Decoding: the `limsup` of the code along the dyadic floors of `t`. (Irreducible: unifying
compositions with an unfolded `limsup` is very slow.) -/
@[irreducible] def dec (c : PCode) (t : ℝ≥0) : ℝ := limsup (fun n => c n (flr n t)) atTop

theorem dyad_flr_le (n : ℕ) (t : ℝ≥0) : dyad n (flr n t) ≤ t := by
  unfold dyad flr
  rw [div_le_iff₀ (by positivity)]
  exact Nat.floor_le (by positivity)

theorem sub_lt_dyad_flr (n : ℕ) (t : ℝ≥0) : (t : ℝ) - 1 / 2 ^ n < dyad n (flr n t) := by
  have h2 : (0 : ℝ) < 2 ^ n := by positivity
  have hfl : (t : ℝ) * 2 ^ n < (⌊t * 2 ^ n⌋₊ : ℝ) + 1 := by
    have := Nat.lt_floor_add_one (t * 2 ^ n)
    exact_mod_cast this
  have hd : (dyad n (flr n t) : ℝ) = (⌊t * 2 ^ n⌋₊ : ℝ) / 2 ^ n := by
    unfold dyad flr; push_cast; rfl
  rw [hd, sub_lt_iff_lt_add, ← add_div, lt_div_iff₀ h2]
  linarith

theorem tendsto_dyad_flr (t : ℝ≥0) : Tendsto (fun n => dyad n (flr n t)) atTop (𝓝 t) := by
  rw [← NNReal.tendsto_coe]
  have h1 : Tendsto (fun n : ℕ => (t : ℝ) - 1 / 2 ^ n) atTop (𝓝 t) := by
    have : Tendsto (fun n : ℕ => (1 : ℝ) / 2 ^ n) atTop (𝓝 0) := by
      simp only [one_div]
      exact tendsto_inv_atTop_zero.comp (tendsto_pow_atTop_atTop_of_one_lt one_lt_two)
    simpa using tendsto_const_nhds.sub this
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le h1 tendsto_const_nhds
    (fun n => (sub_lt_dyad_flr n t).le) fun n => by exact_mod_cast dyad_flr_le n t

/-- Dyadic times are dense: between `t < ζ` there is a dyadic time. -/
theorem exists_dyad_btwn {t : ℝ≥0} {ζ : ℝ≥0∞} (ht : (t : ℝ≥0∞) < ζ) :
    ∃ n k, t < dyad n k ∧ (dyad n k : ℝ≥0∞) < ζ := by
  obtain ⟨u, htu, huζ⟩ := ENNReal.lt_iff_exists_nnreal_btwn.1 ht
  have htu' : t < u := by exact_mod_cast htu
  -- choose `n` with `1/2ⁿ < u - t`, and `k = ⌊t 2ⁿ⌋₊ + 1`
  have hpos : (0 : ℝ) < u - t := sub_pos.2 (by exact_mod_cast htu')
  obtain ⟨n, hn⟩ : ∃ n : ℕ, (1 : ℝ) / 2 ^ n < u - t := by
    obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one hpos (by norm_num : (1 / 2 : ℝ) < 1)
    exact ⟨n, by simpa [div_pow] using hn⟩
  refine ⟨n, flr n t + 1, ?_, ?_⟩
  · have := sub_lt_dyad_flr n t
    have hd : (dyad n (flr n t + 1) : ℝ) = dyad n (flr n t) + 1 / 2 ^ n := by
      unfold dyad; push_cast; ring
    have : (t : ℝ) < dyad n (flr n t + 1) := by rw [hd]; linarith
    exact_mod_cast this
  · have hd : (dyad n (flr n t + 1) : ℝ) = dyad n (flr n t) + 1 / 2 ^ n := by
      unfold dyad; push_cast; ring
    have hle : (dyad n (flr n t) : ℝ) ≤ t := by exact_mod_cast dyad_flr_le n t
    have : (dyad n (flr n t + 1) : ℝ) < u := by rw [hd]; linarith
    exact lt_of_lt_of_le (by exact_mod_cast this) huζ.le

/-- Decoding inverts coding at a point of left continuity. -/
theorem dec_enc {f : ℝ≥0 → ℝ} {t : ℝ≥0} (hf : ContinuousWithinAt f (Iic t) t) :
    dec (enc f) t = f t := by
  have h : Tendsto (fun n => dyad n (flr n t)) atTop (𝓝[Iic t] t) :=
    tendsto_nhdsWithin_iff.2 ⟨tendsto_dyad_flr t, Eventually.of_forall fun n => dyad_flr_le n t⟩
  unfold dec
  exact (hf.tendsto.comp h).limsup_eq

theorem measurable_flr (n : ℕ) : Measurable (flr n) := by
  unfold flr
  exact Nat.measurable_floor.comp (measurable_id.mul_const _)

/-- **Decoding is jointly measurable.** -/
theorem measurable_dec : Measurable fun p : PCode × ℝ≥0 => dec p.1 p.2 := by
  unfold dec
  refine Measurable.limsup fun n => ?_
  have hev : Measurable fun q : PCode × ℕ => q.1 n q.2 :=
    measurable_from_prod_countable_left fun k => measurable_pi_iff.1 (measurable_pi_apply n) k
  exact hev.comp (measurable_fst.prodMk ((measurable_flr n).comp measurable_snd))

/-! ### Uniformly continuous codes -/

/-- The code is uniformly continuous on the dyadic times of `[0, T]` (a countable condition). -/
def UC (c : PCode) (T : ℝ≥0) : Prop :=
  ∀ m : ℕ, ∃ N : ℕ, ∀ n k n' k', dyad n k ≤ T → dyad n' k' ≤ T →
    |(dyad n k : ℝ) - dyad n' k'| < 1 / (N + 1) → |c n k - c n' k'| ≤ 1 / (m + 1)

theorem measurable_code (n k : ℕ) : Measurable fun c : PCode => c n k :=
  measurable_pi_iff.1 (measurable_pi_apply n) k

theorem measurableSet_UC (T : ℝ≥0) : MeasurableSet {c : PCode | UC c T} := by
  have hset : {c : PCode | UC c T} = ⋂ m : ℕ, ⋃ N : ℕ, ⋂ n : ℕ, ⋂ k : ℕ, ⋂ n' : ℕ, ⋂ k' : ℕ,
      {c : PCode | dyad n k ≤ T → dyad n' k' ≤ T →
        |(dyad n k : ℝ) - dyad n' k'| < 1 / (N + 1) → |c n k - c n' k'| ≤ 1 / (m + 1)} := by
    ext c
    simp only [mem_iInter, mem_iUnion]
    rfl
  rw [hset]
  refine MeasurableSet.iInter fun m => MeasurableSet.iUnion fun N => MeasurableSet.iInter
    fun n => MeasurableSet.iInter fun k => MeasurableSet.iInter fun n' => MeasurableSet.iInter
    fun k' => ?_
  by_cases hp : dyad n k ≤ T ∧ dyad n' k' ≤ T ∧ |(dyad n k : ℝ) - dyad n' k'| < 1 / (N + 1)
  · have e : {c : PCode | dyad n k ≤ T → dyad n' k' ≤ T →
        |(dyad n k : ℝ) - dyad n' k'| < 1 / (N + 1) → |c n k - c n' k'| ≤ 1 / (m + 1)} =
        {c : PCode | |c n k - c n' k'| ≤ 1 / (m + 1)} := by
      ext c
      exact ⟨fun h => h hp.1 hp.2.1 hp.2.2, fun h _ _ _ => h⟩
    rw [e]
    exact measurableSet_le (continuous_abs.measurable.comp
      ((measurable_code n k).sub (measurable_code n' k'))) measurable_const
  · have e : {c : PCode | dyad n k ≤ T → dyad n' k' ≤ T →
        |(dyad n k : ℝ) - dyad n' k'| < 1 / (N + 1) → |c n k - c n' k'| ≤ 1 / (m + 1)} =
        univ := by
      ext c
      exact ⟨fun _ => trivial, fun _ h1 h2 h3 => absurd ⟨h1, h2, h3⟩ hp⟩
    rw [e]
    exact MeasurableSet.univ

theorem UC.mono {c : PCode} {T T' : ℝ≥0} (h : UC c T) (hT : T' ≤ T) : UC c T' := fun m => by
  obtain ⟨N, hN⟩ := h m
  exact ⟨N, fun n k n' k' h1 h2 h3 => hN n k n' k' (h1.trans hT) (h2.trans hT) h3⟩

/-- Near `t`, dyadic times are within `1/(N+1)` of each other. -/
theorem eventually_close {t : ℝ≥0} {u : ℕ → ℝ≥0} (hu : Tendsto u atTop (𝓝 t)) (N : ℕ) :
    ∀ᶠ i in atTop, |(u i : ℝ) - t| < 1 / (2 * (N + 1)) := by
  have hu' : Tendsto (fun i => (u i : ℝ)) atTop (𝓝 (t : ℝ)) := NNReal.tendsto_coe.2 hu
  have hpos : (0 : ℝ) < 1 / (2 * (N + 1)) := by positivity
  filter_upwards [Metric.tendsto_nhds.1 hu' _ hpos] with i hi
  simpa [Real.dist_eq] using hi

theorem close_of_close {x y t : ℝ} {N : ℕ} (hx : |x - t| < 1 / (2 * (N + 1)))
    (hy : |y - t| < 1 / (2 * (N + 1))) : |x - y| < 1 / (N + 1) := by
  have e : (1 : ℝ) / (N + 1) = 1 / (2 * (N + 1)) + 1 / (2 * (N + 1)) := by
    field_simp; ring
  calc |x - y| = |(x - t) - (y - t)| := by ring_nf
    _ ≤ |x - t| + |y - t| := abs_sub _ _
    _ < 1 / (2 * (N + 1)) + 1 / (2 * (N + 1)) := add_lt_add hx hy
    _ = 1 / (N + 1) := e.symm

/-- Along the dyadic floors of `t ≤ T`, a `UC` code is a Cauchy sequence, with limit `dec c t`. -/
theorem UC.tendsto_flr {c : PCode} {T t : ℝ≥0} (h : UC c T) (ht : t ≤ T) :
    Tendsto (fun n => c n (flr n t)) atTop (𝓝 (dec c t)) := by
  have hcau : CauchySeq fun n => c n (flr n t) := by
    rw [Metric.cauchySeq_iff]
    intro ε hε
    obtain ⟨m, hm⟩ := exists_nat_one_div_lt hε
    obtain ⟨N, hN⟩ := h m
    obtain ⟨I, hI⟩ := eventually_atTop.1 (eventually_close (tendsto_dyad_flr t) N)
    refine ⟨I, fun p hp q hq => ?_⟩
    rw [Real.dist_eq]
    exact lt_of_le_of_lt (hN p _ q _ ((dyad_flr_le p t).trans ht) ((dyad_flr_le q t).trans ht)
      (close_of_close (hI p hp) (hI q hq))) hm
  obtain ⟨L, hL⟩ := cauchySeq_tendsto_of_complete hcau
  have : dec c t = L := by unfold dec; exact hL.limsup_eq
  rwa [this]

/-- **Convergence along any dyadic sequence.** -/
theorem UC.tendsto_dec {c : PCode} {T t : ℝ≥0} (h : UC c T) (ht : t ≤ T) {nn kk : ℕ → ℕ}
    (hle : ∀ i, dyad (nn i) (kk i) ≤ T)
    (htend : Tendsto (fun i => dyad (nn i) (kk i)) atTop (𝓝 t)) :
    Tendsto (fun i => c (nn i) (kk i)) atTop (𝓝 (dec c t)) := by
  have hflr := h.tendsto_flr ht
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨m, hm⟩ := exists_nat_one_div_lt (half_pos hε)
  obtain ⟨N, hN⟩ := h m
  obtain ⟨I, hI⟩ := eventually_atTop.1 (eventually_close htend N)
  obtain ⟨J, hJ⟩ := eventually_atTop.1 ((eventually_close (tendsto_dyad_flr t) N).and
    (Metric.tendsto_atTop.1 hflr _ (half_pos hε) |> fun ⟨J, hJ⟩ =>
      eventually_atTop.2 ⟨J, hJ⟩))
  refine ⟨I, fun i hi => ?_⟩
  obtain ⟨hJ1, hJ2⟩ := hJ J le_rfl
  have h1 := hN _ _ _ _ (hle i) ((dyad_flr_le J t).trans ht) (close_of_close (hI i hi) hJ1)
  rw [Real.dist_eq] at hJ2 ⊢
  calc |c (nn i) (kk i) - dec c t|
      ≤ |c (nn i) (kk i) - c J (flr J t)| + |c J (flr J t) - dec c t| := abs_sub_le _ _ _
    _ < ε / 2 + ε / 2 := add_lt_add_of_le_of_lt (h1.trans hm.le) hJ2
    _ = ε := add_halves ε

/-- A `UC` code is the decoded path at its dyadic times. -/
theorem UC.dec_dyad {c : PCode} {T : ℝ≥0} (h : UC c T) {n k : ℕ} (hle : dyad n k ≤ T) :
    dec c (dyad n k) = c n k :=
  tendsto_nhds_unique (h.tendsto_dec hle (nn := fun _ => n) (kk := fun _ => k) (fun _ => hle)
    tendsto_const_nhds) tendsto_const_nhds

/-- **The decoded path of a `UC` code is continuous on `[0, T]`.** -/
theorem UC.continuousOn {c : PCode} {T : ℝ≥0} (h : UC c T) : ContinuousOn (dec c) (Iic T) := by
  rw [Metric.continuousOn_iff]
  intro t ht ε hε
  obtain ⟨m, hm⟩ := exists_nat_one_div_lt hε
  obtain ⟨N, hN⟩ := h m
  refine ⟨1 / (2 * (N + 1)), by positivity, fun t' ht' hd => ?_⟩
  have hd' : |(t' : ℝ) - t| < 1 / (2 * (N + 1)) := by
    rw [NNReal.dist_eq] at hd; exact hd
  have hlim := ((h.tendsto_flr ht').sub (h.tendsto_flr ht)).abs
  have hle : |dec c t' - dec c t| ≤ 1 / (m + 1) := by
    refine le_of_tendsto hlim ?_
    have hdiff : Tendsto (fun n => ((dyad n (flr n t') : ℝ) - dyad n (flr n t))) atTop
        (𝓝 ((t' : ℝ) - t)) :=
      (NNReal.tendsto_coe.2 (tendsto_dyad_flr t')).sub (NNReal.tendsto_coe.2 (tendsto_dyad_flr t))
    have hnear : ∀ᶠ n in atTop, |((dyad n (flr n t') : ℝ) - dyad n (flr n t))| < 1 / (N + 1) := by
      have hlt : |(t' : ℝ) - t| < 1 / (N + 1) := by
        refine lt_of_lt_of_le hd' ?_
        rw [div_le_div_iff₀ (by positivity) (by positivity)]
        nlinarith
      exact (continuous_abs.tendsto _ |>.comp hdiff).eventually (gt_mem_nhds hlt)
    filter_upwards [hnear] with n hn
    exact hN _ _ _ _ ((dyad_flr_le n t').trans ht') ((dyad_flr_le n t).trans ht) hn
  rw [Real.dist_eq]
  exact lt_of_le_of_lt hle hm

/-- **Codes of continuous paths are `UC`** (Heine–Cantor on `[0, T]`). -/
theorem uc_enc {f : ℝ≥0 → ℝ} {T : ℝ≥0} (hf : ContinuousOn f (Iic T)) : UC (enc f) T := by
  have hcpt : IsCompact (Iic T) := by
    rw [← Icc_bot]; exact isCompact_Icc
  have huc := hcpt.uniformContinuousOn_of_continuous hf
  rw [Metric.uniformContinuousOn_iff] at huc
  intro m
  obtain ⟨δ, hδ, hδ'⟩ := huc (1 / (m + 1)) (by positivity)
  obtain ⟨N, hN⟩ := exists_nat_one_div_lt hδ
  refine ⟨N, fun n k n' k' h1 h2 h3 => ?_⟩
  have := hδ' _ h1 _ h2 (by rw [NNReal.dist_eq]; exact lt_trans h3 hN)
  rw [Real.dist_eq] at this
  exact this.le

end Assembly

end Sec2

end InteractingSLE
