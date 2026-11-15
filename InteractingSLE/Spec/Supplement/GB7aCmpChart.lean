/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GB7aCmpLoewner
import InteractingSLE.Spec.Supplement.Aux61Cutoff

/-!
# GB7a's pathwise comparison input: the chart at a restart time

Packet PROVE-GB7A3. A chordal Loewner chain driven by a continuous `U` (`U 0 = 0`) with a continuous trace `η`
before `T`, a restart time `q < T` after which the trace stays in `ℍ` and off its past, and a real limit
`η(s) → y > 0` as `s ↑ T`. In the chart at `q`:

* `exists_cutParams`: cut parameters (Aux. lemma 61's two-core cutoff, `Aux61Cutoff`) adapted to a chart trace
  that starts at `0`, stays in `ℍ`, and ends at a real point `V > 0`, avoiding finitely many real marks;
* `exists_isForwardSol_at_restart`: `y` is alive at `q`;
* `eq_zero_of_tendsto_restart`: a positive force coordinate below the real flow of `y` at `q` tends to `0` at `T`
  (otherwise `y` would stay alive through `T`, while the trace reaches it from inside the hulls);
* `exists_energy_bound_of_restart`: **the energy bound** — for weights `c_j` on finitely many force coordinates
  that stay off the driver on `[q, T)`, avoid the chart target `V = f_q(y)` at `q`, and whose weights between the
  driver and the target sum to `0`, the drift energy `∫_q^t (∑ⱼ cⱼ/ûⱼ)²` is bounded for `t < T`
  (`exists_markDrift_energy_le`, Aux. lemma 61).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Filter Set Topology Metric Finset
open scoped NNReal ENNReal

namespace InteractingSLE

namespace GB7a

open QuantumZipper (H Hbar fwdMap fwdHull fwdMapInv IsForwardSol)
open QuantumZipper.RS (shiftDrive)

/-! ### Cut parameters adapted to a chart trace -/

/-- A uniform positive lower bound for finitely many positive reals. -/
theorem exists_pos_le_of_fintype {ι : Type*} [Finite ι] (f : ι → ℝ) (hf : ∀ i, 0 < f i) :
    ∃ δ > 0, ∀ i, δ ≤ f i := by
  rcases isEmpty_or_nonempty ι with hι | hι
  · exact ⟨1, one_pos, fun i => isEmptyElim i⟩
  · obtain ⟨i₀, hi₀⟩ := Finite.exists_min f
    exact ⟨f i₀, hf i₀, hi₀⟩

/-- **Cut parameters for a chart trace.** Let `γ` be continuous on `[0, τ)` with `γ 0 = 0`, in `ℍ` on `(0, τ)`, and
`γ(u) → V > 0` as `u ↑ τ`, and let `p` be finitely many real marks off `0` and `V`. Then there are valid cut
parameters whose zero core avoids the marks, whose target core `(a₁, b₁)` contains `V` and separates the marks
below `V` from those above, and whose region `cutU` contains `γ([0, τ))`. -/
theorem exists_cutParams {τ V : ℝ} (hτ : 0 < τ) (hV : 0 < V) {γ : ℝ → ℂ}
    (hγc : ContinuousOn γ (Ico 0 τ)) (hγ0 : γ 0 = 0) (hγH : ∀ u ∈ Ioo 0 τ, γ u ∈ H)
    (hγlim : Tendsto γ (𝓝[<] τ) (𝓝 (V : ℂ))) {ι : Type*} [Fintype ι] {p : ι → ℝ}
    (hp0 : ∀ j, p j ≠ 0) (hpV : ∀ j, p j ≠ V) :
    ∃ P : CutParams, P.Valid ∧ (∀ j, P.a₀ + P.μ < |p j|) ∧ (∀ j, p j < V → p j < P.a₁ - P.μ) ∧
      (∀ j, V < p j → P.b₁ + P.μ < p j) ∧ V < P.b₁ + P.μ ∧ ∀ u ∈ Ico 0 τ, γ u ∈ cutU P := by
  -- the separation scale `d`
  obtain ⟨δ, hδ, hδle⟩ := exists_pos_le_of_fintype (fun j => min |p j| |p j - V|) fun j =>
    lt_min (abs_pos.2 (hp0 j)) (abs_pos.2 (sub_ne_zero.2 (hpV j)))
  set d := min V δ with hd
  have hd0 : 0 < d := lt_min hV hδ
  have hdV : d ≤ V := min_le_left _ _
  have hdp : ∀ j, d ≤ |p j| := fun j => (min_le_right _ _).trans ((hδle j).trans (min_le_left _ _))
  have hdpV : ∀ j, d ≤ |p j - V| := fun j =>
    (min_le_right _ _).trans ((hδle j).trans (min_le_right _ _))
  -- near `0`
  obtain ⟨δ₁, hδ₁, h₁⟩ := Metric.continuousWithinAt_iff.1 (hγc 0 ⟨le_rfl, hτ⟩) (d / 8) (by positivity)
  -- near `τ`
  obtain ⟨δ₂, hδ₂, h₂⟩ := Metric.tendsto_nhdsWithin_nhds.1 hγlim (d / 8) (by positivity)
  -- the middle
  set a := min (δ₁ / 2) (τ / 2) with ha
  set b := max (τ - δ₂ / 2) (τ / 2) with hb
  have ha0 : 0 < a := lt_min (by positivity) (by positivity)
  have hbτ : b < τ := max_lt (by linarith) (by linarith)
  have hab : a ≤ b := (min_le_right _ _).trans (le_max_right _ _)
  have hMsub : Icc a b ⊆ Ioo 0 τ := fun u hu => ⟨ha0.trans_le hu.1, hu.2.trans_lt hbτ⟩
  have hMc : ContinuousOn γ (Icc a b) := hγc.mono fun u hu => ⟨(hMsub hu).1.le, (hMsub hu).2⟩
  obtain ⟨u₀, hu₀, hmin⟩ := isCompact_Icc.exists_isMinOn (nonempty_Icc.2 hab)
    (Complex.continuous_im.comp_continuousOn hMc)
  set m := (γ u₀).im with hm
  have hm0 : 0 < m := hγH u₀ (hMsub hu₀)
  obtain ⟨B, hB⟩ := isCompact_Icc.exists_bound_of_continuousOn hMc
  set μ := min (d / 16) (m / 4) with hμ
  have hμ0 : 0 < μ := lt_min (by positivity) (by positivity)
  have hμd : μ ≤ d / 16 := min_le_left _ _
  have hμm : μ ≤ m / 4 := min_le_right _ _
  have hB0 : 0 ≤ B := (norm_nonneg _).trans (hB a ⟨le_rfl, hab⟩)
  refine ⟨⟨d / 4, V - d / 4, V + d / 4, μ, B + V + d + 1 + μ⟩, ⟨hμ0, ?_, ?_, ?_, ?_⟩, fun j => ?_,
    fun j hj => ?_, fun j hj => ?_, ?_, fun u hu => ?_⟩
  · show 3 * μ < d / 4
    linarith
  · show d / 4 + μ < V - d / 4 - μ
    linarith
  · show V - d / 4 + 3 * μ < V + d / 4 - 3 * μ
    linarith
  · show 0 < B + V + d + 1 + μ
    linarith
  · show d / 4 + μ < |p j|
    linarith [hdp j]
  · show p j < V - d / 4 - μ
    have h := hdpV j
    rw [abs_of_neg (by linarith)] at h
    linarith
  · show V + d / 4 + μ < p j
    have h := hdpV j
    rw [abs_of_pos (by linarith)] at h
    linarith
  · show V < V + d / 4 + μ
    linarith
  · show ‖γ u‖ < B + V + d + 1 + μ - μ ∧
      (3 * μ < (γ u).im ∨ |(γ u).re| < d / 4 - 2 * μ ∨ (γ u).re ∈ Ioo (V - d / 4 + 2 * μ) (V + d / 4 - 2 * μ))
    rcases lt_or_ge u a with hua | hua
    · -- near `0`
      have hu1 : dist u 0 < δ₁ := by
        rw [Real.dist_eq, sub_zero, abs_of_nonneg hu.1]
        exact hua.trans_le ((min_le_left _ _).trans (by linarith))
      have hγu := h₁ hu hu1
      rw [dist_eq_norm, hγ0, sub_zero] at hγu
      refine ⟨by linarith, Or.inr (Or.inl ?_)⟩
      exact (Complex.abs_re_le_norm _).trans_lt (by linarith)
    rcases le_or_gt u b with hub | hub
    · -- the middle
      have hmid := hmin ⟨hua, hub⟩
      have hBu := hB u ⟨hua, hub⟩
      have hmid' : m ≤ (γ u).im := hmid
      exact ⟨by linarith, Or.inl (by linarith)⟩
    · -- near `τ`
      have hu2 : dist u τ < δ₂ := by
        rw [Real.dist_eq, abs_of_neg (by linarith [hu.2]), neg_sub]
        have : τ - δ₂ / 2 ≤ b := le_max_left _ _
        linarith
      have hγu := h₂ hu.2 hu2
      rw [dist_eq_norm] at hγu
      have hre : |(γ u).re - V| < d / 8 := by
        have := Complex.abs_re_le_norm (γ u - V)
        rw [Complex.sub_re, Complex.ofReal_re] at this
        linarith
      have hnorm : ‖γ u‖ < V + d / 8 := by
        have := norm_sub_norm_le (γ u) (V : ℂ)
        rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hV] at this
        linarith
      refine ⟨by linarith, Or.inr (Or.inr ⟨?_, ?_⟩)⟩
      · linarith [neg_abs_le ((γ u).re - V)]
      · linarith [le_abs_self ((γ u).re - V)]

/-! ### The restart time -/

section Restart

variable {U : ℝ → ℝ} {T : ℝ} {η : ℝ → ℂ} {q : ℝ}

/-- The trace after the restart time `q` (in `ℍ` and off the prefix) is interior in the chart at `q`. -/
theorem chart_of_restart (hη : IsLoewnerTraceLT U T η) (hU : Continuous U) (hU0 : U 0 = 0) (hq : 0 ≤ q)
    (hH : ∀ s ∈ Ioo q T, η s ∈ H) (hinj : ∀ s ∈ Ioo q T, η s ∉ η '' Icc 0 q) {s : ℝ}
    (hs : s ∈ Ioo q T) :
    loewnerTip (shiftDrive U q) (s - q) ∈ H ∧ fwdMap U q (η s) = loewnerTip (shiftDrive U q) (s - q) ∧
      η s ∈ H \ fwdHull U q := by
  have e : q + (s - q) = s := by ring
  have h := hη.chart_of_mem_H hU hU0 hq (sub_nonneg.2 hs.1.le) (by rw [e]; exact hs.2)
    (by rw [e]; exact hH s hs) (by rw [e]; exact hinj s hs)
  rw [e] at h
  exact h

/-- **The real limit point is alive at the restart time.** -/
theorem exists_isForwardSol_at_restart (hη : IsLoewnerTraceLT U T η) (hU : Continuous U) (hU0 : U 0 = 0)
    (hq : 0 ≤ q) (hqT : q < T) (hH : ∀ s ∈ Ioo q T, η s ∈ H)
    (hinj : ∀ s ∈ Ioo q T, η s ∉ η '' Icc 0 q) {y : ℝ} (hy0 : y ≠ 0)
    (hlim : Tendsto η (𝓝[<] T) (𝓝 (y : ℂ))) (hyq : (y : ℂ) ∉ η '' Icc 0 q) :
    ∃ v, IsForwardSol U (y : ℂ) q v := by
  refine exists_isForwardSol_of_mem_closure hU hU0 hη hq hqT hy0 hyq ?_
  refine mem_closure_of_tendsto hlim ?_
  filter_upwards [Ioo_mem_nhdsLT hqT] with s hs
  exact (chart_of_restart hη hU hU0 hq hH hinj hs).2.2

/-- **The force coordinate below the target collides at `T`.** If a force coordinate `u` is positive on
`[q, T)`, starts at or below the real flow of `y` at `q`, and has a limit `L` at `T⁻`, then `L = 0`: otherwise
`y` would stay alive through `T` (`exists_isForwardSol_of_le`), while the trace reaches it from the hulls. -/
theorem eq_zero_of_tendsto_restart (hη : IsLoewnerTraceLT U T η) (hU : Continuous U) (hU0 : U 0 = 0)
    (hq : 0 ≤ q) (hqT : q < T) (hH : ∀ s ∈ Ioo q T, η s ∈ H) {y : ℝ} (hy : 0 < y)
    (hlim : Tendsto η (𝓝[<] T) (𝓝 (y : ℂ))) {v : ℝ → ℂ} (hv : IsForwardSol U (y : ℂ) q v)
    {u : ℝ → ℝ}
    (hu : ∀ s ∈ Ico q T, ContinuousOn u (Icc q s) ∧
      (∀ s₁ ∈ Icc q s, ∀ s₂ ∈ Icc q s, s₁ ≤ s₂ →
        u s₂ - u s₁ = -(U s₂ - U s₁) + ∫ r in s₁..s₂, 2 / u r) ∧
      IntervalIntegrable (fun r => 2 / u r) volume q s)
    (hpos : ∀ s ∈ Ico q T, 0 < u s) (huq : u q ≤ (v q).re) {L : ℝ}
    (hL : Tendsto u (𝓝[<] T) (𝓝 L)) : L = 0 := by
  have hL0 : 0 ≤ L := ge_of_tendsto hL (by
    filter_upwards [Ico_mem_nhdsLT hqT] with s hs using (hpos s hs).le)
  by_contra hne
  have hLpos : 0 < L := lt_of_le_of_ne hL0 (Ne.symm hne)
  obtain ⟨c, hc, hcu⟩ : ∃ c > 0, ∀ s ∈ Ico q T, c ≤ u s := by
    have hev : ∀ᶠ s in 𝓝[<] T, L / 2 < u s := hL (lt_mem_nhds (by linarith))
    obtain ⟨T₁, hT₁, hT₁sub⟩ := (mem_nhdsLT_iff_exists_Ioo_subset).1 hev
    have hT₂ : max T₁ q < T := max_lt hT₁ hqT
    obtain ⟨huc, -, -⟩ := hu (max T₁ q) ⟨le_max_right _ _, hT₂⟩
    obtain ⟨s₀, hs₀, hmin⟩ := isCompact_Icc.exists_isMinOn (nonempty_Icc.2 (le_max_right T₁ q)) huc
    refine ⟨min (u s₀) (L / 2), lt_min (hpos s₀ ⟨hs₀.1, hs₀.2.trans_lt hT₂⟩) (by linarith),
      fun s hs => ?_⟩
    rcases le_or_gt s (max T₁ q) with h | h
    · exact (min_le_left _ _).trans (hmin ⟨hs.1, h⟩)
    · exact (min_le_right _ _).trans (hT₁sub ⟨(le_max_left _ _).trans_lt h, hs.2⟩).le
  have halive := exists_isForwardSol_of_le hU hU0 hy hq hqT.le hv hc hu hcu huq
  refine not_isForwardSol_of_tendsto hU (p := (q + T) / 2) (by linarith) (hq.trans hqT.le)
    (fun s hs => ?_) hlim halive
  have hs0 : 0 ≤ s := by linarith [hs.1]
  rw [hη.2.2 s hs0 hs.2]
  exact ⟨hH s ⟨by linarith [hs.1], hs.2⟩, Or.inl (subset_closure ⟨s, ⟨hs0, le_rfl⟩, rfl⟩)⟩

/-- **The drift energy after the restart time is bounded** (Aux. lemma 61 in the chart at `q`). Let finitely many
force coordinates `ûⱼ` solve the centred equation on `[q, s]` for every `s < T`, stay off the driver on `[q, T)`,
and avoid the chart target `V = Re v(q)` (the real flow of the limit point `y` at `q`) at time `q`; let the weights
`cⱼ` of the coordinates strictly between the driver and the target sum to `0`. Then `∫_q^t (∑ⱼ cⱼ/ûⱼ)²` is
bounded for `t ∈ [q, T)`. -/
theorem exists_energy_bound_of_restart (hη : IsLoewnerTraceLT U T η) (hU : Continuous U) (hU0 : U 0 = 0)
    (hq : 0 ≤ q) (hqT : q < T) (hH : ∀ s ∈ Ioo q T, η s ∈ H)
    (hinj : ∀ s ∈ Ioo q T, η s ∉ η '' Icc 0 q) {y : ℝ} (hy : 0 < y)
    (hlim : Tendsto η (𝓝[<] T) (𝓝 (y : ℂ))) {v : ℝ → ℂ} (hv : IsForwardSol U (y : ℂ) q v)
    {ι : Type*} [Fintype ι] (û : ι → ℝ → ℝ) (c : ι → ℝ)
    (hpkg : ∀ j, ∀ s ∈ Ico q T, ContinuousOn (û j) (Icc q s) ∧
      ∀ s₁ ∈ Icc q s, ∀ s₂ ∈ Icc q s, s₁ ≤ s₂ →
        û j s₂ - û j s₁ = -(U s₂ - U s₁) + ∫ r in s₁..s₂, 2 / û j r)
    (hne : ∀ j, ∀ s ∈ Ico q T, û j s ≠ 0) (hsep : ∀ j, û j q ≠ (v q).re)
    (hcore : ∑ j ∈ univ.filter (fun j => 0 < û j q ∧ û j q < (v q).re), c j = 0) :
    ∃ C, ∀ t ∈ Ico q T, ∫ s in q..t, (∑ j, c j / û j s) ^ 2 ≤ C := by
  set V := (v q).re with hVdef
  obtain ⟨c₁, hc₁, hc₁le⟩ := exists_pos_le_re_of_isForwardSol hU hU0 hy hq hv
  have hV : 0 < V := hc₁.trans_le (hc₁le q ⟨hq, le_rfl⟩)
  have hvq : v q = (V : ℂ) := Complex.ext (by simp [hVdef])
    (by rw [Complex.ofReal_im]; exact im_eq_zero_of_isForwardSol_real hU hv ⟨hq, le_rfl⟩)
  set τ := T - q with hτ
  have hτ0 : 0 < τ := sub_pos.2 hqT
  have hqτ : q + τ = T := by rw [hτ]; ring
  set γ := loewnerTip (shiftDrive U q) with hγ
  have hS : IsLoewnerTraceLT (shiftDrive U q) τ γ := (hη.isLoewnerTraceLT_shift hU hU0 hq).1
  have hUS := QuantumZipper.RS.continuous_shiftDrive hU q
  have hUS0 := QuantumZipper.RS.shiftDrive_zero U q
  have hchart : ∀ u ∈ Ioo 0 τ, γ u ∈ H ∧ fwdMap U q (η (q + u)) = γ u := fun u hu => by
    have hs : q + u ∈ Ioo q T := ⟨by linarith [hu.1], by linarith [hu.2]⟩
    have h := chart_of_restart hη hU hU0 hq hH hinj hs
    rw [add_sub_cancel_left] at h
    exact ⟨h.1, h.2.1⟩
  -- the chart trace tends to `V`
  have hγlim : Tendsto γ (𝓝[<] τ) (𝓝 (V : ℂ)) := by
    have h1 : Tendsto (fun u => q + u) (𝓝[<] τ) (𝓝[<] T) := by
      have hc : Tendsto (fun u => q + u) (𝓝 τ) (𝓝 T) := by
        have : Tendsto (fun u : ℝ => q + u) (𝓝 τ) (𝓝 (q + τ)) :=
          ((continuous_const (y := q)).add continuous_id).tendsto τ
        rwa [hqτ] at this
      refine tendsto_nhdsWithin_iff.2 ⟨hc.mono_left nhdsWithin_le_nhds, ?_⟩
      filter_upwards [self_mem_nhdsWithin] with u hu
      show q + u < T
      have : u < τ := hu
      linarith
    have h2 : Tendsto (fun u => η (q + u)) (𝓝[<] τ) (𝓝[H] (y : ℂ)) := by
      refine tendsto_nhdsWithin_iff.2 ⟨hlim.comp h1, ?_⟩
      filter_upwards [Ioo_mem_nhdsLT hτ0] with u hu
      exact hH (q + u) ⟨by linarith [hu.1], by linarith [hu.2]⟩
    have h3 := (tendsto_fwdMap_of_isForwardSol_real hU hU0 hq hv).comp h2
    rw [hvq] at h3
    refine h3.congr' ?_
    filter_upwards [Ioo_mem_nhdsLT hτ0] with u hu using (hchart u hu).2
  -- the cut configuration
  set p : ι → ℝ := fun j => û j q with hp
  obtain ⟨P, hP, h0, hlo, hhi, hVb, hcut⟩ := exists_cutParams hτ0 hV hS.2.1 hS.1
    (fun u hu => (hchart u hu).1) hγlim (p := p) (fun j => hne j q ⟨le_rfl, hqT⟩) hsep
  set c₀ := -(Real.pi * ∑ j ∈ univ.filter (fun j => 0 < p j), c j) with hc₀
  have hC : CutConfig P p c c₀ :=
    { avoid0 := h0
      avoid1 := fun j => (lt_or_gt_of_ne (hsep j)).imp (hlo j) (hhi j)
      seed := by rw [hc₀]; ring
      core := by
        have hsplit := Finset.sum_filter_add_sum_filter_not (univ.filter (fun j => 0 < p j))
          (fun j => p j < V) c
        rw [Finset.filter_filter, Finset.filter_filter] at hsplit
        have e2 : univ.filter (fun j => 0 < p j ∧ ¬ p j < V) =
            univ.filter (fun j => P.b₁ + P.μ ≤ p j) := by
          ext j
          simp only [Finset.mem_filter, Finset.mem_univ, true_and]
          constructor
          · rintro ⟨-, h2⟩
            exact (hhi j (lt_of_le_of_ne (not_lt.1 h2) (Ne.symm (hsep j)))).le
          · intro h
            exact ⟨by linarith, not_lt.2 (by linarith)⟩
        rw [hcore, zero_add, e2] at hsplit
        rw [hc₀, ← hsplit]
        ring }
  obtain ⟨C, hCb⟩ := exists_markDrift_energy_le hP hC
  refine ⟨max C 0, fun t ht => ?_⟩
  rcases ht.1.eq_or_lt with htq | htq
  · rw [← htq, intervalIntegral.integral_same]
    exact le_max_right _ _
  set t' := t - q with ht'def
  have ht' : 0 < t' := sub_pos.2 htq
  have ht'τ : t' < τ := by linarith [ht.2]
  have hsol : ∀ j, IsForwardSol (shiftDrive U q) (p j : ℂ) t' (fun s => (û j (q + s) : ℂ)) := fun j => by
    obtain ⟨hc, heq⟩ := hpkg j t ht
    exact isForwardSol_shift_of_centred ht.1 hc (fun s hs => hne j s ⟨hs.1, hs.2.trans_lt ht.2⟩) heq
  have hreal : ∀ s ∈ Icc (0 : ℝ) t', γ s ∈ Hbar ∧ ((γ s).im = 0 → γ s = 0) := by
    intro s hs
    rcases hs.1.eq_or_lt with h | h
    · rw [← h, hS.1]
      exact ⟨show (0 : ℝ) ≤ (0 : ℂ).im by simp, fun _ => rfl⟩
    · have hH' : 0 < (γ s).im := (hchart s ⟨h, hs.2.trans_lt ht'τ⟩).1
      exact ⟨show 0 ≤ (γ s).im from hH'.le, fun h0 => absurd h0 hH'.ne'⟩
  have hbound := hCb (shiftDrive U q) t' γ hUS hUS0 ht'
    (hS.2.1.mono fun s hs => ⟨hs.1, hs.2.trans_lt ht'τ⟩)
    (fun s hs => hS.2.2 s hs.1.le (hs.2.trans_lt ht'τ))
    (by rintro _ ⟨s, hs, rfl⟩; exact hcut s ⟨hs.1, hs.2.trans_lt ht'τ⟩)
    hreal (fun j => ⟨_, hsol j⟩) t' ⟨ht'.le, le_rfl⟩
  have hdrift : ∀ s ∈ uIcc 0 t', markDrift (shiftDrive U q) p c s ^ 2 =
      (∑ j, c j / û j (q + s)) ^ 2 := by
    intro s hs
    rw [uIcc_of_le ht'.le] at hs
    simp only [markDrift]
    congr 1
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [fwdMap_eq_of_isForwardSol hUS (hsol j) hs, Complex.ofReal_re]
  rw [intervalIntegral.integral_congr hdrift] at hbound
  have e := intervalIntegral.integral_comp_add_left (fun s => (∑ j, c j / û j s) ^ 2) q (a := 0)
    (b := t')
  simp only [add_zero] at e
  rw [e, ht'def, add_sub_cancel] at hbound
  exact hbound.trans (le_max_left _ _)

end Restart

end GB7a

end InteractingSLE
