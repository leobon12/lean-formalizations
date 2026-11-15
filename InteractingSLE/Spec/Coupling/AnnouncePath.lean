/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Coupling.AnnounceSelect
import InteractingSLE.Spec.Sec2.TerminalPath

/-!
# Announcing the lifetime along one driving path

Packet PROVE-T11-ANN, Theorem 1.1 by the route of ruling R35 (`source/external/AstraIG1/ig1_formalization_proofs.pdf`
§1, (1.2); the predictability of the lifetime asserted in Aux. lemma 3, Specification p. 24). This file is the
deterministic half: for one path of the integrated evolution, the candidate hitting times

`a_{j,m,k} = inf {s < ζ : |w_s − v^{j,L}_s| + (1/(m+1) − (v^{j,L}_s − v^{j+1,L}_s))⁺ < 1/(k+1)}`

for every left cluster size `j + 1` with `∑_{i ≤ j} ρ^{i,L} ≤ −2` and every gap level `m` (and their reflections on the
right), either eventually leave every bounded interval, or stay strictly below `ζ` and increase to it. The zero set of
the functional is the part `{v^{j,L} = w, gap ≥ 1/(m+1)}` of the threshold set, which is closed; the full threshold set
is not, and a "distance to the threshold" may tend to zero at a time before `ζ` when two force points merge at the
moment they hit the driver. Merged force points stay merged: the gaps `v^{j,L} − v^{j+1,L}` are nonincreasing
(`sideGap_vL_anti`), so along a bounded candidate the gap is at least `1/(m+1)` for the whole lifetime and the
candidate equals the hitting sequence of `|w − v^{j,L}|`, independent of `m` (`hitL_eq_of_bdd`). At a finite
lifetime, Aux. lemma 3's terminal state (a whole cluster at the driver, the next point strictly below) makes the
candidate of that cluster and of a large level `m` bounded (`exists_bdd_hitL`).

## Main results

* `hitBelow`: the first time before `ζ` at which a function is below a level, with its order and continuity lemmas;
* `sideGap_vL_anti`: merged force points stay merged;
* `hitL`: the candidates; `pos_sideVal`, `hitL_lt_of_bdd`, `eventually_le_hitL`, `le_sideGap_of_bdd`, `hitL_eq_of_bdd`,
  `exists_bdd_hitL`.
-/

set_option autoImplicit false

noncomputable section

open Set Filter MeasureTheory Topology
open scoped NNReal ENNReal

namespace InteractingSLE

namespace Coupling

/-! ### First time below a level before `ζ` -/

section HitBelow

open scoped Classical in
/-- The first time before `ζ` at which `f < ε` (`⊤` if there is none). -/
def hitBelow (f : ℝ≥0 → ℝ) (ζ : ℝ≥0∞) (ε : ℝ) : WithTop ℝ≥0 :=
  if {s : ℝ≥0 | (s : ℝ≥0∞) < ζ ∧ f s < ε}.Nonempty then
    ((sInf {s : ℝ≥0 | (s : ℝ≥0∞) < ζ ∧ f s < ε} : ℝ≥0) : WithTop ℝ≥0) else ⊤

variable {f g : ℝ≥0 → ℝ} {ζ : ℝ≥0∞} {ε ε' : ℝ}

theorem hitBelow_of_nonempty (h : {s : ℝ≥0 | (s : ℝ≥0∞) < ζ ∧ f s < ε}.Nonempty) :
    hitBelow f ζ ε = ((sInf {s : ℝ≥0 | (s : ℝ≥0∞) < ζ ∧ f s < ε} : ℝ≥0) : WithTop ℝ≥0) := by
  simp only [hitBelow, h, ↓reduceIte]

theorem hitBelow_of_not_nonempty (h : ¬ {s : ℝ≥0 | (s : ℝ≥0∞) < ζ ∧ f s < ε}.Nonempty) :
    hitBelow f ζ ε = ⊤ := by
  simp only [hitBelow, h, ↓reduceIte]

theorem hitBelow_le {s : ℝ≥0} (hs : (s : ℝ≥0∞) < ζ) (hfs : f s < ε) : hitBelow f ζ ε ≤ s := by
  rw [hitBelow_of_nonempty ⟨s, hs, hfs⟩]
  exact WithTop.coe_le_coe.2 (csInf_le (OrderBot.bddBelow _) ⟨hs, hfs⟩)

theorem le_hitBelow {t : ℝ≥0} (h : ∀ s : ℝ≥0, (s : ℝ≥0∞) < ζ → f s < ε → t ≤ s) :
    (t : WithTop ℝ≥0) ≤ hitBelow f ζ ε := by
  by_cases hne : {s : ℝ≥0 | (s : ℝ≥0∞) < ζ ∧ f s < ε}.Nonempty
  · rw [hitBelow_of_nonempty hne]
    exact WithTop.coe_le_coe.2 (le_csInf hne fun s hs => h s hs.1 hs.2)
  · rw [hitBelow_of_not_nonempty hne]
    exact le_top

/-- A lower level is reached later. -/
theorem hitBelow_anti (h : ε' ≤ ε) : hitBelow f ζ ε ≤ hitBelow f ζ ε' := by
  by_cases hne : {s : ℝ≥0 | (s : ℝ≥0∞) < ζ ∧ f s < ε'}.Nonempty
  · have hsub : {s : ℝ≥0 | (s : ℝ≥0∞) < ζ ∧ f s < ε'} ⊆ {s : ℝ≥0 | (s : ℝ≥0∞) < ζ ∧ f s < ε} :=
      fun s hs => ⟨hs.1, hs.2.trans_le h⟩
    rw [hitBelow_of_nonempty hne, hitBelow_of_nonempty (hne.mono hsub)]
    exact WithTop.coe_le_coe.2 (csInf_le_csInf (OrderBot.bddBelow _) hne hsub)
  · rw [hitBelow_of_not_nonempty hne]
    exact le_top

theorem hitBelow_congr (h : ∀ s : ℝ≥0, (s : ℝ≥0∞) < ζ → f s = g s) :
    hitBelow f ζ ε = hitBelow g ζ ε := by
  have hS : {s : ℝ≥0 | (s : ℝ≥0∞) < ζ ∧ f s < ε} = {s : ℝ≥0 | (s : ℝ≥0∞) < ζ ∧ g s < ε} := by
    ext s
    simp only [mem_ofPred_eq]
    constructor
    · rintro ⟨h1, h2⟩; exact ⟨h1, h s h1 ▸ h2⟩
    · rintro ⟨h1, h2⟩; exact ⟨h1, (h s h1).symm ▸ h2⟩
  unfold hitBelow
  rw [hS]

theorem nonempty_of_hitBelow_eq {t : ℝ≥0} (h : hitBelow f ζ ε = t) :
    {s : ℝ≥0 | (s : ℝ≥0∞) < ζ ∧ f s < ε}.Nonempty := by
  by_contra hne
  rw [hitBelow_of_not_nonempty hne] at h
  exact WithTop.top_ne_coe h

theorem sInf_eq_of_hitBelow_eq {t : ℝ≥0} (h : hitBelow f ζ ε = t) :
    sInf {s : ℝ≥0 | (s : ℝ≥0∞) < ζ ∧ f s < ε} = t := by
  rw [hitBelow_of_nonempty (nonempty_of_hitBelow_eq h)] at h
  exact WithTop.coe_inj.1 h

/-- A finite hitting time is strictly before `ζ`. -/
theorem lt_of_hitBelow_eq {t : ℝ≥0} (h : hitBelow f ζ ε = t) : (t : ℝ≥0∞) < ζ := by
  obtain ⟨s, hs⟩ := nonempty_of_hitBelow_eq h
  have hts : t ≤ s := sInf_eq_of_hitBelow_eq h ▸ csInf_le (OrderBot.bddBelow _) hs
  exact lt_of_le_of_lt (by exact_mod_cast hts) hs.1

theorem isOpen_setOf_coe_lt (ζ : ℝ≥0∞) : IsOpen {s : ℝ≥0 | (s : ℝ≥0∞) < ζ} :=
  isOpen_lt ENNReal.continuous_coe continuous_const

/-- At a finite hitting time, the level is reached: `f t ≤ ε`. -/
theorem le_of_hitBelow_eq (hf : ContinuousOn f {s : ℝ≥0 | (s : ℝ≥0∞) < ζ}) {t : ℝ≥0}
    (h : hitBelow f ζ ε = t) : f t ≤ ε := by
  have htζ := lt_of_hitBelow_eq h
  have hmem : t ∈ closure {s : ℝ≥0 | (s : ℝ≥0∞) < ζ ∧ f s < ε} :=
    sInf_eq_of_hitBelow_eq h ▸ csInf_mem_closure (nonempty_of_hitBelow_eq h) (OrderBot.bddBelow _)
  by_contra hlt
  rw [not_le] at hlt
  have hcont : ContinuousAt f t := hf.continuousAt ((isOpen_setOf_coe_lt ζ).mem_nhds htζ)
  obtain ⟨s, hs1, hs2⟩ := mem_closure_iff_nhds.1 hmem _ (hcont.eventually (lt_mem_nhds hlt))
  exact absurd hs2.2 (not_lt.2 hs1.le)

/-- **The hitting time is determined on a dense set of times**: `hitBelow f ζ ε < t` iff `f < ε` at some `d < t`,
`d < ζ`, of a dense set `D`. -/
theorem hitBelow_lt_iff (hf : ContinuousOn f {s : ℝ≥0 | (s : ℝ≥0∞) < ζ}) {D : Set ℝ≥0} (hD : Dense D)
    (t : ℝ≥0) :
    hitBelow f ζ ε < t ↔ ∃ d ∈ D, d < t ∧ (d : ℝ≥0∞) < ζ ∧ f d < ε := by
  constructor
  · intro h
    have hne : hitBelow f ζ ε ≠ ⊤ := ne_top_of_lt h
    obtain ⟨u, hu⟩ := WithTop.ne_top_iff_exists.1 hne
    have hut : u < t := by rw [← hu] at h; exact WithTop.coe_lt_coe.1 h
    have hS := sInf_eq_of_hitBelow_eq hu.symm
    obtain ⟨s, ⟨hsζ, hfs⟩, hst⟩ := exists_lt_of_csInf_lt (nonempty_of_hitBelow_eq hu.symm)
      (hS.symm ▸ hut)
    have hV : IsOpen ({r : ℝ≥0 | (r : ℝ≥0∞) < ζ} ∩ f ⁻¹' Iio ε ∩ Iio t) :=
      (hf.isOpen_inter_preimage (isOpen_setOf_coe_lt ζ) isOpen_Iio).inter isOpen_Iio
    obtain ⟨d, ⟨⟨hdζ, hfd⟩, hdt⟩, hdD⟩ := hD.inter_open_nonempty _ hV ⟨s, ⟨hsζ, hfs⟩, hst⟩
    exact ⟨d, hdD, hdt, hdζ, hfd⟩
  · rintro ⟨d, -, hdt, hdζ, hfd⟩
    exact lt_of_le_of_lt (hitBelow_le hdζ hfd) (WithTop.coe_lt_coe.2 hdt)

/-- **Hitting times of a positive function eventually pass every time before `ζ`**: if `f > 0` is continuous on
`[0, ζ)`, then for `t < ζ` the hitting times of the levels `1/(k+1)` are eventually at least `t`. -/
theorem eventually_le_hitBelow (hf : ContinuousOn f {s : ℝ≥0 | (s : ℝ≥0∞) < ζ})
    (hpos : ∀ s : ℝ≥0, (s : ℝ≥0∞) < ζ → 0 < f s) {t : ℝ≥0} (ht : (t : ℝ≥0∞) < ζ) :
    ∀ᶠ k : ℕ in atTop, (t : WithTop ℝ≥0) ≤ hitBelow f ζ (1 / ((k : ℝ) + 1)) := by
  have hmono : Monotone fun k : ℕ => hitBelow f ζ (1 / ((k : ℝ) + 1)) := fun k k' hkk' =>
    hitBelow_anti (one_div_le_one_div_of_le (by positivity) (by
      have : (k : ℝ) ≤ k' := by exact_mod_cast hkk'
      linarith))
  by_contra hcon
  rw [not_eventually] at hcon
  have hall : ∀ k : ℕ, hitBelow f ζ (1 / ((k : ℝ) + 1)) < t := by
    intro k
    obtain ⟨k', hk', hlt⟩ := (frequently_atTop.1 hcon) k
    exact lt_of_le_of_lt (hmono hk') (not_le.1 hlt)
  have hfin : ∀ k : ℕ, ∃ u : ℝ≥0, hitBelow f ζ (1 / ((k : ℝ) + 1)) = u ∧ u < t := by
    intro k
    obtain ⟨u, hu⟩ := WithTop.ne_top_iff_exists.1 (ne_top_of_lt (hall k))
    exact ⟨u, hu.symm, WithTop.coe_lt_coe.1 (hu ▸ hall k)⟩
  choose u hu hut using hfin
  have humono : Monotone u := fun k k' hkk' => by
    have := hmono hkk'
    simp only [hu] at this
    exact WithTop.coe_le_coe.1 this
  have hbdd : BddAbove (range u) := ⟨t, by rintro _ ⟨k, rfl⟩; exact (hut k).le⟩
  set L := ⨆ k, u k
  have hLt : L ≤ t := ciSup_le fun k => (hut k).le
  have hLζ : (L : ℝ≥0∞) < ζ := lt_of_le_of_lt (by exact_mod_cast hLt) ht
  have hconv : Tendsto u atTop (𝓝 L) := tendsto_atTop_ciSup humono hbdd
  have hcont : ContinuousAt f L := hf.continuousAt ((isOpen_setOf_coe_lt ζ).mem_nhds hLζ)
  have hfle : f L ≤ 0 :=
    le_of_tendsto_of_tendsto' (hcont.tendsto.comp hconv) tendsto_one_div_add_atTop_nhds_zero_nat
      fun k => le_of_hitBelow_eq hf (hu k)
  exact absurd (hpos L hLζ) (not_lt.2 hfle)

end HitBelow

/-! ### The candidate functionals -/

section Side

variable {n : ℕ}

/-- The gap from the `j`-th to the next force point on one side (`1` after the last point). -/
def sideGap (v : Fin n → ℝ) (j : Fin n) : ℝ :=
  if h : j.1 + 1 < n then v j - v ⟨j.1 + 1, h⟩ else 1

/-- The candidate functional `|w − v_j| + (1/(m+1) − gap_j)⁺`. On ordered states its zero set is
`{v_j = w, gap_j ≥ 1/(m+1)}`, where the colliding cluster is exactly `{0, …, j}`. -/
def sideVal (m : ℕ) (j : Fin n) (w : ℝ) (v : Fin n → ℝ) : ℝ :=
  |w - v j| + max 0 (1 / ((m : ℝ) + 1) - sideGap v j)

theorem continuous_sideGap (j : Fin n) : Continuous fun v : Fin n → ℝ => sideGap v j := by
  by_cases h : j.1 + 1 < n
  · simp only [sideGap, h, ↓reduceDIte]
    exact (continuous_apply j).sub (continuous_apply _)
  · simp only [sideGap, h, ↓reduceDIte]
    exact continuous_const

theorem continuous_sideVal (m : ℕ) (j : Fin n) :
    Continuous fun p : ℝ × (Fin n → ℝ) => sideVal m j p.1 p.2 :=
  ((continuous_fst.sub ((continuous_apply j).comp continuous_snd)).abs).add
    (continuous_const.max (continuous_const.sub ((continuous_sideGap j).comp continuous_snd)))

theorem sideVal_nonneg (m : ℕ) (j : Fin n) (w : ℝ) (v : Fin n → ℝ) : 0 ≤ sideVal m j w v :=
  add_nonneg (abs_nonneg _) (le_max_left _ _)

theorem sub_sideGap_le_sideVal (m : ℕ) (j : Fin n) (w : ℝ) (v : Fin n → ℝ) :
    1 / ((m : ℝ) + 1) - sideGap v j ≤ sideVal m j w v :=
  (le_max_right _ _).trans (le_add_of_nonneg_left (abs_nonneg _))

/-- **The candidate functional vanishes only on the threshold set**: on an ordered state whose colliding cluster
does not trigger the threshold, the functional of a cluster `{0, …, j}` of weight `≤ −2` is positive. -/
theorem sideVal_pos {ρ : Fin n → ℝ} {m : ℕ} {j : Fin n} {w : ℝ} {v : Fin n → ℝ} (hanti : Antitone v)
    (hle : ∀ i, v i ≤ w) (hsum : (∑ i ∈ Finset.Iic j, ρ i) ≤ -2)
    (hnot : ¬ (∑ i ∈ Finset.univ.filter (fun i => v i = w), ρ i) ≤ -2) : 0 < sideVal m j w v := by
  by_contra hcon
  have h0 : sideVal m j w v = 0 := le_antisymm (not_lt.1 hcon) (sideVal_nonneg m j w v)
  obtain ⟨habs, hmax⟩ := (add_eq_zero_iff_of_nonneg (abs_nonneg _) (le_max_left _ _)).1 h0
  have hvj : v j = w := (sub_eq_zero.1 (abs_eq_zero.1 habs)).symm
  have hgap : 1 / ((m : ℝ) + 1) ≤ sideGap v j := by
    have := le_max_right (0 : ℝ) (1 / ((m : ℝ) + 1) - sideGap v j)
    rw [hmax] at this
    linarith
  have hgap0 : 0 < sideGap v j := lt_of_lt_of_le (by positivity) hgap
  have hfilter : Finset.univ.filter (fun i => v i = w) = Finset.Iic j := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_Iic]
    constructor
    · intro hvi
      by_contra hij
      rw [not_le] at hij
      have hj : j.1 + 1 < n := lt_of_le_of_lt (Fin.lt_def.1 hij) i.2
      have hle' : v i ≤ v ⟨j.1 + 1, hj⟩ := hanti (Fin.le_def.2 (Fin.lt_def.1 hij))
      simp only [sideGap, hj, ↓reduceDIte] at hgap0
      linarith
    · intro hij
      exact le_antisymm (hle i) (hvj ▸ hanti hij)
  exact hnot (hfilter ▸ hsum)

open scoped Classical in
/-- **The candidates**: the hitting times of the levels `1/(k+1)` by the functional of the cluster `{0, …, j}` at
gap level `m` (`⊤` if the cluster weight exceeds `−2`). -/
def hitL (ρ : Fin n → ℝ) (w : ℝ≥0 → ℝ) (v : Fin n → ℝ≥0 → ℝ) (ζ : ℝ≥0∞) (j : Fin n) (m k : ℕ) :
    WithTop ℝ≥0 :=
  if (∑ i ∈ Finset.Iic j, ρ i) ≤ -2 then
    hitBelow (fun s => sideVal m j (w s) fun i => v i s) ζ (1 / ((k : ℝ) + 1)) else ⊤

theorem hitL_mono (ρ : Fin n → ℝ) (w : ℝ≥0 → ℝ) (v : Fin n → ℝ≥0 → ℝ) (ζ : ℝ≥0∞) (j : Fin n) (m : ℕ) :
    Monotone fun k => hitL ρ w v ζ j m k := by
  intro k k' hkk'
  by_cases hs : (∑ i ∈ Finset.Iic j, ρ i) ≤ -2
  · simp only [hitL, hs, ↓reduceIte]
    refine hitBelow_anti (one_div_le_one_div_of_le (by positivity) ?_)
    have : (k : ℝ) ≤ k' := by exact_mod_cast hkk'
    linarith
  · simp only [hitL, hs, ↓reduceIte, le_refl]

end Side

/-! ### Along one path of the evolution -/

section Path

open Sec2

variable {nL nR : ℕ} {xL : Fin nL → ℝ} {xR : Fin nR → ℝ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ}
  {w : ℝ≥0 → ℝ} {vL : Fin nL → ℝ≥0 → ℝ} {vR : Fin nR → ℝ≥0 → ℝ} {ζ : ℝ≥0∞}

/-- **Merged force points stay merged** (the gaps between neighbouring left force points are nonincreasing before
`ζ`): by the integrated equations, `(v^j − v^{j+1})_{s'} − (v^j − v^{j+1})_s = ∫ₛ^{s'} (2/(v^j − w) − 2/(v^{j+1} − w))`,
and off the null collision set of `v^j` the integrand is `≤ 0` because `0 < w − v^j ≤ w − v^{j+1}`. -/
theorem sideGap_vL_anti (h : IsForcePath xL xR ρL ρR w vL vR ζ) (j : Fin nL) {s s' : ℝ≥0}
    (hss' : s ≤ s') (hs' : (s' : ℝ≥0∞) < ζ) :
    sideGap (fun i => vL i s') j ≤ sideGap (fun i => vL i s) j := by
  by_cases hj : j.1 + 1 < nL
  swap
  · simp only [sideGap, hj, ↓reduceDIte, le_refl]
  simp only [sideGap, hj, ↓reduceDIte]
  set i' : Fin nL := ⟨j.1 + 1, hj⟩
  have hji : j ≤ i' := Fin.le_def.2 (Nat.le_succ _)
  have hss : (s : ℝ) ≤ s' := by exact_mod_cast hss'
  have hint : ∀ i, IntervalIntegrable (fun r : ℝ => 2 / (vL i r.toNNReal - w r.toNNReal)) volume s s' :=
    fun i => (h.intervalIntegrable_forceL hs' i).mono_set (by
      rw [uIcc_of_le hss, uIcc_of_le (NNReal.coe_nonneg s')]
      exact Icc_subset_Icc (NNReal.coe_nonneg s) le_rfl)
  have key : (vL j s' - vL i' s') - (vL j s - vL i' s) = ∫ r in (s : ℝ)..s',
      (2 / (vL j r.toNNReal - w r.toNNReal) - 2 / (vL i' r.toNNReal - w r.toNNReal)) := by
    rw [intervalIntegral.integral_sub (hint j) (hint i'), ← h.vL_sub hss' hs' j, ← h.vL_sub hss' hs' i']
    ring
  have hae : (fun r : ℝ => 2 / (vL j r.toNNReal - w r.toNNReal) -
      2 / (vL i' r.toNNReal - w r.toNNReal)) ≤ᵐ[volume.restrict (Icc (s : ℝ) s')] fun _ => 0 := by
    refine (ae_restrict_iff' measurableSet_Icc).2 ?_
    filter_upwards [measure_eq_zero_iff_ae_notMem.1 (h.volume_collisionL j)] with r hr hrI
    have hr0 : (0 : ℝ) ≤ r := (NNReal.coe_nonneg s).trans hrI.1
    have hlt : (r.toNNReal : ℝ≥0∞) < ζ :=
      lt_of_le_of_lt (by exact_mod_cast Real.toNNReal_le_iff_le_coe.2 hrI.2) hs'
    have hne : w r.toNNReal ≠ vL j r.toNNReal := fun he => hr ⟨hr0, hlt, he⟩
    have hp : 0 < w r.toNNReal - vL j r.toNNReal :=
      sub_pos.2 (lt_of_le_of_ne (h.vL_le_w hlt j) (Ne.symm hne))
    have hpq : w r.toNNReal - vL j r.toNNReal ≤ w r.toNNReal - vL i' r.toNNReal :=
      sub_le_sub_left (h.antitone_vL hlt hji) _
    have h1 := div_le_div_of_nonneg_left (by norm_num : (0 : ℝ) ≤ 2) hp hpq
    rw [← neg_sub (w r.toNNReal) (vL j r.toNNReal), ← neg_sub (w r.toNNReal) (vL i' r.toNNReal),
      div_neg, div_neg]
    linarith
  have hle := intervalIntegral.integral_mono_ae_restrict hss ((hint j).sub (hint i'))
    intervalIntegrable_const hae
  simp only [intervalIntegral.integral_const, smul_eq_mul, mul_zero] at hle
  linarith

theorem continuousOn_sideVal_path (h : IsForcePath xL xR ρL ρR w vL vR ζ) (m : ℕ) (j : Fin nL) :
    ContinuousOn (fun s => sideVal m j (w s) fun i => vL i s) {s : ℝ≥0 | (s : ℝ≥0∞) < ζ} :=
  (continuous_sideVal m j).comp_continuousOn
    (h.continuousOn_w.prodMk (continuousOn_pi.2 h.continuousOn_vL))

theorem pos_sideVal (h : IsForcePath xL xR ρL ρR w vL vR ζ) {m : ℕ} {j : Fin nL}
    (hsum : (∑ i ∈ Finset.Iic j, ρL i) ≤ -2) {s : ℝ≥0} (hs : (s : ℝ≥0∞) < ζ) :
    0 < sideVal m j (w s) fun i => vL i s :=
  sideVal_pos (h.antitone_vL hs) (h.vL_le_w hs) hsum fun hth => h.not_threshold hs (Or.inl hth)

/-- Every time before `ζ` is eventually below the candidates of a cluster of weight `≤ −2`. -/
theorem eventually_le_hitL (h : IsForcePath xL xR ρL ρR w vL vR ζ) {m : ℕ} {j : Fin nL}
    (hsum : (∑ i ∈ Finset.Iic j, ρL i) ≤ -2) {t : ℝ≥0} (ht : (t : ℝ≥0∞) < ζ) :
    ∀ᶠ k : ℕ in atTop, (t : WithTop ℝ≥0) ≤ hitL ρL w vL ζ j m k := by
  simp only [hitL, hsum, ↓reduceIte]
  exact eventually_le_hitBelow (continuousOn_sideVal_path h m j) (fun s hs => pos_sideVal h hsum hs) ht

/-- A bounded candidate belongs to a cluster of weight `≤ −2` and stays strictly below `ζ`. -/
theorem hitL_lt_of_bdd {n : ℕ} {ρ : Fin n → ℝ} {w : ℝ≥0 → ℝ} {v : Fin n → ℝ≥0 → ℝ} {j : Fin n} {m : ℕ}
    (hb : ∃ M : ℕ, ∀ k, hitL ρ w v ζ j m k ≤ ((M : ℝ≥0) : WithTop ℝ≥0)) :
    (∑ i ∈ Finset.Iic j, ρ i) ≤ -2 ∧ ∀ k, ∃ t : ℝ≥0, hitL ρ w v ζ j m k = t ∧ (t : ℝ≥0∞) < ζ := by
  obtain ⟨M, hM⟩ := hb
  have hsum : (∑ i ∈ Finset.Iic j, ρ i) ≤ -2 := by
    by_contra hs
    have := hM 0
    simp only [hitL, hs, ↓reduceIte, top_le_iff] at this
    exact WithTop.coe_ne_top this
  refine ⟨hsum, fun k => ?_⟩
  obtain ⟨t, ht⟩ := WithTop.ne_top_iff_exists.1 (ne_top_of_le_ne_top WithTop.coe_ne_top (hM k))
  refine ⟨t, ht.symm, ?_⟩
  have ht' := ht.symm
  simp only [hitL, hsum, ↓reduceIte] at ht'
  exact lt_of_hitBelow_eq ht'

/-- **Along a bounded candidate the gap stays at least `1/(m+1)`** for the whole lifetime. -/
theorem le_sideGap_of_bdd (h : IsForcePath xL xR ρL ρR w vL vR ζ) {j : Fin nL} {m : ℕ}
    (hb : ∃ M : ℕ, ∀ k, hitL ρL w vL ζ j m k ≤ ((M : ℝ≥0) : WithTop ℝ≥0)) {s : ℝ≥0}
    (hs : (s : ℝ≥0∞) < ζ) : 1 / ((m : ℝ) + 1) ≤ sideGap (fun i => vL i s) j := by
  obtain ⟨hsum, hlt⟩ := hitL_lt_of_bdd hb
  choose t ht htζ using hlt
  have hev : ∀ᶠ k : ℕ in atTop, 1 / ((m : ℝ) + 1) - 1 / ((k : ℝ) + 1) ≤ sideGap (fun i => vL i s) j := by
    filter_upwards [eventually_le_hitL h (m := m) hsum hs] with k hk
    rw [ht k] at hk
    have hsk : s ≤ t k := WithTop.coe_le_coe.1 hk
    have hval : sideVal m j (w (t k)) (fun i => vL i (t k)) ≤ 1 / ((k : ℝ) + 1) := by
      have := ht k
      simp only [hitL, hsum, ↓reduceIte] at this
      exact le_of_hitBelow_eq (continuousOn_sideVal_path h m j) this
    have h1 := sub_sideGap_le_sideVal m j (w (t k)) (fun i => vL i (t k))
    have h2 := sideGap_vL_anti h j hsk (htζ k)
    linarith
  have hlim : Tendsto (fun k : ℕ => 1 / ((m : ℝ) + 1) - 1 / ((k : ℝ) + 1)) atTop
      (𝓝 (1 / ((m : ℝ) + 1) - 0)) :=
    tendsto_const_nhds.sub tendsto_one_div_add_atTop_nhds_zero_nat
  rw [sub_zero] at hlim
  exact le_of_tendsto hlim hev

/-- **A bounded candidate does not depend on the gap level**: it is the hitting sequence of `|w − v^j|`. -/
theorem hitL_eq_of_bdd (h : IsForcePath xL xR ρL ρR w vL vR ζ) {j : Fin nL} {m : ℕ}
    (hb : ∃ M : ℕ, ∀ k, hitL ρL w vL ζ j m k ≤ ((M : ℝ≥0) : WithTop ℝ≥0)) (k : ℕ) :
    hitL ρL w vL ζ j m k = hitBelow (fun s => |w s - vL j s|) ζ (1 / ((k : ℝ) + 1)) := by
  have hsum := (hitL_lt_of_bdd hb).1
  simp only [hitL, hsum, ↓reduceIte]
  refine hitBelow_congr fun s hs => ?_
  have hg := le_sideGap_of_bdd h hb hs
  simp only [sideVal]
  rw [max_eq_left (by linarith), add_zero]

/-- **At a finite lifetime some candidate is bounded** (Aux. lemma 3): if the state converges at `ζ = T > 0` to a
state whose colliding left cluster has weight `≤ −2`, then the candidate of that cluster `{0, …, j}` at a gap level
below the terminal gap `v^j − v^{j+1} > 0` is bounded by `T`. -/
theorem exists_bdd_hitL (h : IsForcePath xL xR ρL ρR w vL vR ζ) {T : ℝ≥0} (hT : 0 < T)
    (hTζ : (T : ℝ≥0∞) = ζ) {w₀ : ℝ} {vL₀ : Fin nL → ℝ}
    (hlim : Tendsto (fun s => (w s, fun i => vL i s)) (𝓝[<] T) (𝓝 (w₀, vL₀)))
    (hth : (∑ i ∈ Finset.univ.filter (fun i => vL₀ i = w₀), ρL i) ≤ -2) :
    ∃ (j : Fin nL) (m : ℕ), ∀ k, hitL ρL w vL ζ j m k ≤ (T : WithTop ℝ≥0) := by
  have : (𝓝[<] T).NeBot := nhdsLT_neBot_of_exists_lt ⟨0, hT⟩
  have hev_lt : ∀ᶠ s : ℝ≥0 in 𝓝[<] T, (s : ℝ≥0∞) < ζ := by
    filter_upwards [self_mem_nhdsWithin] with s hs
    rw [← hTζ]
    exact_mod_cast hs
  have hw : Tendsto w (𝓝[<] T) (𝓝 w₀) := (continuous_fst.tendsto _).comp hlim
  have hv : ∀ i, Tendsto (fun s => vL i s) (𝓝[<] T) (𝓝 (vL₀ i)) := fun i =>
    ((continuous_apply i).tendsto _).comp ((continuous_snd.tendsto _).comp hlim)
  have hanti₀ : Antitone vL₀ := fun i i' hii' =>
    le_of_tendsto_of_tendsto (hv i') (hv i)
      (hev_lt.mono fun _ hs => h.antitone_vL hs hii')
  have hle₀ : ∀ i, vL₀ i ≤ w₀ := fun i =>
    le_of_tendsto_of_tendsto (hv i) hw
      (hev_lt.mono fun _ hs => h.vL_le_w hs i)
  set C := Finset.univ.filter (fun i => vL₀ i = w₀) with hC
  have hCne : C.Nonempty := by
    by_contra hne
    rw [Finset.not_nonempty_iff_eq_empty] at hne
    rw [hne, Finset.sum_empty] at hth
    norm_num at hth
  set j := C.max' hCne with hj_def
  have hvj : vL₀ j = w₀ := (Finset.mem_filter.1 (C.max'_mem hCne)).2
  have hCeq : C = Finset.Iic j := by
    ext i
    simp only [hC, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_Iic]
    constructor
    · intro hi
      exact C.le_max' i (Finset.mem_filter.2 ⟨Finset.mem_univ _, hi⟩)
    · intro hij
      exact le_antisymm (hle₀ i) (hvj ▸ hanti₀ hij)
  have hsum : (∑ i ∈ Finset.Iic j, ρL i) ≤ -2 := hCeq ▸ hth
  have hgap : 0 < sideGap vL₀ j := by
    by_cases hj : j.1 + 1 < nL
    · simp only [sideGap, hj, ↓reduceDIte]
      have hnot : (⟨j.1 + 1, hj⟩ : Fin nL) ∉ C := fun hmem => by
        have := Fin.le_def.1 (C.le_max' _ hmem)
        simp only [← hj_def] at this
        omega
      have hne : vL₀ ⟨j.1 + 1, hj⟩ ≠ w₀ := fun he =>
        hnot (Finset.mem_filter.2 ⟨Finset.mem_univ _, he⟩)
      have hle : vL₀ ⟨j.1 + 1, hj⟩ ≤ vL₀ j := hanti₀ (Fin.le_def.2 (Nat.le_succ _))
      rw [hvj] at hle ⊢
      exact sub_pos.2 (lt_of_le_of_ne hle hne)
    · simp only [sideGap, hj, ↓reduceDIte]
      exact one_pos
  obtain ⟨m, hm⟩ := exists_nat_one_div_lt hgap
  have hval : sideVal m j w₀ vL₀ = 0 := by
    simp only [sideVal, hvj, sub_self, abs_zero, zero_add]
    exact max_eq_left (by linarith)
  have htend : Tendsto (fun s => sideVal m j (w s) fun i => vL i s) (𝓝[<] T) (𝓝 0) := by
    rw [← hval]
    exact ((continuous_sideVal m j).tendsto _).comp hlim
  refine ⟨j, m, fun k => ?_⟩
  have hk : (0 : ℝ) < 1 / ((k : ℝ) + 1) := by positivity
  obtain ⟨s, hsT, hsζ, hfs⟩ :=
    (eventually_mem_nhdsWithin.and (hev_lt.and (htend.eventually (gt_mem_nhds hk)))).exists
  simp only [hitL, hsum, ↓reduceIte]
  exact (hitBelow_le hsζ hfs).trans (WithTop.coe_le_coe.2 (le_of_lt hsT))

end Path

end Coupling

end InteractingSLE
