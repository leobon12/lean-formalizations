/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec4.Repulsion
import InteractingSLE.Spec.Sec4.RepulsionDrift
import InteractingSLE.Spec.Sec4.Noncollision
import InteractingSLE.Spec.Sec2.TerminalEvolution
import InteractingSLE.Stochastic.LocalTime.Bridge

/-!
# Aux. lemma 6: noncollision from ordered partial sums

Packet PROVE-SEC4-A2. Specification §2.2, Aux. lemma 6 and its proof (`source/spec/p001-048.md`).
For `κ > 0` and `c = κ/2 − 2`, an integrated `SLE_κ(ρ)` evolution of an ordered force word whose
amalgamated side partial sums are all at least `c` has infinite lifetime, and every force point is
strictly separated from the driver at every positive time (`aux6Statement`, which proves the
proposition `Sec4.Aux6Statement` of PROVE-SEC4-A).

* `IsIntegratedSLEEvolution.ae_lifetime_eq_top`: a colliding group is a whole initial segment of
  groups, of weight `≥ c > −2`, so Aux. lemma 3 for noncritical side totals
  (`IsIntegratedSLEEvolution.ae_tendsto_threshold_of_ne`) excludes a finite lifetime;
* `IsIntegratedSLEEvolution.ae_w_lt_vR`: the source's argument on the right side: Aux. lemma 5
  (`Repulsion.ae_pos_of_isRepulsionPath`) for the gap `Y = V^{1,R} − W`, with (RP4)–(RP5), on the
  events `{D_q ≥ 2a, 0 < Y_q < a}` for rational `q`, `a` and integer horizons, then the final
  pathwise argument (null collision set, rational times in the final interval below `a`);
* `IsIntegratedSLEEvolution.reflect`: the reflection `x ↦ −x` of an evolution (with `−B`), which
  gives the left side.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal

universe u

namespace InteractingSLE

open Sec4

/-! ### Killed processes -/

/-- A process defined before `ζ`, killed (set to `0`) from `ζ` on. -/
def killedProc {Ω : Type*} (ζ : Ω → ℝ≥0∞) (X : ℝ≥0 → Ω → ℝ) (t : ℝ≥0) (ω : Ω) : ℝ :=
  if (t : ℝ≥0∞) < ζ ω then X t ω else 0

lemma killedProc_of_eq_top {Ω : Type*} {ζ : Ω → ℝ≥0∞} {X : ℝ≥0 → Ω → ℝ} {ω : Ω}
    (h : ζ ω = ⊤) (t : ℝ≥0) : killedProc ζ X t ω = X t ω := by
  simp [killedProc, h]

lemma measurable_killedProc {Ω : Type*} {mΩ : MeasurableSpace Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    {ζ : Ω → ℝ≥0∞} {X : ℝ≥0 → Ω → ℝ} (hX : AdaptedBefore 𝓕 ζ X) (t : ℝ≥0) :
    Measurable[𝓕 t] (killedProc ζ X t) := by
  intro A hA
  have hζ : MeasurableSet[𝓕 t] {ω | (t : ℝ≥0∞) < ζ ω} := by
    simpa using hX t univ MeasurableSet.univ
  have : killedProc ζ X t ⁻¹' A =
      {ω | (t : ℝ≥0∞) < ζ ω ∧ X t ω ∈ A} ∪ ({ω | (t : ℝ≥0∞) < ζ ω}ᶜ ∩ {_ω | (0 : ℝ) ∈ A}) := by
    ext ω
    simp only [killedProc, mem_preimage, mem_union, mem_ofPred_eq, mem_inter_iff, mem_compl_iff]
    split_ifs with h <;> simp [h]
  rw [this]
  exact (hX t A hA).union (hζ.compl.inter (MeasurableSet.const _))

/-! ### Reflection of an evolution -/

theorem IsFilteredBrownianReal.neg {Ω : Type*} {mΩ : MeasurableSpace Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    {B : ℝ≥0 → Ω → ℝ} {P : Measure Ω} (h : IsFilteredBrownianReal 𝓕 B P) :
    IsFilteredBrownianReal 𝓕 (-B) P := by
  refine ⟨h.1.neg, fun t => (h.2.1 t).neg, fun s t hst => ?_⟩
  refine indep_of_indep_of_le_left (h.2.2 s t hst) ?_
  have : (fun ω => (-B) t ω - (-B) s ω) = (fun x : ℝ => -x) ∘ fun ω => B t ω - B s ω := by
    funext ω; simp only [Pi.neg_apply, Function.comp_apply]; ring
  rw [this, ← MeasurableSpace.comap_comp]
  exact MeasurableSpace.comap_mono measurable_neg.comap_le

theorem AdaptedBefore.neg {Ω : Type*} {mΩ : MeasurableSpace Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    {ζ : Ω → ℝ≥0∞} {X : ℝ≥0 → Ω → ℝ} (h : AdaptedBefore 𝓕 ζ X) : AdaptedBefore 𝓕 ζ (-X) := by
  intro t A hA
  have := h t ((fun x : ℝ => -x) ⁻¹' A) (measurable_neg hA)
  simpa only [Pi.neg_apply, mem_preimage] using this

namespace IsIntegratedSLEEvolution

variable {k : ℝ} {nL nR : ℕ} {xL : Fin nL → ℝ} {xR : Fin nR → ℝ} {ρL : Fin nL → ℝ}
  {ρR : Fin nR → ℝ} {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}
  {𝓕 : Filtration ℝ≥0 mΩ} {W : ℝ≥0 → Ω → ℝ} {VL : Fin nL → ℝ≥0 → Ω → ℝ}
  {VR : Fin nR → ℝ≥0 → Ω → ℝ} {B : ℝ≥0 → Ω → ℝ} {ζ : Ω → ℝ≥0∞}

/-- **Reflection of an evolution**: `(−W, −V^R, −V^L, −B)` with the sides exchanged is an
integrated evolution of the reflected word. -/
theorem reflect (h : IsIntegratedSLEEvolution k xL xR ρL ρR P 𝓕 W VL VR B ζ) :
    IsIntegratedSLEEvolution k (-xR) (-xL) ρR ρL P 𝓕 (-W) (fun i => -VR i) (fun i => -VL i)
      (-B) ζ := by
  refine ⟨h.isFilteredBrownianReal.neg, h.adaptedBefore_W.neg,
    fun i => (h.adaptedBefore_VR i).neg, fun i => (h.adaptedBefore_VL i).neg, ?_⟩
  filter_upwards [h.ae_isIntegratedSLEPath] with ω hω
  exact hω.reflect

end IsIntegratedSLEEvolution

namespace Sec4

/-- The total weight of a side with group-end sums at least `c > −2` exceeds `−2`. -/
theorem neg_two_lt_sum_of_hasGroupEndSums {c : ℝ} (hc : -2 < c) {n : ℕ} {ρ x : Fin n → ℝ}
    (h : HasGroupEndSums c ρ x) : -2 < ∑ i, ρ i := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp only [Finset.univ_eq_empty, Finset.sum_empty]; norm_num
  · set j : Fin n := ⟨n - 1, by omega⟩
    have hj := h j (fun i hji => absurd (Fin.lt_def.1 hji) (by have := i.2; simp only [j]; omega))
    have : Finset.univ.filter (fun i => i ≤ j) = Finset.univ := by
      ext i; simp only [Finset.mem_filter, Finset.mem_univ, true_and, iff_true, Fin.le_def, j]
      have := i.2; omega
    rw [this] at hj
    linarith

end Sec4

namespace IsIntegratedSLEEvolution

variable {k : ℝ} {nL nR : ℕ} {xL : Fin nL → ℝ} {xR : Fin nR → ℝ} {ρL : Fin nL → ℝ}
  {ρR : Fin nR → ℝ} {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}
  {𝓕 : Filtration ℝ≥0 mΩ} {W : ℝ≥0 → Ω → ℝ} {VL : Fin nL → ℝ≥0 → Ω → ℝ}
  {VR : Fin nR → ℝ≥0 → Ω → ℝ} {B : ℝ≥0 → Ω → ℝ} {ζ : Ω → ℝ≥0∞}

/-- **The continuation threshold is infinite** (first assertion of Aux. lemma 6): if both sides
have group-end sums at least `c = κ/2 − 2`, then almost surely `ζ = ∞`. Any group colliding with
the driver at the seed or at a finite lifetime is a whole initial segment of groups, of weight
`≥ c > −2`; Aux. lemma 3 for noncritical side totals excludes a finite lifetime. -/
theorem ae_lifetime_eq_top (hk : 0 < k) (hword : IsOrderedForceWord xL xR)
    (hL : HasGroupEndSums (k / 2 - 2) ρL (-xL)) (hR : HasGroupEndSums (k / 2 - 2) ρR xR)
    (h : IsIntegratedSLEEvolution k xL xR ρL ρR P 𝓕 W VL VR B ζ) : ∀ᵐ ω ∂P, ζ ω = ⊤ := by
  have hc : (-2 : ℝ) < k / 2 - 2 := by linarith
  obtain ⟨hxL, hxL0, hxR, hxR0⟩ := hword
  have hsL := (neg_two_lt_sum_of_hasGroupEndSums hc hL).ne'
  have hsR := (neg_two_lt_sum_of_hasGroupEndSums hc hR).ne'
  filter_upwards [h.ae_tendsto_threshold_of_ne hsL hsR, h.ae_isIntegratedSLEPath] with ω hlim hp
  by_contra hne
  obtain ⟨T, hT⟩ : ∃ T : ℝ≥0, (T : ℝ≥0∞) = ζ ω := ⟨(ζ ω).toNNReal, ENNReal.coe_toNNReal hne⟩
  have hfp := hp.isForcePath
  rcases eq_zero_or_pos T with hT0 | hT0
  · have h0 : ζ ω = 0 := by rw [← hT, hT0, ENNReal.coe_zero]
    exact not_thresholdCondition_of_hasGroupEndSums hc hxL hxR hL hR hxL hxR hxL0 hxR0
      (fun _ _ h => h) (fun _ _ h => h) (hfp.threshold_of_eq_zero h0)
  · obtain ⟨w₀, vL₀, vR₀, hlim', hth⟩ := hlim T hT0 hT
    have : NeBot (𝓝[<] T) := nhdsLT_neBot_of_exists_lt ⟨0, hT0⟩
    have hev : ∀ᶠ t : ℝ≥0 in 𝓝[<] T, (t : ℝ≥0∞) < ζ ω := by
      filter_upwards [self_mem_nhdsWithin] with t ht
      rw [← hT]; exact_mod_cast ht
    have hw : Tendsto (fun t => W t ω) (𝓝[<] T) (𝓝 w₀) := hlim'.fst_nhds
    have hvL : ∀ i, Tendsto (fun t => VL i t ω) (𝓝[<] T) (𝓝 (vL₀ i)) := fun i =>
      tendsto_pi_nhds.1 hlim'.snd_nhds.fst_nhds i
    have hvR : ∀ i, Tendsto (fun t => VR i t ω) (𝓝[<] T) (𝓝 (vR₀ i)) := fun i =>
      tendsto_pi_nhds.1 hlim'.snd_nhds.snd_nhds i
    refine not_thresholdCondition_of_hasGroupEndSums hc hxL hxR hL hR ?_ ?_ ?_ ?_ ?_ ?_ hth
    · intro i j hij
      exact le_of_tendsto_of_tendsto (hvL j) (hvL i) (hev.mono fun t ht => hfp.antitone_vL ht hij)
    · intro i j hij
      exact le_of_tendsto_of_tendsto (hvR i) (hvR j) (hev.mono fun t ht => hfp.monotone_vR ht hij)
    · intro i
      exact le_of_tendsto_of_tendsto (hvL i) hw (hev.mono fun t ht => hfp.vL_le_w ht i)
    · intro i
      exact le_of_tendsto_of_tendsto hw (hvR i) (hev.mono fun t ht => hfp.w_le_vR ht i)
    · intro i j hij
      exact tendsto_nhds_unique (hvL i)
        ((hvL j).congr' (hev.mono fun t ht => (hp.vL_eq_of_xL_eq ht hij).symm))
    · intro i j hij
      exact tendsto_nhds_unique (hvR i)
        ((hvR j).congr' (hev.mono fun t ht => (hp.vR_eq_of_xR_eq ht hij).symm))

end IsIntegratedSLEEvolution

namespace Sec4

/-- Finitely many positive reals have a common positive strict lower bound. -/
theorem exists_pos_forall_lt {n : ℕ} (D : Fin n → ℝ) (hD : ∀ i, 0 < D i) :
    ∃ ε > 0, ∀ i, ε < D i := by
  set S := insert (1 : ℝ) (Finset.univ.image D)
  have hS : S.Nonempty := Finset.insert_nonempty _ _
  have h0 : 0 < S.min' hS := by
    refine (Finset.lt_min'_iff S hS).2 fun y hy => ?_
    rcases Finset.mem_insert.1 hy with rfl | hy
    · norm_num
    · obtain ⟨i, -, rfl⟩ := Finset.mem_image.1 hy; exact hD i
  refine ⟨S.min' hS / 2, by linarith, fun i => ?_⟩
  have h1 : S.min' hS ≤ D i :=
    Finset.min'_le S _ (Finset.mem_insert_of_mem (Finset.mem_image_of_mem D (Finset.mem_univ i)))
  linarith

end Sec4

namespace IsIntegratedSLEPath

variable {k : ℝ} {nL nR : ℕ} {xL : Fin nL → ℝ} {xR : Fin nR → ℝ} {ρL : Fin nL → ℝ}
  {ρR : Fin nR → ℝ} {w : ℝ≥0 → ℝ} {vL : Fin nL → ℝ≥0 → ℝ} {vR : Fin nR → ℝ≥0 → ℝ}
  {b : ℝ≥0 → ℝ} {ζ : ℝ≥0∞}

/-- At a positive time the two sides are separated: `V^{i,L}_t < V^{j,R}_t` (otherwise the driver
would sit on the mark `V^{j,R}` throughout `[0, t]`, a collision set of positive measure). -/
theorem vL_lt_vR (h : IsIntegratedSLEPath k xL xR ρL ρR w vL vR b ζ) {t : ℝ≥0}
    (ht : (t : ℝ≥0∞) < ζ) (ht0 : 0 < t) (i : Fin nL) (j : Fin nR) : vL i t < vR j t := by
  have hfp := h.isForcePath
  by_contra hle
  push Not at hle
  have hsub : Icc (0 : ℝ) t ⊆
      {s : ℝ | 0 ≤ s ∧ (s.toNNReal : ℝ≥0∞) < ζ ∧ w s.toNNReal = vR j s.toNNReal} := by
    intro r hr
    have hp := Sec2.toNNReal_le_of_mem_Icc hr
    have hlt := Sec2.toNNReal_lt_of_mem_Icc ht hr
    refine ⟨hr.1, hlt, ?_⟩
    have h1 := hfp.vL_le_of_le hp ht i
    have h2 := hfp.le_vR_of_le hp ht j
    have h3 := hfp.vL_le_w hlt i
    have h4 := hfp.w_le_vR hlt j
    linarith
  have := measure_mono_null hsub (hfp.volume_collisionR j)
  rw [Real.volume_Icc, ENNReal.ofReal_eq_zero, sub_zero] at this
  exact absurd this (not_le.2 (by exact_mod_cast ht0))

end IsIntegratedSLEPath

namespace IsIntegratedSLEEvolution

variable {k : ℝ} {nL nR : ℕ} {xL : Fin nL → ℝ} {xR : Fin nR → ℝ} {ρL : Fin nL → ℝ}
  {ρR : Fin nR → ℝ} {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}
  {𝓕 : Filtration ℝ≥0 mΩ} {W : ℝ≥0 → Ω → ℝ} {VL : Fin nL → ℝ≥0 → Ω → ℝ}
  {VR : Fin nR → ℝ≥0 → Ω → ℝ} {B : ℝ≥0 → Ω → ℝ} {ζ : Ω → ℝ≥0∞}

/-- **Aux. lemma 5 applied to the right gap** (proof of Aux. lemma 6): for `0 < a` and `s ≤ t`,
almost surely on `{s < ζ, D^i_s ≥ 2a ∀ i}` (`D^i = V^{1,R} − V^{i,L}`) with `0 < Y_s < a`, the gap
`Y = V^{1,R} − W` stays positive on `[s, t]` while it stays below `a`. -/
theorem ae_gap_pos (hk : 0 < k) (hword : IsOrderedForceWord xL xR)
    (hR : HasGroupEndSums (k / 2 - 2) ρR xR)
    (h : IsIntegratedSLEEvolution k xL xR ρL ρR P 𝓕 W VL VR B ζ) (hζ : ∀ᵐ ω ∂P, ζ ω = ⊤)
    (hnR : 0 < nR) {s t : ℝ≥0} {a : ℝ} (ha : 0 < a) (hst : s ≤ t) :
    ∀ᵐ ω ∂P, ((s : ℝ≥0∞) < ζ ω ∧ ∀ i, 2 * a ≤
        killedProc ζ (VR ⟨0, hnR⟩) s ω - killedProc ζ (VL i) s ω) →
      0 < killedProc ζ (VR ⟨0, hnR⟩) s ω - killedProc ζ W s ω →
      killedProc ζ (VR ⟨0, hnR⟩) s ω - killedProc ζ W s ω < a →
      ∀ u ∈ Icc s t, (∀ r ∈ Icc s u,
        killedProc ζ (VR ⟨0, hnR⟩) r ω - killedProc ζ W r ω < a) →
        0 < killedProc ζ (VR ⟨0, hnR⟩) u ω - killedProc ζ W u ω := by
  have : IsProbabilityMeasure P :=
    h.isFilteredBrownianReal.1.toIsPreBrownianReal.isGaussianProcess.isProbabilityMeasure
  set i₀ : Fin nR := ⟨0, hnR⟩
  have hB := LocalTime.isFilteredPreBrownian_of_isFilteredBrownianReal h.isFilteredBrownianReal
  set Y : ℝ≥0 → Ω → ℝ := fun t ω => killedProc ζ (VR i₀) t ω - killedProc ζ W t ω with hYdef
  set ψ : ℝ≥0 → Ω → ℝ := fun t ω => rightGapDom ρL ρR (fun i t => killedProc ζ (VL i) t ω)
    (fun i t => killedProc ζ (VR i) t ω) i₀ t with hψdef
  set β : ℝ≥0 → Ω → ℝ := fun t ω => rightGapDrift ρL ρR (fun t => W t ω) (fun i t => VL i t ω)
    (fun i t => VR i t ω) i₀ t
  have hYm : ∀ t, Measurable[𝓕 t] (Y t) := fun t =>
    (measurable_killedProc (h.adaptedBefore_VR i₀) t).sub (measurable_killedProc h.adaptedBefore_W t)
  have hψm : ∀ t, Measurable[𝓕 t] (ψ t) := fun t =>
    ((measurable_killedProc (h.adaptedBefore_VR i₀) t).add (Finset.measurable_sum _ fun i _ =>
      (measurable_killedProc (h.adaptedBefore_VR i) t).const_mul _)).sub
      (Finset.measurable_sum _ fun i _ => (measurable_killedProc (h.adaptedBefore_VL i) t).const_mul _)
  set A : Set Ω := {ω | (s : ℝ≥0∞) < ζ ω ∧ ∀ i, 2 * a ≤
    killedProc ζ (VR i₀) s ω - killedProc ζ (VL i) s ω} with hAdef
  have hAm : MeasurableSet[𝓕 s] A := by
    have : A = {ω | (s : ℝ≥0∞) < ζ ω} ∩ ⋂ i, {ω | 2 * a ≤
        killedProc ζ (VR i₀) s ω - killedProc ζ (VL i) s ω} := by
      ext ω; simp [hAdef]
    rw [this]
    exact (h.measurableSet_lt_lifetime s).inter (MeasurableSet.iInter fun i =>
      measurableSet_le measurable_const ((measurable_killedProc (h.adaptedBefore_VR i₀) s).sub
        (measurable_killedProc (h.adaptedBefore_VL i) s)))
  have hσ : -Real.sqrt k ≠ 0 := neg_ne_zero.2 (Real.sqrt_pos.2 hk).ne'
  have hC : 0 ≤ (∑ i, |ρL i|) / a := div_nonneg (Finset.sum_nonneg fun i _ => abs_nonneg _) ha.le
  refine Repulsion.ae_pos_of_isRepulsionPath (C := (∑ i, |ρL i|) / a) (β := β) hB hσ hC hst hYm hψm
    hAm ?_
  filter_upwards [hζ, h.ae_isIntegratedSLEPath, h.ae_continuous_B] with ω hζω hp hBc hAω
  have hk' : ∀ (X : ℝ≥0 → Ω → ℝ) t, killedProc ζ X t ω = X t ω := fun X t =>
    killedProc_of_eq_top hζω t
  have hYω : (Y · ω) = fun t => VR i₀ t ω - W t ω := by funext t; simp only [hYdef, hk']
  have hψω : (ψ · ω) = rightGapDom ρL ρR (fun i t => VL i t ω) (fun i t => VR i t ω) i₀ := by
    funext t; simp only [hψdef, hk']
  rw [hYω, hψω]
  have hlt : ∀ t : ℝ≥0, (t : ℝ≥0∞) < ζ ω := fun t => by rw [hζω]; exact ENNReal.coe_lt_top
  have hfp := hp.isForcePath
  have hall : ∀ S : Set ℝ≥0, S ⊆ {t | (t : ℝ≥0∞) < ζ ω} := fun S r _ => hlt r
  refine ⟨((hfp.continuousOn_vR i₀).sub hfp.continuousOn_w).mono (hall _), hBc.continuousOn, ?_,
    fun u hu hpos => ⟨hp.intervalIntegrable_rightGapDrift i₀ hu.1 (hlt u),
      hp.gap_eq i₀ hu.1 (hlt u), hp.integral_abs_rightGapDrift_le i₀ hu.1 (hlt u), ?_⟩⟩
  · unfold rightGapDom
    refine (((hfp.continuousOn_vR i₀).add (continuousOn_finsetSum _ fun i _ =>
      (hfp.continuousOn_vR i).const_smul (|ρR i| / 2))).sub (continuousOn_finsetSum _ fun i _ =>
      (hfp.continuousOn_vL i).const_smul (|ρL i| / 2))).mono (hall _)
  · refine Eventually.of_forall fun r hr => ?_
    have hp' := Repulsion.toNNReal_mem_Icc_of_mem hr
    set p := r.toNNReal
    have hY := (hpos p hp').1
    have hL : ∀ i, a ≤ W p ω - VL i p ω := fun i => by
      have h1 := hAω.2 i
      rw [hk', hk'] at h1
      have h2 := hfp.le_vR_of_le hp'.1 (hlt p) i₀
      have h3 := hfp.vL_le_of_le hp'.1 (hlt p) i
      have h4 := (hpos p hp').2
      linarith
    have := hp.rightGapDrift_ge hnR hword.2.2.1 hR (hlt p) ha hY hL
    rw [neg_sq, Real.sq_sqrt hk.le]
    exact this


/-- **Right-side noncollision** (Aux. lemma 6, right side): if the right group-end sums are at
least `c = κ/2 − 2` and `ζ = ∞` almost surely, then almost surely `W_t < V^{1,R}_t` for every
`t > 0`. -/
theorem ae_w_lt_vR (hk : 0 < k) (hword : IsOrderedForceWord xL xR)
    (hR : HasGroupEndSums (k / 2 - 2) ρR xR)
    (h : IsIntegratedSLEEvolution k xL xR ρL ρR P 𝓕 W VL VR B ζ) (hζ : ∀ᵐ ω ∂P, ζ ω = ⊤)
    (hnR : 0 < nR) : ∀ᵐ ω ∂P, ∀ t : ℝ≥0, 0 < t → W t ω < VR ⟨0, hnR⟩ t ω := by
  set i₀ : Fin nR := ⟨0, hnR⟩
  have hall : ∀ᵐ ω ∂P, ∀ q : ℚ, ∀ a : ℚ, ∀ n : ℕ, 0 < (a : ℝ) → (q : ℝ).toNNReal ≤ (n : ℝ≥0) →
      (((q : ℝ).toNNReal : ℝ≥0∞) < ζ ω ∧ ∀ i, 2 * (a : ℝ) ≤
        killedProc ζ (VR i₀) (q : ℝ).toNNReal ω - killedProc ζ (VL i) (q : ℝ).toNNReal ω) →
      0 < killedProc ζ (VR i₀) (q : ℝ).toNNReal ω - killedProc ζ W (q : ℝ).toNNReal ω →
      killedProc ζ (VR i₀) (q : ℝ).toNNReal ω - killedProc ζ W (q : ℝ).toNNReal ω < a →
      ∀ u ∈ Icc (q : ℝ).toNNReal (n : ℝ≥0), (∀ r ∈ Icc (q : ℝ).toNNReal u,
        killedProc ζ (VR i₀) r ω - killedProc ζ W r ω < a) →
        0 < killedProc ζ (VR i₀) u ω - killedProc ζ W u ω := by
    rw [ae_all_iff]; intro q; rw [ae_all_iff]; intro a; rw [ae_all_iff]; intro n
    by_cases hc : 0 < (a : ℝ) ∧ (q : ℝ).toNNReal ≤ (n : ℝ≥0)
    · filter_upwards [h.ae_gap_pos hk hword hR hζ hnR hc.1 hc.2] with ω hω _ _ using hω
    · exact Eventually.of_forall fun ω h1 h2 => absurd ⟨h1, h2⟩ hc
  filter_upwards [hall, hζ, h.ae_isIntegratedSLEPath] with ω hall hζω hp t ht
  have hk' : ∀ (X : ℝ≥0 → Ω → ℝ) t, killedProc ζ X t ω = X t ω := fun X t =>
    killedProc_of_eq_top hζω t
  have hlt : ∀ t : ℝ≥0, (t : ℝ≥0∞) < ζ ω := fun t => by rw [hζω]; exact ENNReal.coe_lt_top
  have hfp := hp.isForcePath
  set y : ℝ≥0 → ℝ := fun t => VR i₀ t ω - W t ω with hydef
  have hYy : ∀ t, killedProc ζ (VR i₀) t ω - killedProc ζ W t ω = y t := fun t => by
    rw [hk', hk']
  have hy0 : ∀ t, 0 ≤ y t := fun t => sub_nonneg.2 (hfp.w_le_vR (hlt t) i₀)
  have hyc : Continuous y := continuousOn_univ.1
    (((hfp.continuousOn_vR i₀).sub hfp.continuousOn_w).mono fun r _ => hlt r)
  by_contra hcon
  push Not at hcon
  have hyt : y t ≤ 0 := by simp only [hydef]; linarith
  have ht2 : 0 < t / 2 := half_pos ht
  -- the level `a`
  obtain ⟨ε, hε, hεD⟩ := exists_pos_forall_lt (fun i => VR i₀ (t / 2) ω - VL i (t / 2) ω)
    fun i => sub_pos.2 (hp.vL_lt_vR (hlt _) ht2 i i₀)
  obtain ⟨a, ha0, haε⟩ := exists_rat_btwn (half_pos hε)
  have ha0' : (0 : ℝ) < a := by exact_mod_cast ha0
  -- the final interval below `a`
  obtain ⟨δ, hδ, hball⟩ := Metric.eventually_nhds_iff.1
    (hyc.continuousAt.eventually (gt_mem_nhds (hyt.trans_lt ha0')))
  set t₀ : ℝ := max ((t : ℝ) / 2) ((t : ℝ) - δ / 2) with ht₀def
  have htpos : (0 : ℝ) < t := by exact_mod_cast ht
  have ht₀ : t₀ < t := max_lt (by linarith) (by linarith)
  have ht₀0 : 0 ≤ t₀ := (by positivity : (0 : ℝ) ≤ (t : ℝ) / 2).trans (le_max_left _ _)
  -- a time in the final interval with a positive gap (the collision set is null)
  obtain ⟨r, hr, hyr⟩ : ∃ r ∈ Ioo t₀ (t : ℝ), y r.toNNReal ≠ 0 := by
    by_contra hall'
    push Not at hall'
    have hsub : Ioo t₀ (t : ℝ) ⊆ {s : ℝ | 0 ≤ s ∧ (s.toNNReal : ℝ≥0∞) < ζ ω ∧
        W s.toNNReal ω = VR i₀ s.toNNReal ω} := fun r hr => by
      refine ⟨ht₀0.trans hr.1.le, hlt _, ?_⟩
      have := hall' r hr
      simp only [hydef] at this
      linarith
    have := measure_mono_null hsub (hfp.volume_collisionR i₀)
    rw [Real.volume_Ioo, ENNReal.ofReal_eq_zero] at this
    linarith
  have hyr' : 0 < y r.toNNReal := lt_of_le_of_ne (hy0 _) (Ne.symm hyr)
  obtain ⟨δ', hδ', hball'⟩ := Metric.eventually_nhds_iff.1
    ((hyc.comp continuous_real_toNNReal).continuousAt.eventually (lt_mem_nhds hyr'))
  obtain ⟨q, hq1, hq2⟩ := exists_rat_btwn (show max t₀ (r - δ') < min (t : ℝ) (r + δ') from
    max_lt (lt_min ht₀ (by linarith [hr.1])) (lt_min (by linarith [hr.2]) (by linarith)))
  have hq0 : (0 : ℝ) ≤ q := ht₀0.trans ((le_max_left _ _).trans hq1.le)
  set s : ℝ≥0 := (q : ℝ).toNNReal with hsdef
  have hsq : (s : ℝ) = q := Real.coe_toNNReal _ hq0
  have hqt : (q : ℝ) < t := hq2.trans_le (min_le_left _ _)
  have hqt₀ : t₀ < q := (le_max_left _ _).trans_lt hq1
  have hst : s ≤ t := by rw [← NNReal.coe_le_coe, hsq]; exact hqt.le
  have hys : 0 < y s := by
    have := hball' (y := (q : ℝ)) (by
      rw [Real.dist_eq, abs_sub_lt_iff]
      constructor
      · linarith [hq2.trans_le (min_le_right _ _)]
      · linarith [(le_max_right _ _).trans_lt hq1])
    exact this
  have hyless : ∀ p ∈ Icc s t, y p < a := fun p hp => hball (by
    rw [NNReal.dist_eq, abs_sub_lt_iff]
    have h1 : (s : ℝ) ≤ p := by exact_mod_cast hp.1
    have h2 : (p : ℝ) ≤ t := by exact_mod_cast hp.2
    have h3 : (t : ℝ) - δ / 2 ≤ t₀ := le_max_right _ _
    constructor <;> linarith)
  have hts : t / 2 ≤ s := by
    rw [← NNReal.coe_le_coe, hsq, NNReal.coe_div, NNReal.coe_two]
    linarith [le_max_left ((t : ℝ) / 2) ((t : ℝ) - δ / 2)]
  have hA : (s : ℝ≥0∞) < ζ ω ∧ ∀ i, 2 * (a : ℝ) ≤
      killedProc ζ (VR i₀) s ω - killedProc ζ (VL i) s ω := by
    refine ⟨hlt s, fun i => ?_⟩
    rw [hk', hk']
    have h1 := hεD i
    have h2 := hfp.le_vR_of_le hts (hlt s) i₀
    have h3 := hfp.vL_le_of_le hts (hlt s) i
    have h4 : (2 : ℝ) * a < ε := by linarith
    linarith
  set n : ℕ := ⌈(t : ℝ)⌉₊
  have htn : t ≤ (n : ℝ≥0) := by
    rw [← NNReal.coe_le_coe, NNReal.coe_natCast]; exact Nat.le_ceil _
  have := hall q a n ha0' (hst.trans htn) hA (by rw [hYy]; exact hys)
    (by rw [hYy]; exact hyless s ⟨le_rfl, hst⟩) t ⟨hst, htn⟩ (fun p hp => by rw [hYy]; exact hyless p hp)
  rw [hYy] at this
  linarith

end IsIntegratedSLEEvolution

namespace Sec4

/-- **Aux. lemma 6 (noncollision from ordered partial sums)**, Specification §2.2: for `κ > 0`
and `c = κ/2 − 2`, an integrated `SLE_κ(ρ)` evolution of an ordered force word whose amalgamated
side partial sums are all at least `c` has infinite continuation threshold, and every force point
is strictly separated from the driver at every positive time. This proves the proposition
`Sec4.Aux6Statement` (PROVE-SEC4-A) for every universe. -/
theorem aux6Statement {k : ℝ} (hk : 0 < k) : Aux6Statement.{u} k := by
  intro nL nR xL xR ρL ρR Ω mΩ P 𝓕 W VL VR B ζ hword hadm h
  obtain ⟨hxL, hxL0, hxR, hxR0⟩ := id hword
  have hL := hasGroupEndSums_left hadm hxL hxL0
  have hR := hasGroupEndSums_right hadm hxR hxR0
  have hζ := h.ae_lifetime_eq_top hk hword hL hR
  have hRsep : ∀ᵐ ω ∂P, ∀ t : ℝ≥0, 0 < t → ∀ i, W t ω < VR i t ω := by
    rcases Nat.eq_zero_or_pos nR with hn | hn
    · exact Eventually.of_forall fun ω t _ i => absurd i.2 (by omega)
    · filter_upwards [h.ae_w_lt_vR hk hword hR hζ hn, hζ, h.ae_isIntegratedSLEPath]
        with ω h1 hζω hp t ht i
      have hlt : (t : ℝ≥0∞) < ζ ω := by rw [hζω]; exact ENNReal.coe_lt_top
      have h0i : (⟨0, hn⟩ : Fin nR) ≤ i := Fin.le_def.2 (Nat.zero_le _)
      exact (h1 t ht).trans_le (hp.isForcePath.monotone_vR hlt h0i)
  have hLsep : ∀ᵐ ω ∂P, ∀ t : ℝ≥0, 0 < t → ∀ i, VL i t ω < W t ω := by
    rcases Nat.eq_zero_or_pos nL with hn | hn
    · exact Eventually.of_forall fun ω t _ i => absurd i.2 (by omega)
    · have hword' : IsOrderedForceWord (-xR) (-xL) :=
        ⟨fun i j hij => neg_le_neg (hxR hij), fun i => neg_nonpos.2 (hxR0 i),
          fun i j hij => neg_le_neg (hxL hij), fun i => neg_nonneg.2 (hxL0 i)⟩
      filter_upwards [h.reflect.ae_w_lt_vR hk hword' hL hζ hn, hζ, h.ae_isIntegratedSLEPath]
        with ω h1 hζω hp t ht i
      have hlt : (t : ℝ≥0∞) < ζ ω := by rw [hζω]; exact ENNReal.coe_lt_top
      have h0i : (⟨0, hn⟩ : Fin nL) ≤ i := Fin.le_def.2 (Nat.zero_le _)
      have h2 := h1 t ht
      simp only [Pi.neg_apply, neg_lt_neg_iff] at h2
      exact (hp.isForcePath.antitone_vL hlt h0i).trans_lt h2
  filter_upwards [hζ, hRsep, hLsep] with ω h1 h2 h3
  exact ⟨h1, fun t ht => ⟨h3 t ht, h2 t ht⟩⟩


/-! ### Lemmas 4.3 and 4.5: the noncollision parts, unconditionally -/

section Charts

open Complex QuantumZipper
open scoped Real

variable {k : ℝ} {nL nR : ℕ} {xL : Fin nL → ℝ} {xR : Fin nR → ℝ} {ρL : Fin nL → ℝ}
  {ρR : Fin nR → ℝ}

/-- **Lemma 4.3, case `a ≤ −Λ`, noncollision part** (chart `e^{πz} − 1`): with the hypotheses of
`noncollision_of_aux6_expChart`, every evolution of the half-plane word has infinite lifetime and no
force point (in particular the image `−1` of the left strip end) meets the driver at a positive
time. -/
theorem noncollision_expChart (hk : 0 < k) (hword : IsOrderedForceWord xL xR) (E : Finset ℝ)
    {a : ℝ} (ha : a ≤ -sleLambda k)
    (hup : ∀ x : ℝ, -Real.exp (π * x) - 1 ∉ E →
      forceBoundaryData k ρL ρR xL xR (-Real.exp (π * x) - 1) =
        a + chiC k * (derivLogExpChart (x + I)).im)
    (hlowL : ∀ y : ℝ, -1 < y → y < 0 → y ∉ E → (∃ i, y < xL i) →
      forceBoundaryData k ρL ρR xL xR y ≤ -sleLambda k + π * chiC k)
    (hlowR : ∀ y : ℝ, 0 ≤ y → y ∉ E → (∃ i, xR i ≤ y) →
      sleLambda k - π * chiC k ≤ forceBoundaryData k ρL ρR xL xR y)
    {Ω : Type u} {mΩ : MeasurableSpace Ω} {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    {W : ℝ≥0 → Ω → ℝ} {VL : Fin nL → ℝ≥0 → Ω → ℝ} {VR : Fin nR → ℝ≥0 → Ω → ℝ}
    {B : ℝ≥0 → Ω → ℝ} {ζ : Ω → ℝ≥0∞}
    (hE : IsIntegratedSLEEvolution k xL xR ρL ρR P 𝓕 W VL VR B ζ) :
    ∀ᵐ ω ∂P, ζ ω = ⊤ ∧ ∀ t : ℝ≥0, 0 < t → (∀ i, VL i t ω < W t ω) ∧ ∀ i, W t ω < VR i t ω :=
  noncollision_of_aux6_expChart hk (aux6Statement hk) hword E ha hup hlowL hlowR hE

/-- Every `y > 1` is the image `1 + e^{−πx}` of a point `x + i` of the upper line under
`1 − e^{−πz}`. -/
theorem exists_leftEndChart_upper {y : ℝ} (hy : 1 < y) : ∃ x : ℝ, 1 + Real.exp (-(π * x)) = y := by
  refine ⟨-Real.log (y - 1) / π, ?_⟩
  rw [mul_div_cancel₀ _ Real.pi_pos.ne', neg_neg, Real.exp_log (by linarith)]
  ring

/-- **Lemma 4.3, case `a ≥ Λ`, noncollision part** (chart `1 − e^{−πz}`, left strip end as
target, right strip end at `1`): if the transported upper data are `b + X · arg ψ'` on `(1, ∞)` with
`b ≥ Λ`, and the lower data satisfy Remark 4.1 on `(−∞, 0)` and `[0, 1)` wherever a mark separates
the point from the seed (off a finite set `E`), then every evolution of the half-plane word has
infinite lifetime and no force point (in particular the image `1` of the right strip end) meets the
driver at a positive time. -/
theorem noncollision_leftEndChart (hk : 0 < k) (hword : IsOrderedForceWord xL xR) (E : Finset ℝ)
    {b : ℝ} (hb : sleLambda k ≤ b)
    (hup : ∀ x : ℝ, 1 + Real.exp (-(π * x)) ∉ E →
      forceBoundaryData k ρL ρR xL xR (1 + Real.exp (-(π * x))) =
        b + chiC k * (derivLogLeftEndChart (x + I)).im)
    (hlowL : ∀ y : ℝ, y < 0 → y ∉ E → (∃ i, y < xL i) →
      forceBoundaryData k ρL ρR xL xR y ≤ -sleLambda k + π * chiC k)
    (hlowR : ∀ y : ℝ, 0 ≤ y → y < 1 → y ∉ E → (∃ i, xR i ≤ y) →
      sleLambda k - π * chiC k ≤ forceBoundaryData k ρL ρR xL xR y)
    {Ω : Type u} {mΩ : MeasurableSpace Ω} {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    {W : ℝ≥0 → Ω → ℝ} {VL : Fin nL → ℝ≥0 → Ω → ℝ} {VR : Fin nR → ℝ≥0 → Ω → ℝ}
    {B : ℝ≥0 → Ω → ℝ} {ζ : Ω → ℝ≥0∞}
    (hE : IsIntegratedSLEEvolution k xL xR ρL ρR P 𝓕 W VL VR B ζ) :
    ∀ᵐ ω ∂P, ζ ω = ⊤ ∧ ∀ t : ℝ≥0, 0 < t → (∀ i, VL i t ω < W t ω) ∧ ∀ i, W t ω < VR i t ω := by
  refine aux6Statement hk xL xR ρL ρR P 𝓕 W VL VR B ζ hword ?_ hE
  refine hasAdmissiblePartialSums_of_forall_not_mem hk (insert 1 E)
    (fun y hy hyE hmark => hlowL y hy (fun h => hyE (Finset.mem_insert_of_mem h)) hmark)
    (fun y hy hyE hmark => ?_)
  have hy1 : y ≠ 1 := fun h => hyE (h ▸ Finset.mem_insert_self _ _)
  have hyE' : y ∉ E := fun h => hyE (Finset.mem_insert_of_mem h)
  rcases lt_or_gt_of_ne hy1 with h | h
  · exact hlowR y hy h hyE' hmark
  · obtain ⟨x, rfl⟩ := exists_leftEndChart_upper h
    rw [hup x hyE']
    exact leftEndChart_upper_height_ge hb x

/-- **Lemma 4.5, noncollision part** (chart `stripQ q`): with the hypotheses of
`noncollision_of_aux6_stripQ`, every evolution of the half-plane word has infinite lifetime and no
force point (in particular neither strip-end image `−1/q`, `1`) meets the driver at a positive
time. -/
theorem noncollision_stripQ (hk : 0 < k) (hword : IsOrderedForceWord xL xR) (E : Finset ℝ)
    {q : ℝ} (hq : 0 < q) {up : ℝ → ℝ}
    (hup_le : ∀ x : ℝ, Real.exp (π * x) < q → up x ≤ -sleLambda k)
    (hup_ge : ∀ x : ℝ, q < Real.exp (π * x) → sleLambda k ≤ up x)
    (htr : ∀ x : ℝ, Real.exp (π * x) ≠ q →
      (Real.exp (π * x) + 1) / (Real.exp (π * x) - q) ∉ E →
      forceBoundaryData k ρL ρR xL xR ((Real.exp (π * x) + 1) / (Real.exp (π * x) - q)) =
        up x + chiC k * (derivLogStripQ q (x + I)).im)
    (hlowL : ∀ y : ℝ, -(1 / q) < y → y < 0 → y ∉ E → (∃ i, y < xL i) →
      forceBoundaryData k ρL ρR xL xR y ≤ -sleLambda k + π * chiC k)
    (hlowR : ∀ y : ℝ, 0 ≤ y → y < 1 → y ∉ E → (∃ i, xR i ≤ y) →
      sleLambda k - π * chiC k ≤ forceBoundaryData k ρL ρR xL xR y)
    {Ω : Type u} {mΩ : MeasurableSpace Ω} {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    {W : ℝ≥0 → Ω → ℝ} {VL : Fin nL → ℝ≥0 → Ω → ℝ} {VR : Fin nR → ℝ≥0 → Ω → ℝ}
    {B : ℝ≥0 → Ω → ℝ} {ζ : Ω → ℝ≥0∞}
    (hE : IsIntegratedSLEEvolution k xL xR ρL ρR P 𝓕 W VL VR B ζ) :
    ∀ᵐ ω ∂P, ζ ω = ⊤ ∧ ∀ t : ℝ≥0, 0 < t → (∀ i, VL i t ω < W t ω) ∧ ∀ i, W t ω < VR i t ω :=
  noncollision_of_aux6_stripQ hk (aux6Statement hk) hword E hq hup_le hup_ge htr hlowL hlowR hE

end Charts

end Sec4

end InteractingSLE
