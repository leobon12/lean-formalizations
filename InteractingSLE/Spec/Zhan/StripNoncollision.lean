/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Zhan.StripNoncollisionLoc
import InteractingSLE.Spec.Zhan.StripEndpointStatement
import InteractingSLE.Spec.Sec2.CriticalLifetime
import InteractingSLE.Spec.Zhan.StripTimeDriver

/-!
# Noncollision on the strip life and the unbounded strip clock

Packet PROVE-ZHAN-A3. Astra, *Formalization proofs and dependency audit*, "Complete proof of noncollision"
(`source/external/AstraIG1/ig1_formalization_proofs.txt` L1103–L1169), for the strip evolution of ruling R36
(`Strip.IsStripSLEEvolution`) with separated lower marks and the prefix sums of (3.3) (`Strip.HasStripPrefixSums`).
Proved here, for every `κ > 0`:

* **the strip clock is unbounded on the strip life** (`ae_hasUnboundedStripClock`, clause (1) of
  `Strip.HasStripEndpoint`, the hypothesis `hclock` of PROVE-ZHAN-A2's `Zhan.exists_stripBrownian`);
* **noncollision on the strip life, including its end** (`ae_stripLife_noncollision`): at every time of the strip
  life the nearest lower marks are strictly separated from the driver, and on every finite strip-time window the
  strip gaps `X = ξ − p^L_1`, `Y = p^R_1 − ξ` and `log(W − v) = ξ − t` stay in a compact range
  (`ae_strip_bounds`: for each `N` there is `m` with `e^{−(m+1)} ≤ W − v ≤ e^{m+1}` and `X, Y ≥ 1/(m+1)` whenever
  `t(s) ≤ N`).

## Proof

A single Lyapunov process replaces Astra's comparison (3.14). With `G = W − v`, the nearest strip gaps `X`, `Y`
(`StripNoncollisionGen.lean`) and `H = ψ(G) + h(X) + h(Y)`, the process `Ψ = e^{−λ t(s)} H` has nonpositive chordal
generator along the evolution (`exists_itoGen_ncLyap_nonpos`, by the Abel bounds (3.12) and the increasing strip
distance `X + Y` of the nearest lower marks, `log_fR_sub_log_eL_ge`). Localized at `σ_{n,m}` (`ncLoc`), the localized
Itô formula gives `E[Ψ(σ_{n,m})] ≤ Ψ(0)` (`integral_ncLyap_ncLoc_le`). If the level-`m` constraints fail at a time
`s₁` of the strip life with `t(s₁) ≤ N`, then for all large `n` the time `σ_{n,m}` is the first failure, where
`H ≥ log(m+1)` and `t ≤ N`; Markov's inequality bounds the probability by `Ψ(0) e^{λN}/log(m+1) → 0`. Pathwise, a
bounded strip clock forces a failure: either the end mark reaches the driver (`G → 0` at a finite strip-life end;
the end-collision property `ae_endCollision`, from Aux. lemma 3, covers the end at a finite lifetime) or the strip
life is infinite with `G` unbounded (`∫ G⁻² < ∞`); a collision of a nearest lower mark makes `X` or `Y` vanish.
-/

set_option autoImplicit false

noncomputable section

open Set Filter MeasureTheory ProbabilityTheory Topology
open scoped NNReal ENNReal

universe u

namespace InteractingSLE

namespace Zhan

open Strip

variable {nL nR : ℕ}

/-! ### The end-collision property (from Aux. lemma 3) -/

section EndCollision

variable {κ τm : ℝ} {pL : Fin nL → ℝ} {pR : Fin nR → ℝ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ}
  {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ} {W : ℝ≥0 → Ω → ℝ}
  {VL : Fin (nL + 1) → ℝ≥0 → Ω → ℝ} {VR : Fin nR → ℝ≥0 → Ω → ℝ} {B : ℝ≥0 → Ω → ℝ} {ζ : Ω → ℝ≥0∞}

theorem sum_filter_castSucc {f : Fin (nL + 1) → ℝ} {p : Fin (nL + 1) → Prop} [DecidablePred p]
    (hlast : ¬ p (Fin.last nL)) :
    ∑ i ∈ Finset.univ.filter p, f i = ∑ i ∈ Finset.univ.filter (fun i : Fin nL => p i.castSucc), f i.castSucc := by
  rw [Finset.sum_filter, Finset.sum_filter, Fin.sum_univ_castSucc]
  simp [hlast]

/-- **The end-collision property.** For a strip evolution with separated marks and the prefix sums of (3.3),
almost surely, at a finite lifetime the end mark meets the driver: `W − v` takes arbitrarily small values before `ζ`
(Aux. lemma 3: at a finite lifetime some colliding group has weight `≤ −2`; groups of lower marks have weight
`≥ κ/2 − 2 > −2`, so the colliding group contains the end mark). In particular `ζ > 0`. -/
theorem ae_endCollision (hκ : 0 < κ) (hsep : IsSeparatedStripWord pL pR) (hpre : HasStripPrefixSums κ ρL ρR)
    (hE : IsStripSLEEvolution κ pL pR ρL ρR τm P 𝓕 W VL VR B ζ) :
    ∀ᵐ ω ∂P, ζ ω ≠ ⊤ → ∀ ε > 0, ∃ s : ℝ≥0, (s : ℝ≥0∞) < ζ ω ∧ W s ω - VL (Fin.last nL) s ω < ε := by
  have : IsProbabilityMeasure P :=
    hE.isFilteredBrownianReal.1.toIsPreBrownianReal.isGaussianProcess.isProbabilityMeasure
  have hc : (-2 : ℝ) < κ / 2 - 2 := by linarith
  have hgL : Sec4.HasGroupEndSums (κ / 2 - 2) ρL (fun i => (i : ℝ)) := hasGroupEndSums_of_prefix hpre.1
  have hgR : Sec4.HasGroupEndSums (κ / 2 - 2) ρR (fun i => (i : ℝ)) := hasGroupEndSums_of_prefix hpre.2
  have hxmono : ∀ n : ℕ, Monotone (fun i : Fin n => (i : ℝ)) := fun n i j hij =>
    Nat.cast_le.2 (Fin.le_iff_val_le_val.1 hij)
  have hxinj : ∀ (n : ℕ) (v : Fin n → ℝ) (i j : Fin n), (i : ℝ) = (j : ℝ) → v i = v j :=
    fun n v i j h => by rw [Fin.ext (by exact_mod_cast h : (i : ℕ) = j)]
  filter_upwards [IsIntegratedSLEEvolution.ae_tendsto_threshold hE hκ, hE.ae_isIntegratedSLEPath]
    with ω hlim hp hne ε hε
  by_contra hcon
  push Not at hcon
  have hfp := hp.isForcePath
  obtain ⟨T, hT⟩ : ∃ T : ℝ≥0, (T : ℝ≥0∞) = ζ ω := ⟨(ζ ω).toNNReal, ENNReal.coe_toNNReal hne⟩
  rcases eq_zero_or_pos T with hT0 | hT0
  · -- `ζ = 0`: the seed is not at the threshold
    have h0 : ζ ω = 0 := by rw [← hT, hT0, ENNReal.coe_zero]
    have hth := hfp.threshold_of_eq_zero h0
    unfold ForceWord.ThresholdCondition at hth
    have hL : ∑ i ∈ Finset.univ.filter (fun i => wordXL pL i = 0), wordRhoL ρL τm i = 0 := by
      refine Finset.sum_eq_zero fun i hi => absurd (Finset.mem_filter.1 hi).2 ?_
      induction i using Fin.lastCases with
      | last => simp
      | cast i =>
        simp only [wordXL_castSucc, sub_eq_zero]
        exact (Real.exp_lt_one_iff.2 (hsep.2.1 i)).ne
    have hR : ∑ j ∈ Finset.univ.filter (fun j => wordXR pR j = 0), ρR j = 0 := by
      refine Finset.sum_eq_zero fun j hj => absurd (Finset.mem_filter.1 hj).2 ?_
      simp only [wordXR, sub_eq_zero]
      exact (Real.one_lt_exp_iff.2 (hsep.2.2.2 j)).ne'
    rw [hL, hR] at hth
    rcases hth with h | h <;> linarith
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
    have hanti : Antitone vL₀ := fun i j hij =>
      le_of_tendsto_of_tendsto (hvL j) (hvL i) (hev.mono fun t ht => hfp.antitone_vL ht hij)
    have hmono : Monotone vR₀ := fun i j hij =>
      le_of_tendsto_of_tendsto (hvR i) (hvR j) (hev.mono fun t ht => hfp.monotone_vR ht hij)
    have hLw : ∀ i, vL₀ i ≤ w₀ := fun i =>
      le_of_tendsto_of_tendsto (hvL i) hw (hev.mono fun t ht => hfp.vL_le_w ht i)
    have hwR : ∀ i, w₀ ≤ vR₀ i := fun i =>
      le_of_tendsto_of_tendsto hw (hvR i) (hev.mono fun t ht => hfp.w_le_vR ht i)
    have hgap : ε ≤ w₀ - vL₀ (Fin.last nL) :=
      ge_of_tendsto (hw.sub (hvL _)) (hev.mono fun t ht => hcon t ht)
    unfold ForceWord.ThresholdCondition at hth
    rcases hth with hL | hR
    · have hlast : ¬ vL₀ (Fin.last nL) = w₀ := by intro h; rw [h] at hgap; linarith
      rw [sum_filter_castSucc hlast] at hL
      simp only [wordRhoL_castSucc] at hL
      have h := Sec4.neg_two_lt_sum_collision (v₀ := fun i : Fin nL => -vL₀ i.castSucc) (w₀ := -w₀) hc
        (hxmono nL) hgL (fun i j hij => neg_le_neg (hanti (Fin.castSucc_le_castSucc_iff.2 hij)))
        (fun i => neg_le_neg (hLw _)) (hxinj nL _)
      simp only [neg_inj] at h
      linarith
    · have h := Sec4.neg_two_lt_sum_collision hc (hxmono nR) hgR hmono hwR (hxinj nR vR₀)
      linarith

end EndCollision

/-! ### The strip distance of the nearest lower marks increases -/

section Distance

variable {a : ℝ} {pL : Fin nL → ℝ} {xR : Fin nR → ℝ} {ρL : Fin (nL + 1) → ℝ} {ρR : Fin nR → ℝ}
  {w : ℝ≥0 → ℝ} {vL : Fin (nL + 1) → ℝ≥0 → ℝ} {vR : Fin nR → ℝ≥0 → ℝ} {b : ℝ≥0 → ℝ} {ζ : ℝ≥0∞}

/-- The nearest lower left mark approaches the end mark: `V^{L,0}_s − v_s ≤ V^{L,0}_0 − v_0` on the strip life. -/
theorem eL_le_eL_zero (hp : IsIntegratedSLEPath a (wordXL pL) xR ρL ρR w vL vR b ζ) (hn : 0 < nL)
    {s : ℝ≥0} (hs : IsStripLife w (vL (Fin.last nL)) ζ s) :
    vL (Fin.castSucc ⟨0, hn⟩) s - vL (Fin.last nL) s ≤
      vL (Fin.castSucc ⟨0, hn⟩) 0 - vL (Fin.last nL) 0 := by
  have hF := hp.isForcePath
  set i₀ : Fin (nL + 1) := Fin.castSucc ⟨0, hn⟩
  have hint : ∀ i, IntervalIntegrable (fun u : ℝ => 2 / (vL i u.toNNReal - w u.toNNReal)) volume 0 s :=
    fun i => hF.intervalIntegrable_forceL hs.1 i
  have e1 := hF.vL_eq hs.1 i₀
  have e2 := hF.vL_eq hs.1 (Fin.last nL)
  have h0 : ∀ i, vL i 0 = (wordXL pL) i := hF.vL_zero
  rw [e1, e2, h0, h0]
  have hge : 0 ≤ ∫ u in (0 : ℝ)..s, (2 / (vL (Fin.last nL) u.toNNReal - w u.toNNReal) -
      2 / (vL i₀ u.toNNReal - w u.toNNReal)) := by
    refine intervalIntegral.integral_nonneg_of_ae_restrict s.coe_nonneg ?_
    have hnull := hF.volume_collisionL i₀
    rw [EventuallyLE, ae_restrict_iff' measurableSet_Icc]
    refine (measure_eq_zero_iff_ae_notMem.1 hnull).mono fun u hu huI => ?_
    have hu0 : 0 ≤ u := huI.1
    have hus : u.toNNReal ≤ s := Real.toNNReal_le_iff_le_coe.2 huI.2
    have hlt : (u.toNNReal : ℝ≥0∞) < ζ := lt_of_le_of_lt (by exact_mod_cast hus) hs.1
    have hne : w u.toNNReal ≠ vL i₀ u.toNNReal := fun h => hu ⟨hu0, hlt, h⟩
    have hG := hs.2 _ hus
    have hle1 : vL i₀ u.toNNReal ≤ w u.toNNReal := hF.vL_le_w hlt i₀
    have hlt1 : vL i₀ u.toNNReal < w u.toNNReal := lt_of_le_of_ne hle1 (Ne.symm hne)
    have hord : vL (Fin.last nL) u.toNNReal ≤ vL i₀ u.toNNReal := hF.antitone_vL hlt (Fin.le_last _)
    show (0 : ℝ) ≤ 2 / (vL (Fin.last nL) u.toNNReal - w u.toNNReal) -
      2 / (vL i₀ u.toNNReal - w u.toNNReal)
    have e1 : 2 / (vL (Fin.last nL) u.toNNReal - w u.toNNReal) =
        -(2 / (w u.toNNReal - vL (Fin.last nL) u.toNNReal)) := by rw [← neg_sub, div_neg]
    have e2 : 2 / (vL i₀ u.toNNReal - w u.toNNReal) = -(2 / (w u.toNNReal - vL i₀ u.toNNReal)) := by
      rw [← neg_sub, div_neg]
    rw [e1, e2]
    have := div_le_div_of_nonneg_left (by norm_num : (0 : ℝ) ≤ 2) (sub_pos.2 hlt1)
      (by linarith : w u.toNNReal - vL i₀ u.toNNReal ≤ w u.toNNReal - vL (Fin.last nL) u.toNNReal)
    linarith
  have := intervalIntegral.integral_sub (hint (Fin.last nL)) (hint i₀)
  linarith

/-- The nearest right mark moves away from the end mark: `V^{R,0}_0 − v_0 ≤ V^{R,0}_s − v_s` on the strip life. -/
theorem fR_zero_le_fR (hp : IsIntegratedSLEPath a (wordXL pL) xR ρL ρR w vL vR b ζ) (hn : 0 < nR)
    {s : ℝ≥0} (hs : IsStripLife w (vL (Fin.last nL)) ζ s) :
    vR ⟨0, hn⟩ 0 - vL (Fin.last nL) 0 ≤ vR ⟨0, hn⟩ s - vL (Fin.last nL) s := by
  have hF := hp.isForcePath
  have hintL : IntervalIntegrable (fun u : ℝ => 2 / (vL (Fin.last nL) u.toNNReal - w u.toNNReal))
      volume 0 s := hF.intervalIntegrable_forceL hs.1 _
  have hintR : IntervalIntegrable (fun u : ℝ => 2 / (vR ⟨0, hn⟩ u.toNNReal - w u.toNNReal)) volume 0 s :=
    hF.intervalIntegrable_forceR hs.1 _
  have e1 := hF.vR_eq hs.1 ⟨0, hn⟩
  have e2 := hF.vL_eq hs.1 (Fin.last nL)
  rw [e1, e2, hF.vR_zero, hF.vL_zero]
  have hge : 0 ≤ ∫ u in (0 : ℝ)..s, (2 / (vR ⟨0, hn⟩ u.toNNReal - w u.toNNReal) -
      2 / (vL (Fin.last nL) u.toNNReal - w u.toNNReal)) := by
    refine intervalIntegral.integral_nonneg s.coe_nonneg fun u hu => ?_
    have hus : u.toNNReal ≤ s := Sec2.toNNReal_le_of_mem_Icc hu
    have hlt : (u.toNNReal : ℝ≥0∞) < ζ := lt_of_le_of_lt (by exact_mod_cast hus) hs.1
    have hG := hs.2 _ hus
    have h1 : 0 ≤ 2 / (vR ⟨0, hn⟩ u.toNNReal - w u.toNNReal) :=
      div_nonneg (by norm_num) (sub_nonneg.2 (hF.w_le_vR hlt _))
    have h2 : 2 / (vL (Fin.last nL) u.toNNReal - w u.toNNReal) < 0 :=
      div_neg_of_pos_of_neg (by norm_num) (by linarith)
    linarith
  have := intervalIntegral.integral_sub hintR hintL
  linarith

end Distance

/-! ### Constants, measurability and the level of `H` at an exit -/

section Consts

/-- The cutoff `c₂`: a third of the initial strip distance `p^R_1 − p^L_1` of the nearest lower marks (`1` if a side
has no lower mark). -/
def ncC2 (pL : Fin nL → ℝ) (pR : Fin nR → ℝ) : ℝ :=
  if h : 0 < nL ∧ 0 < nR then (pR ⟨0, h.2⟩ - pL ⟨0, h.1⟩) / 3 else 1

theorem ncC2_pos {pL : Fin nL → ℝ} {pR : Fin nR → ℝ} (hsep : IsSeparatedStripWord pL pR) :
    0 < ncC2 pL pR := by
  unfold ncC2
  split_ifs with h
  · have := hsep.2.1 ⟨0, h.1⟩; have := hsep.2.2.2 ⟨0, h.2⟩; linarith
  · norm_num

theorem measurable_ncLyap (κ : ℝ) (xL : Fin (nL + 1) → ℝ) (xR : Fin nR → ℝ) (ρL : Fin (nL + 1) → ℝ)
    (ρR : Fin nR → ℝ) (β c₁ c₂ lam : ℝ) : Measurable (ncLyap κ xL xR ρL ρR β c₁ c₂ lam) := by
  have hg : Measurable (gapArg κ xL xR ρL ρR) := (contDiff_gapArg κ xL xR ρL ρR (n := 0)).continuous.measurable
  have hcut : Measurable (ncCut c₁ c₂) := (contDiff_ncCut (n := 0)).continuous.measurable
  have hK : Measurable (ncK β) := by unfold ncK; fun_prop
  have hH : Measurable (ncH β c₁ c₂) := hcut.mul hK
  have hpsi : Measurable ncPsi := by unfold ncPsi; fun_prop
  have hE : ∀ i : Fin nL, Measurable (ncEL (nR := nR) i) := fun i =>
    (contDiff_ncEL i (n := 0)).continuous.measurable
  have hF : ∀ j : Fin nR, Measurable (ncFR (nL := nL) j) := fun j =>
    (contDiff_ncFR j (n := 0)).continuous.measurable
  have hX : ∀ i, Measurable (ncX κ xL xR ρL ρR i) := fun i => hg.log.sub (hE i).log
  have hY : ∀ j, Measurable (ncY κ xL xR ρL ρR j) := fun j => (hF j).log.sub hg.log
  have hobs : Measurable (ncObs κ xL xR ρL ρR β c₁ c₂) := by
    unfold ncObs
    refine ((hpsi.comp hg).add ?_).add ?_
    · by_cases h : 0 < nL
      · simp only [h, ↓reduceDIte]; exact hH.comp (hX _)
      · simp only [h, ↓reduceDIte]; exact measurable_const
    · by_cases h : 0 < nR
      · simp only [h, ↓reduceDIte]; exact hH.comp (hY _)
      · simp only [h, ↓reduceDIte]; exact measurable_const
  unfold ncLyap
  exact (Measurable.exp (by fun_prop)).mul hobs

variable {κ : ℝ} {xL : Fin (nL + 1) → ℝ} {xR : Fin nR → ℝ} {ρL : Fin (nL + 1) → ℝ} {ρR : Fin nR → ℝ}

/-- **At an exit through the level-`m` constraints `H ≥ log(m+1)`** (for `1/(m+1) ≤ c₁`). -/
theorem log_le_ncObs_of_mLevel_nonpos {β c₁ c₂ : ℝ} (hβ : 0 ≤ β) (hc : c₁ < c₂) {m : ℕ}
    (hm : 1 / ((m : ℝ) + 1) ≤ c₁) {p : SCoord nL nR × ℝ} (hp : p ∈ ncRegion κ xL xR ρL ρR)
    (hlev : mLevel m (stateOf κ xL xR ρL ρR p) ≤ 0) :
    Real.log ((m : ℝ) + 1) ≤ ncObs κ xL xR ρL ρR β c₁ c₂ p := by
  have hm1 : (0 : ℝ) < (m : ℝ) + 1 := by positivity
  have hlogm : Real.log ((m : ℝ) + 1) ≤ (m : ℝ) + 1 := by
    have := Real.log_le_sub_one_of_pos hm1; linarith
  set Gv := gapArg κ xL xR ρL ρR p with hGv
  have hG : 0 < Gv := hp.1
  have hgs : (stateOf κ xL xR ρL ρR p).1 - (stateOf κ xL xR ρL ρR p).2.1 (Fin.last nL) = Gv := rfl
  have hLp : 0 ≤ (if h : 0 < nL then ncH β c₁ c₂ (ncX κ xL xR ρL ρR ⟨0, h⟩ p) else 0) := by
    by_cases hn : 0 < nL
    · simp only [hn, ↓reduceDIte]; exact ncH_nonneg hβ (ncX_pos hp hn)
    · simp only [hn, ↓reduceDIte, le_refl]
  have hRp : 0 ≤ (if h : 0 < nR then ncH β c₁ c₂ (ncY κ xL xR ρL ρR ⟨0, h⟩ p) else 0) := by
    by_cases hn : 0 < nR
    · simp only [hn, ↓reduceDIte]; exact ncH_nonneg hβ (ncY_pos hp hn)
    · simp only [hn, ↓reduceDIte, le_refl]
  have hpsi0 : 0 ≤ ncPsi Gv := (Real.log_nonneg (by norm_num)).trans (log_two_le_ncPsi hG)
  have hobs : ncObs κ xL xR ρL ρR β c₁ c₂ p = ncPsi Gv +
      (if h : 0 < nL then ncH β c₁ c₂ (ncX κ xL xR ρL ρR ⟨0, h⟩ p) else 0) +
      (if h : 0 < nR then ncH β c₁ c₂ (ncY κ xL xR ρL ρR ⟨0, h⟩ p) else 0) := rfl
  rw [hobs]
  -- one of the four constraints fails
  by_contra hcon
  push Not at hcon
  have hG1 : Real.exp (-((m : ℝ) + 1)) < Gv := by
    by_contra h; push Not at h
    have := neg_log_le_ncPsi Gv
    have h2 : -Real.log Gv ≥ (m : ℝ) + 1 := by
      have := Real.log_le_log hG h; rw [Real.log_exp] at this; linarith
    linarith
  have hG2 : Gv < Real.exp ((m : ℝ) + 1) := by
    by_contra h; push Not at h
    have := log_le_ncPsi hG
    have h2 : Real.log Gv ≥ (m : ℝ) + 1 := by
      have := Real.log_le_log (Real.exp_pos _) h; rw [Real.log_exp] at this; linarith
    linarith
  have hXc : ∀ hn : 0 < nL, ncEL ⟨0, hn⟩ p < Real.exp (-(1 / ((m : ℝ) + 1))) * Gv := by
    intro hn
    by_contra h; push Not at h
    have he := (hp.2.1 hn).1
    have hX0 := ncX_pos hp hn
    have hXle : ncX κ xL xR ρL ρR ⟨0, hn⟩ p ≤ 1 / ((m : ℝ) + 1) := by
      have := Real.log_le_log (by positivity) h
      rw [Real.log_mul (Real.exp_pos _).ne' hG.ne', Real.log_exp] at this
      simp only [ncX, ← hGv]; linarith
    have hh := log_le_ncH (β := β) hβ hc hX0 (hXle.trans hm)
    have hl : Real.log ((m : ℝ) + 1) ≤ -Real.log (ncX κ xL xR ρL ρR ⟨0, hn⟩ p) := by
      rw [← Real.log_inv]
      refine Real.log_le_log hm1 ?_
      rw [le_inv_comm₀ hm1 hX0]; simpa [one_div] using hXle
    simp only [hn, ↓reduceDIte] at hcon hRp
    linarith
  have hYc : ∀ hn : 0 < nR, Gv < Real.exp (-(1 / ((m : ℝ) + 1))) * ncFR ⟨0, hn⟩ p := by
    intro hn
    by_contra h; push Not at h
    have hf : 0 < ncFR (nL := nL) ⟨0, hn⟩ p := hG.trans (hp.2.2 hn)
    have hY0 := ncY_pos hp hn
    have hYle : ncY κ xL xR ρL ρR ⟨0, hn⟩ p ≤ 1 / ((m : ℝ) + 1) := by
      have := Real.log_le_log (by positivity) h
      rw [Real.log_mul (Real.exp_pos _).ne' hf.ne', Real.log_exp] at this
      simp only [ncY, ← hGv]; linarith
    have hh := log_le_ncH (β := β) hβ hc hY0 (hYle.trans hm)
    have hl : Real.log ((m : ℝ) + 1) ≤ -Real.log (ncY κ xL xR ρL ρR ⟨0, hn⟩ p) := by
      rw [← Real.log_inv]
      refine Real.log_le_log hm1 ?_
      rw [le_inv_comm₀ hm1 hY0]; simpa [one_div] using hYle
    simp only [hn, ↓reduceDIte] at hcon hLp
    linarith
  -- then `mLevel > 0`
  have hpos : 0 < mLevel m (stateOf κ xL xR ρL ρR p) := by
    unfold mLevel
    rw [hgs]
    refine lt_min (lt_min (by linarith) (by linarith)) (lt_min ?_ ?_)
    · by_cases hn : 0 < nL
      · simp only [hn, ↓reduceDIte]; have := hXc hn; simp only [ncEL, stateOf] at this ⊢; linarith
      · simp only [hn, ↓reduceDIte, zero_lt_one]
    · by_cases hn : 0 < nR
      · simp only [hn, ↓reduceDIte]; have := hYc hn; simp only [ncFR, stateOf] at this ⊢; linarith
      · simp only [hn, ↓reduceDIte, zero_lt_one]
  linarith

end Consts

/-! ### The strip distance condition along the path -/

section PathD

variable {a : ℝ} {pL : Fin nL → ℝ} {pR : Fin nR → ℝ} {ρL : Fin (nL + 1) → ℝ} {ρR : Fin nR → ℝ}
  {w : ℝ≥0 → ℝ} {vL : Fin (nL + 1) → ℝ≥0 → ℝ} {vR : Fin nR → ℝ≥0 → ℝ} {b : ℝ≥0 → ℝ} {ζ : ℝ≥0∞}

/-- **Along the strip life the two nearest strip gaps satisfy `X + Y > 2 c₂`**: `X + Y = log(V^{R,0} − v) −
log(V^{L,0} − v)` is at least its initial value `p^R_1 − p^L_1 = 3c₂`. -/
theorem two_ncC2_lt (κ' : ℝ) (xL' : Fin (nL + 1) → ℝ) (xR' : Fin nR → ℝ) (ρL' : Fin (nL + 1) → ℝ)
    (ρR' : Fin nR → ℝ) (hp : IsIntegratedSLEPath a (wordXL pL) (wordXR pR) ρL ρR w vL vR b ζ)
    (hsep : IsSeparatedStripWord pL pR) {s : ℝ≥0} (hs : IsStripLife w (vL (Fin.last nL)) ζ s)
    (T y : ℝ) (hL : 0 < nL) (hR : 0 < nR) :
    2 * ncC2 pL pR < ncX κ' xL' xR' ρL' ρR' ⟨0, hL⟩ (((fun i => vL i s), (fun j => vR j s), T), y) +
      ncY κ' xL' xR' ρL' ρR' ⟨0, hR⟩ (((fun i => vL i s), (fun j => vR j s), T), y) := by
  have hF := hp.isForcePath
  have he := vL_last_lt_vL_castSucc hp hs ⟨0, hL⟩
  have hele := eL_le_eL_zero hp hL hs
  have hfge := fR_zero_le_fR hp hR hs
  have h0L : vL (Fin.castSucc ⟨0, hL⟩) 0 - vL (Fin.last nL) 0 = Real.exp (pL ⟨0, hL⟩) := by
    rw [hF.vL_zero, hF.vL_zero, wordXL_castSucc, wordXL_last]; ring
  have h0R : vR ⟨0, hR⟩ 0 - vL (Fin.last nL) 0 = Real.exp (pR ⟨0, hR⟩) := by
    rw [hF.vR_zero, hF.vL_zero, wordXL_last]; simp only [wordXR]; ring
  rw [h0L] at hele
  rw [h0R] at hfge
  have hsum : ncX κ' xL' xR' ρL' ρR' ⟨0, hL⟩ (((fun i => vL i s), (fun j => vR j s), T), y) +
      ncY κ' xL' xR' ρL' ρR' ⟨0, hR⟩ (((fun i => vL i s), (fun j => vR j s), T), y) =
      Real.log (vR ⟨0, hR⟩ s - vL (Fin.last nL) s) -
        Real.log (vL (Fin.castSucc ⟨0, hL⟩) s - vL (Fin.last nL) s) := by
    simp only [ncX, ncY, ncEL, ncFR]; ring
  rw [hsum]
  have h1 := Real.log_le_log (Real.exp_pos _) hfge
  have h2 := Real.log_le_log (sub_pos.2 he) hele
  rw [Real.log_exp] at h1 h2
  have hc : ncC2 pL pR = (pR ⟨0, hR⟩ - pL ⟨0, hL⟩) / 3 := by
    simp only [ncC2, hL, hR, and_self, ↓reduceDIte]
  have hpos : 0 < pR ⟨0, hR⟩ - pL ⟨0, hL⟩ := by
    have := hsep.2.1 ⟨0, hL⟩; have := hsep.2.2.2 ⟨0, hR⟩; linarith
  rw [hc]; linarith

end PathD

/-! ### The expectation bound -/

section Expect

variable {κ τm : ℝ} {pL : Fin nL → ℝ} {pR : Fin nR → ℝ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ}
  {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ} {W : ℝ≥0 → Ω → ℝ}
  {VL : Fin (nL + 1) → ℝ≥0 → Ω → ℝ} {VR : Fin nR → ℝ≥0 → Ω → ℝ} {B : ℝ≥0 → Ω → ℝ} {ζ : Ω → ℝ≥0∞}
  {G : Set Ω}

theorem stripInit_mem_ncRegion_word (hsep : IsSeparatedStripWord pL pR) :
    stripInit (wordXL pL) (wordXR pR) ∈ ncRegion κ (wordXL pL) (wordXR pR) (wordRhoL ρL τm) ρR := by
  refine stripInit_mem_ncRegion κ _ _ _ _ (by simp) (fun h => ⟨?_, ?_⟩) (fun h => ?_)
  · simp only [wordXL_last, wordXL_castSucc]; linarith [Real.exp_pos (pL ⟨0, h⟩)]
  · simp only [wordXL_castSucc, sub_neg]; exact Real.exp_lt_one_iff.2 (hsep.2.1 _)
  · simp only [wordXR, sub_pos]; exact Real.one_lt_exp_iff.2 (hsep.2.2.2 _)

/-- **`E[Ψ(σ_{n,m})] ≤ Ψ(0)`**: the localized Itô formula with a nonpositive generator. -/
theorem integral_ncLyap_ncLoc_le (hsep : IsSeparatedStripWord pL pR)
    (hE : IsStripSLEEvolution κ pL pR ρL ρR τm P 𝓕 W VL VR B ζ) (hGm : MeasurableSet G) (hGc : P Gᶜ = 0)
    (hgood : ∀ ω ∈ G, IsNcGood κ (wordXL pL) (wordXR pR) (wordRhoL ρL τm) ρR W VL VR B ζ ω)
    {β c₁ lam : ℝ}
    (hgen : ∀ (vL : Fin (nL + 1) → ℝ) (vR : Fin nR → ℝ) (T b w : ℝ),
      w = Real.sqrt κ * b + driftLin (wordXL pL) (wordXR pR) (wordRhoL ρL τm) ρR (vL, vR, T) →
      ((vL, vR, T), b) ∈ ncRegion κ (wordXL pL) (wordXR pR) (wordRhoL ρL τm) ρR → Antitone vL →
      Monotone vR →
      (∀ (hL : 0 < nL) (hR : 0 < nR), 2 * ncC2 pL pR <
        ncX κ (wordXL pL) (wordXR pR) (wordRhoL ρL τm) ρR ⟨0, hL⟩ ((vL, vR, T), b) +
        ncY κ (wordXL pL) (wordXR pR) (wordRhoL ρL τm) ρR ⟨0, hR⟩ ((vL, vR, T), b)) →
      Ito.itoGen (ncLyap κ (wordXL pL) (wordXR pR) (wordRhoL ρL τm) ρR β c₁ (ncC2 pL pR) lam)
        ((vL, vR, T), b) (stripDens w vL vR) ≤ 0) (n m : ℕ) :
    Integrable (fun ω => ncLyap κ (wordXL pL) (wordXR pR) (wordRhoL ρL τm) ρR β c₁ (ncC2 pL pR) lam
      (coordS (wordXL pL) (wordXR pR) G W VL VR (ncLoc G W VL VR B ζ n m ω) ω,
        Sec2.TwoSeed.brownG G B (ncLoc G W VL VR B ζ n m ω) ω)) P ∧
    ∫ ω, ncLyap κ (wordXL pL) (wordXR pR) (wordRhoL ρL τm) ρR β c₁ (ncC2 pL pR) lam
      (coordS (wordXL pL) (wordXR pR) G W VL VR (ncLoc G W VL VR B ζ n m ω) ω,
        Sec2.TwoSeed.brownG G B (ncLoc G W VL VR B ζ n m ω) ω) ∂P ≤
      ncLyap κ (wordXL pL) (wordXR pR) (wordRhoL ρL τm) ρR β c₁ (ncC2 pL pR) lam
        (stripInit (wordXL pL) (wordXR pR)) := by
  have : IsProbabilityMeasure P :=
    hE.isFilteredBrownianReal.1.toIsPreBrownianReal.isGaussianProcess.isProbabilityMeasure
  set xL := wordXL pL with hxL
  set xR := wordXR pR with hxR
  set ρL' := wordRhoL ρL τm with hρL'
  set c₂ := ncC2 pL pR with hc₂
  set Ψ := ncLyap κ xL xR ρL' ρR β c₁ c₂ lam with hΨ
  set σ := ncLoc G W VL VR B ζ n m with hσ
  have h0 : xL (Fin.last nL) < 0 := by simp [hxL]
  have hreg := stripInit_mem_ncRegion_word (κ := κ) (ρL := ρL) (ρR := ρR) (τm := τm) hsep
  have hM := martingale_ncLyap hE hGm hGc hgood h0 hreg β c₁ c₂ lam n m
  have hmin : ∀ ω, min (n : ℝ≥0) (σ ω) = σ ω := fun ω => min_eq_right (ncLoc_le n m ω)
  -- the path points stay in the compact box
  have hK : ∀ ω (t : ℝ≥0), t ≤ σ ω →
      (coordS xL xR G W VL VR t ω, Sec2.TwoSeed.brownG G B t ω) ∈ ncKc κ xL xR ρL' ρR n m := by
    intro ω t ht
    by_cases hω : ω ∈ G
    · simpa only [coordS, Sec2.TwoSeed.brownG, hω, ↓reduceIte] using
        mem_ncKc_of_le_ncLoc (hgood ω hω) hω hgood h0 ht
    · simp only [coordS, Sec2.TwoSeed.brownG, hω, ↓reduceIte]
      exact mem_insert _ _
  -- boundedness and measurability of `Ψ(σ)`
  have hcont : ContinuousOn Ψ (ncKc κ xL xR ρL' ρR n m) :=
    contDiffOn_ncLyap.continuousOn.mono (ncKc_subset_region κ xL xR ρL' ρR hreg n m)
  obtain ⟨C, hC⟩ := (isCompact_ncKc κ xL xR ρL' ρR n m).exists_bound_of_continuousOn hcont
  have hmeas : Measurable fun ω => Ψ (coordS xL xR G W VL VR (σ ω) ω,
      Sec2.TwoSeed.brownG G B (σ ω) ω) := by
    have h1 := (measurable_coordS_ncLoc hE hGm hGc hgood h0 n m n).mono
      ((usualAugmentation 𝓕 P).le n) le_rfl
    have h2 := (measurable_brownG_ncLoc hE hGm hGc hgood n m n).mono
      ((usualAugmentation 𝓕 P).le n) le_rfl
    rw [← hσ] at h1 h2
    simp only [hmin] at h1 h2
    exact (measurable_ncLyap κ xL xR ρL' ρR β c₁ c₂ lam).comp (h1.prodMk h2)
  have hint : Integrable (fun ω => Ψ (coordS xL xR G W VL VR (σ ω) ω,
      Sec2.TwoSeed.brownG G B (σ ω) ω)) P :=
    (integrable_const C).mono' hmeas.aestronglyMeasurable (Eventually.of_forall fun ω =>
      hC _ (hK ω (σ ω) le_rfl))
  refine ⟨hint, ?_⟩
  -- the drift integral is nonpositive
  have hI : ∀ ω, ∫ s in (0 : ℝ)..(σ ω : ℝ), Ito.itoGen Ψ
      (coordS xL xR G W VL VR s.toNNReal ω, Sec2.TwoSeed.brownG G B s.toNNReal ω)
      (densS G W VL VR s ω) ≤ 0 := by
    intro ω
    by_cases hω : ω ∈ G
    · have hωg := hgood ω hω
      have hF := hωg.1.isForcePath
      have hlife := isStripLife_ncLoc hωg hω h0 (n := n) (m := m)
      rw [← neg_nonneg, ← intervalIntegral.integral_neg]
      refine intervalIntegral.integral_nonneg (σ ω).coe_nonneg fun u hu => ?_
      have hr : u.toNNReal ≤ σ ω := Sec2.toNNReal_le_of_mem_Icc hu
      have hlr := hlife.mono hr
      have hpK := hK ω _ hr
      simp only [coordS, densS, Sec2.TwoSeed.brownG, hω, ↓reduceIte] at hpK ⊢
      have hreg' := ncKc_subset_region κ xL xR ρL' ρR hreg n m hpK
      refine neg_nonneg.2 (hgen (fun i => VL i u.toNNReal ω) (fun j => VR j u.toNNReal ω)
        (Strip.stripClock (Strip.extPath (W · ω)) (Strip.extPath (VL (Fin.last nL) · ω)) u.toNNReal)
        (B u.toNNReal ω) (W u.toNNReal ω) (w_eq_driftLin hωg.1 hlr.1) hreg'
        (hF.antitone_vL hlr.1) (hF.monotone_vR hlr.1) fun hL hR => ?_)
      exact two_ncC2_lt κ xL xR ρL' ρR hωg.1 hsep hlr _ _ hL hR
    · rw [hσ, ncLoc_of_not_mem hω, NNReal.coe_zero, intervalIntegral.integral_same]
  -- the martingale identity at times `0` and `n`
  set M : ℝ≥0 → Ω → ℝ := fun t ω => Ψ (coordS xL xR G W VL VR (min t (σ ω)) ω,
      Sec2.TwoSeed.brownG G B (min t (σ ω)) ω) -
      ∫ s in (0 : ℝ)..(min t (σ ω) : ℝ≥0), Ito.itoGen Ψ
        (coordS xL xR G W VL VR s.toNNReal ω, Sec2.TwoSeed.brownG G B s.toNNReal ω)
        (densS G W VL VR s ω) with hMdef
  have hM0 : ∀ ω, M 0 ω = Ψ (stripInit xL xR) := by
    intro ω
    simp only [hMdef, zero_min, NNReal.coe_zero, intervalIntegral.integral_same, sub_zero]
    by_cases hω : ω ∈ G
    · simp only [coordS, Sec2.TwoSeed.brownG, hω, ↓reduceIte]
      rw [stripCoordAt_zero_eq_nc (hgood ω hω)]
    · simp only [coordS, Sec2.TwoSeed.brownG, hω, ↓reduceIte]; rfl
  have heq : ∫ ω, M 0 ω ∂P = ∫ ω, M n ω ∂P := by
    have := hM.setIntegral_eq (zero_le (a := (n : ℝ≥0))) MeasurableSet.univ
    simpa only [setIntegral_univ] using this
  have h0int : ∫ ω, M 0 ω ∂P = Ψ (stripInit xL xR) := by
    simp only [hM0, integral_const, probReal_univ, one_smul]
  calc ∫ ω, Ψ (coordS xL xR G W VL VR (σ ω) ω, Sec2.TwoSeed.brownG G B (σ ω) ω) ∂P
      ≤ ∫ ω, M n ω ∂P := by
        refine integral_mono hint (hM.integrable n) fun ω => ?_
        simp only [hMdef, hmin]
        linarith [hI ω]
    _ = Ψ (stripInit xL xR) := by rw [← heq, h0int]

end Expect

/-! ### Exhaustion: a failure of the level-`m` constraints is seen by `σ_{n,m}` for large `n` -/

section Exhaust

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {κ : ℝ} {xL : Fin (nL + 1) → ℝ} {xR : Fin nR → ℝ}
  {ρL : Fin (nL + 1) → ℝ} {ρR : Fin nR → ℝ} {W : ℝ≥0 → Ω → ℝ} {VL : Fin (nL + 1) → ℝ≥0 → Ω → ℝ}
  {VR : Fin nR → ℝ≥0 → Ω → ℝ} {B : ℝ≥0 → Ω → ℝ} {ζ : Ω → ℝ≥0∞} {G : Set Ω}

/-- **Exhaustion.** If the level-`m` constraints fail at a time `s₁` of the strip life of a good path, then for all
large `n` the localizing time `σ_{n,m}` is at most `s₁` and is a failure time of the level-`m` constraints. -/
theorem exists_ncLoc_exit (hgood : ∀ ω ∈ G, IsNcGood κ xL xR ρL ρR W VL VR B ζ ω)
    (hxL : ∀ i : Fin nL, xL (Fin.last nL) < xL i.castSucc) {ω : Ω} (hωG : ω ∈ G) {m : ℕ} {s₁ : ℝ≥0}
    (hs : IsStripLife (W · ω) (VL (Fin.last nL) · ω) (ζ ω) s₁)
    (hm : mLevel m (Coupling.stateAt W VL VR s₁ ω) < 0) :
    ∃ n₀ : ℕ, ∀ n, n₀ ≤ n → ncLoc G W VL VR B ζ n m ω ≤ s₁ ∧
      mLevel m (Coupling.stateAt W VL VR (ncLoc G W VL VR B ζ n m ω) ω) ≤ 0 := by
  have hω := hgood ω hωG
  have hF := hω.1.isForcePath
  have hsub : Icc (0 : ℝ≥0) s₁ ⊆ {r : ℝ≥0 | (r : ℝ≥0∞) < ζ ω} := fun r hr =>
    lt_of_le_of_lt (by exact_mod_cast hr.2) hs.1
  have hne : (Icc (0 : ℝ≥0) s₁).Nonempty := ⟨0, le_rfl, bot_le⟩
  -- a uniform lower bound for `W − v` and the lower left gaps on `[0, s₁]`
  have hGc : ContinuousOn (fun r => W r ω - VL (Fin.last nL) r ω) (Icc 0 s₁) :=
    (hF.continuousOn_w.sub (hF.continuousOn_vL _)).mono hsub
  obtain ⟨r₀, hr₀, hmin₀⟩ := isCompact_Icc.exists_isMinOn hne hGc
  have hG0 : 0 < W r₀ ω - VL (Fin.last nL) r₀ ω := sub_pos.2 (hs.2 r₀ hr₀.2)
  have hgap : ∀ i : Fin nL, ∃ δ > 0, ∀ r ∈ Icc (0 : ℝ≥0) s₁,
      δ ≤ VL i.castSucc r ω - VL (Fin.last nL) r ω := fun i => by
    have hc : ContinuousOn (fun r => VL i.castSucc r ω - VL (Fin.last nL) r ω) (Icc 0 s₁) :=
      ((hF.continuousOn_vL _).sub (hF.continuousOn_vL _)).mono hsub
    obtain ⟨r₁, hr₁, hmin₁⟩ := isCompact_Icc.exists_isMinOn hne hc
    refine ⟨_, sub_pos.2 (hF.vL_lt_vL_of_lt ((hs.mono hr₁.2).1) (hxL i)
      fun r hr => hs.2 r (hr.trans hr₁.2)), fun r hr => hmin₁ hr⟩
  choose δi hδi hδile using hgap
  obtain ⟨δg, hδg, hδglt⟩ : ∃ δ > 0, ∀ i : Fin nL, δ < δi i := by
    set S := insert (1 : ℝ) (Finset.univ.image δi)
    have hS : S.Nonempty := Finset.insert_nonempty _ _
    have h0 : 0 < S.min' hS := (Finset.lt_min'_iff S hS).2 fun y hy => by
      rcases Finset.mem_insert.1 hy with rfl | hy
      · norm_num
      · obtain ⟨i, -, rfl⟩ := Finset.mem_image.1 hy; exact hδi i
    refine ⟨S.min' hS / 2, by linarith, fun i => ?_⟩
    have := Finset.min'_le S _ (Finset.mem_insert_of_mem (Finset.mem_image_of_mem δi
      (Finset.mem_univ i)))
    linarith
  -- bounds for the state and the Brownian path on `[0, s₁]`
  have hstc : ContinuousOn (fun r => ‖Coupling.stateAt W VL VR r ω‖) (Icc 0 s₁) :=
    (hF.continuousOn_w.prodMk ((continuousOn_pi.2 hF.continuousOn_vL).prodMk
      (continuousOn_pi.2 hF.continuousOn_vR))).norm.mono hsub
  obtain ⟨r₂, hr₂, hmax₂⟩ := isCompact_Icc.exists_isMaxOn hne hstc
  obtain ⟨r₃, hr₃, hmax₃⟩ := isCompact_Icc.exists_isMaxOn hne (hω.2.1.abs.continuousOn (s := Icc 0 s₁))
  set δ := min (W r₀ ω - VL (Fin.last nL) r₀ ω) δg with hδ
  have hδpos : 0 < δ := lt_min hG0 hδg
  obtain ⟨n₀, hn₀⟩ := exists_nat_gt (max (max (s₁ : ℝ) (‖Coupling.stateAt W VL VR r₂ ω‖ + |B r₃ ω| + 1))
    (1 / δ))
  refine ⟨n₀, fun n hn => ?_⟩
  have hn' : (n₀ : ℝ) ≤ n := by exact_mod_cast hn
  have hns : (s₁ : ℝ) < n := ((le_max_left _ _).trans_lt ((le_max_left _ _).trans_lt hn₀)).trans_le hn'
  have hnR : ‖Coupling.stateAt W VL VR r₂ ω‖ + |B r₃ ω| + 1 < n :=
    ((le_max_right _ _).trans_lt ((le_max_left _ _).trans_lt hn₀)).trans_le hn'
  have hnδ : 1 / δ < n := ((le_max_right _ _).trans_lt hn₀).trans_le hn'
  have hδn : 1 / ((n : ℝ) + 1) ≤ δ := by
    rw [div_le_iff₀ (by positivity)]
    rw [div_lt_iff₀ hδpos] at hnδ
    nlinarith
  -- the level-`n` box is kept on `[0, s₁]`
  have hlev : ∀ r ∈ Icc (0 : ℝ≥0) s₁,
      0 ≤ levelFun (1 / ((n : ℝ) + 1)) n (Coupling.stateAt W VL VR r ω) := by
    intro r hr
    refine levelFun_nonneg_iff.2 ⟨?_, ?_, fun i => ?_⟩
    · simp only [Coupling.stateAt]
      exact hδn.trans ((min_le_left _ _).trans (hmin₀ hr))
    · have := isMaxOn_iff.1 hmax₂ r hr
      have h3 := abs_nonneg (B r₃ ω)
      linarith
    · simp only [Coupling.stateAt]
      exact hδn.trans ((min_le_right _ _).trans ((hδglt i).le.trans (hδile i r hr)))
  have hhit : (s₁ : WithTop ℝ≥0) ≤ hitLevel G W VL VR ζ n ω := by
    simp only [hitLevel, hωG, ↓reduceIte]
    refine Coupling.le_hitBelow fun r hrζ hr => ?_
    by_contra hlt
    push Not at hlt
    exact absurd (hlev r ⟨bot_le, hlt.le⟩) (not_le.2 hr)
  have hexit : (s₁ : WithTop ℝ≥0) ≤ MathFin.exitTime (Sec2.TwoSeed.brownG G B) n ω := by
    by_contra hlt
    push Not at hlt
    obtain ⟨u, hu⟩ := WithTop.ne_top_iff_exists.1 (ne_top_of_lt hlt)
    obtain ⟨r, hr, hBr⟩ := (MathFin.exitTime_le_iff (continuous_brownG_nc hgood) n u ω).1 hu.symm.le
    have hus : u < s₁ := by rw [← hu] at hlt; exact WithTop.coe_lt_coe.1 hlt
    have hrs : r ∈ Icc (0 : ℝ≥0) s₁ := ⟨bot_le, hr.2.trans hus.le⟩
    have := isMaxOn_iff.1 hmax₃ r hrs
    simp only [Sec2.TwoSeed.brownG, hωG, ↓reduceIte] at hBr
    have h2 := norm_nonneg (Coupling.stateAt W VL VR r₂ ω)
    linarith
  -- the level-`m` failure time
  set f : ℝ≥0 → ℝ := fun s => mLevel m (Coupling.stateAt W VL VR s ω) with hf
  have hfle : Coupling.hitBelow f (ζ ω) 0 ≤ s₁ := Coupling.hitBelow_le hs.1 hm
  obtain ⟨t, ht⟩ := WithTop.ne_top_iff_exists.1 (ne_top_of_le_ne_top WithTop.coe_ne_top hfle)
  have hts : t ≤ s₁ := by rw [← ht] at hfle; exact WithTop.coe_le_coe.1 hfle
  have hM : hitM G W VL VR ζ m ω = t := by simp only [hitM, hωG, ↓reduceIte]; exact ht.symm
  have hσ : ncLoc G W VL VR B ζ n m ω = t := by
    have e := coe_ncLoc (G := G) (W := W) (VL := VL) (VR := VR) (B := B) (ζ := ζ) n m ω
    rw [hM] at e
    have h1 : ((t : ℝ≥0) : WithTop ℝ≥0) ≤ ((n : ℝ≥0) : WithTop ℝ≥0) :=
      WithTop.coe_le_coe.2 (hts.trans (by rw [← NNReal.coe_le_coe, NNReal.coe_natCast]; exact hns.le))
    have h2 : ((t : ℝ≥0) : WithTop ℝ≥0) ≤ hitLevel G W VL VR ζ n ω :=
      (WithTop.coe_le_coe.2 hts).trans hhit
    have h3 : ((t : ℝ≥0) : WithTop ℝ≥0) ≤ MathFin.exitTime (Sec2.TwoSeed.brownG G B) n ω :=
      (WithTop.coe_le_coe.2 hts).trans hexit
    rw [min_eq_right h2, min_eq_left h3, min_eq_right h1] at e
    exact WithTop.coe_inj.1 e
  refine ⟨hσ ▸ hts, ?_⟩
  rw [hσ]
  exact Coupling.le_of_hitBelow_eq (continuousOn_comp_stateAt (continuous_mLevel m) hF) ht.symm

end Exhaust

/-! ### The main estimate -/

section Main

variable {κ τm : ℝ} {pL : Fin nL → ℝ} {pR : Fin nR → ℝ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ}
  {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ} {W : ℝ≥0 → Ω → ℝ}
  {VL : Fin (nL + 1) → ℝ≥0 → Ω → ℝ} {VR : Fin nR → ℝ≥0 → Ω → ℝ} {B : ℝ≥0 → Ω → ℝ} {ζ : Ω → ℝ≥0∞}

/-- Good paths form a measurable event of full measure. -/
theorem exists_ncGood (hκ : 0 < κ) (hsep : IsSeparatedStripWord pL pR) (hpre : HasStripPrefixSums κ ρL ρR)
    (hE : IsStripSLEEvolution κ pL pR ρL ρR τm P 𝓕 W VL VR B ζ) :
    ∃ G : Set Ω, MeasurableSet G ∧ P Gᶜ = 0 ∧
      ∀ ω ∈ G, IsNcGood κ (wordXL pL) (wordXR pR) (wordRhoL ρL τm) ρR W VL VR B ζ ω := by
  have hae : ∀ᵐ ω ∂P, IsNcGood κ (wordXL pL) (wordXR pR) (wordRhoL ρL τm) ρR W VL VR B ζ ω := by
    filter_upwards [hE.ae_isIntegratedSLEPath, hE.1.1.cont, hE.1.1.eval_zero_ae_eq_zero,
      ae_endCollision hκ hsep hpre hE] with ω h1 h2 h3 h4
    exact ⟨h1, h2, h3, h4⟩
  refine ⟨(toMeasurable P {ω | ¬ IsNcGood κ (wordXL pL) (wordXR pR) (wordRhoL ρL τm) ρR W VL VR B ζ ω})ᶜ,
    (measurableSet_toMeasurable _ _).compl, ?_, fun ω hω => ?_⟩
  · rw [compl_compl, measure_toMeasurable]; exact ae_iff.1 hae
  · by_contra h; exact hω (subset_toMeasurable _ _ h)

/-- **The strip bounds.** For a strip evolution with `κ > 0`, separated lower marks and the prefix sums of (3.3),
almost surely, for every strip-time horizon `N` there is a level `m` such that at every time `s` of the strip life
with `t(s) ≤ N`: `e^{−(m+1)} ≤ W − v ≤ e^{m+1}`, and the nearest lower strip gaps are at least `1/(m+1)`
(`mLevel m ≥ 0`). -/
theorem ae_strip_bounds (hκ : 0 < κ) (hsep : IsSeparatedStripWord pL pR) (hpre : HasStripPrefixSums κ ρL ρR)
    (hE : IsStripSLEEvolution κ pL pR ρL ρR τm P 𝓕 W VL VR B ζ) :
    ∀ᵐ ω ∂P, ∀ N : ℕ, ∃ m : ℕ, ∀ s : ℝ≥0, IsStripLife (W · ω) (VL (Fin.last nL) · ω) (ζ ω) s →
      stripClock (extPath (W · ω)) (extPath (VL (Fin.last nL) · ω)) s ≤ N →
      0 ≤ mLevel m (Coupling.stateAt W VL VR s ω) := by
  have : IsProbabilityMeasure P :=
    hE.isFilteredBrownianReal.1.toIsPreBrownianReal.isGaussianProcess.isProbabilityMeasure
  obtain ⟨G, hGm, hGc, hgood⟩ := exists_ncGood hκ hsep hpre hE
  set xL := wordXL pL with hxLdef
  set xR := wordXR pR with hxRdef
  set ρL' := wordRhoL ρL τm with hρL'
  set c₂ := ncC2 pL pR with hc₂def
  set c₁ := c₂ / 2 with hc₁def
  have hc₂ : 0 < c₂ := ncC2_pos hsep
  have hc₁ : 0 < c₁ := by positivity
  have hc : c₁ < c₂ := by linarith
  set BL := ∑ i, |ρL i| with hBLdef
  set BR := ∑ j, |ρR j| with hBRdef
  have hBL : ∑ i : Fin nL, |ρL' i.castSucc| ≤ BL := by simp only [hρL', wordRhoL_castSucc]; exact le_rfl
  have hpreL : ∀ j : Fin nL, κ / 2 - 2 ≤ ∑ i ∈ Finset.Iic j, ρL' i.castSucc := by
    simpa only [hρL', wordRhoL_castSucc] using hpre.1
  obtain ⟨lam, hlam0, hgen⟩ := exists_itoGen_ncLyap_nonpos (xL := xL) (xR := xR) (ρL := ρL') (ρR := ρR)
    hκ hc₁ hc hBL le_rfl hpreL hpre.2
  set β := ncBeta κ c₂ BL BR (ρL' (Fin.last nL)) with hβdef
  have hBL0 : 0 ≤ BL := Finset.sum_nonneg fun i _ => abs_nonneg _
  have hBR0 : 0 ≤ BR := Finset.sum_nonneg fun i _ => abs_nonneg _
  have hβ : 0 ≤ β := by
    simp only [hβdef, ncBeta]
    have : 0 ≤ BL * uOf c₂ := mul_nonneg hBL0 (uOf_pos hc₂).le
    have : 0 ≤ BR * wOf c₂ := mul_nonneg hBR0 (wOf_pos hc₂).le
    have := abs_nonneg (ρL' (Fin.last nL))
    positivity
  set Ψ := ncLyap κ xL xR ρL' ρR β c₁ c₂ lam with hΨ
  have h0 : xL (Fin.last nL) < 0 := by simp [hxLdef]
  have hxL : ∀ i : Fin nL, xL (Fin.last nL) < xL i.castSucc := fun i => by
    simp only [hxLdef, wordXL_last, wordXL_castSucc]; linarith [Real.exp_pos (pL i)]
  have hreg := stripInit_mem_ncRegion_word (κ := κ) (ρL := ρL) (ρR := ρR) (τm := τm) hsep
  have hΨ0 : 0 < Ψ (stripInit xL xR) :=
    mul_pos (Real.exp_pos _) ((Real.log_pos (by norm_num)).trans_le (log_two_le_ncObs hβ hreg))
  set Ψσ : ℕ → ℕ → Ω → ℝ := fun n m ω => Ψ (coordS xL xR G W VL VR (ncLoc G W VL VR B ζ n m ω) ω,
    Sec2.TwoSeed.brownG G B (ncLoc G W VL VR B ζ n m ω) ω) with hΨσ
  -- reduction to one horizon `N`
  rw [ae_iff]
  have hsub : {ω | ¬ ∀ N : ℕ, ∃ m : ℕ, ∀ s : ℝ≥0, IsStripLife (W · ω) (VL (Fin.last nL) · ω) (ζ ω) s →
      stripClock (extPath (W · ω)) (extPath (VL (Fin.last nL) · ω)) s ≤ N →
      0 ≤ mLevel m (Coupling.stateAt W VL VR s ω)} ⊆ Gᶜ ∪ ⋃ N : ℕ, {ω | ω ∈ G ∧ ∀ m : ℕ, ∃ s : ℝ≥0,
        IsStripLife (W · ω) (VL (Fin.last nL) · ω) (ζ ω) s ∧
        stripClock (extPath (W · ω)) (extPath (VL (Fin.last nL) · ω)) s ≤ N ∧
        mLevel m (Coupling.stateAt W VL VR s ω) < 0} := by
    intro ω hω
    by_cases hωG : ω ∈ G
    · right
      simp only [mem_ofPred_eq, not_forall, not_exists] at hω
      obtain ⟨N, hN⟩ := hω
      refine mem_iUnion.2 ⟨N, hωG, fun m => ?_⟩
      obtain ⟨s, h1, h2, h3⟩ := hN m
      exact ⟨s, h1, h2, not_le.1 h3⟩
    · left; exact hωG
  refine measure_mono_null hsub (measure_union_null hGc (measure_iUnion_null fun N => ?_))
  -- fixed horizon `N`: the bound for one level `m`
  have hbound : ∀ m : ℕ, 1 / ((m : ℝ) + 1) ≤ c₁ → 1 ≤ m →
      P {ω | ω ∈ G ∧ ∀ m : ℕ, ∃ s : ℝ≥0, IsStripLife (W · ω) (VL (Fin.last nL) · ω) (ζ ω) s ∧
        stripClock (extPath (W · ω)) (extPath (VL (Fin.last nL) · ω)) s ≤ N ∧
        mLevel m (Coupling.stateAt W VL VR s ω) < 0} ≤
      ENNReal.ofReal (Ψ (stripInit xL xR) / (Real.exp (-(lam * N)) * Real.log ((m : ℝ) + 1))) := by
    intro m hm hm1
    set K := Real.exp (-(lam * N)) * Real.log ((m : ℝ) + 1) with hK
    have hKpos : 0 < K := mul_pos (Real.exp_pos _) (Real.log_pos (by
      have : (1 : ℝ) ≤ m := by exact_mod_cast hm1
      linarith))
    have hsub2 : {ω | ω ∈ G ∧ ∀ m : ℕ, ∃ s : ℝ≥0, IsStripLife (W · ω) (VL (Fin.last nL) · ω) (ζ ω) s ∧
        stripClock (extPath (W · ω)) (extPath (VL (Fin.last nL) · ω)) s ≤ N ∧
        mLevel m (Coupling.stateAt W VL VR s ω) < 0} ⊆
        ⋃ n₀ : ℕ, ⋂ n : ℕ, ⋂ (_ : n₀ ≤ n), {ω | K ≤ Ψσ n m ω} := by
      rintro ω ⟨hωG, hall⟩
      obtain ⟨s₁, hs₁, hT₁, hm₁⟩ := hall m
      obtain ⟨n₀, hn₀⟩ := exists_ncLoc_exit hgood hxL hωG hs₁ hm₁
      refine mem_iUnion.2 ⟨n₀, mem_iInter₂.2 fun n hn => ?_⟩
      obtain ⟨hσle, hσm⟩ := hn₀ n hn
      have hωg := hgood ω hωG
      have hF := hωg.1.isForcePath
      set σ := ncLoc G W VL VR B ζ n m ω with hσ
      have hlife := isStripLife_ncLoc hωg hωG h0 (n := n) (m := m)
      have hp := mem_ncKc_of_le_ncLoc hωg hωG hgood h0 (n := n) (m := m) (le_refl σ)
      have hreg' := ncKc_subset_region κ xL xR ρL' ρR hreg n m hp
      have hst : stateOf κ xL xR ρL' ρR (stripCoordAt (W · ω) (fun i t => VL i t ω)
          (fun j t => VR j t ω) σ, B σ ω) = Coupling.stateAt W VL VR σ ω :=
        Prod.ext (w_eq_driftLin hωg.1 hlife.1).symm rfl
      have hobs := log_le_ncObs_of_mLevel_nonpos hβ hc hm hreg' (by rw [hst]; exact hσm)
      have hT : stripClock (extPath (W · ω)) (extPath (VL (Fin.last nL) · ω)) σ ≤ N := by
        refine le_trans ?_ hT₁
        simp only [stripClock]
        refine intervalIntegral.integral_mono_interval le_rfl σ.coe_nonneg (by exact_mod_cast hσle)
          (Eventually.of_forall fun u => inv_nonneg.2 (sq_nonneg _)) ?_
        simpa [Strip.extPath] using intervalIntegrable_clockRate hF hs₁
      have hexp : Real.exp (-(lam * N)) ≤ Real.exp (-(lam * stripClock (extPath (W · ω))
          (extPath (VL (Fin.last nL) · ω)) σ)) :=
        Real.exp_le_exp.2 (neg_le_neg (mul_le_mul_of_nonneg_left hT hlam0))
      show K ≤ Ψσ n m ω
      simp only [hΨσ, coordS, Sec2.TwoSeed.brownG, hωG, ↓reduceIte]
      rw [← hσ]
      simp only [hΨ, ncLyap, stripCoordAt]
      exact mul_le_mul hexp hobs (Real.log_nonneg (by
        have : (0 : ℝ) ≤ m := by positivity
        linarith)) (Real.exp_pos _).le
    refine (measure_mono hsub2).trans ?_
    have hmono : Monotone (fun n₀ : ℕ => ⋂ n : ℕ, ⋂ (_ : n₀ ≤ n), {ω | K ≤ Ψσ n m ω}) :=
      fun a b hab => iInter₂_mono' fun n hn => ⟨n, hab.trans hn, subset_rfl⟩
    rw [hmono.measure_iUnion]
    refine iSup_le fun n₀ => ?_
    refine (measure_mono (iInter₂_subset n₀ (le_refl n₀))).trans ?_
    obtain ⟨hint, hle⟩ := integral_ncLyap_ncLoc_le (β := β) (c₁ := c₁) (lam := lam) hsep hE hGm hGc
      hgood hgen n₀ m
    have hnn : 0 ≤ᵐ[P] fun ω => Ψσ n₀ m ω := Eventually.of_forall fun ω => by
      have hpK : (coordS xL xR G W VL VR (ncLoc G W VL VR B ζ n₀ m ω) ω,
          Sec2.TwoSeed.brownG G B (ncLoc G W VL VR B ζ n₀ m ω) ω) ∈ ncKc κ xL xR ρL' ρR n₀ m := by
        by_cases hω : ω ∈ G
        · simpa only [coordS, Sec2.TwoSeed.brownG, hω, ↓reduceIte] using
            mem_ncKc_of_le_ncLoc (hgood ω hω) hω hgood h0 (n := n₀) (m := m) le_rfl
        · simp only [coordS, Sec2.TwoSeed.brownG, hω, ↓reduceIte]
          exact mem_insert _ _
      have hr := ncKc_subset_region κ xL xR ρL' ρR hreg n₀ m hpK
      exact mul_nonneg (Real.exp_pos _).le ((Real.log_nonneg (by norm_num)).trans
        (log_two_le_ncObs hβ hr))
    have hmk := mul_meas_ge_le_integral_of_nonneg hnn hint K
    have hreal : P.real {ω | K ≤ Ψσ n₀ m ω} ≤ Ψ (stripInit xL xR) / K := by
      rw [le_div_iff₀ hKpos]; linarith
    rw [← ofReal_measureReal (measure_ne_top P _)]
    exact ENNReal.ofReal_le_ofReal hreal
  -- letting `m → ∞`
  refine le_antisymm (ENNReal.le_of_forall_pos_le_add fun ε hε _ => ?_) bot_le
  rw [zero_add]
  set A := Ψ (stripInit xL xR) * Real.exp (lam * N) / ε with hA
  have hApos : 0 < A := by positivity
  obtain ⟨m, hm⟩ := exists_nat_ge (max (max 1 (1 / c₁)) (Real.exp A))
  have hm1 : (1 : ℝ) ≤ m := (le_max_left _ _).trans ((le_max_left _ _).trans hm)
  have hmc : 1 / ((m : ℝ) + 1) ≤ c₁ := by
    rw [div_le_iff₀ (by positivity)]
    have := (le_max_right _ _).trans ((le_max_left _ _).trans hm)
    rw [div_le_iff₀ hc₁] at this
    nlinarith
  have hmA : A ≤ Real.log ((m : ℝ) + 1) := by
    have := (le_max_right _ _).trans hm
    rw [← Real.log_exp A]
    exact Real.log_le_log (Real.exp_pos _) (by linarith)
  refine (hbound m hmc (by exact_mod_cast hm1)).trans ?_
  rw [← ENNReal.ofReal_coe_nnreal]
  refine ENNReal.ofReal_le_ofReal ?_
  have hlogpos : 0 < Real.log ((m : ℝ) + 1) := hApos.trans_le hmA
  rw [div_le_iff₀ (mul_pos (Real.exp_pos _) hlogpos)]
  have hεA : Ψ (stripInit xL xR) * Real.exp (lam * N) = A * ε := by
    simp only [hA]; field_simp
  have hexp : Real.exp (-(lam * N)) * Real.exp (lam * N) = 1 := by
    rw [← Real.exp_add]; simp
  have h1 : A * (ε : ℝ) ≤ Real.log ((m : ℝ) + 1) * ε := mul_le_mul_of_nonneg_right hmA ε.coe_nonneg
  calc Ψ (stripInit xL xR) = Ψ (stripInit xL xR) * Real.exp (lam * N) * Real.exp (-(lam * N)) := by
        rw [mul_assoc, mul_comm (Real.exp (lam * N)), hexp, mul_one]
    _ = A * ε * Real.exp (-(lam * N)) := by rw [hεA]
    _ ≤ Real.log ((m : ℝ) + 1) * ε * Real.exp (-(lam * N)) :=
        mul_le_mul_of_nonneg_right h1 (Real.exp_pos _).le
    _ = ε * (Real.exp (-(lam * N)) * Real.log ((m : ℝ) + 1)) := by ring

/-- **Noncollision on the strip life** (Astra L1103–L1169 for strip words): almost surely, at every time of the
strip life every lower left mark is strictly left of the driver and every right mark strictly right of it. -/
theorem ae_stripLife_noncollision (hκ : 0 < κ) (hsep : IsSeparatedStripWord pL pR)
    (hpre : HasStripPrefixSums κ ρL ρR) (hE : IsStripSLEEvolution κ pL pR ρL ρR τm P 𝓕 W VL VR B ζ) :
    ∀ᵐ ω ∂P, ∀ s : ℝ≥0, IsStripLife (W · ω) (VL (Fin.last nL) · ω) (ζ ω) s →
      (∀ i : Fin nL, VL i.castSucc s ω < W s ω) ∧ ∀ j : Fin nR, W s ω < VR j s ω := by
  filter_upwards [ae_strip_bounds hκ hsep hpre hE, hE.ae_isIntegratedSLEPath] with ω hbd hp s hs
  have hF := hp.isForcePath
  obtain ⟨N, hN⟩ := exists_nat_ge (stripClock (extPath (W · ω)) (extPath (VL (Fin.last nL) · ω)) s)
  obtain ⟨m, hm⟩ := hbd N
  obtain ⟨hG1, -, hX, hY⟩ := mLevel_nonneg_iff.1 (hm s hs hN)
  simp only [Coupling.stateAt] at hG1 hX hY
  have hGpos : 0 < W s ω - VL (Fin.last nL) s ω := (Real.exp_pos _).trans_le hG1
  have he1 : Real.exp (-(1 / ((m : ℝ) + 1))) < 1 :=
    Real.exp_lt_one_iff.2 (neg_lt_zero.2 (by positivity))
  refine ⟨fun i => ?_, fun j => ?_⟩
  · have hn : 0 < nL := Fin.pos i
    have h0 := hX hn
    have hle : VL i.castSucc s ω ≤ VL (Fin.castSucc ⟨0, hn⟩) s ω :=
      hF.antitone_vL hs.1 (Fin.castSucc_le_castSucc_iff.2 (Fin.le_def.2 (Nat.zero_le _)))
    nlinarith
  · have hn : 0 < nR := Fin.pos j
    have h0 := hY hn
    have hle : VR ⟨0, hn⟩ s ω ≤ VR j s ω := hF.monotone_vR hs.1 (Fin.le_def.2 (Nat.zero_le _))
    have hf : 0 < VR ⟨0, hn⟩ s ω - VL (Fin.last nL) s ω := by
      by_contra hneg; push Not at hneg
      have : Real.exp (-(1 / ((m : ℝ) + 1))) * (VR ⟨0, hn⟩ s ω - VL (Fin.last nL) s ω) ≤ 0 :=
        mul_nonpos_of_nonneg_of_nonpos (Real.exp_pos _).le hneg
      linarith
    nlinarith

/-- **The strip clock is unbounded on the strip life** (clause (1) of `Strip.HasStripEndpoint`; Astra (ii): "the strip
evolution is defined at every finite strip time"). For a strip evolution with `κ > 0`, separated lower marks and the
prefix sums of (3.3), almost surely `HasUnboundedStripClock` holds. -/
theorem ae_hasUnboundedStripClock (hκ : 0 < κ) (hsep : IsSeparatedStripWord pL pR)
    (hpre : HasStripPrefixSums κ ρL ρR) (hE : IsStripSLEEvolution κ pL pR ρL ρR τm P 𝓕 W VL VR B ζ) :
    ∀ᵐ ω ∂P, HasUnboundedStripClock (W · ω) (VL (Fin.last nL) · ω) (ζ ω) := by
  filter_upwards [ae_strip_bounds hκ hsep hpre hE, hE.ae_isIntegratedSLEPath,
    ae_endCollision hκ hsep hpre hE] with ω hbd hp hec
  intro T₀
  by_contra hcon
  push Not at hcon
  have hF := hp.isForcePath
  obtain ⟨N, hN⟩ := exists_nat_ge T₀
  obtain ⟨m, hm⟩ := hbd N
  have hall : ∀ s : ℝ≥0, IsStripLife (W · ω) (VL (Fin.last nL) · ω) (ζ ω) s →
      Real.exp (-((m : ℝ) + 1)) ≤ W s ω - VL (Fin.last nL) s ω ∧
        W s ω - VL (Fin.last nL) s ω ≤ Real.exp ((m : ℝ) + 1) := fun s hs => by
    obtain ⟨h1, h2, -, -⟩ := mLevel_nonneg_iff.1 (hm s hs ((hcon s hs).le.trans hN))
    exact ⟨h1, h2⟩
  set ε := Real.exp (-((m : ℝ) + 1)) with hε
  have hεpos : 0 < ε := Real.exp_pos _
  have hε1 : ε ≤ 1 := Real.exp_le_one_iff.2 (by linarith [(Nat.cast_nonneg m : (0 : ℝ) ≤ m)])
  set f : ℝ≥0 → ℝ := fun s => W s ω - VL (Fin.last nL) s ω with hf
  have hcont : ContinuousOn f {s : ℝ≥0 | (s : ℝ≥0∞) < ζ ω} := hF.continuousOn_w.sub (hF.continuousOn_vL _)
  have hf0 : f 0 = 1 := by
    simp only [hf, hF.w_zero, hF.vL_zero, wordXL_last]; ring
  -- `W − v ≥ ε` before the lifetime
  have hclaim : ∀ s : ℝ≥0, (s : ℝ≥0∞) < ζ ω → ε ≤ f s := by
    by_contra hc
    push Not at hc
    obtain ⟨s₀, hs₀ζ, hs₀⟩ := hc
    have hτle : Coupling.hitBelow f (ζ ω) ε ≤ s₀ := Coupling.hitBelow_le hs₀ζ hs₀
    obtain ⟨t, ht⟩ := WithTop.ne_top_iff_exists.1 (ne_top_of_le_ne_top WithTop.coe_ne_top hτle)
    have htζ : (t : ℝ≥0∞) < ζ ω := Coupling.lt_of_hitBelow_eq ht.symm
    have hbefore : ∀ r : ℝ≥0, r < t → ε ≤ f r := fun r hr => by
      by_contra h
      push Not at h
      have := Coupling.hitBelow_le (lt_trans (by exact_mod_cast hr) htζ) h
      rw [← ht] at this
      exact absurd (WithTop.coe_le_coe.1 this) (not_le.2 hr)
    have hft : ε ≤ f t := by
      rcases (zero_le (a := t)).eq_or_lt with h00 | ht0
      · rw [← h00, hf0]; exact hε1
      · have hat := hcont.continuousAt ((Coupling.isOpen_setOf_coe_lt (ζ ω)).mem_nhds htζ)
        have : (𝓝[<] t).NeBot := nhdsLT_neBot_of_exists_lt ⟨0, ht0⟩
        refine ge_of_tendsto (hat.tendsto.mono_left (nhdsWithin_le_nhds (s := Iio t))) ?_
        filter_upwards [self_mem_nhdsWithin] with r hr
        exact hbefore r hr
    -- a time just after `t` in the strip life with `W − v < ε`
    have hev1 : ∀ᶠ u : ℝ≥0 in 𝓝 t, (u : ℝ≥0∞) < ζ ω :=
      (Coupling.isOpen_setOf_coe_lt (ζ ω)).mem_nhds htζ
    have hev : ∀ᶠ u : ℝ≥0 in 𝓝 t, (u : ℝ≥0∞) < ζ ω ∧ 0 < f u :=
      hev1.and ((hcont.continuousAt ((Coupling.isOpen_setOf_coe_lt (ζ ω)).mem_nhds htζ)).eventually
          (lt_mem_nhds (hεpos.trans_le hft)))
    obtain ⟨δ, hδ, hball⟩ := Metric.eventually_nhds_iff.1 hev
    set ρ : ℝ≥0 := (δ / 2).toNNReal with hρ
    have hρpos : 0 < ρ := Real.toNNReal_pos.2 (by linarith)
    have hne := Coupling.nonempty_of_hitBelow_eq ht.symm
    have hinf := Coupling.sInf_eq_of_hitBelow_eq ht.symm
    obtain ⟨r, hrS, hrlt⟩ := exists_lt_of_csInf_lt hne (show sInf {s : ℝ≥0 | (s : ℝ≥0∞) < ζ ω ∧ f s < ε} <
      t + ρ by rw [hinf]; exact lt_add_of_pos_right t hρpos)
    have htr : t ≤ r := hinf ▸ csInf_le (OrderBot.bddBelow _) hrS
    have hclose : ∀ u ∈ Icc t r, (u : ℝ≥0∞) < ζ ω ∧ 0 < f u := fun u hu => hball (by
      rw [NNReal.dist_eq, abs_lt]
      have h1 : (t : ℝ) ≤ u := by exact_mod_cast hu.1
      have h2 : (u : ℝ) ≤ r := by exact_mod_cast hu.2
      have h3 : (r : ℝ) < t + ρ := by exact_mod_cast hrlt
      have h4 : (ρ : ℝ) = δ / 2 := Real.coe_toNNReal _ (by linarith)
      constructor <;> linarith)
    have hlife : IsStripLife (W · ω) (VL (Fin.last nL) · ω) (ζ ω) r := by
      refine ⟨hrS.1, fun u hu => ?_⟩
      rcases lt_or_ge u t with hut | htu
      · have := hbefore u hut; simp only [hf] at this; linarith
      · have := (hclose u ⟨htu, hu⟩).2; simp only [hf] at this; linarith
    have := (hall r hlife).1
    have h2 := hrS.2
    simp only [hf] at h2
    linarith
  by_cases hζ : ζ ω = ⊤
  · -- an infinite strip life with `W − v ≤ e^{m+1}` has an unbounded clock
    have hlife : ∀ s : ℝ≥0, IsStripLife (W · ω) (VL (Fin.last nL) · ω) (ζ ω) s := fun s => by
      refine ⟨by rw [hζ]; exact ENNReal.coe_lt_top, fun r _ => ?_⟩
      have := hclaim r (by rw [hζ]; exact ENNReal.coe_lt_top)
      simp only [hf] at this; linarith
    set c := (Real.exp ((m : ℝ) + 1) ^ 2)⁻¹ with hc
    have hcpos : 0 < c := by positivity
    set s : ℝ≥0 := (T₀ / c + 1).toNNReal with hs
    have hsr : (s : ℝ) = T₀ / c + 1 ∨ T₀ / c + 1 ≤ 0 := by
      rcases le_or_gt (T₀ / c + 1) 0 with h | h
      · right; exact h
      · left; exact Real.coe_toNNReal _ h.le
    have hint := intervalIntegrable_clockRate hF (hlife s)
    have hbound : (s : ℝ) * c ≤ stripClock (extPath (W · ω)) (extPath (VL (Fin.last nL) · ω)) s := by
      have := intervalIntegral.integral_mono_on s.coe_nonneg (intervalIntegrable_const (c := c)) hint
        fun u hu => by
          have hu1 : u.toNNReal ≤ s := Sec2.toNNReal_le_of_mem_Icc hu
          obtain ⟨h1, h2⟩ := hall _ ((hlife s).mono hu1)
          have hp : 0 < W u.toNNReal ω - VL (Fin.last nL) u.toNNReal ω := hεpos.trans_le h1
          exact inv_anti₀ (by positivity) (pow_le_pow_left₀ hp.le h2 2)
      simpa [stripClock, Strip.extPath, intervalIntegral.integral_const, mul_comm] using this
    have hlt := hcon s (hlife s)
    rcases hsr with h | h
    · have hsc : (s : ℝ) * c = T₀ + c := by rw [h]; field_simp
      linarith
    · have hT : T₀ ≤ -c := by
        have := (div_le_iff₀ hcpos).1 (by linarith : T₀ / c ≤ -1)
        linarith
      have h0 := hcon 0 (hlife 0)
      simp only [stripClock, NNReal.coe_zero, intervalIntegral.integral_same] at h0
      linarith
  · obtain ⟨s, hsζ, hs⟩ := hec hζ ε hεpos
    have := hclaim s hsζ
    simp only [hf] at this
    linarith

/-- **The strip driver is `√κ` times a Brownian motion in strip time** (PROVE-ZHAN-A2's `exists_stripBrownian`) for
every strip evolution with `κ > 0`, separated lower marks and the prefix sums of (3.3): its hypothesis, the unbounded
strip clock, is `ae_hasUnboundedStripClock`. -/
theorem exists_stripBrownian_of_prefixSums (hκ : 0 < κ) (hsep : IsSeparatedStripWord pL pR)
    (hpre : HasStripPrefixSums κ ρL ρR) (hE : IsStripSLEEvolution κ pL pR ρL ρR τm P 𝓕 W VL VR B ζ) :
    ∃ (𝓗 : Filtration ℝ≥0 mΩ) (B' : ℝ≥0 → Ω → ℝ), IsFilteredBrownianReal 𝓗 B' P ∧
      ∀ᵐ ω ∂P, ∀ t : ℝ≥0,
        IsStripLife (W · ω) (VL (Fin.last nL) · ω) (ζ ω) (chordT (W · ω) (VL (Fin.last nL) · ω) t) ∧
        stripDriver (extPath (W · ω)) (extPath (VL (Fin.last nL) · ω)) t =
          Real.sqrt κ * B' t ω
          - (∑ i : Fin nL, ρL i / 2 * (stripPoint (extPath (W · ω))
              (extPath (VL (Fin.last nL) · ω)) (extPath (VL i.castSucc · ω)) t - pL i))
          - (∑ j, ρR j / 2 * (stripPoint (extPath (W · ω))
              (extPath (VL (Fin.last nL) · ω)) (extPath (VR j · ω)) t - pR j))
          + (τm - tauPlus κ ρL ρR τm) / 2 * t :=
  exists_stripBrownian hκ hE (ae_hasUnboundedStripClock hκ hsep hpre hE)

end Main

end Zhan

end InteractingSLE
