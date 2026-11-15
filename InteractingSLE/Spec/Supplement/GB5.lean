/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GB5Loc
import InteractingSLE.Spec.Supplement.S8Range
import InteractingSLE.Spec.Sec2.Assembly2Pathwise
import InteractingSLE.Spec.Sec4.RepulsionNoncollision

/-!
# Lemma GB5 (general protected-tail estimate)

Packet PROVE-T14-GB. Specification supplement §8.5, **Lemma GB5** (`source/spec/p481-528.md` L874–L922, pp. 516–518):

> Let `k > 0`, `c = k/2 − 2`, and let a one-sided integrated force evolution have right coordinates
> `0 ≤ V₁(0) ≤ ⋯ ≤ V_N(0)`, with the first coordinate allowed to be a seed and coincident labels interpreted as one
> merged group. Write `S_i = Σ_{ℓ ≤ i} ρ_ℓ`. Suppose, for some `j ≥ 2`, that `S_i > −2` (`1 ≤ i < j`),
> `S_i ≥ c` (`j ≤ i ≤ N`). Assume `V₁(0) < V_j(0)`. Then `X_j = V_j − W` never vanishes at a finite time. […] Inner
> admissible mergers are permitted […]. An additional finite group on the opposite side does not change the
> finite-time conclusion, up to the original continuation threshold.

`gb5`: for an integrated `SLE_k(ρ)` evolution (frozen `IsIntegratedSLEEvolution`) of an ordered force word with any
finite left group, a right label `j` with the displayed partial-sum conditions and `x_{R,0} < x_{R,j}`: almost surely
`W_t < V^j_t` at every `t < ζ`. Lean labels start at `0`; the conditions are imposed at the group ends (labels `i`
with `x_i < x_{i'}` for every later label `i'`), which is the source's "compress initially coincident groups before
imposing the displayed conditions"; the original labels are retained in the integrated equations. (`j ≥ 2` in the
source's numbering follows from `V₁(0) < V_j(0)`.) `gb5_left` is the reflected assertion.

## Proof

The source's two random-clock cases are replaced by the Lyapunov function `F = −log X_j + αZ + λZ^p` of
`GB5Lyap.lean`, whose Itô drift is nonpositive up to the drift of the opposite group, which is integrable on the
localized intervals (`GB5Path.lean`). If `X_j` vanishes first at `t* < ζ`, then on `[0, t*]` the marks and `B`
stay in a box, the opposite group is localized (`W − V^{L,0} > 0` at `t*`, `Sec2.vL_lt_vR_of_pos`; `X_j > 0`
before), `d = V^j − V^{i₀} > 0` before `t*` (`gap_pos_of_forall_pos`: `d' = −2d/(X_{i₀} X_j)`), and `t*` is below
an announcing time `T_n < ζ`. So `X_j` reaches every level `ε` first (`gbEvent`), and the Lyapunov estimate
`measureReal_gbEvent_le` bounds the probability of this by `C/log(C'/ε) → 0`.
-/

set_option autoImplicit false

noncomputable section

open Set Filter MeasureTheory ProbabilityTheory Topology Finset
open scoped NNReal ENNReal

namespace InteractingSLE

namespace Supp8

namespace GB5

variable {nL nR : ℕ}

/-! ### `V^j − V^{i₀}` stays positive while `X_j` does -/

section Gap

variable {k : ℝ} {xL : Fin nL → ℝ} {xR : Fin nR → ℝ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ}
  {w : ℝ≥0 → ℝ} {vL : Fin nL → ℝ≥0 → ℝ} {vR : Fin nR → ℝ≥0 → ℝ} {b : ℝ≥0 → ℝ} {ζ : ℝ≥0∞}

/-- **`d = V^j − V^{i₀}` stays positive while `X_j` does** (the source's `d log(V_j − V₁) = −(2/U₁) du`): if
`x_{i₀} < x_j` and `W < V^j` on `[0, t]`, `t < ζ`, then `V^{i₀} < V^j` on `[0, t]`. -/
theorem gap_pos_of_forall_pos (hP : IsIntegratedSLEPath k xL xR ρL ρR w vL vR b ζ) {i₀ j : Fin nR}
    (hxd : xR i₀ < xR j) {t : ℝ≥0} (ht : (t : ℝ≥0∞) < ζ) (hpos : ∀ s ≤ t, w s < vR j s) :
    ∀ s ≤ t, vR i₀ s < vR j s := by
  have hF := hP.isForcePath
  set f : ℝ → ℝ := fun r => vR j r.toNNReal - vR i₀ r.toNNReal with hf
  set g0 : ℝ → ℝ := fun r => (vR i₀ r.toNNReal - w r.toNNReal)⁻¹ with hg0
  set gj : ℝ → ℝ := fun r => (vR j r.toNNReal - w r.toNNReal)⁻¹ with hgj
  set a : ℝ → ℝ := fun r => -2 * (g0 r * gj r) with ha
  have hmem : ∀ r ∈ Icc (0 : ℝ) t, (r.toNNReal : ℝ≥0∞) < ζ := fun r hr =>
    lt_of_le_of_lt (by exact_mod_cast Real.toNNReal_le_iff_le_coe.2 hr.2) ht
  have hrt : ∀ r ∈ Icc (0 : ℝ) t, r.toNNReal ≤ t := fun r hr => Real.toNNReal_le_iff_le_coe.2 hr.2
  have hcont : ∀ i, ContinuousOn (fun r : ℝ => vR i r.toNNReal) (Icc 0 t) := fun i =>
    Ito.continuousOn_rpath (hF.continuousOn_vR i) ht
  have hwc : ContinuousOn (fun r : ℝ => w r.toNNReal) (Icc 0 t) := Ito.continuousOn_rpath hF.continuousOn_w ht
  have hfc : ContinuousOn f (Icc 0 t) := (hcont j).sub (hcont i₀)
  have hgjc : ContinuousOn gj (Icc 0 t) :=
    ((hcont j).sub hwc).inv₀ fun r hr => (sub_pos.2 (hpos _ (hrt r hr))).ne'
  have hg0i : IntegrableOn g0 (Icc 0 t) := by
    have h := intervalIntegrable_inv_gapR' hP ht i₀
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le t.coe_nonneg] at h
    exact (integrableOn_Icc_iff_integrableOn_Ioc (by finiteness)).2 h
  have hai : IntegrableOn a (Icc 0 t) := (hg0i.mul_continuousOn hgjc isCompact_Icc).const_mul (-2)
  have ha0 : ∀ r ∈ Icc (0 : ℝ) t, a r ≤ 0 := fun r hr => by
    have h1 : 0 ≤ g0 r := inv_nonneg.2 (sub_nonneg.2 (hF.w_le_vR (hmem r hr) i₀))
    have h2 : 0 ≤ gj r := inv_nonneg.2 (sub_nonneg.2 (hF.w_le_vR (hmem r hr) j))
    simp only [ha]; nlinarith [mul_nonneg h1 h2]
  have heq : ∀ r ∈ Icc (0 : ℝ) t, f r = f 0 + ∫ u in (0 : ℝ)..r, a u * f u := by
    intro r hr
    have hrζ := hmem r hr
    have hj := hF.vR_eq hrζ j
    have hi := hF.vR_eq hrζ i₀
    have hr' : ((r.toNNReal : ℝ≥0) : ℝ) = r := Real.coe_toNNReal r hr.1
    rw [hr'] at hj hi
    have hf0 : f 0 = xR j - xR i₀ := by
      simp only [hf, Real.toNNReal_zero, hF.vR_zero]
    have hIj := (intervalIntegrable_two_div_gapR hP hrζ j)
    have hIi := (intervalIntegrable_two_div_gapR hP hrζ i₀)
    rw [hr'] at hIj hIi
    have hcongr : ∫ u in (0 : ℝ)..r, a u * f u =
        ∫ u in (0 : ℝ)..r, (2 / (vR j u.toNNReal - w u.toNNReal) - 2 / (vR i₀ u.toNNReal - w u.toNNReal)) := by
      refine intervalIntegral.integral_congr_ae ?_
      filter_upwards [ae_noncollision hP] with u hu huI
      rw [uIoc_of_le hr.1] at huI
      have huζ : (u.toNNReal : ℝ≥0∞) < ζ := hmem u ⟨huI.1.le, huI.2.trans hr.2⟩
      have hne0 : vR i₀ u.toNNReal - w u.toNNReal ≠ 0 :=
        sub_ne_zero.2 fun h => (hu huI.1.le huζ).2 i₀ h.symm
      have hnej : vR j u.toNNReal - w u.toNNReal ≠ 0 :=
        (sub_pos.2 (hpos _ (hrt u ⟨huI.1.le, huI.2.trans hr.2⟩))).ne'
      simp only [ha, hf, hg0, hgj]
      field_simp
      ring
    rw [hcongr, intervalIntegral.integral_sub hIj hIi, hf0]
    simp only [hf]
    linarith
  have hf0 : 0 < f 0 := by simp only [hf, Real.toNNReal_zero, hF.vR_zero]; linarith
  intro s hs
  have := pos_of_eq_add_integral_mul hfc hai ha0 heq hf0 s ⟨s.coe_nonneg, by exact_mod_cast hs⟩
  simpa only [hf, Real.toNNReal_coe, sub_pos] using this

end Gap

/-! ### The bad events of fixed parameters are null -/

section Null

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ} {k : ℝ}
  {xL : Fin nL → ℝ} {xR : Fin nR → ℝ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ}
  {G : Set Ω} {W : ℝ≥0 → Ω → ℝ} {VL : Fin nL → ℝ≥0 → Ω → ℝ} {VR : Fin nR → ℝ≥0 → Ω → ℝ}
  {B : ℝ≥0 → Ω → ℝ} {ζ : Ω → ℝ≥0∞} {T : ℕ → Ω → ℝ≥0} {j : Fin nR}

/-- **For fixed `n`, `γ`, `γ'`, the event "for every level `ε = 1/(m+2)` the gap `X_j` reaches `ε` first, for some
`R`" is null**: its probability is at most `P(⋃_R gbEvent_R) = sup_R P(gbEvent_R) ≤ C/log(C'(m+2)) → 0`. -/
theorem measure_iInter_iUnion_gbEvent (hE : IsIntegratedSLEEvolution k xL xR ρL ρR P 𝓕 W VL VR B ζ)
    (hGm : MeasurableSet G) (hGc : P Gᶜ = 0) (hgood : ∀ ω ∈ G, IsGBGood k xL xR ρL ρR W VL VR B ζ T ω)
    (hT : ∀ n, IsStoppingTime (usualAugmentation 𝓕 P) fun ω => (T n ω : WithTop ℝ≥0))
    (hTn : ∀ n ω, T n ω ≤ n) (hk : 0 < k) {εH : ℝ} (hεH : 0 < εH) (hnR : 0 < nR) (hxm : Monotone xR)
    (hin : ∀ i : Fin nR, i < j → (∀ i', i < i' → xR i < xR i') →
      εH ≤ ∑ l ∈ univ.filter (fun l => l ≤ i), ρR l + 2)
    (hout : ∀ i : Fin nR, j ≤ i → (∀ i', i < i' → xR i < xR i') →
      k / 2 - 2 ≤ ∑ l ∈ univ.filter (fun l => l ≤ i), ρR l)
    (hx0 : 0 ≤ xR ⟨0, hnR⟩) (hxd : xR ⟨0, hnR⟩ < xR j) (n : ℕ) {γ γ' : ℝ} (hγ : 0 < γ) (hγ' : 0 < γ') :
    P (⋂ m : ℕ, ⋃ R : ℕ, gbEvent G W VL VR B ζ T j ⟨0, hnR⟩ n R γ γ' (1 / ((m : ℝ) + 2))) = 0 := by
  have hP : IsProbabilityMeasure P := hE.1.isProbabilityMeasure'
  set Cx := gbCx xR j n with hCx
  set K := lyapObs k εH (initPt xR j ⟨0, hnR⟩) + Real.log Cx + gbCst k εH γ γ' xL xR ρL j n with hK
  set bnd : ℕ → ℝ := fun m => K / Real.log (Cx / (1 / ((m : ℝ) + 2))) with hbnd
  have hCx1 : 1 ≤ Cx := by
    simp only [hCx, gbCx]; have := abs_nonneg (xR j); have : (0 : ℝ) ≤ n := Nat.cast_nonneg n; linarith
  have hεm : ∀ m : ℕ, 1 / ((m : ℝ) + 2) < Cx := fun m => by
    have : 1 / ((m : ℝ) + 2) < 1 := by rw [div_lt_one (by positivity)]; linarith [(Nat.cast_nonneg m : (0 : ℝ) ≤ m)]
    linarith
  have hle : ∀ m : ℕ, P (⋂ m : ℕ, ⋃ R : ℕ, gbEvent G W VL VR B ζ T j ⟨0, hnR⟩ n R γ γ'
      (1 / ((m : ℝ) + 2))) ≤ ENNReal.ofReal (bnd m) := by
    intro m
    refine (measure_mono (iInter_subset _ m)).trans ?_
    rw [Monotone.measure_iUnion (fun R R' hRR' => gbEvent_mono hRR')]
    refine iSup_le fun R => ?_
    rw [← ofReal_measureReal (measure_ne_top P _)]
    exact ENNReal.ofReal_le_ofReal (measureReal_gbEvent_le hE hGm hGc hgood hT hTn hk hεH hnR hxm hin hout
      hx0 hxd hγ hγ' (by positivity) (hεm m))
  have hlim : Tendsto bnd atTop (𝓝 0) := by
    have h1 : Tendsto (fun m : ℕ => Cx / (1 / ((m : ℝ) + 2))) atTop atTop := by
      have : (fun m : ℕ => Cx / (1 / ((m : ℝ) + 2))) = fun m : ℕ => Cx * ((m : ℝ) + 2) := by
        funext m; rw [div_div_eq_mul_div, div_one]
      rw [this]
      exact Tendsto.const_mul_atTop (by linarith) (tendsto_atTop_add_const_right _ 2
        tendsto_natCast_atTop_atTop)
    exact tendsto_const_nhds.div_atTop (Real.tendsto_log_atTop.comp h1)
  have hlim' : Tendsto (fun m => ENNReal.ofReal (bnd m)) atTop (𝓝 0) := by
    have := (ENNReal.continuous_ofReal.tendsto 0).comp hlim
    rwa [ENNReal.ofReal_zero] at this
  exact le_antisymm (ge_of_tendsto' hlim' hle) bot_le

end Null

/-! ### A first zero of `X_j` is covered by the bad events -/

section Cover

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {k : ℝ}
  {xL : Fin nL → ℝ} {xR : Fin nR → ℝ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ}
  {G : Set Ω} {W : ℝ≥0 → Ω → ℝ} {VL : Fin nL → ℝ≥0 → Ω → ℝ} {VR : Fin nR → ℝ≥0 → Ω → ℝ}
  {B : ℝ≥0 → Ω → ℝ} {ζ : Ω → ℝ≥0∞} {T : ℕ → Ω → ℝ≥0} {j : Fin nR}

/-- **The pathwise covering.** On a good path with a zero of `X_j` before `ζ`, there are `n`, `γ = 1/(a+1)`,
`γ' = 1/(b+1)` such that for every level `ε = 1/(m+2)` some `R` makes the path a member of `gbEvent`. -/
theorem exists_mem_gbEvent (hgood : ∀ ω ∈ G, IsGBGood k xL xR ρL ρR W VL VR B ζ T ω)
    (hTm : ∀ ω, Monotone fun n => T n ω) (hF : IsOrderedForceWord xL xR) (hnR : 0 < nR)
    (hxd : xR ⟨0, hnR⟩ < xR j) {ω : Ω} (hω : ω ∈ G) {t : ℝ≥0} (ht : (t : ℝ≥0∞) < ζ ω)
    (hcol : VR j t ω ≤ W t ω) :
    ∃ n a b : ℕ, ∀ m : ℕ, ∃ R : ℕ, ω ∈ gbEvent G W VL VR B ζ T j ⟨0, hnR⟩ n R (1 / ((a : ℝ) + 1))
      (1 / ((b : ℝ) + 1)) (1 / ((m : ℝ) + 2)) := by
  set i₀ : Fin nR := ⟨0, hnR⟩ with hi₀
  have hgω := hgood ω hω
  have hP := hgω.1
  have hFp := hP.isForcePath
  have hx0 : 0 ≤ xR i₀ := hF.2.2.2 i₀
  set x : ℝ≥0 → ℝ := fun s => VR j s ω - W s ω with hxdef
  have hxc : ContinuousOn x {s : ℝ≥0 | (s : ℝ≥0∞) < ζ ω} := (hFp.continuousOn_vR j).sub hFp.continuousOn_w
  have hsub : ∀ {u : ℝ≥0}, (u : ℝ≥0∞) < ζ ω → Icc 0 u ⊆ {s : ℝ≥0 | (s : ℝ≥0∞) < ζ ω} :=
    fun hu s hs => lt_of_le_of_lt (by exact_mod_cast hs.2) hu
  -- the first zero `t*`
  set Z := Icc 0 t ∩ x ⁻¹' Iic 0 with hZ
  have hZc : IsClosed Z := (hxc.mono (hsub ht)).preimage_isClosed_of_isClosed isClosed_Icc isClosed_Iic
  have hZne : Z.Nonempty := ⟨t, ⟨zero_le, le_rfl⟩, show x t ≤ 0 by simp only [hxdef]; linarith⟩
  set ts := sInf Z with hts
  have htsZ : ts ∈ Z := hZc.csInf_mem hZne (OrderBot.bddBelow _)
  have htst : ts ≤ t := htsZ.1.2
  have htsζ : (ts : ℝ≥0∞) < ζ ω := lt_of_le_of_lt (by exact_mod_cast htst) ht
  have hxts : x ts ≤ 0 := htsZ.2
  have hbefore : ∀ s < ts, 0 < x s := fun s hs => by
    by_contra hneg
    push Not at hneg
    exact absurd (csInf_le (OrderBot.bddBelow _) (show s ∈ Z from ⟨⟨zero_le, hs.le.trans htst⟩, hneg⟩))
      (not_le.2 hs)
  have hx0' : x 0 = xR j := by simp only [hxdef, hFp.vR_zero, hFp.w_zero, sub_zero]
  have hts0 : 0 < ts := by
    rcases (zero_le (a := ts)).eq_or_lt with h | h
    · rw [← h, hx0'] at hxts; linarith
    · exact h
  -- `n`: the box, the Brownian bound and the announcing time
  obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn
    ((continuousOn_stateAt_gb hgood hω).mono (hsub htsζ) : ContinuousOn
      (fun s => Coupling.stateAt W VL VR s ω) (Icc 0 ts))
  obtain ⟨CB, hCB⟩ := isCompact_Icc.exists_bound_of_continuousOn
    (hgω.2.1.continuousOn : ContinuousOn (B · ω) (Icc 0 ts))
  obtain ⟨N₁, hN₁⟩ := hgω.2.2.2.2 ts htsζ
  set n := max N₁ (⌈max C CB⌉₊ + 1) with hn
  have hnC : max C CB < n := by
    have h1 : max C CB ≤ ⌈max C CB⌉₊ := Nat.le_ceil _
    have h2 : ((⌈max C CB⌉₊ + 1 : ℕ) : ℝ) ≤ n := by exact_mod_cast le_max_right _ _
    push_cast at h2
    linarith
  have hTts : ts ≤ T n ω := hN₁.trans (hTm ω (le_max_left _ _))
  -- `γ`, `γ'`: the opposite group on `[0, t*]`
  have hleft : ∃ a b : ℕ, ∀ s ≤ ts, ∀ h : 0 < nL,
      1 / ((a : ℝ) + 1) ≤ W s ω - VL ⟨0, h⟩ s ω ∨ 1 / ((b : ℝ) + 1) ≤ x s := by
    rcases Nat.eq_zero_or_pos nL with hnL | hnL
    · exact ⟨0, 0, fun s _ h => absurd h (by omega)⟩
    set l : ℝ≥0 → ℝ := fun s => W s ω - VL ⟨0, hnL⟩ s ω with hl
    have hlc : ContinuousOn l {s : ℝ≥0 | (s : ℝ≥0∞) < ζ ω} := hFp.continuousOn_w.sub (hFp.continuousOn_vL _)
    have hgs : 0 < l ts := by
      have h1 := hP.vL_lt_vR_of_pos hF hts0 htsζ ⟨0, hnL⟩ i₀
      have h2 : VR i₀ ts ω ≤ VR j ts ω := hFp.monotone_vR htsζ (Nat.zero_le _ : i₀ ≤ j)
      simp only [hl]; simp only [hxdef] at hxts; linarith
    have hev := (hlc.continuousAt ((Coupling.isOpen_setOf_coe_lt (ζ ω)).mem_nhds htsζ)).eventually
      (lt_mem_nhds (half_lt_self hgs))
    obtain ⟨δ, hδ, hδl⟩ := Metric.eventually_nhds_iff.1 hev
    set u : ℝ≥0 := ((ts : ℝ) - δ / 2).toNNReal with hu
    have hut : u < ts := by
      rw [← NNReal.coe_lt_coe, hu, Real.coe_toNNReal']
      exact max_lt (by linarith) (by exact_mod_cast hts0)
    have hxu : ∀ s ∈ Icc 0 u, 0 < x s := fun s hs => hbefore s (lt_of_le_of_lt hs.2 hut)
    obtain ⟨s₁, hs₁, hmin⟩ := isCompact_Icc.exists_isMinOn (nonempty_Icc.2 (zero_le (a := u)))
      ((hxc.mono (hsub (lt_of_le_of_lt (by exact_mod_cast hut.le) htsζ))))
    obtain ⟨a, ha⟩ := exists_nat_one_div_lt (half_pos hgs)
    obtain ⟨b, hb⟩ := exists_nat_one_div_lt (hxu s₁ hs₁)
    refine ⟨a, b, fun s hs h => ?_⟩
    have hh : (⟨0, h⟩ : Fin nL) = ⟨0, hnL⟩ := rfl
    rw [hh]
    by_cases hsu : s ≤ u
    · exact Or.inr (hb.le.trans (hmin ⟨zero_le, hsu⟩))
    · push Not at hsu
      left
      have hsu' : (ts : ℝ) - δ / 2 < s := by
        have h1 : (u : ℝ) < s := by exact_mod_cast hsu
        have h2 : (ts : ℝ) - δ / 2 ≤ u := by rw [hu, Real.coe_toNNReal']; exact le_max_left _ _
        linarith
      have hd : dist s ts < δ := by
        have hst : (s : ℝ) ≤ ts := by exact_mod_cast hs
        rw [NNReal.dist_eq, abs_of_nonpos (by linarith)]
        linarith
      exact ha.le.trans (hδl hd).le
  obtain ⟨a, b, hab⟩ := hleft
  refine ⟨n, a, b, fun m => ?_⟩
  set ε : ℝ := 1 / ((m : ℝ) + 2) with hε
  have hε0 : 0 < ε := by positivity
  -- a time `s₀ < t*` with `X_j(s₀) < ε`
  obtain ⟨s₀, hs₀x, hs₀t⟩ : ∃ s₀, x s₀ < ε ∧ s₀ < ts := by
    have hev := (hxc.continuousAt ((Coupling.isOpen_setOf_coe_lt (ζ ω)).mem_nhds htsζ)).eventually
      (gt_mem_nhds (lt_of_le_of_lt hxts hε0))
    have : (𝓝[<] ts).NeBot := nhdsLT_neBot_of_exists_lt ⟨0, hts0⟩
    have h1 : ∀ᶠ s in 𝓝[<] ts, x s < ε := eventually_nhdsWithin_of_eventually_nhds hev
    have h2 : ∀ᶠ s in 𝓝[<] ts, s < ts := eventually_nhdsWithin_of_forall fun s hs => hs
    obtain ⟨s₀, h3, h4⟩ := (h1.and h2).exists
    exact ⟨s₀, h3, h4⟩
  have hs₀ζ : (s₀ : ℝ≥0∞) < ζ ω := lt_of_le_of_lt (by exact_mod_cast hs₀t.le) htsζ
  -- `d > 0` on `[0, s₀]`, hence `≥ 1/(R+1)`
  have hdpos := gap_pos_of_forall_pos hP hxd hs₀ζ (fun s hs => sub_pos.1 (hbefore s (lt_of_le_of_lt hs hs₀t)))
  obtain ⟨s₂, hs₂, hmin₂⟩ := isCompact_Icc.exists_isMinOn (nonempty_Icc.2 (zero_le (a := s₀)))
    (((hFp.continuousOn_vR j).sub (hFp.continuousOn_vR i₀)).mono (hsub hs₀ζ))
  obtain ⟨R, hR⟩ := exists_nat_one_div_lt (sub_pos.2 (hdpos s₂ hs₂.2))
  refine ⟨R, hω, ?_⟩
  have hX : hitX G W VL VR ζ j ε ω ≤ s₀ := by
    simp only [hitX, hω, ↓reduceIte]
    exact Coupling.hitBelow_le hs₀ζ (by simp only [levX, xFun, Coupling.stateAt]; linarith)
  refine hX.trans (le_min (le_min ?_ ?_) ?_)
  · -- the outer constraints hold on `[0, s₀]`
    simp only [hitO, hω, ↓reduceIte]
    refine Coupling.le_hitBelow fun s hsζ hneg => ?_
    by_contra hlt
    push Not at hlt
    have hst : s ≤ ts := (hlt.le.trans hs₀t.le)
    refine absurd hneg (not_lt.2 ?_)
    simp only [levO, le_min_iff]
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · have := (hC s ⟨zero_le, hst⟩).trans (le_max_left C CB)
      linarith
    · have h' : VR j s₂ ω - VR i₀ s₂ ω ≤ VR j s ω - VR i₀ s ω :=
        hmin₂ (show s ∈ Icc 0 s₀ from ⟨zero_le, hlt.le⟩)
      simp only [dFun, Coupling.stateAt]
      linarith
    · simp only [leftFun]
      split_ifs with h
      · rcases hab s hst h with h1 | h1
        · exact le_max_of_le_left (by simp only [Coupling.stateAt]; linarith)
        · exact le_max_of_le_right (by simp only [xFun, Coupling.stateAt]; simp only [hxdef] at h1; linarith)
      · norm_num
  · -- the Brownian motion stays in `(−n, n)` up to `t*`
    by_contra hlt
    push Not at hlt
    obtain ⟨u', hu'⟩ := WithTop.ne_top_iff_exists.1 (ne_top_of_lt hlt)
    rw [← hu'] at hlt
    have hu's : u' < s₀ := WithTop.coe_lt_coe.1 hlt
    obtain ⟨s, hs, hsB⟩ := (MathFin.exitTime_le_iff (continuous_brownG_gb hgood) n u' ω).1 hu'.symm.le
    have hst : s ≤ ts := hs.2.trans (hu's.le.trans hs₀t.le)
    have hb := (hCB s ⟨zero_le, hst⟩).trans (le_max_right C CB)
    simp only [Sec2.TwoSeed.brownG, hω, ↓reduceIte, Real.norm_eq_abs] at hsB hb
    linarith
  · exact_mod_cast hs₀t.le.trans hTts

end Cover

/-! ### Lemma GB5 -/

section Main

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ} {k : ℝ}
  {xL : Fin nL → ℝ} {xR : Fin nR → ℝ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ}
  {W : ℝ≥0 → Ω → ℝ} {VL : Fin nL → ℝ≥0 → Ω → ℝ} {VR : Fin nR → ℝ≥0 → Ω → ℝ}
  {B : ℝ≥0 → Ω → ℝ} {ζ : Ω → ℝ≥0∞}

/-- A positive margin `ε ≤ S_i + 2` for the finitely many inner group ends. -/
theorem exists_inner_margin {j : Fin nR}
    (hin : ∀ i : Fin nR, i < j → (∀ i', i < i' → xR i < xR i') →
      -2 < ∑ l ∈ univ.filter (fun l => l ≤ i), ρR l) :
    ∃ εH : ℝ, 0 < εH ∧ ∀ i : Fin nR, i < j → (∀ i', i < i' → xR i < xR i') →
      εH ≤ ∑ l ∈ univ.filter (fun l => l ≤ i), ρR l + 2 := by
  classical
  set S := (univ : Finset (Fin nR)).image (fun i => if i < j ∧ ∀ i', i < i' → xR i < xR i' then
    ∑ l ∈ univ.filter (fun l => l ≤ i), ρR l + 2 else 1) with hS
  have hne : S.Nonempty := ⟨_, mem_image_of_mem _ (mem_univ j)⟩
  refine ⟨S.min' hne, ?_, fun i hi hend => ?_⟩
  · obtain ⟨i, -, hi⟩ := mem_image.1 (S.min'_mem hne)
    rw [← hi]
    split_ifs with h
    · linarith [hin i h.1 h.2]
    · norm_num
  · have := S.min'_le _ (mem_image_of_mem _ (mem_univ i))
    exact le_trans this (le_of_eq (ite_eq_left_of_eq_true _ _ (eq_true ⟨hi, hend⟩)))

/-- **Lemma GB5** (general protected-tail estimate; specification supplement §8.5, p. 516). Let `k > 0`,
`c = k/2 − 2`, and let `(W, V, B)` be an integrated `SLE_k(ρ)` evolution of an ordered force word (`0 ≤ x_{R,0} ≤ ⋯`;
any finite group on the opposite side). Suppose that for a right label `j` the partial sums
`S_i = Σ_{ℓ ≤ i} ρ_{R,ℓ}` satisfy, at the group ends `i` (`x_{R,i} < x_{R,i'}` for all `i' > i`), `S_i > −2` for
`i < j` and `S_i ≥ c` for `i ≥ j`, and `x_{R,0} < x_{R,j}`. Then almost surely `X_j = V^j − W` does not vanish at any
time before the lifetime: `W_t < V^j_t` for all `t < ζ`. -/
theorem gb5 (hk : 0 < k) (hF : IsOrderedForceWord xL xR) (j : Fin nR)
    (hin : ∀ i : Fin nR, i < j → (∀ i', i < i' → xR i < xR i') →
      -2 < ∑ l ∈ univ.filter (fun l => l ≤ i), ρR l)
    (hout : ∀ i : Fin nR, j ≤ i → (∀ i', i < i' → xR i < xR i') →
      k / 2 - 2 ≤ ∑ l ∈ univ.filter (fun l => l ≤ i), ρR l)
    (hxd : xR ⟨0, Fin.pos j⟩ < xR j) (hE : IsIntegratedSLEEvolution k xL xR ρL ρR P 𝓕 W VL VR B ζ) :
    ∀ᵐ ω ∂P, ∀ t : ℝ≥0, (t : ℝ≥0∞) < ζ ω → W t ω < VR j t ω := by
  have hP : IsProbabilityMeasure P := hE.1.isProbabilityMeasure'
  have hnR : 0 < nR := Fin.pos j
  -- an inadmissible seed has lifetime `0`
  by_cases hseed : ForceWord.ThresholdCondition ρL ρR 0 xL xR
  · filter_upwards [hE.2.2.2.2] with ω hp t ht
    exfalso
    have hFp := hp.isForcePath
    have h0 : ((0 : ℝ≥0) : ℝ≥0∞) < ζ ω := lt_of_le_of_lt bot_le ht
    have := hFp.not_threshold h0
    have hw : W 0 ω = 0 := hFp.w_zero
    have hL : (fun i => VL i 0 ω) = xL := funext hFp.vL_zero
    have hR : (fun i => VR i 0 ω) = xR := funext hFp.vR_zero
    simp only [hw, hL, hR] at this
    exact this hseed
  -- the announcing sequence and the good event
  obtain ⟨T, hTann, hTn⟩ := Coupling.exists_isAnnouncingSeq_le hE hk hseed
  obtain ⟨hT, hTm, hTζ, hTcov⟩ := hTann
  have hae : ∀ᵐ ω ∂P, IsGBGood k xL xR ρL ρR W VL VR B ζ T ω := by
    filter_upwards [hE.2.2.2.2, hE.1.1.cont, hE.1.1.eval_zero_ae_eq_zero, ae_all_iff.2 hTζ, hTcov]
      with ω h1 h2 h3 h4 h5
    exact ⟨h1, h2, h3, h4, h5⟩
  obtain ⟨G, hGm, hGc, hgood⟩ : ∃ G : Set Ω, MeasurableSet G ∧ P Gᶜ = 0 ∧
      ∀ ω ∈ G, IsGBGood k xL xR ρL ρR W VL VR B ζ T ω := by
    refine ⟨(toMeasurable P {ω | ¬ IsGBGood k xL xR ρL ρR W VL VR B ζ T ω})ᶜ,
      (measurableSet_toMeasurable _ _).compl, ?_, fun ω hω => ?_⟩
    · rw [compl_compl, measure_toMeasurable]; exact ae_iff.1 hae
    · by_contra h; exact hω (subset_toMeasurable _ _ h)
  obtain ⟨εH, hεH, hinε⟩ := exists_inner_margin hin
  have hx0 : 0 ≤ xR ⟨0, hnR⟩ := hF.2.2.2 _
  -- the null events of fixed parameters
  have hnull : ∀ n a b : ℕ, P (⋂ m : ℕ, ⋃ R : ℕ, gbEvent G W VL VR B ζ T j ⟨0, hnR⟩ n R
      (1 / ((a : ℝ) + 1)) (1 / ((b : ℝ) + 1)) (1 / ((m : ℝ) + 2))) = 0 := fun n a b =>
    measure_iInter_iUnion_gbEvent hE hGm hGc hgood hT hTn hk hεH hnR hF.2.2.1 hinε hout hx0 hxd n
      (by positivity) (by positivity)
  have hGae : ∀ᵐ ω ∂P, ω ∈ G := by rw [ae_iff]; exact hGc
  have hnot : ∀ᵐ ω ∂P, ∀ n a b : ℕ, ω ∉ ⋂ m : ℕ, ⋃ R : ℕ, gbEvent G W VL VR B ζ T j ⟨0, hnR⟩ n R
      (1 / ((a : ℝ) + 1)) (1 / ((b : ℝ) + 1)) (1 / ((m : ℝ) + 2)) := by
    simp only [ae_all_iff]
    exact fun n a b => measure_eq_zero_iff_ae_notMem.1 (hnull n a b)
  filter_upwards [hGae, hnot] with ω hω hω' t ht
  by_contra hcol
  push Not at hcol
  obtain ⟨n, a, b, hm⟩ := exists_mem_gbEvent hgood hTm hF hnR hxd hω ht hcol
  exact hω' n a b (mem_iInter.2 fun m => mem_iUnion.2 (hm m))

/-- **Lemma GB5, reflected** ("Reflection gives the left-sided assertion"): for a left label `j` with left partial
sums `S_i = Σ_{ℓ ≤ i} ρ_{L,ℓ}` (labels outward from the seed) `> −2` for `i < j` and `≥ c` for `i ≥ j` at the group
ends (`x_{L,i'} < x_{L,i}` for all `i' > i`), and
`x_{L,j} < x_{L,0}`: almost surely `V^{L,j}_t < W_t` for all `t < ζ`. By the reflection `x ↦ −x`
(`IsIntegratedSLEEvolution.reflect`). -/
theorem gb5_left (hk : 0 < k) (hF : IsOrderedForceWord xL xR) (j : Fin nL)
    (hin : ∀ i : Fin nL, i < j → (∀ i', i < i' → xL i' < xL i) →
      -2 < ∑ l ∈ univ.filter (fun l => l ≤ i), ρL l)
    (hout : ∀ i : Fin nL, j ≤ i → (∀ i', i < i' → xL i' < xL i) →
      k / 2 - 2 ≤ ∑ l ∈ univ.filter (fun l => l ≤ i), ρL l)
    (hxd : xL j < xL ⟨0, Fin.pos j⟩) (hE : IsIntegratedSLEEvolution k xL xR ρL ρR P 𝓕 W VL VR B ζ) :
    ∀ᵐ ω ∂P, ∀ t : ℝ≥0, (t : ℝ≥0∞) < ζ ω → VL j t ω < W t ω := by
  have hF' : IsOrderedForceWord (-xR) (-xL) :=
    ⟨hF.2.2.1.neg, fun i => by simp [hF.2.2.2 i], hF.1.neg, fun i => by simp [hF.2.1 i]⟩
  have h := gb5 hk hF' j (fun i hi hend => hin i hi fun i' hii' => by simpa using hend i' hii')
    (fun i hi hend => hout i hi fun i' hii' => by simpa using hend i' hii') (by simpa using hxd) hE.reflect
  filter_upwards [h] with ω hω t ht
  have := hω t ht
  simp only [Pi.neg_apply, neg_lt_neg_iff] at this
  exact this

end Main

end GB5

end Supp8

end InteractingSLE
