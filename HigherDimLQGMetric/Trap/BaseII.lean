import HigherDimLQGMetric.Trap.BaseStep

/-!
# (ii) for the base configuration at one index ([S] Lemma 4.2, MA1 A17)

Packet S3. See `Trap/BaseStep.lean` for the outline. `trap_base_ii` turns a minimizer of
`(w_N·ζ)` between collector points into a collapse candidate of S1c (`CollapseGeodesicCandidate`)
and transfers the marked shortcut back to the minimizer.
-/

set_option autoImplicit false

noncomputable section

open Set Filter Topology BoundedContinuousFunction
open scoped ENNReal

namespace HigherDimLQGMetric

open LQGMetric.MetricGeometry

/-- `ofReal a * ofReal d ≤ W` with `W` finite gives `d ≤ W.toReal / a`. -/
theorem trap_le_div_of_ofReal_mul_le {a d : ℝ} {W : ℝ≥0∞} (ha : 0 < a)
    (hW : W ≠ ⊤) (h : ENNReal.ofReal a * ENNReal.ofReal d ≤ W) : d ≤ W.toReal / a := by
  rw [← ENNReal.ofReal_mul ha.le] at h
  have h' := (ENNReal.ofReal_le_iff_le_toReal hW).1 h
  rw [le_div_iff₀ ha]
  linarith

/-- **(ii) for the base configuration at one index.** If every `Y′`-confined collapse candidate
at index `N` (threshold `b/4`, horizon `T`) has a marked shortcut, then every `(w_N·ζ)`-minimizer
between points of `closure V` at distance `≥ b/2` has a subcurve of weighted length
`≥ λ_N a₁/2` and a shortcut of ratio `≤ ĉ` inside `Y′ = trapSet A V a_col`. -/
theorem trap_base_ii {Z : Type*} [MetricSpace Z]
    {A V K : Set Z} (hA : IsOpen A) (hV : IsOpen V) (hVA : closure V ⊆ A)
    (hKc : IsCompact K) (hKne : K.Nonempty)
    {acol b ε₀ a₀ : ℝ} (ha₀ : 0 < a₀)
    (hcol : ∀ x ∈ closure V, ∀ y ∈ frontier A, 4 * acol ≤ dist x y)
    (hb : 0 < b) (hε₀ : 0 < ε₀) (hε₀b : ε₀ < a₀ * b / 200) (hε₀col : ε₀ < acol / 12)
    {lam eta : ℕ → ℝ} {w : ℕ → Z → ℝ} {N : ℕ} (hlamN : 0 < lam N)
    (hwc : Continuous (w N)) (hwlo : ∀ p, lam N ≤ w N p)
    (hwoff : ∀ p, eta N ≤ Metric.infDist p K → a₀ ≤ w N p) (hwV : ∀ p, p ∉ V → w N p = 1)
    {T : ℝ}
    (hLT : ∀ x ∈ trapSet A V acol, ∀ y ∈ trapSet A V acol,
      Metric.infDist x K ≤ eta N → Metric.infDist y K ≤ eta N →
      ((ENNReal.ofReal (lam N))⁻¹ * weylDistOn (w N) (trapSet A V acol) x y).toReal ≤ T)
    (hi : ∀ x ∈ closure V, ∀ y ∈ closure V,
      weylDistOn (w N) univ x y < ENNReal.ofReal (3 * ε₀))
    (E : Z → Z → ℝ≥0∞) {a₁ ĉ : ℝ}
    (hshort : ∀ C : CollapseGeodesicCandidate (trapSet A V acol) K lam eta w T (b / 4) N,
      HasMarkedShortcut E a₁ ĉ C) :
    ∀ Q : ℝ → Z, ContinuousOn Q (Icc 0 1) → Q 0 ∈ closure V → Q 1 ∈ closure V →
      weightedLength (w N) Q 0 1 = weylDistOn (w N) univ (Q 0) (Q 1) →
      b / 2 ≤ dist (Q 0) (Q 1) →
      ∃ u v, 0 ≤ u ∧ u ≤ v ∧ v ≤ 1 ∧
        ENNReal.ofReal (lam N * (a₁ / 2)) ≤ weightedLength (w N) Q u v ∧
        ∃ S : ℝ → Z, ContinuousOn S (Icc 0 1) ∧ S 0 = Q u ∧ S 1 = Q v ∧
          MapsTo S (Icc 0 1) (trapSet A V acol) ∧
          weightedLengthWith E (w N) S 0 1 ≤ ENNReal.ofReal ĉ * weightedLength (w N) Q u v := by
  intro Q hQc hQ0 hQ1 hmin hsep
  set Y := trapSet A V acol with hY
  set W := weightedLength (w N) Q 0 1 with hW
  have hacol : 0 < acol := by linarith
  have hW3 : W < ENNReal.ofReal (3 * ε₀) := by
    rw [hmin]
    exact hi _ hQ0 _ hQ1
  have hWfin : W ≠ ⊤ := ne_top_of_lt hW3
  have hWr : W.toReal < 3 * ε₀ := by
    have := (ENNReal.toReal_lt_toReal hWfin ENNReal.ofReal_ne_top).2 hW3
    rwa [ENNReal.toReal_ofReal (by positivity)] at this
  -- confinement (C)
  have hQY : MapsTo Q (Icc 0 1) Y := by
    have hcol3 : ∀ x ∈ closure V, ∀ y ∈ frontier A, 3 * ε₀ ≤ dist x y :=
      fun x hx y hy => le_trans (by linarith) (hcol x hx y hy)
    exact (trap_mapsTo_trapSet hA hV hVA hwV hcol3 hQc hQ0 hW3).mono_right
      (trapSet_mono (by linarith))
  -- the closed `η_N`-tube is hit
  set g : ℝ → ℝ := fun τ => Metric.infDist (Q τ) K with hg_def
  have hgc : ContinuousOn g (Icc 0 1) :=
    (Metric.continuous_infDist_pt K).comp_continuousOn hQc
  set S : Set ℝ := Icc (0 : ℝ) 1 ∩ g ⁻¹' Iic (eta N) with hS_def
  have hSc : IsClosed S := hgc.preimage_isClosed_of_isClosed isClosed_Icc isClosed_Iic
  have hSne : S.Nonempty := by
    by_contra hSe
    have hfar : ∀ τ ∈ Icc (0 : ℝ) 1, eta N < g τ := by
      intro τ hτ
      by_contra h
      push Not at h
      exact hSe ⟨τ, hτ, h⟩
    have hw : ∀ τ ∈ Icc (0 : ℝ) 1, a₀ ≤ w N (Q τ) := fun τ hτ => hwoff _ (hfar τ hτ).le
    have h1 := ofReal_mul_curveLength_le_weightedLength (w := w N) (P := Q) zero_le_one hw
    have h2 := edist_le_curveLength Q (zero_le_one : (0 : ℝ) ≤ 1)
    have h3 : ENNReal.ofReal (a₀ * (b / 2)) ≤ W := by
      calc ENNReal.ofReal (a₀ * (b / 2)) = ENNReal.ofReal a₀ * ENNReal.ofReal (b / 2) :=
            ENNReal.ofReal_mul ha₀.le
        _ ≤ ENNReal.ofReal a₀ * edist (Q 0) (Q 1) := by
            gcongr
            rw [edist_dist]
            exact ENNReal.ofReal_le_ofReal hsep
        _ ≤ ENNReal.ofReal a₀ * curveLength Q 0 1 := mul_le_mul' le_rfl h2
        _ ≤ W := h1
    have h4 : ENNReal.ofReal (3 * ε₀) < ENNReal.ofReal (a₀ * (b / 2)) :=
      (ENNReal.ofReal_lt_ofReal_iff (by positivity)).2 (by nlinarith)
    exact absurd (h3.trans_lt hW3) (not_lt.2 h4.le)
  have hSbdd : BddBelow S := ⟨0, fun x hx => hx.1.1⟩
  have hSbdd' : BddAbove S := ⟨1, fun x hx => hx.1.2⟩
  set t₁ := sInf S with ht₁_def
  set t₂ := sSup S with ht₂_def
  have ht₁S : t₁ ∈ S := hSc.csInf_mem hSne hSbdd
  have ht₂S : t₂ ∈ S := hSc.csSup_mem hSne hSbdd'
  have ht₁₂ : t₁ ≤ t₂ := csInf_le hSbdd ht₂S
  have hbefore : ∀ τ ∈ Ico 0 t₁, eta N < Metric.infDist (Q τ) K := by
    intro τ hτ
    by_contra h
    push Not at h
    have : t₁ ≤ τ := csInf_le hSbdd ⟨⟨hτ.1, hτ.2.le.trans ht₁S.1.2⟩, h⟩
    exact absurd hτ.2 (not_lt.2 this)
  have hafter : ∀ τ ∈ Ioc t₂ 1, eta N < Metric.infDist (Q τ) K := by
    intro τ hτ
    by_contra h
    push Not at h
    have : τ ≤ t₂ := le_csSup hSbdd' ⟨⟨ht₂S.1.1.trans hτ.1.le, hτ.2⟩, h⟩
    exact absurd hτ.1 (not_lt.2 this)
  -- prefix and suffix are short
  have hpre := trap_prefix_bound hwoff hQc ht₁S.1 hbefore
  have hsuf := trap_suffix_bound hwoff hQc ht₂S.1 hafter
  rw [edist_dist] at hpre hsuf
  have hd1 := trap_le_div_of_ofReal_mul_le ha₀ hWfin hpre
  have hd2 := trap_le_div_of_ofReal_mul_le ha₀ hWfin hsuf
  have hWa : W.toReal / a₀ < 3 * b / 200 := by
    rw [div_lt_iff₀ ha₀]
    nlinarith
  have hsep' : b / 4 ≤ dist (Q t₁) (Q t₂) := by
    have htri1 := dist_triangle (Q 0) (Q t₁) (Q 1)
    have htri2 := dist_triangle (Q t₁) (Q t₂) (Q 1)
    linarith
  -- the middle segment is a `Y`-confined geodesic
  have hmid := trap_middle_minimal hQc hQY hmin hWfin ht₁S.1.1 ht₁₂ ht₂S.1.2
  have hmidfin : weightedLength (w N) Q t₁ t₂ ≠ ⊤ :=
    ne_top_of_le_ne_top hWfin (weightedLength_mono_interval ht₁S.1.1 ht₁₂ ht₂S.1.2)
  have hsub : Icc t₁ t₂ ⊆ Icc 0 1 := Icc_subset_Icc ht₁S.1.1 ht₂S.1.2
  obtain ⟨P', hP'c, hP'0, hP'L, hP'S, hP'param, hP'corr⟩ :=
    trap_exists_weighted_param (w := w N) (Q := Q) ht₁₂ (hQc.mono hsub) hwc.continuousOn
      (fun t _ => hlamN.trans_le (hwlo _)) hlamN hmidfin
  set L' := (weightedLength (w N) Q t₁ t₂).toReal / lam N with hL'_def
  have hL'0 : 0 ≤ L' := div_nonneg ENNReal.toReal_nonneg hlamN.le
  have hLdef : L' = ((ENNReal.ofReal (lam N))⁻¹ * weylDistOn (w N) Y (Q t₁) (Q t₂)).toReal := by
    rw [← hmid, ENNReal.toReal_mul, ENNReal.toReal_inv, ENNReal.toReal_ofReal hlamN.le,
      hL'_def, div_eq_inv_mul]
  have hx'Y : Q t₁ ∈ Y := hQY ht₁S.1
  have hy'Y : Q t₂ ∈ Y := hQY ht₂S.1
  have hLT' : L' ≤ T := by
    rw [hLdef]
    exact hLT _ hx'Y _ hy'Y ht₁S.2 ht₂S.2
  -- nearest points of the graph
  obtain ⟨u', hu'K, hu'⟩ := hKc.exists_infDist_eq_dist hKne (Q t₁)
  obtain ⟨v', hv'K, hv'⟩ := hKc.exists_infDist_eq_dist hKne (Q t₂)
  have hxu : dist (Q t₁) u' ≤ eta N := by
    rw [← hu']
    exact ht₁S.2
  have hyv : dist (Q t₂) v' ≤ eta N := by
    rw [← hv']
    exact ht₂S.2
  -- the candidate, constant after `L'`
  set P : ℝ → Z := fun τ => P' (min τ L') with hP_def
  have hPeq : ∀ τ, τ ≤ L' → P τ = P' τ := fun τ hτ => by simp only [hP_def, min_eq_left hτ]
  have hPc : ContinuousOn P (Icc 0 T) := by
    refine hP'c.comp (continuous_id.min continuous_const).continuousOn ?_
    intro τ hτ
    exact ⟨le_min hτ.1 hL'0, min_le_right _ _⟩
  have hPY : MapsTo P (Icc 0 T) Y := by
    intro τ hτ
    obtain ⟨r, hr, hrQ⟩ := hP'S (⟨le_min hτ.1 hL'0, min_le_right _ _⟩ : min τ L' ∈ Icc 0 L')
    show P' (min τ L') ∈ Y
    rw [← hrQ]
    exact hQY (hsub hr)
  have hP0 : P 0 = Q t₁ := by rw [hPeq 0 hL'0, hP'0]
  have hPL : P L' = Q t₂ := by rw [hPeq L' le_rfl, hP'L]
  have hparam : ∀ s t, 0 ≤ s → s ≤ t → t ≤ L' →
      weightedLength (w N) P s t = ENNReal.ofReal (lam N * (t - s)) := by
    intro s t hs hst htL
    rw [weightedLength_congr (Q := P') (fun τ hτ => hPeq τ (hτ.2.trans htL))]
    exact hP'param s t hs hst htL
  have hconst : ∀ t, L' ≤ t → t ≤ T → P t = P L' := by
    intro t ht _
    simp only [hP_def, min_eq_right ht, min_self]
  have hsc := hshort
    { x := Q t₁, y := Q t₂, u := u', v := v', hx := hx'Y, hy := hy'Y, hu := hu'K, hv := hv'K,
      hxu := hxu, hyv := hyv, hsep := hsep', L := L', hLdef := hLdef, P := P, hPc := hPc,
      hPY := hPY, hP0 := hP0, hPL := hPL, hLT := hLT', hparam := hparam, hconst := hconst }
  obtain ⟨s, t, hs, hst, htL, hcost, Sh, hShc, hSh0, hSh1, hShY, hShbound⟩ := hsc
  dsimp only at htL hcost hSh0 hSh1 hShbound
  have hwlPP' : weightedLength (w N) P s t = weightedLength (w N) P' s t :=
    weightedLength_congr (fun τ hτ => hPeq τ (hτ.2.trans htL))
  obtain ⟨u, v, hu, huv, hv, hP's, hP't, hwlQ⟩ := hP'corr s t hs hst htL
  refine ⟨u, v, ht₁S.1.1.trans hu, huv, hv.trans ht₂S.1.2, ?_, Sh, hShc, ?_, ?_, hShY, ?_⟩
  · rw [hwlQ, ← hwlPP']
    exact hcost
  · rw [hSh0, hPeq s (hst.trans htL), hP's]
  · rw [hSh1, hPeq t htL, hP't]
  · rw [hwlQ, ← hwlPP']
    exact hShbound

end HigherDimLQGMetric
