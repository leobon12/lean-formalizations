/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.SB2VsLift

/-!
# The coordinate gauge along one sample (D19, step 4)

Packet PROVE-AUX61-NOJUMP (decision D19). Along one sample, the stop gauge in relative time is
`gco s = G̃ (Γ s)` before the relative lifetime `U` and `0` from `U` on, where `Γ` is the relative trace and `G̃` is
the gauge function (`gaugeExt`), bounded by the physical parts `Aph`, `Bph` at the physical point `gch z`.

* **`continuous_gco`** (deterministic): `gco` is continuous. Before `U` it is `G̃ ∘ Γ`. At a finite `U` its left
  limit is `0`, read through physical times: a relative time `s < U` is the clock `a t` of a physical time
  `t ∈ [t_L, Z)`, at which `gch (Γ s) = η' t`, and `η' t` tends to the closed bad set `F` (a finite lifetime: the flow
  ends on `F`) or to infinity (an infinite lifetime: transience).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology Metric
open scoped NNReal ENNReal

namespace InteractingSLE.Theorem14.SB.Vs

/-- **The coordinate gauge**: the gauge function at the relative trace before `U`, `0` from `U` on. -/
def gco (G : ℂ → ℝ≥0∞) (Γ : ℝ≥0 → ℂ) (U : ℝ≥0∞) (s : ℝ≥0) : ℝ :=
  if (s : ℝ≥0∞) < U then (G (Γ s)).toReal else 0

theorem gco_of_lt {G : ℂ → ℝ≥0∞} {Γ : ℝ≥0 → ℂ} {U : ℝ≥0∞} {s : ℝ≥0} (hs : (s : ℝ≥0∞) < U) :
    gco G Γ U s = (G (Γ s)).toReal := by simp [gco, hs]

theorem gco_of_le {G : ℂ → ℝ≥0∞} {Γ : ℝ≥0 → ℂ} {U : ℝ≥0∞} {s : ℝ≥0} (hs : U ≤ (s : ℝ≥0∞)) :
    gco G Γ U s = 0 := by simp [gco, not_lt.2 hs]

section Det

variable {G : ℂ → ℝ≥0∞} {Γ : ℝ≥0 → ℂ} {U : ℝ≥0∞} {gch : ℂ → ℂ} {F : Set ℂ} {a : ℝ≥0 → ℝ≥0∞} {tL : ℝ≥0}
  {Z : ℝ≥0∞} {η' : ℝ≥0 → ℂ}

/-- The left limit of the coordinate gauge at a finite relative lifetime is `0`. -/
theorem tendsto_gco_nhdsLT (hG1 : ∀ z, G z ≤ 1) (hGA : ∀ z, G z ≤ Aph F (gch z)) (hGB : ∀ z, G z ≤ Bph (gch z))
    (ham : Monotone a) (htZ : (tL : ℝ≥0∞) < Z)
    (hread : ∀ t : ℝ≥0, tL ≤ t → (t : ℝ≥0∞) < Z → a t < U ∧ gch (Γ (a t).toNNReal) = η' t)
    (hsurj : ∀ s : ℝ≥0, (s : ℝ≥0∞) < U → ∃ t : ℝ≥0, tL ≤ t ∧ (t : ℝ≥0∞) < Z ∧ a t = s)
    (hη' : ContinuousOn η' {t | (t : ℝ≥0∞) ≤ Z}) (hend : ∀ T : ℝ≥0, (T : ℝ≥0∞) = Z → η' T ∈ F)
    (htr : Z = ⊤ → Tendsto (fun t => ‖η' t‖) atTop atTop) (hU : U ≠ ⊤) :
    Tendsto (gco G Γ U) (𝓝[<] U.toNNReal) (𝓝 0) := by
  have hnn : ∀ s, 0 ≤ gco G Γ U s := fun s => by
    unfold gco; split_ifs
    · exact ENNReal.toReal_nonneg
    · exact le_rfl
  refine tendsto_order.2 ⟨fun c hc => Eventually.of_forall fun s => lt_of_lt_of_le hc (hnn s), fun ε hε => ?_⟩
  -- a physical time after which the physical bound is below `ε`
  have hphys : ∃ t₀ : ℝ≥0, tL ≤ t₀ ∧ (t₀ : ℝ≥0∞) < Z ∧ ∀ t : ℝ≥0, t₀ ≤ t → (t : ℝ≥0∞) < Z →
      min (Aph F (η' t)) (Bph (η' t)) < ENNReal.ofReal ε := by
    by_cases hZ : Z = ⊤
    · have h := (htr hZ).eventually (eventually_gt_atTop (1 / ε))
      obtain ⟨t₁, ht₁⟩ := eventually_atTop.1 h
      refine ⟨max tL t₁, le_max_left _ _, by rw [hZ]; exact ENNReal.coe_lt_top, fun t ht _ => ?_⟩
      refine lt_of_le_of_lt (min_le_right _ _) ?_
      have hn := ht₁ t ((le_max_right _ _).trans ht)
      have hpos : 0 < 1 + ‖η' t‖ := by positivity
      unfold Bph
      rw [ENNReal.ofReal_lt_ofReal_iff hε, div_lt_iff₀ hpos]
      rw [div_lt_iff₀ hε] at hn
      nlinarith [norm_nonneg (η' t)]
    · obtain ⟨T, hT⟩ : ∃ T : ℝ≥0, (T : ℝ≥0∞) = Z := ⟨Z.toNNReal, ENNReal.coe_toNNReal hZ⟩
      have hLT : tL < T := by rw [← hT] at htZ; exact_mod_cast htZ
      have hA0 : Aph F (η' T) = 0 := by
        unfold Aph; rw [infEDist_zero_of_mem (hend T hT)]; exact min_eq_left zero_le
      have hcw : ContinuousWithinAt (fun t => Aph F (η' t)) {t | (t : ℝ≥0∞) ≤ Z} T :=
        (continuous_Aph F).continuousAt.comp_continuousWithinAt (hη' T (le_of_eq hT))
      have hev : ∀ᶠ t in 𝓝[{t | (t : ℝ≥0∞) ≤ Z}] T, Aph F (η' t) < ENNReal.ofReal ε :=
        hcw.eventually (gt_mem_nhds (by show Aph F (η' T) < _; rw [hA0]; exact ENNReal.ofReal_pos.2 hε))
      obtain ⟨δ, hδ, hball⟩ := Metric.mem_nhdsWithin_iff.1 hev
      set t₀ : ℝ≥0 := max tL (T - (δ / 2).toNNReal) with ht₀
      have ht₀T : t₀ < T := max_lt hLT (tsub_lt_self (lt_of_le_of_lt zero_le hLT)
        (Real.toNNReal_pos.2 (half_pos hδ)))
      refine ⟨t₀, le_max_left _ _, by rw [← hT]; exact_mod_cast ht₀T, fun t ht htZ' => ?_⟩
      have htT : t < T := by rw [← hT] at htZ'; exact_mod_cast htZ'
      refine lt_of_le_of_lt (min_le_left _ _) (hball ⟨?_, by rw [← hT]; exact_mod_cast htT.le⟩)
      rw [mem_ball, NNReal.dist_eq]
      have h1 : ((T - (δ / 2).toNNReal : ℝ≥0) : ℝ) ≤ t := by exact_mod_cast (le_max_right _ _).trans ht
      have h2 : (T : ℝ) - δ / 2 ≤ ((T - (δ / 2).toNNReal : ℝ≥0) : ℝ) := by
        rw [NNReal.coe_sub_def]
        refine le_trans ?_ (le_max_left _ _)
        rw [Real.coe_toNNReal _ (by positivity)]
      have h3 : (t : ℝ) < T := by exact_mod_cast htT
      rw [abs_lt]; constructor <;> linarith
  obtain ⟨t₀, ht₀L, ht₀Z, ht₀⟩ := hphys
  have ha₀ : a t₀ < U := (hread t₀ ht₀L ht₀Z).1
  have hU' : (U.toNNReal : ℝ≥0∞) = U := ENNReal.coe_toNNReal hU
  have hs₀ : (a t₀).toNNReal < U.toNNReal := by
    rw [← ENNReal.coe_lt_coe, ENNReal.coe_toNNReal (ne_top_of_lt ha₀), hU']; exact ha₀
  filter_upwards [Ioo_mem_nhdsLT hs₀] with s hs
  have hsU : (s : ℝ≥0∞) < U := by rw [← hU']; exact_mod_cast hs.2
  obtain ⟨t, htL, htZ', hts⟩ := hsurj s hsU
  have htt₀ : t₀ ≤ t := by
    by_contra hlt
    rw [not_le] at hlt
    have h1 := ham hlt.le
    rw [hts] at h1
    have h2 : (s : ℝ≥0∞) > a t₀ := by
      rw [← ENNReal.coe_toNNReal (ne_top_of_lt ha₀)]; exact_mod_cast hs.1
    exact absurd h1 (not_le.2 h2)
  rw [gco_of_lt hsU]
  have hgch : gch (Γ s) = η' t := by
    have := (hread t htL htZ').2
    rw [hts, ENNReal.toNNReal_coe] at this
    exact this
  have hbound : G (Γ s) < ENNReal.ofReal ε :=
    lt_of_le_of_lt (le_min (hGA _) (hGB _)) (by rw [hgch]; exact ht₀ t htt₀ htZ')
  have hfin : G (Γ s) ≠ ⊤ := ne_top_of_le_ne_top ENNReal.one_ne_top (hG1 _)
  rw [← ENNReal.ofReal_toReal hfin] at hbound
  exact (ENNReal.ofReal_lt_ofReal_iff hε).1 hbound

/-- **The coordinate gauge is continuous.** -/
theorem continuous_gco (hGc : ContinuousOn G {z | 0 ≤ z.im}) (hG1 : ∀ z, G z ≤ 1)
    (hGA : ∀ z, G z ≤ Aph F (gch z)) (hGB : ∀ z, G z ≤ Bph (gch z))
    (hΓc : ContinuousOn Γ {s | (s : ℝ≥0∞) < U}) (hΓH : ∀ s : ℝ≥0, (s : ℝ≥0∞) < U → 0 ≤ (Γ s).im)
    (ham : Monotone a) (htZ : (tL : ℝ≥0∞) < Z)
    (hread : ∀ t : ℝ≥0, tL ≤ t → (t : ℝ≥0∞) < Z → a t < U ∧ gch (Γ (a t).toNNReal) = η' t)
    (hsurj : ∀ s : ℝ≥0, (s : ℝ≥0∞) < U → ∃ t : ℝ≥0, tL ≤ t ∧ (t : ℝ≥0∞) < Z ∧ a t = s)
    (hη' : ContinuousOn η' {t | (t : ℝ≥0∞) ≤ Z}) (hend : ∀ T : ℝ≥0, (T : ℝ≥0∞) = Z → η' T ∈ F)
    (htr : Z = ⊤ → Tendsto (fun t => ‖η' t‖) atTop atTop) : Continuous (gco G Γ U) := by
  have hopen : IsOpen {s : ℝ≥0 | (s : ℝ≥0∞) < U} := isOpen_lt ENNReal.continuous_coe continuous_const
  rw [continuous_iff_continuousAt]
  intro s
  rcases lt_or_ge (s : ℝ≥0∞) U with hs | hs
  · -- before the lifetime
    have hcG : ContinuousAt (fun s => (G (Γ s)).toReal) s := by
      have h1 : ContinuousWithinAt G {z | 0 ≤ z.im} (Γ s) := hGc _ (hΓH s hs)
      have h2 : ContinuousAt Γ s := (hΓc s hs).continuousAt (hopen.mem_nhds hs)
      have h3 : ContinuousAt (fun s => G (Γ s)) s := by
        refine h1.tendsto.comp (tendsto_nhdsWithin_iff.2 ⟨h2, ?_⟩)
        filter_upwards [hopen.mem_nhds hs] with s' hs' using hΓH s' hs'
      exact (ENNReal.continuousAt_toReal (ne_top_of_le_ne_top ENNReal.one_ne_top (hG1 (Γ s)))).comp
        (f := fun s => G (Γ s)) h3
    refine hcG.congr ?_
    filter_upwards [hopen.mem_nhds hs] with s' hs'
    rw [gco_of_lt hs']
  · have hU : U ≠ ⊤ := ne_top_of_le_ne_top ENNReal.coe_ne_top hs
    rcases eq_or_lt_of_le hs with he | hlt
    · -- at the lifetime: the left limit is `0`, and it is `0` from there on
      have hsU : s = U.toNNReal := by rw [he, ENNReal.toNNReal_coe]
      refine continuousAt_iff_continuous_left_right.2 ⟨?_, ?_⟩
      · have h := tendsto_gco_nhdsLT hG1 hGA hGB ham htZ hread hsurj hη' hend htr hU
        rw [← hsU] at h
        refine continuousWithinAt_Iio_iff_Iic.1 ?_
        show Tendsto (gco G Γ U) (𝓝[<] s) (𝓝 (gco G Γ U s))
        rw [gco_of_le hs]
        exact h
      · rw [ContinuousWithinAt, gco_of_le hs]
        refine tendsto_const_nhds.congr' ?_
        filter_upwards [self_mem_nhdsWithin] with x hx
        exact (gco_of_le (hs.trans (ENNReal.coe_le_coe.2 hx))).symm
    · -- after the lifetime it is constant
      have hopen' : IsOpen {s : ℝ≥0 | U < (s : ℝ≥0∞)} := isOpen_lt continuous_const ENNReal.continuous_coe
      refine (continuousAt_const (y := (0 : ℝ))).congr ?_
      filter_upwards [hopen'.mem_nhds hlt] with s' hs'
      rw [gco_of_le hs'.le]

end Det

end InteractingSLE.Theorem14.SB.Vs
