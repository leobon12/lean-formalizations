/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Foundations.OrientationWinding
import InteractingSLE.Spec.Sec4.SpecialSimple

/-!
# Lemma S2: two winding-number tools

Packet PROVE-T14-SB4. Two facts about the winding numbers `Orientation.windNum` of loops on `[0, 1]`, used in the
proof of Lemma S2 (supplement p. 578, (S2.2) and "Thus these left-collar points have nonzero winding around a closed
walk in `A ∪ ℝ`"):

* **two-piece loops** (`windNum_mul_eq_pathInc_add`): the winding number of a loop made of two paths is the sum of
  their logarithmic increments `pathInc` divided by `2πi`; reversing a path negates its increment
  (`pathInc_comp_one_sub`). This is the additivity behind (S2.2).
* **a simple loop bounds its winding set** (`mem_closure_windNum_ne_zero`): if a loop that is injective on `[0, 1)`
  winds about some point, then every point of the loop is a limit of points about which it winds. Proof: otherwise
  the set `E` of such points would have its frontier in the loop minus an open subarc, which is an arc; `E` would be
  open and closed in the connected complement of that arc (an arc does not separate the plane,
  `Sec4.isConnected_compl_of_homeomorph_unitInterval`), hence equal to it and unbounded.
-/

set_option autoImplicit false

noncomputable section

open Complex Set Metric Filter Topology Bornology
open scoped Real
open InteractingSLE.Orientation

namespace InteractingSLE

namespace Theorem14

namespace SB

/-! ### Increments along paths -/

/-- The **increment** `ℓ 1 − ℓ 0` of a continuous logarithm `ℓ` of `f − w` along `[0, 1]` (`0` if `f` is not
continuous on `[0, 1]` or passes through `w`). -/
def pathInc (f : ℝ → ℂ) (w : ℂ) : ℂ :=
  haveI := Classical.propDecidable
  if h : ContinuousOn f (Icc 0 1) ∧ ∀ t ∈ Icc (0 : ℝ) 1, f t ≠ w then
    (exists_lift h.1 h.2).choose 1 - (exists_lift h.1 h.2).choose 0
  else 0

/-- The increment of any continuous logarithm. -/
theorem pathInc_spec {f : ℝ → ℂ} {w : ℂ} (hf : ContinuousOn f (Icc 0 1)) (hw : ∀ t ∈ Icc (0 : ℝ) 1, f t ≠ w)
    {ℓ : ℝ → ℂ} (hℓ : ContinuousOn ℓ (Icc 0 1)) (he : ∀ t ∈ Icc (0 : ℝ) 1, exp (ℓ t) = f t - w) :
    pathInc f w = ℓ 1 - ℓ 0 := by
  unfold pathInc
  split
  · rename_i h
    obtain ⟨hc, he'⟩ := (exists_lift h.1 h.2).choose_spec
    have := QuantumZipper.FieldLawler.flts_sub_const isPreconnected_Icc hc hℓ
      (fun t ht => by rw [he' t ht, he t ht]) (right_mem_Icc.2 zero_le_one) (left_mem_Icc.2 zero_le_one)
    linear_combination this
  · rename_i h
    exact absurd ⟨hf, hw⟩ h

theorem mapsTo_one_sub : MapsTo (fun s : ℝ => 1 - s) (Icc 0 1) (Icc 0 1) := fun s hs =>
  ⟨by linarith [hs.2], by linarith [hs.1]⟩

/-- Reversing a path negates its increment. -/
theorem pathInc_comp_one_sub {f : ℝ → ℂ} {w : ℂ} (hf : ContinuousOn f (Icc 0 1))
    (hw : ∀ t ∈ Icc (0 : ℝ) 1, f t ≠ w) : pathInc (fun s => f (1 - s)) w = -pathInc f w := by
  obtain ⟨ℓ, hℓ, he⟩ := exists_lift hf hw
  have hc : ContinuousOn (fun s : ℝ => 1 - s) (Icc 0 1) := (continuous_const.sub continuous_id).continuousOn
  rw [pathInc_spec hf hw hℓ he, pathInc_spec (f := fun s => f (1 - s)) (hf.comp hc mapsTo_one_sub)
    (fun s hs => hw _ (mapsTo_one_sub hs)) (ℓ := fun s => ℓ (1 - s)) (hℓ.comp hc mapsTo_one_sub)
    (fun s hs => he _ (mapsTo_one_sub hs))]
  simp only [sub_self, sub_zero]
  ring

/-- **The winding number of a loop made of two paths**: if `Λ` runs along `f` on `[0, 1/2]` and along `g` on
`[1/2, 1]`, then `windNum Λ w · 2πi = pathInc f w + pathInc g w`. -/
theorem windNum_mul_eq_pathInc_add {Λ f g : ℝ → ℂ} {w : ℂ} (hΛ : ContinuousOn Λ (Icc 0 1)) (hl : Λ 0 = Λ 1)
    (hw : ∀ t ∈ Icc (0 : ℝ) 1, Λ t ≠ w) (hf : ContinuousOn f (Icc 0 1)) (hg : ContinuousOn g (Icc 0 1))
    (hΛf : ∀ t ∈ Icc (0 : ℝ) (1 / 2), Λ t = f (2 * t)) (hΛg : ∀ t ∈ Icc (1 / 2 : ℝ) 1, Λ t = g (2 * t - 1)) :
    (windNum Λ w : ℂ) * (2 * π * I) = pathInc f w + pathInc g w := by
  obtain ⟨ℓ, hℓ, he⟩ := exists_lift hΛ hw
  have hs := windNum_spec hΛ hw hl hℓ he
  have m1 : MapsTo (fun s : ℝ => s / 2) (Icc 0 1) (Icc 0 1) := fun s hs =>
    ⟨by linarith [hs.1], by linarith [hs.2]⟩
  have m1' : MapsTo (fun s : ℝ => s / 2) (Icc 0 1) (Icc 0 (1 / 2)) := fun s hs =>
    ⟨by linarith [hs.1], by linarith [hs.2]⟩
  have m2 : MapsTo (fun s : ℝ => (s + 1) / 2) (Icc 0 1) (Icc 0 1) := fun s hs =>
    ⟨by linarith [hs.1], by linarith [hs.2]⟩
  have m2' : MapsTo (fun s : ℝ => (s + 1) / 2) (Icc 0 1) (Icc (1 / 2) 1) := fun s hs =>
    ⟨by linarith [hs.1], by linarith [hs.2]⟩
  have ef : ∀ s ∈ Icc (0 : ℝ) 1, f s = Λ (s / 2) := fun s hs => by
    rw [hΛf _ (m1' hs), show 2 * (s / 2) = s by ring]
  have eg : ∀ s ∈ Icc (0 : ℝ) 1, g s = Λ ((s + 1) / 2) := fun s hs => by
    rw [hΛg _ (m2' hs), show 2 * ((s + 1) / 2) - 1 = s by ring]
  have hfw : ∀ s ∈ Icc (0 : ℝ) 1, f s ≠ w := fun s hs => by rw [ef s hs]; exact hw _ (m1 hs)
  have hgw : ∀ s ∈ Icc (0 : ℝ) 1, g s ≠ w := fun s hs => by rw [eg s hs]; exact hw _ (m2 hs)
  have hc1 : ContinuousOn (fun s : ℝ => s / 2) (Icc 0 1) := (continuous_id.div_const _).continuousOn
  have hc2 : ContinuousOn (fun s : ℝ => (s + 1) / 2) (Icc 0 1) :=
    ((continuous_id.add continuous_const).div_const _).continuousOn
  rw [pathInc_spec hf hfw (ℓ := fun s => ℓ (s / 2)) (hℓ.comp hc1 m1) (fun s hs => by
      rw [he _ (m1 hs), ef s hs]),
    pathInc_spec hg hgw (ℓ := fun s => ℓ ((s + 1) / 2)) (hℓ.comp hc2 m2) (fun s hs => by
      rw [he _ (m2 hs), eg s hs]), ← hs]
  norm_num

/-! ### A simple loop bounds its winding set -/

/-- A loop has winding number `0` about the points of its own image. -/
theorem windNum_eq_zero_of_mem_image {Λ : ℝ → ℂ} {w : ℂ} (hw : w ∈ Λ '' Icc 0 1) : windNum Λ w = 0 := by
  obtain ⟨t, ht, rfl⟩ := hw
  unfold windNum
  split
  · rename_i h
    exact absurd rfl (h.2 t ht)
  · rfl

/-- The winding number is constant near a point off the loop. -/
theorem eventually_windNum_eq {Λ : ℝ → ℂ} (hΛ : ContinuousOn Λ (Icc 0 1)) (hl : Λ 0 = Λ 1) {w : ℂ}
    (hw : w ∉ Λ '' Icc 0 1) : ∃ r > 0, ∀ w' ∈ ball w r, windNum Λ w' = windNum Λ w := by
  obtain ⟨r, hr, hrK⟩ := exists_ball_disjoint (isCompact_image_Icc hΛ).isClosed hw
  refine ⟨r, hr, fun w' hw' => windNum_eq_of_isPreconnected hΛ hl (convex_ball w r).isPreconnected ?_ hw'
    (mem_ball_self hr)⟩
  refine Set.disjoint_left.2 fun z hz hzK => ?_
  have h1 := hrK z hzK
  rw [mem_ball, dist_eq_norm] at hz
  linarith

/-- The two-piece reparametrization of a loop started at `b` and run until `1 + a`. -/
def shiftLoop' (Λ : ℝ → ℂ) (u : ℝ) : ℂ := if u ≤ 1 then Λ u else Λ (u - 1)

theorem continuousOn_shiftLoop' {Λ : ℝ → ℂ} (hΛ : ContinuousOn Λ (Icc 0 1)) (hl : Λ 0 = Λ 1) {a b : ℝ}
    (ha : 0 ≤ a) (ha1 : a ≤ 1) (hb : 0 ≤ b) (hb1 : b ≤ 1) : ContinuousOn (shiftLoop' Λ) (Icc b (1 + a)) := by
  have h1 : ContinuousOn (shiftLoop' Λ) (Icc b 1) := by
    refine (hΛ.mono (Icc_subset_Icc hb le_rfl)).congr fun u hu => ?_
    simp only [shiftLoop', hu.2, ↓reduceIte]
  have h2 : ContinuousOn (shiftLoop' Λ) (Icc 1 (1 + a)) := by
    have hc : ContinuousOn (fun u : ℝ => Λ (u - 1)) (Icc 1 (1 + a)) :=
      hΛ.comp (continuous_id.sub continuous_const).continuousOn fun u hu =>
        ⟨by linarith [hu.1], by linarith [hu.2]⟩
    refine hc.congr fun u hu => ?_
    rcases eq_or_lt_of_le hu.1 with h | h
    · simp only [shiftLoop', ← h, le_refl, ↓reduceIte, sub_self, hl]
    · simp only [shiftLoop', not_le.2 h, ↓reduceIte]
  have := h1.union_of_isClosed h2 isClosed_Icc isClosed_Icc
  rwa [Icc_union_Icc_eq_Icc hb1 (by linarith)] at this

/-- **A simple loop bounds its winding set.** Let `Λ` be continuous on `[0, 1]`, closed, injective on `[0, 1)`, and
wind about some point. Then every `Λ t`, `0 < t < 1`, is a limit of points about which `Λ` winds. -/
theorem mem_closure_windNum_ne_zero {Λ : ℝ → ℂ} (hΛ : ContinuousOn Λ (Icc 0 1)) (hl : Λ 0 = Λ 1)
    (hinj : InjOn Λ (Ico 0 1)) {w₀ : ℂ} (hw₀ : windNum Λ w₀ ≠ 0) {t₀ : ℝ} (ht₀ : t₀ ∈ Ioo (0 : ℝ) 1) :
    Λ t₀ ∈ closure {w | windNum Λ w ≠ 0} := by
  set E := {w | windNum Λ w ≠ 0} with hEdef
  set K := Λ '' Icc 0 1 with hKdef
  have hKc : IsCompact K := isCompact_image_Icc hΛ
  have hEK : ∀ w ∈ E, w ∉ K := fun w hw hwK => hw (windNum_eq_zero_of_mem_image hwK)
  -- `E` is open, and its closure adds only points of `K`
  have hEo : IsOpen E := by
    refine Metric.isOpen_iff.2 fun w hw => ?_
    obtain ⟨r, hr, hc⟩ := eventually_windNum_eq hΛ hl (hEK w hw)
    exact ⟨r, hr, fun w' hw' => by
      show windNum Λ w' ≠ 0
      rw [hc w' hw']; exact hw⟩
  have hEcl : ∀ w ∈ closure E, w ∉ K → w ∈ E := fun w hw hwK => by
    obtain ⟨r, hr, hc⟩ := eventually_windNum_eq hΛ hl hwK
    obtain ⟨w', hw'E, hw'⟩ := Metric.mem_closure_iff.1 hw r hr
    show windNum Λ w ≠ 0
    rw [← hc w' (by rw [mem_ball, dist_comm]; exact hw')]
    exact hw'E
  -- `E` is bounded
  have hEb : IsBounded E := by
    obtain ⟨M, hM⟩ := hKc.isBounded.exists_norm_le
    refine isBounded_iff_forall_norm_le.2 ⟨M, fun w hw => not_lt.1 fun hlt => hw ?_⟩
    exact windNum_eq_zero_of_norm_lt hΛ hl fun t ht => (hM _ (mem_image_of_mem Λ ht)).trans_lt hlt
  -- injectivity on `(0, 1]`
  have hinj' : InjOn Λ (Ioc 0 1) := by
    intro s hs t ht hst
    rcases eq_or_lt_of_le hs.2 with hs1 | hs1 <;> rcases eq_or_lt_of_le ht.2 with ht1 | ht1
    · rw [hs1, ht1]
    · rw [hs1, ← hl] at hst
      exact absurd (hinj (left_mem_Ico.2 zero_lt_one) ⟨ht.1.le, ht1⟩ hst) (ne_of_lt ht.1)
    · rw [ht1, ← hl] at hst
      exact absurd (hinj ⟨hs.1.le, hs1⟩ (left_mem_Ico.2 zero_lt_one) hst) (ne_of_gt hs.1)
    · exact hinj ⟨hs.1.le, hs1⟩ ⟨ht.1.le, ht1⟩ hst
  by_contra hcon
  -- an open subarc `Λ([a, b])` off `closure E`
  have hU : (closure E)ᶜ ∈ 𝓝 (Λ t₀) := isClosed_closure.isOpen_compl.mem_nhds hcon
  have hcont : ContinuousAt Λ t₀ :=
    hΛ.continuousAt (Icc_mem_nhds ht₀.1 ht₀.2)
  obtain ⟨δ, hδ, hδU⟩ := Metric.mem_nhds_iff.1 (hcont.preimage_mem_nhds hU)
  set a := max (t₀ - δ / 2) (t₀ / 2) with ha
  set b := min (t₀ + δ / 2) ((t₀ + 1) / 2) with hb
  have ha0 : 0 < a := lt_max_of_lt_right (by linarith [ht₀.1])
  have hat : a < t₀ := max_lt (by linarith) (by linarith [ht₀.1])
  have htb : t₀ < b := lt_min (by linarith) (by linarith [ht₀.2])
  have hb1 : b < 1 := min_lt_of_right_lt (by linarith [ht₀.2])
  have hab : Icc a b ⊆ ball t₀ δ := fun u hu => by
    rw [mem_ball, Real.dist_eq, abs_lt]
    constructor
    · linarith [le_max_left (t₀ - δ / 2) (t₀ / 2), hu.1]
    · linarith [min_le_left (t₀ + δ / 2) ((t₀ + 1) / 2), hu.2]
  have hoff : ∀ u ∈ Icc a b, Λ u ∉ closure E := fun u hu => hδU (hab hu)
  -- the complementary arc
  set J := shiftLoop' Λ '' Icc b (1 + a) with hJdef
  have hJc : ContinuousOn (shiftLoop' Λ) (Icc b (1 + a)) :=
    continuousOn_shiftLoop' hΛ hl ha0.le (by linarith) (by linarith) hb1.le
  have hJinj : InjOn (shiftLoop' Λ) (Icc b (1 + a)) := by
    intro u hu v hv huv
    have key : ∀ x ∈ Icc b (1 + a), (x ≤ 1 ∧ shiftLoop' Λ x = Λ x ∧ x ∈ Ioc 0 1) ∨
        (1 < x ∧ shiftLoop' Λ x = Λ (x - 1) ∧ x - 1 ∈ Ioc 0 1 ∧ x - 1 ≤ a) := fun x hx => by
      by_cases h : x ≤ 1
      · exact Or.inl ⟨h, by simp only [shiftLoop', h, ↓reduceIte], ⟨by linarith [hx.1], h⟩⟩
      · refine Or.inr ⟨not_le.1 h, by simp only [shiftLoop', h, ↓reduceIte], ⟨by linarith, ?_⟩, ?_⟩
        · linarith [hx.2]
        · linarith [hx.2]
    rcases key u hu with ⟨hu1, hue, hum⟩ | ⟨hu1, hue, hum, hua⟩ <;>
      rcases key v hv with ⟨hv1, hve, hvm⟩ | ⟨hv1, hve, hvm, hva⟩ <;> rw [hue, hve] at huv
    · exact hinj' hum hvm huv
    · have := hinj' hum hvm huv; linarith [hu.1]
    · have := hinj' hum hvm huv; linarith [hv.1]
    · have := hinj' hum hvm huv; linarith
  obtain ⟨φ⟩ := Sec4.nonempty_homeomorph_unitInterval_image (by linarith) hJc hJinj
  have hJconn : IsConnected Jᶜ := Sec4.isConnected_compl_of_homeomorph_unitInterval φ
  have hJK : J ⊆ K := by
    rintro _ ⟨u, hu, rfl⟩
    by_cases h : u ≤ 1
    · simp only [shiftLoop', h, ↓reduceIte]
      exact mem_image_of_mem Λ ⟨by linarith [hu.1], h⟩
    · simp only [shiftLoop', h, ↓reduceIte]
      exact mem_image_of_mem Λ ⟨by linarith, by linarith [hu.2]⟩
  -- `E` is open and closed in `Jᶜ`
  have hcl : ∀ w ∈ closure E, w ∉ J → w ∈ E := by
    intro w hw hwJ
    by_cases hwK : w ∈ K
    · exfalso
      obtain ⟨t, ht, rfl⟩ := hwK
      by_cases hta : t < a
      · rcases eq_or_lt_of_le ht.1 with h0 | h0
        · refine hwJ ⟨1, ⟨hb1.le, by linarith⟩, ?_⟩
          simp only [shiftLoop', le_refl, ↓reduceIte, ← h0, hl]
        · refine hwJ ⟨1 + t, ⟨by linarith, by linarith⟩, ?_⟩
          simp only [shiftLoop', show ¬ (1 + t ≤ 1) by linarith, ↓reduceIte, add_sub_cancel_left]
      · by_cases htb' : t ≤ b
        · exact hoff t ⟨not_lt.1 hta, htb'⟩ hw
        · refine hwJ ⟨t, ⟨(not_le.1 htb').le, by linarith [ht.2]⟩, ?_⟩
          simp only [shiftLoop', ht.2, ↓reduceIte]
    · exact hEcl w hw hwK
  have hsub : Jᶜ ⊆ E := by
    have hcov : Jᶜ ⊆ E ∪ (closure E)ᶜ := fun w hw => by
      by_cases hwc : w ∈ closure E
      · exact Or.inl (hcl w hwc hw)
      · exact Or.inr hwc
    have hdis : Disjoint E (closure E)ᶜ := Set.disjoint_left.2 fun w hw hwc => hwc (subset_closure hw)
    exact hJconn.isPreconnected.subset_left_of_subset_union hEo isClosed_closure.isOpen_compl hdis hcov
      ⟨w₀, fun h => hEK w₀ hw₀ (hJK h), hw₀⟩
  -- but `Jᶜ` is unbounded
  have hJb : IsBounded J := hKc.isBounded.subset hJK
  have hu : IsBounded (univ : Set ℂ) := by
    rw [← union_compl_self J]
    exact hJb.union (hEb.subset hsub)
  exact NormedSpace.unbounded_univ ℝ ℂ hu

end SB

end Theorem14

end InteractingSLE
