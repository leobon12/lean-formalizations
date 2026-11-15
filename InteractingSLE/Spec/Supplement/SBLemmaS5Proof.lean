/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.SBLemmaS5Main
import InteractingSLE.Spec.Supplement.SBLemmaS2LiftChart
import InteractingSLE.Spec.Supplement.SBLemmaS

/-!
# Lemma S5, main clause: the glued completion (S5c) and the reduction to the side comparison (S5d)

Packet PROVE-T14-SB8. Lemma S5 (supplement pp. 582–583, `source/spec/p577-624.md` L109–L122): "Translate back. Every
new real contact of this completion is strictly below `v_L`, hence outside `I = [v_L, v_R]`. It therefore pulls back
to a genuine original-real point to the left of the old base. Its new interior points pull back inside `D_A`. It cannot
hit the old inside-`K_A` second history, nor a second physical fiber of an old-range point. On the untouched
original-real ray the inverse map is reflected and injective. The retained lifted prefix was already the actual simple
second history. Consequently the whole pullback, joined to the retained portion through `L`, is a proper injective
physical extension of that second history."

* **The boundary extension `g` of `c.inv`** (`A = p([0, 1])`, `c` a left entry chart of `D_A = ℍ ∖ fill(A)` at
  `L = min(A ∩ ℝ)`): real points are not mapped into `D_A` (`g_ofReal_notMem`); a real point mapped to an untouched
  real `x < L` is the boundary value `e x` (`eq_of_g_ofReal_eq`); `g` keeps `closure ℍ`
  (`im_g_nonneg`); `‖w‖ ≤ C₁ ‖g w‖ + C₂` (`exists_norm_le_norm_g`).
* **`gluedCurve β' g bt tL`**: `β'` up to `t_L`, then `g ∘ bt (· − t_L)`.
* **S5c, `isProperCompletion_gluedCurve`**: for the S1 witness `β'` of the second prefix and the left-shifted relative
  completion `bt` of `exists_leftShift_of_ordered`, the glued curve is a proper completion of `β|[0, a₂]`; after `a₂` it
  runs in `D_A ∪ (−∞, L)` (`gluedCurve_mem_of_lt`).
* **S5d** is the named statement `S5SideStatement` (the physical range `A ∪ g(aR([0, a₁]))` is on the closed right of
  the glued curve); **`s5Statement_of_side`** proves `SB.S5Statement` from it.
-/

set_option autoImplicit false

noncomputable section

open Complex Set Metric Filter Topology Bornology
open scoped NNReal
open QuantumZipper (H)
open InteractingSLE.Supp9B (IsProperCurve leftSide rightSide closedRightSide)

namespace InteractingSLE

namespace Theorem14

namespace SB

/-! ### The boundary extension of the inverse chart -/

section Ext

variable {A : Set ℂ} {c : Chart} {g : ℂ → ℂ}

/-- The vertical approach to a real point stays in `ℍ`. -/
theorem tendsto_vertical_nhdsWithin_H (v : ℝ) :
    Tendsto (fun y : ℝ => (v : ℂ) + (y : ℂ) * I) (𝓝[>] 0) (𝓝[H] (v : ℂ)) := by
  refine tendsto_nhdsWithin_iff.2 ⟨?_, ?_⟩
  · have h : Tendsto (fun y : ℝ => (v : ℂ) + (y : ℂ) * I) (𝓝 0) (𝓝 ((v : ℂ) + ((0 : ℝ) : ℂ) * I)) :=
      (Continuous.tendsto (by fun_prop) 0)
    simpa using h.mono_left nhdsWithin_le_nhds
  · filter_upwards [self_mem_nhdsWithin] with y hy
    show 0 < ((v : ℂ) + (y : ℂ) * I).im
    simpa using hy

theorem H_subset_im_nonneg : H ⊆ {z : ℂ | 0 ≤ z.im} := fun z (hz : 0 < z.im) => show 0 ≤ z.im from le_of_lt hz

/-- `g` along the vertical approach to a real point. -/
theorem tendsto_g_vertical (hgc : ContinuousOn g {z | 0 ≤ z.im}) (v : ℝ) :
    Tendsto (fun y : ℝ => g ((v : ℂ) + (y : ℂ) * I)) (𝓝[>] 0) (𝓝 (g v)) :=
  (hgc v (show (0 : ℝ) ≤ ((v : ℝ) : ℂ).im by simp)).tendsto.comp
    ((tendsto_vertical_nhdsWithin_H v).mono_right (nhdsWithin_mono _ H_subset_im_nonneg))

/-- The chart composed with `g` along the vertical approach is the identity. -/
theorem fwd_g_vertical (hD : IsDomainChart (H \ fillH A) c) (hgi : EqOn g c.2.1 H) (v : ℝ) :
    ∀ᶠ y : ℝ in 𝓝[>] 0, c.1 (g ((v : ℂ) + (y : ℂ) * I)) = (v : ℂ) + (y : ℂ) * I := by
  filter_upwards [self_mem_nhdsWithin] with y hy
  have hH : (v : ℂ) + (y : ℂ) * I ∈ H := show 0 < ((v : ℂ) + (y : ℂ) * I).im by simpa using hy
  rw [hgi hH]
  exact hD.1.2.2 _ hH

/-- **A real point is not mapped into `D_A`** (if `g v ∈ D_A`, continuity of the chart at `g v` would give
`c.fwd (g v) = v ∉ ℍ`). -/
theorem g_ofReal_notMem (hD : IsDomainChart (H \ fillH A) c) (hgc : ContinuousOn g {z | 0 ≤ z.im})
    (hgi : EqOn g c.2.1 H) (v : ℝ) : g v ∉ H \ fillH A := by
  intro hz
  have hca : ContinuousAt c.1 (g v) :=
    ((hD.differentiableOn_fwd _ hz).differentiableAt (hD.isOpen.mem_nhds hz)).continuousAt
  have h1 := hca.tendsto.comp (tendsto_g_vertical hgc v)
  have h2 : Tendsto (fun y : ℝ => (v : ℂ) + (y : ℂ) * I) (𝓝[>] 0) (𝓝 (v : ℂ)) :=
    (tendsto_vertical_nhdsWithin_H v).mono_right nhdsWithin_le_nhds
  have h3 : c.1 (g v) = v := tendsto_nhds_unique (h1.congr' (fwd_g_vertical hD hgi v)) h2
  have := hD.fwd_mem hz
  rw [h3] at this
  exact absurd this (by simp [QuantumZipper.H])

/-- `g` maps `ℍ` into `D_A`. -/
theorem g_mem_of_mem_H (hD : IsDomainChart (H \ fillH A) c) (hgi : EqOn g c.2.1 H) {w : ℂ} (hw : w ∈ H) :
    g w ∈ H \ fillH A := by
  rw [hgi hw]
  exact hD.inv_mem hw

/-- **A real point mapped to an untouched real point is its boundary value**: if `c.fwd` has the boundary value `e`
at `x` from `ℍ` and `g v = x`, then `v = e`. -/
theorem eq_of_g_ofReal_eq (hD : IsDomainChart (H \ fillH A) c) (hgc : ContinuousOn g {z | 0 ≤ z.im})
    (hgi : EqOn g c.2.1 H) {x e : ℝ} (he : Tendsto c.1 (𝓝[H] (x : ℂ)) (𝓝 (e : ℂ))) {v : ℝ}
    (hv : g v = x) : v = e := by
  have h1 : Tendsto (fun y : ℝ => g ((v : ℂ) + (y : ℂ) * I)) (𝓝[>] 0) (𝓝[H] (x : ℂ)) := by
    refine tendsto_nhdsWithin_iff.2 ⟨hv ▸ tendsto_g_vertical hgc v, ?_⟩
    filter_upwards [self_mem_nhdsWithin] with y hy
    exact (g_mem_of_mem_H hD hgi (show 0 < ((v : ℂ) + (y : ℂ) * I).im by simpa using hy)).1
  have h2 := (he.comp h1).congr' (fwd_g_vertical hD hgi v)
  have h3 : Tendsto (fun y : ℝ => (v : ℂ) + (y : ℂ) * I) (𝓝[>] 0) (𝓝 (v : ℂ)) :=
    (tendsto_vertical_nhdsWithin_H v).mono_right nhdsWithin_le_nhds
  exact_mod_cast tendsto_nhds_unique h3 h2

/-- **`g` keeps `closure ℍ`.** -/
theorem im_g_nonneg (hD : IsDomainChart (H \ fillH A) c) (hgc : ContinuousOn g {z | 0 ≤ z.im})
    (hgi : EqOn g c.2.1 H) {w : ℂ} (hw : 0 ≤ w.im) : 0 ≤ (g w).im := by
  rcases hw.lt_or_eq with hlt | heq
  · exact le_of_lt (g_mem_of_mem_H hD hgi hlt).1
  · have hw' : w = (w.re : ℂ) := Complex.ext (by simp) (by simp [← heq])
    rw [hw']
    refine ge_of_tendsto ((continuous_im.tendsto _).comp (tendsto_g_vertical hgc w.re)) ?_
    filter_upwards [self_mem_nhdsWithin] with y hy
    exact le_of_lt (g_mem_of_mem_H hD hgi (show 0 < ((w.re : ℂ) + (y : ℂ) * I).im by simpa using hy)).1

/-- **`g` grows at least linearly** on `closure ℍ` (the left entry chart grows at most linearly on `D_A`). -/
theorem exists_norm_le_norm_g {L : ℝ} (hc : IsLeftEntryChart A L c) (hAb : IsBounded A)
    (hAc : IsPreconnected (A ∪ {z : ℂ | z.im ≤ 0})) (hgc : ContinuousOn g {z | 0 ≤ z.im})
    (hgi : EqOn g c.2.1 H) : ∃ C₁ C₂ : ℝ, 0 ≤ C₁ ∧ ∀ w : ℂ, 0 ≤ w.im → ‖w‖ ≤ C₁ * ‖g w‖ + C₂ := by
  obtain ⟨C₁, C₂, hC₁, hb⟩ := hc.exists_norm_fwd_le hAb hAc
  have hD := hc.1
  have hH : ∀ w ∈ H, ‖w‖ ≤ C₁ * ‖g w‖ + C₂ := fun w hw => by
    have h := hb _ (g_mem_of_mem_H hD hgi hw)
    rw [hgi hw]
    rwa [hgi hw, hD.1.2.2 w hw] at h
  refine ⟨C₁, C₂, hC₁, fun w hw => ?_⟩
  rcases hw.lt_or_eq with hlt | heq
  · exact hH w hlt
  · have hw' : w = (w.re : ℂ) := Complex.ext (by simp) (by simp [← heq])
    rw [hw']
    have h1 : Tendsto (fun y : ℝ => C₁ * ‖g ((w.re : ℂ) + (y : ℂ) * I)‖ + C₂ -
        ‖(w.re : ℂ) + (y : ℂ) * I‖) (𝓝[>] 0) (𝓝 (C₁ * ‖g (w.re : ℂ)‖ + C₂ - ‖(w.re : ℂ)‖)) := by
      refine ((((continuous_norm.tendsto _).comp (tendsto_g_vertical hgc w.re)).const_mul C₁).add_const
        C₂).sub ((continuous_norm.tendsto _).comp ((tendsto_vertical_nhdsWithin_H w.re).mono_right
          nhdsWithin_le_nhds))
    have h2 : (0 : ℝ) ≤ C₁ * ‖g (w.re : ℂ)‖ + C₂ - ‖(w.re : ℂ)‖ := ge_of_tendsto h1 (by
      filter_upwards [self_mem_nhdsWithin] with y hy
      have := hH _ (show 0 < ((w.re : ℂ) + (y : ℂ) * I).im by simpa using hy)
      linarith)
    linarith

end Ext

/-! ### The hull of the retained history -/

theorem notMem_hullK_of_mem_D {A : Set ℂ} {z : ℂ} (hz : z ∈ H \ fillH A) : z ∉ hullK A := by
  rintro (h | ⟨x, -, rfl⟩)
  · exact hz.2 h
  · exact absurd hz.1 (by simp [QuantumZipper.H])

theorem ofReal_notMem_hullK {A : Set ℂ} {x : ℝ} (hx : x < realMin A) : (x : ℂ) ∉ hullK A := by
  rintro (h | ⟨y, hy, hyx⟩)
  · exact absurd h.1 (by simp [QuantumZipper.H])
  · have := Complex.ofReal_injective hyx
    subst this
    exact absurd hy.1 (not_le.2 hx)

/-! ### The glued completion (S5c) -/

/-- **The glued curve** of Lemma S5: the S1 witness `β'` up to `t_L`, then the pullback `g ∘ bt (· − t_L)` of the
relative completion `bt`. -/
def gluedCurve (β' : ℝ≥0 → ℂ) (g : ℂ → ℂ) (bt : ℝ≥0 → ℂ) (tL : ℝ≥0) : ℝ≥0 → ℂ :=
  fun s => if s ≤ tL then β' s else g (bt (s - tL))

section Glued

variable {β β' : ℝ≥0 → ℂ} {g : ℂ → ℂ} {bt : ℝ≥0 → ℂ} {tL : ℝ≥0}

theorem gluedCurve_of_le {s : ℝ≥0} (hs : s ≤ tL) : gluedCurve β' g bt tL s = β' s := by
  simp only [gluedCurve, hs, ↓reduceIte]

theorem gluedCurve_of_lt {s : ℝ≥0} (hs : tL < s) : gluedCurve β' g bt tL s = g (bt (s - tL)) := by
  simp only [gluedCurve, not_le.2 hs, ↓reduceIte]

theorem gluedCurve_add (hj : β' tL = g (bt 0)) (u : ℝ≥0) : gluedCurve β' g bt tL (tL + u) = g (bt u) := by
  rcases eq_or_lt_of_le (zero_le : (0 : ℝ≥0) ≤ u) with h | h
  · rw [← h, add_zero, gluedCurve_of_le le_rfl, hj]
  · rw [gluedCurve_of_lt (lt_add_of_pos_right tL h), add_tsub_cancel_left]

theorem gluedCurve_of_ge (hj : β' tL = g (bt 0)) {s : ℝ≥0} (hs : tL ≤ s) :
    gluedCurve β' g bt tL s = g (bt (s - tL)) := by
  rw [← gluedCurve_add hj (s - tL), add_tsub_cancel_of_le hs]

end Glued

section S5c

variable {p : ℝ → ℂ} {β β' : ℝ≥0 → ℂ} {a₂ tL : ℝ≥0} {c : Chart} {g : ℂ → ℂ} {bt : ℝ≥0 → ℂ}

/-- **The three kinds of points of the pulled-back tail** (S5: "Every new real contact of this completion is strictly
below `v_L` [...] It therefore pulls back to a genuine original-real point to the left of the old base. Its new interior
points pull back inside `D_A`. [...] The retained lifted prefix was already the actual simple second history"): a point
`bt u` of the relative completion is in `ℍ` (pulled back into `D_A`), or real within the retained prefix (pulled back
onto the second history), or real after it, negative, and pulled back to an untouched real point `x < L` with
`bt u = e x`. -/
theorem tail_cases (hp : ContinuousOn p (Icc 0 1)) (hp0 : p 0 = 0)
    (hc : IsLeftEntryChart (p '' Icc 0 1) (realMin (p '' Icc 0 1)) c) (hgc : ContinuousOn g {z | 0 ≤ z.im})
    (hgi : EqOn g c.2.1 H) (hbt : IsProperCurve bt) (hβ' : ∀ t ≤ a₂, β' t = β t) (htL : tL ≤ a₂)
    (hbtβ : ∀ s ≤ a₂ - tL, g (bt s) = β (tL + s))
    (hreal : ∀ s, a₂ - tL < s → (bt s).im = 0 → (bt s).re < 0) (u : ℝ≥0) :
    (bt u ∈ H ∧ g (bt u) ∈ H \ fillH (p '' Icc 0 1)) ∨
      ((bt u).im = 0 ∧ u ≤ a₂ - tL ∧ g (bt u) = β' (tL + u)) ∨
      ((bt u).im = 0 ∧ a₂ - tL < u ∧ ∃ x < realMin (p '' Icc 0 1), g (bt u) = x ∧
        (∀ e : ℝ, Tendsto c.1 (𝓝[H] (x : ℂ)) (𝓝 (e : ℂ)) → bt u = e)) := by
  rcases (hbt.2.2.1 u).lt_or_eq with h | h
  · exact Or.inl ⟨h, g_mem_of_mem_H hc.1 hgi h⟩
  · by_cases hu : u ≤ a₂ - tL
    · refine Or.inr (Or.inl ⟨h.symm, hu, ?_⟩)
      rw [hbtβ u hu, hβ' (tL + u) ?_]
      calc tL + u ≤ tL + (a₂ - tL) := add_le_add_right hu tL
        _ = a₂ := add_tsub_cancel_of_le htL
    · have hneg := hreal u (lt_of_not_ge hu) h.symm
      obtain ⟨e, -, -, horient, hsurj⟩ := hc.exists_boundary_orient hp hp0 hgc hgi
      obtain ⟨x, hx, hex⟩ := hsurj _ hneg
      have hbu : bt u = (((bt u).re : ℝ) : ℂ) := Complex.ext (by simp) (by simp [← h])
      refine Or.inr (Or.inr ⟨h.symm, lt_of_not_ge hu, x, hx, ?_, fun e' he' => ?_⟩)
      · rw [hbu, ← hex]
        exact (horient x hx).2
      · have hgx : g (((bt u).re : ℝ) : ℂ) = x := by rw [← hex]; exact (horient x hx).2
        rw [hbu, eq_of_g_ofReal_eq hc.1 hgc hgi he' hgx]

/-- **S5c: the glued curve is a proper completion of the second prefix** (S5: "Consequently the whole pullback,
joined to the retained portion through `L`, is a proper injective physical extension of that second history"). Let
`β'` be an S1 witness for `A = p([0, 1])` and the prefix `β([0, a₂])` (a proper completion with `A` on its closed
right), `c` a left entry chart of `D_A` at `L` with extension `g` of its inverse, `t_L ≤ a₂` with `β(t_L) = L`, and
`bt` a proper curve from `0` with `g ∘ bt = β(t_L + ·)` on `[0, a₂ − t_L]` whose real points after `a₂ − t_L` are
negative. Then `β'|[0, t_L]` followed by `g ∘ bt (· − t_L)` is a proper completion of `β|[0, a₂]`. Injectivity: the
first part is in `K_A` (Lemma S2); the tail is in `D_A`, on the second prefix, or at untouched real points `x < L`
(`tail_cases`), and `g` is injective on each kind. Properness: `‖w‖ ≤ C₁ ‖g w‖ + C₂`. -/
theorem isProperCompletion_gluedCurve (hp : ContinuousOn p (Icc 0 1)) (hp0 : p 0 = 0)
    (hpH : ∀ s ∈ Icc (0 : ℝ) 1, 0 ≤ (p s).im) (hβ0 : β 0 = 0) (hβ' : IsProperCompletion β a₂ β')
    (hA : p '' Icc 0 1 ⊆ closedRightSide β')
    (hc : IsLeftEntryChart (p '' Icc 0 1) (realMin (p '' Icc 0 1)) c) (hgc : ContinuousOn g {z | 0 ≤ z.im})
    (hgi : EqOn g c.2.1 H) (htL : tL ≤ a₂) (hβtL : β tL = realMin (p '' Icc 0 1)) (hbt : IsProperCurve bt)
    (hbtβ : ∀ s ≤ a₂ - tL, g (bt s) = β (tL + s))
    (hreal : ∀ s, a₂ - tL < s → (bt s).im = 0 → (bt s).re < 0) :
    IsProperCompletion β a₂ (gluedCurve β' g bt tL) := by
  set A := p '' Icc 0 1 with hAdef
  set L := realMin A with hLdef
  have hβ'P : IsProperCurve β' := Supp9B.isProperCurve_of_isProperCompletion hβ'
  have hβ'eq : ∀ t ≤ a₂, β' t = β t := hβ'.2.2.2.2
  have hβ'0 : β' 0 = 0 := (hβ'eq 0 zero_le).trans hβ0
  have hβ'tL : β' tL = L := (hβ'eq tL htL).trans hβtL
  obtain ⟨-, tL', htL', -, hsub, -, -⟩ := s2HullStatement p β' hp hp0 hpH hβ'P hβ'0 hA
  have htt : tL' = tL := hβ'P.2.1 (htL'.trans hβ'tL.symm)
  subst htt
  have hD := hc.1
  have hg0 : g (bt 0) = L := by rw [hbtβ 0 zero_le, add_zero, hβtL]
  have hj : β' tL' = g (bt 0) := hβ'tL.trans hg0.symm
  have hT := tail_cases hp hp0 hc hgc hgi hbt hβ'eq htL hbtβ hreal
  have hpre : ∀ s ≤ tL', β' s ∈ hullK A := fun s hs => hsub ⟨s, ⟨zero_le, hs⟩, rfl⟩
  have hle : ∀ u ≤ a₂ - tL', tL' + u ≤ a₂ := fun u hu =>
    (add_le_add_right hu tL').trans (add_tsub_cancel_of_le htL).le
  -- a tail point is never a point of the first part
  have hmix : ∀ s ≤ tL', ∀ u, 0 < u → β' s ≠ g (bt u) := by
    intro s hs u hu he
    rcases hT u with ⟨-, hD'⟩ | ⟨-, hua, hgu⟩ | ⟨-, -, x, hx, hgx, -⟩
    · exact notMem_hullK_of_mem_D hD' (he ▸ hpre s hs)
    · rw [hgu] at he
      have := hβ'P.2.1 he
      rw [this] at hs
      exact absurd hs (not_le.2 (lt_add_of_pos_right tL' hu))
    · rw [hgx] at he
      exact ofReal_notMem_hullK hx (he ▸ hpre s hs)
  -- `g` is injective on the tail
  have htail : ∀ u u', g (bt u) = g (bt u') → u = u' := by
    intro u u' he
    refine hbt.2.1 ?_
    rcases hT u with ⟨hu, hDu⟩ | ⟨hu, hua, hgu⟩ | ⟨hu, hua, x, hx, hgx, hex⟩ <;>
      rcases hT u' with ⟨hu', hDu'⟩ | ⟨hu', hua', hgu'⟩ | ⟨hu', hua', x', hx', hgx', hex'⟩
    · rw [hgi hu, hgi hu'] at he
      exact hD.1.injOn hu hu' he
    · exfalso
      have hb : bt u' = (((bt u').re : ℝ) : ℂ) := Complex.ext (by simp) (by simp [hu'])
      exact g_ofReal_notMem hD hgc hgi (bt u').re (hb ▸ he ▸ hDu)
    · exfalso
      have hb : bt u' = (((bt u').re : ℝ) : ℂ) := Complex.ext (by simp) (by simp [hu'])
      exact g_ofReal_notMem hD hgc hgi (bt u').re (hb ▸ he ▸ hDu)
    · exfalso
      have hb : bt u = (((bt u).re : ℝ) : ℂ) := Complex.ext (by simp) (by simp [hu])
      exact g_ofReal_notMem hD hgc hgi (bt u).re (hb ▸ he.symm ▸ hDu')
    · rw [hgu, hgu'] at he
      have := hβ'P.2.1 he
      rw [add_left_cancel this]
    · obtain ⟨e, he'⟩ := hc.2.1
      rw [hex' (e x') (he'.1 x' hx')]
      have hb : bt u = (((bt u).re : ℝ) : ℂ) := Complex.ext (by simp) (by simp [hu])
      rw [hb, eq_of_g_ofReal_eq hD hgc hgi (he'.1 x' hx') (show g (((bt u).re : ℝ) : ℂ) = x' by
        rw [← hb, he, hgx'])]
    · exfalso
      have hb : bt u = (((bt u).re : ℝ) : ℂ) := Complex.ext (by simp) (by simp [hu])
      exact g_ofReal_notMem hD hgc hgi (bt u).re (hb ▸ he.symm ▸ hDu')
    · obtain ⟨e, he'⟩ := hc.2.1
      rw [hex (e x) (he'.1 x hx)]
      have hb : bt u' = (((bt u').re : ℝ) : ℂ) := Complex.ext (by simp) (by simp [hu'])
      rw [hb, eq_of_g_ofReal_eq hD hgc hgi (he'.1 x hx) (show g (((bt u').re : ℝ) : ℂ) = x by
        rw [← hb, ← he, hgx])]
    · obtain ⟨e, he'⟩ := hc.2.1
      rw [hex (e x) (he'.1 x hx), hex' (e x') (he'.1 x' hx')]
      have hxx : x = x' := by exact_mod_cast hgx.symm.trans (he.trans hgx')
      rw [hxx]
  -- growth of `g`
  have hAc : IsCompact A := isCompact_Icc.image_of_continuousOn hp
  have hAconn : IsPreconnected (A ∪ {z : ℂ | z.im ≤ 0}) := by
    have h0A : (0 : ℂ) ∈ A := ⟨0, left_mem_Icc.2 zero_le_one, hp0⟩
    exact IsPreconnected.union 0 h0A (show (0 : ℂ) ∈ {z : ℂ | z.im ≤ 0} by simp)
      (isPreconnected_Icc.image p hp)
      (convex_halfSpace_le (f := fun z : ℂ => z.im) Complex.imLm.isLinear 0).isPreconnected
  obtain ⟨C₁, C₂, hC₁, hCg⟩ := exists_norm_le_norm_g hc hAc.isBounded hAconn hgc hgi
  refine ⟨?_, ?_, fun s => ?_, ?_, fun s hs => ?_⟩
  · -- continuity
    have hcg : Continuous fun s : ℝ≥0 => g (bt (s - tL')) :=
      hgc.comp_continuous (hbt.1.comp (continuous_id.sub continuous_const)) fun s => hbt.2.2.1 _
    exact Continuous.if_le hβ'P.1 hcg continuous_id continuous_const fun s hs => by
      rw [show s = tL' from hs, tsub_self, hj]
  · -- injectivity
    intro s s' he
    rcases le_or_gt s tL' with hs | hs <;> rcases le_or_gt s' tL' with hs' | hs'
    · rw [gluedCurve_of_le hs, gluedCurve_of_le hs'] at he
      exact hβ'P.2.1 he
    · rw [gluedCurve_of_le hs, gluedCurve_of_lt hs'] at he
      exact absurd he (hmix s hs _ (tsub_pos_of_lt hs'))
    · rw [gluedCurve_of_lt hs, gluedCurve_of_le hs'] at he
      exact absurd he.symm (hmix s' hs' _ (tsub_pos_of_lt hs))
    · rw [gluedCurve_of_lt hs, gluedCurve_of_lt hs'] at he
      have := htail _ _ he
      rw [← add_tsub_cancel_of_le hs.le, ← add_tsub_cancel_of_le hs'.le, this]
  · -- in `closure ℍ`
    rcases le_or_gt s tL' with hs | hs
    · rw [gluedCurve_of_le hs]; exact hβ'P.2.2.1 s
    · rw [gluedCurve_of_lt hs]; exact im_g_nonneg hD hgc hgi (hbt.2.2.1 _)
  · -- properness
    have hsh : Tendsto (fun s : ℝ≥0 => s - tL') atTop atTop :=
      tendsto_atTop_atTop.2 fun b => ⟨b + tL', fun s hs => le_tsub_of_add_le_right hs⟩
    have hpos : (0 : ℝ) < C₁ + 1 := by linarith
    have h1 : Tendsto (fun s : ℝ≥0 => (‖bt (s - tL')‖ - C₂) / (C₁ + 1)) atTop atTop := by
      have h0 := (tendsto_atTop_add_const_right _ (-C₂) (hbt.2.2.2.comp hsh)).atTop_div_const hpos
      refine h0.congr fun s => ?_
      simp only [Function.comp_apply, sub_eq_add_neg]
    refine tendsto_atTop_mono' atTop ?_ h1
    filter_upwards [eventually_gt_atTop tL'] with s hs
    rw [gluedCurve_of_lt hs, div_le_iff₀ (by linarith)]
    have := hCg _ (hbt.2.2.1 (s - tL'))
    nlinarith [norm_nonneg (g (bt (s - tL')))]
  · -- agreement with the prefix
    rcases le_or_gt s tL' with hs' | hs'
    · rw [gluedCurve_of_le hs']; exact hβ'eq s hs
    · rw [gluedCurve_of_lt hs', hbtβ _ (tsub_le_tsub_right hs tL'), add_tsub_cancel_of_le hs'.le]

/-- **After the second prefix the glued curve runs in `D_A ∪ (−∞, L)`** (S5: "Every new real contact of this completion
[...] pulls back to a genuine original-real point to the left of the old base. Its new interior points pull back inside
`D_A`"). -/
theorem gluedCurve_mem_of_lt (hp : ContinuousOn p (Icc 0 1)) (hp0 : p 0 = 0)
    (hβ' : ∀ t ≤ a₂, β' t = β t)
    (hc : IsLeftEntryChart (p '' Icc 0 1) (realMin (p '' Icc 0 1)) c) (hgc : ContinuousOn g {z | 0 ≤ z.im})
    (hgi : EqOn g c.2.1 H) (htL : tL ≤ a₂) (hbt : IsProperCurve bt)
    (hbtβ : ∀ s ≤ a₂ - tL, g (bt s) = β (tL + s))
    (hreal : ∀ s, a₂ - tL < s → (bt s).im = 0 → (bt s).re < 0) {s : ℝ≥0} (hs : a₂ < s) :
    gluedCurve β' g bt tL s ∈ H \ fillH (p '' Icc 0 1) ∨
      ∃ x < realMin (p '' Icc 0 1), gluedCurve β' g bt tL s = x := by
  have hts : tL < s := lt_of_le_of_lt htL hs
  rw [gluedCurve_of_lt hts]
  have hu : a₂ - tL < s - tL := tsub_lt_tsub_right_of_le htL hs
  rcases tail_cases hp hp0 hc hgc hgi hbt hβ' htL hbtβ hreal (s - tL) with ⟨-, hD⟩ | ⟨-, hle, -⟩ |
      ⟨-, -, x, hx, hgx, -⟩
  · exact Or.inl hD
  · exact absurd hle (not_le.2 hu)
  · exact Or.inr ⟨x, hx, hgx⟩

end S5c

/-! ### S5d, and Lemma S5 from it -/

/-- **S5d, the side comparison** (supplement p. 583: "The inherited boundary orientation at `v_L` places all the old
interval `I` on its closed right. Thus the old physical range `A` stays on that side after gluing. [...] Conformality
transports the relative order of interior points of `a`. Its old-range contacts map into `A`, already on the right, and
its other real contacts use reflection. Hence the entire new physical range is on the closed right of the constructed
extension"). In the setting of `isProperCompletion_gluedCurve`, if the relative first prefix `aR([0, a₁])` is on the
closed right of the relative completion `bt`, then `A ∪ g(aR([0, a₁]))` is on the closed right of the glued curve.
**Not proved here** (see `planning/handoffs/PROVE-T14-SB8.md`). -/
def S5SideStatement : Prop :=
  ∀ (p : ℝ → ℂ) (β β' : ℝ≥0 → ℂ) (a₂ : ℝ≥0), ContinuousOn p (Icc 0 1) → p 0 = 0 →
    (∀ s ∈ Icc (0 : ℝ) 1, 0 ≤ (p s).im) → β 0 = 0 → IsProperCompletion β a₂ β' →
    p '' Icc 0 1 ⊆ closedRightSide β' →
    ∀ (c : Chart) (g : ℂ → ℂ), IsLeftEntryChart (p '' Icc 0 1) (realMin (p '' Icc 0 1)) c →
      ContinuousOn g {z | 0 ≤ z.im} → EqOn g c.2.1 H → (∀ z, (g ⁻¹' {z} ∩ {w | 0 ≤ w.im}).Finite) →
    ∀ (tL a₁ : ℝ≥0) (aR bt : ℝ≥0 → ℂ), tL ≤ a₂ → β tL = realMin (p '' Icc 0 1) → IsProperCurve bt →
      bt 0 = 0 → (∀ s ≤ a₂ - tL, g (bt s) = β (tL + s)) →
      (∀ s, a₂ - tL < s → (bt s).im = 0 → (bt s).re < 0) → aR '' Icc 0 a₁ ⊆ closedRightSide bt →
      p '' Icc 0 1 ∪ g '' (aR '' Icc 0 a₁) ⊆ closedRightSide (gluedCurve β' g bt tL)

/-- **Lemma S5's main clause from S5d** (`SB.S5Statement`): the S1 witness `β'`, the left shift `bt` of the ordered
completion of the relative second prefix (`exists_leftShift_of_ordered`), the glued completion (S5c,
`isProperCompletion_gluedCurve`) and S5d. -/
theorem s5Statement_of_side (hS : S5SideStatement) : S5Statement := by
  intro p β a₂ hp hp0 hpH hβ0 hS1 c g hc hgc hgi hgf tL a₁ aR bR w htL hβtL hbR0 hbR hw haR0 hord
  obtain ⟨β', hβ', hA⟩ := hS1
  obtain ⟨bt, hbt, hbt0, hreal, -, haR⟩ := exists_leftShift_of_ordered hbR0 hw haR0 hord
  have hbtP : IsProperCurve bt := Supp9B.isProperCurve_of_isProperCompletion hbt
  have hbtβ : ∀ s ≤ a₂ - tL, g (bt s) = β (tL + s) := fun s hs => by
    rw [hbt.2.2.2.2 s hs]
    exact hbR s hs
  exact ⟨gluedCurve β' g bt tL,
    isProperCompletion_gluedCurve hp hp0 hpH hβ0 hβ' hA hc hgc hgi htL hβtL hbtP hbtβ hreal,
    hS p β β' a₂ hp hp0 hpH hβ0 hβ' hA c g hc hgc hgi hgf tL a₁ aR bt htL hβtL hbtP hbt0 hbtβ hreal haR⟩

end SB

end Theorem14

end InteractingSLE
