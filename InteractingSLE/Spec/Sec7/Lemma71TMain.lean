/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.Lemma71TTrap
import InteractingSLE.Spec.Sec7.Lemma71PWire

/-!
# `MidRealOffStatement`: the middle boundary arcs of a simple Loewner hull meet the real line only on the far side

Packet PROVE-LEMMA71T. For a continuous driver `W` (`W 0 = 0`) with a Loewner trace `η` injective on `[0, t]`, let
`F̄_t` be the boundary extension of `f_t⁻¹`. This file proves **`midRealOffStatement`**
(`Lemma71P.MidRealOffStatement`): `F̄_t` takes no real value `≤ 0` on the left middle interval `(L_t − W_t, 0)` and no
real value `≥ 0` on the right middle interval `(0, R_t − W_t)`.

Proof (left interval; the right one is the mirror argument). Let `x ∈ (L_t − W_t, 0)` with `q = F̄_t(x)` real, `q ≤ 0`.
Then `q = η(v)` lies on the trace (`Lemma71P.mem_image_of_mid`). Far to the left, `F̄_t(z₁)` is a real point off the
trace with `F̄_t(z₁) < q` (`exists_far`: `F̄_t` moves points by a bounded amount). The trap `exists_trap` for
`z₁ < x` gives a bounded set `I` containing `F̄_t(z₀) = η(w)` for a middle point `z₀ ∈ (L_t − W_t, x)` with
`F̄_t(z₀) ≠ q` (`exists_ne_of_injOn`), not containing the tip `η(t) = F̄_t(0)` (`0 ∉ [z₁, x]`), and trapping every
preconnected subset of `ℝ ∪ η([0, t])` that avoids `F̄_t(z₁)` and `q`. If `w > v`, the arc `η([w, t])` is such a set
through `η(w)` and the tip; if `w < v` (so `v > 0` and `q < 0`), `η([0, w]) ∪ [0, ∞)` is such a set and is unbounded
(`false_of_trap`).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Complex Set Metric Filter Topology
open QuantumZipper (H Hbar fwdMapInv fwdHull)

namespace InteractingSLE.Sec7.Lemma71T

open Lemma71P (midL midR MidRealOffStatement)

section Loewner

variable {W : ℝ → ℝ} {η : ℝ → ℂ} {t : ℝ}

/-- **The fibre setting for `F̄_t`** (as in `Lemma71P.eq_zero_of_extendFrom_eq_tip`): with `D = ℍ ∖ K_t` and
`E = ℝ ∪ η([0, t])`, `F̄_t` is holomorphic and injective on `ℍ`, continuous on `ℍ̄`, maps `ℍ` onto `D`, real points into
`∂D` and `∞` to `∞`; `D` is open and disjoint from `E`, and `∂D ⊆ E`. -/
theorem fibre_setting (hη : IsLoewnerTrace W η) (hW : Continuous W) (hW0 : W 0 = 0) (ht : 0 ≤ t) :
    IsOpen (H \ fwdHull W t) ∧ DifferentiableOn ℂ (extendFrom H (fwdMapInv W t)) H ∧
      ContinuousOn (extendFrom H (fwdMapInv W t)) Hbar ∧ InjOn (extendFrom H (fwdMapInv W t)) H ∧
      MapsTo (extendFrom H (fwdMapInv W t)) H (H \ fwdHull W t) ∧
      SurjOn (extendFrom H (fwdMapInv W t)) H (H \ fwdHull W t) ∧
      MapsTo (extendFrom H (fwdMapInv W t)) (Hbar \ H) (frontier (H \ fwdHull W t)) ∧
      Tendsto (extendFrom H (fwdMapInv W t)) (Bornology.cobounded ℂ ⊓ 𝓟 Hbar) (Bornology.cobounded ℂ) ∧
      Disjoint (H \ fwdHull W t) ({z : ℂ | z.im = 0} ∪ η '' Icc 0 t) ∧
      frontier (H \ fwdHull W t) ⊆ {z : ℂ | z.im = 0} ∪ η '' Icc 0 t := by
  set F := extendFrom H (fwdMapInv W t) with hFdef
  set A := η '' Icc 0 t with hA
  have hAc : IsCompact A := hη.isCompact_image t
  obtain ⟨hFd, hFc, hFi, -⟩ := hη.fiber_hyps hW hW0 ht
  have hFeq : EqOn F (fwdMapInv W t) H := fun w hw => ZhanGT4.extendFrom_eq_fwdMapInv hW hW0 ht hw
  have hDo : IsOpen (H \ fwdHull W t) := QuantumZipper.FwdHolo.isOpen_compl_fwdHull hW ht
  have hFD : MapsTo F H (H \ fwdHull W t) := fun w hw => by
    rw [hFeq hw]; exact QuantumZipper.RS.fwdMapInv_mem_compl_fwdHull hW hW0 ht hw
  have hFs : SurjOn F H (H \ fwdHull W t) := (isConformalBijection_fwdMapInv hW hW0 ht).2.surjOn.congr hFeq.symm
  have hFbd : MapsTo F (Hbar \ H) (frontier (H \ fwdHull W t)) := by
    intro w hw
    have him : w.im = 0 := le_antisymm (not_lt.1 hw.2) hw.1
    rw [hDo.frontier_eq]
    refine ⟨?_, hη.extendFrom_not_mem hW hW0 ht him⟩
    have : (𝓝[H] w).NeBot := mem_closure_iff_nhdsWithin_neBot.1 (by rw [closure_H]; exact hw.1)
    exact mem_closure_of_tendsto ((hη.hasBdryLimits hW hW0 ht).tendsto hw.1)
      (eventually_nhdsWithin_of_forall fun y hy => QuantumZipper.RS.fwdMapInv_mem_compl_fwdHull hW hW0 ht hy)
  have hFinf : Tendsto F (Bornology.cobounded ℂ ⊓ 𝓟 Hbar) (Bornology.cobounded ℂ) := by
    obtain ⟨C, hC⟩ := Lemma71P.exists_norm_extendFrom_sub_le' hη hW hW0 ht
    refine tendsto_norm_atTop_iff_cobounded.1 ?_
    have hn : Tendsto (fun w : ℂ => ‖w‖ - C) (Bornology.cobounded ℂ ⊓ 𝓟 Hbar) atTop :=
      tendsto_atTop_add_const_right _ _ (tendsto_norm_cobounded_atTop.mono_left inf_le_left)
    refine tendsto_atTop_mono' _ ?_ hn
    filter_upwards [mem_inf_of_right (mem_principal_self Hbar)] with w hw
    have h1 := hC w hw
    have h2 := norm_sub_norm_le w (F w)
    rw [norm_sub_rev] at h1
    linarith
  have hDE : Disjoint (H \ fwdHull W t) ({z : ℂ | z.im = 0} ∪ A) := by
    refine Set.disjoint_left.2 fun z hz hzE => ?_
    rcases hzE with h | h
    · exact (ne_of_gt (show 0 < z.im from hz.1)) h
    · apply hz.2
      rw [hη.2.2 t ht]
      exact ⟨hz.1, Or.inl (subset_closure h)⟩
  have hfr : frontier (H \ fwdHull W t) ⊆ {z : ℂ | z.im = 0} ∪ A := by
    rw [hη.2.2 t ht]
    have := frontier_H_diff_fillH_subset hAc.isBounded (A := A)
    rwa [hAc.isClosed.closure_eq] at this
  exact ⟨hDo, hFd, hFc, hFi, hFD, hFs, hFbd, hFinf, hDE, hfr⟩

/-- Trace points lie in `ℍ̄`: `η(s) = F̄_s(0)`. -/
theorem trace_mem_Hbar (hη : IsLoewnerTrace W η) (hW : Continuous W) (hW0 : W 0 = 0) {s : ℝ} (hs : 0 ≤ s) :
    η s ∈ Hbar := by
  rw [← ZhanGT4.extendFrom_zero_eq hη hW hW0 hs]
  exact Lemma71P.extendFrom_mem_Hbar hη hW hW0 hs (mem_Hbar_of_im_eq_zero (by simp))

/-- The middle chart points land on the trace prefix (`Lemma71P.mem_image_of_mid` in terms of `midL`, `midR`). -/
theorem mem_image_of_midL_midR (hη : IsLoewnerTrace W η) (hW : Continuous W) (hW0 : W 0 = 0) (ht : 0 ≤ t)
    {z : ℝ} (h1 : midL W t < z) (h2 : z < midR W t) : extendFrom H (fwdMapInv W t) z ∈ η '' Icc 0 t :=
  Lemma71P.mem_image_of_mid hη hW hW0 ht h1 h2

/-- **The trap for `F̄_t`** (`exists_trap` with `D = ℍ ∖ K_t`, `E = ℝ ∪ η([0, t])`). -/
theorem exists_trap_loewner (hη : IsLoewnerTrace W η) (hW : Continuous W) (hW0 : W 0 = 0) (ht : 0 ≤ t)
    {x y : ℝ} (hxy : x < y) (hxr : (extendFrom H (fwdMapInv W t) x).im = 0)
    (hyr : (extendFrom H (fwdMapInv W t) y).im = 0)
    (hne : extendFrom H (fwdMapInv W t) x ≠ extendFrom H (fwdMapInv W t) y) :
    ∃ I : Set ℂ, Bornology.IsBounded I ∧
      (∀ z : ℝ, x < z → z < y → extendFrom H (fwdMapInv W t) z ≠ extendFrom H (fwdMapInv W t) x →
        extendFrom H (fwdMapInv W t) z ≠ extendFrom H (fwdMapInv W t) y → extendFrom H (fwdMapInv W t) z ∈ I) ∧
      (∀ z : ℝ, z < x ∨ y < z → extendFrom H (fwdMapInv W t) z ∉ I) ∧
      (∀ S : Set ℂ, IsPreconnected S → S ⊆ {z : ℂ | z.im = 0} ∪ η '' Icc 0 t →
        extendFrom H (fwdMapInv W t) x ∉ S → extendFrom H (fwdMapInv W t) y ∉ S → ∀ w ∈ S, w ∈ I → S ⊆ I) := by
  obtain ⟨hDo, -, hFc, hFi, hFD, hFs, hFbd, hFinf, hDE, -⟩ := fibre_setting hη hW hW0 ht
  have hEH : {z : ℂ | z.im = 0} ∪ η '' Icc 0 t ⊆ Hbar := by
    rintro z (hz | ⟨s, hs, rfl⟩)
    · exact mem_Hbar_of_im_eq_zero hz
    · exact trace_mem_Hbar hη hW hW0 hs.1
  exact exists_trap hDo sdiff_subset hFc hFi hFD hFs hFbd hFinf hDE hEH hxy hxr hyr hne

/-- **Far real values.** Far to the left (right) of any bound, `F̄_t` takes real values off the trace prefix, below
(above) any given level: `F̄_t` moves points by a bounded amount, the prefix is bounded, and
`∂(ℍ ∖ K_t) ⊆ ℝ ∪ η([0, t])`. -/
theorem exists_far (hη : IsLoewnerTrace W η) (hW : Continuous W) (hW0 : W 0 = 0) (ht : 0 ≤ t) (c d : ℝ) :
    (∃ z : ℝ, z < c ∧ (extendFrom H (fwdMapInv W t) z).im = 0 ∧ extendFrom H (fwdMapInv W t) z ∉ η '' Icc 0 t ∧
      (extendFrom H (fwdMapInv W t) z).re < d) ∧
    (∃ z : ℝ, c < z ∧ (extendFrom H (fwdMapInv W t) z).im = 0 ∧ extendFrom H (fwdMapInv W t) z ∉ η '' Icc 0 t ∧
      d < (extendFrom H (fwdMapInv W t) z).re) := by
  obtain ⟨-, -, -, -, -, -, hFbd, -, -, hfr⟩ := fibre_setting hη hW hW0 ht
  obtain ⟨C, hC⟩ := Lemma71P.exists_norm_extendFrom_sub_le' hη hW hW0 ht
  obtain ⟨M, hM⟩ := (hη.isCompact_image t).isBounded.exists_norm_le
  have hreal : ∀ z : ℝ, M < ‖extendFrom H (fwdMapInv W t) z‖ →
      (extendFrom H (fwdMapInv W t) z).im = 0 ∧ extendFrom H (fwdMapInv W t) z ∉ η '' Icc 0 t := by
    intro z hz
    have hnot : extendFrom H (fwdMapInv W t) z ∉ η '' Icc 0 t := fun h => absurd (hM _ h) (not_le.2 hz)
    have hzb : ((z : ℝ) : ℂ) ∈ Hbar \ H := ⟨mem_Hbar_of_im_eq_zero (by simp), fun h => by
      have : (0 : ℝ) < ((z : ℝ) : ℂ).im := h
      simp at this⟩
    rcases hfr (hFbd hzb) with h | h
    · exact ⟨h, hnot⟩
    · exact absurd h hnot
  have hre : ∀ z : ℝ, |(extendFrom H (fwdMapInv W t) z).re - z| ≤ C := fun z => by
    have h1 := hC z (mem_Hbar_of_im_eq_zero (by simp))
    have h2 := Complex.abs_re_le_norm (extendFrom H (fwdMapInv W t) z - z)
    rw [sub_re, ofReal_re] at h2
    linarith
  have hnorm : ∀ z : ℝ, |(extendFrom H (fwdMapInv W t) z).re| ≤ ‖extendFrom H (fwdMapInv W t) z‖ :=
    fun z => Complex.abs_re_le_norm _
  refine ⟨?_, ?_⟩
  · obtain ⟨z, hz⟩ : ∃ z : ℝ, z = -(|c| + |d| + |C| + |M| + 1) := ⟨_, rfl⟩
    have ha := abs_le.1 (hre z)
    have hn := hnorm z
    have hneg := neg_le_abs (extendFrom H (fwdMapInv W t) z).re
    have hM' : M < ‖extendFrom H (fwdMapInv W t) z‖ := by
      linarith [le_abs_self C, le_abs_self M, abs_nonneg c, abs_nonneg d]
    obtain ⟨him, hnot⟩ := hreal z hM'
    refine ⟨z, by linarith [neg_abs_le c, abs_nonneg d, abs_nonneg C, abs_nonneg M], him, hnot, ?_⟩
    linarith [neg_abs_le d, le_abs_self C, abs_nonneg c, abs_nonneg M]
  · obtain ⟨z, hz⟩ : ∃ z : ℝ, z = |c| + |d| + |C| + |M| + 1 := ⟨_, rfl⟩
    have ha := abs_le.1 (hre z)
    have hn := hnorm z
    have hpos := le_abs_self (extendFrom H (fwdMapInv W t) z).re
    have hM' : M < ‖extendFrom H (fwdMapInv W t) z‖ := by
      linarith [le_abs_self C, le_abs_self M, abs_nonneg c, abs_nonneg d]
    obtain ⟨him, hnot⟩ := hreal z hM'
    refine ⟨z, by linarith [le_abs_self c, abs_nonneg d, abs_nonneg C, abs_nonneg M], him, hnot, ?_⟩
    linarith [le_abs_self d, le_abs_self C, abs_nonneg c, abs_nonneg M]

/-- **The trap contradiction.** Let `a < b` with `F̄_t(a) ≠ F̄_t(b)` real, each of them off the trace prefix or equal
to the trace point `η(v)`, and `0 ∉ [a, b]`. Let `z₀ ∈ (a, b)` with `F̄_t(z₀)` on the prefix but not `η(v)`, and let
`R` be an unbounded preconnected set of real points through `0` containing no endpoint value other than `0`. Then
`False`: with `F̄_t(z₀) = η(w)`, the arc `η([w, t])` (if `w > v`) joins the trap to the tip `η(t) = F̄_t(0)` outside it,
and `η([0, w]) ∪ R` (if `w < v`) is trapped although unbounded. -/
theorem false_of_trap (hη : IsLoewnerTrace W η) (hW : Continuous W) (hW0 : W 0 = 0) (ht : 0 ≤ t)
    (hi : InjOn η (Icc 0 t)) {a b : ℝ} (hab : a < b) (har : (extendFrom H (fwdMapInv W t) a).im = 0)
    (hbr : (extendFrom H (fwdMapInv W t) b).im = 0)
    (hne : extendFrom H (fwdMapInv W t) a ≠ extendFrom H (fwdMapInv W t) b) {v : ℝ} (hv : v ∈ Icc 0 t)
    (hPa : extendFrom H (fwdMapInv W t) a ∉ η '' Icc 0 t ∨ extendFrom H (fwdMapInv W t) a = η v)
    (hPb : extendFrom H (fwdMapInv W t) b ∉ η '' Icc 0 t ∨ extendFrom H (fwdMapInv W t) b = η v)
    (h0 : 0 < a ∨ b < 0) {z₀ : ℝ} (hz₀ : z₀ ∈ Ioo a b)
    (hz₀η : extendFrom H (fwdMapInv W t) z₀ ∈ η '' Icc 0 t) (hz₀v : extendFrom H (fwdMapInv W t) z₀ ≠ η v)
    {R : Set ℂ} (hRc : IsPreconnected R) (hRb : ¬ Bornology.IsBounded R) (hRr : ∀ z ∈ R, z.im = 0)
    (h0R : (0 : ℂ) ∈ R)
    (hRP : ∀ z ∈ R, z = extendFrom H (fwdMapInv W t) a ∨ z = extendFrom H (fwdMapInv W t) b → z = 0) :
    False := by
  obtain ⟨I, hIb, hIin, hIout, hIS⟩ := exists_trap_loewner hη hW hW0 ht hab har hbr hne
  -- trace points at times other than `v` avoid both endpoint values
  have hoffP : ∀ P : ℂ, (P ∉ η '' Icc 0 t ∨ P = η v) → ∀ s ∈ Icc 0 t, s ≠ v → η s ≠ P := by
    rintro P (hP | rfl) s hs hsv he
    · exact hP ⟨s, hs, he⟩
    · exact hsv (hi hs hv he)
  have hneP : ∀ P : ℂ, (P ∉ η '' Icc 0 t ∨ P = η v) → extendFrom H (fwdMapInv W t) z₀ ≠ P := by
    rintro P (hP | rfl) h
    · exact hP (h ▸ hz₀η)
    · exact hz₀v h
  have hz₀I := hIin z₀ hz₀.1 hz₀.2 (hneP _ hPa) (hneP _ hPb)
  have htip : η t ∉ I := by
    have h := hIout 0 h0
    rwa [ofReal_zero, ZhanGT4.extendFrom_zero_eq hη hW hW0 ht] at h
  obtain ⟨w, hw, hwe⟩ := hz₀η
  have hwv : w ≠ v := fun h => hz₀v (by rw [← hwe, h])
  have hηI : η w ∈ I := hwe ▸ hz₀I
  rcases lt_or_gt_of_ne hwv with hlt | hgt
  · -- `w < v`: the prefix `η([0, w])` and the real set `R` are trapped, but `R` is unbounded
    have hv0 : 0 < v := lt_of_le_of_lt hw.1 hlt
    have hS : IsPreconnected (η '' Icc 0 w ∪ R) :=
      IsPreconnected.union 0 ⟨0, ⟨le_rfl, hw.1⟩, hη.1⟩ h0R
        (isPreconnected_Icc.image η (hη.2.1.mono fun s hs => hs.1)) hRc
    have hSE : η '' Icc 0 w ∪ R ⊆ {z : ℂ | z.im = 0} ∪ η '' Icc 0 t := by
      rintro z (⟨s, hs, rfl⟩ | hz)
      · exact Or.inr ⟨s, ⟨hs.1, hs.2.trans hw.2⟩, rfl⟩
      · exact Or.inl (hRr z hz)
    have hnotS : ∀ P : ℂ, (P ∉ η '' Icc 0 t ∨ P = η v) →
        (P = extendFrom H (fwdMapInv W t) a ∨ P = extendFrom H (fwdMapInv W t) b) → P ∉ η '' Icc 0 w ∪ R := by
      rintro P hP hPab (⟨s, hs, he⟩ | hPR)
      · exact hoffP P hP s ⟨hs.1, hs.2.trans hw.2⟩ (ne_of_lt (lt_of_le_of_lt hs.2 hlt)) he
      · have hP0 : P = 0 := hRP P hPR hPab
        exact hoffP P hP 0 ⟨le_rfl, ht⟩ (ne_of_lt hv0) (by rw [hη.1, hP0])
    have hsub := hIS _ hS hSE (hnotS _ hPa (Or.inl rfl)) (hnotS _ hPb (Or.inr rfl)) (η w)
      (Or.inl ⟨w, ⟨hw.1, le_rfl⟩, rfl⟩) hηI
    exact hRb (hIb.subset (subset_union_right.trans hsub))
  · -- `v < w`: the arc `η([w, t])` is trapped, but the tip is not
    have hS : IsPreconnected (η '' Icc w t) :=
      isPreconnected_Icc.image η (hη.2.1.mono fun s hs => hw.1.trans hs.1)
    have hSE : η '' Icc w t ⊆ {z : ℂ | z.im = 0} ∪ η '' Icc 0 t := by
      rintro z ⟨s, hs, rfl⟩
      exact Or.inr ⟨s, ⟨hw.1.trans hs.1, hs.2⟩, rfl⟩
    have hnotS : ∀ P : ℂ, (P ∉ η '' Icc 0 t ∨ P = η v) → P ∉ η '' Icc w t := by
      rintro P hP ⟨s, hs, he⟩
      exact hoffP P hP s ⟨hw.1.trans hs.1, hs.2⟩ (ne_of_gt (lt_of_lt_of_le hgt hs.1)) he
    have hsub := hIS _ hS hSE (hnotS _ hPa) (hnotS _ hPb) (η w) ⟨w, ⟨le_rfl, hw.2⟩, rfl⟩ hηI
    exact htip (hsub ⟨t, ⟨hw.2, le_rfl⟩, rfl⟩)

/-- The real half-lines `[0, ∞)` and `(−∞, 0]` are unbounded. -/
theorem not_isBounded_ofReal_image {J : Set ℝ} (hJ : ∀ B : ℝ, ∃ r ∈ J, B < |r|) :
    ¬ Bornology.IsBounded ((fun r : ℝ => (r : ℂ)) '' J) := by
  intro hb
  obtain ⟨B, hB⟩ := hb.exists_norm_le
  obtain ⟨r, hr, hBr⟩ := hJ B
  have := hB _ ⟨r, hr, rfl⟩
  rw [norm_real, Real.norm_eq_abs] at this
  linarith

/-- **Left middle interval.** `F̄_t` takes no real value `≤ 0` on `(L_t − W_t, 0)`. -/
theorem not_real_nonpos_left (hη : IsLoewnerTrace W η) (hW : Continuous W) (hW0 : W 0 = 0) (ht : 0 ≤ t)
    (hi : InjOn η (Icc 0 t)) {x : ℝ} (hxL : midL W t < x) (hx0 : x < 0) :
    ¬ ((extendFrom H (fwdMapInv W t) x).im = 0 ∧ (extendFrom H (fwdMapInv W t) x).re ≤ 0) := by
  rintro ⟨him, hre⟩
  obtain ⟨-, hFd, hFc, hFi, -⟩ := fibre_setting hη hW hW0 ht
  have hR0 : 0 ≤ midR W t := Lemma71P.midR_nonneg hW ht
  obtain ⟨v, hv, hve⟩ := mem_image_of_midL_midR hη hW hW0 ht hxL (by linarith)
  obtain ⟨⟨z₁, hz₁, hz₁r, hz₁η, hz₁re⟩, -⟩ :=
    exists_far hη hW hW0 ht (midL W t) (extendFrom H (fwdMapInv W t) x).re
  obtain ⟨z₀, hz₀, hz₀ne⟩ := exists_ne_of_injOn hFd hFc hFi hxL (extendFrom H (fwdMapInv W t) x)
  have hne : extendFrom H (fwdMapInv W t) z₁ ≠ extendFrom H (fwdMapInv W t) x := fun h => by
    rw [h] at hz₁re; exact lt_irrefl _ hz₁re
  refine false_of_trap hη hW hW0 ht hi (a := z₁) (b := x) (by linarith) hz₁r him hne hv (Or.inl hz₁η)
    (Or.inr hve.symm) (Or.inr hx0) (z₀ := z₀) ⟨by linarith [hz₀.1], hz₀.2⟩
    (mem_image_of_midL_midR hη hW hW0 ht hz₀.1 (by linarith [hz₀.2])) (hve ▸ hz₀ne)
    (R := (fun r : ℝ => (r : ℂ)) '' Ici 0) (isPreconnected_Ici.image _ continuous_ofReal.continuousOn)
    (not_isBounded_ofReal_image fun B => ⟨|B| + 1, mem_Ici.2 (by positivity), by
      rw [abs_of_pos (by positivity)]; linarith [le_abs_self B]⟩)
    (by rintro _ ⟨r, -, rfl⟩; simp) ⟨0, mem_Ici.2 le_rfl, by simp⟩ ?_
  rintro _ ⟨r, hr, rfl⟩ (h | h)
  · exfalso
    have h' := congrArg Complex.re h
    rw [ofReal_re] at h'
    linarith [mem_Ici.1 hr]
  · have h' := congrArg Complex.re h
    rw [ofReal_re] at h'
    show ((r : ℝ) : ℂ) = 0
    rw [le_antisymm (by linarith) (mem_Ici.1 hr), ofReal_zero]

/-- **Right middle interval.** `F̄_t` takes no real value `≥ 0` on `(0, R_t − W_t)`. -/
theorem not_real_nonneg_right (hη : IsLoewnerTrace W η) (hW : Continuous W) (hW0 : W 0 = 0) (ht : 0 ≤ t)
    (hi : InjOn η (Icc 0 t)) {x : ℝ} (hx0 : 0 < x) (hxR : x < midR W t) :
    ¬ ((extendFrom H (fwdMapInv W t) x).im = 0 ∧ 0 ≤ (extendFrom H (fwdMapInv W t) x).re) := by
  rintro ⟨him, hre⟩
  obtain ⟨-, hFd, hFc, hFi, -⟩ := fibre_setting hη hW hW0 ht
  have hL0 : midL W t ≤ 0 := Lemma71P.midL_nonpos hW ht
  obtain ⟨v, hv, hve⟩ := mem_image_of_midL_midR hη hW hW0 ht (by linarith) hxR
  obtain ⟨-, ⟨z₁, hz₁, hz₁r, hz₁η, hz₁re⟩⟩ :=
    exists_far hη hW hW0 ht (midR W t) (extendFrom H (fwdMapInv W t) x).re
  obtain ⟨z₀, hz₀, hz₀ne⟩ := exists_ne_of_injOn hFd hFc hFi hxR (extendFrom H (fwdMapInv W t) x)
  have hne : extendFrom H (fwdMapInv W t) x ≠ extendFrom H (fwdMapInv W t) z₁ := fun h => by
    rw [h] at hz₁re; exact lt_irrefl _ hz₁re
  refine false_of_trap hη hW hW0 ht hi (a := x) (b := z₁) (hxR.trans hz₁) him hz₁r hne hv (Or.inr hve.symm)
    (Or.inl hz₁η) (Or.inl hx0) (z₀ := z₀) ⟨hz₀.1, by linarith [hz₀.2]⟩
    (mem_image_of_midL_midR hη hW hW0 ht (by linarith [hz₀.1]) hz₀.2) (hve ▸ hz₀ne)
    (R := (fun r : ℝ => (r : ℂ)) '' Iic 0) (isPreconnected_Iic.image _ continuous_ofReal.continuousOn)
    (not_isBounded_ofReal_image fun B => ⟨-(|B| + 1), mem_Iic.2 (by linarith [abs_nonneg B]), by
      rw [abs_neg, abs_of_pos (by positivity)]; linarith [le_abs_self B]⟩)
    (by rintro _ ⟨r, -, rfl⟩; simp) ⟨0, mem_Iic.2 le_rfl, by simp⟩ ?_
  rintro _ ⟨r, hr, rfl⟩ (h | h)
  · have h' := congrArg Complex.re h
    rw [ofReal_re] at h'
    show ((r : ℝ) : ℂ) = 0
    rw [le_antisymm (mem_Iic.1 hr) (by linarith), ofReal_zero]
  · exfalso
    have h' := congrArg Complex.re h
    rw [ofReal_re] at h'
    linarith [mem_Iic.1 hr]

/-- **`MidRealOffStatement`** (PROVE-LEMMA71P's named input): for a continuous driver `W` (`W 0 = 0`) with a Loewner
trace `η` injective on `[0, t]`, the boundary extension `F̄_t` of `f_t⁻¹` takes no real value `≤ 0` on the left middle
interval `(L_t − W_t, 0)` and no real value `≥ 0` on the right middle interval `(0, R_t − W_t)`. -/
theorem midRealOffStatement : MidRealOffStatement := fun _ _ _ hW hW0 ht hη hi =>
  ⟨fun _ hxL hx0 => not_real_nonpos_left hη hW hW0 ht hi hxL hx0,
    fun _ hx0 hxR => not_real_nonneg_right hη hW hW0 ht hi hx0 hxR⟩

end Loewner

end InteractingSLE.Sec7.Lemma71T

end
