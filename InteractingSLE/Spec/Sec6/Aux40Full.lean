/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec6.Aux36FaceFresh
import InteractingSLE.Spec.Sec6.Aux37

/-!
# The reverse-contained Jordan pocket: (JP1)–(JP2), the central face, and the gap equalities

Specification §6.2, **Aux.** lemmas 34, 36, 37, 39–41 (`source/spec/p145-192.md` L869–L905,
`source/spec/p193-240.md` L36–L265) and ruling R41's note
(`source/external/AstraIG1/ig1_ztip_elimination.txt` §1.1–1.2, Propositions 1.5–1.6).

This file states the pathwise hypotheses of Aux. lemmas 39–41 as one predicate
`IsReversePocket` (finite junction `x₀ = α₁(0) = α₂(0) ∈ ℍ`; pocket start `y₀ = α₁(1) = α₂(1)` an
interior point or the original seed `0`):

* `η` is a continuous Loewner trace of a continuous driver `W` with `W 0 = 0`;
* `C` is an open, connected, bounded set with `∂C = α₁([0, 1]) ∪ α₂([0, 1])`, the two incoming
  sides being continuous injective paths in `ℍ` (except possibly at `y₀ = 0`) from `x₀` to `y₀`,
  whose open subarcs are disjoint
  (Aux. lemma 34: "a complementary component whose boundary consists of one subarc of each path,
  from a common point `x₀` to a common point `y₀` … these two open subarcs are disjoint");
* both sides are first visited in reverse order (`R16.IsReverseVisitOrder`), and so is the earlier
  part `β` of the first incoming flow line, a proper simple path in `ℍ` from `x₀` toward the
  original target (`∞`): a point of `β` is visited only after `x₀`;
* `τ = T(y₀)` and `σ = T(x₀)` are the first-visit times.

From these premises the file proves (JP1) (`IsReversePocket.mem_Ioo_of_mem`), (JP2) and the chart
facts at every time `r ∈ [τ, σ)` (`IsReversePocket.chart`), the common-contact order of the incoming
pieces, the central face `F_r = {w ∈ ℍ : f̄_r(w) ∈ C}` as the inner side of a Jordan curve in `ℍ̄`
(`IsReversePocket.exists_face`), and the gap equalities of Propositions 1.5–1.6
(`IsReversePocket.gap_eq`), under **Aux. lemma 37's conclusion** (attachment constancy on every
interval avoiding `C`, `AttachmentConstancy`), the named input whose proof needs the field
comparison of Aux. lemma 37.
-/

set_option autoImplicit false

noncomputable section

open Complex Set Metric Filter Topology Bornology

open QuantumZipper (H Hbar fwdHull fwdMap fwdMapInv)
open InteractingSLE.YuanSimpleApprox (trMap)

namespace InteractingSLE.Sec6

variable {W : ℝ → ℝ} {η : ℝ → ℂ}

/-! ### The pocket hypotheses -/

/-- **The pathwise hypotheses of Aux. lemmas 39–41** for a reverse-contained two-arc Jordan pocket
with finite junction `x₀ = α₁(0) = α₂(0) ∈ ℍ` and start `y₀ = α₁(1) = α₂(1)`, an interior point or
the original seed `0` (the flow lines meet `ℝ` only at their endpoints; Specification
pp. 189–206; Aux. lemma 34's configuration with Aux. lemma 37's first-visit times
`τ = T(y₀)`, `σ = T(x₀)`). `β` is the earlier part of the first incoming flow line, from `x₀`
toward the original target `∞`. -/
structure IsReversePocket (W : ℝ → ℝ) (η : ℝ → ℂ) (C : Set ℂ) (α₁ α₂ β : ℝ → ℂ) (τ σ : ℝ) :
    Prop where
  trace : IsLoewnerTrace W η
  continuous_W : Continuous W
  W_zero : W 0 = 0
  isOpen : IsOpen C
  isConnected : IsConnected C
  isBounded : IsBounded C
  frontier_eq : frontier C = α₁ '' Icc 0 1 ∪ α₂ '' Icc 0 1
  cont₁ : ContinuousOn α₁ (Icc 0 1)
  cont₂ : ContinuousOn α₂ (Icc 0 1)
  inj₁ : InjOn α₁ (Icc 0 1)
  inj₂ : InjOn α₂ (Icc 0 1)
  junction : α₂ 0 = α₁ 0
  seed : α₂ 1 = α₁ 1
  sides : ∀ v ∈ Ioo (0 : ℝ) 1, ∀ v' ∈ Ioo (0 : ℝ) 1, α₁ v ≠ α₂ v'
  mem_H₁ : ∀ v ∈ Ico (0 : ℝ) 1, α₁ v ∈ H
  mem_H₂ : ∀ v ∈ Ico (0 : ℝ) 1, α₂ v ∈ H
  mem_y : α₁ 1 ∈ H ∨ α₁ 1 = 0
  rev₁ : R16.IsReverseVisitOrder α₁ fun t => η '' Icc 0 t
  rev₂ : R16.IsReverseVisitOrder α₂ fun t => η '' Icc 0 t
  cont_β : ContinuousOn β (Ici 0)
  inj_β : InjOn β (Ici 0)
  β_zero : β 0 = α₁ 0
  tendsto_β : Tendsto (fun t => ‖β t‖) atTop atTop
  mem_H_β : ∀ t ∈ Ici (0 : ℝ), β t ∈ H
  rev_β : ∀ t : ℝ, ∀ r ∈ Ici (0 : ℝ), β r ∈ η '' Icc 0 t → α₁ 0 ∈ η '' Icc 0 t
  nonneg : 0 ≤ τ
  nonneg_σ : 0 ≤ σ
  first_y : η τ = α₁ 1
  fresh_y : α₁ 1 ∉ η '' Ico 0 τ
  first_x : η σ = α₁ 0
  fresh_x : α₁ 0 ∉ η '' Ico 0 σ

/-- **Aux. lemma 37's conclusion** (the named input of this file): the first-visit attachments
`u_i(t) = min {u : α_i(u) ∈ R_t}` are constant on every interval `[a, b] ⊆ [τ, σ)` on which the
trace avoids `C` (Specification p. 197: "for every interval `[a, b] ⊂ [τ, σ)` on which
`η'([a, b]) ∩ C = ∅`, the two functions `u_i` are constant on `[a, b]`"). Its proof uses the field
comparison of Aux. lemma 37 (flat clock, germ identification at the first-visit times), which needs
the marked flow-line couplings of Aux. lemmas 32–35. -/
def AttachmentConstancy (η : ℝ → ℂ) (C : Set ℂ) (α₁ α₂ : ℝ → ℂ) (τ σ : ℝ) : Prop :=
  ∀ a b : ℝ, τ ≤ a → a ≤ b → b < σ → (∀ t ∈ Icc a b, η t ∉ C) →
    firstVisit (fun t => η '' Icc 0 t) α₁ b = firstVisit (fun t => η '' Icc 0 t) α₁ a ∧
      firstVisit (fun t => η '' Icc 0 t) α₂ b = firstVisit (fun t => η '' Icc 0 t) α₂ a

/-! ### Elementary topology -/

/-- A preconnected set meeting an open set `U` and missing its frontier lies in `U`. -/
theorem subset_of_isPreconnected_of_disjoint_frontier {P U : Set ℂ} (hP : IsPreconnected P)
    (hU : IsOpen U) (hne : (P ∩ U).Nonempty) (hfr : Disjoint P (frontier U)) : P ⊆ U :=
  hP.subset_of_closure_inter_subset hU hne fun x ⟨hxc, hxP⟩ => by
    by_contra hxU
    exact Set.disjoint_left.1 hfr hxP ⟨hxc, by rwa [hU.interior_eq]⟩

/-- An unbounded preconnected subset of `ℍ` avoiding `R_r = η([0, r])` lies in `D_r = ℍ \ K_r`. -/
theorem subset_domain_of_not_isBounded (hη : IsLoewnerTrace W η) {r : ℝ} (hr : 0 ≤ r)
    {S : Set ℂ} (hS : IsPreconnected S) (hSH : S ⊆ H) (hSR : Disjoint S (η '' Icc 0 r))
    (hSb : ¬ IsBounded S) : S ⊆ H \ fwdHull W r := by
  have hRc : IsCompact (η '' Icc 0 r) :=
    isCompact_Icc.image_of_continuousOn (hη.2.1.mono fun t ht => ht.1)
  obtain ⟨ρ, hρ, hρR⟩ := exists_closure_subset_ball hRc.isBounded
  have hK : fwdHull W r ⊆ ball 0 ρ := by rw [hη.2.2 r hr]; exact fillH_subset_ball hρ hρR
  obtain ⟨p, hpS, hpρ⟩ : ∃ p ∈ S, p ∉ ball (0 : ℂ) ρ := by
    by_contra h
    push Not at h
    exact hSb (isBounded_ball.subset fun p hp => h p hp)
  exact subset_domain_of_isPreconnected hη hr hS hSH hSR hpS ⟨hSH hpS, fun h => hpρ (hK h)⟩

/-- `D_r = ℍ \ K_r` is unbounded. -/
theorem not_isBounded_domain (hη : IsLoewnerTrace W η) {r : ℝ} (hr : 0 ≤ r) :
    ¬ IsBounded (H \ fwdHull W r) := by
  have hRc : IsCompact (η '' Icc 0 r) :=
    isCompact_Icc.image_of_continuousOn (hη.2.1.mono fun t ht => ht.1)
  obtain ⟨ρ, hρ, hρR⟩ := exists_closure_subset_ball hRc.isBounded
  have hK : fwdHull W r ⊆ ball 0 ρ := by rw [hη.2.2 r hr]; exact fillH_subset_ball hρ hρR
  intro hb
  have hH : H ⊆ (H \ fwdHull W r) ∪ ball 0 ρ := fun z hz => by
    by_cases h : z ∈ fwdHull W r
    · exact Or.inr (hK h)
    · exact Or.inl ⟨hz, h⟩
  exact not_isBounded_setOf_lt_im 0 ((hb.union isBounded_ball).subset hH)

/-- The tip lies in the closure of the current domain: `η(t) ∈ closure D_t`. -/
theorem trace_mem_closure_domain (hη : IsLoewnerTrace W η) (hW : Continuous W) (hW0 : W 0 = 0)
    {t : ℝ} (ht : 0 ≤ t) : η t ∈ closure (H \ fwdHull W t) := by
  rw [← traceMapOut_trMap_zero hη hW hW0 ht le_rfl]
  exact trMap_zero_mem_closure hη hW hW0 ht
    (YuanSimpleApprox.trMap_zero_mem_Hbar hη hW hW0 ht le_rfl)

/-- A point of `ℍ` visited by time `r` is in `K_r`. -/
theorem mem_fwdHull_of_mem_trace (hη : IsLoewnerTrace W η) {r : ℝ} (hr : 0 ≤ r) {p : ℂ}
    (hpH : p ∈ H) (hp : p ∈ η '' Icc 0 r) : p ∈ fwdHull W r := by
  by_contra h
  exact notMem_domain_of_mem_trace hη hr hp ⟨hpH, h⟩

/-- A first-visit time: if `p ∉ η([0, T))` and `p ∈ η([0, t])`, then `T ≤ t`. -/
theorem le_of_fresh {p : ℂ} {T t : ℝ} (hT : p ∉ η '' Ico 0 T) (ht : p ∈ η '' Icc 0 t) : T ≤ t := by
  obtain ⟨t', ht', rfl⟩ := ht
  by_contra h
  push Not at h
  exact hT ⟨t', ⟨ht'.1, ht'.2.trans_lt h⟩, rfl⟩

namespace IsReversePocket

variable {C : Set ℂ} {α₁ α₂ β : ℝ → ℂ} {τ σ : ℝ}

/-- The data of one incoming side, uniformly for both sides. -/
theorem arm (hP : IsReversePocket W η C α₁ α₂ β τ σ) {α : ℝ → ℂ} (hα : α = α₁ ∨ α = α₂) :
    ContinuousOn α (Icc 0 1) ∧ InjOn α (Icc 0 1) ∧ α 0 = α₁ 0 ∧ α 1 = α₁ 1 ∧
      (∀ v ∈ Ico (0 : ℝ) 1, α v ∈ H) ∧ R16.IsReverseVisitOrder α fun t => η '' Icc 0 t := by
  rcases hα with rfl | rfl
  · exact ⟨hP.cont₁, hP.inj₁, rfl, rfl, hP.mem_H₁, hP.rev₁⟩
  · exact ⟨hP.cont₂, hP.inj₂, hP.junction, hP.seed, hP.mem_H₂, hP.rev₂⟩

theorem x_ne_y (hP : IsReversePocket W η C α₁ α₂ β τ σ) : α₁ 0 ≠ α₁ 1 := fun h =>
  zero_ne_one (hP.inj₁ ⟨le_rfl, zero_le_one⟩ ⟨zero_le_one, le_rfl⟩ h)

theorem y_mem_Hbar (hP : IsReversePocket W η C α₁ α₂ β τ σ) : α₁ 1 ∈ Hbar := by
  rcases hP.mem_y with h | h
  · exact QuantumZipper.H_subset_Hbar h
  · rw [h]; show (0 : ℝ) ≤ (0 : ℂ).im; simp

/-- A boundary point of the pocket other than `y₀` lies in `ℍ`. -/
theorem mem_H_of_mem_frontier (hP : IsReversePocket W η C α₁ α₂ β τ σ) {z : ℂ}
    (hz : z ∈ frontier C) (hzy : z ≠ α₁ 1) : z ∈ H := by
  rw [hP.frontier_eq] at hz
  rcases hz with ⟨v, hv, rfl⟩ | ⟨v, hv, rfl⟩
  · rcases eq_or_lt_of_le hv.2 with h | h
    · exact absurd (by rw [h]) hzy
    · exact hP.mem_H₁ v ⟨hv.1, h⟩
  · rcases eq_or_lt_of_le hv.2 with h | h
    · exact absurd (by rw [h, hP.seed]) hzy
    · exact hP.mem_H₂ v ⟨hv.1, h⟩

theorem frontier_subset_Hbar (hP : IsReversePocket W η C α₁ α₂ β τ σ) : frontier C ⊆ Hbar :=
  fun z hz => by
    by_cases hzy : z = α₁ 1
    · rw [hzy]; exact hP.y_mem_Hbar
    · exact QuantumZipper.H_subset_Hbar (hP.mem_H_of_mem_frontier hz hzy)

/-- The pocket lies in `ℍ`. -/
theorem subset_H (hP : IsReversePocket W η C α₁ α₂ β τ σ) : C ⊆ H := by
  -- the open lower half-plane misses `C`
  have hL : ∀ w ∈ C, ¬ w.im < 0 := by
    intro w hw hwL
    have hsub := subset_of_isPreconnected_of_disjoint_frontier isPreconnected_lowerHalf
      hP.isOpen ⟨w, hwL, hw⟩ (Set.disjoint_left.2 fun w' hw' hwf => by
        have : (0 : ℝ) ≤ w'.im := hP.frontier_subset_Hbar hwf
        exact absurd hw' (not_lt.2 this))
    exact lowerHalf_not_isBounded (hP.isBounded.subset hsub)
  intro z hz
  show 0 < z.im
  by_contra hle
  push Not at hle
  obtain ⟨ε, hε, hεC⟩ := Metric.isOpen_iff.1 hP.isOpen z hz
  have hw : z - ((ε / 2 : ℝ) : ℂ) * I ∈ C := hεC (by
    rw [mem_ball, dist_eq, sub_sub_cancel_left, norm_neg, norm_mul, norm_I, mul_one, norm_real,
      Real.norm_of_nonneg (by positivity)]
    linarith)
  refine hL _ hw ?_
  simp only [sub_im, mul_im, ofReal_re, I_im, ofReal_im, I_re, mul_zero, add_zero, mul_one]
  linarith

/-- A visited `x₀` forces both whole sides to be visited (reverse order). -/
theorem mem_of_x_mem (hP : IsReversePocket W η C α₁ α₂ β τ σ) {t : ℝ}
    (h : α₁ 0 ∈ η '' Icc 0 t) {α : ℝ → ℂ} (hα : α = α₁ ∨ α = α₂) {v : ℝ}
    (hv : v ∈ Icc (0 : ℝ) 1) : α v ∈ η '' Icc 0 t := by
  obtain ⟨-, -, h0, -, -, hrev⟩ := hP.arm hα
  exact hrev t 0 ⟨le_rfl, zero_le_one⟩ v hv hv.1 (h0 ▸ h)

/-- A visited point of a side forces `y₀` to be visited (reverse order). -/
theorem y_mem_of_mem (hP : IsReversePocket W η C α₁ α₂ β τ σ) {t : ℝ} {α : ℝ → ℂ}
    (hα : α = α₁ ∨ α = α₂) {v : ℝ} (hv : v ∈ Icc (0 : ℝ) 1) (h : α v ∈ η '' Icc 0 t) :
    α₁ 1 ∈ η '' Icc 0 t := by
  obtain ⟨-, -, -, h1, -, hrev⟩ := hP.arm hα
  exact h1 ▸ hrev t v hv 1 ⟨zero_le_one, le_rfl⟩ hv.2 h

theorem y_mem_of_mem_frontier (hP : IsReversePocket W η C α₁ α₂ β τ σ) {t : ℝ} {z : ℂ}
    (hz : z ∈ frontier C) (hzt : z ∈ η '' Icc 0 t) : α₁ 1 ∈ η '' Icc 0 t := by
  rw [hP.frontier_eq] at hz
  rcases hz with ⟨v, hv, rfl⟩ | ⟨v, hv, rfl⟩
  exacts [hP.y_mem_of_mem (Or.inl rfl) hv hzt, hP.y_mem_of_mem (Or.inr rfl) hv hzt]

theorem τ_le (hP : IsReversePocket W η C α₁ α₂ β τ σ) {t : ℝ} (h : α₁ 1 ∈ η '' Icc 0 t) :
    τ ≤ t := le_of_fresh hP.fresh_y h

theorem σ_le (hP : IsReversePocket W η C α₁ α₂ β τ σ) {t : ℝ} (h : α₁ 0 ∈ η '' Icc 0 t) :
    σ ≤ t := le_of_fresh hP.fresh_x h

theorem τ_lt_σ (hP : IsReversePocket W η C α₁ α₂ β τ σ) : τ < σ := by
  have hx : α₁ 0 ∈ η '' Icc 0 σ := ⟨σ, ⟨hP.nonneg_σ, le_rfl⟩, hP.first_x⟩
  refine lt_of_le_of_ne (hP.τ_le (hP.mem_of_x_mem hx (Or.inl rfl) ⟨zero_le_one, le_rfl⟩)) ?_
  intro h
  exact hP.x_ne_y (hP.first_x.symm.trans (h ▸ hP.first_y))

/-- A fresh visit to `∂C` at a positive time is a point of `ℍ` (the seed `0` is visited at time
`0`). -/
theorem mem_H_of_fresh (hP : IsReversePocket W η C α₁ α₂ β τ σ) {a : ℝ} (ha0 : 0 < a)
    (hfr : η a ∈ frontier C) (hfresh : η a ∉ η '' Ico 0 a) : η a ∈ H := by
  by_cases hy : η a = α₁ 1
  · rcases hP.mem_y with h | h
    · rwa [hy]
    · exact absurd ⟨0, ⟨le_rfl, ha0⟩, by rw [hP.trace.1, hy, h]⟩ hfresh
  · exact hP.mem_H_of_mem_frontier hfr hy

theorem isClosed_range (hP : IsReversePocket W η C α₁ α₂ β τ σ) {t : ℝ} :
    IsClosed (η '' Icc 0 t) :=
  (isCompact_Icc.image_of_continuousOn (hP.trace.2.1.mono fun _ hs => hs.1)).isClosed

/-- **(JP1)**: the trace visits `C` only strictly between `τ = T(y₀)` and `σ = T(x₀)`
(Specification p. 189). -/
theorem mem_Ioo_of_mem (hP : IsReversePocket W η C α₁ α₂ β τ σ) {t : ℝ} (ht : 0 ≤ t)
    (htC : η t ∈ C) : t ∈ Ioo τ σ := by
  have hη := hP.trace
  refine ⟨?_, ?_⟩
  · -- the path `η([0, t])` from `0 ∉ C` to `η(t) ∈ C` meets `∂C` before `t`
    have hpre : IsPreconnected (η '' Icc 0 t) :=
      isPreconnected_Icc.image _ (hη.2.1.mono fun s hs => hs.1)
    obtain ⟨z, hzR, hzf⟩ : (η '' Icc 0 t ∩ frontier C).Nonempty := by
      by_contra hne
      have hsub := subset_of_isPreconnected_of_disjoint_frontier hpre hP.isOpen
        ⟨η t, ⟨t, ⟨ht, le_rfl⟩, rfl⟩, htC⟩ (Set.disjoint_iff_inter_eq_empty.2
          (Set.not_nonempty_iff_eq_empty.1 hne))
      have h0 := hP.subset_H (hsub ⟨0, ⟨le_rfl, ht⟩, rfl⟩)
      rw [hη.1] at h0
      exact lt_irrefl _ (show (0 : ℝ) < (0 : ℂ).im from h0)
    obtain ⟨t', ht', rfl⟩ := hzR
    have hτ := hP.τ_le (hP.y_mem_of_mem_frontier hzf ⟨t', ⟨ht'.1, le_rfl⟩, rfl⟩)
    refine lt_of_le_of_lt hτ (lt_of_le_of_ne ht'.2 fun h => ?_)
    rw [h] at hzf
    have := hzf.2
    rw [hP.isOpen.interior_eq] at this
    exact this htC
  · -- after `σ` the whole boundary is visited and `C` is swallowed
    by_contra hσ
    push Not at hσ
    have hx : α₁ 0 ∈ η '' Icc 0 t := ⟨σ, ⟨hP.nonneg_σ, hσ⟩, hP.first_x⟩
    have hfrR : frontier C ⊆ η '' Icc 0 t := by
      rw [hP.frontier_eq]
      rintro _ (⟨v, hv, rfl⟩ | ⟨v, hv, rfl⟩)
      exacts [hP.mem_of_x_mem hx (Or.inl rfl) hv, hP.mem_of_x_mem hx (Or.inr rfl) hv]
    have hDpre := QuantumZipper.RS.isPreconnected_compl_fwdHull hP.continuous_W hP.W_zero ht
    have hDfr : Disjoint (H \ fwdHull W t) (frontier C) := Set.disjoint_right.2 fun z hz =>
      notMem_domain_of_mem_trace hη ht (hfrR hz)
    have hDC : C ∩ (H \ fwdHull W t) = ∅ := by
      by_contra hne
      have hsub := subset_of_isPreconnected_of_disjoint_frontier hDpre hP.isOpen
        (by rw [inter_comm]; exact Set.nonempty_iff_ne_empty.2 hne) hDfr
      exact not_isBounded_domain hη ht (hP.isBounded.subset hsub)
    have hcl := hP.isOpen.inter_closure
      ⟨htC, trace_mem_closure_domain hη hP.continuous_W hP.W_zero ht⟩
    rw [hDC, closure_empty] at hcl
    exact hcl

/-- The incoming prefix `β` is unbounded. -/
theorem not_isBounded_β (hP : IsReversePocket W η C α₁ α₂ β τ σ) : ¬ IsBounded (β '' Ici 0) := by
  intro hb
  obtain ⟨M, hM⟩ := hb.exists_norm_le
  obtain ⟨t, ht⟩ := ((hP.tendsto_β.eventually (eventually_gt_atTop M)).and
    (eventually_ge_atTop 0)).exists
  exact absurd (hM _ ⟨t, ht.2, rfl⟩) (not_le.2 ht.1)

/-- Before `σ` the prefix `β` is unvisited. -/
theorem β_notMem (hP : IsReversePocket W η C α₁ α₂ β τ σ) {t : ℝ} (htσ : t < σ) {r : ℝ}
    (hr : r ∈ Ici (0 : ℝ)) : β r ∉ η '' Icc 0 t := fun h =>
  absurd (hP.σ_le (hP.rev_β t r hr h)) (not_le.2 htσ)

/-- Before `σ` the prefix `β` lies in the current domain. -/
theorem β_mem_domain (hP : IsReversePocket W η C α₁ α₂ β τ σ) {r : ℝ} (hr : 0 ≤ r) (hrσ : r < σ)
    {t : ℝ} (ht : t ∈ Ici (0 : ℝ)) : β t ∈ H \ fwdHull W r := by
  refine subset_domain_of_not_isBounded hP.trace hr (isPreconnected_Ici.image _ hP.cont_β)
    (fun _ ⟨t', ht', h⟩ => h ▸ hP.mem_H_β t' ht')
    (Set.disjoint_left.2 fun _ ⟨t', ht', h⟩ => h ▸ hP.β_notMem hrσ ht') hP.not_isBounded_β
    ⟨t, ht, rfl⟩

/-- **The common-contact order** for the prefix `β`: it meets the two sides only at `x₀`
(Specification p. 190: "a portion of one flow before `x₀` cannot touch an open selected side of the
other flow after `x₀`"). A point of a side is visited by `σ`; a point of `β` only after `x₀`. -/
theorem β_eq_of_eq_arm (hP : IsReversePocket W η C α₁ α₂ β τ σ) {α : ℝ → ℂ}
    (hα : α = α₁ ∨ α = α₂) {v : ℝ} (hv : v ∈ Icc (0 : ℝ) 1) {r : ℝ} (hr : r ∈ Ici (0 : ℝ))
    (h : α v = β r) : α v = α₁ 0 := by
  have hx : α₁ 0 ∈ η '' Icc 0 σ := ⟨σ, ⟨hP.nonneg_σ, le_rfl⟩, hP.first_x⟩
  obtain ⟨t', ht', hpt'⟩ := hP.mem_of_x_mem hx hα hv
  have hβ : β r ∈ η '' Icc 0 t' := ⟨t', ⟨ht'.1, le_rfl⟩, hpt'.trans h⟩
  have hσt := hP.σ_le (hP.rev_β t' r hr hβ)
  rw [← hpt', le_antisymm ht'.2 hσt, hP.first_x]

/-- The two sides meet only at their endpoints; on the half-open sides only at `x₀`. -/
theorem arms_eq (hP : IsReversePocket W η C α₁ α₂ β τ σ) {v v' : ℝ} (hv : v ∈ Ico (0 : ℝ) 1)
    (hv' : v' ∈ Ico (0 : ℝ) 1) (h : α₁ v = α₂ v') : α₁ v = α₁ 0 := by
  rcases eq_or_lt_of_le hv.1 with h0 | h0
  · rw [← h0]
  rcases eq_or_lt_of_le hv'.1 with h0' | h0'
  · rw [h, ← h0', hP.junction]
  exact absurd h (hP.sides v ⟨h0, hv.2⟩ v' ⟨h0', hv'.2⟩)

/-- **(JP2) and the chart at `r ∈ [τ, σ)`.** For each side `α`, with `u = u(r)` its first-visit
parameter: `0 < u ≤ 1`, the open prefix `α([0, u))` lies in `D_r`, and the suffix `α([u, 1])` is
visited by time `r` (hence not in `D_r`). -/
theorem chart (hP : IsReversePocket W η C α₁ α₂ β τ σ) {r : ℝ} (hτr : τ ≤ r) (hrσ : r < σ)
    {α : ℝ → ℂ} (hα : α = α₁ ∨ α = α₂) :
    0 < firstVisit (fun t => η '' Icc 0 t) α r ∧ firstVisit (fun t => η '' Icc 0 t) α r ≤ 1 ∧
      (∀ v ∈ Ico 0 (firstVisit (fun t => η '' Icc 0 t) α r), α v ∈ H \ fwdHull W r) ∧
      (∀ v ∈ Icc (firstVisit (fun t => η '' Icc 0 t) α r) 1, α v ∈ η '' Icc 0 r) ∧
      (∀ v ∈ Icc (firstVisit (fun t => η '' Icc 0 t) α r) 1, α v ∉ H \ fwdHull W r) := by
  obtain ⟨hc, -, h0, h1, hH, hrev⟩ := hP.arm hα
  have hr0 : 0 ≤ r := hP.nonneg.trans hτr
  set u := firstVisit (fun t => η '' Icc 0 t) α r with hudef
  have hne : ∃ v ∈ Icc (0 : ℝ) 1, α v ∈ η '' Icc 0 r :=
    ⟨1, ⟨zero_le_one, le_rfl⟩, by rw [h1]; exact ⟨τ, ⟨hP.nonneg, hτr⟩, hP.first_y⟩⟩
  have hmem := firstVisit_mem (R := fun t => η '' Icc 0 t) hc hP.isClosed_range hne
  have hx : α 0 ∉ η '' Icc 0 r := fun h => by
    rw [h0] at h; exact absurd (hP.σ_le h) (not_le.2 hrσ)
  have hpos : 0 < u := lt_of_le_of_ne hmem.1.1 fun h => hx (by
    have := hmem.2; rw [hudef] at h; rwa [← h] at this)
  have hsuf : ∀ v ∈ Icc u 1, α v ∈ η '' Icc 0 r := fun v hv =>
    hrev r u hmem.1 v ⟨hmem.1.1.trans hv.1, hv.2⟩ hv.1 hmem.2
  have hpre : ∀ v ∈ Ico 0 u, α v ∉ η '' Icc 0 r := fun v hv h =>
    absurd (firstVisit_le ⟨hv.1, hv.2.le.trans hmem.1.2⟩ h) (not_le.2 hv.2)
  refine ⟨hpos, hmem.1.2, fun v hv => ?_, hsuf, fun v hv =>
    notMem_domain_of_mem_trace hP.trace hr0 (hsuf v hv)⟩
  -- the prefix up to `v`, joined with `β`, is an unbounded connected set avoiding `R_r`
  have hv1 : v ≤ 1 := hv.2.le.trans hmem.1.2
  set S := α '' Icc 0 v ∪ β '' Ici 0 with hSdef
  have hSpre : IsPreconnected S :=
    IsPreconnected.union (α 0) ⟨0, ⟨le_rfl, hv.1⟩, rfl⟩ ⟨0, mem_Ici.2 le_rfl, by rw [hP.β_zero, h0]⟩
      (isPreconnected_Icc.image _ (hc.mono (Icc_subset_Icc_right hv1)))
      (isPreconnected_Ici.image _ hP.cont_β)
  have hSH : S ⊆ H := by
    rintro _ (⟨v', hv', rfl⟩ | ⟨t', ht', rfl⟩)
    exacts [hH v' ⟨hv'.1, hv'.2.trans_lt (hv.2.trans_le hmem.1.2)⟩, hP.mem_H_β t' ht']
  have hSR : Disjoint S (η '' Icc 0 r) := by
    refine Set.disjoint_left.2 ?_
    rintro _ (⟨v', hv', rfl⟩ | ⟨t', ht', rfl⟩)
    · exact hpre v' ⟨hv'.1, hv'.2.trans_lt hv.2⟩
    · exact hP.β_notMem hrσ ht'
  have hSb : ¬ IsBounded S := fun h => hP.not_isBounded_β (h.subset subset_union_right)
  exact subset_domain_of_not_isBounded hP.trace hr0 hSpre hSH hSR hSb
    (Or.inl ⟨v, ⟨hv.1, le_rfl⟩, rfl⟩)

/-- **Lemma 1.4 (fresh boundary visit)** in the pocket: a fresh visit `η(a) ∈ ∂C` is the current
first-visit attachment of a side containing it. -/
theorem fresh_attach (hP : IsReversePocket W η C α₁ α₂ β τ σ) {a : ℝ} (ha : 0 ≤ a)
    (haC : η a ∈ frontier C) (hfresh : η a ∉ η '' Ico 0 a) :
    η a = α₁ (firstVisit (fun t => η '' Icc 0 t) α₁ a) ∨
      η a = α₂ (firstVisit (fun t => η '' Icc 0 t) α₂ a) := by
  rw [hP.frontier_eq] at haC
  rcases haC with ⟨v, hv, hav⟩ | ⟨v, hv, hav⟩
  · left
    have hu := R16.firstVisitParam_eq_of_fresh hP.inj₁ hP.rev₁ ha hv hav.symm hfresh
    change firstVisit (fun t => η '' Icc 0 t) α₁ a = v at hu
    rw [hu, hav]
  · right
    have hu := R16.firstVisitParam_eq_of_fresh hP.inj₂ hP.rev₂ ha hv hav.symm hfresh
    change firstVisit (fun t => η '' Icc 0 t) α₂ a = v at hu
    rw [hu, hav]

/-- Two lifted arms with distinct gates meet only at the lifted junction. -/
theorem lift_arms_inter_lt (hW : Continuous W) {r : ℝ} (hr : 0 ≤ r) {u₁ u₂ : ℝ}
    (hα₁D : ∀ v ∈ Ico 0 u₁, α₁ v ∈ H \ fwdHull W r) (hα₂D : ∀ v ∈ Ico 0 u₂, α₂ v ∈ H \ fwdHull W r)
    (h12 : ∀ v ∈ Ico 0 u₁, ∀ v' ∈ Ico 0 u₂, α₁ v = α₂ v' → α₁ v = α₁ 0) {q₁ q₂ : ℝ}
    {a₁ a₂ : ℝ → ℂ} (hq : q₁ ≠ q₂) (ha₁0 : a₁ 0 = q₁) (ha₂0 : a₂ 0 = q₂)
    (ha₁H : ∀ t ∈ Ioc (0 : ℝ) 1, a₁ t ∈ H) (ha₂H : ∀ t ∈ Ioc (0 : ℝ) 1, a₂ t ∈ H)
    (ha₁img : a₁ '' Ioc 0 1 = fwdMap W r '' (α₁ '' Ico 0 u₁))
    (ha₂img : a₂ '' Ioc 0 1 = fwdMap W r '' (α₂ '' Ico 0 u₂)) :
    a₁ '' Icc 0 1 ∩ a₂ '' Icc 0 1 ⊆ {fwdMap W r (α₁ 0)} := by
  have hq₁₂ : (q₁ : ℂ) ≠ q₂ := fun h => hq (ofReal_injective h)
  rintro w ⟨hw₁, hw₂⟩
  rcases eq_or_mem_open_arm ha₁0 hw₁ with h | h
  · exact absurd (h.symm.trans (arm_real ha₂0 ha₂H hw₂ (by rw [h]; simp))) hq₁₂
  rcases eq_or_mem_open_arm ha₂0 hw₂ with h' | h'
  · obtain ⟨t, ht, rfl⟩ := h
    exact absurd (h' ▸ ha₁H t ht) (not_mem_H_ofReal q₂)
  rw [ha₁img] at h; rw [ha₂img] at h'
  exact lift_inter_eq hW hr hα₁D hα₂D h12 h h'

/-- **The central face at `r ∈ [τ, σ)`** (Aux. lemma 36, geometric part; (RG3)): there is a Jordan
curve `Γ ⊆ ℍ̄` with `f̄_r(w) ∈ C ↔ w ∈ innerSide Γ` for `w ∈ ℍ`; i.e. `F_r = g_r(C ∩ D_r)` is the
inner side of `Γ` (the two lifted incoming arms and, for distinct gates, the real segment between
them). -/
theorem exists_face (hP : IsReversePocket W η C α₁ α₂ β τ σ) {r : ℝ} (hτr : τ ≤ r)
    (hrσ : r < σ) : ∃ Γ : Set ℂ, LQGMetric.JordanMap.IsJordanCurve Γ ∧ Γ ⊆ Hbar ∧
      ∀ w ∈ H, (trMap W 0 r w ∈ C ↔ w ∈ innerSide Γ) := by
  have hη := hP.trace
  have hW := hP.continuous_W
  have hW0 := hP.W_zero
  have hr0 : 0 ≤ r := hP.nonneg.trans hτr
  obtain ⟨hu₁, hu₁', hD₁, -, hK₁⟩ := hP.chart hτr hrσ (Or.inl rfl)
  obtain ⟨hu₂, hu₂', hD₂, -, hK₂⟩ := hP.chart hτr hrσ (Or.inr rfl)
  obtain ⟨q₁, a₁, ha₁, ha₁i, ha₁0, ha₁1, ha₁H, -, ha₁img⟩ :=
    exists_arm hη hW hW0 hr0 hu₁ (hP.cont₁.mono (Icc_subset_Icc_right hu₁'))
      (hP.inj₁.mono (Icc_subset_Icc_right hu₁')) hD₁ (hK₁ _ ⟨le_rfl, hu₁'⟩)
  obtain ⟨q₂, a₂, ha₂, ha₂i, ha₂0, ha₂1, ha₂H, -, ha₂img⟩ :=
    exists_arm hη hW hW0 hr0 hu₂ (hP.cont₂.mono (Icc_subset_Icc_right hu₂'))
      (hP.inj₂.mono (Icc_subset_Icc_right hu₂')) hD₂ (hK₂ _ ⟨le_rfl, hu₂'⟩)
  have ha₂1' : a₂ 1 = fwdMap W r (α₁ 0) := by rw [ha₂1, hP.junction]
  have h12 : ∀ v ∈ Ico 0 (firstVisit (fun t => η '' Icc 0 t) α₁ r),
      ∀ v' ∈ Ico 0 (firstVisit (fun t => η '' Icc 0 t) α₂ r), α₁ v = α₂ v' → α₁ v = α₁ 0 :=
    fun v hv v' hv' h => hP.arms_eq ⟨hv.1, hv.2.trans_le hu₁'⟩ ⟨hv'.1, hv'.2.trans_le hu₂'⟩ h
  rcases lt_trichotomy q₁ q₂ with hq | hq | hq
  · have h12' := lift_arms_inter_lt hW hr0 hD₁ hD₂ h12 hq.ne ha₁0 ha₂0 ha₁H ha₂H ha₁img ha₂img
    obtain ⟨hΓJ, hΓH⟩ := isJordanCurve_faceBoundary hq ha₁ ha₂ ha₁i ha₂i ha₁0 ha₂0 ha₁1 ha₂1'
      ha₁H ha₂H h12'
    exact ⟨_, hΓJ, hΓH, fun w hw => trMap_mem_iff_innerSide hη hW hW0 hr0 hP.isOpen
      hP.isBounded hu₁ hu₁' hu₂' hP.frontier_eq hD₁ hD₂ hK₁ hK₂ hq ha₁ ha₂ ha₁i ha₂i ha₁0 ha₂0
      ha₁1 ha₂1' ha₁H ha₂H h12' ha₁img ha₂img hw⟩
  · subst hq
    have h12' : a₁ '' Icc 0 1 ∩ a₂ '' Icc 0 1 ⊆ {(q₁ : ℂ), fwdMap W r (α₁ 0)} := by
      rintro w ⟨hw₁, hw₂⟩
      rcases eq_or_mem_open_arm ha₁0 hw₁ with h | h
      · exact Or.inl h
      rcases eq_or_mem_open_arm ha₂0 hw₂ with h' | h'
      · exact Or.inl h'
      rw [ha₁img] at h; rw [ha₂img] at h'
      exact Or.inr (lift_inter_eq hW hr0 hD₁ hD₂ h12 h h')
    have hΓJ := Sec7.isJordanCurve_image_union ha₁ ha₂ ha₁i ha₂i (by rw [ha₁0, ha₂0])
      (by rw [ha₁1, ha₂1']) (by rw [ha₁0, ha₁1]; exact h12')
    have hΓH : a₁ '' Icc 0 1 ∪ a₂ '' Icc 0 1 ⊆ Hbar :=
      union_subset (image_arm_subset_Hbar ha₁0 ha₁H) (image_arm_subset_Hbar ha₂0 ha₂H)
    exact ⟨_, hΓJ, hΓH, fun w hw => trMap_mem_iff_innerSide_eq hη hW hW0 hr0 hP.isOpen
      hP.isBounded hu₁ hu₁' hu₂' hP.frontier_eq hD₁ hD₂ hK₁ hK₂ ha₁ ha₂ ha₁i ha₂i ha₁0 ha₂0
      ha₁1 ha₂1' ha₁H ha₂H h12' ha₁img ha₂img hw⟩
  · -- relabel the two sides
    have h21 : ∀ v ∈ Ico 0 (firstVisit (fun t => η '' Icc 0 t) α₂ r),
        ∀ v' ∈ Ico 0 (firstVisit (fun t => η '' Icc 0 t) α₁ r), α₂ v = α₁ v' → α₂ v = α₂ 0 :=
      fun v hv v' hv' h => by rw [hP.junction, h]; exact h12 v' hv' v hv h.symm
    have h12' : a₂ '' Icc 0 1 ∩ a₁ '' Icc 0 1 ⊆ {fwdMap W r (α₂ 0)} :=
      lift_arms_inter_lt (α₁ := α₂) (α₂ := α₁) hW hr0 hD₂ hD₁ h21 hq.ne ha₂0 ha₁0 ha₂H ha₁H
        ha₂img ha₁img
    rw [hP.junction] at h12'
    obtain ⟨hΓJ, hΓH⟩ := isJordanCurve_faceBoundary hq ha₂ ha₁ ha₂i ha₁i ha₂0 ha₁0 ha₂1' ha₁1
      ha₂H ha₁H h12'
    refine ⟨_, hΓJ, hΓH, fun w hw => trMap_mem_iff_innerSide hη hW hW0 hr0 hP.isOpen
      hP.isBounded hu₂ hu₂' hu₁' (by rw [hP.frontier_eq, union_comm]) hD₂ hD₁ hK₂ hK₁ hq ha₂ ha₁
      ha₂i ha₁i ha₂0 ha₁0 ha₂1' ha₁1 ha₂H ha₁H h12' ha₂img ha₁img hw⟩

/-- A limit of `C`-visits after `s` is a limit of `C`-visits after every `r < a`. -/
theorem mem_closure_visits_of_lt {s r a : ℝ} (ha : a ∈ closure {t | s < t ∧ η t ∈ C})
    (hra : r < a) : a ∈ closure {t | r < t ∧ η t ∈ C} := by
  rw [_root_.mem_closure_iff] at ha ⊢
  intro U hU haU
  obtain ⟨t, htU, ht⟩ := ha (U ∩ Ioi r) (hU.inter isOpen_Ioi) ⟨haU, hra⟩
  exact ⟨t, htU.1, htU.2, ht.2⟩

/-- A limit of `C`-visits after `s ≥ 0` has its tip in `C̄`. -/
theorem mem_closure_of_mem_closure_visits (hP : IsReversePocket W η C α₁ α₂ β τ σ) {s a : ℝ}
    (hs : 0 ≤ s) (ha : a ∈ closure {t | s < t ∧ η t ∈ C}) : η a ∈ closure C := by
  have hsub : {t | s < t ∧ η t ∈ C} ⊆ Ici 0 := fun t ht => hs.trans ht.1.le
  have ha0 : a ∈ Ici (0 : ℝ) := closure_minimal hsub isClosed_Ici ha
  have hc : ContinuousWithinAt η {t | s < t ∧ η t ∈ C} a := (hP.trace.2.1 a ha0).mono hsub
  exact closure_mono (image_subset_iff.2 fun t ht => ht.2) (hc.mem_closure_image ha)

/-- **Propositions 1.5–1.6 for the pocket** (ruling R41's note, L233–L311; Specification
pp. 201–205, (GC1) and (RG2)). Let `[a, b] ⊆ [τ, σ)` be a nondegenerate interval on which the trace
avoids `C`,
whose left end is `τ` or a limit of `C`-visits after `s`, and whose right end is a limit of later
`C`-visits. Under Aux. lemma 37's attachment constancy, for every chart time `0 ≤ s < a`:
`δ_s(a) = δ_s(b)` and `η(a) = η(b)`. Old start: a fixed chart `r ∈ (s, a)` after both attachment
visits and the gate lemma; fresh start: the chart at `a` with its supplied gate (Lemma 1.4). -/
theorem gap_eq (hP : IsReversePocket W η C α₁ α₂ β τ σ) (hAC : AttachmentConstancy η C α₁ α₂ τ σ)
    {s a b : ℝ} (hs : 0 ≤ s) (hsa : s < a) (hτa : τ ≤ a) (hab : a < b) (hbσ : b < σ)
    (hgap : ∀ t ∈ Icc a b, η t ∉ C) (ha : a = τ ∨ a ∈ closure {t | s < t ∧ η t ∈ C})
    (hb : b ∈ closure {t | a < t ∧ η t ∈ C}) :
    trMap W s a 0 = trMap W s b 0 ∧ η a = η b := by
  have hη := hP.trace
  have hW := hP.continuous_W
  have hW0 := hP.W_zero
  have ha0 : 0 < a := hs.trans_lt hsa
  have haσ : a < σ := hab.trans hbσ
  obtain ⟨hc₁, hc₂⟩ := hAC a b hτa hab.le hbσ hgap
  -- the unvisited pieces at `a` stay unvisited through `b`
  have hunv : ∀ {α : ℝ → ℂ}, (α = α₁ ∨ α = α₂) →
      firstVisit (fun t => η '' Icc 0 t) α b = firstVisit (fun t => η '' Icc 0 t) α a →
      ∀ t ∈ Icc a b, ∀ v ∈ Ico 0 (firstVisit (fun t => η '' Icc 0 t) α a), η t ≠ α v := by
    intro α hα hc t ht v hv h
    obtain ⟨-, hu', -, -, -⟩ := hP.chart hτa haσ hα
    have hle := firstVisit_le (R := fun t => η '' Icc 0 t) (α := α) (t := b)
      ⟨hv.1, hv.2.le.trans hu'⟩ ⟨t, ⟨ha0.le.trans ht.1, ht.2⟩, h⟩
    rw [hc] at hle
    exact absurd hv.2 (not_lt.2 hle)
  have hunv₁ := hunv (Or.inl rfl) hc₁
  have hunv₂ := hunv (Or.inr rfl) hc₂
  have hunv₃ : ∀ t ∈ Icc a b, ∀ r ∈ Ici (0 : ℝ), η t ≠ β r := fun t ht r hr h =>
    hP.β_notMem hbσ hr ⟨t, ⟨ha0.le.trans ht.1, ht.2⟩, h⟩
  have h13 : ∀ {u : ℝ}, u ≤ 1 → ∀ v ∈ Ico 0 u, ∀ r ∈ Ici (0 : ℝ), α₁ v = β r → α₁ v = α₁ 0 :=
    fun hu v hv r hr h => hP.β_eq_of_eq_arm (Or.inl rfl) ⟨hv.1, hv.2.le.trans hu⟩ hr h
  have h23 : ∀ {u : ℝ}, u ≤ 1 → ∀ v ∈ Ico 0 u, ∀ r ∈ Ici (0 : ℝ), α₂ v = β r → α₂ v = α₁ 0 :=
    fun hu v hv r hr h => hP.β_eq_of_eq_arm (Or.inr rfl) ⟨hv.1, hv.2.le.trans hu⟩ hr h
  have h12 : ∀ {u₁ u₂ : ℝ}, u₁ ≤ 1 → u₂ ≤ 1 → ∀ v ∈ Ico 0 u₁, ∀ v' ∈ Ico 0 u₂,
      α₁ v = α₂ v' → α₁ v = α₁ 0 := fun hu₁ hu₂ v hv v' hv' h =>
    hP.arms_eq ⟨hv.1, hv.2.trans_le hu₁⟩ ⟨hv'.1, hv'.2.trans_le hu₂⟩ h
  by_cases hfresh : η a ∈ η '' Ico 0 a
  · -- **old start**: a fixed chart after both attachment visits
    have haτ : a ≠ τ := fun h => hP.fresh_y (by rw [← hP.first_y, ← h]; exact hfresh)
    have ha' := ha.resolve_left haτ
    have hvis : ∀ {α : ℝ → ℂ}, (α = α₁ ∨ α = α₂) →
        ∃ t' ∈ Ico 0 a, η t' = α (firstVisit (fun t => η '' Icc 0 t) α a) := by
      intro α hα
      obtain ⟨-, hu', -, hsuf, -⟩ := hP.chart hτa haσ hα
      obtain ⟨t', ht', hpt'⟩ := hsuf _ ⟨le_rfl, hu'⟩
      rcases eq_or_lt_of_le ht'.2 with h | h
      · rw [h] at hpt'
        obtain ⟨t'', ht'', h''⟩ := hfresh
        exact ⟨t'', ht'', h''.trans hpt'⟩
      · exact ⟨t', ⟨ht'.1, h⟩, hpt'⟩
    obtain ⟨t₁, ht₁, hp₁⟩ := hvis (Or.inl rfl)
    obtain ⟨t₂, ht₂, hp₂⟩ := hvis (Or.inr rfl)
    set M := max s (max t₁ t₂) with hMdef
    have hMa : M < a := max_lt hsa (max_lt ht₁.2 ht₂.2)
    set r := (M + a) / 2 with hrdef
    have hMr : M < r := by rw [hrdef]; linarith
    have hra : r < a := by rw [hrdef]; linarith
    have hsr : s ≤ r := (le_max_left _ _).trans hMr.le
    have ht₁r : t₁ ≤ r := ((le_max_left _ _).trans (le_max_right _ _)).trans hMr.le
    have ht₂r : t₂ ≤ r := ((le_max_right _ _).trans (le_max_right _ _)).trans hMr.le
    have hτr : τ ≤ r := by
      refine (hP.τ_le (hP.y_mem_of_mem (Or.inl rfl) ?_ ⟨t₁, ⟨ht₁.1, le_rfl⟩, hp₁⟩)).trans ht₁r
      obtain ⟨hu, hu', -⟩ := hP.chart hτa haσ (Or.inl rfl)
      exact ⟨hu.le, hu'⟩
    have hrσ : r < σ := hra.trans haσ
    have hr0 : 0 ≤ r := hs.trans hsr
    -- the attachment parameters at `r` and at `a` agree
    have heq : ∀ {α : ℝ → ℂ}, (α = α₁ ∨ α = α₂) → ∀ {t' : ℝ}, t' ∈ Ico 0 a → t' ≤ r →
        η t' = α (firstVisit (fun t => η '' Icc 0 t) α a) →
        firstVisit (fun t => η '' Icc 0 t) α r = firstVisit (fun t => η '' Icc 0 t) α a := by
      intro α hα t' ht' ht'r hp
      obtain ⟨hc, -⟩ := hP.arm hα
      refine firstVisit_eq_of_visited hc monotone_image_Icc hra.le hP.isClosed_range
        ⟨1, ⟨zero_le_one, le_rfl⟩, ?_⟩ ⟨t', ⟨ht'.1, ht'r⟩, hp⟩
      obtain ⟨-, -, -, h1, -⟩ := hP.arm hα
      rw [h1]; exact ⟨τ, ⟨hP.nonneg, hτa⟩, hP.first_y⟩
    have he₁ := heq (Or.inl rfl) ht₁ ht₁r hp₁
    have he₂ := heq (Or.inr rfl) ht₂ ht₂r hp₂
    obtain ⟨hu₁, hu₁', hD₁, -, hK₁⟩ := hP.chart hτr hrσ (Or.inl rfl)
    obtain ⟨hu₂, hu₂', hD₂, -, hK₂⟩ := hP.chart hτr hrσ (Or.inr rfl)
    rw [← he₁] at hunv₁
    rw [← he₂] at hunv₂
    exact ownFuture_gap_eq_of_pocket hη hW hW0 hP.isOpen hP.isBounded hu₁ hu₂ hu₁' hu₂'
      (hP.cont₁.mono (Icc_subset_Icc_right hu₁')) (hP.cont₂.mono (Icc_subset_Icc_right hu₂'))
      (hP.inj₁.mono (Icc_subset_Icc_right hu₁')) (hP.inj₂.mono (Icc_subset_Icc_right hu₂'))
      hP.junction.symm hP.frontier_eq (h12 hu₁' hu₂') hP.cont_β hP.inj_β hP.β_zero hP.tendsto_β
      (h13 hu₁') (h23 hu₂') hs hsr hra hab hD₁ hD₂ hK₁ hK₂
      (fun r' hr' => hP.β_mem_domain hr0 hrσ hr') hgap hunv₁ hunv₂ hunv₃
      (mem_closure_visits_of_lt ha' hra)
      (closure_mono (s := {t | a < t ∧ η t ∈ C}) (t := {t | r < t ∧ η t ∈ C})
        (fun t ht => ⟨hra.trans ht.1, ht.2⟩) hb)
  · -- **fresh start**: the chart at `a` and its supplied gate (Lemma 1.4)
    have hfr : η a ∈ frontier C := by
      rcases ha with h | h
      · rw [h, hP.first_y, hP.frontier_eq]
        exact Or.inl ⟨1, ⟨zero_le_one, le_rfl⟩, rfl⟩
      · refine ⟨hP.mem_closure_of_mem_closure_visits hs h, ?_⟩
        rw [hP.isOpen.interior_eq]
        exact hgap a ⟨le_rfl, hab.le⟩
    have hatt := hP.fresh_attach ha0.le hfr hfresh
    obtain ⟨hu₁, hu₁', hD₁, -, hK₁⟩ := hP.chart hτa haσ (Or.inl rfl)
    obtain ⟨hu₂, hu₂', hD₂, -, hK₂⟩ := hP.chart hτa haσ (Or.inr rfl)
    exact ownFuture_gap_eq_of_pocket_fresh hη hW hW0 hP.isOpen hP.isBounded hu₁ hu₂ hu₁' hu₂'
      (hP.cont₁.mono (Icc_subset_Icc_right hu₁')) (hP.cont₂.mono (Icc_subset_Icc_right hu₂'))
      (hP.inj₁.mono (Icc_subset_Icc_right hu₁')) (hP.inj₂.mono (Icc_subset_Icc_right hu₂'))
      hP.junction.symm hP.frontier_eq (h12 hu₁' hu₂') hP.cont_β hP.inj_β hP.β_zero hP.tendsto_β
      (h13 hu₁') (h23 hu₂') hs hsa.le ha0 hab hD₁ hD₂ hK₁ hK₂
      (fun r' hr' => hP.β_mem_domain ha0.le haσ hr') (hP.mem_H_of_fresh ha0 hfr hfresh) hfresh hatt
      hgap hunv₁ hunv₂ hunv₃ hb

/-- **The initial gap at the original seed** (ruling R41's note, L264–L266: "If `τ = 0` is the
original seed, the initial chart gives the same assertion directly"): if `y₀ = η(0)` (`τ = 0`) and
the
trace avoids `C` on `[0, b]`, `b` a limit of later visits, then `η(b) = η(0)`. In the chart at `0`
(the identity) both lifted sides end at the gate `0 = δ_0(0)`, and the equal-gate lemma with this
supplied gate applies. -/
theorem gap_eq_seed (hP : IsReversePocket W η C α₁ α₂ β τ σ)
    (hAC : AttachmentConstancy η C α₁ α₂ τ σ) (hτ0 : τ = 0) {b : ℝ} (hb0 : 0 < b) (hbσ : b < σ)
    (hgap : ∀ t ∈ Icc 0 b, η t ∉ C) (hb : b ∈ closure {t | 0 < t ∧ η t ∈ C}) : η 0 = η b := by
  have hη := hP.trace
  have hW := hP.continuous_W
  have hW0 := hP.W_zero
  have h0σ : (0 : ℝ) < σ := hb0.trans hbσ
  obtain ⟨hc₁, hc₂⟩ := hAC 0 b hτ0.le hb0.le hbσ hgap
  obtain ⟨hu₁, hu₁', hD₁, hV₁, hK₁⟩ := hP.chart hτ0.le h0σ (Or.inl rfl)
  obtain ⟨hu₂, hu₂', hD₂, hV₂, hK₂⟩ := hP.chart hτ0.le h0σ (Or.inr rfl)
  obtain ⟨q₁, a₁, ha₁, ha₁i, ha₁0, ha₁1, ha₁H, hq₁, ha₁img⟩ :=
    exists_arm hη hW hW0 le_rfl hu₁ (hP.cont₁.mono (Icc_subset_Icc_right hu₁'))
      (hP.inj₁.mono (Icc_subset_Icc_right hu₁')) hD₁ (hK₁ _ ⟨le_rfl, hu₁'⟩)
  obtain ⟨q₂, a₂, ha₂, ha₂i, ha₂0, ha₂1, ha₂H, hq₂, ha₂img⟩ :=
    exists_arm hη hW hW0 le_rfl hu₂ (hP.cont₂.mono (Icc_subset_Icc_right hu₂'))
      (hP.inj₂.mono (Icc_subset_Icc_right hu₂')) hD₂ (hK₂ _ ⟨le_rfl, hu₂'⟩)
  -- both gates are the seed: the attachment visited by time `0` is `η(0) = 0`
  have hgate : ∀ {q : ℝ} {p : ℂ}, trMap W 0 0 (q : ℂ) = p → p ∈ η '' Icc 0 0 → q = 0 := by
    intro q p hq hp
    obtain ⟨t, ht, rfl⟩ := hp
    rw [le_antisymm ht.2 ht.1, hη.1, YuanSimpleApprox.trMap_self hW 0 (ofReal_mem_Hbar q)] at hq
    exact_mod_cast hq
  have hq₁0 := hgate hq₁ (hV₁ _ ⟨le_rfl, hu₁'⟩)
  have hq₂0 := hgate hq₂ (hV₂ _ ⟨le_rfl, hu₂'⟩)
  rw [hq₁0] at ha₁0
  rw [hq₂0] at ha₂0
  have ha₂1' : a₂ 1 = fwdMap W 0 (α₁ 0) := by rw [ha₂1, hP.junction]
  have hunv : ∀ {α : ℝ → ℂ}, (α = α₁ ∨ α = α₂) →
      firstVisit (fun t => η '' Icc 0 t) α b = firstVisit (fun t => η '' Icc 0 t) α 0 →
      ∀ v ∈ Ico 0 (firstVisit (fun t => η '' Icc 0 t) α 0), η b ≠ α v := by
    intro α hα hc v hv h
    obtain ⟨-, hu', -, -, -⟩ := hP.chart hτ0.le h0σ hα
    have hle := firstVisit_le (R := fun t => η '' Icc 0 t) (α := α) (t := b)
      ⟨hv.1, hv.2.le.trans hu'⟩ ⟨b, ⟨hb0.le, le_rfl⟩, h⟩
    rw [hc] at hle
    exact absurd hv.2 (not_lt.2 hle)
  exact (ownFuture_gap_eq_of_arms_eq_of_gate hη hW hW0 hP.isOpen hP.isBounded hu₁ hu₁' hu₂'
    hP.frontier_eq (fun v hv v' hv' h => hP.arms_eq ⟨hv.1, hv.2.trans_le hu₁'⟩
      ⟨hv'.1, hv'.2.trans_le hu₂'⟩ h) le_rfl le_rfl hb0.le hD₁ hD₂ hK₁ hK₂ ha₁ ha₂ ha₁i ha₂i
    ha₁0 ha₂0 ha₁1 ha₂1' ha₁H ha₂H ha₁img ha₂img (hgap b ⟨hb0.le, le_rfl⟩)
    (hunv (Or.inl rfl) hc₁) (hunv (Or.inr rfl) hc₂) hb).2

end IsReversePocket

end InteractingSLE.Sec6
