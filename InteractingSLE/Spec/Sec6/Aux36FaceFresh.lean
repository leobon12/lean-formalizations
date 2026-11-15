/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec6.Aux36FacePocket
import InteractingSLE.Spec.Supplement.R2RefAttach

/-!
# A fresh boundary visit is a current attachment (R41, Lemma 1.4) and the fresh-start gap

Ruling R41's note (`source/external/AstraIG1/ig1_ztip_elimination.txt` L210–L228):

> **Lemma 1.4** (A fresh boundary visit is a current attachment). In a contained, mixed or outer
> pocket, suppose `τ ≤ a < σ`, `p = η(a) ∈ ∂C` is an interior physical point, and `p` has not been
> visited before `a`. Then `p` is a current first-visit attachment on each selected arm containing
> it. Its lifted incoming endpoint equals `W_a`.
>
> *Proof.* For a contained arm `α`, write `p = α(v)` and let `u = u(a)`. One has `u ≤ v` because
> `p ∈ R_a`. If `u < v`, the distinct point `α(u)` was visited strictly before `a`, and reverse
> first-visit order gives `T(p) ≤ T(α(u)) < a`, a contradiction. Thus `u = v`. Its incoming endpoint
> maps to the fresh interior tip, so the deterministic fresh-tip lemma makes it `W_a`.

and the fresh-start case of **Proposition 1.5** (L251–L255): "If `η(a)` is fresh, use the chart
`g_a` itself. Its first incoming endpoint on an arm containing `η(a)` is a gate equal to
`W_a = δ_a(a)`, by Lemma 1.4. ... The version of Lemma 1.3 with a supplied initial gate yields
`δ_a(b) = δ_a(a)`. Applying `f_a` proves the equality."

Charts are centred: the driver `W_a` corresponds to `0`, and `δ_a(a) = 0`.

## Main results

* `notMem_trace_of_fresh`: reverse first-visit order and freshness: the prefix before a fresh
  point is unvisited (a corollary of PROVE-R16's `R16.firstVisitParam_eq_of_fresh`);
* `subset_domain_of_isPreconnected`: a connected unvisited set meeting `D_a` lies in `D_a`
  ("a prefix ... cannot enter a swallowed component before meeting its boundary trace");
* `fresh_attachment`: **Lemma 1.4** (contained arms): the prefix lies in `D_a` and its lift
  converges to `0` (`= W_a`, centred);
* `ownFuture_gap_eq_of_pocket_fresh`: **Proposition 1.5, fresh start**, from the physical pocket
  data in the chart at `a`.

The outer-arm case of Lemma 1.4 uses the exterior Jordan embedding of Aux. lemma 31, which has no
Lean statement; it is not treated here.
-/

set_option autoImplicit false

noncomputable section

open Complex Set Metric Filter Topology Bornology

open QuantumZipper (H Hbar fwdHull fwdMap fwdMapInv)
open InteractingSLE.YuanSimpleApprox (trMap)

namespace InteractingSLE.Sec6

variable {W : ℝ → ℝ} {η : ℝ → ℂ}

/-- **Lemma 1.4, the order step**, as an unvisited prefix: under reverse first-visit order
(`R16.IsReverseVisitOrder`), if `η(a) = α(v)` is a fresh point then no point of `α([0, v))` is
visited by time `a`. A corollary of PROVE-R16's `R16.firstVisitParam_eq_of_fresh` (`u(a) = v`). -/
theorem notMem_trace_of_fresh {α : ℝ → ℂ} (hαi : InjOn α (Icc 0 1))
    (hrev : R16.IsReverseVisitOrder α fun t => η '' Icc 0 t) {a v : ℝ} (ha : 0 ≤ a)
    (hv : v ∈ Icc (0 : ℝ) 1) (hav : η a = α v) (hfresh : η a ∉ η '' Ico 0 a) :
    ∀ v' ∈ Ico 0 v, α v' ∉ η '' Icc 0 a := by
  intro v' hv' hvis
  have hu := R16.firstVisitParam_eq_of_fresh hαi hrev ha hv hav hfresh
  have h2 : R7.firstVisitParam α (fun t => η '' Icc 0 t) a ≤ v' :=
    csInf_le (R7.bddBelow_firstVisitSet α (fun t => η '' Icc 0 t) a)
      ⟨⟨hv'.1, hv'.2.le.trans hv.2⟩, hvis⟩
  rw [hu] at h2
  linarith [hv'.2]

/-- A preconnected subset of `ℍ` avoiding `R_a = η([0, a])` and meeting `D_a = ℍ \ K_a` lies in
`D_a`. -/
theorem subset_domain_of_isPreconnected (hη : IsLoewnerTrace W η) {a : ℝ} (ha : 0 ≤ a)
    {S : Set ℂ} (hS : IsPreconnected S) (hSH : S ⊆ H) (hSR : Disjoint S (η '' Icc 0 a))
    {p : ℂ} (hpS : p ∈ S) (hpD : p ∈ H \ fwdHull W a) : S ⊆ H \ fwdHull W a := by
  rw [hη.2.2 a ha] at hpD ⊢
  have hRc : IsCompact (η '' Icc 0 a) :=
    isCompact_Icc.image_of_continuousOn (hη.2.1.mono fun t ht => ht.1)
  obtain ⟨ρ, hρ, hρR⟩ := exists_closure_subset_ball hRc.isBounded
  rw [H_diff_fillH hρ hρR] at hpD ⊢
  rw [connectedComponentIn_eq hpD]
  refine hS.subset_connectedComponentIn hpS fun z hz => ⟨hSH hz, ?_⟩
  rw [hRc.isClosed.closure_eq]
  exact Set.disjoint_left.1 hSR hz

/-- Visited points of `ℍ` are not in `D_a`. -/
theorem notMem_domain_of_mem_trace (hη : IsLoewnerTrace W η) {a : ℝ} (ha : 0 ≤ a) {p : ℂ}
    (hp : p ∈ η '' Icc 0 a) : p ∉ H \ fwdHull W a := by
  rintro ⟨hpH, hpK⟩
  rw [hη.2.2 a ha] at hpK
  exact hpK ⟨hpH, Or.inl (subset_closure hp)⟩

/-- **Lemma 1.4** (a fresh boundary visit is a current attachment; contained arms), in the form
used by the chart-face geometry. Let `α` be continuous and injective on `[0, 1]` in reverse
first-visit order, `0 ≤ c < v ≤ 1`, `α([c, v)) ⊆ ℍ` and `α(c) ∈ D_a`. If `η(a) = α(v)` is a fresh
interior point, `a > 0`, then the prefix `α([c, v))` lies in `D_a` (so `α(v)` is the current
first-visit attachment), `α(v) ∉ D_a`, and the lifted prefix converges to `0`, the centred driver
`W_a`. (PROVE-R16's `R16.lemma14_contained` gives `u(a) = v` and the gate equation; the domain
statement and the convergence of the lift are added here.) -/
theorem fresh_attachment (hη : IsLoewnerTrace W η) (hW : Continuous W) (hW0 : W 0 = 0) {a : ℝ}
    (ha : 0 < a) {α : ℝ → ℂ} {c v : ℝ} (hα : ContinuousOn α (Icc 0 1))
    (hαi : InjOn α (Icc 0 1)) (hrev : R16.IsReverseVisitOrder α fun t => η '' Icc 0 t)
    (hc0 : 0 ≤ c) (hcv : c < v) (hv1 : v ≤ 1) (hav : η a = α v) (haH : η a ∈ H)
    (hfresh : η a ∉ η '' Ico 0 a) (hαH : ∀ v' ∈ Ico c v, α v' ∈ H)
    (hc : α c ∈ H \ fwdHull W a) :
    (∀ v' ∈ Ico c v, α v' ∈ H \ fwdHull W a) ∧ α v ∉ H \ fwdHull W a ∧
      Tendsto (fun v' => fwdMap W a (α v')) (𝓝[<] v) (𝓝 0) := by
  have hvI : v ∈ Icc (0 : ℝ) 1 := ⟨hc0.trans hcv.le, hv1⟩
  have hun := notMem_trace_of_fresh hαi hrev ha.le hvI hav hfresh
  have hsub : Icc c v ⊆ Icc 0 1 := fun t ht => ⟨hc0.trans ht.1, ht.2.trans hv1⟩
  have hS : IsPreconnected (α '' Ico c v) :=
    isPreconnected_Ico.image α (hα.mono fun t ht => hsub ⟨ht.1, ht.2.le⟩)
  have hD : α '' Ico c v ⊆ H \ fwdHull W a :=
    subset_domain_of_isPreconnected hη ha.le hS (by rintro _ ⟨t, ht, rfl⟩; exact hαH t ht)
      (Set.disjoint_left.2 (by
        rintro _ ⟨t, ht, rfl⟩; exact hun t ⟨hc0.trans ht.1, ht.2⟩))
      ⟨c, ⟨le_rfl, hcv⟩, rfl⟩ hc
  have hD' : ∀ v' ∈ Ico c v, α v' ∈ H \ fwdHull W a := fun v' hv' => hD ⟨v', hv', rfl⟩
  have hvD : α v ∉ H \ fwdHull W a :=
    notMem_domain_of_mem_trace hη ha.le ⟨a, ⟨ha.le, le_rfl⟩, hav⟩
  obtain ⟨q, hq, hlim⟩ := exists_tendsto_lift hη hW hW0 ha.le hcv (hα.mono hsub) hD' hvD
  have hq0 : q = 0 := fresh_tip_fibre hη hW hW0 ha haH hfresh (by rw [hq, hav])
  refine ⟨hD', hvD, ?_⟩
  rw [hq0, ofReal_zero] at hlim
  exact hlim

/-- **Proposition 1.5, fresh start, distinct gates `q₁ < q₂`, in the chart at the gap start `a`**:
the arm data as in `ownFuture_gap_eq_of_arms_lt` (now at chart time `a`), one gate equal to `0`
(`= δ_a(a)`, supplied by Lemma 1.4), and only the final endpoint `b` approached by `C`-visits. -/
theorem ownFuture_gap_eq_of_arms_lt_of_gate (hη : IsLoewnerTrace W η) (hW : Continuous W)
    (hW0 : W 0 = 0) {C : Set ℂ} (hC : IsOpen C) (hCb : IsBounded C) {α₁ α₂ β : ℝ → ℂ}
    {c₁ u₁ e₁ c₂ u₂ e₂ : ℝ} (hcu₁ : c₁ < u₁) (hue₁ : u₁ ≤ e₁) (hue₂ : u₂ ≤ e₂)
    (hfrC : frontier C = α₁ '' Icc c₁ e₁ ∪ α₂ '' Icc c₂ e₂)
    (h12 : ∀ v ∈ Ico c₁ u₁, ∀ v' ∈ Ico c₂ u₂, α₁ v = α₂ v' → α₁ v = α₁ c₁)
    (h13 : ∀ v ∈ Ico c₁ u₁, ∀ τ ∈ Ici (0 : ℝ), α₁ v = β τ → α₁ v = α₁ c₁)
    (h23 : ∀ v ∈ Ico c₂ u₂, ∀ τ ∈ Ici (0 : ℝ), α₂ v = β τ → α₂ v = α₁ c₁)
    (hβ : ContinuousOn β (Ici 0)) (hβi : InjOn β (Ici 0)) (hβ0 : β 0 = α₁ c₁)
    (hβt : Tendsto (fun t => ‖β t‖) atTop atTop) {s a b : ℝ} (hs : 0 ≤ s) (hsa : s ≤ a)
    (hab : a < b) (hα₁D : ∀ v ∈ Ico c₁ u₁, α₁ v ∈ H \ fwdHull W a)
    (hα₂D : ∀ v ∈ Ico c₂ u₂, α₂ v ∈ H \ fwdHull W a)
    (hα₁K : ∀ v ∈ Icc u₁ e₁, α₁ v ∉ H \ fwdHull W a)
    (hα₂K : ∀ v ∈ Icc u₂ e₂, α₂ v ∉ H \ fwdHull W a)
    (hβD : ∀ τ ∈ Ici (0 : ℝ), β τ ∈ H \ fwdHull W a) {q₁ q₂ : ℝ} {a₁ a₂ : ℝ → ℂ} (hq : q₁ < q₂)
    (ha₁ : ContinuousOn a₁ (Icc 0 1)) (ha₂ : ContinuousOn a₂ (Icc 0 1))
    (ha₁i : InjOn a₁ (Icc 0 1)) (ha₂i : InjOn a₂ (Icc 0 1)) (ha₁0 : a₁ 0 = q₁)
    (ha₂0 : a₂ 0 = q₂) (ha₁1 : a₁ 1 = fwdMap W a (α₁ c₁)) (ha₂1 : a₂ 1 = fwdMap W a (α₁ c₁))
    (ha₁H : ∀ t ∈ Ioc (0 : ℝ) 1, a₁ t ∈ H) (ha₂H : ∀ t ∈ Ioc (0 : ℝ) 1, a₂ t ∈ H)
    (ha₁img : a₁ '' Ioc 0 1 = fwdMap W a '' (α₁ '' Ico c₁ u₁))
    (ha₂img : a₂ '' Ioc 0 1 = fwdMap W a '' (α₂ '' Ico c₂ u₂))
    (hgate : q₁ = 0 ∨ q₂ = 0)
    (hgap : ∀ t ∈ Icc a b, η t ∉ C) (hunv₁ : ∀ t ∈ Icc a b, ∀ v ∈ Ico c₁ u₁, η t ≠ α₁ v)
    (hunv₂ : ∀ t ∈ Icc a b, ∀ v ∈ Ico c₂ u₂, η t ≠ α₂ v)
    (hunv₃ : ∀ t ∈ Icc a b, ∀ τ ∈ Ici (0 : ℝ), η t ≠ β τ)
    (hb : b ∈ closure {t | a < t ∧ η t ∈ C}) :
    trMap W s a 0 = trMap W s b 0 ∧ η a = η b := by
  have ha0 : 0 ≤ a := hs.trans hsa
  obtain ⟨ha₃, ha₃i, ha₃H, ha₃t⟩ := thirdArm_props hW hW0 ha0 hβ hβi hβD hβt
  set a₃ : ℝ → ℂ := fun t => fwdMap W a (β t) with ha₃def
  have ha₃img : a₃ '' Ici 0 = fwdMap W a '' (β '' Ici 0) := (image_image _ _ _).symm
  have ha₃0 : a₃ 0 = fwdMap W a (α₁ c₁) := by simp only [ha₃def, hβ0]
  have hopenH : ∀ {a : ℝ → ℂ}, (∀ t ∈ Ioc (0 : ℝ) 1, a t ∈ H) → ∀ w ∈ a '' Ioc 0 1, w ∈ H := by
    rintro a haH _ ⟨t, ht, rfl⟩; exact haH t ht
  have hq₁₂ : (q₁ : ℂ) ≠ q₂ := fun h => by have := ofReal_injective h; linarith
  have h12' : a₁ '' Icc 0 1 ∩ a₂ '' Icc 0 1 ⊆ {fwdMap W a (α₁ c₁)} := by
    rintro w ⟨hw₁, hw₂⟩
    rcases eq_or_mem_open_arm ha₁0 hw₁ with h | h
    · exact absurd (h.symm.trans (arm_real ha₂0 ha₂H hw₂ (by rw [h]; simp))) hq₁₂
    rcases eq_or_mem_open_arm ha₂0 hw₂ with h' | h'
    · exact absurd (h' ▸ hopenH ha₁H w h) (not_mem_H_ofReal q₂)
    rw [ha₁img] at h; rw [ha₂img] at h'
    exact lift_inter_eq hW ha0 hα₁D hα₂D h12 h h'
  have h13' : a₁ '' Icc 0 1 ∩ a₃ '' Ici 0 ⊆ {fwdMap W a (α₁ c₁)} := by
    rintro w ⟨hw₁, hw₃⟩
    have hw₃H : w ∈ H := by obtain ⟨t, ht, rfl⟩ := hw₃; exact ha₃H t ht
    rcases eq_or_mem_open_arm ha₁0 hw₁ with h | h
    · exact absurd (h ▸ hw₃H) (not_mem_H_ofReal q₁)
    rw [ha₁img] at h; rw [ha₃img] at hw₃
    exact lift_inter_eq hW ha0 hα₁D hβD h13 h hw₃
  have h23' : a₂ '' Icc 0 1 ∩ a₃ '' Ici 0 ⊆ {fwdMap W a (α₁ c₁)} := by
    rintro w ⟨hw₂, hw₃⟩
    have hw₃H : w ∈ H := by obtain ⟨t, ht, rfl⟩ := hw₃; exact ha₃H t ht
    rcases eq_or_mem_open_arm ha₂0 hw₂ with h | h
    · exact absurd (h ▸ hw₃H) (not_mem_H_ofReal q₂)
    rw [ha₂img] at h; rw [ha₃img] at hw₃
    exact lift_inter_eq hW ha0 hα₂D hβD h23 h hw₃
  obtain ⟨hΓJ, hΓH⟩ := isJordanCurve_faceBoundary hq ha₁ ha₂ ha₁i ha₂i ha₁0 ha₂0 ha₁1 ha₂1 ha₁H
    ha₂H h12'
  have hiff := fun w (hw : w ∈ H) => trMap_mem_iff_innerSide hη hW hW0 ha0 hC hCb hcu₁ hue₁ hue₂
    hfrC hα₁D hα₂D hα₁K hα₂K hq ha₁ ha₂ ha₁i ha₂i ha₁0 ha₂0 ha₁1 ha₂1 ha₁H ha₂H h12' ha₁img
    ha₂img hw
  set δ : ℝ → ℂ := fun t => trMap W a t 0 with hδ
  have h11 : ∀ t, a ≤ t → η t ∈ C → δ t ∈ H →
      δ t ∈ innerSide (a₁ '' Icc 0 1 ∪ a₂ '' Icc 0 1 ∪ ofReal '' Icc q₁ q₂) := by
    intro t hat htC hδH
    exact (hiff _ hδH).1 (by rw [hδ, traceMapOut_trMap_zero hη hW hW0 ha0 hat]; exact htC)
  have hδF : ∀ t ∈ Icc a b,
      δ t ∉ innerSide (a₁ '' Icc 0 1 ∪ a₂ '' Icc 0 1 ∪ ofReal '' Icc q₁ q₂) := by
    intro t ht hF
    have := (hiff _ (innerSide_subset_H hΓJ hΓH hF)).2 hF
    rw [hδ, traceMapOut_trMap_zero hη hW hW0 ha0 ht.1] at this
    exact hgap t ht this
  have hδa : trMap W a a 0 = 0 := YuanSimpleApprox.trMap_self hW a zero_mem_Hbar
  have heq := gate_lemma_of_gate hq ha₁ ha₂ ha₁i ha₂i ha₁0 ha₂0 ha₁1 ha₂1 ha₁H ha₂H h12' ha₃ ha₃i
    ha₃0 ha₃H ha₃t h13' h23' hab
    ((YuanSimpleApprox.continuousOn_trMap_zero hη hW hW0 ha0).mono fun t ht => ht.1)
    (fun t ht => YuanSimpleApprox.trMap_zero_mem_Hbar hη hW hW0 ha0 ht.1) hδF
    (fun t ht h => by
      rw [ha₁img] at h
      exact ownFuture_notMem_lift hη hW hW0 ha0 ht.1 hα₁D (hunv₁ t ht) h)
    (fun t ht h => by
      rw [ha₂img] at h
      exact ownFuture_notMem_lift hη hW hW0 ha0 ht.1 hα₂D (hunv₂ t ht) h)
    (fun t ht h => by
      rw [ha₃img] at h
      exact ownFuture_notMem_lift hη hW hW0 ha0 ht.1 hβD (hunv₃ t ht) h)
    (fun c d hac hcd _ => ownFuture_not_forall_real hη hW hW0 ha0 hac hcd)
    (by rw [hδa]; rcases hgate with h | h
        · left; rw [h, ofReal_zero]
        · right; rw [h, ofReal_zero])
    (ownFuture_mem_closure_face hη hW hW0 hC ha0 h11 hb)
  exact ownFuture_and_trace_eq hη hW hW0 hs hsa le_rfl hab.le heq

/-- **Proposition 1.5, fresh start, equal gates** `q₁ = q₂ = q = 0`: `δ_a(b)` is the common gate,
which is `δ_a(a) = 0`. -/
theorem ownFuture_gap_eq_of_arms_eq_of_gate (hη : IsLoewnerTrace W η) (hW : Continuous W)
    (hW0 : W 0 = 0) {C : Set ℂ} (hC : IsOpen C) (hCb : IsBounded C) {α₁ α₂ : ℝ → ℂ}
    {c₁ u₁ e₁ c₂ u₂ e₂ : ℝ} (hcu₁ : c₁ < u₁) (hue₁ : u₁ ≤ e₁) (hue₂ : u₂ ≤ e₂)
    (hfrC : frontier C = α₁ '' Icc c₁ e₁ ∪ α₂ '' Icc c₂ e₂)
    (h12 : ∀ v ∈ Ico c₁ u₁, ∀ v' ∈ Ico c₂ u₂, α₁ v = α₂ v' → α₁ v = α₁ c₁)
    {s a b : ℝ} (hs : 0 ≤ s) (hsa : s ≤ a) (hab : a ≤ b)
    (hα₁D : ∀ v ∈ Ico c₁ u₁, α₁ v ∈ H \ fwdHull W a)
    (hα₂D : ∀ v ∈ Ico c₂ u₂, α₂ v ∈ H \ fwdHull W a)
    (hα₁K : ∀ v ∈ Icc u₁ e₁, α₁ v ∉ H \ fwdHull W a)
    (hα₂K : ∀ v ∈ Icc u₂ e₂, α₂ v ∉ H \ fwdHull W a) {a₁ a₂ : ℝ → ℂ}
    (ha₁ : ContinuousOn a₁ (Icc 0 1)) (ha₂ : ContinuousOn a₂ (Icc 0 1))
    (ha₁i : InjOn a₁ (Icc 0 1)) (ha₂i : InjOn a₂ (Icc 0 1)) (ha₁0 : a₁ 0 = (0 : ℝ))
    (ha₂0 : a₂ 0 = (0 : ℝ)) (ha₁1 : a₁ 1 = fwdMap W a (α₁ c₁))
    (ha₂1 : a₂ 1 = fwdMap W a (α₁ c₁))
    (ha₁H : ∀ t ∈ Ioc (0 : ℝ) 1, a₁ t ∈ H) (ha₂H : ∀ t ∈ Ioc (0 : ℝ) 1, a₂ t ∈ H)
    (ha₁img : a₁ '' Ioc 0 1 = fwdMap W a '' (α₁ '' Ico c₁ u₁))
    (ha₂img : a₂ '' Ioc 0 1 = fwdMap W a '' (α₂ '' Ico c₂ u₂))
    (hgapb : η b ∉ C) (hunv₁ : ∀ v ∈ Ico c₁ u₁, η b ≠ α₁ v)
    (hunv₂ : ∀ v ∈ Ico c₂ u₂, η b ≠ α₂ v)
    (hb : b ∈ closure {t | a < t ∧ η t ∈ C}) :
    trMap W s a 0 = trMap W s b 0 ∧ η a = η b := by
  have ha0 : 0 ≤ a := hs.trans hsa
  have h12' : a₁ '' Icc 0 1 ∩ a₂ '' Icc 0 1 ⊆ {((0 : ℝ) : ℂ), fwdMap W a (α₁ c₁)} := by
    rintro w ⟨hw₁, hw₂⟩
    rcases eq_or_mem_open_arm ha₁0 hw₁ with h | h
    · exact Or.inl h
    rcases eq_or_mem_open_arm ha₂0 hw₂ with h' | h'
    · exact Or.inl h'
    rw [ha₁img] at h; rw [ha₂img] at h'
    exact Or.inr (lift_inter_eq hW ha0 hα₁D hα₂D h12 h h')
  have hΓJ := Sec7.isJordanCurve_image_union ha₁ ha₂ ha₁i ha₂i (by rw [ha₁0, ha₂0])
    (by rw [ha₁1, ha₂1]) (by rw [ha₁0, ha₁1]; exact h12')
  have hΓH : a₁ '' Icc 0 1 ∪ a₂ '' Icc 0 1 ⊆ Hbar :=
    union_subset (image_arm_subset_Hbar ha₁0 ha₁H) (image_arm_subset_Hbar ha₂0 ha₂H)
  have hiff := fun w (hw : w ∈ H) => trMap_mem_iff_innerSide_eq hη hW hW0 ha0 hC hCb hcu₁ hue₁
    hue₂ hfrC hα₁D hα₂D hα₁K hα₂K ha₁ ha₂ ha₁i ha₂i ha₁0 ha₂0 ha₁1 ha₂1 ha₁H ha₂H h12' ha₁img
    ha₂img hw
  have h11 : ∀ t, a ≤ t → η t ∈ C → trMap W a t 0 ∈ H →
      trMap W a t 0 ∈ innerSide (a₁ '' Icc 0 1 ∪ a₂ '' Icc 0 1) := by
    intro t hat htC hδH
    exact (hiff _ hδH).1 (by rw [traceMapOut_trMap_zero hη hW hW0 ha0 hat]; exact htC)
  have hFb : trMap W a b 0 ∉ innerSide (a₁ '' Icc 0 1 ∪ a₂ '' Icc 0 1) := by
    intro hF
    have := (hiff _ (innerSide_subset_H hΓJ hΓH hF)).2 hF
    rw [traceMapOut_trMap_zero hη hW hW0 ha0 hab] at this
    exact hgapb this
  have hcl := ownFuture_mem_closure_face hη hW hW0 hC ha0 h11 hb
  have hA : ∀ t ∈ ({b, b} : Set ℝ), trMap W a t 0 ∉ a₁ '' Ioc 0 1 ∪ a₂ '' Ioc 0 1 := by
    intro t ht h
    have htb : t = b := by rcases ht with rfl | rfl <;> rfl
    subst htb
    rcases h with h | h
    · rw [ha₁img] at h
      exact ownFuture_notMem_lift hη hW hW0 ha0 hab hα₁D hunv₁ h
    · rw [ha₂img] at h
      exact ownFuture_notMem_lift hη hW hW0 ha0 hab hα₂D hunv₂ h
  have h := gate_lemma_eq (δ := fun t => trMap W a t 0) (a := b) (b := b) rfl
    (isCompact_of_isJordanCurve hΓJ).isClosed ha₁0 ha₂0 hFb hFb
    (fun t ht h => hA t ht (Or.inl h)) (fun t ht h => hA t ht (Or.inr h)) hcl hcl
  have hδa : trMap W a a 0 = ((0 : ℝ) : ℂ) := by
    rw [ofReal_zero]; exact YuanSimpleApprox.trMap_self hW a zero_mem_Hbar
  exact ownFuture_and_trace_eq hη hW hW0 hs hsa le_rfl hab (hδa.trans h.1.symm)

/-- **Proposition 1.5, fresh start, from the physical pocket** (finite junction; ruling R41's note,
L251–L255). The pocket data are as in `ownFuture_gap_eq_of_pocket`, now in the chart at the gap
start `a > 0`. If `η(a)` is a fresh interior point and is the current attachment on one of the
arms (`η(a) = α₁(u₁)` or `η(a) = α₂(u₂)`; Lemma 1.4, `fresh_attachment`, gives this from reverse
first-visit order), the trace avoids `C` and the unvisited pieces on `[a, b]`, and `b` is a limit
of `C`-visits after `a`, then `δ_s(a) = δ_s(b)` for every `0 ≤ s ≤ a`, and `η(a) = η(b)`. -/
theorem ownFuture_gap_eq_of_pocket_fresh (hη : IsLoewnerTrace W η) (hW : Continuous W)
    (hW0 : W 0 = 0) {C : Set ℂ} (hC : IsOpen C) (hCb : IsBounded C) {α₁ α₂ β : ℝ → ℂ}
    {c₁ u₁ e₁ c₂ u₂ e₂ : ℝ} (hcu₁ : c₁ < u₁) (hcu₂ : c₂ < u₂) (hue₁ : u₁ ≤ e₁) (hue₂ : u₂ ≤ e₂)
    (hα₁ : ContinuousOn α₁ (Icc c₁ u₁)) (hα₂ : ContinuousOn α₂ (Icc c₂ u₂))
    (hα₁i : InjOn α₁ (Icc c₁ u₁)) (hα₂i : InjOn α₂ (Icc c₂ u₂)) (hx₀ : α₁ c₁ = α₂ c₂)
    (hfrC : frontier C = α₁ '' Icc c₁ e₁ ∪ α₂ '' Icc c₂ e₂)
    (h12 : ∀ v ∈ Ico c₁ u₁, ∀ v' ∈ Ico c₂ u₂, α₁ v = α₂ v' → α₁ v = α₁ c₁)
    (hβ : ContinuousOn β (Ici 0)) (hβi : InjOn β (Ici 0)) (hβ0 : β 0 = α₁ c₁)
    (hβt : Tendsto (fun t => ‖β t‖) atTop atTop)
    (h13 : ∀ v ∈ Ico c₁ u₁, ∀ τ ∈ Ici (0 : ℝ), α₁ v = β τ → α₁ v = α₁ c₁)
    (h23 : ∀ v ∈ Ico c₂ u₂, ∀ τ ∈ Ici (0 : ℝ), α₂ v = β τ → α₂ v = α₁ c₁)
    {s a b : ℝ} (hs : 0 ≤ s) (hsa : s ≤ a) (ha : 0 < a) (hab : a < b)
    (hα₁D : ∀ v ∈ Ico c₁ u₁, α₁ v ∈ H \ fwdHull W a)
    (hα₂D : ∀ v ∈ Ico c₂ u₂, α₂ v ∈ H \ fwdHull W a)
    (hα₁K : ∀ v ∈ Icc u₁ e₁, α₁ v ∉ H \ fwdHull W a)
    (hα₂K : ∀ v ∈ Icc u₂ e₂, α₂ v ∉ H \ fwdHull W a)
    (hβD : ∀ τ ∈ Ici (0 : ℝ), β τ ∈ H \ fwdHull W a)
    (haH : η a ∈ H) (hfresh : η a ∉ η '' Ico 0 a) (hatt : η a = α₁ u₁ ∨ η a = α₂ u₂)
    (hgap : ∀ t ∈ Icc a b, η t ∉ C) (hunv₁ : ∀ t ∈ Icc a b, ∀ v ∈ Ico c₁ u₁, η t ≠ α₁ v)
    (hunv₂ : ∀ t ∈ Icc a b, ∀ v ∈ Ico c₂ u₂, η t ≠ α₂ v)
    (hunv₃ : ∀ t ∈ Icc a b, ∀ τ ∈ Ici (0 : ℝ), η t ≠ β τ)
    (hb : b ∈ closure {t | a < t ∧ η t ∈ C}) :
    trMap W s a 0 = trMap W s b 0 ∧ η a = η b := by
  obtain ⟨q₁, a₁, ha₁, ha₁i, ha₁0, ha₁1, ha₁H, hq₁, ha₁img⟩ :=
    exists_arm hη hW hW0 ha.le hcu₁ hα₁ hα₁i hα₁D (hα₁K u₁ ⟨le_rfl, hue₁⟩)
  obtain ⟨q₂, a₂, ha₂, ha₂i, ha₂0, ha₂1, ha₂H, hq₂, ha₂img⟩ :=
    exists_arm hη hW hW0 ha.le hcu₂ hα₂ hα₂i hα₂D (hα₂K u₂ ⟨le_rfl, hue₂⟩)
  have ha₂1' : a₂ 1 = fwdMap W a (α₁ c₁) := by rw [ha₂1, hx₀]
  have hgate : q₁ = 0 ∨ q₂ = 0 := by
    rcases hatt with h | h
    · exact Or.inl (fresh_tip_fibre hη hW hW0 ha haH hfresh (hq₁.trans h.symm))
    · exact Or.inr (fresh_tip_fibre hη hW hW0 ha haH hfresh (hq₂.trans h.symm))
  rcases lt_trichotomy q₁ q₂ with hq | hq | hq
  · exact ownFuture_gap_eq_of_arms_lt_of_gate hη hW hW0 hC hCb hcu₁ hue₁ hue₂ hfrC h12 h13 h23
      hβ hβi hβ0 hβt hs hsa hab hα₁D hα₂D hα₁K hα₂K hβD hq ha₁ ha₂ ha₁i ha₂i ha₁0 ha₂0 ha₁1
      ha₂1' ha₁H ha₂H ha₁img ha₂img hgate hgap hunv₁ hunv₂ hunv₃ hb
  · subst hq
    have h0 : q₁ = 0 := hgate.elim id id
    subst h0
    exact ownFuture_gap_eq_of_arms_eq_of_gate hη hW hW0 hC hCb hcu₁ hue₁ hue₂ hfrC h12 hs hsa
      hab.le hα₁D hα₂D hα₁K hα₂K ha₁ ha₂ ha₁i ha₂i ha₁0 ha₂0 ha₁1 ha₂1' ha₁H ha₂H ha₁img ha₂img
      (hgap b ⟨hab.le, le_rfl⟩) (hunv₁ b ⟨hab.le, le_rfl⟩) (hunv₂ b ⟨hab.le, le_rfl⟩) hb
  · have hx₀' : α₂ c₂ = α₁ c₁ := hx₀.symm
    exact ownFuture_gap_eq_of_arms_lt_of_gate hη hW hW0 hC hCb hcu₂ hue₂ hue₁
      (by rw [hfrC, union_comm])
      (fun v hv v' hv' h => by rw [hx₀']; exact h.trans (h12 v' hv' v hv h.symm))
      (fun v hv τ hτ h => by rw [hx₀']; exact h23 v hv τ hτ h)
      (fun v hv τ hτ h => by rw [hx₀']; exact h13 v hv τ hτ h) hβ hβi (hβ0.trans hx₀) hβt hs
      hsa hab hα₂D hα₁D hα₂K hα₁K hβD hq ha₂ ha₁ ha₂i ha₁i ha₂0 ha₁0 ha₂1 (by rw [ha₁1, hx₀])
      ha₂H ha₁H ha₂img ha₁img hgate.symm hgap hunv₂ hunv₁ hunv₃ hb

end InteractingSLE.Sec6
