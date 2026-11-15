/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec6.Aux39Tree

/-!
# The fixed-chart gate lemma (Lemma 1.3 of the ZTip-elimination note)

Ruling R41 (`source/external/AstraIG1/ig1_ztip_elimination.txt` L140–L186):

> **Lemma 1.3** (The fixed-chart gate lemma). Let `F ⊂ ℍ` have the central Jordan-face geometry
> just described, with gates `q₁, q₂ ∈ ℝ`. If its interior junction `z` is finite, retain also the
> exterior arm from `z` to infinity. Call the resulting unvisited arms and junction the incoming
> tree. Let `δ : [a, b] → ℍ̄` be continuous, finite and bounded, where `a < b`. Suppose that:
> 1. `δ` avoids `F` on `[a, b]` and avoids the open incoming arms, their junction, and infinity
>    throughout that interval;
> 2. `δ` has no nontrivial time interval in `ℝ`;
> 3. `δ(a), δ(b) ∈ F̄`.
>
> Then `δ(a) = δ(b) ∈ {q₁, q₂}`. For the initial endpoint condition it is enough instead to know
> directly that `δ(a)` is one of the gates.

This file proves the lemma for a finite junction `z ∈ ℍ`, for distinct gates (`gate_lemma`,
`gate_lemma_of_gate`) and for equal gates (`gate_lemma_eq`). The central face is the inner side of
`Γ = A₁ ∪ A₂ ∪ [q₁, q₂]` (for equal gates `Γ = A₁ ∪ A₂`), where `A₁, A₂` are simple arms from
the gates to `z`, open in `ℍ`; the exterior arm `A₃` is a simple path in `ℍ` from `z` to `∞`.

## Main results

* `mem_frontier_of_mem_closure_innerSide`: `F̄ \ F ⊆ Γ`;
* `halfDisc_subset_innerSide`: every point of `(q₁, q₂)` has an upper half-disc in `F`;
* `gate_lemma`, `gate_lemma_of_gate`, `gate_lemma_eq`: **Lemma 1.3**.

The case of a junction at infinity (pocket target equal to the original target) is not treated
here.
-/

set_option autoImplicit false

noncomputable section

open Complex Set Metric Filter Topology Bornology

open QuantumZipper (H Hbar)

namespace InteractingSLE.Sec6

/-- Points of the closure of the inner side of a closed set `J` which are not on the inner side
lie on `J`. -/
theorem mem_of_mem_closure_innerSide {J : Set ℂ} (hJ : IsClosed J) {w : ℂ}
    (hw : w ∈ closure (innerSide J)) (hwF : w ∉ innerSide J) : w ∈ J := by
  by_contra hwJ
  have hO : w ∈ outerSide J := by
    have h : w ∈ Jᶜ := hwJ
    rw [compl_eq_innerSide_union_outerSide] at h
    exact h.resolve_left hwF
  have hOo : IsOpen (outerSide J) := hJ.isOpen_compl.connectedComponentIn
  obtain ⟨p, hpO, hpI⟩ := mem_closure_iff.1 hw _ hOo hO
  exact disjoint_innerSide_outerSide.le_bot ⟨hpI, hpO⟩

/-- A nondegenerate time interval inside `[a, b]` around any `t ∈ [a, b]` on which a continuous
path stays in a given neighbourhood of `δ t`. -/
theorem exists_Icc_of_continuousWithinAt {δ : ℝ → ℂ} {a b t ε : ℝ} (hab : a < b)
    (ht : t ∈ Icc a b) (hδ : ContinuousWithinAt δ (Icc a b) t) (hε : 0 < ε) :
    ∃ c d, a ≤ c ∧ c < d ∧ d ≤ b ∧ ∀ s ∈ Icc c d, dist (δ s) (δ t) < ε := by
  obtain ⟨η, hη, hηδ⟩ := Metric.continuousWithinAt_iff.1 hδ ε hε
  rcases lt_or_eq_of_le ht.2 with htb | htb
  · refine ⟨t, min b (t + η / 2), ht.1, lt_min htb (by linarith), min_le_left _ _,
      fun s hs => hηδ ⟨ht.1.trans hs.1, hs.2.trans (min_le_left _ _)⟩ ?_⟩
    rw [Real.dist_eq, abs_lt]
    have := min_le_right b (t + η / 2)
    constructor <;> linarith [hs.1, hs.2]
  · refine ⟨max a (t - η / 2), t, le_max_left _ _, max_lt (htb ▸ hab) (by linarith), ht.2,
      fun s hs => hηδ ⟨(le_max_left _ _).trans hs.1, hs.2.trans ht.2⟩ ?_⟩
    rw [Real.dist_eq, abs_lt]
    have := le_max_right a (t - η / 2)
    constructor <;> linarith [hs.1, hs.2]

section Gate

variable {q₁ q₂ : ℝ} {z : ℂ} {a₁ a₂ a₃ : ℝ → ℂ}

/-- Real points of an arm `a : [0, 1] → ℍ̄` with `a(0, 1] ⊆ ℍ` are its start. -/
theorem arm_real {a : ℝ → ℂ} {q : ℝ} (ha0 : a 0 = q) (haH : ∀ t ∈ Ioc (0 : ℝ) 1, a t ∈ H)
    {w : ℂ} (hw : w ∈ a '' Icc 0 1) (him : w.im = 0) : w = q := by
  obtain ⟨t, ht, rfl⟩ := hw
  rcases eq_or_lt_of_le ht.1 with h | h
  · rw [← h, ha0]
  · have : (0 : ℝ) < (a t).im := haH t ⟨h, ht.2⟩
    linarith

/-- **Every point of `(q₁, q₂)` has an upper half-disc in the central face.** -/
theorem halfDisc_subset_innerSide (ha₁ : ContinuousOn a₁ (Icc 0 1))
    (ha₂ : ContinuousOn a₂ (Icc 0 1)) (ha₁0 : a₁ 0 = q₁) (ha₂0 : a₂ 0 = q₂)
    (ha₁H : ∀ t ∈ Ioc (0 : ℝ) 1, a₁ t ∈ H) (ha₂H : ∀ t ∈ Ioc (0 : ℝ) 1, a₂ t ∈ H)
    (hΓ : LQGMetric.JordanMap.IsJordanCurve (a₁ '' Icc 0 1 ∪ a₂ '' Icc 0 1 ∪ ofReal '' Icc q₁ q₂))
    (hΓH : a₁ '' Icc 0 1 ∪ a₂ '' Icc 0 1 ∪ ofReal '' Icc q₁ q₂ ⊆ Hbar) {v : ℝ}
    (hv : v ∈ Ioo q₁ q₂) :
    ∃ ε > 0, ∀ w : ℂ, dist w v < ε → 0 < w.im →
      w ∈ innerSide (a₁ '' Icc 0 1 ∪ a₂ '' Icc 0 1 ∪ ofReal '' Icc q₁ q₂) := by
  set Γ := a₁ '' Icc 0 1 ∪ a₂ '' Icc 0 1 ∪ ofReal '' Icc q₁ q₂ with hΓdef
  obtain ⟨⟨x₁, hx₁, hin⟩, -, hfr, -, hIo, -, -, -, -⟩ := jordan_sides hΓ hΓH
  -- `v` is off the two arms
  have hA : IsCompact (a₁ '' Icc 0 1 ∪ a₂ '' Icc 0 1) :=
    (isCompact_Icc.image_of_continuousOn ha₁).union (isCompact_Icc.image_of_continuousOn ha₂)
  have hvA : (v : ℂ) ∉ a₁ '' Icc 0 1 ∪ a₂ '' Icc 0 1 := by
    rintro (h | h)
    · have := arm_real ha₁0 ha₁H h (by simp)
      have := ofReal_injective this; linarith [hv.1]
    · have := arm_real ha₂0 ha₂H h (by simp)
      have := ofReal_injective this; linarith [hv.2]
  obtain ⟨ε₀, hε₀, hε₀A⟩ := Metric.isOpen_iff.1 hA.isClosed.isOpen_compl (v : ℂ) hvA
  set ε := min ε₀ (min (v - q₁) (q₂ - v)) with hε
  have hεpos : 0 < ε := lt_min hε₀ (lt_min (by linarith [hv.1]) (by linarith [hv.2]))
  refine ⟨ε, hεpos, ?_⟩
  set B := ball (v : ℂ) ε ∩ H with hB
  have hBΓ : B ⊆ Γᶜ := by
    rintro w ⟨hwb, hwH⟩ hwΓ
    rcases hwΓ with hwA | hwS
    · exact hε₀A (ball_subset_ball (min_le_left _ _) hwb) hwA
    · have h1 : w.im = 0 := im_eq_zero_of_mem_ofReal_image hwS
      have h2 : (0 : ℝ) < w.im := hwH
      linarith
  have hBc : IsPreconnected B := ((convex_ball _ _).inter (convex_halfSpace_im_gt 0)).isPreconnected
  -- `v ∈ Γ = frontier F`, so `F` meets the ball, necessarily in `B`
  have hvΓ : (v : ℂ) ∈ frontier (innerSide Γ) := by
    rw [hfr]; exact Or.inr ⟨v, ⟨hv.1.le, hv.2.le⟩, rfl⟩
  obtain ⟨p, hpb, hpF⟩ := mem_closure_iff.1 (frontier_subset_closure hvΓ) _ isOpen_ball
    (mem_ball_self hεpos)
  have hpH : p ∈ H := innerSide_subset_H hΓ hΓH hpF
  have hsub := hBc.subset_connectedComponentIn (x := p) ⟨hpb, hpH⟩ hBΓ
  have hpcc : connectedComponentIn Γᶜ p = innerSide Γ := by
    rw [hin] at hpF ⊢; exact (connectedComponentIn_eq hpF).symm
  intro w hw hwim
  rw [← hpcc]
  exact hsub ⟨hw, hwim⟩

/-- The boundary `Γ = A₁ ∪ A₂ ∪ [q₁, q₂]` of the central face is a Jordan curve in `ℍ̄`. -/
theorem isJordanCurve_faceBoundary (hq : q₁ < q₂) (ha₁ : ContinuousOn a₁ (Icc 0 1))
    (ha₂ : ContinuousOn a₂ (Icc 0 1)) (ha₁i : InjOn a₁ (Icc 0 1)) (ha₂i : InjOn a₂ (Icc 0 1))
    (ha₁0 : a₁ 0 = q₁) (ha₂0 : a₂ 0 = q₂) (ha₁1 : a₁ 1 = z) (ha₂1 : a₂ 1 = z)
    (ha₁H : ∀ t ∈ Ioc (0 : ℝ) 1, a₁ t ∈ H) (ha₂H : ∀ t ∈ Ioc (0 : ℝ) 1, a₂ t ∈ H)
    (h12 : a₁ '' Icc 0 1 ∩ a₂ '' Icc 0 1 ⊆ {z}) :
    LQGMetric.JordanMap.IsJordanCurve (a₁ '' Icc 0 1 ∪ a₂ '' Icc 0 1 ∪ ofReal '' Icc q₁ q₂) ∧
      a₁ '' Icc 0 1 ∪ a₂ '' Icc 0 1 ∪ ofReal '' Icc q₁ q₂ ⊆ Hbar := by
  have hjvΓ : segPath (q₁ : ℂ) (q₂ : ℂ) 1 = a₂ 0 := by rw [segPath_one, ha₂0]
  have hSeg₀img : segPath (q₁ : ℂ) (q₂ : ℂ) '' Icc 0 1 = ofReal '' Icc q₁ q₂ :=
    image_segPath_ofReal hq.le
  have hJ := Sec7.isJordanCurve_image_union (u := a₁)
    (v := arcJoin (segPath (q₁ : ℂ) (q₂ : ℂ)) a₂) ha₁
    (continuousOn_arcJoin (continuous_segPath _ _).continuousOn ha₂ hjvΓ) ha₁i
    (injOn_arcJoin (injOn_segPath (by
        intro h; have := congrArg Complex.re h; simp at this; linarith)) ha₂i hjvΓ (by
        rintro w ⟨hw1, hw2⟩
        rw [hSeg₀img] at hw1
        rw [mem_singleton_iff, segPath_one,
          arm_real ha₂0 ha₂H hw2 (im_eq_zero_of_mem_ofReal_image hw1)]))
    (by rw [arcJoin_zero, segPath_zero, ha₁0])
    (by rw [arcJoin_one, ha₁1, ha₂1])
    (by
      rw [image_arcJoin hjvΓ, hSeg₀img, ha₁0, ha₁1]
      rintro w ⟨hw1, hw2 | hw2⟩
      · exact Or.inl (arm_real ha₁0 ha₁H hw1 (im_eq_zero_of_mem_ofReal_image hw2))
      · exact Or.inr (h12 ⟨hw1, hw2⟩))
  rw [image_arcJoin hjvΓ, hSeg₀img] at hJ
  have e : a₁ '' Icc 0 1 ∪ (ofReal '' Icc q₁ q₂ ∪ a₂ '' Icc 0 1) =
      a₁ '' Icc 0 1 ∪ a₂ '' Icc 0 1 ∪ ofReal '' Icc q₁ q₂ := by
    rw [union_comm (ofReal '' Icc q₁ q₂), union_assoc]
  rw [e] at hJ
  refine ⟨hJ, ?_⟩
  have hA : ∀ {a : ℝ → ℂ} {q : ℝ}, a 0 = q → (∀ t ∈ Ioc (0 : ℝ) 1, a t ∈ H) →
      a '' Icc 0 1 ⊆ Hbar := by
    rintro a q ha0 haH _ ⟨t, ht, rfl⟩
    rcases eq_or_lt_of_le ht.1 with h | h
    · rw [← h, ha0]; exact ofReal_mem_Hbar q
    · exact (show (0 : ℝ) < (a t).im from haH t ⟨h, ht.2⟩).le
  refine union_subset (union_subset (hA ha₁0 ha₁H) (hA ha₂0 ha₂H)) ?_
  rintro _ ⟨x, -, rfl⟩; exact ofReal_mem_Hbar x

/-- **The endpoints are gates** (step 1 of Lemma 1.3): a point of `F̄ \ F` off the open arms lies
on `[q₁, q₂]`. -/
theorem mem_Icc_of_mem_closure_face (ha₁0 : a₁ 0 = q₁) (ha₂0 : a₂ 0 = q₂)
    (hΓc : IsClosed (a₁ '' Icc 0 1 ∪ a₂ '' Icc 0 1 ∪ ofReal '' Icc q₁ q₂)) {w : ℂ}
    (hw : w ∈ closure (innerSide (a₁ '' Icc 0 1 ∪ a₂ '' Icc 0 1 ∪ ofReal '' Icc q₁ q₂)))
    (hwF : w ∉ innerSide (a₁ '' Icc 0 1 ∪ a₂ '' Icc 0 1 ∪ ofReal '' Icc q₁ q₂))
    (hw₁ : w ∉ a₁ '' Ioc 0 1) (hw₂ : w ∉ a₂ '' Ioc 0 1) (hq : q₁ ≤ q₂) :
    ∃ x ∈ Icc q₁ q₂, w = x := by
  rcases mem_of_mem_closure_innerSide hΓc hw hwF with (h | h) | h
  · obtain ⟨t, ht, rfl⟩ := h
    rcases eq_or_lt_of_le ht.1 with h0 | h0
    · exact ⟨q₁, ⟨le_rfl, hq⟩, by rw [← h0, ha₁0]⟩
    · exact absurd ⟨t, ⟨h0, ht.2⟩, rfl⟩ hw₁
  · obtain ⟨t, ht, rfl⟩ := h
    rcases eq_or_lt_of_le ht.1 with h0 | h0
    · exact ⟨q₂, ⟨hq, le_rfl⟩, by rw [← h0, ha₂0]⟩
    · exact absurd ⟨t, ⟨h0, ht.2⟩, rfl⟩ hw₂
  · obtain ⟨x, hx, rfl⟩ := h; exact ⟨x, hx, rfl⟩

/-- **No visit to `(q₁, q₂)`** (Lemma 1.3, "the identical argument at an interior time"): a
continuous path in `ℍ̄ \ F` without real time intervals never meets `(q₁, q₂)`. -/
theorem not_mem_Ioo_of_avoid_face {Γ : Set ℂ} {δ : ℝ → ℂ} {a b : ℝ} (hab : a < b)
    (hδ : ContinuousOn δ (Icc a b)) (hδF : ∀ t ∈ Icc a b, δ t ∉ innerSide Γ)
    (hδR : ∀ c d, a ≤ c → c < d → d ≤ b → ∃ t ∈ Icc c d, δ t ∈ H)
    (hhalf : ∀ v ∈ Ioo q₁ q₂, ∃ ε > 0, ∀ w : ℂ, dist w v < ε → 0 < w.im → w ∈ innerSide Γ)
    {t : ℝ} (ht : t ∈ Icc a b) : δ t ∉ ofReal '' Ioo q₁ q₂ := by
  rintro ⟨v, hv, hvt⟩
  obtain ⟨ε, hε, hεF⟩ := hhalf v hv
  obtain ⟨c, d, hac, hcd, hdb, hcl⟩ := exists_Icc_of_continuousWithinAt hab ht (hδ t ht) hε
  obtain ⟨s, hs, hsH⟩ := hδR c d hac hcd hdb
  have hs' : s ∈ Icc a b := ⟨hac.trans hs.1, hs.2.trans hdb⟩
  have h1 := hcl s hs
  rw [← hvt] at h1
  exact hδF s hs' (hεF _ h1 hsH)

/-- Truncation of the exterior arm at its first exit from `ball 0 R`. -/
theorem exists_truncation (ha₃ : ContinuousOn a₃ (Ici 0))
    (ha₃t : Tendsto (fun t => ‖a₃ t‖) atTop atTop) {R : ℝ} (h0R : ‖a₃ 0‖ < R) :
    ∃ τ > 0, ‖a₃ τ‖ = R ∧ ∀ t ∈ Ico 0 τ, ‖a₃ t‖ < R := by
  obtain ⟨T, hT⟩ := (ha₃t.eventually (eventually_ge_atTop R)).exists_forall_of_atTop
  set T' := max T 0 with hT'
  have hT'R : R ≤ ‖a₃ T'‖ := hT T' (le_max_left _ _)
  set S := {t ∈ Icc 0 T' | R ≤ ‖a₃ t‖} with hS
  have hSc : IsClosed S := by
    have hc : ContinuousOn (fun t => ‖a₃ t‖) (Icc 0 T') :=
      (ha₃.mono fun t ht => ht.1).norm
    exact hc.preimage_isClosed_of_isClosed isClosed_Icc isClosed_Ici
  have hSne : S.Nonempty := ⟨T', ⟨le_max_right _ _, le_rfl⟩, hT'R⟩
  have hSb : BddBelow S := ⟨0, fun t ht => ht.1.1⟩
  set τ := sInf S with hτ
  have hτS : τ ∈ S := hSc.csInf_mem hSne hSb
  have hτpos : 0 < τ := by
    rcases eq_or_lt_of_le hτS.1.1 with h | h
    · have := hτS.2; rw [← h] at this; linarith
    · exact h
  have hbelow : ∀ t ∈ Ico 0 τ, ‖a₃ t‖ < R := by
    intro t ht
    by_contra hge
    push Not at hge
    have : τ ≤ t := csInf_le hSb ⟨⟨ht.1, ht.2.le.trans hτS.1.2⟩, hge⟩
    linarith [ht.2]
  refine ⟨τ, hτpos, ?_, hbelow⟩
  -- the first hit is on the circle (intermediate value theorem)
  have hc : ContinuousOn (fun t => ‖a₃ t‖) (Icc 0 τ) := (ha₃.mono fun t ht => ht.1).norm
  obtain ⟨t, ht, htR⟩ := intermediate_value_Icc hτpos.le hc ⟨h0R.le, hτS.2⟩
  rcases eq_or_lt_of_le ht.2 with h | h
  · rw [← h]; exact htR
  · exact absurd htR (ne_of_lt (hbelow t ⟨ht.1, h⟩))

/-- **The two gate values agree** (the separation step of Lemma 1.3, finite junction). -/
theorem gate_eq_of_mem_gates (hq : q₁ < q₂) (ha₁ : ContinuousOn a₁ (Icc 0 1))
    (ha₂ : ContinuousOn a₂ (Icc 0 1)) (ha₁i : InjOn a₁ (Icc 0 1)) (ha₂i : InjOn a₂ (Icc 0 1))
    (ha₁0 : a₁ 0 = q₁) (ha₂0 : a₂ 0 = q₂) (ha₁1 : a₁ 1 = z) (ha₂1 : a₂ 1 = z)
    (ha₁H : ∀ t ∈ Ioc (0 : ℝ) 1, a₁ t ∈ H) (ha₂H : ∀ t ∈ Ioc (0 : ℝ) 1, a₂ t ∈ H)
    (h12 : a₁ '' Icc 0 1 ∩ a₂ '' Icc 0 1 ⊆ {z}) (ha₃ : ContinuousOn a₃ (Ici 0))
    (ha₃i : InjOn a₃ (Ici 0)) (ha₃0 : a₃ 0 = z) (ha₃H : ∀ t ∈ Ici (0 : ℝ), a₃ t ∈ H)
    (ha₃t : Tendsto (fun t => ‖a₃ t‖) atTop atTop) (h13 : a₁ '' Icc 0 1 ∩ a₃ '' Ici 0 ⊆ {z})
    (h23 : a₂ '' Icc 0 1 ∩ a₃ '' Ici 0 ⊆ {z}) {δ : ℝ → ℂ} {a b : ℝ} (hab : a ≤ b)
    (hδ : ContinuousOn δ (Icc a b)) (hδH : MapsTo δ (Icc a b) Hbar)
    (hδF : ∀ t ∈ Icc a b, δ t ∉ innerSide (a₁ '' Icc 0 1 ∪ a₂ '' Icc 0 1 ∪ ofReal '' Icc q₁ q₂))
    (hδA₃ : ∀ t ∈ Icc a b, δ t ∉ a₃ '' Ici 0)
    (hδI : ∀ t ∈ Icc a b, δ t ∉ ofReal '' Ioo q₁ q₂)
    (hδa : δ a = q₁ ∨ δ a = q₂) (hδb : δ b = q₁ ∨ δ b = q₂) : δ a = δ b := by
  by_contra hne
  have hqne : (q₁ : ℂ) ≠ q₂ := fun h => by have := ofReal_injective h; linarith
  set P := δ '' Icc a b with hP
  have hPc : IsCompact P := isCompact_Icc.image_of_continuousOn hδ
  have hq₁P : (q₁ : ℂ) ∈ P := by
    rcases hδa with h | h
    · exact ⟨a, ⟨le_rfl, hab⟩, h⟩
    · rcases hδb with h' | h'
      · exact ⟨b, ⟨hab, le_rfl⟩, h'⟩
      · exact absurd (h.trans h'.symm) hne
  have hq₂P : (q₂ : ℂ) ∈ P := by
    rcases hδa with h | h
    · rcases hδb with h' | h'
      · exact absurd (h.trans h'.symm) hne
      · exact ⟨b, ⟨hab, le_rfl⟩, h'⟩
    · exact ⟨a, ⟨le_rfl, hab⟩, h⟩
  -- a radius beyond `P` and the two arms
  have hK : IsCompact (P ∪ a₁ '' Icc 0 1 ∪ a₂ '' Icc 0 1) :=
    (hPc.union (isCompact_Icc.image_of_continuousOn ha₁)).union
      (isCompact_Icc.image_of_continuousOn ha₂)
  obtain ⟨M, hM⟩ := hK.isBounded.exists_norm_le
  set R := max M 0 + 1 with hR
  have hRpos : 0 < R := by positivity
  have hMR : ∀ w ∈ P ∪ a₁ '' Icc 0 1 ∪ a₂ '' Icc 0 1, ‖w‖ < R := fun w hw =>
    lt_of_le_of_lt ((hM w hw).trans (le_max_left _ _)) (lt_add_one _)
  have hz0 : ‖a₃ 0‖ < R := by
    rw [ha₃0]; exact hMR z (Or.inl (Or.inr ⟨1, ⟨zero_le_one, le_rfl⟩, ha₁1⟩))
  obtain ⟨τ, hτ, hτR, hτb⟩ := exists_truncation ha₃ ha₃t hz0
  set a₃' : ℝ → ℂ := fun t => a₃ (τ * t) with ha₃'
  have hmaps : MapsTo (fun t : ℝ => τ * t) (Icc 0 1) (Ici 0) := fun t ht =>
    mul_nonneg hτ.le ht.1
  have hsub₃ : a₃' '' Icc 0 1 ⊆ a₃ '' Ici 0 := by
    rintro _ ⟨t, ht, rfl⟩; exact ⟨τ * t, hmaps ht, rfl⟩
  refine false_of_isPreconnected_tree (q₁ := q₁) (q₂ := q₂) (R := R) (z := z) (e := a₃ τ)
    (a₁ := a₁) (a₂ := a₂) (a₃ := a₃') hq hRpos ha₁ ha₂
    (ha₃.comp (continuous_const.mul continuous_id).continuousOn hmaps) ha₁i ha₂i
    (fun t ht t' ht' h => by
      have := ha₃i (hmaps ht) (hmaps ht') h
      exact mul_left_cancel₀ hτ.ne' this)
    ha₁0 ha₂0 ha₁1 ha₂1 (by simp [ha₃', ha₃0]) (by simp [ha₃']) ha₁H ha₂H
    (fun t ht => ha₃H _ (hmaps ht))
    (fun t ht => hMR _ (Or.inl (Or.inr ⟨t, ht, rfl⟩)))
    (fun t ht => hMR _ (Or.inr ⟨t, ht, rfl⟩))
    (fun t ht => hτb _ ⟨mul_nonneg hτ.le ht.1, by nlinarith [ht.2]⟩) hτR h12
    (fun w hw => h13 ⟨hw.1, hsub₃ hw.2⟩) (fun w hw => h23 ⟨hw.1, hsub₃ hw.2⟩)
    (isPreconnected_Icc.image δ hδ) (fun w hw => mem_ball_zero_iff.2 (hMR w (Or.inl
      (Or.inl hw)))) (by rintro _ ⟨t, ht, rfl⟩; exact hδH ht) hq₁P hq₂P ?_ ?_ ?_
  · rw [Set.disjoint_left]; rintro _ ⟨t, ht, rfl⟩; exact hδF t ht
  · rw [Set.disjoint_left]; rintro _ ⟨t, ht, rfl⟩ h; exact hδA₃ t ht (hsub₃ h)
  · rw [Set.disjoint_left]; rintro _ ⟨t, ht, rfl⟩; exact hδI t ht

/-- **Lemma 1.3** (the fixed-chart gate lemma), finite junction, distinct gates `q₁ < q₂`. Let
`A₁, A₂` be simple arms from the gates to a junction `z`, open in `ℍ` and meeting only at `z`, and
`A₃` a simple path in `ℍ` from `z` to `∞` meeting them only at `z`; let `F` be the inner side of
`Γ = A₁ ∪ A₂ ∪ [q₁, q₂]`. Let `δ : [a, b] → ℍ̄` be continuous, avoid `F`, the open arms (and hence
the junction `z = a₁ 1`) and `A₃`, and have no nontrivial time interval in `ℝ`. If
`δ(a), δ(b) ∈ F̄`, then `δ(a) = δ(b) ∈ {q₁, q₂}`. -/
theorem gate_lemma (hq : q₁ < q₂) (ha₁ : ContinuousOn a₁ (Icc 0 1))
    (ha₂ : ContinuousOn a₂ (Icc 0 1)) (ha₁i : InjOn a₁ (Icc 0 1)) (ha₂i : InjOn a₂ (Icc 0 1))
    (ha₁0 : a₁ 0 = q₁) (ha₂0 : a₂ 0 = q₂) (ha₁1 : a₁ 1 = z) (ha₂1 : a₂ 1 = z)
    (ha₁H : ∀ t ∈ Ioc (0 : ℝ) 1, a₁ t ∈ H) (ha₂H : ∀ t ∈ Ioc (0 : ℝ) 1, a₂ t ∈ H)
    (h12 : a₁ '' Icc 0 1 ∩ a₂ '' Icc 0 1 ⊆ {z}) (ha₃ : ContinuousOn a₃ (Ici 0))
    (ha₃i : InjOn a₃ (Ici 0)) (ha₃0 : a₃ 0 = z) (ha₃H : ∀ t ∈ Ici (0 : ℝ), a₃ t ∈ H)
    (ha₃t : Tendsto (fun t => ‖a₃ t‖) atTop atTop) (h13 : a₁ '' Icc 0 1 ∩ a₃ '' Ici 0 ⊆ {z})
    (h23 : a₂ '' Icc 0 1 ∩ a₃ '' Ici 0 ⊆ {z}) {δ : ℝ → ℂ} {a b : ℝ} (hab : a < b)
    (hδ : ContinuousOn δ (Icc a b)) (hδH : MapsTo δ (Icc a b) Hbar)
    (hδF : ∀ t ∈ Icc a b, δ t ∉ innerSide (a₁ '' Icc 0 1 ∪ a₂ '' Icc 0 1 ∪ ofReal '' Icc q₁ q₂))
    (hδA₁ : ∀ t ∈ Icc a b, δ t ∉ a₁ '' Ioc 0 1) (hδA₂ : ∀ t ∈ Icc a b, δ t ∉ a₂ '' Ioc 0 1)
    (hδA₃ : ∀ t ∈ Icc a b, δ t ∉ a₃ '' Ici 0)
    (hδR : ∀ c d, a ≤ c → c < d → d ≤ b → ∃ t ∈ Icc c d, δ t ∈ H)
    (hδa : δ a ∈ closure (innerSide (a₁ '' Icc 0 1 ∪ a₂ '' Icc 0 1 ∪ ofReal '' Icc q₁ q₂)))
    (hδb : δ b ∈ closure (innerSide (a₁ '' Icc 0 1 ∪ a₂ '' Icc 0 1 ∪ ofReal '' Icc q₁ q₂))) :
    δ a = δ b ∧ (δ a = q₁ ∨ δ a = q₂) := by
  obtain ⟨hΓJ, hΓH⟩ := isJordanCurve_faceBoundary hq ha₁ ha₂ ha₁i ha₂i ha₁0 ha₂0 ha₁1 ha₂1 ha₁H
    ha₂H h12
  have hΓc := (isCompact_of_isJordanCurve hΓJ).isClosed
  have hhalf := fun v hv => halfDisc_subset_innerSide ha₁ ha₂ ha₁0 ha₂0 ha₁H ha₂H hΓJ hΓH
    (v := v) hv
  have hI : ∀ t ∈ Icc a b, δ t ∉ ofReal '' Ioo q₁ q₂ := fun t ht =>
    not_mem_Ioo_of_avoid_face hab hδ hδF hδR hhalf ht
  have hgate : ∀ t ∈ Icc a b, δ t ∈ closure (innerSide (a₁ '' Icc 0 1 ∪ a₂ '' Icc 0 1 ∪
      ofReal '' Icc q₁ q₂)) → δ t = q₁ ∨ δ t = q₂ := by
    intro t ht hcl
    obtain ⟨x, hx, hxt⟩ := mem_Icc_of_mem_closure_face ha₁0 ha₂0 hΓc hcl (hδF t ht)
      (hδA₁ t ht) (hδA₂ t ht) hq.le
    rcases eq_or_lt_of_le hx.1 with h | h
    · left; rw [hxt, h]
    rcases eq_or_lt_of_le hx.2 with h' | h'
    · right; rw [hxt, h']
    · exact absurd ⟨x, ⟨h, h'⟩, hxt.symm⟩ (hI t ht)
  have ha' := hgate a ⟨le_rfl, hab.le⟩ hδa
  have hb' := hgate b ⟨hab.le, le_rfl⟩ hδb
  exact ⟨gate_eq_of_mem_gates hq ha₁ ha₂ ha₁i ha₂i ha₁0 ha₂0 ha₁1 ha₂1 ha₁H ha₂H h12 ha₃ ha₃i ha₃0
    ha₃H ha₃t h13 h23 hab.le hδ hδH hδF hδA₃ hI ha' hb', ha'⟩

/-- **Lemma 1.3 with a supplied initial gate**: "For the initial endpoint condition it is enough
instead to know directly that `δ(a)` is one of the gates." -/
theorem gate_lemma_of_gate (hq : q₁ < q₂) (ha₁ : ContinuousOn a₁ (Icc 0 1))
    (ha₂ : ContinuousOn a₂ (Icc 0 1)) (ha₁i : InjOn a₁ (Icc 0 1)) (ha₂i : InjOn a₂ (Icc 0 1))
    (ha₁0 : a₁ 0 = q₁) (ha₂0 : a₂ 0 = q₂) (ha₁1 : a₁ 1 = z) (ha₂1 : a₂ 1 = z)
    (ha₁H : ∀ t ∈ Ioc (0 : ℝ) 1, a₁ t ∈ H) (ha₂H : ∀ t ∈ Ioc (0 : ℝ) 1, a₂ t ∈ H)
    (h12 : a₁ '' Icc 0 1 ∩ a₂ '' Icc 0 1 ⊆ {z}) (ha₃ : ContinuousOn a₃ (Ici 0))
    (ha₃i : InjOn a₃ (Ici 0)) (ha₃0 : a₃ 0 = z) (ha₃H : ∀ t ∈ Ici (0 : ℝ), a₃ t ∈ H)
    (ha₃t : Tendsto (fun t => ‖a₃ t‖) atTop atTop) (h13 : a₁ '' Icc 0 1 ∩ a₃ '' Ici 0 ⊆ {z})
    (h23 : a₂ '' Icc 0 1 ∩ a₃ '' Ici 0 ⊆ {z}) {δ : ℝ → ℂ} {a b : ℝ} (hab : a < b)
    (hδ : ContinuousOn δ (Icc a b)) (hδH : MapsTo δ (Icc a b) Hbar)
    (hδF : ∀ t ∈ Icc a b, δ t ∉ innerSide (a₁ '' Icc 0 1 ∪ a₂ '' Icc 0 1 ∪ ofReal '' Icc q₁ q₂))
    (hδA₁ : ∀ t ∈ Icc a b, δ t ∉ a₁ '' Ioc 0 1) (hδA₂ : ∀ t ∈ Icc a b, δ t ∉ a₂ '' Ioc 0 1)
    (hδA₃ : ∀ t ∈ Icc a b, δ t ∉ a₃ '' Ici 0)
    (hδR : ∀ c d, a ≤ c → c < d → d ≤ b → ∃ t ∈ Icc c d, δ t ∈ H)
    (hδa : δ a = q₁ ∨ δ a = q₂)
    (hδb : δ b ∈ closure (innerSide (a₁ '' Icc 0 1 ∪ a₂ '' Icc 0 1 ∪ ofReal '' Icc q₁ q₂))) :
    δ a = δ b := by
  obtain ⟨hΓJ, hΓH⟩ := isJordanCurve_faceBoundary hq ha₁ ha₂ ha₁i ha₂i ha₁0 ha₂0 ha₁1 ha₂1 ha₁H
    ha₂H h12
  have hΓc := (isCompact_of_isJordanCurve hΓJ).isClosed
  have hhalf := fun v hv => halfDisc_subset_innerSide ha₁ ha₂ ha₁0 ha₂0 ha₁H ha₂H hΓJ hΓH
    (v := v) hv
  have hI : ∀ t ∈ Icc a b, δ t ∉ ofReal '' Ioo q₁ q₂ := fun t ht =>
    not_mem_Ioo_of_avoid_face hab hδ hδF hδR hhalf ht
  have hb' : δ b = q₁ ∨ δ b = q₂ := by
    obtain ⟨x, hx, hxt⟩ := mem_Icc_of_mem_closure_face ha₁0 ha₂0 hΓc hδb
      (hδF b ⟨hab.le, le_rfl⟩) (hδA₁ b ⟨hab.le, le_rfl⟩) (hδA₂ b ⟨hab.le, le_rfl⟩) hq.le
    rcases eq_or_lt_of_le hx.1 with h | h
    · left; rw [hxt, h]
    rcases eq_or_lt_of_le hx.2 with h' | h'
    · right; rw [hxt, h']
    · exact absurd ⟨x, ⟨h, h'⟩, hxt.symm⟩ (hI b ⟨hab.le, le_rfl⟩)
  exact gate_eq_of_mem_gates hq ha₁ ha₂ ha₁i ha₂i ha₁0 ha₂0 ha₁1 ha₂1 ha₁H ha₂H h12 ha₃ ha₃i ha₃0
    ha₃H ha₃t h13 h23 hab.le hδ hδH hδF hδA₃ hI hδa hb'

/-- **Lemma 1.3, equal gates** `q₁ = q₂ = q`: the Jordan boundary of `F` is `A₁ ∪ A₂`, and a point
of `F̄ \ F` off the open arms is `q`. Hence `δ(a) = δ(b) = q`. -/
theorem gate_lemma_eq {q : ℝ} {J : Set ℂ} (hJ : J = a₁ '' Icc 0 1 ∪ a₂ '' Icc 0 1)
    (hJc : IsClosed J) (ha₁0 : a₁ 0 = q) (ha₂0 : a₂ 0 = q) {δ : ℝ → ℂ} {a b : ℝ}
    (hδFa : δ a ∉ innerSide J) (hδFb : δ b ∉ innerSide J)
    (hδA₁ : ∀ t ∈ ({a, b} : Set ℝ), δ t ∉ a₁ '' Ioc 0 1)
    (hδA₂ : ∀ t ∈ ({a, b} : Set ℝ), δ t ∉ a₂ '' Ioc 0 1)
    (hδa : δ a ∈ closure (innerSide J)) (hδb : δ b ∈ closure (innerSide J)) :
    δ a = q ∧ δ b = q := by
  have key : ∀ t ∈ ({a, b} : Set ℝ), δ t ∉ innerSide J → δ t ∈ closure (innerSide J) →
      δ t = q := by
    intro t ht hF hcl
    have hmem := mem_of_mem_closure_innerSide hJc hcl hF
    rw [hJ] at hmem
    rcases hmem with ⟨s, hs, hst⟩ | ⟨s, hs, hst⟩
    · rcases eq_or_lt_of_le hs.1 with h | h
      · rw [← hst, ← h, ha₁0]
      · exact absurd ⟨s, ⟨h, hs.2⟩, hst⟩ (hδA₁ t ht)
    · rcases eq_or_lt_of_le hs.1 with h | h
      · rw [← hst, ← h, ha₂0]
      · exact absurd ⟨s, ⟨h, hs.2⟩, hst⟩ (hδA₂ t ht)
  exact ⟨key a (Or.inl rfl) hδFa hδa, key b (Or.inr rfl) hδFb hδb⟩

end Gate

end InteractingSLE.Sec6
