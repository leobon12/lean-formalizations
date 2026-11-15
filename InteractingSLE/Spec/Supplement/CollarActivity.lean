/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.CollarActivitySector
import InteractingSLE.Spec.Supplement.G7FirstHit
import InteractingSLE.Foundations.Topology.JaniszewskiHalfPlane
import InteractingSLE.Spec.Supplement.S9Propagation

/-!
# The collar's joint activity in the proof of Theorem 7.12D (real ordered seeds)

Packet PROVE-GB7A. Proof of Theorem 7.12D (specification supplement p. 543; follow-up note D.5, interface 5): at a
proposed first new hit `η₂(t) = η₁(x) = p ∈ ℍ` of the retained first prefix `η₁([0, u])` after the second own time
`r`, "both incident collars are therefore in the own unbounded component […] W5 gives ordered completion at `(u, r)`,
so Aux. lemma 90 gives joint activity". The named input `Supp7.CollarActivityStatement` (`G7Carrier.lean`) states this
for arbitrary curves; its proof here needs the seeds to be real and ordered (`η₂(0) ≤ η₁(0)`), as they are for the
flow lines of Theorem 1.5 (`collarActivity_of_realSeeds`). The proof does not use Aux. lemma 90; it uses the contact
order of ordered proper curves (`Supp9B.contact_order`, Lemma G5 / Aux. lemma 84) and the Schoenflies sides:

* **The first tip.** Take ordered completions `α'` of `η₁([0, u'])` and `β''` of `η₂([0, c''])` with `c'' > t`. The
  contact `α'(x) = β''(t)` and the contact order forbid every contact `α'(σ) = η₂(s)` with `σ > u'` and `s < t`. So the
  future `α'((u', ∞))` misses `A = η₁([0, u']) ∪ η₂([0, r'])`; it is connected and unbounded, so all its points are
  free for `A` (`HalfPlaneSep.isFreeAt_of_not_isBounded`), and the tip `η₁(u') = α'(u')` is in the closure of the
  joint unbounded domain.
* **The second tip.** The actual future `η₂((r', t))` lies on the left of `α'` (it is in `closedLeftSide α'` and
  misses `α'`) and tends to `p = α'(x)`. A thin left-side sector along the arc `α'([x₀, σ₁])`, `x₀ < x < u' < σ₁`, that
  avoids `η₂([0, r'])` and the closed lower half-plane (`Supp9B.exists_leftSide_sector`) contains the late points of
  `η₂` and points next to the free point `α'((u' + σ₁)/2)`; so the connected set made of the sector and `η₂((r', s₁])`
  lies in the joint unbounded domain, and its closure contains `η₂(r')`.

## Main results

* `collarActivity_of_realSeeds`: `CollarActivityStatement`'s conclusion for curves with real seeds `η₂(0) ≤ η₁(0)`.
* `exists_retainedPair_of_realSeeds`: the rational ordinary retained pair of the collar (as `exists_retainedPair`).
* `g7GB7aFirstHitStatement_of_g7_gb7a`: **Theorem 1.5's interface 4 from G7 and GB7a alone** (the collar input of
  `g7GB7aFirstHitStatement_of_inputs` is discharged).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology Metric Bornology
open scoped NNReal ENNReal

universe u

namespace InteractingSLE

namespace Supp7

open Restart Theorem15D5 HalfPlaneSep Supp9B

/-! ### Generalities -/

/-- The active domain of two closed prefixes is the complement in `ℍ` of the filling of their union. -/
theorem activeDomain_eq_H_diff_fillH {η₁ η₂ : ℝ≥0 → ℂ} {s t : ℝ≥0}
    (hA : IsClosed (η₁ '' Icc 0 s ∪ η₂ '' Icc 0 t)) :
    activeDomain η₁ s η₂ t = QuantumZipper.H \ fillH (η₁ '' Icc 0 s ∪ η₂ '' Icc 0 t) := by
  ext z
  exact (mem_H_diff_fillH_of_isClosed hA).symm

/-- A free point of the closed upper half-plane is in the closure of the unbounded domain. -/
theorem mem_closure_of_isFreeAt {F : Set ℂ} {w : ℂ} (hf : IsFreeAt F w) (hw : 0 ≤ w.im) :
    w ∈ closure (QuantumZipper.H \ fillH F) := by
  obtain ⟨ε, hε, hball⟩ := hf
  rw [Metric.mem_closure_iff]
  intro e he
  set m : ℝ := min ε e / 2 with hm
  have hm0 : 0 < m := by positivity
  have hdist : dist w (w + (m : ℂ) * Complex.I) = m := by
    rw [dist_comm, dist_eq_norm, add_sub_cancel_left, norm_mul, Complex.norm_I, mul_one,
      Complex.norm_real, Real.norm_eq_abs, abs_of_pos hm0]
  have hmε : m < ε := by have := min_le_left ε e; rw [hm]; linarith [lt_min hε he]
  have hme : m < e := by have := min_le_right ε e; rw [hm]; linarith [lt_min hε he]
  refine ⟨w + (m : ℂ) * Complex.I, hball ⟨?_, ?_⟩, by rw [hdist]; exact hme⟩
  · rw [mem_ball, dist_comm, hdist]; exact hmε
  · show 0 < (w + (m : ℂ) * Complex.I).im
    simp only [Complex.add_im, Complex.mul_im, Complex.ofReal_re, Complex.I_im, mul_one,
      Complex.ofReal_im, Complex.I_re, mul_zero, add_zero]
    linarith

/-- The image of a parameter interval `[0, T]` on which the path is continuous is compact. -/
theorem isCompact_image_Icc {η : ℝ≥0 → ℂ} {T : ℝ≥0} (hc : ∀ s ≤ T, ContinuousAt η s) :
    IsCompact (η '' Icc 0 T) :=
  isCompact_Icc.image_of_continuousOn fun s hs => (hc s hs.2).continuousWithinAt

/-! ### The collar's joint activity -/

/-- **The collar's joint activity, for real ordered seeds** (proof of Theorem 7.12D, p. 543; the conclusion of
`CollarActivityStatement`). Let two paths from real seeds `η₂(0) ≤ η₁(0)` have W0's ordered proper completions for all
strictly available prefixes, and let the second path, after an own time `r`, make its first new contact with
`η₁([0, u])` at time `t` at an interior point `η₁(x)`, `x < u`. Then for some `δ > 0`, every first cutoff
`u' ∈ (x, x + δ)`, `u' ≤ u`, and second cutoff `r' ∈ (t − δ, t)`, `r' > r`, have both tips in the closure of the
joint unbounded component. Unlike `CollarActivityStatement`, neither the strict contact order nor `η₂(r) ∉ η₁([0, u])`
is needed; the real ordered seeds are. -/
theorem collarActivity_of_realSeeds {η₁ η₂ : ℝ≥0 → ℂ} {ζ₁ ζ₂ : ℝ≥0∞}
    (hW : ∀ a c : ℝ≥0, (a : ℝ≥0∞) < ζ₁ → (c : ℝ≥0∞) < ζ₂ → HasOrderedProperCompletions η₁ a η₂ c)
    (h₁0 : (η₁ 0).im = 0) (h₂0 : (η₂ 0).im = 0)
    (hseed : (η₂ 0).re ≤ (η₁ 0).re) {u r t x : ℝ≥0} (hu : (u : ℝ≥0∞) < ζ₁) (hrt : r < t)
    (ht : (t : ℝ≥0∞) < ζ₂) (hxu : x < u) (heq : η₂ t = η₁ x) (hH : η₁ x ∈ QuantumZipper.H)
    (hfirst : ∀ t' : ℝ≥0, r < t' → t' < t → η₂ t' ∉ η₁ '' Icc 0 u) :
    ∃ δ : ℝ≥0, 0 < δ ∧ ∀ u' r' : ℝ≥0, x < u' → u' < x + δ → u' ≤ u → r < r' → t < r' + δ → r' < t →
      η₁ u' ∈ closure (activeDomain η₁ u' η₂ r') ∧ η₂ r' ∈ closure (activeDomain η₁ u' η₂ r') := by
  have hr : (r : ℝ≥0∞) < ζ₂ := (ENNReal.coe_lt_coe.2 hrt).trans ht
  have hxζ : (x : ℝ≥0∞) < ζ₁ := (ENNReal.coe_lt_coe.2 hxu).trans hu
  have hc₁ : ∀ s : ℝ≥0, (s : ℝ≥0∞) < ζ₁ → ContinuousAt η₁ s := fun s hs =>
    continuousAt_fst_of_completions hW ht hs
  have hc₂ : ∀ s : ℝ≥0, (s : ℝ≥0∞) < ζ₂ → ContinuousAt η₂ s := fun s hs =>
    continuousAt_snd_of_completions hW hu hs
  have hinj₂ := injOn_snd_of_completions hW hu
  set p := η₁ x with hp
  have hHo : IsOpen QuantumZipper.H := isOpen_lt continuous_const Complex.continuous_im
  -- the old second prefix `η₂([0, r])` misses `p`
  have hK₀ : IsCompact (η₂ '' Icc 0 r) := isCompact_image_Icc fun s hs =>
    hc₂ s ((ENNReal.coe_le_coe.2 hs).trans_lt hr)
  have hpK₀ : p ∉ η₂ '' Icc 0 r := by
    rintro ⟨s, hs, hse⟩
    have hsζ : (s : ℝ≥0∞) < ζ₂ := (ENNReal.coe_le_coe.2 hs.2).trans_lt hr
    have hst := hinj₂ hsζ ht (hse.trans heq.symm)
    exact absurd (hst ▸ hs.2) (not_le.2 hrt)
  obtain ⟨ε₀, hε₀, hball₀⟩ : ∃ ε₀ > 0, ball p ε₀ ⊆ QuantumZipper.H ∩ (η₂ '' Icc 0 r)ᶜ :=
    Metric.isOpen_iff.1 (hHo.inter hK₀.isClosed.isOpen_compl) p ⟨hH, hpK₀⟩
  obtain ⟨δ₁, hδ₁, hη₁δ⟩ := Metric.eventually_nhds_iff.1
    ((hc₁ x hxζ).eventually (isOpen_ball.mem_nhds (mem_ball_self hε₀)))
  obtain ⟨δ₂, hδ₂, hη₂δ⟩ := Metric.eventually_nhds_iff.1
    ((hc₂ t ht).eventually (isOpen_ball.mem_nhds
      (show η₂ t ∈ ball p ε₀ by rw [heq]; exact mem_ball_self hε₀)))
  have hxpos : (0 : ℝ) < x := by
    rcases eq_zero_or_pos x with h0x | h0x
    · exfalso
      have h' : 0 < (η₁ 0).im := by rw [← h0x]; exact hH
      linarith
    · exact_mod_cast h0x
  refine ⟨(min δ₁ δ₂).toNNReal, Real.toNNReal_pos.2 (lt_min hδ₁ hδ₂), ?_⟩
  intro u' r' hxu' hu'δ hu'u hrr' hr'δ hr't
  have hδmin : ((min δ₁ δ₂).toNNReal : ℝ) = min δ₁ δ₂ := Real.coe_toNNReal _ (le_min hδ₁.le hδ₂.le)
  have hu'R : (u' : ℝ) < x + min δ₁ δ₂ := by
    have := NNReal.coe_lt_coe.2 hu'δ; rwa [NNReal.coe_add, hδmin] at this
  have htR : (t : ℝ) < r' + min δ₁ δ₂ := by
    have := NNReal.coe_lt_coe.2 hr'δ; rwa [NNReal.coe_add, hδmin] at this
  have hxu'R : (x : ℝ) < u' := NNReal.coe_lt_coe.2 hxu'
  have hr'tR : (r' : ℝ) < t := NNReal.coe_lt_coe.2 hr't
  have hmin1 := min_le_left δ₁ δ₂
  have hmin2 := min_le_right δ₁ δ₂
  have hu'ζ : (u' : ℝ≥0∞) < ζ₁ := (ENNReal.coe_le_coe.2 hu'u).trans_lt hu
  have hr'ζ : (r' : ℝ≥0∞) < ζ₂ := (ENNReal.coe_lt_coe.2 hr't).trans ht
  -- ordered completions at `(u', c'')`, `c'' > t`
  obtain ⟨c'', htc, hcζ⟩ := ENNReal.lt_iff_exists_nnreal_btwn.1 ht
  have htc' : t < c'' := ENNReal.coe_lt_coe.1 htc
  obtain ⟨α', β'', hα, hβ, hord⟩ := hW u' c'' hu'ζ hcζ
  have Pα := isProperCurve_of_isProperCompletion hα
  have Pβ := isProperCurve_of_isProperCompletion hβ
  have hαη : ∀ σ ≤ u', α' σ = η₁ σ := hα.2.2.2.2
  have hβη : ∀ s ≤ c'', β'' s = η₂ s := hβ.2.2.2.2
  have hα0 : (α' 0).im = 0 := by rw [hαη 0 zero_le]; exact h₁0
  have hβ0 : (β'' 0).im = 0 := by rw [hβη 0 zero_le]; exact h₂0
  have hseed' : (β'' 0).re ≤ (α' 0).re := by rw [hαη 0 zero_le, hβη 0 zero_le]; exact hseed
  -- (C1) the completed future of the first path meets no point of the second path before `t`
  have hC1 : ∀ σ s : ℝ≥0, u' < σ → s < t → α' σ ≠ η₂ s := by
    intro σ s hσ hs he
    have hst : α' x = β'' t := by rw [hαη x hxu'.le, hβη t htc'.le, heq]
    have hst' : α' σ = β'' s := by rw [he, hβη s (hs.le.trans htc'.le)]
    exact absurd (contact_order Pα Pβ hα0 hβ0 hseed' hord hst hst' (hxu'.trans hσ)) (not_lt.2 hs.le)
  -- (C2) the second path between `r` and `t` misses the first prefix
  have hC2 : ∀ σ s : ℝ≥0, σ ≤ u' → r < s → s < t → η₁ σ ≠ η₂ s := fun σ s hσ hrs hst he =>
    hfirst s hrs hst ⟨σ, ⟨zero_le, hσ.trans hu'u⟩, he⟩
  -- the joint prefix and its unbounded domain
  set A := η₁ '' Icc 0 u' ∪ η₂ '' Icc 0 r' with hA
  have hAc : IsCompact A :=
    (isCompact_image_Icc fun s hs => hc₁ s ((ENNReal.coe_le_coe.2 hs).trans_lt hu'ζ)).union
      (isCompact_image_Icc fun s hs => hc₂ s ((ENNReal.coe_le_coe.2 hs).trans_lt hr'ζ))
  rw [activeDomain_eq_H_diff_fillH hAc.isClosed]
  set D := QuantumZipper.H \ fillH A with hD
  -- **the first tip**: the completed future `α'((u', ∞))` is free
  set X₁ := α' '' Ioi u' with hX₁
  have hX₁A : X₁ ⊆ {w | 0 ≤ w.im} \ A := by
    rintro _ ⟨σ, hσ, rfl⟩
    refine ⟨Pα.2.2.1 σ, ?_⟩
    rintro (⟨τ, hτ, hτe⟩ | ⟨s, hs, hse⟩)
    · have hστ : σ = τ := Pα.2.1 (hτe.symm.trans (hαη τ hτ.2).symm)
      exact absurd (hστ ▸ hτ.2) (not_le.2 hσ)
    · exact hC1 σ s hσ (hs.2.trans_lt hr't) hse.symm
  have hX₁u : ¬ IsBounded X₁ := by
    intro hb
    obtain ⟨R, hR⟩ := hb.subset_closedBall 0
    obtain ⟨σ, hσ⟩ := ((Pα.2.2.2.eventually (eventually_gt_atTop R)).and (eventually_gt_atTop u')).exists
    have hσR := hR ⟨σ, hσ.2, rfl⟩
    rw [mem_closedBall, dist_zero_right] at hσR
    linarith [hσ.1]
  have hX₁c : IsPreconnected X₁ := isPreconnected_Ioi.image _ Pα.1.continuousOn
  have hfree₁ := isFreeAt_of_not_isBounded hAc.isClosed hAc.isBounded hX₁c hX₁u hX₁A
  have hX₁D : X₁ ⊆ closure D := fun w hw => mem_closure_of_isFreeAt (hfree₁ w hw) (hX₁A hw).1
  have htip₁ : η₁ u' ∈ closure D := by
    have hmem : α' u' ∈ closure X₁ :=
      Pα.1.continuousWithinAt.mem_closure_image (by rw [closure_Ioi]; exact mem_Ici.2 le_rfl)
    rw [← hαη u' le_rfl]
    exact closure_minimal hX₁D isClosed_closure hmem
  refine ⟨htip₁, ?_⟩
  -- **the second tip**: a left-side sector along `α'([x₀, σ₁])`
  have hu'dist : dist u' x < δ₁ := by
    rw [NNReal.dist_eq, abs_of_pos (sub_pos.2 hxu'R)]
    linarith
  have hαu'H : α' u' ∈ QuantumZipper.H := by rw [hαη u' le_rfl]; exact (hball₀ (hη₁δ hu'dist)).1
  obtain ⟨ε₃, hε₃, hα₃⟩ := Metric.eventually_nhds_iff.1
    (Pα.1.continuousAt.eventually (hHo.mem_nhds hαu'H))
  set x₀ : ℝ := max 0 ((x : ℝ) - δ₁ / 2) with hx₀
  set σ₁ : ℝ := (u' : ℝ) + ε₃ / 2 with hσ₁
  have hx₀x : x₀ < x := max_lt hxpos (by linarith)
  have hx₀0 : 0 ≤ x₀ := le_max_left _ _
  set F := η₂ '' Icc 0 r' ∪ {w : ℂ | w.im ≤ 0} with hF
  have hFc : IsClosed F :=
    (isCompact_image_Icc fun s hs => hc₂ s ((ENNReal.coe_le_coe.2 hs).trans_lt hr'ζ)).isClosed.union
      (isClosed_le Complex.continuous_im continuous_const)
  have hdisj : ∀ τ ∈ Icc x₀ σ₁, seedLine α' τ ∉ F := by
    intro τ hτ
    have hτ0 : 0 ≤ τ := hx₀0.trans hτ.1
    have hτ'r : ((τ.toNNReal : ℝ≥0) : ℝ) = τ := Real.coe_toNNReal τ hτ0
    rw [show seedLine α' τ = α' τ.toNNReal by simp [seedLine, hτ0]]
    by_cases hτu : τ.toNNReal ≤ u'
    · -- on the actual first path, near `p`
      rw [hαη _ hτu]
      have h2 : (τ.toNNReal : ℝ) ≤ u' := NNReal.coe_le_coe.2 hτu
      have hd : dist τ.toNNReal x < δ₁ := by
        rw [NNReal.dist_eq, hτ'r, abs_lt]
        have h1 := le_max_right 0 ((x : ℝ) - δ₁ / 2)
        constructor <;> linarith [hτ.1]
      have hb := hball₀ (hη₁δ hd)
      rintro (⟨s, hs, hse⟩ | him)
      · by_cases hsr : s ≤ r
        · exact hb.2 ⟨s, ⟨hs.1, hsr⟩, hse⟩
        · exact hC2 _ s hτu (not_le.1 hsr) (hs.2.trans_lt hr't) hse.symm
      · exact absurd (show 0 < (η₁ τ.toNNReal).im from hb.1) (not_lt.2 him)
    · -- on the completion, just after the tip
      have h3 : (u' : ℝ) < τ.toNNReal := NNReal.coe_lt_coe.2 (not_le.1 hτu)
      have hd : dist τ.toNNReal u' < ε₃ := by
        rw [NNReal.dist_eq, hτ'r, abs_lt]
        rw [hτ'r] at h3
        constructor <;> linarith [hτ.2]
      have hHτ := hα₃ hd
      rintro (⟨s, hs, hse⟩ | him)
      · exact hC1 _ s (not_le.1 hτu) (hs.2.trans_lt hr't) hse.symm
      · exact absurd (show 0 < (α' τ.toNNReal).im from hHτ) (not_lt.2 him)
  obtain ⟨S, hSc, hSL, hSF, hSev⟩ := exists_leftSide_sector Pα hα0 hFc hdisj
  have hSA : S ⊆ QuantumZipper.H \ A := by
    intro w hw
    have hwF : w ∉ F := Set.disjoint_left.1 hSF hw
    refine ⟨?_, ?_⟩
    · show 0 < w.im
      by_contra hc
      exact hwF (Or.inr (not_lt.1 hc))
    · rintro (⟨τ, hτ, hτe⟩ | hw2)
      · have hws : w ∈ seedRayClosure α' := Or.inl ⟨τ, by rw [hαη τ hτ.2, hτe]⟩
        exact leftSide_subset_compl α' (hSL hw) hws
      · exact hwF (Or.inl hw2)
  -- the late second path lies in `ℍ`, on the left of `α'`
  have hleft : ∀ s : ℝ≥0, r' < s → s < t → η₂ s ∈ QuantumZipper.H ∧ η₂ s ∈ leftSide α' := by
    intro s hs hst
    have hsR : (r' : ℝ) < s := NNReal.coe_lt_coe.2 hs
    have hstR : (s : ℝ) < t := NNReal.coe_lt_coe.2 hst
    have hd : dist s t < δ₂ := by
      rw [NNReal.dist_eq, abs_lt]; constructor <;> linarith
    have hHs : η₂ s ∈ QuantumZipper.H := (hball₀ (hη₂δ hd)).1
    refine ⟨hHs, ?_⟩
    have hcl : η₂ s ∈ closedLeftSide α' := by
      rw [← hβη s (hst.le.trans htc'.le)]; exact hord ⟨s, rfl⟩
    rcases hcl with hL | hR
    · exact hL
    · exfalso
      rcases hR with ⟨σ, hσ⟩ | ⟨-, him⟩
      · by_cases hσu : σ ≤ u'
        · exact hC2 σ s hσu (hrr'.trans hs) hst ((hαη σ hσu).symm.trans hσ)
        · exact hC1 σ s (not_le.1 hσu) hst hσ
      · rw [hα0] at him
        exact absurd (show 0 < (η₂ s).im from hHs) (not_lt.2 him)
  -- a late point `η₂(s₁)` in the sector
  have hxI : (x : ℝ) ∈ Ioo x₀ σ₁ := ⟨hx₀x, by linarith⟩
  have hev := hSev x hxI
  rw [seedLine_coe α' x, hαη x hxu'.le] at hev
  obtain ⟨ε₄, hε₄, hball₄⟩ := Metric.eventually_nhds_iff.1 hev
  obtain ⟨ε₅, hε₅, hη₂near⟩ := Metric.eventually_nhds_iff.1 ((hc₂ t ht).eventually
    (isOpen_ball.mem_nhds (show η₂ t ∈ ball p ε₄ by rw [heq]; exact mem_ball_self hε₄)))
  obtain ⟨s₁r, hs₁l, hs₁r⟩ := exists_between
    (show max (r' : ℝ) ((t : ℝ) - ε₅) < t from max_lt hr'tR (by linarith))
  have hs₁0 : 0 ≤ s₁r := (NNReal.coe_nonneg r').trans ((le_max_left _ _).trans hs₁l.le)
  set s₁ := s₁r.toNNReal with hs₁
  have hs₁R : (s₁ : ℝ) = s₁r := Real.coe_toNNReal _ hs₁0
  have hr's₁ : r' < s₁ := by
    rw [← NNReal.coe_lt_coe, hs₁R]; exact (le_max_left _ _).trans_lt hs₁l
  have hs₁t : s₁ < t := by rw [← NNReal.coe_lt_coe, hs₁R]; exact hs₁r
  have hs₁S : η₂ s₁ ∈ S := by
    have hd : dist s₁ t < ε₅ := by
      rw [NNReal.dist_eq, hs₁R, abs_lt]
      have := (le_max_right (r' : ℝ) ((t : ℝ) - ε₅)).trans_lt hs₁l
      constructor <;> linarith
    exact hball₄ (hη₂near hd) (hleft s₁ hr's₁ hs₁t).2
  -- the connected set: the sector and the late second path
  have hIc : IsPreconnected (η₂ '' Ioc r' s₁) :=
    isPreconnected_Ioc.image _ fun s hs =>
      (hc₂ s ((ENNReal.coe_le_coe.2 hs.2).trans_lt ((ENNReal.coe_lt_coe.2 hs₁t).trans ht))).continuousWithinAt
  have hKc : IsPreconnected (S ∪ η₂ '' Ioc r' s₁) :=
    IsPreconnected.union (η₂ s₁) hs₁S ⟨s₁, ⟨hr's₁, le_rfl⟩, rfl⟩ hSc hIc
  have hKA : S ∪ η₂ '' Ioc r' s₁ ⊆ QuantumZipper.H \ A := by
    rintro w (hw | ⟨s, hs, rfl⟩)
    · exact hSA hw
    · have hst : s < t := hs.2.trans_lt hs₁t
      refine ⟨(hleft s hs.1 hst).1, ?_⟩
      rintro (⟨σ, hσ, hσe⟩ | ⟨s', hs', hse⟩)
      · exact hC2 σ s hσ.2 (hrr'.trans hs.1) hst hσe
      · have h1 : (s' : ℝ≥0∞) < ζ₂ := (ENNReal.coe_le_coe.2 hs'.2).trans_lt hr'ζ
        have h2 : (s : ℝ≥0∞) < ζ₂ := (ENNReal.coe_lt_coe.2 hst).trans ht
        have hss := hinj₂ h1 h2 hse
        exact absurd (hss ▸ hs'.2) (not_le.2 hs.1)
  -- a point of the sector next to the free point `α'((u' + σ₁)/2)`
  set σ' : ℝ := ((u' : ℝ) + σ₁) / 2 with hσ'
  have hσ'I : σ' ∈ Ioo x₀ σ₁ := ⟨by linarith, by linarith⟩
  have hσ'0 : 0 ≤ σ' := by linarith [NNReal.coe_nonneg u']
  have hw₀X : seedLine α' σ' ∈ X₁ := by
    refine ⟨σ'.toNNReal, ?_, by simp [seedLine, hσ'0]⟩
    show u' < σ'.toNNReal
    rw [← NNReal.coe_lt_coe, Real.coe_toNNReal _ hσ'0]; linarith
  obtain ⟨ε₆, hε₆, hb₆⟩ := hfree₁ _ hw₀X
  obtain ⟨ε₇, hε₇, hb₇⟩ := Metric.eventually_nhds_iff.1 (hSev σ' hσ'I)
  have hw₀cl : seedLine α' σ' ∈ closure (leftSide α') :=
    seedRayClosure_subset_closure_leftSide Pα hα0 (seedLine_mem hα0 σ')
  obtain ⟨w, hwL, hwd⟩ := Metric.mem_closure_iff.1 hw₀cl (min ε₆ ε₇) (lt_min hε₆ hε₇)
  have hwS : w ∈ S := hb₇ (by rw [dist_comm]; exact hwd.trans_le (min_le_right _ _)) hwL
  have hwD : w ∈ D :=
    hb₆ ⟨by rw [mem_ball, dist_comm]; exact hwd.trans_le (min_le_left _ _), (hSA hwS).1⟩
  have hKD : S ∪ η₂ '' Ioc r' s₁ ⊆ D :=
    (hKc.subset_connectedComponentIn (Or.inl hwS) hKA).trans
      (connectedComponentIn_subset_H_diff_fillH hAc.isClosed hwD)
  have hmem : η₂ r' ∈ closure (η₂ '' Ioc r' s₁) :=
    (hc₂ r' hr'ζ).continuousWithinAt.mem_closure_image
      (by rw [closure_Ioc hr's₁.ne]; exact left_mem_Icc.2 hr's₁.le)
  exact closure_mono (subset_union_right.trans hKD) hmem

/-! ### The retained pair and Theorem 1.5's interface 4 without the collar input -/

/-- **The retained pair of the collar, for real ordered seeds** (as `exists_retainedPair`, with the collar's joint
activity proved by `collarActivity_of_realSeeds`). At a proposed first new hit `η₂(t) = η₁(x) ∈ ℍ`, `x < u`, of
`η₁([0, u])` after `r`, there are rational cutoffs `u' ∈ (x, u]`, `r' ∈ (r, t)` forming an ordinary retained pair. -/
theorem exists_retainedPair_of_realSeeds {η₁ η₂ : ℝ≥0 → ℂ} {ζ₁ ζ₂ : ℝ≥0∞}
    (hW : ∀ a c : ℝ≥0, (a : ℝ≥0∞) < ζ₁ → (c : ℝ≥0∞) < ζ₂ → HasOrderedProperCompletions η₁ a η₂ c)
    (hO : StrictContactsIncreasing η₁ ζ₁ η₂ ζ₂) (h₁0 : (η₁ 0).im = 0) (h₂0 : (η₂ 0).im = 0)
    (hseed : (η₂ 0).re ≤ (η₁ 0).re) {u r t x : ℝ≥0} (hu : (u : ℝ≥0∞) < ζ₁) (hrt : r < t)
    (ht : (t : ℝ≥0∞) < ζ₂) (hxu : x < u) (heq : η₂ t = η₁ x) (hH : η₁ x ∈ QuantumZipper.H)
    (hfirst : ∀ t' : ℝ≥0, r < t' → t' < t → η₂ t' ∉ η₁ '' Icc 0 u) :
    ∃ q : ℚ × ℚ, IsOrdinaryRetainedPair η₁ ζ₁ (q.1 : ℝ).toNNReal η₂ ζ₂ (q.2 : ℝ).toNNReal ∧
      x < (q.1 : ℝ).toNNReal ∧ (q.1 : ℝ).toNNReal ≤ u ∧ r < (q.2 : ℝ).toNNReal ∧ (q.2 : ℝ).toNNReal < t := by
  obtain ⟨δ, hδ, hact⟩ := collarActivity_of_realSeeds hW h₁0 h₂0 hseed hu hrt ht hxu heq hH hfirst
  have hr : (r : ℝ≥0∞) < ζ₂ := (ENNReal.coe_lt_coe.2 hrt).trans ht
  have hxζ : (x : ℝ≥0∞) < ζ₁ := (ENNReal.coe_lt_coe.2 hxu).trans hu
  obtain ⟨ε₁, hε₁, hH₁⟩ := exists_pos_forall_mem_H (continuousAt_fst_of_completions hW hr hxζ) hH
  obtain ⟨ε₂, hε₂, hH₂⟩ := exists_pos_forall_mem_H (continuousAt_snd_of_completions hW hu ht)
    (heq.symm ▸ hH)
  have hδr : (0 : ℝ) < δ := hδ
  obtain ⟨q₁, hq₁l, hq₁r⟩ := exists_rat_btwn (show (x : ℝ) < min (min ((x : ℝ) + δ) ((x : ℝ) + ε₁)) u from
    lt_min (lt_min (by linarith) (by linarith)) (by exact_mod_cast hxu))
  obtain ⟨q₂, hq₂l, hq₂r⟩ := exists_rat_btwn (show max (max ((t : ℝ) - δ) ((t : ℝ) - ε₂)) r < t from
    max_lt (max_lt (by linarith) (by linarith)) (by exact_mod_cast hrt))
  have hx0 : (0 : ℝ) ≤ x := x.2
  have hr0 : (0 : ℝ) ≤ r := r.2
  have hq₁0 : (0 : ℝ) ≤ q₁ := hx0.trans hq₁l.le
  have hq₂0 : (0 : ℝ) ≤ q₂ := hr0.trans ((le_max_right _ _).trans hq₂l.le)
  set u' := (q₁ : ℝ).toNNReal with hu'
  set r' := (q₂ : ℝ).toNNReal with hr'
  have hu'r : (u' : ℝ) = q₁ := Real.coe_toNNReal _ hq₁0
  have hr'r : (r' : ℝ) = q₂ := Real.coe_toNNReal _ hq₂0
  have hxu' : x < u' := by rw [← NNReal.coe_lt_coe, hu'r]; exact hq₁l
  have hu'δ : u' < x + δ := by
    rw [← NNReal.coe_lt_coe, NNReal.coe_add, hu'r]
    exact hq₁r.trans_le ((min_le_left _ _).trans (min_le_left _ _))
  have hu'u : u' ≤ u := by
    rw [← NNReal.coe_le_coe, hu'r]; exact hq₁r.le.trans (min_le_right _ _)
  have hu'ε : dist u' x < ε₁ := by
    rw [NNReal.dist_eq, hu'r, abs_of_pos (by linarith)]
    have := hq₁r.trans_le ((min_le_left _ _).trans (min_le_right _ _))
    linarith
  have hrr' : r < r' := by
    rw [← NNReal.coe_lt_coe, hr'r]; exact (le_max_right _ _).trans_lt hq₂l
  have hr't : r' < t := by rw [← NNReal.coe_lt_coe, hr'r]; exact hq₂r
  have hr'δ : t < r' + δ := by
    rw [← NNReal.coe_lt_coe, NNReal.coe_add, hr'r]
    have := (le_max_left _ _).trans_lt ((le_max_left _ _).trans_lt hq₂l)
    linarith
  have hr'ε : dist r' t < ε₂ := by
    rw [NNReal.dist_eq, hr'r, abs_of_neg (by linarith)]
    have := (le_max_right _ _).trans_lt ((le_max_left _ _).trans_lt hq₂l)
    linarith
  obtain ⟨hact₁, hact₂⟩ := hact u' r' hxu' hu'δ hu'u hrr' hr'δ hr't
  have hu'ζ : (u' : ℝ≥0∞) < ζ₁ := (ENNReal.coe_le_coe.2 hu'u).trans_lt hu
  have hr'ζ : (r' : ℝ≥0∞) < ζ₂ := (ENNReal.coe_lt_coe.2 hr't).trans ht
  refine ⟨(q₁, q₂), ⟨hu'ζ, hr'ζ, hH₁ u' hu'ε, hH₂ r' hr'ε, ?_, ?_, hact₁, hact₂, hW u' r' hu'ζ hr'ζ⟩,
    hxu', hu'u, hrr', hr't⟩
  · exact fun hmem => hfirst r' hrr' hr't (image_mono (Icc_subset_Icc_right hu'u) hmem)
  · rintro ⟨t'', ht'', he⟩
    have ht''ζ : (t'' : ℝ≥0∞) < ζ₂ := (ENNReal.coe_le_coe.2 ht''.2).trans_lt hr'ζ
    have := hO x u' t t'' hxζ hu'ζ ht ht''ζ heq.symm he.symm hxu'
    exact absurd (this.trans_le ht''.2) (not_lt.2 hr't.le)

/-- **Theorem 1.5's interface 4 (G7 + GB7a at a retained pair) from Lemma G7 at the retained pair and Lemma GB7a
alone**: the collar input `CollarActivityStatement` of `g7GB7aFirstHitStatement_of_inputs` is discharged by
`collarActivity_of_realSeeds`, the seeds of the two flow lines being almost surely `x₂ ≤ x₁`. -/
theorem g7GB7aFirstHitStatement_of_g7_gb7a (hG7 : G7RetainedPairStatement.{u})
    (hGB : Supp8.GB7aFlowStatement.{0}) : G7GB7aFirstHitStatement.{u} := by
  intro κ hκ hκ4 b jumps hb x₁ x₂ θ₁ θ₂ hx hwt Ω _ P _ h hh η₁ η₂ ζ₁ ζ₂ h₁ h₂
  have hC := fun q : ℚ × ℚ => hG7 κ hκ hκ4 b jumps hb x₁ x₂ θ₁ θ₂ hx hwt P h hh η₁ η₂ ζ₁ ζ₂ h₁ h₂
    (q.1 : ℝ).toNNReal (q.2 : ℝ).toNNReal
  choose S mS H Γ U M β X K hHm hUm hΓm hΓc hM hβ hX hK hlaw hpair hpath using hC
  -- the conditional paths lie in `ℍ̄`
  have E2 : ∀ q : ℚ × ℚ, ∀ᵐ ω ∂P, ω ∈ M q →
      X q ω ∈ {s | ∀ t : ℝ≥0, (t : ℝ≥0∞) ≤ U q s → 0 ≤ (Γ q s t).im} := by
    intro q
    let _ := mS q
    have := hK q
    refine Restart.ae_mem_of_compProd_eq (hM q) (hβ q) (hX q) (hlaw q)
      (measurableSet_forall_im_nonneg (hUm q) (hΓm q) (hΓc q)) ?_
    filter_upwards [hpair q] with c hc
    exact ae_im_nonneg_of_isFlowLine hc.2
  -- GB7a, integrated back as a product event
  have E3 : ∀ q ab : ℚ × ℚ, ∀ᵐ ω ∂P, ω ∈ M q →
      ¬ (β q ω ∈ goodInterval κ θ₂ ab.1 ab.2 ∧
        X q ω ∈ {s | VisitsStrip (Γ q s) (U q s) ab.1 ab.2}) := by
    intro q ab
    let _ := mS q
    have := hK q
    refine ae_not_mem_prod_of_compProd_eq (hM q) (hβ q) (hX q) (hlaw q) (measurableSet_goodInterval _ _ _ _)
      (measurableSet_visitsStrip (hUm q) (hΓm q) (hΓc q) _ _) ?_
    filter_upwards [hpair q] with c hc hcA
    exact measure_visitsStrip_eq_zero hGB hκ hκ4 hc.1 hc.2 hcA
  filter_upwards [ae_all_iff.2 hpath, ae_all_iff.2 E2, ae_all_iff.2 fun q => ae_all_iff.2 (E3 q),
    Supp9.ae_apply_zero_of_isFlowLine h₁, Supp9.ae_apply_zero_of_isFlowLine h₂]
    with ω hP hI hV h10 h20
  intro hord hstrict u r hu hr _hr2 t x hrt ht hxu heq hHx hfirst
  have hs₁ : (η₁ ω 0).im = 0 := by rw [h10]; simp
  have hs₂ : (η₂ ω 0).im = 0 := by rw [h20]; simp
  have hseed : (η₂ ω 0).re ≤ (η₁ ω 0).re := by rw [h10, h20]; simpa using hx
  obtain ⟨q, hret, hxu', hu'u, hrr', hr't⟩ :=
    exists_retainedPair_of_realSeeds hord hstrict hs₁ hs₂ hseed hu hrt ht hxu heq hHx hfirst
  obtain ⟨hMω, hRC⟩ := hP q hret
  have hinj₁ := injOn_fst_of_completions hord hr
  have hinj₂ := injOn_snd_of_completions hord hu
  have hfirst' : ∀ t' : ℝ≥0, (q.2 : ℝ).toNNReal < t' → t' < t →
      η₂ ω t' ∉ η₁ ω '' Icc 0 (q.1 : ℝ).toNNReal := fun t' h1 h2 hmem =>
    hfirst t' (hrr'.trans h1) h2 (image_mono (Icc_subset_Icc_right hu'u) hmem)
  obtain ⟨s, hsU, y, hΓy, hy0, hyJ, hyR, hyL⟩ :=
    exists_visit_of_isRetainedContinuation hRC (hI q hMω) hinj₁ hinj₂ hret.1 hr't ht hxu' heq hHx
      hret.2.2.2.2.1 hfirst'
  obtain ⟨ab, hcA, hyab⟩ := exists_goodInterval_of_visit hy0 hyJ hyR hyL
  refine hV q ab hMω ⟨hcA, s, hsU, ?_, ?_, ?_⟩
  · rw [hΓy]; simp
  · rw [hΓy]; simpa using hyab.1
  · rw [hΓy]; simpa using hyab.2

end Supp7

end InteractingSLE
