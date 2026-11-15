/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.ZhanGT4.DualA15CofinalEncl

/-!
# Zhan's A.1 (G3): good enclosure pairs whose large enclosure clears a real segment

Packet PROVE-A1-ASSEMBLE. Source: Astra, *Follow-up proofs*, §A.1.3 (`ig1_followup_proofs.txt` L300–L304: "positive
separation from the other enclosure and all nonseed finite force marks … a fixed protected real interval"); R38.

A1-G3CALC's protected pairs `IsProtectedPairG` ask, besides A1-SEEDFIELD's `IsProtectedPair`, that the real segment
`(0, q]` carrying the ordinary mark be `2δ`-far from the large enclosure, with the protected point `q` right of the
ordinary mark. A15F's `exists_goodEncl` gives no such control. Its variant here:

* **`exists_goodEncl_seg`**: for compact prefixes `C₁ ∋ 0`, `C₂ ∋ x₂` as in `exists_goodEncl`, and a real
  `qlo ∈ (0, x₂)` outside `Ĉ₁` such that the real segment `[0, qlo]` misses `Ĉ₂ = C₂ ∪ closure (fill C₂)`, some
  good index of the countable family with the prescribed cap has its protected point `≥ qlo` and its large enclosure
  `2δ`-far from the real segment `[0, q]`;
* **`exists_goodEncl_seg_prefix`**: the same for the prefixes `closure A₁ ∪ {0}`, `closure A₂ ∪ {x₂}` of two Loewner
  hulls (`Ĉ = closure A ∪ {x}`).

The proof is A15F's, with two changes: the protected rational point is chosen in a small interval right of `qlo` that
misses `Ĉ₁ ∪ Ĉ₂`, and the compact real segment `[0, q]` (which then misses `Ĉ₂`) is added to the sets the large dyadic
covers eventually avoid, so the separation `δ` also bounds the distance of the segment from the large enclosure.
-/

set_option autoImplicit false

noncomputable section

open Set Filter Topology Metric
open scoped NNReal ENNReal

namespace InteractingSLE.ZhanGT4.A1Asm

open QuantumZipper (H fwdHull)
open Restart (dyadicSquare dyadicIdx dyadicCover lowerHalf)

/-- The real segment `[a, b]` in `ℂ` is compact. -/
theorem isCompact_realSeg (a b : ℝ) : IsCompact ((fun t : ℝ => (t : ℂ)) '' Icc a b) :=
  isCompact_Icc.image Complex.continuous_ofReal

/-- **A good enclosure pair whose large enclosure clears a real segment.** As A15F's `exists_goodEncl`, with a real
`qlo ∈ (0, x₂)` outside `Ĉ₁` such that `[0, qlo]` misses `Ĉ₂`: the good index can be chosen with its protected point
`q ≥ qlo` and with `‖a − y‖ ≥ 2δ` for every point `a` of the large enclosure and every real `y ∈ [0, q]`. -/
theorem exists_goodEncl_seg {nm : ℕ} {x₂ : ℝ} {p : Fin nm → ℝ} {C₁ C₂ : Set ℂ}
    (hC₁ : IsCompact C₁) (hC₂ : IsCompact C₂) (h0 : (0 : ℂ) ∈ C₁) (hx : (x₂ : ℂ) ∈ C₂)
    (hc₁ : IsPreconnected (C₁ ∪ lowerHalf)) (hc₂ : IsPreconnected (C₂ ∪ lowerHalf))
    (hdisj : Disjoint (C₁ ∪ closure (fillH C₁)) (C₂ ∪ closure (fillH C₂)))
    (hp : ∀ m, (p m : ℂ) ∉ (C₁ ∪ closure (fillH C₁)) ∪ (C₂ ∪ closure (fillH C₂))) {qlo : ℝ} (hqlo : 0 < qlo)
    (hqlox : qlo < x₂) (hseg : ∀ t ∈ Icc (0 : ℝ) qlo, (t : ℂ) ∉ C₂ ∪ closure (fillH C₂))
    (hq₁ : (qlo : ℂ) ∉ C₁ ∪ closure (fillH C₁)) (N : ℕ) (hN : 0 < N) :
    ∃ i : CofIdx, GoodEncl x₂ p i ∧ i.cap = N ∧ C₁ ∩ H ⊆ i.encl₁ ∧ C₂ ∩ H ⊆ i.encl₂ x₂ ∧ qlo ≤ i.prot ∧
      ∀ a ∈ i.encl₂ x₂, ∀ y : ℝ, 0 ≤ y → y ≤ i.prot → 2 * i.sep ≤ ‖a - y‖ := by
  set C₂' : Set ℂ := (fun z : ℂ => z - x₂) '' C₂ with hC₂'
  have hC₂'c : IsCompact C₂' := hC₂.image (continuous_id.sub continuous_const)
  have heC₂' : (fun z : ℂ => z + x₂) '' C₂' = C₂ := by
    rw [hC₂', image_image]
    simp
  have hmemC₂' : ∀ z, z ∈ C₂ → z - x₂ ∈ C₂' := fun z hz => ⟨z, hz, rfl⟩
  have h0' : (0 : ℂ) ∈ C₂' := by simpa using hmemC₂' _ hx
  have hĈ₁ : IsClosed (C₁ ∪ closure (fillH C₁)) := hC₁.isClosed.union isClosed_closure
  have hĈ₂ : IsClosed (C₂ ∪ closure (fillH C₂)) := hC₂.isClosed.union isClosed_closure
  -- the protected rational point, right of `qlo`, with `[qlo, q]` outside both sets
  have hqloĈ : (qlo : ℂ) ∉ (C₁ ∪ closure (fillH C₁)) ∪ (C₂ ∪ closure (fillH C₂)) := by
    rintro (h | h)
    · exact hq₁ h
    · exact hseg qlo ⟨hqlo.le, le_rfl⟩ h
  obtain ⟨ε, hε, hεb⟩ := Metric.isOpen_iff.1 (hĈ₁.union hĈ₂).isOpen_compl (qlo : ℂ) hqloĈ
  obtain ⟨q, hq1, hq2⟩ := exists_rat_btwn (show qlo < min (qlo + ε) x₂ from lt_min (by linarith) hqlox)
  have hqε : (q : ℝ) < qlo + ε := hq2.trans_le (min_le_left _ _)
  have hqx : (q : ℝ) < x₂ := hq2.trans_le (min_le_right _ _)
  have hq0 : 0 < (q : ℝ) := hqlo.trans hq1
  have hnear : ∀ t : ℝ, qlo ≤ t → t < qlo + ε →
      (t : ℂ) ∉ (C₁ ∪ closure (fillH C₁)) ∪ (C₂ ∪ closure (fillH C₂)) := fun t ht1 ht2 hmem => by
    refine hεb ?_ hmem
    rw [mem_ball, dist_eq_norm, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs, abs_lt]
    constructor <;> linarith
  have hqĈ : ((q : ℝ) : ℂ) ∉ (C₁ ∪ closure (fillH C₁)) ∪ (C₂ ∪ closure (fillH C₂)) :=
    hnear q hq1.le hqε
  -- the real segment `[0, q]` misses `Ĉ₂`
  set K : Set ℂ := (fun t : ℝ => (t : ℂ)) '' Icc 0 (q : ℝ) with hK
  have hKc : IsCompact K := isCompact_realSeg 0 q
  have hKĈ₂ : ∀ z ∈ K, z ∉ C₂ ∪ closure (fillH C₂) := by
    rintro z ⟨t, ht, rfl⟩
    rcases le_or_gt t qlo with htq | htq
    · exact hseg t ⟨ht.1, htq⟩
    · exact fun h => hnear t htq.le (by linarith [ht.2]) (Or.inr h)
  -- the dyadic covers and the closures of their fillings
  have hbdd : ∀ D : Set ℂ, Bornology.IsBounded D → IsCompact (closure (fillH D)) := fun D hD => by
    obtain ⟨R, hR, hDR⟩ := exists_closure_subset_ball hD
    exact (Metric.isBounded_ball.subset (fillH_subset_ball hR hDR)).isCompact_closure
  have hD₁b : ∀ m, Bornology.IsBounded (dyadicCover m C₁) := fun m =>
    (Restart.isCompact_dyadicCover hC₁.isBounded m).isBounded
  have hD₂b : ∀ m, Bornology.IsBounded ((fun z : ℂ => z + x₂) '' dyadicCover m C₂') := fun m =>
    ((Restart.isCompact_dyadicCover hC₂'c.isBounded m).image (continuous_id.add continuous_const)).isBounded
  have hXa : Antitone fun m => closure (fillH (dyadicCover m C₁)) := fun _ _ hab =>
    closure_mono (Restart.fillH_dyadicCover_antitone hab)
  have hYa : Antitone fun m => closure (fillH ((fun z : ℂ => z + x₂) '' dyadicCover m C₂')) := fun _ _ hab =>
    closure_mono (fillH_mono (image_mono (Restart.dyadicCover_antitone hab)))
  have hB₁ : ∀ x, x ∉ C₁ ∪ closure (fillH C₁) → ∀ᶠ m in atTop, x ∉ closure (fillH (dyadicCover m C₁)) :=
    fun x hx => notMem_closure_fillH_dyadicCover hC₁ hx
  have hB₂ : ∀ x, x ∉ C₂ ∪ closure (fillH C₂) →
      ∀ᶠ m in atTop, x ∉ closure (fillH ((fun z : ℂ => z + x₂) '' dyadicCover m C₂')) :=
    fun x hx => notMem_closure_fillH_dyadicCover_add hC₂'c x₂ (by rw [heC₂']; exact hx)
  obtain ⟨m₀, hm₀⟩ := exists_disjoint_of_antitone hXa hYa (fun m => hbdd _ (hD₁b m)) (fun m => hbdd _ (hD₂b m))
    fun x hxX hxY => by
      by_cases h1 : x ∈ C₁ ∪ closure (fillH C₁)
      · by_cases h2 : x ∈ C₂ ∪ closure (fillH C₂)
        · exact Set.disjoint_left.1 hdisj h1 h2
        · obtain ⟨m, hm⟩ := (hB₂ x h2).exists
          exact hm (hxY m)
      · obtain ⟨m, hm⟩ := (hB₁ x h1).exists
        exact hm (hxX m)
  obtain ⟨m₁, hm₁⟩ := exists_disjoint_of_antitone (X := fun _ => K) (fun _ _ _ => le_rfl) hYa (fun _ => hKc)
    (fun m => hbdd _ (hD₂b m)) fun x hxX hxY => by
      obtain ⟨m, hm⟩ := (hB₂ x (hKĈ₂ x (hxX 0))).exists
      exact hm (hxY m)
  have hsepev : ∀ᶠ m in atTop, Disjoint (closure (fillH (dyadicCover m C₁)))
      (closure (fillH ((fun z : ℂ => z + x₂) '' dyadicCover m C₂'))) := by
    filter_upwards [eventually_ge_atTop m₀] with m hm
    exact hm₀.mono (hXa hm) (hYa hm)
  have hsegev : ∀ᶠ m in atTop, Disjoint K (closure (fillH ((fun z : ℂ => z + x₂) '' dyadicCover m C₂'))) := by
    filter_upwards [eventually_ge_atTop m₁] with m hm
    exact hm₁.mono_right (hYa hm)
  have hmarkev : ∀ᶠ m in atTop, ∀ j, (p j : ℂ) ∉ closure (fillH (dyadicCover m C₁)) ∧
      (p j : ℂ) ∉ closure (fillH ((fun z : ℂ => z + x₂) '' dyadicCover m C₂')) := by
    rw [eventually_all]
    intro j
    exact (hB₁ _ fun h => hp j (Or.inl h)).and (hB₂ _ fun h => hp j (Or.inr h))
  have hqev : ∀ᶠ m in atTop, ((q : ℝ) : ℂ) ∉ closure (fillH (dyadicCover m C₁)) ∧
      ((q : ℝ) : ℂ) ∉ closure (fillH ((fun z : ℂ => z + x₂) '' dyadicCover m C₂')) :=
    (hB₁ _ fun h => hqĈ (Or.inl h)).and (hB₂ _ fun h => hqĈ (Or.inr h))
  obtain ⟨m, hmsep, hmseg, hmmark, hmq⟩ := (hsepev.and (hsegev.and (hmarkev.and hqev))).exists
  -- the rational separation `δ` (also from the segment) and protection radius `d`
  obtain ⟨δ₀, hδ₀, hδsep⟩ := exists_pos_le_norm_sub_of_disjoint (hbdd _ (hD₁b m)) isClosed_closure hmsep
  obtain ⟨δ₁, hδ₁, hδseg⟩ := exists_pos_le_norm_sub_of_disjoint hKc isClosed_closure hmseg
  obtain ⟨δ, hδ1, hδ2⟩ := exists_rat_btwn (show (0 : ℝ) < min δ₀ δ₁ / 2 by positivity)
  have hδ₀' : 2 * (δ : ℝ) ≤ δ₀ := by linarith [min_le_left δ₀ δ₁]
  have hδ₁' : 2 * (δ : ℝ) ≤ δ₁ := by linarith [min_le_right δ₀ δ₁]
  have hPc : IsCompact (insert ((q : ℝ) : ℂ) (range fun j => (p j : ℂ))) :=
    ((Set.finite_range _).insert _).isCompact
  have hPdis : Disjoint (insert ((q : ℝ) : ℂ) (range fun j => (p j : ℂ)))
      (closure (fillH (dyadicCover m C₁)) ∪ closure (fillH ((fun z : ℂ => z + x₂) '' dyadicCover m C₂'))) := by
    rw [Set.disjoint_left]
    rintro z (rfl | ⟨j, rfl⟩) (hz | hz)
    exacts [hmq.1 hz, hmq.2 hz, (hmmark j).1 hz, (hmmark j).2 hz]
  obtain ⟨ρ, hρ, hρsep⟩ := exists_pos_le_norm_sub_of_disjoint hPc (isClosed_closure.union isClosed_closure) hPdis
  obtain ⟨d, hd1, hd2⟩ := exists_rat_btwn (show (0 : ℝ) < ρ / 2 by positivity)
  -- the index
  set I₁ := (Restart.dyadicIdx_finite hC₁.isBounded m).toFinset with hI₁
  set I₂ := (Restart.dyadicIdx_finite hC₂'c.isBounded m).toFinset with hI₂
  have hsq₁ : sqUnion m I₁ = dyadicCover m C₁ := by
    ext z
    simp only [sqUnion, dyadicCover, hI₁, Set.Finite.mem_toFinset, mem_iUnion, exists_prop]
  have hsq₂ : sqUnion m I₂ = dyadicCover m C₂' := by
    ext z
    simp only [sqUnion, dyadicCover, hI₂, Set.Finite.mem_toFinset, mem_iUnion, exists_prop]
  have hE₁ : CofIdx.encl₁ (m, I₁, I₂, N, δ, q, d) = fillH (dyadicCover m C₁) := by
    show fillH (sqUnion m I₁) = _
    rw [hsq₁]
  have hE₂ : CofIdx.encl₂ x₂ (m, I₁, I₂, N, δ, q, d) = fillH ((fun z : ℂ => z + x₂) '' dyadicCover m C₂') := by
    show fillH ((fun z : ℂ => z + x₂) '' sqUnion m I₂) = _
    rw [hsq₂]
  have hfar : ∀ z ∈ closure (fillH (dyadicCover m C₁)) ∪
      closure (fillH ((fun z : ℂ => z + x₂) '' dyadicCover m C₂')),
      ∀ w ∈ insert ((q : ℝ) : ℂ) (range fun j => (p j : ℂ)), ‖z - w‖ < 2 * (d : ℝ) → False :=
    fun z hz w hw hlt => by
      have := hρsep z hz w hw
      linarith
  have hball : ∀ w ∈ insert ((q : ℝ) : ℂ) (range fun j => (p j : ℂ)),
      Disjoint (ball w (2 * (d : ℝ))) (CofIdx.encl₁ (m, I₁, I₂, N, δ, q, d) ∪
        CofIdx.encl₂ x₂ (m, I₁, I₂, N, δ, q, d)) := by
    intro w hw
    rw [hE₁, hE₂, Set.disjoint_left]
    rintro z hzb (hz | hz)
    · refine hfar z (Or.inl (subset_closure hz)) w hw ?_
      rwa [mem_ball, dist_eq_norm] at hzb
    · refine hfar z (Or.inr (subset_closure hz)) w hw ?_
      rwa [mem_ball, dist_eq_norm] at hzb
  have hmemD₂ : ∀ z : ℂ, z - (x₂ : ℂ) ∈ dyadicCover m C₂' → z ∈ (fun z : ℂ => z + x₂) '' dyadicCover m C₂' :=
    fun z hz => ⟨z - x₂, hz, by ring⟩
  refine ⟨(m, I₁, I₂, N, δ, q, d), ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, rfl, ?_, ?_, ?_, ?_⟩
  · show IsPreconnected (sqUnion m I₁ ∪ lowerHalf)
    rw [hsq₁]
    exact Restart.isPreconnected_dyadicCover_union hc₁ Restart.zero_mem_lowerHalf m
  · show IsPreconnected ((fun z : ℂ => z + x₂) '' sqUnion m I₂ ∪ lowerHalf)
    have hc₂' : IsPreconnected (C₂' ∪ lowerHalf) := by
      have := hc₂.image (fun z : ℂ => z - x₂) (continuous_id.sub continuous_const).continuousOn
      rwa [image_union, ← hC₂', show (fun z : ℂ => z - x₂) '' lowerHalf = lowerHalf by
        simpa [sub_eq_add_neg] using image_add_lowerHalf (-x₂)] at this
    have := (Restart.isPreconnected_dyadicCover_union hc₂' Restart.zero_mem_lowerHalf m).image
      (fun z : ℂ => z + x₂) (continuous_id.add continuous_const).continuousOn
    rwa [image_union, image_add_lowerHalf, ← hsq₂] at this
  · show (0 : ℝ≥0) < (N : ℝ≥0)
    exact_mod_cast hN
  · show (0 : ℝ) < (δ : ℝ)
    exact hδ1
  · intro a ha z hz
    rw [hE₂] at ha
    rw [hE₁] at hz
    have := hδsep a (subset_closure ha) z (subset_closure hz)
    show 2 * (δ : ℝ) ≤ ‖a - z‖
    linarith
  · show (0 : ℝ) < (d : ℝ)
    exact hd1
  · exact hq0
  · exact hqx
  · exact hball _ (mem_insert _ _)
  · intro j
    exact hball _ (mem_insert_of_mem _ ⟨j, rfl⟩)
  · refine ⟨1 / 2 ^ m, by positivity, fun z hz => ?_⟩
    rw [hE₁]
    exact mem_fillH_of_mem_closure hz.2 (subset_closure (ball_zero_subset_dyadicCover h0 m hz.1))
  · refine ⟨1 / 2 ^ m, by positivity, fun z hz => ?_⟩
    rw [hE₂]
    refine mem_fillH_of_mem_closure hz.2 (subset_closure (hmemD₂ z (ball_zero_subset_dyadicCover h0' m ?_)))
    have hz1 := hz.1
    rw [mem_ball, dist_eq_norm] at hz1
    rw [mem_ball, dist_eq_norm, sub_zero]
    exact hz1
  · intro z hz
    rw [hE₁]
    exact mem_fillH_of_mem_closure hz.2 (subset_closure (Restart.subset_dyadicCover m hz.1))
  · intro z hz
    rw [hE₂]
    exact mem_fillH_of_mem_closure hz.2 (subset_closure (hmemD₂ z (Restart.subset_dyadicCover m
      (hmemC₂' z hz.1))))
  · exact hq1.le
  · intro a ha y hy0 hyq
    rw [hE₂] at ha
    have := hδseg a (subset_closure ha) (y : ℂ) ⟨y, ⟨hy0, hyq⟩, rfl⟩
    show 2 * (δ : ℝ) ≤ ‖a - y‖
    linarith

/-- **The segment variant for two Loewner prefixes**: for compact `ℍ`-hulls `A₁`, `A₂` whose prefixes
`closure A₁ ∪ {0}`, `closure A₂ ∪ {x₂}` are disjoint and contain no mark, a real `qlo ∈ (0, x₂)` outside the first
prefix such that `[0, qlo]` misses the second, some good index with the prescribed cap has `A₁ ⊆ encl₁`,
`A₂ ⊆ encl₂`, protected point `q ≥ qlo`, and its large enclosure `2δ`-far from the real segment `[0, q]`. -/
theorem exists_goodEncl_seg_prefix {nm : ℕ} {x₂ : ℝ} {p : Fin nm → ℝ} {A₁ A₂ : Set ℂ}
    (hA₁ : IsHPHull A₁) (hA₂ : IsHPHull A₂) (hdisj : Disjoint (closure A₁ ∪ {0}) (closure A₂ ∪ {(x₂ : ℂ)}))
    (hp : ∀ m, (p m : ℂ) ∉ (closure A₁ ∪ {0}) ∪ (closure A₂ ∪ {(x₂ : ℂ)})) {qlo : ℝ} (hqlo : 0 < qlo)
    (hqlox : qlo < x₂) (hseg : ∀ t ∈ Icc (0 : ℝ) qlo, (t : ℂ) ∉ closure A₂ ∪ {(x₂ : ℂ)})
    (hq₁ : (qlo : ℂ) ∉ closure A₁ ∪ {0}) (N : ℕ) (hN : 0 < N) :
    ∃ i : CofIdx, GoodEncl x₂ p i ∧ i.cap = N ∧ A₁ ⊆ i.encl₁ ∧ A₂ ⊆ i.encl₂ x₂ ∧ qlo ≤ i.prot ∧
      ∀ a ∈ i.encl₂ x₂, ∀ y : ℝ, 0 ≤ y → y ≤ i.prot → 2 * i.sep ≤ ‖a - y‖ := by
  have hpre : ∀ {A : Set ℂ} (hA : IsHPHull A) (x : ℝ),
      IsCompact (closure A ∪ {(x : ℂ)}) ∧ IsPreconnected ((closure A ∪ {(x : ℂ)}) ∪ lowerHalf) ∧
        (closure A ∪ {(x : ℂ)}) ∪ closure (fillH (closure A ∪ {(x : ℂ)})) = closure A ∪ {(x : ℂ)} := by
    intro A hA x
    refine ⟨hA.2.1.isCompact_closure.union isCompact_singleton, ?_, ?_⟩
    · have hxL : (x : ℂ) ∈ lowerHalf := show ((x : ℂ)).im ≤ 0 by simp
      have e : (closure A ∪ {(x : ℂ)}) ∪ lowerHalf = closure (A ∪ lowerHalf) := by
        rw [closure_union, Restart.lowerHalf, isClosed_lowerHalf.closure_eq, union_assoc,
          singleton_union, insert_eq_of_mem (show (x : ℂ) ∈ {z : ℂ | z.im ≤ 0} from hxL)]
      rw [e]
      exact (IsHPHull.isPreconnected_union_lowerHalf hA).closure
    · rw [fillH_closure_union_real hA x]
      exact union_eq_left.2 subset_union_left
  obtain ⟨hK₁, hc₁, he₁⟩ := hpre hA₁ 0
  obtain ⟨hK₂, hc₂, he₂⟩ := hpre hA₂ x₂
  simp only [Complex.ofReal_zero] at hK₁ hc₁ he₁
  obtain ⟨i, hi, hcap, h₁, h₂, hlo, hsg⟩ := exists_goodEncl_seg hK₁ hK₂ (Or.inr rfl) (Or.inr rfl) hc₁ hc₂
    (by rw [he₁, he₂]; exact hdisj) (by rw [he₁, he₂]; exact hp) hqlo hqlox (by rw [he₂]; exact hseg)
    (by rw [he₁]; exact hq₁) N hN
  exact ⟨i, hi, hcap, fun z hz => h₁ ⟨Or.inl (subset_closure hz), hA₁.1 hz⟩,
    fun z hz => h₂ ⟨Or.inl (subset_closure hz), hA₂.1 hz⟩, hlo, hsg⟩

end InteractingSLE.ZhanGT4.A1Asm
