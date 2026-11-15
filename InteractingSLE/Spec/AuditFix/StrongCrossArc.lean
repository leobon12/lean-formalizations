/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.S9Contacts
import InteractingSLE.Spec.Supplement.GB10
import InteractingSLE.Spec.Sec2.AssemblyCode
import InteractingSLE.Frozen.Spec.AgreeAsCurvesAfter

/-!
# Audit fix (crossing): deterministic facts about common open arcs

Packet PROVE-AF-CROSS (external audit of 2026-11-15, §2.2, pp. 6–7). Deterministic lemmas for the strengthened
Theorem 1.5 (iii) (`AuditFix/StrongCross.lean`). `Supp9.HasCommonOpenSubarc α a β c` is the predicate of Lemma W0b
(supplement p. 529): an open subarc `α((x₁, x₂))`, `x₂ ≤ a`, of the first prefix lies in `β([0, c])`.

* `hasCommonOpenSubarc_mono`: monotone in both prefix lengths.
* `hasCommonOpenSubarc_iff_dyadCommonArc`: for continuous prefixes, an equivalent countable description
  `DyadCommonArc` (dyadic times only). It makes the no-common-arc event of the canonical restart space measurable
  (`AuditFix/StrongCrossChart.lean`).
* `not_image_Ioo_subset_of_prefix` (Baire's theorem on a parameter interval,
  `Theorem14.GB10.exists_Icc_subset_of_image_subset_iUnion`): if no open arc of a strict outgoing prefix of `α` lies
  in a strict outgoing prefix of `β`, then no open arc of the whole outgoing available path of `α` lies in the whole
  outgoing available path of `β`. `noCommonOutgoingArc_of_prefix` is the two-sided form.
* `not_agreeAsCurvesAfter_of_noCommonOutgoingArc`: when both paths continue after the contact, "no open arc of the
  first outgoing path lies on the second outgoing path" excludes merging (`AgreeAsCurvesAfter`, the conclusion of
  the frozen merging clause, Theorem 1.5 (ii)).
-/

set_option autoImplicit false

noncomputable section

open Set Filter Topology
open scoped NNReal ENNReal

namespace InteractingSLE

namespace AuditFix

namespace Cross

open Sec2.Assembly Supp9

/-! ### Monotonicity -/

/-- `HasCommonOpenSubarc` is monotone in both prefix lengths. -/
theorem hasCommonOpenSubarc_mono {X : Type*} {α β : ℝ≥0 → X} {a a' c c' : ℝ≥0}
    (h : HasCommonOpenSubarc α a β c) (ha : a ≤ a') (hc : c ≤ c') : HasCommonOpenSubarc α a' β c' := by
  obtain ⟨x₁, x₂, h12, h2a, hsub⟩ := h
  exact ⟨x₁, x₂, h12, h2a.trans ha, hsub.trans (image_mono (Icc_subset_Icc le_rfl hc))⟩

/-! ### A countable description -/

/-- A dyadic witness of a common open subarc of `α([0, a])` in `β([0, c])`: dyadic times `d₁ < d₂ ≤ a` such that,
at every dyadic time of `(d₁, d₂)`, `α` is within every precision `1/(m+1)` of `β` at some dyadic time of `[0, c]`. -/
def DyadCommonArc (α β : ℝ≥0 → ℂ) (a c : ℝ≥0) : Prop :=
  ∃ i j i' j' : ℕ, dyad i j < dyad i' j' ∧ dyad i' j' ≤ a ∧
    ∀ p q : ℕ, dyad i j < dyad p q → dyad p q < dyad i' j' → ∀ m : ℕ, ∃ p' q' : ℕ, dyad p' q' ≤ c ∧
      dist (α (dyad p q)) (β (dyad p' q')) < 1 / ((m : ℝ) + 1)

/-- **The countable description of a common open subarc**, for prefixes continuous on `[0, a]` and `[0, c]`:
shrink the arc to dyadic end points, and use that `β([0, c])` is compact and the dyadic times of `[0, c]` are dense
in it; conversely the dyadic times of `(d₁, d₂)` are dense in it and `β([0, c])` is closed. -/
theorem hasCommonOpenSubarc_iff_dyadCommonArc {α β : ℝ≥0 → ℂ} {a c : ℝ≥0}
    (hα : ContinuousOn α (Icc 0 a)) (hβ : ContinuousOn β (Icc 0 c)) :
    HasCommonOpenSubarc α a β c ↔ DyadCommonArc α β a c := by
  have hK : IsClosed (β '' Icc 0 c) := (isCompact_Icc.image_of_continuousOn hβ).isClosed
  constructor
  · rintro ⟨x₁, x₂, h12, h2a, hsub⟩
    obtain ⟨i, j, hij₁, hij₂⟩ := exists_dyad_btwn (ζ := (x₂ : ℝ≥0∞)) (ENNReal.coe_lt_coe.2 h12)
    obtain ⟨i', j', hd₁, hd₂⟩ := exists_dyad_btwn hij₂
    have hd₂' : dyad i' j' < x₂ := ENNReal.coe_lt_coe.1 hd₂
    refine ⟨i, j, i', j', hd₁, hd₂'.le.trans h2a, fun p q hp hq m => ?_⟩
    obtain ⟨y, hy, hyx⟩ := hsub (mem_image_of_mem α ⟨hij₁.trans hp, hq.trans hd₂'⟩)
    have ht : Tendsto (fun n => dyad n (flr n y)) atTop (𝓝[Icc 0 c] y) :=
      tendsto_nhdsWithin_iff.2 ⟨tendsto_dyad_flr y, Eventually.of_forall fun n =>
        ⟨zero_le, (dyad_flr_le n y).trans hy.2⟩⟩
    have hlim : Tendsto (fun n => β (dyad n (flr n y))) atTop (𝓝 (β y)) := (hβ y hy).tendsto.comp ht
    obtain ⟨N, hN⟩ := Metric.tendsto_atTop.1 hlim _ (by positivity : (0 : ℝ) < 1 / ((m : ℝ) + 1))
    refine ⟨N, flr N y, (dyad_flr_le N y).trans hy.2, ?_⟩
    rw [← hyx, dist_comm]
    exact hN N le_rfl
  · rintro ⟨i, j, i', j', hd, hda, happ⟩
    refine ⟨dyad i j, dyad i' j', hd, hda, ?_⟩
    have hdy : ∀ p q : ℕ, dyad i j < dyad p q → dyad p q < dyad i' j' → α (dyad p q) ∈ β '' Icc 0 c := by
      intro p q hp hq
      rw [← hK.closure_eq]
      refine Metric.mem_closure_iff.2 fun ε hε => ?_
      obtain ⟨m, hm⟩ := exists_nat_one_div_lt hε
      obtain ⟨p', q', hle, hlt⟩ := happ p q hp hq m
      exact ⟨β (dyad p' q'), ⟨dyad p' q', ⟨zero_le, hle⟩, rfl⟩, hlt.trans hm⟩
    rintro _ ⟨x, hx, rfl⟩
    have hxa : x ∈ Icc 0 a := ⟨zero_le, hx.2.le.trans hda⟩
    have ht : Tendsto (fun n => dyad n (flr n x)) atTop (𝓝[Icc 0 a] x) :=
      tendsto_nhdsWithin_iff.2 ⟨tendsto_dyad_flr x, Eventually.of_forall fun n =>
        ⟨zero_le, (dyad_flr_le n x).trans hxa.2⟩⟩
    refine hK.mem_of_tendsto ((hα x hxa).tendsto.comp ht) ?_
    filter_upwards [(tendsto_dyad_flr x).eventually (lt_mem_nhds hx.1)] with n hn
    exact hdy n (flr n x) hn ((dyad_flr_le n x).trans_lt hx.2)

/-! ### From strict prefixes to the whole outgoing paths (Baire) -/

/-- Re-basing an arc inclusion `α([x, y]) ⊆ β([b₀, d])` at the start times `a₀ ≤ x` and `b₀`: the outgoing prefixes
`r ↦ α (a₀ + r)` on `[0, y - a₀]` and `r ↦ β (b₀ + r)` on `[0, d - b₀]` have a common open subarc. -/
theorem hasCommonOpenSubarc_rebase {α β : ℝ≥0 → ℂ} {a₀ b₀ x y d : ℝ≥0} (hax : a₀ ≤ x) (hxy : x < y)
    (h : α '' Icc x y ⊆ β '' Icc b₀ d) :
    HasCommonOpenSubarc (fun r => α (a₀ + r)) (y - a₀) (fun r => β (b₀ + r)) (d - b₀) := by
  refine ⟨x - a₀, y - a₀, tsub_lt_tsub_right_of_le hax hxy, le_rfl, ?_⟩
  rintro _ ⟨r, hr, rfl⟩
  have hr₁ : x < a₀ + r := (tsub_lt_iff_left hax).1 hr.1
  have hr₂ : a₀ + r < y := lt_tsub_iff_left.1 hr.2
  obtain ⟨t, ht, hβt⟩ := h (mem_image_of_mem α ⟨hr₁.le, hr₂.le⟩)
  refine ⟨t - b₀, ⟨zero_le, tsub_le_tsub_right ht.2 b₀⟩, ?_⟩
  show β (b₀ + (t - b₀)) = α (a₀ + r)
  rw [add_tsub_cancel_of_le ht.1]
  exact hβt

/-- The closed strict prefixes `β([b₀, d])` of a path, `d` a dyadic time below `B`, indexed by `ℕ` through
`Nat.unpair` (empty when the dyadic time is not below `B`). -/
def prefixFamily (β : ℝ≥0 → ℂ) (b₀ : ℝ≥0) (B : ℝ≥0∞) (n : ℕ) : Set ℂ :=
  {z | (dyad n.unpair.1 n.unpair.2 : ℝ≥0∞) < B ∧ z ∈ β '' Icc b₀ (dyad n.unpair.1 n.unpair.2)}

theorem isClosed_prefixFamily {β : ℝ≥0 → ℂ} {B : ℝ≥0∞} (hβ : ContinuousOn β {t | (t : ℝ≥0∞) ≤ B})
    (b₀ : ℝ≥0) (n : ℕ) : IsClosed (prefixFamily β b₀ B n) := by
  by_cases hd : (dyad n.unpair.1 n.unpair.2 : ℝ≥0∞) < B
  · have hF : prefixFamily β b₀ B n = β '' Icc b₀ (dyad n.unpair.1 n.unpair.2) := by
      ext z
      simp only [prefixFamily, mem_ofPred_eq, hd, true_and]
    rw [hF]
    exact (isCompact_Icc.image_of_continuousOn (hβ.mono fun t ht =>
      (ENNReal.coe_le_coe.2 ht.2).trans hd.le)).isClosed
  · have hF : prefixFamily β b₀ B n = ∅ := by
      ext z
      simp only [prefixFamily, mem_ofPred_eq, hd, false_and, mem_empty_iff_false]
    rw [hF]
    exact isClosed_empty

/-- **From strict outgoing prefixes to the outgoing available paths.** Let `α`, `β` be continuous on their available
intervals `{t ≤ A}`, `{t ≤ B}`. If no open arc of a strict outgoing prefix `α([a₀, a₀ + u])` (`a₀ + u < A`) lies in a
strict outgoing prefix `β([b₀, b₀ + v])` (`b₀ + v < B`), then no open arc `α((a, a'))`, `a₀ ≤ a < a' ≤ A`, of the
outgoing available path of `α` lies in the outgoing available path `β([b₀, B))`. Proof: a compact sub-arc
`α([p, q])` is covered by the countably many closed prefixes `β([b₀, d])`, `d < B` dyadic; by Baire's theorem one of
them contains a nontrivial sub-arc `α([x, y])`. -/
theorem not_image_Ioo_subset_of_prefix {α β : ℝ≥0 → ℂ} {A B : ℝ≥0∞} {a₀ b₀ : ℝ≥0}
    (hα : ContinuousOn α {t | (t : ℝ≥0∞) ≤ A}) (hβ : ContinuousOn β {t | (t : ℝ≥0∞) ≤ B})
    (hpre : ∀ u v : ℝ≥0, ((a₀ + u : ℝ≥0) : ℝ≥0∞) < A → ((b₀ + v : ℝ≥0) : ℝ≥0∞) < B →
      ¬ HasCommonOpenSubarc (fun r => α (a₀ + r)) u (fun r => β (b₀ + r)) v)
    {a a' : ℝ≥0} (ha : a₀ ≤ a) (haa' : a < a') (ha' : (a' : ℝ≥0∞) ≤ A) :
    ¬ α '' Ioo a a' ⊆ β '' {t | b₀ ≤ t ∧ (t : ℝ≥0∞) < B} := by
  intro hsub
  obtain ⟨p, hap, hpa'⟩ := exists_between haa'
  obtain ⟨q, hpq, hqa'⟩ := exists_between hpa'
  have hqA : (q : ℝ≥0∞) < A := (ENNReal.coe_lt_coe.2 hqa').trans_le ha'
  have hαpq : ContinuousOn α (Icc p q) :=
    hα.mono fun t ht => (ENNReal.coe_le_coe.2 ht.2).trans hqA.le
  have hcov : α '' Icc p q ⊆ ⋃ n, prefixFamily β b₀ B n := by
    rintro _ ⟨x, hx, rfl⟩
    obtain ⟨t, ⟨hbt, htB⟩, hβt⟩ := hsub (mem_image_of_mem α ⟨hap.trans_le hx.1, hx.2.trans_lt hqa'⟩)
    obtain ⟨n, k, htd, hdB⟩ := exists_dyad_btwn htB
    refine mem_iUnion.2 ⟨Nat.pair n k, ?_⟩
    have e : Nat.unpair (Nat.pair n k) = (n, k) := Nat.unpair_pair n k
    show (dyad (Nat.pair n k).unpair.1 (Nat.pair n k).unpair.2 : ℝ≥0∞) < B ∧
      α x ∈ β '' Icc b₀ (dyad (Nat.pair n k).unpair.1 (Nat.pair n k).unpair.2)
    rw [e]
    exact ⟨hdB, t, ⟨hbt, htd.le⟩, hβt⟩
  obtain ⟨n, x, y, hpx, hxy, hyq, hsubF⟩ :=
    Theorem14.GB10.exists_Icc_subset_of_image_subset_iUnion hpq hαpq (isClosed_prefixFamily hβ b₀) hcov
  have hF : ∀ z ∈ α '' Icc x y, (dyad n.unpair.1 n.unpair.2 : ℝ≥0∞) < B ∧
      z ∈ β '' Icc b₀ (dyad n.unpair.1 n.unpair.2) := fun z hz => hsubF hz
  obtain ⟨hdB, t₁, ht₁, -⟩ := hF _ (mem_image_of_mem α (left_mem_Icc.2 hxy.le))
  have hbd : b₀ ≤ dyad n.unpair.1 n.unpair.2 := ht₁.1.trans ht₁.2
  have hax : a₀ ≤ x := ha.trans (hap.le.trans hpx)
  refine hpre (y - a₀) (dyad n.unpair.1 n.unpair.2 - b₀) ?_ ?_
    (hasCommonOpenSubarc_rebase hax hxy fun z hz => (hF z hz).2)
  · rw [add_tsub_cancel_of_le (hax.trans hxy.le)]
    exact (ENNReal.coe_le_coe.2 hyq).trans_lt hqA
  · rw [add_tsub_cancel_of_le hbd]
    exact hdB

/-- **No common open outgoing arc, two-sided, from strict prefixes** (`not_image_Ioo_subset_of_prefix` twice). -/
theorem noCommonOutgoingArc_of_prefix {η₁ η₂ : ℝ≥0 → ℂ} {ζ₁ ζ₂ : ℝ≥0∞} {s₀ t₀ : ℝ≥0}
    (hc₁ : ContinuousOn η₁ {t | (t : ℝ≥0∞) ≤ ζ₁}) (hc₂ : ContinuousOn η₂ {t | (t : ℝ≥0∞) ≤ ζ₂})
    (hpre : ∀ u v : ℝ≥0, ((s₀ + u : ℝ≥0) : ℝ≥0∞) < ζ₁ → ((t₀ + v : ℝ≥0) : ℝ≥0∞) < ζ₂ →
      ¬ HasCommonOpenSubarc (fun r => η₁ (s₀ + r)) u (fun r => η₂ (t₀ + r)) v ∧
        ¬ HasCommonOpenSubarc (fun r => η₂ (t₀ + r)) v (fun r => η₁ (s₀ + r)) u) :
    (∀ a a' : ℝ≥0, s₀ ≤ a → a < a' → (a' : ℝ≥0∞) ≤ ζ₁ →
        ¬ η₁ '' Ioo a a' ⊆ η₂ '' {t | t₀ ≤ t ∧ (t : ℝ≥0∞) < ζ₂}) ∧
      ∀ c c' : ℝ≥0, t₀ ≤ c → c < c' → (c' : ℝ≥0∞) ≤ ζ₂ →
        ¬ η₂ '' Ioo c c' ⊆ η₁ '' {s | s₀ ≤ s ∧ (s : ℝ≥0∞) < ζ₁} :=
  ⟨fun _ _ ha haa' ha' =>
      not_image_Ioo_subset_of_prefix hc₁ hc₂ (fun u v hu hv => (hpre u v hu hv).1) ha haa' ha',
    fun _ _ hc hcc' hc' =>
      not_image_Ioo_subset_of_prefix hc₂ hc₁ (fun v u hv hu => (hpre u v hu hv).2) hc hcc' hc'⟩

/-! ### What the conclusion rules out: merging -/

/-- **No common open outgoing arc excludes merging.** If both paths continue after the contact (`s₀ < ζ₁`,
`t₀ < ζ₂`) and no open arc `η₁((a, a'))`, `s₀ ≤ a < a' ≤ ζ₁`, of the first outgoing available path lies in the second
outgoing available path `η₂([t₀, ζ₂))`, then the two paths do not agree as ordered unparametrized curves after the
contact (`AgreeAsCurvesAfter`, the conclusion of the frozen merging clause, Theorem 1.5 (ii)). Indeed an order
isomorphism `e` of `[s₀, a]` onto `[t₀, c]` with `η₂ ∘ e = η₁` has `s₀ < a` (otherwise its singleton domain could not
reach the two points `t₀ < t₁` of `[t₀, c]`, `c = ζ₂ > t₀`), and then for `s₀ < a' < a` it maps the open arc
`η₁((s₀, a'))` into `η₂([t₀, e(a')])`, with `e(a') < c ≤ ζ₂`. -/
theorem not_agreeAsCurvesAfter_of_noCommonOutgoingArc {η₁ η₂ : ℝ≥0 → ℂ} {ζ₁ ζ₂ : ℝ≥0∞} {s₀ t₀ : ℝ≥0}
    (hs₀ : (s₀ : ℝ≥0∞) < ζ₁) (ht₀ : (t₀ : ℝ≥0∞) < ζ₂)
    (hno : ∀ a a' : ℝ≥0, s₀ ≤ a → a < a' → (a' : ℝ≥0∞) ≤ ζ₁ →
      ¬ η₁ '' Ioo a a' ⊆ η₂ '' {t | t₀ ≤ t ∧ (t : ℝ≥0∞) < ζ₂}) :
    ¬ AgreeAsCurvesAfter η₁ ζ₁ s₀ η₂ ζ₂ t₀ := by
  rintro ⟨a, c, hs₀a, haζ, ht₀c, hcζ, hend, e, he⟩
  -- the domain of `e` is not a singleton
  have hsa : (s₀ : ℝ≥0∞) < a := by
    rcases hend with ha | hc
    · rw [ha]
      exact hs₀
    · by_contra hle
      have ha' : a ≤ s₀ := not_lt.1 hle
      obtain ⟨t₁, ht₀₁, ht₁ζ⟩ := ENNReal.lt_iff_exists_nnreal_btwn.1 ht₀
      have hdom : ∀ x : {s : ℝ≥0 // s₀ ≤ s ∧ (s : ℝ≥0∞) ≤ a}, (x : ℝ≥0) = s₀ := fun x =>
        le_antisymm (ENNReal.coe_le_coe.1 (x.2.2.trans ha')) x.2.1
      have hy₁ : (t₁ : ℝ≥0∞) ≤ c := by
        rw [hc]
        exact ht₁ζ.le
      have heq := e.symm.injective (Subtype.ext ((hdom (e.symm ⟨t₀, le_rfl, ht₀c⟩)).trans
        (hdom (e.symm ⟨t₁, (ENNReal.coe_lt_coe.1 ht₀₁).le, hy₁⟩)).symm))
      exact (ENNReal.coe_lt_coe.1 ht₀₁).ne (congrArg Subtype.val heq)
  obtain ⟨a', hs₀a', ha'a⟩ := ENNReal.lt_iff_exists_nnreal_btwn.1 hsa
  have hs₀a'' : s₀ < a' := ENNReal.coe_lt_coe.1 hs₀a'
  refine hno s₀ a' le_rfl hs₀a'' (ha'a.le.trans haζ) ?_
  rintro _ ⟨x, hx, rfl⟩
  have hxd : s₀ ≤ x ∧ (x : ℝ≥0∞) ≤ a := ⟨hx.1.le, ((ENNReal.coe_lt_coe.2 hx.2).trans ha'a).le⟩
  have had : s₀ ≤ a' ∧ (a' : ℝ≥0∞) ≤ a := ⟨hs₀a''.le, ha'a.le⟩
  have hlt : e ⟨x, hxd⟩ < e ⟨a', had⟩ := e.strictMono (Subtype.mk_lt_mk.2 hx.2)
  refine ⟨(e ⟨x, hxd⟩ : ℝ≥0), ⟨(e ⟨x, hxd⟩).2.1, ?_⟩, he ⟨x, hxd⟩⟩
  exact (ENNReal.coe_lt_coe.2 (Subtype.coe_lt_coe.2 hlt)).trans_le ((e ⟨a', had⟩).2.2.trans hcζ)

/-- **Identical outgoing curves violate the new clause** (the audit's identical-ray diagnostic, §2.2): for one path `η`
read from one contact time `s₀ < ζ` on both sides, some open arc of the outgoing path lies on the outgoing path. So the
no-common-arc clause of `AuditFix.StrongCrossStatement` excludes the identical outgoing curves that the raw predicate
`CrossesFromRightAt` admits. -/
theorem not_noCommonOutgoingArc_self {η : ℝ≥0 → ℂ} {ζ : ℝ≥0∞} {s₀ : ℝ≥0} (hs₀ : (s₀ : ℝ≥0∞) < ζ) :
    ¬ ∀ a a' : ℝ≥0, s₀ ≤ a → a < a' → (a' : ℝ≥0∞) ≤ ζ →
      ¬ η '' Ioo a a' ⊆ η '' {t | s₀ ≤ t ∧ (t : ℝ≥0∞) < ζ} := by
  intro hno
  obtain ⟨a', h1, h2⟩ := ENNReal.lt_iff_exists_nnreal_btwn.1 hs₀
  exact hno s₀ a' le_rfl (ENNReal.coe_lt_coe.1 h1) h2.le
    (image_mono fun t ht => ⟨ht.1.le, (ENNReal.coe_lt_coe.2 ht.2).trans h2⟩)

end Cross

end AuditFix

end InteractingSLE
