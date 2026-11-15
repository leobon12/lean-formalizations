/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.InteractionLens
import InteractingSLE.Foundations.Topology.Jordan.Complex

/-!
# Aux. lemma 33: the Jordan pocket between consecutive ordered common contacts

Packet PROVE-SEC7-A4 (an input of Lemma 7.1, p. 224: "**Aux.** lemma 33 gives the Jordan pocket bounded by the two
corresponding open outer arcs"; also of Aux. lemmas 119–121 in §7.4). Specification §6, Aux. lemma 33
(`source/spec/p145-192.md` L839–L866, pp. 187–188):

> Let `D` be a Jordan domain in the sphere, and let `α, β : [0, 1] → D̄` be continuous injective paths with the same
> distinct endpoints `x, y ∈ ∂D`. Suppose their open paths lie in `D`. Put `S = {s ∈ [0, 1] : α(s) ∈ β([0, 1])}`,
> `j(s) = β⁻¹(α(s))` (`s ∈ S`), and assume that `j` is increasing. Let `(a, b)` be a component of `[0, 1] ∖ S`. Then
> `J = α([a, b]) ∪ β([j(a), j(b)])` (OC9.1) is a Jordan curve. Its side disjoint from the exterior of `D` is a component
> of `D ∖ (α([0, 1]) ∪ β([0, 1]))`, and its boundary consists exactly of the two arcs in (OC9.1). Every remaining portion
> of either path is outside this open component.

The lemma is proved here in the plane `ℂ`, for an open set `D` whose exterior `(closure D)ᶜ` is connected and
unbounded and accumulates at every frontier point of `D` (`frontier D ⊆ closure (closure D)ᶜ`); a bounded Jordan domain
(the bounded side of a Jordan curve) has these properties (`aux33_pocket_of_isJordanCurve`). The sphere form reduces to
it by a Möbius map sending an exterior point to `∞`. In the plane "the side disjoint from the exterior" is the
**bounded** side of `J`, since the exterior is connected, unbounded and disjoint from `J`.

* `aux33_pocket`: **Aux. lemma 33**, the conclusions above;
* `aux33_pocket_of_isJordanCurve`: the same for `D` the bounded side of a Jordan curve;
* `exists_preceding_contact`: **the final assertion** ("there is a preceding common contact `a < b` with no common
  contact strictly between `a` and `b`").

The Jordan curve theorem is `InteractingSLE.Foundations.Jordan.jordan_curve_components_complex` and the union of two
arcs is PROVE-SEC7-B's `Sec7.isJordanCurve_image_union`.
-/

set_option autoImplicit false

noncomputable section

open Set Topology Filter Bornology

namespace InteractingSLE

namespace Sec7

/-! ### Contacts -/

/-- The contact parameters `S = {s ∈ [0, 1] : α(s) ∈ β([0, 1])}` of Aux. lemma 33. -/
def pocketContactSet (α β : ℝ → ℂ) : Set ℝ := {s | s ∈ Icc (0 : ℝ) 1 ∧ α s ∈ β '' Icc 0 1}

/-- The affine image of `[0, 1]` onto `[a, b]`. -/
theorem image_affine_Icc_zero_one {a b : ℝ} (hab : a ≤ b) :
    (fun t : ℝ => a + t * (b - a)) '' Icc 0 1 = Icc a b := by
  ext z
  constructor
  · rintro ⟨t, ⟨ht0, ht1⟩, rfl⟩
    constructor <;> nlinarith
  · rintro ⟨hz1, hz2⟩
    rcases hab.lt_or_eq with hlt | heq
    · refine ⟨(z - a) / (b - a), ⟨div_nonneg (by linarith) (by linarith), ?_⟩, ?_⟩
      · rw [div_le_one (by linarith)]
        linarith
      · field_simp
        ring
    · subst heq
      exact ⟨0, ⟨le_rfl, zero_le_one⟩, by linarith [le_antisymm hz1 hz2]⟩

/-- A subarc of a continuous injective path on `[0, 1]`, reparametrized by `[0, 1]`: continuity, injectivity and
range. -/
theorem subarc_props {γ : ℝ → ℂ} (hγ : ContinuousOn γ (Icc 0 1)) (hγi : InjOn γ (Icc 0 1)) {a b : ℝ}
    (ha : 0 ≤ a) (hab : a < b) (hb : b ≤ 1) :
    ContinuousOn (fun t => γ (a + t * (b - a))) (Icc 0 1) ∧
      InjOn (fun t => γ (a + t * (b - a))) (Icc 0 1) ∧
        (fun t => γ (a + t * (b - a))) '' Icc 0 1 = γ '' Icc a b := by
  have hmaps : MapsTo (fun t : ℝ => a + t * (b - a)) (Icc 0 1) (Icc 0 1) := by
    intro t ht
    have h := (image_affine_Icc_zero_one hab.le) ▸ mem_image_of_mem _ ht
    exact ⟨ha.trans h.1, h.2.trans hb⟩
  refine ⟨hγ.comp (by fun_prop) hmaps, fun t ht t' ht' h => ?_, ?_⟩
  · have h' := hγi (hmaps ht) (hmaps ht') h
    have hba : b - a ≠ 0 := by linarith
    have : t * (b - a) = t' * (b - a) := by linarith
    exact mul_right_cancel₀ hba this
  · rw [← image_affine_Icc_zero_one hab.le, image_image]

/-! ### The pocket -/

section Pocket

variable {D : Set ℂ} {α β : ℝ → ℂ} {j : ℝ → ℝ}

/-- A contact parameter `s` has `j(s) ∈ [0, 1]` and `β(j(s)) = α(s)`. -/
theorem pocketContact_spec (hj : ∀ s ∈ Icc (0 : ℝ) 1, ∀ r ∈ Icc (0 : ℝ) 1, α s = β r → j s = r) {s : ℝ}
    (hs : s ∈ pocketContactSet α β) : j s ∈ Icc (0 : ℝ) 1 ∧ β (j s) = α s := by
  obtain ⟨hs01, r, hr, hrs⟩ := hs
  rw [hj s hs01 r hr hrs.symm]
  exact ⟨hr, hrs⟩

/-- A connected set avoiding a Jordan side `U` of `J`: if it lies off `J` and contains a frontier point of `D` that is
a limit of the exterior, it does not meet the side `U` of `J` disjoint from the exterior. -/
theorem disjoint_side_of_portion {J U P : Set ℂ} {x₁ p : ℂ} (hU : U = connectedComponentIn Jᶜ x₁)
    (hUo : IsOpen U) (hUext : Disjoint U (closure D)ᶜ) (hP : IsPreconnected P) (hPJ : P ⊆ Jᶜ)
    (hp : p ∈ P) (hpcl : p ∈ closure (closure D)ᶜ) : Disjoint P U := by
  have hpU : p ∉ U := by
    intro hpU
    obtain ⟨w, hwU, hwe⟩ := mem_closure_iff.1 hpcl U hUo hpU
    exact hUext.le_bot ⟨hwU, hwe⟩
  have hsub : P ⊆ connectedComponentIn Jᶜ p := hP.subset_connectedComponentIn hp hPJ
  rw [Set.disjoint_left]
  intro q hqP hqU
  have hq : q ∈ connectedComponentIn Jᶜ x₁ := hU ▸ hqU
  have hq' : q ∈ connectedComponentIn Jᶜ p := hsub hqP
  apply hpU
  rw [hU, connectedComponentIn_eq hq, ← connectedComponentIn_eq hq']
  exact mem_connectedComponentIn (hPJ hp)

/-- **Aux. lemma 33** (p. 187), in the plane: the two arcs `α([a, b])` and `β([j(a), j(b)])` between consecutive
ordered common contacts form a Jordan curve `J`; its side `U` disjoint from the exterior of `D` is bounded, lies in `D`,
is a connected component of `D ∖ (α([0, 1]) ∪ β([0, 1]))`, has frontier exactly `J`, and meets neither path. -/
theorem aux33_pocket (hDo : IsOpen D) (hext : IsConnected (closure D)ᶜ)
    (hextu : ¬ IsBounded (closure D)ᶜ) (hfr : frontier D ⊆ closure (closure D)ᶜ)
    (hα : ContinuousOn α (Icc 0 1)) (hβ : ContinuousOn β (Icc 0 1)) (hαi : InjOn α (Icc 0 1))
    (hβi : InjOn β (Icc 0 1)) (h0 : α 0 = β 0) (h1 : α 1 = β 1) (hx : α 0 ∈ frontier D)
    (hy : α 1 ∈ frontier D) (hαD : ∀ s ∈ Ioo (0 : ℝ) 1, α s ∈ D) (hβD : ∀ s ∈ Ioo (0 : ℝ) 1, β s ∈ D)
    (hj : ∀ s ∈ Icc (0 : ℝ) 1, ∀ r ∈ Icc (0 : ℝ) 1, α s = β r → j s = r)
    (hjm : StrictMonoOn j (pocketContactSet α β)) {a b : ℝ} (ha : a ∈ pocketContactSet α β)
    (hb : b ∈ pocketContactSet α β) (hab : a < b) (hgap : ∀ s ∈ Ioo a b, s ∉ pocketContactSet α β) :
    LQGMetric.JordanMap.IsJordanCurve (α '' Icc a b ∪ β '' Icc (j a) (j b)) ∧
      ∃ U : Set ℂ, (∃ x₁ ∈ (α '' Icc a b ∪ β '' Icc (j a) (j b))ᶜ,
          U = connectedComponentIn (α '' Icc a b ∪ β '' Icc (j a) (j b))ᶜ x₁) ∧
        IsOpen U ∧ IsBounded U ∧ Disjoint U (closure D)ᶜ ∧ U ⊆ D ∧
        frontier U = α '' Icc a b ∪ β '' Icc (j a) (j b) ∧
        Disjoint U (α '' Icc 0 1 ∪ β '' Icc 0 1) ∧
        ∃ z ∈ U, connectedComponentIn (D \ (α '' Icc 0 1 ∪ β '' Icc 0 1)) z = U := by
  set J := α '' Icc a b ∪ β '' Icc (j a) (j b) with hJdef
  obtain ⟨ja01, hja⟩ := pocketContact_spec hj ha
  obtain ⟨jb01, hjb⟩ := pocketContact_spec hj hb
  have hjab : j a < j b := hjm ha hb hab
  have ha01 := ha.1
  have hb01 := hb.1
  -- `J` is a Jordan curve
  obtain ⟨huc, hui, hurange⟩ := subarc_props hα hαi ha01.1 hab hb01.2
  obtain ⟨hvc, hvi, hvrange⟩ := subarc_props hβ hβi ja01.1 hjab jb01.2
  have hJ : LQGMetric.JordanMap.IsJordanCurve J := by
    have h := isJordanCurve_image_union huc hvc hui hvi (by simp [hja]) (by simp [hjb]) ?_
    · rwa [hurange, hvrange] at h
    rw [hurange, hvrange]
    rintro z ⟨⟨s, hs, rfl⟩, ⟨r, hr, hrs⟩⟩
    have hs01 : s ∈ Icc (0 : ℝ) 1 := ⟨ha01.1.trans hs.1, hs.2.trans hb01.2⟩
    have hr01 : r ∈ Icc (0 : ℝ) 1 := ⟨ja01.1.trans hr.1, hr.2.trans jb01.2⟩
    have hsS : s ∈ pocketContactSet α β := ⟨hs01, r, hr01, hrs⟩
    have hsab : s = a ∨ s = b := by
      by_contra hne
      push Not at hne
      exact hgap s ⟨lt_of_le_of_ne hs.1 (Ne.symm hne.1), lt_of_le_of_ne hs.2 hne.2⟩ hsS
    simp only [zero_mul, add_zero, one_mul, add_sub_cancel, mem_insert_iff, mem_singleton_iff]
    rcases hsab with rfl | rfl
    · exact Or.inl rfl
    · exact Or.inr rfl
  refine ⟨hJ, ?_⟩
  -- the Jordan curve theorem
  obtain ⟨x₁, hx₁, x₀, hx₀, hbdd, hunb, hdisj, hunion, hfr₁, hfr₀⟩ :=
    Foundations.Jordan.jordan_curve_components_complex hJ
  set U := connectedComponentIn Jᶜ x₁ with hUdef
  have hab01 : Icc a b ⊆ Icc (0 : ℝ) 1 := fun s hs => ⟨ha01.1.trans hs.1, hs.2.trans hb01.2⟩
  have hjab01 : Icc (j a) (j b) ⊆ Icc (0 : ℝ) 1 := fun s hs => ⟨ja01.1.trans hs.1, hs.2.trans jb01.2⟩
  have hJc : IsClosed J :=
    ((isCompact_Icc.image_of_continuousOn (hα.mono hab01)).union
      (isCompact_Icc.image_of_continuousOn (hβ.mono hjab01))).isClosed
  have hUo : IsOpen U := hJc.isOpen_compl.connectedComponentIn
  -- `J` lies in the closure of `D`
  have hcl : ∀ {γ : ℝ → ℂ}, ContinuousOn γ (Icc 0 1) → γ 0 ∈ frontier D → γ 1 ∈ frontier D →
      (∀ s ∈ Ioo (0 : ℝ) 1, γ s ∈ D) → γ '' Icc 0 1 ⊆ closure D := by
    intro γ _ hγ0 hγ1 hγD
    rintro _ ⟨s, hs, rfl⟩
    rcases eq_or_lt_of_le hs.1 with h | h
    · rw [← h]; exact frontier_subset_closure hγ0
    rcases eq_or_lt_of_le hs.2 with h' | h'
    · rw [h']; exact frontier_subset_closure hγ1
    exact subset_closure (hγD s ⟨h, h'⟩)
  have hαcl := hcl hα hx hy hαD
  have hβcl := hcl hβ (h0 ▸ hx) (h1 ▸ hy) hβD
  have hJcl : J ⊆ closure D := by
    exact union_subset ((image_mono hab01).trans hαcl) ((image_mono hjab01).trans hβcl)
  -- the exterior lies on the unbounded side, so `U` is disjoint from it
  have hextJ : (closure D)ᶜ ⊆ Jᶜ := compl_subset_compl.2 hJcl
  have hUext : Disjoint U (closure D)ᶜ := by
    obtain ⟨p, hp⟩ := hext.nonempty
    have hsub : (closure D)ᶜ ⊆ connectedComponentIn Jᶜ p :=
      hext.isPreconnected.subset_connectedComponentIn hp hextJ
    have hpU : p ∉ U := by
      intro hpU
      have heq : connectedComponentIn Jᶜ p = U := by
        rw [hUdef, connectedComponentIn_eq hpU]
      exact hextu (hbdd.subset (heq ▸ hsub))
    rw [Set.disjoint_left]
    intro q hqU hqe
    apply hpU
    have h1' : q ∈ connectedComponentIn Jᶜ p := hsub hqe
    rw [hUdef, connectedComponentIn_eq hqU, ← connectedComponentIn_eq h1']
    exact mem_connectedComponentIn (hextJ hp)
  -- `U` lies in `D`
  have hUD : U ⊆ D := by
    intro z hzU
    by_contra hzD
    have hzcl : z ∈ closure D := by
      by_contra hzcl
      exact hUext.le_bot ⟨hzU, hzcl⟩
    have hzfr : z ∈ frontier D := by rw [hDo.frontier_eq]; exact ⟨hzcl, hzD⟩
    obtain ⟨w, hwU, hwe⟩ := mem_closure_iff.1 (hfr hzfr) U hUo hzU
    exact hUext.le_bot ⟨hwU, hwe⟩
  have hUJ : U ⊆ Jᶜ := connectedComponentIn_subset _ _
  -- the remaining portions of the two paths stay off `U`
  have hportion := fun {P : Set ℂ} {p : ℂ} (hP : IsPreconnected P) (hPJ : P ⊆ Jᶜ) (hp : p ∈ P)
      (hpfr : p ∈ frontier D) => disjoint_side_of_portion (D := D) (J := J) (x₁ := x₁) rfl hUo
      hUext hP hPJ hp (hfr hpfr)
  -- a point of `α` off `[a, b]` is off `J`
  have hαoff : ∀ s ∈ Icc (0 : ℝ) 1, s ∉ Icc a b → α s ∉ J := by
    intro s hs hsab hsJ
    rcases hsJ with ⟨t, ht, hts⟩ | ⟨r, hr, hrs⟩
    · have ht01 : t ∈ Icc (0 : ℝ) 1 := ⟨ha01.1.trans ht.1, ht.2.trans hb01.2⟩
      exact hsab (hαi ht01 hs hts ▸ ht)
    · have hr01 : r ∈ Icc (0 : ℝ) 1 := ⟨ja01.1.trans hr.1, hr.2.trans jb01.2⟩
      have hsS : s ∈ pocketContactSet α β := ⟨hs, r, hr01, hrs⟩
      have hjs : j s = r := hj s hs r hr01 hrs.symm
      rcases not_and_or.1 hsab with h | h
      · have := hjm hsS ha (lt_of_not_ge h)
        linarith [hr.1]
      · have := hjm hb hsS (lt_of_not_ge h)
        linarith [hr.2]
  -- a point of `β` off `[j a, j b]` is off `J`
  have hβoff : ∀ r ∈ Icc (0 : ℝ) 1, r ∉ Icc (j a) (j b) → β r ∉ J := by
    intro r hr hrj hrJ
    rcases hrJ with ⟨t, ht, hts⟩ | ⟨r', hr', hrs⟩
    · have ht01 : t ∈ Icc (0 : ℝ) 1 := ⟨ha01.1.trans ht.1, ht.2.trans hb01.2⟩
      have htS : t ∈ pocketContactSet α β := ⟨ht01, r, hr, hts.symm⟩
      have hjt : j t = r := hj t ht01 r hr hts
      have htab : t = a ∨ t = b := by
        by_contra hne
        push Not at hne
        exact hgap t ⟨lt_of_le_of_ne ht.1 (Ne.symm hne.1), lt_of_le_of_ne ht.2 hne.2⟩ htS
      rcases htab with rfl | rfl
      · exact hrj (hjt ▸ ⟨le_rfl, hjab.le⟩)
      · exact hrj (hjt ▸ ⟨hjab.le, le_rfl⟩)
    · have hr'01 : r' ∈ Icc (0 : ℝ) 1 := ⟨ja01.1.trans hr'.1, hr'.2.trans jb01.2⟩
      exact hrj (hβi hr'01 hr hrs ▸ hr')
  -- the four portions
  have hpα0 : Disjoint (α '' Ico 0 a) U := by
    rcases eq_or_lt_of_le ha01.1 with h | h
    · rw [← h, Ico_self, image_empty]; exact Set.empty_disjoint U
    refine hportion ((isPreconnected_Ico).image _ (hα.mono fun s hs => ⟨hs.1, hs.2.le.trans
      ha01.2⟩)) ?_ ⟨0, ⟨le_rfl, h⟩, rfl⟩ hx
    rintro _ ⟨s, hs, rfl⟩
    exact hαoff s ⟨hs.1, hs.2.le.trans ha01.2⟩ fun h' => absurd h'.1 (not_le.2 hs.2)
  have hpα1 : Disjoint (α '' Ioc b 1) U := by
    rcases eq_or_lt_of_le hb01.2 with h | h
    · rw [h, Ioc_self, image_empty]; exact Set.empty_disjoint U
    refine hportion ((isPreconnected_Ioc).image _ (hα.mono fun s hs => ⟨hb01.1.trans hs.1.le,
      hs.2⟩)) ?_ ⟨1, ⟨h, le_rfl⟩, rfl⟩ hy
    rintro _ ⟨s, hs, rfl⟩
    exact hαoff s ⟨hb01.1.trans hs.1.le, hs.2⟩ fun h' => absurd h'.2 (not_le.2 hs.1)
  have hpβ0 : Disjoint (β '' Ico 0 (j a)) U := by
    rcases eq_or_lt_of_le ja01.1 with h | h
    · rw [← h, Ico_self, image_empty]; exact Set.empty_disjoint U
    refine hportion ((isPreconnected_Ico).image _ (hβ.mono fun s hs => ⟨hs.1, hs.2.le.trans
      ja01.2⟩)) ?_ ⟨0, ⟨le_rfl, h⟩, rfl⟩ (h0 ▸ hx)
    rintro _ ⟨s, hs, rfl⟩
    exact hβoff s ⟨hs.1, hs.2.le.trans ja01.2⟩ fun h' => absurd h'.1 (not_le.2 hs.2)
  have hpβ1 : Disjoint (β '' Ioc (j b) 1) U := by
    rcases eq_or_lt_of_le jb01.2 with h | h
    · rw [h, Ioc_self, image_empty]; exact Set.empty_disjoint U
    refine hportion ((isPreconnected_Ioc).image _ (hβ.mono fun s hs => ⟨jb01.1.trans hs.1.le,
      hs.2⟩)) ?_ ⟨1, ⟨h, le_rfl⟩, rfl⟩ (h1 ▸ hy)
    rintro _ ⟨s, hs, rfl⟩
    exact hβoff s ⟨jb01.1.trans hs.1.le, hs.2⟩ fun h' => absurd h'.2 (not_le.2 hs.1)
  -- `U` meets neither path
  have hUpaths : Disjoint U (α '' Icc 0 1 ∪ β '' Icc 0 1) := by
    rw [Set.disjoint_union_right]
    constructor
    · rw [Set.disjoint_right]
      rintro _ ⟨s, hs, rfl⟩ hsU
      by_cases hsa : s < a
      · exact Set.disjoint_left.1 hpα0 ⟨s, ⟨hs.1, hsa⟩, rfl⟩ hsU
      by_cases hsb : b < s
      · exact Set.disjoint_left.1 hpα1 ⟨s, ⟨hsb, hs.2⟩, rfl⟩ hsU
      exact hUJ hsU (Or.inl ⟨s, ⟨not_lt.1 hsa, not_lt.1 hsb⟩, rfl⟩)
    · rw [Set.disjoint_right]
      rintro _ ⟨s, hs, rfl⟩ hsU
      by_cases hsa : s < j a
      · exact Set.disjoint_left.1 hpβ0 ⟨s, ⟨hs.1, hsa⟩, rfl⟩ hsU
      by_cases hsb : j b < s
      · exact Set.disjoint_left.1 hpβ1 ⟨s, ⟨hsb, hs.2⟩, rfl⟩ hsU
      exact hUJ hsU (Or.inr ⟨s, ⟨not_lt.1 hsa, not_lt.1 hsb⟩, rfl⟩)
  -- `U` is a component of the complement of the two paths in `D`
  have hRJ : D \ (α '' Icc 0 1 ∪ β '' Icc 0 1) ⊆ Jᶜ := by
    intro z hz hzJ
    refine hz.2 ?_
    rcases hzJ with ⟨s, hs, rfl⟩ | ⟨s, hs, rfl⟩
    · exact Or.inl ⟨s, ⟨ha01.1.trans hs.1, hs.2.trans hb01.2⟩, rfl⟩
    · exact Or.inr ⟨s, ⟨ja01.1.trans hs.1, hs.2.trans jb01.2⟩, rfl⟩
  have hx₁U : x₁ ∈ U := mem_connectedComponentIn hx₁
  refine ⟨U, ⟨x₁, hx₁, rfl⟩, hUo, hbdd, hUext, hUD, hfr₁, hUpaths, x₁, hx₁U, ?_⟩
  have hUR : U ⊆ D \ (α '' Icc 0 1 ∪ β '' Icc 0 1) := fun z hz =>
    ⟨hUD hz, fun h => Set.disjoint_left.1 hUpaths hz h⟩
  refine Subset.antisymm ?_ ((isPreconnected_connectedComponentIn).subset_connectedComponentIn
    hx₁U hUR)
  exact (isPreconnected_connectedComponentIn).subset_connectedComponentIn
    (mem_connectedComponentIn (hUR hx₁U)) ((connectedComponentIn_subset _ _).trans hRJ)

/-- The bounded side `D` of a Jordan curve `Γ` satisfies the hypotheses of `aux33_pocket` on `D`: it is open, its
exterior `(closure D)ᶜ` is the unbounded side (connected and unbounded), and its frontier `Γ` is in the closure of the
exterior. -/
theorem isJordanInterior_props {Γ : Set ℂ} (hΓ : LQGMetric.JordanMap.IsJordanCurve Γ) {z : ℂ}
    (hz : z ∈ Γᶜ) (hDb : IsBounded (connectedComponentIn Γᶜ z)) :
    IsOpen (connectedComponentIn Γᶜ z) ∧ IsConnected (closure (connectedComponentIn Γᶜ z))ᶜ ∧
      ¬ IsBounded (closure (connectedComponentIn Γᶜ z))ᶜ ∧
      frontier (connectedComponentIn Γᶜ z) ⊆ closure (closure (connectedComponentIn Γᶜ z))ᶜ ∧
      frontier (connectedComponentIn Γᶜ z) = Γ := by
  obtain ⟨x₁, hx₁, x₀, hx₀, hbdd, hunb, hdisj, hunion, hfr₁, hfr₀⟩ :=
    Foundations.Jordan.jordan_curve_components_complex hΓ
  have hΓc : IsClosed Γ := hfr₁ ▸ isClosed_frontier
  -- `z` lies in the bounded side
  have hzU : connectedComponentIn Γᶜ z = connectedComponentIn Γᶜ x₁ := by
    have hz' := hz
    rw [hunion] at hz'
    rcases hz' with h | h
    · exact (connectedComponentIn_eq h).symm
    · exact absurd ((connectedComponentIn_eq h).symm ▸ hDb) hunb
  rw [hzU]
  have hUo : IsOpen (connectedComponentIn Γᶜ x₁) := hΓc.isOpen_compl.connectedComponentIn
  -- the complement of the closure of the bounded side is the unbounded side
  have hext : (closure (connectedComponentIn Γᶜ x₁))ᶜ = connectedComponentIn Γᶜ x₀ := by
    rw [closure_eq_self_union_frontier, hfr₁]
    ext w
    constructor
    · intro hw
      have hwΓ : w ∈ Γᶜ := fun h => hw (Or.inr h)
      rw [hunion] at hwΓ
      rcases hwΓ with h | h
      · exact absurd (Or.inl h) hw
      · exact h
    · intro hw hw'
      rcases hw' with h | h
      · exact hdisj.le_bot ⟨h, hw⟩
      · exact connectedComponentIn_subset _ _ hw h
  rw [hext]
  refine ⟨hUo, isConnected_connectedComponentIn_iff.2 hx₀, hunb, ?_, hfr₁⟩
  intro w hw
  rw [hfr₁, ← hfr₀] at hw
  exact frontier_subset_closure hw

/-- **Aux. lemma 33 for a bounded Jordan domain** `D` (the bounded side of a Jordan curve `Γ`): the paths run in `D`
between two distinct points of `Γ`. -/
theorem aux33_pocket_of_isJordanCurve {Γ : Set ℂ} (hΓ : LQGMetric.JordanMap.IsJordanCurve Γ) {z : ℂ}
    (hz : z ∈ Γᶜ) (hDb : IsBounded (connectedComponentIn Γᶜ z))
    (hα : ContinuousOn α (Icc 0 1)) (hβ : ContinuousOn β (Icc 0 1)) (hαi : InjOn α (Icc 0 1))
    (hβi : InjOn β (Icc 0 1)) (h0 : α 0 = β 0) (h1 : α 1 = β 1) (hx : α 0 ∈ Γ) (hy : α 1 ∈ Γ)
    (hαD : ∀ s ∈ Ioo (0 : ℝ) 1, α s ∈ connectedComponentIn Γᶜ z)
    (hβD : ∀ s ∈ Ioo (0 : ℝ) 1, β s ∈ connectedComponentIn Γᶜ z)
    (hj : ∀ s ∈ Icc (0 : ℝ) 1, ∀ r ∈ Icc (0 : ℝ) 1, α s = β r → j s = r)
    (hjm : StrictMonoOn j (pocketContactSet α β)) {a b : ℝ} (ha : a ∈ pocketContactSet α β)
    (hb : b ∈ pocketContactSet α β) (hab : a < b) (hgap : ∀ s ∈ Ioo a b, s ∉ pocketContactSet α β) :
    LQGMetric.JordanMap.IsJordanCurve (α '' Icc a b ∪ β '' Icc (j a) (j b)) ∧
      ∃ U : Set ℂ, (∃ x₁ ∈ (α '' Icc a b ∪ β '' Icc (j a) (j b))ᶜ,
          U = connectedComponentIn (α '' Icc a b ∪ β '' Icc (j a) (j b))ᶜ x₁) ∧
        IsOpen U ∧ IsBounded U ∧ Disjoint U (closure (connectedComponentIn Γᶜ z))ᶜ ∧
        U ⊆ connectedComponentIn Γᶜ z ∧
        frontier U = α '' Icc a b ∪ β '' Icc (j a) (j b) ∧
        Disjoint U (α '' Icc 0 1 ∪ β '' Icc 0 1) ∧
        ∃ w ∈ U, connectedComponentIn (connectedComponentIn Γᶜ z \ (α '' Icc 0 1 ∪ β '' Icc 0 1)) w
          = U := by
  obtain ⟨hDo, hext, hextu, hfr, hfrΓ⟩ := isJordanInterior_props hΓ hz hDb
  exact aux33_pocket hDo hext hextu hfr hα hβ hαi hβi h0 h1 (by rw [hfrΓ]; exact hx) (by rw [hfrΓ]; exact hy) hαD hβD hj
    hjm ha hb hab hgap

/-- **Aux. lemma 33, final assertion** (p. 188): "fix `s₁, s₂ ∈ (0, 1)` and let `b` be the first common contact which
is at or after both parameters: `b = min{s ∈ S : s ≥ s₁, j(s) ≥ s₂}`. If `b > s₁` and `j(b) > s₂`, there is a preceding
common contact `a < b` with no common contact strictly between `a` and `b`" (and `aux33_pocket` then gives the pocket
ending at `α(b)`). -/
theorem exists_preceding_contact (hα : ContinuousOn α (Icc 0 1)) (h0 : α 0 = β 0) (h1 : α 1 = β 1)
    (hj : ∀ s ∈ Icc (0 : ℝ) 1, ∀ r ∈ Icc (0 : ℝ) 1, α s = β r → j s = r)
    (hβ : ContinuousOn β (Icc 0 1)) {s₁ s₂ : ℝ} (hs₁ : s₁ ∈ Ioo (0 : ℝ) 1) (hs₂ : s₂ ∈ Ioo (0 : ℝ) 1) :
    ∃ b, (b ∈ pocketContactSet α β ∧ s₁ ≤ b ∧ s₂ ≤ j b) ∧
      (∀ s, s ∈ pocketContactSet α β → s₁ ≤ s → s₂ ≤ j s → b ≤ s) ∧
      (s₁ < b → s₂ < j b → ∃ a ∈ pocketContactSet α β, a < b ∧
        ∀ s ∈ Ioo a b, s ∉ pocketContactSet α β) := by
  -- closed sets of contacts
  have hclosed : ∀ {c d : ℝ}, Icc c d ⊆ Icc 0 1 → ∀ {e f : ℝ}, Icc e f ⊆ Icc 0 1 →
      IsClosed (Icc c d ∩ α ⁻¹' (β '' Icc e f)) := fun hcd _ _ hef =>
    (hα.mono hcd).preimage_isClosed_of_isClosed isClosed_Icc
      (isCompact_Icc.image_of_continuousOn (hβ.mono hef)).isClosed
  have hsub01 : Icc s₁ 1 ⊆ Icc (0 : ℝ) 1 := fun s hs => ⟨hs₁.1.le.trans hs.1, hs.2⟩
  have hsub02 : Icc s₂ 1 ⊆ Icc (0 : ℝ) 1 := fun s hs => ⟨hs₂.1.le.trans hs.1, hs.2⟩
  have hsub03 : Icc 0 s₂ ⊆ Icc (0 : ℝ) 1 := fun s hs => ⟨hs.1, hs.2.trans hs₂.2.le⟩
  set T := Icc s₁ 1 ∩ α ⁻¹' (β '' Icc s₂ 1) with hTdef
  have hT : ∀ s, s ∈ T ↔ s ∈ pocketContactSet α β ∧ s₁ ≤ s ∧ s₂ ≤ j s := by
    intro s
    constructor
    · rintro ⟨hs, r, hr, hrs⟩
      have hjs := hj s (hsub01 hs) r (hsub02 hr) hrs.symm
      exact ⟨⟨hsub01 hs, r, hsub02 hr, hrs⟩, hs.1, hjs ▸ hr.1⟩
    · rintro ⟨⟨hs01, r, hr, hrs⟩, hs1, hs2⟩
      have hjs := hj s hs01 r hr hrs.symm
      exact ⟨⟨hs1, hs01.2⟩, r, ⟨hjs ▸ hs2, hr.2⟩, hrs⟩
  have hTc : IsClosed T := hclosed hsub01 hsub02
  have h1T : (1 : ℝ) ∈ T := ⟨⟨hs₁.2.le, le_rfl⟩, 1, ⟨hs₂.2.le, le_rfl⟩, h1.symm⟩
  have hTne : T.Nonempty := ⟨1, h1T⟩
  have hTbdd : BddBelow T := ⟨s₁, fun s hs => hs.1.1⟩
  set b := sInf T with hbdef
  have hbT : b ∈ T := hTc.csInf_mem hTne hTbdd
  refine ⟨b, (hT b).1 hbT, fun s hs hs1 hs2 => csInf_le hTbdd ((hT s).2 ⟨hs, hs1, hs2⟩),
    fun hb1 hb2 => ?_⟩
  -- the contacts before `b` lie in the closed set `K`, which does not contain `b`
  set S := Icc (0 : ℝ) 1 ∩ α ⁻¹' (β '' Icc 0 1) with hSdef
  have hSc : IsClosed S := hclosed subset_rfl subset_rfl
  have hSeq : S = pocketContactSet α β := rfl
  set K := Icc 0 s₁ ∪ (Icc (0 : ℝ) 1 ∩ α ⁻¹' (β '' Icc 0 s₂)) with hKdef
  have hKc : IsClosed K := isClosed_Icc.union (hclosed subset_rfl hsub03)
  set A := S ∩ Ico 0 b with hAdef
  have hAK : A ⊆ S ∩ K := by
    rintro s ⟨hsS, hs0, hsb⟩
    refine ⟨hsS, ?_⟩
    by_cases hs1 : s₁ ≤ s
    · have hjs : ¬ s₂ ≤ j s := fun h2 => (not_le.2 hsb) (csInf_le hTbdd ((hT s).2 ⟨hsS, hs1, h2⟩))
      obtain ⟨hj01, hjβ⟩ := pocketContact_spec hj hsS
      exact Or.inr ⟨hsS.1, j s, ⟨hj01.1, (not_le.1 hjs).le⟩, hjβ⟩
    · exact Or.inl ⟨hs0, (not_le.1 hs1).le⟩
  have hbK : b ∉ K := by
    rintro (h | ⟨hb01, r, hr, hrb⟩)
    · exact absurd h.2 (not_le.2 hb1)
    · have := hj b hb01 r (hsub03 hr) hrb.symm
      linarith [hr.2]
  have h0A : (0 : ℝ) ∈ A := ⟨⟨⟨le_rfl, zero_le_one⟩, 0, ⟨le_rfl, zero_le_one⟩, h0.symm⟩, le_rfl,
    hs₁.1.trans hb1⟩
  have hAbdd : BddAbove A := ⟨b, fun s hs => hs.2.2.le⟩
  set a := sSup A with hadef
  have haK : a ∈ S ∩ K :=
    closure_minimal hAK (hSc.inter hKc) (csSup_mem_closure ⟨0, h0A⟩ hAbdd)
  have hab : a ≤ b := csSup_le ⟨0, h0A⟩ fun s hs => hs.2.2.le
  have hab' : a < b := lt_of_le_of_ne hab fun h => hbK (h ▸ haK.2)
  refine ⟨a, haK.1, hab', fun s hs hsS => ?_⟩
  have hsA : s ∈ A := ⟨hsS, haK.1.1.1.trans hs.1.le, hs.2⟩
  exact absurd (le_csSup hAbdd hsA) (not_le.2 hs.1)

end Pocket

end Sec7

end InteractingSLE
