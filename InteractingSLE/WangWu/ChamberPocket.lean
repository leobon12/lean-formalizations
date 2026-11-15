/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.WangWu.ChamberOrder
import InteractingSLE.Spec.Sec7.TwoForceMain3Pocket

/-!
# The components between two ordered crosscuts are Jordan pockets

Packet PROVE-WW-B4. Wang–Wu (`source/external/WW17LP/wang_wu_lean_preprocessed.pdf`, ruling R31), proof of
Proposition 4.20: "A component between two ordered simple arcs is bounded by one subarc of each, with common
endpoints and disjoint interiors. This follows by applying the Jordan curve theorem to the arcs between successive
common endpoints. It is a Jordan domain in the sphere." The specification's proof of Lemma 7.1 (p. 224) says the
same: "The outer common-contact set is compact. Each complementary gap has two endpoints, and **Aux.** lemma 33 gives
the Jordan pocket bounded by the two corresponding open outer arcs. These are exactly the nonempty between-components."

Here, for crosscuts `α` (lower) and `β` (upper, avoiding the lower side of `α`) of the unit disc:

* `contactMap α β`: the parameter `j(s) = β⁻¹(α s)` of a contact; `strictMonoOn_contactMap` (Aux. lemma 93);
* `pocket_props`: **Aux. lemma 33** (`Sec7.aux33_pocket_of_isJordanCurve` in the unit disc): for a gap `(a, b)` of the
  contact set, `J = α[a, b] ∪ β[j a, j b]` is a Jordan curve, its inside lies in the disc off both crosscuts, has
  frontier `J`, and is a component of `𝔻 \ (α ∪ β)`;
* `connectedComponentIn_eq_pocket`: **every component between the crosscuts is such a pocket** — a point of the open
  upper side of `α` and lower side of `β` lies in the pocket of a gap. Its component has a boundary point on `α`
  off `β` (otherwise it would fill the lower side of `β`, which meets the lower side of `α`); near such a point the
  upper side of `α` is locally connected (Schoenflies) and meets both the component and the pocket of the
  surrounding gap.
-/

set_option autoImplicit false

noncomputable section

open Set Metric Filter Topology Complex Bornology

namespace InteractingSLE.WangWu

/-- Closure points inside an open set of a component of that open set belong to the component. -/
theorem mem_connectedComponentIn_of_mem_closure {O : Set ℂ} (hO : IsOpen O) {z w : ℂ} (hw : w ∈ O)
    (hcl : w ∈ closure (connectedComponentIn O z)) : w ∈ connectedComponentIn O z := by
  obtain ⟨v, hv, hvz⟩ := mem_closure_iff.1 hcl _ hO.connectedComponentIn (mem_connectedComponentIn hw)
  rw [connectedComponentIn_eq hvz, ← connectedComponentIn_eq hv]
  exact mem_connectedComponentIn hw

/-- Two components of the same set sharing a point are equal. -/
theorem connectedComponentIn_eq_of_mem_of_mem {O : Set ℂ} {z w v : ℂ} (hz : v ∈ connectedComponentIn O z)
    (hw : v ∈ connectedComponentIn O w) : connectedComponentIn O z = connectedComponentIn O w := by
  rw [connectedComponentIn_eq hz, connectedComponentIn_eq hw]

/-- The bounded component of a Jordan curve containing a given point is the inside. -/
theorem connectedComponentIn_eq_jordanIn {Γ : Set ℂ} (hΓ : LQGMetric.JordanMap.IsJordanCurve Γ) {x : ℂ}
    (hx : x ∈ Γᶜ) (hb : IsBounded (connectedComponentIn Γᶜ x)) : connectedComponentIn Γᶜ x = jordanIn Γ := by
  have hxI : x ∈ jordanIn Γ := ⟨hx, hb⟩
  refine Subset.antisymm (fun z hz => ⟨connectedComponentIn_subset _ _ hz, ?_⟩)
    ((isPreconnected_jordanIn hΓ).subset_connectedComponentIn hxI (jordanIn_subset_compl Γ))
  rw [← connectedComponentIn_eq hz]
  exact hb

theorem isJordanCurve_sphere : LQGMetric.JordanMap.IsJordanCurve (sphere (0 : ℂ) 1) :=
  ⟨id, continuousOn_id, injOn_id _, image_id _⟩

theorem connectedComponentIn_compl_sphere :
    connectedComponentIn (sphere (0 : ℂ) 1)ᶜ 0 = ball 0 1 := by
  have h0 : (0 : ℂ) ∈ (sphere (0 : ℂ) 1)ᶜ := by simp
  have hball : ball (0 : ℂ) 1 ⊆ (sphere (0 : ℂ) 1)ᶜ := fun w hw hws => by
    rw [mem_ball, dist_zero_right] at hw
    rw [mem_sphere_zero_iff_norm] at hws
    linarith
  refine Subset.antisymm ?_ ((convex_ball 0 1).isPreconnected.subset_connectedComponentIn
    (mem_ball_self one_pos) hball)
  have hsplit : (sphere (0 : ℂ) 1)ᶜ ⊆ ball 0 1 ∪ {w : ℂ | 1 < ‖w‖} := fun w hw => by
    rw [mem_compl_iff, mem_sphere_zero_iff_norm] at hw
    rcases lt_or_gt_of_ne hw with h | h
    · left; rwa [mem_ball, dist_zero_right]
    · right; exact h
  rcases IsPreconnected.subset_or_subset isOpen_ball (isOpen_lt continuous_const continuous_norm)
    (Set.disjoint_left.2 fun w h₁ h₂ => by
      rw [mem_ball, dist_zero_right] at h₁; exact absurd h₂ (not_lt.2 h₁.le))
    ((connectedComponentIn_subset _ _).trans hsplit) isPreconnected_connectedComponentIn with h | h
  · exact h
  · have := h (mem_connectedComponentIn h0)
    norm_num at this

/-! ### Contacts -/

/-- The contact parameter `j(s) = β⁻¹(α s)` (Aux. lemma 33). -/
def contactMap (α β : ℝ → ℂ) (s : ℝ) : ℝ := Function.invFunOn β (Icc 0 1) (α s)

variable {α β : ℝ → ℂ}

theorem contactMap_eq (hβ : IsDiscCrosscut β) {s r : ℝ} (hr : r ∈ Icc (0 : ℝ) 1) (h : α s = β r) :
    contactMap α β s = r := by
  have hex : ∃ a ∈ Icc (0 : ℝ) 1, β a = α s := ⟨r, hr, h.symm⟩
  have h1 := Function.invFunOn_mem hex
  have h2 := Function.invFunOn_eq hex
  exact hβ.inj h1 hr (h2.trans h)

theorem contactMap_mem (hβ : IsDiscCrosscut β) {s : ℝ} (hs : s ∈ Sec7.pocketContactSet α β) :
    contactMap α β s ∈ Icc (0 : ℝ) 1 ∧ β (contactMap α β s) = α s := by
  obtain ⟨-, r, hr, hrs⟩ := hs
  rw [contactMap_eq hβ hr hrs.symm]
  exact ⟨hr, hrs⟩

theorem strictMonoOn_contactMap (hα : IsDiscCrosscut α) (hβ : IsDiscCrosscut β)
    (hord : Disjoint (crossRange β) (crossSide α (-1))) :
    StrictMonoOn (contactMap α β) (Sec7.pocketContactSet α β) := by
  intro s hs s' hs' hss
  obtain ⟨hj, hjs⟩ := contactMap_mem hβ hs
  obtain ⟨hj', hjs'⟩ := contactMap_mem hβ hs'
  exact hα.lt_of_contact hβ hord hs.1 hs'.1 hj hj' hjs.symm hjs'.symm hss

theorem isClosed_pocketContactSet (hα : IsDiscCrosscut α) (hβ : IsDiscCrosscut β) :
    IsClosed (Sec7.pocketContactSet α β) :=
  hα.cont.preimage_isClosed_of_isClosed isClosed_Icc
    (isCompact_Icc.image_of_continuousOn hβ.cont).isClosed

theorem zero_mem_pocketContactSet (hα : IsDiscCrosscut α) (hβ : IsDiscCrosscut β) :
    (0 : ℝ) ∈ Sec7.pocketContactSet α β :=
  ⟨⟨le_rfl, zero_le_one⟩, 0, ⟨le_rfl, zero_le_one⟩, by rw [hα.zero, hβ.zero]⟩

theorem one_mem_pocketContactSet (hα : IsDiscCrosscut α) (hβ : IsDiscCrosscut β) :
    (1 : ℝ) ∈ Sec7.pocketContactSet α β :=
  ⟨⟨zero_le_one, le_rfl⟩, 1, ⟨zero_le_one, le_rfl⟩, by rw [hα.one, hβ.one]⟩

/-! ### The pockets -/

/-- The boundary curve `α[a, b] ∪ β[j a, j b]` of the pocket of a gap `(a, b)`. -/
def pocketCurve (α β : ℝ → ℂ) (a b : ℝ) : Set ℂ :=
  α '' Icc a b ∪ β '' Icc (contactMap α β a) (contactMap α β b)

/-- A gap of the contact set. -/
def IsContactGap (α β : ℝ → ℂ) (a b : ℝ) : Prop :=
  a ∈ Sec7.pocketContactSet α β ∧ b ∈ Sec7.pocketContactSet α β ∧ a < b ∧
    ∀ s ∈ Ioo a b, s ∉ Sec7.pocketContactSet α β

/-- **Aux. lemma 33 in the disc.** The pocket of a gap is the inside of a Jordan curve, lies in the disc off both
crosscuts, has frontier `α[a, b] ∪ β[j a, j b]`, and is a component of `𝔻 \ (α ∪ β)`. -/
theorem pocket_props (hα : IsDiscCrosscut α) (hβ : IsDiscCrosscut β)
    (hord : Disjoint (crossRange β) (crossSide α (-1))) {a b : ℝ} (hg : IsContactGap α β a b) :
    LQGMetric.JordanMap.IsJordanCurve (pocketCurve α β a b) ∧
      jordanIn (pocketCurve α β a b) ⊆ ball 0 1 ∧
      Disjoint (jordanIn (pocketCurve α β a b)) (crossRange α ∪ crossRange β) ∧
      frontier (jordanIn (pocketCurve α β a b)) = pocketCurve α β a b ∧
      ∃ w ∈ jordanIn (pocketCurve α β a b),
        connectedComponentIn (ball 0 1 \ (crossRange α ∪ crossRange β)) w = jordanIn (pocketCurve α β a b) := by
  obtain ⟨ha, hb, hab, hgap⟩ := hg
  have h0 : (0 : ℂ) ∈ (sphere (0 : ℂ) 1)ᶜ := by simp
  have hD := connectedComponentIn_compl_sphere
  have hDb : IsBounded (connectedComponentIn (sphere (0 : ℂ) 1)ᶜ 0) := by rw [hD]; exact isBounded_ball
  obtain ⟨hJ, U, ⟨x₁, hx₁, rfl⟩, -, hUb, -, hUD, hUfr, hUαβ, w, hwU, hwc⟩ :=
    Sec7.aux33_pocket_of_isJordanCurve isJordanCurve_sphere h0 hDb hα.cont hβ.cont hα.inj hβ.inj
      (by rw [hα.zero, hβ.zero]) (by rw [hα.one, hβ.one])
      (by rw [hα.zero, mem_sphere_zero_iff_norm]; simp) (by rw [hα.one, mem_sphere_zero_iff_norm]; simp)
      (fun s hs => by rw [hD]; exact hα.mem_disc s hs) (fun s hs => by rw [hD]; exact hβ.mem_disc s hs)
      (fun s _ r hr h => contactMap_eq hβ hr h) (strictMonoOn_contactMap hα hβ hord) ha hb hab hgap
  have hU := connectedComponentIn_eq_jordanIn hJ hx₁ hUb
  rw [hD] at hUD hwc
  refine ⟨hJ, hU ▸ hUD, hU ▸ hUαβ, hU ▸ hUfr, w, hU ▸ hwU, hU ▸ hwc⟩

/-- **Every component between two ordered crosscuts is a pocket** (Wang–Wu, proof of Proposition 4.20; specification,
proof of Lemma 7.1: "These are exactly the nonempty between-components"). -/
theorem exists_contactGap_of_between (hα : IsDiscCrosscut α) (hβ : IsDiscCrosscut β)
    (hord : Disjoint (crossRange β) (crossSide α (-1))) {z : ℂ} (hz₁ : z ∈ crossSide α 1)
    (hz₂ : z ∈ crossSide β (-1)) (hzβ : z ∉ crossRange β) :
    ∃ a b, IsContactGap α β a b ∧
      connectedComponentIn (ball 0 1 \ (crossRange α ∪ crossRange β)) z = jordanIn (pocketCurve α β a b) := by
  set O := ball (0 : ℂ) 1 \ (crossRange α ∪ crossRange β) with hO
  have hOo : IsOpen O := isOpen_ball.sdiff (hα.isCompact_crossRange.union hβ.isCompact_crossRange).isClosed
  have hzα : z ∉ crossRange α := (hα.crossSide_subset (Or.inl rfl) hz₁).2
  have hzO : z ∈ O := ⟨(hα.crossSide_subset (Or.inl rfl) hz₁).1, fun h => h.elim hzα hzβ⟩
  set C := connectedComponentIn O z with hC
  have hCO : C ⊆ O := connectedComponentIn_subset O z
  have hCo : IsOpen C := hOo.connectedComponentIn
  have hCc : IsPreconnected C := isPreconnected_connectedComponentIn
  have hzC : z ∈ C := mem_connectedComponentIn hzO
  have hC₁ : C ⊆ crossSide α 1 := hα.subset_crossSide_of_isPreconnected (Or.inl rfl) hCc
    (fun w hw => ⟨(hCO hw).1, fun h => (hCO hw).2 (Or.inl h)⟩) ⟨z, hzC, hz₁⟩
  have hC₂ : C ⊆ crossSide β (-1) := hβ.subset_crossSide_of_isPreconnected (Or.inr rfl) hCc
    (fun w hw => ⟨(hCO hw).1, fun h => (hCO hw).2 (Or.inr h)⟩) ⟨z, hzC, hz₂⟩
  -- (C1) a boundary point of `C` on `α`, off `β`
  have hC1 : ∃ p ∈ closure C, p ∈ crossRange α ∧ p ∉ crossRange β := by
    by_contra hnot
    push Not at hnot
    have hsub : crossSide β (-1) ⊆ C := by
      refine (hβ.isPreconnected_crossSide (Or.inr rfl)).subset_of_closure_inter_subset hCo
        ⟨z, hz₂, hzC⟩ ?_
      rintro w ⟨hwcl, hwS⟩
      have hw' := hβ.crossSide_subset (Or.inr rfl) hwS
      by_cases hwα : w ∈ crossRange α
      · exact absurd (hnot w hwcl hwα) hw'.2
      · exact mem_connectedComponentIn_of_mem_closure hOo ⟨hw'.1, fun h => h.elim hwα hw'.2⟩ hwcl
    obtain ⟨v, hv₁, hv₂⟩ := hα.crossSide_inter_nonempty hβ (Or.inr rfl)
    exact Set.disjoint_left.1 hα.disjoint_crossSide (hC₁ (hsub hv₂)) hv₁
  obtain ⟨p, hpcl, ⟨s₀, hs₀, rfl⟩, hpβ⟩ := hC1
  have hs₀S : s₀ ∉ Sec7.pocketContactSet α β := fun h => hpβ (by
    obtain ⟨-, r, hr, hrs⟩ := h
    exact ⟨r, hr, hrs⟩)
  have hS := isClosed_pocketContactSet hα hβ
  -- (C2) the gap around `s₀`
  set A := Sec7.pocketContactSet α β ∩ Icc 0 s₀
  set B := Sec7.pocketContactSet α β ∩ Icc s₀ 1
  have hA0 : (0 : ℝ) ∈ A := ⟨zero_mem_pocketContactSet hα hβ, le_rfl, hs₀.1⟩
  have hB1 : (1 : ℝ) ∈ B := ⟨one_mem_pocketContactSet hα hβ, hs₀.2, le_rfl⟩
  have hAbdd : BddAbove A := ⟨s₀, fun s hs => hs.2.2⟩
  have hBbdd : BddBelow B := ⟨s₀, fun s hs => hs.2.1⟩
  set a := sSup A
  set b := sInf B
  have haA : a ∈ A := (hS.inter isClosed_Icc).csSup_mem ⟨0, hA0⟩ hAbdd
  have hbB : b ∈ B := (hS.inter isClosed_Icc).csInf_mem ⟨1, hB1⟩ hBbdd
  have has : a < s₀ := lt_of_le_of_ne haA.2.2 fun h => hs₀S (h ▸ haA.1)
  have hsb : s₀ < b := lt_of_le_of_ne hbB.2.1 fun h => hs₀S (h.symm ▸ hbB.1)
  have hgap : IsContactGap α β a b := by
    refine ⟨haA.1, hbB.1, has.trans hsb, fun s hs hsS => ?_⟩
    rcases le_total s s₀ with h | h
    · exact absurd (le_csSup hAbdd ⟨hsS, hsS.1.1, h⟩) (not_le.2 hs.1)
    · exact absurd (csInf_le hBbdd ⟨hsS, h, hsS.1.2⟩) (not_le.2 hs.2)
  obtain ⟨hJ, hUD, hUαβ, hUfr, w, hwU, hwc⟩ := pocket_props hα hβ hord hgap
  set U := jordanIn (pocketCurve α β a b)
  refine ⟨a, b, hgap, ?_⟩
  -- (C3) the pocket lies in the upper side of `α`
  obtain ⟨haS, hbS, hab, hgap'⟩ := hgap
  obtain ⟨hja, hjaβ⟩ := contactMap_mem hβ haS
  obtain ⟨hjb, hjbβ⟩ := contactMap_mem hβ hbS
  have hjab : contactMap α β a < contactMap α β b := strictMonoOn_contactMap hα hβ hord haS hbS hab
  set r₀ := (contactMap α β a + contactMap α β b) / 2 with hr₀def
  have hr₀ : r₀ ∈ Ioo (contactMap α β a) (contactMap α β b) :=
    ⟨by rw [hr₀def]; linarith, by rw [hr₀def]; linarith⟩
  have hr₀01 : r₀ ∈ Ioo (0 : ℝ) 1 := ⟨by linarith [hja.1, hr₀.1], by linarith [hjb.2, hr₀.2]⟩
  have hqα : β r₀ ∉ crossRange α := by
    rintro ⟨v, hv, hvq⟩
    have hvS : v ∈ Sec7.pocketContactSet α β := ⟨hv, r₀, Ioo_subset_Icc_self hr₀01, hvq.symm⟩
    have hjv : contactMap α β v = r₀ := contactMap_eq hβ (Ioo_subset_Icc_self hr₀01) hvq
    have hmono := strictMonoOn_contactMap hα hβ hord
    rcases lt_trichotomy v a with h | h | h
    · have := hmono hvS haS h; rw [hjv] at this; linarith [hr₀.1]
    · rw [h] at hjv; linarith [hr₀.1]
    rcases lt_trichotomy v b with h' | h' | h'
    · exact hgap' v ⟨h, h'⟩ hvS
    · rw [h'] at hjv; linarith [hr₀.2]
    · have := hmono hbS hvS h'; rw [hjv] at this; linarith [hr₀.2]
  have hq1 : β r₀ ∈ crossSide α 1 :=
    hα.mem_crossSide_one_of (hβ.mem_disc r₀ hr₀01) hqα
      (fun h => Set.disjoint_left.1 hord ⟨r₀, Ioo_subset_Icc_self hr₀01, rfl⟩ h)
  have hqU : β r₀ ∈ closure U := by
    rw [closure_eq_self_union_frontier, hUfr]
    exact Or.inr (Or.inr ⟨r₀, Ioo_subset_Icc_self hr₀, rfl⟩)
  have hUO : U ⊆ O := fun v hv => ⟨hUD hv, Set.disjoint_left.1 hUαβ hv⟩
  have hU₁ : U ⊆ crossSide α 1 := by
    refine hα.subset_crossSide_of_isPreconnected (Or.inl rfl) (isPreconnected_jordanIn hJ)
      (fun v hv => ⟨(hUO hv).1, fun h => (hUO hv).2 (Or.inl h)⟩) ?_
    obtain ⟨v, hv, hvU⟩ := mem_closure_iff.1 hqU _ (hα.isOpen_crossSide (Or.inl rfl)) hq1
    exact ⟨v, hvU, hv⟩
  -- local connectivity of the upper side of `α` at `p`
  have hpD : α s₀ ∈ ball (0 : ℂ) 1 :=
    hα.mem_disc s₀ ⟨lt_of_le_of_lt haA.2.1 has, lt_of_lt_of_le hsb hbB.2.2⟩
  obtain ⟨ε₁, hε₁, hε₁β⟩ :=
    Metric.isOpen_iff.1 hβ.isCompact_crossRange.isClosed.isOpen_compl (α s₀) hpβ
  obtain ⟨ε₂, hε₂, hε₂D⟩ := Metric.isOpen_iff.1 isOpen_ball (α s₀) hpD
  obtain ⟨N, hN, hNε, hNc⟩ := exists_mem_nhds_isPreconnected_inter_jordanIn hα.isJordanCurve_upper (α s₀)
    (lt_min hε₁ hε₂)
  have hNO : N ∩ crossSide α 1 ⊆ O := by
    rintro v ⟨hvN, hv1⟩
    have hvb := hNε hvN
    exact ⟨(hα.crossSide_subset (Or.inl rfl) hv1).1, fun h => h.elim
      (hα.crossSide_subset (Or.inl rfl) hv1).2 fun h' => hε₁β (ball_subset_ball (min_le_left _ _) hvb) h'⟩
  have hCN : (C ∩ (N ∩ crossSide α 1)).Nonempty := by
    obtain ⟨v, hvN, hvC⟩ := mem_closure_iff_nhds.1 hpcl N hN
    exact ⟨v, hvC, hvN, hC₁ hvC⟩
  have hUN : (U ∩ (N ∩ crossSide α 1)).Nonempty := by
    have hpU : α s₀ ∈ closure U := by
      rw [closure_eq_self_union_frontier, hUfr]
      exact Or.inr (Or.inl ⟨s₀, ⟨has.le, hsb.le⟩, rfl⟩)
    obtain ⟨v, hvN, hvU⟩ := mem_closure_iff_nhds.1 hpU N hN
    exact ⟨v, hvU, hvN, hU₁ hvU⟩
  obtain ⟨c, hcC, hcV⟩ := hCN
  obtain ⟨u, huU, huV⟩ := hUN
  have hVC : N ∩ crossSide α 1 ⊆ C := by
    rw [hC, connectedComponentIn_eq hcC]
    exact hNc.subset_connectedComponentIn hcV hNO
  have huw : u ∈ connectedComponentIn O w := by rw [hwc]; exact huU
  have hVU : N ∩ crossSide α 1 ⊆ connectedComponentIn O w := by
    rw [connectedComponentIn_eq huw]
    exact hNc.subset_connectedComponentIn huV hNO
  calc C = connectedComponentIn O w := connectedComponentIn_eq_of_mem_of_mem (hVC hcV) (hVU hcV)
    _ = U := hwc


/-- A point of the open disc off a crosscut and off its upper side is on its lower side. -/
theorem IsDiscCrosscut.mem_crossSide_neg_of {γ : ℝ → ℂ} (hγ : IsDiscCrosscut γ) {w : ℂ}
    (hw : w ∈ ball (0 : ℂ) 1) (hwγ : w ∉ crossRange γ) (hw' : w ∉ crossSide γ 1) : w ∈ crossSide γ (-1) := by
  rcases hγ.subset_crossSide_union ⟨hw, hwγ⟩ with h | h
  · exact absurd h hw'
  · exact h

/-- **A pocket lies between the two crosscuts**: in the upper side of `α` and in the lower side of `β`. -/
theorem pocket_subset_between (hα : IsDiscCrosscut α) (hβ : IsDiscCrosscut β)
    (hord : Disjoint (crossRange β) (crossSide α (-1))) {a b : ℝ} (hg : IsContactGap α β a b) :
    jordanIn (pocketCurve α β a b) ⊆ crossSide α 1 ∩ crossSide β (-1) := by
  obtain ⟨hJ, hUD, hUαβ, hUfr, -⟩ := pocket_props hα hβ hord hg
  obtain ⟨haS, hbS, hab, hgap⟩ := hg
  set U := jordanIn (pocketCurve α β a b)
  have hUc := isPreconnected_jordanIn hJ
  have hcl : ∀ q ∈ pocketCurve α β a b, q ∈ closure U := fun q hq => by
    rw [closure_eq_self_union_frontier, hUfr]; exact Or.inr hq
  have hmeet : ∀ {V : Set ℂ}, IsOpen V → ∀ q ∈ V, q ∈ pocketCurve α β a b → (U ∩ V).Nonempty :=
    fun hV q hqV hq => by
      obtain ⟨v, hv, hvU⟩ := mem_closure_iff.1 (hcl q hq) _ hV hqV
      exact ⟨v, hvU, hv⟩
  have hUsub : ∀ v ∈ U, v ∈ ball (0 : ℂ) 1 ∧ v ∉ crossRange α ∧ v ∉ crossRange β := fun v hv =>
    ⟨hUD hv, fun h => Set.disjoint_left.1 hUαβ hv (Or.inl h), fun h => Set.disjoint_left.1 hUαβ hv (Or.inr h)⟩
  have hmono := strictMonoOn_contactMap hα hβ hord
  refine subset_inter ?_ ?_
  · -- a point of `β` inside the gap lies in the upper side of `α`
    obtain ⟨hja, -⟩ := contactMap_mem hβ haS
    obtain ⟨hjb, -⟩ := contactMap_mem hβ hbS
    have hjab := hmono haS hbS hab
    set r₀ := (contactMap α β a + contactMap α β b) / 2 with hr₀def
    have hr₀ : r₀ ∈ Ioo (contactMap α β a) (contactMap α β b) :=
      ⟨by rw [hr₀def]; linarith, by rw [hr₀def]; linarith⟩
    have hr₀01 : r₀ ∈ Ioo (0 : ℝ) 1 := ⟨by linarith [hja.1, hr₀.1], by linarith [hjb.2, hr₀.2]⟩
    have hqα : β r₀ ∉ crossRange α := by
      rintro ⟨v, hv, hvq⟩
      have hvS : v ∈ Sec7.pocketContactSet α β := ⟨hv, r₀, Ioo_subset_Icc_self hr₀01, hvq.symm⟩
      have hjv : contactMap α β v = r₀ := contactMap_eq hβ (Ioo_subset_Icc_self hr₀01) hvq
      rcases lt_trichotomy v a with h | h | h
      · have := hmono hvS haS h; rw [hjv] at this; linarith [hr₀.1]
      · rw [h] at hjv; linarith [hr₀.1]
      rcases lt_trichotomy v b with h' | h' | h'
      · exact hgap v ⟨h, h'⟩ hvS
      · rw [h'] at hjv; linarith [hr₀.2]
      · have := hmono hbS hvS h'; rw [hjv] at this; linarith [hr₀.2]
    have hq1 : β r₀ ∈ crossSide α 1 :=
      hα.mem_crossSide_one_of (hβ.mem_disc r₀ hr₀01) hqα
        (fun h => Set.disjoint_left.1 hord ⟨r₀, Ioo_subset_Icc_self hr₀01, rfl⟩ h)
    exact hα.subset_crossSide_of_isPreconnected (Or.inl rfl) hUc
      (fun v hv => ⟨(hUsub v hv).1, (hUsub v hv).2.1⟩)
      (hmeet (hα.isOpen_crossSide (Or.inl rfl)) _ hq1 (Or.inr ⟨r₀, Ioo_subset_Icc_self hr₀, rfl⟩))
  · -- a point of `α` inside the gap lies in the lower side of `β`
    set s₁ := (a + b) / 2 with hs₁def
    have hs₁ : s₁ ∈ Ioo a b := ⟨by rw [hs₁def]; linarith, by rw [hs₁def]; linarith⟩
    have hs₁01 : s₁ ∈ Ioo (0 : ℝ) 1 := ⟨by linarith [haS.1.1, hs₁.1], by linarith [hbS.1.2, hs₁.2]⟩
    have hqβ : α s₁ ∉ crossRange β := fun h => by
      obtain ⟨r, hr, hrs⟩ := h
      exact hgap s₁ hs₁ ⟨Ioo_subset_Icc_self hs₁01, r, hr, hrs⟩
    have hq2 : α s₁ ∈ crossSide β (-1) :=
      hβ.mem_crossSide_neg_of (hα.mem_disc s₁ hs₁01) hqβ
        (fun h => Set.disjoint_left.1 (hα.disjoint_crossRange_crossSide_swap hβ hord)
          ⟨s₁, Ioo_subset_Icc_self hs₁01, rfl⟩ h)
    exact hβ.subset_crossSide_of_isPreconnected (Or.inr rfl) hUc
      (fun v hv => ⟨(hUsub v hv).1, (hUsub v hv).2.2⟩)
      (hmeet (hβ.isOpen_crossSide (Or.inr rfl)) _ hq2 (Or.inl ⟨s₁, Ioo_subset_Icc_self hs₁, rfl⟩))

end InteractingSLE.WangWu
