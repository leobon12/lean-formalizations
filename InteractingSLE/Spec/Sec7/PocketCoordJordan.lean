/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.PocketCoord

/-!
# Aux. lemma 130's change pocket without global order: the gap endpoints and the pocket as random objects

Packet PROVE-STRIPSYS8. Specification §7.4.1, proof of Aux. lemma 130 (`source/spec/p385-432.md` L455–L470, p. 412):
"Parametrize the two completed simple paths on `[0, 1]` to apply Aux. lemma 33. Their common-contact order is
increasing, by their reverse containment in the same counterflow. The gap in the second path's contact set containing
its change point has `y₀` as its upper endpoint. Its lower endpoint `x₀` and the corresponding gap of the first path
give exactly the Jordan pocket asserted there. […] This argument does not require the two complete paths to be
globally ordered after `y₀`. […] For instance, the endpoints are the infimum and supremum of their closed
contact-parameter sets, obtainable from rational interval tests."

`PocketCoord.lean` treats globally ordered walls (`IsChangeConfig`). After their angle changes the two incoming paths
of (RS13.1) may cross, so this file assumes only the increasing contact order (`IsChangeConfigInc`), as the source
does, and selects the pocket through its gap:

* `gapLo`, `gapHi`: the supremum of the contact parameters of `β` in `[0, c]` and their infimum in `[c, 1]`;
  `isContactGap_gapLo_gapHi`: they are the ends of the gap containing `c`;
* `changeGap`: the pocket of that gap, `jordanIn (α[u, v] ∪ β[gapLo, gapHi])`, with `u, v` the parameters of `α`;
* `IsChangeConfigInc.changePocket`: the pocket in `ℍ`, a component of `ℍ \ (R ∪ L)` whose closure contains `L r`,
  with Cayley image `changeGap`.
-/

set_option autoImplicit false

noncomputable section

open Set Metric Filter Topology Complex Bornology Function
open QuantumZipper (H Hbar)
open QuantumZipper.CA (cayley cayleyInv)
open scoped NNReal

namespace InteractingSLE.Sec7.PocketCoord

open WangWu

/-! ### The ends of the gap containing a parameter -/

section Gap

variable {α β : ℝ → ℂ}

/-- The supremum of the contact parameters of `β` (with `α`) in `[0, c]`. -/
def gapLo (β α : ℝ → ℂ) (c : ℝ) : ℝ := sSup (Sec7.pocketContactSet β α ∩ Icc 0 c)

/-- The infimum of the contact parameters of `β` (with `α`) in `[c, 1]`. -/
def gapHi (β α : ℝ → ℂ) (c : ℝ) : ℝ := sInf (Sec7.pocketContactSet β α ∩ Icc c 1)

/-- **The ends of the gap containing `c` are the supremum and infimum of the contact parameters on either side.** -/
theorem gapLo_gapHi_eq {c : ℝ}
    (hcα : β c ∉ crossRange α) {a b : ℝ} (hg : IsContactGap β α a b) (hcab : c ∈ Ioo a b) :
    gapLo β α c = a ∧ gapHi β α c = b := by
  obtain ⟨ha, hb, -, hgap⟩ := hg
  have hcS : c ∉ Sec7.pocketContactSet β α := fun h => hcα h.2
  constructor
  · refine IsGreatest.csSup_eq ⟨⟨ha, ha.1.1, hcab.1.le⟩, fun s hs => ?_⟩
    by_contra h
    push Not at h
    rcases eq_or_lt_of_le hs.2.2 with rfl | hsc
    · exact hcS hs.1
    · exact hgap s ⟨h, hsc.trans hcab.2⟩ hs.1
  · refine IsLeast.csInf_eq ⟨⟨hb, hcab.2.le, hb.1.2⟩, fun s hs => ?_⟩
    by_contra h
    push Not at h
    rcases eq_or_lt_of_le hs.2.1 with rfl | hcs
    · exact hcS hs.1
    · exact hgap s ⟨hcab.1.trans hcs, h⟩ hs.1

/-- The gap of the contacts of `β` containing a non-contact parameter `c` is `(gapLo, gapHi)`. -/
theorem isContactGap_gapLo_gapHi (hα : IsDiscCrosscut α) (hβ : IsDiscCrosscut β) {c : ℝ}
    (hc : c ∈ Icc (0 : ℝ) 1) (hcα : β c ∉ crossRange α) :
    IsContactGap β α (gapLo β α c) (gapHi β α c) ∧ c ∈ Ioo (gapLo β α c) (gapHi β α c) := by
  have hcS : c ∉ Sec7.pocketContactSet β α := fun h => hcα h.2
  obtain ⟨a, b, hg, hcab⟩ := Aux130.exists_isContactGap_of_notMem hβ hα hc hcS
  obtain ⟨h1, h2⟩ := gapLo_gapHi_eq hcα hg hcab
  rw [h1, h2]
  exact ⟨hg, hcab⟩

/-- The pocket of the gap of `β` containing `c`, read through the parameters `u, v` of `α`. -/
def changeGap (α β : ℝ → ℂ) (c : ℝ) : Set ℂ :=
  jordanIn (α '' Icc (contactMap β α (gapLo β α c)) (contactMap β α (gapHi β α c)) ∪
    β '' Icc (gapLo β α c) (gapHi β α c))

/-- **The change gap is the pocket of an `α`-gap** whose `β`-parameters are `gapLo`, `gapHi`. -/
theorem changeGap_eq (hα : IsDiscCrosscut α) (hβ : IsDiscCrosscut β)
    (hjm : StrictMonoOn (contactMap α β) (Sec7.pocketContactSet α β)) {c : ℝ} (hc : c ∈ Icc (0 : ℝ) 1)
    (hcα : β c ∉ crossRange α) :
    IsContactGap α β (contactMap β α (gapLo β α c)) (contactMap β α (gapHi β α c)) ∧
      contactMap α β (contactMap β α (gapLo β α c)) = gapLo β α c ∧
      contactMap α β (contactMap β α (gapHi β α c)) = gapHi β α c ∧
      changeGap α β c = jordanIn (pocketCurve α β (contactMap β α (gapLo β α c)) (contactMap β α (gapHi β α c))) := by
  obtain ⟨hg, -⟩ := isContactGap_gapLo_gapHi hα hβ hc hcα
  obtain ⟨hg', h1, h2⟩ := isContactGap_swap hα hβ hjm hg
  refine ⟨hg', h1, h2, ?_⟩
  rw [changeGap, pocketCurve, h1, h2]

end Gap

/-! ### Countable tests -/

section Tests

/-- The clamp `max s (min t x)` of `x` to `[s, t]`. -/
def clamp (s t x : ℝ) : ℝ := max s (min t x)

theorem continuous_clamp (s t : ℝ) : Continuous (clamp s t) :=
  continuous_const.max (continuous_const.min continuous_id)

theorem clamp_mem {s t : ℝ} (hst : s ≤ t) (x : ℝ) : clamp s t x ∈ Icc s t :=
  ⟨le_max_left _ _, max_le hst (min_le_left _ _)⟩

theorem clamp_of_mem {s t x : ℝ} (hx : x ∈ Icc s t) : clamp s t x = x := by
  rw [clamp, min_eq_right hx.2, max_eq_right hx.1]

/-- Clamped rationals are dense in `[s, t]`. -/
theorem mem_closure_clamp_rat {s t x : ℝ} (hx : x ∈ Icc s t) :
    x ∈ closure (range fun q : ℚ => clamp s t q) := by
  have hd : x ∈ closure (range ((↑) : ℚ → ℝ)) := by
    rw [(Rat.denseRange_cast : DenseRange ((↑) : ℚ → ℝ)).closure_eq]
    exact mem_univ x
  have h := mem_closure_image (continuous_clamp s t).continuousAt hd
  rw [clamp_of_mem hx, ← range_comp] at h
  exact h

/-- **A minimum test through a dense subset**: a continuous function on a nonempty compact set takes a value `≤ a`
iff it takes values `< a + 1/(n+1)` on a dense subset, for every `n`. -/
theorem exists_le_iff_dense {X : Type*} [TopologicalSpace X] {K D : Set X} (hK : IsCompact K) (hKne : K.Nonempty)
    {F : X → ℝ} (hF : ContinuousOn F K) (hDK : D ⊆ K) (hKD : K ⊆ closure D) (a : ℝ) :
    (∃ x ∈ K, F x ≤ a) ↔ ∀ n : ℕ, ∃ y ∈ D, F y < a + 1 / ((n : ℝ) + 1) := by
  constructor
  · rintro ⟨x, hxK, hxa⟩ n
    have hε : (0 : ℝ) < 1 / ((n : ℝ) + 1) := Nat.one_div_pos_of_nat
    have hU : {y | F y < a + 1 / ((n : ℝ) + 1)} ∈ 𝓝[K] x :=
      (hF x hxK).eventually (gt_mem_nhds (by linarith))
    obtain ⟨V, hVo, hxV, hVK⟩ := mem_nhdsWithin.1 hU
    obtain ⟨y, hyV, hyD⟩ := mem_closure_iff.1 (hKD hxK) V hVo hxV
    exact ⟨y, hyD, hVK ⟨hyV, hDK hyD⟩⟩
  · intro h
    obtain ⟨x, hxK, hmin⟩ := hK.exists_isMinOn hKne hF
    refine ⟨x, hxK, le_of_forall_pos_lt_add fun ε hε => ?_⟩
    obtain ⟨n, hn⟩ := exists_nat_one_div_lt hε
    obtain ⟨y, hyD, hy⟩ := h n
    exact (hmin (hDK hyD)).trans_lt (hy.trans (by linarith))

/-- **The inside of a Jordan curve in the closed unit disc** is the set of points off the curve not joined to `2` in
its complement. -/
theorem mem_jordanIn_iff {J : Set ℂ} (hJ : LQGMetric.JordanMap.IsJordanCurve J) (hJb : J ⊆ closedBall 0 1)
    (w : ℂ) : w ∈ jordanIn J ↔ w ∉ J ∧ w ∉ connectedComponentIn Jᶜ 2 := by
  -- the ray `[2, ∞)` lies outside
  set S : Set ℂ := (fun t : ℝ => (t : ℂ)) '' Ici 2
  have hSpc : IsPreconnected S := isPreconnected_Ici.image _ continuous_ofReal.continuousOn
  have hSJ : Disjoint S J := by
    refine Set.disjoint_left.2 ?_
    rintro _ ⟨t, ht, rfl⟩ hJt
    have := hJb hJt
    rw [mem_closedBall, dist_zero_right, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by
      linarith [mem_Ici.1 ht])] at this
    linarith [mem_Ici.1 ht]
  have hSu : ¬ IsBounded S := by
    intro hb
    obtain ⟨M, hM⟩ := hb.exists_norm_le
    have := hM _ ⟨max 2 (M + 1), mem_Ici.2 (le_max_left _ _), rfl⟩
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by linarith [le_max_left 2 (M + 1)])] at this
    linarith [le_max_right 2 (M + 1)]
  have h2S : (2 : ℂ) ∈ S := ⟨2, mem_Ici.2 le_rfl, by norm_num⟩
  have h2out : (2 : ℂ) ∈ jordanOut J := subset_jordanOut_of_isPreconnected hSpc hSu hSJ h2S
  obtain ⟨-, -, -, -, -, hOpc, -⟩ := JordanSides hJ
  constructor
  · intro hw
    refine ⟨hw.1, fun hw2 => ?_⟩
    -- `w` and `2` have the same component, which contains the unbounded ray
    have hb := hw.2
    rw [← connectedComponentIn_eq hw2] at hb
    exact hSu (hb.subset (hSpc.subset_connectedComponentIn h2S fun z hz => Set.disjoint_left.1 hSJ hz))
  · rintro ⟨hwJ, hw2⟩
    have hwc : w ∈ jordanIn J ∪ jordanOut J := by
      rw [← compl_eq_jordanIn_union_jordanOut J]
      exact hwJ
    rcases hwc with h | h
    · exact h
    · refine absurd ?_ hw2
      exact (isPreconnected_jordanOut hJ).subset_connectedComponentIn h2out (jordanOut_subset_compl J) h

end Tests

/-! ### The change pocket under increasing contact order -/

section HalfPlane

open Lemma71I

/-- **Aux. lemma 130's configuration under increasing contact order** (p. 412): the right wall `R` (first path) and the
left wall `L` (second path) are simple proper curves of `ℍ` from `0` to `∞` whose common contacts occur in the same
order ("Their common-contact order is increasing, by their reverse containment in the same counterflow"), the change
time `r` is positive and the change point `L r` is off `R`. No global order of the walls is assumed. -/
structure IsChangeConfigInc (R L : ℝ≥0 → ℂ) (r : ℝ≥0) : Prop where
  right : IsSimpleProper R
  left : IsSimpleProper L
  inc : StrictMonoOn (contactMap (toDisc (realPath R)) (toDisc (realPath L)))
    (Sec7.pocketContactSet (toDisc (realPath R)) (toDisc (realPath L)))
  pos : 0 < r
  off : L r ∉ range R

variable {R L : ℝ≥0 → ℂ} {r : ℝ≥0}

/-- Global order gives increasing contact order. -/
theorem IsChangeConfig.isChangeConfigInc (h : IsChangeConfig R L r) : IsChangeConfigInc R L r :=
  ⟨h.right, h.left, h.strictMono, h.pos, h.off⟩

/-- **The change pocket** in `ℍ`: the inverse Cayley image of the pocket of the gap containing the change parameter. -/
def changePocket (R L : ℝ≥0 → ℂ) (r : ℝ≥0) : Set ℂ :=
  cayleyInv '' changeGap (toDisc (realPath R)) (toDisc (realPath L)) (discTime r)

namespace IsChangeConfigInc

theorem isDiscCrosscut_right (h : IsChangeConfigInc R L r) : IsDiscCrosscut (toDisc (realPath R)) :=
  h.right.isProperArc.isDiscCrosscut_toDisc

theorem isDiscCrosscut_left (h : IsChangeConfigInc R L r) : IsDiscCrosscut (toDisc (realPath L)) :=
  h.left.isProperArc.isDiscCrosscut_toDisc

theorem mem_Hbar (h : IsChangeConfigInc R L r) : L r ∈ Hbar :=
  le_of_lt (show (0 : ℝ) < (L r).im from h.left.2.2.2.1 r h.pos)

theorem notMem_crossRange (h : IsChangeConfigInc R L r) :
    toDisc (realPath L) (discTime r) ∉ crossRange (toDisc (realPath R)) := by
  rw [toDisc_realPath_discTime, h.right.isProperArc.cayley_mem_crossRange_iff h.mem_Hbar, arcRange_realPath]
  exact h.off

/-- The change gap is the pocket of an `α`-gap (`changeGap_eq` for the walls). -/
theorem changeGap_eq (h : IsChangeConfigInc R L r) :
    IsContactGap (toDisc (realPath R)) (toDisc (realPath L))
        (contactMap (toDisc (realPath L)) (toDisc (realPath R)) (gapLo (toDisc (realPath L)) (toDisc (realPath R))
          (discTime r)))
        (contactMap (toDisc (realPath L)) (toDisc (realPath R)) (gapHi (toDisc (realPath L)) (toDisc (realPath R))
          (discTime r))) ∧
      changeGap (toDisc (realPath R)) (toDisc (realPath L)) (discTime r) =
        jordanIn (pocketCurve (toDisc (realPath R)) (toDisc (realPath L))
          (contactMap (toDisc (realPath L)) (toDisc (realPath R)) (gapLo (toDisc (realPath L)) (toDisc (realPath R))
            (discTime r)))
          (contactMap (toDisc (realPath L)) (toDisc (realPath R)) (gapHi (toDisc (realPath L)) (toDisc (realPath R))
            (discTime r)))) := by
  obtain ⟨hg, -, -, heq⟩ := PocketCoord.changeGap_eq h.isDiscCrosscut_right h.isDiscCrosscut_left h.inc
    (discTime_mem_Icc r) h.notMem_crossRange
  exact ⟨hg, heq⟩

/-- **The change pocket is a component of `ℍ \ (R ∪ L)`** (Aux. lemma 33's last clause, transported), and its
Cayley image is the change gap. -/
theorem changePocket_eq (h : IsChangeConfigInc R L r) :
    ∃ z ∈ H \ (range R ∪ range L), changePocket R L r = connectedComponentIn (H \ (range R ∪ range L)) z ∧
      cayley '' changePocket R L r = changeGap (toDisc (realPath R)) (toDisc (realPath L)) (discTime r) := by
  obtain ⟨hg, heq⟩ := h.changeGap_eq
  obtain ⟨-, hPball, hPdisj, -, w, hwP, hPcc⟩ :=
    pocket_props_of_strictMono h.isDiscCrosscut_right h.isDiscCrosscut_left h.inc hg
  rw [← heq] at hPball hPdisj hwP hPcc
  set P := changeGap (toDisc (realPath R)) (toDisc (realPath L)) (discTime r)
  have hwball := hPball hwP
  set z := cayleyInv w
  have hzH : z ∈ H := QuantumZipper.CA.cayleyInv_mem_H hwball
  have hzHbar : z ∈ Hbar := le_of_lt (show (0 : ℝ) < z.im from hzH)
  have hcz : cayley z = w := cayley_cayleyInv_of_mem_ball hwball
  have hzR : z ∉ range R := by
    rw [← arcRange_realPath, ← h.right.isProperArc.cayley_mem_crossRange_iff hzHbar, hcz]
    exact fun h' => Set.disjoint_left.1 hPdisj hwP (Or.inl h')
  have hzL : z ∉ range L := by
    rw [← arcRange_realPath, ← h.left.isProperArc.cayley_mem_crossRange_iff hzHbar, hcz]
    exact fun h' => Set.disjoint_left.1 hPdisj hwP (Or.inr h')
  have hzU : z ∈ H \ (range R ∪ range L) := ⟨hzH, fun h' => h'.elim hzR hzL⟩
  have hCeq : cayley '' connectedComponentIn (H \ (range R ∪ range L)) z = P := by
    have himg := image_cayley_H_diff h.right.isProperArc h.left.isProperArc
    rw [arcRange_realPath, arcRange_realPath] at himg
    rw [image_cayley_connectedComponentIn sdiff_subset hzU, himg, hcz, hPcc]
  have hinv : changePocket R L r = connectedComponentIn (H \ (range R ∪ range L)) z := by
    show cayleyInv '' P = _
    rw [← hCeq, image_image, image_congr (fun y hy => cayleyInv_cayley_of_mem_Hbar
      (le_of_lt (show (0 : ℝ) < y.im from (connectedComponentIn_subset _ _ hy : y ∈ H \ _).1))), image_id']
  exact ⟨z, hzU, hinv, by rw [hinv, hCeq]⟩

theorem changePocket_subset (h : IsChangeConfigInc R L r) : changePocket R L r ⊆ H \ (range R ∪ range L) := by
  obtain ⟨z, -, hz, -⟩ := h.changePocket_eq
  rw [hz]
  exact connectedComponentIn_subset _ _

/-- The change pocket is open, connected and simply connected. -/
theorem isOpen_isConnected_isSimplyConnected (h : IsChangeConfigInc R L r) :
    IsOpen (changePocket R L r) ∧ IsConnected (changePocket R L r) ∧ IsSimplyConnected (changePocket R L r) := by
  obtain ⟨z, hzU, hz, -⟩ := h.changePocket_eq
  rw [hz]
  exact ⟨(QuantumZipper.isOpen_H.sdiff ((Lemma71Pin.IsSimpleProper.isClosed_range h.right).union
      (Lemma71Pin.IsSimpleProper.isClosed_range h.left))).connectedComponentIn,
    isConnected_connectedComponentIn_iff.2 hzU,
    Lemma71Pin.isSimplyConnected_connectedComponentIn_range h.right h.left hzU⟩

/-- **The change point is on the frontier of the change pocket** (in its closure). -/
theorem mem_closure_changePocket (h : IsChangeConfigInc R L r) : L r ∈ closure (changePocket R L r) := by
  obtain ⟨hg, heq⟩ := h.changeGap_eq
  obtain ⟨z, -, hz, hCeq⟩ := h.changePocket_eq
  obtain ⟨hgap, hcIoo⟩ := isContactGap_gapLo_gapHi h.isDiscCrosscut_right h.isDiscCrosscut_left
    (discTime_mem_Icc r) h.notMem_crossRange
  obtain ⟨-, h1, h2⟩ := isContactGap_swap h.isDiscCrosscut_right h.isDiscCrosscut_left h.inc hgap
  have hfr := image_subset_frontier_pocket h.isDiscCrosscut_right h.isDiscCrosscut_left h.inc hg
  rw [h1, h2, ← heq] at hfr
  have hβc : cayley (L r) ∈ closure (cayley '' changePocket R L r) := by
    rw [hCeq, ← toDisc_realPath_discTime]
    exact frontier_subset_closure (hfr ⟨_, ⟨hcIoo.1.le, hcIoo.2.le⟩, rfl⟩)
  have := mem_closure_image (continuousAt_cayleyInv (cayley_ne_one_of_Hbar h.mem_Hbar)) hβc
  rwa [cayleyInv_cayley_of_mem_Hbar h.mem_Hbar, image_image,
    image_congr (fun y hy => cayleyInv_cayley_of_mem_Hbar
      (le_of_lt (show (0 : ℝ) < y.im from (h.changePocket_subset hy).1))), image_id'] at this

/-- Under global order the change pocket is the unique component between the walls with the change point in its
closure (`PocketCoord.IsChangeConfig.existsUnique_changePocket`). -/
theorem _root_.InteractingSLE.Sec7.PocketCoord.IsChangeConfig.changePocket_eq_of (h : IsChangeConfig R L r)
    {C : Set ℂ} (hC : C ∈ betweenComponents (range R) (range L)) (hcl : L r ∈ closure C) :
    C = changePocket R L r := by
  obtain ⟨u, v, hg, hc, hCeq⟩ := h.changePocket_cayley hC hcl
  have hi := h.isChangeConfigInc
  obtain ⟨hg', heq⟩ := hi.changeGap_eq
  obtain ⟨-, -, -, hCeq'⟩ := hi.changePocket_eq
  obtain ⟨hgap, hcIoo⟩ := isContactGap_gapLo_gapHi hi.isDiscCrosscut_right hi.isDiscCrosscut_left
    (discTime_mem_Icc r) hi.notMem_crossRange
  obtain ⟨-, h1, h2⟩ := isContactGap_swap hi.isDiscCrosscut_right hi.isDiscCrosscut_left hi.inc hgap
  rw [← h1, ← h2] at hcIoo
  obtain ⟨rfl, rfl⟩ := isContactGap_eq_of_mem_Ioo h.strictMono hg hg' hc hcIoo
  have hinj : InjOn cayley H := fun z hz w hw hzw =>
    cayley_injOn_Hbar (le_of_lt (show (0 : ℝ) < z.im from hz)) (le_of_lt (show (0 : ℝ) < w.im from hw)) hzw
  refine (hinj.image_eq_image_iff (IsChangeConfig.subset_H_of_mem_betweenComponents hC)
    (fun y hy => (hi.changePocket_subset hy).1)).1 ?_
  rw [hCeq, hCeq', heq]

end IsChangeConfigInc

end HalfPlane

end InteractingSLE.Sec7.PocketCoord
