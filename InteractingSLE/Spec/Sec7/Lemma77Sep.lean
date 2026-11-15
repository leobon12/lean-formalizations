/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.Lemma77Barrier
import InteractingSLE.Foundations.Topology.JaniszewskiHalfPlane
import InteractingSLE.Foundations.Loewner.YuanCharacterisationArc
import InteractingSLE.Spec.Restart.ClockFlow

/-!
# Planar separation for Lemma 7.7

Packet PROVE-LEMMA77. Deterministic tools for the confinement and lens arguments of Lemma 7.7 (§7.2, pp. 278–282):

* `mem_H_diff_fillH_union_of_mem_jordanOut`: Janiszewski's theorem in the plane, returned to `ℍ`: a point of the
  unbounded domain of a compact `F` lying in the unbounded component of the complement of a compact `G` (which may
  leave `ℍ̄`) is in the unbounded domain of `F ∪ G`, provided `(F ∪ L_R) ∩ G` is preconnected (`L_R` a large lower
  half-disc).
* `mem_H_diff_fillH_union_of_slit`: adding a slit `S ⊆ ℍ` that meets `F` in a preconnected set (an arc attached at
  one point) traps no new point.
* `mem_H_diff_fillH_of_mem_jordanOut_closing`: if `A ⊆ ℍ̄` meets `ℝ` only inside `F ⊆ A`, and `F ∪ L` is
  preconnected for a closing set `L` in the closed lower half-plane, then a point of the unbounded domain of `F`
  lying outside `A ∪ L` is in the unbounded domain of `A`. This is "the unbounded component is on the right of `C`"
  (Aux. lemma 69, p. 274) in a form with no orientation.
* free/trapped helpers, and the tip property of good paths (`Restart.IsPathGood`) as freeness.
-/

set_option autoImplicit false

noncomputable section

open Set Metric Filter Topology Bornology Complex
open scoped NNReal ENNReal

open QuantumZipper (H)

namespace InteractingSLE

namespace Sec7

open HalfPlaneSep

/-! ### Janiszewski's theorem, returned to `ℍ` -/

/-- **Plane Janiszewski, returned to `ℍ`.** -/
theorem mem_H_diff_fillH_union_of_mem_jordanOut {F G : Set ℂ} (hF : IsCompact F) (hG : IsCompact G)
    {R : ℝ} (hR : 0 < R) (hFR : F ⊆ ball 0 R) (hGR : G ⊆ ball 0 R)
    (hFG : IsPreconnected ((F ∪ lowerDisc R) ∩ G)) {z : ℂ}
    (hz : z ∈ H \ fillH F) (hzG : z ∈ WangWu.jordanOut G) : z ∈ H \ fillH (F ∪ G) := by
  set b : ℂ := ((R + 1 : ℝ) : ℂ) * I with hb
  set L := lowerDisc R with hL
  have hbH : b ∈ H := by
    show 0 < b.im
    simp only [hb, mul_im, ofReal_re, I_im, mul_one, ofReal_im, I_re, mul_zero, add_zero]
    linarith
  have hbnorm : ‖b‖ = R + 1 := by
    rw [hb, norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (by linarith)]
  have hbG : ∀ {S : Set ℂ}, S ⊆ ball 0 R → b ∉ S := fun hSR h => by
    have := mem_ball_zero_iff.1 (hSR h); rw [hbnorm] at this; linarith
  have hFG' : IsCompact (F ∪ G) := hF.union hG
  have hFGR : F ∪ G ⊆ ball 0 R := union_subset hFR hGR
  have hEq : H \ fillH (F ∪ G) = connectedComponentIn (H \ (F ∪ G)) b := by
    have := H_diff_fillH hR (show closure (F ∪ G) ⊆ ball 0 R by rwa [hFG'.isClosed.closure_eq])
    rwa [hFG'.isClosed.closure_eq] at this
  -- `b` is joined to `z` off `F ∪ L`
  have h₁ : b ∈ connectedComponentIn (F ∪ L)ᶜ z := by
    have hEqF := H_diff_fillH hR (show closure F ⊆ ball 0 R by rwa [hF.isClosed.closure_eq])
    rw [hF.isClosed.closure_eq] at hEqF
    have hz' := hz
    rw [hEqF] at hz'
    have hbz : b ∈ connectedComponentIn (H \ F) z := by
      rw [← connectedComponentIn_eq hz']
      exact mem_connectedComponentIn ⟨hbH, hbG hFR⟩
    refine connectedComponentIn_mono z ?_ hbz
    rintro w ⟨hwH, hwF⟩ (h | h)
    · exact hwF h
    · exact notMem_lowerDisc_of_mem_H hwH h
  -- `b` is joined to `z` off `G`
  have h₂ : b ∈ connectedComponentIn Gᶜ z := by
    obtain ⟨w, hwC, hwR⟩ : ∃ w ∈ connectedComponentIn Gᶜ z, R < ‖w‖ := by
      by_contra hcon
      push Not at hcon
      exact hzG.2 ((isBounded_closedBall (x := (0 : ℂ)) (r := R)).subset fun w hw =>
        mem_closedBall_zero_iff.2 (hcon w hw))
    have hE : {w : ℂ | R < ‖w‖} ⊆ Gᶜ := fun w hw hwG => by
      have := mem_ball_zero_iff.1 (hGR hwG)
      exact absurd hw (not_lt.2 this.le)
    have hsub := (QuantumZipper.CA.Topo.isPreconnected_setOf_lt_norm R).subset_connectedComponentIn
      (show w ∈ {w : ℂ | R < ‖w‖} from hwR) hE
    rw [← connectedComponentIn_eq hwC] at hsub
    exact hsub (show R < ‖b‖ by rw [hbnorm]; linarith)
  have hzX : z ∉ (F ∪ L) ∪ G := by
    rintro ((h | h) | h)
    · exact (H_diff_fillH_subset_H_diff hF.isClosed hz).2 h
    · exact notMem_lowerDisc_of_mem_H hz.1 h
    · exact hzG.1 h
  have hbX : b ∉ (F ∪ L) ∪ G := by
    rintro ((h | h) | h)
    · exact hbG hFR h
    · exact notMem_lowerDisc_of_mem_H hbH h
    · exact hbG hGR h
  have hJ := QuantumZipper.CA.Topo.janiszewski (hF.union (isCompact_lowerDisc R)) hG hFG hzX hbX
    h₁ h₂
  -- back to `ℍ`
  set C := connectedComponentIn ((F ∪ L) ∪ G)ᶜ z with hCdef
  set P := connectedComponentIn (H \ (F ∪ G)) b with hPdef
  have hPo : IsOpen P := (QuantumZipper.isOpen_H.sdiff hFG'.isClosed).connectedComponentIn
  have hbP : b ∈ P := mem_connectedComponentIn ⟨hbH, fun h => (hbG hFGR) h⟩
  have hfar : ∀ w ∈ H, R ≤ ‖w‖ → w ∈ P := fun w hw hwR =>
    mem_connectedComponentIn_of_le_norm hR hFGR hw hwR
  have hclP : ∀ w ∈ H \ (F ∪ G), w ∈ closure P → w ∈ P := by
    intro w hw hwc
    obtain ⟨ε, hε, hεw⟩ := Metric.isOpen_iff.1 (QuantumZipper.isOpen_H.sdiff hFG'.isClosed) w hw
    obtain ⟨u, huP, hu⟩ := Metric.mem_closure_iff.1 hwc ε hε
    have hub : u ∈ ball w ε := by rw [mem_ball, dist_comm]; exact hu
    have hsub := (convex_ball w ε).isPreconnected.subset_connectedComponentIn hub hεw
    rw [← connectedComponentIn_eq huP] at hsub
    exact hsub (mem_ball_self hε)
  have hCsub : C ⊆ P ∪ {w | R < ‖w‖} ∪ ((closure P)ᶜ ∩ ball 0 R) := by
    intro w hwC
    have hw : w ∉ (F ∪ L) ∪ G := connectedComponentIn_subset _ _ hwC
    have hwF : w ∉ F ∪ G := fun h => h.elim (fun h => hw (Or.inl (Or.inl h))) fun h => hw (Or.inr h)
    have hwL : w ∉ L := fun h => hw (Or.inl (Or.inr h))
    by_cases hwR : R ≤ ‖w‖
    · by_cases hwH : w ∈ H
      · exact Or.inl (Or.inl (hfar w hwH hwR))
      · refine Or.inl (Or.inr (lt_of_le_of_ne hwR fun he => hwL ⟨?_, ?_⟩))
        · rw [mem_closedBall_zero_iff, ← he]
        · exact not_lt.1 (show ¬ (0 < w.im) from hwH)
    · have hwH : w ∈ H := by
        by_contra hwH
        exact hwL ⟨mem_closedBall_zero_iff.2 (not_le.1 hwR).le, not_lt.1 (show ¬ (0 < w.im) from hwH)⟩
      by_cases hwc : w ∈ closure P
      · exact Or.inl (Or.inl (hclP w ⟨hwH, hwF⟩ hwc))
      · exact Or.inr ⟨hwc, mem_ball_zero_iff.2 (not_le.1 hwR)⟩
  have hCP : C ⊆ P ∪ {w | R < ‖w‖} := by
    refine isPreconnected_connectedComponentIn.subset_left_of_subset_union
      (hPo.union (isOpen_lt continuous_const continuous_norm))
      (isClosed_closure.isOpen_compl.inter isOpen_ball) ?_ hCsub ⟨b, hJ, Or.inl hbP⟩
    refine Set.disjoint_left.2 fun w hw hw' => ?_
    rcases hw with hw | hw
    · exact hw'.1 (subset_closure hw)
    · exact absurd (mem_ball_zero_iff.1 hw'.2) (not_lt.2 (le_of_lt hw))
  rw [hEq]
  rcases hCP (mem_connectedComponentIn hzX) with h | h
  · exact h
  · exact hfar z hz.1 (le_of_lt h)

/-- **Adding a slit.** A compact `S ⊆ ℍ` with connected complement (an arc), meeting `F` in a preconnected set,
traps no point of the unbounded domain of `F` off `S`. -/
theorem mem_H_diff_fillH_union_of_slit {F S : Set ℂ} (hF : IsCompact F) (hS : IsCompact S)
    (hSc : IsPreconnected Sᶜ) (hSH : S ⊆ H) (hFS : IsPreconnected (F ∩ S)) {z : ℂ}
    (hz : z ∈ H \ fillH F) (hzS : z ∉ S) : z ∈ H \ fillH (F ∪ S) := by
  obtain ⟨R, hR, hFSR⟩ := (hF.union hS).isBounded.subset_ball_lt 0 0
  refine mem_H_diff_fillH_union_of_mem_jordanOut hF hS hR (subset_union_left.trans hFSR)
    (subset_union_right.trans hFSR) ?_ hz ⟨hzS, ?_⟩
  · have he : (F ∪ lowerDisc R) ∩ S = F ∩ S := by
      ext w
      constructor
      · rintro ⟨h | h, hw⟩
        · exact ⟨h, hw⟩
        · exact absurd h (notMem_lowerDisc_of_mem_H (hSH hw))
      · rintro ⟨h, hw⟩
        exact ⟨Or.inl h, hw⟩
    rwa [he]
  · rw [hSc.connectedComponentIn (show z ∈ Sᶜ from hzS)]
    intro hb
    exact NormedSpace.unbounded_univ ℝ ℂ (by rw [← union_compl_self S]; exact hS.isBounded.union hb)

/-- **The closing Jordan curve.** Let `F ⊆ A ⊆ ℍ̄` be compact with every real point of `A` in `F`, and let `L` be a
compact subset of the closed lower half-plane with `F ∪ L` preconnected. A point of the unbounded domain of `F`
that lies in the unbounded component of `(A ∪ L)ᶜ` is in the unbounded domain of `A`. -/
theorem mem_H_diff_fillH_of_mem_jordanOut_closing {F A L : Set ℂ} (hF : IsCompact F) (hA : IsCompact A)
    (hL : IsCompact L) (hFA : F ⊆ A) (hAim : ∀ w ∈ A, 0 ≤ w.im) (hAre : ∀ w ∈ A, w.im = 0 → w ∈ F)
    (hLim : ∀ w ∈ L, w.im ≤ 0) (hFL : IsPreconnected (F ∪ L)) {z : ℂ} (hz : z ∈ H \ fillH F)
    (hzJ : z ∈ WangWu.jordanOut (A ∪ L)) : z ∈ H \ fillH A := by
  obtain ⟨R, hR, hR'⟩ := (hA.union hL).isBounded.subset_ball_lt 0 0
  have hFR : F ⊆ ball 0 R := hFA.trans (subset_union_left.trans hR')
  have he : (F ∪ lowerDisc R) ∩ (A ∪ L) = F ∪ L := by
    ext w
    constructor
    · rintro ⟨hw | hw, hw' | hw'⟩
      · exact Or.inl hw
      · exact Or.inl hw
      · exact Or.inl (hAre w hw' (le_antisymm hw.2 (hAim w hw')))
      · exact Or.inr hw'
    · rintro (hw | hw)
      · exact ⟨Or.inl hw, Or.inl (hFA hw)⟩
      · exact ⟨Or.inr ⟨mem_closedBall_zero_iff.2 (mem_ball_zero_iff.1 (hR' (Or.inr hw))).le, hLim w hw⟩,
          Or.inr hw⟩
  have key := mem_H_diff_fillH_union_of_mem_jordanOut hF (hA.union hL) hR hFR hR' (by rw [he]; exact hFL)
    hz hzJ
  have hu : F ∪ (A ∪ L) = A ∪ L := union_eq_right.2 (hFA.trans subset_union_left)
  rwa [hu, Restart.fillH_union_of_forall_notMem_H fun w hw hwH => absurd (hLim w hw) (not_le.2 hwH)] at key

/-! ### Free points -/

theorem isFreeAt_of_mem_closure {F : Set ℂ} (hF : IsClosed F) {z : ℂ} (hzF : z ∉ F)
    (hz : z ∈ closure (H \ fillH F)) : IsFreeAt F z :=
  (isFreeAt_or_isTrappedAt hF hzF).resolve_right fun ⟨ε, hε, hd⟩ => by
    obtain ⟨y, hy, hyz⟩ := Metric.mem_closure_iff.1 hz ε hε
    exact Set.disjoint_left.1 hd (by rw [mem_ball, dist_comm]; exact hyz) hy

theorem mem_H_diff_fillH_of_isFreeAt {F : Set ℂ} {z : ℂ} (hf : IsFreeAt F z) (hz : z ∈ H) :
    z ∈ H \ fillH F := by
  obtain ⟨ε, hε, h⟩ := hf
  exact h ⟨mem_ball_self hε, hz⟩

theorem exists_ball_of_isFreeAt {F : Set ℂ} {z : ℂ} (hf : IsFreeAt F z) :
    ∃ ε > 0, ∀ w ∈ ball z ε, w ∈ H → w ∈ H \ fillH F := by
  obtain ⟨ε, hε, h⟩ := hf
  exact ⟨ε, hε, fun w hw hwH => h ⟨hw, hwH⟩⟩

/-- Freeness for two disjoint compact sets gives freeness for their union (Janiszewski in `ℍ`). -/
theorem isFreeAt_union_of_disjoint {F₁ F₂ : Set ℂ} (hF₁ : IsCompact F₁) (hF₂ : IsCompact F₂)
    (hd : Disjoint F₁ F₂) {z : ℂ} (h₁ : IsFreeAt F₁ z) (h₂ : IsFreeAt F₂ z) : IsFreeAt (F₁ ∪ F₂) z := by
  obtain ⟨ε₁, hε₁, hb₁⟩ := h₁
  obtain ⟨ε₂, hε₂, hb₂⟩ := h₂
  refine ⟨min ε₁ ε₂, lt_min hε₁ hε₂, fun w hw => ?_⟩
  refine H_diff_fillH_inter_subset hF₁ hF₂ (fun _ hw => (Set.disjoint_left.1 hd hw.1 hw.2).elim) ⟨?_, ?_⟩
  · exact hb₁ ⟨mem_of_mem_of_subset hw.1 (ball_subset_ball (min_le_left _ _)), hw.2⟩
  · exact hb₂ ⟨mem_of_mem_of_subset hw.1 (ball_subset_ball (min_le_right _ _)), hw.2⟩

/-- A point of `ℍ` in the unbounded domains of two disjoint compact sets is in that of their union. -/
theorem mem_H_diff_fillH_union_of_disjoint {F₁ F₂ : Set ℂ} (hF₁ : IsCompact F₁) (hF₂ : IsCompact F₂)
    (hd : Disjoint F₁ F₂) {z : ℂ} (h₁ : z ∈ H \ fillH F₁) (h₂ : z ∈ H \ fillH F₂) :
    z ∈ H \ fillH (F₁ ∪ F₂) :=
  H_diff_fillH_inter_subset hF₁ hF₂ (fun _ hw => (Set.disjoint_left.1 hd hw.1 hw.2).elim) ⟨h₁, h₂⟩

theorem mem_unboundedPart_of_mem_H_diff_fillH {F : Set ℂ} (hF : IsClosed F) {z : ℂ}
    (hz : z ∈ H \ fillH F) : z ∈ unboundedPart (H \ F) :=
  (mem_H_diff_fillH_of_isClosed hF).1 hz

theorem mem_H_diff_fillH_of_mem_unboundedPart {F : Set ℂ} (hF : IsClosed F) {z : ℂ}
    (hz : z ∈ unboundedPart (H \ F)) : z ∈ H \ fillH F :=
  (mem_H_diff_fillH_of_isClosed hF).2 hz

/-! ### Arcs on `ℝ≥0` parameters -/

/-- An arc `η([s, r])` (`η` continuous and injective there, `s < r`) does not separate the plane. -/
theorem isPreconnected_compl_image_Icc {η : ℝ≥0 → ℂ} {s r : ℝ≥0} (hsr : s < r)
    (hc : ContinuousOn η (Icc s r)) (hi : InjOn η (Icc s r)) : IsPreconnected (η '' Icc s r)ᶜ := by
  set Q : ℝ → ℂ := fun x => η x.toNNReal with hQ
  have hmaps : MapsTo Real.toNNReal (Icc (s : ℝ) r) (Icc s r) := fun x hx =>
    ⟨by rw [← Real.toNNReal_coe (r := s)]; exact Real.toNNReal_le_toNNReal hx.1,
      by rw [← Real.toNNReal_coe (r := r)]; exact Real.toNNReal_le_toNNReal hx.2⟩
  have himg : Q '' Icc (s : ℝ) r = η '' Icc s r := by
    ext z
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact ⟨x.toNNReal, hmaps hx, rfl⟩
    · rintro ⟨y, hy, rfl⟩
      exact ⟨y, ⟨by exact_mod_cast hy.1, by exact_mod_cast hy.2⟩, by simp [hQ]⟩
  have hQc : ContinuousOn Q (Icc (s : ℝ) r) := hc.comp continuous_real_toNNReal.continuousOn hmaps
  have hQi : InjOn Q (Icc (s : ℝ) r) := by
    intro x hx y hy hxy
    have h := hi (hmaps hx) (hmaps hy) hxy
    have hx0 : 0 ≤ x := (NNReal.coe_nonneg s).trans hx.1
    have hy0 : 0 ≤ y := (NNReal.coe_nonneg s).trans hy.1
    have := congrArg (fun t : ℝ≥0 => (t : ℝ)) h
    simpa [Real.coe_toNNReal _ hx0, Real.coe_toNNReal _ hy0] using this
  rw [← himg]
  exact (YuanCharacterisation.isConnected_compl_image_Icc (by exact_mod_cast hsr) hQc hQi).isPreconnected

/-! ### Good paths -/

section GoodPath

open Restart

variable {η : ℝ≥0 → ℂ} {ζ : ℝ≥0∞} {x : ℝ}

theorem IsPathGood.zero (hp : IsPathGood η ζ x) : η 0 = x := by
  obtain ⟨-, w, -, -, hg⟩ := hp
  exact sub_eq_zero.1 hg.1

theorem IsPathGood.continuousOn_Icc (hp : IsPathGood η ζ x) {s : ℝ≥0} (hs : (s : ℝ≥0∞) ≤ ζ) :
    ContinuousOn η (Icc 0 s) :=
  hp.continuousOn.mono fun _ ht => (ENNReal.coe_le_coe.2 ht.2).trans hs

theorem IsPathGood.injOn_Icc (hp : IsPathGood η ζ x) {s : ℝ≥0} (hs : (s : ℝ≥0∞) ≤ ζ) :
    InjOn η (Icc 0 s) :=
  hp.1.mono fun _ ht => (ENNReal.coe_le_coe.2 ht.2).trans hs

theorem IsPathGood.isCompact_image (hp : IsPathGood η ζ x) {s : ℝ≥0} (hs : (s : ℝ≥0∞) ≤ ζ) :
    IsCompact (η '' Icc 0 s) :=
  isCompact_Icc.image_of_continuousOn (IsPathGood.continuousOn_Icc hp hs)

theorem IsPathGood.isCompact_image_Icc (hp : IsPathGood η ζ x) {s r : ℝ≥0} (hr : (r : ℝ≥0∞) ≤ ζ) :
    IsCompact (η '' Icc s r) :=
  isCompact_Icc.image_of_continuousOn
    (hp.continuousOn.mono fun _ ht => (ENNReal.coe_le_coe.2 ht.2).trans hr)

/-- The tip property of a good path. -/
theorem IsPathGood.mem_closure_of_lt (hp : IsPathGood η ζ x) {u s : ℝ≥0} (hus : u < s)
    (hs : (s : ℝ≥0∞) ≤ ζ) : η s ∈ closure (H \ fillH (η '' Icc 0 u)) := by
  obtain ⟨-, w, hw, hw0, hg⟩ := hp
  exact Restart.IsGeneratingTrace.mem_closure_of_lt_add hg hw hw0 hus hs

theorem IsPathGood.im_nonneg (hp : IsPathGood η ζ x) {s : ℝ≥0} (hs : (s : ℝ≥0∞) ≤ ζ) :
    0 ≤ (η s).im := by
  rcases eq_or_lt_of_le ((zero_le : (0 : ℝ≥0) ≤ s)) with h | h
  · rw [← h, IsPathGood.zero hp]; simp
  · have h1 := IsPathGood.mem_closure_of_lt hp h hs
    have h2 : closure (H \ fillH (η '' Icc 0 0)) ⊆ {z : ℂ | 0 ≤ z.im} :=
      closure_minimal (fun z hz => (show (0 : ℝ) ≤ z.im from le_of_lt hz.1))
        (isClosed_le continuous_const continuous_im)
    exact h2 h1

/-- **The tip property as freeness**: for `u < s ≤ ζ`, the old prefix `η([0, u])` is free at `η(s)`. -/
theorem IsPathGood.isFreeAt_of_lt (hp : IsPathGood η ζ x) {u s : ℝ≥0} (hus : u < s)
    (hs : (s : ℝ≥0∞) ≤ ζ) : IsFreeAt (η '' Icc 0 u) (η s) := by
  have huζ : (u : ℝ≥0∞) ≤ ζ := (ENNReal.coe_le_coe.2 hus.le).trans hs
  refine isFreeAt_of_mem_closure (IsPathGood.isCompact_image hp huζ).isClosed ?_
    (IsPathGood.mem_closure_of_lt hp hus hs)
  rintro ⟨r, hr, hrs⟩
  have := hp.1 ((ENNReal.coe_le_coe.2 hr.2).trans huζ) hs hrs
  exact absurd (this ▸ hr.2) (not_le.2 hus)

theorem IsPathGood.mem_H_diff_fillH_of_lt (hp : IsPathGood η ζ x) {u s : ℝ≥0} (hus : u < s)
    (hs : (s : ℝ≥0∞) ≤ ζ) (hsH : η s ∈ H) : η s ∈ H \ fillH (η '' Icc 0 u) :=
  mem_H_diff_fillH_of_isFreeAt (IsPathGood.isFreeAt_of_lt hp hus hs) hsH

/-- **Adding the path's own slit.** If `η([u, r]) ⊆ ℍ`, a point of the unbounded domain of `η([0, u])` off `η([0, r])`
is in the unbounded domain of `η([0, r])`. -/
theorem IsPathGood.mem_H_diff_fillH_of_slit (hp : IsPathGood η ζ x) {u r : ℝ≥0} (hur : u < r)
    (hr : (r : ℝ≥0∞) ≤ ζ) (hH : η '' Icc u r ⊆ H) {z : ℂ} (hz : z ∈ H \ fillH (η '' Icc 0 u))
    (hzr : z ∉ η '' Icc 0 r) : z ∈ H \ fillH (η '' Icc 0 r) := by
  have huζ : (u : ℝ≥0∞) ≤ ζ := (ENNReal.coe_le_coe.2 hur.le).trans hr
  have hsplit : η '' Icc 0 r = η '' Icc 0 u ∪ η '' Icc u r := by
    rw [← image_union, Icc_union_Icc_eq_Icc (zero_le : (0 : ℝ≥0) ≤ u) hur.le]
  have hinter : η '' Icc 0 u ∩ η '' Icc u r = {η u} := by
    refine Subset.antisymm ?_ ?_
    · rintro _ ⟨⟨a, ha, rfl⟩, ⟨c, hc, hac⟩⟩
      have hcζ : (c : ℝ≥0∞) ≤ ζ := (ENNReal.coe_le_coe.2 hc.2).trans hr
      have haζ : (a : ℝ≥0∞) ≤ ζ := (ENNReal.coe_le_coe.2 ha.2).trans huζ
      have := hp.1 hcζ haζ hac
      rw [mem_singleton_iff, ← this, le_antisymm (this ▸ ha.2) hc.1]
    · rintro _ rfl
      exact ⟨⟨u, ⟨(zero_le : (0 : ℝ≥0) ≤ u), le_rfl⟩, rfl⟩, ⟨u, ⟨le_rfl, hur.le⟩, rfl⟩⟩
  rw [hsplit]
  refine mem_H_diff_fillH_union_of_slit (IsPathGood.isCompact_image hp huζ)
    (IsPathGood.isCompact_image_Icc hp hr)
    (isPreconnected_compl_image_Icc hur (hp.continuousOn.mono fun _ ht =>
      (ENNReal.coe_le_coe.2 ht.2).trans hr) (hp.1.mono fun _ ht => (ENNReal.coe_le_coe.2 ht.2).trans hr))
    hH (by rw [hinter]; exact isPreconnected_singleton) hz ?_
  rw [hsplit] at hzr
  exact fun h => hzr (Or.inr h)

/-- **Tip plus slit.** For `u < s ≤ ζ` there is `ε > 0` such that, for every `r ≥ s` with `η([u, r]) ⊆ ℍ`, every
point of `ℍ` off `η([0, r])` within `ε` of `η(s)` is in the unbounded domain of `η([0, r])`. -/
theorem IsPathGood.exists_ball_mem_H_diff_fillH (hp : IsPathGood η ζ x) {u s : ℝ≥0} (hus : u < s)
    (hs : (s : ℝ≥0∞) ≤ ζ) :
    ∃ ε > 0, ∀ r : ℝ≥0, s ≤ r → (r : ℝ≥0∞) ≤ ζ → η '' Icc u r ⊆ H →
      ∀ z ∈ ball (η s) ε, z ∈ H → z ∉ η '' Icc 0 r → z ∈ H \ fillH (η '' Icc 0 r) := by
  obtain ⟨ε, hε, hball⟩ := exists_ball_of_isFreeAt (IsPathGood.isFreeAt_of_lt hp hus hs)
  exact ⟨ε, hε, fun r hsr hr hH z hz hzH hzr =>
    IsPathGood.mem_H_diff_fillH_of_slit hp (hus.trans_le hsr) hr hH (hball z hz hzH) hzr⟩

end GoodPath

end Sec7

end InteractingSLE
