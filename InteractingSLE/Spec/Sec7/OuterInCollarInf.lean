/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.R7GapEqGeoWalls
import InteractingSLE.Spec.Sec7.R7EndFaceLocal
import InteractingSLE.Spec.Sec7.Aux37SideInf
import InteractingSLE.Spec.Sec7.R7StopInMixedInf
import InteractingSLE.Spec.Sec7.R7FaceSelectSides
import InteractingSLE.Spec.Sec7.TwoForceMain3Pocket

/-!
# Exterior collars of the change pocket opening at the flow seed, and the two-outer gap equality at infinity

Packet PROVE-R7-OUTERIN. PROVE-R7-GAPEQ proved the exterior collars of the bounded change pocket
(`R7GapEqGeo.hasExteriorCollar_cfArcR/L`) from the Jordan topology of the bounded pocket. The pocket opening at the
flow seed (`rightLo = 0`) is unbounded in the counterflow chart, but its Cayley image is still a bounded Jordan
domain of the disc (`IsChangeConfigInc.cayleyChange_props`), and `cfPt`, `−cayley` are mutually inverse homeomorphisms
between the open disc and `ℍ`. Hence:

* `isLocConnWithin_compl_closure_cfPocket`: the complement of the closed pocket is locally connected from within at
  every frontier point in `ℍ` (Schoenflies in the disc, transported by `cfPt`);
* **`hasExteriorCollar_cfArcRInf`**, **`hasExteriorCollar_cfArcLInf`**: the exterior collars at every point of the two
  proper arms (`v > 0`), from the same exterior incidence and local frontier as in the bounded case;
* `no_interval_frontier_inf`: Aux. lemma 42 excludes every positive trace interval on the two proper arms (a countable
  union of compact simple arcs);
* **`pocketGapEqInf_outerOuter`**: §5.4's gap equality at infinity for a pocket with two outer arms
  (`R7GapEq.pocketGapEqInf_of_outerCollars`).

R48: nothing here uses Theorem 1.2/1.3, `Theorem12ParamStatement`, `Theorem13Statement` or any `*_of_param`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Complex Set Metric Filter Topology Bornology
open QuantumZipper (H Hbar)
open QuantumZipper.CA (cayley)
open InteractingSLE.WangWu (negInv)
open scoped NNReal

namespace InteractingSLE.Sec7.OuterIn

open WangWu Lemma71I PocketJordan PocketCoord R7StopIn R7GapEq R7GapEqFin R7GapEqGeo

/-! ### Local connectivity is local -/

section Local

/-- Local connectivity from within is unchanged by intersecting with an open neighbourhood. -/
theorem isLocConnWithin_inter_of_isOpen {A U : Set ℂ} {z : ℂ} (hA : Sec6.IsLocConnWithin A z) (hU : IsOpen U)
    (hzU : z ∈ U) : Sec6.IsLocConnWithin (A ∩ U) z := by
  intro ε hε
  obtain ⟨δ, hδ, hδU⟩ := Metric.isOpen_iff.1 hU z hzU
  obtain ⟨A', hA', hA'c, hA'N⟩ := hA (min ε δ) (lt_min hε hδ)
  refine ⟨A', fun w hw => ⟨⟨(hA' hw).1, hδU (ball_subset_ball (min_le_right _ _) (hA' hw).2)⟩,
    ball_subset_ball (min_le_left _ _) (hA' hw).2⟩, hA'c, nhdsWithin_mono _ inter_subset_left hA'N⟩

/-- Local connectivity from within of `A ∩ U` (`U` an open neighbourhood) gives that of `A`. -/
theorem isLocConnWithin_of_inter_isOpen {A U : Set ℂ} {z : ℂ} (hA : Sec6.IsLocConnWithin (A ∩ U) z)
    (hU : IsOpen U) (hzU : z ∈ U) : Sec6.IsLocConnWithin A z := by
  intro ε hε
  obtain ⟨A', hA', hA'c, hA'N⟩ := hA ε hε
  refine ⟨A', fun w hw => ⟨(hA' hw).1.1, (hA' hw).2⟩, hA'c, ?_⟩
  rwa [nhdsWithin_inter_of_mem' (mem_nhdsWithin_of_mem_nhds (hU.mem_nhds hzU))] at hA'N

end Local

/-! ### The complement of the closed pocket near a finite frontier point -/

section Collar

variable {R L : ℝ≥0 → ℂ} {r : ℝ≥0}

/-- **The complement of the closed change pocket is locally connected from within at a frontier point of `ℍ`**
(any change configuration, bounded or opening at the flow seed): Schoenflies for the bounded Jordan pocket of the disc
(`isLocConnWithin_compl_closure_jordan`), transported by `cfPt` (inverse `−cayley`) between the open disc and `ℍ`. -/
theorem isLocConnWithin_compl_closure_cfPocket (h : IsChangeConfigInc R L r) {p : ℂ} (hpH : p ∈ H)
    (hp : -cayley p ∈ frontier (cayley '' changePocket R L r)) :
    Sec6.IsLocConnWithin (closure (cfPocket R L r))ᶜ p := by
  obtain ⟨hJ, hball, hfr⟩ := h.cayleyChange_props
  have hCH := h.changePocket_subset_H
  have hDo := Lemma71F.isOpen_cayley_image h.isOpen_changePocket hCH
  have hDc := Lemma71F.isConnected_cayley_image h.isConnected_changePocket hCH
  have hloc0 := isLocConnWithin_compl_closure_jordan hDo hDc (isBounded_ball.subset hball) (hfr ▸ hJ) hp
  have hpHb : p ∈ Hbar := H_subset_Hbar' hpH
  have hwb : -cayley p ∈ ball (0 : ℂ) 1 := by
    rw [mem_ball_zero_iff, norm_neg, ← mem_ball_zero_iff]
    exact QuantumZipper.CA.cayley_mem_ball hpH
  have hne : ∀ w ∈ ball (0 : ℂ) 1, w ≠ -1 := fun w hw he => by
    rw [he, mem_ball_zero_iff, norm_neg, norm_one] at hw
    exact lt_irrefl _ hw
  have hloc1 := isLocConnWithin_inter_of_isOpen hloc0 isOpen_ball hwb
  have hCeq : cfPocket R L r = cfPt '' (cayley '' changePocket R L r) := by
    rw [cfPocket, image_negInv_eq hCH]
  refine isLocConnWithin_of_inter_isOpen (U := H) ?_ QuantumZipper.isOpen_H hpH
  refine isLocConnWithin_of_inverse (f := cfPt) (g := fun z => -cayley z)
    (E := (closure (cayley '' changePocket R L r))ᶜ ∩ ball 0 1)
    (continuousOn_cfPt.mono fun w hw => hne w hw.2) (continuousAt_cfPt (neg_cayley_ne_neg_one hpHb))
    (continuousAt_neg_cayley hpHb) ?_ ?_ ?_ (cfPt_neg_cayley hpHb) hloc1
  · rintro w ⟨hw, hwb'⟩
    refine ⟨fun hcl => hw ?_, cfPt_mem_H hwb'⟩
    have h1 := neg_cayley_mem_closure hCH hcl
    rwa [neg_cayley_cfPt (hne w hwb')] at h1
  · rintro z ⟨hz, hzH⟩
    have hzb : -cayley z ∈ ball (0 : ℂ) 1 := by
      rw [mem_ball_zero_iff, norm_neg, ← mem_ball_zero_iff]
      exact QuantumZipper.CA.cayley_mem_ball hzH
    refine ⟨fun hcl => hz ?_, hzb⟩
    have h1 := (continuousAt_cfPt (hne _ hzb)).continuousWithinAt.mem_closure_image hcl
    rwa [cfPt_neg_cayley (H_subset_Hbar' hzH), ← hCeq] at h1
  · rintro z ⟨-, hzH⟩
    exact cfPt_neg_cayley (H_subset_Hbar' hzH)

/-- **An exterior collar from exterior incidence, the local frontier and local connectivity of the exterior** (the
argument of `R7GapEqFin.hasExteriorCollar_of_exterior_incidence` without boundedness of the pocket). -/
theorem hasExteriorCollar_of_incidence_locConn {C F K : Set ℂ} {p : ℂ} (hCo : IsOpen C) (hFo : IsOpen F)
    (hfrK : frontier C ⊆ K) (hinc : p ∈ closure (F \ closure C))
    (hfr : ∃ ε > 0, frontier F ∩ ball p ε ⊆ closure C) (hloc : Sec6.IsLocConnWithin (closure C)ᶜ p) :
    HasExteriorCollar C F K p := by
  have hFo' : IsOpen (F \ closure C) := hFo.sdiff isClosed_closure
  have hdisj : Disjoint C (F \ closure C) :=
    Set.disjoint_left.2 fun z hz hzF => hzF.2 (subset_closure hz)
  have hfr' : ∃ ε > 0, frontier (F \ closure C) ∩ ball p ε ⊆ closure C := by
    obtain ⟨ε, hε, hεfr⟩ := hfr
    refine ⟨ε, hε, fun z hz => ?_⟩
    rcases frontier_inter_subset F (closure C)ᶜ hz.1 with ⟨hzF, _⟩ | ⟨_, hzC⟩
    · exact hεfr ⟨hzF, hz.2⟩
    · rw [frontier_compl] at hzC
      exact frontier_subset_closure (frontier_closure_subset hzC)
  obtain ⟨U, hU, hpU, hcov⟩ := hasExteriorCollar_of_locConn hCo hFo' hdisj hfrK hinc hloc hfr'
  refine ⟨U, hU, hpU, fun z hz => ?_⟩
  rcases hcov hz with (hzC | hzF) | hzK
  · exact Or.inl (Or.inl hzC)
  · exact Or.inl (Or.inr hzF.1)
  · exact Or.inr hzK

end Collar

/-! ### The collars at the two proper arms -/

section Arms

variable {R L : ℝ≥0 → ℂ} {r : ℝ≥0}

/-- **Right outer collar of the change pocket opening at the flow seed** (every point `cfArcRInf v`, `v > 0`, of the
proper right arm): as `R7GapEqGeo.hasExteriorCollar_cfArcR`, with the exterior's local connectivity from the disc
(`isLocConnWithin_compl_closure_cfPocket`) in place of the bounded Jordan pocket. -/
theorem hasExteriorCollar_cfArcRInf (h : IsChangeConfigInc R L r) (h0 : rightLo R L r = 0)
    (hCl : changePocket R L r ⊆ leftSideOf (range R)) {F K : Set ℂ}
    (hside : negInv '' rightSideOf (range R) ⊆ F)
    (hK : frontier (cfPocket R L r) ⊆ K) {v : ℝ} (hv : 0 < v) :
    HasExteriorCollar (cfPocket R L r) F K (cfArcRInf R L r v) := by
  have hC := h.isCfPocketInf h0
  obtain ⟨-, hb, hab, -⟩ := h.changeCorner_props
  have hu0 : 0 < rightHi R L r := h0 ▸ hab
  have h1v : 1 < 1 + v := by linarith
  have ht : rightHi R L r / (1 + v) ∈ Ioo 0 (rightHi R L r) :=
    ⟨div_pos hu0 (by linarith), div_lt_self hu0 h1v⟩
  have ht01 : rightHi R L r / (1 + v) ∈ Ioo (0 : ℝ) 1 := ⟨ht.1, ht.2.trans_le hb.2⟩
  have hα := h.isDiscCrosscut_right
  have hne : toDisc (realPath R) (rightHi R L r / (1 + v)) ≠ -1 := fun he => by
    have heq := hα.inj ⟨ht01.1.le, ht01.2.le⟩ ⟨le_rfl, zero_le_one⟩ (he.trans hα.zero.symm)
    exact ht01.1.ne' heq
  have hpH : cfArcRInf R L r v ∈ H := hC.mem_H₁ v hv
  have hp : -cayley (cfArcRInf R L r v) = toDisc (realPath R) (rightHi R L r / (1 + v)) := neg_cayley_cfPt hne
  have hclip : cfPt '' (toDisc (realPath R) '' Ioo 0 (rightHi R L r)) ⊆ closure (cfPocket R L r) := by
    rintro _ ⟨_, ⟨s, hs, rfl⟩, rfl⟩
    apply frontier_subset_closure
    rw [hC.frontier_eq]
    refine Or.inl ⟨rightHi R L r / s - 1, sub_nonneg.2 ((one_le_div hs.1).2 hs.2.le), ?_⟩
    simp only [cfArcRInf, add_sub_cancel, div_div_cancel₀ hu0.ne']
  have hfr := local_frontier_right_clip h.right le_rfl hb.2 ht hp hpH hclip
  obtain ⟨he, -⟩ := cfPt_toDisc_of_mem h.right ht01
  have hpR : negInv (cfArcRInf R L r v) ∈ range R := by
    change negInv (cfPt (toDisc (realPath R) (rightHi R L r / (1 + v)))) ∈ range R
    rw [he, negInv_negInv]
    exact mem_range_self _
  have hRR : Disjoint (range R) (rightSideOf (range R)) := Set.disjoint_left.2
    fun z hzR hzS => hzS.1.2 hzR
  have hinc := rightWall_exterior_incidence h.right h.right hCl hRR hpR (negInv_mem_H hpH)
  rw [negInv_negInv] at hinc
  have hloc : Sec6.IsLocConnWithin (closure (cfPocket R L r))ᶜ (cfArcRInf R L r v) := by
    refine isLocConnWithin_compl_closure_cfPocket h hpH ?_
    rw [hp, h.cayleyChange_props.2.2]
    exact Or.inl ⟨_, ⟨by rw [h0]; exact ht.1.le, ht.2.le⟩, rfl⟩
  obtain ⟨U, hU, hpU, hcov⟩ := hasExteriorCollar_of_incidence_locConn hC.isOpen (forbidden_right h.right).1 hK
    hinc hfr hloc
  refine ⟨U, hU, hpU, fun z hz => ?_⟩
  rcases hcov hz with (hzC | hzF) | hzK
  · exact Or.inl (Or.inl hzC)
  · exact Or.inl (Or.inr (hside hzF))
  · exact Or.inr hzK

/-- **Left outer collar of the change pocket opening at the flow seed** (every point `cfArcLInf v`, `v > 0`). -/
theorem hasExteriorCollar_cfArcLInf (h : IsChangeConfigInc R L r) (h0 : rightLo R L r = 0)
    (hCr : changePocket R L r ⊆ rightSideOf (range L)) {F K : Set ℂ}
    (hside : negInv '' leftSideOf (range L) ⊆ F)
    (hK : frontier (cfPocket R L r) ⊆ K) {v : ℝ} (hv : 0 < v) :
    HasExteriorCollar (cfPocket R L r) F K (cfArcLInf R L r v) := by
  have hC := h.isCfPocketInf h0
  obtain ⟨hg, hc1, hc2, -, -, -⟩ := h.changeCorners
  obtain ⟨-, -, -, -, hb, hab, -⟩ := h.changeCorner_props
  have hl0 := h.leftLo_eq_zero_of_rightLo_eq_zero h0
  have hu0 : 0 < leftHi R L r := hl0 ▸ hab
  have h1v : 1 < 1 + v := by linarith
  have ht : leftHi R L r / (1 + v) ∈ Ioo 0 (leftHi R L r) :=
    ⟨div_pos hu0 (by linarith), div_lt_self hu0 h1v⟩
  have ht01 : leftHi R L r / (1 + v) ∈ Ioo (0 : ℝ) 1 := ⟨ht.1, ht.2.trans_le hb.2⟩
  have hα := h.isDiscCrosscut_left
  have hne : toDisc (realPath L) (leftHi R L r / (1 + v)) ≠ -1 := fun he => by
    have heq := hα.inj ⟨ht01.1.le, ht01.2.le⟩ ⟨le_rfl, zero_le_one⟩ (he.trans hα.zero.symm)
    exact ht01.1.ne' heq
  have hpH : cfArcLInf R L r v ∈ H := hC.mem_H₂ v hv
  have hp : -cayley (cfArcLInf R L r v) = toDisc (realPath L) (leftHi R L r / (1 + v)) := neg_cayley_cfPt hne
  have hclip : cfPt '' (toDisc (realPath L) '' Ioo 0 (leftHi R L r)) ⊆ closure (cfPocket R L r) := by
    rintro _ ⟨_, ⟨s, hs, rfl⟩, rfl⟩
    apply frontier_subset_closure
    rw [hC.frontier_eq]
    refine Or.inr ⟨leftHi R L r / s - 1, sub_nonneg.2 ((one_le_div hs.1).2 hs.2.le), ?_⟩
    simp only [cfArcLInf, add_sub_cancel, div_div_cancel₀ hu0.ne']
  have hfr := local_frontier_left_clip h.left le_rfl hb.2 ht hp hpH hclip
  obtain ⟨he, -⟩ := cfPt_toDisc_of_mem h.left ht01
  have hpL : negInv (cfArcLInf R L r v) ∈ range L := by
    change negInv (cfPt (toDisc (realPath L) (leftHi R L r / (1 + v)))) ∈ range L
    rw [he, negInv_negInv]
    exact mem_range_self _
  have hLL : Disjoint (range L) (rightSideOf (range L)) := Set.disjoint_left.2
    fun z hzL hzS => hzS.1.2 hzL
  have hinc := leftWall_exterior_incidence h.left h.left hCr hLL hpL (negInv_mem_H hpH)
  rw [negInv_negInv] at hinc
  have hloc : Sec6.IsLocConnWithin (closure (cfPocket R L r))ᶜ (cfArcLInf R L r v) := by
    refine isLocConnWithin_compl_closure_cfPocket h hpH ?_
    rw [hp, h.cayleyChange_props.2.2]
    refine Or.inr ⟨_, ?_, rfl⟩
    rw [hc1, hc2, hl0]
    exact ⟨ht.1.le, ht.2.le⟩
  obtain ⟨U, hU, hpU, hcov⟩ := hasExteriorCollar_of_incidence_locConn hC.isOpen (forbidden_left h.left).1 hK
    hinc hfr hloc
  refine ⟨U, hU, hpU, fun z hz => ?_⟩
  rcases hcov hz with (hzC | hzF) | hzK
  · exact Or.inl (Or.inl hzC)
  · exact Or.inl (Or.inr (hside hzF))
  · exact Or.inr hzK

end Arms

/-! ### Aux. lemma 42 on the proper arms, and the gap equality at infinity -/

section Gap

/-- A continuous curve injective on a nontrivial compact interval has a compact simple arc as image. -/
theorem isSimpleArc_image_Icc {α : ℝ → ℂ} {a b : ℝ} (hab : a < b) (hc : ContinuousOn α (Icc a b))
    (hi : InjOn α (Icc a b)) : Theorem14.GB10.IsSimpleArc (α '' Icc a b) := by
  have hmaps : MapsTo (fun v : ℝ => a + v * (b - a)) (Icc 0 1) (Icc a b) := fun v hv => by
    rw [← image_affine_Icc_zero_one hab.le]
    exact ⟨v, hv, rfl⟩
  refine ⟨fun v => α (a + v * (b - a)), hc.comp (by fun_prop) hmaps, fun v hv w hw he => ?_, ?_⟩
  · have h1 := hi (hmaps hv) (hmaps hw) he
    have hba : b - a ≠ 0 := (sub_pos.2 hab).ne'
    exact mul_right_cancel₀ hba (add_left_cancel h1)
  · rw [← image_affine_Icc_zero_one hab.le, image_image]

/-- **Aux. lemma 42 on two proper arms**: no positive trace interval lies in the union of the images of two
continuous curves injective on `[0, ∞)` (a countable union of compact simple arcs `α([n, n + 1])`). -/
theorem no_interval_frontier_inf {η α₁ α₂ : ℝ → ℂ} (hc₁ : ContinuousOn α₁ (Ici 0)) (hc₂ : ContinuousOn α₂ (Ici 0))
    (hi₁ : InjOn α₁ (Ici 0)) (hi₂ : InjOn α₂ (Ici 0)) (hηc : ContinuousOn η (Ici 0))
    (h42 : Theorem14.GB10.NoSimpleArcInterval (fun s : ℝ≥0 => η s) ⊤) :
    ∀ a b : ℝ, 0 ≤ a → a < b → ¬ η '' Icc a b ⊆ α₁ '' Ici 0 ∪ α₂ '' Ici 0 := by
  intro a b ha hab hsub
  set A : ℕ → Set ℂ := fun n => (if Even n then α₁ else α₂) '' Icc ((n / 2 : ℕ) : ℝ) ((n / 2 : ℕ) + 1) with hA
  have hIcc : ∀ m : ℕ, Icc (m : ℝ) (m + 1) ⊆ Ici 0 := fun m x hx => (Nat.cast_nonneg m).trans hx.1
  have hAs : ∀ n, Theorem14.GB10.IsSimpleArc (A n) := fun n => by
    simp only [hA]
    split_ifs
    · exact isSimpleArc_image_Icc (lt_add_one _) (hc₁.mono (hIcc _)) (hi₁.mono (hIcc _))
    · exact isSimpleArc_image_Icc (lt_add_one _) (hc₂.mono (hIcc _)) (hi₂.mono (hIcc _))
  have hab' : a.toNNReal < b.toNNReal := (Real.toNNReal_lt_toNNReal_iff (ha.trans_lt hab)).2 hab
  refine h42.not_image_subset_iUnion hab' ENNReal.coe_lt_top
    (hηc.comp continuous_subtype_val.continuousOn fun s _ => s.2) (A := A) hAs ?_
  rintro _ ⟨s, hs, rfl⟩
  have hs' : (s : ℝ) ∈ Icc a b := by
    constructor
    · have := NNReal.coe_le_coe.2 hs.1
      rwa [Real.coe_toNNReal _ ha] at this
    · have := NNReal.coe_le_coe.2 hs.2
      rwa [Real.coe_toNNReal _ (ha.trans hab.le)] at this
  have hfl : ∀ x : ℝ, 0 ≤ x → x ∈ Icc ((⌊x⌋₊ : ℕ) : ℝ) ((⌊x⌋₊ : ℕ) + 1) := fun x hx =>
    ⟨Nat.floor_le hx, (Nat.lt_floor_add_one x).le⟩
  rcases hsub ⟨_, hs', rfl⟩ with ⟨x, hx, hxe⟩ | ⟨x, hx, hxe⟩
  · refine mem_iUnion.2 ⟨2 * ⌊x⌋₊, ?_⟩
    have h2 : 2 * ⌊x⌋₊ / 2 = ⌊x⌋₊ := by omega
    simp only [hA, even_two_mul, ↓reduceIte, h2]
    exact ⟨x, hfl x hx, hxe⟩
  · refine mem_iUnion.2 ⟨2 * ⌊x⌋₊ + 1, ?_⟩
    have h2 : (2 * ⌊x⌋₊ + 1) / 2 = ⌊x⌋₊ := by omega
    have hodd : ¬ Even (2 * ⌊x⌋₊ + 1) := Nat.not_even_iff_odd.2 (odd_two_mul_add_one _)
    simp only [hA, hodd, ↓reduceIte, h2]
    exact ⟨x, hfl x hx, hxe⟩

variable {R L : ℝ≥0 → ℂ} {r : ℝ≥0}

/-- **§5.4's gap equality at infinity for a pocket with two outer arms** (`M₁ = β_R`, `M₂ = β_L` between the walls,
`rightLo = 0`): every point of the two proper arms has an exterior collar (`hasExteriorCollar_cfArc{R,L}Inf`), so
`R7GapEq.pocketGapEqInf_of_outerCollars` applies; the entrance corner is visited along the clipped `β_R`. -/
theorem pocketGapEqInf_outerOuter (h : IsChangeConfigInc R L r) (h0 : rightLo R L r = 0) {M₁ M₂ : ℝ≥0 → ℂ}
    (hM₁ : IsSimpleProper M₁)
    (hO₁ : IsOrderedArcs (Lemma71I.realPath R) (Lemma71I.realPath M₁) (Lemma71I.realPath L))
    (hO₂ : IsOrderedArcs (Lemma71I.realPath R) (Lemma71I.realPath M₂) (Lemma71I.realPath L))
    (hc₁R : NoCommonArc M₁ R) (hc₁L : NoCommonArc M₁ L) {W : ℝ → ℝ} {η : ℝ → ℂ} (hη : IsLoewnerTrace W η)
    (havoid : ∀ t, 0 ≤ t → negInv (η t) ∉ rightSideOf (range M₁) ∪ leftSideOf (range M₂))
    (hrev₁ : IsWallReverseVisit M₁ η) (hvis₁ : IsWallVisited M₁ η)
    (h42 : Theorem14.GB10.NoSimpleArcInterval (fun s : ℝ≥0 => η s) ⊤) :
    PocketGapEqInf η (cfPocket R L r) (firstHit η (cfArcRInf R L r 0)) := by
  have hC := h.isCfPocketInf h0
  obtain ⟨τ₁, -, -, -, -, hB0, -, hBvis⟩ := exists_midArcInf h hM₁ hO₁ hc₁R hc₁L hη.1 hrev₁
  obtain ⟨hτ0, hτ, -⟩ := firstHit_spec hη.2.1 (hB0 ▸ hBvis hvis₁ 0 (mem_Ici.2 le_rfl))
  let O := cfArcRInf R L r '' Ioi (0 : ℝ) ∪ cfArcLInf R L r '' Ioi (0 : ℝ)
  have hK : ∀ a b : ℝ, 0 ≤ a → a < b → ¬ η '' Icc a b ⊆ frontier (cfPocket R L r) := by
    rw [hC.frontier_eq]
    exact no_interval_frontier_inf hC.cont₁ hC.cont₂ hC.inj₁ hC.inj₂ hη.2.1 h42
  apply pocketGapEqInf_of_outerCollars hη.2.1 hC.isOpen hK
    (F := negInv '' rightSideOf (range M₁) ∪ negInv '' leftSideOf (range M₂)) ?_ (O := O) ?_ ?_ hτ0 hτ
  · intro t ht hm
    rcases hm with hm | hm
    · exact notMem_image_negInv (fun hz => havoid t ht (Or.inl hz)) hm
    · exact notMem_image_negInv (fun hz => havoid t ht (Or.inr hz)) hm
  · rw [hC.frontier_eq]
    rintro p (⟨v, hv, rfl⟩ | ⟨v, hv, rfl⟩)
    · rcases eq_or_lt_of_le (mem_Ici.1 hv) with hv0 | hv0
      · exact Or.inl (congrArg (cfArcRInf R L r) hv0.symm)
      · exact Or.inr (Or.inl ⟨v, hv0, rfl⟩)
    · rcases eq_or_lt_of_le (mem_Ici.1 hv) with hv0 | hv0
      · exact Or.inl ((congrArg (cfArcLInf R L r) hv0.symm).trans hC.seed)
      · exact Or.inr (Or.inr ⟨v, hv0, rfl⟩)
  · rintro p (⟨v, hv, rfl⟩ | ⟨v, hv, rfl⟩)
    · exact hasExteriorCollar_cfArcRInf h h0 (R7FaceSelect.changePocket_subset_left_of_order h hO₁)
        ((R7FaceSelect.right_exterior_subset hO₁).trans subset_union_left) Subset.rfl hv
    · exact hasExteriorCollar_cfArcLInf h h0 (R7FaceSelect.changePocket_subset_right_of_order h hO₂)
        ((R7FaceSelect.left_exterior_subset hO₂).trans subset_union_right) Subset.rfl hv

end Gap

end InteractingSLE.Sec7.OuterIn
