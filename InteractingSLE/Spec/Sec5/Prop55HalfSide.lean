/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.S9BTransfer
import InteractingSLE.Spec.Sec5.Carrier
import InteractingSLE.Frozen.Spec.leftSideOf

/-!
# Proposition 5.5 in `ℍ`: the order of two proper curves from `0`, three ways

Packet PROVE-SEC5-K (specification p. 135, Proposition 5.5: "`η_{θ₂}|[0,τ₂]` almost surely lies to the left of
`η_{θ₁}|[0,τ₁]`. The same result holds if `η_{θ₁}, η_{θ₂}` are flow lines of a GFF `h` on `ℍ` from `0` to `∞`"). Its
proof gives the order in the form "no point of `η_{θ₁}` is strictly on the left of `η_{θ₂}`" (`η_{θ₁}` is contained in
the left boundary of a counterflow line, which passes to the right of `η_{θ₂}`, Proposition 5.1): this is
`LiesRightOf (range η_{θ₁}) (range η_{θ₂})` with the strict sides of `Carrier.lean`. The consumer
(`Lemma71H.Prop55HalfPlaneStatement`) uses the frozen W0 order `range η_{θ₂} ⊆ closedLeftSide η_{θ₁}` (the curve closed
along its lower vertical ray, specification p. 528). This file proves that the first form implies the second for
simple proper curves from `0` (`IsSeedProper`).

## Main results

* `exists_ofReal_mem_closure_of_joinedIn`: **first exit from `ℍ`** along a path off a set `S`;
* `mem_leftSideOf_of_mem_leftSide`: a point of `ℍ` in the Jordan left side of a simple proper curve from `0`
  (`Supp9B.leftSide`) is on its frozen left side `leftSideOf`;
* `leftSideOf_subset_stripLeftSide`: for a closed set off the negative real axis, the frozen left side (components
  reaching `(−∞, 0)`) is the strip left side (components reaching `(−1, 0)`);
* `range_subset_closedLeftSide_of_disjoint`: **the dual order**. If no point of `α` is on the frozen left side of
  `β`, then `β` lies in the closed left side of `α`. Proof: a point of `β` on the Jordan right side of `α` is a limit
  of points of the Jordan left side of `β`, so that side meets the right side of `α`; it is connected and contains the
  common reference point `−1 − i`, so it meets the closed curve of `α`, necessarily at a point `α(s)`, `s > 0`, which is
  then on the frozen left side of `β`;
* `range_subset_closedLeftSide_of_liesRightOf`: the same from the strict-side form of the strip carriers.
-/

set_option autoImplicit false

noncomputable section

open Set Filter Topology Metric Complex
open scoped NNReal
open QuantumZipper (H)

namespace InteractingSLE

namespace Sec5

namespace Prop55Half

/-- A simple proper curve from the seed `0`: continuous, injective, at `0` at time `0`, in `ℍ` at every positive
time, tending to `∞` (the flow lines of Remark 4.1's regime, almost surely). -/
def IsSeedProper (γ : ℝ≥0 → ℂ) : Prop :=
  Continuous γ ∧ Function.Injective γ ∧ γ 0 = 0 ∧ (∀ t, 0 < t → γ t ∈ H) ∧
    Tendsto (fun t => ‖γ t‖) atTop atTop

variable {γ α β : ℝ≥0 → ℂ}

theorem IsSeedProper.im_nonneg (hγ : IsSeedProper γ) (t : ℝ≥0) : 0 ≤ (γ t).im := by
  rcases eq_zero_or_pos t with ht | ht
  · rw [ht, hγ.2.2.1]; simp
  · exact le_of_lt (hγ.2.2.2.1 t ht)

theorem IsSeedProper.im_zero (hγ : IsSeedProper γ) : (γ 0).im = 0 := by
  rw [hγ.2.2.1]; simp

theorem IsSeedProper.isProperCurve (hγ : IsSeedProper γ) : Supp9B.IsProperCurve γ :=
  ⟨hγ.1, hγ.2.1, hγ.im_nonneg, hγ.2.2.2.2⟩

theorem IsSeedProper.isClosed_range (hγ : IsSeedProper γ) : IsClosed (range γ) := by
  rw [← image_univ]; exact Supp9B.isClosed_image hγ.isProperCurve isClosed_univ

/-- A simple proper curve from `0` meets the real axis only at `0`. -/
theorem IsSeedProper.ofReal_notMem_range (hγ : IsSeedProper γ) {x : ℝ} (hx : x ≠ 0) : (x : ℂ) ∉ range γ := by
  rintro ⟨t, ht⟩
  rcases eq_zero_or_pos t with h0 | hpos
  · rw [h0, hγ.2.2.1] at ht
    exact hx (by exact_mod_cast ht.symm)
  · have hH : 0 < (γ t).im := hγ.2.2.2.1 t hpos
    rw [ht] at hH
    simp at hH

/-! ### `ℍ` minus the closed curve -/

/-- The points of the seed-ray closure in `ℍ` are points of the curve. -/
theorem mem_range_of_mem_seedRayClosure (hγ0 : (γ 0).im = 0) {z : ℂ} (hz : z ∈ seedRayClosure γ)
    (hzH : z ∈ H) : z ∈ range γ := by
  rcases hz with hz | ⟨-, hzim⟩
  · exact hz
  · exfalso
    have h : 0 < z.im := hzH
    rw [hγ0] at hzim
    linarith

theorem H_diff_seedRayClosure (hγ0 : (γ 0).im = 0) : H \ seedRayClosure γ = H \ range γ := by
  ext z
  exact ⟨fun hz => ⟨hz.1, fun h => hz.2 (Or.inl h)⟩,
    fun hz => ⟨hz.1, fun h => hz.2 (mem_range_of_mem_seedRayClosure hγ0 h hz.1)⟩⟩

/-! ### First exit from `ℍ` -/

/-- **First exit from `ℍ` along a path.** If a point `z ∈ ℍ` and a point `w` of the open lower half-plane are joined
by a path in a set `U` off a set `S`, then some real point of `U` is in the closure of the component of `z` in
`ℍ \ S` (the first point of the path on `ℝ`). -/
theorem exists_ofReal_mem_closure_of_joinedIn {S U : Set ℂ} {z w : ℂ} (hz : z ∈ H) (hw : w.im < 0)
    (hUS : U ⊆ Sᶜ) (hJ : JoinedIn U z w) :
    ∃ x : ℝ, (x : ℂ) ∈ U ∧ (x : ℂ) ∈ closure (connectedComponentIn (H \ S) z) := by
  set p := hJ.somePath with hp
  set g : ℝ → ℂ := ⇑p.extend with hg
  have hgc : Continuous g := p.continuous_extend
  have hgU : ∀ s, g s ∈ U := fun s => by
    have hs : g s ∈ range p := by rw [← p.extend_range]; exact mem_range_self s
    obtain ⟨t, ht⟩ := hs
    rw [← ht]
    exact hJ.somePath_mem t
  have hg0 : g 0 = z := p.extend_zero
  have hg1 : g 1 = w := p.extend_one
  set T : Set ℝ := Icc 0 1 ∩ {s | (g s).im ≤ 0} with hT
  have hTc : IsClosed T := isClosed_Icc.inter (isClosed_le (continuous_im.comp hgc) continuous_const)
  have h1T : (1 : ℝ) ∈ T := ⟨⟨zero_le_one, le_rfl⟩, by show (g 1).im ≤ 0; rw [hg1]; exact hw.le⟩
  have hTb : BddBelow T := ⟨0, fun s hs => hs.1.1⟩
  set s₀ := sInf T with hs₀
  have hs₀T : s₀ ∈ T := hTc.csInf_mem ⟨1, h1T⟩ hTb
  have hpos : ∀ u, 0 ≤ u → u < s₀ → 0 < (g u).im := fun u hu0 hus => by
    by_contra hneg
    have huT : u ∈ T := ⟨⟨hu0, (hus.trans_le hs₀T.1.2).le⟩, not_lt.1 hneg⟩
    exact absurd (csInf_le hTb huT) (not_le.2 hus)
  have hs₀pos : 0 < s₀ := by
    rcases (hs₀T.1.1).lt_or_eq with h | h
    · exact h
    · exfalso
      have h' : (g 0).im ≤ 0 := by
        have h'' := hs₀T.2
        rw [← h] at h''
        exact h''
      rw [hg0] at h'
      exact absurd (show 0 < z.im from hz) (not_lt.2 h')
  have hcl : g s₀ ∈ closure (g '' Ico 0 s₀) := by
    have hmem : s₀ ∈ closure (Ico 0 s₀) := by
      rw [closure_Ico hs₀pos.ne]
      exact ⟨hs₀pos.le, le_rfl⟩
    exact image_closure_subset_closure_image hgc ⟨s₀, hmem, rfl⟩
  have him0 : (g s₀).im = 0 := by
    refine le_antisymm hs₀T.2 ?_
    have hsub : g '' Ico 0 s₀ ⊆ {v : ℂ | 0 ≤ v.im} := by
      rintro _ ⟨u, hu, rfl⟩
      exact (hpos u hu.1 hu.2).le
    exact closure_minimal hsub (isClosed_le continuous_const continuous_im) hcl
  have hre : ((g s₀).re : ℂ) = g s₀ := Complex.ext (by simp) (by simp [him0])
  refine ⟨(g s₀).re, ?_, ?_⟩
  · rw [hre]
    exact hgU s₀
  · rw [hre]
    refine closure_mono ?_ hcl
    refine (isPreconnected_Ico.image g hgc.continuousOn).subset_connectedComponentIn
      ⟨0, ⟨le_rfl, hs₀pos⟩, hg0⟩ ?_
    rintro _ ⟨u, hu, rfl⟩
    exact ⟨hpos u hu.1 hu.2, hUS (hgU u)⟩

/-! ### The Jordan sides of a simple proper curve from `0` and its frozen sides -/

/-- A real point to the right of the seed and off the closed curve is on the Jordan right side (mirror of
`Supp9B.ofReal_mem_leftSide`). -/
theorem ofReal_mem_rightSide (hγ : ∀ t, 0 ≤ (γ t).im) (h0 : (γ 0).im = 0) {x : ℝ}
    (hx : (γ 0).re < x) (hxγ : (x : ℂ) ∉ seedRayClosure γ) : (x : ℂ) ∈ Supp9B.rightSide γ := by
  have hcl : (x : ℂ) ∈ closure (Supp9B.lowerRight (γ 0).re) := by
    have ht : Tendsto (fun s : ℝ => (x : ℂ) - (s : ℂ) * I) (𝓝[>] 0) (𝓝 (x : ℂ)) := by
      have hc : Continuous (fun s : ℝ => (x : ℂ) - (s : ℂ) * I) := by fun_prop
      simpa using (hc.tendsto 0).mono_left nhdsWithin_le_nhds
    refine mem_closure_of_tendsto ht ?_
    filter_upwards [self_mem_nhdsWithin] with s hs
    constructor <;> simp [hx, show (0 : ℝ) < s from hs]
  have hpc : IsPreconnected (insert (x : ℂ) (Supp9B.lowerRight (γ 0).re)) :=
    (Supp9B.convex_lowerRight _).isPreconnected.subset_closure (subset_insert _ _)
      (insert_subset hcl subset_closure)
  exact hpc.subset_connectedComponentIn (mem_insert_of_mem _ (Supp9B.right_ref_mem_lowerRight h0))
    (insert_subset hxγ (Supp9B.lowerRight_subset_compl hγ)) (mem_insert _ _)

theorem isOpen_leftSide (hγ : IsSeedProper γ) : IsOpen (Supp9B.leftSide γ) :=
  (Supp9B.isClosed_seedRayClosure hγ.isProperCurve).isOpen_compl.connectedComponentIn

theorem isOpen_rightSide (hγ : IsSeedProper γ) : IsOpen (Supp9B.rightSide γ) :=
  (Supp9B.isClosed_seedRayClosure hγ.isProperCurve).isOpen_compl.connectedComponentIn

/-- Every point of the Jordan left side is joined to the reference point `γ(0) − 1 − i` inside it. -/
theorem joinedIn_leftSide (hγ : IsSeedProper γ) {z : ℂ} (hz : z ∈ Supp9B.leftSide γ) :
    JoinedIn (Supp9B.leftSide γ) z (γ 0 - 1 - I) := by
  have href := Supp9B.leftRef_mem_leftSide hγ.im_nonneg hγ.im_zero
  have hpc : IsPathConnected (Supp9B.leftSide γ) :=
    (isOpen_leftSide hγ).isConnected_iff_isPathConnected.1
      (isConnected_connectedComponentIn_iff.2 (connectedComponentIn_subset _ _ href))
  exact hpc.joinedIn z hz _ href

/-- **A point of `ℍ` on the Jordan left side of a simple proper curve from `0` is on its frozen left side.** The
first exit from `ℍ` of a path to `γ(0) − 1 − i` inside the Jordan left side is a real point `x` of that side, so
`x ≠ 0`, `x` is off the curve, and `x < 0` (a positive `x` would be on the Jordan right side). -/
theorem mem_leftSideOf_of_mem_leftSide (hγ : IsSeedProper γ) {z : ℂ} (hzH : z ∈ H)
    (hzL : z ∈ Supp9B.leftSide γ) : z ∈ leftSideOf (range γ) := by
  have h0 := hγ.im_zero
  have hw : (γ 0 - 1 - I).im < 0 := by simp [h0]
  obtain ⟨x, hxL, hxcl⟩ := exists_ofReal_mem_closure_of_joinedIn (S := seedRayClosure γ) hzH hw
    (connectedComponentIn_subset _ _) (joinedIn_leftSide hγ hzL)
  have hxS : (x : ℂ) ∉ seedRayClosure γ := connectedComponentIn_subset _ _ hxL
  have hx0 : x < 0 := by
    rcases lt_trichotomy x 0 with h | h | h
    · exact h
    · exfalso
      apply hxS
      left
      exact ⟨0, by rw [hγ.2.2.1, h]; simp⟩
    · exfalso
      have hR := ofReal_mem_rightSide hγ.im_nonneg h0 (by rw [hγ.2.2.1]; simpa using h) hxS
      exact Set.disjoint_left.1 (Supp9B.disjoint_leftSide_rightSide hγ.isProperCurve h0) hxL hR
  refine ⟨⟨hzH, fun h => connectedComponentIn_subset _ _ hzL (Or.inl h)⟩, x, hx0,
    fun h => hxS (Or.inl h), ?_⟩
  rwa [← H_diff_seedRayClosure h0]

/-! ### Frozen sides and strip sides -/

/-- **For a closed set off the negative real axis, the frozen left side is the strip left side**: a component of
`ℍ \ A` reaching some `x < 0` off `A` also reaches `−1/2 ∈ (−1, 0)`, through a thin rectangle above `[x − 1, −1/2]`. -/
theorem leftSideOf_subset_stripLeftSide {A : Set ℂ} (hA : IsClosed A)
    (hAℝ : ∀ x : ℝ, x < 0 → (x : ℂ) ∉ A) : leftSideOf A ⊆ stripLeftSide A := by
  rintro z ⟨hzA, x, hx0, hxA, hxcl⟩
  by_cases hx1 : -1 < x
  · exact ⟨hzA, x, ⟨hx1, hx0⟩, hxA, hxcl⟩
  rw [not_lt] at hx1
  refine ⟨hzA, -1 / 2, ⟨by norm_num, by norm_num⟩, hAℝ _ (by norm_num), ?_⟩
  set C := connectedComponentIn (H \ A) z with hC
  set Iseg : Set ℂ := (fun s : ℝ => (s : ℂ)) '' Icc (x - 1) (-1 / 2) with hIseg
  have hIc : IsCompact Iseg := isCompact_Icc.image continuous_ofReal
  have hIA : Iseg ⊆ Aᶜ := by
    rintro _ ⟨s, hs, rfl⟩
    exact hAℝ s (by linarith [hs.2])
  obtain ⟨δ, hδ, hsub⟩ := hIc.exists_thickening_subset_open hA.isOpen_compl hIA
  set δ' := min δ (1 / 2) with hδ'
  have hδ'pos : 0 < δ' := lt_min hδ (by norm_num)
  set R : Set ℂ := {v | x - 1 ≤ v.re} ∩ {v | v.re ≤ -1 / 2} ∩ {v | 0 < v.im} ∩ {v | v.im < δ'} with hR
  have hRc : Convex ℝ R :=
    (((convex_halfSpace_re_ge _).inter (convex_halfSpace_re_le _)).inter (convex_halfSpace_im_gt _)).inter
      (convex_halfSpace_im_lt _)
  have hRsub : R ⊆ H \ A := by
    rintro v ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩
    refine ⟨h3, fun hvA => ?_⟩
    have hvI : (v.re : ℂ) ∈ Iseg := ⟨v.re, ⟨h1, h2⟩, rfl⟩
    have hvt : v ∈ thickening δ Iseg := by
      rw [mem_thickening_iff]
      refine ⟨_, hvI, ?_⟩
      rw [Complex.dist_eq]
      have he : v - (v.re : ℂ) = (v.im : ℂ) * I := by
        apply Complex.ext <;> simp
      rw [he, norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos (show (0 : ℝ) < v.im from h3)]
      exact h4.trans_le (min_le_left _ _)
    exact hsub hvt hvA
  -- a point of `C` in the rectangle, near `x`
  obtain ⟨c, hcC, hcx⟩ := Metric.mem_closure_iff.1 hxcl δ' hδ'pos
  have hcH : 0 < c.im := (connectedComponentIn_subset _ _ hcC).1
  have hre : |c.re - x| < δ' := by
    have h1 := Complex.abs_re_le_norm (c - x)
    rw [dist_comm, Complex.dist_eq] at hcx
    simp only [Complex.sub_re, Complex.ofReal_re] at h1
    linarith
  have him : c.im < δ' := by
    have h1 := Complex.abs_im_le_norm (c - x)
    rw [dist_comm, Complex.dist_eq] at hcx
    simp only [Complex.sub_im, Complex.ofReal_im, sub_zero] at h1
    linarith [le_abs_self c.im]
  have hcR : c ∈ R := by
    have hδ'h : δ' ≤ 1 / 2 := min_le_right _ _
    refine ⟨⟨⟨?_, ?_⟩, hcH⟩, him⟩
    · show x - 1 ≤ c.re
      linarith [neg_abs_le (c.re - x)]
    · show c.re ≤ -1 / 2
      linarith [le_abs_self (c.re - x)]
  have hRC : R ⊆ C := by
    have h := hRc.isPreconnected.subset_connectedComponentIn hcR hRsub
    rwa [← connectedComponentIn_eq hcC] at h
  -- `−1/2` is a limit of points of the rectangle
  have hlim : Tendsto (fun s : ℝ => ((-1 / 2 : ℝ) : ℂ) + (s : ℂ) * I) (𝓝[>] 0) (𝓝 ((-1 / 2 : ℝ) : ℂ)) := by
    have hc : Continuous (fun s : ℝ => ((-1 / 2 : ℝ) : ℂ) + (s : ℂ) * I) := by fun_prop
    simpa using (hc.tendsto 0).mono_left nhdsWithin_le_nhds
  have hev : ∀ᶠ s : ℝ in 𝓝[>] (0 : ℝ), ((-1 / 2 : ℝ) : ℂ) + (s : ℂ) * I ∈ C := by
    filter_upwards [Ioo_mem_nhdsGT hδ'pos] with s hs
    refine hRC ⟨⟨⟨?_, ?_⟩, ?_⟩, ?_⟩
    · show x - 1 ≤ (((-1 / 2 : ℝ) : ℂ) + (s : ℂ) * I).re
      simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re, Complex.ofReal_im,
        Complex.I_im, mul_zero, zero_mul, sub_zero, add_zero]
      linarith
    · show (((-1 / 2 : ℝ) : ℂ) + (s : ℂ) * I).re ≤ -1 / 2
      simp
    · show 0 < (((-1 / 2 : ℝ) : ℂ) + (s : ℂ) * I).im
      simpa using hs.1
    · show (((-1 / 2 : ℝ) : ℂ) + (s : ℂ) * I).im < δ'
      simpa using hs.2
  have hmem := mem_closure_of_tendsto hlim hev
  exact_mod_cast hmem

/-- For a simple proper curve from `0`, the strict-side order of the strip carriers gives the frozen one. -/
theorem disjoint_leftSideOf_of_liesRightOf (hβ : IsSeedProper β) {K : Set ℂ} (h : LiesRightOf K (range β)) :
    Disjoint K (leftSideOf (range β)) :=
  h.mono_right (leftSideOf_subset_stripLeftSide hβ.isClosed_range fun _ hx => hβ.ofReal_notMem_range hx.ne)

/-! ### The dual order -/

/-- **The dual order.** Let `α`, `β` be simple proper curves from `0`. If no point of `α` is on the frozen left side
of `β`, then `β` lies in the closed left side of `α` (the frozen W0 order). -/
theorem range_subset_closedLeftSide_of_disjoint (hα : IsSeedProper α) (hβ : IsSeedProper β)
    (hd : Disjoint (range α) (leftSideOf (range β))) : range β ⊆ closedLeftSide α := by
  have hα0 := hα.im_zero
  have hβ0 := hβ.im_zero
  rintro _ ⟨t, rfl⟩
  by_contra hnot
  rw [Supp9B.closedLeftSide_eq] at hnot
  have hnS : β t ∉ seedRayClosure α := fun h => hnot (Or.inr h)
  have hnL : β t ∉ Supp9B.leftSide α := fun h => hnot (Or.inl h)
  have hR : β t ∈ Supp9B.rightSide α := by
    have h : β t ∈ (seedRayClosure α)ᶜ := hnS
    rw [Supp9B.compl_seedRayClosure_eq hα.isProperCurve hα0] at h
    exact h.resolve_left hnL
  -- `β t` is a limit of points of the Jordan left side of `β`
  have hcl : β t ∈ closure (Supp9B.leftSide β) :=
    Supp9B.seedRayClosure_subset_closure_leftSide hβ.isProperCurve hβ0 (Or.inl ⟨t, rfl⟩)
  obtain ⟨w, hwR, hwL⟩ := mem_closure_iff.1 hcl _ (isOpen_rightSide hα) hR
  by_cases hmeet : (Supp9B.leftSide β ∩ seedRayClosure α).Nonempty
  · obtain ⟨u, huL, huS⟩ := hmeet
    have huSβ : u ∉ seedRayClosure β := connectedComponentIn_subset _ _ huL
    rcases huS with ⟨s, rfl⟩ | ⟨hre, him⟩
    · rcases eq_zero_or_pos s with hs | hs
      · apply huSβ
        left
        exact ⟨0, by rw [hs, hα.2.2.1, hβ.2.2.1]⟩
      · exact Set.disjoint_left.1 hd ⟨s, rfl⟩
          (mem_leftSideOf_of_mem_leftSide hβ (hα.2.2.2.1 s hs) huL)
    · apply huSβ
      right
      rw [hα.2.2.1] at hre him
      rw [hβ.2.2.1]
      exact ⟨hre, him⟩
  · have hb : β 0 - 1 - I = α 0 - 1 - I := by rw [hα.2.2.1, hβ.2.2.1]
    have hsub : Supp9B.leftSide β ⊆ Supp9B.leftSide α := by
      have href := Supp9B.leftRef_mem_leftSide hβ.im_nonneg hβ0
      rw [hb] at href
      exact isPreconnected_connectedComponentIn.subset_connectedComponentIn href
        fun v hv hvS => hmeet ⟨v, hv, hvS⟩
    exact Set.disjoint_left.1 (Supp9B.disjoint_leftSide_rightSide hα.isProperCurve hα0) (hsub hwL) hwR

/-- **Proposition 5.5's order, frozen form, from the strict-side form**: for simple proper curves `α = η_{θ₁}`,
`β = η_{θ₂}` from `0`, if no point of `α` is strictly on the (strip) left of `β`, then `β` lies in the closed left
side of `α`. -/
theorem range_subset_closedLeftSide_of_liesRightOf (hα : IsSeedProper α) (hβ : IsSeedProper β)
    (h : LiesRightOf (range α) (range β)) : range β ⊆ closedLeftSide α :=
  range_subset_closedLeftSide_of_disjoint hα hβ (disjoint_leftSideOf_of_liesRightOf hβ h)

/-- The whole curve from its prefixes: if `η([0, n])` lies to the right of `A` for every `n`, so does `η`. -/
theorem liesRightOf_range_of_forall_image_Iic {η : ℝ≥0 → ℂ} {A : Set ℂ}
    (h : ∀ n : ℕ, LiesRightOf (η '' Iic (n : ℝ≥0)) A) : LiesRightOf (range η) A := by
  rw [LiesRightOf, Set.disjoint_left]
  rintro _ ⟨t, rfl⟩
  obtain ⟨n, hn⟩ := exists_nat_ge t
  exact Set.disjoint_left.1 (h n) ⟨t, hn, rfl⟩

end Prop55Half

end Sec5

end InteractingSLE
