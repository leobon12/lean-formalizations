/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.RLCGlue

/-!
# The planar gluing of the stopped reference tangle across genuine original-real contacts

Packet PROVE-RLC-C. Source: "Planar gluing of the stopped reference tangle" (`source/spec/p481-528.md` L527–L535,
pp. 502–503): "Suppose the stopped tangle in that chart admits the completions just supplied by G9–G10, and every real
point fixed by G10 other than its seeds maps to a genuine original-real point outside the retained old range. Map those
completions back and append them to the old histories. They are proper injective extensions: the added tails avoid the
old range, and their only real contacts are the allowed ones. […] The Jordan separation theorem now puts the entire
second completed curve on the closed left side of the first"; and the order part of Lemma G9's proof (p. 502: "Its
real points belong to the closed left side by continuity from its interior points").

PROVE-RLC-A proved the gluing when the chart completions stay in `ℍ` after their seeds
(`RLC.hasOrderedProperCompletions_glue`), using that the left side of such a curve meets `ℍ` in a connected set. With
real contacts this fails (the chart curve cuts pockets off its left side; PROVE-RLC-A's obstacle (a)). Here the chart
completions may have real points after their seeds, in a set `E` of chart real points whose `ψ`-images are genuine
original-real points off the retained union, `ψ` being injective on `E`. The order check replaces connectivity by an
argument along the chart real line (`image_side_subset`): a chart side component which `ψ` sent to the wrong physical
side would reach, along a real interval free of the chart curve, either the other chart seed or a real contact of the
chart curve; just beside that contact the chart real points are in `E`, and their images are physical real points on
the known side of the physical seed. Two mirror forms are used: if the images of `E` lie left of the first physical
seed, through the left side of the first chart curve; if they lie right of the second physical seed, through the right
side of the second chart curve (`Supp9B.range_subset_closedLeftSide_of_closedRightSide` converts back).

## Main results

* `image_side_subset`: side transfer through the chart along the real line (abstract form).
* `glue_side_real`: one glued curve, chart completion with real points in `E`.
* `hasOrderedProperCompletions_glue_real`: **the planar gluing across genuine original-real contacts**.
-/

set_option autoImplicit false

noncomputable section

open Set Filter Topology Metric Complex
open scoped NNReal

open QuantumZipper (H Hbar)

namespace InteractingSLE

namespace RLC

open Supp9B

/-! ### Side transfer along the real line -/

section Core

variable {γ : ℝ≥0 → ℂ} {ψ : ℂ → ℂ} {Sc S1 S2 : Set ℂ} {E Ir : Set ℝ}

theorem convex_H : Convex ℝ H := convex_halfSpace_gt Complex.imLm.isLinear 0

/-- A map continuous on `ℍ̄` is continuous at every point of `ℍ`. -/
theorem continuousAt_of_mem_H (hψc : ContinuousOn ψ Hbar) {z : ℂ} (hz : z ∈ H) : ContinuousAt ψ z :=
  hψc.continuousAt (mem_of_superset (QuantumZipper.isOpen_H.mem_nhds hz) fun w hw =>
    show (0 : ℝ) ≤ w.im from le_of_lt hw)

/-- A real point with imaginary part `0`. -/
theorem eq_ofReal_re_of_im_eq_zero {z : ℂ} (hz : z.im = 0) : z = (z.re : ℂ) :=
  Complex.ext (by simp) (by simp [hz])

/-- The point `y + iε/2` is in `ℍ` and within `ε` of the real point `y`. -/
theorem shift_mem_H {y ε : ℝ} (hε : 0 < ε) : (y : ℂ) + ((ε / 2 : ℝ) : ℂ) * I ∈ H ∧
    dist ((y : ℂ) + ((ε / 2 : ℝ) : ℂ) * I) y < ε := by
  refine ⟨show (0 : ℝ) < ((y : ℂ) + ((ε / 2 : ℝ) : ℂ) * I).im by simp; linarith, ?_⟩
  rw [Complex.dist_eq, add_sub_cancel_left, norm_mul, Complex.norm_I, mul_one, Complex.norm_real,
    Real.norm_eq_abs, abs_of_pos (half_pos hε)]
  exact half_lt_self hε

/-- **Side transfer through a chart along the real line.** Let `Sc` be one side of a proper chart curve `γ` from a
real seed (open, preconnected, reaching below `ℝ`, off `γ`), whose real points are exactly the real points of an
order-connected set `Ir` (not containing the seed) off `γ`. Let `ψ` be continuous on `ℍ̄` and send `Sc ∩ ℍ` into the
union of two disjoint open sets `S1`, `S2`. Suppose `ψ` sends a real point `z₀ ∈ Ir` into `S1`, every real
point of `γ` after its seed lies in an open set `E` of reals, and `ψ` sends every point of `E ∩ Ir` off `γ` into `S1`.
Then `ψ` sends all of `Sc ∩ ℍ` into `S1`. -/
theorem image_side_subset (hγ : IsProperCurve γ) (hSo : IsOpen Sc) (hSp : IsPreconnected Sc)
    (hSlow : ∃ z ∈ Sc, z.im < 0) (hSγ : ∀ z ∈ Sc, z ∉ range γ) (hI : Ir.OrdConnected) (hIγ : (γ 0).re ∉ Ir)
    (hSI : ∀ y : ℝ, (y : ℂ) ∈ Sc → y ∈ Ir) (hIS : ∀ y ∈ Ir, (y : ℂ) ∉ range γ → (y : ℂ) ∈ Sc)
    (hS1 : IsOpen S1) (hS2 : IsOpen S2) (hS12 : Disjoint S1 S2) (hψc : ContinuousOn ψ Hbar)
    (hψS : ∀ z ∈ Sc, z ∈ H → ψ z ∈ S1 ∪ S2) {z₀ : ℝ} (hz₀I : z₀ ∈ Ir) (hz₀ : ψ z₀ ∈ S1) (hEo : IsOpen E)
    (hγE : ∀ t, 0 < t → (γ t).im = 0 → (γ t).re ∈ E)
    (hES : ∀ y ∈ E, y ∈ Ir → (y : ℂ) ∉ range γ → ψ y ∈ S1) :
    ∀ z ∈ Sc, z ∈ H → ψ z ∈ S1 := by
  set B : Set ℂ := {z | z ∈ Sc ∧ z ∈ H ∧ ψ z ∈ S2} with hB
  have hrange : IsClosed (range γ) := by
    rw [← image_univ]; exact isClosed_image hγ isClosed_univ
  -- `B` is open
  have hBo : IsOpen B := by
    rw [isOpen_iff_mem_nhds]
    rintro z ⟨hzS, hzH, hz2⟩
    filter_upwards [hSo.mem_nhds hzS, QuantumZipper.isOpen_H.mem_nhds hzH,
      (continuousAt_of_mem_H hψc hzH).preimage_mem_nhds (hS2.mem_nhds hz2)] with z' h1 h2 h3
    exact ⟨h1, h2, h3⟩
  have hBH : closure B ⊆ Hbar :=
    closure_minimal (fun z hz => show (0 : ℝ) ≤ z.im from le_of_lt hz.2.1) QuantumZipper.isClosed_Hbar
  -- a point of `ℍ̄` sent into `S1` has a neighbourhood in `ℍ` off `B`
  have hgood : ∀ y : ℂ, y ∈ Hbar → ψ y ∈ S1 → ∃ ε > 0, ∀ z ∈ H, dist z y < ε → z ∉ B := by
    intro y hy h1
    obtain ⟨ρ, hρ, hρ1⟩ := Metric.isOpen_iff.1 hS1 _ h1
    obtain ⟨δ, hδ, hδψ⟩ := Metric.continuousWithinAt_iff.1 (hψc y hy) ρ hρ
    exact ⟨δ, hδ, fun z hz hzy hzB =>
      Set.disjoint_left.1 hS12 (hρ1 (hδψ (show (0 : ℝ) ≤ z.im from le_of_lt hz) hzy)) hzB.2.2⟩
  -- near a real point of `Sc` adherent to `B`, all of `ℍ` is in `B`
  have hloc : ∀ y : ℝ, (y : ℂ) ∈ Sc → (y : ℂ) ∈ closure B →
      ∃ ε > 0, ∀ z ∈ H, dist z y < ε → z ∈ B := by
    intro y hyS hyB
    obtain ⟨ε, hε, hεS⟩ := Metric.isOpen_iff.1 hSo _ hyS
    obtain ⟨z₁, hz₁B, hz₁y⟩ := Metric.mem_closure_iff.1 hyB ε hε
    have hU : IsPreconnected (ψ '' (ball (y : ℂ) ε ∩ H)) :=
      ((convex_ball _ _).inter convex_H).isPreconnected.image ψ
        (hψc.mono fun z hz => le_of_lt (show (0 : ℝ) < z.im from hz.2))
    have hsub : ψ '' (ball (y : ℂ) ε ∩ H) ⊆ S1 ∪ S2 := by
      rintro _ ⟨z, hz, rfl⟩; exact hψS z (hεS hz.1) hz.2
    have hz₁U : z₁ ∈ ball (y : ℂ) ε ∩ H := ⟨by rw [mem_ball, dist_comm]; exact hz₁y, hz₁B.2.1⟩
    have h2 := hU.subset_right_of_subset_union hS1 hS2 hS12 hsub ⟨_, ⟨z₁, hz₁U, rfl⟩, hz₁B.2.2⟩
    exact ⟨ε, hε, fun z hz hzy => ⟨hεS (mem_ball.2 hzy), hz, h2 ⟨z, ⟨mem_ball.2 hzy, hz⟩, rfl⟩⟩⟩
  -- no real point of `Sc` is adherent to `B`
  have hreal : ∀ x : ℝ, (x : ℂ) ∈ Sc → (x : ℂ) ∉ closure B := by
    intro x hxS hxB
    have hxI := hSI x hxS
    have hxγ := hSγ _ hxS
    -- a good point `g`, joined to `x` by a real segment in `I` off `γ`
    obtain ⟨g, hgseg, hgS1⟩ : ∃ g : ℝ, (∀ y ∈ uIcc x g, y ∈ Ir ∧ (y : ℂ) ∉ range γ) ∧ ψ g ∈ S1 := by
      by_cases hseg : ∀ y ∈ uIcc x z₀, (y : ℂ) ∉ range γ
      · exact ⟨z₀, fun y hy => ⟨hI.uIcc_subset hxI hz₀I hy, hseg y hy⟩, hz₀⟩
      push Not at hseg
      obtain ⟨k, hk, hkγ⟩ := hseg
      -- the contact closest to `x` is in `E`, and so is a point just before it
      have hcontact : ∀ y ∈ uIcc x z₀, (y : ℂ) ∈ range γ → y ∈ E := by
        intro y hy hyγ
        obtain ⟨t, ht⟩ := hyγ
        have ht0 : 0 < t := by
          refine pos_iff_ne_zero.2 fun h0 => hIγ ?_
          rw [← h0, ht]; simpa using hI.uIcc_subset hxI hz₀I hy
        have := hγE t ht0 (by rw [ht]; simp)
        rwa [ht, ofReal_re] at this
      rcases le_total x z₀ with hxz | hzx
      · set K : Set ℝ := Icc x z₀ ∩ {y | (y : ℂ) ∈ range γ} with hK
        have hKc : IsClosed K := isClosed_Icc.inter (hrange.preimage continuous_ofReal)
        have hkK : k ∈ K := ⟨by rwa [uIcc_of_le hxz] at hk, hkγ⟩
        have hKb : BddBelow K := ⟨x, fun y hy => hy.1.1⟩
        set y₀ := sInf K with hy₀
        have hy₀K : y₀ ∈ K := hKc.csInf_mem ⟨k, hkK⟩ hKb
        have hxy₀ : x < y₀ := lt_of_le_of_ne hy₀K.1.1 fun h => hxγ (h ▸ hy₀K.2)
        have hy₀E : y₀ ∈ E := hcontact y₀ (by rw [uIcc_of_le hxz]; exact hy₀K.1) hy₀K.2
        obtain ⟨ε, hε, hεE⟩ := Metric.isOpen_iff.1 hEo y₀ hy₀E
        set g := max x (y₀ - ε / 2) with hg
        have hgy₀ : g < y₀ := max_lt hxy₀ (by linarith)
        have hxg : x ≤ g := le_max_left _ _
        have hseg' : ∀ y ∈ uIcc x g, y ∈ Ir ∧ (y : ℂ) ∉ range γ := by
          intro y hy
          rw [uIcc_of_le hxg] at hy
          have hyz : y ∈ uIcc x z₀ := by
            rw [uIcc_of_le hxz]; exact ⟨hy.1, (hy.2.trans hgy₀.le).trans hy₀K.1.2⟩
          refine ⟨hI.uIcc_subset hxI hz₀I hyz, fun hyγ => ?_⟩
          have : y₀ ≤ y := csInf_le hKb ⟨by rwa [uIcc_of_le hxz] at hyz, hyγ⟩
          linarith [hy.2]
        have hgE : g ∈ E := hεE (by
          rw [mem_ball, Real.dist_eq, abs_lt]
          constructor <;> [skip; linarith]
          have : y₀ - ε / 2 ≤ g := le_max_right _ _
          linarith)
        exact ⟨g, hseg', hES g hgE (hseg' g right_mem_uIcc).1 (hseg' g right_mem_uIcc).2⟩
      · set K : Set ℝ := Icc z₀ x ∩ {y | (y : ℂ) ∈ range γ} with hK
        have hKc : IsClosed K := isClosed_Icc.inter (hrange.preimage continuous_ofReal)
        have hkK : k ∈ K := ⟨by rwa [uIcc_of_ge hzx] at hk, hkγ⟩
        have hKb : BddAbove K := ⟨x, fun y hy => hy.1.2⟩
        set y₀ := sSup K with hy₀
        have hy₀K : y₀ ∈ K := hKc.csSup_mem ⟨k, hkK⟩ hKb
        have hxy₀ : y₀ < x := lt_of_le_of_ne hy₀K.1.2 fun h => hxγ (h ▸ hy₀K.2)
        have hy₀E : y₀ ∈ E := hcontact y₀ (by rw [uIcc_of_ge hzx]; exact hy₀K.1) hy₀K.2
        obtain ⟨ε, hε, hεE⟩ := Metric.isOpen_iff.1 hEo y₀ hy₀E
        set g := min x (y₀ + ε / 2) with hg
        have hgy₀ : y₀ < g := lt_min hxy₀ (by linarith)
        have hxg : g ≤ x := min_le_left _ _
        have hseg' : ∀ y ∈ uIcc x g, y ∈ Ir ∧ (y : ℂ) ∉ range γ := by
          intro y hy
          rw [uIcc_of_ge hxg] at hy
          have hyz : y ∈ uIcc x z₀ := by
            rw [uIcc_of_ge hzx]; exact ⟨hy₀K.1.1.trans (hgy₀.le.trans hy.1), hy.2⟩
          refine ⟨hI.uIcc_subset hxI hz₀I hyz, fun hyγ => ?_⟩
          have : y ≤ y₀ := le_csSup hKb ⟨by rwa [uIcc_of_ge hzx] at hyz, hyγ⟩
          linarith [hy.1]
        have hgE : g ∈ E := hεE (by
          rw [mem_ball, Real.dist_eq, abs_lt]
          constructor <;> [linarith; skip]
          have : g ≤ y₀ + ε / 2 := min_le_right _ _
          linarith)
        exact ⟨g, hseg', hES g hgE (hseg' g right_mem_uIcc).1 (hseg' g right_mem_uIcc).2⟩
    -- the cover of the segment
    set U₁ : Set ℝ := {y | ∃ ε > 0, ∀ z ∈ H, dist z y < ε → z ∈ B} with hU₁
    set U₂ : Set ℝ := {y | (y : ℂ) ∉ closure B} with hU₂
    have hU₁o : IsOpen U₁ := by
      rw [Metric.isOpen_iff]
      rintro y ⟨ε, hε, h⟩
      refine ⟨ε / 2, half_pos hε, fun y' hy' => ⟨ε / 2, half_pos hε, fun z hz hzy' => h z hz ?_⟩⟩
      have h1 : dist (y' : ℂ) (y : ℂ) < ε / 2 := by
        rw [Complex.dist_eq, ← ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
        rw [mem_ball, Real.dist_eq] at hy'
        exact hy'
      linarith [dist_triangle z (y' : ℂ) (y : ℂ)]
    have hU₂o : IsOpen U₂ := isClosed_closure.isOpen_compl.preimage continuous_ofReal
    have hU₁cl : ∀ y ∈ U₁, (y : ℂ) ∈ closure B := by
      rintro y ⟨ε, hε, h⟩
      refine Metric.mem_closure_iff.2 fun ε' hε' => ?_
      obtain ⟨hzH, hzd⟩ := shift_mem_H (y := y) (lt_min hε hε')
      exact ⟨_, h _ hzH (hzd.trans_le (min_le_left _ _)), by
        rw [dist_comm]; exact hzd.trans_le (min_le_right _ _)⟩
    have hdisj : Disjoint U₁ U₂ := Set.disjoint_left.2 fun y h1 h2 => h2 (hU₁cl y h1)
    have hcover : uIcc x g ⊆ U₁ ∪ U₂ := by
      intro y hy
      obtain ⟨hyI, hyγ⟩ := hgseg y hy
      by_cases hyB : (y : ℂ) ∈ closure B
      · exact Or.inl (hloc y (hIS y hyI hyγ) hyB)
      · exact Or.inr hyB
    have hgU₁ : g ∈ U₁ := isPreconnected_uIcc.subset_left_of_subset_union hU₁o hU₂o hdisj hcover
      ⟨x, left_mem_uIcc, hloc x hxS hxB⟩ right_mem_uIcc
    obtain ⟨ε₁, hε₁, h₁⟩ := hgU₁
    obtain ⟨ε₂, hε₂, h₂⟩ := hgood (g : ℂ) (show (0 : ℝ) ≤ (g : ℂ).im by simp) hgS1
    obtain ⟨hzH, hzd⟩ := shift_mem_H (y := g) (lt_min hε₁ hε₂)
    exact h₂ _ hzH (hzd.trans_le (min_le_right _ _)) (h₁ _ hzH (hzd.trans_le (min_le_left _ _)))
  -- `B` is closed in `Sc`
  have hclosed : ∀ z ∈ Sc, z ∈ closure B → z ∈ B := by
    intro z hzS hzB
    rcases (show (0 : ℝ) ≤ z.im from hBH hzB).lt_or_eq with hpos | hzero
    · rcases hψS z hzS hpos with h1 | h2
      · exfalso
        obtain ⟨ε, hε, hε'⟩ := hgood z (le_of_lt hpos) h1
        obtain ⟨b, hbB, hbd⟩ := Metric.mem_closure_iff.1 hzB ε hε
        exact hε' b hbB.2.1 (by rw [dist_comm]; exact hbd) hbB
      · exact ⟨hzS, hpos, h2⟩
    · rw [eq_ofReal_re_of_im_eq_zero hzero.symm] at hzS hzB
      exact absurd hzB (hreal _ hzS)
  -- conclusion
  intro z hzS hzH
  rcases hψS z hzS hzH with h1 | h2
  · exact h1
  · exfalso
    have hcov : Sc ⊆ B ∪ (closure B)ᶜ := fun z' hz' => by
      by_cases h : z' ∈ closure B
      · exact Or.inl (hclosed z' hz' h)
      · exact Or.inr h
    have hSB := hSp.subset_left_of_subset_union hBo isClosed_closure.isOpen_compl
      (Set.disjoint_left.2 fun _ h h' => h' (subset_closure h)) hcov ⟨z, hzS, hzS, hzH, h2⟩
    obtain ⟨zl, hzlS, hzl⟩ := hSlow
    exact absurd (show (0 : ℝ) < zl.im from (hSB hzlS).2.1) (not_lt.2 hzl.le)

end Core

/-! ### One glued curve with real chart points -/

section Glue

variable {ψ : ℂ → ℂ} {D A : Set ℂ} {E : Set ℝ}

/-- A chart point allowed on a chart completion after its seed: interior, or real with real part in `E` (the chart
real points over genuine original-real points off the retained union). -/
def IsGluePoint (E : Set ℝ) (z : ℂ) : Prop := z ∈ H ∨ (z.im = 0 ∧ z.re ∈ E)

/-- The chart is injective on allowed points. -/
theorem eq_of_isGluePoint (hDH : D ⊆ H) (hψH : MapsTo ψ H D) (hψi : InjOn ψ H)
    (hEi : ∀ y ∈ E, ∀ y' ∈ E, ψ y = ψ y' → y = y') (hEr : ∀ y ∈ E, (ψ y).im = 0) {z z' : ℂ}
    (hz : IsGluePoint E z) (hz' : IsGluePoint E z') (he : ψ z = ψ z') : z = z' := by
  rcases hz with hz | ⟨hz0, hzE⟩ <;> rcases hz' with hz' | ⟨hz'0, hz'E⟩
  · exact hψi hz hz' he
  · exfalso
    have h1 : (0 : ℝ) < (ψ z).im := hDH (hψH hz)
    have h2 := hEr _ hz'E
    rw [← eq_ofReal_re_of_im_eq_zero hz'0, ← he] at h2
    exact (ne_of_gt h1) h2
  · exfalso
    have h1 : (0 : ℝ) < (ψ z').im := hDH (hψH hz')
    have h2 := hEr _ hzE
    rw [← eq_ofReal_re_of_im_eq_zero hz0, he] at h2
    exact (ne_of_gt h1) h2
  · have h := hEi _ hzE _ hz'E (by
      rw [← eq_ofReal_re_of_im_eq_zero hz0, ← eq_ofReal_re_of_im_eq_zero hz'0]; exact he)
    rw [eq_ofReal_re_of_im_eq_zero hz0, eq_ofReal_re_of_im_eq_zero hz'0, h]

/-- The chart image of an allowed point is off the retained union. -/
theorem notMem_of_isGluePoint (hDA : Disjoint D A) (hψH : MapsTo ψ H D) (hEA : ∀ y ∈ E, ψ y ∉ A) {z : ℂ}
    (hz : IsGluePoint E z) : ψ z ∉ A := by
  rcases hz with hz | ⟨hz0, hzE⟩
  · exact Set.disjoint_left.1 hDA (hψH hz)
  · rw [eq_ofReal_re_of_im_eq_zero hz0]; exact hEA _ hzE

/-- The chart image of an allowed point is in `ℍ̄`. -/
theorem im_nonneg_of_isGluePoint (hDH : D ⊆ H) (hψH : MapsTo ψ H D) (hEr : ∀ y ∈ E, (ψ y).im = 0) {z : ℂ}
    (hz : IsGluePoint E z) : 0 ≤ (ψ z).im := by
  rcases hz with hz | ⟨hz0, hzE⟩
  · exact le_of_lt (hDH (hψH hz))
  · rw [eq_ofReal_re_of_im_eq_zero hz0, hEr _ hzE]

/-- **One glued curve, real chart points allowed.** As `RLC.glue_side`, but the chart completion `γ` may have real
points after time `0`, in the set `E` of chart real points on which `ψ` is injective, real-valued and off `A`. -/
theorem glue_side_real {η g γ : ℝ≥0 → ℂ} {c a s : ℝ≥0} {p : ℂ}
    (hca : c ≤ a) (hc : ContinuousOn η (Icc 0 a)) (hi : InjOn η (Icc 0 a)) (hm : ∀ x ≤ a, 0 ≤ (η x).im)
    (hA : ∀ x ≤ c, η x ∈ A) (hDA : Disjoint D A) (hDH : D ⊆ H) (hψH : MapsTo ψ H D) (hψi : InjOn ψ H)
    (hψc : ContinuousOn ψ Hbar) (hψM : ∃ M : ℝ, ∀ z ∈ Hbar, ‖ψ z - z‖ ≤ M)
    (hEi : ∀ y ∈ E, ∀ y' ∈ E, ψ y = ψ y' → y = y') (hEr : ∀ y ∈ E, (ψ y).im = 0) (hEA : ∀ y ∈ E, ψ y ∉ A)
    (hg0 : g 0 = p) (hψp : ψ p = η c) (hs : 0 < s)
    (himg : η '' Icc c a = (fun t => ψ (g t)) '' Icc 0 s) (hend : ψ (g s) = η a)
    (hγ : IsProperCompletion g s γ) (hR : ∀ t, 0 < t → IsGluePoint E (γ t)) :
    IsProperCompletion η a (junction η (fun t => ψ (γ (s + t))) a 0) ∧
    (∀ t, c < t → ∃ t' > 0, junction η (fun t => ψ (γ (s + t))) a 0 t = ψ (γ t')) ∧
    (∀ t', ψ (γ t') ∈ range (junction η (fun t => ψ (γ (s + t))) a 0)) := by
  set T : ℝ≥0 → ℂ := fun t => ψ (γ (s + t)) with hTdef
  have hγg : ∀ t ≤ s, γ t = g t := hγ.2.2.2.2
  have hγHbar : ∀ t, γ t ∈ Hbar := hγ.2.2.1
  have hsG : ∀ t, IsGluePoint E (γ (s + t)) := fun t => hR _ (lt_of_lt_of_le hs le_self_add)
  have hrep : ∀ x, c < x → x ≤ a → ∃ t' ∈ Ioc 0 s, η x = ψ (γ t') := by
    intro x hcx hxa
    have hmem : η x ∈ (fun t => ψ (g t)) '' Icc 0 s := by
      rw [← himg]; exact mem_image_of_mem η ⟨hcx.le, hxa⟩
    obtain ⟨t', ht', he⟩ := hmem
    have he' : ψ (g t') = η x := he
    have ht'0 : t' ≠ 0 := by
      rintro rfl
      rw [hg0, hψp] at he'
      exact (ne_of_gt hcx) (hi ⟨zero_le, hxa⟩ ⟨zero_le, hca⟩ he'.symm)
    exact ⟨t', ⟨pos_iff_ne_zero.2 ht'0, ht'.2⟩, by rw [← he', hγg t' ht'.2]⟩
  obtain ⟨M, hM⟩ := hψM
  have hTp : IsProperCurve T := by
    refine ⟨?_, ?_, ?_, ?_⟩
    · exact hψc.comp_continuous (hγ.1.comp (continuous_const.add continuous_id)) fun t => hγHbar _
    · intro t t' h
      exact add_left_cancel (hγ.2.1 (eq_of_isGluePoint hDH hψH hψi hEi hEr (hsG t) (hsG t') h))
    · intro t
      exact im_nonneg_of_isGluePoint hDH hψH hEr (hsG t)
    · have hst : Tendsto (fun t : ℝ≥0 => s + t) atTop atTop :=
        tendsto_atTop_atTop.2 fun b => ⟨b, fun t ht => ht.trans le_add_self⟩
      have h1 : Tendsto (fun t => ‖γ (s + t)‖) atTop atTop := hγ.2.2.2.1.comp hst
      refine tendsto_atTop_mono (fun t => ?_) (tendsto_atTop_add_const_right _ (-M) h1)
      have h2 := hM _ (hγHbar (s + t))
      have h3 := norm_sub_norm_le (γ (s + t)) (ψ (γ (s + t)))
      rw [norm_sub_rev] at h3
      show ‖γ (s + t)‖ + -M ≤ ‖ψ (γ (s + t))‖
      linarith
  have hT0 : T 0 = η a := by
    show ψ (γ (s + 0)) = η a
    rw [add_zero, hγg s le_rfl, hend]
  have hdisj : ∀ x < a, ∀ t, η x ≠ T t := by
    intro x hxa t he
    by_cases hxc : x ≤ c
    · have h1 := hA x hxc
      rw [he] at h1
      exact notMem_of_isGluePoint hDA hψH hEA (hsG t) h1
    · obtain ⟨t', ht', he'⟩ := hrep x (not_le.1 hxc) hxa.le
      have h1 : γ t' = γ (s + t) :=
        eq_of_isGluePoint hDH hψH hψi hEi hEr (hR t' ht'.1) (hsG t) (he'.symm.trans he)
      have h2 : t' = s + t := hγ.2.1 h1
      have h3 : t = 0 := by
        have h5 : s + t ≤ s := h2 ▸ ht'.2
        simpa using h5
      have h4 : η x = η a := by rw [he, h3, hT0]
      exact (ne_of_lt hxa) (hi ⟨zero_le, hxa.le⟩ ⟨zero_le, le_rfl⟩ h4)
  have hJ := isProperCompletion_junction_of_prefix hc hi hm hTp hT0 hdisj
  refine ⟨hJ, fun t hct => ?_, fun t' => ?_⟩
  · by_cases hta : t ≤ a
    · obtain ⟨t', ht', he⟩ := hrep t hct hta
      exact ⟨t', ht'.1, by rw [junction_of_le hta, he]⟩
    · refine ⟨s + (t - a), lt_of_lt_of_le hs le_self_add, ?_⟩
      rw [junction_of_lt (not_le.1 hta)]
      simp only [hTdef, zero_add]
  · by_cases hts : t' ≤ s
    · have hmem : ψ (g t') ∈ η '' Icc c a := by rw [himg]; exact ⟨t', ⟨zero_le, hts⟩, rfl⟩
      obtain ⟨x, hx, he⟩ := hmem
      exact ⟨x, by rw [junction_of_le hx.2, he, hγg t' hts]⟩
    · have hst : s < t' := not_le.1 hts
      refine ⟨a + (t' - s), ?_⟩
      rw [junction_of_lt (lt_add_of_pos_right a (tsub_pos_of_lt hst))]
      simp only [hTdef, zero_add, add_tsub_cancel_left, add_tsub_cancel_of_le hst.le]

end Glue

/-! ### The planar gluing across real contacts -/

section Main

/-- A point of the left side of a proper curve from a real seed is off the curve. -/
theorem notMem_range_of_mem_leftSide {γ : ℝ≥0 → ℂ} {z : ℂ} (hz : z ∈ leftSide γ) : z ∉ range γ :=
  fun h => connectedComponentIn_subset _ _ hz (Or.inl h)

theorem notMem_range_of_mem_rightSide {γ : ℝ≥0 → ℂ} {z : ℂ} (hz : z ∈ rightSide γ) : z ∉ range γ :=
  fun h => connectedComponentIn_subset _ _ hz (Or.inl h)

/-- A real point off a proper curve from the real seed `γ 0`, on the seed's left, is on the left side; one on its right
is on the right side. -/
theorem ofReal_mem_leftSide_of_notMem {γ : ℝ≥0 → ℂ} (hγ : IsProperCurve γ) (h0 : (γ 0).im = 0) {y : ℝ}
    (hy : y < (γ 0).re) (hyγ : (y : ℂ) ∉ range γ) : (y : ℂ) ∈ leftSide γ :=
  ofReal_mem_leftSide hγ.2.2.1 h0 hy (by
    rintro (h | ⟨hre, -⟩)
    · exact hyγ h
    · simp only [ofReal_re] at hre; exact (ne_of_lt hy) hre)

theorem ofReal_mem_rightSide_of_notMem {γ : ℝ≥0 → ℂ} (hγ : IsProperCurve γ) (h0 : (γ 0).im = 0) {y : ℝ}
    (hy : (γ 0).re < y) (hyγ : (y : ℂ) ∉ range γ) : (y : ℂ) ∈ rightSide γ :=
  ofReal_mem_rightSide hγ.2.2.1 h0 hy (by
    rintro (h | ⟨hre, -⟩)
    · exact hyγ h
    · simp only [ofReal_re] at hre; exact (ne_of_gt hy) hre)

/-- **The planar gluing of the stopped reference tangle across genuine original-real contacts** (supplement §7.8,
pp. 502–503, with the order part of Lemma G9's proof, p. 502). The data of `RLC.hasOrderedProperCompletions_glue`,
with an abstract joint domain `D ⊆ ℍ` off the retained union `A`, except that the chart completions `γ₁`, `γ₂` may
have real points after their seeds, in an open set `E` of chart real points over genuine original-real points: `ψ` is
injective on `E`, real-valued there and off `A`. The images of `E` all lie left of the first physical seed, or all
right of the second (W5, p. 535: the untouched interval at a real contact is "exterior to both current seed
coordinates, or lies between the two"). The chart completions need not avoid each other's seeds here. -/
theorem hasOrderedProperCompletions_glue_real {η₁ η₂ g₁ g₂ γ₁ γ₂ : ℝ≥0 → ℂ} {ψ : ℂ → ℂ} {D : Set ℂ}
    {E : Set ℝ} {u r a b s₁ s₂ : ℝ≥0} {w : ℝ}
    (hold : HasOrderedProperCompletions η₁ u η₂ r) (h01 : (η₁ 0).im = 0) (h02 : (η₂ 0).im = 0)
    (hseed : (η₂ 0).re ≤ (η₁ 0).re) (hua : u ≤ a) (hrb : r ≤ b)
    (hc₁ : ContinuousOn η₁ (Icc 0 a)) (hi₁ : InjOn η₁ (Icc 0 a)) (hm₁ : ∀ x ≤ a, 0 ≤ (η₁ x).im)
    (hc₂ : ContinuousOn η₂ (Icc 0 b)) (hi₂ : InjOn η₂ (Icc 0 b)) (hm₂ : ∀ y ≤ b, 0 ≤ (η₂ y).im)
    (htip₁ : η₁ u ∈ H) (htip₂ : η₂ r ∈ H) (hp₂ : η₂ r ∉ η₁ '' Icc 0 u) (hp₁ : η₁ u ∉ η₂ '' Icc 0 r)
    (hDH : D ⊆ H) (hDA : Disjoint D (η₁ '' Icc 0 u ∪ η₂ '' Icc 0 r)) (hψH : MapsTo ψ H D)
    (hψi : InjOn ψ H) (hψc : ContinuousOn ψ Hbar) (hψM : ∃ M : ℝ, ∀ z ∈ Hbar, ‖ψ z - z‖ ≤ M)
    (hψ0 : ψ 0 = η₂ r) (hψw : ψ w = η₁ u) (hEo : IsOpen E) (hEi : ∀ y ∈ E, ∀ y' ∈ E, ψ y = ψ y' → y = y')
    (hEr : ∀ y ∈ E, (ψ y).im = 0) (hEA : ∀ y ∈ E, ψ y ∉ η₁ '' Icc 0 u ∪ η₂ '' Icc 0 r)
    (hEside : (∀ y ∈ E, (ψ y).re < (η₁ 0).re) ∨ ∀ y ∈ E, (η₂ 0).re < (ψ y).re)
    (hw : 0 < w) (hg₁0 : g₁ 0 = w) (hg₂0 : g₂ 0 = 0) (hs₁ : 0 < s₁) (hs₂ : 0 < s₂)
    (himg₁ : η₁ '' Icc u a = (fun s => ψ (g₁ s)) '' Icc 0 s₁) (hend₁ : ψ (g₁ s₁) = η₁ a)
    (himg₂ : η₂ '' Icc r b = (fun s => ψ (g₂ s)) '' Icc 0 s₂) (hend₂ : ψ (g₂ s₂) = η₂ b)
    (hγ₁ : IsProperCompletion g₁ s₁ γ₁) (hγ₂ : IsProperCompletion g₂ s₂ γ₂)
    (hord : range γ₂ ⊆ closedLeftSide γ₁)
    (hR₁ : ∀ t, 0 < t → IsGluePoint E (γ₁ t)) (hR₂ : ∀ t, 0 < t → IsGluePoint E (γ₂ t)) :
    HasOrderedProperCompletions η₁ a η₂ b := by
  set A := η₁ '' Icc 0 u ∪ η₂ '' Icc 0 r with hA
  obtain ⟨hα, hαrep, hαrange⟩ := glue_side_real (A := A) hua hc₁ hi₁ hm₁
    (fun x hx => Or.inl ⟨x, ⟨zero_le, hx⟩, rfl⟩) hDA hDH hψH hψi hψc hψM hEi hEr hEA hg₁0 hψw hs₁ himg₁ hend₁
    hγ₁ hR₁
  obtain ⟨hβ, hβrep, hβrange⟩ := glue_side_real (A := A) hrb hc₂ hi₂ hm₂
    (fun y hy => Or.inr ⟨y, ⟨zero_le, hy⟩, rfl⟩) hDA hDH hψH hψi hψc hψM hEi hEr hEA hg₂0 hψ0 hs₂ himg₂ hend₂
    hγ₂ hR₂
  set α'' := junction η₁ (fun t => ψ (γ₁ (s₁ + t))) a 0 with hα''
  set β'' := junction η₂ (fun t => ψ (γ₂ (s₂ + t))) b 0 with hβ''
  refine ⟨α'', β'', hα, hβ, ?_⟩
  have hαP := isProperCurve_of_isProperCompletion hα
  have hβP := isProperCurve_of_isProperCompletion hβ
  have hα0 : α'' 0 = η₁ 0 := hα.2.2.2.2 0 zero_le
  have hβ0 : β'' 0 = η₂ 0 := hβ.2.2.2.2 0 zero_le
  have hα''0 : (α'' 0).im = 0 := by rw [hα0]; exact h01
  have hβ''0 : (β'' 0).im = 0 := by rw [hβ0]; exact h02
  have hγ₁P := isProperCurve_of_isProperCompletion hγ₁
  have hγ₂P := isProperCurve_of_isProperCompletion hγ₂
  have hγ₁0 : γ₁ 0 = w := by rw [hγ₁.2.2.2.2 0 zero_le, hg₁0]
  have hγ₂0 : γ₂ 0 = 0 := by rw [hγ₂.2.2.2.2 0 zero_le, hg₂0]
  have hγ₁0im : (γ₁ 0).im = 0 := by rw [hγ₁0]; simp
  have hγ₂0im : (γ₂ 0).im = 0 := by rw [hγ₂0]; simp
  -- the new parts of the glued curves are chart images of allowed points, off `A`
  have hαnew : ∀ t, u < t → α'' t ∉ A := fun t ht => by
    obtain ⟨t', ht', he⟩ := hαrep t ht
    rw [he]; exact notMem_of_isGluePoint hDA hψH hEA (hR₁ t' ht')
  have hβnew : ∀ t, r < t → β'' t ∉ A := fun t ht => by
    obtain ⟨t', ht', he⟩ := hβrep t ht
    rw [he]; exact notMem_of_isGluePoint hDA hψH hEA (hR₂ t' ht')
  -- an allowed chart point off the chart curve is sent off the glued curve
  have hoffα : ∀ z, IsGluePoint E z → z ∉ range γ₁ → ψ z ∉ range α'' := by
    rintro z hz hzγ ⟨t, ht⟩
    by_cases htu : t ≤ u
    · rw [hα.2.2.2.2 t (htu.trans hua)] at ht
      exact notMem_of_isGluePoint hDA hψH hEA hz (ht ▸ Or.inl ⟨t, ⟨zero_le, htu⟩, rfl⟩)
    · obtain ⟨t', ht', he⟩ := hαrep t (not_le.1 htu)
      exact hzγ ⟨t', (eq_of_isGluePoint hDH hψH hψi hEi hEr hz (hR₁ t' ht') (ht.symm.trans he)).symm⟩
  have hoffβ : ∀ z, IsGluePoint E z → z ∉ range γ₂ → ψ z ∉ range β'' := by
    rintro z hz hzγ ⟨t, ht⟩
    by_cases htr : t ≤ r
    · rw [hβ.2.2.2.2 t (htr.trans hrb)] at ht
      exact notMem_of_isGluePoint hDA hψH hEA hz (ht ▸ Or.inr ⟨t, ⟨zero_le, htr⟩, rfl⟩)
    · obtain ⟨t', ht', he⟩ := hβrep t (not_le.1 htr)
      exact hzγ ⟨t', (eq_of_isGluePoint hDH hψH hψi hEi hEr hz (hR₂ t' ht') (ht.symm.trans he)).symm⟩
  have hHim : ∀ z ∈ H, (0 : ℝ) < (ψ z).im := fun z hz => hDH (hψH hz)
  have hγE₁ : ∀ t, 0 < t → (γ₁ t).im = 0 → (γ₁ t).re ∈ E := fun t ht h0 =>
    (hR₁ t ht).elim (fun hH => absurd h0 (ne_of_gt hH)) fun h => h.2
  have hγE₂ : ∀ t, 0 < t → (γ₂ t).im = 0 → (γ₂ t).re ∈ E := fun t ht h0 =>
    (hR₂ t ht).elim (fun hH => absurd h0 (ne_of_gt hH)) fun h => h.2
  obtain ⟨αo, βo, hαo, hβo, hordo⟩ := hold
  rcases hEside with hL | hR
  · -- the images of `E` are left of the first seed: transfer through the left side of `γ₁`
    have hαu : IsProperCompletion η₁ u α'' :=
      ⟨hα.1, hα.2.1, hα.2.2.1, hα.2.2.2.1, fun t ht => hα.2.2.2.2 t (ht.trans hua)⟩
    have htail : ∀ s, u ≤ s → ∀ y ≤ r, α'' s ≠ η₂ y := by
      intro s hs y hy he
      rcases hs.lt_or_eq with hs' | heq
      · exact hαnew s hs' (by rw [he]; exact Or.inr ⟨y, ⟨zero_le, hy⟩, rfl⟩)
      · rw [← heq, hα.2.2.2.2 u hua] at he
        exact hp₁ ⟨y, ⟨zero_le, hy⟩, he.symm⟩
    obtain ⟨β₀, hβ₀, hord₀⟩ :=
      exists_isProperCompletion_subset_closedLeftSide hαo hβo hordo h01 h02 hseed hαu htail
    have hold₂ : ∀ y ≤ r, η₂ y ∈ closedLeftSide α'' := fun y hy => by
      rw [← hβ₀.2.2.2.2 y hy]; exact hord₀ ⟨y, rfl⟩
    have htipL : η₂ r ∈ leftSide α'' := by
      rcases hold₂ r le_rfl with h | h
      · exact h
      · exfalso
        rcases h with ⟨t, ht⟩ | ⟨-, him⟩
        · by_cases htu : t ≤ u
          · rw [hα.2.2.2.2 t (htu.trans hua)] at ht
            exact hp₂ ⟨t, ⟨zero_le, htu⟩, ht⟩
          · exact hαnew t (not_le.1 htu) (ht ▸ Or.inr ⟨r, ⟨zero_le, le_rfl⟩, rfl⟩)
        · rw [hα''0] at him
          exact absurd (show (0 : ℝ) < (η₂ r).im from htip₂) (not_lt.2 him)
    have hEL : ∀ y ∈ E, (y : ℂ) ∉ range γ₁ → ψ y ∈ leftSide α'' := by
      intro y hy hyγ
      have hz : IsGluePoint E (y : ℂ) := Or.inr ⟨by simp, by simpa using hy⟩
      have h1 : ψ y = ((ψ y).re : ℂ) := eq_ofReal_re_of_im_eq_zero (hEr y hy)
      rw [h1]
      exact ofReal_mem_leftSide_of_notMem hαP hα''0 (by rw [hα0]; exact hL y hy) (h1 ▸ hoffα _ hz hyγ)
    have hPL : ∀ z ∈ leftSide γ₁, z ∈ H → ψ z ∈ leftSide α'' := by
      refine image_side_subset (Ir := Iio w) hγ₁P (isOpen_leftSide hγ₁P) isPreconnected_connectedComponentIn
        ⟨_, leftRef_mem_leftSide hγ₁P.2.2.1 hγ₁0im, by simp [hγ₁0im]⟩ (fun z hz => notMem_range_of_mem_leftSide hz)
        ordConnected_Iio (by rw [hγ₁0]; simp) (fun y hy => ?_) (fun y hy hyγ => ?_) (isOpen_leftSide hαP)
        (isOpen_rightSide hαP) (disjoint_leftSide_rightSide hαP hα''0) hψc (fun z hzS hzH => ?_)
        (show (0 : ℝ) ∈ Iio w from hw) (by rw [ofReal_zero, hψ0]; exact htipL) hEo hγE₁
        (fun y hy _ hyγ => hEL y hy hyγ)
      · -- real points of the left side are left of the seed
        have hyγ := notMem_range_of_mem_leftSide hy
        rcases lt_trichotomy y w with h | h | h
        · exact h
        · exact absurd ⟨0, by rw [hγ₁0, h]⟩ hyγ
        · exact absurd (ofReal_mem_rightSide_of_notMem hγ₁P hγ₁0im (by rw [hγ₁0]; simpa using h) hyγ)
            (Set.disjoint_left.1 (disjoint_leftSide_rightSide hγ₁P hγ₁0im) hy)
      · exact ofReal_mem_leftSide_of_notMem hγ₁P hγ₁0im (by rw [hγ₁0]; simpa using hy) hyγ
      · rw [← compl_seedRayClosure_eq hαP hα''0]
        rintro (h | ⟨-, him⟩)
        · exact hoffα z (Or.inl hzH) (notMem_range_of_mem_leftSide hzS) h
        · rw [hα''0] at him; exact absurd (hHim z hzH) (not_lt.2 him)
    rintro _ ⟨t, rfl⟩
    by_cases htr : t ≤ r
    · rw [hβ.2.2.2.2 t (htr.trans hrb)]; exact hold₂ t htr
    · obtain ⟨t', ht', he⟩ := hβrep t (not_le.1 htr)
      rw [he]
      by_cases hγ : γ₂ t' ∈ range γ₁
      · obtain ⟨t'', ht''⟩ := hγ
        rw [← ht'']; exact Or.inr (Or.inl (hαrange t''))
      rcases hR₂ t' ht' with hH' | ⟨h0, hE⟩
      · rcases hord ⟨t', rfl⟩ with hLs | hS
        · exact Or.inl (hPL _ hLs hH')
        · rcases hS with h | ⟨-, him⟩
          · exact absurd h hγ
          · rw [hγ₁0im] at him; exact absurd (show (0 : ℝ) < (γ₂ t').im from hH') (not_lt.2 him)
      · rw [eq_ofReal_re_of_im_eq_zero h0] at hγ ⊢
        exact Or.inl (hEL _ hE hγ)
  · -- the images of `E` are right of the second seed: transfer through the right side of `γ₂`
    have hαoP := isProperCurve_of_isProperCompletion hαo
    have hβoP := isProperCurve_of_isProperCompletion hβo
    have hαo0 : αo 0 = η₁ 0 := hαo.2.2.2.2 0 zero_le
    have hβo0 : βo 0 = η₂ 0 := hβo.2.2.2.2 0 zero_le
    have hordR : range αo ⊆ closedRightSide βo :=
      range_subset_closedRightSide hαoP hβoP (by rw [hαo0]; exact h01) (by rw [hβo0]; exact h02)
        (by rw [hαo0, hβo0]; exact hseed) hordo
    have hold₁ : ∀ x ≤ u, η₁ x ∈ closedRightSide β'' := fun x hx => by
      rw [← hαo.2.2.2.2 x hx]
      refine mem_closedRightSide_of_avoid hβoP hβP (by rw [hβo0]; exact h02)
        (fun t ht => (hβ.2.2.2.2 t (ht.trans hrb)).trans (hβo.2.2.2.2 t ht).symm) hαoP
        (by rw [hαo0]; exact h01) (by rw [hαo0, hβo0]; exact hseed) hordR fun x' hx' s hs he => ?_
      rw [hαo.2.2.2.2 x' (hx'.trans hx)] at he
      rcases hs.lt_or_eq with hs' | heq
      · exact hβnew s hs' (by rw [← he]; exact Or.inl ⟨x', ⟨zero_le, hx'.trans hx⟩, rfl⟩)
      · rw [← heq, hβ.2.2.2.2 r hrb] at he
        exact hp₂ ⟨x', ⟨zero_le, hx'.trans hx⟩, he⟩
    have htipR : η₁ u ∈ rightSide β'' := by
      rcases hold₁ u le_rfl with h | h
      · exact h
      · exfalso
        rcases h with ⟨t, ht⟩ | ⟨-, him⟩
        · by_cases htr : t ≤ r
          · rw [hβ.2.2.2.2 t (htr.trans hrb)] at ht
            exact hp₁ ⟨t, ⟨zero_le, htr⟩, ht⟩
          · exact hβnew t (not_le.1 htr) (ht ▸ Or.inl ⟨u, ⟨zero_le, le_rfl⟩, rfl⟩)
        · rw [hβ''0] at him
          exact absurd (show (0 : ℝ) < (η₁ u).im from htip₁) (not_lt.2 him)
    have hER : ∀ y ∈ E, (y : ℂ) ∉ range γ₂ → ψ y ∈ rightSide β'' := by
      intro y hy hyγ
      have hz : IsGluePoint E (y : ℂ) := Or.inr ⟨by simp, by simpa using hy⟩
      have h1 : ψ y = ((ψ y).re : ℂ) := eq_ofReal_re_of_im_eq_zero (hEr y hy)
      rw [h1]
      exact ofReal_mem_rightSide_of_notMem hβP hβ''0 (by rw [hβ0]; exact hR y hy) (h1 ▸ hoffβ _ hz hyγ)
    have hPR : ∀ z ∈ rightSide γ₂, z ∈ H → ψ z ∈ rightSide β'' := by
      refine image_side_subset (Ir := Ioi 0) hγ₂P (isOpen_rightSide hγ₂P) isPreconnected_connectedComponentIn
        ⟨_, rightRef_mem_rightSide hγ₂P.2.2.1 hγ₂0im, by simp [rightRef, hγ₂0im]⟩
        (fun z hz => notMem_range_of_mem_rightSide hz) ordConnected_Ioi (by rw [hγ₂0]; simp)
        (fun y hy => ?_) (fun y hy hyγ => ?_) (isOpen_rightSide hβP) (isOpen_leftSide hβP)
        (disjoint_leftSide_rightSide hβP hβ''0).symm hψc (fun z hzS hzH => ?_)
        (show w ∈ Ioi (0 : ℝ) from hw) (by rw [hψw]; exact htipR) hEo hγE₂ (fun y hy _ hyγ => hER y hy hyγ)
      · have hyγ := notMem_range_of_mem_rightSide hy
        rcases lt_trichotomy y 0 with h | h | h
        · exact absurd (ofReal_mem_leftSide_of_notMem hγ₂P hγ₂0im (by rw [hγ₂0]; simpa using h) hyγ)
            (Set.disjoint_right.1 (disjoint_leftSide_rightSide hγ₂P hγ₂0im) hy)
        · exact absurd ⟨0, by rw [hγ₂0, h, ofReal_zero]⟩ hyγ
        · exact h
      · exact ofReal_mem_rightSide_of_notMem hγ₂P hγ₂0im (by rw [hγ₂0]; simpa using hy) hyγ
      · rw [union_comm, ← compl_seedRayClosure_eq hβP hβ''0]
        rintro (h | ⟨-, him⟩)
        · exact hoffβ z (Or.inl hzH) (notMem_range_of_mem_rightSide hzS) h
        · rw [hβ''0] at him; exact absurd (hHim z hzH) (not_lt.2 him)
    have hordc : range γ₁ ⊆ closedRightSide γ₂ :=
      range_subset_closedRightSide hγ₁P hγ₂P hγ₁0im hγ₂0im (by rw [hγ₁0, hγ₂0]; simpa using hw.le) hord
    have hαR : range α'' ⊆ closedRightSide β'' := by
      rintro _ ⟨t, rfl⟩
      by_cases htu : t ≤ u
      · rw [hα.2.2.2.2 t (htu.trans hua)]; exact hold₁ t htu
      · obtain ⟨t', ht', he⟩ := hαrep t (not_le.1 htu)
        rw [he]
        by_cases hγ : γ₁ t' ∈ range γ₂
        · obtain ⟨t'', ht''⟩ := hγ
          rw [← ht'']; exact Or.inr (Or.inl (hβrange t''))
        rcases hR₁ t' ht' with hH' | ⟨h0, hE⟩
        · rcases hordc ⟨t', rfl⟩ with hRs | hS
          · exact Or.inl (hPR _ hRs hH')
          · rcases hS with h | ⟨-, him⟩
            · exact absurd h hγ
            · rw [hγ₂0im] at him; exact absurd (show (0 : ℝ) < (γ₁ t').im from hH') (not_lt.2 him)
        · rw [eq_ofReal_re_of_im_eq_zero h0] at hγ ⊢
          exact Or.inl (hER _ hE hγ)
    exact range_subset_closedLeftSide_of_closedRightSide hαP hβP hα''0 hβ''0
      (by rw [hα0, hβ0]; exact hseed) hαR

end Main

end RLC

end InteractingSLE
