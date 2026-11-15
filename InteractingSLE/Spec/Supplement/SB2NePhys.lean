/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.SB2NeInj

/-!
# From the launch chart to the original real line (deterministic)

Packet PROVE-AUX61-NOJUMP (round 22, component F).

* `exists_eq_rightLim_word`, `exists_eq_rightLim_data`: piecewise constant data equal their right limit just right
  of a point;
* `mem_closure_rBad`: a closure point of the right-bad set of a word with an admissible seed is positive, and bad or a
  jump; `badSetC_subset`: with admissible left heights the closed bad set of the word is that closure;
* `rightLim_eq_of_rOrig`: the heights of the launch word on the free ray are the original heights through the
  chart's right profile.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology Metric
open scoped NNReal ENNReal
open QuantumZipper (H Hbar chiC)

namespace InteractingSLE.Theorem14.SB.Ne

open Exist Exist.StagedLaw Exist.Staged Restart GW1W
open PiecewiseConstantBoundaryData (rightLim leftLim)

section Heights

/-- A word equals its right limit just right of a point. -/
theorem exists_eq_rightLim_word (c : BoundaryWord) (y : ℝ) :
    ∃ δ > 0, ∀ t ∈ Ioo y (y + δ), c.fn t = rightLim c.fn y := by
  obtain ⟨δ, hδ, hδJ⟩ := Supp7.exists_pos_forall_notMem c.jumps y
  have hpos : ∀ j < c.1, ¬ (y < c.2.1 j ∧ c.2.1 j < y + δ) := fun j hj hj' =>
    (hδJ _ (BoundaryWord.mem_jumps.2 ⟨j, hj, rfl⟩)).1 hj'
  set q : ℝ := y + δ / 2 with hq
  have hq1 : y < q := by linarith
  have hr : rightLim c.fn y = c.fn q :=
    rightLim_eq_of_noPos hq1 fun j hj hj' => hpos j hj ⟨hj'.1, by linarith [hj'.2]⟩
  refine ⟨δ, hδ, fun t ht => ?_⟩
  rw [hr]
  unfold BoundaryWord.fn
  rcases le_total t q with h | h
  · rw [Wf.index_eq_of_noPos h fun j hj hj' => hpos j hj ⟨lt_of_lt_of_le ht.1 hj'.1, by linarith [hj'.2]⟩]
  · rw [Wf.index_eq_of_noPos h fun j hj hj' => hpos j hj ⟨by linarith [hj'.1], lt_trans hj'.2 ht.2⟩]

/-- Piecewise constant data equal their right limit just right of a point, off the jumps. -/
theorem exists_eq_rightLim_data {b : ℝ → ℝ} {J : Finset ℝ} (hb : IsPiecewiseConstantBoundaryData b J) (x : ℝ) :
    ∃ δ > 0, ∀ t ∈ Ioo x (x + δ), t ∉ J → b t = rightLim b x := by
  obtain ⟨c₀, -, hc₀⟩ := BoundaryWord.exists_fn_eq hb
  obtain ⟨δ, hδ, hδc⟩ := exists_eq_rightLim_word c₀ x
  have hev : ∀ᶠ t in 𝓝[>] x, b t = rightLim c₀.fn x := by
    have h1 : ∀ᶠ t in 𝓝[>] x, t ∈ Ioo x (x + δ) :=
      Ioo_mem_nhdsGT (show x < x + δ by linarith)
    have h2 : ∀ᶠ t in 𝓝[>] x, t ∉ (J : Set ℝ) :=
      (GW1W.eventually_notMem_of_finite J.finite_toSet x).filter_mono (nhdsWithin_mono _ fun z hz => ne_of_gt hz)
    filter_upwards [h1, h2] with t ht1 ht2
    rw [← hc₀ t ht2]
    exact hδc t ht1
  have hlim : rightLim b x = rightLim c₀.fn x := by
    unfold PiecewiseConstantBoundaryData.rightLim
    exact (tendsto_const_nhds.congr' (hev.mono fun t ht => ht.symm)).limUnder_eq
  refine ⟨δ, hδ, fun t ht htJ => ?_⟩
  rw [hlim, ← hc₀ t htJ]
  exact hδc t ht

variable {κ θ : ℝ}

/-- **The right-bad set of a word.** -/
def rBadSet (κ θ : ℝ) (c : BoundaryWord) : Set ℝ := {y | RBadW κ θ c y}

/-- Right limits near a point agree with the right limit at it, away from the jumps (and on the right). -/
theorem rightLim_eq_near (c : BoundaryWord) {y δ₀ : ℝ}
    (hδJ : ∀ z ∈ c.jumps, z ∉ Ioo y (y + δ₀) ∧ z ∉ Ioo (y - δ₀) y) {y' : ℝ} (h1 : y - δ₀ < y')
    (h2 : y' < y + δ₀) (h3 : y ≤ y' ∨ y ∉ c.jumps) : rightLim c.fn y' = rightLim c.fn y := by
  set q : ℝ := (max y y' + (y + δ₀)) / 2 with hq
  have hq1 : max y y' < q := by rw [hq]; have := max_lt (show y < y + δ₀ by linarith) h2; linarith
  have hq2 : q < y + δ₀ := by rw [hq]; have := max_lt (show y < y + δ₀ by linarith) h2; linarith
  have hno2 : ∀ j < c.1, ¬ (y < c.2.1 j ∧ c.2.1 j < q) := fun j hj hj' =>
    (hδJ _ (BoundaryWord.mem_jumps.2 ⟨j, hj, rfl⟩)).1 ⟨hj'.1, lt_trans hj'.2 hq2⟩
  have hno1 : ∀ j < c.1, ¬ (y' < c.2.1 j ∧ c.2.1 j < q) := by
    intro j hj hj'
    have hm := BoundaryWord.mem_jumps.2 ⟨j, hj, rfl⟩
    rcases lt_trichotomy (c.2.1 j) y with hlt | heq | hgt
    · have hyy : y' < y := lt_trans hj'.1 hlt
      exact (hδJ _ hm).2 ⟨by linarith [hj'.1], hlt⟩
    · rcases h3 with h | h
      · exact absurd (heq ▸ hj'.1) (not_lt.2 h)
      · exact h (heq ▸ hm)
    · exact hno2 j hj ⟨hgt, hj'.2⟩
  rw [rightLim_eq_of_noPos (lt_of_le_of_lt (le_max_right _ _) hq1) hno1,
    rightLim_eq_of_noPos (lt_of_le_of_lt (le_max_left _ _) hq1) hno2]

/-- **A closure point of the right-bad set of a word with an admissible seed** is positive, and bad or a jump. -/
theorem mem_closure_rBad {c : BoundaryWord} (hseed : Wf.SeedOK κ θ c) {y : ℝ} (hy : y ∈ closure (rBadSet κ θ c)) :
    0 < y ∧ (RBadW κ θ c y ∨ y ∈ c.jumps) := by
  obtain ⟨δ₀, hδ₀, hδJ⟩ := Supp7.exists_pos_forall_notMem c.jumps y
  obtain ⟨y', hy', hd⟩ := Metric.mem_closure_iff.1 hy δ₀ hδ₀
  rw [Real.dist_eq, abs_lt] at hd
  by_cases hcase : y ≤ y' ∨ y ∉ c.jumps
  · have hr := rightLim_eq_near c hδJ (by linarith [hd.2]) (by linarith [hd.1]) hcase
    have hw : Sec4.cumWeightRight κ (rightLim c.fn y + θ * chiC κ) ≤ -2 := by rw [← hr]; exact hy'.2
    have hpos : 0 < y := by
      by_contra hn
      have hy0 : y = 0 := le_antisymm (not_lt.1 hn) (closure_minimal (fun y'' hy'' => le_of_lt hy''.1) isClosed_Ici hy)
      rw [hy0] at hw
      exact absurd hseed (not_lt.2 hw)
    exact ⟨hpos, Or.inl ⟨hpos, hw⟩⟩
  · push Not at hcase
    exact ⟨lt_trans hy'.1 hcase.1, Or.inr hcase.2⟩

/-- **With admissible left heights, the closed bad set of a word is the closure of its right-bad set.** -/
theorem badSetC_subset {c : BoundaryWord} (hκ : 0 < κ)
    (hleft : ∀ y : ℝ, y < 0 → y ∉ c.jumps → c.fn y + θ * chiC κ < sleLambda κ) {z : ℂ}
    (hz : z ∈ GW2Sdn.badSetC κ c.fn θ 0) : ∃ y : ℝ, z = y ∧ y ∈ closure (rBadSet κ θ c) := by
  obtain ⟨y, hy, rfl⟩ := hz
  refine ⟨y, rfl, ?_⟩
  have hB : {y : ℝ | y < 0 ∧ Sec4.cumWeightLeft κ (leftLim c.fn y + θ * chiC κ) ≤ -2} = ∅ := by
    ext y'
    simp only [mem_ofPred_eq, mem_empty_iff_false, iff_false, not_and, not_le]
    intro hy'
    obtain ⟨δ, hδ, hδJ⟩ := Supp7.exists_pos_forall_notMem c.jumps y'
    set d : ℝ := min δ (-y') with hd
    have hd0 : 0 < d := lt_min hδ (by linarith)
    have hnoP : ∀ j < c.1, ¬ (y' - d < c.2.1 j ∧ c.2.1 j < y') := fun j hj hj' =>
      (hδJ _ (BoundaryWord.mem_jumps.2 ⟨j, hj, rfl⟩)).2 ⟨by have := min_le_left δ (-y'); linarith [hj'.1], hj'.2⟩
    set t₀ : ℝ := y' - d / 2 with ht₀
    have hconst : ∀ t ∈ Ioo (y' - d) y', c.fn t = c.fn t₀ := by
      intro t ht
      unfold BoundaryWord.fn
      rcases le_total t t₀ with h | h
      · rw [Wf.index_eq_of_noPos h fun j hj hj' => hnoP j hj ⟨lt_of_lt_of_le ht.1 hj'.1, by linarith [hj'.2]⟩]
      · rw [Wf.index_eq_of_noPos h fun j hj hj' => hnoP j hj ⟨by linarith [hj'.1], lt_trans hj'.2 ht.2⟩]
    have hl : leftLim c.fn y' = c.fn t₀ := Sec4.leftLim_eq_of_forall (by linarith) hconst
    have ht₀J : t₀ ∉ c.jumps := fun h => (hδJ _ h).2 ⟨by have := min_le_left δ (-y'); linarith, by linarith⟩
    have h := hleft t₀ (by have := min_le_right δ (-y'); linarith) ht₀J
    have hl0 := Sec4.sleLambda_pos hκ
    rw [hl]
    unfold Sec4.cumWeightLeft
    have : -(c.fn t₀ + θ * chiC κ) / sleLambda κ > -1 := by
      rw [gt_iff_lt, lt_div_iff₀ hl0]; linarith
    linarith
  have e : GW2Sdn.badSet κ c.fn θ 0 = closure (rBadSet κ θ c) := by
    unfold GW2Sdn.badSet
    rw [hB, union_empty]
    rfl
  rw [← e]
  exact hy

/-- **The launch word keeps the original heights on the free ray**, through the chart's right profile. -/
theorem rightLim_eq_of_rOrig {b : ℝ → ℝ} {J : Finset ℝ} (hb : IsPiecewiseConstantBoundaryData b J)
    {β : BoundaryWord} {m : ℝ → ℝ} {R : ℝ} (hmono : StrictMonoOn m (Ioi R)) (hcont : ContinuousOn m (Ioi R))
    (hO : ∀ x, R < x → x ∉ J → m x ∉ β.jumps → β.fn (m x) = b x) {x : ℝ} (hx : R < x) :
    rightLim β.fn (m x) = rightLim b x := by
  classical
  obtain ⟨δb, hδb, hb'⟩ := exists_eq_rightLim_data hb x
  obtain ⟨δw, hδw, hw'⟩ := exists_eq_rightLim_word β (m x)
  have hca : ContinuousAt m x := hcont.continuousAt (isOpen_Ioi.mem_nhds hx)
  obtain ⟨η, hη, hηm⟩ := Metric.continuousAt_iff.1 hca δw hδw
  have hfin : (Ioi R ∩ m ⁻¹' (β.jumps : Set ℝ)).Finite :=
    Set.Finite.of_finite_image ((β.jumps.finite_toSet).subset (image_subset_iff.2 fun _ h => h.2))
      (hmono.injOn.mono inter_subset_left)
  set ε : ℝ := min δb η with hε
  have hε0 : 0 < ε := lt_min hδb hη
  obtain ⟨t, ht, htn⟩ := (Set.Ioo_infinite (show x < x + ε by linarith)).exists_notMem_finset
    (J ∪ hfin.toFinset)
  have htJ : t ∉ J := fun h => htn (Finset.mem_union_left _ h)
  have htR : R < t := lt_trans hx ht.1
  have htm : m t ∉ β.jumps := fun h => htn (Finset.mem_union_right _ ((Set.Finite.mem_toFinset _).2 ⟨htR, h⟩))
  have h1 : b t = rightLim b x := hb' t ⟨ht.1, lt_of_lt_of_le ht.2 (by linarith [min_le_left δb η])⟩ htJ
  have hmt : m x < m t := hmono hx htR ht.1
  have hdist : dist (m t) (m x) < δw := hηm (by
    rw [Real.dist_eq, abs_lt]; constructor <;> linarith [ht.1, ht.2, min_le_right δb η])
  rw [Real.dist_eq, abs_lt] at hdist
  have h2 : β.fn (m t) = rightLim β.fn (m x) := hw' (m t) ⟨hmt, by linarith [hdist.2]⟩
  rw [← h2, hO t htR htJ htm, h1]

end Heights


/-! ### B's piece on the original real line -/

section Phys

variable {κ : ℝ} {b : ℝ → ℝ} {J : Finset ℝ}

/-- An original right-bad point is read as a right-bad point of the launch word. -/
theorem rBadW_of_origBadR (hb : IsPiecewiseConstantBoundaryData b J) {s : ExplState} (hRP : RProf s)
    {β : BoundaryWord} (hO : ROrig b J β s) {x : ℝ} (hx : x ∈ origBadR κ b (stRecR s)) :
    RBadW κ (-(Real.pi / 2)) β (rProf (stChart s) x) := by
  refine ⟨hRP.2.2.1 x hx.1, ?_⟩
  rw [rightLim_eq_of_rOrig hb hRP.2.1.1 hRP.2.1.2.1 hO hx.1]
  exact hx.2

/-- The right profile tends to `0` at the record. -/
theorem tendsto_rProf_zero {s : ExplState} (hRP : RProf s) :
    Tendsto (rProf (stChart s)) (𝓝[>] (stRecR s)) (𝓝 0) := by
  rw [Metric.tendsto_nhdsWithin_nhds]
  intro ε hε
  obtain ⟨x₁, hx₁, hx₁ε⟩ := hRP.2.2.2 ε hε
  refine ⟨x₁ - stRecR s, by linarith, fun x hx hd => ?_⟩
  rw [Real.dist_eq, abs_lt] at hd
  have hxR : stRecR s < x := hx
  have h1 := hRP.2.2.1 x hxR
  have h2 := hRP.2.1.1 hxR hx₁ (show x < x₁ by linarith [hd.2])
  rw [Real.dist_eq, sub_zero, abs_lt]
  constructor <;> linarith

/-- **The record is off the closure of the original right-bad points** when the launch seed is admissible. -/
theorem record_notMem_closure (hb : IsPiecewiseConstantBoundaryData b J) {s : ExplState} (hRP : RProf s)
    {β : BoundaryWord} (hO : ROrig b J β s) (hseed : Wf.SeedOK κ (-(Real.pi / 2)) β) :
    stRecR s ∉ closure (origBadR κ b (stRecR s)) := by
  intro hR
  have hne : (𝓝[origBadR κ b (stRecR s)] (stRecR s)).NeBot := mem_closure_iff_nhdsWithin_neBot.1 hR
  have hle : 𝓝[origBadR κ b (stRecR s)] (stRecR s) ≤ 𝓝[>] (stRecR s) := nhdsWithin_mono _ fun x hx => hx.1
  have h0 : (0 : ℝ) ∈ closure (rBadSet κ (-(Real.pi / 2)) β) :=
    mem_closure_of_tendsto ((tendsto_rProf_zero hRP).mono_left hle)
      (eventually_nhdsWithin_of_forall fun x hx => rBadW_of_origBadR hb hRP hO hx)
  exact lt_irrefl _ (mem_closure_rBad hseed h0).1

/-- **A physical free point of B's piece is read in the launch chart at the right profile.** -/
theorem launch_eq_rProf {s : ExplState} (hRP : RProf s) {g : ℂ → ℂ} (hcc : (stChart s).IsConformal)
    (hgc : ContinuousOn g {z | 0 ≤ z.im}) (hgi : EqOn g (stChart s).2.1 H) {C₁ C₂ : ℝ}
    (hprop : ∀ w : ℂ, 0 ≤ w.im → ‖w‖ ≤ C₁ * ‖g w‖ + C₂) (hg0 : g 0 = stRecR s)
    (hrec : ∀ x : ℝ, stRecR s < x → g ((stChart s).1 x) = x)
    (hfree : ∀ x : ℝ, stRecR s < x → ∃ r > 0, ∀ z ∈ H, dist z (x : ℂ) < r → z ∈ (stChart s).2.1 '' H)
    {w : ℂ} (hw : 0 ≤ w.im) {x : ℝ} (hx : stRecR s < x) (hgw : g w = x) :
    w = (rProf (stChart s) x : ℂ) := by
  have hcx : (stChart s).1 x = ((rProf (stChart s) x : ℝ) : ℂ) :=
    Complex.ext (by simp [rProf]) (by simp [hRP.1 x])
  have hpos := hRP.2.2.1 x hx
  rcases hw.lt_or_eq with him | him
  · exfalso
    have : g w ∈ H := by rw [hgi him]; exact hcc.2.1 him
    rw [hgw] at this
    exact absurd this (by show ¬ (0 : ℝ) < ((x : ℝ) : ℂ).im; simp)
  · have hwe : w = ((w.re : ℝ) : ℂ) := Complex.ext (by simp) (by simp [← him])
    set y := w.re with hy
    rw [hwe] at hgw ⊢
    rcases lt_trichotomy y 0 with hneg | hzero | hposy
    · exfalso
      obtain ⟨r, hr, hfr⟩ := hfree x hx
      have h1 : g ((rProf (stChart s) x : ℝ) : ℂ) = x := by rw [← hcx]; exact hrec x hx
      exact not_two_sides hcc hgc hgi hprop hg0 (ne_of_gt hx) hr hfr hneg hpos hgw h1
    · exfalso
      rw [hzero, Complex.ofReal_zero, hg0] at hgw
      exact absurd (by exact_mod_cast hgw) (ne_of_lt hx)
    · obtain ⟨x', hx', hx'y⟩ := hRP.exists_eq hposy
      have hcx' : (stChart s).1 x' = ((rProf (stChart s) x' : ℝ) : ℂ) :=
        Complex.ext (by simp [rProf]) (by simp [hRP.1 x'])
      have h1 : g (y : ℂ) = x' := by
        rw [← hx'y, ← hcx']
        exact hrec x' hx'
      have hxx : x' = x := by
        have := hgw.symm.trans h1
        exact_mod_cast this.symm
      rw [← hx'y, hxx]

/-- **B's piece on the original real line** (deterministic): from the launch facts (seed, left heights, avoidance of
the forbidden set, no visit of a non-bad mark, the tip in the closed bad set), the piece avoids the closure of the
original right-bad points right of its record before its lifetime, and at a finite lifetime ends at such a point. -/
theorem phys_facts (hκ : 0 < κ) (hb : IsPiecewiseConstantBoundaryData b J) {s : ExplState} (hRP : RProf s)
    {β : BoundaryWord} (hO : ROrig b J β s) (hseed : Wf.SeedOK κ (-(Real.pi / 2)) β)
    (hleft : ∀ y : ℝ, y < 0 → y ∉ β.jumps → β.fn y + -(Real.pi / 2) * chiC κ < sleLambda κ)
    {g : ℂ → ℂ} (hcc : (stChart s).IsConformal) (hgc : ContinuousOn g {z | 0 ≤ z.im})
    (hgi : EqOn g (stChart s).2.1 H) {C₁ C₂ : ℝ} (hprop : ∀ w : ℂ, 0 ≤ w.im → ‖w‖ ≤ C₁ * ‖g w‖ + C₂)
    (hg0 : g 0 = stRecR s) (hrec : ∀ x : ℝ, stRecR s < x → g ((stChart s).1 x) = x)
    (hfree : ∀ x : ℝ, stRecR s < x → ∃ r > 0, ∀ z ∈ H, dist z (x : ℂ) < r → z ∈ (stChart s).2.1 '' H)
    {α : ℝ≥0 → ℂ} {ζ : ℝ≥0∞} (hαH : ∀ t : ℝ≥0, (t : ℝ≥0∞) ≤ ζ → 0 ≤ (α t).im)
    (havoid : ∀ t : ℝ≥0, (t : ℝ≥0∞) < ζ → α t ∉ Wf.forb κ (-(Real.pi / 2)) β)
    (hmark : ∀ i, i < β.1 → 0 < β.2.1 i → ¬ RBadW κ (-(Real.pi / 2)) β (β.2.1 i) →
      ∀ t : ℝ≥0, (t : ℝ≥0∞) ≤ ζ → α t ≠ ((β.2.1 i : ℝ) : ℂ))
    {p : ℝ≥0 → ℂ} (hval : ∀ t : ℝ≥0, (t : ℝ≥0∞) ≤ ζ → p t = g (α t)) :
    (∀ t : ℝ≥0, (t : ℝ≥0∞) < ζ → ∀ x : ℝ, p t = x → stRecR s < x → x ∉ closure (origBadR κ b (stRecR s))) ∧
    (ζ ≠ ⊤ → GW2Rd.badDist κ (-(Real.pi / 2)) β (α ζ.toNNReal) = 0 →
      ∃ x : ℝ, p ζ.toNNReal = x ∧ x ∈ origBadR κ b (stRecR s)) := by
  -- a right-bad launch point at a time up to the lifetime is excluded before the lifetime
  have hjump : ∀ t : ℝ≥0, (t : ℝ≥0∞) ≤ ζ → ∀ y : ℝ, α t = (y : ℂ) → 0 < y → y ∈ β.jumps →
      RBadW κ (-(Real.pi / 2)) β y := by
    intro t ht y hy hpos hJ
    obtain ⟨i, hi, hiy⟩ := BoundaryWord.mem_jumps.1 hJ
    by_contra hn
    rw [← hiy] at hn hpos
    exact hmark i hi hpos hn t ht (by rw [hy, hiy])
  have hforb : ∀ t : ℝ≥0, (t : ℝ≥0∞) < ζ → ∀ y : ℝ, α t = (y : ℂ) → ¬ RBadW κ (-(Real.pi / 2)) β y := by
    intro t ht y hy hbad
    apply havoid t ht
    rw [hy]
    refine ⟨by simp, Or.inl ⟨by simpa using hbad.1, ?_⟩⟩
    simpa using hbad.2
  refine ⟨fun t ht x hpx hx hcl => ?_, fun htop hd => ?_⟩
  · have hα := launch_eq_rProf hRP hcc hgc hgi hprop hg0 hrec hfree (hαH t ht.le) hx (by rw [← hval t ht.le]; exact hpx)
    have hca : ContinuousAt (rProf (stChart s)) x := hRP.2.1.2.1.continuousAt (isOpen_Ioi.mem_nhds hx)
    have hmem : rProf (stChart s) x ∈ closure (rBadSet κ (-(Real.pi / 2)) β) :=
      closure_mono (show rProf (stChart s) '' origBadR κ b (stRecR s) ⊆ rBadSet κ (-(Real.pi / 2)) β from
        image_subset_iff.2 fun x' hx' => rBadW_of_origBadR hb hRP hO hx')
        (hca.continuousWithinAt.mem_closure_image hcl)
    obtain ⟨hpos, hbad | hJ⟩ := mem_closure_rBad hseed hmem
    · exact hforb t ht _ hα hbad
    · exact hforb t ht _ hα (hjump t ht.le _ hα hpos hJ)
  · have hcl : α ζ.toNNReal ∈ GW2Sdn.badSetC κ β.fn (-(Real.pi / 2)) 0 := (GW2Rd.badDist_eq_zero_iff _ _).1 hd
    obtain ⟨y, hy, hycl⟩ := badSetC_subset hκ hleft hcl
    have hζle : ((ζ.toNNReal : ℝ≥0) : ℝ≥0∞) ≤ ζ := ENNReal.coe_toNNReal_le_self
    obtain ⟨hpos, hbad | hJ⟩ := mem_closure_rBad hseed hycl
    all_goals
      have hbad' : RBadW κ (-(Real.pi / 2)) β y := by
        first
          | exact hbad
          | exact hjump _ hζle y hy hpos hJ
      obtain ⟨x', hx', hx'y⟩ := hRP.exists_eq hpos
      have hcx' : (stChart s).1 x' = ((rProf (stChart s) x' : ℝ) : ℂ) :=
        Complex.ext (by simp [rProf]) (by simp [hRP.1 x'])
      refine ⟨x', ?_, hx', ?_⟩
      · rw [hval _ hζle, hy, ← hx'y, ← hcx']
        exact hrec x' hx'
      · rw [← rightLim_eq_of_rOrig hb hRP.2.1.1 hRP.2.1.2.1 hO hx', hx'y]
        exact hbad'.2

end Phys

end InteractingSLE.Theorem14.SB.Ne
