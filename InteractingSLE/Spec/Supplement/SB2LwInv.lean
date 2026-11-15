/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.SB2LwState

/-!
# SB2(2)'s word: the invariant of the upper schedule's word at every launch (deterministic)

Packet PROVE-T14-SB2LOW (ruling R99). Lemma SB2, second assertion (supplement p. 632, `source/spec/p625-671.md`
L141): "If the erased upper history has an old right side of angle `ψ_j`, its height is `λ − ψ_jχ`; the lower-flow
left cumulative weight there is `−2 + (ψ_j − φ)χ/λ > −2`. On an exposed old upper-left side the corresponding weight is
`(ψ_j − φ)χ/λ > 0`. All these old groups are admissible. [...] All original-real groups [...] have their original
weights, because the map reflects positively outside the old real base." At a launch of the upper schedule the word
`β` of the conditional law, read in the chart `c` of the state `s`, satisfies `UInv`:

* (state) `UState u s` (`SB2LwState`);
* (`ROrig`) on the untouched ray right of the right record the word is the original word, read through `c`;
* (middle) between the tip `0` and the image of the untouched ray every height is a side height `±λ − ψχ` of a
  schedule angle `ψ` (`SideH`);
* (left) left of the tip every height is admissible for the lower flow of angle `−π/2`: `β − (π/2)χ < λ`.

`uInv_init` is the root (with GW1's ambient bound left of `0`); **`uInv_launch`** is the step through a piece of a
schedule angle `θ > −π/2` stopped at an interior tip, for the stop word `stopWord κ (β, θ, record)` (PROVE-STAGEDLAW3).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Filter Set Topology
open scoped NNReal ENNReal
open QuantumZipper (IsForwardSol chiC fwdMap fwdMapInv fwdHull H)

namespace InteractingSLE.Theorem14.SB.Lh

open Exist Exist.StagedLaw Exist.Staged Restart GW1W

/-- The side heights `λ − ψχ` (right side) and `−λ − ψχ` (left side) of the schedule angles `ψ`. -/
def SideH (κ : ℝ) (l : List (ℝ × ℝ≥0)) (v : ℝ) : Prop :=
  ∃ p ∈ l, v = sleLambda κ - p.1 * chiC κ ∨ v = -sleLambda κ - p.1 * chiC κ

/-- **SB2(2)'s upper invariant** at a state `s` of the upper schedule run from `u`, for the word `β`. -/
def UInv (κ : ℝ) (b : ℝ → ℝ) (jumps : Finset ℝ) (u : ℝ) (l : List (ℝ × ℝ≥0)) (β : BoundaryWord)
    (s : ExplState) : Prop :=
  UState u s ∧ ROrig b jumps β s ∧
    (∀ y, 0 < y → y ∉ β.jumps → (∀ x, stRecR s < x → y < rProf (stChart s) x) → SideH κ l (β.fn y)) ∧
    ∀ y, y < 0 → y ∉ β.jumps → β.fn y + -(Real.pi / 2) * chiC κ < sleLambda κ

variable {κ : ℝ} {b : ℝ → ℝ} {jumps : Finset ℝ} {u : ℝ} {l : List (ℝ × ℝ≥0)}

/-- **The invariant at the root**: the original word recentred at `u`, under GW1's ambient bound left of `0`. -/
theorem uInv_init (hu : u ≤ 0)
    (hamb : ∀ x, x < 0 → x ∉ jumps → b x + -(Real.pi / 2) * chiC κ < sleLambda κ) {c₀ : BoundaryWord}
    (hc₀J : c₀.jumps = jumps) (hc₀ : ∀ y ∉ jumps, c₀.fn y = b y) :
    UInv κ b jumps u l (BoundaryWord.shiftW u c₀) (ExplState.init u) := by
  have hR : stRecR (ExplState.init u) = u := rfl
  have hJ : ∀ y, y ∉ (BoundaryWord.shiftW u c₀).jumps → y + u ∉ jumps := fun y hy h => hy (by
    rw [BoundaryWord.jumps_shiftW, hc₀J]
    exact Finset.mem_image.2 ⟨y + u, h, by ring⟩)
  refine ⟨uState_init u, fun x hx hxJ hzJ => ?_, fun y hy _ hmid => ?_, fun y hy hyJ => ?_⟩
  · rw [rProf_init] at hzJ ⊢
    rw [BoundaryWord.fn_shiftW, sub_add_cancel]
    exact hc₀ x hxJ
  · have := hmid (u + y) (by rw [hR]; linarith)
    rw [rProf_init] at this
    linarith
  · rw [BoundaryWord.fn_shiftW, hc₀ _ (hJ y hyJ)]
    exact hamb _ (by linarith) (hJ y hyJ)

/-- **The original word survives on the new right ray** (the argument of `GW1W.rOrig_of_rel`, for a piece stopped at
an interior tip): the stop word at the image of an untouched point is the launch word there. -/
theorem rOrig_launch (hκ : 0 < κ) (hb : IsPiecewiseConstantBoundaryData b jumps) {β : BoundaryWord}
    {s s₁ : ExplState} {r : RecData} (θ : ℝ) (hmono : StrictMonoOn (rProf (stChart s)) (Ioi (stRecR s)))
    (hpos : ∀ x, stRecR s < x → 0 < rProf (stChart s) x)
    (hcont₁ : ContinuousOn (rProf (stChart s₁)) (Ioi (stRecR s₁))) (hO : ROrig b jumps β s)
    (hrel : ∀ x, stRecR s₁ < x → stRecR s < x ∧
      (∃ v, IsForwardSol (rdrv r) (rProf (stChart s) x : ℂ) (rtime r) v) ∧
      rProf (stChart s₁) x = (fwdMap (rdrv r) (rtime r) (rProf (stChart s) x)).re) :
    ROrig b jumps (stopWord κ (β, θ, r)) s₁ := by
  set γ := stopWord κ (β, θ, r) with hγ
  set m₁ := rProf (stChart s₁) with hm₁
  intro x hx hxJ hzJ
  have hc₁ : ContinuousAt m₁ x := hcont₁.continuousAt (Ioi_mem_nhds hx)
  have hP : ∀ᶠ x' in 𝓝 x, stRecR s₁ < x' ∧ b x' = b x ∧ m₁ x' ∉ γ.jumps ∧ γ.fn (m₁ x') = γ.fn (m₁ x) := by
    have h1 := hc₁.eventually (γ.isPiecewiseConstantBoundaryData (m₁ x) hzJ)
    have h2 := hc₁.eventually ((γ.jumps.finite_toSet.isClosed.isOpen_compl).mem_nhds hzJ)
    filter_upwards [Ioi_mem_nhds hx, hb x hxJ, h1, h2] with x' h0 h3 h4 h5
    exact ⟨h0, h3, h5, h4⟩
  obtain ⟨x', hx'R, hx'J, hmx'J, hx'R₁, hbx', hm₁J, hfn⟩ := exists_near_avoid hmono (hrel x hx).1 jumps β.jumps hP
  obtain ⟨-, hal, heq⟩ := hrel x' hx'R₁
  have hpos' : 0 < rProf (stChart s) x' := hpos x' hx'R
  calc γ.fn (m₁ x) = γ.fn (m₁ x') := hfn.symm
    _ = γ.fn (fwdMap (rdrv r) (rtime r) (rProf (stChart s) x')).re := by rw [heq]
    _ = β.fn (rProf (stChart s) x') :=
        stopWord_fn_fwdMap hκ β θ r hpos' hal hmx'J (by rw [← heq]; exact hm₁J)
    _ = b x' := hO x' hx'R hx'J hmx'J
    _ = b x := hbx'

/-- **The middle stays a side word** (SB2's "old right side [...] height `λ − ψ_jχ`"): between the tip and the image
of the untouched ray, the stop word is the new right side `λ − θχ` or the launch word at an alive point of the old
middle; untouched points swallowed by the piece leave the boundary. -/
theorem mid_launch (hκ : 0 < κ) {β : BoundaryWord} {s s₁ : ExplState} {θ : ℝ} {r : RecData}
    (hθl : ∃ p ∈ l, θ = p.1) (hm : RightGood (rProf (stChart s)) (stRecR s))
    (hpos : ∀ x, stRecR s < x → 0 < rProf (stChart s) x)
    (hM : ∀ y, 0 < y → y ∉ β.jumps → (∀ x, stRecR s < x → y < rProf (stChart s) x) → SideH κ l (β.fn y))
    (hdead : ∀ z, stRecR s < z → z < stRecR s₁ →
      ¬ ∃ v, IsForwardSol (rdrv r) (rProf (stChart s) z : ℂ) (rtime r) v)
    (hrel : ∀ x, stRecR s₁ < x → stRecR s < x ∧
      (∃ v, IsForwardSol (rdrv r) (rProf (stChart s) x : ℂ) (rtime r) v) ∧
      rProf (stChart s₁) x = (fwdMap (rdrv r) (rtime r) (rProf (stChart s) x)).re) :
    ∀ y, 0 < y → y ∉ (stopWord κ (β, θ, r)).jumps → (∀ x, stRecR s₁ < x → y < rProf (stChart s₁) x) →
      SideH κ l ((stopWord κ (β, θ, r)).fn y) := by
  intro y hy hyJ hymid
  set γ := stopWord κ (β, θ, r) with hγ
  set m := rProf (stChart s) with hmdef
  set a := stRecR s with hadef
  set a₁ := stRecR s₁ with ha₁def
  set w := rdrv r with hwdef
  set T := rtime r with hTdef
  have hw : Continuous w := continuous_rdrv r
  have hw0 : w 0 = 0 := rdrv_zero r
  have hT : 0 ≤ T := rtime_nonneg r
  have hH := isRealHalf_of hw hw0 hT
  set F : Finset ℝ := γ.jumps ∪ (β.jumps.image fun z : ℝ => (fwdMap w T (z : ℂ)).re) ∪ {(fwdMap w T (m a₁)).re} with hF
  have hev : ∀ᶠ y' in 𝓝[<] y, γ.fn y' = γ.fn y ∧ 0 < y' ∧ y' < y ∧ y' ∉ (F : Set ℝ) := by
    have h1 := (γ.isPiecewiseConstantBoundaryData y hyJ).filter_mono (nhdsWithin_le_nhds (s := Iio y))
    have h2 : ∀ᶠ y' in 𝓝[<] y, y' ∈ Ioo 0 y := Ioo_mem_nhdsLT hy
    have h3 : ∀ᶠ y' in 𝓝[<] y, y' ∉ (F : Set ℝ) :=
      (eventually_notMem_of_finite F.finite_toSet y).filter_mono (nhdsWithin_mono _ fun z hz => ne_of_lt hz)
    filter_upwards [h1, h2, h3] with y' e1 e2 e3 using ⟨e1, e2.1, e2.2, e3⟩
  obtain ⟨y', hfy, hy'0, hy'y, hy'F⟩ := hev.exists
  have hy'J : y' ∉ γ.jumps := fun h => hy'F (by simp only [hF, Finset.coe_union, mem_union]; exact Or.inl (Or.inl h))
  rw [← hfy]
  rcases stopWord_fn_pos_cases (κ := κ) β θ r hy'0 with h | h
  · rw [h]
    obtain ⟨p, hp, rfl⟩ := hθl
    exact ⟨p, hp, Or.inl rfl⟩
  · obtain ⟨y₀, hy₀, hA₀, hf₀⟩ := exists_alive_eq_of_markPos_lt hw hw0 hT h
    have hy₀J : y₀ ∉ β.jumps := fun hJ => hy'F (by
      simp only [hF, Finset.coe_union, mem_union]
      exact Or.inl (Or.inr (Finset.mem_image.2 ⟨y₀, hJ, hf₀⟩)))
    have hval : γ.fn y' = β.fn y₀ := by
      rw [← hf₀]
      exact stopWord_fn_fwdMap hκ β θ r hy₀ hA₀ hy₀J (by rw [hf₀]; exact hy'J)
    rw [hval]
    refine hM y₀ hy₀ hy₀J fun x hx => ?_
    by_contra hge
    push Not at hge
    -- right of the new record, the old profile stays above `y₀`
    have hright : ∀ x', a₁ < x' → y₀ < m x' := by
      intro x' hx'
      obtain ⟨hx'a, hA', heq⟩ := hrel x' hx'
      by_contra hle'
      push Not at hle'
      have hpos' := hpos x' hx'a
      have hfle : (fwdMap w T (m x')).re ≤ (fwdMap w T y₀).re := by
        rcases hle'.lt_or_eq with hlt | heq'
        · exact (hH.2.2.2.2.1 _ _ hpos' hlt hA' hA₀).le
        · rw [heq']
      have := hymid x' hx'
      rw [heq] at this
      linarith
    rcases lt_or_ge a₁ x with hxa₁ | hxa₁
    · exact absurd (hright x hxa₁) (not_lt.2 hge)
    · have haa : a < a₁ := lt_of_lt_of_le hx hxa₁
      have hcont : ContinuousAt m a₁ := hm.2.1.continuousAt (Ioi_mem_nhds haa)
      have hl : m a₁ ≤ y₀ := by
        refine le_of_tendsto (hcont.tendsto.mono_left (nhdsWithin_le_nhds (s := Iio a₁))) ?_
        filter_upwards [Ioo_mem_nhdsLT haa] with z hz
        by_contra hlt
        push Not at hlt
        exact hdead z hz.1 hz.2 (hH.2.1 y₀ (m z) hy₀ hlt hA₀)
      have hr : y₀ ≤ m a₁ := by
        refine ge_of_tendsto (hcont.tendsto.mono_left (nhdsWithin_le_nhds (s := Ioi a₁))) ?_
        filter_upwards [self_mem_nhdsWithin] with z hz
        exact (hright z hz).le
      have heq : y₀ = m a₁ := le_antisymm hr hl
      apply hy'F
      have : y' = (fwdMap w T (m a₁)).re := by rw [← hf₀, heq]
      simp only [hF, Finset.coe_union, mem_union, Finset.coe_singleton, mem_singleton_iff]
      exact Or.inr this

/-- **The left side stays admissible for the lower flow** (SB2: "All these old groups are admissible"): the new left
side `−λ − θχ` is admissible for the angle `−π/2` because `θ > −π/2` and `χ > 0`. -/
theorem left_launch (hκ : 0 < κ) (hκ4 : κ < 4) {β : BoundaryWord}
    (hL : ∀ y, y < 0 → y ∉ β.jumps → β.fn y + -(Real.pi / 2) * chiC κ < sleLambda κ) {θ : ℝ}
    (hθ : -(Real.pi / 2) < θ) (r : RecData) :
    ∀ y, y < 0 → y ∉ (stopWord κ (β, θ, r)).jumps →
      (stopWord κ (β, θ, r)).fn y + -(Real.pi / 2) * chiC κ < sleLambda κ := by
  intro y hy _
  rcases stopWord_fn_neg_mem hκ β θ r hy with h | ⟨x, hx, hxJ, h⟩
  · rw [h]
    have hχ := Sec4.chiC_pos hκ hκ4
    have hl := Sec4.sleLambda_pos hκ
    have : 0 < θ * chiC κ + Real.pi / 2 * chiC κ := by rw [← add_mul]; exact mul_pos (by linarith) hχ
    linarith
  · rw [h]
    exact hL x hx hxJ

/-- **The step of the upper invariant** through a piece of a schedule angle `θ > −π/2` stopped at an interior tip:
the stop word satisfies the invariant at the new state. -/
theorem uInv_launch (hκ : 0 < κ) (hκ4 : κ < 4) (hb : IsPiecewiseConstantBoundaryData b jumps) {β : BoundaryWord}
    {s : ExplState} (hI : UInv κ b jumps u l β s) (k : ℕ) {θ : ℝ} (hθl : ∃ p ∈ l, θ = p.1)
    (hθ : -(Real.pi / 2) < θ) {D : (ℝ≥0 → ℝ) × ℝ≥0∞} {t : ℝ≥0∞} (hreg : IsRegularDriver D) (ht : t ≠ ⊤)
    (htD : t < D.2) :
    UInv κ b jumps u l (stopWord κ (β, θ, recOf t D)) (ExplState.launch s k D θ t) := by
  obtain ⟨hS, hO, hM, hL⟩ := hI
  obtain ⟨hS₁, -, hdead, hrel⟩ := uState_launch hS k θ hreg ht htD
  exact ⟨hS₁, rOrig_launch hκ hb θ hS.2.2.1.1 hS.2.2.2.1 hS₁.2.2.1.2.1 hO hrel,
    mid_launch hκ hθl hS.2.2.1 hS.2.2.2.1 hM hdead hrel, left_launch hκ hκ4 hL hθ _⟩

end InteractingSLE.Theorem14.SB.Lh
