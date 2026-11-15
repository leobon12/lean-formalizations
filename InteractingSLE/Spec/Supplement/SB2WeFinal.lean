/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.SB2WeInd
import InteractingSLE.Spec.Supplement.SB2WdFinal

/-!
# SB2(1)'s second clause read off at a launch

Packet PROVE-T14-SB2WORD (round 2, ruling R120, D10 step 3). At a launch of the lower walk, in the launch chart `c`
with the entry `m = e_L` at `L = min (A ∩ ℝ)`, the staged word `β` satisfies `SecondClause`:

* there is a set `S` of original-real points on which the chart's profile is strictly increasing, the chart is
  continuous and free (it reflects), and the word is the original word (off finite sets) — "All original-real groups …
  have their original weights, because the map reflects positively outside the old real base" (p. 632);
* off finite sets every chart point is the image of a point of `S` or an old lower-side point of height exactly
  `−λ + (π/2)χ` lying right of the entry `m` (p. 632: "the active lower-flow sides … have height `−λ − φχ`");
* points of `S` with images right of `m` lie at or right of the upper seed `u`, those with images left of `m` lie left
  of `u` (the two sides of the relative upper flow are the two physical sides).

Results: `realMin_le_stRecL` (`L ≤ recL`, from `RecLBound`), **`secondClause_of_lwo`** (deterministic).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology Metric
open scoped NNReal ENNReal
open QuantumZipper (chiC H)
open LQGMetric (DistOn)

universe u

namespace InteractingSLE.Theorem14.SB.Lv

open Exist Exist.Staged Exist.StagedLaw Restart GW1W

variable {κ : ℝ} {b : ℝ → ℝ} {jumps : Finset ℝ}

/-- **SB2(1)'s second clause** in a chart `c` with entry `m`, for the upper seed `u`, read on the data
`(b', jumps')`. -/
def SecondClause (κ : ℝ) (b : ℝ → ℝ) (jumps : Finset ℝ) (c : Chart) (u m : ℝ) (b' : ℝ → ℝ)
    (jumps' : Finset ℝ) : Prop :=
  IsRealChart c ∧ ∃ (S : Set ℝ) (Fx Fy : Finset ℝ),
    StrictMonoOn (rProf c) S ∧
    (∀ x ∈ S, ContinuousAt c.1 (x : ℂ) ∧ ChartFree c x) ∧
    (∀ x ∈ S, x ∉ jumps → x ∉ Fx → rProf c x ∉ jumps' → b' (rProf c x) = b x) ∧
    (∀ y, y ∉ jumps' → y ∉ Fy →
      (b' y = -sleLambda κ - -(Real.pi / 2) * chiC κ ∧ m ≤ y) ∨ ∃ x ∈ S, rProf c x = y) ∧
    (∀ x ∈ S, m < rProf c x → u ≤ x) ∧ (∀ x ∈ S, rProf c x < m → x < u)

/-- **The leftmost real point of the retained prefix is at or left of the left record** (`RecLBound`). -/
theorem realMin_le_stRecL {spec : ExplSpec} {D : ℕ → (ℝ≥0 → ℝ) × ℝ≥0∞} {n : ℕ} {u : ℝ} (hu : u ≤ 0)
    (hAc : IsCompact (prefixPhysSet κ b jumps spec D n ∪ ((↑) : ℝ → ℂ) '' Icc u 0))
    (hB : RecLBound (ExplState.run κ b jumps spec D n)) :
    realMin (prefixPhysSet κ b jumps spec D n ∪ ((↑) : ℝ → ℂ) '' Icc u 0) ≤
      stRecL (ExplState.run κ b jumps spec D n) := by
  set A := prefixPhysSet κ b jumps spec D n ∪ ((↑) : ℝ → ℂ) '' Icc u 0 with hAdef
  have hLA : ∀ y : ℝ, (y : ℂ) ∈ A → realMin A ≤ y := fun y hy => FinRel.realMin_le_of_mem hAc hy
  have hLu : realMin A ≤ u := hLA u (Or.inr ⟨u, ⟨le_rfl, hu⟩, rfl⟩)
  by_contra hlt
  push Not at hlt
  set x := (stRecL (ExplState.run κ b jumps spec D n) + realMin A) / 2 with hx
  obtain ⟨p, hp, z, hz, hz0, hzx⟩ := hB x (by rw [hx]; linarith) (by rw [hx]; linarith)
  have hzA : ((z.re : ℝ) : ℂ) ∈ A := by
    have e : ((z.re : ℝ) : ℂ) = z := Complex.ext (by simp) (by simp [hz0])
    rw [e]
    exact Or.inl (Or.inl (Or.inr (mem_iUnion₂.2 ⟨p, hp, hz⟩)))
  have := hLA z.re hzA
  rw [hx] at hzx
  linarith

/-- **SB2(1)'s second clause from the left-side invariants** (one sample). -/
theorem secondClause_of_lwo {θ : ℝ} (hθ : θ = -(Real.pi / 2)) {spec : ExplSpec} (hspec : spec.1 = 0)
    {D : ℕ → (ℝ≥0 → ℝ) × ℝ≥0∞} (hRL : LuM.RegLaunches κ b jumps spec D) {n : ℕ}
    (hnot : stStatus (ExplState.run κ b jumps spec D n) ≠ GW1Conn.stDone)
    (hc : IsRealChart (stChart (ExplState.run κ b jumps spec D n))) {β : BoundaryWord}
    (hI : LWO κ θ b jumps β (ExplState.run κ b jumps spec D n))
    (harc : ∀ a ∈ (ExplState.run κ b jumps spec D n).2.1, a ⊆ Ici 0) {u : ℝ} (hu : u ≤ 0)
    (hAc : IsCompact (prefixPhysSet κ b jumps spec D n ∪ ((↑) : ℝ → ℂ) '' Icc u 0)) :
    SecondClause κ b jumps (stChart (ExplState.run κ b jumps spec D n)) u
      (Lx.leftEntry (stChart (ExplState.run κ b jumps spec D n))
        (realMin (prefixPhysSet κ b jumps spec D n ∪ ((↑) : ℝ → ℂ) '' Icc u 0))) β.fn β.jumps := by
  subst hθ
  set s := ExplState.run κ b jumps spec D n with hsdef
  set c := stChart s with hcdef
  set A := prefixPhysSet κ b jumps spec D n ∪ ((↑) : ℝ → ℂ) '' Icc u 0 with hAdef
  set L := realMin A with hLdef
  set m := Lx.leftEntry c L with hmdef
  obtain ⟨⟨hs, -, -, hC, hPB, h0⟩, ⟨S, Fx, Fy, hSL, hSR, hSm, hSc, hSo, hSy, hSloc⟩, hRB⟩ := hI
  have hLr : L ≤ stRecL s := realMin_le_stRecL hu hAc hRB
  -- the hull model and the real boundary values left of `L`
  have hLA : ∀ y : ℝ, (y : ℂ) ∈ A → L ≤ y := fun y hy => FinRel.realMin_le_of_mem hAc hy
  have hAf : fillH A = fillH (prefixPhysSet κ b jumps spec D n) := Lw.fillH_union_real _ _
  obtain ⟨M, hK⟩ := Lw.exists_hullModel_fill spec D hRL n hnot
  have hcc := (GW2aCont.isConformal_runChart (κ := κ) (b := b) (jumps := jumps) spec D n
    fun j _ c θ h => hRL j c θ h).1
  obtain ⟨g, hgc, hgi, -, -⟩ := Lw.exists_bdryMap_of_hasProperBdryExt hcc
    (GW1P.isClosed_pieces_run (κ := κ) (b := b) (jumps := jumps) spec D hRL n).1
  have hfree : ∀ x : ℝ, x < L → ∃ ρ > 0, Disjoint (ball (x : ℂ) ρ) M.hull := fun x hx => by
    obtain ⟨ρ, hρ, hd⟩ := Lw.exists_ball_disjoint_fillH hAc fun y hy => lt_of_lt_of_le hx (hLA y hy)
    rw [hAf, ← hK] at hd
    exact ⟨ρ, hρ, hd⟩
  obtain ⟨he, -, -⟩ := GW1Ext.bdryValue_facts hcc M hgc hgi hfree
  have hm := Lx.isLeftEntryValue_runChart spec D hRL n hnot hAc hAf hLA
  have hlim : Tendsto (Lx.bdryValue c) (𝓝[<] L) (𝓝 m) := by
    obtain ⟨e, he', hlim⟩ := hm
    refine hlim.congr' (eventually_nhdsWithin_of_forall fun x hx => ?_)
    have h1 := Lx.tendsto_bdryValue (he' x hx) (by simp)
    rw [h1.1, Complex.ofReal_re]
  have hbv : ∀ x, x < L → Lx.bdryValue c x = rProf c x := fun x hxL => by
    have := GW1P.neBot_nhdsWithin_H (Lw.ofReal_mem_Hbar x)
    have h1 := tendsto_nhds_unique (he x hxL)
      ((hC x (lt_of_lt_of_le hxL hLr)).tendsto.mono_left nhdsWithin_le_nhds)
    rw [hc.eq_ofReal x] at h1
    exact_mod_cast h1
  have hlimr : Tendsto (rProf c) (𝓝[<] L) (𝓝 m) :=
    hlim.congr' (eventually_nhdsWithin_of_forall fun x hx => hbv x hx)
  have hNB : (𝓝[<] L).NeBot := inferInstance
  -- `m` is at most every value right of the image of `(−∞, L)`
  have hm_le : ∀ y, (∀ x, x < L → rProf c x < y) → m ≤ y := fun y hy =>
    le_of_tendsto hlimr (eventually_nhdsWithin_of_forall fun x hx => (hy x hx).le)
  -- the leftmost real point of `A` is right of the record or right of `u`
  have hLmem : (L : ℂ) ∈ A := by
    have hcl : IsClosed {x : ℝ | (x : ℂ) ∈ A} := hAc.isClosed.preimage Complex.continuous_ofReal
    have hne : {x : ℝ | (x : ℂ) ∈ A}.Nonempty := ⟨u, Or.inr ⟨u, ⟨le_rfl, hu⟩, rfl⟩⟩
    have hbdd : BddBelow {x : ℝ | (x : ℂ) ∈ A} := ⟨L, fun y hy => hLA y hy⟩
    exact hcl.csInf_mem hne hbdd
  have hLcase : stRecL s ≤ L ∨ u ≤ L := by
    rcases hLmem with ((h1 | h2) | h3) | h4
    · rw [mem_singleton_iff, hspec] at h1
      left
      have : L = 0 := by exact_mod_cast h1
      rw [this]; exact h0
    · left
      obtain ⟨p, hp, hz⟩ := mem_iUnion₂.1 h2
      have := hPB p hp _ hz (by simp)
      simpa using this
    · left
      obtain ⟨a, ha, x, hx, hxL⟩ := mem_iUnion₂.1 h3
      have hxL' : x = L := by exact_mod_cast hxL
      rw [← hxL']
      exact h0.trans (harc a ha hx)
    · right
      obtain ⟨x, hx, hxL⟩ := h4
      have hxL' : x = L := by exact_mod_cast hxL
      rw [← hxL']
      exact hx.1
  have hLu : L ≤ u := hLA u (Or.inr ⟨u, ⟨le_rfl, hu⟩, rfl⟩)
  refine ⟨hc, S, Fx, Fy, hSm, hSc, hSo, fun y hyJ hyF => ?_, fun x hx hxm => ?_, fun x hx hxm => ?_⟩
  · rcases hSy y hyJ hyF with ⟨hβ, hrt⟩ | h
    · exact Or.inl ⟨hβ, hm_le y fun x hx => hrt x (lt_of_lt_of_le hx hLr)⟩
    · exact Or.inr h
  · -- right of `m`: at or right of `u`
    rcases hSloc x hx with hxr | hx0
    · by_contra hxu
      push Not at hxu
      rcases lt_or_ge x L with hxL | hxL
      · -- then the image is left of `m`
        obtain ⟨x', hx'1, hx'2⟩ := exists_between hxL
        have h1 : rProf c x < rProf c x' :=
          hs.strictMonoOn (show x ∈ Iio (stRecL s) from hxr)
            (show x' ∈ Iio (stRecL s) from lt_of_lt_of_le hx'2 hLr) hx'1
        have h2 : rProf c x' ≤ m :=
          ge_of_tendsto hlimr (Filter.mem_of_superset (Ioo_mem_nhdsLT hx'2) fun z hz =>
            (hs.strictMonoOn (show x' ∈ Iio (stRecL s) from lt_of_lt_of_le hx'2 hLr)
              (show z ∈ Iio (stRecL s) from lt_of_lt_of_le hz.2 hLr) hz.1).le)
        linarith
      · -- then `L < u`, so `L` is right of the record
        have hLu' : L < u := lt_of_le_of_lt hxL hxu
        rcases hLcase with h | h
        · linarith
        · linarith
    · linarith
  · -- left of `m`: left of `L ≤ u`
    rcases hSloc x hx with hxr | hx0
    · by_contra hxu
      push Not at hxu
      have hxL : L ≤ x := le_trans hLu hxu
      have : m ≤ rProf c x := hm_le (rProf c x) fun x' hx' =>
        hs.strictMonoOn (show x' ∈ Iio (stRecL s) from lt_of_lt_of_le hx' hLr)
          (show x ∈ Iio (stRecL s) from hxr) (lt_of_lt_of_le hx' hxL)
      linarith
    · -- a point at or right of `0` maps right of the whole left ray
      have : m ≤ rProf c x := hm_le (rProf c x) fun x' hx' => by
        have hx'r : x' < stRecL s := lt_of_lt_of_le hx' hLr
        exact hSm (hSL x' hx'r) hx (by linarith [h0])
      linarith

/-- **The second clause passes to data agreeing off finite sets** (the exceptional sets absorb the difference). -/
theorem SecondClause.of_eq_off {c : Chart} {u m : ℝ} {b₁ b₂ : ℝ → ℝ} {J₁ J₂ : Finset ℝ}
    (h : SecondClause κ b jumps c u m b₁ J₁) (heq : ∀ y ∉ J₂ ∪ J₁, b₂ y = b₁ y) :
    SecondClause κ b jumps c u m b₂ J₂ := by
  classical
  obtain ⟨hc, S, Fx, Fy, hSm, hSc, hSo, hSy, hSr, hSl⟩ := h
  have hfin : ({x | x ∈ S ∧ rProf c x ∈ J₁} : Set ℝ).Finite := by
    refine Set.Finite.of_finite_image (f := rProf c) (J₁.finite_toSet.subset ?_) ?_
    · rintro _ ⟨x, hx, rfl⟩
      exact hx.2
    · exact hSm.injOn.mono fun x hx => hx.1
  refine ⟨hc, S, Fx ∪ hfin.toFinset, Fy ∪ J₁, hSm, hSc, fun x hx hxJ hxF hzJ => ?_, fun y hyJ hyF => ?_, hSr, hSl⟩
  · have hz1 : rProf c x ∉ J₁ := fun h' =>
      hxF (Finset.mem_union_right _ ((Set.Finite.mem_toFinset _).2 ⟨hx, h'⟩))
    rw [heq _ (by simp [hzJ, hz1])]
    exact hSo x hx hxJ (fun h' => hxF (Finset.mem_union_left _ h')) hz1
  · have hy1 : y ∉ J₁ := fun h' => hyF (Finset.mem_union_right _ h')
    rw [heq y (by simp [hyJ, hy1])]
    exact hSy y hy1 (fun h' => hyF (Finset.mem_union_left _ h'))

end InteractingSLE.Theorem14.SB.Lv
