/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.SB2WdInd
import InteractingSLE.Spec.Supplement.GW1ExtTip

/-!
# SB2(1)'s active word from the left-side invariant: `SB2StageActiveWordStatement`

Packet PROVE-T14-SB2WORD, step 4 of `planning/handoffs/PROVE-T14-SB2FIN5.md` §R3. At a launch of the lower walk the
staged word has SB2(1)'s active word on `(m, 0)` (supplement p. 632, `source/spec/p625-671.md` L127), where `m` is the
entry `e_L` of the launch chart at `L = min (A ∩ ℝ)`, `A` the retained prefix with the bridge `[u, 0]`:

* right of the image of the untouched left ray the word is low (`LLow`);
* otherwise the point is the image of a point `x'` of the untouched left ray, where the word is the original word
  (`LOrig`), and `x' > u`: the chart's real boundary values are its values on the ray (`LCont`), increasing on
  `(−∞, L)` (continuous and injective, `GW1Ext.bdryValue_facts`), with limit `m` at `L⁻`; a point of the ray at or
  left of `u` therefore maps at or left of `m`, using that `L < recL` forces `L = u` (the real points of the pieces are
  right of the left record, `PiecesRealBound`; the connectors lie in `[0, ∞)`).

* **`isActiveWord_of_lw`** (deterministic, one sample);
* **`sb2StageActiveWordStatement`**: `SB2StageActiveWordStatement` holds (no named input);
* **`sb2ActiveWordAmbStatement`**: hence `SB2ActiveWordAmbStatement`, SB2(1)'s first input.
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

/-- **SB2(1)'s active word from the left-side invariant** (one sample). For a run with regular launches, not finished
at `n`, with a real chart, the left-side invariant for the word `β` and every connector in `[0, ∞)`, at every point
`y` of `(m, 0)` off the jumps of `β`, `m` the entry of the run chart at `L = realMin (prefix ∪ [u, 0])`, the word is
low or is an original height of the bridge `(u, 0)`. -/
theorem isActiveWord_of_lw {θ : ℝ} {spec : ExplSpec} (hspec : spec.1 = 0) {D : ℕ → (ℝ≥0 → ℝ) × ℝ≥0∞}
    (hRL : LuM.RegLaunches κ b jumps spec D) {n : ℕ}
    (hnot : stStatus (ExplState.run κ b jumps spec D n) ≠ GW1Conn.stDone)
    (hc : IsRealChart (stChart (ExplState.run κ b jumps spec D n))) {β : BoundaryWord}
    (hLW : LW κ θ b jumps β (ExplState.run κ b jumps spec D n))
    (harc : ∀ a ∈ (ExplState.run κ b jumps spec D n).2.1, a ⊆ Ici 0) {u : ℝ} (hu : u ≤ 0)
    (hAc : IsCompact (prefixPhysSet κ b jumps spec D n ∪ ((↑) : ℝ → ℂ) '' Icc u 0)) :
    ∀ y ∈ Ioo (Lx.leftEntry (stChart (ExplState.run κ b jumps spec D n))
        (realMin (prefixPhysSet κ b jumps spec D n ∪ ((↑) : ℝ → ℂ) '' Icc u 0))) 0, y ∉ β.jumps →
      β.fn y ≤ -sleLambda κ - θ * chiC κ ∨ ∃ x ∈ Ioo u 0, x ∉ jumps ∧ β.fn y = b x := by
  set s := ExplState.run κ b jumps spec D n with hsdef
  set c := stChart s with hcdef
  set A := prefixPhysSet κ b jumps spec D n ∪ ((↑) : ℝ → ℂ) '' Icc u 0 with hAdef
  set L := realMin A with hLdef
  set m := Lx.leftEntry c L with hmdef
  obtain ⟨hs, hO, hL, hC, hB, h0⟩ := hLW
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
  obtain ⟨he, hcont, hinv⟩ := GW1Ext.bdryValue_facts hcc M hgc hgi hfree
  have hm := Lx.isLeftEntryValue_runChart spec D hRL n hnot hAc hAf hLA
  have hlim : Tendsto (Lx.bdryValue c) (𝓝[<] L) (𝓝 m) := by
    obtain ⟨e, he', hlim⟩ := hm
    refine hlim.congr' (eventually_nhdsWithin_of_forall fun x hx => ?_)
    have h1 := Lx.tendsto_bdryValue (he' x hx) (by simp)
    rw [h1.1, Complex.ofReal_re]
  -- on the untouched left ray the boundary values are the chart values
  have hbv : ∀ x, x < L → x < stRecL s → Lx.bdryValue c x = rProf c x := fun x hxL hxr => by
    have := GW1P.neBot_nhdsWithin_H (Lw.ofReal_mem_Hbar x)
    have h1 := tendsto_nhds_unique (he x hxL) ((hC x hxr).tendsto.mono_left nhdsWithin_le_nhds)
    rw [hc.eq_ofReal x] at h1
    exact_mod_cast h1
  -- the leftmost real point of `A` is right of the left record or right of `u`
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
      have := hB p hp _ hz (by simp)
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
  -- continuity of the profile on the untouched ray
  have hcr : ∀ x, x < stRecL s → ContinuousAt (rProf c) x := fun x hx =>
    Complex.continuous_re.continuousAt.comp ((hC x hx).comp Complex.continuous_ofReal.continuousAt)
  intro y ⟨hym, hy0⟩ hyJ
  by_cases hall : ∀ x, x < stRecL s → rProf c x < y
  · exact Or.inl (hL y hy0 hyJ hall)
  right
  push Not at hall
  obtain ⟨x₁, hx₁, hx₁y⟩ := hall
  obtain ⟨x', hx'r, -, hx'y⟩ := hs.exists_eq hx₁ hx₁y
  -- the point of the ray lies right of `u`
  have hux : u < x' := by
    by_contra hxu
    push Not at hxu
    rcases lt_or_ge x' L with hxL | hxL
    · -- the boundary values increase on `(x' − 1, L)`
      have hsub : Ioo (x' - 1) L ⊆ Iio L := fun z hz => hz.2
      have hmono := (hcont.mono hsub).strictMonoOn_of_injOn_Ioo (by linarith : x' - 1 < L)
        (fun z₁ hz₁ z₂ hz₂ hz => by
          have h1 := hinv z₁ hz₁.2
          rw [hz, hinv z₂ hz₂.2] at h1
          exact_mod_cast h1.symm)
      have hm1 : x' - 1 / 2 ∈ Ioo (x' - 1) L := ⟨by linarith, by linarith⟩
      have hm2 : x' ∈ Ioo (x' - 1) L := ⟨by linarith, hxL⟩
      have hval : Lx.bdryValue c (x' - 1 / 2) < Lx.bdryValue c x' := by
        rw [hbv _ (by linarith) (by linarith), hbv _ hxL hx'r]
        exact hs.strictMonoOn (mem_Iio.2 (by linarith : x' - 1 / 2 < stRecL s))
          (show x' ∈ Iio (stRecL s) from hx'r) (by linarith)
      have hinc : StrictMonoOn (Lx.bdryValue c) (Ioo (x' - 1) L) := by
        rcases hmono with h | h
        · exact h
        · exact absurd (h hm1 hm2 (by linarith)) (not_lt.2 hval.le)
      set x'' := (x' + L) / 2 with hx''
      have hx''m : x'' ∈ Ioo (x' - 1) L := ⟨by linarith, by linarith⟩
      have hge : Lx.bdryValue c x'' ≤ m := by
        refine ge_of_tendsto hlim ?_
        filter_upwards [Ioo_mem_nhdsLT (show x'' < L by linarith)] with z hz
        exact (hinc hx''m ⟨by linarith [hz.1], hz.2⟩ hz.1).le
      have hlt : Lx.bdryValue c x' < Lx.bdryValue c x'' := hinc hm2 hx''m (by linarith)
      rw [hbv _ hxL hx'r, hx'y] at hlt
      linarith
    · -- then `L < recL`, so `L = u = x'` and `m` is the profile at `L`
      have hLr : L < stRecL s := lt_of_le_of_lt hxL hx'r
      have huL : u ≤ L := hLcase.resolve_left (not_le.2 hLr)
      have hxe : x' = L := le_antisymm (hxu.trans huL) hxL
      have hlim' : Tendsto (rProf c) (𝓝[<] L) (𝓝 m) :=
        hlim.congr' (eventually_nhdsWithin_of_forall fun z hz => hbv z hz (lt_trans hz hLr))
      have hm' : m = rProf c L :=
        tendsto_nhds_unique hlim' ((hcr L hLr).tendsto.mono_left nhdsWithin_le_nhds)
      rw [hxe] at hx'y
      linarith
  -- the word is the original word near `x'`
  have hP : ∀ᶠ x'' in 𝓝 x', u < x'' ∧ β.fn (rProf c x'') = β.fn y := by
    have h1 := (hcr x' hx'r).eventually (by rw [hx'y]; exact β.isPiecewiseConstantBoundaryData y hyJ)
    filter_upwards [Ioi_mem_nhds hux, h1] with z h2 h3 using ⟨h2, h3⟩
  obtain ⟨x'', hx''r, hx''J, hcx''J, hux'', hfn⟩ := exists_near_avoid_left hs.strictMonoOn hx'r jumps β.jumps hP
  exact ⟨x'', ⟨hux'', lt_of_lt_of_le hx''r h0⟩, hx''J, by rw [← hfn, hO x'' hx''r hx''J hcx''J]⟩

/-- **SB2(1)'s stage active word** (`SB2StageActiveWordStatement`, no named input): the witness of GW1's induction
with the left-side invariant (`GW1W.exists_witness_right_lw`; GW1's ambient bound from `LowerLeftAdmissible`) has, at
every launch `k + 1` of the lower walk, SB2(1)'s active word (`isActiveWord_of_lw`, connectors in `[0, ∞)` by
`ae_arcs_subset_Ici`). -/
theorem sb2StageActiveWordStatement : SB2StageActiveWordStatement.{u} := by
  intro κ hκ _ b jumps hb Ω _ _ P _ h hh hadm E hE hER hreg k u hu
  set w : ExplSpec := boundaryWalkSpec b jumps (-(Real.pi / 2)) true with hwdef
  have hw := isBoundaryContinuedProgram_boundaryWalkSpec b jumps (θ := -(Real.pi / 2))
    ⟨le_rfl, by linarith [Real.pi_pos]⟩ true
  have hamb : ∀ t, t < 0 → t ∉ jumps → b t + -(Real.pi / 2) * chiC κ < sleLambda κ :=
    fun t ht htJ => Ly.height_lt_of_cumWeightLeft hκ (hadm t ht htJ)
  obtain ⟨β, Y, hW, hae⟩ := GW1W.exists_witness_right_lw hκ hb hh (hE w hw) (hreg w) (hER w hw) hamb (k + 1)
  refine ⟨β, Y, hW, ?_⟩
  have harc := ae_arcs_subset_Ici hκ hb hh (hE w hw) (hreg w) hamb
  have hRL := GW1W.regLaunches_of_stagedPiecesRegular (hER w hw)
  filter_upwards [hae, harc, hRL] with ω hω ha hr hF
  obtain ⟨⟨c₀, θ₀⟩, hcθ⟩ := Option.ne_none_iff_exists'.1 hF
  obtain ⟨hI, -, -, hLW⟩ := hω hF
  have hAc := Lx.isCompact_lowerPrefix (u := u) hr hF
  have hnot := Lx.stStatus_ne_done_of_launches _ _ hcθ
  unfold launchEntry
  rw [launchChart_eq hcθ, (eq_launch_of_launches _ _ hcθ).2.2]
  exact isActiveWord_of_lw (by simp [hwdef, boundaryWalkSpec]) hr hnot hI.2.1.1 hLW (ha (k + 1)) hu hAc

/-- **SB2(1)'s active word for every witness of the launch clause** (`SB2ActiveWordAmbStatement`, SB2(1)'s first
input), with no named input. -/
theorem sb2ActiveWordAmbStatement : SB2ActiveWordAmbStatement.{u} :=
  sb2ActiveWordAmbStatement_of_stage sb2StageActiveWordStatement

/-- **SB2(1) in the ambient form from Theorem 1.3 and the driver link alone**
(`sb2UpperLaunchEntryLAmbStatement_of_parts` with the active word proved). -/
theorem sb2UpperLaunchEntryLAmbStatement_of_driverLink (h13 : Exist.Theorem13Statement.{u})
    (hd : SB2DriverLinkAmbStatement.{u}) : Ly.SB2UpperLaunchEntryLAmbStatement.{u} :=
  sb2UpperLaunchEntryLAmbStatement_of_parts h13 sb2ActiveWordAmbStatement hd

end InteractingSLE.Theorem14.SB.Lv
