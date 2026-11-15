/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW1ActiveWord

/-!
# Lemma GW1's active-word classification: the right walk, one stage (deterministic)

Packet PROVE-T14-GW1W. Lemma GW1, proof (`source/spec/p577-624.md` L949–L983, pp. 618–620), for the right boundary
walk (angle `θ`, in the application `θ = −π/2`). At a launch of the walk, the state and the conditional word `β` of
the launched piece satisfy the invariant `RInv`:

* (`LeftLow`) the word is admissible left of the seed: `β + θχ < λ` there ("all active old raw fibers … are on the
  protected terminal tail"; "the still untouched original left intervals …");
* (`RProf`) the chart maps the physical ray right of the current right record increasingly onto `(0, ∞)` ("A
  hydrodynamic chart of `U_j` is increasing … on this ray"; "its incident ray from `w_j` toward `y` is the untouched
  original right ray");
* (`ROrig`) there the word is the original boundary word ("it has the exact zero lift there").

This file proves that a stage of the walk that ends at a right threshold restores the invariant at the next launch
(`rInv_next`), given the two facts of the stage that are probabilistic: the record of the piece is good and the
original height just right of the new record is low (the colliding group of the threshold is on the right). The
real-flow input is `exists_alive_fwdMap_lt`: at a time when a positive point is swallowed, the real flow comes
arbitrarily close to `0` on the alive points.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Filter Set Topology Finset
open scoped NNReal ENNReal
open QuantumZipper (IsForwardSol chiC fwdMap)

namespace InteractingSLE

namespace Theorem14

namespace GW1W

open Exist Exist.StagedLaw Exist.Staged Restart

/-! ### The real flow at a swallowing time -/

section Flow

variable {W : ℝ → ℝ}

/-- **Contraction of the real flow**: for `0 < y₁ < q` alive on `[0, s]`, `f_s(q) − f_s(y₁) ≤ q − y₁`. -/
theorem fwdMap_sub_le (hW : Continuous W) (hW0 : W 0 = 0) {y₁ q s : ℝ} (hy₁ : 0 < y₁) (hyq : y₁ < q)
    (hs : 0 ≤ s) {v u : ℝ → ℂ} (hv : IsForwardSol W (y₁ : ℂ) s v) (hu : IsForwardSol W (q : ℂ) s u) :
    (fwdMap W s q).re - (fwdMap W s y₁).re ≤ q - y₁ := by
  have hd := isMark_of_isForwardSol hW hW0 hy₁ hs hv
  have hanti := antitoneOn_re_sub_mark hW hW0 hs hd hyq hu
  have h := hanti ⟨le_rfl, hs⟩ ⟨hs, le_rfl⟩ hs
  rw [fwdMap_eq_of_isForwardSol hW hu ⟨hs, le_rfl⟩, fwdMap_eq_of_isForwardSol hW hv ⟨hs, le_rfl⟩]
  simp only at h
  rw [re_sol_zero hW0 hs hu, re_sol_zero hW0 hs hv] at h
  exact h

/-- **At a time when a positive real point is swallowed, the real flow is arbitrarily small on alive points.** -/
theorem exists_alive_fwdMap_lt (hW : Continuous W) (hW0 : W 0 = 0) {T y₀ : ℝ} (hy₀ : 0 < y₀)
    (hsw : RealSwallowAt W y₀ T) {ε : ℝ} (hε : 0 < ε) :
    ∃ q : ℝ, 0 < q ∧ (∃ u, IsForwardSol W (q : ℂ) T u) ∧ (fwdMap W T q).re < ε := by
  have hT : 0 < T := hsw.1
  have hH := isRealHalf_of hW hW0 hT.le
  set A : ℝ → Prop := fun y : ℝ => ∃ u, IsForwardSol W (y : ℂ) T u with hAdef
  set P := posInf A with hPdef
  have hy₀P : y₀ ≤ P := by
    by_contra h
    push Not at h
    exact hsw.2.2 (alive_of_posInf_lt hH h)
  -- an alive point just right of the infimum
  have hq : P < P + ε / 2 := by linarith
  obtain ⟨q, hq1, hq2⟩ := exists_between hq
  have hAq : A q := alive_of_posInf_lt hH hq1
  have hq0 : 0 < q := hy₀.trans_le (hy₀P.trans hq1.le)
  -- a point swallowed at `T` just left of the infimum
  set y₁ := max y₀ (P - ε / 2) with hy₁def
  have hy₁0 : 0 < y₁ := lt_of_lt_of_le hy₀ (le_max_left _ _)
  have hy₁P : y₁ ≤ P := max_le hy₀P (by linarith)
  have hy₁q : y₁ < q := hy₁P.trans_lt hq1
  have hdead₁ : ¬ A y₁ := by
    rcases hy₁P.lt_or_eq with hlt | heq
    · exact not_alive_of_lt_posInf hy₁0 hlt
    · rcases le_total y₀ (P - ε / 2) with h | h
      · rw [hy₁def, max_eq_right h] at heq
        linarith
      · rw [hy₁def, max_eq_left h] at heq ⊢
        exact hsw.2.2
  have hsw₁ : RealSwallowAt W y₁ T := by
    refine ⟨hT, fun s hs => ?_, hdead₁⟩
    obtain ⟨v, hv⟩ := hsw.2.1 s hs
    rcases (le_max_left y₀ (P - ε / 2)).lt_or_eq with hlt | heq
    · exact QuantumZipper.RS.exists_isForwardSol_of_lt hW hs.1 (by rw [hW0]; exact hy₀) hlt hv
    · have e : y₁ = y₀ := by rw [hy₁def]; exact heq.symm
      rw [e]
      exact ⟨v, hv⟩
  obtain ⟨u, hu⟩ := hAq
  -- the flow at `q` and at `y₁` near `T`
  have hlim₁ : Tendsto (fun s => (fwdMap W s y₁).re) (𝓝[<] T) (𝓝 0) := by
    have := (Complex.continuous_re.tendsto _).comp (tendsto_fwdMap_of_realSwallowAt hW hW0 hy₁0 hsw₁)
    rw [Complex.zero_re] at this
    exact this
  have hlimq : Tendsto (fun s => (fwdMap W s q).re) (𝓝[<] T) (𝓝 (fwdMap W T q).re) := by
    have hc : ContinuousWithinAt (fun s => (u s).re) (Icc 0 T) T :=
      (Complex.continuous_re.comp_continuousOn hu.1) T ⟨hT.le, le_rfl⟩
    have h1 : Tendsto (fun s => (u s).re) (𝓝[Ico 0 T] T) (𝓝 (u T).re) :=
      hc.tendsto.mono_left (nhdsWithin_mono _ Ico_subset_Icc_self)
    rw [← nhdsWithin_Ico_eq_nhdsLT hT] at *
    rw [fwdMap_eq_of_isForwardSol hW hu ⟨hT.le, le_rfl⟩]
    refine h1.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with s hs
    rw [fwdMap_eq_of_isForwardSol hW hu ⟨hs.1, hs.2.le⟩]
  have hle : ∀ᶠ s in 𝓝[<] T, (fwdMap W s q).re - (fwdMap W s y₁).re ≤ q - y₁ := by
    filter_upwards [Ioo_mem_nhdsLT hT] with s hs
    obtain ⟨v, hv⟩ := hsw₁.2.1 s ⟨hs.1.le, hs.2⟩
    exact fwdMap_sub_le hW hW0 hy₁0 hy₁q hs.1.le hv (QuantumZipper.isForwardSol_restrict hu hs.1.le hs.2.le)
  have hlimit := le_of_tendsto (hlimq.sub hlim₁) hle
  have hq1' : P - ε / 2 ≤ y₁ := le_max_right _ _
  refine ⟨q, hq0, ⟨u, hu⟩, ?_⟩
  rw [sub_zero] at hlimit
  linarith

end Flow

/-! ### Avoiding finitely many points -/

/-- A finite set of reals is avoided on a punctured neighbourhood. -/
theorem eventually_notMem_of_finite {S : Set ℝ} (hS : S.Finite) (x : ℝ) : ∀ᶠ y in 𝓝[≠] x, y ∉ S := by
  have h1 : (S \ {x})ᶜ ∈ 𝓝 x := (hS.sdiff).isClosed.isOpen_compl.mem_nhds (by simp)
  filter_upwards [nhdsWithin_le_nhds h1, self_mem_nhdsWithin] with y hy hyx hyS
  exact hy ⟨hyS, hyx⟩

/-- **Perturbation**: near a point of `(a, ∞)`, a strictly increasing `g` and finitely many exceptional points of the
argument and of the value can be avoided while keeping a local property. -/
theorem exists_near_avoid {g : ℝ → ℝ} {a x : ℝ} (hg : StrictMonoOn g (Ioi a)) (hx : a < x) (F G : Finset ℝ)
    {P : ℝ → Prop} (hP : ∀ᶠ x' in 𝓝 x, P x') : ∃ x', a < x' ∧ x' ∉ F ∧ g x' ∉ G ∧ P x' := by
  have hfin2 : (Ioi a ∩ g ⁻¹' (G : Set ℝ)).Finite := by
    refine Set.Finite.of_finite_image (G.finite_toSet.subset ?_) (hg.injOn.mono inter_subset_left)
    rintro _ ⟨y, hy, rfl⟩
    exact hy.2
  have hfin : ((F : Set ℝ) ∪ (Ioi a ∩ g ⁻¹' (G : Set ℝ))).Finite := F.finite_toSet.union hfin2
  have h := ((hP.and (Ioi_mem_nhds hx)).filter_mono nhdsWithin_le_nhds).and (eventually_notMem_of_finite hfin x)
  obtain ⟨x', ⟨hPx', hax'⟩, hbad⟩ := h.exists
  exact ⟨x', hax', fun h => hbad (Or.inl h), fun h => hbad (Or.inr ⟨hax', h⟩), hPx'⟩

/-! ### The right profile of a state -/

/-- **The right profile of a state**: the chart sends the real line to itself and the physical ray right of the right
record continuously and increasingly onto `(0, ∞)`. -/
def RProf (s : ExplState) : Prop :=
  IsRealChart (stChart s) ∧ RightGood (rProf (stChart s)) (stRecR s) ∧
    (∀ x, stRecR s < x → 0 < rProf (stChart s) x) ∧ ∀ ε > 0, ∃ x, stRecR s < x ∧ rProf (stChart s) x < ε

/-- **The word is the original word on the ray right of the right record** (read in the chart, off the jumps). -/
def ROrig (b : ℝ → ℝ) (jumps : Finset ℝ) (β : BoundaryWord) (s : ExplState) : Prop :=
  ∀ x, stRecR s < x → x ∉ jumps → rProf (stChart s) x ∉ β.jumps → β.fn (rProf (stChart s) x) = b x

theorem RProf.exists_eq {s : ExplState} (hs : RProf s) {y : ℝ} (hy : 0 < y) :
    ∃ x, stRecR s < x ∧ rProf (stChart s) x = y := by
  obtain ⟨x, hx, hxy⟩ := hs.2.2.2 y hy
  exact (exists_eq_iff_exists_lt hs.2.1).2 ⟨x, hx, hxy⟩

section Launch

variable {s : ExplState} {D : (ℝ≥0 → ℝ) × ℝ≥0∞}

/-- **The right profile after a launch that ends at a right threshold.** The new profile is the real flow of the
record driver composed with the old one, on the ray right of the new right record. -/
theorem rProf_launch (hs : RProf s) (k : ℕ) (θ : ℝ) (hreg : IsRegularDriver D)
    (hgood : LocalExt.IsDrvGood (recHist (recOf ⊤ D))) (hfin : D.2 ≠ ⊤)
    (hhit : ∃ x, stRecR s < x ∧ lHit (stChart s) ⊤ D x) :
    RProf (ExplState.launch s k D θ ⊤) ∧ ∀ x, stRecR (ExplState.launch s k D θ ⊤) < x →
      stRecR s < x ∧ (∃ u, IsForwardSol (rdrv (recOf ⊤ D)) (rProf (stChart s) x : ℂ) (rtime (recOf ⊤ D)) u) ∧
      rProf (stChart (ExplState.launch s k D θ ⊤)) x =
        (fwdMap (rdrv (recOf ⊤ D)) (rtime (recOf ⊤ D)) (rProf (stChart s) x)).re := by
  obtain ⟨hc, hm, hpos, hsmall⟩ := hs
  have hmin : min ⊤ D.2 ≠ ⊤ := by rwa [min_eq_right le_top]
  obtain ⟨hch, -, hrec, -, -, -⟩ := launch_eq_of_ne_top s k D θ ⊤ hmin
  have hWr : rdrv (recOf ⊤ D) = stopDrv ⊤ D := by rw [rdrv_recOf]; exact recDrv_eq_stopDrv hreg hgood
  rw [hWr, rtime_recOf]
  set W := stopDrv ⊤ D with hWdef
  set T := stopTime ⊤ D with hTdef
  have hW : Continuous W := by rw [← hWr]; exact continuous_rdrv _
  have hW0 : W 0 = 0 := stopDrv_zero hreg ⊤
  have hT0 : 0 ≤ T := stopTime_nonneg ⊤ D
  have hH := (isRealFlow_stop hreg hgood).1
  set A : ℝ → Prop := fun y : ℝ => ∃ u, IsForwardSol W (y : ℂ) T u with hAdef
  set f : ℝ → ℝ := fun y => (fwdMap W T y).re with hfdef
  set m := rProf (stChart s) with hmdef
  have hrec' : stRecR (ExplState.launch s k D θ ⊤) = newRec m (stRecR s) A := by
    rw [hrec, lRecR_eq_newRec hc]
  have hprof : rProf (stChart (ExplState.launch s k D θ ⊤)) = fun x => f (m x) := by
    funext x
    rw [hch]
    change (fwdMap W T ((stChart s).1 x)).re = (fwdMap W T (m x : ℂ)).re
    rw [hc.eq_ofReal x]
  have hle := le_newRec hm hH
  refine ⟨⟨fun x => ?_, ?_, fun x hx => ?_, fun ε hε => ?_⟩, fun x hx => ?_⟩
  · rw [hch]
    change (fwdMap W T ((stChart s).1 x)).im = 0
    rw [hc.eq_ofReal x]
    exact im_fwdMap_ofReal W hT0 _
  · rw [hprof, hrec']
    exact rightGood_comp hm hH
  · rw [hrec'] at hx
    obtain ⟨h0, hA⟩ := pos_alive_of_newRec_lt hm hH hx
    rw [hprof]
    exact hH.2.2.2.1 _ h0 hA
  · -- the hit point is swallowed at `T`
    obtain ⟨x₀, hx₀, hhit₀, hdead₀⟩ := hhit
    have hy₀ : 0 < m x₀ := hpos x₀ hx₀
    have hdead : ¬ A (m x₀) := by
      intro h
      apply hdead₀
      change ∃ u, IsForwardSol W ((stChart s).1 x₀) T u
      rw [hc.eq_ofReal x₀]
      exact h
    have hTpos : 0 < T := by
      rcases hT0.lt_or_eq with h | h
      · exact h
      · exfalso
        apply hdead
        show ∃ u, IsForwardSol W (m x₀ : ℂ) T u
        rw [← h]
        exact exists_isForwardSol_zero hW0 hy₀.ne'
    have hsw : RealSwallowAt W (m x₀) T := by
      refine ⟨hTpos, fun r hr => ?_, hdead⟩
      have := hhit₀ r hr.2
      rwa [hc.eq_ofReal x₀] at this
    obtain ⟨q, hq0, hAq, hfq⟩ := exists_alive_fwdMap_lt hW hW0 hy₀ hsw (half_pos hε)
    obtain ⟨η, hη, hηf⟩ := hH.2.2.2.2.2.1 q hq0 hAq (ε / 2) (half_pos hε)
    have hq' : q < q + η / 2 := by linarith
    have hAq' : A (q + η / 2) := hH.2.1 q _ hq0 hq' hAq
    obtain ⟨x₁, hx₁, hmx₁⟩ := RProf.exists_eq ⟨hc, hm, hpos, hsmall⟩ hq0
    obtain ⟨x₂, hx₂, hmx₂⟩ := RProf.exists_eq ⟨hc, hm, hpos, hsmall⟩ (hq0.trans hq')
    rw [← hmdef] at hmx₁ hmx₂
    have h12 : x₁ < x₂ := by
      by_contra h
      push Not at h
      rcases h.lt_or_eq with h | h
      · have := hm.1 hx₂ hx₁ h
        rw [hmx₁, hmx₂] at this
        linarith
      · rw [h] at hmx₂
        rw [hmx₂] at hmx₁
        linarith
    have hnew : newRec m (stRecR s) A ≤ x₁ := by
      refine csSup_le (insert_nonempty _ _) fun z hz => ?_
      rcases hz with rfl | ⟨hza, hzA⟩
      · exact hx₁.le
      · by_contra hzx
        push Not at hzx
        apply hzA
        have hlt : m x₁ < m z := hm.1 hx₁ hza hzx
        rw [hmx₁] at hlt
        exact hH.2.1 q _ hq0 hlt hAq
    refine ⟨x₂, by rw [hrec']; exact hnew.trans_lt h12, ?_⟩
    rw [hprof]
    change f (m x₂) < ε
    rw [hmx₂]
    have := hηf (q + η / 2) hAq' (by rw [abs_lt]; constructor <;> linarith)
    rw [abs_lt] at this
    change f (q + η / 2) < ε
    have hfq' : f q < ε / 2 := hfq
    linarith [this.2]
  · rw [hrec'] at hx
    obtain ⟨_, hA⟩ := pos_alive_of_newRec_lt hm hH hx
    refine ⟨hle.trans_lt hx, hA, ?_⟩
    rw [hprof]

/-- **The original word survives on the new right ray** (Lemma GW1, p. 620), in the form used for every launch: if the
new state has a right profile which, right of its record, is the real flow of the record driver at the record time
composed with the old profile, then the stop word is the original word there. -/
theorem rOrig_of_rel {κ : ℝ} (hκ : 0 < κ) {b : ℝ → ℝ} {jumps : Finset ℝ}
    (hb : IsPiecewiseConstantBoundaryData b jumps) {β : BoundaryWord} (hs : RProf s) (hO : ROrig b jumps β s)
    {s₁ : ExplState} {r : RecData} (θ : ℝ)
    (hrel : RProf s₁ ∧ ∀ x, stRecR s₁ < x → stRecR s < x ∧
      (∃ u, IsForwardSol (rdrv r) (rProf (stChart s) x : ℂ) (rtime r) u) ∧
      rProf (stChart s₁) x = (fwdMap (rdrv r) (rtime r) (rProf (stChart s) x)).re) :
    ROrig b jumps (stopWord κ (β, θ, r)) s₁ := by
  obtain ⟨hs₁, hrel⟩ := hrel
  set γ := stopWord κ (β, θ, r) with hγ
  set m₁ := rProf (stChart s₁) with hm₁
  intro x hx hxJ hzJ
  have hc₁ : ContinuousAt m₁ x := hs₁.2.1.2.1.continuousAt (Ioi_mem_nhds hx)
  have hP : ∀ᶠ x' in 𝓝 x, stRecR s₁ < x' ∧ b x' = b x ∧ m₁ x' ∉ γ.jumps ∧ γ.fn (m₁ x') = γ.fn (m₁ x) := by
    have h1 := hc₁.eventually (γ.isPiecewiseConstantBoundaryData (m₁ x) hzJ)
    have h2 := hc₁.eventually ((γ.jumps.finite_toSet.isClosed.isOpen_compl).mem_nhds hzJ)
    filter_upwards [Ioi_mem_nhds hx, hb x hxJ, h1, h2] with x' h0 h3 h4 h5
    exact ⟨h0, h3, h5, h4⟩
  obtain ⟨x', hx'R, hx'J, hmx'J, hx'R₁, hbx', hm₁J, hfn⟩ := exists_near_avoid hs.2.1.1 (hrel x hx).1 jumps β.jumps hP
  obtain ⟨-, hal, heq⟩ := hrel x' hx'R₁
  have hpos : 0 < rProf (stChart s) x' := hs.2.2.1 x' hx'R
  calc γ.fn (m₁ x) = γ.fn (m₁ x') := hfn.symm
    _ = γ.fn (fwdMap (rdrv r) (rtime r) (rProf (stChart s) x')).re := by rw [heq]
    _ = β.fn (rProf (stChart s) x') :=
        stopWord_fn_fwdMap hκ β θ r hpos hal hmx'J (by rw [← heq]; exact hm₁J)
    _ = b x' := hO x' hx'R hx'J hmx'J
    _ = b x := hbx'

/-- **The right profile after a launch with zero lifetime**: nothing is swallowed and the chart is unchanged. -/
theorem rProf_launch_zero (hs : RProf s) (k : ℕ) (θ : ℝ) (hreg : IsRegularDriver D) (h0 : D.2 = 0) :
    RProf (ExplState.launch s k D θ ⊤) ∧ ∀ x, stRecR (ExplState.launch s k D θ ⊤) < x →
      stRecR s < x ∧ (∃ u, IsForwardSol (rdrv (recOf ⊤ D)) (rProf (stChart s) x : ℂ) (rtime (recOf ⊤ D)) u) ∧
      rProf (stChart (ExplState.launch s k D θ ⊤)) x =
        (fwdMap (rdrv (recOf ⊤ D)) (rtime (recOf ⊤ D)) (rProf (stChart s) x)).re := by
  obtain ⟨hc, hm, hpos, hsmall⟩ := hs
  have hmin : min ⊤ D.2 ≠ ⊤ := by rw [h0]; simp
  obtain ⟨hch, -, hrec, -, -, -⟩ := launch_eq_of_ne_top s k D θ ⊤ hmin
  have hT : stopTime ⊤ D = 0 := by simp [stopTime, h0]
  have hW0 : stopDrv ⊤ D 0 = 0 := stopDrv_zero hreg ⊤
  have hprof : rProf (stChart (ExplState.launch s k D θ ⊤)) = rProf (stChart s) := by
    funext x
    rw [hch, hT]
    change (fwdMap (stopDrv ⊤ D) 0 ((stChart s).1 x)).re = _
    rw [fwdMap_zero_time hW0]
    rfl
  have hR : stRecR (ExplState.launch s k D θ ⊤) = stRecR s := by
    rw [hrec]
    unfold lRecR
    have he : {x : ℝ | stRecR s < x ∧ ¬ lAlive (stChart s) ⊤ D x} = ∅ := by
      ext x
      simp only [mem_ofPred_eq, mem_empty_iff_false, iff_false, not_and, not_not]
      intro hx
      unfold lAlive
      rw [hT, hc.eq_ofReal x]
      exact exists_isForwardSol_zero hW0 (hpos x hx).ne'
    rw [he, insert_empty_eq, csSup_singleton]
  have hrt : rtime (recOf ⊤ D) = 0 := by rw [rtime_recOf, hT]
  refine ⟨⟨fun x => ?_, ?_, fun x hx => ?_, fun ε hε => ?_⟩, fun x hx => ?_⟩
  · rw [hch, hT]
    change (fwdMap (stopDrv ⊤ D) 0 ((stChart s).1 x)).im = 0
    rw [fwdMap_zero_time hW0]
    exact hc x
  · rw [hprof, hR]; exact hm
  · rw [hprof]; rw [hR] at hx; exact hpos x hx
  · rw [hprof, hR]; exact hsmall ε hε
  · rw [hR] at hx
    refine ⟨hx, ?_, ?_⟩
    · rw [hrt]
      exact exists_isForwardSol_zero (rdrv_zero _) (hpos x hx).ne'
    · rw [hprof, hrt, fwdMap_zero_time (rdrv_zero _)]
      simp

end Launch

/-! ### The boundary continuation -/

section Cont

open PiecewiseConstantBoundaryData (rightLim leftLim jumpSet)

theorem stChart_moveAlong (s : ExplState) (r : Bool) (w : ℝ) (m : Bool) :
    stChart (ExplState.moveAlong s r w m) = (stChart s).recenter ((stChart s).1 w).re := by
  obtain ⟨pieces, arcs, ret, lau, chart, st, pt, ang, rR, rL⟩ := s
  rfl

theorem stRecR_moveAlong_true (s : ExplState) (w : ℝ) (m : Bool) :
    stRecR (ExplState.moveAlong s true w m) = max (stRecR s) w := by
  obtain ⟨pieces, arcs, ret, lau, chart, st, pt, ang, rR, rL⟩ := s
  rfl

theorem stPt_moveAlong (s : ExplState) (r : Bool) (w : ℝ) (m : Bool) : stPt (ExplState.moveAlong s r w m) = w := by
  obtain ⟨pieces, arcs, ret, lau, chart, st, pt, ang, rR, rL⟩ := s
  rfl

theorem rProf_recenter (c : Chart) (a x : ℝ) : rProf (c.recenter a) x = rProf c x - a := by
  simp [rProf, InteractingSLE.Chart.recenter]

/-- **The boundary continuation from a right threshold** moves right to the first later original jump with an
admissible outward height, or to `∞`. -/
theorem contStep_thr_true {κ : ℝ} (b : ℝ → ℝ) (jumps : Finset ℝ) (s : ExplState)
    (hst : stStatus s = stThr (some true)) (pref : Bool) :
    ExplState.contStep κ b jumps s none pref =
      (let C := (jumpSet b jumps).filter
          (fun x => stPt s < x ∧ -sleLambda κ < rightLim b x + stAngle s * chiC κ)
        if hC : C.Nonempty then ExplState.moveAlong s true (C.min' hC) true
        else ExplState.moveToEnd s true) := by
  obtain ⟨pieces, arcs, ret, lau, chart, st, pt, ang, rR, rL⟩ := s
  change st = _ at hst
  subst hst
  rfl

/-- **The real connector is low** (Lemma GW1, (GW1.3)): between a right threshold `q` whose outward original height
is low and the first later original jump `w` with an admissible outward height, the original heights are low. -/
theorem add_le_neg_of_connector {κ θ : ℝ} {b : ℝ → ℝ} {jumps : Finset ℝ}
    (hb : IsPiecewiseConstantBoundaryData b jumps) {q w x : ℝ}
    (hlow : rightLim b q + θ * chiC κ ≤ -sleLambda κ)
    (hC : ∀ z ∈ jumpSet b jumps, q < z → z < w → rightLim b z + θ * chiC κ ≤ -sleLambda κ)
    (hqx : q < x) (hxw : x < w) (hxJ : x ∉ jumps) : b x + θ * chiC κ ≤ -sleLambda κ := by
  classical
  set G := (jumpSet b jumps).filter (fun z => q < z ∧ z < x) with hG
  have hzero : ∀ z₀, (∀ u ∈ jumpSet b jumps, z₀ < u → u < x → False) →
      ∑ u ∈ jumps.filter (fun u => z₀ < u ∧ u < x), (rightLim b u - leftLim b u) = 0 := by
    intro z₀ hno
    refine Finset.sum_eq_zero fun u hu => ?_
    rw [Finset.mem_filter] at hu
    by_contra hne
    exact hno u (Finset.mem_filter.2 ⟨hu.1, fun h => hne (by rw [h, sub_self])⟩) hu.2.1 hu.2.2
  by_cases hGn : G.Nonempty
  · have hz : G.max' hGn ∈ jumpSet b jumps ∧ q < G.max' hGn ∧ G.max' hGn < x :=
      Finset.mem_filter.1 (Finset.max'_mem G hGn)
    have e := Exist.eq_rightLim_add_sum_seed hb hz.2.2 hxJ
    rw [hzero _ fun u hu hzu hux => absurd (G.le_max' u (Finset.mem_filter.2 ⟨hu, hz.2.1.trans hzu, hux⟩))
      (not_le.2 hzu), add_zero] at e
    rw [e]
    exact hC _ hz.1 hz.2.1 (hz.2.2.trans hxw)
  · have e := Exist.eq_rightLim_add_sum_seed hb hqx hxJ
    rw [hzero _ fun u hu hqu hux => hGn ⟨u, Finset.mem_filter.2 ⟨hu, hqu, hux⟩⟩, add_zero] at e
    rw [e]
    exact hlow

/-- **The invariant at a launch of the right walk** (angle `θ`, word `β`): the word is admissible left of the seed,
the chart has a right profile, and right of the right record the word is the original word. -/
def RInv (κ θ : ℝ) (b : ℝ → ℝ) (jumps : Finset ℝ) (β : BoundaryWord) (s : ExplState) : Prop :=
  (∀ y, y < 0 → y ∉ β.jumps → β.fn y + θ * chiC κ < sleLambda κ) ∧ RProf s ∧ ROrig b jumps β s

/-- **The move to the next restart mark restores the invariant** (Lemma GW1, "The next real connector …": "Items 1–4
are therefore restored"): from a state with a right profile whose word `γ` is admissible at every negative point and
original right of the record, moving right along a low connector to `w` and recentring there gives the invariant for
the recentred word. -/
theorem rInv_moveAlong {κ θ : ℝ} (hκ : 0 < κ) {b : ℝ → ℝ} {jumps : Finset ℝ} {γ : BoundaryWord} {s₁ : ExplState}
    (hs₁ : RProf s₁) (hO : ROrig b jumps γ s₁) (hγL : ∀ y, y < 0 → γ.fn y + θ * chiC κ < sleLambda κ)
    {w : ℝ} (hw : stRecR s₁ < w)
    (hlow : ∀ x, stRecR s₁ < x → x < w → x ∉ jumps → b x + θ * chiC κ ≤ -sleLambda κ) :
    RInv κ θ b jumps (BoundaryWord.shiftW (rProf (stChart s₁) w) γ) (ExplState.moveAlong s₁ true w true) := by
  obtain ⟨hc, hm, hpos, hsmall⟩ := hs₁
  set m := rProf (stChart s₁) with hmdef
  set a := m w with hadef
  have hl : 0 < sleLambda κ := Sec4.sleLambda_pos hκ
  have hR₂ : stRecR (ExplState.moveAlong s₁ true w true) = w := by
    rw [stRecR_moveAlong_true, max_eq_right hw.le]
  have hprof : rProf (stChart (ExplState.moveAlong s₁ true w true)) = fun x => m x - a := by
    funext x
    rw [stChart_moveAlong, rProf_recenter]
    rfl
  have hcw : ContinuousAt m w := hm.2.1.continuousAt (Ioi_mem_nhds hw)
  have hJ : ∀ z, z - a ∉ (BoundaryWord.shiftW a γ).jumps → z ∉ γ.jumps := fun z hz h =>
    hz (by rw [BoundaryWord.jumps_shiftW]; exact Finset.mem_image_of_mem _ h)
  refine ⟨fun y hy hyJ => ?_, ⟨fun x => ?_, ?_, fun x hx => ?_, fun ε hε => ?_⟩, fun x hx hxJ hzJ => ?_⟩
  · -- the left side
    have hyJ' : y + a ∉ γ.jumps := hJ (y + a) (by rwa [add_sub_cancel_right])
    rw [BoundaryWord.fn_shiftW]
    rcases lt_trichotomy (y + a) 0 with hneg | hzero | hposa
    · exact hγL _ hneg
    · -- at the seed of the old word, approach from the left
      have hev := γ.isPiecewiseConstantBoundaryData (y + a) hyJ'
      obtain ⟨z, hz, hzlt⟩ := ((hev.filter_mono nhdsWithin_le_nhds).and
        (self_mem_nhdsWithin : Iio (y + a) ∈ 𝓝[<] (y + a))).exists
      rw [← hz]
      exact hγL z (hzero ▸ hzlt)
    · -- on the connector
      have hza : y + a < a := by linarith
      obtain ⟨x, hx, hmx⟩ := RProf.exists_eq ⟨hc, hm, hpos, hsmall⟩ hposa
      rw [← hmdef] at hmx
      have hxw : x < w := by
        by_contra h
        push Not at h
        have := hm.1.monotoneOn hw hx h
        rw [hmx] at this
        linarith
      have hcx : ContinuousAt m x := hm.2.1.continuousAt (Ioi_mem_nhds hx)
      have hP : ∀ᶠ x' in 𝓝 x, x' < w ∧ γ.fn (m x') = γ.fn (y + a) := by
        have h1 := hcx.eventually (by rw [hmx]; exact γ.isPiecewiseConstantBoundaryData (y + a) hyJ')
        filter_upwards [gt_mem_nhds hxw, h1] with x' h2 h3
        exact ⟨h2, h3⟩
      obtain ⟨x', hx'R, hx'J, hmx'J, hx'w, hfn⟩ := exists_near_avoid hm.1 hx jumps γ.jumps hP
      rw [← hfn, hO x' hx'R hx'J hmx'J]
      have := hlow x' hx'R hx'w hx'J
      linarith
  · rw [stChart_moveAlong]
    change ((stChart s₁).1 x - (((stChart s₁).1 w).re : ℂ)).im = 0
    rw [Complex.sub_im, hc x, Complex.ofReal_im, sub_zero]
  · rw [hprof, hR₂]
    exact (hm.mono_of_le hw.le).sub_const a
  · rw [hR₂] at hx
    rw [hprof]
    have := hm.1 hw (hw.trans hx) hx
    change 0 < m x - m w
    linarith
  · rw [hR₂]
    have hev : ∀ᶠ x in 𝓝 w, |m x - a| < ε := by
      have := hcw.eventually (Metric.ball_mem_nhds (m w) hε)
      filter_upwards [this] with x hx
      rw [Real.dist_eq] at hx
      exact hx
    obtain ⟨x, hx1, hx2⟩ := ((hev.filter_mono nhdsWithin_le_nhds).and
      (self_mem_nhdsWithin : Ioi w ∈ 𝓝[>] w)).exists
    refine ⟨x, hx2, ?_⟩
    rw [hprof]
    exact lt_of_le_of_lt (le_abs_self _) hx1
  · rw [hR₂] at hx
    rw [hprof] at hzJ ⊢
    rw [BoundaryWord.fn_shiftW, sub_add_cancel]
    exact hO x (hw.trans hx) hxJ (hJ (m x) hzJ)

end Cont

/-! ### The end of a stage -/

section Tail

open PiecewiseConstantBoundaryData (rightLim leftLim jumpSet)

/-- The candidate restart marks of a rightward boundary continuation. -/
def restartSet (κ : ℝ) (b : ℝ → ℝ) (jumps : Finset ℝ) (s : ExplState) : Finset ℝ :=
  (jumpSet b jumps).filter (fun x => stPt s < x ∧ -sleLambda κ < rightLim b x + stAngle s * chiC κ)

/-- A launch-ready state of the right walk: at the root or on an arc at its mark (moving right), with the current
point at the right record. -/
def RReady (s : ExplState) : Prop :=
  (stStatus s = .inl () ∨ stStatus s = .inr (.inr (.inr (.inl (true, true))))) ∧ stPt s = stRecR s

/-- **The end of a stage of the right walk** (Lemma GW1, "The next real connector and finite progress"): from a state
whose current point is its right record, with a right profile, a word original right of the record and admissible at
every negative point, and a low outward original height at the current point, a rightward boundary continuation that
reaches a restart mark gives a launch-ready state with the invariant for the recentred word. -/
theorem rInv_tail {κ θ : ℝ} (hκ : 0 < κ) {b : ℝ → ℝ} {jumps : Finset ℝ}
    (hb : IsPiecewiseConstantBoundaryData b jumps) {γ : BoundaryWord} {s₁ s₂ : ExplState} (hs₁ : RProf s₁)
    (hO : ROrig b jumps γ s₁) (hγL : ∀ y, y < 0 → γ.fn y + θ * chiC κ < sleLambda κ) (hpt : stPt s₁ = stRecR s₁)
    (hang : stAngle s₁ = θ) (hlow : rightLim b (stPt s₁) + θ * chiC κ ≤ -sleLambda κ)
    (he : s₂ = if hC : (restartSet κ b jumps s₁).Nonempty then
      ExplState.moveAlong s₁ true ((restartSet κ b jumps s₁).min' hC) true else ExplState.moveToEnd s₁ true)
    (hst : ∃ r, stStatus s₂ = .inr (.inr (.inr (.inl (r, true))))) :
    RInv κ θ b jumps (BoundaryWord.shiftW (rProf (stChart s₁) (stPt s₂)) γ) s₂ ∧ RReady s₂ ∧
      rProf (stChart s₁) (stPt s₂) = ((stChart s₁).1 0 - (stChart s₂).1 0).re := by
  split_ifs at he with hC
  swap
  · exfalso
    obtain ⟨r, hr⟩ := hst
    rw [he] at hr
    obtain ⟨pieces, arcs, ret, lau, chart, st, pt, ang, rR, rL⟩ := s₁
    exact absurd hr (by simp [ExplState.moveToEnd, stStatus])
  subst he
  set w := (restartSet κ b jumps s₁).min' hC with hw
  have hmem := Finset.mem_filter.1 (Finset.min'_mem _ hC)
  have hpw : stPt s₁ < w := hmem.2.1
  have hlowc : ∀ x, stRecR s₁ < x → x < w → x ∉ jumps → b x + θ * chiC κ ≤ -sleLambda κ := by
    intro x hx hxw hxJ
    rw [← hpt] at hx
    refine add_le_neg_of_connector hb hlow (fun z hz hqz hzw => ?_) hx hxw hxJ
    by_contra hgt
    push Not at hgt
    have hz' : z ∈ restartSet κ b jumps s₁ := Finset.mem_filter.2 ⟨hz, hqz, by rw [hang]; exact hgt⟩
    exact absurd ((restartSet κ b jumps s₁).min'_le z hz') (not_le.2 hzw)
  rw [stPt_moveAlong]
  refine ⟨rInv_moveAlong hκ hs₁ hO hγL (by rw [← hpt]; exact hpw) hlowc, ⟨Or.inr ?_, ?_⟩, ?_⟩
  · obtain ⟨pieces, arcs, ret, lau, chart, st, pt, ang, rR, rL⟩ := s₁
    rfl
  · rw [stPt_moveAlong, stRecR_moveAlong_true, max_eq_right (by rw [← hpt]; exact hpw.le)]
  · rw [stChart_moveAlong]
    simp [InteractingSLE.Chart.recenter, rProf]

/-- **The boundary continuation from a zero-lifetime threshold** moves right when the outward height is low. -/
theorem contStep_thr_none_right {κ : ℝ} (b : ℝ → ℝ) (jumps : Finset ℝ) (s : ExplState)
    (hst : stStatus s = stThr none) (hR : rightLim b (stPt s) + stAngle s * chiC κ ≤ -sleLambda κ) :
    ExplState.contStep κ b jumps s none true =
      if hC : (restartSet κ b jumps s).Nonempty then
        ExplState.moveAlong s true ((restartSet κ b jumps s).min' hC) true else ExplState.moveToEnd s true := by
  obtain ⟨pieces, arcs, ret, lau, chart, st, pt, ang, rR, rL⟩ := s
  change st = _ at hst
  subst hst
  change rightLim b pt + ang * chiC κ ≤ -sleLambda κ at hR
  by_cases h2 : sleLambda κ ≤ leftLim b pt + ang * chiC κ
  · simp only [ExplState.contStep, hR, h2, and_self, ↓reduceIte]
    rfl
  · simp only [ExplState.contStep, hR, h2, and_false, ↓reduceIte]
    rfl

/-- **The boundary continuation from a right threshold**, with the restart set. -/
theorem contStep_thr_true' {κ : ℝ} (b : ℝ → ℝ) (jumps : Finset ℝ) (s : ExplState)
    (hst : stStatus s = stThr (some true)) :
    ExplState.contStep κ b jumps s none true =
      if hC : (restartSet κ b jumps s).Nonempty then
        ExplState.moveAlong s true ((restartSet κ b jumps s).min' hC) true else ExplState.moveToEnd s true :=
  contStep_thr_true b jumps s hst true

/-- **A zero-lifetime threshold at an admissible seed kills the walk** (no boundary continuation is available). -/
theorem contStep_thr_none_dead {κ : ℝ} (b : ℝ → ℝ) (jumps : Finset ℝ) (s : ExplState)
    (hst : stStatus s = stThr none) (hL : leftLim b (stPt s) + stAngle s * chiC κ < sleLambda κ)
    (hR : -sleLambda κ < rightLim b (stPt s) + stAngle s * chiC κ) (pref : Bool) :
    stStatus (ExplState.contStep κ b jumps s none pref) = stDead := by
  obtain ⟨pieces, arcs, ret, lau, chart, st, pt, ang, rR, rL⟩ := s
  change st = _ at hst
  subst hst
  change leftLim b pt + ang * chiC κ < sleLambda κ at hL
  change -sleLambda κ < rightLim b pt + ang * chiC κ at hR
  have h1 : ¬ rightLim b pt + ang * chiC κ ≤ -sleLambda κ := not_le.2 hR
  have h2 : ¬ sleLambda κ ≤ leftLim b pt + ang * chiC κ := not_le.2 hL
  simp only [ExplState.contStep, h1, h2, false_and, ↓reduceIte]

end Tail

/-! ### The outcome of a launch through the available lifetime -/

section Outcome

variable {s : ExplState} {k : ℕ} {D : (ℝ≥0 → ℝ) × ℝ≥0∞} {θ : ℝ}

theorem min_top_ne_top (hfin : D.2 ≠ ⊤) : min ⊤ D.2 ≠ ⊤ := by rwa [min_eq_right le_top]

/-- **A launch ending at a right threshold**: a real point right of the old record is hit, and the current point is
the new right record. -/
theorem launch_thr_true (hfin : D.2 ≠ ⊤) (h : stStatus (ExplState.launch s k D θ ⊤) = stThr (some true)) :
    D.2 ≠ 0 ∧ (∃ x, stRecR s < x ∧ lHit (stChart s) ⊤ D x) ∧
      stPt (ExplState.launch s k D θ ⊤) = stRecR (ExplState.launch s k D θ ⊤) ∧
      stAngle (ExplState.launch s k D θ ⊤) = θ := by
  obtain ⟨-, hang, hrec, -, hst, hpt⟩ := launch_eq_of_ne_top s k D θ ⊤ (min_top_ne_top hfin)
  rw [hst] at h
  have hnt : ¬ (⊤ : ℝ≥0∞) < D.2 := not_lt.2 le_top
  unfold lStatus at h
  rw [ite_eq_right_of_eq_false _ _ (eq_false hnt)] at h
  by_cases h0 : D.2 = 0
  · rw [ite_eq_left_of_eq_true _ _ (eq_true h0)] at h
    exfalso
    revert h
    split <;> simp [stThr, stDead]
  rw [ite_eq_right_of_eq_false _ _ (eq_false h0)] at h
  by_cases hx : ∃ x : ℝ, stRecR s < x ∧ lHit (stChart s) ⊤ D x
  · refine ⟨h0, hx, ?_, hang⟩
    rw [hpt, hrec]
    unfold lPt
    rw [ite_eq_right_of_eq_false _ _ (eq_false hnt), ite_eq_right_of_eq_false _ _ (eq_false h0),
      ite_eq_left_of_eq_true _ _ (eq_true hx)]
  · rw [ite_eq_right_of_eq_false _ _ (eq_false hx)] at h
    exfalso
    split_ifs at h <;> simp [stThr, stDead] at h

/-- **The outcome of a launch with a finite positive lifetime**: a right threshold, a left threshold, or death. -/
theorem launch_status_of_pos (hfin : D.2 ≠ ⊤) (h0 : D.2 ≠ 0) :
    stStatus (ExplState.launch s k D θ ⊤) = stThr (some true) ∨
      stStatus (ExplState.launch s k D θ ⊤) = stThr (some false) ∨
      stStatus (ExplState.launch s k D θ ⊤) = stDead := by
  obtain ⟨-, -, -, -, hst, -⟩ := launch_eq_of_ne_top s k D θ ⊤ (min_top_ne_top hfin)
  rw [hst]
  unfold lStatus
  rw [ite_eq_right_of_eq_false _ _ (eq_false (not_lt.2 le_top)), ite_eq_right_of_eq_false _ _ (eq_false h0)]
  split_ifs
  · exact Or.inl rfl
  · exact Or.inr (Or.inl rfl)
  · exact Or.inr (Or.inr rfl)

/-- **A launch with zero lifetime from a state that is not an interior tip** ends at a seed threshold, at the same
point, with the same records. -/
theorem launch_zero (h0 : D.2 = 0) (hs : stStatus s ≠ .inr (.inl ())) :
    stStatus (ExplState.launch s k D θ ⊤) = stThr none ∧ stPt (ExplState.launch s k D θ ⊤) = stPt s ∧
      stAngle (ExplState.launch s k D θ ⊤) = θ := by
  have hfin : D.2 ≠ ⊤ := by rw [h0]; exact ENNReal.zero_ne_top
  obtain ⟨-, hang, -, -, hst, hpt⟩ := launch_eq_of_ne_top s k D θ ⊤ (min_top_ne_top hfin)
  have hnt : ¬ (⊤ : ℝ≥0∞) < D.2 := not_lt.2 le_top
  refine ⟨?_, ?_, hang⟩
  · rw [hst]
    unfold lStatus
    rw [ite_eq_right_of_eq_false _ _ (eq_false hnt), ite_eq_left_of_eq_true _ _ (eq_true h0)]
    revert hs
    split
    · next heq => intro h; exact absurd heq h
    · intro _; rfl
  · rw [hpt]
    unfold lPt
    rw [ite_eq_right_of_eq_false _ _ (eq_false hnt), ite_eq_left_of_eq_true _ _ (eq_true h0)]

end Outcome

end GW1W

end Theorem14

end InteractingSLE
