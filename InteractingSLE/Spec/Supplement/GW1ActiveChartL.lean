/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW1ActiveThr

/-!
# Lemma GW1's active-word classification: the left walk, one stage (deterministic)

Packet PROVE-T14-GW1W. The mirror of `GW1ActiveChart` for the left boundary walk (angle `θ`, in the application
`θ = π/2`; "Reflection gives the left boundary walk `L` at angle `+π/2`", Lemma GW1, p. 618). At a launch of the left
walk the state and the word `β` satisfy `LInv`:

* (`RightHigh`) the word is admissible right of the seed: `−λ < β + θχ` there;
* (`LProf`) the chart maps the physical ray left of the left record increasingly onto `(−∞, 0)` (read through the
  reflected profile `lProf`);
* (`LOrig`) there the word is the original word;
* (`RRight`) right of the right record the chart is increasing, continuous, unbounded and positive (so a point of the
  physical right ray is swallowed only if a positive point of the chart is).

The real-flow input on the left is `exists_alive_fwdMap_lt` for the reflected driver.
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

/-! ### Generic: small values of the new profile -/

/-- **After a launch whose real flow comes arbitrarily close to `0` on alive points, the new profile does too.** -/
theorem exists_newRec_lt_small {m : ℝ → ℝ} {a : ℝ} {A : ℝ → Prop} {f : ℝ → ℝ} (hm : RightGood m a)
    (hpos : ∀ x, a < x → 0 < m x) (hsmall : ∀ ε > 0, ∃ x, a < x ∧ m x < ε) (hH : IsRealHalf A f)
    (hq : ∀ ε > 0, ∃ q, 0 < q ∧ A q ∧ f q < ε) {ε : ℝ} (hε : 0 < ε) :
    ∃ x, newRec m a A < x ∧ f (m x) < ε := by
  obtain ⟨q, hq0, hAq, hfq⟩ := hq (ε / 2) (half_pos hε)
  obtain ⟨η, hη, hηf⟩ := hH.2.2.2.2.2.1 q hq0 hAq (ε / 2) (half_pos hε)
  have hq' : q < q + η / 2 := by linarith
  have hAq' : A (q + η / 2) := hH.2.1 q _ hq0 hq' hAq
  have hex : ∀ y, 0 < y → ∃ x, a < x ∧ m x = y := fun y hy => by
    obtain ⟨x, hx, hxy⟩ := hsmall y hy
    exact (exists_eq_iff_exists_lt hm).2 ⟨x, hx, hxy⟩
  obtain ⟨x₁, hx₁, hmx₁⟩ := hex q hq0
  obtain ⟨x₂, hx₂, hmx₂⟩ := hex (q + η / 2) (hq0.trans hq')
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
  have hnew : newRec m a A ≤ x₁ := by
    refine csSup_le (insert_nonempty _ _) fun z hz => ?_
    rcases hz with rfl | ⟨hza, hzA⟩
    · exact hx₁.le
    · by_contra hzx
      push Not at hzx
      apply hzA
      have hlt : m x₁ < m z := hm.1 hx₁ hza hzx
      rw [hmx₁] at hlt
      exact hH.2.1 q _ hq0 hlt hAq
  refine ⟨x₂, hnew.trans_lt h12, ?_⟩
  rw [hmx₂]
  have := hηf (q + η / 2) hAq' (by rw [abs_lt]; constructor <;> linarith)
  rw [abs_lt] at this
  linarith [this.2]

/-! ### The left profile of a state -/

/-- **The left profile of a state**: the chart sends the real line to itself and the physical ray left of the left
record continuously and decreasingly onto `(−∞, 0)` (read through the reflected profile `lProf`). -/
def LProf (s : ExplState) : Prop :=
  IsRealChart (stChart s) ∧ RightGood (lProf (stChart s)) (-stRecL s) ∧
    (∀ x, -stRecL s < x → 0 < lProf (stChart s) x) ∧ ∀ ε > 0, ∃ x, -stRecL s < x ∧ lProf (stChart s) x < ε

/-- **The word is the original word on the ray left of the left record** (read in the chart, off the jumps). -/
def LOrig (b : ℝ → ℝ) (jumps : Finset ℝ) (β : BoundaryWord) (s : ExplState) : Prop :=
  ∀ x, x < stRecL s → x ∉ jumps → rProf (stChart s) x ∉ β.jumps → β.fn (rProf (stChart s) x) = b x

/-- **Right of the right record the chart is good and positive.** -/
def RRight (s : ExplState) : Prop :=
  RightGood (rProf (stChart s)) (stRecR s) ∧ ∀ x, stRecR s < x → 0 < rProf (stChart s) x

theorem lProf_eq (c : Chart) (x : ℝ) : lProf c x = -rProf c (-x) := rfl

theorem LProf.exists_eq {s : ExplState} (hs : LProf s) {y : ℝ} (hy : 0 < y) :
    ∃ x, -stRecL s < x ∧ lProf (stChart s) x = y := by
  obtain ⟨x, hx, hxy⟩ := hs.2.2.2 y hy
  exact (exists_eq_iff_exists_lt hs.2.1).2 ⟨x, hx, hxy⟩

section Launch

variable {s : ExplState} {D : (ℝ≥0 → ℝ) × ℝ≥0∞}

/-- **The right side after a launch** with a good record at a finite stop: the right profile stays good and
positive right of the new right record, and is the real flow of the old one. -/
theorem rRight_launch (hc : IsRealChart (stChart s)) (hs : RRight s) (k : ℕ) (θ : ℝ) (hreg : IsRegularDriver D)
    (hgood : LocalExt.IsDrvGood (recHist (recOf ⊤ D))) (hfin : D.2 ≠ ⊤) :
    IsRealChart (stChart (ExplState.launch s k D θ ⊤)) ∧ RRight (ExplState.launch s k D θ ⊤) := by
  obtain ⟨hm, hpos⟩ := hs
  obtain ⟨hch, -, hrec, -, -, -⟩ := launch_eq_of_ne_top s k D θ ⊤ (min_top_ne_top hfin)
  set W := stopDrv ⊤ D with hWdef
  set T := stopTime ⊤ D with hTdef
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
  refine ⟨fun x => ?_, ?_, fun x hx => ?_⟩
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

end Launch

/-- **Perturbation on the left** (the mirror of `exists_near_avoid`): near a point of `(−∞, a)`, finitely many
exceptional arguments and values of a function strictly increasing there can be avoided. -/
theorem exists_near_avoid_left {g : ℝ → ℝ} {a x : ℝ} (hg : StrictMonoOn g (Iio a)) (hx : x < a)
    (F G : Finset ℝ) {P : ℝ → Prop} (hP : ∀ᶠ x' in 𝓝 x, P x') : ∃ x', x' < a ∧ x' ∉ F ∧ g x' ∉ G ∧ P x' := by
  have hg' : StrictMonoOn (fun u => -g (-u)) (Ioi (-a)) := fun u hu v hv huv => by
    have := hg (show -v ∈ Iio a from by simp only [Set.mem_Iio, Set.mem_Ioi] at hv ⊢; linarith)
      (show -u ∈ Iio a from by simp only [Set.mem_Iio, Set.mem_Ioi] at hu ⊢; linarith) (by linarith)
    linarith
  have hP' : ∀ᶠ u in 𝓝 (-x), P (-u) := by
    have h := (continuous_neg.tendsto (-x)).eventually (by rwa [neg_neg] : ∀ᶠ x' in 𝓝 (-(-x)), P x')
    exact h
  obtain ⟨u, hu, huF, huG, hPu⟩ := exists_near_avoid hg' (show -a < -x by linarith) (F.image (fun y => -y))
    (G.image (fun y => -y)) hP'
  refine ⟨-u, by linarith [show -a < u from hu], fun h => huF (Finset.mem_image.2 ⟨-u, h, neg_neg u⟩),
    fun h => huG (Finset.mem_image.2 ⟨g (-u), h, rfl⟩), hPu⟩

/-- The profile is strictly increasing on the physical left ray. -/
theorem LProf.strictMonoOn {s : ExplState} (hs : LProf s) : StrictMonoOn (rProf (stChart s)) (Iio (stRecL s)) :=
  fun x hx y hy hxy => by
    have := hs.2.1.1 (show -y ∈ Ioi (-stRecL s) from by simp only [Set.mem_Iio, Set.mem_Ioi] at hy ⊢; linarith)
      (show -x ∈ Ioi (-stRecL s) from by simp only [Set.mem_Iio, Set.mem_Ioi] at hx ⊢; linarith) (by linarith)
    simp only [lProf_eq, neg_neg] at this
    linarith

theorem LProf.neg {s : ExplState} (hs : LProf s) {x : ℝ} (hx : x < stRecL s) : rProf (stChart s) x < 0 := by
  have := hs.2.2.1 (-x) (by linarith)
  rw [lProf_eq, neg_neg] at this
  linarith

section LaunchL

variable {s : ExplState} {D : (ℝ≥0 → ℝ) × ℝ≥0∞}

/-- **The left profile after a launch that ends at a left threshold** (the mirror of `rProf_launch`). -/
theorem lProf_launch (hs : LProf s) (k : ℕ) (θ : ℝ) (hreg : IsRegularDriver D)
    (hgood : LocalExt.IsDrvGood (recHist (recOf ⊤ D))) (hfin : D.2 ≠ ⊤)
    (hhit : ∃ x, x < stRecL s ∧ lHit (stChart s) ⊤ D x) :
    LProf (ExplState.launch s k D θ ⊤) ∧ ∀ x, x < stRecL (ExplState.launch s k D θ ⊤) →
      x < stRecL s ∧ (∃ u, IsForwardSol (rdrv (recOf ⊤ D)) (rProf (stChart s) x : ℂ) (rtime (recOf ⊤ D)) u) ∧
      rProf (stChart (ExplState.launch s k D θ ⊤)) x =
        (fwdMap (rdrv (recOf ⊤ D)) (rtime (recOf ⊤ D)) (rProf (stChart s) x)).re := by
  obtain ⟨hc, hm, hpos, hsmall⟩ := hs
  obtain ⟨hch, -, -, hrecL, -, -⟩ := launch_eq_of_ne_top s k D θ ⊤ (min_top_ne_top hfin)
  have hWr : rdrv (recOf ⊤ D) = stopDrv ⊤ D := by rw [rdrv_recOf]; exact recDrv_eq_stopDrv hreg hgood
  rw [hWr, rtime_recOf]
  set W := stopDrv ⊤ D with hWdef
  set T := stopTime ⊤ D with hTdef
  have hW : Continuous W := by rw [← hWr]; exact continuous_rdrv _
  have hW0 : W 0 = 0 := stopDrv_zero hreg ⊤
  have hT0 : 0 ≤ T := stopTime_nonneg ⊤ D
  have hH := (isRealFlow_stop hreg hgood).2
  set A' : ℝ → Prop := fun y : ℝ => ∃ u, IsForwardSol W ((-y : ℝ) : ℂ) T u with hA'def
  set f' : ℝ → ℝ := fun y => -(fwdMap W T ((-y : ℝ) : ℂ)).re with hf'def
  set m := lProf (stChart s) with hmdef
  have hrecL' : -stRecL (ExplState.launch s k D θ ⊤) = newRec m (-stRecL s) A' := by
    rw [hrecL, lRecL_eq_newRec hc, neg_neg]
  have hprofR : ∀ x, rProf (stChart (ExplState.launch s k D θ ⊤)) x = (fwdMap W T (rProf (stChart s) x)).re := by
    intro x
    rw [hch]
    change (fwdMap W T ((stChart s).1 x)).re = _
    rw [hc.eq_ofReal x]
  have hprofL : lProf (stChart (ExplState.launch s k D θ ⊤)) = fun u => f' (m u) := by
    funext u
    rw [lProf_eq, hprofR]
    change -(fwdMap W T (rProf (stChart s) (-u) : ℂ)).re = -(fwdMap W T ((-(lProf (stChart s) u) : ℝ) : ℂ)).re
    rw [lProf_eq, neg_neg]
  have hle := le_newRec hm hH
  refine ⟨⟨fun x => ?_, ?_, fun u hu => ?_, fun ε hε => ?_⟩, fun x hx => ?_⟩
  · rw [hch]
    change (fwdMap W T ((stChart s).1 x)).im = 0
    rw [hc.eq_ofReal x]
    exact im_fwdMap_ofReal W hT0 _
  · rw [hprofL, hrecL']
    exact rightGood_comp hm hH
  · rw [hrecL'] at hu
    obtain ⟨h0, hA⟩ := pos_alive_of_newRec_lt hm hH hu
    rw [hprofL]
    exact hH.2.2.2.1 _ h0 hA
  · rw [hrecL', hprofL]
    refine exists_newRec_lt_small hm hpos hsmall hH (fun ε hε => ?_) hε
    -- the hit point, reflected, is swallowed at `T` by the reflected driver
    obtain ⟨x₀, hx₀, hhit₀, hdead₀⟩ := hhit
    have hu₀ : -stRecL s < -x₀ := by linarith
    have hy₀ : 0 < m (-x₀) := hpos _ hu₀
    have hc₀ : (stChart s).1 x₀ = ((-(m (-x₀)) : ℝ) : ℂ) := by
      rw [hc.eq_ofReal x₀, hmdef, lProf_eq, neg_neg, neg_neg]
    have hdead : ¬ ∃ u, IsForwardSol (-W) ((m (-x₀) : ℝ) : ℂ) T u := by
      rw [alive_neg_iff]
      intro h
      apply hdead₀
      change ∃ u, IsForwardSol W ((stChart s).1 x₀) T u
      rw [hc₀]
      exact h
    have hTpos : 0 < T := by
      rcases hT0.lt_or_eq with h | h
      · exact h
      · exfalso
        apply hdead
        rw [← h]
        exact exists_isForwardSol_zero (by simp [hW0]) hy₀.ne'
    have hsw : RealSwallowAt (-W) (m (-x₀)) T := by
      refine ⟨hTpos, fun r hr => ?_, hdead⟩
      have := hhit₀ r hr.2
      rw [hc₀] at this
      exact (alive_neg_iff W r (m (-x₀))).2 this
    obtain ⟨q, hq0, hAq, hfq⟩ := exists_alive_fwdMap_lt hW.neg (by simp [hW0]) hy₀ hsw hε
    refine ⟨q, hq0, (alive_neg_iff W T q).1 hAq, ?_⟩
    have hr := QuantumZipper.F1.fwdMap_reflect_ofReal W hT0 (-q)
    rw [neg_neg] at hr
    change -(fwdMap W T ((-q : ℝ) : ℂ)).re < ε
    rw [hr, Complex.neg_re] at hfq
    linarith
  · have hu : newRec m (-stRecL s) A' < -x := by rw [← hrecL']; linarith
    obtain ⟨-, hA⟩ := pos_alive_of_newRec_lt hm hH hu
    refine ⟨by linarith [hle.trans_lt hu], ?_, hprofR x⟩
    have e : ((-(m (-x)) : ℝ) : ℂ) = (rProf (stChart s) x : ℂ) := by rw [hmdef, lProf_eq, neg_neg, neg_neg]
    rw [← e]
    exact hA

/-- **The left profile after a launch with zero lifetime**: nothing is swallowed and the chart is unchanged. -/
theorem lProf_launch_zero (hs : LProf s) (k : ℕ) (θ : ℝ) (hreg : IsRegularDriver D) (h0 : D.2 = 0) :
    LProf (ExplState.launch s k D θ ⊤) ∧ ∀ x, x < stRecL (ExplState.launch s k D θ ⊤) →
      x < stRecL s ∧ (∃ u, IsForwardSol (rdrv (recOf ⊤ D)) (rProf (stChart s) x : ℂ) (rtime (recOf ⊤ D)) u) ∧
      rProf (stChart (ExplState.launch s k D θ ⊤)) x =
        (fwdMap (rdrv (recOf ⊤ D)) (rtime (recOf ⊤ D)) (rProf (stChart s) x)).re := by
  have hc := hs.1
  have hmin : min ⊤ D.2 ≠ ⊤ := by rw [h0]; simp
  obtain ⟨hch, -, -, hrecL, -, -⟩ := launch_eq_of_ne_top s k D θ ⊤ hmin
  have hT : stopTime ⊤ D = 0 := by simp [stopTime, h0]
  have hW0 : stopDrv ⊤ D 0 = 0 := stopDrv_zero hreg ⊤
  have hchart : ∀ z : ℂ, (stChart (ExplState.launch s k D θ ⊤)).1 z = (stChart s).1 z := by
    intro z
    rw [hch, hT]
    change fwdMap (stopDrv ⊤ D) 0 ((stChart s).1 z) = _
    rw [fwdMap_zero_time hW0]
  have hprof : rProf (stChart (ExplState.launch s k D θ ⊤)) = rProf (stChart s) := by
    funext x; simp only [rProf, hchart]
  have hlprof : lProf (stChart (ExplState.launch s k D θ ⊤)) = lProf (stChart s) := by
    funext x; simp only [lProf, hchart]
  have hL : stRecL (ExplState.launch s k D θ ⊤) = stRecL s := by
    rw [hrecL]
    unfold lRecL
    have he : {x : ℝ | x < stRecL s ∧ ¬ lAlive (stChart s) ⊤ D x} = ∅ := by
      ext x
      simp only [mem_ofPred_eq, mem_empty_iff_false, iff_false, not_and, not_not]
      intro hx
      unfold lAlive
      rw [hT, hc.eq_ofReal x]
      exact exists_isForwardSol_zero hW0 (hs.neg hx).ne
    rw [he, insert_empty_eq, csInf_singleton]
  have hrt : rtime (recOf ⊤ D) = 0 := by rw [rtime_recOf, hT]
  refine ⟨⟨fun x => ?_, ?_, ?_, ?_⟩, fun x hx => ?_⟩
  · rw [hchart]; exact hc x
  · rw [hlprof, hL]; exact hs.2.1
  · rw [hlprof, hL]; exact hs.2.2.1
  · rw [hlprof, hL]; exact hs.2.2.2
  · rw [hL] at hx
    refine ⟨hx, ?_, ?_⟩
    · rw [hrt]
      exact exists_isForwardSol_zero (rdrv_zero _) (hs.neg hx).ne
    · rw [hprof, hrt, fwdMap_zero_time (rdrv_zero _)]
      simp

/-- **The original word survives on the new left ray** (the mirror of `rOrig_of_rel`). -/
theorem lOrig_of_rel {κ : ℝ} (hκ : 0 < κ) {b : ℝ → ℝ} {jumps : Finset ℝ}
    (hb : IsPiecewiseConstantBoundaryData b jumps) {β : BoundaryWord} (hs : LProf s) (hO : LOrig b jumps β s)
    {s₁ : ExplState} {r : RecData} (θ : ℝ)
    (hrel : LProf s₁ ∧ ∀ x, x < stRecL s₁ → x < stRecL s ∧
      (∃ u, IsForwardSol (rdrv r) (rProf (stChart s) x : ℂ) (rtime r) u) ∧
      rProf (stChart s₁) x = (fwdMap (rdrv r) (rtime r) (rProf (stChart s) x)).re) :
    LOrig b jumps (stopWord κ (β, θ, r)) s₁ := by
  obtain ⟨hs₁, hrel⟩ := hrel
  set γ := stopWord κ (β, θ, r) with hγ
  set m₁ := rProf (stChart s₁) with hm₁
  intro x hx hxJ hzJ
  have hc₁ : ContinuousAt m₁ x := by
    have hcl : ContinuousAt (lProf (stChart s₁)) (-x) :=
      hs₁.2.1.2.1.continuousAt (Ioi_mem_nhds (by linarith))
    have : m₁ = fun y => -lProf (stChart s₁) (-y) := by
      funext y; rw [hm₁, lProf_eq, neg_neg, neg_neg]
    rw [this]
    exact (hcl.comp (by simpa using continuous_neg.continuousAt (x := x))).neg
  have hP : ∀ᶠ x' in 𝓝 x, x' < stRecL s₁ ∧ b x' = b x ∧ m₁ x' ∉ γ.jumps ∧ γ.fn (m₁ x') = γ.fn (m₁ x) := by
    have h1 := hc₁.eventually (γ.isPiecewiseConstantBoundaryData (m₁ x) hzJ)
    have h2 := hc₁.eventually ((γ.jumps.finite_toSet.isClosed.isOpen_compl).mem_nhds hzJ)
    filter_upwards [Iio_mem_nhds hx, hb x hxJ, h1, h2] with x' h0 h3 h4 h5
    exact ⟨h0, h3, h5, h4⟩
  obtain ⟨x', hx'R, hx'J, hmx'J, hx'R₁, hbx', hm₁J, hfn⟩ :=
    exists_near_avoid_left hs.strictMonoOn (hrel x hx).1 jumps β.jumps hP
  obtain ⟨-, hal, heq⟩ := hrel x' hx'R₁
  have hneg : rProf (stChart s) x' < 0 := hs.neg hx'R
  calc γ.fn (m₁ x) = γ.fn (m₁ x') := hfn.symm
    _ = γ.fn (fwdMap (rdrv r) (rtime r) (rProf (stChart s) x')).re := by rw [heq]
    _ = β.fn (rProf (stChart s) x') :=
        stopWord_fn_fwdMap_neg hκ β θ r hneg hal hmx'J (by rw [← heq]; exact hm₁J)
    _ = b x' := hO x' hx'R hx'J hmx'J
    _ = b x := hbx'

/-- **The left record after a launch with zero lifetime** is unchanged. -/
theorem stRecL_launch_zero {s : ExplState} (hs : LProf s) (k : ℕ) {D : (ℝ≥0 → ℝ) × ℝ≥0∞} (θ : ℝ)
    (hreg : IsRegularDriver D) (h0 : D.2 = 0) : stRecL (ExplState.launch s k D θ ⊤) = stRecL s := by
  have hc := hs.1
  have hmin : min ⊤ D.2 ≠ ⊤ := by rw [h0]; simp
  obtain ⟨-, -, -, hrecL, -, -⟩ := launch_eq_of_ne_top s k D θ ⊤ hmin
  have hT : stopTime ⊤ D = 0 := by simp [stopTime, h0]
  have hW0 : stopDrv ⊤ D 0 = 0 := stopDrv_zero hreg ⊤
  rw [hrecL]
  unfold lRecL
  have he : {x : ℝ | x < stRecL s ∧ ¬ lAlive (stChart s) ⊤ D x} = ∅ := by
    ext x
    simp only [mem_ofPred_eq, mem_empty_iff_false, iff_false, not_and, not_not]
    intro hx
    unfold lAlive
    rw [hT, hc.eq_ofReal x]
    exact exists_isForwardSol_zero hW0 (hs.neg hx).ne
  rw [he, insert_empty_eq, csInf_singleton]

end LaunchL

/-! ### The boundary continuation to the left -/

section ContL

open PiecewiseConstantBoundaryData (rightLim leftLim jumpSet)

theorem stRecR_moveAlong_false (s : ExplState) (w : ℝ) (m : Bool) :
    stRecR (ExplState.moveAlong s false w m) = stRecR s := by
  obtain ⟨pieces, arcs, ret, lau, chart, st, pt, ang, rR, rL⟩ := s
  rfl

theorem stRecL_moveAlong_false (s : ExplState) (w : ℝ) (m : Bool) :
    stRecL (ExplState.moveAlong s false w m) = min (stRecL s) w := by
  obtain ⟨pieces, arcs, ret, lau, chart, st, pt, ang, rR, rL⟩ := s
  rfl

/-- The candidate restart marks of a leftward boundary continuation. -/
def restartSetL (κ : ℝ) (b : ℝ → ℝ) (jumps : Finset ℝ) (s : ExplState) : Finset ℝ :=
  (jumpSet b jumps).filter (fun x => x < stPt s ∧ leftLim b x + stAngle s * chiC κ < sleLambda κ)

/-- **The boundary continuation from a left threshold** moves left. -/
theorem contStep_thr_false {κ : ℝ} (b : ℝ → ℝ) (jumps : Finset ℝ) (s : ExplState)
    (hst : stStatus s = stThr (some false)) (pref : Bool) :
    ExplState.contStep κ b jumps s none pref =
      if hC : (restartSetL κ b jumps s).Nonempty then
        ExplState.moveAlong s false ((restartSetL κ b jumps s).max' hC) true else ExplState.moveToEnd s false := by
  obtain ⟨pieces, arcs, ret, lau, chart, st, pt, ang, rR, rL⟩ := s
  change st = _ at hst
  subst hst
  rfl

/-- **The boundary continuation from a zero-lifetime threshold with an admissible right seed** moves left when the
outward left height is high. -/
theorem contStep_thr_none_left {κ : ℝ} (b : ℝ → ℝ) (jumps : Finset ℝ) (s : ExplState)
    (hst : stStatus s = stThr none) (hR : -sleLambda κ < rightLim b (stPt s) + stAngle s * chiC κ)
    (hL : sleLambda κ ≤ leftLim b (stPt s) + stAngle s * chiC κ) :
    ExplState.contStep κ b jumps s none false =
      if hC : (restartSetL κ b jumps s).Nonempty then
        ExplState.moveAlong s false ((restartSetL κ b jumps s).max' hC) true else ExplState.moveToEnd s false := by
  obtain ⟨pieces, arcs, ret, lau, chart, st, pt, ang, rR, rL⟩ := s
  change st = _ at hst
  subst hst
  change -sleLambda κ < rightLim b pt + ang * chiC κ at hR
  change sleLambda κ ≤ leftLim b pt + ang * chiC κ at hL
  have h1 : ¬ rightLim b pt + ang * chiC κ ≤ -sleLambda κ := not_le.2 hR
  simp only [ExplState.contStep, h1, hL, false_and, ↓reduceIte]
  rfl

/-- **The left real connector is high** (the mirror of `add_le_neg_of_connector`). -/
theorem le_add_of_connector {κ θ : ℝ} {b : ℝ → ℝ} {jumps : Finset ℝ}
    (hb : IsPiecewiseConstantBoundaryData b jumps) {q w x : ℝ}
    (hhigh : sleLambda κ ≤ leftLim b q + θ * chiC κ)
    (hC : ∀ z ∈ jumpSet b jumps, w < z → z < q → sleLambda κ ≤ leftLim b z + θ * chiC κ)
    (hwx : w < x) (hxq : x < q) (hxJ : x ∉ jumps) : sleLambda κ ≤ b x + θ * chiC κ := by
  classical
  set G := (jumpSet b jumps).filter (fun z => x < z ∧ z < q) with hG
  have hzero : ∀ z₀, (∀ u ∈ jumpSet b jumps, x < u → u < z₀ → False) →
      ∑ u ∈ jumps.filter (fun u => x < u ∧ u < z₀), (rightLim b u - leftLim b u) = 0 := by
    intro z₀ hno
    refine Finset.sum_eq_zero fun u hu => ?_
    rw [Finset.mem_filter] at hu
    by_contra hne
    exact hno u (Finset.mem_filter.2 ⟨hu.1, fun h => hne (by rw [h, sub_self])⟩) hu.2.1 hu.2.2
  by_cases hGn : G.Nonempty
  · have hz : G.min' hGn ∈ jumpSet b jumps ∧ x < G.min' hGn ∧ G.min' hGn < q :=
      Finset.mem_filter.1 (Finset.min'_mem G hGn)
    have e := Exist.eq_leftLim_sub_sum_seed hb hz.2.1 hxJ
    rw [hzero _ fun u hu hxu huz => absurd (G.min'_le u (Finset.mem_filter.2 ⟨hu, hxu, huz.trans hz.2.2⟩))
      (not_le.2 huz), sub_zero] at e
    rw [e]
    exact hC _ hz.1 (hwx.trans hz.2.1) hz.2.2
  · have e := Exist.eq_leftLim_sub_sum_seed hb hxq hxJ
    rw [hzero _ fun u hu hxu huq => hGn ⟨u, Finset.mem_filter.2 ⟨hu, hxu, huq⟩⟩, sub_zero] at e
    rw [e]
    exact hhigh

/-- **The invariant at a launch of the left walk** (angle `θ`, word `β`). -/
def LInv (κ θ : ℝ) (b : ℝ → ℝ) (jumps : Finset ℝ) (β : BoundaryWord) (s : ExplState) : Prop :=
  (∀ y, 0 < y → y ∉ β.jumps → -sleLambda κ < β.fn y + θ * chiC κ) ∧ LProf s ∧ LOrig b jumps β s ∧ RRight s

/-- A launch-ready state of the left walk: at the root or on an arc at its mark (moving left), with the current point
at the left record. -/
def LReady (s : ExplState) : Prop :=
  (stStatus s = .inl () ∨ stStatus s = .inr (.inr (.inr (.inl (false, true))))) ∧ stPt s = stRecL s

/-- **The move to the next restart mark restores the left invariant** (the mirror of `rInv_moveAlong`). -/
theorem lInv_moveAlong {κ θ : ℝ} (hκ : 0 < κ) {b : ℝ → ℝ} {jumps : Finset ℝ} {γ : BoundaryWord} {s₁ : ExplState}
    (hs₁ : LProf s₁) (hO : LOrig b jumps γ s₁) (hRR : RRight s₁)
    (hγR : ∀ y, 0 < y → -sleLambda κ < γ.fn y + θ * chiC κ) {w : ℝ} (hw : w < stRecL s₁)
    (hhigh : ∀ x, w < x → x < stRecL s₁ → x ∉ jumps → sleLambda κ ≤ b x + θ * chiC κ) :
    LInv κ θ b jumps (BoundaryWord.shiftW (rProf (stChart s₁) w) γ) (ExplState.moveAlong s₁ false w true) := by
  have hc := hs₁.1
  set m := rProf (stChart s₁) with hmdef
  set a := m w with hadef
  have ha : a < 0 := hs₁.neg hw
  have hl : 0 < sleLambda κ := Sec4.sleLambda_pos hκ
  have hL₂ : stRecL (ExplState.moveAlong s₁ false w true) = w := by
    rw [stRecL_moveAlong_false, min_eq_right hw.le]
  have hR₂ : stRecR (ExplState.moveAlong s₁ false w true) = stRecR s₁ := stRecR_moveAlong_false _ _ _
  have hprof : rProf (stChart (ExplState.moveAlong s₁ false w true)) = fun x => m x - a := by
    funext x
    rw [stChart_moveAlong, rProf_recenter]
    rfl
  have hlprof : lProf (stChart (ExplState.moveAlong s₁ false w true)) = fun u => lProf (stChart s₁) u + a := by
    funext u
    rw [lProf_eq, hprof, lProf_eq]
    ring
  have hcw : ContinuousAt (lProf (stChart s₁)) (-w) := hs₁.2.1.2.1.continuousAt (Ioi_mem_nhds (by linarith))
  have hJ : ∀ z, z - a ∉ (BoundaryWord.shiftW a γ).jumps → z ∉ γ.jumps := fun z hz h =>
    hz (by rw [BoundaryWord.jumps_shiftW]; exact Finset.mem_image_of_mem _ h)
  have hmono := hs₁.strictMonoOn
  refine ⟨fun y hy hyJ => ?_, ⟨fun x => ?_, ?_, fun u hu => ?_, fun ε hε => ?_⟩, fun x hx hxJ hzJ => ?_, ?_, ?_⟩
  · -- the right side of the new word
    have hyJ' : y + a ∉ γ.jumps := hJ (y + a) (by rwa [add_sub_cancel_right])
    rw [BoundaryWord.fn_shiftW]
    rcases lt_trichotomy (y + a) 0 with hneg | hzero | hpos
    · -- on the connector
      obtain ⟨u, hu, hmu⟩ := LProf.exists_eq hs₁ (show 0 < -(y + a) by linarith)
      set x := -u with hxdef
      have hx : x < stRecL s₁ := by linarith
      have hmx : m x = y + a := by
        have : lProf (stChart s₁) u = -m x := by rw [lProf_eq, hxdef]
        linarith
      have hwx : w < x := by
        by_contra h
        push Not at h
        rcases h.lt_or_eq with h | h
        · have := hmono hx hw h
          linarith
        · rw [h] at hmx
          linarith
      have hcx : ContinuousAt m x := by
        have hcl : ContinuousAt (lProf (stChart s₁)) (-x) :=
          hs₁.2.1.2.1.continuousAt (Ioi_mem_nhds (by linarith))
        have : m = fun y => -lProf (stChart s₁) (-y) := by
          funext y; rw [hmdef, lProf_eq, neg_neg, neg_neg]
        rw [this]
        exact (hcl.comp (by simpa using continuous_neg.continuousAt (x := x))).neg
      have hP : ∀ᶠ x' in 𝓝 x, w < x' ∧ γ.fn (m x') = γ.fn (y + a) := by
        have h1 := hcx.eventually (by rw [hmx]; exact γ.isPiecewiseConstantBoundaryData (y + a) hyJ')
        filter_upwards [lt_mem_nhds hwx, h1] with x' h2 h3
        exact ⟨h2, h3⟩
      obtain ⟨x', hx'L, hx'J, hmx'J, hx'w, hfn⟩ := exists_near_avoid_left hmono hx jumps γ.jumps hP
      rw [← hfn, hO x' hx'L hx'J hmx'J]
      have := hhigh x' hx'w hx'L hx'J
      linarith
    · have hev := γ.isPiecewiseConstantBoundaryData (y + a) hyJ'
      obtain ⟨z, hz, hzgt⟩ := ((hev.filter_mono nhdsWithin_le_nhds).and
        (self_mem_nhdsWithin : Ioi (y + a) ∈ 𝓝[>] (y + a))).exists
      rw [← hz]
      exact hγR z (hzero ▸ hzgt)
    · exact hγR _ hpos
  · rw [stChart_moveAlong]
    change ((stChart s₁).1 x - (((stChart s₁).1 w).re : ℂ)).im = 0
    rw [Complex.sub_im, hc x, Complex.ofReal_im, sub_zero]
  · rw [hlprof, hL₂]
    have h1 := hs₁.2.1.mono_of_le (show -stRecL s₁ ≤ -w by linarith)
    have h2 : RightGood (fun u => lProf (stChart s₁) u - -a) (-w) := h1.sub_const (-a)
    simpa only [sub_neg_eq_add] using h2
  · rw [hL₂] at hu
    rw [hlprof]
    have h1 := hs₁.2.1.1 (show -w ∈ Ioi (-stRecL s₁) by simp only [Set.mem_Ioi]; linarith)
      (show u ∈ Ioi (-stRecL s₁) by simp only [Set.mem_Ioi]; linarith) hu
    have h2 : lProf (stChart s₁) (-w) = -a := by rw [lProf_eq, neg_neg]
    linarith
  · rw [hL₂]
    have hev : ∀ᶠ u in 𝓝 (-w), |lProf (stChart s₁) u + a| < ε := by
      have h2 : lProf (stChart s₁) (-w) = -a := by rw [lProf_eq, neg_neg]
      have := hcw.eventually (Metric.ball_mem_nhds (lProf (stChart s₁) (-w)) hε)
      filter_upwards [this] with u hu
      rw [Real.dist_eq, h2, sub_neg_eq_add] at hu
      exact hu
    obtain ⟨u, hu1, hu2⟩ := ((hev.filter_mono nhdsWithin_le_nhds).and
      (self_mem_nhdsWithin : Ioi (-w) ∈ 𝓝[>] (-w))).exists
    refine ⟨u, hu2, ?_⟩
    rw [hlprof]
    exact lt_of_le_of_lt (le_abs_self _) hu1
  · rw [hL₂] at hx
    rw [hprof] at hzJ ⊢
    rw [BoundaryWord.fn_shiftW, sub_add_cancel]
    exact hO x (hx.trans hw) hxJ (hJ (m x) hzJ)
  · rw [hprof, hR₂]
    exact hRR.1.sub_const a
  · intro x hx
    rw [hR₂] at hx
    rw [hprof]
    have := hRR.2 x hx
    linarith

end ContL

/-! ### The end of a stage of the left walk -/

section TailL

open PiecewiseConstantBoundaryData (rightLim leftLim jumpSet)

/-- **The end of a stage of the left walk** (the mirror of `rInv_tail`). -/
theorem lInv_tail {κ θ : ℝ} (hκ : 0 < κ) {b : ℝ → ℝ} {jumps : Finset ℝ}
    (hb : IsPiecewiseConstantBoundaryData b jumps) {γ : BoundaryWord} {s₁ s₂ : ExplState} (hs₁ : LProf s₁)
    (hO : LOrig b jumps γ s₁) (hRR : RRight s₁) (hγR : ∀ y, 0 < y → -sleLambda κ < γ.fn y + θ * chiC κ)
    (hpt : stPt s₁ = stRecL s₁) (hang : stAngle s₁ = θ) (hhigh : sleLambda κ ≤ leftLim b (stPt s₁) + θ * chiC κ)
    (he : s₂ = if hC : (restartSetL κ b jumps s₁).Nonempty then
      ExplState.moveAlong s₁ false ((restartSetL κ b jumps s₁).max' hC) true else ExplState.moveToEnd s₁ false)
    (hst : ∃ r, stStatus s₂ = .inr (.inr (.inr (.inl (r, true))))) :
    LInv κ θ b jumps (BoundaryWord.shiftW (rProf (stChart s₁) (stPt s₂)) γ) s₂ ∧ LReady s₂ ∧
      rProf (stChart s₁) (stPt s₂) = ((stChart s₁).1 0 - (stChart s₂).1 0).re := by
  split_ifs at he with hC
  swap
  · exfalso
    obtain ⟨r, hr⟩ := hst
    rw [he] at hr
    obtain ⟨pieces, arcs, ret, lau, chart, st, pt, ang, rR, rL⟩ := s₁
    exact absurd hr (by simp [ExplState.moveToEnd, stStatus])
  subst he
  set w := (restartSetL κ b jumps s₁).max' hC with hw
  have hmem := Finset.mem_filter.1 (Finset.max'_mem _ hC)
  have hwp : w < stPt s₁ := hmem.2.1
  have hhighc : ∀ x, w < x → x < stRecL s₁ → x ∉ jumps → sleLambda κ ≤ b x + θ * chiC κ := by
    intro x hwx hx hxJ
    rw [← hpt] at hx
    refine le_add_of_connector hb hhigh (fun z hz hwz hzq => ?_) hwx hx hxJ
    by_contra hlt
    push Not at hlt
    have hz' : z ∈ restartSetL κ b jumps s₁ := Finset.mem_filter.2 ⟨hz, hzq, by rw [hang]; exact hlt⟩
    exact absurd ((restartSetL κ b jumps s₁).le_max' z hz') (not_le.2 hwz)
  rw [stPt_moveAlong]
  refine ⟨lInv_moveAlong hκ hs₁ hO hRR hγR (by rw [← hpt]; exact hwp) hhighc, ⟨Or.inr ?_, ?_⟩, ?_⟩
  · obtain ⟨pieces, arcs, ret, lau, chart, st, pt, ang, rR, rL⟩ := s₁
    rfl
  · rw [stPt_moveAlong, stRecL_moveAlong_false, min_eq_right (by rw [← hpt]; exact hwp.le)]
  · rw [stChart_moveAlong]
    simp [InteractingSLE.Chart.recenter, rProf]

/-- **A launch ending at a left threshold**: no real point right of the old right record is hit, a real point left
of the old left record is, and the current point is the new left record. -/
theorem launch_thr_false {s : ExplState} {k : ℕ} {D : (ℝ≥0 → ℝ) × ℝ≥0∞} {θ : ℝ} (hfin : D.2 ≠ ⊤)
    (h : stStatus (ExplState.launch s k D θ ⊤) = stThr (some false)) :
    D.2 ≠ 0 ∧ (∃ x, x < stRecL s ∧ lHit (stChart s) ⊤ D x) ∧
      stPt (ExplState.launch s k D θ ⊤) = stRecL (ExplState.launch s k D θ ⊤) ∧
      stAngle (ExplState.launch s k D θ ⊤) = θ := by
  obtain ⟨-, hang, -, hrecL, hst, hpt⟩ := launch_eq_of_ne_top s k D θ ⊤ (min_top_ne_top hfin)
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
  by_cases hxR : ∃ x : ℝ, stRecR s < x ∧ lHit (stChart s) ⊤ D x
  · rw [ite_eq_left_of_eq_true _ _ (eq_true hxR)] at h
    exact absurd h (by simp [stThr])
  rw [ite_eq_right_of_eq_false _ _ (eq_false hxR)] at h
  by_cases hxL : ∃ x : ℝ, x < stRecL s ∧ lHit (stChart s) ⊤ D x
  · refine ⟨h0, hxL, ?_, hang⟩
    rw [hpt, hrecL]
    unfold lPt
    rw [ite_eq_right_of_eq_false _ _ (eq_false hnt), ite_eq_right_of_eq_false _ _ (eq_false h0),
      ite_eq_right_of_eq_false _ _ (eq_false hxR), ite_eq_left_of_eq_true _ _ (eq_true hxL)]
  · rw [ite_eq_right_of_eq_false _ _ (eq_false hxL)] at h
    exact absurd h (by simp [stThr, stDead])

/-- **A launch does not end at a new right record** when, at a finite positive lifetime, no positive real point of
its chart alive before the lifetime is swallowed at it (the chart being positive right of the right record). -/
theorem launch_ne_thr_true {s : ExplState} (hc : IsRealChart (stChart s)) (hRR : RRight s) (k : ℕ)
    {D : (ℝ≥0 → ℝ) × ℝ≥0∞} (θ : ℝ)
    (hnohit : D.2 ≠ ⊤ → D.2 ≠ 0 → ∀ y : ℝ, 0 < y →
      (∀ r < stopTime ⊤ D, ∃ u, IsForwardSol (stopDrv ⊤ D) (y : ℂ) r u) →
      ∃ u, IsForwardSol (stopDrv ⊤ D) (y : ℂ) (stopTime ⊤ D) u) :
    stStatus (ExplState.launch s k D θ ⊤) ≠ stThr (some true) := by
  by_cases htop : D.2 = ⊤
  · have hmin : min ⊤ D.2 = ⊤ := by rw [htop]; rfl
    rw [(launch_eq_of_top s k D θ ⊤ hmin).2.2.2.2.1]
    simp
  obtain ⟨-, -, -, -, hst, -⟩ := launch_eq_of_ne_top s k D θ ⊤ (min_top_ne_top htop)
  rw [hst]
  unfold lStatus
  rw [ite_eq_right_of_eq_false _ _ (eq_false (not_lt.2 le_top))]
  by_cases h0 : D.2 = 0
  · rw [ite_eq_left_of_eq_true _ _ (eq_true h0)]
    split <;> simp
  rw [ite_eq_right_of_eq_false _ _ (eq_false h0)]
  have hno : ¬ ∃ x : ℝ, stRecR s < x ∧ lHit (stChart s) ⊤ D x := by
    rintro ⟨x, hx, hhx⟩
    rw [lHit_iff hc] at hhx
    exact hhx.2 (hnohit htop h0 _ (hRR.2 x hx) hhx.1)
  rw [ite_eq_right_of_eq_false _ _ (eq_false hno)]
  split_ifs <;> simp

end TailL

end GW1W

end Theorem14

end InteractingSLE
