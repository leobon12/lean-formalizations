/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW1ActiveChartL
import InteractingSLE.Spec.ZhanGT4.CollarBoundary

/-!
# GW2a's connectors: the state invariant of a boundary-continued program (deterministic)

Packet PROVE-GW2A-CONN. Lemma GW1's active-word classification (supplement pp. 618–620) for an arbitrary finite
boundary-continued program, on both untouched original rays. For a state `s` of a run and a word `β`, the invariant
`GInv b jumps β s` says:

* the chart sends real points to real points (`IsRealChart`);
* right of the right record the real profile `x ↦ Re c(x)` is continuous, strictly increasing, unbounded and positive,
  and left of the left record the reflected profile is (`RightGood` and positivity on both rays);
* on both untouched original rays the word, read in the chart, is the original word (`GW1W.ROrig`, `GW1W.LOrig`; "it
  has the exact zero lift there");
* at every point of the untouched rays the chart is continuous from `ℍ` and is inverted by the chart inverse near the
  point (`ChartReadsAt`); this is what turns a chart-coordinate visit of a connector point into a physical visit.

`gInv_launch`: a launch with a good record at a finite stop restores the invariant for the stop word, whatever its
outcome (interior tip, threshold, zero lifetime). The real-flow facts are PROVE-STAGEDLAW2's (`isRealFlow_stop`,
`rightGood_comp`, `pos_alive_of_newRec_lt`), the word transport is PROVE-T14-GW1W's (`stopWord_fn_fwdMap`,
`stopWord_fn_fwdMap_neg`).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Filter Set Topology Finset
open scoped NNReal ENNReal
open QuantumZipper (IsForwardSol chiC fwdMap fwdMapInv fwdHull H)

namespace InteractingSLE

namespace Theorem14

namespace GW2aConn

open Exist Exist.StagedLaw Exist.Staged Restart GW1W

/-! ### Reading the chart at a real point -/

/-- **The chart reads the real point `y`**: the forward chart map is continuous at `y` from inside `ℍ`, and near `y`
it maps `ℍ` into `ℍ` and is inverted by the chart inverse. -/
def ChartReadsAt (c : Chart) (y : ℝ) : Prop :=
  Tendsto c.1 (𝓝[H] (y : ℂ)) (𝓝 (c.1 y)) ∧ ∀ᶠ z in 𝓝[H] (y : ℂ), c.1 z ∈ H ∧ c.2.1 (c.1 z) = z

theorem chartReadsAt_recenter {c : Chart} {y : ℝ} (hy : ChartReadsAt c y) (a : ℝ) :
    ChartReadsAt (c.recenter a) y := by
  obtain ⟨h1, h2⟩ := hy
  refine ⟨h1.sub_const _, ?_⟩
  filter_upwards [h2] with z hz
  refine ⟨?_, ?_⟩
  · show 0 < (c.1 z - (a : ℂ)).im
    rw [Complex.sub_im, Complex.ofReal_im, sub_zero]
    exact hz.1
  · show c.2.1 (c.1 z - (a : ℂ) + (a : ℂ)) = z
    rw [sub_add_cancel]
    exact hz.2

/-- **A Loewner stage keeps the reading at a point alive through the stage.** -/
theorem chartReadsAt_loewner {c : Chart} {y : ℝ} (hy : ChartReadsAt c y) {W : ℝ → ℝ} (hW : Continuous W)
    (hW0 : W 0 = 0) {T : ℝ} (hT : 0 ≤ T) {u : ℝ → ℂ} (hu : IsForwardSol W (c.1 y) T u) :
    ChartReadsAt (c.loewner W T) y := by
  obtain ⟨h1, h2⟩ := hy
  have hp : Tendsto c.1 (𝓝[H] (y : ℂ)) (𝓝[H] (c.1 y)) :=
    tendsto_nhdsWithin_iff.2 ⟨h1, h2.mono fun z hz => hz.1⟩
  have hf := InteractingSLE.tendsto_fwdMap_of_isForwardSol hW hT hu
  have hval : fwdMap W T (c.1 y) = u T := InteractingSLE.fwdMap_eq_of_isForwardSol hW hu ⟨hT, le_rfl⟩
  refine ⟨?_, ?_⟩
  · change Tendsto (fun z => fwdMap W T (c.1 z)) _ (𝓝 (fwdMap W T (c.1 y)))
    rw [hval]
    exact hf.comp hp
  · filter_upwards [h2, hp.eventually (ZhanGT4.eventually_not_mem_fwdHull hW hT hu)] with z hz hzK
    refine ⟨QuantumZipper.FwdHolo.mapsTo_fwdMap hW hT hzK, ?_⟩
    change c.2.1 (fwdMapInv W T (fwdMap W T (c.1 z))) = z
    rw [QuantumZipper.RS.fwdMapInv_fwdMap hW hW0 hT hzK]
    exact hz.2

/-! ### The invariant -/

/-- **The state invariant** (Lemma GW1's classification on both untouched original rays, for any program). -/
def GInv (b : ℝ → ℝ) (jumps : Finset ℝ) (β : BoundaryWord) (s : ExplState) : Prop :=
  IsRealChart (stChart s) ∧
    (RightGood (rProf (stChart s)) (stRecR s) ∧ ∀ x, stRecR s < x → 0 < rProf (stChart s) x) ∧
    (RightGood (lProf (stChart s)) (-stRecL s) ∧ ∀ x, -stRecL s < x → 0 < lProf (stChart s) x) ∧
    ROrig b jumps β s ∧ LOrig b jumps β s ∧
    ∀ y : ℝ, stRecR s < y ∨ y < stRecL s → ChartReadsAt (stChart s) y

/-- The reflected profile is strictly increasing on `(−recL, ∞)` iff the profile is on `(−∞, recL)`. -/
theorem strictMonoOn_of_lProf {c : Chart} {a : ℝ} (h : StrictMonoOn (lProf c) (Ioi (-a))) :
    StrictMonoOn (rProf c) (Iio a) := fun x hx y hy hxy => by
  have := h (show -y ∈ Ioi (-a) from by simp only [Set.mem_Iio, Set.mem_Ioi] at hy ⊢; linarith)
    (show -x ∈ Ioi (-a) from by simp only [Set.mem_Iio, Set.mem_Ioi] at hx ⊢; linarith) (by linarith)
  simp only [lProf_eq, neg_neg] at this
  linarith

theorem rProf_neg_of_lProf {c : Chart} {a : ℝ} (h : ∀ x, -a < x → 0 < lProf c x) {x : ℝ} (hx : x < a) :
    rProf c x < 0 := by
  have := h (-x) (by linarith)
  rw [lProf_eq, neg_neg] at this
  linarith

/-! ### Transport of the original word through a stage -/

variable {κ : ℝ} {b : ℝ → ℝ} {jumps : Finset ℝ}

/-- **The original word survives on the new right ray**: if right of `a₁ ≥ a` the new profile is the real flow of the
record composed with the old profile (alive points), the stop word is the original word there. -/
theorem rOrig_rel (hκ : 0 < κ) (hb : IsPiecewiseConstantBoundaryData b jumps) {β : BoundaryWord} {m m₁ : ℝ → ℝ}
    {a a₁ : ℝ} (hm : StrictMonoOn m (Ioi a)) (hpos : ∀ x, a < x → 0 < m x)
    (hO : ∀ x, a < x → x ∉ jumps → m x ∉ β.jumps → β.fn (m x) = b x) (hm₁ : ContinuousOn m₁ (Ioi a₁))
    (haa : a ≤ a₁) {r : RecData} (θ : ℝ)
    (hrel : ∀ x, a₁ < x → (∃ u, IsForwardSol (rdrv r) (m x : ℂ) (rtime r) u) ∧
      m₁ x = (fwdMap (rdrv r) (rtime r) (m x)).re) :
    ∀ x, a₁ < x → x ∉ jumps → m₁ x ∉ (stopWord κ (β, θ, r)).jumps → (stopWord κ (β, θ, r)).fn (m₁ x) = b x := by
  set γ := stopWord κ (β, θ, r) with hγ
  intro x hx hxJ hzJ
  have hc₁ : ContinuousAt m₁ x := hm₁.continuousAt (Ioi_mem_nhds hx)
  have hP : ∀ᶠ x' in 𝓝 x, a₁ < x' ∧ b x' = b x ∧ m₁ x' ∉ γ.jumps ∧ γ.fn (m₁ x') = γ.fn (m₁ x) := by
    have h1 := hc₁.eventually (γ.isPiecewiseConstantBoundaryData (m₁ x) hzJ)
    have h2 := hc₁.eventually ((γ.jumps.finite_toSet.isClosed.isOpen_compl).mem_nhds hzJ)
    filter_upwards [Ioi_mem_nhds hx, hb x hxJ, h1, h2] with x' h0 h3 h4 h5
    exact ⟨h0, h3, h5, h4⟩
  obtain ⟨x', hx'R, hx'J, hmx'J, hx'R₁, hbx', hm₁J, hfn⟩ :=
    exists_near_avoid hm (haa.trans_lt hx) jumps β.jumps hP
  obtain ⟨hal, heq⟩ := hrel x' hx'R₁
  calc γ.fn (m₁ x) = γ.fn (m₁ x') := hfn.symm
    _ = γ.fn (fwdMap (rdrv r) (rtime r) (m x')).re := by rw [heq]
    _ = β.fn (m x') := stopWord_fn_fwdMap hκ β θ r (hpos x' hx'R) hal hmx'J (by rw [← heq]; exact hm₁J)
    _ = b x' := hO x' hx'R hx'J hmx'J
    _ = b x := hbx'

/-- **The original word survives on the new left ray** (the mirror of `rOrig_rel`). -/
theorem lOrig_rel (hκ : 0 < κ) (hb : IsPiecewiseConstantBoundaryData b jumps) {β : BoundaryWord} {m m₁ : ℝ → ℝ}
    {a a₁ : ℝ} (hm : StrictMonoOn m (Iio a)) (hneg : ∀ x, x < a → m x < 0)
    (hO : ∀ x, x < a → x ∉ jumps → m x ∉ β.jumps → β.fn (m x) = b x) (hm₁ : ContinuousOn m₁ (Iio a₁))
    (haa : a₁ ≤ a) {r : RecData} (θ : ℝ)
    (hrel : ∀ x, x < a₁ → (∃ u, IsForwardSol (rdrv r) (m x : ℂ) (rtime r) u) ∧
      m₁ x = (fwdMap (rdrv r) (rtime r) (m x)).re) :
    ∀ x, x < a₁ → x ∉ jumps → m₁ x ∉ (stopWord κ (β, θ, r)).jumps → (stopWord κ (β, θ, r)).fn (m₁ x) = b x := by
  set γ := stopWord κ (β, θ, r) with hγ
  intro x hx hxJ hzJ
  have hc₁ : ContinuousAt m₁ x := hm₁.continuousAt (Iio_mem_nhds hx)
  have hP : ∀ᶠ x' in 𝓝 x, x' < a₁ ∧ b x' = b x ∧ m₁ x' ∉ γ.jumps ∧ γ.fn (m₁ x') = γ.fn (m₁ x) := by
    have h1 := hc₁.eventually (γ.isPiecewiseConstantBoundaryData (m₁ x) hzJ)
    have h2 := hc₁.eventually ((γ.jumps.finite_toSet.isClosed.isOpen_compl).mem_nhds hzJ)
    filter_upwards [Iio_mem_nhds hx, hb x hxJ, h1, h2] with x' h0 h3 h4 h5
    exact ⟨h0, h3, h5, h4⟩
  obtain ⟨x', hx'R, hx'J, hmx'J, hx'R₁, hbx', hm₁J, hfn⟩ :=
    exists_near_avoid_left hm (hx.trans_le haa) jumps β.jumps hP
  obtain ⟨hal, heq⟩ := hrel x' hx'R₁
  calc γ.fn (m₁ x) = γ.fn (m₁ x') := hfn.symm
    _ = γ.fn (fwdMap (rdrv r) (rtime r) (m x')).re := by rw [heq]
    _ = β.fn (m x') := stopWord_fn_fwdMap_neg hκ β θ r (hneg x' hx'R) hal hmx'J (by rw [← heq]; exact hm₁J)
    _ = b x' := hO x' hx'R hx'J hmx'J
    _ = b x := hbx'

theorem continuousOn_rProf_of_lProf {c : Chart} {a : ℝ} (h : ContinuousOn (lProf c) (Ioi (-a))) :
    ContinuousOn (rProf c) (Iio a) := by
  have e : rProf c = fun x => -lProf c (-x) := by
    funext x; rw [lProf_eq, neg_neg, neg_neg]
  rw [e]
  refine (h.comp continuousOn_neg fun x hx => ?_).neg
  simp only [Set.mem_Iio, Set.mem_Ioi] at hx ⊢
  linarith

/-! ### A launch with a good record -/

/-- **A launch with a good record at a finite stop restores the invariant for the stop word** (Lemma GW1, p. 619:
"every finite active fiber … the untouched original right ray"; whatever the outcome of the stage). -/
theorem gInv_launch (hκ : 0 < κ) (hb : IsPiecewiseConstantBoundaryData b jumps) {β : BoundaryWord}
    {s : ExplState} (hI : GInv b jumps β s) (k : ℕ) {D : (ℝ≥0 → ℝ) × ℝ≥0∞} (θ : ℝ) (t : ℝ≥0∞)
    (hreg : IsRegularDriver D) (hgood : LocalExt.IsDrvGood (recHist (recOf t D))) (hfin : min t D.2 ≠ ⊤) :
    GInv b jumps (stopWord κ (β, θ, recOf t D)) (ExplState.launch s k D θ t) := by
  obtain ⟨hc, ⟨hm, hpos⟩, ⟨hl, hlpos⟩, hO, hOL, hread⟩ := hI
  obtain ⟨hch, -, hrec, hrecL, -, -⟩ := launch_eq_of_ne_top s k D θ t hfin
  have hWr : rdrv (recOf t D) = stopDrv t D := by rw [rdrv_recOf]; exact recDrv_eq_stopDrv hreg hgood
  have hrt : rtime (recOf t D) = stopTime t D := rtime_recOf t D
  set W := stopDrv t D with hWdef
  set T := stopTime t D with hTdef
  have hW : Continuous W := by rw [← hWr]; exact continuous_rdrv _
  have hW0 : W 0 = 0 := stopDrv_zero hreg t
  have hT0 : 0 ≤ T := stopTime_nonneg t D
  have hflow := isRealFlow_stop hreg hgood
  set A : ℝ → Prop := fun y : ℝ => ∃ u, IsForwardSol W (y : ℂ) T u with hAdef
  set f : ℝ → ℝ := fun y => (fwdMap W T y).re with hfdef
  set m := rProf (stChart s) with hmdef
  have hH : IsRealHalf A f := hflow.1
  set A' : ℝ → Prop := fun y : ℝ => ∃ u, IsForwardSol W ((-y : ℝ) : ℂ) T u with hA'def
  set f' : ℝ → ℝ := fun y => -(fwdMap W T ((-y : ℝ) : ℂ)).re with hf'def
  set ml := lProf (stChart s) with hmldef
  have hH' : IsRealHalf A' f' := hflow.2
  set s₁ := ExplState.launch s k D θ t with hs₁
  have hrec' : stRecR s₁ = newRec m (stRecR s) A := by rw [hrec, lRecR_eq_newRec hc]
  have hrecL' : -stRecL s₁ = newRec ml (-stRecL s) A' := by rw [hrecL, lRecL_eq_newRec hc, neg_neg]
  have hprofR : ∀ x, rProf (stChart s₁) x = (fwdMap W T (m x)).re := by
    intro x
    rw [hch]
    change (fwdMap W T ((stChart s).1 x)).re = _
    rw [hc.eq_ofReal x]
  have hprof : rProf (stChart s₁) = fun x => f (m x) := funext hprofR
  have hprofL : lProf (stChart s₁) = fun u => f' (ml u) := by
    funext u
    rw [lProf_eq, hprofR]
    change -(fwdMap W T (rProf (stChart s) (-u) : ℂ)).re = -(fwdMap W T ((-(lProf (stChart s) u) : ℝ) : ℂ)).re
    rw [lProf_eq, neg_neg]
  have hle := le_newRec hm hH
  have hleL := le_newRec hl hH'
  have hRG : RightGood (rProf (stChart s₁)) (stRecR s₁) := by
    rw [hprof, hrec']
    exact rightGood_comp hm hH
  have hLG : RightGood (lProf (stChart s₁)) (-stRecL s₁) := by
    rw [hprofL, hrecL']
    exact rightGood_comp hl hH'
  -- aliveness right of the new right record and left of the new left record
  have halR : ∀ x, stRecR s₁ < x → stRecR s < x ∧ 0 < m x ∧ A (m x) := by
    intro x hx
    rw [hrec'] at hx
    obtain ⟨h0, hA⟩ := pos_alive_of_newRec_lt hm hH hx
    exact ⟨hle.trans_lt hx, h0, hA⟩
  have halL : ∀ x, x < stRecL s₁ → x < stRecL s ∧ 0 < ml (-x) ∧ A' (ml (-x)) := by
    intro x hx
    have hu : newRec ml (-stRecL s) A' < -x := by rw [← hrecL']; linarith
    obtain ⟨h0, hA⟩ := pos_alive_of_newRec_lt hl hH' hu
    exact ⟨by linarith [hleL.trans_lt hu], h0, hA⟩
  have hmL : ∀ x, ((-(ml (-x)) : ℝ) : ℂ) = (m x : ℂ) := fun x => by rw [hmldef, lProf_eq, neg_neg, neg_neg]
  refine ⟨fun x => ?_, ⟨hRG, fun x hx => ?_⟩, ⟨hLG, fun u hu => ?_⟩, ?_, ?_, fun y hy => ?_⟩
  · rw [hch]
    change (fwdMap W T ((stChart s).1 x)).im = 0
    rw [hc.eq_ofReal x]
    exact im_fwdMap_ofReal W hT0 _
  · obtain ⟨-, h0, hA⟩ := halR x hx
    rw [hprof]
    exact hH.2.2.2.1 _ h0 hA
  · rw [hrecL'] at hu
    obtain ⟨h0, hA⟩ := pos_alive_of_newRec_lt hl hH' hu
    rw [hprofL]
    exact hH'.2.2.2.1 _ h0 hA
  · refine rOrig_rel hκ hb hm.1 hpos hO hRG.2.1 (by rw [hrec']; exact hle) θ fun x hx => ?_
    obtain ⟨-, -, hA⟩ := halR x hx
    rw [hWr, hrt]
    exact ⟨hA, hprofR x⟩
  · have hneg : ∀ x, x < stRecL s → m x < 0 := fun x hx => rProf_neg_of_lProf hlpos hx
    have hle' : stRecL s₁ ≤ stRecL s := by linarith [hleL, hrecL']
    refine lOrig_rel hκ hb (strictMonoOn_of_lProf hl.1) hneg hOL (continuousOn_rProf_of_lProf hLG.2.1) hle' θ
      fun x hx => ?_
    obtain ⟨-, -, hA⟩ := halL x hx
    rw [hWr, hrt]
    refine ⟨?_, hprofR x⟩
    rw [← hmL x]
    exact hA
  · rw [hch]
    rcases hy with hy | hy
    · obtain ⟨hy', -, hA⟩ := halR y hy
      obtain ⟨u, hu⟩ := hA
      rw [← hc.eq_ofReal y] at hu
      exact chartReadsAt_loewner (hread y (Or.inl hy')) hW hW0 hT0 hu
    · obtain ⟨hy', -, hA⟩ := halL y hy
      obtain ⟨u, hu⟩ := hA
      rw [hmL y, ← hc.eq_ofReal y] at hu
      exact chartReadsAt_loewner (hread y (Or.inr hy')) hW hW0 hT0 hu

/-! ### The new profile at a swallowing hit tends to `0` -/

/-- **After a launch whose real flow comes arbitrarily close to `0` on alive points, the new profile does too**, when
some point right of the old record is swallowed (`GW1W.exists_newRec_lt_small` without the old profile tending to
`0`: every alive point lies beyond the swallowed one, hence in the range of the old profile). -/
theorem exists_newRec_lt_small_of_dead {m : ℝ → ℝ} {a : ℝ} {A : ℝ → Prop} {f : ℝ → ℝ} (hm : RightGood m a)
    (hH : IsRealHalf A f) {x₀ : ℝ} (hx₀ : a < x₀) (hdead : ¬ A (m x₀))
    (hq : ∀ ε > 0, ∃ q, 0 < q ∧ A q ∧ f q < ε) {ε : ℝ} (hε : 0 < ε) :
    ∃ x, newRec m a A < x ∧ f (m x) < ε := by
  obtain ⟨q, hq0, hAq, hfq⟩ := hq (ε / 2) (half_pos hε)
  obtain ⟨η, hη, hηf⟩ := hH.2.2.2.2.2.1 q hq0 hAq (ε / 2) (half_pos hε)
  have hq' : q < q + η / 2 := by linarith
  have hAq' : A (q + η / 2) := hH.2.1 q _ hq0 hq' hAq
  have hex : ∀ y, 0 < y → A y → ∃ x, a < x ∧ m x = y := fun y hy hAy => by
    have hlt : m x₀ < y := by
      by_contra hle
      push Not at hle
      rcases hle.lt_or_eq with hlt | heq
      · exact hdead (hH.2.1 y _ hy hlt hAy)
      · exact hdead (heq ▸ hAy)
    exact (exists_eq_iff_exists_lt hm).2 ⟨x₀, hx₀, hlt⟩
  obtain ⟨x₁, hx₁, hmx₁⟩ := hex q hq0 hAq
  obtain ⟨x₂, hx₂, hmx₂⟩ := hex (q + η / 2) (hq0.trans hq') hAq'
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

/-- **At a right hit the new right profile tends to `0`** (the threshold point is the new right record). -/
theorem rSmall_launch {β : BoundaryWord} {s : ExplState} (hI : GInv b jumps β s) (k : ℕ)
    {D : (ℝ≥0 → ℝ) × ℝ≥0∞} (θ : ℝ) (t : ℝ≥0∞) (hreg : IsRegularDriver D)
    (hgood : LocalExt.IsDrvGood (recHist (recOf t D))) (hfin : min t D.2 ≠ ⊤)
    (hhit : ∃ x, stRecR s < x ∧ lHit (stChart s) t D x) :
    ∀ ε > 0, ∃ x, stRecR (ExplState.launch s k D θ t) < x ∧
      rProf (stChart (ExplState.launch s k D θ t)) x < ε := by
  obtain ⟨hc, ⟨hm, hpos⟩, -, -, -, -⟩ := hI
  obtain ⟨hch, -, hrec, -, -, -⟩ := launch_eq_of_ne_top s k D θ t hfin
  have hWr : rdrv (recOf t D) = stopDrv t D := by rw [rdrv_recOf]; exact recDrv_eq_stopDrv hreg hgood
  set W := stopDrv t D with hWdef
  set T := stopTime t D with hTdef
  have hW : Continuous W := by rw [← hWr]; exact continuous_rdrv _
  have hW0 : W 0 = 0 := stopDrv_zero hreg t
  have hT0 : 0 ≤ T := stopTime_nonneg t D
  have hH := (isRealFlow_stop hreg hgood).1
  set A : ℝ → Prop := fun y : ℝ => ∃ u, IsForwardSol W (y : ℂ) T u with hAdef
  set f : ℝ → ℝ := fun y => (fwdMap W T y).re with hfdef
  set m := rProf (stChart s) with hmdef
  have hrec' : stRecR (ExplState.launch s k D θ t) = newRec m (stRecR s) A := by
    rw [hrec, lRecR_eq_newRec hc]
  have hprof : rProf (stChart (ExplState.launch s k D θ t)) = fun x => f (m x) := by
    funext x
    rw [hch]
    change (fwdMap W T ((stChart s).1 x)).re = (fwdMap W T (m x : ℂ)).re
    rw [hc.eq_ofReal x]
  intro ε hε
  rw [hrec', hprof]
  obtain ⟨x₀, hx₀, hhit₀, hdead₀⟩ := hhit
  have hy₀ : 0 < m x₀ := hpos x₀ hx₀
  have hdead : ¬ A (m x₀) := by
    intro h
    apply hdead₀
    change ∃ u, IsForwardSol W ((stChart s).1 x₀) T u
    rw [hc.eq_ofReal x₀]
    exact h
  refine exists_newRec_lt_small_of_dead hm hH hx₀ hdead (fun ε' hε' => ?_) hε
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
  exact exists_alive_fwdMap_lt hW hW0 hy₀ hsw hε'

/-- **At a left hit the new reflected left profile tends to `0`** (the mirror of `rSmall_launch`). -/
theorem lSmall_launch {β : BoundaryWord} {s : ExplState} (hI : GInv b jumps β s) (k : ℕ)
    {D : (ℝ≥0 → ℝ) × ℝ≥0∞} (θ : ℝ) (t : ℝ≥0∞) (hreg : IsRegularDriver D)
    (hgood : LocalExt.IsDrvGood (recHist (recOf t D))) (hfin : min t D.2 ≠ ⊤)
    (hhit : ∃ x, x < stRecL s ∧ lHit (stChart s) t D x) :
    ∀ ε > 0, ∃ x, -stRecL (ExplState.launch s k D θ t) < x ∧
      lProf (stChart (ExplState.launch s k D θ t)) x < ε := by
  obtain ⟨hc, -, ⟨hm, hpos⟩, -, -, -⟩ := hI
  obtain ⟨hch, -, -, hrecL, -, -⟩ := launch_eq_of_ne_top s k D θ t hfin
  have hWr : rdrv (recOf t D) = stopDrv t D := by rw [rdrv_recOf]; exact recDrv_eq_stopDrv hreg hgood
  set W := stopDrv t D with hWdef
  set T := stopTime t D with hTdef
  have hW : Continuous W := by rw [← hWr]; exact continuous_rdrv _
  have hW0 : W 0 = 0 := stopDrv_zero hreg t
  have hT0 : 0 ≤ T := stopTime_nonneg t D
  have hH := (isRealFlow_stop hreg hgood).2
  set A' : ℝ → Prop := fun y : ℝ => ∃ u, IsForwardSol W ((-y : ℝ) : ℂ) T u with hA'def
  set f' : ℝ → ℝ := fun y => -(fwdMap W T ((-y : ℝ) : ℂ)).re with hf'def
  set m := lProf (stChart s) with hmdef
  have hH' : IsRealHalf A' f' := hH
  have hrecL' : -stRecL (ExplState.launch s k D θ t) = newRec m (-stRecL s) A' := by
    rw [hrecL, lRecL_eq_newRec hc, neg_neg]
  have hprofR : ∀ x, rProf (stChart (ExplState.launch s k D θ t)) x = (fwdMap W T (rProf (stChart s) x)).re := by
    intro x
    rw [hch]
    change (fwdMap W T ((stChart s).1 x)).re = _
    rw [hc.eq_ofReal x]
  have hprofL : lProf (stChart (ExplState.launch s k D θ t)) = fun u => f' (m u) := by
    funext u
    rw [lProf_eq, hprofR]
    change -(fwdMap W T (rProf (stChart s) (-u) : ℂ)).re = -(fwdMap W T ((-(lProf (stChart s) u) : ℝ) : ℂ)).re
    rw [lProf_eq, neg_neg]
  intro ε hε
  rw [hrecL', hprofL]
  obtain ⟨x₀, hx₀, hhit₀, hdead₀⟩ := hhit
  have hu₀ : -stRecL s < -x₀ := by linarith
  have hy₀ : 0 < m (-x₀) := hpos _ hu₀
  have hc₀ : (stChart s).1 x₀ = ((-(m (-x₀)) : ℝ) : ℂ) := by
    rw [hc.eq_ofReal x₀, hmdef, lProf_eq, neg_neg, neg_neg]
  have hdeadA : ¬ A' (m (-x₀)) := by
    intro h
    apply hdead₀
    change ∃ u, IsForwardSol W ((stChart s).1 x₀) T u
    rw [hc₀]
    exact h
  refine exists_newRec_lt_small_of_dead hm hH' hu₀ hdeadA (fun ε' hε' => ?_) hε
  have hdead : ¬ ∃ u, IsForwardSol (-W) ((m (-x₀) : ℝ) : ℂ) T u := by
    rw [alive_neg_iff]
    exact hdeadA
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
  obtain ⟨q, hq0, hAq, hfq⟩ := exists_alive_fwdMap_lt hW.neg (by simp [hW0]) hy₀ hsw hε'
  refine ⟨q, hq0, (alive_neg_iff W T q).1 hAq, ?_⟩
  have hr := QuantumZipper.F1.fwdMap_reflect_ofReal W hT0 (-q)
  rw [neg_neg] at hr
  change -(fwdMap W T ((-q : ℝ) : ℂ)).re < ε'
  rw [hr, Complex.neg_re] at hfq
  linarith

/-! ### The root -/

/-- **The invariant at the root** (the original word recentred at `0`). -/
theorem gInv_init {c₀ : BoundaryWord} (hc₀J : c₀.jumps = jumps) (hc₀ : ∀ y ∉ jumps, c₀.fn y = b y) :
    GInv b jumps (BoundaryWord.shiftW 0 c₀) (ExplState.init 0) := by
  have hprof : rProf (stChart (ExplState.init 0)) = fun x => x := by
    funext x
    simp [rProf, ExplState.init, InteractingSLE.Chart.recenter, InteractingSLE.Chart.id]
  have hlprof : lProf (stChart (ExplState.init 0)) = fun x => x := by
    funext x
    simp [lProf, ExplState.init, InteractingSLE.Chart.recenter, InteractingSLE.Chart.id]
  have hR : stRecR (ExplState.init 0) = 0 := rfl
  have hL : stRecL (ExplState.init 0) = 0 := rfl
  have hJ : ∀ y, y ∉ (BoundaryWord.shiftW 0 c₀).jumps → y ∉ jumps := fun y hy h => hy (by
    rw [BoundaryWord.jumps_shiftW, hc₀J]
    exact Finset.mem_image.2 ⟨y, h, by ring⟩)
  have hgood : RightGood (fun x : ℝ => x) 0 :=
    ⟨strictMonoOn_id, continuousOn_id, fun M => ⟨max M 0 + 1, by positivity, by linarith [le_max_left M 0]⟩⟩
  have hid : stChart (ExplState.init 0) = (fun z => z - ((0 : ℝ) : ℂ), fun z => z + ((0 : ℝ) : ℂ),
      Chart.id.2.2) := rfl
  refine ⟨fun x => ?_, ⟨?_, fun x hx => ?_⟩, ⟨?_, fun x hx => ?_⟩, fun x hx hxJ hzJ => ?_, fun x hx hxJ hzJ => ?_,
    fun y _ => ?_⟩
  · simp [ExplState.init, InteractingSLE.Chart.recenter, InteractingSLE.Chart.id]
  · rw [hprof, hR]; exact hgood
  · rw [hprof]; rw [hR] at hx; exact hx
  · rw [hlprof]; rw [hL, neg_zero]; exact hgood
  · rw [hlprof]; rw [hL, neg_zero] at hx; exact hx
  · rw [hprof] at hzJ ⊢
    rw [BoundaryWord.fn_shiftW, add_zero]
    exact hc₀ x hxJ
  · rw [hprof] at hzJ ⊢
    rw [BoundaryWord.fn_shiftW, add_zero]
    exact hc₀ x hxJ
  · rw [hid]
    refine ⟨?_, eventually_nhdsWithin_of_forall fun z hz => ?_⟩
    · exact (continuous_id.sub continuous_const).continuousAt.tendsto.mono_left nhdsWithin_le_nhds
    · refine ⟨?_, ?_⟩
      · show 0 < (z - ((0 : ℝ) : ℂ)).im
        rw [Complex.ofReal_zero, sub_zero]
        exact hz
      · show z - ((0 : ℝ) : ℂ) + ((0 : ℝ) : ℂ) = z
        ring

end GW2aConn

end Theorem14

end InteractingSLE
