/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.SB2KLW
import InteractingSLE.Spec.Supplement.GW1WalkExitInverse
import InteractingSLE.Spec.Supplement.GB6LifeBase
import InteractingSLE.Spec.ZhanGT4.A1G3L2Zero

/-!
# SB2(1)'s active word: the lower walk's left side through one launch

Packet PROVE-T14-SB2WORD, step 1 of `planning/handoffs/PROVE-T14-SB2FIN5.md` §R3. SB2(1)'s active word (supplement
p. 632, `source/spec/p625-671.md` L127: "the active lower-flow sides before the next seed have height `−λ − φχ = −Λ`.
The exposed rightward connectors retain their original heights `H ≤ −Λ` [...] Any still exposed initial bridge keeps
its original height") is read off the lower walk's staged word through four facts about the left side of the walk's
state, all carried through a launch here (deterministic):

* `LLow`: right of the chart image of the untouched left ray (and left of the tip) the word is low, `≤ −λ − θχ`;
* `LCont`: the chart is continuous at every real point of the untouched left ray (so its boundary values there are
  its values);
* `PiecesRealBound`: every real point of a recorded piece lies at or right of the left record.

Results: **`lLow_launch`**, **`lCont_launch`**, **`piecesRealBound_launch`**; tools `exists_rat_lt_of_lt_markPosL`,
`exists_alive_eq_of_lt_re` (intermediate values of the real flow on the negative half-line),
`markPosL_mem_jumps_stopWord`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Filter Set Topology
open scoped NNReal ENNReal
open QuantumZipper (IsForwardSol chiC fwdMap fwdMapInv H)

namespace InteractingSLE.Theorem14.GW1W

open Exist Exist.StagedLaw Exist.Staged Restart

/-! ### The real flow on the negative half-line -/

section Flow

variable {w : ℝ → ℝ} {T : ℝ}

/-- **Below a left mark position there is a larger value of the flow at an alive rational point left of the mark's
start** (the definition of `markPosL` as a supremum, by reflection of `le_markPos`). -/
theorem exists_rat_lt_of_lt_markPosL (hw : Continuous w) (hw0 : w 0 = 0) (hT : 0 ≤ T) {x y : ℝ}
    (hy : y < markPosL w T x) :
    ∃ q : ℚ, (q : ℝ) < x ∧ (∃ u, IsForwardSol w ((q : ℝ) : ℂ) T u) ∧ y < (fwdMap w T ((q : ℝ) : ℂ)).re := by
  by_contra hno
  push Not at hno
  have h := le_markPos (w := fun s => -w s) hw.neg (by simp [hw0]) hT (x := -x) (c := -y) fun q hq hal => by
    have hal' : ∃ u, IsForwardSol w (((-(q : ℝ)) : ℝ) : ℂ) T u := (alive_neg_iff w T q).1 hal
    have hq' : ((-q : ℚ) : ℝ) < x := by push_cast; linarith
    have hle := hno (-q) hq' (by rw [Rat.cast_neg]; exact hal')
    have hr : (fwdMap (fun s => -w s) T ((q : ℝ) : ℂ)).re = -(fwdMap w T (((-q : ℚ) : ℝ) : ℂ)).re := by
      have e := QuantumZipper.F1.fwdMap_reflect_ofReal w hT (-(q : ℝ))
      rw [neg_neg] at e
      change (fwdMap (-w) T ((q : ℝ) : ℂ)).re = _
      rw [e, Complex.neg_re]
      push_cast
      rfl
    rw [hr]
    linarith
  have e : markPosL w T x = -markPos (fun s => -w s) T (-x) := rfl
  linarith

/-- **Intermediate values of the real flow on the negative half-line**: below the image of an alive negative point
`q`, every value is the image of an alive point left of `q`. -/
theorem exists_alive_eq_of_lt_re (hw : Continuous w) (hw0 : w 0 = 0) (hT : 0 ≤ T) {q y : ℝ} (hq : q < 0)
    (hqA : ∃ u, IsForwardSol w (q : ℂ) T u) (hy : y < (fwdMap w T q).re) :
    ∃ y₀, y₀ < q ∧ (∃ u, IsForwardSol w (y₀ : ℂ) T u) ∧ (fwdMap w T y₀).re = y := by
  have hH := (isRealFlow_fwd hw hw0 hT).2
  set g : ℝ → ℝ := fun z => -(fwdMap w T ((-z : ℝ) : ℂ)).re with hg
  have hqA' : ∃ u, IsForwardSol w (((-(-q)) : ℝ) : ℂ) T u := by rwa [neg_neg]
  obtain ⟨N, hN⟩ := hH.2.2.2.2.2.2 (-y + 1)
  set z : ℝ := max N (-q) + 1 with hz
  have hqz : -q < z := by have := le_max_right N (-q); linarith
  have hzA : ∃ u, IsForwardSol w (((-z) : ℝ) : ℂ) T u := hH.2.1 (-q) z (by linarith) hqz hqA'
  have hgz : -y + 1 ≤ g z := hN z (by have := le_max_left N (-q); linarith) hzA
  have hA : ∀ x ∈ Icc (-q) z, ∃ u, IsForwardSol w (((-x) : ℝ) : ℂ) T u := fun x hx => by
    rcases hx.1.lt_or_eq with h | h
    · exact hH.2.1 (-q) x (by linarith) h hqA'
    · rw [← h]; exact hqA'
  have hcont : ContinuousOn g (Icc (-q) z) := by
    intro x hx
    rw [Metric.continuousWithinAt_iff]
    intro ε hε
    obtain ⟨η, hη, hf⟩ := hH.2.2.2.2.2.1 x (by linarith [hx.1]) (hA x hx) ε hε
    refine ⟨η, hη, fun x' hx' hd => ?_⟩
    rw [Real.dist_eq] at hd ⊢
    exact hf x' (hA x' hx') hd
  have hgq : g (-q) < -y := by
    change -(fwdMap w T ((-(-q) : ℝ) : ℂ)).re < -y
    rw [neg_neg]
    linarith
  obtain ⟨x₀, hx₀, he⟩ := intermediate_value_Icc hqz.le hcont ⟨hgq.le, by linarith⟩
  have hx₀q : -q < x₀ := by
    rcases hx₀.1.lt_or_eq with h | h
    · exact h
    · rw [← h] at he; linarith
  refine ⟨-x₀, by linarith, hA x₀ hx₀, ?_⟩
  change -(fwdMap w T ((-x₀ : ℝ) : ℂ)).re = -y at he
  linarith

end Flow

/-! ### The left marks of a stop word are jumps -/

/-- **Every left mark position of a stop word is a jump of it.** -/
theorem markPosL_mem_jumps_stopWord {κ : ℝ} (c : BoundaryWord) (θ : ℝ) (r : RecData) {i : ℕ}
    (hi : i < flowLineNL c.fn c.jumps 0) :
    markPosL (rdrv r) (rtime r) ((padFL 0 0 c.fn c.jumps).1.1 i) ∈ (stopWord κ (c, θ, r)).jumps := by
  have hmo := isMarkOrder_stopWord c r
  refine BoundaryWord.mem_jumps.2 ⟨flowLineNL c.fn c.jumps 0 - 1 - i, by
    change _ < flowLineNL c.fn c.jumps 0 + 1 + flowLineNR c.fn c.jumps 0; omega, ?_⟩
  change cumMax (rawPos _ _ _) _ = _
  rw [cumMax_rawPos hmo (by omega)]
  unfold rawPos
  rw [ite_eq_left_of_eq_true _ _ (eq_true (by omega))]
  beta_reduce
  rw [show flowLineNL c.fn c.jumps 0 - 1 - (flowLineNL c.fn c.jumps 0 - 1 - i) = i by omega]

/-- The left mark starts of a flow-line word are `≤ 0`. -/
theorem padFL_fst_fst_nonpos (c : BoundaryWord) {i : ℕ} (hi : i < flowLineNL c.fn c.jumps 0) :
    (padFL 0 0 c.fn c.jumps).1.1 i ≤ 0 := by
  have h := padFL_fst_fst_fin c.fn c.jumps ⟨i, hi⟩
  simp only at h
  rw [h]
  exact GW3Word.flowLineXL_nonpos _ _ _

/-! ### The low side through a launch -/

/-- **The low left side of a state** (SB2(1)'s active word, the part of `(m, 0)` right of the untouched left ray): at
every chart point `y < 0` off the jumps of the word `β` that lies right of the chart image of the whole untouched left
ray `(−∞, recL)`, the word is low, `β ≤ −λ − θχ`. -/
def LLow (κ θ : ℝ) (β : BoundaryWord) (s : ExplState) : Prop :=
  ∀ y, y < 0 → y ∉ β.jumps → (∀ x, x < stRecL s → rProf (stChart s) x < y) →
    β.fn y ≤ -sleLambda κ - θ * chiC κ

/-- The chart of a state is continuous at every real point of the untouched left ray. -/
def LCont (s : ExplState) : Prop :=
  ∀ x : ℝ, x < stRecL s → ContinuousAt (stChart s).1 (x : ℂ)

/-- **The inverse image of a value of the inward profile** (intermediate values on the untouched left ray): a value
`v` at most the profile at some point of the ray is the profile at a point of the ray. -/
theorem LLeft.exists_eq {s : ExplState} (hs : LLeft s) {x v : ℝ} (hx : x < stRecL s)
    (hv : v ≤ rProf (stChart s) x) : ∃ x', x' < stRecL s ∧ x' ≤ x ∧ rProf (stChart s) x' = v := by
  rcases hv.lt_or_eq with hlt | heq
  · have hlt' : lProf (stChart s) (-x) < -v := by rw [lProf_eq, neg_neg]; linarith
    obtain ⟨z, hz, hzv⟩ := (exists_eq_iff_exists_lt hs.1).2 ⟨-x, by linarith, hlt'⟩
    refine ⟨-z, by linarith, ?_, by rw [lProf_eq] at hzv; linarith⟩
    by_contra hzx
    push Not at hzx
    have := hs.strictMonoOn (show x ∈ Iio (stRecL s) from hx) (show -z ∈ Iio (stRecL s) by
      change -z < stRecL s; linarith) hzx
    rw [lProf_eq] at hzv
    linarith
  · exact ⟨x, hx, le_rfl, heq.symm⟩

/-- **The low left side survives a launch** (SB2(1), p. 632, "the active lower-flow sides before the next seed have
height `−λ − φχ`"): after a launch of an angle-`θ` piece with a good record at a finite stop, right of the image of the
new untouched left ray the stop word is low. A point right of every new left mark has the new left-side height
(`stopWord_fn_first`); a point left of a mark is (after a small move to the right) the image of an alive old point
`y₀ < 0` with the old height (`stopWord_fn_fwdMap_neg`), and `y₀` lies right of the image of the old untouched ray
(points of the old ray left of the new record map left of `y`, the others are dead), so the old low side applies. -/
theorem lLow_launch {κ θ : ℝ} (hκ : 0 < κ) {β : BoundaryWord} {s : ExplState} (hc : IsRealChart (stChart s))
    (hs : LLeft s) (hL : LLow κ θ β s) (k : ℕ) {D : (ℝ≥0 → ℝ) × ℝ≥0∞} (hreg : IsRegularDriver D)
    (hgood : LocalExt.IsDrvGood (recHist (recOf ⊤ D))) (hfin : D.2 ≠ ⊤) :
    LLow κ θ (stopWord κ (β, θ, recOf ⊤ D)) (ExplState.launch s k D θ ⊤) := by
  obtain ⟨-, -, hrel⟩ := lLeft_launch hc hs k θ hreg hgood hfin
  set r := recOf ⊤ D with hr
  set W := rdrv r with hWdef
  set T := rtime r with hTdef
  have hW : Continuous W := continuous_rdrv r
  have hW0 : W 0 = 0 := rdrv_zero r
  have hT : 0 ≤ T := rtime_nonneg r
  have hHn := (isRealFlow_fwd hW hW0 hT).2
  set c := stChart s with hcdef
  set s₁ := ExplState.launch s k D θ ⊤ with hs₁
  set γ := stopWord κ (β, θ, r) with hγ
  set f : ℝ → ℝ := fun z => (fwdMap W T (z : ℂ)).re with hf
  set A : ℝ → Prop := fun z => ∃ u, IsForwardSol W (z : ℂ) T u with hAdef
  -- alive negative points form a down-set, and the flow is strictly increasing on them
  have hdown : ∀ z z', z < z' → z' < 0 → A z' → A z := fun z z' hzz' hz' hA' => by
    have h1 : ∃ u, IsForwardSol W (((-(-z')) : ℝ) : ℂ) T u := by rwa [neg_neg]
    have h2 : A (-(-z)) := hHn.2.1 (-z') (-z) (by linarith) (by linarith) h1
    rwa [neg_neg] at h2
  have hmono : ∀ z z', z < z' → z' < 0 → A z → A z' → f z < f z' := fun z z' hzz' hz' hA hA' => by
    have h1 : ∃ u, IsForwardSol W (((-(-z')) : ℝ) : ℂ) T u := by rwa [neg_neg]
    have h2 : ∃ u, IsForwardSol W (((-(-z)) : ℝ) : ℂ) T u := by rwa [neg_neg]
    have h : -f (-(-z')) < -f (-(-z)) := hHn.2.2.2.2.1 (-z') (-z) (by linarith) (by linarith) h1 h2
    simp only [neg_neg] at h
    linarith
  intro y hy hyJ hyR
  by_cases hfirst : ∀ i < flowLineNL β.fn β.jumps 0,
      markPosL (rdrv r) (rtime r) ((padFL 0 0 β.fn β.jumps).1.1 i) < y
  · exact (stopWord_fn_first β θ r hy hyJ hfirst).le
  push Not at hfirst
  obtain ⟨i, hi, hiy⟩ := hfirst
  have hiy' : y < markPosL W T ((padFL 0 0 β.fn β.jumps).1.1 i) :=
    lt_of_le_of_ne hiy fun h => hyJ (h ▸ markPosL_mem_jumps_stopWord (κ := κ) β θ r hi)
  have hp0 := padFL_fst_fst_nonpos β hi
  obtain ⟨q, hqx, hqA, hqy⟩ := exists_rat_lt_of_lt_markPosL hW hW0 hT hiy'
  have hq0 : (q : ℝ) < 0 := lt_of_lt_of_le hqx hp0
  obtain ⟨y₀, hy₀q, hy₀A, hfy₀⟩ := exists_alive_eq_of_lt_re hW hW0 hT hq0 hqA hqy
  replace hfy₀ : f y₀ = y := hfy₀
  -- continuity of the real flow at `y₀`
  have hfc : ContinuousAt f y₀ := by
    obtain ⟨u, hu⟩ := hy₀A
    have h1 := ZhanGT4.A1G3L2.continuousAt_fwdMap_of_isForwardSol (show T < T + 1 by linarith) hT
      hW.continuousOn hu
    exact Complex.continuous_re.continuousAt.comp (h1.comp Complex.continuous_ofReal.continuousAt)
  -- a point slightly right of `y₀` avoiding finitely many values
  set v₁ := rProf c (stRecL s₁) with hv₁
  have hFin : ((insert v₁ β.jumps : Finset ℝ) : Set ℝ).Finite := Finset.finite_toSet _
  have hγev : ∀ᶠ z in 𝓝 y₀, f z ∉ γ.jumps ∧ γ.fn (f z) = γ.fn y := by
    have h1 := hfc.eventually ((γ.jumps.finite_toSet.isClosed.isOpen_compl).mem_nhds (by rw [hfy₀]; exact hyJ))
    have h2 := hfc.eventually (by rw [hfy₀]; exact γ.isPiecewiseConstantBoundaryData y hyJ)
    filter_upwards [h1, h2] with z h1 h2 using ⟨h1, h2⟩
  have hev : ∀ᶠ z : ℝ in 𝓝[>] y₀, (z < (q : ℝ) ∧ f z ∉ γ.jumps ∧ γ.fn (f z) = γ.fn y) ∧
      z ∉ ((insert v₁ β.jumps : Finset ℝ) : Set ℝ) := by
    refine Eventually.and ?_ ((eventually_notMem_of_finite hFin y₀).filter_mono
      (nhdsWithin_mono _ fun z hz => ne_of_gt hz))
    have h3 : ∀ᶠ z : ℝ in 𝓝 y₀, z < (q : ℝ) := gt_mem_nhds hy₀q
    filter_upwards [(h3.and hγev).filter_mono nhdsWithin_le_nhds] with z hz using ⟨hz.1, hz.2⟩
  obtain ⟨y₁, ⟨⟨hy₁q, hfy₁J, hfy₁⟩, hy₁F⟩, hy₀₁⟩ := (hev.and self_mem_nhdsWithin).exists
  have hy₀₁ : y₀ < y₁ := hy₀₁
  have hy₁0 : y₁ < 0 := hy₁q.trans hq0
  have hy₁A : A y₁ := hdown y₁ (q : ℝ) hy₁q hq0 hqA
  have hy₁J : y₁ ∉ β.jumps := fun h => hy₁F (by simp [h])
  have hy₁v : y₁ ≠ v₁ := fun h => hy₁F (by simp [h])
  -- the stop word at the image of `y₁` is the old word at `y₁`
  have hγβ : γ.fn (f y₁) = β.fn y₁ := stopWord_fn_fwdMap_neg hκ β θ r hy₁0 hy₁A hy₁J hfy₁J
  -- `y₁` lies right of the image of the old untouched ray
  have hright : ∀ x, x < stRecL s → rProf c x < y₁ := by
    intro x hx
    by_contra hle
    push Not at hle
    obtain ⟨x', hx', -, hx'v⟩ := hs.exists_eq hx hle
    rcases lt_trichotomy x' (stRecL s₁) with hlt | heq | hgt
    · obtain ⟨-, -, hrx⟩ := hrel x' hlt
      have h1 := hyR x' hlt
      rw [hrx, hx'v] at h1
      have h2 := hmono y₀ y₁ hy₀₁ hy₁0 hy₀A hy₁A
      change f y₁ < y at h1
      rw [← hfy₀] at h1
      linarith
    · exact hy₁v (by rw [← hx'v, heq])
    · -- a dead point of the old ray left of `x'`
      have hWe : W = stopDrv ⊤ D := by rw [hWdef, hr, rdrv_recOf]; exact recDrv_eq_stopDrv hreg hgood
      have hH' := (isRealFlow_stop hreg hgood).2
      obtain ⟨-, -, -, hrecL, -, -⟩ := launch_eq_of_ne_top s k D θ ⊤ (min_top_ne_top hfin)
      have hR1 : -stRecL s₁ = newRec (lProf c) (-stRecL s)
          (fun y : ℝ => ∃ u, IsForwardSol (stopDrv ⊤ D) ((-y : ℝ) : ℂ) (stopTime ⊤ D) u) := by
        rw [hs₁, hrecL, lRecL_eq_newRec hc, neg_neg]
      have hlt : -x' < newRec (lProf c) (-stRecL s)
          (fun y : ℝ => ∃ u, IsForwardSol (stopDrv ⊤ D) ((-y : ℝ) : ℂ) (stopTime ⊤ D) u) := by
        rw [← hR1]; linarith
      obtain ⟨z, hz, hxz⟩ := (lt_csSup_iff (bddAbove_dead hs.1 hH') (insert_nonempty _ _)).1 hlt
      rcases hz with rfl | ⟨hza, hzd⟩
      · linarith
      · apply hzd
        have hzx : -z < x' := by linarith
        have hz' : -z < stRecL s := by linarith
        have hlt2 : rProf c (-z) < y₁ := by
          rw [← hx'v]
          exact hs.strictMonoOn (show -z ∈ Iio (stRecL s) from hz') (show x' ∈ Iio (stRecL s) from hx') hzx
        have hA2 := hdown (rProf c (-z)) y₁ hlt2 hy₁0 hy₁A
        rw [lProf_eq, neg_neg]
        change ∃ u, IsForwardSol W ((rProf c (-z) : ℝ) : ℂ) T u at hA2
        rw [hWe] at hA2
        exact hA2
  calc γ.fn y = γ.fn (f y₁) := hfy₁.symm
    _ = β.fn y₁ := hγβ
    _ ≤ -sleLambda κ - θ * chiC κ := hL y₁ hy₁0 hy₁J hright

/-! ### Continuity on the untouched left ray, the record, and the real points of the pieces -/

section Launch

variable {s : ExplState} {D : (ℝ≥0 → ℝ) × ℝ≥0∞}

/-- **The left record does not increase at a launch.** -/
theorem stRecL_launch_le (hc : IsRealChart (stChart s)) (hs : LLeft s) (k : ℕ) (θ : ℝ) (hreg : IsRegularDriver D)
    (hgood : LocalExt.IsDrvGood (recHist (recOf ⊤ D))) (hfin : D.2 ≠ ⊤) :
    stRecL (ExplState.launch s k D θ ⊤) ≤ stRecL s :=
  le_of_forall_lt fun x hx => ((lLeft_launch hc hs k θ hreg hgood hfin).2.2 x hx).1

/-- **The chart stays continuous on the new untouched left ray**: the new chart is the Loewner map of the stop composed
with the old one, continuous at the (alive) images of the ray (`continuousAt_fwdMap_of_isForwardSol`). -/
theorem lCont_launch (hc : IsRealChart (stChart s)) (hs : LLeft s) (hC : LCont s) (k : ℕ) (θ : ℝ)
    (hreg : IsRegularDriver D) (hgood : LocalExt.IsDrvGood (recHist (recOf ⊤ D))) (hfin : D.2 ≠ ⊤) :
    LCont (ExplState.launch s k D θ ⊤) := by
  obtain ⟨-, -, hrel⟩ := lLeft_launch hc hs k θ hreg hgood hfin
  obtain ⟨hch, -⟩ := launch_eq_of_ne_top s k D θ ⊤ (min_top_ne_top hfin)
  have hWe : rdrv (recOf ⊤ D) = stopDrv ⊤ D := by rw [rdrv_recOf]; exact recDrv_eq_stopDrv hreg hgood
  have hWc : Continuous (stopDrv ⊤ D) := by rw [← hWe]; exact continuous_rdrv _
  have hT := stopTime_nonneg ⊤ D
  intro x hx
  obtain ⟨hxL, ⟨u, hu⟩, -⟩ := hrel x hx
  rw [hWe, rtime_recOf, ← hc.eq_ofReal x] at hu
  have h1 := ZhanGT4.A1G3L2.continuousAt_fwdMap_of_isForwardSol
    (show stopTime ⊤ D < stopTime ⊤ D + 1 by linarith) hT hWc.continuousOn hu
  rw [hch]
  exact h1.comp (hC x hxL)

/-- **Every real point of a recorded piece lies at or right of the left record.** -/
def PiecesRealBound (s : ExplState) : Prop :=
  ∀ p ∈ s.1, ∀ z ∈ p.1.tipSet p.2.1 p.2.2, z.im = 0 → stRecL s ≤ z.re

/-- **The real points of the pieces stay right of the left record through a launch.** A real point `x` of the new
piece left of the new record would be a point of the untouched ray at which the chart is continuous and alive at the
stop; the conformal chart then sends it to the piece's trace point at some time `t ≤` the stop, which is not alive at
`t` (`not_isForwardSol_of_tip`). -/
theorem piecesRealBound_launch (hcc : (stChart s).IsConformal) (hc : IsRealChart (stChart s)) (hs : LLeft s)
    (hC : LCont s) (hB : PiecesRealBound s) (k : ℕ) (θ : ℝ) (hreg : IsRegularDriver D)
    (hgood : LocalExt.IsDrvGood (recHist (recOf ⊤ D))) (hfin : D.2 ≠ ⊤) (hP : GW1P.PieceRegular D.1 D.2) :
    PiecesRealBound (ExplState.launch s k D θ ⊤) := by
  obtain ⟨-, -, hrel⟩ := lLeft_launch hc hs k θ hreg hgood hfin
  have hle := stRecL_launch_le hc hs k θ hreg hgood hfin
  intro p hp z hz hz0
  rw [CounterflowRange.pieces_launch] at hp
  rcases List.mem_append.1 hp with hp | hp
  · exact hle.trans (hB p hp z hz hz0)
  rw [List.mem_singleton] at hp
  subst hp
  by_contra hlt
  push Not at hlt
  set c := stChart s with hcdef
  obtain ⟨hxL, ⟨u, hu⟩, -⟩ := hrel z.re hlt
  have hWe : rdrv (recOf ⊤ D) = stopDrv ⊤ D := by rw [rdrv_recOf]; exact recDrv_eq_stopDrv hreg hgood
  have hWc : Continuous (stopDrv ⊤ D) := by rw [← hWe]; exact continuous_rdrv _
  have hW0 : stopDrv ⊤ D 0 = 0 := stopDrv_zero hreg ⊤
  have hzx : z = ((z.re : ℝ) : ℂ) := Complex.ext (by simp) (by simp [hz0])
  rw [hWe, rtime_recOf, ← hc.eq_ofReal, ← hzx] at hu
  obtain ⟨t, ht, htz⟩ := hz
  have htS : (t : ℝ≥0∞) ≤ D.2 := by simpa only [min_eq_right (le_top : D.2 ≤ ⊤)] using ht
  -- the radial limit of the stage's inverse is the chart image of `z`
  have hV : (fun r : ℝ => (fun r : ℝ≥0 => D.1 (min (r : ℝ≥0∞) (min ⊤ D.2)).toNNReal) r.toNNReal) =
      stopDrv ⊤ D := rfl
  rw [hV] at htz
  have hrad : Tendsto (fun y : ℝ => (y : ℂ) * Complex.I) (𝓝[>] 0) (𝓝[H] 0) := by
    refine tendsto_nhdsWithin_iff.2 ⟨?_, eventually_nhdsWithin_of_forall fun y hy => ?_⟩
    · have hcm : Continuous fun y : ℝ => (y : ℂ) * Complex.I :=
        Complex.continuous_ofReal.mul continuous_const
      have h := hcm.tendsto 0
      simp only [Complex.ofReal_zero, zero_mul] at h
      exact h.mono_left nhdsWithin_le_nhds
    · show 0 < ((y : ℂ) * Complex.I).im
      simpa using hy
  have hmemH : ∀ᶠ y : ℝ in 𝓝[>] (0 : ℝ), fwdMapInv (stopDrv ⊤ D) t ((y : ℂ) * Complex.I) ∈ H :=
    (hrad.eventually (self_mem_nhdsWithin : H ∈ 𝓝[H] (0 : ℂ))).mono fun y hy =>
      (QuantumZipper.RS.fwdMapInv_mem_compl_fwdHull hWc hW0 t.coe_nonneg hy).1
  have h1 : Tendsto (fun y : ℝ => fwdMapInv (stopDrv ⊤ D) t ((y : ℂ) * Complex.I)) (𝓝[>] 0) (𝓝 (c.1 z)) := by
    have hCz : ContinuousAt c.1 z := by have := hC z.re hxL; rwa [← hzx] at this
    have h := hCz.tendsto.comp htz
    refine h.congr' (hmemH.mono fun y hy => ?_)
    exact hcc.2.2 _ hy
  -- the trace of the piece
  obtain ⟨hD0, hDc, α, hα, -⟩ := hP
  let w : ℝ≥0 → ℝ := fun r => D.1 (min (r : ℝ≥0∞) D.2).toNNReal
  have hw : Continuous w := CounterflowRange.continuous_stopped hDc
  have hw0 : w 0 = 0 := by simpa only [w, ENNReal.coe_zero, zero_min, ENNReal.toNNReal_zero] using hD0
  have htip : Tendsto (fwdMapInv (stopDrv ⊤ D) t) (𝓝[H] 0) (𝓝 (α t)) := by
    simpa only [stopDrv_def, min_eq_right (le_top : D.2 ≤ ⊤)] using
      GW1WalkExit.tendsto_inverse_trace_le (CounterflowRange.isGeneratingTrace_stopped hα) hw hw0 htS
  have heq : α t = c.1 z := tendsto_nhds_unique (htip.comp hrad) h1
  rw [heq] at htip
  have htT : (t : ℝ) ≤ stopTime ⊤ D := by
    dsimp only [stopTime]
    rw [min_eq_right (le_top : D.2 ≤ ⊤)]
    have ht' : t ≤ D.2.toNNReal := ENNReal.coe_le_coe.1 (by
      simpa only [ENNReal.coe_toNNReal hfin] using htS)
    exact_mod_cast ht'
  exact Supp8.GB6.not_isForwardSol_of_tip hWc hW0 t.coe_nonneg htip
    (QuantumZipper.isForwardSol_restrict hu t.coe_nonneg htT)

end Launch

end InteractingSLE.Theorem14.GW1W
