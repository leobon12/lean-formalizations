/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.SB4RTrWalk0

/-!
# The restart relation after the forced arc

Packet PROVE-T14-SB4LEAF (ruling R104, the initial-arc version). Two runs of the lower-walk program `prog` on the same
data `B`, from the roots `x₁ < x₂`, whose first pieces have zero lifetime, both follow the boundary from their root to
the first genuine admissible jump `x*` right of `x₂` when no genuine jump in `(x₁, x₂]` is admissible
(`walkFilter_eq`): then they are in `RestartRel` after two instructions (**`restartRel_two`**); if there is no such
jump both have followed the boundary to `∞` (**`done_two`**).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Complex Set Filter Topology
open scoped NNReal ENNReal
open QuantumZipper (chiC H Hbar IsForwardSol fwdMap fwdMapInv)

namespace InteractingSLE.Theorem14.SB.Lf

open Exist.Staged Exist.StagedLaw
open PiecewiseConstantBoundaryData (rightLim leftLim jumpSet)

theorem moveAlong_components (s : ExplState) (r : Bool) (x : ℝ) (am : Bool) :
    (ExplState.moveAlong s r x am).1 = s.1 ∧
      (ExplState.moveAlong s r x am).2.1 = s.2.1 ++ [if r then Icc (stPt s) x else Icc x (stPt s)] ∧
      (ExplState.moveAlong s r x am).2.2.1 = s.2.2.1 ∧ (ExplState.moveAlong s r x am).2.2.2.1 = s.2.2.2.1 ∧
      stChart (ExplState.moveAlong s r x am) = (stChart s).recenter ((stChart s).1 x).re ∧
      stStatus (ExplState.moveAlong s r x am) = .inr (.inr (.inr (.inl (r, am)))) ∧
      stPt (ExplState.moveAlong s r x am) = x ∧ stAngle (ExplState.moveAlong s r x am) = stAngle s ∧
      stRecR (ExplState.moveAlong s r x am) = (if r then max (stRecR s) x else stRecR s) := by
  obtain ⟨_, _, _, _, _, _, _, _, _, _⟩ := s
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

section Two

variable {κ : ℝ} {B : ℝ → ℝ} {JB : Finset ℝ}

/-- The admissible genuine jumps right of a point. -/
def walkFilter (κ : ℝ) (B : ℝ → ℝ) (JB : Finset ℝ) (x : ℝ) : Finset ℝ :=
  (jumpSet B JB).filter (fun y => x < y ∧ -sleLambda κ < rightLim B y + -(Real.pi / 2) * chiC κ)

theorem walkFilter_eq {x₁ x₂ : ℝ} (h12 : x₁ ≤ x₂)
    (hmid : ∀ y ∈ jumpSet B JB, x₁ < y → y ≤ x₂ → ¬ -sleLambda κ < rightLim B y + -(Real.pi / 2) * chiC κ) :
    walkFilter κ B JB x₁ = walkFilter κ B JB x₂ := by
  unfold walkFilter
  refine Finset.filter_congr fun y hy => ⟨fun ⟨h1, h2⟩ => ⟨?_, h2⟩, fun ⟨h1, h2⟩ => ⟨by linarith, h2⟩⟩
  by_contra hle
  exact hmid y hy h1 (not_lt.1 hle) h2

/-- The state after the zero-lifetime first launch of a walk from `x₀`. -/
theorem launch_init_zero_components (x₀ : ℝ) {d : (ℝ≥0 → ℝ) × ℝ≥0∞} (hreg : IsRegularDriver d) (h0 : d.2 = 0) :
    (ExplState.launch (ExplState.init x₀) 0 d (-(Real.pi / 2)) ⊤).1 =
        [(Chart.id.recenter x₀, (fun _ => (0 : ℝ)), (0 : ℝ≥0∞))] ∧
      (ExplState.launch (ExplState.init x₀) 0 d (-(Real.pi / 2)) ⊤).2.1 = [] ∧
      (ExplState.launch (ExplState.init x₀) 0 d (-(Real.pi / 2)) ⊤).2.2.1 =
        Function.update (fun _ : ℕ => ((fun _ : ℝ≥0 => (0 : ℝ)), (0 : ℝ≥0∞), false)) 0
          ((fun _ : ℝ≥0 => (0 : ℝ)), (0 : ℝ≥0∞), true) ∧
      (ExplState.launch (ExplState.init x₀) 0 d (-(Real.pi / 2)) ⊤).2.2.2.1 =
        Function.update (fun _ : ℕ => (none : Option (Chart × ℝ))) 0
          (some (Chart.id.recenter x₀, -(Real.pi / 2))) := by
  obtain ⟨c1, c2, c3, c4⟩ := launch_components (ExplState.init x₀) 0 d (-(Real.pi / 2)) ⊤
  have hW : (fun r : ℝ≥0 => d.1 (min (r : ℝ≥0∞) (min ⊤ d.2)).toNNReal) = fun _ => 0 := by
    funext r
    have e : min (r : ℝ≥0∞) (min ⊤ (0 : ℝ≥0∞)) = 0 := by simp
    rw [h0, e, ENNReal.toNNReal_zero]
    exact hreg.2.1
  have hs : min ⊤ d.2 = 0 := by rw [h0]; simp
  refine ⟨?_, c2, ?_, c4⟩
  · rw [c1, hW, hs]; rfl
  · rw [c3, hW, hs, h0]; rfl

/-- The chart after the arc: the zero-lifetime chart from `x₀` recentred at `x*`. -/
theorem chartEqH_arc (x₁ x₂ x : ℝ) :
    ChartEqH (((Chart.id.recenter x₁).loewner (fun _ => 0) 0).recenter
        ((((Chart.id.recenter x₁).loewner (fun _ => 0) 0).1 x).re))
      (((Chart.id.recenter x₂).loewner (fun _ => 0) 0).recenter
        ((((Chart.id.recenter x₂).loewner (fun _ => 0) 0).1 x).re)) := by
  have hf := GW2aCont.fwdMap_zero_driver_zero (W := fun _ : ℝ => (0 : ℝ)) rfl
  refine ⟨?_, ?_, fun w hw => ?_⟩
  · funext z
    show fwdMap (fun _ => 0) 0 (z - x₁) - ((fwdMap (fun _ => 0) 0 ((x : ℂ) - x₁)).re : ℂ) =
      fwdMap (fun _ => 0) 0 (z - x₂) - ((fwdMap (fun _ => 0) 0 ((x : ℂ) - x₂)).re : ℂ)
    rw [hf]
    simp only [id, Complex.sub_re, Complex.ofReal_re]
    push_cast
    ring
  · show ((Chart.id.recenter x₁).loewner (fun _ => 0) 0).2.2 = ((Chart.id.recenter x₂).loewner (fun _ => 0) 0).2.2
    rw [GW2aCont.loewner_zero_lift, GW2aCont.loewner_zero_lift]
    rfl
  · have hmem : ∀ a : ℝ, w + (a : ℂ) ∈ H := fun a => by
      show 0 < (w + (a : ℂ)).im
      rw [Complex.add_im, Complex.ofReal_im, add_zero]; exact hw
    show ((Chart.id.recenter x₁).loewner (fun _ => 0) 0).2.1
        (w + ((((Chart.id.recenter x₁).loewner (fun _ => 0) 0).1 x).re : ℂ)) =
      ((Chart.id.recenter x₂).loewner (fun _ => 0) 0).2.1
        (w + ((((Chart.id.recenter x₂).loewner (fun _ => 0) 0).1 x).re : ℂ))
    rw [GW2aCont.loewner_zero_inv continuous_const rfl (hmem _),
      GW2aCont.loewner_zero_inv continuous_const rfl (hmem _),
      GW2aCont.loewner_zero_fwd rfl, GW2aCont.loewner_zero_fwd rfl]
    show w + (((x : ℂ) - x₁).re : ℂ) + x₁ = w + (((x : ℂ) - x₂).re : ℂ) + x₂
    simp only [Complex.sub_re, Complex.ofReal_re]
    push_cast
    ring

theorem contDirNone_true_of_low (s : ExplState)
    (hlow : rightLim B (stPt s) + stAngle s * chiC κ ≤ -sleLambda κ) : contDirNone κ B true s = some true := by
  unfold contDirNone
  split_ifs <;> rfl

variable (prog : List Instr) (h0 : prog[0]? = some (.inl (-(Real.pi / 2), ⊤))) (h1 : prog[1]? = some (.inr (.inl true)))
  {D D' : ℕ → (ℝ≥0 → ℝ) × ℝ≥0∞}

include h0 h1 in
theorem run_two_eq_contBranch (x₀ : ℝ) {d : (ℝ≥0 → ℝ) × ℝ≥0∞} (hD : D 0 = d) (hreg : IsRegularDriver d)
    (hz : d.2 = 0) (hlow : rightLim B x₀ - Real.pi / 2 * chiC κ ≤ -sleLambda κ) :
    ExplState.run κ B JB (x₀, false, prog) D 2 =
      contBranch κ B JB (ExplState.launch (ExplState.init x₀) 0 d (-(Real.pi / 2)) ⊤) none true := by
  rw [run_two_walk x₀ prog h0 h1 D, hD, contStep_eq_byStatus]
  obtain ⟨hst, hpt, hang, -, -⟩ := launch_init_zero x₀ hreg hz (-(Real.pi / 2))
  rw [hst]
  show (match contDirNone κ B true _ with
    | none => _ | some true => _ | some false => _) = _
  rw [contDirNone_true_of_low _ (by rw [hpt, hang]; linarith)]

include h0 h1 in
/-- **The restart relation after the forced arc.** -/
theorem restartRel_two {x₁ x₂ : ℝ} (h12 : x₁ ≤ x₂) {d d' : (ℝ≥0 → ℝ) × ℝ≥0∞} (hD : D 0 = d) (hD' : D' 0 = d')
    (hreg : IsRegularDriver d) (hreg' : IsRegularDriver d') (hz : d.2 = 0) (hz' : d'.2 = 0)
    (hlow₁ : rightLim B x₁ - Real.pi / 2 * chiC κ ≤ -sleLambda κ)
    (hlow₂ : rightLim B x₂ - Real.pi / 2 * chiC κ ≤ -sleLambda κ)
    (hmid : ∀ y ∈ jumpSet B JB, x₁ < y → y ≤ x₂ → ¬ -sleLambda κ < rightLim B y + -(Real.pi / 2) * chiC κ)
    (hC : (walkFilter κ B JB x₂).Nonempty) :
    RestartRel (ExplState.run κ B JB (x₁, false, prog) D 2) (ExplState.run κ B JB (x₂, false, prog) D' 2) := by
  rw [run_two_eq_contBranch prog h0 h1 x₁ hD hreg hz hlow₁, run_two_eq_contBranch prog h0 h1 x₂ hD' hreg' hz' hlow₂]
  obtain ⟨hst₁, hpt₁, hang₁, hrec₁, hc₁⟩ := launch_init_zero x₁ hreg hz (-(Real.pi / 2))
  obtain ⟨hst₂, hpt₂, hang₂, hrec₂, hc₂⟩ := launch_init_zero x₂ hreg' hz' (-(Real.pi / 2))
  obtain ⟨p1, a1, r1, l1⟩ := launch_init_zero_components x₁ hreg hz
  obtain ⟨p2, a2, r2, l2⟩ := launch_init_zero_components x₂ hreg' hz'
  have hF := walkFilter_eq (κ := κ) (B := B) (JB := JB) h12 hmid
  have hC₁ : (walkFilter κ B JB x₁).Nonempty := hF ▸ hC
  set x := (walkFilter κ B JB x₂).min' hC with hx
  have hxpos : x₂ < x := (Finset.mem_filter.1 (Finset.min'_mem _ hC)).2.1
  have hx₁ : (walkFilter κ B JB x₁).min' hC₁ = x := by simp only [hx, hF]
  set s₁ := ExplState.launch (ExplState.init x₁) 0 d (-(Real.pi / 2)) ⊤
  set s₂ := ExplState.launch (ExplState.init x₂) 0 d' (-(Real.pi / 2)) ⊤
  have e₁ : contBranch κ B JB s₁ none true = ExplState.moveAlong s₁ true x true := by
    unfold contBranch
    have : (jumpSet B JB).filter (fun y => stPt s₁ < y ∧
        -sleLambda κ < rightLim B y + stAngle s₁ * chiC κ) = walkFilter κ B JB x₁ := by
      rw [hpt₁, hang₁]; rfl
    simp only [↓reduceIte, this, hC₁, ↓reduceDIte, hx₁]
  have e₂ : contBranch κ B JB s₂ none true = ExplState.moveAlong s₂ true x true := by
    unfold contBranch
    have : (jumpSet B JB).filter (fun y => stPt s₂ < y ∧
        -sleLambda κ < rightLim B y + stAngle s₂ * chiC κ) = walkFilter κ B JB x₂ := by
      rw [hpt₂, hang₂]; rfl
    simp only [↓reduceIte, this, hC, ↓reduceDIte]
    rfl
  rw [e₁, e₂]
  obtain ⟨m1, m2, m3, m4, m5, m6, m7, m8, m9⟩ := moveAlong_components s₁ true x true
  obtain ⟨n1, n2, n3, n4, n5, n6, n7, n8, n9⟩ := moveAlong_components s₂ true x true
  refine ⟨⟨_, _, [], [], by rw [m1, p1], by rw [n1, p2], List.Forall₂.nil⟩,
    ⟨Icc x₁ x, Icc x₂ x, [], by rw [m2, a1, hpt₁]; rfl, by rw [n2, a2, hpt₂]; rfl⟩,
    by rw [m3, n3, r1, r2], fun k hk => ?_, ?_, by rw [m6, n6], by rw [m7, n7], by rw [m8, n8, hang₁, hang₂], ?_⟩
  · rw [m4, n4, l1, l2, Function.update_of_ne hk, Function.update_of_ne hk]
    trivial
  · rw [m5, n5, hc₁, hc₂]
    exact chartEqH_arc x₁ x₂ x
  · rw [m9, n9, hrec₁, hrec₂]
    simp only [↓reduceIte]
    rw [max_eq_right (by linarith), max_eq_right hxpos.le]

include h0 h1 in
/-- **No admissible jump after the arc**: the walk follows the boundary to `∞`. -/
theorem run_two_done (x₀ : ℝ) {d : (ℝ≥0 → ℝ) × ℝ≥0∞} (hD : D 0 = d) (hreg : IsRegularDriver d) (hz : d.2 = 0)
    (hlow : rightLim B x₀ - Real.pi / 2 * chiC κ ≤ -sleLambda κ) (hC : ¬ (walkFilter κ B JB x₀).Nonempty) :
    ExplState.run κ B JB (x₀, false, prog) D 2 =
      ExplState.moveToEnd (ExplState.launch (ExplState.init x₀) 0 d (-(Real.pi / 2)) ⊤) true := by
  rw [run_two_eq_contBranch prog h0 h1 x₀ hD hreg hz hlow]
  obtain ⟨-, hpt, hang, -, -⟩ := launch_init_zero x₀ hreg hz (-(Real.pi / 2))
  unfold contBranch
  have : (jumpSet B JB).filter (fun y => stPt (ExplState.launch (ExplState.init x₀) 0 d (-(Real.pi / 2)) ⊤) < y ∧
      -sleLambda κ < rightLim B y + stAngle (ExplState.launch (ExplState.init x₀) 0 d (-(Real.pi / 2)) ⊤) *
        chiC κ) = walkFilter κ B JB x₀ := by
    rw [hpt, hang]; rfl
  simp only [↓reduceIte, this, hC, ↓reduceDIte]

include h0 h1 in
/-- **The arc ends at the first admissible jump**: the walk moves along the boundary to it. -/
theorem run_two_moveAlong (x₀ : ℝ) {d : (ℝ≥0 → ℝ) × ℝ≥0∞} (hD : D 0 = d) (hreg : IsRegularDriver d) (hz : d.2 = 0)
    (hlow : rightLim B x₀ - Real.pi / 2 * chiC κ ≤ -sleLambda κ) (hC : (walkFilter κ B JB x₀).Nonempty) :
    ExplState.run κ B JB (x₀, false, prog) D 2 =
      ExplState.moveAlong (ExplState.launch (ExplState.init x₀) 0 d (-(Real.pi / 2)) ⊤) true
        ((walkFilter κ B JB x₀).min' hC) true := by
  rw [run_two_eq_contBranch prog h0 h1 x₀ hD hreg hz hlow]
  obtain ⟨-, hpt, hang, -, -⟩ := launch_init_zero x₀ hreg hz (-(Real.pi / 2))
  unfold contBranch
  have : (jumpSet B JB).filter (fun y => stPt (ExplState.launch (ExplState.init x₀) 0 d (-(Real.pi / 2)) ⊤) < y ∧
      -sleLambda κ < rightLim B y + stAngle (ExplState.launch (ExplState.init x₀) 0 d (-(Real.pi / 2)) ⊤) *
        chiC κ) = walkFilter κ B JB x₀ := by
    rw [hpt, hang]; rfl
  simp only [↓reduceIte, this, hC, ↓reduceDIte]

end Two

/-! ### Propagation -/

theorem flowStep_done {κ : ℝ} {b : ℝ → ℝ} {gw2 : Bool} {s : ExplState} (hs : stStatus s = stDone) (k : ℕ)
    (d : (ℝ≥0 → ℝ) × ℝ≥0∞) (θ : ℝ) (t : ℝ≥0∞) : ExplState.flowStep κ b gw2 s k d θ t = s := by
  rw [flowStep_eq_cases, hs]
  simp [stTip, stDone, stDead]

theorem contStep_done {κ : ℝ} {b : ℝ → ℝ} {J : Finset ℝ} {s : ExplState} (hs : stStatus s = stDone)
    (vStop : Option ℝ) (pref : Bool) : ExplState.contStep κ b J s vStop pref = s := by
  rw [contStep_eq_byStatus, hs]
  rfl

/-- **A finished run stays put.** -/
theorem run_eq_of_done {κ : ℝ} {b : ℝ → ℝ} {J : Finset ℝ} (spec : ExplSpec) (D : ℕ → (ℝ≥0 → ℝ) × ℝ≥0∞) {n : ℕ}
    (hn : stStatus (ExplState.run κ b J spec D n) = stDone) :
    ∀ k, n ≤ k → ExplState.run κ b J spec D k = ExplState.run κ b J spec D n := by
  intro k hk
  induction k, hk using Nat.le_induction with
  | base => rfl
  | succ k _ ih =>
    rw [run_succ, ih]
    rcases spec.2.2[k]? with _ | i
    · rfl
    · rcases i with ⟨θ, t⟩ | pref | ⟨w, pref⟩
      · exact flowStep_done hn k _ θ t
      · exact contStep_done hn none pref
      · exact contStep_done hn (some w) pref

/-- **The restart relation propagates** along two runs of the same program with the same drivers from instruction
`n` on, as long as every launch of the first run is good and ends on the right. -/
theorem restartRel_run {κ : ℝ} {B : ℝ → ℝ} {JB : Finset ℝ} {spec₁ spec₂ : ExplSpec}
    (hprog : spec₁.2.2 = spec₂.2.2) (hgw : spec₁.2.1 = spec₂.2.1) {D D' : ℕ → (ℝ≥0 → ℝ) × ℝ≥0∞}
    (hreg : ∀ j, IsRegularDriver (D j)) {n : ℕ} (hDD : ∀ j, n ≤ j → D' j = D j)
    (hbase : RestartRel (ExplState.run κ B JB spec₁ D n) (ExplState.run κ B JB spec₂ D' n))
    (hstep : ∀ j, n ≤ j → ∀ θ t, spec₁.2.2[j]? = some (.inl (θ, t)) →
      ExplState.flowStep κ B spec₁.2.1 (ExplState.run κ B JB spec₁ D j) j (D j) θ t =
        ExplState.launch (ExplState.run κ B JB spec₁ D j) j (D j) θ t →
      (min t (D j).2 ≠ ⊤ → LocalExt.IsDrvGood (recHist (recOf t (D j)))) ∧
        RightExit (ExplState.run κ B JB spec₁ D j) t (D j)) :
    ∀ k, n ≤ k → RestartRel (ExplState.run κ B JB spec₁ D k) (ExplState.run κ B JB spec₂ D' k) := by
  intro k hk
  induction k, hk using Nat.le_induction with
  | base => exact hbase
  | succ k hnk ih =>
    rw [run_succ, run_succ, ← hprog, ← hgw]
    rcases hi : spec₁.2.2[k]? with _ | i
    · exact ih
    · rcases i with ⟨θ, t⟩ | pref | ⟨w, pref⟩
      · show RestartRel (ExplState.flowStep κ B spec₁.2.1 _ k (D k) θ t)
          (ExplState.flowStep κ B spec₁.2.1 _ k (D' k) θ t)
        rw [hDD k hnk]
        exact ih.flowStep spec₁.2.1 k θ t (hreg k) (hstep k hnk θ t hi)
      · exact ih.contStep κ B JB none pref
      · exact ih.contStep κ B JB (some w) pref

end InteractingSLE.Theorem14.SB.Lf
