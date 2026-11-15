/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW2aConnInv

/-!
# GW2a's connectors: the boundary continuation step (deterministic)

Packet PROVE-GW2A-CONN. Lemma GW2a (supplement p. 623): "At a right threshold for angle `θ`, move outward on the
untouched original boundary through the intervals `H + θχ ≤ −λ`, and restart at the first later original jump with
`H + θχ > −λ`. At a left threshold use the reflected rule `H + θχ ≥ λ`."

* `contStep_arc_cases`: a boundary continuation that records a connector starts from a right start (a right
  threshold, a zero-lifetime threshold whose outward right height is low, or a partial right connector) and is the
  rightward branch of the frozen `ExplState.contStep`, or the mirror on the left;
* `rMove_rBranch`: the rightward branch moves to a point `x > pt` past only low genuine jumps, or to the end past only
  low genuine jumps (`RMove`);
* at a state with the invariant `GInv` and connector readiness `RConn` (the current point is the right record, the
  right profile tends to `0` there, the outward original height is low), the original data are low on the connector
  (`low_b_of_rMove`), the word read in the chart is low (`β − πχ/2 ≤ −λ`) on the chart image `(0, m x)` of the
  connector (`low_word_of_rConn`), and the invariant and readiness survive the move (`gInv_moveAlong_right`,
  `rConn_moveAlong`).
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
open PiecewiseConstantBoundaryData (rightLim leftLim jumpSet)

variable {κ : ℝ} {b : ℝ → ℝ} {jumps : Finset ℝ}

/-! ### Readiness for a connector -/

/-- **Ready for a rightward connector**: the current point is the right record, the right profile tends to `0` at it,
and the outward original height there is low for the state's angle. -/
def RConn (κ : ℝ) (b : ℝ → ℝ) (s : ExplState) : Prop :=
  stPt s = stRecR s ∧ (∀ ε > 0, ∃ x, stRecR s < x ∧ rProf (stChart s) x < ε) ∧
    rightLim b (stPt s) + stAngle s * chiC κ ≤ -sleLambda κ

/-- **Ready for a leftward connector** (the mirror of `RConn`). -/
def LConn (κ : ℝ) (b : ℝ → ℝ) (s : ExplState) : Prop :=
  stPt s = stRecL s ∧ (∀ ε > 0, ∃ x, -stRecL s < x ∧ lProf (stChart s) x < ε) ∧
    sleLambda κ ≤ leftLim b (stPt s) + stAngle s * chiC κ

/-- The statuses from which a rightward connector starts. -/
def RStart (κ : ℝ) (b : ℝ → ℝ) (s : ExplState) : Prop :=
  stStatus s = stThr (some true) ∨
    (stStatus s = stThr none ∧ rightLim b (stPt s) + stAngle s * chiC κ ≤ -sleLambda κ) ∨
    stStatus s = .inr (.inr (.inr (.inl (true, false))))

/-- The statuses from which a leftward connector starts. -/
def LStart (κ : ℝ) (b : ℝ → ℝ) (s : ExplState) : Prop :=
  stStatus s = stThr (some false) ∨
    (stStatus s = stThr none ∧ sleLambda κ ≤ leftLim b (stPt s) + stAngle s * chiC κ) ∨
    stStatus s = .inr (.inr (.inr (.inl (false, false))))

/-! ### The two branches of the boundary continuation -/

/-- The rightward branch of the frozen `ExplState.contStep`. -/
def rBranch (κ : ℝ) (b : ℝ → ℝ) (jumps : Finset ℝ) (s : ExplState) (vStop : Option ℝ) : ExplState :=
  if hC : ((jumpSet b jumps).filter
      (fun x => stPt s < x ∧ -sleLambda κ < rightLim b x + stAngle s * chiC κ)).Nonempty then
    (match vStop with
      | some v => if stPt s < v ∧ v < Finset.min' _ hC then ExplState.moveAlong s true v false
                  else ExplState.moveAlong s true (Finset.min' _ hC) true
      | none => ExplState.moveAlong s true (Finset.min' _ hC) true)
  else
    (match vStop with
      | some v => if stPt s < v then ExplState.moveAlong s true v false else ExplState.moveToEnd s true
      | none => ExplState.moveToEnd s true)

/-- The leftward branch of the frozen `ExplState.contStep`. -/
def lBranch (κ : ℝ) (b : ℝ → ℝ) (jumps : Finset ℝ) (s : ExplState) (vStop : Option ℝ) : ExplState :=
  if hC : ((jumpSet b jumps).filter
      (fun x => x < stPt s ∧ leftLim b x + stAngle s * chiC κ < sleLambda κ)).Nonempty then
    (match vStop with
      | some v => if Finset.max' _ hC < v ∧ v < stPt s then ExplState.moveAlong s false v false
                  else ExplState.moveAlong s false (Finset.max' _ hC) true
      | none => ExplState.moveAlong s false (Finset.max' _ hC) true)
  else
    (match vStop with
      | some v => if v < stPt s then ExplState.moveAlong s false v false else ExplState.moveToEnd s false
      | none => ExplState.moveToEnd s false)

/-- **A boundary continuation that records a connector** is the rightward branch from a right start or the leftward
branch from a left start. -/
theorem contStep_arc_cases (s : ExplState) (vStop : Option ℝ) (pref : Bool)
    (hne : (ExplState.contStep κ b jumps s vStop pref).2.1 ≠ s.2.1) :
    (RStart κ b s ∧ ExplState.contStep κ b jumps s vStop pref = rBranch κ b jumps s vStop) ∨
      (LStart κ b s ∧ ExplState.contStep κ b jumps s vStop pref = lBranch κ b jumps s vStop) := by
  obtain ⟨pieces, arcs, retained, launches, chart, status, pt, θ, recR, recL⟩ := s
  rcases status with ⟨⟨⟩⟩ | ⟨⟨⟩⟩ | o | ⟨r, m⟩ | ⟨⟨⟩⟩ | ⟨⟨⟩⟩
  · exact absurd rfl hne
  · exact absurd rfl hne
  · rcases o with _ | r
    · by_cases hR : rightLim b pt + θ * chiC κ ≤ -sleLambda κ
      · by_cases hL : sleLambda κ ≤ leftLim b pt + θ * chiC κ
        · cases pref
          · right
            refine ⟨Or.inr (Or.inl ⟨rfl, hL⟩), ?_⟩
            simp only [ExplState.contStep, hR, hL, and_self, ↓reduceIte]
            rfl
          · left
            refine ⟨Or.inr (Or.inl ⟨rfl, hR⟩), ?_⟩
            simp only [ExplState.contStep, hR, hL, and_self, ↓reduceIte]
            rfl
        · left
          refine ⟨Or.inr (Or.inl ⟨rfl, hR⟩), ?_⟩
          simp only [ExplState.contStep, hR, hL, and_false, ↓reduceIte]
          rfl
      · by_cases hL : sleLambda κ ≤ leftLim b pt + θ * chiC κ
        · right
          refine ⟨Or.inr (Or.inl ⟨rfl, hL⟩), ?_⟩
          simp only [ExplState.contStep, hR, hL, false_and, ↓reduceIte]
          rfl
        · exfalso
          apply hne
          simp only [ExplState.contStep, hR, hL, and_false, ↓reduceIte]
    · cases r
      · right
        exact ⟨Or.inl rfl, rfl⟩
      · left
        exact ⟨Or.inl rfl, rfl⟩
  · cases m
    · cases r
      · right
        exact ⟨Or.inr (Or.inr rfl), rfl⟩
      · left
        exact ⟨Or.inr (Or.inr rfl), rfl⟩
    · exact absurd rfl hne
  · exact absurd rfl hne
  · exact absurd rfl hne

/-! ### The moves of the two branches -/

/-- **A rightward move**: along the original boundary to a point `x` beyond the current point, past only low genuine
jumps (also at `x` for a partial move), or to the end past only low genuine jumps. -/
def RMove (κ : ℝ) (b : ℝ → ℝ) (jumps : Finset ℝ) (s s' : ExplState) : Prop :=
  (∃ (x : ℝ) (mk : Bool), s' = ExplState.moveAlong s true x mk ∧ stPt s < x ∧
    (∀ z ∈ jumpSet b jumps, stPt s < z → z < x → rightLim b z + stAngle s * chiC κ ≤ -sleLambda κ) ∧
    (mk = false → ∀ z ∈ jumpSet b jumps, stPt s < z → z ≤ x → rightLim b z + stAngle s * chiC κ ≤ -sleLambda κ)) ∨
  (s' = ExplState.moveToEnd s true ∧
    ∀ z ∈ jumpSet b jumps, stPt s < z → rightLim b z + stAngle s * chiC κ ≤ -sleLambda κ)

/-- **A leftward move** (the mirror of `RMove`). -/
def LMove (κ : ℝ) (b : ℝ → ℝ) (jumps : Finset ℝ) (s s' : ExplState) : Prop :=
  (∃ (x : ℝ) (mk : Bool), s' = ExplState.moveAlong s false x mk ∧ x < stPt s ∧
    (∀ z ∈ jumpSet b jumps, x < z → z < stPt s → sleLambda κ ≤ leftLim b z + stAngle s * chiC κ) ∧
    (mk = false → ∀ z ∈ jumpSet b jumps, x ≤ z → z < stPt s → sleLambda κ ≤ leftLim b z + stAngle s * chiC κ)) ∨
  (s' = ExplState.moveToEnd s false ∧
    ∀ z ∈ jumpSet b jumps, z < stPt s → sleLambda κ ≤ leftLim b z + stAngle s * chiC κ)

theorem rMove_rBranch (s : ExplState) (vStop : Option ℝ) : RMove κ b jumps s (rBranch κ b jumps s vStop) := by
  set C := (jumpSet b jumps).filter
    (fun x => stPt s < x ∧ -sleLambda κ < rightLim b x + stAngle s * chiC κ) with hCdef
  have hnot : ∀ z ∈ jumpSet b jumps, stPt s < z → z ∉ C → rightLim b z + stAngle s * chiC κ ≤ -sleLambda κ := by
    intro z hz hpz hzC
    by_contra h
    exact hzC (Finset.mem_filter.2 ⟨hz, hpz, not_le.1 h⟩)
  unfold rBranch
  by_cases hC : C.Nonempty
  · have hmin := Finset.mem_filter.1 (C.min'_mem hC)
    have hlt : ∀ z ∈ jumpSet b jumps, stPt s < z → z < C.min' hC →
        rightLim b z + stAngle s * chiC κ ≤ -sleLambda κ := fun z hz hpz hzm =>
      hnot z hz hpz fun hzC => absurd (C.min'_le z hzC) (not_le.2 hzm)
    rw [dite_eq_left_of_eq_true (eq_true hC)]
    cases vStop with
    | none => exact Or.inl ⟨_, true, rfl, hmin.2.1, hlt, fun h => absurd h (by simp)⟩
    | some v =>
      simp only
      by_cases hv : stPt s < v ∧ v < C.min' hC
      · rw [ite_eq_left_of_eq_true _ _ (eq_true hv)]
        exact Or.inl ⟨v, false, rfl, hv.1, fun z hz hpz hzv => hlt z hz hpz (hzv.trans hv.2),
          fun _ z hz hpz hzv => hlt z hz hpz (hzv.trans_lt hv.2)⟩
      · rw [ite_eq_right_of_eq_false _ _ (eq_false hv)]
        exact Or.inl ⟨_, true, rfl, hmin.2.1, hlt, fun h => absurd h (by simp)⟩
  · have hall : ∀ z ∈ jumpSet b jumps, stPt s < z → rightLim b z + stAngle s * chiC κ ≤ -sleLambda κ :=
      fun z hz hpz => hnot z hz hpz fun hzC => hC ⟨z, hzC⟩
    rw [dite_eq_right_of_eq_false (eq_false hC)]
    cases vStop with
    | none => exact Or.inr ⟨rfl, hall⟩
    | some v =>
      simp only
      by_cases hv : stPt s < v
      · rw [ite_eq_left_of_eq_true _ _ (eq_true hv)]
        exact Or.inl ⟨v, false, rfl, hv, fun z hz hpz _ => hall z hz hpz, fun _ z hz hpz _ => hall z hz hpz⟩
      · rw [ite_eq_right_of_eq_false _ _ (eq_false hv)]
        exact Or.inr ⟨rfl, hall⟩

theorem lMove_lBranch (s : ExplState) (vStop : Option ℝ) : LMove κ b jumps s (lBranch κ b jumps s vStop) := by
  set C := (jumpSet b jumps).filter
    (fun x => x < stPt s ∧ leftLim b x + stAngle s * chiC κ < sleLambda κ) with hCdef
  have hnot : ∀ z ∈ jumpSet b jumps, z < stPt s → z ∉ C → sleLambda κ ≤ leftLim b z + stAngle s * chiC κ := by
    intro z hz hpz hzC
    by_contra h
    exact hzC (Finset.mem_filter.2 ⟨hz, hpz, not_le.1 h⟩)
  unfold lBranch
  by_cases hC : C.Nonempty
  · have hmax := Finset.mem_filter.1 (C.max'_mem hC)
    have hgt : ∀ z ∈ jumpSet b jumps, C.max' hC < z → z < stPt s →
        sleLambda κ ≤ leftLim b z + stAngle s * chiC κ := fun z hz hzm hpz =>
      hnot z hz hpz fun hzC => absurd (C.le_max' z hzC) (not_le.2 hzm)
    rw [dite_eq_left_of_eq_true (eq_true hC)]
    cases vStop with
    | none => exact Or.inl ⟨_, true, rfl, hmax.2.1, hgt, fun h => absurd h (by simp)⟩
    | some v =>
      simp only
      by_cases hv : C.max' hC < v ∧ v < stPt s
      · rw [ite_eq_left_of_eq_true _ _ (eq_true hv)]
        exact Or.inl ⟨v, false, rfl, hv.2, fun z hz hvz hpz => hgt z hz (hv.1.trans hvz) hpz,
          fun _ z hz hvz hpz => hgt z hz (hv.1.trans_le hvz) hpz⟩
      · rw [ite_eq_right_of_eq_false _ _ (eq_false hv)]
        exact Or.inl ⟨_, true, rfl, hmax.2.1, hgt, fun h => absurd h (by simp)⟩
  · have hall : ∀ z ∈ jumpSet b jumps, z < stPt s → sleLambda κ ≤ leftLim b z + stAngle s * chiC κ :=
      fun z hz hpz => hnot z hz hpz fun hzC => hC ⟨z, hzC⟩
    rw [dite_eq_right_of_eq_false (eq_false hC)]
    cases vStop with
    | none => exact Or.inr ⟨rfl, hall⟩
    | some v =>
      simp only
      by_cases hv : v < stPt s
      · rw [ite_eq_left_of_eq_true _ _ (eq_true hv)]
        exact Or.inl ⟨v, false, rfl, hv, fun z hz _ hpz => hall z hz hpz, fun _ z hz _ hpz => hall z hz hpz⟩
      · rw [ite_eq_right_of_eq_false _ _ (eq_false hv)]
        exact Or.inr ⟨rfl, hall⟩

/-! ### The original data on a connector -/

/-- **The outward height at a point of a low connector is low** (a partial connector stops at `x` inside the low
region: every genuine jump in `(q, x]` keeps the outward height low). -/
theorem rightLim_low_of_lt (hb : IsPiecewiseConstantBoundaryData b jumps) {q x θ : ℝ}
    (hlow0 : rightLim b q + θ * chiC κ ≤ -sleLambda κ)
    (hjumps : ∀ z ∈ jumpSet b jumps, q < z → z ≤ x → rightLim b z + θ * chiC κ ≤ -sleLambda κ) (hqx : q < x) :
    rightLim b x + θ * chiC κ ≤ -sleLambda κ := by
  classical
  obtain ⟨hi, hhi, hconst⟩ := Sec5.Aux22ChartE.exists_forall_Ioo_eq_rightLim hb x
  set M := jumps.filter (x < ·) with hM
  set w : ℝ := min hi (if hne : M.Nonempty then M.min' hne else x + 1) with hw
  have hxw : x < w := by
    refine lt_min hhi ?_
    split_ifs with hne
    · exact (Finset.mem_filter.1 (M.min'_mem hne)).2
    · linarith
  obtain ⟨t, ⟨hxt, htw⟩, htJ⟩ := (Set.Ioo_infinite hxw).exists_notMem_finset jumps
  have hC : ∀ z ∈ jumpSet b jumps, q < z → z < w → rightLim b z + θ * chiC κ ≤ -sleLambda κ := by
    intro z hz hqz hzw
    by_cases hzx : z ≤ x
    · exact hjumps z hz hqz hzx
    · exfalso
      have hzM : z ∈ M := Finset.mem_filter.2 ⟨(Finset.mem_filter.1 hz).1, not_le.1 hzx⟩
      have hne : M.Nonempty := ⟨z, hzM⟩
      have h1 : w ≤ M.min' hne := by
        rw [hw]
        refine (min_le_right _ _).trans ?_
        rw [dite_eq_left_of_eq_true (eq_true hne)]
      linarith [M.min'_le z hzM]
  have h := add_le_neg_of_connector hb hlow0 hC (hqx.trans hxt) htw htJ
  rwa [hconst t ⟨hxt, htw.trans_le (min_le_left _ _)⟩] at h

/-- The mirror of `rightLim_low_of_lt`. -/
theorem leftLim_high_of_gt (hb : IsPiecewiseConstantBoundaryData b jumps) {q x θ : ℝ}
    (hhigh0 : sleLambda κ ≤ leftLim b q + θ * chiC κ)
    (hjumps : ∀ z ∈ jumpSet b jumps, x ≤ z → z < q → sleLambda κ ≤ leftLim b z + θ * chiC κ) (hxq : x < q) :
    sleLambda κ ≤ leftLim b x + θ * chiC κ := by
  classical
  obtain ⟨lo, hlo, hconst⟩ := Sec5.Aux22ChartE.exists_forall_Ioo_eq_leftLim hb x
  set M := jumps.filter (· < x) with hM
  set w : ℝ := max lo (if hne : M.Nonempty then M.max' hne else x - 1) with hw
  have hwx : w < x := by
    refine max_lt hlo ?_
    split_ifs with hne
    · exact (Finset.mem_filter.1 (M.max'_mem hne)).2
    · linarith
  obtain ⟨t, ⟨hwt, htx⟩, htJ⟩ := (Set.Ioo_infinite hwx).exists_notMem_finset jumps
  have hC : ∀ z ∈ jumpSet b jumps, w < z → z < q → sleLambda κ ≤ leftLim b z + θ * chiC κ := by
    intro z hz hwz hzq
    by_cases hxz : x ≤ z
    · exact hjumps z hz hxz hzq
    · exfalso
      have hzM : z ∈ M := Finset.mem_filter.2 ⟨(Finset.mem_filter.1 hz).1, not_le.1 hxz⟩
      have hne : M.Nonempty := ⟨z, hzM⟩
      have h1 : M.max' hne ≤ w := by
        rw [hw]
        refine le_trans ?_ (le_max_right _ _)
        rw [dite_eq_left_of_eq_true (eq_true hne)]
      linarith [M.le_max' z hzM]
  have h := le_add_of_connector hb hhigh0 hC hwt (htx.trans hxq) htJ
  rwa [hconst t ⟨(le_max_left _ _).trans_lt hwt, htx⟩] at h

/-! ### The word read in the chart on a connector -/

/-- **The word is low on the chart image of a right connector** (GW2a, p. 624: `H + θχ ≤ −λ ⟹ H ≤ −λ − θχ ≤ −Λ`):
at a state with the invariant and connector readiness, if the original data are low on `(pt, x)`, the word read in the
chart satisfies `β − πχ/2 ≤ −λ` on `(0, m x)`, `m` the right profile. -/
theorem low_word_of_rConn (hκ : 0 < κ) (hκ4 : κ < 4) {β : BoundaryWord} {s : ExplState} (hI : GInv b jumps β s)
    (hR : RConn κ b s) (hθ : -(Real.pi / 2) ≤ stAngle s) {x : ℝ} (hx : stRecR s < x)
    (hlowb : ∀ y, stPt s < y → y < x → y ∉ jumps → b y + stAngle s * chiC κ ≤ -sleLambda κ) :
    ∀ z, 0 < z → z < rProf (stChart s) x → z ∉ β.jumps →
      β.fn z - Real.pi / 2 * chiC κ ≤ -sleLambda κ := by
  intro z hz0 hzx hzJ
  obtain ⟨-, ⟨hm, -⟩, -, hO, -, -⟩ := hI
  obtain ⟨hpt, hsmall, -⟩ := hR
  obtain ⟨y, hy, hmy⟩ := (exists_eq_iff_exists_lt hm).2 (hsmall z hz0)
  have hyx : y < x := by
    by_contra h
    push Not at h
    rcases h.lt_or_eq with h | h
    · have := hm.1 hx hy h
      linarith
    · rw [← h] at hmy
      linarith
  have hcy : ContinuousAt (rProf (stChart s)) y := hm.2.1.continuousAt (Ioi_mem_nhds hy)
  have hP : ∀ᶠ y' in 𝓝 y, y' < x ∧ β.fn (rProf (stChart s) y') = β.fn z := by
    have h1 := hcy.eventually (by rw [hmy]; exact β.isPiecewiseConstantBoundaryData z hzJ)
    filter_upwards [gt_mem_nhds hyx, h1] with y' h2 h3
    exact ⟨h2, h3⟩
  obtain ⟨y', hy'R, hy'J, hmy'J, hy'x, hfn⟩ := exists_near_avoid hm.1 hy jumps β.jumps hP
  rw [← hfn, hO y' hy'R hy'J hmy'J]
  have hlow := hlowb y' (by rw [hpt]; exact hy'R) hy'x hy'J
  have hχ := Sec4.chiC_pos hκ hκ4
  nlinarith

/-- **The word is high on the chart image of a left connector** (the mirror of `low_word_of_rConn`): `β + πχ/2 ≥ λ`
on `(m x, 0)`. -/
theorem high_word_of_lConn (hκ : 0 < κ) (hκ4 : κ < 4) {β : BoundaryWord} {s : ExplState} (hI : GInv b jumps β s)
    (hL : LConn κ b s) (hθ : stAngle s ≤ Real.pi / 2) {x : ℝ} (hx : x < stRecL s)
    (hhighb : ∀ y, x < y → y < stPt s → y ∉ jumps → sleLambda κ ≤ b y + stAngle s * chiC κ) :
    ∀ z, rProf (stChart s) x < z → z < 0 → z ∉ β.jumps →
      sleLambda κ ≤ β.fn z + Real.pi / 2 * chiC κ := by
  intro z hzx hz0 hzJ
  obtain ⟨-, -, ⟨hl, hlpos⟩, -, hO, -⟩ := hI
  obtain ⟨hpt, hsmall, -⟩ := hL
  obtain ⟨u, hu, hmu⟩ := (exists_eq_iff_exists_lt hl).2 (hsmall (-z) (by linarith))
  set y := -u with hydef
  have hyL : y < stRecL s := by rw [hydef]; linarith
  have hmy : rProf (stChart s) y = z := by
    rw [hydef]
    rw [lProf_eq] at hmu
    linarith
  have hmono := strictMonoOn_of_lProf hl.1
  have hxy : x < y := by
    by_contra h
    push Not at h
    rcases h.lt_or_eq with h | h
    · have := hmono hyL hx h
      linarith
    · rw [h] at hmy
      linarith
  have hcy : ContinuousAt (rProf (stChart s)) y :=
    (continuousOn_rProf_of_lProf hl.2.1).continuousAt (Iio_mem_nhds hyL)
  have hP : ∀ᶠ y' in 𝓝 y, x < y' ∧ β.fn (rProf (stChart s) y') = β.fn z := by
    have h1 := hcy.eventually (by rw [hmy]; exact β.isPiecewiseConstantBoundaryData z hzJ)
    filter_upwards [lt_mem_nhds hxy, h1] with y' h2 h3
    exact ⟨h2, h3⟩
  obtain ⟨y', hy'L, hy'J, hmy'J, hxy', hfn⟩ := exists_near_avoid_left hmono hyL jumps β.jumps hP
  rw [← hfn, hO y' hy'L hy'J hmy'J]
  have hhigh := hhighb y' hxy' (by rw [hpt]; exact hy'L) hy'J
  have hχ := Sec4.chiC_pos hκ hκ4
  nlinarith

/-! ### The invariant through a move -/

theorem stRecL_moveAlong_true (s : ExplState) (w : ℝ) (m : Bool) :
    stRecL (ExplState.moveAlong s true w m) = stRecL s := by
  obtain ⟨pieces, arcs, ret, lau, chart, st, pt, ang, rR, rL⟩ := s
  rfl

theorem stAngle_moveAlong (s : ExplState) (r : Bool) (w : ℝ) (m : Bool) :
    stAngle (ExplState.moveAlong s r w m) = stAngle s := by
  obtain ⟨pieces, arcs, ret, lau, chart, st, pt, ang, rR, rL⟩ := s
  rfl

theorem stStatus_moveAlong (s : ExplState) (r : Bool) (w : ℝ) (m : Bool) :
    stStatus (ExplState.moveAlong s r w m) = .inr (.inr (.inr (.inl (r, m)))) := by
  obtain ⟨pieces, arcs, ret, lau, chart, st, pt, ang, rR, rL⟩ := s
  rfl

theorem rProf_moveAlong (s : ExplState) (r : Bool) (w : ℝ) (m : Bool) (y : ℝ) :
    rProf (stChart (ExplState.moveAlong s r w m)) y = rProf (stChart s) y - rProf (stChart s) w := by
  rw [stChart_moveAlong, rProf_recenter]
  rfl

theorem lProf_moveAlong (s : ExplState) (r : Bool) (w : ℝ) (m : Bool) (u : ℝ) :
    lProf (stChart (ExplState.moveAlong s r w m)) u = lProf (stChart s) u + rProf (stChart s) w := by
  rw [lProf_eq, rProf_moveAlong, lProf_eq]
  ring

theorem notMem_jumps_of_shiftW {β : BoundaryWord} {a z : ℝ} (hz : z - a ∉ (BoundaryWord.shiftW a β).jumps) :
    z ∉ β.jumps := fun h => hz (by rw [BoundaryWord.jumps_shiftW]; exact Finset.mem_image_of_mem _ h)

/-- **The invariant after a move along the original boundary** to a point outside the explored records (the chart
is recentred there; a connector has no field reveal). -/
theorem gInv_moveAlong {β : BoundaryWord} {s : ExplState} (hI : GInv b jumps β s) (r : Bool) {x : ℝ}
    (hx : stRecR s < x ∨ x < stRecL s) (hrx : r = true → stRecR s < x) (hlx : r = false → x < stRecL s) (mk : Bool) :
    GInv b jumps (BoundaryWord.shiftW (rProf (stChart s) x) β) (ExplState.moveAlong s r x mk) := by
  obtain ⟨hc, ⟨hm, hpos⟩, ⟨hl, hlpos⟩, hO, hOL, hread⟩ := hI
  set a := rProf (stChart s) x with ha
  have hR' : stRecR (ExplState.moveAlong s r x mk) = if r then max (stRecR s) x else stRecR s := by
    obtain ⟨pieces, arcs, ret, lau, chart, st, pt, ang, rR, rL⟩ := s
    cases r <;> rfl
  have hL' : stRecL (ExplState.moveAlong s r x mk) = if r then stRecL s else min (stRecL s) x := by
    obtain ⟨pieces, arcs, ret, lau, chart, st, pt, ang, rR, rL⟩ := s
    cases r <;> rfl
  have hRle : stRecR s ≤ stRecR (ExplState.moveAlong s r x mk) := by
    rw [hR']; split_ifs <;> simp
  have hLle : stRecL (ExplState.moveAlong s r x mk) ≤ stRecL s := by
    rw [hL']; split_ifs <;> simp
  -- the sign of `a`
  have hRa : ∀ y, stRecR (ExplState.moveAlong s r x mk) < y → a < rProf (stChart s) y := by
    intro y hy
    cases r
    · have hxL := hlx rfl
      have hya : stRecR s < y := by rw [hR'] at hy; simpa using hy
      have h1 : rProf (stChart s) x < 0 := rProf_neg_of_lProf hlpos hxL
      linarith [hpos y hya]
    · have hxR := hrx rfl
      have hy' : x < y := by rw [hR'] at hy; exact (le_max_right _ _).trans_lt (by simpa using hy)
      exact hm.1 hxR (hxR.trans hy') hy'
  have hLa : ∀ u, -stRecL (ExplState.moveAlong s r x mk) < u → 0 < lProf (stChart s) u + a := by
    intro u hu
    cases r
    · have hxL := hlx rfl
      have hu' : -x < u := by
        rw [hL'] at hu
        simp only [Bool.false_eq_true, ↓reduceIte] at hu
        linarith [min_le_right (stRecL s) x]
      have h1 := strictMonoOn_of_lProf hl.1 (show -u ∈ Iio (stRecL s) by simp only [Set.mem_Iio]; linarith)
        hxL (show -u < x by linarith)
      rw [lProf_eq]
      linarith
    · have hxR := hrx rfl
      have hu' : -stRecL s < u := by rw [hL'] at hu; simpa using hu
      linarith [hlpos u hu', hpos x hxR]
  refine ⟨fun y => ?_, ⟨?_, fun y hy => ?_⟩, ⟨?_, fun u hu => ?_⟩, fun y hy hyJ hzJ => ?_,
    fun y hy hyJ hzJ => ?_, fun y hy => ?_⟩
  · rw [stChart_moveAlong]
    change ((stChart s).1 y - ((((stChart s).1 x).re : ℝ) : ℂ)).im = 0
    rw [Complex.sub_im, hc y, Complex.ofReal_im, sub_zero]
  · have e : rProf (stChart (ExplState.moveAlong s r x mk)) = fun y => rProf (stChart s) y - a :=
      funext fun y => rProf_moveAlong s r x mk y
    rw [e]
    exact (hm.mono_of_le hRle).sub_const a
  · rw [rProf_moveAlong]
    linarith [hRa y hy]
  · have e : lProf (stChart (ExplState.moveAlong s r x mk)) = fun u => lProf (stChart s) u - (-a) :=
      funext fun u => by rw [lProf_moveAlong]; ring
    rw [e]
    exact (hl.mono_of_le (by linarith)).sub_const (-a)
  · rw [lProf_moveAlong]
    exact hLa u hu
  · rw [rProf_moveAlong] at hzJ ⊢
    rw [BoundaryWord.fn_shiftW, sub_add_cancel]
    exact hO y (hRle.trans_lt hy) hyJ (notMem_jumps_of_shiftW hzJ)
  · rw [rProf_moveAlong] at hzJ ⊢
    rw [BoundaryWord.fn_shiftW, sub_add_cancel]
    exact hOL y (hy.trans_le hLle) hyJ (notMem_jumps_of_shiftW hzJ)
  · rw [stChart_moveAlong]
    rcases hy with hy | hy
    · exact chartReadsAt_recenter (hread y (Or.inl (hRle.trans_lt hy))) _
    · exact chartReadsAt_recenter (hread y (Or.inr (hy.trans_le hLle))) _

/-- **Readiness survives a partial right move** inside the low region. -/
theorem rConn_moveAlong {β : BoundaryWord} {s : ExplState} (hI : GInv b jumps β s) (hR : RConn κ b s) {x : ℝ}
    (hpx : stPt s < x) (hlowx : rightLim b x + stAngle s * chiC κ ≤ -sleLambda κ) (mk : Bool) :
    RConn κ b (ExplState.moveAlong s true x mk) := by
  obtain ⟨-, ⟨hm, -⟩, -, -, -, -⟩ := hI
  obtain ⟨hpt, -, -⟩ := hR
  have hxR : stRecR s < x := by rw [← hpt]; exact hpx
  have hR' : stRecR (ExplState.moveAlong s true x mk) = x := by
    rw [stRecR_moveAlong_true, max_eq_right hxR.le]
  refine ⟨by rw [stPt_moveAlong, hR'], fun ε hε => ?_, by rw [stPt_moveAlong, stAngle_moveAlong]; exact hlowx⟩
  have hcx : ContinuousAt (rProf (stChart s)) x := hm.2.1.continuousAt (Ioi_mem_nhds hxR)
  have hev : ∀ᶠ y in 𝓝 x, |rProf (stChart s) y - rProf (stChart s) x| < ε := by
    have := hcx.eventually (Metric.ball_mem_nhds (rProf (stChart s) x) hε)
    filter_upwards [this] with y hy
    rw [Real.dist_eq] at hy
    exact hy
  obtain ⟨y, hy1, hy2⟩ := ((hev.filter_mono nhdsWithin_le_nhds).and
    (self_mem_nhdsWithin : Ioi x ∈ 𝓝[>] x)).exists
  refine ⟨y, by rw [hR']; exact hy2, ?_⟩
  rw [rProf_moveAlong]
  exact lt_of_le_of_lt (le_abs_self _) hy1

/-- **Readiness survives a partial left move** inside the high region (the mirror of `rConn_moveAlong`). -/
theorem lConn_moveAlong {β : BoundaryWord} {s : ExplState} (hI : GInv b jumps β s) (hL : LConn κ b s) {x : ℝ}
    (hxp : x < stPt s) (hhighx : sleLambda κ ≤ leftLim b x + stAngle s * chiC κ) (mk : Bool) :
    LConn κ b (ExplState.moveAlong s false x mk) := by
  obtain ⟨-, -, ⟨hl, -⟩, -, -, -⟩ := hI
  obtain ⟨hpt, -, -⟩ := hL
  have hxL : x < stRecL s := by rw [← hpt]; exact hxp
  have hL' : stRecL (ExplState.moveAlong s false x mk) = x := by
    rw [stRecL_moveAlong_false, min_eq_right hxL.le]
  refine ⟨by rw [stPt_moveAlong, hL'], fun ε hε => ?_, by rw [stPt_moveAlong, stAngle_moveAlong]; exact hhighx⟩
  have hcx : ContinuousAt (lProf (stChart s)) (-x) := hl.2.1.continuousAt (Ioi_mem_nhds (by linarith))
  have hev : ∀ᶠ u in 𝓝 (-x), |lProf (stChart s) u - lProf (stChart s) (-x)| < ε := by
    have := hcx.eventually (Metric.ball_mem_nhds (lProf (stChart s) (-x)) hε)
    filter_upwards [this] with u hu
    rw [Real.dist_eq] at hu
    exact hu
  obtain ⟨u, hu1, hu2⟩ := ((hev.filter_mono nhdsWithin_le_nhds).and
    (self_mem_nhdsWithin : Ioi (-x) ∈ 𝓝[>] (-x))).exists
  refine ⟨u, by rw [hL']; exact hu2, ?_⟩
  rw [lProf_moveAlong]
  have e : lProf (stChart s) (-x) = -rProf (stChart s) x := by rw [lProf_eq, neg_neg]
  rw [e] at hu1
  linarith [le_abs_self (lProf (stChart s) u - -rProf (stChart s) x)]

end GW2aConn

end Theorem14

end InteractingSLE
