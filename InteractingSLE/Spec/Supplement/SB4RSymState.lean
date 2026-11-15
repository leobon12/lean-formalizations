/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.SB4RMirrorLeaf
import InteractingSLE.Spec.Exist.StagedLaw2Launch

/-!
# The reflection symmetry of exploration states

Packet PROVE-T14-SB4LEAF (ruling R104). The exploration machine of Theorem 1.4 (`ExplState.run`) commutes with the
reflection `ρ(z) = −z̄` through the imaginary axis: the data `b ↦ y ↦ −b(−y)` (`Sec7.FlowReflect.reflData`), the
programs `θ ↦ −θ`, `pref ↦ !pref`, `v ↦ −v` (`reflInstr`, `reflSpec`), the drivers `W ↦ −W`
(`Sec7.StripWall.negDrv`), and the states (`reflState`: charts `c ↦ ρ ∘ c ∘ ρ`, connectors `a ↦ −a`, records
`recR ↦ −recL`, `recL ↦ −recR`, the side of a threshold or connector exchanged).

The one asymmetry of the frozen machine is the order of its threshold tests: a launch whose stopped piece swallows real
points on both sides at its final time is classified as a right threshold. A reflected launch agrees exactly with the
reflection of the launch when no such two-sided hit occurs (`TieFree`); otherwise both are thresholds and agree in
everything but their status side and current point.

* `reflInstr`, `reflSpec`, `reflStatus`, `reflState` and their component lemmas, `explState_ext`;
* `reflState_init`, `moveAlong_reflState`, `moveToEnd_reflState`;
* the launch observables: `lAlive_reflChart`, `lHit_reflChart`, `lRecR_reflState`, `lRecL_reflState`,
  `lStatus_reflState`, `lPt_reflState`, and `TieFree`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Complex Set Filter Topology
open scoped NNReal ENNReal Pointwise
open QuantumZipper (chiC H Hbar)

namespace InteractingSLE.Theorem14.SB.Lf

open Supp9B Exist.Staged Exist.StagedLaw
open Sec7.StripWall (negDrv)

/-! ### Reflected programs, statuses and states -/

/-- The reflected instruction: angles and connector targets negated, connector preferences exchanged. -/
def reflInstr : Instr → Instr
  | .inl (θ, t) => .inl (-θ, t)
  | .inr (.inl pref) => .inr (.inl (!pref))
  | .inr (.inr (v, pref)) => .inr (.inr (-v, !pref))

theorem reflInstr_reflInstr (i : Instr) : reflInstr (reflInstr i) = i := by
  rcases i with ⟨θ, t⟩ | pref | ⟨v, pref⟩ <;> simp [reflInstr]

/-- The reflected program specification: the root negated, every instruction reflected. -/
def reflSpec (spec : ExplSpec) : ExplSpec := (-spec.1, spec.2.1, spec.2.2.map reflInstr)

theorem reflSpec_reflSpec (spec : ExplSpec) : reflSpec (reflSpec spec) = spec := by
  obtain ⟨x, g, p⟩ := spec
  simp only [reflSpec, neg_neg, List.map_map]
  congr
  conv_rhs => rw [← List.map_id p]
  exact List.map_congr_left fun i _ => reflInstr_reflInstr i

/-- The reflected status: the side of a threshold or of a connector exchanged. -/
def reflStatus : ExplStatus → ExplStatus
  | .inr (.inr (.inl (some r))) => .inr (.inr (.inl (some (!r))))
  | .inr (.inr (.inr (.inl (r, m)))) => .inr (.inr (.inr (.inl (!r, m))))
  | st => st

theorem reflStatus_reflStatus (st : ExplStatus) : reflStatus (reflStatus st) = st := by
  rcases st with ⟨⟨⟩⟩ | ⟨⟨⟩⟩ | o | ⟨r, m⟩ | ⟨⟨⟩⟩ | ⟨⟨⟩⟩
  all_goals try rfl
  · rcases o with _ | r
    · rfl
    · simp [reflStatus]
  · simp [reflStatus]

/-- The reflected piece: chart reflected, driver negated. -/
def reflPiece (p : Chart × (ℝ≥0 → ℝ) × ℝ≥0∞) : Chart × (ℝ≥0 → ℝ) × ℝ≥0∞ := (reflChart p.1, -p.2.1, p.2.2)

/-- The reflected retained datum: driver negated. -/
def reflRet (r : (ℝ≥0 → ℝ) × ℝ≥0∞ × Bool) : (ℝ≥0 → ℝ) × ℝ≥0∞ × Bool := (-r.1, r.2.1, r.2.2)

/-- The reflected launch record: chart reflected, angle negated. -/
def reflLaunch (o : Option (Chart × ℝ)) : Option (Chart × ℝ) := o.map fun q => (reflChart q.1, -q.2)

/-- **The reflected state.** -/
def reflState : ExplState → ExplState
  | (pieces, arcs, retained, launches, chart, status, pt, angle, recR, recL) =>
    (pieces.map reflPiece, arcs.map fun a => -a, fun k => reflRet (retained k), fun k => reflLaunch (launches k),
      reflChart chart, reflStatus status, -pt, -angle, -recL, -recR)

section Components

variable (s : ExplState)

theorem reflState_pieces : (reflState s).1 = s.1.map reflPiece := by
  obtain ⟨_, _, _, _, _, _, _, _, _, _⟩ := s; rfl

theorem reflState_arcs : (reflState s).2.1 = s.2.1.map fun a => -a := by
  obtain ⟨_, _, _, _, _, _, _, _, _, _⟩ := s; rfl

theorem reflState_retained : (reflState s).2.2.1 = fun k => reflRet (s.2.2.1 k) := by
  obtain ⟨_, _, _, _, _, _, _, _, _, _⟩ := s; rfl

theorem reflState_launches : (reflState s).2.2.2.1 = fun k => reflLaunch (s.2.2.2.1 k) := by
  obtain ⟨_, _, _, _, _, _, _, _, _, _⟩ := s; rfl

theorem stChart_reflState : stChart (reflState s) = reflChart (stChart s) := by
  obtain ⟨_, _, _, _, _, _, _, _, _, _⟩ := s; rfl

theorem stStatus_reflState : stStatus (reflState s) = reflStatus (stStatus s) := by
  obtain ⟨_, _, _, _, _, _, _, _, _, _⟩ := s; rfl

theorem stPt_reflState : stPt (reflState s) = -stPt s := by
  obtain ⟨_, _, _, _, _, _, _, _, _, _⟩ := s; rfl

theorem stAngle_reflState : stAngle (reflState s) = -stAngle s := by
  obtain ⟨_, _, _, _, _, _, _, _, _, _⟩ := s; rfl

theorem stRecR_reflState : stRecR (reflState s) = -stRecL s := by
  obtain ⟨_, _, _, _, _, _, _, _, _, _⟩ := s; rfl

theorem stRecL_reflState : stRecL (reflState s) = -stRecR s := by
  obtain ⟨_, _, _, _, _, _, _, _, _, _⟩ := s; rfl

end Components

/-- **Extensionality of exploration states.** -/
theorem explState_ext {s s' : ExplState} (h1 : s.1 = s'.1) (h2 : s.2.1 = s'.2.1) (h3 : s.2.2.1 = s'.2.2.1)
    (h4 : s.2.2.2.1 = s'.2.2.2.1) (h5 : stChart s = stChart s') (h6 : stStatus s = stStatus s')
    (h7 : stPt s = stPt s') (h8 : stAngle s = stAngle s') (h9 : stRecR s = stRecR s')
    (h10 : stRecL s = stRecL s') : s = s' := by
  obtain ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9, a10⟩ := s
  obtain ⟨b1, b2, b3, b4, b5, b6, b7, b8, b9, b10⟩ := s'
  simp only at h1 h2 h3 h4 h5 h6 h7 h8 h9 h10
  subst h1 h2 h3 h4 h5 h6 h7 h8 h9 h10
  rfl

/-! ### Charts -/

theorem reflChart_id_recenter (x : ℝ) : reflChart (Chart.id.recenter x) = Chart.id.recenter (-x) := by
  refine Prod.ext (funext fun z => ?_) (Prod.ext (funext fun w => ?_) (funext fun z => ?_))
  · show Supp9B.refl (Supp9B.refl z - (x : ℂ)) = z - ((-x : ℝ) : ℂ)
    simp only [Supp9B.refl, map_sub, map_neg, Complex.conj_conj, Complex.conj_ofReal, Complex.ofReal_neg]
    ring
  · show Supp9B.refl (Supp9B.refl w + (x : ℂ)) = w + ((-x : ℝ) : ℂ)
    simp only [Supp9B.refl, map_add, map_neg, Complex.conj_conj, Complex.conj_ofReal, Complex.ofReal_neg]
    ring
  · show -(0 : ℝ) = 0
    exact neg_zero

/-! ### Initial states and connectors -/

theorem reflState_init (x₀ : ℝ) : reflState (ExplState.init x₀) = ExplState.init (-x₀) := by
  refine explState_ext rfl rfl ?_ rfl (reflChart_id_recenter x₀) rfl rfl ?_ rfl rfl
  · funext k
    show reflRet (fun _ => 0, 0, false) = (fun _ => 0, 0, false)
    simp only [reflRet]
    congr 1
    funext r
    simp
  · show -(0 : ℝ) = 0
    exact neg_zero

theorem neg_Icc_eq (a b : ℝ) : -Icc a b = Icc (-b) (-a) := Set.neg_Icc a b

theorem moveAlong_reflState (s : ExplState) (right : Bool) (x : ℝ) (atMark : Bool) :
    ExplState.moveAlong (reflState s) (!right) (-x) atMark = reflState (ExplState.moveAlong s right x atMark) := by
  obtain ⟨pieces, arcs, retained, launches, chart, status, pt, angle, recR, recL⟩ := s
  have hc : (reflChart chart).1 ((-x : ℝ) : ℂ) = Supp9B.refl (chart.1 (x : ℂ)) := by
    show Supp9B.refl (chart.1 (Supp9B.refl ((-x : ℝ) : ℂ))) = _
    rw [refl_ofReal, neg_neg]
  have hre : ((reflChart chart).1 ((-x : ℝ) : ℂ)).re = -(chart.1 (x : ℂ)).re := by
    rw [hc, refl_re]
  cases right
  · simp only [ExplState.moveAlong, reflState, List.map_append, List.map_cons, List.map_nil, Bool.not_false,
      ↓reduceIte, Bool.false_eq_true, hre, reflChart_recenter, reflStatus, Set.neg_Icc, max_neg_neg]
  · simp only [ExplState.moveAlong, reflState, List.map_append, List.map_cons, List.map_nil, Bool.not_true,
      ↓reduceIte, Bool.false_eq_true, hre, reflChart_recenter, reflStatus, Set.neg_Icc, min_neg_neg]

theorem moveToEnd_reflState (s : ExplState) (right : Bool) :
    ExplState.moveToEnd (reflState s) (!right) = reflState (ExplState.moveToEnd s right) := by
  obtain ⟨pieces, arcs, retained, launches, chart, status, pt, angle, recR, recL⟩ := s
  cases right <;>
  · simp only [ExplState.moveToEnd, reflState, List.map_append, List.map_cons, List.map_nil, Bool.not_false,
      Bool.not_true, ↓reduceIte, Bool.false_eq_true, reflStatus, Set.neg_Ici, Set.neg_Iic]

/-! ### Loewner charts under the reflection -/

/-- **The inverse forward map commutes with the reflection** (at every point, for every driver). -/
theorem fwdMapInv_neg_all (W : ℝ → ℝ) {T : ℝ} (hT : 0 ≤ T) (w : ℂ) :
    QuantumZipper.fwdMapInv (-W) T (Supp9B.refl w) = Supp9B.refl (QuantumZipper.fwdMapInv W T w) := by
  have hiff : ∀ z' : ℂ, (z' ∈ H \ QuantumZipper.fwdHull (-W) T ∧
      QuantumZipper.fwdMap (-W) T z' = Supp9B.refl w) ↔
      (Supp9B.refl z' ∈ H \ QuantumZipper.fwdHull W T ∧ QuantumZipper.fwdMap W T (Supp9B.refl z') = w) := by
    intro z'
    have hm : QuantumZipper.fwdMap (-W) T z' = Supp9B.refl (QuantumZipper.fwdMap W T (Supp9B.refl z')) := by
      have := LP.fwdMap_neg W hT (Supp9B.refl z')
      rwa [← refl_eq_reflectC, refl_refl] at this
    have hK : z' ∈ QuantumZipper.fwdHull (-W) T ↔ Supp9B.refl z' ∈ QuantumZipper.fwdHull W T := by
      rw [LP.fwdHull_neg, ← refl_eq_reflectC]
      constructor
      · rintro ⟨y, hy, rfl⟩; rwa [refl_refl]
      · intro h; exact ⟨_, h, refl_refl z'⟩
    have hH : z' ∈ H ↔ Supp9B.refl z' ∈ H := by
      show 0 < z'.im ↔ 0 < (Supp9B.refl z').im
      rw [refl_im]
    rw [hm, Set.mem_sdiff, Set.mem_sdiff, hH, hK]
    constructor
    · rintro ⟨h1, h2⟩; exact ⟨h1, refl_injective h2⟩
    · rintro ⟨h1, h2⟩; exact ⟨h1, by rw [h2]⟩
  unfold QuantumZipper.fwdMapInv
  by_cases hex : ∃! z', z' ∈ H \ QuantumZipper.fwdHull W T ∧ QuantumZipper.fwdMap W T z' = w
  · have hex' : ∃! z', z' ∈ H \ QuantumZipper.fwdHull (-W) T ∧
        QuantumZipper.fwdMap (-W) T z' = Supp9B.refl w := by
      refine ⟨Supp9B.refl hex.choose, (hiff _).2 (by rw [refl_refl]; exact hex.choose_spec.1), fun y hy => ?_⟩
      have := hex.choose_spec.2 _ ((hiff y).1 hy)
      rw [← this, refl_refl]
    simp only [hex', hex, ↓reduceDIte]
    have h1 := hex'.choose_spec.1
    have h2 := hex.choose_spec.2 _ ((hiff _).1 h1)
    rw [← h2, refl_refl]
  · have hex' : ¬ ∃! z', z' ∈ H \ QuantumZipper.fwdHull (-W) T ∧
        QuantumZipper.fwdMap (-W) T z' = Supp9B.refl w := by
      rintro ⟨y, hy, huniq⟩
      refine hex ⟨Supp9B.refl y, (hiff y).1 hy, fun z hz => ?_⟩
      have := huniq (Supp9B.refl z) ((hiff _).2 (by rw [refl_refl]; exact hz))
      rw [← this, refl_refl]
    simp only [hex', hex, ↓reduceDIte]
    simp [Supp9B.refl]

/-- **A Loewner chart of the reflected chain is the reflected Loewner chart.** -/
theorem reflChart_loewner (c : Chart) (W : ℝ → ℝ) {T : ℝ} (hT : 0 ≤ T) :
    (reflChart c).loewner (-W) T = reflChart (c.loewner W T) := by
  refine Prod.ext (funext fun z => ?_) (Prod.ext (funext fun w => ?_) (funext fun z => ?_))
  · show QuantumZipper.fwdMap (-W) T (Supp9B.refl (c.1 (Supp9B.refl z))) =
      Supp9B.refl (QuantumZipper.fwdMap W T (c.1 (Supp9B.refl z)))
    rw [refl_eq_reflectC]; exact LP.fwdMap_neg W hT _
  · show Supp9B.refl (c.2.1 (Supp9B.refl (QuantumZipper.fwdMapInv (-W) T w))) =
      Supp9B.refl (c.2.1 (QuantumZipper.fwdMapInv W T (Supp9B.refl w)))
    have := fwdMapInv_neg_all W hT (Supp9B.refl w)
    rw [refl_refl] at this
    rw [this, refl_refl]
  · show (QuantumZipper.logDerivFwd (-W) T (Supp9B.refl (c.1 (Supp9B.refl z)))).im + -c.2.2 (Supp9B.refl z) =
      -((QuantumZipper.logDerivFwd W T (c.1 (Supp9B.refl z))).im + c.2.2 (Supp9B.refl z))
    rw [refl_eq_reflectC, LP.im_logDerivFwd_neg W hT]
    ring

/-! ### The observables of a launch -/

theorem stopDrv_negDrv (t : ℝ≥0∞) (d : (ℝ≥0 → ℝ) × ℝ≥0∞) : stopDrv t (negDrv d) = -stopDrv t d := by
  funext x; rfl

theorem stopTime_negDrv (t : ℝ≥0∞) (d : (ℝ≥0 → ℝ) × ℝ≥0∞) : stopTime t (negDrv d) = stopTime t d := rfl

theorem reflChart_fwd_ofReal (c : Chart) (x : ℝ) :
    (reflChart c).1 (x : ℂ) = LP.reflectC (c.1 ((-x : ℝ) : ℂ)) := by
  show Supp9B.refl (c.1 (Supp9B.refl (x : ℂ))) = _
  rw [refl_ofReal]; rfl

theorem lAlive_reflChart (c : Chart) (t : ℝ≥0∞) (d : (ℝ≥0 → ℝ) × ℝ≥0∞) (x : ℝ) :
    lAlive (reflChart c) t (negDrv d) (x : ℂ) ↔ lAlive c t d ((-x : ℝ) : ℂ) := by
  unfold lAlive
  rw [stopDrv_negDrv, stopTime_negDrv, reflChart_fwd_ofReal]
  exact LP.exists_isForwardSol_neg_iff

theorem lHit_reflChart (c : Chart) (t : ℝ≥0∞) (d : (ℝ≥0 → ℝ) × ℝ≥0∞) (x : ℝ) :
    lHit (reflChart c) t (negDrv d) (x : ℂ) ↔ lHit c t d ((-x : ℝ) : ℂ) := by
  unfold lHit
  rw [lAlive_reflChart, stopDrv_negDrv, stopTime_negDrv, reflChart_fwd_ofReal]
  simp only [LP.exists_isForwardSol_neg_iff]

theorem exists_hitR_reflState (s : ExplState) (t : ℝ≥0∞) (d : (ℝ≥0 → ℝ) × ℝ≥0∞) :
    (∃ x : ℝ, stRecR (reflState s) < x ∧ lHit (stChart (reflState s)) t (negDrv d) x) ↔
      ∃ x : ℝ, x < stRecL s ∧ lHit (stChart s) t d x := by
  rw [stRecR_reflState, stChart_reflState]
  constructor
  · rintro ⟨x, hx, hh⟩
    exact ⟨-x, by linarith, (lHit_reflChart _ t d x).1 hh⟩
  · rintro ⟨x, hx, hh⟩
    refine ⟨-x, by linarith, (lHit_reflChart _ t d (-x)).2 ?_⟩
    rwa [neg_neg]

theorem exists_hitL_reflState (s : ExplState) (t : ℝ≥0∞) (d : (ℝ≥0 → ℝ) × ℝ≥0∞) :
    (∃ x : ℝ, x < stRecL (reflState s) ∧ lHit (stChart (reflState s)) t (negDrv d) x) ↔
      ∃ x : ℝ, stRecR s < x ∧ lHit (stChart s) t d x := by
  rw [stRecL_reflState, stChart_reflState]
  constructor
  · rintro ⟨x, hx, hh⟩
    exact ⟨-x, by linarith, (lHit_reflChart _ t d x).1 hh⟩
  · rintro ⟨x, hx, hh⟩
    refine ⟨-x, by linarith, (lHit_reflChart _ t d (-x)).2 ?_⟩
    rwa [neg_neg]

theorem lRecR_reflState (s : ExplState) (t : ℝ≥0∞) (d : (ℝ≥0 → ℝ) × ℝ≥0∞) :
    lRecR (reflState s) t (negDrv d) = -lRecL s t d := by
  unfold lRecR lRecL
  rw [← Real.sSup_neg]
  congr 1
  ext x
  simp only [stRecR_reflState, stChart_reflState, mem_insert_iff, Set.mem_ofPred_eq, Set.mem_neg, lAlive_reflChart]
  constructor
  · rintro (rfl | ⟨h1, h2⟩)
    · exact Or.inl (neg_neg _)
    · exact Or.inr ⟨by linarith, h2⟩
  · rintro (h | ⟨h1, h2⟩)
    · exact Or.inl (by rw [← h, neg_neg])
    · exact Or.inr ⟨by linarith, h2⟩

theorem lRecL_reflState (s : ExplState) (t : ℝ≥0∞) (d : (ℝ≥0 → ℝ) × ℝ≥0∞) :
    lRecL (reflState s) t (negDrv d) = -lRecR s t d := by
  unfold lRecR lRecL
  rw [← Real.sInf_neg]
  congr 1
  ext x
  simp only [stRecL_reflState, stChart_reflState, mem_insert_iff, Set.mem_ofPred_eq, Set.mem_neg, lAlive_reflChart]
  constructor
  · rintro (rfl | ⟨h1, h2⟩)
    · exact Or.inl (neg_neg _)
    · exact Or.inr ⟨by linarith, h2⟩
  · rintro (h | ⟨h1, h2⟩)
    · exact Or.inl (by rw [← h, neg_neg])
    · exact Or.inr ⟨by linarith, h2⟩

/-- **No two-sided hit**: the stopped piece does not swallow real points on both sides at its final time (the only
case in which the frozen threshold classification is not reflection symmetric). -/
def TieFree (s : ExplState) (t : ℝ≥0∞) (d : (ℝ≥0 → ℝ) × ℝ≥0∞) : Prop :=
  ¬ t < d.2 → d.2 ≠ 0 → min t d.2 ≠ ⊤ →
    ¬ ((∃ x : ℝ, stRecR s < x ∧ lHit (stChart s) t d x) ∧ ∃ x : ℝ, x < stRecL s ∧ lHit (stChart s) t d x)

theorem reflStatus_eq_tip_iff (st : ExplStatus) : reflStatus st = .inr (.inl ()) ↔ st = .inr (.inl ()) := by
  rcases st with ⟨⟨⟩⟩ | ⟨⟨⟩⟩ | (_ | r) | ⟨r, m⟩ | ⟨⟨⟩⟩ | ⟨⟨⟩⟩ <;> simp [reflStatus]

theorem lStatus_reflState (s : ExplState) (t : ℝ≥0∞) (d : (ℝ≥0 → ℝ) × ℝ≥0∞) (h : TieFree s t d)
    (hmin : min t d.2 ≠ ⊤) : lStatus (reflState s) t (negDrv d) = reflStatus (lStatus s t d) := by
  have hd : (negDrv d).2 = d.2 := rfl
  unfold lStatus
  rw [hd, exists_hitR_reflState, exists_hitL_reflState]
  by_cases h1 : t < d.2
  · simp only [h1, ↓reduceIte]; rfl
  by_cases h2 : d.2 = 0
  · have h1' : ¬ t < 0 := h2 ▸ h1
    simp only [h2, h1', ↓reduceIte, stStatus_reflState]
    by_cases ht : stStatus s = .inr (.inl ())
    · rw [ht]; rfl
    · have ht' : reflStatus (stStatus s) ≠ .inr (.inl ()) := fun h => ht ((reflStatus_eq_tip_iff _).1 h)
      rcases hst : stStatus s with ⟨⟨⟩⟩ | ⟨⟨⟩⟩ | o | ⟨r, m⟩ | ⟨⟨⟩⟩ | ⟨⟨⟩⟩
      all_goals rw [hst] at ht ht'
      all_goals try exact absurd rfl ht
      all_goals try rfl
      rcases o with _ | r <;> rfl
  simp only [h1, h2, ↓reduceIte]
  by_cases hR : ∃ x : ℝ, stRecR s < x ∧ lHit (stChart s) t d x
  · have hL : ¬ ∃ x : ℝ, x < stRecL s ∧ lHit (stChart s) t d x := fun hL => h h1 h2 hmin ⟨hR, hL⟩
    simp [hR, hL, reflStatus]
  · by_cases hL : ∃ x : ℝ, x < stRecL s ∧ lHit (stChart s) t d x
    · simp [hR, hL, reflStatus]
    · simp [hR, hL, reflStatus]

theorem lPt_reflState (s : ExplState) (t : ℝ≥0∞) (d : (ℝ≥0 → ℝ) × ℝ≥0∞) (h : TieFree s t d)
    (hmin : min t d.2 ≠ ⊤) : lPt (reflState s) t (negDrv d) = -lPt s t d := by
  have hd : (negDrv d).2 = d.2 := rfl
  unfold lPt
  rw [hd, exists_hitR_reflState, exists_hitL_reflState, stPt_reflState]
  by_cases h1 : t < d.2
  · simp [h1]
  by_cases h2 : d.2 = 0
  · simp [h2]
  simp only [h1, h2, ↓reduceIte]
  by_cases hR : ∃ x : ℝ, stRecR s < x ∧ lHit (stChart s) t d x
  · have hL : ¬ ∃ x : ℝ, x < stRecL s ∧ lHit (stChart s) t d x := fun hL => h h1 h2 hmin ⟨hR, hL⟩
    simp only [hR, hL, ↓reduceIte, lRecL_reflState]
  · by_cases hL : ∃ x : ℝ, x < stRecL s ∧ lHit (stChart s) t d x
    · simp only [hR, hL, ↓reduceIte, lRecR_reflState]
    · simp only [hR, hL, ↓reduceIte]

/-- **At a two-sided hit both launches are right thresholds.** -/
theorem lStatus_of_not_tieFree (s : ExplState) (t : ℝ≥0∞) (d : (ℝ≥0 → ℝ) × ℝ≥0∞) (h : ¬ TieFree s t d) :
    lStatus s t d = stThr (some true) ∧ lStatus (reflState s) t (negDrv d) = stThr (some true) := by
  simp only [TieFree, not_forall, not_not] at h
  obtain ⟨h1, h2, -, hR, hL⟩ := h
  have hd : (negDrv d).2 = d.2 := rfl
  refine ⟨?_, ?_⟩
  · unfold lStatus
    simp only [h1, h2, hR, ↓reduceIte]
  · unfold lStatus
    rw [hd, exists_hitR_reflState]
    simp only [h1, h2, hL, ↓reduceIte]

end InteractingSLE.Theorem14.SB.Lf
