/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Exist.StagedLaw2State

/-!
# A launch of a measurable random state with a measurable regular driver is measurable

Packet PROVE-STAGEDLAW2. `ExplState.launch` (frozen) runs an ordinary piece with the stopped driver up to the stop
`min t ζ`. Its new chart composes the forward Loewner map with the old chart; its new records are suprema and infima
over the real points not alive at the stop; its new status decides threshold events quantified over all real points.
With the chart profile invariant of `IsMeasState` all of these are measurable (`IsMeasState.launch`):

* `launch_eq_of_ne_top`, `launch_eq_of_top`: the observables of a launch, explicitly;
* `sInf_insert_eq_neg_newRec`: the left record is the right record of the reflected profile;
* on a constant chart, every threshold quantity is evaluated at one point; on a good profile, through
  `newRec_le_iff` and `exists_hit_iff` (countably many points and two measurable candidates); on a bad record nothing
  is alive at the stop and the new chart is constant.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Filter Set Topology
open scoped NNReal ENNReal

namespace InteractingSLE

namespace Exist

namespace StagedLaw

open QuantumZipper Staged

/-! ### Status values -/

/-- Status *tip*. -/
abbrev stTip : ExplStatus := .inr (.inl ())
/-- Status *thr*. -/
abbrev stThr (o : Option Bool) : ExplStatus := .inr (.inr (.inl o))
/-- Status *done*. -/
abbrev stDone : ExplStatus := .inr (.inr (.inr (.inr (.inl ()))))
/-- Status *dead*. -/
abbrev stDead : ExplStatus := .inr (.inr (.inr (.inr (.inr ()))))

/-! ### The observables of a launch -/

section Eq

variable (s : ExplState) (k : ℕ) (d : (ℝ≥0 → ℝ) × ℝ≥0∞) (θ : ℝ) (t : ℝ≥0∞)

/-- The alive predicate of a launch at a point of the chart. -/
def lAlive (c : Chart) (t : ℝ≥0∞) (d : (ℝ≥0 → ℝ) × ℝ≥0∞) (z : ℂ) : Prop :=
  ∃ u, IsForwardSol (stopDrv t d) (c.1 z) (stopTime t d) u

/-- The hit predicate of a launch at a point of the chart. -/
def lHit (c : Chart) (t : ℝ≥0∞) (d : (ℝ≥0 → ℝ) × ℝ≥0∞) (z : ℂ) : Prop :=
  (∀ r < stopTime t d, ∃ u, IsForwardSol (stopDrv t d) (c.1 z) r u) ∧ ¬ lAlive c t d z

/-- The new right record of a launch. -/
def lRecR (s : ExplState) (t : ℝ≥0∞) (d : (ℝ≥0 → ℝ) × ℝ≥0∞) : ℝ :=
  sSup (insert (stRecR s) {x : ℝ | stRecR s < x ∧ ¬ lAlive (stChart s) t d x})

/-- The new left record of a launch. -/
def lRecL (s : ExplState) (t : ℝ≥0∞) (d : (ℝ≥0 → ℝ) × ℝ≥0∞) : ℝ :=
  sInf (insert (stRecL s) {x : ℝ | x < stRecL s ∧ ¬ lAlive (stChart s) t d x})

open Classical in
/-- The new status of a launch with a finite stop. -/
def lStatus (s : ExplState) (t : ℝ≥0∞) (d : (ℝ≥0 → ℝ) × ℝ≥0∞) : ExplStatus :=
  if t < d.2 then stTip
  else if d.2 = 0 then
    (match stStatus s with
      | .inr (.inl ()) => stDead
      | _ => stThr none)
  else if ∃ x : ℝ, stRecR s < x ∧ lHit (stChart s) t d x then stThr (some true)
  else if ∃ x : ℝ, x < stRecL s ∧ lHit (stChart s) t d x then stThr (some false)
  else stDead

open Classical in
/-- The new current point of a launch with a finite stop. -/
def lPt (s : ExplState) (t : ℝ≥0∞) (d : (ℝ≥0 → ℝ) × ℝ≥0∞) : ℝ :=
  if t < d.2 then stPt s
  else if d.2 = 0 then stPt s
  else if ∃ x : ℝ, stRecR s < x ∧ lHit (stChart s) t d x then lRecR s t d
  else if ∃ x : ℝ, x < stRecL s ∧ lHit (stChart s) t d x then lRecL s t d
  else stPt s

theorem stopDrv_def (t : ℝ≥0∞) (d : (ℝ≥0 → ℝ) × ℝ≥0∞) :
    stopDrv t d = fun r : ℝ => d.1 (min ((r.toNNReal : ℝ≥0) : ℝ≥0∞) (min t d.2)).toNNReal := rfl

/-- **The observables of a launch with a finite stop.** -/
theorem launch_eq_of_ne_top (h : min t d.2 ≠ ⊤) :
    stChart (ExplState.launch s k d θ t) = (stChart s).loewner (stopDrv t d) (stopTime t d) ∧
      stAngle (ExplState.launch s k d θ t) = θ ∧ stRecR (ExplState.launch s k d θ t) = lRecR s t d ∧
      stRecL (ExplState.launch s k d θ t) = lRecL s t d ∧ stStatus (ExplState.launch s k d θ t) = lStatus s t d ∧
      stPt (ExplState.launch s k d θ t) = lPt s t d := by
  obtain ⟨pieces, arcs, retained, launches, chart, status, pt, angle, recR, recL⟩ := s
  rcases status with ⟨⟨⟩⟩ | ⟨⟨⟩⟩ | o | p | ⟨⟨⟩⟩ | ⟨⟨⟩⟩ <;>
  · simp only [ExplState.launch, h, ↓reduceIte]
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
    · split_ifs <;> rfl
    · split_ifs <;> rfl
    · split_ifs <;> rfl
    · split_ifs <;> rfl
    · simp only [apply_ite stStatus]
      rfl
    · simp only [apply_ite stPt]
      rfl

/-- **The observables of a launch with an infinite stop.** -/
theorem launch_eq_of_top (h : min t d.2 = ⊤) :
    stChart (ExplState.launch s k d θ t) = stChart s ∧ stAngle (ExplState.launch s k d θ t) = θ ∧
      stRecR (ExplState.launch s k d θ t) = stRecR s ∧ stRecL (ExplState.launch s k d θ t) = stRecL s ∧
      stStatus (ExplState.launch s k d θ t) = stDone ∧ stPt (ExplState.launch s k d θ t) = stPt s := by
  obtain ⟨pieces, arcs, retained, launches, chart, status, pt, angle, recR, recL⟩ := s
  simp only [ExplState.launch, h, ↓reduceIte, and_self]

end Eq


/-! ### Deterministic helpers -/

section Helpers

theorem IsUpDown.neg {A : ℝ → Prop} (h : IsUpDown A) : IsUpDown fun y => A (-y) :=
  ⟨fun q y hq hqy hA => h.2 (-q) (-y) (by linarith) (by linarith) hA,
    fun q y hyq hq hA => h.1 (-q) (-y) (by linarith) (by linarith) hA⟩

/-- **The left record is the right record of the reflected profile.** -/
theorem sInf_insert_eq_neg_newRec (m : ℝ → ℝ) (A : ℝ → Prop) (a : ℝ) :
    sInf (insert a {x | x < a ∧ ¬ A (m x)}) = -newRec (fun x => -m (-x)) (-a) (fun y => A (-y)) := by
  rw [Real.sInf_def, newRec]
  congr 2
  ext x
  simp only [Set.mem_neg, mem_insert_iff, mem_ofPred_eq, neg_neg]
  constructor
  · rintro (h | ⟨h1, h2⟩)
    · exact Or.inl (by linarith)
    · exact Or.inr ⟨by linarith, h2⟩
  · rintro (h | ⟨h1, h2⟩)
    · exact Or.inl (by linarith)
    · exact Or.inr ⟨by linarith, h2⟩

/-- A measurable function agreeing off a measurable set `P` with a measurable function, whose sublevel sets meet `P`
measurably. -/
theorem measurable_of_Iic_on {Ω : Type*} [MeasurableSpace Ω] {f g : Ω → ℝ} {P : Set Ω} (hP : MeasurableSet P)
    (hg : Measurable g) (heq : ∀ ω ∉ P, f ω = g ω) (hf : ∀ c, MeasurableSet (P ∩ {ω | f ω ≤ c})) :
    Measurable f := by
  refine measurable_of_Iic fun c => ?_
  have e : f ⁻¹' Iic c = (P ∩ {ω | f ω ≤ c}) ∪ (Pᶜ ∩ {ω | g ω ≤ c}) := by
    ext ω
    by_cases hω : ω ∈ P <;> simp [hω, heq ω]
  rw [e]
  exact (hf c).union (hP.compl.inter (measurableSet_le hg measurable_const))

theorem stopTime_pos_of {t : ℝ≥0∞} {d : (ℝ≥0 → ℝ) × ℝ≥0∞} (h1 : min t d.2 ≠ ⊤) (h2 : ¬ t < d.2) (h3 : d.2 ≠ 0) :
    0 < stopTime t d := by
  have hle : d.2 ≤ t := not_lt.1 h2
  have hmin : min t d.2 = d.2 := min_eq_right hle
  rw [hmin] at h1
  simp only [stopTime, hmin, NNReal.coe_pos]
  exact ENNReal.toNNReal_pos h3 h1

/-- The alive set at the stop always has the order shape. -/
theorem isUpDown_aliveStop {t : ℝ≥0∞} {d : (ℝ≥0 → ℝ) × ℝ≥0∞} (hd : IsRegularDriver d) :
    IsUpDown fun y : ℝ => ∃ u, IsForwardSol (stopDrv t d) (y : ℂ) (stopTime t d) u := by
  by_cases hF : min t d.2 = ⊤
  · have hT : stopTime t d = 0 := by simp [stopTime, hF]
    simp_rw [hT, exists_isForwardSol_zero_iff, stopDrv_zero hd, Complex.ofReal_zero, ne_eq, Complex.ofReal_eq_zero]
    exact ⟨fun q y hq hqy _ => by linarith, fun q y hyq hq _ => by linarith⟩
  · by_cases hG : LocalExt.IsDrvGood (recHist (recOf t d))
    · exact (isRealFlow_stop hd hG).isUpDown
    · have h := not_alive_stop hd hF hG
      exact ⟨fun q y _ _ hq => absurd hq (h _), fun q y _ _ hq => absurd hq (h _)⟩

end Helpers


/-! ### Measurability of records and threshold events, by pieces -/

section Pieces

variable {Ω : Type*} [MeasurableSpace Ω]

/-- **The new record is measurable**: at an infinite stop it is the old one; on a constant chart it is the old one or
`0`; on a bad record it is `0`; on a good profile with a good record it is read by `newRec_le_iff`. -/
theorem measurable_newRec_pieces {m : Ω → ℝ → ℝ} {a : Ω → ℝ} {A : Ω → ℝ → Prop} {f : Ω → ℝ}
    {F K G : Set Ω} (hF : MeasurableSet F) (hK : MeasurableSet K) (hG : MeasurableSet G) (ha : Measurable a)
    (hm : ∀ x, Measurable fun ω => m ω x) (hAud : ∀ ω, IsUpDown (A ω))
    (hAm : ∀ y : Ω → ℝ, Measurable y → MeasurableSet {ω | A ω (y ω)})
    (hfF : ∀ ω ∈ F, f ω = a ω) (hfN : ∀ ω ∉ F, f ω = newRec (m ω) (a ω) (A ω))
    (hconst : ∀ ω ∈ K, ∀ x, m ω x = m ω 0) (hgood : ∀ ω ∉ K, RightGood (m ω) (a ω))
    (hflow : ∀ ω ∉ F, ω ∈ G → ∃ fl, IsRealHalf (A ω) fl) (hdead : ∀ ω ∉ F, ω ∉ G → ∀ y, ¬ A ω y) :
    Measurable f := by
  classical
  have hpos : Measurable fun ω => posInf (A ω) := measurable_posInf hAud fun q => hAm _ measurable_const
  set g : Ω → ℝ := F.piecewise a (K.piecewise (fun ω => if A ω (m ω 0) then a ω else 0) fun _ => 0) with hgdef
  have hg : Measurable g :=
    Measurable.piecewise hF ha (Measurable.piecewise hK (Measurable.ite (hAm _ (hm 0)) ha measurable_const)
      measurable_const)
  refine measurable_of_Iic_on (P := Fᶜ ∩ Kᶜ ∩ G) ((hF.compl.inter hK.compl).inter hG) hg (fun ω hω => ?_)
    (fun c => ?_)
  · by_cases hωF : ω ∈ F
    · rw [hfF ω hωF, hgdef, piecewise_eq_of_mem _ _ _ hωF]
    · rw [hfN ω hωF, hgdef, piecewise_eq_of_notMem _ _ _ hωF]
      by_cases hωK : ω ∈ K
      · rw [piecewise_eq_of_mem _ _ _ hωK, newRec_of_const (hconst ω hωK)]
      · rw [piecewise_eq_of_notMem _ _ _ hωK]
        have hωG : ω ∉ G := fun h => hω ⟨⟨hωF, hωK⟩, h⟩
        exact newRec_of_dead (hgood ω hωK) (hdead ω hωF hωG)
  · have e : (Fᶜ ∩ Kᶜ ∩ G) ∩ {ω | f ω ≤ c} = (Fᶜ ∩ Kᶜ ∩ G) ∩ ({ω | a ω ≤ c} ∩
        ⋂ q : ℚ, ({ω | max (a ω) c < q}ᶜ ∪ {ω | posInf (A ω) ≤ m ω q})) := by
      ext ω
      simp only [mem_inter_iff, mem_compl_iff, mem_ofPred_eq, mem_iInter, mem_union, not_lt]
      constructor
      · rintro ⟨⟨⟨hωF, hωK⟩, hωG⟩, hfc⟩
        obtain ⟨fl, hfl⟩ := hflow ω hωF hωG
        rw [hfN ω hωF, newRec_le_iff (hgood ω hωK) hfl] at hfc
        refine ⟨⟨⟨hωF, hωK⟩, hωG⟩, hfc.1, fun q => ?_⟩
        by_cases hq : max (a ω) c < q
        · exact Or.inr (hfc.2 q hq)
        · exact Or.inl (not_lt.1 hq)
      · rintro ⟨⟨⟨hωF, hωK⟩, hωG⟩, hac, hq⟩
        obtain ⟨fl, hfl⟩ := hflow ω hωF hωG
        refine ⟨⟨⟨hωF, hωK⟩, hωG⟩, ?_⟩
        rw [hfN ω hωF, newRec_le_iff (hgood ω hωK) hfl]
        exact ⟨hac, fun q hq' => (hq q).resolve_left (not_le.2 hq')⟩
    rw [e]
    refine ((hF.compl.inter hK.compl).inter hG).inter ((measurableSet_le ha measurable_const).inter
      (MeasurableSet.iInter fun q => ?_))
    exact (measurableSet_lt (ha.max measurable_const) measurable_const).compl.union
      (measurableSet_le hpos (hm q))

/-- **A threshold event is measurable**: on a constant chart it is evaluated at one point; on a good profile it is
read by `exists_hit_iff`. -/
theorem measurableSet_hit_pieces {m : Ω → ℝ → ℝ} {a : Ω → ℝ} {H A : Ω → ℝ → Prop} {E K : Set Ω}
    (hE : MeasurableSet E) (hK : MeasurableSet K) (ha : Measurable a) (hm : ∀ x, Measurable fun ω => m ω x)
    (hHud : ∀ ω, IsUpDown (H ω)) (hAud : ∀ ω, IsUpDown (A ω))
    (hHm : ∀ y : Ω → ℝ, Measurable y → MeasurableSet {ω | H ω (y ω)})
    (hAm : ∀ y : Ω → ℝ, Measurable y → MeasurableSet {ω | A ω (y ω)}) (hH0 : ∀ ω ∈ E, ¬ H ω 0)
    (hconst : ∀ ω ∈ K, ∀ x, m ω x = m ω 0) (hgood : ∀ ω ∉ K, RightGood (m ω) (a ω)) :
    MeasurableSet (E ∩ {ω | ∃ x, a ω < x ∧ H ω (m ω x) ∧ ¬ A ω (m ω x)}) := by
  have hpos : Measurable fun ω => posInf (A ω) := measurable_posInf hAud fun q => hAm _ measurable_const
  have hneg : Measurable fun ω => negSup (A ω) := measurable_negSup hAud fun q => hAm _ measurable_const
  set Ψ : (Ω → ℝ) → Set Ω := fun y => ⋃ q' : ℚ, {ω | a ω < q'} ∩ {ω | m ω q' < y ω} with hΨ
  have hΨm : ∀ y : Ω → ℝ, Measurable y → MeasurableSet (Ψ y) := fun y hy =>
    MeasurableSet.iUnion fun q' => (measurableSet_lt ha measurable_const).inter (measurableSet_lt (hm q') hy)
  set hitE : (Ω → ℝ) → Set Ω := fun y => {ω | H ω (y ω)} ∩ {ω | A ω (y ω)}ᶜ with hhitE
  have hhitm : ∀ y : Ω → ℝ, Measurable y → MeasurableSet (hitE y) := fun y hy =>
    (hHm y hy).inter (hAm y hy).compl
  have e : E ∩ {ω | ∃ x, a ω < x ∧ H ω (m ω x) ∧ ¬ A ω (m ω x)} =
      (E ∩ K ∩ hitE fun ω => m ω 0) ∪ (E ∩ Kᶜ ∩ ((⋃ q : ℚ, Ψ (fun _ => (q : ℝ)) ∩ hitE fun _ => (q : ℝ)) ∪
        (Ψ (fun ω => posInf (A ω)) ∩ hitE fun ω => posInf (A ω)) ∪
        (Ψ (fun ω => negSup (A ω)) ∩ hitE fun ω => negSup (A ω)))) := by
    ext ω
    simp only [mem_inter_iff, mem_union, mem_compl_iff, mem_ofPred_eq, mem_iUnion, hΨ, hhitE]
    by_cases hωK : ω ∈ K
    · simp only [hωK, not_true_eq_false, and_false, false_and, or_false, and_true]
      constructor
      · rintro ⟨hωE, x, -, hH, hA⟩
        exact ⟨hωE, by rw [← hconst ω hωK x]; exact hH, by rw [← hconst ω hωK x]; exact hA⟩
      · rintro ⟨hωE, hH, hA⟩
        exact ⟨hωE, a ω + 1, by linarith, by rw [hconst ω hωK]; exact hH, by rw [hconst ω hωK]; exact hA⟩
    · simp only [hωK, false_and, and_false, false_or, not_false_eq_true, and_true]
      refine and_congr_right fun hωE => ?_
      rw [exists_hit_iff (hgood ω hωK) (hH0 ω hωE) (hHud ω) (hAud ω)]
      simp only [exists_lt_iff_rat (hgood ω hωK)]
      rw [or_assoc]
  rw [e]
  refine ((hE.inter hK).inter (hhitm _ (hm 0))).union ((hE.inter hK.compl).inter (MeasurableSet.union
    (MeasurableSet.union (MeasurableSet.iUnion fun q => (hΨm _ measurable_const).inter
      (hhitm _ measurable_const)) ((hΨm _ hpos).inter (hhitm _ hpos))) ((hΨm _ hneg).inter (hhitm _ hneg))))

end Pieces


/-! ### The launch -/

section Main

theorem lHit_iff {c : Chart} (hc : IsRealChart c) (t : ℝ≥0∞) (d : (ℝ≥0 → ℝ) × ℝ≥0∞) (x : ℝ) :
    lHit c t d x ↔ (∀ r < stopTime t d, ∃ u, IsForwardSol (stopDrv t d) ((rProf c x : ℝ) : ℂ) r u) ∧
      ¬ ∃ u, IsForwardSol (stopDrv t d) ((rProf c x : ℝ) : ℂ) (stopTime t d) u := by
  rw [lHit, lAlive, hc.eq_ofReal x]

theorem lRecR_eq_newRec {s : ExplState} (hc : IsRealChart (stChart s)) (t : ℝ≥0∞) (d : (ℝ≥0 → ℝ) × ℝ≥0∞) :
    lRecR s t d = newRec (rProf (stChart s)) (stRecR s)
      (fun y : ℝ => ∃ u, IsForwardSol (stopDrv t d) (y : ℂ) (stopTime t d) u) := by
  unfold lRecR newRec
  simp only [lAlive, hc.eq_ofReal]

theorem lRecL_eq_newRec {s : ExplState} (hc : IsRealChart (stChart s)) (t : ℝ≥0∞) (d : (ℝ≥0 → ℝ) × ℝ≥0∞) :
    lRecL s t d = -newRec (lProf (stChart s)) (-stRecL s)
      (fun y : ℝ => ∃ u, IsForwardSol (stopDrv t d) ((-y : ℝ) : ℂ) (stopTime t d) u) := by
  unfold lRecL
  simp only [lAlive, hc.eq_ofReal]
  exact sInf_insert_eq_neg_newRec (rProf (stChart s))
    (fun y : ℝ => ∃ u, IsForwardSol (stopDrv t d) (y : ℂ) (stopTime t d) u) (stRecL s)

variable {Ω : Type*} [MeasurableSpace Ω] {S : Ω → ExplState} {D : Ω → (ℝ≥0 → ℝ) × ℝ≥0∞}

/-- **A launch of a measurable random state with a measurable, everywhere regular driver is measurable.** -/
theorem IsMeasState.launch (hS : IsMeasState S) (hD : Measurable D) (hreg : ∀ ω, IsRegularDriver (D ω)) (k : ℕ)
    (θ : ℝ) (t : ℝ≥0∞) : IsMeasState fun ω => ExplState.launch (S ω) k (D ω) θ t := by
  classical
  obtain ⟨hst, hp, ha, hR, hL, hc, hr, K, hK, hKc, hKg⟩ := hS
  set F := {ω | min t (D ω).2 = ⊤} with hFdef
  have hF : MeasurableSet F := measurableSet_stop_top t hD
  set G := {ω | LocalExt.IsDrvGood (recHist (recOf t (D ω)))} with hGdef
  have hG : MeasurableSet G := measurableSet_good t hD hreg
  set A : Ω → ℝ → Prop := fun ω y => ∃ u, IsForwardSol (stopDrv t (D ω)) (y : ℂ) (stopTime t (D ω)) u with hAdef
  set H : Ω → ℝ → Prop := fun ω y => ∀ r < stopTime t (D ω), ∃ u, IsForwardSol (stopDrv t (D ω)) (y : ℂ) r u
    with hHdef
  have hAm : ∀ y : Ω → ℝ, Measurable y → MeasurableSet {ω | A ω (y ω)} := fun y hy =>
    (measurable_fwdMap_stop t hD hreg (Complex.measurable_ofReal.comp hy)).2
  have hHm : ∀ y : Ω → ℝ, Measurable y → MeasurableSet {ω | H ω (y ω)} := fun y hy =>
    measurableSet_aliveBefore t hD hreg (Complex.measurable_ofReal.comp hy)
  have hAud : ∀ ω, IsUpDown (A ω) := fun ω => isUpDown_aliveStop (hreg ω)
  have hHud : ∀ ω, IsUpDown (H ω) := fun ω => isUpDown_aliveBefore (hreg ω)
  have hAm' : ∀ y : Ω → ℝ, Measurable y → MeasurableSet {ω | A ω (-(y ω))} := fun y hy => hAm _ hy.neg
  have hHm' : ∀ y : Ω → ℝ, Measurable y → MeasurableSet {ω | H ω (-(y ω))} := fun y hy => hHm _ hy.neg
  have hm : ∀ x : ℝ, Measurable fun ω => rProf (stChart (S ω)) x := fun x => Complex.measurable_re.comp (hc x)
  have hml : ∀ x : ℝ, Measurable fun ω => lProf (stChart (S ω)) x := fun x =>
    (Complex.measurable_re.comp (hc _)).neg
  have hconstR : ∀ ω ∈ K, ∀ x, rProf (stChart (S ω)) x = rProf (stChart (S ω)) 0 := fun ω hω x => by
    simp only [rProf, hKc ω hω x, Complex.ofReal_zero]
  have hconstL : ∀ ω ∈ K, ∀ x, lProf (stChart (S ω)) x = lProf (stChart (S ω)) 0 := fun ω hω x => by
    simp only [lProf, hKc ω hω (-x), neg_zero, Complex.ofReal_zero]
  have hflowR : ∀ ω ∉ F, ω ∈ G → ∃ fl, IsRealHalf (A ω) fl := fun ω _ hωG =>
    ⟨_, (isRealFlow_stop (hreg ω) hωG).1⟩
  have hflowL : ∀ ω ∉ F, ω ∈ G → ∃ fl, IsRealHalf (fun y => A ω (-y)) fl := fun ω _ hωG =>
    ⟨_, (isRealFlow_stop (hreg ω) hωG).2⟩
  have hdead : ∀ ω ∉ F, ω ∉ G → ∀ y, ¬ A ω y := fun ω hωF hωG _ => not_alive_stop (hreg ω) hωF hωG _
  -- the records
  have hRm : Measurable fun ω => stRecR (ExplState.launch (S ω) k (D ω) θ t) :=
    measurable_newRec_pieces hF hK hG hR hm hAud hAm
      (fun ω hω => (launch_eq_of_top _ k _ θ t hω).2.2.1)
      (fun ω hω => by rw [(launch_eq_of_ne_top _ k _ θ t hω).2.2.1, lRecR_eq_newRec (hr ω)])
      hconstR (fun ω hω => (hKg ω hω).1) hflowR hdead
  have hLm' : Measurable fun ω => -stRecL (ExplState.launch (S ω) k (D ω) θ t) :=
    measurable_newRec_pieces (a := fun ω => -stRecL (S ω)) (A := fun ω y => A ω (-y))
      (f := fun ω => -stRecL (ExplState.launch (S ω) k (D ω) θ t)) hF hK hG hL.neg hml (fun ω => (hAud ω).neg) hAm'
      (fun ω hω => by rw [(launch_eq_of_top _ k _ θ t hω).2.2.2.1])
      (fun ω hω => by rw [(launch_eq_of_ne_top _ k _ θ t hω).2.2.2.1, lRecL_eq_newRec (hr ω), neg_neg])
      hconstL (fun ω hω => (hKg ω hω).2) hflowL (fun ω hωF hωG y => hdead ω hωF hωG _)
  have hLm : Measurable fun ω => stRecL (ExplState.launch (S ω) k (D ω) θ t) := by
    have e : (fun ω => stRecL (ExplState.launch (S ω) k (D ω) θ t)) =
        fun ω => -(-stRecL (ExplState.launch (S ω) k (D ω) θ t)) := funext fun _ => (neg_neg _).symm
    rw [e]; exact hLm'.neg
  -- the threshold events
  set E₀ := Fᶜ ∩ {ω | ¬ t < (D ω).2} ∩ {ω | (D ω).2 ≠ 0} with hE₀def
  have hζ : Measurable fun ω => (D ω).2 := measurable_snd.comp hD
  have hE₀ : MeasurableSet E₀ :=
    (hF.compl.inter (measurableSet_lt measurable_const hζ).compl).inter
      (measurableSet_eq_fun hζ measurable_const).compl
  have hH0 : ∀ ω ∈ E₀, ¬ H ω 0 := fun ω hω => by
    have := not_aliveBefore_zero (hreg ω) (stopTime_pos_of hω.1.1 hω.1.2 hω.2)
    simpa [hHdef] using this
  set ER := E₀ ∩ {ω | ∃ x : ℝ, stRecR (S ω) < x ∧ lHit (stChart (S ω)) t (D ω) x} with hERdef
  set EL := E₀ ∩ {ω | ∃ x : ℝ, x < stRecL (S ω) ∧ lHit (stChart (S ω)) t (D ω) x} with hELdef
  have hER : MeasurableSet ER := by
    have h := measurableSet_hit_pieces hE₀ hK hR hm hHud hAud hHm hAm hH0 hconstR (fun ω hω => (hKg ω hω).1)
    have e : ER = E₀ ∩ {ω | ∃ x, stRecR (S ω) < x ∧ H ω (rProf (stChart (S ω)) x) ∧
        ¬ A ω (rProf (stChart (S ω)) x)} := by
      ext ω
      simp only [hERdef, mem_inter_iff, mem_ofPred_eq, lHit_iff (hr ω), hHdef, hAdef]
    rw [e]; exact h
  have hEL : MeasurableSet EL := by
    have h := measurableSet_hit_pieces (m := fun ω => lProf (stChart (S ω))) (a := fun ω => -stRecL (S ω))
      (H := fun ω y => H ω (-y)) (A := fun ω y => A ω (-y)) hE₀ hK hL.neg hml (fun ω => (hHud ω).neg)
      (fun ω => (hAud ω).neg) hHm' hAm' (fun ω hω => by simpa using hH0 ω hω) hconstL (fun ω hω => (hKg ω hω).2)
    have e : EL = E₀ ∩ {ω | ∃ x, -stRecL (S ω) < x ∧ H ω (-lProf (stChart (S ω)) x) ∧
        ¬ A ω (-lProf (stChart (S ω)) x)} := by
      ext ω
      simp only [hELdef, mem_inter_iff, mem_ofPred_eq, lHit_iff (hr ω), hHdef, hAdef]
      refine and_congr_right fun _ =>
        ⟨fun ⟨x, hx, hh⟩ => ⟨-x, by linarith, ?_⟩, fun ⟨x, hx, hh⟩ => ⟨-x, by linarith, ?_⟩⟩
      · simpa only [lProf, rProf, neg_neg] using hh
      · simpa only [lProf, rProf, neg_neg] using hh
    rw [e]; exact h
  -- the status
  let _ : MeasurableSpace ExplStatus := ⊤
  have hstat : Measurable fun ω => stStatus (ExplState.launch (S ω) k (D ω) θ t) := by
    have e : (fun ω => stStatus (ExplState.launch (S ω) k (D ω) θ t)) = fun ω =>
        if ω ∈ F then stDone else if t < (D ω).2 then stTip
        else if (D ω).2 = 0 then (match stStatus (S ω) with
          | .inr (.inl ()) => stDead
          | _ => stThr none)
        else if ω ∈ ER then stThr (some true) else if ω ∈ EL then stThr (some false) else stDead := by
      funext ω
      by_cases hωF : ω ∈ F
      · simp only [hωF, ↓reduceIte]
        exact (launch_eq_of_top _ k _ θ t hωF).2.2.2.2.1
      · rw [(launch_eq_of_ne_top _ k _ θ t hωF).2.2.2.2.1, lStatus]
        simp only [hωF, ↓reduceIte]
        by_cases h1 : t < (D ω).2
        · simp only [h1, ↓reduceIte]
        · by_cases h2 : (D ω).2 = 0
          · simp only [h2, ↓reduceIte]
          · have hω0 : ω ∈ E₀ := ⟨⟨hωF, h1⟩, h2⟩
            simp only [h1, h2, ↓reduceIte, hERdef, hELdef, mem_inter_iff, hω0, true_and, mem_ofPred_eq]
    rw [e]
    have hmatch : Measurable fun ω => (match stStatus (S ω) with
        | .inr (.inl ()) => stDead
        | _ => stThr none : ExplStatus) :=
      measurable_status_cases hst (g := fun st _ => (match st with
        | .inr (.inl ()) => stDead
        | _ => stThr none : ExplStatus)) fun _ => measurable_const
    exact Measurable.ite hF measurable_const (Measurable.ite (measurableSet_lt measurable_const hζ) measurable_const
      (Measurable.ite (measurableSet_eq_fun hζ measurable_const) hmatch
        (Measurable.ite hER measurable_const (Measurable.ite hEL measurable_const measurable_const))))
  -- the current point
  have hpt : Measurable fun ω => stPt (ExplState.launch (S ω) k (D ω) θ t) := by
    have e : (fun ω => stPt (ExplState.launch (S ω) k (D ω) θ t)) = fun ω =>
        if ω ∈ F then stPt (S ω) else if t < (D ω).2 then stPt (S ω) else if (D ω).2 = 0 then stPt (S ω)
        else if ω ∈ ER then stRecR (ExplState.launch (S ω) k (D ω) θ t)
        else if ω ∈ EL then stRecL (ExplState.launch (S ω) k (D ω) θ t) else stPt (S ω) := by
      funext ω
      by_cases hωF : ω ∈ F
      · simp only [hωF, ↓reduceIte]
        exact (launch_eq_of_top _ k _ θ t hωF).2.2.2.2.2
      · obtain ⟨-, -, hR', hL', -, hP'⟩ := launch_eq_of_ne_top (S ω) k (D ω) θ t hωF
        rw [hP', lPt, hR', hL']
        simp only [hωF, ↓reduceIte]
        by_cases h1 : t < (D ω).2
        · simp only [h1, ↓reduceIte]
        · by_cases h2 : (D ω).2 = 0
          · simp only [h2, ↓reduceIte]
          · have hω0 : ω ∈ E₀ := ⟨⟨hωF, h1⟩, h2⟩
            simp only [h1, h2, ↓reduceIte, hERdef, hELdef, mem_inter_iff, hω0, true_and, mem_ofPred_eq]
    rw [e]
    exact Measurable.ite hF hp (Measurable.ite (measurableSet_lt measurable_const hζ) hp
      (Measurable.ite (measurableSet_eq_fun hζ measurable_const) hp
        (Measurable.ite hER hRm (Measurable.ite hEL hLm hp))))
  -- the chart
  have hchart : ∀ ω, ∀ z : ℂ, (stChart (ExplState.launch (S ω) k (D ω) θ t)).1 z =
      if ω ∈ F then (stChart (S ω)).1 z else fwdMap (stopDrv t (D ω)) (stopTime t (D ω)) ((stChart (S ω)).1 z) := by
    intro ω z
    by_cases hωF : ω ∈ F
    · simp only [hωF, ↓reduceIte, (launch_eq_of_top (S ω) k (D ω) θ t hωF).1]
    · simp only [hωF, ↓reduceIte]
      rw [(launch_eq_of_ne_top (S ω) k (D ω) θ t hωF).1]
      rfl
  refine ⟨fun st => hstat (show MeasurableSet[⊤] ({st} : Set ExplStatus) from MeasurableSpace.measurableSet_top),
    hpt, ?_, hRm, hLm, fun z => ?_, fun ω x => ?_,
    K ∪ (Fᶜ ∩ Gᶜ), hK.union (hF.compl.inter hG.compl), fun ω hω x => ?_, fun ω hω => ?_⟩
  · have e : (fun ω => stAngle (ExplState.launch (S ω) k (D ω) θ t)) = fun _ => θ := by
      funext ω
      by_cases hωF : ω ∈ F
      · exact (launch_eq_of_top _ k _ θ t hωF).2.1
      · exact (launch_eq_of_ne_top _ k _ θ t hωF).2.1
    rw [e]; exact measurable_const
  · simp_rw [hchart]
    exact Measurable.ite hF (hc z) (measurable_fwdMap_stop t hD hreg (hc z)).1
  · rw [hchart]
    split_ifs
    · exact hr ω x
    · rw [(hr ω).eq_ofReal x]
      exact im_fwdMap_ofReal _ (stopTime_nonneg t (D ω)) _
  · rw [hchart, hchart]
    rcases hω with hωK | ⟨hωF, hωG⟩
    · split_ifs
      · exact hKc ω hωK x
      · rw [hKc ω hωK x]
    · simp only [show ω ∉ F from hωF, ↓reduceIte]
      rw [fwdMap_of_not (not_alive_stop (hreg ω) hωF hωG _), fwdMap_of_not (not_alive_stop (hreg ω) hωF hωG _)]
  · have hωK : ω ∉ K := fun h => hω (Or.inl h)
    by_cases hωF : ω ∈ F
    · obtain ⟨hc', -, hR', hL', -, -⟩ := launch_eq_of_top (S ω) k (D ω) θ t hωF
      unfold IsGoodProfile
      rw [hc', hR', hL']
      exact hKg ω hωK
    · have hωG : ω ∈ G := by
        by_contra hωG
        exact hω (Or.inr ⟨hωF, hωG⟩)
      obtain ⟨hc', -, hR', hL', -, -⟩ := launch_eq_of_ne_top (S ω) k (D ω) θ t hωF
      have hflow := isRealFlow_stop (hreg ω) hωG
      unfold IsGoodProfile
      rw [hR', hL', lRecR_eq_newRec (hr ω), lRecL_eq_newRec (hr ω), neg_neg]
      refine ⟨(rightGood_comp (hKg ω hωK).1 hflow.1).congr fun x _ => ?_,
        (rightGood_comp (hKg ω hωK).2 hflow.2).congr fun x _ => ?_⟩
      · show _ = ((stChart (ExplState.launch (S ω) k (D ω) θ t)).1 x).re
        rw [hc']
        show _ = (fwdMap (stopDrv t (D ω)) (stopTime t (D ω)) ((stChart (S ω)).1 x)).re
        rw [(hr ω).eq_ofReal x]
      · show _ = -((stChart (ExplState.launch (S ω) k (D ω) θ t)).1 ((-x : ℝ) : ℂ)).re
        rw [hc']
        show _ = -(fwdMap (stopDrv t (D ω)) (stopTime t (D ω)) ((stChart (S ω)).1 ((-x : ℝ) : ℂ))).re
        rw [(hr ω).eq_ofReal (-x)]
        simp only [lProf, rProf, neg_neg]

end Main

end StagedLaw

end Exist

end InteractingSLE
