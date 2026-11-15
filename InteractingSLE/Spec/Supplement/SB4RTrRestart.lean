/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.SB4RTrGood
import InteractingSLE.Spec.Supplement.GW2aContStepAux

/-!
# The restart relation of two runs of the same program

Packet PROVE-T14-SB4LEAF (ruling R104, the initial-arc version). Two runs of the same program on the same data, one
restarted from a later point of the initial forced arc, agree after the arc up to their first piece, first connector,
first launch record and left record, and up to the junk values of their chart inverses off `ℍ` (`RestartRel`). The
relation is preserved by every step whose launch (if any) has a good driver and ends at a right record, a tip, the
target or immediately (`RightExit`): the left record only enters the frozen classification when no real point right
of the right record is swallowed.

* `ChartEqH`, `PieceEqH`, `LaunchEqH`, **`RestartRel`**;
* `RestartRel.moveAlong`, `.moveToEnd`, `.setDead`, `.contBranch`, `.contStep`, **`.launch`**, **`.flowStep`**;
* `tipSet_eq_of_chartEqH`: the physical points of related pieces agree.
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

/-! ### Charts equal on `ℍ` -/

/-- Two charts with the same forward map and lift, and the same inverse on `ℍ`. -/
def ChartEqH (c c' : Chart) : Prop := c.1 = c'.1 ∧ c.2.2 = c'.2.2 ∧ EqOn c.2.1 c'.2.1 H

theorem ChartEqH.recenter {c c' : Chart} (h : ChartEqH c c') (a : ℝ) : ChartEqH (c.recenter a) (c'.recenter a) := by
  refine ⟨by rw [Chart.recenter, Chart.recenter, h.1], h.2.1, fun w hw => h.2.2 ?_⟩
  show 0 < (w + (a : ℂ)).im
  rw [Complex.add_im, Complex.ofReal_im, add_zero]
  exact hw

/-- Two pieces with `ChartEqH` charts and the same driver and stop, the driver continuous from `0`. -/
def PieceEqH (p q : Chart × (ℝ≥0 → ℝ) × ℝ≥0∞) : Prop :=
  ChartEqH p.1 q.1 ∧ p.2 = q.2 ∧ Continuous (fun r : ℝ => p.2.1 r.toNNReal) ∧ p.2.1 0 = 0

/-- The stopped driver of a good regular launch is continuous from `0`. -/
theorem stopDrv_good {d : (ℝ≥0 → ℝ) × ℝ≥0∞} (t : ℝ≥0∞) (hreg : IsRegularDriver d)
    (hg : min t d.2 ≠ ⊤ → LocalExt.IsDrvGood (recHist (recOf t d))) :
    Continuous (stopDrv t d) ∧ stopDrv t d 0 = 0 := by
  refine ⟨?_, stopDrv_zero hreg t⟩
  by_cases hF : min t d.2 = ⊤
  · have hd : d.2 = ⊤ := (min_eq_top.1 hF).2
    have hc : Continuous d.1 := by
      have := hreg.1
      rw [hd] at this
      exact continuousOn_univ.1 (by simpa using this)
    have e : stopDrv t d = fun r : ℝ => d.1 r.toNNReal := by
      funext r
      rw [stopDrv_def, hF]
      simp only [min_top_right, ENNReal.toNNReal_coe]
    rw [e]
    exact hc.comp continuous_real_toNNReal
  · rw [← recDrv_eq_stopDrv hreg (hg hF)]
    exact continuous_recDrv t d

/-- Two launch records with `ChartEqH` charts and the same angle. -/
def LaunchEqH : Option (Chart × ℝ) → Option (Chart × ℝ) → Prop
  | none, none => True
  | some p, some q => ChartEqH p.1 q.1 ∧ p.2 = q.2
  | _, _ => False

/-- **The restart relation.** -/
def RestartRel (s₁ s₂ : ExplState) : Prop :=
  (∃ (p₁ p₂ : Chart × (ℝ≥0 → ℝ) × ℝ≥0∞) (L₁ L₂ : List (Chart × (ℝ≥0 → ℝ) × ℝ≥0∞)),
      s₁.1 = p₁ :: L₁ ∧ s₂.1 = p₂ :: L₂ ∧ List.Forall₂ PieceEqH L₁ L₂) ∧
    (∃ (a₁ a₂ : Set ℝ) (M : List (Set ℝ)), s₁.2.1 = a₁ :: M ∧ s₂.2.1 = a₂ :: M) ∧
    s₁.2.2.1 = s₂.2.2.1 ∧ (∀ k, k ≠ 0 → LaunchEqH (s₁.2.2.2.1 k) (s₂.2.2.2.1 k)) ∧
    ChartEqH (stChart s₁) (stChart s₂) ∧ stStatus s₁ = stStatus s₂ ∧ stPt s₁ = stPt s₂ ∧
    stAngle s₁ = stAngle s₂ ∧ stRecR s₁ = stRecR s₂

section Ops

variable {s₁ s₂ : ExplState}

theorem RestartRel.setDead (h : RestartRel s₁ s₂) : RestartRel (Exist.StagedLaw.setDead s₁)
    (Exist.StagedLaw.setDead s₂) := by
  obtain ⟨_, _, _, _, _, _, _, _, _, _⟩ := s₁
  obtain ⟨_, _, _, _, _, _, _, _, _, _⟩ := s₂
  obtain ⟨h1, h2, h3, h4, h5, -, h7, h8, h9⟩ := h
  exact ⟨h1, h2, h3, h4, h5, rfl, h7, h8, h9⟩

theorem RestartRel.moveToEnd (h : RestartRel s₁ s₂) (right : Bool) :
    RestartRel (ExplState.moveToEnd s₁ right) (ExplState.moveToEnd s₂ right) := by
  obtain ⟨_, _, _, _, _, _, pt₁, _, _, _⟩ := s₁
  obtain ⟨_, _, _, _, _, _, pt₂, _, _, _⟩ := s₂
  obtain ⟨h1, ⟨a₁, a₂, M, e1, e2⟩, h3, h4, h5, -, h7, h8, h9⟩ := h
  change pt₁ = pt₂ at h7
  subst h7
  simp only [] at e1 e2
  refine ⟨h1, ⟨a₁, a₂, M ++ [if right then Ici pt₁ else Iic pt₁], ?_, ?_⟩, h3, h4, h5, rfl, rfl, h8, h9⟩
  · show _ ++ _ = _; rw [e1]; rfl
  · show _ ++ _ = _; rw [e2]; rfl

theorem RestartRel.moveAlong (h : RestartRel s₁ s₂) (right : Bool) (x : ℝ) (am : Bool) :
    RestartRel (ExplState.moveAlong s₁ right x am) (ExplState.moveAlong s₂ right x am) := by
  obtain ⟨_, _, _, _, c₁, _, pt₁, _, r₁, _⟩ := s₁
  obtain ⟨_, _, _, _, c₂, _, pt₂, _, r₂, _⟩ := s₂
  obtain ⟨h1, ⟨a₁, a₂, M, e1, e2⟩, h3, h4, h5, -, h7, h8, h9⟩ := h
  change pt₁ = pt₂ at h7
  change r₁ = r₂ at h9
  subst h7 h9
  simp only [] at e1 e2
  have hc : (c₁.1 x).re = (c₂.1 x).re := by rw [h5.1]
  refine ⟨h1, ⟨a₁, a₂, M ++ [if right then Icc pt₁ x else Icc x pt₁], ?_, ?_⟩, h3, h4, ?_, rfl, rfl, h8, rfl⟩
  · show _ ++ _ = _; rw [e1]; rfl
  · show _ ++ _ = _; rw [e2]; rfl
  · show ChartEqH (c₁.recenter (c₁.1 x).re) (c₂.recenter (c₂.1 x).re)
    rw [hc]; exact h5.recenter _

/-- The branch of a continuation (`StagedLaw.contBranch`) only reads the point and the angle. -/
theorem contBranch_congr (κ : ℝ) (b : ℝ → ℝ) (J : Finset ℝ) (vStop : Option ℝ) (right : Bool)
    {P : ExplState → ExplState → Prop}
    (hA : ∀ r x am, P (ExplState.moveAlong s₁ r x am) (ExplState.moveAlong s₂ r x am))
    (hE : ∀ r, P (ExplState.moveToEnd s₁ r) (ExplState.moveToEnd s₂ r)) (hpt : stPt s₁ = stPt s₂)
    (hang : stAngle s₁ = stAngle s₂) :
    P (contBranch κ b J s₁ vStop right) (contBranch κ b J s₂ vStop right) := by
  unfold contBranch
  rw [← hpt, ← hang]
  split_ifs with hr hC
  · rcases vStop with _ | w
    · exact hA _ _ _
    · simp only []
      split_ifs
      · exact hA _ _ _
      · exact hA _ _ _
  · rcases vStop with _ | w
    · exact hE _
    · simp only []
      split_ifs
      · exact hA _ _ _
      · exact hE _
  · rcases vStop with _ | w
    · exact hA _ _ _
    · simp only []
      split_ifs
      · exact hA _ _ _
      · exact hA _ _ _
  · rcases vStop with _ | w
    · exact hE _
    · simp only []
      split_ifs
      · exact hA _ _ _
      · exact hE _

theorem RestartRel.contStep (h : RestartRel s₁ s₂) (κ : ℝ) (b : ℝ → ℝ) (J : Finset ℝ) (vStop : Option ℝ)
    (pref : Bool) : RestartRel (ExplState.contStep κ b J s₁ vStop pref) (ExplState.contStep κ b J s₂ vStop pref) := by
  rw [contStep_eq_byStatus, contStep_eq_byStatus, ← h.2.2.2.2.2.1]
  have hB : ∀ r, RestartRel (contBranch κ b J s₁ vStop r) (contBranch κ b J s₂ vStop r) := fun r =>
    contBranch_congr κ b J vStop r (fun r x am => h.moveAlong r x am) (fun r => h.moveToEnd r) h.2.2.2.2.2.2.1
      h.2.2.2.2.2.2.2.1
  have hD : contDirNone κ b pref s₁ = contDirNone κ b pref s₂ := by
    unfold contDirNone
    rw [h.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2.1]
  rcases hst : stStatus s₁ with ⟨⟨⟩⟩ | ⟨⟨⟩⟩ | (_ | r) | ⟨r, (_ | _)⟩ | ⟨⟨⟩⟩ | ⟨⟨⟩⟩
  · exact h.setDead
  · exact h.setDead
  · simp only [contByStatus]
    rw [← hD]
    rcases contDirNone κ b pref s₁ with _ | (_ | _)
    · exact h.setDead
    · exact hB false
    · exact hB true
  · exact hB r
  · exact hB r
  · exact h
  · exact h
  · exact h.setDead


/-! ### The launch -/

/-- **A launch ending on the right**: whenever the frozen classification reaches its hit tests, a real point right
of the right record is swallowed. -/
def RightExit (s : ExplState) (t : ℝ≥0∞) (d : (ℝ≥0 → ℝ) × ℝ≥0∞) : Prop :=
  ¬ t < d.2 → d.2 ≠ 0 → min t d.2 ≠ ⊤ → ∃ x : ℝ, stRecR s < x ∧ lHit (stChart s) t d x

theorem lAlive_congr {c c' : Chart} (h : ChartEqH c c') (t : ℝ≥0∞) (d : (ℝ≥0 → ℝ) × ℝ≥0∞) (z : ℂ) :
    lAlive c t d z ↔ lAlive c' t d z := by
  unfold lAlive; rw [h.1]

theorem lHit_congr {c c' : Chart} (h : ChartEqH c c') (t : ℝ≥0∞) (d : (ℝ≥0 → ℝ) × ℝ≥0∞) (z : ℂ) :
    lHit c t d z ↔ lHit c' t d z := by
  unfold lHit; rw [lAlive_congr h, h.1]

theorem RestartRel.recR_launch (h : RestartRel s₁ s₂) (t : ℝ≥0∞) (d : (ℝ≥0 → ℝ) × ℝ≥0∞) :
    lRecR s₁ t d = lRecR s₂ t d := by
  unfold lRecR
  rw [h.2.2.2.2.2.2.2.2]
  congr 2
  ext x
  rw [Set.mem_ofPred_eq, Set.mem_ofPred_eq, lAlive_congr h.2.2.2.2.1]

theorem RestartRel.status_launch (h : RestartRel s₁ s₂) (t : ℝ≥0∞) (d : (ℝ≥0 → ℝ) × ℝ≥0∞) (hR : RightExit s₁ t d)
    (hmin : min t d.2 ≠ ⊤) : lStatus s₁ t d = lStatus s₂ t d := by
  have hR' : ∀ x : ℝ, stRecR s₁ < x ∧ lHit (stChart s₁) t d x ↔ stRecR s₂ < x ∧ lHit (stChart s₂) t d x :=
    fun x => by rw [h.2.2.2.2.2.2.2.2, lHit_congr h.2.2.2.2.1]
  unfold lStatus
  rw [h.2.2.2.2.2.1]
  by_cases h1 : t < d.2
  · simp only [h1, ↓reduceIte]
  by_cases h2 : d.2 = 0
  · simp only [h2, ↓reduceIte]
  obtain ⟨x, hx⟩ := hR h1 h2 hmin
  have hx' : ∃ x : ℝ, stRecR s₂ < x ∧ lHit (stChart s₂) t d x := ⟨x, (hR' x).1 hx⟩
  simp only [h1, h2, show ∃ x : ℝ, stRecR s₁ < x ∧ lHit (stChart s₁) t d x from ⟨x, hx⟩, hx', ↓reduceIte]

theorem RestartRel.pt_launch (h : RestartRel s₁ s₂) (t : ℝ≥0∞) (d : (ℝ≥0 → ℝ) × ℝ≥0∞) (hR : RightExit s₁ t d)
    (hmin : min t d.2 ≠ ⊤) : lPt s₁ t d = lPt s₂ t d := by
  have hR' : ∀ x : ℝ, stRecR s₁ < x ∧ lHit (stChart s₁) t d x ↔ stRecR s₂ < x ∧ lHit (stChart s₂) t d x :=
    fun x => by rw [h.2.2.2.2.2.2.2.2, lHit_congr h.2.2.2.2.1]
  unfold lPt
  rw [h.2.2.2.2.2.2.1, h.recR_launch]
  by_cases h1 : t < d.2
  · simp only [h1, ↓reduceIte]
  by_cases h2 : d.2 = 0
  · simp only [h2, ↓reduceIte]
  obtain ⟨x, hx⟩ := hR h1 h2 hmin
  have hx' : ∃ x : ℝ, stRecR s₂ < x ∧ lHit (stChart s₂) t d x := ⟨x, (hR' x).1 hx⟩
  simp only [h1, h2, show ∃ x : ℝ, stRecR s₁ < x ∧ lHit (stChart s₁) t d x from ⟨x, hx⟩, hx', ↓reduceIte]

theorem ChartEqH.loewner {c c' : Chart} (h : ChartEqH c c') {W : ℝ → ℝ} (hW : Continuous W) (hW0 : W 0 = 0)
    {T : ℝ} (hT : 0 ≤ T) : ChartEqH (c.loewner W T) (c'.loewner W T) := by
  refine ⟨by rw [Chart.loewner, Chart.loewner, h.1], ?_, fun w hw => ?_⟩
  · show (fun z => (QuantumZipper.logDerivFwd W T (c.1 z)).im + c.2.2 z) =
      fun z => (QuantumZipper.logDerivFwd W T (c'.1 z)).im + c'.2.2 z
    rw [h.1, h.2.1]
  · exact h.2.2 (QuantumZipper.RS.fwdMapInv_mem_H hW hW0 hT hw)

theorem launchEqH_update {f g : ℕ → Option (Chart × ℝ)} (hfg : ∀ k, k ≠ 0 → LaunchEqH (f k) (g k)) (j : ℕ)
    {c c' : Chart} (hc : ChartEqH c c') (θ : ℝ) :
    ∀ k, k ≠ 0 → LaunchEqH (Function.update f j (some (c, θ)) k) (Function.update g j (some (c', θ)) k) := by
  intro k hk
  by_cases hkj : k = j
  · subst hkj; simp only [Function.update_self]; exact ⟨hc, rfl⟩
  · simp only [Function.update_of_ne hkj]; exact hfg k hk

/-- **A good launch ending on the right preserves the restart relation.** -/
theorem RestartRel.launch (h : RestartRel s₁ s₂) (k : ℕ) {d : (ℝ≥0 → ℝ) × ℝ≥0∞} (θ : ℝ) (t : ℝ≥0∞)
    (hreg : IsRegularDriver d) (hg : min t d.2 ≠ ⊤ → LocalExt.IsDrvGood (recHist (recOf t d)))
    (hR : RightExit s₁ t d) :
    RestartRel (ExplState.launch s₁ k d θ t) (ExplState.launch s₂ k d θ t) := by
  obtain ⟨c1, c2, c3, c4⟩ := launch_components s₁ k d θ t
  obtain ⟨e1, e2, e3, e4⟩ := launch_components s₂ k d θ t
  obtain ⟨⟨p₁, p₂, L₁, L₂, hp₁, hp₂, hL⟩, ⟨a₁, a₂, M, ha₁, ha₂⟩, hret, hlau, hch, hst, hpt, hang, hrec⟩ := h
  have h' : RestartRel s₁ s₂ := ⟨⟨p₁, p₂, L₁, L₂, hp₁, hp₂, hL⟩, ⟨a₁, a₂, M, ha₁, ha₂⟩, hret, hlau, hch, hst, hpt,
    hang, hrec⟩
  refine ⟨⟨p₁, p₂, L₁ ++ [(stChart s₁, fun r : ℝ≥0 => d.1 (min (r : ℝ≥0∞) (min t d.2)).toNNReal, min t d.2)],
      L₂ ++ [(stChart s₂, fun r : ℝ≥0 => d.1 (min (r : ℝ≥0∞) (min t d.2)).toNNReal, min t d.2)],
      by rw [c1, hp₁]; rfl, by rw [e1, hp₂]; rfl,
      List.rel_append hL (List.Forall₂.cons ⟨hch, rfl, (stopDrv_good t hreg hg).1,
        by simpa [stopDrv_def] using (stopDrv_good t hreg hg).2⟩ List.Forall₂.nil)⟩,
      ⟨a₁, a₂, M, by rw [c2, ha₁], by rw [e2, ha₂]⟩,
      by rw [c3, e3, hret], by rw [c4, e4]; exact launchEqH_update hlau k hch θ, ?_, ?_, ?_, ?_, ?_⟩
  all_goals by_cases hF : min t d.2 = ⊤
  · rw [(launch_eq_of_top _ k d θ t hF).1, (launch_eq_of_top _ k d θ t hF).1]; exact hch
  · rw [(launch_eq_of_ne_top _ k d θ t hF).1, (launch_eq_of_ne_top _ k d θ t hF).1]
    have hc := recDrv_eq_stopDrv hreg (hg hF)
    have hW : Continuous (stopDrv t d) := hc ▸ continuous_recDrv t d
    exact hch.loewner hW (stopDrv_zero hreg t) (stopTime_nonneg t d)
  · rw [(launch_eq_of_top _ k d θ t hF).2.2.2.2.1, (launch_eq_of_top _ k d θ t hF).2.2.2.2.1]
  · rw [(launch_eq_of_ne_top _ k d θ t hF).2.2.2.2.1, (launch_eq_of_ne_top _ k d θ t hF).2.2.2.2.1,
      h'.status_launch t d hR hF]
  · rw [(launch_eq_of_top _ k d θ t hF).2.2.2.2.2, (launch_eq_of_top _ k d θ t hF).2.2.2.2.2]; exact hpt
  · rw [(launch_eq_of_ne_top _ k d θ t hF).2.2.2.2.2, (launch_eq_of_ne_top _ k d θ t hF).2.2.2.2.2,
      h'.pt_launch t d hR hF]
  · rw [(launch_eq_of_top _ k d θ t hF).2.1, (launch_eq_of_top _ k d θ t hF).2.1]
  · rw [(launch_eq_of_ne_top _ k d θ t hF).2.1, (launch_eq_of_ne_top _ k d θ t hF).2.1]
  · rw [(launch_eq_of_top _ k d θ t hF).2.2.1, (launch_eq_of_top _ k d θ t hF).2.2.1]; exact hrec
  · rw [(launch_eq_of_ne_top _ k d θ t hF).2.2.1, (launch_eq_of_ne_top _ k d θ t hF).2.2.1, h'.recR_launch]

theorem heights_congr {κ : ℝ} {b : ℝ → ℝ} (h : RestartRel s₁ s₂) :
    ExplState.heights κ b s₁ = ExplState.heights κ b s₂ := by
  rw [heights_eq, heights_eq, h.2.2.2.2.2.1, h.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2.1]

/-- **A flow step whose launch (if any) is good and ends on the right preserves the restart relation.** -/
theorem RestartRel.flowStep {κ : ℝ} {b : ℝ → ℝ} (h : RestartRel s₁ s₂) (gw2 : Bool) (k : ℕ)
    {d : (ℝ≥0 → ℝ) × ℝ≥0∞} (θ : ℝ) (t : ℝ≥0∞) (hreg : IsRegularDriver d)
    (hg : ExplState.flowStep κ b gw2 s₁ k d θ t = ExplState.launch s₁ k d θ t →
      (min t d.2 ≠ ⊤ → LocalExt.IsDrvGood (recHist (recOf t d))) ∧ RightExit s₁ t d) :
    RestartRel (ExplState.flowStep κ b gw2 s₁ k d θ t) (ExplState.flowStep κ b gw2 s₂ k d θ t) := by
  rw [flowStep_eq_cases] at hg
  rw [flowStep_eq_cases, flowStep_eq_cases, ← h.2.2.2.2.2.1, ← heights_congr (κ := κ) (b := b) h]
  split_ifs with h1 h2 h3 h4
  · obtain ⟨hg1, hg2⟩ := hg (by simp only [h1, ↓reduceIte])
    exact h.launch k θ t hreg hg1 hg2
  · exact h
  · exact h.setDead
  · obtain ⟨hg1, hg2⟩ := hg (by simp only [h1, h2, h3, h4, ↓reduceIte, Bool.false_eq_true])
    exact h.launch k θ t hreg hg1 hg2
  · exact h

end Ops

/-! ### Physical sets -/

/-- **Related pieces have the same physical points.** -/
theorem tipSet_eq_of_pieceEqH {p q : Chart × (ℝ≥0 → ℝ) × ℝ≥0∞} (h : PieceEqH p q) :
    p.1.tipSet p.2.1 p.2.2 = q.1.tipSet q.2.1 q.2.2 := by
  obtain ⟨hc, he, hcont, h0⟩ := h
  rw [← he]
  ext z
  simp only [Chart.tipSet, Set.mem_ofPred_eq]
  refine exists_congr fun t => and_congr_right fun _ => ?_
  have h0' : (fun r : ℝ => p.2.1 r.toNNReal) 0 = 0 := by simpa using h0
  have hev : (fun y : ℝ => p.1.2.1 (fwdMapInv (fun r : ℝ => p.2.1 r.toNNReal) t (y * I))) =ᶠ[𝓝[>] 0]
      fun y : ℝ => q.1.2.1 (fwdMapInv (fun r : ℝ => p.2.1 r.toNNReal) t (y * I)) := by
    filter_upwards [self_mem_nhdsWithin] with y (hy : 0 < y)
    have hyH : (y : ℂ) * I ∈ H := by
      show 0 < ((y : ℂ) * I).im
      simpa using hy
    exact hc.2.2 (QuantumZipper.RS.fwdMapInv_mem_H hcont h0' (NNReal.coe_nonneg t) hyH)
  exact tendsto_congr' hev

/-- The physical points of a state with root `r` (`prefixPhysSet` reads the state after `k` instructions). -/
def statePhys (r : ℝ) (s : ExplState) : Set ℂ :=
  {(r : ℂ)} ∪ (⋃ p ∈ s.1, p.1.tipSet p.2.1 p.2.2) ∪ ⋃ a ∈ s.2.1, ((↑) : ℝ → ℂ) '' a

theorem prefixPhysSet_eq_statePhys (κ : ℝ) (b : ℝ → ℝ) (J : Finset ℝ) (spec : ExplSpec)
    (D : ℕ → (ℝ≥0 → ℝ) × ℝ≥0∞) (k : ℕ) :
    prefixPhysSet κ b J spec D k = statePhys spec.1 (ExplState.run κ b J spec D k) := rfl

theorem statePhys_cons (r : ℝ) {s : ExplState} {p : Chart × (ℝ≥0 → ℝ) × ℝ≥0∞} {L : List (Chart × (ℝ≥0 → ℝ) × ℝ≥0∞)}
    {a : Set ℝ} {M : List (Set ℝ)} (hp : s.1 = p :: L) (ha : s.2.1 = a :: M) :
    statePhys r s = ({(r : ℂ)} ∪ p.1.tipSet p.2.1 p.2.2 ∪ ((↑) : ℝ → ℂ) '' a) ∪
      ((⋃ q ∈ L, q.1.tipSet q.2.1 q.2.2) ∪ ⋃ a' ∈ M, ((↑) : ℝ → ℂ) '' a') := by
  unfold statePhys
  rw [hp, ha]
  simp only [List.mem_cons, Set.iUnion_iUnion_eq_or_left]
  ext z
  simp only [Set.mem_union]
  tauto

theorem biUnion_tipSet_eq_of_forall₂ {L₁ L₂ : List (Chart × (ℝ≥0 → ℝ) × ℝ≥0∞)} (h : List.Forall₂ PieceEqH L₁ L₂) :
    (⋃ q ∈ L₁, q.1.tipSet q.2.1 q.2.2) = ⋃ q ∈ L₂, q.1.tipSet q.2.1 q.2.2 := by
  induction h with
  | nil => rfl
  | cons hpq _ ih =>
    simp only [List.mem_cons, Set.iUnion_iUnion_eq_or_left]
    rw [tipSet_eq_of_pieceEqH hpq, ih]

/-- **Related states have the same physical points away from their first piece and first connector.** -/
theorem RestartRel.statePhys {s₁ s₂ : ExplState} (h : RestartRel s₁ s₂) (r₁ r₂ : ℝ) :
    ∃ (p₁ p₂ : Chart × (ℝ≥0 → ℝ) × ℝ≥0∞) (a₁ a₂ : Set ℝ) (R : Set ℂ),
      (∃ L₁, s₁.1 = p₁ :: L₁) ∧ (∃ L₂, s₂.1 = p₂ :: L₂) ∧ (∃ M, s₁.2.1 = a₁ :: M) ∧ (∃ M, s₂.2.1 = a₂ :: M) ∧
      Lf.statePhys r₁ s₁ = ({(r₁ : ℂ)} ∪ p₁.1.tipSet p₁.2.1 p₁.2.2 ∪ ((↑) : ℝ → ℂ) '' a₁) ∪ R ∧
      Lf.statePhys r₂ s₂ = ({(r₂ : ℂ)} ∪ p₂.1.tipSet p₂.2.1 p₂.2.2 ∪ ((↑) : ℝ → ℂ) '' a₂) ∪ R := by
  obtain ⟨⟨p₁, p₂, L₁, L₂, hp₁, hp₂, hL⟩, ⟨a₁, a₂, M, ha₁, ha₂⟩, -⟩ := h
  refine ⟨p₁, p₂, a₁, a₂, _, ⟨L₁, hp₁⟩, ⟨L₂, hp₂⟩, ⟨M, ha₁⟩, ⟨M, ha₂⟩, statePhys_cons r₁ hp₁ ha₁, ?_⟩
  rw [statePhys_cons r₂ hp₂ ha₂, biUnion_tipSet_eq_of_forall₂ hL]

end InteractingSLE.Theorem14.SB.Lf
