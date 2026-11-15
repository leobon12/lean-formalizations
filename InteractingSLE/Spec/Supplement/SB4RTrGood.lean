/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.SB4RTrStep
import InteractingSLE.Spec.Exist.StagedLaw4

/-!
# Good chart profiles along runs, and the almost-sure translation of staged runs

Packet PROVE-T14-SB4LEAF (ruling R104, the initial-arc version). The translation of a run (`run_trState`) needs
every launch to have bounded swallowed real sets (`RecBdd`). This holds as soon as the state has a real chart with
good profiles beyond both records (`GoodProf`: `IsRealChart` and `IsGoodProfile` of `StagedLaw2State`) and the
launched driver is good (`LocalExt.IsDrvGood` of its record). `GoodProf` is an invariant of the machine along good
launches:

* `goodProf_init`, `GoodProf.setDead`, `GoodProf.moveToEnd`, `GoodProf.moveAlong`, `GoodProf.launch`,
  `GoodProf.rBranch`, `GoodProf.lBranch`, `GoodProf.contStep`, `GoodProf.flowStep`, **`goodProf_run`**;
* **`GoodProf.recBdd`** (`StagedLaw.bddAbove_dead` on both sides);
* **`ae_launch_good`**: a `StagedPiecesRegular` family with drivers regular at every sample launches only good
  drivers almost surely; **`ae_run_trState`**: its runs translate almost surely.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Complex Set Filter Topology
open scoped NNReal ENNReal
open QuantumZipper (chiC H Hbar IsForwardSol fwdMap)

namespace InteractingSLE.Theorem14.SB.Lf

open Exist.Staged Exist.StagedLaw FlowDilate
open PiecewiseConstantBoundaryData (rightLim leftLim jumpSet)

/-- **A good state**: real chart, good profiles beyond both records. -/
def GoodProf (s : ExplState) : Prop := IsRealChart (stChart s) ∧ IsGoodProfile s

theorem goodProf_init (x₀ : ℝ) : GoodProf (ExplState.init x₀) := by
  refine ⟨fun x => ?_, ?_, ?_⟩
  · simp [ExplState.init, Chart.recenter, Chart.id]
  · refine (rightGood_add_const x₀ (-x₀)).congr fun x _ => ?_
    simp [ExplState.init, Chart.recenter, Chart.id, rProf, sub_eq_add_neg]
  · refine (rightGood_add_const (-x₀) x₀).congr fun x _ => ?_
    simp [ExplState.init, Chart.recenter, Chart.id, lProf, add_comm]

theorem GoodProf.setDead {s : ExplState} (h : GoodProf s) : GoodProf (setDead s) := by
  obtain ⟨_, _, _, _, _, _, _, _, _, _⟩ := s; exact h

theorem GoodProf.moveToEnd {s : ExplState} (h : GoodProf s) (right : Bool) :
    GoodProf (ExplState.moveToEnd s right) := by
  obtain ⟨_, _, _, _, _, _, _, _, _, _⟩ := s; exact h

theorem GoodProf.moveAlong {s : ExplState} (h : GoodProf s) (right : Bool) (x : ℝ) (am : Bool) :
    GoodProf (ExplState.moveAlong s right x am) := by
  obtain ⟨hr, hgR, hgL⟩ := h
  refine ⟨fun y => ?_, ?_, ?_⟩
  · show ((stChart s).1 y - (((stChart s).1 x).re : ℂ)).im = 0
    rw [Complex.sub_im, hr y, Complex.ofReal_im, sub_zero]
  · have h1 := hgR.sub_const ((stChart s).1 x).re
    obtain ⟨_, _, _, _, _, _, _, _, _, _⟩ := s
    cases right
    · exact h1.congr fun y _ => by simp [rProf, ExplState.moveAlong, Chart.recenter]
    · exact (h1.mono_of_le (le_max_left _ _)).congr fun y _ => by
        simp [rProf, ExplState.moveAlong, Chart.recenter]
  · have h1 := hgL.sub_const (-((stChart s).1 x).re)
    obtain ⟨_, _, _, _, _, _, _, _, _, _⟩ := s
    cases right
    · refine (h1.mono_of_le ?_).congr fun y _ => ?_
      · exact neg_le_neg (min_le_left _ _)
      · simp only [lProf, ExplState.moveAlong, Chart.recenter, Complex.sub_re, Complex.ofReal_re]
        ring
    · refine h1.congr fun y _ => ?_
      simp only [lProf, ExplState.moveAlong, Chart.recenter, Complex.sub_re, Complex.ofReal_re]
      ring

/-- **A good launch keeps the state good** (`StagedLaw.rightGood_comp` on both sides). -/
theorem GoodProf.launch {s : ExplState} (h : GoodProf s) (k : ℕ) {d : (ℝ≥0 → ℝ) × ℝ≥0∞} (θ : ℝ) (t : ℝ≥0∞)
    (hreg : IsRegularDriver d) (hg : min t d.2 ≠ ⊤ → LocalExt.IsDrvGood (recHist (recOf t d))) :
    GoodProf (ExplState.launch s k d θ t) := by
  obtain ⟨hr, hgR, hgL⟩ := h
  by_cases hF : min t d.2 = ⊤
  · obtain ⟨hc', -, hR', hL', -, -⟩ := launch_eq_of_top s k d θ t hF
    refine ⟨by rw [hc']; exact hr, ?_⟩
    unfold IsGoodProfile
    rw [hc', hR', hL']
    exact ⟨hgR, hgL⟩
  · obtain ⟨hc', -, hR', hL', -, -⟩ := launch_eq_of_ne_top s k d θ t hF
    have hflow := isRealFlow_stop hreg (hg hF)
    refine ⟨fun x => ?_, ?_⟩
    · rw [hc']
      show (fwdMap (stopDrv t d) (stopTime t d) ((stChart s).1 x)).im = 0
      rw [hr.eq_ofReal x]
      exact im_fwdMap_ofReal _ (stopTime_nonneg t d) _
    unfold IsGoodProfile
    rw [hR', hL', lRecR_eq_newRec hr, lRecL_eq_newRec hr, neg_neg]
    refine ⟨(rightGood_comp hgR hflow.1).congr fun x _ => ?_, (rightGood_comp hgL hflow.2).congr fun x _ => ?_⟩
    · show _ = ((stChart (ExplState.launch s k d θ t)).1 x).re
      rw [hc']
      show _ = (fwdMap (stopDrv t d) (stopTime t d) ((stChart s).1 x)).re
      rw [hr.eq_ofReal x]
    · show _ = -((stChart (ExplState.launch s k d θ t)).1 ((-x : ℝ) : ℂ)).re
      rw [hc']
      show _ = -(fwdMap (stopDrv t d) (stopTime t d) ((stChart s).1 ((-x : ℝ) : ℂ))).re
      rw [hr.eq_ofReal (-x)]
      simp only [lProf, rProf, neg_neg]

/-- **A good state launching a good driver has bounded swallowed real sets.** -/
theorem GoodProf.recBdd {s : ExplState} (h : GoodProf s) {d : (ℝ≥0 → ℝ) × ℝ≥0∞} (t : ℝ≥0∞)
    (hreg : IsRegularDriver d) (hg : LocalExt.IsDrvGood (recHist (recOf t d))) : RecBdd s t d := by
  obtain ⟨hr, hgR, hgL⟩ := h
  have hflow := isRealFlow_stop hreg hg
  have hA : ∀ x : ℝ, lAlive (stChart s) t d x ↔
      ∃ u, IsForwardSol (stopDrv t d) ((rProf (stChart s) x : ℝ) : ℂ) (stopTime t d) u := fun x => by
    rw [lAlive, hr.eq_ofReal x]
  refine ⟨?_, ?_⟩
  · have hB := bddAbove_dead hgR hflow.1
    refine hB.mono fun x hx => ?_
    rcases hx with rfl | ⟨h1, h2⟩
    · exact Or.inl rfl
    · exact Or.inr ⟨h1, by rwa [hA] at h2⟩
  · obtain ⟨B, hB⟩ := bddAbove_dead hgL hflow.2
    refine ⟨-B, fun x hx => ?_⟩
    have hmem : -x ∈ insert (-stRecL s) {y : ℝ | -stRecL s < y ∧
        ¬ (fun y => ∃ u, IsForwardSol (stopDrv t d) ((-y : ℝ) : ℂ) (stopTime t d) u) (lProf (stChart s) y)} := by
      rcases hx with rfl | ⟨h1, h2⟩
      · exact Or.inl rfl
      · refine Or.inr ⟨by linarith, ?_⟩
        rw [hA] at h2
        simpa only [lProf, rProf, neg_neg] using h2
    have := hB hmem
    linarith

/-! ### The boundary continuation keeps the state good -/

theorem GoodProf.rBranch {κ : ℝ} {b : ℝ → ℝ} {J : Finset ℝ} {s : ExplState} (h : GoodProf s) (vStop : Option ℝ) :
    GoodProf (GW2aConn.rBranch κ b J s vStop) := by
  unfold GW2aConn.rBranch
  split_ifs with hC
  · rcases vStop with _ | w
    · exact h.moveAlong _ _ _
    · simp only []
      split_ifs
      · exact h.moveAlong _ _ _
      · exact h.moveAlong _ _ _
  · rcases vStop with _ | w
    · exact h.moveToEnd _
    · simp only []
      split_ifs
      · exact h.moveAlong _ _ _
      · exact h.moveToEnd _

theorem GoodProf.lBranch {κ : ℝ} {b : ℝ → ℝ} {J : Finset ℝ} {s : ExplState} (h : GoodProf s) (vStop : Option ℝ) :
    GoodProf (GW2aConn.lBranch κ b J s vStop) := by
  unfold GW2aConn.lBranch
  split_ifs with hC
  · rcases vStop with _ | w
    · exact h.moveAlong _ _ _
    · simp only []
      split_ifs
      · exact h.moveAlong _ _ _
      · exact h.moveAlong _ _ _
  · rcases vStop with _ | w
    · exact h.moveToEnd _
    · simp only []
      split_ifs
      · exact h.moveAlong _ _ _
      · exact h.moveToEnd _

theorem GoodProf.contStep {κ : ℝ} {b : ℝ → ℝ} {J : Finset ℝ} {s : ExplState} (h : GoodProf s) (vStop : Option ℝ)
    (pref : Bool) : GoodProf (ExplState.contStep κ b J s vStop pref) := by
  obtain ⟨pieces, arcs, retained, launches, chart, status, pt, θ, recR, recL⟩ := s
  rcases status with ⟨⟨⟩⟩ | ⟨⟨⟩⟩ | (_ | (_ | _)) | ⟨(_ | _), (_ | _)⟩ | ⟨⟨⟩⟩ | ⟨⟨⟩⟩
  · exact h.setDead
  · exact h.setDead
  · set s₀ : ExplState := (pieces, arcs, retained, launches, chart, stThr none, pt, θ, recR, recL) with hs₀
    by_cases hR : rightLim b pt + θ * chiC κ ≤ -sleLambda κ <;>
    by_cases hL : sleLambda κ ≤ leftLim b pt + θ * chiC κ
    · cases pref
      · have e₁ : ExplState.contStep κ b J s₀ vStop false = GW2aConn.lBranch κ b J s₀ vStop := by
          simp only [hs₀, ExplState.contStep, hR, hL, and_self, ↓reduceIte]; rfl
        rw [e₁]; exact h.lBranch vStop
      · have e₁ : ExplState.contStep κ b J s₀ vStop true = GW2aConn.rBranch κ b J s₀ vStop := by
          simp only [hs₀, ExplState.contStep, hR, hL, and_self, ↓reduceIte]; rfl
        rw [e₁]; exact h.rBranch vStop
    · have e₁ : ExplState.contStep κ b J s₀ vStop pref = GW2aConn.rBranch κ b J s₀ vStop := by
        simp only [hs₀, ExplState.contStep, hR, hL, and_false, ↓reduceIte]; rfl
      rw [e₁]; exact h.rBranch vStop
    · have e₁ : ExplState.contStep κ b J s₀ vStop pref = GW2aConn.lBranch κ b J s₀ vStop := by
        simp only [hs₀, ExplState.contStep, hR, hL, false_and, ↓reduceIte]; rfl
      rw [e₁]; exact h.lBranch vStop
    · have e₁ : ExplState.contStep κ b J s₀ vStop pref = Exist.StagedLaw.setDead s₀ := by
        simp only [hs₀, ExplState.contStep, hR, hL, and_false, ↓reduceIte]; rfl
      rw [e₁]; exact h.setDead
  · exact h.lBranch (κ := κ) (b := b) (J := J) vStop
  · exact h.rBranch (κ := κ) (b := b) (J := J) vStop
  · exact h.lBranch (κ := κ) (b := b) (J := J) vStop
  · exact h
  · exact h.rBranch (κ := κ) (b := b) (J := J) vStop
  · exact h
  · exact h
  · exact h.setDead

theorem GoodProf.flowStep {κ : ℝ} {b : ℝ → ℝ} {s : ExplState} (h : GoodProf s) (gw2 : Bool) (k : ℕ)
    {d : (ℝ≥0 → ℝ) × ℝ≥0∞} (θ : ℝ) (t : ℝ≥0∞) (hreg : IsRegularDriver d)
    (hg : ExplState.flowStep κ b gw2 s k d θ t = ExplState.launch s k d θ t → min t d.2 ≠ ⊤ →
      LocalExt.IsDrvGood (recHist (recOf t d))) :
    GoodProf (ExplState.flowStep κ b gw2 s k d θ t) := by
  by_cases hl : ExplState.flowStep κ b gw2 s k d θ t = ExplState.launch s k d θ t
  · rw [hl]; exact h.launch k θ t hreg (hg hl)
  · rw [flowStep_eq_cases] at hl ⊢
    split_ifs at hl ⊢
    · exact absurd rfl hl
    · exact h
    · exact h.setDead
    · exact absurd rfl hl
    · exact h

/-- **Good launches keep every state of the run good.** -/
theorem goodProf_run {κ : ℝ} {b : ℝ → ℝ} {J : Finset ℝ} (spec : ExplSpec) (D : ℕ → (ℝ≥0 → ℝ) × ℝ≥0∞) (k : ℕ)
    (hreg : ∀ j, IsRegularDriver (D j))
    (hg : ∀ j < k, ∀ θ t, spec.2.2[j]? = some (.inl (θ, t)) →
      ExplState.flowStep κ b spec.2.1 (ExplState.run κ b J spec D j) j (D j) θ t =
        ExplState.launch (ExplState.run κ b J spec D j) j (D j) θ t →
      min t (D j).2 ≠ ⊤ → LocalExt.IsDrvGood (recHist (recOf t (D j)))) :
    GoodProf (ExplState.run κ b J spec D k) := by
  induction k with
  | zero => exact goodProf_init spec.1
  | succ k ih =>
    rw [run_succ]
    have ih' := ih fun j hj => hg j (Nat.lt_succ_of_lt hj)
    rcases hk : spec.2.2[k]? with _ | i
    · exact ih'
    · rcases i with ⟨θ, t⟩ | pref | ⟨w, pref⟩
      · exact ih'.flowStep spec.2.1 k θ t (hreg k) (hg k (Nat.lt_succ_self k) θ t hk)
      · exact ih'.contStep none pref
      · exact ih'.contStep (some w) pref

/-! ### Staged histories launch good drivers -/

theorem launches_of_flowStep_eq_launch {κ : ℝ} {b : ℝ → ℝ} {gw2 : Bool} {s : ExplState} {k : ℕ}
    {d : (ℝ≥0 → ℝ) × ℝ≥0∞} {θ : ℝ} {t : ℝ≥0∞}
    (h : ExplState.flowStep κ b gw2 s k d θ t = ExplState.launch s k d θ t) :
    (ExplState.flowStep κ b gw2 s k d θ t).2.2.2.1 k = some (stChart s, θ) := by
  rw [h, (launch_components s k d θ t).2.2.2, Function.update_self]

/-- **A `StagedPiecesRegular` family launches only good drivers**, almost surely. -/
theorem ae_launch_good {κ : ℝ} {b : ℝ → ℝ} {J : Finset ℝ} {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {spec : ExplSpec} {D : ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞} (hR : StagedPiecesRegular κ b J P spec D)
    (hreg : ∀ j ω, IsRegularDriver (D j ω)) :
    ∀ᵐ ω ∂P, ∀ j θ t, spec.2.2[j]? = some (.inl (θ, t)) →
      ExplState.flowStep κ b spec.2.1 (ExplState.run κ b J spec (fun i => D i ω) j) j (D j ω) θ t =
        ExplState.launch (ExplState.run κ b J spec (fun i => D i ω) j) j (D j ω) θ t →
      min t (D j ω).2 ≠ ⊤ → LocalExt.IsDrvGood (recHist (recOf t (D j ω))) := by
  filter_upwards [hR] with ω hω j θ t hj hl hfin
  have hl' : (ExplState.run κ b J spec (fun i => D i ω) (j + 1)).2.2.2.1 j =
      some (stChart (ExplState.run κ b J spec (fun i => D i ω) j), θ) := by
    rw [run_succ, hj]
    exact launches_of_flowStep_eq_launch hl
  obtain ⟨-, hc, -⟩ := hω j θ t _ hj hl'
  exact isDrvGood_of_continuousOn_le (hreg j ω) hfin hc

/-- **The runs of a `StagedPiecesRegular` family with everywhere regular drivers translate almost surely.** -/
theorem ae_run_trState {κ : ℝ} {b : ℝ → ℝ} {J : Finset ℝ} (hb : IsPiecewiseConstantBoundaryData b J) (v : ℝ)
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {spec : ExplSpec} {D : ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞}
    (hR : StagedPiecesRegular κ b J P spec D) (hreg : ∀ j ω, IsRegularDriver (D j ω)) :
    ∀ᵐ ω ∂P, ∀ k, ExplState.run κ (affData 1 (-v) b) (affJumps 1 (-v) J) (trSpec v spec) (fun i => D i ω) k =
      trState v (ExplState.run κ b J spec (fun i => D i ω) k) := by
  filter_upwards [ae_launch_good hR hreg] with ω hω k
  refine run_trState hb v spec _ k fun j hj θ t hjθ hl hfin => ?_
  have hgood := goodProf_run (κ := κ) (b := b) (J := J) spec (fun i => D i ω) j (fun i => hreg i ω)
    fun i _ θ' t' hi hl' hfin' => hω i θ' t' hi hl' hfin'
  exact hgood.recBdd t (hreg j ω) (hω j θ t hjθ hl hfin)

end InteractingSLE.Theorem14.SB.Lf
