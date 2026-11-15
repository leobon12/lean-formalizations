/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.SB4RTrWalk1

/-!
# The physical set of a walk restarted on its forced arc

Packet PROVE-T14-SB4LEAF (ruling R104, the initial-arc version). For the two runs of `SB4RTrWalk1` (roots `x₁ ≤ x₂`
on the forced arc, first pieces of zero lifetime), at every instruction `L ≥ 2` the physical set of the first run is
the arc `[x₁, x₂]` together with the physical set of the restarted run (**`statePhys_restart`**), both when the arc
ends at an admissible jump (`RestartRel`) and when it runs to `∞`.

* `step_extends`, `run_extends`: runs only append pieces and connectors;
* `tipSet_zero_piece`: a zero-lifetime piece from `x` is the point `x`.
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

/-! ### Runs only append -/

/-- A state extends another: more pieces and connectors at the end. -/
def Extends (s s' : ExplState) : Prop := (∃ X, s'.1 = s.1 ++ X) ∧ ∃ Y, s'.2.1 = s.2.1 ++ Y

theorem Extends.refl (s : ExplState) : Extends s s := ⟨⟨[], by simp⟩, ⟨[], by simp⟩⟩

theorem Extends.trans {s s' s'' : ExplState} (h : Extends s s') (h' : Extends s' s'') : Extends s s'' := by
  obtain ⟨⟨X, hX⟩, ⟨Y, hY⟩⟩ := h
  obtain ⟨⟨X', hX'⟩, ⟨Y', hY'⟩⟩ := h'
  exact ⟨⟨X ++ X', by rw [hX', hX, List.append_assoc]⟩, ⟨Y ++ Y', by rw [hY', hY, List.append_assoc]⟩⟩

theorem extends_setDead (s : ExplState) : Extends s (Exist.StagedLaw.setDead s) := by
  obtain ⟨_, _, _, _, _, _, _, _, _, _⟩ := s; exact Extends.refl _

theorem extends_moveAlong (s : ExplState) (r : Bool) (x : ℝ) (am : Bool) : Extends s (ExplState.moveAlong s r x am) :=
  ⟨⟨[], by rw [(moveAlong_components s r x am).1, List.append_nil]⟩, ⟨_, (moveAlong_components s r x am).2.1⟩⟩

theorem extends_moveToEnd (s : ExplState) (r : Bool) : Extends s (ExplState.moveToEnd s r) := by
  obtain ⟨_, _, _, _, _, _, _, _, _, _⟩ := s
  exact ⟨⟨[], by simp [ExplState.moveToEnd]⟩, ⟨_, rfl⟩⟩

theorem extends_launch (s : ExplState) (k : ℕ) (d : (ℝ≥0 → ℝ) × ℝ≥0∞) (θ : ℝ) (t : ℝ≥0∞) :
    Extends s (ExplState.launch s k d θ t) :=
  ⟨⟨_, (launch_components s k d θ t).1⟩, ⟨[], by rw [(launch_components s k d θ t).2.1, List.append_nil]⟩⟩

theorem extends_step {κ : ℝ} {b : ℝ → ℝ} {J : Finset ℝ} (gw2 : Bool) (D : ℕ → (ℝ≥0 → ℝ) × ℝ≥0∞) (s : ExplState)
    (ik : Instr × ℕ) : Extends s (ExplState.step κ b J gw2 D s ik) := by
  obtain ⟨i, k⟩ := ik
  have hcont : ∀ vStop pref, Extends s (ExplState.contStep κ b J s vStop pref) := fun vStop pref => by
    rw [contStep_eq_byStatus]
    have hB : ∀ r, Extends s (contBranch κ b J s vStop r) := fun r =>
      contBranch_congr (s₁ := s) (s₂ := s) (P := fun x _ => Extends s x) κ b J vStop r
        (fun r x am => extends_moveAlong s r x am) (fun r => extends_moveToEnd s r) rfl rfl
    rcases stStatus s with ⟨⟨⟩⟩ | ⟨⟨⟩⟩ | (_ | r) | ⟨r, (_ | _)⟩ | ⟨⟨⟩⟩ | ⟨⟨⟩⟩
    · exact extends_setDead s
    · exact extends_setDead s
    · simp only [contByStatus]
      rcases contDirNone κ b pref s with _ | (_ | _)
      · exact extends_setDead s
      · exact hB false
      · exact hB true
    · exact hB r
    · exact hB r
    · exact Extends.refl s
    · exact Extends.refl s
    · exact extends_setDead s
  rcases i with ⟨θ, t⟩ | pref | ⟨w, pref⟩
  · show Extends s (ExplState.flowStep κ b gw2 s k (D k) θ t)
    rw [flowStep_eq_cases]
    split_ifs
    · exact extends_launch s k _ θ t
    · exact Extends.refl s
    · exact extends_setDead s
    · exact extends_launch s k _ θ t
    · exact Extends.refl s
  · exact hcont none pref
  · exact hcont (some w) pref

theorem run_extends {κ : ℝ} {b : ℝ → ℝ} {J : Finset ℝ} (spec : ExplSpec) (D : ℕ → (ℝ≥0 → ℝ) × ℝ≥0∞) {n : ℕ} :
    ∀ k, n ≤ k → Extends (ExplState.run κ b J spec D n) (ExplState.run κ b J spec D k) := by
  intro k hk
  induction k, hk using Nat.le_induction with
  | base => exact Extends.refl _
  | succ k _ ih =>
    refine ih.trans ?_
    rw [run_succ]
    rcases spec.2.2[k]? with _ | i
    · exact Extends.refl _
    · exact extends_step spec.2.1 D _ (i, k)

/-! ### The zero-lifetime piece -/

/-- **A zero-lifetime piece from `x` is the point `x`.** -/
theorem tipSet_zero_piece (x : ℝ) : (Chart.id.recenter x).tipSet (fun _ => 0) 0 = {(x : ℂ)} := by
  ext z
  simp only [Chart.tipSet, Set.mem_ofPred_eq, Set.mem_singleton_iff]
  have hf : ∀ y : ℝ, 0 < y → (Chart.id.recenter x).2.1 (fwdMapInv (fun r : ℝ => (fun _ : ℝ≥0 => (0 : ℝ)) r.toNNReal)
      ((0 : ℝ≥0) : ℝ) ((y : ℂ) * I)) = (y : ℂ) * I + x := by
    intro y hy
    have hyH : (y : ℂ) * I ∈ H := by show 0 < ((y : ℂ) * I).im; simpa using hy
    have := GW2aCont.loewner_zero_inv (c := Chart.id.recenter x) (W := fun _ : ℝ => (0 : ℝ)) continuous_const rfl hyH
    rw [NNReal.coe_zero]
    exact this
  have hlim : Tendsto (fun y : ℝ => (Chart.id.recenter x).2.1 (fwdMapInv (fun r : ℝ =>
      (fun _ : ℝ≥0 => (0 : ℝ)) r.toNNReal) ((0 : ℝ≥0) : ℝ) ((y : ℂ) * I))) (𝓝[>] 0) (𝓝 (x : ℂ)) := by
    have h1 : Tendsto (fun y : ℝ => (y : ℂ) * I + x) (𝓝[>] 0) (𝓝 (x : ℂ)) := by
      have : Tendsto (fun y : ℝ => (y : ℂ) * I + x) (𝓝 0) (𝓝 ((((0 : ℝ) : ℂ)) * I + x)) :=
        ((Complex.continuous_ofReal.mul continuous_const).add continuous_const).tendsto 0
      simpa using this.mono_left nhdsWithin_le_nhds
    exact h1.congr' (eventually_nhdsWithin_of_forall fun y hy => (hf y hy).symm)
  constructor
  · rintro ⟨t, ht, hz⟩
    have ht0 : t = 0 := by
      have := ENNReal.coe_le_coe.1 (le_trans ht (le_of_eq rfl : (0 : ℝ≥0∞) ≤ 0))
      exact le_antisymm this bot_le
    subst ht0
    exact tendsto_nhds_unique hz hlim
  · rintro rfl
    exact ⟨0, le_rfl, hlim⟩

/-! ### The physical set -/

theorem statePhys_single (r : ℝ) {s : ExplState} {p : Chart × (ℝ≥0 → ℝ) × ℝ≥0∞} {a : Set ℝ} (hp : s.1 = [p])
    (ha : s.2.1 = [a]) : statePhys r s = {(r : ℂ)} ∪ p.1.tipSet p.2.1 p.2.2 ∪ ((↑) : ℝ → ℂ) '' a := by
  unfold statePhys
  rw [hp, ha]
  simp

theorem head_eq_of_extends {α : Type*} {l X : List α} {p q : α} {L : List α} (hl : l = [q]) (h : p :: L = l ++ X) :
    p = q := by
  rw [hl] at h
  exact (List.cons.inj h).1

section Restart

variable {κ : ℝ} {B : ℝ → ℝ} {JB : Finset ℝ} (prog : List Instr) (h0 : prog[0]? = some (.inl (-(Real.pi / 2), ⊤)))
  (h1 : prog[1]? = some (.inr (.inl true))) {D D' : ℕ → (ℝ≥0 → ℝ) × ℝ≥0∞}

include h0 h1 in
/-- **The physical set of the walk is the arc together with the walk restarted on it.** -/
theorem statePhys_restart {x₁ x₂ : ℝ} (h12 : x₁ ≤ x₂) {d d' : (ℝ≥0 → ℝ) × ℝ≥0∞} (hD : D 0 = d) (hD' : D' 0 = d')
    (hreg : IsRegularDriver d) (hreg' : IsRegularDriver d') (hz : d.2 = 0) (hz' : d'.2 = 0)
    (hlow₁ : rightLim B x₁ - Real.pi / 2 * chiC κ ≤ -sleLambda κ)
    (hlow₂ : rightLim B x₂ - Real.pi / 2 * chiC κ ≤ -sleLambda κ)
    (hmid : ∀ y ∈ jumpSet B JB, x₁ < y → y ≤ x₂ → ¬ -sleLambda κ < rightLim B y + -(Real.pi / 2) * chiC κ)
    (hregD : ∀ j, IsRegularDriver (D j)) (hDD : ∀ j, 2 ≤ j → D' j = D j)
    (hstep : ∀ j, 2 ≤ j → ∀ θ t, (x₁, false, prog).2.2[j]? = some (.inl (θ, t)) →
      ExplState.flowStep κ B false (ExplState.run κ B JB (x₁, false, prog) D j) j (D j) θ t =
        ExplState.launch (ExplState.run κ B JB (x₁, false, prog) D j) j (D j) θ t →
      (min t (D j).2 ≠ ⊤ → LocalExt.IsDrvGood (recHist (recOf t (D j)))) ∧
        RightExit (ExplState.run κ B JB (x₁, false, prog) D j) t (D j))
    (L : ℕ) (hL : 2 ≤ L) :
    statePhys x₁ (ExplState.run κ B JB (x₁, false, prog) D L) =
      ((↑) : ℝ → ℂ) '' Icc x₁ x₂ ∪ statePhys x₂ (ExplState.run κ B JB (x₂, false, prog) D' L) := by
  obtain ⟨p1, a1, -, -⟩ := launch_init_zero_components x₁ hreg hz
  obtain ⟨p2, a2, -, -⟩ := launch_init_zero_components x₂ hreg' hz'
  have hpt₁ := (launch_init_zero x₁ hreg hz (-(Real.pi / 2))).2.1
  have hpt₂ := (launch_init_zero x₂ hreg' hz' (-(Real.pi / 2))).2.1
  have hI : ∀ y : ℝ, x₁ ≤ y → (({(x₁ : ℂ)} ∪ {(x₁ : ℂ)} ∪ ((↑) : ℝ → ℂ) '' Icc x₁ y) : Set ℂ) =
      ((↑) : ℝ → ℂ) '' Icc x₁ y := fun y hy => by
    have hm : (x₁ : ℂ) ∈ ((↑) : ℝ → ℂ) '' Icc x₁ y := ⟨x₁, ⟨le_rfl, hy⟩, rfl⟩
    rw [Set.union_self, Set.union_eq_right.2 (Set.singleton_subset_iff.2 hm)]
  by_cases hC : (walkFilter κ B JB x₂).Nonempty
  · have hF := walkFilter_eq (κ := κ) (B := B) (JB := JB) h12 hmid
    have hC₁ : (walkFilter κ B JB x₁).Nonempty := hF ▸ hC
    set x := (walkFilter κ B JB x₂).min' hC with hx
    have hxpos : x₂ < x := (Finset.mem_filter.1 (Finset.min'_mem _ hC)).2.1
    have hx₁ : (walkFilter κ B JB x₁).min' hC₁ = x := by simp only [hx, hF]
    have e2A := run_two_moveAlong prog h0 h1 x₁ hD hreg hz hlow₁ hC₁
    have e2B := run_two_moveAlong prog h0 h1 x₂ hD' hreg' hz' hlow₂ hC
    rw [hx₁] at e2A
    have hrel := restartRel_run (spec₁ := (x₁, false, prog)) (spec₂ := (x₂, false, prog)) rfl rfl hregD
      (n := 2) hDD (restartRel_two prog h0 h1 h12 hD hD' hreg hreg' hz hz' hlow₁ hlow₂ hmid hC) hstep L hL
    obtain ⟨q₁, q₂, b₁, b₂, R, ⟨L₁, hq₁⟩, ⟨L₂, hq₂⟩, ⟨M₁, hb₁⟩, ⟨M₂, hb₂⟩, e₁, e₂⟩ := hrel.statePhys x₁ x₂
    obtain ⟨⟨X₁, hX₁⟩, ⟨Y₁, hY₁⟩⟩ := run_extends (κ := κ) (b := B) (J := JB) (x₁, false, prog) D L hL
    obtain ⟨⟨X₂, hX₂⟩, ⟨Y₂, hY₂⟩⟩ := run_extends (κ := κ) (b := B) (J := JB) (x₂, false, prog) D' L hL
    have hpA : (ExplState.run κ B JB (x₁, false, prog) D 2).1 = [(Chart.id.recenter x₁, (fun _ => (0 : ℝ)),
        (0 : ℝ≥0∞))] := by rw [e2A, (moveAlong_components _ _ _ _).1, p1]
    have hpB : (ExplState.run κ B JB (x₂, false, prog) D' 2).1 = [(Chart.id.recenter x₂, (fun _ => (0 : ℝ)),
        (0 : ℝ≥0∞))] := by rw [e2B, (moveAlong_components _ _ _ _).1, p2]
    have haA : (ExplState.run κ B JB (x₁, false, prog) D 2).2.1 = [Icc x₁ x] := by
      rw [e2A, (moveAlong_components _ _ _ _).2.1, a1, hpt₁]; rfl
    have haB : (ExplState.run κ B JB (x₂, false, prog) D' 2).2.1 = [Icc x₂ x] := by
      rw [e2B, (moveAlong_components _ _ _ _).2.1, a2, hpt₂]; rfl
    have hq₁' := head_eq_of_extends hpA (hq₁ ▸ hX₁)
    have hq₂' := head_eq_of_extends hpB (hq₂ ▸ hX₂)
    have hb₁' := head_eq_of_extends haA (hb₁ ▸ hY₁)
    have hb₂' := head_eq_of_extends haB (hb₂ ▸ hY₂)
    rw [e₁, e₂, hq₁', hq₂', hb₁', hb₂']
    simp only [tipSet_zero_piece]
    rw [hI x (by linarith), Set.union_self]
    have hsplit : ((↑) : ℝ → ℂ) '' Icc x₁ x = ((↑) : ℝ → ℂ) '' Icc x₁ x₂ ∪ ((↑) : ℝ → ℂ) '' Icc x₂ x := by
      rw [← Set.image_union, Set.Icc_union_Icc_eq_Icc h12 hxpos.le]
    have hm : (x₂ : ℂ) ∈ ((↑) : ℝ → ℂ) '' Icc x₂ x := ⟨x₂, ⟨le_rfl, hxpos.le⟩, rfl⟩
    rw [hsplit, Set.union_eq_right.2 (Set.singleton_subset_iff.2 hm), Set.union_assoc]
  · have hF := walkFilter_eq (κ := κ) (B := B) (JB := JB) h12 hmid
    have hC₁ : ¬ (walkFilter κ B JB x₁).Nonempty := hF ▸ hC
    have e2A := run_two_done prog h0 h1 x₁ hD hreg hz hlow₁ hC₁
    have e2B := run_two_done prog h0 h1 x₂ hD' hreg' hz' hlow₂ hC
    have hdA : stStatus (ExplState.run κ B JB (x₁, false, prog) D 2) = stDone := by
      rw [e2A]; obtain ⟨_, _, _, _, _, _, _, _, _, _⟩ := ExplState.launch (ExplState.init x₁) 0 d (-(Real.pi / 2)) ⊤
      rfl
    have hdB : stStatus (ExplState.run κ B JB (x₂, false, prog) D' 2) = stDone := by
      rw [e2B]; obtain ⟨_, _, _, _, _, _, _, _, _, _⟩ := ExplState.launch (ExplState.init x₂) 0 d' (-(Real.pi / 2)) ⊤
      rfl
    rw [run_eq_of_done _ _ hdA L hL, run_eq_of_done _ _ hdB L hL, e2A, e2B]
    have hmE : ∀ (s : ExplState) (r : ℝ), s.1 = [(Chart.id.recenter r, (fun _ => (0 : ℝ)), (0 : ℝ≥0∞))] →
        s.2.1 = [] → stPt s = r →
        statePhys r (ExplState.moveToEnd s true) = {(r : ℂ)} ∪ {(r : ℂ)} ∪ ((↑) : ℝ → ℂ) '' Ici r := by
      intro s r hp ha hpt
      have h1' : (ExplState.moveToEnd s true).1 = [(Chart.id.recenter r, (fun _ => (0 : ℝ)), (0 : ℝ≥0∞))] := by
        obtain ⟨_, _, _, _, _, _, _, _, _, _⟩ := s; exact hp
      have h2' : (ExplState.moveToEnd s true).2.1 = [Ici r] := by
        obtain ⟨_, _, _, _, _, _, _, _, _, _⟩ := s
        simp only [stPt] at ha hpt
        show _ ++ _ = _
        simp [ha, hpt]
      rw [statePhys_single _ h1' h2', tipSet_zero_piece]
    rw [hmE _ x₁ p1 a1 hpt₁, hmE _ x₂ p2 a2 hpt₂, Set.union_self, Set.union_self]
    have hsplit : ((↑) : ℝ → ℂ) '' Ici x₁ = ((↑) : ℝ → ℂ) '' Icc x₁ x₂ ∪ ((↑) : ℝ → ℂ) '' Ici x₂ := by
      rw [← Set.image_union, Set.Icc_union_Ici_eq_Ici h12]
    have hm₁ : (x₁ : ℂ) ∈ ((↑) : ℝ → ℂ) '' Ici x₁ := ⟨x₁, Set.mem_Ici.2 le_rfl, rfl⟩
    have hm₂ : (x₂ : ℂ) ∈ ((↑) : ℝ → ℂ) '' Ici x₂ := ⟨x₂, Set.mem_Ici.2 le_rfl, rfl⟩
    rw [Set.union_eq_right.2 (Set.singleton_subset_iff.2 hm₁), Set.union_eq_right.2 (Set.singleton_subset_iff.2 hm₂),
      hsplit]

end Restart

end InteractingSLE.Theorem14.SB.Lf
