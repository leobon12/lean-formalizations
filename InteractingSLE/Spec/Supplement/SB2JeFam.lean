/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.SB2JeCore6

/-!
# SB2(2) under the v6 rule: the per-sample rules from a family

Packet PROVE-SB2-LIFTSET (round 21). For a relative family `F` with GEOM2's v6 hypotheses (the zero driver on the
masked zero events, generation of the v4 stage curves on the v6 mask) and a sample `ω` of `Gd`:

* `rootRule6_of_fam`, `stageRule6_of_fam`: the per-sample rules `RootRule6`, `StageRule6` of `sample_core6`;
* `rootRule6_truncDrv`, `stageRule6_truncDrv`, `isRegularDriver_truncDrv`: the rules and the regularity pass to the
  family truncated at `N` (used for GEOM2's admissibility clause, where the family is known only below a stage);
* `recGoodAt_truncDrv`, `denseAt_truncDrv`: the recorded goodness and the dense readings of the truncated family;
* `cρ3_zero_eq`, `cρ3_of_ne_eq`: the v4 stage curves at one sample.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Filter Topology
open scoped NNReal ENNReal
open QuantumZipper (H Hbar)

namespace InteractingSLE.Theorem14.SB.Lk

open Supp9B Lx Lu Leaf FlowDilate Sec4 Exist Exist.Staged Exist.StagedLaw LuM GW1W GW1Bookkeep GW1P
open Sec7.PocketTraversal Sec7.Lemma71C

section Fam

variable {Ω : Type*} {κ θ : ℝ} {b₁ : ℝ → ℝ} {J₁ : Finset ℝ} {b₂ : ℝ → ℝ} {J₂ : Finset ℝ} {R : ℝ} {c : Chart}
  {m : ℝ} {D₁ : Ω → ℕ → Drv}

/-- The v4 stage curve at stage `0` and one sample: the root's curve in the initial chart. -/
theorem cρ3_zero_eq (F : ℕ → Ω → Drv) (ω : Ω) :
    cρ3 κ θ b₁ J₁ b₂ J₂ R c m D₁ 0 F ω = stCurvep c m
      (rootPt (wRun κ θ b₁ J₁ (D₁ ω) (relOff κ θ b₁ J₁ R (D₁ ω))) (D₁ ω (relOff κ θ b₁ J₁ R (D₁ ω))) R)
      (rootLife (wRun κ θ b₁ J₁ (D₁ ω) (relOff κ θ b₁ J₁ R (D₁ ω))) (D₁ ω (relOff κ θ b₁ J₁ R (D₁ ω))) R)
      (ExplState.init 0) := by
  show cΦ3 κ θ b₁ J₁ R c m D₁ 0 ω _ = _
  unfold cΦ3 stageShift rootPt rootLife
  simp only [↓reduceIte, zero_add]
  rfl

/-- The v4 stage curve at a stage `j ≠ 0` and one sample: the unshifted run-chart stage curve. -/
theorem cρ3_of_ne_eq {j : ℕ} (hj : j ≠ 0) (F : ℕ → Ω → Drv) (ω : Ω) :
    cρ3 κ θ b₁ J₁ b₂ J₂ R c m D₁ j F ω = stCurvep c m
      (pcPt (ExplState.run κ b₁ J₁ (boundaryWalkSpec b₁ J₁ θ true) (D₁ ω) (j + relOff κ θ b₁ J₁ R (D₁ ω)))
        (D₁ ω (j + relOff κ θ b₁ J₁ R (D₁ ω))))
      (D₁ ω (j + relOff κ θ b₁ J₁ R (D₁ ω))).2
      (ExplState.run κ b₂ J₂ (boundaryWalkSpec b₂ J₂ θ true) (fun i => F i ω) j) := by
  have hq : (fun t => pcPt (ExplState.run κ b₁ J₁ (boundaryWalkSpec b₁ J₁ θ true) (D₁ ω)
        (j + relOff κ θ b₁ J₁ R (D₁ ω))) (D₁ ω (j + relOff κ θ b₁ J₁ R (D₁ ω))) (0 + t)) =
      pcPt (ExplState.run κ b₁ J₁ (boundaryWalkSpec b₁ J₁ θ true) (D₁ ω) (j + relOff κ θ b₁ J₁ R (D₁ ω)))
        (D₁ ω (j + relOff κ θ b₁ J₁ R (D₁ ω))) :=
    funext fun t => by rw [zero_add]
  show cΦ3 κ θ b₁ J₁ R c m D₁ j ω _ = _
  unfold cΦ3 stageShift
  simp only [hj, ↓reduceIte, ENNReal.coe_zero, tsub_zero]
  rw [hq]

/-- **The root's rule at one sample from the family's v6 hypotheses at stage `0`.** -/
theorem rootRule6_of_fam {Gd : Set Ω} {F : ℕ → Ω → Drv} {ω : Ω} (hω : ω ∈ Gd)
    (hz : ω ∈ mZ Gd (cZ4 κ θ b₁ J₁ R D₁) 0 F → F 0 ω = zeroDrv)
    (hg : ω ∈ Nv.maskEv κ θ b₁ J₁ b₂ J₂ R c m D₁ Gd 0 F →
      (F 0 ω).2 = capLife (cρ3 κ θ b₁ J₁ b₂ J₂ R c m D₁ 0 F ω) ∧
      ∀ T < capLife (cρ3 κ θ b₁ J₁ b₂ J₂ R c m D₁ 0 F ω),
        IsGeneratingTrace (F 0 ω).1 T (capTrace (cρ3 κ θ b₁ J₁ b₂ J₂ R c m D₁ 0 F ω)))
    (hl0 : ¬ ZeroRoot κ θ b₁ J₁ R (D₁ ω) →
      (wRun κ θ b₁ J₁ (D₁ ω) (relOff κ θ b₁ J₁ R (D₁ ω) + 1)).2.2.2.1 (relOff κ θ b₁ J₁ R (D₁ ω)) ≠ none) :
    RootRule6 κ θ b₁ J₁ R c m (D₁ ω) (fun i => F i ω) := by
  refine ⟨fun h => hz (Or.inl ⟨(mem_cZ4_zero_iff κ θ b₁ J₁ R D₁ F ω).2 h, hω⟩), fun hZ hL hd => ?_⟩
  have hm : ω ∈ Nv.maskEv κ θ b₁ J₁ b₂ J₂ R c m D₁ Gd 0 F := by
    refine ⟨hω, fun h => ?_, (mem_launchEv_zero_iff ω).2 (hl0 hZ), fun i hi => absurd hi (Nat.not_lt_zero i),
      (mem_denseEv_zero_iff F ω).2 hd⟩
    rcases (mem_cZ4_zero_iff κ θ b₁ J₁ R D₁ F ω).1 h with h' | h'
    · exact hZ h'
    · exact hL h'
  obtain ⟨he, hgen⟩ := hg hm
  rw [cρ3_zero_eq] at he hgen
  exact ⟨he, hgen⟩

/-- **The later stages' rule at one sample from the family's v6 hypotheses below `N`.** -/
theorem stageRule6_of_fam {Gd : Set Ω} {F : ℕ → Ω → Drv} {ω : Ω} {N : ℕ} (hω : ω ∈ Gd)
    (hg : ∀ i < N, ω ∈ Nv.maskEv κ θ b₁ J₁ b₂ J₂ R c m D₁ Gd i F →
      (F i ω).2 = capLife (cρ3 κ θ b₁ J₁ b₂ J₂ R c m D₁ i F ω) ∧
      ∀ T < capLife (cρ3 κ θ b₁ J₁ b₂ J₂ R c m D₁ i F ω),
        IsGeneratingTrace (F i ω).1 T (capTrace (cρ3 κ θ b₁ J₁ b₂ J₂ R c m D₁ i F ω))) :
    StageRule6 κ θ b₁ J₁ b₂ J₂ c m (D₁ ω) (fun i => F i ω) (relOff κ θ b₁ J₁ R (D₁ ω)) N := by
  intro i h2 hiN hl hpos hrg hdn
  have hi0 : i ≠ 0 := by omega
  have hev : i % 2 = 0 := by
    have h1 := (GW1W.even_of_launches_walk hl).1
    have h2 := relOff_even κ θ b₁ J₁ R (D₁ ω)
    omega
  have hm : ω ∈ Nv.maskEv κ θ b₁ J₁ b₂ J₂ R c m D₁ Gd i F := by
    refine ⟨hω, fun h => ?_, hl, hrg, (mem_denseEv_iff_of_ne hi0 F ω).2 hdn⟩
    rcases (mem_cZ4_of_ne hi0 F ω).1 h with h' | h'
    · omega
    · exact hpos h'
  obtain ⟨he, hgen⟩ := hg i hiN hm
  rw [cρ3_of_ne_eq hi0] at he hgen
  exact ⟨he, hgen⟩

/-- A positive shifted start lifetime is a positive root lifetime. -/
theorem rootLife_ne_zero_of {D : ℕ → Drv} (hL : (D (relOff κ θ b₁ J₁ R D)).2 - shiftD κ θ b₁ J₁ R D 0 ≠ 0) :
    rootLife (wRun κ θ b₁ J₁ D (relOff κ θ b₁ J₁ R D)) (D (relOff κ θ b₁ J₁ R D)) R ≠ 0 := by
  rw [shiftD_zero_eq] at hL
  exact hL

end Fam

section Trunc

variable {κ θ : ℝ} {b₁ : ℝ → ℝ} {J₁ : Finset ℝ} {b₂ : ℝ → ℝ} {J₂ : Finset ℝ} {R : ℝ} {c : Chart} {m : ℝ}
  {D₁ D₂ : ℕ → Drv}

/-- The truncated family's recorded goodness is the family's below the truncation. -/
theorem recGoodAt_truncDrv {κ θ : ℝ} {b₂ : ℝ → ℝ} {J₂ : Finset ℝ} {D : ℕ → Drv} {j i : ℕ} (hij : i ≤ j)
    (h : RecGoodAt κ θ b₂ J₂ (truncDrv D j) i) : RecGoodAt κ θ b₂ J₂ D i := by
  intro i' hi' hl hfin
  have e1 := run_truncDrv (κ := κ) (b := b₂) (jumps := J₂) (boundaryWalkSpec b₂ J₂ θ true) D
    (show i' + 1 ≤ j by omega)
  have e2 : truncDrv D j i' = D i' := truncDrv_of_lt D (by omega)
  have h' := h i' hi' (by rw [e1]; exact hl) (by rw [e2]; exact hfin)
  rwa [e2] at h'

theorem denseAt_truncDrv {κ θ : ℝ} {b₁ : ℝ → ℝ} {J₁ : Finset ℝ} {b₂ : ℝ → ℝ} {J₂ : Finset ℝ} {D₁ D : ℕ → Drv}
    {o : ℕ} {c : Chart} {m : ℝ} {j i : ℕ} (hij : i ≤ j) :
    DenseAt κ θ b₁ J₁ b₂ J₂ D₁ (truncDrv D j) o c m i ↔ DenseAt κ θ b₁ J₁ b₂ J₂ D₁ D o c m i := by
  unfold DenseAt
  rw [run_truncDrv _ D hij]

theorem isRegularDriver_truncDrv {N : ℕ} (h : ∀ i < N, IsRegularDriver (D₂ i)) (i : ℕ) :
    IsRegularDriver (truncDrv D₂ N i) := by
  by_cases hi : i < N
  · rw [truncDrv_of_lt D₂ hi]; exact h i hi
  · unfold truncDrv; simp only [hi, ↓reduceIte]; exact LuM.isRegularDriver_zeroDrv0

theorem rootRule6_truncDrv {N : ℕ} (hN : 0 < N) (h : RootRule6 κ θ b₁ J₁ R c m D₁ D₂) :
    RootRule6 κ θ b₁ J₁ R c m D₁ (truncDrv D₂ N) := by
  unfold RootRule6
  rw [truncDrv_of_lt D₂ hN]
  exact h

theorem stageRule6_truncDrv {o N : ℕ} (h : StageRule6 κ θ b₁ J₁ b₂ J₂ c m D₁ D₂ o N) :
    StageRule6 κ θ b₁ J₁ b₂ J₂ c m D₁ (truncDrv D₂ N) o N := by
  intro i h2 hiN hl hpos hrg hdn
  have e1 := truncDrv_of_lt D₂ hiN
  have e2 := run_truncDrv (κ := κ) (b := b₂) (jumps := J₂) (boundaryWalkSpec b₂ J₂ θ true) D₂ hiN.le
  rw [e1, e2]
  exact h i h2 hiN hl hpos (recGoodAt_truncDrv hiN.le hrg) ((denseAt_truncDrv hiN.le).1 hdn)

end Trunc

end InteractingSLE.Theorem14.SB.Lk
