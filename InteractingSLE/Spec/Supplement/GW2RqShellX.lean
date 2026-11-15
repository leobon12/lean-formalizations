/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW2RqWord

/-!
# The drift constant `C*` of a root and the optimal shell of a decoded stage word (decision D33)

PROVE-GW2-ROOTX round 8. GEOM2's root words at a root `x` have one finite shape (`GW2Wm.exists_hasShape_rootWordX`:
heights in a finite set, at most `N₀` positions). This fixes

* `rootM`, `rootN₀`: a height bound and a position bound of every root word at `(κ, c', x, s)`;
* **`Cstar κ c' x s = driftC κ (max rootM (λ + πχ/2) + πχ/2) rootN₀`**, a constant of the root only;
* **`optShell_schedWordMapX`**: if the base word of a record decodes as the stage word of a split-free past with both
  junction regions nonempty, the optimal shell of GEOM2's raised stage word `schedWordMapX … θa y` presents it, has
  separated angles, and has drift at most `Cstar`.

Deterministic.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Finset
open scoped NNReal
open QuantumZipper (chiC)

namespace InteractingSLE.Theorem14.GW2Rq

open Restart Exist.Staged Exist.StagedLaw GW2Sdf GW2TipSystem GW2TipSystem.RootL6 Sec5 GW2Wm GW2Stl

/-- A finite height set bounds every word of that shape. -/
theorem exists_abs_fn_le_of_shape {S : Set ℝ} (hS : S.Finite) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ (N : ℕ) (c : BoundaryWord), HasShape S N c → ∀ y : ℝ, |c.fn y| ≤ M := by
  obtain ⟨M, hM⟩ := (hS.image fun x : ℝ => |x|).bddAbove
  refine ⟨max M 0, le_max_right _ _, fun N c hc y => ?_⟩
  have hi : c.index y ≤ c.1 := (Finset.card_filter_le _ _).trans (Finset.card_range _).le
  exact (hM ⟨_, hc.1 _ hi, rfl⟩).trans (le_max_left _ _)

/-- The position bound of the root words at `(κ, c', x, s)`. -/
def rootN₀ (κ : ℝ) (c' : BoundaryWord) (x : ℝ) (s : ℝ≥0) : ℕ :=
  (exists_hasShape_rootWordX κ c' x s).choose_spec.2.choose

/-- The height bound of the root words at `(κ, c', x, s)`. -/
def rootM (κ : ℝ) (c' : BoundaryWord) (x : ℝ) (s : ℝ≥0) : ℝ :=
  (exists_abs_fn_le_of_shape (exists_hasShape_rootWordX κ c' x s).choose_spec.1).choose

theorem hasShape_root (κ : ℝ) (c' : BoundaryWord) (x : ℝ) (s : ℝ≥0) (r : RecData) :
    HasShape (exists_hasShape_rootWordX κ c' x s).choose (rootN₀ κ c' x s) (rootWordX κ c' x s r) :=
  (exists_hasShape_rootWordX κ c' x s).choose_spec.2.choose_spec r

theorem abs_fn_root_le (κ : ℝ) (c' : BoundaryWord) (x : ℝ) (s : ℝ≥0) (r : RecData) (z : ℝ) :
    |(rootWordX κ c' x s r).fn z| ≤ rootM κ c' x s :=
  (exists_abs_fn_le_of_shape (exists_hasShape_rootWordX κ c' x s).choose_spec.1).choose_spec.2 _ _
    (hasShape_root κ c' x s r) z

theorem card_jumps_root_le (κ : ℝ) (c' : BoundaryWord) (x : ℝ) (s : ℝ≥0) (r : RecData) :
    (rootWordX κ c' x s r).jumps.card ≤ rootN₀ κ c' x s :=
  Finset.card_image_le.trans ((Finset.card_range _).le.trans (hasShape_root κ c' x s r).2)

/-- **The drift constant of a root**: from the root words' shape only. -/
def Cstar (κ : ℝ) (c' : BoundaryWord) (x : ℝ) (s : ℝ≥0) : ℝ :=
  driftC κ (max (rootM κ c' x s) (sleLambda κ + Real.pi / 2 * chiC κ) + Real.pi / 2 * chiC κ) (rootN₀ κ c' x s)

/-- **The optimal shell of GEOM2's raised stage word of a decoded record.** -/
theorem optShell_schedWordMapX {κ : ℝ} (hκ : 0 < κ) (hκ4 : κ < 4) {c' : BoundaryWord} {x : ℝ} {s : ℝ≥0}
    {L : List (ℝ × ℝ≥0)} {N : ℕ} {hN : L.length = N} {θa : ℝ} {y : RecData} {cf : RecData} {R : ℝ≥0 → ℝ}
    {b : ℕ → ℝ≥0}
    (hdec : baseWordX κ c' x s L N hN y =
      GW2JDetR5.stageWord (κ := κ) (rootWordX κ c' x s) (progAngle L) N (pastOf cf R b N))
    (hθ : ∀ j, progAngle L j ∈ Icc (-(Real.pi / 2)) (Real.pi / 2)) (hθa : θa ∈ Icc (-(Real.pi / 2)) (Real.pi / 2))
    (hsplit : SplitFreePast N (pastOf cf R b N)) (hL : GW2Sdp.junctionL N (pastOf cf R b N) < 0)
    (hR : 0 < GW2Sdp.junctionR N (pastOf cf R b N)) (k : ℕ) (start : ℝ) :
    PresentsO κ (schedWordMapX κ c' x s L N hN θa y) (rootScale k) false
        (optShell κ (schedWordMapX κ c' x s L N hN θa y) θa k start).xL
        (angleWordL κ (optShell κ (schedWordMapX κ c' x s L N hN θa y) θa k start).φ
          (optShell κ (schedWordMapX κ c' x s L N hN θa y) θa k start).mL
          (optShell κ (schedWordMapX κ c' x s L N hN θa y) θa k start).ρL₀)
        (optShell κ (schedWordMapX κ c' x s L N hN θa y) θa k start).xR
        (angleWordR κ (optShell κ (schedWordMapX κ c' x s L N hN θa y) θa k start).φ
          (optShell κ (schedWordMapX κ c' x s L N hN θa y) θa k start).mR
          (optShell κ (schedWordMapX κ c' x s L N hN θa y) θa k start).ρR₀) ∧
      (∀ i, (optShell κ (schedWordMapX κ c' x s L N hN θa y) θa k start).φ i ∈
        Icc (-(Real.pi / 2)) (Real.pi / 2)) ∧
      Prop59Stage.stageDriftBound κ (optShell κ (schedWordMapX κ c' x s L N hN θa y) θa k start).ρL₀
        (optShell κ (schedWordMapX κ c' x s L N hN θa y) θa k start).ρR₀ ≤ Cstar κ c' x s := by
  have hβ : schedWordMapX κ c' x s L N hN θa y =
      GW2Rd.upW (θa * chiC κ) (GW2JDetR5.stageWord (κ := κ) (rootWordX κ c' x s) (progAngle L) N
        (pastOf cf R b N)) := by
    unfold schedWordMapX
    rw [hdec]
  exact optShell_stageWord hκ hκ4 (rootWordX κ c' x s) (progAngle L) hθ
    (fun r z _ => abs_fn_root_le κ c' x s r z) (card_jumps_root_le κ c' x s) N (pastOf cf R b N) hsplit hL hR
    hθa hβ k start

end InteractingSLE.Theorem14.GW2Rq
