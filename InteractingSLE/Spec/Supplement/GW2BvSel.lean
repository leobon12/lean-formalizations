/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW2SdoShape
import InteractingSLE.Spec.Supplement.GW2RvPkg

/-!
# The near selection pinned to the lower, rightward structure (decision D37 (A))

Packet PROVE-GW2-BUF (round 19; the package for SDE's `hwords`, D45 (1)). SDE's `nearSelS` takes the upper (leftward)
family whenever the upper structure holds. J32's reach set is rightward, so clause (iii) of the near facts needs a
rightward family (`goLeft = false`). Decision D37 (A) takes the lower structure. RELDET's
`GW2Rd.ae_nearStructBot_junction` proves it on every alive history of `J32S GW2Sdq.gapFam` (D43).

* `nearShapeBot s flip c`: the lower shape of the dilated base word;
* **`exists_nearSelection_bot`**: under `NearStructBot`, a near family of that shape, with the flow-line positions of
  the dilated base word, presenting the raised base word at angles tending to the lower extreme;
* `nearSelSB` (+ `_eq`, `_shape`, `_positions`, `_goLeft`, `_spec`) and the package **`withNearSB`** (SDE's
  `withNearS` with `nearSelSB`): `withNearSB_shape`, `withNearSB_positions`, **`withNearSB_goLeft`**,
  **`frameNNearWord_withNearSB`**, **`vwordsX_withNearSB`**, `vpkgXSafe_withNearSB`, `sameSlots_withNearSB`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Filter Topology Finset
open scoped NNReal ENNReal
open QuantumZipper (chiC)

universe u

namespace InteractingSLE.Theorem14.GW2Bh

open Restart GW2JDetR11 GW2Sdf GW2Sdh GW2Sdi GW2Sdx GW2Sdy GW2Sdo GW2TipSystem GW2TipSystem.RootC24
  GW2TipSystem.RootN4 GW2TipSystem.RootH10 GW2TipSystem.RootW8 Supp12.DSReach CS3Cross

/-- **The lower shape of the near family of a base word.** -/
def nearShapeBot (s : ℝ≥0) (flip : Bool) (c : BoundaryWord) : ℕ × ℕ × ℕ × ℕ × Bool :=
  (flowLineNL (nearDilWord s flip c).fn (nearDilWord s flip c).jumps 0,
    flowLineNR (nearDilWord s flip c).fn (nearDilWord s flip c).jumps 0,
    flowLineNL (nearDilWord s flip c).fn (nearDilWord s flip c).jumps 0 - 1, cutR (nearDilWord s flip c), false)

/-- **The rightward near selection** under the lower structure: a near family of the lower shape with the flow-line
positions of the dilated base word, and angle indices `ι` such that its word at `m` presents the raised base word at
the angle of `ι m`. -/
theorem exists_nearSelection_bot {Ω : Type u} [MeasurableSpace Ω] (cs : SourceData Ω)
    (r : ScaledRootIdx cs.Θ cs.Q) {s : ℝ≥0} (hs : s ≠ 0) (flip : Bool) {c : BoundaryWord}
    (h : NearStructBot cs.κ s flip c) :
    ∃ (f : NearCrossingFamily.{u} cs.κ) (ι : ℕ → ℕ), famShape f = nearShapeBot s flip c ∧
      PositionsOf f (nearDilWord s flip c) ∧ ∀ m,
        PresentsO cs.κ (GW2Rd.upW ((RootJ31.angleEnumeration cs r (ι m) : ℝ) * chiC cs.κ) c) s flip f.xL (f.ρLs m)
          f.xR (f.ρRs m) := by
  classical
  have hθ₀' : nearSign flip * (-(Real.pi / 2)) = Real.pi / 2 ∨
      nearSign flip * (-(Real.pi / 2)) = -(Real.pi / 2) := by
    cases flip <;> simp [nearSign]
  obtain ⟨ι₀, hι₀⟩ := exists_angleIdx_tendsto cs r hθ₀'
  have hι : Tendsto (fun m => nearSign flip * (RootJ31.angleEnumeration cs r (ι₀ m) : ℝ)) atTop
      (𝓝 (-(Real.pi / 2))) := by
    have := hι₀.const_mul (nearSign flip)
    rwa [← mul_assoc, nearSign_mul_self, one_mul] at this
  obtain ⟨f, N, hgo, hmL, hmR, hf⟩ := exists_nearFamily_bottom_shape.{u} cs.hκ cs.hκ4 h.left h.oldR h.xm h.xp
    h.farL h.farR hι
  obtain ⟨eL, eR, -, -, -, -⟩ := hf 0
  refine ⟨f, fun m => ι₀ (m + N), ?_, positionsOf_of_isFlowType (hf 0), fun m => ?_⟩
  · simp only [famShape, nearShapeBot, hgo, hmL, hmR, eL, eR]
  · have := presentsO_of_isFlowType_nearDilWord hs flip (hf m)
    rwa [← mul_assoc, nearSign_mul_self, one_mul] at this

open Classical in
/-- **The rightward pinned near selection** at a history and sample: under the lower structure,
`exists_nearSelection_bot`'s family and angle indices; otherwise the default family and the identity. -/
def nearSelSB {Ω : Type u} [MeasurableSpace Ω] (cs : SourceData Ω) (r : ScaledRootIdx cs.Θ cs.Q) (s : ℝ≥0)
    (flip : Bool) (c : BoundaryWord) (f₀ : NearCrossingFamily.{u} cs.κ) :
    NearCrossingFamily.{u} cs.κ × (ℕ → ℕ) :=
  if h : s ≠ 0 ∧ NearStructBot cs.κ s flip c then
    ((exists_nearSelection_bot cs r h.1 flip h.2).choose,
      (exists_nearSelection_bot cs r h.1 flip h.2).choose_spec.choose)
  else (f₀, id)

section Sel

variable {Ω : Type u} [MeasurableSpace Ω] (cs : SourceData Ω) (r : ScaledRootIdx cs.Θ cs.Q) {s : ℝ≥0}
  (hs : s ≠ 0) (flip : Bool) {c : BoundaryWord} (h : NearStructBot cs.κ s flip c) (f₀ : NearCrossingFamily.{u} cs.κ)

include hs h in
theorem nearSelSB_eq :
    nearSelSB cs r s flip c f₀ = ((exists_nearSelection_bot cs r hs flip h).choose,
      (exists_nearSelection_bot cs r hs flip h).choose_spec.choose) := by
  unfold nearSelSB
  split_ifs with h'
  · rfl
  · exact absurd ⟨hs, h⟩ h'

include hs h in
theorem nearSelSB_shape : famShape (nearSelSB cs r s flip c f₀).1 = nearShapeBot s flip c := by
  rw [nearSelSB_eq cs r hs flip h f₀]
  exact (exists_nearSelection_bot cs r hs flip h).choose_spec.choose_spec.1

include hs h in
theorem nearSelSB_positions : PositionsOf (nearSelSB cs r s flip c f₀).1 (nearDilWord s flip c) := by
  rw [nearSelSB_eq cs r hs flip h f₀]
  exact (exists_nearSelection_bot cs r hs flip h).choose_spec.choose_spec.2.1

include hs h in
/-- **The rightward selection goes right.** -/
theorem nearSelSB_goLeft : (nearSelSB cs r s flip c f₀).1.goLeft = false := by
  have h1 := nearSelSB_shape cs r hs flip h f₀
  simp only [famShape, nearShapeBot, Prod.mk.injEq] at h1
  exact h1.2.2.2.2

include hs h in
theorem nearSelSB_spec (m : ℕ) :
    PresentsO cs.κ (GW2Rd.upW ((RootJ31.angleEnumeration cs r ((nearSelSB cs r s flip c f₀).2 m) : ℝ) *
      chiC cs.κ) c) s flip (nearSelSB cs r s flip c f₀).1.xL ((nearSelSB cs r s flip c f₀).1.ρLs m)
      (nearSelSB cs r s flip c f₀).1.xR ((nearSelSB cs r s flip c f₀).1.ρRs m) := by
  rw [nearSelSB_eq cs r hs flip h f₀]
  exact (exists_nearSelection_bot cs r hs flip h).choose_spec.choose_spec.2.2 m

end Sel

/-! ### The package with the rightward selection -/

/-- **The package with the rightward pinned near selection** (SDE's `withNearS` with `nearSelSB`). -/
def withNearSB (V : VPkgXFamily.{u}) (lam : NearDil.{u})
    (base : ∀ (Ω : Type u) [MeasurableSpace Ω] [StandardBorelSpace Ω] (c : SourceData Ω)
      (_r : ScaledRootIdx c.Θ c.Q), List (EntryIdx c.Θ c.Q) → Ω → BoundaryWord)
    (kSel : ∀ (Ω : Type u) [MeasurableSpace Ω] [StandardBorelSpace Ω] (c : SourceData Ω)
      (_r : ScaledRootIdx c.Θ c.Q), List (EntryIdx c.Θ c.Q) → Ω → ℕ → ℕ → ℕ) : VPkgXFamily.{u} :=
  fun Ω _ _ c r =>
    { V Ω c r with
      nearFamily := fun l ω => (nearSelSB c r (nearRootScale r.2 (lam Ω c r l ω)) (flipOf l.length)
        (base Ω c r l ω) ((V Ω c r).nearFamily l ω)).1
      nearCandidate := fun l ω n m => Nat.pair ((nearSelSB c r (nearRootScale r.2 (lam Ω c r l ω))
        (flipOf l.length) (base Ω c r l ω) ((V Ω c r).nearFamily l ω)).2 m) (kSel Ω c r l ω n m) }

section Pkg

variable (V : VPkgXFamily.{u}) (lam : NearDil.{u})
  (base : ∀ (Ω : Type u) [MeasurableSpace Ω] [StandardBorelSpace Ω] (c : SourceData Ω)
    (_r : ScaledRootIdx c.Θ c.Q), List (EntryIdx c.Θ c.Q) → Ω → BoundaryWord)
  (kSel : ∀ (Ω : Type u) [MeasurableSpace Ω] [StandardBorelSpace Ω] (c : SourceData Ω)
    (_r : ScaledRootIdx c.Θ c.Q), List (EntryIdx c.Θ c.Q) → Ω → ℕ → ℕ → ℕ)

/-- The rightward selection keeps the package's slots. -/
theorem sameSlots_withNearSB : GW2Rv.SameSlots V (withNearSB V lam base kSel) := fun _ _ _ _ _ => ⟨rfl, rfl⟩

/-- The rightward selection keeps the shells. -/
theorem slowShell_withNearSB (Ω : Type u) [MeasurableSpace Ω] [StandardBorelSpace Ω] (c : SourceData Ω)
    (r : ScaledRootIdx c.Θ c.Q) : (withNearSB V lam base kSel Ω c r).slowShell = (V Ω c r).slowShell := rfl

/-- **The shape identity** where the lower structure holds. -/
theorem withNearSB_shape (Ω : Type u) [MeasurableSpace Ω] [StandardBorelSpace Ω] (c : SourceData Ω)
    (r : ScaledRootIdx c.Θ c.Q) (l : List (EntryIdx c.Θ c.Q)) (ω : Ω) (hlam : lam Ω c r l ω ≠ 0)
    (h : NearStructBot c.κ (nearRootScale r.2 (lam Ω c r l ω)) (flipOf l.length) (base Ω c r l ω)) :
    famShape ((withNearSB V lam base kSel Ω c r).nearFamily l ω) =
      nearShapeBot (nearRootScale r.2 (lam Ω c r l ω)) (flipOf l.length) (base Ω c r l ω) :=
  nearSelSB_shape c r (nearRootScale_ne_zero r.2 hlam) (flipOf l.length) h _

/-- **The position identity** where the lower structure holds. -/
theorem withNearSB_positions (Ω : Type u) [MeasurableSpace Ω] [StandardBorelSpace Ω] (c : SourceData Ω)
    (r : ScaledRootIdx c.Θ c.Q) (l : List (EntryIdx c.Θ c.Q)) (ω : Ω) (hlam : lam Ω c r l ω ≠ 0)
    (h : NearStructBot c.κ (nearRootScale r.2 (lam Ω c r l ω)) (flipOf l.length) (base Ω c r l ω)) :
    PositionsOf ((withNearSB V lam base kSel Ω c r).nearFamily l ω)
      (nearDilWord (nearRootScale r.2 (lam Ω c r l ω)) (flipOf l.length) (base Ω c r l ω)) :=
  nearSelSB_positions c r (nearRootScale_ne_zero r.2 hlam) (flipOf l.length) h _

/-- **The near family goes right** where the lower structure holds. -/
theorem withNearSB_goLeft (Ω : Type u) [MeasurableSpace Ω] [StandardBorelSpace Ω] (c : SourceData Ω)
    (r : ScaledRootIdx c.Θ c.Q) (l : List (EntryIdx c.Θ c.Q)) (ω : Ω) (hlam : lam Ω c r l ω ≠ 0)
    (h : NearStructBot c.κ (nearRootScale r.2 (lam Ω c r l ω)) (flipOf l.length) (base Ω c r l ω)) :
    ((withNearSB V lam base kSel Ω c r).nearFamily l ω).goLeft = false :=
  nearSelSB_goLeft c r (nearRootScale_ne_zero r.2 hlam) (flipOf l.length) h _

/-- **The near words of the package with the rightward selection** (as `GW2Sdo.frameNNearWord_withNearS`). -/
theorem frameNNearWord_withNearSB {D : ConstructionFamily.{u}}
    (hlam : ∀ (Ω : Type u) [MeasurableSpace Ω] [StandardBorelSpace Ω] (c : SourceData Ω)
      (r : ScaledRootIdx c.Θ c.Q) (l : List (EntryIdx c.Θ c.Q)) (ω : Ω), lam Ω c r l ω ≠ 0)
    (hword : ∀ (Ω : Type u) [MeasurableSpace Ω] [StandardBorelSpace Ω] (c : SourceData Ω)
      (r : ScaledRootIdx c.Θ c.Q) (l : List (EntryIdx c.Θ c.Q)),
      ∀ᵐ ω ∂c.P, ω ∈ ((D Ω c).experiment r).data.alive ((D Ω c).G r) l → ∀ n : ℕ, ∀ᶠ m in atTop, ∀ i k : ℕ,
        ((V Ω c r).nearVar l n m (Nat.pair i k)).record ω ∈ ((V Ω c r).nearVar l n m (Nat.pair i k)).E ∧
        ((V Ω c r).nearVar l n m (Nat.pair i k)).β (((V Ω c r).nearVar l n m (Nat.pair i k)).record ω) =
          GW2Rd.upW ((RootJ31.angleEnumeration c r i : ℝ) * chiC c.κ) (base Ω c r l ω))
    (hstruct : ∀ (Ω : Type u) [MeasurableSpace Ω] [StandardBorelSpace Ω] (c : SourceData Ω)
      (r : ScaledRootIdx c.Θ c.Q) (l : List (EntryIdx c.Θ c.Q)),
      ∀ᵐ ω ∂c.P, ω ∈ ((D Ω c).experiment r).data.alive ((D Ω c).G r) l →
        NearStructBot c.κ (nearRootScale r.2 (lam Ω c r l ω)) (flipOf l.length) (base Ω c r l ω)) :
    FrameNNearWord D (((withNearSB V lam base kSel).at 0).frameN lam) := by
  intro Ω _ _ c r l
  filter_upwards [hword Ω c r l, hstruct Ω c r l] with ω hw hs halive n
  filter_upwards [hw halive n] with m hm
  set s := nearRootScale r.2 (lam Ω c r l ω)
  have hs0 : s ≠ 0 := nearRootScale_ne_zero r.2 (hlam Ω c r l ω)
  set sel := nearSelSB c r s (flipOf l.length) (base Ω c r l ω) ((V Ω c r).nearFamily l ω)
  obtain ⟨hE, hβ⟩ := hm (sel.2 m) (kSel Ω c r l ω n m)
  refine ⟨hE, ?_⟩
  show PresentsO c.κ (((V Ω c r).nearVar l n m (Nat.pair (sel.2 m) (kSel Ω c r l ω n m))).β
    (((V Ω c r).nearVar l n m (Nat.pair (sel.2 m) (kSel Ω c r l ω n m))).record ω)) s (flipOf l.length)
    sel.1.xL (sel.1.ρLs m) sel.1.xR (sel.1.ρRs m)
  rw [hβ]
  exact nearSelSB_spec c r hs0 (flipOf l.length) (hs halive) ((V Ω c r).nearFamily l ω) m

/-- The rightward selection changes neither the stage variables nor the shells. -/
theorem vpkgXSafe_withNearSB {V : VPkgXFamily.{u}} (hV : VPkgXSafe V) : VPkgXSafe (withNearSB V lam base kSel) :=
  ⟨hV.nearSafe, hV.slowSafe⟩

/-- **The words of the package with the rightward selection**: its near words, and the package's slow words. -/
theorem vwordsX_withNearSB {D : ConstructionFamily.{u}}
    (hlam : ∀ (Ω : Type u) [MeasurableSpace Ω] [StandardBorelSpace Ω] (c : SourceData Ω)
      (r : ScaledRootIdx c.Θ c.Q) (l : List (EntryIdx c.Θ c.Q)) (ω : Ω), lam Ω c r l ω ≠ 0)
    (hword : ∀ (Ω : Type u) [MeasurableSpace Ω] [StandardBorelSpace Ω] (c : SourceData Ω)
      (r : ScaledRootIdx c.Θ c.Q) (l : List (EntryIdx c.Θ c.Q)),
      ∀ᵐ ω ∂c.P, ω ∈ ((D Ω c).experiment r).data.alive ((D Ω c).G r) l → ∀ n : ℕ, ∀ᶠ m in atTop, ∀ i k : ℕ,
        ((V Ω c r).nearVar l n m (Nat.pair i k)).record ω ∈ ((V Ω c r).nearVar l n m (Nat.pair i k)).E ∧
        ((V Ω c r).nearVar l n m (Nat.pair i k)).β (((V Ω c r).nearVar l n m (Nat.pair i k)).record ω) =
          GW2Rd.upW ((RootJ31.angleEnumeration c r i : ℝ) * chiC c.κ) (base Ω c r l ω))
    (hstruct : ∀ (Ω : Type u) [MeasurableSpace Ω] [StandardBorelSpace Ω] (c : SourceData Ω)
      (r : ScaledRootIdx c.Θ c.Q) (l : List (EntryIdx c.Θ c.Q)),
      ∀ᵐ ω ∂c.P, ω ∈ ((D Ω c).experiment r).data.alive ((D Ω c).G r) l →
        NearStructBot c.κ (nearRootScale r.2 (lam Ω c r l ω)) (flipOf l.length) (base Ω c r l ω))
    (hslow : FrameNSlowWordN D fun n => (V.at n).frameN lam) :
    VWordsX D (withNearSB V lam base kSel) lam :=
  ⟨frameNNearWord_withNearSB V lam base kSel hlam hword hstruct, hslow⟩

end Pkg

end InteractingSLE.Theorem14.GW2Bh
