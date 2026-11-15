/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW2SdyFam
import InteractingSLE.Spec.Supplement.GW2SdxPair

/-!
# The near words from the structure of the dilated base word (the near-model identification)

Packet PROVE-GW2-SDE (round 11; decision D9: the existing chart, the counterflow tip at `∞`). Spec pp. 621–623: at a
history the stage word of a candidate of angle `θ` is the RAISED base word `upW (θχ) c` (STAGEMEAN's word map); the
near comparison reads it dilated by the near scale `s` (R112) and reflected on odd histories; ROOT2's crossing
families need the dilated base word to have the upper or lower structure of `RootH10.exists_crossing_top/bottom`.

* `NearStructTop`, `NearStructBot`, `NearStruct` (that structure of `nearDilWord s flip c`);
* **`exists_nearSelection`**: under the structure, a near family `f` and angle indices `ι` with
  `angleEnumeration (ι m) → ±π/2` such that `f`'s word at `m` presents the raised base word at the angle of `ι m`;
* `nearSel` (that choice, with a default off the structure), `VPkgXFamily.withNear V lam base kSel` (V with the chosen
  near family and the near candidates `Nat.pair (ι m) (kSel n m)`: our angle index, any cap and buffer component);
* **`frameNNearWord_withNear`**: the near words (`FrameNNearWord`, the `nearWord` field of `VWordsX`) of the package
  with the chosen near selection, from (N1)–(N2) the stage-word identity of the near variables at every candidate
  (record in `E`, word `upW (angle · χ) base`) and (N3) the structure of the dilated base word, almost surely on
  alive histories.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Filter Topology
open scoped NNReal ENNReal
open QuantumZipper (chiC)

universe u

namespace InteractingSLE.Theorem14.GW2Sdy

open Restart GW2JDetR11 GW2Sdf GW2Sdh GW2Sdi GW2Sdx GW2TipSystem GW2TipSystem.RootC24 GW2TipSystem.RootN4
  GW2TipSystem.RootH10

/-! ### The structure of the dilated base word -/

section Struct

variable (κ : ℝ) (s : ℝ≥0) (flip : Bool) (c : BoundaryWord)

/-- **The upper structure** (`RootH10.exists_crossing_top`'s hypotheses) of the history's dilated base word. -/
structure NearStructTop : Prop where
  oldL : ∀ y ∈ Set.Ioo (-3) 0, y ∉ (nearDilWord s flip c).jumps → (nearDilWord s flip c).fn y ∈ oldLeftHeights κ
  right : ∀ y, 0 < y → y ∉ (nearDilWord s flip c).jumps → (nearDilWord s flip c).fn y ∈ oldRightHeights κ ∨
    ∃ S : ℝ, -2 < S ∧ (nearDilWord s flip c).fn y = sleLambda (16 / κ) * (1 + S) - Real.pi * chiC κ
  xm : flowLineXL (nearDilWord s flip c).fn (nearDilWord s flip c).jumps 0
    (GW2TipStage.lastL (nearDilWord s flip c).fn (nearDilWord s flip c).jumps) ≤ -3
  xp : 0 < flowLineXR (nearDilWord s flip c).fn (nearDilWord s flip c).jumps 0
    (GW2TipStage.lastR (nearDilWord s flip c).fn (nearDilWord s flip c).jumps)
  farL : ∀ y, y < flowLineXL (nearDilWord s flip c).fn (nearDilWord s flip c).jumps 0
    (GW2TipStage.lastL (nearDilWord s flip c).fn (nearDilWord s flip c).jumps) → y ∉ (nearDilWord s flip c).jumps →
      (nearDilWord s flip c).fn y = -sleLambda (16 / κ) + Real.pi * chiC κ
  farR : ∀ y, flowLineXR (nearDilWord s flip c).fn (nearDilWord s flip c).jumps 0
    (GW2TipStage.lastR (nearDilWord s flip c).fn (nearDilWord s flip c).jumps) < y →
      y ∉ (nearDilWord s flip c).jumps → (nearDilWord s flip c).fn y = sleLambda (16 / κ) - Real.pi * chiC κ

/-- **The lower structure** (`RootH10.exists_crossing_bottom`'s hypotheses) of the history's dilated base word. -/
structure NearStructBot : Prop where
  left : ∀ y, y < 0 → y ∉ (nearDilWord s flip c).jumps → (nearDilWord s flip c).fn y ∈ oldLeftHeights κ ∨
    ∃ S : ℝ, -2 < S ∧ (nearDilWord s flip c).fn y = -sleLambda (16 / κ) * (1 + S) + Real.pi * chiC κ
  oldR : ∀ y ∈ Set.Ioo 0 3, y ∉ (nearDilWord s flip c).jumps → (nearDilWord s flip c).fn y ∈ oldRightHeights κ
  xm : flowLineXL (nearDilWord s flip c).fn (nearDilWord s flip c).jumps 0
    (GW2TipStage.lastL (nearDilWord s flip c).fn (nearDilWord s flip c).jumps) < 0
  xp : 3 ≤ flowLineXR (nearDilWord s flip c).fn (nearDilWord s flip c).jumps 0
    (GW2TipStage.lastR (nearDilWord s flip c).fn (nearDilWord s flip c).jumps)
  farL : ∀ y, y < flowLineXL (nearDilWord s flip c).fn (nearDilWord s flip c).jumps 0
    (GW2TipStage.lastL (nearDilWord s flip c).fn (nearDilWord s flip c).jumps) → y ∉ (nearDilWord s flip c).jumps →
      (nearDilWord s flip c).fn y = -sleLambda (16 / κ) + Real.pi * chiC κ
  farR : ∀ y, flowLineXR (nearDilWord s flip c).fn (nearDilWord s flip c).jumps 0
    (GW2TipStage.lastR (nearDilWord s flip c).fn (nearDilWord s flip c).jumps) < y →
      y ∉ (nearDilWord s flip c).jumps → (nearDilWord s flip c).fn y = sleLambda (16 / κ) - Real.pi * chiC κ

/-- The upper or the lower structure. -/
def NearStruct : Prop := NearStructTop κ s flip c ∨ NearStructBot κ s flip c

end Struct

theorem nearSign_mul_self (flip : Bool) : nearSign flip * nearSign flip = 1 := by
  cases flip <;> simp [nearSign]

/-- **The near selection under the structure**: a near family and angle indices tending to `±π/2` (the sign of the
history's orientation times the structure's extreme) such that the family's word at `m` presents the raised base word
at the angle of `ι m`. -/
theorem exists_nearSelection {Ω : Type u} [MeasurableSpace Ω] (cs : SourceData Ω) (r : ScaledRootIdx cs.Θ cs.Q)
    {s : ℝ≥0} (hs : s ≠ 0) (flip : Bool) {c : BoundaryWord} (h : NearStruct cs.κ s flip c) :
    ∃ (f : NearCrossingFamily.{u} cs.κ) (ι : ℕ → ℕ), ∀ m,
      PresentsO cs.κ (GW2Rd.upW ((RootJ31.angleEnumeration cs r (ι m) : ℝ) * chiC cs.κ) c) s flip f.xL (f.ρLs m)
        f.xR (f.ρRs m) := by
  have key : ∀ θ₀ : ℝ, (θ₀ = Real.pi / 2 ∨ θ₀ = -(Real.pi / 2)) →
      (∀ θs : ℕ → ℝ, Tendsto θs atTop (𝓝 θ₀) → ∃ (f : NearCrossingFamily.{u} cs.κ) (N : ℕ), ∀ m,
        PresentsO cs.κ (GW2Rd.upW (nearSign flip * θs (m + N) * chiC cs.κ) c) s flip f.xL (f.ρLs m) f.xR
          (f.ρRs m)) →
      ∃ (f : NearCrossingFamily.{u} cs.κ) (ι : ℕ → ℕ), ∀ m,
        PresentsO cs.κ (GW2Rd.upW ((RootJ31.angleEnumeration cs r (ι m) : ℝ) * chiC cs.κ) c) s flip f.xL (f.ρLs m)
          f.xR (f.ρRs m) := by
    intro θ₀ hθ₀ hfam
    have hθ₀' : nearSign flip * θ₀ = Real.pi / 2 ∨ nearSign flip * θ₀ = -(Real.pi / 2) := by
      cases flip <;> rcases hθ₀ with rfl | rfl <;> simp [nearSign]
    obtain ⟨ι₀, hι₀⟩ := exists_angleIdx_tendsto cs r hθ₀'
    have hθs : Tendsto (fun m => nearSign flip * (RootJ31.angleEnumeration cs r (ι₀ m) : ℝ)) atTop (𝓝 θ₀) := by
      have := hι₀.const_mul (nearSign flip)
      rwa [← mul_assoc, nearSign_mul_self, one_mul] at this
    obtain ⟨f, N, hf⟩ := hfam _ hθs
    refine ⟨f, fun m => ι₀ (m + N), fun m => ?_⟩
    have := hf m
    rwa [← mul_assoc, nearSign_mul_self, one_mul] at this
  rcases h with h | h
  · exact key _ (Or.inl rfl) fun θs hθ => by
      obtain ⟨f, N, -, hf⟩ := exists_nearFamily_top_presentsO.{u} cs.hκ cs.hκ4 hs flip h.oldL h.right h.xm h.xp
        h.farL h.farR hθ
      exact ⟨f, N, hf⟩
  · exact key _ (Or.inr rfl) fun θs hθ => by
      obtain ⟨f, N, -, hf⟩ := exists_nearFamily_bottom_presentsO.{u} cs.hκ cs.hκ4 hs flip h.left h.oldR h.xm h.xp
        h.farL h.farR hθ
      exact ⟨f, N, hf⟩

/-! ### The package with the chosen near selection -/

open Classical in
/-- **The chosen near selection** at a history and sample: under the structure, `exists_nearSelection`'s family and
angle indices; otherwise the default family and the identity. -/
def nearSel {Ω : Type u} [MeasurableSpace Ω] (cs : SourceData Ω) (r : ScaledRootIdx cs.Θ cs.Q) (s : ℝ≥0)
    (flip : Bool) (c : BoundaryWord) (f₀ : NearCrossingFamily.{u} cs.κ) :
    NearCrossingFamily.{u} cs.κ × (ℕ → ℕ) :=
  if h : s ≠ 0 ∧ NearStruct cs.κ s flip c then
    ((exists_nearSelection cs r h.1 flip h.2).choose, (exists_nearSelection cs r h.1 flip h.2).choose_spec.choose)
  else (f₀, id)

theorem nearSel_eq {Ω : Type u} [MeasurableSpace Ω] (cs : SourceData Ω) (r : ScaledRootIdx cs.Θ cs.Q)
    {s : ℝ≥0} (hs : s ≠ 0) (flip : Bool) {c : BoundaryWord} (h : NearStruct cs.κ s flip c)
    (f₀ : NearCrossingFamily.{u} cs.κ) :
    nearSel cs r s flip c f₀ = ((exists_nearSelection cs r hs flip h).choose,
      (exists_nearSelection cs r hs flip h).choose_spec.choose) := by
  unfold nearSel
  split_ifs with h'
  · rfl
  · exact absurd ⟨hs, h⟩ h'

theorem nearSel_spec {Ω : Type u} [MeasurableSpace Ω] (cs : SourceData Ω) (r : ScaledRootIdx cs.Θ cs.Q)
    {s : ℝ≥0} (hs : s ≠ 0) (flip : Bool) {c : BoundaryWord} (h : NearStruct cs.κ s flip c)
    (f₀ : NearCrossingFamily.{u} cs.κ) (m : ℕ) :
    PresentsO cs.κ (GW2Rd.upW ((RootJ31.angleEnumeration cs r ((nearSel cs r s flip c f₀).2 m) : ℝ) * chiC cs.κ) c)
      s flip (nearSel cs r s flip c f₀).1.xL ((nearSel cs r s flip c f₀).1.ρLs m)
      (nearSel cs r s flip c f₀).1.xR ((nearSel cs r s flip c f₀).1.ρRs m) := by
  rw [nearSel_eq cs r hs flip h f₀]
  exact (exists_nearSelection cs r hs flip h).choose_spec.choose_spec m

/-- **The package with the chosen near selection**: at a history and sample, the near family is `nearSel`'s family for
the base word `base l ω` at the near scale and orientation of ROOT2's frame, and the near candidate of `(n, m)` is
`Nat.pair (ι m) (kSel l ω n m)`: `nearSel`'s angle index, any cap and buffer component. -/
def _root_.InteractingSLE.Theorem14.GW2Sdx.VPkgXFamily.withNear (V : VPkgXFamily.{u}) (lam : NearDil.{u})
    (base : ∀ (Ω : Type u) [MeasurableSpace Ω] [StandardBorelSpace Ω] (c : SourceData Ω)
      (_r : ScaledRootIdx c.Θ c.Q), List (EntryIdx c.Θ c.Q) → Ω → BoundaryWord)
    (kSel : ∀ (Ω : Type u) [MeasurableSpace Ω] [StandardBorelSpace Ω] (c : SourceData Ω)
      (_r : ScaledRootIdx c.Θ c.Q), List (EntryIdx c.Θ c.Q) → Ω → ℕ → ℕ → ℕ) : VPkgXFamily.{u} :=
  fun Ω _ _ c r =>
    { V Ω c r with
      nearFamily := fun l ω => (nearSel c r (nearRootScale r.2 (lam Ω c r l ω)) (flipOf l.length) (base Ω c r l ω)
        ((V Ω c r).nearFamily l ω)).1
      nearCandidate := fun l ω n m => Nat.pair ((nearSel c r (nearRootScale r.2 (lam Ω c r l ω)) (flipOf l.length)
        (base Ω c r l ω) ((V Ω c r).nearFamily l ω)).2 m) (kSel Ω c r l ω n m) }

/-- **The near words of the package with the chosen near selection** (the near-model identification, spec
pp. 621–623): from (N1)–(N2) the stage-word identity of the near variables at every candidate (record in `E`, word the
raised base word at the candidate's angle), eventually in `m`, and (N3) the structure of the dilated base word, both
almost surely on alive histories. -/
theorem frameNNearWord_withNear {D : ConstructionFamily.{u}} (V : VPkgXFamily.{u}) (lam : NearDil.{u})
    (hlam : ∀ (Ω : Type u) [MeasurableSpace Ω] [StandardBorelSpace Ω] (c : SourceData Ω)
      (r : ScaledRootIdx c.Θ c.Q) (l : List (EntryIdx c.Θ c.Q)) (ω : Ω), lam Ω c r l ω ≠ 0)
    (base : ∀ (Ω : Type u) [MeasurableSpace Ω] [StandardBorelSpace Ω] (c : SourceData Ω)
      (_r : ScaledRootIdx c.Θ c.Q), List (EntryIdx c.Θ c.Q) → Ω → BoundaryWord)
    (kSel : ∀ (Ω : Type u) [MeasurableSpace Ω] [StandardBorelSpace Ω] (c : SourceData Ω)
      (_r : ScaledRootIdx c.Θ c.Q), List (EntryIdx c.Θ c.Q) → Ω → ℕ → ℕ → ℕ)
    (hword : ∀ (Ω : Type u) [MeasurableSpace Ω] [StandardBorelSpace Ω] (c : SourceData Ω)
      (r : ScaledRootIdx c.Θ c.Q) (l : List (EntryIdx c.Θ c.Q)),
      ∀ᵐ ω ∂c.P, ω ∈ ((D Ω c).experiment r).data.alive ((D Ω c).G r) l → ∀ n : ℕ, ∀ᶠ m in atTop, ∀ i k : ℕ,
        ((V Ω c r).nearVar l n m (Nat.pair i k)).record ω ∈ ((V Ω c r).nearVar l n m (Nat.pair i k)).E ∧
        ((V Ω c r).nearVar l n m (Nat.pair i k)).β (((V Ω c r).nearVar l n m (Nat.pair i k)).record ω) =
          GW2Rd.upW ((RootJ31.angleEnumeration c r i : ℝ) * chiC c.κ) (base Ω c r l ω))
    (hstruct : ∀ (Ω : Type u) [MeasurableSpace Ω] [StandardBorelSpace Ω] (c : SourceData Ω)
      (r : ScaledRootIdx c.Θ c.Q) (l : List (EntryIdx c.Θ c.Q)),
      ∀ᵐ ω ∂c.P, ω ∈ ((D Ω c).experiment r).data.alive ((D Ω c).G r) l →
        NearStruct c.κ (nearRootScale r.2 (lam Ω c r l ω)) (flipOf l.length) (base Ω c r l ω)) :
    FrameNNearWord D (((V.withNear lam base kSel).at 0).frameN lam) := by
  intro Ω _ _ c r l
  filter_upwards [hword Ω c r l, hstruct Ω c r l] with ω hw hs halive n
  filter_upwards [hw halive n] with m hm
  set s := nearRootScale r.2 (lam Ω c r l ω)
  have hs0 : s ≠ 0 := nearRootScale_ne_zero r.2 (hlam Ω c r l ω)
  set sel := nearSel c r s (flipOf l.length) (base Ω c r l ω) ((V Ω c r).nearFamily l ω)
  obtain ⟨hE, hβ⟩ := hm (sel.2 m) (kSel Ω c r l ω n m)
  refine ⟨hE, ?_⟩
  show PresentsO c.κ (((V Ω c r).nearVar l n m (Nat.pair (sel.2 m) (kSel Ω c r l ω n m))).β
    (((V Ω c r).nearVar l n m (Nat.pair (sel.2 m) (kSel Ω c r l ω n m))).record ω)) s (flipOf l.length)
    sel.1.xL (sel.1.ρLs m) sel.1.xR (sel.1.ρRs m)
  rw [hβ]
  exact nearSel_spec c r hs0 (flipOf l.length) (hs halive) ((V Ω c r).nearFamily l ω) m

/-- The near selection changes neither the stage variables nor the shells: the safe laws carry over. -/
theorem vpkgXSafe_withNear {V : VPkgXFamily.{u}} (hV : VPkgXSafe V) (lam : NearDil.{u})
    (base : ∀ (Ω : Type u) [MeasurableSpace Ω] [StandardBorelSpace Ω] (c : SourceData Ω)
      (_r : ScaledRootIdx c.Θ c.Q), List (EntryIdx c.Θ c.Q) → Ω → BoundaryWord)
    (kSel : ∀ (Ω : Type u) [MeasurableSpace Ω] [StandardBorelSpace Ω] (c : SourceData Ω)
      (_r : ScaledRootIdx c.Θ c.Q), List (EntryIdx c.Θ c.Q) → Ω → ℕ → ℕ → ℕ) :
    VPkgXSafe (V.withNear lam base kSel) :=
  ⟨hV.nearSafe, hV.slowSafe⟩

/-- **The words of the package with the chosen near selection**: the near words of `frameNNearWord_withNear`, and the
package's slow words (unchanged by the near selection). -/
theorem vwordsX_withNear {D : ConstructionFamily.{u}} (V : VPkgXFamily.{u}) (lam : NearDil.{u})
    (hlam : ∀ (Ω : Type u) [MeasurableSpace Ω] [StandardBorelSpace Ω] (c : SourceData Ω)
      (r : ScaledRootIdx c.Θ c.Q) (l : List (EntryIdx c.Θ c.Q)) (ω : Ω), lam Ω c r l ω ≠ 0)
    (base : ∀ (Ω : Type u) [MeasurableSpace Ω] [StandardBorelSpace Ω] (c : SourceData Ω)
      (_r : ScaledRootIdx c.Θ c.Q), List (EntryIdx c.Θ c.Q) → Ω → BoundaryWord)
    (kSel : ∀ (Ω : Type u) [MeasurableSpace Ω] [StandardBorelSpace Ω] (c : SourceData Ω)
      (_r : ScaledRootIdx c.Θ c.Q), List (EntryIdx c.Θ c.Q) → Ω → ℕ → ℕ → ℕ)
    (hword : ∀ (Ω : Type u) [MeasurableSpace Ω] [StandardBorelSpace Ω] (c : SourceData Ω)
      (r : ScaledRootIdx c.Θ c.Q) (l : List (EntryIdx c.Θ c.Q)),
      ∀ᵐ ω ∂c.P, ω ∈ ((D Ω c).experiment r).data.alive ((D Ω c).G r) l → ∀ n : ℕ, ∀ᶠ m in atTop, ∀ i k : ℕ,
        ((V Ω c r).nearVar l n m (Nat.pair i k)).record ω ∈ ((V Ω c r).nearVar l n m (Nat.pair i k)).E ∧
        ((V Ω c r).nearVar l n m (Nat.pair i k)).β (((V Ω c r).nearVar l n m (Nat.pair i k)).record ω) =
          GW2Rd.upW ((RootJ31.angleEnumeration c r i : ℝ) * chiC c.κ) (base Ω c r l ω))
    (hstruct : ∀ (Ω : Type u) [MeasurableSpace Ω] [StandardBorelSpace Ω] (c : SourceData Ω)
      (r : ScaledRootIdx c.Θ c.Q) (l : List (EntryIdx c.Θ c.Q)),
      ∀ᵐ ω ∂c.P, ω ∈ ((D Ω c).experiment r).data.alive ((D Ω c).G r) l →
        NearStruct c.κ (nearRootScale r.2 (lam Ω c r l ω)) (flipOf l.length) (base Ω c r l ω))
    (hslow : FrameNSlowWordN D fun n => (V.at n).frameN lam) :
    VWordsX D (V.withNear lam base kSel) lam :=
  ⟨frameNNearWord_withNear V lam hlam base kSel hword hstruct, hslow⟩

end InteractingSLE.Theorem14.GW2Sdy
