/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW2WxClock
import InteractingSLE.Spec.Supplement.GW2WmChoice
import InteractingSLE.Spec.Supplement.GW2WmPos

/-!
# GW2's stage word map at a root `x`: re-centred by ROOTX's chart reader (decision D8)

Packet PROVE-GW2-GEOM2 (round 8; the root-`x` word-map layer of PROVE-GW2-ROOTX's D8 rebuild). ROOTX's root-`x`
stage chart is `stgChart (relChartX x s rec) R a` with `relChartX x s r = (relChart r).recenter (baseRead x s r)`
(`GW2Rz.relChartX`, `baseRead` ROOT2's measurable boundary reader). The word read in that chart is the joint word
re-centred by the SAME reader:

* **`rootWordX κ c′ x s r`** `= shiftW (baseRead x s r) (jointWordOfRec (specOffset κ) κ c′ r)`: measurable, sorted,
  one finite shape, far heights `−λ′ + πχ` / `λ′ − πχ` (R62's offset); **`baseRead_eq_rootOff`** and
  **`rootWordX_eq_rootWord`**: at an untouched root it is round 7's `rootWord` (both readers are `Re relBdry`);
* `baseWordX`, **`schedWordMapX κ c′ x s L N hN θa`** (the flowed word with the stage decoder),
  **`schedWordMapX_targets`**, `farL_baseWordX`, `farR_baseWordX`, **`totals_half_pi_baseWordX`**,
  **`totals_neg_half_pi_baseWordX`** (D9's check at a root `x`);
* **`wmChoiceX`**: ROOTX's `SchedChoice` input with this word map and `σa = specOffset κ + θa χ`, `kc = χ`;
  **`wmChoiceX_targets`** is the `hβ` hypothesis of `GW2Rz.schedInstX_good`;
* **`baseWordX_augRecX`**: on ROOTX's root-`x` augmented record, on the good event before the root-`x` contact, the
  base word is the root word flowed through the instance's OWN relative stage records between the root-`x` stage
  starts at the physical stage times (`GW2Wm.stageDec_augRecX_trueBd`);
* the label positions re-centred by `baseRead`: **`mem_jumps_rootWordX`**, `labelL_mem_jumps_rootWordX`,
  `labelR_mem_jumps_rootWordX`, **`rootWordX_label_bounds`** (the tail junctions bound all labels).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Filter MeasureTheory Topology
open scoped NNReal ENNReal
open QuantumZipper (chiC)

universe u

namespace InteractingSLE.Theorem14.GW2Wm

open Restart Exist.Staged Exist.StagedLaw Sec7.StripSysField GW2JointKernel GW2TipStage GW2TipSystem

/-! ### The root word re-centred by ROOTX's reader -/

/-- **The root word at the root `x`, re-centred by ROOTX's chart reader** `baseRead x s r`. -/
def rootWordX (κ : ℝ) (c' : BoundaryWord) (x : ℝ) (s : ℝ≥0) (r : RecData) : BoundaryWord :=
  Exist.StagedLaw.BoundaryWord.shiftW (GW2Rz.baseRead x s r) (jointWordOfRec (specOffset κ) κ c' r)

theorem measurable_rootWordX (κ : ℝ) (c' : BoundaryWord) (x : ℝ) (s : ℝ≥0) : Measurable (rootWordX κ c' x s) :=
  Exist.StagedLaw.BoundaryWord.measurable_shiftW.comp
    ((GW2Rz.measurable_baseRead x s).prodMk (measurable_jointWordOfRec _ _ _))

theorem isSorted_rootWordX (κ : ℝ) (c' : BoundaryWord) (x : ℝ) (s : ℝ≥0) (r : RecData) :
    (rootWordX κ c' x s r).IsSorted :=
  Exist.StagedLaw.BoundaryWord.isSorted_shiftW (isSorted_jointWordOfRec _ _ _ _) _

/-- The root words re-centred by `baseRead` have the shape of round 7's root words (re-centring moves positions
only). -/
theorem exists_hasShape_rootWordX (κ : ℝ) (c' : BoundaryWord) (x : ℝ) (s : ℝ≥0) :
    ∃ H₀ : Set ℝ, H₀.Finite ∧ ∃ N₀ : ℕ, ∀ r, GW2Stl.HasShape H₀ N₀ (rootWordX κ c' x s r) := by
  obtain ⟨H₀, hH₀, N₀, h⟩ := exists_hasShape_rootWord κ c' x
  exact ⟨H₀, hH₀, N₀, fun r => h r⟩

theorem farL_rootWordX {κ : ℝ} (hκ : 0 < κ) (c' : BoundaryWord) (x : ℝ) (s : ℝ≥0) (r : RecData)
    (hpos : 0 < markPos (rdrv r) (rtime r) 0) :
    FarL (rootWordX κ c' x s r) (-sleLambda (16 / κ) + Real.pi * chiC κ) :=
  farL_shiftW _ (farL_jointWordOfRec hκ c' r hpos)

theorem farR_rootWordX {κ : ℝ} (hκ : 0 < κ) (c' : BoundaryWord) (x : ℝ) (s : ℝ≥0) (r : RecData)
    (hneg : markPosL (rdrv r) (rtime r) 0 < 0) :
    FarR (rootWordX κ c' x s r) (sleLambda (16 / κ) - Real.pi * chiC κ) :=
  farR_shiftW _ (farR_jointWordOfRec hκ c' r hneg)

/-- **ROOTX's reader is round 7's reader at an untouched root** (both are `Re relBdry`). -/
theorem baseRead_eq_rootOff (x : ℝ) (s : ℝ≥0) (r : RecData) (hs : rtime r = s)
    (hxA : (x : ℂ) ∉ closure (Supp8.Q3Rel.invHull (rdrv r) s)) : GW2Rz.baseRead x s r = rootOff x r := by
  have hsafe : (x : ℂ) ∈ Supp8.GB6.CoordB.relSafe (rdrv r) s :=
    ⟨show (0 : ℝ) ≤ ((x : ℂ)).im by simp, hxA⟩
  unfold GW2Rz.baseRead
  rw [RootA22.boundaryRead_eq_relBdry s r hsafe, rootOff_eq_relBdry x r (by rwa [hs])]
  rw [hs]

/-- **The two root words agree at an untouched root.** -/
theorem rootWordX_eq_rootWord (κ : ℝ) (c' : BoundaryWord) (x : ℝ) (s : ℝ≥0) (r : RecData) (hs : rtime r = s)
    (hxA : (x : ℂ) ∉ closure (Supp8.Q3Rel.invHull (rdrv r) s)) : rootWordX κ c' x s r = rootWord κ c' x r := by
  unfold rootWordX rootWord
  rw [baseRead_eq_rootOff x s r hs hxA]

/-! ### The base word and the word map at a root `x` -/

/-- The base stage word at a root `x`: the re-centred root word flowed through the decoded pieces. -/
def baseWordX (κ : ℝ) (c' : BoundaryWord) (x : ℝ) (s : ℝ≥0) (L : List (ℝ × ℝ≥0)) (N : ℕ) (hN : L.length = N)
    (y : RecData) : BoundaryWord :=
  GW2JDetR5.stageWord (κ := κ) (rootWordX κ c' x s) (progAngle L) N (stageDec x s L N hN y)

/-- **The stage word map at a root `x`**: the base word raised by the current angle. -/
def schedWordMapX (κ : ℝ) (c' : BoundaryWord) (x : ℝ) (s : ℝ≥0) (L : List (ℝ × ℝ≥0)) (N : ℕ) (hN : L.length = N)
    (θa : ℝ) (y : RecData) : BoundaryWord :=
  GW2Rd.upW (θa * chiC κ) (baseWordX κ c' x s L N hN y)

/-- **The three `Good` targets of the root-`x` word map.** -/
theorem schedWordMapX_targets (κ : ℝ) (c' : BoundaryWord) (x : ℝ) (s : ℝ≥0) (L : List (ℝ × ℝ≥0)) (N : ℕ)
    (hN : L.length = N) (θa k : ℝ) :
    Measurable (schedWordMapX κ c' x s L N hN θa) ∧
      (range fun y => Supp8.Q3Stop.wordType k (schedWordMapX κ c' x s L N hN θa y)).Countable ∧
      ∀ y, (schedWordMapX κ c' x s L N hN θa y).IsSorted := by
  obtain ⟨H₀, hH₀, N₀, hW₀⟩ := exists_hasShape_rootWordX κ c' x s
  exact GW2Stl.stageWordMap_targets κ (measurable_rootWordX κ c' x s) (isSorted_rootWordX κ c' x s) hH₀ hW₀
    (progAngle L) N (θa * chiC κ) (measurable_stageDec x s L N hN) k

theorem farL_baseWordX {κ : ℝ} (hκ : 0 < κ) (c' : BoundaryWord) (x : ℝ) (s : ℝ≥0) (L : List (ℝ × ℝ≥0)) (N : ℕ)
    (hN : L.length = N) (y : RecData)
    (hpos : 0 < markPos (rdrv (decHist N y).1) (rtime (decHist N y).1) 0) :
    FarL (baseWordX κ c' x s L N hN y) (-sleLambda (16 / κ) + Real.pi * chiC κ) := by
  refine farL_stageWord (S := RecData) hκ (progAngle L) (A₀ := {r | 0 < markPos (rdrv r) (rtime r) 0})
    (fun r hr => farL_rootWordX hκ c' x s r hr) N (stageDec x s L N hN y) ?_
  rw [pastRoot_stageDec]
  exact hpos

theorem farR_baseWordX {κ : ℝ} (hκ : 0 < κ) (c' : BoundaryWord) (x : ℝ) (s : ℝ≥0) (L : List (ℝ × ℝ≥0)) (N : ℕ)
    (hN : L.length = N) (y : RecData)
    (hneg : markPosL (rdrv (decHist N y).1) (rtime (decHist N y).1) 0 < 0) :
    FarR (baseWordX κ c' x s L N hN y) (sleLambda (16 / κ) - Real.pi * chiC κ) := by
  refine farR_stageWord (S := RecData) hκ (progAngle L) (A₀ := {r | markPosL (rdrv r) (rtime r) 0 < 0})
    (fun r hr => farR_rootWordX hκ c' x s r hr) N (stageDec x s L N hN y) ?_
  rw [pastRoot_stageDec]
  exact hneg

/-- **D9's check at a root `x`, leftward**: totals `(κ − 4, κ/2 − 2)` at `π/2`. -/
theorem totals_half_pi_baseWordX {κ : ℝ} (hκ : 0 < κ) (c' : BoundaryWord) (x : ℝ) (s : ℝ≥0)
    (L : List (ℝ × ℝ≥0)) (N : ℕ) (hN : L.length = N) (y : RecData)
    (hpos : 0 < markPos (rdrv (decHist N y).1) (rtime (decHist N y).1) 0)
    (hneg : markPosL (rdrv (decHist N y).1) (rtime (decHist N y).1) 0 < 0) :
    ∑ i, flowLineRhoL κ (baseWordX κ c' x s L N hN y).fn (baseWordX κ c' x s L N hN y).jumps 0 (Real.pi / 2) i =
        κ - 4 ∧
      ∑ j, flowLineRhoR κ (baseWordX κ c' x s L N hN y).fn (baseWordX κ c' x s L N hN y).jumps 0
        (Real.pi / 2) j = κ / 2 - 2 :=
  totals_half_pi_of_far hκ (farL_baseWordX hκ c' x s L N hN y hpos) (farR_baseWordX hκ c' x s L N hN y hneg)

/-- **D9's check at a root `x`, rightward**: totals `(κ/2 − 2, κ − 4)` at `−π/2`. -/
theorem totals_neg_half_pi_baseWordX {κ : ℝ} (hκ : 0 < κ) (c' : BoundaryWord) (x : ℝ) (s : ℝ≥0)
    (L : List (ℝ × ℝ≥0)) (N : ℕ) (hN : L.length = N) (y : RecData)
    (hpos : 0 < markPos (rdrv (decHist N y).1) (rtime (decHist N y).1) 0)
    (hneg : markPosL (rdrv (decHist N y).1) (rtime (decHist N y).1) 0 < 0) :
    ∑ i, flowLineRhoL κ (baseWordX κ c' x s L N hN y).fn (baseWordX κ c' x s L N hN y).jumps 0
        (-(Real.pi / 2)) i = κ / 2 - 2 ∧
      ∑ j, flowLineRhoR κ (baseWordX κ c' x s L N hN y).fn (baseWordX κ c' x s L N hN y).jumps 0
        (-(Real.pi / 2)) j = κ - 4 :=
  totals_neg_half_pi_of_far hκ (farL_baseWordX hκ c' x s L N hN y hpos) (farR_baseWordX hκ c' x s L N hN y hneg)

/-! ### ROOTX's instance choice -/

/-- **The root-`x` instance choice with the stage word map** and R62's coefficients. -/
def wmChoiceX {Ω : Type u} (κ : ℝ) (c' : BoundaryWord) (x : ℝ) (s : ℝ≥0) (L : List (ℝ × ℝ≥0)) (N : ℕ)
    (hN : L.length = N) (θa : ℝ) (E₀ : Set RecData) (u₀ : ℂ → ℝ) (ℋ : ℝ≥0 → MeasurableSpace Ω) :
    GW2Sdh.SchedChoice Ω where
  β := schedWordMapX κ c' x s L N hN θa
  E₀ := E₀
  σa := specOffset κ + θa * chiC κ
  kc := chiC κ
  u₀ := u₀
  ℋ := ℋ

/-- **The `hβ` hypothesis of `GW2Rz.schedInstX_good`** for `wmChoiceX`. -/
theorem wmChoiceX_targets {Ω : Type u} (κ : ℝ) (c' : BoundaryWord) (x : ℝ) (s : ℝ≥0) (L : List (ℝ × ℝ≥0))
    (N : ℕ) (hN : L.length = N) (θa : ℝ) (E₀ : Set RecData) (u₀ : ℂ → ℝ) (ℋ : ℝ≥0 → MeasurableSpace Ω) :
    Measurable (wmChoiceX κ c' x s L N hN θa E₀ u₀ ℋ).β ∧
      (range fun y => Supp8.Q3Stop.wordType κ ((wmChoiceX κ c' x s L N hN θa E₀ u₀ ℋ).β y)).Countable ∧
      ∀ y, ((wmChoiceX κ c' x s L N hN θa E₀ u₀ ℋ).β y).IsSorted :=
  schedWordMapX_targets κ c' x s L N hN θa κ

/-! ### The word read on ROOTX's record -/

section Inst

variable {Ω : Type*} {x₀ : ℝ} {sp : ℝ≥0} {W Wα : ℝ≥0 → Ω → ℝ} {ζα : Ω → ℝ≥0∞} {GT : Set Ω} {V : Ω → ℝ≥0∞}
  {T : ℝ≥0} {R : ℝ≥0 → Ω → ℝ} {γ α : Ω → ℝ≥0 → ℂ}

/-- **The root-`x` base word on ROOTX's record** is the re-centred root word flowed through the instance's own
relative stage records, between the root-`x` stage starts at the physical stage times (good event, before the
root-`x` contact, the joined physical driver equal to the explored driver up to `T`). -/
theorem baseWordX_augRecX (κ : ℝ) (c' : BoundaryWord) (hGT : ∀ ω ∈ GT, GW2Rz.PhysGoodX x₀ sp Wα ζα W γ α ω)
    (hs : 0 < sp) (hx : 0 ≤ x₀) (L : List (ℝ × ℝ≥0)) (N : ℕ) (hN : L.length = N) {xr : Ω → RecData} {ω : Ω}
    {P : Fin N → RecData} (hxr : xr ω = GW2Rd.stageEnc N (cfRec sp Wα ζα ω, P))
    (hRc : Continuous fun u => R u ω) (hR0 : R 0 ω = 0) (hω : ω ∈ GT) (hV : V ω ≠ ⊤)
    (hT : ∀ j < N, GW2Schedule.schedTime 0 L j ≤ T)
    (hjT : ∀ j < N, GW2Schedule.schedTime 0 L j ≤ Sec5.Prop513Schedule.lastTime 0 L)
    (hcon : ∀ j, 0 < j → j < N → (GW2Schedule.schedTime 0 L j : ℝ≥0∞) < GW2Rz.contactX x₀ sp γ α ω)
    (hagree : ∀ u ≤ T, RootJ31.joinedRead L (fun i => P (Fin.cast hN i)) u = W u ω) :
    baseWordX κ c' x₀ sp L N hN (GW2Rd.augRec xr (GW2Rz.stgPreRecX x₀ sp Wα ζα W GT V T R) ω) =
      GW2JDetR5.stageWord (κ := κ) (rootWordX κ c' x₀ sp) (progAngle L) N
        (pastOf (cfRec sp Wα ζα ω) (fun u => R u ω) (trueBdX x₀ sp Wα ζα W GT V L N T ω) N) := by
  unfold baseWordX
  rw [stageDec_augRecX_trueBd hGT hs hx L N hN hxr hRc hR0 hω hV hT hjT hcon hagree]

end Inst

/-! ### The label positions re-centred by ROOTX's reader -/

section Labels

variable {κ : ℝ} {c' : BoundaryWord} {x : ℝ} {s : ℝ≥0} {r : RecData}

/-- **Every label of the root-`x` root word** is the root `−baseRead`, a returned left mark, or a returned right
mark, re-centred by `baseRead`. -/
theorem mem_jumps_rootWordX {y : ℝ} (hy : y ∈ (rootWordX κ c' x s r).jumps) :
    y = -GW2Rz.baseRead x s r ∨
      (∃ i : Fin (flowLineNL c'.fn c'.jumps 0),
        y = labelL (rdrv r) (rtime r) (flowLineXL c'.fn c'.jumps 0 i) - GW2Rz.baseRead x s r) ∨
      ∃ j : Fin (flowLineNR c'.fn c'.jumps 0),
        y = labelR (rdrv r) (rtime r) (flowLineXR c'.fn c'.jumps 0 j) - GW2Rz.baseRead x s r := by
  have hy' : y + GW2Rz.baseRead x s r - rootOff x r ∈ (rootWord κ c' x r).jumps := by
    unfold rootWordX at hy
    unfold rootWord
    rw [Exist.StagedLaw.BoundaryWord.jumps_shiftW] at hy ⊢
    obtain ⟨w, hw, rfl⟩ := Finset.mem_image.1 hy
    exact Finset.mem_image.2 ⟨w, hw, by ring⟩
  rcases mem_jumps_rootWord hy' with h | ⟨i, h⟩ | ⟨j, h⟩
  · left; linarith
  · exact Or.inr (Or.inl ⟨i, by linarith⟩)
  · exact Or.inr (Or.inr ⟨j, by linarith⟩)

/-- The shift between the two root words' labels. -/
theorem mem_jumps_rootWordX_iff {y : ℝ} :
    y ∈ (rootWordX κ c' x s r).jumps ↔ y + GW2Rz.baseRead x s r - rootOff x r ∈ (rootWord κ c' x r).jumps := by
  unfold rootWordX rootWord
  rw [Exist.StagedLaw.BoundaryWord.jumps_shiftW, Exist.StagedLaw.BoundaryWord.jumps_shiftW]
  constructor
  · rintro hy
    obtain ⟨w, hw, rfl⟩ := Finset.mem_image.1 hy
    exact Finset.mem_image.2 ⟨w, hw, by ring⟩
  · rintro hy
    obtain ⟨w, hw, hwy⟩ := Finset.mem_image.1 hy
    exact Finset.mem_image.2 ⟨w, hw, by linarith⟩

/-- **Each returned left mark, re-centred by `baseRead`, is a label of the root-`x` root word.** -/
theorem labelL_mem_jumps_rootWordX (i : Fin (flowLineNL c'.fn c'.jumps 0)) :
    labelL (rdrv r) (rtime r) (flowLineXL c'.fn c'.jumps 0 i) - GW2Rz.baseRead x s r ∈
      (rootWordX κ c' x s r).jumps := by
  rw [mem_jumps_rootWordX_iff]
  convert labelL_mem_jumps_rootWord (κ := κ) (x := x) (r := r) i using 1
  ring

/-- **Each returned right mark, re-centred by `baseRead`, is a label of the root-`x` root word.** -/
theorem labelR_mem_jumps_rootWordX (j : Fin (flowLineNR c'.fn c'.jumps 0)) :
    labelR (rdrv r) (rtime r) (flowLineXR c'.fn c'.jumps 0 j) - GW2Rz.baseRead x s r ∈
      (rootWordX κ c' x s r).jumps := by
  rw [mem_jumps_rootWordX_iff]
  convert labelR_mem_jumps_rootWord (κ := κ) (x := x) (r := r) j using 1
  ring

/-- **The tail junctions bound all labels of the root-`x` root word** (re-centred by `baseRead`). -/
theorem rootWordX_label_bounds (hpos : 0 < markPos (rdrv r) (rtime r) 0)
    (hneg : markPosL (rdrv r) (rtime r) 0 < 0) {y : ℝ} (hy : y ∈ (rootWordX κ c' x s r).jumps) :
    labelR (rdrv r) (rtime r) 0 - GW2Rz.baseRead x s r ≤ y ∧
      y ≤ labelL (rdrv r) (rtime r) 0 - GW2Rz.baseRead x s r := by
  have h := rootWord_label_bounds (κ := κ) (c' := c') (x := x) hpos hneg (mem_jumps_rootWordX_iff.1 hy)
  constructor <;> linarith [h.1, h.2]

end Labels

end InteractingSLE.Theorem14.GW2Wm
