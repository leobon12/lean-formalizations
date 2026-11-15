/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW2WmFar
import InteractingSLE.Spec.Supplement.GW2StlWord
import InteractingSLE.Spec.Supplement.GW2SfChart

/-!
# GW2's stage word map, part 2: the root word at a root `x`, the word map and its `Good` targets

Packet PROVE-GW2-GEOM2 (round 7; D8/D9 of DECISIONS-FABLE-2). The stage chart at a root `x` is
`((relChart rec).recenter (relBase x s rec)).loewner R a` (D8). Its word at the root (before any piece) is GW2's joint
word with R62's offset, `jointWordOfRec (specOffset κ) κ c′ rec` (the coefficients `1, specOffset κ + θχ, χ` of
`GW2RdSafeData`, the angle entering through the raise `upW (θχ)`), re-centred at the root's chart image. After the
earlier pieces it is the FLOWED word: every stopped piece flows it by `stopWord κ (·, θ_j, record_j)`
(`GW2JDetR5.stageWord`, counterflow first, pieces last).

* `rootOff x r`: a measurable reader of the root's chart image, `−1/Re f_s(−1/x)` (`0` at `x = 0`);
  **`rootOff_eq_relBdry`**: it is `Re relBdry (rdrv r) (rtime r) x = GW2Bf.relBase x s (r, ·)` at an untouched root
  (`GW2Sf.relBdry_of_real`, `CoordB.relBdry_zero`); `measurable_rootOff`;
* **`rootWord κ c′ x r`** `= shiftW (rootOff x r) (jointWordOfRec (specOffset κ) κ c′ r)`: measurable, sorted, of one
  finite shape (`exists_hasShape_rootWord`); `rootWord_zero` (at `x = 0` it is the joint word);
* **`baseWord κ c′ x θ n dec y`** `= stageWord (rootWord κ c′ x) θ n (dec y)` and the **word map**
  `wordMap κ c′ x θ n θa dec y = upW (θa χ) (baseWord … y)` for a measurable decoder `dec` of the stage record into
  the complete retained past (root record and the `n` stopped piece records);
* **`wordMap_targets`**: `Measurable`, countably many word types, sorted (the three `Good` targets of
  `GW2Sde.StageInst.Good` / `SchedChoice`);
* **`farL_baseWord`**, **`farR_baseWord`**, **`totals_half_pi_baseWord`**, **`totals_neg_half_pi_baseWord`**: the
  base word has far heights `−λ′ + πχ`, `λ′ − πχ` and both totals separately, `(κ − 4, κ/2 − 2)` at `π/2` and
  `(κ/2 − 2, κ − 4)` at `−π/2` (D9's check), as soon as the root record's counterflow hull has positive extent on
  both sides; `farL_wordMap`, `farR_wordMap` for the raised word.

Deterministic.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Filter MeasureTheory Topology
open scoped NNReal ENNReal
open QuantumZipper (chiC fwdMap)

namespace InteractingSLE.Theorem14.GW2Wm

open Restart Exist.Staged Exist.StagedLaw Sec7.StripSysField GW2JointKernel GW2TipStage

/-! ### The root's chart image -/

/-- **A measurable reader of the root's chart image**: `−1/Re f_s(−1/x)` for `x ≠ 0`, `0` at `x = 0`. -/
def rootOff (x : ℝ) (r : RecData) : ℝ :=
  if x = 0 then 0 else -((fwdMap (rdrv r) (rtime r) ((-x⁻¹ : ℝ) : ℂ)).re)⁻¹

theorem measurable_rootOff (x : ℝ) : Measurable (rootOff x) := by
  unfold rootOff
  split_ifs
  · exact measurable_const
  · have h := (Exist.StagedLaw.measurable_fwdMap_param (W := rdrv) (fun r => continuous_rdrv r)
      (fun t => measurable_rdrv_apply t) rdrv_zero measurable_rtime (fun r => rtime_nonneg r)
      (measurable_const (a := ((-x⁻¹ : ℝ) : ℂ)))).1
    exact (Complex.measurable_re.comp h).inv.neg

/-- **The reader is the root's chart image** `Re relBdry (rdrv r) (rtime r) x` (ROOTX's `GW2Bf.relBase x s (r, ·)`)
at a root off the closed retained hull. -/
theorem rootOff_eq_relBdry (x : ℝ) (r : RecData)
    (hxA : (x : ℂ) ∉ closure (Supp8.Q3Rel.invHull (rdrv r) (rtime r))) :
    rootOff x r = (Supp8.GB6.CoordB.relBdry (rdrv r) (rtime r) (x : ℂ)).re := by
  unfold rootOff
  split_ifs with hx
  · subst hx
    rw [Complex.ofReal_zero, Supp8.GB6.CoordB.relBdry_zero (continuous_rdrv r) (rdrv_zero r) (rtime_nonneg r),
      Complex.zero_re]
  · rw [GW2Sf.relBdry_of_real (continuous_rdrv r) (rdrv_zero r) (rtime_nonneg r) hx hxA, Complex.ofReal_re]

/-! ### The root word -/

/-- **The root word at the root `x`**: GW2's joint word with R62's offset, re-centred at the root's chart image. -/
def rootWord (κ : ℝ) (c' : BoundaryWord) (x : ℝ) (r : RecData) : BoundaryWord :=
  Exist.StagedLaw.BoundaryWord.shiftW (rootOff x r) (jointWordOfRec (specOffset κ) κ c' r)

theorem rootWord_zero (κ : ℝ) (c' : BoundaryWord) (r : RecData) :
    rootWord κ c' 0 r = jointWordOfRec (specOffset κ) κ c' r := by
  unfold rootWord rootOff Exist.StagedLaw.BoundaryWord.shiftW
  simp only [↓reduceIte, sub_zero]

theorem measurable_rootWord (κ : ℝ) (c' : BoundaryWord) (x : ℝ) : Measurable (rootWord κ c' x) :=
  Exist.StagedLaw.BoundaryWord.measurable_shiftW.comp
    ((measurable_rootOff x).prodMk (measurable_jointWordOfRec _ _ _))

theorem isSorted_rootWord (κ : ℝ) (c' : BoundaryWord) (x : ℝ) (r : RecData) : (rootWord κ c' x r).IsSorted :=
  Exist.StagedLaw.BoundaryWord.isSorted_shiftW (isSorted_jointWordOfRec _ _ _ _) _

/-- **The root words have one finite shape** (the joint word's heights are returned heights of one finite set of
stop-word heights; its length is at most one more than the stop word's). -/
theorem exists_hasShape_rootWord (κ : ℝ) (c' : BoundaryWord) (x : ℝ) :
    ∃ H₀ : Set ℝ, H₀.Finite ∧ ∃ N₀ : ℕ, ∀ r, GW2Stl.HasShape H₀ N₀ (rootWord κ c' x r) := by
  have hc' : GW2Stl.HasShape ((fun j => c'.2.2 j) '' Iic c'.1) c'.1 c' := ⟨fun j hj => ⟨j, hj, rfl⟩, le_rfl⟩
  obtain ⟨H', hH', hst⟩ := GW2Stl.exists_hasShape_stopWord (16 / κ) 0 ((finite_Iic c'.1).image _) c'.1
  refine ⟨(fun p : ℝ × ℝ => -p.1 + (retA κ + specOffset κ) + retL κ * p.2) ''
    (H' ×ˢ ({-(2 * Real.pi), 0} : Set ℝ)), (hH'.prod (toFinite _)).image _, 2 * c'.1 + 3 + 1, fun r => ?_⟩
  have hg := hst c' hc' r
  refine ⟨fun j _ => ?_, ?_⟩
  · refine ⟨((stopWord (16 / κ) (c', 0, r)).fn
        (-(midPt (retCount (stopWord (16 / κ) (c', 0, r))) (retPos (stopWord (16 / κ) (c', 0, r))) j)⁻¹),
      liftBoundary (midPt (retCount (stopWord (16 / κ) (c', 0, r))) (retPos (stopWord (16 / κ) (c', 0, r))) j)),
      ⟨hg.1 _ (BoundaryWord.index_le _ _), ?_⟩, rfl⟩
    unfold liftBoundary
    split_ifs
    · exact mem_insert _ _
    · exact mem_insert_of_mem _ rfl
  · change retCount (stopWord (16 / κ) (c', 0, r)) ≤ _
    have h1 := hg.2
    have h2 := nNeg_le_nNP (stopWord (16 / κ) (c', 0, r))
    have h3 := nPos_add_nNP (stopWord (16 / κ) (c', 0, r))
    unfold retCount
    omega

/-- The root word's far-left height (R62's offset). -/
theorem farL_rootWord {κ : ℝ} (hκ : 0 < κ) (c' : BoundaryWord) (x : ℝ) (r : RecData)
    (hpos : 0 < markPos (rdrv r) (rtime r) 0) :
    FarL (rootWord κ c' x r) (-sleLambda (16 / κ) + Real.pi * chiC κ) :=
  farL_shiftW _ (farL_jointWordOfRec hκ c' r hpos)

/-- The root word's far-right height (R62's offset). -/
theorem farR_rootWord {κ : ℝ} (hκ : 0 < κ) (c' : BoundaryWord) (x : ℝ) (r : RecData)
    (hneg : markPosL (rdrv r) (rtime r) 0 < 0) :
    FarR (rootWord κ c' x r) (sleLambda (16 / κ) - Real.pi * chiC κ) :=
  farR_shiftW _ (farR_jointWordOfRec hκ c' r hneg)

/-! ### The base word and the word map -/

/-- **The base stage word**: the root word at `x` flowed through the `n` stopped pieces decoded from the record. -/
def baseWord (κ : ℝ) (c' : BoundaryWord) (x : ℝ) (θ : ℕ → ℝ) (n : ℕ) (dec : RecData → GW2JDetR5.Past RecData n)
    (y : RecData) : BoundaryWord :=
  GW2JDetR5.stageWord (κ := κ) (rootWord κ c' x) θ n (dec y)

/-- **The stage word map**: the base stage word raised by the current angle `θa` (`upW (θa χ)`). -/
def wordMap (κ : ℝ) (c' : BoundaryWord) (x : ℝ) (θ : ℕ → ℝ) (n : ℕ) (θa : ℝ)
    (dec : RecData → GW2JDetR5.Past RecData n) (y : RecData) : BoundaryWord :=
  GW2Rd.upW (θa * chiC κ) (baseWord κ c' x θ n dec y)

/-- **The three `Good` targets of the word map**: measurable, countably many word types, sorted. -/
theorem wordMap_targets (κ : ℝ) (c' : BoundaryWord) (x : ℝ) (θ : ℕ → ℝ) (n : ℕ) (θa : ℝ)
    {dec : RecData → GW2JDetR5.Past RecData n} (hdec : Measurable dec) (k : ℝ) :
    Measurable (wordMap κ c' x θ n θa dec) ∧
      (range fun y => Supp8.Q3Stop.wordType k (wordMap κ c' x θ n θa dec y)).Countable ∧
      ∀ y, (wordMap κ c' x θ n θa dec y).IsSorted := by
  obtain ⟨H₀, hH₀, N₀, hW₀⟩ := exists_hasShape_rootWord κ c' x
  exact GW2Stl.stageWordMap_targets κ (measurable_rootWord κ c' x) (isSorted_rootWord κ c' x) hH₀ hW₀ θ n
    (θa * chiC κ) hdec k

/-- **The base word's far-left height** `−λ′ + πχ` (R62's offset). -/
theorem farL_baseWord {κ : ℝ} (hκ : 0 < κ) (c' : BoundaryWord) (x : ℝ) (θ : ℕ → ℝ) (n : ℕ)
    (dec : RecData → GW2JDetR5.Past RecData n) (y : RecData)
    (hpos : 0 < markPos (rdrv (pastRoot n (dec y))) (rtime (pastRoot n (dec y))) 0) :
    FarL (baseWord κ c' x θ n dec y) (-sleLambda (16 / κ) + Real.pi * chiC κ) :=
  farL_stageWord (S := RecData) hκ θ (A₀ := {r | 0 < markPos (rdrv r) (rtime r) 0})
    (fun r hr => farL_rootWord hκ c' x r hr) n (dec y) hpos

/-- **The base word's far-right height** `λ′ − πχ` (R62's offset). -/
theorem farR_baseWord {κ : ℝ} (hκ : 0 < κ) (c' : BoundaryWord) (x : ℝ) (θ : ℕ → ℝ) (n : ℕ)
    (dec : RecData → GW2JDetR5.Past RecData n) (y : RecData)
    (hneg : markPosL (rdrv (pastRoot n (dec y))) (rtime (pastRoot n (dec y))) 0 < 0) :
    FarR (baseWord κ c' x θ n dec y) (sleLambda (16 / κ) - Real.pi * chiC κ) :=
  farR_stageWord (S := RecData) hκ θ (A₀ := {r | markPosL (rdrv r) (rtime r) 0 < 0})
    (fun r hr => farR_rootWord hκ c' x r hr) n (dec y) hneg

/-- **D9's check, leftward**: the base word's angle-`π/2` totals are `κ − 4` and `κ/2 − 2`, separately. -/
theorem totals_half_pi_baseWord {κ : ℝ} (hκ : 0 < κ) (c' : BoundaryWord) (x : ℝ) (θ : ℕ → ℝ) (n : ℕ)
    (dec : RecData → GW2JDetR5.Past RecData n) (y : RecData)
    (hpos : 0 < markPos (rdrv (pastRoot n (dec y))) (rtime (pastRoot n (dec y))) 0)
    (hneg : markPosL (rdrv (pastRoot n (dec y))) (rtime (pastRoot n (dec y))) 0 < 0) :
    ∑ i, flowLineRhoL κ (baseWord κ c' x θ n dec y).fn (baseWord κ c' x θ n dec y).jumps 0 (Real.pi / 2) i =
        κ - 4 ∧
      ∑ j, flowLineRhoR κ (baseWord κ c' x θ n dec y).fn (baseWord κ c' x θ n dec y).jumps 0 (Real.pi / 2) j =
        κ / 2 - 2 :=
  totals_half_pi_of_far hκ (farL_baseWord hκ c' x θ n dec y hpos) (farR_baseWord hκ c' x θ n dec y hneg)

/-- **D9's check, rightward**: the base word's angle-`−π/2` totals are `κ/2 − 2` and `κ − 4`, separately. -/
theorem totals_neg_half_pi_baseWord {κ : ℝ} (hκ : 0 < κ) (c' : BoundaryWord) (x : ℝ) (θ : ℕ → ℝ) (n : ℕ)
    (dec : RecData → GW2JDetR5.Past RecData n) (y : RecData)
    (hpos : 0 < markPos (rdrv (pastRoot n (dec y))) (rtime (pastRoot n (dec y))) 0)
    (hneg : markPosL (rdrv (pastRoot n (dec y))) (rtime (pastRoot n (dec y))) 0 < 0) :
    ∑ i, flowLineRhoL κ (baseWord κ c' x θ n dec y).fn (baseWord κ c' x θ n dec y).jumps 0 (-(Real.pi / 2)) i =
        κ / 2 - 2 ∧
      ∑ j, flowLineRhoR κ (baseWord κ c' x θ n dec y).fn (baseWord κ c' x θ n dec y).jumps 0 (-(Real.pi / 2)) j =
        κ - 4 :=
  totals_neg_half_pi_of_far hκ (farL_baseWord hκ c' x θ n dec y hpos) (farR_baseWord hκ c' x θ n dec y hneg)

/-- The raised word's far-left height. -/
theorem farL_wordMap {κ : ℝ} (hκ : 0 < κ) (c' : BoundaryWord) (x : ℝ) (θ : ℕ → ℝ) (n : ℕ) (θa : ℝ)
    (dec : RecData → GW2JDetR5.Past RecData n) (y : RecData)
    (hpos : 0 < markPos (rdrv (pastRoot n (dec y))) (rtime (pastRoot n (dec y))) 0) :
    FarL (wordMap κ c' x θ n θa dec y) (-sleLambda (16 / κ) + Real.pi * chiC κ + θa * chiC κ) :=
  farL_upW _ (farL_baseWord hκ c' x θ n dec y hpos)

/-- The raised word's far-right height. -/
theorem farR_wordMap {κ : ℝ} (hκ : 0 < κ) (c' : BoundaryWord) (x : ℝ) (θ : ℕ → ℝ) (n : ℕ) (θa : ℝ)
    (dec : RecData → GW2JDetR5.Past RecData n) (y : RecData)
    (hneg : markPosL (rdrv (pastRoot n (dec y))) (rtime (pastRoot n (dec y))) 0 < 0) :
    FarR (wordMap κ c' x θ n θa dec y) (sleLambda (16 / κ) - Real.pi * chiC κ + θa * chiC κ) :=
  farR_upW _ (farR_baseWord hκ c' x θ n dec y hneg)

end InteractingSLE.Theorem14.GW2Wm
