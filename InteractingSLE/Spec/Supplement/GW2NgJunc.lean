/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW2NgWord
import InteractingSLE.Spec.Supplement.GW2SdpInv

/-!
# The counterflow junction of a stage word, and the far height beyond it (D78)

Packet PROVE-GW2-NEARIMG2, decision D78. In the relative chart of the root word (`jointWordOfRec`, the counterflow
tip at `∞`), the counterflow's right side is the ray beyond the right junction `jR = −1/markPosL(0)` (GB6's
`jROfRec`): there the word has the far height `λ′ − πχ`. The root-`x` word is re-centred at the root's image
(`shiftW (baseRead …)`), and every past piece moves the junction to its Loewner image `markPos`. This file tracks it:

* `FarRAt c h J`: the word equals `h` on `(J, ∞)` off its jumps (with `FarRAt.mono`);
* `farRAt_jointWordOfRec`, `farRAt_shiftW`, **`farRAt_stopWord`**: the root word, the re-centring, a stopped piece;
* `cfJunction`: the junction carried along a past (as SDE's `junctionR`, but started at the counterflow junction, not
  at the root point);
* **`farRAt_stageWord`**, **`farRAt_schedWordMapX`**: the instance's stage word equals `λ′ − πχ + θa χ` beyond the
  tracked junction `cfJunctionX`;
* **`farJunctionX`** `= max (cfJunctionX) 1`: a positive point at or beyond the junction, with the far height beyond it
  (`farJunctionX_pos`, `farRAt_farJunctionX`). This is the `y > 0` for `FlowSwallowStatement`: a swallow of a point
  at or beyond the junction is a hit of the counterflow side.

**Not SDE's `junctionR`.** Round 32's `FarJunction` reads SDE's `junctionR`, the image of the root POINT along the
past. It is `0` at the root stage, and on `(junctionR, ∞)` the stage word carries the root word's heights, including
the source boundary between the root and the counterflow junction. So a swallow of SDE's `junctionR` is not a contact
with the counterflow; the tracked `cfJunction` is.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set
open scoped NNReal ENNReal
open QuantumZipper (chiC)

universe v

namespace InteractingSLE.Theorem14.GW2Ni

open Restart Exist.Staged Exist.StagedLaw Supp8.GB6 Sec7.StripSysField GW2JointKernel GW1W GW2TipStage GW2Wm

/-- **The far-right height beyond a given point**: the word equals `h` on `(J, ∞)`, off its jumps. -/
def FarRAt (c : BoundaryWord) (h J : ℝ) : Prop := ∀ z, J < z → z ∉ c.jumps → c.fn z = h

theorem FarRAt.mono {c : BoundaryWord} {h J J' : ℝ} (hc : FarRAt c h J) (hJ : J ≤ J') : FarRAt c h J' :=
  fun z hz hzJ => hc z (hJ.trans_lt hz) hzJ

theorem FarRAt.farR {c : BoundaryWord} {h J : ℝ} (hc : FarRAt c h J) : FarR c h := ⟨J, hc⟩

/-- **The root word has the far height beyond the counterflow's right junction** `jR = −1/markPosL(0)`. -/
theorem farRAt_jointWordOfRec {κ : ℝ} (hκ : 0 < κ) (c' : BoundaryWord) (r : RecData)
    (hneg : markPosL (rdrv r) (rtime r) 0 < 0) :
    FarRAt (jointWordOfRec (specOffset κ) κ c' r) (sleLambda (16 / κ) - Real.pi * chiC κ) (jROfRec r) := by
  intro y hy hyJ
  have hm : (markPosL (rdrv r) (rtime r) 0)⁻¹ < 0 := inv_lt_zero.2 hneg
  have hy' : -(markPosL (rdrv r) (rtime r) 0)⁻¹ < y := hy
  have hy0 : 0 < y := by linarith
  have hgs := isSorted_stopWord (16 / κ) (c', 0, r)
  unfold jointWordOfRec at hyJ ⊢
  rw [fn_retWord hgs _ _ hyJ]
  have hz0 : -y⁻¹ < 0 := neg_neg_of_pos (inv_pos.2 hy0)
  have hzm : markPosL (rdrv r) (rtime r) 0 < -y⁻¹ := by
    have h1 : (-markPosL (rdrv r) (rtime r) 0)⁻¹ < y := by rw [inv_neg]; linarith
    have h2 : y⁻¹ < -markPosL (rdrv r) (rtime r) 0 := inv_lt_of_inv_lt₀ (neg_pos.2 hneg) h1
    linarith
  have hzJ : -y⁻¹ ∉ (stopWord (16 / κ) (c', 0, r)).jumps := fun h => hyJ (neg_inv_mem_jumps_retWord hgs _ _ h)
  unfold returnData liftBoundary
  rw [Supp8.GB6.stopWord_fn_flank_left c' 0 r hzm hz0 hzJ,
    ite_eq_right_of_eq_false _ _ (eq_false (not_lt.2 hy0.le)), retA_add_specOffset hκ]
  ring

/-- Re-centring moves the point. -/
theorem farRAt_shiftW {c : BoundaryWord} {h J : ℝ} (a : ℝ) (hc : FarRAt c h J) :
    FarRAt (BoundaryWord.shiftW a c) h (J - a) := fun z hz hzJ => by
  rw [BoundaryWord.fn_shiftW]
  exact hc _ (by linarith) (add_notMem_jumps_of_notMem_shiftW hzJ)

/-- Raising adds the constant. -/
theorem farRAt_upW {c : BoundaryWord} {h J : ℝ} (a : ℝ) (hc : FarRAt c h J) : FarRAt (GW2Rd.upW a c) (h + a) J :=
  fun z hz hzJ => by rw [fn_upW, hc z hz hzJ]

/-- **A stopped piece carries the point to its Loewner image** `markPos`. -/
theorem farRAt_stopWord {κ : ℝ} (hκ : 0 < κ) {c : BoundaryWord} {h b : ℝ} (hc : FarRAt c h b) (hb : 0 ≤ b)
    (θ : ℝ) (r : RecData) : FarRAt (stopWord κ (c, θ, r)) h (markPos (rdrv r) (rtime r) b) := by
  intro z hz hzJ
  have hm := Sec7.StripSideHeightProb.markPos_nonneg (continuous_rdrv r) (rdrv_zero r) (rtime_nonneg r) hb
  obtain ⟨y, hby, hyJ, hfn⟩ := (GW2Sdp.fn_stopWord_right hκ c θ r hb (hm.trans_lt hz) hzJ).2 hz
  rw [hfn]
  exact hc y hby hyJ

/-! ### The junction along a past -/

section Past

variable {S : Type v}

/-- **The counterflow junction carried along a past**: started at `J₀` of the past's root, moved by `markPos`. -/
def cfJunction (J₀ : S → ℝ) : (n : ℕ) → GW2JDetR5.Past S n → ℝ
  | 0 => J₀
  | n + 1 => fun x => markPos (rdrv x.2) (rtime x.2) (cfJunction J₀ n x.1)

theorem cfJunction_nonneg {J₀ : S → ℝ} (hJ₀ : ∀ r, 0 ≤ J₀ r) : ∀ n (x : GW2JDetR5.Past S n), 0 ≤ cfJunction J₀ n x
  | 0, x => hJ₀ x
  | n + 1, x => Sec7.StripSideHeightProb.markPos_nonneg (continuous_rdrv x.2) (rdrv_zero x.2) (rtime_nonneg x.2)
      (cfJunction_nonneg hJ₀ n x.1)

/-- **Every stage word has the far height beyond the carried junction.** -/
theorem farRAt_stageWord {κ : ℝ} (hκ : 0 < κ) {W₀ : S → BoundaryWord} (θ : ℕ → ℝ) {A₀ : Set S} {h : ℝ}
    {J₀ : S → ℝ} (hJ₀ : ∀ r, 0 ≤ J₀ r) (h0 : ∀ r ∈ A₀, FarRAt (W₀ r) h (J₀ r)) :
    ∀ n (x : GW2JDetR5.Past S n), pastRoot n x ∈ A₀ →
      FarRAt (GW2JDetR5.stageWord (κ := κ) W₀ θ n x) h (cfJunction J₀ n x)
  | 0, x, hx => h0 x hx
  | n + 1, x, hx => farRAt_stopWord hκ (farRAt_stageWord hκ θ hJ₀ h0 n x.1 hx)
      (cfJunction_nonneg hJ₀ n x.1) (θ n) x.2

end Past

/-! ### The instance's stage word -/

/-- The counterflow junction of the root-`x` root word (re-centred at the root's image; clipped at `0`). -/
def cfJunctionRootX (x : ℝ) (s : ℝ≥0) (r : RecData) : ℝ := max (jROfRec r - GW2Rz.baseRead x s r) 0

/-- **The counterflow junction of the instance's stage word.** -/
def cfJunctionX (x : ℝ) (s : ℝ≥0) (L : List (ℝ × ℝ≥0)) (N : ℕ) (hN : L.length = N) (y : RecData) : ℝ :=
  cfJunction (cfJunctionRootX x s) N (stageDec x s L N hN y)

/-- **The instance's stage word has the raised far height beyond its counterflow junction.** -/
theorem farRAt_schedWordMapX {κ : ℝ} (hκ : 0 < κ) (c' : BoundaryWord) (x : ℝ) (s : ℝ≥0) (L : List (ℝ × ℝ≥0))
    (N : ℕ) (hN : L.length = N) (θa : ℝ) (y : RecData)
    (hneg : markPosL (rdrv (decHist N y).1) (rtime (decHist N y).1) 0 < 0) :
    FarRAt (schedWordMapX κ c' x s L N hN θa y) (sleLambda (16 / κ) - Real.pi * chiC κ + θa * chiC κ)
      (cfJunctionX x s L N hN y) := by
  have hroot : ∀ r ∈ {r : RecData | markPosL (rdrv r) (rtime r) 0 < 0},
      FarRAt (rootWordX κ c' x s r) (sleLambda (16 / κ) - Real.pi * chiC κ) (cfJunctionRootX x s r) := by
    intro r hr
    exact (farRAt_shiftW _ (farRAt_jointWordOfRec hκ c' r hr)).mono (le_max_left _ _)
  unfold schedWordMapX baseWordX cfJunctionX
  exact farRAt_upW _ (farRAt_stageWord hκ (W₀ := rootWordX κ c' x s) (progAngle L)
    (J₀ := cfJunctionRootX x s) (fun r => le_max_right _ _) hroot N (stageDec x s L N hN y)
    (by rw [pastRoot_stageDec]; exact hneg))

/-- **A positive point at or beyond the counterflow junction**: the `y` of `FlowSwallowStatement`. -/
def farJunctionX (x : ℝ) (s : ℝ≥0) (L : List (ℝ × ℝ≥0)) (N : ℕ) (hN : L.length = N) (y : RecData) : ℝ :=
  max (cfJunctionX x s L N hN y) 1

theorem farJunctionX_pos (x : ℝ) (s : ℝ≥0) (L : List (ℝ × ℝ≥0)) (N : ℕ) (hN : L.length = N) (y : RecData) :
    0 < farJunctionX x s L N hN y :=
  lt_of_lt_of_le one_pos (le_max_right _ _)

theorem cfJunctionX_le_farJunctionX (x : ℝ) (s : ℝ≥0) (L : List (ℝ × ℝ≥0)) (N : ℕ) (hN : L.length = N)
    (y : RecData) : cfJunctionX x s L N hN y ≤ farJunctionX x s L N hN y :=
  le_max_left _ _

theorem farRAt_farJunctionX {κ : ℝ} (hκ : 0 < κ) (c' : BoundaryWord) (x : ℝ) (s : ℝ≥0) (L : List (ℝ × ℝ≥0))
    (N : ℕ) (hN : L.length = N) (θa : ℝ) (y : RecData)
    (hneg : markPosL (rdrv (decHist N y).1) (rtime (decHist N y).1) 0 < 0) :
    FarRAt (schedWordMapX κ c' x s L N hN θa y) (sleLambda (16 / κ) - Real.pi * chiC κ + θa * chiC κ)
      (farJunctionX x s L N hN y) :=
  (farRAt_schedWordMapX hκ c' x s L N hN θa y hneg).mono (cfJunctionX_le_farJunctionX x s L N hN y)

/-- `gb6TS` (part of `goodX`) gives the counterflow's positive extent on the left. -/
theorem markPosL_neg_of_mem_gb6TS {s' : ℝ≥0} {r : RecData} (hr : r ∈ gb6TS s') :
    markPosL (rdrv r) (rtime r) 0 < 0 :=
  hr.2.2.2

/-- **The two premises of `FlowSwallowStatement` for the instance's stage word** (D78): the point
`farJunctionX` (at or beyond the counterflow junction) is positive, and the total right weight is `< κ/2 − 2`; the
word has the far height beyond that point. Hypotheses: an angle below `π/2` and a past whose counterflow record has
positive extent on the left. -/
theorem flowSwallow_premises_schedWordMapX {κ : ℝ} (hκ : 0 < κ) (hκ4 : κ < 4) (c' : BoundaryWord) (x : ℝ)
    (s : ℝ≥0) (L : List (ℝ × ℝ≥0)) (N : ℕ) (hN : L.length = N) {θa : ℝ} (hθ : θa < Real.pi / 2) (y : RecData)
    (hneg : markPosL (rdrv (decHist N y).1) (rtime (decHist N y).1) 0 < 0) :
    0 < farJunctionX x s L N hN y ∧
      ∑ j, flowLineRhoR κ (schedWordMapX κ c' x s L N hN θa y).fn (schedWordMapX κ c' x s L N hN θa y).jumps 0 0 j <
        κ / 2 - 2 ∧
      FarRAt (schedWordMapX κ c' x s L N hN θa y) (sleLambda (16 / κ) - Real.pi * chiC κ + θa * chiC κ)
        (farJunctionX x s L N hN y) :=
  ⟨farJunctionX_pos x s L N hN y, sum_flowLineRhoR_schedWordMapX_lt hκ hκ4 c' x s L N hN hθ y hneg,
    farRAt_farJunctionX hκ c' x s L N hN θa y hneg⟩

/-- The premises with the angle in the source's open range and the past's counterflow record in `gb6TS`. -/
theorem flowSwallow_premises_schedWordMapX_of_mem {κ : ℝ} (hκ : 0 < κ) (hκ4 : κ < 4) (c' : BoundaryWord) (x : ℝ)
    (s : ℝ≥0) (L : List (ℝ × ℝ≥0)) (N : ℕ) (hN : L.length = N) {θa : ℝ}
    (hθ : θa ∈ Ioo (-(Real.pi / 2)) (Real.pi / 2)) (y : RecData) {s' : ℝ≥0} (hrec : (decHist N y).1 ∈ gb6TS s') :
    0 < farJunctionX x s L N hN y ∧
      ∑ j, flowLineRhoR κ (schedWordMapX κ c' x s L N hN θa y).fn (schedWordMapX κ c' x s L N hN θa y).jumps 0 0 j <
        κ / 2 - 2 ∧
      FarRAt (schedWordMapX κ c' x s L N hN θa y) (sleLambda (16 / κ) - Real.pi * chiC κ + θa * chiC κ)
        (farJunctionX x s L N hN y) :=
  flowSwallow_premises_schedWordMapX hκ hκ4 c' x s L N hN hθ.2 y (markPosL_neg_of_mem_gb6TS hrec)

end InteractingSLE.Theorem14.GW2Ni
