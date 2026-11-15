/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW2NjRel
import InteractingSLE.Spec.Sec5.Prop59NodeTreeFlow
import InteractingSLE.Spec.Supplement.SB2CxMark
import InteractingSLE.Spec.Supplement.GW2NuConv
import InteractingSLE.Spec.Sec5.CrossCondGenCloseMarks
import InteractingSLE.Spec.Supplement.GB6LifeBase
import InteractingSLE.Spec.Supplement.GW2GmBack
import InteractingSLE.Spec.Supplement.GW2BjImg

/-!
# The counterflow's right side is `[cfJunction, ∞)` in the stage chart (D81, part 3)

Packet PROVE-GW2-NEARIMG2, decision D81. The stage chart maps out the past of the relative driver `R` up to the stage
start `b N` (the decoded past `GW2Wm.pastOf cf R b N`, records of `stgDrv R (b j)` between the boundaries). Then:

* **`cfJunction_pastOf`**: the counterflow junction carried along the decoded past is the right mark of `J₀` for `R`
  at the stage start, `markPos R (b N) J₀` (`markPos` composes along shifted drivers, `SB.Cx.markPos_shiftDrive`);
* **`alive_shiftDrv_of_markPos_lt`**: if every real point beyond `J₀` stays alive for `R`, every real point beyond
  `markPos R a₀ J₀` stays alive for the stage driver `R(a₀ + ·) − R(a₀)` (`Prop59NodeTree.alive_shift`, and a point
  right of an alive point is alive);
* **`aliveRead_stgDrv_of_cfJunction_lt`**: hence, for the stage driver `stgDrv R (b N)`, every `q > cfJunction`
  satisfies `GW2Bh.aliveRead n q` at every `n` — the form RELDET's `BadCode` reads;
* **`aliveRead_stgDrv_cDrv`**: the instance for the glued relative driver `cDrv` of a contact with an unbounded
  relative clock (a first contact at the counterflow's tip): the hypothesis "alive beyond `J₀`" is
  `alive_cDrv_of_gt` (`GW2NjRel`).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Filter Topology MeasureTheory
open scoped NNReal ENNReal
open QuantumZipper (H Hbar fwdHull)

namespace InteractingSLE.Theorem14.GW2Ni

open Exist Staged StagedLaw Restart Supp8.GB6 Supp8.GB6.CoordB GW2TipSystem GW2Rz GW2Wm
open MartChar.RealFlow

/-! ### Transport to the stage driver -/

/-- **Beyond the stage-start image of the junction, every point stays alive for the stage driver.** -/
theorem alive_shiftDrv_of_markPos_lt {W : ℝ → ℝ} (hW : Continuous W) (hW0 : W 0 = 0) {J₀ a₀ u : ℝ} (ha₀ : 0 ≤ a₀)
    (hu : 0 ≤ u) (hJ₀ : 0 ≤ J₀) (halive : ∀ p, J₀ < p → Alive W p (a₀ + u)) {q : ℝ} (hq : markPos W a₀ J₀ < q) :
    Alive (Sec5.Prop59NodeTree.shiftDrv W a₀) q u := by
  have hm := Sec5.CrossCond.Gen.markPos_eq_rightImg_of_nonneg hW hW0 ha₀ hJ₀
  have hlt : rightImg W J₀ a₀ < q + W a₀ := by linarith
  obtain ⟨r₀, hJr, -, hgr⟩ := exists_lt_of_rightImg_lt hW ha₀ hlt
  obtain ⟨hsh, -⟩ := Sec5.Prop59NodeTree.alive_shift hW ha₀ hu (halive r₀ hJr)
  have hcf : cflow W r₀ a₀ ≤ q := by
    unfold gImg at hgr
    linarith
  exact GW2Nu.alive_of_le_point (Sec5.Prop59NodeTree.continuous_shiftDrv hW a₀) hu hsh hcf

/-! ### The junction along a decoded past -/

/-- A piece record of the decoded past reads the shifted driver. -/
theorem markPos_stgRec {R : ℝ≥0 → ℝ} (hR : Continuous R) (a d : ℝ≥0) (y : ℝ) :
    markPos (rdrv (recOf (d : ℝ≥0∞) (fun u => GW2Rd.stgDrv R a u, ⊤)))
        (rtime (recOf (d : ℝ≥0∞) (fun u => GW2Rd.stgDrv R a u, ⊤))) y =
      markPos (QuantumZipper.RS.shiftDrive (Ito.rpath R) a) d y := by
  have hc : Continuous fun u => GW2Rd.stgDrv R a u :=
    (hR.comp (continuous_const.add continuous_id)).sub continuous_const
  have he : IsRegularDriver ((fun u => GW2Rd.stgDrv R a u), (⊤ : ℝ≥0∞)) :=
    Gm.isRegularDriver_top hc (GW2Rd.stgDrv_zero R a)
  have hfin : min (d : ℝ≥0∞) (⊤ : ℝ≥0∞) ≠ ⊤ := by rw [min_top_right]; exact ENNReal.coe_ne_top
  have hrt : rtime (recOf (d : ℝ≥0∞) (fun u => GW2Rd.stgDrv R a u, ⊤)) = d := by
    rw [rtime_recOf_coe]
    simp only [min_top_right, ENNReal.toNNReal_coe]
  rw [hrt]
  refine Sec7.StripSideHeightProb.markPos_congr (fun z hz => ?_) y
  have hz0 : 0 ≤ z := hz.1
  have hzd : z.toNNReal ≤ d := Real.toNNReal_le_iff_le_coe.2 hz.2
  have h1 := Gm.rdrv_recOf_eq he hfin hc.continuousOn z.toNNReal
  rw [Real.coe_toNNReal _ hz0] at h1
  rw [h1]
  simp only [min_top_right, ENNReal.toNNReal_coe, min_eq_left hzd, GW2Rd.stgDrv,
    QuantumZipper.RS.shiftDrive, Ito.rpath, Real.toNNReal_coe]
  congr 2
  rw [Real.toNNReal_add a.coe_nonneg hz0, Real.toNNReal_coe]

/-- **The junction carried along a decoded past is the right mark of `J₀` at the stage start.** -/
theorem cfJunction_pastOf {R : ℝ≥0 → ℝ} (hR : Continuous R) (hR0 : R 0 = 0) {b : ℕ → ℝ≥0} (hb0 : b 0 = 0)
    (hbm : Monotone b) {J₀ : RecData → ℝ} (hJ₀ : ∀ r, 0 ≤ J₀ r) (cf : RecData) :
    ∀ n, cfJunction J₀ (n + 1) (GW2Wm.pastOf cf R b (n + 1)) = markPos (Ito.rpath R) (b (n + 1)) (J₀ cf)
  | 0 => by
    have hRc : Continuous (Ito.rpath R) := hR.comp continuous_real_toNNReal
    change markPos (rdrv (recOf ((b (0 + 1) - b 0 : ℝ≥0) : ℝ≥0∞) (fun u => GW2Rd.stgDrv R (b 0) u, ⊤)))
      (rtime (recOf ((b (0 + 1) - b 0 : ℝ≥0) : ℝ≥0∞) (fun u => GW2Rd.stgDrv R (b 0) u, ⊤))) (J₀ cf) = _
    rw [markPos_stgRec hR]
    have hsh : QuantumZipper.RS.shiftDrive (Ito.rpath R) (b 0) = Ito.rpath R := by
      funext r
      simp only [QuantumZipper.RS.shiftDrive, hb0, NNReal.coe_zero, zero_add, Ito.rpath, Real.toNNReal_zero, hR0,
        sub_zero]
    rw [hsh, hb0, tsub_zero]
  | n + 1 => by
    have hRc : Continuous (Ito.rpath R) := hR.comp continuous_real_toNNReal
    have hRc0 : Ito.rpath R 0 = 0 := by simp only [Ito.rpath, Real.toNNReal_zero, hR0]
    have ih := cfJunction_pastOf hR hR0 hb0 hbm hJ₀ cf n
    change markPos (rdrv (recOf ((b (n + 1 + 1) - b (n + 1) : ℝ≥0) : ℝ≥0∞)
        (fun u => GW2Rd.stgDrv R (b (n + 1)) u, ⊤)))
      (rtime (recOf ((b (n + 1 + 1) - b (n + 1) : ℝ≥0) : ℝ≥0∞) (fun u => GW2Rd.stgDrv R (b (n + 1)) u, ⊤)))
      (cfJunction J₀ (n + 1) (GW2Wm.pastOf cf R b (n + 1))) = _
    rw [ih, markPos_stgRec hR]
    have hle : b (n + 1) ≤ b (n + 1 + 1) := hbm (Nat.le_succ _)
    rw [SB.Cx.markPos_shiftDrive hRc hRc0 (b (n + 1)).coe_nonneg (b (n + 1 + 1) - b (n + 1)).coe_nonneg
      (hJ₀ cf), NNReal.coe_sub hle]
    congr 1
    ring

/-! ### The stage driver -/

/-- The frozen stage driver and the shifted driver agree up to the freezing time. -/
theorem alive_frozen_stgDrv_iff {R : ℝ≥0 → ℝ} (a : ℝ≥0) (n : ℝ≥0) (q : ℝ) :
    Alive (frozenDrive (GW2Rd.stgDrv R a) n) q n ↔ Alive (Sec5.Prop59NodeTree.shiftDrv (Ito.rpath R) a) q n := by
  refine Supp8.GB6.alive_congr fun r hr => ?_
  have hr0 : 0 ≤ r := hr.1
  simp only [frozenDrive, min_eq_left hr.2, GW2Rd.stgDrv, Sec5.Prop59NodeTree.shiftDrv, Ito.rpath,
    Real.toNNReal_coe]
  rw [Real.toNNReal_add a.coe_nonneg hr0, Real.toNNReal_coe]

/-- **Beyond the carried junction every point stays alive for the stage driver at every time** (`GW2Bh.aliveRead`,
the form of RELDET's `BadCode`), when every point beyond `J₀` stays alive for the relative driver. -/
theorem aliveRead_stgDrv_of_cfJunction_lt {R : ℝ≥0 → ℝ} (hR : Continuous R) (hR0 : R 0 = 0) {b : ℕ → ℝ≥0}
    (hb0 : b 0 = 0) (hbm : Monotone b) {J₀ : RecData → ℝ} (hJ₀ : ∀ r, 0 ≤ J₀ r) (cf : RecData)
    (halive : ∀ p, J₀ cf < p → ∀ t : ℝ, 0 ≤ t → Alive (Ito.rpath R) p t) (N : ℕ) {q : ℝ}
    (hq : cfJunction J₀ N (GW2Wm.pastOf cf R b N) < q) (n : ℕ) :
    GW2Bh.aliveRead n q (GW2Rd.stgDrv R (b N)) := by
  have hRc : Continuous (Ito.rpath R) := hR.comp continuous_real_toNNReal
  have hRc0 : Ito.rpath R 0 = 0 := by simp only [Ito.rpath, Real.toNNReal_zero, hR0]
  have hsc : Continuous (GW2Rd.stgDrv R (b N)) :=
    (hR.comp (continuous_const.add continuous_id)).sub continuous_const
  rw [GW2Bh.aliveRead_iff q hsc.continuousOn]
  rw [show ((n : ℝ≥0) : ℝ) = (n : ℝ) by norm_cast]
  have key : Alive (Sec5.Prop59NodeTree.shiftDrv (Ito.rpath R) (b N)) q n := by
    cases N with
    | zero =>
      have hsh : Sec5.Prop59NodeTree.shiftDrv (Ito.rpath R) ((b 0 : ℝ≥0) : ℝ) = Ito.rpath R := by
        funext r
        simp only [Sec5.Prop59NodeTree.shiftDrv, hb0, NNReal.coe_zero, zero_add, hRc0, sub_zero]
      rw [hsh]
      exact halive q hq n (Nat.cast_nonneg n)
    | succ k =>
      rw [cfJunction_pastOf hR hR0 hb0 hbm hJ₀ cf k] at hq
      exact alive_shiftDrv_of_markPos_lt hRc hRc0 (b (k + 1)).coe_nonneg (Nat.cast_nonneg n) (hJ₀ cf)
        (fun p hp => halive p hp _ (add_nonneg (b (k + 1)).coe_nonneg (Nat.cast_nonneg n))) hq
  have h := (alive_frozen_stgDrv_iff (R := R) (b N) (n : ℝ≥0) q).2
  push_cast at h
  exact h key

/-! ### The instance: the glued relative driver of a contact with an unbounded clock -/

section Sample

variable {Ω : Type*} (W : ℝ≥0 → Ω → ℝ) (ζ : Ω → ℝ≥0∞) (ω : Ω)
  {α : ℝ≥0 → ℂ} (hα : IsGeneratingTrace (W · ω) ⊤ α)
  (hW : Continuous (W · ω)) (hW0 : W 0 ω = 0) (hζ : ζ ω = ⊤)
  {s : ℝ≥0} (hs : 0 < s) {x : ℝ} (hx : 0 ≤ x) (harc : ∀ u ∈ Icc 0 s, x * ‖α u‖ < 1)
  {w : ℝ≥0 → ℝ} (hwc : Continuous w) (hw0 : w 0 = 0) {γ : ℝ≥0 → ℂ} (hγ : IsGeneratingTrace w ⊤ γ)
  {τ : ℝ≥0} (hT : firstContactTime (fun t => sphereInv (((x : ℂ) + γ t : ℂ) : OnePoint ℂ))
    ((fun u => (α u : OnePoint ℂ)) '' Icc 0 s) = (τ : ℝ≥0∞))

include hα hW hW0 hζ hs hx harc hwc hw0 hγ hT in
/-- **The counterflow's right side is `[cfJunction, ∞)` in the stage chart** (D81), for the glued relative driver
`cDrv` of a first contact with an unbounded relative clock (a first contact at the counterflow's tip): along any
decoded past of `cDrv` from the counterflow record, every `q` beyond the carried junction stays alive for the stage
driver at every time. -/
theorem aliveRead_stgDrv_cDrv (hneg : markPosL (rdrv (cfRec s W ζ ω)) (rtime (cfRec s W ζ ω)) 0 < 0)
    (hunb : ∀ y : ℝ, ∃ v : ℝ≥0, v < τ ∧ y < gClk x s (cfRec s W ζ ω) w v)
    {b : ℕ → ℝ≥0} (hb0 : b 0 = 0) (hbm : Monotone b) (N : ℕ) {q : ℝ}
    (hq : cfJunction (cfJunctionRootX x s) N
      (GW2Wm.pastOf (cfRec s W ζ ω) (cDrv x s (cfRec s W ζ ω) w τ) b N) < q) (n : ℕ) :
    GW2Bh.aliveRead n q (GW2Rd.stgDrv (cDrv x s (cfRec s W ζ ω) w τ) (b N)) := by
  set D := cDrv x s (cfRec s W ζ ω) w τ with hD
  have hDc : Continuous D := continuous_iff_continuousAt.2 fun u => by
    obtain ⟨v, hvτ, hv⟩ := hunb u
    exact continuousAt_cDrv W ζ ω hα hW hW0 hζ hs hx harc hwc hw0 hγ hT hvτ hv
  have hD0 : D 0 = 0 := cDrv_zero W ζ ω hα hW hW0 hζ hs hx harc hwc hw0 hγ hT
  refine aliveRead_stgDrv_of_cfJunction_lt hDc hD0 hb0 hbm (fun r => le_max_right _ _) (cfRec s W ζ ω)
    (fun p hp t ht => ?_) N hq n
  have hpJ : junctionX x s (cfRec s W ζ ω) < p := lt_of_le_of_lt (le_max_left _ _) hp
  have hp0 : 0 < p := lt_of_le_of_lt (le_max_right _ _) hp
  obtain ⟨v, hvτ, hv⟩ := hunb (t + 1)
  have hal := alive_cDrv_of_gt W ζ ω hα hW hW0 hζ hs hx harc hwc hw0 hγ hT hneg hvτ
    (t := t.toNNReal) (t₂ := t + 1 / 2) (by rw [Real.coe_toNNReal _ ht]; linarith) (by linarith) hpJ hp0
  rw [Real.coe_toNNReal _ ht] at hal
  refine (Supp8.GB6.alive_congr fun r hr => ?_).1 hal
  simp only [frozenDrive, Ito.rpath]
  rw [min_eq_left (by linarith [hr.2])]

end Sample

end InteractingSLE.Theorem14.GW2Ni
