/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.ZhanGT4.A1CommonWord
import InteractingSLE.Spec.ZhanGT4.A1EightSeedAssembly
import InteractingSLE.Spec.ZhanGT4.A1EightFinAssembly
import InteractingSLE.Spec.ZhanGT4.DualTwoDirEncl

/-!
# Zhan's A.1: the rectangle data at every sample, from a protected enclosure family

Packet PROVE-A1-COMMON. Source: Astra, *Follow-up proofs*, §A.1.3–A.1.5 (`ig1_followup_proofs.txt` L300–L425: the
curves are stopped at their exits from the members of a countable family of separated enclosure pairs).

`IsEnclFamily H₁ H₂ δ q dd p N Tm` packages what A1-EIGHTSEED / A1-EIGHTFIN / A1-G3CALC ask of the enclosures: protected
pairs (`IsProtectedPair`), positive caps `N m ≤ Tm m`, relative neighbourhoods of the two sources, and the large
enclosure in the large curve's own frame is an `ℍ`-hull. The rectangles are the lifetime-capped exits

* `S₁ m x = lifeExit (W₁ · x) (ζ₁ x) (H₁ m) (N m)` (small curve, from `0`),
* `S₂ m y = lifeExit (W₂ · y + p) (ζ₂ y) (H₂ m) (N m)` (large curve, shifted to start at `p`).

At every sample of patched marginals (pathwise relation, continuous Brownian path, and for the small curves the
separation predicate of `A1CommonWord`), all pathwise rectangle hypotheses of `seedFieldInputM_of_eight(_rows)` and
`seedFieldInputG_of_g3` hold: **`eight_rect`**, **`g3_rect`** (`hgood₁`, `hc₂`, `h0₂`, `hgood₂`, `hS₂pos`, `hU`, and the
strict large exit). The exits are stopping times of the usual augmentation: **`isStoppingTime_rect₁`**,
**`isStoppingTime_rect₂`**.
-/

set_option autoImplicit false

noncomputable section

open Complex Set Filter Topology Metric MeasureTheory
open scoped NNReal ENNReal

namespace InteractingSLE.ZhanGT4.A1Common

open QuantumZipper (H fwdHull)
open A2X A1EightSeed A1SeedField

/-! ### Protected enclosure families -/

/-- **A protected enclosure family** for the source `p > 0` of the large curve: for every `m`, a protected pair
`(H₁ m, H₂ m)` with separation `δ m`, protected point `q m` and radius `dd m`, a positive cap `N m ≤ Tm m`, relative
neighbourhoods of the sources `0 ∈ H₁ m` and `p ∈ H₂ m`, and the large enclosure translated to the large curve's own
frame is an `ℍ`-hull. -/
structure IsEnclFamily (H₁ H₂ : ℕ → Set ℂ) (δ q dd : ℕ → ℝ) (p : ℝ) (N : ℕ → ℝ≥0) (Tm : ℕ → ℝ) : Prop where
  pp : ∀ m, IsProtectedPair (H₁ m) (H₂ m) (δ m) p (q m) (dd m)
  N_pos : ∀ m, 0 < N m
  N_le : ∀ m, (N m : ℝ) ≤ Tm m
  nbhd₁ : ∀ m, ∃ ε > (0 : ℝ), ball (0 : ℂ) ε ∩ H ⊆ H₁ m
  nbhd₂ : ∀ m, ∃ ε > (0 : ℝ), ball (p : ℂ) ε ∩ H ⊆ H₂ m
  hull₂ : ∀ m, IsHPHull (transl (-p) (H₂ m))

section Geometry

/-- A bounded set lies in a closed disc of positive radius about `0`. -/
theorem exists_closedBall_of_isBounded {E : Set ℂ} (hE : Bornology.IsBounded E) :
    ∃ R > (0 : ℝ), E ⊆ closedBall (0 : ℂ) R := by
  obtain ⟨r, hr⟩ := hE.subset_closedBall 0
  exact ⟨max r 1, lt_of_lt_of_le one_pos (le_max_right _ _), hr.trans (closedBall_subset_closedBall (le_max_left _ _))⟩

/-- A set containing a relative neighbourhood of a real point `c` in `ℍ` has `c` in its closure. -/
theorem mem_closure_of_nbhd {E : Set ℂ} {c : ℝ} {ε : ℝ} (hε : 0 < ε) (hE : ball (c : ℂ) ε ∩ H ⊆ E) :
    (c : ℂ) ∈ closure E := by
  rw [Metric.mem_closure_iff]
  intro r hr
  refine ⟨(c : ℂ) + ((min ε r / 2 : ℝ) : ℂ) * Complex.I, hE ⟨?_, ?_⟩, ?_⟩
  · rw [mem_ball, dist_eq_norm, add_sub_cancel_left, norm_mul, Complex.norm_I, mul_one, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos (by positivity)]
    linarith [min_le_left ε r]
  · show 0 < ((c : ℂ) + ((min ε r / 2 : ℝ) : ℂ) * Complex.I).im
    simp only [Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.ofReal_re, Complex.I_im, mul_one,
      Complex.I_re, mul_zero, add_zero, zero_add]
    positivity
  · rw [dist_eq_norm, sub_add_cancel_left, norm_neg, norm_mul, Complex.norm_I, mul_one, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos (by positivity)]
    linarith [min_le_right ε r]

/-- `transl (−p) E` is the preimage of `E` under `z ↦ z + p`. -/
theorem transl_neg_eq_preimage (p : ℝ) (E : Set ℂ) : transl (-p) E = (fun z : ℂ => z + p) ⁻¹' E := by
  ext w
  rw [mem_transl_iff]
  simp only [mem_preimage, Complex.ofReal_neg, sub_neg_eq_add]

/-- **The large curve's source is protected from the small enclosure**: `B(p, δ) ∩ H₁ = ∅`. -/
theorem IsProtectedPair.disjoint_ball_src {H₁ H₂ : Set ℂ} {δ p q dd : ℝ} (hpp : IsProtectedPair H₁ H₂ δ p q dd) :
    Disjoint (ball (p : ℂ) δ) H₁ := by
  refine Set.disjoint_left.2 fun z hz hz₁ => ?_
  have h := le_norm_of_mem_closure hpp.sep hpp.src hz₁
  rw [mem_ball, dist_eq_norm, norm_sub_rev] at hz
  linarith [hpp.sep_pos]

namespace IsEnclFamily

variable {H₁ H₂ : ℕ → Set ℂ} {δ q dd : ℕ → ℝ} {p : ℝ} {N : ℕ → ℝ≥0} {Tm : ℕ → ℝ}
  (hF : IsEnclFamily H₁ H₂ δ q dd p N Tm)
include hF

theorem zero_mem_closure₁ (m : ℕ) : (0 : ℂ) ∈ closure (H₁ m) := by
  obtain ⟨ε, hε, h⟩ := hF.nbhd₁ m
  simpa using mem_closure_of_nbhd (c := 0) hε (by simpa using h)

theorem zero_mem_closure₂ (m : ℕ) : (0 : ℂ) ∈ closure (transl (-p) (H₂ m)) := by
  obtain ⟨ε, hε, h⟩ := hF.nbhd₂ m
  refine mem_closure_of_nbhd (c := 0) hε fun z hz => ?_
  rw [mem_transl_iff]
  refine h ⟨?_, ?_⟩
  · have := hz.1
    rw [mem_ball, dist_eq_norm] at this ⊢
    simpa using this
  · have h2 : 0 < z.im := hz.2
    show 0 < (z - ((-p : ℝ) : ℂ)).im
    simpa using h2

theorem nbhd₂' (m : ℕ) : ∃ ε > (0 : ℝ), ball (0 : ℂ) ε ∩ H ⊆ transl (-p) (H₂ m) := by
  obtain ⟨ε, hε, h⟩ := hF.nbhd₂ m
  refine ⟨ε, hε, fun z hz => ?_⟩
  rw [mem_transl_iff]
  refine h ⟨?_, ?_⟩
  · have := hz.1
    rw [mem_ball, dist_eq_norm] at this ⊢
    simpa using this
  · have h2 : 0 < z.im := hz.2
    show 0 < (z - ((-p : ℝ) : ℂ)).im
    simpa using h2

/-- The small curve's source `−p` (own frame of the large curve) is protected from the translated large enclosure. -/
theorem disjoint_ball_neg_src (m : ℕ) : Disjoint (ball ((-p : ℝ) : ℂ) (δ m)) (transl (-p) (H₂ m)) :=
  A1EightFin.disjoint_ball_neg_src (hF.pp m) (by simpa using hF.zero_mem_closure₁ m)

end IsEnclFamily

end Geometry

/-! ### Hulls of the stopped drivers -/

section Hulls

/-- **The hull of the driver stopped at `S`, at time `S`**, is the driver's hull at `S` when the driver is continuous a
little past `S`. -/
theorem fwdHull_stopDrv_self {w : ℝ → ℝ} {S r : ℝ} (hS : 0 ≤ S) (hSr : S < r) (hc : ContinuousOn w (Icc 0 r)) :
    fwdHull (A1Ref.stopDrv w S) S = fwdHull w S :=
  LocalExt.fwdHull_congr_of_continuousOn ((A1Ref.continuous_stopDrv (hc.mono (Icc_subset_Icc_right hSr.le))
    hS).continuousOn) hc hS hSr (A1Ref.stopDrv_eqOn w S)

variable {ζ : ℝ≥0∞} {w : ℝ≥0 → ℝ}

/-- **The stopped small driver's hull at the exit lies in the enclosure** (A1-EIGHTSEED's `hgood₁` hull clause). -/
theorem fwdHull_stopDrv_lifeExit_subset (hwc : ContinuousOn w {t | (t : ℝ≥0∞) < ζ}) (hw0 : w 0 = 0)
    {E : Set ℂ} (hE : IsHPHull E) {N : ℝ≥0} (hlt : (lifeExit w ζ E N : ℝ≥0∞) < ζ) :
    fwdHull (A1Ref.stopDrv (Strip.extPath w) (lifeExit w ζ E N)) (lifeExit w ζ E N) ⊆ E := by
  obtain ⟨r, hTr, -, hcr⟩ := exists_real_btwn_continuousOn hwc hlt
  rw [fwdHull_stopDrv_self (lifeExit w ζ E N).coe_nonneg hTr hcr]
  exact fwdHull_lifeExit_subset hwc hw0 hE hlt

/-- **The frozen large path's hull at its exit lies in the enclosure** (A1-EIGHTSEED's `hgood₂` hull clause): the
exit of `w + p` from `E` is the exit of `w` from `transl (−p) E`. -/
theorem fwdHull_frzPath_lifeExit_subset {Y : Type*} {W₂ : ℝ≥0 → Y → ℝ} {ζ₂ : Y → ℝ≥0∞} {y : Y} {p : ℝ}
    (hwc : ContinuousOn (W₂ · y) {t | (t : ℝ≥0∞) < ζ₂ y}) (hw0 : W₂ 0 y = 0) {E : Set ℂ}
    (hE : IsHPHull (transl (-p) E)) {N : ℝ≥0}
    (hlt : (lifeExit (fun t => W₂ t y + p) (ζ₂ y) E N : ℝ≥0∞) < ζ₂ y) :
    fwdHull (frzPath W₂ p (lifeExit (fun t => W₂ t y + p) (ζ₂ y) E N) y)
      (lifeExit (fun t => W₂ t y + p) (ζ₂ y) E N) ⊆ E := by
  rw [lifeExit_add_const, ← transl_neg_eq_preimage] at hlt ⊢
  set S := lifeExit (W₂ · y) (ζ₂ y) (transl (-p) E) N
  have hK := fwdHull_stopDrv_lifeExit_subset hwc hw0 hE hlt
  have e : fwdHull (frzPath W₂ p S y) S =
      (fun z : ℂ => z + p) '' fwdHull (A1Ref.stopDrv (Strip.extPath (W₂ · y)) S) S :=
    ConformalImageFull.fwdHull_add_const _ p S
  rw [e, image_subset_iff, ← transl_neg_eq_preimage]
  exact hK

end Hulls

/-! ### One curve, one rectangle -/

section OneCurve

variable {a : ℝ} {nL nR : ℕ} {xL : Fin nL → ℝ} {xR : Fin nR → ℝ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ}
  {w : ℝ≥0 → ℝ} {vL : Fin nL → ℝ≥0 → ℝ} {vR : Fin nR → ℝ≥0 → ℝ} {b : ℝ≥0 → ℝ} {ζ : ℝ≥0∞}

/-- **The small curve's rectangle facts** (A1-EIGHTSEED's `hgood₁` at one sample and one rectangle), given the strict
exit. -/
theorem small_rect_facts (hP : IsIntegratedSLEPath a xL xR ρL ρR w vL vR b ζ)
    (hthr0 : ¬ ForceWord.ThresholdCondition ρL ρR 0 xL xR) {E : Set ℂ} (hE : IsHPHull E) {ε : ℝ} (hε : 0 < ε)
    (hnb : ball (0 : ℂ) ε ∩ H ⊆ E) {N : ℝ≥0} (hN : 0 < N) {Tm : ℝ} (hNT : (N : ℝ) ≤ Tm)
    (hlt : (lifeExit w ζ E N : ℝ≥0∞) < ζ) :
    (lifeExit w ζ E N : ℝ≥0∞) < ζ ∧ 0 < (lifeExit w ζ E N : ℝ) ∧ (lifeExit w ζ E N : ℝ) ≤ Tm ∧
      fwdHull (A1Ref.stopDrv (Strip.extPath w) (lifeExit w ζ E N)) (lifeExit w ζ E N) ⊆ E :=
  ⟨hlt, NNReal.coe_pos.2 (lifeExit_pos hP.2.2.2.1 hP.1 (zeta_pos_of_not_threshold hP hthr0) hN hε hnb),
    (NNReal.coe_le_coe.2 lifeExit_le).trans hNT, fwdHull_stopDrv_lifeExit_subset hP.2.2.2.1 hP.1 hE hlt⟩

/-- **The large curve's rectangle facts** (A1-EIGHTSEED's `hc₂`, `hgood₂`, A1-EIGHTFIN's `hS₂pos` at one sample and
one rectangle), given the strict exit in the large curve's own frame. -/
theorem large_rect_facts {Y : Type*} {W₂ : ℝ≥0 → Y → ℝ} {y : Y} {p : ℝ} {vL : Fin nL → ℝ≥0 → ℝ}
    {vR : Fin nR → ℝ≥0 → ℝ} (hP : IsIntegratedSLEPath a xL xR ρL ρR (W₂ · y) vL vR b ζ)
    (hthr0 : ¬ ForceWord.ThresholdCondition ρL ρR 0 xL xR) {E : Set ℂ} (hE : IsHPHull (transl (-p) E)) {ε : ℝ}
    (hε : 0 < ε) (hnb : ball (0 : ℂ) ε ∩ H ⊆ transl (-p) E) {N : ℝ≥0} (hN : 0 < N) {Tm : ℝ}
    (hNT : (N : ℝ) ≤ Tm) (hlt : (lifeExit (W₂ · y) ζ (transl (-p) E) N : ℝ≥0∞) < ζ) :
    (lifeExit (fun t => W₂ t y + p) ζ E N : ℝ≥0∞) < ζ ∧
      ContinuousOn (Strip.extPath (W₂ · y)) (Icc 0 (lifeExit (fun t => W₂ t y + p) ζ E N)) ∧
      ((lifeExit (fun t => W₂ t y + p) ζ E N : ℝ) ≤ Tm ∧
        fwdHull (frzPath W₂ p (lifeExit (fun t => W₂ t y + p) ζ E N) y) (lifeExit (fun t => W₂ t y + p) ζ E N) ⊆ E) ∧
      0 < (lifeExit (fun t => W₂ t y + p) ζ E N : ℝ) := by
  have e : lifeExit (fun t => W₂ t y + p) ζ E N = lifeExit (W₂ · y) ζ (transl (-p) E) N := by
    rw [lifeExit_add_const, transl_neg_eq_preimage]
  have hlt' : (lifeExit (fun t => W₂ t y + p) ζ E N : ℝ≥0∞) < ζ := by rw [e]; exact hlt
  refine ⟨hlt', A1Ref.continuousOn_extPath_Icc hP.2.2.2.1 (by rw [ENNReal.ofReal_coe_nnreal]; exact hlt'),
    ⟨(NNReal.coe_le_coe.2 lifeExit_le).trans hNT,
      fwdHull_frzPath_lifeExit_subset (ζ₂ := fun _ => ζ) hP.2.2.2.1 hP.1 hE hlt'⟩, ?_⟩
  rw [e]
  exact NNReal.coe_pos.2 (lifeExit_pos hP.2.2.2.1 hP.1 (zeta_pos_of_not_threshold hP hthr0) hN hε hnb)

end OneCurve

/-! ### The exits are stopping times -/

section Stop

variable {X : Type*} {mX : MeasurableSpace X} {𝓕 : Filtration ℝ≥0 mX} [𝓕.IsRightContinuous]
  {W : ℝ≥0 → X → ℝ} {ζ : X → ℝ≥0∞}

/-- The small exits are stopping times of every right-continuous filtration in which the driver is adapted before the
lifetime (e.g. the usual augmentation of a patched marginal). -/
theorem isStoppingTime_rect₁ (hwc : ∀ x, ContinuousOn (W · x) {t | (t : ℝ≥0∞) < ζ x}) (hwa : AdaptedBefore 𝓕 ζ W)
    {E : ℕ → Set ℂ} (hE : ∀ m, IsHPHull (E m)) (N : ℕ → ℝ≥0) (m : ℕ) :
    IsStoppingTime 𝓕 fun x => ((lifeExit (W · x) (ζ x) (E m) (N m) : ℝ≥0) : WithTop ℝ≥0) :=
  isStoppingTime_lifeExit hwc hwa (hE m).2.2.1 (N m)

/-- The large exits (driver shifted to `p`) are stopping times. -/
theorem isStoppingTime_rect₂ (hwc : ∀ x, ContinuousOn (W · x) {t | (t : ℝ≥0∞) < ζ x}) (hwa : AdaptedBefore 𝓕 ζ W)
    {E : ℕ → Set ℂ} (hE : ∀ m, IsHPHull (E m)) (N : ℕ → ℝ≥0) (p : ℝ) (m : ℕ) :
    IsStoppingTime 𝓕 fun x => ((lifeExit (fun t => W t x + p) (ζ x) (E m) (N m) : ℝ≥0) : WithTop ℝ≥0) :=
  isStoppingTime_lifeExit (w := fun t x => W t x + p) (continuousOn_add_const hwc p) (adaptedBefore_add_const hwa p)
    (hE m).2.2.1 (N m)

end Stop

/-! ### The two cases -/

section Cases

variable {X Y : Type*} {κ x y : ℝ} {H₁ H₂ : ℕ → Set ℂ} {δ q dd : ℕ → ℝ} {N : ℕ → ℝ≥0} {Tm : ℕ → ℝ}

/-- **(Eight) The pathwise rectangle hypotheses at every sample.** For marginals whose small curve satisfies the
pathwise relation and `GoodSmallEight` at every sample and whose large curve satisfies its pathwise relation at every
sample, both with continuous Brownian paths, and the exits `S₁`, `S₂` from a protected enclosure family: the
hypotheses `hU`, `hgood₁`, `hsep₁`, `hc₂`, `h0₂`, `hgood₂` of A1-EIGHTSEED's `seedFieldInputM_of_eight`, A1-EIGHTFIN's
`hS₂pos`, and the strict large exit. -/
theorem eight_rect (hκ8 : 8 ≤ κ) (hx : x < 0) {W₁ : ℝ≥0 → X → ℝ} {VL₁ : Fin 1 → ℝ≥0 → X → ℝ}
    {VR₁ : Fin 2 → ℝ≥0 → X → ℝ} {B₁ : ℝ≥0 → X → ℝ} {ζ₁ : X → ℝ≥0∞} {W₂ : ℝ≥0 → Y → ℝ}
    {VL₂ : Fin 1 → ℝ≥0 → Y → ℝ} {VR₂ : Fin 0 → ℝ≥0 → Y → ℝ} {B₂ : ℝ≥0 → Y → ℝ} {ζ₂ : Y → ℝ≥0∞}
    (hP₁ : ∀ ω, IsIntegratedSLEPath (kh κ) ![0] ![0, -x] (smallEightRhoL κ) (smallEightRhoR κ) (W₁ · ω)
      (fun i t => VL₁ i t ω) (fun i t => VR₁ i t ω) (B₁ · ω) (ζ₁ ω))
    (hg₁ : ∀ ω, GoodSmallEight (W₁ · ω) (fun i t => VL₁ i t ω) (fun i t => VR₁ i t ω) (B₁ · ω) (ζ₁ ω))
    (hB₁ : ∀ ω, Continuous (B₁ · ω))
    (hP₂ : ∀ ω, IsIntegratedSLEPath κ ![x] ![] ![0] ![] (W₂ · ω) (fun i t => VL₂ i t ω) (fun i t => VR₂ i t ω)
      (B₂ · ω) (ζ₂ ω))
    (hB₂ : ∀ ω, Continuous (B₂ · ω)) (hF : IsEnclFamily H₁ H₂ δ q dd (-x) N Tm) :
    let S₁ : ℕ → X → ℝ≥0 := fun m ω => lifeExit (W₁ · ω) (ζ₁ ω) (H₁ m) (N m)
    let S₂ : ℕ → Y → ℝ≥0 := fun m ω => lifeExit (fun t => W₂ t ω + -x) (ζ₂ ω) (H₂ m) (N m)
    (∀ m, ∃ U : ℝ≥0, (∀ ω, S₁ m ω ≤ U) ∧ ∀ ω, S₂ m ω ≤ U) ∧
    (∀ m ω, (S₁ m ω : ℝ≥0∞) < ζ₁ ω ∧ 0 < (S₁ m ω : ℝ) ∧ (S₁ m ω : ℝ) ≤ Tm m ∧
      fwdHull (eightDrv W₁ S₁ m ω) (S₁ m ω) ⊆ H₁ m) ∧
    (∀ ω (s : ℝ≥0), 0 < s → (s : ℝ≥0∞) < ζ₁ ω → VL₁ 0 s ω ≠ W₁ s ω ∧ VR₁ 0 s ω ≠ W₁ s ω) ∧
    (∀ m ω, ContinuousOn (Strip.extPath (W₂ · ω)) (Icc 0 (S₂ m ω))) ∧ (∀ ω, W₂ 0 ω = 0) ∧
    (∀ m ω, (S₂ m ω : ℝ) ≤ Tm m ∧ fwdHull (frzPath W₂ (-x) (S₂ m ω) ω) (S₂ m ω) ⊆ H₂ m) ∧
    (∀ m ω, 0 < (S₂ m ω : ℝ)) ∧ (∀ m ω, (S₂ m ω : ℝ≥0∞) < ζ₂ ω) := by
  intro S₁ S₂
  have hthr₁ : ¬ ForceWord.ThresholdCondition (smallEightRhoL κ) (smallEightRhoR κ) 0 ![0] ![0, -x] :=
    not_threshold_smallEight hκ8 0 _ _ (by simp; linarith)
  have hlt₁ : ∀ m ω, (S₁ m ω : ℝ≥0∞) < ζ₁ ω := fun m ω => by
    obtain ⟨R, hR, hER⟩ := exists_closedBall_of_isBounded (hF.pp m).hull₁.2.1
    exact lifeExit_lt_smallEight hκ8 hx (hP₁ ω) (hg₁ ω) (hB₁ ω) hR hER (hF.pp m).hull₁ (hF.zero_mem_closure₁ m)
      (hF.pp m).sep_pos (IsProtectedPair.disjoint_ball_src (hF.pp m)) (N m)
  have hlt₂ : ∀ m ω, (lifeExit (W₂ · ω) (ζ₂ ω) (transl (-(-x)) (H₂ m)) (N m) : ℝ≥0∞) < ζ₂ ω := fun m ω => by
    obtain ⟨R, hR, hER⟩ := exists_closedBall_of_isBounded (hF.hull₂ m).2.1
    have hd := hF.disjoint_ball_neg_src m
    have e : (((-(-x) : ℝ)) : ℂ) = (x : ℂ) := by simp
    rw [e] at hd
    exact lifeExit_lt_largeEight hx (hP₂ ω) (hB₂ ω) hR hER (hF.hull₂ m) (hF.zero_mem_closure₂ m)
      (hF.pp m).sep_pos hd (N m)
  have hL : ∀ m ω, (S₂ m ω : ℝ≥0∞) < ζ₂ ω ∧ ContinuousOn (Strip.extPath (W₂ · ω)) (Icc 0 (S₂ m ω)) ∧
      ((S₂ m ω : ℝ) ≤ Tm m ∧ fwdHull (frzPath W₂ (-x) (S₂ m ω) ω) (S₂ m ω) ⊆ H₂ m) ∧ 0 < (S₂ m ω : ℝ) :=
      fun m ω => by
    obtain ⟨ε, hε, hnb⟩ := hF.nbhd₂' m
    exact large_rect_facts (hP₂ ω) (not_threshold_largeEight 0 _ _) (hF.hull₂ m) hε hnb (hF.N_pos m)
      (hF.N_le m) (hlt₂ m ω)
  refine ⟨fun m => ⟨N m, fun ω => lifeExit_le, fun ω => lifeExit_le⟩, fun m ω => ?_,
    fun ω s hs hsζ => smallEight_sep_of_good (hg₁ ω) s hs hsζ, fun m ω => (hL m ω).2.1, fun ω => (hP₂ ω).1,
    fun m ω => (hL m ω).2.2.1, fun m ω => (hL m ω).2.2.2, fun m ω => (hL m ω).1⟩
  obtain ⟨ε, hε, hnb⟩ := hF.nbhd₁ m
  exact small_rect_facts (hP₁ ω) hthr₁ (hF.pp m).hull₁ hε hnb (hF.N_pos m) (hF.N_le m) (hlt₁ m ω)

/-- **(G3) The pathwise rectangle hypotheses at every sample**: as `eight_rect`, for (G3)'s words, with the additional
non-collisions of the ordinary mark (`hsepO`) and of the other source (`hneP`) of A1-G3CALC. -/
theorem g3_rect (hκ4 : 4 < κ) (hκ8 : κ < 8) (hyx : y < x) (hx : x < 0) {W₁ : ℝ≥0 → X → ℝ}
    {VL₁ : Fin 1 → ℝ≥0 → X → ℝ} {VR₁ : Fin 3 → ℝ≥0 → X → ℝ} {B₁ : ℝ≥0 → X → ℝ} {ζ₁ : X → ℝ≥0∞}
    {W₂ : ℝ≥0 → Y → ℝ} {VL₂ : Fin 2 → ℝ≥0 → Y → ℝ} {VR₂ : Fin 0 → ℝ≥0 → Y → ℝ} {B₂ : ℝ≥0 → Y → ℝ}
    {ζ₂ : Y → ℝ≥0∞}
    (hP₁ : ∀ ω, IsIntegratedSLEPath (kh κ) ![0] ![0, x - y, -y] (smallG3RhoL κ) (smallG3RhoR κ) (W₁ · ω)
      (fun i t => VL₁ i t ω) (fun i t => VR₁ i t ω) (B₁ · ω) (ζ₁ ω))
    (hg₁ : ∀ ω, GoodSmallG3 (W₁ · ω) (fun i t => VL₁ i t ω) (fun i t => VR₁ i t ω) (B₁ · ω) (ζ₁ ω))
    (hB₁ : ∀ ω, Continuous (B₁ · ω))
    (hP₂ : ∀ ω, IsIntegratedSLEPath κ ![x, y] ![] ![κ - 4, -4] ![] (W₂ · ω) (fun i t => VL₂ i t ω)
      (fun i t => VR₂ i t ω) (B₂ · ω) (ζ₂ ω))
    (hB₂ : ∀ ω, Continuous (B₂ · ω)) (hF : IsEnclFamily H₁ H₂ δ q dd (-y) N Tm) :
    let S₁ : ℕ → X → ℝ≥0 := fun m ω => lifeExit (W₁ · ω) (ζ₁ ω) (H₁ m) (N m)
    let S₂ : ℕ → Y → ℝ≥0 := fun m ω => lifeExit (fun t => W₂ t ω + -y) (ζ₂ ω) (H₂ m) (N m)
    (∀ m, ∃ U : ℝ≥0, (∀ ω, S₁ m ω ≤ U) ∧ ∀ ω, S₂ m ω ≤ U) ∧
    (∀ m ω, (S₁ m ω : ℝ≥0∞) < ζ₁ ω ∧ 0 < (S₁ m ω : ℝ) ∧ (S₁ m ω : ℝ) ≤ Tm m ∧
      fwdHull (eightDrv W₁ S₁ m ω) (S₁ m ω) ⊆ H₁ m) ∧
    (∀ ω (s : ℝ≥0), 0 < s → (s : ℝ≥0∞) < ζ₁ ω → VL₁ 0 s ω ≠ W₁ s ω ∧ VR₁ 0 s ω ≠ W₁ s ω) ∧
    (∀ ω (s : ℝ≥0), (s : ℝ≥0∞) < ζ₁ ω → VR₁ 1 s ω ≠ W₁ s ω) ∧
    (∀ ω (s : ℝ≥0), (s : ℝ≥0∞) < ζ₁ ω → VR₁ 2 s ω ≠ W₁ s ω) ∧
    (∀ m ω, ContinuousOn (Strip.extPath (W₂ · ω)) (Icc 0 (S₂ m ω))) ∧ (∀ ω, W₂ 0 ω = 0) ∧
    (∀ m ω, (S₂ m ω : ℝ) ≤ Tm m ∧ fwdHull (frzPath W₂ (-y) (S₂ m ω) ω) (S₂ m ω) ⊆ H₂ m) ∧
    (∀ m ω, 0 < (S₂ m ω : ℝ)) ∧ (∀ m ω, (S₂ m ω : ℝ≥0∞) < ζ₂ ω) := by
  intro S₁ S₂
  have hy : y < 0 := hyx.trans hx
  have hthr₁ : ¬ ForceWord.ThresholdCondition (smallG3RhoL κ) (smallG3RhoR κ) 0 ![0] ![0, x - y, -y] :=
    not_threshold_smallG3 hκ4 hκ8 0 _ _ (by simp; linarith)
  have hthr₂ : ¬ ForceWord.ThresholdCondition (![κ - 4, -4] : Fin 2 → ℝ) ![] 0 ![x, y] ![] :=
    not_threshold_largeG3 hκ4 0 _ _ (by simp; linarith)
  have hlt₁ : ∀ m ω, (S₁ m ω : ℝ≥0∞) < ζ₁ ω := fun m ω => by
    obtain ⟨R, hR, hER⟩ := exists_closedBall_of_isBounded (hF.pp m).hull₁.2.1
    exact lifeExit_lt_smallG3 hκ4 hκ8 hy (hP₁ ω) (hg₁ ω) (hB₁ ω) hR hER (hF.pp m).hull₁ (hF.zero_mem_closure₁ m)
      (hF.pp m).sep_pos (IsProtectedPair.disjoint_ball_src (hF.pp m)) (N m)
  have hlt₂ : ∀ m ω, (lifeExit (W₂ · ω) (ζ₂ ω) (transl (-(-y)) (H₂ m)) (N m) : ℝ≥0∞) < ζ₂ ω := fun m ω => by
    obtain ⟨R, hR, hER⟩ := exists_closedBall_of_isBounded (hF.hull₂ m).2.1
    have hd := hF.disjoint_ball_neg_src m
    have e : (((-(-y) : ℝ)) : ℂ) = (y : ℂ) := by simp
    rw [e] at hd
    exact lifeExit_lt_largeG3 hκ4 hy (hP₂ ω) (hB₂ ω) hR hER (hF.hull₂ m) (hF.zero_mem_closure₂ m)
      (hF.pp m).sep_pos hd (N m)
  have hL : ∀ m ω, (S₂ m ω : ℝ≥0∞) < ζ₂ ω ∧ ContinuousOn (Strip.extPath (W₂ · ω)) (Icc 0 (S₂ m ω)) ∧
      ((S₂ m ω : ℝ) ≤ Tm m ∧ fwdHull (frzPath W₂ (-y) (S₂ m ω) ω) (S₂ m ω) ⊆ H₂ m) ∧ 0 < (S₂ m ω : ℝ) :=
      fun m ω => by
    obtain ⟨ε, hε, hnb⟩ := hF.nbhd₂' m
    exact large_rect_facts (hP₂ ω) hthr₂ (hF.hull₂ m) hε hnb (hF.N_pos m) (hF.N_le m) (hlt₂ m ω)
  refine ⟨fun m => ⟨N m, fun ω => lifeExit_le, fun ω => lifeExit_le⟩, fun m ω => ?_,
    fun ω s hs hsζ => smallG3_sep_of_good (hg₁ ω) s hs hsζ,
    fun ω s hsζ => smallG3_sepO_of_good hyx (hP₁ ω) (hg₁ ω) s hsζ,
    fun ω s hsζ => smallG3_sepP_of_good hκ4 hκ8 hyx hx (hP₁ ω) (hg₁ ω) s hsζ, fun m ω => (hL m ω).2.1,
    fun ω => (hP₂ ω).1, fun m ω => (hL m ω).2.2.1, fun m ω => (hL m ω).2.2.2, fun m ω => (hL m ω).1⟩
  obtain ⟨ε, hε, hnb⟩ := hF.nbhd₁ m
  exact small_rect_facts (hP₁ ω) hthr₁ (hF.pp m).hull₁ hε hnb (hF.N_pos m) (hF.N_le m) (hlt₁ m ω)

end Cases

end InteractingSLE.ZhanGT4.A1Common
