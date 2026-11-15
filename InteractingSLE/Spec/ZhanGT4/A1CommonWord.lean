/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.ZhanGT4.A1CommonExit
import InteractingSLE.Spec.ZhanGT4.A1CommonPatch
import InteractingSLE.Spec.ZhanGT4.A2Part3IDWire
import InteractingSLE.Foundations.Loewner.ConformalImageFull

/-!
# Zhan's A.1: the four curves of (G3) and (Eight) — non-collisions and exits before the lifetime

Packet PROVE-A1-COMMON. Source: Astra, *Follow-up proofs*, §A.1 (`ig1_followup_proofs.txt` L160–L187: the small and
large words of (G3) and (Eight)) and §A.1.3 (L300–L330).

The two cases of A.1 have four marginals:

* (Eight) small: `SLE_κ̂([0]; [0, −x])` with weights `(−κ̂/2; κ̂/2 − 2, −κ̂/2)`; large: `SLE_κ([x]; [])` with
  weight `0`;
* (G3) small: `SLE_κ̂([0]; [0, x − y, −y])` with weights `(3κ̂/2 − 4; 2 − κ̂/2, κ̂ − 4, −κ̂/2)`; large:
  `SLE_κ([x, y]; [])` with weights `(κ − 4, −4)`.

For each:

* `not_threshold_*`: the threshold condition fails as soon as the other curve's source (resp. the large curve's mark
  `y`, `x` for Eight) is off the driver;
* (small curves) `GoodSmall*` and `ae_goodSmall*`: the almost sure separation of the seeds (and of the ordinary mark)
  from
  the driver (A2-P3-ID's `smallEight_sep`, `smallG3_sep`), the predicate to which `IsRegMarginal.exists_patch` applies;
  the every-sample non-collisions `hsep₁`, `hsepO`, `hneP` of A1-EIGHTSEED / A1-G3CALC follow (`*_sep_of_good`);
* `lifeExit_lt_*`: the enclosure exit precedes the lifetime at every sample with a continuous Brownian path
  (`A1Common.lifeExit_lt_of_protected`, `…_left`);
* `zeta_pos_of_not_threshold`, `lifeExit_add_const` (the large curve's exit in the shifted frame).
-/

set_option autoImplicit false

noncomputable section

open Complex Set Filter Topology Metric MeasureTheory
open scoped NNReal ENNReal

namespace InteractingSLE.ZhanGT4.A1Common

open QuantumZipper (H fwdHull)
open A2X A1EightSeed

/-! ### Generic facts -/

section Generic

variable {a : ℝ} {nL nR : ℕ} {xL : Fin nL → ℝ} {xR : Fin nR → ℝ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ}
  {w : ℝ≥0 → ℝ} {vL : Fin nL → ℝ≥0 → ℝ} {vR : Fin nR → ℝ≥0 → ℝ} {b : ℝ≥0 → ℝ} {ζ : ℝ≥0∞}

/-- **The lifetime is positive** when the seed state is not a threshold state (maximality at `ζ = 0`). -/
theorem zeta_pos_of_not_threshold (hP : IsIntegratedSLEPath a xL xR ρL ρR w vL vR b ζ)
    (h : ¬ ForceWord.ThresholdCondition ρL ρR 0 xL xR) : 0 < ζ :=
  pos_iff_ne_zero.2 fun h0 => h (hP.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 h0)

/-- **The exit of a translated driver** is the exit of the driver from the translated enclosure. -/
theorem lifeExit_add_const (w : ℝ≥0 → ℝ) (ζ : ℝ≥0∞) (E : Set ℂ) (N : ℝ≥0) (p : ℝ) :
    lifeExit (fun t => w t + p) ζ E N = lifeExit w ζ ((fun z : ℂ => z + p) ⁻¹' E) N := by
  unfold lifeExit
  congr 2
  ext t
  have e : fwdHull (Strip.extPath fun t => w t + p) t = (fun z : ℂ => z + p) '' fwdHull (Strip.extPath w) t :=
    ConformalImageFull.fwdHull_add_const (Strip.extPath w) p t
  simp only [mem_ofPred_eq, e, image_subset_iff]

end Generic

/-! ### (Eight) -/

section Eight

variable {κ x : ℝ}

/-- **(Eight, small)** The threshold condition fails whenever the other source `−x` is off the driver. -/
theorem not_threshold_smallEight (hκ8 : 8 ≤ κ) (w₀ : ℝ) (vL₀ : Fin 1 → ℝ) (vR₀ : Fin 2 → ℝ) (h : vR₀ 1 ≠ w₀) :
    ¬ ForceWord.ThresholdCondition (smallEightRhoL κ) (smallEightRhoR κ) w₀ vL₀ vR₀ := by
  obtain ⟨hk0, hk2⟩ := kh_bounds_eight hκ8
  simp only [ForceWord.ThresholdCondition, Finset.sum_filter, Fin.sum_univ_one, Fin.sum_univ_two, smallEightRhoL,
    smallEightRhoR, Matrix.cons_val_zero, Matrix.cons_val_one, h, ite_false, add_zero, not_or, not_le]
  constructor <;> split_ifs <;> linarith

/-- **(Eight, large)** The large word (one mark of weight `0`) never satisfies the threshold condition. -/
theorem not_threshold_largeEight (w₀ : ℝ) (vL₀ : Fin 1 → ℝ) (vR₀ : Fin 0 → ℝ) :
    ¬ ForceWord.ThresholdCondition (![0] : Fin 1 → ℝ) ![] w₀ vL₀ vR₀ := by
  simp only [ForceWord.ThresholdCondition, Finset.sum_filter, Fin.sum_univ_one, Finset.univ_eq_empty,
    Finset.sum_empty, Matrix.cons_val_zero, not_or, not_le]
  constructor
  · split_ifs <;> norm_num
  · norm_num

/-- The every-sample separation of the small (Eight) curve: both seeds strictly off the driver at positive times. -/
def GoodSmallEight (w : ℝ≥0 → ℝ) (vL : Fin 1 → ℝ≥0 → ℝ) (vR : Fin 2 → ℝ≥0 → ℝ) (_b : ℝ≥0 → ℝ) (ζ : ℝ≥0∞) :
    Prop :=
  ∀ t : ℝ≥0, 0 < t → (t : ℝ≥0∞) < ζ → vL 0 t < w t ∧ w t < vR 0 t

/-- **The small (Eight) curve is good almost surely** (A2-P3-ID's `smallEight_sep`). -/
theorem ae_goodSmallEight (hκ8 : 8 ≤ κ) (hx : x < 0) {X : Type*} {mX : MeasurableSpace X} {P : Measure X}
    {𝓕 : Filtration ℝ≥0 mX} {W : ℝ≥0 → X → ℝ} {VL : Fin 1 → ℝ≥0 → X → ℝ} {VR : Fin 2 → ℝ≥0 → X → ℝ}
    {B : ℝ≥0 → X → ℝ} {ζ : X → ℝ≥0∞}
    (h : A1Marg.IsRegMarginal (kh κ) ![0] ![0, -x] (smallEightRhoL κ) (smallEightRhoR κ) P 𝓕 W VL VR B ζ) :
    ∀ᵐ ω ∂P, GoodSmallEight (W · ω) (fun i t => VL i t ω) (fun i t => VR i t ω) (B · ω) (ζ ω) :=
  A2P3ID.smallEight_sep hκ8 hx h.evol

/-- **(Eight, small) Seeds off the driver** (A1-EIGHTSEED's `hsep₁` at one sample). -/
theorem smallEight_sep_of_good {w : ℝ≥0 → ℝ} {vL : Fin 1 → ℝ≥0 → ℝ} {vR : Fin 2 → ℝ≥0 → ℝ} {b : ℝ≥0 → ℝ}
    {ζ : ℝ≥0∞} (hg : GoodSmallEight w vL vR b ζ) (s : ℝ≥0) (hs : 0 < s) (hsζ : (s : ℝ≥0∞) < ζ) :
    vL 0 s ≠ w s ∧ vR 0 s ≠ w s :=
  ⟨(hg s hs hsζ).1.ne, (hg s hs hsζ).2.ne'⟩

/-- **(Eight, small) The exit precedes the lifetime** at every good sample with a continuous Brownian path, for a
bounded `ℍ`-hull enclosure `E ∋ 0` (in closure) protected from the other source `−x`. -/
theorem lifeExit_lt_smallEight (hκ8 : 8 ≤ κ) (hx : x < 0) {w : ℝ≥0 → ℝ} {vL : Fin 1 → ℝ≥0 → ℝ}
    {vR : Fin 2 → ℝ≥0 → ℝ} {b : ℝ≥0 → ℝ} {ζ : ℝ≥0∞}
    (hP : IsIntegratedSLEPath (kh κ) ![0] ![0, -x] (smallEightRhoL κ) (smallEightRhoR κ) w vL vR b ζ)
    (hg : GoodSmallEight w vL vR b ζ) (hb : Continuous b) {E : Set ℂ} {R : ℝ} (hR : 0 < R)
    (hER : E ⊆ closedBall (0 : ℂ) R) (hE : IsHPHull E) (h0E : (0 : ℂ) ∈ closure E) {ρ : ℝ} (hρ : 0 < ρ)
    (hpE : Disjoint (ball ((-x : ℝ) : ℂ) ρ) E) (N : ℝ≥0) : (lifeExit w ζ E N : ℝ≥0∞) < ζ :=
  lifeExit_lt_of_protected hP hb hR hER hE h0E (fun i => by fin_cases i; rfl)
    (fun i s hs hsζ => by fin_cases i; exact (hg s hs hsζ).1.ne) (j := 1) (fun i => by fin_cases i <;> decide) hρ
    (by simpa using hpE) (by simp; linarith) (not_threshold_smallEight hκ8) N

/-- **(Eight, large) The exit precedes the lifetime** at every sample with a continuous Brownian path, for a bounded
`ℍ`-hull enclosure `E` (in the large curve's own frame, `0` in its closure) protected from the mark `x`. -/
theorem lifeExit_lt_largeEight (hx : x < 0) {w : ℝ≥0 → ℝ} {vL : Fin 1 → ℝ≥0 → ℝ}
    {vR : Fin 0 → ℝ≥0 → ℝ} {b : ℝ≥0 → ℝ} {ζ : ℝ≥0∞}
    (hP : IsIntegratedSLEPath κ ![x] ![] ![0] ![] w vL vR b ζ) (hb : Continuous b) {E : Set ℂ} {R : ℝ}
    (hR : 0 < R) (hER : E ⊆ closedBall (0 : ℂ) R) (hE : IsHPHull E) (h0E : (0 : ℂ) ∈ closure E) {ρ : ℝ}
    (hρ : 0 < ρ) (hxE : Disjoint (ball (x : ℂ) ρ) E) (N : ℝ≥0) : (lifeExit w ζ E N : ℝ≥0∞) < ζ :=
  lifeExit_lt_of_protected_left hP hb hR hER hE h0E (j := 0) (fun i => by fin_cases i; decide) hρ
    (by simpa using hxE) (by simp; linarith) (fun w₀ vL₀ vR₀ _ => not_threshold_largeEight w₀ vL₀ vR₀) N

end Eight

/-! ### (G3) -/

section G3

variable {κ x y : ℝ}

/-- **(G3, small)** The threshold condition fails whenever the other source `−y` is off the driver. -/
theorem not_threshold_smallG3 (hκ4 : 4 < κ) (hκ8 : κ < 8) (w₀ : ℝ) (vL₀ : Fin 1 → ℝ) (vR₀ : Fin 3 → ℝ)
    (h : vR₀ 2 ≠ w₀) : ¬ ForceWord.ThresholdCondition (smallG3RhoL κ) (smallG3RhoR κ) w₀ vL₀ vR₀ := by
  obtain ⟨hk2, hk4⟩ := kh_bounds_G3 hκ4 hκ8
  simp only [ForceWord.ThresholdCondition, Finset.sum_filter, Fin.sum_univ_one, Fin.sum_univ_three, smallG3RhoL,
    smallG3RhoR, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, h, ite_false, add_zero, not_or,
    not_le]
  constructor <;> split_ifs <;> linarith

/-- **(G3, large)** The threshold condition fails whenever the mark `y` is off the driver. -/
theorem not_threshold_largeG3 (hκ4 : 4 < κ) (w₀ : ℝ) (vL₀ : Fin 2 → ℝ) (vR₀ : Fin 0 → ℝ) (h : vL₀ 1 ≠ w₀) :
    ¬ ForceWord.ThresholdCondition (![κ - 4, -4] : Fin 2 → ℝ) ![] w₀ vL₀ vR₀ := by
  simp only [ForceWord.ThresholdCondition, Finset.sum_filter, Fin.sum_univ_two, Finset.univ_eq_empty,
    Finset.sum_empty, Matrix.cons_val_zero, Matrix.cons_val_one, h, ite_false, add_zero, not_or, not_le]
  constructor
  · split_ifs <;> linarith
  · norm_num

/-- The every-sample separation of the small (G3) curve: the seeds and the ordinary mark strictly in order at positive
times. -/
def GoodSmallG3 (w : ℝ≥0 → ℝ) (vL : Fin 1 → ℝ≥0 → ℝ) (vR : Fin 3 → ℝ≥0 → ℝ) (_b : ℝ≥0 → ℝ) (ζ : ℝ≥0∞) : Prop :=
  ∀ t : ℝ≥0, 0 < t → (t : ℝ≥0∞) < ζ → vL 0 t < w t ∧ w t < vR 0 t ∧ vR 0 t < vR 1 t

/-- **The small (G3) curve is good almost surely** (A2-P3-ID's `smallG3_sep`). -/
theorem ae_goodSmallG3 (hκ4 : 4 < κ) (hκ8 : κ < 8) (hyx : y < x) (hx : x < 0) {X : Type*} {mX : MeasurableSpace X}
    {P : Measure X} {𝓕 : Filtration ℝ≥0 mX} {W : ℝ≥0 → X → ℝ} {VL : Fin 1 → ℝ≥0 → X → ℝ}
    {VR : Fin 3 → ℝ≥0 → X → ℝ} {B : ℝ≥0 → X → ℝ} {ζ : X → ℝ≥0∞}
    (h : A1Marg.IsRegMarginal (kh κ) ![0] ![0, x - y, -y] (smallG3RhoL κ) (smallG3RhoR κ) P 𝓕 W VL VR B ζ) :
    ∀ᵐ ω ∂P, GoodSmallG3 (W · ω) (fun i t => VL i t ω) (fun i t => VR i t ω) (B · ω) (ζ ω) :=
  A2P3ID.smallG3_sep hκ4 hκ8 hyx hx h.evol

variable {w : ℝ≥0 → ℝ} {vL : Fin 1 → ℝ≥0 → ℝ} {vR : Fin 3 → ℝ≥0 → ℝ} {b : ℝ≥0 → ℝ} {ζ : ℝ≥0∞}

/-- **(G3, small) Seeds off the driver** (`hsep₁` at one sample). -/
theorem smallG3_sep_of_good (hg : GoodSmallG3 w vL vR b ζ) (s : ℝ≥0) (hs : 0 < s) (hsζ : (s : ℝ≥0∞) < ζ) :
    vL 0 s ≠ w s ∧ vR 0 s ≠ w s :=
  ⟨(hg s hs hsζ).1.ne, (hg s hs hsζ).2.1.ne'⟩

/-- **(G3, small) The ordinary mark is off the driver before the lifetime** (A1-G3CALC's `hsepO` at one sample). -/
theorem smallG3_sepO_of_good (hyx : y < x)
    (hP : IsIntegratedSLEPath (kh κ) ![0] ![0, x - y, -y] (smallG3RhoL κ) (smallG3RhoR κ) w vL vR b ζ)
    (hg : GoodSmallG3 w vL vR b ζ) (s : ℝ≥0) (hsζ : (s : ℝ≥0∞) < ζ) : vR 1 s ≠ w s := by
  rcases eq_zero_or_pos s with rfl | hs
  · rw [hP.2.2.1 1, hP.1]; simp; linarith
  · obtain ⟨-, h1, h2⟩ := hg s hs hsζ
    exact (h1.trans h2).ne'

/-- **(G3, small) The other source is off the driver before the lifetime** (A1-G3CALC's `hneP` at one sample). -/
theorem smallG3_sepP_of_good (hκ4 : 4 < κ) (hκ8 : κ < 8) (hyx : y < x) (hx : x < 0)
    (hP : IsIntegratedSLEPath (kh κ) ![0] ![0, x - y, -y] (smallG3RhoL κ) (smallG3RhoR κ) w vL vR b ζ)
    (hg : GoodSmallG3 w vL vR b ζ) (s : ℝ≥0) (hsζ : (s : ℝ≥0∞) < ζ) : vR 2 s ≠ w s := by
  rcases eq_zero_or_pos s with rfl | hs
  · rw [hP.2.2.1 2, hP.1]; simp; linarith
  · obtain ⟨-, h1, h2⟩ := hg s hs hsζ
    exact ((h1.trans h2).trans (P3.smallG3_vR_one_lt_two hκ4 hκ8 hx hP hsζ)).ne'

/-- **(G3, small) The exit precedes the lifetime** at every good sample with a continuous Brownian path, for a bounded
`ℍ`-hull enclosure `E ∋ 0` (in closure) protected from the other source `−y`. -/
theorem lifeExit_lt_smallG3 (hκ4 : 4 < κ) (hκ8 : κ < 8) (hy : y < 0)
    (hP : IsIntegratedSLEPath (kh κ) ![0] ![0, x - y, -y] (smallG3RhoL κ) (smallG3RhoR κ) w vL vR b ζ)
    (hg : GoodSmallG3 w vL vR b ζ) (hb : Continuous b) {E : Set ℂ} {R : ℝ} (hR : 0 < R)
    (hER : E ⊆ closedBall (0 : ℂ) R) (hE : IsHPHull E) (h0E : (0 : ℂ) ∈ closure E) {ρ : ℝ} (hρ : 0 < ρ)
    (hpE : Disjoint (ball ((-y : ℝ) : ℂ) ρ) E) (N : ℝ≥0) : (lifeExit w ζ E N : ℝ≥0∞) < ζ :=
  lifeExit_lt_of_protected hP hb hR hER hE h0E (fun i => by fin_cases i; rfl)
    (fun i s hs hsζ => by fin_cases i; exact (hg s hs hsζ).1.ne) (j := 2) (fun i => by fin_cases i <;> decide) hρ
    (by simpa using hpE) (by simp; linarith) (not_threshold_smallG3 hκ4 hκ8) N

/-- **(G3, large) The exit precedes the lifetime** at every sample with a continuous Brownian path, for a bounded
`ℍ`-hull enclosure `E` (in the large curve's own frame, `0` in its closure) protected from the mark `y`. -/
theorem lifeExit_lt_largeG3 (hκ4 : 4 < κ) (hy : y < 0) {w : ℝ≥0 → ℝ} {vL : Fin 2 → ℝ≥0 → ℝ}
    {vR : Fin 0 → ℝ≥0 → ℝ} {b : ℝ≥0 → ℝ} {ζ : ℝ≥0∞}
    (hP : IsIntegratedSLEPath κ ![x, y] ![] ![κ - 4, -4] ![] w vL vR b ζ) (hb : Continuous b) {E : Set ℂ} {R : ℝ}
    (hR : 0 < R) (hER : E ⊆ closedBall (0 : ℂ) R) (hE : IsHPHull E) (h0E : (0 : ℂ) ∈ closure E) {ρ : ℝ}
    (hρ : 0 < ρ) (hyE : Disjoint (ball (y : ℂ) ρ) E) (N : ℝ≥0) : (lifeExit w ζ E N : ℝ≥0∞) < ζ :=
  lifeExit_lt_of_protected_left hP hb hR hER hE h0E (j := 1) (fun i => by fin_cases i <;> decide) hρ
    (by simpa using hyE) (by simp; linarith) (not_threshold_largeG3 hκ4) N

end G3

end InteractingSLE.ZhanGT4.A1Common
