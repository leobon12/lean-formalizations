/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.ZhanGT4.MixtureA33ChordalScale

/-!
# (G3) in chordal coordinates, unconditionally

Packet PROVE-ZHAN-A33 (Astra, *Follow-up proofs* §A.3.2, L686–L705; ruling R36). For `κ ≥ 4` the chordal integrated
`SLE_κ(κ − 4, −4)` evolution from `(0; −1, y)`, `y = −1 − e^u`, has an almost surely unbounded strip clock of the end
mark `−1` on its strip life (`ae_hasUnboundedStripClock_a33`). Hence (`MixtureA33ChordalForced.lean`) its strip driver
is PROVE-ZHAN-A32's forced driver `forcedDrv κ σ u B̃`, `σ = 3 − κ/2` (`exists_stripDriver_eq_forcedDrv_a33`), and
its law is the forced law, the `u`-component of A32's mixture (`map_stripDriver_eq_forcedLaw_a33`): **the original
killed chordal law is the `f(u) du`-mixture of these `SLE_κ(κ − 4, −4)` laws** in strip coordinates.

## Proof of the unbounded clock

Scale by `c = |y|² = (1 + e^u)²` (`isIntegratedSLEEvolution_scale`): the scaled evolution has left marks
`(−1/|y|, −1)`, i.e. it is the R36 strip evolution `Strip.IsStripSLEEvolution κ ![p] ![] ![κ − 4] ![] (−4)` with the
lower mark `p = log(1 − 1/|y|) < 0` and the end mark the scaled `y`. Its word is separated and has the prefix sums of
(3.3) (`κ − 4 ≥ κ/2 − 2`), so PROVE-ZHAN-A3's `ae_hasUnboundedStripClock` and `ae_stripLife_noncollision` apply: the
clock of the end `y` is unbounded on its strip life, and the mark `−1` stays strictly left of the driver there. The two
strip lives therefore coincide and, since `0 < W − V_{−1} ≤ W − V_y`, the clock of `−1` dominates the clock of `y`.
Scale back (`hasUnboundedStripClock_of_scale`).
-/

set_option autoImplicit false

noncomputable section

open Set Filter MeasureTheory ProbabilityTheory Topology
open scoped NNReal ENNReal

namespace InteractingSLE.ZhanGT4.UpMark

open Zhan Mix

variable {Ω : Type*} {mΩ : MeasurableSpace Ω}

/-- The scale `c = (1 + e^u)²`. -/
def a33Scale (u : ℝ) : ℝ≥0 := ((1 + Real.exp u) ^ 2).toNNReal

theorem a33Scale_ne_zero (u : ℝ) : a33Scale u ≠ 0 := by
  rw [a33Scale, Ne, Real.toNNReal_eq_zero, not_le]; positivity

theorem sqrt_a33Scale (u : ℝ) : Real.sqrt (a33Scale u) = 1 + Real.exp u := by
  rw [a33Scale, Real.coe_toNNReal _ (by positivity), Real.sqrt_sq (by positivity)]

/-- The lower strip mark of the scaled word: `log(1 − 1/(1 + e^u))`. -/
def a33LowMark (u : ℝ) : ℝ := Real.log (1 - (1 + Real.exp u)⁻¹)

theorem a33_one_sub_pos (u : ℝ) : 0 < 1 - (1 + Real.exp u)⁻¹ := by
  have h : (1 + Real.exp u)⁻¹ < 1 := inv_lt_one_of_one_lt₀ (by linarith [Real.exp_pos u])
  linarith

theorem a33LowMark_neg (u : ℝ) : a33LowMark u < 0 := by
  refine Real.log_neg (a33_one_sub_pos u) ?_
  have : 0 < (1 + Real.exp u)⁻¹ := inv_pos.2 (by positivity)
  linarith

/-- The scaled word is the R36 word of the lower mark `a33LowMark u`. -/
theorem a33_scaled_wordXL (u : ℝ) :
    (fun i => (Real.sqrt (a33Scale u))⁻¹ * upWordXL ![u] i) = Strip.wordXL ![a33LowMark u] := by
  funext i
  rw [sqrt_a33Scale]
  have hpos : 0 < 1 + Real.exp u := by positivity
  fin_cases i
  · simp only [Fin.zero_eta, upWordXL_zero, Strip.wordXL, a33LowMark]
    rw [show (0 : Fin 2) = (0 : Fin 1).castSucc from rfl, Fin.snoc_castSucc]
    simp only [Matrix.cons_val_zero]
    rw [Real.exp_log (a33_one_sub_pos u)]
    ring
  · simp only [Fin.mk_one, Strip.wordXL]
    rw [show (1 : Fin 2) = Fin.last 1 from rfl, Fin.snoc_last]
    rw [show (Fin.last 1 : Fin (1 + 1)) = (0 : Fin 1).succ from rfl, upWordXL_succ]
    simp only [Matrix.cons_val_zero]
    field_simp
    ring

theorem a33_rhoL (κ : ℝ) : a33RhoL κ = Strip.wordRhoL ![κ - 4] (-4) := by
  funext i
  fin_cases i <;> rfl

/-- **The strip clock of the end mark `−1` is almost surely unbounded on the strip life** for the chordal integrated
`SLE_κ(κ − 4, −4)` evolution from `(0; −1, −1 − e^u)`, `κ ≥ 4`. -/
theorem ae_hasUnboundedStripClock_a33 {κ u : ℝ} (hκ : 4 ≤ κ) {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    {W : ℝ≥0 → Ω → ℝ} {VL : Fin 2 → ℝ≥0 → Ω → ℝ} {VR : Fin 0 → ℝ≥0 → Ω → ℝ} {B : ℝ≥0 → Ω → ℝ}
    {ζ : Ω → ℝ≥0∞} (hE : IsIntegratedSLEEvolution κ (upWordXL ![u]) ![] (a33RhoL κ) ![] P 𝓕 W VL VR B ζ) :
    ∀ᵐ ω ∂P, HasUnboundedStripClock (W · ω) (VL 0 · ω) (ζ ω) := by
  have hκ0 : 0 < κ := by linarith
  set c := a33Scale u with hcdef
  have hc : c ≠ 0 := a33Scale_ne_zero u
  set a : ℝ := (Real.sqrt c)⁻¹ with hadef
  have ha : 0 < a := scaleFactor_pos hc
  have hac : a ^ 2 * c = 1 := scaleFactor_sq_mul hc
  have hE1 := isIntegratedSLEEvolution_scale hc hE
  have hxR : (fun j : Fin 0 => (Real.sqrt c)⁻¹ * (![] : Fin 0 → ℝ) j) = Strip.wordXR ![] := funext fun j => j.elim0
  rw [a33_scaled_wordXL, hxR, a33_rhoL] at hE1
  have hE' : Strip.IsStripSLEEvolution κ ![a33LowMark u] ![] ![κ - 4] ![] (-4) P (scaleFilt 𝓕 c) (scaleProc c W)
      (fun i => scaleProc c (VL i)) (fun j => scaleProc c (VR j)) (scaleProc c B) (fun ω => ζ ω / c) := hE1
  have hsep : Strip.IsSeparatedStripWord ![a33LowMark u] (![] : Fin 0 → ℝ) := by
    refine ⟨fun i j hij => ?_, fun i => ?_, fun i => i.elim0, fun i => i.elim0⟩
    · exact absurd hij (by fin_cases i; fin_cases j; simp)
    · fin_cases i; simpa using a33LowMark_neg u
  have hpre : Strip.HasStripPrefixSums κ ![κ - 4] (![] : Fin 0 → ℝ) := by
    refine ⟨fun j => ?_, fun j => j.elim0⟩
    fin_cases j
    simp only [Fin.zero_eta]
    rw [show (Finset.Iic (0 : Fin 1)) = {0} from rfl, Finset.sum_singleton]
    simp only [Matrix.cons_val_zero]
    linarith
  filter_upwards [ae_hasUnboundedStripClock hκ0 hsep hpre hE', ae_stripLife_noncollision hκ0 hsep hpre hE',
    hE'.2.2.2.2] with ω hcl hnc hp
  -- the clock of the scaled end `−1` (index `0`)
  have hF := hp.isForcePath
  have hcl0 : HasUnboundedStripClock (scalePath a c (W · ω)) (scalePath a c (VL 0 · ω)) (ζ ω / c) := by
    intro T
    obtain ⟨s, hs, hT⟩ := hcl T
    have hlife0 : Strip.IsStripLife (scalePath a c (W · ω)) (scalePath a c (VL 0 · ω)) (ζ ω / c) s :=
      ⟨hs.1, fun r hr => (hnc r (hs.mono hr)).1 0⟩
    refine ⟨s, hlife0, hT.trans ?_⟩
    have hint1 := Zhan.intervalIntegrable_clockRate hF hs
    have hint0 := UpMark.intervalIntegrable_clockRate (vL := fun i t => scaleProc c (VL i) t ω) hF hlife0
    refine intervalIntegral.integral_mono_on s.coe_nonneg hint1 hint0 fun r hr => ?_
    have hr' : r.toNNReal ≤ s := Sec2.toNNReal_le_of_mem_Icc hr
    have hrζ : (r.toNNReal : ℝ≥0∞) < ζ ω / c := lt_of_le_of_lt (by exact_mod_cast hr') hs.1
    have h0 : 0 < scaleProc c W r.toNNReal ω - scaleProc c (VL 0) r.toNNReal ω :=
      sub_pos.2 (hlife0.2 _ hr')
    have hle : scaleProc c (VL (Fin.last 1)) r.toNNReal ω ≤ scaleProc c (VL 0) r.toNNReal ω :=
      hp.2.2.2.2.2.2.1 _ hrζ (Fin.zero_le _)
    simp only [Strip.extPath]
    exact inv_anti₀ (by positivity) (pow_le_pow_left₀ h0.le (by linarith) 2)
  exact hasUnboundedStripClock_of_scale hc ha hac hcl0

/-- **(G3), chordal form, pathwise** (`κ ≥ 4`): for the chordal integrated `SLE_κ(κ − 4, −4)` evolution from
`(0; −1, −1 − e^u)` there is a Brownian motion `B̃` (continuous paths, `B̃₀ = 0`) such that almost surely its strip
driver is `forcedDrv κ (3 − κ/2) u B̃` at every strip time. -/
theorem exists_stripDriver_eq_forcedDrv_a33 {κ u : ℝ} (hκ : 4 ≤ κ) {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    {W : ℝ≥0 → Ω → ℝ} {VL : Fin 2 → ℝ≥0 → Ω → ℝ} {VR : Fin 0 → ℝ≥0 → Ω → ℝ} {B : ℝ≥0 → Ω → ℝ}
    {ζ : Ω → ℝ≥0∞} (hE : IsIntegratedSLEEvolution κ (upWordXL ![u]) ![] (a33RhoL κ) ![] P 𝓕 W VL VR B ζ) :
    ∃ (𝓗 : Filtration ℝ≥0 mΩ) (B' : ℝ≥0 → Ω → ℝ), IsFilteredBrownianReal 𝓗 B' P ∧
      (∀ ω, Continuous (B' · ω)) ∧ (∀ ω, B' 0 ω = 0) ∧
      ∀ᵐ ω ∂P, ∀ t : ℝ≥0, Strip.stripDriver (Strip.extPath (W · ω)) (Strip.extPath (VL 0 · ω)) t =
        forcedDrv κ (3 - κ / 2) (fun _ => u) B' t ω :=
  exists_stripDriver_eq_forcedDrv (by linarith) hE (ae_hasUnboundedStripClock_a33 hκ hE)

/-- **(G3), chordal form, in law** (`κ ≥ 4`): the law of the strip driver path of the chordal integrated
`SLE_κ(κ − 4, −4)` evolution from `(0; −1, −1 − e^u)` is the forced law `Law(forcedPath κ (3 − κ/2) u β)` of any
Brownian motion `β`, the `u`-component of PROVE-ZHAN-A32's mixture `mixLaw` (`Mix.mixLaw_eq_map_prod`). -/
theorem map_stripDriver_eq_forcedLaw_a33 {κ u : ℝ} (hκ : 4 ≤ κ) {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    {W : ℝ≥0 → Ω → ℝ} {VL : Fin 2 → ℝ≥0 → Ω → ℝ} {VR : Fin 0 → ℝ≥0 → Ω → ℝ} {B : ℝ≥0 → Ω → ℝ}
    {ζ : Ω → ℝ≥0∞} (hE : IsIntegratedSLEEvolution κ (upWordXL ![u]) ![] (a33RhoL κ) ![] P 𝓕 W VL VR B ζ)
    {Ω' : Type*} {mΩ' : MeasurableSpace Ω'} {Q : Measure Ω'} {β : ℝ≥0 → Ω' → ℝ} (hβ : IsPreBrownianReal β Q)
    (hβm : ∀ t, Measurable (β t)) :
    P.map (fun ω (t : ℝ≥0) => Strip.stripDriver (Strip.extPath (W · ω)) (Strip.extPath (VL 0 · ω)) t) =
      Q.map fun ω' => forcedPath κ (3 - κ / 2) u (pathOf β ω') :=
  map_stripDriver_eq_forcedLaw (by linarith) hE (ae_hasUnboundedStripClock_a33 hκ hE) hβ hβm

end InteractingSLE.ZhanGT4.UpMark
