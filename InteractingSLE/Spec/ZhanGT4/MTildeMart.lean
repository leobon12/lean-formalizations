/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.ZhanGT4.FrozenMeas
import InteractingSLE.Stochastic.ItoAdaptedStop
import InteractingSLE.Spec.Sec6.Prop65Point

/-!
# The stopped martingale of an exponential log-field along a Brownian driver

Packet PROVE-ZHAN-GT4-A8. Source: Astra, *Follow-up proofs*, §A.1.2–A.1.3 (`ig1_followup_proofs.txt` L268–L341, R38):
"First suppose `W_j` has zero drift … Hence the drift is zero", with the other curve frozen; (D9) bounds `M̃` on the
protected rectangle. A7 (`ItoFieldFrozen`, `MTildeBoundField`) proved the deterministic half: on every time piece on
which the driver stays near a fixed centre `y`, `log M̃` is a regular log-field (`IsLogField`, with a path-independent
bound), and the generator of `M̃` vanishes along the curve. This file supplies the stochastic glue, for a general
log-field `ℓ(ω, t, x)` along the driver `W = σB`:

* on each piece `[a, b]` of a grid the cut-off centre is frozen at `σ B_a`, and the piece is stopped at the first time
  the driver moves `ρ/2` away from it (`pieceExit`, a capped hitting time, `Prop65.hitLe`) and at `S`; the stopped
  Itô theorem for adapted fields (`Ito.integral_mul_fieldStopped_sub_eq_zero`) gives a zero-mean increment;
* the increments of the pieces telescope up to the first piece that is exited early (`goodE`); as the mesh tends to
  zero no piece is exited early (uniform continuity of the path), and dominated convergence (`|M| ≤ e^K`) gives

  `E[ξ (M_{t∧S} − M_{s∧S})] = 0` for bounded `𝓕_s`-measurable `ξ`, `M_r = exp ℓ(r, σB_r)`.

## Main results

* `pieceExit`, `isStoppingTime_pieceExit`, `le_pieceExit`, `abs_sub_le_of_le_pieceExit`, `pieceExit_eq_of_forall`;
* `integral_mul_piece_eq_zero` (one piece) and **`integral_mul_logField_stopped_sub_eq_zero`** (the martingale
  identity).
-/

set_option autoImplicit false

noncomputable section

open Set Filter Topology MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace InteractingSLE.ZhanGT4

open Sec6.Prop65 (hitLe)

/-! ### The exit time of a piece -/

section Piece

variable {Ω : Type*}

/-- The level process of a piece starting at `a`: `ρ/2 − |σ(B_{u∨a} − B_a)|` (equal to `ρ/2` before `a`). -/
def pieceY (σ ρ : ℝ) (B : ℝ≥0 → Ω → ℝ) (a : ℝ≥0) (u : ℝ≥0) (ω : Ω) : ℝ :=
  ρ / 2 - |σ * (B (max u a) ω - B a ω)|

/-- **The exit time of the piece `[a, b]`**: the first time the driver `σB` is `ρ/2` away from `σB_a`, capped at `b`. -/
def pieceExit (σ ρ : ℝ) (B : ℝ≥0 → Ω → ℝ) (a b : ℝ≥0) (ω : Ω) : ℝ≥0 := hitLe (pieceY σ ρ B a) 0 b ω

variable {σ ρ : ℝ} {B : ℝ≥0 → Ω → ℝ} {a b : ℝ≥0}

theorem continuous_pieceY (hBc : ∀ ω, Continuous (B · ω)) (ω : Ω) :
    Continuous fun u => pieceY σ ρ B a u ω :=
  continuous_const.sub ((continuous_const.mul (((hBc ω).comp (continuous_id.max continuous_const)).sub
    continuous_const)).abs)

theorem pieceY_of_le {u : ℝ≥0} (hu : u ≤ a) (ω : Ω) : pieceY σ ρ B a u ω = ρ / 2 := by
  simp [pieceY, max_eq_right hu]

theorem pieceExit_le (ω : Ω) : pieceExit σ ρ B a b ω ≤ b := Sec6.Prop65.hitLe_le _ _ _ _

theorem le_pieceExit (hBc : ∀ ω, Continuous (B · ω)) (hρ : 0 < ρ) (hab : a ≤ b) (ω : Ω) :
    a ≤ pieceExit σ ρ B a b ω :=
  Sec6.Prop65.le_hitLe_of_forall (fun ω => continuous_pieceY hBc ω) hab fun u hu => by
    rw [pieceY_of_le hu]; linarith

/-- Up to the exit time, the driver stays within `ρ/2` of the frozen centre. -/
theorem abs_sub_le_of_le_pieceExit (hBc : ∀ ω, Continuous (B · ω)) (hρ : 0 < ρ) {ω : Ω} {u : ℝ≥0}
    (hau : a ≤ u) (hu : u ≤ pieceExit σ ρ B a b ω) : |σ * B u ω - σ * B a ω| ≤ ρ / 2 := by
  have h0 : (0 : ℝ) < pieceY σ ρ B a 0 ω := by rw [pieceY_of_le zero_le]; linarith
  have h := Sec6.Prop65.le_of_le_hitLe (fun ω => continuous_pieceY hBc ω) h0 hu
  simp only [pieceY, max_eq_left hau] at h
  rw [← mul_sub]
  linarith

/-- If the driver stays strictly within `ρ/2` of the centre on `[a, b]`, the piece is not exited early. -/
theorem pieceExit_eq_of_forall (hBc : ∀ ω, Continuous (B · ω)) (hρ : 0 < ρ) {ω : Ω}
    (h : ∀ u : ℝ≥0, a ≤ u → u ≤ b → |σ * B u ω - σ * B a ω| < ρ / 2) : pieceExit σ ρ B a b ω = b := by
  refine le_antisymm (pieceExit_le ω) (Sec6.Prop65.le_hitLe_of_forall (fun ω => continuous_pieceY hBc ω) le_rfl
    fun u hu => ?_)
  rcases le_total u a with hua | hau
  · rw [pieceY_of_le hua]; linarith
  · have := h u hau hu
    simp only [pieceY, max_eq_left hau]
    rw [mul_sub]
    linarith

variable {mΩ : MeasurableSpace Ω} {𝓕 : Filtration ℝ≥0 mΩ}

theorem measurable_pieceY (hBm : ∀ u, Measurable[𝓕 u] (B u)) (u : ℝ≥0) :
    Measurable[𝓕 u] (pieceY σ ρ B a u) := by
  rcases le_total u a with hua | hau
  · have : pieceY σ ρ B a u = fun _ => ρ / 2 := funext fun ω => pieceY_of_le hua ω
    rw [this]; exact measurable_const
  · have hBa : Measurable[𝓕 u] (B a) := (hBm a).mono (𝓕.mono hau) le_rfl
    show Measurable[𝓕 u] fun ω => ρ / 2 - |σ * (B (max u a) ω - B a ω)|
    rw [max_eq_left hau]
    have hg : Continuous fun p : ℝ × ℝ => ρ / 2 - |σ * (p.1 - p.2)| := by fun_prop
    exact hg.measurable.comp ((hBm u).prodMk hBa)

theorem isStoppingTime_pieceExit (hBc : ∀ ω, Continuous (B · ω)) (hBm : ∀ u, Measurable[𝓕 u] (B u)) :
    IsStoppingTime 𝓕 fun ω => (pieceExit σ ρ B a b ω : WithTop ℝ≥0) :=
  Sec6.Prop65.isStoppingTime_hitLe (fun ω => continuous_pieceY hBc ω) (measurable_pieceY hBm) 0 b

end Piece

/-! ### Cut-off functions: a bound uniform in the centre, joint continuity -/

theorem cutChi_shift (k : ℕ) (y ρ x : ℝ) : cutChi k y ρ x = cutChi k 0 ρ (x - y) := by
  simp [cutChi]

/-- A bound for the cut-off derivatives that does not depend on the centre. -/
theorem exists_bound_cutChi_uniform (ρ : ℝ) :
    ∃ C, 0 ≤ C ∧ ∀ y : ℝ, ∀ k ≤ 4, ∀ x, |cutChi k y ρ x| ≤ C := by
  obtain ⟨C, hC, hb⟩ := exists_bound_cutChi 0 ρ
  exact ⟨C, hC, fun y k hk x => by rw [cutChi_shift]; exact hb k hk _⟩

theorem continuous_cutChi_uncurry (k : ℕ) (ρ : ℝ) : Continuous fun p : ℝ × ℝ => cutChi k p.1 ρ p.2 :=
  continuous_const.mul ((continuous_iterDeriv_stdBump k).comp ((continuous_snd.sub continuous_fst).div_const ρ))

/-! ### The log-field along the driver -/

section Setting

variable {Ω : Type*} {mΩ : MeasurableSpace Ω}

/-- The exponential `exp ℓ(r, σB_r)` of a log-field along the driver `σB`. -/
def logFieldExp (σ : ℝ) (B : ℝ≥0 → Ω → ℝ) (ℓ : Ω → ℝ → ℝ → ℝ) (r : ℝ≥0) (ω : Ω) : ℝ :=
  Real.exp (ℓ ω r (σ * B r ω))

/-- **A log-field along the driver `σB` up to the time `S`** (the abstract form of A7's `FrzData.isLogField_of_D9`,
`FrzData.cutField_gen_eq_zero_of_D9` and the measurability of the frozen factors):
* `loc`: on every interval `[b, c] ⊆ [0, S]` on which the driver stays within `ρ` of a centre `y`, `ℓ` is a regular
  log-field on `[b, c] × (y − 3ρ, y + 3ρ)` with the bound `K`;
* `gen`: the generator of `e^ℓ` vanishes along the driver, `ℓ_t + (σ²/2)(ℓ_xx + ℓ_x²) = 0` at `(r, σB_r)`, `r ≤ S`;
* `meas0`–`meas2`: `ℓ`, `ℓ_x`, `ℓ_xx` along the driver are adapted on `{r ≤ S}`. -/
structure IsDriverLogField (𝓕 : Filtration ℝ≥0 mΩ) (σ ρ K : ℝ) (B : ℝ≥0 → Ω → ℝ) (S : Ω → ℝ≥0)
    (ℓ ℓx ℓxx ℓxxx ℓt : Ω → ℝ → ℝ → ℝ) : Prop where
  loc : ∀ ω (b c y : ℝ), 0 ≤ b → b ≤ c → c ≤ S ω → (∀ r ∈ Icc b c, |σ * B r.toNNReal ω - y| < ρ) →
    IsLogField (ℓ ω) (ℓx ω) (ℓxx ω) (ℓxxx ω) (ℓt ω) b c y ρ K
  gen : ∀ ω (r : ℝ), 0 ≤ r → r ≤ S ω → ℓt ω r (σ * B r.toNNReal ω) +
    σ ^ 2 / 2 * (ℓxx ω r (σ * B r.toNNReal ω) + ℓx ω r (σ * B r.toNNReal ω) ^ 2) = 0
  meas0 : ∀ r : ℝ≥0, Measurable[𝓕 r] ({ω | r ≤ S ω}.indicator fun ω => ℓ ω r (σ * B r ω))
  meas1 : ∀ r : ℝ≥0, Measurable[𝓕 r] ({ω | r ≤ S ω}.indicator fun ω => ℓx ω r (σ * B r ω))
  meas2 : ∀ r : ℝ≥0, Measurable[𝓕 r] ({ω | r ≤ S ω}.indicator fun ω => ℓxx ω r (σ * B r ω))

namespace IsDriverLogField

variable {𝓕 : Filtration ℝ≥0 mΩ} {σ ρ K : ℝ} {B : ℝ≥0 → Ω → ℝ} {S : Ω → ℝ≥0}
  {ℓ ℓx ℓxx ℓxxx ℓt : Ω → ℝ → ℝ → ℝ} (hL : IsDriverLogField 𝓕 σ ρ K B S ℓ ℓx ℓxx ℓxxx ℓt)
include hL

omit hL in
theorem continuous_driver (hBc : ∀ ω, Continuous (B · ω)) (ω : Ω) :
    Continuous fun r : ℝ => σ * B r.toNNReal ω :=
  continuous_const.mul ((hBc ω).comp continuous_real_toNNReal)

/-- `ℓ` along the driver is continuous on `[0, S]`. -/
theorem continuousOn_driver (hBc : ∀ ω, Continuous (B · ω)) (hρ : 0 < ρ) (ω : Ω) :
    ContinuousOn (fun r : ℝ => ℓ ω r (σ * B r.toNNReal ω)) (Icc 0 (S ω)) := by
  intro r₀ hr₀
  have hf := continuous_driver (σ := σ) hBc ω
  obtain ⟨δ, hδ, hfδ⟩ := Metric.continuousAt_iff.1 hf.continuousAt ρ hρ
  set b := max 0 (r₀ - δ / 2)
  set c := min (S ω : ℝ) (r₀ + δ / 2)
  have hb0 : 0 ≤ b := le_max_left _ _
  have hbr : b ≤ r₀ := max_le hr₀.1 (by linarith)
  have hrc : r₀ ≤ c := le_min hr₀.2 (by linarith)
  have hcS : c ≤ S ω := min_le_left _ _
  have hdr : ∀ r ∈ Icc b c, |σ * B r.toNNReal ω - σ * B r₀.toNNReal ω| < ρ := fun r hr => by
    have h1 : r₀ - δ / 2 ≤ r := (le_max_right _ _).trans hr.1
    have h2 : r ≤ r₀ + δ / 2 := hr.2.trans (min_le_right _ _)
    have := hfδ (x := r) (by rw [Real.dist_eq, abs_lt]; constructor <;> linarith)
    rwa [Real.dist_eq] at this
  have hLF := hL.loc ω b c _ hb0 (hbr.trans hrc) hcS hdr
  have hmaps : MapsTo (fun r : ℝ => (r, σ * B r.toNNReal ω)) (Icc b c)
      (Icc b c ×ˢ {x | |x - σ * B r₀.toNNReal ω| < 3 * ρ}) := fun r hr =>
    ⟨hr, show |σ * B r.toNNReal ω - σ * B r₀.toNNReal ω| < 3 * ρ by have := hdr r hr; linarith⟩
  have hcomp := hLF.cont.comp (continuousOn_id.prodMk hf.continuousOn) hmaps
  have hmem : Icc b c ∈ 𝓝[Icc 0 (S ω : ℝ)] r₀ := by
    refine mem_nhdsWithin.2 ⟨Ioo (r₀ - δ / 2) (r₀ + δ / 2), isOpen_Ioo, ⟨by linarith, by linarith⟩, ?_⟩
    rintro r ⟨⟨hr1, hr2⟩, hr3, hr4⟩
    exact ⟨max_le hr3 hr1.le, le_min hr4 hr2.le⟩
  exact (hcomp r₀ ⟨hbr, hrc⟩).mono_of_mem_nhdsWithin hmem

/-- `ℓ` along the driver is bounded by `K` on `[0, S]`. -/
theorem abs_le (hρ : 0 < ρ) (ω : Ω) {r : ℝ} (hr : r ∈ Icc 0 (S ω : ℝ)) :
    |ℓ ω r (σ * B r.toNNReal ω)| ≤ K := by
  have hLF := hL.loc ω r r (σ * B r.toNNReal ω) hr.1 le_rfl hr.2 fun u hu => by
    rw [show u = r from le_antisymm hu.2 hu.1, sub_self, abs_zero]; exact hρ
  exact (hLF.bound r ⟨le_rfl, le_rfl⟩ _ (by rw [sub_self, abs_zero]; linarith)).1

/-- **The stopped exponential is adapted**: for a stopping time `T ≤ S`, `ω ↦ exp ℓ(r ∧ T, σB_{r∧T})` is
`𝓕_r`-measurable. -/
theorem measurable_logFieldExp_stopped (hBc : ∀ ω, Continuous (B · ω)) (hρ : 0 < ρ) {T : Ω → ℝ≥0}
    (hT : IsStoppingTime 𝓕 fun ω => (T ω : WithTop ℝ≥0)) (hTS : ∀ ω, T ω ≤ S ω) (r : ℝ≥0) :
    Measurable[𝓕 r] fun ω => logFieldExp σ B ℓ (min r (T ω)) ω := by
  have h := Ito.measurable_stopped_of_agree (β := ℝ) (X := fun u ω => logFieldExp σ B ℓ u ω)
    (K := fun u ω => Real.exp ({ω | u ≤ S ω}.indicator (fun ω => ℓ ω u (σ * B u ω)) ω)) hT
    (fun u => Real.continuous_exp.measurable.comp (hL.meas0 u)) (G := univ) MeasurableSet.univ 0
    (fun ω _ u hu => by
      simp only [logFieldExp]
      rw [indicator_of_mem (show ω ∈ {ω | u ≤ S ω} from hu.trans (hTS ω))])
    (fun ω _ => by
      have hc := hL.continuousOn_driver hBc hρ ω
      have hc' : ContinuousOn (fun u : ℝ≥0 => ℓ ω u (σ * B u ω)) (Iic (T ω)) := by
        have := hc.comp NNReal.continuous_coe.continuousOn (fun u hu =>
          ⟨u.coe_nonneg, NNReal.coe_le_coe.2 ((mem_Iic.1 hu).trans (hTS ω))⟩)
        simpa only [Function.comp_def, Real.toNNReal_coe] using this
      exact Real.continuous_exp.comp_continuousOn hc') r
  simpa only [mem_univ, ↓reduceIte] using h

end IsDriverLogField

end Setting

/-! ### One piece -/

section OnePiece

variable {Ω : Type*} {mΩ : MeasurableSpace Ω}

open scoped Classical in
/-- The cut-off field of the piece starting at `a` (centre `σB_a`) in the Brownian variable, `0` off the event `E`. -/
def pieceF (σ ρ : ℝ) (B : ℝ≥0 → Ω → ℝ) (ℓ : Ω → ℝ → ℝ → ℝ) (a : ℝ≥0) (E : Set Ω) (r : ℝ) (ω : Ω) (x : ℝ) : ℝ :=
  if ω ∈ E then cutField (ℓ ω) (σ * B a ω) ρ r (σ * x) else 0

open scoped Classical in
/-- Its first space derivative (`0` after `S`). -/
def pieceF1 (σ ρ : ℝ) (B : ℝ≥0 → Ω → ℝ) (S : Ω → ℝ≥0) (ℓ ℓx : Ω → ℝ → ℝ → ℝ) (a : ℝ≥0) (E : Set Ω) (r : ℝ)
    (ω : Ω) (x : ℝ) : ℝ :=
  if ω ∈ E ∧ r ≤ S ω then σ * cutField1 (ℓ ω) (ℓx ω) (σ * B a ω) ρ r (σ * x) else 0

open scoped Classical in
/-- Its second space derivative (`0` after `S`). -/
def pieceF2 (σ ρ : ℝ) (B : ℝ≥0 → Ω → ℝ) (S : Ω → ℝ≥0) (ℓ ℓx ℓxx : Ω → ℝ → ℝ → ℝ) (a : ℝ≥0) (E : Set Ω)
    (r : ℝ) (ω : Ω) (x : ℝ) : ℝ :=
  if ω ∈ E ∧ r ≤ S ω then σ ^ 2 * cutField2 (ℓ ω) (ℓx ω) (ℓxx ω) (σ * B a ω) ρ r (σ * x) else 0

open scoped Classical in
/-- Its time derivative. -/
def pieceFT (σ ρ : ℝ) (B : ℝ≥0 → Ω → ℝ) (ℓ ℓt : Ω → ℝ → ℝ → ℝ) (a : ℝ≥0) (E : Set Ω) (r : ℝ) (ω : Ω) (x : ℝ) :
    ℝ :=
  if ω ∈ E then cutFieldT (ℓ ω) (ℓt ω) (σ * B a ω) ρ r (σ * x) else 0

/-- The stopping time of the piece `[a, b]`: `S`, or the exit of the driver from `ρ/2` of `σB_a` (at least `a`). -/
def pieceStop (σ ρ : ℝ) (B : ℝ≥0 → Ω → ℝ) (S : Ω → ℝ≥0) (a b : ℝ≥0) (ω : Ω) : ℝ≥0 :=
  max a (min (S ω) (pieceExit σ ρ B a b ω))

variable {𝓕 : Filtration ℝ≥0 mΩ} {σ ρ K : ℝ} {B : ℝ≥0 → Ω → ℝ} {S : Ω → ℝ≥0}
  {ℓ ℓx ℓxx ℓxxx ℓt : Ω → ℝ → ℝ → ℝ} {a b : ℝ≥0} {E : Set Ω}

theorem le_pieceStop (ω : Ω) : a ≤ pieceStop σ ρ B S a b ω := le_max_left _ _

theorem pieceStop_eq (hBc : ∀ ω, Continuous (B · ω)) (hρ : 0 < ρ) (hab : a ≤ b) {ω : Ω} (haS : a ≤ S ω) :
    pieceStop σ ρ B S a b ω = min (S ω) (pieceExit σ ρ B a b ω) :=
  max_eq_right (le_min haS (le_pieceExit hBc hρ hab ω))

theorem pieceStop_le_S (hBc : ∀ ω, Continuous (B · ω)) (hρ : 0 < ρ) (hab : a ≤ b) {ω : Ω} (haS : a ≤ S ω) :
    pieceStop σ ρ B S a b ω ≤ S ω := by
  rw [pieceStop_eq hBc hρ hab haS]; exact min_le_left _ _

/-- Up to the piece stop, the driver is within `ρ/2` of the centre. -/
theorem abs_sub_le_of_le_pieceStop (hBc : ∀ ω, Continuous (B · ω)) (hρ : 0 < ρ) (hab : a ≤ b) {ω : Ω}
    (haS : a ≤ S ω) {r : ℝ} (har : (a : ℝ) ≤ r) (hr : r ≤ pieceStop σ ρ B S a b ω) :
    |σ * B r.toNNReal ω - σ * B a ω| ≤ ρ / 2 := by
  rw [pieceStop_eq hBc hρ hab haS] at hr
  exact abs_sub_le_of_le_pieceExit hBc hρ ((Real.le_toNNReal_iff_coe_le (a.coe_nonneg.trans har)).2 har)
    (Real.toNNReal_le_iff_le_coe.2 (hr.trans (NNReal.coe_le_coe.2 (min_le_right _ _))))

namespace IsDriverLogField

variable (hL : IsDriverLogField 𝓕 σ ρ K B S ℓ ℓx ℓxx ℓxxx ℓt)
include hL

/-- **The piece is a log-field region**: up to the piece stop, `ℓ` is a regular log-field around the centre. -/
theorem piece_isLogField (hBc : ∀ ω, Continuous (B · ω)) (hρ : 0 < ρ) (hab : a ≤ b) {ω : Ω} (haS : a ≤ S ω) :
    IsLogField (ℓ ω) (ℓx ω) (ℓxx ω) (ℓxxx ω) (ℓt ω) a (min (b : ℝ) (pieceStop σ ρ B S a b ω)) (σ * B a ω) ρ K :=
  hL.loc ω a _ _ a.coe_nonneg (le_min (NNReal.coe_le_coe.2 hab) (NNReal.coe_le_coe.2 (le_pieceStop ω)))
    ((min_le_right _ _).trans (NNReal.coe_le_coe.2 (pieceStop_le_S hBc hρ hab haS))) fun r hr =>
      (abs_sub_le_of_le_pieceStop hBc hρ hab haS hr.1 (hr.2.trans (min_le_right _ _))).trans_lt (by linarith)

/-- **The generator of the piece field vanishes along the driver**, up to the piece stop. -/
theorem fieldGen_piece_eq_zero (hBc : ∀ ω, Continuous (B · ω)) (hρ : 0 < ρ) (hab : a ≤ b) {ω : Ω}
    (hES : ∀ ω ∈ E, a ≤ S ω) {u : ℝ} (hau : (a : ℝ) ≤ u) (hu : u ≤ pieceStop σ ρ B S a b ω) :
    Ito.fieldGen (pieceF2 σ ρ B S ℓ ℓx ℓxx a E) (pieceFT σ ρ B ℓ ℓt a E) B u ω = 0 := by
  by_cases hω : ω ∈ E
  · have haS := hES ω hω
    have huS : u ≤ S ω := hu.trans (NNReal.coe_le_coe.2 (pieceStop_le_S hBc hρ hab haS))
    have hd := abs_sub_le_of_le_pieceStop hBc hρ hab haS hau hu
    have hd' : |σ * B u.toNNReal ω - σ * B a ω| < ρ := hd.trans_lt (by linarith)
    have e0 := cutChi_zero_eq_one hρ hd'
    have e1 := cutChi_succ_eq_zero hρ hd' (k := 1) one_pos
    have e2 := cutChi_succ_eq_zero hρ hd' (k := 2) two_pos
    have hg := hL.gen ω u (a.coe_nonneg.trans hau) huS
    simp only [Ito.fieldGen, pieceF2, pieceFT, hω, huS, and_self, ↓reduceIte, cutFieldT, cutField2, cutExp2,
      e0, e1, e2]
    have : Real.exp (ℓ ω u (σ * B u.toNNReal ω)) * (ℓt ω u (σ * B u.toNNReal ω) + σ ^ 2 / 2 *
        (ℓxx ω u (σ * B u.toNNReal ω) + ℓx ω u (σ * B u.toNNReal ω) ^ 2)) = 0 := by rw [hg, mul_zero]
    linear_combination this
  · simp [Ito.fieldGen, pieceF2, pieceFT, hω]

/-- **The stopped piece process is the stopped exponential** on `E` (and `0` off `E`): the cut-off is `1` near the
driver and the generator integral vanishes. -/
theorem fieldStopped_piece (hBc : ∀ ω, Continuous (B · ω)) (hρ : 0 < ρ) (hab : a ≤ b) (hES : ∀ ω ∈ E, a ≤ S ω)
    {r : ℝ≥0} (har : a ≤ r) (ω : Ω) :
    Ito.fieldStopped (pieceF σ ρ B ℓ a E) (pieceF2 σ ρ B S ℓ ℓx ℓxx a E) (pieceFT σ ρ B ℓ ℓt a E) B
      (pieceStop σ ρ B S a b) a r ω =
      E.indicator (fun ω => logFieldExp σ B ℓ (min r (pieceStop σ ρ B S a b ω)) ω) ω := by
  set τ := min r (pieceStop σ ρ B S a b ω) with hτ
  have haτ : a ≤ τ := le_min har (le_pieceStop ω)
  have hint : ∫ u in (a : ℝ)..(τ : ℝ), Ito.fieldGen (pieceF2 σ ρ B S ℓ ℓx ℓxx a E) (pieceFT σ ρ B ℓ ℓt a E) B u ω
      = 0 := by
    rw [intervalIntegral.integral_congr (g := fun _ => (0 : ℝ)) fun u hu => ?_, intervalIntegral.integral_zero]
    rw [uIcc_of_le (NNReal.coe_le_coe.2 haτ)] at hu
    exact hL.fieldGen_piece_eq_zero hBc hρ hab hES hu.1
      (hu.2.trans (NNReal.coe_le_coe.2 (min_le_right _ _)))
  simp only [Ito.fieldStopped, ← hτ, hint, sub_zero]
  by_cases hω : ω ∈ E
  · have haS := hES ω hω
    have hd := abs_sub_le_of_le_pieceStop (σ := σ) hBc hρ hab haS (NNReal.coe_le_coe.2 haτ)
      (NNReal.coe_le_coe.2 (min_le_right _ _))
    rw [Real.toNNReal_coe] at hd
    have e0 := cutChi_zero_eq_one hρ (hd.trans_lt (by linarith : ρ / 2 < ρ))
    simp only [pieceF, hω, ↓reduceIte, indicator_of_mem hω, cutField, cutExp0, e0, one_mul, logFieldExp, ← hτ]
  · simp only [pieceF, hω, ↓reduceIte, indicator_of_notMem hω]

end IsDriverLogField

/-- A stopping time `T` (valued in `ℝ≥0`) has adapted sublevel events. -/
theorem measurableSet_le_of_isStoppingTime {T : Ω → ℝ≥0} (hT : IsStoppingTime 𝓕 fun ω => (T ω : WithTop ℝ≥0))
    (r : ℝ≥0) : MeasurableSet[𝓕 r] {ω | T ω ≤ r} := by
  have := hT.measurableSet_le r
  simpa only [WithTop.coe_le_coe] using this

theorem measurableSet_ge_of_isStoppingTime {T : Ω → ℝ≥0} (hT : IsStoppingTime 𝓕 fun ω => (T ω : WithTop ℝ≥0))
    (r : ℝ≥0) : MeasurableSet[𝓕 r] {ω | r ≤ T ω} := by
  have := hT.measurableSet_ge r
  simpa only [WithTop.coe_le_coe] using this

theorem isStoppingTime_pieceStop (hBc : ∀ ω, Continuous (B · ω)) (hBm : ∀ u, Measurable[𝓕 u] (B u))
    (hS : IsStoppingTime 𝓕 fun ω => (S ω : WithTop ℝ≥0)) :
    IsStoppingTime 𝓕 fun ω => (pieceStop σ ρ B S a b ω : WithTop ℝ≥0) := by
  have h := (hS.min (isStoppingTime_pieceExit (σ := σ) (ρ := ρ) (a := a) (b := b) hBc hBm)).max_const a
  have e : (fun ω => max (min (S ω : WithTop ℝ≥0) (pieceExit σ ρ B a b ω)) (a : WithTop ℝ≥0)) =
      fun ω => (pieceStop σ ρ B S a b ω : WithTop ℝ≥0) := funext fun ω => by
    simp only [pieceStop, WithTop.coe_max, WithTop.coe_min, max_comm]
  rwa [e] at h

theorem isStoppingTime_min_pieceExit (hBc : ∀ ω, Continuous (B · ω)) (hBm : ∀ u, Measurable[𝓕 u] (B u))
    (hS : IsStoppingTime 𝓕 fun ω => (S ω : WithTop ℝ≥0)) :
    IsStoppingTime 𝓕 fun ω => (min (S ω) (pieceExit σ ρ B a b ω) : WithTop ℝ≥0) := by
  have h := hS.min (isStoppingTime_pieceExit (σ := σ) (ρ := ρ) (a := a) (b := b) hBc hBm)
  simpa only [WithTop.coe_min] using h

/-! #### The piece fields on and off the event -/

section Cases

variable {r : ℝ} {ω : Ω}

theorem pieceF_of_mem (hω : ω ∈ E) :
    pieceF σ ρ B ℓ a E r ω = fun x => cutField (ℓ ω) (σ * B a ω) ρ r (σ * x) := by
  funext x; simp [pieceF, hω]

theorem pieceF_of_notMem (hω : ω ∉ E) : pieceF σ ρ B ℓ a E r ω = fun _ => 0 := by
  funext x; simp [pieceF, hω]

theorem pieceF1_of_mem (hω : ω ∈ E) (hr : r ≤ S ω) :
    pieceF1 σ ρ B S ℓ ℓx a E r ω = fun x => σ * cutField1 (ℓ ω) (ℓx ω) (σ * B a ω) ρ r (σ * x) := by
  funext x; simp [pieceF1, hω, hr]

theorem pieceF1_of_notMem (hω : ω ∉ E) : pieceF1 σ ρ B S ℓ ℓx a E r ω = fun _ => 0 := by
  funext x; simp [pieceF1, hω]

theorem pieceF2_of_mem (hω : ω ∈ E) (hr : r ≤ S ω) :
    pieceF2 σ ρ B S ℓ ℓx ℓxx a E r ω = fun x => σ ^ 2 * cutField2 (ℓ ω) (ℓx ω) (ℓxx ω) (σ * B a ω) ρ r (σ * x) := by
  funext x; simp [pieceF2, hω, hr]

theorem pieceF2_of_notMem (hω : ω ∉ E) : pieceF2 σ ρ B S ℓ ℓx ℓxx a E r ω = fun _ => 0 := by
  funext x; simp [pieceF2, hω]

theorem pieceFT_of_mem (hω : ω ∈ E) :
    pieceFT σ ρ B ℓ ℓt a E r ω = fun x => cutFieldT (ℓ ω) (ℓt ω) (σ * B a ω) ρ r (σ * x) := by
  funext x; simp [pieceFT, hω]

theorem pieceFT_of_notMem (hω : ω ∉ E) : pieceFT σ ρ B ℓ ℓt a E r ω = fun _ => 0 := by
  funext x; simp [pieceFT, hω]

end Cases

namespace IsDriverLogField

variable (hL : IsDriverLogField 𝓕 σ ρ K B S ℓ ℓx ℓxx ℓxxx ℓt)
include hL

/-- The first space derivative of the piece field along the driver is adapted. -/
theorem measurable_pieceF1 (hBm : ∀ u, Measurable[𝓕 u] (B u))
    (hS : IsStoppingTime 𝓕 fun ω => (S ω : WithTop ℝ≥0)) (hEm : MeasurableSet[𝓕 a] E) {r : ℝ≥0} (har : a ≤ r) :
    Measurable[𝓕 r] fun ω => pieceF1 σ ρ B S ℓ ℓx a E r ω (B r ω) := by
  have hg : Continuous fun p : ℝ × ℝ × ℝ × ℝ => σ * ((cutChi 1 (σ * p.1) ρ (σ * p.2.1) +
      cutChi 0 (σ * p.1) ρ (σ * p.2.1) * p.2.2.2) * Real.exp p.2.2.1) := by
    have hc : Continuous fun p : ℝ × ℝ × ℝ × ℝ => (σ * p.1, σ * p.2.1) := by fun_prop
    have h0 := (continuous_cutChi_uncurry 0 ρ).comp hc
    have h1 := (continuous_cutChi_uncurry 1 ρ).comp hc
    exact continuous_const.mul ((h1.add (h0.mul (by fun_prop))).mul (by fun_prop))
  have hBa : Measurable[𝓕 r] (B a) := (hBm a).mono (𝓕.mono har) le_rfl
  have hgm := hg.measurable.comp (hBa.prodMk ((hBm r).prodMk ((hL.meas0 r).prodMk (hL.meas1 r))))
  have hset : MeasurableSet[𝓕 r] (E ∩ {ω | r ≤ S ω}) :=
    (𝓕.mono har _ hEm).inter (measurableSet_ge_of_isStoppingTime hS r)
  convert hgm.indicator hset using 1
  funext ω
  by_cases h : ω ∈ E ∧ r ≤ S ω
  · have h2 : ω ∈ {ω | r ≤ S ω} := h.2
    rw [indicator_of_mem (show ω ∈ E ∩ {ω | r ≤ S ω} from h), pieceF1_of_mem h.1 (NNReal.coe_le_coe.2 h.2)]
    simp only [Function.comp_apply, indicator_of_mem h2, cutField1, cutExp1]
  · rw [indicator_of_notMem (show ω ∉ E ∩ {ω | r ≤ S ω} from h)]
    by_cases hω : ω ∈ E
    · have hr : ¬ (r : ℝ) ≤ S ω := fun h' => h ⟨hω, NNReal.coe_le_coe.1 h'⟩
      simp [pieceF1, hω, hr]
    · rw [pieceF1_of_notMem hω]

/-- The second space derivative of the piece field along the driver is adapted. -/
theorem measurable_pieceF2 (hBm : ∀ u, Measurable[𝓕 u] (B u))
    (hS : IsStoppingTime 𝓕 fun ω => (S ω : WithTop ℝ≥0)) (hEm : MeasurableSet[𝓕 a] E) {r : ℝ≥0} (har : a ≤ r) :
    Measurable[𝓕 r] fun ω => pieceF2 σ ρ B S ℓ ℓx ℓxx a E r ω (B r ω) := by
  have hg : Continuous fun p : ℝ × ℝ × ℝ × ℝ × ℝ => σ ^ 2 * ((cutChi 2 (σ * p.1) ρ (σ * p.2.1) +
      2 * cutChi 1 (σ * p.1) ρ (σ * p.2.1) * p.2.2.2.1 +
      cutChi 0 (σ * p.1) ρ (σ * p.2.1) * (p.2.2.2.2 + p.2.2.2.1 ^ 2)) * Real.exp p.2.2.1) := by
    have hc : Continuous fun p : ℝ × ℝ × ℝ × ℝ × ℝ => (σ * p.1, σ * p.2.1) := by fun_prop
    have h0 := (continuous_cutChi_uncurry 0 ρ).comp hc
    have h1 := (continuous_cutChi_uncurry 1 ρ).comp hc
    have h2 := (continuous_cutChi_uncurry 2 ρ).comp hc
    exact continuous_const.mul (((h2.add ((continuous_const.mul h1).mul (by fun_prop))).add
      (h0.mul (by fun_prop))).mul (by fun_prop))
  have hBa : Measurable[𝓕 r] (B a) := (hBm a).mono (𝓕.mono har) le_rfl
  have hgm := hg.measurable.comp (hBa.prodMk ((hBm r).prodMk ((hL.meas0 r).prodMk
    ((hL.meas1 r).prodMk (hL.meas2 r)))))
  have hset : MeasurableSet[𝓕 r] (E ∩ {ω | r ≤ S ω}) :=
    (𝓕.mono har _ hEm).inter (measurableSet_ge_of_isStoppingTime hS r)
  convert hgm.indicator hset using 1
  funext ω
  by_cases h : ω ∈ E ∧ r ≤ S ω
  · have h2 : ω ∈ {ω | r ≤ S ω} := h.2
    rw [indicator_of_mem (show ω ∈ E ∩ {ω | r ≤ S ω} from h), pieceF2_of_mem h.1 (NNReal.coe_le_coe.2 h.2)]
    simp only [Function.comp_apply, indicator_of_mem h2, cutField2, cutExp2]
  · rw [indicator_of_notMem (show ω ∉ E ∩ {ω | r ≤ S ω} from h)]
    by_cases hω : ω ∈ E
    · have hr : ¬ (r : ℝ) ≤ S ω := fun h' => h ⟨hω, NNReal.coe_le_coe.1 h'⟩
      simp [pieceF2, hω, hr]
    · rw [pieceF2_of_notMem hω]

/-- The stopped piece process is measurable. -/
theorem measurable_fieldStopped_piece (hBc : ∀ ω, Continuous (B · ω)) (hBm : ∀ u, Measurable[𝓕 u] (B u))
    (hρ : 0 < ρ) (hab : a ≤ b) (hS : IsStoppingTime 𝓕 fun ω => (S ω : WithTop ℝ≥0))
    (hEm : MeasurableSet[𝓕 a] E) (hES : ∀ ω ∈ E, a ≤ S ω) {r : ℝ≥0} (har : a ≤ r) :
    Measurable (Ito.fieldStopped (pieceF σ ρ B ℓ a E) (pieceF2 σ ρ B S ℓ ℓx ℓxx a E) (pieceFT σ ρ B ℓ ℓt a E) B
      (pieceStop σ ρ B S a b) a r) := by
  have heq : Ito.fieldStopped (pieceF σ ρ B ℓ a E) (pieceF2 σ ρ B S ℓ ℓx ℓxx a E) (pieceFT σ ρ B ℓ ℓt a E) B
      (pieceStop σ ρ B S a b) a r =
      E.indicator fun ω => logFieldExp σ B ℓ (min r (min (S ω) (pieceExit σ ρ B a b ω))) ω := by
    funext ω
    rw [hL.fieldStopped_piece hBc hρ hab hES har ω]
    by_cases hω : ω ∈ E
    · rw [indicator_of_mem hω, indicator_of_mem hω, pieceStop_eq hBc hρ hab (hES ω hω)]
    · rw [indicator_of_notMem hω, indicator_of_notMem hω]
  rw [heq]
  exact ((hL.measurable_logFieldExp_stopped hBc hρ (isStoppingTime_min_pieceExit hBc hBm hS)
    (fun ω => min_le_left _ _) r).mono (𝓕.le r) le_rfl).indicator (𝓕.le a _ hEm)

/-- **One piece.** On an `𝓕_a`-event `E ⊆ {a ≤ S}`, the increment of the stopped exponential over `[a, b]`, stopped
also at the exit `pieceExit` of the driver from the `ρ/2`-neighbourhood of `σB_a`, has zero mean against bounded
`𝓕_a`-measurable `ξ` (A5's stopped Itô theorem for the frozen-centre cut-off field). -/
theorem integral_mul_piece_eq_zero {P : Measure Ω} (hB : IsFilteredBrownianReal 𝓕 B P)
    (hBc : ∀ ω, Continuous (B · ω)) (hσ : 0 ≤ σ) (hρ : 0 < ρ)
    (hS : IsStoppingTime 𝓕 fun ω => (S ω : WithTop ℝ≥0)) (hab : a ≤ b) (hEm : MeasurableSet[𝓕 a] E)
    (hES : ∀ ω ∈ E, a ≤ S ω) {ξ : Ω → ℝ} (hξ : Measurable[𝓕 a] ξ) (hξb : ∀ ω, |ξ ω| ≤ 1) :
    ∫ ω, ξ ω * E.indicator (fun ω => logFieldExp σ B ℓ (min b (min (S ω) (pieceExit σ ρ B a b ω))) ω -
      logFieldExp σ B ℓ a ω) ω ∂P = 0 := by
  have hBm : ∀ u, Measurable[𝓕 u] (B u) := fun u => hB.2.1 u
  have hP := hB.isProbabilityMeasure'
  obtain ⟨ω₀⟩ : Nonempty Ω := by
    by_contra h
    rw [not_nonempty_iff] at h
    have := hP.measure_univ
    rw [Set.univ_eq_empty_iff.2 h, measure_empty] at this
    exact zero_ne_one this
  have hK0 : 0 ≤ K := (hL.loc ω₀ 0 0 (σ * B (0 : ℝ).toNNReal ω₀) le_rfl le_rfl (NNReal.coe_nonneg _)
    fun r hr => by rw [show r = 0 from le_antisymm hr.2 hr.1, sub_self, abs_zero]; exact hρ).Knonneg
  obtain ⟨Cχ, hCχ, hχ⟩ := exists_bound_cutChi_uniform ρ
  set B₀ := 8 * Cχ * (1 + K) ^ 3 * Real.exp K with hB₀
  have hB₀0 : 0 ≤ B₀ := by positivity
  set C := (1 + σ) ^ 3 * B₀ with hC
  have hσk : ∀ k ≤ 3, σ ^ k ≤ (1 + σ) ^ 3 := fun k hk =>
    (pow_le_pow_left₀ hσ (by linarith) k).trans (pow_le_pow_right₀ (by linarith) hk)
  have hCk : ∀ k ≤ 3, σ ^ k * B₀ ≤ C := fun k hk => mul_le_mul_of_nonneg_right (hσk k hk) hB₀0
  have hC0 : B₀ ≤ C := by simpa using hCk 0 (by norm_num)
  have hC1 : σ * B₀ ≤ C := by simpa using hCk 1 (by norm_num)
  have hC2 : σ ^ 2 * B₀ ≤ C := hCk 2 (by norm_num)
  have hC3 : σ ^ 3 * B₀ ≤ C := hCk 3 (by norm_num)
  have hC00 : 0 ≤ C := hB₀0.trans hC0
  have hrS : ∀ ω ∈ E, ∀ r ∈ Icc (a : ℝ) (min (b : ℝ) (pieceStop σ ρ B S a b ω)), r ≤ S ω := fun ω hω r hr =>
    hr.2.trans ((min_le_right _ _).trans (NNReal.coe_le_coe.2 (pieceStop_le_S hBc hρ hab (hES ω hω))))
  have sc := fun ω (hω : ω ∈ E) => (hL.piece_isLogField hBc hρ hab (hES ω hω)).scaled hσ hCχ (hχ (σ * B a ω))
  have key := Ito.integral_mul_fieldStopped_sub_eq_zero hB hBc (Φ := pieceF σ ρ B ℓ a E)
    (Φ1 := pieceF1 σ ρ B S ℓ ℓx a E) (Φ2 := pieceF2 σ ρ B S ℓ ℓx ℓxx a E) (Ψ := pieceFT σ ρ B ℓ ℓt a E) (C := C)
    hab (S := pieceStop σ ρ B S a b) (measurableSet_le_of_isStoppingTime (isStoppingTime_pieceStop hBc hBm hS))
    le_pieceStop
    (fun ω r hr x => by
      by_cases hω : ω ∈ E
      · rw [pieceF_of_mem hω, pieceF1_of_mem hω (hrS ω hω r hr)]
        exact (sc ω hω).1 r hr x
      · rw [pieceF_of_notMem hω, pieceF1_of_notMem hω]; exact hasDerivAt_const x 0)
    (fun ω r hr x => by
      by_cases hω : ω ∈ E
      · rw [pieceF1_of_mem hω (hrS ω hω r hr), pieceF2_of_mem hω (hrS ω hω r hr)]
        exact (sc ω hω).2.1 r hr x
      · rw [pieceF1_of_notMem hω, pieceF2_of_notMem hω]; exact hasDerivAt_const x 0)
    (fun ω r hr x y => by
      by_cases hω : ω ∈ E
      · rw [pieceF2_of_mem hω (hrS ω hω r hr)]
        exact ((sc ω hω).2.2.1 r hr x y).trans (mul_le_mul_of_nonneg_right hC3 (abs_nonneg _))
      · rw [pieceF2_of_notMem hω, sub_self, abs_zero]; positivity)
    (fun ω x a₁ a₂ h₁ h₁₂ h₂ => by
      by_cases hω : ω ∈ E
      · rw [pieceF_of_mem hω, pieceF_of_mem hω]
        simp only [pieceFT, hω, ↓reduceIte]
        exact (sc ω hω).2.2.2.1 x a₁ a₂ h₁ h₁₂ h₂
      · simp [pieceF, pieceFT, hω])
    (fun ω => by
      by_cases hω : ω ∈ E
      · simp only [pieceFT, hω, ↓reduceIte]
        exact (sc ω hω).2.2.2.2.1
      · simp only [pieceFT, hω, ↓reduceIte]
        exact continuousOn_const)
    (fun ω => by
      by_cases hω : ω ∈ E
      · exact (sc ω hω).2.2.2.2.2.1.congr fun p hp => by rw [pieceF2_of_mem hω (hrS ω hω p.1 hp.1)]
      · simp only [pieceF2, hω, false_and, ↓reduceIte]
        exact continuousOn_const)
    (fun ω r hr x => by
      by_cases hω : ω ∈ E
      · rw [pieceF_of_mem hω]; exact ((sc ω hω).2.2.2.2.2.2 r hr x).1.trans hC0
      · rw [pieceF_of_notMem hω, abs_zero]; exact hC00)
    (fun ω r hr x => by
      by_cases hω : ω ∈ E
      · rw [pieceF1_of_mem hω (hrS ω hω r hr)]; exact ((sc ω hω).2.2.2.2.2.2 r hr x).2.1.trans hC1
      · rw [pieceF1_of_notMem hω, abs_zero]; exact hC00)
    (fun ω r hr x => by
      by_cases hω : ω ∈ E
      · rw [pieceF2_of_mem hω (hrS ω hω r hr)]; exact ((sc ω hω).2.2.2.2.2.2 r hr x).2.2.1.trans hC2
      · rw [pieceF2_of_notMem hω, abs_zero]; exact hC00)
    (fun ω r hr x => by
      by_cases hω : ω ∈ E
      · rw [pieceFT_of_mem hω]; exact ((sc ω hω).2.2.2.2.2.2 r hr x).2.2.2.trans hC0
      · rw [pieceFT_of_notMem hω, abs_zero]; exact hC00)
    (fun r har _ => hL.measurable_pieceF1 hBm hS hEm har)
    (fun r har _ => hL.measurable_pieceF2 hBm hS hEm har)
    (fun r har _ => hL.measurable_fieldStopped_piece hBc hBm hρ hab hS hEm hES har) hξ hξb
  have hpt : ∀ ω, Ito.fieldStopped (pieceF σ ρ B ℓ a E) (pieceF2 σ ρ B S ℓ ℓx ℓxx a E) (pieceFT σ ρ B ℓ ℓt a E) B
      (pieceStop σ ρ B S a b) a b ω - Ito.fieldStopped (pieceF σ ρ B ℓ a E) (pieceF2 σ ρ B S ℓ ℓx ℓxx a E)
        (pieceFT σ ρ B ℓ ℓt a E) B (pieceStop σ ρ B S a b) a a ω =
      E.indicator (fun ω => logFieldExp σ B ℓ (min b (min (S ω) (pieceExit σ ρ B a b ω))) ω -
        logFieldExp σ B ℓ a ω) ω := fun ω => by
    rw [hL.fieldStopped_piece hBc hρ hab hES hab ω, hL.fieldStopped_piece hBc hρ hab hES le_rfl ω]
    by_cases hω : ω ∈ E
    · simp only [indicator_of_mem hω, pieceStop_eq hBc hρ hab (hES ω hω)]
      rw [min_eq_left (le_min (hES ω hω) (le_pieceExit hBc hρ hab ω))]
    · simp only [indicator_of_notMem hω, sub_zero]
  simpa only [hpt] using key

end IsDriverLogField

end OnePiece

/-! ### The grid of pieces -/

section Grid

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {𝓕 : Filtration ℝ≥0 mΩ} {σ ρ K : ℝ} {B : ℝ≥0 → Ω → ℝ}
  {S : Ω → ℝ≥0} {ℓ ℓx ℓxx ℓxxx ℓt : Ω → ℝ → ℝ → ℝ} {s t : ℝ≥0}

/-- The exit time of the `j`-th piece of the uniform grid of `[s, t]` with `n` pieces. -/
def gridExit (σ ρ : ℝ) (B : ℝ≥0 → Ω → ℝ) (s t : ℝ≥0) (n j : ℕ) (ω : Ω) : ℝ≥0 :=
  pieceExit σ ρ B (Ito.unifGrid s t n j) (Ito.unifGrid s t n (j + 1)) ω

/-- The event that the `j`-th piece starts before `S` and no earlier piece was exited early. -/
def gridGood (σ ρ : ℝ) (B : ℝ≥0 → Ω → ℝ) (S : Ω → ℝ≥0) (s t : ℝ≥0) (n j : ℕ) : Set Ω :=
  {ω | Ito.unifGrid s t n j ≤ S ω ∧ ∀ i < j, Ito.unifGrid s t n (i + 1) ≤ gridExit σ ρ B s t n i ω}

/-- The stopped increment of the `j`-th piece. -/
def gridInc (σ ρ : ℝ) (B : ℝ≥0 → Ω → ℝ) (S : Ω → ℝ≥0) (ℓ : Ω → ℝ → ℝ → ℝ) (s t : ℝ≥0) (n j : ℕ) (ω : Ω) : ℝ :=
  (gridGood σ ρ B S s t n j).indicator (fun ω => logFieldExp σ B ℓ
    (min (Ito.unifGrid s t n (j + 1)) (min (S ω) (gridExit σ ρ B s t n j ω))) ω -
      logFieldExp σ B ℓ (Ito.unifGrid s t n j) ω) ω

theorem gridGood_succ_subset (hst : s ≤ t) (n j : ℕ) :
    gridGood σ ρ B S s t n (j + 1) ⊆ gridGood σ ρ B S s t n j := fun _ hω =>
  ⟨(Ito.unifGrid_le_succ hst n j).trans hω.1, fun i hi => hω.2 i (Nat.lt_succ_of_lt hi)⟩

theorem measurableSet_gridGood (hBc : ∀ ω, Continuous (B · ω)) (hBm : ∀ u, Measurable[𝓕 u] (B u))
    (hS : IsStoppingTime 𝓕 fun ω => (S ω : WithTop ℝ≥0)) (hst : s ≤ t) (n j : ℕ) :
    MeasurableSet[𝓕 (Ito.unifGrid s t n j)] (gridGood σ ρ B S s t n j) := by
  have heq : gridGood σ ρ B S s t n j = {ω | Ito.unifGrid s t n j ≤ S ω} ∩
      ⋂ i : Fin j, {ω | Ito.unifGrid s t n (i + 1) ≤ gridExit σ ρ B s t n i ω} := by
    ext ω
    simp only [gridGood, mem_ofPred_eq, mem_inter_iff, mem_iInter]
    exact ⟨fun h => ⟨h.1, fun i => h.2 i i.2⟩, fun h => ⟨h.1, fun i hi => h.2 ⟨i, hi⟩⟩⟩
  rw [heq]
  refine (measurableSet_ge_of_isStoppingTime hS _).inter (MeasurableSet.iInter fun i => ?_)
  exact 𝓕.mono (Ito.unifGrid_mono hst n (Nat.succ_le_of_lt i.2)) _
    (measurableSet_ge_of_isStoppingTime (isStoppingTime_pieceExit hBc hBm) _)

namespace IsDriverLogField

variable (hL : IsDriverLogField 𝓕 σ ρ K B S ℓ ℓx ℓxx ℓxxx ℓt)
include hL

/-- Before `S`, the exponential is bounded by `e^K`. -/
theorem abs_logFieldExp_le (hρ : 0 < ρ) {ω : Ω} {τ : ℝ≥0} (hτ : τ ≤ S ω) :
    |logFieldExp σ B ℓ τ ω| ≤ Real.exp K := by
  have h := hL.abs_le (σ := σ) hρ ω (r := τ) ⟨τ.coe_nonneg, NNReal.coe_le_coe.2 hτ⟩
  rw [Real.toNNReal_coe] at h
  rw [logFieldExp, abs_of_pos (Real.exp_pos _)]
  exact Real.exp_le_exp.2 (le_of_abs_le h)

omit hL in
/-- **The telescoping invariant** of the grid sums: each partial sum is `M_τ − M_{s∧S}` for some `τ ≤ S`, and it is
`M_{t_k} − M_{s∧S}` on the good event of the `k`-th piece. -/
theorem gridSum_invariant (hst : s ≤ t) (n : ℕ) (ω : Ω) (k : ℕ) :
    (∃ τ : ℝ≥0, τ ≤ S ω ∧ ∑ j ∈ Finset.range k, gridInc σ ρ B S ℓ s t n j ω =
        logFieldExp σ B ℓ τ ω - logFieldExp σ B ℓ (min s (S ω)) ω) ∧
      (ω ∈ gridGood σ ρ B S s t n k → ∑ j ∈ Finset.range k, gridInc σ ρ B S ℓ s t n j ω =
        logFieldExp σ B ℓ (Ito.unifGrid s t n k) ω - logFieldExp σ B ℓ (min s (S ω)) ω) := by
  induction k with
  | zero =>
    refine ⟨⟨min s (S ω), min_le_right _ _, by simp⟩, fun h => ?_⟩
    rw [Finset.sum_range_zero, Ito.unifGrid_zero hst, min_eq_left (by simpa [Ito.unifGrid_zero hst] using h.1),
      sub_self]
  | succ k ih =>
    rw [Finset.sum_range_succ]
    by_cases hω : ω ∈ gridGood σ ρ B S s t n k
    · have hk := ih.2 hω
      have hinc : gridInc σ ρ B S ℓ s t n k ω = logFieldExp σ B ℓ
          (min (Ito.unifGrid s t n (k + 1)) (min (S ω) (gridExit σ ρ B s t n k ω))) ω -
            logFieldExp σ B ℓ (Ito.unifGrid s t n k) ω := by
        rw [gridInc, indicator_of_mem hω]
      rw [hk, hinc]
      refine ⟨⟨_, (min_le_right _ _).trans (min_le_left _ _), by ring⟩, fun h' => ?_⟩
      rw [min_eq_left (le_min h'.1 (h'.2 k (Nat.lt_succ_self k)))]
      ring
    · have hinc : gridInc σ ρ B S ℓ s t n k ω = 0 := by rw [gridInc, indicator_of_notMem hω]
      rw [hinc, add_zero]
      exact ⟨ih.1, fun h' => absurd (gridGood_succ_subset hst n k h') hω⟩

omit hL in
/-- On a path whose pieces are never exited early, the grid sum is the stopped increment. -/
theorem gridSum_eq_of_forall (hst : s ≤ t) {n : ℕ} {ω : Ω}
    (hgood : ∀ i < n, gridExit σ ρ B s t n i ω = Ito.unifGrid s t n (i + 1)) :
    ∀ k ≤ n, ∑ j ∈ Finset.range k, gridInc σ ρ B S ℓ s t n j ω =
      logFieldExp σ B ℓ (min (Ito.unifGrid s t n k) (S ω)) ω - logFieldExp σ B ℓ (min s (S ω)) ω := by
  intro k
  induction k with
  | zero => intro _; simp [Ito.unifGrid_zero hst]
  | succ k ih =>
    intro hk
    rw [Finset.sum_range_succ, ih (Nat.le_of_succ_le hk)]
    have hex := hgood k hk
    by_cases hω : Ito.unifGrid s t n k ≤ S ω
    · have hmem : ω ∈ gridGood σ ρ B S s t n k :=
        ⟨hω, fun i hi => (hgood i (hi.trans hk)).ge⟩
      rw [gridInc, indicator_of_mem hmem, hex, min_eq_left hω]
      have : min (Ito.unifGrid s t n (k + 1)) (min (S ω) (Ito.unifGrid s t n (k + 1))) =
          min (Ito.unifGrid s t n (k + 1)) (S ω) := by
        rw [min_comm (S ω), ← min_assoc, min_self]
      rw [this]
      ring
    · have hnot : ω ∉ gridGood σ ρ B S s t n k := fun h => hω h.1
      push Not at hω
      rw [gridInc, indicator_of_notMem hnot, add_zero, min_eq_right hω.le,
        min_eq_right (hω.le.trans (Ito.unifGrid_le_succ hst n k))]

theorem measurable_gridInc (hBc : ∀ ω, Continuous (B · ω)) (hBm : ∀ u, Measurable[𝓕 u] (B u)) (hρ : 0 < ρ)
    (hS : IsStoppingTime 𝓕 fun ω => (S ω : WithTop ℝ≥0)) (hst : s ≤ t) (n j : ℕ) :
    Measurable (gridInc σ ρ B S ℓ s t n j) := by
  have h1 := (hL.measurable_logFieldExp_stopped hBc hρ (isStoppingTime_min_pieceExit (σ := σ) (ρ := ρ)
    (a := Ito.unifGrid s t n j) (b := Ito.unifGrid s t n (j + 1)) hBc hBm hS) (fun ω => min_le_left _ _)
    (Ito.unifGrid s t n (j + 1))).mono (𝓕.le _) le_rfl
  have h2 := (hL.measurable_logFieldExp_stopped hBc hρ hS (fun ω => le_rfl) (Ito.unifGrid s t n j)).mono
    (𝓕.le _) le_rfl
  have hG := 𝓕.le _ _ (measurableSet_gridGood (σ := σ) (ρ := ρ) hBc hBm hS hst n j)
  convert (h1.sub h2).indicator hG using 1
  funext ω
  by_cases hω : ω ∈ gridGood σ ρ B S s t n j
  · rw [gridInc, indicator_of_mem hω, indicator_of_mem hω, Pi.sub_apply, min_eq_left hω.1]
    rfl
  · rw [gridInc, indicator_of_notMem hω, indicator_of_notMem hω]

/-- **The stopped exponential of a log-field along the driver is a martingale**:
`E[ξ (M_{t∧S} − M_{s∧S})] = 0` for every bounded `𝓕_s`-measurable `ξ`, `M_r = exp ℓ(r, σB_r)` (§A.1.2–A.1.3: the
drift of `M̃` vanishes with the other curve frozen, and `M̃` is bounded on the protected rectangle). -/
theorem integral_mul_logField_stopped_sub_eq_zero {P : Measure Ω} (hB : IsFilteredBrownianReal 𝓕 B P)
    (hBc : ∀ ω, Continuous (B · ω)) (hσ : 0 ≤ σ) (hρ : 0 < ρ)
    (hS : IsStoppingTime 𝓕 fun ω => (S ω : WithTop ℝ≥0)) (hst : s ≤ t) {ξ : Ω → ℝ} (hξ : Measurable[𝓕 s] ξ)
    (hξb : ∀ ω, |ξ ω| ≤ 1) :
    ∫ ω, ξ ω * (logFieldExp σ B ℓ (min t (S ω)) ω - logFieldExp σ B ℓ (min s (S ω)) ω) ∂P = 0 := by
  have hBm : ∀ u, Measurable[𝓕 u] (B u) := fun u => hB.2.1 u
  have hP := hB.isProbabilityMeasure'
  have hξm : Measurable ξ := hξ.mono (𝓕.le s) le_rfl
  set F : ℕ → Ω → ℝ := fun n ω => ξ ω * ∑ j ∈ Finset.range (n + 1), gridInc σ ρ B S ℓ s t (n + 1) j ω with hF
  -- each grid sum has zero mean
  have hzero : ∀ n, ∫ ω, F n ω ∂P = 0 := fun n => by
    have hint : ∀ j ∈ Finset.range (n + 1), Integrable (fun ω => ξ ω * gridInc σ ρ B S ℓ s t (n + 1) j ω) P :=
      fun j _ => by
        refine (integrable_const (2 * Real.exp K)).mono'
          (hξm.mul (hL.measurable_gridInc hBc hBm hρ hS hst (n + 1) j)).aestronglyMeasurable
          (Eventually.of_forall fun ω => ?_)
        rw [Real.norm_eq_abs, abs_mul]
        have hb : |gridInc σ ρ B S ℓ s t (n + 1) j ω| ≤ 2 * Real.exp K := by
          by_cases hω : ω ∈ gridGood σ ρ B S s t (n + 1) j
          · rw [gridInc, indicator_of_mem hω]
            refine (abs_sub _ _).trans ?_
            have h1 := hL.abs_logFieldExp_le hρ (ω := ω)
              ((min_le_right _ _).trans (min_le_left _ _) : min (Ito.unifGrid s t (n + 1) (j + 1))
                (min (S ω) (gridExit σ ρ B s t (n + 1) j ω)) ≤ S ω)
            have h2 := hL.abs_logFieldExp_le hρ (ω := ω) hω.1
            linarith
          · rw [gridInc, indicator_of_notMem hω, abs_zero]; positivity
        calc |ξ ω| * |gridInc σ ρ B S ℓ s t (n + 1) j ω| ≤ 1 * (2 * Real.exp K) :=
              mul_le_mul (hξb ω) hb (abs_nonneg _) zero_le_one
          _ = 2 * Real.exp K := one_mul _
    simp only [hF, Finset.mul_sum]
    rw [integral_finsetSum _ hint]
    refine Finset.sum_eq_zero fun j hj => ?_
    have hj' : j < n + 1 := Finset.mem_range.1 hj
    exact hL.integral_mul_piece_eq_zero hB hBc hσ hρ hS (Ito.unifGrid_le_succ hst (n + 1) j)
      (measurableSet_gridGood hBc hBm hS hst (n + 1) j) (fun ω hω => hω.1)
      (hξ.mono (𝓕.mono (Ito.le_unifGrid hst (n + 1) j)) le_rfl) hξb
  -- the grid sums converge pathwise
  have hlim : ∀ ω, Tendsto (fun n => F n ω) atTop
      (𝓝 (ξ ω * (logFieldExp σ B ℓ (min t (S ω)) ω - logFieldExp σ B ℓ (min s (S ω)) ω))) := fun ω => by
    have hf := continuous_driver (σ := σ) hBc ω
    obtain ⟨δ, hδ, hfδ⟩ := Metric.uniformContinuousOn_iff.1
      (isCompact_Icc.uniformContinuousOn_of_continuous (s := Icc (s : ℝ) t) hf.continuousOn) (ρ / 2)
        (half_pos hρ)
    obtain ⟨N, hN⟩ := exists_nat_gt (((t : ℝ) - s) / δ)
    refine tendsto_const_nhds.congr' (eventually_atTop.2 ⟨N, fun n hn => ?_⟩)
    have hts : (0 : ℝ) ≤ (t : ℝ) - s := sub_nonneg.2 (NNReal.coe_le_coe.2 hst)
    have hn0 : (0 : ℝ) < (n : ℝ) + 1 := by positivity
    have hmesh : ((t : ℝ) - s) / ((n : ℝ) + 1) < δ := by
      rw [div_lt_iff₀ hn0]
      rw [div_lt_iff₀ hδ] at hN
      have : (N : ℝ) ≤ n := by exact_mod_cast hn
      nlinarith
    have hgood : ∀ i < n + 1, gridExit σ ρ B s t (n + 1) i ω = Ito.unifGrid s t (n + 1) (i + 1) := fun i hi =>
      pieceExit_eq_of_forall hBc hρ fun u hu1 hu2 => by
        have hsi := Ito.le_unifGrid hst (n + 1) i
        have hit := Ito.unifGrid_le hst (Nat.succ_pos n) (Nat.succ_le_of_lt hi)
        have hu : (u : ℝ) ∈ Icc (s : ℝ) t :=
          ⟨NNReal.coe_le_coe.2 (hsi.trans hu1), NNReal.coe_le_coe.2 (hu2.trans hit)⟩
        have hg : ((Ito.unifGrid s t (n + 1) i : ℝ≥0) : ℝ) ∈ Icc (s : ℝ) t :=
          ⟨NNReal.coe_le_coe.2 hsi, NNReal.coe_le_coe.2 ((Ito.unifGrid_le_succ hst (n + 1) i).trans hit)⟩
        have hd : dist (u : ℝ) (Ito.unifGrid s t (n + 1) i : ℝ) < δ := by
          rw [Real.dist_eq, abs_of_nonneg (sub_nonneg.2 (NNReal.coe_le_coe.2 hu1))]
          have h1 := Ito.unifGrid_succ_sub hst (n + 1) i
          have h2 : (u : ℝ) ≤ Ito.unifGrid s t (n + 1) (i + 1) := NNReal.coe_le_coe.2 hu2
          push_cast at h1
          linarith
        have := hfδ _ hu _ hg hd
        rwa [Real.dist_eq, Real.toNNReal_coe, Real.toNNReal_coe] at this
    have hsum := gridSum_eq_of_forall (ℓ := ℓ) (S := S) hst hgood (n + 1) le_rfl
    rw [Ito.unifGrid_self hst (Nat.succ_pos n)] at hsum
    simp only [hF, hsum]
  -- dominated convergence
  have hbd : ∀ n, ∀ᵐ ω ∂P, ‖F n ω‖ ≤ 2 * Real.exp K := fun n => Eventually.of_forall fun ω => by
    obtain ⟨⟨τ, hτ, hsum⟩, -⟩ := gridSum_invariant (σ := σ) (ρ := ρ) (B := B) (S := S) (ℓ := ℓ) hst (n + 1) ω
      (n + 1)
    rw [Real.norm_eq_abs, hF, abs_mul, hsum]
    have h1 := hL.abs_logFieldExp_le hρ hτ
    have h2 := hL.abs_logFieldExp_le hρ (ω := ω) (min_le_right s (S ω))
    calc |ξ ω| * |logFieldExp σ B ℓ τ ω - logFieldExp σ B ℓ (min s (S ω)) ω| ≤ 1 * (2 * Real.exp K) :=
          mul_le_mul (hξb ω) ((abs_sub _ _).trans (by linarith)) (abs_nonneg _) zero_le_one
      _ = 2 * Real.exp K := one_mul _
  have hFm : ∀ n, AEStronglyMeasurable (F n) P := fun n =>
    (hξm.mul (Finset.measurable_sum _ fun j _ =>
      hL.measurable_gridInc hBc hBm hρ hS hst (n + 1) j)).aestronglyMeasurable
  have hT := tendsto_integral_of_dominated_convergence (fun _ => 2 * Real.exp K) hFm (integrable_const _) hbd
    (Eventually.of_forall hlim)
  simp only [hzero] at hT
  exact tendsto_nhds_unique hT tendsto_const_nhds

/-- **The stopped exponential of a log-field along the driver is a martingale** (Mathlib form). -/
theorem martingale_logFieldExp_stopped {P : Measure Ω} (hB : IsFilteredBrownianReal 𝓕 B P)
    (hBc : ∀ ω, Continuous (B · ω)) (hσ : 0 ≤ σ) (hρ : 0 < ρ)
    (hS : IsStoppingTime 𝓕 fun ω => (S ω : WithTop ℝ≥0)) :
    Martingale (fun t ω => logFieldExp σ B ℓ (min t (S ω)) ω) 𝓕 P := by
  have hP := hB.isProbabilityMeasure'
  have hMm : ∀ t : ℝ≥0, Measurable[𝓕 t] fun ω => logFieldExp σ B ℓ (min t (S ω)) ω := fun t =>
    hL.measurable_logFieldExp_stopped hBc hρ hS (fun ω => le_rfl) t
  have hMi : ∀ t : ℝ≥0, Integrable (fun ω => logFieldExp σ B ℓ (min t (S ω)) ω) P := fun t =>
    (integrable_const (Real.exp K)).mono' ((hMm t).mono (𝓕.le t) le_rfl).aestronglyMeasurable
      (Eventually.of_forall fun ω => by
        rw [Real.norm_eq_abs]; exact hL.abs_logFieldExp_le hρ (min_le_right _ _))
  refine ⟨fun t => (hMm t).stronglyMeasurable, fun s t hst => ?_⟩
  refine (ae_eq_condExp_of_forall_setIntegral_eq (𝓕.le s) (hMi t)
    (fun A _ _ => (hMi s).integrableOn) (fun A hA _ => ?_)
    ((hMm s).stronglyMeasurable.aestronglyMeasurable)).symm
  have hAm : MeasurableSet A := 𝓕.le s A hA
  set ξ : Ω → ℝ := A.indicator (fun _ => (1 : ℝ)) with hξdef
  have hξm : Measurable[𝓕 s] ξ := measurable_const.indicator hA
  have hξb : ∀ ω, |ξ ω| ≤ 1 := fun ω => by by_cases hω : ω ∈ A <;> simp [hξdef, hω]
  have hξA : ∀ f : Ω → ℝ, ∫ ω, ξ ω * f ω ∂P = ∫ ω in A, f ω ∂P := by
    intro f
    rw [← integral_indicator hAm]
    congr 1
    funext ω
    by_cases hω : ω ∈ A <;> simp [hξdef, hω]
  have h0 := hL.integral_mul_logField_stopped_sub_eq_zero hB hBc hσ hρ hS hst hξm hξb
  have hi : ∀ r, Integrable (fun ω => ξ ω * logFieldExp σ B ℓ (min r (S ω)) ω) P := fun r =>
    (hMi r).bdd_mul (hξm.mono (𝓕.le s) le_rfl).aestronglyMeasurable
      (Eventually.of_forall fun ω => by rw [Real.norm_eq_abs]; exact hξb ω)
  have h1 : ∫ ω, ξ ω * (logFieldExp σ B ℓ (min t (S ω)) ω - logFieldExp σ B ℓ (min s (S ω)) ω) ∂P =
      (∫ ω, ξ ω * logFieldExp σ B ℓ (min t (S ω)) ω ∂P) - ∫ ω, ξ ω * logFieldExp σ B ℓ (min s (S ω)) ω ∂P := by
    rw [← integral_sub (hi t) (hi s)]
    congr 1; funext ω; ring
  rw [h1, hξA, hξA] at h0
  linarith

end IsDriverLogField

end Grid

end InteractingSLE.ZhanGT4
