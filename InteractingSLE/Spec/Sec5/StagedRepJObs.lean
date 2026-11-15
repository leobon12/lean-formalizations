/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec5.StagedRepJWire
import InteractingSLE.Spec.Sec5.StagedNodeStart

/-!
# Prop 5.9's later root stages: arc pieces of a dilated killed arc

Packet PROVE-STAGED-REPJ (towards `GlueObs`). PIECES' tree candidates are pieces of the **dilated** joint-chart image
`λ ψ ∘ α`, while the glued restarted word is a piece of the undilated image. At a sample where the two arcs are related
by the dilation (`ArcScaleAt`: `γ' = c γ`, same pre-contact times, start capacities `S₀' = c² S₀`), the dilated piece is
the Brownian scaling of the undilated one:

* `ArcScaleAt.lt_arcζ`, **`ArcScaleAt.arcW_eq`** (`W'(u) = c W(u / c²)`), **`ArcScaleAt.arcζ_eq`** (`ζ' = c² ζ`);
* **`ArcScaleAt.arcVL_sub_arcW`**, **`ArcScaleAt.arcVR_sub_arcW`**: the relative marks scale the same way (S3's restart
  formula with REP2's local driver and `rightImg_scale`).

R48: nothing here uses Theorem 1.2/1.3 or any `*_of_param`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Filter Set
open scoped NNReal ENNReal

namespace InteractingSLE.Sec5.CrossCond.StagedRepJ

open WangWu WangWu.ImgWord Prop59System Prop59Stage Prop59Pieces StagedRepLater StagedS3 MartChar.RealFlow
open Prop59NodeTree (shiftDrv)
open Sec7.Lemma71C (capClock)
open LQGMetric (DistOn)
open scoped Real
open GlueCond Cond44Ref Word49 StagedS4 StagedS5 StagedS6 StagedKill StagedCand
open Restart Exist.StagedLaw Exist.Staged Sec7.AdmCode Prop513TreeExtract Prop513Schedule Prop513Target
open Sec4 (IsStripGFF IsStripCounterflowDriver)
open LawUnique (HistorySpace)

section Gen

theorem shiftDrv_scD (g : ℝ → ℝ) {c : ℝ} (hc : 0 < c) (S : ℝ) :
    shiftDrv (scD c g) (c ^ 2 * S) = scD c (shiftDrv g S) := by
  funext r
  have hc2 : c ^ 2 ≠ 0 := (pow_pos hc 2).ne'
  simp only [shiftDrv, scD]
  rw [show (c ^ 2 * S + r) / c ^ 2 = S + r / c ^ 2 by field_simp, show c ^ 2 * S / c ^ 2 = S by field_simp]
  ring

theorem rightImg_scD' {g : ℝ → ℝ} (hg : Continuous g) {c : ℝ} (hc : 0 < c) (y : ℝ) {u : ℝ} (hu : 0 ≤ u) :
    rightImg (scD c g) (c * y) u = c * rightImg g y (u / c ^ 2) := by
  have h := rightImg_scale hg hc y (div_nonneg hu (pow_pos hc 2).le)
  rwa [mul_div_cancel₀ u (pow_pos hc 2).ne'] at h

/-- The local driver of a killed arc before a pre-contact capacity, as a continuous driver. -/
theorem exists_continuous_eqOn_kPath {g : ℝ → ℂ} {Q : Set ℝ} (hg : IsKilledArc g Q) {T : ℝ≥0}
    (hT : (T : WithTop ℝ≥0) < kLife g Q) :
    ∃ w : ℝ → ℝ, Continuous w ∧ EqOn (kPath g Q) w (Icc 0 (T : ℝ)) := by
  obtain ⟨S, hS, hlt⟩ := lt_kLife_iff.1 hT
  have hS0 : 0 < S := by
    by_contra hn
    have hS0' : S = 0 := le_antisymm (not_lt.1 hn) (hg.nonneg S hS)
    rw [hS0', hg.capClock_zero] at hlt
    exact absurd hlt (not_lt.2 (NNReal.coe_nonneg _))
  exact ⟨locDrv g S, (hg.locDrv_spec hS hS0).1, kPath_eqOn_locDrv hg hS hS0 hlt⟩

end Gen

section ArcScale

variable {Ω Ω' : Type*} {nL nR : ℕ} {γ : Ω → ℝ → ℂ} {P : Ω → Set ℝ} {S₀ : Ω → ℝ≥0} {A : Set Ω}
  {γ' : Ω' → ℝ → ℂ} {P' : Ω' → Set ℝ} {S₀' : Ω' → ℝ≥0} {A' : Set Ω'} {ω : Ω} {ω' : Ω'} {c : ℝ}

/-- **Two arc data related by the dilation `c` at two samples**: the second image curve is `c` times the first, with
the same pre-contact times, and its start capacity is `c²` times the first's. -/
structure ArcScaleAt (γ : Ω → ℝ → ℂ) (P : Ω → Set ℝ) (S₀ : Ω → ℝ≥0) (A : Set Ω) (γ' : Ω' → ℝ → ℂ)
    (P' : Ω' → Set ℝ) (S₀' : Ω' → ℝ≥0) (A' : Set Ω') (ω : Ω) (ω' : Ω') (c : ℝ) : Prop where
  pos : 0 < c
  arc : IsKilledArc (γ ω) (P ω)
  img : γ' ω' = fun v => (c : ℂ) * γ ω v
  pre : P' ω' = P ω
  start : tf c * S₀' ω' = S₀ ω
  mem : ω' ∈ A' ↔ ω ∈ A

variable (h : ArcScaleAt γ P S₀ A γ' P' S₀' A' ω ω' c)
include h

theorem ArcScaleAt.lt_kLife (u : ℝ≥0) :
    ((S₀' ω' + u : ℝ≥0) : WithTop ℝ≥0) < kLife (γ' ω') (P' ω') ↔
      ((S₀ ω + tf c * u : ℝ≥0) : WithTop ℝ≥0) < kLife (γ ω) (P ω) := by
  rw [h.img, h.pre, lt_kLife_smul_iff h.arc h.pos, mul_add, h.start]

theorem ArcScaleAt.lt_arcζ (u : ℝ≥0) :
    (u : ℝ≥0∞) < arcζ γ' P' S₀' A' ω' ↔ ((tf c * u : ℝ≥0) : ℝ≥0∞) < arcζ γ P S₀ A ω := by
  rw [lt_arcζ_iff, lt_arcζ_iff, h.mem, h.lt_kLife]

/-- **The driver of the dilated piece**: `W'(u) = c W(u / c²)`. -/
theorem ArcScaleAt.arcW_eq (u : ℝ≥0) : arcW γ' P' S₀' A' u ω' = c * arcW γ P S₀ A (tf c * u) ω := by
  by_cases hu : (u : ℝ≥0∞) < arcζ γ' P' S₀' A' ω'
  · have hu' := (h.lt_arcζ u).1 hu
    rw [arcW_of_lt hu, arcW_of_lt hu', h.img, h.pre, kW_smul h.arc h.pos, kW_smul h.arc h.pos, mul_add, h.start]
    ring
  · have hu' : ¬ ((tf c * u : ℝ≥0) : ℝ≥0∞) < arcζ γ P S₀ A ω := fun h' => hu ((h.lt_arcζ u).2 h')
    have e1 : arcW γ' P' S₀' A' u ω' = 0 := by
      classical
      rw [lt_arcζ_iff] at hu
      simp only [Prop59Pieces.arcW, hu, ↓reduceIte]
    have e2 : arcW γ P S₀ A (tf c * u) ω = 0 := by
      classical
      rw [lt_arcζ_iff] at hu'
      simp only [Prop59Pieces.arcW, hu', ↓reduceIte]
    rw [e1, e2, mul_zero]

/-- **The lifetime of the dilated piece**: `ζ' = ζ / c⁻²`. -/
theorem ArcScaleAt.arcζ_eq : arcζ γ' P' S₀' A' ω' = arcζ γ P S₀ A ω / (tf c : ℝ≥0∞) := by
  have key : ∀ t : ℝ≥0, (t : ℝ≥0∞) < arcζ γ' P' S₀' A' ω' ↔ (t : ℝ≥0∞) < arcζ γ P S₀ A ω / (tf c : ℝ≥0∞) :=
    fun t => by rw [ZhanGT4.UpMark.coe_lt_div_iff (tf_ne_zero h.pos)]; exact h.lt_arcζ t
  refine le_antisymm (le_of_forall_lt fun x hx => ?_) (le_of_forall_lt fun x hx => ?_)
  · obtain ⟨t, hxt, htk⟩ := ENNReal.lt_iff_exists_nnreal_btwn.1 hx
    exact lt_trans hxt ((key t).1 htk)
  · obtain ⟨t, hxt, htk⟩ := ENNReal.lt_iff_exists_nnreal_btwn.1 hx
    exact lt_trans hxt ((key t).2 htk)

theorem ArcScaleAt.start_coe : ((S₀' ω' : ℝ≥0) : ℝ) = c ^ 2 * (S₀ ω : ℝ) := by
  have e : ((tf c * S₀' ω' : ℝ≥0) : ℝ) = (S₀ ω : ℝ) := by rw [h.start]
  rw [coe_tf_mul h.pos] at e
  rw [(div_eq_iff (pow_pos h.pos 2).ne').1 e]
  ring

/-- The continuous drivers of the two arcs up to a pre-contact capacity. -/
theorem ArcScaleAt.exists_drivers {u : ℝ≥0} (hu : (u : ℝ≥0∞) < arcζ γ' P' S₀' A' ω') :
    ∃ w : ℝ → ℝ, Continuous w ∧ EqOn (kPath (γ ω) (P ω)) w (Icc 0 ((S₀ ω + tf c * u : ℝ≥0) : ℝ)) ∧
      EqOn (kPath (γ' ω') (P' ω')) (scD c w) (Icc 0 ((S₀' ω' + u : ℝ≥0) : ℝ)) := by
  have hu' := (h.lt_arcζ u).1 hu
  obtain ⟨-, hl⟩ := (lt_arcζ_iff (γ := γ) (P := P) (S₀ := S₀) (A := A)).1 hu'
  obtain ⟨w, hw, hEq⟩ := exists_continuous_eqOn_kPath h.arc hl
  refine ⟨w, hw, hEq, fun v hv => ?_⟩
  have hc2 : 0 < c ^ 2 := pow_pos h.pos 2
  rw [h.img, h.pre, kPath_smul h.arc h.pos]
  simp only [scD]
  have hv' : v / c ^ 2 ∈ Icc 0 ((S₀ ω + tf c * u : ℝ≥0) : ℝ) := by
    refine ⟨div_nonneg hv.1 hc2.le, ?_⟩
    rw [div_le_iff₀ hc2, NNReal.coe_add, coe_tf_mul h.pos]
    have hv2 := hv.2
    rw [NNReal.coe_add, h.start_coe] at hv2
    have e : ((S₀ ω : ℝ) + u / c ^ 2) * c ^ 2 = c ^ 2 * (S₀ ω : ℝ) + u := by
      rw [add_mul, div_mul_cancel₀ (u : ℝ) hc2.ne']; ring
    linarith
  rw [hEq hv']

/-- **The relative left marks of the dilated piece**: `(V'_L − W')(u) = c (V_L − W)(u / c²)`. -/
theorem ArcScaleAt.arcVL_sub_arcW {xL : Ω → Fin nL → ℝ} {xL' : Ω' → Fin nL → ℝ}
    (hx : xL' ω' = fun i => c * xL ω i) {u : ℝ≥0} (hu : (u : ℝ≥0∞) < arcζ γ' P' S₀' A' ω') (i : Fin nL) :
    arcVL γ' P' S₀' A' xL' i u ω' - arcW γ' P' S₀' A' u ω' =
      c * (arcVL γ P S₀ A xL i (tf c * u) ω - arcW γ P S₀ A (tf c * u) ω) := by
  have hu' := (h.lt_arcζ u).1 hu
  obtain ⟨hA', hl'⟩ := (lt_arcζ_iff (γ := γ') (P := P') (S₀ := S₀') (A := A')).1 hu
  obtain ⟨hA, hl⟩ := (lt_arcζ_iff (γ := γ) (P := P) (S₀ := S₀) (A := A)).1 hu'
  obtain ⟨w, hw, hEq, hEq'⟩ := h.exists_drivers hu
  have hxi : xL' ω' i = c * xL ω i := by rw [hx]
  rw [StagedS3.arcVL_sub_arcW (γ := γ) (P := P) (S₀ := S₀) (xL := xL) hA hl hw hEq i,
    StagedS3.arcVL_sub_arcW (γ := γ') (P := P') (S₀ := S₀') (xL := xL') hA' hl' (continuous_scD hw c) hEq' i, hxi,
    h.start_coe]
  have hneg : (fun s => -scD c w s) = scD c (fun s => -w s) := by funext s; simp only [scD]; ring
  rw [hneg, shiftDrv_scD _ h.pos, shiftDrv_scD _ h.pos, show -(c * xL ω i) = c * -xL ω i by ring,
    rightImg_scD' (g := shiftDrv (fun s => -w s) (S₀ ω)) (Prop59NodeTree.continuous_shiftDrv hw.neg _) h.pos
      (-xL ω i) u.coe_nonneg, coe_tf_mul h.pos]
  simp only [scD]
  ring

/-- **The relative right marks of the dilated piece.** -/
theorem ArcScaleAt.arcVR_sub_arcW {xR : Ω → Fin nR → ℝ} {xR' : Ω' → Fin nR → ℝ}
    (hx : xR' ω' = fun k => c * xR ω k) {u : ℝ≥0} (hu : (u : ℝ≥0∞) < arcζ γ' P' S₀' A' ω') (k : Fin nR) :
    arcVR γ' P' S₀' A' xR' k u ω' - arcW γ' P' S₀' A' u ω' =
      c * (arcVR γ P S₀ A xR k (tf c * u) ω - arcW γ P S₀ A (tf c * u) ω) := by
  have hu' := (h.lt_arcζ u).1 hu
  obtain ⟨hA', hl'⟩ := (lt_arcζ_iff (γ := γ') (P := P') (S₀ := S₀') (A := A')).1 hu
  obtain ⟨hA, hl⟩ := (lt_arcζ_iff (γ := γ) (P := P) (S₀ := S₀) (A := A)).1 hu'
  obtain ⟨w, hw, hEq, hEq'⟩ := h.exists_drivers hu
  have hxk : xR' ω' k = c * xR ω k := by rw [hx]
  rw [StagedS3.arcVR_sub_arcW (γ := γ) (P := P) (S₀ := S₀) (xR := xR) hA hl hw hEq k,
    StagedS3.arcVR_sub_arcW (γ := γ') (P := P') (S₀ := S₀') (xR := xR') hA' hl' (continuous_scD hw c) hEq' k, hxk,
    h.start_coe, shiftDrv_scD _ h.pos,
    rightImg_scD' (Prop59NodeTree.continuous_shiftDrv hw _) h.pos _ u.coe_nonneg, coe_tf_mul h.pos]
  simp only [scD]
  ring

end ArcScale

/-! ### `Gam`'s candidate read on the glued space -/

section Ident

variable (x₀ : ℝ) (h44 : Theorem12ParamCond44Statement.{0}) {κ a b a' b' : ℝ} (hκ : 0 < κ) (hκ4 : κ < 4)
  (hb : IsFig51Bounds κ a b a' b') {Ω : Type} [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω]
  (P : Measure Ω) [IsProbabilityMeasure P] (h : Ω → DistOn upperHalfPlaneOpens) (W : ℝ≥0 → Ω → ℝ)
  (ζ : Ω → ℝ≥0∞)

omit mΩ [StandardBorelSpace Ω] [IsProbabilityMeasure P] in
/-- The staged path of the glued space is PIECES' candidate path of `qField`. -/
theorem seedLine_candW (ℓ : ℕ) (t : Fin ℓ → ℝ≥0) (ω : Ω) :
    seedLine (fun _ => ⊤) (candW x₀ h44 hκ hκ4 hb h ℓ t) ω =
      qPath h44 hκ hκ4 (sourceWord (x₀ := x₀) hκ hb) (qField x₀ κ h) ℓ t ω := by
  have hk : (fun r => killedProc (fun _ : Ω => (⊤ : ℝ≥0∞)) (candW x₀ h44 hκ hκ4 hb h ℓ t) r ω) =
      fun r => candW x₀ h44 hκ hκ4 hb h ℓ t r ω := funext (killedProc_of_eq_top rfl)
  funext u
  simp only [seedLine, hk]
  rfl

omit [StandardBorelSpace Ω] in
theorem gamData_img_eq {hhm : Measurable h} {ℓ : ℕ} {t : Fin ℓ → ℝ≥0} (hv : IsValid ℓ t) {s : ℝ≥0}
    {p : Ω × HistorySpace 0 0} (hpE : p ∈ candEg x₀ h44 hκ hκ4 hb P h W ζ hhm ℓ t s)
    (hZ : gZ x₀ (κ := κ) h p ∈ gamGood h44 hκ hκ4 (x₀ := x₀) hb) :
    (gamData h44 hκ hκ4 (x₀ := x₀) hb s).img ℓ t (gZ x₀ (κ := κ) h p) =
      fun u => (rootLam s p.2 : ℂ) * gCurve s (fun _ => ⊤) (candW x₀ h44 hκ hκ4 hb h ℓ t)
        (candEg x₀ h44 hκ hκ4 hb P h W ζ hhm ℓ t s) p u := by
  rw [TreeData.img, tImg_of_mem (show gZ x₀ (κ := κ) h p ∈ (gamData h44 hκ hκ4 (x₀ := x₀) hb s).Gc ℓ t from ⟨hv, hZ⟩),
    gCurve_of_mem hpE, seedLine_candW, qPath_eq_fst hκ hκ4 h44 _ (qField x₀ κ h) ℓ t p.1 p.2]
  rfl

omit [StandardBorelSpace Ω] in
theorem gamData_pre_eq {hhm : Measurable h} {ℓ : ℕ} {t : Fin ℓ → ℝ≥0} (hv : IsValid ℓ t) {s : ℝ≥0}
    {p : Ω × HistorySpace 0 0} (hpE : p ∈ candEg x₀ h44 hκ hκ4 hb P h W ζ hhm ℓ t s)
    (hZ : gZ x₀ (κ := κ) h p ∈ gamGood h44 hκ hκ4 (x₀ := x₀) hb) :
    (gamData h44 hκ hκ4 (x₀ := x₀) hb s).pre ℓ t (gZ x₀ (κ := κ) h p) =
      gPre s (fun _ => ⊤) (candW x₀ h44 hκ hκ4 hb h ℓ t) (candEg x₀ h44 hκ hκ4 hb P h W ζ hhm ℓ t s) p := by
  rw [TreeData.pre, tPre_of_mem (show gZ x₀ (κ := κ) h p ∈ (gamData h44 hκ hκ4 (x₀ := x₀) hb s).Gc ℓ t from ⟨hv, hZ⟩),
    gPre_of_mem hpE, seedLine_candW, qPath_eq_fst hκ hκ4 h44 _ (qField x₀ κ h) ℓ t p.1 p.2]
  rfl

omit [StandardBorelSpace Ω] in
theorem mem_gamData_alive_iff {hhm : Measurable h} {ℓ : ℕ} {t : Fin ℓ → ℝ≥0} (hv : IsValid ℓ t) {s : ℝ≥0}
    {p : Ω × HistorySpace 0 0} (hpE : p ∈ candEg x₀ h44 hκ hκ4 hb P h W ζ hhm ℓ t s)
    (hZ : gZ x₀ (κ := κ) h p ∈ gamGood h44 hκ hκ4 (x₀ := x₀) hb) :
    gZ x₀ (κ := κ) h p ∈ (gamData h44 hκ hκ4 (x₀ := x₀) hb s).alive ℓ t ↔
      p ∈ gA x₀ h44 hκ hκ4 hb P h W ζ hhm ℓ t s := by
  simp only [TreeData.alive, mem_ofPred_eq, gamData_pre_eq x₀ h44 hκ hκ4 hb P h W ζ hv hpE hZ, s3Alive,
    lastO_eq hv]
  exact ⟨fun h' => ⟨hpE, h'.2⟩, fun h' => ⟨⟨hv, hZ⟩, h'.2⟩⟩

omit [StandardBorelSpace Ω] in
/-- **`Gam`'s stage-`ℓ` arc is the `rootLam`-dilation of the glued restarted arc** at a good alive sample. -/
theorem arcScaleAt_gam {hhm : Measurable h} {ℓ : ℕ} {t : Fin ℓ → ℝ≥0} (hv : IsValid ℓ t) {s : ℝ≥0}
    {p : Ω × HistorySpace 0 0} (hpA : p ∈ gA x₀ h44 hκ hκ4 hb P h W ζ hhm ℓ t s)
    (hZ : gZ x₀ (κ := κ) h p ∈ gamGood h44 hκ hκ4 (x₀ := x₀) hb) :
    ArcScaleAt (gCurve s (fun _ => ⊤) (candW x₀ h44 hκ hκ4 hb h ℓ t) (candEg x₀ h44 hκ hκ4 hb P h W ζ hhm ℓ t s))
      (gPre s (fun _ => ⊤) (candW x₀ h44 hκ hκ4 hb h ℓ t) (candEg x₀ h44 hκ hκ4 hb P h W ζ hhm ℓ t s))
      (s3Start s (candW x₀ h44 hκ hκ4 hb h ℓ t) (candEg x₀ h44 hκ hκ4 hb P h W ζ hhm ℓ t s) (lastO ℓ t : ℝ)) univ
      ((gamData h44 hκ hκ4 (x₀ := x₀) hb s).img ℓ t) ((gamData h44 hκ hκ4 (x₀ := x₀) hb s).pre ℓ t)
      ((gamData h44 hκ hκ4 (x₀ := x₀) hb s).startCap ℓ t) ((gamData h44 hκ hκ4 (x₀ := x₀) hb s).alive ℓ t) p
      (gZ x₀ (κ := κ) h p) (rootLam s p.2) := by
  classical
  have hEg := candEg_good x₀ h44 hκ hκ4 hb P h W ζ hhm ℓ t s
  have hγ := isKilledArc_gCurve hEg p
  have hpE := hpA.1
  have hlam := rootLam_pos s p.2
  have hal := (mem_gamData_alive_iff x₀ h44 hκ hκ4 hb P h W ζ hv hpE hZ).2 hpA
  refine ⟨hlam, hγ, gamData_img_eq x₀ h44 hκ hκ4 hb P h W ζ hv hpE hZ,
    gamData_pre_eq x₀ h44 hκ hκ4 hb P h W ζ hv hpE hZ, ?_, ⟨fun _ => mem_univ _, fun _ => hal⟩⟩
  have hq : qLast ℓ t ∈ gPre s (fun _ => ⊤) (candW x₀ h44 hκ hκ4 hb h ℓ t)
      (candEg x₀ h44 hκ hκ4 hb P h W ζ hhm ℓ t s) p := by
    rw [← lastO_eq hv]; exact hpA.2
  have hcap := capClock_smul hγ hlam hq
  simp only [TreeData.startCap, hal, ↓reduceIte, gamData_img_eq x₀ h44 hκ hκ4 hb P h W ζ hv hpE hZ, s3Start, hpA,
    ← lastO_eq hv]
  rw [lastO_eq hv, hcap, tf, ← Real.toNNReal_mul (by positivity), ← mul_assoc, inv_pow,
    inv_mul_cancel₀ (pow_pos hlam 2).ne', one_mul]

/-- **The marks identity of a later stage** (named statement): almost surely on the alive event and `gZ⁻¹ gamR`,
the tree marks of `Gam`'s candidate `(ℓ, t)` are the `rootLam`-dilated initial marks of the glued restarted word in
tree order. -/
def GlueMarks (hhm : Measurable h) (ℓ : ℕ) (t : Fin ℓ → ℝ≥0) (s : ℝ≥0) : Prop :=
  ∀ᵐ p ∂(gMu x₀ (κ := κ) P h W ζ hhm), p ∈ gA x₀ h44 hκ hκ4 hb P h W ζ hhm ℓ t s →
    gZ x₀ (κ := κ) h p ∈ gamR h44 hκ hκ4 (x₀ := x₀) hb s ℓ t →
    (gamData h44 hκ hκ4 (x₀ := x₀) hb s).marks ℓ t (gZ x₀ (κ := κ) h p) =
      (fun i => rootLam s p.2 * gVL x₀ h44 hκ hκ4 hb P h W ζ hhm ℓ t s i 0 p,
        fun k => rootLam s p.2 * gVR x₀ h44 hκ hκ4 hb P h W ζ hhm ℓ t s k 0 p)

omit mΩ [StandardBorelSpace Ω] [IsProbabilityMeasure P] in
/-- The canonical marks of a tree family are its tree marks. -/
theorem canonY_cand_snd {Ω' : Type*} {nL₀ nR₀ : ℕ} (D : TreeData Ω' nL₀ nR₀) (j : ℕ) (t : Fin (j + 1) → ℝ≥0)
    (ω : Ω') : (canonY D.cand (treeY0 D) (j + 1) t ω).2 = D.marks (j + 1) t ω := by
  rw [StagedNode.TreeData.marks_succ]
  rfl

omit [StandardBorelSpace Ω] in
include hκ4 in
/-- **`GlueObs` from the marks identity** (and the good set of `Gam` almost surely on the glued space). -/
theorem glueObs_of_marks {hhm : Measurable h} {j : ℕ} {t : Fin (j + 1) → ℝ≥0} (hv : IsValid (j + 1) t) {s : ℝ≥0}
    (hgam : ∀ᵐ p ∂(gMu x₀ (κ := κ) P h W ζ hhm), gZ x₀ (κ := κ) h p ∈ gamGood h44 hκ hκ4 (x₀ := x₀) hb)
    (hm : GlueMarks x₀ h44 hκ hκ4 hb P h W ζ hhm (j + 1) t s) :
    GlueObs x₀ h44 hκ hκ4 hb P h W ζ hhm (j + 1) t s := by
  have hEg := candEg_good x₀ h44 hκ hκ4 hb P h W ζ hhm (j + 1) t s
  filter_upwards [hm, hgam] with p hmk hZ hpA hR
  have hsc := arcScaleAt_gam x₀ h44 hκ hκ4 hb P h W ζ hv hpA hZ
  have hmarks := hmk hpA hR
  have hlam := rootLam_pos s p.2
  have hsq : (√(gC s p : ℝ))⁻¹ = rootLam s p.2 := sqrt_tf_inv hlam
  refine ⟨?_, ?_⟩
  · rw [canonY_cand_snd, hmarks]
    simp only [dilV, hsq]
  · -- the killed samples
    have hxL : ((gamData h44 hκ hκ4 (x₀ := x₀) hb s).marks (j + 1) t (gZ x₀ (κ := κ) h p)).1 =
        fun i => rootLam s p.2 * s3XL (flowLineXL (sourceWord (x₀ := x₀) hκ hb).fn
          (sourceWord (x₀ := x₀) hκ hb).jumps 0) (candTs (j + 1) t) (j + 1) s (candW x₀ h44 hκ hκ4 hb h (j + 1) t)
          (candEg x₀ h44 hκ hκ4 hb P h W ζ hhm (j + 1) t s) (lastO (j + 1) t : ℝ) p (treeIdx (j + 1) _ i) := by
      rw [hmarks]
      funext i
      simp only [gVL, s6VL_zero hEg (candTs_bounds hv) p i]
    have hxR : ((gamData h44 hκ hκ4 (x₀ := x₀) hb s).marks (j + 1) t (gZ x₀ (κ := κ) h p)).2 =
        fun k => rootLam s p.2 * s3XR (flowLineXR (sourceWord (x₀ := x₀) hκ hb).fn
          (sourceWord (x₀ := x₀) hκ hb).jumps 0) (candTs (j + 1) t) (j + 1) s (candW x₀ h44 hκ hκ4 hb h (j + 1) t)
          (candEg x₀ h44 hκ hκ4 hb P h W ζ hhm (j + 1) t s) (lastO (j + 1) t : ℝ) p (treeIdx (j + 1) _ k) := by
      rw [hmarks]
      funext k
      simp only [gVR, s6VR_zero hEg (candTs_bounds hv) p k]
    have hζ := hsc.arcζ_eq
    show samp _ _ _ ((gamCand h44 hκ hκ4 (x₀ := x₀) hb s (j + 1) t).ζ (gZ x₀ (κ := κ) h p)) = _
    have hζ' : (gamCand h44 hκ hκ4 (x₀ := x₀) hb s (j + 1) t).ζ (gZ x₀ (κ := κ) h p) =
        gζ x₀ h44 hκ hκ4 hb P h W ζ hhm (j + 1) t s p / (gC s p : ℝ≥0∞) := hζ
    rw [hζ']
    refine StagedKCand.samp_congr fun u hu => ?_
    have hu' : (u : ℝ≥0∞) < arcζ ((gamData h44 hκ hκ4 (x₀ := x₀) hb s).img (j + 1) t)
        ((gamData h44 hκ hκ4 (x₀ := x₀) hb s).pre (j + 1) t) ((gamData h44 hκ hκ4 (x₀ := x₀) hb s).startCap (j + 1) t)
        ((gamData h44 hκ hκ4 (x₀ := x₀) hb s).alive (j + 1) t) (gZ x₀ (κ := κ) h p) := by rw [hζ]; exact hu
    have hW := hsc.arcW_eq u
    refine ⟨?_, fun i => ?_, fun k => ?_⟩
    · show arcW _ _ _ _ u _ = _
      rw [hW, hsq]
      rfl
    · have e := hsc.arcVL_sub_arcW (xL := fun p i => s3XL (flowLineXL (sourceWord (x₀ := x₀) hκ hb).fn
          (sourceWord (x₀ := x₀) hκ hb).jumps 0) (candTs (j + 1) t) (j + 1) s (candW x₀ h44 hκ hκ4 hb h (j + 1) t)
          (candEg x₀ h44 hκ hκ4 hb P h W ζ hhm (j + 1) t s) (lastO (j + 1) t : ℝ) p (treeIdx (j + 1) _ i))
        (xL' := fun ω => ((gamData h44 hκ hκ4 (x₀ := x₀) hb s).marks (j + 1) t ω).1) hxL hu' i
      rw [hsq]
      have e2 : arcVL ((gamData h44 hκ hκ4 (x₀ := x₀) hb s).img (j + 1) t)
          ((gamData h44 hκ hκ4 (x₀ := x₀) hb s).pre (j + 1) t)
          ((gamData h44 hκ hκ4 (x₀ := x₀) hb s).startCap (j + 1) t)
          ((gamData h44 hκ hκ4 (x₀ := x₀) hb s).alive (j + 1) t)
          (fun ω => ((gamData h44 hκ hκ4 (x₀ := x₀) hb s).marks (j + 1) t ω).1) i u (gZ x₀ (κ := κ) h p) =
          rootLam s p.2 * gVL x₀ h44 hκ hκ4 hb P h W ζ hhm (j + 1) t s i (gC s p * u) p := by
        have := e
        rw [hW] at this
        have e3 : gVL x₀ h44 hκ hκ4 hb P h W ζ hhm (j + 1) t s i (gC s p * u) p =
            arcVL (gCurve s (fun _ => ⊤) (candW x₀ h44 hκ hκ4 hb h (j + 1) t)
              (candEg x₀ h44 hκ hκ4 hb P h W ζ hhm (j + 1) t s))
              (gPre s (fun _ => ⊤) (candW x₀ h44 hκ hκ4 hb h (j + 1) t)
                (candEg x₀ h44 hκ hκ4 hb P h W ζ hhm (j + 1) t s))
              (s3Start s (candW x₀ h44 hκ hκ4 hb h (j + 1) t) (candEg x₀ h44 hκ hκ4 hb P h W ζ hhm (j + 1) t s)
                (lastO (j + 1) t : ℝ)) univ
              (fun p i => s3XL (flowLineXL (sourceWord (x₀ := x₀) hκ hb).fn (sourceWord (x₀ := x₀) hκ hb).jumps 0)
                (candTs (j + 1) t) (j + 1) s (candW x₀ h44 hκ hκ4 hb h (j + 1) t)
                (candEg x₀ h44 hκ hκ4 hb P h W ζ hhm (j + 1) t s) (lastO (j + 1) t : ℝ) p (treeIdx (j + 1) _ i))
              i (tf (rootLam s p.2) * u) p := rfl
        rw [e3]
        linear_combination this
      exact e2
    · have e := hsc.arcVR_sub_arcW (xR := fun p k => s3XR (flowLineXR (sourceWord (x₀ := x₀) hκ hb).fn
          (sourceWord (x₀ := x₀) hκ hb).jumps 0) (candTs (j + 1) t) (j + 1) s (candW x₀ h44 hκ hκ4 hb h (j + 1) t)
          (candEg x₀ h44 hκ hκ4 hb P h W ζ hhm (j + 1) t s) (lastO (j + 1) t : ℝ) p (treeIdx (j + 1) _ k))
        (xR' := fun ω => ((gamData h44 hκ hκ4 (x₀ := x₀) hb s).marks (j + 1) t ω).2) hxR hu' k
      rw [hsq]
      have e2 : arcVR ((gamData h44 hκ hκ4 (x₀ := x₀) hb s).img (j + 1) t)
          ((gamData h44 hκ hκ4 (x₀ := x₀) hb s).pre (j + 1) t)
          ((gamData h44 hκ hκ4 (x₀ := x₀) hb s).startCap (j + 1) t)
          ((gamData h44 hκ hκ4 (x₀ := x₀) hb s).alive (j + 1) t)
          (fun ω => ((gamData h44 hκ hκ4 (x₀ := x₀) hb s).marks (j + 1) t ω).2) k u (gZ x₀ (κ := κ) h p) =
          rootLam s p.2 * gVR x₀ h44 hκ hκ4 hb P h W ζ hhm (j + 1) t s k (gC s p * u) p := by
        have := e
        rw [hW] at this
        have e3 : gVR x₀ h44 hκ hκ4 hb P h W ζ hhm (j + 1) t s k (gC s p * u) p =
            arcVR (gCurve s (fun _ => ⊤) (candW x₀ h44 hκ hκ4 hb h (j + 1) t)
              (candEg x₀ h44 hκ hκ4 hb P h W ζ hhm (j + 1) t s))
              (gPre s (fun _ => ⊤) (candW x₀ h44 hκ hκ4 hb h (j + 1) t)
                (candEg x₀ h44 hκ hκ4 hb P h W ζ hhm (j + 1) t s))
              (s3Start s (candW x₀ h44 hκ hκ4 hb h (j + 1) t) (candEg x₀ h44 hκ hκ4 hb P h W ζ hhm (j + 1) t s)
                (lastO (j + 1) t : ℝ)) univ
              (fun p k => s3XR (flowLineXR (sourceWord (x₀ := x₀) hκ hb).fn (sourceWord (x₀ := x₀) hκ hb).jumps 0)
                (candTs (j + 1) t) (j + 1) s (candW x₀ h44 hκ hκ4 hb h (j + 1) t)
                (candEg x₀ h44 hκ hκ4 hb P h W ζ hhm (j + 1) t s) (lastO (j + 1) t : ℝ) p (treeIdx (j + 1) _ k))
              k (tf (rootLam s p.2) * u) p := rfl
        rw [e3]
        linear_combination this
      exact e2

end Ident

end InteractingSLE.Sec5.CrossCond.StagedRepJ
