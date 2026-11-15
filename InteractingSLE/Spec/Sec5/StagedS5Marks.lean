/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec5.StagedS5Chart
import InteractingSLE.Spec.Sec5.StagedS4Meas

/-!
# Measurability of the restarted word: initial marks, processes and chart

Packet PROVE-STAGED-S5 ((M3) of `planning/handoffs/PROVE-STAGED-S3.md` §5.2, ambient part). The initial marks of the
restarted word are the image stage marks at the restart capacity `T = S₀`. Through PROVE-PROP59-PIECES' arc pieces of
the same killed arc they are measurable:

* a **born mark** of the switch at capacity `a ≤ T` is `chartAL (shiftDrive W a) (T − a)`, the arc piece started at
  `a` with initial mark `0`, read at `T − a` relative to its driver (`bornArcL_eq`; PROVE-STAGED-S3's
  `arcVL_sub_arcW` and `chartAL_shift` at `a = S`);
* a **root mark** is `−rightImg(−W)(−x)(T) − W(T)`, the arc piece started at `0` with initial mark `x`
  (`rootArcL_eq`);

so the stage marks are `stageArcL`/`stageArcR` (`stageArcL_eq`), measurable for any measurable family of killed arcs
(`measurable_stageArcL`). On the glued space this gives the measurability of PROVE-STAGED-S3's initial marks
`s3XL`/`s3XR` (`measurable_s3XL`), of the restarted processes for the constant filtration
(`adaptedBefore_s3W_const`, …) and of the restarted chart (`isMeasChart_s3Chart`).

Conditional helpers with distinct names; R48: nothing here uses Theorem 1.2/1.3.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology Metric
open scoped NNReal ENNReal
open QuantumZipper (H fwdHull)

namespace InteractingSLE.Sec5.CrossCond.StagedS5

open WangWu WangWu.ImgWord Coupling StagedS3 StagedFinal Word49 LawUnique
open MartChar.RealFlow (rightImg rightImg_zero)
open Prop59Pieces (arcW arcVL arcVR arcζ IsKilledFamily)
open Prop59NodeTree (shiftDrv)
open QuantumZipper.RS (shiftDrive)
open Sec7.Lemma71C (capClock)

/-! ### Stage marks through arc pieces -/

section Arc

variable {X : Type*} {γ : X → ℝ → ℂ} {P : X → Set ℝ}

/-- The left born mark of a switch at capacity `Sb`, read at the capacity `T` (relative to the driver). -/
def bornArcL (γ : X → ℝ → ℂ) (P : X → Set ℝ) (Sb T : X → ℝ≥0) (x : X) : ℝ :=
  arcVL γ P Sb univ (fun _ _ => (0 : ℝ)) (0 : Fin 1) (T x - Sb x) x - arcW γ P Sb univ (T x - Sb x) x

/-- The right born mark of a switch at capacity `Sb`, read at the capacity `T`. -/
def bornArcR (γ : X → ℝ → ℂ) (P : X → Set ℝ) (Sb T : X → ℝ≥0) (x : X) : ℝ :=
  arcVR γ P Sb univ (fun _ _ => (0 : ℝ)) (0 : Fin 1) (T x - Sb x) x - arcW γ P Sb univ (T x - Sb x) x

/-- The left root marks with initial positions `X0`, read at the capacity `T`. -/
def rootArcL {n : ℕ} (γ : X → ℝ → ℂ) (P : X → Set ℝ) (X0 : X → Fin n → ℝ) (T : X → ℝ≥0) (k : Fin n) (x : X) : ℝ :=
  arcVL γ P (fun _ => 0) univ X0 k (T x) x - arcW γ P (fun _ => 0) univ (T x) x

/-- The right root marks with initial positions `X0`, read at the capacity `T`. -/
def rootArcR {n : ℕ} (γ : X → ℝ → ℂ) (P : X → Set ℝ) (X0 : X → Fin n → ℝ) (T : X → ℝ≥0) (k : Fin n) (x : X) : ℝ :=
  arcVR γ P (fun _ => 0) univ X0 k (T x) x - arcW γ P (fun _ => 0) univ (T x) x

/-- The left stage marks (born marks first, oldest first). -/
def stageArcL {n : ℕ} (γ : X → ℝ → ℂ) (P : X → Set ℝ) (Sb : ℕ → X → ℝ≥0) (T : X → ℝ≥0) (X0 : X → Fin n → ℝ)
    (ℓ : ℕ) (x : X) : Fin (ℓ + n) → ℝ :=
  Fin.append (fun j : Fin ℓ => bornArcL γ P (Sb (j + 1)) T x) (fun k => rootArcL γ P X0 T k x)

/-- The right stage marks. -/
def stageArcR {n : ℕ} (γ : X → ℝ → ℂ) (P : X → Set ℝ) (Sb : ℕ → X → ℝ≥0) (T : X → ℝ≥0) (X0 : X → Fin n → ℝ)
    (ℓ : ℕ) (x : X) : Fin (ℓ + n) → ℝ :=
  Fin.append (fun j : Fin ℓ => bornArcR γ P (Sb (j + 1)) T x) (fun k => rootArcR γ P X0 T k x)

variable {Sb T : X → ℝ≥0} {x : X} {w : ℝ → ℝ}

theorem chartAL_shiftDrive_zero (hw : Continuous w) (a : ℝ) : chartAL (shiftDrive w a) 0 = 0 := by
  have h0 : shiftDrive w a 0 = 0 := by simp [shiftDrive]
  have hc : Continuous fun r => -shiftDrive w a r := (QuantumZipper.RS.continuous_shiftDrive hw a).neg
  unfold chartAL
  rw [rightImg_zero hc (by simp [h0]) le_rfl, h0]
  ring

theorem chartAR_shiftDrive_zero (hw : Continuous w) (a : ℝ) : chartAR (shiftDrive w a) 0 = 0 := by
  have h0 : shiftDrive w a 0 = 0 := by simp [shiftDrive]
  have hc : Continuous (shiftDrive w a) := QuantumZipper.RS.continuous_shiftDrive hw a
  unfold chartAR
  rw [rightImg_zero hc h0 le_rfl, h0]
  ring

theorem bornArcL_eq (hT : ((T x : ℝ≥0) : WithTop ℝ≥0) < kLife (γ x) (P x)) (hle : Sb x ≤ T x)
    (hw : Continuous w) (hEq : EqOn (kPath (γ x) (P x)) w (Icc 0 (T x))) :
    bornArcL γ P Sb T x = chartAL (shiftDrive w (Sb x)) ((T x : ℝ) - Sb x) := by
  have hST : Sb x + (T x - Sb x) = T x := add_tsub_cancel_of_le hle
  have h := arcVL_sub_arcW (γ := γ) (P := P) (S₀ := Sb) (Al := univ) (xL := fun (_ : X) (_ : Fin 1) => (0 : ℝ)) (ω := x)
    (mem_univ x) (r := T x - Sb x) (by rw [hST]; exact hT) hw (by rw [hST]; exact hEq) 0
  have hc := chartAL_shift hw (le_refl ((Sb x : ℝ))) (r := ((T x - Sb x : ℝ≥0) : ℝ)) (NNReal.coe_nonneg _)
  rw [sub_self, chartAL_shiftDrive_zero hw, add_sub_cancel_left] at hc
  rw [bornArcL, h, hc, NNReal.coe_sub hle]

theorem bornArcR_eq (hT : ((T x : ℝ≥0) : WithTop ℝ≥0) < kLife (γ x) (P x)) (hle : Sb x ≤ T x)
    (hw : Continuous w) (hEq : EqOn (kPath (γ x) (P x)) w (Icc 0 (T x))) :
    bornArcR γ P Sb T x = chartAR (shiftDrive w (Sb x)) ((T x : ℝ) - Sb x) := by
  have hST : Sb x + (T x - Sb x) = T x := add_tsub_cancel_of_le hle
  have h := arcVR_sub_arcW (γ := γ) (P := P) (S₀ := Sb) (Al := univ) (xR := fun (_ : X) (_ : Fin 1) => (0 : ℝ)) (ω := x)
    (mem_univ x) (r := T x - Sb x) (by rw [hST]; exact hT) hw (by rw [hST]; exact hEq) 0
  have hc := chartAR_shift hw (le_refl ((Sb x : ℝ))) (r := ((T x - Sb x : ℝ≥0) : ℝ)) (NNReal.coe_nonneg _)
  rw [sub_self, chartAR_shiftDrive_zero hw, add_sub_cancel_left] at hc
  rw [bornArcR, h, hc, NNReal.coe_sub hle]

theorem rootArcL_eq {n : ℕ} {X0 : X → Fin n → ℝ} (hT : ((T x : ℝ≥0) : WithTop ℝ≥0) < kLife (γ x) (P x))
    (hw : Continuous w) (hw0 : w 0 = 0) (hEq : EqOn (kPath (γ x) (P x)) w (Icc 0 (T x))) (k : Fin n) :
    rootArcL γ P X0 T k x = -rightImg (fun r => -w r) (-X0 x k) (T x) - w (T x) := by
  have h := arcVL_sub_arcW (γ := γ) (P := P) (S₀ := fun _ => (0 : ℝ≥0)) (Al := univ) (xL := X0) (ω := x)
    (mem_univ x) (r := T x) (by rw [zero_add]; exact hT) hw (by rw [zero_add]; exact hEq) k
  have hs : shiftDrv (fun s => -w s) ((0 : ℝ≥0) : ℝ) = fun r => -w r := by
    funext r
    simp [shiftDrv, hw0]
  have hs' : shiftDrv w ((0 : ℝ≥0) : ℝ) (T x) = w (T x) := by simp [shiftDrv, hw0]
  rw [rootArcL, h, hs, hs']

theorem rootArcR_eq {n : ℕ} {X0 : X → Fin n → ℝ} (hT : ((T x : ℝ≥0) : WithTop ℝ≥0) < kLife (γ x) (P x))
    (hw : Continuous w) (hw0 : w 0 = 0) (hEq : EqOn (kPath (γ x) (P x)) w (Icc 0 (T x))) (k : Fin n) :
    rootArcR γ P X0 T k x = rightImg w (X0 x k) (T x) - w (T x) := by
  have h := arcVR_sub_arcW (γ := γ) (P := P) (S₀ := fun _ => (0 : ℝ≥0)) (Al := univ) (xR := X0) (ω := x)
    (mem_univ x) (r := T x) (by rw [zero_add]; exact hT) hw (by rw [zero_add]; exact hEq) k
  have hs : shiftDrv w ((0 : ℝ≥0) : ℝ) = w := by
    funext r
    simp [shiftDrv, hw0]
  rw [rootArcR, h, hs]

/-- **The image stage marks at the capacity `T` are the arc-piece stage marks.** -/
theorem stageArcL_eq {nL : ℕ} {Sb : ℕ → X → ℝ≥0} {X0 : X → Fin (nL + 1) → ℝ} {ℓ : ℕ}
    (hγ : IsKilledArc (γ x) (P x)) (hT : ((T x : ℝ≥0) : WithTop ℝ≥0) < kLife (γ x) (P x))
    (hSb : ∀ j : Fin ℓ, Sb (j + 1) x ≤ T x) (xL : Fin nL → ℝ) (ω : ℝ → ℝ) (s : ℝ)
    (hX0 : X0 x = GlueImg.imgMarkL xL ω s) {A : ℕ → ℝ} (hA : ∀ j : Fin ℓ, A (j + 1) = Sb (j + 1) x) :
    stageArcL γ P Sb T X0 ℓ x = imgStageVL xL ω s (kPath (γ x) (P x)) (T x) A ℓ := by
  have hwc := continuous_clampDrv_kPath hγ hT
  have hw0 : Ito.clampDrv (kPath (γ x) (P x)) (T x) 0 = 0 := clampDrv_kPath_zero hγ
  have hEq : EqOn (kPath (γ x) (P x)) (Ito.clampDrv (kPath (γ x) (P x)) (T x)) (Icc 0 (T x)) :=
    fun r hr => (Ito.clampDrv_eqOn hr).symm
  rw [imgStageVL_congr hwc hEq xL ω s (fun j => by rw [hA j]; exact ⟨NNReal.coe_nonneg _, hSb j⟩)
    (NNReal.coe_nonneg _)]
  funext i
  refine Fin.addCases (fun j => ?_) (fun k => ?_) i
  · simp only [stageArcL, imgStageVL, Fin.append_left, imgBornL, hA j]
    exact bornArcL_eq hT (hSb j) hwc hEq
  · simp only [stageArcL, imgStageVL, Fin.append_right, rootVL]
    rw [rootArcL_eq hT hwc hw0 hEq k, hX0]

theorem stageArcR_eq {nR : ℕ} {Sb : ℕ → X → ℝ≥0} {X0 : X → Fin (nR + 1) → ℝ} {ℓ : ℕ}
    (hγ : IsKilledArc (γ x) (P x)) (hT : ((T x : ℝ≥0) : WithTop ℝ≥0) < kLife (γ x) (P x))
    (hSb : ∀ j : Fin ℓ, Sb (j + 1) x ≤ T x) (xR : Fin nR → ℝ) (ω : ℝ → ℝ) (s : ℝ)
    (hX0 : X0 x = GlueImg.imgMarkR xR ω s) {A : ℕ → ℝ} (hA : ∀ j : Fin ℓ, A (j + 1) = Sb (j + 1) x) :
    stageArcR γ P Sb T X0 ℓ x = imgStageVR xR ω s (kPath (γ x) (P x)) (T x) A ℓ := by
  have hwc := continuous_clampDrv_kPath hγ hT
  have hw0 : Ito.clampDrv (kPath (γ x) (P x)) (T x) 0 = 0 := clampDrv_kPath_zero hγ
  have hEq : EqOn (kPath (γ x) (P x)) (Ito.clampDrv (kPath (γ x) (P x)) (T x)) (Icc 0 (T x)) :=
    fun r hr => (Ito.clampDrv_eqOn hr).symm
  rw [imgStageVR_congr hwc hEq xR ω s (fun j => by rw [hA j]; exact ⟨NNReal.coe_nonneg _, hSb j⟩)
    (NNReal.coe_nonneg _)]
  funext i
  refine Fin.addCases (fun j => ?_) (fun k => ?_) i
  · simp only [stageArcR, imgStageVR, Fin.append_left, imgBornR, hA j]
    exact bornArcR_eq hT (hSb j) hwc hEq
  · simp only [stageArcR, imgStageVR, Fin.append_right, rootVR]
    rw [rootArcR_eq hT hwc hw0 hEq k, hX0]

variable [MeasurableSpace X]

theorem measurable_bornArcL (hF : IsKilledFamily γ P) (hSb : Measurable Sb) (hT : Measurable T) :
    Measurable (bornArcL γ P Sb T) := by
  have hd : Measurable fun x => ((T x - Sb x : ℝ≥0), x) := (hT.sub hSb).prodMk measurable_id
  have h1 := (Prop59Pieces.measurable_uncurry_arcVL hF hSb MeasurableSet.univ
    (xL := fun (_ : X) (_ : Fin 1) => (0 : ℝ)) measurable_const 0).comp hd
  have h2 := (Prop59Pieces.measurable_uncurry_arcW hF hSb MeasurableSet.univ).comp hd
  exact h1.sub h2

theorem measurable_bornArcR (hF : IsKilledFamily γ P) (hSb : Measurable Sb) (hT : Measurable T) :
    Measurable (bornArcR γ P Sb T) := by
  have hd : Measurable fun x => ((T x - Sb x : ℝ≥0), x) := (hT.sub hSb).prodMk measurable_id
  have h1 := (Prop59Pieces.measurable_uncurry_arcVR hF hSb MeasurableSet.univ
    (xR := fun (_ : X) (_ : Fin 1) => (0 : ℝ)) measurable_const 0).comp hd
  have h2 := (Prop59Pieces.measurable_uncurry_arcW hF hSb MeasurableSet.univ).comp hd
  exact h1.sub h2

theorem measurable_rootArcL {n : ℕ} {X0 : X → Fin n → ℝ} (hF : IsKilledFamily γ P) (hX0 : Measurable X0)
    (hT : Measurable T) (k : Fin n) : Measurable (rootArcL γ P X0 T k) := by
  have hd : Measurable fun x => (T x, x) := hT.prodMk measurable_id
  have h1 := (Prop59Pieces.measurable_uncurry_arcVL hF (S₀ := fun _ => (0 : ℝ≥0)) measurable_const
    MeasurableSet.univ hX0 k).comp hd
  have h2 := (Prop59Pieces.measurable_uncurry_arcW hF (S₀ := fun _ => (0 : ℝ≥0)) measurable_const
    MeasurableSet.univ).comp hd
  exact h1.sub h2

theorem measurable_rootArcR {n : ℕ} {X0 : X → Fin n → ℝ} (hF : IsKilledFamily γ P) (hX0 : Measurable X0)
    (hT : Measurable T) (k : Fin n) : Measurable (rootArcR γ P X0 T k) := by
  have hd : Measurable fun x => (T x, x) := hT.prodMk measurable_id
  have h1 := (Prop59Pieces.measurable_uncurry_arcVR hF (S₀ := fun _ => (0 : ℝ≥0)) measurable_const
    MeasurableSet.univ hX0 k).comp hd
  have h2 := (Prop59Pieces.measurable_uncurry_arcW hF (S₀ := fun _ => (0 : ℝ≥0)) measurable_const
    MeasurableSet.univ).comp hd
  exact h1.sub h2

theorem measurable_stageArcL {n : ℕ} {Sb : ℕ → X → ℝ≥0} {X0 : X → Fin n → ℝ} (hF : IsKilledFamily γ P)
    (hSb : ∀ m, Measurable (Sb m)) (hT : Measurable T) (hX0 : Measurable X0) (ℓ : ℕ) :
    Measurable (stageArcL γ P Sb T X0 ℓ) := by
  refine measurable_pi_iff.2 fun i => ?_
  refine Fin.addCases (fun j => ?_) (fun k => ?_) i
  · simp only [stageArcL, Fin.append_left]
    exact measurable_bornArcL hF (hSb _) hT
  · simp only [stageArcL, Fin.append_right]
    exact measurable_rootArcL hF hX0 hT k

theorem measurable_stageArcR {n : ℕ} {Sb : ℕ → X → ℝ≥0} {X0 : X → Fin n → ℝ} (hF : IsKilledFamily γ P)
    (hSb : ∀ m, Measurable (Sb m)) (hT : Measurable T) (hX0 : Measurable X0) (ℓ : ℕ) :
    Measurable (stageArcR γ P Sb T X0 ℓ) := by
  refine measurable_pi_iff.2 fun i => ?_
  refine Fin.addCases (fun j => ?_) (fun k => ?_) i
  · simp only [stageArcR, Fin.append_left]
    exact measurable_bornArcR hF (hSb _) hT
  · simp only [stageArcR, Fin.append_right]
    exact measurable_rootArcR hF hX0 hT k

/-- The capacity of a measurable family of killed arcs at a rational own time, `0` after the contact. -/
def capQ (γ : X → ℝ → ℂ) (P : X → Set ℝ) (u : ℚ) (x : X) : ℝ≥0 :=
  (({x | (u : ℝ) ∈ P x}.indicator fun x => capClock (γ x) u) x).toNNReal

theorem measurable_capQ (hF : IsKilledFamily γ P) (u : ℚ) : Measurable (capQ γ P u) :=
  measurable_real_toNNReal.comp (hF.cap u)

omit [MeasurableSpace X] in
theorem coe_capQ (hγ : IsKilledArc (γ x) (P x)) {u : ℚ} (hu : (u : ℝ) ∈ P x) :
    ((capQ γ P u x : ℝ≥0) : ℝ) = capClock (γ x) u := by
  rw [capQ, indicator_of_mem (show x ∈ {x | (u : ℝ) ∈ P x} from hu), Real.coe_toNNReal _ (hγ.capClock_nonneg hu)]

end Arc

/-! ### Random charts read from the counterflow history -/

section CfChart

variable {X : Type*} {m : MeasurableSpace X} {s : ℝ≥0} {Y : X → HistorySpace 0 0}

/-- **The counterflow chart read from a history whose stop at `s` is measurable has measurable data.** -/
theorem isMeasChart_cfChart (hY : Measurable[m] fun x => GlueCond.cfStop s (Y x)) :
    IsMeasChart m fun x => cfChart s (Y x) :=
  ⟨fun x => isConformal_cfChart (Y x), fun x => continuousOn_lift_cfChart (Y x),
    fun z ρ => measurableSet_comp_of_stopSigma (measurableSet_closedBall_subset_dom_cfChart z ρ) hY,
    fun z => measurable_indicator_fwd_cfChart_comp hY z, fun z => measurable_indicator_lift_cfChart_comp hY z⟩

end CfChart

end InteractingSLE.Sec5.CrossCond.StagedS5
