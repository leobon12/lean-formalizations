/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec5.StagedS3Shift
import InteractingSLE.Spec.Sec5.CrossCondThetaMart

/-!
# Proposition 5.9 at depth `ℓ`, step S3: (SW3) at the end of a piece as the restarted word's chart clause

Packet PROVE-STAGED-S3. On the θ-glued space, the staged path of a fixed extreme-angle schedule is read in the
counterflow chart; after the last switch (own time `τ`, image capacity `S₀`) the **restarted image word** is
PROVE-PROP59-PIECES' arc piece of the killed image arc started at `S₀` (`s3W`, `s3VL`, `s3VR`, `s3ζ`), with the
stage marks at `S₀` as initial marks (`s3XL`, `s3XR`), observed in the **restarted chart** `s3Chart`
(`rChart` of `StagedS3Shift`).

* **`ae_s3_charIdent`**: at the end `q` of piece `ℓ` of the schedule (own time `q ≥ τ`, before the first contact),
  DEPTH's `ae_stage_charIdent` is, almost surely on the alive event, the restarted word's chart formula
  `exp(i chartMean − ½ chartVar)` at the restarted image time `r_q = σ(q) − S₀`, with the stage weights
  `imgStageRhoL/R` and the height constant `2πχ + (θ_ℓ − θ₀)χ`.

Conditional helpers with distinct names; they replace no source theorem. R48: nothing here uses Theorem 1.2/1.3,
`Theorem12ParamStatement`, `Theorem13Statement` or any `*_of_param`; the only named input is
`Theorem12ParamCond44Statement` (R74), through DEPTH.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set Metric Filter Topology Complex
open scoped NNReal ENNReal Real
open QuantumZipper (H Hbar fwdHull fwdMap fwdMapInv logDerivFwd chiC)
open QuantumZipper.RS (shiftDrive)
open LQGMetric (DistOn TestOn)

universe u

namespace InteractingSLE.Sec5.CrossCond.StagedS3

open WangWu hiding ratPt exists_ratPt_dist_lt
open WangWu.ImgWord LawUnique GlueCond Cond44Ref CfRegQ Prop411Q WholeField LocalSets
open ImgDrv MartChar MartChar.RealFlow GlueImg Word49 Theta StagedFinal
open Restart Exist.StagedLaw Exist.Staged Theorem14.GW2Schedule
open Sec7.AdmCode Prop513TreeExtract Prop513Schedule StagedGlue StagedCand StagedDepth
open Sec7.Lemma71C (capClock)
open CrossCond.Staged (stageGood stageDrv catN cumT)
open Prop59Pieces (arcW arcVL arcVR arcζ)

/-! ### The restarted image word on the glued space -/

section Obj

variable {Ω : Type*} {nL nR : ℕ}

/-- **The alive event** of the last switch: a good glued sample whose last switch (own time `τ`) precedes the first
contact with the counterflow. -/
def s3Alive (s : ℝ≥0) (Wj : ℝ≥0 → Ω → ℝ) (E : Set (Ω × HistorySpace 0 0)) (τ : ℝ) :
    Set (Ω × HistorySpace 0 0) :=
  {p | p ∈ E ∧ τ ∈ gPre s (fun _ => ⊤) Wj E p}

open scoped Classical in
/-- **The restart capacity** `S₀ = σ(τ)` on the alive event (`0` elsewhere). -/
def s3Start (s : ℝ≥0) (Wj : ℝ≥0 → Ω → ℝ) (E : Set (Ω × HistorySpace 0 0)) (τ : ℝ)
    (p : Ω × HistorySpace 0 0) : ℝ≥0 :=
  if p ∈ s3Alive s Wj E τ then (capClock (gCurve s (fun _ => ⊤) Wj E p) τ).toNNReal else 0

/-- **The restarted image driver** `u ↦ kW(S₀ + u) − kW(S₀)`. -/
def s3W (s : ℝ≥0) (Wj : ℝ≥0 → Ω → ℝ) (E : Set (Ω × HistorySpace 0 0)) (τ : ℝ) :
    ℝ≥0 → Ω × HistorySpace 0 0 → ℝ :=
  arcW (gCurve s (fun _ => ⊤) Wj E) (gPre s (fun _ => ⊤) Wj E) (s3Start s Wj E τ) univ

/-- **The restarted lifetime** (the first contact after `S₀`). -/
def s3ζ (s : ℝ≥0) (Wj : ℝ≥0 → Ω → ℝ) (E : Set (Ω × HistorySpace 0 0)) (τ : ℝ) :
    Ω × HistorySpace 0 0 → ℝ≥0∞ :=
  arcζ (gCurve s (fun _ => ⊤) Wj E) (gPre s (fun _ => ⊤) Wj E) (s3Start s Wj E τ) univ

/-- **The restarted chart**: the counterflow chart followed by the image chain's Loewner stage up to `S₀`. -/
def s3Chart (s : ℝ≥0) (Wj : ℝ≥0 → Ω → ℝ) (E : Set (Ω × HistorySpace 0 0)) (τ : ℝ)
    (p : Ω × HistorySpace 0 0) : Chart :=
  rChart (cfChart s p.2) (gCurve s (fun _ => ⊤) Wj E p) (gPre s (fun _ => ⊤) Wj E p) (s3Start s Wj E τ p)

open scoped Classical in
/-- **The initial left marks** of the restarted word: the left marks of the image stage word at `S₀` (relative to
the driver; switch `m` born at `σ(τ_m)`), `0` off the alive event. -/
def s3XL (xL : Fin nL → ℝ) (τs : ℕ → ℝ) (ℓ : ℕ) (s : ℝ≥0) (Wj : ℝ≥0 → Ω → ℝ) (E : Set (Ω × HistorySpace 0 0))
    (τ : ℝ) (p : Ω × HistorySpace 0 0) : Fin (ℓ + (nL + 1)) → ℝ :=
  if p ∈ s3Alive s Wj E τ then
    imgStageVL xL (cfDrv0 s p.2) s (kPath (gCurve s (fun _ => ⊤) Wj E p) (gPre s (fun _ => ⊤) Wj E p))
      (s3Start s Wj E τ p) (fun m => capClock (gCurve s (fun _ => ⊤) Wj E p) (τs m)) ℓ
  else 0

open scoped Classical in
/-- **The initial right marks** of the restarted word. -/
def s3XR (xR : Fin nR → ℝ) (τs : ℕ → ℝ) (ℓ : ℕ) (s : ℝ≥0) (Wj : ℝ≥0 → Ω → ℝ) (E : Set (Ω × HistorySpace 0 0))
    (τ : ℝ) (p : Ω × HistorySpace 0 0) : Fin (ℓ + (nR + 1)) → ℝ :=
  if p ∈ s3Alive s Wj E τ then
    imgStageVR xR (cfDrv0 s p.2) s (kPath (gCurve s (fun _ => ⊤) Wj E p) (gPre s (fun _ => ⊤) Wj E p))
      (s3Start s Wj E τ p) (fun m => capClock (gCurve s (fun _ => ⊤) Wj E p) (τs m)) ℓ
  else 0

/-- **The restarted left marks**: the real Loewner images of the initial left marks under the restarted driver. -/
def s3VL (xL : Fin nL → ℝ) (τs : ℕ → ℝ) (ℓ : ℕ) (s : ℝ≥0) (Wj : ℝ≥0 → Ω → ℝ) (E : Set (Ω × HistorySpace 0 0))
    (τ : ℝ) : Fin (ℓ + (nL + 1)) → ℝ≥0 → Ω × HistorySpace 0 0 → ℝ :=
  arcVL (gCurve s (fun _ => ⊤) Wj E) (gPre s (fun _ => ⊤) Wj E) (s3Start s Wj E τ) univ (s3XL xL τs ℓ s Wj E τ)

/-- **The restarted right marks.** -/
def s3VR (xR : Fin nR → ℝ) (τs : ℕ → ℝ) (ℓ : ℕ) (s : ℝ≥0) (Wj : ℝ≥0 → Ω → ℝ) (E : Set (Ω × HistorySpace 0 0))
    (τ : ℝ) : Fin (ℓ + (nR + 1)) → ℝ≥0 → Ω × HistorySpace 0 0 → ℝ :=
  arcVR (gCurve s (fun _ => ⊤) Wj E) (gPre s (fun _ => ⊤) Wj E) (s3Start s Wj E τ) univ (s3XR xR τs ℓ s Wj E τ)

end Obj

/-! ### Signs and switch-time congruence of the image stage marks -/

section Sign

variable {nL nR : ℕ} {w : ℝ → ℝ} {T : ℝ} {A A' : ℕ → ℝ} {ℓ : ℕ}

theorem imgStageVL_nonpos (hw : Continuous w) (xL : Fin nL → ℝ) (ω : ℝ → ℝ) (s : ℝ) (hT : 0 ≤ T)
    (hA : ∀ j : Fin ℓ, A (j + 1) ≤ T) (i : Fin (ℓ + (nL + 1))) : imgStageVL xL ω s w T A ℓ i ≤ 0 := by
  refine Fin.addCases (fun j => ?_) (fun k => ?_) i
  · simp only [imgStageVL, Fin.append_left, imgBornL]
    exact chartAL_nonpos (QuantumZipper.RS.continuous_shiftDrive hw _) (sub_nonneg.2 (hA j))
  · simp only [imgStageVL, Fin.append_right, rootVL]
    have := le_rightImg (w := fun r => -w r) hw.neg (-imgMarkL xL ω s k) hT
    linarith

theorem imgStageVR_nonneg (hw : Continuous w) (xR : Fin nR → ℝ) (ω : ℝ → ℝ) (s : ℝ) (hT : 0 ≤ T)
    (hA : ∀ j : Fin ℓ, A (j + 1) ≤ T) (i : Fin (ℓ + (nR + 1))) : 0 ≤ imgStageVR xR ω s w T A ℓ i := by
  refine Fin.addCases (fun j => ?_) (fun k => ?_) i
  · simp only [imgStageVR, Fin.append_left, imgBornR]
    exact chartAR_nonneg (QuantumZipper.RS.continuous_shiftDrive hw _) (sub_nonneg.2 (hA j))
  · simp only [imgStageVR, Fin.append_right, rootVR]
    have := le_rightImg hw (imgMarkR xR ω s k) hT
    linarith

theorem imgStageVL_congr_A (xL : Fin nL → ℝ) (ω : ℝ → ℝ) (s : ℝ) (h : ∀ j : Fin ℓ, A (j + 1) = A' (j + 1)) :
    imgStageVL xL ω s w T A ℓ = imgStageVL xL ω s w T A' ℓ := by
  funext i
  refine Fin.addCases (fun j => ?_) (fun k => ?_) i
  · simp only [imgStageVL, Fin.append_left, imgBornL, h j]
  · simp only [imgStageVL, Fin.append_right]

theorem imgStageVR_congr_A (xR : Fin nR → ℝ) (ω : ℝ → ℝ) (s : ℝ) (h : ∀ j : Fin ℓ, A (j + 1) = A' (j + 1)) :
    imgStageVR xR ω s w T A ℓ = imgStageVR xR ω s w T A' ℓ := by
  funext i
  refine Fin.addCases (fun j => ?_) (fun k => ?_) i
  · simp only [imgStageVR, Fin.append_left, imgBornR, h j]
  · simp only [imgStageVR, Fin.append_right]

end Sign

/-! ### The restarted marks relative to the restarted driver are the stage marks -/

section Rel

variable {Ω : Type*} {nL nR : ℕ} {s : ℝ≥0} {Wj : ℝ≥0 → Ω → ℝ} {E : Set (Ω × HistorySpace 0 0)} {τ : ℝ}
  {p : Ω × HistorySpace 0 0}

theorem s3Start_of_mem (hp : p ∈ s3Alive s Wj E τ) :
    s3Start s Wj E τ p = (capClock (gCurve s (fun _ => ⊤) Wj E p) τ).toNNReal := by
  simp only [s3Start, hp, ↓reduceIte]

/-- **The pre-contact data of an alive sample at a later own time `q`**: the restart capacity is at most `σ(q)`,
`S₀ + (σ(q) − S₀) = σ(q)` lies before the terminal capacity, and the killed chain driver agrees on `[0, σ(q)]` with
any continuous extension `W''` of the chain driver. -/
theorem s3_pre (hEg : ∀ p ∈ E, IsGood49 s (fun _ => ⊤) Wj p) (hp : p ∈ s3Alive s Wj E τ) {q : ℝ}
    (hq : q ∈ gPre s (fun _ => ⊤) Wj E p) (hτq : τ ≤ q) {W'' : ℝ → ℝ}
    (hEq : EqOn W'' (chainDrv (gCurve s (fun _ => ⊤) Wj E p) (gPre s (fun _ => ⊤) Wj E p))
      (Icc 0 (capClock (gCurve s (fun _ => ⊤) Wj E p) q))) :
    s3Start s Wj E τ p ≤ (capClock (gCurve s (fun _ => ⊤) Wj E p) q).toNNReal ∧
      s3Start s Wj E τ p + ((capClock (gCurve s (fun _ => ⊤) Wj E p) q).toNNReal - s3Start s Wj E τ p) =
        (capClock (gCurve s (fun _ => ⊤) Wj E p) q).toNNReal ∧
      ((((capClock (gCurve s (fun _ => ⊤) Wj E p) q).toNNReal : ℝ≥0) : WithTop ℝ≥0) <
        kLife (gCurve s (fun _ => ⊤) Wj E p) (gPre s (fun _ => ⊤) Wj E p)) ∧
      EqOn (kPath (gCurve s (fun _ => ⊤) Wj E p) (gPre s (fun _ => ⊤) Wj E p)) W''
        (Icc 0 (capClock (gCurve s (fun _ => ⊤) Wj E p) q)) := by
  set γ := gCurve s (fun _ => ⊤) Wj E p with hγdef
  set P := gPre s (fun _ => ⊤) Wj E p with hPdef
  have hγ : IsKilledArc γ P := isKilledArc_gCurve hEg p
  have hτP : τ ∈ P := hp.2
  have hle : capClock γ τ ≤ capClock γ q := hγ.strictMonoOn_capClock.monotoneOn hτP hq hτq
  have hS : s3Start s Wj E τ p ≤ (capClock γ q).toNNReal := by
    rw [s3Start_of_mem hp]
    exact Real.toNNReal_le_toNNReal hle
  have hlt := hγ.lt_kLife hq
  refine ⟨hS, add_tsub_cancel_of_le hS, hlt, fun x hx => ?_⟩
  have hx0 : 0 ≤ x := hx.1
  have hxq : x.toNNReal ≤ (capClock γ q).toNNReal := Real.toNNReal_le_toNNReal hx.2
  have hxl : ((x.toNNReal : ℝ≥0) : WithTop ℝ≥0) < kLife γ P := lt_of_le_of_lt (WithTop.coe_le_coe.2 hxq) hlt
  simp only [kPath]
  rw [kW_of_lt hxl, Real.coe_toNNReal _ hx0, hEq hx]

variable {xL : Fin nL → ℝ} {xR : Fin nR → ℝ} {τs : ℕ → ℝ} {ℓ : ℕ}

/-- The switch capacities of an alive sample lie in `[0, S₀]`. -/
theorem s3_switch (hEg : ∀ p ∈ E, IsGood49 s (fun _ => ⊤) Wj p) (hp : p ∈ s3Alive s Wj E τ)
    (hτs : ∀ j : Fin ℓ, 0 ≤ τs (j + 1) ∧ τs (j + 1) ≤ τ) (j : Fin ℓ) :
    0 ≤ capClock (gCurve s (fun _ => ⊤) Wj E p) (τs (j + 1)) ∧
      capClock (gCurve s (fun _ => ⊤) Wj E p) (τs (j + 1)) ≤ (s3Start s Wj E τ p : ℝ) := by
  have hγ := isKilledArc_gCurve hEg p
  have hτP : τ ∈ gPre s (fun _ => ⊤) Wj E p := hp.2
  have hmem : τs (j + 1) ∈ gPre s (fun _ => ⊤) Wj E p := hγ.icc τ hτP (hτs j)
  rw [s3Start_of_mem hp]
  refine ⟨hγ.capClock_nonneg hmem, ?_⟩
  rw [Real.coe_toNNReal _ (hγ.capClock_nonneg hτP)]
  exact hγ.strictMonoOn_capClock.monotoneOn hmem hτP (hτs j).2

/-- **The restarted left marks relative to the restarted driver at `r_q = σ(q) − S₀` are the left marks of the
image stage word at `σ(q)`** (for any continuous extension `W''` of the chain driver). -/
theorem s3VL_sub_s3W (hEg : ∀ p ∈ E, IsGood49 s (fun _ => ⊤) Wj p) (hp : p ∈ s3Alive s Wj E τ) {q : ℝ}
    (hq : q ∈ gPre s (fun _ => ⊤) Wj E p) (hτq : τ ≤ q) {W'' : ℝ → ℝ} (hW'' : Continuous W'')
    (hEq : EqOn W'' (chainDrv (gCurve s (fun _ => ⊤) Wj E p) (gPre s (fun _ => ⊤) Wj E p))
      (Icc 0 (capClock (gCurve s (fun _ => ⊤) Wj E p) q)))
    (hτs : ∀ j : Fin ℓ, 0 ≤ τs (j + 1) ∧ τs (j + 1) ≤ τ) :
    (fun i => s3VL xL τs ℓ s Wj E τ i ((capClock (gCurve s (fun _ => ⊤) Wj E p) q).toNNReal -
        s3Start s Wj E τ p) p -
      s3W s Wj E τ ((capClock (gCurve s (fun _ => ⊤) Wj E p) q).toNNReal - s3Start s Wj E τ p) p) =
      imgStageVL xL (cfDrv0 s p.2) s W'' (capClock (gCurve s (fun _ => ⊤) Wj E p) q)
        (fun m => capClock (gCurve s (fun _ => ⊤) Wj E p) (τs m)) ℓ := by
  set γ := gCurve s (fun _ => ⊤) Wj E p with hγdef
  set P := gPre s (fun _ => ⊤) Wj E p with hPdef
  have hγ : IsKilledArc γ P := isKilledArc_gCurve hEg p
  obtain ⟨hS, hsum, hlt, hEqk⟩ := s3_pre hEg hp hq hτq hEq
  set S₀ := s3Start s Wj E τ p with hS₀
  set r := (capClock γ q).toNNReal - S₀ with hrdef
  have hcq : 0 ≤ capClock γ q := hγ.capClock_nonneg hq
  have hsumR : ((S₀ + r : ℝ≥0) : ℝ) = capClock γ q := by rw [hsum, Real.coe_toNNReal _ hcq]
  have hr : ((S₀ + r : ℝ≥0) : WithTop ℝ≥0) < kLife γ P := by rw [hsum]; exact hlt
  have hEq' : EqOn (kPath γ P) W'' (Icc 0 ((S₀ + r : ℝ≥0) : ℝ)) := by rw [hsumR]; exact hEqk
  have hA := s3_switch hEg hp hτs
  have hEqS : EqOn (kPath γ P) W'' (Icc 0 (S₀ : ℝ)) := fun x hx =>
    hEq' ⟨hx.1, hx.2.trans (by exact_mod_cast le_self_add)⟩
  funext i
  have h1 := Sec5.CrossCond.StagedS3.arcVL_sub_arcW (γ := gCurve s (fun _ => ⊤) Wj E)
    (P := gPre s (fun _ => ⊤) Wj E) (S₀ := s3Start s Wj E τ) (Al := univ) (xL := s3XL xL τs ℓ s Wj E τ)
    (mem_univ p) hr hW'' hEq' i
  simp only [s3VL, s3W]
  rw [h1]
  have hx0 : s3XL xL τs ℓ s Wj E τ p = imgStageVL xL (cfDrv0 s p.2) s W'' (S₀ : ℝ) (fun m => capClock γ (τs m)) ℓ := by
    simp only [s3XL, hp, ↓reduceIte]
    exact imgStageVL_congr hW'' hEqS xL _ s hA S₀.coe_nonneg
  rw [hx0, imgStageVL_shift hW'' xL (cfDrv0 s p.2) s (fun j => (hA j).2) S₀.coe_nonneg r.coe_nonneg i,
    ← NNReal.coe_add, hsumR]

/-- **The restarted right marks relative to the restarted driver at `r_q` are the right stage marks at `σ(q)`.** -/
theorem s3VR_sub_s3W (hEg : ∀ p ∈ E, IsGood49 s (fun _ => ⊤) Wj p) (hp : p ∈ s3Alive s Wj E τ) {q : ℝ}
    (hq : q ∈ gPre s (fun _ => ⊤) Wj E p) (hτq : τ ≤ q) {W'' : ℝ → ℝ} (hW'' : Continuous W'')
    (hEq : EqOn W'' (chainDrv (gCurve s (fun _ => ⊤) Wj E p) (gPre s (fun _ => ⊤) Wj E p))
      (Icc 0 (capClock (gCurve s (fun _ => ⊤) Wj E p) q)))
    (hτs : ∀ j : Fin ℓ, 0 ≤ τs (j + 1) ∧ τs (j + 1) ≤ τ) :
    (fun i => s3VR xR τs ℓ s Wj E τ i ((capClock (gCurve s (fun _ => ⊤) Wj E p) q).toNNReal -
        s3Start s Wj E τ p) p -
      s3W s Wj E τ ((capClock (gCurve s (fun _ => ⊤) Wj E p) q).toNNReal - s3Start s Wj E τ p) p) =
      imgStageVR xR (cfDrv0 s p.2) s W'' (capClock (gCurve s (fun _ => ⊤) Wj E p) q)
        (fun m => capClock (gCurve s (fun _ => ⊤) Wj E p) (τs m)) ℓ := by
  set γ := gCurve s (fun _ => ⊤) Wj E p with hγdef
  set P := gPre s (fun _ => ⊤) Wj E p with hPdef
  have hγ : IsKilledArc γ P := isKilledArc_gCurve hEg p
  obtain ⟨hS, hsum, hlt, hEqk⟩ := s3_pre hEg hp hq hτq hEq
  set S₀ := s3Start s Wj E τ p with hS₀
  set r := (capClock γ q).toNNReal - S₀ with hrdef
  have hcq : 0 ≤ capClock γ q := hγ.capClock_nonneg hq
  have hsumR : ((S₀ + r : ℝ≥0) : ℝ) = capClock γ q := by rw [hsum, Real.coe_toNNReal _ hcq]
  have hr : ((S₀ + r : ℝ≥0) : WithTop ℝ≥0) < kLife γ P := by rw [hsum]; exact hlt
  have hEq' : EqOn (kPath γ P) W'' (Icc 0 ((S₀ + r : ℝ≥0) : ℝ)) := by rw [hsumR]; exact hEqk
  have hA := s3_switch hEg hp hτs
  have hEqS : EqOn (kPath γ P) W'' (Icc 0 (S₀ : ℝ)) := fun x hx =>
    hEq' ⟨hx.1, hx.2.trans (by exact_mod_cast le_self_add)⟩
  funext i
  have h1 := Sec5.CrossCond.StagedS3.arcVR_sub_arcW (γ := gCurve s (fun _ => ⊤) Wj E)
    (P := gPre s (fun _ => ⊤) Wj E) (S₀ := s3Start s Wj E τ) (Al := univ) (xR := s3XR xR τs ℓ s Wj E τ)
    (mem_univ p) hr hW'' hEq' i
  simp only [s3VR, s3W]
  rw [h1]
  have hx0 : s3XR xR τs ℓ s Wj E τ p = imgStageVR xR (cfDrv0 s p.2) s W'' (S₀ : ℝ) (fun m => capClock γ (τs m)) ℓ := by
    simp only [s3XR, hp, ↓reduceIte]
    exact imgStageVR_congr hW'' hEqS xR _ s hA S₀.coe_nonneg
  rw [hx0, imgStageVR_shift hW'' xR (cfDrv0 s p.2) s (fun j => (hA j).2) S₀.coe_nonneg r.coe_nonneg i,
    ← NNReal.coe_add, hsumR]

end Rel

/-! ### (SW3) at the end of a piece is the restarted word's chart formula -/

section Glued

variable (h44 : Theorem12ParamCond44Statement.{u}) {κ θ : ℝ} (hκ : 0 < κ) (hκ4 : κ < 4) {nL nR : ℕ}
  {xL : Fin nL → ℝ} {xR : Fin nR → ℝ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ}
  {Ω : Type u} [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {𝓕 : Filtration ℝ≥0 mΩ} {W : ℝ≥0 → Ω → ℝ} {VL : Fin nL → ℝ≥0 → Ω → ℝ} {VR : Fin nR → ℝ≥0 → Ω → ℝ}
  {B : ℝ≥0 → Ω → ℝ} {ζ : Ω → ℝ≥0∞} {h : Ω → DistOn upperHalfPlaneOpens}
  {Ω₂ : Type u} {mΩ₂ : MeasurableSpace Ω₂} {P₂ : Measure Ω₂} [IsProbabilityMeasure P₂]
  {h₂ : Ω₂ → DistOn upperHalfPlaneOpens} {W₂ : ℝ≥0 → Ω₂ → ℝ} {ζ₂ : Ω₂ → ℝ≥0∞}
  {k : Kernel (DistOn upperHalfPlaneOpens) (HistorySpace 0 0)} [IsMarkovKernel k] {u₀ : ℂ → ℝ}
  {E : ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞} {hs : Ω → DistOn upperHalfPlaneOpens} {us : ℂ → ℝ}

include h44 hκ hκ4 in
/-- **(SW3) at the end of piece `ℓ` as the restarted word's chart formula.** Under the hypotheses of DEPTH's
`ae_stage_charIdent` for the schedule `sc` (switch own times `τs (j+1) = startT (schedD sc) (j+1) ≤ τ ≤ q`, where `q`
is the end of piece `ℓ`), almost surely on the alive event with `q` before the first contact and the restarted
chart-avoidance event at `r_q = σ(q) − S₀`, the conditional characteristic value of `h(φ)` given DEPTH's σ-algebra is
`exp(i chartMean − ½ chartVar)` of the restarted word (stage weights, height constant `2πχ + (θ_ℓ − θ₀)χ`). -/
theorem ae_s3_charIdent (hC : IsOptionalHullCoupling κ xL xR ρL ρR P 𝓕 W VL VR B ζ h)
    (hθb : CfThetaBounds κ θ ρL ρR xL xR) (hcf : IsCenteredCounterflowDriver κ P₂ h₂ W₂ ζ₂)
    (hlaw : P.map (fun ω => cfFieldT κ θ (h ω)) = P₂.map h₂)
    (hk : P₂.map (fun ω => (h₂ ω, cfHistory W₂ ζ₂ ω)) = P₂.map h₂ ⊗ₘ k)
    (hu₀ : IsBoundedHarmonicExtension (forceBoundaryData κ ρL ρR xL xR) (forceJumpSet xL xR) u₀)
    (hxL : ∀ i, xL i ≤ 0) (hxR : ∀ j, 0 ≤ xR j)
    (hcs : ∀ ω, WholeField.centredField hs us ω = WholeField.centredField h u₀ ω)
    (c₀ : BoundaryWord) (hc₀ : ExtremeHeights κ c₀) (hh : IsGFFWithBoundaryData P hs c₀.fn c₀.jumps)
    (hus : IsBoundedHarmonicExtension c₀.fn c₀.jumps us) (sc : Schedule)
    (hu₀s : ∀ z, u₀ z = us z + schedAngle (scheduleList sc) 0 * chiC κ)
    (hE : IsStagedHistory κ c₀.fn c₀.jumps P hs (scheduleSpec sc) E) (hreg : ∀ j ω, IsRegularDriver (E j ω))
    {ℓ : ℕ} (hn : ℓ + 1 ≤ schedL sc) {s : ℝ≥0} (hs0 : 0 < s) {u' : ℂ → ℝ}
    (hu' : IsBoundedHarmonicExtension
      (cfWordData κ (fun x => forceBoundaryData κ ρL ρR xL xR x + -(θ * chiC κ)) (forceJumpFinset xL xR))
      (cfWordJumps κ (fun x => forceBoundaryData κ ρL ρR xL xR x + -(θ * chiC κ)) (forceJumpFinset xL xR)) u')
    {τ : ℝ} {τs : ℕ → ℝ} (hτs : ∀ j : Fin ℓ, startT (fun i => (schedD sc i : ℝ)) (j + 1) = τs (j + 1))
    (hτsτ : ∀ j : Fin ℓ, 0 ≤ τs (j + 1) ∧ τs (j + 1) ≤ τ) (hτq : τ ≤ ((cumT (schedD sc) ℓ : ℝ≥0) : ℝ))
    (φ : TestOn upperHalfPlaneOpens) :
    ∀ᵐ p ∂(glueMeasure P k (fun ω => cfFieldT κ θ (h ω)) ((measurable_cfFieldT κ θ).comp hC.2.1)),
      p ∈ s3Alive s (joinProc sc E) (glueGood (glueMeasure P k (fun ω => cfFieldT κ θ (h ω))
        ((measurable_cfFieldT κ θ).comp hC.2.1)) s (fun _ => ⊤) (joinProc sc E)) τ →
      ((cumT (schedD sc) ℓ : ℝ≥0) : ℝ) ∈ gPre s (fun _ => ⊤) (joinProc sc E)
        (glueGood (glueMeasure P k (fun ω => cfFieldT κ θ (h ω)) ((measurable_cfFieldT κ θ).comp hC.2.1)) s
          (fun _ => ⊤) (joinProc sc E)) p →
      Sec7.Lemma71D.IsChartAvoid
        (fun t => s3W s (joinProc sc E) (glueGood (glueMeasure P k (fun ω => cfFieldT κ θ (h ω))
          ((measurable_cfFieldT κ θ).comp hC.2.1)) s (fun _ => ⊤) (joinProc sc E)) τ t p)
        (s3ζ s (joinProc sc E) (glueGood (glueMeasure P k (fun ω => cfFieldT κ θ (h ω))
          ((measurable_cfFieldT κ θ).comp hC.2.1)) s (fun _ => ⊤) (joinProc sc E)) τ p)
        (s3Chart s (joinProc sc E) (glueGood (glueMeasure P k (fun ω => cfFieldT κ θ (h ω))
          ((measurable_cfFieldT κ θ).comp hC.2.1)) s (fun _ => ⊤) (joinProc sc E)) τ p) φ
        ((capClock (gCurve s (fun _ => ⊤) (joinProc sc E) (glueGood (glueMeasure P k
          (fun ω => cfFieldT κ θ (h ω)) ((measurable_cfFieldT κ θ).comp hC.2.1)) s (fun _ => ⊤) (joinProc sc E)) p)
            ((cumT (schedD sc) ℓ : ℝ≥0) : ℝ)).toNNReal -
          s3Start s (joinProc sc E) (glueGood (glueMeasure P k (fun ω => cfFieldT κ θ (h ω))
            ((measurable_cfFieldT κ θ).comp hC.2.1)) s (fun _ => ⊤) (joinProc sc E)) τ p) →
      (glueMeasure P k (fun ω => cfFieldT κ θ (h ω)) ((measurable_cfFieldT κ θ).comp hC.2.1))[
          fun p' => Complex.exp (Complex.I * (h p'.1 φ : ℂ)) |
          germSigma (fun p : Ω × HistorySpace 0 0 =>
              recHull sc ℓ (pastMap κ c₀.fn c₀.jumps (scheduleSpec sc) E (ℓ + 1) p.1) ∪ cfHullQ s p.2)
            (fun p : Ω × HistorySpace 0 0 => cenTT κ θ u₀ (cfFieldT κ θ (h p.1))) ⊔
          ((inferInstance : MeasurableSpace (PastData (ℓ + 1))).prod (stopSigma s)).comap
            (fun p : Ω × HistorySpace 0 0 => (pastMap κ c₀.fn c₀.jumps (scheduleSpec sc) E (ℓ + 1) p.1, p.2))] p =
        Complex.exp (Complex.I * ((Sec7.Lemma71D.chartMean κ
            (imgStageRhoL κ θ ρL (fun j => schedAngle (scheduleList sc) j - schedAngle (scheduleList sc) 0) ℓ)
            (imgStageRhoR κ θ ρR (fun j => schedAngle (scheduleList sc) j - schedAngle (scheduleList sc) 0) ℓ)
            (fun t => s3W s (joinProc sc E) (glueGood (glueMeasure P k (fun ω => cfFieldT κ θ (h ω))
              ((measurable_cfFieldT κ θ).comp hC.2.1)) s (fun _ => ⊤) (joinProc sc E)) τ t p)
            (fun i t => s3VL xL τs ℓ s (joinProc sc E) (glueGood (glueMeasure P k (fun ω => cfFieldT κ θ (h ω))
              ((measurable_cfFieldT κ θ).comp hC.2.1)) s (fun _ => ⊤) (joinProc sc E)) τ i t p)
            (fun i t => s3VR xR τs ℓ s (joinProc sc E) (glueGood (glueMeasure P k (fun ω => cfFieldT κ θ (h ω))
              ((measurable_cfFieldT κ θ).comp hC.2.1)) s (fun _ => ⊤) (joinProc sc E)) τ i t p)
            (s3Chart s (joinProc sc E) (glueGood (glueMeasure P k (fun ω => cfFieldT κ θ (h ω))
              ((measurable_cfFieldT κ θ).comp hC.2.1)) s (fun _ => ⊤) (joinProc sc E)) τ p)
            (2 * Real.pi * chiC κ + (schedAngle (scheduleList sc) ℓ - schedAngle (scheduleList sc) 0) * chiC κ)
            (chiC κ) φ
            ((capClock (gCurve s (fun _ => ⊤) (joinProc sc E) (glueGood (glueMeasure P k
              (fun ω => cfFieldT κ θ (h ω)) ((measurable_cfFieldT κ θ).comp hC.2.1)) s (fun _ => ⊤)
                (joinProc sc E)) p) ((cumT (schedD sc) ℓ : ℝ≥0) : ℝ)).toNNReal -
              s3Start s (joinProc sc E) (glueGood (glueMeasure P k (fun ω => cfFieldT κ θ (h ω))
                ((measurable_cfFieldT κ θ).comp hC.2.1)) s (fun _ => ⊤) (joinProc sc E)) τ p) : ℝ) : ℂ) -
          (((1 / 2 : ℝ) * Sec7.Lemma71D.chartVar
            (fun t => s3W s (joinProc sc E) (glueGood (glueMeasure P k (fun ω => cfFieldT κ θ (h ω))
              ((measurable_cfFieldT κ θ).comp hC.2.1)) s (fun _ => ⊤) (joinProc sc E)) τ t p)
            (s3Chart s (joinProc sc E) (glueGood (glueMeasure P k (fun ω => cfFieldT κ θ (h ω))
              ((measurable_cfFieldT κ θ).comp hC.2.1)) s (fun _ => ⊤) (joinProc sc E)) τ p) φ
            ((capClock (gCurve s (fun _ => ⊤) (joinProc sc E) (glueGood (glueMeasure P k
              (fun ω => cfFieldT κ θ (h ω)) ((measurable_cfFieldT κ θ).comp hC.2.1)) s (fun _ => ⊤)
                (joinProc sc E)) p) ((cumT (schedD sc) ℓ : ℝ≥0) : ℝ)).toNNReal -
              s3Start s (joinProc sc E) (glueGood (glueMeasure P k (fun ω => cfFieldT κ θ (h ω))
                ((measurable_cfFieldT κ θ).comp hC.2.1)) s (fun _ => ⊤) (joinProc sc E)) τ p) : ℝ) : ℂ)) := by
  set μ := glueMeasure P k (fun ω => cfFieldT κ θ (h ω)) ((measurable_cfFieldT κ θ).comp hC.2.1) with hμ
  set Wj := joinProc sc E with hWj
  set Eg := glueGood μ s (fun _ => ⊤) Wj with hEgdef
  set ang := schedAngle (scheduleList sc) with hang
  set q : ℝ := ((cumT (schedD sc) ℓ : ℝ≥0) : ℝ) with hqdef
  have hEg : ∀ p ∈ Eg, IsGood49 s (fun _ => ⊤) Wj p := isGood49_of_mem_glueGood
  have hXm : Measurable fun ω => cfFieldT κ θ (h ω) := (measurable_cfFieldT κ θ).comp hC.2.1
  have hGg := ae_glue_fst (μ := P) k hXm ((ae_isGoodSched h44 hκ hκ4 c₀ hc₀ hh sc hE hreg).and
    (ae_schedule_goodPath h44 hκ hκ4 c₀ hc₀ hh sc hE hreg))
  have hchar := ae_stage_charIdent h44 hκ hκ4 hC hθb hcf hlaw hk hu₀ hxL hxR hcs c₀ hc₀ hh hus sc hu₀s hE hreg hn
    hs0 hu' φ
  filter_upwards [hGg, hchar] with p ⟨hgs, hgp⟩ hch hpA htP hav
  have hpE : p ∈ Eg := hpA.1
  set γ := gCurve s (fun _ => ⊤) Wj Eg p with hγdef
  set Pp := gPre s (fun _ => ⊤) Wj Eg p with hPdef
  have hγ : IsKilledArc γ Pp := isKilledArc_gCurve hEg p
  -- the staged trace and the hull of the records
  obtain ⟨hjc, hj0, hαp, hα⟩ := properArc_seedLine_joinProc sc (fun j => hreg j p.1) hgp
  have hgood := StagedDepth.IsGoodSched.mem_stageGood (κ := κ) (c₀ := c₀) hgs (fun j => hreg j p.1) hn
  set u := pastMap κ c₀.fn c₀.jumps (scheduleSpec sc) E (ℓ + 1) p.1 with hudef
  set Wα : ℝ → ℝ := fun r => joinW sc E p.1 r.toNNReal with hWαdef
  set Wcat : ℝ → ℝ := Ito.rpath (catN (stageDrv κ c₀.fn c₀.jumps (scheduleSpec sc) E ℓ p.1) (schedD sc) ℓ)
    with hWcatdef
  have hWα : Continuous Wα := hjc.comp continuous_real_toNNReal
  have hWcat : Continuous Wcat := CrossCond.Staged.continuous_rpath_of
    (CrossCond.Staged.continuous_catN (CrossCond.Staged.continuous_stageDrv ℓ p.1)
      (CrossCond.Staged.stageDrv_zero ℓ p.1) ℓ)
  have hq0 : (0 : ℝ) ≤ q := NNReal.coe_nonneg _
  have hagree : EqOn Wα Wcat (Icc 0 q) := fun r hr => by
    simp only [hWαdef, hWcatdef, Ito.rpath]
    exact StagedDepth.IsGoodSched.joinW_eq_catN_stageDrv hgs hreg hn (Real.toNNReal_le_iff_le_coe.2 hr.2)
  have hHullF : recHull sc ℓ u = fwdHull Wα q := by
    rw [hudef, recHull_pastMap_eq_fwdHull]
    exact (YuanCorollary13.fwdHull_eq_of_eqOn_Icc hWα hWcat hq0 fun r hr => hagree hr).symm
  have hHull : recHull sc ℓ u = WangWu.seedLine (fun _ => ⊤) Wj p.1 '' Ioc 0 q := by
    rw [hHullF, fwdHull_eq_image_Ioc hα hαp hq0]
  -- the records give the switch times
  have hprog := isFlowProg_scheduleProgram 0 (scheduleList sc)
  have hrec : ∀ j : Fin ℓ, startT (recSeqT u) (j + 1) = τs (j + 1) := fun j => by
    rw [← hτs j]
    refine startT_congr fun i hi => ?_
    exact (StagedFinal.stage_records (κ := κ) (b := c₀.fn) (jumps := c₀.jumps) (spec := scheduleSpec sc) rfl
      hprog (schedDelta_ne_top 0 _) hn hgood (by omega)).1
  -- the restarted chart image of the avoidance domain
  have hτP : τ ∈ Pp := hpA.2
  set S₀ := s3Start s Wj Eg τ p with hS₀def
  set r := (capClock γ q).toNNReal - S₀ with hrdef
  have hsumle : S₀ ≤ (capClock γ q).toNNReal := by
    rw [hS₀def, s3Start_of_mem hpA]
    exact Real.toNNReal_le_toNNReal (hγ.strictMonoOn_capClock.monotoneOn hτP htP hτq)
  have hsum : S₀ + r = (capClock γ q).toNNReal := add_tsub_cancel_of_le hsumle
  have hr : ((S₀ + r : ℝ≥0) : WithTop ℝ≥0) < kLife γ Pp := by rw [hsum]; exact hγ.lt_kLife htP
  have hw' : ∀ v : ℝ≥0, ((S₀ + v : ℝ≥0) : WithTop ℝ≥0) < kLife γ Pp →
      s3W s Wj Eg τ v p = kW γ Pp (S₀ + v) - kW γ Pp S₀ := fun v hv =>
    Prop59Pieces.arcW_of_lt (Prop59Pieces.lt_arcζ_iff.2 ⟨mem_univ p, hv⟩)
  obtain ⟨himg, -⟩ := rChart_restart (isConformal_cfChart p.2) hγ hr hw' κ 0 (fun _ => 0)
  have hset : (s3Chart s Wj Eg τ p).2.1 '' (H \ fwdHull (fun x : ℝ => s3W s Wj Eg τ x.toNNReal p) r) =
      H \ (recHull sc ℓ u ∪ cfHullQ s p.2) := by
    rw [hHull]
    change (rChart (cfChart s p.2) γ Pp S₀).2.1 '' _ = _
    rw [himg, hsum, ← cfChart_inv_image_eq' hEg hpE htP]
    rfl
  have hφ : tsupport φ ⊆ H \ (recHull sc ℓ u ∪ cfHullQ s p.2) := hset ▸ hav.2
  -- DEPTH's identification at this sample
  obtain ⟨W'', hW'', -, hEq, hmain⟩ := hch hpE htP hφ
  have hVL := s3VL_sub_s3W (xL := xL) hEg hpA htP hτq hW'' hEq hτsτ
  have hVR := s3VR_sub_s3W (xR := xR) hEg hpA htP hτq hW'' hEq hτsτ
  obtain ⟨-, -, -, hEqk⟩ := s3_pre hEg hpA htP hτq hEq
  have hcq : 0 ≤ capClock γ q := hγ.capClock_nonneg htP
  have hsumR : ((S₀ + r : ℝ≥0) : ℝ) = capClock γ q := by rw [hsum, Real.coe_toNNReal _ hcq]
  have hEq' : EqOn (kPath γ Pp) W'' (Icc 0 ((S₀ + r : ℝ≥0) : ℝ)) := by rw [hsumR]; exact hEqk
  -- a bounded harmonic extension of the restarted word at `r`
  set ρL' := imgStageRhoL κ θ ρL (fun j => ang j - ang 0) ℓ with hρL'
  set ρR' := imgStageRhoR κ θ ρR (fun j => ang j - ang 0) ℓ with hρR'
  obtain ⟨v, hv⟩ := Sec4.exists_isBoundedHarmonicExtension_forceBoundaryData κ ρL' ρR'
    (fun i => s3VL xL τs ℓ s Wj Eg τ i r p - s3W s Wj Eg τ r p)
    (fun i => s3VR xR τs ℓ s Wj Eg τ i r p - s3W s Wj Eg τ r p)
  have hA := s3_switch hEg hpA hτsτ
  have hAA : ∀ j : Fin ℓ, capClock γ (τs (j + 1)) = capClock γ (startT (recSeqT u) (j + 1)) := fun j => by
    rw [hrec j]
  have hv' : IsBoundedHarmonicExtension (forceBoundaryData κ ρL' ρR'
      (imgStageVL xL (cfDrv0 s p.2) s W'' (capClock γ q) (fun m => capClock γ (startT (recSeqT u) m)) ℓ)
      (imgStageVR xR (cfDrv0 s p.2) s W'' (capClock γ q) (fun m => capClock γ (startT (recSeqT u) m)) ℓ))
      (forceJumpSet
        (imgStageVL xL (cfDrv0 s p.2) s W'' (capClock γ q) (fun m => capClock γ (startT (recSeqT u) m)) ℓ)
        (imgStageVR xR (cfDrv0 s p.2) s W'' (capClock γ q) (fun m => capClock γ (startT (recSeqT u) m)) ℓ))
      v := by
    rw [← imgStageVL_congr_A (A := fun m => capClock γ (τs m)) xL _ s hAA,
      ← imgStageVR_congr_A (A := fun m => capClock γ (τs m)) xR _ s hAA, ← hVL, ← hVR]
    exact hv
  have hm := hmain v hv'
  rw [hm]
  have hS₀q : (S₀ : ℝ) ≤ capClock γ q := by rw [← hsumR]; exact_mod_cast le_self_add
  -- the mean
  have hcont : ContinuousOn (fun t => s3W s Wj Eg τ t p) {t | (t : ℝ≥0∞) < s3ζ s Wj Eg τ p} :=
    Prop59Pieces.continuousOn_arcW (fun p => isKilledArc_gCurve hEg p) p
  have hord : ∀ i, s3VL xL τs ℓ s Wj Eg τ i r p ≤ s3W s Wj Eg τ r p := fun i => by
    have h1 := congrFun hVL i
    have h2 := imgStageVL_nonpos (A := fun m => capClock γ (τs m)) hW'' xL (cfDrv0 s p.2) s hcq
      (fun j => (hA j).2.trans hS₀q) i
    simp only at h1
    linarith
  have hordR : ∀ i, s3W s Wj Eg τ r p ≤ s3VR xR τs ℓ s Wj Eg τ i r p := fun i => by
    have h1 := congrFun hVR i
    have h2 := imgStageVR_nonneg (A := fun m => capClock γ (τs m)) hW'' xR (cfDrv0 s p.2) s hcq
      (fun j => (hA j).2.trans hS₀q) i
    simp only at h1
    linarith
  have hconf : (s3Chart s Wj Eg τ p).IsConformal :=
    isConformal_rChart (isConformal_cfChart p.2) hγ
      (lt_of_le_of_lt (WithTop.coe_le_coe.2 le_self_add) hr)
  have hcm := Sec7.Lemma71D.integral_couplingMean_eq_chartMean (κ := κ) (ρL := ρL') (ρR := ρR')
    (vL := fun i t => s3VL xL τs ℓ s Wj Eg τ i t p) (vR := fun i t => s3VR xR τs ℓ s Wj Eg τ i t p)
    (a := 2 * Real.pi * chiC κ + (ang ℓ - ang 0) * chiC κ) (k := chiC κ) hconf hcont hav hord hordR hv
  have hint := integral_rChart_eq hγ s p.2 hr hw' hEq' κ ((ang ℓ - ang 0) * chiC κ) v φ (hset ▸ hφ)
  rw [hsumR] at hint
  have hvar : QuantumZipper.zeroGFFTestCov (H \ relClosureH (recHull sc ℓ u ∪ cfHullQ s p.2)) φ φ =
      Sec7.Lemma71D.chartVar (fun t => s3W s Wj Eg τ t p) (s3Chart s Wj Eg τ p) φ r := by
    obtain ⟨hGH, hGo⟩ := cfHullQ_relClosed s p.2
    have hsub : recHull sc ℓ u ∪ cfHullQ s p.2 ⊆ H := by
      rw [hHullF]
      exact union_subset (fun z hz => hz.1) hGH
    have hopen : IsOpen (H \ (recHull sc ℓ u ∪ cfHullQ s p.2)) := by
      have e : H \ (recHull sc ℓ u ∪ cfHullQ s p.2) = (H \ recHull sc ℓ u) ∩ (H \ cfHullQ s p.2) := by
        ext z; simp only [Set.mem_sdiff, mem_inter_iff, mem_union]; tauto
      rw [e, hHullF]
      exact (QuantumZipper.FwdHolo.isOpen_compl_fwdHull hWα hq0).inter hGo
    rw [Sec7.Lemma71D.chartVar, relClosureH_eq hsub hopen]
    exact congrArg (fun S => QuantumZipper.zeroGFFTestCov S φ φ) hset.symm
  have hcm' : ∫ z, (couplingMean κ (fun x : ℝ => s3W s Wj Eg τ x.toNNReal p) (r : ℝ) v
        ((rChart (cfChart s p.2) γ Pp S₀).1 z) - (2 * Real.pi * chiC κ + (ang ℓ - ang 0) * chiC κ) -
        chiC κ * (rChart (cfChart s p.2) γ Pp S₀).2.2 z) * φ z =
      Sec7.Lemma71D.chartMean κ ρL' ρR' (fun t => s3W s Wj Eg τ t p) (fun i t => s3VL xL τs ℓ s Wj Eg τ i t p)
        (fun i t => s3VR xR τs ℓ s Wj Eg τ i t p) (s3Chart s Wj Eg τ p)
        (2 * Real.pi * chiC κ + (ang ℓ - ang 0) * chiC κ) (chiC κ) φ r := hcm
  rw [← hint, hcm', hvar, Complex.ofReal_exp, ← Complex.exp_add]
  congr 1
  push_cast
  ring

end Glued

end InteractingSLE.Sec5.CrossCond.StagedS3
