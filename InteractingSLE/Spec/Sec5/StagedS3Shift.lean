/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec5.StagedDepthChar
import InteractingSLE.Spec.Sec5.MarkovFlow
import InteractingSLE.Spec.Sec5.Prop59NodeTreeFlow
import InteractingSLE.Spec.Sec5.Prop59PiecesArc
import InteractingSLE.Spec.Sec7.LocalExtGChart

/-!
# Proposition 5.9 at depth `ℓ`, step S3: the image stage word restarted at the last switch (deterministic part)

Packet PROVE-STAGED-S3. After the last switch (own time `τ`, image capacity `S₀ = σ(τ)`) the image stage word is read
in the **restarted chart** `rChart c γ P S₀ = c.loewner (f_{S₀} of the killed image chain)`: its driver is
`u ↦ kW(S₀ + u) − kW(S₀)` and its marks are the real Loewner images, under the restarted driver, of the stage marks
at `S₀`. This file proves the deterministic identities that turn DEPTH's (SW3) formula at `T = S₀ + r` into the chart
clause of the restarted word:

* `rChart`, `isConformal_rChart`, **`rChart_restart`** (the image of the restarted hull complement and the coupling
  mean through the restarted chart, from `Markov.restart_path`);
* `relL_shift`, `relR_shift`, `chartAL_shift`, `chartAR_shift`, **`imgStageVL_shift`**, **`imgStageVR_shift`**
  (the stage marks restarted at `S` are the stage marks at `S + r`, by the flow property `rightImg_shiftDrv`),
  `imgStageVL_congr`, `imgStageVR_congr`;
* `realPath_arcW_eqOn`, **`arcVL_sub_arcW`**, **`arcVR_sub_arcW`** (PROVE-PROP59-PIECES' restarted arc marks relative
  to the restarted driver);
* **`integrand_rChart_eq`**, **`integral_rChart_eq`** (the restarted chart integrand with the constant
  `2πχ + (θ_ℓ − θ₀)χ` is (SW3)'s integrand at `T = S₀ + r`).

Conditional helpers with distinct names; they replace no source theorem. R48: nothing here uses Theorem 1.2/1.3,
`Theorem12ParamStatement`, `Theorem13Statement` or any `*_of_param`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology
open QuantumZipper (H fwdHull fwdMap fwdMapInv logDerivFwd chiC)
open scoped NNReal ENNReal

namespace InteractingSLE.Sec5.CrossCond.StagedS3

open WangWu WangWu.ImgWord

/-! ### The restarted chart of a killed arc -/

section Chart

variable {γ : ℝ → ℂ} {P : Set ℝ} {S₀ : ℝ≥0}

/-- **The restarted chart**: the chart `c` followed by the centred Loewner stage of the killed image chain up to the
capacity `S₀` (the driver clamped after `S₀`, so that it is continuous). -/
def rChart (c : Chart) (γ : ℝ → ℂ) (P : Set ℝ) (S₀ : ℝ≥0) : Chart :=
  c.loewner (Ito.clampDrv (kPath γ P) S₀) S₀

theorem continuousOn_kPath_Icc (hγ : IsKilledArc γ P) (hS : (S₀ : WithTop ℝ≥0) < kLife γ P) :
    ContinuousOn (kPath γ P) (Icc 0 S₀) := by
  obtain ⟨c, hc, w, hw, hEq⟩ := hγ.isLocCont S₀ hS
  exact hw.continuousOn.congr fun x hx => hEq ⟨hx.1, hx.2.trans hc.le⟩

theorem kPath_zero (hγ : IsKilledArc γ P) : kPath γ P 0 = 0 := by
  simp only [kPath, Real.toNNReal_zero, hγ.kW_zero]

theorem continuous_clampDrv_kPath (hγ : IsKilledArc γ P) (hS : (S₀ : WithTop ℝ≥0) < kLife γ P) :
    Continuous (Ito.clampDrv (kPath γ P) S₀) :=
  Ito.continuous_clampDrv S₀.coe_nonneg (continuousOn_kPath_Icc hγ hS)

theorem clampDrv_kPath_zero (hγ : IsKilledArc γ P) : Ito.clampDrv (kPath γ P) S₀ 0 = 0 := by
  rw [Ito.clampDrv_eqOn ⟨le_rfl, S₀.coe_nonneg⟩, kPath_zero hγ]

/-- The restarted chart is conformal. -/
theorem isConformal_rChart {c : Chart} (hc : c.IsConformal) (hγ : IsKilledArc γ P)
    (hS : (S₀ : WithTop ℝ≥0) < kLife γ P) : (rChart c γ P S₀).IsConformal :=
  hc.loewner (continuous_clampDrv_kPath hγ hS) (clampDrv_kPath_zero hγ) S₀.coe_nonneg

/-- A Loewner stage after a chart is the composition with the identity chart's stage. -/
theorem loewner_eq_trans (c : Chart) (W : ℝ → ℝ) (t : ℝ) : c.loewner W t = c.trans (Chart.id.loewner W t) := by
  unfold Chart.loewner Chart.trans Chart.id
  simp only [add_zero]

/-- **The restart identities through the restarted chart.** For a killed arc and `S₀ + r` before the terminal
capacity, let `w'` agree before the lifetime with the restarted killed driver `u ↦ kW(S₀ + u) − kW(S₀)`. Then the
restarted chart sends the complement of the restarted hull at `r` onto the `c`-preimage of the complement of the hull
at `S₀ + r`, and there the restarted coupling mean read through the restarted chart minus `χ` times its lift is the
coupling mean at `S₀ + r` read through `c` minus `χ` times the lift of `c`. -/
theorem rChart_restart {c : Chart} (hc : c.IsConformal) (hγ : IsKilledArc γ P) {r : ℝ≥0}
    (hr : ((S₀ + r : ℝ≥0) : WithTop ℝ≥0) < kLife γ P) {w' : ℝ≥0 → ℝ}
    (hw' : ∀ u : ℝ≥0, ((S₀ + u : ℝ≥0) : WithTop ℝ≥0) < kLife γ P → w' u = kW γ P (S₀ + u) - kW γ P S₀)
    (κ a : ℝ) (u : ℂ → ℝ) :
    (rChart c γ P S₀).2.1 '' (H \ fwdHull (fun s : ℝ => w' s.toNNReal) r) =
        c.2.1 '' (H \ fwdHull (kPath γ P) ((S₀ + r : ℝ≥0) : ℝ)) ∧
      ∀ z ∈ (rChart c γ P S₀).2.1 '' (H \ fwdHull (fun s : ℝ => w' s.toNNReal) r),
        couplingMean κ (fun s : ℝ => w' s.toNNReal) r u ((rChart c γ P S₀).1 z) - a -
            chiC κ * (rChart c γ P S₀).2.2 z =
          couplingMean κ (kPath γ P) ((S₀ + r : ℝ≥0) : ℝ) u (c.1 z) - a - chiC κ * c.2.2 z := by
  have hSl : (S₀ : WithTop ℝ≥0) < kLife γ P :=
    lt_of_le_of_lt (WithTop.coe_le_coe.2 (le_self_add)) hr
  have hw : ContinuousOn (kW γ P) {t : ℝ≥0 | (t : ℝ≥0∞) < Prop59Pieces.lifeE γ P} := hγ.continuousOn_kW
  obtain ⟨h1, h2⟩ := Markov.restart_path hw hγ.kW_zero (T := S₀) (r := r) hr κ u
  -- room after `S₀ + r`
  obtain ⟨t₂, hTr₂, ht₂ζ⟩ := ENNReal.lt_iff_exists_nnreal_btwn.1 (show ((S₀ + r : ℝ≥0) : ℝ≥0∞) <
    Prop59Pieces.lifeE γ P from hr)
  have hTr₂' : ((S₀ + r : ℝ≥0) : ℝ) < t₂ := by exact_mod_cast hTr₂
  have hr₂ : (r : ℝ) < t₂ - S₀ := by push_cast at hTr₂'; linarith
  have hS₂ : (S₀ : ℝ) < t₂ := by linarith [r.coe_nonneg]
  -- the restarted drivers agree
  have hagree : ∀ x ∈ Icc (0 : ℝ) (t₂ - S₀), w' x.toNNReal = kW γ P (S₀ + x.toNNReal) - kW γ P S₀ := by
    intro x hx
    refine hw' _ (lt_of_le_of_lt (WithTop.coe_le_coe.2 ?_) (show ((t₂ : ℝ≥0) : WithTop ℝ≥0) < kLife γ P from ht₂ζ))
    rw [← NNReal.coe_le_coe, NNReal.coe_add, Real.coe_toNNReal _ hx.1]
    linarith [hx.2]
  have hK' : fwdHull (fun s : ℝ => w' s.toNNReal) r =
      fwdHull (fun s : ℝ => kW γ P (S₀ + s.toNNReal) - kW γ P S₀) r :=
    fwdHull_eq_of_eqOn r.coe_nonneg hr₂ hagree
  have hcm : ∀ y, couplingMean κ (fun s : ℝ => w' s.toNNReal) r u y =
      couplingMean κ (fun s : ℝ => kW γ P (S₀ + s.toNNReal) - kW γ P S₀) r u y := fun y =>
    Markov.couplingMean_congr_of_eqOn (fun x hx => hagree x hx) r.coe_nonneg hr₂.le κ u y
  -- the chart
  have hcont₂ : ContinuousOn (kPath γ P) (Icc 0 t₂) := continuousOn_kPath_Icc hγ ht₂ζ
  have hid : Chart.id.loewner (Ito.clampDrv (kPath γ P) S₀) S₀ = Chart.id.loewner (kPath γ P) S₀ :=
    LocalExt.id_loewner_congr (continuous_clampDrv_kPath hγ hSl).continuousOn hcont₂ S₀.coe_nonneg hS₂
      Ito.clampDrv_eqOn
  have hrc : rChart c γ P S₀ = c.trans (Chart.id.loewner (kPath γ P) S₀) := by
    rw [rChart, loewner_eq_trans, hid]
  have hkp : (fun s : ℝ => kW γ P s.toNNReal) = kPath γ P := rfl
  rw [hkp] at h1 h2
  have himg : (rChart c γ P S₀).2.1 '' (H \ fwdHull (fun s : ℝ => w' s.toNNReal) r) =
      c.2.1 '' (H \ fwdHull (kPath γ P) ((S₀ + r : ℝ≥0) : ℝ)) := by
    rw [hrc, hK', ← h1]
    ext z
    simp only [mem_image]
    constructor
    · rintro ⟨v, hv, rfl⟩
      exact ⟨_, ⟨v, hv, rfl⟩, Chart.trans_inv _ _ _⟩
    · rintro ⟨_, ⟨v, hv, rfl⟩, rfl⟩
      exact ⟨v, hv, Chart.trans_inv _ _ _⟩
  refine ⟨himg, fun z hz => ?_⟩
  rw [himg] at hz
  obtain ⟨v, hv, rfl⟩ := hz
  have hcv : c.1 (c.2.1 v) = v := hc.2.2 v hv.1
  rw [← h1] at hv
  have key := h2 v hv
  rw [hrc, Chart.trans_fst, Chart.trans_lift, hcv, hcm]
  rw [← key]
  ring

end Chart

/-! ### The real flow restarted at an image time -/

section Flow

open MartChar.RealFlow Prop59NodeTree StagedFinal GlueImg
open QuantumZipper.RS (shiftDrive)

variable {w : ℝ → ℝ}

theorem shiftDrv_neg (w : ℝ → ℝ) (S : ℝ) : shiftDrv (fun s => -w s) S = fun r => -shiftDrv w S r := by
  funext r
  simp only [shiftDrv]
  ring

theorem shiftDrv_shiftDrive (w : ℝ → ℝ) (a S : ℝ) : shiftDrv (shiftDrive w a) (S - a) = shiftDrv w S := by
  funext r
  simp only [shiftDrv, shiftDrive]
  ring_nf

/-- **A left mark restarted at `S`**: its position relative to the driver after `r` more units of the restarted flow
is its relative position at `S + r`. -/
theorem relL_shift (hw : Continuous w) {S r : ℝ} (hS : 0 ≤ S) (hr : 0 ≤ r) (x : ℝ) :
    -rightImg (shiftDrv (fun s => -w s) S) (-(-rightImg (fun s => -w s) x S - w S)) r - shiftDrv w S r =
      -rightImg (fun s => -w s) x (S + r) - w (S + r) := by
  have h := rightImg_shiftDrv (w := fun s => -w s) hw.neg hS hr x
  have e : -(-rightImg (fun s => -w s) x S - w S) = rightImg (fun s => -w s) x S - (fun s => -w s) S := by ring
  rw [e, h]
  simp only [shiftDrv]
  ring

/-- **A right mark restarted at `S`.** -/
theorem relR_shift (hw : Continuous w) {S r : ℝ} (hS : 0 ≤ S) (hr : 0 ≤ r) (x : ℝ) :
    rightImg (shiftDrv w S) (rightImg w x S - w S) r - shiftDrv w S r = rightImg w x (S + r) - w (S + r) := by
  rw [rightImg_shiftDrv hw hS hr x]
  simp only [shiftDrv]
  ring

/-- **A left born mark restarted at `S`** (born at `a ≤ S`). -/
theorem chartAL_shift (hw : Continuous w) {a S r : ℝ} (ha : a ≤ S) (hr : 0 ≤ r) :
    -rightImg (shiftDrv (fun s => -w s) S) (-chartAL (shiftDrive w a) (S - a)) r - shiftDrv w S r =
      chartAL (shiftDrive w a) (S + r - a) := by
  have hv : Continuous (shiftDrive w a) := QuantumZipper.RS.continuous_shiftDrive hw a
  have h := relL_shift hv (sub_nonneg.2 ha) hr 0
  have hneg : shiftDrv (fun s => -shiftDrive w a s) (S - a) = shiftDrv (fun s => -w s) S := by
    rw [shiftDrv_neg, shiftDrv_neg, shiftDrv_shiftDrive]
  rw [hneg, shiftDrv_shiftDrive] at h
  rw [show S + r - a = S - a + r by ring]
  simp only [chartAL]
  rw [← h]

/-- **A right born mark restarted at `S`** (born at `a ≤ S`). -/
theorem chartAR_shift (hw : Continuous w) {a S r : ℝ} (ha : a ≤ S) (hr : 0 ≤ r) :
    rightImg (shiftDrv w S) (chartAR (shiftDrive w a) (S - a)) r - shiftDrv w S r =
      chartAR (shiftDrive w a) (S + r - a) := by
  have hv : Continuous (shiftDrive w a) := QuantumZipper.RS.continuous_shiftDrive hw a
  have h := relR_shift hv (sub_nonneg.2 ha) hr 0
  rw [shiftDrv_shiftDrive] at h
  rw [show S + r - a = S - a + r by ring]
  simp only [chartAR]
  rw [← h]

/-- **The left marks of the image stage word restarted at `S`** (all switches born before `S`): after `r` more units
of the restarted flow their positions relative to the driver are those of the stage word at `S + r`. -/
theorem imgStageVL_shift {nL : ℕ} (hw : Continuous w) (xL : Fin nL → ℝ) (ω : ℝ → ℝ) (s : ℝ) {S r : ℝ}
    {A : ℕ → ℝ} {ℓ : ℕ} (hA : ∀ j : Fin ℓ, A (j + 1) ≤ S) (hS : 0 ≤ S) (hr : 0 ≤ r) (i : Fin (ℓ + (nL + 1))) :
    -rightImg (shiftDrv (fun s => -w s) S) (-imgStageVL xL ω s w S A ℓ i) r - shiftDrv w S r =
      imgStageVL xL ω s w (S + r) A ℓ i := by
  refine Fin.addCases (fun j => ?_) (fun k => ?_) i
  · simp only [imgStageVL, Fin.append_left, imgBornL]
    exact chartAL_shift hw (hA j) hr
  · simp only [imgStageVL, Fin.append_right, rootVL]
    have h := relL_shift hw hS hr (-imgMarkL xL ω s k)
    rw [← h]

/-- **The right marks of the image stage word restarted at `S`.** -/
theorem imgStageVR_shift {nR : ℕ} (hw : Continuous w) (xR : Fin nR → ℝ) (ω : ℝ → ℝ) (s : ℝ) {S r : ℝ}
    {A : ℕ → ℝ} {ℓ : ℕ} (hA : ∀ j : Fin ℓ, A (j + 1) ≤ S) (hS : 0 ≤ S) (hr : 0 ≤ r) (i : Fin (ℓ + (nR + 1))) :
    rightImg (shiftDrv w S) (imgStageVR xR ω s w S A ℓ i) r - shiftDrv w S r =
      imgStageVR xR ω s w (S + r) A ℓ i := by
  refine Fin.addCases (fun j => ?_) (fun k => ?_) i
  · simp only [imgStageVR, Fin.append_left, imgBornR]
    exact chartAR_shift hw (hA j) hr
  · simp only [imgStageVR, Fin.append_right, rootVR]
    exact relR_shift hw hS hr _

/-- The left marks of the image stage word at `T` only depend on the driver on `[0, T]`. -/
theorem imgStageVL_congr {nL : ℕ} {w w' : ℝ → ℝ} (hw' : Continuous w') {T : ℝ} (h : EqOn w w' (Icc 0 T))
    (xL : Fin nL → ℝ) (ω : ℝ → ℝ) (s : ℝ) {A : ℕ → ℝ} {ℓ : ℕ}
    (hA : ∀ j : Fin ℓ, 0 ≤ A (j + 1) ∧ A (j + 1) ≤ T) (hT : 0 ≤ T) :
    imgStageVL xL ω s w T A ℓ = imgStageVL xL ω s w' T A ℓ := by
  funext i
  refine Fin.addCases (fun j => ?_) (fun k => ?_) i
  · simp only [imgStageVL, Fin.append_left, imgBornL, chartAL]
    obtain ⟨ha0, haT⟩ := hA j
    have hE : EqOn (shiftDrive w (A (j + 1))) (shiftDrive w' (A (j + 1))) (Icc 0 (T - A (j + 1))) := by
      intro x hx
      simp only [shiftDrive]
      rw [h ⟨by linarith [hx.1], by linarith [hx.2]⟩, h ⟨ha0, haT⟩]
    have hc : Continuous fun x => -shiftDrive w' (A (j + 1)) x :=
      (QuantumZipper.RS.continuous_shiftDrive hw' _).neg
    rw [Sec7.Lemma71B.rightImg_congr hc (sub_nonneg.2 haT) (fun x hx => by simp only [hE hx]),
      hE ⟨sub_nonneg.2 haT, le_rfl⟩]
  · simp only [imgStageVL, Fin.append_right, rootVL]
    rw [Sec7.Lemma71B.rightImg_congr hw'.neg hT (fun x hx => by simp only [Pi.neg_apply, h hx]),
      h ⟨hT, le_rfl⟩]
    rfl

/-- The right marks of the image stage word at `T` only depend on the driver on `[0, T]`. -/
theorem imgStageVR_congr {nR : ℕ} {w w' : ℝ → ℝ} (hw' : Continuous w') {T : ℝ} (h : EqOn w w' (Icc 0 T))
    (xR : Fin nR → ℝ) (ω : ℝ → ℝ) (s : ℝ) {A : ℕ → ℝ} {ℓ : ℕ}
    (hA : ∀ j : Fin ℓ, 0 ≤ A (j + 1) ∧ A (j + 1) ≤ T) (hT : 0 ≤ T) :
    imgStageVR xR ω s w T A ℓ = imgStageVR xR ω s w' T A ℓ := by
  funext i
  refine Fin.addCases (fun j => ?_) (fun k => ?_) i
  · simp only [imgStageVR, Fin.append_left, imgBornR, chartAR]
    obtain ⟨ha0, haT⟩ := hA j
    have hE : EqOn (shiftDrive w (A (j + 1))) (shiftDrive w' (A (j + 1))) (Icc 0 (T - A (j + 1))) := by
      intro x hx
      simp only [shiftDrive]
      rw [h ⟨by linarith [hx.1], by linarith [hx.2]⟩, h ⟨ha0, haT⟩]
    have hc : Continuous (shiftDrive w' (A (j + 1))) := QuantumZipper.RS.continuous_shiftDrive hw' _
    rw [Sec7.Lemma71B.rightImg_congr hc (sub_nonneg.2 haT) hE, hE ⟨sub_nonneg.2 haT, le_rfl⟩]
  · simp only [imgStageVR, Fin.append_right, rootVR]
    rw [Sec7.Lemma71B.rightImg_congr hw' hT h, h ⟨hT, le_rfl⟩]

end Flow

/-! ### The restarted marks of a killed family -/

section Arc

open MartChar.RealFlow Prop59NodeTree Prop59Pieces

variable {Ω : Type*} {nL nR : ℕ} {γ : Ω → ℝ → ℂ} {P : Ω → Set ℝ} {S₀ : Ω → ℝ≥0} {Al : Set Ω}

/-- On the alive event before the lifetime, the restarted driver read on `ℝ` is the shifted driver of any continuous
extension of the killed chain driver. -/
theorem realPath_arcW_eqOn {ω : Ω} (hω : ω ∈ Al) {r : ℝ≥0}
    (hr : ((S₀ ω + r : ℝ≥0) : WithTop ℝ≥0) < kLife (γ ω) (P ω)) {w : ℝ → ℝ}
    (hEq : EqOn (kPath (γ ω) (P ω)) w (Icc 0 ((S₀ ω + r : ℝ≥0) : ℝ))) :
    EqOn (Bessel.realPath (arcW γ P S₀ Al) ω) (shiftDrv w (S₀ ω)) (Icc 0 r) := by
  intro t ht
  have htr : t.toNNReal ≤ r := by rw [Real.toNNReal_le_iff_le_coe]; exact ht.2
  have hlt : ((t.toNNReal : ℝ≥0) : ℝ≥0∞) < arcζ γ P S₀ Al ω := by
    rw [lt_arcζ_iff]
    exact ⟨hω, lt_of_le_of_lt (WithTop.coe_le_coe.2 (add_le_add_right htr _)) hr⟩
  have hmem : ∀ x : ℝ≥0, x ≤ S₀ ω + r → (x : ℝ) ∈ Icc 0 ((S₀ ω + r : ℝ≥0) : ℝ) := fun x hx =>
    ⟨x.coe_nonneg, by exact_mod_cast hx⟩
  simp only [Bessel.realPath, shiftDrv]
  rw [arcW_of_lt hlt, ← kPath_coe, ← kPath_coe, hEq (hmem _ (add_le_add_right htr _)),
    hEq (hmem _ le_self_add)]
  congr 1
  push_cast
  rw [Real.coe_toNNReal _ ht.1]

/-- **The restarted left marks relative to the restarted driver**, through a continuous extension of the driver. -/
theorem arcVL_sub_arcW {xL : Ω → Fin nL → ℝ} {ω : Ω} (hω : ω ∈ Al) {r : ℝ≥0}
    (hr : ((S₀ ω + r : ℝ≥0) : WithTop ℝ≥0) < kLife (γ ω) (P ω)) {w : ℝ → ℝ} (hw : Continuous w)
    (hEq : EqOn (kPath (γ ω) (P ω)) w (Icc 0 ((S₀ ω + r : ℝ≥0) : ℝ))) (i : Fin nL) :
    arcVL γ P S₀ Al xL i r ω - arcW γ P S₀ Al r ω =
      -rightImg (shiftDrv (fun s => -w s) (S₀ ω)) (-xL ω i) r - shiftDrv w (S₀ ω) r := by
  have hlt : ((r : ℝ≥0) : ℝ≥0∞) < arcζ γ P S₀ Al ω := lt_arcζ_iff.2 ⟨hω, hr⟩
  have hE := realPath_arcW_eqOn hω hr hEq
  have hW : arcW γ P S₀ Al r ω = shiftDrv w (S₀ ω) r := by
    have := hE ⟨r.coe_nonneg, le_rfl⟩
    simpa only [Bessel.realPath, Real.toNNReal_coe] using this
  have hc : Continuous (shiftDrv (fun s => -w s) (S₀ ω)) := continuous_shiftDrv hw.neg _
  simp only [arcVL, hlt, ↓reduceIte]
  rw [hW]
  congr 2
  refine Sec7.Lemma71B.rightImg_congr hc r.coe_nonneg (fun t ht => ?_) _
  have := hE ht
  simp only [Bessel.realPath] at this ⊢
  rw [this, shiftDrv_neg]

/-- **The restarted right marks relative to the restarted driver.** -/
theorem arcVR_sub_arcW {xR : Ω → Fin nR → ℝ} {ω : Ω} (hω : ω ∈ Al) {r : ℝ≥0}
    (hr : ((S₀ ω + r : ℝ≥0) : WithTop ℝ≥0) < kLife (γ ω) (P ω)) {w : ℝ → ℝ} (hw : Continuous w)
    (hEq : EqOn (kPath (γ ω) (P ω)) w (Icc 0 ((S₀ ω + r : ℝ≥0) : ℝ))) (k : Fin nR) :
    arcVR γ P S₀ Al xR k r ω - arcW γ P S₀ Al r ω =
      rightImg (shiftDrv w (S₀ ω)) (xR ω k) r - shiftDrv w (S₀ ω) r := by
  have hlt : ((r : ℝ≥0) : ℝ≥0∞) < arcζ γ P S₀ Al ω := lt_arcζ_iff.2 ⟨hω, hr⟩
  have hE := realPath_arcW_eqOn hω hr hEq
  have hW : arcW γ P S₀ Al r ω = shiftDrv w (S₀ ω) r := by
    have := hE ⟨r.coe_nonneg, le_rfl⟩
    simpa only [Bessel.realPath, Real.toNNReal_coe] using this
  have hc : Continuous (shiftDrv w (S₀ ω)) := continuous_shiftDrv hw _
  simp only [arcVR, hlt, ↓reduceIte]
  rw [hW, Sec7.Lemma71B.rightImg_congr hc r.coe_nonneg hE]

end Arc

/-! ### The restarted chart mean is the staged mean read in the counterflow chart -/

section Ident

open Word49 GlueImg LawUnique

variable {γ : ℝ → ℂ} {P : Set ℝ} {S₀ : ℝ≥0}

/-- **The integrand of the restarted chart clause is the integrand of (SW3)** (Astra's follow-up 4 §3, read after the
last switch): for `z` in the restarted chart image of the complement of the restarted hull at `r`, the restarted
coupling mean through the restarted chart, minus the constant `2πχ + c` and `χ` times the chart's lift, is
`(u ∘ f_T ∘ Ψ − c) − χ (arg f_T′ ∘ Ψ + arg Ψ′)` at `T = S₀ + r`, for any continuous extension `W''` of the chain
driver. -/
theorem integrand_rChart_eq (hγ : IsKilledArc γ P) (s : ℝ≥0) (y : HistorySpace 0 0) {r : ℝ≥0}
    (hr : ((S₀ + r : ℝ≥0) : WithTop ℝ≥0) < kLife γ P) {w' : ℝ≥0 → ℝ}
    (hw' : ∀ u : ℝ≥0, ((S₀ + u : ℝ≥0) : WithTop ℝ≥0) < kLife γ P → w' u = kW γ P (S₀ + u) - kW γ P S₀)
    {W'' : ℝ → ℝ} (hEq : EqOn (kPath γ P) W'' (Icc 0 ((S₀ + r : ℝ≥0) : ℝ))) (κ c : ℝ) (u : ℂ → ℝ) {z : ℂ}
    (hz : z ∈ (rChart (cfChart s y) γ P S₀).2.1 '' (H \ fwdHull (fun x : ℝ => w' x.toNNReal) r)) :
    couplingMean κ (fun x : ℝ => w' x.toNNReal) r u ((rChart (cfChart s y) γ P S₀).1 z) -
        (2 * Real.pi * chiC κ + c) - chiC κ * (rChart (cfChart s y) γ P S₀).2.2 z =
      (u (fwdMap W'' ((S₀ + r : ℝ≥0) : ℝ) (revChart (cfDrv0 s y) s z)) - c) -
        chiC κ * ((logDerivFwd W'' ((S₀ + r : ℝ≥0) : ℝ) (revChart (cfDrv0 s y) s z)).im +
          (logDerivPsi (cfDrv0 s y) s z).im) := by
  obtain ⟨-, h2⟩ := rChart_restart (isConformal_cfChart y) hγ hr hw' κ (2 * Real.pi * chiC κ + c) u
  rw [h2 z hz]
  unfold couplingMean
  have hT : (0 : ℝ) ≤ ((S₀ + r : ℝ≥0) : ℝ) := NNReal.coe_nonneg _
  rw [fwdMap_eq_of_eqOn hT fun x hx => hEq hx, Ito.logDerivFwd_congr_of_eqOn hEq hT le_rfl, cfChart_fst,
    cfChart_lift, im_logDerivPsi_eq]
  ring

/-- **The integral form**: when `supp φ` lies in the restarted chart image of the complement of the restarted hull. -/
theorem integral_rChart_eq (hγ : IsKilledArc γ P) (s : ℝ≥0) (y : HistorySpace 0 0) {r : ℝ≥0}
    (hr : ((S₀ + r : ℝ≥0) : WithTop ℝ≥0) < kLife γ P) {w' : ℝ≥0 → ℝ}
    (hw' : ∀ u : ℝ≥0, ((S₀ + u : ℝ≥0) : WithTop ℝ≥0) < kLife γ P → w' u = kW γ P (S₀ + u) - kW γ P S₀)
    {W'' : ℝ → ℝ} (hEq : EqOn (kPath γ P) W'' (Icc 0 ((S₀ + r : ℝ≥0) : ℝ))) (κ c : ℝ) (u : ℂ → ℝ)
    (φ : LQGMetric.TestOn upperHalfPlaneOpens)
    (hφ : tsupport φ ⊆ (rChart (cfChart s y) γ P S₀).2.1 '' (H \ fwdHull (fun x : ℝ => w' x.toNNReal) r)) :
    ∫ z, (couplingMean κ (fun x : ℝ => w' x.toNNReal) r u ((rChart (cfChart s y) γ P S₀).1 z) -
        (2 * Real.pi * chiC κ + c) - chiC κ * (rChart (cfChart s y) γ P S₀).2.2 z) * φ z =
      ∫ z, ((u (fwdMap W'' ((S₀ + r : ℝ≥0) : ℝ) (revChart (cfDrv0 s y) s z)) - c) -
        chiC κ * ((logDerivFwd W'' ((S₀ + r : ℝ≥0) : ℝ) (revChart (cfDrv0 s y) s z)).im +
          (logDerivPsi (cfDrv0 s y) s z).im)) * φ z := by
  refine integral_congr_ae (ae_of_all _ fun z => ?_)
  by_cases hz : z ∈ tsupport φ
  · simp only
    rw [integrand_rChart_eq hγ s y hr hw' hEq κ c u (hφ hz)]
  · simp only [image_eq_zero_of_notMem_tsupport hz, mul_zero]

end Ident

end InteractingSLE.Sec5.CrossCond.StagedS3
