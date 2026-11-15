/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec5.StagedS5Marks

/-!
# The restarted word on the glued space and on good stopped data

Packet PROVE-STAGED-S5 ((M3) of `planning/handoffs/PROVE-STAGED-S3.md` §5.2).

* **Glued space** (ambient measurability): PROVE-STAGED-S3's initial marks `s3XL`/`s3XR` are, on the alive event, the
  arc-piece stage marks of `StagedS5Marks` (`s3XL_eq_ite`), hence measurable (`measurable_s3XL`); the restarted
  processes `s3W`, `s3VL`, `s3VR`, the lifetime `s3ζ` and the restarted chart `s3Chart` (`isMeasChart_s3Chart`) are
  measurable.
* **Good stopped data** `XD s q = {y : Y49 0 0 // IsGoodD s q y}`: the same construction for the stopped killed family
  `(gammaD, PD q)` (`s5W`, `s5VL`, `s5VR`, `s5ζ`, `s5Chart`), with its measurability (`measurable_s5XL`,
  `isMeasChart_s5Chart`) and the window `s5Win` of the Galmarino filtration (`measurableSet_s5Win`).

Conditional helpers with distinct names; R48: nothing here uses Theorem 1.2/1.3.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology Metric
open scoped NNReal ENNReal
open QuantumZipper (H fwdHull)

namespace InteractingSLE.Sec5.CrossCond.StagedS5

open WangWu WangWu.ImgWord Coupling StagedS3 StagedFinal Word49 LawUnique
open Prop59Pieces (arcW arcVL arcVR arcζ IsKilledFamily)
open Sec7.Lemma71C (capClock)

/-! ### The glued space -/

section Glued

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {𝓕 : Filtration ℝ≥0 mΩ} {s : ℝ≥0} {Wj : ℝ≥0 → Ω → ℝ}
  {E : Set (Ω × HistorySpace 0 0)} {nL nR : ℕ}

omit mΩ in
theorem s3Start_lt_kLife' (hEg : ∀ p ∈ E, IsGood49 s (fun _ => ⊤) Wj p) (τ : ℝ) (p : Ω × HistorySpace 0 0) :
    ((s3Start s Wj E τ p : ℝ≥0) : WithTop ℝ≥0) < kLife (gCurve s (fun _ => ⊤) Wj E p) (gPre s (fun _ => ⊤) Wj E p) := by
  classical
  by_cases hp : p ∈ s3Alive s Wj E τ
  · exact StagedS4.s3Start_lt_kLife hEg hp
  · have h0 : s3Start s Wj E τ p = 0 := by simp only [s3Start, hp, ↓reduceIte]
    rw [h0]
    exact (isKilledArc_gCurve hEg p).zero_lt_kLife

omit mΩ in
open scoped Classical in
/-- **The initial left marks are the arc-piece stage marks on the alive event.** -/
theorem s3XL_eq_ite (hEg : ∀ p ∈ E, IsGood49 s (fun _ => ⊤) Wj p) (xL : Fin nL → ℝ) {τ : ℚ} {τs : ℕ → ℝ}
    {τq : ℕ → ℚ} {ℓ : ℕ} (hτs : ∀ j : Fin ℓ, 0 ≤ τs (j + 1) ∧ τs (j + 1) ≤ τ)
    (hτq : ∀ j : Fin ℓ, τs (j + 1) = τq (j + 1)) :
    s3XL xL τs ℓ s Wj E τ = fun p => if p ∈ s3Alive s Wj E τ then
      stageArcL (gCurve s (fun _ => ⊤) Wj E) (gPre s (fun _ => ⊤) Wj E)
        (fun m => capQ (gCurve s (fun _ => ⊤) Wj E) (gPre s (fun _ => ⊤) Wj E) (τq m)) (s3Start s Wj E τ)
        (Word49.gXL xL s E) ℓ p else 0 := by
  funext p
  by_cases hp : p ∈ s3Alive s Wj E τ
  · have hγ := isKilledArc_gCurve hEg p
    have hmem : ∀ j : Fin ℓ, (τq (j + 1) : ℝ) ∈ gPre s (fun _ => ⊤) Wj E p := fun j => by
      rw [← hτq j]
      exact hγ.icc _ hp.2 (hτs j)
    simp only [s3XL, hp, ↓reduceIte]
    symm
    refine stageArcL_eq hγ (StagedS4.s3Start_lt_kLife hEg hp) (fun j => ?_) xL (cfDrv0 s p.2) s ?_ (fun j => ?_)
    · rw [← NNReal.coe_le_coe, coe_capQ hγ (hmem j), ← hτq j]
      exact (s3_switch hEg hp hτs j).2
    · simp only [Word49.gXL, hp.1, ↓reduceIte]
    · rw [coe_capQ hγ (hmem j), ← hτq j]
  · simp only [s3XL, hp, ↓reduceIte]

omit mΩ in
open scoped Classical in
theorem s3XR_eq_ite (hEg : ∀ p ∈ E, IsGood49 s (fun _ => ⊤) Wj p) (xR : Fin nR → ℝ) {τ : ℚ} {τs : ℕ → ℝ}
    {τq : ℕ → ℚ} {ℓ : ℕ} (hτs : ∀ j : Fin ℓ, 0 ≤ τs (j + 1) ∧ τs (j + 1) ≤ τ)
    (hτq : ∀ j : Fin ℓ, τs (j + 1) = τq (j + 1)) :
    s3XR xR τs ℓ s Wj E τ = fun p => if p ∈ s3Alive s Wj E τ then
      stageArcR (gCurve s (fun _ => ⊤) Wj E) (gPre s (fun _ => ⊤) Wj E)
        (fun m => capQ (gCurve s (fun _ => ⊤) Wj E) (gPre s (fun _ => ⊤) Wj E) (τq m)) (s3Start s Wj E τ)
        (Word49.gXR xR s E) ℓ p else 0 := by
  funext p
  by_cases hp : p ∈ s3Alive s Wj E τ
  · have hγ := isKilledArc_gCurve hEg p
    have hmem : ∀ j : Fin ℓ, (τq (j + 1) : ℝ) ∈ gPre s (fun _ => ⊤) Wj E p := fun j => by
      rw [← hτq j]
      exact hγ.icc _ hp.2 (hτs j)
    simp only [s3XR, hp, ↓reduceIte]
    symm
    refine stageArcR_eq hγ (StagedS4.s3Start_lt_kLife hEg hp) (fun j => ?_) xR (cfDrv0 s p.2) s ?_ (fun j => ?_)
    · rw [← NNReal.coe_le_coe, coe_capQ hγ (hmem j), ← hτq j]
      exact (s3_switch hEg hp hτs j).2
    · simp only [Word49.gXR, hp.1, ↓reduceIte]
    · rw [coe_capQ hγ (hmem j), ← hτq j]
  · simp only [s3XR, hp, ↓reduceIte]

variable (hW : AdaptedBefore 𝓕 (fun _ => ⊤) Wj) (hE : MeasurableSet E)
  (hEg : ∀ p ∈ E, IsGood49 s (fun _ => ⊤) Wj p)
include hW hE hEg

theorem measurable_s3XL (xL : Fin nL → ℝ) {τ : ℚ} {τs : ℕ → ℝ} {τq : ℕ → ℚ} {ℓ : ℕ}
    (hτs : ∀ j : Fin ℓ, 0 ≤ τs (j + 1) ∧ τs (j + 1) ≤ τ) (hτq : ∀ j : Fin ℓ, τs (j + 1) = τq (j + 1)) :
    Measurable (s3XL xL τs ℓ s Wj E τ) := by
  classical
  have hF := StagedS4.isKilledFamily_gCurve hW hE hEg
  rw [s3XL_eq_ite hEg xL hτs hτq]
  exact Measurable.ite (StagedS4.measurableSet_s3Alive hW hE hEg τ)
    (measurable_stageArcL hF (fun m => measurable_capQ hF _) (StagedS4.measurable_s3Start hW hE hEg τ)
      (measurable_gXL xL hE) ℓ) measurable_const

theorem measurable_s3XR (xR : Fin nR → ℝ) {τ : ℚ} {τs : ℕ → ℝ} {τq : ℕ → ℚ} {ℓ : ℕ}
    (hτs : ∀ j : Fin ℓ, 0 ≤ τs (j + 1) ∧ τs (j + 1) ≤ τ) (hτq : ∀ j : Fin ℓ, τs (j + 1) = τq (j + 1)) :
    Measurable (s3XR xR τs ℓ s Wj E τ) := by
  classical
  have hF := StagedS4.isKilledFamily_gCurve hW hE hEg
  rw [s3XR_eq_ite hEg xR hτs hτq]
  exact Measurable.ite (StagedS4.measurableSet_s3Alive hW hE hEg τ)
    (measurable_stageArcR hF (fun m => measurable_capQ hF _) (StagedS4.measurable_s3Start hW hE hEg τ)
      (measurable_gXR xR hE) ℓ) measurable_const

theorem measurable_s3ζ (τ : ℚ) : Measurable (s3ζ s Wj E τ) :=
  Prop59Pieces.measurable_arcζ (StagedS4.isKilledFamily_gCurve hW hE hEg) (StagedS4.measurable_s3Start hW hE hEg τ)
    MeasurableSet.univ

theorem measurable_s3W (τ : ℚ) (u : ℝ≥0) : Measurable (s3W s Wj E τ u) :=
  Prop59Pieces.measurable_arcW (StagedS4.isKilledFamily_gCurve hW hE hEg) (StagedS4.measurable_s3Start hW hE hEg τ)
    MeasurableSet.univ u

theorem measurable_s3VL (xL : Fin nL → ℝ) {τ : ℚ} {τs : ℕ → ℝ} {τq : ℕ → ℚ} {ℓ : ℕ}
    (hτs : ∀ j : Fin ℓ, 0 ≤ τs (j + 1) ∧ τs (j + 1) ≤ τ) (hτq : ∀ j : Fin ℓ, τs (j + 1) = τq (j + 1))
    (i : Fin (ℓ + (nL + 1))) (u : ℝ≥0) : Measurable (s3VL xL τs ℓ s Wj E τ i u) :=
  (Prop59Pieces.measurable_uncurry_arcVL (StagedS4.isKilledFamily_gCurve hW hE hEg)
    (StagedS4.measurable_s3Start hW hE hEg τ) MeasurableSet.univ (measurable_s3XL hW hE hEg xL hτs hτq) i).comp
    (measurable_const.prodMk measurable_id)

theorem measurable_s3VR (xR : Fin nR → ℝ) {τ : ℚ} {τs : ℕ → ℝ} {τq : ℕ → ℚ} {ℓ : ℕ}
    (hτs : ∀ j : Fin ℓ, 0 ≤ τs (j + 1) ∧ τs (j + 1) ≤ τ) (hτq : ∀ j : Fin ℓ, τs (j + 1) = τq (j + 1))
    (i : Fin (ℓ + (nR + 1))) (u : ℝ≥0) : Measurable (s3VR xR τs ℓ s Wj E τ i u) :=
  (Prop59Pieces.measurable_uncurry_arcVR (StagedS4.isKilledFamily_gCurve hW hE hEg)
    (StagedS4.measurable_s3Start hW hE hEg τ) MeasurableSet.univ (measurable_s3XR hW hE hEg xR hτs hτq) i).comp
    (measurable_const.prodMk measurable_id)

/-- **The restarted chart on the glued space has measurable data.** -/
theorem isMeasChart_s3Chart (τ : ℚ) :
    IsMeasChart (inferInstance : MeasurableSpace (Ω × HistorySpace 0 0)) (s3Chart s Wj E τ) := by
  have hc : IsMeasChart (inferInstance : MeasurableSpace (Ω × HistorySpace 0 0)) fun p => cfChart s p.2 :=
    isMeasChart_cfChart (Y := Prod.snd) ((GlueCond.measurable_cfStop s).comp measurable_snd)
  exact isMeasChart_rChart (StagedS4.isKilledFamily_gCurve hW hE hEg) (StagedS4.measurable_s3Start hW hE hEg τ)
    (s3Start_lt_kLife' hEg τ) hc

end Glued

/-! ### Good stopped data -/

section Stopped

/-- The good stopped data at the own time `q`. -/
abbrev XD (s : ℝ≥0) (q : ℚ) : Type := {y : Y49 0 0 // IsGoodD s q y}

variable {s : ℝ≥0} {q : ℚ} {nL nR : ℕ}

/-- The stopped image curve. -/
def s5γ (s : ℝ≥0) (q : ℚ) : XD s q → ℝ → ℂ := fun x => gammaD s x.1

/-- The stopped pre-contact times before `q`. -/
def s5P (s : ℝ≥0) (q : ℚ) : XD s q → Set ℝ := fun x => PD q s x.1

theorem isKilledFamily_s5 : IsKilledFamily (s5γ s q) (s5P s q) :=
  ⟨fun x => x.2.killed, fun u => measurableSet_mem_PD u, fun u => measurable_indicator_capClock_gammaD_PD u,
    fun u => (measurable_gammaD (u : ℝ)).comp measurable_subtype_coe⟩

/-- The stopped alive event: the last switch `τ` before the contact (and before `q`). -/
def s5Alive (s : ℝ≥0) (q τ : ℚ) : Set (XD s q) := {x | (τ : ℝ) ∈ s5P s q x}

/-- The stopped restart capacity. -/
def s5S₀ (s : ℝ≥0) (q τ : ℚ) : XD s q → ℝ≥0 := capQ (s5γ s q) (s5P s q) τ

theorem measurableSet_s5Alive (τ : ℚ) : MeasurableSet (s5Alive s q τ) := measurableSet_mem_PD τ

theorem measurable_s5S₀ (τ : ℚ) : Measurable (s5S₀ s q τ) := measurable_capQ isKilledFamily_s5 τ

theorem s5S₀_of_alive {τ : ℚ} {x : XD s q} (hx : x ∈ s5Alive s q τ) :
    s5S₀ s q τ x = (capClock (s5γ s q x) τ).toNNReal := by
  rw [s5S₀, capQ, indicator_of_mem (show x ∈ {x | (τ : ℝ) ∈ s5P s q x} from hx)]

theorem s5S₀_of_not_alive {τ : ℚ} {x : XD s q} (hx : x ∉ s5Alive s q τ) : s5S₀ s q τ x = 0 := by
  rw [s5S₀, capQ, indicator_of_notMem (show x ∉ {x | (τ : ℝ) ∈ s5P s q x} from hx), Real.toNNReal_zero]

theorem s5S₀_lt_kLife (τ : ℚ) (x : XD s q) :
    ((s5S₀ s q τ x : ℝ≥0) : WithTop ℝ≥0) < kLife (s5γ s q x) (s5P s q x) := by
  by_cases hx : x ∈ s5Alive s q τ
  · rw [s5S₀_of_alive hx]
    exact x.2.killed.lt_kLife hx
  · rw [s5S₀_of_not_alive hx]
    exact x.2.killed.zero_lt_kLife

open scoped Classical in
/-- The stopped initial left marks (the image stage marks of the stopped data at the restart capacity). -/
def s5XL (xL : Fin nL → ℝ) (τs : ℕ → ℝ) (ℓ : ℕ) (s : ℝ≥0) (q τ : ℚ) (x : XD s q) : Fin (ℓ + (nL + 1)) → ℝ :=
  if x ∈ s5Alive s q τ then
    imgStageVL xL (cfDrv0 s x.1.2) s (kPath (s5γ s q x) (s5P s q x)) (s5S₀ s q τ x)
      (fun m => capClock (s5γ s q x) (τs m)) ℓ
  else 0

open scoped Classical in
/-- The stopped initial right marks. -/
def s5XR (xR : Fin nR → ℝ) (τs : ℕ → ℝ) (ℓ : ℕ) (s : ℝ≥0) (q τ : ℚ) (x : XD s q) : Fin (ℓ + (nR + 1)) → ℝ :=
  if x ∈ s5Alive s q τ then
    imgStageVR xR (cfDrv0 s x.1.2) s (kPath (s5γ s q x) (s5P s q x)) (s5S₀ s q τ x)
      (fun m => capClock (s5γ s q x) (τs m)) ℓ
  else 0

/-- The stopped restarted driver. -/
def s5W (s : ℝ≥0) (q τ : ℚ) : ℝ≥0 → XD s q → ℝ := arcW (s5γ s q) (s5P s q) (s5S₀ s q τ) univ

/-- The stopped restarted lifetime. -/
def s5ζ (s : ℝ≥0) (q τ : ℚ) : XD s q → ℝ≥0∞ := arcζ (s5γ s q) (s5P s q) (s5S₀ s q τ) univ

/-- The stopped restarted left marks. -/
def s5VL (xL : Fin nL → ℝ) (τs : ℕ → ℝ) (ℓ : ℕ) (s : ℝ≥0) (q τ : ℚ) :
    Fin (ℓ + (nL + 1)) → ℝ≥0 → XD s q → ℝ :=
  arcVL (s5γ s q) (s5P s q) (s5S₀ s q τ) univ (s5XL xL τs ℓ s q τ)

/-- The stopped restarted right marks. -/
def s5VR (xR : Fin nR → ℝ) (τs : ℕ → ℝ) (ℓ : ℕ) (s : ℝ≥0) (q τ : ℚ) :
    Fin (ℓ + (nR + 1)) → ℝ≥0 → XD s q → ℝ :=
  arcVR (s5γ s q) (s5P s q) (s5S₀ s q τ) univ (s5XR xR τs ℓ s q τ)

/-- The stopped restarted chart. -/
def s5Chart (s : ℝ≥0) (q τ : ℚ) (x : XD s q) : Chart :=
  rChart (cfChart s x.1.2) (s5γ s q x) (s5P s q x) (s5S₀ s q τ x)

open scoped Classical in
theorem s5XL_eq_ite (xL : Fin nL → ℝ) {τ : ℚ} {τs : ℕ → ℝ} {τq : ℕ → ℚ} {ℓ : ℕ}
    (hτs : ∀ j : Fin ℓ, 0 ≤ τs (j + 1) ∧ τs (j + 1) ≤ τ) (hτq : ∀ j : Fin ℓ, τs (j + 1) = τq (j + 1)) :
    s5XL xL τs ℓ s q τ = fun x => if x ∈ s5Alive s q τ then
      stageArcL (s5γ s q) (s5P s q) (fun m => capQ (s5γ s q) (s5P s q) (τq m)) (s5S₀ s q τ)
        (fun x => GlueImg.imgMarkL xL (cfDrv0 s x.1.2) s) ℓ x else 0 := by
  funext x
  by_cases hx : x ∈ s5Alive s q τ
  · have hγ : IsKilledArc (s5γ s q x) (s5P s q x) := x.2.killed
    have hmem : ∀ j : Fin ℓ, (τq (j + 1) : ℝ) ∈ s5P s q x := fun j => by
      rw [← hτq j]
      exact hγ.icc _ hx (hτs j)
    simp only [s5XL, hx, ↓reduceIte]
    symm
    refine stageArcL_eq (γ := s5γ s q) (P := s5P s q) (x := x) (T := s5S₀ s q τ)
      (Sb := fun m => capQ (s5γ s q) (s5P s q) (τq m)) (X0 := fun x => GlueImg.imgMarkL xL (cfDrv0 s x.1.2) s)
      hγ (s5S₀_lt_kLife τ x) (fun j => ?_) xL (cfDrv0 s x.1.2) s rfl (fun j => ?_)
    · rw [← NNReal.coe_le_coe, coe_capQ (γ := s5γ s q) (P := s5P s q) hγ (hmem j), s5S₀_of_alive hx,
        Real.coe_toNNReal _ (hγ.capClock_nonneg hx), ← hτq j]
      exact hγ.strictMonoOn_capClock.monotoneOn (hγ.icc _ hx (hτs j)) hx (hτs j).2
    · rw [coe_capQ (γ := s5γ s q) (P := s5P s q) hγ (hmem j), ← hτq j]
  · simp only [s5XL, hx, ↓reduceIte]

open scoped Classical in
theorem s5XR_eq_ite (xR : Fin nR → ℝ) {τ : ℚ} {τs : ℕ → ℝ} {τq : ℕ → ℚ} {ℓ : ℕ}
    (hτs : ∀ j : Fin ℓ, 0 ≤ τs (j + 1) ∧ τs (j + 1) ≤ τ) (hτq : ∀ j : Fin ℓ, τs (j + 1) = τq (j + 1)) :
    s5XR xR τs ℓ s q τ = fun x => if x ∈ s5Alive s q τ then
      stageArcR (s5γ s q) (s5P s q) (fun m => capQ (s5γ s q) (s5P s q) (τq m)) (s5S₀ s q τ)
        (fun x => GlueImg.imgMarkR xR (cfDrv0 s x.1.2) s) ℓ x else 0 := by
  funext x
  by_cases hx : x ∈ s5Alive s q τ
  · have hγ : IsKilledArc (s5γ s q x) (s5P s q x) := x.2.killed
    have hmem : ∀ j : Fin ℓ, (τq (j + 1) : ℝ) ∈ s5P s q x := fun j => by
      rw [← hτq j]
      exact hγ.icc _ hx (hτs j)
    simp only [s5XR, hx, ↓reduceIte]
    symm
    refine stageArcR_eq (γ := s5γ s q) (P := s5P s q) (x := x) (T := s5S₀ s q τ)
      (Sb := fun m => capQ (s5γ s q) (s5P s q) (τq m)) (X0 := fun x => GlueImg.imgMarkR xR (cfDrv0 s x.1.2) s)
      hγ (s5S₀_lt_kLife τ x) (fun j => ?_) xR (cfDrv0 s x.1.2) s rfl (fun j => ?_)
    · rw [← NNReal.coe_le_coe, coe_capQ (γ := s5γ s q) (P := s5P s q) hγ (hmem j), s5S₀_of_alive hx,
        Real.coe_toNNReal _ (hγ.capClock_nonneg hx), ← hτq j]
      exact hγ.strictMonoOn_capClock.monotoneOn (hγ.icc _ hx (hτs j)) hx (hτs j).2
    · rw [coe_capQ (γ := s5γ s q) (P := s5P s q) hγ (hmem j), ← hτq j]
  · simp only [s5XR, hx, ↓reduceIte]

theorem measurable_s5XL (xL : Fin nL → ℝ) {τ : ℚ} {τs : ℕ → ℝ} {τq : ℕ → ℚ} {ℓ : ℕ}
    (hτs : ∀ j : Fin ℓ, 0 ≤ τs (j + 1) ∧ τs (j + 1) ≤ τ) (hτq : ∀ j : Fin ℓ, τs (j + 1) = τq (j + 1)) :
    Measurable (s5XL xL τs ℓ s q τ) := by
  classical
  rw [s5XL_eq_ite xL hτs hτq]
  exact Measurable.ite (measurableSet_s5Alive τ)
    (measurable_stageArcL isKilledFamily_s5 (fun m => measurable_capQ isKilledFamily_s5 _) (measurable_s5S₀ τ)
      ((measurable_gXLD (nR := 0) xL s).comp
        (measurable_const (a := (0 : HistorySpace nL 0)).prodMk (measurable_snd.comp measurable_subtype_coe))) ℓ)
      measurable_const

theorem measurable_s5XR (xR : Fin nR → ℝ) {τ : ℚ} {τs : ℕ → ℝ} {τq : ℕ → ℚ} {ℓ : ℕ}
    (hτs : ∀ j : Fin ℓ, 0 ≤ τs (j + 1) ∧ τs (j + 1) ≤ τ) (hτq : ∀ j : Fin ℓ, τs (j + 1) = τq (j + 1)) :
    Measurable (s5XR xR τs ℓ s q τ) := by
  classical
  rw [s5XR_eq_ite xR hτs hτq]
  exact Measurable.ite (measurableSet_s5Alive τ)
    (measurable_stageArcR isKilledFamily_s5 (fun m => measurable_capQ isKilledFamily_s5 _) (measurable_s5S₀ τ)
      ((measurable_gXRD (nL := 0) xR s).comp
        (measurable_const (a := (0 : HistorySpace 0 nR)).prodMk (measurable_snd.comp measurable_subtype_coe))) ℓ)
      measurable_const

theorem measurable_s5ζ (τ : ℚ) : Measurable (s5ζ s q τ) :=
  Prop59Pieces.measurable_arcζ isKilledFamily_s5 (measurable_s5S₀ τ) MeasurableSet.univ

theorem measurable_s5W (τ : ℚ) (u : ℝ≥0) : Measurable (s5W s q τ u) :=
  Prop59Pieces.measurable_arcW isKilledFamily_s5 (measurable_s5S₀ τ) MeasurableSet.univ u

theorem measurable_s5VL (xL : Fin nL → ℝ) {τ : ℚ} {τs : ℕ → ℝ} {τq : ℕ → ℚ} {ℓ : ℕ}
    (hτs : ∀ j : Fin ℓ, 0 ≤ τs (j + 1) ∧ τs (j + 1) ≤ τ) (hτq : ∀ j : Fin ℓ, τs (j + 1) = τq (j + 1))
    (i : Fin (ℓ + (nL + 1))) (u : ℝ≥0) : Measurable (s5VL xL τs ℓ s q τ i u) :=
  (Prop59Pieces.measurable_uncurry_arcVL isKilledFamily_s5 (measurable_s5S₀ τ) MeasurableSet.univ
    (measurable_s5XL xL hτs hτq) i).comp (measurable_const.prodMk measurable_id)

theorem measurable_s5VR (xR : Fin nR → ℝ) {τ : ℚ} {τs : ℕ → ℝ} {τq : ℕ → ℚ} {ℓ : ℕ}
    (hτs : ∀ j : Fin ℓ, 0 ≤ τs (j + 1) ∧ τs (j + 1) ≤ τ) (hτq : ∀ j : Fin ℓ, τs (j + 1) = τq (j + 1))
    (i : Fin (ℓ + (nR + 1))) (u : ℝ≥0) : Measurable (s5VR xR τs ℓ s q τ i u) :=
  (Prop59Pieces.measurable_uncurry_arcVR isKilledFamily_s5 (measurable_s5S₀ τ) MeasurableSet.univ
    (measurable_s5XR xR hτs hτq) i).comp (measurable_const.prodMk measurable_id)

/-- **The stopped restarted chart has measurable data.** -/
theorem isMeasChart_s5Chart (τ : ℚ) : IsMeasChart (inferInstance : MeasurableSpace (XD s q)) (s5Chart s q τ) := by
  have hc : IsMeasChart (inferInstance : MeasurableSpace (XD s q)) fun x => cfChart s x.1.2 :=
    isMeasChart_cfChart (Y := fun x : XD s q => x.1.2)
      ((GlueCond.measurable_cfStop s).comp (measurable_snd.comp measurable_subtype_coe))
  exact isMeasChart_rChart isKilledFamily_s5 (measurable_s5S₀ τ) (s5S₀_lt_kLife τ) hc

/-- The capacity of the stopped image curve at a rational own time up to `q` (`0` after the contact). -/
def capD (s : ℝ≥0) (q u : ℚ) (x : XD s q) : ℝ :=
  ({x : XD s q | (u : ℝ) ∈ PcD s x.1}.indicator fun x => capClock (gammaD s x.1) u) x

/-- **The window of the Galmarino filtration in stopped data**: the last switch `τ` and the own time `q` before the
contact, and `S₀ + r < σ(q)`. -/
def s5Win (s : ℝ≥0) (q τ : ℚ) (r : ℝ≥0) : Set (XD s q) :=
  {x | (τ : ℝ) ∈ PcD s x.1 ∧ (q : ℝ) ∈ PcD s x.1 ∧ (((capD s q τ x).toNNReal + r : ℝ≥0) : ℝ) < capD s q q x}

theorem measurableSet_s5Win {τ : ℚ} (hτ0 : (0 : ℝ) ≤ τ) (hτq : (τ : ℝ) ≤ q) (r : ℝ≥0) :
    MeasurableSet (s5Win s q τ r) := by
  have hq0 : (0 : ℝ) ≤ q := hτ0.trans hτq
  have hc : ∀ u : ℚ, (0 : ℝ) ≤ u → (u : ℝ) ≤ q → Measurable (capD s q u) := fun u hu0 huq =>
    measurable_indicator_capClock_gammaD u hu0 huq
  have hL : Measurable fun x => (((capD s q τ x).toNNReal + r : ℝ≥0) : ℝ) :=
    measurable_coe_nnreal_real.comp ((measurable_real_toNNReal.comp (hc τ hτ0 hτq)).add_const r)
  exact (measurableSet_mem_PcD τ hτ0 hτq).inter ((measurableSet_mem_PcD q hq0 le_rfl).inter
    (measurableSet_lt hL (hc q hq0 le_rfl)))

end Stopped

end InteractingSLE.Sec5.CrossCond.StagedS5
