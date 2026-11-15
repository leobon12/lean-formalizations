/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.ZhanGT4.A1G3RRIdent
import InteractingSLE.Spec.ZhanGT4.A1EightFinAssembly
import InteractingSLE.Spec.ZhanGT4.A1CommonExit
import InteractingSLE.Spec.ZhanGT4.A1MargSpace

/-!
# Zhan's A.1 (G3): the row martingale of one rectangle

Packet PROVE-A1-G3RECTROW. Source: Astra, *Follow-up proofs*, §A.1.4 (`ig1_followup_proofs.txt` L363–L407: "with the
first path fixed, `t ↦ M(s, t)` is a martingale in the second filtration") and §A.1.3 ((D9) on a protected
rectangle).

Fix the small curve at one sample and a positive own time `s ≤ S₁`. By `seedHeightField_g3Rec_row_eq` the row
`t ↦ seedHeightField (g3Rec …) (ω₁, ·) s (t ∧ S₂)` is `exp(L(t ∧ S₂, W_{t∧S₂}) − L(0, W_0))` for the field
`L = log M̃ + ℓ`: the frozen-curve logarithm of the opposite view (a tube field with vanishing driftless generator,
`isTubeLogField_frz`, with the uniform (D9) facts of `exists_twoCurveD9_eView`) plus the logarithm `ℓ` of the inverse
`SLE_κ(κ − 4, −4)` martingale (a drifted log-field, `G3Field.isDriftLogField_g3`, with the uniform force gaps of
`exists_gap_bounds_left`). Their sum is a drifted log-field (`isDriftLogField_add`: the drift is `−κ ℓ_x`), so A22's
`normalized_martingale_zero` / `normalized_path_facts` make the row a martingale with continuous paths.

* `exists_gap_bounds_left`: uniform two-sided bounds of the real flow at a protected point left of an `ℍ`-hull;
* `disjoint_ball_mark`: the ordinary mark is protected from the large enclosure (segment condition);
* **`g3_row`**: the row martingale and its continuity, for one rectangle and one small sample.
-/

set_option autoImplicit false

noncomputable section

open Complex Set Filter Topology Metric MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace InteractingSLE.ZhanGT4.A1G3RR

open QuantumZipper (IsForwardSol fwdMap fwdHull)
open A2X A1SeedField A1EightSeed A1EightFin A1G3Calc A1G3Id G3Field A1Common

/-- **Uniform two-sided bounds of the real flow at a protected point left of an `ℍ`-hull**: for `x₀ < 0` with
`ball x₀ ρ ∩ E = ∅` and `0 ∈ closure E`, constants `0 < c ≤ C` such that for every continuous driver from `0` whose
hull lies in `E` up to `T ≤ Tm`, `c ≤ |Re g_t(x₀)| ≤ C` on `[0, T]` (A1-EIGHTFIN's `exists_real_gap_bounds`, with a
protected point on the right of `E`). -/
theorem exists_gap_bounds_left {E : Set ℂ} (hE : IsHPHull E) {x₀ ρ : ℝ} (hρ : 0 < ρ) (hx₀ : x₀ < 0)
    (hxE : Disjoint (ball (x₀ : ℂ) ρ) E) (h0E : (0 : ℂ) ∈ closure E) (Tm : ℝ) :
    ∃ c C : ℝ, 0 < c ∧ 0 ≤ C ∧ ∀ W : ℝ → ℝ, Continuous W → W 0 = 0 → ∀ T : ℝ, 0 ≤ T → T ≤ Tm →
      fwdHull W T ⊆ E → ∀ t ∈ Icc (0 : ℝ) T, c ≤ |(fwdMap W t x₀).re| ∧ |(fwdMap W t x₀).re| ≤ C := by
  obtain ⟨R, hR⟩ := hE.2.1.exists_norm_le
  set xr : ℝ := max R 0 + 2 with hxr
  have hxrE : Disjoint (ball (xr : ℂ) 1) E := by
    refine Set.disjoint_left.2 fun z hz hzE => ?_
    have h1 := hR z hzE
    rw [mem_ball, dist_eq_norm] at hz
    have h2 : ‖(xr : ℂ)‖ ≤ ‖z‖ + ‖z - xr‖ := by
      calc ‖(xr : ℂ)‖ = ‖z - (z - xr)‖ := by ring_nf
        _ ≤ ‖z‖ + ‖z - xr‖ := norm_sub_le _ _
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by positivity)] at h2
    linarith [le_max_left R 0]
  have hxr0 : 0 < xr := by positivity
  obtain ⟨c, C, hc, hC, hb⟩ := exists_real_gap_bounds hE (lt_min hρ one_pos)
    (hxE.mono_left (ball_subset_ball (min_le_left _ _))) (hxrE.mono_left (ball_subset_ball (min_le_right _ _))) Tm
  refine ⟨c, C, hc, hC, fun W hW hW0 T hT hTm hK t ht => hb W hW ?_ ?_ ?_ T hT hTm hK t ht⟩
  · rw [hW0]; simpa using h0E
  · rw [hW0]; exact hx₀
  · rw [hW0]; exact hxr0

/-- **The ordinary mark is protected from the large enclosure**: a point `x₀ ∈ (0, q]` has its `δ`-ball, translated by
`−p`, disjoint from `transl (−p) H₂` (the segment condition of `IsProtectedPairG`). -/
theorem disjoint_ball_mark {H₁ H₂ : Set ℂ} {δ p q dd : ℝ} (hpp : IsProtectedPairG H₁ H₂ δ p q dd) {x₀ : ℝ}
    (h0 : 0 < x₀) (hq : x₀ ≤ q) : Disjoint (ball ((x₀ - p : ℝ) : ℂ) δ) (transl (-p) H₂) := by
  refine Set.disjoint_left.2 fun z hz hzG => ?_
  rw [mem_transl_iff] at hzG
  have h1 := hpp.seg _ hzG x₀ h0 hq
  rw [mem_ball, dist_eq_norm] at hz
  have e : z - ((-p : ℝ) : ℂ) - (x₀ : ℂ) = z - ((x₀ - p : ℝ) : ℂ) := by push_cast; ring
  rw [e] at h1
  linarith [hpp.pair.sep_pos]

/-! ### The row martingale of one rectangle -/

section Row

variable {X Y : Type*} [mY : MeasurableSpace Y]

/-- **The (G3) row martingale of one rectangle.** Fix a protected pair (`IsProtectedPairG`, other source `p`), a small
sample `ω₁` with its rectangle data (the small `G3` path with the ordinary mark `xR 1 ∈ (0, q]`, the exit
`S₁ m ω₁ < ζ₁` with hull in `H₁`, the seeds and the ordinary mark off the driver), a regular large
`SLE_κ(κ − 4, −4)` marginal with continuous Brownian paths whose force points start at `xR 1 − p` and `−p`, and large
exits `S₂ m` (stopping times, bounded, before the lifetime, positive, hull in `H₂` after the shift by `p`). Then for
every own time `s ∈ (0, S₁ m ω₁]` the row `t ↦ seedHeightField (g3Rec …) (ω₁, ·) s (t ∧ S₂ m)` is a martingale of the
large filtration, with continuous paths at every sample. -/
theorem g3_row {P₂ : Measure Y} [IsProbabilityMeasure P₂] {κ p a₀ : ℝ} (hκ : 0 < κ) {xL : Fin 1 → ℝ}
    {xR : Fin 3 → ℝ} {ρL : Fin 1 → ℝ} {ρR : Fin 3 → ℝ} {W₁ : ℝ≥0 → X → ℝ} {VL₁ : Fin 1 → ℝ≥0 → X → ℝ}
    {VR₁ : Fin 3 → ℝ≥0 → X → ℝ} {B₁ : ℝ≥0 → X → ℝ} {ζ₁ : X → ℝ≥0∞} {S₁ : ℕ → X → ℝ≥0} {H₁ H₂ : Set ℂ}
    {δ q dd Tm : ℝ} {m : ℕ} {ω₁ : X} (hpp : IsProtectedPairG H₁ H₂ δ p q dd)
    (hP : IsIntegratedSLEPath a₀ xL xR ρL ρR (W₁ · ω₁) (fun i s => VL₁ i s ω₁) (fun i s => VR₁ i s ω₁) (B₁ · ω₁)
      (ζ₁ ω₁))
    (hxL : xL 0 = 0) (hxR : xR 0 = 0) (hxO : 0 < xR 1) (hxOq : xR 1 ≤ q)
    (hgood₁ : (S₁ m ω₁ : ℝ≥0∞) < ζ₁ ω₁ ∧ 0 < (S₁ m ω₁ : ℝ) ∧ (S₁ m ω₁ : ℝ) ≤ Tm ∧
      fwdHull (eightDrv W₁ S₁ m ω₁) (S₁ m ω₁) ⊆ H₁)
    (hsep₁ : ∀ s : ℝ≥0, 0 < s → (s : ℝ≥0∞) < ζ₁ ω₁ → VL₁ 0 s ω₁ ≠ W₁ s ω₁ ∧ VR₁ 0 s ω₁ ≠ W₁ s ω₁)
    (hsepO : ∀ s : ℝ≥0, (s : ℝ≥0∞) < ζ₁ ω₁ → VR₁ 1 s ω₁ ≠ W₁ s ω₁)
    {𝓕₂ : Filtration ℝ≥0 mY} {xL₂ : Fin 2 → ℝ} {xR₂ ρR₂ : Fin 0 → ℝ} {W₂ B₂ : ℝ≥0 → Y → ℝ}
    {VL₂ : Fin 2 → ℝ≥0 → Y → ℝ} {VR₂ : Fin 0 → ℝ≥0 → Y → ℝ} {ζ₂ : Y → ℝ≥0∞}
    (h₂ : A1Marg.IsRegMarginal κ xL₂ xR₂ ![κ - 4, -4] ρR₂ P₂ 𝓕₂ W₂ VL₂ VR₂ B₂ ζ₂)
    (hB₂ : ∀ y, Continuous (B₂ · y)) (hx₂ : xL₂ 0 = xR 1 - p) (hy₂ : xL₂ 1 = -p) {S₂ : ℕ → Y → ℝ≥0}
    (hS₂ : IsStoppingTime 𝓕₂ fun y => (S₂ m y : WithTop ℝ≥0)) {U : ℝ≥0} (hU : ∀ y, S₂ m y ≤ U)
    (hS₂ζ : ∀ y, (S₂ m y : ℝ≥0∞) < ζ₂ y) (hS₂pos : ∀ y, 0 < (S₂ m y : ℝ))
    (hgood₂ : ∀ y, (S₂ m y : ℝ) ≤ Tm ∧ fwdHull (frzPath W₂ p (S₂ m y) y) (S₂ m y) ⊆ H₂)
    (hK₂ : ∀ y, fwdHull (Strip.extPath (W₂ · y)) (S₂ m y) ⊆ transl (-p) H₂)
    {s : ℝ} (hs : s ∈ Ioc (0 : ℝ) (S₁ m ω₁)) :
    Martingale (fun (t : ℝ≥0) y => seedHeightField (g3Rec κ p W₁ VL₁ VR₁ W₂ S₁ m) (ω₁, y) s
        (min (t : ℝ) (S₂ m y))) 𝓕₂ P₂ ∧
      ∀ y, Continuous fun t : ℝ≥0 => seedHeightField (g3Rec κ p W₁ VL₁ VR₁ W₂ S₁ m) (ω₁, y) s
        (min (t : ℝ) (S₂ m y)) := by
  have hpq : xR 1 < p := hxOq.trans_lt hpp.pair.prot_lt
  have hsI : s ∈ Icc (0 : ℝ) (S₁ m ω₁) := Ioc_subset_Icc_self hs
  obtain ⟨y₀⟩ := nonempty_of_isProbabilityMeasure P₂
  -- the large path facts at every sample
  have hc₂ : ∀ y, ContinuousOn (Strip.extPath (W₂ · y)) (Icc 0 (S₂ m y : ℝ)) := fun y =>
    A1Ref.continuousOn_extPath_Icc (h₂.path y).2.2.2.1 (by rw [ENNReal.ofReal_coe_nnreal]; exact hS₂ζ y)
  have h0₂ : ∀ y, W₂ 0 y = 0 := fun y => (h₂.path y).1
  -- the enclosure data of every rectangle
  have hne : ∀ r : ℝ≥0, 0 < r → r ≤ S₁ m ω₁ → VL₁ 0 r ω₁ ≠ W₁ r ω₁ ∧ VR₁ 0 r ω₁ ≠ W₁ r ω₁ := fun r hr hrS =>
    hsep₁ r hr (lt_of_le_of_lt (ENNReal.coe_le_coe.2 hrS) hgood₁.1)
  have hEq := eightDrv_eqOn W₁ S₁ m ω₁
  have hloW := vL_le_of_path hP 0 hgood₁.1 hEq
  have hWhi := le_vR_of_path hP 0 hgood₁.1 hEq
  have hset : ∀ y, G3Setup H₁ H₂ δ p q dd Tm (eightDrv W₁ S₁ m ω₁) (frzPath W₂ p (S₂ m y) y) (S₁ m ω₁)
      (S₂ m y) (Strip.extPath (VL₁ 0 · ω₁)) (Strip.extPath (VR₁ 0 · ω₁)) (g3Marks VL₁ VR₁ ω₁) := fun y => by
    have hrec := isSourceRecordG_g3Rec (κ := κ) (p := p) (m := m) hP hxL hxR hxO hxOq hgood₁.1 hgood₁.2.1
      (fun r hr hrS => (hne r hr hrS).1) (fun r hr hrS => (hne r hr hrS).2)
      (fun r hrS => hsepO r (lt_of_le_of_lt (ENNReal.coe_le_coe.2 hrS) hgood₁.1))
      (by have := hpp.pair.rad_pos; positivity) (hpp.pair.prot.mono_right subset_union_left) (hc₂ y) (h0₂ y)
      (hS₂pos y) (hgood₂ y).1 hgood₁.2.2.1 hpp.pair.sep_pos hpp.pair.sep hgood₁.2.2.2 (hgood₂ y).2
    exact g3Setup_of_isSourceRecordG hpp hrec rfl rfl (fun t ht => Icc_subset_uIcc ⟨hloW t ht, hWhi t ht⟩)
  have hv₀ := (hset y₀).view
  -- the small curve at the own time `s`
  have hVq : ∀ j, g3Marks VL₁ VR₁ ω₁ j s ≤ (fwdMap (eightDrv W₁ S₁ m ω₁) s q).re + eightDrv W₁ S₁ m ω₁ s :=
    fun j => G3Setup.marks_le (hset y₀) hs (hloW s hsI) j
  have hVW : ∀ j, g3Marks VL₁ VR₁ ω₁ j s ≠ eightDrv W₁ S₁ m ω₁ s := fun j => ((hset y₀).mark j).ne s hs
  have hVinj : Function.Injective fun j => g3Marks VL₁ VR₁ ω₁ j s := (hset y₀).inj s hs
  -- (D9) of the opposite views, uniformly in the large sample
  obtain ⟨r, a₀', γ, Γ, lam, hr, ha₀', hγ, hD⟩ :=
    exists_twoCurveD9_eView hpp.pair hs hv₀.cont₁ hv₀.zero₁ hv₀.le₁ hv₀.K₁ hVq hVW hVinj
  obtain ⟨L, hL⟩ := exists_scaleOK hr ha₀' hγ Γ lam Tm
  set d : Y → FrzData 3 := fun y => eView (kh κ) (g3RR κ) (eightDrv W₁ S₁ m ω₁) (frzPath W₂ p (S₂ m y) y)
    (S₁ m ω₁) (S₂ m y) (g3Marks VL₁ VR₁ ω₁) s with hd
  have hz : ∀ y, frzPath W₂ p (S₂ m y) y 0 = p := fun y => frzPath_zero (h0₂ y) (S₂ m y).coe_nonneg
  have hWd : ∀ y, (fun u => frzPath W₂ p (S₂ m y) y u - frzPath W₂ p (S₂ m y) y 0) =
      A1Ref.stopDrv (Strip.extPath (W₂ · y)) (S₂ m y) := fun y =>
    A1Asm.frzPath_sub_zero_eq (h0₂ y) p (S₂ m y) (S₂ m y).coe_nonneg
  have hdW : ∀ y, ∀ t ∈ Icc (0 : ℝ) (S₂ m y), (d y).W t = driftDriver (Real.sqrt κ) B₂ (D κ W₂ B₂) y t := by
    intro y t ht
    show frzPath W₂ p (S₂ m y) y t - frzPath W₂ p (S₂ m y) y 0 = _
    rw [show frzPath W₂ p (S₂ m y) y t - frzPath W₂ p (S₂ m y) y 0 =
        A1Ref.stopDrv (Strip.extPath (W₂ · y)) (S₂ m y) t from congrFun (hWd y) t, A1Ref.stopDrv_eqOn _ _ ht,
      driftDriver_eq]
    rfl
  have hown : ∀ y, OwnData (d y).W (fwdHull (fun u => eightDrv W₁ S₁ m ω₁ u - p) s) (d y).φ (S₂ m y) (d y).a
      (d y).W' := fun y => by
    have h := ((hset y).view.tOwn hsI).1
    rw [show fwdHull (fun u => eightDrv W₁ S₁ m ω₁ u - frzPath W₂ p (S₂ m y) y 0) s =
      fwdHull (fun u => eightDrv W₁ S₁ m ω₁ u - p) s by rw [hz y]] at h
    exact h
  have hDy : ∀ y, TwoCurveD9 (d y) (fwdHull (fun u => eightDrv W₁ S₁ m ω₁ u - p) s) (S₂ m y) r a₀' γ Γ lam :=
    fun y => hD (kh κ) (g3RR κ) _ _ _ _ (hset y).view
  have hTube := isTubeLogField_frz (𝓕 := 𝓕₂) (σ := Real.sqrt κ) (B := B₂) (D := D κ W₂ B₂) (S := S₂ m) d
    (φ := frzChart (fun u => eightDrv W₁ S₁ m ω₁ u - p) s) (κ := 16 / kh κ)
    (ζ₀ := eightDrv W₁ S₁ m ω₁ s - p) (rr := fun j => -(kh κ / 4) * g3RR κ j)
    (ζ := fun j => g3Marks VL₁ VR₁ ω₁ j s - p)
    (fun y => by
      show frzChart (fun u => eightDrv W₁ S₁ m ω₁ u - frzPath W₂ p (S₂ m y) y 0) s = _
      rw [hz y])
    (fun _ => rfl) (fun _ => rfl)
    (fun y => by
      show eightDrv W₁ S₁ m ω₁ s - frzPath W₂ p (S₂ m y) y 0 = _
      rw [hz y])
    (fun y => by
      show (fun j => g3Marks VL₁ VR₁ ω₁ j s - frzPath W₂ p (S₂ m y) y 0) = _
      rw [hz y])
    hdW (X := fun u y => A1Ref.stopDrv (Strip.extPath (W₂ · y)) (S₂ m y) u)
    (fun u => measurable_stopDrv_of_progressive h₂.progW hS₂ u)
    (fun y => (A1Ref.continuous_stopDrv (hc₂ y) (S₂ m y).coe_nonneg).comp NNReal.continuous_coe)
    (fun y => by
      funext t
      show frzPath W₂ p (S₂ m y) y t - frzPath W₂ p (S₂ m y) y 0 =
        A1Ref.stopDrv (Strip.extPath (W₂ · y)) (S₂ m y) (t.toNNReal : ℝ)
      rw [show frzPath W₂ p (S₂ m y) y t - frzPath W₂ p (S₂ m y) y 0 =
        A1Ref.stopDrv (Strip.extPath (W₂ · y)) (S₂ m y) t from congrFun (hWd y) t]
      exact (eightDrv_toNNReal W₂ (fun _ _ => S₂ m y) 0 y t).symm)
    hS₂ hL (fun y => (hgood₂ y).1) hown hDy
  -- the force gaps of the large curve, uniform in the sample
  set E := transl (-p) H₂ with hEdef
  have hE : IsHPHull E := isHPHull_transl hpp.pair.hull₂ (-p)
  have h0E : (0 : ℂ) ∈ closure E := by
    have := mem_closure_transl hpp.pair.src (-p)
    simpa using this
  have h0H₁ : ((0 : ℝ) : ℂ) ∈ closure H₁ := by
    have := closure_mono hv₀.K₁ (start_mem_closure_fwdHull hv₀.cont₁ hv₀.pos₁)
    rwa [hv₀.zero₁] at this
  have hp : 0 < p := hxO.trans hpq
  have hxneg : ∀ i, xL₂ i < 0 := fun i => by
    fin_cases i
    · show xL₂ 0 < 0
      rw [hx₂]; linarith
    · show xL₂ 1 < 0
      rw [hy₂]; linarith
  have hball : ∀ i, Disjoint (ball ((xL₂ i : ℝ) : ℂ) δ) E := fun i => by
    fin_cases i
    · show Disjoint (ball ((xL₂ 0 : ℝ) : ℂ) δ) E
      rw [hx₂]; exact disjoint_ball_mark hpp hxO hxOq
    · show Disjoint (ball ((xL₂ 1 : ℝ) : ℂ) δ) E
      rw [hy₂]; exact disjoint_ball_neg_src hpp.pair h0H₁
  choose c C hc hC hb using fun i => exists_gap_bounds_left hE hpp.pair.sep_pos (hxneg i) (hball i) h0E Tm
  have hWdc : ∀ y, Continuous (A1Ref.stopDrv (Strip.extPath (W₂ · y)) (S₂ m y)) := fun y =>
    A1Ref.continuous_stopDrv (hc₂ y) (S₂ m y).coe_nonneg
  have hWd0 : ∀ y, A1Ref.stopDrv (Strip.extPath (W₂ · y)) (S₂ m y) 0 = 0 := fun y => by
    rw [A1Ref.stopDrv_eqOn _ _ ⟨le_rfl, (S₂ m y).coe_nonneg⟩]
    simp [Strip.extPath, h0₂ y]
  have hKd : ∀ y, fwdHull (A1Ref.stopDrv (Strip.extPath (W₂ · y)) (S₂ m y)) (S₂ m y) ⊆ E := fun y => by
    have h := fwdHull_sub_const_subset (c := p) (hgood₂ y).2
    have e : (fun u => frzPath W₂ p (S₂ m y) y u - p) = A1Ref.stopDrv (Strip.extPath (W₂ · y)) (S₂ m y) := by
      funext u; simp only [frzPath, add_sub_cancel_right]
    rwa [e] at h
  have hgap : ∀ y (r : ℝ≥0), r ≤ S₂ m y → ∀ i, c i ≤ |W₂ r y - VL₂ i r y| ∧ |W₂ r y - VL₂ i r y| ≤ C i := by
    intro y r hr i
    obtain ⟨-, -, -, hcw, hcvL, -, -, -, -, -, -, -, -, hvLeq, -⟩ := id (h₂.path y)
    have hveq : ∀ t : ℝ≥0, (t : ℝ≥0∞) < ζ₂ y →
        VL₂ i t y = xL₂ i + ∫ u in (0 : ℝ)..t, 2 / (VL₂ i u.toNNReal y - W₂ u.toNNReal y) := fun t ht =>
      hvLeq t ht i
    obtain ⟨cy, hcy, hgy⟩ := protected_mark_bounds (h₂.path y) (hcvL i) hveq (hxneg i).ne hE h0E
      hpp.pair.sep_pos (hball i)
    have hsep : ∀ r' ≤ S₂ m y, VL₂ i r' y ≠ W₂ r' y := fun r' hr' he => by
      have := (hgy (S₂ m y) (hS₂ζ y) (hK₂ y)).1 r' hr'
      simp only at this
      rw [he, sub_self, abs_zero] at this
      linarith
    have hid := fwdMap_stopDrv_add_eq hcw (hcvL i) hveq (hS₂ζ y) hsep hr
    have hWr : A1Ref.stopDrv (Strip.extPath (W₂ · y)) (S₂ m y) r = W₂ r y := by
      rw [A1Ref.stopDrv_eqOn _ _ ⟨r.coe_nonneg, NNReal.coe_le_coe.2 hr⟩]
      simp [Strip.extPath]
    have hbd := hb i _ (hWdc y) (hWd0 y) (S₂ m y) (S₂ m y).coe_nonneg (hgood₂ y).1 (hKd y) r
      ⟨r.coe_nonneg, NNReal.coe_le_coe.2 hr⟩
    have e : W₂ r y - VL₂ i r y =
        -(fwdMap (A1Ref.stopDrv (Strip.extPath (W₂ · y)) (S₂ m y)) r (xL₂ i)).re := by
      simp only at hid
      linarith
    rw [e, abs_neg]
    exact hbd
  set δ₂ := min (c 0) (c 1) with hδ₂def
  have hδ₂ : 0 < δ₂ := lt_min (hc 0) (hc 1)
  have hcδ : ∀ i, δ₂ ≤ c i := fun i => by
    fin_cases i
    · exact min_le_left _ _
    · exact min_le_right _ _
  have hCR : ∀ i, C i ≤ max (C 0) (C 1) := fun i => by
    fin_cases i
    · exact le_max_left _ _
    · exact le_max_right _ _
  have hpo : ∀ y, PathOn κ xL₂ xR₂ ρR₂ W₂ VL₂ VR₂ B₂ ζ₂ y (S₂ m y) δ₂ := fun y =>
    ⟨h₂.path y, hS₂ζ y, hδ₂, fun r hr i => (hcδ i).trans (hgap y r hr i).1⟩
  obtain ⟨K₂, hG⟩ := isDriftLogField_g3 (𝓕 := 𝓕₂) hκ hpo
    (fun y r hr i => (hgap y r hr i).2.trans (hCR i)) hU hδ₂ h₂.progW h₂.progVL hS₂
  -- the sum of the two fields
  set ρc := min (δ₂ / 8) (3 * cutRad r a₀' γ / 4) with hρcdef
  have hρc : 0 < ρc := lt_min (by positivity) (by have := cutRad_pos hr ha₀' hγ; positivity)
  have hσ : ∀ y, (d y).κ = Real.sqrt κ ^ 2 := fun y => by
    show 16 / kh κ = _
    rw [sixteen_div_kh hκ.ne', Real.sq_sqrt hκ.le]
  have hsum := isDriftLogField_add (IsDriftLogField.mono_radius hG (min_le_left _ _))
    (hTube.mono_radius (min_le_right _ _))
    (fun y t ht => FrzData.gen_eq_zero_of_twoCurveD9 (d y) (hown y) (hDy y) (hσ y) (Real.sqrt_pos.2 hκ).ne'
      (by simpa only [NNReal.coe_zero] using ht) (hdW y t (by simpa only [NNReal.coe_zero] using ht)))
    (fun y t ht => by
      have ht' : t ∈ Icc (0 : ℝ) (S₂ m y) := by simpa only [NNReal.coe_zero] using ht
      have h0 := (hpo y).ne ht' 0
      have h1 := (hpo y).ne ht' 1
      rw [driftDriver_eq, Real.sq_sqrt hκ.le]
      simp only [drift, ellX, cy, cx]
      field_simp
      ring)
  obtain ⟨hm, -⟩ := hsum.normalized_martingale_zero h₂.evol.1 hB₂ (Real.sqrt_nonneg κ) hρc hS₂
  obtain ⟨hcont, -⟩ := hsum.normalized_path_facts hB₂ hρc
  -- the row is the normalized exponential of the sum
  have hV2 : g3Marks VL₁ VR₁ ω₁ 2 0 = xR 1 := by
    obtain ⟨-, -, hvR0, -⟩ := id hP
    change Strip.extPath (VR₁ 1 · ω₁) 0 = xR 1
    simp only [Strip.extPath, Real.toNNReal_zero]
    exact hvR0 1
  have hrow : ∀ y (u : ℝ≥0), u ≤ S₂ m y →
      seedHeightField (g3Rec κ p W₁ VL₁ VR₁ W₂ S₁ m) (ω₁, y) s u =
        Real.exp (((d y).ell u (driftDriver (Real.sqrt κ) B₂ (D κ W₂ B₂) y u) +
            ell κ W₂ VL₂ y u (driftDriver (Real.sqrt κ) B₂ (D κ W₂ B₂) y u)) -
          ((d y).ell 0 (driftDriver (Real.sqrt κ) B₂ (D κ W₂ B₂) y 0) +
            ell κ W₂ VL₂ y 0 (driftDriver (Real.sqrt κ) B₂ (D κ W₂ B₂) y 0))) := by
    intro y u hu
    rw [driftDriver_eq, driftDriver_eq]
    exact seedHeightField_g3Rec_row_eq hκ (hset y) (hc₂ y) (h0₂ y) (by rw [hV2]; exact hxO.ne')
      (by rw [hV2]; exact hpq.ne) (hpo y) (by rw [hx₂, hV2]) hy₂ hs hu
  refine ⟨?_, fun y => ?_⟩
  · convert hm using 1
    funext t y
    rw [← NNReal.coe_min, hrow y _ (min_le_right _ _)]
  · convert hcont y using 1
    funext t
    rw [← NNReal.coe_min, hrow y _ (min_le_right _ _)]

end Row

end InteractingSLE.ZhanGT4.A1G3RR
