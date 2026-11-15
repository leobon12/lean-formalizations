/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.ZhanGT4.A1G3L2SndLaw
import InteractingSLE.Spec.ZhanGT4.A1G3L2Zero
import InteractingSLE.Spec.ZhanGT4.A2TipSepGeom

/-!
# Zhan's A.1 under R83, (G3), small-curve direction: the seeded capacity geometry of the column

Packet PROVE-A1-G3LAW2. At a frozen sample `y₀` live at a protected frozen time `σ ∈ (0, S₂ᵏ(y₀)]` and every small
sample `x₀`, for the record `s = g3Col … k σ y₀ x₀`:

* `large_force_facts`: the frozen chart of the large curve (physical map shifted by `c`) is continuous at the images
  `xL i + c` of the large curve's marks, its real part there is the force point `c + V_i(σ)`, and these points are off
  the closed frozen hull (they are alive);
* **`g3Col_hstart`**: the record's image chain starts at `V_y(σ) − y` (`W'(0) + y = V_y(σ)`);
* **`g3Col_geometry`**: the seeded capacity coordinates of the column form a `SeedImageGeometry` with the small
  image word `(![0], ![0, V_x(σ) − V_y(σ), W(σ) − V_y(σ)])` (A1-MULTIMARK's `seedImageGeometry_capForce`: image
  equations of the marks and the frozen tip, positive-time sides from the monotone own map, initial word from the own
  map at time `0`, `ownExt_zero_eq`).
-/

set_option autoImplicit false

noncomputable section

open Complex Set Filter Topology Metric MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace InteractingSLE.ZhanGT4.A1G3L2

open QuantumZipper (H fwdHull fwdMap IsForwardSol)
open A2X A1Ref A1Canon A1Core A1Frozen A1Marg A1Law A1Patch A1SeedField A1EightSeed A1G3Calc A1Common A1EightFin
  A1Asm A1Family A1Forces A1RLaw A1G3Law A1LargeDens A1SeedGeom A1MultiMark

/-! ### The large curve's marks in the frozen chart -/

section Large

variable {κ x y : ℝ} {W : ℝ≥0 → ℝ} {VL : Fin 2 → ℝ≥0 → ℝ} {VR : Fin 0 → ℝ≥0 → ℝ} {B : ℝ≥0 → ℝ} {ζ : ℝ≥0∞}

/-- **The large curve's marks in its frozen chart**: at a live time `σ` (strip life), for each mark `i` and shift
`c`, the physical map `physMap c W σ` is continuous at `xL i + c`, has real part `c + V_i(σ)` there, and `xL i + c`
is off the closed physical hull. -/
theorem large_force_facts (hP : IsIntegratedSLEPath κ ![x, y] ![] ![κ - 4, -4] ![] W VL VR B ζ)
    {σ : ℝ≥0} (hlive : Strip.IsStripLife W (VL 0) ζ σ) (i : Fin 2) (c : ℝ) :
    ContinuousAt (physMap c (Strip.extPath W) σ) (((![x, y] : Fin 2 → ℝ) i + c : ℝ) : ℂ) ∧
      (physMap c (Strip.extPath W) σ (((![x, y] : Fin 2 → ℝ) i + c : ℝ) : ℂ)).re = c + VL i σ ∧
      (((![x, y] : Fin 2 → ℝ) i + c : ℝ) : ℂ) ∉ closure (physHull c (Strip.extPath W) σ) := by
  obtain ⟨-, hL0, -, hcw, hcL, -, hanti, -, -, -, -, -, -, hLeq, -⟩ := hP
  have hsep : ∀ r ≤ σ, VL i r ≠ W r := by
    intro r hr
    have hlt : VL 0 r < W r := hlive.2 r hr
    have hrζ : (r : ℝ≥0∞) < ζ := lt_of_le_of_lt (ENNReal.coe_le_coe.2 hr) hlive.1
    fin_cases i
    · exact hlt.ne
    · exact (lt_of_le_of_lt (hanti r hrζ (show (0 : Fin 2) ≤ 1 by decide)) hlt).ne
  have hu := isForwardSol_extPath_of_force (hcL i) hcw (fun t ht => hLeq t ht i) hlive.1 hsep
  obtain ⟨τ', hστ', hcτ⟩ := A1Ref.exists_continuousOn_extPath_beyond hcw hlive.1
  have hf := continuousAt_fwdMap_of_isForwardSol hστ' σ.coe_nonneg hcτ hu
  have hpt : (((![x, y] : Fin 2 → ℝ) i + c : ℝ) : ℂ) - (c : ℂ) = ((((![x, y] : Fin 2 → ℝ) i : ℝ)) : ℂ) := by
    push_cast; ring
  refine ⟨?_, ?_, ?_⟩
  · have hg : ContinuousAt (fun z : ℂ => fwdMap (Strip.extPath W) σ (z - c))
        (((![x, y] : Fin 2 → ℝ) i + c : ℝ) : ℂ) :=
      ContinuousAt.comp_of_eq hf (continuousAt_id.sub continuousAt_const) hpt
    have e : physMap c (Strip.extPath W) σ =
        fun z => ((c : ℂ) + (Strip.extPath W σ : ℂ)) + fwdMap (Strip.extPath W) σ (z - c) := rfl
    rw [e]
    exact continuousAt_const.add hg
  · have hval := A1SeedField.fwdMap_add_eq_force (hcL i) (fun t ht => hLeq t ht i) hlive.1
      hsep (A1Ref.continuousOn_extPath_Icc hcw (by rw [ENNReal.ofReal_coe_nnreal]; exact hlive.1))
      (fun _ _ => rfl) ⟨σ.coe_nonneg, le_rfl⟩
    simp only [physMap, hpt, add_re, ofReal_re]
    have he : Strip.extPath (VL i) (σ : ℝ) = VL i σ := by simp [Strip.extPath]
    rw [he] at hval
    linarith only [hval]
  · set V := stopDrv (Strip.extPath W) τ' with hVdef
    have hVc : Continuous V := continuous_stopDrv hcτ (σ.coe_nonneg.trans hστ'.le)
    have hVe : EqOn (Strip.extPath W) V (Icc 0 τ') := (stopDrv_eqOn _ τ').symm
    have hu' : IsForwardSol V ((((![x, y] : Fin 2 → ℝ) i : ℝ)) : ℂ) σ _ := QuantumZipper.isForwardSol_congr_drive
      (fun r hr => hVe ⟨hr.1, hr.2.trans hστ'.le⟩) hu
    have hK : physHull c (Strip.extPath W) σ = physHull c V σ :=
      A1SeedGeom.physHull_congr_of_continuousOn hcτ hVc.continuousOn σ.coe_nonneg hστ'
        (hVe.mono (Icc_subset_Icc_right hστ'.le))
    have hnot := A2TipSep.not_mem_closure_fwdHull_of_isForwardSol hVc σ.coe_nonneg hu'
    have hcl : closure ((fun z => z + (c : ℂ)) '' fwdHull V σ) = (fun z => z + (c : ℂ)) '' closure (fwdHull V σ) :=
      ((Homeomorph.addRight (c : ℂ)).image_closure (fwdHull V σ)).symm
    rw [hK, physHull, hcl]
    intro hmem
    obtain ⟨z, hz, hze⟩ := hmem
    have hz' : z = ((((![x, y] : Fin 2 → ℝ) i : ℝ)) : ℂ) := by
      have h1 : z + c = (((![x, y] : Fin 2 → ℝ) i + c : ℝ) : ℂ) := hze
      rw [← hpt, ← h1]; ring
    rw [hz'] at hz
    exact hnot hz

end Large

/-! ### The image equation of a mark coordinate -/

section Mark

/-- **The image mark equation for a mark coordinate** (mirror of A22's `hasDerivWithinAt_image_seed` with
A1-G3CALC's `IsMarkCoordinate` in place of `IsSeedCoordinate`). -/
theorem hasDerivWithinAt_image_mark {n : ℕ} (s : SeedData n) {A : Set ℂ} {T r L₀ : ℝ} {I : ℝ → Set ℝ}
    (h : OwnData s.W A s.φ T s.a s.W') (hr : 0 < r) (hI : ∀ t ∈ Icc (0 : ℝ) T, Convex ℝ (I t))
    (hWI : ∀ t ∈ Icc (0 : ℝ) T, s.W t ∈ I t) (hVI : ∀ t ∈ Icc (0 : ℝ) T, ∀ m, s.V m t ∈ I t)
    (hclear : ∀ t ∈ Icc (0 : ℝ) T, ∀ x ∈ I t, Disjoint (ball (x : ℂ) r)
      ((fun z => QuantumZipper.fwdMap s.W t z + s.W t) '' A))
    (hb : ∀ t ∈ Icc (0 : ℝ) T, ∀ x ∈ I t, deriv (s.F 0 t) x ∈ Icc (Real.exp (-L₀)) (Real.exp L₀))
    (hmark : ∀ m, IsMarkCoordinate s.W (s.V m) T) (m : Fin n) {t : ℝ} (ht : t ∈ Ioc (0 : ℝ) T) :
    HasDerivWithinAt (fun u => s.B0 u m) (2 * s.A 1 t ^ 2 / (s.B0 t m - s.A 0 t)) (Ioc 0 T) t := by
  have ht' := Ioc_subset_Icc_self ht
  have hd : DifferentiableOn ℝ (s.F 0 t) (I t) := by
    intro x hx
    have hh := (h.ownExt_props ht' (hclear t ht' x hx)).1
    have hdx := hh.differentiableAt (isOpen_ball.mem_nhds (mem_ball_self (by positivity)))
    exact hdx.hasDerivAt.real_of_complex.differentiableAt.differentiableWithinAt
  have hmono := strictMonoOn_of_deriv_pos (hI t ht') hd.continuousOn
    (fun x hx => (Real.exp_pos _).trans_le (hb t ht' x (interior_subset hx)).1)
  have hne : s.B0 t m ≠ s.A 0 t := fun he =>
    (hmark m).ne t ht (hmono.injOn (hVI t ht' m) (hWI t ht') he)
  have he0 : s.A 0 t = s.W' (s.a t) := h.frzA_zero ht'
  have hVF : (ownExt s.W s.W' s.a s.φ t (s.V m t)).re ≠ s.W' (s.a t) := by
    rwa [← he0]
  obtain ⟨ρ, hρ, η, hη, hcl⟩ := exists_fixed_seed_clear hr (hmark m).cont
    (fun u hu => hclear u hu _ (hVI u hu m)) ht'
  rw [he0]
  exact h.hasDerivWithinAt_markVal Ioc_subset_Icc_self ht' ((hmark m).deriv t ht) hρ hη hcl ((hmark m).ne t ht) hVF

/-- **The own map at a positive time is strictly increasing on the extended interval.** -/
theorem strictMonoOn_F_of_clear {n : ℕ} (s : SeedData n) {A : Set ℂ} {T r L₀ : ℝ} {I : ℝ → Set ℝ}
    (h : OwnData s.W A s.φ T s.a s.W') (hr : 0 < r) (hI : ∀ t ∈ Icc (0 : ℝ) T, Convex ℝ (I t))
    (hclear : ∀ t ∈ Icc (0 : ℝ) T, ∀ x ∈ I t, Disjoint (ball (x : ℂ) r)
      ((fun z => QuantumZipper.fwdMap s.W t z + s.W t) '' A))
    (hb : ∀ t ∈ Icc (0 : ℝ) T, ∀ x ∈ I t, deriv (s.F 0 t) x ∈ Icc (Real.exp (-L₀)) (Real.exp L₀)) {t : ℝ}
    (ht : t ∈ Icc (0 : ℝ) T) : StrictMonoOn (s.F 0 t) (I t) := by
  have hd : DifferentiableOn ℝ (s.F 0 t) (I t) := by
    intro x hx
    have hh := (h.ownExt_props ht (hclear t ht x hx)).1
    have hdx := hh.differentiableAt (isOpen_ball.mem_nhds (mem_ball_self (by positivity)))
    exact hdx.hasDerivAt.real_of_complex.differentiableAt.differentiableWithinAt
  exact strictMonoOn_of_deriv_pos (hI t ht) hd.continuousOn
    (fun x hx => (Real.exp_pos _).trans_le (hb t ht x (interior_subset hx)).1)

end Mark

/-! ### The seeded capacity geometry of the G3 column -/

section Geo

variable {X Y : Type*} [mX : MeasurableSpace X] [mY : MeasurableSpace Y]
  {κ x y : ℝ} {P₁ : Measure X} {P₂ : Measure Y} {𝓖₁ : Filtration ℝ≥0 mX} {𝓖₂ : Filtration ℝ≥0 mY}
  [𝓖₁.IsRightContinuous] [𝓖₂.IsRightContinuous] {W₁ : ℝ≥0 → X → ℝ} {VL₁ : Fin 1 → ℝ≥0 → X → ℝ}
  {VR₁ : Fin 3 → ℝ≥0 → X → ℝ} {B₁ : ℝ≥0 → X → ℝ} {ζ₁ : X → ℝ≥0∞} {W₂ : ℝ≥0 → Y → ℝ}
  {VL₂ : Fin 2 → ℝ≥0 → Y → ℝ} {VR₂ : Fin 0 → ℝ≥0 → Y → ℝ} {B₂ : ℝ≥0 → Y → ℝ} {ζ₂ : Y → ℝ≥0∞}

variable (hκ4 : 4 < κ) (hκ8 : κ < 8) (hyx : y < x) (hx : x < 0)
  (h₁ : IsRegMarginal (kh κ) ![0] ![0, x - y, -y] (smallG3RhoL κ) (smallG3RhoR κ) P₁ 𝓖₁ W₁ VL₁ VR₁ B₁ ζ₁)
  (hB₁ : ∀ ω, Continuous (B₁ · ω))
  (hg₁ : ∀ ω, GoodSmallG3 (W₁ · ω) (fun i t => VL₁ i t ω) (fun i t => VR₁ i t ω) (B₁ · ω) (ζ₁ ω))
  (h₂ : IsRegMarginal κ ![x, y] ![] ![κ - 4, -4] ![] P₂ 𝓖₂ W₂ VL₂ VR₂ B₂ ζ₂) (hB₂ : ∀ ω, Continuous (B₂ · ω))

include hκ4 hκ8 hyx hx h₁ hB₁ hg₁ h₂ hB₂

/-- **The image chain of the column starts at the image of the small source**: `W'(0) + y = V_y(σ)`. -/
theorem g3Col_hstart (k : ℕ) (y₀ : Y) {σ : ℝ≥0} (hσ : 0 < σ) (hσS : σ ≤ g3S₂ x y W₂ ζ₂ k y₀)
    (hlive : g3SndLive W₂ VL₂ ζ₂ σ y₀) (x₀ : X) :
    (g3Col κ x y W₁ VL₁ VR₁ ζ₁ W₂ k σ y₀ x₀).W' 0 + y = VL₂ 1 σ y₀ := by
  obtain ⟨hown, -, -, -⟩ := g3Col_facts hκ4 hκ8 hyx hx h₁ hB₁ hg₁ h₂ hB₂ k y₀ hσ hσS x₀
  obtain ⟨hc, hre, -⟩ := large_force_facts (h₂.path y₀) hlive 1 (0 - y)
  have hpt : ((![x, y] : Fin 2 → ℝ) 1 + (0 - y) : ℝ) = 0 := by simp
  rw [hpt] at hc hre
  rw [imgStart_eq_of_ownData hown hc, hre]
  ring

/-- **The seeded capacity geometry of the G3 column** at a live protected frozen time: the seeded capacity driver and
force coordinates (in the order `g3ChargeEquiv` of the small image word) form a `SeedImageGeometry` with the small
image word `(![0], g3SndWordR …)` up to the capacity horizon. -/
theorem g3Col_geometry [IsProbabilityMeasure P₁] (k : ℕ) (y₀ : Y) {σ : ℝ≥0} (hσ : 0 < σ)
    (hσS : σ ≤ g3S₂ x y W₂ ζ₂ k y₀) (hlive : g3SndLive W₂ VL₂ ζ₂ σ y₀) (x₀ : X) :
    SeedImageGeometry (![0] : Fin 1 → ℝ) (g3SndWordR W₂ VL₂ σ y₀) (smallG3RhoL κ) (smallG3RhoR κ)
      (seedCapacityDriver (g3Col κ x y W₁ VL₁ VR₁ ζ₁ W₂ k σ y₀) (g3S₁ x y W₁ ζ₁ k) · x₀)
      (fun i u => seedCapacityForce (g3Col κ x y W₁ VL₁ VR₁ ζ₁ W₂ k σ y₀) (g3S₁ x y W₁ ζ₁ k)
        (g3ChargeEquiv (.inl i)) u x₀)
      (fun j u => seedCapacityForce (g3Col κ x y W₁ VL₁ VR₁ ζ₁ W₂ k σ y₀) (g3S₁ x y W₁ ζ₁ k)
        (g3ChargeEquiv (.inr j)) u x₀)
      (seedCapacityHorizon (g3Col κ x y W₁ VL₁ VR₁ ζ₁ W₂ k σ y₀) (g3S₁ x y W₁ ζ₁ k) x₀) := by
  have hqlo : 0 < x - y := by linarith
  have hqlox : x - y < -y := by linarith
  have hne : (goodIdxG (-y) (x - y) ![x - y]).Nonempty :=
    goodIdxG_nonempty hqlo hqlox (fun m => by fin_cases m; simp; linarith) (fun m => by fin_cases m; simp; linarith)
  have hF := isEnclFamily_cofG hne
  obtain ⟨-, hgood₁, hsep₁, hsepO, -, -, -, -, -, -⟩ :=
    g3_rect hκ4 hκ8 hyx hx h₁.path hg₁ hB₁ h₂.path hB₂ hF
  obtain ⟨hpp, hrec, hcol⟩ := g3_isSourceColumnG hκ4 hκ8 hyx hx h₁ hB₁ hg₁ h₂ hB₂ k y₀ (σ := (σ : ℝ))
    (by exact_mod_cast hσ) (by exact_mod_cast hσS)
  obtain ⟨hCc, hCs, c, hc, hClb⟩ := clock_facts_of_column hpp hcol
  obtain ⟨hownP, hWj, -, -⟩ := g3Col_facts hκ4 hκ8 hyx hx h₁ hB₁ hg₁ h₂ hB₂ k y₀ hσ hσS x₀
  have hstart := g3Col_hstart hκ4 hκ8 hyx hx h₁ hB₁ hg₁ h₂ hB₂ k y₀ hσ hσS hlive x₀
  have hword := smallG3_isSeedWord hκ4 hκ8 hyx (h₂.path y₀) hlive
  obtain ⟨hW0₁, hL0₁, hR0₁, -, -, -, -, hLw₁, hwR₁, -⟩ := h₁.path x₀
  set T : ℝ := (g3S₁ x y W₁ ζ₁ k x₀ : ℝ) with hTdef
  set s := g3Col κ x y W₁ VL₁ VR₁ ζ₁ W₂ k σ y₀ x₀ with hs
  set Wf := frzPath W₂ (-y) σ y₀ with hWf
  have r := hrec x₀
  have h : OwnData s.W (fwdHull Wf σ) s.φ T s.a s.W' := r.own
  have hφ : s.φ = fun z => fwdMap Wf σ z + Wf σ := congrArg SeedData.φ r.source
  have hownF : OwnData s.W (fwdHull Wf σ) (fun z => fwdMap Wf σ z + Wf σ) T s.a s.W' := by rw [← hφ]; exact h
  have hζ₀ : s.ζ₀ = Wf σ := congrArg SeedData.ζ₀ r.source
  -- clearance, derivative bounds and the alive frozen tip
  have hW0H : ((s.W 0 : ℝ) : ℂ) ∈ closure (cofGH₁ (-y) (x - y) ![x - y] k) :=
    closure_mono r.sub₁ (start_mem_closure_fwdHull h.cont h.pos)
  have hWfH : ((Wf 0 : ℝ) : ℂ) ∈ closure (cofGH₂ (-y) (x - y) ![x - y] k) := by
    rw [r.zeroW₂]; exact hpp.pair.src
  have hqWf : cofGq (-y) (x - y) ![x - y] k < Wf 0 := by rw [r.zeroW₂]; exact hpp.pair.prot_lt
  obtain ⟨rr, L₀, hrr, -, hinterval⟩ := exists_ext_interval_own_bounds_right hpp.pair.hull₁ hpp.pair.hull₂
    hpp.pair.sep_pos hpp.pair.sep hpp.pair.prot_pos hpp.pair.rad_pos hpp.pair.prot hpp.seg
    (cofGTm (-y) (x - y) ![x - y] k)
  have hII := fun t (ht : t ∈ Icc (0 : ℝ) T) xx (hxx : xx ∈ uIcc (Strip.extPath (VL₁ 0 · x₀) t)
      ((fwdMap s.W t (cofGq (-y) (x - y) ![x - y] k)).re + s.W t)) =>
    hinterval s.W Wf (Strip.extPath (VL₁ 0 · x₀)) (Strip.extPath (VR₁ 0 · x₀)) T σ s.a s.W' hownF r.contW₂ r.pos₂
      hW0H hWfH hqWf r.le₂ r.sub₁ r.sub₂ r.lo r.hi t ht xx hxx
  have hint := fun t ht xx hxx => (hII t ht xx hxx).1
  have hb : ∀ t ∈ Icc (0 : ℝ) T, ∀ xx ∈ uIcc (Strip.extPath (VL₁ 0 · x₀) t)
      ((fwdMap s.W t (cofGq (-y) (x - y) ![x - y] k)).re + s.W t),
      deriv (s.F 0 t) xx ∈ Icc (Real.exp (-L₀)) (Real.exp L₀) := fun t ht xx hxx => by
    have := (hII t ht xx hxx).2
    rw [← hφ] at this
    exact this
  obtain ⟨r₀', a₀, γ, Γ, lam, hr₀, ha₀, -, hd9⟩ :=
    exists_twoCurveD9 hpp.pair.hull₁ hpp.pair.hull₂ hpp.pair.sep_pos hpp.pair.sep hpp.pair.rad_pos
      hpp.pair.prot_pos hpp.pair.prot (p := (Fin.elim0 : Fin 0 → ℝ)) (fun m => Fin.elim0 m) (fun m => Fin.elim0 m)
      (cofGTm (-y) (x - y) ![x - y] k)
  obtain ⟨v₀, hv₀⟩ : ∃ v, IsForwardSol s.W' s.ζ₀ (s.a T) v := by
    rw [hζ₀]
    exact (hd9 s.W Wf σ T s.a s.W' 0 Fin.elim0 hownF r.contW₂ hWfH hqWf r.pos₂ r.le₂ r.le₁ r.sub₁ r.sub₂).alive₀
  have hne0 : ∀ u ∈ Icc (0 : ℝ) T, frzImg s.W' s.a s.ζ₀ u ≠ s.A 0 u := fun u hu =>
    sub_ne_zero.1 (h.frzImg_sub_ne_zero hv₀ hu)
  -- continuity and image equations of the marks
  have hcB0 : ∀ m, ContinuousOn (fun t => s.B0 t m) (Icc 0 T) := by
    intro m
    have hds : ContinuousOn (fun u => dslope (s.F 0 u) (s.W u) (s.V m u)) (Icc 0 T) :=
      h.continuousOn_dslope_moving hrr h.cont.continuousOn (r.mark m).cont
        (fun u hu => hint u hu _ (r.drv u hu)) (fun u hu => hint u hu _ (r.marks u hu m))
    refine ((h.continuousOn_frzA 0).add (((r.mark m).cont.sub h.cont.continuousOn).mul hds)).congr fun u _ => ?_
    have he := sub_smul_dslope (s.F 0 u) (s.W u) (s.V m u)
    simp only [smul_eq_mul] at he
    show s.F 0 u (s.V m u) = s.F 0 u (s.W u) + (s.V m u - s.W u) * dslope (s.F 0 u) (s.W u) (s.V m u)
    linarith only [he]
  have hlt₁ : (g3S₁ x y W₁ ζ₁ k x₀ : ℝ≥0∞) < ζ₁ x₀ := (hgood₁ k x₀).1
  have htn : ∀ t ∈ Icc (0 : ℝ) T, (t.toNNReal : ℝ≥0∞) < ζ₁ x₀ := fun t ht =>
    lt_of_le_of_lt (ENNReal.coe_le_coe.2 (Real.toNNReal_le_iff_le_coe.2 ht.2)) hlt₁
  have hWt : ∀ t ∈ Icc (0 : ℝ) T, s.W t = W₁ t.toNNReal x₀ := fun t ht => hWj ht
  have hrate : ∀ m, ∀ t ∈ Icc (0 : ℝ) T,
      IntervalIntegrable (fun u => 2 / (s.V m u - s.W u)) volume 0 t := by
    intro m t ht
    fin_cases m
    · exact r.lo.integrable t ht
    · exact r.hi.integrable t ht
    · refine intervalIntegrable_rate_of_ne h.cont.continuousOn (r.mark 2).cont (fun u hu => ?_) t ht
      have hV' : s.V 2 u = VR₁ 1 u.toNNReal x₀ := rfl
      rw [hV', hWt u hu]
      exact hsepO x₀ _ (htn u hu)
  have hi := imageEntranceIntegrable_of_rate s h hrr (fun t _ => convex_uIcc _ _) r.drv r.marks hint hb
    (fun m => (r.mark m).cont) hrate
  have himark := s.integrated_image_marks hcB0
    (fun m u hu => hasDerivWithinAt_image_mark s h hrr (fun t _ => convex_uIcc _ _) r.drv r.marks hint hb r.mark m hu)
    hi
  -- the sides at positive times
  have hmono := fun t (ht : t ∈ Icc (0 : ℝ) T) =>
    strictMonoOn_F_of_clear s h hrr (fun t _ => convex_uIcc _ _) hint hb ht
  have hside : ∀ t ∈ Ioc (0 : ℝ) T, s.V 0 t < s.W t ∧ s.W t < s.V 1 t ∧ s.W t < s.V 2 t := by
    intro t ht
    have ht' := Ioc_subset_Icc_self ht
    have hpos : 0 < t.toNNReal := Real.toNNReal_pos.2 ht.1
    have hV0 : s.V 0 t = VL₁ 0 t.toNNReal x₀ := rfl
    have hV1 : s.V 1 t = VR₁ 0 t.toNNReal x₀ := rfl
    have hV2 : s.V 2 t = VR₁ 1 t.toNNReal x₀ := rfl
    obtain ⟨hn0, hn1⟩ := hsep₁ x₀ t.toNNReal hpos (htn t ht')
    rw [hV0, hV1, hV2, hWt t ht']
    exact ⟨lt_of_le_of_ne (hLw₁ _ (htn t ht') 0) hn0, lt_of_le_of_ne (hwR₁ _ (htn t ht') 0) (Ne.symm hn1),
      lt_of_le_of_ne (hwR₁ _ (htn t ht') 1) (Ne.symm (hsepO x₀ _ (htn t ht')))⟩
  have hBlt : ∀ m, ∀ t ∈ Icc (0 : ℝ) T, s.V m t < s.W t → s.B0 t m < s.A 0 t := fun m t ht hlt =>
    hmono t ht (r.marks t ht m) (r.drv t ht) hlt
  have hBgt : ∀ m, ∀ t ∈ Icc (0 : ℝ) T, s.W t < s.V m t → s.A 0 t < s.B0 t m := fun m t ht hlt =>
    hmono t ht (r.drv t ht) (r.marks t ht m) hlt
  -- the initial word
  have hA00 : s.A 0 0 = s.W' 0 := A1MultiMark.A_zero_zero s h
  have hW0 : s.W 0 = 0 := h.zero
  have hV00 : s.V 0 0 = 0 := by
    show VL₁ 0 (0 : ℝ).toNNReal x₀ = 0
    rw [Real.toNNReal_zero]; exact hL0₁ 0
  have hV10 : s.V 1 0 = 0 := by
    show VR₁ 0 (0 : ℝ).toNNReal x₀ = 0
    rw [Real.toNNReal_zero]; exact hR0₁ 0
  have hV20 : s.V 2 0 = x - y := by
    show VR₁ 1 (0 : ℝ).toNNReal x₀ = x - y
    rw [Real.toNNReal_zero]; exact hR0₁ 1
  have hWfσ : Wf σ = W₂ σ y₀ - y := by
    show stopDrv (Strip.extPath (W₂ · y₀)) σ σ + -y = W₂ σ y₀ - y
    rw [stopDrv_eqOn _ σ ⟨σ.coe_nonneg, le_rfl⟩]
    simp [Strip.extPath, sub_eq_add_neg]
  have hφP : s.φ = physMap (0 - y) (Strip.extPath (W₂ · y₀)) σ := by
    rw [hφ, zero_sub]
    exact frzChart_frzPath_eq W₂ (-y) σ.coe_nonneg y₀
  obtain ⟨hcx, hrex, hnotx⟩ := large_force_facts (h₂.path y₀) hlive 0 (0 - y)
  have hptx : ((![x, y] : Fin 2 → ℝ) 0 + (0 - y) : ℝ) = x - y := by simp; ring
  rw [hptx] at hcx hrex hnotx
  have hB02 : s.B0 0 2 = (0 - y) + VL₂ 0 σ y₀ := by
    show (ownExt s.W s.W' s.a s.φ 0 (s.V 2 0)).re = _
    rw [hV20, hφP, ownExt_zero_eq hownP hnotx hcx]
    exact hrex
  have hlt₂ : VL₂ 1 σ y₀ < W₂ σ y₀ := by
    have hP := h₂.path y₀
    obtain ⟨-, -, -, -, -, -, hanti, -⟩ := hP
    exact lt_of_le_of_lt (hanti σ hlive.1 (show (0 : Fin 2) ≤ 1 by decide)) (hlive.2 σ le_rfl)
  have hζW' : s.W' 0 < s.ζ₀ := by
    rw [hζ₀, hWfσ]
    linarith only [hstart, hlt₂]
  -- assembly
  refine seedImageGeometry_capForce (d := g3Col κ x y W₁ VL₁ VR₁ ζ₁ W₂ k σ y₀) (S := g3S₁ x y W₁ ζ₁ k)
    (fun ω => (hrec ω).own) hCc hCs hc hClb
    (fun i ω t => (g3Col κ x y W₁ VL₁ VR₁ ζ₁ W₂ k σ y₀ ω).imageForce t (g3ChargeEquiv (.inl i)))
    (fun j ω t => (g3Col κ x y W₁ VL₁ VR₁ ζ₁ W₂ k σ y₀ ω).imageForce t (g3ChargeEquiv (.inr j))) hword x₀
    (fun i => ?_) (fun j => ?_) (fun i t ht => ?_) (fun j t ht => ?_) (fun i t ht => ?_) (fun j t ht => ?_)
    (fun i => ?_) (fun j => ?_)
  · fin_cases i
    exact hcB0 0
  · fin_cases j
    · exact hcB0 1
    · exact hcB0 2
    · exact A1MultiMark.continuousOn_frzImg s h hv₀
  · fin_cases i
    exact ⟨hi 0 t ht, himark 0 t ht⟩
  · fin_cases j
    · exact ⟨hi 1 t ht, himark 1 t ht⟩
    · exact ⟨hi 2 t ht, himark 2 t ht⟩
    · exact A1MultiMark.ownImageEq_frozen s h hv₀ hne0 t ht
  · fin_cases i
    exact hBlt 0 t (Ioc_subset_Icc_self ht) (hside t ht).1
  · fin_cases j
    · exact hBgt 1 t (Ioc_subset_Icc_self ht) (hside t ht).2.1
    · exact hBgt 2 t (Ioc_subset_Icc_self ht) (hside t ht).2.2
    · exact A1MultiMark.A0_lt_frzImg s h hv₀ hne0 hζW' t (Ioc_subset_Icc_self ht)
  · fin_cases i
    show s.F 0 0 (s.V 0 0) - s.F 0 0 (s.W 0) = 0
    rw [hV00, hW0, sub_self]
  · fin_cases j
    · show s.F 0 0 (s.V 1 0) - s.F 0 0 (s.W 0) = 0
      rw [hV10, hW0, sub_self]
    · show s.B0 0 2 - s.A 0 0 = VL₂ 0 σ y₀ - VL₂ 1 σ y₀
      rw [hB02, hA00]
      linarith only [hstart]
    · show frzImg s.W' s.a s.ζ₀ 0 - s.A 0 0 = W₂ σ y₀ - VL₂ 1 σ y₀
      rw [A1MultiMark.frzImg_zero s h hζW'.ne', hA00, hζ₀, hWfσ]
      linarith only [hstart]

end Geo

end InteractingSLE.ZhanGT4.A1G3L2
