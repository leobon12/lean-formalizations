/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.ZhanGT4.A1ESndId
import InteractingSLE.Spec.ZhanGT4.A1G3L2SndGeo

/-!
# Zhan's A.1 under R83, (Eight), small-curve direction: the seeded capacity geometry of the column

Packet PROVE-A1-EIGHTSND (mirror of PROVE-A1-G3LAW2's `A1G3L2SndGeo`). At a frozen sample `y₀` live at a protected
frozen time `σ ∈ (0, S₂ᵏ(y₀)]` and every small sample `x₀`, for the record `s = eightCol … k σ y₀ x₀`:

* `largeEight_force_facts`: the frozen chart of the large curve (physical map shifted by `c`) is continuous at the image
  `x + c` of its mark, its real part there is `c + V(σ)`, and `x + c` is off the closed frozen hull (it is alive);
* **`eightCol_hstart`**: the record's image chain starts at `V(σ) − x` (`W'(0) + x = V(σ)`);
* **`eightCol_geometry`**: the seeded capacity coordinates of the column form a `SeedImageGeometry` with the small image
  word `(![0], ![0, W(σ) − V(σ)])` (A1-MULTIMARK's `seedImageGeometry_capForce`: image equations of the seeds (A22's
  `hasDerivWithinAt_image_seed`, entrance integrability of seeds) and of the frozen tip, positive-time sides from the
  monotone own map, the initial word).
-/

set_option autoImplicit false

noncomputable section

open Complex Set Filter Topology Metric MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace InteractingSLE.ZhanGT4.A1ESnd

open QuantumZipper (H fwdHull fwdMap IsForwardSol)
open A2X A1Ref A1Canon A1Core A1Frozen A1Marg A1Law A1Patch A1SeedField A1EightSeed A1G3Calc A1Common A1EightFin
  A1Asm A1Family A1Forces A1RLaw A1LargeDens A1ELaw A1G3L2 A1SeedGeom A1MultiMark

/-! ### The large curve's mark in the frozen chart -/

section Large

variable {κ x : ℝ} {W : ℝ≥0 → ℝ} {VL : Fin 1 → ℝ≥0 → ℝ} {VR : Fin 0 → ℝ≥0 → ℝ} {B : ℝ≥0 → ℝ} {ζ : ℝ≥0∞}

/-- **The large Eight curve's mark in its frozen chart**: at a live time `σ` (strip life), for each shift `c`, the
physical map `physMap c W σ` is continuous at `x + c`, has real part `c + V(σ)` there, and `x + c` is off the closed
physical hull. -/
theorem largeEight_force_facts (hP : IsIntegratedSLEPath κ ![x] ![] ![0] ![] W VL VR B ζ)
    {σ : ℝ≥0} (hlive : Strip.IsStripLife W (VL 0) ζ σ) (c : ℝ) :
    ContinuousAt (physMap c (Strip.extPath W) σ) (((![x] : Fin 1 → ℝ) 0 + c : ℝ) : ℂ) ∧
      (physMap c (Strip.extPath W) σ (((![x] : Fin 1 → ℝ) 0 + c : ℝ) : ℂ)).re = c + VL 0 σ ∧
      (((![x] : Fin 1 → ℝ) 0 + c : ℝ) : ℂ) ∉ closure (physHull c (Strip.extPath W) σ) := by
  obtain ⟨-, -, -, hcw, hcL, -, -, -, -, -, -, -, -, hLeq, -⟩ := hP
  have hsep : ∀ r ≤ σ, VL 0 r ≠ W r := fun r hr => (hlive.2 r hr).ne
  have hu := isForwardSol_extPath_of_force (hcL 0) hcw (fun t ht => hLeq t ht 0) hlive.1 hsep
  obtain ⟨τ', hστ', hcτ⟩ := A1Ref.exists_continuousOn_extPath_beyond hcw hlive.1
  have hf := continuousAt_fwdMap_of_isForwardSol hστ' σ.coe_nonneg hcτ hu
  have hpt : (((![x] : Fin 1 → ℝ) 0 + c : ℝ) : ℂ) - (c : ℂ) = ((((![x] : Fin 1 → ℝ) 0 : ℝ)) : ℂ) := by
    push_cast; ring
  refine ⟨?_, ?_, ?_⟩
  · have hg : ContinuousAt (fun z : ℂ => fwdMap (Strip.extPath W) σ (z - c))
        (((![x] : Fin 1 → ℝ) 0 + c : ℝ) : ℂ) :=
      ContinuousAt.comp_of_eq hf (continuousAt_id.sub continuousAt_const) hpt
    have e : physMap c (Strip.extPath W) σ =
        fun z => ((c : ℂ) + (Strip.extPath W σ : ℂ)) + fwdMap (Strip.extPath W) σ (z - c) := rfl
    rw [e]
    exact continuousAt_const.add hg
  · have hval := A1SeedField.fwdMap_add_eq_force (hcL 0) (fun t ht => hLeq t ht 0) hlive.1
      hsep (A1Ref.continuousOn_extPath_Icc hcw (by rw [ENNReal.ofReal_coe_nnreal]; exact hlive.1))
      (fun _ _ => rfl) ⟨σ.coe_nonneg, le_rfl⟩
    simp only [physMap, hpt, add_re, ofReal_re]
    have he : Strip.extPath (VL 0) (σ : ℝ) = VL 0 σ := by simp [Strip.extPath]
    rw [he] at hval
    linarith only [hval]
  · set V := stopDrv (Strip.extPath W) τ' with hVdef
    have hVc : Continuous V := continuous_stopDrv hcτ (σ.coe_nonneg.trans hστ'.le)
    have hVe : EqOn (Strip.extPath W) V (Icc 0 τ') := (stopDrv_eqOn _ τ').symm
    have hu' : IsForwardSol V ((((![x] : Fin 1 → ℝ) 0 : ℝ)) : ℂ) σ _ := QuantumZipper.isForwardSol_congr_drive
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
    have hz' : z = ((((![x] : Fin 1 → ℝ) 0 : ℝ)) : ℂ) := by
      have h1 : z + c = (((![x] : Fin 1 → ℝ) 0 + c : ℝ) : ℂ) := hze
      rw [← hpt, ← h1]; ring
    rw [hz'] at hz
    exact hnot hz

end Large

/-! ### The seeded capacity geometry of the Eight column -/

section Geo

variable {X Y : Type*} [mX : MeasurableSpace X] [mY : MeasurableSpace Y]
  {κ x : ℝ} {P₁ : Measure X} {P₂ : Measure Y} {𝓖₁ : Filtration ℝ≥0 mX} {𝓖₂ : Filtration ℝ≥0 mY}
  [𝓖₁.IsRightContinuous] {W₁ : ℝ≥0 → X → ℝ} {VL₁ : Fin 1 → ℝ≥0 → X → ℝ} {VR₁ : Fin 2 → ℝ≥0 → X → ℝ}
  {B₁ : ℝ≥0 → X → ℝ} {ζ₁ : X → ℝ≥0∞} {W₂ : ℝ≥0 → Y → ℝ} {VL₂ : Fin 1 → ℝ≥0 → Y → ℝ}
  {VR₂ : Fin 0 → ℝ≥0 → Y → ℝ} {B₂ : ℝ≥0 → Y → ℝ} {ζ₂ : Y → ℝ≥0∞}

variable (hκ8 : 8 ≤ κ) (hx : x < 0)
  (h₁ : IsRegMarginal (kh κ) ![0] ![0, -x] (smallEightRhoL κ) (smallEightRhoR κ) P₁ 𝓖₁ W₁ VL₁ VR₁ B₁ ζ₁)
  (hB₁ : ∀ ω, Continuous (B₁ · ω))
  (hg₁ : ∀ ω, GoodSmallEight (W₁ · ω) (fun i t => VL₁ i t ω) (fun i t => VR₁ i t ω) (B₁ · ω) (ζ₁ ω))
  (h₂ : IsRegMarginal κ ![x] ![] ![0] ![] P₂ 𝓖₂ W₂ VL₂ VR₂ B₂ ζ₂) (hB₂ : ∀ ω, Continuous (B₂ · ω))

include hκ8 hx h₁ hB₁ hg₁ h₂ hB₂

omit [𝓖₁.IsRightContinuous] in
/-- **The image chain of the column starts at the image of the small source**: `W'(0) + x = V(σ)`. -/
theorem eightCol_hstart (k : ℕ) (y₀ : Y) {σ : ℝ≥0} (hσ : 0 < σ) (hσS : σ ≤ eightS₂ x W₂ ζ₂ k y₀)
    (hlive : eightSndLive W₂ VL₂ ζ₂ σ y₀) (x₀ : X) :
    (eightCol κ x W₁ VL₁ VR₁ ζ₁ W₂ k σ y₀ x₀).W' 0 + x = VL₂ 0 σ y₀ := by
  obtain ⟨hown, -, -, -⟩ := eightCol_facts hκ8 hx h₁ hB₁ hg₁ h₂ hB₂ k y₀ hσ hσS x₀
  obtain ⟨hc, hre, -⟩ := largeEight_force_facts (h₂.path y₀) hlive (0 - x)
  have hpt : ((![x] : Fin 1 → ℝ) 0 + (0 - x) : ℝ) = 0 := by simp
  rw [hpt] at hc hre
  rw [imgStart_eq_of_ownData hown hc, hre]
  ring

/-- **The seeded capacity geometry of the Eight column** at a live protected frozen time: the seeded capacity driver
and force coordinates (in the order `eightChargeEquiv` of the small image word) form a `SeedImageGeometry` with the
small image word `(![0], eightSndWordR …)` up to the capacity horizon. -/
theorem eightCol_geometry [IsProbabilityMeasure P₁] (k : ℕ) (y₀ : Y) {σ : ℝ≥0} (hσ : 0 < σ)
    (hσS : σ ≤ eightS₂ x W₂ ζ₂ k y₀) (hlive : eightSndLive W₂ VL₂ ζ₂ σ y₀) (x₀ : X) :
    SeedImageGeometry (![0] : Fin 1 → ℝ) (eightSndWordR W₂ VL₂ σ y₀) (smallEightRhoL κ) (smallEightRhoR κ)
      (seedCapacityDriver (eightCol κ x W₁ VL₁ VR₁ ζ₁ W₂ k σ y₀) (eightS₁ x W₁ ζ₁ k) · x₀)
      (fun i u => seedCapacityForce (eightCol κ x W₁ VL₁ VR₁ ζ₁ W₂ k σ y₀) (eightS₁ x W₁ ζ₁ k)
        (eightChargeEquiv (.inl i)) u x₀)
      (fun j u => seedCapacityForce (eightCol κ x W₁ VL₁ VR₁ ζ₁ W₂ k σ y₀) (eightS₁ x W₁ ζ₁ k)
        (eightChargeEquiv (.inr j)) u x₀)
      (seedCapacityHorizon (eightCol κ x W₁ VL₁ VR₁ ζ₁ W₂ k σ y₀) (eightS₁ x W₁ ζ₁ k) x₀) := by
  obtain ⟨hR1, hsep₁, -, -⟩ := eight_rect_facts hκ8 hx h₁ hB₁ hg₁ h₂ hB₂
  obtain ⟨hpp, -⟩ := eight_isSourceColumn hκ8 hx h₁ hB₁ hg₁ h₂ hB₂ k y₀ (σ := (σ : ℝ)) (by exact_mod_cast hσ)
    (by exact_mod_cast hσS)
  have hrec := fun ω => eight_isSourceRecord hκ8 hx h₁ hB₁ hg₁ h₂ hB₂ k y₀ (σ := (σ : ℝ)) (by exact_mod_cast hσ)
    (by exact_mod_cast hσS) ω
  obtain ⟨hCc, hCs, c, hc, hClb⟩ := eightCol_clock hκ8 hx h₁ hB₁ hg₁ h₂ hB₂ k y₀ hσ hσS
  have hstart := eightCol_hstart hκ8 hx h₁ hB₁ hg₁ h₂ hB₂ k y₀ hσ hσS hlive x₀
  have hword := smallEight_isSeedWord (W := (W₂ · y₀)) (VL := fun i t => VL₂ i t y₀) hκ8 hlive
  obtain ⟨hW0₁, hL0₁, hR0₁, -, -, -, -, hLw₁, hwR₁, -⟩ := h₁.path x₀
  set T : ℝ := (eightS₁ x W₁ ζ₁ k x₀ : ℝ) with hTdef
  set s := eightCol κ x W₁ VL₁ VR₁ ζ₁ W₂ k σ y₀ x₀ with hs
  set Wf := frzPath W₂ (-x) σ y₀ with hWf
  have r := hrec x₀
  have h : OwnData s.W (fwdHull Wf σ) s.φ T s.a s.W' := r.own
  have hφ : s.φ = fun z => fwdMap Wf σ z + Wf σ := congrArg SeedData.φ r.source
  have hownF : OwnData s.W (fwdHull Wf σ) (fun z => fwdMap Wf σ z + Wf σ) T s.a s.W' := by rw [← hφ]; exact h
  have hζ₀ : s.ζ₀ = Wf σ := congrArg SeedData.ζ₀ r.source
  -- clearance, derivative bounds and the alive frozen tip
  have hW0H : ((s.W 0 : ℝ) : ℂ) ∈ closure (cofH₁ (-x) ![] k) :=
    closure_mono r.sub₁ (start_mem_closure_fwdHull h.cont h.pos)
  have hWfH : ((Wf 0 : ℝ) : ℂ) ∈ closure (cofH₂ (-x) ![] k) := by
    rw [r.zeroW₂]; exact hpp.src
  have hWq : s.W 0 < cofq (-x) ![] k := by rw [h.zero]; exact hpp.prot_pos
  have hqWf : cofq (-x) ![] k < Wf 0 := by rw [r.zeroW₂]; exact hpp.prot_lt
  obtain ⟨rr, L₀, hrr, -, hinterval⟩ := exists_seed_interval_own_bounds_right hpp.hull₁ hpp.hull₂
    hpp.sep_pos hpp.sep hpp.rad_pos hpp.prot (cofTm (-x) ![] k)
  have hII := fun t (ht : t ∈ Icc (0 : ℝ) T) xx (hxx : xx ∈ uIcc (Strip.extPath (VL₁ 0 · x₀) t)
      (Strip.extPath (VR₁ 0 · x₀) t)) =>
    hinterval s.W Wf (Strip.extPath (VL₁ 0 · x₀)) (Strip.extPath (VR₁ 0 · x₀)) T σ s.a s.W' hownF r.contW₂ r.pos₂
      hW0H hWfH hWq hqWf r.le₂ r.sub₁ r.sub₂ r.lo r.hi t ht xx hxx
  have hint := fun t ht xx hxx => (hII t ht xx hxx).1
  have hb : ∀ t ∈ Icc (0 : ℝ) T, ∀ xx ∈ uIcc (Strip.extPath (VL₁ 0 · x₀) t) (Strip.extPath (VR₁ 0 · x₀) t),
      deriv (s.F 0 t) xx ∈ Icc (Real.exp (-L₀)) (Real.exp L₀) := fun t ht xx hxx => by
    have := (hII t ht xx hxx).2
    rw [← hφ] at this
    exact this
  obtain ⟨r₀', a₀, γ, Γ, lam, hr₀, ha₀, -, hd9⟩ :=
    exists_twoCurveD9 hpp.hull₁ hpp.hull₂ hpp.sep_pos hpp.sep hpp.rad_pos
      hpp.prot_pos hpp.prot (p := (Fin.elim0 : Fin 0 → ℝ)) (fun m => Fin.elim0 m) (fun m => Fin.elim0 m)
      (cofTm (-x) ![] k)
  obtain ⟨v₀, hv₀⟩ : ∃ v, IsForwardSol s.W' s.ζ₀ (s.a T) v := by
    rw [hζ₀]
    exact (hd9 s.W Wf σ T s.a s.W' 0 Fin.elim0 hownF r.contW₂ hWfH hqWf r.pos₂ r.le₂ r.le₁ r.sub₁ r.sub₂).alive₀
  have hne0 : ∀ u ∈ Icc (0 : ℝ) T, frzImg s.W' s.a s.ζ₀ u ≠ s.A 0 u := fun u hu =>
    sub_ne_zero.1 (h.frzImg_sub_ne_zero hv₀ hu)
  -- continuity and image equations of the seeds
  have hcB0 : ∀ m, ContinuousOn (fun t => s.B0 t m) (Icc 0 T) := by
    intro m
    have hds : ContinuousOn (fun u => dslope (s.F 0 u) (s.W u) (s.V m u)) (Icc 0 T) :=
      h.continuousOn_dslope_moving hrr h.cont.continuousOn (r.seed m).cont
        (fun u hu => hint u hu _ (r.drv u hu)) (fun u hu => hint u hu _ (r.marks u hu m))
    refine ((h.continuousOn_frzA 0).add (((r.seed m).cont.sub h.cont.continuousOn).mul hds)).congr fun u _ => ?_
    have he := sub_smul_dslope (s.F 0 u) (s.W u) (s.V m u)
    simp only [smul_eq_mul] at he
    show s.F 0 u (s.V m u) = s.F 0 u (s.W u) + (s.V m u - s.W u) * dslope (s.F 0 u) (s.W u) (s.V m u)
    linarith only [he]
  have hlt₁ : (eightS₁ x W₁ ζ₁ k x₀ : ℝ≥0∞) < ζ₁ x₀ := (hR1 k x₀).1
  have htn : ∀ t ∈ Icc (0 : ℝ) T, (t.toNNReal : ℝ≥0∞) < ζ₁ x₀ := fun t ht =>
    lt_of_le_of_lt (ENNReal.coe_le_coe.2 (Real.toNNReal_le_iff_le_coe.2 ht.2)) hlt₁
  have hWt : ∀ t ∈ Icc (0 : ℝ) T, s.W t = W₁ t.toNNReal x₀ := fun t ht => eightDrv_eqOn W₁ (eightS₁ x W₁ ζ₁) k x₀ ht
  have hi := s.imageEntranceIntegrable_of_seed h hrr (fun t _ => convex_uIcc _ _) r.drv r.marks hint hb r.seed
  have himark := s.integrated_image_marks hcB0
    (fun m u hu => s.hasDerivWithinAt_image_seed h hrr (fun t _ => convex_uIcc _ _) r.drv r.marks hint hb r.seed m hu)
    hi
  -- the sides at positive times
  have hmono := fun t (ht : t ∈ Icc (0 : ℝ) T) =>
    strictMonoOn_F_of_clear s h hrr (fun t _ => convex_uIcc _ _) hint hb ht
  have hside : ∀ t ∈ Ioc (0 : ℝ) T, s.V 0 t < s.W t ∧ s.W t < s.V 1 t := by
    intro t ht
    have ht' := Ioc_subset_Icc_self ht
    have hpos : 0 < t.toNNReal := Real.toNNReal_pos.2 ht.1
    have hV0 : s.V 0 t = VL₁ 0 t.toNNReal x₀ := rfl
    have hV1 : s.V 1 t = VR₁ 0 t.toNNReal x₀ := rfl
    obtain ⟨hn0, hn1⟩ := hsep₁ x₀ t.toNNReal hpos (htn t ht')
    rw [hV0, hV1, hWt t ht']
    exact ⟨lt_of_le_of_ne (hLw₁ _ (htn t ht') 0) hn0, lt_of_le_of_ne (hwR₁ _ (htn t ht') 0) (Ne.symm hn1)⟩
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
  have hWfσ : Wf σ = W₂ σ y₀ - x := by
    show stopDrv (Strip.extPath (W₂ · y₀)) σ σ + -x = W₂ σ y₀ - x
    rw [stopDrv_eqOn _ σ ⟨σ.coe_nonneg, le_rfl⟩]
    simp [Strip.extPath, sub_eq_add_neg]
  have hlt₂ : VL₂ 0 σ y₀ < W₂ σ y₀ := hlive.2 σ le_rfl
  have hζW' : s.W' 0 < s.ζ₀ := by
    rw [hζ₀, hWfσ]
    linarith only [hstart, hlt₂]
  -- assembly
  refine seedImageGeometry_capForce (d := eightCol κ x W₁ VL₁ VR₁ ζ₁ W₂ k σ y₀) (S := eightS₁ x W₁ ζ₁ k)
    (fun ω => (hrec ω).own) hCc hCs hc hClb
    (fun i ω t => (eightCol κ x W₁ VL₁ VR₁ ζ₁ W₂ k σ y₀ ω).imageForce t (eightChargeEquiv (.inl i)))
    (fun j ω t => (eightCol κ x W₁ VL₁ VR₁ ζ₁ W₂ k σ y₀ ω).imageForce t (eightChargeEquiv (.inr j))) hword x₀
    (fun i => ?_) (fun j => ?_) (fun i t ht => ?_) (fun j t ht => ?_) (fun i t ht => ?_) (fun j t ht => ?_)
    (fun i => ?_) (fun j => ?_)
  · fin_cases i
    exact hcB0 0
  · fin_cases j
    · exact hcB0 1
    · exact A1MultiMark.continuousOn_frzImg s h hv₀
  · fin_cases i
    exact ⟨hi 0 t ht, himark 0 t ht⟩
  · fin_cases j
    · exact ⟨hi 1 t ht, himark 1 t ht⟩
    · exact A1MultiMark.ownImageEq_frozen s h hv₀ hne0 t ht
  · fin_cases i
    exact hBlt 0 t (Ioc_subset_Icc_self ht) (hside t ht).1
  · fin_cases j
    · exact hBgt 1 t (Ioc_subset_Icc_self ht) (hside t ht).2
    · exact A1MultiMark.A0_lt_frzImg s h hv₀ hne0 hζW' t (Ioc_subset_Icc_self ht)
  · fin_cases i
    show s.F 0 0 (s.V 0 0) - s.F 0 0 (s.W 0) = 0
    rw [hV00, hW0, sub_self]
  · fin_cases j
    · show s.F 0 0 (s.V 1 0) - s.F 0 0 (s.W 0) = 0
      rw [hV10, hW0, sub_self]
    · show frzImg s.W' s.a s.ζ₀ 0 - s.A 0 0 = W₂ σ y₀ - VL₂ 0 σ y₀
      rw [A1MultiMark.frzImg_zero s h hζW'.ne', hA00, hζ₀, hWfσ]
      linarith only [hstart]

end Geo

end InteractingSLE.ZhanGT4.A1ESnd
