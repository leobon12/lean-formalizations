/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.WangWu.Prop418RangeCode
import InteractingSLE.Spec.Sec7.StripSysField
import InteractingSLE.Spec.Exist.FlowField

/-!
# Wang–Wu Proposition 4.18: the forward and reverse lines on one glued space

Packet PROVE-WW-B10. Source: `source/external/WW17LP/wang_wu_lean_preprocessed.pdf` (ruling R31), proof of
Proposition 4.18 (text dump L1604–1653): "Conditionally on `h`, sample a forward line `α` and a reverse line `β`
independently. […] The reverse trace is the level line of `−h` from `∞` to `0`." This file prepares the glued space.

* **Lines read from a dyadic history** (`histLine`, `revLine`): the trace evaluation of the driver recovered from a
  dyadic killed history, and its image under `R(z) = −1/z`. For a marked chain on an infinite lifetime the line read
  from the killed history is the seed line (`histLine_killedHistory`).
* **Laws on glued spaces.** `glueMeasure_map_pair_apply`: the joint law of a variable of `Ω` and the glued sample on
  rectangles, `∫ κ(a)(C) k_D(a)(A) dν(a)`, where `k_D` is any version of the conditional law of `D` given `X`.
  `map_prodMap_compProd_of_involutive`: transport of `ν ⊗ₘ k` by an involution of the first factor.
* **The reflected field.** `reflectField = returnField 0 0` (`−h ∘ R` on test functions) is an involution of the
  distribution space (`reflectField_reflectField`).
* **The reverse coupling has the forward field law** (`map_reflectField_eq_twoSeed`): for the two-seed words
  `(r_L; r_R)` and `(r_R; r_L)`, the field of any optional hull coupling of the second, reflected by `R`, has the law of
  the field of any optional hull coupling of the first (both are GFFs with the same boundary data off `0`).
* **`glue_swap_law`** ("interchange the curves"): for two such couplings, with the glue kernels chosen as conditional
  laws of the reverse histories given the reflected fields, the joint law of (forward history, reverse sample) on the
  first glued space equals the joint law of (reverse sample, forward history) on the second.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology Metric
open scoped NNReal ENNReal

namespace InteractingSLE.WangWu

open QuantumZipper (H)
open LQGMetric (DistOn TestOn)
open LawUnique

/-! ### Lines read from a dyadic history -/

section Lines

variable {nL nR : ℕ}

/-- **The line read from a dyadic history**: the trace evaluation of the driver recovered from the history. -/
def histLine (y : HistorySpace nL nR) (s : ℝ) : ℂ := LP.traceAt s.toNNReal (pathsOfHistory y).2.1

/-- **The reverse line in forward coordinates**: the image of `histLine` under `R(z) = −1/z`. -/
def revLine (y : HistorySpace nL nR) (s : ℝ) : ℂ := negInv (histLine y s)

theorem measurable_histLine (s : ℝ) : Measurable fun y : HistorySpace nL nR => histLine y s :=
  (LP.measurable_traceAt _).comp (measurable_fst.comp (measurable_snd.comp measurable_pathsOfHistory))

theorem measurable_revLine (s : ℝ) : Measurable fun y : HistorySpace nL nR => revLine y s :=
  (measurable_histLine s).inv.neg

theorem negInv_negInv' (z : ℂ) : negInv (negInv z) = z := Sec7.StripSysField.negInv_negInv z

theorem continuousAt_negInv {z : ℂ} (hz : z ≠ 0) : ContinuousAt negInv z :=
  (continuousAt_inv₀ hz).neg

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {W : ℝ≥0 → Ω → ℝ} {VL : Fin nL → ℝ≥0 → Ω → ℝ}
  {VR : Fin nR → ℝ≥0 → Ω → ℝ} {ζ : Ω → ℝ≥0∞}

/-- The driver read from the killed history agrees with the driver before the lifetime, if it is continuous there. -/
theorem pathsOfHistory_killedHistory_driver {ω : Ω}
    (hc : ContinuousOn (fun t => W t ω) {t | (t : ℝ≥0∞) < ζ ω}) {t : ℝ≥0} (ht : (t : ℝ≥0∞) < ζ ω) :
    (pathsOfHistory (killedHistory W VL VR ζ ω)).2.1 t = W t ω := by
  refine Tendsto.limUnder_eq ((tendsto_lowerDyadic_of_continuousOn hc ht).congr fun n => ?_)
  have hlt : (dyadicTime (lowerDyadic t n) : ℝ≥0∞) < ζ ω :=
    lt_of_le_of_lt (ENNReal.coe_le_coe.2 (dyadicTime_lowerDyadic_le t n)) ht
  simp only [killedHistory, hlt, ↓reduceIte]

/-- **On an infinite lifetime with a continuous driver, the line read from the killed history is the seed line.** -/
theorem histLine_killedHistory {ω : Ω} (hζ : ζ ω = ⊤) (hc : Continuous fun t => W t ω) :
    histLine (killedHistory W VL VR ζ ω) = seedLine ζ W ω := by
  have hk : (fun t => killedProc ζ W t ω) = fun t => W t ω := funext (killedProc_of_eq_top hζ)
  have hd : (pathsOfHistory (killedHistory W VL VR ζ ω)).2.1 = fun t => W t ω := funext fun t =>
    pathsOfHistory_killedHistory_driver (VL := VL) (VR := VR) hc.continuousOn (by rw [hζ]; exact ENNReal.coe_lt_top)
  funext s
  simp only [histLine, seedLine, hk, hd]

end Lines

/-! ### Laws on glued spaces -/

section Laws

variable {Ω α β E : Type*} {mΩ : MeasurableSpace Ω} [mα : MeasurableSpace α] [mβ : MeasurableSpace β]
  [mE : MeasurableSpace E] {μ : Measure Ω} [IsProbabilityMeasure μ] {X : Ω → α}

/-- **The joint law of a variable of `Ω` and the glued sample, on rectangles**: if `k_D` is a version of the
conditional law of `D` given `X` (`μ.map (X, D) = μ.map X ⊗ₘ k_D`), then
`P_glue(D ∈ A, sample ∈ C) = ∫ κ(a)(C) k_D(a)(A) d(μ.map X)(a)`. -/
theorem glueMeasure_map_pair_apply (κ : Kernel α β) [IsMarkovKernel κ] (hX : Measurable X) {D : Ω → E}
    (hD : Measurable D) (kD : Kernel α E) [IsMarkovKernel kD]
    (hjoint : μ.map (fun ω => (X ω, D ω)) = μ.map X ⊗ₘ kD) {A : Set E} {C : Set β} (hA : MeasurableSet A)
    (hC : MeasurableSet C) :
    (glueMeasure μ κ X hX).map (fun p => (D p.1, p.2)) (A ×ˢ C) = ∫⁻ a, κ a C * kD a A ∂(μ.map X) := by
  have hm : Measurable fun p : Ω × β => (D p.1, p.2) := (hD.comp measurable_fst).prodMk measurable_snd
  rw [Measure.map_apply hm (hA.prod hC)]
  have h1 : (fun p : Ω × β => (D p.1, p.2)) ⁻¹' (A ×ˢ C) = (D ⁻¹' A) ×ˢ C := by ext; simp
  rw [h1, glueMeasure_apply_prod κ hX (hD hA) hC]
  set F : α × E → ℝ≥0∞ := (univ ×ˢ A).indicator fun z => κ z.1 C with hFdef
  have hF : Measurable F := ((κ.measurable_coe hC).comp measurable_fst).indicator (MeasurableSet.univ.prod hA)
  have hXD : Measurable fun ω => (X ω, D ω) := hX.prodMk hD
  have e1 : ∫⁻ ω in D ⁻¹' A, κ (X ω) C ∂μ = ∫⁻ ω, F (X ω, D ω) ∂μ := by
    rw [← lintegral_indicator (hD hA)]
    refine lintegral_congr fun ω => ?_
    by_cases hω : D ω ∈ A
    · simp [hFdef, hω, Set.indicator_of_mem]
    · simp [hFdef, hω, Set.indicator_of_notMem]
  rw [e1, ← lintegral_map hF hXD, hjoint, Measure.lintegral_compProd hF]
  refine lintegral_congr fun a => ?_
  have e2 : (fun e => F (a, e)) = A.indicator fun _ => κ a C := by
    funext e
    by_cases he : e ∈ A
    · simp [hFdef, he]
    · simp [hFdef, he]
  rw [e2, lintegral_indicator_const hA]

/-- **Transport of `ν ⊗ₘ k` by an involution `R` of the first factor**: `(ν ⊗ₘ k).map (R × id) = ν.map R ⊗ₘ k ∘ R`. -/
theorem map_prodMap_compProd_of_involutive {ν : Measure α} [IsProbabilityMeasure ν] (k : Kernel α E)
    [IsMarkovKernel k] {R : α → α} (hR : Measurable R) (hinv : ∀ a, R (R a) = a) :
    (ν ⊗ₘ k).map (Prod.map R id) = ν.map R ⊗ₘ k.comap R hR := by
  have hm : Measurable (Prod.map R (id : E → E)) := hR.prodMap measurable_id
  refine Measure.ext_prod fun {s t} hs ht => ?_
  rw [Measure.map_apply hm (hs.prod ht), Measure.compProd_apply_prod hs ht]
  have h1 : Prod.map R (id : E → E) ⁻¹' (s ×ˢ t) = (R ⁻¹' s) ×ˢ t := by ext; simp
  rw [h1, Measure.compProd_apply_prod (hR hs) ht, setLIntegral_map hs ((k.comap R hR).measurable_coe ht) hR]
  refine setLIntegral_congr_fun (hR hs) fun a _ => ?_
  simp only [Kernel.comap_apply, hinv]

end Laws

/-! ### The reflected field -/

section Reflect

open Sec7.StripSysField

/-- **The reflected field** `−h ∘ R`, `R(z) = −1/z` (the return field with no additive terms). -/
def reflectField (f : DistOn upperHalfPlaneOpens) : DistOn upperHalfPlaneOpens := returnField 0 0 f

theorem measurable_reflectField : Measurable reflectField := measurable_returnField 0 0

theorem reflectField_apply (f : DistOn upperHalfPlaneOpens) (φ : TestOn upperHalfPlaneOpens) :
    reflectField f φ = -f (Chart.pushTest isConformal_infinityReturnChart φ) := by
  rw [reflectField, returnField_apply]
  ring

/-- The return-chart transport of test functions is an involution. -/
theorem pushTest_return_return (φ : TestOn upperHalfPlaneOpens) :
    Chart.pushTest isConformal_infinityReturnChart (Chart.pushTest isConformal_infinityReturnChart φ) = φ := by
  ext z
  by_cases hz : z ∈ H
  · have hz' : z ∈ infinityReturnChart.dom := by
      rw [← SetLike.mem_coe, coe_dom_infinityReturnChart]; exact hz
    have hRz : (-z⁻¹) ∈ infinityReturnChart.dom := by
      rw [← SetLike.mem_coe, coe_dom_infinityReturnChart]; exact negInv_mem_H hz
    rw [Chart.pushTest_apply_of_mem _ _ hz']
    change ‖deriv (fun z : ℂ => -z⁻¹) z‖ ^ 2 * Chart.pushTest _ φ (-z⁻¹) = φ z
    rw [Chart.pushTest_apply_of_mem _ _ hRz]
    change ‖deriv (fun z : ℂ => -z⁻¹) z‖ ^ 2 * (‖deriv (fun z : ℂ => -z⁻¹) (-z⁻¹)‖ ^ 2 * φ (-(-z⁻¹)⁻¹)) = φ z
    rw [norm_deriv_negInv, norm_deriv_negInv, Sec7.StripSysField.negInv_negInv, norm_neg, norm_inv, inv_inv, ← mul_assoc,
      ← mul_pow, ← mul_pow, inv_mul_cancel₀ (norm_ne_zero_iff.2 (mem_H_ne_zero hz)), one_pow, one_pow, one_mul]
  · have hz' : z ∉ infinityReturnChart.dom := by
      rw [← SetLike.mem_coe, coe_dom_infinityReturnChart]; exact hz
    rw [Chart.pushTest_apply_of_notMem _ _ hz']
    exact (φ.zero_on_compl (show z ∈ ((upperHalfPlaneOpens : Set ℂ))ᶜ from hz)).symm

/-- **The reflection is an involution of the distribution space.** -/
theorem reflectField_reflectField (f : DistOn upperHalfPlaneOpens) : reflectField (reflectField f) = f := by
  ext φ
  rw [reflectField_apply, reflectField_apply, pushTest_return_return, neg_neg]

end Reflect

/-! ### The reverse coupling has the forward field law -/

section FieldLaw

open Sec7.StripSysField

/-- The two-seed boundary data: `−(π/√κ)(1 + r_L)` on `ℝ₋`, `(π/√κ)(1 + r_R)` on `[0, ∞)`. -/
theorem forceBoundaryData_twoSeed (κ rL rR x : ℝ) :
    forceBoundaryData κ (fun _ : Fin 1 => rL) (fun _ : Fin 1 => rR) LP.twoSeedXL LP.twoSeedXR x =
      if x < 0 then -(Real.pi / Real.sqrt κ) * (1 + rL) else (Real.pi / Real.sqrt κ) * (1 + rR) := by
  unfold forceBoundaryData
  split_ifs with hx
  · have e : Finset.univ.filter (fun i : Fin 1 => x < LP.twoSeedXL i) = Finset.univ := by
      ext i; simp [LP.twoSeedXL, hx]
    rw [e, Fin.sum_univ_one]
  · have e : Finset.univ.filter (fun i : Fin 1 => LP.twoSeedXR i ≤ x) = Finset.univ := by
      ext i; simp [LP.twoSeedXR, not_lt.1 hx]
    rw [e, Fin.sum_univ_one]

theorem forceJumpSet_twoSeed : forceJumpSet LP.twoSeedXL LP.twoSeedXR = (({0} : Finset ℝ) : Set ℝ) := by
  ext x
  simp [forceJumpSet, LP.twoSeedXL, LP.twoSeedXR, eq_comm]

theorem returnExcept_zero : returnExcept ({0} : Finset ℝ) = {0} := by
  simp [returnExcept]

/-- Off `0`, the return data of the reflected two-seed word `(r_R; r_L)` are the data of `(r_L; r_R)`. -/
theorem returnData_twoSeed (rL rR : ℝ) {x : ℝ} (hx : x ≠ 0) :
    returnData 0 0 (forceBoundaryData 4 (fun _ : Fin 1 => rR) (fun _ : Fin 1 => rL) LP.twoSeedXL LP.twoSeedXR) x =
      forceBoundaryData 4 (fun _ : Fin 1 => rL) (fun _ : Fin 1 => rR) LP.twoSeedXL LP.twoSeedXR x := by
  rw [returnData, forceBoundaryData_twoSeed, forceBoundaryData_twoSeed]
  rcases hx.lt_or_gt with h | h
  · have h' : ¬ (-x⁻¹ < 0) := not_lt.2 (by have := inv_lt_zero.2 h; linarith)
    simp only [h', h, ↓reduceIte]
    ring
  · have h' : -x⁻¹ < 0 := by have := inv_pos.2 h; linarith
    simp only [h', not_lt.2 h.le, ↓reduceIte]
    ring

theorem isBoundedHarmonicExtension_congr {g g' : ℝ → ℝ} {S : Set ℝ} {u : ℂ → ℝ}
    (hgg : ∀ x, x ∉ S → g x = g' x) (hu : IsBoundedHarmonicExtension g S u) :
    IsBoundedHarmonicExtension g' S u :=
  ⟨hu.1, hu.2.1, fun x hx => hgg x hx ▸ hu.2.2 x hx⟩

theorem isGFFWithBoundaryData_congr {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {h : Ω → DistOn upperHalfPlaneOpens} {g g' : ℝ → ℝ} {S : Set ℝ} (hgg : ∀ x, x ∉ S → g x = g' x)
    (hh : IsGFFWithBoundaryData P h g S) : IsGFFWithBoundaryData P h g' S :=
  ⟨hh.1, fun u hu => hh.2 u (isBoundedHarmonicExtension_congr (fun x hx => (hgg x hx).symm) hu)⟩

/-- **The reflected reverse field has the forward field law**: if `h` is a GFF with the two-seed data of `(r_L; r_R)`
and `h₂` one with the data of `(r_R; r_L)`, then `−h₂ ∘ R` has the law of `h` (conformal invariance of the
zero-boundary GFF under `R(z) = −1/z`, `isGFFWithBoundaryData_returnField`). -/
theorem map_reflectField_eq_twoSeed {rL rR : ℝ} {Ω Ω₂ : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω₂]
    {P : Measure Ω} {P₂ : Measure Ω₂} {h : Ω → DistOn upperHalfPlaneOpens} {h₂ : Ω₂ → DistOn upperHalfPlaneOpens}
    (hh : IsGFFWithBoundaryData P h
      (forceBoundaryData 4 (fun _ : Fin 1 => rL) (fun _ : Fin 1 => rR) LP.twoSeedXL LP.twoSeedXR)
      (forceJumpSet LP.twoSeedXL LP.twoSeedXR))
    (hh₂ : IsGFFWithBoundaryData P₂ h₂
      (forceBoundaryData 4 (fun _ : Fin 1 => rR) (fun _ : Fin 1 => rL) LP.twoSeedXL LP.twoSeedXR)
      (forceJumpSet LP.twoSeedXL LP.twoSeedXR)) :
    P.map h = P₂.map fun ω => reflectField (h₂ ω) := by
  rw [forceJumpSet_twoSeed] at hh hh₂
  have hg : ∃ u, IsBoundedHarmonicExtension
      (forceBoundaryData 4 (fun _ : Fin 1 => rR) (fun _ : Fin 1 => rL) LP.twoSeedXL LP.twoSeedXR)
      (({0} : Finset ℝ) : Set ℝ) u := by
    rw [← forceJumpSet_twoSeed]
    exact exists_isBoundedHarmonicExtension_forceBoundaryData 4 _ _ _ _
  have hr := isGFFWithBoundaryData_returnField 0 0 hg hh₂
  rw [returnExcept_zero] at hr
  have hr' : IsGFFWithBoundaryData P₂ (fun ω => reflectField (h₂ ω))
      (forceBoundaryData 4 (fun _ : Fin 1 => rL) (fun _ : Fin 1 => rR) LP.twoSeedXL LP.twoSeedXR)
      (({0} : Finset ℝ) : Set ℝ) :=
    isGFFWithBoundaryData_congr (fun x hx => returnData_twoSeed rL rR (by simpa using hx)) hr
  obtain ⟨u, hu⟩ : ∃ u, IsBoundedHarmonicExtension
      (forceBoundaryData 4 (fun _ : Fin 1 => rL) (fun _ : Fin 1 => rR) LP.twoSeedXL LP.twoSeedXR)
      (({0} : Finset ℝ) : Set ℝ) u := by
    rw [← forceJumpSet_twoSeed]
    exact exists_isBoundedHarmonicExtension_forceBoundaryData 4 _ _ _ _
  exact Exist.map_eq_of_isGFFWithBoundaryData hh hr' hu

end FieldLaw

/-! ### Interchanging the curves: one joint law on both glued spaces -/

section Swap

variable {Ω Ω₂ E E₂ : Type*} {mΩ : MeasurableSpace Ω} {mΩ₂ : MeasurableSpace Ω₂} [mE : MeasurableSpace E]
  [mE₂ : MeasurableSpace E₂] {P : Measure Ω} [IsProbabilityMeasure P]
  {P₂ : Measure Ω₂} [IsProbabilityMeasure P₂] {h : Ω → DistOn upperHalfPlaneOpens}
  {h₂ : Ω₂ → DistOn upperHalfPlaneOpens} {D : Ω → E} {D₂ : Ω₂ → E₂}

/-- The kernel property transported by the reflection: if `k` is a conditional law of `D₂` given `R h₂`, then
`k ∘ R` is one of `D₂` given `h₂`. -/
theorem map_pair_reflect_eq (hh₂ : Measurable h₂) (hD₂ : Measurable D₂) (k : Kernel (DistOn upperHalfPlaneOpens) E₂)
    [IsMarkovKernel k]
    (hk : P₂.map (fun ω => (reflectField (h₂ ω), D₂ ω)) = P₂.map (fun ω => reflectField (h₂ ω)) ⊗ₘ k) :
    P₂.map (fun ω => (h₂ ω, D₂ ω)) = P₂.map h₂ ⊗ₘ k.comap reflectField measurable_reflectField := by
  have hRh : Measurable fun ω => reflectField (h₂ ω) := measurable_reflectField.comp hh₂
  have hm : Measurable (Prod.map reflectField (id : E₂ → E₂)) := measurable_reflectField.prodMap measurable_id
  have e1 : P₂.map (fun ω => (h₂ ω, D₂ ω)) =
      (P₂.map (fun ω => (reflectField (h₂ ω), D₂ ω))).map (Prod.map reflectField id) := by
    rw [Measure.map_map hm (hRh.prodMk hD₂)]
    congr 1
    funext ω
    simp [reflectField_reflectField]
  have e2 : (P₂.map fun ω => reflectField (h₂ ω)).map reflectField = P₂.map h₂ := by
    rw [Measure.map_map measurable_reflectField hRh]
    congr 1
    funext ω
    simp [reflectField_reflectField]
  rw [e1, hk, map_prodMap_compProd_of_involutive k measurable_reflectField reflectField_reflectField, e2]

/-- **Interchanging the curves.** Let `D` be a variable of `(Ω, P)` with field `h`, `D₂` one of `(Ω₂, P₂)` with field
`h₂`, the field laws matched by the reflection (`P.map h = P₂.map (R h₂)`). Glue to `Ω` a sample of a conditional law
`k` of `D₂` given `R h₂`, and to `Ω₂` a sample of `k₁ ∘ R`, `k₁` a conditional law of `D` given `h`. Then the joint law
of `(D, sample)` on the first glued space is the joint law of `(sample, D₂)` on the second. -/
theorem glue_swap_law (hh : Measurable h) (hh₂ : Measurable h₂) (hD : Measurable D) (hD₂ : Measurable D₂)
    (hlaw : P.map h = P₂.map fun ω => reflectField (h₂ ω)) (k : Kernel (DistOn upperHalfPlaneOpens) E₂)
    [IsMarkovKernel k]
    (hk : P₂.map (fun ω => (reflectField (h₂ ω), D₂ ω)) = P₂.map (fun ω => reflectField (h₂ ω)) ⊗ₘ k)
    (k₁ : Kernel (DistOn upperHalfPlaneOpens) E) [IsMarkovKernel k₁]
    (hk₁ : P.map (fun ω => (h ω, D ω)) = P.map h ⊗ₘ k₁) :
    (glueMeasure P k h hh).map (fun p => (D p.1, p.2)) =
      (glueMeasure P₂ (k₁.comap reflectField measurable_reflectField) h₂ hh₂).map (fun p => (p.2, D₂ p.1)) := by
  have hRh : Measurable fun ω => reflectField (h₂ ω) := measurable_reflectField.comp hh₂
  refine Measure.ext_prod fun {A C} hA hC => ?_
  rw [glueMeasure_map_pair_apply k hh hD k₁ hk₁ hA hC]
  have hsw : Measurable fun p : Ω₂ × E => (p.2, D₂ p.1) := measurable_snd.prodMk (hD₂.comp measurable_fst)
  have hpair : Measurable fun p : Ω₂ × E => (D₂ p.1, p.2) := (hD₂.comp measurable_fst).prodMk measurable_snd
  have e1 : (glueMeasure P₂ (k₁.comap reflectField measurable_reflectField) h₂ hh₂).map
      (fun p => (p.2, D₂ p.1)) (A ×ˢ C) =
      (glueMeasure P₂ (k₁.comap reflectField measurable_reflectField) h₂ hh₂).map
      (fun p => (D₂ p.1, p.2)) (C ×ˢ A) := by
    rw [Measure.map_apply hsw (hA.prod hC), Measure.map_apply hpair (hC.prod hA)]
    congr 1
    ext p
    simp [and_comm]
  rw [e1, glueMeasure_map_pair_apply _ hh₂ hD₂ (k.comap reflectField measurable_reflectField)
    (map_pair_reflect_eq hh₂ hD₂ k hk) hC hA]
  have hf : Measurable fun f => k₁ f A * k f C :=
    (k₁.measurable_coe hA).mul (k.measurable_coe hC)
  have e2 : (P₂.map h₂).map reflectField = P₂.map fun ω => reflectField (h₂ ω) :=
    Measure.map_map measurable_reflectField hh₂
  calc ∫⁻ f, k f C * k₁ f A ∂(P.map h) = ∫⁻ f, k₁ f A * k f C ∂(P.map h) := by
        simp_rw [mul_comm]
    _ = ∫⁻ f, k₁ f A * k f C ∂((P₂.map h₂).map reflectField) := by rw [e2, hlaw]
    _ = ∫⁻ g, k₁ (reflectField g) A * k (reflectField g) C ∂(P₂.map h₂) :=
        lintegral_map hf measurable_reflectField
    _ = _ := by simp only [Kernel.comap_apply]

end Swap

end InteractingSLE.WangWu
