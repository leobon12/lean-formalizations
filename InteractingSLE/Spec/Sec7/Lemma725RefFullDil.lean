/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.Lemma725RefFullDilField
import InteractingSLE.Spec.Sec7.CounterflowProbDilation
import InteractingSLE.Spec.Sec7.LocalExtGChart
import InteractingSLE.Spec.Coupling.SafeEnergy
import InteractingSLE.Frozen.Spec.IsOptionalHullCoupling
import QuantumZipper.Proofs.Zipper.B3dDet

/-!
# Aux. lemma 126: dilation of a whole optional hull coupling

Packet PROVE-LEMMA725REF2. Specification §7.4, Aux. lemma 126's proof (`source/spec/p385-432.md` L251–L316,
pp. 401–402, "Universal field determination"):

> Dilation of a whole two-seed pair acts on its field by `H₀^{(a)}(z) = H₀(z/a)`. The derivative of `z ↦ z/a` is
> positive real, so its winding correction is zero. The two boundary constants and the zero-boundary GFF law are
> invariant under this dilation. Original optional hull locality and its Gaussian specification are preserved.

With `c > 0`, `a = √c` and Mathlib's Brownian scaling convention (`Sec7.Dilation.dilProc c X = (√c)⁻¹ X(c ·)`, the
source's dilation by `a⁻¹`), the dilated coupling is `(dilProc c W, dilProc c V, dilProc c B, ζ / c)` with the field
`h(a ·) = dilField (a⁻¹) h` (**`IsOptionalHullCoupling.dilate`**), for every force word (positions `a⁻¹ x`).

* Loewner scaling along one path (`dilDrv a w = w(a² ·)/a`): `fwdHull_dilDrv` (hull `a⁻¹ K_{a² t}`), `fwdMap_dilDrv`,
  `logDerivFwd_dilDrv`, `couplingMean_dilDrv`, and `loewnerGreenEnergy_dilDrv` (through the identification of the
  energy with the zero-boundary covariance on `ℍ \ K_t`, `Coupling.loewnerGreenEnergy_eq_zeroGFFTestCov`, and its
  dilation invariance `zeroGFFTestCov_dil`);
* the killed driving filtration of the dilated process is the time-changed one (`killedDrivingSigma_dil`,
  `drivingFiltration_dil`), so its stopping times are the time changes of the original ones, with the same σ-algebras
  (`isStoppingTime_mapMul`, `measurableSpace_mapMul`).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal

open QuantumZipper (H fwdHull fwdMap logDerivFwd)
open LQGMetric (TestOn DistOn)

universe u

namespace InteractingSLE

namespace Sec7

namespace Lemma725RefFull

/-! ### Loewner scaling along one path -/

section Path

variable {a : ℝ}

/-- The dilated driver `s ↦ w(a² s)/a` (QuantumZipper's scaling convention). -/
def dilDrv (a : ℝ) (w : ℝ → ℝ) : ℝ → ℝ := fun s => w (a ^ 2 * s) / a

theorem dilDrv_apply (w : ℝ → ℝ) (s : ℝ) : dilDrv a w s = w (a ^ 2 * s) / a := rfl

theorem continuous_dilDrv {w : ℝ → ℝ} (hw : Continuous w) : Continuous (dilDrv a w) := by
  unfold dilDrv
  fun_prop

theorem dilDrv_zero {w : ℝ → ℝ} (hw0 : w 0 = 0) : dilDrv a w 0 = 0 := by
  simp [dilDrv, hw0]

/-- **The hull of the dilated driver**: `K'_t = a⁻¹ K_{a² t}`. -/
theorem fwdHull_dilDrv (ha : 0 < a) (w : ℝ → ℝ) {t : ℝ} (ht : 0 ≤ t) :
    fwdHull (dilDrv a w) t = dil a⁻¹ '' fwdHull w (a ^ 2 * t) := by
  ext z
  change z ∈ fwdHull (fun s => w (a ^ 2 * s) / a) t ↔ _
  rw [QuantumZipper.LoewnerAlgebra.mem_fwdHull_scale_iff w ha ht z]
  constructor
  · intro hz
    exact ⟨(a : ℂ) * z, hz, dil_inv_dil ha z⟩
  · rintro ⟨y, hy, rfl⟩
    rwa [show (a : ℂ) * dil a⁻¹ y = y from dil_dil_inv ha y]

/-- **The forward map of the dilated driver**: `f'_t(z) = f_{a² t}(a z)/a`. -/
theorem fwdMap_dilDrv (ha : 0 < a) (w : ℝ → ℝ) {t : ℝ} (ht : 0 ≤ t) (z : ℂ) :
    fwdMap (dilDrv a w) t z = fwdMap w (a ^ 2 * t) (dil a z) / a :=
  QuantumZipper.B3d.fwdMap_scale_of w ha ht z

/-- **The derivative branch of the dilated driver**: `log f'_t'(z) = log f_{a² t}'(a z)`. -/
theorem logDerivFwd_dilDrv (ha : 0 < a) (w : ℝ → ℝ) {t : ℝ} (ht : 0 ≤ t) (z : ℂ) :
    logDerivFwd (dilDrv a w) t z = logDerivFwd w (a ^ 2 * t) (dil a z) := by
  have ha0 : (a : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 ha.ne'
  have ha2 : (a ^ 2 : ℝ) ≠ 0 := pow_ne_zero 2 ha.ne'
  unfold logDerivFwd
  congr 1
  have e : ∀ s ∈ uIcc (0 : ℝ) t, (2 : ℂ) / fwdMap (dilDrv a w) s z ^ 2 =
      ((a ^ 2 : ℝ) : ℂ) * ((fun σ : ℝ => (2 : ℂ) / fwdMap w σ (dil a z) ^ 2) (a ^ 2 * s)) := by
    intro s hs
    rw [uIcc_of_le ht] at hs
    rw [fwdMap_dilDrv ha w hs.1 z]
    by_cases h0 : fwdMap w (a ^ 2 * s) (dil a z) = 0
    · simp [h0]
    · push_cast
      field_simp
  rw [intervalIntegral.integral_congr e, intervalIntegral.integral_const_mul,
    intervalIntegral.integral_comp_mul_left (fun σ : ℝ => (2 : ℂ) / fwdMap w σ (dil a z) ^ 2) ha2, mul_zero,
    Complex.real_smul, ← mul_assoc]
  push_cast
  rw [mul_inv_cancel₀ (by exact_mod_cast ha2), one_mul]

/-- **The coupling mean of the dilated driver**: `M'_t(u)(z) = M_{a² t}(u(a⁻¹ ·))(a z)` (the winding correction is
unchanged since the dilation has a positive derivative). -/
theorem couplingMean_dilDrv (ha : 0 < a) (κ : ℝ) (w : ℝ → ℝ) {t : ℝ} (ht : 0 ≤ t) (u : ℂ → ℝ) (z : ℂ) :
    couplingMean κ (dilDrv a w) t u z = couplingMean κ w (a ^ 2 * t) (fun y => u (dil a⁻¹ y)) (dil a z) := by
  unfold couplingMean
  rw [fwdMap_dilDrv ha w ht z, logDerivFwd_dilDrv ha w ht z]
  congr 2
  simp only [dil, Complex.ofReal_inv]
  ring

/-- `z / a⁻¹ = a z`. -/
theorem div_inv_eq_dil (z : ℂ) : z / ((a⁻¹ : ℝ) : ℂ) = dil a z := by
  rw [Complex.ofReal_inv, div_inv_eq_mul, dil, mul_comm]

/-- **The integrated coupling mean of the dilated driver**: `∫ M'_t φ = ∫ M_{a² t} φ'`, `φ' = a⁻² φ(a⁻¹ ·)`. -/
theorem integral_couplingMean_dilDrv (ha : 0 < a) (κ : ℝ) (w : ℝ → ℝ) {t : ℝ} (ht : 0 ≤ t) (u : ℂ → ℝ)
    (φ : TestOn upperHalfPlaneOpens) :
    ∫ z, couplingMean κ (dilDrv a w) t u z * φ z =
      ∫ z, couplingMean κ w (a ^ 2 * t) (fun y => u (dil a⁻¹ y)) z *
        Chart.pushTest (Chart.isConformal_dilation (inv_pos.2 ha)) φ z := by
  rw [integral_mul_pushTest_dilation (inv_pos.2 ha)]
  simp only [div_inv_eq_dil, couplingMean_dilDrv ha κ w ht]

/-- **The Green energy of the dilated driver** (continuous driver, `w 0 = 0`, support avoiding the dilated hull):
`E'_t(φ) = E_{a² t}(a⁻² φ(a⁻¹ ·))`. Both are zero-boundary covariances on the hull complements
(`Coupling.loewnerGreenEnergy_eq_zeroGFFTestCov`), which correspond under the dilation (`zeroGFFTestCov_dil`). -/
theorem loewnerGreenEnergy_dilDrv (ha : 0 < a) {w : ℝ → ℝ} (hw : Continuous w) (hw0 : w 0 = 0) {t : ℝ}
    (ht : 0 ≤ t) (φ : TestOn upperHalfPlaneOpens) (hφ : Disjoint (tsupport φ) (fwdHull (dilDrv a w) t)) :
    loewnerGreenEnergy (dilDrv a w) t φ =
      loewnerGreenEnergy w (a ^ 2 * t) (Chart.pushTest (Chart.isConformal_dilation (inv_pos.2 ha)) φ) := by
  have hr := inv_pos.2 ha
  have ht' : 0 ≤ a ^ 2 * t := by positivity
  set ψ := Chart.pushTest (Chart.isConformal_dilation hr) φ
  have hψ : Disjoint (tsupport ψ) (fwdHull w (a ^ 2 * t)) := by
    rw [Set.disjoint_left]
    intro z hz hzK
    have h1 := tsupport_pushTest_dilation hr φ hz
    refine Set.disjoint_left.1 hφ h1 ?_
    rw [fwdHull_dilDrv ha w ht]
    exact ⟨z, hzK, rfl⟩
  rw [Coupling.loewnerGreenEnergy_eq_zeroGFFTestCov (continuous_dilDrv hw) (dilDrv_zero hw0) ht φ hφ,
    Coupling.loewnerGreenEnergy_eq_zeroGFFTestCov hw hw0 ht' ψ hψ, Coupling.coe_hullComplOpens,
    Coupling.coe_hullComplOpens, Coupling.coe_testOnHullCompl, Coupling.coe_testOnHullCompl,
    fwdHull_dilDrv ha w ht, H_diff_image_dil hr,
    ← zeroGFFTestCov_dil hr (QuantumZipper.FwdHolo.isOpen_compl_fwdHull hw ht') sdiff_subset]

end Path

/-- A test function whose support avoids `r K` transports to one whose support avoids `K`. -/
theorem disjoint_pushTest_dilation {r : ℝ} (hr : 0 < r) {φ : TestOn upperHalfPlaneOpens} {K : Set ℂ}
    (hφ : Disjoint (tsupport φ) (dil r '' K)) :
    Disjoint (tsupport (Chart.pushTest (Chart.isConformal_dilation hr) φ)) K := by
  rw [Set.disjoint_left]
  intro z hz hzK
  exact Set.disjoint_left.1 hφ (tsupport_pushTest_dilation hr φ hz) ⟨z, hzK, rfl⟩

/-! ### The dilated killed driving process, its filtration and its stopping times -/

section Filtration

open _root_.InteractingSLE.Sec7.Dilation

variable {c : ℝ≥0} {Ω : Type u} {nL nR : ℕ} {W : ℝ≥0 → Ω → ℝ} {VL : Fin nL → ℝ≥0 → Ω → ℝ}
  {VR : Fin nR → ℝ≥0 → Ω → ℝ} {ζ : Ω → ℝ≥0∞}

/-- The scaling `(w, v_L, v_R) ↦ s (w, v_L, v_R)` of the state space. -/
def stateMul (s : ℝ) (p : ℝ × (Fin nL → ℝ) × (Fin nR → ℝ)) : ℝ × (Fin nL → ℝ) × (Fin nR → ℝ) :=
  (s * p.1, fun i => s * p.2.1 i, fun j => s * p.2.2 j)

theorem measurable_stateMul (s : ℝ) : Measurable (stateMul (nL := nL) (nR := nR) s) := by
  unfold stateMul
  fun_prop

theorem stateMul_stateMul_inv {s : ℝ} (hs : s ≠ 0) (p : ℝ × (Fin nL → ℝ) × (Fin nR → ℝ)) :
    stateMul s (stateMul s⁻¹ p) = p := by
  simp only [stateMul, ← mul_assoc, mul_inv_cancel₀ hs, one_mul]

theorem killedSet_dil (hc : c ≠ 0) (r : ℝ≥0) (A : Set (ℝ × (Fin nL → ℝ) × (Fin nR → ℝ))) :
    {ω | (r : ℝ≥0∞) < ζ ω / c ∧
      (dilProc c W r ω, fun i => dilProc c (VL i) r ω, fun j => dilProc c (VR j) r ω) ∈ A} =
    {ω | ((c * r : ℝ≥0) : ℝ≥0∞) < ζ ω ∧
      (W (c * r) ω, fun i => VL i (c * r) ω, fun j => VR j (c * r) ω) ∈ stateMul (√(c : ℝ))⁻¹ ⁻¹' A} := by
  ext ω
  simp only [mem_ofPred_eq, coe_lt_div_iff hc, mem_preimage]
  rfl

/-- **The dilated killed driving process is measurable.** -/
theorem isMeasurableKilledDriving_dil [MeasurableSpace Ω] (hc : c ≠ 0)
    (hX : IsMeasurableKilledDriving W VL VR ζ) :
    IsMeasurableKilledDriving (dilProc c W) (fun i => dilProc c (VL i)) (fun j => dilProc c (VR j))
      (fun ω => ζ ω / c) := fun r A hA => by
  change MeasurableSet {ω | (r : ℝ≥0∞) < ζ ω / c ∧
    (dilProc c W r ω, fun i => dilProc c (VL i) r ω, fun j => dilProc c (VR j) r ω) ∈ A}
  rw [killedSet_dil hc]
  exact hX (c * r) _ (measurable_stateMul _ hA)

/-- **The dilated process generates the time-changed killed driving σ-algebras.** -/
theorem killedDrivingSigma_dil (hc : c ≠ 0) (t : ℝ≥0) :
    killedDrivingSigma (dilProc c W) (fun i => dilProc c (VL i)) (fun j => dilProc c (VR j)) (fun ω => ζ ω / c) t =
      killedDrivingSigma W VL VR ζ (c * t) := by
  have hs : (√(c : ℝ))⁻¹ ≠ 0 := inv_sqrt_ne_zero hc
  refine le_antisymm (MeasurableSpace.generateFrom_le ?_) (MeasurableSpace.generateFrom_le ?_)
  · rintro _ ⟨r, hr, A, hA, rfl⟩
    change MeasurableSet[killedDrivingSigma W VL VR ζ (c * t)] {ω | (r : ℝ≥0∞) < ζ ω / c ∧
      (dilProc c W r ω, fun i => dilProc c (VL i) r ω, fun j => dilProc c (VR j) r ω) ∈ A}
    rw [killedSet_dil hc]
    exact MeasurableSpace.measurableSet_generateFrom
      ⟨c * r, mul_le_mul_of_nonneg_left hr c.2, _, measurable_stateMul _ hA, rfl⟩
  · rintro _ ⟨r, hr, A, hA, rfl⟩
    refine MeasurableSpace.measurableSet_generateFrom
      ⟨r / c, ?_, stateMul (√(c : ℝ)) ⁻¹' A, measurable_stateMul _ hA, ?_⟩
    · rw [div_le_iff₀ (pos_iff_ne_zero.2 hc), mul_comm]
      exact hr
    · change _ = {ω | ((r / c : ℝ≥0) : ℝ≥0∞) < ζ ω / c ∧ (dilProc c W (r / c) ω,
        fun i => dilProc c (VL i) (r / c) ω, fun j => dilProc c (VR j) (r / c) ω) ∈ stateMul (√(c : ℝ)) ⁻¹' A}
      rw [killedSet_dil hc, mul_div_cancel₀ r hc, ← preimage_comp]
      have e : stateMul (√(c : ℝ)) ∘ stateMul (√(c : ℝ))⁻¹ = (id : ℝ × (Fin nL → ℝ) × (Fin nR → ℝ) → _) :=
        funext fun p => by rw [Function.comp_apply, ← inv_inv (√(c : ℝ)), inv_inv, stateMul_stateMul_inv
          (sqrt_ne_zero_of_ne hc)]; rfl
      rw [e, preimage_id]

theorem killedDrivingFiltration_apply [MeasurableSpace Ω] (hX : IsMeasurableKilledDriving W VL VR ζ) (t : ℝ≥0) :
    killedDrivingFiltration hX t = killedDrivingSigma W VL VR ζ t := rfl

/-- **The driving filtration of the dilated process is the time-changed one**: `𝓕'_t = 𝓕_{ct}`. -/
theorem drivingFiltration_dil [MeasurableSpace Ω] (hc : c ≠ 0) (P : Measure Ω)
    (hX : IsMeasurableKilledDriving W VL VR ζ) (t : ℝ≥0) :
    drivingFiltration P (isMeasurableKilledDriving_dil hc hX) t = drivingFiltration P hX (c * t) := by
  have hcpos : 0 < c := pos_iff_ne_zero.2 hc
  unfold drivingFiltration usualAugmentation
  rw [Filtration.rightCont_eq, Filtration.rightCont_eq]
  simp only [Filtration.coeFn_sup, Pi.sup_apply, Filtration.const_apply, killedDrivingFiltration_apply,
    killedDrivingSigma_dil hc]
  refine le_antisymm (le_iInf₂ fun j hj => ?_) (le_iInf₂ fun j hj => ?_)
  · have hj' : t < j / c := by
      rw [lt_div_iff₀ hcpos, mul_comm]
      exact hj
    refine (iInf₂_le (j / c) hj').trans ?_
    rw [mul_div_cancel₀ j hc]
  · exact iInf₂_le (c * j) (mul_lt_mul_of_pos_left hj hcpos)

/-- The time change `x ↦ c x` of an extended time. -/
def mapMul (c : ℝ≥0) (x : WithTop ℝ≥0) : WithTop ℝ≥0 := x.map (c * ·)

theorem mapMul_le_coe_iff (hc : c ≠ 0) (x : WithTop ℝ≥0) (i : ℝ≥0) :
    mapMul c x ≤ (i : WithTop ℝ≥0) ↔ x ≤ ((i / c : ℝ≥0) : WithTop ℝ≥0) := by
  cases x with
  | top =>
    simp only [mapMul, WithTop.map_top]
    exact ⟨fun h => absurd (top_le_iff.1 h) WithTop.coe_ne_top, fun h => absurd (top_le_iff.1 h) WithTop.coe_ne_top⟩
  | coe y =>
    simp only [mapMul, WithTop.map_coe, WithTop.coe_le_coe]
    rw [le_div_iff₀ (pos_iff_ne_zero.2 hc), mul_comm]

theorem untopD_mapMul (x : WithTop ℝ≥0) : (mapMul c x).untopD 0 = c * x.untopD 0 := by
  cases x with
  | top => simp [mapMul]
  | coe y => rw [mapMul, WithTop.map_coe, WithTop.untopD_coe, WithTop.untopD_coe]

theorem coe_mapMul_lt_iff (hc : c ≠ 0) (x : WithTop ℝ≥0) (ζ' : ℝ≥0∞) :
    ((mapMul c x : WithTop ℝ≥0) : ℝ≥0∞) < ζ' ↔ (x : ℝ≥0∞) < ζ' / (c : ℝ≥0∞) := by
  cases x with
  | top =>
    simp only [mapMul, WithTop.map_top]
    change (⊤ : ℝ≥0∞) < ζ' ↔ (⊤ : ℝ≥0∞) < ζ' / (c : ℝ≥0∞)
    simp
  | coe y =>
    simp only [mapMul, WithTop.map_coe]
    change ((c * y : ℝ≥0) : ℝ≥0∞) < ζ' ↔ (y : ℝ≥0∞) < ζ' / (c : ℝ≥0∞)
    rw [coe_lt_div_iff hc]

/-- **Stopping times under the time change**: if `τ'` is a stopping time of `𝓕' = 𝓕_{c ·}`, then `c τ'` is a
stopping time of `𝓕`. -/
theorem isStoppingTime_mapMul [MeasurableSpace Ω] {f f' : Filtration ℝ≥0 ‹MeasurableSpace Ω›} (hc : c ≠ 0)
    (hff : ∀ t, f' t = f (c * t)) {τ : Ω → WithTop ℝ≥0} (hτ : IsStoppingTime f' τ) :
    IsStoppingTime f fun ω => mapMul c (τ ω) := by
  intro i
  have e : {ω | mapMul c (τ ω) ≤ (i : WithTop ℝ≥0)} = {ω | τ ω ≤ ((i / c : ℝ≥0) : WithTop ℝ≥0)} := by
    ext ω
    exact mapMul_le_coe_iff hc _ _
  rw [e]
  have h := hτ (i / c)
  rwa [hff, mul_div_cancel₀ i hc] at h

/-- **The σ-algebra of a stopping time is unchanged by the time change.** -/
theorem measurableSpace_mapMul [MeasurableSpace Ω] {f f' : Filtration ℝ≥0 ‹MeasurableSpace Ω›} (hc : c ≠ 0)
    (hff : ∀ t, f' t = f (c * t)) {τ : Ω → WithTop ℝ≥0} (hτ : IsStoppingTime f' τ)
    (hτ' : IsStoppingTime f fun ω => mapMul c (τ ω)) : hτ.measurableSpace = hτ'.measurableSpace := by
  have hsup : (⨆ t, f' t) = ⨆ t, f t := by
    refine le_antisymm (iSup_le fun t => ?_) (iSup_le fun t => ?_)
    · rw [hff]
      exact le_iSup (fun t => f t) (c * t)
    · calc f t = f' (t / c) := by rw [hff, mul_div_cancel₀ t hc]
        _ ≤ ⨆ t, f' t := le_iSup (fun t => f' t) (t / c)
  refine MeasurableSpace.ext fun s => ?_
  change (MeasurableSet[⨆ t, f' t] s ∧ ∀ i : ℝ≥0, MeasurableSet[f' i] (s ∩ {ω | τ ω ≤ i})) ↔
    (MeasurableSet[⨆ t, f t] s ∧ ∀ i : ℝ≥0, MeasurableSet[f i] (s ∩ {ω | mapMul c (τ ω) ≤ i}))
  rw [hsup]
  refine and_congr Iff.rfl ⟨fun h i => ?_, fun h i => ?_⟩
  · have h' := h (i / c)
    rw [hff, mul_div_cancel₀ i hc] at h'
    have e : {ω | mapMul c (τ ω) ≤ (i : WithTop ℝ≥0)} = {ω | τ ω ≤ ((i / c : ℝ≥0) : WithTop ℝ≥0)} := by
      ext ω
      exact mapMul_le_coe_iff hc _ _
    rwa [e]
  · have h' := h (c * i)
    rw [hff]
    have e : {ω | mapMul c (τ ω) ≤ ((c * i : ℝ≥0) : WithTop ℝ≥0)} = {ω | τ ω ≤ (i : WithTop ℝ≥0)} := by
      ext ω
      rw [mem_ofPred_eq, mapMul_le_coe_iff hc, mul_div_cancel_left₀ i hc]
      rfl
    rwa [e] at h'

end Filtration

/-- A finite extended time is the coercion of its `untopD`. -/
theorem coe_untopD_of_lt'' {x : WithTop ℝ≥0} {b : ℝ≥0∞} (h : (x : ℝ≥0∞) < b) :
    (((x.untopD 0 : ℝ≥0)) : ℝ≥0∞) = x := by
  cases x with
  | top => exact absurd h (not_lt.2 le_top)
  | coe s => rfl

/-- The Green energy at time `t` only sees the driver on `[0, t]`. -/
theorem loewnerGreenEnergy_congr' {w w' : ℝ → ℝ} {t : ℝ} (h : EqOn w w' (Icc 0 t)) (φ : ℂ → ℝ) :
    loewnerGreenEnergy w t φ = loewnerGreenEnergy w' t φ := by
  unfold loewnerGreenEnergy
  simp only [Ito.fwdMap_congr_of_eqOn_of_le h le_rfl]

/-! ### The dilated coupling -/

section Coupling

open _root_.InteractingSLE.Sec7.Dilation

theorem dilProc_toNNReal_eq_dilDrv {Ω : Type*} (c : ℝ≥0) (W : ℝ≥0 → Ω → ℝ) (ω : Ω) :
    (fun s : ℝ => dilProc c W s.toNNReal ω) = dilDrv (√(c : ℝ)) (fun s : ℝ => W s.toNNReal ω) := by
  funext s
  rw [dilDrv_apply, Real.sq_sqrt c.coe_nonneg, dilProc_apply, dilPath_toNNReal, div_eq_inv_mul]

/-- **Aux. lemma 126, the dilation of a whole coupling** (p. 401–402: "Dilation of a whole two-seed pair acts on its
field by `H₀^{(a)}(z) = H₀(z/a)` … Original optional hull locality and its Gaussian specification are preserved"):
if `(W, V, B, ζ)` with the field `h` satisfies the frozen optional hull specification of the word `(x_L; x_R)`, then
the dilated evolution `(√c)⁻¹ (W, V, B)(c ·)` with lifetime `ζ / c` (filtration `𝓕_{c ·}`) and the field `h(√c ·)`
satisfies it for the word `(√c)⁻¹ (x_L; x_R)`. -/
theorem IsOptionalHullCoupling.dilate {κ : ℝ} {nL nR : ℕ} {xL : Fin nL → ℝ} {xR : Fin nR → ℝ} {ρL : Fin nL → ℝ}
    {ρR : Fin nR → ℝ} {Ω : Type u} {mΩ : MeasurableSpace Ω} {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    {W : ℝ≥0 → Ω → ℝ} {VL : Fin nL → ℝ≥0 → Ω → ℝ} {VR : Fin nR → ℝ≥0 → Ω → ℝ} {B : ℝ≥0 → Ω → ℝ}
    {ζ : Ω → ℝ≥0∞} {h : Ω → DistOn upperHalfPlaneOpens} {c : ℝ≥0} (hc : c ≠ 0)
    (hC : IsOptionalHullCoupling κ xL xR ρL ρR P 𝓕 W VL VR B ζ h) :
    IsOptionalHullCoupling κ (fun i => (√(c : ℝ))⁻¹ * xL i) (fun i => (√(c : ℝ))⁻¹ * xR i) ρL ρR P
      (dilFiltration c 𝓕) (dilProc c W) (fun i => dilProc c (VL i)) (fun j => dilProc c (VR j)) (dilProc c B)
      (fun ω => ζ ω / c) (fun ω => dilField (inv_pos.2 (sqrt_pos_of_ne hc)) (h ω)) := by
  have ha : 0 < √(c : ℝ) := sqrt_pos_of_ne hc
  have hr : 0 < (√(c : ℝ))⁻¹ := inv_pos.2 ha
  have ha2 : √(c : ℝ) ^ 2 = c := Real.sq_sqrt c.coe_nonneg
  obtain ⟨hev, hm, hgff, hX, hloc⟩ := hC
  refine ⟨hev.dilate hc, (measurable_dilField hr).comp hm, fun u₀ hu₀ => isZBGFFProcess_dilField hr hgff u₀ hu₀,
    isMeasurableKilledDriving_dil hc hX, fun τ' hτ' hτζ => ?_⟩
  -- the original stopping time `c τ'`
  have hff := drivingFiltration_dil hc P hX
  have hτ : IsStoppingTime (drivingFiltration P hX) fun ω => mapMul c (τ' ω) := isStoppingTime_mapMul hc hff hτ'
  have hτζ' : ∀ᵐ ω ∂P, ((mapMul c (τ' ω) : WithTop ℝ≥0) : ℝ≥0∞) < ζ ω :=
    hτζ.mono fun ω hω => (coe_mapMul_lt_iff hc _ _).2 hω
  obtain ⟨hls, hlaw⟩ := hloc _ hτ hτζ'
  have hT : ∀ ω, ((mapMul c (τ' ω)).untopD 0 : ℝ≥0) = c * (τ' ω).untopD 0 := fun ω => untopD_mapMul _
  have hTr : ∀ ω, (((mapMul c (τ' ω)).untopD 0 : ℝ≥0) : ℝ) = √(c : ℝ) ^ 2 * ((τ' ω).untopD 0 : ℝ≥0) := fun ω => by
    rw [hT, NNReal.coe_mul, ha2]
  -- the hulls
  have hhull : ∀ ω, fwdHull (fun s : ℝ => dilProc c W s.toNNReal ω) ((τ' ω).untopD 0 : ℝ≥0) =
      dil (√(c : ℝ))⁻¹ '' fwdHull (fun s : ℝ => W s.toNNReal ω) ((mapMul c (τ' ω)).untopD 0 : ℝ≥0) := by
    intro ω
    rw [dilProc_toNNReal_eq_dilDrv, fwdHull_dilDrv ha _ (NNReal.coe_nonneg _), hTr]
  refine ⟨?_, fun u hu φ => ?_⟩
  · simp only [hhull]
    exact IsLocalSet.dilate hr hls
  -- the conditional law
  set ψ := Chart.pushTest (Chart.isConformal_dilation hr) φ with hψ
  have hpos : ∀ ω, (fun i => dilProc c (VL i) ((τ' ω).untopD 0) ω - dilProc c W ((τ' ω).untopD 0) ω) =
      fun i => (√(c : ℝ))⁻¹ * (VL i ((mapMul c (τ' ω)).untopD 0) ω - W ((mapMul c (τ' ω)).untopD 0) ω) := by
    intro ω
    funext i
    rw [hT, dilProc, dilProc, mul_sub]
  have hposR : ∀ ω, (fun j => dilProc c (VR j) ((τ' ω).untopD 0) ω - dilProc c W ((τ' ω).untopD 0) ω) =
      fun j => (√(c : ℝ))⁻¹ * (VR j ((mapMul c (τ' ω)).untopD 0) ω - W ((mapMul c (τ' ω)).untopD 0) ω) := by
    intro ω
    funext j
    rw [hT, dilProc, dilProc, mul_sub]
  have hu' : ∀ ω, IsBoundedHarmonicExtension
      (forceBoundaryData κ ρL ρR
        (fun i => VL i ((mapMul c (τ' ω)).untopD 0) ω - W ((mapMul c (τ' ω)).untopD 0) ω)
        (fun j => VR j ((mapMul c (τ' ω)).untopD 0) ω - W ((mapMul c (τ' ω)).untopD 0) ω))
      (forceJumpSet (fun i => VL i ((mapMul c (τ' ω)).untopD 0) ω - W ((mapMul c (τ' ω)).untopD 0) ω)
        (fun j => VR j ((mapMul c (τ' ω)).untopD 0) ω - W ((mapMul c (τ' ω)).untopD 0) ω))
      (fun z => u ω (dil (√(c : ℝ))⁻¹ z)) := fun ω => by
    have h1 := hu ω
    rw [hpos ω, hposR ω] at h1
    exact isBoundedHarmonicExtension_force_comp_dil hr h1
  have hl := hlaw (fun ω z => u ω (dil (√(c : ℝ))⁻¹ z)) hu' ψ
  have hpath := hev.2.2.2.2
  have hcm := measurableSpace_mapMul hc hff hτ' hτ
  filter_upwards [hl, hpath, hτζ'] with ω hω hpω hτω hdisj
  -- the support of `ψ` avoids the original hull
  rw [hhull ω] at hdisj
  have hdisj' := disjoint_pushTest_dilation hr hdisj
  rw [hcm]
  change condExp hτ.measurableSpace P (fun ω' => Complex.exp (Complex.I * ((h ω' ψ : ℝ) : ℂ))) ω = _
  rw [hω hdisj']
  -- continuity of the driver beyond the stop, and a clamped continuous driver
  have hTζ : (((mapMul c (τ' ω)).untopD 0 : ℝ≥0) : ℝ≥0∞) < ζ ω := by
    rw [coe_untopD_of_lt'' hτω]
    exact hτω
  obtain ⟨T', hTT', hT'ζ⟩ := ENNReal.lt_iff_exists_nnreal_btwn.1 hTζ
  have hTT'r : (((mapMul c (τ' ω)).untopD 0 : ℝ≥0) : ℝ) < T' := by exact_mod_cast ENNReal.coe_lt_coe.1 hTT'
  have hwc : ContinuousOn (fun s : ℝ => W s.toNNReal ω) (Icc 0 (T' : ℝ)) :=
    Ito.continuousOn_rpath hpω.2.2.2.1 hT'ζ
  have hwcc : Continuous (Ito.clampDrv (fun s : ℝ => W s.toNNReal ω) T') := Ito.continuous_clampDrv T'.2 hwc
  have hwc0 : Ito.clampDrv (fun s : ℝ => W s.toNNReal ω) T' 0 = 0 := by
    simp only [Ito.clampDrv, max_self, min_eq_left (NNReal.coe_nonneg T'), Real.toNNReal_zero]
    exact hpω.1
  have heq : EqOn (Ito.clampDrv (fun s : ℝ => W s.toNNReal ω) T') (fun s : ℝ => W s.toNNReal ω) (Icc 0 T') :=
    Ito.clampDrv_eqOn
  have heqT : EqOn (fun s : ℝ => W s.toNNReal ω) (Ito.clampDrv (fun s : ℝ => W s.toNNReal ω) T')
      (Icc 0 (((mapMul c (τ' ω)).untopD 0 : ℝ≥0) : ℝ)) := fun s hs =>
    (heq ⟨hs.1, hs.2.trans hTT'r.le⟩).symm
  have heqd : EqOn (dilDrv (√(c : ℝ)) fun s : ℝ => W s.toNNReal ω)
      (dilDrv (√(c : ℝ)) (Ito.clampDrv (fun s : ℝ => W s.toNNReal ω) T')) (Icc 0 (((τ' ω).untopD 0 : ℝ≥0) : ℝ)) :=
    fun s hs => by
      simp only [dilDrv_apply]
      have hmem : √(c : ℝ) ^ 2 * s ∈ Icc 0 (((mapMul c (τ' ω)).untopD 0 : ℝ≥0) : ℝ) :=
        ⟨by have := hs.1; positivity, by rw [hTr]; exact mul_le_mul_of_nonneg_left hs.2 (by positivity)⟩
      rw [show W (√(c : ℝ) ^ 2 * s).toNNReal ω = Ito.clampDrv (fun s : ℝ => W s.toNNReal ω) T' (√(c : ℝ) ^ 2 * s)
        from heqT hmem]
  have hhullc : fwdHull (Ito.clampDrv (fun s : ℝ => W s.toNNReal ω) T') ((mapMul c (τ' ω)).untopD 0 : ℝ≥0) =
      fwdHull (fun s : ℝ => W s.toNNReal ω) ((mapMul c (τ' ω)).untopD 0 : ℝ≥0) :=
    LocalExt.fwdHull_congr_of_eqOn_of_lt (NNReal.coe_nonneg _) hTT'r heq
  have hdc : Disjoint (tsupport φ)
      (fwdHull (dilDrv (√(c : ℝ)) (Ito.clampDrv (fun s : ℝ => W s.toNNReal ω) T')) ((τ' ω).untopD 0 : ℝ≥0)) := by
    rw [fwdHull_dilDrv ha _ (NNReal.coe_nonneg _), ← hTr, hhullc]
    exact hdisj
  have hE : loewnerGreenEnergy (dilDrv (√(c : ℝ)) fun s : ℝ => W s.toNNReal ω) ((τ' ω).untopD 0 : ℝ≥0) φ =
      loewnerGreenEnergy (fun s : ℝ => W s.toNNReal ω) ((mapMul c (τ' ω)).untopD 0 : ℝ≥0) ψ := by
    rw [loewnerGreenEnergy_congr' heqd, loewnerGreenEnergy_dilDrv ha hwcc hwc0 (NNReal.coe_nonneg _) φ hdc,
      ← hTr, ← loewnerGreenEnergy_congr' heqT]
  have hI := integral_couplingMean_dilDrv ha κ (fun s : ℝ => W s.toNNReal ω) (NNReal.coe_nonneg ((τ' ω).untopD 0))
    (u ω) φ
  rw [← hTr] at hI
  rw [dilProc_toNNReal_eq_dilDrv, hI, hE]

end Coupling

end Lemma725RefFull

end Sec7

end InteractingSLE
