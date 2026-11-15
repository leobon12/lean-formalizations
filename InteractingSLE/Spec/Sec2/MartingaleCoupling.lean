import InteractingSLE.Spec.Sec2.MartingaleExtract
import InteractingSLE.Spec.Sec2.MartingaleLaurent
import InteractingSLE.Spec.Ito.Mean

/-!
# From the coupling-mean local martingales to the Laurent-coefficient martingales

Packet PROVE-SEC2-MART. Specification, Theorem 2.4 and its proof (`source/spec/p001-048.md`,
L819–L866). The hypothesis of the converse implication is that for every `z ∈ ℍ` the coupling mean
`𝔥_t(z)` of Theorem 1.1 (the frozen `couplingMean`, built from the bounded harmonic extension of the
frozen `forceBoundaryData` at the centred force points) is a local martingale before `z` is swallowed.
For the explicit extension (`meanExt`, Impl's `forceExt`) and ordered force points
`V^{i,L} ≤ W ≤ V^{i,R}`,

  `𝔥_t(z) = π (1 + ∑ ρ^R)/√κ + harmPart κ ρ W t V z`   (`couplingMean_meanExt_eq`),

the identity (2.5) proved by PROVE-T11-ITO (`Ito.couplingMean_eq_meanHarmonic`). Combining the
local-martingale hypothesis at `z = iY` and `z = Y(1+i)` with the Laurent estimates of
`MartingaleLaurent` and the limit theorems of `MartingaleExtract` gives
(`martingale_driftProc_quadProc_of_couplingMean`): the processes `N` and `Q` stopped at every
localizing time `min T (exitTime Z N)` are martingales — the hypotheses of the Lévy step
`isFilteredBrownianReal_martProc_div_sqrt`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter Topology Complex
open QuantumZipper (H)
open scoped NNReal ENNReal

namespace InteractingSLE

namespace MartChar

variable {nL nR : ℕ}

/-! ### Joining the two sides -/

/-- The weights of both sides, indexed by `Fin nL ⊕ Fin nR`. -/
def jointρ (ρL : Fin nL → ℝ) (ρR : Fin nR → ℝ) : Fin nL ⊕ Fin nR → ℝ := Sum.elim ρL ρR

/-- The force-point coordinates of both sides, indexed by `Fin nL ⊕ Fin nR`. -/
def jointV {β : Type*} (vL : Fin nL → β) (vR : Fin nR → β) : Fin nL ⊕ Fin nR → β := Sum.elim vL vR

/-- The explicit bounded harmonic extension of the force-word data at the centred positions
`vL − w`, `vR − w` (Impl's `forceExt`). -/
def meanExt (κ : ℝ) (ρL : Fin nL → ℝ) (ρR : Fin nR → ℝ) (w : ℝ) (vL : Fin nL → ℝ)
    (vR : Fin nR → ℝ) : ℂ → ℝ :=
  Impl.forceExt κ (Ito.weightWord ρL ρR) (fun i => vL i - w) (fun i => vR i - w)

theorem isBoundedHarmonicExtension_meanExt (κ : ℝ) (ρL : Fin nL → ℝ) (ρR : Fin nR → ℝ) (w : ℝ)
    (vL : Fin nL → ℝ) (vR : Fin nR → ℝ) :
    IsBoundedHarmonicExtension
      (forceBoundaryData κ ρL ρR (fun i => vL i - w) (fun i => vR i - w))
      (forceJumpSet (fun i => vL i - w) (fun i => vR i - w)) (meanExt κ ρL ρR w vL vR) :=
  Impl.isBoundedHarmonicExtension_forceExt κ (Ito.weightWord ρL ρR) _ _

/-- **The coupling mean is explicit** (2.5): for ordered force points and `f_t(z) ∈ ℍ`,
`𝔥_t(z) = π (1 + ∑ ρ^R)/√κ + harmPart`. -/
theorem couplingMean_meanExt_eq (κ : ℝ) (ρL : Fin nL → ℝ) (ρR : Fin nR → ℝ) {w : ℝ → ℝ} {t : ℝ}
    {vL : Fin nL → ℝ} {vR : Fin nR → ℝ} (hvL : ∀ i, vL i ≤ w t) (hvR : ∀ i, w t ≤ vR i) {z : ℂ}
    (hf : QuantumZipper.fwdMap w t z ∈ H) :
    couplingMean κ w t (meanExt κ ρL ρR (w t) vL vR) z
      = Real.pi / Real.sqrt κ * (1 + ∑ i, ρR i)
        + harmPart κ (jointρ ρL ρR) w t (jointV vL vR) z := by
  rw [Ito.couplingMean_eq_meanHarmonic (fun i => sub_nonpos.2 (hvL i))
    (fun i => sub_nonneg.2 (hvR i)) (isBoundedHarmonicExtension_meanExt κ ρL ρR (w t) vL vR) hf]
  simp only [Ito.meanHarmonic, harmPart, jointρ, jointV, Fintype.sum_sum_type, Sum.elim_inl,
    Sum.elim_inr]
  have hL : ∀ i, QuantumZipper.fwdMap w t z - ((vL i - w t : ℝ) : ℂ)
      = QuantumZipper.fwdMap w t z + (w t : ℂ) - (vL i : ℂ) := fun i => by push_cast; ring
  have hR : ∀ i, QuantumZipper.fwdMap w t z - ((vR i - w t : ℝ) : ℂ)
      = QuantumZipper.fwdMap w t z + (w t : ℂ) - (vR i : ℂ) := fun i => by push_cast; ring
  simp only [hL, hR]
  ring

/-! ### Deterministic properties of `harmPart` -/

section HarmPart

variable {ι : Type*} [Fintype ι] {w : ℝ → ℝ}

/-- The constant of `abs_harmPart_le`. -/
def harmBound (κ : ℝ) (ρ : ι → ℝ) (K T : ℝ) : ℝ :=
  1 / Real.sqrt κ * (2 + ∑ j, |ρ j|) * Real.pi
    + |QuantumZipper.chiC κ| * (24 * dispConst K T * T + 2 * T)

/-- A uniform bound for `harmPart` before swallowing, far from the origin. -/
theorem abs_harmPart_le (κ : ℝ) (ρ : ι → ℝ) (hw : Continuous w) (hw0 : w 0 = 0) {t T K : ℝ}
    (ht : 0 ≤ t) (htT : t ≤ T) (hK : ∀ r ∈ Icc (0 : ℝ) t, |w r| ≤ K) (v : ι → ℝ) {z : ℂ}
    (hz : z ∈ H \ QuantumZipper.fwdHull w t) (hz1 : 1 ≤ ‖z‖)
    (hzD : 2 * dispConst K T ≤ ‖z‖) :
    |harmPart κ ρ w t v z| ≤ harmBound κ ρ K T := by
  have hK0 : 0 ≤ K := (abs_nonneg _).trans (hK 0 ⟨le_rfl, ht⟩)
  have hDt : 24 * K + 8 * Real.sqrt t ≤ dispConst K T := by
    simp only [dispConst]; linarith [Real.sqrt_le_sqrt htT]
  have hL := norm_logDerivFwd_add_le hw hw0 ht hK hz (by linarith)
  have hnz : 0 < ‖z‖ := by linarith
  have hLb : |(QuantumZipper.logDerivFwd w t z).im| ≤ 24 * dispConst K T * T + 2 * T := by
    refine (Complex.abs_im_le_norm _).trans ?_
    have h2 : ‖2 * (t : ℂ) / z ^ 2‖ ≤ 2 * T := by
      rw [norm_div, norm_mul, Complex.norm_ofNat, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg ht, norm_pow]
      have : 1 ≤ ‖z‖ ^ 2 := one_le_pow₀ hz1
      rw [div_le_iff₀ (by positivity)]
      nlinarith
    have h1 : 24 * (24 * K + 8 * Real.sqrt t) * t / ‖z‖ ^ 3 ≤ 24 * dispConst K T * T := by
      have : 1 ≤ ‖z‖ ^ 3 := one_le_pow₀ hz1
      rw [div_le_iff₀ (by positivity)]
      have hDT0 : 0 ≤ dispConst K T := (by positivity : (0:ℝ) ≤ 24 * K + 8 * Real.sqrt t).trans hDt
      have h3 : 24 * (24 * K + 8 * Real.sqrt t) * t ≤ 24 * dispConst K T * T := by
        have := mul_le_mul hDt htT ht hDT0
        linarith
      have h4 : 24 * dispConst K T * T ≤ 24 * dispConst K T * T * ‖z‖ ^ 3 :=
        le_mul_of_one_le_right (by have := ht.trans htT; positivity) this
      linarith
    calc ‖QuantumZipper.logDerivFwd w t z‖
        = ‖(QuantumZipper.logDerivFwd w t z + 2 * t / z ^ 2) - 2 * t / z ^ 2‖ := by ring_nf
      _ ≤ ‖QuantumZipper.logDerivFwd w t z + 2 * t / z ^ 2‖ + ‖2 * (t : ℂ) / z ^ 2‖ := norm_sub_le _ _
      _ ≤ 24 * dispConst K T * T + 2 * T := by linarith
  have hsum : |∑ j, ρ j * arg (QuantumZipper.fwdMap w t z + (w t : ℂ) - (v j : ℂ))|
      ≤ (∑ j, |ρ j|) * Real.pi := by
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    rw [Finset.sum_mul]
    exact Finset.sum_le_sum fun j _ => by
      rw [abs_mul]; exact mul_le_mul_of_nonneg_left (Complex.abs_arg_le_pi _) (abs_nonneg _)
  have hsk : 0 ≤ 1 / Real.sqrt κ := by positivity
  simp only [harmPart, harmBound]
  calc |-(1 / Real.sqrt κ) * (2 * arg (QuantumZipper.fwdMap w t z)
          + ∑ j, ρ j * arg (QuantumZipper.fwdMap w t z + (w t : ℂ) - (v j : ℂ)))
        - QuantumZipper.chiC κ * (QuantumZipper.logDerivFwd w t z).im|
      ≤ 1 / Real.sqrt κ * (2 * Real.pi + (∑ j, |ρ j|) * Real.pi)
        + |QuantumZipper.chiC κ| * (24 * dispConst K T * T + 2 * T) := by
        refine (abs_sub _ _).trans (add_le_add ?_ ?_)
        · rw [abs_mul, abs_neg, abs_of_nonneg hsk]
          refine mul_le_mul_of_nonneg_left ((abs_add_le _ _).trans (add_le_add ?_ hsum)) hsk
          rw [abs_mul, abs_two]
          exact mul_le_mul_of_nonneg_left (Complex.abs_arg_le_pi _) (by norm_num)
        · rw [abs_mul]; exact mul_le_mul_of_nonneg_left hLb (abs_nonneg _)
    _ = _ := by ring

/-- Continuity of `harmPart` in time before swallowing. -/
theorem continuousOn_harmPart (κ : ℝ) (ρ : ι → ℝ) (hw : Continuous w) {T : ℝ} (hT : 0 ≤ T)
    {z : ℂ} (hz : z ∈ H \ QuantumZipper.fwdHull w T) {v : ι → ℝ → ℝ}
    (hv : ∀ j, ContinuousOn (v j) (Icc 0 T)) :
    ContinuousOn (fun t => harmPart κ ρ w t (fun j => v j t) z) (Icc 0 T) := by
  have hf := Ito.continuousOn_fwdMap_time' hw hT hz
  have hL := Ito.continuousOn_logDerivFwd hw hT hz
  have him : ∀ t ∈ Icc 0 T, 0 < (QuantumZipper.fwdMap w t z).im := fun t ht =>
    Ito.im_fwdMap_pos hw hT hz ht
  have harg : ContinuousOn (fun t => arg (QuantumZipper.fwdMap w t z)) (Icc 0 T) := fun t ht =>
    ContinuousAt.comp_continuousWithinAt (g := Complex.arg)
      (f := fun s => QuantumZipper.fwdMap w s z) (Complex.continuousAt_arg (Or.inr (him t ht).ne'))
      (hf t ht)
  have harg' : ∀ j, ContinuousOn
      (fun t => arg (QuantumZipper.fwdMap w t z + (w t : ℂ) - (v j t : ℂ))) (Icc 0 T) :=
    fun j t ht => by
      have hc : ContinuousWithinAt
          (fun t => QuantumZipper.fwdMap w t z + (w t : ℂ) - (v j t : ℂ)) (Icc 0 T) t :=
        ((hf t ht).add (Complex.continuous_ofReal.comp hw).continuousWithinAt).sub
          (Complex.continuous_ofReal.continuousAt.comp_continuousWithinAt (hv j t ht))
      have hpos : 0 < (QuantumZipper.fwdMap w t z + (w t : ℂ) - (v j t : ℂ)).im := by
        simpa using him t ht
      exact ContinuousAt.comp_continuousWithinAt (g := Complex.arg)
        (f := fun t => QuantumZipper.fwdMap w t z + (w t : ℂ) - (v j t : ℂ))
        (Complex.continuousAt_arg (Or.inr hpos.ne')) hc
  have hLi : ContinuousOn (fun t => (QuantumZipper.logDerivFwd w t z).im) (Icc 0 T) :=
    Complex.continuous_im.comp_continuousOn hL
  simp only [harmPart]
  refine (continuousOn_const.mul ((continuousOn_const.mul harg).add
    (continuousOn_finsetSum _ fun j _ => continuousOn_const.mul (harg' j)))).sub
    (continuousOn_const.mul hLi)

end HarmPart

/-! ### The coupling-mean processes -/

section Process

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}

/-- The driver path `s ↦ W_{s⁺}` on `ℝ` of a process indexed by `ℝ≥0`. -/
def wpath (W : ℝ≥0 → Ω → ℝ) (ω : Ω) : ℝ → ℝ := fun s => W s.toNNReal ω

/-- The coupling mean `𝔥_t(z)` of Theorem 1.1 along the processes `(W, V^L, V^R)`, with the explicit
bounded harmonic extension. -/
def coupProc (κ : ℝ) (ρL : Fin nL → ℝ) (ρR : Fin nR → ℝ) (W : ℝ≥0 → Ω → ℝ)
    (VL : Fin nL → ℝ≥0 → Ω → ℝ) (VR : Fin nR → ℝ≥0 → Ω → ℝ) (z : ℂ) : ℝ≥0 → Ω → ℝ :=
  fun t ω => couplingMean κ (wpath W ω) t
    (meanExt κ ρL ρR (W t ω) (fun i => VL i t ω) (fun i => VR i t ω)) z

lemma wpath_coe (W : ℝ≥0 → Ω → ℝ) (ω : Ω) (t : ℝ≥0) : wpath W ω (t : ℝ) = W t ω := by
  simp [wpath]

lemma continuous_wpath {W : ℝ≥0 → Ω → ℝ} (hWc : ∀ ω, Continuous fun t => W t ω) (ω : Ω) :
    Continuous (wpath W ω) :=
  (hWc ω).comp continuous_real_toNNReal

/-- The coupling-mean process equals `c + harmPart` before swallowing. -/
lemma coupProc_eq {κ : ℝ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ} {W : ℝ≥0 → Ω → ℝ}
    {VL : Fin nL → ℝ≥0 → Ω → ℝ} {VR : Fin nR → ℝ≥0 → Ω → ℝ}
    (hWc : ∀ ω, Continuous fun t => W t ω) (hordL : ∀ ω t i, VL i t ω ≤ W t ω)
    (hordR : ∀ ω t i, W t ω ≤ VR i t ω) {z : ℂ} {ω : Ω} {t T' : ℝ≥0} (htT' : t ≤ T')
    (hz : z ∈ H \ QuantumZipper.fwdHull (wpath W ω) T') :
    coupProc κ ρL ρR W VL VR z t ω = Real.pi / Real.sqrt κ * (1 + ∑ i, ρR i)
      + harmPart κ (jointρ ρL ρR) (wpath W ω) t (jointV (fun i => VL i t ω) (fun i => VR i t ω)) z := by
  have hf : QuantumZipper.fwdMap (wpath W ω) t z ∈ H :=
    Ito.im_fwdMap_pos (continuous_wpath hWc ω) (NNReal.coe_nonneg T') hz
      ⟨NNReal.coe_nonneg t, by exact_mod_cast htT'⟩
  have h := couplingMean_meanExt_eq κ ρL ρR (w := wpath W ω) (t := t)
    (vL := fun i => VL i t ω) (vR := fun i => VR i t ω)
    (fun i => by rw [wpath_coe]; exact hordL ω t i) (fun i => by rw [wpath_coe]; exact hordR ω t i) hf
  rw [wpath_coe] at h
  exact h

lemma jointV_apply_eq {β : Type*} (VL : Fin nL → ℝ≥0 → Ω → β) (VR : Fin nR → ℝ≥0 → Ω → β)
    (t : ℝ≥0) (ω : Ω) :
    jointV (fun i => VL i t ω) (fun i => VR i t ω) = fun j => jointV VL VR j t ω := by
  funext j; cases j <;> rfl

/-- **The coupling mean stopped at a localizing time has constant set integrals**, for every `z`
far enough from the origin, when it is a local martingale before `z` is swallowed. -/
theorem setIntegral_stoppedProcess_coupProc_eq [IsProbabilityMeasure P] {κ : ℝ}
    {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ} {W : ℝ≥0 → Ω → ℝ} {VL : Fin nL → ℝ≥0 → Ω → ℝ}
    {VR : Fin nR → ℝ≥0 → Ω → ℝ} {xL : Fin nL → ℝ} {xR : Fin nR → ℝ}
    (hW0 : ∀ ω, W 0 ω = 0) (hVL0 : ∀ i ω, VL i 0 ω = xL i) (hVR0 : ∀ i ω, VR i 0 ω = xR i)
    (hWc : ∀ ω, Continuous fun t => W t ω) (hVLc : ∀ i ω, Continuous fun t => VL i t ω)
    (hVRc : ∀ i ω, Continuous fun t => VR i t ω) (hWa : StronglyAdapted 𝓕 W)
    (hVLa : ∀ i, StronglyAdapted 𝓕 (VL i)) (hVRa : ∀ i, StronglyAdapted 𝓕 (VR i))
    (hordL : ∀ ω t i, VL i t ω ≤ W t ω) (hordR : ∀ ω t i, W t ω ≤ VR i t ω) {z : ℂ}
    (hzH : z ∈ H)
    (hmart : IsLocalMartingaleBefore 𝓕 P
      (fun ω => (QuantumZipper.swallowTime (wpath W ω) z : WithTop ℝ≥0))
      (coupProc κ ρL ρR W VL VR z))
    (T N : ℕ) (hzR : laurentRadius ((N : ℝ) + |(0 : ℝ)| + ∑ j, |jointV xL xR j|) T ≤ ‖z‖) :
    (∀ t, Integrable
      (stoppedProcess (coupProc κ ρL ρR W VL VR z) (locTime W (jointV VL VR) T N) t) P) ∧
      ∀ s t : ℝ≥0, s ≤ t → ∀ A, MeasurableSet[𝓕 s] A →
        ∫ ω in A, stoppedProcess (coupProc κ ρL ρR W VL VR z) (locTime W (jointV VL VR) T N) t ω ∂P
          = ∫ ω in A, stoppedProcess (coupProc κ ρL ρR W VL VR z)
              (locTime W (jointV VL VR) T N) s ω ∂P := by
  set V := jointV VL VR with hV
  set ρ := jointρ ρL ρR with hρ
  set K : ℝ := (N : ℝ) + |(0 : ℝ)| + ∑ j, |jointV xL xR j| with hK
  set τ := locTime W V T N with hτdef
  set c : ℝ := Real.pi / Real.sqrt κ * (1 + ∑ i, ρR i) with hc
  have hVc : ∀ j ω, Continuous fun t => V j t ω := fun j ω => by
    cases j with
    | inl i => exact hVLc i ω
    | inr i => exact hVRc i ω
  have hVa : ∀ j, StronglyAdapted 𝓕 (V j) := fun j => by
    cases j with
    | inl i => exact hVLa i
    | inr i => exact hVRa i
  have hV0 : ∀ j ω, V j 0 ω = jointV xL xR j := fun j ω => by
    cases j with
    | inl i => exact hVL0 i ω
    | inr i => exact hVR0 i ω
  have hτ : IsStoppingTime 𝓕 τ := isStoppingTime_locTime hWc hVc hWa hVa T N
  have hτT : ∀ ω, τ ω ≤ ((T : ℝ≥0) : WithTop ℝ≥0) := locTime_le T N
  have hbd : ∀ ω (t : ℝ≥0), (t : WithTop ℝ≥0) ≤ τ ω → |W t ω| ≤ K ∧ ∀ j, |V j t ω| ≤ K :=
    fun ω t ht => abs_le_of_le_locTime hW0 hV0 hWc hVc ht
  have hle_T : ∀ ω (t : ℝ≥0), (t : WithTop ℝ≥0) ≤ τ ω → (t : ℝ) ≤ T := fun ω t ht => by
    have := ht.trans (hτT ω)
    exact_mod_cast (WithTop.coe_le_coe.1 this)
  have hpb : ∀ ω (t : ℝ≥0), (t : WithTop ℝ≥0) ≤ τ ω → ∀ r ∈ Icc (0 : ℝ) t, |wpath W ω r| ≤ K :=
    fun ω t ht r hr => (hbd ω r.toNNReal ((WithTop.coe_le_coe.2
      (Real.toNNReal_le_iff_le_coe.2 hr.2)).trans ht)).1
  have hR1 : 1 ≤ ‖z‖ := (one_le_laurentRadius _ _).trans hzR
  have hR3 : 2 * dispConst K T + 1 ≤ ‖z‖ :=
    (le_max_left _ _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans hzR))
  have hR4 : K + 3 * Real.sqrt T + 1 ≤ ‖z‖ :=
    (le_max_right _ _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans hzR))
  have hns : ∀ ω (t : ℝ≥0), (t : WithTop ℝ≥0) ≤ τ ω →
      z ∈ H \ QuantumZipper.fwdHull (wpath W ω) t := fun ω t ht => by
    refine mem_diff_fwdHull_of_norm (continuous_wpath hWc ω) (NNReal.coe_nonneg t) (hpb ω t ht)
      hzH ?_
    have := Real.sqrt_le_sqrt (hle_T ω t ht)
    linarith
  -- `τ` comes before the swallowing time
  have hτζ : ∀ ω, τ ω < (QuantumZipper.swallowTime (wpath W ω) z : WithTop ℝ≥0) := fun ω => by
    have hne : τ ω ≠ ⊤ := ne_top_of_le_ne_top WithTop.coe_ne_top (hτT ω)
    obtain ⟨r, hr⟩ := WithTop.ne_top_iff_exists.1 hne
    have hz := hns ω r (hr ▸ le_rfl)
    have hnot : ¬ QuantumZipper.swallowTime (wpath W ω) z ≤ ENNReal.ofReal r :=
      fun h => hz.2 ⟨hzH, h⟩
    rw [not_le, ENNReal.ofReal_coe_nnreal] at hnot
    rw [← hr]
    exact hnot
  -- right-continuity before swallowing
  have hrc : ∀ ω (s : ℝ≥0), (s : WithTop ℝ≥0) < (QuantumZipper.swallowTime (wpath W ω) z : WithTop ℝ≥0) →
      ContinuousWithinAt (coupProc κ ρL ρR W VL VR z · ω) (Ici s) s := by
    intro ω s hs
    obtain ⟨T', hsT', hT'⟩ := ENNReal.lt_iff_exists_nnreal_btwn.1 hs
    have hsT'' : s < T' := ENNReal.coe_lt_coe.1 hsT'
    have hzT' : z ∈ H \ QuantumZipper.fwdHull (wpath W ω) T' := by
      refine ⟨hzH, fun h => ?_⟩
      have h2 := h.2
      rw [ENNReal.ofReal_coe_nnreal] at h2
      exact absurd h2 (not_le.2 hT')
    set g : ℝ → ℝ := fun x => c + harmPart κ ρ (wpath W ω) x (fun j => V j x.toNNReal ω) z with hg_def
    have hg : ContinuousOn g (Icc 0 T') :=
      continuousOn_const.add (continuousOn_harmPart κ ρ (continuous_wpath hWc ω)
        (NNReal.coe_nonneg T') hzT' fun j => ((hVc j ω).comp continuous_real_toNNReal).continuousOn)
    have heq : ∀ t : ℝ≥0, t ≤ T' → coupProc κ ρL ρR W VL VR z t ω = g t := fun t ht => by
      rw [coupProc_eq hWc hordL hordR ht hzT', hg_def, jointV_apply_eq]
      simp only [Real.toNNReal_coe, hc, hρ, hV]
    have hgc : ContinuousOn (fun t : ℝ≥0 => g t) (Iic T') :=
      hg.comp NNReal.continuous_coe.continuousOn fun t ht =>
        ⟨NNReal.coe_nonneg t, by exact_mod_cast ht⟩
    have hca : ContinuousAt (fun t : ℝ≥0 => g t) s := hgc.continuousAt (Iic_mem_nhds hsT'')
    have heq' : (fun t : ℝ≥0 => g t) =ᶠ[𝓝 s] (coupProc κ ρL ρR W VL VR z · ω) := by
      filter_upwards [Iic_mem_nhds hsT''] with t ht
      exact (heq t ht).symm
    exact (hca.congr heq').continuousWithinAt
  -- the bound
  have hC : ∀ ω (t : ℝ≥0), (t : WithTop ℝ≥0) ≤ τ ω →
      |coupProc κ ρL ρR W VL VR z t ω| ≤ |c| + harmBound κ ρ K T := fun ω t ht => by
    rw [coupProc_eq hWc hordL hordR le_rfl (hns ω t ht)]
    refine (abs_add_le _ _).trans (add_le_add le_rfl ?_)
    exact abs_harmPart_le κ ρ (continuous_wpath hWc ω) (by simp [wpath, hW0])
      (NNReal.coe_nonneg t) (hle_T ω t ht) (hpb ω t ht) _ (hns ω t ht) hR1 (by linarith)
  exact setIntegral_stoppedProcess_eq_of_isLocalMartingaleBefore hmart hrc hτ hτT
    (ae_of_all _ hτζ) hC

/-- **The Laurent-coefficient processes are martingales up to every localizing time** when every
coupling mean `𝔥_t(z)`, `z ∈ ℍ`, is a local martingale before `z` is swallowed. -/
theorem martingale_driftProc_quadProc_of_couplingMean [IsProbabilityMeasure P] {κ : ℝ}
    (hκ : 0 < κ) {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ} {W : ℝ≥0 → Ω → ℝ}
    {VL : Fin nL → ℝ≥0 → Ω → ℝ} {VR : Fin nR → ℝ≥0 → Ω → ℝ} {xL : Fin nL → ℝ}
    {xR : Fin nR → ℝ} (hW0 : ∀ ω, W 0 ω = 0) (hVL0 : ∀ i ω, VL i 0 ω = xL i)
    (hVR0 : ∀ i ω, VR i 0 ω = xR i) (hWc : ∀ ω, Continuous fun t => W t ω)
    (hVLc : ∀ i ω, Continuous fun t => VL i t ω) (hVRc : ∀ i ω, Continuous fun t => VR i t ω)
    (hWa : StronglyAdapted 𝓕 W) (hVLa : ∀ i, StronglyAdapted 𝓕 (VL i))
    (hVRa : ∀ i, StronglyAdapted 𝓕 (VR i)) (hordL : ∀ ω t i, VL i t ω ≤ W t ω)
    (hordR : ∀ ω t i, W t ω ≤ VR i t ω)
    (hmart : ∀ z ∈ H, IsLocalMartingaleBefore 𝓕 P
      (fun ω => (QuantumZipper.swallowTime (wpath W ω) z : WithTop ℝ≥0))
      (coupProc κ ρL ρR W VL VR z))
    (T N : ℕ) :
    Martingale (stoppedProcess (driftProc (jointρ ρL ρR) W (jointV VL VR))
        (locTime W (jointV VL VR) T N)) 𝓕 P ∧
      Martingale (stoppedProcess (quadProc κ (jointρ ρL ρR) W (jointV VL VR))
        (locTime W (jointV VL VR) T N)) 𝓕 P := by
  set V := jointV VL VR with hV
  set ρ := jointρ ρL ρR with hρ
  set K : ℝ := (N : ℝ) + |(0 : ℝ)| + ∑ j, |jointV xL xR j| with hK
  set τ := locTime W V T N with hτdef
  set c : ℝ := Real.pi / Real.sqrt κ * (1 + ∑ i, ρR i) with hc
  set R := laurentRadius K T with hR
  have hVc : ∀ j ω, Continuous fun t => V j t ω := fun j ω => by
    cases j with
    | inl i => exact hVLc i ω
    | inr i => exact hVRc i ω
  have hVa : ∀ j, StronglyAdapted 𝓕 (V j) := fun j => by
    cases j with
    | inl i => exact hVLa i
    | inr i => exact hVRa i
  have hV0 : ∀ j ω, V j 0 ω = jointV xL xR j := fun j ω => by
    cases j with
    | inl i => exact hVL0 i ω
    | inr i => exact hVR0 i ω
  have hτ : IsStoppingTime 𝓕 τ := isStoppingTime_locTime hWc hVc hWa hVa T N
  have hτT : ∀ ω, τ ω ≤ ((T : ℝ≥0) : WithTop ℝ≥0) := locTime_le T N
  have hK0 : 0 ≤ K := by
    have : 0 ≤ ∑ j, |jointV xL xR j| := Finset.sum_nonneg fun j _ => abs_nonneg _
    positivity
  have hsk : 0 < Real.sqrt κ := Real.sqrt_pos.2 hκ
  -- stopped times and bounds
  set θ : ℝ≥0 → Ω → ℝ≥0 := fun u ω => (min (u : WithTop ℝ≥0) (τ ω)).untopA with hθ
  have hθτ : ∀ u ω, ((θ u ω : ℝ≥0) : WithTop ℝ≥0) ≤ τ ω := fun u ω => by
    simp only [hθ]
    rw [coe_untopA_of_ne_top (ne_top_of_le_ne_top WithTop.coe_ne_top (min_le_left _ _))]
    exact min_le_right _ _
  have hθT : ∀ u ω, (θ u ω : ℝ) ≤ T := fun u ω => by
    have := (hθτ u ω).trans (hτT ω)
    exact_mod_cast (WithTop.coe_le_coe.1 this)
  have hbd : ∀ u ω, |W (θ u ω) ω| ≤ K ∧ ∀ j, |V j (θ u ω) ω| ≤ K := fun u ω =>
    abs_le_of_le_locTime hW0 hV0 hWc hVc (hθτ u ω)
  have hpb : ∀ u ω, ∀ r ∈ Icc (0 : ℝ) (θ u ω), |wpath W ω r| ≤ K := fun u ω r hr =>
    (abs_le_of_le_locTime hW0 hV0 hWc hVc ((WithTop.coe_le_coe.2
      (Real.toNNReal_le_iff_le_coe.2 hr.2)).trans (hθτ u ω))).1
  have hw0 : ∀ ω, wpath W ω 0 = 0 := fun ω => by simp [wpath, hW0]
  -- the identity at stopped times
  have hstop : ∀ (z : ℂ), z ∈ H → R ≤ ‖z‖ → ∀ u ω,
      stoppedProcess (coupProc κ ρL ρR W VL VR z) τ u ω
        = c + harmPart κ ρ (wpath W ω) (θ u ω) (fun j => V j (θ u ω) ω) z := by
    intro z hzH hzR u ω
    have hR4 : K + 3 * Real.sqrt T + 1 ≤ ‖z‖ :=
      (le_max_right _ _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans hzR))
    have hns : z ∈ H \ QuantumZipper.fwdHull (wpath W ω) (θ u ω) := by
      refine mem_diff_fwdHull_of_norm (continuous_wpath hWc ω) (NNReal.coe_nonneg _) (hpb u ω)
        hzH ?_
      have := Real.sqrt_le_sqrt (hθT u ω)
      linarith
    show coupProc κ ρL ρR W VL VR z (θ u ω) ω = _
    rw [coupProc_eq hWc hordL hordR le_rfl hns, jointV_apply_eq]
  -- the radii
  set Y : ℕ → ℝ := fun k => (k : ℝ) + R with hY
  have hR1 : 1 ≤ R := one_le_laurentRadius K T
  have hYR : ∀ k, R ≤ Y k := fun k => by simp only [hY]; linarith [(Nat.cast_nonneg k : (0 : ℝ) ≤ k)]
  have hYpos : ∀ k, 0 < Y k := fun k => by linarith [hYR k]
  have hYtop : Tendsto Y atTop atTop := tendsto_atTop_add_const_right _ R tendsto_natCast_atTop_atTop
  have hzI : ∀ k, ((Y k : ℂ) * Complex.I) ∈ H ∧ R ≤ ‖(Y k : ℂ) * Complex.I‖ := fun k => by
    refine ⟨?_, ?_⟩
    · show 0 < ((Y k : ℂ) * Complex.I).im
      simp [hYpos k]
    · rw [norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos (hYpos k)]
      exact hYR k
  have hzD : ∀ k, ((Y k : ℂ) * (1 + Complex.I)) ∈ H ∧ R ≤ ‖(Y k : ℂ) * (1 + Complex.I)‖ :=
    fun k => by
      refine ⟨?_, ?_⟩
      · show 0 < ((Y k : ℂ) * (1 + Complex.I)).im
        simp [hYpos k]
      · have h1I : (1 : ℝ) ≤ ‖(1 : ℂ) + Complex.I‖ := by
          have h := Complex.abs_re_le_norm ((1 : ℂ) + Complex.I)
          simp only [Complex.add_re, Complex.one_re, Complex.I_re, add_zero, abs_one] at h
          exact h
        rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (hYpos k)]
        nlinarith [hYR k, hYpos k]
  -- the two coupling processes at the radii
  have hI := fun k => setIntegral_stoppedProcess_coupProc_eq hW0 hVL0 hVR0 hWc hVLc hVRc hWa hVLa
    hVRa hordL hordR (hzI k).1 (hmart _ (hzI k).1) T N (hzI k).2
  have hD := fun k => setIntegral_stoppedProcess_coupProc_eq hW0 hVL0 hVR0 hWc hVLc hVRc hWa hVLa
    hVRa hordL hordR (hzD k).1 (hmart _ (hzD k).1) T N (hzD k).2
  -- adaptedness and integrability of `N^τ`, `Q^τ`
  have hNc : ∀ ω, Continuous fun t => driftProc ρ W V t ω := fun ω => by
    simp only [driftProc, driftValue]
    exact (continuous_const.mul (hWc ω)).add (continuous_finsetSum _ fun j _ =>
      continuous_const.mul (hVc j ω))
  have hQc : ∀ ω, Continuous fun t => quadProc κ ρ W V t ω := fun ω => by
    simp only [quadProc, quadValue]
    exact (((hWc ω).pow 2).add (continuous_const.mul (continuous_finsetSum _ fun j _ =>
      continuous_const.mul ((hVc j ω).pow 2)))).sub
      (continuous_const.mul NNReal.continuous_coe)
  have hNa : StronglyAdapted 𝓕 (driftProc ρ W V) := fun t => by
    have h1 := (hWa t).measurable
    have h2 := fun j => ((hVa j) t).measurable
    have : Measurable[𝓕 t] (driftProc ρ W V t) := by
      show Measurable[𝓕 t] fun ω => 2 * W t ω + ∑ j, ρ j * V j t ω
      fun_prop
    exact this.stronglyMeasurable
  have hQa : StronglyAdapted 𝓕 (quadProc κ ρ W V) := fun t => by
    have h1 := (hWa t).measurable
    have h2 := fun j => ((hVa j) t).measurable
    have : Measurable[𝓕 t] (quadProc κ ρ W V t) := by
      show Measurable[𝓕 t] fun ω =>
        W t ω ^ 2 + 1 / 2 * (∑ j, ρ j * V j t ω ^ 2) - (2 * (∑ j, ρ j) + κ) * (t : ℝ)
      fun_prop
    exact this.stronglyMeasurable
  have hNsa := stronglyAdapted_stoppedProcess_of_continuous hNa hNc hτ
  have hQsa := stronglyAdapted_stoppedProcess_of_continuous hQa hQc hτ
  have hNval : ∀ u ω, stoppedProcess (driftProc ρ W V) τ u ω
      = driftValue ρ (wpath W ω (θ u ω)) (fun j => V j (θ u ω) ω) := fun u ω => by
    rw [wpath_coe]; rfl
  have hQval : ∀ u ω, stoppedProcess (quadProc κ ρ W V) τ u ω
      = quadValue κ ρ (wpath W ω (θ u ω)) (fun j => V j (θ u ω) ω) (θ u ω) := fun u ω => by
    rw [wpath_coe]; rfl
  set Rρ : ℝ := ∑ j, |ρ j| with hRρ
  have hRρ0 : 0 ≤ Rρ := Finset.sum_nonneg fun j _ => abs_nonneg _
  have hNb : ∀ u ω, |stoppedProcess (driftProc ρ W V) τ u ω| ≤ 2 * K + Rρ * K := fun u ω => by
    rw [hNval, wpath_coe]
    simp only [driftValue]
    have h1 : |∑ j, ρ j * V j (θ u ω) ω| ≤ Rρ * K := by
      refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
      rw [hRρ, Finset.sum_mul]
      exact Finset.sum_le_sum fun j _ => by
        rw [abs_mul]; exact mul_le_mul_of_nonneg_left ((hbd u ω).2 j) (abs_nonneg _)
    have h2 : |2 * W (θ u ω) ω| ≤ 2 * K := by
      rw [abs_mul, abs_two]; linarith [(hbd u ω).1]
    exact (abs_add_le _ _).trans (by linarith)
  have hQb : ∀ u ω, |stoppedProcess (quadProc κ ρ W V) τ u ω|
      ≤ K ^ 2 + Rρ * K ^ 2 + |2 * (∑ j, ρ j) + κ| * T := fun u ω => by
    rw [hQval, wpath_coe]
    simp only [quadValue]
    have h1 : |∑ j, ρ j * V j (θ u ω) ω ^ 2| ≤ Rρ * K ^ 2 := by
      refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
      rw [hRρ, Finset.sum_mul]
      exact Finset.sum_le_sum fun j _ => by
        rw [abs_mul, abs_pow]
        exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (abs_nonneg _) ((hbd u ω).2 j) 2)
          (abs_nonneg _)
    have h2 : |W (θ u ω) ω ^ 2| ≤ K ^ 2 := by
      rw [abs_pow]; exact pow_le_pow_left₀ (abs_nonneg _) (hbd u ω).1 2
    have h3 : |(2 * (∑ j, ρ j) + κ) * (θ u ω : ℝ)| ≤ |2 * (∑ j, ρ j) + κ| * T := by
      rw [abs_mul, NNReal.abs_eq]
      exact mul_le_mul_of_nonneg_left (hθT u ω) (abs_nonneg _)
    have h4 : |1 / 2 * ∑ j, ρ j * V j (θ u ω) ω ^ 2| ≤ Rρ * K ^ 2 := by
      rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)]
      have : 0 ≤ Rρ * K ^ 2 := by positivity
      linarith
    calc _ ≤ |W (θ u ω) ω ^ 2 + 1 / 2 * ∑ j, ρ j * V j (θ u ω) ω ^ 2|
          + |(2 * (∑ j, ρ j) + κ) * (θ u ω : ℝ)| := abs_sub _ _
      _ ≤ _ := by linarith [abs_add_le (W (θ u ω) ω ^ 2) (1 / 2 * ∑ j, ρ j * V j (θ u ω) ω ^ 2)]
  have hNint : ∀ u, Integrable (stoppedProcess (driftProc ρ W V) τ u) P := fun u =>
    Integrable.of_bound ((hNsa u).mono (𝓕.le u)).aestronglyMeasurable _
      (Eventually.of_forall fun ω => by rw [Real.norm_eq_abs]; exact hNb u ω)
  have hQint : ∀ u, Integrable (stoppedProcess (quadProc κ ρ W V) τ u) P := fun u =>
    Integrable.of_bound ((hQsa u).mono (𝓕.le u)).aestronglyMeasurable _
      (Eventually.of_forall fun ω => by rw [Real.norm_eq_abs]; exact hQb u ω)
  set C := harmConst κ ρ K T with hCdef
  -- set integrals of an affine function of a process
  have haff : ∀ (X : ℝ≥0 → Ω → ℝ), (∀ u, Integrable (X u) P) → ∀ (a b : ℝ) (u : ℝ≥0) (A : Set Ω),
      ∫ ω in A, (a * X u ω + b) ∂P = a * ∫ ω in A, X u ω ∂P + b * (P A).toReal := by
    intro X hX a b u A
    rw [integral_add ((hX u).integrableOn.const_mul a) (integrable_const b),
      integral_const_mul, setIntegral_const, smul_eq_mul, mul_comm (P.real A)]
    rfl
  -- the first coefficient
  have hNmart : Martingale (stoppedProcess (driftProc ρ W V) τ) 𝓕 P := by
    refine martingale_of_forall_abs_sub_le hNsa hNint
      (G := fun k t ω => -(Real.sqrt κ * Y k)
        * stoppedProcess (coupProc κ ρL ρR W VL VR ((Y k : ℂ) * Complex.I)) τ t ω
        + Real.sqrt κ * Y k * (c + phiI κ ρ))
      (fun k t => (((hI k).1 t).aestronglyMeasurable.const_mul _).add aestronglyMeasurable_const)
      (ε := fun k => Real.sqrt κ * C / Y k ^ 2) ?_ ?_ ?_
    · exact tendsto_const_nhds.div_atTop ((tendsto_pow_atTop two_ne_zero).comp hYtop)
    · intro k t ω
      rw [hstop _ (hzI k).1 (hzI k).2, hNval]
      have hl := abs_laurent_one_le κ ρ (continuous_wpath hWc ω) (hw0 ω) (NNReal.coe_nonneg _)
        (hθT t ω) (hpb t ω) (hbd t ω).2 (hYR k)
      have hid : -(Real.sqrt κ * Y k) * (c + harmPart κ ρ (wpath W ω) (θ t ω)
          (fun j => V j (θ t ω) ω) ((Y k : ℂ) * Complex.I)) + Real.sqrt κ * Y k * (c + phiI κ ρ)
          - driftValue ρ (wpath W ω (θ t ω)) (fun j => V j (θ t ω) ω)
          = -(Real.sqrt κ * (Y k * (harmPart κ ρ (wpath W ω) (θ t ω) (fun j => V j (θ t ω) ω)
              ((Y k : ℂ) * Complex.I) - phiI κ ρ)
            + driftValue ρ (wpath W ω (θ t ω)) (fun j => V j (θ t ω) ω) / Real.sqrt κ)) := by
        field_simp; ring
      rw [hid, abs_neg, abs_mul, abs_of_pos hsk]
      calc _ ≤ Real.sqrt κ * (C / Y k ^ 2) := mul_le_mul_of_nonneg_left hl hsk.le
        _ = Real.sqrt κ * C / Y k ^ 2 := by ring
    · intro k s t hst A hA
      rw [haff _ (hI k).1, haff _ (hI k).1, (hI k).2 s t hst A hA]
  refine ⟨hNmart, ?_⟩
  -- the second coefficient
  refine martingale_of_forall_abs_sub_le hQsa hQint
    (G := fun k t ω => -(2 * Y k ^ 2 * Real.sqrt κ)
      * stoppedProcess (coupProc κ ρL ρR W VL VR ((Y k : ℂ) * (1 + Complex.I))) τ t ω
      + 2 * Y k ^ 2 * Real.sqrt κ * (c + phiD κ ρ)
      - Y k * stoppedProcess (driftProc ρ W V) τ t ω)
    (fun k t => ((((hD k).1 t).aestronglyMeasurable.const_mul _).add
      aestronglyMeasurable_const).sub ((hNint t).aestronglyMeasurable.const_mul _))
    (ε := fun k => 2 * Real.sqrt κ * C / Y k) ?_ ?_ ?_
  · exact tendsto_const_nhds.div_atTop hYtop
  · intro k t ω
    rw [hstop _ (hzD k).1 (hzD k).2, hNval, hQval]
    have hl := abs_laurent_two_le hκ ρ (continuous_wpath hWc ω) (hw0 ω) (NNReal.coe_nonneg _)
      (hθT t ω) (hpb t ω) (hbd t ω).2 (hYR k)
    have hid : -(2 * Y k ^ 2 * Real.sqrt κ) * (c + harmPart κ ρ (wpath W ω) (θ t ω)
        (fun j => V j (θ t ω) ω) ((Y k : ℂ) * (1 + Complex.I)))
        + 2 * Y k ^ 2 * Real.sqrt κ * (c + phiD κ ρ)
        - Y k * driftValue ρ (wpath W ω (θ t ω)) (fun j => V j (θ t ω) ω)
        - quadValue κ ρ (wpath W ω (θ t ω)) (fun j => V j (θ t ω) ω) (θ t ω)
        = -(2 * Y k ^ 2 * Real.sqrt κ * (harmPart κ ρ (wpath W ω) (θ t ω) (fun j => V j (θ t ω) ω)
            ((Y k : ℂ) * (1 + Complex.I)) - phiD κ ρ)
          + Y k * driftValue ρ (wpath W ω (θ t ω)) (fun j => V j (θ t ω) ω)
          + quadValue κ ρ (wpath W ω (θ t ω)) (fun j => V j (θ t ω) ω) (θ t ω)) := by ring
    rw [hid, abs_neg]
    exact hl
  · intro k s t hst A hA
    have hX := (hD k).1
    have h1 : ∀ u, ∫ ω in A, (-(2 * Y k ^ 2 * Real.sqrt κ)
        * stoppedProcess (coupProc κ ρL ρR W VL VR ((Y k : ℂ) * (1 + Complex.I))) τ u ω
        + 2 * Y k ^ 2 * Real.sqrt κ * (c + phiD κ ρ)
        - Y k * stoppedProcess (driftProc ρ W V) τ u ω) ∂P
        = (-(2 * Y k ^ 2 * Real.sqrt κ) * ∫ ω in A,
            stoppedProcess (coupProc κ ρL ρR W VL VR ((Y k : ℂ) * (1 + Complex.I))) τ u ω ∂P
          + 2 * Y k ^ 2 * Real.sqrt κ * (c + phiD κ ρ) * (P A).toReal)
          - Y k * ∫ ω in A, stoppedProcess (driftProc ρ W V) τ u ω ∂P := fun u => by
      have hI1 : IntegrableOn (fun ω => -(2 * Y k ^ 2 * Real.sqrt κ)
          * stoppedProcess (coupProc κ ρL ρR W VL VR ((Y k : ℂ) * (1 + Complex.I))) τ u ω
          + 2 * Y k ^ 2 * Real.sqrt κ * (c + phiD κ ρ)) A P :=
        ((hX u).integrableOn.const_mul _).add (integrable_const _)
      have hI2 : IntegrableOn (fun ω => Y k * stoppedProcess (driftProc ρ W V) τ u ω) A P :=
        (hNint u).integrableOn.const_mul _
      rw [integral_sub hI1 hI2, integral_const_mul, haff _ hX]
    rw [h1, h1, (hD k).2 s t hst A hA, hNmart.setIntegral_eq hst hA]

end Process

end MartChar

end InteractingSLE
