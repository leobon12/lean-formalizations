import InteractingSLE.Spec.Ito.Bracket

/-!
# The Itô derivative of `log f_t(z)`

Packet PROVE-T11-ITO (Specification L498, second display):
`d log f_t(z) = ((4 − κ)/(2 f_t(z)²) − ∑ ρ/(f_t(z)(W_t − V_t))) dt − (√κ/f_t(z)) dB_t`.
In martingale form, for every protected stopping time `σ` (`exists_martingale_log_fwdMap`): both
`log |f_{t∧σ}(z)| − ∫₀^{t∧σ} Re D_s ds` and `arg f_{t∧σ}(z) − ∫₀^{t∧σ} Im D_s ds`, `D_s = (4 − κ)/(2 f_s²) − μ_s/f_s`,
agree almost surely, at every time, with martingales (the real and imaginary parts of `log f`, with `arg` the
principal branch, continuous on `ℍ`).
-/

set_option autoImplicit false

noncomputable section

open Set Filter MeasureTheory ProbabilityTheory Topology Complex
open scoped NNReal ENNReal

namespace InteractingSLE

namespace Ito

variable {nL nR : ℕ}

/-- `arg f` as a function of the coordinates (`f = Γ − √κ x`). -/
def argF (κ : ℝ) (p : Coord nL nR × ℝ) : ℝ := arg (coordF κ p)

/-- `log |f|` as a function of the coordinates. -/
def logNormF (κ : ℝ) (p : Coord nL nR × ℝ) : ℝ := Real.log ‖coordF κ p‖

theorem coordF_ne_zero {κ : ℝ} {p : Coord nL nR × ℝ} (hp : p ∈ obsRegion κ) : coordF κ p ≠ 0 :=
  fun h => by have := hp.1; rw [h, zero_im] at this; exact lt_irrefl 0 this

theorem contDiffAt_argF (κ : ℝ) {n : WithTop ℕ∞} {p : Coord nL nR × ℝ} (hp : p ∈ obsRegion κ) :
    ContDiffAt ℝ n (argF κ) p :=
  (contDiffAt_arg (mem_slitPlane_of_im_pos hp.1)).comp p (contDiff_coordF κ).contDiffAt

theorem contDiffAt_logNormF (κ : ℝ) {n : WithTop ℕ∞} {p : Coord nL nR × ℝ} (hp : p ∈ obsRegion κ) :
    ContDiffAt ℝ n (logNormF κ) p :=
  (Real.contDiffAt_log.2 (norm_ne_zero_iff.2 (coordF_ne_zero hp))).comp p
    ((contDiffAt_norm ℂ (coordF_ne_zero hp)).comp p (contDiff_coordF κ).contDiffAt)

theorem hasDerivAt_coordF_line (κ : ℝ) (p : Coord nL nR × ℝ) (v : Coord nL nR) :
    HasDerivAt (fun t : ℝ => coordF κ ((p.1 + t • v, p.2) : Coord nL nR × ℝ)) v.1 0 := by
  have h1 := ((hasDerivAt_id (0 : ℝ)).ofReal_comp.mul_const v.1).const_add (coordF κ p)
  refine (h1.congr_deriv (by simp)).congr_of_eventuallyEq (Eventually.of_forall fun t => ?_)
  simp [coordF, Complex.real_smul]; ring

/-- The generator of `arg f`: `Im(v_Γ/f) + ½ Im(−(√κ)²/f²)`. -/
theorem itoGen_argF (κ : ℝ) {p : Coord nL nR × ℝ} (hp : p ∈ obsRegion κ) (v : Coord nL nR) :
    itoGen (argF κ) p v = (v.1 / coordF κ p).im +
      1 / 2 * ((-(Real.sqrt κ : ℂ) ^ 2) / coordF κ p ^ 2).im := by
  have hd : DifferentiableAt ℝ (argF κ) p := (contDiffAt_argF κ (n := 1) hp).differentiableAt one_ne_zero
  have hslit := mem_slitPlane_of_im_pos hp.1
  have h1 : partialFst (argF κ) p v = (v.1 / coordF κ p).im := by
    refine partialFst_eq_of_hasDerivAt hd ?_
    have := hasDerivAt_arg_comp (hasDerivAt_coordF_line κ p v) (by simpa using hslit)
    simpa [argF] using this
  have hsnd : ∀ q : Coord nL nR × ℝ, q ∈ obsRegion κ →
      partialSnd (argF κ) q = ((-(Real.sqrt κ : ℂ)) / coordF κ q).im := fun q hq =>
    partialSnd_eq_of_hasDerivAt ((contDiffAt_argF κ (n := 1) hq).differentiableAt one_ne_zero)
      (hasDerivAt_arg_comp (hasDerivAt_coordF_snd κ q.1 q.2) (mem_slitPlane_of_im_pos hq.1))
  have h2 : partialSndSnd (argF κ) p = ((-(Real.sqrt κ : ℂ) ^ 2) / coordF κ p ^ 2).im := by
    refine partialSndSnd_eq_of_hasDerivAt (contDiffAt_argF κ hp)
      (g := fun y => ((-(Real.sqrt κ : ℂ)) / coordF κ ((p.1, y) : Coord nL nR × ℝ)).im) ?_ ?_
    · have hc : Continuous fun y : ℝ => ((p.1, y) : Coord nL nR × ℝ) :=
        continuous_const.prodMk continuous_id
      have hopen : ∀ᶠ y in 𝓝 p.2, ((p.1, y) : Coord nL nR × ℝ) ∈ obsRegion κ :=
        hc.continuousAt.preimage_mem_nhds ((isOpen_obsRegion κ).mem_nhds hp)
      exact hopen.mono fun y hy => hsnd _ hy
    · have hne : coordF κ ((p.1, p.2) : Coord nL nR × ℝ) ≠ 0 := coordF_ne_zero hp
      have hdiv := (hasDerivAt_const p.2 (-(Real.sqrt κ : ℂ))).div
        (hasDerivAt_coordF_snd κ p.1 p.2) hne
      refine (imCLM.hasFDerivAt.comp_hasDerivAt p.2 hdiv).congr_deriv ?_
      have e : (0 * coordF κ p - -(Real.sqrt κ : ℂ) * -(Real.sqrt κ : ℂ)) / coordF κ p ^ 2 =
          -(Real.sqrt κ : ℂ) ^ 2 / coordF κ p ^ 2 := by ring
      simp only [imCLM_apply, Prod.mk.eta, e]
  simp only [itoGen, h1, h2]

/-- The generator of `log |f|`: `Re(v_Γ/f) + ½ Re(−(√κ)²/f²)`. -/
theorem itoGen_logNormF (κ : ℝ) {p : Coord nL nR × ℝ} (hp : p ∈ obsRegion κ) (v : Coord nL nR) :
    itoGen (logNormF κ) p v = (v.1 / coordF κ p).re +
      1 / 2 * ((-(Real.sqrt κ : ℂ) ^ 2) / coordF κ p ^ 2).re := by
  have hd : DifferentiableAt ℝ (logNormF κ) p :=
    (contDiffAt_logNormF κ (n := 1) hp).differentiableAt one_ne_zero
  have h1 : partialFst (logNormF κ) p v = (v.1 / coordF κ p).re := by
    refine partialFst_eq_of_hasDerivAt hd ?_
    have := QuantumZipper.FwdClock.hasDerivWithinAt_log_norm
      (hasDerivAt_coordF_line κ p v).hasDerivWithinAt (s := univ) (by simpa using coordF_ne_zero hp)
    rw [hasDerivWithinAt_univ] at this
    simpa [logNormF] using this
  have hsnd : ∀ q : Coord nL nR × ℝ, q ∈ obsRegion κ →
      partialSnd (logNormF κ) q = ((-(Real.sqrt κ : ℂ)) / coordF κ q).re := fun q hq => by
    refine partialSnd_eq_of_hasDerivAt ((contDiffAt_logNormF κ (n := 1) hq).differentiableAt
      one_ne_zero) ?_
    have := QuantumZipper.FwdClock.hasDerivWithinAt_log_norm
      (hasDerivAt_coordF_snd κ q.1 q.2).hasDerivWithinAt (s := univ) (coordF_ne_zero hq)
    rw [hasDerivWithinAt_univ] at this
    exact this
  have h2 : partialSndSnd (logNormF κ) p = ((-(Real.sqrt κ : ℂ) ^ 2) / coordF κ p ^ 2).re := by
    refine partialSndSnd_eq_of_hasDerivAt (contDiffAt_logNormF κ hp)
      (g := fun y => ((-(Real.sqrt κ : ℂ)) / coordF κ ((p.1, y) : Coord nL nR × ℝ)).re) ?_ ?_
    · have hc : Continuous fun y : ℝ => ((p.1, y) : Coord nL nR × ℝ) :=
        continuous_const.prodMk continuous_id
      have hopen : ∀ᶠ y in 𝓝 p.2, ((p.1, y) : Coord nL nR × ℝ) ∈ obsRegion κ :=
        hc.continuousAt.preimage_mem_nhds ((isOpen_obsRegion κ).mem_nhds hp)
      exact hopen.mono fun y hy => hsnd _ hy
    · have hne : coordF κ ((p.1, p.2) : Coord nL nR × ℝ) ≠ 0 := coordF_ne_zero hp
      have hdiv := (hasDerivAt_const p.2 (-(Real.sqrt κ : ℂ))).div
        (hasDerivAt_coordF_snd κ p.1 p.2) hne
      refine (reCLM.hasFDerivAt.comp_hasDerivAt p.2 hdiv).congr_deriv ?_
      have e : (0 * coordF κ p - -(Real.sqrt κ : ℂ) * -(Real.sqrt κ : ℂ)) / coordF κ p ^ 2 =
          -(Real.sqrt κ : ℂ) ^ 2 / coordF κ p ^ 2 := by ring
      simp only [reCLM_apply, Prod.mk.eta, e]
  simp only [itoGen, h1, h2]

/-- The drift of `log f` at a state: `((2/f − μ)/f) − (√κ)²/(2f²) = (4 − κ)/(2f²) − μ/f` (`κ ≥ 0`). -/
theorem logDrift_eq {κ : ℝ} (hκ : 0 ≤ κ) {f : ℂ} (hf : f ≠ 0) (μ : ℝ) :
    (2 / f - (μ : ℂ)) / f + 1 / 2 * ((-(Real.sqrt κ : ℂ) ^ 2) / f ^ 2) =
      (4 - κ) / (2 * f ^ 2) - μ / f := by
  have hs : (Real.sqrt κ : ℂ) ^ 2 = (κ : ℂ) := by rw [← ofReal_pow, Real.sq_sqrt hκ]
  rw [hs]
  field_simp
  ring

section Martingale

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
  {κ : ℝ} {xL : Fin nL → ℝ} {xR : Fin nR → ℝ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ}
  {W : ℝ≥0 → Ω → ℝ} {VL : Fin nL → ℝ≥0 → Ω → ℝ} {VR : Fin nR → ℝ≥0 → Ω → ℝ} {B : ℝ≥0 → Ω → ℝ}
  {ζ : Ω → ℝ≥0∞}

/-- **The Itô derivative of `log f_t(z)`** (Specification L498): for every protected stopping time `σ`, with
`D_s = (4 − κ)/(2 f_s(z)²) − μ_s/f_s(z)` and `μ_s = ∑ ρ/(W_s − V_s)` (`driftAt`), the processes
`log |f_{t∧σ}(z)| − ∫₀^{t∧σ} Re D_s ds` and `arg f_{t∧σ}(z) − ∫₀^{t∧σ} Im D_s ds` agree almost surely, at every
time, with martingales. -/
theorem exists_martingale_log_fwdMap
    (hE : IsIntegratedSLEEvolution κ xL xR ρL ρR P 𝓕 W VL VR B ζ) (hκ : 0 < κ) {z : ℂ}
    (hz : 0 < z.im) {σ : Ω → ℝ≥0}
    (hσ : IsStoppingTime (nullAugmented 𝓕 P) fun ω => (σ ω : WithTop ℝ≥0)) {δ R N : ℝ}
    (hδ : 0 < δ)
    (hσp : ∀ᵐ ω ∂P, (σ ω : ℝ≥0∞) < ζ ω ∧
      (∃ u, QuantumZipper.IsForwardSol (rpath (W · ω)) z (σ ω) u) ∧
      δ ≤ (QuantumZipper.fwdMap (rpath (W · ω)) (σ ω) z).im ∧ (σ ω : ℝ) ≤ N ∧
      ∀ s ≤ σ ω, |W s ω| ≤ R ∧ |B s ω| ≤ R ∧ (∀ i, |VL i s ω| ≤ R) ∧ ∀ i, |VR i s ω| ≤ R) :
    (∃ M : ℝ≥0 → Ω → ℝ, Martingale M (nullAugmented 𝓕 P) P ∧ ∀ᵐ ω ∂P, ∀ t,
      M t ω = Real.log ‖QuantumZipper.fwdMap (fun s : ℝ => W s.toNNReal ω) (min t (σ ω) : ℝ≥0) z‖ -
        ∫ s in (0 : ℝ)..(min t (σ ω) : ℝ≥0),
          ((4 - κ) / (2 * QuantumZipper.fwdMap (fun s : ℝ => W s.toNNReal ω) s z ^ 2) -
            (driftAt ρL ρR (W · ω) (fun i t => VL i t ω) (fun i t => VR i t ω) s : ℂ) /
              QuantumZipper.fwdMap (fun s : ℝ => W s.toNNReal ω) s z).re) ∧
    (∃ M : ℝ≥0 → Ω → ℝ, Martingale M (nullAugmented 𝓕 P) P ∧ ∀ᵐ ω ∂P, ∀ t,
      M t ω = arg (QuantumZipper.fwdMap (fun s : ℝ => W s.toNNReal ω) (min t (σ ω) : ℝ≥0) z) -
        ∫ s in (0 : ℝ)..(min t (σ ω) : ℝ≥0),
          ((4 - κ) / (2 * QuantumZipper.fwdMap (fun s : ℝ => W s.toNNReal ω) s z ^ 2) -
            (driftAt ρL ρR (W · ω) (fun i t => VL i t ω) (fun i t => VR i t ω) s : ℂ) /
              QuantumZipper.fwdMap (fun s : ℝ => W s.toNNReal ω) s z).im) := by
  -- the generator along the path, for every `s ∈ (0, σ]`
  have hgen : ∀ ω, IsIntegratedSLEPath κ xL xR ρL ρR (fun t => W t ω) (fun i t => VL i t ω)
      (fun i t => VR i t ω) (fun t => B t ω) (ζ ω) → (σ ω : ℝ≥0∞) < ζ ω →
      (∃ u, QuantumZipper.IsForwardSol (rpath (W · ω)) z (σ ω) u) → ∀ s ∈ Ioc (0 : ℝ) (σ ω),
      (densityAt z ρL ρR (W · ω) (fun i t => VL i t ω) (fun i t => VR i t ω) s).1 /
          coordF κ ((coordProc κ z W VL VR B s.toNNReal ω, B s.toNNReal ω) : Coord nL nR × ℝ) +
        1 / 2 * ((-(Real.sqrt κ : ℂ) ^ 2) / coordF κ
          ((coordProc κ z W VL VR B s.toNNReal ω, B s.toNNReal ω) : Coord nL nR × ℝ) ^ 2) =
      (4 - κ) / (2 * QuantumZipper.fwdMap (fun s : ℝ => W s.toNNReal ω) s z ^ 2) -
        (driftAt ρL ρR (W · ω) (fun i t => VL i t ω) (fun i t => VR i t ω) s : ℂ) /
          QuantumZipper.fwdMap (fun s : ℝ => W s.toNNReal ω) s z := by
    intro ω hPω hσζ hsol s hs
    have hs0 : 0 ≤ s := hs.1.le
    have hsT : s.toNNReal ≤ σ ω := Real.toNNReal_le_iff_le_coe.2 hs.2
    have hmem : ((coordProc κ z W VL VR B s.toNNReal ω, B s.toNNReal ω) : Coord nL nR × ℝ) ∈
        obsRegion κ := mem_obsRegion_coordAt (κ := κ) (b := fun t => B t ω) hPω hσζ hz hsol hsT
    have hcf : coordF κ ((coordProc κ z W VL VR B s.toNNReal ω, B s.toNNReal ω) :
        Coord nL nR × ℝ) = QuantumZipper.fwdMap (fun s : ℝ => W s.toNNReal ω) s z := by
      simp only [coordProc]; rw [coordF_coordAt, Real.coe_toNNReal _ hs0]; rfl
    have hne : coordF κ ((coordProc κ z W VL VR B s.toNNReal ω, B s.toNNReal ω) :
        Coord nL nR × ℝ) ≠ 0 := coordF_ne_zero hmem
    rw [hcf] at hne ⊢
    have hμ : ((∑ i, ρL i / -(VL i s.toNNReal ω - W s.toNNReal ω) +
        ∑ i, ρR i / -(VR i s.toNNReal ω - W s.toNNReal ω) : ℝ) : ℂ) =
        (driftAt ρL ρR (W · ω) (fun i t => VL i t ω) (fun i t => VR i t ω) s : ℂ) := by
      simp only [neg_sub, driftAt]
    simp only [densityAt, coordDensity, hμ]
    exact logDrift_eq hκ.le hne _
  refine ⟨?_, ?_⟩
  · obtain ⟨M, hM, hae⟩ := exists_martingale_coordObs hE hz hσ hδ hσp
      (Φ := logNormF κ) fun p hp => (contDiffAt_logNormF κ hp).contDiffWithinAt
    refine ⟨M, hM, ?_⟩
    filter_upwards [hae, hE.2.2.2.2, hσp] with ω hMω hPω hσω t
    obtain ⟨hσζ, hsol, -⟩ := hσω
    rw [hMω t]
    congr 1
    · simp only [logNormF, coordProc, coordF_coordAt]; rfl
    · refine integral_congr_of_ae_Ioc (T := σ ω) (min t (σ ω)).coe_nonneg
        (by exact_mod_cast min_le_right t (σ ω)) (Eventually.of_forall fun s hs => ?_)
      have hmem : ((coordProc κ z W VL VR B s.toNNReal ω, B s.toNNReal ω) : Coord nL nR × ℝ) ∈
          obsRegion κ := mem_obsRegion_coordAt (κ := κ) (b := fun t => B t ω) hPω hσζ hz hsol
        (Real.toNNReal_le_iff_le_coe.2 hs.2)
      rw [itoGen_logNormF κ hmem, ← hgen ω hPω hσζ hsol s hs]
      simp
  · obtain ⟨M, hM, hae⟩ := exists_martingale_coordObs hE hz hσ hδ hσp
      (Φ := argF κ) fun p hp => (contDiffAt_argF κ hp).contDiffWithinAt
    refine ⟨M, hM, ?_⟩
    filter_upwards [hae, hE.2.2.2.2, hσp] with ω hMω hPω hσω t
    obtain ⟨hσζ, hsol, -⟩ := hσω
    rw [hMω t]
    congr 1
    · simp only [argF, coordProc, coordF_coordAt]; rfl
    · refine integral_congr_of_ae_Ioc (T := σ ω) (min t (σ ω)).coe_nonneg
        (by exact_mod_cast min_le_right t (σ ω)) (Eventually.of_forall fun s hs => ?_)
      have hmem : ((coordProc κ z W VL VR B s.toNNReal ω, B s.toNNReal ω) : Coord nL nR × ℝ) ∈
          obsRegion κ := mem_obsRegion_coordAt (κ := κ) (b := fun t => B t ω) hPω hσζ hz hsol
        (Real.toNNReal_le_iff_le_coe.2 hs.2)
      rw [itoGen_argF κ hmem, ← hgen ω hPω hσζ hsol s hs]
      simp

end Martingale

end Ito

end InteractingSLE
