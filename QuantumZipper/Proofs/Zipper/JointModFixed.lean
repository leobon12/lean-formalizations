import QuantumZipper.Proofs.Zipper.JointModKolm

/-!
# JOINTMOD, step 2 (continued): the continuous modification for a fixed driver

Parameters `q ∈ ℝ⁴`: circle centre `cen q = q 0 + i|q 1|`, radius `rad q = 2^{q 2}`
(`RegSample.cen`, `RegSample.rad`), time `tP T q = max (min (q 3) T) 0`. The Gaussian family
`q ↦ X(ν4 W T q)`, `ν4 W T q = (fc(cen q, rad q)).map (fwdMapInv W (tP T q))`, has a continuous
modification (`exists_contMod_ν4`), by the moment bound `momentBound_ν4` (time modulus
`abs_kernelCov2_νT_time_unif`, space modulus `abs_kernelCov2_νT_space_unif`, Gaussian moments)
and `KolmG.exists_continuous_modification_G` with `d = 4`.

Sources: Duplantier–Sheffield, Invent. Math. 185 (2011), Prop. 3.1; Revuz–Yor, 3rd ed., Ch. I,
Thm (2.1). The two-step increment splitting follows `RegCont.momentBound_μq`.
-/

noncomputable section

open Complex Filter MeasureTheory ProbabilityTheory Set
open scoped Topology Real ENNReal NNReal

namespace QuantumZipper
namespace RegUnif

open TwoPoint RegCont KolmD KolmG RegSample

variable {W : ℝ → ℝ}

/-- The clamped time parameter. -/
def tP (T : ℝ) (q : Fin 4 → ℝ) : ℝ := max (min (q 3) T) 0

/-- The unzipped folded circle with parameter `q`. -/
abbrev ν4 (W : ℝ → ℝ) (T : ℝ) (q : Fin 4 → ℝ) : Measure ℂ := νT W (cen q) (rad q) (tP T q)

theorem tP_mem {T : ℝ} (hT : 0 ≤ T) (q : Fin 4 → ℝ) : tP T q ∈ Icc 0 T :=
  ⟨le_max_right _ _, max_le (min_le_right _ _) hT⟩

theorem abs_tP_sub_le (T : ℝ) (q q' : Fin 4 → ℝ) : |tP T q - tP T q'| ≤ ‖q - q'‖ :=
  (abs_clamp_sub_le _ _ _).trans (by simpa using norm_le_pi_norm (q - q') 3)

theorem box_circle {R : ℕ} {q : Fin 4 → ℝ} (hq : q ∈ boxD R) :
    Real.exp (-R) ≤ rad q ∧ ‖cen q‖ + rad q ≤ 2 * R + Real.exp R := by
  refine ⟨rad_ge hq, ?_⟩
  have h2 := Real.log_pos (by norm_num : (1 : ℝ) < 2)
  have h1 := log_two_le_one
  have hR0 : (0 : ℝ) ≤ R := Nat.cast_nonneg R
  have hr : rad q ≤ Real.exp R := by
    show Real.exp (Real.log 2 * q 2) ≤ Real.exp R
    refine Real.exp_le_exp.2 ?_
    have := abs_le.1 (hq 2)
    nlinarith [mul_le_mul_of_nonneg_left this.2 h2.le, mul_nonneg (sub_nonneg.2 h1) hR0]
  have hc : ‖cen q‖ ≤ 2 * R := by
    refine (Complex.norm_le_abs_re_add_abs_im _).trans ?_
    have e1 : (cen q).re = q 0 := rfl
    have e2 : (cen q).im = |q 1| := rfl
    rw [e1, e2, abs_abs]
    linarith [hq 0, hq 1]
  linarith

theorem admissible_ν4 (hW : Continuous W) (hW0 : W 0 = 0) {T : ℝ} (hT : 0 ≤ T)
    (q : Fin 4 → ℝ) : IsAdmissibleH (ν4 W T q) ∧ ν4 W T q univ = 1 := by
  obtain ⟨M, hM⟩ := exists_abs_le_on_Icc hW T
  obtain ⟨i1, f1, b1⟩ := νT_box_facts hW hW0 (rad_pos q) hM (tP_mem hT q) le_rfl le_rfl
  refine ⟨FrostmanReg.isAdmissibleH_of_frostman
    (R := revBound (2 * M) T (‖cen q‖ + rad q)) ?_ f1 (by norm_num), measure_univ⟩
  have h1 : ∀ᵐ x ∂ν4 W T q, x ∈ Metric.closedBall (0 : ℂ) (revBound (2 * M) T (‖cen q‖ + rad q))
      ∩ Hbar :=
    b1.mono fun z hz => ⟨mem_closedBall_zero_iff.2 hz.2, (show (0 : ℝ) < z.im from hz.1).le⟩
  exact ae_iff.1 h1

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {X : Ω → FieldSample}

/-- **Moment bound on boxes** `E|Z q − Z q'|^{2m} ≤ K ‖q − q'‖^{m a/12}`. -/
theorem momentBound_ν4 (hX : IsFreeGFFModConstH X P) (hW : Continuous W) (hW0 : W 0 = 0)
    {T : ℝ} (hT : 0 < T) {a CH : ℝ} (ha : 0 < a) (ha1 : a ≤ 1) (hCH : 0 ≤ CH)
    (hH : ∀ t ∈ Icc (0 : ℝ) T, ∀ t' ∈ Icc (0 : ℝ) T, |t - t'| ≤ 1 / 2 →
      |W t - W t'| ≤ CH * |t - t'| ^ a) (m R : ℕ) :
    ∃ K, 0 ≤ K ∧ MomentBoundG (fun q ω => X ω (ν4 W T q)) P (2 * m) ((m : ℝ) * (a / 12)) K R := by
  obtain ⟨M, hM⟩ := exists_abs_le_on_Icc hW T
  have hM0 : 0 ≤ M := (abs_nonneg _).trans (hM 0 ⟨le_rfl, hT.le⟩)
  set r₀ := Real.exp (-(R : ℝ)) with hr₀def
  have hr₀ : 0 < r₀ := Real.exp_pos _
  set Rb := 2 * (R : ℝ) + Real.exp R with hRb
  set L := Real.exp R + 3 with hL
  have hL0 : 0 ≤ L := by positivity
  set β := a / 12 with hβdef
  have hβ0 : 0 ≤ β := by positivity
  have hβ : β ≤ 1 / 12 := by rw [hβdef]; linarith
  set Kt := timeK M T r₀ Rb CH with hKt
  have hKt0 : 0 ≤ Kt := by
    have := timeConst_nonneg (R := Rb) hM0 hT.le hr₀
    have := potC_nonneg (R := Rb) hM0 hT.le hr₀
    rw [hKt]; unfold timeK; positivity
  have hSK : 0 ≤ spaceK M T r₀ Rb := by
    have := spaceConst_nonneg (R := Rb) hM0 hT.le hr₀
    have := potC_nonneg (R := Rb) hM0 hT.le hr₀
    unfold spaceK; positivity
  set Ks := spaceK M T r₀ Rb * L ^ β with hKs
  have hKs0 : 0 ≤ Ks := by positivity
  set c := gaussianAbsMoment (2 * m) with hc
  have hc0 : 0 ≤ c := gaussianAbsMoment_nonneg _
  refine ⟨2 ^ (2 * m - 1) * c * (Kt ^ m + Ks ^ m), by positivity, fun q hq q' hq' => ?_⟩
  show ∫⁻ ω, ENNReal.ofReal (|X ω (ν4 W T q) - X ω (ν4 W T q')| ^ (2 * m)) ∂P ≤ _
  set q'' : Fin 4 → ℝ := Function.update q 3 (q' 3) with hq''
  have e0 : q'' 0 = q 0 := Function.update_of_ne (by decide) _ _
  have e1 : q'' 1 = q 1 := Function.update_of_ne (by decide) _ _
  have e2 : q'' 2 = q 2 := Function.update_of_ne (by decide) _ _
  have e3 : q'' 3 = q' 3 := by simp [q'']
  have hcen : cen q'' = cen q := by unfold cen; rw [e0, e1]
  have hrad : rad q'' = rad q := by unfold rad; rw [e2]
  have htP : tP T q'' = tP T q' := by unfold tP; rw [e3]
  set Δ := ‖q - q'‖ with hΔ
  have hΔ0 : 0 ≤ Δ := norm_nonneg _
  obtain ⟨hr1, hR1⟩ := box_circle hq
  obtain ⟨hr2, hR2⟩ := box_circle hq'
  have v1 : |kernelCov2 neumannH (ν4 W T q, ν4 W T q'') (ν4 W T q, ν4 W T q'')| ≤
      Kt * Δ ^ β := by
    simp only [ν4, hcen, hrad, htP]
    refine (abs_kernelCov2_νT_time_unif hW hW0 hr₀ hM ha ha1 hCH hH hr1 hR1 (tP_mem hT.le q)
      (tP_mem hT.le q')).trans ?_
    exact mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow (abs_nonneg _) (abs_tP_sub_le T q q') hβ0) hKt0
  have v2 : |kernelCov2 neumannH (ν4 W T q'', ν4 W T q') (ν4 W T q'', ν4 W T q')| ≤
      Ks * Δ ^ β := by
    simp only [ν4, hcen, hrad, htP]
    refine (abs_kernelCov2_νT_space_unif hW hW0 hr₀ hM hβ0 hβ (tP_mem hT.le q') hr1 hr2 hR1
      hR2).trans ?_
    have hpl := param_lip hq hq'
    have hd : ‖cen q - cen q'‖ + |rad q - rad q'| ≤ L * Δ := by
      linarith [abs_nonneg (sm q - sm q')]
    have h3 := Real.rpow_le_rpow (by positivity) hd hβ0
    rw [Real.mul_rpow hL0 hΔ0] at h3
    calc spaceK M T r₀ Rb * (‖cen q - cen q'‖ + |rad q - rad q'|) ^ β
        ≤ spaceK M T r₀ Rb * (L ^ β * Δ ^ β) := mul_le_mul_of_nonneg_left h3 hSK
      _ = Ks * Δ ^ β := by rw [hKs]; ring
  obtain ⟨ad1, ms1⟩ := admissible_ν4 hW hW0 hT.le q
  obtain ⟨ad2, ms2⟩ := admissible_ν4 hW hW0 hT.le q''
  obtain ⟨ad3, ms3⟩ := admissible_ν4 hW hW0 hT.le q'
  have hm1 := lintegral_pow_diff_le hX ad1 ad2 (ms1.trans ms2.symm) m v1
  have hm2 := lintegral_pow_diff_le hX ad2 ad3 (ms2.trans ms3.symm) m v2
  set A := fun ω => X ω (ν4 W T q)
  set B := fun ω => X ω (ν4 W T q'')
  set Cc := fun ω => X ω (ν4 W T q')
  have hmeas : Measurable fun ω => ENNReal.ofReal (|A ω - B ω| ^ (2 * m)) :=
    ((continuous_abs.measurable.comp
      ((hX.measurable_coord _).sub (hX.measurable_coord _))).pow_const _).ennreal_ofReal
  have hpt : ∀ ω, ENNReal.ofReal (|A ω - Cc ω| ^ (2 * m)) ≤ ENNReal.ofReal (2 ^ (2 * m - 1)) *
      (ENNReal.ofReal (|A ω - B ω| ^ (2 * m)) + ENNReal.ofReal (|B ω - Cc ω| ^ (2 * m))) := by
    intro ω
    rw [← ENNReal.ofReal_add (by positivity) (by positivity), ← ENNReal.ofReal_mul (by positivity)]
    refine ENNReal.ofReal_le_ofReal ?_
    have := add_pow_abs_le (A ω - B ω) (B ω - Cc ω) (2 * m)
    rwa [show A ω - B ω + (B ω - Cc ω) = A ω - Cc ω by ring] at this
  have epow : ∀ K : ℝ, (K * Δ ^ β) ^ m = K ^ m * Δ ^ ((m : ℝ) * β) := fun K => by
    rw [mul_pow, ← Real.rpow_natCast (Δ ^ β), ← Real.rpow_mul hΔ0, mul_comm β]
  calc ∫⁻ ω, ENNReal.ofReal (|A ω - Cc ω| ^ (2 * m)) ∂P
      ≤ ∫⁻ ω, ENNReal.ofReal (2 ^ (2 * m - 1)) *
          (ENNReal.ofReal (|A ω - B ω| ^ (2 * m)) + ENNReal.ofReal (|B ω - Cc ω| ^ (2 * m))) ∂P :=
        lintegral_mono hpt
    _ = ENNReal.ofReal (2 ^ (2 * m - 1)) * ((∫⁻ ω, ENNReal.ofReal (|A ω - B ω| ^ (2 * m)) ∂P) +
          ∫⁻ ω, ENNReal.ofReal (|B ω - Cc ω| ^ (2 * m)) ∂P) := by
        rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, lintegral_add_left hmeas]
    _ ≤ ENNReal.ofReal (2 ^ (2 * m - 1)) * (ENNReal.ofReal ((Kt * Δ ^ β) ^ m * c) +
          ENNReal.ofReal ((Ks * Δ ^ β) ^ m * c)) := by gcongr
    _ = ENNReal.ofReal (2 ^ (2 * m - 1) * c * (Kt ^ m + Ks ^ m) * Δ ^ ((m : ℝ) * β)) := by
        have h1 : 0 ≤ (Kt * Δ ^ β) ^ m * c := by positivity
        have h2 : 0 ≤ (Ks * Δ ^ β) ^ m * c := by positivity
        rw [← ENNReal.ofReal_add h1 h2, ← ENNReal.ofReal_mul (by positivity), epow, epow]
        congr 1; ring

/-- **Continuous modification for a fixed driver** (four-parameter Kolmogorov step). -/
theorem exists_contMod_ν4 (hX : IsFreeGFFModConstH X P) [IsProbabilityMeasure P]
    (hW : Continuous W) (hW0 : W 0 = 0) {T : ℝ} (hT : 0 < T) {a CH : ℝ} (ha : 0 < a)
    (ha1 : a ≤ 1) (hCH : 0 ≤ CH)
    (hH : ∀ t ∈ Icc (0 : ℝ) T, ∀ t' ∈ Icc (0 : ℝ) T, |t - t'| ≤ 1 / 2 →
      |W t - W t'| ≤ CH * |t - t'| ^ a) :
    ∃ Y : (Fin 4 → ℝ) → Ω → ℝ, (∀ ω, Continuous fun q => Y q ω) ∧
      (∀ q, (fun ω => Y q ω) =ᵐ[P] fun ω => X ω (ν4 W T q)) ∧
      ∀ᵐ ω ∂P, ∀ q, Tendsto (fun n => X ω (ν4 W T (rndD n q))) atTop (𝓝 (Y q ω)) := by
  set β := a / 12 with hβ
  have hβ0 : 0 < β := by positivity
  obtain ⟨hθ0, hθ1, hρ⟩ := kolm_exponents' hβ0
  exact exists_continuous_modification_G (d := 4)
    (Z := fun q ω => X ω (ν4 W T q)) (P := P) le_rfl hθ0 hθ1
    (fun q => (hX.measurable_coord _).aemeasurable) (by positivity) hρ
    (fun R => momentBound_ν4 hX hW hW0 hT ha ha1 hCH hH _ R)

end RegUnif
end QuantumZipper
