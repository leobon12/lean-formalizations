import QuantumZipper.Proofs.Zipper.D3PlusN2FMVarClamp

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# N2Z-FMVAR, part K (2): Kolmogorov assembly

Task N2Z-FMVAR. `n2ZFirstModeVar_of_nodes : FMReprStmt → FMAdmStmt → N2ZFMEnergyStmt →
N2ZFirstModeVarStmt`.

For fixed `m`, `n ≥ n₀`, `k`, put `Z q = X(fmPos q) − X(fmNeg q)` (clamped rescaled first-mode
pairs). By linearity `Z q − Z q'` is a.s. the pair `X(fmPos q + fmNeg q') − X(fmNeg q + fmPos q')`,
a centred Gaussian of variance its Neumann energy (`RegCont.map_diff_eq_gaussianReal`), which the
energy node bounds by `8 c ‖q − q'‖` (the clamp is Lipschitz, `fmParams_lip`). The dyadic
Kolmogorov criterion (`KolmG.exists_continuous_modification_G`, `d = 4`, `p = 16`, `a = 8`) gives
a continuous modification `V`, made measurable by `WedgeTK.exists_measurable_modification4`.
On a countable dense subset of the block the first mode equals `Z ∘ fmParam` a.s.
(`FMReprStmt`, clamp inverts `fmParam` there), and both sides are continuous on the block, so
they agree on the whole block a.s.

Sources: Duplantier–Sheffield, *Liouville quantum gravity and KPZ*, Invent. Math. 185 (2011),
Prop. 3.1 (continuous modification of circle averages); Revuz–Yor, *Continuous Martingales and
Brownian Motion*, 3rd ed., Ch. I, Thm (2.1) (Kolmogorov–Čentsov); Hu–Miller–Peres, *Thick points
of the Gaussian free field*, Ann. Probab. 38 (2010), Prop. 2.1 (pattern). Bookkeeping own.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter
open scoped Real ENNReal NNReal

namespace QuantumZipper
namespace D3Plus

open KolmD KolmG

/-! ## The block as a parameter set, and continuity of the first mode on it -/

/-- The parameter block `w ∈ fmBox m`, `τ ∈ (2^{-(n+1)}, 2^{-n}]`, `s ∈ (0, τ)`. -/
def fmBlockSet (m n : ℕ) : Set (ℂ × ℝ × ℝ) :=
  {p | p.1 ∈ fmBox m ∧ p.2.1 ∈ Ioc ((2 : ℝ)⁻¹ ^ (n + 1)) ((2 : ℝ)⁻¹ ^ n) ∧ p.2.2 ∈ Ioo 0 p.2.1}

theorem continuous_fmPart (k : Fin 2) : Continuous (fmPart k) := by
  show Continuous fun z : ℂ => if k = 0 then z.re else z.im
  split_ifs
  · exact Complex.continuous_re
  · exact Complex.continuous_im

theorem continuous_fmInt_block {g : ℂ × ℝ → ℝ} (hg : ContinuousOn g (Hbar ×ˢ Ioi 0)) {m n : ℕ}
    (hnm : (2 : ℝ)⁻¹ ^ n ≤ 1 / ((m : ℝ) + 1)) :
    Continuous fun p : fmBlockSet m n => fmInt g p.1.1 p.1.2.1 p.1.2.2 := by
  unfold fmInt
  refine intervalIntegral.continuous_parametric_intervalIntegral_of_continuous' ?_ _ _
  have hmap : Continuous fun x : fmBlockSet m n × ℝ =>
      ((x.1.1.1 + (x.1.1.2.1 : ℂ) * Complex.exp ((x.2 : ℂ) * Complex.I)), x.1.1.2.2) := by
    fun_prop
  have hmem : ∀ x : fmBlockSet m n × ℝ,
      ((x.1.1.1 + (x.1.1.2.1 : ℂ) * Complex.exp ((x.2 : ℂ) * Complex.I)), x.1.1.2.2) ∈
        Hbar ×ˢ Ioi (0 : ℝ) := by
    rintro ⟨⟨⟨w, τ, s⟩, hw, hτ, hs⟩, θ⟩
    refine ⟨?_, hs.1⟩
    show 0 ≤ (w + (τ : ℂ) * Complex.exp ((θ : ℂ) * Complex.I)).im
    have hτ0 : 0 < τ := lt_trans (by positivity) hτ.1
    have h1 : |((τ : ℂ) * Complex.exp ((θ : ℂ) * Complex.I)).im| ≤ τ := by
      refine (Complex.abs_im_le_norm _).trans (le_of_eq ?_)
      rw [norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one, Complex.norm_real,
        Real.norm_eq_abs, abs_of_pos hτ0]
    have h2 := (abs_le.1 h1).1
    rw [Complex.add_im]
    have := hw.2
    linarith [hτ.2]
  have hc := hg.comp_continuous hmap hmem
  exact (Complex.continuous_ofReal.comp hc).mul (by fun_prop)

/-- Two continuous functions of the block that agree on a dense subset agree everywhere. -/
theorem fm_block_eq_of_dense {g : ℂ × ℝ → ℝ} (hg : ContinuousOn g (Hbar ×ˢ Ioi 0)) {m n : ℕ}
    (hnm : (2 : ℝ)⁻¹ ^ n ≤ 1 / ((m : ℝ) + 1)) (k : Fin 2) {v : (Fin 4 → ℝ) → ℝ}
    (hv : Continuous v) {D : Set (fmBlockSet m n)} (hD : Dense D)
    (hDeq : ∀ p ∈ D, fmPart k (fmInt g p.1.1 p.1.2.1 p.1.2.2) = v (fmParam n p.1.1 p.1.2.1 p.1.2.2)) :
    ∀ w ∈ fmBox m, ∀ τ ∈ Ioc ((2 : ℝ)⁻¹ ^ (n + 1)) ((2 : ℝ)⁻¹ ^ n), ∀ s ∈ Ioo 0 τ,
      fmPart k (fmInt g w τ s) = v (fmParam n w τ s) := by
  have hF : Continuous fun p : fmBlockSet m n => fmPart k (fmInt g p.1.1 p.1.2.1 p.1.2.2) :=
    (continuous_fmPart k).comp (continuous_fmInt_block hg hnm)
  have hH : Continuous fun p : fmBlockSet m n => v (fmParam n p.1.1 p.1.2.1 p.1.2.2) := by
    refine hv.comp ?_
    unfold fmParam
    refine continuous_pi fun i => ?_
    fin_cases i <;> simp <;> fun_prop
  have heq := Continuous.ext_on hD hF hH hDeq
  intro w hw τ hτ s hs
  exact congrFun heq ⟨(w, τ, s), hw, hτ, hs⟩

/-! ## Laws of the pairs -/

section Laws

variable {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} {X : Ω → FieldSample}

theorem norm_fmRq_dir (n : ℕ) (q : Fin 4 → ℝ) (k : Fin 2) :
    ‖(fmRq n q : ℂ) * fmDir k‖ = fmRq n q := by
  rw [norm_mul, norm_fmDir, mul_one, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (fmRq_pos n q)]

theorem fmPos_adm (hA : FMAdmStmt) {m n : ℕ} (hnm : 2 * (2 : ℝ)⁻¹ ^ n < 1 / ((m : ℝ) + 1))
    (k : Fin 2) (q : Fin 4 → ℝ) : IsAdmissibleH (fmPos m n k q) ∧ IsAdmissibleH (fmNeg m n k q) := by
  have h1 : ‖(fmRq n q : ℂ) * fmDir k‖ + fmSq n q < (fmCq m n q).im := by
    rw [norm_fmRq_dir]
    have := fmRq_le n q; have := fmSq_le n q; have := fmCq_im_ge m n q
    linarith
  have hpos : 0 < ‖(fmRq n q : ℂ) * fmDir k‖ := by rw [norm_fmRq_dir]; exact fmRq_pos n q
  refine ⟨hA _ _ _ (fmSq_nonneg n q) hpos h1, hA _ _ _ (fmSq_nonneg n q) ?_ ?_⟩
  · rwa [norm_neg]
  · rwa [norm_neg]

theorem fm_map_pt (hX : IsFreeGFFModConstH X P) (hA : FMAdmStmt) {m n : ℕ}
    (hnm : 2 * (2 : ℝ)⁻¹ ^ n < 1 / ((m : ℝ) + 1)) (k : Fin 2) (q : Fin 4 → ℝ) :
    P.map (fun ω => X ω (fmPos m n k q) - X ω (fmNeg m n k q)) =
      gaussianReal 0 (kernelCov2 neumannH (fmPos m n k q, fmNeg m n k q)
        (fmPos m n k q, fmNeg m n k q)).toNNReal := by
  obtain ⟨h1, h2⟩ := fmPos_adm hA hnm k q
  exact RegCont.map_diff_eq_gaussianReal hX h1 h2 (by simp only [fmPos, fmNeg, fmMeas_univ])

theorem fm_map_incr (hX : IsFreeGFFModConstH X P) (hA : FMAdmStmt) {m n : ℕ}
    (hnm : 2 * (2 : ℝ)⁻¹ ^ n < 1 / ((m : ℝ) + 1)) (k : Fin 2) (q q' : Fin 4 → ℝ) :
    P.map (fun ω => (X ω (fmPos m n k q) - X ω (fmNeg m n k q)) -
        (X ω (fmPos m n k q') - X ω (fmNeg m n k q'))) =
      gaussianReal 0 (kernelCov2 neumannH
        (fmPos m n k q + fmNeg m n k q', fmNeg m n k q + fmPos m n k q')
        (fmPos m n k q + fmNeg m n k q', fmNeg m n k q + fmPos m n k q')).toNNReal := by
  obtain ⟨h1, h2⟩ := fmPos_adm hA hnm k q
  obtain ⟨h1', h2'⟩ := fmPos_adm hA hnm k q'
  have hl1 := hX.linear _ _ h1 h2' 1 1
  have hl2 := hX.linear _ _ h2 h1' 1 1
  simp only [one_smul, NNReal.coe_one, one_mul] at hl1 hl2
  have hae : (fun ω => (X ω (fmPos m n k q) - X ω (fmNeg m n k q)) -
        (X ω (fmPos m n k q') - X ω (fmNeg m n k q'))) =ᵐ[P]
      fun ω => X ω (fmPos m n k q + fmNeg m n k q') - X ω (fmNeg m n k q + fmPos m n k q') := by
    filter_upwards [hl1, hl2] with ω e1 e2
    rw [e1, e2]; ring
  rw [Measure.map_congr hae]
  refine RegCont.map_diff_eq_gaussianReal hX (isAdmissibleH_add h1 h2')
    (isAdmissibleH_add h2 h1') ?_
  simp only [Measure.add_apply, fmPos, fmNeg, fmMeas_univ]

end Laws

/-! ## The assembly -/

theorem fm_rho_lt : 16 * ((1 / 2 : ℝ) ^ (8 : ℝ) / (7 / 8 : ℝ) ^ 16) < 1 := by
  rw [show (8 : ℝ) = ((8 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]; norm_num

/-- Energy bounds at the clamped parameters. -/
theorem fm_energy_q {m : ℕ} {c τ₀ : ℝ} (hc : 0 ≤ c)
    (hEm : ∀ u : ℂ, ‖u‖ = 1 → ∀ w w' : ℂ, ‖w‖ ≤ 2 * ((m : ℝ) + 1) → ‖w'‖ ≤ 2 * ((m : ℝ) + 1) →
      1 / ((m : ℝ) + 1) ≤ w.im → 1 / ((m : ℝ) + 1) ≤ w'.im →
      ∀ τ τ' : ℝ, 0 < τ → τ ≤ τ₀ → τ ≤ 2 * τ' → τ' ≤ 2 * τ →
      ∀ s s' : ℝ, 0 ≤ s → s ≤ τ → 0 ≤ s' → s' ≤ τ' →
        kernelCov2 neumannH (fmMeas w ((τ : ℂ) * u) s, fmMeas w (-((τ : ℂ) * u)) s)
            (fmMeas w ((τ : ℂ) * u) s, fmMeas w (-((τ : ℂ) * u)) s) ≤ c ∧
        kernelCov2 neumannH
            (fmMeas w ((τ : ℂ) * u) s + fmMeas w' (-((τ' : ℂ) * u)) s',
              fmMeas w (-((τ : ℂ) * u)) s + fmMeas w' ((τ' : ℂ) * u) s')
            (fmMeas w ((τ : ℂ) * u) s + fmMeas w' (-((τ' : ℂ) * u)) s',
              fmMeas w (-((τ : ℂ) * u)) s + fmMeas w' ((τ' : ℂ) * u) s') ≤
          c * (‖w - w'‖ + |τ - τ'| + |s - s'|) / τ)
    {n : ℕ} (hnτ : (2 : ℝ)⁻¹ ^ n ≤ τ₀) (k : Fin 2) (q q' : Fin 4 → ℝ) :
    kernelCov2 neumannH (fmPos m n k q, fmNeg m n k q) (fmPos m n k q, fmNeg m n k q) ≤ c ∧
    kernelCov2 neumannH
        (fmPos m n k q + fmNeg m n k q', fmNeg m n k q + fmPos m n k q')
        (fmPos m n k q + fmNeg m n k q', fmNeg m n k q + fmPos m n k q') ≤
      8 * c * ‖q - q'‖ := by
  have hτ := fmRq_pos n q
  have h := hEm (fmDir k) (norm_fmDir k) (fmCq m n q) (fmCq m n q') (norm_fmCq_le m n q)
    (norm_fmCq_le m n q') (fmCq_im_ge m n q) (fmCq_im_ge m n q') (fmRq n q) (fmRq n q') hτ
    ((fmRq_le n q).trans hnτ) (by linarith [fmRq_le n q, fmRq_ge n q'])
    (by linarith [fmRq_le n q', fmRq_ge n q]) (fmSq n q) (fmSq n q') (fmSq_nonneg n q)
    (fmSq_le n q) (fmSq_nonneg n q') (fmSq_le n q')
  refine ⟨h.1, h.2.trans ?_⟩
  rw [div_le_iff₀ hτ]
  have hl := fmParams_lip m n q q'
  have hg := fmRq_ge n q
  have hD : 0 ≤ ‖q - q'‖ := norm_nonneg _
  have e1 := mul_le_mul_of_nonneg_left hl hc
  have e2 := mul_le_mul_of_nonneg_left hg (by positivity : (0 : ℝ) ≤ 8 * c * ‖q - q'‖)
  nlinarith

/-- **Part K.** The representation, admissibility and energy nodes give the variance node. -/
theorem n2ZFirstModeVar_of_nodes (hR : FMReprStmt) (hA : FMAdmStmt) (hE : N2ZFMEnergyStmt) :
    N2ZFirstModeVarStmt := by
  intro Ω _ P _ X hX
  obtain ⟨G, hG⟩ := WedgeTK.exists_isRegVersion hX
  refine ⟨G, hG, fun m => ?_⟩
  obtain ⟨c, hc, τ₀, hτ₀, hEm⟩ := hE m
  have hm1 : (0 : ℝ) < (m : ℝ) + 1 := by positivity
  set ε : ℝ := min τ₀ (1 / (4 * ((m : ℝ) + 1))) with hε
  have hε0 : 0 < ε := lt_min hτ₀ (by positivity)
  obtain ⟨n₀, hn₀⟩ := exists_pow_lt_of_lt_one hε0 (by norm_num : (2 : ℝ)⁻¹ < 1)
  refine ⟨8 * c, by positivity, n₀, fun n hn k => ?_⟩
  have hpow : (2 : ℝ)⁻¹ ^ n ≤ (2 : ℝ)⁻¹ ^ n₀ := pow_le_pow_of_le_one (by norm_num) (by norm_num) hn
  have hnτ : (2 : ℝ)⁻¹ ^ n ≤ τ₀ := by linarith [min_le_left τ₀ (1 / (4 * ((m : ℝ) + 1)))]
  have h4 : (2 : ℝ)⁻¹ ^ n < 1 / (4 * ((m : ℝ) + 1)) := by
    linarith [min_le_right τ₀ (1 / (4 * ((m : ℝ) + 1)))]
  have hq : 1 / (4 * ((m : ℝ) + 1)) = (1 / ((m : ℝ) + 1)) / 4 := by field_simp
  have hnm : 2 * (2 : ℝ)⁻¹ ^ n < 1 / ((m : ℝ) + 1) := by
    have := two_pow_inv_pos n
    have : (0 : ℝ) < 1 / ((m : ℝ) + 1) := by positivity
    linarith
  have hnm' : (2 : ℝ)⁻¹ ^ n ≤ 1 / ((m : ℝ) + 1) := by linarith [two_pow_inv_pos n]
  set Z : (Fin 4 → ℝ) → Ω → ℝ := fun q ω => X ω (fmPos m n k q) - X ω (fmNeg m n k q) with hZ
  have hZm : ∀ q, Measurable (Z q) := fun q =>
    (hX.measurable_coord _).sub (hX.measurable_coord _)
  have hlaw : ∀ q q', ∃ v : ℝ≥0, P.map (fun ω => Z q ω - Z q' ω) = gaussianReal 0 v ∧
      (v : ℝ) ≤ 8 * c * ‖q - q'‖ := fun q q' =>
    ⟨_, fm_map_incr hX hA hnm k q q', by
      rw [Real.coe_toNNReal']
      exact max_le (fm_energy_q hc hEm hnτ k q q').2 (by positivity)⟩
  have hmom : ∀ R : ℕ, ∃ K, 0 ≤ K ∧ MomentBoundG Z P 16 8 K R := fun R =>
    ⟨(8 * c) ^ 8 * gaussianAbsMoment 16,
      mul_nonneg (by positivity) (gaussianAbsMoment_nonneg 16), fun q _ q' _ => by
      obtain ⟨v, hv, hvb⟩ := hlaw q q'
      rw [RegSample.lintegral_pow16_of_map_eq (U := fun ω => Z q ω - Z q' ω)
        ((hZm q).sub (hZm q')) hv]
      apply ENNReal.ofReal_le_ofReal
      have h8 := pow_le_pow_left₀ (NNReal.coe_nonneg _) hvb 8
      rw [show (8 : ℝ) = ((8 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
      calc (v : ℝ) ^ 8 * gaussianAbsMoment 16 ≤ (8 * c * ‖q - q'‖) ^ 8 * gaussianAbsMoment 16 :=
            mul_le_mul_of_nonneg_right h8 (gaussianAbsMoment_nonneg 16)
        _ = (8 * c) ^ 8 * gaussianAbsMoment 16 * ‖q - q'‖ ^ 8 := by ring⟩
  obtain ⟨Y, hYc, hYZ, -⟩ := exists_continuous_modification_G (d := 4) (Z := Z) (P := P) le_rfl
    (θ := 7 / 8) (by norm_num) (by norm_num) (fun q => (hZm q).aemeasurable) (p := 16) (a := 8)
    (by norm_num) fm_rho_lt hmom
  obtain ⟨V, hVc, hVm, hVY⟩ := WedgeTK.exists_measurable_modification4 hYc hZm hYZ
  have hVZ : ∀ q, V q =ᵐ[P] Z q := fun q => by
    filter_upwards [hVY, hYZ q] with ω h1 h2
    rw [h1 q]; exact h2
  refine ⟨V, hVc, hVm, fun q _ q' _ => ?_, fun q _ => ?_, ?_⟩
  · obtain ⟨v, hv, hvb⟩ := hlaw q q'
    refine ⟨v, ?_, hvb⟩
    rw [← hv]
    exact Measure.map_congr ((hVZ q).sub (hVZ q'))
  · refine ⟨_, (Measure.map_congr (hVZ q)).trans (fm_map_pt hX hA hnm k q), ?_⟩
    rw [Real.coe_toNNReal']
    exact max_le ((fm_energy_q hc hEm hnτ k q q).1.trans (by linarith)) (by positivity)
  · obtain ⟨D, hDc, hDd⟩ := TopologicalSpace.exists_countable_dense (fmBlockSet m n)
    have hall : ∀ᵐ ω ∂P, ∀ p ∈ D, fmPart k (fmInt (G ω) p.1.1 p.1.2.1 p.1.2.2) =
        V (fmParam n p.1.1 p.1.2.1 p.1.2.2) ω := by
      refine (eventually_countable_ball hDc).2 fun p _ => ?_
      obtain ⟨⟨w, τ, s⟩, hw, hτ, hs⟩ := p
      have hτ0 : 0 < τ := lt_trans (by positivity) hτ.1
      have hτw : τ ≤ w.im := by linarith [hτ.2, hw.2]
      filter_upwards [hR P X hX G hG k w τ s hτ0 hτw hs.1, hVZ (fmParam n w τ s)] with ω h1 h2
      show fmPart k (fmInt (G ω) w τ s) = V (fmParam n w τ s) ω
      rw [h1, h2]
      simp only [hZ, fmPos, fmNeg, fmCq_fmParam hw, fmRq_fmParam hτ, fmSq_fmParam hτ hs]
    filter_upwards [hall] with ω hω
    exact fm_block_eq_of_dense (hG.cont ω) hnm' k (hVc ω) hDd hω

end D3Plus
end QuantumZipper
