import QuantumZipper.Proofs.Thm18.G1FMVarClamp

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# G1-FM-KOLM5 (2): Kolmogorov assembly in five parameters

Task G1-FM-KOLM5. `g1FMPushVar_of_nodes : G1FMReprStmt → G1FMAdmStmt → G1FMEnergyStmt →
G1FMPushVarStmt`, the 5-parameter copy of `D3Plus.n2ZFirstModeVar_of_nodes`
(`D3PlusN2FMVarKolm.lean`).

For fixed `ψ`, `m`, `n ≥ n₀`, `k`, put `Z q = X(pfmPos q) − X(pfmNeg q)` (clamped rescaled pushed
first-mode pairs, `q ∈ ℝ⁵`). By linearity `Z q − Z q'` is a.s. a pair of admissible measures of
equal mass, a centred Gaussian of variance its Neumann energy (`RegCont.map_diff_eq_gaussianReal`),
bounded by `10 c ‖q − q'‖` by the energy node and the Lipschitz clamp (`fmParams5_lip`). The
Kolmogorov criterion in `d = 5` parameters (`KolmN.exists_continuous_modification_N`, `p = 16`,
`a = 8 > 5`) gives a continuous modification, made measurable by
`exists_measurable_modificationN`. On a countable dense subset of the 5D block the first mode
equals `Z ∘ fmParam5` a.s. (`G1FMReprStmt`; the clamp inverts `fmParam5` there), and both sides are
continuous on the block (`V` is continuous on `ℂ × (0,∞) × (0,∞)`), so they agree on the block a.s.

Sources: Duplantier–Sheffield, *Liouville quantum gravity and KPZ*, Invent. Math. 185 (2011),
Prop. 3.1 (continuous modification of circle averages); Revuz–Yor, *Continuous Martingales and
Brownian Motion*, 3rd ed., Ch. I, Thm (2.1) (Kolmogorov–Čentsov); Hu–Miller–Peres, *Thick points
of the Gaussian free field*, Ann. Probab. 38 (2010), Prop. 2.1 (pattern). Bookkeeping own.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter
open scoped Real ENNReal NNReal

namespace QuantumZipper
namespace Thm18Asm
namespace G1FM

open D3Plus KolmD KolmG

/-! ## The 5D block and continuity of the first mode on it -/

/-- The parameter block `w ∈ fmBox m`, `τ ∈ (2^{-(n+1)}, 2^{-n}]`, `s ∈ (0, τ)`,
`S ∈ [1/(m+1), m+1]`. -/
def fm5BlockSet (m n : ℕ) : Set (ℂ × ℝ × ℝ × ℝ) :=
  {p | p.1 ∈ fmBox m ∧ p.2.1 ∈ Ioc ((2 : ℝ)⁻¹ ^ (n + 1)) ((2 : ℝ)⁻¹ ^ n) ∧
    p.2.2.1 ∈ Ioo 0 p.2.1 ∧ p.2.2.2 ∈ Icc (1 / ((m : ℝ) + 1)) ((m : ℝ) + 1)}

theorem continuous_fm5Int_block {V : ℂ × ℝ × ℝ → ℝ}
    (hV : ContinuousOn V (univ ×ˢ Ioi 0 ×ˢ Ioi 0)) {m n : ℕ} :
    Continuous fun p : fm5BlockSet m n =>
      fmInt (fun x => V (x.1, x.2, p.1.2.2.2)) p.1.1 p.1.2.1 p.1.2.2.1 := by
  unfold fmInt
  refine intervalIntegral.continuous_parametric_intervalIntegral_of_continuous' ?_ _ _
  have hmap : Continuous fun x : fm5BlockSet m n × ℝ =>
      ((x.1.1.1 + (x.1.1.2.1 : ℂ) * Complex.exp ((x.2 : ℂ) * Complex.I)), x.1.1.2.2.1,
        x.1.1.2.2.2) := by
    fun_prop
  have hmem : ∀ x : fm5BlockSet m n × ℝ,
      ((x.1.1.1 + (x.1.1.2.1 : ℂ) * Complex.exp ((x.2 : ℂ) * Complex.I)), x.1.1.2.2.1,
        x.1.1.2.2.2) ∈ univ ×ˢ Ioi (0 : ℝ) ×ˢ Ioi (0 : ℝ) := by
    rintro ⟨⟨⟨w, τ, s, S⟩, hw, hτ, hs, hS⟩, θ⟩
    exact ⟨mem_univ _, hs.1, lt_of_lt_of_le (by positivity) hS.1⟩
  have hc := hV.comp_continuous hmap hmem
  exact (Complex.continuous_ofReal.comp hc).mul (by fun_prop)

/-- Two continuous functions of the 5D block that agree on a dense subset agree everywhere. -/
theorem fm5_block_eq_of_dense {V : ℂ × ℝ × ℝ → ℝ}
    (hV : ContinuousOn V (univ ×ˢ Ioi 0 ×ˢ Ioi 0)) {m n : ℕ} (k : Fin 2)
    {v : (Fin 5 → ℝ) → ℝ} (hv : Continuous v) {D : Set (fm5BlockSet m n)} (hD : Dense D)
    (hDeq : ∀ p ∈ D, fmPart k (fmInt (fun x => V (x.1, x.2, p.1.2.2.2)) p.1.1 p.1.2.1 p.1.2.2.1) =
      v (fmParam5 n p.1.1 p.1.2.1 p.1.2.2.1 p.1.2.2.2)) :
    ∀ w ∈ fmBox m, ∀ τ ∈ Ioc ((2 : ℝ)⁻¹ ^ (n + 1)) ((2 : ℝ)⁻¹ ^ n), ∀ s ∈ Ioo 0 τ,
      ∀ S ∈ Icc (1 / ((m : ℝ) + 1)) ((m : ℝ) + 1),
        fmPart k (fmInt (fun x => V (x.1, x.2, S)) w τ s) = v (fmParam5 n w τ s S) := by
  have hF : Continuous fun p : fm5BlockSet m n =>
      fmPart k (fmInt (fun x => V (x.1, x.2, p.1.2.2.2)) p.1.1 p.1.2.1 p.1.2.2.1) :=
    (continuous_fmPart k).comp (continuous_fm5Int_block hV)
  have hH : Continuous fun p : fm5BlockSet m n =>
      v (fmParam5 n p.1.1 p.1.2.1 p.1.2.2.1 p.1.2.2.2) := by
    refine hv.comp ?_
    unfold fmParam5
    refine continuous_pi fun i => ?_
    fin_cases i <;> simp <;> fun_prop
  have heq := Continuous.ext_on hD hF hH hDeq
  intro w hw τ hτ s hs S hS
  exact congrFun heq ⟨(w, τ, s, S), hw, hτ, hs, hS⟩

/-! ## Laws of the pairs -/

section Laws

variable {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} {X : Ω → FieldSample}
  {ψ : ℂ → ℂ}

theorem pfmPos_adm (hA : G1FMAdmStmt) (hψ : G1RC.PsiGood ψ) {m n : ℕ}
    (hnm : 2 * (2 : ℝ)⁻¹ ^ n < 1 / ((m : ℝ) + 1)) (k : Fin 2) (q : Fin 5 → ℝ) :
    IsAdmissibleH (pfmPos ψ m n k q) ∧ IsAdmissibleH (pfmNeg ψ m n k q) := by
  have h1 : ‖(fmRq n (fmPr q) : ℂ) * fmDir k‖ + fmSq n (fmPr q) < (fmCq m n (fmPr q)).im := by
    rw [norm_fmRq_dir]
    have := fmRq_le n (fmPr q); have := fmSq_le n (fmPr q); have := fmCq_im_ge m n (fmPr q)
    linarith
  have hpos : 0 < ‖(fmRq n (fmPr q) : ℂ) * fmDir k‖ := by
    rw [norm_fmRq_dir]; exact fmRq_pos n _
  have hS := fmSSq_pos m n q
  refine ⟨hA ψ hψ _ _ _ _ (fmSq_nonneg n _) hpos h1 hS,
    hA ψ hψ _ _ _ _ (fmSq_nonneg n _) ?_ ?_ hS⟩
  · rwa [norm_neg]
  · rwa [norm_neg]

theorem pfm_map_pt (hX : IsFreeGFFModConstH X P) (hA : G1FMAdmStmt) (hψ : G1RC.PsiGood ψ)
    {m n : ℕ} (hnm : 2 * (2 : ℝ)⁻¹ ^ n < 1 / ((m : ℝ) + 1)) (k : Fin 2) (q : Fin 5 → ℝ) :
    P.map (fun ω => X ω (pfmPos ψ m n k q) - X ω (pfmNeg ψ m n k q)) =
      gaussianReal 0 (kernelCov2 neumannH (pfmPos ψ m n k q, pfmNeg ψ m n k q)
        (pfmPos ψ m n k q, pfmNeg ψ m n k q)).toNNReal := by
  obtain ⟨h1, h2⟩ := pfmPos_adm hA hψ hnm k q
  exact RegCont.map_diff_eq_gaussianReal hX h1 h2
    (by simp only [pfmPos, pfmNeg, pfmMeas_univ hψ.1])

theorem pfm_map_incr (hX : IsFreeGFFModConstH X P) (hA : G1FMAdmStmt) (hψ : G1RC.PsiGood ψ)
    {m n : ℕ} (hnm : 2 * (2 : ℝ)⁻¹ ^ n < 1 / ((m : ℝ) + 1)) (k : Fin 2) (q q' : Fin 5 → ℝ) :
    P.map (fun ω => (X ω (pfmPos ψ m n k q) - X ω (pfmNeg ψ m n k q)) -
        (X ω (pfmPos ψ m n k q') - X ω (pfmNeg ψ m n k q'))) =
      gaussianReal 0 (kernelCov2 neumannH
        (pfmPos ψ m n k q + pfmNeg ψ m n k q', pfmNeg ψ m n k q + pfmPos ψ m n k q')
        (pfmPos ψ m n k q + pfmNeg ψ m n k q', pfmNeg ψ m n k q + pfmPos ψ m n k q')).toNNReal := by
  obtain ⟨h1, h2⟩ := pfmPos_adm hA hψ hnm k q
  obtain ⟨h1', h2'⟩ := pfmPos_adm hA hψ hnm k q'
  have hl1 := hX.linear _ _ h1 h2' 1 1
  have hl2 := hX.linear _ _ h2 h1' 1 1
  simp only [one_smul, NNReal.coe_one, one_mul] at hl1 hl2
  have hae : (fun ω => (X ω (pfmPos ψ m n k q) - X ω (pfmNeg ψ m n k q)) -
        (X ω (pfmPos ψ m n k q') - X ω (pfmNeg ψ m n k q'))) =ᵐ[P]
      fun ω => X ω (pfmPos ψ m n k q + pfmNeg ψ m n k q') -
        X ω (pfmNeg ψ m n k q + pfmPos ψ m n k q') := by
    filter_upwards [hl1, hl2] with ω e1 e2
    rw [e1, e2]; ring
  rw [Measure.map_congr hae]
  refine RegCont.map_diff_eq_gaussianReal hX (isAdmissibleH_add h1 h2')
    (isAdmissibleH_add h2 h1') ?_
  simp only [Measure.add_apply, pfmPos, pfmNeg, pfmMeas_univ hψ.1]

end Laws

/-! ## The assembly -/

/-- Energy bounds at the clamped parameters. -/
theorem pfm_energy_q {ψ : ℂ → ℂ} {m : ℕ} {c τ₀ : ℝ} (hc : 0 ≤ c)
    (hEm : ∀ u : ℂ, ‖u‖ = 1 → ∀ w w' : ℂ, ‖w‖ ≤ 2 * ((m : ℝ) + 1) → ‖w'‖ ≤ 2 * ((m : ℝ) + 1) →
      1 / ((m : ℝ) + 1) ≤ w.im → 1 / ((m : ℝ) + 1) ≤ w'.im →
      ∀ τ τ' : ℝ, 0 < τ → τ ≤ τ₀ → τ ≤ 2 * τ' → τ' ≤ 2 * τ →
      ∀ s s' : ℝ, 0 ≤ s → s ≤ τ → 0 ≤ s' → s' ≤ τ' →
      ∀ S S' : ℝ, S ∈ Icc (1 / ((m : ℝ) + 1)) ((m : ℝ) + 1) →
        S' ∈ Icc (1 / ((m : ℝ) + 1)) ((m : ℝ) + 1) →
        kernelCov2 neumannH (pfmMeas ψ S w ((τ : ℂ) * u) s, pfmMeas ψ S w (-((τ : ℂ) * u)) s)
            (pfmMeas ψ S w ((τ : ℂ) * u) s, pfmMeas ψ S w (-((τ : ℂ) * u)) s) ≤ c ∧
        kernelCov2 neumannH
            (pfmMeas ψ S w ((τ : ℂ) * u) s + pfmMeas ψ S' w' (-((τ' : ℂ) * u)) s',
              pfmMeas ψ S w (-((τ : ℂ) * u)) s + pfmMeas ψ S' w' ((τ' : ℂ) * u) s')
            (pfmMeas ψ S w ((τ : ℂ) * u) s + pfmMeas ψ S' w' (-((τ' : ℂ) * u)) s',
              pfmMeas ψ S w (-((τ : ℂ) * u)) s + pfmMeas ψ S' w' ((τ' : ℂ) * u) s') ≤
          c * (‖w - w'‖ + |τ - τ'| + |s - s'| + |S - S'|) / τ)
    {n : ℕ} (hnτ : (2 : ℝ)⁻¹ ^ n ≤ τ₀) (k : Fin 2) (q q' : Fin 5 → ℝ) :
    kernelCov2 neumannH (pfmPos ψ m n k q, pfmNeg ψ m n k q)
        (pfmPos ψ m n k q, pfmNeg ψ m n k q) ≤ c ∧
    kernelCov2 neumannH
        (pfmPos ψ m n k q + pfmNeg ψ m n k q', pfmNeg ψ m n k q + pfmPos ψ m n k q')
        (pfmPos ψ m n k q + pfmNeg ψ m n k q', pfmNeg ψ m n k q + pfmPos ψ m n k q') ≤
      10 * c * ‖q - q'‖ := by
  have hτ := fmRq_pos n (fmPr q)
  have h := hEm (fmDir k) (norm_fmDir k) (fmCq m n (fmPr q)) (fmCq m n (fmPr q'))
    (norm_fmCq_le m n _) (norm_fmCq_le m n _) (fmCq_im_ge m n _) (fmCq_im_ge m n _)
    (fmRq n (fmPr q)) (fmRq n (fmPr q')) hτ ((fmRq_le n _).trans hnτ)
    (by linarith [fmRq_le n (fmPr q), fmRq_ge n (fmPr q')])
    (by linarith [fmRq_le n (fmPr q'), fmRq_ge n (fmPr q)]) (fmSq n (fmPr q)) (fmSq n (fmPr q'))
    (fmSq_nonneg n _) (fmSq_le n _) (fmSq_nonneg n _) (fmSq_le n _)
    (fmSSq m n q) (fmSSq m n q') (fmSSq_mem m n q) (fmSSq_mem m n q')
  refine ⟨h.1, h.2.trans ?_⟩
  rw [div_le_iff₀ hτ]
  have hl := fmParams5_lip m n q q'
  have hg := fmRq_ge n (fmPr q)
  have hD : 0 ≤ ‖q - q'‖ := norm_nonneg _
  have e1 := mul_le_mul_of_nonneg_left hl hc
  have e2 := mul_le_mul_of_nonneg_left hg (by positivity : (0 : ℝ) ≤ 10 * c * ‖q - q'‖)
  nlinarith

end G1FM

open D3Plus KolmD KolmG G1FM

/-- **G1-FM-PUSHVAR from the three nodes** (5-parameter Kolmogorov assembly). -/
theorem g1FMPushVar_of_nodes (hR : G1FMReprStmt) (hA : G1FMAdmStmt) (hE : G1FMEnergyStmt) :
    G1FMPushVarStmt := by
  intro ψ hψ Ω _ P _ X hX V hVc hVX m
  obtain ⟨c, hc, τ₀, hτ₀, hEm⟩ := hE ψ hψ m
  have hm1 : (0 : ℝ) < (m : ℝ) + 1 := by positivity
  set ε : ℝ := min τ₀ (1 / (4 * ((m : ℝ) + 1))) with hε
  have hε0 : 0 < ε := lt_min hτ₀ (by positivity)
  obtain ⟨n₀, hn₀⟩ := exists_pow_lt_of_lt_one hε0 (by norm_num : (2 : ℝ)⁻¹ < 1)
  refine ⟨10 * c, by positivity, n₀, fun n hn k => ?_⟩
  have hpow : (2 : ℝ)⁻¹ ^ n ≤ (2 : ℝ)⁻¹ ^ n₀ := pow_le_pow_of_le_one (by norm_num) (by norm_num) hn
  have hnτ : (2 : ℝ)⁻¹ ^ n ≤ τ₀ := by linarith [min_le_left τ₀ (1 / (4 * ((m : ℝ) + 1)))]
  have h4 : (2 : ℝ)⁻¹ ^ n < 1 / (4 * ((m : ℝ) + 1)) := by
    linarith [min_le_right τ₀ (1 / (4 * ((m : ℝ) + 1)))]
  have hq : 1 / (4 * ((m : ℝ) + 1)) = (1 / ((m : ℝ) + 1)) / 4 := by field_simp
  have hnm : 2 * (2 : ℝ)⁻¹ ^ n < 1 / ((m : ℝ) + 1) := by
    have := two_pow_inv_pos n
    have : (0 : ℝ) < 1 / ((m : ℝ) + 1) := by positivity
    linarith
  set Z : (Fin 5 → ℝ) → Ω → ℝ := fun q ω => X ω (pfmPos ψ m n k q) - X ω (pfmNeg ψ m n k q)
    with hZ
  have hZm : ∀ q, Measurable (Z q) := fun q =>
    (hX.measurable_coord _).sub (hX.measurable_coord _)
  have hlaw : ∀ q q', ∃ v : ℝ≥0, P.map (fun ω => Z q ω - Z q' ω) = gaussianReal 0 v ∧
      (v : ℝ) ≤ 10 * c * ‖q - q'‖ := fun q q' =>
    ⟨_, pfm_map_incr hX hA hψ hnm k q q', by
      rw [Real.coe_toNNReal']
      exact max_le (pfm_energy_q hc hEm hnτ k q q').2 (by positivity)⟩
  have hmom : ∀ R : ℕ, ∃ K, 0 ≤ K ∧ MomentBoundG Z P 16 8 K R := fun R =>
    ⟨(10 * c) ^ 8 * gaussianAbsMoment 16,
      mul_nonneg (by positivity) (gaussianAbsMoment_nonneg 16),
      fm5_momentBound_of_var hZm fun q _ q' _ => hlaw q q'⟩
  obtain ⟨Y, hYc, hYZ, -⟩ := KolmN.exists_continuous_modification_N (d := 5) (Z := Z) (P := P)
    (fun q => (hZm q).aemeasurable) (p := 16) (by norm_num) (a := 8) (by norm_num) hmom
  obtain ⟨W, hWc, hWm, hWY⟩ := exists_measurable_modificationN hYc hZm hYZ
  have hWZ : ∀ q, W q =ᵐ[P] Z q := fun q => by
    filter_upwards [hWY, hYZ q] with ω h1 h2
    rw [h1 q]; exact h2
  refine ⟨W, hWc, hWm, fun q _ q' _ => ?_, fun q _ => ?_, ?_⟩
  · obtain ⟨v, hv, hvb⟩ := hlaw q q'
    refine ⟨v, ?_, hvb⟩
    rw [← hv]
    exact Measure.map_congr ((hWZ q).sub (hWZ q'))
  · refine ⟨_, (Measure.map_congr (hWZ q)).trans (pfm_map_pt hX hA hψ hnm k q), ?_⟩
    rw [Real.coe_toNNReal']
    have h0 := norm_nonneg (q - q)
    exact max_le ((pfm_energy_q hc hEm hnτ k q q).1.trans (by linarith)) (by positivity)
  · obtain ⟨D, hDc, hDd⟩ := TopologicalSpace.exists_countable_dense (fm5BlockSet m n)
    have hall : ∀ᵐ ω ∂P, ∀ p ∈ D,
        fmPart k (fmInt (fun x => V (x.1, x.2, p.1.2.2.2) ω) p.1.1 p.1.2.1 p.1.2.2.1) =
          W (fmParam5 n p.1.1 p.1.2.1 p.1.2.2.1 p.1.2.2.2) ω := by
      refine (eventually_countable_ball hDc).2 fun p _ => ?_
      obtain ⟨⟨w, τ, s, S⟩, hw, hτ, hs, hS⟩ := p
      have hτ0 : 0 < τ := lt_trans (by positivity) hτ.1
      have hS0 : 0 < S := lt_of_lt_of_le (by positivity) hS.1
      have hτs : τ + s < w.im := by linarith [hτ.2, hw.2, hs.2]
      filter_upwards [hR ψ hψ P X hX V hVc hVX k w τ s S hτ0 hs.1 hτs hS0,
        hWZ (fmParam5 n w τ s S)] with ω h1 h2
      show fmPart k (fmInt (fun x => V (x.1, x.2, S) ω) w τ s) = W (fmParam5 n w τ s S) ω
      rw [h1, h2]
      simp only [hZ, pfmPos, pfmNeg, fmPr_fmParam5, fmCq_fmParam hw, fmRq_fmParam hτ,
        fmSq_fmParam hτ hs, fmSSq_fmParam5 hS]
    filter_upwards [hall] with ω hω
    exact fm5_block_eq_of_dense (hVc ω) k (hWc ω) hDd hω

end Thm18Asm
end QuantumZipper
