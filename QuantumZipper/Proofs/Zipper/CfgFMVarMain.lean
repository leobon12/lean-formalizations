import QuantumZipper.Proofs.Zipper.CfgFMVarKolm

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# CFG-FM-VAR (3): the variance node from the time energy node

`CfgFM.cfgFMVar_of_energy`: `CfgFMVarStmt κ T hT` from the energy node `TEnergy` for the
drivers of good paths. Ingredients: the fibre identification `ae_fZE_eq` (for a good path the
continuous extension `ZE` equals the regularized values `evalReg (X ω) (ν4 W T q)` a.s.
(`RegUnif.ae_fibre4`), which equal `X ω (ψ_t)_* fc(c, r)` a.s. by
`FrostmanReg.ae_evalReg_eq_frostman`), the scale-1 stochastic Fubini `tRepr`, and the
Kolmogorov assembly of `CfgFMVarKolm.lean`. Sources as there; bookkeeping own.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter
open scoped Real ENNReal NNReal

namespace QuantumZipper.E6
namespace CfgFM

open D3Plus KolmD KolmG RegUnif RegCont CharFun RegSample Thm18Asm Thm18Asm.G1FM

/-- **Fibre identification.** For a good path, the continuous extension at `(t, d, r)` is a.s. the
field paired with the pushed circle `(ψ_t)_* fc(d, r)`. -/
theorem ae_fZE_eq {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {X : Ω → FieldSample} (hX : IsFreeGFFModConstH X P) {κ T : ℝ} (hT : 0 < T)
    {f : C(Icc (0 : ℝ) T, ℝ)} (hf : f ∈ GoodP hT.le (1 / 3)) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) T)
    {d : ℂ} {r : ℝ} (hr : 0 < r) (hrd : r < d.im) :
    (fun ω => fZE hT.le κ (f, X ω) t (d, r)) =ᵐ[P]
      fun ω => X ω ((foldedCircle d r).map fun z => ((1 : ℝ) : ℂ) * tpsi (Wof κ T hT.le f) t z) := by
  set W := Wof κ T hT.le f with hWdef
  have hWc : Continuous W := continuous_Wof κ T hT.le f
  have hW0 : W 0 = 0 := Wof_zero_of_GoodP hT.le κ hf
  have hp : (t, (d, r)) ∈ parSet T := ⟨ht, (show (0 : ℝ) ≤ d.im by linarith), hr⟩
  obtain ⟨M, hM⟩ := exists_abs_le_on_Icc hWc T
  obtain ⟨i1, f1, b1⟩ := νT_box_facts hWc hW0 hr hM ht (w := d) le_rfl le_rfl
  have h1 : ∀ᵐ x ∂νT W d r t, x ∈ Metric.closedBall (0 : ℂ)
      (revBound (2 * M) T (‖d‖ + r)) ∩ Hbar :=
    b1.mono fun z hz => ⟨mem_closedBall_zero_iff.2 hz.2, (show (0 : ℝ) < z.im from hz.1).le⟩
  have hmap : νT W d r t = (foldedCircle d r).map fun z => ((1 : ℝ) : ℂ) * tpsi W t z := by
    refine Measure.map_congr ?_
    filter_upwards [TwoPoint.foldedCircle_ae_mem_H d hr] with z hz
    rw [tpsi_eq hWc hW0 ht.1 hz, Complex.ofReal_one, one_mul]
  filter_upwards [ae_fibre4 hX hT κ (pr4 (t, (d, r))) f,
    FrostmanReg.ae_evalReg_eq_frostman hX (ae_iff.1 h1) f1 (by norm_num)] with ω h1 h2
  rcases h1 with h | ⟨⟨hU, he⟩, -⟩
  · exact absurd hf h.1
  · show ZE hT.le κ (f, X ω) (pr4 (t, (d, r))) = _
    simp only [mem_ofPred_eq] at hU he
    simp only [ZE, hU, ↓reduceIte]
    rw [he, Gm_eq hT.le κ _ hW0 (X ω), ν4_pr4 W hp, ← hmap]
    exact h2

/-! ## The time block -/

/-- The parameter block `w ∈ fmBox m`, `τ ∈ (2^{-(n+1)}, 2^{-n}]`, `s ∈ (0, τ)`, `t ∈ [0,T]`. -/
def tBlockSet (T : ℝ) (m n : ℕ) : Set (ℂ × ℝ × ℝ × ℝ) :=
  {p | p.1 ∈ fmBox m ∧ p.2.1 ∈ Ioc ((2 : ℝ)⁻¹ ^ (n + 1)) ((2 : ℝ)⁻¹ ^ n) ∧
    p.2.2.1 ∈ Ioo 0 p.2.1 ∧ p.2.2.2 ∈ Icc 0 T}

theorem continuous_tInt_block {G : ℝ × ℂ × ℝ → ℝ} (hG : ContinuousOn G (univ ×ˢ univ ×ˢ Ioi 0))
    {T : ℝ} {m n : ℕ} :
    Continuous fun p : tBlockSet T m n =>
      fmInt (fun x => G (p.1.2.2.2, x.1, x.2)) p.1.1 p.1.2.1 p.1.2.2.1 := by
  unfold fmInt
  refine intervalIntegral.continuous_parametric_intervalIntegral_of_continuous' ?_ _ _
  have hmap : Continuous fun x : tBlockSet T m n × ℝ =>
      (x.1.1.2.2.2, (x.1.1.1 + (x.1.1.2.1 : ℂ) * Complex.exp ((x.2 : ℂ) * Complex.I)),
        x.1.1.2.2.1) := by
    fun_prop
  have hmem : ∀ x : tBlockSet T m n × ℝ,
      (x.1.1.2.2.2, (x.1.1.1 + (x.1.1.2.1 : ℂ) * Complex.exp ((x.2 : ℂ) * Complex.I)),
        x.1.1.2.2.1) ∈ univ ×ˢ univ ×ˢ Ioi (0 : ℝ) := by
    rintro ⟨⟨⟨w, τ, s, t⟩, hw, hτ, hs, ht⟩, θ⟩
    exact ⟨mem_univ _, mem_univ _, hs.1⟩
  have hc := hG.comp_continuous hmap hmem
  exact (Complex.continuous_ofReal.comp hc).mul (by fun_prop)

theorem t_block_eq_of_dense {G : ℝ × ℂ × ℝ → ℝ} (hG : ContinuousOn G (univ ×ˢ univ ×ˢ Ioi 0))
    {T : ℝ} {m n : ℕ} (k : Fin 2) {v : (Fin 5 → ℝ) → ℝ} (hv : Continuous v)
    {D : Set (tBlockSet T m n)} (hD : Dense D)
    (hDeq : ∀ p ∈ D, fmPart k (fmInt (fun x => G (p.1.2.2.2, x.1, x.2)) p.1.1 p.1.2.1 p.1.2.2.1) =
      v (fmParamH n p.1.1 p.1.2.1 p.1.2.2.1 p.1.2.2.2)) :
    ∀ w ∈ fmBox m, ∀ τ ∈ Ioc ((2 : ℝ)⁻¹ ^ (n + 1)) ((2 : ℝ)⁻¹ ^ n), ∀ s ∈ Ioo 0 τ,
      ∀ t ∈ Icc (0 : ℝ) T,
        fmPart k (fmInt (fun x => G (t, x.1, x.2)) w τ s) = v (fmParamH n w τ s t) := by
  have hF : Continuous fun p : tBlockSet T m n =>
      fmPart k (fmInt (fun x => G (p.1.2.2.2, x.1, x.2)) p.1.1 p.1.2.1 p.1.2.2.1) :=
    (continuous_fmPart k).comp (continuous_tInt_block hG)
  have hH : Continuous fun p : tBlockSet T m n =>
      v (fmParamH n p.1.1 p.1.2.1 p.1.2.2.1 p.1.2.2.2) := by
    refine hv.comp ?_
    unfold fmParamH
    refine continuous_pi fun i => ?_
    fin_cases i <;> simp <;> fun_prop
  have heq := Continuous.ext_on hD hF hH hDeq
  intro w hw τ hτ s hs t ht
  exact congrFun heq ⟨(w, τ, s, t), hw, hτ, hs, ht⟩

/-! ## The assembly -/

/-- **CFG-FM-VAR from the time energy node.** -/
theorem cfgFMVar_of_energy (κ T : ℝ) (hT : 0 < T)
    (hE : ∀ f ∈ GoodP hT.le (1 / 3), TEnergy (Wof κ T hT.le f) T) : CfgFMVarStmt κ T hT := by
  intro Ω _ P _ X hX f hf m
  set W := Wof κ T hT.le f with hWdef
  have hWc : Continuous W := continuous_Wof κ T hT.le f
  have hW0 : W 0 = 0 := Wof_zero_of_GoodP hT.le κ hf
  obtain ⟨c, hc, τ₀, hτ₀, hEm⟩ := t_energy hWc hW0 hT.le (hE f hf) m
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
  set Z : (Fin 5 → ℝ) → Ω → ℝ := fun q ω => X ω (tPos W T m n k q) - X ω (tNeg W T m n k q)
    with hZ
  have hZm : ∀ q, Measurable (Z q) := fun q =>
    (hX.measurable_coord _).sub (hX.measurable_coord _)
  have hlaw : ∀ q q', ∃ v : ℝ≥0, P.map (fun ω => Z q ω - Z q' ω) = gaussianReal 0 v ∧
      (v : ℝ) ≤ 10 * c * ‖q - q'‖ ^ ((1 : ℝ) / 3) := fun q q' =>
    ⟨_, t_map_incr hX hWc hW0 hT.le hnm k q q', by
      rw [Real.coe_toNNReal']
      exact max_le (hEm n hnτ hnm k q q').2 (by positivity)⟩
  have hmom : ∀ R : ℕ, ∃ K, 0 ≤ K ∧ MomentBoundG Z P 60 10 K R := fun R =>
    ⟨(10 * c) ^ 30 * gaussianAbsMoment 60,
      mul_nonneg (by positivity) (gaussianAbsMoment_nonneg 60),
      fmH_momentBound_of_var hZm fun q _ q' _ => hlaw q q'⟩
  obtain ⟨Y, hYc, hYZ, -⟩ := KolmN.exists_continuous_modification_N (d := 5) (Z := Z) (P := P)
    (fun q => (hZm q).aemeasurable) (p := 60) (by norm_num) (a := 10) (by norm_num) hmom
  obtain ⟨Y', hY'c, hY'm, hY'Y⟩ := exists_measurable_modificationN hYc hZm hYZ
  have hY'Z : ∀ q, Y' q =ᵐ[P] Z q := fun q => by
    filter_upwards [hY'Y, hYZ q] with ω h1 h2
    rw [h1 q]; exact h2
  have hGc : ∀ ω, ContinuousOn (fun p : ℝ × ℂ × ℝ => fZE hT.le κ (f, X ω) p.1 (p.2.1, p.2.2))
      (univ ×ˢ univ ×ˢ Ioi 0) := fun ω =>
    (continuous_ZE hT.le κ _).comp_continuousOn (continuousOn_pr.comp
      (by fun_prop : Continuous fun p : ℝ × ℂ × ℝ => ((p.2.1, p.2.2), p.1)).continuousOn
      fun p hp => hp.2.2)
  refine ⟨Y', hY'c, hY'm, fun q _ q' _ => ?_, fun q _ => ?_, ?_⟩
  · obtain ⟨v, hv, hvb⟩ := hlaw q q'
    refine ⟨v, ?_, hvb⟩
    rw [← hv]
    exact Measure.map_congr ((hY'Z q).sub (hY'Z q'))
  · refine ⟨_, (Measure.map_congr (hY'Z q)).trans (t_map_pt hX hWc hW0 hT.le hnm k q), ?_⟩
    rw [Real.coe_toNNReal']
    exact max_le ((hEm n hnτ hnm k q q).1.trans (by linarith)) (by positivity)
  · obtain ⟨D, hDc, hDd⟩ := TopologicalSpace.exists_countable_dense (tBlockSet T m n)
    have hall : ∀ᵐ ω ∂P, ∀ p ∈ D,
        fmPart k (fmInt (fun x => fZE hT.le κ (f, X ω) p.1.2.2.2 (x.1, x.2)) p.1.1 p.1.2.1
          p.1.2.2.1) = Y' (fmParamH n p.1.1 p.1.2.1 p.1.2.2.1 p.1.2.2.2) ω := by
      refine (eventually_countable_ball hDc).2 fun p _ => ?_
      obtain ⟨⟨w, τ, s, t⟩, hw, hτ, hs, ht⟩ := p
      have hτ0 : 0 < τ := lt_trans (by positivity) hτ.1
      have hτs : τ + s < w.im := by linarith [hτ.2, hw.2, hs.2]
      have hVc : ∀ ω, ContinuousOn (fun p : ℂ × ℝ => fZE hT.le κ (f, X ω) t p)
          (univ ×ˢ Ioi 0) := fun ω =>
        (hGc ω).comp (Continuous.continuousOn (by fun_prop : Continuous fun p : ℂ × ℝ =>
          (t, p.1, p.2))) fun p hp => ⟨mem_univ _, mem_univ _, hp.2⟩
      filter_upwards [tRepr (tpsi_psiGood hWc hW0 ht.1) hX hVc
        (fun d r hr hrd => ae_fZE_eq hX hT hf ht hr hrd) k hτ0 hs.1 hτs,
        hY'Z (fmParamH n w τ s t)] with ω h1 h2
      show fmPart k (fmInt (fun x => fZE hT.le κ (f, X ω) t (x.1, x.2)) w τ s) =
        Y' (fmParamH n w τ s t) ω
      refine h1.trans (Eq.trans ?_ h2.symm)
      simp only [hZ, tPos, tNeg, fmPr_fmParamH, fmCq_fmParam hw, fmRq_fmParam hτ,
        fmSq_fmParam hτ hs, fmTt_fmParamH ht]
    filter_upwards [hall] with ω hω
    exact t_block_eq_of_dense (hGc ω) k (hY'c ω) hDd hω

end CfgFM
end QuantumZipper.E6
