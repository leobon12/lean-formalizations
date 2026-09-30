import QuantumZipper.Proofs.LQG.WedgeBdryInfABasic
import QuantumZipper.Proofs.LQG.WedgeBdryInfStmt

/-!
# WEDGE-BDRY 4 (a): weighted infinite boundary mass of the free field

`wedgeBdryFreeInfStmt_holds : WedgeBdryFreeInfStmt`: for the free field `X`, `γ ∈ (0,2)` and
`α'' < Q`, a.s. `∫_{[1,∞)} t^{−α''γ/2} dν_X = ∞`.

Sheffield (arXiv:1012.4797, §1.6, p. 21) asserts that a quantum wedge has infinite boundary
length; no proof is given there. The argument here is our own (handoff/WEDGE-BDRY.md
item 4 (a)), built on the exact dyadic scaling already used in `InfMass`
(`isVagueLimitR_rescale`, `map_normC_rescale`):

* windows `a_n = ∫_{(2^n,2^{n+1})} t^{−β} dν_X`, `β = α''γ/2 ≥ 0` (the case `α'' < 0` reduces to
  `α'' = 0` by monotonicity of the weight on `[1,∞)`);
* `a_n ≥ exp(S_n) M'_n`, where `M'_n = Ψ(normC(rescale X Q 2^n))` has the law of
  `M = e^{−γX(fc(0,1))/2} ν_X(1,2) > 0` and
  `S_n = γ/2 (X(fc(0,2^n)) − X(fc(0,1)) + (Q − α'') n log 2) + γ/2 X(fc(0,1)) − β log 2`;
* hence `P(a_n < 1) → 0` along a subsequence (Chebyshev, `tendsto_prob_drift`), and reverse
  Fatou for events (`ae_frequently_one_le_of_prob_small`) gives `a_n ≥ 1` infinitely often a.s.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped NNReal ENNReal

namespace QuantumZipper

namespace WedgeBdry

open InfMass Factorization LQGMeas

theorem preimage_mul_inv_Ioo_one_two (n : ℕ) :
    (fun s : ℝ => s * ((2 : ℝ) ^ n)⁻¹) ⁻¹' Ioo 1 2 = Ioo ((2 : ℝ) ^ n) (2 ^ (n + 1)) := by
  have hb : (0 : ℝ) < 2 ^ n := by positivity
  ext t
  simp only [mem_preimage, mem_Ioo]
  rw [lt_mul_inv_iff₀ hb, mul_inv_lt_iff₀ hb, one_mul, pow_succ, mul_comm (2 : ℝ) (2 ^ n)]

theorem window_weight_le {β : ℝ} (hβ : 0 ≤ β) (n : ℕ) {t : ℝ}
    (ht : t ∈ Ioo ((2 : ℝ) ^ n) (2 ^ (n + 1))) :
    Real.exp (-(((n : ℝ) + 1) * Real.log 2) * β) ≤ t ^ (-β) := by
  have h2 : (0 : ℝ) < 2 ^ (n + 1) := by positivity
  have ht0 : 0 < t := (pow_pos two_pos n).trans ht.1
  have e : Real.exp (-(((n : ℝ) + 1) * Real.log 2) * β) = ((2 : ℝ) ^ (n + 1)) ^ (-β) := by
    rw [Real.rpow_def_of_pos h2, Real.log_pow]
    congr 1
    push_cast
    ring
  rw [e, Real.rpow_neg h2.le, Real.rpow_neg ht0.le]
  exact inv_anti₀ (Real.rpow_pos_of_pos ht0 _) (Real.rpow_le_rpow ht0.le ht.2.le hβ)

section FreeField

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {X : Ω → FieldSample}

/-- The window bound `a_n ≥ exp(S_n) · M'_n` (deterministic on the regular event). -/
theorem ae_window_bound (hX : IsFreeGFFModConstH X P) {G : Ω → ℂ × ℝ → ℝ}
    (hG : WedgeTK.IsRegVersion X P G) {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) {β : ℝ}
    (hβ : 0 ≤ β) (n : ℕ) :
    ∀ᵐ ω ∂P, ENNReal.ofReal (Real.exp (-(((n : ℝ) + 1) * Real.log 2) * β + γ / 2 *
        (X ω (fc01.map fun u => (((2 : ℝ) ^ n : ℝ) : ℂ) * u) + Qc γ * (n * Real.log 2)))) *
        Psi γ (Ioo 1 2) (reconstruct (normC (rescale (X ω) (Qc γ) ((2 : ℝ) ^ n)))) ≤
      ∫⁻ t in Ioo ((2 : ℝ) ^ n) (2 ^ (n + 1)), ENNReal.ofReal (t ^ (-β))
        ∂qBoundaryMeasure γ (X ω) := by
  have hb0 : (0 : ℝ) < 2 ^ n := by positivity
  filter_upwards [hG.reg, BdryExist.ae_isVagueLimitR_qBoundaryMeasure hX hγ hγ2,
    ae_evalReg_map_fc hG hb0 0 one_pos] with ω hreg hν hω
  have hR := hreg.rescale' (Qc γ) hb0
  have hνR := isVagueLimitR_rescale hreg hγ.ne' hν n
  have hPsi := (Psi_normC γ (Ioo (1 : ℝ) 2) _).trans (Psi_addConst isOpen_Ioo ⟨_, hR⟩ hνR _)
  have hm : Measurable fun s : ℝ => s * ((2 : ℝ) ^ n)⁻¹ := measurable_id.mul_const _
  rw [Measure.map_apply hm measurableSet_Ioo, preimage_mul_inv_Ioo_one_two] at hPsi
  have h01 : IsProbabilityMeasure fc01 := by unfold fc01; infer_instance
  have hR01 : rescale (X ω) (Qc γ) ((2 : ℝ) ^ n) fc01 =
      X ω (fc01.map fun u => (((2 : ℝ) ^ n : ℝ) : ℂ) * u) + Qc γ * (n * Real.log 2) := by
    rw [rescale_fc_apply _ _ hb0 fc01, show fc01 = foldedCircle 0 1 from rfl, hω, Real.log_pow]
  rw [hPsi, hR01, ← mul_assoc, ← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.exp_add]
  refine le_trans ?_ (setLIntegral_mono (ENNReal.measurable_ofReal.comp
    (measurable_id.pow_const _)) fun t ht => ENNReal.ofReal_le_ofReal (window_weight_le hβ n ht))
  rw [setLIntegral_const]
  apply le_of_eq
  congr 3
  ring

/-- **WEDGE-BDRY 4 (a), case `α'' ≥ 0`.** -/
theorem ae_lintegral_Ici_weight_eq_top_of_nonneg (hX : IsFreeGFFModConstH X P) {γ : ℝ}
    (hγ : 0 < γ) (hγ2 : γ < 2) {α'' : ℝ} (h0 : 0 ≤ α'') (hα : α'' < Qc γ) :
    ∀ᵐ ω ∂P, ∫⁻ t in Ici (1 : ℝ), ENNReal.ofReal (t ^ (-(α'' * γ / 2)))
      ∂qBoundaryMeasure γ (X ω) = ⊤ := by
  obtain ⟨G, hG⟩ := WedgeTK.exists_isRegVersion hX
  have hXm : Measurable X := WedgeTK.measurable_X_pi hX
  have hΦm : Measurable fun c : ℕ → ℝ => Psi γ (Ioo (1 : ℝ) 2) (reconstruct c) :=
    (measurable_Psi γ _).comp measurable_reconstruct
  have hNm : Measurable fun ω => normC (X ω) :=
    measurable_pi_iff.2 fun i => (hX.measurable_coord _).sub (hX.measurable_coord _)
  have hNm' : ∀ n : ℕ, Measurable fun ω => normC (rescale (X ω) (Qc γ) ((2 : ℝ) ^ n)) := by
    intro n
    have : IsProbabilityMeasure fc01 := by unfold fc01; infer_instance
    refine measurable_pi_iff.2 fun i => ?_
    have : IsProbabilityMeasure (fcI i) := by unfold fcI; infer_instance
    exact ((measurable_coordChange_apply (fun z : ℂ => (((2 : ℝ) ^ n : ℝ) : ℂ) * z) (Qc γ)
      (fcI i)).comp hXm).sub ((measurable_coordChange_apply
        (fun z : ℂ => (((2 : ℝ) ^ n : ℝ) : ℂ) * z) (Qc γ) fc01).comp hXm)
  set M : Ω → ℝ≥0∞ := fun ω => Psi γ (Ioo (1 : ℝ) 2) (reconstruct (normC (X ω))) with hM
  set M' : ℕ → Ω → ℝ≥0∞ := fun n ω =>
    Psi γ (Ioo (1 : ℝ) 2) (reconstruct (normC (rescale (X ω) (Qc γ) ((2 : ℝ) ^ n)))) with hM'
  have hMm : Measurable M := hΦm.comp hNm
  have hM'm : ∀ n, Measurable (M' n) := fun n => hΦm.comp (hNm' n)
  have hlaw : ∀ n, P.map (M' n) = P.map M := by
    intro n
    have e1 : M' n = (fun c : ℕ → ℝ => Psi γ (Ioo (1 : ℝ) 2) (reconstruct c)) ∘
      fun ω => normC (rescale (X ω) (Qc γ) ((2 : ℝ) ^ n)) := rfl
    have e2 : M = (fun c : ℕ → ℝ => Psi γ (Ioo (1 : ℝ) 2) (reconstruct c)) ∘
      fun ω => normC (X ω) := rfl
    rw [e1, e2, ← Measure.map_map hΦm (hNm' n), ← Measure.map_map hΦm hNm,
      map_normC_rescale hX hG (Qc γ) (by positivity)]
  have hMpos : ∀ᵐ ω ∂P, 0 < M ω := by
    filter_upwards [hG.reg, BdryExist.ae_isVagueLimitR_qBoundaryMeasure hX hγ hγ2,
      Positivity.ae_forall_pos_qBoundaryMeasure hX hγ hγ2] with ω hreg hν hpos
    have h := (Psi_normC γ (Ioo (1 : ℝ) 2) (X ω)).trans
      (Psi_addConst isOpen_Ioo ⟨_, hreg⟩ hν _)
    show 0 < Psi γ (Ioo (1 : ℝ) 2) (reconstruct (normC (X ω)))
    rw [h]
    exact ENNReal.mul_pos (ENNReal.ofReal_pos.2 (Real.exp_pos _)).ne'
      (hpos _ (by rw [interior_Ioo]; exact ⟨3 / 2, by norm_num, by norm_num⟩)).ne'
  have hsmallM : Tendsto (fun k : ℕ => P {ω | M ω < ((k : ℝ≥0∞) + 1)⁻¹}) atTop (𝓝 0) := by
    have hanti : Antitone fun k : ℕ => {ω | M ω < ((k : ℝ≥0∞) + 1)⁻¹} := by
      intro k k' hkk' ω hω
      simp only [mem_setOf_eq] at hω ⊢
      refine hω.trans_le (ENNReal.inv_le_inv.2 ?_)
      gcongr
    have hlim := tendsto_measure_iInter_atTop (μ := P)
      (fun k => (measurableSet_lt hMm measurable_const).nullMeasurableSet) hanti
      ⟨0, measure_ne_top _ _⟩
    have h0 : P (⋂ k : ℕ, {ω | M ω < ((k : ℝ≥0∞) + 1)⁻¹}) = 0 := by
      refine measure_mono_null (fun ω hω => ?_) (ae_iff.1 hMpos)
      simp only [mem_iInter, mem_setOf_eq] at hω ⊢
      intro hp
      obtain ⟨k, hk⟩ := ENNReal.exists_inv_nat_lt hp.ne'
      have : ((k : ℝ≥0∞) + 1)⁻¹ ≤ (k : ℝ≥0∞)⁻¹ := ENNReal.inv_le_inv.2 le_self_add
      exact absurd ((hω k).trans_le this) (not_lt.2 hk.le)
    rw [h0] at hlim
    exact hlim
  have hsmallX : Tendsto (fun K : ℕ => P {ω | X ω fc01 ≤ -(K : ℝ)}) atTop (𝓝 0) := by
    have hanti : Antitone fun K : ℕ => {ω | X ω fc01 ≤ -(K : ℝ)} := by
      intro K K' h ω hω
      simp only [mem_setOf_eq] at hω ⊢
      have : (K : ℝ) ≤ K' := by exact_mod_cast h
      linarith
    have hlim := tendsto_measure_iInter_atTop (μ := P)
      (fun K => (measurableSet_le (hX.measurable_coord fc01) measurable_const).nullMeasurableSet)
      hanti ⟨0, measure_ne_top _ _⟩
    have h0 : (⋂ K : ℕ, {ω | X ω fc01 ≤ -(K : ℝ)}) = ∅ := by
      refine eq_empty_iff_forall_notMem.2 fun ω hω => ?_
      simp only [mem_iInter, mem_setOf_eq] at hω
      obtain ⟨K, hK⟩ := exists_nat_gt (-(X ω fc01))
      linarith [hω K]
    rw [h0, measure_empty] at hlim
    exact hlim
  have hβ0 : 0 ≤ α'' * γ / 2 := by positivity
  have hq0 : 0 < Qc γ - α'' := by linarith
  have hbad : ∀ n k K : ℕ, P {ω | ∫⁻ t in Ioo ((2 : ℝ) ^ n) (2 ^ (n + 1)),
      ENNReal.ofReal (t ^ (-(α'' * γ / 2))) ∂qBoundaryMeasure γ (X ω) < 1} ≤
      P {ω | M' n ω < ((k : ℝ≥0∞) + 1)⁻¹} + P {ω | X ω fc01 ≤ -(K : ℝ)} +
      P {ω | X ω (fc01.map fun u => (((2 : ℝ) ^ n : ℝ) : ℂ) * u) - X ω fc01 +
        (Qc γ - α'') * (n * Real.log 2) ≤
        2 / γ * (Real.log ((k : ℝ) + 1) + α'' * γ / 2 * Real.log 2) + K} := by
    intro n k K
    refine (measure_mono_ae ?_).trans ((measure_union_le _ _).trans
      (add_le_add_left (measure_union_le _ _) _))
    filter_upwards [ae_window_bound hX hG hγ hγ2 hβ0 n] with ω hω hlt
    refine by_contra fun hcon => ?_
    simp only [mem_union, mem_setOf_eq, not_or, not_lt, not_le] at hcon hlt
    obtain ⟨⟨h1, h2⟩, h3⟩ := hcon
    set V := X ω (fc01.map fun u => (((2 : ℝ) ^ n : ℝ) : ℂ) * u) with hV
    have key : γ / 2 * (2 / γ * (Real.log ((k : ℝ) + 1) + α'' * γ / 2 * Real.log 2)) =
        Real.log ((k : ℝ) + 1) + α'' * γ / 2 * Real.log 2 := by
      field_simp
    have h3' := mul_lt_mul_of_pos_left h3 (half_pos hγ)
    have h2' := mul_lt_mul_of_pos_left h2 (half_pos hγ)
    have hS : Real.log ((k : ℝ) + 1) < -(((n : ℝ) + 1) * Real.log 2) * (α'' * γ / 2) +
        γ / 2 * (V + Qc γ * (n * Real.log 2)) := by
      nlinarith [key, h3', h2']
    have hE : ((k : ℝ≥0∞) + 1) ≤ ENNReal.ofReal (Real.exp (-(((n : ℝ) + 1) * Real.log 2) *
        (α'' * γ / 2) + γ / 2 * (V + Qc γ * (n * Real.log 2)))) := by
      rw [show ((k : ℝ≥0∞) + 1) = ENNReal.ofReal ((k : ℝ) + 1) by
        rw [ENNReal.ofReal_add (Nat.cast_nonneg _) zero_le_one, ENNReal.ofReal_natCast,
          ENNReal.ofReal_one]]
      exact ENNReal.ofReal_le_ofReal ((Real.log_lt_iff_lt_exp (by positivity)).1 hS).le
    have h1' : 1 ≤ ENNReal.ofReal (Real.exp (-(((n : ℝ) + 1) * Real.log 2) *
        (α'' * γ / 2) + γ / 2 * (V + Qc γ * (n * Real.log 2)))) * M' n ω :=
      calc (1 : ℝ≥0∞) = ((k : ℝ≥0∞) + 1) * ((k : ℝ≥0∞) + 1)⁻¹ :=
            (ENNReal.mul_inv_cancel (by positivity) (by simp)).symm
        _ ≤ _ := mul_le_mul' hE h1
    exact absurd (h1'.trans hω) (not_le.2 hlt)
  have hsmall : ∀ ε : ℝ≥0∞, 0 < ε → ∀ N : ℕ, ∃ n ≥ N, P {ω | ∫⁻ t in Ioo ((2 : ℝ) ^ n)
      (2 ^ (n + 1)), ENNReal.ofReal (t ^ (-(α'' * γ / 2))) ∂qBoundaryMeasure γ (X ω) < 1} ≤ ε := by
    intro ε hε N
    have hε3 : 0 < ε / 3 := ENNReal.div_pos hε.ne' (by norm_num)
    obtain ⟨k, hk⟩ := ((tendsto_order.1 hsmallM).2 _ hε3).exists
    obtain ⟨K, hK⟩ := ((tendsto_order.1 hsmallX).2 _ hε3).exists
    obtain ⟨n, hn⟩ := (((tendsto_order.1 (tendsto_prob_drift hX hq0
      (2 / γ * (Real.log ((k : ℝ) + 1) + α'' * γ / 2 * Real.log 2) + K))).2 _ hε3).and
        (eventually_ge_atTop N)).exists
    refine ⟨n, hn.2, (hbad n k K).trans ?_⟩
    have hMn : P {ω | M' n ω < ((k : ℝ≥0∞) + 1)⁻¹} = P {ω | M ω < ((k : ℝ≥0∞) + 1)⁻¹} := by
      have := congrArg (fun μ : Measure ℝ≥0∞ => μ (Iio ((k : ℝ≥0∞) + 1)⁻¹)) (hlaw n)
      rw [Measure.map_apply (hM'm n) measurableSet_Iio,
        Measure.map_apply hMm measurableSet_Iio] at this
      exact this
    rw [hMn, ← ENNReal.add_thirds ε]
    exact add_le_add (add_le_add hk.le hK.le) hn.1.le
  filter_upwards [ae_frequently_one_le_of_prob_small _ hsmall] with ω hω
  exact lintegral_Ici_one_eq_top_of_frequently hω

end FreeField

/-- **WEDGE-BDRY 4 (a).** -/
theorem wedgeBdryFreeInfStmt_holds : WedgeBdryFreeInfStmt := by
  intro Ω _ P _ X hX γ hγ hγ2 α'' hα
  have hQ : 0 < Qc γ := by unfold Qc; positivity
  have h := ae_lintegral_Ici_weight_eq_top_of_nonneg hX hγ hγ2 (le_max_right α'' 0)
    (max_lt hα hQ)
  filter_upwards [h] with ω hω
  rw [eq_top_iff, ← hω]
  refine setLIntegral_mono (ENNReal.measurable_ofReal.comp (measurable_id.pow_const _))
    fun t ht => ENNReal.ofReal_le_ofReal (Real.rpow_le_rpow_of_exponent_le (mem_Ici.1 ht) ?_)
  have : α'' ≤ max α'' 0 := le_max_left _ _
  nlinarith

end WedgeBdry

end QuantumZipper
