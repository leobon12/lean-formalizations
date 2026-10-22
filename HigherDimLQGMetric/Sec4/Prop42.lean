import HigherDimLQGMetric.Sec4.Lemma45

/-!
# [1] Proposition 4.2 (packet L9b; MA6 P10, Prop 4.2 and its proof)

`prop42`: MA6's statement of [1] Prop 4.2 (comparison of the normalized convolution LFPP with a weak exponential
metric with arbitrary normalizers; the constant `C` does not depend on `U`), with the B3/B2 interface hypotheses
`hL6a : ∀ d ξ κ, L6a_tight d ξ κ` (corrected [1] Lemma 3.3) and `hB2 : ∀ d κ ξ Q, RealEpsAdapterShape d κ ξ Q`
(MA7 D-ADP, which discharges `L6a_tight`'s premise together with L10a's `l10a_dgzHyp`) as leading explicit
arguments (rulings M30, M31). `prop42Shape_of hL6a hB2 : Prop42Shape` is the same statement in the form of the
orchestrator's B4 interface (consumed by L9c, [1] Theorem 1.6).

Proof ([1] p. 37 with MA6 P10): Lemma 4.5 gives, for small `ε`, at least `|N^ε|/2 ≥ |N^ε|/10` radii with ratio in
`[C₅⁻¹, C₅]`; Lemma 4.4 with this set gives (4.9), (4.10) for the localized LFPP `D̂^ε` with constant `C₄ C₅`, outside
probability `θ/2`; Lemma 4.1 on a ball containing `B_{ε^{1-ζ}}(U)` gives `|h*_ε - ĥ*_ε| ≤ log 2/ξ` there outside
probability `θ/2`, so the internal LFPP distances of `h*_ε` and `ĥ*_ε` on `B_{ε^{1-ζ}}(U)` (and on `U`) differ by a
factor `≤ 2` (MA6 G-12: the omitted `D̂^ε → D^ε` passage); `C = 2 C₄ C₅`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology Metric
open scoped ENNReal

namespace HigherDimLQGMetric

open HigherDimLFPP (Rd e₁ IsLFPPKernel)

variable {d : ℕ}

/-- field comparison for set distances -/
theorem fieldSetDistIn_le_exp_mul {ξ : ℝ} {φ ψ : Rd d → ℝ} {V A B : Set (Rd d)} {M : ℝ}
    (hM : ∀ z ∈ V, |φ z - ψ z| ≤ M) :
    fieldSetDistIn ξ φ V A B ≤ ENNReal.ofReal (Real.exp (|ξ| * M)) * fieldSetDistIn ξ ψ V A B := by
  have hK0 : ENNReal.ofReal (Real.exp (|ξ| * M)) ≠ 0 := by simp [Real.exp_pos]
  unfold fieldSetDistIn
  simp only [ENNReal.mul_iInf_of_ne hK0 ENNReal.ofReal_ne_top]
  exact iInf₂_mono fun x _ => iInf₂_mono fun y _ => fieldDistIn_le_exp_mul hM

theorem l9b_exp_log_two {ξ : ℝ} (hξ : 0 < ξ) : Real.exp (|ξ| * (Real.log 2 / ξ)) = 2 := by
  rw [abs_of_pos hξ, mul_div_cancel₀ _ hξ.ne', Real.exp_log two_pos]

/-- **[1] Proposition 4.2** (MA6's `prop42`, with the interface hypotheses `hL6a`, `hB2` first). -/
theorem prop42 (hL6a : ∀ (d : ℕ) (ξ : ℝ) (κ : Rd d → ℝ), L6a_tight d ξ κ)
    (hB2 : ∀ (d : ℕ) (κ : Rd d → ℝ) (ξ Q : ℝ), DGZ.RealEpsAdapterShape d κ ξ Q)
    (hd : 3 ≤ d) {ξ : ℝ} (hξ : 0 < ξ) (hsub : Real.sqrt (2 * d) < distExp d ξ)
    {κ : Rd d → ℝ} (hκ : IsLFPPKernel κ) {D : DistRd d → ContMetric d} {c : ℝ → ℝ}
    (hD : IsWeakExpMetric d ξ D c) {ζ : ℝ} (hζ0 : 0 < ζ) (hζ1 : ζ < 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ U : Set (Rd d), IsOpen U → Bornology.IsBounded U → IsConnected U →
      ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
        (h : Ω → DistRd d), IsNormalizedLGF h P →
        Tendsto (fun ε => P {ω | ¬ ∀ z ∈ U, ∀ w ∈ U,
            ENNReal.ofReal ((aEps κ ξ ε)⁻¹) * lfppSetDistIn κ ξ ε (h ω)
                (Metric.thickening (ε ^ (1 - ζ)) U) (Metric.ball z (ε ^ (1 - ζ)))
                (Metric.ball w (ε ^ (1 - ζ))) ≤ ENNReal.ofReal C * (D (h ω)).internal U z w ∧
            setDistIn (D (h ω)) (Metric.thickening (ε ^ (1 - ζ)) U) (Metric.ball z (ε ^ (1 - ζ)))
                (Metric.ball w (ε ^ (1 - ζ))) ≤
              ENNReal.ofReal C * (ENNReal.ofReal ((aEps κ ξ ε)⁻¹) * lfppDistIn κ ξ ε (h ω) U z w)})
          (𝓝[>] 0) (𝓝 0) := by
  have hd2 : 2 ≤ d := by omega
  obtain ⟨C₅, hC₅, ε₅, hε₅, H45⟩ := ref1_lemma45 hL6a hB2 hd hξ hsub hκ hD hζ0 hζ1
  obtain ⟨C₄, hC₄, H44⟩ := ref1_lemma44 hL6a hB2 hd hξ hsub hκ hD hζ0 hζ1
  have hC₅0 : 0 < C₅ := by linarith
  refine ⟨2 * (C₄ * C₅), by positivity, ?_⟩
  intro U _ hU _ Ω _ P _ h hh
  rw [ENNReal.tendsto_nhds_zero]
  intro θ hθ
  have hθ2 : 0 < θ / 2 := ENNReal.half_pos hθ.ne'
  obtain ⟨ε₄, hε₄, H4⟩ := H44 U hU (θ / 2) hθ2
  obtain ⟨R', hR'⟩ := hU.subset_closedBall 0
  set R : ℝ := max R' 0 + 1 with hR
  have hR0 : 0 < R := by positivity
  set η : ℝ := Real.log 2 / ξ with hη
  have hη0 : 0 < η := div_pos (Real.log_pos (by norm_num)) hξ
  have h41 := (ENNReal.tendsto_nhds_zero.1 (ref1_lemma41 hd2 hκ P h hh hR0 hη0)) (θ / 2) hθ2
  have hrpow : ∀ᶠ ε in 𝓝[>] (0 : ℝ), ε ^ (1 - ζ) ≤ 1 := by
    filter_upwards [self_mem_nhdsWithin, Ioo_mem_nhdsGT (show (0 : ℝ) < 1 by norm_num)] with
      ε hε hε1
    exact Real.rpow_le_one (le_of_lt hε) hε1.2.le (by linarith)
  filter_upwards [h41, hrpow, Ioo_mem_nhdsGT (lt_min hε₄ hε₅)] with ε hloc hεζ hε
  have hε0 : 0 < ε := hε.1
  have hε4 : ε < ε₄ := hε.2.trans_le (min_le_left _ _)
  have hε5 : ε < ε₅ := hε.2.trans_le (min_le_right _ _)
  have hG45 := H45 ε ⟨hε0, hε5⟩
  set G := (nIdx ζ ε).filter fun k =>
    C₅⁻¹ ≤ l9bRatio κ ξ c ε (dyad k) ∧ l9bRatio κ ξ c ε (dyad k) ≤ C₅ with hG
  have hGcard : (nIdx ζ ε).card ≤ 10 * G.card := by omega
  have hbad44 := H4 P h hh ε ⟨hε0, hε4⟩ G (Finset.filter_subset _ _) hGcard C₅⁻¹ C₅
    (inv_pos.2 hC₅0) hC₅0 fun k hk => (Finset.mem_filter.1 hk).2
  -- the bad event of Prop 4.2 is contained in the union of the two bad events
  have hsub' : {ω | ¬ ∀ z ∈ U, ∀ w ∈ U,
      ENNReal.ofReal ((aEps κ ξ ε)⁻¹) * lfppSetDistIn κ ξ ε (h ω)
          (Metric.thickening (ε ^ (1 - ζ)) U) (Metric.ball z (ε ^ (1 - ζ)))
          (Metric.ball w (ε ^ (1 - ζ))) ≤ ENNReal.ofReal (2 * (C₄ * C₅)) * (D (h ω)).internal U z w ∧
      setDistIn (D (h ω)) (Metric.thickening (ε ^ (1 - ζ)) U) (Metric.ball z (ε ^ (1 - ζ)))
          (Metric.ball w (ε ^ (1 - ζ))) ≤
        ENNReal.ofReal (2 * (C₄ * C₅)) * (ENNReal.ofReal ((aEps κ ξ ε)⁻¹) *
          lfppDistIn κ ξ ε (h ω) U z w)} ⊆
      {ω | ¬ ∀ z ∈ U, ∀ w ∈ U,
          ENNReal.ofReal ((aEps κ ξ ε)⁻¹) * fieldSetDistIn ξ (locField κ ε (h ω))
              (thickening (ε ^ (1 - ζ)) U) (ball z (ε ^ (1 - ζ))) (ball w (ε ^ (1 - ζ))) ≤
            ENNReal.ofReal (C₄ * C₅) * (D (h ω)).internal U z w ∧
          setDistIn (D (h ω)) (thickening (ε ^ (1 - ζ)) U) (ball z (ε ^ (1 - ζ)))
              (ball w (ε ^ (1 - ζ))) ≤
            ENNReal.ofReal (C₄ * C₅⁻¹⁻¹) * (ENNReal.ofReal ((aEps κ ξ ε)⁻¹) *
              fieldDistIn ξ (locField κ ε (h ω)) U z w)} ∪
      {ω | ∃ x ∈ closedBall (0 : Rd d) R,
        η < |convMollify κ ε (h ω) x - locField κ ε (h ω) x|} := by
    intro ω hω
    by_contra hnot
    simp only [mem_union, mem_ofPred_eq, not_or, not_not, not_exists, not_and, not_lt] at hnot
    obtain ⟨hgood, hclose⟩ := hnot
    apply hω
    intro z hz w hw
    obtain ⟨h49, h410⟩ := hgood z hz w hw
    -- the two fields are `log 2 / ξ`-close on `B_1(U) ⊆ B̄_R(0)`
    have hV : ∀ x ∈ thickening (ε ^ (1 - ζ)) U, |convMollify κ ε (h ω) x -
        locField κ ε (h ω) x| ≤ η := by
      intro x hx
      refine hclose x ?_
      obtain ⟨y, hyU, hxy⟩ := mem_thickening_iff.1 hx
      rw [mem_closedBall, dist_zero_right]
      have hy := hR' hyU
      rw [mem_closedBall, dist_zero_right] at hy
      rw [dist_eq_norm] at hxy
      have : ‖x‖ ≤ ‖x - y‖ + ‖y‖ := by
        calc ‖x‖ = ‖(x - y) + y‖ := by congr 1; abel
          _ ≤ _ := norm_add_le _ _
      have := le_max_left R' 0
      linarith
    have hUV : U ⊆ thickening (ε ^ (1 - ζ)) U :=
      self_subset_thickening (Real.rpow_pos_of_pos hε0 _) U
    have hexp := l9b_exp_log_two hξ
    constructor
    · rw [lfppSetDistIn_eq_fieldSetDistIn]
      have hcmp := fieldSetDistIn_le_exp_mul (ξ := ξ) (A := ball z (ε ^ (1 - ζ)))
        (B := ball w (ε ^ (1 - ζ))) hV
      rw [hexp] at hcmp
      calc ENNReal.ofReal (aEps κ ξ ε)⁻¹ * fieldSetDistIn ξ (convMollify κ ε (h ω))
            (thickening (ε ^ (1 - ζ)) U) (ball z (ε ^ (1 - ζ))) (ball w (ε ^ (1 - ζ)))
          ≤ ENNReal.ofReal (aEps κ ξ ε)⁻¹ * (ENNReal.ofReal 2 * fieldSetDistIn ξ
              (locField κ ε (h ω)) (thickening (ε ^ (1 - ζ)) U) (ball z (ε ^ (1 - ζ)))
                (ball w (ε ^ (1 - ζ)))) := by gcongr
        _ = ENNReal.ofReal 2 * (ENNReal.ofReal (aEps κ ξ ε)⁻¹ * fieldSetDistIn ξ
              (locField κ ε (h ω)) (thickening (ε ^ (1 - ζ)) U) (ball z (ε ^ (1 - ζ)))
                (ball w (ε ^ (1 - ζ)))) := by ring
        _ ≤ ENNReal.ofReal 2 * (ENNReal.ofReal (C₄ * C₅) * (D (h ω)).internal U z w) := by
            gcongr
        _ = ENNReal.ofReal (2 * (C₄ * C₅)) * (D (h ω)).internal U z w := by
            rw [← mul_assoc, ← ENNReal.ofReal_mul (by norm_num)]
    · rw [lfppDistIn_eq_fieldDistIn]
      have hcmp : fieldDistIn ξ (locField κ ε (h ω)) U z w ≤
          ENNReal.ofReal 2 * fieldDistIn ξ (convMollify κ ε (h ω)) U z w := by
        have := fieldDistIn_le_exp_mul (ξ := ξ) (φ := locField κ ε (h ω))
          (ψ := convMollify κ ε (h ω)) (V := U) (x := z) (y := w) (M := η)
          (fun x hx => by rw [abs_sub_comm]; exact hV x (hUV hx))
        rwa [hexp] at this
      rw [inv_inv] at h410
      calc setDistIn (D (h ω)) (thickening (ε ^ (1 - ζ)) U) (ball z (ε ^ (1 - ζ)))
            (ball w (ε ^ (1 - ζ)))
          ≤ ENNReal.ofReal (C₄ * C₅) * (ENNReal.ofReal (aEps κ ξ ε)⁻¹ *
              fieldDistIn ξ (locField κ ε (h ω)) U z w) := h410
        _ ≤ ENNReal.ofReal (C₄ * C₅) * (ENNReal.ofReal (aEps κ ξ ε)⁻¹ *
              (ENNReal.ofReal 2 * fieldDistIn ξ (convMollify κ ε (h ω)) U z w)) := by gcongr
        _ = ENNReal.ofReal (2 * (C₄ * C₅)) * (ENNReal.ofReal (aEps κ ξ ε)⁻¹ *
              fieldDistIn ξ (convMollify κ ε (h ω)) U z w) := by
            rw [ENNReal.ofReal_mul (p := 2) (by norm_num)]; ring
  calc _ ≤ _ := measure_mono hsub'
    _ ≤ θ / 2 + θ / 2 := (measure_union_le _ _).trans (add_le_add hbad44 hloc)
    _ = θ := ENNReal.add_halves θ

/-- **[1] Proposition 4.2** in the form of the B4 interface (`Prop42Shape`, consumed by L9c). -/
theorem prop42Shape_of (hL6a : ∀ (d : ℕ) (ξ : ℝ) (κ : Rd d → ℝ), L6a_tight d ξ κ)
    (hB2 : ∀ (d : ℕ) (κ : Rd d → ℝ) (ξ Q : ℝ), DGZ.RealEpsAdapterShape d κ ξ Q) :
    Prop42Shape :=
  fun _ hd _ hξ hsub _ hκ _ _ hD _ hζ0 hζ1 => prop42 hL6a hB2 hd hξ hsub hκ hD hζ0 hζ1

end HigherDimLQGMetric
