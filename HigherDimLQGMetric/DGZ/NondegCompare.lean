import HigherDimLQGMetric.DGZ.NondegRelation

/-!
# Comparison of local coordinates after removing a fixed coarse field

The zero sets of the `m=0` and `m>0` internal metrics agree in every joint limit. The
closed comparison relations below record the finite multiplicative constants at the prelimit.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal

namespace HigherDimLQGMetric.DGZ

open HigherDimLFPP HigherDimLFPP.Perc

variable {d : ℕ}

/-- Closed bi-Lipschitz relation between two internal coordinates. -/
def nd_compSet (r : ℝ) (i : nd_DomainIndex d r) (m : ℕ) (R : ℝ) :
    Set (nd_Joint d r) :=
  {x | ∀ p : nd_domain r i × nd_domain r i,
    x.2 (i, 0) p ≤ R * x.2 (i, m) p ∧
      x.2 (i, m) p ≤ R * x.2 (i, 0) p}

theorem nd_isClosed_compSet (r : ℝ) (i : nd_DomainIndex d r) (m : ℕ) (R : ℝ) :
    IsClosed (nd_compSet r i m R) := by
  have e : nd_compSet r i m R = ⋂ p : nd_domain r i × nd_domain r i,
      {x : nd_Joint d r |
        x.2 (i, 0) p ≤ R * x.2 (i, m) p ∧
          x.2 (i, m) p ≤ R * x.2 (i, 0) p} := by
    ext x
    simp [nd_compSet]
  rw [e]
  refine isClosed_iInter fun p => ?_
  have h0 : Continuous (fun x : nd_Joint d r => x.2 (i, 0) p) :=
    (continuous_eval_const p).comp ((continuous_apply (i, 0)).comp continuous_snd)
  have hm : Continuous (fun x : nd_Joint d r => x.2 (i, m) p) :=
    (continuous_eval_const p).comp ((continuous_apply (i, m)).comp continuous_snd)
  exact (isClosed_le h0 (continuous_const.mul hm)).inter
    (isClosed_le hm (continuous_const.mul h0))

/-- Multiplicative stability of a normalized internal LFPP metric under a bounded field change. -/
theorem nd_internalMetricC_le_exp_mul {U : Set (Rd d)} (hU : IsOpen U)
    (hUc : IsPreconnected U) {φ ψ : Rd d → ℝ}
    (hφ : Continuous φ) (hψ : Continuous ψ) (ξ a M : ℝ)
    (ha : 0 ≤ a⁻¹) (hM : ∀ z ∈ U, |φ z - ψ z| ≤ M)
    (p : U × U) :
    internalMetricC ξ φ U a p ≤
      Real.exp (|ξ| * M) * internalMetricC ξ ψ U a p := by
  rw [internalMetricC_apply hφ hU hUc a p,
    internalMetricC_apply hψ hU hUc a p]
  have h := lfppDistOn_le_exp_mul hφ hψ hM
    (x := p.1.1) (y := p.2.1) (V := U) (ζ := ξ)
  calc
    a⁻¹ * lfppDistOn ξ φ U p.1.1 p.2.1
        ≤ a⁻¹ * (Real.exp (|ξ| * M) * lfppDistOn ξ ψ U p.1.1 p.2.1) :=
          mul_le_mul_of_nonneg_left h ha
    _ = Real.exp (|ξ| * M) * (a⁻¹ * lfppDistOn ξ ψ U p.1.1 p.2.1) := by ring

/-- A bounded coarse field makes the two local coordinates bi-Lipschitz at every level. -/
theorem nd_jointSample_mem_compSet {κ : Rd d → ℝ} {ξ Q : ℝ}
    (h : DGZHyp d κ ξ Q) {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
    {W : WN d → Ω → ℝ} {H : ℕ → Rd d → Ω → ℝ}
    (hH : IsDyadicRealization κ P W H) {q : ℝ≥0∞} (hq0 : 0 < q) (hq1 : q < 1)
    (r : ℝ) (n : ℕ) (i : nd_DomainIndex d r) (m : ℕ) (M : ℝ)
    (ω : Ω) (hzero : ∀ z, H 0 z ω = 0)
    (hbound : ∀ z ∈ nd_domain r i, |H m z ω| ≤ M) :
    nd_jointSample P H ξ q r n ω ∈ nd_compSet r i m (Real.exp (|ξ| * M)) := by
  intro p
  have hU := nd_isOpen_domain r i
  have hUc := (nd_isConnected_domain r i).isPreconnected
  have hn : Continuous fun z => H n z ω := (hH.band n).continuous ω
  have hm : Continuous fun z => H m z ω := (hH.band m).continuous ω
  have hz : (fun z => H n z ω - H 0 z ω) = (fun z => H n z ω) :=
    funext fun z => by rw [hzero z, sub_zero]
  have hnm : Continuous fun z => H n z ω - H m z ω := hn.sub hm
  have ha : 0 ≤ (aQ P H ξ n q)⁻¹ := inv_nonneg.2
    (tight_aQ_pos (by have := h.dim; omega : 0 < d) hH ξ n hq0 hq1).le
  constructor
  · change internalMetricC ξ (fun z => H n z ω - H 0 z ω) (nd_domain r i)
        (aQ P H ξ n q) p ≤
        Real.exp (|ξ| * M) *
          internalMetricC ξ (fun z => H n z ω - H m z ω) (nd_domain r i)
            (aQ P H ξ n q) p
    rw [hz]
    exact nd_internalMetricC_le_exp_mul hU hUc hn hnm ξ _ M ha
      (fun z hzU => by
        have heq : H n z ω - (H n z ω - H m z ω) = H m z ω := by ring
        simpa only [heq] using hbound z hzU) p
  · change internalMetricC ξ (fun z => H n z ω - H m z ω) (nd_domain r i)
        (aQ P H ξ n q) p ≤
        Real.exp (|ξ| * M) *
          internalMetricC ξ (fun z => H n z ω - H 0 z ω) (nd_domain r i)
            (aQ P H ξ n q) p
    rw [hz]
    exact nd_internalMetricC_le_exp_mul hU hUc hnm hn ξ _ M ha
      (fun z hzU => by
        have heq : (H n z ω - H m z ω) - H n z ω = -H m z ω := by ring
        simpa only [heq, abs_neg] using hbound z hzU) p

/-- Uniform probability of the closed comparison relation at every dyadic level. -/
theorem nd_prelimit_compSet_prob {κ : Rd d → ℝ} {ξ Q : ℝ}
    (h : DGZHyp d κ ξ Q) {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
    {W : WN d → Ω → ℝ} {H : ℕ → Rd d → Ω → ℝ}
    (hH : IsDyadicRealization κ P W H) {q : ℝ≥0∞} (hq0 : 0 < q) (hq1 : q < 1)
    (r : ℝ) (i : nd_DomainIndex d r) (m : ℕ) {θ : ℝ} (hθ : 0 < θ) :
    ∃ R : ℝ, 1 ≤ R ∧ ∀ n : ℕ,
      (1 : ℝ≥0∞) - ENNReal.ofReal θ ≤
        (nd_jointLaw P hH.whiteNoise.isProbabilityMeasure H ξ q r n : Measure (nd_Joint d r))
          (nd_compSet r i m R) := by
  obtain ⟨R₀, hR₀, hUbox⟩ := nd_exists_domain_cbox r i
  obtain ⟨L, hL, htail⟩ := exists_sup_tail_level_tight h.kernel m hR₀ hθ
  let R : ℝ := Real.exp (|ξ| * L)
  have hR : 1 ≤ R := by
    dsimp [R]
    exact (Real.one_le_exp_iff).2 (mul_nonneg (abs_nonneg ξ) hL)
  refine ⟨R, hR, fun n => ?_⟩
  let F := nd_compSet r i m R
  let X := nd_jointSample P H ξ q r n
  have hX : Measurable X := nd_measurable_jointSample hH ξ q r n
  have hF : MeasurableSet F := (nd_isClosed_compSet r i m R).measurableSet
  have hzero := ae_forall_eq_zero_of_isBandVersion_self h.kernel hH.whiteNoise one_pos
    ((hH.band 0).congr_band (pow_zero _) rfl)
  have hbad : P {ω | ∃ z ∈ HigherDimLFPP.DGZ.cbox (0 : Rd d) R₀,
      L < |H m z ω|} ≤ ENNReal.ofReal θ :=
    htail hH.whiteNoise (hH.band m) 0
  have hcompl : P (X ⁻¹' F)ᶜ ≤ ENNReal.ofReal θ := by
    calc
      P (X ⁻¹' F)ᶜ ≤ P {ω | ∃ z ∈ HigherDimLFPP.DGZ.cbox (0 : Rd d) R₀,
          L < |H m z ω|} := by
            apply measure_mono_ae
            filter_upwards [hzero] with ω hz hω
            by_contra hb
            have hbound : ∀ z ∈ nd_domain r i, |H m z ω| ≤ L := by
              intro z hzU
              exact le_of_not_gt (fun hlt => hb ⟨z, hUbox hzU, hlt⟩)
            exact hω (nd_jointSample_mem_compSet h hH hq0 hq1 r n i m L ω hz hbound)
      _ ≤ ENNReal.ofReal θ := hbad
  change (1 : ℝ≥0∞) - ENNReal.ofReal θ ≤ (P.map X) F
  rw [Measure.map_apply hX hF]
  apply tsub_le_iff_right.2
  calc
    1 = P (X ⁻¹' F) + P (X ⁻¹' F)ᶜ :=
      (@prob_add_prob_compl Ω _ P _ hH.whiteNoise.isProbabilityMeasure (hX hF)).symm
    _ ≤ P (X ⁻¹' F) + ENNReal.ofReal θ := add_le_add le_rfl hcompl

end HigherDimLQGMetric.DGZ
