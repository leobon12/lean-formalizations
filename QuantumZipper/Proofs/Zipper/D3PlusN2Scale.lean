import QuantumZipper.Proofs.Zipper.D3PlusN2Harm

/-!
# D3⁺(i), node N2-scale: the local scale tends to `0`, from the harmonic part

Task D3P-N2. Proves `D3PlusIN2FixScaleStmt` (`D3PlusN2CM.lean`) from `D3PlusN2HarmPartStmt`
(`D3PlusN2Harm.lean`). Source of the analytic part: the proof of D3⁺(iii) (`D3PlusIII.lean`;
Sheffield, arXiv:1012.4797, proof of Prop. 1.6, p. 25): adding `L/γ` multiplies the area by
`e^L`, and the area of the model field is positive on every half-ball and finite near `0`.

Steps (own elementary arguments):
* with `H_ω` the harmonic part, the zoomed local field `Z + α(−log) + φ + L/γ` agrees at every
  dyadic circle of `circSet r` with the D3⁺(iii) model `zoomModel γ α L 0 (X ω) ψ_ω`,
  `ψ_ω = φ − H_ω + X ω 0` (continuous on the half-disc) and with N1's local model
  (`agreeNear_zoomModel_tm`, `agreeNear_n2`);
* hence a.s. for all `L` the N1 parameter is good and the local scale is the measurable surrogate
  `scaleSur`, and a.s. eventually it lies in `(0, δ)` (`eventually_sInf_pos_lt`);
* dominated convergence for the indicators of the (measurable) surrogate bad events.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal ENNReal

namespace QuantumZipper
namespace D3Plus

/-- The D3⁺(iii) model with correction `φ − H + x 0` agrees with N1's local model. -/
theorem agreeNear_zoomModel_tm {γ α L r : ℝ} {x : FieldSample} {φ Hc : ℂ → ℝ}
    (hφ : ContinuousOn φ (Metric.ball (0 : ℂ) r ∩ Hbar))
    (hH : ContinuousOn Hc (Metric.ball (0 : ℂ) r ∩ Hbar))
    (hdec : ∀ μ ∈ circSet r, x (K3.bal 0 r μ) = ∫ z, Hc z ∂μ) :
    AgreeNear (zoomModel γ α L 0 x (fun z => φ z - Hc z + x 0))
      (locModel γ L r (fun μ : LocIdx r => x μ.1 - x (K3.bal 0 r μ.1), circData α φ)) r := by
  classical
  intro n k z hz
  have hmem : foldedCircle (dyadicRoundC n z) (radius k) ∈ circSet r := ⟨n, k, z, hz, rfl⟩
  have hloc := isLocalH_of_mem_circSet hmem
  have i1 : Integrable (fun w => α * -Real.log ‖w‖ + φ w)
      (foldedCircle (dyadicRoundC n z) (radius k)) := integrable_circ hφ hmem
  have iH : Integrable Hc (foldedCircle (dyadicRoundC n z) (radius k)) :=
    integrable_of_admCorr le_rfl hH ⟨_, hloc⟩
  have i2 : Integrable (fun w => (α * -Real.log ‖w‖ + φ w) - Hc w)
      (foldedCircle (dyadicRoundC n z) (radius k)) := i1.sub iH
  have e : (fun w => α * -Real.log ‖w‖ + (φ w - Hc w + x 0) + (L / γ - x 0)) =
      fun w => ((α * -Real.log ‖w‖ + φ w) - Hc w) + L / γ := by
    funext w; ring
  simp only [zoomModel, locModel, dif_pos hmem, circData, ofFun, Pi.add_apply]
  rw [e, integral_add i2 (integrable_const _), integral_sub i1 iH, integral_const, Measure.real,
    measure_univ, ENNReal.toReal_one, one_smul, ← hdec _ hmem]
  ring

/-- **`D3PlusIN2FixScaleStmt` from the harmonic part.** -/
theorem d3PlusIN2FixScale_of_harm (hHP : D3PlusN2HarmPartStmt) : D3PlusIN2FixScaleStmt := by
  intro γ α r Ω _ P _ X φ hγ hγ2 hα hr hX hφ δ hδ
  set p : Ω → N1Idx r := fun ω => (localZ X r ω, circData α φ) with hpdef
  have hp : Measurable p := (measurable_localZ hX hr).prodMk measurable_const
  have key : ∀ᵐ ω ∂P, (∀ L : ℝ, scaleParamOn γ (locZField X r ω + ofFun (n2Shift γ α L φ))
      (halfDisc r) = scaleSur γ L r (p ω)) ∧
      ∀ᶠ L in atTop, 0 < scaleSur γ L r (p ω) ∧ scaleSur γ L r (p ω) < δ := by
    filter_upwards [hHP r P X hr hX, AreaExist.ae_isVagueLimitOn_qAreaMeasure hX hγ hγ2,
      AreaOffsets.ae_isLQGGood hX hγ hγ2, PositivityArea.ae_forall_pos_qAreaMeasure hX hγ hγ2,
      WedgeFinZero.ae_withDensity_ball_lt_top hX hγ hγ2 hα] with ω hHω hvag hgood hpos hfin
    obtain ⟨Hc, hc, -, hdec⟩ := hHω
    set ψ : ℂ → ℝ := fun z => φ z - Hc z + X ω 0 with hψdef
    have hψc : ContinuousOn ψ (Metric.ball (0 : ℂ) r ∩ Hbar) :=
      (hφ.1.sub hc).add continuousOn_const
    have hag : ∀ L, AgreeNear (zoomModel γ α L 0 (X ω) ψ) (locModel γ L r (p ω)) r :=
      fun L => agreeNear_zoomModel_tm hφ.1 hc hdec
    have hag2 : ∀ L, AgreeNear (locZField X r ω + ofFun (n2Shift γ α L φ))
        (locModel γ L r (p ω)) r :=
      fun L => agreeNear_n2 fun μ hμ => ⟨integrable_circ hφ.1 hμ, rfl⟩
    have hU := isOpen_halfDisc r
    have hres := AtomlessUncond.isVagueLimitOn_restrict hU (halfDisc_subset_H r) hvag
    have hW : IsOpen (Metric.ball (0 : ℂ) r \ {0}) :=
      Metric.isOpen_ball.sdiff isClosed_singleton
    have hvagL : ∀ L : ℝ, ∃ m, IsVagueLimitOn (halfDisc r)
        (areaApprox γ (zoomModel γ α L 0 (X ω) ψ)) m := fun L =>
      ⟨_, LocalRule.isVagueLimitOn_add_ofFun hgood.1 hU (halfDisc_subset_H r) hres hW
        (halfDisc_subset_ball_diff r) (continuousOn_zoomPot (γ := γ) (α := α) (L := L)
          (ρ₀ := 0) (x := X ω) hψc)⟩
    have hgoodL : ∀ L, p ω ∈ goodN1 γ L r := fun L =>
      (exists_isVagueLimitOn_halfDisc_iff (hag L)).1 (hvagL L)
    have hsur : ∀ L, scaleSur γ L r (p ω) =
        scaleParamOn γ (zoomModel γ α L 0 (X ω) ψ) (halfDisc r) := fun L =>
      (scaleSur_eq (hgoodL L)).trans (scaleParamOn_halfDisc_congr (hag L)).symm
    refine ⟨fun L => (scaleParamOn_halfDisc_congr (hag2 L)).trans (scaleSur_eq (hgoodL L)).symm,
      ?_⟩
    filter_upwards [eventually_sInf_pos_lt
      (zoomMeasure_pos (γ := γ) (α := α) (ρ₀ := 0) (x := X ω) hr hpos hψc)
      (zoomMeasure_fin (ρ₀ := 0) (x := X ω) hγ hr hfin hψc) hδ] with L hL
    rw [hsur L, scaleParamOn_zoomModel hγ.ne' hgood.1 hvag hψc]
    exact hL
  set B' : ℝ → Set Ω := fun L =>
    p ⁻¹' {q | ¬(0 < scaleSur γ L r q ∧ scaleSur γ L r q < δ)} with hB'def
  have hB'm : ∀ L, MeasurableSet (B' L) := fun L => hp
    (((measurableSet_lt measurable_const (measurable_scaleSur γ L r)).inter
      (measurableSet_lt (measurable_scaleSur γ L r) measurable_const)).compl)
  have hae : ∀ L, P {ω | ¬(0 < scaleParamOn γ (locZField X r ω + ofFun (n2Shift γ α L φ))
      (halfDisc r) ∧ scaleParamOn γ (locZField X r ω + ofFun (n2Shift γ α L φ)) (halfDisc r) <
        δ)} = P (B' L) := by
    intro L
    refine measure_congr ?_
    filter_upwards [key] with ω hω
    show (¬(0 < scaleParamOn γ (locZField X r ω + ofFun (n2Shift γ α L φ)) (halfDisc r) ∧
      scaleParamOn γ (locZField X r ω + ofFun (n2Shift γ α L φ)) (halfDisc r) < δ)) =
        (¬(0 < scaleSur γ L r (p ω) ∧ scaleSur γ L r (p ω) < δ))
    rw [hω.1 L]
  simp_rw [hae]
  have hlim : Tendsto (fun L => ∫⁻ ω, (B' L).indicator 1 ω ∂P) atTop (𝓝 (∫⁻ _ω, 0 ∂P)) := by
    refine tendsto_lintegral_filter_of_dominated_convergence (fun _ => 1)
      (Eventually.of_forall fun L => measurable_one.indicator (hB'm L))
      (Eventually.of_forall fun L => Eventually.of_forall fun ω =>
        indicator_le_self' (fun _ _ => zero_le_one) ω) (by simp) ?_
    filter_upwards [key] with ω hω
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [hω.2] with L hL
    have hn : ω ∉ B' L := by
      simp only [hB'def, mem_preimage, mem_setOf_eq, not_not]
      exact hL
    rw [indicator_of_notMem hn]
  simp only [lintegral_zero] at hlim
  refine hlim.congr fun L => ?_
  rw [lintegral_indicator_one (hB'm L)]

/-- **Node N2 (rich) from three inputs**: the model zoom, the free-field Cameron–Martin bound and
the continuous harmonic part. -/
theorem d3PlusIN2Rich_of_core (hZ : D3PlusIN2TmZeroStmt) (hCMI : CMIncrStmt)
    (hHP : D3PlusN2HarmPartStmt) : D3PlusIN2RichStmt :=
  d3PlusIN2Rich_of_nodes hZ hCMI (d3PlusIN2FixScale_of_harm hHP) (d3PlusIN2FixMacro_of_harm hHP)

end D3Plus
end QuantumZipper
