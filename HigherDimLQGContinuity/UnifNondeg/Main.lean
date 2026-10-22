import HigherDimLQGContinuity.UnifNondeg.Nondeg
import HigherDimLQGContinuity.UnifTight.Exports
import HigherDimLQGContinuity.UnifTight.NondegCross

/-!
# The targets of packet U5: the sequence zero-one law, (A.3) = I9, (A.4) = I7 (ruling N28)

Blueprint Part D, `d:prop-u69`, `d:prop-u64` (NA3 §2.8–2.9, R11). By ruling N28 the interfaces I7 and I9 are proved
**without** the median-normalized I8 (which needs I7: packet U4's `uHolderTight_of_quantComp`), from packet U4's
hypothesis-free high-quantile forms:

* `holderTightAQShape_unif` (Part D `d:lem-u61`(b)) — `uHolderTightAQShape_holds`;
* `distInfAQShape_unif` (Part D `d:lem-u65`(c), `G = 0`) — `uDistInfAQShape_holds`;
* `nondeg_cross_pos_unif` (Part D `d:lem-u65`(b)) — `uCrossPosAt_holds`.

Results (all for `d ≥ 2` and an admissible kernel `κ`, no further hypothesis):
* `uNondegInputs_holds : UNondegInputs d κ` (one quantile `q ≥ ½` per `(b, μ)` at which the three inputs hold);
* **`nd_zeroOne_limitLaw_seq`**: the zero-one law along parameter arrays (blueprint `d:prop-u69`; the sequence version
  of `DGZ.nd_zeroOne_limitLaw`);
* **`uNondeg : UNondegShape d κ`** (interface I9; Part D `d:prop-u64`(a));
* **`uQuantComp : UQuantCompShape d κ`** (interface I7; Part D `d:prop-u64`(b)).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set Metric
open scoped ENNReal

namespace HigherDimLQGContinuity

open HigherDimLQGMetric HigherDimLQGMetric.DGZ
open HigherDimLFPP HigherDimLFPP.Perc
open HigherDimLFPP.DGZ (latPt cbox obox)

variable {d : ℕ}

/-! ### The uniform inputs from packet U4 -/

/-- U4's high-quantile Hölder bound (`holderTightAQShape_unif`) is `UHolderTightAQShape`. -/
theorem uHolderTightAQShape_holds (hd : 2 ≤ d) {κ : Rd d → ℝ} (hκ : IsLFPPKernel κ) :
    UHolderTightAQShape d κ :=
  holderTightAQShape_unif hd hκ

/-- U4's high-quantile distance to infinity (`distInfAQShape_unif`) is `UDistInfAQShape`. -/
theorem uDistInfAQShape_holds (hd : 2 ≤ d) {κ : Rd d → ℝ} (hκ : IsLFPPKernel κ) :
    UDistInfAQShape d κ :=
  distInfAQShape_unif hd hκ

/-- U4's positive crossings (`nondeg_cross_pos_unif`, every depth) at every high quantile. -/
theorem uCrossPosAt_holds (hd : 2 ≤ d) {κ : Rd d → ℝ} (hκ : IsLFPPKernel κ) {b μ : ℝ} (hb : 0 < b)
    (hμ : 0 < μ) :
    ∃ q₃ : ℝ≥0∞, 0 < q₃ ∧ q₃ < 1 ∧ ∀ q : ℝ≥0∞, q₃ ≤ q → q < 1 → UCrossPosAt d κ b μ q := by
  obtain ⟨q₃, hq₃0, hq₃1, hcross⟩ := nondeg_cross_pos_unif hd hκ hb hμ
  refine ⟨q₃, hq₃0, hq₃1, fun q hq hq1 r hr hrd => ?_⟩
  obtain ⟨c, hc, hcb⟩ := hcross q hq hq1 r hr hrd
  exact ⟨c, hc, 0, fun ξ hξ Ω _ P W H hH n _ => hcb ξ hξ Ω P W H hH n⟩

/-- **The uniform inputs hold** at the quantile `q = max(q₁, q₂, q₃, ½)` of U4's three high-quantile results, with
`β = μ/2`. -/
theorem uNondegInputs_holds (hd : 2 ≤ d) {κ : Rd d → ℝ} (hκ : IsLFPPKernel κ) : UNondegInputs d κ := by
  intro b μ hb hμ
  obtain ⟨q₁, -, hq₁1, hT⟩ := uHolderTightAQShape_holds hd hκ b μ hb hμ (μ / 2) (by positivity)
    (by linarith)
  obtain ⟨q₂, -, hq₂1, hI⟩ := uDistInfAQShape_holds hd hκ b μ hb hμ
  obtain ⟨q₃, -, hq₃1, hW⟩ := uCrossPosAt_holds hd hκ hb hμ
  have hhalf1 : (2⁻¹ : ℝ≥0∞) < 1 := ENNReal.inv_lt_one.2 ENNReal.one_lt_two
  set q : ℝ≥0∞ := max (max q₁ q₂) (max q₃ 2⁻¹) with hq
  have hq1 : q < 1 := max_lt (max_lt hq₁1 hq₂1) (max_lt hq₃1 hhalf1)
  have h1 : q₁ ≤ q := (le_max_left _ _).trans (le_max_left _ _)
  have h2 : q₂ ≤ q := (le_max_right _ _).trans (le_max_left _ _)
  have h3 : q₃ ≤ q := (le_max_left _ _).trans (le_max_right _ _)
  have hh : (2⁻¹ : ℝ≥0∞) ≤ q := (le_max_right _ _).trans (le_max_right _ _)
  exact ⟨q, hh, hq1, μ / 2, by positivity, hT q h1 hq1, hI q h2 hq1, hW q h3 hq1⟩

/-! ### The targets -/

/-- **U-nondegeneracy (A.3) at every depth** (Part D `d:prop-u64`(a); interface I9 `UNondegShape`), with no
hypothesis beyond `d ≥ 2` and an admissible kernel (ruling N28). -/
theorem uNondeg (hd : 2 ≤ d) {κ : Rd d → ℝ} (hκ : IsLFPPKernel κ) : UNondegShape d κ :=
  uNondeg_of_inputs hd hκ (uNondegInputs_holds hd hκ)

/-- **Comparability of quantiles (A.4)** (Part D `d:prop-u64`(b); interface I7 `UQuantCompShape`), with no
hypothesis beyond `d ≥ 2` and an admissible kernel (ruling N28). -/
theorem uQuantComp (hd : 2 ≤ d) {κ : Rd d → ℝ} (hκ : IsLFPPKernel κ) : UQuantCompShape d κ :=
  uQuantComp_of_inputs hd hκ (uNondegInputs_holds hd hκ)

/-- **The zero-one law along parameter arrays** (Part D `d:prop-u69`; NA3 R11; the sequence version of
`DGZ.nd_zeroOne_limitLaw`): for `b, μ > 0` there is `q₂ ∈ (0, 1)` such that for every `q ∈ [q₂, 1)`, every grid
radius and shell radius `r > 0`, every dyadic realization, every array `ξs k ∈ S(b, μ)` and depths `ns k → ∞`, and
every weak limit `μ₀` of the joint laws `nd_jointLaw (ξs k) q (ns k)` (the normalized whole-space metric and all
deleted-scale internal metrics on the cubical domains, normalized by `a^{ξs k}_{ns k}(q)`), the event
`{D̃(across B_{2r}(0) \ B_r(0)) > 0}` has `μ₀`-probability `0` or `1`. -/
theorem nd_zeroOne_limitLaw_seq (hd : 2 ≤ d) {κ : Rd d → ℝ} (hκ : IsLFPPKernel κ) {b μ : ℝ}
    (hb : 0 < b) (hμ : 0 < μ) :
    ∃ q₂ : ℝ≥0∞, 0 < q₂ ∧ q₂ < 1 ∧ ∀ q : ℝ≥0∞, q₂ ≤ q → q < 1 →
      ∀ rGrid r : ℝ, 0 < rGrid → 0 < r →
      ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) (W : WN d → Ω → ℝ) (H : ℕ → Rd d → Ω → ℝ)
        (hH : IsDyadicRealization κ P W H) (ξs : ℕ → ℝ), (∀ k, UHyp d κ b μ (ξs k)) →
        ∀ ns : ℕ → ℕ, Tendsto ns atTop atTop →
        ∀ μ₀ : ProbabilityMeasure (nd_Joint d rGrid),
          Tendsto
            (fun k => nd_jointLaw P hH.whiteNoise.isProbabilityMeasure H (ξs k) q rGrid (ns k))
            atTop (𝓝 μ₀) →
          (μ₀ : Measure (nd_Joint d rGrid)) (nd_positiveCrossEvent rGrid r) = 0 ∨
            (μ₀ : Measure (nd_Joint d rGrid)) (nd_positiveCrossEvent rGrid r) = 1 := by
  obtain ⟨q₂, hq₂0, hq₂1, hI⟩ := uDistInfAQShape_holds hd hκ b μ hb hμ
  refine ⟨q₂, hq₂0, hq₂1, ?_⟩
  intro q hq hq1 rGrid r hrGrid hr Ω _ P W H hH ξs hU ns hns μ₀ hlim
  have hq0 : 0 < q := hq₂0.trans_le hq
  have hIq : UDistInfAt d κ b μ q := hI q hq hq1
  have hbdd : ∀ r' : ℝ, 0 < r' →
      ∀ᵐ s ∂(μ₀ : Measure (nd_Joint d rGrid)), s ∈ nd_boundedZeroEvent rGrid r' := by
    intro r' hr'
    refine u5_ae_boundedZeroEvent hH hU hq0 hq1 rGrid r' hr' ns hlim fun θ hθ => ?_
    obtain ⟨R, hR, N, hN⟩ := hIq r' 1 θ hr' hθ
    refine ⟨R, hR, ?_⟩
    filter_upwards [hns.eventually (eventually_ge_atTop N)] with k hk
    simpa only [one_mul] using hN (ξs k) (hU k) Ω P W H hH (ns k) hk
  exact u5_zeroOne_limitLaw_of_bounded hH hU hq0 hq1 rGrid r hrGrid hr ns hns hlim (hbdd r hr)
    (hbdd (2 * r) (by positivity))

/-- **Law transfer of the normalized whole-space metric** between dyadic realizations: the law of
`a^ξ_n(q)⁻¹ D^ξ_n` on `C(ℝ^d × ℝ^d, ℝ)` does not depend on the realization. -/
theorem u5_map_normMetricC_eq {κ : Rd d → ℝ} {Ω Ω' : Type} [MeasurableSpace Ω] [MeasurableSpace Ω']
    {P : Measure Ω} {P' : Measure Ω'} {W : WN d → Ω → ℝ} {W' : WN d → Ω' → ℝ}
    {H : ℕ → Rd d → Ω → ℝ} {H' : ℕ → Rd d → Ω' → ℝ}
    (hH : IsDyadicRealization κ P W H) (hH' : IsDyadicRealization κ P' W' H') (ξ : ℝ) (q : ℝ≥0∞)
    (n : ℕ) :
    P.map (fun ω => normMetricC ξ (fun z => H n z ω) (aQ P H ξ n q)) =
      P'.map (fun ω => normMetricC ξ (fun z => H' n z ω) (aQ P' H' ξ n q)) := by
  rw [aQ_eq_of_isDyadicRealization hH hH' ξ n q]
  have hG : Measurable fun f : C(Rd d, ℝ) => normMetricC ξ (fun z => f z) (aQ P' H' ξ n q) :=
    measurable_normMetricC (H := fun z (f : C(Rd d, ℝ)) => f z) (fun f => f.continuous)
      (fun z => (continuous_eval_const z).measurable) ξ _
  exact (hH.band n).map_comp_eq_of_measurable (hH'.band n) hH.whiteNoise hH'.whiteNoise
    (G := fun φ => normMetricC ξ φ (aQ P' H' ξ n q)) hG

/-- **The zero-one law along parameter arrays, in the form of the blueprint** (Part D `d:prop-u69`): for `b, μ > 0`
there is `q₂ ∈ (0, 1)` such that for `q ∈ [q₂, 1)`, `r > 0`, every array `ξs k ∈ S(b, μ)` with depths `ns k → ∞` and
realizations `(P k, W k, H k)`: if the laws `ν k` of `D^{ξs k}_{ns k} / a^{ξs k}_{ns k}(q)` on `C(ℝ^d × ℝ^d, ℝ)`
converge to `ν₀`, then `ν₀[D̃(∂B_r(0), ∂B_{2r}(0)) > 0] ∈ {0, 1}`. Proof: transfer the laws to one realization,
extract a convergent subsequence of joint laws (tightness, (μ0)), identify `ν₀` with its first marginal, and apply
`nd_zeroOne_limitLaw_seq`'s argument. -/
theorem nd_zeroOne_limitLaw_seq_marginal (hd : 2 ≤ d) {κ : Rd d → ℝ} (hκ : IsLFPPKernel κ) {b μ : ℝ}
    (hb : 0 < b) (hμ : 0 < μ) :
    ∃ q₂ : ℝ≥0∞, 0 < q₂ ∧ q₂ < 1 ∧ ∀ q : ℝ≥0∞, q₂ ≤ q → q < 1 → ∀ r : ℝ, 0 < r →
      ∀ ξs : ℕ → ℝ, (∀ k, UHyp d κ b μ (ξs k)) → ∀ ns : ℕ → ℕ, Tendsto ns atTop atTop →
      ∀ (Ω : ℕ → Type) [∀ k, MeasurableSpace (Ω k)] (P : ∀ k, Measure (Ω k))
        (W : ∀ k, WN d → Ω k → ℝ) (H : ∀ k, ℕ → Rd d → Ω k → ℝ),
        (∀ k, IsDyadicRealization κ (P k) (W k) (H k)) →
      ∀ (ν : ℕ → ProbabilityMeasure C(Rd d × Rd d, ℝ)) (ν₀ : ProbabilityMeasure C(Rd d × Rd d, ℝ)),
        (∀ k, (ν k : Measure C(Rd d × Rd d, ℝ)) = (P k).map (fun ω =>
          normMetricC (ξs k) (fun z => H k (ns k) z ω) (aQ (P k) (H k) (ξs k) (ns k) q))) →
        Tendsto ν atTop (𝓝 ν₀) →
        (ν₀ : Measure C(Rd d × Rd d, ℝ)) {D | 0 < nd_crossPhi 0 (2 * r) r D} = 0 ∨
          (ν₀ : Measure C(Rd d × Rd d, ℝ)) {D | 0 < nd_crossPhi 0 (2 * r) r D} = 1 := by
  obtain ⟨q₁, hq₁0, hq₁1, hT⟩ := uHolderTightAQShape_holds hd hκ b μ hb hμ (μ / 2) (by positivity)
    (by linarith)
  obtain ⟨q₂, hq₂0, hq₂1, hI⟩ := uDistInfAQShape_holds hd hκ b μ hb hμ
  refine ⟨max q₁ q₂, hq₁0.trans_le (le_max_left _ _), max_lt hq₁1 hq₂1, ?_⟩
  intro q hq hq1 r hr ξs hU ns hns Ω _ P W H hH ν ν₀ hν hlim
  have hq0 : 0 < q := hq₁0.trans_le ((le_max_left _ _).trans hq)
  have hTq : UHolderTightAt d κ b μ q (μ / 2) := hT q ((le_max_left _ _).trans hq) hq1
  have hIq : UDistInfAt d κ b μ q := hI q ((le_max_right _ _).trans hq) hq1
  -- one realization
  obtain ⟨W₀, hW₀⟩ := exists_isWhiteNoise d
  obtain ⟨H₀, hH₀⟩ := exists_isDyadicRealization hκ hW₀
  set P₀ : Measure (ℕ → ℝ) := LQGDimension.ExistAsm.stdP with hP₀
  have hP₀p : IsProbabilityMeasure P₀ := hH₀.whiteNoise.isProbabilityMeasure
  -- the joint laws along a subsequence
  obtain ⟨μ₀, ψ, hψ, hjoint⟩ := u5_exists_joint_limit hκ hTq (by positivity) hq0 hq1 r P₀ W₀ H₀ hH₀
    ξs hU ns
  -- their first marginals are the given laws
  have hmarg : ∀ k, (nd_jointLaw P₀ hH₀.whiteNoise.isProbabilityMeasure H₀ (ξs k) q r (ns k)).map
      Prod.fst = ν k := by
    intro k
    apply Subtype.ext
    change (P₀.map (nd_jointSample P₀ H₀ (ξs k) q r (ns k))).map Prod.fst = (ν k : Measure _)
    rw [Measure.map_map measurable_fst (nd_measurable_jointSample hH₀ (ξs k) q r (ns k)), hν k,
      u5_map_normMetricC_eq (hH k) hH₀ (ξs k) q (ns k)]
    rfl
  have h1 : Tendsto (fun k => ν (ψ k)) atTop (𝓝 (μ₀.map Prod.fst)) := by
    have := ProbabilityMeasure.tendsto_map_of_tendsto_of_continuous _ _ hjoint continuous_fst
    simpa only [hmarg] using this
  have h2 : Tendsto (fun k => ν (ψ k)) atTop (𝓝 ν₀) := hlim.comp hψ.tendsto_atTop
  have heq : ν₀ = μ₀.map Prod.fst := tendsto_nhds_unique h2 h1
  -- the event in the first coordinate
  have hZ : (ν₀ : Measure C(Rd d × Rd d, ℝ)) {D | 0 < nd_crossPhi 0 (2 * r) r D} =
      (μ₀ : Measure (nd_Joint d r)) (nd_positiveCrossEvent r r) := by
    rw [heq, ProbabilityMeasure.toMeasure_map, Measure.map_apply measurable_fst
      (isOpen_lt continuous_const (nd_continuous_crossPhi 0 (2 * r) r)).measurableSet]
    rfl
  rw [hZ]
  -- the zero-one law along the subsequence
  let ξs' : ℕ → ℝ := fun k => ξs (ψ k)
  let ns' : ℕ → ℕ := fun k => ns (ψ k)
  have hU' : ∀ k, UHyp d κ b μ (ξs' k) := fun k => hU (ψ k)
  have hns' : Tendsto ns' atTop atTop := hns.comp hψ.tendsto_atTop
  have hlim' : Tendsto
      (fun k => nd_jointLaw P₀ hH₀.whiteNoise.isProbabilityMeasure H₀ (ξs' k) q r (ns' k))
      atTop (𝓝 μ₀) := hjoint
  have hbdd : ∀ r' : ℝ, 0 < r' →
      ∀ᵐ s ∂(μ₀ : Measure (nd_Joint d r)), s ∈ nd_boundedZeroEvent r r' := by
    intro r' hr'
    refine u5_ae_boundedZeroEvent hH₀ hU' hq0 hq1 r r' hr' ns' hlim' fun θ hθ => ?_
    obtain ⟨R, hR, N, hN⟩ := hIq r' 1 θ hr' hθ
    refine ⟨R, hR, ?_⟩
    filter_upwards [hns'.eventually (eventually_ge_atTop N)] with k hk
    simpa only [one_mul] using hN (ξs' k) (hU' k) (ℕ → ℝ) P₀ W₀ H₀ hH₀ (ns' k) hk
  exact u5_zeroOne_limitLaw_of_bounded hH₀ hU' hq0 hq1 r r hr hr ns' hns' hlim' (hbdd r hr)
    (hbdd (2 * r) (by positivity))

end HigherDimLQGContinuity
