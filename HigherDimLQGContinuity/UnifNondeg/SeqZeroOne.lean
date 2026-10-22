import HigherDimLQGContinuity.UnifNondeg.SeqLimit

/-!
# Sequence zero-one law, part 2: the zero-one argument along parameter arrays (packet U5)

Blueprint Part D, `d:prop-u69` (NA3 R11, N-M5; [8]-bp `r2:lem:68`, `r2:prop:69`). The component-free argument of the
sealed `DGZ.nd_zeroOne_limitLaw_of_bounded` (thickenings `E^j` of the zero sets by selected grid cells, the exit
decomposition, the identification of the selected-cell events with events of the deleted-scale local coordinates,
independence on separated domains, and the summation `μ(Z) ≤ μ(Z)²`) with the fixed `ξ` replaced by an array
`ξs k ∈ S(b, μ)`. Every deterministic step is reused verbatim from the sealed library; the probabilistic inputs are
the array versions of `UnifNondeg/SeqLimit.lean`.

Main result: `u5_zeroOne_limitLaw_of_bounded` — if the joint laws along `(ξs k, ns k)`, `ns k → ∞`, converge to
`μ₀` and the zero sets of `∂B_r(0)` and `∂B_{2r}(0)` are almost surely bounded under `μ₀`, then
`μ₀(D̃(across B_{2r}(0) \ B_r(0)) > 0) ∈ {0, 1}`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal

namespace HigherDimLQGContinuity

open HigherDimLQGMetric HigherDimLQGMetric.DGZ
open HigherDimLFPP HigherDimLFPP.Perc
open HigherDimLFPP.DGZ (latPt cbox obox)

variable {d : ℕ}

section ZeroOne

variable {κ : Rd d → ℝ} {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
  {W : WN d → Ω → ℝ} {H : ℕ → Rd d → Ω → ℝ} {b μ : ℝ} {ξs : ℕ → ℝ} {q : ℝ≥0∞}

/-- The exit inequality for every domain containing the inner sphere (port of `DGZ.nd_ae_exitForAll_of_tendsto`). -/
theorem u5_ae_exitForAll (hH : IsDyadicRealization κ P W H) (hU : ∀ k, UHyp d κ b μ (ξs k))
    (hq0 : 0 < q) (hq1 : q < 1) (rGrid r : ℝ) (hr : 0 < r) (ns : ℕ → ℕ)
    {μ₀ : ProbabilityMeasure (nd_Joint d rGrid)}
    (hlim : Tendsto
      (fun k => nd_jointLaw P hH.whiteNoise.isProbabilityMeasure H (ξs k) q rGrid (ns k))
      atTop (𝓝 μ₀)) :
    ∀ᵐ s ∂(μ₀ : Measure (nd_Joint d rGrid)),
      ∀ i : nd_DomainIndex d rGrid, lsph (0 : Rd d) r ⊆ nd_domain rGrid i →
        ∀ x : Rd d, x ∉ nd_domain rGrid i →
          nd_setInf (frontier (nd_domain rGrid i)) (lsph 0 r) s.1 ≤
            nd_pointSetInf (lsph 0 r) s.1 x := by
  have hd : 2 ≤ d := (hU 0).dim
  apply ae_all_iff.mpr
  intro i
  by_cases hsub : lsph (0 : Rd d) r ⊆ nd_domain rGrid i
  · let A : Set (nd_domain rGrid i) := {y | y.1 ∈ lsph (0 : Rd d) r}
    have hAimage : ((↑) '' A : Set (Rd d)) = lsph (0 : Rd d) r := by
      ext y
      constructor
      · rintro ⟨x, hx, rfl⟩
        exact hx
      · intro hy
        exact ⟨⟨y, hsub hy⟩, hy, rfl⟩
    have hAcompact : IsCompact A := by
      rw [Subtype.isCompact_iff, hAimage]
      exact tn_isCompact_lsph 0 r
    have hAne : A.Nonempty := by
      obtain ⟨y, hy⟩ := lsph_nonempty (by omega : 0 < d) 0 hr.le
      exact ⟨⟨y, hsub hy⟩, hy⟩
    have hae := u5_ae_allOutsideExitSet hH hU hq0 hq1 rGrid ns hlim i hAcompact hAne
    filter_upwards [hae] with s hs _ x hx
    have hxrel := Set.mem_iInter.mp hs ⟨x, hx⟩
    change s ∈ nd_outsideExitSet rGrid i A x at hxrel
    simpa only [nd_outsideExitSet, Set.mem_ofPred_eq, hAimage,
      ← nd_pointSetInf_eq_setInf] using hxrel
  · exact Filter.Eventually.of_forall fun _s hsub' => False.elim (hsub hsub')

/-- The thickenings of the zero set are connected (port of `DGZ.nd_ae_isConnected_thickening_of_tendsto`). -/
theorem u5_ae_isConnected_thickening (hH : IsDyadicRealization κ P W H)
    (hU : ∀ k, UHyp d κ b μ (ξs k)) (hq0 : 0 < q) (hq1 : q < 1)
    (rGrid r : ℝ) (hrGrid : 0 < rGrid) (hr : 0 < r) (j : ℕ) (ns : ℕ → ℕ)
    {μ₀ : ProbabilityMeasure (nd_Joint d rGrid)}
    (hlim : Tendsto
      (fun k => nd_jointLaw P hH.whiteNoise.isProbabilityMeasure H (ξs k) q rGrid (ns k))
      atTop (𝓝 μ₀))
    (hbounded : ∀ᵐ s ∂(μ₀ : Measure (nd_Joint d rGrid)), s ∈ nd_boundedZeroEvent rGrid r) :
    ∀ᵐ s ∂(μ₀ : Measure (nd_Joint d rGrid)), IsConnected (nd_thickening rGrid r j s) := by
  have hpseudo := u5_ae_pseudoSet hH hU hq0 hq1 rGrid ns hlim
  have hexit := u5_ae_exitForAll hH hU hq0 hq1 rGrid r hr ns hlim
  filter_upwards [hpseudo, hbounded, hexit] with s hs hbound hexit'
  let S : Finset (Zd d) :=
    (nd_selectedCell_finite hrGrid r j s (nd_zeroSet_isBounded_of_event hbound)).toFinset
  have hsel : s ∈ nd_selectedEq rGrid r j S := by
    intro z
    simp only [S, Set.Finite.mem_toFinset]
    rfl
  exact nd_isConnected_thickening_of_exit (hU 0).dim hrGrid hr j s hs S hsel hexit'

/-- The collar relation for every domain containing the inner sphere (port of
`DGZ.nd_ae_collarForAll_of_tendsto`). -/
theorem u5_ae_collarForAll (hH : IsDyadicRealization κ P W H) (hU : ∀ k, UHyp d κ b μ (ξs k))
    (hq0 : 0 < q) (hq1 : q < 1) (rGrid r : ℝ) (hrGrid : 0 < rGrid) (hr : 0 < r) (ns : ℕ → ℕ)
    {μ₀ : ProbabilityMeasure (nd_Joint d rGrid)}
    (hlim : Tendsto
      (fun k => nd_jointLaw P hH.whiteNoise.isProbabilityMeasure H (ξs k) q rGrid (ns k))
      atTop (𝓝 μ₀)) :
    ∀ᵐ s ∂(μ₀ : Measure (nd_Joint d rGrid)),
      ∀ i : nd_DomainIndex d rGrid, lsph (0 : Rd d) r ⊆ nd_domain rGrid i →
        ∃ c : ℝ, 0 < c ∧ c < nd_gridRadius rGrid i.1.1 ∧
          s ∈ nd_collarSet rGrid i (nd_interiorDist i) c
            (frontier (nd_domain rGrid i)) (nd_shellInDomain r i) := by
  apply ae_all_iff.mpr
  intro i
  by_cases hsub : lsph (0 : Rd d) r ⊆ nd_domain rGrid i
  · have hd : 0 < d := by have := (hU 0).dim; omega
    obtain ⟨c, hc, hcρ, hcA⟩ := nd_exists_shellCollarLevel hd hrGrid hr i hsub
    have hg : Continuous (nd_interiorDist i) := nd_continuous_interiorDist i
    have hgU : ∀ z, z ∉ nd_domain rGrid i → nd_interiorDist i z ≤ 0 := by
      intro z hz
      exact le_of_eq (nd_interiorDist_eq_zero_of_not_mem i hz)
    have hFcomp : IsCompact (frontier (nd_domain rGrid i)) := nd_isCompact_frontier_domain rGrid i
    have hAne : (nd_shellInDomain r i).Nonempty := nd_shellInDomain_nonempty hd hr.le i hsub
    have hFne : (frontier (nd_domain rGrid i)).Nonempty :=
      nd_frontier_domain_nonempty hd rGrid i ⟨hAne.some.1, hAne.some.2⟩
    have hAcomp : IsCompact (nd_shellInDomain r i) := nd_isCompact_shellInDomain r i hsub
    have hgF : ∀ z ∈ frontier (nd_domain rGrid i), nd_interiorDist i z ≤ c := by
      intro z hz
      rw [nd_interiorDist_frontier_zero i hz]
      exact hc.le
    have hgA : ∀ z ∈ ((↑) '' nd_shellInDomain r i : Set (Rd d)), c ≤ nd_interiorDist i z := by
      rintro z ⟨x, hx, rfl⟩
      exact hcA x hx
    have hae := u5_ae_collarSet hH hU hq0 hq1 rGrid ns hlim i hg hc hgU hFcomp hFne hAcomp hAne hgF hgA
    filter_upwards [hae] with s hs _
    exact ⟨c, hc, hcρ, hs⟩
  · exact Filter.Eventually.of_forall fun _s hsub' => False.elim (hsub hsub')

/-- The selected-cell events agree almost surely with events of one deleted-scale local coordinate (port of
`DGZ.nd_ae_selectedEq_iff_localSelectedEq_of_tendsto`; the claims (A)–(C) of [8]-bp `r2:prop:69`). -/
theorem u5_ae_selectedEq_iff_localSelectedEq (hH : IsDyadicRealization κ P W H)
    (hU : ∀ k, UHyp d κ b μ (ξs k)) (hq0 : 0 < q) (hq1 : q < 1)
    (rGrid r : ℝ) (hrGrid : 0 < rGrid) (hr : 0 < r) (ns : ℕ → ℕ)
    {μ₀ : ProbabilityMeasure (nd_Joint d rGrid)}
    (hlim : Tendsto
      (fun k => nd_jointLaw P hH.whiteNoise.isProbabilityMeasure H (ξs k) q rGrid (ns k))
      atTop (𝓝 μ₀)) (i : nd_DomainIndex d rGrid)
    (hsub : lsph (0 : Rd d) r ⊆ nd_domain rGrid i) (m : ℕ) :
    ∀ᵐ s ∂(μ₀ : Measure (nd_Joint d rGrid)),
      (s ∈ nd_selectedEq rGrid r i.1.1 i.1.2 ↔
        s ∈ nd_localSelectedEq i (nd_shellInDomain r i) m i.1.1 i.1.2) := by
  have hd : 0 < d := by have := (hU 0).dim; omega
  have hAcomp := nd_isCompact_shellInDomain r i hsub
  have hAne := nd_shellInDomain_nonempty hd hr.le i hsub
  have hpseudo := u5_ae_pseudoSet hH hU hq0 hq1 rGrid ns hlim
  have hLE := u5_ae_globalLE hH hU hq0 hq1 rGrid ns hlim i
  have hNN0 := u5_ae_nonnegLocalSet hH hU hq0 hq1 rGrid ns hlim i 0
  have hNNm := u5_ae_nonnegLocalSet hH hU hq0 hq1 rGrid ns hlim i m
  have hdiag := u5_ae_localDiagSet hH rGrid ns hlim i 0
  have hinside := u5_ae_allInsideExitSet hH hU hq0 hq1 rGrid ns hlim i hAcomp hAne
  have houtside := u5_ae_allOutsideExitSet hH hU hq0 hq1 rGrid ns hlim i hAcomp hAne
  have hcomp := u5_ae_finiteCompSet hH hU hq0 hq1 rGrid ns hlim i m
  have hcollar := u5_ae_collarForAll hH hU hq0 hq1 rGrid r hrGrid hr ns hlim
  filter_upwards [hpseudo, hLE, hNN0, hNNm, hdiag, hinside, houtside, hcomp, hcollar] with s hs hsLE
    hsNN0 hsNNm hsdiag hsinside hsoutside hscomp hscollar
  obtain ⟨c, hc, hcρ, hsC⟩ := hscollar i hsub
  constructor
  · intro hsel
    have hloc := nd_mem_localSelectedEq_of_globalSelectedEq hd hrGrid hr i s hs hsLE hsNN0 hsinside hsel
    exact (nd_localSelectedEq_iff_of_finiteCompSet hd hr.le i hsub m i.1.1 i.1.2
      s hscomp hsNN0 hsNNm).1 hloc
  · intro hloc
    have hloc0 := (nd_localSelectedEq_iff_of_finiteCompSet hd hr.le i hsub
      m i.1.1 i.1.2 s hscomp hsNN0 hsNNm).2 hloc
    exact nd_mem_globalSelectedEq_of_localSelectedEq hd hrGrid hr i hsub s
      hs hsLE hsNN0 hsdiag hsinside hsoutside hc hcρ hsC hloc0

/-- Independence of selected-cell events on separated domains in array limits (port of
`DGZ.nd_selectedEq_indep_of_tendsto`). -/
theorem u5_selectedEq_indep (hH : IsDyadicRealization κ P W H) (hU : ∀ k, UHyp d κ b μ (ξs k))
    (hq0 : 0 < q) (hq1 : q < 1) (rGrid r₁ r₂ : ℝ) (hrGrid : 0 < rGrid) (hr₁ : 0 < r₁) (hr₂ : 0 < r₂)
    (ns : ℕ → ℕ) (hns : Tendsto ns atTop atTop) {μ₀ : ProbabilityMeasure (nd_Joint d rGrid)}
    (hlim : Tendsto
      (fun k => nd_jointLaw P hH.whiteNoise.isProbabilityMeasure H (ξs k) q rGrid (ns k))
      atTop (𝓝 μ₀))
    (i₁ i₂ : nd_DomainIndex d rGrid)
    (hsub₁ : lsph (0 : Rd d) r₁ ⊆ nd_domain rGrid i₁)
    (hsub₂ : lsph (0 : Rd d) r₂ ⊆ nd_domain rGrid i₂)
    (m : ℕ) (ρ : ℝ) (hρ : ∀ y, ρ ≤ ‖y‖ → κ y = 0)
    (hsep : ∀ z ∈ nd_domain rGrid i₁, ∀ w ∈ nd_domain rGrid i₂, 2 * ρ * ((2 : ℝ)⁻¹ ^ m) < ‖z - w‖) :
    (μ₀ : Measure (nd_Joint d rGrid))
      (nd_selectedEq rGrid r₁ i₁.1.1 i₁.1.2 ∩ nd_selectedEq rGrid r₂ i₂.1.1 i₂.1.2) =
      (μ₀ : Measure (nd_Joint d rGrid)) (nd_selectedEq rGrid r₁ i₁.1.1 i₁.1.2) *
      (μ₀ : Measure (nd_Joint d rGrid)) (nd_selectedEq rGrid r₂ i₂.1.1 i₂.1.2) := by
  let A₁ := nd_selectedEq rGrid r₁ i₁.1.1 i₁.1.2
  let A₂ := nd_selectedEq rGrid r₂ i₂.1.1 i₂.1.2
  let B₁ := nd_localSelectedEqC i₁ (nd_shellInDomain r₁ i₁) m i₁.1.1 i₁.1.2
  let B₂ := nd_localSelectedEqC i₂ (nd_shellInDomain r₂ i₂) m i₂.1.1 i₂.1.2
  let f₁ : nd_Joint d rGrid → C(nd_domain rGrid i₁ × nd_domain rGrid i₁, ℝ) := fun s => s.2 (i₁, m)
  let f₂ : nd_Joint d rGrid → C(nd_domain rGrid i₂ × nd_domain rGrid i₂, ℝ) := fun s => s.2 (i₂, m)
  have hB₁ : MeasurableSet B₁ :=
    nd_measurableSet_localSelectedEqC i₁ (nd_isCompact_shellInDomain r₁ i₁ hsub₁) m i₁.1.1 i₁.1.2
  have hB₂ : MeasurableSet B₂ :=
    nd_measurableSet_localSelectedEqC i₂ (nd_isCompact_shellInDomain r₂ i₂ hsub₂) m i₂.1.1 i₂.1.2
  have heq₁ : A₁ =ᵐ[(μ₀ : Measure (nd_Joint d rGrid))] f₁ ⁻¹' B₁ := by
    filter_upwards [u5_ae_selectedEq_iff_localSelectedEq hH hU hq0 hq1 rGrid r₁ hrGrid hr₁ ns hlim
      i₁ hsub₁ m] with s hs
    exact propext hs
  have heq₂ : A₂ =ᵐ[(μ₀ : Measure (nd_Joint d rGrid))] f₂ ⁻¹' B₂ := by
    filter_upwards [u5_ae_selectedEq_iff_localSelectedEq hH hU hq0 hq1 rGrid r₂ hrGrid hr₂ ns hlim
      i₂ hsub₂ m] with s hs
    exact propext hs
  have hind := u5_indepFun_jointLimit hH hU q rGrid ns hns hlim m i₁ i₂ ρ hρ hsep
  calc
    (μ₀ : Measure (nd_Joint d rGrid)) (A₁ ∩ A₂) =
        (μ₀ : Measure (nd_Joint d rGrid)) ((f₁ ⁻¹' B₁) ∩ (f₂ ⁻¹' B₂)) :=
      measure_congr (heq₁.inter heq₂)
    _ = (μ₀ : Measure (nd_Joint d rGrid)) (f₁ ⁻¹' B₁) *
          (μ₀ : Measure (nd_Joint d rGrid)) (f₂ ⁻¹' B₂) :=
      hind.measure_inter_preimage_eq_mul B₁ B₂ hB₁ hB₂
    _ = (μ₀ : Measure (nd_Joint d rGrid)) A₁ * (μ₀ : Measure (nd_Joint d rGrid)) A₂ := by
      rw [measure_congr heq₁, measure_congr heq₂]

/-- Independence on positively separated domains (port of `DGZ.nd_selectedEq_indep_of_domainSeparated`). -/
theorem u5_selectedEq_indep_of_domainSeparated (hH : IsDyadicRealization κ P W H)
    (hU : ∀ k, UHyp d κ b μ (ξs k)) (hq0 : 0 < q) (hq1 : q < 1)
    (rGrid r₁ r₂ : ℝ) (hrGrid : 0 < rGrid) (hr₁ : 0 < r₁) (hr₂ : 0 < r₂)
    (ns : ℕ → ℕ) (hns : Tendsto ns atTop atTop) {μ₀ : ProbabilityMeasure (nd_Joint d rGrid)}
    (hlim : Tendsto
      (fun k => nd_jointLaw P hH.whiteNoise.isProbabilityMeasure H (ξs k) q rGrid (ns k))
      atTop (𝓝 μ₀))
    (i₁ i₂ : nd_DomainIndex d rGrid)
    (hsub₁ : lsph (0 : Rd d) r₁ ⊆ nd_domain rGrid i₁)
    (hsub₂ : lsph (0 : Rd d) r₂ ⊆ nd_domain rGrid i₂)
    (hsep : nd_domainSeparated rGrid i₁ i₂) :
    (μ₀ : Measure (nd_Joint d rGrid))
      (nd_selectedEq rGrid r₁ i₁.1.1 i₁.1.2 ∩ nd_selectedEq rGrid r₂ i₂.1.1 i₂.1.2) =
      (μ₀ : Measure (nd_Joint d rGrid)) (nd_selectedEq rGrid r₁ i₁.1.1 i₁.1.2) *
      (μ₀ : Measure (nd_Joint d rGrid)) (nd_selectedEq rGrid r₂ i₂.1.1 i₂.1.2) := by
  obtain ⟨δ, hδ, hgap⟩ := hsep
  obtain ⟨ρ, hρ0, hρ⟩ := (hU 0).base.kernel.exists_radius
  have hpow : Tendsto (fun m : ℕ => 2 * ρ * ((2 : ℝ)⁻¹ ^ m)) atTop (𝓝 0) := by
    simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one
      (by norm_num : (0 : ℝ) ≤ (2 : ℝ)⁻¹) (by norm_num : (2 : ℝ)⁻¹ < 1)).const_mul (2 * ρ)
  obtain ⟨m, hm⟩ := (hpow.eventually (eventually_lt_nhds hδ)).exists
  apply u5_selectedEq_indep hH hU hq0 hq1 rGrid r₁ r₂ hrGrid hr₁ hr₂ ns hns hlim i₁ i₂ hsub₁ hsub₂ m ρ hρ
  intro z hz w hw
  exact hm.trans_le (hgap z hz w hw)

/-- A selected domain at every grid level (port of `DGZ.nd_ae_exists_selectedIndex_of_tendsto`). -/
theorem u5_ae_exists_selectedIndex (hH : IsDyadicRealization κ P W H)
    (hU : ∀ k, UHyp d κ b μ (ξs k)) (hq0 : 0 < q) (hq1 : q < 1)
    (rGrid r : ℝ) (hrGrid : 0 < rGrid) (hr : 0 < r) (ns : ℕ → ℕ)
    {μ₀ : ProbabilityMeasure (nd_Joint d rGrid)}
    (hlim : Tendsto
      (fun k => nd_jointLaw P hH.whiteNoise.isProbabilityMeasure H (ξs k) q rGrid (ns k))
      atTop (𝓝 μ₀))
    (hbounded : ∀ᵐ s ∂(μ₀ : Measure (nd_Joint d rGrid)), s ∈ nd_boundedZeroEvent rGrid r) :
    ∀ᵐ s ∂(μ₀ : Measure (nd_Joint d rGrid)),
      ∀ j : ℕ, ∃ i : nd_DomainIndex d rGrid, i.1.1 = j ∧ s ∈ nd_selectedEq rGrid r i.1.1 i.1.2 := by
  apply ae_all_iff.mpr
  intro j
  have hconn := u5_ae_isConnected_thickening hH hU hq0 hq1 rGrid r hrGrid hr j ns hlim hbounded
  filter_upwards [hbounded, hconn] with s hsB hsC
  exact nd_exists_selectedIndex_of_bounded_connected hrGrid j s hsB hsC

/-- Factorization of the good-code events on separated domains (port of `DGZ.nd_goodCode_factor_of_separated`). -/
theorem u5_goodCode_factor_of_separated (hH : IsDyadicRealization κ P W H)
    (hU : ∀ k, UHyp d κ b μ (ξs k)) (hq0 : 0 < q) (hq1 : q < 1)
    (rGrid r : ℝ) (hrGrid : 0 < rGrid) (hr : 0 < r) (ns : ℕ → ℕ) (hns : Tendsto ns atTop atTop)
    {μ₀ : ProbabilityMeasure (nd_Joint d rGrid)}
    (hlim : Tendsto
      (fun k => nd_jointLaw P hH.whiteNoise.isProbabilityMeasure H (ξs k) q rGrid (ns k))
      atTop (𝓝 μ₀)) (j : ℕ)
    (i : nd_GoodIndex (d := d) rGrid r (2 * r) j) (k : nd_GoodIndex (d := d) rGrid (2 * r) r j)
    (hsep : nd_domainSeparated rGrid i.1 k.1) :
    (μ₀ : Measure (nd_Joint d rGrid))
      (nd_goodCodeEvent rGrid r (2 * r) j i ∩ nd_goodCodeEvent rGrid (2 * r) r j k) =
      (μ₀ : Measure (nd_Joint d rGrid)) (nd_goodCodeEvent rGrid r (2 * r) j i) *
      (μ₀ : Measure (nd_Joint d rGrid)) (nd_goodCodeEvent rGrid (2 * r) r j k) :=
  u5_selectedEq_indep_of_domainSeparated hH hU hq0 hq1 rGrid r (2 * r) hrGrid hr
    (mul_pos (by norm_num) hr) ns hns hlim i.1 k.1 i.2.2.1 k.2.2.1 hsep

/-- `μ₀(separated pair event) ≤ μ₀(Z)²` (port of `DGZ.nd_sepPairEvent_measure_le_square`). -/
theorem u5_sepPairEvent_measure_le_square (hH : IsDyadicRealization κ P W H)
    (hU : ∀ k, UHyp d κ b μ (ξs k)) (hq0 : 0 < q) (hq1 : q < 1)
    (rGrid r : ℝ) (hrGrid : 0 < rGrid) (hr : 0 < r) (ns : ℕ → ℕ) (hns : Tendsto ns atTop atTop)
    {μ₀ : ProbabilityMeasure (nd_Joint d rGrid)}
    (hlim : Tendsto
      (fun k => nd_jointLaw P hH.whiteNoise.isProbabilityMeasure H (ξs k) q rGrid (ns k))
      atTop (𝓝 μ₀)) (j : ℕ) :
    (μ₀ : Measure (nd_Joint d rGrid)) (nd_sepPairEvent rGrid r j) ≤
      (μ₀ : Measure (nd_Joint d rGrid)) (nd_positiveCrossEvent rGrid r) *
        (μ₀ : Measure (nd_Joint d rGrid)) (nd_positiveCrossEvent rGrid r) := by
  classical
  let ν : Measure (nd_Joint d rGrid) := μ₀
  let Z := nd_positiveCrossEvent (d := d) rGrid r
  let A (i : nd_GoodIndex (d := d) rGrid r (2 * r) j) := nd_goodCodeEvent rGrid r (2 * r) j i
  let B (i : nd_GoodIndex (d := d) rGrid (2 * r) r j) := nd_goodCodeEvent rGrid (2 * r) r j i
  let sep (i : nd_GoodIndex (d := d) rGrid r (2 * r) j) (k : nd_GoodIndex (d := d) rGrid (2 * r) r j) :=
    nd_domainSeparated rGrid i.1 k.1
  have hd : 0 < d := by have := (hU 0).dim; omega
  have hpseudo := u5_ae_pseudoSet hH hU hq0 hq1 rGrid ns hlim
  have hA : (∑' i, ν (A i)) ≤ ν Z := nd_tsum_goodCode_first_le_cross hd hrGrid hr j ν hpseudo
  have hB : (∑' i, ν (B i)) ≤ ν Z := nd_tsum_goodCode_second_le_cross hd hrGrid hr j ν hpseudo
  have hfac (i : nd_GoodIndex (d := d) rGrid r (2 * r) j)
      (k : nd_GoodIndex (d := d) rGrid (2 * r) r j) (hsep : sep i k) :
      ν (A i ∩ B k) = ν (A i) * ν (B k) :=
    u5_goodCode_factor_of_separated hH hU hq0 hq1 rGrid r hrGrid hr ns hns hlim j i k hsep
  rw [nd_sepPairEvent_eq]
  exact nd_measure_pairUnion_le_mul ν A B sep hfac hA hB

/-- **The zero-one law along a parameter array, for bounded zero sets** (port of
`DGZ.nd_zeroOne_limitLaw_of_bounded`; blueprint `d:prop-u69`): if the joint laws along `(ξs k, ns k)`,
`ξs k ∈ S(b, μ)`, `ns k → ∞`, converge to `μ₀` and the zero sets of `∂B_r(0)` and `∂B_{2r}(0)` are almost surely
bounded, then `μ₀(Z) ∈ {0, 1}` for `Z = {D̃(across B_{2r}(0) \ B_r(0)) > 0}`. -/
theorem u5_zeroOne_limitLaw_of_bounded (hH : IsDyadicRealization κ P W H)
    (hU : ∀ k, UHyp d κ b μ (ξs k)) (hq0 : 0 < q) (hq1 : q < 1)
    (rGrid r : ℝ) (hrGrid : 0 < rGrid) (hr : 0 < r) (ns : ℕ → ℕ) (hns : Tendsto ns atTop atTop)
    {μ₀ : ProbabilityMeasure (nd_Joint d rGrid)}
    (hlim : Tendsto
      (fun k => nd_jointLaw P hH.whiteNoise.isProbabilityMeasure H (ξs k) q rGrid (ns k))
      atTop (𝓝 μ₀))
    (hb₁ : ∀ᵐ s ∂(μ₀ : Measure (nd_Joint d rGrid)), s ∈ nd_boundedZeroEvent rGrid r)
    (hb₂ : ∀ᵐ s ∂(μ₀ : Measure (nd_Joint d rGrid)), s ∈ nd_boundedZeroEvent rGrid (2 * r)) :
    (μ₀ : Measure (nd_Joint d rGrid)) (nd_positiveCrossEvent rGrid r) = 0 ∨
      (μ₀ : Measure (nd_Joint d rGrid)) (nd_positiveCrossEvent rGrid r) = 1 := by
  let ν : Measure (nd_Joint d rGrid) := μ₀
  let Z := nd_positiveCrossEvent (d := d) rGrid r
  have hd : 0 < d := by have := (hU 0).dim; omega
  have hpseudo := u5_ae_pseudoSet hH hU hq0 hq1 rGrid ns hlim
  have hi₁ := u5_ae_exists_selectedIndex hH hU hq0 hq1 rGrid r hrGrid hr ns hlim hb₁
  have hi₂ := u5_ae_exists_selectedIndex hH hU hq0 hq1 rGrid (2 * r) hrGrid
    (mul_pos (by norm_num) hr) ns hlim hb₂
  have hev : ∀ᵐ s ∂ν, s ∈ Z → ∀ᶠ j : ℕ in atTop, s ∈ nd_sepPairEvent rGrid r j := by
    filter_upwards [hpseudo, hb₁, hb₂, hi₁, hi₂] with s hs hsB₁ hsB₂ hsI₁ hsI₂ hsZ
    exact nd_eventually_mem_sepPairEvent hd hrGrid hr s hs hsB₁ hsB₂ hsI₁ hsI₂ hsZ
  have hsq : ν Z ≤ ν Z * ν Z :=
    nd_measure_le_of_ae_eventually ν Z (nd_sepPairEvent rGrid r) (ν Z * ν Z) hev
      (fun j => u5_sepPairEvent_measure_le_square hH hU hq0 hq1 rGrid r hrGrid hr ns hns hlim j)
  have hle : ν Z ≤ 1 := prob_le_one
  by_cases hz : ν Z = 0
  · exact Or.inl hz
  · right
    have hfin : ν Z ≠ ∞ := ne_top_of_le_ne_top (by simp) hle
    have hone : 1 ≤ ν Z := (ENNReal.mul_le_mul_iff_left hz hfin).mp (by simpa using hsq)
    exact le_antisymm hle hone

end ZeroOne

end HigherDimLQGContinuity
