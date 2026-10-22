import HigherDimLQGMetric.DGZ.NondegZeroOneCore
import HigherDimLQGContinuity.Core.Interfaces
import HigherDimLQGContinuity.UnifBase.Hyp

/-!
# Sequence zero-one law, part 1: closed relations along parameter arrays (packet U5)

Blueprint Part D, `d:prop-u69` (NA3 R11, §2.8, N-M5; [8]-bp `r2:lem:68`, `r2:prop:69`). The sealed fixed-`ξ` proof
of DGZ Lemma 6.9 (`HigherDimLQGMetric.DGZ.Nondeg*`) passes closed relations of the prelimit joint states
`nd_jointSample P H ξ q r n` to every weak limit of their laws `nd_jointLaw P _ H ξ q r (ns k)`. Here the fixed `ξ`
is replaced by an array `ξs k ∈ S(b, μ)` (`UHyp d κ b μ (ξs k)`), with one dyadic realization `(P, W, H)`:

* `u5_ae_mem_of_forall`: a closed relation that holds almost surely at every level `(ξs k, ns k)` holds almost
  surely under every limit `μ₀` of the joint laws (closed-set portmanteau).
* Ports of the limit statements of the sealed chain, each from the sealed per-level statement at `ξ := ξs k`
  (step (μ1), (μ3) of NA3 R11: deterministic, valid for every `k`): `u5_ae_globalLE`, `u5_ae_nonnegLocalSet`,
  `u5_ae_insideExitSet`, `u5_ae_outsideExitSet`, `u5_ae_allInsideExitSet`, `u5_ae_allOutsideExitSet`,
  `u5_ae_collarSet`, `u5_ae_globalOutsideBarrierSet`, `u5_ae_pseudoSet`, `u5_ae_localDiagSet`.
* Step (μ2), uniform in `ξ ≤ b`: `u5_prelimit_compSet_prob` (the comparison constant `e^{b L}`, `L` a `ξ`-free
  quantile bound of `sup |h_m|`), `u5_limit_compSet_prob`, `u5_ae_finiteCompSet`.
* Step (μ4): `u5_indepFun_jointLimit` (independence of deleted-scale internal metrics on far domains holds at every
  level, and limits of product laws are product laws).
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

section Transfer

variable {κ : Rd d → ℝ} {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
  {W : WN d → Ω → ℝ} {H : ℕ → Rd d → Ω → ℝ}

/-- **Closed-set transfer along a parameter array**: a closed relation of the joint state that holds almost surely
at every level `(ξs k, ns k)` holds almost surely for every weak limit of the joint laws. -/
theorem u5_ae_mem_of_forall (hH : IsDyadicRealization κ P W H) {q : ℝ≥0∞} {rGrid : ℝ}
    {ξs : ℕ → ℝ} {ns : ℕ → ℕ} {μ₀ : ProbabilityMeasure (nd_Joint d rGrid)}
    (hlim : Tendsto
      (fun k => nd_jointLaw P hH.whiteNoise.isProbabilityMeasure H (ξs k) q rGrid (ns k))
      atTop (𝓝 μ₀))
    {C : Set (nd_Joint d rGrid)} (hC : IsClosed C)
    (hk : ∀ k, ∀ᵐ ω ∂P, nd_jointSample P H (ξs k) q rGrid (ns k) ω ∈ C) :
    ∀ᵐ s ∂(μ₀ : Measure (nd_Joint d rGrid)), s ∈ C := by
  apply LQGMetric.DFGPS.ae_mem_of_isClosed_of_forall hlim hC
  intro k
  change (P.map (nd_jointSample P H (ξs k) q rGrid (ns k))) C = 1
  rw [Measure.map_apply (nd_measurable_jointSample hH (ξs k) q rGrid (ns k)) hC.measurableSet]
  exact (measure_congr (eventuallyEqSet_univ.2 (hk k))).trans
    (@IsProbabilityMeasure.measure_univ Ω _ P hH.whiteNoise.isProbabilityMeasure)

/-- The pointwise form of `u5_ae_mem_of_forall`. -/
theorem u5_ae_mem_of_forall_pointwise (hH : IsDyadicRealization κ P W H) {q : ℝ≥0∞} {rGrid : ℝ}
    {ξs : ℕ → ℝ} {ns : ℕ → ℕ} {μ₀ : ProbabilityMeasure (nd_Joint d rGrid)}
    (hlim : Tendsto
      (fun k => nd_jointLaw P hH.whiteNoise.isProbabilityMeasure H (ξs k) q rGrid (ns k))
      atTop (𝓝 μ₀))
    {C : Set (nd_Joint d rGrid)} (hC : IsClosed C)
    (hk : ∀ k ω, nd_jointSample P H (ξs k) q rGrid (ns k) ω ∈ C) :
    ∀ᵐ s ∂(μ₀ : Measure (nd_Joint d rGrid)), s ∈ C :=
  u5_ae_mem_of_forall hH hlim hC fun k => Filter.Eventually.of_forall (hk k)

/-- **Closed-set lower bounds along a parameter array** (portmanteau): if eventually every level gives the closed
set probability at least `t`, so does every weak limit. -/
theorem u5_le_measure_of_eventually (hH : IsDyadicRealization κ P W H) {q : ℝ≥0∞} {rGrid : ℝ}
    {ξs : ℕ → ℝ} {ns : ℕ → ℕ} {μ₀ : ProbabilityMeasure (nd_Joint d rGrid)}
    (hlim : Tendsto
      (fun k => nd_jointLaw P hH.whiteNoise.isProbabilityMeasure H (ξs k) q rGrid (ns k))
      atTop (𝓝 μ₀))
    {C : Set (nd_Joint d rGrid)} (hC : IsClosed C) {t : ℝ≥0∞}
    (hk : ∀ᶠ k in atTop, t ≤ P (nd_jointSample P H (ξs k) q rGrid (ns k) ⁻¹' C)) :
    t ≤ (μ₀ : Measure (nd_Joint d rGrid)) C := by
  apply LQGMetric.DFGPS.le_measure_of_isClosed hlim hC
  filter_upwards [hk] with k hk
  change t ≤ (P.map (nd_jointSample P H (ξs k) q rGrid (ns k))) C
  rwa [Measure.map_apply (nd_measurable_jointSample hH (ξs k) q rGrid (ns k)) hC.measurableSet]

end Transfer

/-! ### The closed relations of the sealed chain, along arrays (steps (μ1), (μ3)) -/

section Relations

variable {κ : Rd d → ℝ} {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
  {W : WN d → Ω → ℝ} {H : ℕ → Rd d → Ω → ℝ} {b μ : ℝ} {ξs : ℕ → ℝ} {q : ℝ≥0∞}

/-- `D̃(x, y) ≤ D̃_{0,U}(x, y)` in every array limit (port of `DGZ.nd_ae_globalLE_of_tendsto`). -/
theorem u5_ae_globalLE (hH : IsDyadicRealization κ P W H) (hU : ∀ k, UHyp d κ b μ (ξs k))
    (hq0 : 0 < q) (hq1 : q < 1) (r : ℝ) (ns : ℕ → ℕ) {μ₀ : ProbabilityMeasure (nd_Joint d r)}
    (hlim : Tendsto
      (fun k => nd_jointLaw P hH.whiteNoise.isProbabilityMeasure H (ξs k) q r (ns k))
      atTop (𝓝 μ₀)) (i : nd_DomainIndex d r) :
    ∀ᵐ x ∂(μ₀ : Measure (nd_Joint d r)), x ∈ nd_globalLE r i :=
  u5_ae_mem_of_forall hH hlim (nd_isClosed_globalLE r i) fun k =>
    nd_jointSample_mem_globalLE (hU k).base hH hq0 hq1 r (ns k) i

/-- Nonnegativity of the local coordinates in every array limit. -/
theorem u5_ae_nonnegLocalSet (hH : IsDyadicRealization κ P W H) (hU : ∀ k, UHyp d κ b μ (ξs k))
    (hq0 : 0 < q) (hq1 : q < 1) (r : ℝ) (ns : ℕ → ℕ) {μ₀ : ProbabilityMeasure (nd_Joint d r)}
    (hlim : Tendsto
      (fun k => nd_jointLaw P hH.whiteNoise.isProbabilityMeasure H (ξs k) q r (ns k))
      atTop (𝓝 μ₀)) (i : nd_DomainIndex d r) (m : ℕ) :
    ∀ᵐ x ∂(μ₀ : Measure (nd_Joint d r)), x ∈ nd_nonnegLocalSet r i m :=
  u5_ae_mem_of_forall_pointwise hH hlim (nd_isClosed_nonnegLocalSet r i m) fun k ω =>
    nd_jointSample_mem_nonnegLocalSet (hU k).base hH hq0 hq1 r (ns k) i m ω

/-- First-exit decomposition (inside points) in every array limit. -/
theorem u5_ae_insideExitSet (hH : IsDyadicRealization κ P W H) (hU : ∀ k, UHyp d κ b μ (ξs k))
    (hq0 : 0 < q) (hq1 : q < 1) (r : ℝ) (ns : ℕ → ℕ) {μ₀ : ProbabilityMeasure (nd_Joint d r)}
    (hlim : Tendsto
      (fun k => nd_jointLaw P hH.whiteNoise.isProbabilityMeasure H (ξs k) q r (ns k))
      atTop (𝓝 μ₀)) (i : nd_DomainIndex d r)
    {A : Set (nd_domain r i)} (hA : IsCompact A) (hAne : A.Nonempty) (x : nd_domain r i) :
    ∀ᵐ s ∂(μ₀ : Measure (nd_Joint d r)), s ∈ nd_insideExitSet r i A x :=
  u5_ae_mem_of_forall hH hlim (nd_isClosed_insideExitSet r i hA x) fun k =>
    nd_jointSample_mem_insideExitSet (hU k).base hH hq0 hq1 r (ns k) i A hAne x

/-- First-exit decomposition (outside points) in every array limit. -/
theorem u5_ae_outsideExitSet (hH : IsDyadicRealization κ P W H) (hU : ∀ k, UHyp d κ b μ (ξs k))
    (hq0 : 0 < q) (hq1 : q < 1) (r : ℝ) (ns : ℕ → ℕ) {μ₀ : ProbabilityMeasure (nd_Joint d r)}
    (hlim : Tendsto
      (fun k => nd_jointLaw P hH.whiteNoise.isProbabilityMeasure H (ξs k) q r (ns k))
      atTop (𝓝 μ₀)) (i : nd_DomainIndex d r)
    {A : Set (nd_domain r i)} (hA : IsCompact A) (hAne : A.Nonempty)
    (x : Rd d) (hx : x ∉ nd_domain r i) :
    ∀ᵐ s ∂(μ₀ : Measure (nd_Joint d r)), s ∈ nd_outsideExitSet r i A x := by
  refine u5_ae_mem_of_forall_pointwise hH hlim (nd_isClosed_outsideExitSet r i hA x) fun k ω => ?_
  have hx' := nd_jointSample_mem_outsideExitSet (hU k).base hH hq0 hq1 r (ns k) i A hAne x hx
  change ω ∈ (nd_jointSample P H (ξs k) q r (ns k)) ⁻¹' nd_outsideExitSet r i A x
  rw [hx']
  trivial

/-- The inside exit inequality for all points of a domain, in every array limit. -/
theorem u5_ae_allInsideExitSet (hH : IsDyadicRealization κ P W H) (hU : ∀ k, UHyp d κ b μ (ξs k))
    (hq0 : 0 < q) (hq1 : q < 1) (r : ℝ) (ns : ℕ → ℕ) {μ₀ : ProbabilityMeasure (nd_Joint d r)}
    (hlim : Tendsto
      (fun k => nd_jointLaw P hH.whiteNoise.isProbabilityMeasure H (ξs k) q r (ns k))
      atTop (𝓝 μ₀)) (i : nd_DomainIndex d r)
    {A : Set (nd_domain r i)} (hA : IsCompact A) (hAne : A.Nonempty) :
    ∀ᵐ s ∂(μ₀ : Measure (nd_Joint d r)), s ∈ nd_allInsideExitSet r i A := by
  refine u5_ae_mem_of_forall hH hlim (nd_isClosed_allInsideExitSet r i hA) fun k => ?_
  have hzero := ae_forall_eq_zero_of_isBandVersion_self (hU k).base.kernel hH.whiteNoise one_pos
    ((hH.band 0).congr_band (pow_zero _) rfl)
  filter_upwards [hzero] with ω hω
  exact Set.mem_iInter.2 fun x =>
    nd_jointSample_mem_insideExitSet_of_zero (hU k).base hH hq0 hq1 r (ns k) i A hAne x ω hω

/-- The outside exit inequality for all points outside a domain, in every array limit. -/
theorem u5_ae_allOutsideExitSet (hH : IsDyadicRealization κ P W H) (hU : ∀ k, UHyp d κ b μ (ξs k))
    (hq0 : 0 < q) (hq1 : q < 1) (r : ℝ) (ns : ℕ → ℕ) {μ₀ : ProbabilityMeasure (nd_Joint d r)}
    (hlim : Tendsto
      (fun k => nd_jointLaw P hH.whiteNoise.isProbabilityMeasure H (ξs k) q r (ns k))
      atTop (𝓝 μ₀)) (i : nd_DomainIndex d r)
    {A : Set (nd_domain r i)} (hA : IsCompact A) (hAne : A.Nonempty) :
    ∀ᵐ s ∂(μ₀ : Measure (nd_Joint d r)), s ∈ nd_allOutsideExitSet r i A := by
  refine u5_ae_mem_of_forall_pointwise hH hlim (nd_isClosed_allOutsideExitSet r i hA) fun k ω => ?_
  simp only [nd_allOutsideExitSet, Set.mem_iInter]
  intro x
  have hx := nd_jointSample_mem_outsideExitSet (hU k).base hH hq0 hq1 r (ns k) i A hAne x.1 x.2
  change ω ∈ (nd_jointSample P H (ξs k) q r (ns k)) ⁻¹' nd_outsideExitSet r i A x.1
  rw [hx]
  trivial

/-- The collar relation in every array limit. -/
theorem u5_ae_collarSet (hH : IsDyadicRealization κ P W H) (hU : ∀ k, UHyp d κ b μ (ξs k))
    (hq0 : 0 < q) (hq1 : q < 1) (r : ℝ) (ns : ℕ → ℕ) {μ₀ : ProbabilityMeasure (nd_Joint d r)}
    (hlim : Tendsto
      (fun k => nd_jointLaw P hH.whiteNoise.isProbabilityMeasure H (ξs k) q r (ns k))
      atTop (𝓝 μ₀)) (i : nd_DomainIndex d r)
    {g : Rd d → ℝ} (hg : Continuous g) {ρ : ℝ} (hρ : 0 < ρ)
    (hgU : ∀ z, z ∉ nd_domain r i → g z ≤ 0)
    {F : Set (Rd d)} (hF : IsCompact F) (hFne : F.Nonempty)
    {A : Set (nd_domain r i)} (hA : IsCompact A) (hAne : A.Nonempty)
    (hgF : ∀ z ∈ F, g z ≤ ρ)
    (hgA : ∀ z ∈ ((↑) '' A : Set (Rd d)), ρ ≤ g z) :
    ∀ᵐ s ∂(μ₀ : Measure (nd_Joint d r)), s ∈ nd_collarSet r i g ρ F A :=
  u5_ae_mem_of_forall hH hlim (nd_isClosed_collarSet r i hg hρ hgU hF hA) fun k =>
    nd_jointSample_mem_collarSet (hU k).base hH hq0 hq1 r (ns k) i hg hρ hgU hFne hAne hgF hgA

/-- The global outside barrier in every array limit. -/
theorem u5_ae_globalOutsideBarrierSet (hH : IsDyadicRealization κ P W H)
    (hU : ∀ k, UHyp d κ b μ (ξs k)) (hq0 : 0 < q) (hq1 : q < 1)
    (rGrid r : ℝ) (hr : 0 < r) (R : ℝ) (hrr : r < R) (ns : ℕ → ℕ)
    {μ₀ : ProbabilityMeasure (nd_Joint d rGrid)}
    (hlim : Tendsto
      (fun k => nd_jointLaw P hH.whiteNoise.isProbabilityMeasure H (ξs k) q rGrid (ns k))
      atTop (𝓝 μ₀)) :
    ∀ᵐ s ∂(μ₀ : Measure (nd_Joint d rGrid)), s ∈ nd_globalOutsideBarrierSet rGrid R r :=
  u5_ae_mem_of_forall_pointwise hH hlim (nd_isClosed_globalOutsideBarrierSet rGrid R r)
    fun k ω => nd_jointSample_mem_globalOutsideBarrierSet (hU k).base hH hq0 hq1 rGrid hr hrr (ns k) ω

/-- Array limits are carried by pseudo-metrics. -/
theorem u5_ae_pseudoSet (hH : IsDyadicRealization κ P W H) (hU : ∀ k, UHyp d κ b μ (ξs k))
    (hq0 : 0 < q) (hq1 : q < 1) (rGrid : ℝ) (ns : ℕ → ℕ)
    {μ₀ : ProbabilityMeasure (nd_Joint d rGrid)}
    (hlim : Tendsto
      (fun k => nd_jointLaw P hH.whiteNoise.isProbabilityMeasure H (ξs k) q rGrid (ns k))
      atTop (𝓝 μ₀)) :
    ∀ᵐ s ∂(μ₀ : Measure (nd_Joint d rGrid)), s ∈ nd_pseudoSet rGrid :=
  u5_ae_mem_of_forall_pointwise hH hlim (nd_isClosed_pseudoSet rGrid) fun k ω =>
    nd_jointSample_mem_pseudoSet (hU k).base hH hq0 hq1 rGrid (ns k) ω

/-- The local coordinates vanish on the diagonal in every array limit. -/
theorem u5_ae_localDiagSet (hH : IsDyadicRealization κ P W H) (rGrid : ℝ) (ns : ℕ → ℕ)
    {μ₀ : ProbabilityMeasure (nd_Joint d rGrid)}
    (hlim : Tendsto
      (fun k => nd_jointLaw P hH.whiteNoise.isProbabilityMeasure H (ξs k) q rGrid (ns k))
      atTop (𝓝 μ₀)) (i : nd_DomainIndex d rGrid) (m : ℕ) :
    ∀ᵐ s ∂(μ₀ : Measure (nd_Joint d rGrid)), s ∈ nd_localDiagSet rGrid i m :=
  u5_ae_mem_of_forall_pointwise hH hlim (nd_isClosed_localDiagSet rGrid i m) fun k ω =>
    nd_jointSample_mem_localDiagSet hH q rGrid (ns k) i m ω

end Relations

/-! ### Step (μ2): the coarse-field comparison, uniformly in `ξ ≤ b` -/

section Compare

variable {κ : Rd d → ℝ} {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
  {W : WN d → Ω → ℝ} {H : ℕ → Rd d → Ω → ℝ} {b μ : ℝ} {ξs : ℕ → ℝ} {q : ℝ≥0∞}

/-- The comparison relation is monotone in its constant on nonnegative states. -/
theorem u5_compSet_mono (r : ℝ) (i : nd_DomainIndex d r) (m : ℕ) {R R' : ℝ} (hRR' : R ≤ R')
    {x : nd_Joint d r} (hx : x ∈ nd_compSet r i m R)
    (h0 : x ∈ nd_nonnegLocalSet r i 0) (hm : x ∈ nd_nonnegLocalSet r i m) :
    x ∈ nd_compSet r i m R' := by
  intro p
  obtain ⟨h1, h2⟩ := hx p
  exact ⟨h1.trans (mul_le_mul_of_nonneg_right hRR' (hm p)),
    h2.trans (mul_le_mul_of_nonneg_right hRR' (h0 p))⟩

/-- **(μ2) at every level, uniformly in `ξ ∈ S(b, μ)`**: the closed comparison relation with constant `e^{b L}` has
probability at least `1 - θ` under every joint law, where `L` is a `ξ`-free quantile bound of `sup |h_m|` on the
domain (port of `DGZ.nd_prelimit_compSet_prob` with `e^{|ξ| L} ≤ e^{b L}`). -/
theorem u5_prelimit_compSet_prob (hκ : IsLFPPKernel κ) (hb : 0 < b)
    (r : ℝ) (i : nd_DomainIndex d r) (m : ℕ) {θ : ℝ} (hθ : 0 < θ) :
    ∃ R : ℝ, 1 ≤ R ∧ ∀ ξ : ℝ, UHyp d κ b μ ξ →
      ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) (W : WN d → Ω → ℝ)
        (H : ℕ → Rd d → Ω → ℝ) (hH : IsDyadicRealization κ P W H) {q : ℝ≥0∞}, 0 < q → q < 1 →
        ∀ n : ℕ, (1 : ℝ≥0∞) - ENNReal.ofReal θ ≤
          (nd_jointLaw P hH.whiteNoise.isProbabilityMeasure H ξ q r n : Measure (nd_Joint d r))
            (nd_compSet r i m R) := by
  obtain ⟨R₀, hR₀, hUbox⟩ := nd_exists_domain_cbox r i
  obtain ⟨L, hL, htail⟩ := exists_sup_tail_level_tight hκ m hR₀ hθ
  refine ⟨Real.exp (b * L), Real.one_le_exp_iff.2 (mul_nonneg hb.le hL), ?_⟩
  intro ξ hU Ω _ P W H hH q hq0 hq1 n
  let F := nd_compSet r i m (Real.exp (b * L))
  let X := nd_jointSample P H ξ q r n
  have hX : Measurable X := nd_measurable_jointSample hH ξ q r n
  have hF : MeasurableSet F := (nd_isClosed_compSet r i m _).measurableSet
  have hzero := ae_forall_eq_zero_of_isBandVersion_self hκ hH.whiteNoise one_pos
    ((hH.band 0).congr_band (pow_zero _) rfl)
  have hbad : P {ω | ∃ z ∈ HigherDimLFPP.DGZ.cbox (0 : Rd d) R₀, L < |H m z ω|} ≤
      ENNReal.ofReal θ := htail hH.whiteNoise (hH.band m) 0
  have hξb : |ξ| * L ≤ b * L := by
    rw [abs_of_pos hU.xi_pos]
    exact mul_le_mul_of_nonneg_right hU.le_b hL
  have hcompl : P (X ⁻¹' F)ᶜ ≤ ENNReal.ofReal θ := by
    calc
      P (X ⁻¹' F)ᶜ ≤ P {ω | ∃ z ∈ HigherDimLFPP.DGZ.cbox (0 : Rd d) R₀, L < |H m z ω|} := by
            apply measure_mono_ae
            filter_upwards [hzero] with ω hz hω
            by_contra hbd
            have hbound : ∀ z ∈ nd_domain r i, |H m z ω| ≤ L := by
              intro z hzU
              exact le_of_not_gt (fun hlt => hbd ⟨z, hUbox hzU, hlt⟩)
            have hmem := nd_jointSample_mem_compSet hU.base hH hq0 hq1 r n i m L ω hz hbound
            exact hω (u5_compSet_mono r i m (Real.exp_le_exp.2 hξb) hmem
              (nd_jointSample_mem_nonnegLocalSet hU.base hH hq0 hq1 r n i 0 ω)
              (nd_jointSample_mem_nonnegLocalSet hU.base hH hq0 hq1 r n i m ω))
      _ ≤ ENNReal.ofReal θ := hbad
  change (1 : ℝ≥0∞) - ENNReal.ofReal θ ≤ (P.map X) F
  rw [Measure.map_apply hX hF]
  apply tsub_le_iff_right.2
  calc
    1 = P (X ⁻¹' F) + P (X ⁻¹' F)ᶜ :=
      (@prob_add_prob_compl Ω _ P _ hH.whiteNoise.isProbabilityMeasure (hX hF)).symm
    _ ≤ P (X ⁻¹' F) + ENNReal.ofReal θ := add_le_add le_rfl hcompl

/-- **(μ2) in every array limit**: a finite comparison constant with probability `≥ 1 - θ`
(port of `DGZ.nd_limit_compSet_prob`). -/
theorem u5_limit_compSet_prob (hH : IsDyadicRealization κ P W H) (hU : ∀ k, UHyp d κ b μ (ξs k))
    (hq0 : 0 < q) (hq1 : q < 1) (r : ℝ) (ns : ℕ → ℕ) {μ₀ : ProbabilityMeasure (nd_Joint d r)}
    (hlim : Tendsto
      (fun k => nd_jointLaw P hH.whiteNoise.isProbabilityMeasure H (ξs k) q r (ns k))
      atTop (𝓝 μ₀)) (i : nd_DomainIndex d r) (m : ℕ) {θ : ℝ} (hθ : 0 < θ) :
    ∃ R : ℝ, 1 ≤ R ∧
      (1 : ℝ≥0∞) - ENNReal.ofReal θ ≤ (μ₀ : Measure (nd_Joint d r)) (nd_compSet r i m R) := by
  obtain ⟨R, hR, hbound⟩ := u5_prelimit_compSet_prob (hU 0).base.kernel (hU 0).b_pos r i m hθ
  exact ⟨R, hR, LQGMetric.DFGPS.le_measure_of_isClosed hlim (nd_isClosed_compSet r i m R)
    (Filter.Eventually.of_forall fun k => hbound (ξs k) (hU k) Ω P W H hH hq0 hq1 (ns k))⟩

/-- **The zero sets of the `m = 0` and `m > 0` local coordinates agree** in every array limit (port of
`DGZ.nd_ae_finiteCompSet_of_tendsto`). -/
theorem u5_ae_finiteCompSet (hH : IsDyadicRealization κ P W H) (hU : ∀ k, UHyp d κ b μ (ξs k))
    (hq0 : 0 < q) (hq1 : q < 1) (r : ℝ) (ns : ℕ → ℕ) {μ₀ : ProbabilityMeasure (nd_Joint d r)}
    (hlim : Tendsto
      (fun k => nd_jointLaw P hH.whiteNoise.isProbabilityMeasure H (ξs k) q r (ns k))
      atTop (𝓝 μ₀)) (i : nd_DomainIndex d r) (m : ℕ) :
    ∀ᵐ x ∂(μ₀ : Measure (nd_Joint d r)), x ∈ nd_finiteCompSet r i m := by
  let F := nd_finiteCompSet r i m
  have hF : MeasurableSet F := nd_measurableSet_finiteCompSet r i m
  have h0 := u5_ae_nonnegLocalSet hH hU hq0 hq1 r ns hlim i 0
  have hm := u5_ae_nonnegLocalSet hH hU hq0 hq1 r ns hlim i m
  have hfull : (μ₀ : Measure (nd_Joint d r)) F = 1 := by
    apply le_antisymm prob_le_one
    apply ENNReal.le_of_forall_pos_le_add
    intro ε hε _
    obtain ⟨R, hR, hbound⟩ := u5_limit_compSet_prob hH hU hq0 hq1 r ns hlim i m
      (show 0 < (ε : ℝ) by exact_mod_cast hε)
    have hmeasure : (μ₀ : Measure (nd_Joint d r)) (nd_compSet r i m R) ≤
        (μ₀ : Measure (nd_Joint d r)) F := by
      apply measure_mono_ae
      filter_upwards [h0, hm] with x hx0 hxm hx
      exact nd_mem_finiteCompSet_of_compSet r i m hR hx hx0 hxm
    have heps : ENNReal.ofReal (ε : ℝ) = (ε : ℝ≥0∞) := by simp
    rw [heps] at hbound
    exact (tsub_le_iff_right.mp hbound).trans (add_le_add hmeasure le_rfl)
  change ∀ᵐ x ∂(μ₀ : Measure (nd_Joint d r)), x ∈ F
  exact (ae_mem_iff_measure_eq hF.nullMeasurableSet).2 (by rw [hfull, measure_univ])

end Compare

/-! ### Step (μ4): independence of separated deleted-scale coordinates in array limits -/

section Indep

variable {κ : Rd d → ℝ} {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
  {W : WN d → Ω → ℝ} {H : ℕ → Rd d → Ω → ℝ} {b μ : ℝ} {ξs : ℕ → ℝ}

/-- **Independence survives array limits** (port of `DGZ.nd_indepFun_jointLimit`): at every level `k` with
`ns k ≥ m`, the deleted-scale internal metrics on two domains at distance `> 2ρ 2^{-m}` are independent (finite range
of `κ`), and limits of product laws are product laws. -/
theorem u5_indepFun_jointLimit (hH : IsDyadicRealization κ P W H) (hU : ∀ k, UHyp d κ b μ (ξs k))
    (q : ℝ≥0∞) (r : ℝ) (ns : ℕ → ℕ) (hns : Tendsto ns atTop atTop)
    {μ₀ : ProbabilityMeasure (nd_Joint d r)}
    (hlim : Tendsto
      (fun k => nd_jointLaw P hH.whiteNoise.isProbabilityMeasure H (ξs k) q r (ns k))
      atTop (𝓝 μ₀)) (m : ℕ) (i₁ i₂ : nd_DomainIndex d r) (ρ : ℝ)
    (hρ : ∀ y, ρ ≤ ‖y‖ → κ y = 0)
    (hsep : ∀ z ∈ nd_domain r i₁, ∀ w ∈ nd_domain r i₂, 2 * ρ * ((2 : ℝ)⁻¹ ^ m) < ‖z - w‖) :
    IndepFun (fun x : nd_Joint d r => x.2 (i₁, m))
      (fun x : nd_Joint d r => x.2 (i₂, m)) (μ₀ : Measure (nd_Joint d r)) := by
  have : IsProbabilityMeasure P := hH.whiteNoise.isProbabilityMeasure
  obtain ⟨N, hN⟩ := (hns.eventually (eventually_ge_atTop m)).exists_forall_of_atTop
  let f : nd_Joint d r →
      C(nd_domain r i₁ × nd_domain r i₁, ℝ) × C(nd_domain r i₂ × nd_domain r i₂, ℝ) :=
    fun x => (x.2 (i₁, m), x.2 (i₂, m))
  have hf : Continuous f :=
    ((continuous_apply (i₁, m)).comp continuous_snd).prodMk
      ((continuous_apply (i₂, m)).comp continuous_snd)
  let ν : ℕ → ProbabilityMeasure (nd_Joint d r) := fun k =>
    nd_jointLaw P hH.whiteNoise.isProbabilityMeasure H (ξs (k + N)) q r (ns (k + N))
  let ρn : ℕ → ProbabilityMeasure
      (C(nd_domain r i₁ × nd_domain r i₁, ℝ) × C(nd_domain r i₂ × nd_domain r i₂, ℝ)) :=
    fun k => (ν k).map f
  let ρ₀ : ProbabilityMeasure
      (C(nd_domain r i₁ × nd_domain r i₁, ℝ) × C(nd_domain r i₂ × nd_domain r i₂, ℝ)) :=
    μ₀.map f
  have hν : Tendsto ν atTop (𝓝 μ₀) := hlim.comp (tendsto_add_atTop_nat N)
  have hconv : Tendsto ρn atTop (𝓝 ρ₀) :=
    (ProbabilityMeasure.continuous_map hf).tendsto μ₀ |>.comp hν
  apply LQGMetric.DFGPS.L217.indepFun_of_tendsto_law
    (P := P) (P' := (μ₀ : Measure (nd_Joint d r)))
    (Xn := fun k ω => (nd_jointSample P H (ξs (k + N)) q r (ns (k + N)) ω).2 (i₁, m))
    (Yn := fun k ω => (nd_jointSample P H (ξs (k + N)) q r (ns (k + N)) ω).2 (i₂, m))
    (ρ := ρn) (ρ₀ := ρ₀)
  · intro k
    exact ((measurable_pi_apply (i₁, m)).comp measurable_snd |>.comp
      (nd_measurable_jointSample hH (ξs (k + N)) q r (ns (k + N)))).aemeasurable
  · intro k
    exact ((measurable_pi_apply (i₂, m)).comp measurable_snd |>.comp
      (nd_measurable_jointSample hH (ξs (k + N)) q r (ns (k + N)))).aemeasurable
  · exact ((measurable_pi_apply (i₁, m)).comp measurable_snd).aemeasurable
  · exact ((measurable_pi_apply (i₂, m)).comp measurable_snd).aemeasurable
  · intro k
    exact nd_indepFun_jointLocal (hU (k + N)).base hH q r (ns (k + N)) m
      (hN (k + N) (by omega)) i₁ i₂ ρ hρ hsep
  · intro k
    change ((P.map (nd_jointSample P H (ξs (k + N)) q r (ns (k + N)))).map f) = _
    rw [Measure.map_map hf.measurable (nd_measurable_jointSample hH (ξs (k + N)) q r (ns (k + N)))]
    rfl
  · rfl
  · exact hconv

end Indep


end HigherDimLQGContinuity
