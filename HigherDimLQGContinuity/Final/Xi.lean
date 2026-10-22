import HigherDimLQGContinuity.Final.Medians
import HigherDimLQGContinuity.Param.Interval
import HigherDimLQGContinuity.Median.MedianOneStrong
import HigherDimLQGMetric.Sec4.Lemma41Uniform
import HigherDimLQGMetric.Sharp.ScaledMetric

/-!
# The median-one version in the Weyl parameter

Packet E4: final normalization, law transfer, and locally uniform continuity.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.style.haveILetI false

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal
open HigherDimLQGMetric
open HigherDimLFPP (Rd e₁)

namespace HigherDimLQGContinuity

/-- Compact-open convergence of distance functions gives the exact locally
uniform extended-distance convergence used in Theorem 1.1. -/
theorem e4_tendsto_supDistLU {d : ℕ} {ι : Type*} {L : Filter ι}
    {F : ι → C(Rd d × Rd d, ℝ)} {G : C(Rd d × Rd d, ℝ)}
    (hF : Tendsto F L (𝓝 G)) (R : ℝ) :
    Tendsto (fun i => supDistLU d R (F i) G) L (𝓝 0) := by
  let K : Set (Rd d × Rd d) :=
    Metric.closedBall (0 : Rd d) R ×ˢ Metric.closedBall (0 : Rd d) R
  have hK : IsCompact K := (isCompact_closedBall _ _).prod (isCompact_closedBall _ _)
  letI : CompactSpace K := isCompact_iff_compactSpace.mp hK
  have hres : Tendsto (fun i => (F i).restrict K) L (𝓝 (G.restrict K)) :=
    ((ContinuousMap.continuous_restrict K).tendsto _).comp hF
  have hpair : Tendsto (fun i => ((F i).restrict K, G.restrict K)) L
      (𝓝 (G.restrict K, G.restrict K)) := by
    simpa only [nhds_prod_eq] using hres.prodMk (tendsto_const_nhds (x := G.restrict K))
  have hed : Tendsto (fun i => edist ((F i).restrict K) (G.restrict K)) L (𝓝 0) := by
    simpa only [Function.comp_def, edist_self] using (continuous_edist.tendsto _).comp hpair
  convert hed using 1
  ext i
  simp only [supDistLU, ContinuousMap.edist_eq_iSup, iSup_subtype, K,
    ContinuousMap.restrict_apply]

/-- Canonical almost-sure events transfer to every normalized LGF law, even
when their predicates are not known measurable. -/
theorem ae_of_normLGFLaw {d : ℕ} (hd : 2 ≤ d)
    {A : Set (DistRd d)} (hA : ∀ᵐ g ∂(normLGFLaw d), g ∈ A)
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {h : Ω → DistRd d} (hh : IsNormalizedLGF h P) :
    ∀ᵐ ω ∂P, h ω ∈ A := by
  have hnull : normLGFLaw d Aᶜ = 0 := (ae_iff).1 hA
  have hle := l9b_preimage_le_normLGFLaw hd hh Aᶜ
  have hzero : P (h ⁻¹' Aᶜ) = 0 := le_zero_iff.mp (hle.trans_eq hnull)
  exact (ae_iff).2 hzero

/-- A median-one strong assignment has precisely the mean-log scaling of the
positive version. -/
theorem medianXi_eq_exp_neg_logMean {d : ℕ} (hd : 3 ≤ d)
    {X : ℝ → DistRd d → C(Rd d × Rd d, ℝ)} (hX : PosVersionStmt d X)
    {ξ : ℝ} (hξ : 0 < ξ) (hsub : Real.sqrt (2 * d) < distExp d ξ)
    {E : DistRd d → ContMetric d}
    (hE : IsStrongExpMetric d ξ (distExp d ξ) E) (hM : IsMedianOne d E) :
    medianXi d X ξ = Real.exp (-logMean E) := by
  haveI : IsProbabilityMeasure (normLGFLaw d) := (normLGFLaw_spec_holds d (by omega)).1
  have hmE : LQGMetric.IsMedian
      ((normLGFLaw d).map fun g => (E g).1 (0, e₁ d)) 1 :=
    (isMedianOne_iff_isMedian hE.measurable).1 hM
  have hc : 0 < Real.exp (-logMean E) := Real.exp_pos _
  have hmR : LQGMetric.IsMedian
      ((normLGFLaw d).map fun g => (rho E g).1 (0, e₁ d))
      (Real.exp (-logMean E)) := by
    have hXmeas : AEMeasurable (fun g => (E g).1 (0, e₁ d)) (normLGFLaw d) :=
      (p2_measurable_contMetric_apply hE.measurable _).aemeasurable
    have h := (e4_median_mul_iff hXmeas hc (1 : ℝ)).2 hmE
    simpa only [mul_one, rho_apply] using h
  exact ((medianXi_spec hd hX hξ hsub hE).2.2 _ hmR).symm

/-- The positive version normalized by its median agrees almost surely with
every median-one strong assignment at a fixed subcritical parameter. -/
theorem version_medianOne_ae {d : ℕ} (hd : 3 ≤ d)
    {X : ℝ → DistRd d → C(Rd d × Rd d, ℝ)} (hX : PosVersionStmt d X)
    {ξ : ℝ} (hξ : 0 < ξ) (hsub : Real.sqrt (2 * d) < distExp d ξ)
    {E : DistRd d → ContMetric d}
    (hE : IsStrongExpMetric d ξ (distExp d ξ) E) (hM : IsMedianOne d E) :
    ∀ᵐ g ∂(normLGFLaw d),
      (medianXi d X ξ)⁻¹ • X ξ g = (E g).1 := by
  have hm : medianXi d X ξ = Real.exp (-logMean E) :=
    medianXi_eq_exp_neg_logMean hd hX hξ hsub hE hM
  filter_upwards [hX.2.1 ξ hξ hsub E hE] with g hg
  rw [hg, hm]
  apply ContinuousMap.ext
  intro p
  simp only [ContinuousMap.smul_apply, smul_eq_mul, rho_apply]
  rw [Real.exp_neg]
  field_simp

/-- The final family: the median-normalized positive version on one measurable
full set, and the Euclidean metric everywhere else. -/
noncomputable def finalVersion (d : ℕ)
    (X : ℝ → DistRd d → C(Rd d × Rd d, ℝ)) (Good : Set (DistRd d)) :
    ℝ → DistRd d → C(Rd d × Rd d, ℝ) := by
  classical
  exact fun ξ g => if ξ ∈ subcritSet d ∧ g ∈ Good then
    (medianXi d X ξ)⁻¹ • X ξ g else euclidDistC d

theorem e4_finalVersion_measurable {d : ℕ} (hd : 3 ≤ d)
    {X : ℝ → DistRd d → C(Rd d × Rd d, ℝ)} (hX : PosVersionStmt d X)
    {Good : Set (DistRd d)} (hGood : MeasurableSet Good) :
    Measurable (Function.uncurry (finalVersion d X Good)) := by
  classical
  have hSopen : IsOpen (subcritSet d) := by
    rw [subcritSet_eq_Ioo (by omega)]
    exact isOpen_Ioo
  have hSm : MeasurableSet (subcritSet d) := hSopen.measurableSet
  have hmc : ContinuousOn (medianXi d X) (subcritSet d) := by
    simpa only [subcritSet] using continuousOn_medianXi hd hX
  have hm : Measurable ((subcritSet d).piecewise (medianXi d X) (fun _ => 1)) :=
    hmc.measurable_piecewise continuousOn_const hSm
  have hc : Measurable (fun p : ℝ × DistRd d =>
      (((subcritSet d).piecewise (medianXi d X) (fun _ => 1)) p.1)⁻¹) :=
    (hm.comp measurable_fst).inv
  have hbase : Measurable (fun p : ℝ × DistRd d =>
      (((subcritSet d).piecewise (medianXi d X) (fun _ => 1)) p.1)⁻¹ • X p.1 p.2) :=
    hc.smul hX.1
  have hcond : MeasurableSet {p : ℝ × DistRd d | p.1 ∈ subcritSet d ∧ p.2 ∈ Good} :=
    (hSm.preimage measurable_fst).inter (hGood.preimage measurable_snd)
  have h : Measurable (fun p : ℝ × DistRd d =>
      if p.1 ∈ subcritSet d ∧ p.2 ∈ Good then
        (((subcritSet d).piecewise (medianXi d X) (fun _ => 1)) p.1)⁻¹ • X p.1 p.2
      else euclidDistC d) := hbase.ite hcond measurable_const
  convert h using 1
  ext p
  by_cases hp : p.1 ∈ subcritSet d ∧ p.2 ∈ Good
  · simp only [finalVersion, Function.uncurry, hp,
      Set.piecewise_eq_of_mem _ _ _ hp.1]
  · simp only [finalVersion, Function.uncurry, hp, ite_false]

theorem e4_finalVersion_tendsto {d : ℕ} (hd : 3 ≤ d)
    {X : ℝ → DistRd d → C(Rd d × Rd d, ℝ)}
    (hX : PosVersionStmt d X) (hE : EndpointStmt d X)
    {Good : Set (DistRd d)} {g : DistRd d} (hg : g ∈ Good)
    (hgc : ContinuousOn (fun ξ => X ξ g) (subcritSet d))
    (hge : Tendsto (fun ξ => X ξ g) (𝓝[subcritSet d] 0) (𝓝 (euclidDistC d)))
    {ξ₀ : ℝ} (hξ₀ : ξ₀ ∈ xiRange d) :
    Tendsto (fun ξ => finalVersion d X Good ξ g)
      (𝓝[xiRange d] ξ₀) (𝓝 (finalVersion d X Good ξ₀ g)) := by
  classical
  have hS : xiRange d = insert 0 (subcritSet d) := xiRange_eq_insert_subcritSet d
  rcases (hS ▸ hξ₀ : ξ₀ ∈ insert 0 (subcritSet d)) with hzero | hpos
  · subst ξ₀
    have hD0 : finalVersion d X Good 0 g = euclidDistC d := by
      simp [finalVersion, subcritSet]
    have hmed := tendsto_medianXi_zero hd hX hE
    have hscaled : Tendsto
        (fun ξ => (medianXi d X ξ)⁻¹ • X ξ g)
        (𝓝[subcritSet d] 0) (𝓝 (euclidDistC d)) := by
      have h := (hmed.inv₀ one_ne_zero).smul hge
      simpa only [subcritSet, inv_one, one_smul] using h
    have hD : Tendsto (fun ξ => finalVersion d X Good ξ g)
        (𝓝[subcritSet d] 0) (𝓝 (euclidDistC d)) := by
      exact hscaled.congr' (eventually_nhdsWithin_of_forall fun ξ hξ => by
        simp only [finalVersion, hξ, hg, and_self, ite_true])
    rw [hS, nhdsWithin_insert, hD0]
    have hpure : Tendsto (fun ξ => finalVersion d X Good ξ g) (pure 0)
        (𝓝 (euclidDistC d)) := by
      simpa only [hD0] using
        tendsto_pure_nhds (fun ξ => finalVersion d X Good ξ g) 0
    exact tendsto_sup.2 ⟨hpure, hD⟩
  · have hξpos : 0 < ξ₀ := hpos.1
    have hmc := continuousOn_medianXi hd hX ξ₀ hpos
    have hmp : 0 < medianXi d X ξ₀ := by
      obtain ⟨⟨E, hEE, -⟩, -⟩ := theorem12 d ξ₀ hd hpos.1 hpos.2
      exact (medianXi_spec hd hX hpos.1 hpos.2 hEE).1
    have hscaled : Tendsto
        (fun ξ => (medianXi d X ξ)⁻¹ • X ξ g)
        (𝓝[subcritSet d] ξ₀)
        (𝓝 ((medianXi d X ξ₀)⁻¹ • X ξ₀ g)) :=
      (hmc.inv₀ hmp.ne').smul (hgc ξ₀ hpos)
    have hD : Tendsto (fun ξ => finalVersion d X Good ξ g)
        (𝓝[subcritSet d] ξ₀) (𝓝 (finalVersion d X Good ξ₀ g)) := by
      have hD0 : finalVersion d X Good ξ₀ g = (medianXi d X ξ₀)⁻¹ • X ξ₀ g := by
        simp [finalVersion, hpos, hg]
      rw [hD0]
      exact hscaled.congr' (eventually_nhdsWithin_of_forall fun ξ hξ => by
        simp [finalVersion, hξ, hg])
    rwa [hS, nhdsWithin_insert_of_ne hξpos.ne']

/-- Packet E4: from a positive version and its Euclidean endpoint to the
median-one `ξ` statement of Theorem 1.1. -/
theorem theorem11Xi_of_parts
    (h : ∀ d : ℕ, 3 ≤ d → SubcritLocal d ∧ ∃ X : ℝ → DistRd d → C(Rd d × Rd d, ℝ),
      PosVersionStmt d X ∧ EndpointStmt d X) : Theorem11XiStmt := by
  intro d hd
  obtain ⟨-, X, hX, hE⟩ := h d hd
  have hAE : ∀ᵐ g ∂(normLGFLaw d),
      ContinuousOn (fun ξ => X ξ g) (subcritSet d) ∧
        Tendsto (fun ξ => X ξ g) (𝓝[subcritSet d] 0) (𝓝 (euclidDistC d)) :=
    hX.2.2.and hE
  obtain ⟨N, hNsub, hNm, hNzero⟩ :=
    exists_measurable_superset_of_null ((ae_iff).1 hAE)
  let Good : Set (DistRd d) := Nᶜ
  have hGm : MeasurableSet Good := hNm.compl
  have hGAE : ∀ᵐ g ∂(normLGFLaw d), g ∈ Good :=
    (ae_iff).2 (show normLGFLaw d {g | g ∉ Good} = 0 by
      have hset : {g | g ∉ Good} = N := by
        ext g
        simp [Good]
      rw [hset]
      exact hNzero)
  have hG (g : DistRd d) (hg : g ∈ Good) :
      ContinuousOn (fun ξ => X ξ g) (subcritSet d) ∧
        Tendsto (fun ξ => X ξ g) (𝓝[subcritSet d] 0) (𝓝 (euclidDistC d)) := by
    by_contra hn
    exact hg (hNsub hn)
  refine ⟨finalVersion d X Good, e4_finalVersion_measurable hd hX hGm, ?_, ?_, ?_⟩
  · intro g
    simp [finalVersion, subcritSet]
  · intro ξ hξ hsub E hEstrong hM Ω _ P _ hf hh
    have hcanon : ∀ᵐ g ∂(normLGFLaw d),
        finalVersion d X Good ξ g = (E g).1 := by
      filter_upwards [hGAE, version_medianOne_ae hd hX hξ hsub hEstrong hM]
        with g hg hnorm
      have hmem : ξ ∈ subcritSet d := ⟨hξ, hsub⟩
      simpa [finalVersion, hmem, hg] using hnorm
    exact ae_of_normLGFLaw (by omega) hcanon hh
  · intro Ω _ P _ hf hh
    have hcanon : ∀ᵐ g ∂(normLGFLaw d),
        ∀ ξ₀ ∈ xiRange d, ∀ R : ℝ, 0 < R →
          Tendsto (fun ξ => supDistLU d R
            (finalVersion d X Good ξ g) (finalVersion d X Good ξ₀ g))
            (𝓝[xiRange d] ξ₀) (𝓝 0) := by
      filter_upwards [hGAE] with g hg ξ₀ hξ₀ R _
      exact e4_tendsto_supDistLU
        (e4_finalVersion_tendsto hd hX hE hg (hG g hg).1 (hG g hg).2 hξ₀) R
    exact ae_of_normLGFLaw (by omega) hcanon hh

end HigherDimLQGContinuity
