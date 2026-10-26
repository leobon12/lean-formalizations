import HigherDimLFPPAS.Normalizer.AEps
import HigherDimLQGMetric.Field.LGFPlusCont
import HigherDimLQGMetric.Sphere.Scaling

/-!
# Transfer of Assumption 1.1 (v) between normalized LGFs (packet N1; MA1 Details A3)

The events of (1.6), `{ω | δ ≤ sup_{B̄_R × B̄_R} edist (𝔞_ε⁻¹ D^ε_{h(ω)}, D_{h(ω)})}`, are preimages under the
field of sets of distributions that are null-measurable for the normalized law `normLGFLaw d`: the LFPP
distance of a continuous convolution field is continuous in both endpoints, each point evaluation is
a.e.-measurable, `D` is measurable, and the supremum reduces to a countable one
(`n1_nullMeasurableSet_lfppEvent`). Hence every two normalized LGFs, on any probability spaces, give
these events the same (outer) probability, and (1.6) for one normalized LGF is (1.6) for all of them
(`n1_tendstoInProbLU_transfer_of_cont`), in particular for the recentred rescaled fields `h^{z,r}`
(`n1_tendstoInProbLU_recentAff_of_cont`, `n1_tendstoInProbLU_paperRecentred_of_cont`; the paper's
`h^{z,r} = h(z + r ·) − h_r(z)` is a normalized LGF, `n1_isNormalizedLGF_paperRecentred`). The seed enters
only through the a.s. continuity of the convolution field (`hc`).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Filter Topology Set Metric
open scoped ENNReal

namespace HigherDimLFPPAS.Normalizer

open HigherDimLQGMetric
open HigherDimLFPP (Rd e₁)

/-- The point evaluations `g ↦ D_g(p)` of a measurable assignment are measurable. -/
theorem n1_measurable_apply {d : ℕ} {D : DistRd d → ContMetric d} (hDm : Measurable D)
    (p : Rd d × Rd d) : Measurable fun g : DistRd d => (D g).1 p :=
  ((continuous_eval_const p).comp continuous_subtype_val).measurable.comp hDm

/-- **Null-measurability of the events of (1.6)** for the normalized law: for any scalar `a`, set
`S ⊆ ℝ^d × ℝ^d` and level `c`, the set of distributions `g` with
`c ≤ sup_{p ∈ S} edist (a D^ε_g(p)) (D_g(p))` is null-measurable for `normLGFLaw d`. -/
theorem n1_nullMeasurableSet_lfppEvent {d : ℕ} {κ : Rd d → ℝ} (ξ : ℝ) {ε : ℝ}
    (hc : ∀ᵐ g ∂(normLGFLaw d), Continuous fun z => convMollify κ ε g z)
    {D : DistRd d → ContMetric d} (hDm : Measurable D) (a : ℝ) (S : Set (Rd d × Rd d))
    (c : ℝ≥0∞) :
    NullMeasurableSet {g : DistRd d | c ≤ ⨆ p ∈ S,
      edist ((a • lfppDist κ ξ ε g) p) ((D g).1 p)} (normLGFLaw d) := by
  refine n1_nullMeasurableSet_supEdist_ge (X := fun g => a • lfppDist κ ξ ε g)
    (Y := fun g => ⇑(D g).1) ?_ (Eventually.of_forall fun g => (D g).1.continuous) ?_ ?_ S c
  · filter_upwards [hc] with g hg
    exact (n1_continuous_lfppDist (ξ := ξ) hg).const_smul a
  · intro p
    exact (n1_aemeasurable_lfppDist ξ measurable_id hc p).const_smul a
  · intro p
    exact (n1_measurable_apply hDm p).aemeasurable

/-- **Equal probabilities of the events of (1.6)** for two normalized LGFs on arbitrary probability
spaces. -/
theorem n1_prob_lfppEvent_eq {d : ℕ} (hd : 2 ≤ d) {κ : Rd d → ℝ} (ξ : ℝ) {ε : ℝ}
    (hc : ∀ᵐ g ∂(normLGFLaw d), Continuous fun z => convMollify κ ε g z)
    {D : DistRd d → ContMetric d} (hDm : Measurable D) (a : ℝ) (S : Set (Rd d × Rd d))
    (c : ℝ≥0∞) {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω'] {P : Measure Ω}
    [IsProbabilityMeasure P] {P' : Measure Ω'} [IsProbabilityMeasure P'] {h : Ω → DistRd d}
    {g : Ω' → DistRd d} (hh : IsNormalizedLGF h P) (hg : IsNormalizedLGF g P') :
    P {ω | c ≤ ⨆ p ∈ S, edist ((a • lfppDist κ ξ ε (h ω)) p) ((D (h ω)).1 p)} =
      P' {ω | c ≤ ⨆ p ∈ S, edist ((a • lfppDist κ ξ ε (g ω)) p) ((D (g ω)).1 p)} :=
  n1_preimage_eq_preimage hd hh hg (n1_nullMeasurableSet_lfppEvent ξ hc hDm a S c)

/-- **Transfer of (1.6)** (MA1 A3): if the convolution fields of the normalized LGF are a.s. continuous
at every cutoff, then (1.6) for one normalized LGF `h` (on `(Ω, P)`) implies (1.6) for every normalized
LGF `g` on every probability space `(Ω', P')`. -/
theorem n1_tendstoInProbLU_transfer_of_cont {d : ℕ} (hd : 2 ≤ d) {κ : Rd d → ℝ} {ξ : ℝ}
    (hc : ∀ ε : ℝ, 0 < ε → ∀ᵐ g ∂(normLGFLaw d), Continuous fun z => convMollify κ ε g z)
    {D : DistRd d → ContMetric d} (hDm : Measurable D)
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P] {h : Ω → DistRd d}
    (hh : IsNormalizedLGF h P)
    (hconv : TendstoInProbLU P (fun ε ω => (aEps κ ξ ε)⁻¹ • lfppDist κ ξ ε (h ω)) (𝓝[>] 0)
      (fun ω => (D (h ω)).1))
    {Ω' : Type*} [MeasurableSpace Ω'] {P' : Measure Ω'} [IsProbabilityMeasure P']
    {g : Ω' → DistRd d} (hg : IsNormalizedLGF g P') :
    TendstoInProbLU P' (fun ε ω => (aEps κ ξ ε)⁻¹ • lfppDist κ ξ ε (g ω)) (𝓝[>] 0)
      (fun ω => (D (g ω)).1) := by
  intro R hR δ hδ
  refine (hconv R hR δ hδ).congr' ?_
  filter_upwards [self_mem_nhdsWithin] with ε hε
  exact n1_prob_lfppEvent_eq hd ξ (hc ε hε) hDm _ _ _ hh hg

/-- (1.6) for the recentred rescaled fields `recentAff r z h = h(r · + z) − (h(r · + z))_1(0)`. -/
theorem n1_tendstoInProbLU_recentAff_of_cont {d : ℕ} (hd : 2 ≤ d) {κ : Rd d → ℝ} {ξ : ℝ}
    (hc : ∀ ε : ℝ, 0 < ε → ∀ᵐ g ∂(normLGFLaw d), Continuous fun z => convMollify κ ε g z)
    {D : DistRd d → ContMetric d} (hDm : Measurable D)
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P] {h : Ω → DistRd d}
    (hh : IsNormalizedLGF h P)
    (hconv : TendstoInProbLU P (fun ε ω => (aEps κ ξ ε)⁻¹ • lfppDist κ ξ ε (h ω)) (𝓝[>] 0)
      (fun ω => (D (h ω)).1))
    {r : ℝ} (hr : 0 < r) (z : Rd d) :
    TendstoInProbLU P (fun ε ω => (aEps κ ξ ε)⁻¹ • lfppDist κ ξ ε (recentAff r z (h ω))) (𝓝[>] 0)
      (fun ω => (D (recentAff r z (h ω))).1) :=
  n1_tendstoInProbLU_transfer_of_cont hd hc hDm hh hconv (isNormalizedLGF_recentAff hd hh.1 hr z)

/-- The paper's recentred rescaled field `h^{z,r} = h(z + r ·) − h_r(z)` of a normalized LGF is a
normalized LGF. -/
theorem n1_isNormalizedLGF_paperRecentred {d : ℕ} (hd : 2 ≤ d) {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} {h : Ω → DistRd d} (hh : IsNormalizedLGF h P) {r : ℝ} (hr : 0 < r)
    (z : Rd d) :
    IsNormalizedLGF (fun ω => addConst (affineComp r z (h ω)) (-sphereAvg (h ω) r z)) P := by
  have hk : IsWholeSpaceLGF (fun ω => affineComp r z (h ω)) P := hh.1.affineComp hr z
  refine ⟨hk.addConst ((measurable_sphereAvg_left r z).comp hh.1.measurable).neg, ?_⟩
  filter_upwards [hk.ae_exists_tendsto_sphereAvgSeq hd one_pos 0,
    hh.1.ae_sphereAvg_affineComp hd hr z one_pos 0] with ω hconv hsph
  rw [sphereAvg_addConst_of_mem_convSet (by omega) hconv, hsph]
  simp only [mul_one, smul_zero, zero_add, add_neg_cancel]

/-- (1.6) for the paper's recentred rescaled fields `h^{z,r} = h(z + r ·) − h_r(z)` (MA1 MN-3: "(1.6)
for a field with the same law", l. 302 and l. 414–417). -/
theorem n1_tendstoInProbLU_paperRecentred_of_cont {d : ℕ} (hd : 2 ≤ d) {κ : Rd d → ℝ} {ξ : ℝ}
    (hc : ∀ ε : ℝ, 0 < ε → ∀ᵐ g ∂(normLGFLaw d), Continuous fun z => convMollify κ ε g z)
    {D : DistRd d → ContMetric d} (hDm : Measurable D)
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P] {h : Ω → DistRd d}
    (hh : IsNormalizedLGF h P)
    (hconv : TendstoInProbLU P (fun ε ω => (aEps κ ξ ε)⁻¹ • lfppDist κ ξ ε (h ω)) (𝓝[>] 0)
      (fun ω => (D (h ω)).1))
    {r : ℝ} (hr : 0 < r) (z : Rd d) :
    TendstoInProbLU P (fun ε ω => (aEps κ ξ ε)⁻¹ •
        lfppDist κ ξ ε (addConst (affineComp r z (h ω)) (-sphereAvg (h ω) r z))) (𝓝[>] 0)
      (fun ω => (D (addConst (affineComp r z (h ω)) (-sphereAvg (h ω) r z))).1) :=
  n1_tendstoInProbLU_transfer_of_cont hd hc hDm hh hconv
    (n1_isNormalizedLGF_paperRecentred hd hh hr z)

end HigherDimLFPPAS.Normalizer
