import HigherDimLQGMetric.LGF.Law
import HigherDimLQGMetric.Field.SphereBump
import HigherDimLQGMetric.Field.LGFPlusCont
import HigherDimLQGMetric.Frozen.NormLGFLaw

/-!
# The normalized LGF: existence and uniqueness of its law, reduced to sphere-average convergence
(packet F2, target 4)

Source: `source/higher-dimensional-lqg-metric.pdf` l. 57 ("we choose `h_1(0) = 0`"), l. 1573; the
sanity anchor `normLGFLaw_spec` (frozen, `DRAFT_SORRY`); MA3 D-LT (`NormalizedLawUnique`); S1
Details (a10) (`normLGFLaw_spec`: existence from F2, uniqueness from the a.s. convergence of the
mollified unit-sphere averages, which needs the sphere-average covariances of packet F3).

The only property of the sphere averages used here is the **a.s. convergence** of the mollified
unit-sphere averages `sphereAvgSeq (h ω) 1 0 n → h_1(0)` for whole-space LGFs (`SphereConvAS d`,
the case `r = 1`, `z = 0` of the frozen `sphereAvg_spec`, packet F3). Everything else is proved:

* `convSet`: the set of distributions whose unit-sphere averages at `0` converge; it is measurable
  for `sigma0` (convergence only depends on the mean-zero differences `⟨g, Ψ_n − Ψ_0⟩`), so its
  probability is the same for all LGFs (`ae_mem_convSet_of_exists`: convergence for one LGF implies
  convergence for every LGF);
* `sphereAvg_addConst_of_mem_convSet`: on `convSet`, `(g + c)_1(0) = g_1(0) + c`;
* `IsWholeSpaceLGF.isNormalizedLGF_normalize`: `h − h_1(0)` is a normalized LGF;
* `isNormalizedLGF_map_id`: the law of a normalized LGF is a normalized LGF on `𝒟'(ℝ^d)`;
* `IsNormalizedLGF.map_eq`: two normalized LGFs have the same law on `𝒟'(ℝ^d)`;
* `normLGFLaw_spec_of_sphereConv` (**the reduction**): `SphereConvAS d` and the existence of one
  LGF (target 1, `exists_isWholeSpaceLGF`) imply the frozen statement of `normLGFLaw_spec` at `d`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set

namespace HigherDimLQGMetric

open HigherDimLFPP (Rd)

variable {d : ℕ}

/-! ## The convergence set of the unit-sphere averages at the origin -/

/-- Distributions whose mollified unit-sphere averages at `0` converge. -/
def convSet (d : ℕ) : Set (DistRd d) :=
  {g | ∃ a, Tendsto (sphereAvgSeq g 1 0) atTop (𝓝 a)}

/-- **The input from packet F3** (case `r = 1`, `z = 0` of the frozen `sphereAvg_spec`): for every
whole-space LGF, the mollified unit-sphere averages at `0` converge almost surely. -/
def SphereConvAS (d : ℕ) : Prop :=
  ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) (h : Ω → DistRd d),
    IsWholeSpaceLGF h P → ∀ᵐ ω ∂P, h ω ∈ convSet d

theorem measurableSet_convSet : MeasurableSet (convSet d) :=
  measurableSet_exists_tendsto_sphereAvgSeq 1 0

theorem exists_tendsto_iff_sub_const (s : ℕ → ℝ) (b : ℝ) :
    (∃ a, Tendsto s atTop (𝓝 a)) ↔ ∃ a, Tendsto (fun n => s n - b) atTop (𝓝 a) := by
  constructor
  · rintro ⟨a, ha⟩
    exact ⟨a - b, ha.sub_const b⟩
  · rintro ⟨a, ha⟩
    refine ⟨a + b, ?_⟩
    have := ha.add_const b
    simpa only [sub_add_cancel] using this

/-- `convSet` only depends on the mean-zero pairings `⟨g, Ψ_n − Ψ_0⟩`: it is `sigma0`-measurable. -/
theorem measurableSet_convSet_sigma0 (hd : 1 ≤ d) : MeasurableSet[sigma0 d] (convSet d) := by
  set T : Set (TestRd0 d → ℝ) :=
    {a | ∃ c, Tendsto (fun n => a (sphDiff0 hd n 0 1 0 0 1)) atTop (𝓝 c)} with hT
  have hTm : MeasurableSet T :=
    MeasureTheory.measurableSet_exists_tendsto fun n => measurable_pi_apply _
  refine ⟨T, hTm, ?_⟩
  ext g
  simp only [mem_preimage, hT, mem_ofPred_eq, convSet]
  have e : (fun n => ev0 g (sphDiff0 hd n 0 1 0 0 1)) =
      fun n => sphereAvgSeq g 1 0 n - sphereAvgSeq g 1 0 0 := by
    funext n
    rw [sphereAvgSeq_sub_eq_apply_sphDiff]
    rfl
  rw [e, ← exists_tendsto_iff_sub_const]

/-- Convergence of the unit-sphere averages for one LGF implies it for every LGF (law transfer on
`sigma0`). -/
theorem ae_mem_convSet_of_ae_mem {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    {P : Measure Ω} {P' : Measure Ω'} {h : Ω → DistRd d} {h' : Ω' → DistRd d} (hd : 1 ≤ d)
    (hh : IsWholeSpaceLGF h P) (hh' : IsWholeSpaceLGF h' P')
    (hconv : ∀ᵐ ω ∂P, h ω ∈ convSet d) : ∀ᵐ ω ∂P', h' ω ∈ convSet d := by
  have hc : MeasurableSet[sigma0 d] (convSet d)ᶜ := (measurableSet_convSet_sigma0 hd).compl
  have e := measure_preimage_eq_of_sigma0 hc hh hh'
  rw [ae_iff] at hconv ⊢
  have h1 : {ω | ¬h ω ∈ convSet d} = h ⁻¹' (convSet d)ᶜ := rfl
  have h2 : {ω | ¬h' ω ∈ convSet d} = h' ⁻¹' (convSet d)ᶜ := rfl
  rw [h2, ← e, ← h1, hconv]

/-- `SphereConvAS d` follows from the a.s. convergence for a single LGF (e.g. the white-noise
realization of target 1). -/
theorem sphereConvAS_of_exists (hd : 1 ≤ d)
    (hex : ∃ (Ω : Type) (_ : MeasurableSpace Ω) (P : Measure Ω) (h : Ω → DistRd d),
      IsWholeSpaceLGF h P ∧ ∀ᵐ ω ∂P, h ω ∈ convSet d) : SphereConvAS d := by
  obtain ⟨Ω₀, _, P₀, h₀, hh₀, hc₀⟩ := hex
  intro Ω _ P h hh
  exact ae_mem_convSet_of_ae_mem hd hh₀ hh hc₀

/-- On `convSet`, adding a constant shifts the unit-sphere average by that constant. -/
theorem sphereAvg_addConst_of_mem_convSet (hd : 1 ≤ d) {g : DistRd d} (hg : g ∈ convSet d)
    (c : ℝ) : sphereAvg (addConst g c) 1 0 = sphereAvg g 1 0 + c := by
  obtain ⟨a, ha⟩ := hg
  exact sphereAvg_addConst_of_tendsto hd ha c

/-! ## Normalization by the unit-sphere average -/

variable {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω'] {P : Measure Ω}
  {P' : Measure Ω'}

/-- `h − h_1(0)` is a normalized LGF, provided the unit-sphere averages of `h` converge a.s. -/
theorem IsWholeSpaceLGF.isNormalizedLGF_normalize (hd : 1 ≤ d) {h : Ω → DistRd d}
    (hh : IsWholeSpaceLGF h P) (hconv : ∀ᵐ ω ∂P, h ω ∈ convSet d) :
    IsNormalizedLGF (fun ω => HigherDimLQGMetric.addConst (h ω) (-sphereAvg (h ω) 1 0)) P := by
  refine ⟨hh.addConst ((measurable_sphereAvg_left 1 0).comp hh.measurable).neg, ?_⟩
  filter_upwards [hconv] with ω hω
  rw [sphereAvg_addConst_of_mem_convSet hd hω, add_neg_cancel]

/-- The law of a normalized LGF is (the law of) a normalized LGF on `𝒟'(ℝ^d)`. -/
theorem IsNormalizedLGF.map_id {h : Ω → DistRd d} (hh : IsNormalizedLGF h P) :
    IsNormalizedLGF (id : DistRd d → DistRd d) (P.map h) := by
  refine ⟨hh.1.map_id, ?_⟩
  have hS : MeasurableSet {k : DistRd d | sphereAvg k 1 0 = 0} :=
    measurableSet_eq_fun (measurable_sphereAvg_left 1 0) measurable_const
  show ∀ᵐ k ∂(P.map h), sphereAvg k 1 0 = 0
  rw [ae_map_iff hh.1.measurable.aemeasurable hS]
  exact hh.2

/-- A mean-one test function: `∫ ψ_{0,0} = 1`. -/
theorem integral_bumpTest_zero : ∫ x, bumpTest 0 (0 : Rd d) x = 1 := integral_bumpTest 0 0

/-- **Uniqueness of the normalized law**: under `SphereConvAS d` (packet F3), any two normalized
LGFs have the same law on `𝒟'(ℝ^d)`. -/
theorem IsNormalizedLGF.map_eq (hd : 1 ≤ d) {h : Ω → DistRd d} {h' : Ω' → DistRd d}
    (hh : IsNormalizedLGF h P) (hh' : IsNormalizedLGF h' P')
    (hconv : ∀ᵐ ω ∂P, h ω ∈ convSet d) (hconv' : ∀ᵐ ω ∂P', h' ω ∈ convSet d) :
    P.map h = P'.map h' := by
  refine map_eq_of_normalized_ae integral_bumpTest_zero (measurable_sphereAvg_left 1 0) hh.1 hh'.1
    ?_ ?_ hh.2 hh'.2
  · filter_upwards [hconv] with ω hω c using sphereAvg_addConst_of_mem_convSet hd hω c
  · filter_upwards [hconv'] with ω hω c using sphereAvg_addConst_of_mem_convSet hd hω c

/-- Uniqueness on the canonical space: two probability laws of normalized LGFs on `𝒟'(ℝ^d)`
agree. -/
theorem normalized_law_unique (hd : 1 ≤ d) (hS : SphereConvAS d) {μ ν : Measure (DistRd d)}
    (hμ : IsNormalizedLGF id μ) (hν : IsNormalizedLGF id ν) : μ = ν := by
  have e := IsNormalizedLGF.map_eq hd hμ hν (hS μ id hμ.1) (hS ν id hν.1)
  simpa only [Measure.map_id] using e

/-- **The reduction for the sanity anchor `normLGFLaw_spec`** (target 4): if some whole-space LGF
exists (target 1, `exists_isWholeSpaceLGF`) and the unit-sphere averages of every LGF converge a.s.
(`SphereConvAS d`, packet F3), then `normLGFLaw d` is a probability measure, it is the law of a
normalized LGF, and it is the only such law (the frozen statement of `normLGFLaw_spec` at `d`). -/
theorem normLGFLaw_spec_of_sphereConv (hd : 1 ≤ d)
    (hex : ∃ (Ω : Type) (_ : MeasurableSpace Ω) (P : Measure Ω) (h : Ω → DistRd d),
      IsWholeSpaceLGF h P)
    (hS : SphereConvAS d) :
    IsProbabilityMeasure (normLGFLaw d) ∧ IsNormalizedLGF id (normLGFLaw d) ∧
      ∀ μ : Measure (DistRd d), IsProbabilityMeasure μ → IsNormalizedLGF id μ →
        μ = normLGFLaw d := by
  obtain ⟨Ω₀, _, P₀, h₀, hh₀⟩ := hex
  have hn₀ := hh₀.isNormalizedLGF_normalize hd (hS P₀ h₀ hh₀)
  have := hh₀.gaussian.isProbabilityMeasure
  have hex' : ∃ μ : Measure (DistRd d), IsProbabilityMeasure μ ∧ IsNormalizedLGF id μ :=
    ⟨P₀.map fun ω => addConst (h₀ ω) (-sphereAvg (h₀ ω) 1 0),
      inferInstance, hn₀.map_id⟩
  have hlaw : normLGFLaw d = hex'.choose := by
    rw [normLGFLaw, dite_eq_left hex']
  have hspec := hex'.choose_spec
  rw [hlaw]
  exact ⟨hspec.1, hspec.2, fun μ _ hμ => normalized_law_unique hd hS hμ hspec.2⟩

/-- `SphereConvAS d` follows from the statement of the frozen characterization anchor
`sphereAvg_spec` at `d` (case `r = 1`, `z = 0`; an LGF is an LGF plus the continuous function
`0`). -/
theorem sphereConvAS_of_sphereAvg_spec {d : ℕ}
    (hspec : ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
      (h : Ω → DistRd d), IsLGFPlusCont h P → ∀ r : ℝ, 0 < r → ∀ z : Rd d,
        ∀ᵐ ω ∂P, Tendsto (fun n : ℕ => ∫ u, h ω (bumpTest n (z + r • u)) ∂(unitSphereProb d))
          atTop (𝓝 (sphereAvg (h ω) r z))) :
    SphereConvAS d := by
  intro Ω _ P h hh
  have := hh.gaussian.isProbabilityMeasure
  filter_upwards [hspec P h hh.isLGFPlusCont 1 one_pos 0] with ω hω
  exact ⟨_, hω⟩

/-- **The reduction `normLGFLaw_spec ⇐ sphereAvg_spec`** (target 4): the statement of the frozen
characterization anchor `sphereAvg_spec` implies the statement of the frozen sanity anchor
`normLGFLaw_spec` (existence of the LGF is target 1, `exists_isWholeSpaceLGF`; uniqueness of the
normalized law is `normalized_law_unique`). Both statements are copied verbatim from the frozen
anchors (which are not imported). -/
theorem normLGFLaw_spec_of_sphereAvg_spec
    (hex : ∀ d : ℕ, 2 ≤ d → ∃ (Ω : Type) (_ : MeasurableSpace Ω) (P : Measure Ω)
      (h : Ω → DistRd d), IsWholeSpaceLGF h P)
    (hspec : ∀ (d : ℕ), 2 ≤ d → ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
      [IsProbabilityMeasure P] (h : Ω → DistRd d), IsLGFPlusCont h P → ∀ r : ℝ, 0 < r →
        ∀ z : Rd d, ∀ᵐ ω ∂P, Tendsto (fun n : ℕ => ∫ u, h ω (bumpTest n (z + r • u))
          ∂(unitSphereProb d)) atTop (𝓝 (sphereAvg (h ω) r z))) :
    ∀ (d : ℕ), 2 ≤ d → IsProbabilityMeasure (normLGFLaw d) ∧ IsNormalizedLGF id (normLGFLaw d) ∧
      ∀ μ : Measure (DistRd d), IsProbabilityMeasure μ → IsNormalizedLGF id μ →
        μ = normLGFLaw d :=
  fun d hd => normLGFLaw_spec_of_sphereConv (by omega) (hex d hd)
    (sphereConvAS_of_sphereAvg_spec (hspec d hd))

end HigherDimLQGMetric
