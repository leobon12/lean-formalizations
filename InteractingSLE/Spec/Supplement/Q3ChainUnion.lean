/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.Q3ChainMeas
import InteractingSLE.Spec.Sec7.SideHeightHull
import InteractingSLE.Spec.Sec6.Prop61Mean
import InteractingSLE.Impl.ForceBoundaryData

/-!
# The counterflow's own hull mean at its flowed marks

Packet PROVE-Q3-REL3, item (B) of `planning/handoffs/PROVE-Q3-REL.md` §4.2: the input `hind₂` of
`Q3Rel.ae_eqOn_unionMean_of_relConfigOff` for GB6 (the explored hull is the counterflow's own hull `K'_t` at a
deterministic time).

* `exists_measurable_hull_version`: a hitting-measurable version of the counterflow hull (read from the killed history);
* `ae_eqOn_unionMean_of_relConfigOff_ver`: PROVE-Q3-REL's union mean with a version of the explored hull;
* **`ae_eqOn_unionMean_gb6`**: GB6's union mean at deterministic times from the union-law inputs;
* **`ae_eqOn_cfMean`**: for an optional hull coupling of a counterflow word (any parameter `k > 0`, angle `0`, from
  `0`) of almost surely infinite lifetime, a hitting-measurable hull `K'_t` and a local-set mean `g₂` of `K'_t` for
  the centred field: almost surely, every harmonic representative `w₂` of `g₂` off `K'_t` satisfies
  `w₂ + 𝔥⁰ = G_E ∘ f_t − χ arg f_t′` off `K'_t`, for every bounded harmonic extension `G_E` of the counterflow's
  force data **at its flowed marks** (`cfFlowedData k b J W t`). Proof:
  `Sec7.SideHeight.ae_apply_eq_of_isLocalSetMean_flowHull`
  (the hull mean of a coupling), `Q3Chain.ae_gap_eq_markPos` (the coupling's marks are the flowed marks), uniqueness of
  bounded harmonic extensions and of harmonic functions with the same test integrals.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Filter Set Topology
open scoped NNReal ENNReal
open QuantumZipper (H fwdMap fwdMapInv fwdHull logDerivFwd)
open LQGMetric (DistOn TestOn)

universe u

namespace InteractingSLE.Supp8.Q3Chain

open LocalSets

/-- **The counterflow's own hull mean at its flowed marks** (`hind₂` of `Q3Rel.ae_eqOn_unionMean_of_relConfigOff`). -/
theorem ae_eqOn_cfMean {k : ℝ} (hk : 0 < k) {b' : ℝ → ℝ} {J' : Finset ℝ} {Ω : Type u} {mΩ : MeasurableSpace Ω}
    {P : Measure Ω} [IsProbabilityMeasure P] {𝓕 : Filtration ℝ≥0 mΩ} {W : ℝ≥0 → Ω → ℝ}
    {VL : Fin (flowLineNL b' J' 0) → ℝ≥0 → Ω → ℝ} {VR : Fin (flowLineNR b' J' 0) → ℝ≥0 → Ω → ℝ}
    {B : ℝ≥0 → Ω → ℝ} {ζ : Ω → ℝ≥0∞} {h' : Ω → DistOn upperHalfPlaneOpens}
    (hC : IsOptionalHullCoupling k (flowLineXL b' J' 0) (flowLineXR b' J' 0) (flowLineRhoL k b' J' 0 0)
      (flowLineRhoR k b' J' 0 0) P 𝓕 W VL VR B ζ h')
    (hζ : ∀ᵐ ω ∂P, ζ ω = ⊤) {u₀ : ℂ → ℝ}
    (hu₀ : IsBoundedHarmonicExtension (cfData k b' J') (forceJumpSet (flowLineXL b' J' 0) (flowLineXR b' J' 0)) u₀)
    (hh0 : LQGMetric.IsZeroBoundaryGFF upperHalfPlaneOpens (WholeField.centredField h' u₀) P) (t : ℝ≥0)
    {K : Ω → Set ℂ} (hKeq : ∀ᵐ ω ∂P, K ω = fwdHull (fun r : ℝ => W r.toNNReal ω) t)
    (hKm : Measurable[mΩ, hittingSigma] K) {g₂ : Ω → DistOn upperHalfPlaneOpens}
    (hg₂ : IsLocalSetMean K (WholeField.centredField h' u₀) P g₂) :
    ∀ᵐ ω ∂P, Continuous (fun r => W r ω) → W 0 ω = 0 →
      ∀ GE : ℂ → ℝ, IsBoundedHarmonicExtension (cfFlowedData k b' J' (fun r : ℝ => W r.toNNReal ω) t)
          (cfFlowedJumps b' J' (fun r : ℝ => W r.toNNReal ω) t) GE →
        ∀ w₂ : ℂ → ℝ, InnerProductSpace.HarmonicOnNhd w₂ (H \ K ω) →
          (∀ φ : TestOn upperHalfPlaneOpens, tsupport φ ⊆ H \ K ω → g₂ ω φ = ∫ z, w₂ z * φ z) →
          EqOn (fun z => w₂ z + u₀ z)
            (fun z => GE (fwdMap (fun r : ℝ => W r.toNNReal ω) t z) -
              QuantumZipper.chiC k * (logDerivFwd (fun r : ℝ => W r.toNNReal ω) t z).im)
            (H \ K ω) := by
  classical
  -- bounded harmonic extensions of the coupling's force data at `t`
  set u : Ω → ℂ → ℝ := fun ω => (Sec7.StripSysField.exists_isBoundedHarmonicExtension_forceBoundaryData k
    (flowLineRhoL k b' J' 0 0) (flowLineRhoR k b' J' 0 0) (fun i => VL i t ω - W t ω)
    (fun j => VR j t ω - W t ω)).choose with hudef
  have hu : ∀ ω, IsBoundedHarmonicExtension
      (forceBoundaryData k (flowLineRhoL k b' J' 0 0) (flowLineRhoR k b' J' 0 0)
        (fun i => VL i (((fun _ : Ω => ((t : ℝ≥0) : WithTop ℝ≥0)) ω).untopD 0) ω -
          W (((fun _ : Ω => ((t : ℝ≥0) : WithTop ℝ≥0)) ω).untopD 0) ω)
        (fun i => VR i (((fun _ : Ω => ((t : ℝ≥0) : WithTop ℝ≥0)) ω).untopD 0) ω -
          W (((fun _ : Ω => ((t : ℝ≥0) : WithTop ℝ≥0)) ω).untopD 0) ω))
      (forceJumpSet (fun i => VL i (((fun _ : Ω => ((t : ℝ≥0) : WithTop ℝ≥0)) ω).untopD 0) ω -
          W (((fun _ : Ω => ((t : ℝ≥0) : WithTop ℝ≥0)) ω).untopD 0) ω)
        (fun i => VR i (((fun _ : Ω => ((t : ℝ≥0) : WithTop ℝ≥0)) ω).untopD 0) ω -
          W (((fun _ : Ω => ((t : ℝ≥0) : WithTop ℝ≥0)) ω).untopD 0) ω)) (u ω) := fun ω => by
    simp only [WithTop.untopD_coe]
    exact (Sec7.StripSysField.exists_isBoundedHarmonicExtension_forceBoundaryData k
      (flowLineRhoL k b' J' 0 0) (flowLineRhoR k b' J' 0 0) (fun i => VL i t ω - W t ω)
      (fun j => VR j t ω - W t ω)).choose_spec
  have hX := hC.2.2.2.1
  have hτζ : ∀ᵐ ω ∂P, ((((fun _ : Ω => ((t : ℝ≥0) : WithTop ℝ≥0)) ω) : WithTop ℝ≥0) : ℝ≥0∞) < ζ ω := by
    filter_upwards [hζ] with ω hω
    rw [hω]
    exact ENNReal.coe_lt_top
  have htr : ∀ ω, IsTranslateAddConst 0 (0 * 0) (h' ω) (h' ω) := fun ω =>
    Sec7.StripSysField.isTranslateAddConst_zero_self (h' ω) 0
  have hmean := Sec7.SideHeight.ae_apply_eq_of_isLocalSetMean_flowHull hC hk htr hh0 hu₀.1 hu₀
    (fun z _ => by simp) hX (isStoppingTime_const _ t) hτζ hKm
    (by
      filter_upwards [hKeq] with ω hω
      simp only [hω, WithTop.untopD_coe, Complex.ofReal_zero, add_zero, image_id']) hg₂ hu
  filter_upwards [hmean, ae_gap_eq_markPos hC, hζ, hKeq] with ω hmω hgap hζω hKω hWc hW0
  rw [hKω] at hmω ⊢
  intro GE hGE w₂ hw₂ hrep
  have hD : Continuous fun r : ℝ => W r.toNNReal ω := hWc.comp continuous_real_toNNReal
  have hD0 : (fun r : ℝ => W r.toNNReal ω) 0 = 0 := by simp [hW0]
  have hlt : ((t : ℝ≥0) : ℝ≥0∞) < ζ ω := by rw [hζω]; exact ENNReal.coe_lt_top
  obtain ⟨hL, hR⟩ := hgap _ hD hD0 t hlt fun s _ => by simp
  -- the coupling's extension is the flowed one
  have huω : IsBoundedHarmonicExtension (cfFlowedData k b' J' (fun r : ℝ => W r.toNNReal ω) t)
      (cfFlowedJumps b' J' (fun r : ℝ => W r.toNNReal ω) t) (u ω) := by
    have h1 := hu ω
    simp only [WithTop.untopD_coe] at h1
    rw [forceBoundaryData_gap_eq_cfFlowedData hL hR, forceJumpSet_gap_eq_cfFlowedJumps hL hR] at h1
    exact h1
  have hGEu : EqOn GE (u ω) H :=
    Impl.eqOn_of_isBoundedHarmonicExtension (Finset.finite_toSet _) huω hGE
  -- the two harmonic representatives
  have hO : IsOpen (H \ fwdHull (fun r : ℝ => W r.toNNReal ω) t) :=
    QuantumZipper.FwdHolo.isOpen_compl_fwdHull hD t.2
  have hcm := Sec7.SideHeight.harmonicOnNhd_couplingMean (κ := k) hD t.coe_nonneg huω.1
  have hm2 : InnerProductSpace.HarmonicOnNhd
      (fun z => couplingMean k (fun r : ℝ => W r.toNNReal ω) t (u ω) z - u₀ z)
      (H \ fwdHull (fun r : ℝ => W r.toNNReal ω) t) := fun z hz =>
    (hcm z hz).sub (hu₀.1 z hz.1)
  have heq : EqOn w₂ (fun z => couplingMean k (fun r : ℝ => W r.toNNReal ω) t (u ω) z - u₀ z)
      (H \ fwdHull (fun r : ℝ => W r.toNNReal ω) t) := by
    refine Sec6.eqOn_of_integral_mul_eq hO sdiff_subset hw₂ hm2 fun φ hφ => ?_
    rw [← hrep φ hφ, hmω φ hφ]
    refine integral_congr_ae (Eventually.of_forall fun z => ?_)
    simp only [Complex.ofReal_zero, sub_zero, mul_zero]
    rfl
  intro z hz
  have h1 := heq hz
  have h2 := hGEu (QuantumZipper.FwdHolo.mapsTo_fwdMap hD t.coe_nonneg hz)
  simp only [couplingMean] at h1
  show w₂ z + u₀ z = GE (fwdMap (fun r : ℝ => W r.toNNReal ω) t z) -
    QuantumZipper.chiC k * (logDerivFwd (fun r : ℝ => W r.toNNReal ω) t z).im
  rw [h1]
  linarith


/-- **A hitting-measurable version of the counterflow hull at a deterministic time** (the hull read from the killed
driving history, `Sec5.GlueCond.hullAt`): for an optional hull coupling of almost surely infinite lifetime. -/
theorem exists_measurable_hull_version {k : ℝ} {nL nR : ℕ} {xL : Fin nL → ℝ} {xR : Fin nR → ℝ} {ρL : Fin nL → ℝ}
    {ρR : Fin nR → ℝ} {Ω : Type u} {mΩ : MeasurableSpace Ω} {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    {W : ℝ≥0 → Ω → ℝ} {VL : Fin nL → ℝ≥0 → Ω → ℝ} {VR : Fin nR → ℝ≥0 → Ω → ℝ} {B : ℝ≥0 → Ω → ℝ}
    {ζ : Ω → ℝ≥0∞} {h' : Ω → DistOn upperHalfPlaneOpens}
    (hC : IsOptionalHullCoupling k xL xR ρL ρR P 𝓕 W VL VR B ζ h') (hζ : ∀ᵐ ω ∂P, ζ ω = ⊤) (t : ℝ≥0) :
    ∃ K : Ω → Set ℂ, Measurable[mΩ, hittingSigma] K ∧
      ∀ᵐ ω ∂P, K ω = fwdHull (fun r : ℝ => W r.toNNReal ω) t := by
  obtain ⟨hX, -⟩ := hC.2.2.2
  refine ⟨fun ω => Sec5.GlueCond.hullAt t (LawUnique.killedHistory W VL VR ζ ω),
    (Sec5.GlueCond.measurable_hullAt t).comp (LawUnique.measurable_killedHistory hX), ?_⟩
  filter_upwards [Aux50Hit.ae_isGoodPath hC.1 hζ] with ω hg
  exact Aux50Hit.regHull_stopHistory_cstop hg t

/-! ### The union mean with a version of the explored hull -/

/-- **`Q3Rel.ae_eqOn_unionMean_of_relConfigOff` with a version `K` of the explored hull**: the same conclusion for any
random set `K` equal almost surely on `D` to the explored hull `K_t` (so that a hitting-measurable version can be
used). Same proof (`SB.SewGerm.ae_survivingWordBoundary_union`, `SB.SewGerm.ae_eqOn_physicalMean_of_boundary`). -/
theorem ae_eqOn_unionMean_of_relConfigOff_ver
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {h : Ω → DistOn upperHalfPlaneOpens} {u₀ : ℂ → ℝ}
    (hh0 : LQGMetric.IsZeroBoundaryGFF upperHalfPlaneOpens (WholeField.centredField h u₀) P)
    (hu₀ : InnerProductSpace.HarmonicOnNhd u₀ H) (hu₀b : ∃ M : ℝ, ∀ z ∈ H, |u₀ z| ≤ M)
    {A K : Ω → Set ℂ} {Ψ Ψi LΨ : Ω → ℂ → ℂ} {Sb : Ω → Finset ℝ} {w Wr : Ω → ℝ → ℝ} {η ηr : Ω → ℝ → ℂ}
    {t u : Ω → ℝ} {χ lam : ℝ}
    {β₀ βE βu : Ω → ℝ → ℝ} {S₀ SE Su : Ω → Finset ℝ} {G₀ GE G v : Ω → ℂ → ℝ}
    (hAm : Measurable[mΩ, hittingSigma] A) (hKm : Measurable[mΩ, hittingSigma] K)
    (hdA : MeasurableSpace.comap A hittingSigma ≤
      aeSigma (MeasurableSpace.comap (WholeField.centredField h u₀) inferInstance) P)
    (hlA : IsLocalSet A (WholeField.centredField h u₀) P)
    (hlK : IsLocalSet K (WholeField.centredField h u₀) P)
    (hlU : IsLocalSet (fun ω => A ω ∪ K ω) (WholeField.centredField h u₀) P)
    (hunbA : ∀ᵐ ω ∂P, ∀ z ∈ lowerUnion (A ω),
      ¬ Bornology.IsBounded (connectedComponentIn (lowerUnion (A ω)) z))
    (hunbK : ∀ᵐ ω ∂P, ∀ z ∈ lowerUnion (K ω),
      ¬ Bornology.IsBounded (connectedComponentIn (lowerUnion (K ω)) z))
    {g g₁ g₂ : Ω → DistOn upperHalfPlaneOpens}
    (hg : IsLocalSetMean (fun ω => A ω ∪ K ω) (WholeField.centredField h u₀) P g)
    (hg₁ : IsLocalSetMean A (WholeField.centredField h u₀) P g₁)
    (hg₂ : IsLocalSetMean K (WholeField.centredField h u₀) P g₂)
    {D : Set Ω} (hKeq : ∀ᵐ ω ∂P, ω ∈ D → K ω = fwdHull (w ω) (t ω))
    (hcfg : ∀ᵐ ω ∂P, ω ∈ D → Q3Rel.IsRelConfigOff (A ω) (Ψ ω) (Ψi ω) (LΨ ω) (Sb ω) (w ω) (Wr ω) (η ω) (ηr ω) (t ω)
      (u ω) χ lam (β₀ ω) (βE ω) (βu ω) (S₀ ω) (SE ω) (Su ω) (G₀ ω) (GE ω) (G ω) (v ω))
    (hind₁ : ∀ᵐ ω ∂P, ω ∈ D → ∀ w₁ : ℂ → ℝ, InnerProductSpace.HarmonicOnNhd w₁ (H \ A ω) →
      (∀ φ : TestOn upperHalfPlaneOpens, tsupport φ ⊆ H \ A ω → g₁ ω φ = ∫ z, w₁ z * φ z) →
      EqOn (fun z => w₁ z + u₀ z) (fun z => G₀ ω (Ψ ω z) - χ * (LΨ ω z).im) (H \ A ω))
    (hind₂ : ∀ᵐ ω ∂P, ω ∈ D → ∀ w₂ : ℂ → ℝ, InnerProductSpace.HarmonicOnNhd w₂ (H \ K ω) →
      (∀ φ : TestOn upperHalfPlaneOpens, tsupport φ ⊆ H \ K ω → g₂ ω φ = ∫ z, w₂ z * φ z) →
      EqOn (fun z => w₂ z + u₀ z) (fun z => GE ω (fwdMap (w ω) (t ω) z) - χ * (logDerivFwd (w ω) (t ω) z).im)
        (H \ K ω)) :
    ∀ᵐ ω ∂P, ω ∈ D → ∀ wU : ℂ → ℝ, InnerProductSpace.HarmonicOnNhd wU (H \ (A ω ∪ K ω)) →
      (∀ φ : TestOn upperHalfPlaneOpens, tsupport φ ⊆ H \ (A ω ∪ K ω) → g ω φ = ∫ z, wU z * φ z) →
      EqOn (fun z => wU z + u₀ z) (v ω) (H \ (A ω ∪ K ω)) := by
  have hword : ∀ᵐ ω ∂P, ω ∈ D → ∀ w₁ w₂ : ℂ → ℝ,
      InnerProductSpace.HarmonicOnNhd w₁ (H \ A ω) →
      (∀ φ : TestOn upperHalfPlaneOpens, tsupport φ ⊆ H \ A ω → g₁ ω φ = ∫ z, w₁ z * φ z) →
      InnerProductSpace.HarmonicOnNhd w₂ (H \ K ω) →
      (∀ φ : TestOn upperHalfPlaneOpens, tsupport φ ⊆ H \ K ω → g₂ ω φ = ∫ z, w₂ z * φ z) →
      Theorem14.SB.SewGerm.HasUnionWordBoundary (A ω) (K ω) u₀ (v ω) w₁ w₂ χ (βu ω) (Su ω) := by
    filter_upwards [hcfg, hind₁, hind₂, hKeq] with ω hc h1 h2 hK hωD w₁ w₂ hw₁ hr₁ hw₂ hr₂
    have e := hK hωD
    have h2' := h2 hωD
    rw [e] at hw₂ hr₂ h2' ⊢
    exact (hc hωD).hasUnionWordBoundary (h1 hωD w₁ hw₁ hr₁) (h2' w₂ hw₂ hr₂)
  have hsurv := Theorem14.SB.SewGerm.ae_survivingWordBoundary_union hh0 hAm hKm hdA hlA hlK hunbA hunbK hg hg₁ hg₂
    u₀ v χ βu Su hword
  exact Theorem14.SB.SewGerm.ae_eqOn_physicalMean_of_boundary hh0 hu₀ hu₀b (measurable_union_hitting hAm hKm) hlU
    hg χ hsurv

/-! ### GB6's union mean at deterministic times -/

open GB6 (relMap relInv relClock firstContactTime sphereInv gb6WordOfRec gb6Rec)
open Q3Rel (invHull relLog relBad IsRelConfigOff)

/-- **GB6's union mean at deterministic times, from the union-law inputs** (Astra's follow-up 3, Q3 §3.3 for GB6;
supplement p. 519–520, "Thus the conditional Poisson mean is exactly the evolving finite word"). Counterflow frame: the
counterflow is an optional hull coupling of its word `(b', J')` at `16/κ` (field `h'`, driver `W`, infinite lifetime,
complete traces), the flow prefix `α[0, s]` (an `IsFlowLineDriver` at `κ` of the original field) is read as the
retained set `A = −1/K^α_s` (`invHull`), and `K = K'_t` is the counterflow hull at the deterministic time `t > 0`.
`A` and the explored hull `K` are versions: `A = invHull Uω s` almost surely on `E ∩ {s < ζα}`, `A` is almost
surely the inversion of a compact `ℍ`-hull (e.g. the reflected flow hull at a stop), and `K = K'_t` almost surely
(e.g. the hull read from the killed history, `exists_measurable_hull_version`).

On the event `D = E ∩ {s < ζα, α(s) ∈ ℍ, t < T_c}`, the harmonic representative `w_U` of the local-set mean of `A ∪ K`
(for the centred field `h' − 𝔥⁰`) satisfies `w_U + 𝔥⁰ = G ∘ g̃_u ∘ Ψ − χ (arg g̃_u′ ∘ Ψ + Im relLog)`, where `Ψ` is
GB6's retained chart, `(Wr, u)` the relative chain with `Ψ(K) = K̃_u`, and `G` a bounded harmonic extension of the
**relative word**: the chart field's word `β = gb6WordOfRec κ θ c r` at the marks flowed by `Wr` to `u`.

Inputs not proved here (those of `Q3Rel.ae_eqOn_unionMean_of_relConfigOff` that are about the field): hitting-
measurability of `A` and `K`, field-determination of `A`, locality of `A` and of `A ∪ K`, and the retained-set mean
`hind₁` (the chart field's word through `Ψ`). Proved here: the configuration with GB6's actual words
(`ae_isRelConfigOff_gb6_flow`), the locality of `K`, the unbounded components, and the explored-hull mean `hind₂`
(`ae_eqOn_cfMean`). -/
theorem ae_eqOn_unionMean_gb6 {κ : ℝ} (hκ : 0 < κ) (hκ4 : κ < 4) {b : ℝ → ℝ} {J : Finset ℝ} {θ : ℝ}
    {Ω : Type u} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {h : Ω → DistOn upperHalfPlaneOpens} {Wα : ℝ≥0 → Ω → ℝ} {ζα : Ω → ℝ≥0∞} {α γ : Ω → ℝ≥0 → ℂ}
    (hF : IsFlowLineDriver κ b J θ P h Wα ζα) (hα : ∀ᵐ ω ∂P, IsGeneratingTrace (fun t => Wα t ω) (ζα ω) (α ω))
    {b' : ℝ → ℝ} {J' : Finset ℝ} {𝓕 : Filtration ℝ≥0 mΩ} {W : ℝ≥0 → Ω → ℝ}
    {VL : Fin (flowLineNL b' J' 0) → ℝ≥0 → Ω → ℝ} {VR : Fin (flowLineNR b' J' 0) → ℝ≥0 → Ω → ℝ}
    {B : ℝ≥0 → Ω → ℝ} {ζ : Ω → ℝ≥0∞} {h' : Ω → DistOn upperHalfPlaneOpens}
    (hC : IsOptionalHullCoupling (16 / κ) (flowLineXL b' J' 0) (flowLineXR b' J' 0) (flowLineRhoL (16 / κ) b' J' 0 0)
      (flowLineRhoR (16 / κ) b' J' 0 0) P 𝓕 W VL VR B ζ h')
    (hζ : ∀ᵐ ω ∂P, ζ ω = ⊤)
    (hW : ∀ᵐ ω ∂P, Continuous (fun t => W t ω) ∧ W 0 ω = 0 ∧ IsGeneratingTrace (fun t => W t ω) ⊤ (γ ω))
    {u₀ : ℂ → ℝ}
    (hu₀ : IsBoundedHarmonicExtension (cfData (16 / κ) b' J')
      (forceJumpSet (flowLineXL b' J' 0) (flowLineXR b' J' 0)) u₀)
    (hh0 : LQGMetric.IsZeroBoundaryGFF upperHalfPlaneOpens (WholeField.centredField h' u₀) P)
    (c : Restart.BoundaryWord) (s t : ℝ≥0) (ht0 : 0 < t)
    (E : Set Ω) {A : Ω → Set ℂ}
    (hAeq : ∀ᵐ ω ∂P, ω ∈ E → (s : ℝ≥0∞) < ζα ω → A ω = invHull (fun r : ℝ => Wα r.toNNReal ω) s)
    (hAhull : ∀ᵐ ω ∂P, ∃ K : Set ℂ, IsHPHull K ∧ A ω = WangWu.negInv '' K)
    {K : Ω → Set ℂ} (hKeq : ∀ᵐ ω ∂P, K ω = fwdHull (fun r : ℝ => W r.toNNReal ω) t)
    (hAm : Measurable[mΩ, hittingSigma] A) (hKm : Measurable[mΩ, hittingSigma] K)
    (hdA : MeasurableSpace.comap A hittingSigma ≤
      aeSigma (MeasurableSpace.comap (WholeField.centredField h' u₀) inferInstance) P)
    (hlA : IsLocalSet A (WholeField.centredField h' u₀) P)
    (hlU : IsLocalSet (fun ω => A ω ∪ K ω) (WholeField.centredField h' u₀) P)
    {g g₁ g₂ : Ω → DistOn upperHalfPlaneOpens}
    (hg : IsLocalSetMean (fun ω => A ω ∪ K ω) (WholeField.centredField h' u₀) P g)
    (hg₁ : IsLocalSetMean A (WholeField.centredField h' u₀) P g₁)
    (hg₂ : IsLocalSetMean K (WholeField.centredField h' u₀) P g₂)
    (hind₁ : ∀ᵐ ω ∂P, ω ∈ E → (s : ℝ≥0∞) < ζα ω → α ω s ∈ H →
      ∀ G₀ : ℂ → ℝ, IsBoundedHarmonicExtension
          (cfData (16 / κ) (gb6WordOfRec κ θ c (gb6Rec s Wα ζα ω)).fn (gb6WordOfRec κ θ c (gb6Rec s Wα ζα ω)).jumps)
          (cfJumps (gb6WordOfRec κ θ c (gb6Rec s Wα ζα ω)).fn (gb6WordOfRec κ θ c (gb6Rec s Wα ζα ω)).jumps) G₀ →
        ∀ w₁ : ℂ → ℝ, InnerProductSpace.HarmonicOnNhd w₁ (H \ A ω) →
          (∀ φ : TestOn upperHalfPlaneOpens, tsupport φ ⊆ H \ A ω → g₁ ω φ = ∫ z, w₁ z * φ z) →
          EqOn (fun z => w₁ z + u₀ z)
            (fun z => G₀ (relMap (fun r : ℝ => Wα r.toNNReal ω) s z) -
              QuantumZipper.chiC (16 / κ) * (relLog (fun r : ℝ => Wα r.toNNReal ω) s z).im)
            (H \ A ω)) :
    ∀ᵐ ω ∂P, ω ∈ E → (s : ℝ≥0∞) < ζα ω → α ω s ∈ H →
      (t : ℝ≥0∞) < firstContactTime (fun t => sphereInv (γ ω t : OnePoint ℂ))
        ((fun t => (α ω t : OnePoint ℂ)) '' Icc 0 s) →
      ∃ (Wr : ℝ → ℝ) (ηr : ℝ → ℂ) (G : ℂ → ℝ), Continuous Wr ∧ Wr 0 = 0 ∧ IsLoewnerTrace Wr ηr ∧
        0 < relClock (fun r : ℝ => Wα r.toNNReal ω) s (fun r : ℝ => W r.toNNReal ω) t ∧
        relMap (fun r : ℝ => Wα r.toNNReal ω) s '' fwdHull (fun r : ℝ => W r.toNNReal ω) t =
          fwdHull Wr (relClock (fun r : ℝ => Wα r.toNNReal ω) s (fun r : ℝ => W r.toNNReal ω) t) ∧
        IsBoundedHarmonicExtension
          (cfFlowedData (16 / κ) (gb6WordOfRec κ θ c (gb6Rec s Wα ζα ω)).fn
            (gb6WordOfRec κ θ c (gb6Rec s Wα ζα ω)).jumps Wr
            (relClock (fun r : ℝ => Wα r.toNNReal ω) s (fun r : ℝ => W r.toNNReal ω) t))
          (cfFlowedJumps (gb6WordOfRec κ θ c (gb6Rec s Wα ζα ω)).fn
            (gb6WordOfRec κ θ c (gb6Rec s Wα ζα ω)).jumps Wr
            (relClock (fun r : ℝ => Wα r.toNNReal ω) s (fun r : ℝ => W r.toNNReal ω) t)) G ∧
        ∀ wU : ℂ → ℝ, InnerProductSpace.HarmonicOnNhd wU (H \ (A ω ∪ K ω)) →
          (∀ φ : TestOn upperHalfPlaneOpens, tsupport φ ⊆ H \ (A ω ∪ K ω) →
            g ω φ = ∫ z, wU z * φ z) →
          EqOn (fun z => wU z + u₀ z)
            (fun z => G (fwdMap Wr (relClock (fun r : ℝ => Wα r.toNNReal ω) s (fun r : ℝ => W r.toNNReal ω) t)
                (relMap (fun r : ℝ => Wα r.toNNReal ω) s z)) -
              QuantumZipper.chiC (16 / κ) *
                ((logDerivFwd Wr (relClock (fun r : ℝ => Wα r.toNNReal ω) s (fun r : ℝ => W r.toNNReal ω) t)
                  (relMap (fun r : ℝ => Wα r.toNNReal ω) s z)).im +
                  (relLog (fun r : ℝ => Wα r.toNNReal ω) s z).im))
            (H \ (A ω ∪ K ω)) := by
  classical
  -- the per-sample relative chain, chosen
  set Tc : Ω → ℝ≥0∞ := fun ω => firstContactTime (fun t => sphereInv (γ ω t : OnePoint ℂ))
    ((fun t => (α ω t : OnePoint ℂ)) '' Icc 0 s) with hTc
  set D : Set Ω := {ω | ω ∈ E ∧ (s : ℝ≥0∞) < ζα ω ∧ α ω s ∈ H ∧ (t : ℝ≥0∞) < Tc ω} with hD
  have hex : ∀ᵐ ω ∂P, ω ∈ D → ∃ p : (ℝ → ℝ) × (ℝ → ℂ), IsGB6RelChain κ θ c b' J' s t Wα W ζα γ ω p.1 p.2 := by
    filter_upwards [ae_isRelConfigOff_gb6_flow hκ hκ4 hF hα hW b' J' c s] with ω hω hωD
    obtain ⟨-, hs, hsH, htc⟩ := hωD
    obtain ⟨t₁, htt₁, ht₁⟩ := ENNReal.lt_iff_exists_nnreal_btwn.1 htc
    obtain ⟨Wr, ηr, hR⟩ := hω hs hsH t t₁ ht0 (ENNReal.coe_lt_coe.1 htt₁) ht₁
    exact ⟨(Wr, ηr), hR⟩
  set pr : Ω → (ℝ → ℝ) × (ℝ → ℂ) := fun ω =>
    Classical.epsilon fun p : (ℝ → ℝ) × (ℝ → ℂ) => IsGB6RelChain κ θ c b' J' s t Wα W ζα γ ω p.1 p.2 with hpr
  have hprs : ∀ᵐ ω ∂P, ω ∈ D → IsGB6RelChain κ θ c b' J' s t Wα W ζα γ ω (pr ω).1 (pr ω).2 := by
    filter_upwards [hex] with ω hω hωD
    exact Classical.epsilon_spec (p := fun p : (ℝ → ℝ) × (ℝ → ℂ) =>
      IsGB6RelChain κ θ c b' J' s t Wα W ζα γ ω p.1 p.2) (hω hωD)
  -- the three bounded harmonic extensions
  set uc : Ω → ℝ := fun ω => relClock (fun r : ℝ => Wα r.toNNReal ω) s (fun r : ℝ => W r.toNNReal ω) t with huc
  set G₀ : Ω → ℂ → ℝ := fun ω => (Sec7.StripSysField.exists_isBoundedHarmonicExtension_forceBoundaryData (16 / κ)
    (flowLineRhoL (16 / κ) (gb6WordOfRec κ θ c (gb6Rec s Wα ζα ω)).fn (gb6WordOfRec κ θ c (gb6Rec s Wα ζα ω)).jumps 0 0)
    (flowLineRhoR (16 / κ) (gb6WordOfRec κ θ c (gb6Rec s Wα ζα ω)).fn (gb6WordOfRec κ θ c (gb6Rec s Wα ζα ω)).jumps 0 0)
    (flowLineXL (gb6WordOfRec κ θ c (gb6Rec s Wα ζα ω)).fn (gb6WordOfRec κ θ c (gb6Rec s Wα ζα ω)).jumps 0)
    (flowLineXR (gb6WordOfRec κ θ c (gb6Rec s Wα ζα ω)).fn
      (gb6WordOfRec κ θ c (gb6Rec s Wα ζα ω)).jumps 0)).choose with hG₀
  set GE : Ω → ℂ → ℝ := fun ω => (Sec7.StripSysField.exists_isBoundedHarmonicExtension_forceBoundaryData (16 / κ)
    (flowLineRhoL (16 / κ) b' J' 0 0) (flowLineRhoR (16 / κ) b' J' 0 0)
    (fun i => Exist.StagedLaw.markPosL (fun r : ℝ => W r.toNNReal ω) t (flowLineXL b' J' 0 i))
    (fun j => Exist.StagedLaw.markPos (fun r : ℝ => W r.toNNReal ω) t (flowLineXR b' J' 0 j))).choose with hGE
  set G : Ω → ℂ → ℝ := fun ω => (Sec7.StripSysField.exists_isBoundedHarmonicExtension_forceBoundaryData (16 / κ)
    (flowLineRhoL (16 / κ) (gb6WordOfRec κ θ c (gb6Rec s Wα ζα ω)).fn (gb6WordOfRec κ θ c (gb6Rec s Wα ζα ω)).jumps 0 0)
    (flowLineRhoR (16 / κ) (gb6WordOfRec κ θ c (gb6Rec s Wα ζα ω)).fn (gb6WordOfRec κ θ c (gb6Rec s Wα ζα ω)).jumps 0 0)
    (fun i => Exist.StagedLaw.markPosL (pr ω).1 (uc ω)
      (flowLineXL (gb6WordOfRec κ θ c (gb6Rec s Wα ζα ω)).fn (gb6WordOfRec κ θ c (gb6Rec s Wα ζα ω)).jumps 0 i))
    (fun j => Exist.StagedLaw.markPos (pr ω).1 (uc ω)
      (flowLineXR (gb6WordOfRec κ θ c (gb6Rec s Wα ζα ω)).fn
        (gb6WordOfRec κ θ c (gb6Rec s Wα ζα ω)).jumps 0 j))).choose with hG
  have hG₀s : ∀ ω, IsBoundedHarmonicExtension
      (cfData (16 / κ) (gb6WordOfRec κ θ c (gb6Rec s Wα ζα ω)).fn (gb6WordOfRec κ θ c (gb6Rec s Wα ζα ω)).jumps)
      (cfJumps (gb6WordOfRec κ θ c (gb6Rec s Wα ζα ω)).fn (gb6WordOfRec κ θ c (gb6Rec s Wα ζα ω)).jumps) (G₀ ω) :=
    fun ω => by
      rw [coe_cfJumps]
      exact (Sec7.StripSysField.exists_isBoundedHarmonicExtension_forceBoundaryData _ _ _ _ _).choose_spec
  have hGEs : ∀ ω, IsBoundedHarmonicExtension (cfFlowedData (16 / κ) b' J' (fun r : ℝ => W r.toNNReal ω) t)
      (cfFlowedJumps b' J' (fun r : ℝ => W r.toNNReal ω) t) (GE ω) := fun ω => by
    rw [cfFlowedJumps, flowedJumps, coe_initJumps]
    exact (Sec7.StripSysField.exists_isBoundedHarmonicExtension_forceBoundaryData _ _ _ _ _).choose_spec
  have hGs : ∀ ω, IsBoundedHarmonicExtension
      (cfFlowedData (16 / κ) (gb6WordOfRec κ θ c (gb6Rec s Wα ζα ω)).fn (gb6WordOfRec κ θ c (gb6Rec s Wα ζα ω)).jumps
        (pr ω).1 (uc ω))
      (cfFlowedJumps (gb6WordOfRec κ θ c (gb6Rec s Wα ζα ω)).fn (gb6WordOfRec κ θ c (gb6Rec s Wα ζα ω)).jumps
        (pr ω).1 (uc ω)) (G ω) := fun ω => by
    rw [cfFlowedJumps, flowedJumps, coe_initJumps]
    exact (Sec7.StripSysField.exists_isBoundedHarmonicExtension_forceBoundaryData _ _ _ _ _).choose_spec
  -- the candidate mean
  set v : Ω → ℂ → ℝ := fun ω z => G ω (fwdMap (pr ω).1 (uc ω) (relMap (fun r : ℝ => Wα r.toNNReal ω) s z)) -
    QuantumZipper.chiC (16 / κ) * ((logDerivFwd (pr ω).1 (uc ω) (relMap (fun r : ℝ => Wα r.toNNReal ω) s z)).im +
      (relLog (fun r : ℝ => Wα r.toNNReal ω) s z).im) with hv
  -- the configuration on `D`
  have hcfg : ∀ᵐ ω ∂P, ω ∈ D → IsRelConfigOff (A ω)
      (relMap (fun r : ℝ => Wα r.toNNReal ω) s) (relInv (fun r : ℝ => Wα r.toNNReal ω) s)
      (relLog (fun r : ℝ => Wα r.toNNReal ω) s) (relBad (fun r : ℝ => Wα r.toNNReal ω) s)
      (fun r : ℝ => W r.toNNReal ω) (pr ω).1 (fun r : ℝ => γ ω r.toNNReal) (pr ω).2 ((fun _ : Ω => (t : ℝ)) ω)
      (uc ω) (QuantumZipper.chiC (16 / κ)) (Real.pi / Real.sqrt (16 / κ))
      (cfData (16 / κ) (gb6WordOfRec κ θ c (gb6Rec s Wα ζα ω)).fn (gb6WordOfRec κ θ c (gb6Rec s Wα ζα ω)).jumps)
      (cfFlowedData (16 / κ) b' J' (fun r : ℝ => W r.toNNReal ω) t)
      (cfFlowedData (16 / κ) (gb6WordOfRec κ θ c (gb6Rec s Wα ζα ω)).fn
        (gb6WordOfRec κ θ c (gb6Rec s Wα ζα ω)).jumps (pr ω).1 (uc ω))
      (cfJumps (gb6WordOfRec κ θ c (gb6Rec s Wα ζα ω)).fn (gb6WordOfRec κ θ c (gb6Rec s Wα ζα ω)).jumps)
      (cfFlowedJumps b' J' (fun r : ℝ => W r.toNNReal ω) t)
      (cfFlowedJumps (gb6WordOfRec κ θ c (gb6Rec s Wα ζα ω)).fn
        (gb6WordOfRec κ θ c (gb6Rec s Wα ζα ω)).jumps (pr ω).1 (uc ω))
      (G₀ ω) (GE ω) (G ω) (v ω) := by
    filter_upwards [hprs, hAeq] with ω hω hAω hωD
    have hc := (hω hωD).2.2.2.2.2
    rw [← hAω hωD.1 hωD.2.1] at hc
    exact hc (G₀ ω) (GE ω) (G ω) (v ω) (hG₀s ω) (hGEs ω) (hGs ω) fun z => rfl
  -- locality and topology of the counterflow hull
  obtain ⟨hX, hker⟩ := hC.2.2.2
  have hτζ : ∀ᵐ ω ∂P, ((((fun _ : Ω => ((t : ℝ≥0) : WithTop ℝ≥0)) ω) : WithTop ℝ≥0) : ℝ≥0∞) < ζ ω := by
    filter_upwards [hζ] with ω hω
    rw [hω]
    exact ENNReal.coe_lt_top
  have hK' : IsLocalSet (fun ω => fwdHull (fun r : ℝ => W r.toNNReal ω) t) h' P := by
    have h1 := (hker (fun _ => ((t : ℝ≥0) : WithTop ℝ≥0)) (isStoppingTime_const _ t) hτζ).1
    simpa only [WithTop.untopD_coe] using h1
  have hlK : IsLocalSet K (WholeField.centredField h' u₀) P := by
    refine Coupling.IsLocalSet.congr_set
      (WholeField.IsLocalSet.sub_dist hK' (WholeField.isHarmonicDistOn_smoothDist hu₀.1)) ?_
    filter_upwards [hKeq] with ω hω
    simp only [hω]
  have hunbK : ∀ᵐ ω ∂P, ∀ z ∈ lowerUnion (K ω),
      ¬ Bornology.IsBounded (connectedComponentIn (lowerUnion (K ω)) z) := by
    filter_upwards [hKeq, hW] with ω hω hWω
    rw [hω]
    exact Sec5.GlueCond.not_isBounded_lowerUnion_of_isHPHull
      (isHPHull_fwdHull (hWω.1.comp continuous_real_toNNReal) t.coe_nonneg)
  have hunbA : ∀ᵐ ω ∂P, ∀ z ∈ lowerUnion (A ω),
      ¬ Bornology.IsBounded (connectedComponentIn (lowerUnion (A ω)) z) := by
    filter_upwards [hAhull] with ω hω
    obtain ⟨K, hK, hAK⟩ := hω
    rw [hAK]
    exact Sec5.GlueCond.not_isBounded_lowerUnion_image_negInv hK
  -- the two partial means
  have hind₂ := ae_eqOn_cfMean (by positivity) hC hζ hu₀ hh0 t hKeq hKm hg₂
  have hmain := ae_eqOn_unionMean_of_relConfigOff_ver hh0 hu₀.1 hu₀.2.1 hAm hKm hdA hlA hlK hlU hunbA hunbK hg hg₁
    hg₂ (D := D) (by filter_upwards [hKeq] with ω hω _ using hω) hcfg
    (by
      filter_upwards [hind₁] with ω hω hωD w₁ hw₁ hr₁
      exact hω hωD.1 hωD.2.1 hωD.2.2.1 (G₀ ω) (hG₀s ω) w₁ hw₁ hr₁)
    (by
      filter_upwards [hind₂, hW] with ω hω hWω hωD w₂ hw₂ hr₂
      exact hω hWω.1 hWω.2.1 (GE ω) (hGEs ω) w₂ hw₂ hr₂)
  filter_upwards [hmain, hprs] with ω hω hpω hE hs hsH htc
  have hωD : ω ∈ D := ⟨hE, hs, hsH, htc⟩
  obtain ⟨h1, h2, h3, h4, h5, -⟩ := hpω hωD
  exact ⟨(pr ω).1, (pr ω).2, G ω, h1, h2, h3, h4, h5, hGs ω, fun wU hwU hrU => hω hωD wU hwU hrU⟩

end InteractingSLE.Supp8.Q3Chain
