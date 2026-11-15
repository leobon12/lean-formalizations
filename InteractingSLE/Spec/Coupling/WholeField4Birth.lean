/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Coupling.WholeField4Announce
import InteractingSLE.Spec.Coupling.WholeField3Brown
import InteractingSLE.Spec.Coupling.Assembly11Safe
import InteractingSLE.WangWu.CouplingBridge
import InteractingSLE.WangWu.BridgeTrace
import InteractingSLE.WangWu.CouplingMain

/-!
# Whole-field identification C.3: the kernel at a pocket's birth, and the Green limit (WF8) at `κ = 4`

Source: `source/external/AstraIG1/ig1_followup_proofs.txt` (ruling R38), Part C.3 (L1584–1640): "Fix a deterministic point
`q ∈ ℍ`, with first swallowing time `β_q` … The level stops `inf{t : Y_t ≤ 1/n}`, capped at `S` and the usual pre-lifetime
bounds, announce `β_q` on the stated event. Denote them by `βₙ`. The sigma-algebra `Γ_{β−} := σ(⋃ₙ Γ_{βₙ})` contains the
entire stopped continuous driving history through the birth." Then (WF8): "`G_{D_{βₙ}}(z, w) ⟶ G_P(z, w)`" and "the
limiting covariance is the direct sum of the newborn component kernels and the active kernel." C.6 (L1874–1890) runs the
same argument along the announcing sequence of the lifetime.

## Main results

* `exists_announced_kernel`: the announced kernel (`ae_condExp_iSup_histGerm_eq`) for any nondecreasing sequence of real
  driving stops `ρₙ < ζ`, with chosen hull versions and the canonical extensions `bheAt` (`testedFrozenMean`); one
  filtration `Γₙ = Γ(𝓕_{ρₙ}, K_{ρₙ})` serves every test function.
* `exists_announced_kernel_history`: the same Gaussian law given the announced driving history `⋁ 𝓕_{ρₙ}` alone (Lévy's
  upward theorem along the frozen kernels given `𝓕_{ρₙ}`).
* **`exists_birthSeq_kernel`** (C.3, general `κ > 0`): for a compact `K ⊆ ℍ` (for instance a point `q`) there are
  driving stops `ρₙ < ζ`, nondecreasing, at which `K` is not yet swallowed and which reach every time `t < ζ` at which `K`
  is still unswallowed (so `ρₙ ↑ β_K ∧ ζ`, `β_K` the first swallowing time of `K`): the announcing sequence of the birth.
  Given `Γ_{β−} = ⋁ Γ_{ρₙ}`, every test avoiding the hulls has the Gaussian law with the limit mean and limit variance.
* `exists_lifetimeSeq_kernel` (C.6, active part): the same along an announcing sequence of the lifetime.
* `isTestFn_of_testOn`: test functions on `ℍ` are Wang–Wu test functions.
* **`tendsto_zeroGFFTestCov_hull_four`** ((WF8) at `κ = 4`, integrated and deterministic): along times `tₙ ↑ β < ζ`
  with `φ` avoiding every `K_{tₙ}`, `G_{ℍ∖K_{tₙ}}(φ, φ) → G_{ℍ∖η[0,β]}(φ, φ)` when a continuous trace `η` exists and
  `η[0,β]` has zero area. `ℍ ∖ η[0,β]` contains the newborn pockets and the active domain, and its Green form is the sum
  over components: the "direct sum of the newborn component kernels and the active kernel" of C.3. The analytic content
  is QuantumZipper's C5 theorem (through `WangWu.BridgeTrace`) and the continuity of the retained Green form
  (`WangWu.continuous_retainedGreenForm_min`); no Carathéodory kernel theorem is needed.
* **`exists_announced_kernel_four`** (C.3 at `κ = 4`): combining the two, given `Γ_{β−}` or given the announced history,
  the field paired with a test avoiding the pre-birth hulls is Gaussian with variance `G_{ℍ∖η[0,β]}(φ, φ)`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal

namespace InteractingSLE

namespace WholeField

open QuantumZipper Ito Coupling LQGMetric

/-! ### Test functions -/

/-- Every test function on `ℍ` is a Wang–Wu test function (continuous, compactly supported, vanishing below a positive
height). -/
theorem isTestFn_of_testOn (φ : TestOn upperHalfPlaneOpens) : WangWu.IsTestFn φ := by
  refine ⟨φ.contDiff.continuous, φ.hasCompactSupport, ?_⟩
  rcases (tsupport φ).eq_empty_or_nonempty with he | hne
  · refine ⟨1, one_pos, fun a _ => image_eq_zero_of_notMem_tsupport ?_⟩
    rw [he]
    exact notMem_empty a
  · obtain ⟨z, hz, hmin⟩ :=
      φ.hasCompactSupport.isCompact.exists_isMinOn hne Complex.continuous_im.continuousOn
    refine ⟨z.im, φ.tsupport_subset hz, fun a ha => image_eq_zero_of_notMem_tsupport fun haS => ?_⟩
    exact absurd (hmin haS) (not_le.2 ha)

/-! ### (WF8) at `κ = 4`: the Green limit at a birth -/

section Green

variable {nL nR : ℕ} {xL : Fin nL → ℝ} {xR : Fin nR → ℝ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ}

/-- **(WF8) at `κ = 4`, integrated form.** For an integrated `SLE₄(ρ)` path, times `tₙ → β` with `tₙ ≤ β < ζ`, a test
function `φ` avoiding every hull `K_{tₙ}`, and a continuous generating trace `η` before `ζ` with `η[0, β] ∩ ℍ` of zero
area: `G_{ℍ∖K_{tₙ}}(φ, φ) → G_{ℍ∖η[0,β]}(φ, φ)`. -/
theorem tendsto_zeroGFFTestCov_hull_four {w : ℝ≥0 → ℝ} {vL : Fin nL → ℝ≥0 → ℝ} {vR : Fin nR → ℝ≥0 → ℝ}
    {b : ℝ≥0 → ℝ} {ζ : ℝ≥0∞} (hP : IsIntegratedSLEPath 4 xL xR ρL ρR w vL vR b ζ) {t : ℕ → ℝ≥0} {β : ℝ≥0}
    (ht : Tendsto t atTop (𝓝 β)) (htβ : ∀ n, t n ≤ β) (hβ : (β : ℝ≥0∞) < ζ) (φ : TestOn upperHalfPlaneOpens)
    (hdisj : ∀ n, Disjoint (tsupport φ) (fwdHull (fun s : ℝ => w s.toNNReal) (t n : ℝ)))
    {η : ℝ≥0 → ℂ} (hη : IsGeneratingTrace w ζ η) (harea : volume (η '' Icc 0 β ∩ H) = 0) :
    Tendsto (fun n => zeroGFFTestCov (H \ fwdHull (fun s : ℝ => w s.toNNReal) (t n : ℝ)) φ φ) atTop
      (𝓝 (zeroGFFTestCov (H \ η '' Icc 0 β) φ φ)) := by
  have hw0 : w 0 = 0 := hP.1
  have hw : ContinuousOn w {s | (s : ℝ≥0∞) < ζ} := hP.2.2.2.1
  have hφT := isTestFn_of_testOn φ
  have hφH : tsupport φ ⊆ H := φ.tsupport_subset
  have htζ : ∀ n, ((t n : ℝ≥0) : ℝ≥0∞) < ζ := fun n =>
    lt_of_le_of_lt (by exact_mod_cast htβ n) hβ
  -- each term is the retained Green form at `tₙ ∧ β`
  have e : ∀ n, zeroGFFTestCov (H \ fwdHull (fun s : ℝ => w s.toNNReal) (t n : ℝ)) φ φ =
      WangWu.retainedGreenForm w (min (t n) β) φ φ := fun n => by
    rw [← WholeField.loewnerGreenEnergy_rpath_eq_zeroGFFTestCov hw hw0 (htζ n) φ (hdisj n),
      min_eq_left (htβ n), ← WangWu.retainedGreenEnergy_eq_form,
      WangWu.retainedGreenEnergy_eq_loewnerGreenEnergy hP (htζ n) hφH (hdisj n)]
    rfl
  simp only [e]
  have hc := WangWu.continuous_retainedGreenForm_min hP hβ hφT hφT
  have hlim := (hc.tendsto β).comp ht
  rw [min_self] at hlim
  rw [InteractingSLE.zeroGFFTestCov_compl_image_eq_retainedGreenEnergy hη hw hw0 hβ harea φ,
    WangWu.retainedGreenEnergy_eq_form]
  exact hlim

end Green

/-! ### Announcing sequences of real driving stops -/

section Seq

universe u

variable {κ : ℝ} {nL nR : ℕ} {xL : Fin nL → ℝ} {xR : Fin nR → ℝ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ}
  {Ω : Type u} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P] {𝓕 : Filtration ℝ≥0 mΩ}
  {W : ℝ≥0 → Ω → ℝ} {VL : Fin nL → ℝ≥0 → Ω → ℝ} {VR : Fin nR → ℝ≥0 → Ω → ℝ} {B : ℝ≥0 → Ω → ℝ}
  {ζ : Ω → ℝ≥0∞} {h : Ω → DistOn upperHalfPlaneOpens}

/-- The tested frozen mean `(𝔥_s − 𝔥₀, φ)` at the state of `ω` at time `s`, with the canonical extension `bheAt`. -/
def testedFrozenMean (κ : ℝ) (ρL : Fin nL → ℝ) (ρR : Fin nR → ℝ) (W : ℝ≥0 → Ω → ℝ) (VL : Fin nL → ℝ≥0 → Ω → ℝ)
    (VR : Fin nR → ℝ≥0 → Ω → ℝ) (u₀ : ℂ → ℝ) (φ : TestOn upperHalfPlaneOpens) (s : ℝ≥0) (ω : Ω) : ℝ :=
  (∫ z, couplingMean κ (fun r : ℝ => W r.toNNReal ω) s
      (bheAt κ ρL ρR (W s ω) (fun i => VL i s ω) (fun i => VR i s ω)) z * φ z) - ∫ z, u₀ z * φ z

/-- **The announced kernel along real driving stops.** For a nondecreasing sequence `ρₙ < ζ` of real stopping times of
the frozen driving filtration there are hitting-measurable versions `Aₙ` of the hulls `K_{ρₙ}` and the filtration
`Γₙ = Γ(𝓕_{ρₙ}, Aₙ)` such that, for every test function `φ`, almost surely on `{φ avoids every Aₙ}`: the tested frozen
means converge to `E[(h⁰, φ) | ⋁ Γₙ]`, the variances `G_{ℍ∖Aₙ}(φ, φ)` decrease to `C_∞`, and the conditional
characteristic function given `⋁ Γₙ` is `e^{i E[(h⁰, φ) | ⋁ Γₙ]} e^{−C_∞/2}`. -/
theorem exists_announced_kernel (hC : IsOptionalHullCoupling κ xL xR ρL ρR P 𝓕 W VL VR B ζ h)
    (hκ : 0 < κ) {u₀ : ℂ → ℝ}
    (hu₀ : IsBoundedHarmonicExtension (forceBoundaryData κ ρL ρR xL xR) (forceJumpSet xL xR) u₀)
    (hX : IsMeasurableKilledDriving W VL VR ζ) {ρ : ℕ → Ω → ℝ≥0}
    (hρ : ∀ n, IsStoppingTime (drivingFiltration P hX) fun ω => (ρ n ω : WithTop ℝ≥0))
    (hρm : ∀ ω, Monotone fun n => ρ n ω) (hρζ : ∀ n, ∀ᵐ ω ∂P, (ρ n ω : ℝ≥0∞) < ζ ω) :
    ∃ (A : ℕ → Ω → Set ℂ) (𝒢 : Filtration ℕ mΩ),
      (∀ n, Measurable[mΩ, hittingSigma] (A n)) ∧
      (∀ n, ∀ᵐ ω ∂P, A n ω = fwdHull (fun s : ℝ => W s.toNNReal ω) (ρ n ω : ℝ)) ∧
      (∀ n, 𝒢 n = histGerm (hρ n).measurableSpace (A n) (centredField h u₀)) ∧
      ∀ φ : TestOn upperHalfPlaneOpens, ∀ᵐ ω ∂P, (∀ n, Disjoint (tsupport φ) (A n ω)) →
        Tendsto (fun n => testedFrozenMean κ ρL ρR W VL VR u₀ φ (ρ n ω) ω) atTop
          (𝓝 ((P[fun ω' => centredField h u₀ ω' φ | ⨆ n, 𝒢 n]) ω)) ∧
        Tendsto (fun n => zeroGFFTestCov (H \ A n ω) φ φ) atTop
          (𝓝 (⨅ n, zeroGFFTestCov (H \ A n ω) φ φ)) ∧
        (P[fun ω' => Complex.exp (Complex.I * (centredField h u₀ ω' φ : ℂ)) | ⨆ n, 𝒢 n]) ω =
          Complex.exp (Complex.I * ((P[fun ω' => centredField h u₀ ω' φ | ⨆ n, 𝒢 n]) ω : ℂ)) *
            ((Real.exp (-(1 / 2) * ⨅ n, zeroGFFTestCov (H \ A n ω) φ φ) : ℝ) : ℂ) := by
  have hσm : Monotone fun n ω => (ρ n ω : WithTop ℝ≥0) := fun m n hmn ω =>
    WithTop.coe_le_coe.2 (hρm ω hmn)
  have hker := hC.2.2.2.choose_spec
  have hver : ∀ n, ∃ A' : Ω → Set ℂ, Measurable[mΩ, hittingSigma] A' ∧
      ∀ᵐ ω ∂P, A' ω = fwdHull (fun s : ℝ => W s.toNNReal ω)
        (((ρ n ω : WithTop ℝ≥0).untopD 0 : ℝ≥0) : ℝ) := fun n => by
    obtain ⟨A', hA'm, hA'e, -⟩ := IsLocalSet.exists_measurable_version ((hker _ (hρ n) (hρζ n)).1) hC.2.1
    exact ⟨A', hA'm, hA'e⟩
  choose A hAm hAK using hver
  obtain ⟨𝒢, h𝒢⟩ := exists_histGerm_filtration_nat (σ := fun n ω => (ρ n ω : WithTop ℝ≥0)) hC hκ u₀ hX hρ hσm
    hρζ hAm hAK
  refine ⟨A, 𝒢, hAm, fun n => (hAK n).mono fun ω hω => by rw [hω, WithTop.untopD_coe], h𝒢, fun φ => ?_⟩
  have hk := ae_condExp_iSup_histGerm_eq (σ := fun n ω => (ρ n ω : WithTop ℝ≥0)) hC hκ hu₀ hX hρ hσm hρζ hAm
    hAK h𝒢 (u := fun n ω => bheAt κ ρL ρR (W (((ρ n ω : WithTop ℝ≥0)).untopD 0) ω)
      (fun i => VL i (((ρ n ω : WithTop ℝ≥0)).untopD 0) ω) (fun i => VR i (((ρ n ω : WithTop ℝ≥0)).untopD 0) ω))
    (fun n ω => bheAt_spec κ ρL ρR _ _ _) φ
  simp only [WithTop.untopD_coe] at hk
  exact hk

/-- **The announced kernel given the history alone.** In the setting of `exists_announced_kernel`, conditioning on the
announced driving history `⋁ₙ 𝓕_{ρₙ}` (without the hull germs) gives the same Gaussian law: almost surely on
`{φ avoids every Aₙ}`, `E[e^{i(h, φ)} | ⋁ₙ 𝓕_{ρₙ}] = e^{i(m_∞ + (𝔥₀, φ)) − C_∞/2}`, where
`m_∞ = E[(h⁰, φ) | ⋁ Γₙ] = lim (𝔥_{ρₙ} − 𝔥₀, φ)` and `C_∞ = ⨅ₙ G_{ℍ∖Aₙ}(φ, φ)`. (Lévy's upward theorem along the frozen
kernels given `𝓕_{ρₙ}`; the limit parameters are those of the germ version.) -/
theorem exists_announced_kernel_history (hC : IsOptionalHullCoupling κ xL xR ρL ρR P 𝓕 W VL VR B ζ h)
    (hκ : 0 < κ) {u₀ : ℂ → ℝ}
    (hu₀ : IsBoundedHarmonicExtension (forceBoundaryData κ ρL ρR xL xR) (forceJumpSet xL xR) u₀)
    (hX : IsMeasurableKilledDriving W VL VR ζ) {ρ : ℕ → Ω → ℝ≥0}
    (hρ : ∀ n, IsStoppingTime (drivingFiltration P hX) fun ω => (ρ n ω : WithTop ℝ≥0))
    (hρm : ∀ ω, Monotone fun n => ρ n ω) (hρζ : ∀ n, ∀ᵐ ω ∂P, (ρ n ω : ℝ≥0∞) < ζ ω) :
    ∃ (A : ℕ → Ω → Set ℂ) (𝒢 : Filtration ℕ mΩ),
      (∀ n, Measurable[mΩ, hittingSigma] (A n)) ∧
      (∀ n, ∀ᵐ ω ∂P, A n ω = fwdHull (fun s : ℝ => W s.toNNReal ω) (ρ n ω : ℝ)) ∧
      (∀ n, 𝒢 n = histGerm (hρ n).measurableSpace (A n) (centredField h u₀)) ∧
      ∀ φ : TestOn upperHalfPlaneOpens, ∀ᵐ ω ∂P, (∀ n, Disjoint (tsupport φ) (A n ω)) →
        Tendsto (fun n => testedFrozenMean κ ρL ρR W VL VR u₀ φ (ρ n ω) ω) atTop
          (𝓝 ((P[fun ω' => centredField h u₀ ω' φ | ⨆ n, 𝒢 n]) ω)) ∧
        Tendsto (fun n => zeroGFFTestCov (H \ A n ω) φ φ) atTop
          (𝓝 (⨅ n, zeroGFFTestCov (H \ A n ω) φ φ)) ∧
        (P[fun ω' => Complex.exp (Complex.I * (centredField h u₀ ω' φ : ℂ)) | ⨆ n, 𝒢 n]) ω =
          Complex.exp (Complex.I * ((P[fun ω' => centredField h u₀ ω' φ | ⨆ n, 𝒢 n]) ω : ℂ)) *
            ((Real.exp (-(1 / 2) * ⨅ n, zeroGFFTestCov (H \ A n ω) φ φ) : ℝ) : ℂ) ∧
        (P[fun ω' => Complex.exp (Complex.I * (h ω' φ : ℂ)) | ⨆ n, (hρ n).measurableSpace]) ω =
          Complex.exp (Complex.I * (((P[fun ω' => centredField h u₀ ω' φ | ⨆ n, 𝒢 n]) ω +
              ∫ z, u₀ z * φ z : ℝ) : ℂ) -
            (((1 / 2 : ℝ) * ⨅ n, zeroGFFTestCov (H \ A n ω) φ φ : ℝ) : ℂ)) := by
  obtain ⟨A, 𝒢, hAm, hAK, h𝒢, hker⟩ := exists_announced_kernel hC hκ hu₀ hX hρ hρm hρζ
  refine ⟨A, 𝒢, hAm, hAK, h𝒢, fun φ => ?_⟩
  -- the announced history filtration
  let ℱ : Filtration ℕ mΩ :=
    { seq := fun n => (hρ n).measurableSpace
      mono' := fun m n hmn => (hρ m).measurableSpace_mono (hρ n) fun ω => WithTop.coe_le_coe.2 (hρm ω hmn)
      le' := fun n => (hρ n).measurableSpace_le }
  have hhm : Measurable fun ω' => h ω' φ := ((measurable_pi_apply φ).comp (comap_measurable _)).comp hC.2.1
  have hint : Integrable (fun ω' => Complex.exp (Complex.I * (h ω' φ : ℂ))) P := by
    refine Integrable.of_bound (C := 1) ?_ (Eventually.of_forall fun ω => ?_)
    · exact (Complex.measurable_exp.comp (measurable_const.mul
        (Complex.measurable_ofReal.comp hhm))).aestronglyMeasurable
    · rw [Complex.norm_exp_I_mul_ofReal]
  have hfz := fun n => (hC.2.2.2.choose_spec _ (hρ n) (hρζ n)).2
    (fun ω => bheAt κ ρL ρR (W (((ρ n ω : WithTop ℝ≥0)).untopD 0) ω)
      (fun i => VL i (((ρ n ω : WithTop ℝ≥0)).untopD 0) ω) (fun i => VR i (((ρ n ω : WithTop ℝ≥0)).untopD 0) ω))
    (fun ω => bheAt_spec κ ρL ρR _ _ _) φ
  simp only [WithTop.untopD_coe] at hfz
  filter_upwards [hker φ, ae_all_iff.2 hfz, ae_all_iff.2 hAK, ae_all_iff.2 hρζ, hC.1.2.2.2.2,
    tendsto_ae_condExp_complex (P := P) ℱ hint] with ω hk hfr hAω hζω hp hlev hdisj
  obtain ⟨h1, h2, h3⟩ := hk hdisj
  have hd : ∀ n, Disjoint (tsupport φ) (fwdHull (fun s : ℝ => W s.toNNReal ω) (ρ n ω : ℝ)) := fun n => by
    rw [← hAω n]; exact hdisj n
  refine ⟨h1, h2, h3, tendsto_nhds_unique hlev ?_⟩
  have e : ∀ n, (P[fun ω' => Complex.exp (Complex.I * (h ω' φ : ℂ)) | ℱ n]) ω =
      Complex.exp (Complex.I * ((testedFrozenMean κ ρL ρR W VL VR u₀ φ (ρ n ω) ω + ∫ z, u₀ z * φ z : ℝ) : ℂ) -
        (((1 / 2 : ℝ) * zeroGFFTestCov (H \ A n ω) φ φ : ℝ) : ℂ)) := fun n => by
    change (P[fun ω' => Complex.exp (Complex.I * (h ω' φ : ℂ)) | (hρ n).measurableSpace]) ω = _
    rw [hfr n (hd n), hAω n, WholeField.loewnerGreenEnergy_rpath_eq_zeroGFFTestCov hp.2.2.2.1 hp.1 (hζω n) φ (hd n)]
    simp only [testedFrozenMean, sub_add_cancel]
  simp only [e]
  have hcont : Continuous fun p : ℝ × ℝ => Complex.exp (Complex.I * ((p.1 : ℝ) : ℂ) - ((p.2 : ℝ) : ℂ)) :=
    Complex.continuous_exp.comp ((continuous_const.mul (Complex.continuous_ofReal.comp continuous_fst)).sub
      (Complex.continuous_ofReal.comp continuous_snd))
  have hpair := ((h1.add_const (∫ z, u₀ z * φ z)).prodMk_nhds (h2.const_mul (1 / 2 : ℝ)))
  exact (hcont.tendsto _).comp hpair

/-- **C.3: the announcing sequence of a birth, and the kernel given the pre-birth information.** Let the seed be
admissible (otherwise `ζ = 0` and there is nothing to announce), and let `K ⊆ ℍ` be compact with `Im ≥ m > 0` on `K`
(for instance a single point `q`). There are real driving stops `ρₙ < ζ`, nondecreasing, at which `K` is not yet
swallowed, and which eventually exceed every time `t < ζ` at which `K` is still unswallowed — so `ρₙ ↑ β_K ∧ ζ`, with
`β_K` the first swallowing time of `K` — together with hull versions `Aₙ` and the filtration `Γₙ = Γ(𝓕_{ρₙ}, Aₙ)`.
Given `Γ_{β−} = ⋁ Γₙ`, every test function avoiding the hulls `Aₙ` has the Gaussian conditional law with the limit
mean `E[(h⁰, φ) | Γ_{β−}] = lim (𝔥_{ρₙ} − 𝔥₀, φ)` and the limit variance `C_∞ = ⨅ₙ G_{ℍ∖Aₙ}(φ, φ)`. -/
theorem exists_birthSeq_kernel (hC : IsOptionalHullCoupling κ xL xR ρL ρR P 𝓕 W VL VR B ζ h)
    (hκ : 0 < κ) {u₀ : ℂ → ℝ}
    (hu₀ : IsBoundedHarmonicExtension (forceBoundaryData κ ρL ρR xL xR) (forceJumpSet xL xR) u₀)
    (hX : IsMeasurableKilledDriving W VL VR ζ) (hseed : ¬ ForceWord.ThresholdCondition ρL ρR 0 xL xR)
    {K : Set ℂ} (hK : IsCompact K) (hKH : K ⊆ H) {m : ℝ} (hm : 0 < m) (hKm : ∀ z ∈ K, m ≤ z.im) :
    ∃ (ρ : ℕ → Ω → ℝ≥0) (hρ : ∀ n, IsStoppingTime (drivingFiltration P hX) fun ω => (ρ n ω : WithTop ℝ≥0))
      (A : ℕ → Ω → Set ℂ) (𝒢 : Filtration ℕ mΩ),
      (∀ ω, Monotone fun n => ρ n ω) ∧ (∀ n, ∀ᵐ ω ∂P, (ρ n ω : ℝ≥0∞) < ζ ω) ∧
      (∀ n, ∀ᵐ ω ∂P, Disjoint K (A n ω)) ∧
      (∀ᵐ ω ∂P, ∀ t : ℝ≥0, (t : ℝ≥0∞) < ζ ω → Disjoint K (fwdHull (fun s : ℝ => W s.toNNReal ω) (t : ℝ)) →
        ∀ᶠ n in atTop, t ≤ ρ n ω) ∧
      (∀ n, Measurable[mΩ, hittingSigma] (A n)) ∧
      (∀ n, ∀ᵐ ω ∂P, A n ω = fwdHull (fun s : ℝ => W s.toNNReal ω) (ρ n ω : ℝ)) ∧
      (∀ n, 𝒢 n = histGerm (hρ n).measurableSpace (A n) (centredField h u₀)) ∧
      ∀ φ : TestOn upperHalfPlaneOpens, ∀ᵐ ω ∂P, (∀ n, Disjoint (tsupport φ) (A n ω)) →
        Tendsto (fun n => testedFrozenMean κ ρL ρR W VL VR u₀ φ (ρ n ω) ω) atTop
          (𝓝 ((P[fun ω' => centredField h u₀ ω' φ | ⨆ n, 𝒢 n]) ω)) ∧
        Tendsto (fun n => zeroGFFTestCov (H \ A n ω) φ φ) atTop
          (𝓝 (⨅ n, zeroGFFTestCov (H \ A n ω) φ φ)) ∧
        (P[fun ω' => Complex.exp (Complex.I * (centredField h u₀ ω' φ : ℂ)) | ⨆ n, 𝒢 n]) ω =
          Complex.exp (Complex.I * ((P[fun ω' => centredField h u₀ ω' φ | ⨆ n, 𝒢 n]) ω : ℂ)) *
            ((Real.exp (-(1 / 2) * ⨅ n, zeroGFFTestCov (H \ A n ω) φ φ) : ℝ) : ℂ) := by
  have hE := hC.1
  have : (drivingFiltration P hX).IsRightContinuous := Ito.isRightContinuous_usualAugmentation _ _
  obtain ⟨σ₀, hσ₀, -⟩ := exists_isAnnouncingSeq_of_adapted (𝓖 := drivingFiltration P hX) (B := B)
    (κ := κ) (xL := xL) (xR := xR) (fun s hs h0 => Ito.measurableSet_usualAugmentation_of_null hs h0 0)
    (Ito.adaptedBefore_mono (Ito.le_usualAugmentation _ _) (adaptedBefore_killedDriving_W hX))
    (fun i => Ito.adaptedBefore_mono (Ito.le_usualAugmentation _ _) (adaptedBefore_killedDriving_VL hX i))
    (fun i => Ito.adaptedBefore_mono (Ito.le_usualAugmentation _ _) (adaptedBefore_killedDriving_VR hX i))
    hE.2.2.2.2 (hE.ae_tendsto_threshold hκ) hseed
  have hpath : ∀ᵐ ω ∂P, ContinuousOn (fun t => W t ω) {t | (t : ℝ≥0∞) < ζ ω} ∧ W 0 ω = 0 := by
    filter_upwards [hE.2.2.2.2] with ω hp using ⟨hp.2.2.2.1, hp.1⟩
  obtain ⟨ρ, hρ, -, hρm, hsafe, hexh⟩ := exists_safeSeq_of_adapted (𝓗 := killedDrivingFiltration hX)
    (adaptedBefore_killedDriving_W hX) hpath hK hKH hm hKm hσ₀.1 hσ₀.2.1 hσ₀.2.2.1
  have hρζ : ∀ n, ∀ᵐ ω ∂P, (ρ n ω : ℝ≥0∞) < ζ ω := fun n => (hsafe n).mono fun ω hω => hω.1
  obtain ⟨A, 𝒢, hAm, hAK, h𝒢, hker⟩ := exists_announced_kernel hC hκ hu₀ hX hρ hρm hρζ
  refine ⟨ρ, hρ, A, 𝒢, hρm, hρζ, fun n => ?_, ?_, hAm, hAK, h𝒢, hker⟩
  · filter_upwards [hsafe n, hAK n, hpath] with ω hs hA hp
    rw [hA]
    refine Set.disjoint_left.2 fun z hz hzK => ?_
    exact notMem_fwdHull_of_alive hp.1 hs.1 (lt_of_lt_of_le hm (hKm z hz)) (hs.2.2.2 z hz).1 hzK
  · filter_upwards [hexh, hσ₀.2.2.2] with ω hex hann t ht hdisj
    obtain ⟨j, hj⟩ := hann t ht
    refine hex j t hj fun z hz => ?_
    exact WangWu.exists_isForwardSol_of_not_mem_hull (hKH hz) (Set.disjoint_left.1 hdisj hz)

/-- **C.6, active part: the kernel along an announcing sequence of the lifetime.** For an admissible seed there are real
driving stops `σₙ ≤ n`, nondecreasing, with `σₙ < ζ` and every `t < ζ` below some `σₙ`, together with hull versions and
the filtration `Γₙ = Γ(𝓕_{σₙ}, K_{σₙ})`, such that given `⋁ Γₙ` every test function avoiding all the hulls has the
Gaussian conditional law with the limit mean and the limit variance. -/
theorem exists_lifetimeSeq_kernel (hC : IsOptionalHullCoupling κ xL xR ρL ρR P 𝓕 W VL VR B ζ h)
    (hκ : 0 < κ) {u₀ : ℂ → ℝ}
    (hu₀ : IsBoundedHarmonicExtension (forceBoundaryData κ ρL ρR xL xR) (forceJumpSet xL xR) u₀)
    (hX : IsMeasurableKilledDriving W VL VR ζ) (hseed : ¬ ForceWord.ThresholdCondition ρL ρR 0 xL xR) :
    ∃ (σ : ℕ → Ω → ℝ≥0) (hσ : ∀ n, IsStoppingTime (drivingFiltration P hX) fun ω => (σ n ω : WithTop ℝ≥0))
      (A : ℕ → Ω → Set ℂ) (𝒢 : Filtration ℕ mΩ),
      IsAnnouncingSeq (drivingFiltration P hX) P ζ σ ∧ (∀ n ω, σ n ω ≤ n) ∧
      (∀ n, Measurable[mΩ, hittingSigma] (A n)) ∧
      (∀ n, ∀ᵐ ω ∂P, A n ω = fwdHull (fun s : ℝ => W s.toNNReal ω) (σ n ω : ℝ)) ∧
      (∀ n, 𝒢 n = histGerm (hσ n).measurableSpace (A n) (centredField h u₀)) ∧
      ∀ φ : TestOn upperHalfPlaneOpens, ∀ᵐ ω ∂P, (∀ n, Disjoint (tsupport φ) (A n ω)) →
        Tendsto (fun n => testedFrozenMean κ ρL ρR W VL VR u₀ φ (σ n ω) ω) atTop
          (𝓝 ((P[fun ω' => centredField h u₀ ω' φ | ⨆ n, 𝒢 n]) ω)) ∧
        Tendsto (fun n => zeroGFFTestCov (H \ A n ω) φ φ) atTop
          (𝓝 (⨅ n, zeroGFFTestCov (H \ A n ω) φ φ)) ∧
        (P[fun ω' => Complex.exp (Complex.I * (centredField h u₀ ω' φ : ℂ)) | ⨆ n, 𝒢 n]) ω =
          Complex.exp (Complex.I * ((P[fun ω' => centredField h u₀ ω' φ | ⨆ n, 𝒢 n]) ω : ℂ)) *
            ((Real.exp (-(1 / 2) * ⨅ n, zeroGFFTestCov (H \ A n ω) φ φ) : ℝ) : ℂ) := by
  have hE := hC.1
  have : (drivingFiltration P hX).IsRightContinuous := Ito.isRightContinuous_usualAugmentation _ _
  obtain ⟨σ₀, hσ₀, hσ₀n⟩ := exists_isAnnouncingSeq_of_adapted (𝓖 := drivingFiltration P hX) (B := B)
    (κ := κ) (xL := xL) (xR := xR) (fun s hs h0 => Ito.measurableSet_usualAugmentation_of_null hs h0 0)
    (Ito.adaptedBefore_mono (Ito.le_usualAugmentation _ _) (adaptedBefore_killedDriving_W hX))
    (fun i => Ito.adaptedBefore_mono (Ito.le_usualAugmentation _ _) (adaptedBefore_killedDriving_VL hX i))
    (fun i => Ito.adaptedBefore_mono (Ito.le_usualAugmentation _ _) (adaptedBefore_killedDriving_VR hX i))
    hE.2.2.2.2 (hE.ae_tendsto_threshold hκ) hseed
  obtain ⟨A, 𝒢, hAm, hAK, h𝒢, hker⟩ := exists_announced_kernel hC hκ hu₀ hX hσ₀.1 hσ₀.2.1 hσ₀.2.2.1
  exact ⟨σ₀, hσ₀.1, A, 𝒢, hσ₀, hσ₀n, hAm, hAK, h𝒢, hker⟩

/-- **C.3 at `κ = 4`: the birth kernel with the identified variance.** In the setting of `exists_announced_kernel` for
`κ = 4`, almost surely: if a test function `φ` avoids every hull `K_{ρₙ}`, the stops `ρₙ` increase to `β < ζ`, and `η`
is a continuous generating trace before `ζ` with `η[0, β] ∩ ℍ` of zero area, then, given the hull germs `⋁ Γₙ` and given
the announced history `⋁ 𝓕_{ρₙ}` alike, `(h, φ)` is Gaussian with variance `G_{ℍ∖η[0,β]}(φ, φ)` (the direct sum of the
newborn pockets' and the active domain's Green forms) and the limit mean:

* `E[e^{i(h⁰, φ)} | ⋁ Γₙ] = e^{i m_∞} e^{−G_{ℍ∖η[0,β]}(φ, φ)/2}`;
* `E[e^{i(h, φ)} | ⋁ 𝓕_{ρₙ}] = e^{i(m_∞ + (𝔥₀, φ)) − G_{ℍ∖η[0,β]}(φ, φ)/2}`;

with `m_∞ = E[(h⁰, φ) | ⋁ Γₙ] = lim (𝔥_{ρₙ} − 𝔥₀, φ)`. -/
theorem exists_announced_kernel_four (hC : IsOptionalHullCoupling 4 xL xR ρL ρR P 𝓕 W VL VR B ζ h)
    {u₀ : ℂ → ℝ} (hu₀ : IsBoundedHarmonicExtension (forceBoundaryData 4 ρL ρR xL xR) (forceJumpSet xL xR) u₀)
    (hX : IsMeasurableKilledDriving W VL VR ζ) {ρ : ℕ → Ω → ℝ≥0}
    (hρ : ∀ n, IsStoppingTime (drivingFiltration P hX) fun ω => (ρ n ω : WithTop ℝ≥0))
    (hρm : ∀ ω, Monotone fun n => ρ n ω) (hρζ : ∀ n, ∀ᵐ ω ∂P, (ρ n ω : ℝ≥0∞) < ζ ω) :
    ∃ (A : ℕ → Ω → Set ℂ) (𝒢 : Filtration ℕ mΩ),
      (∀ n, Measurable[mΩ, hittingSigma] (A n)) ∧
      (∀ n, ∀ᵐ ω ∂P, A n ω = fwdHull (fun s : ℝ => W s.toNNReal ω) (ρ n ω : ℝ)) ∧
      (∀ n, 𝒢 n = histGerm (hρ n).measurableSpace (A n) (centredField h u₀)) ∧
      ∀ φ : TestOn upperHalfPlaneOpens, ∀ᵐ ω ∂P, (∀ n, Disjoint (tsupport φ) (A n ω)) →
        Tendsto (fun n => testedFrozenMean 4 ρL ρR W VL VR u₀ φ (ρ n ω) ω) atTop
          (𝓝 ((P[fun ω' => centredField h u₀ ω' φ | ⨆ n, 𝒢 n]) ω)) ∧
        ∀ β : ℝ≥0, Tendsto (fun n => ρ n ω) atTop (𝓝 β) → (β : ℝ≥0∞) < ζ ω →
          ∀ η : ℝ≥0 → ℂ, IsGeneratingTrace (fun t => W t ω) (ζ ω) η → volume (η '' Icc 0 β ∩ H) = 0 →
            (P[fun ω' => Complex.exp (Complex.I * (centredField h u₀ ω' φ : ℂ)) | ⨆ n, 𝒢 n]) ω =
              Complex.exp (Complex.I * ((P[fun ω' => centredField h u₀ ω' φ | ⨆ n, 𝒢 n]) ω : ℂ)) *
                ((Real.exp (-(1 / 2) * zeroGFFTestCov (H \ η '' Icc 0 β) φ φ) : ℝ) : ℂ) ∧
            (P[fun ω' => Complex.exp (Complex.I * (h ω' φ : ℂ)) | ⨆ n, (hρ n).measurableSpace]) ω =
              Complex.exp (Complex.I * (((P[fun ω' => centredField h u₀ ω' φ | ⨆ n, 𝒢 n]) ω +
                  ∫ z, u₀ z * φ z : ℝ) : ℂ) -
                (((1 / 2 : ℝ) * zeroGFFTestCov (H \ η '' Icc 0 β) φ φ : ℝ) : ℂ)) := by
  obtain ⟨A, 𝒢, hAm, hAK, h𝒢, hker⟩ := exists_announced_kernel_history hC four_pos hu₀ hX hρ hρm hρζ
  refine ⟨A, 𝒢, hAm, hAK, h𝒢, fun φ => ?_⟩
  filter_upwards [hker φ, hC.1.2.2.2.2, ae_all_iff.2 hAK] with ω hk hP hAω hdisj
  obtain ⟨h1, h2, h3, h4⟩ := hk hdisj
  refine ⟨h1, fun β hβ hβζ η hη harea => ?_⟩
  have hd : ∀ n, Disjoint (tsupport φ) (fwdHull (fun s : ℝ => W s.toNNReal ω) (ρ n ω : ℝ)) := fun n => by
    rw [← hAω n]; exact hdisj n
  have hG := tendsto_zeroGFFTestCov_hull_four hP hβ (fun n => (hρm ω).ge_of_tendsto hβ n) hβζ φ hd hη harea
  have e : ⨅ n, zeroGFFTestCov (H \ A n ω) φ φ = zeroGFFTestCov (H \ η '' Icc 0 β) φ φ := by
    refine tendsto_nhds_unique h2 (hG.congr fun n => ?_)
    rw [hAω n]
  rw [← e]
  exact ⟨h3, h4⟩

end Seq

end WholeField

end InteractingSLE
