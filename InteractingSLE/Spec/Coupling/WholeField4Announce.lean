/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Coupling.WholeField2Germ
import InteractingSLE.GFF.LocalSets.MarkovNesting
import Mathlib.Probability.Martingale.Convergence

/-!
# Whole-field identification C.3: the kernel along an announcing sequence

Source: `source/external/AstraIG1/ig1_followup_proofs.txt` (ruling R38), Part C.3 (L1584–1640), "Pass the marked kernels to
the announced birth": "The marked kernel gives, for real `u_j`, (WF9) … Increasing conditional-expectation convergence applies
to the left side, and in `L²` to each field pairing. Hence the displayed mean pairings converge on the component event."
The additional note (`ig1_additional_proofs.txt`, ruling R39), Lemma 7.10 (L2951–2975), "Announced conditional identities":
"Suppose `𝒢ₙ` increase to `𝒢_∞ = σ(⋃ 𝒢ₙ)`. Let `Eₙ ∈ 𝒢ₙ` and let `E ∈ 𝒢_∞` be such that each outcome of `E` lies in `Eₙ` for
every sufficiently large `n`. Suppose, on `Eₙ`, a fixed finite list of ambient tests has conditional mean `mₙ` and covariance
`Cₙ`. If `Cₙ → C` on `E`, then its conditional characteristic function on `E` is the limit of the Gaussian characteristic
functions, with mean `m_∞ = E[H | 𝒢_∞] = lim mₙ` on `E`." The same lemma is used at a pocket's birth (Aux. lemma 48,
L3143–3170: `P_z = σ(⋃ G⁰_{σₙ})`) and along the announcing sequence of the lifetime (C.6, L1874–1890).

## Main results

* `tendsto_ae_condExp_complex`: Lévy's upward theorem for complex-valued integrable functions;
* `ae_tendsto_condExp_of_eventually` (Lemma 7.10, scalar form): on the event where the conditional mean and characteristic
  function are eventually Gaussian with parameters `mₙ`, `Cₙ`, the means converge to the limit conditional mean and the
  Gaussian characteristic functions converge to the limit conditional characteristic function;
* **`ae_condExp_iSup_histGerm_eq`** (the announced kernel): for a nondecreasing sequence of driving stops `σₙ < ζ` with
  hull germs `Γₙ = Γ(𝓕_{σₙ}, K_{σₙ})`, almost surely on the event that a test `φ` avoids every `K_{σₙ}`, the frozen means
  `(𝔥_{σₙ} − 𝔥₀, φ)` converge to `E[(h⁰, φ) | ⋁ Γₙ]`, the variances `G_{ℍ∖K_{σₙ}}(φ, φ)` decrease to their infimum `C_∞`,
  and `E[e^{i(h⁰, φ)} | ⋁ Γₙ] = e^{i E[(h⁰, φ) | ⋁ Γₙ]} e^{−C_∞/2}`: given the announced information the field off the
  limit hull is still Gaussian, with the limit mean and the limit variance.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal

namespace InteractingSLE

namespace WholeField

open QuantumZipper Ito Coupling LQGMetric

/-! ### Lévy's upward theorem for complex functions, and Lemma 7.10 -/

section Levy

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}

/-- A complex sequence converges once its real and imaginary parts do. -/
theorem tendsto_of_re_im {f : ℕ → ℂ} {z : ℂ} (hre : Tendsto (fun n => (f n).re) atTop (𝓝 z.re))
    (him : Tendsto (fun n => (f n).im) atTop (𝓝 z.im)) : Tendsto f atTop (𝓝 z) := by
  have h := ((Complex.continuous_ofReal.tendsto _).comp hre).add
    (((Complex.continuous_ofReal.tendsto _).comp him).mul_const Complex.I)
  simp only [Function.comp_def, Complex.re_add_im] at h
  exact h

/-- **Lévy's upward theorem for complex-valued functions.** -/
theorem tendsto_ae_condExp_complex [IsFiniteMeasure P] (ℱ : Filtration ℕ mΩ) {g : Ω → ℂ}
    (hg : Integrable g P) :
    ∀ᵐ ω ∂P, Tendsto (fun n => (P[g | ℱ n]) ω) atTop (𝓝 ((P[g | ⨆ n, ℱ n]) ω)) := by
  have hre : ∀ (m : MeasurableSpace Ω), Complex.reCLM ∘ P[g | m] =ᵐ[P] P[Complex.reCLM ∘ g | m] :=
    fun m => Complex.reCLM.comp_condExp_comm hg
  have him : ∀ (m : MeasurableSpace Ω), Complex.imCLM ∘ P[g | m] =ᵐ[P] P[Complex.imCLM ∘ g | m] :=
    fun m => Complex.imCLM.comp_condExp_comm hg
  filter_upwards [ae_all_iff.2 fun n => hre (ℱ n), ae_all_iff.2 fun n => him (ℱ n), hre (⨆ n, ℱ n),
    him (⨆ n, ℱ n), tendsto_ae_condExp (μ := P) (ℱ := ℱ) (Complex.reCLM ∘ g),
    tendsto_ae_condExp (μ := P) (ℱ := ℱ) (Complex.imCLM ∘ g)] with ω h1 h2 h3 h4 h5 h6
  refine tendsto_of_re_im ?_ ?_
  · have e1 : ∀ n, (P[g | ℱ n] ω).re = P[Complex.reCLM ∘ g | ℱ n] ω := fun n => h1 n
    have e3 : (P[g | ⨆ n, ℱ n] ω).re = P[Complex.reCLM ∘ g | ⨆ n, ℱ n] ω := h3
    simp only [e1, e3]
    exact h5
  · have e2 : ∀ n, (P[g | ℱ n] ω).im = P[Complex.imCLM ∘ g | ℱ n] ω := fun n => h2 n
    have e4 : (P[g | ⨆ n, ℱ n] ω).im = P[Complex.imCLM ∘ g | ⨆ n, ℱ n] ω := h4
    simp only [e2, e4]
    exact h6

/-- **Announced conditional identities** (Lemma 7.10 of the additional note, scalar form). Let `ℱ` be a filtration indexed
by `ℕ`, `X` an integrable real variable, and suppose that, almost surely on events `Eₙ`, the conditional mean of `X` given
`ℱₙ` is `mₙ` and its conditional characteristic function is the Gaussian one `e^{i mₙ} e^{−Cₙ/2}`. Then, almost surely
whenever `ω ∈ Eₙ` for all large `n`, `mₙ → E[X | ⋁ ℱₙ]` and `e^{i mₙ} e^{−Cₙ/2} → E[e^{iX} | ⋁ ℱₙ]`. -/
theorem ae_tendsto_condExp_of_eventually [IsFiniteMeasure P] (ℱ : Filtration ℕ mΩ) {X : Ω → ℝ}
    (hXm : Measurable X) {E : ℕ → Set Ω} {m C : ℕ → Ω → ℝ}
    (hm : ∀ n, ∀ᵐ ω ∂P, ω ∈ E n → (P[X | ℱ n]) ω = m n ω)
    (hc : ∀ n, ∀ᵐ ω ∂P, ω ∈ E n → (P[fun ω' => Complex.exp (Complex.I * (X ω' : ℂ)) | ℱ n]) ω =
      Complex.exp (Complex.I * (m n ω : ℂ)) * ((Real.exp (-(1 / 2) * C n ω) : ℝ) : ℂ)) :
    ∀ᵐ ω ∂P, (∀ᶠ n in atTop, ω ∈ E n) →
      Tendsto (fun n => m n ω) atTop (𝓝 ((P[X | ⨆ n, ℱ n]) ω)) ∧
      Tendsto (fun n => Complex.exp (Complex.I * (m n ω : ℂ)) * ((Real.exp (-(1 / 2) * C n ω) : ℝ) : ℂ))
        atTop (𝓝 ((P[fun ω' => Complex.exp (Complex.I * (X ω' : ℂ)) | ⨆ n, ℱ n]) ω)) := by
  have hei : Integrable (fun ω' => Complex.exp (Complex.I * (X ω' : ℂ))) P := by
    refine Integrable.of_bound (C := 1) ?_ (Eventually.of_forall fun ω => ?_)
    · exact (Complex.measurable_exp.comp (measurable_const.mul
        (Complex.measurable_ofReal.comp hXm))).aestronglyMeasurable
    · rw [Complex.norm_exp_I_mul_ofReal]
  filter_upwards [ae_all_iff.2 hm, ae_all_iff.2 hc, tendsto_ae_condExp (μ := P) (ℱ := ℱ) X,
    tendsto_ae_condExp_complex (P := P) ℱ hei] with ω h1 h2 h3 h4 hev
  refine ⟨h3.congr' ?_, h4.congr' ?_⟩
  · filter_upwards [hev] with n hn using h1 n hn
  · filter_upwards [hev] with n hn using h2 n hn

/-- **Lemma 7.10 with a converging variance.** If moreover `Cₙ → c` on the event, the limit conditional characteristic
function is the Gaussian one with the limit mean: `E[e^{iX} | ⋁ ℱₙ] = e^{i E[X | ⋁ ℱₙ]} e^{−c/2}`. -/
theorem ae_condExp_iSup_eq_of_eventually [IsFiniteMeasure P] (ℱ : Filtration ℕ mΩ) {X : Ω → ℝ}
    (hXm : Measurable X) {E : ℕ → Set Ω} {m C : ℕ → Ω → ℝ} {c : Ω → ℝ}
    (hm : ∀ n, ∀ᵐ ω ∂P, ω ∈ E n → (P[X | ℱ n]) ω = m n ω)
    (hc : ∀ n, ∀ᵐ ω ∂P, ω ∈ E n → (P[fun ω' => Complex.exp (Complex.I * (X ω' : ℂ)) | ℱ n]) ω =
      Complex.exp (Complex.I * (m n ω : ℂ)) * ((Real.exp (-(1 / 2) * C n ω) : ℝ) : ℂ)) :
    ∀ᵐ ω ∂P, (∀ᶠ n in atTop, ω ∈ E n) → Tendsto (fun n => C n ω) atTop (𝓝 (c ω)) →
      Tendsto (fun n => m n ω) atTop (𝓝 ((P[X | ⨆ n, ℱ n]) ω)) ∧
      (P[fun ω' => Complex.exp (Complex.I * (X ω' : ℂ)) | ⨆ n, ℱ n]) ω =
        Complex.exp (Complex.I * ((P[X | ⨆ n, ℱ n]) ω : ℂ)) * ((Real.exp (-(1 / 2) * c ω) : ℝ) : ℂ) := by
  filter_upwards [ae_tendsto_condExp_of_eventually ℱ hXm hm hc] with ω hω hev hC
  obtain ⟨h1, h2⟩ := hω hev
  refine ⟨h1, tendsto_nhds_unique h2 ?_⟩
  have hexp : Continuous fun x : ℝ => Complex.exp (Complex.I * (x : ℂ)) :=
    Complex.continuous_exp.comp (continuous_const.mul Complex.continuous_ofReal)
  have hgau : Continuous fun x : ℝ => ((Real.exp (-(1 / 2) * x) : ℝ) : ℂ) :=
    Complex.continuous_ofReal.comp (Real.continuous_exp.comp (continuous_const.mul continuous_id))
  exact ((hexp.tendsto _).comp h1).mul ((hgau.tendsto _).comp hC)

end Levy

/-! ### The kernel along an announcing sequence of driving stops -/

section Announce

universe u

variable {κ : ℝ} {nL nR : ℕ} {xL : Fin nL → ℝ} {xR : Fin nR → ℝ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ}
  {Ω : Type u} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P] {𝓕 : Filtration ℝ≥0 mΩ}
  {W : ℝ≥0 → Ω → ℝ} {VL : Fin nL → ℝ≥0 → Ω → ℝ} {VR : Fin nR → ℝ≥0 → Ω → ℝ} {B : ℝ≥0 → Ω → ℝ}
  {ζ : Ω → ℝ≥0∞} {h : Ω → DistOn upperHalfPlaneOpens}

/-- **The announced germ filtration.** For a nondecreasing sequence of stopping times `σₙ < ζ` of the frozen driving
filtration with hitting-measurable versions `Aₙ` of the hulls `K_{σₙ}`, the history-marked hull germs
`Γₙ = Γ(𝓕_{σₙ}, Aₙ)` form a filtration indexed by `ℕ` (`histGerm_hull_mono`). -/
theorem exists_histGerm_filtration_nat (hC : IsOptionalHullCoupling κ xL xR ρL ρR P 𝓕 W VL VR B ζ h)
    (hκ : 0 < κ) (u₀ : ℂ → ℝ) (hX : IsMeasurableKilledDriving W VL VR ζ) {σ : ℕ → Ω → WithTop ℝ≥0}
    (hσ : ∀ n, IsStoppingTime (drivingFiltration P hX) (σ n)) (hσm : Monotone σ)
    (hσζ : ∀ n, ∀ᵐ ω ∂P, (σ n ω : ℝ≥0∞) < ζ ω)
    {A : ℕ → Ω → Set ℂ} (hA : ∀ n, Measurable[mΩ, hittingSigma] (A n))
    (hAK : ∀ n, ∀ᵐ ω ∂P, A n ω = fwdHull (fun s : ℝ => W s.toNNReal ω) ((σ n ω).untopD 0 : ℝ≥0)) :
    ∃ 𝒢 : Filtration ℕ mΩ, ∀ n, 𝒢 n = histGerm (hσ n).measurableSpace (A n) (centredField h u₀) := by
  have hh0m := measurable_centredField hC.2.1 u₀
  have hE := hC.1
  by_cases hseed : ForceWord.ThresholdCondition ρL ρR 0 xL xR
  · exfalso
    have hF : ∀ᵐ ω ∂P, False := by
      filter_upwards [hE.2.2.2.2, hσζ 0] with ω hp hlt
      rw [WangWu.IsIntegratedSLEPath.lifetime_eq_zero_of_threshold hp hseed] at hlt
      exact ENNReal.not_lt_zero hlt
    obtain ⟨_, h'⟩ := hF.exists
    exact h'
  have : (drivingFiltration P hX).IsRightContinuous := Ito.isRightContinuous_usualAugmentation _ _
  obtain ⟨σ₀, hσ₀, -⟩ := exists_isAnnouncingSeq_of_adapted (𝓖 := drivingFiltration P hX) (B := B)
    (κ := κ) (xL := xL) (xR := xR) (fun s hs h0 => Ito.measurableSet_usualAugmentation_of_null hs h0 0)
    (Ito.adaptedBefore_mono (Ito.le_usualAugmentation _ _) (adaptedBefore_killedDriving_W hX))
    (fun i => Ito.adaptedBefore_mono (Ito.le_usualAugmentation _ _) (adaptedBefore_killedDriving_VL hX i))
    (fun i => Ito.adaptedBefore_mono (Ito.le_usualAugmentation _ _) (adaptedBefore_killedDriving_VR hX i))
    hE.2.2.2.2 (hE.ae_tendsto_threshold hκ) hseed
  let 𝒢 : Filtration ℕ mΩ :=
    { seq := fun n => histGerm (hσ n).measurableSpace (A n) (centredField h u₀)
      mono' := fun m n hmn => histGerm_hull_mono hE hX hσ₀ (hσ m) (hσ n) (hσm hmn) (hσζ m) (hσζ n) (hA m)
        (hA n) (hAK m) (hAK n) hh0m
      le' := fun n => histGerm_le (hσ n).measurableSpace_le (hA n) hh0m }
  exact ⟨𝒢, fun n => rfl⟩

/-- **The kernel given the announced information** (C.3 "Pass the marked kernels to the announced birth", Lemma 7.10 of
the additional note, Aux. lemma 48's `P_z = σ(⋃ G⁰_{σₙ})`). Let `σₙ` be a nondecreasing sequence of stopping times of the
frozen driving filtration with `σₙ < ζ`, with hitting-measurable versions `Aₙ` of the hulls `K_{σₙ}` and bounded harmonic
extensions `uₙ` of the data at `σₙ`, and let `𝒢` be the filtration of the history-marked hull germs
`Γₙ = Γ(𝓕_{σₙ}, Aₙ)` (`exists_histGerm_filtration_nat`). For a test function `φ`, almost surely on the event that `φ`
avoids every `Aₙ`:

* the frozen means `(𝔥_{σₙ} − 𝔥₀, φ)` converge to `E[(h⁰, φ) | ⋁ₙ Γₙ]`;
* the variances `G_{ℍ∖Aₙ}(φ, φ)` decrease to their infimum `C_∞`;
* `E[e^{i(h⁰, φ)} | ⋁ₙ Γₙ] = e^{i E[(h⁰, φ) | ⋁ₙ Γₙ]} e^{−C_∞/2}`.

Here `h⁰ = h − 𝔥₀` is the centred field. -/
theorem ae_condExp_iSup_histGerm_eq (hC : IsOptionalHullCoupling κ xL xR ρL ρR P 𝓕 W VL VR B ζ h)
    (hκ : 0 < κ) {u₀ : ℂ → ℝ}
    (hu₀ : IsBoundedHarmonicExtension (forceBoundaryData κ ρL ρR xL xR) (forceJumpSet xL xR) u₀)
    (hX : IsMeasurableKilledDriving W VL VR ζ) {σ : ℕ → Ω → WithTop ℝ≥0}
    (hσ : ∀ n, IsStoppingTime (drivingFiltration P hX) (σ n)) (hσm : Monotone σ)
    (hσζ : ∀ n, ∀ᵐ ω ∂P, (σ n ω : ℝ≥0∞) < ζ ω)
    {A : ℕ → Ω → Set ℂ} (hA : ∀ n, Measurable[mΩ, hittingSigma] (A n))
    (hAK : ∀ n, ∀ᵐ ω ∂P, A n ω = fwdHull (fun s : ℝ => W s.toNNReal ω) ((σ n ω).untopD 0 : ℝ≥0))
    {𝒢 : Filtration ℕ mΩ} (h𝒢 : ∀ n, 𝒢 n = histGerm (hσ n).measurableSpace (A n) (centredField h u₀))
    {u : ℕ → Ω → ℂ → ℝ}
    (hu : ∀ n ω, IsBoundedHarmonicExtension
      (forceBoundaryData κ ρL ρR (fun i => VL i ((σ n ω).untopD 0) ω - W ((σ n ω).untopD 0) ω)
        (fun i => VR i ((σ n ω).untopD 0) ω - W ((σ n ω).untopD 0) ω))
      (forceJumpSet (fun i => VL i ((σ n ω).untopD 0) ω - W ((σ n ω).untopD 0) ω)
        (fun i => VR i ((σ n ω).untopD 0) ω - W ((σ n ω).untopD 0) ω)) (u n ω))
    (φ : TestOn upperHalfPlaneOpens) :
    ∀ᵐ ω ∂P, (∀ n, Disjoint (tsupport φ) (A n ω)) →
      Tendsto (fun n => (∫ z, couplingMean κ (fun s : ℝ => W s.toNNReal ω) ((σ n ω).untopD 0 : ℝ≥0)
          (u n ω) z * φ z) - ∫ z, u₀ z * φ z)
        atTop (𝓝 ((P[fun ω' => centredField h u₀ ω' φ | ⨆ n, 𝒢 n]) ω)) ∧
      Tendsto (fun n => zeroGFFTestCov (H \ A n ω) φ φ) atTop
        (𝓝 (⨅ n, zeroGFFTestCov (H \ A n ω) φ φ)) ∧
      (P[fun ω' => Complex.exp (Complex.I * (centredField h u₀ ω' φ : ℂ)) | ⨆ n, 𝒢 n]) ω =
        Complex.exp (Complex.I * ((P[fun ω' => centredField h u₀ ω' φ | ⨆ n, 𝒢 n]) ω : ℂ)) *
          ((Real.exp (-(1 / 2) * ⨅ n, zeroGFFTestCov (H \ A n ω) φ φ) : ℝ) : ℂ) := by
  have hh0m := measurable_centredField hC.2.1 u₀
  have hker := hC.2.2.2.choose_spec
  have hk : ∀ n, _ := fun n => by
    have h' := ae_condExp_histGerm_hull_eq hC hκ hu₀ hX (hσ n) (hσζ n) (hA n) (hAK n) (hu n) φ
    rw [← h𝒢 n] at h'
    exact h'
  have hX0m : Measurable fun ω' => centredField h u₀ ω' φ :=
    ((measurable_pi_apply φ).comp (comap_measurable _)).comp hh0m
  have hlim := ae_condExp_iSup_eq_of_eventually (P := P) 𝒢 hX0m
    (E := fun n => {ω | Disjoint (tsupport φ) (A n ω)})
    (c := fun ω => ⨅ n, zeroGFFTestCov (H \ A n ω) φ φ) (fun n => (hk n).1) (fun n => (hk n).2)
  -- the hulls: open complements, increasing
  have hAc : ∀ n, ∀ᵐ ω ∂P, A n ω ⊆ H ∧ IsOpen (H \ A n ω) := fun n => by
    filter_upwards [((hker _ (hσ n) (hσζ n)).1).2.1, hAK n] with ω h1 h2
    rw [h2]
    exact h1
  have hAmono : ∀ n, ∀ᵐ ω ∂P, A n ω ⊆ A (n + 1) ω := fun n => by
    filter_upwards [hAK n, hAK (n + 1), hσζ (n + 1)] with ω h1 h2 h3
    rw [h1, h2]
    refine (QuantumZipper.fwdHull_mono).1 ?_
    have htop : σ (n + 1) ω ≠ ⊤ := fun h' => by rw [h'] at h3; exact absurd h3 (not_lt.2 le_top)
    have hle := hσm (Nat.le_succ n) ω
    rw [← coe_untopD_of_ne_top htop] at hle
    have htop' : σ n ω ≠ ⊤ := ne_top_of_le_ne_top WithTop.coe_ne_top hle
    rw [← coe_untopD_of_ne_top htop'] at hle
    exact NNReal.coe_le_coe.2 (WithTop.coe_le_coe.1 hle)
  filter_upwards [hlim, ae_all_iff.2 hAc, ae_all_iff.2 hAmono] with ω hω hAcω hmono hdisj
  have hanti : Antitone fun n => zeroGFFTestCov (H \ A n ω) φ φ := antitone_nat_of_succ_le fun n =>
    LocalSets.zeroGFFTestCov_mono (hAcω (n + 1)).2 (hAcω n).2 (sdiff_subset_sdiff_right (hmono n)) sdiff_subset φ
  have hbdd : BddBelow (range fun n => zeroGFFTestCov (H \ A n ω) φ φ) :=
    ⟨0, by rintro _ ⟨n, rfl⟩; exact LocalSets.zeroGFFTestCov_self_nonneg (hAcω n).2 sdiff_subset φ⟩
  have hCt := tendsto_atTop_ciInf hanti hbdd
  obtain ⟨h1, h2⟩ := hω (Eventually.of_forall hdisj) hCt
  exact ⟨h1, hCt, h2⟩

end Announce

end WholeField

end InteractingSLE
