/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec2.GirsanovRiemann
import MathFin.Probability.Martingales.UnifIntegrableL2
import MathFin.Probability.Brownian.ExpMartingaleBrownian
import MathFin.Probability.Brownian.Girsanov.GirsanovFiltered
import MathFin.Probability.Martingales.EquivMeasure
import InteractingSLE.Frozen.Spec.IsFilteredBrownianReal

/-!
# The Doléans density and Girsanov's theorem in a general filtration

Packet PROVE-SEC2-GIR. Specification, proof of Theorem 2.2 (`source/spec/p001-048.md` L486: "Girsanov's
theorem applies because the remaining force points introduce a smooth drift to the Brownian motion") and the
explicit density of Aux. lemma 4 (L694–L698): for a bounded drift the density
`Z = exp(∫ θ dB - ½ ∫ θ² ds)` makes `B - ∫ θ ds` a Brownian motion ([KS91] Theorem 3.5.1, [RY99] VIII.1.7).

Sign convention of `formal-mathfin`: for a bounded progressive `θ`, under `Q = Z_T · P` with
`Z_t = exp(-∫₀ᵗ θ dB - ½ ∫₀ᵗ θ²)` (`doleansDensity`), the process `B + ∫₀^· θ` is a `Q`-Brownian
motion. The specification's `D` (an added drift of `W = √κ B + …`) is `θ = -κ^{-1/2} D`.

Main results, for `B` a Brownian motion of the filtration `𝓕` and `θ` bounded, progressively measurable,
and left-continuous at almost every time (`IsRiemannRegular`):

* `martingale_doleansDensity`: the density process is a positive `𝓕`-martingale of mean one;
* `isExpQMartingale_drift`: Girsanov on `[0, T]`, as exponential-martingale data under `Z_T · P`;
* `isFilteredBrownianReal_girsanov`: if `θ` vanishes after `T`, then `B + ∫₀^· θ` is a Brownian motion
  of `𝓕` under `Z_T · P` (the frozen predicate `IsFilteredBrownianReal` of Definition 2.1).
-/

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal

noncomputable section

namespace InteractingSLE

namespace Girsanov

/-! ### Running integrals of a progressive process -/

section Aux

variable {Ω : Type*} [MeasurableSpace Ω]

theorem stronglyMeasurable_integral_comp_aux (t : ℝ≥0) {f : ℝ≥0 → Ω → ℝ}
    (hf : StronglyMeasurable fun p : Set.Iic t × Ω => f p.1 p.2) {g : ℝ → ℝ} (hg : Measurable g) :
    StronglyMeasurable fun ω => ∫ u in (0 : ℝ)..(t : ℝ), g (f u.toNNReal ω) := by
  let φ : Ω × ℝ → Set.Iic t × Ω := fun p =>
    (⟨min p.2.toNNReal t, Set.mem_Iic.2 (min_le_right _ _)⟩, p.1)
  have hφ : Measurable φ :=
    (((measurable_real_toNNReal.min measurable_const).comp measurable_snd).subtype_mk).prodMk
      measurable_fst
  have hF : StronglyMeasurable fun p : Ω × ℝ => g (f (min p.2.toNNReal t) p.1) :=
    (hg.comp (hf.measurable.comp hφ)).stronglyMeasurable
  have h := hF.integral_prod_right' (ν := (volume : Measure ℝ).restrict (Set.Ioc 0 (t : ℝ)))
  convert h using 1
  funext ω
  rw [intervalIntegral.integral_of_le (NNReal.coe_nonneg t)]
  refine setIntegral_congr_fun measurableSet_Ioc fun u hu => ?_
  simp only
  rw [min_eq_left]
  rw [← NNReal.coe_le_coe, Real.coe_toNNReal _ hu.1.le]
  exact hu.2

end Aux

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
  {B θ : ℝ≥0 → Ω → ℝ}

/-- The running integral `∫₀ᵗ g(θ_u) du` of a progressive process is `𝓕 t`-measurable. -/
theorem stronglyMeasurable_integral_comp (hθ : IsStronglyProgressive 𝓕 θ) {g : ℝ → ℝ}
    (hg : Measurable g) (t : ℝ≥0) :
    StronglyMeasurable[𝓕 t] fun ω => ∫ u in (0 : ℝ)..(t : ℝ), g (θ u.toNNReal ω) :=
  @stronglyMeasurable_integral_comp_aux Ω (𝓕 t) t θ (hθ t) g hg

/-- For a fixed `ω`, a progressive process has measurable time paths. -/
theorem measurable_time_of_progressive (hθ : IsStronglyProgressive 𝓕 θ) (ω : Ω) :
    Measurable fun u : ℝ => θ u.toNNReal ω := by
  intro s hs
  -- on `u ≤ n` the path is a section of the jointly measurable restriction to `Iic n × Ω`
  have hsec : ∀ n : ℕ, MeasurableSet {u : ℝ | u ≤ n ∧ θ u.toNNReal ω ∈ s} := by
    intro n
    let ψ : ℝ → Set.Iic (n : ℝ≥0) × Ω := fun u =>
      (⟨min u.toNNReal n, Set.mem_Iic.2 (min_le_right _ _)⟩, ω)
    have hψ : @Measurable ℝ _ _ (Subtype.instMeasurableSpace.prod (𝓕 (n : ℝ≥0))) ψ := by
      refine @Measurable.prodMk _ _ _ _ _ (𝓕 (n : ℝ≥0)) _ _ ?_ ?_
      · exact (measurable_real_toNNReal.min measurable_const).subtype_mk
      · exact @measurable_const _ _ (𝓕 (n : ℝ≥0)) _ ω
    have h := (hθ (n : ℝ≥0)).measurable.comp hψ hs
    have heq : {u : ℝ | u ≤ n ∧ θ u.toNNReal ω ∈ s} = {u : ℝ | u ≤ n} ∩ (fun p : Set.Iic (n : ℝ≥0) × Ω =>
        θ p.1 p.2) ∘ ψ ⁻¹' s := by
      ext u
      simp only [Set.mem_ofPred_eq, Set.mem_inter_iff, Set.mem_preimage, Function.comp_apply, ψ]
      constructor
      · rintro ⟨hu, h⟩
        refine ⟨hu, ?_⟩
        rwa [min_eq_left]
        rw [← NNReal.coe_le_coe]
        rcases le_or_gt u 0 with h0 | h0
        · rw [Real.toNNReal_of_nonpos h0]; simp
        · rw [Real.coe_toNNReal _ h0.le]; exact_mod_cast hu
      · rintro ⟨hu, h⟩
        refine ⟨hu, ?_⟩
        rwa [min_eq_left] at h
        rw [← NNReal.coe_le_coe]
        rcases le_or_gt u 0 with h0 | h0
        · rw [Real.toNNReal_of_nonpos h0]; simp
        · rw [Real.coe_toNNReal _ h0.le]; exact_mod_cast hu
    rw [heq]
    exact (measurableSet_Iic).inter h
  have : (fun u : ℝ => θ u.toNNReal ω) ⁻¹' s = ⋃ n : ℕ, {u : ℝ | u ≤ n ∧ θ u.toNNReal ω ∈ s} := by
    ext u
    simp only [Set.mem_preimage, Set.mem_iUnion, Set.mem_ofPred_eq]
    constructor
    · intro h
      obtain ⟨n, hn⟩ := exists_nat_ge u
      exact ⟨n, hn, h⟩
    · rintro ⟨n, -, h⟩
      exact h
  rw [this]
  exact MeasurableSet.iUnion hsec

/-! ### The density and its dyadic approximations -/

/-- The drift `∫₀ᵗ θ_u du` (with the frozen convention `∫ s in 0..t, f s.toNNReal`). -/
def drift (θ : ℝ≥0 → Ω → ℝ) (t : ℝ≥0) (ω : Ω) : ℝ := ∫ u in (0 : ℝ)..(t : ℝ), θ u.toNNReal ω

/-- The quadratic integral `∫₀ᵗ θ_u² du`. -/
def quadInt (θ : ℝ≥0 → Ω → ℝ) (t : ℝ≥0) (ω : Ω) : ℝ :=
  ∫ u in (0 : ℝ)..(t : ℝ), θ u.toNNReal ω ^ 2

/-- **The Doléans density** `Z_t = exp(-∫₀ᵗ θ dB - ½ ∫₀ᵗ θ² du)`. -/
def doleansDensity (P : Measure Ω) (𝓕 : Filtration ℝ≥0 mΩ) (B θ : ℝ≥0 → Ω → ℝ) (t : ℝ≥0)
    (ω : Ω) : ℝ :=
  Real.exp (-stochIntegral P 𝓕 B θ t ω - quadInt θ t ω / 2)

/-- The simple Doléans densities of the dyadic left-point approximations (`formal-mathfin`). -/
def approxDensity (B θ : ℝ≥0 → Ω → ℝ) (n : ℕ) (t : ℝ≥0) (ω : Ω) : ℝ :=
  MathFin.simpleDoleansExp (X := B) (grid n) (fun i ω => -(θ (grid n i) ω)) (cells n) t ω

/-- The drift of the dyadic left-point approximation. -/
def approxDrift (θ : ℝ≥0 → Ω → ℝ) (n : ℕ) (t : ℝ≥0) (ω : Ω) : ℝ :=
  MathFin.simpleDrift (grid n) (fun i => θ (grid n i)) (cells n) t ω

theorem doleansDensity_pos (t : ℝ≥0) (ω : Ω) : 0 < doleansDensity P 𝓕 B θ t ω := Real.exp_pos _

theorem approxDensity_eq {n : ℕ} {t : ℝ≥0} (htn : t ≤ n) (ω : Ω) :
    approxDensity B θ n t ω
      = Real.exp (-riemannSum B θ n t ω - (∫ u in (0 : ℝ)..(t : ℝ), (stepFun θ n u ω) ^ 2) / 2) := by
  rw [approxDensity, MathFin.SimpleDoleansMoments.simpleDoleansExp_neg_eq,
    ← simpleQuadVar_eq_integral htn, riemannSum_eq_simpleStochSum]
  ring_nf

theorem approxDrift_eq {n : ℕ} {t : ℝ≥0} (htn : t ≤ n) (ω : Ω) :
    approxDrift θ n t ω = ∫ u in (0 : ℝ)..(t : ℝ), stepFun θ n u ω :=
  simpleDrift_eq_integral htn ω

/-- The index shift `n ↦ n + ⌈T⌉₊` makes every approximation cover `[0, T]`. -/
theorem le_shift (T : ℝ≥0) (n : ℕ) : T ≤ ((n + ⌈(T : ℝ)⌉₊ : ℕ) : ℝ≥0) := by
  rw [← NNReal.coe_le_coe]
  push_cast
  exact (Nat.le_ceil _).trans (le_add_of_nonneg_left (Nat.cast_nonneg _))

theorem tendsto_shift (T : ℝ≥0) : Tendsto (fun n : ℕ => n + ⌈(T : ℝ)⌉₊) atTop atTop :=
  tendsto_add_atTop_nat _

variable [IsProbabilityMeasure P]

/-- Along a subsequence of any subsequence, the Riemann sums converge almost surely, and so do the
approximate quadratic integrals and drifts (pathwise, for every index). -/
theorem exists_subseq_ae_tendsto (hB : IsFilteredPreBrownian B 𝓕 P)
    (hθm : StronglyAdapted 𝓕 θ) {C : ℝ} (hθb : ∀ t ω, |θ t ω| ≤ C)
    (hθreg : IsRiemannRegular P θ) (t : ℝ≥0) (ns : ℕ → ℕ) (hns : Tendsto ns atTop atTop) :
    ∃ ms : ℕ → ℕ, StrictMono ms ∧ ∀ᵐ ω ∂P,
      Tendsto (fun k => riemannSum B θ (ns (ms k)) t ω) atTop (𝓝 (stochIntegral P 𝓕 B θ t ω)) ∧
      (∀ u : ℝ≥0, Tendsto (fun n => ∫ v in (0 : ℝ)..(u : ℝ), (stepFun θ n v ω) ^ 2) atTop
        (𝓝 (quadInt θ u ω))) ∧
      (∀ u : ℝ≥0, Tendsto (fun n => ∫ v in (0 : ℝ)..(u : ℝ), stepFun θ n v ω) atTop
        (𝓝 (drift θ u ω))) := by
  have hmeas := (tendstoInMeasure_riemannSum hB hθm hθb hθreg t).comp hns
  obtain ⟨ms, hmono, hms⟩ := hmeas.exists_seq_tendsto_ae
  refine ⟨ms, hmono, ?_⟩
  filter_upwards [hms, hθreg] with ω h1 h2
  exact ⟨h1, fun u => tendsto_integral_stepFun hθb h2 u (fun x => x ^ 2) (continuous_pow 2),
    fun u => tendsto_integral_stepFun hθb h2 u id continuous_id⟩

theorem adapted_gridVal (hθm : StronglyAdapted 𝓕 θ) (n : ℕ) :
    ∀ i, StronglyMeasurable[(𝓕 (grid n i) : MeasurableSpace Ω)] (θ (grid n i)) :=
  fun _ => hθm _

theorem le_grid_cells_of_le {t : ℝ≥0} {c : ℕ} (htc : t ≤ c) (n : ℕ) :
    t ≤ grid (n + c) (cells (n + c)) := by
  rw [grid_cells]
  exact htc.trans (by exact_mod_cast Nat.le_add_left c n)

section Engine

variable [hB : IsFilteredPreBrownian B 𝓕 P]

include hB

/-- Pathwise limit of the shifted approximating densities along an a.e.-subsequence. -/
theorem exists_subseq_ae_tendsto_approxDensity (hθm : StronglyAdapted 𝓕 θ) {C : ℝ}
    (hθb : ∀ t ω, |θ t ω| ≤ C) (hθreg : IsRiemannRegular P θ) {t : ℝ≥0} {c : ℕ} (htc : t ≤ c)
    (ns : ℕ → ℕ) (hns : Tendsto ns atTop atTop) :
    ∃ ms : ℕ → ℕ, ∀ᵐ ω ∂P,
      Tendsto (fun k => approxDensity B θ (ns (ms k) + c) t ω) atTop
        (𝓝 (doleansDensity P 𝓕 B θ t ω)) ∧
      ∀ u : ℝ≥0, u ≤ t → Tendsto (fun k => approxDrift θ (ns (ms k) + c) u ω) atTop
        (𝓝 (drift θ u ω)) := by
  have hns' : Tendsto (fun k => ns k + c) atTop atTop := (tendsto_add_atTop_nat c).comp hns
  obtain ⟨ms, hmono, hms⟩ := exists_subseq_ae_tendsto hB hθm hθb hθreg t _ hns'
  refine ⟨ms, ?_⟩
  have hcomp : Tendsto (fun k => ns (ms k) + c) atTop atTop := hns'.comp hmono.tendsto_atTop
  filter_upwards [hms] with ω ⟨h1, h2, h3⟩
  refine ⟨?_, fun u hut => ?_⟩
  · have hq := (h2 t).comp hcomp
    have h := (Real.continuous_exp.tendsto _).comp ((h1.neg).sub (hq.div_const 2))
    refine h.congr fun k => ?_
    rw [approxDensity_eq (le_grid_cells_of_le htc _ |>.trans_eq (grid_cells _))]
    rfl
  · refine ((h3 u).comp hcomp).congr fun k => ?_
    rw [approxDrift_eq ((le_grid_cells_of_le (hut.trans htc) _).trans_eq (grid_cells _))]
    rfl

theorem memLp_approxDensity (hθm : StronglyAdapted 𝓕 θ) {C : ℝ} (hθb : ∀ t ω, |θ t ω| ≤ C)
    {t : ℝ≥0} {c : ℕ} (htc : t ≤ c) (n : ℕ) : MemLp (approxDensity B θ (n + c) t) 2 P :=
  MathFin.SimpleDoleansMoments.memLp_simpleDoleans_two (X := B) (P := P) (𝓕 := 𝓕)
    (grid_mono _) (grid_zero _) (adapted_gridVal hθm _) (fun _ ω => hθb _ ω) _
    (le_grid_cells_of_le htc n)

theorem sq_integral_approxDensity_le (hθm : StronglyAdapted 𝓕 θ) {C : ℝ}
    (hθb : ∀ t ω, |θ t ω| ≤ C) {t : ℝ≥0} {c : ℕ} (htc : t ≤ c) (n : ℕ) :
    ∫ ω, (approxDensity B θ (n + c) t ω) ^ 2 ∂P ≤ Real.exp (C ^ 2 * (t : ℝ)) :=
  MathFin.SimpleDoleansMoments.sq_integral_simpleDoleans_le (X := B) (P := P) (𝓕 := 𝓕)
    (grid_mono _) (grid_zero _) (adapted_gridVal hθm _) (fun _ ω => hθb _ ω) _
    (le_grid_cells_of_le htc n)

theorem measurable_approxDensity (hθm : StronglyAdapted 𝓕 θ) {C : ℝ} (hθb : ∀ t ω, |θ t ω| ≤ C)
    (n : ℕ) (t : ℝ≥0) : Measurable (approxDensity B θ n t) :=
  MathFin.SimpleDoleansMoments.measurable_simpleDoleans (X := B) (P := P) (𝓕 := 𝓕)
    (grid_mono _) (adapted_gridVal hθm _) (fun _ ω => hθb _ ω) _ t

/-- The density is square integrable (Fatou along an a.e.-subsequence). -/
theorem memLp_doleansDensity (hθm : StronglyAdapted 𝓕 θ) {C : ℝ} (hθb : ∀ t ω, |θ t ω| ≤ C)
    (hθreg : IsRiemannRegular P θ) (t : ℝ≥0) : MemLp (doleansDensity P 𝓕 B θ t) 2 P := by
  have htc : t ≤ (⌈(t : ℝ)⌉₊ : ℝ≥0) := by simpa using le_shift t 0
  obtain ⟨ms, hms⟩ := exists_subseq_ae_tendsto_approxDensity (B := B) hθm hθb hθreg htc id
    tendsto_id
  exact MathFin.memLp_two_of_subseq_ae_of_sq_bound (memLp_approxDensity (B := B) hθm hθb htc)
    (fun n => measurable_approxDensity (B := B) (P := P) hθm hθb _ t)
    (sq_integral_approxDensity_le (B := B) hθm hθb htc)
    ⟨ms, hms.mono fun ω h => h.1⟩

/-- **The set integrals of the approximating densities converge** to those of the density. -/
theorem tendsto_setIntegral_approxDensity (hθm : StronglyAdapted 𝓕 θ) {C : ℝ}
    (hθb : ∀ t ω, |θ t ω| ≤ C) (hθreg : IsRiemannRegular P θ) {t : ℝ≥0} {c : ℕ} (htc : t ≤ c)
    (A : Set Ω) :
    Tendsto (fun n => ∫ ω in A, approxDensity B θ (n + c) t ω ∂P) atTop
      (𝓝 (∫ ω in A, doleansDensity P 𝓕 B θ t ω ∂P)) :=
  MathFin.tendsto_setIntegral_of_subseq_ae_of_sq_bound (memLp_approxDensity (B := B) hθm hθb htc)
    (sq_integral_approxDensity_le (B := B) hθm hθb htc)
    ((memLp_doleansDensity (B := B) hθm hθb hθreg t).mono_exponent (by norm_num))
    (fun ns hns => by
      obtain ⟨ms, hms⟩ := exists_subseq_ae_tendsto_approxDensity (B := B) hθm hθb hθreg htc ns
        hns
      exact ⟨ms, hms.mono fun ω h => h.1⟩) A

/-- `∫_A Z_t = ∫_A Z_s` for `s ≤ t` and `A ∈ 𝓕 s`. -/
theorem setIntegral_doleansDensity_eq (hθm : StronglyAdapted 𝓕 θ) {C : ℝ}
    (hθb : ∀ t ω, |θ t ω| ≤ C) (hθreg : IsRiemannRegular P θ) {s t : ℝ≥0} (hst : s ≤ t)
    {A : Set Ω} (hA : MeasurableSet[𝓕 s] A) :
    ∫ ω in A, doleansDensity P 𝓕 B θ t ω ∂P = ∫ ω in A, doleansDensity P 𝓕 B θ s ω ∂P := by
  set c := ⌈(t : ℝ)⌉₊
  have htc : t ≤ (c : ℝ≥0) := by simpa using le_shift t 0
  have h1 := tendsto_setIntegral_approxDensity (B := B) hθm hθb hθreg htc A
  have h2 := tendsto_setIntegral_approxDensity (B := B) hθm hθb hθreg (hst.trans htc) A
  refine tendsto_nhds_unique h1 (h2.congr fun n => ?_)
  have hmart := MathFin.simpleDoleansExp_isMartingale (X := B) (P := P) (𝓕 := 𝓕) (grid (n + c))
    (grid_mono _) (fun i ω => -(θ (grid (n + c) i) ω)) (fun i => (hθm _).neg)
    (K := C) (fun _ ω => by rw [abs_neg]; exact hθb _ ω) (cells (n + c))
  exact hmart.setIntegral_eq hst hA

theorem integral_doleansDensity (hθm : StronglyAdapted 𝓕 θ) {C : ℝ}
    (hθb : ∀ t ω, |θ t ω| ≤ C) (hθreg : IsRiemannRegular P θ) (t : ℝ≥0) :
    ∫ ω, doleansDensity P 𝓕 B θ t ω ∂P = 1 := by
  set c := ⌈(t : ℝ)⌉₊
  have htc : t ≤ (c : ℝ≥0) := by simpa using le_shift t 0
  have h1 := tendsto_setIntegral_approxDensity (B := B) hθm hθb hθreg htc Set.univ
  simp only [Measure.restrict_univ] at h1
  refine tendsto_nhds_unique h1 (tendsto_const_nhds.congr fun n => ?_)
  exact (MathFin.simpleDoleansExp_integral_eq_one (X := B) (P := P) (𝓕 := 𝓕) (grid (n + c))
    (grid_mono _) (fun i ω => -(θ (grid (n + c) i) ω)) (fun i => (hθm _).neg)
    (K := C) (fun _ ω => by rw [abs_neg]; exact hθb _ ω) (cells (n + c)) t).symm

theorem stronglyMeasurable_doleansDensity (hθ : IsStronglyProgressive 𝓕 θ) {C : ℝ}
    (hθb : ∀ t ω, |θ t ω| ≤ C) (hθreg : IsRiemannRegular P θ) (t : ℝ≥0) :
    StronglyMeasurable[𝓕 t] (doleansDensity P 𝓕 B θ t) := by
  have hI := (isRiemannLimit_stochIntegral hB hθ.stronglyAdapted hθb hθreg t).1
  have hq : StronglyMeasurable[𝓕 t] (quadInt θ t) :=
    stronglyMeasurable_integral_comp hθ (measurable_id.pow_const 2) t
  exact (hI.measurable.neg.sub (hq.measurable.div_const 2)).exp.stronglyMeasurable

/-- **The density martingale.** For a bounded progressive integrand that is left-continuous at almost
every time, the Doléans density `exp(-∫₀ᵗ θ dB - ½ ∫₀ᵗ θ²)` is a positive `𝓕`-martingale of mean
one. -/
theorem martingale_doleansDensity (hθ : IsStronglyProgressive 𝓕 θ) {C : ℝ}
    (hθb : ∀ t ω, |θ t ω| ≤ C) (hθreg : IsRiemannRegular P θ) :
    Martingale (doleansDensity P 𝓕 B θ) 𝓕 P := by
  have hθm := hθ.stronglyAdapted
  refine ⟨fun t => stronglyMeasurable_doleansDensity hθ hθb hθreg t, fun s t hst => ?_⟩
  have hint : Integrable (doleansDensity P 𝓕 B θ t) P :=
    (memLp_doleansDensity (B := B) hθm hθb hθreg t).integrable one_le_two
  exact (ae_eq_condExp_of_forall_setIntegral_eq (𝓕.le s) hint
    (fun A _ _ => ((memLp_doleansDensity (B := B) hθm hθb hθreg s).integrable
      one_le_two).integrableOn)
    (fun A hA _ => (setIntegral_doleansDensity_eq (B := B) hθm hθb hθreg hst hA).symm)
    (stronglyMeasurable_doleansDensity hθ hθb hθreg s).aestronglyMeasurable).symm

end Engine

/-! ### Girsanov's theorem on `[0, T]` -/

/-- The drift-corrected process `B_t + ∫₀ᵗ θ_u du`. -/
def girsanovProcess (B θ : ℝ≥0 → Ω → ℝ) (t : ℝ≥0) (ω : Ω) : ℝ := B t ω + drift θ t ω

/-- The Girsanov measure `Q_T = Z_T · P` of horizon `T`. -/
def girsanovMeasure (P : Measure Ω) (𝓕 : Filtration ℝ≥0 mΩ) (B θ : ℝ≥0 → Ω → ℝ) (T : ℝ≥0) :
    Measure Ω :=
  P.withDensity fun ω => ENNReal.ofReal (doleansDensity P 𝓕 B θ T ω)

section GirsanovT

variable [hB : IsFilteredPreBrownian B 𝓕 P]

include hB

/-- **Mutual absolute continuity.** `Q_T = Z_T · P` is a probability measure equivalent to `P`
(the specification's "absolutely continuous with respect to the one-force-point process", L486). -/
theorem isEquivProbMeasure_girsanovMeasure (hθm : StronglyAdapted 𝓕 θ) {C : ℝ}
    (hθb : ∀ t ω, |θ t ω| ≤ C) (hθreg : IsRiemannRegular P θ) (T : ℝ≥0) :
    MathFin.IsEquivProbMeasure P (girsanovMeasure P 𝓕 B θ T) :=
  MathFin.isEquivProbMeasure_withDensity P (fun ω => doleansDensity_pos T ω)
    ((memLp_doleansDensity (B := B) hθm hθb hθreg T).integrable one_le_two)
    (integral_doleansDensity (B := B) hθm hθb hθreg T)

theorem isProbabilityMeasure_girsanovMeasure (hθm : StronglyAdapted 𝓕 θ) {C : ℝ}
    (hθb : ∀ t ω, |θ t ω| ≤ C) (hθreg : IsRiemannRegular P θ) (T : ℝ≥0) :
    IsProbabilityMeasure (girsanovMeasure P 𝓕 B θ T) :=
  (isEquivProbMeasure_girsanovMeasure hθm hθb hθreg T).isProb

/-- The limit engine for the mixed products `exp(a (B_u + drift) - a²u/2) · Z_T`. -/
theorem tendsto_setIntegral_mixed (hθm : StronglyAdapted 𝓕 θ) {C : ℝ}
    (hθb : ∀ t ω, |θ t ω| ≤ C) (hθreg : IsRiemannRegular P θ) {T : ℝ≥0} {c : ℕ}
    (hTc : T ≤ c) (a : ℝ) {u : ℝ≥0} (huT : u ≤ T) (A : Set Ω) :
    Tendsto (fun n => ∫ ω in A, Real.exp (a * (B u ω + approxDrift θ (n + c) u ω)
        - a ^ 2 * (u : ℝ) / 2) * approxDensity B θ (n + c) T ω ∂P) atTop
      (𝓝 (∫ ω in A, Real.exp (a * girsanovProcess B θ u ω - a ^ 2 * (u : ℝ) / 2)
        * doleansDensity P 𝓕 B θ T ω ∂P)) := by
  have hmem := fun n => MathFin.SimpleDoleansMoments.memLp_mixedProduct_two (X := B) (P := P)
    (𝓕 := 𝓕) (grid_mono (n + c)) (grid_zero _) (adapted_gridVal hθm _) (fun _ ω => hθb _ ω) a
    (cells (n + c)) huT (le_grid_cells_of_le hTc n)
  have hM := fun n => MathFin.SimpleDoleansMoments.sq_integral_mixedProduct_le (X := B) (P := P)
    (𝓕 := 𝓕) (grid_mono (n + c)) (grid_zero _) (adapted_gridVal hθm _) (fun _ ω => hθb _ ω) a
    (cells (n + c)) huT (le_grid_cells_of_le hTc n)
  have hmeas : ∀ n, Measurable fun ω => Real.exp (a * (B u ω + approxDrift θ (n + c) u ω)
      - a ^ 2 * (u : ℝ) / 2) * approxDensity B θ (n + c) T ω := fun n =>
    (MathFin.SimpleDoleansMoments.measurable_driftExp (X := B) (P := P) (𝓕 := 𝓕)
      (grid_mono (n + c)) (adapted_gridVal hθm _) a _ u).mul
      (measurable_approxDensity (B := B) (P := P) hθm hθb _ T)
  have hsub : ∀ ns : ℕ → ℕ, Tendsto ns atTop atTop → ∃ ms : ℕ → ℕ, ∀ᵐ ω ∂P,
      Tendsto (fun k => Real.exp (a * (B u ω + approxDrift θ (ns (ms k) + c) u ω)
        - a ^ 2 * (u : ℝ) / 2) * approxDensity B θ (ns (ms k) + c) T ω) atTop
        (𝓝 (Real.exp (a * girsanovProcess B θ u ω - a ^ 2 * (u : ℝ) / 2)
          * doleansDensity P 𝓕 B θ T ω)) := by
    intro ns hns
    obtain ⟨ms, hms⟩ := exists_subseq_ae_tendsto_approxDensity (B := B) hθm hθb hθreg hTc ns hns
    refine ⟨ms, hms.mono fun ω h => ?_⟩
    have hd := h.2 u huT
    have he : Tendsto (fun k => Real.exp (a * (B u ω + approxDrift θ (ns (ms k) + c) u ω)
        - a ^ 2 * (u : ℝ) / 2)) atTop
        (𝓝 (Real.exp (a * girsanovProcess B θ u ω - a ^ 2 * (u : ℝ) / 2))) :=
      (Real.continuous_exp.tendsto _).comp
        (((tendsto_const_nhds.add hd).const_mul a).sub tendsto_const_nhds)
    exact he.mul h.1
  have hg2 := MathFin.memLp_two_of_subseq_ae_of_sq_bound hmem hmeas hM (hsub id tendsto_id)
  exact MathFin.tendsto_setIntegral_of_subseq_ae_of_sq_bound hmem hM
    (hg2.mono_exponent (by norm_num)) hsub A

omit [IsProbabilityMeasure P] in
theorem stronglyAdapted_girsanovProcess (hθ : IsStronglyProgressive 𝓕 θ) :
    StronglyAdapted 𝓕 (girsanovProcess B θ) := fun t =>
  (hB.stronglyAdapted t).add (stronglyMeasurable_integral_comp hθ measurable_id t)

/-- **Girsanov's theorem on `[0, T]`** (bounded progressive integrand, left-continuous at almost
every time, arbitrary filtration): under `Q_T = Z_T · P`, every `exp(a (B + ∫θ) - a² t/2)` is a
martingale on `[0, T]`. -/
theorem isExpQMartingale_girsanov (hθ : IsStronglyProgressive 𝓕 θ) {C : ℝ}
    (hθb : ∀ t ω, |θ t ω| ≤ C) (hθreg : IsRiemannRegular P θ) (T : ℝ≥0) :
    MathFin.IsExpQMartingale (girsanovMeasure P 𝓕 B θ T) 𝓕 (girsanovProcess B θ) T := by
  have hθm := hθ.stronglyAdapted
  have hZm : AEStronglyMeasurable (doleansDensity P 𝓕 B θ T) P :=
    (memLp_doleansDensity (B := B) hθm hθb hθreg T).aestronglyMeasurable
  have hZpos : ∀ ω, 0 ≤ doleansDensity P 𝓕 B θ T ω := fun ω => (doleansDensity_pos T ω).le
  refine ⟨stronglyAdapted_girsanovProcess (P := P) hθ, ?_, ?_⟩
  · have hac : girsanovMeasure P 𝓕 B θ T ≪ P := withDensity_absolutelyContinuous _ _
    filter_upwards [hac.ae_le (MathFin.X0_ae_eq_zero (X := B) (𝓕 := 𝓕) (P := P))] with ω hω
    simp [girsanovProcess, drift, hω]
  · intro a s t hst htT A hA
    have hAm : MeasurableSet A := 𝓕.le s A hA
    set c := ⌈(T : ℝ)⌉₊
    have hTc : T ≤ (c : ℝ≥0) := by simpa using le_shift T 0
    have h1 := tendsto_setIntegral_mixed (B := B) hθm hθb hθreg hTc a htT A
    have h2 := tendsto_setIntegral_mixed (B := B) hθm hθb hθreg hTc a (hst.trans htT) A
    rw [girsanovMeasure, MathFin.setIntegral_withDensity_ofReal hZm hZpos _ hAm,
      MathFin.setIntegral_withDensity_ofReal hZm hZpos _ hAm]
    refine tendsto_nhds_unique h1 (h2.congr fun n => ?_)
    have hfield : ∫ ω in A, Real.exp (a * (B t ω + approxDrift θ (n + c) t ω)
          - a ^ 2 * (t : ℝ) / 2)
          ∂(P.withDensity fun ω => ENNReal.ofReal (approxDensity B θ (n + c) T ω))
        = ∫ ω in A, Real.exp (a * (B s ω + approxDrift θ (n + c) s ω) - a ^ 2 * (s : ℝ) / 2)
          ∂(P.withDensity fun ω => ENNReal.ofReal (approxDensity B θ (n + c) T ω)) :=
      (MathFin.isExpQMartingale_BthetaSimple (X := B) (𝓕 := 𝓕) (P := P)
        (grid (n + c)) (grid_mono _) (grid_zero _) (fun i => θ (grid (n + c) i))
        (adapted_gridVal hθm _) (fun _ ω => hθb _ ω) (cells (n + c))
        (le_grid_cells_of_le hTc n)).martingale a hst htT hA
    have hZnm : AEStronglyMeasurable (approxDensity B θ (n + c) T) P :=
      (measurable_approxDensity (B := B) (P := P) hθm hθb (n + c) T).aestronglyMeasurable
    have hZnpos : ∀ ω, 0 ≤ approxDensity B θ (n + c) T ω := fun ω =>
      (MathFin.simpleDoleansExp_pos _ _ _ _ ω).le
    rw [MathFin.setIntegral_withDensity_ofReal hZnm hZnpos _ hAm,
      MathFin.setIntegral_withDensity_ofReal hZnm hZnpos _ hAm] at hfield
    exact hfield.symm

end GirsanovT

/-! ### All horizons: a drift that vanishes after `T` -/

theorem intervalIntegrable_time (hθ : IsStronglyProgressive 𝓕 θ) {C : ℝ}
    (hθb : ∀ t ω, |θ t ω| ≤ C) (ω : Ω) (a b : ℝ) :
    IntervalIntegrable (fun u : ℝ => θ u.toNNReal ω) volume a b :=
  (intervalIntegrable_const (c := C)).mono_fun'
    (measurable_time_of_progressive hθ ω).aestronglyMeasurable
    (ae_of_all _ fun u => by show ‖θ u.toNNReal ω‖ ≤ C; rw [Real.norm_eq_abs]; exact hθb _ ω)

theorem continuous_drift (hθ : IsStronglyProgressive 𝓕 θ) {C : ℝ} (hθb : ∀ t ω, |θ t ω| ≤ C)
    (ω : Ω) : Continuous fun t => drift θ t ω :=
  (intervalIntegral.continuous_primitive (intervalIntegrable_time hθ hθb ω) 0).comp
    NNReal.continuous_coe

theorem drift_eq_of_le (hθ : IsStronglyProgressive 𝓕 θ) {C : ℝ} (hθb : ∀ t ω, |θ t ω| ≤ C)
    {T : ℝ≥0} (hθT : ∀ t ω, T ≤ t → θ t ω = 0) {t : ℝ≥0} (hTt : T ≤ t) (ω : Ω) :
    drift θ t ω = drift θ T ω := by
  rw [drift, drift, ← intervalIntegral.integral_add_adjacent_intervals
    (intervalIntegrable_time hθ hθb ω 0 T) (intervalIntegrable_time hθ hθb ω T t), add_eq_left]
  have h : Set.EqOn (fun u : ℝ => θ u.toNNReal ω) (fun _ => 0) (Set.uIcc (T : ℝ) (t : ℝ)) :=
    fun u hu => by
      rw [Set.uIcc_of_le (by exact_mod_cast hTt)] at hu
      apply hθT
      rw [← NNReal.coe_le_coe, Real.coe_toNNReal _ ((NNReal.coe_nonneg T).trans hu.1)]
      exact hu.1
  rw [intervalIntegral.integral_congr h]
  simp

section AllHorizons

variable [hB : IsFilteredPreBrownian B 𝓕 P]

include hB

/-- **The exponential martingale step past the horizon** (as in `formal-mathfin`'s
`setIntegral_expBthetaPred_tail`): for `T ≤ s ≤ t`, the drift is frozen and the increment
`B_t - B_s` is independent of `𝓕 s`. -/
theorem setIntegral_girsanov_tail (hθ : IsStronglyProgressive 𝓕 θ) {C : ℝ}
    (hθb : ∀ t ω, |θ t ω| ≤ C) (hθreg : IsRiemannRegular P θ) {T : ℝ≥0}
    (hθT : ∀ t ω, T ≤ t → θ t ω = 0) (a : ℝ) {s t : ℝ≥0} (hTs : T ≤ s) (hst : s ≤ t)
    {A : Set Ω} (hA : MeasurableSet[𝓕 s] A) :
    ∫ ω in A, Real.exp (a * girsanovProcess B θ t ω - a ^ 2 * (t : ℝ) / 2)
        ∂(girsanovMeasure P 𝓕 B θ T)
      = ∫ ω in A, Real.exp (a * girsanovProcess B θ s ω - a ^ 2 * (s : ℝ) / 2)
        ∂(girsanovMeasure P 𝓕 B θ T) := by
  have hθm := hθ.stronglyAdapted
  have hAm : MeasurableSet A := 𝓕.le s A hA
  have hZs : StronglyMeasurable[𝓕 s] (doleansDensity P 𝓕 B θ T) :=
    (stronglyMeasurable_doleansDensity (B := B) hθ hθb hθreg T).mono (𝓕.mono hTs)
  have hZm : AEStronglyMeasurable (doleansDensity P 𝓕 B θ T) P :=
    (hZs.mono (𝓕.le s)).aestronglyMeasurable
  have hZpos : ∀ ω, 0 ≤ doleansDensity P 𝓕 B θ T ω := fun ω => (doleansDensity_pos T ω).le
  rw [girsanovMeasure, MathFin.setIntegral_withDensity_ofReal hZm hZpos _ hAm,
    MathFin.setIntegral_withDensity_ofReal hZm hZpos _ hAm]
  set Ns : Ω → ℝ := fun ω => Real.exp (a * girsanovProcess B θ s ω - a ^ 2 * (s : ℝ) / 2)
  set G : Ω → ℝ := fun ω => Real.exp (a * (B t ω - B s ω) - a ^ 2 * ((t : ℝ) - s) / 2)
  have hsplit : ∀ ω, Real.exp (a * girsanovProcess B θ t ω - a ^ 2 * (t : ℝ) / 2)
      = Ns ω * G ω := fun ω => by
    simp only [Ns, G, ← Real.exp_add, girsanovProcess,
      drift_eq_of_le hθ hθb hθT (hTs.trans hst), drift_eq_of_le hθ hθb hθT hTs]
    congr 1
    ring
  have hNs : StronglyMeasurable[𝓕 s] Ns :=
    (((stronglyAdapted_girsanovProcess (P := P) hθ s).measurable.const_mul a).sub_const
      _).exp.stronglyMeasurable
  have hfsm : StronglyMeasurable[𝓕 s] (A.indicator fun ω => Ns ω * doleansDensity P 𝓕 B θ T ω) :=
    (hNs.mul hZs).indicator hA
  have hBt : Measurable (B t) := ((hB.stronglyAdapted t).mono (𝓕.le t)).measurable
  have hBs : Measurable (B s) := ((hB.stronglyAdapted s).mono (𝓕.le s)).measurable
  have hGm : Measurable[MeasurableSpace.comap (B t - B s) inferInstance] G := by
    have hΔ : Measurable[MeasurableSpace.comap (B t - B s) inferInstance] (B t - B s) :=
      comap_measurable _
    exact ((hΔ.const_mul a).sub_const _).exp
  have hindep : IndepFun (A.indicator fun ω => Ns ω * doleansDensity P 𝓕 B θ T ω) G P := by
    rw [IndepFun_iff_Indep]
    exact indep_of_indep_of_le_left (indep_of_indep_of_le_right (hB.indep s t hst).symm
      hGm.comap_le) hfsm.measurable.comap_le
  have hG1 : ∫ ω, G ω ∂P = 1 := MathFin.integral_exp_increment hB.toIsPreBrownianReal hst a
  calc ∫ ω in A, Real.exp (a * girsanovProcess B θ t ω - a ^ 2 * (t : ℝ) / 2)
          * doleansDensity P 𝓕 B θ T ω ∂P
      = ∫ ω, (A.indicator fun ω => Ns ω * doleansDensity P 𝓕 B θ T ω) ω * G ω ∂P := by
        rw [← integral_indicator hAm]
        refine integral_congr_ae (ae_of_all _ fun ω => ?_)
        by_cases hωA : ω ∈ A
        · simp only [Set.indicator_of_mem hωA, hsplit]
          ring
        · simp [Set.indicator_of_notMem hωA]
    _ = (∫ ω, (A.indicator fun ω => Ns ω * doleansDensity P 𝓕 B θ T ω) ω ∂P) * ∫ ω, G ω ∂P :=
        hindep.integral_fun_mul_eq_mul_integral (hfsm.mono (𝓕.le s)).aestronglyMeasurable
          (((hBt.sub hBs).const_mul a).sub_const _).exp.aestronglyMeasurable
    _ = ∫ ω in A, Ns ω * doleansDensity P 𝓕 B θ T ω ∂P := by
        rw [hG1, mul_one, integral_indicator hAm]

/-- The exponential-martingale data for every horizon, when the integrand vanishes after `T`. -/
theorem isExpQMartingale_girsanov_all (hθ : IsStronglyProgressive 𝓕 θ) {C : ℝ}
    (hθb : ∀ t ω, |θ t ω| ≤ C) (hθreg : IsRiemannRegular P θ) {T : ℝ≥0}
    (hθT : ∀ t ω, T ≤ t → θ t ω = 0) (T' : ℝ≥0) :
    MathFin.IsExpQMartingale (girsanovMeasure P 𝓕 B θ T) 𝓕 (girsanovProcess B θ) T' := by
  have hT := isExpQMartingale_girsanov (B := B) (P := P) hθ hθb hθreg T
  refine ⟨hT.adapted, hT.zero_start, ?_⟩
  intro a s t hst _ A hA
  by_cases hsT : T ≤ s
  · exact setIntegral_girsanov_tail hθ hθb hθreg hθT a hsT hst hA
  · push Not at hsT
    by_cases htT : t ≤ T
    · exact hT.martingale a hst htT hA
    · push Not at htT
      have hAT : MeasurableSet[𝓕 T] A := 𝓕.mono hsT.le A hA
      exact (setIntegral_girsanov_tail hθ hθb hθreg hθT a le_rfl htT.le hAT).trans
        (hT.martingale a hsT.le le_rfl hA)

end AllHorizons

/-! ### The frozen form: a Brownian motion of the filtration under the changed measure -/

omit [IsProbabilityMeasure P] in
/-- A Brownian motion of the filtration in the sense of Definition 2.1 (the frozen
`IsFilteredBrownianReal`) is a filtered pre-Brownian motion in the sense of `brownian-motion`. -/
theorem isFilteredPreBrownian_of_isFilteredBrownianReal (h : IsFilteredBrownianReal 𝓕 B P) :
    IsFilteredPreBrownian B 𝓕 P where
  toIsPreBrownianReal := h.1.toIsPreBrownianReal
  stronglyAdapted := fun t => (h.2.1 t).stronglyMeasurable
  indep := h.2.2

/-- **Girsanov's theorem for a Brownian motion of an arbitrary filtration** ([KS91] Theorem 3.5.1,
[RY99] VIII.1.7, bounded case). Let `B` be a Brownian motion of `𝓕` (Definition 2.1) and `θ` a
bounded progressive process that is left-continuous at almost every time and vanishes after `T`.
Then under `Q_T = Z_T · P`, `Z_T = exp(-∫₀ᵀ θ dB - ½ ∫₀ᵀ θ²)`, the process `B + ∫₀^· θ` is again a
Brownian motion of `𝓕`, and `Q_T` is a probability measure equivalent to `P`. -/
theorem isFilteredBrownianReal_girsanov (hBF : IsFilteredBrownianReal 𝓕 B P)
    (hθ : IsStronglyProgressive 𝓕 θ) {C : ℝ} (hθb : ∀ t ω, |θ t ω| ≤ C)
    (hθreg : IsRiemannRegular P θ) {T : ℝ≥0} (hθT : ∀ t ω, T ≤ t → θ t ω = 0) :
    IsFilteredBrownianReal 𝓕 (girsanovProcess B θ) (girsanovMeasure P 𝓕 B θ T) := by
  have := isFilteredPreBrownian_of_isFilteredBrownianReal hBF
  have hθm := hθ.stronglyAdapted
  have := isProbabilityMeasure_girsanovMeasure (B := B) hθm hθb hθreg T
  have hall := isExpQMartingale_girsanov_all (B := B) (P := P) hθ hθb hθreg hθT
  have hcont : ∀ᵐ ω ∂(girsanovMeasure P 𝓕 B θ T), Continuous (girsanovProcess B θ · ω) := by
    have hac : girsanovMeasure P 𝓕 B θ T ≪ P := withDensity_absolutelyContinuous _ _
    filter_upwards [hac.ae_le hBF.1.cont] with ω hω
    exact hω.add (continuous_drift hθ hθb ω)
  exact ⟨MathFin.isBrownianReal_of_expMartingale hall hcont,
    (stronglyAdapted_girsanovProcess (P := P) hθ).adapted,
    (MathFin.isFilteredPreBrownian_of_expMartingale hall).indep⟩

end Girsanov

end InteractingSLE
