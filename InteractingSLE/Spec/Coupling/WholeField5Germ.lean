/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Coupling.WholeField5Ext
import InteractingSLE.Spec.Coupling.WholeField2Germ
import InteractingSLE.Spec.Sec6.Prop65DDS
import MathFin.Probability.Martingales.UnifIntegrableL2

/-!
# The germ filtration up to the lifetime: abstract steps

Packet PROVE-WHOLEFIELD5, (WF7) (follow-up note C.2, `ig1_followup_proofs.txt` L1522–1550: "Lévy's characterization,
followed by localization over the announcing times and capacity bounds, proves that `B` is Brownian in the enlarged
germ filtration up to `T_*`").

PROVE-WHOLEFIELD4 made the noise Brownian in the germ filtration stopped at one bounded stop `S < ζ`
(`martingale_stoppedNoise_germ_exp`). Along an announcing sequence `S_m ↑ ζ` these filtrations increase; their
supremum `𝒢^∞_u = ⋁_m 𝒢^{(m)}_u` carries the noise up to the lifetime. This file proves the two abstract steps.

* `measurableSet_histGerm_inter` (**germ events stop like stopping σ-algebras**): if `E ∩ G ∈ ℋ₂` for every
  `E ∈ ℋ₁`, `G ∈ ℋ₂`, `A₁` is `ℋ₁`-measurable and `A₁ ⊆ A₂` almost surely on `G`, then `E ∩ G ∈ Γ(ℋ₂, A₂)` for every
  `E ∈ Γ(ℋ₁, A₁)`. With `ℋ₁ = 𝓕_T`, `ℋ₂ = 𝓕_U`, `G = {T ≤ U}`: the germ at `T` restricted to `{T ≤ U}` lies in the
  germ at `U`.
* `annClock S u = ⨆_m (u ∧ S_m)`: the clock `u ∧ ζ` of the announcing sequence, defined everywhere.
* `isTCExpMartingale_annClock` (**the exponential martingale up to the lifetime**): if each `e^{a B_{t∧S_m} − a²(t∧S_m)/2}`
  is a martingale of `𝒢^{(m)}` (increasing in `m`, containing the null sets), then the data `IsTCExpMartingale` of the
  completion hold for `⋁_m 𝒢^{(m)}`, the noise `B_{ℓ_u}` and the clock `ℓ_u = ⨆_m (u ∧ S_m)`. Proof: on a set of
  `𝒢^{(m₀)}_s` the martingale identities hold for all `m ≥ m₀`; Vitali's theorem with the `L²` bound
  `E[e^{2aY − a²c}] ≤ e^{a²u} E[e^{2aY − (2a)²c/2}] = e^{a²u}` passes them to the limit; π-λ on the increasing union
  (`Sec6.Prop65.setLIntegral_eq_of_iSup`) and simple-function approximation of the weight finish.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped ENNReal NNReal

namespace InteractingSLE

namespace WholeField

open LocalSets QuantumZipper LQGMetric

/-! ### Germ events at a stopping time, restricted to `{T ≤ U}` -/

section GermInter

variable {Ω : Type*} {ℋ₁ ℋ₂ : MeasurableSpace Ω} [mΩ : MeasurableSpace Ω] {P : Measure Ω}

/-- The σ-algebra of the sets whose trace on `G` belongs to `M` (for `G ∈ M`). -/
@[instance_reducible]
def traceSigma (M : MeasurableSpace Ω) (G : Set Ω) (hG : MeasurableSet[M] G) : MeasurableSpace Ω where
  MeasurableSet' E := MeasurableSet[M] (E ∩ G)
  measurableSet_empty := by simp only [empty_inter]; exact @MeasurableSet.empty _ M
  measurableSet_compl E hE := by
    have e : Eᶜ ∩ G = G \ (E ∩ G) := by
      ext ω; simp only [mem_inter_iff, mem_compl_iff, Set.mem_sdiff]; tauto
    rw [e]
    exact hG.diff hE
  measurableSet_iUnion f hf := by
    rw [iUnion_inter]
    exact MeasurableSet.iUnion hf

/-- **Germ events stop like stopping σ-algebras.** Let `G ∈ ℋ₂` with `E ∩ G ∈ ℋ₂` for every `E ∈ ℋ₁`, let `A₁` be
`ℋ₁`-measurable with `A₁ ⊆ A₂` almost surely on `G`, and let `ℋ₂ ≤ mΩ` contain the null sets. Then `E ∩ G ∈ Γ(ℋ₂, A₂)`
for every `E ∈ Γ(ℋ₁, A₁)`. -/
theorem measurableSet_histGerm_inter {G : Set Ω} (hG : MeasurableSet[ℋ₂] G)
    (hℋ : ∀ E, MeasurableSet[ℋ₁] E → MeasurableSet[ℋ₂] (E ∩ G)) (hℋ₂ : ℋ₂ ≤ mΩ)
    (hnull : ∀ N : Set Ω, MeasurableSet[mΩ] N → P N = 0 → MeasurableSet[ℋ₂] N)
    {A₁ A₂ : Ω → Set ℂ} (hA₁ : Measurable[ℋ₁, hittingSigma] A₁) (hA₂ : Measurable[mΩ, hittingSigma] A₂)
    {h : Ω → DistOn upperHalfPlaneOpens} (hh : Measurable h) (hsub : ∀ᵐ ω ∂P, ω ∈ G → A₁ ω ⊆ A₂ ω)
    {E : Set Ω} (hE : MeasurableSet[histGerm ℋ₁ A₁ h] E) : MeasurableSet[histGerm ℋ₂ A₂ h] (E ∩ G) := by
  rw [histGerm, MeasurableSpace.measurableSet_iInf] at hE ⊢
  intro n
  have hδ : 0 < 1 / ((n : ℝ) + 1) := by positivity
  have hM₂ : ℋ₂ ⊔ germSigmaAt A₂ h (1 / ((n : ℝ) + 1)) ≤ mΩ := sup_le hℋ₂ (germSigmaAt_le' hA₂ hh hδ)
  have hGM : MeasurableSet[ℋ₂ ⊔ germSigmaAt A₂ h (1 / ((n : ℝ) + 1))] G :=
    le_sup_left (α := MeasurableSpace Ω) _ hG
  have hle : ℋ₁ ⊔ germSigmaAt A₁ h (1 / ((n : ℝ) + 1)) ≤ traceSigma _ G hGM := by
    refine sup_le (fun E hE => le_sup_left (α := MeasurableSpace Ω) _ (hℋ E hE))
      (sup_le ?_ (MeasurableSpace.generateFrom_le ?_))
    · rintro _ ⟨S, hS, rfl⟩
      exact le_sup_left (α := MeasurableSpace Ω) _ (hℋ _ (hA₁ hS))
    · rintro _ ⟨φ, B, hB, rfl⟩
      have hS := measurableSet_subset_germNbhd φ.hasCompactSupport.isCompact φ.tsupport_subset hδ
      have h1 : MeasurableSet[ℋ₂]
          ({ω | tsupport φ ⊆ germNbhd (1 / ((n : ℝ) + 1)) (A₁ ω)} ∩ G) := hℋ _ (hA₁ hS)
      have hφ : MeasurableSet[mΩ] ((fun ω => h ω φ) ⁻¹' B) := (measurable_distOn_apply φ).comp hh hB
      have hF : MeasurableSet[ℋ₂ ⊔ germSigmaAt A₂ h (1 / ((n : ℝ) + 1))]
          (({ω | tsupport φ ⊆ germNbhd (1 / ((n : ℝ) + 1)) (A₁ ω)} ∩ G) ∩
            ({ω | tsupport φ ⊆ germNbhd (1 / ((n : ℝ) + 1)) (A₂ ω)} ∩ (fun ω => h ω φ) ⁻¹' B)) :=
        (le_sup_left (α := MeasurableSpace Ω) _ h1).inter (le_sup_right (α := MeasurableSpace Ω) _
          (le_sup_right (α := MeasurableSpace Ω) _
            (MeasurableSpace.measurableSet_generateFrom ⟨φ, B, hB, rfl⟩)))
      have hEm : MeasurableSet[mΩ] (({ω | tsupport φ ⊆ germNbhd (1 / ((n : ℝ) + 1)) (A₁ ω)} ∩
          (fun ω => h ω φ) ⁻¹' B) ∩ G) := by
        have e : ({ω | tsupport φ ⊆ germNbhd (1 / ((n : ℝ) + 1)) (A₁ ω)} ∩ (fun ω => h ω φ) ⁻¹' B) ∩ G =
            ({ω | tsupport φ ⊆ germNbhd (1 / ((n : ℝ) + 1)) (A₁ ω)} ∩ G) ∩ (fun ω => h ω φ) ⁻¹' B := by
          ext ω; simp only [mem_inter_iff]; tauto
        rw [e]
        exact (hℋ₂ _ h1).inter hφ
      refine measurableSet_of_ae_eq hM₂ (fun N hN h0 => le_sup_left (α := MeasurableSpace Ω) _ (hnull N hN h0))
        hEm hF ?_
      filter_upwards [hsub] with ω hω
      apply propext
      simp only [mem_inter_iff, mem_ofPred_eq, mem_preimage]
      exact ⟨fun h' => ⟨⟨h'.1.1, h'.2⟩, h'.1.1.trans (germNbhd_mono_set (hω h'.2)), h'.1.2⟩,
        fun h' => ⟨⟨h'.1.1, h'.2.2⟩, h'.1.2⟩⟩
  exact hle _ (hE n)

end GermInter

/-! ### The clock of an announcing sequence -/

section Clock

variable {Ω : Type*}

/-- The clock `ℓ_u = ⨆_m (u ∧ S_m)` of a sequence of times (`= u ∧ ζ` for an announcing sequence of `ζ`). -/
def annClock (S : ℕ → Ω → ℝ≥0) (u : ℝ≥0) (ω : Ω) : ℝ≥0 := ⨆ m, min u (S m ω)

theorem bddAbove_min (S : ℕ → Ω → ℝ≥0) (u : ℝ≥0) (ω : Ω) : BddAbove (range fun m => min u (S m ω)) :=
  ⟨u, by rintro _ ⟨m, rfl⟩; exact min_le_left _ _⟩

theorem annClock_le (S : ℕ → Ω → ℝ≥0) (u : ℝ≥0) (ω : Ω) : annClock S u ω ≤ u :=
  ciSup_le fun _ => min_le_left _ _

theorem min_le_annClock (S : ℕ → Ω → ℝ≥0) (u : ℝ≥0) (ω : Ω) (m : ℕ) : min u (S m ω) ≤ annClock S u ω :=
  le_ciSup (bddAbove_min S u ω) m

theorem annClock_min_eq (S : ℕ → Ω → ℝ≥0) {s u : ℝ≥0} (hsu : s ≤ u) (ω : Ω) :
    annClock S s ω = min s (annClock S u ω) := by
  rw [annClock, annClock, ← Sec6.Prop65.IsDDSLevels.iSup_min_eq (bddAbove_min S u ω) s]
  congr 1
  funext m
  rw [← min_assoc, min_eq_left hsu]

theorem annClock_eq_of_le {S : ℕ → Ω → ℝ≥0} {u : ℝ≥0} {ω : Ω} {m : ℕ} (h : u ≤ S m ω) :
    annClock S u ω = u :=
  le_antisymm (annClock_le S u ω) ((min_eq_left h).symm.le.trans (min_le_annClock S u ω m))

theorem annClock_zero (S : ℕ → Ω → ℝ≥0) (ω : Ω) : annClock S 0 ω = 0 :=
  le_antisymm (annClock_le S 0 ω) zero_le

theorem continuous_annClock (S : ℕ → Ω → ℝ≥0) (ω : Ω) : Continuous fun u => annClock S u ω := by
  refine continuous_iff_continuousAt.2 fun u => ?_
  have hev : (fun v => min v (annClock S (u + 1) ω)) =ᶠ[𝓝 u] fun v => annClock S v ω := by
    filter_upwards [gt_mem_nhds (show u < u + 1 from lt_add_one u)] with v hv
    exact (annClock_min_eq S hv.le ω).symm
  exact (continuous_id.min continuous_const).continuousAt.congr hev

/-- For a nondecreasing sequence, `u ∧ S_m → ℓ_u`. -/
theorem tendsto_min_annClock {S : ℕ → Ω → ℝ≥0} (hS : ∀ ω, Monotone fun m => S m ω) (u : ℝ≥0) (ω : Ω) :
    Tendsto (fun m => min u (S m ω)) atTop (𝓝 (annClock S u ω)) :=
  tendsto_atTop_ciSup (fun _ _ hmn => min_le_min le_rfl (hS ω hmn)) (bddAbove_min S u ω)

end Clock

/-! ### The supremum of an increasing sequence of filtrations -/

section ISup

variable {Ω : Type*} {mΩ : MeasurableSpace Ω}

/-- The filtration `u ↦ ⨆_m 𝒢^{(m)}_u`. -/
def iSupFiltration (𝒢 : ℕ → Filtration ℝ≥0 mΩ) : Filtration ℝ≥0 mΩ where
  seq u := ⨆ m, 𝒢 m u
  mono' _ _ huv := iSup_mono fun m => (𝒢 m).mono huv
  le' u := iSup_le fun m => (𝒢 m).le u

theorem iSupFiltration_apply (𝒢 : ℕ → Filtration ℝ≥0 mΩ) (u : ℝ≥0) : iSupFiltration 𝒢 u = ⨆ m, 𝒢 m u := rfl

theorem le_iSupFiltration (𝒢 : ℕ → Filtration ℝ≥0 mΩ) (m : ℕ) (u : ℝ≥0) : 𝒢 m u ≤ iSupFiltration 𝒢 u :=
  le_iSup (fun m => 𝒢 m u) m

end ISup

/-! ### The exponential martingale up to the lifetime -/

section ExpLimit

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}

/-- **The exponential martingale up to the lifetime.** Let `𝒢^{(m)}` be filtrations increasing in `m`, `S_m`
nondecreasing in `m` with `u ∧ S_m` measurable for `𝒢^{(m)}_u`, and `Bv` a process with every path continuous and
`Bv₀ = 0`, such that `e^{a Bv_{t∧S_m} − a² (t∧S_m)/2}` is a `𝒢^{(m)}`-martingale for every `m` and `a`. Then the noise
`Bv_{ℓ_u}`, with the clock `ℓ_u = ⨆_m (u ∧ S_m)`, has the exponential-martingale data `IsTCExpMartingale` for the
filtration `⋁_m 𝒢^{(m)}`. -/
theorem isTCExpMartingale_annClock [IsProbabilityMeasure P] {𝒢 : ℕ → Filtration ℝ≥0 mΩ}
    (h𝒢 : ∀ u, Monotone fun m => 𝒢 m u) {S : ℕ → Ω → ℝ≥0} (hSmono : ∀ ω, Monotone fun m => S m ω)
    (hSm : ∀ m u, Measurable[𝒢 m u] fun ω => min u (S m ω))
    {Bv : ℝ≥0 → Ω → ℝ} (hBvc : ∀ ω, Continuous fun t => Bv t ω) (hBv0 : ∀ ω, Bv 0 ω = 0)
    (hexp : ∀ m (a : ℝ), Martingale (fun t ω => Real.exp (a * Bv (min t (S m ω)) ω -
      a ^ 2 * ((min t (S m ω) : ℝ≥0) : ℝ) / 2)) (𝒢 m) P) :
    Sec6.Prop65.IsTCExpMartingale P (iSupFiltration 𝒢) (fun u ω => Bv (annClock S u ω) ω)
      (annClock S) := by
  -- the stopped exponentials and their limits
  set E : ℕ → ℝ → ℝ≥0 → Ω → ℝ := fun m b t ω => Real.exp (b * Bv (min t (S m ω)) ω -
    b ^ 2 * ((min t (S m ω) : ℝ≥0) : ℝ) / 2) with hE
  set F : ℝ → ℝ≥0 → Ω → ℝ := fun b t ω => Real.exp (b * Bv (annClock S t ω) ω -
    b ^ 2 * (annClock S t ω : ℝ) / 2) with hF
  have hBvlim : ∀ t ω, Tendsto (fun m => Bv (min t (S m ω)) ω) atTop (𝓝 (Bv (annClock S t ω) ω)) :=
    fun t ω => ((hBvc ω).tendsto _).comp (tendsto_min_annClock hSmono t ω)
  have hconv : ∀ b t ω, Tendsto (fun m => E m b t ω) atTop (𝓝 (F b t ω)) := by
    intro b t ω
    have h3 : Tendsto (fun m => ((min t (S m ω) : ℝ≥0) : ℝ)) atTop (𝓝 (annClock S t ω : ℝ)) :=
      (NNReal.continuous_coe.tendsto _).comp (tendsto_min_annClock hSmono t ω)
    exact (Real.continuous_exp.tendsto _).comp (((hBvlim t ω).const_mul b).sub
      ((h3.const_mul (b ^ 2)).div_const 2))
  have hEad : ∀ m b t, Measurable[𝒢 m t] (E m b t) := fun m b t =>
    ((hexp m b).stronglyAdapted t).measurable
  have hEm : ∀ m b t, Measurable (E m b t) := fun m b t => (hEad m b t).mono ((𝒢 m).le t) le_rfl
  have hFm : ∀ b t, Measurable (F b t) := fun b t =>
    measurable_of_tendsto_metrizable (fun m => hEm m b t) (tendsto_pi_nhds.2 (hconv b t))
  -- the noise at `u ∧ S_m` is `𝒢^{(m)}_u`-measurable
  have hXm : ∀ m u, Measurable[𝒢 m u] fun ω => Bv (min u (S m ω)) ω := by
    intro m u
    have hc : Measurable[𝒢 m u] fun ω => ((min u (S m ω) : ℝ≥0) : ℝ) :=
      measurable_coe_nnreal_real.comp (hSm m u)
    have e : (fun ω => Bv (min u (S m ω)) ω) =
        fun ω => Real.log (E m 1 u ω) + ((min u (S m ω) : ℝ≥0) : ℝ) / 2 := by
      funext ω
      simp only [hE, Real.log_exp]
      ring
    rw [e]
    exact (Real.measurable_log.comp (hEad m 1 u)).add (hc.div_const 2)
  -- total mass and the `L²` bound
  have hint : ∀ m b t, Integrable (E m b t) P := fun m b t => (hexp m b).integrable t
  have hone : ∀ m b t, ∫ ω, E m b t ω ∂P = 1 := by
    intro m b t
    have h0 := (hexp m b).setIntegral_eq (zero_le (a := t)) (@MeasurableSet.univ _ (𝒢 m 0))
    simp only [Measure.restrict_univ] at h0
    rw [← h0]
    simp [hBv0]
  have hsq : ∀ m b t ω, E m b t ω ^ 2 ≤ Real.exp (b ^ 2 * (t : ℝ)) * E m (2 * b) t ω := by
    intro m b t ω
    have hc : ((min t (S m ω) : ℝ≥0) : ℝ) ≤ t := by exact_mod_cast min_le_left t (S m ω)
    simp only [hE]
    rw [← Real.exp_nat_mul, ← Real.exp_add]
    refine Real.exp_le_exp.2 ?_
    generalize ((min t (S m ω) : ℝ≥0) : ℝ) = c at hc ⊢
    generalize Bv (min t (S m ω)) ω = X
    have hb : 0 ≤ b ^ 2 := sq_nonneg b
    push_cast
    nlinarith [mul_le_mul_of_nonneg_left hc hb]
  have hL2 : ∀ m b t, MemLp (E m b t) 2 P := by
    intro m b t
    refine (memLp_two_iff_integrable_sq (hEm m b t).aestronglyMeasurable).2 ?_
    refine ((hint m (2 * b) t).const_mul (Real.exp (b ^ 2 * (t : ℝ)))).mono'
      ((hEm m b t).pow_const 2).aestronglyMeasurable (ae_of_all _ fun ω => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    exact hsq m b t ω
  have hbound : ∀ m b t, ∫ ω, E m b t ω ^ 2 ∂P ≤ Real.exp (b ^ 2 * (t : ℝ)) := by
    intro m b t
    calc ∫ ω, E m b t ω ^ 2 ∂P ≤ ∫ ω, Real.exp (b ^ 2 * (t : ℝ)) * E m (2 * b) t ω ∂P :=
          integral_mono ((memLp_two_iff_integrable_sq (hEm m b t).aestronglyMeasurable).1 (hL2 m b t))
            ((hint m (2 * b) t).const_mul _) (hsq m b t)
      _ = Real.exp (b ^ 2 * (t : ℝ)) := by rw [integral_const_mul, hone, mul_one]
  have hFL1 : ∀ b t, MemLp (F b t) 1 P := fun b t =>
    (MathFin.memLp_two_of_subseq_ae_of_sq_bound (hL2 · b t) (hEm · b t) (hbound · b t)
      ⟨id, ae_of_all _ fun ω => hconv b t ω⟩).mono_exponent (by norm_num)
  have hlimset : ∀ b t (A : Set Ω), Tendsto (fun m => ∫ ω in A, E m b t ω ∂P) atTop
      (𝓝 (∫ ω in A, F b t ω ∂P)) := fun b t A =>
    MathFin.tendsto_setIntegral_of_subseq_ae_of_sq_bound (hL2 · b t) (hbound · b t) (hFL1 b t)
      (fun ns hns => ⟨id, ae_of_all _ fun ω => (hconv b t ω).comp hns⟩) A
  -- the identity on each `𝒢^{(m₀)}_s`
  have hFpos : ∀ b t ω, 0 ≤ F b t ω := fun b t ω => (Real.exp_pos _).le
  have hset : ∀ (b : ℝ) {s u : ℝ≥0}, s ≤ u → ∀ j (A : Set Ω), MeasurableSet[𝒢 j s] A →
      ∫⁻ ω in A, ENNReal.ofReal (F b u ω) ∂P = ∫⁻ ω in A, ENNReal.ofReal (F b s ω) ∂P := by
    intro b s u hsu j A hA
    have heq : ∫ ω in A, F b u ω ∂P = ∫ ω in A, F b s ω ∂P := by
      refine tendsto_nhds_unique (hlimset b u A) ((hlimset b s A).congr' ?_)
      filter_upwards [eventually_ge_atTop j] with m hm
      exact (hexp m b).setIntegral_eq hsu (h𝒢 s hm A hA)
    rw [← ofReal_integral_eq_lintegral_ofReal (memLp_one_iff_integrable.1 (hFL1 b u)).integrableOn
      (ae_of_all _ (hFpos b u)), ← ofReal_integral_eq_lintegral_ofReal
      (memLp_one_iff_integrable.1 (hFL1 b s)).integrableOn (ae_of_all _ (hFpos b s)), heq]
  refine ⟨fun u => ?_, fun u => ?_, annClock_le S, fun s u ω hsu => annClock_min_eq S hsu ω,
    fun ω => (hBvc ω).comp (continuous_annClock S ω), fun ω => by simp [annClock_zero, hBv0], ?_⟩
  · exact @measurable_of_tendsto_metrizable Ω ℝ (iSupFiltration 𝒢 u) _ _ _ _ _ _
      (fun m => (hXm m u).mono (le_iSupFiltration 𝒢 m u) le_rfl) (tendsto_pi_nhds.2 (hBvlim u))
  · exact Measurable.iSup fun m => (hSm m u).mono (le_iSupFiltration 𝒢 m u) le_rfl
  · intro b s u hsu W hW
    have htot : ∫⁻ ω, ENNReal.ofReal (F b s ω) ∂P ≠ ∞ := by
      rw [← ofReal_integral_eq_lintegral_ofReal (memLp_one_iff_integrable.1 (hFL1 b s))
        (ae_of_all _ (hFpos b s))]
      exact ENNReal.ofReal_ne_top
    have hall := Sec6.Prop65.setLIntegral_eq_of_iSup (P := P) (fun j k hjk => h𝒢 s hjk)
      (fun j => (𝒢 j).le s) htot (hset b hsu)
    exact Sec6.Prop65.lintegral_mul_eq_of_forall_setLIntegral_eq ((iSupFiltration 𝒢).le s)
      (ENNReal.measurable_ofReal.comp (hFm b u)) (ENNReal.measurable_ofReal.comp (hFm b s)) hall hW

end ExpLimit

end WholeField

end InteractingSLE
