import QuantumZipper.Proofs.Section5.Prop16MeasReduce

/-!
# Proposition 1.6, node D4-MEAS (part 3): measurability of local area pairings on random domains

For a measurable family of samples `x p` and random open domains `U p` exhausted by a measurable
family of continuous cut-offs `φ n p` (`IsBumpFamily`), on the event `goodSet` that the local
area measure `qAreaMeasureOn γ (x p) (U p)` is a genuine vague limit:

* `integral_qAreaMeasureOn_eq_Phi`: `∫ f d(qAreaMeasureOn γ (x p) (U p))` is an explicit countable
  limit of the measurable pre-limit integrals `∫ f φ_n d(areaApprox γ (x p) k)` (including the
  Bochner junk value `0` when `f` is not integrable, detected by `∫⁻ |f| < ∞`);
* `aemeasurable_integral_qAreaMeasureOn`: hence the pairing is a.e.-measurable in `p` as soon as
  `goodSet` is null-measurable (off `goodSet` the measure is the junk `0`).

Own elementary proof (monotone and dominated convergence; AGENT_GUIDE cost rule), following the
approach of `LQGMeas.measurable_qAreaMeasure_open` (`Proofs/LQG/Measurability.lean`).
-/

noncomputable section

open MeasureTheory Filter Set
open scoped Topology ENNReal

namespace QuantumZipper

namespace Prop16Area

namespace Meas

open LQGMeas

variable {α : Type*} [MeasurableSpace α]

/-- A measurable family of continuous cut-offs `0 ≤ φ n p ≤ 1`, supported in `U p`, increasing in
`n` and eventually `1` at every point of `U p`. -/
structure IsBumpFamily (U : α → Set ℂ) (φ : ℕ → α → ℂ → ℝ) : Prop where
  meas : ∀ n, Measurable fun q : α × ℂ => φ n q.1 q.2
  cont : ∀ n p, Continuous (φ n p)
  nonneg : ∀ n p z, 0 ≤ φ n p z
  le_one : ∀ n p z, φ n p z ≤ 1
  tsupp : ∀ n p, tsupport (φ n p) ⊆ U p
  mono : ∀ p z, Monotone fun n => φ n p z
  reach : ∀ p z, z ∈ U p → ∃ n, φ n p z = 1

/-- The event that the local area measure is a genuine vague limit. -/
def goodSet (γ : ℝ) (x : α → FieldSample) (U : α → Set ℂ) : Set α :=
  {p | ∃ m, IsVagueLimitOn (U p) (areaApprox γ (x p)) m}

theorem isVagueLimitOn_qAreaMeasureOn {γ : ℝ} {y : FieldSample} {V : Set ℂ}
    (hg : ∃ m, IsVagueLimitOn V (areaApprox γ y) m) :
    IsVagueLimitOn V (areaApprox γ y) (qAreaMeasureOn γ y V) := by
  unfold qAreaMeasureOn; rw [dif_pos hg]; exact hg.choose_spec

theorem qAreaMeasureOn_of_not {γ : ℝ} {y : FieldSample} {V : Set ℂ}
    (hg : ¬ ∃ m, IsVagueLimitOn V (areaApprox γ y) m) : qAreaMeasureOn γ y V = 0 := by
  unfold qAreaMeasureOn; rw [dif_neg hg]

/-- Pre-limit integrals with a parameter-dependent integrand are measurable. -/
theorem measurable_integral_areaApprox_param (γ : ℝ) (k : ℕ) {x : α → FieldSample}
    (hx : Measurable x) {g : α → ℂ → ℝ} (hg : Measurable fun q : α × ℂ => g q.1 q.2) :
    Measurable fun p => ∫ z, g p z ∂areaApprox γ (x p) k := by
  let Dn : α × ℂ → ℝ := fun q => radius k ^ (γ ^ 2 / 2) * Real.exp (γ * avgReg (x q.1) k q.2)
  have hA : Measurable fun q : α × ℂ => avgReg (x q.1) k q.2 :=
    Measurable.comp (g := fun r : FieldSample × ℂ => avgReg r.1 k r.2)
      (f := fun q : α × ℂ => (x q.1, q.2)) (measurable_avgReg k)
      ((hx.comp measurable_fst).prodMk measurable_snd)
  have hDm : Measurable Dn := (Real.measurable_exp.comp (hA.const_mul γ)).const_mul _
  have hD0 : ∀ q, 0 ≤ Dn q := fun q =>
    mul_nonneg (Real.rpow_nonneg (radius_pos k).le _) (Real.exp_pos _).le
  have heq : ∀ p, ∫ z, g p z ∂areaApprox γ (x p) k =
      ∫ z, Dn (p, z) * g p z ∂(volume.restrict H) := fun p =>
    GoodSample.integral_withDensity_ofReal (μ := volume.restrict H)
      (hDm.comp (measurable_const.prodMk measurable_id)) (fun z => hD0 _) (g p)
  simp_rw [heq]
  exact (StronglyMeasurable.integral_prod_right' (ν := volume.restrict H)
    (f := fun q : α × ℂ => Dn q * g q.1 q.2) (hDm.mul hg).stronglyMeasurable).measurable

/-- The limit of the pre-limit integrals (junk `0` if it does not exist). -/
def Psi (γ : ℝ) (x : α → FieldSample) (g : α → ℂ → ℝ) (p : α) : ℝ :=
  limUnder atTop fun k => ∫ z, g p z ∂areaApprox γ (x p) k

theorem measurable_Psi (γ : ℝ) {x : α → FieldSample} (hx : Measurable x) {g : α → ℂ → ℝ}
    (hg : Measurable fun q : α × ℂ => g q.1 q.2) : Measurable (Psi γ x g) :=
  (StronglyMeasurable.limUnder fun k =>
    (measurable_integral_areaApprox_param γ k hx hg).stronglyMeasurable).measurable

variable {γ : ℝ} {x : α → FieldSample} {U : α → Set ℂ} {φ : ℕ → α → ℂ → ℝ}

omit [MeasurableSpace α] in
theorem integral_eq_Psi {p : α} (hp : p ∈ goodSet γ x U) {g : α → ℂ → ℝ}
    (hc : Continuous (g p)) (hcs : HasCompactSupport (g p)) (hV : tsupport (g p) ⊆ U p) :
    ∫ z, g p z ∂qAreaMeasureOn γ (x p) (U p) = Psi γ x g p :=
  (((isVagueLimitOn_qAreaMeasureOn hp).2.2 _ hc hcs hV).limUnder_eq).symm

theorem bump_eventually_one (hφ : IsBumpFamily U φ) {p : α} {z : ℂ} (hz : z ∈ U p) :
    ∀ᶠ n in atTop, φ n p z = 1 := by
  obtain ⟨n, hn⟩ := hφ.reach p z hz
  filter_upwards [eventually_ge_atTop n] with m hm
  exact le_antisymm (hφ.le_one m p z) (hn ▸ hφ.mono p z hm)

theorem bump_eq_zero (hφ : IsBumpFamily U φ) {n : ℕ} {p : α} {z : ℂ} (hz : z ∉ U p) :
    φ n p z = 0 := by
  by_contra h
  exact hz (hφ.tsupp n p (subset_tsupport _ h))

/-- `∫⁻ |f|` against a vague limit on `U p`, as a supremum of cut-off integrals. -/
theorem lintegral_eq_iSup (hφ : IsBumpFamily U φ) {p : α} {m : Measure ℂ}
    (hm : IsVagueLimitOn (U p) (areaApprox γ (x p)) m) {g : ℂ → ℝ} (hg : Continuous g)
    (hgc : HasCompactSupport g) (hg0 : ∀ z, 0 ≤ g z) :
    ∫⁻ z, ENNReal.ofReal (g z) ∂m = ⨆ n, ENNReal.ofReal (∫ z, g z * φ n p z ∂m) := by
  have hint : ∀ n, Integrable (fun z => g z * φ n p z) m := fun n =>
    GoodSample.integrable_of_tsupport hm.2.1 (hg.mul (hφ.cont n p)) (hgc.mul_right)
      ((tsupport_mul_subset_right).trans (hφ.tsupp n p))
  have e1 : ∀ n, ENNReal.ofReal (∫ z, g z * φ n p z ∂m) =
      ∫⁻ z, ENNReal.ofReal (g z * φ n p z) ∂m := fun n =>
    ofReal_integral_eq_lintegral_ofReal (hint n)
      (ae_of_all _ fun z => mul_nonneg (hg0 z) (hφ.nonneg n p z))
  simp_rw [e1]
  rw [← lintegral_iSup (f := fun n z => ENNReal.ofReal (g z * φ n p z)) (fun n => ENNReal.measurable_ofReal.comp
      (hg.mul (hφ.cont n p)).measurable)
    (fun a b hab z => ENNReal.ofReal_le_ofReal
      (mul_le_mul_of_nonneg_left (hφ.mono p z hab) (hg0 z)))]
  have hae : ∀ᵐ z ∂m, z ∈ U p := ae_iff.2 hm.1
  refine lintegral_congr_ae ?_
  filter_upwards [hae] with z hz
  refine le_antisymm ?_ (iSup_le fun n => ENNReal.ofReal_le_ofReal
    (mul_le_of_le_one_right (hg0 z) (hφ.le_one n p z)))
  obtain ⟨n, hn⟩ := (bump_eventually_one hφ hz).exists
  exact le_iSup_of_le n (by rw [hn, mul_one])

/-- The explicit measurable formula for the pairing on good samples. -/
def Phi (γ : ℝ) (x : α → FieldSample) (φ : ℕ → α → ℂ → ℝ) (f : ℂ → ℝ) (p : α) : ℝ :=
  if (⨆ n, ENNReal.ofReal (Psi γ x (fun p z => |f z| * φ n p z) p)) < ⊤ then
    limUnder atTop (fun n => Psi γ x (fun p z => f z * φ n p z) p)
  else 0

theorem measurable_Phi (hx : Measurable x) (hφ : IsBumpFamily U φ) {f : ℂ → ℝ}
    (hf : Continuous f) : Measurable (Phi γ x φ f) := by
  have h1 : ∀ n, Measurable (Psi γ x (fun p z => |f z| * φ n p z)) := fun n =>
    measurable_Psi γ hx ((hf.abs.measurable.comp measurable_snd).mul (hφ.meas n))
  have h2 : ∀ n, Measurable (Psi γ x (fun p z => f z * φ n p z)) := fun n =>
    measurable_Psi γ hx ((hf.measurable.comp measurable_snd).mul (hφ.meas n))
  refine Measurable.ite (measurableSet_lt (Measurable.iSup fun n =>
    ENNReal.measurable_ofReal.comp (h1 n)) measurable_const) ?_ measurable_const
  exact (StronglyMeasurable.limUnder fun n => (h2 n).stronglyMeasurable).measurable

theorem integral_qAreaMeasureOn_eq_Phi (hφ : IsBumpFamily U φ) {p : α}
    (hp : p ∈ goodSet γ x U) {f : ℂ → ℝ} (hf : Continuous f) (hfc : HasCompactSupport f) :
    ∫ z, f z ∂qAreaMeasureOn γ (x p) (U p) = Phi γ x φ f p := by
  set m := qAreaMeasureOn γ (x p) (U p) with hmdef
  have hm : IsVagueLimitOn (U p) (areaApprox γ (x p)) m := isVagueLimitOn_qAreaMeasureOn hp
  have hsupp : ∀ (g : ℂ → ℝ) n, tsupport (fun z => g z * φ n p z) ⊆ U p := fun g n =>
    (tsupport_mul_subset_right).trans (hφ.tsupp n p)
  have eA : ∀ n, Psi γ x (fun p z => |f z| * φ n p z) p = ∫ z, |f z| * φ n p z ∂m := fun n =>
    (integral_eq_Psi (g := fun p z => |f z| * φ n p z) hp (hf.abs.mul (hφ.cont n p))
      (hfc.abs.mul_right) (hsupp _ n)).symm
  have eB : ∀ n, Psi γ x (fun p z => f z * φ n p z) p = ∫ z, f z * φ n p z ∂m := fun n =>
    (integral_eq_Psi (g := fun p z => f z * φ n p z) hp (hf.mul (hφ.cont n p))
      (hfc.mul_right) (hsupp _ n)).symm
  have hL := lintegral_eq_iSup hφ hm hf.abs hfc.abs (fun z => abs_nonneg _)
  have hint : Integrable f m ↔ (⨆ n, ENNReal.ofReal (∫ z, |f z| * φ n p z ∂m)) < ⊤ := by
    rw [← hL]
    constructor
    · intro h
      have := h.2
      rw [HasFiniteIntegral] at this
      simpa only [Real.enorm_eq_ofReal_abs] using this
    · intro h
      refine ⟨hf.aestronglyMeasurable, ?_⟩
      rw [HasFiniteIntegral]
      simpa only [Real.enorm_eq_ofReal_abs] using h
  unfold Phi
  simp_rw [eA, eB]
  by_cases hi : Integrable f m
  · rw [if_pos (hint.1 hi)]
    refine (Tendsto.limUnder_eq ?_).symm
    refine tendsto_integral_of_dominated_convergence (fun z => ‖f z‖)
      (fun n => (hf.mul (hφ.cont n p)).aestronglyMeasurable) hi.norm (fun n => ae_of_all _
        fun z => ?_) ?_
    · rw [norm_mul, Real.norm_eq_abs (φ n p z), abs_of_nonneg (hφ.nonneg n p z)]
      exact mul_le_of_le_one_right (norm_nonneg _) (hφ.le_one n p z)
    · filter_upwards [(ae_iff.2 hm.1 : ∀ᵐ z ∂m, z ∈ U p)] with z hz
      refine tendsto_const_nhds.congr' ?_
      filter_upwards [bump_eventually_one hφ hz] with n hn
      rw [hn, mul_one]
  · rw [if_neg (fun h => hi (hint.2 h)), integral_undef hi]

/-- **`hmeas`, generic form.** -/
theorem aemeasurable_integral_qAreaMeasureOn {μ : Measure α} (hx : Measurable x)
    (hφ : IsBumpFamily U φ) (hG : NullMeasurableSet (goodSet γ x U) μ) {f : ℂ → ℝ}
    (hf : Continuous f) (hfc : HasCompactSupport f) :
    AEMeasurable (fun p => ∫ z, f z ∂qAreaMeasureOn γ (x p) (U p)) μ := by
  have e : (fun p => ∫ z, f z ∂qAreaMeasureOn γ (x p) (U p)) =
      (goodSet γ x U).indicator (Phi γ x φ f) := by
    funext p
    by_cases hp : p ∈ goodSet γ x U
    · rw [indicator_of_mem hp]; exact integral_qAreaMeasureOn_eq_Phi hφ hp hf hfc
    · rw [indicator_of_notMem hp, qAreaMeasureOn_of_not hp, integral_zero_measure]
  rw [e]
  exact (measurable_Phi hx hφ hf).aemeasurable.indicator₀ hG

end Meas

end Prop16Area

end QuantumZipper
