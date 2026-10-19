import HigherDimLFPP.Field.Bands
import HigherDimLFPP.Field.RampPath
import HigherDimLFPP.Lower.Quantile

/-!
# Atomic measures and displacement couplings (lower comparison, source §5.1–§5.2)

Packet P-L3 (ruling H6; audit HA4, "Details for later use" D3(e), D4 (K3)–(K5), D5 step 6,
D6 Steps 1, 2, 4).  Deterministic measure theory used by Lemmas 5.2 and 5.3.

* `atomM A c p = Σ_{a ∈ A} c a δ_{p a}`: finitely supported measures (the Riemann measures
  `ν_j^N`, `ν₀^N`, the replaced measures `ν_{j,μ}` and their prefixes).  `bandVecM_atomM`: for a
  band `(a, b)` with `a > 0` the white-noise vector of `⟨H_{a,b}, Σ c δ_p⟩` is
  `Σ c • k_{a,b,p}` (P-F1's point vectors), so finite-model statistics are white-noise
  pairings of atomic measures.
* Coupling algebra for P-F2's `CoupledWithin`: monotonicity, sums, scalar multiples,
  push-forward by similarities (`coupledWithin_map_sim`, displacement times the ratio).
* `coupledWithin_dirac_segMeasure`, `coupledWithin_riemann_segMeasure`: a left Riemann
  measure of a segment is coupled with the segment's uniform measure within `|b - a|/N`
  (HA4 D5 step 6).
* `coupledWithin_quantile`: a finitely supported `μ` with `μ_x ∈ W(r)` and transverse parts
  `≤ m` is coupled with `ν₀ = 𝓛` (uniform measure on `[0,1] e₁`) within `r + m`
  (HA4 D3(e), the lift of P-L1's `exists_quantile_coupling`).

2D source: none (the 2D lower bound has no couplings).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set
open scoped RealInnerProductSpace ENNReal

namespace HigherDimLFPP.Lower

variable {d : ℕ}

/-! ## Atomic measures -/

section Atom

variable {α : Type*}

/-- The finitely supported measure `Σ_{a ∈ A} c a δ_{p a}`. -/
def atomM (A : Finset α) (c : α → ℝ) (p : α → Rd d) : Measure (Rd d) :=
  ∑ a ∈ A, ENNReal.ofReal (c a) • Measure.dirac (p a)

theorem atomM_apply (A : Finset α) (c : α → ℝ) (p : α → Rd d) (s : Set (Rd d)) :
    atomM A c p s = ∑ a ∈ A, ENNReal.ofReal (c a) * s.indicator 1 (p a) := by
  rw [atomM, Measure.finsetSum_apply]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Measure.smul_apply, Measure.dirac_apply, smul_eq_mul]

theorem atomM_univ (A : Finset α) (c : α → ℝ) (p : α → Rd d) :
    atomM A c p univ = ∑ a ∈ A, ENNReal.ofReal (c a) := by
  rw [atomM_apply]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [indicator_of_mem (mem_univ _), Pi.one_apply, mul_one]

instance isFiniteMeasure_atomM (A : Finset α) (c : α → ℝ) (p : α → Rd d) :
    IsFiniteMeasure (atomM A c p) :=
  ⟨by
    rw [atomM_univ]
    exact ENNReal.sum_lt_top.2 fun a _ => ENNReal.ofReal_lt_top⟩

theorem atomM_real_univ (A : Finset α) {c : α → ℝ} (hc : ∀ a ∈ A, 0 ≤ c a) (p : α → Rd d) :
    (atomM A c p).real univ = ∑ a ∈ A, c a := by
  rw [measureReal_def, atomM_univ, ENNReal.toReal_sum fun a _ => ENNReal.ofReal_ne_top]
  exact Finset.sum_congr rfl fun a ha => ENNReal.toReal_ofReal (hc a ha)

theorem isProbabilityMeasure_atomM (A : Finset α) {c : α → ℝ} (hc : ∀ a ∈ A, 0 ≤ c a)
    (hsum : ∑ a ∈ A, c a = 1) (p : α → Rd d) : IsProbabilityMeasure (atomM A c p) :=
  ⟨by
    rw [atomM_univ, ← ENNReal.ofReal_sum_of_nonneg hc, hsum, ENNReal.ofReal_one]⟩

instance isFiniteMeasure_ofReal_smul_dirac (c : ℝ) (z : Rd d) :
    IsFiniteMeasure (ENNReal.ofReal c • Measure.dirac z) :=
  Measure.smul_finite _ ENNReal.ofReal_ne_top

@[simp] theorem atomM_empty (c : α → ℝ) (p : α → Rd d) : atomM (∅ : Finset α) c p = 0 := by
  simp [atomM]

theorem atomM_insert [DecidableEq α] {A : Finset α} {x : α} (hx : x ∉ A) (c : α → ℝ)
    (p : α → Rd d) :
    atomM (insert x A) c p = ENNReal.ofReal (c x) • Measure.dirac (p x) + atomM A c p := by
  rw [atomM, Finset.sum_insert hx, ← atomM]

/-- Sub-families give smaller measures (nonnegative weights). -/
theorem atomM_mono_set {A B : Finset α} (hAB : A ⊆ B) (c : α → ℝ) (p : α → Rd d) :
    atomM A c p ≤ atomM B c p := by
  refine Measure.le_iff.2 fun s _ => ?_
  rw [atomM_apply, atomM_apply]
  exact Finset.sum_le_sum_of_subset_of_nonneg hAB fun _ _ _ => zero_le

/-- Push-forward of an atomic measure. -/
theorem map_atomM (A : Finset α) (c : α → ℝ) (p : α → Rd d) {f : Rd d → Rd d}
    (hf : Measurable f) : (atomM A c p).map f = atomM A c (fun a => f (p a)) := by
  rw [atomM, atomM]
  induction A using Finset.cons_induction with
  | empty => simp
  | cons x A hx ih =>
    rw [Finset.sum_cons, Finset.sum_cons, Measure.map_add _ _ hf, ih,
      Measure.map_smul _ hf.aemeasurable, Measure.map_dirac]

/-- Averages of atomic measures are atomic measures on the product index set. -/
theorem sum_smul_atomM {β : Type*} (B : Finset β) {a : ℝ} (ha : 0 ≤ a) (A : Finset α)
    (c : α → ℝ) (p : β → α → Rd d) :
    ∑ i ∈ B, ENNReal.ofReal a • atomM A c (p i) =
      atomM (B ×ˢ A) (fun x => a * c x.2) (fun x => p x.1 x.2) := by
  rw [atomM, Finset.sum_product]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [atomM, Finset.smul_sum]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [smul_smul, ENNReal.ofReal_mul ha]

end Atom

/-! ## Band vectors of atomic measures -/

section BandVec

variable {κ : Rd d → ℝ}

theorem bandVecM_add_zero (hκ : IsLFPPKernel κ) {S : Set ℝ} {μ₁ μ₂ : Measure (Rd d)}
    [IsFiniteMeasure μ₁] [IsFiniteMeasure μ₂] (h₁ : IsPairable κ S μ₁ 0)
    (h₂ : IsPairable κ S μ₂ 0) :
    bandVecM κ S (μ₁ + μ₂) 0 = bandVecM κ S μ₁ 0 + bandVecM κ S μ₂ 0 := by
  have h := bandVecM_add hκ h₁ h₂
  rwa [add_zero] at h

theorem bandVecM_smul_zero (S : Set ℝ) (μ : Measure (Rd d)) {c : ℝ≥0∞} (hc : c ≠ ⊤) :
    bandVecM κ S (c • μ) 0 = c.toReal • bandVecM κ S μ 0 := by
  have h := bandVecM_smul (κ := κ) S μ 0 hc
  rwa [smul_zero] at h

/-- Every finite measure is pairable with `0` on a band `(a, b)` with `a > 0`. -/
theorem isPairable_Ioo_zero (hκ : IsLFPPKernel κ) {a b : ℝ} (ha : 0 < a) (μ : Measure (Rd d))
    [IsFiniteMeasure μ] : IsPairable κ (Ioo a b) μ 0 :=
  isPairable_of_subset_Icc hκ measurableSet_Ioo ha Ioo_subset_Icc_self μ 0

/-- On a band `(a, b)` with `a > 0`, `⟨H_{a,b}, μ - ν⟩ = ⟨H_{a,b}, μ⟩ - ⟨H_{a,b}, ν⟩`. -/
theorem bandVecM_Ioo_sub (hκ : IsLFPPKernel κ) {a b : ℝ} (ha : 0 < a) (μ ν : Measure (Rd d))
    [IsFiniteMeasure μ] [IsFiniteMeasure ν] :
    bandVecM κ (Ioo a b) μ ν = bandVecM κ (Ioo a b) μ 0 - bandVecM κ (Ioo a b) ν 0 :=
  bandVecM_sub (isPairable_Ioo_zero hκ ha μ) (isPairable_Ioo_zero hκ ha ν)

/-- **Band vectors of atomic measures** (white-noise form of finite-model statistics): for a
band `(a, b)` with `a > 0` and nonnegative weights,
`bandVecM κ (a, b) (Σ c δ_p) 0 = Σ c • k_{a,b,p}`. -/
theorem bandVecM_atomM (hκ : IsLFPPKernel κ) {a b : ℝ} (ha : 0 < a) {α : Type*}
    (A : Finset α) {c : α → ℝ} (hc : ∀ x ∈ A, 0 ≤ c x) (p : α → Rd d) :
    bandVecM κ (Ioo a b) (atomM A c p) 0 = ∑ x ∈ A, c x • bandVec κ a b (p x) := by
  classical
  induction A using Finset.induction_on with
  | empty => simp [bandVecM_self]
  | insert x A hx ih =>
    rw [atomM_insert hx, bandVecM_add_zero hκ (isPairable_Ioo_zero hκ ha _)
      (isPairable_Ioo_zero hκ ha _), ih fun y hy => hc y (Finset.mem_insert_of_mem hy),
      Finset.sum_insert hx, bandVecM_smul_zero _ _ ENNReal.ofReal_ne_top, bandVecM_dirac_zero,
      ENNReal.toReal_ofReal (hc x (Finset.mem_insert_self x A))]

end BandVec

/-! ## Coupling algebra -/

section Coupling

theorem map_finsetSum {α β ι : Type*} [MeasurableSpace α] [MeasurableSpace β] {f : α → β}
    (hf : Measurable f) (s : Finset ι) (μ : ι → Measure α) :
    (∑ i ∈ s, μ i).map f = ∑ i ∈ s, (μ i).map f := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert x s hx ih => rw [Finset.sum_insert hx, Measure.map_add _ _ hf, ih, Finset.sum_insert hx]

theorem ae_finsetSum {α ι : Type*} [MeasurableSpace α] (s : Finset ι) (μ : ι → Measure α)
    {p : α → Prop} (h : ∀ i ∈ s, ∀ᵐ x ∂μ i, p x) : ∀ᵐ x ∂(∑ i ∈ s, μ i), p x := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert x s hx ih =>
    rw [Finset.sum_insert hx, ae_add_measure_iff]
    exact ⟨h x (Finset.mem_insert_self x s), ih fun i hi => h i (Finset.mem_insert_of_mem hi)⟩

theorem coupledWithin_mono {μ ν : Measure (Rd d)} {u u' : ℝ} (h : CoupledWithin μ ν u)
    (hu : u ≤ u') : CoupledWithin μ ν u' := by
  obtain ⟨cpl, h1, h2, h3⟩ := h
  exact ⟨cpl, h1, h2, h3.mono fun q hq => hq.trans hu⟩

theorem coupledWithin_zero (u : ℝ) : CoupledWithin (0 : Measure (Rd d)) 0 u :=
  ⟨0, Measure.map_zero _, Measure.map_zero _, by simp⟩

theorem coupledWithin_add {μ₁ ν₁ μ₂ ν₂ : Measure (Rd d)} {u : ℝ} (h₁ : CoupledWithin μ₁ ν₁ u)
    (h₂ : CoupledWithin μ₂ ν₂ u) : CoupledWithin (μ₁ + μ₂) (ν₁ + ν₂) u := by
  obtain ⟨c₁, a₁, b₁, e₁⟩ := h₁
  obtain ⟨c₂, a₂, b₂, e₂⟩ := h₂
  refine ⟨c₁ + c₂, ?_, ?_, ae_add_measure_iff.2 ⟨e₁, e₂⟩⟩
  · rw [Measure.map_add _ _ measurable_fst, a₁, a₂]
  · rw [Measure.map_add _ _ measurable_snd, b₁, b₂]

theorem coupledWithin_smul (c : ℝ≥0∞) {μ ν : Measure (Rd d)} {u : ℝ} (h : CoupledWithin μ ν u) :
    CoupledWithin (c • μ) (c • ν) u := by
  obtain ⟨cpl, h1, h2, h3⟩ := h
  refine ⟨c • cpl, ?_, ?_, Measure.ae_smul_measure h3 c⟩
  · rw [Measure.map_smul _ measurable_fst.aemeasurable, h1]
  · rw [Measure.map_smul _ measurable_snd.aemeasurable, h2]

theorem coupledWithin_finsetSum {α : Type*} (A : Finset α) (μ ν : α → Measure (Rd d)) {u : ℝ}
    (h : ∀ a ∈ A, CoupledWithin (μ a) (ν a) u) :
    CoupledWithin (∑ a ∈ A, μ a) (∑ a ∈ A, ν a) u := by
  classical
  induction A using Finset.induction_on with
  | empty => simpa using coupledWithin_zero u
  | insert x A hx ih =>
    rw [Finset.sum_insert hx, Finset.sum_insert hx]
    exact coupledWithin_add (h x (Finset.mem_insert_self x A))
      (ih fun a ha => h a (Finset.mem_insert_of_mem ha))

/-- **Push-forward by a similarity** multiplies the displacement by the ratio. -/
theorem coupledWithin_map_sim (S : SimD d) {μ ν : Measure (Rd d)} {u : ℝ}
    (h : CoupledWithin μ ν u) : CoupledWithin (μ.map S.app) (ν.map S.app) (|S.r| * u) := by
  obtain ⟨cpl, h1, h2, h3⟩ := h
  have hS : Measurable S.app := S.continuous_app.measurable
  have hp : Measurable (Prod.map S.app S.app) := hS.prodMap hS
  refine ⟨cpl.map (Prod.map S.app S.app), ?_, ?_, ?_⟩
  · rw [Measure.map_map measurable_fst hp, ← h1, Measure.map_map hS measurable_fst]
    rfl
  · rw [Measure.map_map measurable_snd hp, ← h2, Measure.map_map hS measurable_snd]
    rfl
  · rw [ae_map_iff hp.aemeasurable (measurableSet_le (by fun_prop) measurable_const)]
    filter_upwards [h3] with q hq
    simp only [Prod.map_fst, Prod.map_snd]
    rw [SimD.norm_app_sub]
    exact mul_le_mul_of_nonneg_left hq (abs_nonneg _)

/-- A Dirac mass is coupled with the uniform measure on a segment within the larger distance to
the endpoints. -/
theorem coupledWithin_dirac_segMeasure (p a b : Rd d) {u : ℝ} (ha : ‖p - a‖ ≤ u)
    (hb : ‖p - b‖ ≤ u) : CoupledWithin (Measure.dirac p) (Upper.segMeasure a b) u := by
  have hd : Measure.dirac p = (volume.restrict (Icc (0 : ℝ) 1)).map (fun _ => p) := by
    rw [Measure.map_const, Measure.restrict_apply_univ, Real.volume_Icc, sub_zero,
      ENNReal.ofReal_one, one_smul]
  rw [hd, Upper.segMeasure_eq]
  refine coupledWithin_map measurable_const (Upper.measurable_lin a b) fun s hs => ?_
  have e : p - Upper.lin a b s = (1 - s) • (p - a) + s • (p - b) := by
    simp only [Upper.lin]
    module
  have h1 : 0 ≤ 1 - s := by linarith [hs.2]
  rw [e]
  calc ‖(1 - s) • (p - a) + s • (p - b)‖ ≤ ‖(1 - s) • (p - a)‖ + ‖s • (p - b)‖ :=
        norm_add_le _ _
    _ = (1 - s) * ‖p - a‖ + s * ‖p - b‖ := by
        rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg h1,
          abs_of_nonneg hs.1]
    _ ≤ (1 - s) * u + s * u :=
        add_le_add (mul_le_mul_of_nonneg_left ha h1) (mul_le_mul_of_nonneg_left hb hs.1)
    _ = u := by ring

/-- **Left Riemann measure of a segment** (HA4 D5, step 6): `N⁻¹ Σ_{l<N} δ_{a + (l/N)(b - a)}`
is coupled with the uniform measure on `[a, b]` within `|b - a| / N`. -/
theorem coupledWithin_riemann_segMeasure (a b : Rd d) {N : ℕ} (hN : 0 < N) :
    CoupledWithin (atomM (Finset.range N) (fun _ => 1 / (N : ℝ))
        (fun l => Upper.lin a b ((l : ℝ) / N)))
      (Upper.segMeasure a b) (‖b - a‖ / N) := by
  have hN' : (0 : ℝ) < N := by exact_mod_cast hN
  set τ : ℕ → ℝ := fun l => (l : ℝ) / N with hτ
  have hmono : ∀ l < N, τ l ≤ τ (l + 1) := fun l _ => by
    simp only [hτ]
    push_cast
    exact div_le_div_of_nonneg_right (by linarith) hN'.le
  have h0 : τ 0 = 0 := by simp [hτ]
  have h1 : τ N = 1 := by simp [hτ, div_self hN'.ne']
  rw [Upper.segMeasure_split a b τ hmono h0 h1, Upper.segSum, atomM]
  refine coupledWithin_finsetSum _ _ _ fun l _ => ?_
  have hw : τ (l + 1) - τ l = 1 / (N : ℝ) := by
    simp only [hτ]
    push_cast
    field_simp
    ring
  rw [hw]
  refine coupledWithin_smul _ (coupledWithin_dirac_segMeasure _ _ _ ?_ ?_)
  · rw [sub_self, norm_zero]
    positivity
  · have e : Upper.lin a b (τ l) - Upper.lin a b (τ (l + 1)) = (τ l - τ (l + 1)) • (b - a) := by
      simp only [Upper.lin]
      module
    rw [e, norm_smul, Real.norm_eq_abs, abs_sub_comm, hw, abs_of_pos (by positivity)]
    exact le_of_eq (by ring)

/-- `ν₀ = 𝓛`: the uniform measure on `[0, 1] e₁` as a push-forward. -/
theorem lin_zero_e₁ (s : ℝ) : Upper.lin (0 : Rd d) (e₁ d) s = s • e₁ d := by
  simp only [Upper.lin, zero_add, sub_zero]

/-- **The quantile coupling, lifted** (HA4 D3(e)): a finitely supported probability measure
`μ = Σ w δ_z` with `μ_x ∈ W(r)` whose atoms have transverse parts `≤ m` is coupled with the
uniform measure on `[0,1] e₁` within `r + m`. -/
theorem coupledWithin_quantile (hd : 0 < d) {S : Finset (Rd d)} {w : Rd d → ℝ}
    (hμ : IsFinProb S w) {r m : ℝ} (hW : HorizW S w r)
    (htr : ∀ z ∈ S, w z ≠ 0 → ‖transv z‖ ≤ m) :
    CoupledWithin (atomM S w id) (Upper.segMeasure 0 (e₁ d)) (r + m) := by
  obtain ⟨cl, hcl, hdisj, hclose, -⟩ := exists_quantile_coupling hμ hW
  set I : Rd d → Set ℝ := fun z => Ioc (cl z) (cl z + w z) with hI
  have hImeas : ∀ z, MeasurableSet (I z) := fun z => measurableSet_Ioc
  -- the pieces tile `(0, 1]` up to a null set
  have hsub : (⋃ z ∈ S, I z) ⊆ Ioc (0 : ℝ) 1 := by
    intro t ht
    simp only [mem_iUnion] at ht
    obtain ⟨z, hz, htz⟩ := ht
    exact ⟨lt_of_le_of_lt (hcl z hz).1 htz.1, htz.2.trans (hcl z hz).2⟩
  have hvolI : ∀ z ∈ S, volume (I z) = ENNReal.ofReal (w z) := fun z _ => by
    rw [hI, Real.volume_Ioc, add_sub_cancel_left]
  have hvolU : volume (⋃ z ∈ S, I z) = 1 := by
    rw [measure_biUnion_finset (fun z _ z' _ hzz' => hdisj (Finset.mem_coe.2 ‹_›)
      (Finset.mem_coe.2 ‹_›) hzz') fun z _ => hImeas z]
    rw [Finset.sum_congr rfl hvolI, ← ENNReal.ofReal_sum_of_nonneg hμ.1, hμ.2,
      ENNReal.ofReal_one]
  have hae : (⋃ z ∈ S, I z) =ᵐ[volume] Ioc (0 : ℝ) 1 := by
    refine (ae_eq_of_subset_of_measure_ge hsub ?_ ?_ ?_)
    · rw [hvolU, Real.volume_Ioc, sub_zero, ENNReal.ofReal_one]
    · exact (Finset.measurableSet_biUnion _ fun z _ => hImeas z).nullMeasurableSet
    · rw [Real.volume_Ioc]; exact ENNReal.ofReal_ne_top
  have hrestr : ∑ z ∈ S, volume.restrict (I z) = volume.restrict (Icc (0 : ℝ) 1) := by
    rw [← Measure.restrict_congr_set Ioc_ae_eq_Icc, ← Measure.restrict_congr_set hae,
      Measure.restrict_biUnion_finset (fun z hz z' hz' hzz' => hdisj hz hz' hzz') hImeas]
    exact (Measure.sum_coe_finset S fun z => volume.restrict (I z)).symm
  -- the coupling
  have hp : ∀ z : Rd d, Measurable fun t : ℝ => (z, t • e₁ d) := fun z => by fun_prop
  have hse : Measurable fun t : ℝ => t • e₁ d := by fun_prop
  refine ⟨∑ z ∈ S, (volume.restrict (I z)).map fun t => (z, t • e₁ d), ?_, ?_, ?_⟩
  · rw [map_finsetSum measurable_fst, atomM]
    refine Finset.sum_congr rfl fun z hz => ?_
    rw [Measure.map_map measurable_fst (hp z)]
    have e : (Prod.fst ∘ fun t : ℝ => (z, t • e₁ d)) = fun _ => z := rfl
    rw [e, Measure.map_const, Measure.restrict_apply_univ, hvolI z hz]
    rfl
  · rw [map_finsetSum measurable_snd]
    have e : ∀ z ∈ S, ((volume.restrict (I z)).map fun t => (z, t • e₁ d)).map Prod.snd =
        (volume.restrict (I z)).map fun t => t • e₁ d := fun z _ => by
      rw [Measure.map_map measurable_snd (hp z)]
      rfl
    rw [Finset.sum_congr rfl e, ← map_finsetSum hse, hrestr, Upper.segMeasure_eq]
    congr 1
    funext t
    rw [lin_zero_e₁]
  · refine ae_finsetSum _ _ fun z hz => ?_
    rw [ae_map_iff (hp z).aemeasurable (measurableSet_le (by fun_prop) measurable_const)]
    by_cases hw : w z = 0
    · have hI0 : I z = ∅ := by rw [hI]; simp [hw]
      rw [hI0, Measure.restrict_empty]
      simp
    · filter_upwards [ae_restrict_mem (hImeas z)] with t ht
      exact norm_sub_smul_e₁_le hd (hclose z hz t ht) (htr z hz hw)

end Coupling

end HigherDimLFPP.Lower
