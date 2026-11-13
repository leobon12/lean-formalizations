import QuantumZipper.Proofs.RS.TraceGen
import QuantumZipper.Proofs.RS.KoebeLoewnerTime
import QuantumZipper.Proofs.RS.HullBasics
import QuantumZipper.Proofs.RS.TraceShift

/-!
# SLE₈ note, §5: from a uniform radial bound to the trace (deterministic bridge)

Source: `source/sle8-continuity.pdf`, §5, proof of Theorem 1.1 (anchor `thm-1.1-proof`, PDF pp. 11–12),
transcription `source/sle8/sle8-continuity.md`.

For a continuous driver `W` with `W 0 = 0`, let `F_t = fwdMapInv W t` be the centered inverse Loewner
map. The proof of Theorem 1.1 in the note runs as follows (equation (5.6) and the paragraph after it):

* if `sup_{t ≤ T} |F_t(iy) − F_t(iy')|` is bounded by a quantity `ε(y)` tending to `0` as `y ↓ 0`
  (for instance `ε(y) = sup_{t ≤ T} ∫_0^y |F_t'(iv)| dv`, (5.6)), then `F_t(iy)` converges uniformly
  on `[0, T]`;
* `t ↦ F_t(iy)` is continuous for fixed `y > 0`, so the limit `γ` is continuous, and `γ(0) = 0`;
* the deterministic trace criterion [RS05, Theorem 4.1] gives that `H_t = ℍ \ K_t` is the unbounded
  connected component of `ℍ \ γ([0, t])`.

This file proves that deduction for an arbitrary rate `ε` (the note's rate is logarithmic, (5.1)),
generalizing QuantumZipper's power-rate bridge `RS.tendstoUniformlyOn_fwdMapInv_mul_I_of_bound`. The
trace criterion is QuantumZipper's `RS.exists_compl_fwdHull_eq_connectedComponentIn_mul_I`
(uniform-convergence form of [RS05, Theorem 4.1]).

## Main results

* `InteractingSLE.SLE8.exists_continuous_trace_of_norm_sub_le`: a uniform Cauchy bound on every
  `[0, T]` gives the conclusion of the frozen Theorem 1.1 (`ae_exists_continuous_trace`) for `W`.
* `InteractingSLE.SLE8.exists_continuous_trace_of_lintegral_le`: the same from a uniform bound on the
  improper integrals `∫_0^y |F_t'(iv)| dv` (the form of Proposition 5.1).
* `InteractingSLE.SLE8.lintegral_deriv_fwdMapInv_scale`: Brownian-scaling bookkeeping for these
  integrals (used to pass from `[0, 1]` to `[0, j]`).
-/

noncomputable section

open MeasureTheory Filter Set Metric Complex
open scoped NNReal ENNReal Topology

namespace InteractingSLE.SLE8

open QuantumZipper

variable {W : ℝ → ℝ}

/-! ## Elementary facts on `fwdMapInv` -/

/-- At time `0` the centered inverse map is the identity on `ℍ` (for `W 0 = 0`). -/
theorem fwdMapInv_zero_eq_self (hW : Continuous W) (hW0 : W 0 = 0) {w : ℂ} (hw : 0 < w.im) :
    fwdMapInv W 0 w = w := by
  have hfwd : ∀ z : ℂ, z ≠ 0 → fwdMap W 0 z = z := by
    intro z hz
    have hex : ∃ u, IsForwardSol W z 0 u := by
      refine ⟨fun _ => z, continuousOn_const, fun t ht => ?_⟩
      have ht0 : t = 0 := le_antisymm ht.2 ht.1
      subst ht0
      exact ⟨hz, by simp [hW0]⟩
    unfold fwdMap
    rw [dite_eq_left hex]
    have := (hex.choose_spec.2 0 ⟨le_rfl, le_rfl⟩).2
    simpa [hW0] using this
  have hne : ∀ z : ℂ, 0 < z.im → z ≠ 0 := fun z hz h => by
    rw [h, Complex.zero_im] at hz
    exact lt_irrefl _ hz
  have hP : ∀ z' : ℂ, (z' ∈ H \ fwdHull W 0 ∧ fwdMap W 0 z' = w) ↔ z' = w := by
    intro z'
    rw [RS.fwdHull_zero_eq_empty hW, sdiff_empty]
    constructor
    · rintro ⟨hz, he⟩
      rw [hfwd z' (hne z' hz)] at he
      exact he
    · rintro rfl
      exact ⟨hw, hfwd z' (hne z' hw)⟩
  have hex : ∃! z', z' ∈ H \ fwdHull W 0 ∧ fwdMap W 0 z' = w :=
    ⟨w, (hP _).2 rfl, fun y hy => (hP y).1 hy⟩
  unfold fwdMapInv
  rw [dite_eq_left hex]
  exact (hP _).1 hex.choose_spec.1

/-- `y i ∈ ℍ` for `y > 0`. -/
theorem ofReal_mul_I_mem_H {y : ℝ} (hy : 0 < y) : (y : ℂ) * I ∈ H := by
  show 0 < ((y : ℂ) * I).im
  simpa using hy

/-- Fundamental theorem of calculus along a vertical segment (the first inequality of (5.6)):
`|F_t(iy₁) − F_t(iy₂)| ≤ ∫_{y₂}^{y₁} |F_t'(iv)| dv` for `0 < y₂ ≤ y₁`. -/
theorem norm_fwdMapInv_mul_I_sub_le_integral (hW : Continuous W) (hW0 : W 0 = 0) {t : ℝ}
    (ht : 0 ≤ t) {y₁ y₂ : ℝ} (hy₂ : 0 < y₂) (hy : y₂ ≤ y₁) :
    ‖fwdMapInv W t (y₁ * I) - fwdMapInv W t (y₂ * I)‖ ≤
      ∫ v in y₂..y₁, ‖deriv (fwdMapInv W t) (v * I)‖ := by
  set f : ℂ → ℂ := fwdMapInv W t with hf
  have hopen : IsOpen {z : ℂ | 0 < z.im} := isOpen_lt continuous_const Complex.continuous_im
  have hd : DifferentiableOn ℂ f {z : ℂ | 0 < z.im} := RS.differentiableOn_fwdMapInv hW hW0 ht
  have hd' : DifferentiableOn ℂ (deriv f) {z : ℂ | 0 < z.im} := hd.deriv hopen
  have hmem : ∀ x ∈ uIcc y₂ y₁, (x : ℂ) * I ∈ {z : ℂ | 0 < z.im} := fun x hx => by
    rw [uIcc_of_le hy] at hx
    exact ofReal_mul_I_mem_H (lt_of_lt_of_le hy₂ hx.1)
  have hγ : ∀ s : ℝ, HasDerivAt (fun y : ℝ => (y : ℂ) * I) I s := fun s =>
    (hasDerivAt_mul_const (x := (s : ℂ)) (I : ℂ)).comp_ofReal
  have hderiv : ∀ x ∈ uIcc y₂ y₁,
      HasDerivAt (fun x : ℝ => f (x * I)) (deriv f (x * I) * I) x := by
    intro x hx
    have hdx : DifferentiableAt ℂ f (x * I) := hd.differentiableAt (hopen.mem_nhds (hmem x hx))
    exact hdx.hasDerivAt.comp x (hγ x)
  have hcont : ContinuousOn (fun x : ℝ => deriv f (x * I) * I) (uIcc y₂ y₁) := by
    have hc : ContinuousOn (fun x : ℝ => (x : ℂ) * I) (uIcc y₂ y₁) := by fun_prop
    exact (hd'.continuousOn.comp hc hmem).mul continuousOn_const
  rw [← intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hcont.intervalIntegrable]
  refine (intervalIntegral.norm_integral_le_integral_norm hy).trans (le_of_eq ?_)
  congr 1
  ext x
  rw [norm_mul, Complex.norm_I, mul_one]

/-- The same bound with the improper (Lebesgue) integral over `(0, y₁]`. -/
theorem ofReal_norm_fwdMapInv_mul_I_sub_le_lintegral (hW : Continuous W) (hW0 : W 0 = 0) {t : ℝ}
    (ht : 0 ≤ t) {y₁ y₂ : ℝ} (hy₂ : 0 < y₂) (hy : y₂ ≤ y₁) :
    ENNReal.ofReal ‖fwdMapInv W t (y₁ * I) - fwdMapInv W t (y₂ * I)‖ ≤
      ∫⁻ v in Ioc 0 y₁, ‖deriv (fwdMapInv W t) (v * I)‖ₑ := by
  set f : ℂ → ℂ := fwdMapInv W t with hf
  have hopen : IsOpen {z : ℂ | 0 < z.im} := isOpen_lt continuous_const Complex.continuous_im
  have hd : DifferentiableOn ℂ f {z : ℂ | 0 < z.im} := RS.differentiableOn_fwdMapInv hW hW0 ht
  have hd' : DifferentiableOn ℂ (deriv f) {z : ℂ | 0 < z.im} := hd.deriv hopen
  have hcont : ContinuousOn (fun x : ℝ => deriv f (x * I)) (Icc y₂ y₁) := by
    have hc : ContinuousOn (fun x : ℝ => (x : ℂ) * I) (Icc y₂ y₁) := by fun_prop
    exact hd'.continuousOn.comp hc fun x hx => ofReal_mul_I_mem_H (lt_of_lt_of_le hy₂ hx.1)
  have hint : IntegrableOn (fun x : ℝ => deriv f (x * I)) (Ioc y₂ y₁) :=
    (hcont.integrableOn_Icc).mono_set Ioc_subset_Icc_self
  calc ENNReal.ofReal ‖f (y₁ * I) - f (y₂ * I)‖
      ≤ ENNReal.ofReal (∫ v in y₂..y₁, ‖deriv f (v * I)‖) :=
        ENNReal.ofReal_le_ofReal (norm_fwdMapInv_mul_I_sub_le_integral hW hW0 ht hy₂ hy)
    _ = ∫⁻ v in Ioc y₂ y₁, ‖deriv f (v * I)‖ₑ := by
        rw [intervalIntegral.integral_of_le hy, ofReal_integral_norm_eq_lintegral_enorm hint]
    _ ≤ ∫⁻ v in Ioc 0 y₁, ‖deriv f (v * I)‖ₑ :=
        lintegral_mono_set (Ioc_subset_Ioc_left hy₂.le)

/-! ## Uniform Cauchy bounds give uniform radial limits -/

/-- **Uniform radial limits from a uniform Cauchy bound.** If `‖F y t − F y' t‖ ≤ ε y` for
`0 < y' ≤ y ≤ y₀` and `t ∈ S`, with `ε y → 0` as `y ↓ 0`, then `F y t` converges as `y ↓ 0`, uniformly
on `S`, to `limUnder (𝓝[>] 0) (F · t)`, and the limit is within `ε y` of `F y t`. -/
theorem tendstoUniformlyOn_limUnder_of_norm_sub_le {α : Type*} {F : ℝ → α → ℂ} {S : Set α}
    {ε : ℝ → ℝ} {y₀ : ℝ} (hy₀ : 0 < y₀) (hε : Tendsto ε (𝓝[>] 0) (𝓝 0))
    (h : ∀ t ∈ S, ∀ y ∈ Ioc 0 y₀, ∀ y' ∈ Ioc 0 y, ‖F y t - F y' t‖ ≤ ε y) :
    (∀ t ∈ S, Tendsto (fun y => F y t) (𝓝[>] 0) (𝓝 (limUnder (𝓝[>] 0) fun y => F y t))) ∧
      (∀ t ∈ S, ∀ y ∈ Ioc 0 y₀, ‖F y t - limUnder (𝓝[>] 0) (fun y => F y t)‖ ≤ ε y) ∧
      TendstoUniformlyOn F (fun t => limUnder (𝓝[>] (0 : ℝ)) fun y => F y t) (𝓝[>] 0) S := by
  have hIoc : Ioc (0 : ℝ) y₀ ∈ 𝓝[>] (0 : ℝ) := RS.Ioc_mem_nhdsGT_zero hy₀
  -- the good set of heights for a tolerance `e`
  have hgood : ∀ e > (0 : ℝ), {y : ℝ | y ∈ Ioc 0 y₀ ∧ ε y < e} ∈ 𝓝[>] (0 : ℝ) := fun e he =>
    inter_mem hIoc (hε (Iio_mem_nhds he))
  have hlim : ∀ t ∈ S, Tendsto (fun y => F y t) (𝓝[>] 0)
      (𝓝 (limUnder (𝓝[>] 0) fun y => F y t)) := by
    intro t ht
    refine tendsto_nhds_limUnder (cauchy_map_iff_exists_tendsto.1 ?_)
    refine Metric.cauchy_iff.2 ⟨inferInstance, fun e he => ?_⟩
    refine ⟨(fun y => F y t) '' {y : ℝ | y ∈ Ioc 0 y₀ ∧ ε y < e}, image_mem_map (hgood e he), ?_⟩
    rintro _ ⟨y, hy, rfl⟩ _ ⟨y', hy', rfl⟩
    rw [dist_eq_norm]
    rcases le_total y' y with hyy | hyy
    · exact (h t ht y hy.1 y' ⟨hy'.1.1, hyy⟩).trans_lt hy.2
    · rw [norm_sub_rev]
      exact (h t ht y' hy'.1 y ⟨hy.1.1, hyy⟩).trans_lt hy'.2
  have hbd : ∀ t ∈ S, ∀ y ∈ Ioc 0 y₀,
      ‖F y t - limUnder (𝓝[>] 0) (fun y => F y t)‖ ≤ ε y := by
    intro t ht y hy
    have hT : Tendsto (fun y' => ‖F y t - F y' t‖) (𝓝[>] 0)
        (𝓝 ‖F y t - limUnder (𝓝[>] 0) (fun y => F y t)‖) :=
      ((hlim t ht).const_sub (F y t)).norm
    refine le_of_tendsto hT ?_
    filter_upwards [RS.Ioc_mem_nhdsGT_zero hy.1] with y' hy'
    exact h t ht y hy y' hy'
  refine ⟨hlim, hbd, ?_⟩
  rw [Metric.tendstoUniformlyOn_iff]
  intro e he
  filter_upwards [hgood e he] with y hy t ht
  rw [dist_comm, dist_eq_norm]
  exact (hbd t ht y hy.1).trans_lt hy.2

/-- The uniform Cauchy bound for the centered inverse maps on `[0, T]` gives the uniform
convergence `F_t(iy) → trace W t` on `[0, T]` and the continuity of `trace W` there. -/
theorem tendstoUniformlyOn_trace_of_norm_sub_le (hW : Continuous W) (hW0 : W 0 = 0) {T : ℝ}
    (hT : 0 ≤ T) {ε : ℝ → ℝ} {y₀ : ℝ} (hy₀ : 0 < y₀) (hε : Tendsto ε (𝓝[>] 0) (𝓝 0))
    (h : ∀ t ∈ Icc 0 T, ∀ y ∈ Ioc 0 y₀, ∀ y' ∈ Ioc 0 y,
      ‖fwdMapInv W t (y * I) - fwdMapInv W t (y' * I)‖ ≤ ε y) :
    TendstoUniformlyOn (fun (y : ℝ) (s : ℝ) => fwdMapInv W s (y * I)) (trace W) (𝓝[>] 0)
        (Icc 0 T) ∧
      ContinuousOn (trace W) (Icc 0 T) := by
  obtain ⟨-, -, hU⟩ := tendstoUniformlyOn_limUnder_of_norm_sub_le
    (F := fun (y : ℝ) (s : ℝ) => fwdMapInv W s (y * I)) hy₀ hε h
  have hU' : TendstoUniformlyOn (fun (y : ℝ) (s : ℝ) => fwdMapInv W s (y * I)) (trace W)
      (𝓝[>] 0) (Icc 0 T) := hU
  refine ⟨hU', hU'.continuousOn ?_⟩
  exact ((eventually_mem_nhdsWithin (s := Ioi (0 : ℝ)) (a := 0)).mono fun y hy =>
    RS.continuousOn_fwdMapInv_mul_I hW hW0 (mem_Ioi.1 hy) hT).frequently

/-- A function on `ℝ` continuous on every `[0, T]` restricts to a continuous function on `ℝ≥0`. -/
theorem continuous_comp_coe_of_continuousOn {E : Type*} [TopologicalSpace E] {g : ℝ → E}
    (h : ∀ T : ℝ, 0 ≤ T → ContinuousOn g (Icc 0 T)) : Continuous fun t : ℝ≥0 => g t := by
  refine continuous_iff_continuousAt.2 fun t₀ => ?_
  have hc : ContinuousOn (g ∘ NNReal.toReal) (NNReal.toReal ⁻¹' Icc 0 ((t₀ : ℝ) + 1)) :=
    (h _ (by positivity)).comp NNReal.continuous_coe.continuousOn (mapsTo_preimage _ _)
  refine hc.continuousAt (Filter.mem_of_superset
    ((isOpen_Iio.preimage NNReal.continuous_coe).mem_nhds (show (t₀ : ℝ) < t₀ + 1 by linarith))
    fun x hx => ⟨x.2, le_of_lt hx⟩)

/-! ## The bridge: uniform radial bounds give the trace and generate the hulls -/

/-- **Deterministic bridge (SLE₈ note, proof of Theorem 1.1, pp. 11–12), Cauchy form.** Let `W` be a
continuous driver with `W 0 = 0`. Suppose that on every `[0, T]` the centered inverse maps satisfy a
uniform Cauchy bound `‖F_t(iy) − F_t(iy')‖ ≤ ε_T(y)` for `0 < y' ≤ y ≤ y₀(T)`, with `ε_T(y) → 0` as
`y ↓ 0`. Then `F_t(iy)` converges locally uniformly in `t ∈ [0, ∞)` to a continuous
`γ : ℝ≥0 → \overline{ℍ}` with `γ 0 = 0`, and for every `t` the domain `ℍ \ K_t` is the unbounded
connected component of `ℍ \ γ([0, t])` — the conclusion of the frozen Theorem 1.1 for the driver
`W`. -/
theorem exists_continuous_trace_of_norm_sub_le (hW : Continuous W) (hW0 : W 0 = 0)
    (h : ∀ T : ℝ, 0 ≤ T → ∃ ε : ℝ → ℝ, Tendsto ε (𝓝[>] 0) (𝓝 0) ∧ ∃ y₀ > (0 : ℝ),
      ∀ t ∈ Icc 0 T, ∀ y ∈ Ioc 0 y₀, ∀ y' ∈ Ioc 0 y,
        ‖fwdMapInv W t (y * I) - fwdMapInv W t (y' * I)‖ ≤ ε y) :
    ∃ γ : ℝ≥0 → ℂ,
      TendstoLocallyUniformly
          (fun (y : ℝ) (t : ℝ≥0) => fwdMapInv W t (y * Complex.I)) γ (𝓝[>] 0) ∧
        Continuous γ ∧ (∀ t, γ t ∈ Hbar) ∧ γ 0 = 0 ∧
        ∀ t : ℝ≥0,
          (∃ z ∈ H \ fwdHull W t,
              connectedComponentIn (H \ γ '' Icc 0 t) z = H \ fwdHull W t) ∧
            ¬ Bornology.IsBounded (H \ fwdHull W t) := by
  have hU : ∀ T : ℝ, 0 ≤ T →
      TendstoUniformlyOn (fun (y : ℝ) (s : ℝ) => fwdMapInv W s (y * I)) (trace W) (𝓝[>] 0)
        (Icc 0 T) ∧ ContinuousOn (trace W) (Icc 0 T) := by
    intro T hT
    obtain ⟨ε, hε, y₀, hy₀, hb⟩ := h T hT
    exact tendstoUniformlyOn_trace_of_norm_sub_le hW hW0 hT hy₀ hε hb
  refine ⟨fun t => trace W t, ?_, continuous_comp_coe_of_continuousOn fun T hT => (hU T hT).2,
    fun t => ?_, ?_, fun t => ?_⟩
  · -- locally uniform convergence on `ℝ≥0`
    rw [tendstoLocallyUniformly_iff_forall_isCompact]
    intro K hK
    obtain ⟨T, hT⟩ := hK.bddAbove
    exact ((hU T T.2).1.comp NNReal.toReal).mono fun x hx =>
      ⟨x.2, NNReal.coe_le_coe.2 (hT hx)⟩
  · -- the trace lies in the closed half-plane
    have hlim := (hU t t.2).1.tendsto_at ⟨t.2, le_rfl⟩
    refine (isClosed_le continuous_const Complex.continuous_im).mem_of_tendsto hlim ?_
    filter_upwards [self_mem_nhdsWithin] with y (hy : 0 < y)
    exact le_of_lt (RS.fwdMapInv_mem_H hW hW0 t.2 (ofReal_mul_I_mem_H hy))
  · -- `γ(0) = 0`, since `F_0` is the identity
    show trace W ((0 : ℝ≥0) : ℝ) = 0
    rw [NNReal.coe_zero]
    unfold trace
    have heq : (fun y : ℝ => fwdMapInv W 0 (y * Complex.I)) =ᶠ[𝓝[>] (0 : ℝ)]
        fun y : ℝ => (y : ℂ) * Complex.I := by
      filter_upwards [self_mem_nhdsWithin] with y (hy : 0 < y)
      exact fwdMapInv_zero_eq_self hW hW0 (ofReal_mul_I_mem_H hy)
    refine Tendsto.limUnder_eq ((tendsto_congr' heq).2 ?_)
    have hc : Continuous fun y : ℝ => (y : ℂ) * Complex.I := by fun_prop
    simpa using (hc.tendsto 0).mono_left (nhdsWithin_le_nhds (s := Ioi (0 : ℝ)))
  · -- the hull complement is the unbounded component (QuantumZipper's form of [RS05, Thm 4.1])
    obtain ⟨hunif, hcont⟩ := hU t t.2
    obtain ⟨M₀, hM₀⟩ :=
      RS.exists_compl_fwdHull_eq_connectedComponentIn_mul_I hW hW0 t.2 hunif hcont
    have himg : (fun s : ℝ≥0 => trace W s) '' Icc 0 t = trace W '' Icc 0 (t : ℝ) := by
      rw [show (fun s : ℝ≥0 => trace W s) = trace W ∘ NNReal.toReal from rfl, image_comp,
        NNReal.image_coe_Icc, NNReal.coe_zero]
    refine ⟨⟨(M₀ : ℂ) * I, (hM₀ M₀ le_rfl).1, ?_⟩, ?_⟩
    · rw [himg]
      exact ((hM₀ M₀ le_rfl).2).symm
    · intro hbdd
      obtain ⟨R, hR⟩ := isBounded_iff_forall_norm_le.1 hbdd
      set M : ℝ := max M₀ (|R| + 1) with hM
      have hMmem := (hM₀ M (le_max_left _ _)).1
      have h1 := hR _ hMmem
      have hMpos : 0 < M := lt_of_lt_of_le (by positivity) (le_max_right M₀ (|R| + 1))
      rw [norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos hMpos] at h1
      linarith [le_max_right M₀ (|R| + 1), le_abs_self R]

/-- **Deterministic bridge, integral form** (the form of Proposition 5.1 and (5.6)). If on every
`[0, T]` the improper integrals `∫_0^y |F_t'(iv)| dv` are bounded, uniformly in `t ∈ [0, T]`, by
`ε_T(y)` for `0 < y ≤ y₀(T)`, with `ε_T(y) → 0` as `y ↓ 0`, then the conclusion of the frozen
Theorem 1.1 holds for the driver `W`. -/
theorem exists_continuous_trace_of_lintegral_le (hW : Continuous W) (hW0 : W 0 = 0)
    (h : ∀ T : ℝ, 0 ≤ T → ∃ ε : ℝ → ℝ, Tendsto ε (𝓝[>] 0) (𝓝 0) ∧ ∃ y₀ > (0 : ℝ),
      ∀ t ∈ Icc 0 T, ∀ y ∈ Ioc 0 y₀,
        ∫⁻ v in Ioc 0 y, ‖deriv (fwdMapInv W t) (v * I)‖ₑ ≤ ENNReal.ofReal (ε y)) :
    ∃ γ : ℝ≥0 → ℂ,
      TendstoLocallyUniformly
          (fun (y : ℝ) (t : ℝ≥0) => fwdMapInv W t (y * Complex.I)) γ (𝓝[>] 0) ∧
        Continuous γ ∧ (∀ t, γ t ∈ Hbar) ∧ γ 0 = 0 ∧
        ∀ t : ℝ≥0,
          (∃ z ∈ H \ fwdHull W t,
              connectedComponentIn (H \ γ '' Icc 0 t) z = H \ fwdHull W t) ∧
            ¬ Bornology.IsBounded (H \ fwdHull W t) := by
  refine exists_continuous_trace_of_norm_sub_le hW hW0 fun T hT => ?_
  obtain ⟨ε, hε, y₀, hy₀, hb⟩ := h T hT
  refine ⟨fun y => max (ε y) 0, ?_, y₀, hy₀, fun t ht y hy y' hy' => ?_⟩
  · simpa using hε.max (tendsto_const_nhds (x := (0 : ℝ)))
  · have h1 := (ofReal_norm_fwdMapInv_mul_I_sub_le_lintegral hW hW0 ht.1 hy'.1 hy'.2).trans
      (hb t ht y hy)
    rcases (ENNReal.ofReal_le_ofReal_iff'.1 h1) with h2 | h2
    · exact h2.trans (le_max_left _ _)
    · exact h2.trans (le_max_right _ _)

/-! ## Scaling (Brownian scaling bookkeeping, pp. 11–12: "Brownian scaling applies the same
conclusion on each deterministic interval `[0, j]`") -/

/-- Change of variables `u = a v` in a lintegral over `(0, y]`. -/
theorem setLIntegral_Ioc_comp_mul_left (g : ℝ → ℝ≥0∞) {a : ℝ} (ha : 0 < a) (y : ℝ) :
    ∫⁻ v in Ioc 0 y, g (a * v) = ENNReal.ofReal a⁻¹ * ∫⁻ u in Ioc 0 (a * y), g u := by
  have hemb : MeasurableEmbedding fun x : ℝ => a * x := measurableEmbedding_mulLeft₀ ha.ne'
  rw [← lintegral_indicator measurableSet_Ioc, ← lintegral_indicator measurableSet_Ioc]
  have hiff : ∀ v : ℝ, a * v ∈ Ioc 0 (a * y) ↔ v ∈ Ioc 0 y := fun v => by
    simp only [mem_Ioc]
    constructor
    · rintro ⟨h1, h2⟩
      exact ⟨pos_of_mul_pos_right h1 ha.le, le_of_mul_le_mul_left h2 ha⟩
    · rintro ⟨h1, h2⟩
      exact ⟨mul_pos ha h1, mul_le_mul_of_nonneg_left h2 ha.le⟩
  have hind : (Ioc 0 y).indicator (fun v => g (a * v)) =
      fun v => (Ioc 0 (a * y)).indicator g (a * v) := by
    ext v
    by_cases hv : v ∈ Ioc 0 y
    · rw [indicator_of_mem hv, indicator_of_mem ((hiff v).2 hv)]
    · rw [indicator_of_notMem hv, indicator_of_notMem (fun h => hv ((hiff v).1 h))]
  rw [hind, ← hemb.lintegral_map, Real.map_volume_mul_left ha.ne', lintegral_smul_measure,
    abs_of_pos (inv_pos.2 ha)]
  rfl

/-- Derivative of the scaled centered inverse map: for the driver `r ↦ W (a² r) / a`, the
derivative of `F_t` at `iv` equals the derivative of `F_{a² t}` (driver `W`) at `i a v`. -/
theorem deriv_fwdMapInv_scale (hW : Continuous W) (hW0 : W 0 = 0) {a : ℝ} (ha : 0 < a) {t : ℝ}
    (ht : 0 ≤ t) {v : ℝ} (hv : 0 < v) :
    deriv (fwdMapInv (fun r => W (a ^ 2 * r) / a) t) (v * I) =
      deriv (fwdMapInv W (a ^ 2 * t)) ((a * v : ℝ) * I) := by
  set F : ℂ → ℂ := fwdMapInv W (a ^ 2 * t) with hF
  have hev : fwdMapInv (fun r => W (a ^ 2 * r) / a) t =ᶠ[𝓝 ((v : ℂ) * I)]
      fun w => F (a * w) / a :=
    Filter.eventually_of_mem (isOpen_H.mem_nhds (ofReal_mul_I_mem_H hv)) fun w hw =>
      RS.fwdMapInv_scale hW hW0 ha ht hw
  rw [hev.deriv_eq]
  have hpt : (a : ℂ) * ((v : ℂ) * I) = ((a * v : ℝ) : ℂ) * I := by push_cast; ring
  have hdF : DifferentiableAt ℂ F ((a : ℂ) * ((v : ℂ) * I)) := by
    rw [hpt]
    exact RS.differentiableAt_fwdMapInv hW hW0 (by positivity)
      (ofReal_mul_I_mem_H (mul_pos ha hv))
  have hlin : HasDerivAt (fun w : ℂ => (a : ℂ) * w) (a : ℂ) ((v : ℂ) * I) := by
    simpa using (hasDerivAt_id ((v : ℂ) * I)).const_mul (a : ℂ)
  have h2 : HasDerivAt (fun w => F (a * w) / a) (deriv F ((a : ℂ) * ((v : ℂ) * I)) * a / a)
      ((v : ℂ) * I) := (hdF.hasDerivAt.comp _ hlin).div_const _
  rw [h2.deriv, mul_div_assoc, div_self (by exact_mod_cast ha.ne'), mul_one, hpt]

/-- **Scaling of the radial integrals.** For the driver `r ↦ W (a² r) / a` (Brownian scaling with
`a = √j`), `∫_0^y |F_t'(iv)| dv = a⁻¹ ∫_0^{a y} |F_{a² t}'(iu)| du`, where the right side uses the
driver `W`. -/
theorem lintegral_deriv_fwdMapInv_scale (hW : Continuous W) (hW0 : W 0 = 0) {a : ℝ} (ha : 0 < a)
    {t : ℝ} (ht : 0 ≤ t) (y : ℝ) :
    ∫⁻ v in Ioc 0 y, ‖deriv (fwdMapInv (fun r => W (a ^ 2 * r) / a) t) (v * I)‖ₑ =
      ENNReal.ofReal a⁻¹ * ∫⁻ u in Ioc 0 (a * y), ‖deriv (fwdMapInv W (a ^ 2 * t)) (u * I)‖ₑ := by
  rw [← setLIntegral_Ioc_comp_mul_left (fun u => ‖deriv (fwdMapInv W (a ^ 2 * t)) (u * I)‖ₑ) ha]
  refine setLIntegral_congr_fun measurableSet_Ioc fun v hv => ?_
  rw [deriv_fwdMapInv_scale hW hW0 ha ht hv.1]

end InteractingSLE.SLE8
