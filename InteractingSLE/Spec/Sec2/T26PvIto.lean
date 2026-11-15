/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec2.T26PvAlg
import InteractingSLE.Spec.Sec2.T26PvPath
import InteractingSLE.Spec.Ito.Gm2Lifetime
import InteractingSLE.Spec.Ito.Measurability

/-!
# Theorem 2.6, the provider, part 4: the one-point semimartingale argument

Packet PROVE-T26-PROVIDER. Specification, proof of Theorem 2.6 (`source/spec/p001-048.md` L977–L986): "The
semimartingale argument in the proof of Theorem 2.4 applies using this one point `z`, after localization before it is
swallowed. […] the prescribed bracket implies `dQ_t = κ dt`. Equation (2.6), now for this single point, then implies
`dC_t = 0`."

Let `X = 𝔥(z)` be a continuous local martingale before `ζ ≤ τ_z` with `X² − A` one too, `A_t = log (crad(ℍ, z) /
crad(ℍ ∖ K_t, z))`. With the coordinates `Y = (g_t(z), V, Im log f_t'(z))` (finite variation: `dg = 2/f dt`,
`dℓ = Im(−2/f²) dt`, `dVʲ` the Stieltjes measures of the force points) the driver is `W = drvF(Y, X)`
(`T26PvAlg`). The mixed Itô formula `Ito.Gm2.isCLMBefore_residual_and_bracket` (general bracket, before a lifetime)
gives that the residual `W − ∫ drift` and its square minus `∫ (∂ₓ drvF)² dA` are continuous local martingales before
`ζ`. Pointwise (`T26PvAlg`, `T26PvStj`):

* the bracket density is `κ`, so the bracket is `κ t` ("`dQ = κ dt`");
* the drift is `−½ ∑ ρⱼ (Vʲ_t − Vʲ_0)` ("`dC = 0`"), so the residual is `martProc ρ W V = W − W₀ + ½ ∑ ρⱼ (Vʲ − Vʲ₀)`.

Main result: **`isCLMBefore_martProc_of_onePoint`**: `martProc` and `martProc² − κ t` are continuous local
martingales before `ζ`. The coordinates are read through the killed Loewner map (`Ito.aliveSet`), so that they are
adapted at every time; before `ζ` they are the actual ones.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open QuantumZipper (H)
open scoped NNReal ENNReal

namespace InteractingSLE.Sec2.T26Pv

open Ito

/-! ### Continuity before a lifetime from continuity on compact intervals -/

theorem continuousOn_lt_of_Icc {E : Type*} [TopologicalSpace E] {g : ℝ → E} {τ : ℝ≥0∞}
    (h : ∀ T : ℝ≥0, (T : ℝ≥0∞) < τ → ContinuousOn g (Icc 0 (T : ℝ))) :
    ContinuousOn (fun t : ℝ≥0 => g t) {t | (t : ℝ≥0∞) < τ} := by
  intro t ht
  obtain ⟨T, htT, hTτ⟩ := ENNReal.lt_iff_exists_nnreal_btwn.1 ht
  have htT' : t < T := by exact_mod_cast htT
  have hc : ContinuousWithinAt g (Icc 0 (T : ℝ)) t := h T hTτ t ⟨t.coe_nonneg, by exact_mod_cast htT'.le⟩
  have hc' : ContinuousWithinAt (fun s : ℝ≥0 => g s) (Iic T) t := by
    refine hc.comp NNReal.continuous_coe.continuousWithinAt fun s hs => ⟨s.coe_nonneg, ?_⟩
    exact_mod_cast hs
  exact (hc'.continuousAt (Iic_mem_nhds htT')).continuousWithinAt

/-! ### The killed one-point coordinates -/

section Coords

variable {Ω : Type*} {ι : Type*} [Fintype ι]

/-- The alive event at time `t`: `z` has a forward solution on `[0, t]`. -/
def alv (W : ℝ≥0 → Ω → ℝ) (z : ℂ) (t : ℝ≥0) : Set Ω := Ito.aliveSet W (fun _ => ⊤) univ z t

open Classical in
/-- The killed forward map `f_t(z)` (`0` off the alive event). -/
def fK (W : ℝ≥0 → Ω → ℝ) (z : ℂ) (t : ℝ≥0) (ω : Ω) : ℂ :=
  if ω ∈ alv W z t then QuantumZipper.fwdMap (rpath (W · ω)) t z else 0

open Classical in
/-- The killed `Im log f_t'(z)` (`0` off the alive event). -/
def ℓK (W : ℝ≥0 → Ω → ℝ) (z : ℂ) (t : ℝ≥0) (ω : Ω) : ℝ :=
  if ω ∈ alv W z t then (QuantumZipper.logDerivFwd (rpath (W · ω)) t z).im else 0

/-- The finite-variation coordinates `Y = (g_t(z), V_t, Im log f_t'(z))`. -/
def Yc (W : ℝ≥0 → Ω → ℝ) (V : ι → ℝ≥0 → Ω → ℝ) (z : ℂ) (t : ℝ≥0) (ω : Ω) : St ι :=
  (fK W z t ω + (W t ω : ℂ), fun j => V j t ω, ℓK W z t ω)

/-- The time density of `Y`. -/
def cT (W : ℝ≥0 → Ω → ℝ) (z : ℂ) (t : ℝ≥0) (ω : Ω) : St ι := timeDir ι (fK W z t ω)

/-- The density of the bracket `A` against time: `4 (Im f)²/|f|⁴`. -/
def aT (W : ℝ≥0 → Ω → ℝ) (z : ℂ) (t : ℝ≥0) (ω : Ω) : ℝ :=
  4 * (fK W z t ω).im ^ 2 / ‖fK W z t ω‖ ^ 4

/-- The explicit bracket `log (2 Im z / (2 Im f_t(z)/|f_t'(z)|))`. -/
def Aexp (W : ℝ≥0 → Ω → ℝ) (z : ℂ) (t : ℝ≥0) (ω : Ω) : ℝ :=
  Real.log (2 * z.im / (2 * (QuantumZipper.fwdMap (rpath (W · ω)) t z).im /
    ‖deriv (QuantumZipper.fwdMap (rpath (W · ω)) t) z‖))

variable {W : ℝ≥0 → Ω → ℝ} {z : ℂ} {ω : Ω} {t : ℝ≥0}

theorem continuous_rpath' (hWc : Continuous (W · ω)) : Continuous (rpath (W · ω)) :=
  hWc.comp continuous_real_toNNReal

theorem mem_alv_of_lt (hz : z ∈ H)
    (ht : (t : ℝ≥0∞) < QuantumZipper.swallowTime (rpath (W · ω)) z) : ω ∈ alv W z t := by
  refine ⟨mem_univ _, ENNReal.coe_lt_top, ?_⟩
  exact exists_isForwardSol_of_mem t.coe_nonneg (Certify2426.mem_diff_fwdHull_of_lt_swallowTime hz ht)

theorem fK_of_lt (hz : z ∈ H)
    (ht : (t : ℝ≥0∞) < QuantumZipper.swallowTime (rpath (W · ω)) z) :
    fK W z t ω = QuantumZipper.fwdMap (rpath (W · ω)) t z := by
  classical
  simp only [fK, mem_alv_of_lt hz ht, ↓reduceIte]

theorem ℓK_of_lt (hz : z ∈ H)
    (ht : (t : ℝ≥0∞) < QuantumZipper.swallowTime (rpath (W · ω)) z) :
    ℓK W z t ω = (QuantumZipper.logDerivFwd (rpath (W · ω)) t z).im := by
  classical
  simp only [ℓK, mem_alv_of_lt hz ht, ↓reduceIte]

theorem im_fwdMap_pos_of_lt (hWc : Continuous (W · ω)) (hz : z ∈ H)
    (ht : (t : ℝ≥0∞) < QuantumZipper.swallowTime (rpath (W · ω)) z) :
    0 < (QuantumZipper.fwdMap (rpath (W · ω)) t z).im :=
  im_fwdMap_pos (continuous_rpath' hWc) t.coe_nonneg
    (Certify2426.mem_diff_fwdHull_of_lt_swallowTime hz ht) ⟨t.coe_nonneg, le_rfl⟩

/-- On `[0, T]`, `T < τ_z`, the killed forward map is the forward map. -/
theorem fK_toNNReal_of_mem_Icc (hz : z ∈ H) {T : ℝ≥0}
    (hT : (T : ℝ≥0∞) < QuantumZipper.swallowTime (rpath (W · ω)) z) {x : ℝ} (hx : x ∈ Icc 0 (T : ℝ)) :
    fK W z x.toNNReal ω = QuantumZipper.fwdMap (rpath (W · ω)) x z := by
  have hxT : (x.toNNReal : ℝ≥0∞) < QuantumZipper.swallowTime (rpath (W · ω)) z := by
    refine lt_of_le_of_lt ?_ hT
    exact_mod_cast Real.toNNReal_le_iff_le_coe.2 hx.2
  rw [fK_of_lt hz hxT, Real.coe_toNNReal _ hx.1]

end Coords

/-! ### Adaptedness of the killed coordinates -/

section MeasHelp

variable {α : Type*} {m : MeasurableSpace α} {ι : Type*}

/-- Measurability of a triple (binder σ-algebra, so that it applies to `Measurable[𝓖 t]`). -/
theorem measurable_triple {f : α → ℂ} {g : α → ι → ℝ} {h : α → ℝ} (hf : Measurable f) (hg : Measurable g)
    (hh : Measurable h) : Measurable fun a => (f a, g a, h a) :=
  hf.prodMk (hg.prodMk hh)

/-- Measurability into a function space (binder σ-algebra). -/
theorem measurable_pi_of {g : α → ι → ℝ} (h : ∀ j, Measurable fun a => g a j) : Measurable g :=
  Measurable.of_eval h

end MeasHelp

section Meas

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {𝓖 : Filtration ℝ≥0 mΩ} {ι : Type*} [Fintype ι]
  {W : ℝ≥0 → Ω → ℝ} {V : ι → ℝ≥0 → Ω → ℝ} {z : ℂ}

theorem adaptedBefore_top_of_stronglyAdapted (hWa : StronglyAdapted 𝓖 W) :
    AdaptedBefore 𝓖 (fun _ => ⊤) W := by
  intro t A hA
  have he : {ω | (t : ℝ≥0∞) < ⊤ ∧ W t ω ∈ A} = W t ⁻¹' A := by
    ext ω
    simp
  rw [he]
  exact (hWa t).measurable hA

theorem measurable_fK (hWa : StronglyAdapted 𝓖 W) (hWc : ∀ ω, Continuous (W · ω)) (hz : z ∈ H)
    (t : ℝ≥0) : Measurable[𝓖 t] (fK W z t) := by
  classical
  have h := Ito.measurable_fwdMap_alive (adaptedBefore_top_of_stronglyAdapted hWa)
    (fun ω _ => (hWc ω).continuousOn) (@MeasurableSet.univ Ω (𝓖 0)) hz t
  convert h using 1
  funext ω
  by_cases hω : ω ∈ Ito.aliveSet W (fun _ => ⊤) univ z t
  · simp only [fK, alv, hω, ↓reduceIte]
  · simp only [fK, alv, hω, ↓reduceIte]

theorem measurable_ℓK (hWa : StronglyAdapted 𝓖 W) (hWc : ∀ ω, Continuous (W · ω)) (hz : z ∈ H)
    (t : ℝ≥0) : Measurable[𝓖 t] (ℓK W z t) := by
  classical
  have h := Ito.measurable_logDerivFwd_alive (adaptedBefore_top_of_stronglyAdapted hWa)
    (fun ω _ => (hWc ω).continuousOn) (@MeasurableSet.univ Ω (𝓖 0)) hz t
  have h' := Complex.continuous_im.measurable.comp h
  convert h' using 1
  funext ω
  by_cases hω : ω ∈ Ito.aliveSet W (fun _ => ⊤) univ z t
  · simp only [ℓK, alv, hω, ↓reduceIte, Function.comp_apply]
  · simp only [ℓK, alv, hω, ↓reduceIte, Function.comp_apply, Complex.zero_im]

omit [Fintype ι] in
theorem measurable_timeDir : Measurable (timeDir ι) := by
  unfold timeDir
  have h1 : Measurable fun f : ℂ => (2 : ℂ) / f := measurable_const.div measurable_id
  have h2 : Measurable fun f : ℂ => ((-2 : ℂ) / f ^ 2).im :=
    Complex.continuous_im.measurable.comp (measurable_const.div (measurable_id.pow_const 2))
  exact h1.prodMk (measurable_const.prodMk h2)

theorem measurable_aDens : Measurable fun f : ℂ => 4 * f.im ^ 2 / ‖f‖ ^ 4 :=
  (measurable_const.mul (Complex.continuous_im.measurable.pow_const 2)).div
    (continuous_norm.measurable.pow_const 4)

omit [Fintype ι] in
theorem measurable_Yc (hWa : StronglyAdapted 𝓖 W) (hWc : ∀ ω, Continuous (W · ω))
    (hVa : ∀ j, StronglyAdapted 𝓖 (V j)) (hz : z ∈ H) (t : ℝ≥0) :
    Measurable[𝓖 t] (Yc W V z t) := by
  have h1 : Measurable[𝓖 t] fun ω => fK W z t ω + (W t ω : ℂ) :=
    (measurable_fK hWa hWc hz t).add (Complex.measurable_ofReal.comp (hWa t).measurable)
  have h2 : Measurable[𝓖 t] fun ω => fun j => V j t ω :=
    @measurable_pi_of Ω (𝓖 t) ι _ fun j => (hVa j t).measurable
  exact @measurable_triple Ω (𝓖 t) ι _ _ _ h1 h2 (measurable_ℓK hWa hWc hz t)

omit [Fintype ι] in
theorem measurable_cT (hWa : StronglyAdapted 𝓖 W) (hWc : ∀ ω, Continuous (W · ω)) (hz : z ∈ H)
    (t : ℝ≥0) : Measurable[𝓖 t] (cT (ι := ι) W z t) :=
  measurable_timeDir.comp (measurable_fK hWa hWc hz t)

theorem measurable_aT (hWa : StronglyAdapted 𝓖 W) (hWc : ∀ ω, Continuous (W · ω)) (hz : z ∈ H)
    (t : ℝ≥0) : Measurable[𝓖 t] (aT W z t) :=
  measurable_aDens.comp (measurable_fK hWa hWc hz t)

end Meas

/-! ### Continuity before `τ_z` -/

section Cont

variable {Ω : Type*} {ι : Type*} [Fintype ι] {W : ℝ≥0 → Ω → ℝ} {V : ι → ℝ≥0 → Ω → ℝ} {z : ℂ} {ω : Ω}

/-- The times before the swallowing of `z`. -/
def befSw (W : ℝ≥0 → Ω → ℝ) (z : ℂ) (ω : Ω) : Set ℝ≥0 :=
  {t | (t : ℝ≥0∞) < QuantumZipper.swallowTime (rpath (W · ω)) z}

theorem continuousOn_fwdMap_befSw (hWc : Continuous (W · ω)) (hz : z ∈ H) :
    ContinuousOn (fun t : ℝ≥0 => QuantumZipper.fwdMap (rpath (W · ω)) t z) (befSw W z ω) :=
  continuousOn_lt_of_Icc (g := fun s : ℝ => QuantumZipper.fwdMap (rpath (W · ω)) s z) fun T hT =>
    continuousOn_fwdMap_time' (continuous_rpath' hWc) T.coe_nonneg
      (Certify2426.mem_diff_fwdHull_of_lt_swallowTime hz hT)

theorem continuousOn_logDerivFwd_befSw (hWc : Continuous (W · ω)) (hz : z ∈ H) :
    ContinuousOn (fun t : ℝ≥0 => QuantumZipper.logDerivFwd (rpath (W · ω)) t z) (befSw W z ω) :=
  continuousOn_lt_of_Icc (g := fun s : ℝ => QuantumZipper.logDerivFwd (rpath (W · ω)) s z) fun T hT =>
    continuousOn_logDerivFwd (continuous_rpath' hWc) T.coe_nonneg
      (Certify2426.mem_diff_fwdHull_of_lt_swallowTime hz hT)

theorem continuousOn_fK (hWc : Continuous (W · ω)) (hz : z ∈ H) :
    ContinuousOn (fun t => fK W z t ω) (befSw W z ω) :=
  (continuousOn_fwdMap_befSw hWc hz).congr fun _ ht => fK_of_lt hz ht

theorem fK_ne_zero (hWc : Continuous (W · ω)) (hz : z ∈ H) {t : ℝ≥0} (ht : t ∈ befSw W z ω) :
    fK W z t ω ≠ 0 := by
  rw [fK_of_lt hz ht]
  intro h0
  have := im_fwdMap_pos_of_lt hWc hz ht
  rw [h0, Complex.zero_im] at this
  exact lt_irrefl 0 this

theorem im_fK_pos (hWc : Continuous (W · ω)) (hz : z ∈ H) {t : ℝ≥0} (ht : t ∈ befSw W z ω) :
    0 < (fK W z t ω).im := by
  rw [fK_of_lt hz ht]
  exact im_fwdMap_pos_of_lt hWc hz ht

omit [Fintype ι] in
theorem continuousOn_Yc (hWc : Continuous (W · ω)) (hVc : ∀ j, Continuous (V j · ω)) (hz : z ∈ H) :
    ContinuousOn (fun t => Yc W V z t ω) (befSw W z ω) := by
  have h1 : ContinuousOn (fun t => fK W z t ω + (W t ω : ℂ)) (befSw W z ω) :=
    (continuousOn_fK hWc hz).add (Complex.continuous_ofReal.comp hWc).continuousOn
  have h2 : ContinuousOn (fun t => fun j => V j t ω) (befSw W z ω) :=
    (continuous_pi fun j => hVc j).continuousOn
  have h3 : ContinuousOn (fun t => ℓK W z t ω) (befSw W z ω) :=
    ((Complex.continuous_im.comp_continuousOn (continuousOn_logDerivFwd_befSw hWc hz)).congr
      fun _ ht => ℓK_of_lt hz ht)
  exact h1.prodMk (h2.prodMk h3)

omit [Fintype ι] in
theorem continuousOn_cT (hWc : Continuous (W · ω)) (hz : z ∈ H) :
    ContinuousOn (fun t => cT (ι := ι) W z t ω) (befSw W z ω) := by
  have hf := continuousOn_fK hWc hz
  have hne : ∀ t ∈ befSw W z ω, fK W z t ω ≠ 0 := fun t ht => fK_ne_zero hWc hz ht
  have h1 : ContinuousOn (fun t => (2 : ℂ) / fK W z t ω) (befSw W z ω) := continuousOn_const.div hf hne
  have h2 : ContinuousOn (fun t => ((-2 : ℂ) / fK W z t ω ^ 2).im) (befSw W z ω) :=
    Complex.continuous_im.comp_continuousOn (continuousOn_const.div (hf.pow 2) fun t ht => pow_ne_zero 2 (hne t ht))
  exact h1.prodMk (continuousOn_const.prodMk h2)

theorem continuousOn_aT (hWc : Continuous (W · ω)) (hz : z ∈ H) :
    ContinuousOn (fun t => aT W z t ω) (befSw W z ω) := by
  have hf := continuousOn_fK hWc hz
  exact (continuousOn_const.mul ((Complex.continuous_im.comp_continuousOn hf).pow 2)).div
    ((continuous_norm.comp_continuousOn hf).pow 4) fun t ht =>
      pow_ne_zero 4 (norm_ne_zero_iff.2 (fK_ne_zero hWc hz ht))

end Cont

/-! ### The integrators and densities -/

section Integrators

variable {Ω : Type*} {ι : Type*} [Fintype ι] [DecidableEq ι] {n : ℕ}

/-- The integrators: time, then the force points `ε_j Vʲ` (enumerated by `e`). -/
def Uf (V : ι → ℝ≥0 → Ω → ℝ) (ε : ι → ℝ) (hU : ∀ ω j, Monotone fun t => ε j * V j t ω)
    (hVc : ∀ ω j, Continuous (V j · ω)) (e : ι ≃ Fin n) : Fin (n + 1) → Ω → StieltjesFunction ℝ≥0 :=
  fun k ω => Fin.cases clk (fun i => stj (fun t => ε (e.symm i) * V (e.symm i) t ω) (hU ω _)
    (continuous_mul_path (hVc ω _))) k

/-- The densities of `Y`. -/
def cF (W : ℝ≥0 → Ω → ℝ) (z : ℂ) (ε : ι → ℝ) (e : ι ≃ Fin n) : Fin (n + 1) → ℝ≥0 → Ω → St ι :=
  fun k t ω => Fin.cases (cT W z t ω) (fun i => ε (e.symm i) • forceDir (e.symm i)) k

/-- The densities of the bracket `A`. -/
def aF (W : ℝ≥0 → Ω → ℝ) (z : ℂ) (n : ℕ) : Fin (n + 1) → ℝ≥0 → Ω → ℝ :=
  fun k t ω => Fin.cases (aT W z t ω) (fun _ => 0) k

end Integrators

/-! ### The per-sample identities -/

section Sample

variable {Ω : Type*} {ι : Type*} [Fintype ι] [DecidableEq ι] {n : ℕ}
  {W : ℝ≥0 → Ω → ℝ} {V : ι → ℝ≥0 → Ω → ℝ} {z : ℂ} {ω : Ω} {ε : ι → ℝ}

omit [Fintype ι] [DecidableEq ι] in
theorem befSw_mono {s t : ℝ≥0} (hst : s ≤ t) (ht : t ∈ befSw W z ω) : s ∈ befSw W z ω := by
  show (s : ℝ≥0∞) < _
  exact lt_of_le_of_lt (by exact_mod_cast hst) ht

omit [Fintype ι] [DecidableEq ι] in
theorem Icc_subset_befSw {t : ℝ≥0} (ht : t ∈ befSw W z ω) : Icc 0 t ⊆ befSw W z ω :=
  fun _ hs => befSw_mono hs.2 ht

theorem integrableOn_Ioc_of_continuousOn {E : Type*} [NormedAddCommGroup E] (A : StieltjesFunction ℝ≥0)
    {g : ℝ≥0 → E} {t : ℝ≥0} (hg : ContinuousOn g (Icc 0 t)) : IntegrableOn g (Ioc 0 t) A.measure :=
  (hg.integrableOn_Icc).mono_set Ioc_subset_Icc_self

omit [Fintype ι] [DecidableEq ι] in
theorem zero_mem_befSw (hWc : Continuous (W · ω)) (hz : z ∈ H) : (0 : ℝ≥0) ∈ befSw W z ω := by
  show ((0 : ℝ≥0) : ℝ≥0∞) < _
  rw [ENNReal.coe_zero]
  exact QuantumZipper.swallowTime_pos (continuous_rpath' hWc) hz

omit [Fintype ι] [DecidableEq ι] in
theorem fK_zero_add (hWc : Continuous (W · ω)) (hz : z ∈ H) : fK W z 0 ω + (W 0 ω : ℂ) = z := by
  have hz0 : z ≠ ((rpath (W · ω) 0 : ℝ) : ℂ) := fun h => by
    have : (0 : ℝ) < z.im := hz
    rw [h] at this
    simp at this
  rw [fK_of_lt hz (zero_mem_befSw hWc hz), NNReal.coe_zero, Certify2426.fwdMap_time_zero _ hz0]
  simp [rpath]

omit [Fintype ι] [DecidableEq ι] in
theorem ℓK_zero (hWc : Continuous (W · ω)) (hz : z ∈ H) : ℓK W z 0 ω = 0 := by
  rw [ℓK_of_lt hz (zero_mem_befSw hWc hz)]
  simp [QuantumZipper.logDerivFwd]

/-- The force-point integrals: `∑ᵢ ∫_{(0,t]} εⱼ eⱼ d(εⱼ Vʲ) = (0, V_t − V_0, 0)`. -/
theorem sum_force_integral (hε : ∀ j, ε j * ε j = 1) (hU : ∀ ω j, Monotone fun t => ε j * V j t ω)
    (hVc' : ∀ ω j, Continuous (V j · ω)) (e : ι ≃ Fin n) (t : ℝ≥0) :
    ∑ i : Fin n, ∫ _ in Ioc 0 t, (ε (e.symm i) • forceDir (e.symm i) : St ι)
        ∂(stj (fun t => ε (e.symm i) * V (e.symm i) t ω) (hU ω _) (continuous_mul_path (hVc' ω _))).measure =
      ((0 : ℂ), fun j => V j t ω - V j 0 ω, (0 : ℝ)) := by
  simp only [setIntegral_const]
  rw [e.symm.sum_comp (fun j => (stj (fun t => ε j * V j t ω) (hU ω j)
    (continuous_mul_path (hVc' ω j))).measure.real (Ioc 0 t) • (ε j • forceDir j : St ι))]
  have hterm : ∀ j, (stj (fun t => ε j * V j t ω) (hU ω j) (continuous_mul_path (hVc' ω j))).measure.real
      (Ioc 0 t) • (ε j • forceDir j : St ι) = (V j t ω - V j 0 ω) • (forceDir j : St ι) := by
    intro j
    rw [Ito.Gen.stieltjes_measureReal_Ioc _ (zero_le : (0 : ℝ≥0) ≤ t), stj_apply, stj_apply, smul_smul]
    congr 1
    linear_combination (V j t ω - V j 0 ω) * hε j
  simp only [hterm]
  refine Prod.ext ?_ (Prod.ext ?_ ?_)
  · simp [forceDir, Prod.fst_sum]
  · funext k
    rw [Prod.snd_sum, Prod.fst_sum, Finset.sum_apply]
    rw [Finset.sum_eq_single k]
    · simp [forceDir]
    · intro j _ hjk
      simp [forceDir, Ne.symm hjk]
    · intro hk; exact absurd (Finset.mem_univ k) hk
  · simp [forceDir, Prod.snd_sum]

/-- **`Y` as Stieltjes integrals** (the input `hY` of the mixed Itô formula). -/
theorem Yc_eq_add_sum_integral (hWc : Continuous (W · ω)) (hz : z ∈ H) (hε : ∀ j, ε j * ε j = 1)
    (hU : ∀ ω j, Monotone fun t => ε j * V j t ω) (hVc' : ∀ ω j, Continuous (V j · ω)) (e : ι ≃ Fin n)
    {t : ℝ≥0} (ht : t ∈ befSw W z ω) :
    Yc W V z t ω = Yc W V z 0 ω + ∑ k, ∫ u in Ioc 0 t, cF W z ε e k u ω ∂(Uf V ε hU hVc' e k ω).measure := by
  rw [Fin.sum_univ_succ]
  simp only [cF, Uf, Fin.cases_zero, Fin.cases_succ]
  rw [sum_force_integral hε hU hVc' e t]
  have hcont : ContinuousOn (fun u => cT (ι := ι) W z u ω) (Icc 0 t) :=
    (continuousOn_cT hWc hz).mono (Icc_subset_befSw ht)
  have hint : Integrable (fun u => cT (ι := ι) W z u ω) (clk.measure.restrict (Ioc 0 t)) :=
    integrableOn_Ioc_of_continuousOn clk hcont
  have hint2 : Integrable (fun u => (cT (ι := ι) W z u ω).2) (clk.measure.restrict (Ioc 0 t)) :=
    hint.snd
  have hmemT : ∀ x ∈ Icc (0 : ℝ) t, fK W z x.toNNReal ω = QuantumZipper.fwdMap (rpath (W · ω)) x z :=
    fun x hx => fK_toNNReal_of_mem_Icc hz ht hx
  have hzt := Certify2426.mem_diff_fwdHull_of_lt_swallowTime hz ht
  have hr := continuous_rpath' hWc
  refine Prod.ext ?_ (Prod.ext ?_ ?_)
  · -- `g_t(z)`
    rw [Prod.fst_add, Prod.fst_add, fst_integral hint]
    simp only [Yc, cT, timeDir, add_zero]
    rw [fK_zero_add hWc hz, setIntegral_clk_eq_intervalIntegral_complex, fK_of_lt hz ht]
    have h := fwdMap_add_eq_add_integral hr t.coe_nonneg hzt
    rw [show (W t ω : ℂ) = (rpath (W · ω) t : ℂ) by simp [rpath], h]
    congr 1
    refine intervalIntegral.integral_congr fun x hx => ?_
    rw [uIcc_of_le t.coe_nonneg] at hx
    simp only [hmemT x hx]
  · -- the force points
    funext j
    rw [Prod.snd_add, Prod.snd_add, Prod.fst_add, Prod.fst_add, snd_integral hint, fst_integral hint2]
    simp only [Yc, cT, timeDir, Pi.add_apply, integral_zero, zero_add]
    ring
  · -- `Im log f_t'(z)`
    rw [Prod.snd_add, Prod.snd_add, Prod.snd_add, Prod.snd_add, snd_integral hint, snd_integral hint2]
    simp only [Yc, cT, timeDir, add_zero]
    rw [ℓK_zero hWc hz, zero_add, setIntegral_clk_eq_intervalIntegral, ℓK_of_lt hz ht,
      im_logDerivFwd_eq_integral hr t.coe_nonneg hzt]
    refine intervalIntegral.integral_congr fun x hx => ?_
    rw [uIcc_of_le t.coe_nonneg] at hx
    simp only [hmemT x hx]

omit [Fintype ι] [DecidableEq ι] in
/-- **The bracket `A` as a time integral** (the input `hA` of the mixed Itô formula). -/
theorem Aexp_eq_sum_integral (hWc : Continuous (W · ω)) (hz : z ∈ H)
    (hU : ∀ ω j, Monotone fun t => ε j * V j t ω) (hVc' : ∀ ω j, Continuous (V j · ω)) (e : ι ≃ Fin n)
    {t : ℝ≥0} (ht : t ∈ befSw W z ω) :
    Aexp W z t ω = ∑ k, ∫ u in Ioc 0 t, aF W z n k u ω ∂(Uf V ε hU hVc' e k ω).measure := by
  rw [Fin.sum_univ_succ]
  simp only [aF, Uf, Fin.cases_zero, Fin.cases_succ, integral_zero, Finset.sum_const_zero, add_zero]
  rw [setIntegral_clk_eq_intervalIntegral, Aexp,
    log_conformalRadius_eq_integral (continuous_rpath' hWc) t.coe_nonneg
      (Certify2426.mem_diff_fwdHull_of_lt_swallowTime hz ht)]
  refine intervalIntegral.integral_congr fun x hx => ?_
  rw [uIcc_of_le t.coe_nonneg] at hx
  simp only [aT, fK_toNNReal_of_mem_Icc hz ht hx]

/-- The mean `𝔥_t(z)` at one sample, in the form (2.5): `(2/√κ)(c − arg f − ½ ∑ ρⱼ arg (g − vʲ)) − χ ℓ`. -/
def IsMeanFormula (κ c : ℝ) (ρ : ι → ℝ) (W : ℝ≥0 → Ω → ℝ) (V : ι → ℝ≥0 → Ω → ℝ) (z : ℂ)
    (X : ℝ≥0 → Ω → ℝ) (ω : Ω) (t : ℝ≥0) : Prop :=
  X t ω = 2 / Real.sqrt κ * (c - Complex.arg (QuantumZipper.fwdMap (rpath (W · ω)) t z)
    - 1 / 2 * ∑ j, ρ j * Complex.arg (QuantumZipper.fwdMap (rpath (W · ω)) t z + (W t ω : ℂ) - (V j t ω : ℂ)))
    - QuantumZipper.chiC κ * (QuantumZipper.logDerivFwd (rpath (W · ω)) t z).im

variable {κ c : ℝ} {ρ : ι → ℝ} {X : ℝ≥0 → Ω → ℝ}

omit [Fintype ι] [DecidableEq ι] in
theorem Yc_fst_sub (hz : z ∈ H) {t : ℝ≥0} (ht : t ∈ befSw W z ω) :
    (Yc W V z t ω, X t ω).1.1 - (W t ω : ℂ) = QuantumZipper.fwdMap (rpath (W · ω)) t z := by
  simp only [Yc, fK_of_lt hz ht, add_sub_cancel_right]

omit [DecidableEq ι] in
/-- **At the state, `Θ = arg f_t(z)`**. -/
theorem ang_Yc (hκ : 0 < κ) (hz : z ∈ H) {t : ℝ≥0} (ht : t ∈ befSw W z ω)
    (hX : IsMeanFormula κ c ρ W V z X ω t) :
    ang κ c ρ (Yc W V z t ω, X t ω) = Complex.arg ((Yc W V z t ω, X t ω).1.1 - (W t ω : ℂ)) := by
  rw [Yc_fst_sub hz ht]
  have hsk : Real.sqrt κ ≠ 0 := (Real.sqrt_pos.2 hκ).ne'
  simp only [ang, Yc, fK_of_lt hz ht, ℓK_of_lt hz ht]
  rw [hX]
  field_simp
  ring

omit [DecidableEq ι] in
theorem mem_dom_Yc (hκ : 0 < κ) (hWc : Continuous (W · ω)) (hz : z ∈ H) {t : ℝ≥0} (ht : t ∈ befSw W z ω)
    (hX : IsMeanFormula κ c ρ W V z X ω t) : (Yc W V z t ω, X t ω) ∈ dom κ c ρ := by
  have hpos : 0 < (QuantumZipper.fwdMap (rpath (W · ω)) t z).im := im_fwdMap_pos_of_lt hWc hz ht
  have him : 0 < (Yc W V z t ω, X t ω).1.1.im := by
    simp only [Yc, fK_of_lt hz ht, Complex.add_im, Complex.ofReal_im, add_zero]
    exact hpos
  refine ⟨him, ?_, ?_⟩
  · rw [ang_Yc hκ hz ht hX, Yc_fst_sub hz ht]
    refine lt_of_le_of_ne (Complex.arg_nonneg_iff.2 hpos.le) fun h => ?_
    have := (Complex.arg_eq_zero_iff.1 h.symm).2
    exact hpos.ne' this
  · rw [ang_Yc hκ hz ht hX, Yc_fst_sub hz ht]
    exact Complex.arg_lt_pi_iff.2 (Or.inr hpos.ne')

omit [DecidableEq ι] in
/-- **At the state, `drvF = W`**. -/
theorem drvF_Yc (hκ : 0 < κ) (hWc : Continuous (W · ω)) (hz : z ∈ H) {t : ℝ≥0} (ht : t ∈ befSw W z ω)
    (hX : IsMeanFormula κ c ρ W V z X ω t) : drvF κ c ρ (Yc W V z t ω, X t ω) = W t ω := by
  have hd := mem_dom_Yc hκ hWc hz ht hX
  unfold drvF
  rw [cot_ang_of_state hd.1 (ang_Yc hκ hz ht hX)]
  have hb : (Yc W V z t ω, X t ω).1.1.im ≠ 0 := hd.1.ne'
  field_simp
  simp only [Yc, Complex.add_re, Complex.ofReal_re]
  ring

omit [Fintype ι] [DecidableEq ι] in
theorem continuousOn_phiF (hWc : Continuous (W · ω)) (hVc : ∀ j, Continuous (V j · ω)) (hz : z ∈ H) (j : ι) :
    ContinuousOn (fun u => phiF ρ (Yc W V z u ω, X u ω) (W u ω) j) (befSw W z ω) := by
  have hY := continuousOn_Yc (V := V) hWc hVc hz
  have h1 : ContinuousOn (fun u => (Yc W V z u ω).1) (befSw W z ω) := continuous_fst.comp_continuousOn hY
  have hnum : ContinuousOn (fun u => 1 / 2 * ρ j * ((V j u ω - W u ω) - 2 * ((Yc W V z u ω).1.re - W u ω)))
      (befSw W z ω) :=
    continuousOn_const.mul ((((hVc j).sub hWc).continuousOn).sub (continuousOn_const.mul
      ((Complex.continuous_re.comp_continuousOn h1).sub hWc.continuousOn)))
  have hden : ContinuousOn (fun u => Complex.normSq ((Yc W V z u ω).1 - (V j u ω : ℂ))) (befSw W z ω) :=
    Complex.continuous_normSq.comp_continuousOn (h1.sub (Complex.continuous_ofReal.comp (hVc j)).continuousOn)
  refine (hnum.div hden fun u hu => ?_).congr fun u _ => rfl
  refine (normSq_pos_of_im_pos ?_ (V j u ω)).ne'
  simp only [Yc, Complex.add_im, Complex.ofReal_im, add_zero]
  exact im_fK_pos hWc hz hu

/-- **The drift of the residual**: `∑ₖ ∫_{(0,t]} driftDensityₖ dUₖ = −½ ∑ ρⱼ (Vʲ_t − Vʲ_0)` ("`dC = 0`"). -/
theorem drift_sum_eq (hκ : 0 < κ) (hWc : Continuous (W · ω)) (hz : z ∈ H) (hε : ∀ j, ε j * ε j = 1)
    (hU : ∀ ω j, Monotone fun t => ε j * V j t ω) (hVc' : ∀ ω j, Continuous (V j · ω))
    (hsign : ∀ j u, 0 ≤ ε j * (V j u ω - W u ω)) (hpath : ∀ j, MartChar.IsForcePath (W · ω) (V j · ω))
    (e : ι ≃ Fin n) {t : ℝ≥0} (ht : t ∈ befSw W z ω) (hX : ∀ u ≤ t, IsMeanFormula κ c ρ W V z X ω u) :
    ∑ k, ∫ u in Ioc 0 t, Gm2.driftDensity (drvF κ c ρ) (Yc W V z) X (cF W z ε e) (aF W z n) k u ω
        ∂(Uf V ε hU hVc' e k ω).measure = -(1 / 2) * ∑ j, ρ j * (V j t ω - V j 0 ω) := by
  have hVc : ∀ j, Continuous (V j · ω) := fun j => hVc' ω j
  set φ : ι → ℝ≥0 → ℝ := fun j u => phiF ρ (Yc W V z u ω, X u ω) (W u ω) j with hφ
  have hφc : ∀ j, ContinuousOn (φ j) (Icc 0 t) := fun j =>
    (continuousOn_phiF hWc hVc hz j).mono (Icc_subset_befSw ht)
  have hmem : ∀ u ∈ Ioc 0 t, u ∈ befSw W z ω ∧ IsMeanFormula κ c ρ W V z X ω u := fun u hu =>
    ⟨befSw_mono hu.2 ht, hX u hu.2⟩
  rw [Fin.sum_univ_succ]
  simp only [Gm2.driftDensity, cF, aF, Uf, Fin.cases_zero, Fin.cases_succ, mul_zero, add_zero]
  -- the time term
  have htime : ∫ u in Ioc 0 t, (partialFst (drvF κ c ρ) (Yc W V z u ω, X u ω) (cT W z u ω) +
      1 / 2 * partialSndSnd (drvF κ c ρ) (Yc W V z u ω, X u ω) * aT W z u ω) ∂clk.measure =
      -2 * ∑ j, ∫ u in Ioc 0 t, φ j u ∂clk.measure := by
    rw [← integral_finsetSum _ fun j _ => integrableOn_Ioc_of_continuousOn clk (hφc j),
      ← integral_const_mul]
    refine setIntegral_congr_fun measurableSet_Ioc fun u hu => ?_
    obtain ⟨hu1, hu2⟩ := hmem u hu
    have hd := mem_dom_Yc hκ hWc hz hu1 hu2
    have hst := ang_Yc hκ hz hu1 hu2
    have h0 := timeDensity_add_eq_zero hκ hd hst
    have hcT : cT (ι := ι) W z u ω = timeDir ι ((Yc W V z u ω, X u ω).1.1 - (W u ω : ℂ)) := by
      simp only [cT, Yc, add_sub_cancel_right]
    have haT : aT W z u ω = 4 * ((Yc W V z u ω, X u ω).1.1 - (W u ω : ℂ)).im ^ 2 /
        ‖(Yc W V z u ω, X u ω).1.1 - (W u ω : ℂ)‖ ^ 4 := by
      simp only [aT, Yc, add_sub_cancel_right]
    rw [hcT, haT]
    simp only [hφ]
    linarith
  -- the force terms
  have hforce : ∀ j, ∫ u in Ioc 0 t, partialFst (drvF κ c ρ) (Yc W V z u ω, X u ω) (ε j • forceDir j)
      ∂(stj (fun t => ε j * V j t ω) (hU ω j) (continuous_mul_path (hVc' ω j))).measure =
      -(1 / 2) * (ρ j * (V j t ω - V j 0 ω)) + 2 * ∫ u in Ioc 0 t, φ j u ∂clk.measure := by
    intro j
    set A := stj (fun t => ε j * V j t ω) (hU ω j) (continuous_mul_path (hVc' ω j)) with hA
    have hg : ContinuousOn (fun u => ε j * (V j u ω - W u ω) * φ j u) (Icc 0 t) :=
      (continuousOn_const.mul (((hVc j).sub hWc).continuousOn)).mul (hφc j)
    have e1 : ∫ u in Ioc 0 t, partialFst (drvF κ c ρ) (Yc W V z u ω, X u ω) (ε j • forceDir j) ∂A.measure =
        ∫ u in Ioc 0 t, (ε j * (-(1 / 2) * ρ j) + ε j * (V j u ω - W u ω) * φ j u) ∂A.measure := by
      refine setIntegral_congr_fun measurableSet_Ioc fun u hu => ?_
      obtain ⟨hu1, hu2⟩ := hmem u hu
      rw [ContinuousLinearMap.map_smul, partialFst_forceDir_drvF (mem_dom_Yc hκ hWc hz hu1 hu2)
        (ang_Yc hκ hz hu1 hu2) j, smul_eq_mul]
      simp only [hφ, Yc]
      ring
    rw [e1, integral_add (integrableOn_Ioc_of_continuousOn A continuousOn_const)
      (integrableOn_Ioc_of_continuousOn A hg), setIntegral_const,
      Ito.Gen.stieltjes_measureReal_Ioc _ (zero_le : (0 : ℝ≥0) ≤ t),
      setIntegral_gap_mul_eq hWc (hpath j) (hε j) (hU ω j) (fun u => hsign j u) (φ j) t]
    simp only [hA, stj_apply, smul_eq_mul]
    linear_combination (-(1 / 2) * ρ j * (V j t ω - V j 0 ω)) * hε j
  rw [htime, e.symm.sum_comp (fun j => ∫ u in Ioc 0 t, partialFst (drvF κ c ρ) (Yc W V z u ω, X u ω)
    (ε j • forceDir j) ∂(stj (fun t => ε j * V j t ω) (hU ω j) (continuous_mul_path (hVc' ω j))).measure)]
  simp only [hforce, Finset.sum_add_distrib, ← Finset.mul_sum]
  ring

omit [DecidableEq ι] in
/-- **The bracket of the residual is `κ t`** ("`dQ = κ dt`"). -/
theorem bracket_sum_eq (hκ : 0 < κ) (hWc : Continuous (W · ω)) (hz : z ∈ H)
    (hU : ∀ ω j, Monotone fun t => ε j * V j t ω) (hVc' : ∀ ω j, Continuous (V j · ω))
    (e : ι ≃ Fin n) {t : ℝ≥0} (ht : t ∈ befSw W z ω) (hX : ∀ u ≤ t, IsMeanFormula κ c ρ W V z X ω u) :
    ∑ k, ∫ u in Ioc 0 t, partialSnd (drvF κ c ρ) (Yc W V z u ω, X u ω) ^ 2 * aF W z n k u ω
        ∂(Uf V ε hU hVc' e k ω).measure = κ * t := by
  rw [Fin.sum_univ_succ]
  simp only [aF, Uf, Fin.cases_zero, Fin.cases_succ, mul_zero, integral_zero, Finset.sum_const_zero,
    add_zero]
  have e1 : ∫ u in Ioc 0 t, partialSnd (drvF κ c ρ) (Yc W V z u ω, X u ω) ^ 2 * aT W z u ω ∂clk.measure =
      ∫ _ in Ioc 0 t, κ ∂clk.measure := by
    refine setIntegral_congr_fun measurableSet_Ioc fun u hu => ?_
    have hu1 : u ∈ befSw W z ω := befSw_mono hu.2 ht
    have hu2 := hX u hu.2
    have h := partialSnd_drvF_sq_mul hκ (mem_dom_Yc hκ hWc hz hu1 hu2) (ang_Yc hκ hz hu1 hu2)
    have hf : (Yc W V z u ω, X u ω).1.1 - (W u ω : ℂ) = fK W z u ω := by
      simp only [Yc, add_sub_cancel_right]
    rw [hf] at h
    simpa only [aT] using h
  rw [e1, setIntegral_const, Ito.Gen.stieltjes_measureReal_Ioc _ (zero_le : (0 : ℝ≥0) ≤ t), smul_eq_mul]
  simp
  ring

omit [DecidableEq ι] in
/-- The mean formula is continuous before `τ_z`. -/
theorem continuousOn_meanFormula (hWc : Continuous (W · ω)) (hVc : ∀ j, Continuous (V j · ω)) (hz : z ∈ H) :
    ContinuousOn (fun t : ℝ≥0 => 2 / Real.sqrt κ * (c - Complex.arg (QuantumZipper.fwdMap (rpath (W · ω)) t z)
      - 1 / 2 * ∑ j, ρ j * Complex.arg (QuantumZipper.fwdMap (rpath (W · ω)) t z + (W t ω : ℂ) - (V j t ω : ℂ)))
      - QuantumZipper.chiC κ * (QuantumZipper.logDerivFwd (rpath (W · ω)) t z).im) (befSw W z ω) := by
  have hf := continuousOn_fwdMap_befSw hWc hz
  have hpos : ∀ t ∈ befSw W z ω, 0 < (QuantumZipper.fwdMap (rpath (W · ω)) t z).im := fun t ht =>
    im_fwdMap_pos_of_lt hWc hz ht
  have harg : ContinuousOn (fun t : ℝ≥0 => Complex.arg (QuantumZipper.fwdMap (rpath (W · ω)) t z))
      (befSw W z ω) := fun t ht =>
    (Complex.continuousAt_arg (mem_slitPlane_of_im_pos (hpos t ht))).comp_continuousWithinAt
      (f := fun t : ℝ≥0 => QuantumZipper.fwdMap (rpath (W · ω)) t z) (hf t ht)
  have hargj : ∀ j, ContinuousOn (fun t : ℝ≥0 => Complex.arg (QuantumZipper.fwdMap (rpath (W · ω)) t z +
      (W t ω : ℂ) - (V j t ω : ℂ))) (befSw W z ω) := by
    intro j t ht
    have hc : ContinuousWithinAt (fun t : ℝ≥0 => QuantumZipper.fwdMap (rpath (W · ω)) t z + (W t ω : ℂ) -
        (V j t ω : ℂ)) (befSw W z ω) t :=
      ((hf t ht).add (Complex.continuous_ofReal.comp hWc).continuousWithinAt).sub
        (Complex.continuous_ofReal.comp (hVc j)).continuousWithinAt
    refine (Complex.continuousAt_arg (mem_slitPlane_of_im_pos ?_)).comp_continuousWithinAt hc
    simp only [Complex.sub_im, Complex.add_im, Complex.ofReal_im, add_zero, sub_zero]
    exact hpos t ht
  have hℓ : ContinuousOn (fun t : ℝ≥0 => (QuantumZipper.logDerivFwd (rpath (W · ω)) t z).im) (befSw W z ω) :=
    Complex.continuous_im.comp_continuousOn (continuousOn_logDerivFwd_befSw hWc hz)
  exact (continuousOn_const.mul ((continuousOn_const.sub harg).sub (continuousOn_const.mul
    (continuousOn_finsetSum _ fun j _ => continuousOn_const.mul (hargj j))))).sub (continuousOn_const.mul hℓ)

end Sample


/-! ### The one-point semimartingale theorem -/

section Main

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} {𝓖 : Filtration ℝ≥0 mΩ}
  {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- **Theorem 2.6's one-point semimartingale argument.** Let `W` be a continuous adapted driver from `0`, `Vʲ`
continuous adapted force paths (`IsForcePath`) of direction `εⱼ = ±1` on the correct side of the driver, and let
`X = 𝔥(z)` be given by (2.5) before `ζ ≤ τ_z`. If `X` and `X² − A` (`A_t = log (crad(ℍ, z)/crad(ℍ ∖ K_t, z))`, explicit
form `Aexp`) are continuous local martingales before `ζ`, then so are `M = W − W₀ + ½ ∑ ρⱼ (Vʲ − Vʲ₀)`
(`MartChar.martProc`) and `M² − κ t`. -/
theorem isCLMBefore_martProc_of_onePoint [IsProbabilityMeasure P] {κ c : ℝ} (hκ : 0 < κ) {ρ : ι → ℝ}
    {ε : ι → ℝ} (hε : ∀ j, ε j * ε j = 1) {W : ℝ≥0 → Ω → ℝ} {V : ι → ℝ≥0 → Ω → ℝ}
    (hWc : ∀ ω, Continuous (W · ω)) (hWa : StronglyAdapted 𝓖 W)
    (hVc : ∀ ω j, Continuous (V j · ω)) (hVa : ∀ j, StronglyAdapted 𝓖 (V j))
    (hU : ∀ ω j, Monotone fun t => ε j * V j t ω) (hsign : ∀ ω j u, 0 ≤ ε j * (V j u ω - W u ω))
    (hpath : ∀ ω j, MartChar.IsForcePath (W · ω) (V j · ω))
    {z : ℂ} (hz : z ∈ H) {ζ : Ω → WithTop ℝ≥0}
    (hζ : ∀ ω (t : ℝ≥0), (t : WithTop ℝ≥0) < ζ ω → t ∈ befSw W z ω)
    {X : ℝ≥0 → Ω → ℝ} (hXf : ∀ ω (t : ℝ≥0), (t : WithTop ℝ≥0) < ζ ω → IsMeanFormula κ c ρ W V z X ω t)
    (hX : IsContLocalMartingaleBefore 𝓖 P ζ X)
    (hXA : IsContLocalMartingaleBefore 𝓖 P ζ (fun t ω => X t ω ^ 2 - Aexp W z t ω)) :
    IsContLocalMartingaleBefore 𝓖 P ζ (MartChar.martProc ρ W V) ∧
      IsContLocalMartingaleBefore 𝓖 P ζ (fun t ω => MartChar.martProc ρ W V t ω ^ 2 - κ * t) := by
  set e : ι ≃ Fin (Fintype.card ι) := Fintype.equivFin ι with he
  have hdown : ∀ ω (t : ℝ≥0), (t : WithTop ℝ≥0) < ζ ω → ∀ u ≤ t, (u : WithTop ℝ≥0) < ζ ω :=
    fun ω t ht u hu => lt_of_le_of_lt (WithTop.coe_le_coe.2 hu) ht
  have hXf' : ∀ ω (t : ℝ≥0), (t : WithTop ℝ≥0) < ζ ω → ∀ u ≤ t, IsMeanFormula κ c ρ W V z X ω u :=
    fun ω t ht u hu => hXf ω u (hdown ω t ht u hu)
  have hS : ∀ ω, {t : ℝ≥0 | (t : WithTop ℝ≥0) < ζ ω} ⊆ befSw W z ω := fun ω t ht => hζ ω t ht
  -- the inputs of the mixed Itô formula
  have hXc : ∀ ω, ContinuousOn (X · ω) {t | (t : WithTop ℝ≥0) < ζ ω} := fun ω =>
    ((continuousOn_meanFormula (κ := κ) (c := c) (ρ := ρ) (hWc ω) (fun j => hVc ω j) hz).mono (hS ω)).congr
      fun t ht => hXf ω t ht
  have hYc : ∀ ω, ContinuousOn (Yc W V z · ω) {t | (t : WithTop ℝ≥0) < ζ ω} := fun ω =>
    (continuousOn_Yc (hWc ω) (fun j => hVc ω j) hz).mono (hS ω)
  have hcc : ∀ k ω, ContinuousOn (cF W z ε e k · ω) {t | (t : WithTop ℝ≥0) < ζ ω} := by
    intro k ω
    refine Fin.cases ?_ (fun i => ?_) k
    · exact (continuousOn_cT (hWc ω) hz).mono (hS ω)
    · exact continuousOn_const
  have hac : ∀ k ω, ContinuousOn (aF W z (Fintype.card ι) k · ω) {t | (t : WithTop ℝ≥0) < ζ ω} := by
    intro k ω
    refine Fin.cases ?_ (fun i => ?_) k
    · exact (continuousOn_aT (hWc ω) hz).mono (hS ω)
    · exact continuousOn_const
  have ha0 : ∀ k ω (u : ℝ≥0), (u : WithTop ℝ≥0) < ζ ω → 0 ≤ aF W z (Fintype.card ι) k u ω := by
    intro k ω u _
    refine Fin.cases ?_ (fun i => ?_) k
    · simp only [aF, Fin.cases_zero, aT]; positivity
    · simp [aF]
  have hUc : ∀ k ω, Continuous (Uf V ε hU hVc e k ω) := by
    intro k ω
    refine Fin.cases ?_ (fun i => ?_) k
    · show Continuous fun t => (Ito.GenCont.clockPath id monotone_id continuous_id t : ℝ)
      simp only [Ito.GenCont.clockPath_apply, id]
      exact NNReal.continuous_coe
    · show Continuous fun t => (stj (fun t => ε (e.symm i) * V (e.symm i) t ω) (hU ω _)
        (continuous_mul_path (hVc ω _)) t : ℝ)
      simp only [stj_apply]
      exact continuous_mul_path (hVc ω _)
  have hY : ∀ ω (t : ℝ≥0), (t : WithTop ℝ≥0) < ζ ω → Yc W V z t ω = Yc W V z 0 ω +
      ∑ k, ∫ u in Ioc 0 t, cF W z ε e k u ω ∂(Uf V ε hU hVc e k ω).measure := fun ω t ht =>
    Yc_eq_add_sum_integral (hWc ω) hz hε hU hVc e (hζ ω t ht)
  have hA : ∀ ω (t : ℝ≥0), (t : WithTop ℝ≥0) < ζ ω →
      Aexp W z t ω = ∑ k, ∫ u in Ioc 0 t, aF W z (Fintype.card ι) k u ω ∂(Uf V ε hU hVc e k ω).measure :=
    fun ω t ht => Aexp_eq_sum_integral (hWc ω) hz hU hVc e (hζ ω t ht)
  have hO : ∀ ω (t : ℝ≥0), (t : WithTop ℝ≥0) < ζ ω → (Yc W V z t ω, X t ω) ∈ dom κ c ρ := fun ω t ht =>
    mem_dom_Yc hκ (hWc ω) hz (hζ ω t ht) (hXf ω t ht)
  have hYa : ∀ t, Measurable[𝓖 t] (Yc W V z t) := fun t => measurable_Yc hWa hWc hVa hz t
  have hca : ∀ k t, Measurable[𝓖 t] (cF W z ε e k t) := by
    intro k t
    refine Fin.cases ?_ (fun i => ?_) k
    · exact measurable_cT hWa hWc hz t
    · exact measurable_const
  have haa : ∀ k t, Measurable[𝓖 t] (aF W z (Fintype.card ι) k t) := by
    intro k t
    refine Fin.cases ?_ (fun i => ?_) k
    · exact measurable_aT hWa hWc hz t
    · exact measurable_const
  have hUa : ∀ k t, Measurable[𝓖 t] fun ω => Uf V ε hU hVc e k ω t := by
    intro k t
    refine Fin.cases ?_ (fun i => ?_) k
    · exact measurable_const
    · show Measurable[𝓖 t] fun ω => ε (e.symm i) * V (e.symm i) t ω
      exact (hVa (e.symm i) t).measurable.const_mul _
  obtain ⟨h1, h2⟩ := Gm2.isCLMBefore_residual_and_bracket (P := P) (𝓕 := 𝓖) (F := drvF κ c ρ)
    (O := dom κ c ρ) (ζ := ζ) (X := X) (A := Aexp W z) (Y := Yc W V z) (U := Uf V ε hU hVc e)
    (c := cF W z ε e) (a := aF W z (Fintype.card ι)) (isOpen_dom κ c ρ) (contDiffOn_drvF κ c ρ) hX hXA hXc
    hYc hcc hac ha0 hUc hY hA hO hYa hca haa hUa
  -- the residual is `martProc`, the bracket is `κ t`
  have hres : ∀ ω (t : ℝ≥0), (t : WithTop ℝ≥0) < ζ ω →
      Gm2.residual (drvF κ c ρ) (Yc W V z) X (Uf V ε hU hVc e) (cF W z ε e) (aF W z (Fintype.card ι)) t ω =
        MartChar.martProc ρ W V t ω := by
    intro ω t ht
    have h0 : ((0 : ℝ≥0) : WithTop ℝ≥0) < ζ ω := hdown ω t ht 0 (zero_le : (0 : ℝ≥0) ≤ t)
    simp only [Gm2.residual, MartChar.martProc, MartChar.martValue]
    rw [drvF_Yc hκ (hWc ω) hz (hζ ω t ht) (hXf ω t ht), drvF_Yc hκ (hWc ω) hz (hζ ω 0 h0) (hXf ω 0 h0),
      drift_sum_eq hκ (hWc ω) hz hε hU hVc (fun j u => hsign ω j u) (fun j => hpath ω j) e (hζ ω t ht)
        (hXf' ω t ht)]
    ring
  have hbr : ∀ ω (t : ℝ≥0), (t : WithTop ℝ≥0) < ζ ω →
      Gm2.bracket (drvF κ c ρ) (Yc W V z) X (Uf V ε hU hVc e) (aF W z (Fintype.card ι)) t ω = κ * t :=
    fun ω t ht => bracket_sum_eq hκ (hWc ω) hz hU hVc e (hζ ω t ht) (hXf' ω t ht)
  refine ⟨(Certify2426.isContLocalMartingaleBefore_congr hres).1 h1,
    (Certify2426.isContLocalMartingaleBefore_congr fun ω t ht => ?_).1 h2⟩
  simp only [hres ω t ht, hbr ω t ht]

end Main

end InteractingSLE.Sec2.T26Pv
