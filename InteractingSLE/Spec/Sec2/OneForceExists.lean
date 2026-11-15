/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec2.OneForceLip
import InteractingSLE.Stochastic.Bessel.Existence
import QuantumZipper.Proofs.ItoLite.Dynkin
import InteractingSLE.Frozen.Spec.IsIntegratedSLEEvolution

/-!
# One force point: existence of the evolution (the Bessel construction (2.3))

Packet PROVE-SEC2-ONE. Specification p. 19 ((2.2)–(2.3), `source/spec/p001-048.md` L427–L447) and
the first sentence of the proof of Theorem 2.2 (p. 21, L484): from a Brownian motion `B`, the
construction (2.3) is an integrated `SLE_a(ρ)` evolution of Definition 2.1 with one force point,
up to the continuation threshold.

* `oneX c x D`, `oneζ c x D`, `oneJ c x D`: the scalar process `X` (the Bessel process for
  `c > 0`, the killed solution for `c ≤ 0`), its lifetime, and `J_t = ∫₀ᵗ X⁻¹` (written through
  the equation when `c > 0`), driven by a process `D` with continuous paths.
* `ae_one`: almost surely `X` is a killed path with the threshold behaviour of (2.3).
* `measurableSet_one`: `{t < ζ, (X_t, J_t) ∈ A} ∈ 𝓕_t` (adaptedness before the lifetime).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped NNReal ENNReal

namespace InteractingSLE

namespace OneForce

/-! ### A measurable event for continuous processes -/

/-- For a process with continuous paths on `[0, t]` and measurable values there, "stays above `ε`
on `[0, t]`" is a measurable event. -/
theorem measurableSet_forall_Icc_lt {α : Type*} {mα : MeasurableSpace α} {Y : ℝ → α → ℝ}
    {t : ℝ} (ht : 0 ≤ t) (hYm : ∀ s ∈ Icc (0 : ℝ) t, Measurable (Y s))
    (hYc : ∀ ω, ContinuousOn (Y · ω) (Icc 0 t)) (ε : ℝ) :
    MeasurableSet {ω | ∀ s ∈ Icc (0 : ℝ) t, ε < Y s ω} := by
  have : Nonempty (Icc (0 : ℝ) t) := ⟨⟨0, le_rfl, ht⟩⟩
  obtain ⟨D, hDc, hDd⟩ := TopologicalSpace.exists_countable_dense (Icc (0 : ℝ) t)
  have : Countable D := hDc.to_subtype
  have heq : {ω | ∀ s ∈ Icc (0 : ℝ) t, ε < Y s ω}
      = ⋃ k : ℕ, ⋂ d : D, {ω | ε + 1 / ((k : ℝ) + 1) ≤ Y ((d : Icc (0 : ℝ) t) : ℝ) ω} := by
    ext ω
    simp only [mem_ofPred_eq, mem_iUnion, mem_iInter]
    constructor
    · intro h
      obtain ⟨s₀, hs₀, hmin⟩ := isCompact_Icc.exists_isMinOn (nonempty_Icc.2 ht) (hYc ω)
      obtain ⟨k, hk⟩ := exists_nat_one_div_lt (sub_pos.2 (h s₀ hs₀))
      refine ⟨k, fun d => ?_⟩
      have h1 : Y s₀ ω ≤ Y ((d : Icc (0 : ℝ) t) : ℝ) ω := hmin (d : Icc (0 : ℝ) t).2
      linarith
    · rintro ⟨k, hk⟩ s hs
      have hcl : IsClosed {y : Icc (0 : ℝ) t | ε + 1 / ((k : ℝ) + 1) ≤ Y (y : ℝ) ω} :=
        isClosed_le continuous_const (hYc ω).domRestrict
      have hsub : D ⊆ {y : Icc (0 : ℝ) t | ε + 1 / ((k : ℝ) + 1) ≤ Y (y : ℝ) ω} :=
        fun d hd => hk ⟨d, hd⟩
      have hall := hcl.closure_subset_iff.2 hsub
      rw [hDd.closure_eq] at hall
      have h1 : ε + 1 / ((k : ℝ) + 1) ≤ Y s ω := hall (mem_univ ⟨s, hs⟩)
      have h2 : (0 : ℝ) < 1 / ((k : ℝ) + 1) := by positivity
      linarith
  rw [heq]
  exact MeasurableSet.iUnion fun k => MeasurableSet.iInter fun d =>
    measurableSet_le measurable_const (hYm _ (d : Icc (0 : ℝ) t).2)


/-! ### The scalar process -/

variable {Ω : Type*} {mΩ : MeasurableSpace Ω}

/-- The scalar process `X` of (2.3) driven by `D`: the Bessel process for `c > 0`, the killed
solution for `c ≤ 0` and `x > 0`, and the constant `x` (with lifetime `0`) otherwise. -/
def oneX (c x : ℝ) (D : ℝ≥0 → Ω → ℝ) (t : ℝ≥0) (ω : Ω) : ℝ :=
  if 0 < c then Bessel.besselProc c x D t ω
  else if 0 < x then killPath c x (Bessel.realPath D ω) t else x

/-- The lifetime of `oneX`: `∞` for `c > 0`, the first zero for `c ≤ 0` and `x > 0`, and `0`
otherwise. -/
def oneζ (c x : ℝ) (D : ℝ≥0 → Ω → ℝ) (ω : Ω) : ℝ≥0∞ :=
  if 0 < c then ⊤ else if 0 < x then killTime c x (Bessel.realPath D ω) else 0

/-- `J_t = ∫₀ᵗ X⁻¹`, written as `(X_t − x − D_t)/c` when `c > 0` (equal almost surely). -/
def oneJ (c x : ℝ) (D : ℝ≥0 → Ω → ℝ) (t : ℝ≥0) (ω : Ω) : ℝ :=
  if 0 < c then (oneX c x D t ω - x - D t ω) / c
  else ∫ s in (0 : ℝ)..t, (oneX c x D s.toNNReal ω)⁻¹

omit mΩ in
theorem realPath_coe (D : ℝ≥0 → Ω → ℝ) (ω : Ω) :
    (fun t : ℝ≥0 => Bessel.realPath D ω t) = fun t => D t ω := by
  funext t
  simp [Bessel.realPath]

variable {P : Measure Ω} {D : ℝ≥0 → Ω → ℝ} {c x : ℝ}

omit mΩ in
theorem oneX_of_pos (hc : 0 < c) (t : ℝ≥0) (ω : Ω) :
    oneX c x D t ω = Bessel.besselProc c x D t ω := by
  simp [oneX, hc]

omit mΩ in
theorem oneX_of_kill (hc : ¬ 0 < c) (hx : 0 < x) (t : ℝ≥0) (ω : Ω) :
    oneX c x D t ω = killPath c x (Bessel.realPath D ω) t := by
  simp [oneX, hc, hx]

omit mΩ in
theorem oneX_of_zero (hc : ¬ 0 < c) (hx : ¬ 0 < x) (t : ℝ≥0) (ω : Ω) : oneX c x D t ω = x := by
  simp [oneX, hc, hx]

omit mΩ in
theorem oneζ_of_pos (hc : 0 < c) (ω : Ω) : oneζ c x D ω = ⊤ := by
  simp [oneζ, hc]

omit mΩ in
theorem oneζ_of_kill (hc : ¬ 0 < c) (hx : 0 < x) (ω : Ω) :
    oneζ c x D ω = killTime c x (Bessel.realPath D ω) := by
  simp [oneζ, hc, hx]

omit mΩ in
theorem oneζ_of_zero (hc : ¬ 0 < c) (hx : ¬ 0 < x) (ω : Ω) : oneζ c x D ω = 0 := by
  simp [oneζ, hc, hx]

omit mΩ in
theorem oneJ_of_pos (hc : 0 < c) (t : ℝ≥0) (ω : Ω) :
    oneJ c x D t ω = (oneX c x D t ω - x - D t ω) / c := by
  simp [oneJ, hc]

omit mΩ in
theorem oneJ_of_nonpos (hc : ¬ 0 < c) (t : ℝ≥0) (ω : Ω) :
    oneJ c x D t ω = ∫ s in (0 : ℝ)..t, (oneX c x D s.toNNReal ω)⁻¹ := by
  simp [oneJ, hc]

/-- **The scalar process of (2.3) is almost surely a killed path with the threshold behaviour
of Definition 2.1**, and `J = ∫ X⁻¹`. -/
theorem ae_one (hD : IsPreBrownianReal D P) (hDm : ∀ t, Measurable (D t))
    (hDc : ∀ ω, Continuous (D · ω)) (hD0 : ∀ ω, D 0 ω = 0) (hx : 0 ≤ x) :
    ∀ᵐ ω ∂P, IsKilledPath c x (fun t => D t ω) (fun t => oneX c x D t ω) (oneζ c x D ω) ∧
      (c ≤ 0 → ∀ t : ℝ≥0, (t : ℝ≥0∞) < oneζ c x D ω → oneX c x D t ω ≠ 0) ∧
      (oneζ c x D ω = 0 → x = 0 ∧ c ≤ 0) ∧
      (∀ T : ℝ≥0, 0 < T → (T : ℝ≥0∞) = oneζ c x D ω →
        c ≤ 0 ∧ Tendsto (fun t => oneX c x D t ω) (𝓝[<] T) (𝓝 0)) ∧
      ∀ t : ℝ≥0, oneJ c x D t ω = ∫ s in (0 : ℝ)..t, (oneX c x D s.toNNReal ω)⁻¹ := by
  by_cases hc : 0 < c
  · filter_upwards [Bessel.ae_isBesselPath hD hDc hDm hc hx] with ω hω
    have hX : (fun t => oneX c x D t ω) = fun t => Bessel.besselProc c x D t ω :=
      funext fun t => oneX_of_pos hc t ω
    rw [hX, oneζ_of_pos hc]
    refine ⟨hω.isKilledPath (hD0 ω), fun h => absurd h (not_le.2 hc), fun h => absurd h
      ENNReal.top_ne_zero, fun T _ hT => absurd hT ENNReal.coe_ne_top, fun t => ?_⟩
    have heq := hω.2.2.2.2 t
    simp only at heq
    simp only [oneJ_of_pos hc, oneX_of_pos hc]
    rw [heq, integral_div_eq_mul c (fun u => Bessel.besselProc c x D u ω)]
    field_simp
    ring
  · have hc' : c ≤ 0 := not_lt.1 hc
    refine ae_of_all _ fun ω => ?_
    have hw := Bessel.continuous_realPath hDc ω
    have hw0 : Bessel.realPath D ω 0 = 0 := by simp [Bessel.realPath, hD0 ω]
    by_cases hxp : 0 < x
    · have hX : (fun t => oneX c x D t ω) = killPath c x (Bessel.realPath D ω) :=
        funext fun t => oneX_of_kill hc hxp t ω
      have hK := isKilledPath_killPath hc' hxp hw hw0
      rw [realPath_coe] at hK
      refine ⟨by rw [hX, oneζ_of_kill hc hxp]; exact hK, fun _ t ht => ?_, fun h => ?_,
        fun T hT hTζ => ⟨hc', ?_⟩, fun t => oneJ_of_nonpos hc t ω⟩
      · rw [oneζ_of_kill hc hxp] at ht
        rw [oneX_of_kill hc hxp]
        exact (killPath_pos hc' hxp hw ht).ne'
      · rw [oneζ_of_kill hc hxp] at h
        exact absurd h (killTime_pos hxp hc' hw hw0).ne'
      · rw [oneζ_of_kill hc hxp] at hTζ
        rw [hX]
        exact tendsto_killPath hc' hxp hw hw0 hTζ hT
    · have hx0 : x = 0 := le_antisymm (not_lt.1 hxp) hx
      rw [oneζ_of_zero hc hxp]
      refine ⟨⟨oneX_of_zero hc hxp 0 ω, fun t ht => absurd ht ENNReal.not_lt_zero,
        fun t ht => absurd ht ENNReal.not_lt_zero, ?_,
        fun t ht => absurd ht ENNReal.not_lt_zero, fun t ht => absurd ht ENNReal.not_lt_zero⟩,
        fun _ t ht => absurd ht ENNReal.not_lt_zero, fun _ => ⟨hx0, hc'⟩,
        fun T hT hTζ => ?_, fun t => oneJ_of_nonpos hc t ω⟩
      · refine measure_mono_null (fun s hs => ?_) (measure_empty (μ := (volume : Measure ℝ)))
        exact absurd hs.2.1 ENNReal.not_lt_zero
      · exact absurd (ENNReal.coe_eq_zero.1 hTζ) hT.ne'


/-! ### Adaptedness before the lifetime -/

/-- The regularized solutions driven by `D` are adapted. -/
theorem measurable_killSeq (𝓕 : Filtration ℝ≥0 mΩ) (hDad : ∀ t, Measurable[𝓕 t] (D t))
    (hDc : ∀ ω, Continuous (D · ω)) (hc : c ≤ 0) (hx : 0 < x) (n : ℕ) (t : ℝ≥0) :
    Measurable[𝓕 t] (fun ω => killSeq c x (Bessel.realPath D ω) n t) := by
  obtain ⟨⟨K, hK⟩, ⟨M, hM⟩, -⟩ := lipData_regDrift (w := fun _ => (0 : ℝ)) hc
    (killEps_pos hx n) continuous_const
  refine QuantumZipper.Dynkin.measurable_of_integralEq 𝓕 hDad hDc hK
    (fun y => by rw [Real.norm_eq_abs]; exact hM y) (u := x) (e := (1 : ℝ))
    (U := fun t ω => killSeq c x (Bessel.realPath D ω) n t) (fun ω t => ?_)
    (fun ω => continuous_killSeq_coe hc hx (Bessel.continuous_realPath hDc ω) n) t
  rw [killSeq_eq hc hx (Bessel.continuous_realPath hDc ω) n t.coe_nonneg, smul_eq_mul, mul_one]
  have hD : Bessel.realPath D ω t = D t ω := by simp [Bessel.realPath]
  have hI : ∫ s in (0 : ℝ)..t, Bessel.regDrift c (killEps x n)
        (killSeq c x (Bessel.realPath D ω) n s)
      = ∫ s in (0 : ℝ)..t, Bessel.regDrift c (killEps x n)
        (killSeq c x (Bessel.realPath D ω) n (s.toNNReal : ℝ)) := by
    refine intervalIntegral.integral_congr fun s hs => ?_
    rw [uIcc_of_le t.coe_nonneg] at hs
    simp only [Real.coe_toNNReal s hs.1]
  rw [hD, hI]
  ring

/-- The integral `∫₀ᵗ (max (killSeq n) εₙ)⁻¹`, equal to `∫₀ᵗ X⁻¹` while `killSeq n` is alive. -/
def killJ (c x : ℝ) (D : ℝ≥0 → Ω → ℝ) (n : ℕ) (t : ℝ≥0) (ω : Ω) : ℝ :=
  ∫ r in (0 : ℝ)..t,
    (max (killSeq c x (Bessel.realPath D ω) n (r.toNNReal : ℝ)) (killEps x n))⁻¹

theorem measurable_killJ (𝓕 : Filtration ℝ≥0 mΩ) (hDad : ∀ t, Measurable[𝓕 t] (D t))
    (hDc : ∀ ω, Continuous (D · ω)) (hc : c ≤ 0) (hx : 0 < x) (n : ℕ) (t : ℝ≥0) :
    Measurable[𝓕 t] (killJ c x D n t) := by
  have hφ : Continuous fun y : ℝ => (max y (killEps x n))⁻¹ :=
    (continuous_id.max continuous_const).inv₀ fun y =>
      (lt_of_lt_of_le (killEps_pos hx n) (le_max_right _ _)).ne'
  exact QuantumZipper.Dynkin.measurable_integral_adapted 𝓕
    (X := fun t ω => killSeq c x (Bessel.realPath D ω) n t)
    (measurable_killSeq 𝓕 hDad hDc hc hx n)
    (fun ω => continuous_killSeq_coe hc hx (Bessel.continuous_realPath hDc ω) n) hφ t

omit mΩ in
theorem oneJ_eq_killJ (hDc : ∀ ω, Continuous (D · ω)) (hc : ¬ 0 < c) (hx : 0 < x) {n : ℕ}
    {t : ℝ≥0} {ω : Ω} (hn : KillAlive c x (Bessel.realPath D ω) n t) :
    oneJ c x D t ω = killJ c x D n t ω := by
  have hw := Bessel.continuous_realPath hDc ω
  rw [oneJ_of_nonpos hc, killJ]
  refine intervalIntegral.integral_congr fun s hs => ?_
  rw [uIcc_of_le t.coe_nonneg] at hs
  rw [oneX_of_kill hc hx, killPath_eqOn (not_lt.1 hc) hx hw hn hs, Real.coe_toNNReal s hs.1,
    max_eq_left (hn s hs).le]

/-- **Adaptedness before the lifetime**: `{t < ζ, (X_t, J_t, D_t) ∈ A} ∈ 𝓕_t`. -/
theorem measurableSet_one (𝓕 : Filtration ℝ≥0 mΩ) (hDad : ∀ t, Measurable[𝓕 t] (D t))
    (hDc : ∀ ω, Continuous (D · ω)) (t : ℝ≥0) {A : Set (ℝ × ℝ × ℝ)} (hA : MeasurableSet A) :
    MeasurableSet[𝓕 t]
      {ω | (t : ℝ≥0∞) < oneζ c x D ω ∧ (oneX c x D t ω, oneJ c x D t ω, D t ω) ∈ A} := by
  by_cases hc : 0 < c
  · have hXm : Measurable[𝓕 t] (fun ω => oneX c x D t ω) := by
      simp only [oneX_of_pos hc]
      exact Bessel.besselProc_measurable 𝓕 hDad hDc hc t
    have hJm : Measurable[𝓕 t] (fun ω => oneJ c x D t ω) := by
      simp only [oneJ_of_pos hc]
      exact ((hXm.sub measurable_const).sub (hDad t)).div_const c
    have heq : {ω | (t : ℝ≥0∞) < oneζ c x D ω ∧ (oneX c x D t ω, oneJ c x D t ω, D t ω) ∈ A}
        = (fun ω => (oneX c x D t ω, oneJ c x D t ω, D t ω)) ⁻¹' A := by
      ext ω
      simp [oneζ_of_pos hc]
    rw [heq]
    exact (hXm.prodMk (hJm.prodMk (hDad t))) hA
  by_cases hxp : 0 < x
  · have hc' : c ≤ 0 := not_lt.1 hc
    have heq : {ω | (t : ℝ≥0∞) < oneζ c x D ω ∧ (oneX c x D t ω, oneJ c x D t ω, D t ω) ∈ A}
        = ⋃ n : ℕ, ({ω | KillAlive c x (Bessel.realPath D ω) n t} ∩
          (fun ω => (killSeq c x (Bessel.realPath D ω) n t, killJ c x D n t ω, D t ω)) ⁻¹'
            A) := by
      ext ω
      have hw := Bessel.continuous_realPath hDc ω
      simp only [mem_ofPred_eq, mem_iUnion, mem_inter_iff, mem_preimage, oneζ_of_kill hc hxp]
      constructor
      · rintro ⟨ht, hA'⟩
        obtain ⟨n, hn⟩ := (lt_killTime_iff hc' hxp hw).1 ht
        refine ⟨n, hn, ?_⟩
        rwa [oneX_of_kill hc hxp, killPath_eq hc' hxp hw hn, oneJ_eq_killJ hDc hc hxp hn] at hA'
      · rintro ⟨n, hn, hA'⟩
        refine ⟨(lt_killTime_iff hc' hxp hw).2 ⟨n, hn⟩, ?_⟩
        rwa [oneX_of_kill hc hxp, killPath_eq hc' hxp hw hn, oneJ_eq_killJ hDc hc hxp hn]
    rw [heq]
    refine MeasurableSet.iUnion fun n => MeasurableSet.inter ?_ ?_
    · refine measurableSet_forall_Icc_lt (Y := fun s ω => killSeq c x (Bessel.realPath D ω) n s)
        t.coe_nonneg (fun s hs => ?_) (fun ω => (continuousOn_killSeq hc' hxp
          (Bessel.continuous_realPath hDc ω) n).mono fun _ hs => hs.1) _
      have h := measurable_killSeq 𝓕 hDad hDc hc' hxp n s.toNNReal
      rw [Real.coe_toNNReal s hs.1] at h
      exact h.mono (𝓕.mono (Real.toNNReal_le_iff_le_coe.2 hs.2)) le_rfl
    · exact ((measurable_killSeq 𝓕 hDad hDc hc' hxp n t).prodMk
        ((measurable_killJ 𝓕 hDad hDc hc' hxp n t).prodMk (hDad t))) hA
  · have heq : {ω | (t : ℝ≥0∞) < oneζ c x D ω ∧
        (oneX c x D t ω, oneJ c x D t ω, D t ω) ∈ A} = ∅ := by
      ext ω
      simp [oneζ_of_zero hc hxp]
    rw [heq]
    exact @MeasurableSet.empty Ω (𝓕 t)

/-! ### The evolution with one force point -/

theorem div_nonpos_iff_le {a ρ : ℝ} (ha : 0 < a) : (ρ + 2) / a ≤ 0 ↔ ρ ≤ -2 := by
  rw [div_le_iff₀ ha, zero_mul]
  constructor <;> intro h <;> linarith

theorem neg_div_sqrt_eq_zero_iff {a x₀ : ℝ} (ha : 0 < a) : -x₀ / Real.sqrt a = 0 ↔ x₀ = 0 := by
  rw [div_eq_zero_iff, neg_eq_zero, or_iff_left (Real.sqrt_pos.2 ha).ne']

theorem div_sqrt_eq_zero_iff {a x₀ : ℝ} (ha : 0 < a) : x₀ / Real.sqrt a = 0 ↔ x₀ = 0 := by
  rw [div_eq_zero_iff, or_iff_left (Real.sqrt_pos.2 ha).ne']

/-- The force point of (2.3) on the left, as a process: `V_t = x₀ − (2/√a) J_t`. -/
def leftVProc (a x₀ ρ : ℝ) (B : ℝ≥0 → Ω → ℝ) (t : ℝ≥0) (ω : Ω) : ℝ :=
  x₀ - 2 / Real.sqrt a * oneJ ((ρ + 2) / a) (-x₀ / Real.sqrt a) B t ω

/-- The driver of (2.3) with the force point on the left: `W_t = V_t + √a X_t`. -/
def leftWProc (a x₀ ρ : ℝ) (B : ℝ≥0 → Ω → ℝ) (t : ℝ≥0) (ω : Ω) : ℝ :=
  leftVProc a x₀ ρ B t ω + Real.sqrt a * oneX ((ρ + 2) / a) (-x₀ / Real.sqrt a) B t ω

/-- The lifetime of (2.3) with the force point on the left. -/
def leftζ (a x₀ ρ : ℝ) (B : ℝ≥0 → Ω → ℝ) (ω : Ω) : ℝ≥0∞ :=
  oneζ ((ρ + 2) / a) (-x₀ / Real.sqrt a) B ω

/-- The negated driving process, for the force point on the right. -/
def negProc (B : ℝ≥0 → Ω → ℝ) (t : ℝ≥0) (ω : Ω) : ℝ := -B t ω

/-- The force point of (2.3) on the right: `V_t = x₀ + (2/√a) J_t`, `X` driven by `−B`. -/
def rightVProc (a x₀ ρ : ℝ) (B : ℝ≥0 → Ω → ℝ) (t : ℝ≥0) (ω : Ω) : ℝ :=
  x₀ + 2 / Real.sqrt a * oneJ ((ρ + 2) / a) (x₀ / Real.sqrt a) (negProc B) t ω

/-- The driver of (2.3) with the force point on the right: `W_t = V_t − √a X_t`. -/
def rightWProc (a x₀ ρ : ℝ) (B : ℝ≥0 → Ω → ℝ) (t : ℝ≥0) (ω : Ω) : ℝ :=
  rightVProc a x₀ ρ B t ω - Real.sqrt a * oneX ((ρ + 2) / a) (x₀ / Real.sqrt a) (negProc B) t ω

/-- The lifetime of (2.3) with the force point on the right. -/
def rightζ (a x₀ ρ : ℝ) (B : ℝ≥0 → Ω → ℝ) (ω : Ω) : ℝ≥0∞ :=
  oneζ ((ρ + 2) / a) (x₀ / Real.sqrt a) (negProc B) ω

/-- Adaptedness before `ζ` of a continuous function of `(X, J)`. -/
theorem adaptedBefore_of_comp (𝓕 : Filtration ℝ≥0 mΩ) (hDad : ∀ t, Measurable[𝓕 t] (D t))
    (hDc : ∀ ω, Continuous (D · ω)) {g : ℝ × ℝ → ℝ} (hg : Measurable g) {Y : ℝ≥0 → Ω → ℝ}
    (hY : ∀ t ω, Y t ω = g (oneX c x D t ω, oneJ c x D t ω)) :
    AdaptedBefore 𝓕 (oneζ c x D) Y := by
  intro t A hA
  have heq : {ω | (t : ℝ≥0∞) < oneζ c x D ω ∧ Y t ω ∈ A}
      = {ω | (t : ℝ≥0∞) < oneζ c x D ω ∧ (oneX c x D t ω, oneJ c x D t ω, D t ω) ∈
          (fun p : ℝ × ℝ × ℝ => g (p.1, p.2.1)) ⁻¹' A} := by
    ext ω
    simp only [mem_ofPred_eq, mem_preimage, hY]
  rw [heq]
  exact measurableSet_one 𝓕 hDad hDc t ((hg.comp (by fun_prop)) hA)

/-- **Theorem 2.2, one force point on the left, existence (the Bessel construction (2.3))**:
on any filtered probability space carrying a filtered Brownian motion `B` with continuous paths
started at `0`, the processes `leftWProc`, `leftVProc` with lifetime `leftζ` form an integrated
`SLE_a(ρ)` evolution of Definition 2.1 with the single force point `x₀ ≤ 0` (weight `ρ`), up to
its continuation threshold. -/
theorem isIntegratedSLEEvolution_left {a : ℝ} (ha : 0 < a) {xL : Fin 1 → ℝ} {xR : Fin 0 → ℝ}
    {ρL : Fin 1 → ℝ} {ρR : Fin 0 → ℝ} (hxL : xL 0 ≤ 0) {𝓕 : Filtration ℝ≥0 mΩ}
    {B : ℝ≥0 → Ω → ℝ} (hB : IsFilteredBrownianReal 𝓕 B P) (hBc : ∀ ω, Continuous (B · ω))
    (hB0 : ∀ ω, B 0 ω = 0) (VR : Fin 0 → ℝ≥0 → Ω → ℝ) :
    IsIntegratedSLEEvolution a xL xR ρL ρR P 𝓕 (leftWProc a (xL 0) (ρL 0) B)
      (fun _ => leftVProc a (xL 0) (ρL 0) B) VR B (leftζ a (xL 0) (ρL 0) B) := by
  have hr : 0 < Real.sqrt a := Real.sqrt_pos.2 ha
  have hx : 0 ≤ -xL 0 / Real.sqrt a := div_nonneg (neg_nonneg.2 hxL) hr.le
  have hBad : ∀ t, Measurable[𝓕 t] (B t) := fun t => hB.2.1 t
  have hBm : ∀ t, Measurable (B t) := fun t => (hBad t).mono (𝓕.le t) le_rfl
  refine ⟨hB, ?_, fun _ => ?_, fun i => i.elim0, ?_⟩
  · exact adaptedBefore_of_comp 𝓕 hBad hBc
      (g := fun p => xL 0 - 2 / Real.sqrt a * p.2 + Real.sqrt a * p.1) (by fun_prop)
      fun t ω => rfl
  · exact adaptedBefore_of_comp 𝓕 hBad hBc
      (g := fun p => xL 0 - 2 / Real.sqrt a * p.2) (by fun_prop) fun t ω => rfl
  filter_upwards [ae_one (c := (ρL 0 + 2) / a) hB.1.toIsPreBrownianReal hBm hBc hB0 hx]
    with ω ⟨hK, hpos, hζ0, hζT, hJ⟩
  set X : ℝ≥0 → ℝ := fun t => oneX ((ρL 0 + 2) / a) (-xL 0 / Real.sqrt a) B t ω with hXdef
  have hV : (fun t => leftVProc a (xL 0) (ρL 0) B t ω) = leftV a (xL 0) X := by
    funext t
    rw [leftV_eq_sub, leftVProc, hJ t]
  have hW : (fun t => leftWProc a (xL 0) (ρL 0) B t ω) = leftW a (xL 0) X := by
    funext t
    rw [leftW, ← hV]
    rfl
  have key := isIntegratedSLEPath_left ha (xL := xL) (xR := xR) (ρL := ρL) (ρR := ρR) hK
    (fun t ht hρ => hpos ((div_nonpos_iff_le ha).2 hρ) t ht)
    (fun h => ⟨(neg_div_sqrt_eq_zero_iff ha).1 (hζ0 h).1, (div_nonpos_iff_le ha).1 (hζ0 h).2⟩)
    (fun T hT hTζ => ⟨(div_nonpos_iff_le ha).1 (hζT T hT hTζ).1, (hζT T hT hTζ).2⟩)
    (fun i t => VR i t ω)
  rw [← hW, ← hV] at key
  exact key

/-- **Theorem 2.2, one force point on the right, existence (the Bessel construction (2.3))**:
the standard single-force-point `SLE_a(ρ)` with `x₀ ≥ 0`, as in `isIntegratedSLEEvolution_left`
(here `X = (V − W)/√a` is driven by `−B`). -/
theorem isIntegratedSLEEvolution_right {a : ℝ} (ha : 0 < a) {xL : Fin 0 → ℝ} {xR : Fin 1 → ℝ}
    {ρL : Fin 0 → ℝ} {ρR : Fin 1 → ℝ} (hxR : 0 ≤ xR 0) {𝓕 : Filtration ℝ≥0 mΩ}
    {B : ℝ≥0 → Ω → ℝ} (hB : IsFilteredBrownianReal 𝓕 B P) (hBc : ∀ ω, Continuous (B · ω))
    (hB0 : ∀ ω, B 0 ω = 0) (VL : Fin 0 → ℝ≥0 → Ω → ℝ) :
    IsIntegratedSLEEvolution a xL xR ρL ρR P 𝓕 (rightWProc a (xR 0) (ρR 0) B) VL
      (fun _ => rightVProc a (xR 0) (ρR 0) B) B (rightζ a (xR 0) (ρR 0) B) := by
  have hr : 0 < Real.sqrt a := Real.sqrt_pos.2 ha
  have hx : 0 ≤ xR 0 / Real.sqrt a := div_nonneg hxR hr.le
  have hBad : ∀ t, Measurable[𝓕 t] (negProc B t) := fun t => (hB.2.1 t).neg
  have hBm : ∀ t, Measurable (negProc B t) := fun t => (hBad t).mono (𝓕.le t) le_rfl
  have hBc' : ∀ ω, Continuous (negProc B · ω) := fun ω => (hBc ω).neg
  have hB0' : ∀ ω, negProc B 0 ω = 0 := fun ω => by simp [negProc, hB0 ω]
  have hpre : IsPreBrownianReal (negProc B) P := hB.1.toIsPreBrownianReal.neg
  refine ⟨hB, ?_, fun i => i.elim0, fun _ => ?_, ?_⟩
  · exact adaptedBefore_of_comp 𝓕 hBad hBc'
      (g := fun p => xR 0 + 2 / Real.sqrt a * p.2 - Real.sqrt a * p.1) (by fun_prop)
      fun t ω => rfl
  · exact adaptedBefore_of_comp 𝓕 hBad hBc'
      (g := fun p => xR 0 + 2 / Real.sqrt a * p.2) (by fun_prop) fun t ω => rfl
  filter_upwards [ae_one (c := (ρR 0 + 2) / a) hpre hBm hBc' hB0' hx]
    with ω ⟨hK, hpos, hζ0, hζT, hJ⟩
  set X : ℝ≥0 → ℝ := fun t => oneX ((ρR 0 + 2) / a) (xR 0 / Real.sqrt a) (negProc B) t ω
    with hXdef
  have hV : (fun t => rightVProc a (xR 0) (ρR 0) B t ω) = rightV a (xR 0) X := by
    funext t
    rw [rightV_eq_add, rightVProc, hJ t]
  have hW : (fun t => rightWProc a (xR 0) (ρR 0) B t ω) = rightW a (xR 0) X := by
    funext t
    rw [rightW, ← hV]
    rfl
  have key := isIntegratedSLEPath_right ha (xL := xL) (xR := xR) (ρL := ρL) (ρR := ρR)
    (b := fun t => B t ω) hK
    (fun t ht hρ => hpos ((div_nonpos_iff_le ha).2 hρ) t ht)
    (fun h => ⟨(div_sqrt_eq_zero_iff ha).1 (hζ0 h).1, (div_nonpos_iff_le ha).1 (hζ0 h).2⟩)
    (fun T hT hTζ => ⟨(div_nonpos_iff_le ha).1 (hζT T hT hTζ).1, (hζT T hT hTζ).2⟩)
    (fun i t => VL i t ω)
  rw [← hW, ← hV] at key
  exact key

end OneForce

end InteractingSLE
