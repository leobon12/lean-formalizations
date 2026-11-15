/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec2.TwoSeedLawBridge
import InteractingSLE.Spec.Sec2.JacobiLaw
import InteractingSLE.Spec.Sec2.OneForceLaw

/-!
# Two seeds: the killed state as a measurable functional of the angle path

Packet PROVE-SEC2-JAC2. Specification, proof of Theorem 2.2 (`source/spec/p001-048.md`, L546): "Integrating
the force-point equations back from `−∞` recovers exactly `t, L^-, L^+`, and `w` above. This proves uniqueness
in law of `(W, V^L, V^R)`, and the integrated equation determines `B` from this triple."

The angle path `U` (logarithmic clock) lives in the space `CPathR` of continuous real paths on `ℝ` with the
subspace σ-algebra of the product σ-algebra. This file shows

* `measurableSet_killedSet`: for times `t_j` and Borel sets `A_j`, the set of paths `U` for which
  `t_j < Z(U)` and the clock construction `(w, L^-, L^+, b)(u(t_j)) ∈ A_j` for all `j` is measurable; here
  `Z(U) = sup_u t(u)` is the total clock (`totalClock`) and the state is `stateF` (the clock construction of
  `TwoSeedClock`, with `b = κ^{-1/2}(w + ½ρ_L L^- + ½ρ_R L^+)`);
* `map_toCPathR_eq`: two processes solving the Jacobi martingale problem with the same parameters have the
  same law on `CPathR` (finite-dimensional laws from `IsJacobiMP.map_eq`, then uniqueness of projective
  limits);
* `lifetime_eq_totalClock`, `state_eq_stateF`: on a good two-seed path, `ζ = Z(U)` and the state at every
  `t < ζ` is `stateF U t`, `U` the logarithmic-clock angle.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter Topology Real
open scoped NNReal ENNReal

namespace InteractingSLE

namespace Sec2

namespace TwoSeed

/-! ### The path space and the clamped path -/

/-- Continuous real paths indexed by the logarithmic clock, with the subspace σ-algebra of the
product σ-algebra. -/
abbrev CPathR : Type := {f : ℝ → ℝ // Continuous f}

/-- The path clamped to `[0, 1]` (equal to the path for angle paths). -/
def clampU (f : CPathR) (v : ℝ) : ℝ := max 0 (min 1 (f.1 v))

theorem continuous_clampU (f : CPathR) : Continuous (clampU f) :=
  continuous_const.max (continuous_const.min f.2)

theorem clampU_mem (f : CPathR) (v : ℝ) : clampU f v ∈ Icc (0 : ℝ) 1 :=
  ⟨le_max_left _ _, max_le zero_le_one (min_le_left _ _)⟩

theorem clampU_eq {f : CPathR} (h : ∀ v, f.1 v ∈ Icc (0 : ℝ) 1) : clampU f = f.1 := by
  funext v
  simp only [clampU, min_eq_right (h v).2, max_eq_right (h v).1]

theorem measurable_clampU_apply (v : ℝ) : Measurable fun f : CPathR => clampU f v :=
  measurable_const.max (measurable_const.min ((measurable_pi_apply v).comp measurable_subtype_coe))

/-- Joint measurability of a continuous function of time and the clamped path. -/
theorem measurable_uncurry_clampU {F : ℝ → ℝ → ℝ} (hF : Continuous (Function.uncurry F)) :
    Measurable fun p : ℝ × CPathR => F p.1 (clampU p.2 p.1) := by
  have h := measurable_uncurry_of_continuous_of_measurable (u := fun (v : ℝ) (f : CPathR) =>
    F v (clampU f v)) (fun f => hF.comp (continuous_id.prodMk (continuous_clampU f)))
    (fun v => hF.measurable.comp (measurable_const.prodMk (measurable_clampU_apply v)))
  exact h

/-- Integrals of a continuous function of time and the clamped path are measurable in the path. -/
theorem measurable_integral_clampU {F : ℝ → ℝ → ℝ} (hF : Continuous (Function.uncurry F))
    (μ : Measure ℝ) [SFinite μ] : Measurable fun f : CPathR => ∫ v, F v (clampU f v) ∂μ := by
  have h : StronglyMeasurable (Function.uncurry fun (f : CPathR) (v : ℝ) => F v (clampU f v)) :=
    ((measurable_uncurry_clampU hF).comp measurable_swap).stronglyMeasurable
  exact (h.integral_prod_right (ν := μ)).measurable

theorem measurable_clock (u : ℝ) : Measurable fun f : CPathR => clock (clampU f) u := by
  simp only [clock, clockDensity]
  exact measurable_integral_clampU (F := fun v x => exp (2 * v) * (x * (1 - x)) / 2)
    (by fun_prop) _

theorem measurable_lowerL (u : ℝ) : Measurable fun f : CPathR => lowerL (clampU f) u := by
  simp only [lowerL]
  exact (measurable_integral_clampU (F := fun v x => exp v * (1 - x)) (by fun_prop) _).neg

theorem measurable_upperL (u : ℝ) : Measurable fun f : CPathR => upperL (clampU f) u := by
  simp only [upperL]
  exact measurable_integral_clampU (F := fun v x => exp v * x) (by fun_prop) _

theorem measurable_driver (u : ℝ) : Measurable fun f : CPathR => driver (clampU f) u := by
  simp only [driver]
  exact (measurable_lowerL u).add (measurable_const.mul (measurable_clampU_apply u))

/-- Joint measurability of a clock functional that is continuous in time and measurable in the path. -/
theorem measurable_uncurry_of_clock {g : ℝ → CPathR → ℝ} (hc : ∀ f, Continuous fun u => g u f)
    (hm : ∀ u, Measurable (g u)) : Measurable fun p : ℝ × CPathR => g p.1 p.2 :=
  measurable_uncurry_of_continuous_of_measurable hc hm

/-- The inverse clock is measurable in the path, at each positive time. -/
theorem measurable_invClock {t : ℝ} (ht : 0 < t) :
    Measurable fun f : CPathR => invClock (clampU f) t := by
  refine measurable_of_Iic fun c => ?_
  have heq : (fun f : CPathR => invClock (clampU f) t) ⁻¹' Iic c =
      {f | t ≤ clock (clampU f) c} ∪ ({f | ∀ q : ℚ, clock (clampU f) q < t} ∩ {_f | 0 ≤ c}) := by
    ext f
    set U := clampU f
    have hc := continuous_clampU f
    have h01 := clampU_mem f
    obtain ⟨u₀, hu₀⟩ := exists_clock_lt hc h01 ht
    have hbdd : BddBelow {u | t ≤ clock U u} := by
      refine ⟨u₀, fun u hu => le_of_lt (lt_of_not_ge fun h => ?_)⟩
      exact absurd ((show t ≤ clock U u from hu).trans (monotone_clock hc h01 h)) (not_le.2 hu₀)
    simp only [mem_preimage, mem_Iic, mem_union, mem_ofPred_eq, mem_inter_iff]
    constructor
    · intro hle
      by_cases hne : {u | t ≤ clock U u}.Nonempty
      · left
        have hmem : t ≤ clock U (invClock U t) :=
          (isClosed_le continuous_const (continuous_clock hc h01)).csInf_mem hne hbdd
        exact hmem.trans (monotone_clock hc h01 hle)
      · right
        rw [not_nonempty_iff_eq_empty] at hne
        refine ⟨fun q => lt_of_not_ge fun hq => ?_, ?_⟩
        · have : (q : ℝ) ∈ {u | t ≤ clock U u} := hq
          rw [hne] at this; exact this
        · have : invClock U t = 0 := by rw [invClock, hne, Real.sInf_empty]
          rwa [this] at hle
    · rintro (h | ⟨hq, hc0⟩)
      · exact csInf_le hbdd h
      · have hemp : {u | t ≤ clock U u} = ∅ := by
          refine eq_empty_iff_forall_notMem.2 fun u hu => ?_
          obtain ⟨q, hq'⟩ := exists_rat_gt u
          exact absurd ((show t ≤ clock U u from hu).trans (monotone_clock hc h01 hq'.le))
            (not_le.2 (hq q))
        rw [invClock, hemp, Real.sInf_empty]
        exact hc0
  have hall : {f : CPathR | ∀ q : ℚ, clock (clampU f) q < t} =
      ⋂ q : ℚ, {f : CPathR | clock (clampU f) q < t} := by
    ext f; simp only [mem_ofPred_eq, mem_iInter]
  rw [heq, hall]
  exact (measurableSet_le measurable_const (measurable_clock c)).union
    ((MeasurableSet.iInter fun q : ℚ => measurableSet_lt (measurable_clock (q : ℝ)) measurable_const).inter
      (MeasurableSet.const _))

/-- A clock functional evaluated at the inverse clock (`phys`) is measurable in the path. -/
theorem measurable_phys {g : ℝ → CPathR → ℝ} (hc : ∀ f, Continuous fun u => g u f)
    (hm : ∀ u, Measurable (g u)) (t : ℝ) :
    Measurable fun f : CPathR => phys (clampU f) (fun u => g u f) t := by
  rcases le_or_gt t 0 with ht | ht
  · simp only [phys_of_nonpos ht]; exact measurable_const
  · simp only [phys_of_pos ht]
    exact (measurable_uncurry_of_clock hc hm).comp ((measurable_invClock ht).prodMk measurable_id)

theorem measurable_phys_driver (t : ℝ) :
    Measurable fun f : CPathR => phys (clampU f) (driver (clampU f)) t :=
  measurable_phys (g := fun u f => driver (clampU f) u)
    (fun f => continuous_driver (continuous_clampU f) (clampU_mem f)) measurable_driver t

theorem measurable_phys_lowerL (t : ℝ) :
    Measurable fun f : CPathR => phys (clampU f) (lowerL (clampU f)) t :=
  measurable_phys (g := fun u f => lowerL (clampU f) u)
    (fun f => continuous_lowerL (continuous_clampU f) (clampU_mem f)) measurable_lowerL t

theorem measurable_phys_upperL (t : ℝ) :
    Measurable fun f : CPathR => phys (clampU f) (upperL (clampU f)) t :=
  measurable_phys (g := fun u f => upperL (clampU f) u)
    (fun f => continuous_upperL (continuous_clampU f) (clampU_mem f)) measurable_upperL t

/-! ### The total clock, the state functional and the killed set -/

/-- The total clock `Z(U) = sup_u t(u)`: the lifetime of the clock construction. -/
def totalClock (f : CPathR) : ℝ≥0∞ := ⨆ q : ℚ, ENNReal.ofReal (clock (clampU f) q)

theorem measurable_totalClock : Measurable totalClock :=
  Measurable.iSup fun q => ENNReal.measurable_ofReal.comp (measurable_clock q)

/-- The state `(w, L^-, L^+, b)` of the clock construction at physical time `t`. -/
def stateF (κ : ℝ) (ρL ρR : Fin 1 → ℝ) (f : CPathR) (t : ℝ≥0) :
    ℝ × (Fin 1 → ℝ) × (Fin 1 → ℝ) × ℝ :=
  (phys (clampU f) (driver (clampU f)) t, fun _ => phys (clampU f) (lowerL (clampU f)) t,
    fun _ => phys (clampU f) (upperL (clampU f)) t,
    (phys (clampU f) (driver (clampU f)) t + ρL 0 / 2 * phys (clampU f) (lowerL (clampU f)) t +
      ρR 0 / 2 * phys (clampU f) (upperL (clampU f)) t) / Real.sqrt κ)

theorem measurable_stateF (κ : ℝ) (ρL ρR : Fin 1 → ℝ) (t : ℝ≥0) :
    Measurable fun f => stateF κ ρL ρR f t :=
  (measurable_phys_driver t).prodMk ((measurable_pi_iff.2 fun _ => measurable_phys_lowerL t).prodMk
    ((measurable_pi_iff.2 fun _ => measurable_phys_upperL t).prodMk
      ((((measurable_phys_driver t).add (measurable_const.mul (measurable_phys_lowerL t))).add
        (measurable_const.mul (measurable_phys_upperL t))).div_const _)))

/-- The paths whose clock construction is alive at the times `t_j` with state in `A_j`. -/
def killedSet (κ : ℝ) (ρL ρR : Fin 1 → ℝ) {n : ℕ} (ts : Fin n → ℝ≥0)
    (A : Fin n → Set (ℝ × (Fin 1 → ℝ) × (Fin 1 → ℝ) × ℝ)) : Set CPathR :=
  {f | ∀ j, (ts j : ℝ≥0∞) < totalClock f ∧ stateF κ ρL ρR f (ts j) ∈ A j}

theorem measurableSet_killedSet (κ : ℝ) (ρL ρR : Fin 1 → ℝ) {n : ℕ} (ts : Fin n → ℝ≥0)
    {A : Fin n → Set (ℝ × (Fin 1 → ℝ) × (Fin 1 → ℝ) × ℝ)} (hA : ∀ j, MeasurableSet (A j)) :
    MeasurableSet (killedSet κ ρL ρR ts A) := by
  have : killedSet κ ρL ρR ts A = ⋂ j, ({f | (ts j : ℝ≥0∞) < totalClock f} ∩
      (fun f => stateF κ ρL ρR f (ts j)) ⁻¹' A j) := by
    ext f; simp only [killedSet, mem_ofPred_eq, mem_iInter, mem_inter_iff, mem_preimage]
  rw [this]
  exact MeasurableSet.iInter fun j => (measurableSet_lt measurable_const measurable_totalClock).inter
    (measurable_stateF κ ρL ρR (ts j) (hA j))

/-! ### Uniqueness of the path law of a Jacobi martingale-problem solution -/

/-- The path of a process with continuous paths, as an element of `CPathR`. -/
def toCPathR {Ω : Type*} (U : ℝ → Ω → ℝ) (hc : ∀ ω, Continuous fun u => U u ω) (ω : Ω) : CPathR :=
  ⟨fun u => U u ω, hc ω⟩

theorem measurable_toCPathR {Ω : Type*} [MeasurableSpace Ω] {U : ℝ → Ω → ℝ}
    (hm : ∀ u, Measurable (U u)) (hc : ∀ ω, Continuous fun u => U u ω) :
    Measurable (toCPathR U hc) :=
  Measurable.subtype_mk (measurable_pi_iff.2 hm)

/-- **Two solutions of the Jacobi martingale problem have the same law on `CPathR`.** -/
theorem map_toCPathR_eq {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω'] {P : Measure Ω}
    {P' : Measure Ω'} [IsProbabilityMeasure P] [IsProbabilityMeasure P'] {κ a b : ℝ}
    {U : ℝ → Ω → ℝ} {U' : ℝ → Ω' → ℝ} (hU : Jacobi.IsJacobiMP κ a b P U)
    (hU' : Jacobi.IsJacobiMP κ a b P' U') (hκ : 0 ≤ κ) (hab : 0 < a + b) :
    P.map (toCPathR U hU.continuous) = P'.map (toCPathR U' hU'.continuous) := by
  refine QuantumZipper.RS.map_val_injective_rs ?_
  rw [Measure.map_map measurable_subtype_coe (measurable_toCPathR hU.measurable hU.continuous),
    Measure.map_map measurable_subtype_coe (measurable_toCPathR hU'.measurable hU'.continuous)]
  have hX : AEMeasurable (fun ω => fun u => U u ω) P :=
    (measurable_pi_iff.2 hU.measurable).aemeasurable
  have hX' : AEMeasurable (fun ω => fun u => U' u ω) P' :=
    (measurable_pi_iff.2 hU'.measurable).aemeasurable
  have h1 := isProjectiveLimit_map (X := fun u ω => U u ω) hX
  have h2 := isProjectiveLimit_map (X := fun u ω => U' u ω) hX'
  have hfdd : ∀ I : Finset ℝ, P.map (fun ω => I.restrict fun u => U u ω) =
      P'.map (fun ω => I.restrict fun u => U' u ω) := by
    intro I
    set e := I.equivFin
    set t : Fin I.card → ℝ := fun i => (e.symm i : ℝ)
    set φ : (Fin I.card → ℝ) → (I → ℝ) := fun g x => g (e x)
    have hφ : Measurable φ := measurable_pi_iff.2 fun x => measurable_pi_apply (e x)
    have hrw : (fun ω => I.restrict fun u => U u ω) = φ ∘ fun ω i => U (t i) ω := by
      funext ω x
      simp only [Finset.restrict, Function.comp_apply, φ, t, Equiv.symm_apply_apply]
    have hrw' : (fun ω => I.restrict fun u => U' u ω) = φ ∘ fun ω i => U' (t i) ω := by
      funext ω x
      simp only [Finset.restrict, Function.comp_apply, φ, t, Equiv.symm_apply_apply]
    rw [hrw, hrw', ← Measure.map_map hφ (measurable_pi_iff.2 fun i => hU.measurable (t i)),
      ← Measure.map_map hφ (measurable_pi_iff.2 fun i => hU'.measurable (t i)),
      hU.map_eq hU' hκ hab t]
  have h2' : IsProjectiveLimit (P'.map fun ω => fun u => U' u ω)
      (fun I : Finset ℝ => P.map fun ω => I.restrict fun u => U u ω) := by
    intro I
    rw [h2 I]
    exact (hfdd I).symm
  exact h1.unique h2'

/-! ### Pathwise identification on a good two-seed path -/

/-- With a strictly increasing clock, `u(t(u)) = u` without assuming that the clock diverges. -/
theorem invClock_eq_of_clock_eq {U : ℝ → ℝ} (hc : Continuous U) (h01 : ∀ v, U v ∈ Icc (0 : ℝ) 1)
    (hnull : volume {v | U v = 0 ∨ U v = 1} = 0) {u t : ℝ} (ht : clock U u = t) :
    invClock U t = u := by
  have hsm := strictMono_clock hc h01 hnull
  have hl : IsLeast {u' | t ≤ clock U u'} u := by
    refine ⟨ht.ge, fun u' hu' => not_lt.1 fun hlt => ?_⟩
    have h1 : clock U u' < t := ht ▸ hsm hlt
    exact absurd (lt_of_le_of_lt (show t ≤ clock U u' from hu') h1) (lt_irrefl t)
  exact hl.csInf_eq

section PathId

variable {κ : ℝ} {ρL ρR : Fin 1 → ℝ} {w : ℝ≥0 → ℝ} {vL vR : Fin 1 → ℝ≥0 → ℝ} {b : ℝ≥0 → ℝ}
  {ζ : ℝ≥0∞}
variable (h : IsIntegratedSLEPath κ (fun _ => 0) (fun _ => 0) ρL ρR w vL vR b ζ)
include h

/-- **The integrated equation determines `B`**: `√κ b_t = W_t + ½ρ_L V^L_t + ½ρ_R V^R_t`. -/
theorem sqrt_mul_b_eq {t : ℝ≥0} (ht : (t : ℝ≥0∞) < ζ) :
    Real.sqrt κ * b t = w t + ρL 0 / 2 * vL 0 t + ρR 0 / 2 * vR 0 t := by
  have hw := path_w_eq h ht
  simp only [Fin.sum_univ_one] at hw
  have hL : ∫ s in (0 : ℝ)..t, ρL 0 / (w s.toNNReal - vL 0 s.toNNReal) = -(ρL 0 / 2) * vL 0 t := by
    have e : ∫ s in (0 : ℝ)..t, ρL 0 / (w s.toNNReal - vL 0 s.toNNReal) =
        ρL 0 / 2 * ∫ s in (0 : ℝ)..t, 2 / gapLR w vL s := by
      rw [← intervalIntegral.integral_const_mul]
      refine intervalIntegral.integral_congr fun s _ => ?_
      simp only [gapLR]
      ring
    rw [e, vL_eq_neg_integral h ht]
    ring
  have hR : ∫ s in (0 : ℝ)..t, ρR 0 / (w s.toNNReal - vR 0 s.toNNReal) = -(ρR 0 / 2) * vR 0 t := by
    have e : ∫ s in (0 : ℝ)..t, ρR 0 / (w s.toNNReal - vR 0 s.toNNReal) =
        -(ρR 0 / 2) * ∫ s in (0 : ℝ)..t, 2 / gapRR w vR s := by
      rw [← intervalIntegral.integral_const_mul]
      refine intervalIntegral.integral_congr fun s _ => ?_
      simp only [gapRR]
      rw [← neg_sub, div_neg]
      ring
    rw [e, vR_eq_integral h ht]
  rw [hL, hR] at hw
  linarith

variable (hb : Continuous b) (hρL : -2 < ρL 0) (hρR : -2 < ρR 0)
include hb hρL hρR

/-- **The lifetime is the total clock of the angle path.** -/
theorem lifetime_eq_iSup_clock :
    ζ = ⨆ q : ℚ, ENNReal.ofReal (clock (logAngle w vL vR ζ) q) := by
  have hρL' : ∀ i, -2 < ρL i := fun i => by fin_cases i; exact hρL
  have hρR' : ∀ i, -2 < ρR i := fun i => by fin_cases i; exact hρR
  obtain ⟨hUc, hU01, -, hid⟩ := logAngle_spec h hb hρL' hρR'
  refine le_antisymm (le_of_forall_lt fun x hx => ?_)
    (iSup_le fun q => clock_logAngle_le h hb hρL' hρR' q)
  obtain ⟨t, hxt, htζ⟩ := ENNReal.lt_iff_exists_nnreal_btwn.1 hx
  have ht0 : 0 < t := by
    rcases (zero_le (a := t)).eq_or_lt with h0 | h0
    · rw [← h0] at hxt; exact absurd hxt (not_lt.2 bot_le)
    · exact h0
  obtain ⟨hclock, -⟩ := hid t htζ ht0
  obtain ⟨q, hq⟩ := exists_rat_gt (log (sepN vL vR t))
  refine lt_of_lt_of_le hxt (le_trans ?_ (le_iSup _ q))
  rw [← ENNReal.ofReal_coe_nnreal]
  refine ENNReal.ofReal_le_ofReal ?_
  rw [← hclock]
  exact monotone_clock hUc hU01 hq.le

/-- **The state before the lifetime is the clock construction of the angle path.** -/
theorem state_eq_phys (hκ : 0 < κ) (hb0 : b 0 = 0) {t : ℝ≥0} (ht : (t : ℝ≥0∞) < ζ) :
    ((w t, (fun i => vL i t), (fun i => vR i t), b t) : ℝ × (Fin 1 → ℝ) × (Fin 1 → ℝ) × ℝ) =
      (phys (logAngle w vL vR ζ) (driver (logAngle w vL vR ζ)) t,
        fun _ => phys (logAngle w vL vR ζ) (lowerL (logAngle w vL vR ζ)) t,
        fun _ => phys (logAngle w vL vR ζ) (upperL (logAngle w vL vR ζ)) t,
        (phys (logAngle w vL vR ζ) (driver (logAngle w vL vR ζ)) t +
          ρL 0 / 2 * phys (logAngle w vL vR ζ) (lowerL (logAngle w vL vR ζ)) t +
          ρR 0 / 2 * phys (logAngle w vL vR ζ) (upperL (logAngle w vL vR ζ)) t) / Real.sqrt κ) := by
  have hρL' : ∀ i, -2 < ρL i := fun i => by fin_cases i; exact hρL
  have hρR' : ∀ i, -2 < ρR i := fun i => by fin_cases i; exact hρR
  obtain ⟨hUc, hU01, hnull, hid⟩ := logAngle_spec h hb hρL' hρR'
  set U := logAngle w vL vR ζ
  have hb_eq : b t = (w t + ρL 0 / 2 * vL 0 t + ρR 0 / 2 * vR 0 t) / Real.sqrt κ := by
    rw [eq_div_iff (Real.sqrt_pos.2 hκ).ne', mul_comm]
    exact sqrt_mul_b_eq h ht
  rcases (zero_le (a := t)).eq_or_lt with h0 | ht0
  · subst h0
    have hw0 : w 0 = 0 := h.1
    have hl0 : vL 0 0 = 0 := path_vL_zero h
    have hr0 : vR 0 0 = 0 := path_vR_zero h
    simp only [NNReal.coe_zero, phys_of_nonpos le_rfl, hw0, hb0, mul_zero, add_zero, zero_div]
    refine Prod.ext rfl (Prod.ext ?_ (Prod.ext ?_ rfl))
    · funext i; fin_cases i; exact hl0
    · funext i; fin_cases i; exact hr0
  · obtain ⟨hclock, hvl, hvr, hww⟩ := hid t ht ht0
    have hinv : invClock U t = log (sepN vL vR t) := invClock_eq_of_clock_eq hUc hU01 hnull hclock
    have htpos : (0 : ℝ) < t := ht0
    simp only [phys_of_pos htpos, hinv]
    rw [hb_eq, hww, hvl, hvr]
    refine Prod.ext rfl (Prod.ext ?_ (Prod.ext ?_ rfl))
    · funext i; fin_cases i; exact hvl
    · funext i; fin_cases i; exact hvr

end PathId

end TwoSeed

end Sec2

end InteractingSLE
