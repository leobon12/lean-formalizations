/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec2.TwoSeedLawGen
import InteractingSLE.Spec.Ito.Localize
import InteractingSLE.Spec.Ito.Measurability
import MathFin.Probability.Brownian.ExitTime
import InteractingSLE.Frozen.Spec.IsIntegratedSLEEvolution

/-!
# Two seeds: the logarithmic-clock angle of an evolution solves the Jacobi martingale problem

Packet PROVE-SEC2-JAC2. Specification, proof of Theorem 2.2 (`source/spec/p001-048.md`, L540–L546): for any
integrated evolution with force points `0⁻, 0⁺` and weights `ρ_L, ρ_R > −2`, "the change of clock
`u = log ℓ_t` transforms `X` into precisely the Jacobi diffusion above". In the form used by the moment
uniqueness of `JacobiMoments.lean`: the angle `U_u = (W − V^L)/ℓ` at the hitting time `τ_u` of the level
`ℓ = e^u` (`logAngle`), modified on a null set, satisfies `Jacobi.IsJacobiMP κ (ρ_L + 2) (ρ_R + 2)`
(`isJacobiMP_angle`).

Proof. The angle is `A = (√κ B + Λ¹)/Λ²` with `Λ` absolutely continuous (`TwoSeedLawGen`). On the
null-augmented filtration, with the Brownian motion and the coordinates modified off a full-measure event
of good paths, the localized Itô formula (`Ito.martingale_itoLocalized`) at the stopping time
`σ_N = τ_v ∧ (exit time of |B| from [−N, N])` makes
`A^n_{t∧σ_N} − ∫_0^{t∧σ_N} (∂_Λ A^n · λ + ½ ∂²_B A^n)` a martingale. Optional sampling between
`τ_w ∧ σ_N` and a deterministic bound of `τ_v` (`8τ_v ≤ e^{2v}`) against a bounded `𝓕_{τ_w ∧ σ_N}`-measurable
product of earlier angles, the clock change `integral_itoGen_angleObs`, and dominated convergence as
`N → ∞` give the martingale-problem identity of `IsJacobiMP`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter Topology Real
open scoped NNReal ENNReal Classical

namespace InteractingSLE

namespace Sec2

namespace TwoSeed

/-! ### Hitting times of a good path -/

section PathHit

variable {κ : ℝ} {ρL ρR : Fin 1 → ℝ} {w : ℝ≥0 → ℝ} {vL vR : Fin 1 → ℝ≥0 → ℝ} {b : ℝ≥0 → ℝ}
  {ζ : ℝ≥0∞}
variable (h : IsIntegratedSLEPath κ (fun _ => 0) (fun _ => 0) ρL ρR w vL vR b ζ)
  (hb : Continuous b) (hρL : -2 < ρL 0) (hρR : -2 < ρR 0)
include h hb hρL hρR

/-- Every level `e^u` is reached before the lifetime. -/
theorem hitTime_lt_and_sepN (u : ℝ) :
    (hitTime vL vR ζ u : ℝ≥0∞) < ζ ∧ sepN vL vR (hitTime vL vR ζ u) = exp u := by
  obtain ⟨t₀, ht₀, hle⟩ := sepN_unbounded h hb (fun i => by fin_cases i; exact hρL)
    (fun i => by fin_cases i; exact hρR) (exp u)
  obtain ⟨h1, h2⟩ := hitTime_spec h ht₀ hle
  exact ⟨lt_of_le_of_lt (by exact_mod_cast h1) ht₀, h2⟩

theorem hitTime_le_iff (u : ℝ) (t : ℝ≥0) :
    hitTime vL vR ζ u ≤ t ↔ ((t : ℝ≥0∞) < ζ ∧ exp u ≤ sepN vL vR t) ∨ ζ ≤ t := by
  obtain ⟨hlt, he⟩ := hitTime_lt_and_sepN h hb hρL hρR u
  constructor
  · intro hle
    by_cases ht : (t : ℝ≥0∞) < ζ
    · exact Or.inl ⟨ht, he ▸ le_sepN_of_le h ht hle le_rfl⟩
    · exact Or.inr (not_lt.1 ht)
  · rintro (⟨ht, hle⟩ | hζ)
    · exact csInf_le (OrderBot.bddBelow _) ⟨ht, hle⟩
    · exact_mod_cast (lt_of_lt_of_le hlt hζ).le

theorem hitTime_mono {u₁ u₂ : ℝ} (hu : u₁ ≤ u₂) : hitTime vL vR ζ u₁ ≤ hitTime vL vR ζ u₂ := by
  obtain ⟨hlt, he⟩ := hitTime_lt_and_sepN h hb hρL hρR u₂
  exact monotoneOn_hitTime h hlt ((exp_le_exp.2 hu).trans he.ge) he.ge hu

theorem eight_mul_hitTime_le (u : ℝ) : 8 * (hitTime vL vR ζ u : ℝ) ≤ exp u ^ 2 := by
  obtain ⟨hlt, he⟩ := hitTime_lt_and_sepN h hb hρL hρR u
  rw [← he]
  exact eight_mul_le_sepN_sq h hlt

/-- The angle observable at a hitting time is the power of the logarithmic-clock angle. -/
theorem angleObs_hitTime {c : ℝ} (hc : 0 < c) (n : ℕ) {u : ℝ} (hcu : c / 2 ≤ exp u) :
    angleObs κ c n (acCoord κ w vL vR b (hitTime vL vR ζ u), b (hitTime vL vR ζ u)) =
      logAngle w vL vR ζ u ^ n := by
  obtain ⟨-, he⟩ := hitTime_lt_and_sepN h hb hρL hρR u
  simp only [angleObs, acCoord]
  rw [he, cutψ_of_le hc hcu, logAngle]
  congr 2
  ring

/-- Between `τ_w` and a later time `σ ≤ τ_v`, the generator integral is a logarithmic-clock integral up to
`log ℓ_σ ∈ [w, v]`. -/
theorem integral_itoGen_angleObs_upTo (hκ : 0 ≤ κ) {w₀ v₀ : ℝ} {σ : ℝ≥0}
    (hσw : hitTime vL vR ζ w₀ < σ) (hσv : σ ≤ hitTime vL vR ζ v₀) (n : ℕ) :
    ∃ u₂, w₀ ≤ u₂ ∧ u₂ ≤ v₀ ∧
      ∫ s in (hitTime vL vR ζ w₀ : ℝ)..(σ : ℝ),
          Ito.itoGen (angleObs κ (exp w₀) n) (acCoord κ w vL vR b s.toNNReal, b s.toNNReal)
            (acDens ρL ρR w vL vR s) =
        ∫ x in w₀..u₂, Jacobi.gen κ (ρL 0 + 2) (ρR 0 + 2) (fun y => y ^ n)
          (logAngle w vL vR ζ x) := by
  obtain ⟨hvζ, hve⟩ := hitTime_lt_and_sepN h hb hρL hρR v₀
  obtain ⟨-, hwe⟩ := hitTime_lt_and_sepN h hb hρL hρR w₀
  have hσζ : (σ : ℝ≥0∞) < ζ := lt_of_le_of_lt (by exact_mod_cast hσv) hvζ
  have hσ0 : 0 < σ := lt_of_le_of_lt zero_le hσw
  have hlt : exp w₀ < sepN vL vR σ := hwe ▸ sepN_lt_sepN h hσζ hσw le_rfl
  have hle : sepN vL vR σ ≤ exp v₀ := hve ▸ le_sepN_of_le h hvζ hσv le_rfl
  have hpos : 0 < sepN vL vR σ := (exp_pos _).trans hlt
  refine ⟨log (sepN vL vR σ), ?_, ?_, ?_⟩
  · rw [← log_exp w₀]; exact (log_lt_log (exp_pos _) hlt).le
  · rw [← log_exp v₀]; exact log_le_log hpos hle
  · have hUc := (logAngle_spec h hb (fun i => by fin_cases i; exact hρL)
      (fun i => by fin_cases i; exact hρR)).1
    have := integral_itoGen_angleObs h hκ (u₁ := w₀) (u₂ := log (sepN vL vR σ))
      (log_exp w₀ ▸ log_le_log (exp_pos _) hlt.le) hσζ (by rw [exp_log hpos]) hUc n
    rwa [hitTime_log_sepN h hσζ hσ0] at this

end PathHit

/-! ### Process-level objects -/

section Generic

variable {Ω : Type*} {mΩ : MeasurableSpace Ω}

/-- A process living before `ζ` and killed to `0` afterwards is adapted. -/
theorem measurable_killed {𝓕 : Filtration ℝ≥0 mΩ} {ζ : Ω → ℝ≥0∞} {X : ℝ≥0 → Ω → ℝ}
    (hX : AdaptedBefore 𝓕 ζ X) (t : ℝ≥0) :
    Measurable[𝓕 t] fun ω => if (t : ℝ≥0∞) < ζ ω then X t ω else 0 := by
  intro A hA
  have h1 := hX t A hA
  have h2 : MeasurableSet[𝓕 t] {ω | (t : ℝ≥0∞) < ζ ω} := by
    simpa using hX t univ MeasurableSet.univ
  by_cases h0 : (0 : ℝ) ∈ A
  · have : (fun ω => if (t : ℝ≥0∞) < ζ ω then X t ω else 0) ⁻¹' A =
        {ω | (t : ℝ≥0∞) < ζ ω ∧ X t ω ∈ A} ∪ {ω | (t : ℝ≥0∞) < ζ ω}ᶜ := by
      ext ω
      by_cases ht : (t : ℝ≥0∞) < ζ ω <;> simp [ht, h0]
    rw [this]
    exact h1.union h2.compl
  · have : (fun ω => if (t : ℝ≥0∞) < ζ ω then X t ω else 0) ⁻¹' A =
        {ω | (t : ℝ≥0∞) < ζ ω ∧ X t ω ∈ A} := by
      ext ω
      by_cases ht : (t : ℝ≥0∞) < ζ ω <;> simp [ht, h0]
    rw [this]
    exact h1

/-- The minimum of a finite time and a possibly infinite one, as a finite time. -/
def capTime (τ : Ω → ℝ≥0) (e : Ω → WithTop ℝ≥0) (ω : Ω) : ℝ≥0 :=
  (min (τ ω : WithTop ℝ≥0) (e ω)).untop (ne_top_of_le_ne_top WithTop.coe_ne_top (min_le_left _ _))

theorem coe_capTime (τ : Ω → ℝ≥0) (e : Ω → WithTop ℝ≥0) (ω : Ω) :
    (capTime τ e ω : WithTop ℝ≥0) = min (τ ω : WithTop ℝ≥0) (e ω) :=
  WithTop.coe_untop _ _

theorem capTime_le (τ : Ω → ℝ≥0) (e : Ω → WithTop ℝ≥0) (ω : Ω) : capTime τ e ω ≤ τ ω := by
  have := min_le_left (τ ω : WithTop ℝ≥0) (e ω)
  rw [← coe_capTime] at this
  exact_mod_cast this

theorem capTime_le_right (τ : Ω → ℝ≥0) (e : Ω → WithTop ℝ≥0) (ω : Ω) :
    (capTime τ e ω : WithTop ℝ≥0) ≤ e ω := by
  rw [coe_capTime]; exact min_le_right _ _

theorem capTime_eq_of_le {τ : Ω → ℝ≥0} {e : Ω → WithTop ℝ≥0} {ω : Ω} (h : (τ ω : WithTop ℝ≥0) ≤ e ω) :
    capTime τ e ω = τ ω := by
  have := coe_capTime τ e ω
  rw [min_eq_left h] at this
  exact_mod_cast this

theorem isStoppingTime_capTime {𝓖 : Filtration ℝ≥0 mΩ} {τ : Ω → ℝ≥0} {e : Ω → WithTop ℝ≥0}
    (hτ : IsStoppingTime 𝓖 fun ω => (τ ω : WithTop ℝ≥0)) (he : IsStoppingTime 𝓖 e) :
    IsStoppingTime 𝓖 fun ω => (capTime τ e ω : WithTop ℝ≥0) := by
  simp_rw [coe_capTime]
  exact hτ.min he

/-- **Optional sampling against a bounded `𝓖_ρ`-measurable factor**: for a continuous martingale `M`,
a stopping time `ρ ≤ T` and a bounded `𝓖_ρ`-measurable `Z`, `E[Z (M_T − M_ρ)] = 0`. -/
theorem integral_mul_sub_stoppedValue_eq_zero {P : Measure Ω} [IsFiniteMeasure P]
    {𝓖 : Filtration ℝ≥0 mΩ} {M : ℝ≥0 → Ω → ℝ} (hM : Martingale M 𝓖 P)
    (hMc : ∀ ω, Continuous fun t => M t ω) {ρ : Ω → WithTop ℝ≥0} (hρ : IsStoppingTime 𝓖 ρ)
    {T : ℝ≥0} (hρT : ∀ ω, ρ ω ≤ T) {Z : Ω → ℝ} (hZ : StronglyMeasurable[hρ.measurableSpace] Z)
    {C : ℝ} (hZC : ∀ ω, |Z ω| ≤ C) :
    ∫ ω, Z ω * (M T ω - stoppedValue M ρ ω) ∂P = 0 := by
  have hm := hρ.measurableSpace_le
  have hos := Martingale.stoppedValue_ae_eq_condExp_of_rightContinuous hM
    (fun ω t => (hMc ω).continuousWithinAt) hρ (isStoppingTime_const 𝓖 T) hρT (T := T)
    (fun _ => le_rfl)
  rw [stoppedValue_const] at hos
  have hMT : Integrable (M T) P := hM.integrable T
  have hZm : AEStronglyMeasurable Z P := (hZ.mono hm).aestronglyMeasurable
  have hZb : ∀ᵐ ω ∂P, ‖Z ω‖ ≤ C := ae_of_all _ fun ω => by rw [Real.norm_eq_abs]; exact hZC ω
  have hZMT : Integrable (Z * M T) P := hMT.bdd_mul hZm hZb
  have hρi : Integrable (stoppedValue M ρ) P := integrable_condExp.congr hos.symm
  have hZMρ : Integrable (Z * stoppedValue M ρ) P := hρi.bdd_mul hZm hZb
  have hpull := condExp_mul_of_stronglyMeasurable_left (m := hρ.measurableSpace) hZ hZMT hMT
  have h1 : ∫ ω, (Z * M T) ω ∂P = ∫ ω, (Z * stoppedValue M ρ) ω ∂P := by
    rw [← integral_condExp hm]
    refine integral_congr_ae ?_
    filter_upwards [hpull, hos] with ω h1 h2
    rw [h1, Pi.mul_apply, Pi.mul_apply, h2]
  have h2 : (fun ω => Z ω * (M T ω - stoppedValue M ρ ω)) = Z * M T - Z * stoppedValue M ρ := by
    funext ω; simp only [Pi.sub_apply, Pi.mul_apply]; ring
  rw [h2, show Z * M T - Z * stoppedValue M ρ = fun ω => (Z * M T) ω - (Z * stoppedValue M ρ) ω
    from rfl, integral_sub hZMT hZMρ, h1, sub_self]

theorem stoppedValue_coe {β : Type*} (M : ℝ≥0 → Ω → β) (r : Ω → ℝ≥0) :
    stoppedValue M (fun ω => ((r ω : ℝ≥0) : WithTop ℝ≥0)) = fun ω => M (r ω) ω := rfl

/-- The Jacobi generator of `x^n` is bounded on `[0, 1]`. -/
theorem abs_gen_pow_le (κ a c : ℝ) (n : ℕ) {x : ℝ} (hx : x ∈ Icc (0 : ℝ) 1) :
    |Jacobi.gen κ a c (fun y => y ^ n) x| ≤ |Jacobi.dcoef κ a n| + |Jacobi.ccoef κ a c n| := by
  rw [Jacobi.gen_pow]
  have h1 : |x ^ (n - 1)| ≤ 1 := by
    rw [abs_pow, abs_of_nonneg hx.1]; exact pow_le_one₀ hx.1 hx.2
  have h2 : |x ^ n| ≤ 1 := by
    rw [abs_pow, abs_of_nonneg hx.1]; exact pow_le_one₀ hx.1 hx.2
  refine (abs_add_le _ _).trans (add_le_add ?_ ?_)
  · rw [abs_mul]; exact mul_le_of_le_one_right (abs_nonneg _) h1
  · rw [abs_mul]; exact mul_le_of_le_one_right (abs_nonneg _) h2

theorem abs_integral_gen_le (κ a c : ℝ) (n : ℕ) {U : ℝ → ℝ} (hU : ∀ x, U x ∈ Icc (0 : ℝ) 1)
    {w u : ℝ} (hwu : w ≤ u) :
    |∫ x in w..u, Jacobi.gen κ a c (fun y => y ^ n) (U x)| ≤
      (u - w) * (|Jacobi.dcoef κ a n| + |Jacobi.ccoef κ a c n|) := by
  have := intervalIntegral.norm_integral_le_of_norm_le_const (a := w) (b := u)
    (C := |Jacobi.dcoef κ a n| + |Jacobi.ccoef κ a c n|)
    (f := fun x => Jacobi.gen κ a c (fun y => y ^ n) (U x))
    (fun x _ => by rw [Real.norm_eq_abs]; exact abs_gen_pow_le κ a c n (hU x))
  rw [Real.norm_eq_abs, abs_of_nonneg (sub_nonneg.2 hwu)] at this
  linarith

end Generic

section Process

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
  {κ : ℝ} {ρL ρR : Fin 1 → ℝ} {W : ℝ≥0 → Ω → ℝ} {VL VR : Fin 1 → ℝ≥0 → Ω → ℝ}
  {B : ℝ≥0 → Ω → ℝ} {ζ : Ω → ℝ≥0∞} {G : Set Ω}

/-- The good paths of a two-seed evolution: the pathwise conditions hold, `B` is continuous and
starts at `0`. -/
def IsGoodTwoSeed (κ : ℝ) (ρL ρR : Fin 1 → ℝ) (W : ℝ≥0 → Ω → ℝ) (VL VR : Fin 1 → ℝ≥0 → Ω → ℝ)
    (B : ℝ≥0 → Ω → ℝ) (ζ : Ω → ℝ≥0∞) (ω : Ω) : Prop :=
  IsIntegratedSLEPath κ (fun _ => 0) (fun _ => 0) ρL ρR (W · ω) (fun i t => VL i t ω)
    (fun i t => VR i t ω) (B · ω) (ζ ω) ∧ Continuous (B · ω) ∧ B 0 ω = 0

/-- The hitting time of the level `e^u` by the separation, on the good event `G` (`0` off it). -/
def hitG (G : Set Ω) (VL VR : Fin 1 → ℝ≥0 → Ω → ℝ) (ζ : Ω → ℝ≥0∞) (u : ℝ) (ω : Ω) : ℝ≥0 :=
  if ω ∈ G then hitTime (fun i t => VL i t ω) (fun i t => VR i t ω) (ζ ω) u else 0

/-- The logarithmic-clock angle on the good event (`0` off it). -/
def angleG (G : Set Ω) (W : ℝ≥0 → Ω → ℝ) (VL VR : Fin 1 → ℝ≥0 → Ω → ℝ) (ζ : Ω → ℝ≥0∞) (u : ℝ)
    (ω : Ω) : ℝ :=
  if ω ∈ G then logAngle (W · ω) (fun i t => VL i t ω) (fun i t => VR i t ω) (ζ ω) u else 0

/-- The absolutely continuous coordinates on the good event (`0` off it). -/
def coordG (κ : ℝ) (G : Set Ω) (W : ℝ≥0 → Ω → ℝ) (VL VR : Fin 1 → ℝ≥0 → Ω → ℝ) (B : ℝ≥0 → Ω → ℝ)
    (t : ℝ≥0) (ω : Ω) : ℝ × ℝ :=
  if ω ∈ G then acCoord κ (W · ω) (fun i t => VL i t ω) (fun i t => VR i t ω) (B · ω) t else 0

/-- Their density on the good event (`0` off it). -/
def densG (ρL ρR : Fin 1 → ℝ) (G : Set Ω) (W : ℝ≥0 → Ω → ℝ) (VL VR : Fin 1 → ℝ≥0 → Ω → ℝ)
    (s : ℝ) (ω : Ω) : ℝ × ℝ :=
  if ω ∈ G then acDens ρL ρR (W · ω) (fun i t => VL i t ω) (fun i t => VR i t ω) s else 0

/-- The Brownian motion on the good event (`0` off it). -/
def brownG (G : Set Ω) (B : ℝ≥0 → Ω → ℝ) (t : ℝ≥0) (ω : Ω) : ℝ := if ω ∈ G then B t ω else 0

variable (hE : IsIntegratedSLEEvolution κ (fun _ => 0) (fun _ => 0) ρL ρR P 𝓕 W VL VR B ζ)
  (hρL : -2 < ρL 0) (hρR : -2 < ρR 0) (hGm : MeasurableSet G) (hGc : P Gᶜ = 0)
  (hgood : ∀ ω ∈ G, IsGoodTwoSeed κ ρL ρR W VL VR B ζ ω)

include hGm hGc in
theorem measurableSet_good_nullAugmented (t : ℝ≥0) : MeasurableSet[Ito.nullAugmented 𝓕 P t] G := by
  have := (Ito.measurableSet_nullAugmented_of_null (𝓕 := 𝓕) hGm.compl hGc t).compl
  rwa [compl_compl] at this

include hE hρL hρR hGm hGc hgood in
/-- The hitting times are stopping times of the null-augmented filtration. -/
theorem isStoppingTime_hitG (u : ℝ) :
    IsStoppingTime (Ito.nullAugmented 𝓕 P) fun ω => (hitG G VL VR ζ u ω : WithTop ℝ≥0) := by
  obtain ⟨-, -, hVLa, hVRa, -⟩ := hE
  intro t
  set kL := fun ω => if (t : ℝ≥0∞) < ζ ω then VL 0 t ω else 0
  set kR := fun ω => if (t : ℝ≥0∞) < ζ ω then VR 0 t ω else 0
  have hkL : Measurable[𝓕 t] kL := measurable_killed (hVLa 0) t
  have hkR : Measurable[𝓕 t] kR := measurable_killed (hVRa 0) t
  have hζt : MeasurableSet[𝓕 t] {ω | (t : ℝ≥0∞) < ζ ω} := by
    simpa using hVLa 0 t univ MeasurableSet.univ
  have hlev : MeasurableSet[𝓕 t] {ω | exp u ≤ kR ω - kL ω} :=
    measurableSet_le measurable_const (hkR.sub hkL)
  have heq : {ω | (hitG G VL VR ζ u ω : WithTop ℝ≥0) ≤ t} =
      Gᶜ ∪ (G ∩ (({ω | (t : ℝ≥0∞) < ζ ω} ∩ {ω | exp u ≤ kR ω - kL ω}) ∪
        {ω | (t : ℝ≥0∞) < ζ ω}ᶜ)) := by
    ext ω
    by_cases hω : ω ∈ G
    · obtain ⟨hP, hBc, -⟩ := hgood ω hω
      simp only [mem_ofPred_eq, hitG, hω, ↓reduceIte, WithTop.coe_le_coe, mem_union, mem_compl_iff,
        not_true_eq_false, mem_inter_iff, true_and, false_or, not_lt]
      rw [hitTime_le_iff hP hBc hρL hρR u t]
      by_cases ht : (t : ℝ≥0∞) < ζ ω
      · simp [kL, kR, ht, sepN]
      · simp [ht, not_lt.1 ht]
    · simp only [hitG, hω, ↓reduceIte, mem_ofPred_eq, WithTop.coe_zero, mem_union, mem_compl_iff,
        not_false_eq_true, true_or, iff_true]
      exact_mod_cast (zero_le (a := t))
  rw [heq]
  have hG' := measurableSet_good_nullAugmented hGm hGc (𝓕 := 𝓕) t
  exact hG'.compl.union (hG'.inter (((Ito.le_nullAugmented 𝓕 P t _ hζt).inter
    (Ito.le_nullAugmented 𝓕 P t _ hlev)).union (Ito.le_nullAugmented 𝓕 P t _ hζt).compl))

/-! #### Pathwise facts on the good event -/

section GoodFacts

variable {v : ℝ} {ω : Ω}

include hρL hρR hgood

theorem lt_of_le_hitG (hω : ω ∈ G) {t : ℝ≥0} (ht : t ≤ hitG G VL VR ζ v ω) : (t : ℝ≥0∞) < ζ ω := by
  obtain ⟨hP, hBc, -⟩ := hgood ω hω
  simp only [hitG, hω, ↓reduceIte] at ht
  exact lt_of_le_of_lt (by exact_mod_cast ht) (hitTime_lt_and_sepN hP hBc hρL hρR v).1

theorem sepN_le_of_le_hitG (hω : ω ∈ G) {t : ℝ≥0} (ht : t ≤ hitG G VL VR ζ v ω) :
    sepN (fun i t => VL i t ω) (fun i t => VR i t ω) t ≤ exp v := by
  obtain ⟨hP, hBc, -⟩ := hgood ω hω
  simp only [hitG, hω, ↓reduceIte] at ht
  obtain ⟨hlt, he⟩ := hitTime_lt_and_sepN hP hBc hρL hρR v
  rw [← he]
  exact le_sepN_of_le hP hlt ht le_rfl

theorem coordG_mem (hω : ω ∈ G) {t : ℝ≥0} (ht : t ≤ hitG G VL VR ζ v ω) :
    (coordG κ G W VL VR B t ω).2 ∈ Icc 0 (exp v) ∧
      W t ω - VL 0 t ω ∈ Icc 0 ((coordG κ G W VL VR B t ω).2) := by
  obtain ⟨hP, -, -⟩ := hgood ω hω
  have htζ := lt_of_le_hitG hρL hρR hgood hω ht
  have h1 := path_vL_le_w hP htζ
  have h2 := path_w_le_vR hP htζ
  simp only [coordG, hω, ↓reduceIte, acCoord, sepN]
  refine ⟨⟨by linarith, ?_⟩, ⟨by linarith, by linarith⟩⟩
  have := sepN_le_of_le_hitG hρL hρR hgood hω ht
  simpa [sepN] using this

end GoodFacts

/-! #### The localized Itô martingale of the angle -/

/-- The localizing time `σ_N = τ_v ∧ (exit time of |B| from (−N, N))`. -/
def locTime (G : Set Ω) (VL VR : Fin 1 → ℝ≥0 → Ω → ℝ) (ζ : Ω → ℝ≥0∞) (B : ℝ≥0 → Ω → ℝ) (v : ℝ)
    (N : ℕ) (ω : Ω) : ℝ≥0 :=
  capTime (hitG G VL VR ζ v) (MathFin.exitTime (brownG G B) N) ω

/-- A compact box containing the stopped coordinates. -/
def boxK (κ v : ℝ) (N : ℕ) : Set ((ℝ × ℝ) × ℝ) :=
  (Icc (-(exp v + Real.sqrt κ * N)) (exp v + Real.sqrt κ * N) ×ˢ Icc 0 (exp v)) ×ˢ
    Icc (-(N : ℝ)) N

theorem isCompact_boxK (κ v : ℝ) (N : ℕ) : IsCompact (boxK κ v N) :=
  (isCompact_Icc.prod isCompact_Icc).prod isCompact_Icc

include hgood in
theorem continuous_brownG (ω : Ω) : Continuous (brownG G B · ω) := by
  by_cases hω : ω ∈ G
  · simpa only [brownG, hω, ↓reduceIte] using (hgood ω hω).2.1
  · simp only [brownG, hω, ↓reduceIte]; exact continuous_const

include hE hGm hGc hgood in
theorem isFilteredBrownianReal_brownG :
    IsFilteredBrownianReal (Ito.nullAugmented 𝓕 P) (brownG G B) P :=
  (Ito.isFilteredBrownianReal_modify hE.1 hGm hGc fun ω hω => (hgood ω hω).2.1).1

include hE hρL hρR hGm hGc hgood in
theorem isStoppingTime_locTime (v : ℝ) (N : ℕ) :
    IsStoppingTime (Ito.nullAugmented 𝓕 P) fun ω => (locTime G VL VR ζ B v N ω : WithTop ℝ≥0) :=
  isStoppingTime_capTime (isStoppingTime_hitG hE hρL hρR hGm hGc hgood v)
    (MathFin.isStoppingTime_exitTime_of_measurable
      (isFilteredBrownianReal_brownG hE hGm hGc hgood).2.1 (continuous_brownG hgood) N)

include hgood in
theorem abs_brownG_le {N : ℕ} {ω : Ω} (hω : ω ∈ G) {t : ℝ≥0}
    (ht : (t : WithTop ℝ≥0) ≤ MathFin.exitTime (brownG G B) N ω) : |brownG G B t ω| ≤ N := by
  rcases (zero_le (a := t)).eq_or_lt with rfl | ht0
  · simp only [brownG, hω, ↓reduceIte, (hgood ω hω).2.2, abs_zero]; exact Nat.cast_nonneg N
  · exact MathFin.abs_le_N_of_le_exitTime (continuous_brownG hgood) ht0 ht

theorem locTime_le_hitG (v : ℝ) (N : ℕ) (ω : Ω) :
    locTime G VL VR ζ B v N ω ≤ hitG G VL VR ζ v ω := capTime_le _ _ ω

include hE hρL hρR hGm hGc hgood in
/-- The coordinates stopped at a stopping time before `τ_v` are adapted. -/
theorem measurable_coordG_stopped {v : ℝ} {σ : Ω → ℝ≥0}
    (hσ : IsStoppingTime (Ito.nullAugmented 𝓕 P) fun ω => (σ ω : WithTop ℝ≥0))
    (hσhit : ∀ ω, σ ω ≤ hitG G VL VR ζ v ω) (t : ℝ≥0) :
    Measurable[Ito.nullAugmented 𝓕 P t] fun ω => coordG κ G W VL VR B (min t (σ ω)) ω := by
  obtain ⟨hB, hWa, hVLa, hVRa, -⟩ := hE
  set 𝓖 := Ito.nullAugmented 𝓕 P
  have hG0 := measurableSet_good_nullAugmented hGm hGc (𝓕 := 𝓕) 0
  set Kp : ℝ≥0 → Ω → ℝ × ℝ := fun s ω =>
    ((if (s : ℝ≥0∞) < ζ ω then W s ω else 0) - Real.sqrt κ * B s ω -
        (if (s : ℝ≥0∞) < ζ ω then VL 0 s ω else 0),
      (if (s : ℝ≥0∞) < ζ ω then VR 0 s ω else 0) - (if (s : ℝ≥0∞) < ζ ω then VL 0 s ω else 0))
    with hKp
  have hKpm : ∀ s, Measurable[𝓖 s] (Kp s) := fun s => by
    have hw := (measurable_killed hWa s).mono (Ito.le_nullAugmented 𝓕 P s) le_rfl
    have hl := (measurable_killed (hVLa 0) s).mono (Ito.le_nullAugmented 𝓕 P s) le_rfl
    have hr := (measurable_killed (hVRa 0) s).mono (Ito.le_nullAugmented 𝓕 P s) le_rfl
    have hb := (hB.2.1 s).mono (Ito.le_nullAugmented 𝓕 P s) le_rfl
    exact ((hw.sub (measurable_const.mul hb)).sub hl).prodMk (hr.sub hl)
  refine Ito.measurable_stopped_of_agree (X := fun s ω => acCoord κ (W · ω) (fun i t => VL i t ω)
    (fun i t => VR i t ω) (B · ω) s) hσ hKpm hG0 (0 : ℝ × ℝ) (fun ω hω s hs => ?_)
    (fun ω hω => ?_) t
  · have hsζ := lt_of_le_hitG hρL hρR hgood hω (hs.trans (hσhit ω))
    simp only [hKp, hsζ, ↓reduceIte, acCoord, sepN]
  · obtain ⟨hP, hBc, -⟩ := hgood ω hω
    have hsub : Iic (σ ω) ⊆ {t | (t : ℝ≥0∞) < ζ ω} := fun s hs =>
      lt_of_le_hitG hρL hρR hgood hω ((mem_Iic.1 hs).trans (hσhit ω))
    have hW := (path_continuousOn_w hP).mono hsub
    have hL := (path_continuousOn_vL hP).mono hsub
    have hR := (path_continuousOn_vR hP).mono hsub
    exact ((hW.sub (continuous_const.mul hBc).continuousOn).sub hL).prodMk (hR.sub hL)

include hρL hρR hgood in
/-- The coordinates stopped before `τ_v` have continuous paths. -/
theorem continuous_coordG_stopped {v : ℝ} {σ : Ω → ℝ≥0} (hσhit : ∀ ω, σ ω ≤ hitG G VL VR ζ v ω)
    (ω : Ω) : Continuous fun t : ℝ≥0 => coordG κ G W VL VR B (min t (σ ω)) ω := by
  by_cases hω : ω ∈ G
  · obtain ⟨hP, hBc, -⟩ := hgood ω hω
    have hsub : Iic (σ ω) ⊆ {t | (t : ℝ≥0∞) < ζ ω} := fun s hs =>
      lt_of_le_hitG hρL hρR hgood hω ((mem_Iic.1 hs).trans (hσhit ω))
    have hW := (path_continuousOn_w hP).mono hsub
    have hL := (path_continuousOn_vL hP).mono hsub
    have hR := (path_continuousOn_vR hP).mono hsub
    have hX : ContinuousOn (fun s => acCoord κ (W · ω) (fun i t => VL i t ω)
        (fun i t => VR i t ω) (B · ω) s) (Iic (σ ω)) :=
      ((hW.sub (continuous_const.mul hBc).continuousOn).sub hL).prodMk (hR.sub hL)
    simp only [coordG, hω, ↓reduceIte]
    exact hX.comp_continuous (continuous_id.min continuous_const) fun t => mem_Iic.2 (min_le_right _ _)
  · simp only [coordG, hω, ↓reduceIte]; exact continuous_const

include hE hGm hGc hgood in
/-- The Brownian motion stopped at a stopping time is adapted. -/
theorem measurable_brownG_stopped {σ : Ω → ℝ≥0}
    (hσ : IsStoppingTime (Ito.nullAugmented 𝓕 P) fun ω => (σ ω : WithTop ℝ≥0)) (t : ℝ≥0) :
    Measurable[Ito.nullAugmented 𝓕 P t] fun ω => brownG G B (min t (σ ω)) ω := by
  have hG0 := measurableSet_good_nullAugmented hGm hGc (𝓕 := 𝓕) 0
  have hB' := isFilteredBrownianReal_brownG hE hGm hGc hgood
  have h := Ito.measurable_stopped_of_agree (X := brownG G B) hσ hB'.2.1 hG0 (0 : ℝ)
    (fun ω _ s _ => rfl) (fun ω _ => (continuous_brownG hgood ω).continuousOn) t
  convert h using 2 with ω
  by_cases hω : ω ∈ G <;> simp [brownG, hω]

include hE hρL hρR hGm hGc hgood in
/-- **The localized Itô martingale of the angle.** -/
theorem martingale_angle (v : ℝ) {c : ℝ} (hc : 0 < c) (n N : ℕ) :
    Martingale (fun t ω =>
      angleObs κ c n (coordG κ G W VL VR B (min t (locTime G VL VR ζ B v N ω)) ω,
        brownG G B (min t (locTime G VL VR ζ B v N ω)) ω) -
      ∫ s in (0 : ℝ)..(min t (locTime G VL VR ζ B v N ω) : ℝ≥0),
        Ito.itoGen (angleObs κ c n) (coordG κ G W VL VR B s.toNNReal ω, brownG G B s.toNNReal ω)
          (densG ρL ρR G W VL VR s ω)) (Ito.nullAugmented 𝓕 P) P := by
  have hE' := hE
  obtain ⟨hB, hWa, hVLa, hVRa, -⟩ := hE'
  set 𝓖 := Ito.nullAugmented 𝓕 P
  set σ := locTime G VL VR ζ B v N
  have hσ := isStoppingTime_locTime hE hρL hρR hGm hGc hgood v N
  have hσhit : ∀ ω, σ ω ≤ hitG G VL VR ζ v ω := locTime_le_hitG v N
  have hG0 := measurableSet_good_nullAugmented hGm hGc (𝓕 := 𝓕) 0
  have hΛm : ∀ t, Measurable[𝓖 t] fun ω => coordG κ G W VL VR B (min t (σ ω)) ω :=
    measurable_coordG_stopped hE hρL hρR hGm hGc hgood hσ hσhit
  -- pathwise hypotheses
  have hlam : ∀ ω, IntervalIntegrable (densG ρL ρR G W VL VR · ω) volume 0 (σ ω) := fun ω => by
    by_cases hω : ω ∈ G
    · simpa only [densG, hω, ↓reduceIte] using intervalIntegrable_acDens (hgood ω hω).1
        (lt_of_le_hitG hρL hρR hgood hω (hσhit ω))
    · simp only [densG, hω, ↓reduceIte]; exact intervalIntegrable_const
  have hΛ : ∀ ω (t : ℝ≥0), t ≤ σ ω → coordG κ G W VL VR B t ω =
      coordG κ G W VL VR B 0 ω + ∫ s in (0 : ℝ)..t, densG ρL ρR G W VL VR s ω := by
    intro ω t ht
    by_cases hω : ω ∈ G
    · simp only [coordG, densG, hω, ↓reduceIte]
      exact acCoord_eq_add_integral (hgood ω hω).1
        (lt_of_le_hitG hρL hρR hgood hω (ht.trans (hσhit ω)))
    · simp only [coordG, densG, hω, ↓reduceIte, intervalIntegral.integral_zero, add_zero]
  set Kb := (|ρL 0 + 2| + |ρR 0| + 2) / 2 * exp v with hKbdef
  have hKb0 : 0 ≤ Kb := by positivity
  have hKb : ∀ ω, ∫ s in (0 : ℝ)..(σ ω), ‖densG ρL ρR G W VL VR s ω‖ ≤ Kb := by
    intro ω
    by_cases hω : ω ∈ G
    · simp only [densG, hω, ↓reduceIte]
      refine (integral_norm_acDens_le (hgood ω hω).1
        (lt_of_le_hitG hρL hρR hgood hω (hσhit ω))).trans ?_
      exact mul_le_mul_of_nonneg_left (sepN_le_of_le_hitG hρL hρR hgood hω (hσhit ω))
        (by positivity)
    · simp only [densG, hω, ↓reduceIte, norm_zero, intervalIntegral.integral_zero]; exact hKb0
  have hK : ∀ ω (t : ℝ≥0), t ≤ σ ω →
      (coordG κ G W VL VR B t ω, brownG G B t ω) ∈ boxK κ v N := by
    intro ω t ht
    have hN0 : (0 : ℝ) ≤ N := Nat.cast_nonneg N
    have hsq := Real.sqrt_nonneg κ
    by_cases hω : ω ∈ G
    · have hth := ht.trans (hσhit ω)
      obtain ⟨⟨h20, h2v⟩, hX0, hXℓ⟩ := coordG_mem hρL hρR hgood (κ := κ) hω hth
      have hBN : |brownG G B t ω| ≤ N := abs_brownG_le hgood hω
        ((WithTop.coe_le_coe.2 ht).trans (capTime_le_right _ _ ω))
      have hBN' : |B t ω| ≤ N := by simpa only [brownG, hω, ↓reduceIte] using hBN
      have h1 : (coordG κ G W VL VR B t ω).1 = (W t ω - VL 0 t ω) - Real.sqrt κ * B t ω := by
        simp only [coordG, hω, ↓reduceIte, acCoord]; ring
      have hsB : |Real.sqrt κ * B t ω| ≤ Real.sqrt κ * N := by
        rw [abs_mul, abs_of_nonneg hsq]; exact mul_le_mul_of_nonneg_left hBN' hsq
      refine ⟨⟨⟨?_, ?_⟩, h20, h2v⟩, abs_le.1 hBN⟩
      · rw [h1]; linarith [(abs_le.1 hsB).2]
      · rw [h1]; linarith [(abs_le.1 hsB).1]
    · simp only [coordG, brownG, hω, ↓reduceIte, boxK]
      refine ⟨⟨⟨?_, ?_⟩, le_rfl, (exp_pos v).le⟩, ?_, hN0⟩
      · simp only [Prod.fst_zero]; nlinarith [exp_pos v]
      · simp only [Prod.fst_zero]; nlinarith [exp_pos v]
      · linarith
  exact Ito.martingale_itoLocalized (isFilteredBrownianReal_brownG hE hGm hGc hgood)
    (continuous_brownG hgood) isOpen_univ (contDiff_angleObs κ hc n).contDiffOn
    (isCompact_boxK κ v N) (subset_univ _) hσ hΛm hlam hΛ hKb hK

include hρL hρR hgood in
theorem intervalIntegrable_densG {v : ℝ} {σ : Ω → ℝ≥0} (hσhit : ∀ ω, σ ω ≤ hitG G VL VR ζ v ω)
    (ω : Ω) : IntervalIntegrable (densG ρL ρR G W VL VR · ω) volume 0 (σ ω) := by
  by_cases hω : ω ∈ G
  · simpa only [densG, hω, ↓reduceIte] using intervalIntegrable_acDens (hgood ω hω).1
      (lt_of_le_hitG hρL hρR hgood hω (hσhit ω))
  · simp only [densG, hω, ↓reduceIte]; exact intervalIntegrable_const

include hρL hρR hgood in
/-- The Itô generator along a good path is integrable up to a time before `τ_v`. -/
theorem intervalIntegrable_itoGen_angleG {v c : ℝ} (hc : 0 < c) (n : ℕ) {σ : Ω → ℝ≥0}
    (hσhit : ∀ ω, σ ω ≤ hitG G VL VR ζ v ω) (ω : Ω) :
    IntervalIntegrable (fun s => Ito.itoGen (angleObs κ c n)
      (coordG κ G W VL VR B s.toNNReal ω, brownG G B s.toNNReal ω) (densG ρL ρR G W VL VR s ω))
      volume 0 (σ ω) := by
  have hF := contDiff_angleObs κ hc n
  have hq : Continuous fun t : ℝ≥0 => (coordG κ G W VL VR B (min t (σ ω)) ω,
      brownG G B (min t (σ ω)) ω) :=
    (continuous_coordG_stopped hρL hρR hgood hσhit ω).prodMk
      ((continuous_brownG hgood ω).comp (continuous_id.min continuous_const))
  have hpc : ContinuousOn (fun s : ℝ => (coordG κ G W VL VR B s.toNNReal ω,
      brownG G B s.toNNReal ω)) (uIcc 0 (σ ω : ℝ)) := by
    refine (hq.comp continuous_real_toNNReal).continuousOn.congr fun s hs => ?_
    rw [uIcc_of_le (σ ω).coe_nonneg] at hs
    have : min s.toNNReal (σ ω) = s.toNNReal :=
      min_eq_left (Real.toNNReal_le_iff_le_coe.2 hs.2)
    simp only [Function.comp_apply, this]
  have hF1 : ContDiff ℝ 2 (fderiv ℝ (angleObs κ c n)) := hF.fderiv_right (by norm_num)
  have hPFc : Continuous (Ito.partialFst (angleObs κ c n)) :=
    (hF.continuous_fderiv (by norm_num)).clm_comp continuous_const
  have hPSSc : Continuous (Ito.partialSndSnd (angleObs κ c n)) :=
    ((hF1.continuous_fderiv (by norm_num)).clm_apply continuous_const).clm_apply continuous_const
  exact (Ito.intervalIntegrable_clm_apply (hPFc.comp_continuousOn hpc)
      (intervalIntegrable_densG hρL hρR hgood hσhit ω)).add
      (ContinuousOn.intervalIntegrable (u := fun s => 1 / 2 * Ito.partialSndSnd (angleObs κ c n)
        (coordG κ G W VL VR B s.toNNReal ω, brownG G B s.toNNReal ω))
        (continuousOn_const.mul (hPSSc.comp_continuousOn hpc)))

include hρL hρR hgood in
/-- The localized Itô martingale of the angle has continuous paths. -/
theorem continuous_martingale_angle (v : ℝ) {c : ℝ} (hc : 0 < c) (n N : ℕ) (ω : Ω) :
    Continuous fun t : ℝ≥0 =>
      angleObs κ c n (coordG κ G W VL VR B (min t (locTime G VL VR ζ B v N ω)) ω,
        brownG G B (min t (locTime G VL VR ζ B v N ω)) ω) -
      ∫ s in (0 : ℝ)..(min t (locTime G VL VR ζ B v N ω) : ℝ≥0),
        Ito.itoGen (angleObs κ c n) (coordG κ G W VL VR B s.toNNReal ω, brownG G B s.toNNReal ω)
          (densG ρL ρR G W VL VR s ω) := by
  set σ := locTime G VL VR ζ B v N
  have hσhit : ∀ ω, σ ω ≤ hitG G VL VR ζ v ω := locTime_le_hitG v N
  have hq : Continuous fun t : ℝ≥0 => (coordG κ G W VL VR B (min t (σ ω)) ω,
      brownG G B (min t (σ ω)) ω) :=
    (continuous_coordG_stopped hρL hρR hgood hσhit ω).prodMk
      ((continuous_brownG hgood ω).comp (continuous_id.min continuous_const))
  refine ((contDiff_angleObs κ hc n).continuous.comp hq).sub ?_
  have hprim := intervalIntegral.continuousOn_primitive_interval'
    (intervalIntegrable_itoGen_angleG hρL hρR hgood hc n hσhit ω) left_mem_uIcc
  refine hprim.comp_continuous (NNReal.continuous_coe.comp (continuous_id.min continuous_const))
    fun t => ?_
  rw [uIcc_of_le (σ ω).coe_nonneg]
  exact ⟨(min t (σ ω)).coe_nonneg, NNReal.coe_le_coe.2 (min_le_right _ _)⟩

/-! #### Bounds, stabilization of the localization, measurability of the angle -/

/-- A ratio `X / cutψ c ℓ` with `0 ≤ X ≤ ℓ` lies in `[0, 2]`. -/
theorem div_cutψ_mem {c : ℝ} (hc : 0 < c) {X ℓ : ℝ} (hX : 0 ≤ X) (hXℓ : X ≤ ℓ) :
    X / cutψ c ℓ ∈ Icc (0 : ℝ) 2 := by
  have hψ := cutψ_pos hc ℓ
  refine ⟨div_nonneg hX hψ.le, (div_le_iff₀ hψ).2 ?_⟩
  rcases le_or_gt (c / 2) ℓ with h | h
  · rw [cutψ_of_le hc h]; linarith
  · have := le_cutψ hc ℓ; linarith

include hρL hρR hgood in
theorem angleObs_coordG_mem {v c : ℝ} (hc : 0 < c) {ω : Ω} {t : ℝ≥0}
    (ht : t ≤ hitG G VL VR ζ v ω) :
    (Real.sqrt κ * brownG G B t ω + (coordG κ G W VL VR B t ω).1) /
      cutψ c (coordG κ G W VL VR B t ω).2 ∈ Icc (0 : ℝ) 2 := by
  by_cases hω : ω ∈ G
  · obtain ⟨-, hX0, hXℓ⟩ := coordG_mem hρL hρR hgood (κ := κ) (B := B) (W := W) hω ht
    have h1 : Real.sqrt κ * brownG G B t ω + (coordG κ G W VL VR B t ω).1 = W t ω - VL 0 t ω := by
      simp only [brownG, coordG, hω, ↓reduceIte, acCoord]; ring
    rw [h1]
    exact div_cutψ_mem hc hX0 hXℓ
  · simp only [brownG, coordG, hω, ↓reduceIte, mul_zero, Prod.fst_zero, Prod.snd_zero, add_zero,
      zero_div]
    exact ⟨le_rfl, zero_le_two⟩

include hρL hρR hgood in
theorem abs_angleObs_coordG_le {v c : ℝ} (hc : 0 < c) (n : ℕ) {ω : Ω} {t : ℝ≥0}
    (ht : t ≤ hitG G VL VR ζ v ω) :
    |angleObs κ c n (coordG κ G W VL VR B t ω, brownG G B t ω)| ≤ 2 ^ n := by
  obtain ⟨h0, h2⟩ := angleObs_coordG_mem hρL hρR hgood (W := W) (B := B) (κ := κ) hc ht
  simp only [angleObs]
  rw [abs_pow, abs_of_nonneg h0]
  exact pow_le_pow_left₀ h0 h2 n

include hgood in
/-- For a good path, the localization `σ_N` equals `τ_v` for all large `N`. -/
theorem eventually_locTime_eq (v : ℝ) (ω : Ω) :
    ∀ᶠ N : ℕ in atTop, locTime G VL VR ζ B v N ω = hitG G VL VR ζ v ω := by
  obtain ⟨M, hM⟩ := (isCompact_Icc (a := (0 : ℝ≥0)) (b := hitG G VL VR ζ v ω)).exists_bound_of_continuousOn
    (continuous_brownG hgood ω).continuousOn
  obtain ⟨N₀, hN₀⟩ := exists_nat_gt M
  filter_upwards [eventually_ge_atTop N₀] with N hN
  refine capTime_eq_of_le ?_
  by_contra hlt
  rw [not_le] at hlt
  obtain ⟨e, he⟩ : ∃ e : ℝ≥0, MathFin.exitTime (brownG G B) N ω = e :=
    WithTop.ne_top_iff_exists.1 (ne_top_of_lt hlt) |>.imp fun _ h => h.symm
  rw [he] at hlt
  obtain ⟨s, hs, hNs⟩ := (MathFin.exitTime_le_iff (continuous_brownG hgood) N e ω).1 he.le
  have hsle : s ≤ hitG G VL VR ζ v ω := hs.2.trans (WithTop.coe_le_coe.1 hlt.le)
  have := hM s ⟨zero_le, hsle⟩
  rw [Real.norm_eq_abs] at this
  have hN' : (N₀ : ℝ) ≤ N := by exact_mod_cast hN
  linarith

include hE hρL hρR hGm hGc hgood in
/-- **The modified angle is measurable** at each logarithmic time. -/
theorem measurable_angleG (u : ℝ) : Measurable (angleG G W VL VR ζ u) := by
  set T : ℝ≥0 := Real.toNNReal (exp u ^ 2 / 8)
  have hhitT : ∀ ω, hitG G VL VR ζ u ω ≤ T := fun ω => by
    by_cases hω : ω ∈ G
    · obtain ⟨hP, hBc, -⟩ := hgood ω hω
      simp only [hitG, hω, ↓reduceIte]
      rw [← NNReal.coe_le_coe, Real.coe_toNNReal _ (by positivity)]
      have := eight_mul_hitTime_le hP hBc hρL hρR u
      linarith
    · simp only [hitG, hω, ↓reduceIte]; exact zero_le
  have hτ := isStoppingTime_hitG hE hρL hρR hGm hGc hgood u
  have h1 := measurable_coordG_stopped hE hρL hρR hGm hGc hgood hτ (fun ω => le_rfl) T
  have h2 := measurable_brownG_stopped hE hGm hGc hgood hτ T
  have h3 : Measurable[Ito.nullAugmented 𝓕 P T] fun ω => angleObs κ (exp u) 1
      (coordG κ G W VL VR B (min T (hitG G VL VR ζ u ω)) ω,
        brownG G B (min T (hitG G VL VR ζ u ω)) ω) :=
    (contDiff_angleObs κ (exp_pos u) 1).continuous.measurable.comp (h1.prodMk h2)
  have heq : angleG G W VL VR ζ u = fun ω => angleObs κ (exp u) 1
      (coordG κ G W VL VR B (min T (hitG G VL VR ζ u ω)) ω,
        brownG G B (min T (hitG G VL VR ζ u ω)) ω) := by
    funext ω
    rw [min_eq_right (hhitT ω)]
    by_cases hω : ω ∈ G
    · obtain ⟨hP, hBc, -⟩ := hgood ω hω
      have := angleObs_hitTime hP hBc hρL hρR (κ := κ) (exp_pos u) 1 (c := exp u) (u := u)
        (by linarith [exp_pos u])
      simp only [coordG, brownG, hitG, angleG, hω, ↓reduceIte, pow_one] at this ⊢
      exact this.symm
    · simp [coordG, brownG, angleG, hω, angleObs]
  rw [heq]
  exact h3.mono ((Ito.nullAugmented 𝓕 P).le T) le_rfl


include hρL hρR hgood in
/-- The generator integral between `τ_w ∧ σ_N` and `σ_N` is bounded uniformly in `N` and `ω`. -/
theorem abs_integral_itoGen_angleG_le (hκ : 0 ≤ κ) {w v : ℝ} (hwv : w ≤ v) (n N : ℕ) (ω : Ω) :
    |∫ s in (min (hitG G VL VR ζ w ω) (locTime G VL VR ζ B v N ω) : ℝ≥0)..
        (locTime G VL VR ζ B v N ω : ℝ),
      Ito.itoGen (angleObs κ (exp w) n) (coordG κ G W VL VR B s.toNNReal ω, brownG G B s.toNNReal ω)
        (densG ρL ρR G W VL VR s ω)| ≤
      (v - w) * (|Jacobi.dcoef κ (ρL 0 + 2) n| + |Jacobi.ccoef κ (ρL 0 + 2) (ρR 0 + 2) n|) := by
  have hC : 0 ≤ (v - w) * (|Jacobi.dcoef κ (ρL 0 + 2) n| + |Jacobi.ccoef κ (ρL 0 + 2) (ρR 0 + 2) n|) :=
    mul_nonneg (sub_nonneg.2 hwv) (by positivity)
  set σ := locTime G VL VR ζ B v N ω
  by_cases hle : σ ≤ hitG G VL VR ζ w ω
  · rw [min_eq_right hle, intervalIntegral.integral_same, abs_zero]; exact hC
  rw [not_le] at hle
  rw [min_eq_left hle.le]
  by_cases hω : ω ∈ G
  · obtain ⟨hP, hBc, -⟩ := hgood ω hω
    have hσv : σ ≤ hitG G VL VR ζ v ω := locTime_le_hitG v N ω
    simp only [hitG, hω, ↓reduceIte] at hle hσv
    obtain ⟨u₂, hwu, huv, heq⟩ := integral_itoGen_angleObs_upTo hP hBc hρL hρR hκ hle hσv n
    simp only [coordG, brownG, densG, hitG, hω, ↓reduceIte]
    rw [heq]
    refine (abs_integral_gen_le κ _ _ n (logAngle_spec hP hBc (fun i => by fin_cases i; exact hρL)
      (fun i => by fin_cases i; exact hρR)).2.1 hwu).trans ?_
    exact mul_le_mul_of_nonneg_right (by linarith) (by positivity)
  · exfalso
    have := locTime_le_hitG (G := G) (VL := VL) (VR := VR) (ζ := ζ) (B := B) v N ω
    simp only [hitG, hω, ↓reduceIte] at this hle
    exact absurd (lt_of_lt_of_le hle this) (lt_irrefl 0)

/-! #### The martingale increment between `τ_w ∧ σ_N` and `σ_N` -/

include hρL hρR hgood in
theorem hitG_le_bound (u : ℝ) (ω : Ω) : hitG G VL VR ζ u ω ≤ Real.toNNReal (exp u ^ 2 / 8) := by
  by_cases hω : ω ∈ G
  · obtain ⟨hP, hBc, -⟩ := hgood ω hω
    simp only [hitG, hω, ↓reduceIte]
    rw [← NNReal.coe_le_coe, Real.coe_toNNReal _ (by positivity)]
    have := eight_mul_hitTime_le hP hBc hρL hρR u
    linarith
  · simp only [hitG, hω, ↓reduceIte]; exact zero_le

/-- The localized Itô process of the angle (`martingale_angle`). -/
def angleMart (κ c : ℝ) (n : ℕ) (ρL ρR : Fin 1 → ℝ) (G : Set Ω) (W : ℝ≥0 → Ω → ℝ)
    (VL VR : Fin 1 → ℝ≥0 → Ω → ℝ) (B : ℝ≥0 → Ω → ℝ) (σ : Ω → ℝ≥0) (t : ℝ≥0) (ω : Ω) : ℝ :=
  angleObs κ c n (coordG κ G W VL VR B (min t (σ ω)) ω, brownG G B (min t (σ ω)) ω) -
    ∫ s in (0 : ℝ)..(min t (σ ω) : ℝ≥0),
      Ito.itoGen (angleObs κ c n) (coordG κ G W VL VR B s.toNNReal ω, brownG G B s.toNNReal ω)
        (densG ρL ρR G W VL VR s ω)

include hρL hρR hgood in
theorem angleMart_sub {v c : ℝ} (hc : 0 < c) (n : ℕ) {σ : Ω → ℝ≥0}
    (hσhit : ∀ ω, σ ω ≤ hitG G VL VR ζ v ω) (ω : Ω) {t₁ t₂ : ℝ≥0} (h1 : t₁ ≤ σ ω)
    (h2 : σ ω ≤ t₂) :
    angleMart κ c n ρL ρR G W VL VR B σ t₂ ω - angleMart κ c n ρL ρR G W VL VR B σ t₁ ω =
      angleObs κ c n (coordG κ G W VL VR B (σ ω) ω, brownG G B (σ ω) ω) -
        angleObs κ c n (coordG κ G W VL VR B t₁ ω, brownG G B t₁ ω) -
        ∫ s in (t₁ : ℝ)..(σ ω : ℝ), Ito.itoGen (angleObs κ c n)
          (coordG κ G W VL VR B s.toNNReal ω, brownG G B s.toNNReal ω) (densG ρL ρR G W VL VR s ω) := by
  have hint := intervalIntegrable_itoGen_angleG hρL hρR hgood (W := W) (B := B) (κ := κ) hc n
    hσhit ω
  have hint1 : IntervalIntegrable (fun s => Ito.itoGen (angleObs κ c n)
      (coordG κ G W VL VR B s.toNNReal ω, brownG G B s.toNNReal ω) (densG ρL ρR G W VL VR s ω))
      volume 0 (t₁ : ℝ) :=
    hint.mono_set (by
      rw [uIcc_of_le t₁.coe_nonneg, uIcc_of_le (σ ω).coe_nonneg]
      exact Icc_subset_Icc le_rfl (by exact_mod_cast h1))
  simp only [angleMart, min_eq_right h2, min_eq_left h1]
  rw [← intervalIntegral.integral_interval_sub_left hint hint1]
  ring

include hρL hρR hgood in
/-- The increment is bounded uniformly in `N` and `ω`. -/
theorem abs_angleMart_sub_le (hκ : 0 ≤ κ) {w v : ℝ} (hwv : w ≤ v) (n N : ℕ) (ω : Ω) {T : ℝ≥0}
    (hT : locTime G VL VR ζ B v N ω ≤ T) :
    |angleMart κ (exp w) n ρL ρR G W VL VR B (locTime G VL VR ζ B v N) T ω -
      angleMart κ (exp w) n ρL ρR G W VL VR B (locTime G VL VR ζ B v N)
        (min (hitG G VL VR ζ w ω) (locTime G VL VR ζ B v N ω)) ω| ≤
      2 ^ n + 2 ^ n +
        (v - w) * (|Jacobi.dcoef κ (ρL 0 + 2) n| + |Jacobi.ccoef κ (ρL 0 + 2) (ρR 0 + 2) n|) := by
  have hσhit : ∀ ω, locTime G VL VR ζ B v N ω ≤ hitG G VL VR ζ v ω := locTime_le_hitG v N
  rw [angleMart_sub hρL hρR hgood (exp_pos w) n hσhit ω (min_le_right _ _) hT]
  have h1 := abs_angleObs_coordG_le hρL hρR hgood (W := W) (B := B) (κ := κ) (exp_pos w) n
    (hσhit ω)
  have h2 := abs_angleObs_coordG_le hρL hρR hgood (W := W) (B := B) (κ := κ) (exp_pos w) n
    ((min_le_right (hitG G VL VR ζ w ω) _).trans (hσhit ω))
  have h3 := abs_integral_itoGen_angleG_le hρL hρR hgood (W := W) (B := B) hκ hwv n N ω
  refine (abs_sub _ _).trans (add_le_add ((abs_sub _ _).trans (add_le_add h1 h2)) h3)

include hρL hρR hgood in
theorem hitG_mono {u₁ u₂ : ℝ} (hu : u₁ ≤ u₂) (ω : Ω) : hitG G VL VR ζ u₁ ω ≤ hitG G VL VR ζ u₂ ω := by
  by_cases hω : ω ∈ G
  · obtain ⟨hP, hBc, -⟩ := hgood ω hω
    simp only [hitG, hω, ↓reduceIte]
    exact hitTime_mono hP hBc hρL hρR hu
  · simp only [hitG, hω, ↓reduceIte]; exact le_rfl

include hρL hρR hgood in
/-- **On a good path the increment is the Jacobi martingale-problem increment** of the angle. -/
theorem increment_eq_of_good (hκ : 0 ≤ κ) {w v : ℝ} (hwv : w ≤ v) (n : ℕ) {ω : Ω} (hω : ω ∈ G) :
    angleObs κ (exp w) n (coordG κ G W VL VR B (hitG G VL VR ζ v ω) ω,
        brownG G B (hitG G VL VR ζ v ω) ω) -
      angleObs κ (exp w) n (coordG κ G W VL VR B (hitG G VL VR ζ w ω) ω,
        brownG G B (hitG G VL VR ζ w ω) ω) -
      ∫ s in (hitG G VL VR ζ w ω : ℝ)..(hitG G VL VR ζ v ω : ℝ), Ito.itoGen (angleObs κ (exp w) n)
        (coordG κ G W VL VR B s.toNNReal ω, brownG G B s.toNNReal ω) (densG ρL ρR G W VL VR s ω) =
    angleG G W VL VR ζ v ω ^ n - angleG G W VL VR ζ w ω ^ n -
      ∫ x in w..v, Jacobi.gen κ (ρL 0 + 2) (ρR 0 + 2) (fun y => y ^ n) (angleG G W VL VR ζ x ω) := by
  obtain ⟨hP, hBc, -⟩ := hgood ω hω
  have hUc := (logAngle_spec hP hBc (fun i => by fin_cases i; exact hρL)
    (fun i => by fin_cases i; exact hρR)).1
  obtain ⟨hvζ, hve⟩ := hitTime_lt_and_sepN hP hBc hρL hρR v
  have hcv : exp w / 2 ≤ exp v := by linarith [exp_le_exp.2 hwv, exp_pos w]
  have hcw : exp w / 2 ≤ exp w := by linarith [exp_pos w]
  simp only [coordG, brownG, densG, hitG, angleG, hω, ↓reduceIte]
  rw [angleObs_hitTime hP hBc hρL hρR (exp_pos w) n (u := v) hcv,
    angleObs_hitTime hP hBc hρL hρR (exp_pos w) n (u := w) hcw,
    integral_itoGen_angleObs hP hκ hwv hvζ hve.ge hUc n]

/-- The bounded factors `A_{t ∧ σ}` (cut off at `c`) used for the products of earlier angles. -/
def angleFac (κ c : ℝ) (G : Set Ω) (W : ℝ≥0 → Ω → ℝ) (VL VR : Fin 1 → ℝ≥0 → Ω → ℝ)
    (B : ℝ≥0 → Ω → ℝ) (σ : Ω → ℝ≥0) (t : ℝ≥0) (ω : Ω) : ℝ :=
  angleObs κ c 1 (coordG κ G W VL VR B (min t (σ ω)) ω, brownG G B (min t (σ ω)) ω)

include hE hρL hρR hGm hGc hgood in
theorem isStronglyProgressive_angleFac {v c : ℝ} (hc : 0 < c) {σ : Ω → ℝ≥0}
    (hσ : IsStoppingTime (Ito.nullAugmented 𝓕 P) fun ω => (σ ω : WithTop ℝ≥0))
    (hσhit : ∀ ω, σ ω ≤ hitG G VL VR ζ v ω) :
    IsStronglyProgressive (Ito.nullAugmented 𝓕 P) (angleFac κ c G W VL VR B σ) := by
  refine isStronglyProgressive_of_rightContinuous (fun t => ?_) (fun ω t => ?_)
  · exact ((contDiff_angleObs κ hc 1).continuous.measurable.comp
      ((measurable_coordG_stopped hE hρL hρR hGm hGc hgood hσ hσhit t).prodMk
        (measurable_brownG_stopped hE hGm hGc hgood hσ t))).stronglyMeasurable
  · exact (((contDiff_angleObs κ hc 1).continuous.comp
      ((continuous_coordG_stopped hρL hρR hgood hσhit ω).prodMk
        ((continuous_brownG hgood ω).comp (continuous_id.min continuous_const))))).continuousWithinAt

include hρL hρR hgood in
theorem abs_angleFac_le {v c : ℝ} (hc : 0 < c) {σ : Ω → ℝ≥0} (hσhit : ∀ ω, σ ω ≤ hitG G VL VR ζ v ω)
    (t : ℝ≥0) (ω : Ω) : |angleFac κ c G W VL VR B σ t ω| ≤ 2 := by
  have := abs_angleObs_coordG_le hρL hρR hgood (W := W) (B := B) (κ := κ) hc 1
    ((min_le_right t (σ ω)).trans (hσhit ω))
  rw [pow_one] at this
  exact this

include hρL hρR hgood in
theorem angleObs_hitG_eq {c : ℝ} (hc : 0 < c) (n : ℕ) {u : ℝ} (hcu : c / 2 ≤ exp u) {ω : Ω}
    (hω : ω ∈ G) :
    angleObs κ c n (coordG κ G W VL VR B (hitG G VL VR ζ u ω) ω, brownG G B (hitG G VL VR ζ u ω) ω) =
      angleG G W VL VR ζ u ω ^ n := by
  obtain ⟨hP, hBc, -⟩ := hgood ω hω
  simp only [coordG, brownG, hitG, angleG, hω, ↓reduceIte]
  exact angleObs_hitTime hP hBc hρL hρR hc n hcu

include hE hρL hρR hGm hGc hgood in
/-- **The martingale-problem identity** of `IsJacobiMP` for the modified angle. -/
theorem integral_jacobiIncrement_eq_zero (hκ : 0 < κ) {m : ℕ} (s : Fin m → ℝ) (k : Fin m → ℕ)
    (n : ℕ) {w v : ℝ} (hsw : ∀ i, s i ≤ w) (hwv : w ≤ v) :
    ∫ ω, (∏ i, angleG G W VL VR ζ (s i) ω ^ k i) *
      (angleG G W VL VR ζ v ω ^ n - angleG G W VL VR ζ w ω ^ n -
        ∫ x in w..v, Jacobi.gen κ (ρL 0 + 2) (ρR 0 + 2) (fun y => y ^ n)
          (angleG G W VL VR ζ x ω)) ∂P = 0 := by
  have hP : IsProbabilityMeasure P := hE.1.isProbabilityMeasure'
  set 𝓖 := Ito.nullAugmented 𝓕 P
  set c' : ℝ := exp (-(∑ i, |s i|)) with hc'
  have hc'pos : 0 < c' := exp_pos _
  have hc'le : ∀ i, c' / 2 ≤ exp (s i) := fun i => by
    have h1 : |s i| ≤ ∑ j, |s j| :=
      Finset.single_le_sum (f := fun j => |s j|) (fun j _ => abs_nonneg _) (Finset.mem_univ i)
    have h2 : -(∑ j, |s j|) ≤ s i := by linarith [neg_abs_le (s i)]
    have := exp_le_exp.2 h2
    linarith [exp_pos (-(∑ j, |s j|))]
  set σ : ℕ → Ω → ℝ≥0 := fun N => locTime G VL VR ζ B v N with hσdef
  set T : ℝ≥0 := Real.toNNReal (exp v ^ 2 / 8) with hTdef
  have hσhit : ∀ N ω, σ N ω ≤ hitG G VL VR ζ v ω := fun N => locTime_le_hitG v N
  have hσT : ∀ N ω, σ N ω ≤ T := fun N ω =>
    (hσhit N ω).trans (hitG_le_bound hρL hρR hgood v ω)
  have hσst : ∀ N, IsStoppingTime 𝓖 fun ω => (σ N ω : WithTop ℝ≥0) := fun N =>
    isStoppingTime_locTime hE hρL hρR hGm hGc hgood v N
  set M : ℕ → ℝ≥0 → Ω → ℝ := fun N => angleMart κ (exp w) n ρL ρR G W VL VR B (σ N) with hMdef
  have hM : ∀ N, Martingale (M N) 𝓖 P := fun N =>
    martingale_angle hE hρL hρR hGm hGc hgood v (exp_pos w) n N
  have hMc : ∀ N ω, Continuous fun t => M N t ω := fun N ω =>
    continuous_martingale_angle hρL hρR hgood v (exp_pos w) n N ω
  set r : ℕ → Ω → ℝ≥0 := fun N ω => min (hitG G VL VR ζ w ω) (σ N ω) with hrdef
  have hr : ∀ N, IsStoppingTime 𝓖 fun ω => (r N ω : WithTop ℝ≥0) := fun N => by
    simp_rw [hrdef, WithTop.coe_min]
    exact (isStoppingTime_hitG hE hρL hρR hGm hGc hgood w).min (hσst N)
  -- the bounded factor
  set Z : ℕ → Ω → ℝ := fun N ω => ∏ i, angleFac κ c' G W VL VR B (σ N)
    (min (hitG G VL VR ζ (s i) ω) (σ N ω)) ω ^ k i with hZdef
  have hZm : ∀ N, StronglyMeasurable[(hr N).measurableSpace] (Z N) := by
    intro N
    have hprog := isStronglyProgressive_angleFac hE hρL hρR hGm hGc hgood hc'pos (hσst N)
      (hσhit N)
    have hfac : ∀ i, Measurable[(hr N).measurableSpace] fun ω => angleFac κ c' G W VL VR B (σ N)
        (min (hitG G VL VR ζ (s i) ω) (σ N ω)) ω := by
      intro i
      have hτ : IsStoppingTime 𝓖 fun ω =>
          ((min (hitG G VL VR ζ (s i) ω) (σ N ω) : ℝ≥0) : WithTop ℝ≥0) := by
        simp_rw [WithTop.coe_min]
        exact (isStoppingTime_hitG hE hρL hρR hGm hGc hgood (s i)).min (hσst N)
      have h1 := measurable_stoppedValue hprog hτ
      rw [stoppedValue_coe] at h1
      refine h1.mono (hτ.measurableSpace_mono (hr N) fun ω => ?_) le_rfl
      exact WithTop.coe_le_coe.2 (min_le_min_right _ (hitG_mono hρL hρR hgood (hsw i) ω))
    exact (Finset.measurable_prod _ fun i _ => (hfac i).pow_const (k i)).stronglyMeasurable
  have hZb : ∀ N ω, |Z N ω| ≤ 2 ^ (∑ i, k i) := by
    intro N ω
    simp only [hZdef]
    rw [Finset.abs_prod, ← Finset.prod_pow_eq_pow_sum]
    refine Finset.prod_le_prod₀ (fun i _ => abs_nonneg _) fun i _ => ?_
    rw [abs_pow]
    exact pow_le_pow_left₀ (abs_nonneg _) (abs_angleFac_le hρL hρR hgood hc'pos (hσhit N) _ ω) _
  -- optional sampling: each approximating integral vanishes
  have h0 : ∀ N, ∫ ω, Z N ω * (M N T ω - M N (r N ω) ω) ∂P = 0 := fun N => by
    have := integral_mul_sub_stoppedValue_eq_zero (hM N) (hMc N) (hr N) (T := T)
      (fun ω => WithTop.coe_le_coe.2 ((min_le_right _ _).trans (hσT N ω))) (hZm N) (hZb N)
    rwa [stoppedValue_coe] at this
  -- domination
  set Cg := |Jacobi.dcoef κ (ρL 0 + 2) n| + |Jacobi.ccoef κ (ρL 0 + 2) (ρR 0 + 2) n|
  set Cb : ℝ := 2 ^ (∑ i, k i) * (2 ^ n + 2 ^ n + (v - w) * Cg)
  have hbound : ∀ N ω, ‖Z N ω * (M N T ω - M N (r N ω) ω)‖ ≤ Cb := by
    intro N ω
    rw [Real.norm_eq_abs, abs_mul]
    exact mul_le_mul (hZb N ω)
      (abs_angleMart_sub_le hρL hρR hgood hκ.le hwv n N ω (hσT N ω)) (abs_nonneg _)
      (by positivity)
  have hmeas : ∀ N, AEStronglyMeasurable (fun ω => Z N ω * (M N T ω - M N (r N ω) ω)) P := by
    intro N
    have hZ : AEStronglyMeasurable (Z N) P :=
      ((hZm N).mono (hr N).measurableSpace_le).aestronglyMeasurable
    have hMT : AEStronglyMeasurable (M N T) P := (((hM N).1 T).mono (𝓖.le T)).aestronglyMeasurable
    have hprog := isStronglyProgressive_of_rightContinuous (hM N).1
      (fun ω t => (hMc N ω).continuousWithinAt)
    have hMr := (measurable_stoppedValue hprog (hr N)).mono (hr N).measurableSpace_le le_rfl
    rw [stoppedValue_coe] at hMr
    exact hZ.mul (hMT.sub (hMr.aestronglyMeasurable (μ := P)))
  -- the limit on the good event
  have hlim : ∀ᵐ ω ∂P, Tendsto (fun N => Z N ω * (M N T ω - M N (r N ω) ω)) atTop
      (𝓝 ((∏ i, angleG G W VL VR ζ (s i) ω ^ k i) *
        (angleG G W VL VR ζ v ω ^ n - angleG G W VL VR ζ w ω ^ n -
          ∫ x in w..v, Jacobi.gen κ (ρL 0 + 2) (ρR 0 + 2) (fun y => y ^ n)
            (angleG G W VL VR ζ x ω)))) := by
    filter_upwards [show ∀ᵐ ω ∂P, ω ∈ G from by rw [ae_iff]; exact hGc] with ω hω
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [eventually_locTime_eq hgood v ω] with N hN
    have hN' : σ N ω = hitG G VL VR ζ v ω := hN
    have hwv' := hitG_mono hρL hρR hgood hwv ω
    have hrN : r N ω = hitG G VL VR ζ w ω := by simp only [hrdef, hN', min_eq_left hwv']
    have hinc : M N T ω - M N (r N ω) ω =
        angleG G W VL VR ζ v ω ^ n - angleG G W VL VR ζ w ω ^ n -
          ∫ x in w..v, Jacobi.gen κ (ρL 0 + 2) (ρR 0 + 2) (fun y => y ^ n)
            (angleG G W VL VR ζ x ω) := by
      simp only [hMdef]
      rw [angleMart_sub hρL hρR hgood (exp_pos w) n (hσhit N) ω (min_le_right _ _) (hσT N ω)]
      rw [show r N ω = min (hitG G VL VR ζ w ω) (σ N ω) from rfl] at hrN
      rw [hrN, hN']
      exact increment_eq_of_good hρL hρR hgood hκ.le hwv n hω
    have hZN : Z N ω = ∏ i, angleG G W VL VR ζ (s i) ω ^ k i := by
      simp only [hZdef, angleFac]
      refine Finset.prod_congr rfl fun i _ => ?_
      have hle : hitG G VL VR ζ (s i) ω ≤ σ N ω :=
        hN' ▸ hitG_mono hρL hρR hgood ((hsw i).trans hwv) ω
      rw [min_eq_left hle, min_eq_left hle, angleObs_hitG_eq hρL hρR hgood hc'pos 1 (hc'le i) hω,
        pow_one]
    rw [hZN, hinc]
  have hDCT := tendsto_integral_of_dominated_convergence (fun _ => Cb) hmeas (integrable_const Cb)
    (fun N => ae_of_all _ (hbound N)) hlim
  simp only [h0] at hDCT
  exact tendsto_nhds_unique hDCT tendsto_const_nhds

include hE hρL hρR hGm hGc hgood in
/-- **The modified logarithmic-clock angle solves the Jacobi martingale problem.** -/
theorem isJacobiMP_angleG (hκ : 0 < κ) :
    Jacobi.IsJacobiMP κ (ρL 0 + 2) (ρR 0 + 2) P (angleG G W VL VR ζ) := by
  have hρL' : ∀ i, -2 < ρL i := fun i => by fin_cases i; exact hρL
  have hρR' : ∀ i, -2 < ρR i := fun i => by fin_cases i; exact hρR
  refine ⟨fun u ω => ?_, fun ω => ?_, measurable_angleG hE hρL hρR hGm hGc hgood,
    fun m s k n w v hsw hwv => integral_jacobiIncrement_eq_zero hE hρL hρR hGm hGc hgood hκ s k n
      hsw hwv⟩
  · by_cases hω : ω ∈ G
    · obtain ⟨hPω, hBc, -⟩ := hgood ω hω
      simp only [angleG, hω, ↓reduceIte]
      exact (logAngle_spec hPω hBc hρL' hρR').2.1 u
    · simp only [angleG, hω, ↓reduceIte]; exact ⟨le_rfl, zero_le_one⟩
  · by_cases hω : ω ∈ G
    · obtain ⟨hPω, hBc, -⟩ := hgood ω hω
      simp only [angleG, hω, ↓reduceIte]
      exact (logAngle_spec hPω hBc hρL' hρR').1
    · simp only [angleG, hω, ↓reduceIte]; exact continuous_const

omit hρL hρR in
include hE in
/-- A measurable full-measure event of good paths. -/
theorem exists_good : ∃ G : Set Ω, MeasurableSet G ∧ P Gᶜ = 0 ∧
    ∀ ω ∈ G, IsGoodTwoSeed κ ρL ρR W VL VR B ζ ω := by
  have hae : ∀ᵐ ω ∂P, IsGoodTwoSeed κ ρL ρR W VL VR B ζ ω := by
    filter_upwards [hE.2.2.2.2, hE.1.1.cont, hE.1.1.eval_zero_ae_eq_zero] with ω h1 h2 h3
    exact ⟨h1, h2, h3⟩
  refine ⟨(toMeasurable P {ω | ¬ IsGoodTwoSeed κ ρL ρR W VL VR B ζ ω})ᶜ,
    (measurableSet_toMeasurable _ _).compl, ?_, fun ω hω => ?_⟩
  · rw [compl_compl, measure_toMeasurable]; exact ae_iff.1 hae
  · by_contra h; exact hω (subset_toMeasurable _ _ h)

end Process

/-- **The logarithmic-clock angle of a two-seed evolution is a Jacobi diffusion** (martingale-problem
form): for an integrated evolution with force points `0⁻, 0⁺`, weights `ρ_L, ρ_R > −2` and `κ > 0`, the angle
`U_u = (W − V^L)/(V^R − V^L)` at the hitting time of the level `e^u` (`logAngle`) agrees almost surely, for
all `u`, with a process solving `Jacobi.IsJacobiMP κ (ρ_L + 2) (ρ_R + 2)`. -/
theorem exists_isJacobiMP_logAngle {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ} {κ : ℝ} {ρL ρR : Fin 1 → ℝ} {W : ℝ≥0 → Ω → ℝ}
    {VL VR : Fin 1 → ℝ≥0 → Ω → ℝ} {B : ℝ≥0 → Ω → ℝ} {ζ : Ω → ℝ≥0∞}
    (hE : IsIntegratedSLEEvolution κ (fun _ => 0) (fun _ => 0) ρL ρR P 𝓕 W VL VR B ζ)
    (hκ : 0 < κ) (hρL : -2 < ρL 0) (hρR : -2 < ρR 0) :
    ∃ U : ℝ → Ω → ℝ, Jacobi.IsJacobiMP κ (ρL 0 + 2) (ρR 0 + 2) P U ∧
      ∀ᵐ ω ∂P, ∀ u, U u ω = logAngle (W · ω) (fun i t => VL i t ω) (fun i t => VR i t ω) (ζ ω) u := by
  obtain ⟨G, hGm, hGc, hgood⟩ := exists_good hE
  refine ⟨angleG G W VL VR ζ, isJacobiMP_angleG hE hρL hρR hGm hGc hgood hκ, ?_⟩
  filter_upwards [show ∀ᵐ ω ∂P, ω ∈ G from by rw [ae_iff]; exact hGc] with ω hω u
  simp only [angleG, hω, ↓reduceIte]

end TwoSeed

end Sec2

end InteractingSLE
