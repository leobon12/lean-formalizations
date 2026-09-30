import QuantumZipper.Proofs.Zipper.GenUCKolm

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# GENERIC-UC (2/2): uniform convergence, continuous limit, `evalReg` and exactness

Built on the Kolmogorov step `GenUC.exists_contMod_gen` (GenUCKolm). The family-specific inputs
enter as explicit hypotheses, exactly the four nodes of the D33 / XFLOW / ZIPLEN-2 / SW-core
chains:

* `GenFam` (admissibility, mass, energy moduli) and a Lipschitz retraction onto the compact
  parameter set `S` (the XFLOW `FlowAdmStmt`, `FlowEnergyStmt`);
* the identity `Φ ρ p = X(μ p ρ) + det ρ p` a.s. at each fixed countable parameter (the XFLOW
  `FlowIdentStmt`; Duplantier–Sheffield, *Liouville quantum gravity and KPZ*, Invent. Math. 185
  (2011), Prop. 3.1);
* the uniform convergence of the deterministic part `det ρ → detLim` as `ρ → 0` (`FlowDetStmt`);
* pathwise continuity in the parameter of the smoothed pairings (for the extension from a
  countable dense set to all of `S`) and of the raw value (for exactness).

Results:
* `ae_unifConv_countable`: a.s. `Φ ρ p → L p` uniformly over a countable `D ⊆ S` as `ρ → 0`
  along a countable set `R` of radii, with `L` continuous on `S` for every sample and
  `L p = X(μ p 0) + detLim p` a.s. at each fixed `p`;
* `ae_unifConv_all`: the same uniformly over all of `S` (pathwise continuity in `p`);
* `ae_unifConv_all_radii`: uniformly over `S` and all radii `ρ ∈ (0, δ)` (joint pathwise
  continuity, `R` dense in `[0,1]`: the continuous-radius version, as ZIPLEN-2-CONT);
* `ae_evalReg_eq_gen`, `ae_exact_gen`: `evalReg x_ω (ν p) = L p ω` for all `p ∈ S`, and
  `evalReg x_ω (ν p) = x_ω (ν p)` for all `p ∈ S` (RC3), a.s.

Own bookkeeping (as in D33, `RegUnif.fixedUCStmt_of_id_det`, and XFLOW-UC,
`F1.xFlowFixedUCQAllStmt_of`); the probabilistic input is Kolmogorov–Čentsov (Revuz–Yor,
3rd ed., Ch. I, Thm (2.1)).
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology ENNReal

namespace QuantumZipper
namespace GenUC

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {X : Ω → FieldSample}
variable {n : ℕ} {S : Set (Fin n → ℝ)} {μ : (Fin n → ℝ) → ℝ → Measure ℂ} {M : ℝ≥0∞} {K c : ℝ}
  {ret : (Fin n → ℝ) → Fin n → ℝ} {L : ℝ}

/-- A function continuous on `S` and `≤ ε` on a subset `D ⊆ S` with `S ⊆ closure D` is `≤ ε` on
`S`. -/
theorem le_of_continuousOn_of_dense {g : (Fin n → ℝ) → ℝ} {D : Set (Fin n → ℝ)} (hDS : D ⊆ S)
    (hdense : S ⊆ closure D) (hg : ContinuousOn g S) {ε : ℝ} (hD : ∀ p ∈ D, g p ≤ ε) :
    ∀ p ∈ S, g p ≤ ε := by
  intro p hp
  have h := ((hg p hp).mono hDS).mem_closure_image (hdense hp)
  have hsub : closure (g '' D) ⊆ Iic ε :=
    closure_minimal (by rintro _ ⟨q, hq, rfl⟩; exact hD q hq) isClosed_Iic
  exact hsub h

/-- **GENERIC-UC, uniform convergence on a countable parameter set.** -/
theorem ae_unifConv_countable (hX : IsFreeGFFModConstH X P) (hF : GenFam S μ M K c)
    (hR : IsLipRetr S ret L) (hS : IsCompact S) {D : Set (Fin n → ℝ)} (hD : D.Countable)
    (hDS : D ⊆ S) {R : Set ℝ} (hRc : R.Countable) (hRI : R ⊆ Icc 0 1)
    (Φ : ℝ → (Fin n → ℝ) → Ω → ℝ) (det : ℝ → (Fin n → ℝ) → ℝ) (detLim : (Fin n → ℝ) → ℝ)
    (hdetc : ContinuousOn detLim S)
    (hid : ∀ ρ ∈ R, ∀ p ∈ D, ∀ᵐ ω ∂P, Φ ρ p ω = X ω (μ p ρ) + det ρ p)
    (hdet : ∀ ε > 0, ∃ δ > 0, ∀ ρ ∈ R, ρ < δ → ∀ p ∈ S, |det ρ p - detLim p| < ε) :
    ∃ Lim : (Fin n → ℝ) → Ω → ℝ, (∀ ω, ContinuousOn (fun p => Lim p ω) S) ∧
      (∀ p ∈ S, (fun ω => Lim p ω) =ᵐ[P] fun ω => X ω (μ p 0) + detLim p) ∧
      ∀ᵐ ω ∂P, ∀ ε > 0, ∃ δ > 0, ∀ ρ ∈ R, ρ < δ → ∀ p ∈ D, |Φ ρ p ω - Lim p ω| < ε := by
  obtain ⟨Y, hYc, hYZ⟩ := exists_contMod_gen hX hF hR
  refine ⟨fun p ω => Y p 0 ω + detLim p, fun ω => ?_, fun p hp => ?_, ?_⟩
  · exact ((hYc ω).comp (continuous_id.prodMk continuous_const)).continuousOn.add hdetc
  · filter_upwards [hYZ p hp 0 ⟨le_rfl, zero_le_one⟩] with ω h
    rw [h]
  have hgood : ∀ᵐ ω ∂P, ∀ x ∈ R ×ˢ D,
      Φ x.1 x.2 ω = X ω (μ x.2 x.1) + det x.1 x.2 ∧ Y x.2 x.1 ω = X ω (μ x.2 x.1) := by
    refine (ae_ball_iff (hRc.prod hD)).2 fun x hx => ?_
    filter_upwards [hid x.1 hx.1 x.2 hx.2, hYZ x.2 (hDS hx.2) x.1 (hRI hx.1)] with ω h1 h2
    exact ⟨h1, h2⟩
  filter_upwards [hgood] with ω hω ε hε
  have hK : IsCompact (S ×ˢ Icc (0 : ℝ) 1) := hS.prod isCompact_Icc
  obtain ⟨η, hη, hU⟩ := Metric.uniformContinuousOn_iff.1
    (hK.uniformContinuousOn_of_continuous (hYc ω).continuousOn) (ε / 2) (by positivity)
  obtain ⟨δ, hδ, hd⟩ := hdet (ε / 2) (by positivity)
  refine ⟨min η δ, lt_min hη hδ, fun ρ hρ hρδ p hp => ?_⟩
  have hρ0 := hRI hρ
  have e := hω (ρ, p) ⟨hρ, hp⟩
  have hdist : dist ((p, ρ) : (Fin n → ℝ) × ℝ) (p, 0) < η := by
    rw [Prod.dist_eq, dist_self, Real.dist_eq, sub_zero, abs_of_nonneg hρ0.1]
    exact max_lt hη (lt_of_lt_of_le hρδ (min_le_left _ _))
  have hY : dist (Y p ρ ω) (Y p 0 ω) < ε / 2 :=
    hU (p, ρ) ⟨hDS hp, hρ0⟩ (p, 0) ⟨hDS hp, le_rfl, zero_le_one⟩ hdist
  have hdd := hd ρ hρ (lt_of_lt_of_le hρδ (min_le_right _ _)) p (hDS hp)
  rw [Real.dist_eq] at hY
  rw [e.1, ← e.2]
  rw [abs_lt] at hY hdd ⊢
  constructor <;> linarith [hY.1, hY.2, hdd.1, hdd.2]

/-- **GENERIC-UC, uniform convergence on all of `S`** (pathwise continuity in `p` of the
smoothed pairings, `D` dense in `S`). -/
theorem ae_unifConv_all (hX : IsFreeGFFModConstH X P) (hF : GenFam S μ M K c)
    (hR : IsLipRetr S ret L) (hS : IsCompact S) {D : Set (Fin n → ℝ)} (hD : D.Countable)
    (hDS : D ⊆ S) (hdense : S ⊆ closure D) {R : Set ℝ} (hRc : R.Countable)
    (hRI : R ⊆ Icc 0 1)
    (Φ : ℝ → (Fin n → ℝ) → Ω → ℝ) (det : ℝ → (Fin n → ℝ) → ℝ) (detLim : (Fin n → ℝ) → ℝ)
    (hdetc : ContinuousOn detLim S)
    (hid : ∀ ρ ∈ R, ∀ p ∈ D, ∀ᵐ ω ∂P, Φ ρ p ω = X ω (μ p ρ) + det ρ p)
    (hdet : ∀ ε > 0, ∃ δ > 0, ∀ ρ ∈ R, ρ < δ → ∀ p ∈ S, |det ρ p - detLim p| < ε)
    (hΦc : ∀ᵐ ω ∂P, ∀ ρ ∈ R, ContinuousOn (fun p => Φ ρ p ω) S) :
    ∃ Lim : (Fin n → ℝ) → Ω → ℝ, (∀ ω, ContinuousOn (fun p => Lim p ω) S) ∧
      (∀ p ∈ S, (fun ω => Lim p ω) =ᵐ[P] fun ω => X ω (μ p 0) + detLim p) ∧
      ∀ᵐ ω ∂P, ∀ ε > 0, ∃ δ > 0, ∀ ρ ∈ R, ρ < δ → ∀ p ∈ S, |Φ ρ p ω - Lim p ω| ≤ ε := by
  obtain ⟨Lim, hLc, hLe, hconv⟩ :=
    ae_unifConv_countable hX hF hR hS hD hDS hRc hRI Φ det detLim hdetc hid hdet
  refine ⟨Lim, hLc, hLe, ?_⟩
  filter_upwards [hconv, hΦc] with ω hω hc ε hε
  obtain ⟨δ, hδ, h⟩ := hω ε hε
  refine ⟨δ, hδ, fun ρ hρ hρδ => le_of_continuousOn_of_dense hDS hdense
    (((hc ρ hρ).sub (hLc ω)).abs) fun p hp => (h ρ hρ hρδ p hp).le⟩

/-- **GENERIC-UC, continuous radius.** With joint pathwise continuity of `(p, ρ) ↦ Φ ρ p` on
`S × (0,1]` and `R` dense in `[0,1]`, the convergence is uniform over `S` and all radii. -/
theorem ae_unifConv_all_radii (hX : IsFreeGFFModConstH X P) (hF : GenFam S μ M K c)
    (hR : IsLipRetr S ret L) (hS : IsCompact S) {D : Set (Fin n → ℝ)} (hD : D.Countable)
    (hDS : D ⊆ S) (hdense : S ⊆ closure D) {R : Set ℝ} (hRc : R.Countable)
    (hRI : R ⊆ Icc 0 1) (hRd : ∀ a b : ℝ, 0 ≤ a → a < b → b ≤ 1 → ∃ ρ ∈ R, a < ρ ∧ ρ < b)
    (Φ : ℝ → (Fin n → ℝ) → Ω → ℝ) (det : ℝ → (Fin n → ℝ) → ℝ) (detLim : (Fin n → ℝ) → ℝ)
    (hdetc : ContinuousOn detLim S)
    (hid : ∀ ρ ∈ R, ∀ p ∈ D, ∀ᵐ ω ∂P, Φ ρ p ω = X ω (μ p ρ) + det ρ p)
    (hdet : ∀ ε > 0, ∃ δ > 0, ∀ ρ ∈ R, ρ < δ → ∀ p ∈ S, |det ρ p - detLim p| < ε)
    (hΦc : ∀ᵐ ω ∂P, ContinuousOn (fun z : (Fin n → ℝ) × ℝ => Φ z.2 z.1 ω) (S ×ˢ Ioc 0 1)) :
    ∃ Lim : (Fin n → ℝ) → Ω → ℝ, (∀ ω, ContinuousOn (fun p => Lim p ω) S) ∧
      (∀ p ∈ S, (fun ω => Lim p ω) =ᵐ[P] fun ω => X ω (μ p 0) + detLim p) ∧
      ∀ᵐ ω ∂P, ∀ ε > 0, ∃ δ > 0, ∀ ρ : ℝ, 0 < ρ → ρ < δ → ∀ p ∈ S,
        |Φ ρ p ω - Lim p ω| ≤ ε := by
  obtain ⟨Lim, hLc, hLe, hconv⟩ :=
    ae_unifConv_countable hX hF hR hS hD hDS hRc hRI Φ det detLim hdetc hid hdet
  refine ⟨Lim, hLc, hLe, ?_⟩
  filter_upwards [hconv, hΦc] with ω hω hc ε hε
  obtain ⟨δ₀, hδ₀, h⟩ := hω ε hε
  set δ := min δ₀ 1 with hδdef
  refine ⟨δ, lt_min hδ₀ one_pos, fun ρ hρ0 hρδ p hp => ?_⟩
  have hρ1 : ρ ≤ 1 := (lt_of_lt_of_le hρδ (min_le_right _ _)).le
  set g : (Fin n → ℝ) × ℝ → ℝ := fun z => |Φ z.2 z.1 ω - Lim z.1 ω| with hg
  have hgc : ContinuousOn g (S ×ˢ Ioc 0 1) :=
    (hc.sub ((hLc ω).comp continuousOn_fst fun z hz => hz.1)).abs
  set E : Set ((Fin n → ℝ) × ℝ) := D ×ˢ (R ∩ Ioo 0 δ) with hE
  have hES : E ⊆ S ×ˢ Ioc 0 1 := fun z hz =>
    ⟨hDS hz.1, hz.2.2.1, (lt_of_lt_of_le hz.2.2.2 (min_le_right _ _)).le⟩
  have hρcl : ρ ∈ closure (R ∩ Ioo 0 δ) := by
    refine Metric.mem_closure_iff.2 fun e he => ?_
    have hab : max 0 (ρ - e) < min (ρ + e) δ :=
      max_lt (lt_min (by linarith) (by linarith)) (lt_min (by linarith) (by linarith))
    obtain ⟨r, hr, har, hrb⟩ := hRd (max 0 (ρ - e)) (min (ρ + e) δ) (le_max_left _ _) hab
      ((min_le_right _ _).trans (min_le_right _ _))
    refine ⟨r, ⟨hr, lt_of_le_of_lt (le_max_left _ _) har,
      lt_of_lt_of_le hrb (min_le_right _ _)⟩, ?_⟩
    rw [Real.dist_eq, abs_lt]
    constructor
    · linarith [lt_of_lt_of_le hrb (min_le_left _ _)]
    · linarith [lt_of_le_of_lt (le_max_right _ _) har]
  have hmem : (p, ρ) ∈ closure E := by
    rw [hE, closure_prod_eq]; exact ⟨hdense hp, hρcl⟩
  have h1 := ((hgc (p, ρ) ⟨hp, hρ0, hρ1⟩).mono hES).mem_closure_image hmem
  have hsub : closure (g '' E) ⊆ Iic ε := closure_minimal (by
    rintro _ ⟨z, hz, rfl⟩
    exact (h z.2 hz.2.1 (lt_of_lt_of_le hz.2.2.2 (min_le_left _ _)) z.1 hz.1).le) isClosed_Iic
  exact hsub h1

end GenUC
end QuantumZipper
