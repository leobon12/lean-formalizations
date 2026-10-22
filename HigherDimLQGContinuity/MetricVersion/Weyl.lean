import HigherDimLQGContinuity.MetricVersion.Construct
import HigherDimLQGContinuity.MetricVersion.Frame
import HigherDimLQGContinuity.Param.Interval
import HigherDimLQGMetric.Frozen.Theorem12
import HigherDimLQGMetric.Metric.WeylBasic
import HigherDimLQGMetric.Sharp.ScaledMetric

/-!
# Metric-valued versions (packet E5): the invariant good event and the Weyl bounds at all frame translates

Part C, `c:lem-opt-weyl` ((5.9), with NA4 §1.3's MINOR repair: the Weyl events are intersected at all translates).
Let `X` satisfy `PosVersionStmt d X` and let `F` be a pairing frame. For the countably many rational parameters
`q ∈ S_d` fix strong assignments `D_q` (`theorem12`). The event `E₀` (a measurable full subset of) "the family is
continuous on `S_d`, and at every rational `q`: `X(q) = ρ^{D_q}`, `D_q` is a length metric and Weyl scaling holds for all
continuous `f`" is translated by all rational frame shifts and intersected:
`E = ⋂_{v ∈ ℕ →₀ ℚ} {g : g + f_v ∈ E₀}`. Then `E` is measurable, almost sure (`c:lem-opt-cm`), invariant under the
rational frame shifts, and for `g ∈ E`, `ξ ∈ S_d`:
`e^{-ξ M} X(ξ)(g) ≤ X(ξ)(g + f_v) ≤ e^{ξ M} X(ξ)(g)` for every `M ≥ |f_v|`, in particular `M = ‖f_v‖_∞`
(`weyl_translates_ae`); at rational `ξ` from
`weylScale_mem_Icc_of_isLength`, then by continuity in `ξ` (both `g` and `g + f_v` lie in `E`).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Filter Topology Set Metric
open scoped ENNReal

namespace HigherDimLQGContinuity

open HigherDimLQGMetric
open HigherDimLFPP (Rd)

variable {d : ℕ}

theorem mv_isOpen_subcritSet (hd : 2 ≤ d) : IsOpen (subcritSet d) := by
  rw [subcritSet_eq_Ioo hd]
  exact isOpen_Ioo

/-- The rational positive subcritical parameters (a countable index type). -/
abbrev MVRatParam (d : ℕ) : Type := {q : ℚ // (q : ℝ) ∈ subcritSet d}

/-- Strong assignments exist at every positive subcritical parameter (`theorem12`). -/
theorem mv_exists_strong (hd : 3 ≤ d) {ξ : ℝ} (hξ : ξ ∈ subcritSet d) :
    ∃ D : DistRd d → ContMetric d, IsStrongExpMetric d ξ (distExp d ξ) D := by
  obtain ⟨D, hD, -⟩ := (theorem12 d ξ hd hξ.1 hξ.2).1
  exact ⟨D, hD⟩

/-- `ρ^D_g` is a length metric when `D_g` is. -/
theorem mv_rho_isLength {D : DistRd d → ContMetric d} {g : DistRd d} (h : (D g).IsLength) :
    (rho D g).IsLength :=
  ContMetric.isLength_smul _ h

/-- **`c:lem-opt-weyl`** (with `c:lem-opt-cm`): the invariant good event and the Weyl bounds at every rational frame
translate, for every positive subcritical parameter. The event also carries the continuity of the family on
`S_d` and the length metrics at the rational parameters. -/
theorem weyl_translates_ae (hd : 3 ≤ d) (F : PairingFrame d) {X : ℝ → DistRd d → C(Rd d × Rd d, ℝ)}
    (hX : PosVersionStmt d X) :
    ∃ E : Set (DistRd d), MeasurableSet E ∧ (∀ᵐ g ∂(normLGFLaw d), g ∈ E) ∧
      (∀ (v : ℕ →₀ ℚ) (g : DistRd d), addFun g (mvFrameShift F v) ∈ E ↔ g ∈ E) ∧
      (∀ g ∈ E, ContinuousOn (fun ξ => X ξ g) (subcritSet d)) ∧
      (∀ g ∈ E, ∀ q : ℚ, (q : ℝ) ∈ subcritSet d → ∃ G : ContMetric d, G.1 = X q g ∧ G.IsLength) ∧
      ∀ (v : ℕ →₀ ℚ) (M : ℝ), (∀ x : Rd d, |mvFrameShift F v x| ≤ M) →
        ∀ g ∈ E, ∀ ξ ∈ subcritSet d, ∀ p : Rd d × Rd d,
          Real.exp (-(ξ * M)) * X ξ g p ≤ X ξ (addFun g (mvFrameShift F v)) p ∧
            X ξ (addFun g (mvFrameShift F v)) p ≤ Real.exp (ξ * M) * X ξ g p := by
  have hd2 : 2 ≤ d := by omega
  have hspec := normLGFLaw_spec_holds d hd2
  have := hspec.1
  have hlgf : IsLGFPlusCont (id : DistRd d → DistRd d) (normLGFLaw d) := hspec.2.1.1.isLGFPlusCont
  have hS : IsOpen (subcritSet d) := mv_isOpen_subcritSet hd2
  -- strong assignments at the rational parameters
  choose D hD using fun q : MVRatParam d => mv_exists_strong hd q.2
  -- the almost-sure property
  set P₀ : DistRd d → Prop := fun g => ContinuousOn (fun ξ => X ξ g) (subcritSet d) ∧
    ∀ q : MVRatParam d, X q g = (rho (D q) g).1 ∧ (D q g).IsLength ∧
      ∀ f : C(Rd d, ℝ), ∀ z w : Rd d,
        weylScale (q : ℝ) f (D q g) z w = ENNReal.ofReal ((D q (addFun g f)).1 (z, w)) with hP₀def
  have hP₀ : ∀ᵐ g ∂(normLGFLaw d), P₀ g := by
    have h2 : ∀ᵐ g ∂(normLGFLaw d), ∀ q : MVRatParam d, X q g = (rho (D q) g).1 ∧ (D q g).IsLength ∧
        ∀ f : C(Rd d, ℝ), ∀ z w : Rd d,
          weylScale (q : ℝ) f (D q g) z w = ENNReal.ofReal ((D q (addFun g f)).1 (z, w)) := by
      rw [ae_all_iff]
      intro q
      filter_upwards [hX.2.1 q q.2.1 q.2.2 (D q) (hD q), (hD q).length _ id hlgf,
        (hD q).weyl _ id hlgf] with g h1 h2 h3
      exact ⟨h1, h2, h3⟩
    filter_upwards [hX.2.2, h2] with g h1 h2
    exact ⟨h1, h2⟩
  obtain ⟨N, hNsub, hNm, hN0⟩ := exists_measurable_superset_of_null (ae_iff.1 hP₀)
  have hE₀ : ∀ g ∈ Nᶜ, P₀ g := fun g hg => by
    by_contra h
    exact hg (hNsub h)
  have hE₀ae : ∀ᵐ g ∂(normLGFLaw d), g ∈ Nᶜ := by
    rw [ae_iff]
    simpa only [mem_compl_iff, not_not, ofPred_mem_eq] using hN0
  -- the invariant event
  set E : Set (DistRd d) := ⋂ v : ℕ →₀ ℚ, (fun g => addFun g (mvFrameShift F v)) ⁻¹' Nᶜ with hEdef
  have hmemE : ∀ g, g ∈ E ↔ ∀ v : ℕ →₀ ℚ, addFun g (mvFrameShift F v) ∈ Nᶜ := fun g => by
    simp only [hEdef, mem_iInter, mem_preimage]
  have hEm : MeasurableSet E :=
    MeasurableSet.iInter fun v => measurable_addFun_left _ hNm.compl
  have hEae : ∀ᵐ g ∂(normLGFLaw d), g ∈ E := by
    have : ∀ᵐ g ∂(normLGFLaw d), ∀ v : ℕ →₀ ℚ, addFun g (mvFrameShift F v) ∈ Nᶜ := by
      rw [ae_all_iff]
      intro v
      exact ae_addFun_frame_of_ae hd2 F _ hE₀ae
    filter_upwards [this] with g hg
    exact (hmemE g).2 hg
  have hinv : ∀ (w : ℕ →₀ ℚ) (g : DistRd d), addFun g (mvFrameShift F w) ∈ E ↔ g ∈ E := by
    intro w g
    rw [hmemE, hmemE]
    simp_rw [addFun_addFun, ← mvFrameShift_add]
    constructor
    · intro h v
      have := h (v - w)
      rwa [add_sub_cancel] at this
    · intro h v
      exact h (w + v)
  have hEE₀ : ∀ g ∈ E, P₀ g := fun g hg => by
    have := ((hmemE g).1 hg) 0
    rw [mvFrameShift_zero, addFun_zero] at this
    exact hE₀ _ this
  refine ⟨E, hEm, hEae, hinv, fun g hg => (hEE₀ g hg).1, ?_, ?_⟩
  · -- rational parameters: length metrics
    intro g hg q hq
    obtain ⟨h1, h2, -⟩ := (hEE₀ g hg).2 ⟨q, hq⟩
    exact ⟨rho (D ⟨q, hq⟩) g, h1.symm, mv_rho_isLength h2⟩
  · -- the Weyl bounds
    intro v M hM g hg ξ hξ p
    set f := mvFrameShift F v with hf
    have hg' : addFun g f ∈ E := (hinv v g).2 hg
    have hcg := (hEE₀ g hg).1
    have hcg' := (hEE₀ _ hg').1
    -- the bounds at rational parameters
    have hrat : ∀ q : ℚ, (q : ℝ) ∈ subcritSet d →
        Real.exp (-((q : ℝ) * M)) * X q g p ≤ X q (addFun g f) p ∧
          X q (addFun g f) p ≤ Real.exp ((q : ℝ) * M) * X q g p := by
      intro q hq
      obtain ⟨hXg, hLg, hWg⟩ := (hEE₀ g hg).2 ⟨q, hq⟩
      obtain ⟨hXg', -, -⟩ := (hEE₀ _ hg').2 ⟨q, hq⟩
      have hq0 : (0 : ℝ) < q := hq.1
      have ha : ∀ x, -((q : ℝ) * M) ≤ (q : ℝ) * f x := fun x => by
        have := (abs_le.1 (hM x)).1
        nlinarith
      have hb : ∀ x, (q : ℝ) * f x ≤ (q : ℝ) * M := fun x =>
        mul_le_mul_of_nonneg_left (abs_le.1 (hM x)).2 hq0.le
      obtain ⟨hlo, hhi⟩ := weylScale_mem_Icc_of_isLength (z := p.1) (w := p.2) hLg ha hb
      rw [hWg] at hlo hhi
      have hlo' : Real.exp (-((q : ℝ) * M)) * (D ⟨q, hq⟩ g).1 p ≤ (D ⟨q, hq⟩ (addFun g f)).1 p :=
        (ENNReal.ofReal_le_ofReal_iff ((D ⟨q, hq⟩ (addFun g f)).nonneg p.1 p.2)).1 hlo
      have hhi' : (D ⟨q, hq⟩ (addFun g f)).1 p ≤ Real.exp ((q : ℝ) * M) * (D ⟨q, hq⟩ g).1 p :=
        (ENNReal.ofReal_le_ofReal_iff (mul_nonneg (Real.exp_pos _).le
          ((D ⟨q, hq⟩ g).nonneg p.1 p.2))).1 hhi
      rw [hXg, hXg']
      simp only [rho, ContMetric.smul_apply]
      set b := Real.exp (-logMean (D ⟨q, hq⟩))
      have hb0 : 0 < b := Real.exp_pos _
      constructor
      · calc Real.exp (-((q : ℝ) * M)) * (b * (D ⟨q, hq⟩ g).1 p)
            = b * (Real.exp (-((q : ℝ) * M)) * (D ⟨q, hq⟩ g).1 p) := by ring
          _ ≤ b * (D ⟨q, hq⟩ (addFun g f)).1 p := mul_le_mul_of_nonneg_left hlo' hb0.le
      · calc b * (D ⟨q, hq⟩ (addFun g f)).1 p
            ≤ b * (Real.exp ((q : ℝ) * M) * (D ⟨q, hq⟩ g).1 p) := mul_le_mul_of_nonneg_left hhi' hb0.le
          _ = Real.exp ((q : ℝ) * M) * (b * (D ⟨q, hq⟩ g).1 p) := by ring
    -- extension to every parameter by continuity
    have hcont1 : ContinuousOn (fun ξ => Real.exp (-(ξ * M)) * X ξ g p) (subcritSet d) :=
      ((Real.continuous_exp.comp ((continuous_id.mul continuous_const).neg)).continuousOn).mul
        (mv_continuousOn_eval hcg p)
    have hcont2 : ContinuousOn (fun ξ => X ξ (addFun g f) p) (subcritSet d) := mv_continuousOn_eval hcg' p
    have hcont3 : ContinuousOn (fun ξ => Real.exp (ξ * M) * X ξ g p) (subcritSet d) :=
      ((Real.continuous_exp.comp (continuous_id.mul continuous_const)).continuousOn).mul
        (mv_continuousOn_eval hcg p)
    exact ⟨mv_le_of_rat hS hcont1 hcont2 (fun q hq => (hrat q hq).1) ξ hξ,
      mv_le_of_rat hS hcont2 hcont3 (fun q hq => (hrat q hq).2) ξ hξ⟩

end HigherDimLQGContinuity
