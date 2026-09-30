import QuantumZipper.Proofs.Thm18.A1RFBind
import QuantumZipper.Proofs.Zipper.F1ReflReg

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# A1RF (3): `A1RFFullYStmt` from per-loop convergence and continuity along the smeared family

The smeared measure `a1rfNu W t left d s ρ = (μ ⊗ m).map Ψ_ρ`,
`Ψ_ρ(z, θ) = f_t⁻¹(foldH(z + ρ e^{iθ}))`, `μ = (f_t ∘ ψ)_* fc(d, s)`, `m` the angle measure
(A1RFBind.lean). `A1RFFullYStmt` splits into:

* `A1RFLoopUCStmt` (open; bookkeeping on proved engines): a.s., for every `t > 0`, `ρ > 0` and
  bounded set of centres in `ℍ̄`, the regularized pairings of `Y` along the pulled-back folded
  circles `(f_t⁻¹)_* fc(z, ρ)` converge uniformly. At the free-field level this is the proved
  flow convergence `F1.xFlowUCStmt_holds` at the parameters `(0, t, z, ρ)`
  (`flowNu_zero_left`: `flowNu W (0, t, z, ρ) = (f_t⁻¹)_* fc(z, ρ)`);
* `A1RFSmearContStmt` (open; the analytic core): a.s., for all `t, d, s`,
  `ρ ↦ evalReg Y (a1rfNu … ρ)` is continuous at `ρ = 0⁺`. This is Duplantier–Sheffield,
  Invent. Math. 185 (2011), Prop. 3.1 for the family `(t, d, s, ρ) ↦ a1rfNu … ρ`, whose member at
  `ρ = 0` is `(f_t⁻¹)_* μ = ψ_* fc(d, s)` (`A1RF.map_prod_zero`).

* `A1RF.integral_evalReg_fc_eq_nu` (deterministic): for a regular sample and `ρ > 0`, uniform
  convergence along the loops gives `∫ evalReg x ((f_t⁻¹)_* fc(z, ρ)) dμ(z) = evalReg x ν_ρ`
  (A1RFBind: Fubini at each dyadic scale and dominated convergence; the domination from the
  compactness of the support and uniform convergence).
* **`a1rfFullYStmt_of : A1RFLoopUCStmt → A1RFSmearContStmt → A1RFFullYStmt`.**

Own elementary bookkeeping.
-/

noncomputable section

open MeasureTheory Filter Set Function Metric
open scoped Topology ENNReal NNReal

namespace QuantumZipper
namespace R18

open Thm18Asm

/-- The pulled-back folded circles of radius `ρ` smeared along the pushed side circle. -/
def a1rfNu (W : ℝ → ℝ) (t : ℝ) (left : Bool) (d : ℂ) (s ρ : ℝ) : Measure ℂ :=
  ((a1rMu W t left d s).prod E6.XAreaPC.angMeas).map
    (fun p : ℂ × ℝ => fwdMapInv W t (foldH (circleMap p.1 ρ p.2)))

/-- **Per-loop uniform convergence** (open): the regularized pairings of `Y` along the
pulled-back folded circles converge uniformly on bounded sets of centres, for all `t > 0`,
`ρ > 0`. -/
def A1RFLoopUCStmt : Prop :=
  ∀ (γ : ℝ) {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (B : ℝ≥0 → Ω → ℝ) (Y : Ω → FieldSample),
    Thm18Setting γ P B Y → Thm18Inputs γ P B Y → ∀ᵐ ω ∂P,
      ∀ t : ℝ, 0 < t → ∀ ρ : ℝ, 0 < ρ → ∀ R : ℝ,
        TendstoUniformlyOn (fun (k : ℕ) (z : ℂ) => ∫ u, avgReg (Y ω) k u
            ∂((foldedCircle z ρ).map (fwdMapInv (drive (γ ^ 2) B ω) t)))
          (fun z => evalReg (Y ω) ((foldedCircle z ρ).map (fwdMapInv (drive (γ ^ 2) B ω) t)))
          atTop (Hbar ∩ closedBall 0 R)

/-- **Continuity along the smeared family at `ρ = 0`** (open; Duplantier–Sheffield 2011,
Prop. 3.1 for the family `a1rfNu`). -/
def A1RFSmearContStmt : Prop :=
  ∀ (γ : ℝ) {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (B : ℝ≥0 → Ω → ℝ) (Y : Ω → FieldSample),
    Thm18Setting γ P B Y → Thm18Inputs γ P B Y → ∀ left : Bool, ∀ᵐ ω ∂P,
      ∀ t : ℝ, 0 < t → ∀ d ∈ Hbar, ∀ s : ℝ, 0 < s →
        Tendsto (fun ρ => evalReg (Y ω) (a1rfNu (drive (γ ^ 2) B ω) t left d s ρ)) (𝓝[>] 0)
          (𝓝 (evalReg (Y ω) (a1rfNu (drive (γ ^ 2) B ω) t left d s 0)))

namespace A1RF

variable {W : ℝ → ℝ}

theorem angMeas_univ : E6.XAreaPC.angMeas univ = 1 := by
  have h := (isProbabilityMeasure_foldedCircle (0 : ℂ) 1).measure_univ
  have hm : Measurable fun θ : ℝ => foldH (circleMap (0 : ℂ) 1 θ) :=
    measurable_foldH.comp (measurable_circleMap _ _)
  rw [E6.XAreaPC.foldedCircle_eq_map_angMeas, Measure.map_apply hm MeasurableSet.univ,
    preimage_univ] at h
  exact h

instance isProbabilityMeasure_angMeas : IsProbabilityMeasure E6.XAreaPC.angMeas :=
  ⟨angMeas_univ⟩

/-- `avgReg` of a regular sample is its witness at dyadic radii. -/
theorem avgReg_eq_of_regular {x : FieldSample} {F : ℂ × ℝ → ℝ} (hF : IsRegularWith x F)
    (k : ℕ) {w : ℂ} (hw : w ∈ Hbar) : avgReg x k w = F (w, radius k) :=
  (hF.2.1 k w hw).limUnder_eq

/-- Bound of `avgReg` at a fixed scale on a bounded part of `ℍ̄`. -/
theorem exists_bound_avgReg {x : FieldSample} {F : ℂ × ℝ → ℝ} (hF : IsRegularWith x F)
    (k : ℕ) (R : ℝ) : ∃ M : ℝ, 0 ≤ M ∧ ∀ w ∈ Hbar ∩ closedBall 0 R, |avgReg x k w| ≤ M := by
  have hK : IsCompact (Hbar ∩ closedBall (0 : ℂ) R) :=
    (isCompact_closedBall (0 : ℂ) R).inter_left isClosed_Hbar
  have hc : ContinuousOn (fun w => F (w, radius k)) (Hbar ∩ closedBall (0 : ℂ) R) :=
    hF.1.comp (continuousOn_id.prodMk continuousOn_const) fun w hw =>
      ⟨hw.1, radius_pos k⟩
  obtain ⟨M, hM⟩ := hK.exists_bound_of_continuousOn hc
  refine ⟨max M 0, le_max_right _ _, fun w hw => ?_⟩
  rw [avgReg_eq_of_regular hF k hw.1, ← Real.norm_eq_abs]
  exact (hM w hw).trans (le_max_left _ _)

/-- **The full smoothing at radius `ρ > 0` is the regularized evaluation at `ν_ρ`.** -/
theorem integral_evalReg_fc_eq_nu {x : FieldSample} {F : ℂ × ℝ → ℝ} (hF : IsRegularWith x F)
    (hG : G1zDrvGood W) {t : ℝ} (ht : 0 < t) (left : Bool) (d : ℂ) {s : ℝ} (hs : 0 < s)
    {ρ : ℝ} (hρ : 0 < ρ)
    (hUC : ∀ R : ℝ, TendstoUniformlyOn (fun (k : ℕ) (z : ℂ) => ∫ u, avgReg x k u
        ∂((foldedCircle z ρ).map (fwdMapInv W t)))
      (fun z => evalReg x ((foldedCircle z ρ).map (fwdMapInv W t))) atTop
      (Hbar ∩ closedBall 0 R)) :
    ∫ z, evalReg x ((foldedCircle z ρ).map (fwdMapInv W t)) ∂(a1rMu W t left d s) =
      evalReg x (a1rfNu W t left d s ρ) := by
  set g := fwdMapInv W t with hgdef
  set μ := a1rMu W t left d s with hμ
  set m := E6.XAreaPC.angMeas with hm
  set Ψ : ℂ × ℝ → ℂ := fun p => g (foldH (circleMap p.1 ρ p.2)) with hΨdef
  have hgm : Measurable g := RTBeur.measurable_fwdMapInv_rt hG.1 hG.2.1 ht.le
  have hΨ : Measurable Ψ := measurable_smear hgm ρ
  have hak : ∀ k : ℕ, Measurable (avgReg x k) := fun k =>
    (measurable_avgReg k).comp (measurable_const.prodMk measurable_id)
  have hcm : ∀ z : ℂ, Measurable fun θ : ℝ => foldH (circleMap z ρ θ) := fun z =>
    measurable_foldH.comp (measurable_circleMap _ _)
  obtain ⟨Rr, hsupp⟩ := A1R.exists_ae_bdd_a1rMu hG ht left d hs
  obtain ⟨C, hC⟩ := G1ZA1a.exists_bound_fwdMapInv hG ht
  set R' := Rr + ρ + |C| with hR'
  -- the loops of centres in the support stay in a fixed bounded part of `ℍ̄`
  have hcirc : ∀ z : ℂ, ‖z‖ ≤ Rr → ∀ᵐ θ ∂m, Ψ (z, θ) ∈ Hbar ∩ closedBall 0 R' := by
    intro z hzR
    have h1 := TwoPoint.foldedCircle_ae_mem_H z hρ
    have h2 := TwoPoint.foldedCircle_ae_norm_le z hρ.le
    rw [E6.XAreaPC.foldedCircle_eq_map_angMeas] at h1 h2
    have h1' := (ae_map_iff (hcm z).aemeasurable isOpen_H.measurableSet).1 h1
    have h2' := (ae_map_iff (hcm z).aemeasurable
      (measurableSet_le measurable_norm measurable_const)).1 h2
    filter_upwards [h1', h2'] with θ hθ1 hθ2
    refine ⟨F1.fwdMapInv_mem_Hbar W t _, ?_⟩
    rw [mem_closedBall, dist_zero_right]
    have h3 := hC _ hθ1
    have h4 : ‖g (foldH (circleMap z ρ θ))‖ ≤ ‖foldH (circleMap z ρ θ)‖ + C := by
      have := norm_sub_norm_le (g (foldH (circleMap z ρ θ))) (foldH (circleMap z ρ θ))
      linarith
    show ‖g (foldH (circleMap z ρ θ))‖ ≤ Rr + ρ + |C|
    linarith [le_abs_self C]
  -- per-scale bounds
  have hMk : ∀ k : ℕ, ∃ M : ℝ, 0 ≤ M ∧ ∀ w ∈ Hbar ∩ closedBall 0 R', |avgReg x k w| ≤ M :=
    fun k => exists_bound_avgReg hF k R'
  choose Mk hMk0 hMkb using hMk
  have hΦeq : ∀ (k : ℕ) (z : ℂ), ∫ u, avgReg x k u ∂((foldedCircle z ρ).map g) =
      ∫ θ, avgReg x k (Ψ (z, θ)) ∂m := by
    intro k z
    rw [fc_map_eq_angMeas_map hgm]
    exact integral_map (hgm.comp (hcm z)).aemeasurable (hak k).aestronglyMeasurable
  have hEeq : ∀ z : ℂ, evalReg x ((foldedCircle z ρ).map g) =
      evalReg x (m.map fun θ => Ψ (z, θ)) := fun z => by rw [fc_map_eq_angMeas_map hgm]
  have hΦb : ∀ (k : ℕ) (z : ℂ), ‖z‖ ≤ Rr → |∫ θ, avgReg x k (Ψ (z, θ)) ∂m| ≤ Mk k := by
    intro k z hzR
    have := norm_integral_le_of_norm_le_const (μ := m) (f := fun θ => avgReg x k (Ψ (z, θ)))
      ((hcirc z hzR).mono fun θ hθ => by rw [Real.norm_eq_abs]; exact hMkb k _ hθ)
    simpa [Real.norm_eq_abs] using this
  -- uniform convergence on the support
  have hU := hUC Rr
  have hS : ∀ᵐ z ∂μ, z ∈ Hbar ∩ closedBall 0 Rr := hsupp.mono fun z hz =>
    ⟨hz.1, by rw [mem_closedBall, dist_zero_right]; exact hz.2⟩
  obtain ⟨K, hK⟩ := eventually_atTop.1 ((Metric.tendstoUniformlyOn_iff.1 hU) 1 one_pos)
  set M : ℝ := (∑ k ∈ Finset.range (K + 1), Mk k) + 2 with hMdef
  have hsum : ∀ k ≤ K, Mk k ≤ ∑ j ∈ Finset.range (K + 1), Mk j := fun k hk =>
    Finset.single_le_sum (f := Mk) (fun j _ => hMk0 j) (Finset.mem_range.2 (by omega))
  have hdom : ∀ k : ℕ, ∀ᵐ z ∂μ, |∫ θ, avgReg x k (Ψ (z, θ)) ∂m| ≤ M := by
    intro k
    filter_upwards [hS] with z hz
    have hzR : ‖z‖ ≤ Rr := by simpa [mem_closedBall, dist_zero_right] using hz.2
    rcases le_or_gt k K with hk | hk
    · linarith [hΦb k z hzR, hsum k hk]
    · have e1 := hK k hk.le z hz
      have e2 := hK K le_rfl z hz
      rw [Real.dist_eq, hΦeq] at e1 e2
      have e3 := hΦb K z hzR
      have e4 := hsum K le_rfl
      rw [abs_lt] at e1 e2
      rw [abs_le] at e3 ⊢
      constructor <;> linarith [e1.1, e1.2, e2.1, e2.2, e3.1, e3.2]
  have hconv : ∀ᵐ z ∂μ, Tendsto (fun k : ℕ => ∫ θ, avgReg x k (Ψ (z, θ)) ∂m) atTop
      (𝓝 (evalReg x (m.map fun θ => Ψ (z, θ)))) := by
    filter_upwards [hS] with z hz
    have := hU.tendsto_at hz
    simp only [hΦeq, hEeq] at this
    exact this
  have hbk : ∀ k : ℕ, ∃ M : ℝ, ∀ᵐ p ∂(μ.prod m), |avgReg x k (Ψ p)| ≤ M := by
    intro k
    refine ⟨Mk k, (Measure.ae_prod_iff_ae_ae ?_).2 ?_⟩
    · exact measurableSet_le (continuous_abs.measurable.comp ((hak k).comp hΨ)) measurable_const
    · filter_upwards [hsupp] with z hz
      filter_upwards [hcirc z hz.2] with θ hθ
      exact hMkb k _ hθ
  rw [show a1rfNu W t left d s ρ = (μ.prod m).map Ψ from rfl,
    evalReg_map_prod_eq hΨ hbk hdom hconv]
  exact integral_congr_ae (Eventually.of_forall fun z => hEeq z)

end A1RF

/-- **The full smoothing node from per-loop convergence and continuity along the smeared
family.** -/
theorem a1rfFullYStmt_of (hL : A1RFLoopUCStmt) (hC : A1RFSmearContStmt) : A1RFFullYStmt := by
  intro γ Ω _ P _ B Y hS hIn left
  filter_upwards [hL γ P B Y hS hIn, hC γ P B Y hS hIn left, ae_g1zDrvGood hS hIn, hIn.1]
    with ω hl hc hG hgood t ht d hd s hs
  obtain ⟨F, hF⟩ := hgood.1.1
  set W := drive (γ ^ 2) B ω with hWdef
  have hgm : Measurable (fwdMapInv W t) := RTBeur.measurable_fwdMapInv_rt hG.1 hG.2.1 ht.le
  obtain ⟨Rr, hsupp⟩ := A1R.exists_ae_bdd_a1rMu hG ht left d hs
  have e0 : a1rfNu W t left d s 0 = (a1rMu W t left d s).map (fwdMapInv W t) :=
    A1RF.map_prod_zero (hsupp.mono fun z hz => hz.1) hgm
  rw [← e0]
  refine (hc t ht d hd s hs).congr' ?_
  filter_upwards [self_mem_nhdsWithin] with ρ hρ
  exact (A1RF.integral_evalReg_fc_eq_nu hF hG ht left d hs hρ (hl t ht ρ hρ)).symm

end R18
end QuantumZipper
