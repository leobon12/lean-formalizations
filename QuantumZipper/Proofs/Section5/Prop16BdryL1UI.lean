import QuantumZipper.Proofs.Section5.Prop16ActRegBdryLoc
import QuantumZipper.Proofs.Section5.Prop16LocalAssembly
import QuantumZipper.Proofs.Section5.Prop16D4WInNice
import QuantumZipper.Proofs.LQG.Measurability
import Mathlib.MeasureTheory.Function.UniformIntegrable

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# Proposition 1.6, node B′: `Prop16BdryL1LocStmt` from uniform integrability

`prop16BdryL1LocStmt_of_ui : Prop16BdryUIStmt → Prop16BdryL1LocStmt`.

The local `L¹` statement splits into a pathwise part and a probabilistic part.

* **Pathwise part (proved here from `Prop16PalmHyp`).** Almost surely the mixed field is locally
  good on `D ∪ (a,b)` (`IsLocNiceOn`, part of `Prop16PalmHyp`), so the approximations
  `bdryApprox γ (h0 + X ω)` converge vaguely on `(a,b)` (`Prop16Area.G.prop16_hexB`), and by
  uniqueness of vague limits on open sets (`LocalRule.qBoundaryMeasureOn_eq`) the limit is
  `ν_h = prop16Nu`. Hence for every continuous `f` vanishing off `[t-η, t+η] ⊆ (a,b)`,
  a.s. `∫ f d bdryApprox_k → ∫ f dν_h`.
* **Probabilistic part (node `Prop16BdryUIStmt`).** Near every `t ∈ (a,b)` the masses
  `bdryApprox_k(h0 + X)([t-η, t+η])`, `k ≥ k₀`, are a.s. finite and uniformly integrable.

Almost sure convergence plus uniform integrability gives `L¹` convergence (Vitali's convergence
theorem, mathlib `MeasureTheory.tendsto_Lp_finite_of_tendsto_ae`). This is exactly the route of
Duplantier–Sheffield, *Liouville quantum gravity and KPZ*, Invent. Math. 185 (2011)
(arXiv:0808.1560, `literature/0808.1560.pdf`), proof of Prop. 1.2, pp. 23–26: "since
Proposition 1.1 implies the existence of the limit of `µ_ε(S)`, it is enough to show that the
random variables `M_ε = µ_ε(S)` are uniformly integrable" (eq. (29)–(30), proved with rooted
measures); the boundary measure is treated the same way in their §6. The node
`Prop16BdryUIStmt` is that uniform integrability statement for the boundary approximations of
the mixed field near the free arc; the wiring below is our own bookkeeping.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Metric
open scoped Topology ENNReal NNReal

namespace QuantumZipper

namespace Prop16Asm

/-- **Node B′-UI (uniform integrability of the boundary masses near the free arc).** Under the
Proposition 1.6 hypotheses, every `t ∈ (a,b)` has a window `[t-η, t+η] ⊂ (a,b)` and a scale
`k₀` such that for `k ≥ k₀` the approximating masses `bdryApprox_k(h0 + X)([t-η,t+η])` are a.s.
finite and, as real random variables, uniformly integrable (in the probabilistic sense:
a.e.-strongly measurable, `L¹`-bounded, uniformly absolutely continuous). -/
def Prop16BdryUIStmt : Prop :=
  ∀ (γ : ℝ) (D : Set ℂ) (c d a b : ℝ) (h0 : ℂ → ℝ) {Ω : Type} [MeasurableSpace Ω]
    (P : Measure Ω) (X : Ω → FieldSample), Prop16PalmHyp γ D c d a b h0 P X →
    ∀ t ∈ Ioo a b, ∃ η > 0, a < t - η ∧ t + η < b ∧ ∃ k₀ : ℕ,
      (∀ k ≥ k₀, ∀ᵐ ω ∂P, bdryApprox γ (ofFun h0 + X ω) k (Icc (t - η) (t + η)) < ⊤) ∧
      UniformIntegrable (fun (k : ℕ) (ω : Ω) =>
        (bdryApprox γ (ofFun h0 + X ω) (k + k₀) (Icc (t - η) (t + η))).toReal) 1 P

/-- The mixed field `h0 + X` is a measurable map into `FieldSample`. -/
theorem measurable_ofFun_add_bdryUI {Ω : Type} [MeasurableSpace Ω] {X : Ω → FieldSample}
    (hX : ∀ μ : Measure ℂ, Measurable fun ω => X ω μ) (h0 : ℂ → ℝ) :
    Measurable fun ω => ofFun h0 + X ω :=
  measurable_pi_iff.2 fun μ => measurable_const.add (hX μ)

/-- A bounded function vanishing off `[p,q]` has `|∫ f dμ| ≤ C μ([p,q])`. -/
theorem norm_integral_le_of_vanish_bdryUI {f : ℝ → ℝ} {C : ℝ} (hC : ∀ x, ‖f x‖ ≤ C) {p q : ℝ}
    (hK : ∀ x ∉ Icc p q, f x = 0) {μ : Measure ℝ} (hμ : μ (Icc p q) < ⊤) :
    ‖∫ x, f x ∂μ‖ ≤ C * (μ (Icc p q)).toReal := by
  rw [← setIntegral_eq_integral_of_forall_compl_eq_zero hK]
  exact norm_setIntegral_le_of_norm_le_const hμ fun x _ => hC x

/-- Uniform integrability is inherited by a family dominated by a constant multiple. -/
theorem uniformIntegrable_of_le_mul_bdryUI {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
    {F M : ℕ → Ω → ℝ} {C : ℝ} (hC : 0 ≤ C) (hM : UniformIntegrable M 1 P)
    (hF : ∀ k, AEStronglyMeasurable (F k) P)
    (hle : ∀ k, ∀ᵐ ω ∂P, ‖F k ω‖ ≤ C * ‖M k ω‖) : UniformIntegrable F 1 P := by
  obtain ⟨-, hMu, B, hB⟩ := hM
  have hC1 : (0 : ℝ) < C + 1 := by linarith
  have hle' : ∀ k, ∀ᵐ ω ∂P, ‖F k ω‖ ≤ (C + 1) * ‖M k ω‖ := fun k =>
    (hle k).mono fun ω h => h.trans (by nlinarith [norm_nonneg (M k ω)])
  refine ⟨hF, ?_, ⟨(C + 1).toNNReal * B, fun k => ?_⟩⟩
  · rw [unifIntegrable_iff] at hMu ⊢
    intro ε hε
    have hne : ENNReal.ofReal (C + 1) ≠ 0 := by
      rw [ne_eq, ENNReal.ofReal_eq_zero, not_le]; exact hC1
    obtain ⟨δ, hδ, hδ'⟩ := hMu (ε / ENNReal.ofReal (C + 1))
      (ENNReal.div_pos_iff.2 ⟨hε.ne', ENNReal.ofReal_ne_top⟩)
    refine ⟨δ, hδ, fun i s hs => ?_⟩
    calc eLpNorm (F i) 1 (P.restrict s)
        ≤ ENNReal.ofReal (C + 1) * eLpNorm (M i) 1 (P.restrict s) :=
          eLpNorm_le_mul_eLpNorm_of_ae_le_mul (ae_restrict_of_ae (hle' i)) 1
      _ ≤ ENNReal.ofReal (C + 1) * (ε / ENNReal.ofReal (C + 1)) := by
          gcongr; exact hδ' i s hs
      _ = ε := ENNReal.mul_div_cancel hne ENNReal.ofReal_ne_top
  · calc eLpNorm (F k) 1 P ≤ ENNReal.ofReal (C + 1) * eLpNorm (M k) 1 P :=
          eLpNorm_le_mul_eLpNorm_of_ae_le_mul (hle' k) 1
      _ ≤ ENNReal.ofReal (C + 1) * B := by gcongr; exact hB k
      _ = (((C + 1).toNNReal * B : ℝ≥0) : ℝ≥0∞) := by
          rw [ENNReal.coe_mul]; rfl

/-- **Node `Prop16BdryL1LocStmt` from uniform integrability** (Vitali). -/
theorem prop16BdryL1LocStmt_of_ui (hUI : Prop16BdryUIStmt) : Prop16BdryL1LocStmt := by
  intro γ D c d a b h0 Ω _ P X hH t ht
  obtain ⟨η, hη, hat, htb, k₀, hfin, hU⟩ := hUI γ D c d a b h0 P X hH t ht
  obtain ⟨⟨hγ, -, ⟨hDo, -, -, hDH, -⟩, -, -, -, hh0, hP, hXg, -, -⟩, -, hnice⟩ := hH
  have := hP
  set K := Icc (t - η) (t + η) with hKdef
  refine ⟨η, hη, hat, htb, k₀, ?_, ?_⟩
  · rw [ae_all_iff]
    intro k
    by_cases hk : k ≥ k₀
    · exact (hfin k hk).mono fun ω h _ => h
    · exact ae_of_all _ fun ω h => absurd h hk
  intro f hf hfc hfK
  obtain ⟨Cf, hCf⟩ := hf.bounded_above_of_compact_support hfc
  have hCf0 : 0 ≤ Cf := (norm_nonneg _).trans (hCf 0)
  have hXm := measurable_ofFun_add_bdryUI hXg.measurable_coord h0
  set F : ℕ → Ω → ℝ := fun k ω => ∫ x, f x ∂(bdryApprox γ (ofFun h0 + X ω) k) with hFdef
  set G : Ω → ℝ := fun ω => ∫ x, f x ∂(prop16Nu γ h0 a b (X ω)) with hGdef
  have hFm : ∀ k, Measurable (F k) := fun k =>
    (LQGMeas.meas_integral_bdryApprox γ k hf.measurable).comp hXm
  -- the pathwise part: a.s. convergence
  have hts : tsupport f ⊆ Ioo a b := by
    refine (closure_minimal (fun x hx => ?_) (isClosed_Icc (a := t - η) (b := t + η))).trans
      (fun x (hx : x ∈ Icc (t - η) (t + η)) => ⟨by linarith [hx.1], by linarith [hx.2]⟩)
    by_contra h
    exact hx (hfK x h)
  have hlg : ∀ᵐ ω ∂P, Prop16Area.G.IsLocallyGoodOn γ (D ∪ realSet (Ioo a b)) (X ω) :=
    hnice.mono fun _ h => h.isLocallyGoodOn
  have hconv : ∀ᵐ ω ∂P, Tendsto (fun k => F k ω) atTop (𝓝 (G ω)) := by
    filter_upwards [Prop16Area.G.prop16_hexB hγ hDo hDH hh0 hlg] with ω hω
    obtain ⟨ν, hν⟩ := hω
    have heq : prop16Nu γ h0 a b (X ω) = ν := LocalRule.qBoundaryMeasureOn_eq isOpen_Ioo hν
    simp only [hFdef, hGdef, heq]
    exact hν.2.2 f hf hfc hts
  -- the shifted families
  set M : ℕ → Ω → ℝ := fun k ω =>
    (bdryApprox γ (ofFun h0 + X ω) (k + k₀) K).toReal with hMdef
  set Fs : ℕ → Ω → ℝ := fun k => F (k + k₀) with hFsdef
  have hle : ∀ k, ∀ᵐ ω ∂P, ‖Fs k ω‖ ≤ Cf * ‖M k ω‖ := fun k =>
    (hfin (k + k₀) (Nat.le_add_left _ _)).mono fun ω hω => by
      rw [Real.norm_eq_abs (M k ω), abs_of_nonneg ENNReal.toReal_nonneg]
      exact norm_integral_le_of_vanish_bdryUI hCf hfK hω
  have hFsU : UniformIntegrable Fs 1 P :=
    uniformIntegrable_of_le_mul_bdryUI hCf0 hU (fun k => (hFm (k + k₀)).aestronglyMeasurable) hle
  have hconv' : ∀ᵐ ω ∂P, Tendsto (fun k => Fs k ω) atTop (𝓝 (G ω)) :=
    hconv.mono fun ω h => h.comp (tendsto_add_atTop_nat k₀)
  have hGm : MemLp G 1 P := hFsU.memLp_of_ae_tendsto hconv'
  have hGi : Integrable G P := memLp_one_iff_integrable.1 hGm
  have hFi : ∀ k ≥ k₀, Integrable (F k) P := fun k hk => by
    have e : k = (k - k₀) + k₀ := (Nat.sub_add_cancel hk).symm
    rw [e]
    exact memLp_one_iff_integrable.1 (hFsU.memLp (k - k₀))
  refine ⟨fun k hk => (hFi k hk).sub hGi, ?_⟩
  have hV := tendsto_Lp_finite_of_tendsto_ae le_rfl ENNReal.one_ne_top
    (fun k => (hFm (k + k₀)).aestronglyMeasurable) hGm hFsU.2.1 hconv'
  have hV' : Tendsto (fun k => ∫ ω, |F (k + k₀) ω - G ω| ∂P) atTop (𝓝 0) := by
    have h2 := (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp hV
    rw [ENNReal.toReal_zero] at h2
    refine h2.congr fun k => ?_
    simp only [Function.comp_apply, eLpNorm_one_eq_lintegral_enorm]
    rw [← integral_norm_eq_lintegral_enorm
      ((hFm (k + k₀)).aestronglyMeasurable.sub hGm.1)]
    simp only [Pi.sub_apply, Real.norm_eq_abs]
  exact (tendsto_add_atTop_iff_nat k₀).1 hV'

end Prop16Asm

end QuantumZipper
