import QuantumZipper.Proofs.Section5.Prop16BdryL1UI

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# Proposition 1.6, node B′: uniform integrability from a uniform moment bound

`prop16BdryUIStmt_of_mom : Prop16BdryMomStmt → Prop16BdryUIStmt`, hence
`prop16BdryL1LocStmt_of_mom : Prop16BdryMomStmt → Prop16BdryL1LocStmt`.

`Prop16BdryMomStmt`: near every point of the free arc, the approximating boundary masses of the
mixed field have a moment of some order `p > 1` bounded uniformly in the scale. A family bounded
in `L^p`, `p > 1`, on a probability space is uniformly integrable (Hölder:
`E[|Y| ; S] ≤ ‖Y‖_p P(S)^{1-1/p}`). Own elementary argument for this step (mathlib has Hölder,
`eLpNorm_le_eLpNorm_mul_rpow_measure_univ`, but not the `L^p`-bounded ⇒ UI corollary).

This is the alternative leaf for the moment chain of the free field
(`GMC/BdryMomentsScale.lean`, `momentDyadic_of_innerMomentStmt`); the uniform-integrability leaf
`Prop16BdryUIStmt` itself is exactly the step proved by Duplantier–Sheffield, *Liouville quantum
gravity and KPZ*, Invent. Math. 185 (2011), proof of Prop. 1.2 (eqs. (29)–(30), rooted
measures), boundary version §6.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology ENNReal NNReal

namespace QuantumZipper

namespace Prop16Asm

/-- **Node B′-MOM (uniform moment bound near the free arc).** Every `t ∈ (a,b)` has a window
`[t-η, t+η] ⊂ (a,b)`, a scale `k₀`, an exponent `p > 1` and a finite `A` with
`E[bdryApprox_k(h0 + X)([t-η,t+η])^p] ≤ A` for all `k ≥ k₀`. -/
def Prop16BdryMomStmt : Prop :=
  ∀ (γ : ℝ) (D : Set ℂ) (c d a b : ℝ) (h0 : ℂ → ℝ) {Ω : Type} [MeasurableSpace Ω]
    (P : Measure Ω) (X : Ω → FieldSample), Prop16PalmHyp γ D c d a b h0 P X →
    ∀ t ∈ Ioo a b, ∃ η > 0, a < t - η ∧ t + η < b ∧ ∃ k₀ : ℕ, ∃ p : ℝ, 1 < p ∧
      ∃ A : ℝ≥0∞, A ≠ ⊤ ∧ ∀ k ≥ k₀,
        ∫⁻ ω, bdryApprox γ (ofFun h0 + X ω) k (Icc (t - η) (t + η)) ^ p ∂P ≤ A

/-- An `L^p`-bounded (`p > 1`) family of `[0,∞]`-valued random variables is uniformly integrable
after `toReal`. Own elementary argument (Hölder). -/
theorem uniformIntegrable_toReal_of_lintegral_rpow_le {Ω : Type} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] {m : ℕ → Ω → ℝ≥0∞} (hm : ∀ k, Measurable (m k))
    {p : ℝ} (hp : 1 < p) {A : ℝ≥0∞} (hA : A ≠ ⊤) (hb : ∀ k, ∫⁻ ω, m k ω ^ p ∂P ≤ A) :
    UniformIntegrable (fun k ω => (m k ω).toReal) 1 P := by
  have hp0 : 0 < p := by linarith
  set q : ℝ≥0∞ := ENNReal.ofReal p with hqdef
  have hq0 : q ≠ 0 := by
    rw [hqdef, ne_eq, ENNReal.ofReal_eq_zero, not_le]; exact hp0
  have hqt : q ≠ ⊤ := ENNReal.ofReal_ne_top
  have hqr : q.toReal = p := ENNReal.toReal_ofReal hp0.le
  have h1q : (1 : ℝ≥0∞) ≤ q := by
    rw [hqdef, ← ENNReal.ofReal_one]; exact ENNReal.ofReal_le_ofReal hp.le
  have hmeas : ∀ k, AEStronglyMeasurable (fun ω => (m k ω).toReal) P := fun k =>
    (ENNReal.measurable_toReal.comp (hm k)).aestronglyMeasurable
  have hAp : A ^ (1 / p) ≠ ⊤ := ENNReal.rpow_ne_top_of_nonneg (by positivity) hA
  have hLq : ∀ k (s : Set Ω),
      eLpNorm (fun ω => (m k ω).toReal) q (P.restrict s) ≤ A ^ (1 / p) := by
    intro k s
    rw [eLpNorm_eq_lintegral_rpow_enorm_toReal hq0 hqt, hqr]
    refine ENNReal.rpow_le_rpow ?_ (by positivity)
    calc ∫⁻ ω in s, ‖(m k ω).toReal‖ₑ ^ p ∂P ≤ ∫⁻ ω in s, m k ω ^ p ∂P :=
          lintegral_mono fun ω => by
            refine ENNReal.rpow_le_rpow ?_ hp0.le
            rw [Real.enorm_of_nonneg ENNReal.toReal_nonneg]
            exact ENNReal.ofReal_toReal_le
      _ ≤ ∫⁻ ω, m k ω ^ p ∂P := setLIntegral_le_lintegral _ _
      _ ≤ A := hb k
  have hr : 0 < 1 - 1 / p := by
    rw [sub_pos, div_lt_one hp0]; exact hp
  have hH : ∀ k (s : Set Ω), eLpNorm (fun ω => (m k ω).toReal) 1 (P.restrict s) ≤
      A ^ (1 / p) * P s ^ (1 - 1 / p) := by
    intro k s
    have h := eLpNorm_le_eLpNorm_mul_rpow_measure_univ (μ := P.restrict s) h1q
      (hmeas k).restrict
    rw [Measure.restrict_apply_univ, ENNReal.toReal_one, hqr, div_one] at h
    exact h.trans (mul_le_mul' (hLq k s) le_rfl)
  refine ⟨hmeas, ?_, ⟨(A ^ (1 / p)).toNNReal, fun k => ?_⟩⟩
  · have hlim : Tendsto (fun ε : ℝ≥0∞ => A ^ (1 / p) * ε ^ (1 - 1 / p)) (𝓝 0) (𝓝 0) := by
      have h0 := (ENNReal.continuous_rpow_const (y := 1 - 1 / p)).tendsto 0
      rw [ENNReal.zero_rpow_of_pos hr] at h0
      simpa using ENNReal.Tendsto.const_mul h0 (Or.inr hAp)
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hlim
      (fun _ => bot_le) fun ε => ?_
    refine iSup_le fun k => iSup_le fun s => iSup_le fun hs => (hH k s).trans ?_
    exact mul_le_mul' le_rfl (ENNReal.rpow_le_rpow hs hr.le)
  · have h := hH k univ
    rw [measure_univ, ENNReal.one_rpow, mul_one, Measure.restrict_univ] at h
    rw [ENNReal.coe_toNNReal hAp]
    exact h

/-- **`Prop16BdryUIStmt` from the uniform moment bound.** -/
theorem prop16BdryUIStmt_of_mom (hM : Prop16BdryMomStmt) : Prop16BdryUIStmt := by
  intro γ D c d a b h0 Ω _ P X hH t ht
  obtain ⟨η, hη, hat, htb, k₀, p, hp, A, hA, hb⟩ := hM γ D c d a b h0 P X hH t ht
  obtain ⟨⟨-, -, -, -, -, -, -, hP, hXg, -, -⟩, -, -⟩ := hH
  have := hP
  have hXm := measurable_ofFun_add_bdryUI hXg.measurable_coord h0
  have hmk : ∀ k, Measurable fun ω =>
      bdryApprox γ (ofFun h0 + X ω) k (Icc (t - η) (t + η)) := fun k =>
    (Measure.measurable_coe measurableSet_Icc).comp ((measurable_bdryApprox γ k).comp hXm)
  refine ⟨η, hη, hat, htb, k₀, fun k hk => ?_,
    uniformIntegrable_toReal_of_lintegral_rpow_le (fun k => hmk (k + k₀)) hp hA
      fun k => hb (k + k₀) (Nat.le_add_left _ _)⟩
  have hfin : ∫⁻ ω, bdryApprox γ (ofFun h0 + X ω) k (Icc (t - η) (t + η)) ^ p ∂P ≠ ⊤ :=
    ne_top_of_le_ne_top hA (hb k hk)
  filter_upwards [ae_lt_top' ((hmk k).pow_const p).aemeasurable hfin] with ω hω
  by_contra hc
  rw [not_lt, top_le_iff] at hc
  rw [hc, ENNReal.top_rpow_of_pos (by linarith)] at hω
  exact lt_irrefl _ hω

/-- **`Prop16BdryL1LocStmt` from the uniform moment bound.** -/
theorem prop16BdryL1LocStmt_of_mom (hM : Prop16BdryMomStmt) : Prop16BdryL1LocStmt :=
  prop16BdryL1LocStmt_of_ui (prop16BdryUIStmt_of_mom hM)

end Prop16Asm

end QuantumZipper
