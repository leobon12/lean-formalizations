import QuantumZipper.Proofs.Section5.Prop16NodeB2Reg
import Mathlib.Topology.PartitionOfUnity

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# Proposition 1.6, node B′: `Prop16BdryL1Stmt` from its local form

`prop16BdryL1Stmt_of_loc : Prop16BdryL1LocStmt → Prop16BdryL1Stmt`. The window statement
`Prop16BdryL1Stmt` (`L¹(P)` convergence of `∫ f d bdryApprox_k(h0 + X)` to `∫ f dν_h` for test
functions `f` vanishing off a window `[a',b'] ⊂ (a,b)`) follows from the **local** statement
`Prop16BdryL1LocStmt`: every `t ∈ (a,b)` has a neighbourhood `[t − η, t + η] ⊂ (a,b)` on which the
approximations are a.s. finite at small scales and the convergence holds (with integrable differences) for test
functions vanishing off it. The local form is the one the M7 half-disc coupling at `t`
(`K3.mixedFreeCouplingHalfDisc_holds`, `ae_avgReg_coupling`) is designed to give.

Proof: a finite subcover of `[a',b']` and a subordinate continuous partition of unity (mathlib's
`PartitionOfUnity.exists_isSubordinate`) split `f = ∑ ρ_i f`; the integrals split a.s. (finite
measures on the pieces), and the triangle inequality bounds the window error by the sum of the
local ones. Own elementary argument.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Metric
open scoped Topology ENNReal

namespace QuantumZipper

namespace Prop16Asm

/-- **Local form of node `Prop16BdryL1Stmt`.** -/
def Prop16BdryL1LocStmt : Prop :=
  ∀ (γ : ℝ) (D : Set ℂ) (c d a b : ℝ) (h0 : ℂ → ℝ) {Ω : Type} [MeasurableSpace Ω]
    (P : Measure Ω) (X : Ω → FieldSample), Prop16PalmHyp γ D c d a b h0 P X →
    ∀ t ∈ Ioo a b, ∃ η > 0, a < t - η ∧ t + η < b ∧ ∃ k₀ : ℕ,
      (∀ᵐ ω ∂P, ∀ k ≥ k₀, bdryApprox γ (ofFun h0 + X ω) k (Icc (t - η) (t + η)) < ⊤) ∧
      ∀ f : ℝ → ℝ, Continuous f → HasCompactSupport f → (∀ x ∉ Icc (t - η) (t + η), f x = 0) →
        (∀ k ≥ k₀, Integrable (fun ω => ∫ x, f x ∂(bdryApprox γ (ofFun h0 + X ω) k) -
          ∫ x, f x ∂(prop16Nu γ h0 a b (X ω))) P) ∧
        Tendsto (fun k => ∫ ω, |∫ x, f x ∂(bdryApprox γ (ofFun h0 + X ω) k) -
          ∫ x, f x ∂(prop16Nu γ h0 a b (X ω))| ∂P) atTop (𝓝 0)

/-- A bounded continuous function vanishing off `K` is integrable for a measure finite on `K`. -/
theorem integrable_of_vanish_off_Icc {g : ℝ → ℝ} (hg : Continuous g) {C : ℝ}
    (hC : ∀ x, ‖g x‖ ≤ C) {p q : ℝ} (hK : ∀ x ∉ Icc p q, g x = 0) {μ : Measure ℝ}
    (hμ : μ (Icc p q) < ⊤) : Integrable g μ := by
  have e : g = (Icc p q).indicator g := by
    funext x
    by_cases hx : x ∈ Icc p q
    · rw [indicator_of_mem hx]
    · rw [indicator_of_notMem hx, hK x hx]
  rw [e, integrable_indicator_iff measurableSet_Icc]
  have : IsFiniteMeasure (μ.restrict (Icc p q)) := isFiniteMeasure_restrict.2 hμ.ne
  exact Integrable.of_bound hg.aestronglyMeasurable C (ae_of_all _ hC)

/-- **`Prop16BdryL1Stmt` from its local form.** -/
theorem prop16BdryL1Stmt_of_loc (hL : Prop16BdryL1LocStmt) : Prop16BdryL1Stmt := by
  intro γ D c d a b h0 Ω _ P X hH a' b' ha hb f hf hfc hfab
  have hloc := hL γ D c d a b h0 P X hH
  obtain ⟨⟨-, -, -, -, -, -, -, -, -, -, hfin⟩, hν, -⟩ := hH
  choose! η hη using hloc
  have hsub : Icc a' b' ⊆ Ioo a b := fun x hx => ⟨by linarith [hx.1], by linarith [hx.2]⟩
  set U : Icc a' b' → Set ℝ := fun t => Ioo ((t : ℝ) - η t) ((t : ℝ) + η t) with hU
  obtain ⟨F, hF⟩ := isCompact_Icc.elim_finite_subcover U (fun t => isOpen_Ioo)
    (fun x hx => mem_iUnion.2 ⟨⟨x, hx⟩, by
      have := (hη x (hsub hx)).1
      exact ⟨by simp only; linarith, by simp only; linarith⟩⟩)
  set V : F → Set ℝ := fun i => U i.1 with hV
  have hsV : Icc a' b' ⊆ ⋃ i : F, V i := fun x hx => by
    obtain ⟨t, ht, hxt⟩ := mem_iUnion₂.1 (hF hx)
    exact mem_iUnion.2 ⟨⟨t, ht⟩, hxt⟩
  obtain ⟨ρ, hρ⟩ := PartitionOfUnity.exists_isSubordinate isClosed_Icc V (fun i => isOpen_Ioo) hsV
  set T : F → ℝ := fun i => ((i.1 : Icc a' b') : ℝ) with hT
  have hTab : ∀ i, T i ∈ Ioo a b := fun i => hsub (i.1 : Icc a' b').2
  set K : F → Set ℝ := fun i => Icc (T i - η (T i)) (T i + η (T i)) with hK
  set g : F → ℝ → ℝ := fun i x => ρ i x * f x with hg
  have hgc : ∀ i, Continuous (g i) := fun i => (ρ i).continuous.mul hf
  have hgcs : ∀ i, HasCompactSupport (g i) := fun i => hfc.mul_left
  have hgK : ∀ i, ∀ x ∉ K i, g i x = 0 := fun i x hx => by
    have : ρ i x = 0 := image_eq_zero_of_notMem_tsupport fun hmem =>
      hx (Ioo_subset_Icc_self (hρ i hmem))
    simp only [hg, this, zero_mul]
  have hfsum : f = fun x => ∑ i, g i x := by
    funext x
    by_cases hx : x ∈ Icc a' b'
    · have h1 := ρ.sum_eq_one hx
      rw [finsum_eq_sum_of_fintype] at h1
      simp only [hg, ← Finset.sum_mul, h1, one_mul]
    · simp only [hg, hfab x hx, mul_zero, Finset.sum_const_zero]
  obtain ⟨Cf, hCf⟩ := hf.bounded_above_of_compact_support hfc
  have hgb : ∀ i x, ‖g i x‖ ≤ Cf := fun i x => by
    have h0 := ρ.nonneg i x
    have h1 := ρ.le_one i x
    simp only [hg, norm_mul, Real.norm_eq_abs, abs_of_nonneg h0]
    calc ρ i x * |f x| ≤ 1 * |f x| := by gcongr
      _ = ‖f x‖ := by rw [one_mul, Real.norm_eq_abs]
      _ ≤ Cf := hCf x
  choose k₀ hk₀ using fun i => (hη (T i) (hTab i)).2.2.2
  set K₀ : ℕ := ∑ i, k₀ i with hK₀
  have hK₀i : ∀ i, k₀ i ≤ K₀ := fun i =>
    Finset.single_le_sum (f := k₀) (fun j _ => Nat.zero_le _) (Finset.mem_univ i)
  have hloc := fun i => (hk₀ i).2 (g i) (hgc i) (hgcs i) (hgK i)
  -- almost sure splitting
  have hA : ∀ᵐ ω ∂P, ∀ i, ∀ k ≥ K₀, bdryApprox γ (ofFun h0 + X ω) k (K i) < ⊤ :=
    ae_all_iff.2 fun i => (hk₀ i).1.mono fun ω hω k hk => hω k ((hK₀i i).trans hk)
  have hNu : ∀ᵐ ω ∂P, prop16Nu γ h0 a b (X ω) (Icc a b) < ⊤ :=
    ae_lt_top' ((Measure.measurable_coe measurableSet_Icc).comp_aemeasurable hν) hfin.ne
  have hKab : ∀ i, K i ⊆ Icc a b := fun i => by
    have := hη (T i) (hTab i)
    exact Icc_subset_Icc (by linarith [this.2.1]) (by linarith [this.2.2.1])
  have hkey : ∀ k ≥ K₀, ∀ᵐ ω ∂P, |∫ x, f x ∂(bdryApprox γ (ofFun h0 + X ω) k) -
      ∫ x, f x ∂(prop16Nu γ h0 a b (X ω))| ≤
      ∑ i, |∫ x, g i x ∂(bdryApprox γ (ofFun h0 + X ω) k) -
        ∫ x, g i x ∂(prop16Nu γ h0 a b (X ω))| := fun k hk => by
    filter_upwards [hA, hNu] with ω hAω hNω
    have hiA : ∀ i, Integrable (g i) (bdryApprox γ (ofFun h0 + X ω) k) := fun i =>
      integrable_of_vanish_off_Icc (hgc i) (hgb i) (hgK i) (hAω i k hk)
    have hiN : ∀ i, Integrable (g i) (prop16Nu γ h0 a b (X ω)) := fun i =>
      integrable_of_vanish_off_Icc (hgc i) (hgb i) (hgK i)
        (lt_of_le_of_lt (measure_mono (hKab i)) hNω)
    rw [hfsum, integral_finsetSum _ fun i _ => hiA i, integral_finsetSum _ fun i _ => hiN i,
      ← Finset.sum_sub_distrib]
    exact Finset.abs_sum_le_sum_abs _ _
  have hle : ∀ k ≥ K₀, ∫ ω, |∫ x, f x ∂(bdryApprox γ (ofFun h0 + X ω) k) -
      ∫ x, f x ∂(prop16Nu γ h0 a b (X ω))| ∂P ≤
      ∑ i, ∫ ω, |∫ x, g i x ∂(bdryApprox γ (ofFun h0 + X ω) k) -
        ∫ x, g i x ∂(prop16Nu γ h0 a b (X ω))| ∂P := fun k hk => by
    rw [← integral_finsetSum _ fun i _ => ((hloc i).1 k ((hK₀i i).trans hk)).abs]
    exact integral_mono_of_nonneg (ae_of_all _ fun ω => abs_nonneg _)
      (integrable_finsetSum _ fun i _ => ((hloc i).1 k ((hK₀i i).trans hk)).abs) (hkey k hk)
  have hsum : Tendsto (fun k => ∑ i, ∫ ω, |∫ x, g i x ∂(bdryApprox γ (ofFun h0 + X ω) k) -
      ∫ x, g i x ∂(prop16Nu γ h0 a b (X ω))| ∂P) atTop (𝓝 0) := by
    simpa using tendsto_finsetSum (Finset.univ : Finset F) fun i _ => (hloc i).2
  exact squeeze_zero' (Eventually.of_forall fun k => integral_nonneg fun ω => abs_nonneg _)
    (eventually_atTop.2 ⟨K₀, hle⟩) hsum

end Prop16Asm

end QuantumZipper
