import QuantumZipper.Proofs.Thm18.G1SideAsm
import QuantumZipper.Proofs.Thm18.G1SideFam

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# G1-SIDE (11): the side boundary limit along all radii for one test function, per sample

For one sample: the pulled-back canonical field `x = coordChange (rescale w Q s) ψ Q` with RC3,
the dilation family `dilFam Ψe` on `dilBox N ∋ (s, c)` (exact at the dyadic circles, with the
continuum smoothing limits, and with the uniform transport over the dilated test functions),
then for a test function `f` supported in the side window,

  `∫ f d(bdryR γ x (c 2^{-k})) → ∫ f d(Φ⁻¹_*(ν_{rescale w Q s}|_S))`

uniformly in `c ∈ [1,2]` (`tendsto_side_of_family`). This is the coordinate-change rule of
Duplantier–Sheffield (Invent. Math. 185 (2011), Prop. 2.1) at the side map, along all radii
(Sheffield–Wang arXiv:1605.06171 Thm 1.4), assembled from G1-SIDE (1)–(10). Own bookkeeping.
-/

noncomputable section

open MeasureTheory Filter Set Function
open scoped Topology ENNReal NNReal

namespace QuantumZipper
namespace G1Side

open Thm18Asm

theorem mem_dilBox_pair {N : ℕ} {s c : ℝ} (hs : s ∈ Icc (1 / (N : ℝ)) N)
    (hc : c ∈ Icc (1 : ℝ) 2) : (![s, c] : Fin 2 → ℝ) ∈ dilBox N := by
  simp only [dilBox, mem_setOf_eq, Matrix.cons_val_zero, Matrix.cons_val_one]
  exact ⟨hs, hc⟩

set_option maxHeartbeats 800000 in
/-- **Side boundary limit along all radii for one test function** (per sample). -/
theorem tendsto_side_of_family {γ : ℝ} (hγ : 0 < γ) {w : FieldSample} (hw : IsLQGGood γ w)
    {ψ : ℂ → ℂ} (hψm : Measurable ψ) (hψ0 : ∀ z ∈ H, deriv ψ z ≠ 0)
    (hψH : ∀ z ∈ H, ψ z ∈ Hbar)
    (hψi : ∀ d ∈ Hbar, ∀ r > 0, Integrable (fun z => Real.log ‖deriv ψ z‖) (foldedCircle d r))
    {s : ℝ} (hs : 0 < s)
    (hRC3 : ∀ d ∈ Hbar, ∀ r : ℝ, 0 < r →
      evalReg (coordChange (rescale w (Qc γ) s) ψ (Qc γ)) (foldedCircle d r) =
        coordChange (rescale w (Qc γ) s) ψ (Qc γ) (foldedCircle d r))
    {left : Bool} {Φ : ℝ ≃o ℝ} (hΦ0 : Φ 0 = 0)
    {Ψe : ℂ → ℂ} {a b a' b' : ℝ} (hab : a ≤ b) (hsub : Icc a' b' ⊆ Icc a b)
    (hS : Icc a' b' ⊆ g1SideHalf left) {N : ℕ} (hsN : s ∈ Icc (1 / (N : ℝ)) N)
    (hEqH : ∀ q ∈ dilBox N, EqOn (dilFam Ψe q) (fun z => (q 0 : ℂ) * ψ ((q 1 : ℂ) * z)) H)
    (hbv : ∀ q ∈ dilBox N, ∀ t ∈ Icc a b, dilFam Ψe q t = ((q 0 * Φ (q 1 * t) : ℝ) : ℂ))
    (hExact : ∀ᶠ k in atTop, ∀ q ∈ dilBox N, (∀ u ∈ Icc a b,
      avgReg (coordChange w (dilFam Ψe q) (Qc γ)) k (u : ℂ) =
        coordChange w (dilFam Ψe q) (Qc γ) (foldedCircle (u : ℂ) (radius k))) ∧
      ContinuousOn (fun u : ℝ => avgReg (coordChange w (dilFam Ψe q) (Qc γ)) k (u : ℂ))
        (Icc a b))
    (hCont : ∀ᶠ k in atTop, ∀ q ∈ dilBox N, ∀ u ∈ Icc a b,
      (∀ σ : ℝ, 0 < σ → Integrable (fun v => evalReg w (foldedCircle v σ))
        ((foldedCircle (u : ℂ) (radius k)).map (dilFam Ψe q))) ∧
      ∃ L : ℝ, Tendsto (fun σ => ∫ v, evalReg w (foldedCircle v σ)
        ∂((foldedCircle (u : ℂ) (radius k)).map (dilFam Ψe q))) (𝓝[>] 0) (𝓝 L))
    {f : ℝ → ℝ} (hf : Continuous f)
    (htsupp : ∀ c ∈ Icc (1 : ℝ) 2, ∀ t ∈ tsupport f, t / c ∈ Icc a' b')
    (hU : ∀ η : ℝ, 0 < η → ∀ᶠ k in atTop, ∀ q ∈ dilBox N, ∀ c ∈ Icc (1 : ℝ) 2,
      |∫ u, f (c * u) ∂bdryApprox γ (coordChange w (dilFam Ψe q) (Qc γ)) k -
        ∫ u in Icc (dilFam Ψe q a).re (dilFam Ψe q b).re,
          f (c * Function.invFunOn (fun t : ℝ => (dilFam Ψe q t).re) (Icc a b) u)
            ∂qBoundaryMeasure γ w| ≤ η) :
    Tendsto (fun i => ∫ t, f t ∂bdryR γ (coordChange (rescale w (Qc γ) s) ψ (Qc γ)) (goodRad i))
      goodFilter
      (𝓝 (∫ t, f t ∂(((qBoundaryMeasure γ (rescale w (Qc γ) s)).restrict
        (g1SideHalf left)).map Φ.symm))) := by
  set ν := ((qBoundaryMeasure γ (rescale w (Qc γ) s)).restrict (g1SideHalf left)).map Φ.symm
  have hvan : ∀ c ∈ Icc (1 : ℝ) 2, ∀ u, u ∉ Icc a' b' → f (c * u) = 0 := by
    intro c hc u hu
    by_contra hne
    have hc0 : 0 < c := by linarith [hc.1]
    have := htsupp c hc _ (subset_tsupport f hne)
    rw [mul_div_cancel_left₀ u hc0.ne'] at this
    exact hu this
  have hvan1 : ∀ u, u ∉ Icc a' b' → f u = 0 := fun u hu => by
    simpa using hvan 1 ⟨le_rfl, by norm_num⟩ u hu
  rw [Metric.tendsto_nhds]
  intro ε hε
  unfold goodFilter
  rw [eventually_prod_principal_iff]
  filter_upwards [hU (ε / 2) (by positivity), hExact, hCont] with k hkU hkE hkC c hc
  have hc0 : 0 < c := by linarith [hc.1]
  set q : Fin 2 → ℝ := ![s, c] with hqdef
  have hq : q ∈ dilBox N := mem_dilBox_pair hsN hc
  have hq0 : q 0 = s := rfl
  have hq1 : q 1 = c := rfl
  -- the offset identity
  have hE : ∀ t ∈ tsupport f,
      evalReg (coordChange (rescale w (Qc γ) s) ψ (Qc γ)) (foldedCircle (t : ℂ) (c * radius k)) =
        avgReg (coordChange w (dilFam Ψe q) (Qc γ)) k ((t / c : ℝ) : ℂ) - Qc γ * Real.log c := by
    intro t ht
    have htc : t / c ∈ Icc a b := hsub (htsupp c hc t ht)
    have hEq : EqOn (dilFam Ψe q) (fun z => (s : ℂ) * ψ ((c : ℂ) * z)) H := by
      have := hEqH q hq
      simpa [hq0, hq1] using this
    obtain ⟨hint, hlim⟩ := hkC q hq _ htc
    exact offset_hE hw.1 hψm hψ0 hψH hψi hs hc0 hEq hRC3 ((hkE q hq).1 _ htc) hint hlim
  have hoff := integral_bdryR_offset_of_avg hγ hc0 k hE
  -- the limit
  have hbvq : ∀ t ∈ Icc a b, dilFam Ψe q t = ((s * Φ (c * t) : ℝ) : ℂ) := fun t ht => by
    simpa [hq0, hq1] using hbv q hq t ht
  have hid := limit_ident hγ hw hs hc hΦ0 hab hsub hS hbvq hf (hvan c hc) hvan1
  have hk := hkU q hq c hc
  rw [hid] at hk
  simp only [goodRad]
  rw [Real.dist_eq, hoff]
  linarith

end G1Side
end QuantumZipper
