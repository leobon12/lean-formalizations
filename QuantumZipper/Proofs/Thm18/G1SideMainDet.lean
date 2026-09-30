import QuantumZipper.Proofs.Thm18.G1SideLim
import QuantumZipper.Proofs.Thm18.G1ZBdryTransp
import QuantumZipper.Proofs.Thm18.G4BSideLen

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# G1-SIDE (10): the side boundary limit from countably many good windows (per sample)

`WinGood γ w ψ left Φ p q N` packages, for the window `[p,q]` of the side half-line and the box
`dilBox N`, a dilation family of the reflected side map (`exists_dilFamily`) together with the
three per-sample inputs of `tendsto_side_of_family` (exactness, continuum limit, uniform offset
transport). If all rational windows are good, the pulled-back field has the side boundary limit
`((ν|_S).map Φ⁻¹)` (`sideBdryLim_of_winGood`): clauses (i)–(ii) as in `isVagueLimitOnR_side`,
clause (iii) by `tendsto_side_of_family` on a rational window containing the support.
Own bookkeeping.
-/

noncomputable section

open MeasureTheory Filter Set Function
open scoped Topology ENNReal NNReal

namespace QuantumZipper
namespace G1Side

open Thm18Asm

/-- A good rational window (per sample). -/
def WinGood (γ : ℝ) (w : FieldSample) (ψ : ℂ → ℂ) (left : Bool) (Φ : ℝ ≃o ℝ) (p q : ℝ)
    (N : ℕ) : Prop :=
  ∃ (Ψe : ℂ → ℂ) (a b a' b' : ℝ), a < a' ∧ b' < b ∧ Icc a' b' ⊆ g1SideHalf left ∧
    (∀ c ∈ Icc (1 : ℝ) 2, ∀ t ∈ Icc p q, t / c ∈ Icc a' b') ∧
    (∀ s ∈ dilBox N, EqOn (dilFam Ψe s) (fun z => (s 0 : ℂ) * ψ ((s 1 : ℂ) * z)) H) ∧
    (∀ s ∈ dilBox N, ∀ t ∈ Icc a b, dilFam Ψe s t = ((s 0 * Φ (s 1 * t) : ℝ) : ℂ)) ∧
    (∀ᶠ k in atTop, ∀ q ∈ dilBox N, (∀ u ∈ Icc a b,
      avgReg (coordChange w (dilFam Ψe q) (Qc γ)) k (u : ℂ) =
        coordChange w (dilFam Ψe q) (Qc γ) (foldedCircle (u : ℂ) (radius k))) ∧
      ContinuousOn (fun u : ℝ => avgReg (coordChange w (dilFam Ψe q) (Qc γ)) k (u : ℂ))
        (Icc a b)) ∧
    (∀ᶠ k in atTop, ∀ q ∈ dilBox N, ∀ u ∈ Icc a b,
      (∀ σ : ℝ, 0 < σ → Integrable (fun v => evalReg w (foldedCircle v σ))
        ((foldedCircle (u : ℂ) (radius k)).map (dilFam Ψe q))) ∧
      ∃ L : ℝ, Tendsto (fun σ => ∫ v, evalReg w (foldedCircle v σ)
        ∂((foldedCircle (u : ℂ) (radius k)).map (dilFam Ψe q))) (𝓝[>] 0) (𝓝 L)) ∧
    ∀ f : ℝ → ℝ, Continuous f → HasCompactSupport f → ∀ a'' b'' : ℝ,
      a < a'' → b'' < b → (∀ c ∈ Icc (1 : ℝ) 2, ∀ u, u ∉ Icc a'' b'' → f (c * u) = 0) →
      ∀ η : ℝ, 0 < η → ∀ᶠ k in atTop, ∀ q ∈ dilBox N, ∀ c ∈ Icc (1 : ℝ) 2,
        |∫ u, f (c * u) ∂bdryApprox γ (coordChange w (dilFam Ψe q) (Qc γ)) k -
          ∫ u in Icc (dilFam Ψe q a).re (dilFam Ψe q b).re,
            f (c * Function.invFunOn (fun t : ℝ => (dilFam Ψe q t).re) (Icc a b) u)
              ∂qBoundaryMeasure γ w| ≤ η

/-- **Side boundary limit from good rational windows** (per sample). -/
theorem sideBdryLim_of_winGood {γ : ℝ} (hγ : 0 < γ) {w : FieldSample} (hw : IsLQGGood γ w)
    {ψ : ℂ → ℂ} (hψm : Measurable ψ) (hψ0 : ∀ z ∈ H, deriv ψ z ≠ 0)
    (hψH : ∀ z ∈ H, ψ z ∈ H)
    (hψi : ∀ d ∈ Hbar, ∀ r > 0, Integrable (fun z => Real.log ‖deriv ψ z‖) (foldedCircle d r))
    {s : ℝ} (hs : 0 < s)
    (hRC3 : ∀ d ∈ Hbar, ∀ r > 0,
      evalReg (coordChange (rescale w (Qc γ) s) ψ (Qc γ)) (foldedCircle d r) =
        coordChange (rescale w (Qc γ) s) ψ (Qc γ) (foldedCircle d r))
    {left : Bool} {Φ : ℝ ≃o ℝ} (hΦ0 : Φ 0 = 0)
    (hwin : ∀ p q : ℚ, ∀ N : ℕ, (p : ℝ) < q → Icc (p : ℝ) q ⊆ g1SideHalf left → 1 ≤ N →
      WinGood γ w ψ left Φ p q N) :
    G1Z2SideBdryLim γ left (coordChange (rescale w (Qc γ) s) ψ (Qc γ))
      (((qBoundaryMeasure γ (rescale w (Qc γ) s)).restrict (g1SideHalf left)).map Φ.symm) := by
  have := G4Core.isLocallyFinite_qBoundaryMeasure γ (rescale w (Qc γ) s)
  have hIm := image_g1SideHalf hΦ0 left
  refine ⟨?_, fun K hK hKS => ?_, fun f hf hfc hfS => ?_⟩
  · rw [pull_apply Φ (measurableSet_g1SideHalf left).compl, image_compl_eq Φ.bijective, hIm,
      compl_inter_self, measure_empty]
  · rw [pull_apply Φ hK.isClosed.measurableSet]
    exact (measure_mono inter_subset_left).trans_lt (hK.image Φ.continuous).measure_lt_top
  -- a rational window containing the support
  obtain ⟨p0, q0, hpq0, hI0, hK0⟩ := exists_side_window left hfc hfS
  obtain ⟨p1, q1, hpq1, hI1, hK1⟩ := exists_side_window left (isCompact_Icc (a := p0) (b := q0))
    hI0
  have hp10 : p1 < p0 := (hK1 ⟨le_rfl, hpq0.le⟩).1
  have hq01 : q0 < q1 := (hK1 ⟨hpq0.le, le_rfl⟩).2
  obtain ⟨p, hp1, hp2⟩ := exists_rat_btwn hp10
  obtain ⟨q, hq1, hq2⟩ := exists_rat_btwn hq01
  have hpq : (p : ℝ) < q := by linarith
  have hIpq : Icc (p : ℝ) q ⊆ g1SideHalf left := fun x hx =>
    hI1 ⟨by linarith [hx.1], by linarith [hx.2]⟩
  have hsuppI : tsupport f ⊆ Icc (p : ℝ) q := fun x hx =>
    ⟨by linarith [(hK0 hx).1], by linarith [(hK0 hx).2]⟩
  -- the box containing the scale
  set N : ℕ := ⌈s⌉₊ + ⌈1 / s⌉₊ + 1 with hN
  have hN1 : 1 ≤ N := by omega
  have hsN : s ∈ Icc (1 / (N : ℝ)) N := by
    have h1 := Nat.le_ceil s
    have h2 := Nat.le_ceil (1 / s)
    have hNr : (N : ℝ) = ⌈s⌉₊ + ⌈1 / s⌉₊ + 1 := by rw [hN]; push_cast; ring
    have hN0 : (0 : ℝ) < N := by rw [hNr]; positivity
    constructor
    · rw [div_le_iff₀ hN0]
      have : 1 / s < N := by rw [hNr]; linarith [(Nat.cast_nonneg ⌈s⌉₊ : (0 : ℝ) ≤ _)]
      rw [div_lt_iff₀ hs] at this
      linarith
    · rw [hNr]; linarith [(Nat.cast_nonneg ⌈1 / s⌉₊ : (0 : ℝ) ≤ _)]
  obtain ⟨Ψe, a, b, a', b', ha, hb, hS', hdiv, hEqH, hbv, hExact, hCont, hOff⟩ :=
    hwin p q N hpq hIpq hN1
  have hab' : a' ≤ b' := by
    have := hdiv 1 ⟨le_rfl, by norm_num⟩ p ⟨le_rfl, hpq.le⟩
    exact this.1.trans this.2
  have htsupp : ∀ c ∈ Icc (1 : ℝ) 2, ∀ t ∈ tsupport f, t / c ∈ Icc a' b' :=
    fun c hc t ht => hdiv c hc t (hsuppI ht)
  have hvan : ∀ c ∈ Icc (1 : ℝ) 2, ∀ u, u ∉ Icc a' b' → f (c * u) = 0 := by
    intro c hc u hu
    by_contra hne
    have hc0 : 0 < c := by linarith [hc.1]
    have := htsupp c hc _ (subset_tsupport f hne)
    rw [mul_div_cancel_left₀ u hc0.ne'] at this
    exact hu this
  exact tendsto_side_of_family hγ hw hψm hψ0 (fun z hz => show 0 ≤ (ψ z).im from le_of_lt (hψH z hz)) hψi hs
    (fun d hd r hr => hRC3 d hd r hr) hΦ0 (by linarith) (Icc_subset_Icc ha.le hb.le) hS' hsN
    hEqH hbv hExact hCont hf htsupp (hOff f hf hfc a' b' ha hb hvan)

end G1Side
end QuantumZipper
