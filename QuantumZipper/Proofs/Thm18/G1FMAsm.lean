import QuantumZipper.Proofs.Thm18.G1FMDPart
import QuantumZipper.Proofs.Thm18.G1PairLipRed
import QuantumZipper.Proofs.Zipper.D3PlusN2FirstModeBC

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# G1-FIRSTMODE (2): `G1RestFirstModeStmt` from a first-mode bound for the pushed free field

The node `G1RestFirstModeStmt` (G1PairLipRed.lean) asks for an a.s. bound `C/√τ` on the first
circle mode of `s ↦ evalReg x (fc(w + τe^{iθ}, s))`, `x` the pulled-back canonical wedge field.
We split the raw value (`G1RC.raw_coordChange_rescale_wedge`, RC3 `G1RC.ae_rc3_of`) as

  `evalReg x (fc(v, s)) = V(v, s, S) + dPart(v, s)`,

where `V(d, r, S)` is the continuous modification of `X((S ψ)_* fc(d, r))` with a.s. limits of
the smoothed pairings (`G1RC.exists_pushed_limit`, from the proved `G1PsiExtStmt`) evaluated at
the random canonical scale `S`, and `dPart` is the deterministic part (profile, `Q log S`,
`Q ∫ log|ψ'|`), bounded near compacts of `H` (`G1FM.dPart_bound`), so its first mode is
`≤ 2π M ≤ 2π M/√τ`.

The Gaussian part is the node `G1FMPushStmt` stated here: for every map `ψ` with the properties
`G1RC.PsiGood` of the selected inverse uniformizers and every continuous modification `V` of the
pushed circle pairings `X((S ψ)_* fc(d, r))` (circles inside `H`), a.s. the first mode of
`V(·, ·, S)` is `O(τ^{-1/2})` uniformly for `w` in a compact of `H`, `s < τ < τ₀` and `S` in a
compact of `(0, ∞)`. This is the pushed, scale-uniform analogue of the proved free-field node
`D3Plus.N2ZFirstModeStmt` (Hu–Miller–Peres, *Thick points of the Gaussian free field*,
Ann. Probab. 38 (2010), Prop. 2.1 and its proof).

Main result: `g1RestFirstMode_of_push : G1FMPushStmt → G1RestFirstModeStmt`.
Own bookkeeping (the analytic inputs are the cited proved lemmas).
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Metric Set Function
open scoped Topology NNReal Real

namespace QuantumZipper
namespace Thm18Asm

/-- **Node G1-FM-PUSH**: first-mode bound for the free field pushed by a conformal map, uniform
in the scale `S` on compacts of `(0, ∞)`. -/
def G1FMPushStmt : Prop :=
  ∀ ψ : ℂ → ℂ, G1RC.PsiGood ψ →
    ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
      (X : Ω → FieldSample), IsFreeGFFModConstH X P →
    ∀ V : ℂ × ℝ × ℝ → Ω → ℝ, (∀ ω, ContinuousOn (fun p => V p ω) (univ ×ˢ Ioi 0 ×ˢ Ioi 0)) →
      (∀ (d : ℂ) (r S : ℝ), 0 < r → r < d.im → 0 < S → (fun ω => V (d, r, S) ω) =ᵐ[P]
        fun ω => X ω ((foldedCircle d r).map fun z => (S : ℂ) * ψ z)) →
      ∀ᵐ ω ∂P, ∀ K : Set ℂ, IsCompact K → K ⊆ H → ∀ N : ℕ, ∃ C τ₀ : ℝ, 0 < τ₀ ∧
        ∀ w ∈ K, ∀ τ ∈ Ioo 0 τ₀, ∀ s ∈ Ioo 0 τ,
          ∀ S ∈ Icc (1 / ((N : ℝ) + 1)) ((N : ℝ) + 1),
            ‖D3Plus.fmInt (fun p => V (p.1, p.2, S) ω) w τ s‖ ≤ C / Real.sqrt τ

namespace G1FM

open G1RC F1.RC3Two CA.Koebe WedgeTK CircleFubini

theorem exists_nat_Icc {S : ℝ} (hS : 0 < S) :
    ∃ N : ℕ, S ∈ Icc (1 / ((N : ℝ) + 1)) ((N : ℝ) + 1) := by
  obtain ⟨N, hN⟩ := exists_nat_gt (max S S⁻¹)
  have h1 : S < N := (le_max_left _ _).trans_lt hN
  have h2 : S⁻¹ < N := (le_max_right _ _).trans_lt hN
  refine ⟨N, ?_, by linarith⟩
  rw [div_le_iff₀ (by positivity)]
  have h3 : S * S⁻¹ = 1 := mul_inv_cancel₀ hS.ne'
  nlinarith

theorem circ_mem_Hbar {w : ℂ} {τ : ℝ} (hτ : 0 ≤ τ) (hw : τ < w.im) (θ : ℝ) :
    w + (τ : ℂ) * Complex.exp ((θ : ℂ) * Complex.I) ∈ Hbar := by
  show (0 : ℝ) ≤ (w + (τ : ℂ) * Complex.exp ((θ : ℂ) * Complex.I)).im
  rw [Complex.add_im, Complex.im_ofReal_mul, Complex.exp_ofReal_mul_I_im]
  nlinarith [Real.neg_one_le_sin θ]

theorem dist_circ {w : ℂ} {τ : ℝ} (hτ : 0 ≤ τ) (θ : ℝ) :
    dist (w + (τ : ℂ) * Complex.exp ((θ : ℂ) * Complex.I)) w = τ := by
  rw [dist_eq_norm, add_sub_cancel_left, norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one,
    Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hτ]

end G1FM

open G1RC F1.RC3Two CA.Koebe WedgeTK CircleFubini in
/-- **G1-REST-FIRSTMODE from the pushed first-mode node.** -/
theorem g1RestFirstMode_of_push (hP : G1FMPushStmt) : G1RestFirstModeStmt := by
  intro γ hγ hγ2 Ω _ P _ B hB Ω' _ P' _ X A hX hA hXA Ψ hΨ
  obtain ⟨G, hG⟩ := exists_isRegVersion hX
  have hExt : G1PsiExtStmt := g1PsiExtStmt_of_holder_α g1GoodBMStmt_sideHolderGood
  have hgoodA : ∀ᵐ a ∂(P.map (pathOf B)), ∀ left, PsiGood (Ψ left a) :=
    ae_map_pathOf_of_chord g1RegPathChordStmt hγ hγ2 hB hΨ
      (fun ψs => ∀ left, PsiGood (ψs left)) (fun a hc hs left => psiGood_of_sel hΨ hc hs left)
  filter_upwards [hExt γ hγ hγ2 P B hB P' X A hX hA hXA Ψ hΨ,
    g1ProfileStmt_holds γ hγ hγ2 P B hB P' X A hX hA hXA Ψ hΨ,
    ae_rc3_of hExt (g1RawSmoothStmt_of_profile g1ProfileStmt_holds) γ hγ hγ2 P B hB P' X A
      hX hA hXA Ψ hΨ, hgoodA] with a ha1 ha2 ha3 ha4 left
  obtain ⟨ψe, hψem, hψec, hψeH, heq, β, hβ, hBd⟩ := ha1 left
  obtain ⟨V, hVc, hVmod, hVlim⟩ := exists_pushed_limit hψem hψec hψeH hβ hBd hX hG
  have hψ := ha4 left
  have hmodψ : ∀ (d : ℂ) (r S : ℝ), 0 < r → r < d.im → 0 < S → (fun ω => V (d, r, S) ω) =ᵐ[P']
      fun ω => X ω ((foldedCircle d r).map fun z => (S : ℂ) * Ψ left a z) := by
    intro d r S hr hrd hS
    have hmap : (foldedCircle d r).map (fun z => (S : ℂ) * ψe z) =
        (foldedCircle d r).map (fun z => (S : ℂ) * Ψ left a z) := by
      refine Measure.map_congr ?_
      have hd : d ∈ Hbar := show (0 : ℝ) ≤ d.im by linarith
      filter_upwards [foldedCircle_ae_dist_le' hd hr.le] with z hz
      have h1 : |(z - d).im| ≤ ‖z - d‖ := Complex.abs_im_le_norm _
      rw [Complex.sub_im, ← dist_eq_norm] at h1
      have hzH : z ∈ H := show 0 < z.im by linarith [neg_abs_le (z.im - d.im)]
      rw [heq hzH]
    filter_upwards [hVmod d r S hr hS] with ω h
    rw [h, hmap]
  filter_upwards [ha2 left G hG, ha3 left, hVlim, hP _ hψ P' X hX V hVc hmodψ,
    ae_wedgeGood hX hA hXA hG, ae_scale_pos hγ hγ2 hX hA hXA, F1.ae_growth_radAvgReg hX,
    F1.ae_growth_wedge hA] with ω' hω hrc hlim hb hW hS hr hw
  obtain ⟨K₁, M₁, hM₁, h₁⟩ := hr
  obtain ⟨K₂, M₂, hM₂, h₂⟩ := hw
  have hgm := measurable_wg (x := X ω') (Q := Qc γ) hW.cont
  have hgc := continuousOn_wg (Q := Qc γ) hW.good hW.cont
  have hbd := bd_wg (Q := Qc γ) (A := fun t => A t ω') hM₁ hM₂ h₁ h₂
  set S := scaleParam γ (wedge0 γ X A ω') with hSdef
  intro K hK hKH
  obtain ⟨N, hN⟩ := G1FM.exists_nat_Icc hS
  obtain ⟨C₁, τ₁, hτ₁, hb₁⟩ := hb K hK hKH N
  obtain ⟨M, τ₂, hM, hτ₂, hτ₂K, hbM⟩ := G1FM.dPart_bound hψ hS hgm hgc hbd hK hKH
  refine ⟨C₁ + M * (2 * π), min (min τ₁ τ₂) 1, lt_min (lt_min hτ₁ hτ₂) one_pos,
    fun w hw τ hτ s hs => ?_⟩
  have hτ0 : 0 < τ := hτ.1
  have hτ1 : τ < τ₁ := hτ.2.trans_le ((min_le_left _ _).trans (min_le_left _ _))
  have hτ2 : τ < τ₂ := hτ.2.trans_le ((min_le_left _ _).trans (min_le_right _ _))
  have hτ3 : τ < 1 := hτ.2.trans_le (min_le_right _ _)
  have hs0 : 0 < s := hs.1
  have hwτ : τ < w.im := hτ2.trans (hτ₂K w hw)
  set v : ℝ → ℂ := fun θ => w + (τ : ℂ) * Complex.exp ((θ : ℂ) * Complex.I) with hv
  have hvH : ∀ θ, v θ ∈ Hbar := fun θ => G1FM.circ_mem_Hbar hτ0.le hwτ θ
  have hvc : Continuous v := by rw [hv]; fun_prop
  have hρ : Tendsto (fun k : ℕ => S * radius k) atTop (𝓝[>] 0) := by
    refine tendsto_nhdsWithin_iff.2 ⟨?_, Eventually.of_forall fun k => mul_pos hS (radius_pos k)⟩
    simpa using (RegClosure.tendsto_radius_nhdsGT.mono_right nhdsWithin_le_nhds).const_mul S
  have hsplit : ∀ θ, evalReg (coordChange (wedgeRep γ X A ω') (Ψ left a) (Qc γ))
      (foldedCircle (v θ) s) = V (v θ, s, S) ω' + dPart γ X A (Ψ left a) ω' (v θ, s) := by
    intro θ
    rw [hrc (v θ) (hvH θ) s hs0]
    exact raw_coordChange_rescale_wedge hW (Qc γ) hS hψ.1 heq hs0 (hω.1 (v θ) (hvH θ) s hs0)
      ((hlim (v θ) s S hs0 hS).comp hρ)
  have hc1 : Continuous fun θ : ℝ => V (v θ, s, S) ω' := by
    refine (hVc ω').comp_continuous (by fun_prop) fun θ => ?_
    exact ⟨mem_univ _, show (0 : ℝ) < s from hs0, show (0 : ℝ) < S from hS⟩
  have hc2 : Continuous fun θ : ℝ => dPart γ X A (Ψ left a) ω' (v θ, s) :=
    hω.2.1.comp_continuous (by fun_prop) fun θ => ⟨hvH θ, show (0 : ℝ) < s from hs0⟩
  have hint : (∫ θ in (0 : ℝ)..(2 * π),
      ((evalReg (coordChange (wedgeRep γ X A ω') (Ψ left a) (Qc γ))
          (foldedCircle (w + (τ : ℂ) * Complex.exp ((θ : ℂ) * Complex.I)) s) : ℝ) : ℂ) *
        Complex.exp ((θ : ℂ) * Complex.I)) =
      D3Plus.fmInt (fun p => V (p.1, p.2, S) ω') w τ s +
        ∫ θ in (0 : ℝ)..(2 * π), ((dPart γ X A (Ψ left a) ω' (v θ, s) : ℝ) : ℂ) *
          Complex.exp ((θ : ℂ) * Complex.I) := by
    unfold D3Plus.fmInt
    rw [← intervalIntegral.integral_add]
    · refine intervalIntegral.integral_congr fun θ _ => ?_
      simp only
      rw [show w + (τ : ℂ) * Complex.exp ((θ : ℂ) * Complex.I) = v θ from rfl, hsplit θ]
      push_cast
      ring
    · exact ((Complex.continuous_ofReal.comp hc1).mul (by fun_prop)).intervalIntegrable _ _
    · exact ((Complex.continuous_ofReal.comp hc2).mul (by fun_prop)).intervalIntegrable _ _
  have hD : ‖∫ θ in (0 : ℝ)..(2 * π), ((dPart γ X A (Ψ left a) ω' (v θ, s) : ℝ) : ℂ) *
      Complex.exp ((θ : ℂ) * Complex.I)‖ ≤ M * (2 * π) := by
    have := intervalIntegral.norm_integral_le_of_norm_le_const (a := 0) (b := 2 * π) (C := M)
      (f := fun θ : ℝ => ((dPart γ X A (Ψ left a) ω' (v θ, s) : ℝ) : ℂ) *
        Complex.exp ((θ : ℂ) * Complex.I)) fun θ _ => by
      rw [norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one, Complex.norm_real,
        Real.norm_eq_abs]
      exact hbM w hw (v θ) ((G1FM.dist_circ hτ0.le θ).le.trans hτ2.le) s hs0
        (hs.2.trans hτ2).le
    rwa [sub_zero, abs_of_pos (by positivity)] at this
  have hsq : 0 < Real.sqrt τ := Real.sqrt_pos.2 hτ0
  have hsq1 : Real.sqrt τ ≤ 1 := Real.sqrt_le_one.mpr hτ3.le
  have hle : M * (2 * π) ≤ M * (2 * π) / Real.sqrt τ :=
    le_div_self (by positivity) hsq hsq1
  rw [hint, add_div]
  calc _ ≤ ‖D3Plus.fmInt (fun p => V (p.1, p.2, S) ω') w τ s‖ + M * (2 * π) :=
        (norm_add_le _ _).trans (add_le_add le_rfl hD)
    _ ≤ _ := add_le_add (hb₁ w hw τ ⟨hτ0, hτ1⟩ s hs S hN) hle

end Thm18Asm
end QuantumZipper
