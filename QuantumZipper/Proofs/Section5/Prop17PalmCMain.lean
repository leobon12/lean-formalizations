import QuantumZipper.Proofs.Section5.Prop17PalmCSetup
import QuantumZipper.Proofs.Section5.Prop17PalmZoomScale

/-!
# Proposition 1.7, Palm-zoom node C: assembly (PALM-C)

The concrete D3⁺ data at the fixed boundary point `x ∈ [0, 1]` for `ϖ = foldedCircle 0 3`
(`palmCField`, `palmCRho`, `palmCCorr`), the D3⁺ `Setup` for them (`palmC_setup`, radius `1`),
the **identification node** `Prop17PalmCAgreeStmt γ` (proved from regularity and measurability
in `Prop17PalmCAgree.lean`, `Prop17PalmCReg.lean`, `Prop17PalmCMeas.lean`), and

* `prop17FreeFixedZoom_of_agree : D3PlusIStmtRich → Prop17PalmCAgreeStmt γ →
  Prop17FreeFixedZoomStmt γ (foldedCircle 0 3) 0 1`;
* `theorem1_7_of_palmC`: `theorem1_7_of_freeNodes'` with node C replaced by these two inputs.

Why the data are right (formal computation, Sheffield, arXiv:1012.4797, proof of Prop. 1.6,
p. 25): with `s = shiftFun γ 0 ϖ x = (γ/2)(neumannH x · − kPot ϖ)` and `c₀ = ∫ s dϖ`,
`zoomField γ C (N_ϖ(s + X)) x` pairs with `μ` as
`∫ s(z + x) dμ + X(μ(· − x)) − (c₀ + X ϖ) μ(ℂ) + (C/γ) μ(ℂ)`, and
`s(z + x) = γ(−log‖z‖) − (γ/2) kPot ϖ (z + x)` (`neumannH_add_real`-type identity), which is the
pairing of `zoomModel γ γ C ρ₀ X' g` with `X' = palmCField X x`, `ρ₀ = palmCRho ϖ x`
(`X' ρ₀ = X ϖ`), `g = palmCCorr γ ϖ x`. `Prop17PalmCAgreeStmt` asks that the (regularized,
global-canonical) zoom coordinates and the (raw, local-canonical) D3⁺ model data agree inside
`closedBall 0 R` with probability `→ 1` as `C → ∞`.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Metric
open scoped Topology ENNReal NNReal ComplexConjugate

namespace QuantumZipper
namespace S5
namespace FieldLaw
namespace Raw

open WedgeMeas Factorization CoordsFull TV PalmShift FieldShift PalmNorm

/-- The free field translated by `x`: `X' ω μ = X ω (μ(· − x))`. -/
def palmCField {Ω : Type*} (X : Ω → FieldSample) (x : ℝ) (ω : Ω) : FieldSample :=
  fun μ => X ω (μ.map (· + (x : ℂ)))

/-- The normalizing measure translated by `−x`. -/
def palmCRho (ϖ : Measure ℂ) (x : ℝ) : Measure ℂ := ϖ.map (· + ((-x : ℝ) : ℂ))

/-- The deterministic correction `g = −(γ/2) kPot ϖ (· + x) − ∫ shiftFun dϖ`. -/
def palmCCorr (γ : ℝ) (ϖ : Measure ℂ) (x : ℝ) (z : ℂ) : ℝ :=
  -(γ / 2) * kPot ϖ (z + x) - ∫ u, shiftFun γ (0 : ℂ → ℝ) ϖ x u ∂ϖ

theorem palmC_norm_foldH (w : ℂ) : ‖foldH w‖ = ‖w‖ := by
  unfold foldH; split_ifs <;> simp

/-- **The D3⁺ setup at `x ∈ [0, 1]`** (radius `1`, trivial conditioning data). -/
theorem palmC_setup {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) {Ω : Type} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] {X : Ω → FieldSample} (hX : IsFreeGFFModConstH X P)
    {x : ℝ}
    (hx : x ∈ Icc (0 : ℝ) 1) :
    D3Plus.Setup γ γ 1 (palmCRho (foldedCircle 0 3) x) P (palmCField X x) (fun _ : Ω => ())
      (fun _ => palmCCorr γ (foldedCircle 0 3) x) := by
  have hxn : ‖(x : ℂ)‖ ≤ 1 := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_le]; constructor <;> linarith [hx.1, hx.2]
  exact
    { hγ := hγ
      hγ2 := hγ2
      hα := gamma_lt_Qc' hγ hγ2
      hr := one_pos
      hX := isFreeGFFModConstH_translate hX x
      hΞ := measurable_const
      hind := by
        rw [MeasurableSpace.comap_const]
        exact indep_bot_left _
      hρ := isAdmissibleH_map_add_real
        (isAdmissibleH_foldedCircle (by simp [Hbar]) (by norm_num)) (-x)
      hρ1 := by rw [palmCRho, map_add_real_univ, measure_univ]
      hρB := by
        rw [palmCRho, Measure.map_apply (measurable_add_const _) measurableSet_ball]
        refine measure_mono_null (fun z hz => ?_)
          (LateralGerm.foldedCircle_ball_eq_zero (s := 3) (δ := 2) two_pos (by norm_num))
        simp only [mem_preimage, mem_ball, dist_zero_right] at hz ⊢
        calc ‖z‖ = ‖(z + ((-x : ℝ) : ℂ)) + (x : ℂ)‖ := by push_cast; ring_nf
          _ ≤ ‖z + ((-x : ℝ) : ℂ)‖ + ‖(x : ℂ)‖ := norm_add_le _ _
          _ < 2 := by linarith
      harm := fun _ z hz => by
        have hev : (fun w => palmCCorr γ (foldedCircle 0 3) x (foldH w)) =ᶠ[𝓝 z]
            fun _ => -(γ / 2) * (-2 * Real.log 3) -
              ∫ u, shiftFun γ (0 : ℂ → ℝ) (foldedCircle 0 3) x u ∂(foldedCircle 0 3) := by
          filter_upwards [isOpen_ball.mem_nhds hz] with w hw
          rw [mem_ball, dist_zero_right] at hw
          have h3 : ‖foldH w + (x : ℂ)‖ < 3 := by
            calc ‖foldH w + (x : ℂ)‖ ≤ ‖foldH w‖ + ‖(x : ℂ)‖ := norm_add_le _ _
              _ < 3 := by rw [palmC_norm_foldH]; linarith
          simp only [palmCCorr]
          rw [kPot_foldedCircle_three h3]
        exact (InnerProductSpace.harmonicAt_congr_nhds hev).2
          (InnerProductSpace.harmonicAt_const _)
      gmeas := fun _ => measurable_const }

/-- **Node C″ (identification of the fixed-point zoom with the D3⁺ model).** For every free
field `X` and every `x ∈ [0, 1]`: the zoom coordinates at `x` of the Palm-shifted field
`N_ϖ(X + (γ/2)(neumannH x · − kPot ϖ))` (`ϖ = foldedCircle 0 3`) are a.e.-measurable, and for
every `R` they agree inside `closedBall 0 R` with the D3⁺ model data of
`zoomModel γ γ C (palmCRho ϖ x) (palmCField X x ω) (palmCCorr γ ϖ x)` on `halfDisc 1`, except
on an event whose (outer) probability tends to `0` as `C → ∞`. -/
def Prop17PalmCAgreeStmt (γ : ℝ) : Prop :=
  ∀ (Ω' : Type) (_ : MeasurableSpace Ω') (P' : Measure Ω') (X : Ω' → FieldSample),
    IsProbabilityMeasure P' → IsFreeGFFModConstH X P' → ∀ x ∈ Icc (0 : ℝ) 1,
      (∀ C : ℝ, AEMeasurable (fun ω => palmZoomCoords γ C (foldedCircle 0 3) X (ω, x)) P') ∧
      ∀ R : ℕ, Tendsto (fun C : ℝ => P' {ω |
        locFull R (palmZoomCoords γ C (foldedCircle 0 3) X (ω, x)) ≠
          palmCModelData γ 1 C R (palmCRho (foldedCircle 0 3) x) (palmCField X x ω)
            (palmCCorr γ (foldedCircle 0 3) x)}) atTop (𝓝 0)

theorem prop17PalmCModel_of_agree {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2)
    (h : Prop17PalmCAgreeStmt γ) : Prop17PalmCModelStmt γ (foldedCircle 0 3) 0 1 := by
  intro Ω' _ P' X A hP' hX _ _ x hx
  obtain ⟨hm, ht⟩ := h Ω' _ P' X hP' hX x hx
  have := hP'
  exact ⟨1, _, _, _, palmC_setup hγ hγ2 hX hx, hm, ht⟩

/-- **Node C** from D3⁺(i) (rich form) and the identification node. -/
theorem prop17FreeFixedZoom_of_agree {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2)
    (hI : D3Plus.D3PlusIStmtRich) (h : Prop17PalmCAgreeStmt γ) :
    Prop17FreeFixedZoomStmt γ (foldedCircle 0 3) 0 1 :=
  prop17FreeFixedZoom_of_model hγ hγ2 hI (prop17PalmCModel_of_agree hγ hγ2 h)

end Raw
end FieldLaw
end S5
end QuantumZipper
