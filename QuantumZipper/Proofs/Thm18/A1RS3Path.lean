import QuantumZipper.Proofs.Thm18.A1RS3Pos

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# A1RS3 (5): the rational Cauchy estimate for the rescaled field (pathwise)

**`ratCauchy_y_of_Z`**: for one sample, if the unscaled field `Z = X + α₀(−log|·|) + G` with the
driver `V` satisfies the rational Cauchy estimate, `y` has the regularized averages of
`rescale Z Q b`, its driver is `W = V(b² ·)/b`, its pairings against the members `ν_{p,0}` are
continuous (R3) and have continuum limits along continuous radii (`F1.ContData`), then `y` with
`W` satisfies the rational Cauchy estimate. The identity
`Φ_y(ρ, p) = Φ_Z(bρ, T p) + Q log b` (`T p = (b² t, μ⁻¹ d, μ⁻¹ s)`) holds for `ρ > 0`
(`evalReg_smear_rescale_pos`) and `ρ = 0` (`evalReg_sidePush_rescale`), and
`ratCauchy_of_rescale` applies (with (R2) for `Z`, `continuousOn_evalReg_smearFam_Z`).
Own elementary bookkeeping.
-/

noncomputable section

open MeasureTheory Set Filter Metric
open scoped Topology

namespace QuantumZipper
namespace R18
namespace A1RS

open Thm18Asm F1 B3d.ZipLen

variable {κ : ℝ} {X Z : FieldSample} {FX : ℂ × ℝ → ℝ} {G : ℂ → ℝ} {V : ℝ → ℝ}

/-- The parameter rescaling `T p = (c₀ t, c₁ Re d, c₁ Im d, c₁ s)`. -/
def parScale (c : Fin 4 → ℝ) (p : Fin 4 → ℝ) : Fin 4 → ℝ := fun i => c i * p i

theorem continuous_parScale (c : Fin 4 → ℝ) : Continuous (parScale c) :=
  continuous_pi fun i => continuous_const.mul (continuous_apply i)

theorem parScale_mapsTo {c : Fin 4 → ℝ} (h0 : 0 < c 0) (h3 : 0 < c 3) :
    MapsTo (parScale c) smearU smearU := fun _ hp =>
  ⟨mul_pos h0 hp.1, mul_pos h3 hp.2⟩

theorem parScale_inv {c : Fin 4 → ℝ} (hc : ∀ i, c i ≠ 0) (p : Fin 4 → ℝ) :
    parScale c (parScale (fun i => (c i)⁻¹) p) = p := by
  funext i
  simp only [parScale]
  rw [← mul_assoc, mul_inv_cancel₀ (hc i), one_mul]

theorem parScale_parScale (c c' : Fin 4 → ℝ) (p : Fin 4 → ℝ) :
    parScale c (parScale c' p) = parScale (fun i => c i * c' i) p := by
  funext i
  simp only [parScale]
  ring

/-- **The rational Cauchy estimate for the rescaled field.** The estimate for `Z` may be given in
any positively rescaled parametrization `p ↦ ν_{parScale e p, ρ}`. -/
theorem ratCauchy_y_of_Z (hκ : 0 < κ) (hFX : IsRegularWith X FX) (hGc : Continuous G)
    (hZfc : ∀ d ∈ Hbar, ∀ r : ℝ, 0 < r →
      Z (foldedCircle d r) = (X + F2.logSingField κ + ofFun G) (foldedCircle d r))
    (hGV : G1zDrvGood V)
    (hfy : ∀ i : ℕ, evalReg (ofFun (h0rev κ) + X)
        (foldedCircle (CoordsFull.fullIndex i).1 (CoordsFull.fullIndex i).2) =
      (ofFun (h0rev κ) + X) (foldedCircle (CoordsFull.fullIndex i).1
        (CoordsFull.fullIndex i).2))
    (hS1 : ∀ m : ℕ, ∃ L : ℝ × ℝ × ℂ × ℝ → ℝ,
      TendstoUniformlyOn (fun ρ p => flowPhiYc κ X V ρ p) L (𝓝[>] 0) (flowBox m))
    {Q b : ℝ} (hb : 0 < b) {y : FieldSample} (hy : avgReg y = avgReg (rescale Z Q b))
    {Fy : ℂ × ℝ → ℝ} (hyF : IsRegularWith y Fy)
    (hGW : G1zDrvGood fun r => V (b ^ 2 * r) / b)
    (hUCy : ∀ t : ℝ, 0 < t → ∀ ρ : ℝ, 0 < ρ → ∀ R : ℝ,
      TendstoUniformlyOn (fun (k : ℕ) (z : ℂ) => ∫ u, avgReg y k u
          ∂((foldedCircle z ρ).map (fwdMapInv (fun r => V (b ^ 2 * r) / b) t)))
        (fun z => evalReg y ((foldedCircle z ρ).map (fwdMapInv (fun r => V (b ^ 2 * r) / b) t)))
        atTop (Hbar ∩ closedBall 0 R))
    (hex : ∀ t : ℝ, 0 ≤ t → ∃ p : ℂ,
      Tendsto (fun y : ℝ => fwdMapInv V t (y * Complex.I)) (𝓝[>] 0) (𝓝 p)) (left : Bool)
    (hCD : ∀ (d : ℂ) (s : ℝ), 0 < s →
      ContData y ((foldedCircle d s).map (g1zSideMap left fun r => V (b ^ 2 * r) / b)))
    (hR3 : ContinuousOn (fun p => evalReg y (smearFam (fun r => V (b ^ 2 * r) / b) left p 0))
      smearU)
    {e : Fin 4 → ℝ} (he : ∀ i, 0 < e i)
    (hCZ : ∀ a c : Fin 4 → ℚ, GenUC.ratBox a c ⊆ smearU → ∀ n : ℕ, ∃ N : ℕ, ∀ r : ℚ, 0 < r →
      (r : ℝ) < 1 / ((N : ℝ) + 1) → ∀ q : Fin 4 → ℚ, ratPt q ∈ GenUC.ratBox a c →
        |evalReg Z (smearFam V left (parScale e (ratPt q)) r) -
          evalReg Z (smearFam V left (parScale e (ratPt q)) 0)| < 1 / ((n : ℝ) + 1)) :
    ∀ a c : Fin 4 → ℚ, GenUC.ratBox a c ⊆ smearU → ∀ n : ℕ, ∃ N : ℕ, ∀ r : ℚ, 0 < r →
      (r : ℝ) < 1 / ((N : ℝ) + 1) → ∀ q : Fin 4 → ℚ, ratPt q ∈ GenUC.ratBox a c →
        |evalReg y (smearFam (fun r => V (b ^ 2 * r) / b) left (ratPt q) r) -
          evalReg y (smearFam (fun r => V (b ^ 2 * r) / b) left (ratPt q) 0)| <
            1 / ((n : ℝ) + 1) := by
  obtain ⟨μ, hμ, hψ⟩ := sideMap_scale hGV hb hGW hex left
  set c : Fin 4 → ℝ := ![b ^ 2, μ⁻¹, μ⁻¹, μ⁻¹] with hcdef
  have hc0 : c 0 = b ^ 2 := rfl
  have hc1 : c 1 = μ⁻¹ := rfl
  have hc2 : c 2 = μ⁻¹ := rfl
  have hc3 : c 3 = μ⁻¹ := rfl
  have hcne : ∀ i, c i ≠ 0 := by
    intro i
    fin_cases i
    · exact (pow_pos hb 2).ne'
    all_goals exact (inv_pos.2 hμ).ne'
  have hcpos0 : 0 < c 0 := by rw [hc0]; positivity
  have hcpos3 : 0 < c 3 := by rw [hc3]; exact inv_pos.2 hμ
  set ci : Fin 4 → ℝ := fun i => (c i)⁻¹ with hci
  have hZreg : IsRegularSample Z := ⟨_, isRegularWith_Z (κ := κ) hFX hGc hZfc⟩
  have hparD : ∀ p : Fin 4 → ℝ, parD (parScale c p) = ((μ⁻¹ : ℝ) : ℂ) * parD p := by
    intro p
    apply Complex.ext <;> simp [parD, parScale, hc1, hc2]
  have hid : ∀ ρ : ℝ, 0 ≤ ρ → ∀ p ∈ smearU,
      evalReg y (smearFam (fun r => V (b ^ 2 * r) / b) left p ρ) =
        evalReg Z (smearFam V left (parScale c p) (b * ρ)) + Q * Real.log b := by
    intro ρ hρ p hp
    have hTp : parScale c p ∈ smearU := parScale_mapsTo hcpos0 hcpos3 hp
    rcases hρ.lt_or_eq with hρ | hρ
    · have h := evalReg_smear_rescale_pos hκ hFX hGc hZfc hGV hfy hS1 hb hy hyF hGW hUCy hμ hψ
        hp.1 (parD p) hp.2 hρ
      have e : smearFam V left (parScale c p) (b * ρ) =
          a1rfNu V (b ^ 2 * p 0) left (((μ⁻¹ : ℝ) : ℂ) * parD p) (μ⁻¹ * p 3) (b * ρ) := by
        simp only [smearFam, hparD]
        rfl
      rw [e]
      exact h
    · subst hρ
      rw [mul_zero, smearFam_zero_eq hGW left hp, smearFam_zero_eq hGV left hTp, hparD]
      exact evalReg_sidePush_rescale hZreg hb hy hGV hGW hμ hψ (parD p) hp.2
        (hCD (parD p) (p 3) hp.2)
  have hcpos : ∀ i, 0 < c i := by
    intro i
    fin_cases i
    · show 0 < b ^ 2; positivity
    all_goals exact inv_pos.2 hμ
  obtain ⟨c', hc'def⟩ : ∃ c' : Fin 4 → ℝ, c' = fun i => (e i)⁻¹ * c i := ⟨_, rfl⟩
  have hc'pos : ∀ i, 0 < c' i := by
    intro i
    rw [hc'def]
    exact mul_pos (inv_pos.2 (he i)) (hcpos i)
  have hec' : ∀ p, parScale e (parScale c' p) = parScale c p := by
    intro p
    rw [parScale_parScale]
    congr 1
    funext i
    rw [hc'def, ← mul_assoc, mul_inv_cancel₀ (he i).ne', one_mul]
  have heU : MapsTo (parScale e) smearU smearU := parScale_mapsTo (he 0) (he 3)
  refine ratCauchy_of_rescale (ΦZ := fun ρ p => evalReg Z (smearFam V left (parScale e p) ρ))
    (Φy := fun ρ p => evalReg y (smearFam (fun r => V (b ^ 2 * r) / b) left p ρ))
    (T := parScale c') (S := parScale fun i => (c' i)⁻¹) (K := Q * Real.log b) hb (continuous_parScale c')
    (parScale_mapsTo (hc'pos 0) (hc'pos 3)) (continuous_parScale _).continuousOn
    (parScale_mapsTo (inv_pos.2 (hc'pos 0)) (inv_pos.2 (hc'pos 3)))
    (fun p _ => parScale_inv (fun i => (hc'pos i).ne') p) hCZ ?_ hR3 ?_
  · have h := continuousOn_evalReg_smearFam_Z hκ hFX hGc hZfc hGV.1 hGV.2.1 hfy hS1 hGV left
    have hf : Continuous fun z : (Fin 4 → ℝ) × ℝ => (parScale e z.1, z.2) :=
      ((continuous_parScale e).comp continuous_fst).prodMk continuous_snd
    have hmt : MapsTo (fun z : (Fin 4 → ℝ) × ℝ => (parScale e z.1, z.2)) (smearU ×ˢ Ioi 0)
        (smearU ×ˢ Ioi 0) := fun z hz => ⟨heU hz.1, hz.2⟩
    have h2 := h.comp hf.continuousOn hmt
    show ContinuousOn (fun z : (Fin 4 → ℝ) × ℝ => evalReg Z (smearFam V left (parScale e z.1) z.2))
      (smearU ×ˢ Ioi 0)
    exact h2.congr fun z _ => rfl
  · intro ρ hρ p hp
    show evalReg y (smearFam (fun r => V (b ^ 2 * r) / b) left p ρ) =
      evalReg Z (smearFam V left (parScale e (parScale c' p)) (b * ρ)) + Q * Real.log b
    rw [hec', hid ρ hρ p hp]

end A1RS
end R18
end QuantumZipper
