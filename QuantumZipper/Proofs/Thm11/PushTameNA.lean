import QuantumZipper.Proofs.Thm11.PushTameAS
import QuantumZipper.Proofs.GFF.ZeroRegBoundaryNA

/-!
# The pushforward test measures are tame without the log hypothesis

Corollary of RG-3a/RG-3b for `ZeroRegBoundaryNA`: for `κ ∈ (0,4]`, `T > 0` and
`ρ ∈ TestFun H`, almost surely, whenever the real barriers `±R` are not swallowed by time `T`,
`ν_T^± = pushTest (drive κ B ω) T (ρ^±)` satisfy `ZeroRegBdryNA.TameBdry` (bounded Green
potential, Frostman bound with `p = α = 2`, strip decay with `η = 1`, compact support). No
admissibility and no clock integrability (`hlog`) is needed, so `ZeroRegBdryNA.ae_tendsto_evalReg_NA`
and `ZeroRegBdryNA.integral_cexp_evalReg_NA` apply, also at `κ = 4`.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal

namespace QuantumZipper
namespace PushTameNA

open PushTame PushTameAS ZeroRegBdryNA

/-- **Deterministic tameness** of `ν_T` given the barriers and the strip decay. -/
theorem tameBdry_pushTest {W : ℝ → ℝ} (hW : Continuous W) (hW0 : W 0 = 0) {T : ℝ} (hT : 0 < T)
    {φ : ℂ → ℝ≥0∞} (hφ : Measurable φ) {c : ℝ≥0∞} (hc : c < ⊤) (hφc : ∀ z, φ z ≤ c)
    {K : Set ℂ} (hK : IsCompact K) (hKH : K ⊆ H) (hφK : ∀ z ∉ K, φ z = 0) {R : ℝ}
    (hR : 0 < R) (hKR : ∀ a ∈ K, |a.re| < R) (hp : ∃ v, IsForwardSol W (R : ℂ) T v)
    (hm : ∃ v, IsForwardSol W ((-R : ℝ) : ℂ) T v) {C η : ℝ} (hC : 0 ≤ C) (hη : 0 < η)
    (hS : ∀ t : ℝ, 1 ≤ t → pushTest W T φ {z | z.im < Real.exp (-Real.exp t)} ≤
      ENNReal.ofReal (C * t ^ (-(1 + η)))) :
    TameBdry (pushTest W T φ) := by
  obtain ⟨Rk, hRk⟩ := hK.isBounded.exists_norm_le
  have hbdd : Bornology.IsBounded (fwdMap W T '' (K ∩ (H \ fwdHull W T))) :=
    isBounded_fwdMap_image_of_barriers hW hT.le (by rw [hW0, abs_zero]; exact hR) hp hm
      (M := Rk) fun a ha => ⟨hKR a ha, (Complex.im_le_norm a).trans (hRk a ha)⟩
  obtain ⟨M, hM, hF⟩ := pushTest_ball_le hW hT.le hc hφc hK hφK
  exact ⟨isFiniteMeasure_pushTest hφ hc hφc hK hKH hφK,
    pushTest_support hW hT.le hK.isClosed hφK hbdd,
    pushTest_greenH_pot hW hW0 hT hφ hc hφc hK hKH hφK,
    ⟨M, 2, 2, hM, by norm_num, by norm_num, hF⟩, ⟨C, η, hC, hη, hS⟩⟩

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {B : ℝ≥0 → Ω → ℝ}

end PushTameNA
end QuantumZipper
