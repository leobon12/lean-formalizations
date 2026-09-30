import QuantumZipper.Proofs.Zipper.CfgFMDefs
import QuantumZipper.Proofs.Thm18.G1FM2Final

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# CFG-FM-VAR (0): definitions for the time-indexed first-mode variance chain

The unzipping maps `ψ_t = f_t⁻¹` of a continuous driver `W` with `W 0 = 0`, in the globally
measurable form `tpsi W t = revMap (vRev W t) t` (equal to `fwdMapInv W t` on `ℍ`,
`UnzipInvariance.fwdMapInv_eq_revMap_timeRev`), and the time analogues of
`Thm18Asm.PushPotLip` and `Thm18Asm.G1FMEnergyStmt` (scale `S = 1`, the time `t ∈ [0,T]` in
place of the scale). Bookkeeping only.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Metric
open scoped Topology NNReal

namespace QuantumZipper.E6
namespace CfgFM

/-- The unzipping map `ψ_t`, globally measurable version. -/
def tpsi (W : ℝ → ℝ) (t : ℝ) : ℂ → ℂ := revMap (RegCont.vRev W t) t

theorem tpsi_eq {W : ℝ → ℝ} (hW : Continuous W) (hW0 : W 0 = 0) {t : ℝ} (ht : 0 ≤ t) {w : ℂ}
    (hw : w ∈ H) : tpsi W t w = fwdMapInv W t w :=
  (UnzipInvariance.fwdMapInv_eq_revMap_timeRev W hW hW0 ht hw).symm

theorem tpsi_eqOn {W : ℝ → ℝ} (hW : Continuous W) (hW0 : W 0 = 0) {t : ℝ} (ht : 0 ≤ t) :
    EqOn (tpsi W t) (fwdMapInv W t) H := fun _ hw => tpsi_eq hW hW0 ht hw

/-- `ψ_t` is a good map in the sense of `G1RC.PsiGood`. -/
theorem tpsi_psiGood {W : ℝ → ℝ} (hW : Continuous W) (hW0 : W 0 = 0) {t : ℝ} (ht : 0 ≤ t) :
    Thm18Asm.G1RC.PsiGood (tpsi W t) := by
  have hd := RS.differentiableOn_fwdMapInv hW hW0 ht
  have hinj := RS.injOn_fwdMapInv hW hW0 ht
  have he := tpsi_eqOn hW hW0 ht
  refine ⟨TwoPoint.measurable_revMap (RegCont.continuous_vRev hW t) ht, hd.congr he,
    fun a ha b hb hab => hinj ha hb (by rw [← he ha, ← he hb]; exact hab),
    fun z hz => by rw [he hz]; exact RS.fwdMapInv_mem_H hW hW0 ht hz, fun R => ?_⟩
  obtain ⟨M, hM⟩ := RegCont.exists_abs_le_on_Icc hW t
  refine ⟨RegCont.revBound (2 * M) t R, fun z hz hzR => ?_⟩
  rw [he hz]
  exact (RegCont.fwdMapInv_mem_H_bound hW hW0 hM ht le_rfl hz hzR).2

/-- Pushed first-mode measure of `ψ_t` (scale `1`). -/
abbrev tfm (W : ℝ → ℝ) (t : ℝ) (w v : ℂ) (s : ℝ) : Measure ℂ :=
  Thm18Asm.pfmMeas (tpsi W t) 1 w v s

/-- Uniform (in `t ∈ [0,T]`) local bounds and Lipschitz bound of the pushed potentials:
the time analogue of `Thm18Asm.PushPotLip`. -/
def TPushPotLip (W : ℝ → ℝ) (T : ℝ) : Prop :=
  ∀ m : ℕ, ∃ M₀ M₁ rD L ρ₁ τ₁ : ℝ, 0 ≤ M₀ ∧ 0 ≤ M₁ ∧ 0 < rD ∧ 0 ≤ L ∧ 0 < ρ₁ ∧ 0 < τ₁ ∧
    2 * τ₁ ≤ rD ∧ ∀ w : ℂ, ‖w‖ ≤ 2 * ((m : ℝ) + 1) → 1 / ((m : ℝ) + 1) ≤ w.im →
      rD < w.im ∧ ∀ t ∈ Icc (0 : ℝ) T, (∀ x ∈ closedBall w rD, ‖tpsi W t x‖ ≤ M₀) ∧
      (∀ x ∈ closedBall w rD, ∀ x' ∈ closedBall w rD,
        ‖tpsi W t x - tpsi W t x'‖ ≤ M₁ * ‖x - x'‖) ∧
      ∀ u : ℂ, ‖u‖ = 1 → ∀ τ s : ℝ, 0 < τ → τ ≤ τ₁ → 0 ≤ s → s ≤ τ →
        ∀ p ∈ ball (tpsi W t w) ρ₁, ∀ p' ∈ ball (tpsi W t w) ρ₁,
          |Thm18Asm.pushPot (tpsi W t) 1 w ((τ : ℂ) * u) s p -
            Thm18Asm.pushPot (tpsi W t) 1 w ((τ : ℂ) * u) s p'| ≤ L / τ * ‖p - p'‖

/-- Hölder-`1/3` displacement of `ψ_t` in time, uniformly on the regions of level `m`. -/
def TDisp (W : ℝ → ℝ) (T : ℝ) : Prop :=
  ∀ m : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ t ∈ Icc (0 : ℝ) T, ∀ t' ∈ Icc (0 : ℝ) T, ∀ x : ℂ,
    ‖x‖ ≤ 2 * ((m : ℝ) + 1) + 1 → 1 / (2 * ((m : ℝ) + 1)) ≤ x.im →
      ‖tpsi W t x - tpsi W t' x‖ ≤ C * |t - t'| ^ ((1 : ℝ) / 3)

/-- Energy node in time (time analogue of `Thm18Asm.G1FMEnergyStmt`). -/
def TEnergy (W : ℝ → ℝ) (T : ℝ) : Prop :=
  ∀ m : ℕ, ∃ c : ℝ, 0 ≤ c ∧ ∃ τ₀ : ℝ, 0 < τ₀ ∧
    ∀ u : ℂ, ‖u‖ = 1 → ∀ w w' : ℂ, ‖w‖ ≤ 2 * ((m : ℝ) + 1) → ‖w'‖ ≤ 2 * ((m : ℝ) + 1) →
      1 / ((m : ℝ) + 1) ≤ w.im → 1 / ((m : ℝ) + 1) ≤ w'.im →
      ∀ τ τ' : ℝ, 0 < τ → τ ≤ τ₀ → τ ≤ 2 * τ' → τ' ≤ 2 * τ →
      ∀ s s' : ℝ, 0 ≤ s → s ≤ τ → 0 ≤ s' → s' ≤ τ' →
      ∀ t ∈ Icc (0 : ℝ) T, ∀ t' ∈ Icc (0 : ℝ) T,
        kernelCov2 neumannH (tfm W t w ((τ : ℂ) * u) s, tfm W t w (-((τ : ℂ) * u)) s)
            (tfm W t w ((τ : ℂ) * u) s, tfm W t w (-((τ : ℂ) * u)) s) ≤ c ∧
        kernelCov2 neumannH
            (tfm W t w ((τ : ℂ) * u) s + tfm W t' w' (-((τ' : ℂ) * u)) s',
              tfm W t w (-((τ : ℂ) * u)) s + tfm W t' w' ((τ' : ℂ) * u) s')
            (tfm W t w ((τ : ℂ) * u) s + tfm W t' w' (-((τ' : ℂ) * u)) s',
              tfm W t w (-((τ : ℂ) * u)) s + tfm W t' w' ((τ' : ℂ) * u) s') ≤
          c * (‖w - w'‖ + |τ - τ'| + |s - s'| + |t - t'| ^ ((1 : ℝ) / 3)) / τ

end CfgFM
end QuantumZipper.E6
