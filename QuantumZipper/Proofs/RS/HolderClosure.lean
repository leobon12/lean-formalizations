import QuantumZipper.Proofs.RS.HolderBox
import QuantumZipper.Blueprint.External3

/-!
# RS RH3′: `Blueprint.RevMapHolder` (Option B)

Blueprint `blueprint/EXT_RS_BLUEPRINT.md`, §5, node RH3′; DECISIONS D6.

## Main statements

* `RS.holder_box_of_holder_H` (deterministic): if `F = f` on `H`, `F` is continuous on `Hbar`,
  and `f` obeys `‖f z − f w‖ ≤ C ‖z − w‖^α` on `H ∩ closedBall 0 (2R+1)`, then `F` obeys the same
  bound on the closed box `[-R,R] × [0,R]`.
* `RS.revMapHolder : Blueprint.RevMapHolder`.

## Proof

RH2 (`ae_revMap_holder`) on `H ∩ closedBall 0 (2R+1)`, then pass to the closed box by
continuity of the Carathéodory extension: for `z, w` in the box and `0 < ε < 1`, the points
`z + iε, w + iε` lie in `H ∩ closedBall 0 (2R+1)` and have the same difference `z − w`; let
`ε → 0⁺`. This is the extension-by-continuity step of RS Thm 5.2 (p. 21), where the Hölder bound
is stated on bounded subsets of `ℍ`; the passage to the closure is our own elementary argument
(own elementary proof).
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set Complex
open scoped ENNReal NNReal

namespace QuantumZipper
namespace RS

/-- Vertical approach from above stays in `Hbar` and tends to the base point. -/
theorem tendsto_add_mul_I_nhdsWithin_Hbar {z : ℂ} (hz : z ∈ Hbar) :
    Tendsto (fun ε : ℝ => z + (ε : ℂ) * I) (𝓝[>] 0) (𝓝[Hbar] z) := by
  refine tendsto_nhdsWithin_iff.2 ⟨?_, ?_⟩
  · have hc : Continuous fun ε : ℝ => z + (ε : ℂ) * I := by fun_prop
    have := hc.tendsto 0
    simp only [ofReal_zero, zero_mul, add_zero] at this
    exact this.mono_left nhdsWithin_le_nhds
  · filter_upwards [self_mem_nhdsWithin] with ε hε
    show 0 ≤ (z + (ε : ℂ) * I).im
    have hz' : 0 ≤ z.im := hz
    have : (0 : ℝ) < ε := hε
    simp only [add_im, mul_im, ofReal_re, I_im, ofReal_im, I_re, mul_zero, add_zero, mul_one]
    linarith

/-- **RH3′, deterministic part.** A Hölder bound for `f` on `H ∩ closedBall 0 (2R+1)` passes to
any continuous extension `F` on the closed box `[-R,R] × [0,R]` (own elementary proof). -/
theorem holder_box_of_holder_H {f F : ℂ → ℂ} (hEq : EqOn F f H) (hFc : ContinuousOn F Hbar)
    {α C R : ℝ}
    (hhol : ∀ z ∈ H, ∀ w ∈ H, ‖z‖ ≤ 2 * R + 1 → ‖w‖ ≤ 2 * R + 1 →
      ‖f z - f w‖ ≤ C * ‖z - w‖ ^ α) :
    ∀ z ∈ Icc (-R) R ×ℂ Icc 0 R, ∀ w ∈ Icc (-R) R ×ℂ Icc 0 R,
      ‖F z - F w‖ ≤ C * ‖z - w‖ ^ α := by
  intro z hz w hw
  rw [mem_reProdIm] at hz hw
  have hzH : z ∈ Hbar := hz.2.1
  have hwH : w ∈ Hbar := hw.2.1
  have hnorm : ∀ p : ℂ, p.re ∈ Icc (-R) R → p.im ∈ Icc 0 R → ∀ ε : ℝ, 0 < ε → ε < 1 →
      p + (ε : ℂ) * I ∈ H ∧ ‖p + (ε : ℂ) * I‖ ≤ 2 * R + 1 := by
    intro p hre him ε hε hε1
    have him' : (p + (ε : ℂ) * I).im = p.im + ε := by simp
    refine ⟨show 0 < (p + (ε : ℂ) * I).im by rw [him']; linarith [him.1], ?_⟩
    have h1 : ‖p‖ ≤ |p.re| + |p.im| := norm_le_abs_re_add_abs_im p
    have h2 : ‖(ε : ℂ) * I‖ = ε := by simp [abs_of_pos hε]
    have h3 : |p.re| ≤ R := abs_le.2 ⟨hre.1, hre.2⟩
    have h4 : |p.im| ≤ R := by rw [abs_of_nonneg him.1]; exact him.2
    calc ‖p + (ε : ℂ) * I‖ ≤ ‖p‖ + ‖(ε : ℂ) * I‖ := norm_add_le _ _
      _ ≤ 2 * R + 1 := by rw [h2]; linarith
  have hlim : Tendsto (fun ε : ℝ => ‖F (z + (ε : ℂ) * I) - F (w + (ε : ℂ) * I)‖) (𝓝[>] 0)
      (𝓝 ‖F z - F w‖) :=
    (((hFc z hzH).tendsto.comp (tendsto_add_mul_I_nhdsWithin_Hbar hzH)).sub
      ((hFc w hwH).tendsto.comp (tendsto_add_mul_I_nhdsWithin_Hbar hwH))).norm
  refine le_of_tendsto hlim ?_
  filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < 1 by norm_num)] with ε hε
  obtain ⟨hzε, hzn⟩ := hnorm z hz.1 hz.2 ε hε.1 hε.2
  obtain ⟨hwε, hwn⟩ := hnorm w hw.1 hw.2 ε hε.1 hε.2
  rw [hEq hzε, hEq hwε]
  have := hhol _ hzε _ hwε hzn hwn
  rwa [show z + (ε : ℂ) * I - (w + (ε : ℂ) * I) = z - w by ring] at this

/-- **RH3′: `Blueprint.RevMapHolder`** (DECISIONS D6; RS Thm 5.2, p. 21, *reformulated* for the
reverse map, closed boxes and an ω-dependent exponent — entry L-RMH, not the literal text; via
RH2). -/
theorem revMapHolder : Blueprint.RevMapHolder := by
  intro κ hκ hκ4 T hT Ω _ P _ B hB
  obtain ⟨α, hα, h⟩ := ae_revMap_holder hB hκ hκ4 hT
  filter_upwards [h] with ω hω
  intro F hF R _
  obtain ⟨C, hC⟩ := hω (2 * R + 1)
  exact ⟨α, C, hα, holder_box_of_holder_H hF.1 hF.2.1 hC⟩

end RS
end QuantumZipper
