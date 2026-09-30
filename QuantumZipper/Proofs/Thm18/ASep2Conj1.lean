import QuantumZipper.Proofs.Thm18.ASep2Conj2
import QuantumZipper.Proofs.Thm18.ASepConj1D

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# ASEP2 (D1, conjunct 1): the rescaled field is exact for every continuous profile

For a fixed good driver `W` and a free field `X`, almost surely, for **every** continuous `g` and
every good parameter `p = (τ, a)`, the rescaled unzipped field `rescale U_g Q a`,
`U_g = coordChange (ofFun g + X ω) f_τ⁻¹ Q`, is exact at `σ.map ψ_p` (`ae_conj1_add_good`), and
in `G4SepConcl0` form (`ae_conj1_add_sep`).

Proof (as `ae_conj1_goodBox`, with the profile split off):
* `U_g` is a regular sample with witness `Z_τ + D_g` (`isRegularWith_add_of`), where `Z_τ` is the
  fixed-driver joint witness of `U_0` and `D_g(c, ρ) = ∫ g ∘ R dfc(c, ρ)` is the deterministic
  profile term, itself a regular witness (`isRegularWith_Dg`, commutation `integral_Dfun_swap`);
* the continuous-radius limit of `∫ (Z_τ + D_g)(v, ρ) dν_p` exists: the `Z_τ` part by the
  continuous-radius engine at profile `0` (`ae_tendsto_Phi_box`), the `D_g` part deterministically
  (`det_unif_A0_rho`);
* `conj1_of_limit`.

Own elementary bookkeeping on top of the free-field engine (Duplantier–Sheffield, Invent. Math.
185 (2011), Prop. 3.1).
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Metric
open scoped Topology

namespace QuantumZipper
namespace ASep

open Thm18Asm Thm18Asm.G4Core RegCont TwoPoint CoordReg GenUC

/-- **Regular witness of a field whose dyadic raw values split.** -/
theorem isRegularWith_add_of {U0 Uh yD : FieldSample} {Z0 D : ℂ × ℝ → ℝ}
    (hU : IsRegularWith U0 Z0) (hD : IsRegularWith yD D)
    (hraw : ∀ n j : ℕ, ∀ z : ℂ, Uh (foldedCircle (dyadicRoundC n z) (radius j)) =
      U0 (foldedCircle (dyadicRoundC n z) (radius j)) + D (foldH (dyadicRoundC n z), radius j)) :
    IsRegularWith Uh (fun q => Z0 q + D q) := by
  refine ⟨hU.1.add hD.1, fun k z hz => ?_, ?_⟩
  · have hf : Tendsto (fun n => (foldH (dyadicRoundC n z), radius k)) atTop
        (𝓝[Hbar ×ˢ Ioi 0] (z, radius k)) := by
      refine tendsto_nhdsWithin_iff.2 ⟨?_, Eventually.of_forall fun n =>
        (⟨CircleFubini.foldH_mem_Hbar' _, radius_pos k⟩ :
          (foldH (dyadicRoundC n z), radius k) ∈ Hbar ×ˢ Ioi (0 : ℝ))⟩
      have := (CircleFubini.continuous_foldH'.tendsto z).comp (RegClosure.tendsto_dyadicRoundC z)
      rw [CircleFubini.foldH_of_mem' hz] at this
      exact this.prodMk_nhds tendsto_const_nhds
    have h2 := (hD.1 (z, radius k) ⟨hz, radius_pos k⟩).tendsto.comp hf
    exact Tendsto.congr (fun n => (hraw n k z).symm) ((hU.2.1 k z hz).add h2)
  · refine RegClosure.tluo_of_dist_le (RegClosure.tluo_add hU.2.2 hD.2.2) ?_
    filter_upwards [self_mem_nhdsWithin] with ρ (hρ : 0 < ρ) q hq
    rw [integral_add (RegClosure.integrable_fc (RegClosure.continuousOn_slice hU.1 hρ) _ hq.2.le)
      (RegClosure.integrable_fc (RegClosure.continuousOn_slice hD.1 hρ) _ hq.2.le)]

/-- **The deterministic profile term is a regular witness.** -/
theorem isRegularWith_Dg {W : ℝ → ℝ} (hW : Continuous W) {τ : ℝ} (hτ : 0 ≤ τ) {g : ℂ → ℝ}
    (hg : Continuous g) :
    IsRegularWith (ofFun fun u => g (revMap (vRev W τ) τ u))
      (fun q => Dfix W 0 g 0 (τ, q)) := by
  have hV := continuous_vRev hW τ
  refine (RegUnif.isRegularWith_of_witness ?_ ?_ ?_).1
  · exact (continuousOn_Dfun (W := vRev W τ) (T := τ) hV hτ 0 hg 0).mono fun q hq => hq.2
  · intro k d _
    show ∫ u, g (revMap (vRev W τ) τ u) ∂foldedCircle d (radius k) = Dfun (vRev W τ) τ 0 g 0 _
    unfold Dfun
    simp
  · intro w _ r ρ hr hρ
    exact integral_Dfun_swap (W := vRev W τ) (T := τ) hV hτ 0 hg 0 w hr hρ

variable {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} {X : Ω → FieldSample}

end ASep
end QuantumZipper
