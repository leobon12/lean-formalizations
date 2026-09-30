import QuantumZipper.Proofs.Zipper.SWCoreB8FMain
import QuantumZipper.Proofs.Zipper.SWCoreB8FComp
import QuantumZipper.Proofs.Zipper.SWCoreA9Main
import QuantumZipper.Proofs.Zipper.Cor15RezipRegGood

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# SWC-B8F (7): identification of the offset integrals of `h⁰` with the pair integrals

* `offset_ident` (deterministic): for `y₀` regular with `RegEq y₀ (coordChange x₀ ψ Q)`, `ψ`
  conformal on `ℍ`, and the exactness of `coordChange x₀ ψ Q` on the dilated dyadic circles, the
  offset approximation of `y₀` at `c 2^{-k}` is the dyadic approximation of
  `coordChange x₀ (ψ ∘ (c ·)) Q` tested against `g(c ·)` (`integral_bdryR_offset_eq_bdryApprox`,
  `RegEq`-invariance of `rescale`, `bdryApprox_comp_mul_eq`).
* **`ident_off_of_pair`**: for a pair `(B', Y')` (Brownian, free, independent) whose unzipped
  fields represent `h⁰_{q+σ}` up to `RegEq` at rational `σ`, a.s. the offset integrals `awIntOff`
  at rational times and offsets are the pair integrals `pairJc`. The exactness on the countably
  many dilated circles comes from the jointly continuous regular witness of the pair's unzipped
  fields (`RegUnif.jointModStmt_holds`, `a9_ae_regular_Zh`), which agrees with the raw values at
  fixed parameters. This answers the orchestrator's warning (non-dyadic radii after dilation):
  the regularity is used at the rational offsets only, and `acfam_off_of_pair` passes to all
  offsets by continuity.

Own bookkeeping.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal ENNReal

namespace QuantumZipper
namespace SWCore

open CharFun B2 B5 RevMapExtension RegUnif

theorem rescale_congr_regEq {x y : FieldSample} (h : RegEq x y) (Q c : ℝ) :
    rescale x Q c = rescale y Q c := by
  unfold rescale
  exact coordChange_congr_regEq h _ Q

/-- **Deterministic identification.** -/
theorem offset_ident {γ : ℝ} (hγ : 0 < γ) {y₀ x₀ : FieldSample} {G : ℂ × ℝ → ℝ}
    (hG : IsRegularWith y₀ G) {ψ : ℂ → ℂ} (hR : RegEq y₀ (coordChange x₀ ψ (Qc γ)))
    (hψd : DifferentiableOn ℂ ψ H) (hψ0 : ∀ w ∈ H, deriv ψ w ≠ 0) (hψm : Measurable ψ)
    (hψi : InjOn ψ H) {c : ℝ} (hc : 0 < c) (k : ℕ)
    (hexact : ∀ t : ℝ, ∀ n : ℕ,
      evalReg (coordChange x₀ ψ (Qc γ))
          (foldedCircle ((c : ℂ) * dyadicRoundC n (t : ℂ)) (c * radius k)) =
        coordChange x₀ ψ (Qc γ) (foldedCircle ((c : ℂ) * dyadicRoundC n (t : ℂ)) (c * radius k)))
    (g : ℝ → ℝ) :
    ∫ t, g t ∂bdryR γ y₀ (c * radius k) =
      ∫ u, g (c * u) ∂bdryApprox γ (coordChange x₀ (fun w => ψ ((c : ℂ) * w)) (Qc γ)) k := by
  rw [integral_bdryR_offset_eq_bdryApprox hγ hG hc k g, rescale_congr_regEq hR,
    bdryApprox_comp_mul_eq γ x₀ (Qc γ) hψd hψ0 hψm hc k
      (fun t n => Thm18Asm.G1.integrable_log_norm_deriv_foldedCircle_of_injOn hψd hψi _
        (mul_pos hc (radius_pos k))) hexact]

variable {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]

theorem dyadicRoundC_real_mem_Dy (n : ℕ) (t : ℝ) : dyadicRoundC n (t : ℂ) ∈ Dy := by
  have hH : dyadicRoundC n (t : ℂ) ∈ Hbar :=
    CircleCont.dyadicRoundC_mem_Hbar (by simp [Hbar]) n
  refine mem_iUnion.2 ⟨n, (t : ℂ), ?_⟩
  exact CircleFubini.foldH_of_mem' hH

theorem mul_mem_Hbar_of_pos {c : ℝ} (hc : 0 < c) {w : ℂ} (hw : w ∈ Hbar) : (c : ℂ) * w ∈ Hbar := by
  show (0 : ℝ) ≤ ((c : ℂ) * w).im
  rw [Complex.im_ofReal_mul]
  exact mul_nonneg hc.le hw

set_option maxHeartbeats 1000000 in
/-- **Identification of the offset integrals with a pair.** -/
theorem ident_off_of_pair {κ : ℝ} {B : ℝ≥0 → Ω → ℝ} {X : Ω → FieldSample}
    (hB : IsBrownianReal B P) (hX : IsFreeGFFModConstH X P) (hind : IndepFun (pathOf B) X P)
    {T : ℝ} {q : ℚ} (hq : (0 : ℝ) ≤ q) (hqT : (q : ℝ) < T) (hκ : 0 < κ)
    {B' : ℝ≥0 → Ω → ℝ} {Y' : Ω → FieldSample} (hB' : IsBrownianReal B' P)
    (hY' : IsFreeGFFModConstH Y' P) (hind' : IndepFun (pathOf B') Y' P)
    (hRE : ∀ᵐ ω ∂P, ∀ σ : ℚ, (σ : ℝ) ∈ Icc (0 : ℝ) (T - q) →
      RegEq (h0f κ ((q : ℝ) + σ) B X ω) (coordChange (ofFun (h0rev κ) + Y' ω)
        (revMap (vrev (drive κ B' ω) σ) σ) (Qc (Real.sqrt κ))))
    (hwin : ∀ᵐ ω ∂P, ∀ σ : ℚ, (σ : ℝ) ∈ Icc (0 : ℝ) (T - q) →
      realRevMap (Vr κ T B ω) (T - ((q : ℝ) + σ)) =
        realRevMap (vrev (drive κ B' ω) (T - q)) (T - q - σ))
    (u v : ℝ) (f : ℝ → ℝ) :
    ∀ᵐ ω ∂P, ∀ σ : ℚ, (σ : ℝ) ∈ Icc (0 : ℝ) (T - q) → ∀ e : ℚ, (e : ℝ) ∈ Icc (1 : ℝ) 2 →
      ∀ k : ℕ, awIntOff κ T B X ω u v f ((q : ℝ) + σ) (k, e) =
        pairJc κ (T - q) B' Y' ω u v f σ e k := by
  have hT : 0 < T := lt_of_le_of_lt hq hqT
  have hTq : 0 < T - q := by linarith
  have hγ : 0 < Real.sqrt κ := Real.sqrt_pos.2 hκ
  obtain ⟨Zh, hZc, hZmod, hZcomm⟩ := jointModStmt_holds κ (Real.sqrt κ) hB' hY' hind' hTq
  have hZreg := a9_ae_regular_Zh hB' hY' hind' hTq hZc hZmod hZcomm
  have hZraw : ∀ᵐ ω ∂P, ∀ σ : ℚ, (σ : ℝ) ∈ Icc (0 : ℝ) (T - q) → ∀ e : ℚ,
      (e : ℝ) ∈ Icc (1 : ℝ) 2 → ∀ k : ℕ, ∀ d ∈ Dy,
        Zh ((σ : ℝ), (((e : ℝ) : ℂ) * d, (e : ℝ) * radius k)) ω =
          unzippedField (Real.sqrt κ) (ofFun (h0rev κ) + Y' ω, drive κ B' ω) σ
            (foldedCircle (((e : ℝ) : ℂ) * d) ((e : ℝ) * radius k)) := by
    refine ae_all_iff.2 fun σ => ?_
    by_cases hσ : (σ : ℝ) ∈ Icc (0 : ℝ) (T - q)
    swap
    · exact ae_of_all _ fun ω h => absurd h hσ
    suffices h : ∀ᵐ ω ∂P, ∀ e : ℚ, (e : ℝ) ∈ Icc (1 : ℝ) 2 → ∀ k : ℕ, ∀ d ∈ Dy,
        Zh ((σ : ℝ), (((e : ℝ) : ℂ) * d, (e : ℝ) * radius k)) ω =
          unzippedField (Real.sqrt κ) (ofFun (h0rev κ) + Y' ω, drive κ B' ω) σ
            (foldedCircle (((e : ℝ) : ℂ) * d) ((e : ℝ) * radius k)) from
      h.mono fun ω h _ => h
    refine ae_all_iff.2 fun e => ?_
    by_cases he : (e : ℝ) ∈ Icc (1 : ℝ) 2
    swap
    · exact ae_of_all _ fun ω h => absurd h he
    suffices h : ∀ᵐ ω ∂P, ∀ k : ℕ, ∀ d ∈ Dy,
        Zh ((σ : ℝ), (((e : ℝ) : ℂ) * d, (e : ℝ) * radius k)) ω =
          unzippedField (Real.sqrt κ) (ofFun (h0rev κ) + Y' ω, drive κ B' ω) σ
            (foldedCircle (((e : ℝ) : ℂ) * d) ((e : ℝ) * radius k)) from
      h.mono fun ω h _ => h
    refine ae_all_iff.2 fun k => ?_
    have he0 : (0 : ℝ) < e := by linarith [he.1]
    have hball := (eventually_countable_ball countable_Dy).2 fun d hd =>
      hZmod ((σ : ℝ), (((e : ℝ) : ℂ) * d, (e : ℝ) * radius k))
        ⟨hσ, mul_mem_Hbar_of_pos he0 (Dy_subset_Hbar hd), mul_pos he0 (radius_pos k)⟩
    filter_upwards [hball] with ω hω d hd
    exact (hω d hd).symm ▸ rfl
  filter_upwards [hZreg, hZraw, hRE, hwin,
    ae_forall_isRegularWith_joint (κ := κ) (γ := Real.sqrt κ) hB hX hind hT, hB'.cont,
    hB'.eval_zero_ae_eq_zero] with ω hZr hZw hRω hwω hG hc' h0'
    σ hσ e he k
  obtain ⟨G, -, hGr⟩ := hG
  have he0 : (0 : ℝ) < e := by linarith [he.1]
  set W' := drive κ B' ω with hW'
  have hW'c : Continuous W' := drive_continuous hc'
  have hW'0 : W' 0 = 0 := by simp [hW', drive, h0']
  set ψ := revMap (vrev W' σ) σ with hψ
  have hVc : Continuous (vrev W' σ) := continuous_vrev hW'c _
  have hs : (q : ℝ) + σ ∈ Icc (0 : ℝ) T := ⟨by linarith [hσ.1], by linarith [hσ.2]⟩
  have hreg : IsRegularWith (h0f κ ((q : ℝ) + σ) B X ω) (fun p => G ((q : ℝ) + σ, p)) := by
    rw [h0f_eq_unzippedField]; exact hGr _ hs
  -- the unzipped field of the pair and the map `ψ` agree on `ℍ`
  have hEq : EqOn (fwdMapInv W' σ) ψ H := by
    intro w hw
    rw [UnzipInvariance.fwdMapInv_eq_revMap_timeRev _ hW'c hW'0 hσ.1 hw]
    exact ReverseFlow.revMap_congr_drive w (fun r hr => (vrev_of_mem hr).symm)
  have hexact : ∀ t : ℝ, ∀ n : ℕ,
      evalReg (coordChange (ofFun (h0rev κ) + Y' ω) ψ (Qc (Real.sqrt κ)))
          (foldedCircle (((e : ℝ) : ℂ) * dyadicRoundC n (t : ℂ)) ((e : ℝ) * radius k)) =
        coordChange (ofFun (h0rev κ) + Y' ω) ψ (Qc (Real.sqrt κ))
          (foldedCircle (((e : ℝ) : ℂ) * dyadicRoundC n (t : ℂ)) ((e : ℝ) * radius k)) := by
    intro t n
    set w := ((e : ℝ) : ℂ) * dyadicRoundC n (t : ℂ) with hw
    have hwH : w ∈ Hbar := mul_mem_Hbar_of_pos he0
      (CircleCont.dyadicRoundC_mem_Hbar (by simp [Hbar]) n)
    have hr : 0 < (e : ℝ) * radius k := mul_pos he0 (radius_pos k)
    have hU := (hZr σ hσ).evalReg_fc w hr
    rw [CircleFubini.foldH_of_mem' hwH] at hU
    have hA : avgReg (coordChange (ofFun (h0rev κ) + Y' ω) ψ (Qc (Real.sqrt κ))) =
        avgReg (unzippedField (Real.sqrt κ) (ofFun (h0rev κ) + Y' ω, W') σ) := by
      unfold unzippedField
      exact (Cor15Group.avgReg_coordChange_congr_H _ hEq _).symm
    have hraw : coordChange (ofFun (h0rev κ) + Y' ω) ψ (Qc (Real.sqrt κ)) (foldedCircle w
        ((e : ℝ) * radius k)) = unzippedField (Real.sqrt κ) (ofFun (h0rev κ) + Y' ω, W') σ
          (foldedCircle w ((e : ℝ) * radius k)) := by
      unfold unzippedField
      exact (coordChange_congr_onH _ hEq _ (TwoPoint.foldedCircle_ae_mem_H _ hr)).symm
    have hev : evalReg (coordChange (ofFun (h0rev κ) + Y' ω) ψ (Qc (Real.sqrt κ))) =
        evalReg (unzippedField (Real.sqrt κ) (ofFun (h0rev κ) + Y' ω, W') σ) := by
      funext ν; unfold evalReg; rw [hA]
    rw [hev, hraw, hU, hw, hZw σ hσ e he k _ (dyadicRoundC_real_mem_Dy n t)]
  have hRE' := hRω σ hσ
  have key := offset_ident hγ hreg hRE'
    (differentiableOn_revMap _ hVc hσ.1) (fun w hw => deriv_revMap_ne_zero _ hVc hσ.1 hw)
    (TwoPoint.measurable_revMap hVc hσ.1) (injOn_revMap _ hVc hσ.1) he0 k hexact
    (awTest (realRevMap (Vr κ T B ω) (T - ((q : ℝ) + σ))) u v f)
  unfold awIntOff pairJc
  simp only [goodRad]
  rw [key, hwω σ hσ]
  have hmapEq : EqOn (fun z => ψ (((e : ℝ) : ℂ) * z))
      (fun z => revMapExt (vrev W' σ) σ (((e : ℝ) : ℂ) * z)) H := by
    intro z hz
    simp only [hψ]
    rw [revMapExt_eq_revMap hVc hσ.1 (mul_mem_H_of_pos he0 hz)]
  rw [bdryApprox_coordChange_congr_onH _ _ hmapEq]

end SWCore
end QuantumZipper
