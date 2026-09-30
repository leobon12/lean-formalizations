import QuantumZipper.Proofs.Thm18.G3ZqNodes
import QuantumZipper.Proofs.Thm18.G0MapLoc
import QuantumZipper.Proofs.Thm18.G3ZpExt
import QuantumZipper.Proofs.Thm18.G3Cv2Reg

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# G3PATH-FIX (map): the local maps of a good path are G0 maps near `0` on `ℍ`

* `g3mapP_g0Ext`: at every point of the side half-line, the measurable local map
  `g3mapP Ψ left (y, a, 1, x)` of a good path agrees on `ball 0 r₀ ∩ ℍ` with an admissible map of
  G0 (`IsG0Map`), namely `w ↦ Ψ̃(w + Φ⁻¹(x)) − x` with `Ψ̃` the Schwarz reflection of the side map
  (`G1Z2.sideReflChordStmt_holds`). Same argument as `G0MapLoc.g1zLocMap_g0Ext`, at one point.
* `agreeNear_zoomFieldVia_of_eqOn`: two local maps agreeing on `ball 0 r₀ ∩ ℍ` give zooms whose
  raw values agree at the dyadic folded circles inside `ball 0 r₀`.

Own elementary bookkeeping (AGENT_GUIDE cost rule).
-/

noncomputable section

open MeasureTheory Filter Set Metric Complex
open scoped Topology NNReal

namespace QuantumZipper
namespace Thm18Asm
namespace G3ZqF

open G3Z2b2 G1ZZ1

/-- **The local map of a good path at a side point agrees near `0` on `ℍ` with a G0 map.** -/
theorem g3mapP_g0Ext {γ : ℝ} {Ψ : Bool → (ℝ≥0 → ℝ) → ℂ → ℂ} (hsel : G1PsiSel γ Ψ)
    {a : ℝ≥0 → ℝ} (ha : G3Zq.G3ZqGoodPath γ a) {left : Bool} {x : ℝ}
    (hx : x ∈ g1SideHalf left) (y : FieldSample) :
    ∃ r₀ : ℝ, 0 < r₀ ∧ ∃ Φ : ℂ → ℂ, IsG0Map r₀ Φ ∧
      EqOn Φ (g3mapP Ψ left (y, a, 1, x)) (ball 0 r₀ ∩ H) := by
  obtain ⟨φ₀, hφ₀, hΨa⟩ := hsel.2.2 a ha.1 ha.2 left
  obtain ⟨Φo, hR⟩ := G1Z2.sideReflChordStmt_holds _ ha.2 left φ₀ hφ₀
  rw [← hΨa] at hR
  set B : ℝ := Φo.symm x with hBdef
  have hB : B ∈ g1SideHalf left := (mem_half_symm_iff hR.1 left x).2 hx
  have hΦB : Φo B = x := Φo.apply_symm_apply x
  have hpre : g3bpre Ψ left a x = B := g3bpre_eq hR hx
  have hB0 : 0 < |B| := by
    cases left <;> simp only [g1SideHalf, Bool.false_eq_true, if_false, if_true, mem_Ioi,
      mem_Iio] at hB
    · exact abs_pos.2 hB.ne'
    · exact abs_pos.2 hB.ne
  set δ : ℝ := |B| / 2 with hδ
  have hδ0 : 0 < δ := by positivity
  have hIcc : Icc (B - δ) (B + δ) ⊆ g1SideHalf left := by
    intro t ht
    cases left <;> simp only [g1SideHalf, Bool.false_eq_true, if_false, if_true, mem_Ioi,
      mem_Iio] at hB ⊢
    · rw [abs_of_pos hB] at hδ; linarith [ht.1]
    · rw [abs_of_neg hB] at hδ; linarith [ht.2]
  obtain ⟨U, Ψt, hU, hJU, hΨ, hΨΦ, hder, heqH⟩ := hR.2 (B - δ) (B + δ) (by linarith) hIcc
  have hBI : B ∈ Icc (B - δ) (B + δ) := ⟨by linarith, by linarith⟩
  have hdiffAt : ∀ t ∈ Icc (B - δ) (B + δ), HasStrictDerivAt Ψt (deriv Ψt t) (t : ℂ) :=
    fun t ht => ((hΨ.analyticAt (hU.mem_nhds (hJU t ht))).hasStrictDerivAt)
  have hs := (hdiffAt B hBI).hasStrictFDerivAt_equiv (hder B hBI)
  set e := hs.toOpenPartialHomeomorph Ψt with he
  have hinj : InjOn Ψt e.source := by
    have := e.injOn
    rwa [he, hs.toOpenPartialHomeomorph_coe] at this
  set O : Set ℂ := e.source ∩ U ∩ {z | B - δ < z.re ∧ z.re < B + δ} with hO
  have hOo : IsOpen O := (e.open_source.inter hU).inter
    ((isOpen_lt continuous_const Complex.continuous_re).inter
      (isOpen_lt Complex.continuous_re continuous_const))
  have hBre : (B : ℂ) ∈ {z : ℂ | B - δ < z.re ∧ z.re < B + δ} := by
    simp only [mem_setOf_eq, ofReal_re]
    constructor <;> linarith
  have hBO : (B : ℂ) ∈ O := ⟨⟨hs.mem_toOpenPartialHomeomorph_source, hJU B hBI⟩, hBre⟩
  obtain ⟨ε, hε, hεO⟩ := Metric.isOpen_iff.1 hOo _ hBO
  have hball : ∀ w ∈ ball (0 : ℂ) ε, w + (B : ℂ) ∈ O := by
    intro w hw
    apply hεO
    rw [mem_ball, dist_eq_norm, add_sub_cancel_right]
    simpa using hw
  set d := deriv Ψt B with hd
  have hdb : HasDerivAt Ψt d (B : ℂ) := (hdiffAt B hBI).hasDerivAt
  have hKw : B ∈ Ioo (B - δ) (B + δ) := ⟨by linarith, by linarith⟩
  have hre : ∀ᶠ t : ℝ in 𝓝 B, (Ψt (t : ℂ)) = ((Φo t : ℝ) : ℂ) := by
    filter_upwards [Ioo_mem_nhds hKw.1 hKw.2] with t ht
    exact hΨΦ t (Ioo_subset_Icc_self ht)
  have hIm : HasDerivAt (fun t : ℝ => (Ψt (t : ℂ)).im) d.im B := by
    have := (hdb.const_mul (-Complex.I)).real_of_complex
    simpa using this
  have hIm0 : d.im = 0 := by
    have h0 : HasDerivAt (fun t : ℝ => (Ψt (t : ℂ)).im) 0 B :=
      (hasDerivAt_const B (0 : ℝ)).congr_of_eventuallyEq
        (hre.mono fun t ht => by simp [ht])
    exact hIm.unique h0
  have hRe : HasDerivAt (fun t : ℝ => Φo t) d.re B := by
    have h1 : HasDerivAt (fun t : ℝ => (Ψt (t : ℂ)).re) d.re B := hdb.real_of_complex
    exact h1.congr_of_eventuallyEq (hre.mono fun t ht => by simp [ht])
  have hRe0 : 0 ≤ d.re := hRe.nonneg_of_monotone Φo.monotone
  have hdne : d ≠ 0 := hder B hBI
  have hRepos : 0 < d.re := by
    rcases hRe0.lt_or_eq with h | h
    · exact h
    · exact absurd (Complex.ext h.symm hIm0) hdne
  have hderiv0 : deriv (fun w : ℂ => Ψt (w + (B : ℂ)) - (x : ℂ)) 0 = d := by
    have h1 : HasDerivAt (fun w : ℂ => Ψt (w + (B : ℂ))) d 0 :=
      HasDerivAt.comp_add_const 0 (B : ℂ) (by simpa using hdb)
    exact (h1.sub_const (x : ℂ)).deriv
  refine ⟨ε, hε, fun w => Ψt (w + (B : ℂ)) - (x : ℂ), ⟨?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
  · intro w hw
    have hwU : w + (B : ℂ) ∈ U := (hball w hw).1.2
    exact ((hΨ.differentiableAt (hU.mem_nhds hwU)).comp w
      (differentiableAt_id.add_const _)).differentiableWithinAt.sub_const _
  · intro w hw v hv hwv
    have h1 : Ψt (w + (B : ℂ)) = Ψt (v + (B : ℂ)) := by simpa using hwv
    have := hinj (hball w hw).1.1 (hball v hv).1.1 h1
    simpa using this
  · intro t ht
    have htb : (t : ℂ) + (B : ℂ) ∈ O := hball _ (by simpa using ht)
    have hI : t + B ∈ Icc (B - δ) (B + δ) := by
      obtain ⟨-, h1, h2⟩ := htb
      simp at h1 h2
      exact ⟨by linarith, by linarith⟩
    show (Ψt ((t : ℂ) + (B : ℂ)) - (x : ℂ)).im = 0
    rw [← Complex.ofReal_add, hΨΦ _ hI]
    simp
  · show Ψt ((0 : ℂ) + (B : ℂ)) - (x : ℂ) = 0
    rw [zero_add, hΨΦ B hBI, hΦB, sub_self]
  · show (deriv (fun w : ℂ => Ψt (w + (B : ℂ)) - (x : ℂ)) 0).im = 0
    rw [hderiv0, hIm0]
  · show 0 < (deriv (fun w : ℂ => Ψt (w + (B : ℂ)) - (x : ℂ)) 0).re
    rw [hderiv0]; exact hRepos
  · intro w hw
    have hwH : w + (B : ℂ) ∈ H := by
      show 0 < (w + (B : ℂ)).im; simpa using (show 0 < w.im from hw.2)
    show Ψt (w + (B : ℂ)) - (x : ℂ) = g3mapP Ψ left (y, a, 1, x) w
    simp only [g3mapP, g3mapB, g3locM, div_one, ofReal_one, one_mul, hpre]
    rw [heqH hwH]

/-- **Zooms through two maps agreeing on `ball 0 r₀ ∩ ℍ` agree near `0`.** -/
theorem agreeNear_zoomFieldVia_of_eqOn {r₀ : ℝ} {ψ Φ : ℂ → ℂ}
    (heq : EqOn Φ ψ (ball 0 r₀ ∩ H)) (γ L : ℝ) (h : FieldSample) (x : ℝ) :
    D3Plus.AgreeNear (zoomFieldVia γ L h x ψ) (zoomFieldVia γ L h x Φ) r₀ := by
  intro n k z hz
  set d := dyadicRoundC n z with hddef
  have hk := radius_pos k
  have hnull := G3Cv.foldedCircle_compl_null (c := d) (b := 0) (ρ := ‖d‖ + radius k) hk
    (by simp)
  have hmem : ∀ᵐ u ∂foldedCircle d (radius k), u ∈ ball (0 : ℂ) r₀ ∩ H := by
    filter_upwards [G3Cv.ae_mem_of_compl_null_g3cv hnull,
      TwoPoint.foldedCircle_ae_mem_H d hk] with u hu hu'
    refine ⟨?_, hu'⟩
    have : ‖u‖ ≤ ‖d‖ + radius k := by simpa using hu.1
    rw [mem_ball, dist_zero_right]; linarith
  have hmap : (foldedCircle d (radius k)).map ψ = (foldedCircle d (radius k)).map Φ :=
    Measure.map_congr (hmem.mono fun u hu => (heq hu).symm)
  have hder : (fun u => Real.log ‖deriv ψ u‖) =ᵐ[foldedCircle d (radius k)]
      fun u => Real.log ‖deriv Φ u‖ :=
    hmem.mono fun u hu => by
      show Real.log ‖deriv ψ u‖ = Real.log ‖deriv Φ u‖
      rw [Filter.EventuallyEq.deriv_eq (eventually_of_mem
        ((isOpen_ball.inter isOpen_H).mem_nhds hu) fun v hv => (heq hv).symm)]
  have hc : coordChange (translate h (x : ℂ)) ψ (Qc γ) (foldedCircle d (radius k)) =
      coordChange (translate h (x : ℂ)) Φ (Qc γ) (foldedCircle d (radius k)) := by
    simp only [coordChange, hmap, integral_congr_ae hder]
  simp only [zoomFieldVia, addConst, hc]

end G3ZqF
end Thm18Asm
end QuantumZipper
