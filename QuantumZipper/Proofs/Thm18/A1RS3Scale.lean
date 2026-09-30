import QuantumZipper.Proofs.Thm18.A1RS3Resc
import QuantumZipper.Proofs.Thm18.G1ZmScale

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# A1RS3 (2): Brownian scaling of the side map and of the pushed side circles (deterministic)

For a good driver `V` and `b > 0`, the scaled driver `W = V(b² ·)/b` (Loewner scaling:
`f^W_t = b⁻¹ f^V_{b²t}(b ·)`, trace `η_W = b⁻¹ η_V(b² ·)`):

* `scaledDrv_eq`: `V(b² max(r,0))/b = V(b² r)/b` (the driver of the canonical configuration);
* `mem_traceImg_scale`: the trace image of `W` is the trace image of `V` dilated by `b⁻¹`;
* `sideMap_scale`: `ψ_W(w) = b⁻¹ ψ_V(μ⁻¹ w)` on `ℍ` for some `μ > 0` (both are inverse normalized
  uniformizers of the dilated side domain, `G1Zm.invFunOn_dil`);
* `a1rMu_scale`: `(a1rMu W t d s).map (b ·) = a1rMu V (b² t) (μ⁻¹ d) (μ⁻¹ s)`;
* `sidePush_scale`: `(ψ_W* fc(d, s)).map (b ·) = ψ_V* fc(μ⁻¹ d, μ⁻¹ s)`.

Own elementary bookkeeping (as `G1Zm.psi_scalePath`, for the side map `g1zSideMap`).
-/

noncomputable section

open MeasureTheory Set Filter Metric
open scoped Topology

namespace QuantumZipper
namespace R18
namespace A1RS

open Thm18Asm

variable {V : ℝ → ℝ} {b : ℝ}

theorem scaledDrv_eq (hG : G1zDrvGood V) (hb : 0 < b) :
    (fun r => V (b ^ 2 * max r 0) / b) = fun r => V (b ^ 2 * r) / b := by
  funext r
  rw [hG.2.2.1 (b ^ 2 * r), mul_max_of_nonneg _ _ (by positivity : (0 : ℝ) ≤ b ^ 2), mul_zero]

/-- The trace image of `V(b² ·)/b` is that of `V` dilated by `b⁻¹`. -/
theorem mem_traceImg_scale (hV : Continuous V) (hV0 : V 0 = 0) (hb : 0 < b)
    (hex : ∀ t : ℝ, 0 ≤ t → ∃ p : ℂ,
      Tendsto (fun y : ℝ => fwdMapInv V t (y * Complex.I)) (𝓝[>] 0) (𝓝 p)) (w : ℂ) :
    w ∈ trace (fun r => V (b ^ 2 * r) / b) '' Ici 0 ↔
      (((b⁻¹ : ℝ) : ℂ))⁻¹ * w ∈ trace V '' Ici 0 := by
  have hb' : (b : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hb.ne'
  have htr : ∀ t : ℝ, 0 ≤ t → trace (fun r => V (b ^ 2 * r) / b) t = trace V (b ^ 2 * t) / b := by
    intro t ht
    obtain ⟨p, hp⟩ := hex (b ^ 2 * t) (by positivity)
    exact (RS.trace_scale hV hV0 hb ht hp).2
  have hinv : (((b⁻¹ : ℝ) : ℂ))⁻¹ * w = (b : ℂ) * w := by push_cast; rw [inv_inv]
  rw [hinv]
  constructor
  · rintro ⟨t, ht, rfl⟩
    refine ⟨b ^ 2 * t, mul_nonneg (sq_nonneg b) ht, ?_⟩
    rw [htr t ht, mul_div_cancel₀ _ hb']
  · rintro ⟨s, hs, hsw⟩
    have hs0 : (0 : ℝ) ≤ s / b ^ 2 := div_nonneg hs (sq_nonneg b)
    refine ⟨s / b ^ 2, hs0, ?_⟩
    rw [htr _ hs0, mul_div_cancel₀ _ (pow_pos hb 2).ne', hsw]
    field_simp

/-- **Scale covariance of the side map.** -/
theorem sideMap_scale (hGV : G1zDrvGood V) (hb : 0 < b)
    (hGW : G1zDrvGood fun r => V (b ^ 2 * r) / b)
    (hex : ∀ t : ℝ, 0 ≤ t → ∃ p : ℂ,
      Tendsto (fun y : ℝ => fwdMapInv V t (y * Complex.I)) (𝓝[>] 0) (𝓝 p)) (left : Bool) :
    ∃ μ : ℝ, 0 < μ ∧ ∀ w ∈ H, g1zSideMap left (fun r => V (b ^ 2 * r) / b) w =
      ((b⁻¹ : ℝ) : ℂ) * g1zSideMap left V (((μ : ℂ))⁻¹ * w) := by
  have hs := hGV.2.2.2.1
  have hs' := hGW.2.2.2.1
  have hN := G1ZA1a.isNormalizedUniformizer_sideDom hs left
  have hN' := G1ZA1a.isNormalizedUniformizer_sideDom hs' left
  have hD : ∀ w, w ∈ sideDom (trace fun r => V (b ^ 2 * r) / b) left ↔
      (((b⁻¹ : ℝ) : ℂ))⁻¹ * w ∈ sideDom (trace V) left :=
    G1Zm.mem_sideDom_dil (inv_pos.2 hb) (mem_traceImg_scale hGV.1 hGV.2.1 hb hex) left
  obtain ⟨μ, hμ, h⟩ := G1Zm.invFunOn_dil hN hN' (G1ZA1a.isOpen_sideDom hs' left)
    (G1ZA1a.nhdsWithin_zero_sideDom_neBot hs' left)
    (G1ZA1a.neBot_cobounded_inf_sideDom hs' left) (inv_pos.2 hb) hD
  exact ⟨μ, hμ, fun w hw => h w hw⟩

/-- The pointwise Loewner identity behind `a1rMu_scale`. -/
theorem fwdMap_sideMap_scale (hGV : G1zDrvGood V) (hb : 0 < b)
    (hGW : G1zDrvGood fun r => V (b ^ 2 * r) / b) {left : Bool} {μ : ℝ}
    (hψ : ∀ w ∈ H, g1zSideMap left (fun r => V (b ^ 2 * r) / b) w =
      ((b⁻¹ : ℝ) : ℂ) * g1zSideMap left V (((μ : ℂ))⁻¹ * w))
    {t : ℝ} (ht : 0 ≤ t) {w : ℂ} (hw : w ∈ H) :
    (b : ℂ) * fwdMap (fun r => V (b ^ 2 * r) / b) t
        (g1zSideMap left (fun r => V (b ^ 2 * r) / b) w) =
      fwdMap V (b ^ 2 * t) (g1zSideMap left V (((μ : ℂ))⁻¹ * w)) := by
  set W : ℝ → ℝ := fun r => V (b ^ 2 * r) / b with hWdef
  have hb' : (b : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hb.ne'
  have hz := sideMap_mem_compl_fwdHull hGW ht left hw
  set z := g1zSideMap left W w with hzdef
  have hu : fwdMap W t z ∈ H := FwdHolo.mapsTo_fwdMap hGW.1 ht hz
  have hbu : (b : ℂ) * fwdMap W t z ∈ H := by
    show 0 < ((b : ℂ) * fwdMap W t z).im
    rw [Complex.im_ofReal_mul]
    exact mul_pos hb hu
  have h1 : fwdMapInv W t (fwdMap W t z) = z := RS.fwdMapInv_fwdMap hGW.1 hGW.2.1 ht hz
  rw [hWdef, RS.fwdMapInv_scale hGV.1 hGV.2.1 hb ht hu] at h1
  have h2 : fwdMapInv V (b ^ 2 * t) ((b : ℂ) * fwdMap W t z) =
      g1zSideMap left V (((μ : ℂ))⁻¹ * w) := by
    rw [div_eq_iff hb'] at h1
    rw [h1, hzdef, hψ w hw]
    push_cast
    field_simp
  rw [← h2, RS.fwdMap_fwdMapInv hGV.1 hGV.2.1 (by positivity) hbu]

/-- **Scaling of the pushed side circles.** -/
theorem a1rMu_scale (hGV : G1zDrvGood V) (hb : 0 < b)
    (hGW : G1zDrvGood fun r => V (b ^ 2 * r) / b) {left : Bool} {μ : ℝ} (hμ : 0 < μ)
    (hψ : ∀ w ∈ H, g1zSideMap left (fun r => V (b ^ 2 * r) / b) w =
      ((b⁻¹ : ℝ) : ℂ) * g1zSideMap left V (((μ : ℂ))⁻¹ * w))
    {t : ℝ} (ht : 0 < t) (d : ℂ) {s : ℝ} (hs : 0 < s) :
    (a1rMu (fun r => V (b ^ 2 * r) / b) t left d s).map (fun z => (b : ℂ) * z) =
      a1rMu V (b ^ 2 * t) left (((μ⁻¹ : ℝ) : ℂ) * d) (μ⁻¹ * s) := by
  set W : ℝ → ℝ := fun r => V (b ^ 2 * r) / b with hWdef
  have hbt : 0 < b ^ 2 * t := by positivity
  obtain ⟨-, -, g, hgm, hEq⟩ := A1R.sidePush_props hGW ht left
  obtain ⟨-, -, g', hgm', hEq'⟩ := A1R.sidePush_props hGV hbt left
  have hae := TwoPoint.foldedCircle_ae_mem_H d hs
  have hFa : AEMeasurable (fun w => fwdMap W t (g1zSideMap left W w)) (foldedCircle d s) :=
    hgm.aemeasurable.congr (hae.mono fun w hw => (hEq hw).symm)
  have hμi : 0 < μ⁻¹ := inv_pos.2 hμ
  have hc : Measurable fun w : ℂ => ((μ⁻¹ : ℝ) : ℂ) * w := measurable_const_mul _
  have hae' := TwoPoint.foldedCircle_ae_mem_H (((μ⁻¹ : ℝ) : ℂ) * d) (mul_pos hμi hs)
  have hGa : AEMeasurable (fun w => fwdMap V (b ^ 2 * t) (g1zSideMap left V w))
      ((foldedCircle d s).map fun w => ((μ⁻¹ : ℝ) : ℂ) * w) := by
    rw [WedgeTK.fc_map_mul d s hμi]
    exact hgm'.aemeasurable.congr (hae'.mono fun w hw => (hEq' hw).symm)
  unfold a1rMu
  rw [AEMeasurable.map_map_of_aemeasurable (measurable_const_mul _).aemeasurable hFa,
    ← WedgeTK.fc_map_mul d s hμi, AEMeasurable.map_map_of_aemeasurable hGa hc.aemeasurable]
  refine Measure.map_congr (hae.mono fun w hw => ?_)
  simp only [Function.comp_apply]
  rw [fwdMap_sideMap_scale hGV hb hGW hψ ht.le hw]
  push_cast
  rfl

/-- **Scaling of the side circles pushed by the side map.** -/
theorem sidePush_scale (hGV : G1zDrvGood V) (hb : 0 < b)
    (hGW : G1zDrvGood fun r => V (b ^ 2 * r) / b) {left : Bool} {μ : ℝ} (hμ : 0 < μ)
    (hψ : ∀ w ∈ H, g1zSideMap left (fun r => V (b ^ 2 * r) / b) w =
      ((b⁻¹ : ℝ) : ℂ) * g1zSideMap left V (((μ : ℂ))⁻¹ * w)) (d : ℂ) {s : ℝ} (hs : 0 < s) :
    ((foldedCircle d s).map (g1zSideMap left fun r => V (b ^ 2 * r) / b)).map
        (fun z => (b : ℂ) * z) =
      (foldedCircle (((μ⁻¹ : ℝ) : ℂ) * d) (μ⁻¹ * s)).map (g1zSideMap left V) := by
  have hb' : (b : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hb.ne'
  have hμi : 0 < μ⁻¹ := inv_pos.2 hμ
  have hm := measurable_g1zSideMap hGW left
  have hm' := measurable_g1zSideMap hGV left
  have hc : Measurable fun w : ℂ => ((μ⁻¹ : ℝ) : ℂ) * w := measurable_const_mul _
  rw [Measure.map_map (measurable_const_mul _) hm, ← WedgeTK.fc_map_mul d s hμi,
    Measure.map_map hm' hc]
  refine Measure.map_congr ((TwoPoint.foldedCircle_ae_mem_H d hs).mono fun w hw => ?_)
  simp only [Function.comp_apply]
  rw [hψ w hw]
  push_cast
  field_simp

end A1RS
end R18
end QuantumZipper
