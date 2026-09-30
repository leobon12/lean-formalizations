import QuantumZipper.Proofs.Section5.Prop16D4WAssembly
import QuantumZipper.Proofs.Section5.Prop16D4WInNice

/-!
# D4⁺ʷ inputs (part 2): the unperturbed zoomed field and the clause `hloc`

The unperturbed zoomed field of Proposition 1.6 at the marked point `p = (ω, t)` is
`zoomFree γ C 𝔥₀ X p = X ω(· + t) + C/γ + 𝔥₀(t)`: the zoomed field
`h(· + t) + C/γ` (`h = 𝔥₀ + X ω`) with the continuous remainder `ψ_t = 𝔥₀(· + t) − 𝔥₀(t)`
removed (Sheffield, arXiv:1012.4797, proof of Prop. 1.6, p. 25: near a boundary point `𝔥₀` is
approximately the constant `𝔥₀(t)`).

For a sample locally good on `D ∪ (a,b)` (`x = y + ψ` on the dyadic folded circles near it):
* `fcAgree_zoomField`, `circAgree_zoomFree`, `circAgree_zoomY`: the zoomed fields agree near
  `D − t` with `y(· + t)` plus explicit continuous functions;
* `hloc_point`: the deterministic content of clause `hloc` of `Prop16D4WInputsStmt`, with
  `V = (D ∪ (a,b)) − t`;
* `prop16_hloc`: clause `hloc` under the weighted law.
Own elementary arguments (bookkeeping of the local rule).
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Metric
open scoped Topology ENNReal

namespace QuantumZipper

namespace Prop16Asm

open Prop16Area.G GoodSample RegClosure LocalRule CircleFubini

/-- **The unperturbed zoomed field** `X ω(· + t) + C/γ + 𝔥₀(t)` at `p = (ω, t)`. -/
def zoomFree (γ C : ℝ) (h0 : ℂ → ℝ) {Ω : Type} (X : Ω → FieldSample) (p : Ω × ℝ) :
    FieldSample :=
  addConst (zoomField γ C (X p.1) p.2) (h0 p.2)

/-- The neighbourhood `(D ∪ (a,b)) − t` of `D − t`. -/
abbrev zoomNbhd (D : Set ℂ) (a b t : ℝ) : Set ℂ := zoomDomain (D ∪ realSet (Ioo a b)) t

theorem fcAgree_addConst_ofFun {W : Set ℂ} {F z : FieldSample} {φ : ℂ → ℝ}
    (hφ : ContinuousOn φ (W ∩ Hbar)) (h : FcAgree W F (z + ofFun φ)) (c : ℝ) :
    FcAgree W (addConst F c) (z + ofFun (fun u => φ u + c)) := by
  intro d hd r hr hW
  have hi := integrable_fc_of_continuousOn hd hr (hφ.mono fun u hu => ⟨hW hu, hu.2⟩)
  have e := h d hd r hr hW
  simp only [addConst, Pi.add_apply, ofFun] at e ⊢
  rw [e, integral_add hi (integrable_const c), integral_const]
  simp [measureReal_def]
  ring

theorem preimage_add_inter_Hbar (W : Set ℂ) (t : ℝ) :
    (fun z => z + (t : ℂ)) ⁻¹' W ∩ Hbar = (fun z => z + (t : ℂ)) ⁻¹' (W ∩ Hbar) := by
  ext z
  simp [Hbar]

theorem continuousOn_comp_add {S : Set ℂ} {f : ℂ → ℝ} (hf : ContinuousOn f S) (t : ℝ) :
    ContinuousOn (fun u => f (u + t)) ((fun z => z + (t : ℂ)) ⁻¹' S) :=
  hf.comp (continuous_id.add continuous_const).continuousOn fun _ hu => hu

section Agree

variable {γ : ℝ} {V0 W : Set ℂ} (hWo : IsOpen W) (hWV : W ∩ Hbar = V0) {x0 y : FieldSample}
  {ψ : ℂ → ℝ} (hy : IsLQGGood γ y) (hψ : ContinuousOn ψ V0) (hag : CircAgree W x0 (y + ofFun ψ))
include hWo hWV hy hψ hag

/-- The zoomed field of a locally good sample. -/
theorem fcAgree_zoomField (C t : ℝ) :
    FcAgree ((fun z => z + (t : ℂ)) ⁻¹' W) (zoomField γ C x0 t)
      (translate y (t : ℂ) + ofFun (fun u => ψ (u + t) + C / γ)) := by
  have hψW : ContinuousOn ψ (W ∩ Hbar) := hWV ▸ hψ
  have hψt : ContinuousOn (fun u => ψ (u + t)) ((fun z => z + (t : ℂ)) ⁻¹' W ∩ Hbar) := by
    rw [preimage_add_inter_Hbar]; exact continuousOn_comp_add hψW t
  exact fcAgree_addConst_ofFun hψt
    ((fcAgree_translate hWo hag t).trans (fcAgree_translate_add_ofFun hy.1 hWo hψW t)) (C / γ)

/-- The unperturbed zoomed field of a locally good sample. -/
theorem circAgree_zoomFree (C t k : ℝ) :
    CircAgree ((fun z => z + (t : ℂ)) ⁻¹' W) (addConst (zoomField γ C x0 t) k)
      (translate y (t : ℂ) + ofFun (fun u => ψ (u + t) + C / γ + k)) := by
  have hψW : ContinuousOn ψ (W ∩ Hbar) := hWV ▸ hψ
  have hψt : ContinuousOn (fun u => ψ (u + t) + C / γ) ((fun z => z + (t : ℂ)) ⁻¹' W ∩ Hbar) := by
    rw [preimage_add_inter_Hbar]; exact (continuousOn_comp_add hψW t).add continuousOn_const
  exact (fcAgree_addConst_ofFun hψt (fcAgree_zoomField hWo hWV hy hψ hag C t) k).circAgree

end Agree

/-- **Clause `hloc`, deterministic form.** -/
theorem hloc_point {γ : ℝ} {D : Set ℂ} (hD : IsOpen D) (hDH : D ⊆ H) {a b : ℝ} {h0 : ℂ → ℝ}
    (hh0 : ContinuousOn h0 (D ∪ realSet (Ioo a b))) {x0 : FieldSample}
    (hx : IsLocallyGoodOn γ (D ∪ realSet (Ioo a b)) x0) (C t : ℝ) :
    IsLocallyGoodOn γ (zoomNbhd D a b t) (addConst (zoomField γ C x0 t) (h0 t)) ∧
      zoomDomain D t ⊆ zoomNbhd D a b t ∧
      ContinuousOn (fun z => h0 (z + t) - h0 t) (zoomNbhd D a b t) ∧
      IsLocallyGoodOn γ (zoomNbhd D a b t) (zoomField γ C (ofFun h0 + x0) t) ∧
      qAreaMeasureOn γ (zoomField γ C (ofFun h0 + x0) t) (zoomDomain D t) =
        qAreaMeasureOn γ (ofFun (fun z => h0 (z + t) - h0 t) + addConst (zoomField γ C x0 t) (h0 t))
          (zoomDomain D t) := by
  obtain ⟨W, hWo, hWV, y, ψ, hy, hψ, hag⟩ := hx
  set V0 := D ∪ realSet (Ioo a b)
  set Wt := (fun z => z + (t : ℂ)) ⁻¹' W with hWt
  have hWto : IsOpen Wt := hWo.preimage (continuous_id.add continuous_const)
  have hWtV : Wt ∩ Hbar = zoomNbhd D a b t := by
    rw [hWt, preimage_add_inter_Hbar, hWV]; rfl
  have hyt : IsLQGGood γ (translate y (t : ℂ)) := hy.translate t
  have hψt : ContinuousOn (fun u => ψ (u + t)) (zoomNbhd D a b t) := continuousOn_comp_add hψ t
  have hh0t : ContinuousOn (fun u => h0 (u + t)) (zoomNbhd D a b t) := continuousOn_comp_add hh0 t
  have hrem : ContinuousOn (fun z => h0 (z + t) - h0 t) (zoomNbhd D a b t) :=
    hh0t.sub continuousOn_const
  -- the unperturbed field
  have hF := circAgree_zoomFree hWo hWV hy hψ hag C t (h0 t)
  have hφF : ContinuousOn (fun u => ψ (u + t) + C / γ + h0 t) (zoomNbhd D a b t) :=
    (hψt.add continuousOn_const).add continuousOn_const
  -- the actual zoomed field
  have hag' := circAgree_ofFun_add hWV hψ hh0 hag
  have hY : FcAgree Wt (zoomField γ C (ofFun h0 + x0) t)
      (translate y (t : ℂ) + ofFun (fun u => (ψ (u + t) + h0 (u + t)) + C / γ)) :=
    fcAgree_zoomField hWo hWV hy (hψ.add hh0) hag' C t
  have hφY : ContinuousOn (fun u => (ψ (u + t) + h0 (u + t)) + C / γ) (zoomNbhd D a b t) :=
    (hψt.add hh0t).add continuousOn_const
  -- the perturbed unperturbed field
  have hFp := circAgree_ofFun_add hWtV hφF hrem hF
  have hUo : IsOpen (zoomDomain D t) := hD.preimage (continuous_id.add continuous_const)
  have hUH : zoomDomain D t ⊆ H := fun z hz => by
    have : 0 < (z + (t : ℂ)).im := hDH hz
    show 0 < z.im
    simpa using this
  have hUV : zoomDomain D t ⊆ zoomNbhd D a b t := preimage_mono subset_union_left
  have hUW : zoomDomain D t ⊆ Wt := fun z hz => by
    have := hUV hz
    rw [← hWtV] at this
    exact this.1
  refine ⟨⟨Wt, hWto, hWtV, _, _, hyt, hφF, hF⟩, hUV, hrem, ⟨Wt, hWto, hWtV, _, _, hyt, hφY,
    hY.circAgree⟩, ?_⟩
  rw [qAreaMeasureOn_eq_withDensity_of_agree hWto hyt (hWtV ▸ hφY) hY.circAgree hUo hUH hUW,
    qAreaMeasureOn_eq_withDensity_of_agree hWto hyt (hWtV ▸ (hφF.add hrem)) hFp hUo hUH hUW]
  congr 1
  funext u
  congr 3
  ring

variable {Ω : Type} [MeasurableSpace Ω]

/-- **Clause `hloc` of `Prop16D4WInputsStmt`** under the weighted law, from local goodness. -/
theorem prop16_hloc {γ : ℝ} {D : Set ℂ} {c d a b : ℝ} {h0 : ℂ → ℝ} {P : Measure Ω}
    {X : Ω → FieldSample} (hdat : Prop16Data γ D c d a b h0 P X)
    (hν : AEMeasurable (fun ω => prop16Nu γ h0 a b (X ω)) P)
    (hlg : ∀ᵐ ω ∂P, IsLocallyGoodOn γ (D ∪ realSet (Ioo a b)) (X ω)) (C : ℝ) :
    ∀ᵐ p ∂(prop16Q γ h0 a b P X),
      IsLocallyGoodOn γ (zoomNbhd D a b p.2) (zoomFree γ C h0 X p) ∧
      zoomDomain D p.2 ⊆ zoomNbhd D a b p.2 ∧
      ContinuousOn (fun z => h0 (z + p.2) - h0 p.2) (zoomNbhd D a b p.2) ∧
      IsLocallyGoodOn γ (zoomNbhd D a b p.2) (zoomField γ C (ofFun h0 + X p.1) p.2) ∧
      qAreaMeasureOn γ (zoomField γ C (ofFun h0 + X p.1) p.2) (zoomDomain D p.2) =
        qAreaMeasureOn γ (ofFun (fun z => h0 (z + p.2) - h0 p.2) + zoomFree γ C h0 X p)
          (zoomDomain D p.2) := by
  obtain ⟨-, -, ⟨hDo, -, -, hDH, -⟩, -, -, -, hh0, -, -, -, hfin⟩ := hdat
  exact ae_prop16Law_of_ae (G := fun ω t =>
      IsLocallyGoodOn γ (zoomNbhd D a b t) (addConst (zoomField γ C (X ω) t) (h0 t)) ∧
      zoomDomain D t ⊆ zoomNbhd D a b t ∧
      ContinuousOn (fun z => h0 (z + t) - h0 t) (zoomNbhd D a b t) ∧
      IsLocallyGoodOn γ (zoomNbhd D a b t) (zoomField γ C (ofFun h0 + X ω) t) ∧
      qAreaMeasureOn γ (zoomField γ C (ofFun h0 + X ω) t) (zoomDomain D t) =
        qAreaMeasureOn γ (ofFun (fun z => h0 (z + t) - h0 t) +
          addConst (zoomField γ C (X ω) t) (h0 t)) (zoomDomain D t))
    (aemeasurable_prop16Kernel' hν hfin) (fun ω => sFinite_prop16Nu γ h0 a b (X ω))
    (fun ω => prop16Nu_compl_Ioo γ h0 a b (X ω))
    (hlg.mono fun ω hω t _ => hloc_point hDo hDH hh0 hω C t)

end Prop16Asm

end QuantumZipper
