import QuantumZipper.Proofs.Section5.Prop16LitRegP6

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# Proposition 1.6, literal form: local regularity of the Palm chart zoom at a fixed point (D98)

`Prop16Lit.ae_localAreaRegular_palm`: at a fixed boundary point `x ∈ (a,b)`, almost surely, for
every level `C`, the chart zoom of the Palm-shifted field is `LocalAreaRegular` on
`B(0, r₀ x) ∩ ℍ` (local coupling with the free field, `ae_chartY`, `localAreaRegular_zoomLit`).
Own bookkeeping (as `prop16LitExAFixStmt_proved`).
-/

noncomputable section

open MeasureTheory Filter Set Function Metric
open scoped Topology ENNReal

namespace QuantumZipper
namespace Prop16Lit

open ExA Prop16Asm CoordChangeArea

/-- **Coupled data at a fixed point, with a chart-regular translated free sample.** -/
theorem ae_coupled_chartY {D : Set ℂ} {c d : ℝ} (hgeo : K3.Prop16Geometry D c d) {Ω : Type}
    [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P] {X : Ω → FieldSample}
    (hX : IsMixedGFF D (realSet (Icc c d)) X P) {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) (x : ℝ)
    {ψ : ℂ → ℂ} (hψm : Measurable ψ) (hψd : DifferentiableOn ℂ ψ H) (hψi : InjOn ψ H) (hψH : MapsTo ψ H H)
    (hψ0 : ∀ z ∈ H, deriv ψ z ≠ 0) :
    ∀ᵐ ω ∂P, ∃ (xf yt : FieldSample) (G : ℂ × ℝ → ℝ) (φ : ℂ → ℝ), IsRegularWith xf G ∧
      (∃ ν, ChartY γ ψ yt ν) ∧ RawShift yt G x ∧ ContinuousOn φ D ∧
      Prop16Area.G.CircAgree D (X ω) (xf + ofFun φ) := by
  have hcd : c < d := hgeo.2.2.2.2.1
  obtain ⟨W, hWo, hWV⟩ := locGood_exists_open hgeo le_rfl le_rfl (a := c) (b := d)
  obtain ⟨Ω₀, _, _, P₀, Y, Xf, hP₀, hY, hXf, hag⟩ :=
    prop16MixedFreeLocCoupling_mm D c d c d hgeo hcd le_rfl le_rfl
  obtain ⟨G, hG⟩ := WedgeTK.exists_isRegVersion hXf
  have hXt : IsFreeGFFModConstH (fun ω₀ (μ : Measure ℂ) => Xf ω₀ (μ.map (· + (x : ℂ)))) P₀ :=
    S5.FieldLaw.Raw.isFreeGFFModConstH_translate hXf x
  have hS : ∀ᵐ ω₀ ∂P₀, ω₀ ∈ {ω₀ | (∃ ν, ChartY γ ψ (fun μ => Xf ω₀ (μ.map (· + (x : ℂ)))) ν) ∧
      IsRegularWith (Xf ω₀) (G ω₀) ∧ RawShift (fun μ => Xf ω₀ (μ.map (· + (x : ℂ)))) (G ω₀) x ∧
      ∃ φ : ℂ → ℝ, ContinuousOn φ (D ∪ realSet (Ioo c d)) ∧
        Prop16Area.G.CircAgree (D ∪ realSet (Ioo c d)) (Y ω₀) (Xf ω₀ + ofFun φ)} := by
    filter_upwards [ae_chartY hXt hγ hγ2 hψm hψd hψi hψH hψ0, hG.reg, ae_rawShift hG x, hag]
      with ω₀ h1 h2 h3 h4 using ⟨⟨_, h1⟩, h2, h3, h4⟩
  have hDW : D ⊆ W := fun z hz => by
    have : z ∈ W ∩ Hbar := by rw [hWV]; exact Or.inl hz
    exact this.1
  let I := {m : Measure ℂ // m ∈ locCircSet D}
  have : Countable I := (locCircSet_countable D).to_subtype
  have hadm : ∀ i : I, IsAdmissibleDual D (mixedSpace D (realSet (Icc c d))) i.1 := by
    rintro ⟨_, n, k, z, hz, hsub, rfl⟩
    exact locGood_isAdmissible_circle hgeo le_rfl le_rfl hWo hWV
      (CircleCont.dyadicRoundC_mem_Hbar hz n) (radius_pos k) (hsub.trans hDW)
  have hlaw := locGood_map_eq_of_isMixedGFF hX hY (fun i : I => i.1) hadm
  have hmF : Measurable fun ω (i : I) => X ω i.1 :=
    measurable_pi_iff.2 fun i => hX.measurable_coord _
  have hmG : Measurable fun ω (i : I) => Y ω i.1 :=
    measurable_pi_iff.2 fun i => hY.measurable_coord _
  filter_upwards [locGood_ae_exists_of_map_eq hmF.aemeasurable hmG hlaw hS] with ω hω
  obtain ⟨ω₀, ⟨h1, h2, h3, φ, hφ, hag'⟩, hFG⟩ := hω
  refine ⟨Xf ω₀, _, G ω₀, φ, h2, h1, h3, hφ.mono subset_union_left, fun n k z hz hsub => ?_⟩
  have e := congrFun hFG ⟨_, n, k, z, hz, hsub, rfl⟩
  exact e.trans (hag' n k z hz fun u hu => Or.inl (hsub hu))

theorem ae_localAreaRegular_palm {γ : ℝ} {D : Set ℂ} {c d a b : ℝ} {h0 : ℂ → ℝ} {Ω : Type}
    [MeasurableSpace Ω] {P : Measure Ω} {X : Ω → FieldSample}
    (hdat : Prop16Data γ D c d a b h0 P X) {ψ : ℝ → ℂ → ℂ} {r₀ : ℝ → ℝ}
    (hfam : LitFamily D a b ψ r₀) (x : ℝ) (hx : x ∈ Ioo a b) :
    ∀ᵐ ω ∂P, ∀ C : ℝ, ∃ μ, LocalAreaRegular γ
      (zoomFieldLit γ C (ofFun h0 + palmMixedField γ D (realSet (Icc c d)) X x ω) x (ψ x))
      (ball 0 (r₀ x) ∩ H) μ := by
  obtain ⟨hγ, hγ2, hgeo, -, hca, hbd, hh0, hP, hX, -, -⟩ := hdat
  obtain ⟨hψm, -, hch⟩ := hfam
  have hxcd : x ∈ Ioo c d := ⟨lt_of_le_of_lt hca hx.1, lt_of_lt_of_le hx.2 hbd⟩
  obtain ⟨hψd, hψi, hψim, -, -⟩ := hch x hx
  have hψxm : Measurable (ψ x) := hψm.comp (measurable_const.prodMk measurable_id)
  have hDo : IsOpen D := hgeo.1
  have hDH : D ⊆ H := hgeo.2.2.2.1
  have hZo : IsOpen (zoomDomain D x) := hDo.preimage (continuous_id.add continuous_const)
  have hZH : zoomDomain D x ⊆ H := zoomDomain_subset_H hDH x
  have hψZ : MapsTo (ψ x) H (zoomDomain D x) := fun w hw => hψim ▸ mem_image_of_mem (ψ x) hw
  have hψH : MapsTo (ψ x) H H := hψZ.mono_right hZH
  have hψ0 : ∀ z ∈ H, deriv (ψ x) z ≠ 0 := fun z hz =>
    CA.deriv_ne_zero_of_injOn isOpen_H hψd hψi hz
  haveI := hP
  filter_upwards [ae_coupled_chartY hgeo hX hγ hγ2 x hψxm hψd hψi hψH hψ0] with ω hω C
  obtain ⟨xf, yt, G, φ, hreg, ⟨ν, hcg⟩, hraw, hφ, hag⟩ := hω
  obtain ⟨g, hg, hagT⟩ := circAgree_palm_translate (γ := γ) hgeo hxcd
    (hh0.mono subset_union_left) hreg hraw hφ hag
  exact localAreaRegular_zoomLit hcg hψxm hψd hψ0 hψH hZo hg hagT (isOpen_ball.inter isOpen_H)
    inter_subset_right (hψZ.mono_left inter_subset_right) C

end Prop16Lit
end QuantumZipper
