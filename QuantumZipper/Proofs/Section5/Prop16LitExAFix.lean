import QuantumZipper.Proofs.Section5.Prop16LitExAFixD1
import QuantumZipper.Proofs.Section5.Prop16LitFixCovProof

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# Proposition 1.6, literal form: `Prop16LitExAFixStmt`, proved (COORD-CHANGE, D98)

At a fixed boundary point `x ∈ (a,b)`, almost surely, the chart zoom of the Palm-shifted field
satisfies the countable condition `GoodA` (local area limit on `B(0, r₀ x) ∩ ℍ` and eventually
finite approximations). Route (as `Prop16Lit.prop16LitFixCov1Stmt_proved`, split into small
lemmas): the local coupling of the mixed GFF with the free field
(`Prop16Asm.prop16MixedFreeLocCoupling_mm`) and the law transfer give a free sample `xf` with
`X ω = xf + φ` on the dyadic circles in `D` (`ae_coupled_data`); the Palm shift and `h₀` are
continuous on `D` (`Prop16Asm.continuousOn_palmPsi`); the translate by `x` of the free sample is a
chart-good free sample (`ae_chartGood`, DS11 Prop. 2.1); `goodA_zoomLit_of_agree` concludes.
Own bookkeeping.
-/

noncomputable section

open MeasureTheory Filter Set Function Metric
open scoped Topology ENNReal

namespace QuantumZipper
namespace Prop16Lit
namespace ExA

open Prop16Asm CoordChangeArea

/-- The raw dyadic values of `yt` are those of the witness `G` shifted by `x`. -/
def RawShift (yt : FieldSample) (G : ℂ × ℝ → ℝ) (x : ℝ) : Prop :=
  ∀ (n k : ℕ) (p : ℤ × ℤ), (⟨(p.1 : ℝ) / 2 ^ n, (p.2 : ℝ) / 2 ^ n⟩ : ℂ) ∈ Hbar →
    yt (foldedCircle ⟨(p.1 : ℝ) / 2 ^ n, (p.2 : ℝ) / 2 ^ n⟩ (radius k)) =
      G ((⟨(p.1 : ℝ) / 2 ^ n, (p.2 : ℝ) / 2 ^ n⟩ : ℂ) + (x : ℂ), radius k)

theorem ae_rawShift {Ω₀ : Type} [MeasurableSpace Ω₀] {P₀ : Measure Ω₀} {Xf : Ω₀ → FieldSample}
    {G : Ω₀ → ℂ × ℝ → ℝ} (hG : WedgeTK.IsRegVersion Xf P₀ G) (x : ℝ) :
    ∀ᵐ ω₀ ∂P₀, RawShift (fun μ => Xf ω₀ (μ.map (· + (x : ℂ)))) (G ω₀) x := by
  unfold RawShift
  rw [ae_all_iff]; intro n; rw [ae_all_iff]; intro k; rw [ae_all_iff]; intro p
  by_cases hp : (⟨(p.1 : ℝ) / 2 ^ n, (p.2 : ℝ) / 2 ^ n⟩ : ℂ) ∈ Hbar
  · have hpx : (⟨(p.1 : ℝ) / 2 ^ n, (p.2 : ℝ) / 2 ^ n⟩ : ℂ) + (x : ℂ) ∈ Hbar := by
      have h0 : (0 : ℝ) ≤ (⟨(p.1 : ℝ) / 2 ^ n, (p.2 : ℝ) / 2 ^ n⟩ : ℂ).im := hp
      show (0 : ℝ) ≤ _; simpa using h0
    filter_upwards [hG.raw _ hpx _ (radius_pos k)] with ω₀ h _
    show Xf ω₀ ((foldedCircle _ _).map (· + (x : ℂ))) = _
    rw [Thm18Asm.ExactCl.foldedCircle_map_add x]
    exact h.symm
  · exact ae_of_all _ fun _ h => absurd h hp

theorem rawShift_dyadic {yt : FieldSample} {G : ℂ × ℝ → ℝ} {x : ℝ} (h : RawShift yt G x)
    (n k : ℕ) (z : ℂ) (hz : z ∈ Hbar) :
    yt (foldedCircle (dyadicRoundC n z) (radius k)) = G (dyadicRoundC n z + (x : ℂ), radius k) :=
  h n k (⌊(2 : ℝ) ^ n * z.re⌋, ⌊(2 : ℝ) ^ n * z.im⌋) (CircleCont.dyadicRoundC_mem_Hbar hz n)

/-- **Coupled data at a fixed point** (law transfer from the local coupling). -/
theorem ae_coupled_data {D : Set ℂ} {c d : ℝ} (hgeo : K3.Prop16Geometry D c d) {Ω : Type}
    [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P] {X : Ω → FieldSample}
    (hX : IsMixedGFF D (realSet (Icc c d)) X P) {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) (x : ℝ)
    {ψ : ℂ → ℂ} (hψd : DifferentiableOn ℂ ψ H) (hψi : InjOn ψ H) (hψH : MapsTo ψ H H)
    (hψ0 : ∀ z ∈ H, deriv ψ z ≠ 0) :
    ∀ᵐ ω ∂P, ∃ (xf yt : FieldSample) (G : ℂ × ℝ → ℝ) (φ : ℂ → ℝ), IsRegularWith xf G ∧
      ChartGood γ ψ yt ∧ RawShift yt G x ∧ ContinuousOn φ D ∧
      Prop16Area.G.CircAgree D (X ω) (xf + ofFun φ) := by
  have hcd : c < d := hgeo.2.2.2.2.1
  obtain ⟨W, hWo, hWV⟩ := locGood_exists_open hgeo le_rfl le_rfl (a := c) (b := d)
  obtain ⟨Ω₀, _, _, P₀, Y, Xf, hP₀, hY, hXf, hag⟩ :=
    prop16MixedFreeLocCoupling_mm D c d c d hgeo hcd le_rfl le_rfl
  obtain ⟨G, hG⟩ := WedgeTK.exists_isRegVersion hXf
  have hXt : IsFreeGFFModConstH (fun ω₀ (μ : Measure ℂ) => Xf ω₀ (μ.map (· + (x : ℂ)))) P₀ :=
    S5.FieldLaw.Raw.isFreeGFFModConstH_translate hXf x
  have hS : ∀ᵐ ω₀ ∂P₀, ω₀ ∈ {ω₀ | ChartGood γ ψ (fun μ => Xf ω₀ (μ.map (· + (x : ℂ)))) ∧
      IsRegularWith (Xf ω₀) (G ω₀) ∧ RawShift (fun μ => Xf ω₀ (μ.map (· + (x : ℂ)))) (G ω₀) x ∧
      ∃ φ : ℂ → ℝ, ContinuousOn φ (D ∪ realSet (Ioo c d)) ∧
        Prop16Area.G.CircAgree (D ∪ realSet (Ioo c d)) (Y ω₀) (Xf ω₀ + ofFun φ)} := by
    filter_upwards [ae_chartGood hXt hγ hγ2 hψd hψi hψH hψ0, hG.reg, ae_rawShift hG x, hag]
      with ω₀ h1 h2 h3 h4 using ⟨h1, h2, h3, h4⟩
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

/-- **The Palm-shifted field, translated, is locally a shifted free sample plus a continuous
function.** -/
theorem circAgree_palm_translate {γ : ℝ} {D : Set ℂ} {c d x : ℝ}
    (hgeo : K3.Prop16Geometry D c d) (hxcd : x ∈ Ioo c d) {h0 : ℂ → ℝ}
    (hh0 : ContinuousOn h0 D) {Xω xf yt : FieldSample} {G : ℂ × ℝ → ℝ}
    (hreg : IsRegularWith xf G) (hraw : RawShift yt G x) {φ : ℂ → ℝ} (hφ : ContinuousOn φ D)
    (hag : Prop16Area.G.CircAgree D Xω (xf + ofFun φ)) :
    ∃ g : ℂ → ℝ, ContinuousOn g (zoomDomain D x) ∧
      Prop16Area.G.CircAgree (zoomDomain D x)
        (translate (ofFun h0 + (Xω + (γ / 2) • mixedGreenSample D (realSet (Icc c d)) x))
          (x : ℂ)) (yt + ofFun g) := by
  classical
  have hDo : IsOpen D := hgeo.1
  have hψPc : ContinuousOn (palmPsi D (realSet (Icc c d)) x) D := continuousOn_palmPsi hgeo hxcd
  have hPD : Prop16Area.G.CircAgree D (Xω + (γ / 2) • mixedGreenSample D (realSet (Icc c d)) x)
      (xf + ofFun fun z => φ z + (γ / 2) * palmPsi D (realSet (Icc c d)) x z) := by
    intro n k z hz hsub
    have hc := CircleCont.dyadicRoundC_mem_Hbar hz n
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    rw [hag n k z hz hsub, Pi.add_apply,
      mixedGreenSample_eq_ofFun_palmPsi hgeo hxcd hc (radius_pos k) hsub]
    simp only [ofFun]
    rw [integral_add (Prop16Area.G.integrable_fc_of_continuousOn hc (radius_pos k) (hφ.mono hsub))
      ((Prop16Area.G.integrable_fc_of_continuousOn hc (radius_pos k) (hψPc.mono hsub)).const_mul
        (γ / 2)), integral_const_mul]
    ring
  have hxD := circAgree_ofFun_add_open (hφ.add (continuousOn_const.mul hψPc)) hh0 hPD
  set Φ : ℂ → ℝ := fun z => (φ z + (γ / 2) * palmPsi D (realSet (Icc c d)) x z) + h0 z with hΦdef
  have hΦc : ContinuousOn Φ D := (hφ.add (continuousOn_const.mul hψPc)).add hh0
  set Φ' : ℂ → ℝ := D.piecewise Φ 0 with hΦ'def
  have hΦ'm : Measurable Φ' := hΦc.measurable_piecewise continuousOn_const hDo.measurableSet
  have hΦΦ' : EqOn Φ' Φ D := fun z hz => Set.piecewise_eq_of_mem _ _ _ hz
  have hΦ'c : ContinuousOn Φ' D := hΦc.congr hΦΦ'
  have hx'D : Prop16Area.G.CircAgree D
      (ofFun h0 + (Xω + (γ / 2) • mixedGreenSample D (realSet (Icc c d)) x)) (xf + ofFun Φ') := by
    intro n k z hz hsub
    rw [hxD n k z hz hsub]
    simp only [Pi.add_apply, ofFun]
    congr 1
    refine integral_congr_ae ?_
    filter_upwards [G1Side.ae_fc_mem_closedBall (CircleCont.dyadicRoundC_mem_Hbar hz n)
      (radius_pos k).le, RegClosure.fc_ae_mem_Hbar _ _] with u h1 h2
    exact (hΦΦ' (hsub ⟨h1, h2⟩)).symm
  refine ⟨fun u => Φ' (u + (x : ℂ)), hΦ'c.comp (continuous_id.add continuous_const).continuousOn
    fun u hu => hu, ?_⟩
  exact circAgree_translate hDo hreg hΦ'c hΦ'm hx'D x (rawShift_dyadic hraw)

/-- **`Prop16LitExAFixStmt`, proved.** -/
theorem prop16LitExAFixStmt_proved : Prop16LitExAFixStmt := by
  intro γ D c d a b h0 Ω _ P X hdat ψ r₀ hfam C x hx
  obtain ⟨hγ, hγ2, hgeo, -, hca, hbd, hh0, hP, hX, -, -⟩ := hdat
  obtain ⟨hψm, -, hch⟩ := hfam
  have hxcd : x ∈ Ioo c d := ⟨lt_of_le_of_lt hca hx.1, lt_of_lt_of_le hx.2 hbd⟩
  obtain ⟨hψd, hψi, hψim, -, -⟩ := hch x hx
  have hψxm : Measurable (ψ x) := hψm.comp (measurable_const.prodMk measurable_id)
  have hDo : IsOpen D := hgeo.1
  have hDH : D ⊆ H := hgeo.2.2.2.1
  have hZo : IsOpen (zoomDomain D x) := hDo.preimage (continuous_id.add continuous_const)
  have hZH : zoomDomain D x ⊆ H := fun z hz => by
    have h1 : (0 : ℝ) < (z + (x : ℂ)).im := hDH hz
    show 0 < z.im
    simpa using h1
  have hψZ : MapsTo (ψ x) H (zoomDomain D x) := fun w hw => hψim ▸ mem_image_of_mem (ψ x) hw
  have hψH : MapsTo (ψ x) H H := hψZ.mono_right hZH
  have hψ0 : ∀ z ∈ H, deriv (ψ x) z ≠ 0 := fun z hz =>
    CA.deriv_ne_zero_of_injOn isOpen_H hψd hψi hz
  haveI := hP
  filter_upwards [ae_coupled_data hgeo hX hγ hγ2 x hψd hψi hψH hψ0] with ω hω
  obtain ⟨xf, yt, G, φ, hreg, hcg, hraw, hφ, hag⟩ := hω
  obtain ⟨g, hg, hagT⟩ := circAgree_palm_translate (γ := γ) hgeo hxcd
    (hh0.mono subset_union_left) hreg hraw hφ hag
  exact goodA_zoomLit_of_agree hcg hψxm hψd hψ0 hZo hZH hg hagT
    (hψZ.mono_left inter_subset_right)

end ExA
end Prop16Lit
end QuantumZipper
