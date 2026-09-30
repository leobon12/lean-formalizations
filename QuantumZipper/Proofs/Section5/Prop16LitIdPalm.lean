import QuantumZipper.Proofs.Section5.Prop16LitIdEvent
import QuantumZipper.Proofs.Section5.Prop16LitFixCovProof

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# Proposition 1.6, literal form: the identity event at a fixed point (COORD-CHANGE, D98)

* `Prop16Lit.eventually_integral_eq_of_circAgree`, `idGood_congr`: the event `IdGood` only reads
  the fields near the chart domain and its image;
* `Prop16Lit.idGood_of_limits`: from the two local vague limits and the chart identity
  (clause (1) of `Prop16LitCovStmt`), the event holds;
* `Prop16Lit.ae_idGood_palm`: at a fixed point, a.s. for the Palm-shifted field (the chart
  identity `prop16LitFixCov1Stmt_proved`, the chart zoom limit from `prop16LitExAFixStmt_proved`,
  the straight zoom limit from the local coupling with a good free sample).
Own bookkeeping.
-/

noncomputable section

open MeasureTheory Filter Set Metric
open scoped Topology ENNReal

namespace QuantumZipper
namespace Prop16Lit

open ExA Prop16Asm CoordChangeArea

variable {D : Set ℂ} {a b : ℝ} {ψ : ℝ → ℂ → ℂ} {r₀ : ℝ → ℝ}

/-- Test integrals only see the field near the support, eventually. -/
theorem eventually_integral_eq_of_circAgree {γ : ℝ} {W : Set ℂ} (hWo : IsOpen W) (hWH : W ⊆ H)
    {Z Z' : FieldSample} (h : Prop16Area.G.CircAgree W Z Z') {T : ℂ → ℝ}
    (hTs : HasCompactSupport T) (hTW : tsupport T ⊆ W) :
    ∀ᶠ k in atTop, ∫ z, T z ∂areaApprox γ Z k = ∫ z, T z ∂areaApprox γ Z' k := by
  filter_upwards [areaApprox_congr_of_circAgree hWo hWH h hTs hTW] with k hk
  rw [E6.integral_areaApprox_eq, E6.integral_areaApprox_eq]
  refine integral_congr_ae (ae_of_all _ fun t => ?_)
  by_cases ht : t ∈ tsupport T
  · simp only [E6.areaDensK, hk t ht]
  · simp only [image_eq_zero_of_notMem_tsupport ht, mul_zero]

/-- The pulled-back test functions are test functions in the image of the chart domain. -/
theorem pullT_test (hfam : LitFamily D a b ψ r₀) (hDH : D ⊆ H) {x : ℝ} (hx : x ∈ Ioo a b)
    {g : ℂ → ℝ} (hg : g ∈ famF) (n : ℕ) :
    Continuous (pullT ψ a b r₀ (FnT r₀ g n) x) ∧ HasCompactSupport (pullT ψ a b r₀ (FnT r₀ g n) x) ∧
      tsupport (pullT ψ a b r₀ (FnT r₀ g n) x) ⊆ ψ x '' (ball 0 (r₀ x) ∩ H) := by
  obtain ⟨hc, hs, hU⟩ := FnT_test (r₀ := r₀) hg n x
  have hsub := tsupport_pullT_subset hfam hx hs hU
  have hcont : ContinuousOn (ψ x) (tsupport (FnT r₀ g n x)) :=
    (hfam.2.2 x hx).1.continuousOn.mono (hU.trans inter_subset_right)
  exact ⟨continuous_pullT hfam hDH hx hc hs hU,
    (hs.isCompact.image_of_continuousOn hcont).of_isClosed_subset (isClosed_tsupport _) hsub,
    hsub.trans (image_mono hU)⟩

theorem chart_image_subset (hfam : LitFamily D a b ψ r₀) {x : ℝ} (hx : x ∈ Ioo a b) :
    ψ x '' (ball 0 (r₀ x) ∩ H) ⊆ zoomDomain D x := by
  obtain ⟨-, -, himg, -⟩ := hfam.2.2 x hx
  rintro _ ⟨u, hu, rfl⟩
  exact himg ▸ mem_image_of_mem (ψ x) hu.2

/-- **Locality of the identity event.** -/
theorem idGood_congr {γ : ℝ} (hfam : LitFamily D a b ψ r₀) (hDo : IsOpen D) (hDH : D ⊆ H)
    {x : ℝ} (hx : x ∈ Ioo a b) {Z Z' Y Y' : FieldSample}
    (hZ : Prop16Area.G.CircAgree (ball 0 (r₀ x) ∩ H) Z Z')
    (hY : Prop16Area.G.CircAgree (zoomDomain D x) Y Y') (h : IdGood ψ a b r₀ γ Z Y x) :
    IdGood ψ a b r₀ γ Z' Y' x := by
  have hVo : IsOpen (zoomDomain D x) := hDo.preimage (continuous_id.add continuous_const)
  intro n g hg
  obtain ⟨l, h1, h2⟩ := h n g hg
  obtain ⟨-, hs, hU⟩ := FnT_test (r₀ := r₀) hg n x
  obtain ⟨-, hs', hV⟩ := pullT_test hfam hDH hx hg n
  refine ⟨l, h1.congr' ?_, h2.congr' ?_⟩
  · exact eventually_integral_eq_of_circAgree (isOpen_ball.inter isOpen_H) inter_subset_right
      hZ hs hU
  · exact eventually_integral_eq_of_circAgree hVo (zoomDomain_subset_H hDH x) hY hs'
      (hV.trans (chart_image_subset hfam hx))

/-- **The event from the two limits and the chart identity.** -/
theorem idGood_of_limits {γ : ℝ} (hfam : LitFamily D a b ψ r₀) (hDo : IsOpen D) (hDH : D ⊆ H)
    {x : ℝ} (hx : x ∈ Ioo a b) {Z Y : FieldSample} {μZ μY : Measure ℂ}
    (hμZ : IsVagueLimitOn (ball 0 (r₀ x) ∩ H) (areaApprox γ Z) μZ)
    (hμY : IsVagueLimitOn (zoomDomain D x) (areaApprox γ Y) μY)
    (hid : μZ.map (ψ x) = μY.restrict (ψ x '' (ball 0 (r₀ x) ∩ H))) :
    IdGood ψ a b r₀ γ Z Y x := by
  have hψm : Measurable (ψ x) := hfam.1.comp (measurable_const.prodMk measurable_id)
  intro n g hg
  obtain ⟨hc, hs, hU⟩ := FnT_test (r₀ := r₀) hg n x
  obtain ⟨hc', hs', hV⟩ := pullT_test hfam hDH hx hg n
  refine ⟨_, hμZ.2.2 _ hc hs hU, ?_⟩
  have ht := hμY.2.2 _ hc' hs' (hV.trans (chart_image_subset hfam hx))
  convert ht using 2
  -- `∫ F dμZ = ∫ F ∘ ψ⁻¹ dμY`
  have hImeas : MeasurableSet (ψ x '' (ball 0 (r₀ x) ∩ H)) := by
    have e : ψ x '' (ball 0 (r₀ x) ∩ H) =
        (fun w : ℂ => (x, w)) ⁻¹' range (chartPair ψ a b r₀) := by
      ext w; exact (mem_range_chartPair_iff hx).symm
    rw [e]
    exact (measurableEmbedding_chartPair hfam).measurableSet_range.preimage
      (measurable_const.prodMk measurable_id)
  rw [← setIntegral_eq_integral_of_forall_compl_eq_zero (s := ψ x '' (ball 0 (r₀ x) ∩ H))
    fun w hw => image_eq_zero_of_notMem_tsupport fun h => hw (hV h)]
  rw [← hid, integral_map hψm.aemeasurable hc'.aestronglyMeasurable]
  refine integral_congr_ae ?_
  have hc0 : μZ (ball 0 (r₀ x) ∩ H)ᶜ = 0 := hμZ.1
  filter_upwards [measure_eq_zero_iff_ae_notMem.1 hc0] with u hu
  have hu' : u ∈ ball 0 (r₀ x) ∩ H := by simpa using hu
  unfold pullT
  rw [if_pos ((mem_range_chartPair_iff hx).2 ⟨u, hu', rfl⟩), chartInv_apply hfam hx hu']

namespace ExA
/-- **Coupled data at a fixed point, with a good translated free sample.** -/
theorem ae_coupled_good {D : Set ℂ} {c d : ℝ} (hgeo : K3.Prop16Geometry D c d) {Ω : Type}
    [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P] {X : Ω → FieldSample}
    (hX : IsMixedGFF D (realSet (Icc c d)) X P) {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) (x : ℝ) :
    ∀ᵐ ω ∂P, ∃ (xf yt : FieldSample) (G : ℂ × ℝ → ℝ) (φ : ℂ → ℝ), IsRegularWith xf G ∧
      IsLQGGood γ yt ∧ RawShift yt G x ∧ ContinuousOn φ D ∧
      Prop16Area.G.CircAgree D (X ω) (xf + ofFun φ) := by
  have hcd : c < d := hgeo.2.2.2.2.1
  obtain ⟨W, hWo, hWV⟩ := locGood_exists_open hgeo le_rfl le_rfl (a := c) (b := d)
  obtain ⟨Ω₀, _, _, P₀, Y, Xf, hP₀, hY, hXf, hag⟩ :=
    prop16MixedFreeLocCoupling_mm D c d c d hgeo hcd le_rfl le_rfl
  obtain ⟨G, hG⟩ := WedgeTK.exists_isRegVersion hXf
  have hXt : IsFreeGFFModConstH (fun ω₀ (μ : Measure ℂ) => Xf ω₀ (μ.map (· + (x : ℂ)))) P₀ :=
    S5.FieldLaw.Raw.isFreeGFFModConstH_translate hXf x
  have hS : ∀ᵐ ω₀ ∂P₀, ω₀ ∈ {ω₀ | IsLQGGood γ (fun μ => Xf ω₀ (μ.map (· + (x : ℂ)))) ∧
      IsRegularWith (Xf ω₀) (G ω₀) ∧ RawShift (fun μ => Xf ω₀ (μ.map (· + (x : ℂ)))) (G ω₀) x ∧
      ∃ φ : ℂ → ℝ, ContinuousOn φ (D ∪ realSet (Ioo c d)) ∧
        Prop16Area.G.CircAgree (D ∪ realSet (Ioo c d)) (Y ω₀) (Xf ω₀ + ofFun φ)} := by
    filter_upwards [AreaOffsets.ae_isLQGGood hXt hγ hγ2, hG.reg, ae_rawShift hG x, hag]
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

end ExA

/-- **The identity event at a fixed point, a.s. for the Palm-shifted field.** -/
theorem ae_idGood_palm {γ : ℝ} {c d : ℝ} {h0 : ℂ → ℝ} {Ω : Type} [MeasurableSpace Ω]
    {P : Measure Ω} {X : Ω → FieldSample} (hdat : Prop16Data γ D c d a b h0 P X)
    (hfam : LitFamily D a b ψ r₀) (C x : ℝ) (hx : x ∈ Ioo a b) :
    ∀ᵐ ω ∂P, IdGood ψ a b r₀ γ
      (zoomFieldLit γ C (ofFun h0 + palmMixedField γ D (realSet (Icc c d)) X x ω) x (ψ x))
      (zoomField γ C (ofFun h0 + palmMixedField γ D (realSet (Icc c d)) X x ω) x) x := by
  obtain ⟨hγ, hγ2, hgeo, -, hca, hbd, hh0, hP, hX, -, -⟩ := id hdat
  have hxcd : x ∈ Ioo c d := ⟨lt_of_le_of_lt hca hx.1, lt_of_lt_of_le hx.2 hbd⟩
  have hDo : IsOpen D := hgeo.1
  have hDH : D ⊆ H := hgeo.2.2.2.1
  have hVo : IsOpen (zoomDomain D x) := hDo.preimage (continuous_id.add continuous_const)
  have hVH : zoomDomain D x ⊆ H := zoomDomain_subset_H hDH x
  haveI := hP
  filter_upwards [prop16LitExAFixStmt_proved γ D c d a b h0 P X hdat ψ r₀ hfam C x hx,
    prop16LitFixCov1Stmt_proved γ D c d a b h0 P X hdat ψ r₀ hfam x hx,
    ae_coupled_good hgeo hX hγ hγ2 x] with ω hA hid hω
  obtain ⟨xf, yt, G, φ, hreg, hgood, hraw, hφ, hag⟩ := hω
  obtain ⟨g, hg, hagT⟩ := circAgree_palm_translate (γ := γ) hgeo hxcd
    (hh0.mono subset_union_left) hreg hraw hφ hag
  obtain ⟨μZ, hμZ⟩ := exists_vague_of_goodA hA
  have hagC := CoordChangeArea.circAgree_addConst hg hagT (C / γ)
  obtain ⟨μY, hμY⟩ := Prop16Area.G.exists_limit_of_agree hVo hgood
    ((hg.add continuousOn_const).mono inter_subset_left) hagC hVo hVH subset_rfl
  have hμY' : IsVagueLimitOn (zoomDomain D x)
      (areaApprox γ (zoomField γ C (ofFun h0 + palmMixedField γ D (realSet (Icc c d)) X x ω) x))
      μY := hμY
  have hidC := hid C
  rw [LocalRule.qAreaMeasureOn_eq (isOpen_ball.inter isOpen_H) hμZ,
    LocalRule.qAreaMeasureOn_eq hVo hμY'] at hidC
  exact idGood_of_limits hfam hDo hDH hx hμZ hμY' hidC

end Prop16Lit
end QuantumZipper
