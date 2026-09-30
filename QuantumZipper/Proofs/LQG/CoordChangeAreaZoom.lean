import QuantumZipper.Proofs.LQG.CoordChangeAreaMixed
import QuantumZipper.Proofs.Thm18.ExactClG1

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# Coordinate change of the area measure: translations and additive constants (COORD-CHANGE, D98)

Deterministic bookkeeping for reading the local coordinate-change theorems through the zoom of
Proposition 1.6 (`h ↦ h(· + x) + C/γ`):

* `CoordChangeArea.tendsto_fc_of_regular`, `evalReg_fc_of_circAgree_reg`: for `h = y + Φ` on the
  dyadic circles in `W` (`y` regular with witness `F`, `Φ` continuous on `W`), every folded
  circle carried by `W` has `⟨h, fc(w,ρ)⟩ = F(w,ρ) + ∫ Φ dfc(w,ρ)`;
* `CoordChangeArea.circAgree_translate`: the real translate `h(· + x)` then agrees on the dyadic
  circles of `W − x` with `y' + Φ(· + x)`, for any `y'` whose dyadic circle values are `F(· + x)`;
* `CoordChangeArea.circAgree_addConst`: adding a constant on both sides;
* `CoordChangeArea.isVagueLimitOn_congr_avgReg`: local vague limits only see the circle
  averages on compact subsets, eventually.

Own elementary bookkeeping (the locality of the regularization, FOUNDATIONS §0.1).
-/

noncomputable section

open MeasureTheory Filter Set Function Metric
open scoped Topology ENNReal

namespace QuantumZipper
namespace CoordChangeArea

open SWCore GoodSample G1Side

/-- The dyadic smoothings of a regular sample converge on every folded circle in `Hbar`. -/
theorem tendsto_fc_of_regular {y : FieldSample} {F : ℂ × ℝ → ℝ} (hF : IsRegularWith y F)
    {w : ℂ} (hw : w ∈ Hbar) {ρ : ℝ} (hρ : 0 < ρ) :
    Tendsto (fun j => ∫ u, avgReg y j u ∂foldedCircle w ρ) atTop (𝓝 (F (w, ρ))) := by
  have e : ∀ k : ℕ, ∫ u, avgReg y k u ∂foldedCircle w ρ = ∫ u, F (u, radius k) ∂foldedCircle w ρ :=
    fun k => integral_congr_ae ((RegClosure.fc_ae_mem_Hbar w ρ).mono fun u hu => hF.avgReg_eq k hu)
  simp_rw [e]
  exact (hF.2.2.tendsto_at (a := (w, ρ)) ⟨hw, hρ⟩).comp RegClosure.tendsto_radius_nhdsGT

/-- **Circle values of a field that is locally a regular sample plus a continuous function.** -/
theorem evalReg_fc_of_circAgree_reg {W : Set ℂ} (hWo : IsOpen W) {h y : FieldSample}
    {F : ℂ × ℝ → ℝ} (hF : IsRegularWith y F) {Φ : ℂ → ℝ} (hΦ : ContinuousOn Φ W)
    (hag : Prop16Area.G.CircAgree W h (y + ofFun Φ)) {w : ℂ} (hw : w ∈ Hbar) {ρ : ℝ}
    (hρ : 0 < ρ) (hsub : closedBall w ρ ∩ Hbar ⊆ W) :
    evalReg h (foldedCircle w ρ) = F (w, ρ) + ∫ u, Φ u ∂foldedCircle w ρ := by
  have hK : IsCompact (closedBall w ρ ∩ Hbar) := (isCompact_closedBall _ _).inter_right isClosed_Hbar
  have hν : ∀ᵐ u ∂foldedCircle w ρ, u ∈ closedBall w ρ ∩ Hbar := by
    filter_upwards [G1Side.ae_fc_mem_closedBall hw hρ.le, RegClosure.fc_ae_mem_Hbar w ρ]
      with u h1 h2 using ⟨h1, h2⟩
  rw [evalReg_eq_add_of_circAgree hWo hF hΦ hag hK hsub inter_subset_right hν
    (tendsto_fc_of_regular hF hw hρ), hF.evalReg_fc_of_mem hw hρ]

/-- **Real translates of a locally regular field.** -/
theorem circAgree_translate {W : Set ℂ} (hWo : IsOpen W) {h y : FieldSample}
    {F : ℂ × ℝ → ℝ} (hF : IsRegularWith y F) {Φ : ℂ → ℝ} (hΦ : ContinuousOn Φ W)
    (hΦm : Measurable Φ) (hag : Prop16Area.G.CircAgree W h (y + ofFun Φ)) (x : ℝ)
    {y' : FieldSample}
    (hy' : ∀ (n k : ℕ) (z : ℂ), z ∈ Hbar →
      y' (foldedCircle (dyadicRoundC n z) (radius k)) =
        F (dyadicRoundC n z + (x : ℂ), radius k)) :
    Prop16Area.G.CircAgree ((fun z => z + (x : ℂ)) ⁻¹' W) (translate h (x : ℂ))
      (y' + ofFun fun u => Φ (u + (x : ℂ))) := by
  intro n k z hz hsub
  set d := dyadicRoundC n z with hd
  have hdH : d ∈ Hbar := CircleCont.dyadicRoundC_mem_Hbar hz n
  have hdxH : d + (x : ℂ) ∈ Hbar := by
    have h0 : (0 : ℝ) ≤ d.im := hdH
    show (0 : ℝ) ≤ (d + (x : ℂ)).im; simpa using h0
  have hsub' : closedBall (d + (x : ℂ)) (radius k) ∩ Hbar ⊆ W := by
    rintro u ⟨hu1, hu2⟩
    have : u - (x : ℂ) ∈ closedBall d (radius k) ∩ Hbar := by
      refine ⟨?_, ?_⟩
      · rw [mem_closedBall, dist_eq_norm] at hu1 ⊢
        have e : u - (x : ℂ) - d = u - (d + (x : ℂ)) := by ring
        rwa [e]
      · have h0 : (0 : ℝ) ≤ u.im := hu2
        show (0 : ℝ) ≤ (u - (x : ℂ)).im; simpa using h0
    have h2 := hsub this
    simpa using h2
  show evalReg h ((foldedCircle d (radius k)).map (· + (x : ℂ))) =
    y' (foldedCircle d (radius k)) + ∫ u, Φ (u + (x : ℂ)) ∂foldedCircle d (radius k)
  rw [Thm18Asm.ExactCl.foldedCircle_map_add x,
    evalReg_fc_of_circAgree_reg hWo hF hΦ hag hdxH (radius_pos k) hsub', hy' n k z hz]
  congr 1
  rw [← Thm18Asm.ExactCl.foldedCircle_map_add x, integral_map (measurable_add_const _).aemeasurable
    hΦm.aestronglyMeasurable]

/-- Adding a constant on both sides of a local agreement. -/
theorem circAgree_addConst {W : Set ℂ} {x y : FieldSample} {Φ : ℂ → ℝ}
    (hΦ : ContinuousOn Φ W) (hag : Prop16Area.G.CircAgree W x (y + ofFun Φ)) (c : ℝ) :
    Prop16Area.G.CircAgree W (addConst x c) (y + ofFun fun u => Φ u + c) := by
  intro n k z hz hsub
  simp only [addConst, Pi.add_apply]
  rw [hag n k z hz hsub, Pi.add_apply]
  simp only [ofFun]
  have hi := Prop16Area.G.integrable_fc_of_continuousOn (CircleCont.dyadicRoundC_mem_Hbar hz n)
    (radius_pos k) (hΦ.mono hsub)
  rw [integral_add hi (integrable_const c), integral_const, probReal_univ, one_smul,
    measure_univ, ENNReal.toReal_one, mul_one]
  ring

/-- **Local vague limits only see the circle averages on compacts, eventually.** -/
theorem isVagueLimitOn_congr_avgReg {γ : ℝ} {U : Set ℂ} {x x' : FieldSample}
    (h : ∀ K, IsCompact K → K ⊆ U → ∀ᶠ k in atTop, ∀ z ∈ K, avgReg x k z = avgReg x' k z)
    {μ : Measure ℂ} (hμ : IsVagueLimitOn U (areaApprox γ x) μ) :
    IsVagueLimitOn U (areaApprox γ x') μ := by
  refine ⟨hμ.1, hμ.2.1, fun f hf hfc hfU => (hμ.2.2 f hf hfc hfU).congr' ?_⟩
  filter_upwards [h _ hfc hfU] with k hk
  rw [E6.integral_areaApprox_eq, E6.integral_areaApprox_eq]
  refine integral_congr_ae (ae_of_all _ fun t => ?_)
  by_cases ht : t ∈ tsupport f
  · simp only [E6.areaDensK, hk t ht]
  · simp [image_eq_zero_of_notMem_tsupport ht]

/-- A function continuous on a compact carrier of a finite measure is integrable. -/
theorem integrable_of_continuousOn_carrier {g : ℂ → ℝ} {K : Set ℂ} (hK : IsCompact K)
    (hg : ContinuousOn g K) {ν : Measure ℂ} [IsFiniteMeasure ν] (hν : ∀ᵐ w ∂ν, w ∈ K) :
    Integrable g ν := by
  have hi := hg.integrableOn_compact (μ := ν) hK
  rwa [IntegrableOn, Measure.restrict_eq_self_of_ae_mem hν] at hi

set_option maxHeartbeats 800000 in
/-- **The additive constant commutes with the coordinate change**, at the level of local area
limits: `(z + c) ∘ ψ + Q log|ψ'|` and `(z ∘ ψ + Q log|ψ'|) + c` have the same local limits on
`U`, for `z` locally a regular sample `y` plus a continuous function, with regular pushed
averages of `y` along `ψ`. -/
theorem isVagueLimitOn_addConst_coordChange {γ : ℝ} {z y : FieldSample} {F : ℂ × ℝ → ℝ}
    (hF : IsRegularWith y F) {ψ : ℂ → ℂ} (hψm : Measurable ψ) (hψd : DifferentiableOn ℂ ψ H)
    (hpush : PushRegular y ψ) {W : Set ℂ} (hWo : IsOpen W) {g : ℂ → ℝ} (hg : ContinuousOn g W)
    (hag : Prop16Area.G.CircAgree W z (y + ofFun g)) {U : Set ℂ} (hUo : IsOpen U) (hUH : U ⊆ H)
    (hUW : MapsTo ψ U W) (hUHb : MapsTo ψ U Hbar) (Q c : ℝ) {μ : Measure ℂ}
    (hμ : IsVagueLimitOn U (areaApprox γ (coordChange (addConst z c) ψ Q)) μ) :
    IsVagueLimitOn U (areaApprox γ (addConst (coordChange z ψ Q) c)) μ := by
  have hagc := circAgree_addConst hg hag c
  have hgc : ContinuousOn (fun u => g u + c) W := hg.add continuousOn_const
  refine isVagueLimitOn_congr_avgReg (fun K hK hKU => ?_) hμ
  obtain ⟨ε₀, hε₀, hε₀U⟩ := hK.exists_cthickening_subset_open hUo hKU
  set K₂ := cthickening ε₀ K with hK₂def
  have hK₂ : IsCompact K₂ := hK.cthickening
  have hK₂H : K₂ ⊆ H := hε₀U.trans hUH
  obtain ⟨k₀, hk₀⟩ := hpush K₂ hK₂ hK₂H
  set Kψ := ψ '' K₂ with hKψdef
  have hKψ : IsCompact Kψ := hK₂.image_of_continuousOn (hψd.continuousOn.mono hK₂H)
  have hKψW : Kψ ⊆ W := image_subset_iff.2 (hUW.mono_left hε₀U)
  have hKψH : Kψ ⊆ Hbar := image_subset_iff.2 (hUHb.mono_left hε₀U)
  have hrad : ∀ᶠ k in atTop, k₀ ≤ k ∧ 2 * radius k ≤ ε₀ :=
    (eventually_ge_atTop k₀).and ((RegClosure.tendsto_radius_nhdsGT.mono_right
      nhdsWithin_le_nhds).eventually (ge_mem_nhds (by linarith : (0 : ℝ) < ε₀ / 2)) |>.mono
      fun k hk => by linarith)
  filter_upwards [hrad] with k hk w hw
  refine ASep.avgReg_congr_of_eventually ?_
  filter_upwards [a7_dyadic_small (z := w) (radius_pos k)] with n hn
  set dn := dyadicRoundC n w with hdn
  have hball : closedBall dn (radius k) ⊆ K₂ := by
    refine hn.1.trans ?_
    intro u hu
    exact mem_cthickening_of_dist_le u w ε₀ K hw ((mem_closedBall.1 hu).trans hk.2)
  have hdK : dn ∈ K₂ := hball (mem_closedBall_self (radius_pos k).le)
  have hdH : dn ∈ Hbar := H_subset_Hbar (hK₂H hdK)
  set ν := (foldedCircle dn (radius k)).map ψ with hνdef
  haveI : IsProbabilityMeasure ν :=
    (Measure.isProbabilityMeasure_map_iff hψm.aemeasurable).2 inferInstance
  have hν : ∀ᵐ v ∂ν, v ∈ Kψ :=
    ae_map_fc_mem hψm hdH (radius_pos k).le hKψ.isClosed.measurableSet
      fun u hu => mem_image_of_mem ψ (hball hu)
  have hL := (hk₀ k hk.1).1 dn hdK
  have e1 := evalReg_eq_add_of_circAgree hWo hF hgc hagc hKψ hKψW hKψH hν hL
  have e2 := evalReg_eq_add_of_circAgree hWo hF hg hag hKψ hKψW hKψH hν hL
  have hgi : Integrable g ν := integrable_of_continuousOn_carrier hKψ (hg.mono hKψW) hν
  have e3 : ∫ v, (g v + c) ∂ν = ∫ v, g v ∂ν + c := by
    rw [integral_add hgi (integrable_const c), integral_const, probReal_univ, one_smul]
  simp only [coordChange, addConst]
  rw [e1, e2, e3, measure_univ, ENNReal.toReal_one, mul_one]
  ring

end CoordChangeArea
end QuantumZipper
