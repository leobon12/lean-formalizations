/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.LocalExtNRefSide
import InteractingSLE.Spec.Sec7.LocalExtNRef

/-!
# Aux. lemma 54, (Loc) after the stop: `ExtPostLocalStatement κ`

Packet PROVE-LOCEXT-N. On a record extension `E = Q ⊗ κ₀(record)` of a stopped seed coupling by a time-adapted reference,
after the reference's capped local stop (`D₀ = A₀ ∩ {Ŝ ≤ s}`, `A₀ ∈ 𝓖_s`, `C ∩ K̂_s = ∅`), the original centred field
`X = h − 𝔥₀` satisfies the projection identity at `U ⊆ C`. Write `X = Z + Y` (Markov decomposition at `U`).

1. On `D₀` the hull avoids `C`, so the projections agree: `Z(p.1) = Ẑ(p.2)` (`ae_markov_eq_of_lapTest_eq`, an `L²`
   argument with common Dirichlet approximations), and the records of `Y` and `Ŷ` agree test function by test function.
2. `∫_{snd⁻¹ D₀} F(p.1) dE = ∫ F · κ₀(rec)(D₀) · 1_{C ∩ K_S = ∅} dQ` (compProd), and `κ₀(rec)(D₀)` is a function of
   `(Z, record of Y)`.
3. Q side (history-marked locality at `S`, `indep_markSigmaQ`): `Z ⫫ (Y(Ξ), record of Y)`, so `e^{iY(Ξ)}` may be replaced
   by its conditional expectation `ã(record of Y)` (`integral_mul_eq_of_indepFun_condExp`).
4. Back on `E` and through the record (`map_eq_of_ae_coord`) to the reference, where `Ẑ ⫫ (Ŷ, 𝓖_s)`
   (`setIntegral_refRecord_gauss`): `∫_{snd⁻¹ D₀} e^{iX(χ)} dE = exp(−‖covVec_U χ‖²/2) · c` with `c` independent of
   `χ ∈ {−Δf/2π + Ξ, Ξ}`; `gaussFactor_lapTest_add` finishes.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology QuantumZipper TopologicalSpace
open scoped NNReal ENNReal RealInnerProductSpace

universe u

namespace InteractingSLE

namespace LocalExt

open Sec7 Sec4 LQGMetric LQGMetric.MarkovZB Coupling LocalSets Ito QuantumZipper.K3 QuantumZipper.Thm11Asm
open SupercriticalConformalCovariance.GM24 (smoothDist)

section Agree

variable {Ω Ωr : Type*} [MeasurableSpace Ω] [MeasurableSpace Ωr] {Q : Measure Ω} {Pr : Measure Ωr}
  {E : Measure (Ω × Ωr)}

/-- **Markov projections agree where the fields agree on `U`**: if `X₁(p.1)` and `X₂(p.2)` have the same Dirichlet
pairings on `D`, the projections onto `H(U)` agree almost surely on `D` (common `L²` approximations). -/
theorem ae_markov_eq_of_lapTest_eq (hfst : E.map Prod.fst = Q) (hsnd : E.map Prod.snd = Pr)
    {X₁ : Ω → DistOn upperHalfPlaneOpens} {X₂ : Ωr → DistOn upperHalfPlaneOpens} {U : Opens ℂ}
    (hU : U ≤ upperHalfPlaneOpens) {G : DistOn upperHalfPlaneOpens → DistOn upperHalfPlaneOpens}
    (hX₁ : Measurable X₁) (hX₂ : Measurable X₂) (hG : Measurable G)
    (hd₁ : GFF.IsMarkovDecomposition U upperHalfPlaneOpens X₁ (fun ω => G (X₁ ω)) Q)
    (hd₂ : GFF.IsMarkovDecomposition U upperHalfPlaneOpens X₂ (fun ω => G (X₂ ω)) Pr) {D : Set (Ω × Ωr)}
    (hD : MeasurableSet D) (hagree : ∀ f : zsSub (U : Set ℂ), ∀ᵐ p ∂E, p ∈ D →
      X₁ p.1 (lapTest U f) = X₂ p.2 (lapTest U f)) (χ : TestOn upperHalfPlaneOpens) :
    ∀ᵐ p ∂E, p ∈ D → G (X₁ p.1) χ = G (X₂ p.2) χ := by
  obtain ⟨f, hfg, -⟩ := exists_tendsto_integral_sq_of_isMarkovDecomposition hU hd₁ χ
  set u₁ : ℕ → Ω → ℝ := fun n ω => G (X₁ ω) χ - X₁ ω (lapTest U (f n)) with hu₁
  set u₂ : ℕ → Ωr → ℝ := fun n ω => G (X₂ ω) χ - X₂ ω (lapTest U (f n)) with hu₂
  have hm₁ : ∀ n, MemLp (u₁ n) 2 Q := fun n => memLp_markov_sub_lapTest hU hd₁ χ (f n)
  have hm₂ : ∀ n, MemLp (u₂ n) 2 Pr := fun n => memLp_markov_sub_lapTest hU hd₂ χ (f n)
  have hi₁ : ∀ n, ∫ ω, (u₁ n ω) ^ 2 ∂Q = ‖covVec (U : Set ℂ) χ - gradFeat (U : Set ℂ) (f n).1‖ ^ 2 := fun n =>
    integral_sq_sub_lapTest_of_isMarkovDecomposition hU hd₁ χ (f n)
  have hi₂ : ∀ n, ∫ ω, (u₂ n ω) ^ 2 ∂Pr = ‖covVec (U : Set ℂ) χ - gradFeat (U : Set ℂ) (f n).1‖ ^ 2 := fun n =>
    integral_sq_sub_lapTest_of_isMarkovDecomposition hU hd₂ χ (f n)
  have hfstm : Measurable (Prod.fst : Ω × Ωr → Ω) := measurable_fst
  have hsndm : Measurable (Prod.snd : Ω × Ωr → Ωr) := measurable_snd
  -- the squared differences on `E`
  have hsq₁ : ∀ n, Integrable (fun p : Ω × Ωr => (u₁ n p.1) ^ 2) E := fun n => by
    have := (hm₁ n).integrable_sq
    rw [← hfst] at this
    exact this.comp_measurable hfstm
  have hsq₂ : ∀ n, Integrable (fun p : Ω × Ωr => (u₂ n p.2) ^ 2) E := fun n => by
    have := (hm₂ n).integrable_sq
    rw [← hsnd] at this
    exact this.comp_measurable hsndm
  have hE₁ : ∀ n, ∫ p, (u₁ n p.1) ^ 2 ∂E = ∫ ω, (u₁ n ω) ^ 2 ∂Q := fun n => by
    rw [← hfst, integral_map hfstm.aemeasurable (by rw [hfst]; exact (hm₁ n).integrable_sq.aestronglyMeasurable)]
  have hE₂ : ∀ n, ∫ p, (u₂ n p.2) ^ 2 ∂E = ∫ ω, (u₂ n ω) ^ 2 ∂Pr := fun n => by
    rw [← hsnd, integral_map hsndm.aemeasurable (by rw [hsnd]; exact (hm₂ n).integrable_sq.aestronglyMeasurable)]
  set d : Ω × Ωr → ℝ := fun p => G (X₁ p.1) χ - G (X₂ p.2) χ with hd_def
  have hdu : ∀ n, ∀ᵐ p ∂E, D.indicator (fun p => (d p) ^ 2) p ≤ 2 * (u₁ n p.1) ^ 2 + 2 * (u₂ n p.2) ^ 2 := by
    intro n
    filter_upwards [hagree (f n)] with p hp
    by_cases hpD : p ∈ D
    · rw [indicator_of_mem hpD]
      have e : d p = u₁ n p.1 - u₂ n p.2 := by
        simp only [hd_def, hu₁, hu₂, hp hpD]
        ring
      rw [e]
      nlinarith [sq_nonneg (u₁ n p.1 + u₂ n p.2)]
    · rw [indicator_of_notMem hpD]
      positivity
  have hdm : Measurable fun p : Ω × Ωr => D.indicator (fun p => (d p) ^ 2) p :=
    (((measurable_distOn_apply χ).comp (hG.comp (hX₁.comp hfstm))).sub
      ((measurable_distOn_apply χ).comp (hG.comp (hX₂.comp hsndm)))).pow_const 2 |>.indicator hD
  have hdint : Integrable (fun p => D.indicator (fun p => (d p) ^ 2) p) E :=
    Integrable.mono' (((hsq₁ 0).const_mul 2).add ((hsq₂ 0).const_mul 2)) hdm.aestronglyMeasurable
      (by filter_upwards [hdu 0] with p hp
          rw [Real.norm_eq_abs, abs_of_nonneg (by by_cases hpD : p ∈ D <;> simp [hpD, sq_nonneg])]
          exact hp)
  have hle : ∀ n, ∫ p, D.indicator (fun p => (d p) ^ 2) p ∂E ≤
      4 * ‖covVec (U : Set ℂ) χ - gradFeat (U : Set ℂ) (f n).1‖ ^ 2 := fun n => by
    calc _ ≤ ∫ p, (2 * (u₁ n p.1) ^ 2 + 2 * (u₂ n p.2) ^ 2) ∂E :=
          integral_mono_ae hdint (((hsq₁ n).const_mul 2).add ((hsq₂ n).const_mul 2)) (hdu n)
      _ = _ := by
          rw [integral_add ((hsq₁ n).const_mul 2) ((hsq₂ n).const_mul 2), integral_const_mul,
            integral_const_mul, hE₁, hE₂, hi₁, hi₂]
          ring
  have hlim : Tendsto (fun n => 4 * ‖covVec (U : Set ℂ) χ - gradFeat (U : Set ℂ) (f n).1‖ ^ 2) atTop (𝓝 0) := by
    have : Tendsto (fun n => covVec (U : Set ℂ) χ - gradFeat (U : Set ℂ) (f n).1) atTop (𝓝 0) := by
      simpa using (tendsto_const_nhds (x := covVec (U : Set ℂ) χ)).sub hfg
    simpa using ((continuous_norm.tendsto _).comp this).pow 2 |>.const_mul 4
  have h0 : ∫ p, D.indicator (fun p => (d p) ^ 2) p ∂E = 0 :=
    le_antisymm (ge_of_tendsto' hlim hle) (integral_nonneg fun p => by
      by_cases hpD : p ∈ D <;> simp [hpD, sq_nonneg])
  have hae := (integral_eq_zero_iff_of_nonneg (fun p => by
      by_cases hpD : p ∈ D <;> simp [hpD, sq_nonneg]) hdint).1 h0
  filter_upwards [hae] with p hp hpD
  have := hp
  simp only [Pi.zero_apply, indicator_of_mem hpD, hd_def, pow_eq_zero_iff two_ne_zero] at this
  linarith

end Agree

/-! ### Records -/

theorem fieldRec_add (x x' : DistOn upperHalfPlaneOpens) (y : TwoSeedHist) (ψ : TestOn upperHalfPlaneOpens) :
    fieldRec (x + x') y ψ = fieldRec x y ψ + fieldRec x' y ψ := by
  classical
  by_cases hd : Disjoint (tsupport ψ) (tsHull y)
  · rw [fieldRec_of_disjoint hd, fieldRec_of_disjoint hd, fieldRec_of_disjoint hd]
    rfl
  · simp only [fieldRec, hd, ↓reduceIte, add_zero]

/-- The record rebuilt from a projection `z`, the time-`0` mean `T₀` and the record of the complementary projection. -/
def recBuild (T₀ : DistOn upperHalfPlaneOpens) (x : DistOn upperHalfPlaneOpens × RecSp) : RecSp :=
  (x.2.1, fun ψ => fieldRec (x.1 + T₀) x.2.1 ψ + x.2.2 ψ)

theorem measurable_recBuild (T₀ : DistOn upperHalfPlaneOpens) : Measurable (recBuild T₀) := by
  have hs : Measurable (Prod.snd : DistOn upperHalfPlaneOpens × RecSp → RecSp) := measurable_snd
  have hy : Measurable fun x : DistOn upperHalfPlaneOpens × RecSp => x.2.1 := measurable_fst.comp hs
  have hF : Measurable fun x : DistOn upperHalfPlaneOpens × RecSp => x.2.2 := measurable_snd.comp hs
  have h1 : Measurable fun x : DistOn upperHalfPlaneOpens × RecSp => (x.1 + T₀, x.2.1) :=
    ((WholeField.measurable_add_dist T₀).comp measurable_fst).prodMk hy
  have h2 : ∀ ψ : TestOn upperHalfPlaneOpens,
      Measurable fun x : DistOn upperHalfPlaneOpens × RecSp => fieldRec (x.1 + T₀) x.2.1 ψ + x.2.2 ψ :=
    fun ψ => ((measurable_fieldRec_apply ψ).comp h1).add ((measurable_pi_apply ψ).comp hF)
  exact hy.prodMk (Measurable.of_eval h2)

/-! ### The reference hull after the capped local stop -/

section RefHull

variable {κ rL rR r : ℝ} {nL nR : ℕ} {xL : Fin nL → ℝ} {xR : Fin nR → ℝ}
  {Ωr : Type*} [mΩr : MeasurableSpace Ωr] {Pr : Measure Ωr}
  {Wr : ℝ≥0 → Ωr → ℝ} {VLr VRr : Fin 1 → ℝ≥0 → Ωr → ℝ} {Br : ℝ≥0 → Ωr → ℝ} {ζr : Ωr → ℝ≥0∞} {Gr : Set Ωr}

/-- **After the capped local stop and before a safe stop, the hull read from the reference's history avoids `C`.** -/
theorem ae_disjoint_tsHull_refVer (hL : -2 < rL) (hR : -2 < rR) (hr : 0 < r) (hG0 : Pr Grᶜ = 0)
    (hG : ∀ ω ∈ Gr, IsGoodPath κ LP.twoSeedXL LP.twoSeedXR (fun _ => rL) (fun _ => rR) Wr VLr VRr Br ζr ω)
    {C : Set ℂ} (hCH : C ⊆ H) {s : Ωr → ℝ≥0}
    (hsafe : ∀ᵐ ω ∂Pr, (s ω : ℝ≥0∞) < ζr ω ∧ Disjoint C (fwdHull (fun r : ℝ => Wr r.toNNReal ω) (s ω))) :
    ∀ᵐ ω ∂Pr, capStop r Gr ζr Wr ω ≤ (s ω : WithTop ℝ≥0) →
      Disjoint C (tsHull (refVer xL xR r Gr Wr VLr VRr ζr ω)) := by
  have hGP : ∀ᵐ ω ∂Pr, ω ∈ Gr := ae_iff.2 (by exact hG0)
  filter_upwards [hsafe, hGP] with ω hsω hω hle
  obtain ⟨-, hdis⟩ := hsω
  obtain ⟨hS, hSζ⟩ := capStop_ref hL hR hr hG hω
  rw [refVer_eq_tsOf xL xR hL hR hr hG hω]
  have hS₀s : ((capStop r Gr ζr Wr ω).untopD 0 : ℝ≥0) ≤ s ω := by
    rw [hS] at hle
    exact WithTop.coe_le_coe.1 hle
  exact disjoint_tsHull_tsOf (continuousOn_refState xL xR (hG ω hω) hSζ) hSζ (hG ω hω).1.2.2.2.1
    (fun _ _ => rfl) hCH (hdis.mono_right (show fwdHull (fun r : ℝ => Wr r.toNNReal ω) (((capStop r Gr ζr Wr ω).untopD 0 : ℝ≥0) : ℝ) ⊆
      fwdHull (fun r : ℝ => Wr r.toNNReal ω) (s ω) from
      fun _ hz => ⟨hz.1, hz.2.trans (ENNReal.ofReal_le_ofReal (by exact_mod_cast hS₀s))⟩))

end RefHull

theorem recBuild_markov (T₀ x : DistOn upperHalfPlaneOpens)
    (G : DistOn upperHalfPlaneOpens → DistOn upperHalfPlaneOpens) (y : TwoSeedHist) :
    recBuild T₀ (G (x - T₀), recOf (markovCompl G (x - T₀)) y) = recOf x y := by
  refine Prod.ext rfl (funext fun ψ => ?_)
  simp only [recBuild, recOf]
  rw [← fieldRec_add]
  congr 1
  simp only [markovCompl]
  abel

/-! ### The post-stop identity -/

/-- **`ExtPostLocalStatement κ`** (PROVE-LOCEXT-L's named input (Loc-post)): on a record extension of a stopped seed
coupling by a time-adapted reference, after the reference's capped local stop and before a safe stop at which the
reference satisfies the projection identity, the original centred field satisfies the projection identity. -/
theorem extPostLocalStatement (κ : ℝ) : ExtPostLocalStatement.{u} κ := by
  classical
  intro nL nR xL xR ρL ρR r hF hr hL hR Ω mΩ Q hQ W VL VR S h hc Ωr mΩr Pr 𝓕r Wr VLr VRr Br ζr hr' href Gr hGm
    hG0 hG E hE u₀ hu₀ C hC hCH U hUC s hs hsafe hid f Ξ A₀ hA₀
  obtain ⟨⟨-, hPr, hCr, -, -, -⟩, -⟩ := href
  have : IsProbabilityMeasure Pr := hPr
  obtain ⟨hfst, hsnd, hRR, hfR, hrecm, κ₀, hκ₀, hEeq⟩ := hE
  have : IsProbabilityMeasure E := isProbabilityMeasure_of_map_fst hfst
  have := hκ₀
  obtain ⟨-, -, -, -, -, -, -, hhm, hgff, -⟩ := id hc
  have hu₀c : ContinuousOn u₀ H := fun z hz => (hu₀.1 z hz).1.continuousAt.continuousWithinAt
  obtain ⟨T₀, hT₀def⟩ : ∃ T₀, T₀ = smoothDist upperHalfPlaneOpens u₀ := ⟨_, rfl⟩
  rw [← hT₀def] at hid ⊢
  have hT₀ : IsHarmonicDistOn T₀ H := hT₀def ▸ isHarmonicDistOn_smoothDist_of hu₀
  have hX₁ : IsZeroBoundaryGFF upperHalfPlaneOpens (fun ω => h ω - T₀) Q :=
    hT₀def ▸ isZeroBoundaryGFF_sub_smoothDist hhm hu₀c (hgff u₀ hu₀)
  have hX₂ : IsZeroBoundaryGFF upperHalfPlaneOpens (fun ω => hr' ω - T₀) Pr :=
    hT₀def ▸ isZeroBoundaryGFF_sub_smoothDist hCr.2.1 hu₀c (hCr.2.2.1 u₀ hu₀)
  have hUH : (U : Set ℂ) ⊆ H := hUC.trans hCH
  have hU : U ≤ upperHalfPlaneOpens := hUH
  obtain ⟨G, hGG, hGd⟩ := exists_markovMap U hUH
  have hd₁ := hGd hX₁
  have hd₂ := hGd hX₂
  have hX₁m : Measurable fun ω => h ω - T₀ := (WholeField.measurable_sub_dist T₀).comp hhm
  have hX₂m : Measurable fun ω => hr' ω - T₀ := (WholeField.measurable_sub_dist T₀).comp hCr.2.1
  have hRm := hc.measurable_stRecHist
  -- the event after the capped local stop
  obtain ⟨hXr, -⟩ := hCr.2.2.2
  have hŜd := isStoppingTime_capStop hXr hGm hG0 hG r
  have hŜ := Ito.isStoppingTime_usualAugmentation_of_drivingFiltration hCr.1 hXr hŜd
  obtain ⟨D₀, hD₀def⟩ : ∃ D₀ : Set Ωr, D₀ = A₀ ∩ {ω | capStop r Gr ζr Wr ω ≤ (s ω : WithTop ℝ≥0)} := ⟨_, rfl⟩
  rw [← hD₀def]
  have hD₀m : MeasurableSet D₀ := by
    have h1 := hŜ.measurableSet_inter_le hs _ (@MeasurableSet.univ _ hŜ.measurableSpace)
    have h2 := (hŜ.min hs).measurableSpace_mono hs (fun ω => min_le_right _ _) _ h1
    rw [univ_inter] at h2
    rw [hD₀def]
    exact hs.measurableSpace_le _ (hA₀.inter h2)
  have hD₀E : MeasurableSet (Prod.snd ⁻¹' D₀ : Set (Ω × Ωr)) := measurable_snd hD₀m
  -- the histories
  set y := stRecHist xL xR W VL VR S with hydef
  set yv := refVer xL xR r Gr Wr VLr VRr ζr with hyvdef
  have hyv_ae : ∀ᵐ p ∂E, refRecHist xL xR r Gr Wr VLr VRr ζr p.2 = yv p.2 := by
    have := ae_refVer_eq xL xR hL hR hr hG0 hG
    rw [← hsnd] at this
    filter_upwards [ae_of_ae_map measurable_snd.aemeasurable this] with p hp
    exact hp.symm
  have hyE : ∀ᵐ p ∂E, y p.1 = yv p.2 := by
    filter_upwards [hRR, hyv_ae] with p h1 h2
    rw [h1, h2]
  have hregE : ∀ᵐ p ∂E, IsRegularStop W VL VR S p.1 := by
    have := hc.ae_isRegularStop hr
    rw [← hfst] at this
    exact ae_of_ae_map measurable_fst.aemeasurable this
  have hdisE : ∀ᵐ p ∂E, p.2 ∈ D₀ → Disjoint C (tsHull (yv p.2)) := by
    have := ae_disjoint_tsHull_refVer (xL := xL) (xR := xR) hL hR hr hG0 hG hCH hsafe
    rw [← hsnd] at this
    filter_upwards [ae_of_ae_map measurable_snd.aemeasurable this] with p hp hpD
    rw [hD₀def] at hpD
    exact hp hpD.2
  -- the recorded value at a regular stop
  have hrecon : ∀ ω, IsRegularStop W VL VR S ω → histRecon (y ω) = y ω ∧ (0 : WithTop ℝ≥0) < (y ω).1 := by
    intro ω hω
    obtain ⟨S₀, hS₀⟩ := WithTop.ne_top_iff_exists.1 hω.2.1
    have hS0 : 0 < S₀ := by
      have := hω.1
      rw [← hS₀] at this
      exact_mod_cast this
    rw [hydef, stRecHist_eq_tsOf hω hS₀.symm]
    exact ⟨histRecon_tsOf hS0 (continuousOn_stState_of_regular hω hS₀.symm), WithTop.coe_lt_coe.2 hS0⟩
  -- the support of the extension after the stop
  set Γq : Set Ω := y ⁻¹' (preMarkSet 0 univ ∩ {z | Disjoint C (tsHull z)}) with hΓqdef
  have hΓqm : MeasurableSet Γq :=
    hRm ((preMarkSigma_le _ (measurableSet_preMarkSet 0 MeasurableSet.univ)).inter (measurableSet_disjoint_tsHull hC))
  have hsuppE : ∀ᵐ p ∂E, p.2 ∈ D₀ → p.1 ∈ Γq := by
    filter_upwards [hyE, hregE, hdisE] with p h1 h2 h3 hp
    refine ⟨⟨?_, mem_univ _⟩, ?_⟩
    · simpa using (hrecon p.1 h2).2
    · show Disjoint C (tsHull (y p.1))
      rw [h1]
      exact h3 hp
  -- 1. the projections agree after the stop
  have hlapE : ∀ ψ : TestOn upperHalfPlaneOpens, ∀ᵐ p ∂E, p.2 ∈ D₀ →
      Disjoint (tsupport ψ) (tsHull (yv p.2)) → (h p.1 - T₀) ψ = (hr' p.2 - T₀) ψ := by
    intro ψ
    filter_upwards [hfR ψ, hyE, hyv_ae] with p hp hy hy' _ hdis
    rw [hy, ← hy'] at hp
    have hdis' : Disjoint (tsupport ψ) (tsHull (refRecHist xL xR r Gr Wr VLr VRr ζr p.2)) := by rw [hy']; exact hdis
    rw [fieldRec_of_disjoint hdis', fieldRec_of_disjoint hdis'] at hp
    simp only [sub_apply, hp]
  have hZE : ∀ χ : TestOn upperHalfPlaneOpens, ∀ᵐ p ∂E, p ∈ Prod.snd ⁻¹' D₀ →
      G (h p.1 - T₀) χ = G (hr' p.2 - T₀) χ := fun χ =>
    ae_markov_eq_of_lapTest_eq hfst hsnd hU hX₁m hX₂m hGG hd₁ hd₂ hD₀E (fun f' => by
      filter_upwards [hlapE (lapTest U f'), hdisE] with p hp hd hpD
      exact hp hpD ((hd hpD).mono_left ((tsupport_lapTest_subset hU f').trans (f'.2.2.2.trans hUC)))) χ
  -- 2. the compound-product formula
  set rec : Ω → RecSp := fun ω => recOf (h ω) (y ω) with hrecdef
  set g : RecSp → ℝ := fun R => (κ₀ R D₀).toReal with hgdef
  have hgm : Measurable g := (κ₀.measurable_coe hD₀m).ennreal_toReal
  have hg01 : ∀ R, 0 ≤ g R ∧ g R ≤ 1 := fun R => ⟨ENNReal.toReal_nonneg, by
    have := prob_le_one (μ := κ₀ R) (s := D₀)
    exact ENNReal.toReal_le_of_le_ofReal zero_le_one (by simpa using this)⟩
  have hCP : ∀ F : Ω → ℂ, Measurable F → (∀ ω, ‖F ω‖ ≤ 1) →
      ∫ p in Prod.snd ⁻¹' D₀, F p.1 ∂E = ∫ ω, F ω * ((g (rec ω) : ℝ) : ℂ) * Γq.indicator (fun _ => (1 : ℂ)) ω ∂Q := by
    intro F hF hFb
    have hnull : (Prod.snd ⁻¹' D₀ : Set (Ω × Ωr)) =ᵐ[E] (Γq ×ˢ D₀ : Set (Ω × Ωr)) := by
      filter_upwards [hsuppE] with p hp
      apply propext
      simp only [mem_preimage, mem_prod]
      exact ⟨fun h2 => ⟨hp h2, h2⟩, fun h2 => h2.2⟩
    have hint : IntegrableOn (fun p : Ω × Ωr => F p.1) (Γq ×ˢ D₀) (Q ⊗ₘ κ₀.comap rec hrecm) :=
      (Integrable.of_bound (hF.comp measurable_fst).aestronglyMeasurable 1
        (Eventually.of_forall fun p => hFb p.1)).integrableOn
    rw [setIntegral_congr_set hnull, hEeq, Measure.setIntegral_compProd hΓqm hD₀m hint, ← integral_indicator hΓqm]
    refine integral_congr_ae (Eventually.of_forall fun ω => ?_)
    by_cases hω : ω ∈ Γq
    · simp only [indicator_of_mem hω, setIntegral_const, Kernel.comap_apply, measureReal_def, hgdef,
        Complex.real_smul, mul_one]
      ring
    · simp only [indicator_of_notMem hω, mul_zero]
  -- 3. the Q side: the record of the complementary projection, measurable for the marked σ-algebra
  set Y₁ : Ω → DistOn upperHalfPlaneOpens := fun ω => markovCompl G (h ω - T₀) with hY₁def
  set Vq : Ω → ℝ × RecSp := fun ω => (Γq.indicator (fun _ => (1 : ℝ)) ω,
    (refRecordOn Γq Y₁ (fun ω => histRecon (y ω)) ω).2) with hVqdef
  have hΓqσ : MeasurableSet[markSigmaQ xL xR W VL VR S U] Γq :=
    MeasurableSpace.measurableSet_generateFrom ⟨0, univ, C, MeasurableSet.univ, hC, hCH, hUC, rfl⟩
  have hNσ : ∀ N : Set TwoSeedHist, MeasurableSet[preMarkSigma] N →
      MeasurableSet[markSigmaQ xL xR W VL VR S U] (y ⁻¹' ((preMarkSet 0 univ ∩ {z | Disjoint C (tsHull z)}) ∩ N)) := by
    intro N hN
    refine MeasurableSpace.induction_on_inter (m := preMarkSigma)
      (C := fun N _ => MeasurableSet[markSigmaQ xL xR W VL VR S U]
        (y ⁻¹' ((preMarkSet 0 univ ∩ {z | Disjoint C (tsHull z)}) ∩ N))) rfl isPiSystem_preMarkSets
      (by simp) ?_ ?_ ?_ N hN
    · rintro _ ⟨t, Γ, hΓ, rfl⟩
      refine MeasurableSpace.measurableSet_generateFrom ⟨t, truncH 0 ⁻¹' univ ∩ Γ, C,
        ((measurable_truncH 0) MeasurableSet.univ).inter hΓ, hC, hCH, hUC, ?_⟩
      rw [← preMarkSet_inter_of_le (zero_le : (0 : ℚ≥0) ≤ t)]
      congr 1
      ext z
      simp only [mem_inter_iff, mem_ofPred_eq]
      tauto
    · intro N' _ hN'
      have e : y ⁻¹' ((preMarkSet 0 univ ∩ {z | Disjoint C (tsHull z)}) ∩ N'ᶜ) =
          Γq \ y ⁻¹' ((preMarkSet 0 univ ∩ {z | Disjoint C (tsHull z)}) ∩ N') := by
        ext ω
        simp only [hΓqdef, mem_preimage, mem_inter_iff, Set.mem_sdiff, mem_compl_iff]
        tauto
      rw [e]
      exact hΓqσ.diff hN'
    · intro Ns _ _ hNs
      rw [inter_iUnion, preimage_iUnion]
      exact MeasurableSet.iUnion hNs
  have hVqm : Measurable[MeasurableSpace.comap Y₁ inferInstance ⊔ markSigmaQ xL xR W VL VR S U] Vq := by
    have h𝓜r : markSigmaQ xL xR W VL VR S U ≤
        MeasurableSpace.comap Y₁ inferInstance ⊔ markSigmaQ xL xR W VL VR S U := le_sup_right
    have hrec := measurable_refRecordOn (𝓐 := MeasurableSpace.comap Y₁ inferInstance)
      (𝓜 := MeasurableSpace.comap Y₁ inferInstance ⊔ markSigmaQ xL xR W VL VR S U) (D₀ := Γq)
      (yv := fun ω => histRecon (y ω)) (comap_measurable Y₁) le_sup_left (h𝓜r _ hΓqσ) fun M hM => by
        have := hNσ _ (measurable_histRecon hM)
        exact h𝓜r _ this
    exact Measurable.prodMk (m := MeasurableSpace.comap Y₁ inferInstance ⊔ markSigmaQ xL xR W VL VR S U)
      (measurable_const.indicator (h𝓜r _ hΓqσ)) hrec.snd
  set W₁ : Ω → ℝ × (ℝ × RecSp) := fun ω => (Y₁ ω Ξ, Vq ω) with hW₁def
  have hW₁m : Measurable[MeasurableSpace.comap Y₁ inferInstance ⊔ markSigmaQ xL xR W VL VR S U] W₁ :=
    Measurable.prodMk (m := MeasurableSpace.comap Y₁ inferInstance ⊔ markSigmaQ xL xR W VL VR S U)
      (((measurable_distOn_apply Ξ).comp (comap_measurable Y₁)).mono le_sup_left le_rfl) hVqm
  have hindQ : IndepFun (fun ω => G (h ω - T₀)) W₁ Q :=
    (IndepFun_iff_Indep _ _ _).2 (indep_of_indep_of_le_right (hc.indep_markSigmaQ hr hT₀ hUH hGG hd₁) hW₁m.comap_le)
  have hσle : MeasurableSpace.comap Y₁ inferInstance ⊔ markSigmaQ xL xR W VL VR S U ≤ mΩ :=
    sup_le ((measurable_markovCompl hGG).comp hX₁m).comap_le (markSigmaQ_le hRm _)
  have hW₁m' : Measurable W₁ := hW₁m.mono hσle le_rfl
  -- the conditional expectation of `e^{iY(Ξ)}` given the record of `Y`
  set A : Ω → ℂ := fun ω => Complex.exp (Complex.I * (Y₁ ω Ξ : ℂ)) with hAdef
  have hsm : StronglyMeasurable[MeasurableSpace.comap Vq inferInstance]
      (Q[A | MeasurableSpace.comap Vq inferInstance]) := stronglyMeasurable_condExp
  obtain ⟨ã₀, hã₀, hã₀e⟩ := hsm.exists_eq_measurable_comp
  set ã : ℝ × RecSp → ℂ := fun x => if ‖ã₀ x‖ ≤ 1 then ã₀ x else 0 with hãdef
  have hãm : Measurable ã := hã₀.measurable.ite (measurableSet_le hã₀.measurable.norm measurable_const) measurable_const
  have hãb : ∀ x, ‖ã x‖ ≤ 1 := fun x => by
    by_cases hx : ‖ã₀ x‖ ≤ 1
    · simp only [hãdef, hx, ↓reduceIte]
    · simp only [hãdef, hx, ↓reduceIte, norm_zero, zero_le_one]
  have hãe : Q[A | MeasurableSpace.comap Vq inferInstance] =ᵐ[Q] fun ω => ã (Vq ω) := by
    have hb := ae_bdd_norm_condExp_of_ae_bdd_norm (m := MeasurableSpace.comap Vq inferInstance) (μ := Q) (R := 1)
      (f := A) (Eventually.of_forall fun ω => (Complex.norm_exp_I_mul_ofReal _).le)
    filter_upwards [hb] with ω hω
    have e := congrFun hã₀e ω
    simp only [Function.comp_apply] at e
    rw [e] at hω ⊢
    simp only [hãdef, hω, ↓reduceIte]
  -- 4. the chain for one test function
  have hregQ := hc.ae_isRegularStop hr
  have hVqΓ : ∀ ω, IsRegularStop W VL VR S ω → ω ∈ Γq → Vq ω = ((1 : ℝ), recOf (Y₁ ω) (y ω)) := by
    intro ω hω hΓ
    simp only [hVqdef, indicator_of_mem hΓ, refRecordOn_of_mem hΓ, (hrecon ω hω).1]
  have hVq0 : ∀ ω, ω ∉ Γq → (Vq ω).1 = 0 := fun ω hΓ => by
    simp only [hVqdef, indicator_of_notMem hΓ]
  have hyvm : Measurable yv := measurable_refVer hCr hGm hG0 hG
  have hY₂m : Measurable fun ω => markovCompl G (hr' ω - T₀) := (measurable_markovCompl hGG).comp hX₂m
  have hVqm' : Measurable Vq := hVqm.mono hσle le_rfl
  have hY₁Ξ : ∀ ω, (h ω - T₀) Ξ = G (h ω - T₀) Ξ + Y₁ ω Ξ := fun ω => by
    simp only [hY₁def, markovCompl, sub_apply]
    ring
  have key : ∀ χ : TestOn upperHalfPlaneOpens, (∀ᵐ ω ∂Q, Y₁ ω χ = Y₁ ω Ξ) →
      ∫ p in Prod.snd ⁻¹' D₀, Complex.exp (Complex.I * ((h p.1 - T₀) χ : ℂ)) ∂E =
        gaussFactor U χ * ∫ ω in D₀, ã ((1 : ℝ), recOf (markovCompl G (hr' ω - T₀)) (yv ω)) ∂Pr := by
    intro χ hYχ
    set Φ : DistOn upperHalfPlaneOpens × (ℝ × RecSp) → ℂ := fun x => Complex.exp (Complex.I * (x.1 χ : ℂ)) *
      (if x.2.1 = 1 then ((g (recBuild T₀ (x.1, x.2.2)) : ℝ) : ℂ) else 0) with hΦdef
    have hΦm : Measurable Φ := (GFF.measurable_exp_I_mul ((measurable_distOn_apply χ).comp measurable_fst)).mul
      (Measurable.ite (measurableSet_eq_fun (measurable_fst.comp measurable_snd) measurable_const)
        (Complex.measurable_ofReal.comp (hgm.comp ((measurable_recBuild T₀).comp
          (measurable_fst.prodMk (measurable_snd.comp measurable_snd))))) measurable_const)
    have hΦb : ∀ x, ‖Φ x‖ ≤ 1 := fun x => by
      rw [hΦdef, norm_mul, Complex.norm_exp_I_mul_ofReal, one_mul]
      split_ifs
      · rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hg01 _).1]; exact (hg01 _).2
      · rw [norm_zero]; exact zero_le_one
    have hrecQ : ∀ ω, IsRegularStop W VL VR S ω → ω ∈ Γq →
        recBuild T₀ (G (h ω - T₀), (Vq ω).2) = rec ω := fun ω hω hΓ => by
      rw [hVqΓ ω hω hΓ]
      exact recBuild_markov T₀ (h ω) G (y ω)
    have hdec : ∀ᵐ ω ∂Q, Complex.exp (Complex.I * ((h ω - T₀) χ : ℂ)) * ((g (rec ω) : ℝ) : ℂ) *
        Γq.indicator (fun _ => (1 : ℂ)) ω = A ω * Φ (G (h ω - T₀), Vq ω) := by
      filter_upwards [hYχ, hregQ] with ω hY hreg
      by_cases hΓ : ω ∈ Γq
      · have h1 : (Vq ω).1 = 1 := by rw [hVqΓ ω hreg hΓ]
        rw [indicator_of_mem hΓ, hΦdef]
        simp only [h1, ↓reduceIte, hrecQ ω hreg hΓ, hAdef, mul_one]
        rw [show (h ω - T₀) χ = G (h ω - T₀) χ + Y₁ ω χ by simp only [hY₁def, markovCompl, sub_apply]; ring, hY]
        push_cast
        rw [mul_add, Complex.exp_add]
        ring
      · have h0 : ¬ (Vq ω).1 = 1 := by rw [hVq0 ω hΓ]; norm_num
        rw [indicator_of_notMem hΓ, hΦdef]
        simp only [h0, ↓reduceIte, mul_zero]
    have hdec' : ∀ᵐ ω ∂Q, ã (Vq ω) * Complex.exp (Complex.I * (G (h ω - T₀) χ : ℂ)) * ((g (rec ω) : ℝ) : ℂ) *
        Γq.indicator (fun _ => (1 : ℂ)) ω = ã (Vq ω) * Φ (G (h ω - T₀), Vq ω) := by
      filter_upwards [hregQ] with ω hreg
      by_cases hΓ : ω ∈ Γq
      · have h1 : (Vq ω).1 = 1 := by rw [hVqΓ ω hreg hΓ]
        rw [indicator_of_mem hΓ, hΦdef]
        simp only [h1, ↓reduceIte, hrecQ ω hreg hΓ, mul_one]
        ring
      · have h0 : ¬ (Vq ω).1 = 1 := by rw [hVq0 ω hΓ]; norm_num
        rw [indicator_of_notMem hΓ, hΦdef]
        simp only [h0, ↓reduceIte, mul_zero]
    have hGL := integral_mul_eq_of_indepFun_condExp (hGG.comp hX₁m) hW₁m' hindQ
      (a := fun w : ℝ × (ℝ × RecSp) => Complex.exp (Complex.I * (w.1 : ℂ)))
      (GFF.measurable_exp_I_mul measurable_fst) (fun w => (Complex.norm_exp_I_mul_ofReal _).le)
      (v := Prod.snd) measurable_snd hãm hãb hãe hΦm hΦb
    have hFm : Measurable fun ω => ã (Vq ω) * Complex.exp (Complex.I * (G (h ω - T₀) χ : ℂ)) :=
      (hãm.comp hVqm').mul (GFF.measurable_exp_I_mul ((measurable_distOn_apply χ).comp (hGG.comp hX₁m)))
    have hFb : ∀ ω, ‖ã (Vq ω) * Complex.exp (Complex.I * (G (h ω - T₀) χ : ℂ))‖ ≤ 1 := fun ω => by
      rw [norm_mul, Complex.norm_exp_I_mul_ofReal, mul_one]; exact hãb _
    rw [hCP (fun ω => Complex.exp (Complex.I * ((h ω - T₀) χ : ℂ)))
      (GFF.measurable_exp_I_mul ((measurable_distOn_apply χ).comp hX₁m))
      (fun ω => (Complex.norm_exp_I_mul_ofReal _).le), integral_congr_ae hdec]
    have hGL' : ∫ ω, A ω * Φ (G (h ω - T₀), Vq ω) ∂Q = ∫ ω, ã (Vq ω) * Φ (G (h ω - T₀), Vq ω) ∂Q := hGL
    rw [hGL', ← integral_congr_ae hdec',
      ← hCP (fun ω => ã (Vq ω) * Complex.exp (Complex.I * (G (h ω - T₀) χ : ℂ))) hFm hFb]
    -- transfer to the reference through the record
    set f₁ : Ω × Ωr → (ℝ × ℝ × TwoSeedHist) × (TestOn upperHalfPlaneOpens → ℝ) :=
      fun p => ((G (h p.1 - T₀) χ, (Vq p.1).1, (Vq p.1).2.1), (Vq p.1).2.2) with hf₁def
    set f₂ : Ω × Ωr → (ℝ × ℝ × TwoSeedHist) × (TestOn upperHalfPlaneOpens → ℝ) :=
      fun p => ((G (hr' p.2 - T₀) χ, (1 : ℝ), yv p.2), fieldRec (markovCompl G (hr' p.2 - T₀)) (yv p.2))
      with hf₂def
    set k : (ℝ × ℝ × TwoSeedHist) × (TestOn upperHalfPlaneOpens → ℝ) → ℂ :=
      fun x => ã (x.1.2.1, (x.1.2.2, x.2)) * Complex.exp (Complex.I * (x.1.1 : ℂ)) with hkdef
    have hf₁m : Measurable f₁ :=
      ((((measurable_distOn_apply χ).comp (hGG.comp hX₁m)).comp measurable_fst).prodMk
        (((measurable_fst.comp hVqm').comp measurable_fst).prodMk
          ((measurable_fst.comp (measurable_snd.comp hVqm')).comp measurable_fst))).prodMk
        ((measurable_snd.comp (measurable_snd.comp hVqm')).comp measurable_fst)
    have hf₂m : Measurable f₂ :=
      ((((measurable_distOn_apply χ).comp (hGG.comp hX₂m)).comp measurable_snd).prodMk
        (measurable_const.prodMk (hyvm.comp measurable_snd))).prodMk
        ((measurable_snd.comp (measurable_recOf.comp (hY₂m.prodMk hyvm))).comp measurable_snd)
    have hkm : Measurable k := (hãm.comp ((measurable_fst.comp (measurable_snd.comp measurable_fst)).prodMk
      ((measurable_snd.comp (measurable_snd.comp measurable_fst)).prodMk measurable_snd))).mul
      (GFF.measurable_exp_I_mul (measurable_fst.comp measurable_fst))
    have h1 : ∀ᵐ p ∂E.restrict (Prod.snd ⁻¹' D₀), (f₁ p).1 = (f₂ p).1 := by
      rw [ae_restrict_iff' hD₀E]
      filter_upwards [hZE χ, hsuppE, hregE, hyE] with p hz hs' hreg hy hp
      simp only [hf₁def, hf₂def, hVqΓ p.1 hreg (hs' hp), recOf, hz hp, hy]
    have h2 : ∀ ψ, ∀ᵐ p ∂E.restrict (Prod.snd ⁻¹' D₀), (f₁ p).2 ψ = (f₂ p).2 ψ := by
      intro ψ
      rw [ae_restrict_iff' hD₀E]
      filter_upwards [hZE ψ, hsuppE, hregE, hyE, hlapE ψ] with p hz hs' hreg hy hl hp
      simp only [hf₁def, hf₂def, hVqΓ p.1 hreg (hs' hp), recOf, hy]
      by_cases hd : Disjoint (tsupport ψ) (tsHull (yv p.2))
      · rw [fieldRec_of_disjoint hd, fieldRec_of_disjoint hd]
        simp only [hY₁def, markovCompl, sub_apply]
        rw [hz hp]
        have := hl hp hd
        simp only [sub_apply] at this
        rw [this]
      · simp only [fieldRec, hd, ↓reduceIte]
    have hmap := map_eq_of_ae_coord hf₁m hf₂m h1 h2
    have htr : ∫ p in Prod.snd ⁻¹' D₀, ã (Vq p.1) * Complex.exp (Complex.I * (G (h p.1 - T₀) χ : ℂ)) ∂E =
        ∫ p in Prod.snd ⁻¹' D₀, ã ((1 : ℝ), recOf (markovCompl G (hr' p.2 - T₀)) (yv p.2)) *
          Complex.exp (Complex.I * (G (hr' p.2 - T₀) χ : ℂ)) ∂E := by
      calc _ = ∫ p, k (f₁ p) ∂E.restrict (Prod.snd ⁻¹' D₀) := rfl
        _ = ∫ x, k x ∂(E.restrict (Prod.snd ⁻¹' D₀)).map f₁ :=
          (integral_map hf₁m.aemeasurable hkm.aestronglyMeasurable).symm
        _ = ∫ x, k x ∂(E.restrict (Prod.snd ⁻¹' D₀)).map f₂ := by rw [hmap]
        _ = ∫ p, k (f₂ p) ∂E.restrict (Prod.snd ⁻¹' D₀) :=
          integral_map hf₂m.aemeasurable hkm.aestronglyMeasurable
        _ = _ := rfl
    rw [htr]
    have hFm₂ : Measurable fun ω => ã ((1 : ℝ), recOf (markovCompl G (hr' ω - T₀)) (yv ω)) *
        Complex.exp (Complex.I * (G (hr' ω - T₀) χ : ℂ)) :=
      (hãm.comp (measurable_const.prodMk (measurable_recOf.comp (hY₂m.prodMk hyvm)))).mul
        (GFF.measurable_exp_I_mul ((measurable_distOn_apply χ).comp (hGG.comp hX₂m)))
    have hsm := setIntegral_map (μ := E) (g := Prod.snd) (f := fun ω => ã ((1 : ℝ), recOf (markovCompl G (hr' ω - T₀))
      (yv ω)) * Complex.exp (Complex.I * (G (hr' ω - T₀) χ : ℂ))) hD₀m
      (by rw [hsnd]; exact hFm₂.aestronglyMeasurable) measurable_snd.aemeasurable
    rw [hsnd] at hsm
    rw [← hsm]
    have href := setIntegral_refRecord_gauss (xL := xL) (xR := xR) (r := r) hCr hGm hG0 hG hX₂m hUH hGG hd₂ hs hid hA₀ hãm χ
    rw [← hD₀def] at href
    rw [← href]
    refine integral_congr_ae (Eventually.of_forall fun ω => ?_)
    simp only [hyvdef]
    ring
  -- 5. the projection identity
  have hlap : ∀ᵐ ω ∂Q, Y₁ ω (lapTest U f + Ξ) = Y₁ ω Ξ := by
    filter_upwards [ae_markov_sub_lapTest_eq hU hd₁ (lapTest U f) f] with ω hω
    rw [sub_self, map_zero] at hω
    simp only [hY₁def, markovCompl, map_add, sub_apply] at hω ⊢
    linarith
  rw [key _ hlap, key Ξ (Eventually.of_forall fun _ => rfl), gaussFactor_lapTest_add hUH f Ξ, mul_assoc]

/-- **Aux. lemma 54 for stopped seed couplings** (`StoppedSeedExtensionStatement κ`), for every `κ > 0`: both of
PROVE-LOCEXT-L's named inputs are proved (`extPostLocalStatement`, `emptySideReferenceLSStatement`). -/
theorem stoppedSeedExtensionStatement {κ : ℝ} (hκ : 0 < κ) : StoppedSeedExtensionStatement.{u} κ :=
  stoppedSeedExtensionStatement_of_post hκ (emptySideReferenceLSStatement hκ) (extPostLocalStatement κ)

end LocalExt

end InteractingSLE
