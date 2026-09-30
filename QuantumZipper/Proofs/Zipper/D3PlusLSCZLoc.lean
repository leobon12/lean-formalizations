import QuantumZipper.Proofs.Zipper.D3PlusN2CMInst
import QuantumZipper.Proofs.Zipper.D3PlusIICond

/-!
# D3⁺(ii), part vanishing at `0` (task LSCZERO-CORE): locality and the shift estimate

Route (D24; Sheffield arXiv:1012.4797, proof of Prop. 1.6, p. 25: near the marked point the
smooth part is "approximately constant"; Cameron–Martin: Berestycki–Powell arXiv:2004.04720,
Lemmas 3.12, 3.14, p. 79). The two corrections `g, g'` agree at `0`; on the event that the local
scale is `< ε/(R+2)` the zoomed pair of either model field only reads the field on the dyadic
circles of `ball 0 ε`, where the `g'`-model is the `g`-model shifted by `μ ↦ ∫ (g' − g) dμ`.

* `lsczG γ ε R`: the measurable reading `v ↦ (TmRichN1 γ ε R 0 (v, 0), log scaleSur γ 0 ε (v, 0))`
  of the field restricted to the `ε`-local measures; `lsczG_congr`: it only reads the dyadic
  circles of `ball 0 ε`.
* `zoomPairFull_eq_lsczG` (deterministic locality, rich data **and** log scale; extends
  `locFieldFull_canonicalOn_eq_local`), `zoomGen_eq_lsczG_of_not_bad` (the model field of a
  `Setup`, off the bad-scale event).
* `macroF_sub_eq_integral`: on the dyadic circles the macroscopic data of `g'` and `g` differ by
  `∫ (g' − g) dμ`.
* `lscz_lintegral_shift_le`: the conditioning/shift estimate: for `Z ⊥ 𝒢`, `𝒢`-measurable `a, b`
  and a reading `G` with `G(v + a + b) = G(v + sh + a)`, the two expectations of
  `Φ(ω, G(ℓ(Z) + a (+ b)))` differ by at most `∫⁻ min(d_TV(law ℓ(Z), law ℓ(Z) + sh ω), 1)`
  (lower integral; no measurability of the TV distance in `ω` is needed).

Own elementary arguments (AGENT_GUIDE cost rule), from `lintegral_comp_indep` (Kallenberg FMP
Lemma 3.11) and TV duality.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal ENNReal

namespace QuantumZipper
namespace D3Plus

/-- The reading of the rich zoomed pair from the field on the `ε`-local measures. -/
def lsczG (γ ε : ℝ) (R : ℕ) (v : LocIdx ε → ℝ) : ((ℕ → ℝ) × (TestFun H → ℝ)) × ℝ :=
  (TmRichN1 γ ε R 0 (v, 0), Real.log (scaleSur γ 0 ε (v, 0)))

theorem measurable_lsczG (γ ε : ℝ) (R : ℕ) : Measurable (lsczG γ ε R) :=
  ((measurable_TmRichN1 γ ε R 0).comp (measurable_id.prodMk measurable_const)).prodMk
    (Real.measurable_log.comp
      ((measurable_scaleSur γ 0 ε).comp (measurable_id.prodMk measurable_const)))

theorem lsczG_congr {γ ε : ℝ} {R : ℕ} {v v' : LocIdx ε → ℝ}
    (h : ∀ μ : LocIdx ε, μ.1 ∈ circSet ε → v μ = v' μ) : lsczG γ ε R v = lsczG γ ε R v' := by
  have hm : locModel γ 0 ε (v, 0) = locModel γ 0 ε (v', 0) := by
    classical
    funext μ
    unfold locModel
    split_ifs with hμ
    · dsimp only
      rw [h _ hμ]
    · rfl
  have hs : scaleSur γ 0 ε (v, 0) = scaleSur γ 0 ε (v', 0) := by
    simp only [scaleSur, Prop16Area.Meas.M, Prop16Area.Meas.Psi, bumpHD, hm]
  simp only [lsczG, TmRichN1_congr hm, hs]

theorem circSet_mono {ε r : ℝ} (hεr : ε ≤ r) : circSet ε ⊆ circSet r := by
  rintro μ ⟨n, k, z, hz, rfl⟩
  exact ⟨n, k, z, hz.trans_le hεr, rfl⟩

/-- **Deterministic locality of the rich zoomed pair** (with the log scale). -/
theorem zoomPairFull_eq_lsczG {γ r ε : ℝ} {R : ℕ} {y : FieldSample}
    (hε : 0 < ε) (hεr : ε ≤ r) (h0 : 0 < scaleParamOn γ y (halfDisc r))
    (hlt : scaleParamOn γ y (halfDisc r) < ε / (R + 2)) :
    (locFieldFull R (canonicalOn γ y (halfDisc r)), Real.log (scaleParamOn γ y (halfDisc r))) =
      lsczG γ ε R (resField ε y) := by
  refine Prod.ext (locFieldFull_canonicalOn_eq_local hε hεr h0 hlt) ?_
  have hR1 : ε / (R + 2) ≤ ε / (R + 1) :=
    div_le_div_of_nonneg_left hε.le (by positivity) (by linarith)
  have hR0 : ε / (R + 1) ≤ ε := div_le_self hε.le (by linarith [(R.cast_nonneg : (0 : ℝ) ≤ R)])
  have hs := scaleParamOn_halfDisc_restrict hεr h0 ((hlt.trans_le hR1).trans_le hR0)
  have hag : AgreeNear y (locModel γ 0 ε (resField ε y, 0)) ε := by
    intro n k z hz
    have hmem : foldedCircle (dyadicRoundC n z) (radius k) ∈ circSet ε := ⟨n, k, z, hz, rfl⟩
    simp [locModel, dif_pos hmem, resField]
  have hsc := scaleParamOn_halfDisc_congr (γ := γ) hag
  have hpos : 0 < scaleParamOn γ (locModel γ 0 ε (resField ε y, 0)) (halfDisc ε) := by
    rw [← hsc, hs]; exact h0
  show Real.log _ = Real.log (scaleSur γ 0 ε (resField ε y, 0))
  rw [scaleSur_eq (mem_goodN1_of_pos hpos), ← hsc, hs]

section Setup

variable {γ α r : ℝ} {ρ₀ : Measure ℂ} {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
  {X : Ω → FieldSample} {E' : Type*} [MeasurableSpace E'] {Ξ : Ω → E'} {g : Ω → ℂ → ℝ}

theorem admCorr_of_setup (hS : Setup γ α r ρ₀ P X Ξ g) (ω : Ω) : AdmCorr r (g ω) :=
  ⟨continuousOn_g_of_harm (hS.harm ω), r, hS.hr, hS.harm ω⟩

/-- **The model zoomed pair off the bad-scale event, read on the `ε`-local circles.** -/
theorem zoomGen_eq_lsczG_of_not_bad (hS : Setup γ α r ρ₀ P X Ξ g) {ε : ℝ} (hε : 0 < ε)
    (hεr : ε ≤ r) {R : ℕ} {L : ℝ} {ω : Ω}
    (hω : ω ∉ badScale γ α r (ε / (R + 2)) ρ₀ X g L) {v : LocIdx ε → ℝ}
    (hv : ∀ μ : LocIdx ε, μ.1 ∈ circSet ε →
      v μ = resField ε (locZField X r ω) μ + (macroF α r ρ₀ X g ω μ.1 + L / γ)) :
    zoomGen locFieldFull γ α L r R ρ₀ (X ω) (g ω) = lsczG γ ε R v := by
  classical
  simp only [badScale, mem_setOf_eq, not_not] at hω
  refine (zoomPairFull_eq_lsczG hε hεr hω.1 hω.2).trans (lsczG_congr fun μ hμ => ?_)
  rw [hv μ hμ]
  have hμr : μ.1 ∈ circSet r := circSet_mono hεr hμ
  obtain ⟨n, k, z, hz, hμe⟩ := hμ
  have hag := agreeNear_zoomModel_locModel hS L ω n k z (hz.trans_le hεr)
  rw [← hμe] at hag
  simp only [resField]
  rw [hag, locZField_apply_of_local X ω (isLocalH_of_mem_circSet hμr)]
  simp only [locModel, dif_pos hμr, localZ]
  ring

/-- On the dyadic circles, the macroscopic data of two corrections differ by the integral of
the difference. -/
theorem macroF_sub_eq_integral {g' : Ω → ℂ → ℝ} (hS : Setup γ α r ρ₀ P X Ξ g)
    (hS' : Setup γ α r ρ₀ P X Ξ g') (ω : Ω) {μ : Measure ℂ} (hμ : μ ∈ circSet r) :
    macroF α r ρ₀ X g' ω μ - macroF α r ρ₀ X g ω μ = ∫ z, (g' ω z - g ω z) ∂μ := by
  classical
  obtain ⟨d, ρ, hρ, hdr, rfl⟩ := exists_of_mem_circSet hμ
  simp only [macroF, if_pos hμ, circVal]
  have e : ∫ z, (g' ω z - g ω z) ∂foldedCircle d ρ =
      ∫ z, ((α * -Real.log ‖z‖ + g' ω z) - (α * -Real.log ‖z‖ + g ω z)) ∂foldedCircle d ρ := by
    congr 1; funext z; ring
  rw [e, integral_sub (integrable_zoomPot_circ hS' ω hρ hdr) (integrable_zoomPot_circ hS ω hρ hdr)]
  ring

end Setup

/-- **The conditioning/shift estimate** (own elementary argument: integrate out the independent
part `Z` (`lintegral_comp_indep`), then TV duality for the shifted law at each `ω`). -/
theorem lscz_lintegral_shift_le {Ω S ι E : Type*} {m𝒢 : MeasurableSpace Ω}
    [mΩ : MeasurableSpace Ω] [MeasurableSpace S] [MeasurableSpace E] {P : Measure Ω}
    [IsProbabilityMeasure P] (hm : m𝒢 ≤ mΩ) {Z : Ω → S} (hZ : Measurable Z)
    (hind : Indep (MeasurableSpace.comap Z inferInstance) m𝒢 P) {ℓ : S → ι → ℝ}
    (hℓ : Measurable ℓ) {G : (ι → ℝ) → E} (hG : Measurable G) {a b : Ω → ι → ℝ}
    (ha : Measurable[m𝒢] a) (hb : Measurable[m𝒢] b) (sh : Ω → ι → ℝ)
    (hsh : ∀ ω v, G (v + a ω + b ω) = G (v + sh ω + a ω)) {Φ : Ω × E → ℝ≥0∞}
    (hΦ : Measurable[m𝒢.prod inferInstance] Φ) (h1 : ∀ p, Φ p ≤ 1) :
    ∫⁻ ω, Φ (ω, G (ℓ (Z ω) + a ω + b ω)) ∂P ≤ ∫⁻ ω, Φ (ω, G (ℓ (Z ω) + a ω)) ∂P +
        ∫⁻ ω, min (TV.tvDist (P.map fun ω' => ℓ (Z ω'))
          (P.map fun ω' => ℓ (Z ω') + sh ω)) 1 ∂P ∧
      ∫⁻ ω, Φ (ω, G (ℓ (Z ω) + a ω)) ∂P ≤ ∫⁻ ω, Φ (ω, G (ℓ (Z ω) + a ω + b ω)) ∂P +
        ∫⁻ ω, min (TV.tvDist (P.map fun ω' => ℓ (Z ω'))
          (P.map fun ω' => ℓ (Z ω') + sh ω)) 1 ∂P := by
  have hid : @Measurable Ω Ω mΩ m𝒢 id := fun s hs => hm s hs
  have hΦ' : Measurable Φ :=
    @Measurable.comp (Ω × E) (Ω × E) ℝ≥0∞ _ (m𝒢.prod inferInstance) _ _ _ hΦ
      (hid.prodMap measurable_id)
  have ha' : Measurable a := ha.mono hm le_rfl
  have hb' : Measurable b := hb.mono hm le_rfl
  have hΨ1 : Measurable[m𝒢.prod inferInstance]
      fun q : Ω × S => Φ (q.1, G (ℓ q.2 + a q.1 + b q.1)) :=
    hΦ.comp (measurable_fst.prodMk (hG.comp (((hℓ.comp measurable_snd).add
      (ha.comp measurable_fst)).add (hb.comp measurable_fst))))
  have hΨ0 : Measurable[m𝒢.prod inferInstance] fun q : Ω × S => Φ (q.1, G (ℓ q.2 + a q.1)) :=
    hΦ.comp (measurable_fst.prodMk (hG.comp ((hℓ.comp measurable_snd).add
      (ha.comp measurable_fst))))
  have hΨ1' : Measurable fun q : Ω × S => Φ (q.1, G (ℓ q.2 + a q.1 + b q.1)) :=
    hΦ'.comp (measurable_fst.prodMk (hG.comp (((hℓ.comp measurable_snd).add
      (ha'.comp measurable_fst)).add (hb'.comp measurable_fst))))
  have hΨ0' : Measurable fun q : Ω × S => Φ (q.1, G (ℓ q.2 + a q.1)) :=
    hΦ'.comp (measurable_fst.prodMk (hG.comp ((hℓ.comp measurable_snd).add
      (ha'.comp measurable_fst))))
  have e1 : ∫⁻ ω, Φ (ω, G (ℓ (Z ω) + a ω + b ω)) ∂P =
      ∫⁻ ω, ∫⁻ s, Φ (ω, G (ℓ s + a ω + b ω)) ∂(P.map Z) ∂P :=
    lintegral_comp_indep hm hZ hind hΨ1
  have e0 : ∫⁻ ω, Φ (ω, G (ℓ (Z ω) + a ω)) ∂P =
      ∫⁻ ω, ∫⁻ s, Φ (ω, G (ℓ s + a ω)) ∂(P.map Z) ∂P :=
    lintegral_comp_indep hm hZ hind hΨ0
  have hA1 : Measurable fun ω => ∫⁻ s, Φ (ω, G (ℓ s + a ω + b ω)) ∂(P.map Z) :=
    hΨ1'.lintegral_prod_right'
  have hA0 : Measurable fun ω => ∫⁻ s, Φ (ω, G (ℓ s + a ω)) ∂(P.map Z) :=
    hΨ0'.lintegral_prod_right'
  have hW : Measurable fun ω' => ℓ (Z ω') := hℓ.comp hZ
  -- pointwise estimate
  have hpt : ∀ ω, ∫⁻ s, Φ (ω, G (ℓ s + a ω + b ω)) ∂(P.map Z) ≤
        ∫⁻ s, Φ (ω, G (ℓ s + a ω)) ∂(P.map Z) + min (TV.tvDist (P.map fun ω' => ℓ (Z ω'))
          (P.map fun ω' => ℓ (Z ω') + sh ω)) 1 ∧
      ∫⁻ s, Φ (ω, G (ℓ s + a ω)) ∂(P.map Z) ≤
        ∫⁻ s, Φ (ω, G (ℓ s + a ω + b ω)) ∂(P.map Z) + min (TV.tvDist (P.map fun ω' => ℓ (Z ω'))
          (P.map fun ω' => ℓ (Z ω') + sh ω)) 1 := by
    intro ω
    set f : (ι → ℝ) → ℝ≥0∞ := fun v => Φ (ω, G (v + a ω)) with hf_def
    have hf : Measurable f :=
      hΦ'.comp (measurable_const.prodMk (hG.comp (measurable_id.add_const _)))
    have hf1 : ∀ v, f v ≤ 1 := fun v => h1 _
    have hk : Measurable fun ω' => ℓ (Z ω') + sh ω := hW.add_const _
    have i1 : ∫⁻ s, Φ (ω, G (ℓ s + a ω + b ω)) ∂(P.map Z) =
        ∫⁻ v, f v ∂(P.map fun ω' => ℓ (Z ω') + sh ω) := by
      rw [lintegral_map hf hk]
      refine (lintegral_map (μ := P)
        (hΨ1'.comp (measurable_const.prodMk measurable_id) :
          Measurable fun s => Φ (ω, G (ℓ s + a ω + b ω))) hZ).trans
        (lintegral_congr fun ω' => ?_)
      show Φ (ω, G (ℓ (Z ω') + a ω + b ω)) = f (ℓ (Z ω') + sh ω)
      rw [hsh]
    have i0 : ∫⁻ s, Φ (ω, G (ℓ s + a ω)) ∂(P.map Z) =
        ∫⁻ v, f v ∂(P.map fun ω' => ℓ (Z ω')) := by
      rw [lintegral_map hf hW]
      exact lintegral_map (μ := P)
        (hΨ0'.comp (measurable_const.prodMk measurable_id) :
          Measurable fun s => Φ (ω, G (ℓ s + a ω))) hZ
    set T := TV.tvDist (P.map fun ω' => ℓ (Z ω')) (P.map fun ω' => ℓ (Z ω') + sh ω)
    have hT : T ≤ min T 1 := le_min le_rfl TV.tvDist_le_one
    have hT' : TV.tvDist (P.map fun ω' => ℓ (Z ω') + sh ω) (P.map fun ω' => ℓ (Z ω')) ≤
        min T 1 := TV.tvDist_comm.le.trans hT
    rw [i1, i0]
    exact ⟨(TV.lintegral_le_lintegral_add_tvDist hf hf1).trans (add_le_add le_rfl hT'),
      (TV.lintegral_le_lintegral_add_tvDist hf hf1).trans (add_le_add le_rfl hT)⟩
  rw [e1, e0]
  constructor
  · calc _ ≤ ∫⁻ ω, (∫⁻ s, Φ (ω, G (ℓ s + a ω)) ∂(P.map Z) + min (TV.tvDist
          (P.map fun ω' => ℓ (Z ω')) (P.map fun ω' => ℓ (Z ω') + sh ω)) 1) ∂P :=
          lintegral_mono fun ω => (hpt ω).1
      _ = _ := lintegral_add_left hA0 _
  · calc _ ≤ ∫⁻ ω, (∫⁻ s, Φ (ω, G (ℓ s + a ω + b ω)) ∂(P.map Z) + min (TV.tvDist
          (P.map fun ω' => ℓ (Z ω')) (P.map fun ω' => ℓ (Z ω') + sh ω)) 1) ∂P :=
          lintegral_mono fun ω => (hpt ω).2
      _ = _ := lintegral_add_left hA1 _

end D3Plus
end QuantumZipper
