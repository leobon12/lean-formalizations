import QuantumZipper.Proofs.Zipper.D3PlusLSCZLoc
import QuantumZipper.Proofs.Zipper.D3PlusIIRich

/-!
# D3⁺(ii), part vanishing at `0`: `LSCZeroGen locFieldFull` holds (task LSCZERO-CORE)

**`lscZeroGen_locFieldFull : LSCZeroGen locFieldFull`**, hence
`d3PlusIIRich_of_lscConst : LSCConstGen locFieldFull → D3PlusIIStmtRich`.

Proof (D24; Sheffield arXiv:1012.4797, proof of Prop. 1.6, p. 25, "approximately constant";
Cameron–Martin: Berestycki–Powell arXiv:2004.04720, Lemmas 3.12, 3.14, p. 79). The comparison is
made on the diagonal (the same `ω` for `g` and `g'`), so no frozen-correction model is needed:

1. For each `ω`, `h_ω = g' ω − g ω` is admissible with `h_ω(0) = 0`; the local CM bound
   (`d3PlusIN2FixCMLoc_of_parts cmIncrStmt_holds n2Cutoff_holds`) gives
   `c(ε, ω) = d_TV(law Z|_ε, law Z|_ε + ∫ h_ω) → 0` as `ε → 0⁺`; by dominated convergence for
   lower integrals (`tendsto_lintegral_of_ae_tendsto_nonmeas`) fix `ε ≤ r` with
   `∫⁻ min(c(ε, ·), 1) < η/2`.
2. Off the bad-scale events of `g` and `g'` at threshold `ε/(R+2)` (probability `→ 0`, D3⁺(iii),
   `tendsto_prob_badScale`), both zoomed pairs are `lsczG` of `Z|_ε + a` and `Z|_ε + a + b`
   (`zoomGen_eq_lsczG_of_not_bad`), with `a, b` read from the macroscopic data (`condSigma`-
   measurable), and on the circles `b = ∫ h_ω` (`macroF_sub_eq_integral`).
3. `lscz_lintegral_shift_le` (independence `indep_localZ_condSigma` + TV duality) bounds the
   difference of the two expectations by `∫⁻ min(c(ε, ·), 1)`.

The hypothesis `|g − g'| ≤ K` of `LSCZeroGen` is not needed. Own elementary assembly of proved
inputs (AGENT_GUIDE cost rule).
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal ENNReal

namespace QuantumZipper
namespace D3Plus

theorem lscz_meas_add {Ω : Type*} {m : MeasurableSpace Ω} {F : Ω → FieldSample}
    (hF : Measurable[m] F) {ε : ℝ} (c : ℝ) :
    Measurable[m] fun ω (μ : LocIdx ε) => F ω μ.1 + c :=
  measurable_pi_iff.2 fun μ => ((measurable_pi_apply μ.1).comp hF).add_const c

theorem lscz_meas_sub {Ω : Type*} {m : MeasurableSpace Ω} {F F' : Ω → FieldSample}
    (hF : Measurable[m] F) (hF' : Measurable[m] F') {ε : ℝ} :
    Measurable[m] fun ω (μ : LocIdx ε) => F ω μ.1 - F' ω μ.1 :=
  measurable_pi_iff.2 fun μ => ((measurable_pi_apply μ.1).comp hF).sub
    ((measurable_pi_apply μ.1).comp hF')

/-- **D3⁺(ii), part vanishing at `0`, for D25's rich local data.** -/
theorem lscZeroGen_locFieldFull : LSCZeroGen locFieldFull := by
  intro γ α r ρ₀ Ω _ P _ X E' _ Ξ g g' K hS hS' h0 _hK R η hη
  have hm := condSigma_le hS
  have hZ : Measurable (localZ X r) := measurable_localZ hS.hX hS.hr
  have hind := indep_localZ_condSigma hS
  set hd : Ω → ℂ → ℝ := fun ω z => g' ω z - g ω z with hd_def
  set c : ℝ → Ω → ℝ≥0∞ := fun ε ω => TV.tvDist
      (P.map fun ω' => resField ε (extLoc r (localZ X r ω')))
      (P.map fun ω' => resField ε (extLoc r (localZ X r ω')) + pairShift ε (hd ω)) with hc_def
  have hc : ∀ ω, Tendsto (fun ε => c ε ω) (𝓝[>] 0) (𝓝 0) := fun ω =>
    d3PlusIN2FixCMLoc_of_parts cmIncrStmt_holds n2Cutoff_holds r P X (hd ω) hS.hr hS.hX
      (admCorr_sub (admCorr_of_setup hS ω) (admCorr_of_setup hS' ω)) (by simp [hd_def, h0])
  have hlim : Tendsto (fun L : ℝ => ∫⁻ ω, min (c L⁻¹ ω) 1 ∂P) atTop (𝓝 0) :=
    tendsto_lintegral_of_ae_tendsto_nonmeas (fun L ω => min (c L⁻¹ ω) 1)
      (fun _ _ => min_le_right _ _) (ae_of_all _ fun ω => by
        simpa using ((hc ω).comp (tendsto_nhdsWithin_iff.2 ⟨tendsto_inv_atTop_zero,
          (eventually_gt_atTop 0).mono fun x hx => inv_pos.2 hx⟩)).min
          (tendsto_const_nhds (x := (1 : ℝ≥0∞))))
  have hη2 : 0 < η / 2 := ENNReal.half_pos hη.ne'
  have hη4 : 0 < η / 2 / 2 := ENNReal.half_pos hη2.ne'
  obtain ⟨L₀, hL₀, hL₀r⟩ := ((hlim.eventually (gt_mem_nhds hη2)).and
    (eventually_ge_atTop (max r⁻¹ 1))).exists
  have hL₀pos : 0 < L₀ := lt_of_lt_of_le one_pos ((le_max_right _ _).trans hL₀r)
  have hε : 0 < L₀⁻¹ := inv_pos.2 hL₀pos
  have hεr : L₀⁻¹ ≤ r := inv_le_of_inv_le₀ hS.hr ((le_max_left _ _).trans hL₀r)
  have hδ : 0 < L₀⁻¹ / (R + 2) := by positivity
  set B : ℝ → Set Ω := fun L => badScale γ α r (L₀⁻¹ / (R + 2)) ρ₀ X g L ∪
    badScale γ α r (L₀⁻¹ / (R + 2)) ρ₀ X g' L with hB_def
  have hB : Tendsto (fun L => P (B L)) atTop (𝓝 0) := by
    have h1 := tendsto_prob_badScale hS hδ (nullMeasurableSet_badScale hS _)
    have h2 := tendsto_prob_badScale hS' hδ (nullMeasurableSet_badScale hS' _)
    have h12 := h1.add h2
    rw [add_zero] at h12
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds h12
      (fun L => bot_le) (fun L => measure_union_le _ _)
  filter_upwards [hB.eventually (gt_mem_nhds hη4)] with L hBL Φ hΦ h1
  dsimp only
  set ε := L₀⁻¹ with hε_def
  set ℓ : (LocIdx r → ℝ) → LocIdx ε → ℝ := fun s => resField ε (extLoc r s) with hℓ_def
  have hℓ : Measurable ℓ := (measurable_resField ε).comp (measurable_extLoc r)
  set a : Ω → LocIdx ε → ℝ := fun ω μ => macroF α r ρ₀ X g ω μ.1 + L / γ with ha_def
  set b : Ω → LocIdx ε → ℝ := fun ω μ => macroF α r ρ₀ X g' ω μ.1 - macroF α r ρ₀ X g ω μ.1
    with hb_def
  have ha : Measurable[condSigma Ξ X r] a := lscz_meas_add (measurable_macroF hS) _
  have hb : Measurable[condSigma Ξ X r] b :=
    lscz_meas_sub (measurable_macroF hS') (measurable_macroF hS)
  have hsh : ∀ ω v, lsczG γ ε R (v + a ω + b ω) =
      lsczG γ ε R (v + pairShift ε (hd ω) + a ω) := by
    intro ω v
    refine lsczG_congr fun μ hμ => ?_
    have e := macroF_sub_eq_integral hS hS' ω (circSet_mono hεr hμ)
    simp only [Pi.add_apply, hb_def, pairShift, hd_def, e]
    ring
  obtain ⟨k1, k2⟩ := lscz_lintegral_shift_le hm hZ hind hℓ (measurable_lsczG γ ε R) ha hb
    (fun ω => pairShift ε (hd ω)) hsh hΦ h1
  have hM : ∫⁻ ω, min (TV.tvDist (P.map fun ω' => ℓ (localZ X r ω'))
      (P.map fun ω' => ℓ (localZ X r ω') + pairShift ε (hd ω))) 1 ∂P ≤ η / 2 := hL₀.le
  have a1 := lintegral_le_add_of_eq_off (P := P)
    (u := fun ω => Φ (ω, zoomGen locFieldFull γ α L r R ρ₀ (X ω) (g ω)))
    (v := fun ω => Φ (ω, lsczG γ ε R (ℓ (localZ X r ω) + a ω))) (fun ω => h1 _) (B L)
    (ae_of_all _ fun ω hω => by
      rw [zoomGen_eq_lsczG_of_not_bad hS hε hεr (v := ℓ (localZ X r ω) + a ω)
        (fun h => hω (Or.inl h)) fun μ _ => rfl])
  have a2 := lintegral_le_add_of_eq_off (P := P)
    (v := fun ω => Φ (ω, zoomGen locFieldFull γ α L r R ρ₀ (X ω) (g ω)))
    (u := fun ω => Φ (ω, lsczG γ ε R (ℓ (localZ X r ω) + a ω))) (fun ω => h1 _) (B L)
    (ae_of_all _ fun ω hω => by
      rw [zoomGen_eq_lsczG_of_not_bad hS hε hεr (v := ℓ (localZ X r ω) + a ω)
        (fun h => hω (Or.inl h)) fun μ _ => rfl])
  have hv' : ∀ ω, ∀ μ : LocIdx ε, μ.1 ∈ circSet ε → (ℓ (localZ X r ω) + a ω + b ω) μ =
      resField ε (locZField X r ω) μ + (macroF α r ρ₀ X g' ω μ.1 + L / γ) := by
    intro ω μ _
    simp only [Pi.add_apply, hℓ_def, ha_def, hb_def, locZField]
    ring
  have b1 := lintegral_le_add_of_eq_off (P := P)
    (u := fun ω => Φ (ω, zoomGen locFieldFull γ α L r R ρ₀ (X ω) (g' ω)))
    (v := fun ω => Φ (ω, lsczG γ ε R (ℓ (localZ X r ω) + a ω + b ω))) (fun ω => h1 _) (B L)
    (ae_of_all _ fun ω hω => by
      rw [zoomGen_eq_lsczG_of_not_bad hS' hε hεr (fun h => hω (Or.inr h)) (hv' ω)])
  have b2 := lintegral_le_add_of_eq_off (P := P)
    (v := fun ω => Φ (ω, zoomGen locFieldFull γ α L r R ρ₀ (X ω) (g' ω)))
    (u := fun ω => Φ (ω, lsczG γ ε R (ℓ (localZ X r ω) + a ω + b ω))) (fun ω => h1 _) (B L)
    (ae_of_all _ fun ω hω => by
      rw [zoomGen_eq_lsczG_of_not_bad hS' hε hεr (fun h => hω (Or.inr h)) (hv' ω)])
  set IV := ∫⁻ ω, Φ (ω, zoomGen locFieldFull γ α L r R ρ₀ (X ω) (g ω)) ∂P
  set IV' := ∫⁻ ω, Φ (ω, zoomGen locFieldFull γ α L r R ρ₀ (X ω) (g' ω)) ∂P
  set IU := ∫⁻ ω, Φ (ω, lsczG γ ε R (ℓ (localZ X r ω) + a ω)) ∂P
  set IU' := ∫⁻ ω, Φ (ω, lsczG γ ε R (ℓ (localZ X r ω) + a ω + b ω)) ∂P
  set M := ∫⁻ ω, min (TV.tvDist (P.map fun ω' => ℓ (localZ X r ω'))
      (P.map fun ω' => ℓ (localZ X r ω') + pairShift ε (hd ω))) 1 ∂P
  have hsum : η / 2 / 2 + η / 2 + η / 2 / 2 = η := by
    rw [add_right_comm, ENNReal.add_halves, ENNReal.add_halves]
  constructor
  · calc IV ≤ IU + P (B L) := a1
      _ ≤ IU' + M + P (B L) := by gcongr
      _ ≤ IV' + P (B L) + M + P (B L) := by gcongr
      _ ≤ IV' + η / 2 / 2 + η / 2 + η / 2 / 2 := by gcongr
      _ = IV' + η := by rw [add_assoc, add_assoc, ← add_assoc (η / 2 / 2), hsum]
  · calc IV' ≤ IU' + P (B L) := b1
      _ ≤ IU + M + P (B L) := by gcongr
      _ ≤ IV + P (B L) + M + P (B L) := by gcongr
      _ ≤ IV + η / 2 / 2 + η / 2 + η / 2 / 2 := by gcongr
      _ = IV + η := by rw [add_assoc, add_assoc, ← add_assoc (η / 2 / 2), hsum]

/-- **Rich D3⁺(ii) from its constant (level-shift) part alone.** -/
theorem d3PlusIIRich_of_lscConst (hC : LSCConstGen locFieldFull) : D3PlusIIStmtRich :=
  d3PlusIIRich_of_const_zero hC lscZeroGen_locFieldFull

end D3Plus
end QuantumZipper
