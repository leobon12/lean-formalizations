import QuantumZipper.Proofs.Zipper.D3PlusN2H2Free
import QuantumZipper.Proofs.Zipper.UnzipInvariance

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# N2-H2 on the restricted index from the per-index free-field identity (task N2H2-FREE)

`N2H2WinReprStmt` (`D3PlusN2H2WinCM.lean`) asks in its last clause for an almost-sure equality of
the whole window processes `latWinFreeW K a X ω = G (…)` (all indices at once). Only the laws of
these processes enter `n2H2HarmWin_of_repr`, and the law of a process indexed by `WinIdx K` (product
σ-algebra) is determined by its finite-dimensional marginals, so the per-index form suffices
(`UnzipInvariance.map_eq_of_forall_ae_eq`). Here:

* `N2H2WinReprIStmt`: `N2H2WinReprStmt` with its last clause per index (`∀ i, ∀ᵐ ω`);
* `n2H2HarmWin_of_reprI : N2H2WinReprIStmt → N2H2HarmWinStmt` (the proof of
  `n2H2HarmWin_of_repr`, with `Measure.map_congr` replaced by the marginal argument);
* `n2H2WinReprI_of_freeI : N2H2ReprFreeIStmt → N2H2WinReprIStmt` (the proof of
  `n2H2WinRepr_of_free`, per index);
* `n2H2HarmWinStmt_holds : N2H2HarmWinStmt` (with `n2H2ReprFreeIStmt_holds`).

Sources: Duplantier–Miller–Sheffield, arXiv:1409.7055, Prop. 4.7(ii), pp. 77–78; Cameron–Martin:
Berestycki–Powell arXiv:2004.04720, Lemmas 3.12, 3.14 (as in `D3PlusN2H2WinCM.lean`).
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal ENNReal

namespace QuantumZipper
namespace D3Plus

/-- **N2-H2 representation node, per-index form** (last clause per window index). -/
def N2H2WinReprIStmt : Prop :=
  ∀ (r : ℝ) (K : ℕ) {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (X : Ω → FieldSample), 0 < r → IsFreeGFFModConstH X P →
    ∃ hd : Ω → ℂ → ℝ, (∀ᵐ ω ∂P, AdmCorr r (hd ω) ∧ hd ω 0 = 0) ∧
      ∀ ε : ℝ, 0 < ε → ε ≤ r → ∃ b : Ω → LocIdx ε → ℝ, Measurable[K3.outsideSigma X 0 r] b ∧
        ∀ᶠ a in 𝓝[>] (0 : ℝ), ∃ G : (LocIdx ε → ℝ) → (WinIdx K → ℝ), Measurable G ∧
          (∀ᵐ ω ∂P, ∀ v, G (v + b ω) = G (v + pairShift ε (hd ω))) ∧
          (∀ᵐ ω ∂P, latWinW K a (n2LatY X r ω) = G (resField ε (locZField X r ω))) ∧
          (∀ i, ∀ᵐ ω ∂P, latWinFreeW K a X ω i = G (resField ε (locZField X r ω) + b ω) i)

/-- **N2-H2 on the restricted index from the per-index representation node.** -/
theorem n2H2HarmWin_of_reprI (hR : N2H2WinReprIStmt) : N2H2HarmWinStmt := by
  intro r K Ω _ P _ X hr hX
  obtain ⟨hd, hhd, hrest⟩ := hR r K P X hr hX
  set c : ℝ → Ω → ℝ≥0∞ := fun ε ω => min (TV.tvDist
      (P.map fun ω' => resField ε (locZField X r ω'))
      (P.map fun ω' => resField ε (locZField X r ω') + pairShift ε (hd ω))) 1 with hc_def
  have hc : ∀ᵐ ω ∂P, Tendsto (fun ε => c ε ω) (𝓝[>] 0) (𝓝 0) := by
    filter_upwards [hhd] with ω hω
    have h := d3PlusIN2FixCMLoc_of_parts cmIncrStmt_holds n2Cutoff_holds r P X (hd ω) hr hX
      hω.1 hω.2
    simpa using h.min (tendsto_const_nhds (x := (1 : ℝ≥0∞)))
  have hlim : Tendsto (fun L : ℝ => ∫⁻ ω, c L⁻¹ ω ∂P) atTop (𝓝 0) :=
    tendsto_lintegral_of_ae_tendsto_nonmeas (fun L ω => c L⁻¹ ω)
      (fun _ _ => min_le_right _ _) (by
        filter_upwards [hc] with ω hω
        exact hω.comp (tendsto_nhdsWithin_iff.2 ⟨tendsto_inv_atTop_zero,
          (eventually_gt_atTop 0).mono fun x hx => inv_pos.2 hx⟩))
  rw [ENNReal.tendsto_nhds_zero]
  intro η hη
  obtain ⟨L₀, hL₀, hL₀r⟩ := ((hlim.eventually (gt_mem_nhds hη)).and
    (eventually_ge_atTop (max r⁻¹ 1))).exists
  have hL₀pos : 0 < L₀ := lt_of_lt_of_le one_pos ((le_max_right _ _).trans hL₀r)
  have hε : 0 < L₀⁻¹ := inv_pos.2 hL₀pos
  have hεr : L₀⁻¹ ≤ r := inv_le_of_inv_le₀ hr ((le_max_left _ _).trans hL₀r)
  obtain ⟨b, hb, hev⟩ := hrest L₀⁻¹ hε hεr
  filter_upwards [hev] with a ha
  obtain ⟨G, hG, hsh, hM, hF⟩ := ha
  have hle : K3.outsideSigma X 0 r ≤ ‹MeasurableSpace Ω› :=
    iSup_le fun _ => ((hX.measurable_coord _).sub (hX.measurable_coord _)).comap_le
  have h1 : Measurable fun ω => resField L₀⁻¹ (locZField X r ω) :=
    (measurable_resField _).comp (measurable_locZField hX hr)
  have h2 : Measurable b := hb.mono hle le_rfl
  have hsum : Measurable fun ω => resField L₀⁻¹ (locZField X r ω) + b ω :=
    measurable_pi_iff.2 fun μ => ((measurable_pi_apply μ).comp h1).add
      ((measurable_pi_apply μ).comp h2)
  rw [Measure.map_congr hM, UnzipInvariance.map_eq_of_forall_ae_eq
    (measurable_latWinFreeW hX.measurable_coord K a) (hG.comp hsum) hF]
  exact (tvDist_map_shift_le_win hX hr hG hb _ hsh).trans hL₀.le

/-- **Reduction of the per-index representation node** to the per-index free-field identity
(the proof of `n2H2WinRepr_of_free`, per index in the last clause). -/
theorem n2H2WinReprI_of_freeI (hF : N2H2ReprFreeIStmt) : N2H2WinReprIStmt := by
  intro r K Ω _ P _ X hr hX
  have hA := ae_reprHarmAt (P := P) hX hr
  refine ⟨reprHd X r, ?_, fun ε hε hεr => ⟨reprB X r ε, measurable_reprB hr hεr, ?_⟩⟩
  · filter_upwards [hA] with ω hω
    obtain ⟨hc, ⟨ρ, hρ, hh⟩, -, -⟩ := hω
    refine ⟨⟨hc.sub continuousOn_const, ρ, hρ,
      hh.sub (InnerProductSpace.harmonicOnNhd_const _)⟩, ?_⟩
    show reprH X r ω 0 - reprH X r ω 0 = 0
    exact sub_self _
  · have h1 : ∀ᶠ a in 𝓝 (0 : ℝ), a * K < ε := by
      have : Tendsto (fun a : ℝ => a * K) (𝓝 0) (𝓝 0) := by
        simpa using (tendsto_id (x := 𝓝 (0 : ℝ))).mul_const (K : ℝ)
      exact this.eventually (gt_mem_nhds hε)
    filter_upwards [self_mem_nhdsWithin, nhdsWithin_le_nhds h1] with a ha haK
    have ha' : 0 < a := ha
    have hsupp := fun i => winIdx_map_compl K i ha'
    refine ⟨reprG K a ε, measurable_reprG K a ε, ?_, ?_, ?_⟩
    · filter_upwards [hA] with ω hω
      obtain ⟨hc, -, h0, hdec⟩ := hω
      intro v
      funext i
      refine evalReg_reprY (y := extLoc ε (v + pairShift ε (reprHd X r ω))) ?_ ?_ (hsupp i) haK
      · intro μ hμ
        have hloc := isLocalH_of_mem_reprCirc hμ
        obtain ⟨p, hp, hp0, hpε, rfl⟩ := hμ
        simp only [extLoc, dif_pos hloc, Pi.add_apply]
        congr 1
        have hint : Integrable (reprH X r ω) (foldedCircle p.1 p.2) :=
          integrable_of_admCorr (r := r) le_rfl hc
            ⟨_, isLocalH_foldedCircle_repr hp0 (hpε.trans_le hεr)⟩
        simp only [reprB, pairShift, reprHd, measure_univ, ite_true]
        rw [integral_sub hint (integrable_const _), integral_const, Measure.real, measure_univ,
          ENNReal.toReal_one, one_smul, ← hdec p hp hp0 (hpε.trans_le hεr), h0]
      · intro c hc
        unfold reprY
        rw [if_pos hc]
    · filter_upwards with ω
      funext i
      symm
      exact evalReg_reprY (y := locZField X r ω)
        (fun μ hμ => extLoc_resField_of_local _ (isLocalH_of_mem_reprCirc hμ))
        (fun c hc => by unfold n2LatY; rw [if_pos (isLocalH_mono_repr hεr hc)]) (hsupp i) haK
    · intro i
      filter_upwards [hF K P X hX (fun ω => X ω (K3.halfDiscPoisson 0 r ((0 : ℝ) : ℂ))) a ha' i]
        with ω hω
      rw [← hω]
      symm
      refine evalReg_reprY
        (y := fun μ => X ω μ - (μ Set.univ).toReal * X ω (K3.halfDiscPoisson 0 r ((0 : ℝ) : ℂ)))
        (Y := lateralPart fun μ =>
          X ω μ - (μ Set.univ).toReal * X ω (K3.halfDiscPoisson 0 r ((0 : ℝ) : ℂ)))
        ?_ (fun _ _ => rfl) (hsupp i) haK
      intro μ hμ
      have hloc := isLocalH_of_mem_reprCirc hμ
      obtain ⟨p, hp, hp0, hpε, rfl⟩ := hμ
      simp only [extLoc, dif_pos hloc, Pi.add_apply, resField, reprB, measure_univ, ite_true,
        ENNReal.toReal_one, one_mul]
      rw [locZField_apply_of_local X ω (isLocalH_mono_repr hεr hloc)]
      simp only [K3.markovZ]
      ring

/-- **N2-H2 on the restricted index (D36 form of `N2HLatTVStmt`'s model side): PROVED.** -/
theorem n2H2HarmWinStmt_holds : N2H2HarmWinStmt :=
  n2H2HarmWin_of_reprI (n2H2WinReprI_of_freeI n2H2ReprFreeIStmt_holds)

end D3Plus
end QuantumZipper
