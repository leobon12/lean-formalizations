import QuantumZipper.Proofs.Zipper.D3PlusLSCCCore

/-!
# D3⁺(ii), constant part: `LSCConstGen locFieldFull` from the deterministic node `LSCCTmStmt`

Task LSCCONST. **`lscConstGen_locFieldFull_of_tm : LSCCTmStmt → LSCConstGen locFieldFull`.**

Proof (Sheffield arXiv:1012.4797, proof of Prop. 1.6, p. 25: conditionally on the macroscopic
data the model is the local part plus a deterministic correction; own elementary glue):

1. Off the bad-scale event of `g` at level `L` (resp. at level `L + γ c ω`, which is the bad-scale
   event of the `Setup` correction `g + c` at level `L`, `zoomModel_add_const`), the zoomed pair is
   `pairN1 L (localZ, F ω)` (resp. `pairN1 (L + γ c ω) (localZ, F ω) = pairN1 L (localZ, F ω + c ω)`,
   `locModel_level_shift`), `F = macroF` (`zoomGen_eq_pairN1_of_not_bad`).
2. `lscc_lintegral_factor_le` bounds the difference of the two expectations by the lower integral
   of `min(d_L(ω), 1)`, `d_L(ω)` the TV distance of the two frozen-`ω` laws.
3. For a.e. `ω`, `F ω` is circle data of an admissible `φ_ω` (`d3PlusIN2FixMacro_of_harm
   d3PlusN2HarmPart_holds`), so `d_L(ω)` is the TV distance of `LSCCTmStmt` with `c = γ c ω`,
   which tends to `0`; dominated convergence for lower integrals
   (`tendsto_lintegral_of_ae_tendsto_nonmeas`) and D3⁺(iii) (`tendsto_prob_badScale`) conclude.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal ENNReal

namespace QuantumZipper
namespace D3Plus

theorem lscc_meas_add_const {Ω : Type*} {m : MeasurableSpace Ω} {F : Ω → FieldSample}
    (hF : Measurable[m] F) {c : Ω → ℝ} (hc : Measurable[m] c) :
    Measurable[m] fun ω (μ : Measure ℂ) => F ω μ + c ω := by
  refine @measurable_fieldSample_of Ω m _ fun μ => ?_
  exact Measurable.add (m := m) ((measurable_pi_apply μ).comp hF) hc

/-- **The constant (level-shift) part of D3⁺(ii) for the rich data, from the deterministic
node.** -/
theorem lscConstGen_locFieldFull_of_tm (hT : LSCCTmStmt) : LSCConstGen locFieldFull := by
  intro γ α r ρ₀ Ω _ P _ X E' _ Ξ g c K hS hc _hcK R η hη
  have hγ : γ ≠ 0 := hS.hγ.ne'
  have hm := condSigma_le hS
  have hZ : Measurable (localZ X r) := measurable_localZ hS.hX hS.hr
  have hind := indep_localZ_condSigma hS
  set F : Ω → FieldSample := macroF α r ρ₀ X g with hF_def
  have hF : Measurable[condSigma Ξ X r] F := measurable_macroF hS
  set F2 : Ω → FieldSample := fun ω μ => F ω μ + c ω with hF2_def
  have hF2 : Measurable[condSigma Ξ X r] F2 := lscc_meas_add_const hF hc
  set d : ℝ → Ω → ℝ≥0∞ := fun L ω => min (TV.tvDist
      ((P.map (localZ X r)).map fun s => pairN1 γ r R L (s, F ω))
      ((P.map (localZ X r)).map fun s => pairN1 γ r R L (s, F2 ω))) 1 with hd_def
  have hd : ∀ᵐ ω ∂P, Tendsto (fun L => d L ω) atTop (𝓝 0) := by
    filter_upwards [d3PlusIN2FixMacro_of_harm d3PlusN2HarmPart_holds γ α r ρ₀ P X Ξ g hS]
      with ω hω
    obtain ⟨φ, hφ, hdec⟩ := hω
    have h := hT γ α r P X φ (γ * c ω) hS.hγ hS.hγ2 hS.hα hS.hr hS.hX hφ R
    have e : ∀ L, TV.tvDist
        ((P.map (localZ X r)).map fun s => pairN1 γ r R L (s, F ω))
        ((P.map (localZ X r)).map fun s => pairN1 γ r R L (s, F2 ω)) =
        TV.tvDist (P.map fun ω' => pairN1 γ r R L (localZ X r ω', circData α φ))
          (P.map fun ω' => pairN1 γ r R (L + γ * c ω) (localZ X r ω', circData α φ)) := by
      intro L
      have hm1 : Measurable fun s => pairN1 γ r R L (s, F ω) :=
        (measurable_pairN1 γ r R L).comp (measurable_id.prodMk measurable_const)
      have hm2 : Measurable fun s => pairN1 γ r R L (s, F2 ω) :=
        (measurable_pairN1 γ r R L).comp (measurable_id.prodMk measurable_const)
      have e1 : (fun s => pairN1 γ r R L (s, F ω)) ∘ localZ X r =
          fun ω' => pairN1 γ r R L (localZ X r ω', circData α φ) :=
        funext fun ω' => pairN1_congr (locModel_congr_circ fun μ hμ => (hdec μ hμ).2)
      have e2 : (fun s => pairN1 γ r R L (s, F2 ω)) ∘ localZ X r =
          fun ω' => pairN1 γ r R (L + γ * c ω) (localZ X r ω', circData α φ) := by
        funext ω'
        refine pairN1_congr ?_
        rw [locModel_level_shift hγ]
        exact locModel_congr_circ fun μ hμ => by
          show F ω μ + c ω = circData α φ μ + c ω
          rw [hF_def, (hdec μ hμ).2]
          rfl
      rw [Measure.map_map hm1 hZ, Measure.map_map hm2 hZ, e1, e2]
    have h' := (h.congr fun L => (e L).symm).min (tendsto_const_nhds (x := (1 : ℝ≥0∞)))
    simpa [hd_def] using h'
  have hlim : Tendsto (fun L => ∫⁻ ω, d L ω ∂P) atTop (𝓝 0) :=
    tendsto_lintegral_of_ae_tendsto_nonmeas d (fun _ _ => min_le_right _ _) hd
  have hε0 : 0 < r / (R + 1) := div_pos hS.hr (by positivity)
  have hS2 := hS.add_const hc
  set B1 : ℝ → Set Ω := fun L => badScale γ α r (r / (R + 1)) ρ₀ X g L with hB1_def
  set B2 : ℝ → Set Ω := fun L =>
    badScale γ α r (r / (R + 1)) ρ₀ X (fun ω z => g ω z + c ω) L with hB2_def
  have hB1 : Tendsto (fun L => P (B1 L)) atTop (𝓝 0) :=
    tendsto_prob_badScale hS hε0 (nullMeasurableSet_badScale hS _)
  have hB2 : Tendsto (fun L => P (B2 L)) atTop (𝓝 0) :=
    tendsto_prob_badScale hS2 hε0 (nullMeasurableSet_badScale hS2 _)
  have hB2' : ∀ L ω, ω ∉ B2 L → ω ∉ badScale γ α r (r / (R + 1)) ρ₀ X g (L + γ * c ω) := by
    intro L ω h
    simpa only [hB2_def, badScale, Set.mem_ofPred_eq, zoomModel_add_const hγ] using h
  have hη2 : 0 < η / 2 := ENNReal.half_pos hη.ne'
  have hη4 : 0 < η / 2 / 2 := ENNReal.half_pos hη2.ne'
  filter_upwards [hB1.eventually (gt_mem_nhds hη4), hB2.eventually (gt_mem_nhds hη4),
    hlim.eventually (gt_mem_nhds hη2)] with L hL1 hL2 hL3 Φ hΦ h1
  dsimp only
  obtain ⟨k1, k2⟩ := lscc_lintegral_factor_le hm hZ hind hF hF2 (measurable_pairN1 γ r R L) hΦ h1
  have hU : ∀ ω, ω ∉ B1 L → zoomGen locFieldFull γ α L r R ρ₀ (X ω) (g ω) =
      pairN1 γ r R L (localZ X r ω, F ω) := fun ω hω =>
    zoomGen_eq_pairN1_of_not_bad hS L ω hω
  have hU' : ∀ ω, ω ∉ B2 L → zoomGen locFieldFull γ α (L + γ * c ω) r R ρ₀ (X ω) (g ω) =
      pairN1 γ r R L (localZ X r ω, F2 ω) := fun ω hω =>
    (zoomGen_eq_pairN1_of_not_bad hS (L + γ * c ω) ω (hB2' L ω hω)).trans
      (pairN1_congr (locModel_level_shift hγ L r (c ω) _ _))
  have a1 := lintegral_le_add_of_eq_off (P := P)
    (u := fun ω => Φ (ω, zoomGen locFieldFull γ α L r R ρ₀ (X ω) (g ω)))
    (v := fun ω => Φ (ω, pairN1 γ r R L (localZ X r ω, F ω))) (fun ω => h1 _) (B1 L)
    (ae_of_all _ fun ω hω => by rw [hU ω hω])
  have a2 := lintegral_le_add_of_eq_off (P := P)
    (v := fun ω => Φ (ω, zoomGen locFieldFull γ α L r R ρ₀ (X ω) (g ω)))
    (u := fun ω => Φ (ω, pairN1 γ r R L (localZ X r ω, F ω))) (fun ω => h1 _) (B1 L)
    (ae_of_all _ fun ω hω => by rw [hU ω hω])
  have b1 := lintegral_le_add_of_eq_off (P := P)
    (u := fun ω => Φ (ω, zoomGen locFieldFull γ α (L + γ * c ω) r R ρ₀ (X ω) (g ω)))
    (v := fun ω => Φ (ω, pairN1 γ r R L (localZ X r ω, F2 ω))) (fun ω => h1 _) (B2 L)
    (ae_of_all _ fun ω hω => by rw [hU' ω hω])
  have b2 := lintegral_le_add_of_eq_off (P := P)
    (v := fun ω => Φ (ω, zoomGen locFieldFull γ α (L + γ * c ω) r R ρ₀ (X ω) (g ω)))
    (u := fun ω => Φ (ω, pairN1 γ r R L (localZ X r ω, F2 ω))) (fun ω => h1 _) (B2 L)
    (ae_of_all _ fun ω hω => by rw [hU' ω hω])
  set IV := ∫⁻ ω, Φ (ω, zoomGen locFieldFull γ α L r R ρ₀ (X ω) (g ω)) ∂P
  set IV' := ∫⁻ ω, Φ (ω, zoomGen locFieldFull γ α (L + γ * c ω) r R ρ₀ (X ω) (g ω)) ∂P
  set IU := ∫⁻ ω, Φ (ω, pairN1 γ r R L (localZ X r ω, F ω)) ∂P
  set IU' := ∫⁻ ω, Φ (ω, pairN1 γ r R L (localZ X r ω, F2 ω)) ∂P
  set M := ∫⁻ ω, d L ω ∂P
  have hsum : η / 2 / 2 + η / 2 + η / 2 / 2 = η := by
    rw [add_right_comm, ENNReal.add_halves, ENNReal.add_halves]
  constructor
  · calc IV ≤ IU + P (B1 L) := a1
      _ ≤ IU' + M + P (B1 L) := by gcongr
      _ ≤ IV' + P (B2 L) + M + P (B1 L) := by gcongr
      _ ≤ IV' + η / 2 / 2 + η / 2 + η / 2 / 2 := by gcongr
      _ = IV' + η := by rw [add_assoc, add_assoc, ← add_assoc (η / 2 / 2), hsum]
  · calc IV' ≤ IU' + P (B2 L) := b1
      _ ≤ IU + M + P (B2 L) := by gcongr
      _ ≤ IV + P (B1 L) + M + P (B2 L) := by gcongr
      _ ≤ IV + η / 2 / 2 + η / 2 + η / 2 / 2 := by gcongr
      _ = IV + η := by rw [add_assoc, add_assoc, ← add_assoc (η / 2 / 2), hsum]

end D3Plus
end QuantumZipper
