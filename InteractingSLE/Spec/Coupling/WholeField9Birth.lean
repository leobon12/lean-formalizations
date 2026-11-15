/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Coupling.WholeField9Mean
import InteractingSLE.Spec.Coupling.WholeField7Birth

/-!
# C.4 for every `κ > 0`: the pocket step at a birth, in conditional-mean form

Packet PROVE-WHOLEFIELD9 (follow-up note C.3–C.4, `source/external/AstraIG1/ig1_followup_proofs.txt` L1546–1704;
ruling R38).

The kernel value is written with the conditional mean (`cmKer`):

  `E[e^{i(h, ψ)} | 𝓕_τ] = exp(i E[(h, ψ) | 𝓕_τ] − ½ Q_{U_τ}(ψ))`.

**The birth step** (`ae_condExp_exp_eq_cmKer_of_birth`). Let `ψ = ψI + ψJ` with `supp ψI` swallowed at once at `β`
and `supp ψJ` earlier. If the identity holds, for every multiple `cψ`, at every bounded driving stop `τ < ζ` on an event
`Q τ` which holds on a left neighbourhood of `β`, then it holds at every bounded driving stop `σ ≥ β`. The proof is
PROVE-WHOLEFIELD7's (birth sequence, first positive term, birth transfer `ae_condExp_eq_of_birth`) with two changes:

* the kernel values converge because the conditional means converge (Lévy's upward theorem along the announcing stops,
  `ae_tendsto_condExp_real_of_announce`) and the retained Green energy is continuous (`WholeField9Path`); no bound on
  the mean is needed;
* the birth transfer gives `E[e^{ic(h,ψ)} | 𝓕_σ] = exp(i c E[(h,ψ) | 𝓕_T] − ½ c² Q)` at the birth stop `T`; this
  identity for all `c` **freezes the conditional mean**: `E[(h,ψ) | 𝓕_σ] = E[(h,ψ) | 𝓕_T]`
  (`ae_condExp_eq_of_condCharFun_on`).

If moreover the conditional mean of `ψ` vanishes on `Q τ`, it vanishes at `σ` (the second conclusion): this is the
harmonicity of the pocket means ("all preceding means annihilate Laplacians of tests. Their distributional limit does
also", C.3).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology Metric Complex
open scoped NNReal ENNReal

namespace InteractingSLE

namespace WholeField

open LQGMetric QuantumZipper LocalSets Ito Coupling

/-! ### The kernel value in conditional-mean form -/

section Ker

variable {Ω : Type*} {mΩ : MeasurableSpace Ω}

/-- **The Gaussian kernel value in conditional-mean form**: `exp(i E[(h,ψ) | m] − ½ Q_{U_t}(ψ))` at `ω`. -/
def cmKer (P : Measure Ω) (m : MeasurableSpace Ω) (h : Ω → DistOn upperHalfPlaneOpens) (W : ℝ≥0 → Ω → ℝ)
    (t : ℝ≥0) (ψ : TestOn upperHalfPlaneOpens) (ω : Ω) : ℂ :=
  WangWu.gaussCF ((P[fun ω' => h ω' ψ | m]) ω) (WangWu.retainedGreenEnergy (W · ω) t ψ)

/-- The retained Green energy is quadratic. -/
theorem retainedGreenEnergy_smul (w : ℝ≥0 → ℝ) (t : ℝ≥0) (c : ℝ) (φ : ℂ → ℝ) :
    WangWu.retainedGreenEnergy w t (c • φ) = c ^ 2 * WangWu.retainedGreenEnergy w t φ := by
  unfold WangWu.retainedGreenEnergy
  rw [← integral_const_mul]
  refine integral_congr_ae (Eventually.of_forall fun a => ?_)
  show (∫ b, (c • φ) a * WangWu.retainedGreen w t a b * (c • φ) b) =
    c ^ 2 * ∫ b, φ a * WangWu.retainedGreen w t a b * φ b
  rw [← integral_const_mul]
  refine integral_congr_ae (Eventually.of_forall fun b => ?_)
  simp only [Pi.smul_apply, smul_eq_mul]
  ring

theorem retainedGreenEnergy_testOn_smul (w : ℝ≥0 → ℝ) (t : ℝ≥0) (c : ℝ) (ψ : TestOn upperHalfPlaneOpens) :
    WangWu.retainedGreenEnergy w t ⇑(c • ψ) = c ^ 2 * WangWu.retainedGreenEnergy w t ψ := by
  rw [show (⇑(c • ψ) : ℂ → ℝ) = c • ⇑ψ from funext fun z => testOn_smul_apply c ψ z]
  exact retainedGreenEnergy_smul w t c ψ

theorem exp_pairing_smul (h : Ω → DistOn upperHalfPlaneOpens) (c : ℝ) (ψ : TestOn upperHalfPlaneOpens) :
    (fun ω' => cexp (I * (h ω' (c • ψ) : ℂ))) = fun ω' => cexp (I * ((c * h ω' ψ : ℝ) : ℂ)) := by
  funext ω'; rw [map_smul, smul_eq_mul]

theorem condExp_pairing_smul {P : Measure Ω} (m : MeasurableSpace Ω) (h : Ω → DistOn upperHalfPlaneOpens)
    (c : ℝ) (ψ : TestOn upperHalfPlaneOpens) :
    P[fun ω => h ω (c • ψ) | m] =ᵐ[P] fun ω => c * (P[fun ω => h ω ψ | m]) ω := by
  have e : (fun ω => h ω (c • ψ)) = c • fun ω => h ω ψ := by
    funext ω; simp [map_smul]
  rw [e]
  exact (condExp_smul c _ _).trans (Eventually.of_forall fun ω => by simp)

/-- `cmKer` of a multiple, in the form `exp(i c μ − ½ c² Q)`. -/
theorem ae_cmKer_smul {P : Measure Ω} (m : MeasurableSpace Ω) (h : Ω → DistOn upperHalfPlaneOpens)
    (W : ℝ≥0 → Ω → ℝ) (t : Ω → ℝ≥0) (c : ℝ) (ψ : TestOn upperHalfPlaneOpens) :
    ∀ᵐ ω ∂P, cmKer P m h W (t ω) (c • ψ) ω =
      cexp (I * ((c * (P[fun ω' => h ω' ψ | m]) ω : ℝ) : ℂ) -
        (((1 / 2) * (c ^ 2 * WangWu.retainedGreenEnergy (W · ω) (t ω) ψ) : ℝ) : ℂ)) := by
  filter_upwards [condExp_pairing_smul m h c ψ] with ω hω
  rw [cmKer, hω, retainedGreenEnergy_testOn_smul, WangWu.gaussCF]

end Ker

/-! ### Lévy's upward theorem for real variables along announcing stops -/

section Levy

universe v

variable {κ : ℝ} {nL nR : ℕ} {xL : Fin nL → ℝ} {xR : Fin nR → ℝ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ}
  {Ω : Type v} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P] {𝓕 : Filtration ℝ≥0 mΩ}
  {W : ℝ≥0 → Ω → ℝ} {VL : Fin nL → ℝ≥0 → Ω → ℝ} {VR : Fin nR → ℝ≥0 → Ω → ℝ} {B : ℝ≥0 → Ω → ℝ}
  {ζ : Ω → ℝ≥0∞} {h : Ω → DistOn upperHalfPlaneOpens}

/-- **Lévy's upward theorem along announcing stops, real version** (`ae_tendsto_condExp_of_announce`). -/
theorem ae_tendsto_condExp_real_of_announce (hC : IsOptionalHullCoupling κ xL xR ρL ρR P 𝓕 W VL VR B ζ h)
    (hκ : 0 < κ) {u₀ : ℂ → ℝ}
    (hu₀ : IsBoundedHarmonicExtension (forceBoundaryData κ ρL ρR xL xR) (forceJumpSet xL xR) u₀)
    (hX : IsMeasurableKilledDriving W VL VR ζ) {T : Ω → ℝ≥0}
    (hT : IsStoppingTime (drivingFiltration P hX) fun ω => (T ω : WithTop ℝ≥0))
    (hTζ : ∀ᵐ ω ∂P, (T ω : ℝ≥0∞) < ζ ω) (hT0 : ∀ᵐ ω ∂P, 0 < T ω ∨ ∀ i j, xL i < xR j)
    {ρ : ℕ → Ω → ℝ≥0} (hρ : ∀ n, IsStoppingTime (drivingFiltration P hX) fun ω => (ρ n ω : WithTop ℝ≥0))
    (hρm : ∀ ω, Monotone fun n => ρ n ω) (hρT : ∀ n ω, ρ n ω ≤ T ω)
    (hρlim : ∀ᵐ ω ∂P, Tendsto (fun n => ρ n ω) atTop (𝓝 (T ω))) {Y : Ω → ℝ} (hY : Integrable Y P) :
    ∀ᵐ ω ∂P, Tendsto (fun n => (P[Y | (hρ n).measurableSpace]) ω) atTop
      (𝓝 ((P[Y | hT.measurableSpace]) ω)) := by
  have hl := ae_tendsto_condExp_of_announce hC hκ hu₀ hX hT hTζ hT0 hρ hρm hρT hρlim hY.ofReal
  have hc : ∀ m : MeasurableSpace Ω, (fun ω => ((P[Y | m]) ω : ℂ)) =ᵐ[P] P[fun ω => (Y ω : ℂ) | m] :=
    fun m => Complex.ofRealCLM.comp_condExp_comm hY
  filter_upwards [hl, ae_all_iff.2 fun n => hc (hρ n).measurableSpace, hc hT.measurableSpace] with ω h1 h2 h3
  have h4 : Tendsto (fun n => ((P[Y | (hρ n).measurableSpace]) ω : ℂ)) atTop
      (𝓝 ((P[Y | hT.measurableSpace]) ω : ℂ)) := by
    rw [h3]; exact h1.congr fun n => (h2 n).symm
  have h5 := (Complex.continuous_re.tendsto _).comp h4
  simp only [Complex.ofReal_re] at h5
  exact h5.congr fun n => by simp [Function.comp]

end Levy

/-! ### The birth step -/

section Birth

universe v

variable {κ : ℝ} {nL nR : ℕ} {xL : Fin nL → ℝ} {xR : Fin nR → ℝ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ}
  {Ω : Type v} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P] {𝓕 : Filtration ℝ≥0 mΩ}
  {W : ℝ≥0 → Ω → ℝ} {VL : Fin nL → ℝ≥0 → Ω → ℝ} {VR : Fin nR → ℝ≥0 → Ω → ℝ} {B : ℝ≥0 → Ω → ℝ}
  {ζ : Ω → ℝ≥0∞} {h : Ω → DistOn upperHalfPlaneOpens}

/-- **C.4, the pocket step at a birth, in conditional-mean form** (every `κ > 0`). Let `ψ = ψI + ψJ`. Suppose that for
every real `c` the identity `E[e^{i(h, cψ)} | 𝓕_τ] = cmKer_τ(cψ)` holds at every bounded driving stop `τ < ζ` almost
surely on `{Q τ}` (`hIH`), and that `Q t` holds on a left neighbourhood of `β` whenever `Ev β` (`hQ`). Then:

1. for every `c`, at every bounded driving stop `σ < ζ`, almost surely, for every birth time `β ≤ σ` of `supp ψI`
   (with `supp ψJ` swallowed earlier) with `Ev β`, `E[e^{i(h, cψ)} | 𝓕_σ] = cmKer_σ(cψ)`;
2. if moreover `E[(h, ψ) | 𝓕_τ] = 0` on `{Q τ}` at every such `τ` (`hzero`), then `E[(h, ψ) | 𝓕_σ] = 0` almost surely
   on the same birth event. -/
theorem ae_condExp_exp_eq_cmKer_of_birth (hC : IsOptionalHullCoupling κ xL xR ρL ρR P 𝓕 W VL VR B ζ h)
    (hκ : 0 < κ) {u₀ : ℂ → ℝ}
    (hu₀ : IsBoundedHarmonicExtension (forceBoundaryData κ ρL ρR xL xR) (forceJumpSet xL xR) u₀)
    (hX : IsMeasurableKilledDriving W VL VR ζ) {σ : Ω → ℝ≥0}
    (hσ : IsStoppingTime (drivingFiltration P hX) fun ω => (σ ω : WithTop ℝ≥0))
    (hσζ : ∀ᵐ ω ∂P, (σ ω : ℝ≥0∞) < ζ ω) {N : ℝ≥0} (hσN : ∀ ω, σ ω ≤ N)
    (ψI ψJ : TestOn upperHalfPlaneOpens) (Q : ℝ≥0 → Ω → Prop) (Ev : Ω → ℝ≥0 → Prop)
    (hIH : ∀ c : ℝ, ∀ (τ : Ω → ℝ≥0) (hτ : IsStoppingTime (drivingFiltration P hX) fun ω => (τ ω : WithTop ℝ≥0)),
      (∀ᵐ ω ∂P, (τ ω : ℝ≥0∞) < ζ ω) → (∀ ω, τ ω ≤ N + 1) →
      ∀ᵐ ω ∂P, Q (τ ω) ω →
        (P[fun ω' => cexp (I * (h ω' (c • (ψI + ψJ)) : ℂ)) | hτ.measurableSpace]) ω =
          cmKer P hτ.measurableSpace h W (τ ω) (c • (ψI + ψJ)) ω)
    (hQ : ∀ ω β, 0 < β → Ev ω β → ∃ t₀ < β, ∀ t, t₀ ≤ t → t < β → Q t ω) :
    (∀ c : ℝ, ∀ᵐ ω ∂P, ∀ β : ℝ≥0, β ≤ σ ω → Ev ω β → IsBirthAt (W · ω) (tsupport ψI) (tsupport ψJ) β →
      (P[fun ω' => cexp (I * (h ω' (c • (ψI + ψJ)) : ℂ)) | hσ.measurableSpace]) ω =
        cmKer P hσ.measurableSpace h W (σ ω) (c • (ψI + ψJ)) ω) ∧
    ((∀ (τ : Ω → ℝ≥0) (hτ : IsStoppingTime (drivingFiltration P hX) fun ω => (τ ω : WithTop ℝ≥0)),
      (∀ᵐ ω ∂P, (τ ω : ℝ≥0∞) < ζ ω) → (∀ ω, τ ω ≤ N + 1) →
      ∀ᵐ ω ∂P, Q (τ ω) ω → (P[fun ω' => h ω' (ψI + ψJ) | hτ.measurableSpace]) ω = 0) →
      ∀ᵐ ω ∂P, ∀ β : ℝ≥0, β ≤ σ ω → Ev ω β → IsBirthAt (W · ω) (tsupport ψI) (tsupport ψJ) β →
        (P[fun ω' => h ω' (ψI + ψJ) | hσ.measurableSpace]) ω = 0) := by
  have hE := hC.1
  have hh := hC.2.1
  set K : Set ℂ := tsupport ψI with hKdef
  have hK : IsCompact K := ψI.hasCompactSupport.isCompact
  have hKH : K ⊆ H := ψI.tsupport_subset
  obtain ⟨m, hm, hKm⟩ := exists_pos_le_im_of_isCompact' hK hKH
  obtain ⟨ρ, hρ, A, -, hρm, hρζ, hdA, hexh, -, hAK, -, -⟩ :=
    exists_birthSeq_kernel hC hκ hu₀ hX (not_threshold_seed_of_ae_lt hE hσζ) hK hKH hm hKm
  have hζpos : ∀ᵐ ω ∂P, 0 < ζ ω := hσζ.mono fun ω hω => lt_of_le_of_lt bot_le hω
  -- capped birth sequence and its first positive term
  obtain ⟨ρc, hρcdef⟩ : ∃ ρc : ℕ → Ω → ℝ≥0, ρc = fun n ω => min (ρ n ω) (N + 1) := ⟨_, rfl⟩
  have hρc : ∀ n, IsStoppingTime (drivingFiltration P hX) fun ω => (ρc n ω : WithTop ℝ≥0) := fun n => by
    have e : (fun ω => (ρc n ω : WithTop ℝ≥0)) = fun ω => min (ρ n ω : WithTop ℝ≥0) ((N + 1 : ℝ≥0) : WithTop ℝ≥0) :=
      funext fun ω => by rw [hρcdef]; exact WithTop.coe_min _ _
    rw [e]; exact (hρ n).min_const _
  have hρcm : ∀ ω, Monotone fun n => ρc n ω := fun ω _ _ hmn => by
    rw [hρcdef]; exact min_le_min_right _ (hρm ω hmn)
  have hρcN : ∀ n ω, ρc n ω ≤ N + 1 := fun n ω => by rw [hρcdef]; exact min_le_right _ _
  have hρcle : ∀ n ω, ρc n ω ≤ ρ n ω := fun n ω => by rw [hρcdef]; exact min_le_left _ _
  have hbdd : ∀ ω, BddAbove (range fun n => ρc n ω) := fun ω => ⟨N + 1, by rintro _ ⟨n, rfl⟩; exact hρcN n ω⟩
  obtain ⟨U, hUdef⟩ : ∃ U : Ω → ℝ≥0, U = firstPos ρc := ⟨_, rfl⟩
  have hU : IsStoppingTime (drivingFiltration P hX) fun ω => (U ω : WithTop ℝ≥0) := by
    rw [hUdef]; exact isStoppingTime_firstPos hρc
  have hUN : ∀ ω, U ω ≤ N + 1 := fun ω => by
    rcases firstPos_eq_zero_or (ρ := ρc) ω with h0 | ⟨n, hn⟩
    · rw [hUdef, h0]; exact zero_le
    · rw [hUdef, hn]; exact hρcN n ω
  obtain ⟨ρi, hρidef⟩ : ∃ ρi : Ω → ℝ≥0, ρi = fun ω => ⨆ n, ρc n ω := ⟨_, rfl⟩
  have hρi : IsStoppingTime (drivingFiltration P hX) fun ω => (ρi ω : WithTop ℝ≥0) := by
    rw [hρidef]; exact WangWu.isStoppingTime_iSup_coe hρc hρcN
  -- the birth stop, the later stop, the announcing stops
  obtain ⟨T, hTdef⟩ : ∃ T : Ω → ℝ≥0, T = fun ω => max (min (ρi ω) (σ ω)) (U ω) := ⟨_, rfl⟩
  have hT : IsStoppingTime (drivingFiltration P hX) fun ω => (T ω : WithTop ℝ≥0) := by
    rw [hTdef]; exact isStoppingTime_coe_max (isStoppingTime_coe_min hρi hσ) hU
  obtain ⟨σ', hσ'def⟩ : ∃ σ' : Ω → ℝ≥0, σ' = fun ω => max (σ ω) (U ω) := ⟨_, rfl⟩
  have hσ' : IsStoppingTime (drivingFiltration P hX) fun ω => (σ' ω : WithTop ℝ≥0) := by
    rw [hσ'def]; exact isStoppingTime_coe_max hσ hU
  obtain ⟨ρv, hρvdef⟩ : ∃ ρv : ℕ → Ω → ℝ≥0, ρv = fun n ω => max (min (ρc n ω) (σ ω)) (U ω) := ⟨_, rfl⟩
  have hρv : ∀ n, IsStoppingTime (drivingFiltration P hX) fun ω => (ρv n ω : WithTop ℝ≥0) := fun n => by
    rw [hρvdef]; exact isStoppingTime_coe_max (isStoppingTime_coe_min (hρc n) hσ) hU
  have hρvm : ∀ ω, Monotone fun n => ρv n ω := fun ω _ _ hmn => by
    rw [hρvdef]; exact max_le_max_right _ (min_le_min_right _ (hρcm ω hmn))
  have hρvT : ∀ n ω, ρv n ω ≤ T ω := fun n ω => by
    rw [hρvdef, hTdef, hρidef]; exact max_le_max_right _ (min_le_min_right _ (le_ciSup (hbdd ω) n))
  have hρvlim : ∀ ω, Tendsto (fun n => ρv n ω) atTop (𝓝 (T ω)) := fun ω => by
    rw [hρvdef, hTdef, hρidef]
    exact ((tendsto_atTop_ciSup (hρcm ω) (hbdd ω)).min tendsto_const_nhds).max tendsto_const_nhds
  have hTσ' : ∀ ω, T ω ≤ σ' ω := fun ω => by
    rw [hTdef, hσ'def]; exact max_le_max_right _ (min_le_right _ _)
  have hρvN : ∀ n ω, ρv n ω ≤ N + 1 := fun n ω => by
    rw [hρvdef]
    exact max_le ((min_le_right _ _).trans ((hσN ω).trans (le_add_of_nonneg_right zero_le))) (hUN ω)
  have hUζ : ∀ᵐ ω ∂P, (U ω : ℝ≥0∞) < ζ ω := by
    filter_upwards [ae_all_iff.2 hρζ, hζpos] with ω h1 h0
    rcases firstPos_eq_zero_or (ρ := ρc) ω with hz | ⟨n, hn⟩
    · rw [hUdef, hz, ENNReal.coe_zero]; exact h0
    · rw [hUdef, hn]; exact lt_of_le_of_lt (by exact_mod_cast hρcle n ω) (h1 n)
  have hσ'ζ : ∀ᵐ ω ∂P, (σ' ω : ℝ≥0∞) < ζ ω := by
    filter_upwards [hσζ, hUζ] with ω h1 h2
    rw [hσ'def]; simp only [ENNReal.coe_max]
    exact max_lt h1 h2
  have hTζ : ∀ᵐ ω ∂P, (T ω : ℝ≥0∞) < ζ ω := hσ'ζ.mono fun ω hω =>
    lt_of_le_of_lt (by exact_mod_cast hTσ' ω) hω
  have hρvζ : ∀ n, ∀ᵐ ω ∂P, (ρv n ω : ℝ≥0∞) < ζ ω := fun n => hTζ.mono fun ω hω =>
    lt_of_le_of_lt (by exact_mod_cast hρvT n ω) hω
  have hU0 : ∀ᵐ ω ∂P, 0 < U ω := by
    filter_upwards [hexh, hE.2.2.2.2, hζpos] with ω hex hp h0
    obtain ⟨t, ht0, htζ, htd⟩ := exists_pos_disjoint_fwdHull_of_path hp.2.2.2.1 hp.1 h0 hK hKH
    obtain ⟨n, hn⟩ := (hex t htζ htd).exists
    rw [hUdef]
    exact firstPos_pos ⟨n, by rw [hρcdef]; exact lt_min (ht0.trans_le hn) (by positivity)⟩
  have hT0 : ∀ᵐ ω ∂P, 0 < T ω ∨ ∀ i j, xL i < xR j :=
    hU0.mono fun ω hω => Or.inl (hω.trans_le (by rw [hTdef]; exact le_max_right _ _))
  -- the facts on the event
  have hev : ∀ᵐ ω ∂P, ∀ β : ℝ≥0, β ≤ σ ω → IsBirthAt (W · ω) (tsupport ψI) (tsupport ψJ) β →
      T ω = β ∧ σ' ω = σ ω ∧ (∀ n, ρ n ω < β) ∧ (∀ᶠ n in atTop, ρv n ω = ρ n ω) ∧
        Tendsto (fun n => ρ n ω) atTop (𝓝 β) ∧ 0 < β := by
    filter_upwards [ae_all_iff.2 hdA, ae_all_iff.2 hAK, hexh, hσζ, hE.2.2.2.2, hU0] with ω hd hak hex hσω hp
      hU0ω β hβσ hb
    obtain ⟨⟨z₀, hz₀⟩, hsI, -⟩ := hb
    have hlt : ∀ n, ρ n ω < β := fun n => by
      by_contra hle
      refine Set.disjoint_left.1 (hd n) hz₀ ?_
      rw [hak n]
      refine ⟨hKH hz₀, ?_⟩
      show swallowTime (Ito.rpath (W · ω)) z₀ ≤ ENNReal.ofReal ((ρ n ω : ℝ≥0) : ℝ)
      rw [hsI z₀ hz₀, ENNReal.ofReal_coe_nnreal]
      exact_mod_cast not_lt.1 hle
    have hβN : β < N + 1 := lt_of_le_of_lt (hβσ.trans (hσN ω)) (lt_add_one N)
    have hρc_eq : ∀ n, ρc n ω = ρ n ω := fun n => by
      rw [hρcdef]; exact min_eq_left ((hlt n).le.trans hβN.le)
    have hρi_eq : (⨆ n, ρc n ω) = β := by
      refine le_antisymm (ciSup_le fun n => (hρc_eq n ▸ hlt n).le) ?_
      refine le_of_forall_lt_imp_le_of_dense fun t ht => ?_
      have htζ : (t : ℝ≥0∞) < ζ ω := lt_of_lt_of_le (by exact_mod_cast ht.trans_le hβσ) hσω.le
      have hdisj : Disjoint K (fwdHull (fun s : ℝ => W s.toNNReal ω) (t : ℝ)) :=
        isActiveLabel_of_lt_swallowTime (w := (W · ω)) (C := K) (t := t) fun z hz => by
          rw [hsI z hz]; exact_mod_cast ht
      obtain ⟨n, hn⟩ := (hex t htζ hdisj).exists
      exact hn.trans ((hρc_eq n).symm ▸ le_ciSup (hbdd ω) n)
    have hUβ : U ω ≤ β := by
      rcases firstPos_eq_zero_or (ρ := ρc) ω with hz | ⟨n, hn⟩
      · rw [hUdef, hz]; exact zero_le
      · rw [hUdef, hn, hρc_eq n]; exact (hlt n).le
    have hβpos : 0 < β := lt_of_lt_of_le hU0ω hUβ
    have hρlim : Tendsto (fun n => ρ n ω) atTop (𝓝 β) := by
      have := tendsto_atTop_ciSup (hρcm ω) (hbdd ω)
      rw [hρi_eq] at this
      exact this.congr fun n => hρc_eq n
    refine ⟨?_, by rw [hσ'def]; exact max_eq_left (hUβ.trans hβσ), hlt, ?_, hρlim, hβpos⟩
    · rw [hTdef, hρidef]; show max (min (⨆ n, ρc n ω) (σ ω)) (U ω) = β
      rw [hρi_eq, min_eq_left hβσ, max_eq_left hUβ]
    · filter_upwards [hρlim.eventually (lt_mem_nhds hβpos)] with n hn
      have hU : U ω ≤ ρc n ω := by rw [hUdef]; exact firstPos_le (hρcm ω) (by rw [hρc_eq n]; exact hn)
      rw [hρvdef]; show max (min (ρc n ω) (σ ω)) (U ω) = ρ n ω
      rw [min_eq_left ((hρc_eq n).symm ▸ (hlt n).le.trans hβσ), max_eq_left hU, hρc_eq n]
  -- hull version at the birth stop and the pocket event
  have hTN : ∀ ω, T ω ≤ N + 1 := fun ω => (hTσ' ω).trans (by
    rw [hσ'def]; exact max_le ((hσN ω).trans (le_add_of_nonneg_right zero_le)) (hUN ω))
  obtain ⟨AT, hATm, hATK, hAT𝓕⟩ := exists_hullVersion hC hκ hX hT hTζ
  obtain ⟨F, hFm, hFsub, hFmem⟩ := exists_pocketEvent hAT𝓕 (ψI + ψJ).tsupport_subset
  -- the supports
  have hsupp : ∀ z, z ∈ tsupport (ψI + ψJ) → z ∈ tsupport ψI ∪ tsupport ψJ := fun z hz =>
    tsupport_add (⇑ψI) (⇑ψJ) hz
  have hsle : ∀ ω β, IsBirthAt (W · ω) (tsupport ψI) (tsupport ψJ) β →
      ∀ z ∈ tsupport (ψI + ψJ), swallowTime (Ito.rpath (W · ω)) z ≤ β := fun ω β hb z hz => by
    rcases hsupp z hz with hz | hz
    · exact (hb.2.1 z hz).le
    · exact (hb.2.2 z hz).le
  set E : Set Ω := {ω | ∃ β : ℝ≥0, β ≤ σ ω ∧ Ev ω β ∧ IsBirthAt (W · ω) (tsupport ψI) (tsupport ψJ) β}
    with hEdef
  set ψ : TestOn upperHalfPlaneOpens := ψI + ψJ with hψdef
  have hint : ∀ φ : TestOn upperHalfPlaneOpens, Integrable (fun ω => h ω φ) P := integrable_pairing hC
  -- the birth transfer, for every multiple
  have hpre : ∀ c : ℝ, ∀ᵐ ω ∂P, ω ∈ E →
      (P[fun ω' => cexp (I * (h ω' (c • ψ) : ℂ)) | hσ.measurableSpace]) ω =
        WangWu.gaussCF ((P[fun ω' => h ω' (c • ψ) | hT.measurableSpace]) ω)
          (WangWu.retainedGreenEnergy (W · ω) (σ ω) (c • ψ)) := by
    intro c
    have hFZ : StronglyMeasurable[histGerm hT.measurableSpace AT (centredField h u₀)]
        (F.indicator fun ω => cexp (I * (h ω (c • ψ) : ℂ))) :=
      stronglyMeasurable_indicator_exp_histGerm (h := h) hu₀.1 hFm fun ω hω δ hδ =>
        (tsupport_smul_subset_right (fun _ => c) ψ).trans (hFsub ω hω δ hδ)
    have h1 : ∀ n, ∀ᵐ ω ∂P, ω ∈ {ω | Q (ρv n ω) ω} →
        (P[fun ω' => cexp (I * (h ω' (c • ψ) : ℂ)) | (hρv n).measurableSpace]) ω =
          cmKer P (hρv n).measurableSpace h W (ρv n ω) (c • ψ) ω := fun n =>
      hIH c (ρv n) (hρv n) (hρvζ n) (hρvN n)
    have h2 : ∀ᵐ ω ∂P, ω ∈ E → ∀ᶠ n in atTop, ω ∈ {ω | Q (ρv n ω) ω} := by
      filter_upwards [hev] with ω hevω ⟨β, hβσ, hEv, hb⟩
      obtain ⟨-, -, hlt, hevρ, hρlim, hβpos⟩ := hevω β hβσ hb
      obtain ⟨t₀, ht₀, hQt⟩ := hQ ω β hβpos hEv
      filter_upwards [hevρ, hρlim.eventually (lt_mem_nhds ht₀)] with n hn1 hn2
      show Q (ρv n ω) ω
      rw [hn1]; exact hQt _ hn2.le (hlt n)
    have hlev := ae_tendsto_condExp_real_of_announce hC hκ hu₀ hX hT hTζ hT0 hρv hρvm hρvT
      (Eventually.of_forall hρvlim) (hint (c • ψ))
    have h3 : ∀ᵐ ω ∂P, ω ∈ E → Tendsto (fun n => cmKer P (hρv n).measurableSpace h W (ρv n ω) (c • ψ) ω)
        atTop (𝓝 (WangWu.gaussCF ((P[fun ω' => h ω' (c • ψ) | hT.measurableSpace]) ω)
          (WangWu.retainedGreenEnergy (W · ω) (T ω) (c • ψ)))) := by
      filter_upwards [hlev, hE.2.2.2.2, hTζ] with ω hl hp hTω _
      have hc := continuous_retainedGreenForm_min_of_path hp.2.2.2.1 hp.1 hTω
        (isTestFn_of_testOn (c • ψ)) (isTestFn_of_testOn (c • ψ))
      have hgreen : Tendsto (fun n => WangWu.retainedGreenEnergy (W · ω) (ρv n ω) (c • ψ)) atTop
          (𝓝 (WangWu.retainedGreenEnergy (W · ω) (T ω) (c • ψ))) := by
        have h1 := (hc.tendsto (T ω)).comp (hρvlim ω)
        rw [min_self] at h1
        refine h1.congr fun n => ?_
        simp only [Function.comp_apply, min_eq_left (hρvT n ω)]
        rfl
      exact (WangWu.continuous_gaussCF.tendsto _).comp (hl.prodMk_nhds hgreen)
    have h4 : ∀ᵐ ω ∂P, ω ∈ E → ω ∈ F ∧ T ω ≤ σ' ω := by
      filter_upwards [hev, hATK] with ω hevω hATω ⟨β, hβσ, hEv, hb⟩
      obtain ⟨hTβ, -⟩ := hevω β hβσ hb
      refine ⟨hFmem ω ?_, hTσ' ω⟩
      rw [hATω, hTβ]
      intro z hz
      refine ⟨(ψI + ψJ).tsupport_subset hz, ?_⟩
      show swallowTime (Ito.rpath (W · ω)) z ≤ ENNReal.ofReal ((β : ℝ≥0) : ℝ)
      rw [ENNReal.ofReal_coe_nnreal]
      exact hsle ω β hb z hz
    have hbirth := ae_condExp_eq_of_birth hC hκ hu₀ hX hT hσ' hTζ hT0 hρv hρvm hρvT
      (Eventually.of_forall hρvlim) hATm hATK (aestronglyMeasurable_exp_pairing hC.2.1 (c • ψ))
      (fun ω => norm_exp_I_mul_pairing (c • ψ) ω) hFm hFZ h1 h2 h3 h4
    have hmin := condExp_min_stopping_time_ae_eq_restrict_le (μ := P)
      (f := fun ω' => cexp (I * (h ω' (c • ψ) : ℂ))) hσ' hσ
    have hcongr : (hσ'.min hσ).measurableSpace = hσ.measurableSpace :=
      IsStoppingTime.measurableSpace_congr _ _ (funext fun ω => min_eq_right
        (WithTop.coe_le_coe.2 (by rw [hσ'def]; exact le_max_left _ _)))
    rw [hcongr] at hmin
    have hmin' := ae_imp_of_ae_restrict hmin
    filter_upwards [hbirth, hmin', hev] with ω hb1 hb2 hevω hωE
    obtain ⟨β, hβσ, hEv, hb⟩ := hωE
    obtain ⟨hTβ, hσ'σ, -⟩ := hevω β hβσ hb
    rw [hb2 (show ((σ' ω : ℝ≥0) : WithTop ℝ≥0) ≤ ((σ ω : ℝ≥0) : WithTop ℝ≥0) by rw [hσ'σ]),
      hb1 ⟨β, hβσ, hEv, hb⟩, hTβ]
    congr 1
    refine (retainedGreenEnergy_eq_of_swallowTime_le (fun z hz => ?_) hβσ).symm
    exact hsle ω β hb z ((tsupport_smul_subset_right (fun _ => c) ψ) (subset_tsupport _ hz))
  -- the freeze of the conditional mean
  have hfreeze : ∀ᵐ ω ∂P, ω ∈ E →
      (P[fun ω' => h ω' ψ | hσ.measurableSpace]) ω = (P[fun ω' => h ω' ψ | hT.measurableSpace]) ω := by
    refine ae_condExp_eq_of_condCharFun_on (hint ψ)
      (v := fun ω => WangWu.retainedGreenEnergy (W · ω) (σ ω) ψ) fun c => ?_
    filter_upwards [hpre c, condExp_pairing_smul (P := P) hT.measurableSpace h c ψ] with ω h1 h2 hωE
    rw [← exp_pairing_smul, h1 hωE, h2]
    first
    | rw [retainedGreenEnergy_testOn_smul, WangWu.gaussCF]
    | rw [retainedGreenEnergy_smul, WangWu.gaussCF]
  refine ⟨fun c => ?_, fun hzero => ?_⟩
  · filter_upwards [hpre c, hfreeze, condExp_pairing_smul (P := P) hT.measurableSpace h c ψ,
      condExp_pairing_smul (P := P) hσ.measurableSpace h c ψ] with ω h1 h2 h3 h4 β hβσ hEv hb
    have hωE : ω ∈ E := ⟨β, hβσ, hEv, hb⟩
    rw [h1 hωE, cmKer, h3, h4, h2 hωE]
    rfl
  · have hlev := ae_tendsto_condExp_real_of_announce hC hκ hu₀ hX hT hTζ hT0 hρv hρvm hρvT
      (Eventually.of_forall hρvlim) (hint ψ)
    have hz : ∀ᵐ ω ∂P, ∀ n, Q (ρv n ω) ω → (P[fun ω' => h ω' ψ | (hρv n).measurableSpace]) ω = 0 :=
      ae_all_iff.2 fun n => hzero (ρv n) (hρv n) (hρvζ n) (hρvN n)
    filter_upwards [hlev, hz, hfreeze, hev] with ω hl hzω hfr hevω β hβσ hEv hb
    have hωE : ω ∈ E := ⟨β, hβσ, hEv, hb⟩
    obtain ⟨-, -, hlt, hevρ, hρlim, hβpos⟩ := hevω β hβσ hb
    obtain ⟨t₀, ht₀, hQt⟩ := hQ ω β hβpos hEv
    rw [hfr hωE]
    refine tendsto_nhds_unique hl (tendsto_const_nhds.congr' ?_)
    filter_upwards [hevρ, hρlim.eventually (lt_mem_nhds ht₀)] with n hn1 hn2
    refine (hzω n ?_).symm
    rw [hn1]; exact hQt _ hn2.le (hlt n)

end Birth

end WholeField

end InteractingSLE
