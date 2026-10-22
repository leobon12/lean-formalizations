import HigherDimLQGMetric.Sec6.Prop62Cover
import HigherDimLQGMetric.Sec6.Transfer
import HigherDimLQGMetric.Amplify.Defs
import HigherDimLQGMetric.Freq.Translate

/-!
# [S] Proposition 6.2 (P): the probability bound

Packet S6b. Source: MA3 Details (a) **D-6.2** (*Construction*: "For `r` as in (P): `P[config ∈ 𝒢] ≥ p`
after allocating the failure probabilities (Lemma 6.1's event implies the witness condition: `D^U ≥ D`,
lengths of paths in `U` agree)"; (P): `{∃ j : config ∈ N_j} ⊇ {config ∈ 𝒢}`), blueprint Part A §6
(`prop:62`, steps (4)–(5), (8)), source l. 1053–1063, 1099–1101.

* `s6b_witness_of_arc`: an arc of Lemma 6.1 in `r·K` (centre `0`) gives a witness path of the
  continuous configuration at `(0, r)` with `A = c₂ A₁`.
* `s6b_prob_center`: (P) at centre `0` from M2b's D-SF5 mass bound and Lemma 6.1's event.
* `s6b_config_translate`: translation of configurations; `s6b_prob`: (P) at every centre (translation
  covariance, S4c's `s4c_witEvent_law_eq`).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace HigherDimLQGMetric

open MeasureTheory Set Filter BoundedContinuousFunction unitInterval
open _root_.Topology
open HigherDimLFPP (Rd)
open scoped ENNReal
open LQGMetric.MetricGeometry

variable {d : ℕ}

/-! ### Witnesses from the arcs of Lemma 6.1 -/

/-- An arc of Lemma 6.1 in `r·K` gives a witness path of the configuration at `(0, r)`. -/
theorem s6b_witness_of_arc (hd : 2 ≤ d) {D₀ Dt₀ : ContMetric d} (hl : D₀.IsLength)
    (hlt : Dt₀.IsLength) {s r : ℝ} (hs : 0 < s) (hr : 0 < r) {K : Set (Rd d)}
    (hKU : K ⊆ configOuter d) {γ : ℝ → Rd d} (hγc : ContinuousOn γ (Icc 0 1))
    (hγK : ∀ τ ∈ Icc (0 : ℝ) 1, γ τ ∈ (fun x => r • x) '' K) {a₁ c₂ A₁ : ℝ} (hc₂ : 0 ≤ c₂)
    (hA₁0 : 0 ≤ A₁) (hrat : Dt₀.len γ 0 1 ≤ ENNReal.ofReal (c₂ * D₀.1 (γ 0, γ 1)))
    (hsep : a₁ * s ≤ D₀.1 (γ 0, γ 1)) (hlen : D₀.len γ 0 1 ≤ ENNReal.ofReal (A₁ * s)) :
    s6bWitness (configC hd D₀ Dt₀ hl hlt hs hr 0) K (c₂ * A₁) a₁ c₂ := by
  set q := configC hd D₀ Dt₀ hl hlt hs hr 0 with hq_def
  have hq1 : IsCoordinate q.1 :=
    config_internalC_isCoordinate (configScaledMetric D₀ hs hr 0)
      (configScaledMetric_isLength D₀ hl hs hr 0) configOuter_isOpen (configOuter_isPreconnected hd)
  have hq2 : IsCoordinate q.2.1 :=
    config_internalC_isCoordinate (configScaledMetric Dt₀ hs hr 0)
      (configScaledMetric_isLength Dt₀ hlt hs hr 0) configOuter_isOpen
      (configOuter_isPreconnected hd)
  have hmem : ∀ t : I, r⁻¹ • γ t ∈ configOuter d := fun t => by
    obtain ⟨x, hx, hxe⟩ := hγK t t.2
    simp only at hxe
    rw [← hxe, smul_smul, inv_mul_cancel₀ hr.ne', one_smul]
    exact hKU hx
  have hγI : Continuous (fun t : I => γ t) := hγc.comp_continuous continuous_subtype_val
    (fun t => t.2)
  let u0 : C(I, configOuter d) :=
    ⟨fun t => ⟨r⁻¹ • γ t, hmem t⟩, Continuous.subtype_mk (hγI.const_smul r⁻¹) _⟩
  let u : I →ᵇ configOuter d := mkOfCompact u0
  have hu_apply : ∀ t : I, ((u t : configOuter d) : Rd d) = r⁻¹ • γ t := fun t => rfl
  have huB : ∀ t, ((u t : configOuter d) : Rd d) ∈ K := by
    intro t
    obtain ⟨x, hx, hxe⟩ := hγK t t.2
    simp only at hxe
    rw [hu_apply, ← hxe, smul_smul, inv_mul_cancel₀ hr.ne', one_smul]
    exact hx
  have huc : ContinuousOn (Set.IccExtend zero_le_one u) (Icc 0 1) :=
    (continuous_IccExtend_iff.mpr u.continuous).continuousOn
  have hreal : EqOn (fun t => r • ((Set.IccExtend zero_le_one u t : configOuter d) : Rd d) + 0) γ
      (Icc 0 1) := by
    intro t ht
    simp only [Set.IccExtend_of_mem zero_le_one u ht, hu_apply, add_zero, smul_smul,
      mul_inv_cancel₀ hr.ne', one_smul]
  have hE1 : ∀ x y : configOuter d, ENNReal.ofReal (q.1 (x, y)) = ENNReal.ofReal s⁻¹ *
      D₀.internal (ann 0 (r / 2) (5 * r)) (r • (x : Rd d) + 0) (r • (y : Rd d) + 0) :=
    fun x y => configC_bridge_outer hd D₀ Dt₀ hl hlt hs hr 0 x y
  have hE2 : ∀ x y : configOuter d, ENNReal.ofReal (q.2.1 (x, y)) = ENNReal.ofReal s⁻¹ *
      Dt₀.internal (ann 0 (r / 2) (5 * r)) (r • (x : Rd d) + 0) (r • (y : Rd d) + 0) :=
    fun x y => configC_bridge_outer_tilde hd D₀ Dt₀ hl hlt hs hr 0 x y
  -- the `D̃` length of the normalized arc
  have hlen2 : curveLengthWith (fun x y => ENNReal.ofReal (q.2.1 (x, y)))
      (Set.IccExtend zero_le_one u) 0 1 = ENNReal.ofReal s⁻¹ * Dt₀.len γ 0 1 := by
    have h := S6a.curveLengthWith_cfg (E := fun x y => ENNReal.ofReal (q.2.1 (x, y))) hr hE2 huc
    rw [Dt₀.len_congr hreal] at h
    exact h
  -- the endpoint distance
  have hu0 : (u 0 : Rd d) = r⁻¹ • γ 0 := rfl
  have hu1 : (u 1 : Rd d) = r⁻¹ • γ 1 := rfl
  have hγ0 : r • ((u 0 : configOuter d) : Rd d) + 0 = γ 0 := by
    rw [hu0, add_zero, smul_smul, mul_inv_cancel₀ hr.ne', one_smul]
  have hγ1 : r • ((u 1 : configOuter d) : Rd d) + 0 = γ 1 := by
    rw [hu1, add_zero, smul_smul, mul_inv_cancel₀ hr.ne', one_smul]
  have hq1nn : 0 ≤ q.1 (u 0, u 1) := by
    have h := dist_nonneg (x := MetricFunSpace.pt q.1 hq1.metric (u 0))
      (y := MetricFunSpace.pt q.1 hq1.metric (u 1))
    exact h
  have hend : s⁻¹ * D₀.1 (γ 0, γ 1) ≤ q.1 (u 0, u 1) := by
    have h := hE1 (u 0) (u 1)
    rw [hγ0, hγ1] at h
    have h2 : ENNReal.ofReal (s⁻¹ * D₀.1 (γ 0, γ 1)) ≤ ENNReal.ofReal (q.1 (u 0, u 1)) := by
      rw [h, ENNReal.ofReal_mul (inv_nonneg.2 hs.le)]
      exact mul_le_mul_right (D₀.ofReal_le_internal _ _ _) _
    exact (ENNReal.ofReal_le_ofReal_iff hq1nn).1 h2
  have hDnn : 0 ≤ D₀.1 (γ 0, γ 1) := D₀.nonneg _ _
  -- the ratio and the length bound
  have hbound : curveLengthWith (fun x y => ENNReal.ofReal (q.2.1 (x, y)))
      (Set.IccExtend zero_le_one u) 0 1 ≤ ENNReal.ofReal (c₂ * (s⁻¹ * D₀.1 (γ 0, γ 1))) := by
    rw [hlen2]
    calc ENNReal.ofReal s⁻¹ * Dt₀.len γ 0 1
        ≤ ENNReal.ofReal s⁻¹ * ENNReal.ofReal (c₂ * D₀.1 (γ 0, γ 1)) := mul_le_mul_right hrat _
      _ = ENNReal.ofReal (c₂ * (s⁻¹ * D₀.1 (γ 0, γ 1))) := by
        rw [← ENNReal.ofReal_mul (inv_nonneg.2 hs.le)]
        ring_nf
  have hDlen : D₀.1 (γ 0, γ 1) ≤ A₁ * s :=
    (ENNReal.ofReal_le_ofReal_iff (mul_nonneg hA₁0 hs.le)).1
      ((D₀.ofReal_le_len γ zero_le_one).trans hlen)
  have hA₁ : s⁻¹ * D₀.1 (γ 0, γ 1) ≤ A₁ := by
    rw [inv_mul_le_iff₀ hs]
    linarith
  refine s6b_witness_of_path hq2 (u := u) huB ?_ ?_ ?_ ?_
  · exact mul_nonneg hc₂ hA₁0
  · exact hbound.trans (ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left hA₁ hc₂))
  · have : a₁ ≤ s⁻¹ * D₀.1 (γ 0, γ 1) := by
      rw [le_inv_mul_iff₀ hs]
      linarith
    exact this.trans hend
  · exact hbound.trans (ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left hend hc₂))

/-! ### (P) at centre `0` -/

/-- **(P) at centre `0`**: the D-SF5 mass bound and the event of Lemma 6.1, each of probability at
least `1 - η`, give a trap configuration with probability at least `1 - 2η`. -/
theorem s6b_prob_center (hd : 2 ≤ d) {ξ Q : ℝ} {D Dt : DistRd d → ContMetric d}
    {c C : ℝ} {β : ConfigBounds d} {η : ℝ} (hη : 0 ≤ η) (hη1 : η ≤ 1)
    {M : ℕ} {Kb : Fin M → Set (Rd d)} (hKb : ∀ i, Kb i ⊆ configOuter d)
    {A₁ a₁ c₂ : ℝ} (hc₂ : 0 ≤ c₂) (hA₁ : 0 ≤ A₁)
    {J : ℕ} {N : ℕ → Set (Config d)}
    (hcover : ∀ (D₀ Dt₀ : ContMetric d) (hl : D₀.IsLength) (hlt : Dt₀.IsLength) {s r : ℝ}
      (hs : 0 < s) (hr : 0 < r),
      configC hd D₀ Dt₀ hl hlt hs hr 0 ∈ configCompactFamily hd c C β →
      (∀ i, s6bWitness (configC hd D₀ Dt₀ hl hlt hs hr 0) (Kb i) (c₂ * A₁) a₁ c₂) →
      ∃ j < J, config D₀ Dt₀ s r 0 ∈ N j)
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P] (h : Ω → DistRd d)
    {r : ℝ} (hr : 0 < r) (Ξ : Ω → ConfigC d) (hΞm : Measurable Ξ)
    (hΞae : ∀ᵐ ω ∂P, ∃ (hl : (D (h ω)).IsLength) (hlt : (Dt (h ω)).IsLength),
      Ξ ω = configC hd (D (h ω)) (Dt (h ω)) hl hlt (sNorm_pos ξ Q (h ω) hr 0) hr 0)
    (hΞmass : 1 - ENNReal.ofReal η ≤ P {ω | Ξ ω ∈ configCompactFamily hd c C β})
    (hFFA : ENNReal.ofReal (1 - η) ≤ P {ω | ∀ i, ∃ γ : ℝ → Rd d, IsSimpleArc γ ∧
      (∀ τ ∈ Icc (0 : ℝ) 1, γ τ ∈ (fun x => r • x) '' Kb i) ∧
      (Dt (h ω)).len γ 0 1 ≤ ENNReal.ofReal (c₂ * (D (h ω)).1 (γ 0, γ 1)) ∧
      a₁ * sNorm ξ Q (h ω) r 0 ≤ (D (h ω)).1 (γ 0, γ 1) ∧
      (D (h ω)).len γ 0 1 ≤ ENNReal.ofReal (A₁ * sNorm ξ Q (h ω) r 0)}) :
    ENNReal.ofReal (1 - 2 * η) ≤
      P {ω | ∃ j < J, config (D (h ω)) (Dt (h ω)) (sNorm ξ Q (h ω) r 0) r 0 ∈ N j} := by
  obtain ⟨S, hSae, hSm, hS⟩ := hΞae.exists_measurable_mem
  set G : Set Ω := {ω | Ξ ω ∈ configCompactFamily hd c C β} with hG_def
  have hGm : MeasurableSet G :=
    hΞm (configCompactFamily_isCompact hd c C β).isClosed.measurableSet
  set E : Set Ω := {ω | ∀ i, ∃ γ : ℝ → Rd d, IsSimpleArc γ ∧
      (∀ τ ∈ Icc (0 : ℝ) 1, γ τ ∈ (fun x => r • x) '' Kb i) ∧
      (Dt (h ω)).len γ 0 1 ≤ ENNReal.ofReal (c₂ * (D (h ω)).1 (γ 0, γ 1)) ∧
      a₁ * sNorm ξ Q (h ω) r 0 ≤ (D (h ω)).1 (γ 0, γ 1) ∧
      (D (h ω)).len γ 0 1 ≤ ENNReal.ofReal (A₁ * sNorm ξ Q (h ω) r 0)} with hE_def
  have hsub : E ∩ (G ∩ S) ⊆
      {ω | ∃ j < J, config (D (h ω)) (Dt (h ω)) (sNorm ξ Q (h ω) r 0) r 0 ∈ N j} := by
    rintro ω ⟨hEω, hGω, hSω⟩
    obtain ⟨hl, hlt, hΞeq⟩ := hS ω hSω
    have hC : configC hd (D (h ω)) (Dt (h ω)) hl hlt (sNorm_pos ξ Q (h ω) hr 0) hr 0 ∈
        configCompactFamily hd c C β := by
      rw [← hΞeq]
      exact hGω
    refine hcover (D (h ω)) (Dt (h ω)) hl hlt (sNorm_pos ξ Q (h ω) hr 0) hr hC (fun i => ?_)
    obtain ⟨γ, hγ, hγK, hrat, hsep, hlen⟩ := hEω i
    exact s6b_witness_of_arc hd hl hlt (sNorm_pos ξ Q (h ω) hr 0) hr (hKb i) hγ.1 hγK hc₂ hA₁
      hrat hsep hlen
  have hSc : P Sᶜ = 0 := hSae
  have hbad : P (G ∩ S)ᶜ ≤ ENNReal.ofReal η := by
    rw [compl_inter]
    calc P (Gᶜ ∪ Sᶜ) ≤ P Gᶜ + P Sᶜ := measure_union_le _ _
      _ = P Gᶜ := by rw [hSc, add_zero]
      _ = 1 - P G := prob_compl_eq_one_sub hGm
      _ ≤ 1 - (1 - ENNReal.ofReal η) := tsub_le_tsub_left hΞmass 1
      _ = ENNReal.ofReal η := ENNReal.sub_sub_cancel ENNReal.one_ne_top
          (by rw [← ENNReal.ofReal_one]; exact ENNReal.ofReal_le_ofReal hη1)
  have hsplit : P E ≤ P (E ∩ (G ∩ S)) + P (G ∩ S)ᶜ := by
    calc P E ≤ P (E ∩ (G ∩ S) ∪ (G ∩ S)ᶜ) := by
          refine measure_mono fun ω hω => ?_
          by_cases h' : ω ∈ G ∩ S
          · exact Or.inl ⟨hω, h'⟩
          · exact Or.inr h'
      _ ≤ _ := measure_union_le _ _
  calc ENNReal.ofReal (1 - 2 * η) = ENNReal.ofReal (1 - η) - ENNReal.ofReal η := by
        rw [← ENNReal.ofReal_sub _ hη]
        ring_nf
    _ ≤ P E - P (G ∩ S)ᶜ := tsub_le_tsub hFFA hbad
    _ ≤ P (E ∩ (G ∩ S)) := tsub_le_iff_right.2 hsplit
    _ ≤ _ := measure_mono hsub

/-! ### Translation to every centre -/

theorem s6b_config_translate (D Dt : ContMetric d) (s r : ℝ) (z : Rd d) :
    config (D.affine 1 one_ne_zero z) (Dt.affine 1 one_ne_zero z) s r 0 = config D Dt s r z := by
  have himg (a b : ℝ) : (fun x : Rd d => x + z) '' ann 0 a b = ann z a b := by
    simpa only [one_mul, one_smul] using image_ann_affine (r := 1) one_pos z a b
  simp only [config, ContMetric.internal_affine, one_smul, add_zero, himg]

/-- **(P) at every centre**, from (P) at centre `0` for every LGF (translation covariance). -/
theorem s6b_prob (hd : 2 ≤ d) {ξ Q : ℝ} {D Dt : DistRd d → ContMetric d}
    (hD : IsSharpWeakExpMetric d ξ Q D) (hDt : IsSharpWeakExpMetric d ξ Q Dt)
    {U a A₀ ℓ β₀ t ρ pw p : ℝ} (hρ : 0 < ρ) {J : ℕ} {N : ℕ → Set (Config d)}
    (hcenter : ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
      (h : Ω → DistRd d), IsWholeSpaceLGF h P → ∀ r : ℝ, 0 < r →
      ENNReal.ofReal pw ≤ P (h ⁻¹' WitEvent Dt D ξ Q U a A₀ ℓ β₀ t (ρ * r) 0) →
      ENNReal.ofReal p ≤
        P {ω | ∃ j < J, config (D (h ω)) (Dt (h ω)) (sNorm ξ Q (h ω) r 0) r 0 ∈ N j}) :
    ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
      (h : Ω → DistRd d), IsWholeSpaceLGF h P → ∀ r : ℝ, 0 < r →
      ENNReal.ofReal pw ≤ P (h ⁻¹' WitEvent Dt D ξ Q U a A₀ ℓ β₀ t (ρ * r) 0) →
      ∀ z : Rd d, ENNReal.ofReal p ≤
        P {ω | ∃ j < J, config (D (h ω)) (Dt (h ω)) (sNorm ξ Q (h ω) r z) r z ∈ N j} := by
  intro Ω _ P _ h hh r hr hW z
  set ht : Ω → DistRd d := fun ω => affineComp 1 z (h ω) with hht_def
  have hht : IsWholeSpaceLGF ht P := hh.affineComp one_pos z
  have hWt : ENNReal.ofReal pw ≤ P (ht ⁻¹' WitEvent Dt D ξ Q U a A₀ ℓ β₀ t (ρ * r) 0) := by
    rw [s4c_witEvent_law_eq P P ht h hht hh hDt hD hd U a A₀ ℓ β₀ t (mul_pos hρ hr) 0]
    exact hW
  have hbound := hcenter P ht hht r hr hWt
  have hae : ∀ᵐ ω ∂P, config (D (ht ω)) (Dt (ht ω)) (sNorm ξ Q (ht ω) r 0) r 0 =
      config (D (h ω)) (Dt (h ω)) (sNorm ξ Q (h ω) r z) r z := by
    filter_upwards [hD.ae_metric_translate P h hh z, hDt.ae_metric_translate P h hh z,
      hh.ae_sphereAvg_affineComp hd one_pos z hr 0] with ω hmD hmDt hsph
    have hs : sNorm ξ Q (ht ω) r 0 = sNorm ξ Q (h ω) r z := by
      simp only [ht, sNorm]
      simpa only [one_mul, smul_zero, zero_add] using congrArg
        (fun v : ℝ => r ^ (ξ * Q) * Real.exp (ξ * v)) hsph
    rw [hs, hmD, hmDt]
    exact s6b_config_translate _ _ _ _ _
  refine hbound.trans (measure_mono_ae ?_)
  filter_upwards [hae] with ω hω hmem
  obtain ⟨j, hj, hjN⟩ := hmem
  exact ⟨j, hj, hω ▸ hjN⟩

end HigherDimLQGMetric
