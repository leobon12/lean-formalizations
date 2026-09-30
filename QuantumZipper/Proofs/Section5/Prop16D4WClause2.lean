import QuantumZipper.Proofs.Section5.Prop16D4WOsc
import QuantumZipper.Proofs.Section5.Prop16GAssembly
import QuantumZipper.Proofs.Section5.Prop16Assembly

/-!
# Proposition 1.6, D4⁺ʷ clause (2) for the objects of `theorem1_6`

Decision D24 (`DECISIONS.md`). `prop16_weak_clause2` proves clause (2) of
`Prop16Asm.Prop16TVWeakStmt` (the canonical zoomed field's area pairings are close in probability
to `locArea γ R f (Z C)`), with the witness `Z C p = canonicalOn γ (x C p) (zoomDomain D p.2)`,
for any family `x C p` ("the zoomed field without the continuous remainder") satisfying:

* `hloc`: a.s. `x C p` and the actual zoomed field `Y C p = zoomField γ C (𝔥₀ + X p.1) p.2` are
  locally good on some `V ⊇ D − p.2` on which `ψ_p = 𝔥₀(· + p.2) − 𝔥₀(p.2)` is continuous, and the
  local area measure of `Y C p` on `D − p.2` is that of `ofFun ψ_p + x C p`;
* `hsc0`: the local scale of `x` tends to `0` in probability (D3⁺(iii) transported);
* `hscale`: the ratio of the local scales of `ofFun ψ_p + x` and `x` tends to `1` in probability;
* `htight`: the local area of `x` in the half-ball of radius `ρ ·` (scale of `x`) is tight.

The remaining inputs `φ(a·) → 0` and "the canonical domain contains `hball R`" are proved here
from the continuity of `𝔥₀` on `D ∪ (a,b)`, the site condition of the geometry, and `hsc0`.

Own elementary arguments (AGENT_GUIDE cost rule), following the route of D24 and Sheffield,
arXiv:1012.4797, proof of Prop. 1.6 (p. 25).
-/

noncomputable section

open MeasureTheory Filter Topology Set Metric
open scoped ENNReal

namespace QuantumZipper

namespace Prop16Asm

open Prop16Area.G

/-- The canonical domain contains `hball R` once the scaled half-ball fits in `U`. -/
theorem hball_subset_canonicalDomainOn {γ : ℝ} {x : FieldSample} {U : Set ℂ} {ρ : ℝ}
    (ha : 0 < scaleParamOn γ x U) (hρ : ball (0 : ℂ) ρ ∩ H ⊆ U) {R : ℕ}
    (hsR : scaleParamOn γ x U * R < ρ) : Prop16Area.hball R ⊆ canonicalDomainOn γ x U := by
  rintro z ⟨hz, hzH⟩
  refine hρ ⟨?_, ?_⟩
  · rw [mem_ball, dist_zero_right, norm_mul, Complex.norm_real,
      Real.norm_of_nonneg ha.le]
    rw [mem_ball, dist_zero_right] at hz
    nlinarith
  · show 0 < ((scaleParamOn γ x U : ℂ) * z).im
    rw [Complex.im_ofReal_mul]; exact mul_pos ha hzH

/-- **Uniform site radius** on a compact set of real points. -/
theorem exists_uniform_site {D : Set ℂ} {c d : ℝ}
    (hdisc : ∀ t ∈ Ioo c d, ∃ r > 0, ball (t : ℂ) r ∩ H ⊆ D) {K : Set ℝ} (hK : IsCompact K)
    (hKcd : K ⊆ Ioo c d) : ∃ ρ > 0, ∀ t ∈ K, ball (t : ℂ) ρ ∩ H ⊆ D := by
  have hloc : ∀ t : K, ∃ r > 0, ball ((t : ℝ) : ℂ) r ∩ H ⊆ D := fun t => hdisc t (hKcd t.2)
  choose r hr hrD using hloc
  obtain ⟨δ, hδ, hδK⟩ := lebesgue_number_lemma_of_metric
    (c := fun i : K => ball (((i : ℝ)) : ℂ) (r i)) (hK.image Complex.continuous_ofReal)
    (fun _ => isOpen_ball) (by
      rintro _ ⟨t, ht, rfl⟩
      exact mem_iUnion.2 ⟨⟨t, ht⟩, mem_ball_self (hr _)⟩)
  refine ⟨δ, hδ, fun t ht => ?_⟩
  obtain ⟨i, hi⟩ := hδK _ ⟨t, ht, rfl⟩
  exact fun z hz => hrD i ⟨hi hz.1, hz.2⟩

/-- The marked point lies in a fixed compact part of `(a,b)` with high probability. -/
theorem exists_N_marked_compact {Ω : Type*} [MeasurableSpace Ω] (Q : Measure Ω)
    [IsFiniteMeasure Q] {a b : ℝ} (t : Ω → ℝ) (ht : Measurable t)
    (hta : ∀ᵐ ω ∂Q, t ω ∈ Ioo a b) {θ : ℝ≥0∞} (hθ : 0 < θ) :
    ∃ N : ℕ, Q {ω | t ω ∉ Icc (a + 1 / ((N : ℝ) + 1)) (b - 1 / ((N : ℝ) + 1))} ≤ θ := by
  set A : ℕ → Set Ω := fun N => {ω | t ω ∉ Icc (a + 1 / ((N : ℝ) + 1)) (b - 1 / ((N : ℝ) + 1))}
  have hAm : ∀ N, MeasurableSet (A N) := fun N => (ht measurableSet_Icc).compl
  have hAa : Antitone A := fun m n hmn ω hω h => hω (by
    obtain ⟨h1, h2⟩ := h
    have h : 1 / ((n : ℝ) + 1) ≤ 1 / ((m : ℝ) + 1) :=
      one_div_le_one_div_of_le (by positivity) (by exact_mod_cast Nat.succ_le_succ hmn)
    exact ⟨by linarith, by linarith⟩)
  have hAi : Q (⋂ N, A N) = 0 := by
    refine measure_mono_null (fun ω hω => ?_) (ae_iff.1 hta)
    simp only [mem_iInter] at hω
    intro htab
    obtain ⟨N, hN⟩ := Prop16Area.G.mem_iUnion_ioo htab
    exact hω N ⟨hN.1.le, hN.2.le⟩
  have hlim := tendsto_measure_iInter_atTop (μ := Q) (fun N => (hAm N).nullMeasurableSet) hAa
    ⟨0, measure_ne_top _ _⟩
  rw [hAi] at hlim
  exact (ENNReal.tendsto_nhds_zero.1 hlim θ hθ).exists

/-- **The canonical domain eventually contains `hball R`, in probability.** -/
theorem tendsto_prob_hdom {Ω : Type*} [MeasurableSpace Ω] (Q : Measure Ω) [IsFiniteMeasure Q]
    {γ : ℝ} {D : Set ℂ} {c d a b : ℝ} (hca : c ≤ a) (hbd : b ≤ d)
    (hdisc : ∀ t ∈ Ioo c d, ∃ r > 0, ball (t : ℂ) r ∩ H ⊆ D) (t : Ω → ℝ) (ht : Measurable t)
    (hta : ∀ᵐ ω ∂Q, t ω ∈ Ioo a b) (x : ℝ → Ω → FieldSample)
    (hs : ∀ δ > 0, Tendsto (fun C => Q {ω | ¬ (0 < scaleParamOn γ (x C ω) (zoomDomain D (t ω)) ∧
      scaleParamOn γ (x C ω) (zoomDomain D (t ω)) < δ)}) atTop (𝓝 0)) (R : ℕ) :
    Tendsto (fun C => Q {ω | ¬ Prop16Area.hball R ⊆
      canonicalDomainOn γ (x C ω) (zoomDomain D (t ω))}) atTop (𝓝 0) := by
  rw [ENNReal.tendsto_nhds_zero]
  intro θ hθ
  have hθ2 : 0 < θ / 2 := ENNReal.div_pos hθ.ne' (by norm_num)
  obtain ⟨N, hN⟩ := exists_N_marked_compact Q t ht hta hθ2
  have hKcd : Icc (a + 1 / ((N : ℝ) + 1)) (b - 1 / ((N : ℝ) + 1)) ⊆ Ioo c d := fun u hu => by
    have : (0 : ℝ) < 1 / ((N : ℝ) + 1) := by positivity
    exact ⟨by linarith [hu.1], by linarith [hu.2]⟩
  obtain ⟨ρ, hρ, hρD⟩ := exists_uniform_site hdisc isCompact_Icc hKcd
  have hR1 : (0 : ℝ) < R + 1 := by positivity
  filter_upwards [(ENNReal.tendsto_nhds_zero.1 (hs (ρ / (R + 1)) (div_pos hρ hR1))) (θ / 2) hθ2]
    with C hC
  refine (measure_mono (fun ω hω => ?_ : _ ⊆ {ω | t ω ∉ Icc (a + 1 / ((N : ℝ) + 1))
      (b - 1 / ((N : ℝ) + 1))} ∪ {ω | ¬ (0 < scaleParamOn γ (x C ω) (zoomDomain D (t ω)) ∧
      scaleParamOn γ (x C ω) (zoomDomain D (t ω)) < ρ / (R + 1))})).trans
    ((measure_union_le _ _).trans ((add_le_add hN hC).trans (le_of_eq (ENNReal.add_halves θ))))
  simp only [mem_ofPred_eq] at hω
  by_contra hc
  simp only [mem_union, mem_ofPred_eq, not_or, not_not] at hc
  obtain ⟨htK, ha, has⟩ := hc
  refine hω (hball_subset_canonicalDomainOn (ρ := ρ) ha (fun z (hz : z ∈ ball 0 ρ ∩ H) => ?_) ?_)
  · show z + (t ω : ℂ) ∈ D
    refine hρD _ htK ⟨?_, ?_⟩
    · rw [mem_ball, dist_eq_norm, add_sub_cancel_right]
      simpa using hz.1
    · have h2 : (0 : ℝ) < z.im := hz.2
      show 0 < (z + (t ω : ℂ)).im
      simpa using h2
  · have : scaleParamOn γ (x C ω) (zoomDomain D (t ω)) * (R + 1) < ρ := by
      rwa [lt_div_iff₀ hR1] at has
    nlinarith

/-- **Clause (2) of D4⁺ʷ for Proposition 1.6's objects**, from `hloc`, `hsc0`, `hscale`,
`htight` (see the module docstring). -/
theorem prop16_weak_clause2 {γ : ℝ} {D : Set ℂ} {c d a b : ℝ} {h0 : ℂ → ℝ} {Ω : Type}
    [MeasurableSpace Ω] {P : Measure Ω} {X : Ω → FieldSample}
    (hdat : Prop16Data γ D c d a b h0 P X)
    (hν : AEMeasurable (fun ω => prop16Nu γ h0 a b (X ω)) P)
    (x : ℝ → Ω × ℝ → FieldSample) (V : ℝ → Ω × ℝ → Set ℂ)
    (hloc : ∀ C, ∀ᵐ p ∂(prop16Q γ h0 a b P X), IsLocallyGoodOn γ (V C p) (x C p) ∧
      zoomDomain D p.2 ⊆ V C p ∧ ContinuousOn (fun z => h0 (z + p.2) - h0 p.2) (V C p) ∧
      IsLocallyGoodOn γ (V C p) (zoomField γ C (ofFun h0 + X p.1) p.2) ∧
      qAreaMeasureOn γ (zoomField γ C (ofFun h0 + X p.1) p.2) (zoomDomain D p.2) =
        qAreaMeasureOn γ (ofFun (fun z => h0 (z + p.2) - h0 p.2) + x C p) (zoomDomain D p.2))
    (hsc0 : ∀ δ > 0, Tendsto (fun C => prop16Q γ h0 a b P X
      {p | ¬ (0 < scaleParamOn γ (x C p) (zoomDomain D p.2) ∧
        scaleParamOn γ (x C p) (zoomDomain D p.2) < δ)}) atTop (𝓝 0))
    (hscale : ∀ κ > 0, Tendsto (fun C => prop16Q γ h0 a b P X
      {p | ¬ (0 < scaleParamOn γ (x C p) (zoomDomain D p.2) ∧
        0 < scaleParamOn γ (ofFun (fun z => h0 (z + p.2) - h0 p.2) + x C p) (zoomDomain D p.2) ∧
        |scaleParamOn γ (ofFun (fun z => h0 (z + p.2) - h0 p.2) + x C p) (zoomDomain D p.2) -
            scaleParamOn γ (x C p) (zoomDomain D p.2)| ≤
          κ * scaleParamOn γ (x C p) (zoomDomain D p.2))}) atTop (𝓝 0))
    (htight : ∀ ρ > 0, ∀ θ > 0, ∃ M : ℝ, ∀ᶠ C in atTop, prop16Q γ h0 a b P X
      {p | ¬ qAreaMeasureOn γ (x C p) (zoomDomain D p.2)
        (ball 0 (ρ * scaleParamOn γ (x C p) (zoomDomain D p.2))) ≤ ENNReal.ofReal M} ≤ θ) :
    ∀ (R : ℕ) (f : ℂ → ℝ), Continuous f → HasCompactSupport f →
      (∀ z, f z ≠ 0 → z ∈ Metric.ball (0 : ℂ) R) → ∀ δ > 0,
      Tendsto (fun C => prop16Q γ h0 a b P X {p | δ <
        |∫ z, f z ∂(qAreaMeasureOn γ
            (canonicalOn γ (zoomField γ C (ofFun h0 + X p.1) p.2) (zoomDomain D p.2))
            (canonicalDomainOn γ (zoomField γ C (ofFun h0 + X p.1) p.2) (zoomDomain D p.2))) -
          Prop16Area.locArea γ R f (canonicalOn γ (x C p) (zoomDomain D p.2))|}) atTop (𝓝 0) := by
  intro R f hf hfc hfR δ hδ
  obtain ⟨hγ, -, ⟨hDo, -, -, hDH, -, -, hdisc⟩, -, hca, hbd, hh0, hP, -, hpos, hfin⟩ := hdat
  have hQ : IsProbabilityMeasure (prop16Q γ h0 a b P X) :=
    isProbabilityMeasure_prop16Law' hν hpos hfin
  have hta : ∀ᵐ p ∂(prop16Q γ h0 a b P X), p.2 ∈ Ioo a b :=
    ae_prop16Law_of_ae (G := fun _ t => t ∈ Ioo a b) (aemeasurable_prop16Kernel' hν hfin)
      (fun ω => sFinite_prop16Nu γ h0 a b (X ω)) (fun ω => prop16Nu_compl_Ioo γ h0 a b (X ω))
      (ae_of_all _ fun _ _ ht => ht)
  have hZo : ∀ t : ℝ, IsOpen (zoomDomain D t) := fun t =>
    hDo.preimage (continuous_id.add continuous_const)
  have hZH : ∀ t : ℝ, zoomDomain D t ⊆ H := fun t z hz => by
    have h1 : (0 : ℝ) < (z + (t : ℂ)).im := hDH hz
    show 0 < z.im
    simpa using h1
  -- `φ(a·) → 0`
  have hφ : ∀ ρ > 0, ∀ ε > 0, Tendsto (fun C => prop16Q γ h0 a b P X {p | ¬ ∀ z ∈ zoomDomain D p.2,
      ‖z‖ < ρ * scaleParamOn γ (x C p) (zoomDomain D p.2) →
        |h0 (z + p.2) - h0 p.2| ≤ ε}) atTop (𝓝 0) := by
    intro ρ hρ ε hε
    have hs' : ∀ r > 0, Tendsto (fun C => prop16Q γ h0 a b P X
        {p | ¬ scaleParamOn γ (x C p) (zoomDomain D p.2) < r}) atTop (𝓝 0) := fun r hr =>
      tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds (hsc0 r hr) (fun _ => bot_le)
        fun C => measure_mono fun p hp h => hp h.2
    have := tendsto_prob_osc (prop16Q γ h0 a b P X) hh0 subset_union_right Prod.snd
      measurable_snd hta (fun C p => scaleParamOn γ (x C p) (zoomDomain D p.2)) hs' hρ hε
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds this (fun _ => bot_le)
      fun C => measure_mono fun p hp h => hp fun z hz hzn => h z (Or.inl hz) hzn
  have hdom := tendsto_prob_hdom (prop16Q γ h0 a b P X) hca hbd hdisc Prod.snd measurable_snd hta
    x hsc0 R
  exact tendsto_pairing_locArea_close (prop16Q γ h0 a b P X) hγ
    (fun C p => zoomField γ C (ofFun h0 + X p.1) p.2) x
    (fun _ p => fun z => h0 (z + p.2) - h0 p.2) (fun _ p => zoomDomain D p.2) V
    (fun C => (hloc C).mono fun p h =>
      ⟨⟨h.1, hZo p.2, hZH p.2, h.2.1, h.2.2.1⟩, h.2.2.2.1, h.2.2.2.2⟩)
    hscale hφ htight R hdom hf hfc hfR hδ

end Prop16Asm

end QuantumZipper
