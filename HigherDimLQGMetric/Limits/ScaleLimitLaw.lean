import HigherDimLQGMetric.Limits.ScaleLawBridge
import HigherDimLQGMetric.Limits.ScaleMedian

/-!
# One-radius limit law of the rescaled metric

At each radius, a subsequence of deterministic LFPP normalization ratios has
a positive limit.  The resulting scaled limit law belongs to the compact
closure of the original LFPP metric laws.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Filter Topology Set

namespace HigherDimLQGMetric

open HigherDimLFPP (Rd e₁)

/-- At a fixed radius, the randomly rescaled limit law becomes a member of the
original LFPP compact closure after multiplication by a positive constant. -/
theorem l6c_scaleLimit_law_in_closure
    (hL6a : ∀ d ξ κ, L6a_tight d ξ κ)
    {d : ℕ} (ξ : ℝ) (κ : Rd d → ℝ)
    (hB2 : ∃ Q : ℝ, DGZ.DGZHyp d κ ξ Q ∧ DGZ.RealEpsAdapterShape d κ ξ Q)
    (εs : ℕ → ℝ) (hεs : ∀ n, 0 < εs n) (hεt : Tendsto εs atTop (𝓝 0))
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (h : Ω → DistRd d) (Dh : Ω → ContMetric d)
    (hh : IsNormalizedLGF h P) (hDh : Measurable Dh)
    (hstable : StablyTendstoLU P h
      (fun n ω => lfppSeq κ ξ εs (h ω) n) (fun ω => (Dh ω).1))
    {r : ℝ} (hr : 0 < r) :
    let K : Set (ProbabilityMeasure C(Rd d × Rd d, ℝ)) :=
      closure {ν | ∃ ε ∈ Ioo (0 : ℝ) 1,
        (ν : Measure C(Rd d × Rd d, ℝ)) =
          P.map (fun ω => toCMapRd ((aEps κ ξ ε)⁻¹ • lfppDist κ ξ ε (h ω)))}
    let Z : Ω → C(Rd d × Rd d, ℝ) := fun ω =>
      Real.exp (-ξ * sphereAvg (h ω) r 0) •
        (Dh ω).1.comp ⟨fun p : Rd d × Rd d => (r • p.1, r • p.2), by fun_prop⟩
    ∃ η : ProbabilityMeasure C(Rd d × Rd d, ℝ),
      (η : Measure C(Rd d × Rd d, ℝ)) = P.map Z ∧
      ∃ β : ℝ, 0 < β ∧ η.map (fun D => β • D) ∈ K := by
  let _ : PolishSpace C(Rd d × Rd d, ℝ) :=
    LQGMetric.polishSpace_continuousMap _ _
  intro K Z
  let Q := Classical.choose hB2
  have hQ : DGZ.DGZHyp d κ ξ Q := (Classical.choose_spec hB2).1
  have hd := hQ.dim
  have hκ := hQ.kernel
  have hA := (hL6a d ξ κ) hB2 P h hh.1.isLGFPlusBddCont
  have hK : IsCompact K := by
    let _ := TopologicalSpace.upgradeIsCompletelyMetrizable C(Rd d × Rd d, ℝ)
    apply isCompact_closure_of_isTightMeasureSet
    refine hA.2.2.1.subset ?_
    rintro μ ⟨ν, hν, rfl⟩
    exact hν
  obtain ⟨m₀, hm₀, hmK⟩ := l6c_uniform_lfppMedian_pos hL6a ξ κ hB2 P h hh
  let X : ℕ → Ω → C(Rd d × Rd d, ℝ) := fun n ω => lfppSeq κ ξ εs (h ω) n
  let Y : Ω → C(Rd d × Rd d, ℝ) := fun ω => (Dh ω).1
  have hX (n : ℕ) : AEMeasurable (X n) P :=
    l6a_aemeasurable_normalized_lfpp hd κ hκ ξ (hεs n) P h
      hh.1.isLGFPlusBddCont
  have hY : AEMeasurable Y P :=
    (measurable_subtype_coe.comp hDh).aemeasurable
  let W : ℕ → Ω → C(Rd d × Rd d, ℝ) := fun n ω =>
    Real.exp (-ξ * sphereAvg (h ω) r 0) •
      (X n ω).comp ⟨fun p : Rd d × Rd d => (r • p.1, r • p.2), by fun_prop⟩
  have hW := l6c_stable_scaleLaw P h hh.1.measurable X Y hX hY hstable ξ r
  let ηn : ℕ → ProbabilityMeasure C(Rd d × Rd d, ℝ) := fun n =>
    ⟨P.map (W n), (Measure.isProbabilityMeasure_map_iff
      (hW.forall_aemeasurable n)).mpr inferInstance⟩
  let η : ProbabilityMeasure C(Rd d × Rd d, ℝ) :=
    ⟨P.map Z, (Measure.isProbabilityMeasure_map_iff
      hW.aemeasurable_limit).mpr inferInstance⟩
  have hη : Tendsto ηn atTop (𝓝 η) := hW.tendsto
  let νn : ℕ → ProbabilityMeasure C(Rd d × Rd d, ℝ) := fun n =>
    ⟨P.map (fun ω => toCMapRd ((aEps κ ξ (εs n / r))⁻¹ •
      lfppDist κ ξ (εs n / r) (h ω))),
      (Measure.isProbabilityMeasure_map_iff
        (l6a_aemeasurable_normalized_lfpp hd κ hκ ξ
          (div_pos (hεs n) hr) P h hh.1.isLGFPlusBddCont)).mpr inferInstance⟩
  let b : ℕ → ℝ := fun n =>
    aEps κ ξ (εs n) / (r * aEps κ ξ (εs n / r))
  have hb (n : ℕ) : 0 < b n := by
    dsimp [b]
    exact div_pos (l6a_aEps_pos hd κ hκ ξ (hεs n))
      (mul_pos hr (l6a_aEps_pos hd κ hκ ξ (div_pos (hεs n) hr)))
  have hν (n : ℕ) : (νn n : Measure C(Rd d × Rd d, ℝ)) =
      (ηn n : Measure C(Rd d × Rd d, ℝ)).map (fun D => b n • D) := by
    exact l6c_law_scaled_prelimit hd κ hκ ξ P h hh (hεs n) hr
  have hεr0 : Tendsto (fun n => εs n / r) atTop (𝓝 0) := by
    simpa using hεt.div_const r
  have hsmall : ∀ᶠ n in atTop, εs n / r < 1 :=
    hεr0.eventually (gt_mem_nhds one_pos)
  have hνK : ∀ᶠ n in atTop, νn n ∈ K := by
    filter_upwards [hsmall] with n hn
    apply subset_closure
    refine ⟨εs n / r, ⟨div_pos (hεs n) hr, hn⟩, ?_⟩
    rfl
  have hmedlo : ∀ᶠ n in atTop,
      m₀ ≤ lowerMedian (νn n : Measure C(Rd d × Rd d, ℝ))
        (fun D => D (0, e₁ d)) := hνK.mono (fun n hn => hmK (νn n) hn)
  have hmedhi : ∀ᶠ n in atTop,
      lowerMedian (νn n : Measure C(Rd d × Rd d, ℝ))
        (fun D => D (0, e₁ d)) ≤ 1 :=
    hνK.mono (fun n hn => l6c_lfppMedian_le_one hL6a ξ κ hB2 P h hh (νn n) hn)
  have hpos : ∀ᵐ D ∂(η : Measure C(Rd d × Rd d, ℝ)), 0 < D (0, e₁ d) := by
    change ∀ᵐ D ∂(P.map Z), 0 < D (0, e₁ d)
    have hset : MeasurableSet {D : C(Rd d × Rd d, ℝ) | 0 < D (0, e₁ d)} := by
      have he : Continuous (fun D : C(Rd d × Rd d, ℝ) => D (0, e₁ d)) :=
        continuous_eval_const _
      exact (isOpen_Ioi.preimage he).measurableSet
    rw [ae_map_iff hW.aemeasurable_limit hset]
    filter_upwards with ω
    simpa [Z, Y] using
      l6c_scalePoint_pos (by omega : 0 < d) ξ hr (h ω) (Dh ω)
  obtain ⟨_, _, β, hβ, _, hβK, _⟩ :=
    l6c_ratio_cluster ηn νn η b hb hη hν K hK hνK m₀ hm₀
      hmedlo hmedhi hpos
  exact ⟨η, rfl, β, hβ, hβK⟩

end HigherDimLQGMetric
