import HigherDimLQGMetric.Locality.SkorokhodFull

/-! Skorokhod representation with a fixed measurable Polish observation of
the field attached to every finite stage. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.style.haveILetI false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology

namespace HigherDimLQGMetric

open HigherDimLFPP (Rd)

theorem l7a_exists_skorokhod_marks
    (hL6a : ∀ d ξ κ, L6a_tight d ξ κ)
    {d : ℕ} (hd : 2 ≤ d) (ξ : ℝ) (κ : Rd d → ℝ)
    (hκ : HigherDimLFPP.IsLFPPKernel κ)
    (hB2 : ∃ Q : ℝ, DGZ.DGZHyp d κ ξ Q ∧ DGZ.RealEpsAdapterShape d κ ξ Q)
    (εs : ℕ → ℝ) (hεs : ∀ n, 0 < εs n)
    (hεt : Tendsto εs atTop (𝓝 0))
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (h : Ω → DistRd d) (Dh : Ω → ContMetric d)
    (hh : IsNormalizedLGF h P) (hDh : Measurable Dh)
    (hstable : StablyTendstoLU P h
      (fun n ω => lfppSeq κ ξ εs (h ω) n) (fun ω => (Dh ω).1))
    {M : Type} [TopologicalSpace M] [MeasurableSpace M]
    [OpensMeasurableSpace M] [BorelSpace M] [PolishSpace M]
    (Φ : (CoordJ → ℝ) → M) (hΦ : Measurable Φ) :
    ∃ (E : Type) (_ : MeasurableSpace E) (_ : StandardBorelSpace E)
      (Q : Measure E), IsProbabilityMeasure Q ∧
      ∃ (Z : ℕ → E → ((CoordJ → ℝ) × M) × C(Rd d × Rd d, ℝ))
        (Zlim : E → ((CoordJ → ℝ) × M) × C(Rd d × Rd d, ℝ)),
        (∀ n, Measurable (Z n)) ∧ Measurable Zlim ∧
        (∀ n, Q.map (Z n) = P.map (fun ω =>
          ((pairJ ⊤ (h ω), Φ (pairJ ⊤ (h ω))),
            lfppSeq κ ξ εs (h ω) n))) ∧
        Q.map Zlim = P.map (fun ω =>
          ((pairJ ⊤ (h ω), Φ (pairJ ⊤ (h ω))), (Dh ω).1)) ∧
        (∀ e, Tendsto (fun n => Z n e) atTop (𝓝 (Zlim e))) ∧
        (∀ᵐ e ∂Q, IsContLengthFn (Zlim e).2 ∧ IsProperFn (Zlim e).2) := by
  letI : PolishSpace C(Rd d × Rd d, ℝ) :=
    LQGMetric.polishSpace_continuousMap _ _
  let X : ℕ → Ω → C(Rd d × Rd d, ℝ) :=
    fun n ω => lfppSeq κ ξ εs (h ω) n
  let Y : Ω → C(Rd d × Rd d, ℝ) := fun ω => (Dh ω).1
  let Ψ : (CoordJ → ℝ) → (CoordJ → ℝ) × M := fun x => (x, Φ x)
  have hΨ : Measurable Ψ := measurable_id.prodMk hΦ
  have hXa (n : ℕ) : AEMeasurable (X n) P :=
    l6a_aemeasurable_normalized_lfpp hd κ hκ ξ (hεs n) P h
      hh.1.isLGFPlusBddCont
  have hYm : Measurable Y := measurable_subtype_coe.comp hDh
  have hν := l7a_stable_adjoin_field_ae P h hh.1.measurable X Y
    hXa hYm hstable Ψ hΨ
  obtain ⟨E, mE, hsb, Q, hQ, Z, Zlim, hZm, hZlimm,
    hZlaw, hZlimlaw, hZc⟩ :=
    LQGMetric.DFGPS.L217.exists_skorokhod_representation_sb hν
  letI : MeasurableSpace E := mE
  letI : StandardBorelSpace E := hsb
  letI : IsProbabilityMeasure Q := hQ
  have hgoodlaw := l7a_stable_limit_law_good hL6a ξ κ hB2
    εs hεs hεt P h Dh hh hDh hstable
  have hYlaw : Q.map (fun e => (Zlim e).2) = P.map Y := by
    calc
      Q.map (fun e => (Zlim e).2) = (Q.map Zlim).map Prod.snd :=
        (Measure.map_map measurable_snd hZlimm).symm
      _ = (P.map (fun ω => ((pairJ ⊤ (h ω), Φ (pairJ ⊤ (h ω))),
          Y ω))).map Prod.snd := by
        rw [hZlimlaw]
        change (P.map (fun ω => ((pairJ ⊤ (h ω), Φ (pairJ ⊤ (h ω))),
          Y ω))).map Prod.snd = _
        rfl
      _ = P.map Y := by
        simpa only [Function.comp_def] using
          (Measure.map_map measurable_snd
            (((((measurable_pairJ ⊤).comp hh.1.measurable).prodMk
              (hΦ.comp ((measurable_pairJ ⊤).comp hh.1.measurable))).prodMk hYm)))
  have hgood : ∀ᵐ e ∂Q,
      IsContLengthFn (Zlim e).2 ∧ IsProperFn (Zlim e).2 := by
    have ht : ∀ᵐ D ∂Q.map (fun e => (Zlim e).2),
        IsContLengthFn D ∧ IsProperFn D := by
      rw [hYlaw]
      exact hgoodlaw
    exact ae_of_ae_map (measurable_snd.comp hZlimm).aemeasurable ht
  exact ⟨E, mE, hsb, Q, hQ, Z, Zlim, hZm, hZlimm,
    hZlaw, hZlimlaw, hZc, hgood⟩

end HigherDimLQGMetric
