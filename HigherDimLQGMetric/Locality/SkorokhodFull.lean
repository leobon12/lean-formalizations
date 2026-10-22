import HigherDimLQGMetric.Locality.SkorokhodGraph
import HigherDimLQGMetric.Locality.StableAdjoinAE
import LQGMetric.Papers.DFGPS.L2_17Core3B

/-! A Skorokhod representation of the stable field–LFPP law. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.style.haveILetI false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology

namespace HigherDimLQGMetric

open HigherDimLFPP (Rd)

theorem l7a_exists_skorokhod_full
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
      (fun n ω => lfppSeq κ ξ εs (h ω) n) (fun ω => (Dh ω).1)) :
    ∃ (E : Type) (_ : MeasurableSpace E) (_ : StandardBorelSpace E)
      (Q : Measure E), IsProbabilityMeasure Q ∧
      ∃ (Z : ℕ → E → (CoordJ → ℝ) × C(Rd d × Rd d, ℝ))
        (Zlim : E → (CoordJ → ℝ) × C(Rd d × Rd d, ℝ)),
        (∀ n, Measurable (Z n)) ∧ Measurable Zlim ∧
        (∀ n, Q.map (Z n) = P.map
          (fun ω => (pairJ ⊤ (h ω), lfppSeq κ ξ εs (h ω) n))) ∧
        Q.map Zlim = P.map (fun ω => (pairJ ⊤ (h ω), (Dh ω).1)) ∧
        (∀ e, Tendsto (fun n => Z n e) atTop (𝓝 (Zlim e))) ∧
        (∀ n, Q.map (fun e => pairJInv ⊤ (Z n e).1) = P.map h) ∧
        Q.map (fun e => pairJInv ⊤ (Zlim e).1) = P.map h ∧
        (∀ᵐ e ∂Q, ∀ n, (Z n e).2 =
          lfppSeq κ ξ εs (pairJInv ⊤ (Z n e).1) n) ∧
        (∀ᵐ e ∂Q, IsContLengthFn (Zlim e).2 ∧ IsProperFn (Zlim e).2) := by
  letI : PolishSpace C(Rd d × Rd d, ℝ) :=
    LQGMetric.polishSpace_continuousMap _ _
  let X : ℕ → Ω → C(Rd d × Rd d, ℝ) :=
    fun n ω => lfppSeq κ ξ εs (h ω) n
  let Y : Ω → C(Rd d × Rd d, ℝ) := fun ω => (Dh ω).1
  have hXa (n : ℕ) : AEMeasurable (X n) P :=
    l6a_aemeasurable_normalized_lfpp hd κ hκ ξ (hεs n) P h
      hh.1.isLGFPlusBddCont
  have hYm : Measurable Y := measurable_subtype_coe.comp hDh
  have hν := l7a_stable_adjoin_field_ae P h hh.1.measurable X Y
    hXa hYm hstable (id : (CoordJ → ℝ) → CoordJ → ℝ) measurable_id
  simp only [id_eq] at hν
  obtain ⟨E, mE, hsb, Q, hQ, Z, Zlim, hZm, hZlimm,
    hZlaw, hZlimlaw, hZc⟩ :=
    LQGMetric.DFGPS.L217.exists_skorokhod_representation_sb hν
  letI : MeasurableSpace E := mE
  letI : StandardBorelSpace E := hsb
  letI : IsProbabilityMeasure Q := hQ
  have hfieldlaw (n : ℕ) :
      Q.map (fun e => pairJInv ⊤ (Z n e).1) = P.map h := by
    obtain ⟨F, hFm, _, hgraphlaw⟩ :=
      l7a_lfpp_joint_law_graph hd κ hκ ξ εs hεs P h hh n
    have hX : Measurable (fun q : (CoordJ → ℝ) × C(Rd d × Rd d, ℝ) =>
        pairJInv (d := d) ⊤ q.1) :=
      (measurable_pairJInv (d := d) ⊤).comp measurable_fst
    calc
      Q.map (fun e => pairJInv ⊤ (Z n e).1) =
          (Q.map (Z n)).map (fun q => pairJInv ⊤ q.1) :=
        (Measure.map_map hX (hZm n)).symm
      _ = ((P.map h).map (fun g => (pairJ ⊤ g, F g))).map
          (fun q => pairJInv ⊤ q.1) := by
        rw [hZlaw n]
        change (P.map (fun ω => (pairJ ⊤ (h ω), X n ω))).map
            (fun q => pairJInv ⊤ q.1) = _
        rw [hgraphlaw]
      _ = (P.map h).map (id : DistRd d → DistRd d) := by
        rw [Measure.map_map hX ((measurable_pairJ ⊤).prodMk hFm)]
        congr 1
        funext g
        exact pairJInv_pairJ ⊤ g
      _ = P.map h := Measure.map_id
  have hfieldlim :
      Q.map (fun e => pairJInv ⊤ (Zlim e).1) = P.map h := by
    have hX : Measurable (fun q : (CoordJ → ℝ) × C(Rd d × Rd d, ℝ) =>
        pairJInv (d := d) ⊤ q.1) :=
      (measurable_pairJInv (d := d) ⊤).comp measurable_fst
    calc
      Q.map (fun e => pairJInv ⊤ (Zlim e).1) =
          (Q.map Zlim).map (fun q => pairJInv ⊤ q.1) :=
        (Measure.map_map hX hZlimm).symm
      _ = (P.map (fun ω => (pairJ ⊤ (h ω), Y ω))).map
          (fun q => pairJInv ⊤ q.1) := by
        rw [hZlimlaw]
        change (P.map (fun ω => (pairJ ⊤ (h ω), Y ω))).map
            (fun q => pairJInv ⊤ q.1) = _
        rfl
      _ = P.map (id ∘ h) := by
        simpa only [Function.comp_def, pairJInv_pairJ, id_eq] using
          (Measure.map_map hX
            (((measurable_pairJ ⊤).comp hh.1.measurable).prodMk hYm))
      _ = P.map h := rfl
  have hgraph (n : ℕ) : ∀ᵐ e ∂Q, (Z n e).2 =
      lfppSeq κ ξ εs (pairJInv ⊤ (Z n e).1) n :=
    l7a_ae_graph_of_joint_law hd κ hκ ξ εs hεs P h hh n Q
      (Z n) (hZm n) (hZlaw n)
  have hgoodlaw := l7a_stable_limit_law_good hL6a ξ κ hB2
    εs hεs hεt P h Dh hh hDh hstable
  have hYlaw : Q.map (fun e => (Zlim e).2) = P.map Y := by
    calc
      Q.map (fun e => (Zlim e).2) = (Q.map Zlim).map Prod.snd :=
        (Measure.map_map measurable_snd hZlimm).symm
      _ = (P.map (fun ω => (pairJ ⊤ (h ω), Y ω))).map Prod.snd := by
        rw [hZlimlaw]
        change (P.map (fun ω => (pairJ ⊤ (h ω), Y ω))).map Prod.snd = _
        rfl
      _ = P.map Y := by
        simpa only [Function.comp_def] using
          (Measure.map_map measurable_snd
            (((measurable_pairJ ⊤).comp hh.1.measurable).prodMk hYm))
  have hgood : ∀ᵐ e ∂Q,
      IsContLengthFn (Zlim e).2 ∧ IsProperFn (Zlim e).2 := by
    have ht : ∀ᵐ D ∂Q.map (fun e => (Zlim e).2),
        IsContLengthFn D ∧ IsProperFn D := by
      rw [hYlaw]
      exact hgoodlaw
    exact ae_of_ae_map (measurable_snd.comp hZlimm).aemeasurable ht
  exact ⟨E, mE, hsb, Q, hQ, Z, Zlim, hZm, hZlimm,
    hZlaw, hZlimlaw, hZc, hfieldlaw, hfieldlim,
    ae_all_iff.mpr hgraph, hgood⟩

end HigherDimLQGMetric
