import HigherDimLQGMetric.Determ.CenterPre
import HigherDimLQGMetric.Local.CopiesMain
import LQGMetric.Papers.LM.C1_8Trans
import HigherDimLQGMetric.Modulus.Tilt

/-! Locality and length transfer across equal field–metric laws. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.style.haveILetI false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set
open LQGMetric.GM.Bilip
open HigherDimLFPP (Rd)
open scoped ENNReal

namespace HigherDimLQGMetric

private theorem determ_jl_chain_of_internal {d : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} {h : Ω → DistRd d} {D : Ω → ContMetric d}
    (ξ : ℝ) (z : Rd d) (r : ℝ) (hlen : ∀ᵐ ω ∂P, (D ω).IsLength)
    (hI : IsJointlyLocalRd P (fun ω => l7b_recenter (h ω) r z)
      (l7b_intFam ξ h D r z) (l7b_intFam ξ h D r z)) :
    IsJointlyLocalRd P (fun ω => l7b_recenter (h ω) r z)
      (l7b_chainFam ξ h D r z) (l7b_chainFam ξ h D r z) := by
  intro V hV
  let W : Set (Rd d) := (closure (V : Set (Rd d)))ᶜ
  have hW : IsOpen W := isClosed_closure.isOpen_compl
  have H := hI V hV
  change LQGMetric.CondIndepEv (fieldSigmaRd (fun ω => l7b_recenter (h ω) r z) V)
    (famSigmaRd (l7b_intFam ξ h D r z) V ⊔ famSigmaRd (l7b_intFam ξ h D r z) V)
    (fullSigmaRd (fun ω => l7b_recenter (h ω) r z) ⊔
      famSigmaRd (l7b_intFam ξ h D r z) W ⊔
      famSigmaRd (l7b_intFam ξ h D r z) W) P at H
  refine LQGMetric.GM.Bilip.CondIndepEv.of_le_aeClosure H ?_ ?_
  · exact sup_le
      ((l7b_chainSigma_le_ae_int hlen r z V.isOpen).trans (aeClosure_mono le_sup_left))
      ((l7b_chainSigma_le_ae_int hlen r z V.isOpen).trans (aeClosure_mono le_sup_right))
  · exact sup_le (sup_le (le_sup_left.trans le_sup_left |>.trans (le_aeClosure _))
      ((l7b_chainSigma_le_ae_int hlen r z hW).trans
        (aeClosure_mono (le_sup_right.trans le_sup_left))))
      ((l7b_chainSigma_le_ae_int hlen r z hW).trans (aeClosure_mono le_sup_right))

private theorem determ_jl_internal_of_chain {d : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} {h : Ω → DistRd d} {D : Ω → ContMetric d}
    (ξ : ℝ) (z : Rd d) (r : ℝ) (hlen : ∀ᵐ ω ∂P, (D ω).IsLength)
    (hI : IsJointlyLocalRd P (fun ω => l7b_recenter (h ω) r z)
      (l7b_chainFam ξ h D r z) (l7b_chainFam ξ h D r z)) :
    IsJointlyLocalRd P (fun ω => l7b_recenter (h ω) r z)
      (l7b_intFam ξ h D r z) (l7b_intFam ξ h D r z) := by
  intro V hV
  let W : Set (Rd d) := (closure (V : Set (Rd d)))ᶜ
  have hW : IsOpen W := isClosed_closure.isOpen_compl
  have H := hI V hV
  change LQGMetric.CondIndepEv (fieldSigmaRd (fun ω => l7b_recenter (h ω) r z) V)
    (famSigmaRd (l7b_chainFam ξ h D r z) V ⊔ famSigmaRd (l7b_chainFam ξ h D r z) V)
    (fullSigmaRd (fun ω => l7b_recenter (h ω) r z) ⊔
      famSigmaRd (l7b_chainFam ξ h D r z) W ⊔
      famSigmaRd (l7b_chainFam ξ h D r z) W) P at H
  refine LQGMetric.GM.Bilip.CondIndepEv.of_le_aeClosure H ?_ ?_
  · exact sup_le
      ((l7b_intSigma_le_ae_chain hlen r z V.isOpen).trans (aeClosure_mono le_sup_left))
      ((l7b_intSigma_le_ae_chain hlen r z V.isOpen).trans (aeClosure_mono le_sup_right))
  · exact sup_le (sup_le (le_sup_left.trans le_sup_left |>.trans (le_aeClosure _))
      ((l7b_intSigma_le_ae_chain hlen r z hW).trans
        (aeClosure_mono (le_sup_right.trans le_sup_left))))
      ((l7b_intSigma_le_ae_chain hlen r z hW).trans (aeClosure_mono le_sup_right))

/-- The Borel chain version of ξ-locality depends only on the joint law of field and metric. -/
private theorem determ_jl_chain_law {d : ℕ} {Ω Ω' : Type*}
    [MeasurableSpace Ω] [MeasurableSpace Ω']
    (P : Measure Ω) (P' : Measure Ω') [IsProbabilityMeasure P]
    [IsProbabilityMeasure P'] (h : Ω → DistRd d) (D : Ω → ContMetric d)
    (h' : Ω' → DistRd d) (D' : Ω' → ContMetric d)
    (hh : Measurable h) (hD : Measurable D)
    (hh' : Measurable h') (hD' : Measurable D')
    (hlaw : P.map (fun ω => (h ω, D ω)) = P'.map (fun ω => (h' ω, D' ω)))
    (ξ : ℝ) (z : Rd d) (r : ℝ)
    (hI : IsJointlyLocalRd P (fun ω => l7b_recenter (h ω) r z)
      (l7b_chainFam ξ h D r z) (l7b_chainFam ξ h D r z)) :
    IsJointlyLocalRd P' (fun ω => l7b_recenter (h' ω) r z)
      (l7b_chainFam ξ h' D' r z) (l7b_chainFam ξ h' D' r z) := by
  intro V hV
  let Φ : Ω → DistRd d × ContMetric d := fun ω => (h ω, D ω)
  let Ψ : Ω' → DistRd d × ContMetric d := fun ω => (h' ω, D' ω)
  let k : DistRd d × ContMetric d → DistRd d := fun t => l7b_recenter t.1 r z
  let J : DistRd d × ContMetric d → Set (Rd d) → Rd d → Rd d → ℝ≥0∞ :=
    l7b_chainFam ξ (fun t : DistRd d × ContMetric d => t.1)
      (fun t : DistRd d × ContMetric d => t.2) r z
  let W : Set (Rd d) := (closure (V : Set (Rd d)))ᶜ
  have hW : IsOpen W := isClosed_closure.isOpen_compl
  have hΦ : Measurable Φ := hh.prodMk hD
  have hΨ : Measurable Ψ := hh'.prodMk hD'
  have hk : Measurable k := (l7b_measurable_recenter r z).comp measurable_fst
  have hJ (U : Set (Rd d)) :
      Measurable (fun t : DistRd d × ContMetric d => J t U) :=
    l7b_measurable_chainFam ξ measurable_fst measurable_snd r z U
  have hG : fieldSigmaRd k V ≤
      (inferInstance : MeasurableSpace (DistRd d × ContMetric d)) :=
    ((measurable_restrictTo V).comp hk).comap_le
  have hA : famSigmaRd J (V : Set (Rd d)) ⊔ famSigmaRd J (V : Set (Rd d)) ≤
      (inferInstance : MeasurableSpace (DistRd d × ContMetric d)) :=
    sup_le (hJ V).comap_le (hJ V).comap_le
  have hB : fullSigmaRd k ⊔ famSigmaRd J W ⊔ famSigmaRd J W ≤
      (inferInstance : MeasurableSpace (DistRd d × ContMetric d)) :=
    sup_le (sup_le hk.comap_le (hJ W).comap_le) (hJ W).comap_le
  have hsource : LQGMetric.CondIndepEv
      ((fieldSigmaRd k V).comap Φ)
      ((famSigmaRd J (V : Set (Rd d)) ⊔ famSigmaRd J (V : Set (Rd d))).comap Φ)
      ((fullSigmaRd k ⊔ famSigmaRd J W ⊔ famSigmaRd J W).comap Φ) P := by
    simp only [fieldSigmaRd, famSigmaRd, fullSigmaRd,
      MeasurableSpace.comap_sup, MeasurableSpace.comap_comp]
    exact hI V hV
  have hbase := LQGMetric.DFGPS.L217.condIndepEv_map hΦ hG hA hB hsource
  rw [hlaw] at hbase
  have htarget := LQGMetric.LM.c18_condIndepEv_comap hΨ hG hA hB hbase
  have hGc : (fieldSigmaRd k V).comap Ψ =
      fieldSigmaRd (fun ω => l7b_recenter (h' ω) r z) V := by
    simp only [fieldSigmaRd, MeasurableSpace.comap_comp]
    rfl
  have hAc : (famSigmaRd J (V : Set (Rd d)) ⊔
      famSigmaRd J (V : Set (Rd d))).comap Ψ =
      famSigmaRd (l7b_chainFam ξ h' D' r z) V ⊔
        famSigmaRd (l7b_chainFam ξ h' D' r z) V := by
    simp only [famSigmaRd, MeasurableSpace.comap_sup, MeasurableSpace.comap_comp]
    rfl
  have hBc : (fullSigmaRd k ⊔ famSigmaRd J W ⊔ famSigmaRd J W).comap Ψ =
      fullSigmaRd (fun ω => l7b_recenter (h' ω) r z) ⊔
        famSigmaRd (l7b_chainFam ξ h' D' r z) W ⊔
        famSigmaRd (l7b_chainFam ξ h' D' r z) W := by
    simp only [fullSigmaRd, famSigmaRd, MeasurableSpace.comap_sup,
      MeasurableSpace.comap_comp]
    rfl
  rw [hGc, hAc, hBc] at htarget
  exact htarget

/-- The universally measurable length-metric property transfers through equal Borel laws. -/
theorem determ_length_law_transfer {d : ℕ} {Ω Ω' : Type*}
    [MeasurableSpace Ω] [MeasurableSpace Ω']
    (P : Measure Ω) (P' : Measure Ω') [IsProbabilityMeasure P]
    [IsProbabilityMeasure P'] (D : Ω → ContMetric d) (D' : Ω' → ContMetric d)
    (hD : Measurable D) (hD' : Measurable D')
    (hlaw : P.map D = P'.map D')
    (hlen : ∀ᵐ ω ∂P, (D ω).IsLength) :
    ∀ᵐ ω ∂P', (D' ω).IsLength := by
  haveI : IsProbabilityMeasure (P.map D) :=
    (Measure.isProbabilityMeasure_map_iff hD.aemeasurable).2 inferInstance
  obtain ⟨M, hMS, hM, hMae⟩ :=
    (determ_uMeasurableSet_isLength d (P.map D) inferInstance).exists_measurable_subset_ae_eq
  obtain ⟨N, hSN, hN, hN0⟩ := exists_measurable_superset_of_null
    (show (P.map D) ({E : ContMetric d | E.IsLength} \ M) = 0 from ae_le_set.1 hMae.symm.le)
  have hDM : ∀ᵐ ω ∂P, D ω ∈ M := by
    have hN' : ∀ᵐ ω ∂P, D ω ∉ N := by
      rw [Measure.map_apply hD hN] at hN0
      exact measure_eq_zero_iff_ae_notMem.1 hN0
    filter_upwards [hlen, hN'] with ω h1 h2
    by_contra h3
    exact h2 (hSN ⟨h1, h3⟩)
  have hmap : ∀ᵐ E ∂P.map D, E ∈ M :=
    (ae_map_iff hD.aemeasurable hM).2 hDM
  rw [hlaw] at hmap
  exact ((ae_map_iff hD'.aemeasurable hM).1 hmap).mono fun _ hE => hMS hE

/-- ξ-additivity of one metric is a property of its field–metric law. -/
theorem determ_xiAdditive_law_transfer {d : ℕ} {Ω Ω' : Type*}
    [MeasurableSpace Ω] [MeasurableSpace Ω']
    (P : Measure Ω) (P' : Measure Ω') [IsProbabilityMeasure P]
    [IsProbabilityMeasure P'] (h : Ω → DistRd d) (D : Ω → ContMetric d)
    (h' : Ω' → DistRd d) (D' : Ω' → ContMetric d)
    (hh : Measurable h) (hD : Measurable D)
    (hh' : Measurable h') (hD' : Measurable D')
    (hlaw : P.map (fun ω => (h ω, D ω)) = P'.map (fun ω => (h' ω, D' ω)))
    (ξ : ℝ) (hadd : IsXiAdditiveRd ξ P h D D) :
    IsXiAdditiveRd ξ P' h' D' D' := by
  have hDlaw : P.map D = P'.map D' := by
    calc
      P.map D = (P.map (fun ω => (h ω, D ω))).map Prod.snd := by
        rw [Measure.map_map measurable_snd (hh.prodMk hD)]
        rfl
      _ = (P'.map (fun ω => (h' ω, D' ω))).map Prod.snd := by rw [hlaw]
      _ = P'.map D' := by
        rw [Measure.map_map measurable_snd (hh'.prodMk hD')]
        rfl
  have hlen : ∀ᵐ ω ∂P, (D ω).IsLength := hadd.2.2.1.mono fun _ hω => hω.1
  have hlen' := determ_length_law_transfer P P' D D' hD hD' hDlaw hlen
  refine ⟨hD', hD', ?_, ?_⟩
  · exact hlen'.mono fun _ hω => ⟨hω, hω⟩
  · intro z r hr
    exact determ_jl_internal_of_chain ξ z r hlen'
      (determ_jl_chain_law P P' h D h' D' hh hD hh' hD' hlaw ξ z r
        (determ_jl_chain_of_internal ξ z r hlen (hadd.2.2.2 z r hr)))

/-- The normalized LGF property transfers to another measurable realization of its law. -/
theorem determ_normalized_law_transfer {d : ℕ} {Ω Ω' : Type*}
    [MeasurableSpace Ω] [MeasurableSpace Ω']
    (P : Measure Ω) (P' : Measure Ω')
    (h : Ω → DistRd d) (h' : Ω' → DistRd d)
    (hh : IsNormalizedLGF h P) (hh' : Measurable h')
    (hlaw : P.map h = P'.map h') : IsNormalizedLGF h' P' := by
  have hpair : P'.map (pairProc h') = P.map (pairProc h) := by
    have hproc : Measurable (ev0 : DistRd d → TestRd0 d → ℝ) :=
      measurable_pi_iff.2 fun φ => measurable_distOn_apply φ.1
    calc
      P'.map (pairProc h') = (P'.map h').map ev0 := by
        rw [Measure.map_map hproc hh']
        rfl
      _ = (P.map h).map ev0 := by rw [← hlaw]
      _ = P.map (pairProc h) := by
        rw [Measure.map_map hproc hh.1.measurable]
        rfl
  have hwhole : IsWholeSpaceLGF h' P' :=
    w3b_isWholeSpaceLGF_of_map_pairProc_eq hh.1 hh' hpair
  refine ⟨hwhole, ?_⟩
  have hS : MeasurableSet {g : DistRd d | sphereAvg g 1 0 = 0} :=
    measurableSet_eq_fun (measurable_sphereAvg_left 1 0) measurable_const
  have hmap : ∀ᵐ g ∂P.map h, sphereAvg g 1 0 = 0 :=
    (ae_map_iff hh.1.measurable.aemeasurable hS).2 hh.2
  rw [hlaw] at hmap
  exact (ae_map_iff hh'.aemeasurable hS).1 hmap

end HigherDimLQGMetric
