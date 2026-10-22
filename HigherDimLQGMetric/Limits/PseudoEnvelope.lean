import HigherDimLQGMetric.Sec10.Envelope

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open MeasureTheory Set Topology Filter
namespace HigherDimLQGMetric
open HigherDimLFPP (Rd)

private theorem l6c_supEnvelope_diag_alg {d : ℕ}
    {K : Set C(Rd d × Rd d, ℝ)} (hKne : K.Nonempty)
    (hKalg : K ⊆ metricAlgSet_select) (x : Rd d) :
    s8a_supEnvelope K (x,x) = 0 := by
  have he : (fun M : C(Rd d × Rd d, ℝ) => M (x,x)) '' K = {0} := by
    ext z
    constructor
    · rintro ⟨M, hM, rfl⟩
      exact Set.mem_singleton_iff.mpr ((hKalg hM).1 x)
    · intro hz
      obtain ⟨M, hM⟩ := hKne
      exact ⟨M, hM, by simpa [Set.mem_singleton_iff.mp hz] using (hKalg hM).1 x⟩
  simp only [s8a_supEnvelope, he, csSup_singleton]

private theorem l6c_envelope_abs_diff {d : ℕ}
    {K : Set C(Rd d × Rd d, ℝ)} (hK : IsCompact K)
    {a b : ℝ} (hb : 0 ≤ b)
    {E : C(Rd d × Rd d, ℝ)} (hE : E ∈ s8a_envelope K a b)
    (p q : Rd d × Rd d) :
    |E p - E q| ≤ b * (s8a_supEnvelope K (p.1,q.1) +
      s8a_supEnvelope K (p.2,q.2)) := by
  have halg := hE.1
  have h1 := halg.2.2 p.1 q.1 p.2
  have h2 := halg.2.2 q.1 q.2 p.2
  have h3 := halg.2.2 q.1 p.1 q.2
  have h4 := halg.2.2 p.1 p.2 q.2
  have hfirst : E p - E q ≤ E (p.1,q.1) + E (p.2,q.2) := by
    rw [halg.2.1 q.2 p.2] at h2
    linarith
  have hsecond : -(E p - E q) ≤ E (p.1,q.1) + E (p.2,q.2) := by
    rw [halg.2.1 q.1 p.1] at h3
    linarith
  have hcross := add_le_add (s8a_envelope_upper hK hb hE (p.1,q.1))
    (s8a_envelope_upper hK hb hE (p.2,q.2))
  rw [← mul_add] at hcross
  have hlower : -(E (p.1,q.1) + E (p.2,q.2)) ≤ E p - E q := by linarith
  exact (abs_le.mpr ⟨hlower, hfirst⟩).trans hcross

/-- Compactness of a closed envelope requires only the metric algebra laws of
its witness family. Separation is not needed for Arzelà–Ascoli. -/
theorem l6c_pseudoEnvelope_isCompact {d : ℕ}
    {K : Set C(Rd d × Rd d, ℝ)} (hK : IsCompact K)
    (hKalg : K ⊆ metricAlgSet_select)
    {a b : ℝ} (_ha : 0 < a) (hb : 0 ≤ b) :
    IsCompact (s8a_envelope K a b) := by
  by_cases hKne : K.Nonempty
  · let S := s8a_envelope K a b
    have hSclosed : IsClosed S := s8a_envelope_isClosed K hK a b
    have hU := s8a_continuous_supEnvelope K hK
    have hdiag : ∀ x : Rd d, s8a_supEnvelope K (x,x) = 0 :=
      l6c_supEnvelope_diag_alg hKne hKalg
    have hEqui : Equicontinuous (fun E : S => (E.1 : Rd d × Rd d → ℝ)) := by
      intro p
      rw [Metric.equicontinuousAt_iff_right]
      intro ε hε
      let V : Rd d × Rd d → ℝ := fun q =>
        b * (s8a_supEnvelope K (p.1,q.1) + s8a_supEnvelope K (p.2,q.2))
      have hVc : ContinuousAt V p := by
        exact (continuous_const.mul ((hU.comp (continuous_const.prodMk continuous_fst)).add
          (hU.comp (continuous_const.prodMk continuous_snd)))).continuousAt
      have hV0 : V p = 0 := by simp [V, hdiag]
      have hev : ∀ᶠ q in 𝓝 p, V q < ε := hVc.eventually (gt_mem_nhds (by simpa only [hV0] using hε))
      filter_upwards [hev] with q hq E
      rw [Real.dist_eq]
      exact (l6c_envelope_abs_diff hK hb E.2 p q).trans_lt hq
    have hclosedEmbedding : IsClosedEmbedding
        (UniformOnFun.ofFun {J : Set (Rd d × Rd d) | IsCompact J} ∘
          fun E : S => (E.1 : Rd d × Rd d → ℝ)) := by
      have hcover : ⋃₀ {J : Set (Rd d × Rd d) | IsCompact J} = univ := by
        apply eq_univ_iff_forall.mpr
        intro p
        exact mem_sUnion_of_mem (mem_singleton p) isCompact_singleton
      let : T2Space (UniformOnFun (Rd d × Rd d) ℝ
          {J : Set (Rd d × Rd d) | IsCompact J}) :=
        UniformOnFun.t2Space_of_covering hcover
      simpa only [ContinuousMap.toUniformOnFunIsCompact, Function.comp_def] using
        (ContinuousMap.isUniformEmbedding_toUniformOnFunIsCompact.isClosedEmbedding.comp
          hSclosed.isClosedEmbedding_subtypeVal)
    have hpoint : ∀ J ∈ ({J : Set (Rd d × Rd d) | IsCompact J}),
        ∀ p ∈ J, ∃ Q : Set ℝ, IsCompact Q ∧ ∀ E : S, E.1 p ∈ Q := by
      intro J _ p _
      refine ⟨Set.Icc 0 (max (b * s8a_supEnvelope K p) 0), isCompact_Icc, ?_⟩
      intro E
      have hnonneg : 0 ≤ E.1 p := by
        have htri := E.2.1.2.2 p.1 p.2 p.1
        rw [E.2.1.1, E.2.1.2.1 p.2 p.1] at htri
        linarith
      exact ⟨hnonneg, (s8a_envelope_upper hK hb E.2 p).trans (le_max_left _ _)⟩
    have hcompactS : CompactSpace S :=
      ArzelaAscoli.compactSpace_of_isClosedEmbedding
        (fun _ hJ => hJ) hclosedEmbedding
        (fun J _ => hEqui.equicontinuousOn J) hpoint
    exact isCompact_iff_compactSpace.mpr hcompactS
  · have hKe : K = ∅ := Set.not_nonempty_iff_eq_empty.mp hKne
    have hSe : s8a_envelope K a b = ∅ := by
      ext E
      simp [s8a_envelope, hKe]
    rw [hSe]
    exact isCompact_empty

end HigherDimLQGMetric
