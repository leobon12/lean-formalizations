import HigherDimLQGMetric.Sec10.Perturb
import HigherDimLQGMetric.Select.MetricBorel
import Mathlib.Topology.UniformSpace.Ascoli
import Mathlib.Topology.Maps.Proper.Basic

/-!
# Compact envelopes of metric functions

This file contains the deterministic Arzelà–Ascoli step for transferring tightness under
uniform comparison with a compact set of continuous metrics.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set Topology

namespace HigherDimLQGMetric

open HigherDimLFPP (Rd)

variable {d : ℕ}

/-- The closed algebraic metric conditions and a two-sided comparison to a member of `K`. -/
def s8a_envelope (K : Set C(Rd d × Rd d, ℝ)) (a b : ℝ) :
    Set C(Rd d × Rd d, ℝ) :=
  {E | E ∈ metricAlgSet_select (d := d) ∧
    ∃ M ∈ K, ∀ p : Rd d × Rd d, a * M p ≤ E p ∧ E p ≤ b * M p}

private theorem s8a_isClosed_comparison (K : Set C(Rd d × Rd d, ℝ))
    (hK : IsCompact K) (a b : ℝ) :
    IsClosed {E : C(Rd d × Rd d, ℝ) |
      ∃ M ∈ K, ∀ p : Rd d × Rd d, a * M p ≤ E p ∧ E p ≤ b * M p} := by
  let : CompactSpace K := isCompact_iff_compactSpace.mp hK
  let A : Set (K × C(Rd d × Rd d, ℝ)) :=
    {q | ∀ p : Rd d × Rd d,
      a * (q.1 : C(Rd d × Rd d, ℝ)) p ≤ q.2 p ∧
      q.2 p ≤ b * (q.1 : C(Rd d × Rd d, ℝ)) p}
  have hA : IsClosed A := by
    unfold A
    simp only [ofPred_forall]
    apply isClosed_iInter
    intro p
    apply IsClosed.inter
    · change IsClosed {q : K × C(Rd d × Rd d, ℝ) |
        a * (q.1 : C(Rd d × Rd d, ℝ)) p ≤ q.2 p}
      exact isClosed_le
        (continuous_const.mul ((continuous_eval_const p).comp
          (continuous_subtype_val.comp continuous_fst)))
        ((continuous_eval_const p).comp continuous_snd)
    · change IsClosed {q : K × C(Rd d × Rd d, ℝ) |
        q.2 p ≤ b * (q.1 : C(Rd d × Rd d, ℝ)) p}
      exact isClosed_le
        ((continuous_eval_const p).comp continuous_snd)
        (continuous_const.mul ((continuous_eval_const p).comp
          (continuous_subtype_val.comp continuous_fst)))
  have himage : IsClosed ((Prod.snd : K × C(Rd d × Rd d, ℝ) →
      C(Rd d × Rd d, ℝ)) '' A) := isClosedMap_snd_of_compactSpace A hA
  convert himage using 1
  ext E
  simp only [mem_ofPred_eq, mem_image, Prod.exists]
  constructor
  · rintro ⟨M, hM, hcmp⟩
    exact ⟨⟨M, hM⟩, E, hcmp, rfl⟩
  · rintro ⟨M, E', hcmp, he⟩
    subst E'
    exact ⟨M.1, M.2, hcmp⟩

/-- Compact-witness metric envelopes are closed. -/
theorem s8a_envelope_isClosed (K : Set C(Rd d × Rd d, ℝ))
    (hK : IsCompact K) (a b : ℝ) : IsClosed (s8a_envelope K a b) := by
  unfold s8a_envelope
  exact (isClosed_metricAlgSet_select d).inter (s8a_isClosed_comparison K hK a b)

/-- The lower comparison transfers the Euclidean topology from the witness metric. -/
theorem s8a_envelope_isContinuousMetric {K : Set C(Rd d × Rd d, ℝ)}
    (hK : K ⊆ {M | IsContinuousMetric M}) {a b : ℝ} (ha : 0 < a)
    {E : C(Rd d × Rd d, ℝ)} (hE : E ∈ s8a_envelope K a b) :
    IsContinuousMetric E := by
  obtain ⟨halg, M, hM, hcmp⟩ := hE
  have hMm : IsContinuousMetric M := hK hM
  refine { self_eq_zero := halg.1
           eq_of_eq_zero := ?_
           symm := halg.2.1
           triangle := halg.2.2
           euclidean_of_small := ?_ }
  · intro x y h0
    have hle := (hcmp (x, y)).1
    rw [h0] at hle
    have hM0 : 0 ≤ M (x, y) := by
      have htri := hMm.triangle x y x
      rw [hMm.self_eq_zero, hMm.symm y x] at htri
      linarith
    have hMzero : M (x, y) = 0 := by nlinarith
    exact hMm.eq_of_eq_zero x y hMzero
  · intro x ε hε
    obtain ⟨δ, hδ, hsmall⟩ := hMm.euclidean_of_small x ε hε
    refine ⟨a * δ, mul_pos ha hδ, fun y hy => ?_⟩
    apply hsmall
    have hle := (hcmp (x, y)).1
    nlinarith [lt_of_le_of_lt hle hy]

/-- Pointwise supremum of a compact family of metric functions. -/
def s8a_supEnvelope (K : Set C(Rd d × Rd d, ℝ))
    (p : Rd d × Rd d) : ℝ := sSup ((fun M : C(Rd d × Rd d, ℝ) => M p) '' K)

theorem s8a_continuous_supEnvelope (K : Set C(Rd d × Rd d, ℝ))
    (hK : IsCompact K) : Continuous (s8a_supEnvelope K) := by
  have hc : Continuous (fun q : (Rd d × Rd d) × C(Rd d × Rd d, ℝ) => q.2 q.1) :=
    continuous_eval.comp (continuous_snd.prodMk continuous_fst)
  exact hK.continuous_sSup hc

theorem s8a_le_supEnvelope {K : Set C(Rd d × Rd d, ℝ)}
    (hK : IsCompact K) {M : C(Rd d × Rd d, ℝ)} (hM : M ∈ K)
    (p : Rd d × Rd d) : M p ≤ s8a_supEnvelope K p := by
  unfold s8a_supEnvelope
  exact le_csSup (hK.bddAbove_image (continuous_eval_const p).continuousOn)
    ⟨M, hM, rfl⟩

/-- A compact witness family gives a uniform pointwise upper bound on its envelope. -/
theorem s8a_envelope_upper {K : Set C(Rd d × Rd d, ℝ)}
    (hK : IsCompact K) {a b : ℝ} (hb : 0 ≤ b)
    {E : C(Rd d × Rd d, ℝ)} (hE : E ∈ s8a_envelope K a b)
    (p : Rd d × Rd d) : E p ≤ b * s8a_supEnvelope K p := by
  obtain ⟨_, M, hM, hcmp⟩ := hE
  exact (hcmp p).2.trans (mul_le_mul_of_nonneg_left (s8a_le_supEnvelope hK hM p) hb)

private theorem s8a_envelope_abs_diff {K : Set C(Rd d × Rd d, ℝ)}
    (hK : IsCompact K) {a b : ℝ} (hb : 0 ≤ b)
    {E : C(Rd d × Rd d, ℝ)} (hE : E ∈ s8a_envelope K a b)
    (p q : Rd d × Rd d) :
    |E p - E q| ≤ b * (s8a_supEnvelope K (p.1, q.1) +
      s8a_supEnvelope K (p.2, q.2)) := by
  have halg := hE.1
  have h1 := halg.2.2 p.1 q.1 p.2
  have h2 := halg.2.2 q.1 q.2 p.2
  have h3 := halg.2.2 q.1 p.1 q.2
  have h4 := halg.2.2 p.1 p.2 q.2
  have hfirst : E p - E q ≤ E (p.1, q.1) + E (p.2, q.2) := by
    rw [halg.2.1 q.2 p.2] at h2
    linarith
  have hsecond : -(E p - E q) ≤ E (p.1, q.1) + E (p.2, q.2) := by
    rw [halg.2.1 q.1 p.1] at h3
    linarith
  have hcross := add_le_add (s8a_envelope_upper hK hb hE (p.1, q.1))
    (s8a_envelope_upper hK hb hE (p.2, q.2))
  rw [← mul_add] at hcross
  have hlower : -(E (p.1, q.1) + E (p.2, q.2)) ≤ E p - E q := by linarith
  exact (abs_le.mpr ⟨hlower, hfirst⟩).trans hcross

theorem s8a_metricFn_nonneg {E : C(Rd d × Rd d, ℝ)}
    (hE : IsContinuousMetric E) (x y : Rd d) : 0 ≤ E (x, y) := by
  have h := hE.triangle x y x
  rw [hE.self_eq_zero, hE.symm y x] at h
  linarith

theorem s8a_supEnvelope_diag {K : Set C(Rd d × Rd d, ℝ)}
    (hKnonempty : K.Nonempty) (hKm : K ⊆ {M | IsContinuousMetric M})
    (x : Rd d) : s8a_supEnvelope K (x, x) = 0 := by
  have he : (fun M : C(Rd d × Rd d, ℝ) => M (x, x)) '' K = {0} := by
    ext z
    constructor
    · rintro ⟨M, hM, rfl⟩
      exact Set.mem_singleton_iff.mpr ((hKm hM).self_eq_zero x)
    · intro hz
      obtain ⟨M, hM⟩ := hKnonempty
      exact ⟨M, hM, by simpa [Set.mem_singleton_iff.mp hz] using (hKm hM).self_eq_zero x⟩
  simp only [s8a_supEnvelope, he, csSup_singleton]

/-- A closed metric envelope over a compact set is compact in the local uniform topology. -/
theorem s8a_envelope_isCompact {K : Set C(Rd d × Rd d, ℝ)}
    (hK : IsCompact K) (hKm : K ⊆ {M | IsContinuousMetric M})
    {a b : ℝ} (ha : 0 < a) (hb : 0 ≤ b) : IsCompact (s8a_envelope K a b) := by
  by_cases hKn : K.Nonempty
  · let S := s8a_envelope K a b
    have hSclosed : IsClosed S := s8a_envelope_isClosed K hK a b
    have hU := s8a_continuous_supEnvelope K hK
    have hdiag : ∀ x : Rd d, s8a_supEnvelope K (x, x) = 0 :=
      s8a_supEnvelope_diag hKn hKm
    have hEqui : Equicontinuous (fun E : S => (E.1 : Rd d × Rd d → ℝ)) := by
      intro p
      rw [Metric.equicontinuousAt_iff_right]
      intro ε hε
      let V : Rd d × Rd d → ℝ := fun q =>
        b * (s8a_supEnvelope K (p.1, q.1) + s8a_supEnvelope K (p.2, q.2))
      have hVc : ContinuousAt V p := by
        exact (continuous_const.mul ((hU.comp (continuous_const.prodMk continuous_fst)).add
          (hU.comp (continuous_const.prodMk continuous_snd)))).continuousAt
      have hV0 : V p = 0 := by simp [V, hdiag]
      have hev : ∀ᶠ q in 𝓝 p, V q < ε := by
        have := hVc.eventually (gt_mem_nhds (by simpa only [hV0] using hε))
        exact this
      filter_upwards [hev] with q hq E
      rw [Real.dist_eq]
      exact (s8a_envelope_abs_diff hK hb E.2 p q).trans_lt hq
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
      exact ⟨s8a_metricFn_nonneg (s8a_envelope_isContinuousMetric hKm ha E.2) p.1 p.2,
        (s8a_envelope_upper hK hb E.2 p).trans (le_max_left _ _)⟩
    have hcompactS : CompactSpace S :=
      ArzelaAscoli.compactSpace_of_isClosedEmbedding
        (fun _ hJ => hJ) hclosedEmbedding
        (fun J _ => hEqui.equicontinuousOn J) hpoint
    exact isCompact_iff_compactSpace.mpr hcompactS
  · have hKe : K = ∅ := Set.not_nonempty_iff_eq_empty.mp hKn
    have hSe : s8a_envelope K a b = ∅ := by
      ext E
      simp [s8a_envelope, hKe]
    rw [hSe]
    exact isCompact_empty

/-- On a connected metric domain, an equicontinuous family of continuous functions that
vanishes at one point is pointwise bounded. -/
theorem s8a_pointwiseBounded_of_equicontinuous
    {X : Type*} [MetricSpace X] [ConnectedSpace X]
    (S : Set C(X, ℝ))
    (hEqui : Equicontinuous (fun E : S => (E.1 : X → ℝ)))
    (x₀ : X) (hzero : ∀ E : S, E.1 x₀ = 0)
    (x : X) : ∃ M : ℝ, ∀ E : S, |E.1 x| ≤ M := by
  let U : Set X := {p | ∃ M : ℝ, ∀ E : S, |E.1 p| ≤ M}
  have hnear : ∀ p : X, ∃ δ > 0, ∀ q, dist q p < δ → (p ∈ U ↔ q ∈ U) := by
    intro p
    obtain ⟨δ, hδ, hmod⟩ := Metric.equicontinuousAt_iff.mp (hEqui p) 1 one_pos
    refine ⟨δ, hδ, fun q hq => ?_⟩
    have hdiff : ∀ E : S, |E.1 q - E.1 p| < 1 := by
      intro E
      simpa only [Real.dist_eq, abs_sub_comm] using hmod q hq E
    constructor
    · rintro ⟨M, hM⟩
      refine ⟨M + 1, fun E => ?_⟩
      have ht := abs_sub_abs_le_abs_sub (E.1 q) (E.1 p)
      linarith [hM E, hdiff E]
    · rintro ⟨M, hM⟩
      refine ⟨M + 1, fun E => ?_⟩
      have ht := abs_sub_abs_le_abs_sub (E.1 p) (E.1 q)
      rw [abs_sub_comm] at ht
      linarith [hM E, hdiff E]
  have hUopen : IsOpen U := Metric.isOpen_iff.mpr fun p hp => by
    obtain ⟨δ, hδ, hn⟩ := hnear p
    exact ⟨δ, hδ, fun q hq => (hn q (by simpa only [dist_comm] using
      (Metric.mem_ball.mp hq))).1 hp⟩
  have hUclosed : IsClosed U := by
    rw [← isOpen_compl_iff]
    refine Metric.isOpen_iff.mpr fun p hp => ?_
    obtain ⟨δ, hδ, hn⟩ := hnear p
    exact ⟨δ, hδ, fun q hq hqU => hp
      ((hn q (by simpa only [dist_comm] using (Metric.mem_ball.mp hq))).2 hqU)⟩
  have hUne : U.Nonempty := ⟨x₀, 0, fun E => by rw [hzero E, abs_zero]⟩
  have hUall : U = univ := (isClopen_iff.mp ⟨hUclosed, hUopen⟩).resolve_left hUne.ne_empty
  have hx : x ∈ U := hUall.symm ▸ mem_univ x
  exact hx

/-- Closed equicontinuous families of metric functions are compact: the metric axioms and
connectedness supply pointwise boundedness for Arzelà–Ascoli. -/
theorem s8a_isCompact_of_closed_equicontinuous_metric
    {S : Set C(Rd d × Rd d, ℝ)} (hSclosed : IsClosed S)
    (hSmetric : S ⊆ {E | IsContinuousMetric E})
    (hEqui : Equicontinuous (fun E : S => (E.1 : Rd d × Rd d → ℝ))) :
    IsCompact S := by
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
    obtain ⟨M, hM⟩ := s8a_pointwiseBounded_of_equicontinuous S hEqui
      ((0 : Rd d), (0 : Rd d)) (fun E => (hSmetric E.2).self_eq_zero 0) p
    refine ⟨Icc (-M) M, isCompact_Icc, fun E => ?_⟩
    exact abs_le.mp (hM E)
  have hcompactS : CompactSpace S :=
    ArzelaAscoli.compactSpace_of_isClosedEmbedding
      (fun _ hJ => hJ) hclosedEmbedding
      (fun J _ => hEqui.equicontinuousOn J) hpoint
  exact isCompact_iff_compactSpace.mpr hcompactS

end HigherDimLQGMetric
