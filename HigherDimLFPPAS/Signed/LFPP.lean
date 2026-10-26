import HigherDimLFPPAS.Frozen.IsAdmissibleSeed
import HigherDimLFPPAS.Signed.Sec4
import HigherDimLQGMetric.Main.LFPPMedian
import HigherDimLQGMetric.Main.Cor104
import HigherDimLQGMetric.Sec4.AEpsLocBdd
import HigherDimLQGMetric.Sec4.LfppTight

/-!
# Sign-free copies: `𝔞_ε`: positivity and local boundedness; LFPP bounds from tightness

Packet G1 (ruling L7; planning audit `planning/audits/MA3-inputs.md` §4.1 and §4.3 items 1–2). The declarations of
`HigherDimLQGMetric.Main.LFPPMedian`, `HigherDimLQGMetric.Main.Cor104`, `HigherDimLQGMetric.Sec4.AEpsLocBdd`,
`HigherDimLQGMetric.Sec4.LfppTight`
whose statements mention the kernel predicate, copied with hypothesis `HigherDimLFPPAS.IsAdmissibleSeed κ` (the
paper's seeds: no sign condition) in place of `HigherDimLFPP.IsLFPPKernel κ`. Each copy `<name>_seed` has the
statement of `HigherDimLQGMetric.<name>` except for the kernel hypothesis (kernel-dependent definitions it mentions
are replaced by their copies); its proof is the host proof, with calls to copied declarations redirected to the
copies and everything else reused directly. Host-private helpers called by the copied proofs are copied as private
`<name>_seed`.
No proof uses nonnegativity of the seed: `IsAdmissibleSeed` has no such field.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace HigherDimLFPPAS.Signed

open HigherDimLQGMetric

section LFPPMedian
/-! Copies from `HigherDimLQGMetric.Main.LFPPMedian`. -/

set_option maxHeartbeats 300000
open MeasureTheory Filter Topology Set
open scoped ENNReal
open HigherDimLFPP (Rd e₁)

/-- For a normalized LGF, every positive-cutoff convolution field is continuous a.s.
Sign-free copy of `HigherDimLQGMetric.l10a_ae_continuous_convMollify`. -/
theorem l10a_ae_continuous_convMollify_seed {d : ℕ} (hd : 2 ≤ d)
    (κ : Rd d → ℝ) (hκ : HigherDimLFPPAS.IsAdmissibleSeed κ)
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (h : Ω → DistRd d) (hh : IsNormalizedLGF h P) {ε : ℝ} (hε : 0 < ε) :
    ∀ᵐ ω ∂P, Continuous fun z => convMollify κ ε (h ω) z := by
  have hC := l2b_ae_convMollify_continuousOn_seed d hd κ hκ P h hh
  exact hC.mono (fun ω hω => by
    have hc : Continuous fun z : Rd d => (ε, z) := continuous_const.prodMk continuous_id
    have hf := hω.comp_continuous hc (fun _ => ⟨hε, mem_univ _⟩)
    simpa only [Function.comp_def, Prod.fst, Prod.snd] using hf)

/-- The whole-space LFPP point distance is a.e.-measurable for a normalized LGF.
Sign-free copy of `HigherDimLQGMetric.l10a_aemeasurable_lfppPoint`. -/
theorem l10a_aemeasurable_lfppPoint_seed {d : ℕ} (hd : 2 ≤ d)
    (κ : Rd d → ℝ) (hκ : HigherDimLFPPAS.IsAdmissibleSeed κ)
    (ξ : ℝ) {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (h : Ω → DistRd d) (hh : IsNormalizedLGF h P) {ε : ℝ} (hε : 0 < ε) :
    AEMeasurable (fun ω => lfppDist κ ξ ε (h ω) (0, e₁ d)) P := by
  let H : Rd d → Ω → ℝ := fun z ω => convMollify κ ε (h ω) z
  have hm : ∀ z, Measurable (H z) := fun z =>
    (l10a_measurable_convMollify_apply κ ε z).comp hh.1.measurable
  have hc : ∀ᵐ ω ∂P, Continuous fun z => H z ω :=
    l10a_ae_continuous_convMollify_seed hd κ hκ P h hh hε
  classical
  let Y : Rd d → Ω → ℝ := fun z ω =>
    if hcont : Continuous (fun z => H z ω) then H z ω else 0
  have hYc : ∀ ω, Continuous fun z => Y z ω := by
    intro ω
    by_cases hcont : Continuous (fun z => H z ω)
    · have heq : (fun z => Y z ω) = (fun z => H z ω) := by
        funext z
        exact dite_eq_left hcont
      rw [heq]
      exact hcont
    · have heq : (fun z => Y z ω) = (fun _ => 0) := by
        funext z
        exact dite_eq_right hcont
      rw [heq]
      exact continuous_const
  have hYae : ∀ᵐ ω ∂P, ∀ z, Y z ω = H z ω := by
    filter_upwards [hc] with ω hω z
    exact dite_eq_left hω
  have hYm : ∀ z, AEMeasurable (Y z) P := by
    intro z
    have heq : Y z =ᵐ[P] H z := hYae.mono fun _ hω => hω z
    exact (aemeasurable_congr heq.symm).1 (hm z).aemeasurable
  have hCM := l10a_aemeasurable_toContMap Y hYm hYc
  have hF : Measurable (fun φ : C(Rd d, ℝ) =>
      HigherDimLFPP.lfppDistOn ξ φ univ 0 (e₁ d)) :=
    HigherDimLFPP.measurable_lfppDistOn_continuousMap isOpen_univ ξ 0 (e₁ d)
  have hAY : AEMeasurable (fun ω =>
      HigherDimLFPP.lfppDistOn ξ (fun z => Y z ω) univ 0 (e₁ d)) P := by
    simpa only [Function.comp_def, ContinuousMap.coe_mk] using hF.comp_aemeasurable hCM
  have heq : (fun ω => HigherDimLFPP.lfppDistOn ξ (fun z => Y z ω) univ 0 (e₁ d)) =ᵐ[P]
      (fun ω => lfppDist κ ξ ε (h ω) (0, e₁ d)) := by
    filter_upwards [hYae] with ω hω
    simp only [lfppDist]
    congr 1
    funext z
    exact hω z
  exact (aemeasurable_congr heq).1 hAY

end LFPPMedian

section Cor104
/-! Copies from `HigherDimLQGMetric.Main.Cor104`. -/

set_option linter.style.haveILetI false
open MeasureTheory Filter Topology Set
open scoped ENNReal
open HigherDimLFPP (Rd e₁)

/-- The LFPP normalizer is positive.
Sign-free copy of `HigherDimLQGMetric.l10a_aEps_pos`. -/
theorem l10a_aEps_pos_seed {d : ℕ} (hd : 2 ≤ d)
    {κ : Rd d → ℝ} (hκ : HigherDimLFPPAS.IsAdmissibleSeed κ)
    (ξ : ℝ) {ε : ℝ} (hε : 0 < ε) : 0 < aEps κ ξ ε := by
  letI : IsProbabilityMeasure (normLGFLaw d) := (normLGFLaw_spec_holds d hd).1
  have hn : IsNormalizedLGF id (normLGFLaw d) := (normLGFLaw_spec_holds d hd).2.1
  have hXm : AEMeasurable (fun g : DistRd d => lfppDist κ ξ ε g (0, e₁ d))
      (normLGFLaw d) := l10a_aemeasurable_lfppPoint_seed hd κ hκ ξ (normLGFLaw d) id hn hε
  have hc := l10a_ae_continuous_convMollify_seed hd κ hκ (normLGFLaw d) id hn hε
  have hXp : ∀ᵐ g ∂(normLGFLaw d), 0 < lfppDist κ ξ ε g (0, e₁ d) := by
    filter_upwards [hc] with g hg
    exact HigherDimLFPP.lfppDistOn_pos hg
      (HigherDimLFPP.e₁_ne_zero (by omega : 0 < d)).symm
      ((HigherDimLFPP.pcwJoined_cube d).mono (subset_univ _))
  rw [l6a_aEps_eq_lowerMedian]
  exact l6a_lowerMedian_pos (normLGFLaw d)
    (fun g => lfppDist κ ξ ε g (0, e₁ d)) hXm hXp

end Cor104

section AEpsLocBdd
/-! Copies from `HigherDimLQGMetric.Sec4.AEpsLocBdd`. -/

open MeasureTheory Set Filter Topology Metric
open scoped ENNReal
open HigherDimLFPP (Rd e₁ lfppDistOn)
variable {d : ℕ}

/-- **Local boundedness of `𝔞_δ`** (MA6 P11): for `0 < a`, `𝔞_δ` is bounded above and below by positive constants
on `[a, b]`.
Sign-free copy of `HigherDimLQGMetric.l9b_aEps_locBdd`. -/
theorem l9b_aEps_locBdd_seed (hd : 2 ≤ d) {κ : Rd d → ℝ} (hκ : HigherDimLFPPAS.IsAdmissibleSeed κ) (ξ : ℝ)
    {a b : ℝ} (ha : 0 < a) :
    ∃ B : ℝ, 0 < B ∧ ∀ δ ∈ Icc a b, B⁻¹ ≤ aEps κ ξ δ ∧ aEps κ ξ δ ≤ B := by
  have hprob : IsProbabilityMeasure (normLGFLaw d) := (normLGFLaw_spec_holds d hd).1
  have hnorm : IsNormalizedLGF id (normLGFLaw d) := (normLGFLaw_spec_holds d hd).2.1
  set P : Measure (DistRd d) := normLGFLaw d with hP
  set K : Set (ℝ × Rd d) := Icc a b ×ˢ closedBall (0 : Rd d) 1 with hK
  obtain ⟨T, hTc, hTK, hKT⟩ := TopologicalSpace.exists_countable_dense_subset K
  let E : ℕ → Set (DistRd d) := fun n => ⋂ p ∈ T, {g | |convMollify κ p.1 g p.2| ≤ n}
  have hEm : ∀ n, MeasurableSet (E n) := fun n =>
    MeasurableSet.biInter hTc fun p _ =>
      measurableSet_le (continuous_abs.measurable.comp (l10a_measurable_convMollify_apply κ p.1 p.2))
        measurable_const
  have hEmono : Monotone E := by
    intro m n hmn g hg
    refine mem_iInter₂.2 fun p hp => ?_
    have h1 : |convMollify κ p.1 g p.2| ≤ m := mem_iInter₂.1 hg p hp
    have h2 : (m : ℝ) ≤ n := by exact_mod_cast hmn
    exact h1.trans h2
  have hjoint := l2b_ae_convMollify_continuousOn_seed d hd κ hκ P id hnorm
  have hKsub : K ⊆ Ioi 0 ×ˢ univ :=
    prod_mono (fun δ hδ => mem_Ioi.2 (ha.trans_le hδ.1)) (subset_univ _)
  have hKc : IsCompact K := isCompact_Icc.prod (isCompact_closedBall 0 1)
  have hcover : ∀ᵐ g ∂P, g ∈ ⋃ n, E n := by
    filter_upwards [hjoint] with g hg
    obtain ⟨M, hM⟩ := hKc.exists_bound_of_continuousOn (hg.mono hKsub)
    obtain ⟨n, hn⟩ := exists_nat_ge M
    refine mem_iUnion.2 ⟨n, mem_iInter₂.2 fun p hp => ?_⟩
    have h1 := hM p (hTK hp)
    rw [Real.norm_eq_abs] at h1
    show |convMollify κ p.1 g p.2| ≤ n
    exact h1.trans hn
  have hfull : P (⋃ n, E n) = 1 := by
    have hset : (⋃ n, E n) =ᵐ[P] (univ : Set (DistRd d)) :=
      hcover.mono fun g hg => propext ⟨fun _ => mem_univ g, fun _ => hg⟩
    rw [measure_congr hset, measure_univ]
  have hlim := tendsto_measure_iUnion_atTop (μ := P) hEmono
  rw [hfull] at hlim
  have hhalf : (2 : ℝ≥0∞)⁻¹ < 1 := ENNReal.inv_lt_one.2 (by norm_num)
  obtain ⟨n, hn⟩ := (hlim.eventually (Ioi_mem_nhds hhalf)).exists
  have hn' : (2 : ℝ≥0∞)⁻¹ < P (E n) := hn
  -- the complement of the good event has probability `< 1/2`
  have hcompl : P (E n)ᶜ < (2 : ℝ≥0∞)⁻¹ := by
    rw [prob_compl_eq_one_sub (hEm n)]
    refine ENNReal.sub_lt_of_lt_add prob_le_one ?_
    calc (1 : ℝ≥0∞) = 2⁻¹ + 2⁻¹ := ENNReal.inv_two_add_inv_two.symm
      _ < 2⁻¹ + P (E n) := ENNReal.add_lt_add_left (by simp) hn'
  refine ⟨Real.exp (|ξ| * n), Real.exp_pos _, fun δ hδ => ?_⟩
  have hδ0 : 0 < δ := ha.trans_le hδ.1
  -- on the good event, the two-sided bound holds at `δ`
  have hgood : ∀ᵐ g ∂P, g ∈ E n → Real.exp (-(|ξ| * n)) ≤ lfppDist κ ξ δ g (0, e₁ d) ∧
      lfppDist κ ξ δ g (0, e₁ d) ≤ Real.exp (|ξ| * n) := by
    filter_upwards [hjoint] with g hg hgE
    have hc : Continuous (convMollify κ δ g) := by
      have hc' : Continuous fun z : Rd d => (δ, z) := continuous_const.prodMk continuous_id
      have hf := hg.comp_continuous hc' (fun _ => ⟨hδ0, mem_univ _⟩)
      simpa only [Function.comp_def, id_eq] using hf
    have hbd : ∀ x ∈ closedBall (0 : Rd d) 1, |convMollify κ δ g x| ≤ n := by
      intro x hx
      have hpK : (δ, x) ∈ K := ⟨hδ, hx⟩
      have hcw : ContinuousWithinAt (fun p : ℝ × Rd d => |convMollify κ p.1 (id g) p.2|) T (δ, x) :=
        ((hg (δ, x) (hKsub hpK)).mono (hTK.trans hKsub)).abs
      exact hcw.closure_le (hKT hpK) continuousWithinAt_const fun p hp => mem_iInter₂.1 hgE p hp
    exact l9b_lfppDist_e₁_bounds (by omega) hc hbd
  have hup : (2 : ℝ≥0∞)⁻¹ ≤ P {g | lfppDist κ ξ δ g (0, e₁ d) ≤ Real.exp (|ξ| * n)} :=
    hn'.le.trans (measure_mono_ae (hgood.mono fun g hg hgE => (hg hgE).2))
  have hlow : P {g | lfppDist κ ξ δ g (0, e₁ d) < Real.exp (-(|ξ| * n))} < (2 : ℝ≥0∞)⁻¹ :=
    lt_of_le_of_lt (measure_mono_ae (hgood.mono fun g hg
      (hlt : lfppDist κ ξ δ g (0, e₁ d) < Real.exp (-(|ξ| * n))) =>
        (fun hgE : g ∈ E n => absurd hlt (not_lt.2 (hg hgE).1) : g ∉ E n))) hcompl
  refine ⟨?_, l9b_aEps_le hup⟩
  rw [← Real.exp_neg]
  exact l9b_le_aEps hup hlow

end AEpsLocBdd

section LfppTight
/-! Copies from `HigherDimLQGMetric.Sec4.LfppTight`. -/

open MeasureTheory Set Filter Topology Metric
open scoped ENNReal
open HigherDimLFPP (Rd e₁ lfppDistOn PcwJoined lfppLength)
variable {d : ℕ}

/-- a.s. continuity of the convolution field on the canonical space
Sign-free copy of `HigherDimLQGMetric.l9b_canonical_cont`. -/
theorem l9b_canonical_cont_seed (hd : 2 ≤ d) {κ : Rd d → ℝ} (hκ : HigherDimLFPPAS.IsAdmissibleSeed κ)
    {δ : ℝ} (hδ : 0 < δ) : ∀ᵐ g ∂(normLGFLaw d), Continuous (convMollify κ δ g) := by
  have := l9b_normLGFLaw_prob hd
  filter_upwards [l2b_ae_convMollify_continuousOn_seed d hd κ hκ (normLGFLaw d) id
    (l9b_normLGFLaw_normalized hd)] with g hg
  have hc : Continuous fun z : Rd d => (δ, z) := continuous_const.prodMk continuous_id
  have hf := hg.comp_continuous hc (fun _ => ⟨hδ, mem_univ _⟩)
  simpa only [Function.comp_def, id] using hf
section Canonical
variable {κ : Rd d → ℝ} {ξ : ℝ}

/-- **Across lower bound** (MA6 P2, LFPP family): for `0 < a < b` and `θ > 0` there is `c > 0` with
`normLGFLaw{D^δ(∂B_a, ∂B_b) < c 𝔞_δ} < θ` for every `δ ∈ (0,1)`.
Sign-free copy of `HigherDimLQGMetric.l9b_lfpp_across_lower`. -/
theorem l9b_lfpp_across_lower_seed (hd : 2 ≤ d) (hκ : HigherDimLFPPAS.IsAdmissibleSeed κ)
    (hpos : ∀ δ ∈ Ioo (0 : ℝ) 1, 0 < aEps κ ξ δ)
    (hT : TightOver (normLGFLaw d) (fun δ g => lfppX κ ξ δ g) (Ioo 0 1))
    {a b : ℝ} (ha : 0 < a) (hab : a < b) {θ : ℝ≥0∞} (hθ : 0 < θ) :
    ∃ c : ℝ, 0 < c ∧ ∀ δ ∈ Ioo (0 : ℝ) 1, normLGFLaw d {g |
      DGZ.lfppSetDist ξ (convMollify κ δ g) univ (sphere 0 a) (sphere 0 b) < c * aEps κ ξ δ} < θ := by
  have := l9b_normLGFLaw_prob hd
  have hOff : ∀ p : Rd d × Rd d, p ∈ sphere (0 : Rd d) a ×ˢ sphere (0 : Rd d) b → p.1 ≠ p.2 := by
    intro p hp heq
    have h1 : dist p.1 (0 : Rd d) = a := hp.1
    have h2 : dist p.2 (0 : Rd d) = b := hp.2
    rw [heq] at h1
    linarith
  obtain ⟨s, hs, H⟩ := hT.lower_offDiag ((isCompact_sphere (0 : Rd d) a).prod
    (isCompact_sphere 0 b)) hOff hθ
  refine ⟨s, hs, fun δ hδ => ?_⟩
  refine lt_of_le_of_lt (measure_mono_ae ?_) (H δ hδ)
  filter_upwards [l9b_canonical_cont_seed hd hκ hδ.1] with g hg hbad hgood
  have hA : (sphere (0 : Rd d) a).Nonempty := by
    have : Nontrivial (Rd d) := Module.nontrivial_of_finrank_pos (R := ℝ) (by
      rw [finrank_euclideanSpace_fin]; omega)
    exact NormedSpace.sphere_nonempty.2 ha.le
  have hB : (sphere (0 : Rd d) b).Nonempty := by
    have : Nontrivial (Rd d) := Module.nontrivial_of_finrank_pos (R := ℝ) (by
      rw [finrank_euclideanSpace_fin]; omega)
    exact NormedSpace.sphere_nonempty.2 (ha.trans hab).le
  have hle : s * aEps κ ξ δ ≤
      DGZ.lfppSetDist ξ (convMollify κ δ g) univ (sphere 0 a) (sphere 0 b) := by
    refine DGZ.le_lfppSetDist hA hB fun u hu v hv => ?_
    have h := hgood (u, v) ⟨hu, hv⟩
    rw [l9b_lfppX_apply hg] at h
    have hpos' := hpos δ hδ
    have := (lt_inv_mul_iff₀ hpos').1 h
    rw [mul_comm]
    exact this.le
  exact (not_lt.2 hle) hbad

/-- **Sphere-diameter upper bound** (MA6 P2, LFPP family, piecewise-`C¹` internal distances): for `θ > 0`
there is `C > 0` with `normLGFLaw{diam_{A_{1/2,2}}(∂B_1) > C 𝔞_δ} < θ` for every `δ ∈ (0,1)`.
Sign-free copy of `HigherDimLQGMetric.l9b_lfpp_diam_upper`. -/
theorem l9b_lfpp_diam_upper_seed (hd : 2 ≤ d) (hκ : HigherDimLFPPAS.IsAdmissibleSeed κ)
    (hpos : ∀ δ ∈ Ioo (0 : ℝ) 1, 0 < aEps κ ξ δ)
    (hT : TightOver (normLGFLaw d) (fun δ g => lfppX κ ξ δ g) (Ioo 0 1))
    {θ : ℝ≥0∞} (hθ : 0 < θ) :
    ∃ C : ℝ, 0 < C ∧ ∀ δ ∈ Ioo (0 : ℝ) 1, normLGFLaw d {g |
      C * aEps κ ξ δ < DGZ.lfppDiam ξ (convMollify κ δ g) (sphere 0 1) (ann 0 (1 / 2) 2)} < θ := by
  have := l9b_normLGFLaw_prob hd
  have hθ2 : 0 < θ / 2 := ENNReal.half_pos hθ.ne'
  let K : Set (Rd d) := sphere 0 1
  let V : Set (Rd d) := ann 0 (1 / 2) 2
  obtain ⟨s, hs, Hsep⟩ := hT.lower_offDiag
    ((isCompact_sphere (0 : Rd d) 1).prod compact_frontier_unit_ann)
    sphere_frontier_offDiag hθ2
  obtain ⟨b, hb, Hmod⟩ := hT.modulus (isCompact_sphere (0 : Rd d) 1) hs hθ2
  obtain ⟨N, hN⟩ := compact_connected_chain_bound
    (isCompact_sphere (0 : Rd d) 1) (isConnected_unit_sphere hd) hb
  refine ⟨(N + 1) * s, by positivity, fun δ hδ => ?_⟩
  have hV : IsOpen V := isOpen_ann _ _ _
  have hVc : IsPreconnected V := (config_isConnected_ann hd 0 (by norm_num) (by norm_num)).2
  have hKV : K ⊆ V := unit_sphere_subset_ann
  have hpos' := hpos δ hδ
  have hgood : ∀ g : DistRd d, Continuous (convMollify κ δ g) →
      (∀ p ∈ K ×ˢ frontier V, s < lfppX κ ξ δ g p) →
      (∀ u ∈ K, ∀ v ∈ K, ‖u - v‖ ≤ b → lfppX κ ξ δ g (u, v) < s) →
      DGZ.lfppDiam ξ (convMollify κ δ g) (sphere 0 1) (ann 0 (1 / 2) 2) ≤ (N + 1) * s * aEps κ ξ δ := by
    intro g hg hsep hmod
    set φ := convMollify κ δ g with hφdef
    -- short steps: internal distance at most `s 𝔞_δ`
    have hshort : ∀ x y, sharpShortStep K b x y →
        fieldDistIn ξ φ V x y ≤ ENNReal.ofReal (s * aEps κ ξ δ) := by
      intro x y hxy
      have hxV : x ∈ V := hKV hxy.1
      have hD : DGZ.lfppMetric ξ φ x y < s * aEps κ ξ δ := by
        have h := hmod x hxy.1 y hxy.2.1 (by rw [← dist_eq_norm]; exact hxy.2.2.le)
        rw [l9b_lfppX_apply hg] at h
        rw [mul_comm]
        exact (inv_mul_lt_iff₀ hpos').1 h
      have hfr : ∀ w ∈ frontier V, s * aEps κ ξ δ ≤ DGZ.lfppMetric ξ φ x w := by
        intro w hw
        have h := hsep (x, w) ⟨hxy.1, hw⟩
        rw [l9b_lfppX_apply hg] at h
        rw [mul_comm]
        exact ((lt_inv_mul_iff₀ hpos').1 h).le
      obtain ⟨hj, hle⟩ := l9b_lfppDistOn_le_of_frontier hg hV hxV hD hfr
      rw [fieldDistIn_eq_ofReal hg hj]
      exact ENNReal.ofReal_le_ofReal (hle.trans hD.le)
    have hchain : ∀ u ∈ K, ∀ v ∈ K, fieldDistIn ξ φ V u v ≤
        (N : ℝ≥0∞) * ENNReal.ofReal (s * aEps κ ξ δ) :=
      fun u hu v hv => hN u hu v hv (fieldDistIn ξ φ V) (fun x hx => fieldDistIn_self (hKV hx))
        (fieldDistIn_triangle hg) _ hshort
    refine DGZ.lfppDiam_le (by positivity) fun u hu v hv => ?_
    have hj := DGZ.pcwJoined_of_isPreconnected hV hVc (hKV hu) (hKV hv)
    have h := hchain u hu v hv
    rw [fieldDistIn_eq_ofReal hg hj, ← ENNReal.ofReal_natCast,
      ← ENNReal.ofReal_mul (Nat.cast_nonneg N)] at h
    have h' := (ENNReal.ofReal_le_ofReal_iff (by positivity)).1 h
    calc lfppDistOn ξ φ V u v ≤ N * (s * aEps κ ξ δ) := h'
      _ ≤ (N + 1) * s * aEps κ ξ δ := by nlinarith
  calc normLGFLaw d {g | (N + 1) * s * aEps κ ξ δ <
        DGZ.lfppDiam ξ (convMollify κ δ g) (sphere 0 1) (ann 0 (1 / 2) 2)}
      ≤ normLGFLaw d ({g | ¬ ∀ p ∈ K ×ˢ frontier V, s < lfppX κ ξ δ g p} ∪
          {g | ¬ ∀ u ∈ K, ∀ v ∈ K, ‖u - v‖ ≤ b → lfppX κ ξ δ g (u, v) < s}) := by
        refine measure_mono_ae ?_
        filter_upwards [l9b_canonical_cont_seed hd hκ hδ.1] with g hg hbad
        by_contra hnot
        simp only [mem_union, mem_ofPred_eq, not_or, not_not] at hnot
        exact (not_lt.2 (hgood g hg hnot.1 hnot.2)) hbad
    _ ≤ normLGFLaw d {g | ¬ ∀ p ∈ K ×ˢ frontier V, s < lfppX κ ξ δ g p} +
        normLGFLaw d {g | ¬ ∀ u ∈ K, ∀ v ∈ K, ‖u - v‖ ≤ b → lfppX κ ξ δ g (u, v) < s} :=
      measure_union_le _ _
    _ < θ / 2 + θ / 2 := ENNReal.add_lt_add (Hsep δ hδ) (Hmod δ hδ)
    _ = θ := ENNReal.add_halves θ
end Canonical

end LfppTight

end HigherDimLFPPAS.Signed
