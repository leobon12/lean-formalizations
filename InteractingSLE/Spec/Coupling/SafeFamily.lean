import InteractingSLE.Spec.Coupling.StopFamily

/-!
# The countable family of safe stops

Packet PROVE-T11-L312, Theorem 1.1 by the route of ruling R35 (`source/external/AstraIG1/ig1_formalization_proofs.pdf`
§1, (1.11)–(1.13); Specification L559–L565, node `SPEC.thm-1.1#safe-stops`). Given an announcing sequence
`T_n < T_* = ζ`, `T_n ↑ ζ` (the driving prerequisite (1.2), `IsAnnouncingSeq`), the stops
`s_{U,n} = T_n ∧ inf{t : inf_{z ∈ Ū} Im g_t(z) ≤ ·}` for `U` a finite union of rational balls with `Ū ⊆ ℍ`
(`exists_safeSeq_of_seq` with `K = Ū`) form a countable family with `s_{U,n} < ζ`, `Ū ∩ K_{s_{U,n}} = ∅`, which
exhausts avoidance (1.12): if `t < ζ` and a compact `K ⊆ ℍ` avoids `K_t`, then `K ⊆ U` and `t ≤ s_{U,n}` for some
member. This is the hypothesis `hexh` of `setIntegral_cexp_eq_cfAt_of_family`.

## Main results

* `IsAnnouncingSeq`: the announcing sequence of the lifetime (Astra (1.2); Specification L554–L557);
* `notMem_fwdHull_of_alive`: a point alive at `t < ζ` is not in the hull of the raw driving path;
* `exists_rationalBalls`: a compact set inside an open set lies in a finite union of rational balls whose closed balls
  stay inside;
* **`exists_safeFamily`**: the countable family of safe stops.
-/

set_option autoImplicit false

noncomputable section

open Set Filter MeasureTheory ProbabilityTheory Topology QuantumZipper Metric
open scoped NNReal ENNReal Classical

namespace InteractingSLE

namespace Coupling

open Ito

variable {Ω : Type*} {mΩ : MeasurableSpace Ω}

/-- **An announcing sequence of the lifetime** (Astra §1, (1.2); Specification L554–L557, node
`SPEC.thm-1.1#announcing-sequence`): stopping times `T_n` of `𝓖`, nondecreasing in `n`, with `T_n < ζ` almost surely
and, almost surely, every `t < ζ` below some `T_n` (so `T_n ↑ ζ`). -/
def IsAnnouncingSeq (𝓖 : Filtration ℝ≥0 mΩ) (P : Measure Ω) (ζ : Ω → ℝ≥0∞) (T : ℕ → Ω → ℝ≥0) :
    Prop :=
  (∀ n, IsStoppingTime 𝓖 fun ω => (T n ω : WithTop ℝ≥0)) ∧ (∀ ω, Monotone fun n => T n ω) ∧
    (∀ n, ∀ᵐ ω ∂P, (T n ω : ℝ≥0∞) < ζ ω) ∧
    ∀ᵐ ω ∂P, ∀ t : ℝ≥0, (t : ℝ≥0∞) < ζ ω → ∃ n, t ≤ T n ω

/-- **A point alive at `t < ζ` is outside the hull of the raw driving path** (the raw path is continuous on a
neighbourhood of `[0, t]`, so the forward solution extends beyond `t`). -/
theorem notMem_fwdHull_of_alive {w : ℝ≥0 → ℝ} {ζ : ℝ≥0∞}
    (hw : ContinuousOn w {t | (t : ℝ≥0∞) < ζ}) {t : ℝ≥0} (ht : (t : ℝ≥0∞) < ζ) {z : ℂ}
    (hz : 0 < z.im) (hsol : ∃ u, IsForwardSol (rpath w) z t u) : z ∉ fwdHull (rpath w) t := by
  obtain ⟨T', htT', hT'ζ⟩ := ENNReal.lt_iff_exists_nnreal_btwn.1 ht
  have htT : t < T' := by exact_mod_cast htT'
  have hwT := continuousOn_rpath hw hT'ζ
  have hc := continuous_clampDrv T'.coe_nonneg hwT
  have hsol' : ∃ u, IsForwardSol (clampDrv (rpath w) T') z t u := by
    obtain ⟨u, hu⟩ := hsol
    refine ⟨u, (isForwardSol_iff_of_eqOn (fun r hr => ?_) u).1 hu⟩
    exact (clampDrv_eqOn (W := rpath w) ⟨hr.1, hr.2.trans (by exact_mod_cast htT.le)⟩).symm
  obtain ⟨u, hu⟩ := hsol'
  have hnot := notMem_fwdHull_of_isForwardSol hc hz t.coe_nonneg hu
  have hlt : ENNReal.ofReal t < swallowTime (clampDrv (rpath w) T') z := by
    by_contra hle
    exact hnot ⟨hz, not_lt.1 hle⟩
  obtain ⟨x, ⟨T'', ⟨hT''0, v, hv⟩, rfl⟩, hxlt⟩ := lt_sSup_iff.1 hlt
  have htT'' : (t : ℝ) < T'' := (ENNReal.ofReal_lt_ofReal_iff_of_nonneg t.coe_nonneg).1 hxlt
  set T₃ : ℝ := min T'' T'
  have ht3 : (t : ℝ) < T₃ := lt_min htT'' (by exact_mod_cast htT)
  have hv3 : IsForwardSol (rpath w) z T₃ v := by
    refine (isForwardSol_iff_of_eqOn (fun r hr => ?_) v).2
      (isForwardSol_of_le hv (le_trans t.coe_nonneg ht3.le) (min_le_left _ _))
    exact (clampDrv_eqOn (W := rpath w) ⟨hr.1, hr.2.trans (min_le_right _ _)⟩).symm
  rintro ⟨-, hK⟩
  have hge : ENNReal.ofReal T₃ ≤ swallowTime (rpath w) z :=
    le_sSup ⟨T₃, ⟨le_trans t.coe_nonneg ht3.le, v, hv3⟩, rfl⟩
  have := hge.trans hK
  rw [ENNReal.ofReal_le_ofReal_iff t.coe_nonneg] at this
  linarith

/-! ### Finite unions of rational balls -/

/-- The centre `q₁ + i q₂` of a rational ball `(q₁, q₂, r)`. -/
def ratCentre (b : ℚ × ℚ × ℚ) : ℂ := ⟨(b.1 : ℝ), (b.2.1 : ℝ)⟩

/-- The open union of the balls of `F`. -/
def ballsU (F : Finset (ℚ × ℚ × ℚ)) : Set ℂ := ⋃ b ∈ F, ball (ratCentre b) (b.2.2 : ℝ)

/-- The closed union of the closed balls of `F`. -/
def ballsK (F : Finset (ℚ × ℚ × ℚ)) : Set ℂ := ⋃ b ∈ F, closedBall (ratCentre b) (b.2.2 : ℝ)

theorem isOpen_ballsU (F : Finset (ℚ × ℚ × ℚ)) : IsOpen (ballsU F) :=
  isOpen_biUnion fun _ _ => isOpen_ball

theorem isCompact_ballsK (F : Finset (ℚ × ℚ × ℚ)) : IsCompact (ballsK F) :=
  F.isCompact_biUnion fun _ _ => isCompact_closedBall _ _

theorem ballsU_subset_ballsK (F : Finset (ℚ × ℚ × ℚ)) : ballsU F ⊆ ballsK F :=
  biUnion_mono subset_rfl fun _ _ => ball_subset_closedBall

theorem closure_ballsU_subset (F : Finset (ℚ × ℚ × ℚ)) : closure (ballsU F) ⊆ ballsK F :=
  closure_minimal (ballsU_subset_ballsK F) (isCompact_ballsK F).isClosed

/-- **Rational balls**: a compact `K` inside an open `O ⊆ ℂ` lies in a finite union of rational balls whose closed
balls stay in `O`. -/
theorem exists_rationalBalls {K O : Set ℂ} (hK : IsCompact K) (hO : IsOpen O) (hKO : K ⊆ O) :
    ∃ F : Finset (ℚ × ℚ × ℚ), K ⊆ ballsU F ∧ ballsK F ⊆ O := by
  set J := {b : ℚ × ℚ × ℚ // closedBall (ratCentre b) (b.2.2 : ℝ) ⊆ O}
  have hcov : K ⊆ ⋃ b : J, ball (ratCentre b.1) (b.1.2.2 : ℝ) := by
    intro z hz
    obtain ⟨ε, hε, hεO⟩ := Metric.isOpen_iff.1 hO z (hKO hz)
    obtain ⟨q₁, hq₁⟩ := exists_rat_btwn (show z.re - ε / 8 < z.re + ε / 8 by linarith)
    obtain ⟨q₂, hq₂⟩ := exists_rat_btwn (show z.im - ε / 8 < z.im + ε / 8 by linarith)
    obtain ⟨r, hr⟩ := exists_rat_btwn (show ε / 4 < ε / 2 by linarith)
    set c : ℂ := ⟨(q₁ : ℝ), (q₂ : ℝ)⟩ with hc
    have hcz : dist c z < ε / 4 := by
      rw [Complex.dist_eq]
      calc ‖c - z‖ ≤ |(c - z).re| + |(c - z).im| := Complex.norm_le_abs_re_add_abs_im _
        _ < ε / 8 + ε / 8 := by
          simp only [Complex.sub_re, Complex.sub_im, hc]
          exact add_lt_add (abs_sub_lt_iff.2 ⟨by linarith [hq₁.2], by linarith [hq₁.1]⟩)
            (abs_sub_lt_iff.2 ⟨by linarith [hq₂.2], by linarith [hq₂.1]⟩)
        _ = ε / 4 := by ring
    have hsub : closedBall c (r : ℝ) ⊆ O := by
      intro y hy
      refine hεO ?_
      rw [mem_ball]
      calc dist y z ≤ dist y c + dist c z := dist_triangle _ _ _
        _ < ε / 2 + ε / 4 := add_lt_add_of_le_of_lt ((mem_closedBall.1 hy).trans hr.2.le) hcz
        _ < ε := by linarith
    refine mem_iUnion.2 ⟨⟨(q₁, q₂, r), hsub⟩, ?_⟩
    rw [mem_ball, dist_comm]
    exact lt_trans hcz hr.1
  obtain ⟨t, ht⟩ := hK.elim_finite_subcover (fun b : J => ball (ratCentre b.1) (b.1.2.2 : ℝ))
    (fun _ => isOpen_ball) hcov
  refine ⟨t.map (Function.Embedding.subtype _), fun z hz => ?_, ?_⟩
  · obtain ⟨b, hb, hzb⟩ := mem_iUnion₂.1 (ht hz)
    exact mem_iUnion₂.2 ⟨b.1, Finset.mem_map_of_mem _ hb, hzb⟩
  · refine iUnion₂_subset fun b hb => ?_
    obtain ⟨b', -, rfl⟩ := Finset.mem_map.1 hb
    exact b'.2

/-! ### The family -/

/-- The index set of the family: finite sets of rational balls whose closed balls lie in `ℍ`. -/
def RatBallSet : Type := {F : Finset (ℚ × ℚ × ℚ) // ballsK F ⊆ H}

instance : Countable RatBallSet := by unfold RatBallSet; infer_instance

variable {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ} {nL nR : ℕ} {κ : ℝ} {xL : Fin nL → ℝ}
  {xR : Fin nR → ℝ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ} {W : ℝ≥0 → Ω → ℝ} {VL : Fin nL → ℝ≥0 → Ω → ℝ}
  {VR : Fin nR → ℝ≥0 → Ω → ℝ} {B : ℝ≥0 → Ω → ℝ} {ζ : Ω → ℝ≥0∞}

/-- **The countable family of safe stops** (Astra §1, (1.11)–(1.13); Specification L559–L565). For an announcing
sequence `T_n` of the lifetime, there are stopping times `s_{F,n}` of the usual augmentation, indexed by the finite
unions `F` of rational balls with closures in `ℍ` and `n ∈ ℕ`, nondecreasing in `n`, with `s_{F,n} < ζ` and the closed
balls of `F` unswallowed at `s_{F,n}` almost surely, which exhaust avoidance: almost surely, for every `t < ζ` and
every compact `K ⊆ ℍ ∖ K_t` there is a member with `K ⊆ ⋃ F` and `t ≤ s_{F,n}`. -/
theorem exists_safeFamily (hE : IsIntegratedSLEEvolution κ xL xR ρL ρR P 𝓕 W VL VR B ζ)
    {T : ℕ → Ω → ℝ≥0} (hT : IsAnnouncingSeq (usualAugmentation 𝓕 P) P ζ T) :
    ∃ s : RatBallSet × ℕ → Ω → ℝ≥0,
      (∀ i, IsStoppingTime (usualAugmentation 𝓕 P) fun ω => (s i ω : WithTop ℝ≥0)) ∧
      (∀ F ω, Monotone fun n => s (F, n) ω) ∧
      (∀ i, ∀ᵐ ω ∂P, (s i ω : ℝ≥0∞) < ζ ω ∧
        Disjoint (ballsK i.1.1) (fwdHull (fun r : ℝ => W r.toNNReal ω) (s i ω))) ∧
      ∀ᵐ ω ∂P, ∀ t : ℝ≥0, (t : ℝ≥0∞) < ζ ω → ∀ K : Set ℂ, IsCompact K → K ⊆ H →
        Disjoint K (fwdHull (fun r : ℝ => W r.toNNReal ω) t) → ∃ i, K ⊆ ballsU i.1.1 ∧ t ≤ s i ω := by
  obtain ⟨hTst, hTm, hTζ, hTex⟩ := hT
  have hseq : ∀ F : RatBallSet, ∃ ρ : ℕ → Ω → ℝ≥0,
      (∀ n, IsStoppingTime (usualAugmentation 𝓕 P) fun ω => (ρ n ω : WithTop ℝ≥0)) ∧
      (∀ ω, Monotone fun n => ρ n ω) ∧
      (∀ n : ℕ, ∀ᵐ ω ∂P, ∃ δ, IsSafeAt (ballsK F.1) δ n (T n ω) (ζ ω) (W · ω) (ρ n ω)) ∧
      ∀ᵐ ω ∂P, ∀ (j : ℕ) (t : ℝ≥0), t ≤ T j ω →
        (∀ z ∈ ballsK F.1, ∃ u, IsForwardSol (rpath (W · ω)) z t u) → ∀ᶠ n in atTop, t ≤ ρ n ω := by
    intro F
    obtain ⟨m, hm, hKm⟩ := exists_pos_le_im_of_isCompact (isCompact_ballsK F.1) F.2
    obtain ⟨ρ, h1, -, h3, h4, h5⟩ := exists_safeSeq_of_seq hE (isCompact_ballsK F.1) F.2 hm hKm hTst
      hTm hTζ
    exact ⟨ρ, h1, h3, fun n => (h4 n).mono fun ω h => ⟨_, h⟩, h5⟩
  choose ρ hρst hρm hρsafe hρex using hseq
  refine ⟨fun i => ρ i.1 i.2, fun i => hρst i.1 i.2, fun F ω => hρm F ω, fun i => ?_, ?_⟩
  · filter_upwards [hρsafe i.1 i.2, hE.2.2.2.2] with ω hS hP
    obtain ⟨δ, hS⟩ := hS
    exact ⟨hS.1, Set.disjoint_left.2 fun z hz =>
      notMem_fwdHull_of_alive hP.2.2.2.1 hS.1 (i.1.2 hz) (hS.2.2.2 z hz).1⟩
  · filter_upwards [ae_all_iff.2 hρex, hTex, hE.2.2.2.2] with ω hex hTω hP
    intro t ht K hK hKH hdis
    have hwt := continuousOn_rpath hP.2.2.2.1 ht
    set O : Set ℂ := H \ fwdHull (clampDrv (rpath (W · ω)) t) t with hO_def
    have hO : IsOpen O :=
      FwdHolo.isOpen_compl_fwdHull (continuous_clampDrv t.coe_nonneg hwt) t.coe_nonneg
    have hKO : K ⊆ O := fun z hz =>
      mem_diff_fwdHull_clampDrv t.coe_nonneg hwt (hKH hz)
        (exists_isForwardSol_of_mem t.coe_nonneg ⟨hKH hz, fun h' => hdis.ne_of_mem hz h' rfl⟩)
    obtain ⟨F₀, hKF, hFO⟩ := exists_rationalBalls hK hO hKO
    set F : RatBallSet := ⟨F₀, hFO.trans sdiff_subset⟩
    have halive : ∀ z ∈ ballsK F.1, ∃ u, IsForwardSol (rpath (W · ω)) z t u := fun z hz => by
      obtain ⟨u, hu⟩ := exists_isForwardSol_of_mem t.coe_nonneg (hFO hz)
      exact ⟨u, (isForwardSol_iff_of_eqOn (clampDrv_eqOn (W := rpath (W · ω))) u).1 hu⟩
    obtain ⟨j, hj⟩ := hTω t ht
    obtain ⟨n, hn⟩ := (hex F j t hj halive).exists
    exact ⟨(F, n), hKF, hn⟩

end Coupling

end InteractingSLE
