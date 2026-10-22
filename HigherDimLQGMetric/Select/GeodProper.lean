import HigherDimLQGMetric.Select.GeodCompact
import Mathlib.Order.Filter.Finite

/-!
# Proper projection of bounded geodesic relations

Packet M3a, MA1 A10. A convergent sequence of metrics and bounded constant-speed
geodesics has a convergent path subsequence. The uniform modulus follows from local
uniform metric convergence on a compact ball and the Euclidean topology of the limit.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Filter Topology unitInterval

namespace HigherDimLQGMetric

open HigherDimLFPP (Rd)

variable {d : ℕ}

private theorem geodSeq_equicontinuous (x y : Rd d) (n : ℕ)
    (Ds : ℕ → ContMetric d) (D : ContMetric d)
    (hDs : Tendsto Ds atTop (𝓝 D))
    (η : ℕ → C(unitInterval, Rd d))
    (hη : ∀ j, ((Ds j).1, η j) ∈ geodBoundRel x y n) :
    Equicontinuous fun j => (η j : unitInterval → Rd d) := by
  intro s
  rw [Metric.equicontinuousAt_iff_right]
  intro ε hε
  let K : Set (Rd d) := Metric.closedBall (0 : Rd d) n
  have hK : IsCompact K := isCompact_closedBall (0 : Rd d) n
  have hKD : IsCompact (D.pt '' K) := D.isCompact_image_pt hK
  have hu : UniformContinuousOn D.unpt (D.pt '' K) :=
    hKD.uniformContinuousOn_of_continuous D.continuous_unpt.continuousOn
  obtain ⟨μ, hμ, hμu⟩ := Metric.uniformContinuousOn_iff.1 hu ε hε
  let ρ : ℝ := min 1 (μ / 2)
  have hρ : 0 < ρ := lt_min zero_lt_one (half_pos hμ)
  have hρμ : ρ ≤ μ / 2 := min_le_right _ _
  have hρ1 : ρ ≤ 1 := min_le_left _ _
  have hloc := ContMetric.tendsto_iff_tendstoLocallyUniformly.mp hDs
  have huni := (tendstoLocallyUniformly_iff_forall_isCompact.mp hloc)
    (K ×ˢ K) (hK.prod hK)
  have hclose : ∀ᶠ j in atTop,
      ∀ p ∈ K ×ˢ K, dist (D.1 p) ((Ds j).1 p) < ρ :=
    (Metric.tendstoUniformlyOn_iff.mp huni) ρ hρ
  obtain ⟨N, hN⟩ := eventually_atTop.mp hclose
  let a : ℝ := D.1 (x, y) + 1
  have ha : 0 < a := by dsimp [a]; linarith [D.nonneg x y]
  have hμa : 0 < μ / (2 * a) := div_pos hμ (by positivity)
  have hfinite : ∀ᶠ t in 𝓝 s,
      ∀ j ∈ Finset.range N, dist ((η j) s) ((η j) t) < ε := by
    apply (Finset.range N).eventually_all.mpr
    intro j hj
    have hcont : ContinuousAt (fun t : unitInterval => dist ((η j) s) ((η j) t)) s :=
      continuousAt_const.dist ((η j).continuous.continuousAt)
    have hz : dist ((η j) s) ((η j) s) = 0 := dist_self _
    have he := hcont.tendsto
    rw [hz] at he
    exact he (gt_mem_nhds hε)
  filter_upwards [hfinite, Metric.ball_mem_nhds s hμa] with t hfin ht j
  by_cases hj : j < N
  · exact hfin j (Finset.mem_range.mpr hj)
  · have hjN : N ≤ j := Nat.le_of_not_gt hj
    have hC := hN j hjN
    have hηj := hη j
    change IsConstSpeedGeodFn (Ds j).1 x y (η j) ∧
      ∀ u, ‖(η j) u‖ ≤ n at hηj
    have hs : (η j) s ∈ K := by
      simpa only [K, Metric.mem_closedBall, dist_zero_right] using hηj.2 s
    have ht' : (η j) t ∈ K := by
      simpa only [K, Metric.mem_closedBall, dist_zero_right] using hηj.2 t
    have hx : x ∈ K := by
      rw [← hηj.1.1]
      simpa only [K, Metric.mem_closedBall, dist_zero_right] using hηj.2 0
    have hy : y ∈ K := by
      rw [← hηj.1.2.1]
      simpa only [K, Metric.mem_closedBall, dist_zero_right] using hηj.2 1
    have hxy := hC (x, y) ⟨hx, hy⟩
    have hst := hC ((η j) s, (η j) t) ⟨hs, ht'⟩
    have hbound : (Ds j).1 (x, y) < a := by
      rw [Real.dist_eq] at hxy
      have habs := (abs_sub_lt_iff.mp hxy).2
      dsimp [a]
      linarith
    have hsmall : dist (D.pt ((η j) s)) (D.pt ((η j) t)) < μ := by
      rw [D.dist_pt]
      have hdiff : D.1 ((η j) s, (η j) t) < (Ds j).1 ((η j) s, (η j) t) + ρ := by
        rw [Real.dist_eq] at hst
        linarith [(abs_sub_lt_iff.mp hst).1]
      have htime : dist s t < μ / (2 * a) := by rwa [Metric.mem_ball, dist_comm] at ht
      have hmul : dist s t * a < μ / 2 := by
        have := (lt_div_iff₀ (by positivity : (0 : ℝ) < 2 * a)).mp htime
        nlinarith
      have hstep : (Ds j).1 ((η j) s, (η j) t) ≤ dist s t * a := by
        rw [hηj.1.2.2 s t, ← Real.dist_eq, ← Subtype.dist_eq]
        exact mul_le_mul_of_nonneg_left hbound.le (dist_nonneg)
      linarith
    have hsD : D.pt ((η j) s) ∈ D.pt '' K := ⟨_, hs, rfl⟩
    have htD : D.pt ((η j) t) ∈ D.pt '' K := ⟨_, ht', rfl⟩
    simpa only [D.unpt_pt] using hμu _ hsD _ htD hsmall


/-- Sequential properness: bounded geodesics for converging continuous metrics have a
convergent subsequence, and its limit is a geodesic of the limit metric. -/
theorem geodBoundRel_tendsto_subseq (x y : Rd d) (n : ℕ)
    (Ds : ℕ → ContMetric d) (D : ContMetric d)
    (hDs : Tendsto Ds atTop (𝓝 D))
    (η : ℕ → C(unitInterval, Rd d))
    (hη : ∀ j, ((Ds j).1, η j) ∈ geodBoundRel x y n) :
    ∃ γ : C(unitInterval, Rd d), ∃ φ : ℕ → ℕ,
      StrictMono φ ∧ Tendsto (η ∘ φ) atTop (𝓝 γ) ∧
        (D.1, γ) ∈ geodBoundRel x y n := by
  let A : Set (unitInterval → Rd d) := range fun j => (η j : unitInterval → Rd d)
  let T : Set (unitInterval → Rd d) := closure A
  have hAeq : A.Equicontinuous :=
    equicontinuous_iff_range.mp (geodSeq_equicontinuous x y n Ds D hDs η hη)
  have hTeq : T.Equicontinuous := hAeq.closure
  let K : Set (Rd d) := Metric.closedBall (0 : Rd d) n
  have hB : IsCompact (Set.pi univ fun _ : unitInterval => K) :=
    isCompact_univ_pi fun _ => isCompact_closedBall (0 : Rd d) n
  have hAsub : A ⊆ Set.pi univ fun _ : unitInterval => K := by
    rintro f ⟨j, rfl⟩ t _
    have hj := hη j
    change IsConstSpeedGeodFn (Ds j).1 x y (η j) ∧ ∀ u, ‖(η j) u‖ ≤ n at hj
    simpa only [K, Metric.mem_closedBall, dist_zero_right] using hj.2 t
  have hTsub : T ⊆ Set.pi univ fun _ : unitInterval => K :=
    closure_minimal hAsub hB.isClosed
  have hTc : IsCompact T := hB.of_isClosed_subset isClosed_closure hTsub
  let S : Set C(unitInterval, Rd d) := {γ | γ.toFun ∈ T}
  have hcont : ∀ f ∈ T, Continuous f := by
    intro f hf
    exact hTeq.continuous ⟨f, hf⟩
  have himg : ContinuousMap.toFun '' S = T := by
    ext f
    constructor
    · rintro ⟨γ, hγ, rfl⟩
      exact hγ
    · intro hf
      refine ⟨⟨f, hcont f hf⟩, ?_, rfl⟩
      exact hf
  have hSeq : Equicontinuous ((↑) : S → unitInterval → Rd d) := by
    convert hTeq.comp (fun γ : S => (⟨γ.1.toFun, γ.2⟩ : T)) using 1
    ext γ t
    rfl
  have hSc : IsCompact S := ArzelaAscoli.isCompact_of_equicontinuous S
    (himg ▸ hTc) hSeq
  have hηS : ∀ j, η j ∈ S := by
    intro j
    exact subset_closure ⟨j, rfl⟩
  obtain ⟨γ, hγ, φ, hφ, hlim⟩ := hSc.tendsto_subseq hηS
  have hDφ : Tendsto (fun j => (Ds (φ j)).1) atTop (𝓝 D.1) :=
    (continuous_subtype_val.tendsto D).comp (hDs.comp hφ.tendsto_atTop)
  have hpair : Tendsto (fun j => ((Ds (φ j)).1, η (φ j))) atTop (𝓝 (D.1, γ)) :=
    hDφ.prodMk_nhds hlim
  have hγrel : (D.1, γ) ∈ geodBoundRel x y n :=
    (isClosed_geodBoundRel x y n).mem_of_tendsto hpair
      (Eventually.of_forall fun j => hη (φ j))
  exact ⟨γ, φ, hφ, hlim, hγrel⟩


/-- Closed projection along a bounded geodesic relation. The base may contain
extra parameters (used for lexicographic comparisons of two paths). -/
theorem isClosed_geodProjection {X : Type*} [TopologicalSpace X]
    [SequentialSpace X] [FirstCountableTopology X]
    (x y : Rd d) (n : ℕ) (M : X → ContMetric d) (hM : Continuous M)
    {F : Set (X × C(unitInterval, Rd d))} (hF : IsClosed F)
    (hsub : ∀ p ∈ F, ((M p.1).1, p.2) ∈ geodBoundRel x y n) :
    IsClosed (Prod.fst '' F) := by
  rw [← isSeqClosed_iff_isClosed]
  intro v z hv hlim
  choose p hp heq using fun j => hv j
  let η : ℕ → C(unitInterval, Rd d) := fun j => (p j).2
  have hηF : ∀ j, (v j, η j) ∈ F := by
    intro j
    change (v j, (p j).2) ∈ F
    rw [← heq j]
    exact hp j
  have hMlim : Tendsto (fun j => M (v j)) atTop (𝓝 (M z)) := hM.continuousAt.tendsto.comp hlim
  obtain ⟨γ, φ, hφ, hγlim, -⟩ :=
    geodBoundRel_tendsto_subseq x y n (fun j => M (v j)) (M z) hMlim η
      (fun j => hsub _ (hηF j))
  have hvlim : Tendsto (v ∘ φ) atTop (𝓝 z) := hlim.comp hφ.tendsto_atTop
  have hpair : Tendsto (fun j => (v (φ j), η (φ j))) atTop (𝓝 (z, γ)) :=
    hvlim.prodMk_nhds hγlim
  have hlast : (z, γ) ∈ F := hF.mem_of_tendsto hpair
    (Eventually.of_forall fun j => hηF (φ j))
  exact ⟨(z, γ), hlast, rfl⟩

end HigherDimLQGMetric
