import InteractingSLE.GFF.LocalSets.Prop38Moment
import InteractingSLE.GFF.LocalSets.Prop39
import InteractingSLE.GFF.LocalSets.BoundaryVanishing
import InteractingSLE.Foundations.Topology.SimplyConnected

/-!
# Proposition 3.8: geometry of the complement of `A₂`

Specification §3.2, proof of Proposition 3.8 (p. 60, transcription
`source/spec/p049-096.md#prop-3.8-proof`): "These components are simply connected: `A₂` is
connected and includes the ambient boundary." Packet PROVE-LS-C.

* `isSimplyConnected_connectedComponentIn_compl` : if every component of `S ∪ {Im ≤ 0}` is
  unbounded (e.g. `S ∪ ℝ` connected, `not_isBounded_of_isPreconnected_union_real`), every component
  of `ℍ ∖ S` is simply connected (via the planar criterion `isSimplyConnected_of_forall_not_isBounded`);
* `zeroGFFTestCov_sub_le_of_component` : the Koebe variance bound of Proposition 3.3's proof
  (`GFF.zeroGFFTestCov_sub_le_of_dist`) on the component of `ℍ ∖ S` containing the bump centre,
  transported to `ℍ ∖ S` by the component decomposition of the Green covariance;
* `compDist` and `measurable_compDist` : the distance `d(ω, y)` from `y` to the complement of
  `ℍ ∖ A(ω)` (through the relative closure), jointly measurable.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Filter Set Topology TopologicalSpace Metric EMetric
open scoped ENNReal

namespace InteractingSLE
namespace LocalSets

open QuantumZipper LQGMetric
open QuantumZipper.CA.Koebe (koebeCovConst koebeDistExp koebeCovConst_pos koebeDistExp_pos)

/-! ### Simple connectivity of the components -/

/-- The closed set `S ∪ {Im ≤ 0}` that the components of `ℍ ∖ S` avoid. -/
def lowerUnion (S : Set ℂ) : Set ℂ := S ∪ {w : ℂ | w.im ≤ 0}

lemma compl_H_diff_eq (S : Set ℂ) : (H \ S)ᶜ = lowerUnion S := by
  ext z
  simp only [lowerUnion, mem_compl_iff, Set.mem_sdiff, mem_union, mem_ofPred_eq, not_and,
    not_not]
  constructor
  · intro h
    by_cases hz : z ∈ H
    · exact Or.inl (h hz)
    · right; simpa [H] using hz
  · rintro (h | h) hz
    · exact h
    · exact absurd hz (by simp [H]; linarith)

/-- If every component of `S ∪ {Im ≤ 0}` is unbounded, every component of `ℍ ∖ S` is simply
connected. -/
theorem isSimplyConnected_connectedComponentIn_compl {S : Set ℂ} (hS : IsOpen (H \ S))
    (hunb : ∀ z ∈ lowerUnion S, ¬ Bornology.IsBounded (connectedComponentIn (lowerUnion S) z))
    {y : ℂ} (hy : y ∈ H \ S) : IsSimplyConnected (connectedComponentIn (H \ S) y) := by
  set U := connectedComponentIn (H \ S) y with hUdef
  have hUo : IsOpen U := hS.connectedComponentIn
  have hUc : IsConnected U := isConnected_connectedComponentIn_iff.2 hy
  have hUS : U ⊆ H \ S := connectedComponentIn_subset _ _
  have hFU : lowerUnion S ⊆ Uᶜ := by
    rw [← compl_H_diff_eq]; exact compl_subset_compl.2 hUS
  refine isSimplyConnected_of_forall_not_isBounded hUo hUc fun a ha => ?_
  -- a point `b` of `S ∪ {Im ≤ 0}` in the component of `a`
  obtain ⟨b, hbF, hbK⟩ : ∃ b ∈ lowerUnion S, b ∈ connectedComponentIn Uᶜ a := by
    by_cases haF : a ∈ lowerUnion S
    · exact ⟨a, haF, mem_connectedComponentIn ha⟩
    · have haHS : a ∈ H \ S := by
        by_contra h; exact haF (by rw [← compl_H_diff_eq]; exact h)
      set U' := connectedComponentIn (H \ S) a
      have hU'o : IsOpen U' := hS.connectedComponentIn
      have haU' : a ∈ U' := mem_connectedComponentIn haHS
      have hdisj : Disjoint U U' := by
        rw [Set.disjoint_left]
        intro w hwU hwU'
        have e1 : U = connectedComponentIn (H \ S) w := connectedComponentIn_eq hwU
        have e2 : U' = connectedComponentIn (H \ S) w := connectedComponentIn_eq hwU'
        exact ha (by rw [e1, ← e2]; exact haU')
      have hU'ne : U' ≠ univ := fun h => by
        have : (-Complex.I : ℂ) ∈ U' := h ▸ mem_univ _
        have h1 : (0 : ℝ) < (-Complex.I).im := (connectedComponentIn_subset _ _ this).1
        simp at h1; linarith
      obtain ⟨b, hb⟩ := nonempty_frontier_iff.2 ⟨⟨a, haU'⟩, hU'ne⟩
      have hbU' : b ∉ U' := fun h => by
        rw [frontier, hU'o.interior_eq] at hb; exact hb.2 h
      have hbF : b ∈ lowerUnion S := by
        rw [← compl_H_diff_eq]
        intro hbHS
        have hnb : connectedComponentIn (H \ S) b ∈ 𝓝 b :=
          hS.connectedComponentIn.mem_nhds (mem_connectedComponentIn hbHS)
        obtain ⟨w, hwb, hwU'⟩ := mem_closure_iff_nhds.1 (frontier_subset_closure hb) _ hnb
        have e1 : connectedComponentIn (H \ S) b = connectedComponentIn (H \ S) w :=
          connectedComponentIn_eq hwb
        have e2 : U' = connectedComponentIn (H \ S) w := connectedComponentIn_eq hwU'
        exact hbU' (by rw [e2, ← e1]; exact mem_connectedComponentIn hbHS)
      have hcl : closure U' ⊆ Uᶜ := fun z hz hzU =>
        Set.disjoint_left.1 (hdisj.closure_right hUo) hzU hz
      have hsub := (isPreconnected_connectedComponentIn.closure).subset_connectedComponentIn
        (subset_closure haU') hcl
      exact ⟨b, hbF, hsub (frontier_subset_closure hb)⟩
  have hsub : connectedComponentIn (lowerUnion S) b ⊆ connectedComponentIn Uᶜ a := by
    rw [connectedComponentIn_eq hbK]
    exact (isPreconnected_connectedComponentIn.subset_connectedComponentIn
      (mem_connectedComponentIn hbF) ((connectedComponentIn_subset _ _).trans hFU))
  exact fun hbd => hunb b hbF (hbd.subset hsub)

/-- If `S ∪ ℝ` is preconnected, every component of `S ∪ {Im ≤ 0}` is unbounded. -/
theorem not_isBounded_of_isPreconnected_union_real {S : Set ℂ}
    (hS : IsPreconnected (S ∪ {w : ℂ | w.im = 0})) :
    ∀ z ∈ lowerUnion S, ¬ Bornology.IsBounded (connectedComponentIn (lowerUnion S) z) := by
  have hpre : IsPreconnected (lowerUnion S) := by
    have e : lowerUnion S = (S ∪ {w : ℂ | w.im = 0}) ∪ {w : ℂ | w.im ≤ 0} := by
      ext w; simp only [lowerUnion, mem_union, mem_ofPred_eq]
      constructor
      · rintro (h | h)
        · exact Or.inl (Or.inl h)
        · exact Or.inr h
      · rintro ((h | h) | h)
        · exact Or.inl h
        · exact Or.inr h.le
        · exact Or.inr h
    rw [e]
    exact hS.union (0 : ℂ) (Or.inr (by simp)) (by simp) isPreconnected_lowerHalf
  intro z hz hb
  rw [hpre.connectedComponentIn hz] at hb
  exact not_isBounded_lowerHalf (hb.subset subset_union_right)

/-! ### The distance to the complement of a component -/

/-- The distance from `y ∈ ℍ ∖ S` to the complement of its component equals the distance to the
complement of `ℍ ∖ S`. -/
lemma infDist_compl_connectedComponentIn {V : Set ℂ} (hV : IsOpen V) (hVne : V ≠ univ) {y : ℂ}
    (hy : y ∈ V) : infDist y (connectedComponentIn V y)ᶜ = infDist y Vᶜ := by
  have hVc : (Vᶜ).Nonempty := nonempty_compl.2 hVne
  refine le_antisymm (infDist_le_infDist_of_subset
    (compl_subset_compl.2 (connectedComponentIn_subset _ _)) hVc) ?_
  have hball : ball y (infDist y Vᶜ) ⊆ connectedComponentIn V y := by
    refine (isPreconnected_ball).subset_connectedComponentIn
      (mem_ball_self ((IsClosed.notMem_iff_infDist_pos hV.isClosed_compl hVc).1 (fun h => h hy)))
      fun w hw => ?_
    by_contra hwV
    have := infDist_le_dist_of_mem (x := y) (show w ∈ Vᶜ from hwV)
    rw [mem_ball, dist_comm] at hw
    linarith
  refine (le_infDist (hVc.mono (compl_subset_compl.2 (connectedComponentIn_subset _ _)))).2
    fun w hw => ?_
  by_contra hlt
  push Not at hlt
  exact hw (hball (by rw [mem_ball, dist_comm]; exact hlt))

lemma ball_infDist_subset_connectedComponentIn {V : Set ℂ} (hV : IsOpen V) (hVne : V ≠ univ)
    {y : ℂ} (hy : y ∈ V) : ball y (infDist y Vᶜ) ⊆ connectedComponentIn V y := by
  have hVc : (Vᶜ).Nonempty := nonempty_compl.2 hVne
  refine (isPreconnected_ball).subset_connectedComponentIn
    (mem_ball_self ((IsClosed.notMem_iff_infDist_pos hV.isClosed_compl hVc).1 (fun h => h hy)))
    fun w hw => ?_
  by_contra hwV
  have := infDist_le_dist_of_mem (x := y) (show w ∈ Vᶜ from hwV)
  rw [mem_ball, dist_comm] at hw
  linarith

lemma H_diff_ne_univ (S : Set ℂ) : H \ S ≠ univ := fun h => by
  have h1 : (0 : ℝ) < (-Complex.I).im := (h ▸ mem_univ (-Complex.I) : -Complex.I ∈ H \ S).1
  simp at h1; linarith

/-- **The Koebe variance bound on a component** (proof of Proposition 3.3, applied in the
component of `ℍ ∖ S` containing `y`). If every component of `S ∪ {Im ≤ 0}` is unbounded,
`B(y, R) ⊆ U`, `d = dist(y, ∂(ℍ ∖ S))`, `t = (2d/(cR))^(1/C₂) ≤ 1/4`, and `ψ ≥ 0` is supported in
`B(y, t d)`, then `σ²_{ℍ∖S}(ψ) − σ²_{(ℍ∖S)∩U}(ψ) ≤ 4 t (∫ ψ)²`. -/
theorem zeroGFFTestCov_sub_le_of_component {S U : Set ℂ} (hS : IsOpen (H \ S)) (hU : IsOpen U)
    (hunb : ∀ z ∈ lowerUnion S, ¬ Bornology.IsBounded (connectedComponentIn (lowerUnion S) z))
    {y : ℂ} (hy : y ∈ H \ S) {R : ℝ} (hR : 0 < R) (hRU : ball y R ⊆ U)
    (ht : (2 * infDist y (H \ S)ᶜ / (koebeCovConst * R)) ^ koebeDistExp⁻¹ ≤ 1 / 4)
    (ψ : TestOn upperHalfPlaneOpens) (hψ0 : ∀ z, 0 ≤ ψ z)
    (hψs : ∀ z, ψ z ≠ 0 → dist z y <
      (2 * infDist y (H \ S)ᶜ / (koebeCovConst * R)) ^ koebeDistExp⁻¹ * infDist y (H \ S)ᶜ) :
    zeroGFFTestCov (H \ S) ψ ψ - zeroGFFTestCov ((H \ S) ∩ U) ψ ψ ≤
      4 * (2 * infDist y (H \ S)ᶜ / (koebeCovConst * R)) ^ koebeDistExp⁻¹ * (∫ z, ψ z) ^ 2 := by
  set O := connectedComponentIn (H \ S) y with hOdef
  have hOo : IsOpen O := hS.connectedComponentIn
  have hOS : O ⊆ H \ S := connectedComponentIn_subset _ _
  have hOH : O ⊆ H := hOS.trans sdiff_subset
  have hOne : O ≠ univ := fun h => H_diff_ne_univ S (eq_univ_of_univ_subset (h ▸ hOS))
  have hd : infDist y Oᶜ = infDist y (H \ S)ᶜ :=
    infDist_compl_connectedComponentIn hS (H_diff_ne_univ S) hy
  set d := infDist y (H \ S)ᶜ with hddef
  set t := (2 * d / (koebeCovConst * R)) ^ koebeDistExp⁻¹ with htdef
  have hdR : d < R := by
    have := GFF.infDist_lt_of_koebeScale_le (D := O) (x := y) hR (by
      unfold GFF.koebeScale; rw [hd]; exact ht)
    rwa [hd] at this
  have hd0 : 0 < d := (IsClosed.notMem_iff_infDist_pos hS.isClosed_compl
    (nonempty_compl.2 (H_diff_ne_univ S))).1 (fun h => h hy)
  have ht1 : t ≤ 1 / 4 := ht
  have htd : t * d < d := by nlinarith
  have hsupp : tsupport ψ ⊆ closedBall y (t * d) := by
    refine closure_minimal (fun z hz => ?_) isClosed_closedBall
    exact mem_closedBall.2 (hψs z hz).le
  have hcl : closedBall y (t * d) ⊆ O ∩ U := by
    intro z hz
    have hz' : dist z y < d := lt_of_le_of_lt (mem_closedBall.1 hz) htd
    refine ⟨ball_infDist_subset_connectedComponentIn hS (H_diff_ne_univ S) hy hz', hRU ?_⟩
    rw [mem_ball]; linarith
  have hsO : tsupport ψ ⊆ O := hsupp.trans (hcl.trans inter_subset_left)
  have hsOU : tsupport ψ ⊆ O ∩ U := hsupp.trans hcl
  let O' : Opens ℂ := ⟨O, hOo⟩
  let V' : Opens ℂ := ⟨O ∩ U, hOo.inter hU⟩
  let ρ : TestOn O' := ⟨ψ, ψ.contDiff, ψ.hasCompactSupport, hsO⟩
  let ρV : TestOn V' := ⟨ψ, ψ.contDiff, ψ.hasCompactSupport, hsOU⟩
  have hVO : V' ≤ O' := fun z hz => hz.1
  have hmain := GFF.zeroGFFTestCov_sub_le_of_dist (D := O') (V := V') hVO
    (isConnected_connectedComponentIn_iff.2 hy)
    (isSimplyConnected_connectedComponentIn_compl hS hunb hy) hOne
    (mem_connectedComponentIn hy) hR (fun z hzO hzy => ⟨hzO, hRU (mem_ball.2 hzy)⟩)
    (by show (2 * infDist y Oᶜ / (koebeCovConst * R)) ^ koebeDistExp⁻¹ ≤ 1 / 4
        rw [hd]; exact ht)
    ρ ρV rfl hψ0 (fun z hz => by
      show dist z y < (2 * infDist y Oᶜ / (koebeCovConst * R)) ^ koebeDistExp⁻¹ * infDist y Oᶜ
      rw [hd]; exact hψs z hz)
  change zeroGFFTestCov O ψ ψ - zeroGFFTestCov (O ∩ U) ψ ψ ≤
    4 * (2 * infDist y Oᶜ / (koebeCovConst * R)) ^ koebeDistExp⁻¹ * (∫ z, ψ z) ^ 2 at hmain
  rw [hd] at hmain
  have hCc : ∀ z ∈ O, connectedComponentIn (H \ S) z ⊆ O := fun z hz => by
    rw [hOdef, connectedComponentIn_eq hz]
  have e1 := zeroGFFTestCov_eq_of_isClopen hS sdiff_subset hOo hOS
    (isOpen_diff_of_forall_connectedComponentIn_subset hS hCc) ψ hsO
  have e2 := zeroGFFTestCov_mono (hOo.inter hU) (hS.inter hU) (inter_subset_inter_left _ hOS)
    (inter_subset_left.trans sdiff_subset) ψ
  rw [e1]
  linarith

/-! ### The distance to the complement of `ℍ ∖ A`, as a random field -/

/-- `d(S, y) = dist(y, ∂(ℍ ∖ S))`, through the relative closure of `S`. -/
def compDist (S : Set ℂ) (y : ℂ) : ℝ := infDist y (H \ relClosureH S)ᶜ

lemma compl_H_diff_relClosureH (S : Set ℂ) :
    (H \ relClosureH S)ᶜ = closure (S ∩ H) ∪ Hᶜ := by
  ext z
  by_cases hz : z ∈ H
  · simp [relClosureH, hz]
  · simp [hz]

lemma compDist_eq (S : Set ℂ) (y : ℂ) :
    compDist S y = (infEDist y (S ∩ H) ⊓ infEDist y Hᶜ).toReal := by
  rw [compDist, compl_H_diff_relClosureH, Metric.infDist, infEDist_union, infEDist_closure]

lemma continuous_compDist (S : Set ℂ) : Continuous (compDist S) := continuous_infDist_pt _

lemma measurable_compDist_left {Ω : Type*} [MeasurableSpace Ω] {A : Ω → Set ℂ}
    (hA : Measurable[_, hittingSigma] A) (y : ℂ) : Measurable fun ω => compDist (A ω) y := by
  have h1 : Measurable fun ω => infEDist y (A ω ∩ H) := (measurable_infEDist_inter_H y).comp hA
  have h2 : Measurable fun ω => min (infEDist y (A ω ∩ H)) (infEDist y Hᶜ) :=
    h1.min measurable_const
  have e : (fun ω => compDist (A ω) y) =
      fun ω => (min (infEDist y (A ω ∩ H)) (infEDist y Hᶜ)).toReal := by
    funext ω; rw [compDist_eq]
  rw [e]
  exact h2.ennreal_toReal

/-- The random distance `(ω, y) ↦ d(A ω, y)` is jointly measurable. -/
theorem measurable_compDist {Ω : Type*} [MeasurableSpace Ω] {A : Ω → Set ℂ}
    (hA : Measurable[_, hittingSigma] A) : Measurable fun p : Ω × ℂ => compDist (A p.1) p.2 := by
  have h1 : Measurable (Function.uncurry fun (y : ℂ) (ω : Ω) => compDist (A ω) y) :=
    measurable_uncurry_of_continuous_of_measurable (fun ω => continuous_compDist (A ω))
      (measurable_compDist_left hA)
  have e : (fun p : Ω × ℂ => compDist (A p.1) p.2) =
      (Function.uncurry fun (y : ℂ) (ω : Ω) => compDist (A ω) y) ∘ Prod.swap := by
    funext p; rfl
  rw [e]
  exact h1.comp measurable_swap

end LocalSets
end InteractingSLE
