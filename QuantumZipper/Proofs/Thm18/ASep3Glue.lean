import QuantumZipper.Proofs.Zipper.GenUCOpen

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# ASEP3 (step 14): gluing box-wise continuous modifications

The Kolmogorov step `GenUC.exists_contMod_gen` gives a continuous modification on one compact
rational box (of side `≤ 1`, as the radius reparametrizations of ASep3Inner need). The scale joint witness needs one modification on an open parameter set (all
centres in `ℍ̄`, all radii, all scales). `ae_glue_modification`: if every rational box inside an
open `U ⊆ ℝⁿ` carries a modification of `Z` continuous on the box, then there is one
modification of `Z` on `U`, almost surely continuous on `U` (two box modifications agree a.s. on
a countable dense subset of the intersection, hence on the intersection; the glued function
agrees near each point with the modification of a box containing a neighbourhood of it).
Own elementary argument (standard).
-/

noncomputable section

open MeasureTheory Filter Set Metric
open scoped Topology

namespace QuantumZipper
namespace ASep

open GenUC

/-- A rational box with an open neighbourhood of `p` inside it, inside an open set. -/
theorem exists_ratBox_nhds {n : ℕ} {U : Set (Fin n → ℝ)} (hU : IsOpen U) {p : Fin n → ℝ}
    (hp : p ∈ U) : ∃ a b : Fin n → ℚ, ratBox a b ⊆ U ∧ ratBox a b ∈ 𝓝 p ∧
      ∀ i, (b i : ℝ) - a i ≤ 1 := by
  obtain ⟨e₀, he₀, hball₀⟩ := Metric.isOpen_iff.1 hU p hp
  set e := min e₀ 1 with he_def
  have he : 0 < e := lt_min he₀ one_pos
  have hball : ball p e ⊆ U := (ball_subset_ball (min_le_left _ _)).trans hball₀
  have hlo : ∀ i, ∃ q : ℚ, p i - e / 2 < q ∧ (q : ℝ) < p i := fun i =>
    exists_rat_btwn (by linarith)
  have hhi : ∀ i, ∃ q : ℚ, p i < q ∧ (q : ℝ) < p i + e / 2 := fun i =>
    exists_rat_btwn (by linarith)
  choose a ha using hlo
  choose b hb using hhi
  refine ⟨a, b, fun q hq => hball ?_, ?_, fun i => ?_⟩
  · rw [mem_ball, dist_pi_lt_iff he]
    intro i
    have h := hq i (mem_univ i)
    rw [Real.dist_eq, abs_lt]
    constructor <;> linarith [(ha i).1, (hb i).2, h.1, h.2]
  · refine Filter.mem_of_superset ((isOpen_set_pi finite_univ fun i _ => isOpen_Ioo).mem_nhds
      (fun i _ => ⟨(ha i).2, (hb i).1⟩)) fun q hq i hi => ?_
    exact Ioo_subset_Icc_self (hq i hi)
  · have := min_le_right e₀ 1
    linarith [(ha i).1, (hb i).2]

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}

/-- **Gluing box-wise continuous modifications.** -/
theorem ae_glue_modification {n : ℕ} {U : Set (Fin n → ℝ)} (hU : IsOpen U)
    {Z : (Fin n → ℝ) → Ω → ℝ}
    (hloc : ∀ a b : Fin n → ℚ, ratBox a b ⊆ U → (∀ i, (b i : ℝ) - a i ≤ 1) →
      ∃ Y : (Fin n → ℝ) → Ω → ℝ,
      (∀ ω, ContinuousOn (fun p => Y p ω) (ratBox a b)) ∧
        ∀ p ∈ ratBox a b, (fun ω => Y p ω) =ᵐ[P] Z p) :
    ∃ Y : (Fin n → ℝ) → Ω → ℝ, (∀ᵐ ω ∂P, ContinuousOn (fun p => Y p ω) U) ∧
      ∀ p ∈ U, (fun ω => Y p ω) =ᵐ[P] Z p := by
  classical
  choose Yb hYc hYe using hloc
  -- two box modifications agree on the intersection
  have hagree : ∀ abab : ((Fin n → ℚ) × (Fin n → ℚ)) × ((Fin n → ℚ) × (Fin n → ℚ)),
      ∀ᵐ ω ∂P, ∀ (h : ratBox abab.1.1 abab.1.2 ⊆ U) (hs : ∀ i, (abab.1.2 i : ℝ) - abab.1.1 i ≤ 1)
        (h' : ratBox abab.2.1 abab.2.2 ⊆ U) (hs' : ∀ i, (abab.2.2 i : ℝ) - abab.2.1 i ≤ 1),
        ∀ q ∈ ratBox abab.1.1 abab.1.2 ∩ ratBox abab.2.1 abab.2.2,
          Yb _ _ h hs q ω = Yb _ _ h' hs' q ω := by
    rintro ⟨⟨a, b⟩, ⟨a', b'⟩⟩
    by_cases h : ratBox a b ⊆ U ∧ ∀ i, (b i : ℝ) - a i ≤ 1
    · by_cases h' : ratBox a' b' ⊆ U ∧ ∀ i, (b' i : ℝ) - a' i ≤ 1
      · obtain ⟨h, hs⟩ := h
        obtain ⟨h', hs'⟩ := h'
        obtain ⟨D, hDc, hDS, hSD⟩ :=
          TopologicalSpace.exists_countable_dense_subset (ratBox a b ∩ ratBox a' b')
        have hD : ∀ᵐ ω ∂P, ∀ q ∈ D, Yb a b h hs q ω = Yb a' b' h' hs' q ω := by
          refine (ae_ball_iff hDc).2 fun q hq => ?_
          filter_upwards [hYe a b h hs q (hDS hq).1, hYe a' b' h' hs' q (hDS hq).2] with ω h1 h2
          rw [h1, h2]
        filter_upwards [hD] with ω hω _ _ _ _
        exact EqOn.of_subset_closure hω ((hYc a b h hs ω).mono inter_subset_left)
          ((hYc a' b' h' hs' ω).mono inter_subset_right) hDS hSD
      · exact ae_of_all _ fun ω _ _ h'' hs'' => absurd ⟨h'', hs''⟩ h'
    · exact ae_of_all _ fun ω h'' hs'' => absurd ⟨h'', hs''⟩ h
  have hall := ae_all_iff.2 hagree
  -- choose, for each point, a box that is a neighbourhood of it
  have hbox : ∀ p ∈ U, ∃ ab : (Fin n → ℚ) × (Fin n → ℚ), ratBox ab.1 ab.2 ⊆ U ∧
      ratBox ab.1 ab.2 ∈ 𝓝 p ∧ ∀ i, (ab.2 i : ℝ) - ab.1 i ≤ 1 := fun p hp => by
    obtain ⟨a, b, h1, h2, h3⟩ := exists_ratBox_nhds hU hp
    exact ⟨(a, b), h1, h2, h3⟩
  choose AB hABU hABn hABs using hbox
  set Y : (Fin n → ℝ) → Ω → ℝ := fun p ω =>
    if hp : p ∈ U then Yb (AB p hp).1 (AB p hp).2 (hABU p hp) (hABs p hp) p ω else 0 with hYdef
  refine ⟨Y, ?_, fun p hp => ?_⟩
  · filter_upwards [hall] with ω hω
    intro p hp
    have hev : (fun q => Y q ω) =ᶠ[𝓝 p]
        fun q => Yb (AB p hp).1 (AB p hp).2 (hABU p hp) (hABs p hp) q ω := by
      filter_upwards [hABn p hp] with q hq
      have hqU : q ∈ U := hABU p hp hq
      simp only [hYdef, dif_pos hqU]
      exact hω (((AB q hqU).1, (AB q hqU).2), ((AB p hp).1, (AB p hp).2)) (hABU q hqU)
        (hABs q hqU) (hABU p hp) (hABs p hp) q ⟨mem_of_mem_nhds (hABn q hqU), hq⟩
    have hc : ContinuousAt (fun q => Yb (AB p hp).1 (AB p hp).2 (hABU p hp) (hABs p hp) q ω) p :=
      (hYc _ _ (hABU p hp) (hABs p hp) ω).continuousAt (hABn p hp)
    exact (hc.congr hev.symm).continuousWithinAt
  · have e : (fun ω => Y p ω) =
        fun ω => Yb (AB p hp).1 (AB p hp).2 (hABU p hp) (hABs p hp) p ω := by
      funext ω; simp only [hYdef, dif_pos hp]
    rw [e]
    exact hYe _ _ (hABU p hp) (hABs p hp) p (mem_of_mem_nhds (hABn p hp))

end ASep
end QuantumZipper
