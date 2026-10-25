import SupercriticalLQGUniqueness.B2.PfeLocal.L4Lattice
import SupercriticalLQGUniqueness.B2.PfeLocal.CircleMin
import SupercriticalLQGUniqueness.B2.PfeLocal.CirclePath

 


















set_option autoImplicit false
noncomputable section

open Set Metric MeasureTheory Filter Topology
open scoped ENNReal
open LQGMetric

namespace SupercriticalLQGUniqueness.B2.PfeLocal

 
def l4Ev (ξ : ℝ) (c : Set.Ioi (0 : ℝ) → Set.Ioi (0 : ℝ)) (g : DistC) (D : LSCMetric) (w : ℂ)
    (k₀ k : ℕ) (C : Set.Ioi (1 : ℝ)) : Prop :=
  ENNReal.ofReal ((c ⟨l1Scale k₀ k, l1Scale_pos k₀ k⟩ : ℝ) / (C : ℝ) *
      Real.exp (ξ * circleAvg g (l1Scale k₀ k) w)) <
    acrossDist D (innerAnnulus w (l1Scale k₀ k) (l1Scale_pos k₀ k)) ∧
  aroundDist D (outerAnnulus w (l1Scale k₀ k) (l1Scale_pos k₀ k)) <
    ENNReal.ofReal ((C : ℝ) * (c ⟨l1Scale k₀ k, l1Scale_pos k₀ k⟩ : ℝ) *
      Real.exp (ξ * circleAvg g (l1Scale k₀ k) w))

 
def l4Good (ξ : ℝ) (c : Set.Ioi (0 : ℝ) → Set.Ioi (0 : ℝ)) (g : DistC) (D : LSCMetric) (w : ℂ)
    (k₀ : ℕ) (C : Set.Ioi (1 : ℝ)) : Finset ℕ := by
  classical exact (Finset.Icc 1 k₀).filter fun k => l4Ev ξ c g D w k₀ k C

 
def l4LatticeGood (ξ : ℝ) (c : Set.Ioi (0 : ℝ) → Set.Ioi (0 : ℝ)) (g : DistC) (D₁ D₂ : LSCMetric)
    (k₀ : ℕ) (R : ℝ) (C : Set.Ioi (1 : ℝ)) : Prop :=
  ∀ w ∈ l4Lattice k₀ R, (3 / 4 : ℝ) * k₀ ≤ (l4Good ξ c g D₁ w k₀ C).card ∧
    (3 / 4 : ℝ) * k₀ ≤ (l4Good ξ c g D₂ w k₀ C).card

theorem l1Scale_anti (k₀ : ℕ) {k k' : ℕ} (h : k ≤ k') : l1Scale k₀ k' ≤ l1Scale k₀ k := by
  unfold l1Scale
  exact pow_le_pow_of_le_one (by norm_num) (by norm_num) (by omega)

 
theorem l4_chain_of_counts (ξ : ℝ) (c : Set.Ioi (0 : ℝ) → Set.Ioi (0 : ℝ)) (g : DistC)
    (D₁ D₂ : LSCMetric) {k₀ : ℕ} (hk₀ : 1 ≤ k₀) {R : ℝ} (hR : 0 ≤ R) (C : Set.Ioi (1 : ℝ))
    (hgood : l4LatticeGood ξ c g D₁ D₂ k₀ R C) (P : ℝ → ℂ) {a b : ℝ} (hab : a ≤ b)
    (hPc : ContinuousOn P (Icc a b)) (hPR : ∀ t ∈ Icc a b, ‖P t‖ ≤ R)
    (hlen : D₁.len P a b < ∞) :
    ∃ x₁ ∈ closedBall (P a) (4 * l1Scale k₀ 1), ∃ x₂ ∈ closedBall (P b) (4 * l1Scale k₀ 1),
      D₂ (x₁, x₂) ≤ ENNReal.ofReal ((C : ℝ) ^ 2) * D₁.len P a b := by
  classical
  have hC : (1 : ℝ) < C := C.2
  have hC0 : (0 : ℝ) < C := by linarith
  set G : Finset (ℂ × ℕ) := l4Lattice k₀ R ×ˢ Finset.Icc 1 k₀ with hG
  have hGne : G.Nonempty := by
    obtain ⟨w, hw, -⟩ := l4_lattice_near k₀ hR (p := 0) (by simpa using hR)
    exact ⟨(w, 1), Finset.mem_product.2 ⟨hw, Finset.mem_Icc.2 ⟨le_rfl, hk₀⟩⟩⟩
  set f : ℂ × ℕ → ℝ := fun q => (c ⟨l1Scale k₀ q.2, l1Scale_pos k₀ q.2⟩ : ℝ) / (C : ℝ) *
    Real.exp (ξ * circleAvg g (l1Scale k₀ q.2) q.1) with hf
  set μ₀ : ℝ := G.inf' hGne f with hμ₀
  have hμ₀pos : 0 < μ₀ := by
    rw [hμ₀, Finset.lt_inf'_iff]
    intro q _
    have := Set.mem_Ioi.1 (c ⟨l1Scale k₀ q.2, l1Scale_pos k₀ q.2⟩).2
    simp only [hf]
    exact mul_pos (div_pos this hC0) (Real.exp_pos _)
  refine l4_chain D₁ D₂ (ENNReal.ofReal ((C : ℝ) ^ 2)) (l1Scale k₀ 1) μ₀ hμ₀pos P hab hPc hlen
    fun t ht => ?_
  obtain ⟨w, hw, hdist⟩ := l4_lattice_near k₀ hR (hPR t ht)
  obtain ⟨h₁, h₂⟩ := hgood w hw
  obtain ⟨k, hk⟩ := l4_finset_meet hk₀ (Finset.filter_subset _ _) (Finset.filter_subset _ _) h₁ h₂
  rw [Finset.mem_inter] at hk
  obtain ⟨hk₁, hk₂⟩ := hk
  have hk₁' := (Finset.mem_filter.1 hk₁)
  have hk₂' := (Finset.mem_filter.1 hk₂)
  obtain ⟨hkI, hE₁⟩ := hk₁'
  obtain ⟨-, hE₂⟩ := hk₂'
  obtain ⟨hk1, hkk₀⟩ := Finset.mem_Icc.1 hkI
  set r := l1Scale k₀ k
  refine ⟨w, r, l1Scale_pos k₀ k, l1Scale_anti k₀ hk1, ?_, ?_, ?_⟩
  · rw [mem_ball]
    have h1 : l4Spacing k₀ ≤ r / 4 := by
      unfold l4Spacing; have := l1Scale_anti k₀ hkk₀; linarith
    have := l1Scale_pos k₀ k
    linarith
  · refine le_trans (ENNReal.ofReal_le_ofReal ?_) hE₁.1.le
    exact Finset.inf'_le (s := G) f (b := (w, k)) (Finset.mem_product.2 ⟨hw, hkI⟩)
  · refine lt_of_lt_of_le hE₂.2 ?_
    have heq : ENNReal.ofReal ((C : ℝ) * (c ⟨r, l1Scale_pos k₀ k⟩ : ℝ) *
        Real.exp (ξ * circleAvg g r w)) = ENNReal.ofReal ((C : ℝ) ^ 2) *
        ENNReal.ofReal ((c ⟨r, l1Scale_pos k₀ k⟩ : ℝ) / (C : ℝ) * Real.exp (ξ * circleAvg g r w)) := by
      rw [← ENNReal.ofReal_mul (by positivity)]
      congr 1
      field_simp
    rw [heq]
    exact mul_le_mul_right hE₁.1.le _

 
theorem l4_lsc_le_of_tendsto (D : LSCMetric) {u : ℕ → ℂ × ℂ} {p : ℂ × ℂ}
    (hu : Tendsto u atTop (𝓝 p)) {M : ℝ≥0∞} (hM : ∀ j, D (u j) ≤ M) : D p ≤ M := by
  by_contra hlt
  push Not at hlt
  have := (D.2.2 p M hlt).filter_mono (le_refl _)
  obtain ⟨j, hj⟩ := (hu.eventually this).exists
  exact absurd (hM j) (not_le.2 hj)

 
theorem l4_bilip_general {Ω₂ : Type} [MeasurableSpace Ω₂] (Q : Measure Ω₂)
    [IsProbabilityMeasure Q] (ξ : ℝ) (c : Set.Ioi (0 : ℝ) → Set.Ioi (0 : ℝ))
    (C : Set.Ioi (1 : ℝ)) (g : Ω₂ → DistC) (X₁ X₂ : Ω₂ → LSCMetric)
    (hgeo : ∀ᵐ p ∂Q, (∀ u : ℂ, ∀ δ : ℝ, 0 < δ → ∃ η : ℝ, 0 < η ∧
        ∀ v : ℂ, (X₁ p).1 (u, v) < ENNReal.ofReal η → dist u v < δ) ∧
      (∀ u v : ℂ, (X₁ p).1 (u, v) < ∞ → ∃ (γ : ℝ → ℂ) (a b : ℝ),
        (X₁ p).IsCurve γ a b ∧ γ a = u ∧ γ b = v ∧ (X₁ p).len γ a b = (X₁ p).1 (u, v)))
    (hprob : ∀ R : ℕ, Tendsto (fun k₀ => Q {p | ¬ l4LatticeGood ξ c (g p) (X₁ p) (X₂ p) k₀ R C})
      atTop (𝓝 0)) :
    ∀ᵐ p ∂Q, ∀ O O' : Set ℂ, Iface.IsRationalCircle O → Iface.IsRationalCircle O' →
      Iface.setDistance (X₂ p).1 O O' ≤
        ENNReal.ofReal ((C : ℝ) ^ 2) * Iface.setDistance (X₁ p).1 O O' := by
  have hC : (1 : ℝ) < C := C.2
  
  have hfreq : ∀ᵐ p ∂Q, ∀ R : ℕ, ∃ᶠ k₀ in atTop,
      l4LatticeGood ξ c (g p) (X₁ p) (X₂ p) k₀ R C := by
    rw [ae_all_iff]
    intro R
    have hnull : Q {p | ∀ᶠ k₀ in atTop, p ∈ {p | ¬ l4LatticeGood ξ c (g p) (X₁ p) (X₂ p) k₀ R C}}
        = 0 := by
      refine le_antisymm (ENNReal.le_of_forall_pos_le_add fun ε hε _ => ?_) (zero_le)
      rw [zero_add]
      exact l1_measure_eventually_le ((ENNReal.tendsto_nhds_zero.1 (hprob R)) ε
        (by exact_mod_cast hε))
    rw [ae_iff]
    refine measure_mono_null (fun p hp => ?_) hnull
    simp only [mem_ofPred_eq, Filter.not_frequently] at hp ⊢
    exact hp
  filter_upwards [hgeo, hfreq] with p hpgeo hfr O O' hO hO'
  obtain ⟨hsmall, hgeod⟩ := hpgeo
  obtain ⟨z₁, hz₁, z₂, hz₂, heq⟩ := rationalCircle_distance_attained (X₁ p) hO hO'
  by_cases hfin : Iface.setDistance (X₁ p).1 O O' = ∞
  · rw [hfin, ENNReal.mul_top (by
      have : (0 : ℝ) < (C : ℝ) ^ 2 := by positivity
      exact (ENNReal.ofReal_pos.2 this).ne')]
    exact le_top
  have hfin' : (X₁ p).1 (z₁, z₂) < ∞ := heq ▸ lt_top_iff_ne_top.2 hfin
  obtain ⟨γ, a, b, hγ, hγa, hγb, hlen⟩ := hgeod z₁ z₂ hfin'
  have hab : a ≤ b := hγ.1
  have hγc : ContinuousOn γ (Icc a b) := continuousOn_euclidean_of_small_metric (X₁ p) hsmall γ hγ
  obtain ⟨R₀, hR₀⟩ := ((isCompact_Icc.image_of_continuousOn hγc).isBounded).subset_closedBall 0
  obtain ⟨R, hR⟩ := exists_nat_ge R₀
  have hγR : ∀ t ∈ Icc a b, ‖γ t‖ ≤ (R : ℝ) := by
    intro t ht
    have := hR₀ ⟨t, ht, rfl⟩
    rw [mem_closedBall, dist_zero_right] at this
    linarith
  have hlenfin : (X₁ p).len γ a b < ∞ := hlen ▸ hfin'
  
  have hQ : ∃ᶠ k₀ in atTop, ∃ x₁ ∈ closedBall z₁ (4 * l1Scale k₀ 1),
      ∃ x₂ ∈ closedBall z₂ (4 * l1Scale k₀ 1),
        (X₂ p) (x₁, x₂) ≤ ENNReal.ofReal ((C : ℝ) ^ 2) * (X₁ p).len γ a b := by
    refine ((hfr R).and_eventually (eventually_ge_atTop 1)).mono fun k₀ hk => ?_
    obtain ⟨hgood, hk₀⟩ := hk
    have := l4_chain_of_counts ξ c (g p) (X₁ p) (X₂ p) hk₀ (by positivity) C hgood γ hab hγc hγR
      hlenfin
    rw [hγa, hγb] at this
    exact this
  obtain ⟨φ, hφ, hφQ⟩ := Filter.extraction_of_frequently_atTop hQ
  choose x₁ hx₁ x₂ hx₂ hxle using hφQ
  have hρ : Tendsto (fun j => 4 * l1Scale (φ j) 1) atTop (𝓝 0) := by
    have h1 : Tendsto (fun k : ℕ => l1Scale k 1) atTop (𝓝 0) := by
      unfold l1Scale
      exact (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)).comp
        (tendsto_add_atTop_nat 1)
    simpa using (h1.comp hφ.tendsto_atTop).const_mul 4
  have hconv : ∀ (z : ℂ) (x : ℕ → ℂ), (∀ j, x j ∈ closedBall z (4 * l1Scale (φ j) 1)) →
      Tendsto x atTop (𝓝 z) := by
    intro z x hx
    rw [tendsto_iff_dist_tendsto_zero]
    exact squeeze_zero (fun j => dist_nonneg) (fun j => mem_closedBall.1 (hx j)) hρ
  have hlim := l4_lsc_le_of_tendsto (X₂ p) ((hconv z₁ x₁ hx₁).prodMk_nhds (hconv z₂ x₂ hx₂))
    hxle
  calc Iface.setDistance (X₂ p).1 O O' ≤ (X₂ p).1 (z₁, z₂) :=
        iInf₂_le_of_le z₁ hz₁ (iInf₂_le z₂ hz₂)
    _ ≤ ENNReal.ofReal ((C : ℝ) ^ 2) * (X₁ p).len γ a b := hlim
    _ = ENNReal.ofReal ((C : ℝ) ^ 2) * Iface.setDistance (X₁ p).1 O O' := by rw [hlen, ← heq]

end SupercriticalLQGUniqueness.B2.PfeLocal
