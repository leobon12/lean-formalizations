import SupercriticalLQGUniqueness.Uniqueness.Toolkit.PlanarSeparation.PathHit
import SupercriticalLQGUniqueness.Uniqueness.Toolkit.GaussianSymmetry
import Mathlib.Algebra.Order.Round




 






set_option autoImplicit false
noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace SupercriticalLQGUniqueness.Uniqueness.Positivity.SignDuality

variable (G : Finset ℂ) (J : Finset ℕ) (δ : ℝ)

abbrev Vector := G → J → ℝ
abbrev Pattern := G → J → Bool

 
def signs (y : Vector G J) : Pattern G J :=
  fun z j => decide (0 ≤ y z j)

 
def lowPattern (p : Pattern G J) (z : G) : Prop :=
  2 * (Finset.univ.filter fun j : J => p z j = true).card < J.card

def low (y : Vector G J) (z : G) : Prop :=
  lowPattern G J (signs G J y) z

 
def badPattern (δ : ℝ) (p : Pattern G J) : Set ℂ := by
  classical
  exact ⋃ z : G, if lowPattern G J p z then ∅ else Metric.closedBall (z : ℂ) δ

def Bad (δ : ℝ) (y : Vector G J) : Set ℂ :=
  badPattern G J δ (signs G J y)

 
def circuitPattern (δ : ℝ) (p : Pattern G J) : Prop :=
  ∃ S : Set ℂ, IsCompact S ∧ IsPathConnected S ∧
    S ⊆ {z : ℂ | 1 < dist z 0 ∧ dist z 0 < 2} ∧
    Disconnects S (Metric.sphere (0 : ℂ) 1) (Metric.sphere (0 : ℂ) 2) ∧
    Disjoint S (badPattern G J δ p)

 
def crossingPattern (δ : ℝ) (p : Pattern G J) : Prop :=
  ∃ X : Set ℂ, IsCompact X ∧ IsPathConnected X ∧
    X ⊆ Metric.ball (0 : ℂ) 3 ∧
    (X ∩ Metric.closedBall (0 : ℂ) 1).Nonempty ∧
    (X ∩ (Metric.ball (0 : ℂ) 2)ᶜ).Nonempty ∧
    Disjoint X (badPattern G J δ p)

def B_circ (δ : ℝ) : Set (Vector G J) :=
  {y | circuitPattern G J δ (signs G J y)}

def B_cross (δ : ℝ) : Set (Vector G J) :=
  {y | crossingPattern G J δ (signs G J y)}

theorem measurable_signs : Measurable (signs G J) := by
  classical
  apply measurable_pi_iff.mpr
  intro z
  apply measurable_pi_iff.mpr
  intro j
  change Measurable (fun y : Vector G J => if 0 ≤ y z j then true else false)
  exact Measurable.ite (measurableSet_le measurable_const
    ((measurable_pi_apply j).comp (measurable_pi_apply z))) measurable_const measurable_const

theorem measurableSet_B_circ : MeasurableSet (B_circ G J δ) := by
  classical
  change MeasurableSet ((signs G J) ⁻¹' {p | circuitPattern G J δ p})
  exact (Set.to_countable _).measurableSet.preimage (measurable_signs G J)

theorem measurableSet_B_cross : MeasurableSet (B_cross G J δ) := by
  classical
  change MeasurableSet ((signs G J) ⁻¹' {p | crossingPattern G J δ p})
  exact (Set.to_countable _).measurableSet.preimage (measurable_signs G J)

theorem low_iff (y : Vector G J) (z : G) :
    low G J y z ↔
      2 * (Finset.univ.filter fun j : J => 0 ≤ y z j).card < J.card := by
  simp only [low, lowPattern, signs, decide_eq_true_eq]

theorem low_neg_iff (y : Vector G J) (z : G) :
    low G J (-y) z ↔
      2 * (Finset.univ.filter fun j : J => y z j ≤ 0).card < J.card := by
  simpa only [low_iff, Pi.neg_apply, neg_nonneg]

 
theorem not_low_and_low_neg (y : Vector G J) (z : G) :
    ¬ (low G J y z ∧ low G J (-y) z) := by
  classical
  intro h
  rw [low_iff] at h
  rw [low_neg_iff] at h
  let A : Finset J := Finset.univ.filter fun j : J => 0 ≤ y z j
  let C : Finset J := Finset.univ.filter fun j : J => y z j ≤ 0
  have hcover : (Finset.univ : Finset J) ⊆ A ∪ C := by
    intro j hj
    by_cases hj0 : 0 ≤ y z j
    · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hj, hj0⟩)
    · exact Finset.mem_union_right _ (Finset.mem_filter.mpr
        ⟨hj, le_of_lt (lt_of_not_ge hj0)⟩)
  have hcard : J.card ≤ A.card + C.card := by
    calc
      J.card = (Finset.univ : Finset J).card := by simp
      _ ≤ (A ∪ C).card := Finset.card_le_card hcover
      _ ≤ A.card + C.card := Finset.card_union_le A C
  have hA : A = Finset.univ.filter (fun j : J => 0 ≤ y z j) := by
    ext j
    simp only [A]
  have hC : C = Finset.univ.filter (fun j : J => y z j ≤ 0) := by
    ext j
    simp only [C]
  rw [hA, hC] at hcard
  omega

theorem mem_Bad_of_not_low (y : Vector G J) (z : G) (hz : ¬ low G J y z)
    {w : ℂ} (hw : dist w z.1 ≤ δ) : w ∈ Bad G J δ y := by
  classical
  change w ∈ (⋃ z : G, if lowPattern G J (signs G J y) z then ∅
    else Metric.closedBall (z : ℂ) δ)
  refine Set.mem_iUnion.mpr ⟨z, ?_⟩
  have hz' : ¬ lowPattern G J (signs G J y) z := hz
  rw [if_neg hz']
  exact Metric.mem_closedBall.mpr hw

 
theorem low_of_avoids_Bad (y : Vector G J) (z : G) {S : Set ℂ}
    (havoid : Disjoint S (Bad G J δ y)) {w : ℂ}
    (hwS : w ∈ S) (hwz : dist w z.1 ≤ δ) : low G J y z := by
  by_contra hn
  exact (Set.disjoint_left.mp havoid) hwS (mem_Bad_of_not_low G J δ y z hn hwz)

theorem avoids_Bad_of_near_low (y : Vector G J) {S : Set ℂ}
    (hlow : ∀ w ∈ S, ∀ z : G, dist w z.1 ≤ δ → low G J y z) :
    Disjoint S (Bad G J δ y) := by
  classical
  apply Set.disjoint_left.mpr
  intro w hwS hwB
  change w ∈ (⋃ z : G, if lowPattern G J (signs G J y) z then ∅
    else Metric.closedBall (z : ℂ) δ) at hwB
  obtain ⟨z, hz⟩ := Set.mem_iUnion.mp hwB
  have hlowz := hlow w hwS z
  by_cases h : low G J y z
  · have h' : lowPattern G J (signs G J y) z := h
    rw [if_pos h'] at hz
    exact hz
  · have h' : ¬ lowPattern G J (signs G J y) z := h
    rw [if_neg h'] at hz
    exact h (hlowz (Metric.mem_closedBall.mp hz))

theorem circuit_of_trace (y : Vector G J) (S : Set ℂ)
    (hcompact : IsCompact S) (hpath : IsPathConnected S)
    (hann : S ⊆ {z : ℂ | 1 < dist z 0 ∧ dist z 0 < 2})
    (hdisc : Disconnects S (Metric.sphere (0 : ℂ) 1)
      (Metric.sphere (0 : ℂ) 2))
    (hlow : ∀ w ∈ S, ∀ z : G, dist w z.1 ≤ δ → low G J y z) :
    y ∈ B_circ G J δ := by
  exact ⟨S, hcompact, hpath, hann, hdisc,
    avoids_Bad_of_near_low G J δ y hlow⟩

theorem crossing_of_trace (y : Vector G J) (X : Set ℂ)
    (hcompact : IsCompact X) (hpath : IsPathConnected X)
    (hball : X ⊆ Metric.ball (0 : ℂ) 3)
    (hin : (X ∩ Metric.closedBall (0 : ℂ) 1).Nonempty)
    (hout : (X ∩ (Metric.ball (0 : ℂ) 2)ᶜ).Nonempty)
    (hlow : ∀ w ∈ X, ∀ z : G, dist w z.1 ≤ δ → low G J y z) :
    y ∈ B_cross G J δ := by
  exact ⟨X, hcompact, hpath, hball, hin, hout,
    avoids_Bad_of_near_low G J δ y hlow⟩

 
theorem crossing_of_eleven_traces (y : Vector G J) (S : ℕ → Set ℂ)
    (hdisc : ∀ j ≤ 10, LQGMetric.Disconnects (S j)
      (Metric.sphere (((1 + (j : ℝ) / 10 : ℝ) : ℂ)) (1 / 15 : ℝ))
      (Metric.sphere (((1 + (j : ℝ) / 10 : ℝ) : ℂ)) (2 / 15 : ℝ)))
    (hcompact : ∀ j ≤ 10, IsCompact (S j))
    (hpath : ∀ j ≤ 10, IsPathConnected (S j))
    (hball : ∀ j ≤ 10, S j ⊆ Metric.ball (0 : ℂ) 3)
    (hlow : ∀ j ≤ 10, ∀ w ∈ S j, ∀ z : G,
      dist w z.1 ≤ δ → low G J y z) :
    y ∈ B_cross G J δ := by
  let X : Set ℂ := ⋃ j ∈ Finset.range 11, S j
  have hcX : IsCompact X := by
    exact (Finset.range 11).isCompact_biUnion (fun j hj =>
      hcompact j (Nat.le_of_lt_succ (Finset.mem_range.mp hj)))
  have hpX : IsPathConnected X :=
    Toolkit.PlanarSeparation.eleven_small_trace_chain S hdisc hpath
  have hbX : X ⊆ Metric.ball (0 : ℂ) 3 := by
    intro w hw
    simp only [X, Set.mem_iUnion, Finset.mem_range] at hw
    obtain ⟨j, hj, hwj⟩ := hw
    exact hball j (by omega) hwj
  have hiX : (X ∩ Metric.closedBall (0 : ℂ) 1).Nonempty := by
    obtain ⟨w, hw, hwball⟩ :=
      Toolkit.PlanarSeparation.first_small_trace_inside
        (by simpa using hdisc 0 (by omega))
    exact ⟨w, Set.mem_iUnion.mpr ⟨0, Set.mem_iUnion.mpr
      ⟨Finset.mem_range.mpr (by omega), hw⟩⟩, hwball⟩
  have hoX : (X ∩ (Metric.ball (0 : ℂ) 2)ᶜ).Nonempty := by
    obtain ⟨w, hw, hwball⟩ :=
      Toolkit.PlanarSeparation.last_small_trace_outside
        (by convert hdisc 10 (by omega) using 1 <;> norm_num)
    exact ⟨w, Set.mem_iUnion.mpr ⟨10, Set.mem_iUnion.mpr
      ⟨Finset.mem_range.mpr (by omega), hw⟩⟩, hwball⟩
  have hlX : ∀ w ∈ X, ∀ z : G, dist w z.1 ≤ δ → low G J y z := by
    intro w hw z hwz
    simp only [X, Set.mem_iUnion, Finset.mem_range] at hw
    obtain ⟨j, hj, hwj⟩ := hw
    exact hlow j (by omega) w hwj z hwz
  exact crossing_of_trace G J δ y X hcX hpX hbX hiX hoX hlX

 
theorem circuit_crossing_disjoint
    (hmesh : ∀ w : ℂ, dist w 0 < 2 → ∃ z : G, dist w z.1 ≤ δ)
    (y : Vector G J) :
    ¬ (-(y) ∈ B_circ G J δ ∧ y ∈ B_cross G J δ) := by
  rintro ⟨hc, hx⟩
  rcases hc with ⟨S, _hSc, _hSp, hSa, hSd, hSb⟩
  rcases hx with ⟨X, _hXc, hXp, _hXb, hXin, hXout, hXbad⟩
  obtain ⟨w, hwS, hwX⟩ :=
    Toolkit.PlanarSeparation.disconnects_meets_pathConnected_crossing
      (by norm_num : (1 : ℝ) ≤ 2)
      (Toolkit.PlanarSeparation.candidate_disconnects_implies_path_hit hSd)
      hXp hXin hXout
  obtain ⟨z, hwz⟩ := hmesh w (hSa hwS).2
  have hlneg := low_of_avoids_Bad G J δ (-y) z hSb hwS hwz
  have hlpos := low_of_avoids_Bad G J δ y z hXbad hwX hwz
  exact not_low_and_low_neg G J y z ⟨hlpos, hlneg⟩

 

theorem probability_duality {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (Y : Ω → Vector G J) (hY : Measurable Y)
    (hAX4 : μ.map (fun ω => -Y ω) = μ.map Y)
    (hmesh : ∀ w : ℂ, dist w 0 < 2 → ∃ z : G, dist w z.1 ≤ δ)
    (E : Set Ω)
    (hAX11_AX12_circ : E ⊆ Y ⁻¹' B_circ G J δ)
    (hAX11_AX12_cross : E ⊆ Y ⁻¹' B_cross G J δ) :
    (2 : ℝ≥0∞) * μ E ≤ 1 := by
  let A : Set Ω := (fun ω => -Y ω) ⁻¹' B_circ G J δ
  let B : Set Ω := Y ⁻¹' B_cross G J δ
  have hAm : MeasurableSet A :=
    (measurableSet_B_circ G J δ).preimage (measurable_neg.comp hY)
  have hBm : MeasurableSet B :=
    (measurableSet_B_cross G J δ).preimage hY
  have hdisj : Disjoint A B := Set.disjoint_left.mpr (by
    intro ω hA hB
    exact circuit_crossing_disjoint G J δ hmesh (Y ω) ⟨hA, hB⟩)
  have hsymA : μ A = μ (Y ⁻¹' B_circ G J δ) := by
    change μ ((fun ω => -Y ω) ⁻¹' B_circ G J δ) =
      μ (Y ⁻¹' B_circ G J δ)
    have hneg : Measurable (fun ω => -Y ω) := measurable_neg.comp hY
    rw [← Measure.map_apply hneg (measurableSet_B_circ G J δ),
      hAX4, Measure.map_apply hY (measurableSet_B_circ G J δ)]
  have hEA : μ E ≤ μ A := hsymA ▸ measure_mono hAX11_AX12_circ
  have hEB : μ E ≤ μ B := measure_mono hAX11_AX12_cross
  calc
    (2 : ℝ≥0∞) * μ E = μ E + μ E := by ring
    _ ≤ μ A + μ B := add_le_add hEA hEB
    _ = μ (A ∪ B) := (measure_union hdisj hBm).symm
    _ ≤ μ Set.univ := measure_mono (Set.subset_univ _)
    _ = 1 := measure_univ

 

theorem finite_circleAverage_sign_symmetry
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (h : Ω → LQGMetric.DistC)
    (hh : IsNormalizedWholePlaneGFF h μ)
    (p : G × J → Set.Ioi (0 : ℝ) × ℂ)
    (a : (Set.Ioi (0 : ℝ) × ℂ) → Ω → ℝ)
    (ha : ∀ q : G × J, ∀ᵐ ω ∂μ,
      IsCircleAverage (h ω) (p q).1 (p q).2 (a (p q) ω))
    (hma : ∀ q : G × J, Measurable (a (p q))) :
    μ.map (fun ω z j => -a (p (z, j)) ω) =
      μ.map (fun ω z j => a (p (z, j)) ω) := by
  classical
  let I : Finset (Set.Ioi (0 : ℝ) × ℂ) := Finset.univ.image p
  let σ : G × J → I := fun q =>
    ⟨p q, Finset.mem_image.mpr ⟨q, Finset.mem_univ _, rfl⟩⟩
  let R : (I → ℝ) → Vector G J := fun x z j => x (σ (z, j))
  let X : Ω → I → ℝ := fun ω i => a i.1 ω
  have hXI : Measurable X := by
    apply measurable_pi_iff.mpr
    intro i
    obtain ⟨q, _, hq⟩ := Finset.mem_image.mp i.2
    simpa only [X, ← hq] using hma q
  have hR : Measurable R := by
    apply measurable_pi_iff.mpr
    intro z
    apply measurable_pi_iff.mpr
    intro j
    exact measurable_pi_apply (σ (z, j))
  have haI : ∀ i ∈ I, ∀ᵐ ω ∂μ,
      IsCircleAverage (h ω) i.1 i.2 (a i ω) := by
    intro i hi
    obtain ⟨q, _, hq⟩ := Finset.mem_image.mp hi
    subst i
    exact ha q
  have hAX4 := finite_circleAverage_symmetry hh I a haI
  have hXN : Measurable (fun ω (i : I) => -a i.1 ω) := measurable_neg.comp hXI
  calc
    μ.map (fun ω z j => -a (p (z, j)) ω) =
        (μ.map (fun ω (i : I) => -a i.1 ω)).map R := by
      rw [Measure.map_map hR hXN]
      rfl
    _ = (μ.map X).map R := by rw [hAX4]
    _ = μ.map (fun ω z j => a (p (z, j)) ω) := by
      rw [Measure.map_map hR hXI]
      rfl

 


theorem ax14_probability_bound
    {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (h : Ω → LQGMetric.DistC)
    (hh : IsNormalizedWholePlaneGFF h μ)
    (p : G × J → Set.Ioi (0 : ℝ) × ℂ)
    (a : (Set.Ioi (0 : ℝ) × ℂ) → Ω → ℝ)
    (hAX4_version : ∀ q : G × J, ∀ᵐ ω ∂μ,
      IsCircleAverage (h ω) (p q).1 (p q).2 (a (p q) ω))
    (hAX4_measurable : ∀ q : G × J, Measurable (a (p q)))
    (hAX11_mesh : ∀ w : ℂ, dist w 0 < 2 → ∃ z : G, dist w z.1 ≤ δ)
    (E : Set Ω)
    (hAX12_AX13 : ∀ ω ∈ E,
      ∃ (S₀ : Set ℂ) (S : ℕ → Set ℂ),
        IsCompact S₀ ∧ IsPathConnected S₀ ∧
        S₀ ⊆ {z : ℂ | 1 < dist z 0 ∧ dist z 0 < 2} ∧
        Disconnects S₀ (Metric.sphere (0 : ℂ) 1)
          (Metric.sphere (0 : ℂ) 2) ∧
        (∀ j ≤ 10, LQGMetric.Disconnects (S j)
          (Metric.sphere (((1 + (j : ℝ) / 10 : ℝ) : ℂ)) (1 / 15 : ℝ))
          (Metric.sphere (((1 + (j : ℝ) / 10 : ℝ) : ℂ)) (2 / 15 : ℝ))) ∧
        (∀ j ≤ 10, IsCompact (S j)) ∧
        (∀ j ≤ 10, IsPathConnected (S j)) ∧
        (∀ j ≤ 10, S j ⊆ Metric.ball (0 : ℂ) 3) ∧
        (∀ w ∈ S₀, ∀ z : G, dist w z.1 ≤ δ →
          low G J (fun z j => a (p (z, j)) ω) z) ∧
        (∀ j ≤ 10, ∀ w ∈ S j, ∀ z : G,
          dist w z.1 ≤ δ → low G J (fun z j => a (p (z, j)) ω) z)) :
    (2 : ℝ≥0∞) * μ E ≤ 1 := by
  let Y : Ω → Vector G J := fun ω z j => a (p (z, j)) ω
  have hY : Measurable Y := by
    apply measurable_pi_iff.mpr
    intro z
    apply measurable_pi_iff.mpr
    intro j
    exact hAX4_measurable (z, j)
  have hsym : μ.map (fun ω => -Y ω) = μ.map Y :=
    finite_circleAverage_sign_symmetry G J μ h hh p a hAX4_version hAX4_measurable
  have hEcirc : E ⊆ Y ⁻¹' B_circ G J δ := by
    intro ω hω
    obtain ⟨S₀, S, hc₀, hp₀, ha₀, hd₀, _, _, _, _, hl₀, _⟩ :=
      hAX12_AX13 ω hω
    exact circuit_of_trace G J δ (Y ω) S₀ hc₀ hp₀ ha₀ hd₀ hl₀
  have hEcross : E ⊆ Y ⁻¹' B_cross G J δ := by
    intro ω hω
    obtain ⟨S₀, S, _, _, _, _, hd, hc, hp, hb, _, hl⟩ :=
      hAX12_AX13 ω hω
    exact crossing_of_eleven_traces G J δ (Y ω) S hd hc hp hb hl
  exact probability_duality G J δ μ Y hY hsym hAX11_mesh E hEcirc hEcross

def latticePoint (δ : ℝ) (n m : ℤ) : ℂ :=
  (δ * n : ℝ) + (δ * m : ℝ) * Complex.I

theorem abs_sub_round_mul (δ x : ℝ) (hδ : 0 < δ) :
    |x - δ * (round (x / δ) : ℝ)| ≤ δ / 2 := by
  have h := abs_sub_round (x / δ)
  have heq : x - δ * (round (x / δ) : ℝ) =
      δ * (x / δ - (round (x / δ) : ℝ)) := by
    field_simp
  rw [heq, abs_mul, abs_of_pos hδ]
  have hmul := mul_le_mul_of_nonneg_left h hδ.le
  nlinarith only [hmul]

theorem exists_near_latticePoint (δ : ℝ) (hδ : 0 < δ) (w : ℂ) :
    ∃ n m : ℤ, dist w (latticePoint δ n m) ≤ δ := by
  refine ⟨round (w.re / δ), round (w.im / δ), ?_⟩
  have hre := abs_sub_round_mul δ w.re hδ
  have him := abs_sub_round_mul δ w.im hδ
  have hnorm := Complex.norm_le_abs_re_add_abs_im
    (w - latticePoint δ (round (w.re / δ)) (round (w.im / δ)))
  have heqre : (w - latticePoint δ (round (w.re / δ)) (round (w.im / δ))).re =
      w.re - δ * (round (w.re / δ) : ℝ) := by
    simp [latticePoint]
  have heqim : (w - latticePoint δ (round (w.re / δ)) (round (w.im / δ))).im =
      w.im - δ * (round (w.im / δ) : ℝ) := by
    simp [latticePoint]
  rw [heqre, heqim] at hnorm
  rw [dist_eq_norm]
  linarith only [hre, him, hnorm]

 

theorem mesh_of_lattice_grid (G : Finset ℂ) (δ : ℝ)
    (hδ : 0 < δ) (hδ1 : δ < 1)
    (hgrid : ∀ n m : ℤ, dist (latticePoint δ n m) 0 < 3 →
      latticePoint δ n m ∈ G) :
    ∀ w : ℂ, dist w 0 < 2 → ∃ z : G, dist w z.1 ≤ δ := by
  intro w hw
  obtain ⟨n, m, hnear⟩ := exists_near_latticePoint δ hδ w
  have hinside : dist (latticePoint δ n m) 0 < 3 := by
    calc
      dist (latticePoint δ n m) 0 ≤
          dist (latticePoint δ n m) w + dist w 0 := dist_triangle _ _ _
      _ < 3 := by rw [dist_comm (latticePoint δ n m) w]; linarith
  exact ⟨⟨latticePoint δ n m, hgrid n m hinside⟩, hnear⟩

end SupercriticalLQGUniqueness.Uniqueness.Positivity.SignDuality
