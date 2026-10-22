import HigherDimLQGContinuity.MomentsW1.BadScaleDefs

/-! # Measurability of finite-support cluster statuses -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace HigherDimLQGContinuity

open HigherDimLFPP HigherDimLFPP.Perc
open HigherDimLFPP.DGZ (latPt latPt_apply)
open HigherDimLQGMetric.DGZ

theorem measurableSet_wnClosed {d : ℕ} {κ : Rd d → ℝ}
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {W : WN d → Ω → ℝ} {H : ℕ → Rd d → Ω → ℝ}
    (hH : IsDyadicRealization κ P W H) (ξ R : ℝ) (q : ℝ≥0∞)
    (k n : ℕ) (x : Zd d) : MeasurableSet (wnClosed P H ξ R q k n x) := by
  have hc : ∀ ω, Continuous fun z => H n z ω - H k z ω :=
    fun ω => ((hH.band n).continuous ω).sub ((hH.band k).continuous ω)
  have hm : ∀ z, Measurable (fun ω => H n z ω - H k z ω) :=
    fun z => ((hH.band n).measurable z).sub ((hH.band k).measurable z)
  have hs : 0 < (2 : ℝ)⁻¹ ^ k := by positivity
  have hclosed := HigherDimLFPP.DGZ.measurableSet_closedSite hc hm hs ξ
    (aQ P H ξ (n - k) q) (R + 3) x
  exact (MeasurableSet.const (x ∈ wnRegion R k)).inter hclosed

/-- Every enlarged physical box contains finitely many sites at a fixed mesh. -/
theorem wnRegion_bounded {d : ℕ} (R : ℝ) (k : ℕ) :
    ∃ N : ℕ, ∀ x ∈ wnRegion (d := d) R k, WithinInf (N : ℤ) x 0 := by
  let s : ℝ := (2 : ℝ)⁻¹ ^ k
  have hs : 0 < s := by dsimp [s]; positivity
  let N : ℕ := ⌈(R + 3) / s⌉₊
  have hN : (R + 3) / s ≤ N := Nat.le_ceil _
  refine ⟨N, ?_⟩
  intro x hx i
  have hx' := hx i
  have hcast : |((x i : ℤ) : ℝ)| * s < R + 3 := by
    change |s * ((x i : ℤ) : ℝ)| < R + 3 at hx'
    rw [abs_mul, abs_of_pos hs] at hx'
    simpa only [mul_comm] using hx'
  have hcast' : |((x i : ℤ) : ℝ)| ≤ N := by
    have := (le_div_iff₀ hs).2 hcast.le
    exact this.trans hN
  have hi : |x i| ≤ (N : ℤ) := by exact_mod_cast hcast'
  simpa only [Pi.zero_apply, sub_zero] using hi

theorem wnRegion_finite {d : ℕ} (R : ℝ) (k : ℕ) :
    (wnRegion (d := d) R k).Finite := by
  obtain ⟨N, hN⟩ := wnRegion_bounded (d := d) R k
  exact finite_of_withinInf hN

/-- The lattice radius of the enlarged box grows at most linearly in `R` and as `2^k`. -/
theorem wnRegion_bounded_le {d : ℕ} {R : ℝ} (hR : 1 ≤ R) (k : ℕ) :
    ∃ N : ℕ, (∀ x ∈ wnRegion (d := d) R k, WithinInf (N : ℤ) x 0) ∧
      (N : ℝ) ≤ (R + 4) * (2 : ℝ) ^ k := by
  let s : ℝ := (2 : ℝ)⁻¹ ^ k
  have hs : 0 < s := by dsimp [s]; positivity
  let N : ℕ := ⌈(R + 3) / s⌉₊
  have hN : (R + 3) / s ≤ N := Nat.le_ceil _
  have hNupper : (N : ℝ) < (R + 3) / s + 1 :=
    Nat.ceil_lt_add_one (by positivity)
  have hpow : (1 : ℝ) ≤ (2 : ℝ) ^ k := one_le_pow₀ (by norm_num)
  have hdiv : (R + 3) / s = (R + 3) * (2 : ℝ) ^ k := by
    dsimp [s]
    rw [inv_pow, div_inv_eq_mul]
  refine ⟨N, ?_, ?_⟩
  · intro x hx i
    have hx' := hx i
    have hcast : |((x i : ℤ) : ℝ)| * s < R + 3 := by
      change |s * ((x i : ℤ) : ℝ)| < R + 3 at hx'
      rw [abs_mul, abs_of_pos hs] at hx'
      simpa only [mul_comm] using hx'
    have hcast' : |((x i : ℤ) : ℝ)| ≤ N := by
      have := (le_div_iff₀ hs).2 hcast.le
      exact this.trans hN
    have hi : |x i| ≤ (N : ℤ) := by exact_mod_cast hcast'
    simpa only [Pi.zero_apply, sub_zero] using hi
  · rw [hdiv] at hNupper
    nlinarith

theorem wnClosed_support_finite {d : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (H : ℕ → Rd d → Ω → ℝ)
    (ξ R : ℝ) (q : ℝ≥0∞) (k n : ℕ) :
    {x | wnClosed P H ξ R q k n x ≠ ∅}.Finite := by
  apply (wnRegion_finite (d := d) R k).subset
  intro x hx
  by_contra hnot
  apply hx
  ext ω
  simp [wnClosed, hnot]

/-- A small-cluster event is measurable when the site status is measurable and only finitely
many sites can be closed. This encodes the configuration as a measurable finite set. -/
theorem wnMeasurable_smallClusters {d : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    (closed : Zd d → Set Ω) (hm : ∀ x, MeasurableSet (closed x))
    (hfin : {x | closed x ≠ ∅}.Finite) (D : ℕ) :
    MeasurableSet {ω | SmallClusters {x | ω ∉ closed x} D} := by
  classical
  let F : Finset (Zd d) := hfin.toFinset
  let B : Ω → Finset (Zd d) := fun ω => F.filter fun x => ω ∈ closed x
  have hF (x : Zd d) (hx : x ∉ F) : closed x = ∅ := by
    by_contra h
    exact hx (hfin.mem_toFinset.mpr h)
  have hB : Measurable B := by
    apply measurable_finset_iff.mpr
    intro x
    by_cases hx : x ∈ F
    · have hm' : Measurable (fun ω : Ω => ω ∈ closed x) :=
        (measurableSet_setOfPred.1 (hm x))
      simpa only [B, Finset.mem_filter, hx, true_and] using hm'
    · simpa only [B, Finset.mem_filter, hx, false_and] using
        (measurable_const : Measurable fun _ : Ω => False)
  have heq (ω : Ω) : {x | ω ∉ closed x} = ((B ω : Finset (Zd d)) : Set (Zd d))ᶜ := by
    ext x
    by_cases hx : x ∈ F
    · simp only [B, Set.mem_ofPred_eq, Set.mem_compl_iff, Finset.mem_coe,
        Finset.mem_filter, hx, true_and]
    · simp [B, hx, hF x hx]
  have hS : MeasurableSet {S : Finset (Zd d) |
      SmallClusters (((S : Set (Zd d)))ᶜ) D} :=
    (Set.countable_univ.mono (subset_univ _)).measurableSet
  have hpre := hB hS
  convert hpre using 1
  ext ω
  simp only [Set.mem_preimage, Set.mem_ofPred_eq, heq]

theorem measurableSet_wnGood_smallClusters {d : ℕ} {κ : Rd d → ℝ}
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {W : WN d → Ω → ℝ} {H : ℕ → Rd d → Ω → ℝ}
    (hH : IsDyadicRealization κ P W H) (ξ R : ℝ) (q : ℝ≥0∞)
    (k n D : ℕ) :
    MeasurableSet {ω | SmallClusters (wnGood P H ξ R q k n ω) D} := by
  change MeasurableSet {ω | SmallClusters
    {x | ω ∉ wnClosed P H ξ R q k n x} D}
  exact wnMeasurable_smallClusters (wnClosed P H ξ R q k n)
    (measurableSet_wnClosed hH ξ R q k n)
    (wnClosed_support_finite P H ξ R q k n) D

theorem wnRough_eq {d : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (H : ℕ → Rd d → Ω → ℝ)
    (ξ R : ℝ) (q : ℝ≥0∞) (k n : ℕ) (y : Zd d) :
    wnRough P H ξ R q k n y =
      wnClosed P H ξ R q (k - 1) n y ∪
        ⋃ z ∈ boxF (2 • y) 1, wnClosed P H ξ R q k n z := by
  ext ω
  simp only [wnRough, wnNice, wnGood, Set.mem_ofPred_eq, Set.mem_union,
    Set.mem_iUnion, mem_boxF]
  push Not
  tauto

theorem measurableSet_wnRough {d : ℕ} {κ : Rd d → ℝ}
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {W : WN d → Ω → ℝ} {H : ℕ → Rd d → Ω → ℝ}
    (hH : IsDyadicRealization κ P W H) (ξ R : ℝ) (q : ℝ≥0∞)
    (k n : ℕ) (y : Zd d) : MeasurableSet (wnRough P H ξ R q k n y) := by
  rw [wnRough_eq]
  exact (measurableSet_wnClosed hH ξ R q (k - 1) n y).union
    (Finset.measurableSet_biUnion _ fun z _ => measurableSet_wnClosed hH ξ R q k n z)

theorem wnRough_support_bounded {d : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (H : ℕ → Rd d → Ω → ℝ)
    (ξ R : ℝ) (q : ℝ≥0∞) (k n : ℕ) :
    ∃ N : ℕ, ∀ y, wnRough P H ξ R q k n y ≠ ∅ → WithinInf (N : ℤ) y 0 := by
  obtain ⟨N₁, hN₁⟩ := wnRegion_bounded (d := d) R (k - 1)
  obtain ⟨N₂, hN₂⟩ := wnRegion_bounded (d := d) R k
  refine ⟨N₁ + N₂ + 1, ?_⟩
  intro y hy
  obtain ⟨ω, hω⟩ := Set.nonempty_iff_ne_empty.mpr hy
  rw [wnRough_eq] at hω
  intro i
  rcases hω with hω | hω
  · have hreg : y ∈ wnRegion R (k - 1) := hω.1
    have h := hN₁ y hreg i
    simp only [Pi.zero_apply, sub_zero] at h ⊢
    omega
  · obtain ⟨z, hz⟩ := Set.mem_iUnion.1 hω
    obtain ⟨hz, hzclosed⟩ := Set.mem_iUnion.1 hz
    have hreg : z ∈ wnRegion R k := hzclosed.1
    have hN := hN₂ z hreg i
    have hz' := (mem_boxF.1 hz) i
    rw [two_smul_apply] at hz'
    simp only [Pi.zero_apply, sub_zero] at hN ⊢
    rw [abs_le] at hN hz' ⊢
    omega

theorem wnRough_support_finite {d : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (H : ℕ → Rd d → Ω → ℝ)
    (ξ R : ℝ) (q : ℝ≥0∞) (k n : ℕ) :
    {y | wnRough P H ξ R q k n y ≠ ∅}.Finite := by
  obtain ⟨N, hN⟩ := wnRough_support_bounded P H ξ R q k n
  exact finite_of_withinInf (fun y hy => hN y hy)

/-- Quantitative support radius for rough sites. -/
theorem wnRough_support_bounded_le {d : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (H : ℕ → Rd d → Ω → ℝ)
    (ξ : ℝ) {R : ℝ} (hR : 1 ≤ R) (q : ℝ≥0∞) (k n : ℕ) :
    ∃ N : ℕ, (∀ y, wnRough P H ξ R q k n y ≠ ∅ → WithinInf (N : ℤ) y 0) ∧
      (N : ℝ) ≤ 3 * (R + 4) * (2 : ℝ) ^ k := by
  obtain ⟨N₁, hN₁, hN₁le⟩ := wnRegion_bounded_le (d := d) hR (k - 1)
  obtain ⟨N₂, hN₂, hN₂le⟩ := wnRegion_bounded_le (d := d) hR k
  let N := N₁ + N₂ + 1
  refine ⟨N, ?_, ?_⟩
  · intro y hy i
    obtain ⟨ω, hω⟩ := Set.nonempty_iff_ne_empty.mpr hy
    rw [wnRough_eq] at hω
    rcases hω with hω | hω
    · have h := hN₁ y hω.1 i
      simp only [Pi.zero_apply, sub_zero] at h ⊢
      dsimp [N]
      omega
    · obtain ⟨z, hz⟩ := Set.mem_iUnion.1 hω
      obtain ⟨hz, hzclosed⟩ := Set.mem_iUnion.1 hz
      have hN := hN₂ z hzclosed.1 i
      have hz' := (mem_boxF.1 hz) i
      rw [two_smul_apply] at hz'
      simp only [Pi.zero_apply, sub_zero] at hN ⊢
      rw [abs_le] at hN hz' ⊢
      dsimp [N]
      omega
  · have hpow : (2 : ℝ) ^ (k - 1) ≤ (2 : ℝ) ^ k := by
      exact pow_le_pow_right₀ (by norm_num) (Nat.sub_le k 1)
    have hbase : 0 ≤ R + 4 := by linarith
    have hbase1 : (1 : ℝ) ≤ (R + 4) * (2 : ℝ) ^ k := by
      have hp : (1 : ℝ) ≤ (2 : ℝ) ^ k := one_le_pow₀ (by norm_num)
      nlinarith
    have hN₁le' : (N₁ : ℝ) ≤ (R + 4) * (2 : ℝ) ^ k :=
      hN₁le.trans (mul_le_mul_of_nonneg_left hpow hbase)
    dsimp [N]
    push_cast
    nlinarith

theorem measurableSet_wnNice_smallClusters {d : ℕ} {κ : Rd d → ℝ}
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {W : WN d → Ω → ℝ} {H : ℕ → Rd d → Ω → ℝ}
    (hH : IsDyadicRealization κ P W H) (ξ R : ℝ) (q : ℝ≥0∞)
    (k n D : ℕ) :
    MeasurableSet {ω | SmallClusters
      (wnNice (wnGood P H ξ R q (k - 1) n ω)
        (wnGood P H ξ R q k n ω)) D} := by
  have h := wnMeasurable_smallClusters (wnRough P H ξ R q k n)
    (measurableSet_wnRough hH ξ R q k n)
    (wnRough_support_finite P H ξ R q k n) D
  convert h using 1
  ext ω
  have heq : wnNice (wnGood P H ξ R q (k - 1) n ω)
      (wnGood P H ξ R q k n ω) =
      {y | ω ∉ wnRough P H ξ R q k n y} := by
    ext y
    simp [wnRough]
  simp only [Set.mem_ofPred_eq, heq]

theorem measurableSet_wnBadAt {d : ℕ} {κ : Rd d → ℝ}
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {W : WN d → Ω → ℝ} {H : ℕ → Rd d → Ω → ℝ}
    (hH : IsDyadicRealization κ P W H) (ξ R : ℝ) (q : ℝ≥0∞)
    (k n : ℕ) : MeasurableSet (wnBadAt P H ξ R q k n) := by
  have h : MeasurableSet ({ω | ¬ SmallClusters (wnGood P H ξ R q k n ω)
      (wnBadDiameter k)} ∪
    {ω | ¬ SmallClusters (wnGood P H ξ R q (k - 1) n ω)
      (wnBadDiameter (k - 1))} ∪
    {ω | ¬ SmallClusters (wnNice (wnGood P H ξ R q (k - 1) n ω)
      (wnGood P H ξ R q k n ω)) (wnRoughDiameter k)}) := by
    exact ((measurableSet_wnGood_smallClusters hH ξ R q k n _).compl.union
      (measurableSet_wnGood_smallClusters hH ξ R q (k - 1) n _).compl).union
      (measurableSet_wnNice_smallClusters hH ξ R q k n _).compl
  convert h using 1
  ext ω
  simp [wnBadAt, or_assoc]

theorem measurable_wnBadScale {d : ℕ} {κ : Rd d → ℝ}
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {W : WN d → Ω → ℝ} {H : ℕ → Rd d → Ω → ℝ}
    (hH : IsDyadicRealization κ P W H) (ξ R : ℝ) (q : ℝ≥0∞)
    (n : ℕ) : Measurable (wnBadScale P H ξ R q n) := by
  classical
  let f : ℕ → Ω → ℕ := fun k ω => if ω ∈ wnBadAt P H ξ R q k n then k + 1 else 0
  have hf (k : ℕ) : Measurable (f k) :=
    Measurable.ite (measurableSet_wnBadAt hH ξ R q k n) measurable_const measurable_const
  have hs (S : Finset ℕ) : Measurable (fun ω => S.sup fun k => f k ω) := by
    induction S using Finset.induction_on with
    | empty => exact measurable_const
    | @insert k S _ ih =>
      simpa only [Finset.sup_insert] using (hf k).max ih
  change Measurable (fun ω => max 110 ((Finset.Ico 110 n).sup fun k => f k ω))
  exact
    (measurable_const : Measurable fun _ : Ω => (110 : ℕ)).max (hs (Finset.Ico 110 n))

end HigherDimLQGContinuity
