import MatedCRTHarmonic.GMS3.Recurrence

/-!
# The Green function and the effective resistance

Source: GMS [18] proof of Theorem 1.4 ([18]: `Gr_{τ^ε}(0, 0)/deg(0) = Energy(f⁰_ε)⁻¹`, "by
Dirichlet's principle, [LP16, Exercise 2.13]"): the number of visits to `a`
before `T_Z` is geometric with success probability `P_a[T_Z < T_a^+] = C_eff(a ↔ Z)/deg(a)`.

For a connected graph, a vertex `a` and a finite `U ∋ a` (`W = Uᶜ`):

* `visitBefore G a W n = {X_n = a, n < T_W}` and the **Green function**
  `green G a U = Gr_{T_W}(a, a) = ∑_n P_a[X_n = a, n < T_W]` (the expected number of visits to `a` before
  `T_W`, `green_eq_lintegral`);
* `firstReturn G a W m`: the first return to `a` after time `0` happens at time `m + 1`, before `T_W`;
* `walkLaw_visitBefore_succ` (**renewal identity**):
  `P_a[X_{n+1} = a, n + 1 < T_W] = ∑_{m ≤ n} P_a[first return at m + 1 < T_W] P_a[X_{n−m} = a, n − m < T_W]`
  (Markov property at the deterministic time `m + 1`);
* `green_eq_inv_escProb`: `Gr_{T_W}(a, a) = P_a[T_W < T_a^+]⁻¹`;
* `effRes_eq_green_div_deg` (**effective resistance = Green function / degree**):
  `effRes G a U = Gr_{T_W}(a, a)/deg(a)`;
* `green_ge_of_energy` (the Green function form of Dirichlet's principle, [18] (1.8)):
  `Gr_{T_W}(a, a)/deg(a) ≥ 1/Energy(g)` for every test function `g`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Finset
open scoped ENNReal Topology Classical

namespace MatedCRTHarmonic.GMS3

open Markov Harmonic HarmonicInfinity LFMultigraph

variable {V E : Type*} (G : LFMultigraph V E)

/-- `{X_n = a, n < T_W}`. -/
def visitBefore (a : V) (W : Set V) (n : ℕ) : Set (ℕ → G.State) :=
  {ω | G.stateVertex (ω n) = a ∧ (n : ℕ∞) < hitTime (G.stateVertex ⁻¹' W) ω}

/-- **The Green function** `Gr_{T_W}(a, a) = ∑_n P_a[X_n = a, n < T_W]` (`W = Uᶜ`). -/
def green (a : V) (U : Finset V) : ℝ≥0∞ :=
  ∑' n, G.walkLaw a (visitBefore G a ((U : Set V)ᶜ) n)

/-- The first return to `a` after time `0` happens at time `m + 1`, before `T_W`. -/
def firstReturn (a : V) (W : Set V) (m : ℕ) : Set (ℕ → G.State) :=
  {ω | G.stateVertex (ω 0) ∉ W ∧
    hitTime (G.stateVertex ⁻¹' insert a W) (walkShift 1 ω) = m ∧ G.stateVertex (ω (m + 1)) = a}

theorem measurableSet_stateVertex_eval (n : ℕ) (A : Set V) :
    MeasurableSet {ω : ℕ → G.State | G.stateVertex (ω n) ∈ A} := by
  have hm : Measurable fun ω : ℕ → G.State => ω n := measurable_pi_apply n
  exact hm (MeasurableSet.of_discrete (s := G.stateVertex ⁻¹' A))

theorem measurableSet_visitBefore (a : V) (W : Set V) (n : ℕ) :
    MeasurableSet (visitBefore G a W n) := by
  have h1 : MeasurableSet {ω : ℕ → G.State | G.stateVertex (ω n) = a} :=
    measurableSet_stateVertex_eval G n {a}
  have h2 : MeasurableSet {ω : ℕ → G.State | (n : ℕ∞) < hitTime (G.stateVertex ⁻¹' W) ω} :=
    (measurable_hitTime MeasurableSet.of_discrete) (MeasurableSet.of_discrete (s := Set.Ioi (n : ℕ∞)))
  exact h1.inter h2

/-- `visitBefore` is an event of the vertex path. -/
theorem chainLaw_visitBefore (a : V) (W : Set V) (n : ℕ) (s : G.State) :
    chainLaw G.walkKernel s (visitBefore G a W n) =
      G.walkLaw (G.stateVertex s) (visitBefore G a W n) :=
  chainLaw_vertexEvent (isNNChain_walk G) s
    (Q := fun X => X n = a ∧ (n : ℕ∞) < hitTime W X) (measurableSet_visitBefore G a W n)

theorem measurableSet_firstReturn (a : V) (W : Set V) (m : ℕ) :
    MeasurableSet (firstReturn G a W m) := by
  have h0 : MeasurableSet {ω : ℕ → G.State | G.stateVertex (ω 0) ∉ W} :=
    measurableSet_stateVertex_eval G 0 Wᶜ
  have h1 : MeasurableSet {ω : ℕ → G.State |
      hitTime (G.stateVertex ⁻¹' insert a W) (walkShift 1 ω) = m} :=
    (measurable_hitTime MeasurableSet.of_discrete).comp (measurable_walkShift 1)
      (measurableSet_singleton _)
  have h2 : MeasurableSet {ω : ℕ → G.State | G.stateVertex (ω (m + 1)) = a} :=
    measurableSet_stateVertex_eval G (m + 1) {a}
  exact h0.inter (h1.inter h2)

/-- The first-return event at time `m + 1` only depends on the path up to time `m + 1`. -/
theorem measurableSet_piLE_firstReturn (a : V) (W : Set V) (m : ℕ) :
    MeasurableSet[Filtration.piLE (X := fun _ : ℕ => G.State) (m + 1)] (firstReturn G a W m) := by
  refine measurableSet_piLE_of_forall_eq (measurableSet_firstReturn G a W m) ?_
  rintro ω ω' hω ⟨h0, h1, h2⟩
  refine ⟨by rwa [← hω 0 (Nat.zero_le _)], ?_, by rwa [← hω (m + 1) le_rfl]⟩
  rw [hitTime_eq_coe_iff] at h1 ⊢
  simp only [walkShift_apply] at h1 ⊢
  refine ⟨?_, fun j hj => ?_⟩
  · rw [← hω (1 + m) (by omega)]; exact h1.1
  · rw [← hω (1 + j) (by omega)]; exact h1.2 j hj

/-! ### The renewal identity -/

theorem mem_visitBefore_iff {a : V} {W : Set V} {n : ℕ} {ω : ℕ → G.State} :
    ω ∈ visitBefore G a W n ↔ G.stateVertex (ω n) = a ∧ ∀ j ≤ n, G.stateVertex (ω j) ∉ W := by
  unfold visitBefore
  rw [Set.mem_ofPred_eq, coe_lt_hitTime_iff]
  rfl

/-- The set identity behind the renewal equation (`a ∉ W`). -/
theorem visitBefore_succ_eq {a : V} {W : Set V} (ha : a ∉ W) (n : ℕ) :
    visitBefore G a W (n + 1) =
      ⋃ m ∈ Finset.range (n + 1),
        firstReturn G a W m ∩ walkShift (m + 1) ⁻¹' visitBefore G a W (n - m) := by
  ext ω
  simp only [Set.mem_iUnion, Finset.mem_range, Set.mem_inter_iff, Set.mem_preimage, exists_prop,
    mem_visitBefore_iff, walkShift_apply]
  constructor
  · rintro ⟨hX, hnoW⟩
    have hI : hitTime (G.stateVertex ⁻¹' insert a W) (walkShift 1 ω) ≤ n := by
      refine hitTime_le_of_mem ?_
      show G.stateVertex (walkShift 1 ω n) ∈ insert a W
      rw [walkShift_apply, Nat.add_comm, hX]
      exact Set.mem_insert a W
    obtain ⟨m, hm⟩ := ENat.ne_top_iff_exists.mp (ne_top_of_le_ne_top (ENat.natCast_ne_top n) hI)
    have hmn : m ≤ n := by
      have : (m : ℕ∞) ≤ n := hm ▸ hI
      exact_mod_cast this
    have hmem := hitTime_eq_coe_iff.mp hm.symm
    simp only [walkShift_apply, Set.mem_preimage] at hmem
    have hm1 : G.stateVertex (ω (m + 1)) = a := by
      have h := hmem.1
      rw [Nat.add_comm] at h
      rcases h with h | h
      · exact h
      · exact absurd h (hnoW (m + 1) (by omega))
    refine ⟨m, by omega, ⟨hnoW 0 (Nat.zero_le _), hm.symm, hm1⟩, ?_, fun j hj => ?_⟩
    · rw [show m + 1 + (n - m) = n + 1 by omega]
      exact hX
    · exact hnoW (m + 1 + j) (by omega)
  · rintro ⟨m, hmn, ⟨h0, hm, hm1⟩, hX, hpost⟩
    have hmem := hitTime_eq_coe_iff.mp hm
    simp only [walkShift_apply, Set.mem_preimage] at hmem
    refine ⟨by rwa [show m + 1 + (n - m) = n + 1 by omega] at hX, fun j hj => ?_⟩
    rcases Nat.lt_or_ge (m + 1) j with hlt | hle
    · have := hpost (j - (m + 1)) (by omega)
      rwa [show m + 1 + (j - (m + 1)) = j by omega] at this
    rcases Nat.eq_zero_or_pos j with rfl | hpos
    · exact h0
    rcases Nat.lt_or_ge j (m + 1) with hlt' | hge
    · have := hmem.2 (j - 1) (by omega)
      rw [show 1 + (j - 1) = j by omega] at this
      exact fun hW => this (Set.mem_insert_of_mem a hW)
    · rw [show j = m + 1 by omega, hm1]
      exact ha

/-- **Renewal identity** (Markov property at the deterministic time `m + 1`):
`P_a[X_{n+1} = a, n+1 < T_W] = ∑_{m ≤ n} P_a[first return at m+1 < T_W] · P_a[X_{n−m} = a, n−m < T_W]`. -/
theorem walkLaw_visitBefore_succ {a : V} {W : Set V} (ha : a ∉ W) (n : ℕ) :
    G.walkLaw a (visitBefore G a W (n + 1)) =
      ∑ m ∈ Finset.range (n + 1), G.walkLaw a (firstReturn G a W m) *
        G.walkLaw a (visitBefore G a W (n - m)) := by
  rw [visitBefore_succ_eq G ha n, measure_biUnion_finset]
  · refine Finset.sum_congr rfl fun m _ => ?_
    rw [walkLaw_eq, chainLaw_inter_walkShift_preimage_of_piLE _ _ (m + 1)
      (measurableSet_piLE_firstReturn G a W m) (measurableSet_visitBefore G a W (n - m))]
    have hcongr : ∫⁻ ω in firstReturn G a W m, chainLaw G.walkKernel (ω (m + 1))
        (visitBefore G a W (n - m)) ∂chainLaw G.walkKernel (startState G a) =
        ∫⁻ ω in firstReturn G a W m, G.walkLaw a (visitBefore G a W (n - m))
          ∂chainLaw G.walkKernel (startState G a) := by
      refine setLIntegral_congr_fun (measurableSet_firstReturn G a W m) fun ω hω => ?_
      rw [chainLaw_visitBefore, hω.2.2]
    rw [hcongr, setLIntegral_const, mul_comm, walkLaw_eq]
  · intro m _ m' _ hmm'
    refine Set.disjoint_left.mpr fun ω h h' => hmm' ?_
    have := h.1.2.1.symm.trans h'.1.2.1
    exact_mod_cast this
  · intro m _
    exact (measurableSet_firstReturn G a W m).inter
      ((measurable_walkShift (m + 1)) (measurableSet_visitBefore G a W (n - m)))

theorem walkLaw_visitBefore_zero {a : V} {W : Set V} (ha : a ∉ W) :
    G.walkLaw a (visitBefore G a W 0) = 1 := by
  refine le_antisymm prob_le_one ?_
  rw [← measure_univ (μ := G.walkLaw a)]
  refine (measure_congr ?_).ge
  filter_upwards [chainLaw_ae_start G.walkKernel (startState G a)] with ω h0
  simp only [Set.mem_univ, eq_iff_iff, iff_true]
  rw [mem_visitBefore_iff]
  refine ⟨by rw [h0]; rfl, fun j hj => ?_⟩
  rw [Nat.le_zero.mp hj, h0]
  exact ha

/-! ### The first-return probabilities -/

/-- `P_y(X_{T_I} ∈ {a}ᶜ) = P_y(X_{T_I} ∈ W)` for `I = {a} ∪ W`, `a ∉ W`. -/
theorem hitDist_compl_singleton_eq {a : V} {W : Set V} (ha : a ∉ W) (y : V) :
    hitDist G (insert a W) y ({a} : Set V)ᶜ = hitDist G (insert a W) y W := by
  rw [hitDist_inter_self G _ ({a} : Set V)ᶜ, hitDist_inter_self G _ W]
  congr 1
  ext x
  simp only [Set.mem_inter_iff, Set.mem_insert_iff, Set.mem_compl_iff, Set.mem_singleton_iff]
  constructor
  · rintro ⟨h | h, h'⟩
    · exact absurd h h'
    · exact ⟨Or.inr h, h⟩
  · rintro ⟨-, h⟩
    refine ⟨Or.inr h, ?_⟩
    rintro rfl
    exact ha h

theorem hitDist_singleton_add_eq_one (hconn : G.adj.Connected) {a : V} {U : Finset V}
    (haU : a ∈ U) (y : V) :
    hitDist G (insert a ((U : Set V)ᶜ)) y {a} + hitDist G (insert a ((U : Set V)ᶜ)) y ((U : Set V)ᶜ) = 1 := by
  have h := hitDist_add_compl_eq_one G (walkLaw_hitTime_insert_ne_top G hconn (U := U) (a := a) y) {a}
  rwa [hitDist_compl_singleton_eq G (by simpa using haU)] at h

/-- The union of the first-return events. -/
theorem iUnion_firstReturn (a : V) (W : Set V) :
    ⋃ m, firstReturn G a W m = {ω | G.stateVertex (ω 0) ∉ W} ∩
      walkShift 1 ⁻¹' hitEvent (G.stateVertex ⁻¹' insert a W) (G.stateVertex ⁻¹' {a}) := by
  ext ω
  simp only [Set.mem_iUnion, Set.mem_inter_iff, Set.mem_preimage, Set.mem_ofPred_eq, hitEvent]
  constructor
  · rintro ⟨m, h0, hm, ha⟩
    refine ⟨h0, by rw [hm]; exact ENat.natCast_ne_top m, ?_⟩
    rw [stopState_eq_of_eq hm, walkShift_apply, Nat.add_comm]
    exact ha
  · rintro ⟨h0, hT, ha⟩
    obtain ⟨m, hm⟩ := ENat.ne_top_iff_exists.mp hT
    refine ⟨m, h0, hm.symm, ?_⟩
    rw [stopState_eq_of_eq hm.symm, walkShift_apply, Nat.add_comm] at ha
    exact ha

/-- **The first-return probabilities and the escape probability add up to one.** -/
theorem tsum_firstReturn_add_escProb (hconn : G.adj.Connected) {a : V} {U : Finset V}
    (haU : a ∈ U) :
    ∑' m, G.walkLaw a (firstReturn G a ((U : Set V)ᶜ) m) + escProb G a ((U : Set V)ᶜ) = 1 := by
  set W : Set V := (U : Set V)ᶜ
  have haW : a ∉ W := by simpa [W] using haU
  rw [← measure_iUnion (fun m m' hmm' => Set.disjoint_left.mpr fun ω h h' =>
      hmm' (by exact_mod_cast h.2.1.symm.trans h'.2.1))
    (measurableSet_firstReturn G a W), iUnion_firstReturn]
  have hae : G.walkLaw a ({ω | G.stateVertex (ω 0) ∉ W} ∩
      walkShift 1 ⁻¹' hitEvent (G.stateVertex ⁻¹' insert a W) (G.stateVertex ⁻¹' {a})) =
      G.walkLaw a (walkShift 1 ⁻¹' hitEvent (G.stateVertex ⁻¹' insert a W)
        (G.stateVertex ⁻¹' {a})) := by
    refine measure_congr ?_
    filter_upwards [chainLaw_ae_start G.walkKernel (startState G a)] with ω h0
    simp only [Set.mem_inter_iff, Set.mem_ofPred_eq, eq_iff_iff, and_iff_right_iff_imp]
    intro _
    rw [h0]
    exact haW
  rw [hae, walkLaw_walkShift_one G a (measurableSet_hitEvent _ _), escProb_eq_avg, ← mul_add,
    ← Finset.sum_add_distrib]
  simp_rw [hitDist_dartState]
  rw [Finset.sum_congr rfl fun d _ => hitDist_singleton_add_eq_one G hconn haU (G.dtgt d),
    Finset.sum_const, nsmul_eq_mul, mul_one]
  exact ENNReal.inv_mul_cancel (Nat.cast_ne_zero.mpr (deg_ne_zero G a)) (ENNReal.natCast_ne_top _)

/-! ### The Green function -/

/-- A finite double-sum bound for the Cauchy product. -/
theorem sum_range_sum_range_mul_le (f g : ℕ → ℝ≥0∞) (k : ℕ) :
    ∑ n ∈ Finset.range k, ∑ m ∈ Finset.range (n + 1), f m * g (n - m) ≤
      (∑ m ∈ Finset.range k, f m) * ∑ j ∈ Finset.range k, g j := by
  rw [Finset.sum_comm' (t' := Finset.range k) (s' := fun m => Finset.Ico m k)
    (fun n m => by simp only [Finset.mem_range, Finset.mem_Ico]; omega), Finset.sum_mul]
  refine Finset.sum_le_sum fun m hm => ?_
  rw [← Finset.mul_sum]
  gcongr
  rw [Finset.sum_Ico_eq_sum_range]
  simp only [Nat.add_sub_cancel_left]
  exact Finset.sum_le_sum_of_subset (Finset.range_subset_range.mpr (Nat.sub_le k m))

/-- The reverse finite bound for the Cauchy product. -/
theorem mul_sum_range_le_sum_range_sum_range (f g : ℕ → ℝ≥0∞) (N : ℕ) :
    (∑ m ∈ Finset.range N, f m) * ∑ j ∈ Finset.range N, g j ≤
      ∑ n ∈ Finset.range (2 * N), ∑ m ∈ Finset.range (n + 1), f m * g (n - m) := by
  rw [Finset.sum_comm' (t' := Finset.range (2 * N)) (s' := fun m => Finset.Ico m (2 * N))
    (fun n m => by simp only [Finset.mem_range, Finset.mem_Ico]; omega), Finset.sum_mul]
  calc ∑ m ∈ Finset.range N, f m * ∑ j ∈ Finset.range N, g j
      ≤ ∑ m ∈ Finset.range N, ∑ n ∈ Finset.Ico m (2 * N), f m * g (n - m) := by
        refine Finset.sum_le_sum fun m hm => ?_
        rw [← Finset.mul_sum]
        gcongr
        rw [Finset.sum_Ico_eq_sum_range]
        simp only [Nat.add_sub_cancel_left]
        exact Finset.sum_le_sum_of_subset (Finset.range_subset_range.mpr
          (by rw [Finset.mem_range] at hm; omega))
    _ ≤ ∑ m ∈ Finset.range (2 * N), ∑ n ∈ Finset.Ico m (2 * N), f m * g (n - m) :=
        Finset.sum_le_sum_of_subset (Finset.range_subset_range.mpr (by omega))

/-- **The Green function is the inverse escape probability**:
`Gr_{T_W}(a, a) = P_a[T_W < T_a^+]⁻¹` (`W = Uᶜ`). -/
theorem green_eq_inv_escProb (hconn : G.adj.Connected) {a : V} {U : Finset V} (haU : a ∈ U) :
    green G a U = (escProb G a ((U : Set V)ᶜ))⁻¹ := by
  set W : Set V := (U : Set V)ᶜ
  have haW : a ∉ W := by simpa [W] using haU
  set p : ℕ → ℝ≥0∞ := fun n => G.walkLaw a (visitBefore G a W n) with hp
  set r : ℕ → ℝ≥0∞ := fun m => G.walkLaw a (firstReturn G a W m) with hr
  set e := escProb G a W
  have hRe : (∑' m, r m) + e = 1 := tsum_firstReturn_add_escProb G hconn haU
  have hp0 : p 0 = 1 := walkLaw_visitBefore_zero G haW
  have hrec : ∀ n, p (n + 1) = ∑ m ∈ Finset.range (n + 1), r m * p (n - m) :=
    fun n => walkLaw_visitBefore_succ G haW n
  have hgreen : green G a U = ∑' n, p n := rfl
  have hRfin' : (∑' m, r m) ≠ ⊤ := ne_top_of_le_ne_top ENNReal.one_ne_top (hRe ▸ le_self_add)
  -- partial sums
  have hsplit : ∀ k, ∑ n ∈ Finset.range (k + 1), p n =
      1 + ∑ n ∈ Finset.range k, ∑ m ∈ Finset.range (n + 1), r m * p (n - m) := by
    intro k
    rw [Finset.sum_range_succ', add_comm, hp0]
    simp_rw [hrec]
  -- truncation: `Gₖ · e ≤ 1`
  have htrunc : ∀ k, (∑ n ∈ Finset.range k, p n) * e ≤ 1 := by
    intro k
    cases k with
    | zero => simp
    | succ k =>
      have hGfin : ∑ n ∈ Finset.range (k + 1), p n ≠ ⊤ :=
        ENNReal.sum_ne_top.mpr fun n _ => measure_ne_top _ _
      have hle : ∑ n ∈ Finset.range (k + 1), p n ≤
          1 + (∑' m, r m) * ∑ n ∈ Finset.range (k + 1), p n := by
        rw [hsplit k]
        calc 1 + ∑ n ∈ Finset.range k, ∑ m ∈ Finset.range (n + 1), r m * p (n - m)
            ≤ 1 + (∑ m ∈ Finset.range k, r m) * ∑ j ∈ Finset.range k, p j := by
              gcongr; exact sum_range_sum_range_mul_le r p k
          _ ≤ 1 + (∑' m, r m) * (1 + ∑ n ∈ Finset.range k, ∑ m ∈ Finset.range (n + 1),
                r m * p (n - m)) := by
              gcongr
              · exact ENNReal.sum_le_tsum _
              · rw [← hsplit k]
                exact Finset.sum_le_sum_of_subset (Finset.range_subset_range.mpr (Nat.le_succ k))
      set Gk := ∑ n ∈ Finset.range (k + 1), p n
      have hRfin : (∑' m, r m) * Gk ≠ ⊤ := ENNReal.mul_ne_top hRfin' hGfin
      have : (∑' m, r m) * Gk + Gk * e ≤ (∑' m, r m) * Gk + 1 := by
        calc (∑' m, r m) * Gk + Gk * e = Gk * ((∑' m, r m) + e) := by ring
          _ = Gk := by rw [hRe, mul_one]
          _ ≤ 1 + (∑' m, r m) * Gk := hle
          _ = (∑' m, r m) * Gk + 1 := add_comm _ _
      exact (ENNReal.add_le_add_iff_left hRfin).mp this
  have hle1 : (∑' n, p n) * e ≤ 1 := by
    rw [ENNReal.tsum_eq_iSup_nat, ENNReal.iSup_mul]
    exact iSup_le htrunc
  -- lower bound: `Gr ≥ 1 + R Gr`
  have hlow : 1 + (∑' m, r m) * ∑' n, p n ≤ ∑' n, p n := by
    have hmono : Monotone fun N => ∑ n ∈ Finset.range N, p n :=
      fun i j hij => Finset.sum_le_sum_of_subset (Finset.range_subset_range.mpr hij)
    have hmono' : Monotone fun N => ∑ n ∈ Finset.range N, r n :=
      fun i j hij => Finset.sum_le_sum_of_subset (Finset.range_subset_range.mpr hij)
    have hN : ∀ N, 1 + (∑ m ∈ Finset.range N, r m) * ∑ n ∈ Finset.range N, p n ≤ ∑' n, p n := by
      intro N
      calc 1 + (∑ m ∈ Finset.range N, r m) * ∑ n ∈ Finset.range N, p n
          ≤ 1 + ∑ n ∈ Finset.range (2 * N), ∑ m ∈ Finset.range (n + 1), r m * p (n - m) := by
            gcongr; exact mul_sum_range_le_sum_range_sum_range r p N
        _ = ∑ n ∈ Finset.range (2 * N + 1), p n := (hsplit (2 * N)).symm
        _ ≤ ∑' n, p n := ENNReal.sum_le_tsum _
    conv_lhs => rw [ENNReal.tsum_eq_iSup_nat (f := r), ENNReal.tsum_eq_iSup_nat (f := p),
      ENNReal.iSup_mul]
    simp_rw [ENNReal.mul_iSup]
    rw [ENNReal.add_iSup]
    refine iSup_le fun N => ?_
    rw [ENNReal.add_iSup]
    refine iSup_le fun M => ?_
    calc 1 + (∑ m ∈ Finset.range N, r m) * ∑ n ∈ Finset.range M, p n
        ≤ 1 + (∑ m ∈ Finset.range (max N M), r m) * ∑ n ∈ Finset.range (max N M), p n := by
          gcongr
          · exact le_max_left N M
          · exact le_max_right N M
      _ ≤ ∑' n, p n := hN _
  rw [hgreen]
  by_cases he : e = 0
  · rw [he, ENNReal.inv_zero]
    rw [he, add_zero] at hRe
    rw [hRe, one_mul] at hlow
    by_contra hne
    have h1 : ∑' n, p n < ∑' n, p n + 1 := ENNReal.lt_add_right hne one_ne_zero
    have h2 : ∑' n, p n + 1 ≤ ∑' n, p n := by rw [add_comm]; exact hlow
    exact absurd (h1.trans_le h2) (lt_irrefl _)
  · have hfin : ∑' n, p n ≠ ⊤ := by
      intro htop
      rw [htop, ENNReal.top_mul he] at hle1
      exact absurd hle1 (by simp)
    have hRfin : (∑' m, r m) * ∑' n, p n ≠ ⊤ := ENNReal.mul_ne_top hRfin' hfin
    have hge1 : 1 ≤ (∑' n, p n) * e := by
      have h1 : (∑' m, r m) * (∑' n, p n) + 1 ≤ (∑' m, r m) * (∑' n, p n) + (∑' n, p n) * e := by
        calc (∑' m, r m) * (∑' n, p n) + 1 = 1 + (∑' m, r m) * ∑' n, p n := add_comm _ _
          _ ≤ ∑' n, p n := hlow
          _ = (∑' n, p n) * ((∑' m, r m) + e) := by rw [hRe, mul_one]
          _ = (∑' m, r m) * (∑' n, p n) + (∑' n, p n) * e := by ring
      exact (ENNReal.add_le_add_iff_left hRfin).mp h1
    exact ENNReal.eq_inv_of_mul_eq_one_left (le_antisymm hle1 hge1)

/-- **Effective resistance = Green function / degree** ([18]; Details (c5)). -/
theorem effRes_eq_green_div_deg (hconn : G.adj.Connected) {a : V} {U : Finset V} (haU : a ∈ U) :
    effRes G a U = (green G a U).toReal / G.deg a := by
  rw [green_eq_inv_escProb G hconn haU, ENNReal.toReal_inv]
  unfold effRes effCond
  rw [mul_inv, div_eq_mul_inv, mul_comm]

/-- **Green function form of Dirichlet's principle** ([18] (1.8)): for every test function `g`
(`g(a) = 1`, `g = 0` off `U`), `Gr_{T_{Uᶜ}}(a, a) ≥ deg(a) / Energy(g)`. -/
theorem green_ge_of_energy (hconn : G.adj.Connected) {a : V} {U : Finset V} (haU : a ∈ U)
    {g : V → ℝ} (hga : g a = 1) (hg : ∀ x ∉ U, g x = 0) :
    ENNReal.ofReal (G.deg a / energy G (nbhd G U) g) ≤ green G a U := by
  rw [green_eq_inv_escProb G hconn haU]
  have hdeg : (0 : ℝ) < G.deg a := Nat.cast_pos.mpr (Nat.pos_of_ne_zero (deg_ne_zero G a))
  rcases (energy_nonneg G (nbhd G U) g).eq_or_lt with h0 | hpos
  · rw [← h0, div_zero, ENNReal.ofReal_zero]
    exact bot_le
  have hesc : escProb G a ((U : Set V)ᶜ) ≤ ENNReal.ofReal (energy G (nbhd G U) g / G.deg a) := by
    rw [← ENNReal.ofReal_toReal (escProb_ne_top G a _)]
    refine ENNReal.ofReal_le_ofReal ?_
    rw [le_div_iff₀ hdeg, mul_comm]
    exact effCond_le_energy G hconn haU hga hg
  calc ENNReal.ofReal (G.deg a / energy G (nbhd G U) g)
      = (ENNReal.ofReal (energy G (nbhd G U) g / G.deg a))⁻¹ := by
        rw [← ENNReal.ofReal_inv_of_pos (div_pos hpos hdeg), inv_div]
    _ ≤ (escProb G a ((U : Set V)ᶜ))⁻¹ := ENNReal.inv_le_inv.mpr hesc

/-- Dirichlet's principle with an energy bound: if `Energy(g) ≤ B` for a test function `g`, then
`Gr_{T_{Uᶜ}}(a, a) ≥ deg(a)/B`. -/
theorem green_ge_of_energy_le (hconn : G.adj.Connected) {a : V} {U : Finset V} (haU : a ∈ U)
    {g : V → ℝ} (hga : g a = 1) (hg : ∀ x ∉ U, g x = 0) {B : ℝ}
    (hB : energy G (nbhd G U) g ≤ B) : ENNReal.ofReal (G.deg a / B) ≤ green G a U := by
  have hB0 : 0 ≤ B := (energy_nonneg G _ g).trans hB
  rcases hB0.eq_or_lt with h0 | hpos
  · rw [← h0, div_zero, ENNReal.ofReal_zero]
    exact bot_le
  rw [green_eq_inv_escProb G hconn haU]
  have hdeg : (0 : ℝ) < G.deg a := Nat.cast_pos.mpr (Nat.pos_of_ne_zero (deg_ne_zero G a))
  have hesc : escProb G a ((U : Set V)ᶜ) ≤ ENNReal.ofReal (B / G.deg a) := by
    rw [← ENNReal.ofReal_toReal (escProb_ne_top G a _)]
    refine ENNReal.ofReal_le_ofReal ?_
    rw [le_div_iff₀ hdeg, mul_comm]
    exact (effCond_le_energy G hconn haU hga hg).trans hB
  calc ENNReal.ofReal (G.deg a / B) = (ENNReal.ofReal (B / G.deg a))⁻¹ := by
        rw [← ENNReal.ofReal_inv_of_pos (div_pos hpos hdeg), inv_div]
    _ ≤ (escProb G a ((U : Set V)ᶜ))⁻¹ := ENNReal.inv_le_inv.mpr hesc

/-- `Gr_{T_W}(a, a)` is the expected number of visits to `a` before `T_W`. -/
theorem green_eq_lintegral (a : V) (U : Finset V) :
    green G a U = ∫⁻ ω, ∑' n, (visitBefore G a ((U : Set V)ᶜ) n).indicator (fun _ => (1 : ℝ≥0∞)) ω
      ∂G.walkLaw a := by
  rw [lintegral_tsum fun n => ((measurable_const (a := (1 : ℝ≥0∞))).indicator
    (measurableSet_visitBefore G a _ n)).aemeasurable]
  unfold green
  congr 1
  funext n
  rw [lintegral_indicator_const (measurableSet_visitBefore G a _ n), one_mul]

end MatedCRTHarmonic.GMS3
