/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.Lemma71IStop
import InteractingSLE.Spec.Sec7.Lemma71EJordan
import InteractingSLE.Spec.Sec7.Lemma71ETop
import InteractingSLE.Spec.Coupling.WholeField2Cap
import InteractingSLE.Spec.Sec6.CondMeanStopPath

/-!
# Lemma 7.1's pocket: the capacity stopping rule of an outer-measurable chart

Packet PROVE-LEMMA71I, part (β), continued. PROVE-LEMMA71H's construction of the capacity-time stopping rule (G6)
asks for the pocket chart "as a measurable function of the outer histories `(x, y) ∈ Hist × Hist`". Here this is
obtained from any chart family that is measurable for `𝓐₀ = σ(A)` (`A ω` the pair of outer histories) in the pointwise
sense of `Lemma71E.exists_measurable_jordanPocketChart`:

* `measurableSet_setOf_mem`, `measurable_indicator_uncurry`: the domain `{(ω, z) : z ∈ C ω}` and the chart
  `(ω, z) ↦ 1_{z ∈ C ω} F ω z` are jointly measurable on `Ω × ℂ` (dense-sequence approach inside the open domain,
  `Lemma71E.exists_measurable_approach`, and continuity of the chart);
* `exists_measurable_factor_prodMap`: **Doob–Dynkin through `A × id`** (`Measurable.exists_eq_measurable_comp` and
  `MeasurableSpace.comap_prodMap`): a `σ(A) ⊗ Borel`-measurable map is `G (A ω, z)` for a measurable `G`;
* `capFamily G M q x c`: the grid capacity `WholeField.hcapHit` of the chart values `G (x, c r)` of the coordinates
  `c r`, `r ≤ q`, lying in the domain `M`; measurable (`measurable_capFamily`) and local (`capFamily_local`);
* **`exists_capacityRule`**: for every `σ(A)`-measurable chart family there are a measurable `G` and a measurable
  domain `M` on `X × ℂ` representing it, and for every level `a` the rule `levelRule (capFamily G M) a` is jointly
  measurable and Galmarino for every coordinate function — the hypotheses `hSm`, `hSg` of the three-curve law
  (`Sec6.Three.ae_condExp_exp_eq_three_of_tendsto`) with `X = Hist × Hist`.

What remains of G6 is the identification along the actual middle curve (`levelRule_eq_of_continuous`): the capacity
family read on `pathCoord γ` is the capacity clock of the mapped segment in the original time (see the handoff).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology Metric
open scoped NNReal ENNReal

namespace InteractingSLE.Sec7.Lemma71I

/-! ### Joint measurability of a random open domain and of a chart on it -/

section Joint

variable {Ω : Type*} [MeasurableSpace Ω] {C : Ω → Set ℂ}

/-- The graph `{(ω, z) : z ∈ C ω}` of a random open set with measurable closed-ball events is measurable. -/
theorem measurableSet_setOf_mem (hCo : ∀ ω, IsOpen (C ω))
    (hCm : ∀ (z : ℂ) (r : ℝ), MeasurableSet {ω | closedBall z r ⊆ C ω}) :
    MeasurableSet {p : Ω × ℂ | p.2 ∈ C p.1} := by
  obtain ⟨e, he⟩ := TopologicalSpace.exists_dense_seq ℂ
  have heq : {p : Ω × ℂ | p.2 ∈ C p.1} = ⋃ k : ℕ, ⋃ m : ℕ,
      {ω | closedBall (e k) (1 / ((m : ℝ) + 1)) ⊆ C ω} ×ˢ ball (e k) (1 / ((m : ℝ) + 1)) := by
    ext ⟨ω, z⟩
    simp only [mem_ofPred_eq, mem_iUnion, mem_prod]
    constructor
    · intro hz
      obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 (hCo ω) z hz
      obtain ⟨m, hm⟩ := exists_nat_one_div_lt (show 0 < ε / 3 by positivity)
      have hr : (0 : ℝ) < 1 / ((m : ℝ) + 1) := by positivity
      obtain ⟨k, hk⟩ := he.exists_dist_lt z hr
      refine ⟨k, m, fun w hw => hball ?_, ?_⟩
      · rw [mem_ball]
        calc dist w z ≤ dist w (e k) + dist (e k) z := dist_triangle _ _ _
          _ ≤ 1 / ((m : ℝ) + 1) + 1 / ((m : ℝ) + 1) := by
              rw [mem_closedBall] at hw
              rw [dist_comm] at hk
              linarith
          _ < ε := by linarith
      · rw [mem_ball]
        exact hk
    · rintro ⟨k, m, hsub, hz⟩
      exact hsub (ball_subset_closedBall hz)
  rw [heq]
  exact MeasurableSet.iUnion fun k => MeasurableSet.iUnion fun m => (hCm _ _).prod measurableSet_ball

/-- **A chart family continuous on a random open domain, measurable at each point, is jointly measurable.** -/
theorem measurable_indicator_uncurry (hCo : ∀ ω, IsOpen (C ω))
    (hCm : ∀ (z : ℂ) (r : ℝ), MeasurableSet {ω | closedBall z r ⊆ C ω}) {F : Ω → ℂ → ℂ}
    (hFc : ∀ ω, ContinuousOn (F ω) (C ω)) (hFm : ∀ z, Measurable ({ω | z ∈ C ω}.indicator fun ω => F ω z)) :
    Measurable ({p : Ω × ℂ | p.2 ∈ C p.1}.indicator fun p => F p.1 p.2) := by
  classical
  set M := {p : Ω × ℂ | p.2 ∈ C p.1} with hMdef
  have hM : MeasurableSet M := measurableSet_setOf_mem hCo hCm
  have hmem : ∀ z, MeasurableSet {ω | z ∈ C ω} := Lemma71E.measurableSet_mem_of_closedBall hCo hCm
  -- an auxiliary open domain on `Ω × ℂ`: `C ω` on `M`, everything off `M`
  set C' : Ω × ℂ → Set ℂ := fun p => if p ∈ M then C p.1 else univ with hC'
  have hC'o : ∀ p, IsOpen (C' p) := fun p => by
    simp only [hC']
    split_ifs
    · exact hCo p.1
    · exact isOpen_univ
  have hC'm : ∀ w, MeasurableSet {p : Ω × ℂ | w ∈ C' p} := fun w => by
    have : {p : Ω × ℂ | w ∈ C' p} = (M ∩ Prod.fst ⁻¹' {ω | w ∈ C ω}) ∪ Mᶜ := by
      ext p
      by_cases hp : p ∈ M <;> simp [hC', hp]
    rw [this]
    exact (hM.inter (measurable_fst (hmem w))).union hM.compl
  have hxC : ∀ p : Ω × ℂ, p.2 ∈ closure (C' p) := fun p => by
    by_cases hp : p ∈ M
    · simp only [hC', hp, ↓reduceIte]
      exact subset_closure hp
    · simp only [hC', hp, ↓reduceIte, closure_univ, mem_univ]
  obtain ⟨e, he⟩ := TopologicalSpace.exists_dense_seq ℂ
  obtain ⟨N, hNm, hNC, hNt⟩ := Lemma71E.exists_measurable_approach hC'o hC'm he measurable_snd hxC
  -- the chart, set to `0` off `M`
  set F' : Ω × ℂ → ℂ → ℂ := fun p w => if p ∈ M then F p.1 w else 0 with hF'
  have hF'm : ∀ w, Measurable ({p : Ω × ℂ | w ∈ C' p}.indicator fun p => F' p w) := fun w => by
    have : ({p : Ω × ℂ | w ∈ C' p}.indicator fun p => F' p w) =
        M.indicator fun p => ({ω | w ∈ C ω}.indicator fun ω => F ω w) p.1 := by
      funext p
      by_cases hp : p ∈ M
      · by_cases hw : w ∈ C p.1
        · simp [hC', hF', hp, hw]
        · simp [hC', hF', hp, hw]
      · simp [hC', hF', hp]
    rw [this]
    exact ((hFm w).comp measurable_fst).indicator hM
  have hterm : ∀ m, Measurable fun p : Ω × ℂ => F' p (e (N m p)) := fun m =>
    Lemma71E.measurable_at_seq (hNm m) (hNC m) hF'm
  refine measurable_of_tendsto_metrizable hterm (tendsto_pi_nhds.2 fun p => ?_)
  by_cases hp : p ∈ M
  · have h1 : Tendsto (fun m => e (N m p)) atTop (𝓝[C p.1] p.2) := by
      have := hNt p
      simp only [hC', hp, ↓reduceIte] at this
      exact this
    have h2 := ((hFc p.1) p.2 hp).tendsto.comp h1
    simp only [indicator_of_mem hp]
    refine h2.congr fun m => ?_
    simp [hF', hp]
  · simp only [indicator_of_notMem hp]
    refine tendsto_const_nhds.congr fun m => ?_
    simp [hF', hp]

end Joint

/-! ### Doob–Dynkin through the outer histories -/

/-- **Doob–Dynkin through `A × id`**: a map on `Ω × W` measurable for `σ(A) ⊗ 𝓦` is `G (A ω, w)` for a measurable
`G` on `Y × W`. -/
theorem exists_measurable_factor_prodMap {Ω Y W Z : Type*} [mY : MeasurableSpace Y] [mW : MeasurableSpace W]
    [MeasurableSpace Z] [StandardBorelSpace Z] [Nonempty Z] {A : Ω → Y} {g : Ω × W → Z}
    (hg : Measurable[(mY.comap A).prod mW] g) : ∃ G : Y × W → Z, Measurable G ∧ ∀ ω w, g (ω, w) = G (A ω, w) := by
  have heq : (mY.comap A).prod mW = (mY.prod mW).comap (Prod.map A id) := by
    rw [MeasurableSpace.comap_prodMap, MeasurableSpace.comap_id]
  rw [heq] at hg
  obtain ⟨G, hG, hgG⟩ := hg.exists_eq_measurable_comp
  exact ⟨G, hG, fun ω w => congrFun hgG (ω, w)⟩

/-- A set measurable for `σ(A) ⊗ 𝓦` is the preimage of a measurable set under `A × id`. -/
theorem exists_measurableSet_prodMap {Ω Y W : Type*} [mY : MeasurableSpace Y] [mW : MeasurableSpace W]
    {A : Ω → Y} {M : Set (Ω × W)} (hM : MeasurableSet[(mY.comap A).prod mW] M) :
    ∃ M' : Set (Y × W), MeasurableSet M' ∧ ∀ ω w, (ω, w) ∈ M ↔ (A ω, w) ∈ M' := by
  have heq : (mY.comap A).prod mW = (mY.prod mW).comap (Prod.map A id) := by
    rw [MeasurableSpace.comap_prodMap, MeasurableSpace.comap_id]
  rw [heq] at hM
  obtain ⟨M', hM', rfl⟩ := hM
  exact ⟨M', hM', fun ω w => Iff.rfl⟩

/-! ### The capacity family -/

section Family

variable {X : Type*}

/-- The chart values `G (x, c r)` of the coordinates `c r`, `r ≤ q`, that lie in the domain `M`. -/
def capSet (G : X × ℂ → ℂ) (M : Set (X × ℂ)) (q : ℚ≥0) (x : X) (c : ℚ≥0 → ℂ) : Set ℂ :=
  {w | ∃ r : ℚ≥0, r ≤ q ∧ (x, c r) ∈ M ∧ G (x, c r) = w}

/-- **The capacity family**: the grid capacity of `capSet`. -/
def capFamily (G : X × ℂ → ℂ) (M : Set (X × ℂ)) (q : ℚ≥0) (x : X) (c : ℚ≥0 → ℂ) : ℝ≥0∞ :=
  WholeField.hcapHit (capSet G M q x c)

/-- The capacity family at `q` depends only on the coordinates at rationals `≤ q`. -/
theorem capFamily_local (G : X × ℂ → ℂ) (M : Set (X × ℂ)) (q : ℚ≥0) (x : X) (c c' : ℚ≥0 → ℂ)
    (h : ∀ r : ℚ≥0, r ≤ q → c r = c' r) : capFamily G M q x c' = capFamily G M q x c := by
  have : capSet G M q x c' = capSet G M q x c := by
    ext w
    constructor
    · rintro ⟨r, hr, hM, rfl⟩
      exact ⟨r, hr, by rw [h r hr]; exact hM, by rw [h r hr]⟩
    · rintro ⟨r, hr, hM, rfl⟩
      exact ⟨r, hr, by rw [← h r hr]; exact hM, by rw [← h r hr]⟩
  rw [capFamily, this, capFamily]

/-- The capacity family is jointly measurable. -/
theorem measurable_capFamily [MeasurableSpace X] {G : X × ℂ → ℂ} {M : Set (X × ℂ)} (hG : Measurable G)
    (hM : MeasurableSet M) (q : ℚ≥0) : Measurable fun z : X × (ℚ≥0 → ℂ) => capFamily G M q z.1 z.2 := by
  have hset : Measurable[_, hittingSigma] fun z : X × (ℚ≥0 → ℂ) => capSet G M q z.1 z.2 := by
    refine @measurable_generateFrom _ (Set ℂ) _ _ _ fun S hS => ?_
    obtain ⟨U, hU, -, rfl⟩ := hS
    have heq : (fun z : X × (ℚ≥0 → ℂ) => capSet G M q z.1 z.2) ⁻¹' {A | (A ∩ U).Nonempty} =
        ⋃ r : ℚ≥0, {z : X × (ℚ≥0 → ℂ) | r ≤ q ∧ (z.1, z.2 r) ∈ M ∧ G (z.1, z.2 r) ∈ U} := by
      ext z
      simp only [mem_preimage, mem_ofPred_eq, mem_iUnion, capSet]
      constructor
      · rintro ⟨w, ⟨r, hr, hM, rfl⟩, hwU⟩
        exact ⟨r, hr, hM, hwU⟩
      · rintro ⟨r, hr, hM, hU⟩
        exact ⟨_, ⟨r, hr, hM, rfl⟩, hU⟩
    rw [heq]
    refine MeasurableSet.iUnion fun r => ?_
    have hp : Measurable fun z : X × (ℚ≥0 → ℂ) => (z.1, z.2 r) :=
      measurable_fst.prodMk ((measurable_pi_apply r).comp measurable_snd)
    exact (MeasurableSet.const (r ≤ q)).inter ((hp hM).inter ((hG.comp hp) hU.measurableSet))
  exact WholeField.measurable_hcapHit.comp hset

end Family

/-! ### The capacity rule of an outer-measurable chart -/

/-- **The capacity stopping rule of an outer-measurable chart family** (G6 of PROVE-LEMMA71H, measurability and
Galmarino parts). Let `A : Ω → X` (for Lemma 7.1: the pair of complete outer histories, `X = Hist × Hist`), and let
`C ω` (open) and `F ω` (continuous on `C ω`) be a random domain and chart, measurable for `σ(A)` in the pointwise
sense (closed-ball events of `C`, the chart at each fixed point). Then `C` and `F` are represented on `X × ℂ` by a
measurable domain `M` and a measurable map `G`, and for every level `a` the rule `levelRule (capFamily G M) a` is
jointly measurable and Galmarino for every coordinate function. -/
theorem exists_capacityRule {X Ω : Type*} [mX : MeasurableSpace X] {A : Ω → X} {C : Ω → Set ℂ}
    {F : Ω → ℂ → ℂ} (hCo : ∀ ω, IsOpen (C ω))
    (hCm : ∀ (z : ℂ) (r : ℝ), MeasurableSet[mX.comap A] {ω | closedBall z r ⊆ C ω})
    (hFc : ∀ ω, ContinuousOn (F ω) (C ω))
    (hFm : ∀ z, Measurable[mX.comap A] ({ω | z ∈ C ω}.indicator fun ω => F ω z)) :
    ∃ (G : X × ℂ → ℂ) (M : Set (X × ℂ)), Measurable G ∧ MeasurableSet M ∧
      (∀ ω z, (A ω, z) ∈ M ↔ z ∈ C ω) ∧ (∀ ω z, z ∈ C ω → G (A ω, z) = F ω z) ∧
      ∀ a : ℝ≥0∞, (Measurable fun p : X × (ℚ≥0 → ℂ) => levelRule (capFamily G M) a p.1 p.2) ∧
        ∀ x c c', (∀ q : ℚ≥0, ((q : ℝ≥0) : ℝ≥0∞) ≤ levelRule (capFamily G M) a x c → c q = c' q) →
          levelRule (capFamily G M) a x c' = levelRule (capFamily G M) a x c := by
  let _ : MeasurableSpace Ω := mX.comap A
  have hMm : MeasurableSet {p : Ω × ℂ | p.2 ∈ C p.1} := measurableSet_setOf_mem hCo hCm
  have hFj := measurable_indicator_uncurry hCo hCm hFc hFm
  obtain ⟨M, hM, hMiff⟩ := exists_measurableSet_prodMap (A := A) hMm
  obtain ⟨G, hG, hGeq⟩ := exists_measurable_factor_prodMap (A := A) hFj
  refine ⟨G, M, hG, hM, fun ω z => (hMiff ω z).symm, fun ω z hz => ?_, fun a => ⟨?_, ?_⟩⟩
  · rw [← hGeq ω z]
    exact indicator_of_mem (show (ω, z) ∈ {p : Ω × ℂ | p.2 ∈ C p.1} from hz) _
  · exact measurable_levelRule (measurable_capFamily hG hM)
  · exact fun x c c' h => levelRule_galmarino (capFamily_local G M) x c c' h

end InteractingSLE.Sec7.Lemma71I
