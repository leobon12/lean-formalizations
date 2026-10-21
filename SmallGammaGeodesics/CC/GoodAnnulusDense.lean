import LQGMetric.Papers.GM.S3.GoodAnnulusMeas3

/-!
# Regularization of a two-point function along a dense sequence (track CC, packet CC9a)

Auxiliary for [3] Lemma 3.8 (CC0, Details D14; `CC/GoodAnnulusMeas.lean`). The transported metric
`D^ϕ(·,·;A)` is a function of `h|_A` only through its values at the pairs of a countable dense
subset of `A` (locality is a statement about countably many coordinates). To read the good-annulus
event off these countably many values, we use the *upper regularization along the sequence*
`q : ℕ → ℂ`,

`denseUp q x u v = inf_n sup {x(i,j) : |q i − u| < 1/(n+1), |q j − v| < 1/(n+1)}`,

for `x : ℕ × ℕ → [0,∞]`. Its properties (own elementary arguments):
* `measurable_denseUp`: it is jointly Borel in `(x, u, v)`;
* `denseUp_lt_of_lt`: it is upper semicontinuous in `v`; hence `iInf_denseUp_eq`: on an open
  subset of `U` (where `q` is dense) its infimum is the infimum over the sequence points, and
  `bdFun_denseUp`: GM's `bdFun` of it is the countable formula `denseBd`, which is Borel in
  `(x, u)` (`measurable_denseBd`);
* `denseUp_eq`: if `J` is continuous on `U × U` (`U` open, `q` dense in `U`), the regularization
  of `x = J(q ·, q ·)` is `J` on `U × U`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set Filter Metric Topology
open scoped ENNReal

namespace SmallGammaGeodesics.CC

open LQGMetric

/-- the level-`n` supremum of `x` over the sequence pairs near `(u, v)` -/
def denseSup (q : ℕ → ℂ) (x : ℕ × ℕ → ℝ≥0∞) (n : ℕ) (u v : ℂ) : ℝ≥0∞ :=
  ⨆ (i : ℕ) (j : ℕ) (_ : ‖q i - u‖ < 1 / ((n : ℝ) + 1) ∧ ‖q j - v‖ < 1 / ((n : ℝ) + 1)),
    x (i, j)

/-- the upper regularization of `x : ℕ × ℕ → [0,∞]` along the sequence `q` -/
def denseUp (q : ℕ → ℂ) (x : ℕ × ℕ → ℝ≥0∞) (u v : ℂ) : ℝ≥0∞ :=
  ⨅ n : ℕ, denseSup q x n u v

/-- the countable formula for `GM.bdFun (denseUp q x) U u` (`bdFun_denseUp`) -/
def denseBd (q : ℕ → ℂ) (U : Set ℂ) (x : ℕ × ℕ → ℝ≥0∞) (u : ℂ) : ℝ≥0∞ :=
  ⨆ n : ℕ, ⨅ (k : ℕ) (_ : q k ∈ GM.nearFrontier U (1 / ((n : ℝ) + 1))), denseUp q x u (q k)

variable {q : ℕ → ℂ}

/-! ## Measurability -/

theorem measurable_denseSup (q : ℕ → ℂ) (n : ℕ) :
    Measurable fun p : (ℕ × ℕ → ℝ≥0∞) × ℂ × ℂ => denseSup q p.1 n p.2.1 p.2.2 := by
  classical
  unfold denseSup
  refine Measurable.iSup fun i => Measurable.iSup fun j => ?_
  simp only [iSup_eq_if]
  refine Measurable.ite ?_ ((measurable_pi_apply (i, j)).comp measurable_fst) measurable_const
  have ho : IsOpen {p : (ℕ × ℕ → ℝ≥0∞) × ℂ × ℂ |
      ‖q i - p.2.1‖ < 1 / ((n : ℝ) + 1) ∧ ‖q j - p.2.2‖ < 1 / ((n : ℝ) + 1)} :=
    (isOpen_lt (continuous_const.sub continuous_snd.fst).norm continuous_const).inter
      (isOpen_lt (continuous_const.sub continuous_snd.snd).norm continuous_const)
  exact ho.measurableSet

/-- the regularization is jointly Borel in `(x, u, v)` -/
theorem measurable_denseUp (q : ℕ → ℂ) :
    Measurable fun p : (ℕ × ℕ → ℝ≥0∞) × ℂ × ℂ => denseUp q p.1 p.2.1 p.2.2 :=
  Measurable.iInf fun n => measurable_denseSup q n

/-- composition form of `measurable_denseUp` -/
theorem measurable_denseUp_comp {X : Type*} [MeasurableSpace X] (q : ℕ → ℂ)
    {x : X → ℕ × ℕ → ℝ≥0∞} {u v : X → ℂ} (hx : Measurable x) (hu : Measurable u)
    (hv : Measurable v) : Measurable fun a => denseUp q (x a) (u a) (v a) :=
  Measurable.comp (g := fun p : (ℕ × ℕ → ℝ≥0∞) × ℂ × ℂ => denseUp q p.1 p.2.1 p.2.2)
    (f := fun a => (x a, u a, v a)) (measurable_denseUp q) (hx.prodMk (hu.prodMk hv))

/-- the countable boundary formula is jointly Borel in `(x, u)` -/
theorem measurable_denseBd (q : ℕ → ℂ) (U : Set ℂ) :
    Measurable fun p : (ℕ × ℕ → ℝ≥0∞) × ℂ => denseBd q U p.1 p.2 := by
  refine Measurable.iSup fun n => Measurable.iInf fun k => ?_
  by_cases hk : q k ∈ GM.nearFrontier U (1 / ((n : ℝ) + 1))
  · have e : (fun p : (ℕ × ℕ → ℝ≥0∞) × ℂ =>
        ⨅ (_ : q k ∈ GM.nearFrontier U (1 / ((n : ℝ) + 1))), denseUp q p.1 p.2 (q k)) =
        fun p => denseUp q p.1 p.2 (q k) := funext fun p => iInf_pos hk
    rw [e]
    exact measurable_denseUp_comp q measurable_fst measurable_snd measurable_const
  · have e : (fun p : (ℕ × ℕ → ℝ≥0∞) × ℂ =>
        ⨅ (_ : q k ∈ GM.nearFrontier U (1 / ((n : ℝ) + 1))), denseUp q p.1 p.2 (q k)) =
        fun _ => ⊤ := funext fun p => iInf_neg hk
    rw [e]
    exact measurable_const

/-! ## Constant multiples -/

/-- the regularization commutes with multiplication by a constant `k ∈ (0, ∞)` -/
theorem denseUp_const_mul {k : ℝ≥0∞} (hk0 : k ≠ 0) (hkt : k ≠ ⊤) (q : ℕ → ℂ)
    (x : ℕ × ℕ → ℝ≥0∞) (u v : ℂ) :
    denseUp q (fun p => k * x p) u v = k * denseUp q x u v := by
  simp only [denseUp, denseSup, ENNReal.mul_iInf_of_ne hk0 hkt, ENNReal.mul_iSup]

/-! ## Upper semicontinuity in the second variable -/

lemma denseSup_mono_of {x : ℕ × ℕ → ℝ≥0∞} {n m : ℕ} {u v v' : ℂ}
    (hmn : 1 / ((m : ℝ) + 1) ≤ 1 / ((n : ℝ) + 1))
    (hv : ∀ y : ℂ, ‖y - v'‖ < 1 / ((m : ℝ) + 1) → ‖y - v‖ < 1 / ((n : ℝ) + 1)) :
    denseSup q x m u v' ≤ denseSup q x n u v := by
  refine iSup_le fun i => iSup_le fun j => iSup_le fun hij => ?_
  exact le_iSup_of_le i (le_iSup_of_le j (le_iSup_of_le ⟨hij.1.trans_le hmn, hv _ hij.2⟩ le_rfl))

/-- **upper semicontinuity**: `denseUp q x u · < b` near any point where it is `< b` -/
theorem denseUp_lt_of_lt {x : ℕ × ℕ → ℝ≥0∞} {u v : ℂ} {b : ℝ≥0∞} (hb : denseUp q x u v < b) :
    ∃ δ > 0, ∀ v' : ℂ, ‖v' - v‖ < δ → denseUp q x u v' < b := by
  obtain ⟨n, hn⟩ := iInf_lt_iff.1 hb
  refine ⟨1 / (2 * ((n : ℝ) + 1)), by positivity, fun v' hv' => ?_⟩
  refine lt_of_le_of_lt ((iInf_le _ (2 * n + 1)).trans (denseSup_mono_of ?_ ?_)) hn
  · push_cast
    gcongr
    linarith
  · intro y hy
    push_cast at hy
    have e : (1 : ℝ) / (2 * (n : ℝ) + 1 + 1) = 1 / (2 * ((n : ℝ) + 1)) := by ring_nf
    rw [e] at hy
    calc ‖y - v‖ ≤ ‖y - v'‖ + ‖v' - v‖ := norm_sub_le_norm_sub_add_norm_sub y v' v
      _ < 1 / (2 * ((n : ℝ) + 1)) + 1 / (2 * ((n : ℝ) + 1)) := add_lt_add hy hv'
      _ = 1 / ((n : ℝ) + 1) := by field_simp; ring

/-- on an open subset `O` of the set `U` where `q` is dense, the infimum of `denseUp q x u` over
`O` is its infimum over the sequence points in `O` -/
theorem iInf_denseUp_eq {U O : Set ℂ} (hqd : U ⊆ closure (range q)) (hO : IsOpen O)
    (hOU : O ⊆ U) (x : ℕ × ℕ → ℝ≥0∞) (u : ℂ) :
    ⨅ y ∈ O, denseUp q x u y = ⨅ (k : ℕ) (_ : q k ∈ O), denseUp q x u (q k) := by
  refine le_antisymm (le_iInf₂ fun k hk => iInf₂_le (q k) hk) (le_iInf₂ fun y hy => ?_)
  refine le_of_forall_gt fun b hb => ?_
  obtain ⟨δ, hδ, hδ'⟩ := denseUp_lt_of_lt hb
  have hyc : y ∈ closure (range q) := hqd (hOU hy)
  obtain ⟨_, ⟨hyO, hyδ⟩, ⟨k, rfl⟩⟩ := mem_closure_iff.1 hyc (O ∩ ball y δ)
    (hO.inter isOpen_ball) ⟨hy, mem_ball_self hδ⟩
  refine lt_of_le_of_lt (iInf₂_le k hyO) (hδ' _ ?_)
  rw [← dist_eq_norm]
  exact hyδ

lemma isOpen_nearFrontier {U : Set ℂ} (hU : IsOpen U) (δ : ℝ) :
    IsOpen (GM.nearFrontier U δ) :=
  hU.inter (isOpen_lt (continuous_infDist_pt _) continuous_const)

lemma nearFrontier_subset (U : Set ℂ) (δ : ℝ) : GM.nearFrontier U δ ⊆ U := fun _ hy => hy.1

/-- GM's `bdFun` of the regularization is the countable formula `denseBd` -/
theorem bdFun_denseUp {U : Set ℂ} (hU : IsOpen U) (hqd : U ⊆ closure (range q))
    (x : ℕ × ℕ → ℝ≥0∞) (u : ℂ) : GM.bdFun (denseUp q x) U u = denseBd q U x u := by
  unfold GM.bdFun denseBd
  refine iSup_congr fun n => ?_
  exact iInf_denseUp_eq hqd (isOpen_nearFrontier hU _) (nearFrontier_subset U _) x u

/-! ## The regularization of a continuous function is the function -/

/-- if `J` is continuous on `U × U` (`U` open, `q` dense in `U`), the regularization of its values
at the sequence pairs is `J` on `U × U` -/
theorem denseUp_eq {U : Set ℂ} (hU : IsOpen U) (hqd : U ⊆ closure (range q))
    {J : ℂ → ℂ → ℝ≥0∞} (hJ : ContinuousOn (fun p : ℂ × ℂ => J p.1 p.2) (U ×ˢ U)) {u v : ℂ}
    (hu : u ∈ U) (hv : v ∈ U) : denseUp q (fun ij => J (q ij.1) (q ij.2)) u v = J u v := by
  have hca : ContinuousAt (fun p : ℂ × ℂ => J p.1 p.2) (u, v) :=
    hJ.continuousAt ((hU.prod hU).mem_nhds ⟨hu, hv⟩)
  -- points of the sequence close to a point of `U`
  have hclose : ∀ w ∈ U, ∀ ε > 0, ∃ i, ‖q i - w‖ < ε := fun w hw ε hε => by
    obtain ⟨_, hb, ⟨i, rfl⟩⟩ := mem_closure_iff.1 (hqd hw) (ball w ε) isOpen_ball
      (mem_ball_self hε)
    exact ⟨i, by rw [← dist_eq_norm]; exact hb⟩
  -- a neighbourhood of `(u, v)` in product form
  have hnbhd : ∀ s ∈ 𝓝 (J u v), ∃ δ > 0, ∀ u' v' : ℂ, ‖u' - u‖ < δ → ‖v' - v‖ < δ →
      J u' v' ∈ s := fun s hs => by
    obtain ⟨δ, hδ, hδ'⟩ := Metric.mem_nhds_iff.1 (hca hs)
    refine ⟨δ, hδ, fun u' v' h1 h2 => ?_⟩
    have hmem : ((u', v') : ℂ × ℂ) ∈ ball (u, v) δ := by
      rw [mem_ball, Prod.dist_eq, dist_eq_norm, dist_eq_norm]
      exact max_lt h1 h2
    exact hδ' hmem
  refine le_antisymm ?_ ?_
  · refine le_of_forall_gt fun c hc => ?_
    obtain ⟨c', hc1, hc2⟩ := exists_between hc
    obtain ⟨δ, hδ, hδ'⟩ := hnbhd (Iio c') (Iio_mem_nhds hc1)
    obtain ⟨n, hn⟩ := exists_nat_one_div_lt hδ
    refine lt_of_le_of_lt ((iInf_le _ n).trans ?_) hc2
    refine iSup_le fun i => iSup_le fun j => iSup_le fun hij => ?_
    exact (hδ' (q i) (q j) (hij.1.trans hn) (hij.2.trans hn)).le
  · refine le_iInf fun n => le_of_forall_lt fun c hc => ?_
    obtain ⟨δ, hδ, hδ'⟩ := hnbhd (Ioi c) (Ioi_mem_nhds hc)
    have hε : 0 < min δ (1 / ((n : ℝ) + 1)) := lt_min hδ (by positivity)
    obtain ⟨i, hi⟩ := hclose u hu _ hε
    obtain ⟨j, hj⟩ := hclose v hv _ hε
    refine lt_of_lt_of_le (hδ' (q i) (q j) (hi.trans_le (min_le_left _ _))
      (hj.trans_le (min_le_left _ _))) ?_
    exact le_iSup_of_le i (le_iSup_of_le j (le_iSup_of_le
      ⟨hi.trans_le (min_le_right _ _), hj.trans_le (min_le_right _ _)⟩ le_rfl))

end SmallGammaGeodesics.CC
