import InteractingSLE.Spec.Sec2.MartingaleStieltjes

/-!
# The quadratic-variation defect of a Loewner driver along a partition (pathwise layer)

Packet PROVE-SEC2-MART. Specification, proof of Theorem 2.4 (`source/spec/p001-048.md`, anchor
`thm-2.4-proof`, L856–L874): the local-martingale hypothesis identifies the quadratic variation of
the driver, `d⟨M⟩ = κ dt`. We use the two lowest Laurent coefficients of `𝔥_t(z)` at `∞`, the
processes `N = 2W + ∑ⱼ ρⱼ Vʲ` and `Q = W² + ½ ∑ⱼ ρⱼ (Vʲ)² − (2 ∑ⱼ ρⱼ + κ) t`, and the martingale part
`M = W − W₀ + ½ ∑ⱼ ρⱼ (Vʲ − Vʲ₀)` of the driver. Along a partition, the increments satisfy the
exact cell identity (`cell_identity`)

  `Δ(M²) − κ Δt = ΔQ + 2 (M − W) ΔM + cellDefect`,

and this file proves that the summed `cellDefect` tends to `0` pathwise as the mesh tends to `0`
(`exists_delta_abs_sum_cellDefect_le`), using the Riemann–Stieltjes limit
`∑ (Vʲ − W) ΔVʲ → 2 Δt` of `MartingaleStieltjes` and the vanishing of `∑ Δf Δg` for continuous `f`
and monotone `g`. A uniform bound (`abs_sum_cellDefect_le`) gives the domination for the
martingale step.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology

namespace InteractingSLE

namespace MartChar

variable {ι : Type*} [Fintype ι]

/-- The defect of one cell `[t₀, t₁]` (with `dt = t₁ − t₀`) in the identity
`Δ(M²) − κ Δt = ΔQ + 2 (M − W) ΔM + cellDefect` (see `cell_identity`): driver values `w₀, w₁`,
force-point values `v₀, v₁`, weights `ρ`. -/
def cellDefect (ρ : ι → ℝ) (w₀ w₁ : ℝ) (v₀ v₁ : ι → ℝ) (dt : ℝ) : ℝ :=
  (∑ j, ρ j * (2 * dt - (v₀ j - w₀) * (v₁ j - v₀ j)))
    - (1 / 2) * (∑ j, ρ j * ((v₁ j - v₀ j) * (v₁ j - v₀ j)))
    + (w₁ - w₀) * (∑ j, ρ j * (v₁ j - v₀ j))
    + (1 / 4) * ((∑ j, ρ j * (v₁ j - v₀ j)) * (∑ j, ρ j * (v₁ j - v₀ j)))

/-- The martingale part `M = W − W₀ + ½ ∑ⱼ ρⱼ (Vʲ − Vʲ₀)` of a state, relative to an initial state. -/
def martValue (ρ : ι → ℝ) (w₀ : ℝ) (v₀ : ι → ℝ) (w : ℝ) (v : ι → ℝ) : ℝ :=
  w - w₀ + (1 / 2) * ∑ j, ρ j * (v j - v₀ j)

/-- The first Laurent coefficient `N = 2W + ∑ⱼ ρⱼ Vʲ` of a state. -/
def driftValue (ρ : ι → ℝ) (w : ℝ) (v : ι → ℝ) : ℝ :=
  2 * w + ∑ j, ρ j * v j

/-- The second Laurent coefficient `Q = W² + ½ ∑ⱼ ρⱼ (Vʲ)² − (2 ∑ⱼ ρⱼ + κ) t` of a state at time
`t`. -/
def quadValue (κ : ℝ) (ρ : ι → ℝ) (w : ℝ) (v : ι → ℝ) (t : ℝ) : ℝ :=
  w ^ 2 + (1 / 2) * (∑ j, ρ j * v j ^ 2) - (2 * (∑ j, ρ j) + κ) * t

/-- **The cell identity.** For a cell `[t₀, t₁]` with states `(w₀', v₀')`, `(w₁', v₁')` and the
martingale part `M` relative to an initial state `(w₀, v₀)`:
`M₁² − M₀² − κ (t₁ − t₀) = (Q₁ − Q₀) + 2 (M₀ − w₀') (M₁ − M₀) + cellDefect`. -/
lemma cell_identity (κ : ℝ) (ρ : ι → ℝ) (w₀ : ℝ) (v₀ : ι → ℝ) (a₀ a₁ : ℝ) (b₀ b₁ : ι → ℝ)
    (t₀ t₁ : ℝ) :
    martValue ρ w₀ v₀ a₁ b₁ ^ 2 - martValue ρ w₀ v₀ a₀ b₀ ^ 2 - κ * (t₁ - t₀)
      = (quadValue κ ρ a₁ b₁ t₁ - quadValue κ ρ a₀ b₀ t₀)
        + 2 * (martValue ρ w₀ v₀ a₀ b₀ - a₀) * (martValue ρ w₀ v₀ a₁ b₁ - martValue ρ w₀ v₀ a₀ b₀)
        + cellDefect ρ a₀ a₁ b₀ b₁ (t₁ - t₀) := by
  -- reduce every sum to the four scalars `σ, A₀, A₁, B₀, B₁` and `P = ∑ ρ v₀`
  have hdiff : (∑ j, ρ j * (b₁ j - b₀ j)) = (∑ j, ρ j * b₁ j) - ∑ j, ρ j * b₀ j := by
    rw [← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun j _ => by ring
  have hm : ∀ b : ι → ℝ, (∑ j, ρ j * (b j - v₀ j)) = (∑ j, ρ j * b j) - ∑ j, ρ j * v₀ j := by
    intro b
    rw [← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun j _ => by ring
  have hdef : (∑ j, ρ j * (2 * (t₁ - t₀) - (b₀ j - a₀) * (b₁ j - b₀ j)))
      - (1 / 2) * (∑ j, ρ j * ((b₁ j - b₀ j) * (b₁ j - b₀ j)))
      = 2 * (t₁ - t₀) * (∑ j, ρ j) - (1 / 2) * ((∑ j, ρ j * b₁ j ^ 2) - ∑ j, ρ j * b₀ j ^ 2)
        + a₀ * ((∑ j, ρ j * b₁ j) - ∑ j, ρ j * b₀ j) := by
    have key : ∀ j, ρ j * (2 * (t₁ - t₀) - (b₀ j - a₀) * (b₁ j - b₀ j))
        - 1 / 2 * (ρ j * ((b₁ j - b₀ j) * (b₁ j - b₀ j)))
        = 2 * (t₁ - t₀) * ρ j - 1 / 2 * (ρ j * b₁ j ^ 2 - ρ j * b₀ j ^ 2)
          + a₀ * (ρ j * b₁ j - ρ j * b₀ j) := fun j => by ring
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib, Finset.sum_congr rfl fun j _ => key j]
    simp only [← Finset.mul_sum, Finset.sum_sub_distrib, Finset.sum_add_distrib]
  simp only [martValue, quadValue, cellDefect, hm]
  rw [hdiff]
  set S := ∑ j, ρ j * (2 * (t₁ - t₀) - (b₀ j - a₀) * (b₁ j - b₀ j))
  set T := ∑ j, ρ j * ((b₁ j - b₀ j) * (b₁ j - b₀ j))
  set A₀ := ∑ j, ρ j * b₀ j
  set A₁ := ∑ j, ρ j * b₁ j
  set P := ∑ j, ρ j * v₀ j
  set B₀ := ∑ j, ρ j * b₀ j ^ 2
  set B₁ := ∑ j, ρ j * b₁ j ^ 2
  set σ := ∑ j, ρ j
  linear_combination (-1 : ℝ) * hdef

/-! ### Pathwise convergence of the summed defect -/

/-- A positive lower bound for finitely many positive reals. -/
lemma exists_pos_forall_le_of_finite {κ : Type*} [Finite κ] (f : κ → ℝ) (hf : ∀ j, 0 < f j) :
    ∃ δ > 0, ∀ j, δ ≤ f j := by
  cases nonempty_fintype κ
  by_cases h : Nonempty κ
  · obtain ⟨j₀, -, hj₀⟩ := Finset.exists_min_image Finset.univ f Finset.univ_nonempty
    exact ⟨f j₀, hf j₀, fun j => hj₀ j (Finset.mem_univ j)⟩
  · exact ⟨1, one_pos, fun j => (h ⟨j⟩).elim⟩

/-- The summed defect, regrouped by force point (sequence form). -/
lemma sum_cellDefect_eq (ρ : ι → ℝ) (wk : ℕ → ℝ) (vk : ι → ℕ → ℝ) (tk : ℕ → ℝ) (n : ℕ) :
    ∑ k ∈ Finset.range n, cellDefect ρ (wk k) (wk (k + 1)) (fun j => vk j k)
        (fun j => vk j (k + 1)) (tk (k + 1) - tk k)
      = (∑ j, ρ j * (2 * (tk n - tk 0)
          - ∑ k ∈ Finset.range n, (vk j k - wk k) * (vk j (k + 1) - vk j k)))
        - (1 / 2) * (∑ j, ρ j * ∑ k ∈ Finset.range n,
            (vk j (k + 1) - vk j k) * (vk j (k + 1) - vk j k))
        + (∑ k ∈ Finset.range n, (wk (k + 1) - wk k) * ∑ j, ρ j * (vk j (k + 1) - vk j k))
        + (1 / 4) * (∑ k ∈ Finset.range n,
            (∑ j, ρ j * (vk j (k + 1) - vk j k)) * ∑ j, ρ j * (vk j (k + 1) - vk j k)) := by
  simp only [cellDefect, Finset.sum_add_distrib, Finset.sum_sub_distrib]
  have h1 : ∑ k ∈ Finset.range n, ∑ j, ρ j * (2 * (tk (k + 1) - tk k)
      - (vk j k - wk k) * (vk j (k + 1) - vk j k))
      = ∑ j, ρ j * (2 * (tk n - tk 0)
          - ∑ k ∈ Finset.range n, (vk j k - wk k) * (vk j (k + 1) - vk j k)) := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [← Finset.mul_sum, Finset.sum_sub_distrib, ← Finset.mul_sum, Finset.sum_range_sub tk]
  have h2 : ∑ k ∈ Finset.range n, (1 / 2 : ℝ) * ∑ j, ρ j * ((vk j (k + 1) - vk j k)
      * (vk j (k + 1) - vk j k))
      = (1 / 2) * ∑ j, ρ j * ∑ k ∈ Finset.range n,
          (vk j (k + 1) - vk j k) * (vk j (k + 1) - vk j k) := by
    rw [← Finset.mul_sum, Finset.sum_comm]
    congr 1
    exact Finset.sum_congr rfl fun j _ => (Finset.mul_sum _ _ _).symm
  rw [h1, h2, ← Finset.mul_sum]

/-- The increment of `A = ∑ⱼ ρⱼ vʲ` is dominated by the weighted increments of the force points. -/
lemma abs_sum_mul_sub_le (ρ : ι → ℝ) (x y : ι → ℝ) :
    |∑ j, ρ j * (y j - x j)| ≤ ∑ j, |ρ j| * |y j - x j| := by
  refine (Finset.abs_sum_le_sum_abs _ _).trans (le_of_eq ?_)
  exact Finset.sum_congr rfl fun j _ => abs_mul _ _

/-- The total variation of `A = ∑ⱼ ρⱼ vʲ` along a partition. -/
lemma sum_abs_sum_mul_sub_le (ρ : ι → ℝ) (vk : ι → ℕ → ℝ) (n : ℕ) :
    ∑ k ∈ Finset.range n, |∑ j, ρ j * (vk j (k + 1) - vk j k)|
      ≤ ∑ j, |ρ j| * ∑ k ∈ Finset.range n, |vk j (k + 1) - vk j k| := by
  calc ∑ k ∈ Finset.range n, |∑ j, ρ j * (vk j (k + 1) - vk j k)|
      ≤ ∑ k ∈ Finset.range n, ∑ j, |ρ j| * |vk j (k + 1) - vk j k| :=
        Finset.sum_le_sum fun k _ => abs_sum_mul_sub_le ρ _ _
    _ = ∑ j, |ρ j| * ∑ k ∈ Finset.range n, |vk j (k + 1) - vk j k| := by
        rw [Finset.sum_comm]
        exact Finset.sum_congr rfl fun j _ => (Finset.mul_sum _ _ _).symm

variable {w : ℝ → ℝ} {v : ι → ℝ → ℝ} {a b : ℝ}

/-- **The summed defect vanishes as the mesh tends to `0`** (pathwise). Hypotheses: the driver `w`
and the force points `vʲ` are continuous on `[a, b]`, each `vʲ` is monotone, solves
`(vʲ)' = 2/(vʲ − w)` away from its collisions with `w`, and has a Lebesgue-null collision set. -/
theorem exists_delta_abs_sum_cellDefect_le (ρ : ι → ℝ) (hw : ContinuousOn w (Icc a b))
    (hv : ∀ j, ContinuousOn (v j) (Icc a b))
    (hmono : ∀ j, MonotoneOn (v j) (Icc a b) ∨ AntitoneOn (v j) (Icc a b))
    (hderiv : ∀ j, ∀ u ∈ Ioo a b, v j u ≠ w u → HasDerivAt (v j) (2 / (v j u - w u)) u)
    (hnull : ∀ j, volume {u ∈ Icc a b | v j u = w u} = 0) {ε : ℝ} (hε : 0 < ε) :
    ∃ δ > 0, ∀ (n : ℕ) (p : ℕ → ℝ), Monotone p → p 0 = a → p n = b →
      (∀ k < n, p (k + 1) - p k < δ) →
      |∑ k ∈ Finset.range n, cellDefect ρ (w (p k)) (w (p (k + 1))) (fun j => v j (p k))
          (fun j => v j (p (k + 1))) (p (k + 1) - p k)| ≤ ε := by
  set R : ℝ := (∑ j, |ρ j|) + 1 with hR_def
  set Vt : ℝ := (∑ j, |v j b - v j a|) + 1 with hVt_def
  have hR0 : 0 ≤ ∑ j, |ρ j| := Finset.sum_nonneg fun j _ => abs_nonneg _
  have hR : 1 ≤ R := by linarith
  have hVt0 : 0 ≤ ∑ j, |v j b - v j a| := Finset.sum_nonneg fun j _ => abs_nonneg _
  have hVt : 1 ≤ Vt := by linarith
  set ε₁ : ℝ := ε / (4 * R) with hε₁_def
  have hε₁ : 0 < ε₁ := div_pos hε (by positivity)
  set η : ℝ := min 1 (ε / (8 * R ^ 2 * Vt)) with hη_def
  have hη : 0 < η := lt_min one_pos (div_pos hε (by positivity))
  -- the Riemann–Stieltjes limits, one per force point
  have hDL : ∀ j, ∃ δ > 0, ∀ (n : ℕ) (p : ℕ → ℝ), Monotone p → p 0 = a → p n = b →
      (∀ k < n, p (k + 1) - p k < δ) →
      |(∑ k ∈ Finset.range n, (v j (p k) - w (p k)) * (v j (p (k + 1)) - v j (p k)))
        - 2 * (b - a)| ≤ ε₁ := fun j =>
    exists_delta_abs_sum_gap_mul_sub_sub_le (hv j) hw (hmono j) (hderiv j) (hnull j) hε₁
  choose δD hδD hD using hDL
  have hUC : ∀ j, ∃ δ > 0, ∀ x ∈ Icc a b, ∀ y ∈ Icc a b, |x - y| < δ → |v j x - v j y| < η :=
    fun j => exists_delta_abs_sub_lt (hv j) hη
  choose δV hδV hV using hUC
  obtain ⟨δW, hδW, hW⟩ := exists_delta_abs_sub_lt hw hη
  obtain ⟨δ₀, hδ₀, hδ₀le⟩ := exists_pos_forall_le_of_finite (fun j => min (δD j) (δV j))
    fun j => lt_min (hδD j) (hδV j)
  refine ⟨min δ₀ δW, lt_min hδ₀ hδW, fun n p hp h0 hn hmesh => ?_⟩
  have hmem : ∀ k ≤ n, p k ∈ Icc a b := fun k hk => mem_Icc_of_partition hp h0 hn hk
  have hinc : ∀ k < n, |p (k + 1) - p k| < min δ₀ δW := fun k hk => by
    rw [abs_of_nonneg (sub_nonneg.2 (hp (Nat.le_succ k)))]
    exact hmesh k hk
  -- small increments
  have hdv : ∀ j, ∀ k < n, |v j (p (k + 1)) - v j (p k)| ≤ η := fun j k hk =>
    (hV j _ (hmem _ hk) _ (hmem _ hk.le) ((hinc k hk).trans_le
      ((min_le_left _ _).trans ((hδ₀le j).trans (min_le_right _ _))))).le
  have hdw : ∀ k < n, |w (p (k + 1)) - w (p k)| ≤ η := fun k hk =>
    (hW _ (hmem _ hk) _ (hmem _ hk.le) ((hinc k hk).trans_le (min_le_right _ _))).le
  have hvar : ∀ j, ∑ k ∈ Finset.range n, |v j (p (k + 1)) - v j (p k)| = |v j b - v j a| :=
    fun j => sum_abs_sub_eq_of_monotoneOn_or_antitoneOn (hmono j) hp h0 hn
  have hvarle : ∀ j, |v j b - v j a| ≤ Vt := fun j => by
    have := Finset.single_le_sum (f := fun j => |v j b - v j a|) (fun j _ => abs_nonneg _)
      (Finset.mem_univ j)
    linarith
  have hAvar : ∑ k ∈ Finset.range n, |∑ j, ρ j * (v j (p (k + 1)) - v j (p k))| ≤ R * Vt := by
    refine (sum_abs_sum_mul_sub_le ρ (fun j k => v j (p k)) n).trans ?_
    simp only [hvar]
    calc ∑ j, |ρ j| * |v j b - v j a| ≤ ∑ j, |ρ j| * Vt :=
          Finset.sum_le_sum fun j _ => mul_le_mul_of_nonneg_left (hvarle j) (abs_nonneg _)
      _ = (∑ j, |ρ j|) * Vt := (Finset.sum_mul _ _ _).symm
      _ ≤ R * Vt := mul_le_mul_of_nonneg_right (by linarith) (by linarith)
  have hdA : ∀ k < n, |∑ j, ρ j * (v j (p (k + 1)) - v j (p k))| ≤ R * η := fun k hk => by
    refine (abs_sum_mul_sub_le ρ _ _).trans ?_
    calc ∑ j, |ρ j| * |v j (p (k + 1)) - v j (p k)| ≤ ∑ j, |ρ j| * η :=
          Finset.sum_le_sum fun j _ => mul_le_mul_of_nonneg_left (hdv j k hk) (abs_nonneg _)
      _ = (∑ j, |ρ j|) * η := (Finset.sum_mul _ _ _).symm
      _ ≤ R * η := mul_le_mul_of_nonneg_right (by linarith) hη.le
  -- the four pieces
  rw [sum_cellDefect_eq ρ (fun k => w (p k)) (fun j k => v j (p k)) p n, hn, h0]
  set T1 := ∑ j, ρ j * (2 * (b - a)
    - ∑ k ∈ Finset.range n, (v j (p k) - w (p k)) * (v j (p (k + 1)) - v j (p k)))
  set T2 := ∑ j, ρ j * ∑ k ∈ Finset.range n,
    (v j (p (k + 1)) - v j (p k)) * (v j (p (k + 1)) - v j (p k))
  set T3 := ∑ k ∈ Finset.range n,
    (w (p (k + 1)) - w (p k)) * ∑ j, ρ j * (v j (p (k + 1)) - v j (p k))
  set T4 := ∑ k ∈ Finset.range n,
    (∑ j, ρ j * (v j (p (k + 1)) - v j (p k))) * ∑ j, ρ j * (v j (p (k + 1)) - v j (p k))
  have h1 : |T1| ≤ ε / 4 := by
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    calc ∑ j, |ρ j * (2 * (b - a)
          - ∑ k ∈ Finset.range n, (v j (p k) - w (p k)) * (v j (p (k + 1)) - v j (p k)))|
        ≤ ∑ j, |ρ j| * ε₁ := Finset.sum_le_sum fun j _ => by
          rw [abs_mul, abs_sub_comm]
          exact mul_le_mul_of_nonneg_left (hD j n p hp h0 hn fun k hk =>
            (hmesh k hk).trans_le ((min_le_left _ _).trans ((hδ₀le j).trans
              (min_le_left _ _)))) (abs_nonneg _)
      _ = (∑ j, |ρ j|) * ε₁ := (Finset.sum_mul _ _ _).symm
      _ ≤ R * ε₁ := mul_le_mul_of_nonneg_right (by linarith) hε₁.le
      _ = ε / 4 := by rw [hε₁_def]; field_simp
  have h2 : |T2| ≤ R * η * Vt := by
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    calc ∑ j, |ρ j * ∑ k ∈ Finset.range n,
          (v j (p (k + 1)) - v j (p k)) * (v j (p (k + 1)) - v j (p k))|
        ≤ ∑ j, |ρ j| * (η * Vt) := Finset.sum_le_sum fun j _ => by
          rw [abs_mul]
          refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
          refine (abs_sum_mul_le (hdv j)).trans ?_
          rw [hvar j]
          exact mul_le_mul_of_nonneg_left (hvarle j) hη.le
      _ = (∑ j, |ρ j|) * (η * Vt) := (Finset.sum_mul _ _ _).symm
      _ ≤ R * (η * Vt) := mul_le_mul_of_nonneg_right (by linarith) (by positivity)
      _ = R * η * Vt := by ring
  have h3 : |T3| ≤ η * (R * Vt) :=
    (abs_sum_mul_le hdw).trans (mul_le_mul_of_nonneg_left hAvar hη.le)
  have h4 : |T4| ≤ R * η * (R * Vt) :=
    (abs_sum_mul_le hdA).trans (mul_le_mul_of_nonneg_left hAvar (by positivity))
  have hη2 : η * (R ^ 2 * Vt) ≤ ε / 8 := by
    have hle : η ≤ ε / (8 * R ^ 2 * Vt) := min_le_right _ _
    calc η * (R ^ 2 * Vt) ≤ ε / (8 * R ^ 2 * Vt) * (R ^ 2 * Vt) :=
          mul_le_mul_of_nonneg_right hle (by positivity)
      _ = ε / 8 := by field_simp
  have hηR : R * η * Vt ≤ η * (R ^ 2 * Vt) := by
    have : R ≤ R ^ 2 := by nlinarith
    calc R * η * Vt = η * (R * Vt) := by ring
      _ ≤ η * (R ^ 2 * Vt) := by gcongr
  have hη1 : η ≤ 1 := min_le_left _ _
  calc |T1 - 1 / 2 * T2 + T3 + 1 / 4 * T4| ≤ |T1| + 1 / 2 * |T2| + |T3| + 1 / 4 * |T4| := by
        have e1 := abs_add_le (T1 - 1 / 2 * T2 + T3) (1 / 4 * T4)
        have e2 := abs_add_le (T1 - 1 / 2 * T2) T3
        have e3 := abs_sub T1 (1 / 2 * T2)
        have e4 : |1 / 2 * T2| = 1 / 2 * |T2| := by
          rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)]
        have e5 : |1 / 4 * T4| = 1 / 4 * |T4| := by
          rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 4)]
        linarith
    _ ≤ ε := by
        have h3' : η * (R * Vt) ≤ η * (R ^ 2 * Vt) := by
          have : R ≤ R ^ 2 := by nlinarith
          gcongr
        have h4' : R * η * (R * Vt) = η * (R ^ 2 * Vt) := by ring
        nlinarith [abs_nonneg T2, abs_nonneg T4]

/-- The uniform bound for the summed defect. -/
def defectBound (ρ : ι → ℝ) (K L : ℝ) : ℝ :=
  (∑ j, |ρ j|) * (2 * L + 10 * K ^ 2) + (∑ j, |ρ j|) ^ 2 * K ^ 2

/-- **Uniform bound for the summed defect**: if the driver and the monotone force points are
bounded by `K` at the partition points, the summed defect is at most `defectBound ρ K (b − a)`. -/
theorem abs_sum_cellDefect_le (ρ : ι → ℝ)
    (hmono : ∀ j, MonotoneOn (v j) (Icc a b) ∨ AntitoneOn (v j) (Icc a b)) {n : ℕ}
    {p : ℕ → ℝ} (hp : Monotone p) (h0 : p 0 = a) (hn : p n = b) {K : ℝ}
    (hK : ∀ k ≤ n, |w (p k)| ≤ K ∧ ∀ j, |v j (p k)| ≤ K) :
    |∑ k ∈ Finset.range n, cellDefect ρ (w (p k)) (w (p (k + 1))) (fun j => v j (p k))
        (fun j => v j (p (k + 1))) (p (k + 1) - p k)| ≤ defectBound ρ K (b - a) := by
  set R : ℝ := ∑ j, |ρ j| with hR_def
  have hR : 0 ≤ R := Finset.sum_nonneg fun j _ => abs_nonneg _
  have hab : 0 ≤ b - a := sub_nonneg.2 (le_of_partition hp h0 hn)
  have hK0 : 0 ≤ K := (abs_nonneg _).trans (hK 0 (Nat.zero_le n)).1
  have hvar : ∀ j, ∑ k ∈ Finset.range n, |v j (p (k + 1)) - v j (p k)| = |v j b - v j a| :=
    fun j => sum_abs_sub_eq_of_monotoneOn_or_antitoneOn (hmono j) hp h0 hn
  have hvarle : ∀ j, |v j b - v j a| ≤ 2 * K := fun j => by
    have h1 := (hK n le_rfl).2 j
    have h2 := (hK 0 (Nat.zero_le n)).2 j
    rw [hn] at h1
    rw [h0] at h2
    calc |v j b - v j a| ≤ |v j b| + |v j a| := abs_sub _ _
      _ ≤ 2 * K := by linarith
  have hdv : ∀ j, ∀ k < n, |v j (p (k + 1)) - v j (p k)| ≤ 2 * K := fun j k hk => by
    calc |v j (p (k + 1)) - v j (p k)| ≤ |v j (p (k + 1))| + |v j (p k)| := abs_sub _ _
      _ ≤ 2 * K := by linarith [(hK (k + 1) hk).2 j, (hK k hk.le).2 j]
  have hdw : ∀ k < n, |w (p (k + 1)) - w (p k)| ≤ 2 * K := fun k hk => by
    calc |w (p (k + 1)) - w (p k)| ≤ |w (p (k + 1))| + |w (p k)| := abs_sub _ _
      _ ≤ 2 * K := by linarith [(hK (k + 1) hk).1, (hK k hk.le).1]
  have hAvar : ∑ k ∈ Finset.range n, |∑ j, ρ j * (v j (p (k + 1)) - v j (p k))| ≤ R * (2 * K) := by
    refine (sum_abs_sum_mul_sub_le ρ (fun j k => v j (p k)) n).trans ?_
    simp only [hvar]
    calc ∑ j, |ρ j| * |v j b - v j a| ≤ ∑ j, |ρ j| * (2 * K) :=
          Finset.sum_le_sum fun j _ => mul_le_mul_of_nonneg_left (hvarle j) (abs_nonneg _)
      _ = R * (2 * K) := (Finset.sum_mul _ _ _).symm
  have hdA : ∀ k < n, |∑ j, ρ j * (v j (p (k + 1)) - v j (p k))| ≤ R * (2 * K) := fun k hk => by
    refine (abs_sum_mul_sub_le ρ _ _).trans ?_
    calc ∑ j, |ρ j| * |v j (p (k + 1)) - v j (p k)| ≤ ∑ j, |ρ j| * (2 * K) :=
          Finset.sum_le_sum fun j _ => mul_le_mul_of_nonneg_left (hdv j k hk) (abs_nonneg _)
      _ = R * (2 * K) := (Finset.sum_mul _ _ _).symm
  have hgap : ∀ j, ∀ k < n, |v j (p k) - w (p k)| ≤ 2 * K := fun j k hk => by
    calc |v j (p k) - w (p k)| ≤ |v j (p k)| + |w (p k)| := abs_sub _ _
      _ ≤ 2 * K := by linarith [(hK k hk.le).2 j, (hK k hk.le).1]
  rw [sum_cellDefect_eq ρ (fun k => w (p k)) (fun j k => v j (p k)) p n, hn, h0]
  set T1 := ∑ j, ρ j * (2 * (b - a)
    - ∑ k ∈ Finset.range n, (v j (p k) - w (p k)) * (v j (p (k + 1)) - v j (p k)))
  set T2 := ∑ j, ρ j * ∑ k ∈ Finset.range n,
    (v j (p (k + 1)) - v j (p k)) * (v j (p (k + 1)) - v j (p k))
  set T3 := ∑ k ∈ Finset.range n,
    (w (p (k + 1)) - w (p k)) * ∑ j, ρ j * (v j (p (k + 1)) - v j (p k))
  set T4 := ∑ k ∈ Finset.range n,
    (∑ j, ρ j * (v j (p (k + 1)) - v j (p k))) * ∑ j, ρ j * (v j (p (k + 1)) - v j (p k))
  have hS : ∀ j, |∑ k ∈ Finset.range n, (v j (p k) - w (p k)) * (v j (p (k + 1)) - v j (p k))|
      ≤ 4 * K ^ 2 := fun j => by
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    calc ∑ k ∈ Finset.range n, |(v j (p k) - w (p k)) * (v j (p (k + 1)) - v j (p k))|
        ≤ ∑ k ∈ Finset.range n, 2 * K * |v j (p (k + 1)) - v j (p k)| :=
          Finset.sum_le_sum fun k hk => by
            rw [abs_mul]
            exact mul_le_mul_of_nonneg_right (hgap j k (Finset.mem_range.1 hk)) (abs_nonneg _)
      _ = 2 * K * |v j b - v j a| := by rw [← Finset.mul_sum, hvar j]
      _ ≤ 2 * K * (2 * K) := mul_le_mul_of_nonneg_left (hvarle j) (by positivity)
      _ = 4 * K ^ 2 := by ring
  have h1 : |T1| ≤ R * (2 * (b - a) + 4 * K ^ 2) := by
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    calc ∑ j, |ρ j * (2 * (b - a)
          - ∑ k ∈ Finset.range n, (v j (p k) - w (p k)) * (v j (p (k + 1)) - v j (p k)))|
        ≤ ∑ j, |ρ j| * (2 * (b - a) + 4 * K ^ 2) := Finset.sum_le_sum fun j _ => by
          rw [abs_mul]
          refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
          calc _ ≤ |2 * (b - a)| + |∑ k ∈ Finset.range n,
                (v j (p k) - w (p k)) * (v j (p (k + 1)) - v j (p k))| := abs_sub _ _
            _ ≤ 2 * (b - a) + 4 * K ^ 2 := by
                rw [abs_of_nonneg (by positivity : (0 : ℝ) ≤ 2 * (b - a))]
                linarith [hS j]
      _ = R * (2 * (b - a) + 4 * K ^ 2) := (Finset.sum_mul _ _ _).symm
  have h2 : |T2| ≤ R * (4 * K ^ 2) := by
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    calc ∑ j, |ρ j * ∑ k ∈ Finset.range n,
          (v j (p (k + 1)) - v j (p k)) * (v j (p (k + 1)) - v j (p k))|
        ≤ ∑ j, |ρ j| * (4 * K ^ 2) := Finset.sum_le_sum fun j _ => by
          rw [abs_mul]
          refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
          refine (abs_sum_mul_le (hdv j)).trans ?_
          rw [hvar j]
          nlinarith [hvarle j]
      _ = R * (4 * K ^ 2) := (Finset.sum_mul _ _ _).symm
  have h3 : |T3| ≤ 2 * K * (R * (2 * K)) :=
    (abs_sum_mul_le hdw).trans (mul_le_mul_of_nonneg_left hAvar (by positivity))
  have h4 : |T4| ≤ R * (2 * K) * (R * (2 * K)) :=
    (abs_sum_mul_le hdA).trans (mul_le_mul_of_nonneg_left hAvar (by positivity))
  have e1 := abs_add_le (T1 - 1 / 2 * T2 + T3) (1 / 4 * T4)
  have e2 := abs_add_le (T1 - 1 / 2 * T2) T3
  have e3 := abs_sub T1 (1 / 2 * T2)
  have e4 : |1 / 2 * T2| = 1 / 2 * |T2| := by
    rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)]
  have e5 : |1 / 4 * T4| = 1 / 4 * |T4| := by
    rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 4)]
  simp only [defectBound]
  rw [← hR_def]
  nlinarith

end MartChar

end InteractingSLE
