import HigherDimLQGContinuity.Topology.Clearance

/-!
# Lemma 4.1′, polygonal and box form (`d ≥ 3`)

Packet Q1 (ruling N9). Source: planning audit `planning/audits/NA2-section-4.md`, Details (c) **R1′**
(lattice discretization of the path of Lemma 4.1′); [C] Lemma 4.1, l. 522–524 and 550–553.

**Statement** (`lemma41_polygonal`, explicit form `lemma41_polygonal_explicit`). In the setting of
`lemma41_clearance`, assume moreover `Ω ⊆ B̄(0, R₀)` and `B̄(x, u), B̄(y, u) ⊆ Ω`. Then `x` and `y`
are joined by a polygonal path `z 0 = x, …, z n = y` whose segments lie in `Ω` at distance
`≥ c u^{1/(αβ)²}` from the arc, with `n ≤ C u^{-d/(αβ)²}` edges (`c = polygonalClearanceConst`,
`C = polygonalConst`).

**Proof.** The eroded set `Ω_κ = {w : B̄(w, u/2) ⊆ Ω}` (`erodedSet`) is open, convex, contains `x, y`
and `B̄(γ(t), b₀/2)`; Lemma 4.1′ in `Ω_κ` with `(b₀/2, u/2)` gives a path `Π` with clearance
`r = c (u/2)^{1/(αβ)²}`. With `e = r/4`, `η = e/√d` and `N` from uniform continuity
(`|Π(s) - Π(s′)| < e` for `|s - s′| ≤ 1/N`), the chain `x, q_1, …, q_{N-1}, y`, where `q_i` is the
coordinatewise floor rounding of `Π(i/N)` to `ηℤ^d` (`latticeSnap`, error `≤ η√d = e`), has every
segment inside `B̄(Π(i/N), 2e) ⊆ B̄(Π(i/N), u/2) ⊆ Ω` and at distance `≥ r - 2e = r/2` from the arc.
All its vertices lie in the finite set `{x, y} ∪ (ηℤ^d ∩ [-M η, M η]^d)`, `M = ⌈R₀/η⌉`
(`latticeBox`); a shortest such chain has distinct vertices (`exists_shortChain_lt_card`), hence at
most `(2M + 1)^d + 1 ≤ C u^{-d/(αβ)²}` edges. (The audit's king-move graph and
`SimpleGraph.Walk.toPath` are replaced by this direct shortest-chain argument.)
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Metric
open HigherDimLFPP (Rd)

namespace HigherDimLQGContinuity.Topology

variable {d : ℕ}

/-! ### Shortest chains have distinct vertices -/

/-- A chain `z 0 = x, …, z N = y` with vertices in a finite set `F` and consecutive vertices related
by `R` can be shortened to one with fewer than `#F` steps. -/
lemma exists_shortChain_lt_card {E : Type*} (F : Finset E) (R : E → E → Prop) {x y : E}
    (h : ∃ (N : ℕ) (z : ℕ → E), z 0 = x ∧ z N = y ∧ (∀ i ≤ N, z i ∈ F) ∧
      ∀ i < N, R (z i) (z (i + 1))) :
    ∃ (n : ℕ) (z : ℕ → E), z 0 = x ∧ z n = y ∧ n < F.card ∧ (∀ i ≤ n, z i ∈ F) ∧
      ∀ i < n, R (z i) (z (i + 1)) := by
  classical
  set n := Nat.find h with hn
  obtain ⟨z, hz0, hzn, hzF, hzR⟩ := Nat.find_spec h
  refine ⟨n, z, hz0, hzn, ?_, hzF, hzR⟩
  -- the vertices `z 0, …, z n` are distinct
  have hinj : InjOn z (Finset.range (n + 1) : Set ℕ) := by
    intro i hi j hj hij
    simp only [Finset.coe_range, mem_Iio] at hi hj
    by_contra hne
    -- cut out the loop between the two visits
    have key : ∀ i j, i < j → j ≤ n → z i = z j → False := by
      intro i j hij hjn hz
      set z' : ℕ → E := fun k => if k ≤ i then z k else z (k + (j - i)) with hz'
      have hlt : n - (j - i) < n := by omega
      apply Nat.find_min h hlt
      refine ⟨z', ?_, ?_, ?_, ?_⟩
      · simp only [hz', Nat.zero_le, ↓reduceIte, hz0]
      · simp only [hz']
        split_ifs with h1
        · have : n - (j - i) = i := by omega
          rw [this, hz, show j = n by omega, hzn]
        · rw [show n - (j - i) + (j - i) = n by omega, hzn]
      · intro k hk
        simp only [hz']
        split_ifs with h1
        · exact hzF k (by omega)
        · exact hzF _ (by omega)
      · intro k hk
        simp only [hz']
        by_cases h1 : k + 1 ≤ i
        · have h0 : k ≤ i := by omega
          simp only [h0, h1, ↓reduceIte]
          exact hzR k (by omega)
        · simp only [h1, ↓reduceIte]
          by_cases h2 : k ≤ i
          · simp only [h2, ↓reduceIte]
            have hki : k = i := by omega
            subst hki
            rw [hz, show k + 1 + (j - k) = j + 1 by omega]
            exact hzR j (by omega)
          · simp only [h2, ↓reduceIte]
            rw [show k + 1 + (j - i) = k + (j - i) + 1 by omega]
            exact hzR _ (by omega)
    rcases lt_or_gt_of_ne hne with h1 | h1
    · exact key i j h1 (by omega) hij
    · exact key j i h1 (by omega) hij.symm
  have hsub : (Finset.range (n + 1)).image z ⊆ F := by
    intro w hw
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.1 hw
    exact hzF i (Nat.lt_succ_iff.1 (Finset.mem_range.1 hi))
  have := Finset.card_le_card hsub
  rw [Finset.card_image_of_injOn hinj, Finset.card_range] at this
  omega

/-! ### Lattice rounding -/

/-- The coordinatewise floor rounding `η ⌊v / η⌋` of `v` to the lattice `ηℤ^d`. -/
def latticeSnap (η : ℝ) (v : Rd d) : Rd d := WithLp.toLp 2 fun j => η * (⌊v j / η⌋ : ℝ)

/-- The lattice points `η k`, `k ∈ [-M, M]^d`. -/
def latticeBox (d : ℕ) (η : ℝ) (M : ℤ) : Finset (Rd d) :=
  (Fintype.piFinset fun _ : Fin d => Finset.Icc (-M) M).image
    fun k => WithLp.toLp 2 fun j => η * (k j : ℝ)

lemma norm_latticeSnap_sub_le {η : ℝ} (hη : 0 < η) (v : Rd d) :
    ‖latticeSnap η v - v‖ ≤ η * √d := by
  rw [EuclideanSpace.norm_eq]
  have hcoord : ∀ j, ‖(latticeSnap η v - v).ofLp j‖ ^ 2 ≤ η ^ 2 := by
    intro j
    have hco : (latticeSnap η v - v).ofLp j = η * (⌊v j / η⌋ : ℝ) - v j := by
      simp [latticeSnap]
    rw [hco, Real.norm_eq_abs, sq_abs]
    have h1 : (⌊v j / η⌋ : ℝ) ≤ v j / η := Int.floor_le _
    have h2 : v j / η < (⌊v j / η⌋ : ℝ) + 1 := Int.lt_floor_add_one _
    have h1' : η * (⌊v j / η⌋ : ℝ) ≤ v j := by
      have := mul_le_mul_of_nonneg_left h1 hη.le
      rwa [mul_div_cancel₀ _ hη.ne'] at this
    have h2' : v j < η * (⌊v j / η⌋ : ℝ) + η := by
      have := mul_lt_mul_of_pos_left h2 hη
      rwa [mul_div_cancel₀ _ hη.ne', mul_add, mul_one] at this
    nlinarith
  calc √(∑ j, ‖(latticeSnap η v - v).ofLp j‖ ^ 2) ≤ √(∑ _j : Fin d, η ^ 2) :=
        Real.sqrt_le_sqrt (Finset.sum_le_sum fun j _ => hcoord j)
    _ = η * √d := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
          Real.sqrt_mul (Nat.cast_nonneg _), Real.sqrt_sq hη.le, mul_comm]

lemma latticeSnap_mem_latticeBox {η R : ℝ} (hη : 0 < η) {v : Rd d} (hv : ‖v‖ ≤ R) :
    latticeSnap η v ∈ latticeBox d η ⌈R / η⌉ := by
  refine Finset.mem_image.2 ⟨fun j => ⌊v j / η⌋, Fintype.mem_piFinset.2 fun j => ?_, rfl⟩
  have hvj : |v j| ≤ R := by
    have := PiLp.norm_apply_le v j
    rw [Real.norm_eq_abs] at this
    exact this.trans hv
  rw [Finset.mem_Icc]
  constructor
  · rw [← Int.floor_neg]
    apply Int.floor_mono
    rw [← neg_div]
    exact div_le_div_of_nonneg_right (by linarith [neg_abs_le (v j)]) hη.le
  · exact (Int.floor_mono (div_le_div_of_nonneg_right ((le_abs_self _).trans hvj) hη.le)).trans
      (Int.floor_le_ceil _)

lemma card_latticeBox_le (η : ℝ) (M : ℤ) :
    (latticeBox d η M).card ≤ (M + 1 - -M).toNat ^ d := by
  refine Finset.card_image_le.trans ?_
  rw [Fintype.card_piFinset, Finset.prod_const, Finset.card_univ, Fintype.card_fin, Int.card_Icc]

/-! ### The eroded domain -/

/-- The eroded set `{w : B̄(w, κ) ⊆ Ω}`. -/
def erodedSet (Ω : Set (Rd d)) (κ : ℝ) : Set (Rd d) := {w | closedBall w κ ⊆ Ω}

lemma isOpen_erodedSet {Ω : Set (Rd d)} (hΩ : IsOpen Ω) {κ : ℝ} (hκ : 0 ≤ κ) :
    IsOpen (erodedSet Ω κ) := by
  rw [Metric.isOpen_iff]
  intro w hw
  obtain ⟨δ, hδ, hδΩ⟩ := (isCompact_closedBall w κ).exists_cthickening_subset_open hΩ hw
  rw [cthickening_closedBall hδ.le hκ] at hδΩ
  refine ⟨δ, hδ, fun w' hw' => ?_⟩
  exact (closedBall_subset_closedBall' (by rw [mem_ball] at hw'; linarith)).trans hδΩ

lemma convex_erodedSet {Ω : Set (Rd d)} (hΩc : Convex ℝ Ω) (κ : ℝ) :
    Convex ℝ (erodedSet Ω κ) := by
  intro w₁ hw₁ w₂ hw₂ a b ha hb hab z hz
  set v := z - (a • w₁ + b • w₂) with hv
  have hvn : ‖v‖ ≤ κ := by rw [hv, ← dist_eq_norm]; exact hz
  have h1 : w₁ + v ∈ Ω := hw₁ (by rw [mem_closedBall, dist_eq_norm, add_sub_cancel_left]; exact hvn)
  have h2 : w₂ + v ∈ Ω := hw₂ (by rw [mem_closedBall, dist_eq_norm, add_sub_cancel_left]; exact hvn)
  have hz' : z = a • (w₁ + v) + b • (w₂ + v) := by
    rw [smul_add, smul_add, add_add_add_comm, ← add_smul, hab, one_smul, hv]
    abel
  rw [hz']
  exact hΩc h1 h2 ha hb hab

/-! ### The constants of R1′ -/

/-- The clearance constant of the polygonal form: `c (u/2)^{1/(αβ)²} / 2 = (c 2^{-1/(αβ)²} / 2)
u^{1/(αβ)²}`. -/
def polygonalClearanceConst (A α β : ℝ) : ℝ :=
  clearanceConst A α β / 2 ^ ((α * β) ^ 2)⁻¹ / 2

/-- The edge-count constant of the polygonal form: `((8 √d R₀ + 3) / (c 2^{-1/(αβ)²}))^d + 2`. -/
def polygonalConst (d : ℕ) (A α β R₀ : ℝ) : ℝ :=
  ((8 * √(d : ℝ) * R₀ + 3) / (clearanceConst A α β / 2 ^ ((α * β) ^ 2)⁻¹)) ^ d + 2

lemma polygonalClearanceConst_pos {A α β : ℝ} (hA : 0 < A) : 0 < polygonalClearanceConst A α β := by
  unfold polygonalClearanceConst
  have := clearanceConst_pos (α := α) (β := β) hA
  positivity

lemma polygonalConst_pos {A α β R₀ : ℝ} (hA : 0 < A) (hR₀ : 0 ≤ R₀) :
    0 < polygonalConst d A α β R₀ := by
  unfold polygonalConst
  have := clearanceConst_pos (α := α) (β := β) hA
  positivity

/-! ### Lemma 4.1′, polygonal form -/

/-- **Lemma 4.1′, polygonal and box form, explicit constants** (R1′): a polygonal path from `x` to
`y` with at most `C u^{-d/(αβ)²}` edges (`C = polygonalConst d A α β R₀`), every segment in `Ω` at
distance `≥ c u^{1/(αβ)²}` from the arc (`c = polygonalClearanceConst A α β`). -/
theorem lemma41_polygonal_explicit (hd : 3 ≤ d) {A α β R₀ : ℝ} (hA : 1 ≤ A) (hα : 0 < α)
    (hα1 : α ≤ 1) (hβ : 0 < β) (hβ1 : β ≤ 1) (hR₀ : 0 < R₀) {γ : ℝ → Rd d}
    (hγ : ArcModuli γ A α β) {Ω : Set (Rd d)} (hΩ : IsOpen Ω) (hΩc : Convex ℝ Ω)
    (hΩR : Ω ⊆ closedBall 0 R₀) {b₀ : ℝ} (hγΩ : ∀ t ∈ Icc (0 : ℝ) 1, closedBall (γ t) b₀ ⊆ Ω)
    {u : ℝ} (hu : 0 < u) (hu1 : u ≤ 1) (hub : u ≤ b₀ / 2) {x y : Rd d}
    (hxΩ : closedBall x u ⊆ Ω) (hyΩ : closedBall y u ⊆ Ω)
    (hxu : ∀ t ∈ Icc (0 : ℝ) 1, u ≤ dist x (γ t)) (hyu : ∀ t ∈ Icc (0 : ℝ) 1, u ≤ dist y (γ t)) :
    ∃ (n : ℕ) (z : ℕ → Rd d), z 0 = x ∧ z n = y ∧
      (n : ℝ) ≤ polygonalConst d A α β R₀ * u ^ (-((d : ℝ) / (α * β) ^ 2)) ∧
      ∀ i < n, ∀ w ∈ segment ℝ (z i) (z (i + 1)), w ∈ Ω ∧
        ∀ t ∈ Icc (0 : ℝ) 1, polygonalClearanceConst A α β * u ^ ((α * β) ^ 2)⁻¹ ≤ dist w (γ t) := by
  classical
  have hA0 : 0 < A := by linarith
  have hd0 : (0 : ℝ) < d := by exact_mod_cast (show 0 < d by omega)
  have hsd : 0 < √(d : ℝ) := Real.sqrt_pos.2 hd0
  set p := ((α * β) ^ 2)⁻¹ with hp
  have hab : 0 < α * β := mul_pos hα hβ
  have hab1 : α * β ≤ 1 := by nlinarith
  have hp1 : 1 ≤ p := (one_le_inv₀ (pow_pos hab 2)).2 (pow_le_one₀ hab.le hab1)
  set c₁ := clearanceConst A α β with hc₁
  have hc₁0 : 0 < c₁ := clearanceConst_pos hA0
  have hc₁1 : c₁ ≤ 1 := clearanceConst_le_one hA hα hβ
  set c₂ := c₁ / 2 ^ p with hc₂
  have hc₂0 : 0 < c₂ := by positivity
  set r := c₂ * u ^ p with hr
  have hr' : c₁ * (u / 2) ^ p = r := by
    rw [Real.div_rpow hu.le (by norm_num), hr, hc₂]
    ring
  have hr0 : 0 < r := by positivity
  have hru : r ≤ u / 2 := by
    rw [← hr']
    have h1 : (u / 2) ^ p ≤ u / 2 := by
      have := Real.rpow_le_rpow_of_exponent_ge (by positivity : 0 < u / 2) (by linarith) hp1
      rwa [Real.rpow_one] at this
    have h0 : 0 ≤ (u / 2) ^ p := by positivity
    nlinarith
  -- the eroded domain `Ω_κ = {w : B̄(w, u/2) ⊆ Ω}`
  set Ωκ := erodedSet Ω (u / 2) with hΩκ
  have hΩκo : IsOpen Ωκ := isOpen_erodedSet hΩ (by positivity)
  have hΩκc : Convex ℝ Ωκ := convex_erodedSet hΩc _
  have hΩκΩ : ∀ w ∈ Ωκ, closedBall w (u / 2) ⊆ Ω := fun w hw => hw
  have hγΩκ : ∀ t ∈ Icc (0 : ℝ) 1, closedBall (γ t) (b₀ / 2) ⊆ Ωκ := by
    intro t ht w hw
    rw [mem_closedBall] at hw
    exact (closedBall_subset_closedBall' (by linarith)).trans (hγΩ t ht)
  have hxκ : x ∈ Ωκ := (closedBall_subset_closedBall (by linarith)).trans hxΩ
  have hyκ : y ∈ Ωκ := (closedBall_subset_closedBall (by linarith)).trans hyΩ
  -- the path of Lemma 4.1′ in `Ω_κ`, with clearance `r`
  have hJ := lemma41_clearance_explicit hd hA hα hα1 hβ hβ1 hγ hΩκo hΩκc hγΩκ (u := u / 2)
    (by positivity) (by linarith) (by linarith) hxκ hyκ (fun t ht => by linarith [hxu t ht])
    (fun t ht => by linarith [hyu t ht])
  rw [← hc₁, ← hp, hr'] at hJ
  obtain ⟨P, hP⟩ := hJ
  have hPext : ∀ s, P.extend s ∈ Ωκ ∧ ∀ t ∈ Icc (0 : ℝ) 1, r < dist (P.extend s) (γ t) :=
    fun s => hP _
  -- uniform continuity: steps `1/N` move `Π` by less than `e = r/4`
  set e := r / 4 with he
  have he0 : 0 < e := by positivity
  obtain ⟨δ, hδ, hδP⟩ := Metric.uniformContinuousOn_iff.1
    (isCompact_Icc.uniformContinuousOn_of_continuous P.continuous_extend.continuousOn) e he0
  obtain ⟨N, hN⟩ := exists_nat_gt (1 / δ)
  have hNpos : (0 : ℝ) < N := lt_trans (by positivity) hN
  have hN0 : N ≠ 0 := by
    rintro rfl
    simp at hNpos
  set pt : ℕ → Rd d := fun i => P.extend ((i : ℝ) / N) with hpt
  have hpt0 : pt 0 = x := by simp [hpt]
  have hptN : pt N = y := by simp [hpt, div_self hNpos.ne']
  have hstep : ∀ i < N, dist (pt (i + 1)) (pt i) < e := by
    intro i hi
    have hi' : (i : ℝ) + 1 ≤ N := by exact_mod_cast hi
    apply hδP
    · refine ⟨by positivity, ?_⟩
      rw [div_le_one hNpos]
      push_cast
      linarith
    · refine ⟨by positivity, ?_⟩
      rw [div_le_one hNpos]
      linarith
    · rw [Real.dist_eq]
      push_cast
      rw [← sub_div, add_sub_cancel_left, abs_of_pos (by positivity)]
      exact (one_div_lt hNpos hδ).2 hN
  -- lattice rounding of the nodes `Π(i/N)`, `0 < i < N`
  set η := e / √(d : ℝ) with hη
  have hη0 : 0 < η := by positivity
  have hηe : η * √(d : ℝ) = e := by
    rw [hη]
    field_simp
  set M := ⌈R₀ / η⌉ with hM
  set F' : Finset (Rd d) := insert x (insert y (latticeBox d η M)) with hF'
  set z₀ : ℕ → Rd d := fun i => if i = 0 then x else if i = N then y else latticeSnap η (pt i)
    with hz₀
  have hz₀pt : ∀ i ≤ N, z₀ i ∈ F' ∧ ‖z₀ i - pt i‖ ≤ e := by
    intro i hi
    by_cases h0 : i = 0
    · subst h0
      have : z₀ 0 = x := by simp [hz₀]
      rw [this, hpt0, sub_self, norm_zero]
      exact ⟨Finset.mem_insert_self _ _, he0.le⟩
    by_cases hiN : i = N
    · subst hiN
      have : z₀ i = y := by simp [hz₀, h0]
      rw [this, hptN, sub_self, norm_zero]
      exact ⟨Finset.mem_insert_of_mem (Finset.mem_insert_self _ _), he0.le⟩
    · have : z₀ i = latticeSnap η (pt i) := by simp [hz₀, h0, hiN]
      rw [this]
      refine ⟨Finset.mem_insert_of_mem (Finset.mem_insert_of_mem
        (latticeSnap_mem_latticeBox hη0 ?_)), (norm_latticeSnap_sub_le hη0 _).trans hηe.le⟩
      have := hΩR (hΩκΩ _ (hPext ((i : ℝ) / N)).1 (mem_closedBall_self (by positivity)))
      rwa [mem_closedBall, dist_zero_right] at this
  -- every segment of the chain lies in `Ω` at distance `≥ r/2` from the arc
  set G := {w : Rd d | w ∈ Ω ∧ ∀ t ∈ Icc (0 : ℝ) 1, r / 2 ≤ dist w (γ t)} with hG
  have hseg : ∀ i < N, segment ℝ (z₀ i) (z₀ (i + 1)) ⊆ G := by
    intro i hi
    have h1 := (hz₀pt i hi.le).2
    have h2 := (hz₀pt (i + 1) hi).2
    have hst := hstep i hi
    rw [dist_eq_norm] at hst
    have h2' : ‖z₀ (i + 1) - pt i‖ ≤ 2 * e := by
      calc ‖z₀ (i + 1) - pt i‖ = ‖(z₀ (i + 1) - pt (i + 1)) + (pt (i + 1) - pt i)‖ := by
            rw [sub_add_sub_cancel]
        _ ≤ ‖z₀ (i + 1) - pt (i + 1)‖ + ‖pt (i + 1) - pt i‖ := norm_add_le _ _
        _ ≤ 2 * e := by linarith
    have hB : segment ℝ (z₀ i) (z₀ (i + 1)) ⊆ closedBall (pt i) (2 * e) :=
      (convex_closedBall _ _).segment_subset
        (by rw [mem_closedBall, dist_eq_norm]; linarith)
        (by rw [mem_closedBall, dist_eq_norm]; exact h2')
    intro w hw
    have hwB := hB hw
    rw [mem_closedBall] at hwB
    refine ⟨hΩκΩ _ (hPext ((i : ℝ) / N)).1 (by rw [mem_closedBall]; linarith), fun t ht => ?_⟩
    have hfar := (hPext ((i : ℝ) / N)).2 t ht
    have htri := dist_triangle (pt i) w (γ t)
    rw [dist_comm (pt i) w] at htri
    have : dist (pt i) (γ t) = dist (P.extend ((i : ℝ) / N)) (γ t) := rfl
    linarith
  -- a shortest chain has fewer than `#F'` steps
  obtain ⟨n, z, hz0, hzn, hncard, -, hzseg⟩ :=
    exists_shortChain_lt_card (x := x) (y := y) F' (fun a b => segment ℝ a b ⊆ G)
      ⟨N, z₀, by simp [hz₀], by simp [hz₀, hN0], fun i hi => (hz₀pt i hi).1, hseg⟩
  refine ⟨n, z, hz0, hzn, ?_, fun i hi w hw => ?_⟩
  · -- the edge count
    have hcardF : F'.card ≤ (M + 1 - -M).toNat ^ d + 2 := by
      have h1 : F'.card ≤ (insert y (latticeBox d η M)).card + 1 := Finset.card_insert_le _ _
      have h2 := Finset.card_insert_le y (latticeBox d η M)
      have h3 := card_latticeBox_le (d := d) η M
      omega
    have hn1 : n ≤ (M + 1 - -M).toNat ^ d + 1 := by omega
    have hM0 : 0 ≤ M := Int.ceil_nonneg (by positivity)
    have hk : (((M + 1 - -M).toNat : ℕ) : ℝ) = 2 * (M : ℝ) + 1 := by
      rw [← Int.cast_natCast, Int.toNat_of_nonneg (by omega)]
      push_cast
      ring
    have hMlt : (M : ℝ) < R₀ / η + 1 := Int.ceil_lt_add_one _
    have hRη : R₀ / η * r = 4 * √(d : ℝ) * R₀ := by
      rw [hη, he]
      field_simp
    have hbase : 2 * (M : ℝ) + 1 ≤ (8 * √(d : ℝ) * R₀ + 3) / r := by
      rw [le_div_iff₀ hr0]
      have hr1 : r ≤ 1 := by linarith
      nlinarith
    have hpow : (2 * (M : ℝ) + 1) ^ d ≤
        ((8 * √(d : ℝ) * R₀ + 3) / c₂) ^ d * ((u ^ p) ^ d)⁻¹ := by
      calc (2 * (M : ℝ) + 1) ^ d ≤ ((8 * √(d : ℝ) * R₀ + 3) / r) ^ d :=
            pow_le_pow_left₀ (by positivity) hbase d
        _ = ((8 * √(d : ℝ) * R₀ + 3) / c₂) ^ d * ((u ^ p) ^ d)⁻¹ := by
            rw [hr, ← div_div, div_pow, div_eq_mul_inv]
    set U := u ^ (-((d : ℝ) / (α * β) ^ 2)) with hU
    have hupd : ((u ^ p) ^ d)⁻¹ = U := by
      rw [hU, Real.rpow_neg hu.le, ← Real.rpow_natCast, ← Real.rpow_mul hu.le, hp]
      congr 2
      ring
    have hU1 : 1 ≤ U := by
      rw [← hupd]
      have : (u ^ p) ^ d ≤ 1 := pow_le_one₀ (by positivity) (Real.rpow_le_one hu.le hu1 (by positivity))
      exact (one_le_inv₀ (by positivity)).2 this
    have hC : polygonalConst d A α β R₀ = ((8 * √(d : ℝ) * R₀ + 3) / c₂) ^ d + 2 := by
      rw [polygonalConst, ← hc₁, ← hp, ← hc₂]
    have hn1' : (n : ℝ) ≤ (2 * (M : ℝ) + 1) ^ d + 1 := by
      rw [← hk]
      exact_mod_cast hn1
    rw [hupd] at hpow
    rw [hC]
    calc (n : ℝ) ≤ ((8 * √(d : ℝ) * R₀ + 3) / c₂) ^ d * U + 1 := by linarith
      _ ≤ ((8 * √(d : ℝ) * R₀ + 3) / c₂) ^ d * U + 2 * U := by linarith
      _ = (((8 * √(d : ℝ) * R₀ + 3) / c₂) ^ d + 2) * U := by ring
  · -- the clearance
    obtain ⟨hwΩ, hwd⟩ := hzseg i hi hw
    refine ⟨hwΩ, fun t ht => ?_⟩
    have hc : polygonalClearanceConst A α β * u ^ p = r / 2 := by
      rw [polygonalClearanceConst, ← hc₁, ← hp, hr, hc₂]
      ring
    rw [hc]
    exact hwd t ht

/-- **Lemma 4.1′, polygonal form** (lattice discretization of the path of `lemma41_clearance`;
shortest chain on the lattice): at most `C u^{-C}` edges, clearance `c u^{1/(αβ)²}`. -/
theorem lemma41_polygonal (hd : 3 ≤ d) {A α β R₀ : ℝ} (hA : 1 ≤ A) (hα : 0 < α) (hα1 : α ≤ 1)
    (hβ : 0 < β) (hβ1 : β ≤ 1) (hR₀ : 0 < R₀) :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∀ γ : ℝ → Rd d, ArcModuli γ A α β →
    ∀ Ω : Set (Rd d), IsOpen Ω → Convex ℝ Ω → Ω ⊆ closedBall 0 R₀ → ∀ b₀ : ℝ, 0 < b₀ →
      (∀ t ∈ Icc (0 : ℝ) 1, closedBall (γ t) b₀ ⊆ Ω) →
    ∀ u : ℝ, 0 < u → u ≤ 1 → u ≤ b₀ / 2 → ∀ x y : Rd d,
      closedBall x u ⊆ Ω → closedBall y u ⊆ Ω →
      (∀ t ∈ Icc (0 : ℝ) 1, u ≤ dist x (γ t)) → (∀ t ∈ Icc (0 : ℝ) 1, u ≤ dist y (γ t)) →
      ∃ (n : ℕ) (z : ℕ → Rd d), z 0 = x ∧ z n = y ∧ (n : ℝ) ≤ C * u ^ (-C) ∧
        ∀ i < n, ∀ w ∈ segment ℝ (z i) (z (i + 1)), w ∈ Ω ∧
          ∀ t ∈ Icc (0 : ℝ) 1, c * u ^ ((α * β) ^ 2)⁻¹ ≤ dist w (γ t) := by
  have hA0 : 0 < A := by linarith
  set C₁ := polygonalConst d A α β R₀ with hC₁
  have hC₁ : 0 < C₁ := polygonalConst_pos hA0 hR₀.le
  set q := (d : ℝ) / (α * β) ^ 2 with hq
  refine ⟨polygonalClearanceConst A α β, max C₁ q, polygonalClearanceConst_pos hA0,
    lt_max_of_lt_left hC₁, fun γ hγ Ω hΩ hΩc hΩR b₀ _ hγΩ u hu hu1 hub x y hxΩ hyΩ hxu hyu => ?_⟩
  obtain ⟨n, z, hz0, hzn, hn, hseg⟩ := lemma41_polygonal_explicit hd hA hα hα1 hβ hβ1 hR₀ hγ hΩ
    hΩc hΩR hγΩ hu hu1 hub hxΩ hyΩ hxu hyu
  refine ⟨n, z, hz0, hzn, hn.trans ?_, hseg⟩
  rw [← hq]
  have hU : u ^ (-q) ≤ u ^ (-max C₁ q) :=
    Real.rpow_le_rpow_of_exponent_ge hu hu1 (neg_le_neg (le_max_right _ _))
  have hU0 : 0 ≤ u ^ (-q) := Real.rpow_nonneg hu.le _
  calc C₁ * u ^ (-q) ≤ max C₁ q * u ^ (-q) :=
        mul_le_mul_of_nonneg_right (le_max_left _ _) hU0
    _ ≤ max C₁ q * u ^ (-max C₁ q) :=
        mul_le_mul_of_nonneg_left hU (hC₁.le.trans (le_max_left _ _))

end HigherDimLQGContinuity.Topology

end
