import HigherDimLQGContinuity.Routing.LeadPaths

/-!
# Two leads in a reserved box (blueprint `b:lem-leads`)

Packet Q2 (ruling N9). Sources: planning audit `planning/audits/NA2-section-4.md`, §§1.4–1.5 and
Details (c) **R3**, **R4**; blueprint Part B, Lemma `b:lem-leads` ([C] p. 11–12, l. 566–601).

**Statement** (`exists_leads`, packet name `two_leads`). Let `d ≥ 3`, `R = m + [-L, L]^d ⊆ B̄₄`
(`0 < L ≤ 1`), `|u| = 1`, ports `p₀ = m - L u`, `p₁ = m + L u` on the grid `o + νℤ^d`, and an arc
`γ` with `ArcModuli γ A α β` (`A ≥ 1`, `α, β ∈ (0, 1]`) inside `B̄(m, L/32)`. Let `0 < t₀ ≤ 1/6`,
`r = leadR A α β L t₀`, `N = leadN d r`, and `ν > 0` with `ν ≤ c₀ (r/(4√d))/(2N + 5)³` and
`√d ν ≤ r`. Then there are two grid sequences `y₀` (from `p₀` to near `γ(0)`) and `y₁` (from `p₁` to
near `γ(1)`) satisfying `IsLead` ((L1)–(L5) of the blueprint, each lead avoiding `γ([t₀, 1])`,
resp. `γ([0, 1 - t₀])`, by `7r`), with pairwise distinct vertices and segments of different leads
at distance `≥ c₁ν³` (`c₁ = gpC1 4 = 1/100`).

**Proof.** `exists_prelead` (Lemma 4.1′ of packet Q1 applied to the truncated arcs of
`arcModuli_truncate`, with `u = u_lead`) gives the two paths, with clearance `10 r`. Moves
(`isLead_of_moves`): the vertices other than the ports and the attachments are pushed inward by the
homothety `resHom m (r/(√d L))` (displacement `≤ r`, coordinate margin `r/√d`); the attachments
`γ(0), γ(1)` are rounded to the grid (`gridRound`, `≤ √d ν/2`); the general-position core `gp_core`
on the index type `Fin (n₀ + 1) ⊕ Fin (n₁ + 1)` (fixed: the two ports and the two attachments) moves
the free vertices by `≤ r/(4√d)` onto the grid. Total displacement `≤ 2r` (clearance `10r - 2r`),
margins `≥ 3r/(4√d)` for free vertices, and the port incidence (L5) from the concavity of the
coordinate margin along the first segment (`dist_port_le`).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Metric
open HigherDimLFPP (Rd)
open HigherDimLQGContinuity.Topology (ArcModuli polygonalClearanceConst)

namespace HigherDimLQGContinuity.Routing

variable {d : ℕ}

/-- A point `m + c u` with `|c| ≤ L`, `|u| ≤ 1` lies in the box `m + [-L, L]^d`. -/
lemma add_smul_mem_resBox {m u : Rd d} {L c : ℝ} (hc : |c| ≤ L) (hu : ‖u‖ ≤ 1) :
    m + c • u ∈ resBox m L := by
  intro k
  have he : (m + c • u) k - m k = c * u k := by simp
  have huk : |u k| ≤ 1 := by
    have := abs_coord_sub_le_norm u 0 k
    simp only [PiLp.zero_apply, sub_zero] at this
    exact this.trans hu
  rw [he, abs_mul]
  nlinarith [abs_nonneg c, abs_nonneg (u k)]

/-- **One lead from its moves** (blueprint `b:lem-leads`, proof, "Moves" and (L5)): if the
pre-moves sequence `q` (port `q 0 = p`, endpoint `q n = g`, vertices in the box, clearance `10 r`)
is moved to `y` (port fixed, endpoint rounded to the grid, the other vertices within `r/(4√d)` of
their homothety images), and `y` has the general-position properties, then `y` is a lead. -/
theorem isLead_of_moves (hd : 1 ≤ d) {m p g o : Rd d} {L r ν : ℝ} {I : Set ℝ} {γ : ℝ → Rd d}
    {N n : ℕ} (hL : 0 < L) (hr : 0 < r) (hrL : r ≤ L / 160) (hr1 : r ≤ 1) (hν : 0 < ν)
    (hνr : √(d : ℝ) * ν ≤ r) (hn : 2 ≤ n) (hnN : n ≤ N) (hp : p ∈ resBox m L)
    (hg : ‖g - m‖ ≤ L / 32) {q : ℕ → Rd d} (hq0 : q 0 = p) (hqn : q n = g)
    (hqbox : ∀ j ≤ n, q j ∈ resBox m L)
    (hqclear : ∀ j < n, ∀ x ∈ segment ℝ (q j) (q (j + 1)), ∀ t ∈ I, 10 * r ≤ dist x (γ t))
    {y : ℕ → Rd d} (hy0 : y 0 = p) (hyn : y n = gridRound ν o g)
    (hyfree : ∀ j, 1 ≤ j → j < n →
      ‖y j - resHom m (r / (√(d : ℝ) * L)) (q j)‖ ≤ r / (4 * √(d : ℝ)))
    (hgrid : ∀ j ≤ n, OnGrid ν o (y j)) (hinj : ∀ j ≤ n, ∀ j' ≤ n, y j = y j' → j = j')
    (hsep : ∀ j j', j + 2 ≤ j' → j' < n → ∀ x ∈ segment ℝ (y j) (y (j + 1)),
      ∀ x' ∈ segment ℝ (y j') (y (j' + 1)), gpC1 4 * ν ^ 3 ≤ dist x x')
    (hinc : ∀ j, j + 1 < n →
      segment ℝ (y j) (y (j + 1)) ∩ segment ℝ (y (j + 1)) (y (j + 2)) = {y (j + 1)}) :
    IsLead m L p g I γ r ν o N n y := by
  set s := √(d : ℝ) with hsdef
  have hs1 : 1 ≤ s := by rw [hsdef, Real.one_le_sqrt]; exact_mod_cast hd
  have hs0 : 0 < s := by linarith
  have hss : s * s = d := Real.mul_self_sqrt (Nat.cast_nonneg d)
  set lam := r / (s * L) with hlamdef
  have hlam0 : 0 ≤ lam := by positivity
  have hlamL : lam * L = r / s := by rw [hlamdef]; field_simp
  have hlam1 : lam ≤ 1 := by
    rw [hlamdef, div_le_one (by positivity)]
    nlinarith
  have hround : ‖gridRound ν o g - g‖ ≤ r / 2 := by
    have := norm_gridRound_sub_le hν o g
    rw [← hsdef] at this
    linarith
  have hr4 : r / (4 * s) ≤ r / 4 := div_le_div_of_nonneg_left hr.le (by norm_num) (by linarith)
  -- margins of the free vertices (`3r/(4√d)`) and of the attachment
  have hmargin_free : ∀ j, 1 ≤ j → j < n → ∀ k, |y j k - m k| + 3 * r / (4 * s) ≤ L := by
    intro j hj1 hjn k
    have h1 := (abs_coord_sub_le_norm (y j) (resHom m lam (q j)) k).trans (hyfree j hj1 hjn)
    have h2 : |resHom m lam (q j) k - m k| ≤ L - r / s := by
      rw [resHom_coord, abs_mul, abs_of_nonneg (by linarith)]
      have := hqbox j hjn.le k
      nlinarith
    have h3 : |y j k - m k| ≤ |y j k - resHom m lam (q j) k| + |resHom m lam (q j) k - m k| := by
      have := abs_add_le (y j k - resHom m lam (q j) k) (resHom m lam (q j) k - m k)
      rwa [sub_add_sub_cancel] at this
    have h4 : r / (4 * s) + 3 * r / (4 * s) = r / s := by field_simp; ring
    linarith
  have hmargin_last : ∀ k, |y n k - m k| + r / (4 * s) ≤ L := by
    intro k
    have h1 : ‖y n - m‖ ≤ r / 2 + L / 32 := by
      rw [hyn]
      calc ‖gridRound ν o g - m‖ = ‖(gridRound ν o g - g) + (g - m)‖ := by congr 1; abel
        _ ≤ ‖gridRound ν o g - g‖ + ‖g - m‖ := norm_add_le _ _
        _ ≤ r / 2 + L / 32 := add_le_add hround hg
    have := (abs_coord_sub_le_norm (y n) m k).trans h1
    linarith
  have hmargin : ∀ j, 1 ≤ j → j ≤ n → ∀ k, |y j k - m k| + r / (4 * s) ≤ L := by
    intro j hj1 hjn k
    rcases Nat.lt_or_ge j n with h | h
    · have := hmargin_free j hj1 h k
      have : r / (4 * s) ≤ 3 * r / (4 * s) := div_le_div_of_nonneg_right (by linarith) (by positivity)
      linarith
    · rw [le_antisymm hjn h]; exact hmargin_last k
  have hbox : ∀ j ≤ n, y j ∈ resBox m L := by
    intro j hj k
    rcases Nat.eq_zero_or_pos j with h0 | h0
    · rw [h0, hy0]; exact hp k
    · have := hmargin j h0 hj k
      have : 0 ≤ r / (4 * s) := by positivity
      linarith
  -- displacement `≤ 2r`
  have hdisp : ∀ j ≤ n, ‖q j - y j‖ ≤ 2 * r := by
    intro j hj
    rcases Nat.eq_zero_or_pos j with h0 | h0
    · rw [h0, hq0, hy0, sub_self, norm_zero]; linarith
    rcases Nat.lt_or_ge j n with h | h
    · have h1 : ‖q j - resHom m lam (q j)‖ ≤ r := by
        rw [norm_sub_rev, norm_resHom_sub m hlam0]
        have := norm_sub_le_of_mem_resBox hL.le (hqbox j hj)
        rw [← hsdef] at this
        calc lam * ‖q j - m‖ ≤ lam * (s * L) := mul_le_mul_of_nonneg_left this hlam0
          _ = r := by rw [hlamdef]; field_simp
      have h2 : ‖resHom m lam (q j) - y j‖ ≤ r / 4 := by
        rw [norm_sub_rev]; exact (hyfree j h0 h).trans hr4
      calc ‖q j - y j‖ = ‖(q j - resHom m lam (q j)) + (resHom m lam (q j) - y j)‖ := by
            congr 1; abel
        _ ≤ ‖q j - resHom m lam (q j)‖ + ‖resHom m lam (q j) - y j‖ := norm_add_le _ _
        _ ≤ 2 * r := by linarith
    · rw [le_antisymm hj h, hqn, hyn, norm_sub_rev]; linarith
  refine
    { start := hy0
      two_le := hn
      le_N := hnN
      onGrid := hgrid
      mem_box := hbox
      attach := by rw [hyn]; exact norm_gridRound_sub_le hν o g
      clear := ?_
      margin := hmargin
      injOn := hinj
      sep := hsep
      inc := hinc
      port := ?_ }
  · -- (L2): clearance `10 r - 2 r`
    intro j hj x hx t ht
    obtain ⟨x', hx', hxx'⟩ := exists_mem_segment_near hx (hdisp j hj.le) (hdisp (j + 1) hj)
    have h1 := hqclear j hj x' hx' t ht
    have h2 : dist x' (γ t) ≤ dist x' x + dist x (γ t) := dist_triangle _ _ _
    rw [dist_comm x' x, dist_eq_norm x x'] at h2
    linarith
  · -- (L5): the port incidence
    intro ω hω hωr z ⟨j, hj, x, hx, hzx⟩ hz
    rcases Nat.eq_zero_or_pos j with h0 | h0
    · subst h0
      rw [hy0, zero_add] at hx
      have hμ : 0 < 3 * r / (4 * s) := by positivity
      have hmar1 : ∀ k, |y 1 k - m k| + 3 * r / (4 * s) ≤ L :=
        hmargin_free 1 le_rfl (by omega)
      have hdp := dist_port_le hp hmar1 hμ hx hzx hz
      have hy1p : ‖y 1 - p‖ ≤ s * (2 * L) := by
        have := norm_sub_le_of_mem_resBox₂ hL.le (hbox 1 (by omega)) hp
        rwa [← hsdef] at this
      have hω' : ω / (3 * r / (4 * s)) * ‖y 1 - p‖ ≤ 4 * d * L * ω / r := by
        have e1 : ω / (3 * r / (4 * s)) = 4 * s * ω / (3 * r) := by field_simp
        rw [e1]
        calc 4 * s * ω / (3 * r) * ‖y 1 - p‖ ≤ 4 * s * ω / (3 * r) * (s * (2 * L)) :=
              mul_le_mul_of_nonneg_left hy1p (by positivity)
          _ = 8 / 3 * (s * s) * L * ω / r := by field_simp; ring
          _ ≤ 4 * d * L * ω / r := by
              rw [hss]
              apply div_le_div_of_nonneg_right _ hr.le
              have : (0 : ℝ) ≤ d * L * ω := by positivity
              nlinarith
      have hωr' : ω ≤ ω / r := by
        rw [le_div_iff₀ hr]; nlinarith
      calc dist z p ≤ ω + ω / (3 * r / (4 * s)) * ‖y 1 - p‖ := hdp
        _ ≤ ω / r + 4 * d * L * ω / r := add_le_add hωr' hω'
        _ = (4 * d * L + 1) * ω / r := by ring
    · exfalso
      apply hz
      have hωμ : ω < r / (4 * s) := by
        calc ω ≤ r / (8 * s) := hωr
          _ < r / (4 * s) := div_lt_div_of_pos_left hr (by positivity) (by linarith)
      exact mem_resBoxInt_of_near_segment (hmargin j h0 hj.le) (hmargin (j + 1) (by omega) hj)
        hωμ hx hzx

/-- The homothety `resHom m λ`, `0 ≤ λ ≤ 1`, maps the box into itself. -/
lemma resHom_mem_resBox {m z : Rd d} {L lam : ℝ} (hlam0 : 0 ≤ lam) (hlam1 : lam ≤ 1)
    (hz : z ∈ resBox m L) : resHom m lam z ∈ resBox m L := by
  intro k
  rw [resHom_coord, abs_mul, abs_of_nonneg (by linarith)]
  have h1 := hz k
  have h2 : (1 - lam) * |z k - m k| ≤ 1 * |z k - m k| :=
    mul_le_mul_of_nonneg_right (by linarith) (abs_nonneg _)
  linarith

/-! ### General position for the two chains -/

/-- **General position for two chains** (step (4) of the moves of `b:lem-leads`): the free
vertices of two chains `z₀ 0, …, z₀ n₀` and `z₁ 0, …, z₁ n₁` (fixed: the four endpoints, distinct
grid points; all vertices in `B̄(0, 4)`) move by at most `δ ≤ 1` onto the grid, with distinct
vertices, nonconsecutive segments of one chain and segments of different chains at distance
`≥ c₁ν³` (`c₁ = gpC1 4`), and consecutive segments meeting only at their common vertex. -/
theorem exists_gp_two_chains (hd : 3 ≤ d) {n₀ n₁ : ℕ} (hn₀ : 2 ≤ n₀) (hn₁ : 2 ≤ n₁) {ν δ : ℝ}
    (o : Rd d) (hν : 0 < ν) (hδ1 : δ ≤ 1)
    (hcore : √(d : ℝ) * ν * ((((n₀ + 1 + (n₁ + 1) : ℕ) : ℝ)) ^ 3 + 1) ≤ δ)
    (z₀ z₁ : ℕ → Rd d) (hz₀ : ∀ j ≤ n₀, ‖z₀ j‖ ≤ 4) (hz₁ : ∀ j ≤ n₁, ‖z₁ j‖ ≤ 4)
    (hg₀ : OnGrid ν o (z₀ 0)) (hg₀' : OnGrid ν o (z₀ n₀)) (hg₁ : OnGrid ν o (z₁ 0))
    (hg₁' : OnGrid ν o (z₁ n₁)) (h01 : z₀ 0 ≠ z₀ n₀) (h02 : z₀ 0 ≠ z₁ 0) (h03 : z₀ 0 ≠ z₁ n₁)
    (h12 : z₀ n₀ ≠ z₁ 0) (h13 : z₀ n₀ ≠ z₁ n₁) (h23 : z₁ 0 ≠ z₁ n₁) :
    ∃ y₀ y₁ : ℕ → Rd d, y₀ 0 = z₀ 0 ∧ y₀ n₀ = z₀ n₀ ∧ y₁ 0 = z₁ 0 ∧ y₁ n₁ = z₁ n₁ ∧
      (∀ j ≤ n₀, ‖y₀ j - z₀ j‖ ≤ δ) ∧ (∀ j ≤ n₁, ‖y₁ j - z₁ j‖ ≤ δ) ∧
      (∀ j ≤ n₀, OnGrid ν o (y₀ j)) ∧ (∀ j ≤ n₁, OnGrid ν o (y₁ j)) ∧
      (∀ j ≤ n₀, ∀ j' ≤ n₀, y₀ j = y₀ j' → j = j') ∧
      (∀ j ≤ n₁, ∀ j' ≤ n₁, y₁ j = y₁ j' → j = j') ∧
      (∀ j ≤ n₀, ∀ j' ≤ n₁, y₀ j ≠ y₁ j') ∧
      (∀ j j', j + 2 ≤ j' → j' < n₀ → ∀ x ∈ segment ℝ (y₀ j) (y₀ (j + 1)),
        ∀ x' ∈ segment ℝ (y₀ j') (y₀ (j' + 1)), gpC1 4 * ν ^ 3 ≤ dist x x') ∧
      (∀ j j', j + 2 ≤ j' → j' < n₁ → ∀ x ∈ segment ℝ (y₁ j) (y₁ (j + 1)),
        ∀ x' ∈ segment ℝ (y₁ j') (y₁ (j' + 1)), gpC1 4 * ν ^ 3 ≤ dist x x') ∧
      (∀ j, j + 1 < n₀ →
        segment ℝ (y₀ j) (y₀ (j + 1)) ∩ segment ℝ (y₀ (j + 1)) (y₀ (j + 2)) = {y₀ (j + 1)}) ∧
      (∀ j, j + 1 < n₁ →
        segment ℝ (y₁ j) (y₁ (j + 1)) ∩ segment ℝ (y₁ (j + 1)) (y₁ (j + 2)) = {y₁ (j + 1)}) ∧
      (∀ j < n₀, ∀ j' < n₁, ∀ x ∈ segment ℝ (y₀ j) (y₀ (j + 1)),
        ∀ x' ∈ segment ℝ (y₁ j') (y₁ (j' + 1)), gpC1 4 * ν ^ 3 ≤ dist x x') := by
  classical
  let v : Fin (n₀ + 1) ⊕ Fin (n₁ + 1) → Rd d := Sum.elim (fun j => z₀ j) (fun j => z₁ j)
  let F : Finset (Fin (n₀ + 1) ⊕ Fin (n₁ + 1)) :=
    {Sum.inl 0, Sum.inl (Fin.last n₀), Sum.inr 0, Sum.inr (Fin.last n₁)}
  have hFl : ∀ j : Fin (n₀ + 1), Sum.inl j ∈ F ↔ ((j : ℕ) = 0 ∨ (j : ℕ) = n₀) := by
    intro j
    simp only [F, Finset.mem_insert, Finset.mem_singleton, Sum.inl.injEq, reduceCtorEq, or_false,
      Fin.ext_iff, Fin.val_zero, Fin.val_last]
  have hFr : ∀ j : Fin (n₁ + 1), Sum.inr j ∈ F ↔ ((j : ℕ) = 0 ∨ (j : ℕ) = n₁) := by
    intro j
    simp only [F, Finset.mem_insert, Finset.mem_singleton, Sum.inr.injEq, reduceCtorEq, false_or,
      Fin.ext_iff, Fin.val_zero, Fin.val_last]
  have hv0l : v (Sum.inl 0) = z₀ 0 := by simp [v]
  have hvLl : v (Sum.inl (Fin.last n₀)) = z₀ n₀ := by simp [v]
  have hv0r : v (Sum.inr 0) = z₁ 0 := by simp [v]
  have hvLr : v (Sum.inr (Fin.last n₁)) = z₁ n₁ := by simp [v]
  have hFcases : ∀ i ∈ F, i = Sum.inl 0 ∨ i = Sum.inl (Fin.last n₀) ∨ i = Sum.inr 0 ∨
      i = Sum.inr (Fin.last n₁) := by
    intro i hi
    simpa only [F, Finset.mem_insert, Finset.mem_singleton] using hi
  have hFgrid : ∀ i ∈ F, OnGrid ν o (v i) := by
    intro i hi
    rcases hFcases i hi with rfl | rfl | rfl | rfl
    · rw [hv0l]; exact hg₀
    · rw [hvLl]; exact hg₀'
    · rw [hv0r]; exact hg₁
    · rw [hvLr]; exact hg₁'
  have hFinj : Set.InjOn v F := by
    intro i hi j hj hij
    rcases hFcases i hi with rfl | rfl | rfl | rfl <;>
      rcases hFcases j hj with rfl | rfl | rfl | rfl <;>
      simp only [hv0l, hvLl, hv0r, hvLr] at hij <;>
      first
      | rfl
      | exact absurd hij h01 | exact absurd hij.symm h01
      | exact absurd hij h02 | exact absurd hij.symm h02
      | exact absurd hij h03 | exact absurd hij.symm h03
      | exact absurd hij h12 | exact absurd hij.symm h12
      | exact absurd hij h13 | exact absurd hij.symm h13
      | exact absurd hij h23 | exact absurd hij.symm h23
  have hcore' : √(d : ℝ) * ν *
      ((Fintype.card (Fin (n₀ + 1) ⊕ Fin (n₁ + 1)) : ℝ) ^ 3 + 1) ≤ δ := by
    rw [Fintype.card_sum, Fintype.card_fin, Fintype.card_fin]
    exact hcore
  obtain ⟨w, hwF, hwv, hwg, hwI⟩ := gp_core hd v F o hν hcore' hFgrid hFinj
  have hwinj : Function.Injective w := hwI.injective
  have hwB : ∀ i, ‖w i‖ ≤ 4 + 1 := by
    intro i
    have h1 : ‖v i‖ ≤ 4 := by
      rcases i with j | j
      · exact hz₀ j (by omega)
      · exact hz₁ j (by omega)
    have h2 : ‖w i‖ ≤ ‖v i‖ + ‖w i - v i‖ := by
      calc ‖w i‖ = ‖v i + (w i - v i)‖ := by congr 1; abel
        _ ≤ _ := norm_add_le _ _
    linarith [hwv i]
  -- the index maps
  let e₀ : ℕ → Fin (n₀ + 1) ⊕ Fin (n₁ + 1) := fun j =>
    if h : j < n₀ + 1 then Sum.inl ⟨j, h⟩ else Sum.inl 0
  let e₁ : ℕ → Fin (n₀ + 1) ⊕ Fin (n₁ + 1) := fun j =>
    if h : j < n₁ + 1 then Sum.inr ⟨j, h⟩ else Sum.inr 0
  have he₀ : ∀ j (h : j ≤ n₀), e₀ j = Sum.inl ⟨j, by omega⟩ := fun j h => by
    simp only [e₀, show j < n₀ + 1 by omega, ↓reduceDIte]
  have he₁ : ∀ j (h : j ≤ n₁), e₁ j = Sum.inr ⟨j, by omega⟩ := fun j h => by
    simp only [e₁, show j < n₁ + 1 by omega, ↓reduceDIte]
  have hve₀ : ∀ j ≤ n₀, v (e₀ j) = z₀ j := fun j hj => by rw [he₀ j hj]; rfl
  have hve₁ : ∀ j ≤ n₁, v (e₁ j) = z₁ j := fun j hj => by rw [he₁ j hj]; rfl
  have he₀inj : ∀ j ≤ n₀, ∀ j' ≤ n₀, e₀ j = e₀ j' → j = j' := by
    intro j hj j' hj' h
    rw [he₀ j hj, he₀ j' hj', Sum.inl.injEq, Fin.mk.injEq] at h
    exact h
  have he₁inj : ∀ j ≤ n₁, ∀ j' ≤ n₁, e₁ j = e₁ j' → j = j' := by
    intro j hj j' hj' h
    rw [he₁ j hj, he₁ j' hj', Sum.inr.injEq, Fin.mk.injEq] at h
    exact h
  have he₀₁ : ∀ j ≤ n₀, ∀ j' ≤ n₁, e₀ j ≠ e₁ j' := by
    intro j hj j' hj' h
    rw [he₀ j hj, he₁ j' hj'] at h
    exact Sum.inl_ne_inr h
  have he₀F : ∀ j, 1 ≤ j → j < n₀ → e₀ j ∉ F := by
    intro j h1 h2
    rw [he₀ j h2.le, hFl]
    simp only
    omega
  have he₁F : ∀ j, 1 ≤ j → j < n₁ → e₁ j ∉ F := by
    intro j h1 h2
    rw [he₁ j h2.le, hFr]
    simp only
    omega
  have hfree₀ : ∀ j < n₀, e₀ j ∉ F ∨ e₀ (j + 1) ∉ F := by
    intro j hj
    rcases Nat.eq_zero_or_pos j with h0 | h0
    · right; exact he₀F (j + 1) (by omega) (by omega)
    · left; exact he₀F j h0 hj
  have hfree₁ : ∀ j < n₁, e₁ j ∉ F ∨ e₁ (j + 1) ∉ F := by
    intro j hj
    rcases Nat.eq_zero_or_pos j with h0 | h0
    · right; exact he₁F (j + 1) (by omega) (by omega)
    · left; exact he₁F j h0 hj
  have he₀0 : e₀ 0 = Sum.inl 0 := by rw [he₀ 0 (by omega)]; rfl
  have he₀n : e₀ n₀ = Sum.inl (Fin.last n₀) := by rw [he₀ n₀ le_rfl]; rfl
  have he₁0 : e₁ 0 = Sum.inr 0 := by rw [he₁ 0 (by omega)]; rfl
  have he₁n : e₁ n₁ = Sum.inr (Fin.last n₁) := by rw [he₁ n₁ le_rfl]; rfl
  have hmemF : ∀ {i}, i = Sum.inl 0 ∨ i = Sum.inl (Fin.last n₀) ∨ i = Sum.inr 0 ∨
      i = Sum.inr (Fin.last n₁) → i ∈ F := by
    intro i hi
    simp only [F, Finset.mem_insert, Finset.mem_singleton]
    exact hi
  have hsepw := fun {i j k l} => hwI.segment_sep (R₀ := 4) hν (by norm_num) hwg hwB
    (i := i) (j := j) (k := k) (l := l)
  have hne₀ : ∀ {j j'}, j ≤ n₀ → j' ≤ n₀ → j ≠ j' → e₀ j ≠ e₀ j' :=
    fun hj hj' h he => h (he₀inj _ hj _ hj' he)
  have hne₁ : ∀ {j j'}, j ≤ n₁ → j' ≤ n₁ → j ≠ j' → e₁ j ≠ e₁ j' :=
    fun hj hj' h he => h (he₁inj _ hj _ hj' he)
  refine ⟨fun j => w (e₀ j), fun j => w (e₁ j), ?_, ?_, ?_, ?_, fun j hj => ?_, fun j hj => ?_,
    fun j _ => hwg _, fun j _ => hwg _, fun j hj j' hj' h => he₀inj j hj j' hj' (hwinj h),
    fun j hj j' hj' h => he₁inj j hj j' hj' (hwinj h),
    fun j hj j' hj' h => he₀₁ j hj j' hj' (hwinj h), ?_, ?_, ?_, ?_, ?_⟩
  · show w (e₀ 0) = z₀ 0
    rw [he₀0, hwF _ (hmemF (Or.inl rfl)), hv0l]
  · show w (e₀ n₀) = z₀ n₀
    rw [he₀n, hwF _ (hmemF (Or.inr (Or.inl rfl))), hvLl]
  · show w (e₁ 0) = z₁ 0
    rw [he₁0, hwF _ (hmemF (Or.inr (Or.inr (Or.inl rfl)))), hv0r]
  · show w (e₁ n₁) = z₁ n₁
    rw [he₁n, hwF _ (hmemF (Or.inr (Or.inr (Or.inr rfl)))), hvLr]
  · show ‖w (e₀ j) - z₀ j‖ ≤ δ
    rw [← hve₀ j hj]; exact hwv _
  · show ‖w (e₁ j) - z₁ j‖ ≤ δ
    rw [← hve₁ j hj]; exact hwv _
  · intro j j' hjj' hj' x hx x' hx'
    exact hsepw (hne₀ (by omega) (by omega) (by omega)) (hne₀ (by omega) (by omega) (by omega))
      (hne₀ (by omega) (by omega) (by omega)) (hne₀ (by omega) (by omega) (by omega))
      (hne₀ (by omega) (by omega) (by omega)) (hne₀ (by omega) (by omega) (by omega))
      (hfree₀ j (by omega)) (hfree₀ j' hj') x hx x' hx'
  · intro j j' hjj' hj' x hx x' hx'
    exact hsepw (hne₁ (by omega) (by omega) (by omega)) (hne₁ (by omega) (by omega) (by omega))
      (hne₁ (by omega) (by omega) (by omega)) (hne₁ (by omega) (by omega) (by omega))
      (hne₁ (by omega) (by omega) (by omega)) (hne₁ (by omega) (by omega) (by omega))
      (hfree₁ j (by omega)) (hfree₁ j' hj') x hx x' hx'
  · intro j hj
    exact hwI.segment_inter (hne₀ (by omega) (by omega) (by omega))
      (hne₀ (by omega) (by omega) (by omega)) (hne₀ (by omega) (by omega) (by omega))
      (Or.inr (Or.inl (he₀F (j + 1) (by omega) hj)))
  · intro j hj
    exact hwI.segment_inter (hne₁ (by omega) (by omega) (by omega))
      (hne₁ (by omega) (by omega) (by omega)) (hne₁ (by omega) (by omega) (by omega))
      (Or.inr (Or.inl (he₁F (j + 1) (by omega) hj)))
  · intro j hj j' hj' x hx x' hx'
    exact hsepw (hne₀ (by omega) (by omega) (by omega)) (he₀₁ j hj.le j' hj'.le)
      (he₀₁ j hj.le (j' + 1) hj') (he₀₁ (j + 1) hj j' hj'.le) (he₀₁ (j + 1) hj (j' + 1) hj')
      (hne₁ (by omega) (by omega) (by omega)) (hfree₀ j hj) (hfree₁ j' hj') x hx x' hx'

/-! ### The two pre-paths -/

section Prepaths

variable {A α β L t₀ : ℝ}

/-- An edge count bounded by the polygonal constant gives `k + 1 ≤ N`. -/
lemma succ_le_leadN (hd : 1 ≤ d) (hA : 1 ≤ A) (hα : 0 < α) (hβ : 0 < β) (ht₀ : 0 < t₀)
    (hL : 0 < L) {k : ℕ}
    (hk : (k : ℝ) ≤ Topology.polygonalConst d (2 * A) α β 4 *
      leadU A β L t₀ ^ (-((d : ℝ) / (α * β) ^ 2))) :
    k + 1 ≤ leadN d (leadR A α β L t₀) := by
  have := Nat.le_floor (hk.trans (polygonal_count_le hd hA hα hβ ht₀ hL))
  rw [leadN]
  omega

/-- The clearance of the pre-paths in terms of `r`: `c₄₁′ u_lead^{1/(αβ)²} = 10 r`. -/
lemma polygonalClearance_eq_ten_leadR :
    polygonalClearanceConst (2 * A) α β * leadU A β L t₀ ^ ((α * β) ^ 2)⁻¹ =
      10 * leadR A α β L t₀ := by
  rw [leadR]; ring

/-- The pre-path of the first lead (port `m - L u`, endpoint `γ(0)`, clearance `10 r` from
`γ([t₀, 1])`). -/
lemma exists_prelead₀ (hd : 3 ≤ d) (hA : 1 ≤ A) (hα : 0 < α) (hα1 : α ≤ 1) (hβ : 0 < β)
    (hβ1 : β ≤ 1) {m : Rd d} (hL : 0 < L) (hL1 : L ≤ 1) (hbox : resBox m L ⊆ closedBall 0 4)
    {u : Rd d} (hu : ‖u‖ = 1) {γ : ℝ → Rd d} (hγ : ArcModuli γ A α β)
    (hγm : ∀ t ∈ Icc (0 : ℝ) 1, γ t ∈ closedBall m (L / 32)) (ht₀ : 0 < t₀) (ht₀' : t₀ ≤ 1 / 6) :
    ∃ (n : ℕ) (q : ℕ → Rd d), q 0 = m - L • u ∧ q n = γ 0 ∧ 2 ≤ n ∧
      n ≤ leadN d (leadR A α β L t₀) ∧ (∀ j ≤ n, q j ∈ resBox m L) ∧
      (∀ j < n, ∀ x ∈ segment ℝ (q j) (q (j + 1)), ∀ t ∈ Icc t₀ 1,
        10 * leadR A α β L t₀ ≤ dist x (γ t)) := by
  have hA0 : 0 < A := by linarith
  have ht₁ : 0 < 1 - t₀ := by linarith
  have hη := (arcModuli_truncate hγ hA0.le hα ht₀ (by linarith)).1
  have hmem : ∀ ς ∈ Icc (0 : ℝ) 1, t₀ + ς * (1 - t₀) ∈ Icc t₀ 1 := fun ς hς =>
    ⟨by nlinarith [hς.1], by nlinarith [hς.2]⟩
  have hI : ∀ t ∈ Icc t₀ 1, t ∈ Icc (0 : ℝ) 1 := fun t ht => ⟨by linarith [ht.1], ht.2⟩
  have hUA : leadU A β L t₀ ≤ (t₀ / A) ^ β⁻¹ :=
    leadU_le_pow.trans (Real.rpow_le_rpow (by positivity)
      (div_le_div_of_nonneg_left ht₀.le hA0 (by linarith)) (by positivity))
  obtain ⟨k, q, hq0, -, hqe, hk1, hk, hqbox, -, hqclear⟩ :=
    exists_prelead hd hA hα hα1 hβ hβ1 hL hL1 hbox hu hη
      (fun ς hς => hγm _ (hI _ (hmem ς hς))) (hγm 0 ⟨le_rfl, zero_le_one⟩)
      (leadU_pos hA0 ht₀ hL) leadU_le_L (fun ς hς => by
        have := arcModuli_endpoint_sep_zero hγ hA0 hβ ht₀.le (hmem ς hς)
        rw [dist_eq_norm]; linarith)
  refine ⟨k + 1, q, hq0, hqe, by omega, succ_le_leadN (by omega) hA hα hβ ht₀ hL hk, hqbox,
    fun j hj x hx t ht => ?_⟩
  have hς : (t - t₀) / (1 - t₀) ∈ Icc (0 : ℝ) 1 :=
    ⟨div_nonneg (by linarith [ht.1]) ht₁.le, (div_le_one ht₁).2 (by linarith [ht.2])⟩
  have h := hqclear j hj x hx _ hς
  have he : t₀ + (t - t₀) / (1 - t₀) * (1 - t₀) = t := by field_simp; ring
  rwa [polygonalClearance_eq_ten_leadR, he] at h

/-- The pre-path of the second lead (port `m + L u`, endpoint `γ(1)`, clearance `10 r` from
`γ([0, 1 - t₀])`). -/
lemma exists_prelead₁ (hd : 3 ≤ d) (hA : 1 ≤ A) (hα : 0 < α) (hα1 : α ≤ 1) (hβ : 0 < β)
    (hβ1 : β ≤ 1) {m : Rd d} (hL : 0 < L) (hL1 : L ≤ 1) (hbox : resBox m L ⊆ closedBall 0 4)
    {u : Rd d} (hu : ‖u‖ = 1) {γ : ℝ → Rd d} (hγ : ArcModuli γ A α β)
    (hγm : ∀ t ∈ Icc (0 : ℝ) 1, γ t ∈ closedBall m (L / 32)) (ht₀ : 0 < t₀) (ht₀' : t₀ ≤ 1 / 6) :
    ∃ (n : ℕ) (q : ℕ → Rd d), q 0 = m + L • u ∧ q n = γ 1 ∧ 2 ≤ n ∧
      n ≤ leadN d (leadR A α β L t₀) ∧ (∀ j ≤ n, q j ∈ resBox m L) ∧
      (∀ j < n, ∀ x ∈ segment ℝ (q j) (q (j + 1)), ∀ t ∈ Icc 0 (1 - t₀),
        10 * leadR A α β L t₀ ≤ dist x (γ t)) := by
  have hA0 : 0 < A := by linarith
  have ht₁ : 0 < 1 - t₀ := by linarith
  have hη := (arcModuli_truncate hγ hA0.le hα ht₀ (by linarith)).2
  have hmem : ∀ ς ∈ Icc (0 : ℝ) 1, ς * (1 - t₀) ∈ Icc 0 (1 - t₀) := fun ς hς =>
    ⟨by nlinarith [hς.1], by nlinarith [hς.2]⟩
  have hI : ∀ t ∈ Icc 0 (1 - t₀), t ∈ Icc (0 : ℝ) 1 := fun t ht => ⟨ht.1, by linarith [ht.2]⟩
  have hUA : leadU A β L t₀ ≤ (t₀ / A) ^ β⁻¹ :=
    leadU_le_pow.trans (Real.rpow_le_rpow (by positivity)
      (div_le_div_of_nonneg_left ht₀.le hA0 (by linarith)) (by positivity))
  have hu' : ‖-u‖ = 1 := by rw [norm_neg, hu]
  obtain ⟨k, q, hq0, -, hqe, hk1, hk, hqbox, -, hqclear⟩ :=
    exists_prelead hd hA hα hα1 hβ hβ1 hL hL1 hbox hu' hη
      (fun ς hς => hγm _ (hI _ (hmem ς hς))) (hγm 1 ⟨zero_le_one, le_rfl⟩)
      (leadU_pos hA0 ht₀ hL) leadU_le_L (fun ς hς => by
        have := arcModuli_endpoint_sep_one hγ hA0 hβ ht₀.le (hmem ς hς)
        rw [dist_eq_norm]; linarith)
  rw [smul_neg, sub_neg_eq_add] at hq0
  refine ⟨k + 1, q, hq0, hqe, by omega, succ_le_leadN (by omega) hA hα hβ ht₀ hL hk, hqbox,
    fun j hj x hx t ht => ?_⟩
  have hς : t / (1 - t₀) ∈ Icc (0 : ℝ) 1 := ⟨div_nonneg ht.1 ht₁.le, (div_le_one ht₁).2 ht.2⟩
  have h := hqclear j hj x hx _ hς
  have he : t / (1 - t₀) * (1 - t₀) = t := by field_simp
  rwa [polygonalClearance_eq_ten_leadR, he] at h

/-- `r < (1/A)^{1/β}`: the arc endpoints, at distance `≥ (1/A)^{1/β}`, are far apart at scale `r`. -/
lemma leadR_lt (hA : 1 ≤ A) (hα : 0 < α) (hα1 : α ≤ 1) (hβ : 0 < β) (hβ1 : β ≤ 1)
    (ht₀ : 0 < t₀) (ht₀' : t₀ ≤ 2) (hL : 0 < L) (hL1 : L ≤ 1) :
    leadR A α β L t₀ < (1 / A) ^ β⁻¹ := by
  have hA0 : 0 < A := by linarith
  have h10 := ten_leadR_le hA hα hα1 hβ hβ1 ht₀ hL hL1
  have hr0 := leadR_pos (α := α) (β := β) hA ht₀ hL
  have hU : leadU A β L t₀ ≤ (1 / A) ^ β⁻¹ :=
    leadU_le_pow.trans (Real.rpow_le_rpow (by positivity)
      (by rw [div_le_div_iff₀ (by positivity) hA0]; nlinarith) (by positivity))
  have hpos : 0 < (1 / A) ^ β⁻¹ := Real.rpow_pos_of_pos (by positivity) _
  linarith

end Prepaths

/-! ### The fixed points -/

/-- The ports and the rounded attachments are four distinct grid points in the box. -/
lemma leads_endpoints {A α β : ℝ} (hA : 0 < A) (hβ : 0 < β) {m u o : Rd d}
    {L r ν : ℝ} (hL : 0 < L) (hu : ‖u‖ = 1) {γ : ℝ → Rd d} (hγ : ArcModuli γ A α β)
    (hγm : ∀ t ∈ Icc (0 : ℝ) 1, γ t ∈ closedBall m (L / 32)) (hν : 0 < ν)
    (hνr : √(d : ℝ) * ν ≤ r) (hrL : r ≤ L / 160) (hrA : r < (1 / A) ^ β⁻¹) :
    m - L • u ∈ resBox m L ∧ m + L • u ∈ resBox m L ∧
      gridRound ν o (γ 0) ∈ resBox m L ∧ gridRound ν o (γ 1) ∈ resBox m L ∧
      m - L • u ≠ gridRound ν o (γ 0) ∧ m - L • u ≠ m + L • u ∧
      m - L • u ≠ gridRound ν o (γ 1) ∧ gridRound ν o (γ 0) ≠ m + L • u ∧
      gridRound ν o (γ 0) ≠ gridRound ν o (γ 1) ∧ m + L • u ≠ gridRound ν o (γ 1) := by
  have hround : ∀ x : Rd d, ‖gridRound ν o x - x‖ ≤ r / 2 := fun x => by
    have := norm_gridRound_sub_le hν o x; linarith
  have h0I : (0 : ℝ) ∈ Icc (0 : ℝ) 1 := ⟨le_rfl, zero_le_one⟩
  have h1I : (1 : ℝ) ∈ Icc (0 : ℝ) 1 := ⟨zero_le_one, le_rfl⟩
  have hp₀box : m - L • u ∈ resBox m L := by
    rw [sub_eq_add_neg, ← neg_smul]
    exact add_smul_mem_resBox (by rw [abs_neg, abs_of_pos hL]) hu.le
  have hp₁box : m + L • u ∈ resBox m L := add_smul_mem_resBox (by rw [abs_of_pos hL]) hu.le
  have hp₀m : ‖m - L • u - m‖ = L := by
    rw [sub_sub_cancel_left, norm_neg, norm_smul, hu, mul_one, Real.norm_of_nonneg hL.le]
  have hp₁m : ‖m + L • u - m‖ = L := by
    rw [add_sub_cancel_left, norm_smul, hu, mul_one, Real.norm_of_nonneg hL.le]
  have ham : ∀ t ∈ Icc (0 : ℝ) 1, ‖gridRound ν o (γ t) - m‖ < L := fun t ht => by
    have h2 : ‖γ t - m‖ ≤ L / 32 := by rw [← dist_eq_norm]; exact hγm t ht
    calc ‖gridRound ν o (γ t) - m‖ = ‖(gridRound ν o (γ t) - γ t) + (γ t - m)‖ := by
          congr 1; abel
      _ ≤ ‖gridRound ν o (γ t) - γ t‖ + ‖γ t - m‖ := norm_add_le _ _
      _ < L := by linarith [hround (γ t)]
  have hne : ∀ {x y : Rd d}, ‖x - m‖ = L → ‖y - m‖ < L → x ≠ y := by
    intro x y hx hy hxy; rw [hxy] at hx; linarith
  have hp₀p₁ : m - L • u ≠ m + L • u := by
    intro h
    have : m + L • u - (m - L • u) = (2 * L) • u := by module
    rw [h, sub_self] at this
    have h2 := congrArg norm this
    rw [norm_zero, norm_smul, hu, mul_one, Real.norm_of_nonneg (by linarith)] at h2
    linarith
  have ha₀a₁ : gridRound ν o (γ 0) ≠ gridRound ν o (γ 1) := by
    intro h
    have hsep := arcModuli_le_norm_sub hγ hA hβ h0I h1I
    rw [zero_sub, abs_neg, abs_one] at hsep
    have hle : ‖γ 0 - γ 1‖ ≤ r := by
      calc ‖γ 0 - γ 1‖ = ‖(γ 0 - gridRound ν o (γ 0)) + (gridRound ν o (γ 1) - γ 1)‖ := by
            rw [h]; congr 1; abel
        _ ≤ ‖γ 0 - gridRound ν o (γ 0)‖ + ‖gridRound ν o (γ 1) - γ 1‖ := norm_add_le _ _
        _ ≤ r := by rw [norm_sub_rev]; linarith [hround (γ 0), hround (γ 1)]
    linarith
  exact ⟨hp₀box, hp₁box, resBoxInt_subset_resBox m L (mem_resBoxInt_of_norm_lt (ham 0 h0I)),
    resBoxInt_subset_resBox m L (mem_resBoxInt_of_norm_lt (ham 1 h1I)),
    hne hp₀m (ham 0 h0I), hp₀p₁, hne hp₀m (ham 1 h1I), fun h => hne hp₁m (ham 0 h0I) h.symm,
    ha₀a₁, hne hp₁m (ham 1 h1I)⟩

/-! ### Two leads -/

/-- **Two leads in a reserved box** (blueprint `b:lem-leads`; R3, R4; `d ≥ 3`). -/
theorem exists_leads (hd : 3 ≤ d) {A α β : ℝ} (hA : 1 ≤ A) (hα : 0 < α) (hα1 : α ≤ 1)
    (hβ : 0 < β) (hβ1 : β ≤ 1) {m : Rd d} {L : ℝ} (hL : 0 < L) (hL1 : L ≤ 1)
    (hbox : resBox m L ⊆ closedBall 0 4) {u : Rd d} (hu : ‖u‖ = 1) {ν : ℝ} {o : Rd d}
    (hν : 0 < ν) (hp₀ : OnGrid ν o (m - L • u)) (hp₁ : OnGrid ν o (m + L • u))
    {γ : ℝ → Rd d} (hγ : ArcModuli γ A α β)
    (hγm : ∀ t ∈ Icc (0 : ℝ) 1, γ t ∈ closedBall m (L / 32)) {t₀ : ℝ} (ht₀ : 0 < t₀)
    (ht₀' : t₀ ≤ 1 / 6)
    (hνN : ν ≤ gpC0 d * (leadR A α β L t₀ / (4 * √(d : ℝ))) /
      (2 * (leadN d (leadR A α β L t₀) : ℝ) + 5) ^ 3)
    (hνr : √(d : ℝ) * ν ≤ leadR A α β L t₀) :
    ∃ (n₀ n₁ : ℕ) (y₀ y₁ : ℕ → Rd d),
      IsLead m L (m - L • u) (γ 0) (Icc t₀ 1) γ (leadR A α β L t₀) ν o
        (leadN d (leadR A α β L t₀)) n₀ y₀ ∧
      IsLead m L (m + L • u) (γ 1) (Icc 0 (1 - t₀)) γ (leadR A α β L t₀) ν o
        (leadN d (leadR A α β L t₀)) n₁ y₁ ∧
      (∀ j ≤ n₀, ∀ j' ≤ n₁, y₀ j ≠ y₁ j') ∧
      (∀ j < n₀, ∀ j' < n₁, ∀ x ∈ segment ℝ (y₀ j) (y₀ (j + 1)),
        ∀ x' ∈ segment ℝ (y₁ j') (y₁ (j' + 1)), gpC1 4 * ν ^ 3 ≤ dist x x') := by
  have hA0 : 0 < A := by linarith
  have hd1 : 1 ≤ d := by omega
  obtain ⟨n₀, q₀, hq₀0, hq₀n, hn₀2, hn₀N, hq₀box, hq₀clear⟩ :=
    exists_prelead₀ hd hA hα hα1 hβ hβ1 hL hL1 hbox hu hγ hγm ht₀ ht₀'
  obtain ⟨n₁, q₁, hq₁0, hq₁n, hn₁2, hn₁N, hq₁box, hq₁clear⟩ :=
    exists_prelead₁ hd hA hα hα1 hβ hβ1 hL hL1 hbox hu hγ hγm ht₀ ht₀'
  set r := leadR A α β L t₀ with hrdef
  set N := leadN d r with hNdef
  have hr0 : 0 < r := leadR_pos hA ht₀ hL
  have hrL : r ≤ L / 160 := leadR_le_L hA hα hα1 hβ hβ1 ht₀ hL hL1
  have hr1 : r ≤ 1 := by linarith
  obtain ⟨hp₀box, hp₁box, ha₀box, ha₁box, h01, h02, h03, h12, h13, h23⟩ :=
    leads_endpoints (o := o) hA0 hβ hL hu hγ hγm hν hνr hrL
      (leadR_lt hA hα hα1 hβ hβ1 ht₀ (by linarith) hL hL1)
  have hs0 : 0 < √(d : ℝ) := Real.sqrt_pos.2 (by exact_mod_cast (show 0 < d by omega))
  set lam := r / (√(d : ℝ) * L) with hlam
  have hlam0 : 0 ≤ lam := by positivity
  have hlam1 : lam ≤ 1 := by
    rw [hlam, div_le_one (by positivity)]
    have : 1 ≤ √(d : ℝ) := by rw [Real.one_le_sqrt]; exact_mod_cast hd1
    nlinarith
  let z₀ : ℕ → Rd d := fun j =>
    if j = 0 then m - L • u else if j = n₀ then gridRound ν o (γ 0) else resHom m lam (q₀ j)
  let z₁ : ℕ → Rd d := fun j =>
    if j = 0 then m + L • u else if j = n₁ then gridRound ν o (γ 1) else resHom m lam (q₁ j)
  have hn₀0 : n₀ ≠ 0 := by omega
  have hn₁0 : n₁ ≠ 0 := by omega
  have hz₀0 : z₀ 0 = m - L • u := by simp only [z₀, ↓reduceIte]
  have hz₀n : z₀ n₀ = gridRound ν o (γ 0) := by simp only [z₀, hn₀0, ↓reduceIte]
  have hz₁0 : z₁ 0 = m + L • u := by simp only [z₁, ↓reduceIte]
  have hz₁n : z₁ n₁ = gridRound ν o (γ 1) := by simp only [z₁, hn₁0, ↓reduceIte]
  have hz₀m : ∀ j, 1 ≤ j → j < n₀ → z₀ j = resHom m lam (q₀ j) := fun j h1 h2 => by
    have h1' : j ≠ 0 := by omega
    have h2' : j ≠ n₀ := by omega
    simp only [z₀, h1', h2', ↓reduceIte]
  have hz₁m : ∀ j, 1 ≤ j → j < n₁ → z₁ j = resHom m lam (q₁ j) := fun j h1 h2 => by
    have h1' : j ≠ 0 := by omega
    have h2' : j ≠ n₁ := by omega
    simp only [z₁, h1', h2', ↓reduceIte]
  have hball : ∀ x, x ∈ resBox m L → ‖x‖ ≤ 4 := fun x hx => by
    have := hbox hx
    rwa [mem_closedBall, dist_zero_right] at this
  have hz₀b : ∀ j ≤ n₀, ‖z₀ j‖ ≤ 4 := by
    intro j hj
    apply hball
    rcases Nat.eq_zero_or_pos j with h0 | h0
    · rw [h0, hz₀0]; exact hp₀box
    rcases Nat.lt_or_ge j n₀ with h | h
    · rw [hz₀m j h0 h]; exact resHom_mem_resBox hlam0 hlam1 (hq₀box j hj)
    · rw [le_antisymm hj h, hz₀n]; exact ha₀box
  have hz₁b : ∀ j ≤ n₁, ‖z₁ j‖ ≤ 4 := by
    intro j hj
    apply hball
    rcases Nat.eq_zero_or_pos j with h0 | h0
    · rw [h0, hz₁0]; exact hp₁box
    rcases Nat.lt_or_ge j n₁ with h | h
    · rw [hz₁m j h0 h]; exact resHom_mem_resBox hlam0 hlam1 (hq₁box j hj)
    · rw [le_antisymm hj h, hz₁n]; exact ha₁box
  -- the general-position hypothesis
  set δ := r / (4 * √(d : ℝ)) with hδdef
  have hδ0 : 0 ≤ δ := by positivity
  have hδ1 : δ ≤ 1 := by
    rw [hδdef, div_le_one (by positivity)]
    have : 1 ≤ √(d : ℝ) := by rw [Real.one_le_sqrt]; exact_mod_cast hd1
    linarith
  have hcore : √(d : ℝ) * ν * ((((n₀ + 1 + (n₁ + 1) : ℕ) : ℝ)) ^ 3 + 1) ≤ δ := by
    have hν' : ν ≤ gpC0 d * δ / (((2 * N + 4 : ℕ) : ℝ) + 1) ^ 3 := by
      have : (((2 * N + 4 : ℕ) : ℝ) + 1) = 2 * (N : ℝ) + 5 := by push_cast; ring
      rw [this]; exact hνN
    have h1 := gp_hyp_of_le hd1 hν hδ0 hν'
    have hcard : (((n₀ + 1 + (n₁ + 1) : ℕ) : ℝ)) ≤ ((2 * N + 4 : ℕ) : ℝ) := by
      exact_mod_cast (by omega : n₀ + 1 + (n₁ + 1) ≤ 2 * N + 4)
    have h3 : (((n₀ + 1 + (n₁ + 1) : ℕ) : ℝ)) ^ 3 ≤ ((2 * N + 4 : ℕ) : ℝ) ^ 3 :=
      pow_le_pow_left₀ (Nat.cast_nonneg _) hcard 3
    calc √(d : ℝ) * ν * ((((n₀ + 1 + (n₁ + 1) : ℕ) : ℝ)) ^ 3 + 1)
        ≤ √(d : ℝ) * ν * (((2 * N + 4 : ℕ) : ℝ) ^ 3 + 1) :=
          mul_le_mul_of_nonneg_left (by linarith) (by positivity)
      _ ≤ δ := h1
  obtain ⟨y₀, y₁, hy₀0, hy₀n, hy₁0, hy₁n, hd₀, hd₁, hg₀, hg₁, hi₀, hi₁, hi₀₁, hs₀, hs₁, hc₀,
      hc₁, hs₀₁⟩ :=
    exists_gp_two_chains hd hn₀2 hn₁2 o hν hδ1 hcore z₀ z₁ hz₀b hz₁b
      (by rw [hz₀0]; exact hp₀) (by rw [hz₀n]; exact onGrid_gridRound ν o _)
      (by rw [hz₁0]; exact hp₁) (by rw [hz₁n]; exact onGrid_gridRound ν o _)
      (by rw [hz₀0, hz₀n]; exact h01) (by rw [hz₀0, hz₁0]; exact h02)
      (by rw [hz₀0, hz₁n]; exact h03) (by rw [hz₀n, hz₁0]; exact h12)
      (by rw [hz₀n, hz₁n]; exact h13) (by rw [hz₁0, hz₁n]; exact h23)
  have hγ0 : ‖γ 0 - m‖ ≤ L / 32 := by rw [← dist_eq_norm]; exact hγm 0 ⟨le_rfl, zero_le_one⟩
  have hγ1 : ‖γ 1 - m‖ ≤ L / 32 := by rw [← dist_eq_norm]; exact hγm 1 ⟨zero_le_one, le_rfl⟩
  refine ⟨n₀, n₁, y₀, y₁, ?_, ?_, hi₀₁, hs₀₁⟩
  · refine isLead_of_moves hd1 hL hr0 hrL hr1 hν hνr hn₀2 hn₀N hp₀box hγ0 hq₀0 hq₀n hq₀box
      hq₀clear (hy₀0.trans hz₀0) (hy₀n.trans hz₀n) (fun j h1 h2 => ?_) hg₀ hi₀ hs₀ hc₀
    rw [← hz₀m j h1 h2]; exact hd₀ j h2.le
  · refine isLead_of_moves hd1 hL hr0 hrL hr1 hν hνr hn₁2 hn₁N hp₁box hγ1 hq₁0 hq₁n hq₁box
      hq₁clear (hy₁0.trans hz₁0) (hy₁n.trans hz₁n) (fun j h1 h2 => ?_) hg₁ hi₁ hs₁ hc₁
    rw [← hz₁m j h1 h2]; exact hd₁ j h2.le

/-- The packet name of `exists_leads` (packet Q2, target 3). -/
alias two_leads := exists_leads

end HigherDimLQGContinuity.Routing

end
