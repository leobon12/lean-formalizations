import SupercriticalLFPPAS.Main.Event

/-!
# §7: the lower-limit condition (1.2) (packet T7)

Paper §7, l. 633–646; SB2 §2.8 "(1.2)" steps 1–5. On the event `MainGood`, for every sequence of cutoffs `ε_n → 0` and
every `(z_n, w_n) → (z, w)`, `D(z, w) ≤ liminf X_{ε_n}(z_n, w_n)`:

1. if `X_{ε_n}(z_n, w_n) ≤ L` frequently, an ordinary near-minimizer of length `< L + θ` from `z_n` to `w_n` stays in
   `B_{R₁}(0)` (Lemma 6.2, `mem_ball_of_len_lt_setDist`);
2. at the mesh point `δ = k(ε_n)^{-a}` of the window containing `ε_n`, (2.1), (2.2) and the corrected (6.1) give
   `X̂_δ(z_n, w_n) ≤ e^θ (L + θ)` (`lfppMetric_le_of_confined`);
3. an `X̂_δ`-geodesic from `z_n` to `w_n` exists inside `B_{R₁}(0)` (`LFPPGeodesicStmt` with the escape bound);
4. (5.2) on the mesh gives `D(B_ρ(z_n), B_ρ(w_n)) ≤ (1 + 1/j) e^θ (L + θ)` with `ρ = 513 δ^s → 0` (internal ≥ whole
   plane);
5. lower semicontinuity of `D` gives `D(z, w) ≤ (1 + 1/j) e^θ (L + θ) + θ`; then `j → ∞`, `θ → 0`.
-/

set_option autoImplicit false

noncomputable section

open Set Filter Topology Metric
open scoped ENNReal

namespace SupercriticalLFPPAS.Main

open LQGMetric (DistC)
open SupercriticalLQGUniqueness (LSCMetric rescaledLFPP)
open SupercriticalLQGUniqueness.B2.Median (lfppMetric)
open SupercriticalLQGUniqueness.Uniqueness.OptimalConstants.Ratios (setDist)

/-- A liminf lower bound in `[-∞, ∞]` for `[0, ∞]`-valued sequences from frequent real upper bounds. -/
theorem coe_le_liminf_of_frequently {u : ℕ → ℝ≥0∞} {v : ℝ≥0∞}
    (h : ∀ L : ℝ, 0 ≤ L → (∃ᶠ n in atTop, u n ≤ ENNReal.ofReal L) → v ≤ ENNReal.ofReal L) :
    (v : EReal) ≤ liminf (fun n => (u n : EReal)) atTop := by
  by_contra hlt
  rw [not_le] at hlt
  obtain ⟨b, hb1, hb2⟩ := exists_between hlt
  have hfr : ∃ᶠ n in atTop, (u n : EReal) < b := frequently_lt_of_liminf_lt (by isBoundedDefault) hb1
  rcases le_or_gt b 0 with hb0 | hb0
  · obtain ⟨n, hn⟩ := hfr.exists
    exact absurd (hn.trans_le hb0) (not_lt.2 (EReal.coe_ennreal_nonneg _))
  · have hbtop : b ≠ ⊤ := ne_top_of_lt hb2
    have hbbot : b ≠ ⊥ := ne_bot_of_gt hb0
    have hL : 0 ≤ b.toReal := EReal.toReal_nonneg hb0.le
    have hbL : ((ENNReal.ofReal b.toReal : ℝ≥0∞) : EReal) = b := by
      rw [EReal.coe_ennreal_ofReal, max_eq_left hL, EReal.coe_toReal hbtop hbbot]
    have hfr' : ∃ᶠ n in atTop, u n ≤ ENNReal.ofReal b.toReal := hfr.mono fun n hn => by
      rw [← hbL, EReal.coe_ennreal_lt_coe_ennreal_iff] at hn
      exact hn.le
    have h2 : (v : EReal) ≤ b := by
      rw [← hbL]
      exact EReal.coe_ennreal_le_coe_ennreal_iff.2 (h _ hL hfr')
    exact absurd hb2 (not_lt.2 h2)

/-- `d(K, B) ≤ d({x}, B)` for `x ∈ K`. -/
theorem setDist_le_setDist_singleton (d : LSCMetric) {K B : Set ℂ} {x : ℂ} (hx : x ∈ K) :
    setDist d K B ≤ setDist d {x} B :=
  le_iInf₂ fun z hz => by
    rw [mem_singleton_iff.1 hz]
    exact iInf₂_le x hx

/-- **The core of (1.2)** for one `j ≥ 1` and one slack `θ ∈ (0, 1]` (SB2 §2.8 steps 1–5). -/
theorem lower_core (S : Core.Setup) {a s : ℕ → ℕ → ℝ} {g : DistC} {Y : Set.Ioi (0 : ℝ) → C(ℂ, ℝ)}
    (hG : Core.LFPPGeodesicStmt) (hW : Core.NormalizerWindowStmt S) (hg : MainGood S a s g Y)
    {ε : ℕ → Set.Ioi (0 : ℝ)} (hε : Tendsto (fun n => (ε n : ℝ)) atTop (𝓝 0))
    {p : ℕ → ℂ × ℂ} {q : ℂ × ℂ} (hp : Tendsto p atTop (𝓝 q)) {L : ℝ} (hL : 0 ≤ L)
    (hfreq : ∃ᶠ n in atTop, Core.lfppM S (ε n) (Y (ε n)) (p n) ≤ ENNReal.ofReal L)
    {j : ℕ} (hj : 1 ≤ j) {θ : ℝ} (hθ : 0 < θ) (hθ1 : θ ≤ 1) :
    S.D g q ≤ ENNReal.ofReal ((1 + 1 / (j : ℝ)) * (Real.exp θ * (L + θ)) + θ) := by
  set c : ℝ := (1 + 1 / (j : ℝ)) * (Real.exp θ * (L + θ)) + θ with hc
  by_contra hcon
  rw [not_le] at hcon
  -- step 5 prepared: lower semicontinuity of `D` at `q`
  obtain ⟨r, hr, hball⟩ := Metric.eventually_nhds_iff.1 ((S.D g).lowerSemicontinuous q _ hcon)
  set ξ : ℝ := (S.ξ : ℝ) with hξdef
  have hξ : 0 < ξ := S.ξ.2
  -- step 1: confinement data (Lemma 6.2) for the compact `K` containing the endpoints
  set K : Set ℂ := closedBall 0 (‖q.1‖ + ‖q.2‖ + 1) with hKdef
  set M : ℝ := 3 * (L + 1) + 1 with hMdef
  obtain ⟨R₁, hKR₁, ε₀, hε₀, hconf⟩ := hg.confine K (isCompact_closedBall _ _) M
  set R : ℕ := ⌈R₁⌉₊ + 1 with hRdef
  have hR1 : 1 ≤ R := Nat.le_add_left 1 _
  have hR₁R : R₁ ≤ (R : ℝ) := by
    rw [hRdef]
    push_cast
    linarith [Nat.le_ceil R₁]
  set A := a j R with hAdef
  set σ := s j R with hσdef
  have hA : 0 < A := hg.a_pos j R
  have hσ : 0 < σ := hg.s_pos j R
  set η : ℝ := θ / (1 + 2 * ξ) with hηdef
  have hη : 0 < η := by positivity
  have hηθ : η + |ξ| * (2 * η) = θ := by
    rw [abs_of_pos hξ, hηdef]
    field_simp
  set Kf : Set ℂ := closedBall 0 R₁ with hKfdef
  have hKf : IsCompact Kf := isCompact_closedBall _ _
  -- conditions along the mesh, transported to the sequence through the mesh index
  have hεw : Tendsto (fun n => (ε n : ℝ)) atTop (𝓝[>] 0) :=
    tendsto_nhdsWithin_iff.2 ⟨hε, Eventually.of_forall fun n => (ε n).2⟩
  have hkn : Tendsto (fun n => meshIdx A (ε n : ℝ)) atTop atTop := (tendsto_meshIdx hA).comp hεw
  have h1 := hkn.eventually (eventually_ge_atTop 2)
  have h2 := hkn.eventually
    (((tendsto_mesh_pow hA).mono_right nhdsWithin_le_nhds).eventually (gt_mem_nhds hε₀))
  have h3 := hkn.eventually (hg.mesh j R hj hR1)
  have h4 := hkn.eventually (hg.meshOsc j R Kf hKf η hη)
  have h5 := hkn.eventually (hW A hA η hη)
  have h6 := hkn.eventually ((tendsto_mesh_pow hA).eventually (hg.locApprox Kf hKf η hη))
  have h7 := hkn.eventually ((tendsto_mesh_rad hA hσ).eventually (gt_mem_nhds (half_pos hr)))
  have h8 := hε.eventually (gt_mem_nhds hε₀)
  have h9 := hε.eventually (gt_mem_nhds one_pos)
  have h10 := hp.eventually (ball_mem_nhds q (half_pos hr))
  have h11 := hp.eventually (ball_mem_nhds q one_pos)
  obtain ⟨n, hnL, hn1, hn2, hn3, hn4, hn5, hn6, hn7, hn8, hn9, hn10, hn11⟩ :=
    (hfreq.and_eventually (h1.and (h2.and (h3.and (h4.and (h5.and (h6.and (h7.and (h8.and (h9.and
      (h10.and h11))))))))))).exists
  -- the mesh point of the window containing `ε_n`
  set k := meshIdx A (ε n : ℝ) with hkdef
  set δ : ℝ := (k : ℝ) ^ (-A) with hδdef
  have hδ : δ ∈ Ioo (0 : ℝ) 1 := mesh_pow_mem_Ioo hA hn1
  set δ' : Set.Ioi (0 : ℝ) := ⟨δ, hδ.1⟩ with hδ'def
  obtain ⟨-, hw1, hw2⟩ := meshIdx_window hA (ε n).2 hn9.le
  have hkpos : (0 : ℝ) < k := by
    have : (2 : ℝ) ≤ k := by exact_mod_cast hn1
    linarith
  have hδw : ((k : ℝ) + 1) ^ (-A) ≤ δ :=
    Real.rpow_le_rpow_of_nonpos hkpos (by linarith) (by linarith)
  -- step 2: the field and normalizer comparisons on `B_{R₁}(0)`
  set φ' : C(ℂ, ℝ) := SupercriticalLQGUniqueness.B2.Polylog.plMollifyC 1 δ hδ g with hφ'def
  have hfield : ∀ x ∈ ball (0 : ℂ) R₁, |φ' x - Y (ε n) x| ≤ 2 * η := by
    intro x hx
    have hxK : x ∈ Kf := ball_subset_closedBall hx
    have hosc : |Y (ε n) x - Y δ' x| ≤ η := hn4 (ε n) δ' hw1 hw2 hδw le_rfl x hxK
    have hloc : |Y δ' x - SupercriticalLQGUniqueness.B2.Polylog.plMollify 1 δ hδ g x| ≤ η := hn6 hδ x hxK
    have hφ' : φ' x = SupercriticalLQGUniqueness.B2.Polylog.plMollify 1 δ hδ g x := rfl
    rw [hφ']
    have e1 := abs_sub_le (SupercriticalLQGUniqueness.B2.Polylog.plMollify 1 δ hδ g x) (Y δ' x) (Y (ε n) x)
    rw [abs_sub_comm (SupercriticalLQGUniqueness.B2.Polylog.plMollify 1 δ hδ g x) (Y δ' x),
      abs_sub_comm (Y δ' x) (Y (ε n) x)] at e1
    linarith
  have hratio : (S.m (ε n) : ℝ) / (S.m δ' : ℝ) ≤ Real.exp η := by
    have hpos : 0 < (S.m (ε n) : ℝ) / (S.m δ' : ℝ) := div_pos (S.m (ε n)).2 (S.m δ').2
    exact (Real.log_le_iff_le_exp hpos).1 ((le_abs_self _).trans (hn5 (ε n) δ' hw1 hw2 hδw le_rfl))
  have hfactor : (S.m (ε n) : ℝ) / (S.m δ' : ℝ) * Real.exp (|ξ| * (2 * η)) ≤ Real.exp θ := by
    rw [← hηθ, Real.exp_add]
    exact mul_le_mul_of_nonneg_right hratio (Real.exp_pos _).le
  -- the ordinary near-minimizer, transferred to the localized mesh metric
  have hxK : (p n).1 ∈ K := by
    have hd : dist (p n).1 q.1 < 1 := lt_of_le_of_lt (le_max_left _ _) (mem_ball.1 hn11)
    rw [hKdef, mem_closedBall_zero_iff]
    have := norm_le_norm_add_norm_sub' (p n).1 q.1
    rw [← dist_eq_norm] at this
    linarith [norm_nonneg q.2]
  have hεn : (ε n : ℝ) ∈ Ioo (0 : ℝ) 1 := ⟨(ε n).2, hn9⟩
  have hcf := hconf (ε n) hεn hn8
  have hLM : L + θ ≤ M := by rw [hMdef]; linarith
  have hloc_bd : lfppMetric ξ (S.m δ') φ' ((p n).1, (p n).2) ≤ ENNReal.ofReal (Real.exp θ * (L + θ)) := by
    have hxy : lfppMetric ξ (S.m (ε n)) (Y (ε n)) ((p n).1, (p n).2) < ENNReal.ofReal (L + θ) :=
      hnL.trans_lt ((ENNReal.ofReal_lt_ofReal_iff (by linarith)).2 (by linarith))
    have hLe : ENNReal.ofReal (L + θ) ≤ setDist (lfppMetric ξ (S.m (ε n)) (Y (ε n))) K (sphere 0 R₁) :=
      (ENNReal.ofReal_le_ofReal hLM).trans hcf.2.le
    calc lfppMetric ξ (S.m δ') φ' ((p n).1, (p n).2)
        ≤ ENNReal.ofReal ((S.m (ε n) : ℝ) / (S.m δ' : ℝ) * Real.exp (|ξ| * (2 * η))) * ENNReal.ofReal (L + θ) :=
          lfppMetric_le_of_confined ξ (S.m (ε n)) (S.m δ') hKR₁ hfield hxK hxy hLe
      _ ≤ ENNReal.ofReal (Real.exp θ) * ENNReal.ofReal (L + θ) :=
          mul_le_mul_left (ENNReal.ofReal_le_ofReal hfactor) _
      _ = ENNReal.ofReal (Real.exp θ * (L + θ)) := (ENNReal.ofReal_mul (Real.exp_pos _).le).symm
  -- step 3: a localized geodesic inside `B_{R₁}(0)`
  have hexpθ : Real.exp θ * (L + θ) < M := by
    have he : Real.exp θ ≤ 3 :=
      (Real.exp_le_exp.2 hθ1).trans (by have := Real.exp_one_lt_d9; norm_num at this ⊢; linarith)
    calc Real.exp θ * (L + θ) ≤ 3 * (L + θ) := mul_le_mul_of_nonneg_right he (by linarith)
      _ < M := by rw [hMdef]; linarith
  have hnorm : ‖(p n).1‖ < R₁ := mem_ball_zero_iff.1 (hKR₁ hxK)
  have hlt : lfppMetric ξ (S.m δ') φ' ((p n).1, (p n).2) <
      setDist (lfppMetric ξ (S.m δ') φ') {(p n).1} (sphere 0 R₁) :=
    calc lfppMetric ξ (S.m δ') φ' ((p n).1, (p n).2) ≤ ENNReal.ofReal (Real.exp θ * (L + θ)) := hloc_bd
      _ < ENNReal.ofReal M := (ENNReal.ofReal_lt_ofReal_iff (by linarith)).2 hexpθ
      _ < setDist (Core.locMetric S δ hδ g) K (sphere 0 R₁) := (hconf δ hδ hn2).1
      _ ≤ setDist (lfppMetric ξ (S.m δ') φ') {(p n).1} (sphere 0 R₁) :=
          setDist_le_setDist_singleton _ hxK
  obtain ⟨Pg, T, hP0, hPT, hgeo⟩ := hG ξ (S.m δ') φ' (p n).1 (p n).2 R₁ hnorm hlt
  have hgeoR : Core.IsGeodIn (Core.locMetric S δ hδ g) Pg T R := isGeodIn_mono hgeo hR₁R
  have hT0 : 0 ≤ T := hgeo.1.1
  have hTval : ENNReal.ofReal T = lfppMetric ξ (S.m δ') φ' ((p n).1, (p n).2) := by
    rw [← hP0, ← hPT]
    exact ofReal_eq_of_unitSpeed_geodesic _ hgeo.1 hgeo.2.1
  have hTle : T ≤ Real.exp θ * (L + θ) :=
    (ENNReal.ofReal_le_ofReal_iff (by positivity)).1 (hTval ▸ hloc_bd)
  -- step 4: the reverse comparison (5.2) on the mesh
  have hcomp := (hn3 hδ).2 Pg T hgeoR 0 T le_rfl hT0 le_rfl
  have hj0 : (0 : ℝ) ≤ 1 / (j : ℝ) := by positivity
  have hlt2 : (S.D g).internalSetDist (ball 0 ((R : ℝ) + 2))
      {y | (y : ℂ) ∈ ball (Pg 0) (513 * δ ^ σ)} {y | (y : ℂ) ∈ ball (Pg T) (513 * δ ^ σ)} <
      ENNReal.ofReal c := by
    refine hcomp.trans_lt ((ENNReal.ofReal_lt_ofReal_iff (by positivity)).2 ?_)
    rw [hc, sub_zero]
    have := mul_le_mul_of_nonneg_left hTle (by linarith : (0 : ℝ) ≤ 1 + 1 / (j : ℝ))
    linarith
  unfold SupercriticalLQGUniqueness.LSCMetric.internalSetDist at hlt2
  simp only [iInf_lt_iff] at hlt2
  obtain ⟨x, hx, y, hy, hxy⟩ := hlt2
  have hDxy : S.D g ((x : ℂ), (y : ℂ)) < ENNReal.ofReal c :=
    (LSCMetric.edist_le_internal _ _ (x, y)).trans_lt hxy
  -- step 5: lower semicontinuity
  have hx' : dist (x : ℂ) (p n).1 < r / 2 := by
    have := mem_ball.1 (show (x : ℂ) ∈ ball (Pg 0) (513 * δ ^ σ) from hx)
    rw [hP0] at this
    linarith
  have hy' : dist (y : ℂ) (p n).2 < r / 2 := by
    have := mem_ball.1 (show (y : ℂ) ∈ ball (Pg T) (513 * δ ^ σ) from hy)
    rw [hPT] at this
    linarith
  have hpq : dist (p n) q < r / 2 := mem_ball.1 hn10
  rw [Prod.dist_eq] at hpq
  have hdist : dist ((x : ℂ), (y : ℂ)) q < r := by
    rw [Prod.dist_eq]
    refine max_lt ?_ ?_
    · linarith [dist_triangle (x : ℂ) (p n).1 q.1, le_max_left (dist (p n).1 q.1) (dist (p n).2 q.2)]
    · linarith [dist_triangle (y : ℂ) (p n).2 q.2, le_max_right (dist (p n).1 q.1) (dist (p n).2 q.2)]
  exact lt_asymm hDxy (hball hdist)

/-- (1.2) at one frequent bound: if `X_{ε_n}(p_n) ≤ L` frequently, then `D(q) ≤ L` (`lower_core` with `j → ∞`,
`θ = 1/(j+1) → 0`). -/
theorem le_of_frequently (S : Core.Setup) {a s : ℕ → ℕ → ℝ} {g : DistC} {Y : Set.Ioi (0 : ℝ) → C(ℂ, ℝ)}
    (hG : Core.LFPPGeodesicStmt) (hW : Core.NormalizerWindowStmt S) (hg : MainGood S a s g Y)
    {ε : ℕ → Set.Ioi (0 : ℝ)} (hε : Tendsto (fun n => (ε n : ℝ)) atTop (𝓝 0))
    {p : ℕ → ℂ × ℂ} {q : ℂ × ℂ} (hp : Tendsto p atTop (𝓝 q)) {L : ℝ} (hL : 0 ≤ L)
    (hfreq : ∃ᶠ n in atTop, Core.lfppM S (ε n) (Y (ε n)) (p n) ≤ ENNReal.ofReal L) :
    S.D g q ≤ ENNReal.ofReal L := by
  set t : ℕ → ℝ := fun j => (1 + 1 / ((j : ℝ) + 1)) * (Real.exp (1 / ((j : ℝ) + 1)) * (L + 1 / ((j : ℝ) + 1))) +
    1 / ((j : ℝ) + 1) with htdef
  have hbound : ∀ j : ℕ, S.D g q ≤ ENNReal.ofReal (t j) := by
    intro j
    have hθ : (0 : ℝ) < 1 / ((j : ℝ) + 1) := by positivity
    have hθ1 : 1 / ((j : ℝ) + 1) ≤ 1 := by
      rw [div_le_one (by positivity)]
      linarith [(Nat.cast_nonneg j : (0 : ℝ) ≤ j)]
    have := lower_core S hG hW hg hε hp hL hfreq (j := j + 1) (Nat.le_add_left 1 j) hθ hθ1
    simpa only [htdef, Nat.cast_add, Nat.cast_one] using this
  have hu : Tendsto (fun j : ℕ => 1 / ((j : ℝ) + 1)) atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  have ht : Tendsto t atTop (𝓝 L) := by
    have := ((tendsto_const_nhds (x := (1 : ℝ))).add hu).mul
      (((Real.continuous_exp.tendsto 0).comp hu).mul ((tendsto_const_nhds (x := L)).add hu)) |>.add hu
    simpa only [htdef, add_zero, Real.exp_zero, one_mul, Function.comp_def] using this
  exact ge_of_tendsto' (ENNReal.tendsto_ofReal ht) hbound

/-- **(1.2)**, the lower-limit condition of `LSCTendsto`, on the event `MainGood`, for every sequence of cutoffs
`ε_n → 0` (paper §7, l. 633–646). -/
theorem lowerLimit (S : Core.Setup) {a s : ℕ → ℕ → ℝ} {g : DistC} {Y : Set.Ioi (0 : ℝ) → C(ℂ, ℝ)}
    (hG : Core.LFPPGeodesicStmt) (hW : Core.NormalizerWindowStmt S) (hg : MainGood S a s g Y)
    {ε : ℕ → Set.Ioi (0 : ℝ)} (hε : Tendsto (fun n => (ε n : ℝ)) atTop (𝓝 0))
    (p : ℕ → ℂ × ℂ) (q : ℂ × ℂ) (hp : Tendsto p atTop (𝓝 q)) :
    (S.D g).toLSCFun.1 q ≤ liminf (fun n => rescaledLFPP (S.ξ : ℝ) (S.m (ε n)) (Y (ε n)) (p n)) atTop :=
  coe_le_liminf_of_frequently (u := fun n => Core.lfppM S (ε n) (Y (ε n)) (p n))
    fun _ hL hfreq => le_of_frequently S hG hW hg hε hp hL hfreq

end SupercriticalLFPPAS.Main
