import SupercriticalLFPPAS.Main.LowerLimit

/-!
# §7: recovery sequences (packet T7)

Paper §7, l. 647–661; SB2 §2.8 "Recovery". On the event `MainGood`, for every sequence of cutoffs `ε_n → 0` and every
`q = (z, w)` there are `p_n → q` with `X_{ε_n}(p_n) → D(q)`:

* `D(q) = ∞`: the constant pair, by (1.2) (`lowerLimit`);
* `D(q) < ∞`: a unit-speed `D`-geodesic from `z` to `w` (Pfeffer, `MainGood.geod`), Euclidean continuous
  (`MainGood.eucl`), inside some `B_R(0)`. For each `j`, (5.1) on the mesh `(j, R)` gives endpoints within
  `513 δ^s` of `z, w` whose localized distance *internal to `B_{R+2}(0)`* is at most `(1 + 1/j) D(q)`; the internal
  metric confines the near-minimizers, so (2.1), (2.2) and the corrected (6.1) transfer the bound to every real cutoff
  of the window of `δ` (`recovery_core`). A diagonal choice `j(n) → ∞` (`exists_diag`) and (1.2) finish.

The diagonal case `z = w` is covered by the finite case (the geodesic is constant).
-/

set_option autoImplicit false

noncomputable section

open Set Filter Topology Metric
open scoped ENNReal

namespace SupercriticalLFPPAS.Main

open LQGMetric (DistC)
open SupercriticalLQGUniqueness (LSCMetric rescaledLFPP)
open SupercriticalLQGUniqueness.B2.Median (lfppMetric)

/-- **Diagonal selection.** If each `Q j` holds eventually, some `J n → ∞` has `Q (J n) n` eventually. -/
theorem exists_diag {Q : ℕ → ℕ → Prop} (h : ∀ j, ∀ᶠ n in atTop, Q j n) :
    ∃ J : ℕ → ℕ, Tendsto J atTop atTop ∧ ∀ᶠ n in atTop, Q (J n) n := by
  classical
  choose N hN using fun j => eventually_atTop.1 (h j)
  refine ⟨fun n => Nat.findGreatest (fun j => ∀ i ≤ j, N i ≤ n) n, ?_, ?_⟩
  · refine tendsto_atTop_atTop.2 fun j₀ => ⟨j₀ + ∑ i ∈ Finset.range (j₀ + 1), N i, fun n hn => ?_⟩
    refine Nat.le_findGreatest (by omega) fun i hi => ?_
    have : N i ≤ ∑ i ∈ Finset.range (j₀ + 1), N i :=
      Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_range.2 (by omega))
    omega
  · filter_upwards [eventually_ge_atTop (N 0)] with n hn
    have hP := Nat.findGreatest_spec (P := fun j => ∀ i ≤ j, N i ≤ n) (m := 0) (Nat.zero_le n)
      (fun i hi => by rw [Nat.le_zero.1 hi]; exact hn)
    exact hN _ n (hP _ le_rfl)

/-- **Recovery at one `j ≥ 1` and one slack `θ > 0`** (SB2 §2.8 "Recovery"): for a unit-speed `D`-geodesic `γ` on
`[0, T]` inside `B_R(0)`, every small real cutoff `ε` has endpoints within `θ` of `γ 0`, `γ T` whose normalized LFPP
distance is at most `e^θ ((1 + 1/j) T + θ)`. -/
theorem recovery_core (S : Core.Setup) {a s : ℕ → ℕ → ℝ} {g : DistC} {Y : Set.Ioi (0 : ℝ) → C(ℂ, ℝ)}
    (hW : Core.NormalizerWindowStmt S) (hg : MainGood S a s g Y)
    {γ : ℝ → ℂ} {T : ℝ} {R : ℕ} (hR : 1 ≤ R) (hγ : Core.IsGeodIn (S.D g) γ T R)
    {j : ℕ} (hj : 1 ≤ j) {θ : ℝ} (hθ : 0 < θ) :
    ∀ᶠ ε in 𝓝[>] (0 : ℝ), ∀ hε : 0 < ε, ∃ x y : ℂ, dist x (γ 0) < θ ∧ dist y (γ T) < θ ∧
      Core.lfppM S ⟨ε, hε⟩ (Y ⟨ε, hε⟩) (x, y) ≤
        ENNReal.ofReal (Real.exp θ * ((1 + 1 / (j : ℝ)) * T + θ)) := by
  set ξ : ℝ := (S.ξ : ℝ) with hξdef
  have hξ : 0 < ξ := S.ξ.2
  set A := a j R with hAdef
  set σ := s j R with hσdef
  have hA : 0 < A := hg.a_pos j R
  have hσ : 0 < σ := hg.s_pos j R
  set η : ℝ := θ / (1 + 2 * ξ) with hηdef
  have hη : 0 < η := by positivity
  have hηθ : η + |ξ| * (2 * η) = θ := by
    rw [abs_of_pos hξ, hηdef]
    field_simp
  set W : Set ℂ := ball 0 ((R : ℝ) + 2) with hWdef
  set Kf : Set ℂ := closedBall 0 ((R : ℝ) + 2) with hKfdef
  have hKf : IsCompact Kf := isCompact_closedBall _ _
  have hT0 : 0 ≤ T := hγ.1.1
  have hk := tendsto_meshIdx hA
  have h1 := hk.eventually (eventually_ge_atTop 2)
  have h3 := hk.eventually (hg.mesh j R hj hR)
  have h4 := hk.eventually (hg.meshOsc j R Kf hKf η hη)
  have h5 := hk.eventually (hW A hA η hη)
  have h6 := hk.eventually ((tendsto_mesh_pow hA).eventually (hg.locApprox Kf hKf η hη))
  have h7 := hk.eventually ((tendsto_mesh_rad hA hσ).eventually (gt_mem_nhds hθ))
  have h9 : ∀ᶠ ε in 𝓝[>] (0 : ℝ), ε ∈ Ioo (0 : ℝ) 1 := Ioo_mem_nhdsGT one_pos
  filter_upwards [h1, h3, h4, h5, h6, h7, h9] with ε hn1 hn3 hn4 hn5 hn6 hn7 hn9 hε
  -- the mesh point of the window containing `ε`
  set k := meshIdx A ε with hkdef
  set δ : ℝ := (k : ℝ) ^ (-A) with hδdef
  have hδ : δ ∈ Ioo (0 : ℝ) 1 := mesh_pow_mem_Ioo hA hn1
  set δ' : Set.Ioi (0 : ℝ) := ⟨δ, hδ.1⟩ with hδ'def
  set εs : Set.Ioi (0 : ℝ) := ⟨ε, hε⟩ with hεsdef
  obtain ⟨-, hw1, hw2⟩ := meshIdx_window hA hε hn9.2.le
  have hkpos : (0 : ℝ) < k := by
    have : (2 : ℝ) ≤ k := by exact_mod_cast hn1
    linarith
  have hδw : ((k : ℝ) + 1) ^ (-A) ≤ δ :=
    Real.rpow_le_rpow_of_nonpos hkpos (by linarith) (by linarith)
  -- field and normalizer comparisons on `B_{R+2}(0)`
  set φ : C(ℂ, ℝ) := SupercriticalLQGUniqueness.B2.Polylog.plMollifyC 1 δ hδ g with hφdef
  have hfield : ∀ x ∈ W, |Y εs x - φ x| ≤ 2 * η := by
    intro x hx
    have hxK : x ∈ Kf := ball_subset_closedBall hx
    have hosc : |Y εs x - Y δ' x| ≤ η := hn4 εs δ' hw1 hw2 hδw le_rfl x hxK
    have hloc : |Y δ' x - SupercriticalLQGUniqueness.B2.Polylog.plMollify 1 δ hδ g x| ≤ η := hn6 hδ x hxK
    have hφx : φ x = SupercriticalLQGUniqueness.B2.Polylog.plMollify 1 δ hδ g x := rfl
    rw [hφx]
    have e1 := abs_sub_le (Y εs x) (Y δ' x) (SupercriticalLQGUniqueness.B2.Polylog.plMollify 1 δ hδ g x)
    linarith
  have hratio : (S.m δ' : ℝ) / (S.m εs : ℝ) ≤ Real.exp η := by
    have hpos : 0 < (S.m δ' : ℝ) / (S.m εs : ℝ) := div_pos (S.m δ').2 (S.m εs).2
    exact (Real.log_le_iff_le_exp hpos).1 ((le_abs_self _).trans (hn5 δ' εs hδw le_rfl hw1 hw2))
  have hfactor : (S.m δ' : ℝ) / (S.m εs : ℝ) * Real.exp (|ξ| * (2 * η)) ≤ Real.exp θ := by
    rw [← hηθ, Real.exp_add]
    exact mul_le_mul_of_nonneg_right hratio (Real.exp_pos _).le
  -- the forward comparison (5.1) on the mesh
  have hcomp := (hn3 hδ).1 γ T hγ 0 T le_rfl hT0 le_rfl
  have hj0 : (0 : ℝ) ≤ 1 / (j : ℝ) := by positivity
  have hlt : (Core.locMetric S δ hδ g).internalSetDist W
      {y | (y : ℂ) ∈ ball (γ 0) (513 * δ ^ σ)} {y | (y : ℂ) ∈ ball (γ T) (513 * δ ^ σ)} <
      ENNReal.ofReal ((1 + 1 / (j : ℝ)) * T + θ) := by
    refine hcomp.trans_lt ((ENNReal.ofReal_lt_ofReal_iff (by positivity)).2 ?_)
    rw [sub_zero]
    linarith
  unfold SupercriticalLQGUniqueness.LSCMetric.internalSetDist at hlt
  simp only [iInf_lt_iff] at hlt
  obtain ⟨x, hx, y, hy, hxy⟩ := hlt
  refine ⟨x, y, ?_, ?_, ?_⟩
  · exact (mem_ball.1 (show (x : ℂ) ∈ ball (γ 0) (513 * δ ^ σ) from hx)).trans hn7
  · exact (mem_ball.1 (show (y : ℂ) ∈ ball (γ T) (513 * δ ^ σ) from hy)).trans hn7
  · calc Core.lfppM S εs (Y εs) ((x : ℂ), (y : ℂ))
        ≤ ENNReal.ofReal ((S.m δ' : ℝ) / (S.m εs : ℝ) * Real.exp (|ξ| * (2 * η))) *
            (lfppMetric ξ (S.m δ') φ).internal W (x, y) :=
          lfppMetric_le_internal_mul ξ (S.m δ') (S.m εs) isOpen_ball hfield (x, y)
      _ ≤ ENNReal.ofReal (Real.exp θ) * ENNReal.ofReal ((1 + 1 / (j : ℝ)) * T + θ) :=
          mul_le_mul' (ENNReal.ofReal_le_ofReal hfactor) hxy.le
      _ = ENNReal.ofReal (Real.exp θ * ((1 + 1 / (j : ℝ)) * T + θ)) :=
          (ENNReal.ofReal_mul (Real.exp_pos _).le).symm

/-- **Recovery**, the second condition of `LSCTendsto`, on the event `MainGood`, for every sequence of cutoffs
`ε_n → 0` (paper §7, l. 647–661). -/
theorem recovery (S : Core.Setup) {a s : ℕ → ℕ → ℝ} {g : DistC} {Y : Set.Ioi (0 : ℝ) → C(ℂ, ℝ)}
    (hG : Core.LFPPGeodesicStmt) (hW : Core.NormalizerWindowStmt S) (hg : MainGood S a s g Y)
    {ε : ℕ → Set.Ioi (0 : ℝ)} (hε : Tendsto (fun n => (ε n : ℝ)) atTop (𝓝 0)) (q : ℂ × ℂ) :
    ∃ p : ℕ → ℂ × ℂ, Tendsto p atTop (𝓝 q) ∧
      Tendsto (fun n => rescaledLFPP (S.ξ : ℝ) (S.m (ε n)) (Y (ε n)) (p n)) atTop
        (𝓝 ((S.D g).toLSCFun.1 q)) := by
  by_cases htop : S.D g q = ⊤
  · -- infinite distance: the constant pair, by (1.2)
    refine ⟨fun _ => q, tendsto_const_nhds, ?_⟩
    have hlow := lowerLimit S hG hW hg hε (fun _ => q) q tendsto_const_nhds
    have h1 : (S.D g).toLSCFun.1 q = ⊤ := by
      change ((S.D g q : ℝ≥0∞) : EReal) = ⊤
      rw [htop, EReal.coe_ennreal_top]
    rw [h1] at hlow ⊢
    exact tendsto_order.2 ⟨fun b hb => eventually_lt_of_lt_liminf (hb.trans_le hlow),
      fun b hb => absurd hb (not_lt.2 le_top)⟩
  · -- finite distance: a `D`-geodesic and the diagonal over `j`
    have hfin : S.D g (q.1, q.2) < ⊤ := lt_top_iff_ne_top.2 htop
    obtain ⟨γ, T, hsg⟩ := hg.geod q.1 q.2 hfin
    have hgeod := SupercriticalLQGUniqueness.Uniqueness.EndSaving.FiniteEvents.SetGeodesic.isGeodesic _ _ _ _ _ hsg
    obtain ⟨⟨hcurve, hunit, hlen, hlt⟩, h0, hT, -⟩ := hsg
    have h0' : γ 0 = q.1 := h0
    have hT' : γ T = q.2 := hT
    have hcont : ContinuousOn γ (Icc 0 T) := hg.eucl γ 0 T hcurve (hlen ▸ hlt)
    obtain ⟨R₀, hR₀⟩ := (isCompact_Icc.image_of_continuousOn hcont).isBounded.subset_ball 0
    set R : ℕ := ⌈R₀⌉₊ + 1 with hRdef
    have hR1 : 1 ≤ R := Nat.le_add_left 1 _
    have hR₀R : R₀ ≤ (R : ℝ) := by
      rw [hRdef]
      push_cast
      linarith [Nat.le_ceil R₀]
    have hgeo : Core.IsGeodIn (S.D g) γ T R :=
      ⟨hgeod, hunit, hcont, fun t ht => ball_subset_ball hR₀R (hR₀ ⟨t, ht, rfl⟩)⟩
    have hTval : ENNReal.ofReal T = S.D g q := by
      rw [ofReal_eq_of_unitSpeed_geodesic _ hgeod hunit, h0', hT']
    set θ : ℕ → ℝ := fun j => 1 / ((j : ℝ) + 1) with hθdef
    set t : ℕ → ℝ := fun j => Real.exp (θ j) * ((1 + 1 / ((j : ℝ) + 1)) * T + θ j) with htdef
    have hQ : ∀ j : ℕ, ∀ᶠ n in atTop, ∃ x y : ℂ, dist x q.1 < θ j ∧ dist y q.2 < θ j ∧
        Core.lfppM S (ε n) (Y (ε n)) (x, y) ≤ ENNReal.ofReal (t j) := by
      intro j
      have hc := recovery_core S hW hg hR1 hgeo (j := j + 1) (Nat.le_add_left 1 j)
        (θ := θ j) (by positivity)
      have hεw : Tendsto (fun n => (ε n : ℝ)) atTop (𝓝[>] 0) :=
        tendsto_nhdsWithin_iff.2 ⟨hε, Eventually.of_forall fun n => (ε n).2⟩
      filter_upwards [hεw.eventually hc] with n hn
      obtain ⟨x, y, hx, hy, hxy⟩ := hn (ε n).2
      refine ⟨x, y, h0' ▸ hx, hT' ▸ hy, ?_⟩
      simpa only [htdef, Nat.cast_add, Nat.cast_one] using hxy
    obtain ⟨J, hJ, hJQ⟩ := exists_diag hQ
    classical
    set p : ℕ → ℂ × ℂ := fun n => if hn : ∃ x y : ℂ, dist x q.1 < θ (J n) ∧ dist y q.2 < θ (J n) ∧
        Core.lfppM S (ε n) (Y (ε n)) (x, y) ≤ ENNReal.ofReal (t (J n)) then
      (hn.choose, hn.choose_spec.choose) else q with hpdef
    have hpQ : ∀ᶠ n in atTop, dist (p n).1 q.1 < θ (J n) ∧ dist (p n).2 q.2 < θ (J n) ∧
        Core.lfppM S (ε n) (Y (ε n)) (p n) ≤ ENNReal.ofReal (t (J n)) := by
      filter_upwards [hJQ] with n hn
      simp only [hpdef, hn, ↓reduceDIte]
      exact hn.choose_spec.choose_spec
    have hu : Tendsto θ atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
    have hθJ : Tendsto (fun n => θ (J n)) atTop (𝓝 0) := hu.comp hJ
    have hp : Tendsto p atTop (𝓝 q) := by
      rw [tendsto_iff_dist_tendsto_zero]
      refine squeeze_zero' (Eventually.of_forall fun n => dist_nonneg) ?_ hθJ
      filter_upwards [hpQ] with n hn
      rw [Prod.dist_eq]
      exact max_le hn.1.le hn.2.1.le
    have ht : Tendsto t atTop (𝓝 T) := by
      have := ((Real.continuous_exp.tendsto 0).comp hu).mul
        ((((tendsto_const_nhds (x := (1 : ℝ))).add hu).mul (tendsto_const_nhds (x := T))).add hu)
      simpa only [htdef, hθdef, add_zero, Real.exp_zero, one_mul, Function.comp_def] using this
    refine ⟨p, hp, ?_⟩
    have hlow := lowerLimit S hG hW hg hε p q hp
    have hup : Tendsto (fun n => ((ENNReal.ofReal (t (J n)) : ℝ≥0∞) : EReal)) atTop
        (𝓝 ((S.D g).toLSCFun.1 q)) := by
      have hq : (S.D g).toLSCFun.1 q = ((ENNReal.ofReal T : ℝ≥0∞) : EReal) := by
        rw [hTval]
        rfl
      rw [hq]
      exact (continuous_coe_ennreal_ereal.tendsto _).comp (ENNReal.tendsto_ofReal (ht.comp hJ))
    refine tendsto_order.2 ⟨fun b hb => eventually_lt_of_lt_liminf (hb.trans_le hlow), fun b hb => ?_⟩
    filter_upwards [hup.eventually (gt_mem_nhds hb), hpQ] with n hn1 hn2
    exact lt_of_le_of_lt (EReal.coe_ennreal_le_coe_ennreal_iff.2 hn2.2.2) hn1

end SupercriticalLFPPAS.Main
