import QuantumZipper.Proofs.LQG.ZoomRadialEndBasic

/-!
# The radial process at a zoom is the wedge radial process: final assembly (TASKS.md R6, D3-RAD-D)

Final assembly of the D3 radial comparison `abs_prob_zoomRadial_sub_le` (TASKS.md row R6,
blueprint SECTION5 node D3 / E_BRANCH D3⁺): the radially normalized process at the first hitting
time `Tc` of `0` by the drifted Brownian path `Xc c b = c + √2 b + (α−Q)·`, truncated at `−S`,
matches the wedge radial process on every measurable path set `E` up to the event that the wedge
path's backward half is `≥ c` on the window `[−S,0]`:

`|P{trunc S (Vpath) ∈ E} − P'{trunc S (A) ∈ E}| ≤ 2 P'{∃u ∈ [0,S], c ≤ A(−u)}`.

* **(iv) `prob_Tc_lt_le_prob_wedge_high`** — the Williams comparison: `{Tc < S}` is contained in
  `{∃u ∈ [0,S], c ≤ Zp u}` for the Williams pasting `Zp` (`Zp (Tc) = Xc 0 = c`), whose law is that
  of the Williams path `Yh u = A(−u)` (`hW`); the uncountable quantifier is made measurable by
  replacing it with rational times at thresholds `c − 1/(n+1)` (`exists_rat_Icc_le_sub`), which is
  legitimate because `Zp` and `Yh` are continuous *for every* `ω` after passing to the nice
  versions of `B, B'` (`exists_nice_version`).
* **(iii) `prob_trunc_Vpath_cross`** (proved in `ZoomRadialFinal.lean`) — the left-hand side
  depends only on the law of the Brownian motion, and the sandwich
  (`ZoomRadial.prob_trunc_Vpath_le_add`, `prob_trunc_Rw_le_add`) bounds the difference by
  `P'{Tc < S}`, which (iv) bounds by the wedge-high event.

Sources: Sheffield (arXiv:1012.4797) §1.6 and the proof of Prop. 1.6; Williams (1974);
Rogers–Pitman (1981) Thm 1; Revuz–Yor VII.4. The rational reduction of the hitting condition and
the `ℝ≥0∞` algebra are own elementary arguments (proof-route deviation only, the same device as
`ZoomRadialMain.tendsto_prob_wedge_high`); `exists_rat_Icc_le_sub` generalizes
`ZoomRadialMain.exists_rat_Icc_le_sub_one` (own elementary proof).
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology

namespace QuantumZipper
namespace ZoomRadial

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
-- `Ω'` is at universe `0` because `WilliamsDriftDecomposition` only quantifies over `Type`
variable {Ω' : Type} [MeasurableSpace Ω'] {P' : Measure Ω'} [IsProbabilityMeasure P']

/-! ## 5. Step (iv): the Williams comparison -/

/-- If `c − 1/(n+1) ≤ x` for every `n : ℕ`, then `c ≤ x` (own elementary proof). -/
theorem le_of_forall_one_div_nat_le {c x : ℝ} (h : ∀ n : ℕ, c - 1 / (n + 1) ≤ x) : c ≤ x := by
  refine le_of_forall_pos_le_add fun ε hε => ?_
  obtain ⟨n, hn⟩ : ∃ n : ℕ, 1 / (n + 1 : ℝ) < ε := by
    obtain ⟨n, hn⟩ := exists_nat_gt ε⁻¹
    refine ⟨n, ?_⟩
    have h2 : ε * ε⁻¹ < ε * (n : ℝ) := mul_lt_mul_of_pos_left hn hε
    have h3 : ε * ε⁻¹ = 1 := mul_inv_cancel₀ (ne_of_gt hε)
    rw [div_lt_iff₀ (by positivity : (0 : ℝ) < (n : ℝ) + 1)]
    nlinarith [h2, h3]
  linarith [h n]

/-- **D3-RAD step (iv): the Williams comparison.** The zoom happens before time `S` only with
probability at most that of the wedge path's backward half reaching `c` somewhere on `[−S, 0]`. -/
theorem prob_Tc_lt_le_prob_wedge_high (hW : WilliamsDriftDecomposition) {α Q : ℝ} (hαQ : α < Q)
    {B B' : ℝ≥0 → Ω' → ℝ} (hB : IsBrownianReal B P') (hB' : IsBrownianReal B' P')
    (hInd : IndepFun (pathOf B) (pathOf B') P') {A : ℝ → Ω' → ℝ}
    (hAB : ∀ ω t, A t ω = wedgePath α Q (fun s => B s ω) (fun s => B' s ω) t)
    {c S : ℝ} (hc : 0 < c) (hS : 0 ≤ S) :
    P' {ω | Tc α Q c B ω < S} ≤ P' {ω | ∃ u ∈ Set.Icc 0 S, c ≤ A (-u) ω} := by
  classical
  obtain ⟨β, hβm, hβc, hβz, hβh, hβb⟩ := exists_nice_version (P := P') hB hαQ hc
  obtain ⟨β', hβ'm, hβ'c, hβ'z, hβ'h, hβ'b⟩ := exists_nice_version (P := P') hB' hαQ hc
  -- β, β' are Brownian motions and independent
  have hβB : IsBrownianReal β P' :=
    ⟨hB.toIsPreBrownianReal.congr (fun s => hβb.mono fun ω h => (h s).symm), ae_of_all _ hβc⟩
  have hβ'B : IsBrownianReal β' P' :=
    ⟨hB'.toIsPreBrownianReal.congr (fun s => hβ'b.mono fun ω h => (h s).symm), ae_of_all _ hβ'c⟩
  have hind : IndepFun (pathOf β) (pathOf β') P' :=
    hInd.congr (hβb.mono fun ω h => funext fun s => (h s).symm)
      (hβ'b.mono fun ω h => funext fun s => (h s).symm)
  -- the good set
  set G : Set Ω' := {ω | (∀ s : ℝ≥0, β s ω = B s ω) ∧ (∀ s : ℝ≥0, β' s ω = B' s ω)} with hG
  have hGnull : P' Gᶜ = 0 := by
    have h1 : P' {ω | ¬ (∀ s : ℝ≥0, β s ω = B s ω)} = 0 := ae_iff.1 hβb
    have h2 : P' {ω | ¬ (∀ s : ℝ≥0, β' s ω = B' s ω)} = 0 := ae_iff.1 hβ'b
    have hsub : Gᶜ ⊆ {ω | ¬ (∀ s : ℝ≥0, β s ω = B s ω)} ∪
        {ω | ¬ (∀ s : ℝ≥0, β' s ω = B' s ω)} := by
      intro ω hω
      rw [hG, Set.mem_compl_iff, Set.mem_setOf_eq, not_and_or] at hω
      exact hω.elim Or.inl Or.inr
    refine le_antisymm ?_ zero_le
    calc P' Gᶜ ≤ P' ({ω | ¬ (∀ s : ℝ≥0, β s ω = B s ω)} ∪
          {ω | ¬ (∀ s : ℝ≥0, β' s ω = B' s ω)}) := measure_mono hsub
      _ ≤ P' {ω | ¬ (∀ s : ℝ≥0, β s ω = B s ω)} +
          P' {ω | ¬ (∀ s : ℝ≥0, β' s ω = B' s ω)} := measure_union_le _ _
      _ = 0 := by rw [h1, h2, add_zero]
  -- the rational-indexed path set
  set 𝓠 : Set (ℝ≥0 → ℝ) := ⋂ n : ℕ, ⋃ q : {q : ℚ // (q : ℝ) ∈ Set.Icc 0 S},
      {p : ℝ≥0 → ℝ | c - 1 / (n + 1) ≤ p (q.1 : ℝ).toNNReal} with h𝓠
  have h𝓠m : MeasurableSet 𝓠 := by
    rw [h𝓠]
    exact MeasurableSet.iInter fun n => MeasurableSet.iUnion fun q =>
      measurableSet_le measurable_const (measurable_pi_apply _)
  -- the `Zp`-side inclusion: `{Tc < S} ⊆ Zp⁻¹'𝓠 ∪ Gᶜ`
  have hsub1 : {ω : Ω' | Tc α Q c B ω < S} ⊆ willZpNN α Q c β β' ⁻¹' 𝓠 ∪ Gᶜ := by
    intro ω hω
    by_cases hGω : ω ∈ G
    · left
      rw [Set.mem_preimage, h𝓠]
      simp only [Set.mem_iInter, Set.mem_iUnion, Set.mem_setOf_eq]
      intro n
      -- the hitting time of β, in the `willTc` parametrization
      have hspec : 0 ≤ willTc α Q c β ω ∧ willX α Q β (willTc α Q c β ω) ω = -c ∧
          ∀ s : ℝ, 0 ≤ s → willX α Q β s ω ≤ -c → willTc α Q c β ω ≤ s := by
        have hdrift : ∃ s : ℝ, 0 ≤ s ∧ Xdrift α Q (pathOf β ω) s ≤ -c :=
          exists_drift_le (α := α) (Q := Q) (c := c) (β := β) (ω := ω) (hβh ω)
        have h := WedgeTrans.hitTime_spec (continuous_Xdrift (hβc ω))
          (by simp only [Xdrift, pathOf, Real.toNNReal_zero, hβz ω, mul_zero, sub_zero])
          hc hdrift
        simpa only [WedgeTrans.hitTime, willTc, willX, Xdrift, pathOf] using h
      have hTB : willTc α Q c β ω = Tc α Q c B ω := by
        rw [willTc_eq_Tc]
        have hX : ∀ t : ℝ, Xc α Q c β ω t = Xc α Q c B ω t := fun t => by
          simp only [Xc, hGω.1 t.toNNReal]
        rw [Tc, Tc]
        congr 1
        ext t
        exact and_congr_right fun _ => by rw [hX t]
      have hT0 : 0 ≤ willTc α Q c β ω := hspec.1
      have hTlt : willTc α Q c β ω < S := by rw [hTB]; exact hω
      have hTpos : 0 < willTc α Q c β ω := by
        rcases lt_trichotomy (willTc α Q c β ω) 0 with h | h | h
        · exact absurd hT0 (not_le.2 h)
        · exfalso
          have h0 : willX α Q β 0 ω = 0 := by
            simp only [willX, Real.toNNReal_zero, hβz ω, mul_zero, sub_zero]
          have hc' := hspec.2.1
          rw [h, h0] at hc'
          linarith
        · exact h
      -- rationalization at the hitting time
      obtain ⟨q, hqmem, hq⟩ := exists_rat_Icc_le_sub
        (f := fun u : ℝ => willZp α Q c β β' u.toNNReal ω)
        (S := S) (c := c) (u := willTc α Q c β ω) (ε := 1 / (↑n + 1))
        ((continuous_willZp (α := α) (Q := Q) (c := c) (ω := ω) (hβc ω) (hβz ω) (hβ'c ω)
          (hβ'z ω)).comp (NNReal.continuous_coe.comp continuous_real_toNNReal))
        hS ⟨hT0, hTlt.le⟩ (by
          rw [show willZp α Q c β β' (willTc α Q c β ω).toNNReal ω
              = willZp α Q c β β' (willTc α Q c β ω) ω from by
                rw [Real.coe_toNNReal _ hT0]]
          exact le_of_eq (willZp_Tc α Q c β β' ω (hβz ω)).symm)
        (by positivity : (0 : ℝ) < 1 / (↑n + 1))
      exact ⟨⟨q, hqmem⟩, by
        simpa only [willZpNN] using hq⟩
    · exact Or.inr hGω
  -- the `Yh`-side inclusion: `Yh⁻¹'𝓠 ∩ G ⊆ {∃u ∈ [0,S], c ≤ A (−u)}`
  have hsub2 : (willYhNN α Q β' ⁻¹' 𝓠) ∩ G ⊆ {ω : Ω' | ∃ u ∈ Set.Icc 0 S, c ≤ A (-u) ω} := by
    intro ω hω
    obtain ⟨h𝓠ω, hGω⟩ := hω
    have hwit : ∀ n : ℕ, ∃ q : {q : ℚ // (q : ℝ) ∈ Set.Icc 0 S},
        c - 1 / (n + 1) ≤ willYh α Q β' ((q.1 : ℝ).toNNReal) ω := by
      intro n
      have h := h𝓠ω
      simp only [Set.mem_preimage, h𝓠, Set.mem_iInter, Set.mem_iUnion, Set.mem_setOf_eq] at h
      exact h n
    -- on `G` the backward half of `A` is the Williams path of `β'`
    have hAY : ∀ u ∈ Set.Icc (0 : ℝ) S, A (-u) ω = willYh α Q β' u ω := by
      intro u hu
      by_cases hu0 : u = 0
      · subst hu0
        rw [neg_zero]
        have hA0 : A 0 ω = 0 := by
          rw [hAB ω 0]
          simp only [wedgePath, if_pos le_rfl, Real.toNNReal_zero, mul_zero, add_zero]
          rw [(hGω.1 0).symm, hβz ω, mul_zero]
        rw [hA0, willYh_zero α Q β' ω (hβ'c ω) (hβ'z ω)]
      · have hupos : 0 < u := lt_of_le_of_ne hu.1 (Ne.symm hu0)
        have hneg : ¬ ((0 : ℝ) ≤ -u) := by linarith
        have hBt : (fun s : ℝ => √2 * B' s.toNNReal ω - (α - Q) * s) = willYt α Q β' ω := by
          funext s
          simp only [willYt]
          rw [show B' s.toNNReal ω = β' s.toNNReal ω from (hGω.2 s.toNNReal).symm]
          ring
        rw [hAB ω (-u)]
        show (if (0 : ℝ) ≤ -u then √2 * B (-u).toNNReal ω + (α - Q) * (-u)
          else (fun s : ℝ => √2 * B' s.toNNReal ω - (α - Q) * s)
            (-(-u) + lastZero (fun s : ℝ => √2 * B' s.toNNReal ω - (α - Q) * s))) =
          willYh α Q β' u ω
        rw [if_neg hneg, hBt, neg_neg]
    -- maximize the continuous function `u ↦ Yh u` on `[0,S]`
    set F : ℝ → ℝ := fun x => willYh α Q β' x.toNNReal ω with hF
    have hFc : Continuous F := by
      rw [show F = fun x : ℝ => willYt α Q β' ω (x.toNNReal + lastZero (willYt α Q β' ω)) from rfl]
      refine ((continuous_const.mul ((hβ'c ω).comp continuous_real_toNNReal)).add
        (continuous_const.mul continuous_id)).comp ?_
      exact (NNReal.continuous_coe.comp continuous_real_toNNReal).add continuous_const
    obtain ⟨u₀, hu₀mem, hu₀max⟩ := isCompact_Icc.exists_isMaxOn
      (⟨0, le_rfl, hS⟩ : (Set.Icc (0 : ℝ) S).Nonempty) hFc.continuousOn
    have hcu₀ : c ≤ F u₀ := by
      refine le_of_forall_one_div_nat_le fun n => ?_
      obtain ⟨q, hq⟩ := hwit n
      calc c - 1 / (↑n + 1) ≤ willYh α Q β' ((q.1 : ℝ).toNNReal) ω := hq
        _ = F (q.1 : ℝ) := by
            rw [show F (q.1 : ℝ) = willYh α Q β' ((q.1 : ℝ).toNNReal) ω from rfl]
        _ ≤ F u₀ := hu₀max q.2
    refine ⟨u₀, hu₀mem, ?_⟩
    rw [hAY u₀ hu₀mem]
    rw [show willYh α Q β' u₀ ω = F u₀ from
      congrArg (fun x : ℝ => willYh α Q β' x ω) (Real.coe_toNNReal u₀ hu₀mem.1).symm]
    exact hcu₀
  -- transfer the rational event through the Williams law equality
  have hZpa : AEMeasurable (willZpNN α Q c β β') P' :=
    (measurable_willZp_path hc hβm hβ'm hβc hβz hβ'c hβ'z hβh).aemeasurable
  have hYha : AEMeasurable (willYhNN α Q β') P' := by
    have hYtc : ∀ ω, Continuous (willYt α Q β' ω) := fun ω =>
      (continuous_const.mul ((hβ'c ω).comp continuous_real_toNNReal)).add
        (continuous_const.mul continuous_id)
    have hYtm : ∀ s : ℝ, Measurable fun ω => willYt α Q β' ω s := fun s =>
      (((hβ'm.of_uncurry_left (x := s.toNNReal)).const_mul (√2))).add_const ((Q - α) * s)
    have hLm : Measurable fun ω => lastZero (willYt α Q β' ω) :=
      WedgeMeas.measurable_lastZero hYtc hYtm
    have hYtJ : Measurable fun p : Ω' × ℝ => willYt α Q β' p.1 p.2 :=
      (measurable_uncurry_of_continuous_of_measurable (u := fun r ω => willYt α Q β' ω r)
        hYtc hYtm).comp measurable_swap
    refine (measurable_pi_iff.2 fun u : ℝ≥0 => ?_).aemeasurable
    simp only [willYhNN, willYh]
    exact hYtJ.comp (measurable_id.prodMk (measurable_const.add hLm))
  have hkey : P' (willZpNN α Q c β β' ⁻¹' 𝓠) = P' (willYhNN α Q β' ⁻¹' 𝓠) := by
    rw [show P' (willZpNN α Q c β β' ⁻¹' 𝓠) = (P'.map (willZpNN α Q c β β')) 𝓠 from
        (Measure.map_apply_of_aemeasurable hZpa h𝓠m).symm,
      show P' (willYhNN α Q β' ⁻¹' 𝓠) = (P'.map (willYhNN α Q β')) 𝓠 from
        (Measure.map_apply_of_aemeasurable hYha h𝓠m).symm,
      williams_law hW hαQ hc hβB hβ'B hind]
  have hYhle : P' (willYhNN α Q β' ⁻¹' 𝓠) ≤
      P' {ω | ∃ u ∈ Set.Icc 0 S, c ≤ A (-u) ω} := by
    have hsplit : willYhNN α Q β' ⁻¹' 𝓠 ⊆
        ((willYhNN α Q β' ⁻¹' 𝓠) ∩ G) ∪ Gᶜ := by
      intro ω hω
      by_cases hG : ω ∈ G
      · exact Or.inl ⟨hω, hG⟩
      · exact Or.inr hG
    calc P' (willYhNN α Q β' ⁻¹' 𝓠)
        ≤ P' (((willYhNN α Q β' ⁻¹' 𝓠) ∩ G) ∪ Gᶜ) := measure_mono hsplit
      _ ≤ P' ((willYhNN α Q β' ⁻¹' 𝓠) ∩ G) + P' Gᶜ := measure_union_le _ _
      _ = P' ((willYhNN α Q β' ⁻¹' 𝓠) ∩ G) := by rw [hGnull, add_zero]
      _ ≤ P' {ω | ∃ u ∈ Set.Icc 0 S, c ≤ A (-u) ω} := measure_mono hsub2
  calc P' {ω | Tc α Q c B ω < S}
      ≤ P' (willZpNN α Q c β β' ⁻¹' 𝓠 ∪ Gᶜ) := measure_mono hsub1
    _ ≤ P' (willZpNN α Q c β β' ⁻¹' 𝓠) + P' Gᶜ := measure_union_le _ _
    _ = P' (willZpNN α Q c β β' ⁻¹' 𝓠) := by rw [hGnull, add_zero]
    _ = P' (willYhNN α Q β' ⁻¹' 𝓠) := hkey
    _ ≤ P' {ω | ∃ u ∈ Set.Icc 0 S, c ≤ A (-u) ω} := hYhle

/-! ## 6. The assembled comparison -/

/-- **TASKS.md R6, D3-RAD: the radial process at a zoom is the wedge radial process.** The
truncated radially normalized process at the zoom has, on every measurable set of paths `E`, the
same probability (up to `2 P'{∃u ∈ [0,S], c ≤ A(−u)}`) as the truncated wedge radial process.

Sources: Sheffield (arXiv:1012.4797) §1.6 and the proof of Prop. 1.6 (the radial process at a zoom
is `BM + drift` re-centred at its first hit of `0`, compared with the wedge radial process);
Williams (1974); Rogers–Pitman (1981) Thm 1; Revuz–Yor VII.4. -/
theorem abs_prob_zoomRadial_sub_le (hW : WilliamsDriftDecomposition) {α Q : ℝ} (hαQ : α < Q)
    {b : ℝ≥0 → Ω → ℝ} (hb : IsBrownianReal b P) {A : ℝ → Ω' → ℝ}
    (hA : IsWedgeProcess α Q A P') {c S : ℝ} (hc : 0 < c) (hS : 0 ≤ S)
    {E : Set (ℝ → ℝ)} (hE : MeasurableSet E) :
    |(P {ω | (fun s => zoomRadial α Q b c ω (max s (-S))) ∈ E}).toReal -
      (P' {ω' | (fun s => A (max s (-S)) ω') ∈ E}).toReal| ≤
    2 * (P' {ω' | ∃ u ∈ Set.Icc 0 S, c ≤ A (-u) ω'}).toReal := by
  classical
  obtain ⟨B, B', hB, hB', hInd, hAB⟩ := hA
  have hcross : P {ω | trunc S (Vpath α Q c b ω) ∈ E} =
      P' {ω' | trunc S (Vpath α Q c B ω') ∈ E} :=
    prob_trunc_Vpath_cross (P' := P') (B := B) hB hαQ hc hE hb
  have hpush : P' {ω | trunc S (Rw α Q B B' c ω) ∈ E} =
      P' {ω | trunc S (fun t => A t ω) ∈ E} :=
    prob_trunc_Rw_eq_prob_trunc_wedge (P' := P') hW hαQ
      ⟨B, B', hB, hB', hInd, hAB⟩ hc hB hB' hAB hE
  have hcmp : P' {ω | Tc α Q c B ω < S} ≤
      P' {ω | ∃ u ∈ Set.Icc 0 S, c ≤ A (-u) ω} :=
    prob_Tc_lt_le_prob_wedge_high (P' := P') hW hαQ hB hB' hInd hAB hc hS
  have hs1 : P' {ω | trunc S (Vpath α Q c B ω) ∈ E} ≤
      P' {ω | trunc S (Rw α Q B B' c ω) ∈ E} + P' {ω | Tc α Q c B ω < S} :=
    prob_trunc_Vpath_le_add (P := P') (b := B) (b' := B') (E := E)
  have hs2 : P' {ω | trunc S (Rw α Q B B' c ω) ∈ E} ≤
      P' {ω | trunc S (Vpath α Q c B ω) ∈ E} + P' {ω | Tc α Q c B ω < S} :=
    prob_trunc_Rw_le_add (P := P') (b := B) (b' := B') (E := E)
  set a : ℝ≥0∞ := P' {ω | trunc S (Vpath α Q c B ω) ∈ E} with ha
  set r : ℝ≥0∞ := P' {ω | trunc S (Rw α Q B B' c ω) ∈ E} with hr
  set δ : ℝ≥0∞ := P' {ω | Tc α Q c B ω < S} with hδ
  set X : ℝ≥0∞ := P' {ω' | ∃ u ∈ Set.Icc 0 S, c ≤ A (-u) ω'} with hX
  have hδX : δ ≤ X := by rw [hδ, hX]; exact hcmp
  have h1 : a.toReal ≤ r.toReal + δ.toReal := by
    refine (ENNReal.toReal_mono ?_ ?_).trans ENNReal.toReal_add_le
    · rw [ENNReal.add_ne_top]; exact ⟨measure_ne_top P' _, measure_ne_top P' _⟩
    · rw [ha, hr, hδ]; exact hs1
  have h2 : r.toReal ≤ a.toReal + δ.toReal := by
    refine (ENNReal.toReal_mono ?_ ?_).trans ENNReal.toReal_add_le
    · rw [ENNReal.add_ne_top]; exact ⟨measure_ne_top P' _, measure_ne_top P' _⟩
    · rw [ha, hr, hδ]; exact hs2
  have h3 : |a.toReal - r.toReal| ≤ δ.toReal := abs_sub_le_iff.2 ⟨by linarith, by linarith⟩
  have h4 : δ.toReal ≤ 2 * X.toReal := by
    have h5 : δ.toReal ≤ X.toReal := ENNReal.toReal_mono (measure_ne_top P' _) hδX
    linarith [ENNReal.toReal_nonneg (a := X)]
  have e1 : P {ω | (fun s => zoomRadial α Q b c ω (max s (-S))) ∈ E} = a := by
    rw [← hcross]
    rfl
  have e2 : P' {ω' | (fun s => A (max s (-S)) ω') ∈ E} = r := by
    rw [hpush]
    rfl
  rw [e1, e2]
  exact h3.trans h4

end ZoomRadial
end QuantumZipper
