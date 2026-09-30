import QuantumZipper.Proofs.Zipper.UnifRC3Det
import QuantumZipper.Proofs.Zipper.JointModFinal

/-!
# UNIF-RC3 (decision D33): `UnifRC3Stmt` from a uniform-Cauchy input

Setup: `B` Brownian, `X` a free-boundary GFF modulo constants, `pathOf B ⟂ X`, `W = drive κ B`,
`y_u` the field unzipped by `u` (`= Yf κ (u+s) s B X`), `R_{u,s} = revMap (vrev W (u+s)) s`,
`α_{u,s} = (R_{u,s})_* fc(d, 2^{-k})` (`d ∈ Dy`). The regularized values

`Φ_j(u, s) = ∫ avgReg y_u j dα_{u,s}`   (`PhiJ`)

converge as `j → ∞` to `evalReg y_u α_{u,s}`. The **single open input** of the route D33 is

* `UnifUCStmt`: for each `k` and `d ∈ Dy`, almost surely `Φ_j` is uniformly Cauchy in `j` over
  the rational points of the triangle `tri T` (`triQ T`).

**Main result** `unifRC3Stmt_of_uc`: `UnifUCStmt ⇒ RegUnif.UnifRC3Stmt` (for `T > 0`), hence
`B3d.CapCocycleRegStmt` by `capCocycleRegStmt_of_unifRC3'`. Pathwise argument on one full event:

1. JointMod (`jointModStmt_holds`): a jointly continuous witness `Z(u, c, ρ)` of all `y_u`
   (`ae_exists_joint_witness`), so `Φ_j(u, s) = ∫ Z(u, R_{u,s}(z), 2^{-j}) dfc(z)`, continuous in
   `(u, s)` (`continuousOn_integral_comp_R`);
2. uniform Cauchy on `triQ T` + continuity ⇒ uniform Cauchy on `tri T` ⇒ a continuous limit
   `L = evalReg y_u α_{u,s}`;
3. the raw side `y_u(α_{u,s}) = y_{u+s}(fc) − Q ∫ log |R_{u,s}'| dfc` (`single_apply_fc`) is
   continuous (`RegCont.ae_continuousOn_unzippedField`, `continuousOn_integral_log_deriv_R`);
4. fixed-time RC3 (`ae_evalReg_Yf_fc_gen`) gives `L = y_u(α_{u,s})` on the countable set
   `triQ T`, which is dense in `tri T` (`tri_subset_closure_triQ`); conclude by continuity.

Sources: Duplantier–Sheffield, *Liouville quantum gravity and KPZ*, Invent. Math. 185 (2011),
Prop. 3.1 (through the fixed-time RC3 of `CoordRegComp` and JointMod); the uniformization by
density and continuity is an **own elementary argument** (as `UnifRCConv.tendsto_PsiK_of_uc`).
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal

namespace QuantumZipper
namespace RegUnif

open B2 RegCont TwoPoint

/-! ## Rational points of the time triangle -/

/-- The points of `tri T` with rational coordinates. -/
def triQ (T : ℝ) : Set (ℝ × ℝ) := {p | p ∈ tri T ∧ ∃ a b : ℚ, p = ((a : ℝ), (b : ℝ))}

theorem triQ_subset_tri (T : ℝ) : triQ T ⊆ tri T := fun _ hp => hp.1

theorem countable_triQ (T : ℝ) : (triQ T).Countable := by
  refine ((countable_range fun q : ℚ × ℚ => ((q.1 : ℝ), (q.2 : ℝ)))).mono ?_
  rintro p ⟨-, a, b, rfl⟩
  exact ⟨(a, b), rfl⟩

/-- **`triQ T` is dense in `tri T`** for `T > 0`. -/
theorem tri_subset_closure_triQ {T : ℝ} (hT : 0 < T) : tri T ⊆ closure (triQ T) := by
  set O : Set (ℝ × ℝ) := {p | 0 < p.1 ∧ 0 < p.2 ∧ p.1 + p.2 < T} with hO
  have hOo : IsOpen O :=
    (isOpen_lt continuous_const continuous_fst).inter
      ((isOpen_lt continuous_const continuous_snd).inter
        (isOpen_lt (continuous_fst.add continuous_snd) continuous_const))
  have hQ : Dense (range (Prod.map ((↑) : ℚ → ℝ) ((↑) : ℚ → ℝ))) :=
    Rat.denseRange_cast.prodMap Rat.denseRange_cast
  have hO1 : O ⊆ closure (triQ T) := by
    refine (hQ.open_subset_closure_inter hOo).trans (closure_mono ?_)
    rintro p ⟨⟨h1, h2, h3⟩, ⟨q, rfl⟩⟩
    exact ⟨⟨h1.le, h2.le, h3.le⟩, q.1, q.2, rfl⟩
  rintro ⟨u, s⟩ ⟨hu, hs, hus⟩
  set c : ℝ × ℝ := (T / 3, T / 3)
  set f : ℝ → ℝ × ℝ := fun l => ((1 - l) * u + l * (T / 3), (1 - l) * s + l * (T / 3)) with hf
  have hfc : Continuous f := by rw [hf]; fun_prop
  have hf0 : f 0 = (u, s) := by simp [hf]
  have hlim : Tendsto f (𝓝[>] 0) (𝓝 (u, s)) := by
    rw [← hf0]; exact hfc.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
  have hev : ∀ᶠ l in 𝓝[>] (0 : ℝ), f l ∈ closure (triQ T) := by
    filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < 1 by norm_num)] with l hl
    refine hO1 ⟨?_, ?_, ?_⟩
    · show 0 < (1 - l) * u + l * (T / 3)
      nlinarith [hl.1, hl.2]
    · show 0 < (1 - l) * s + l * (T / 3)
      nlinarith [hl.1, hl.2]
    · show (1 - l) * u + l * (T / 3) + ((1 - l) * s + l * (T / 3)) < T
      nlinarith [hl.1, hl.2]
  have := mem_closure_of_tendsto hlim hev
  rwa [closure_closure] at this

/-! ## A jointly continuous witness of all `y_u` -/

variable {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} {B : ℝ≥0 → Ω → ℝ}
  {X : Ω → FieldSample}

/-- **Jointly continuous witness** (the proof of `ae_forall_isRegularWith_of_jointMod`, keeping
the joint continuity of the witness). -/
theorem ae_exists_joint_witness [IsProbabilityMeasure P] {κ γ T : ℝ}
    (hB : IsBrownianReal B P) (hX : IsFreeGFFModConstH X P) (hind : IndepFun (pathOf B) X P)
    (hT : 0 < T) :
    ∀ᵐ ω ∂P, ∃ Z : ℝ × (ℂ × ℝ) → ℝ, ContinuousOn Z (parSet T) ∧ ∀ t ∈ Icc 0 T,
      IsRegularWith (unzippedField γ (ofFun (h0rev κ) + X ω, drive κ B ω) t)
        (fun p => Z (t, p)) := by
  obtain ⟨Zh, hc, hmod, hcomm⟩ := jointModStmt_holds κ γ hB hX hind hT
  obtain ⟨D, hDc, hDT, hTD⟩ := TopologicalSpace.exists_countable_dense_subset (Icc (0 : ℝ) T)
  set S4 : Set (ℝ × ((ℂ × ℝ) × ℝ)) := Icc 0 T ×ˢ ((Hbar ×ˢ Ioi 0) ×ˢ Ioi 0) with hS4
  obtain ⟨D4, hD4c, hD4S, hSD4⟩ := TopologicalSpace.exists_countable_dense_subset S4
  have hraw : ∀ᵐ ω ∂P, ∀ t ∈ D, ∀ k : ℕ, ∀ d ∈ Dy,
      unzippedField γ (ofFun (h0rev κ) + X ω, drive κ B ω) t (foldedCircle d (radius k)) =
        Zh (t, (d, radius k)) ω :=
    (eventually_countable_ball hDc).2 fun t ht => ae_all_iff.2 fun k =>
      (eventually_countable_ball countable_Dy).2 fun d hd =>
        (hmod (t, (d, radius k)) ⟨hDT ht, Dy_subset_Hbar hd, radius_pos k⟩).mono
          fun ω hω => hω.symm
  have hcm : ∀ᵐ ω ∂P, ∀ q ∈ D4, ∫ u, Zh (q.1, (u, q.2.2)) ω ∂foldedCircle q.2.1.1 q.2.1.2 =
      ∫ v, Zh (q.1, (v, q.2.1.2)) ω ∂foldedCircle q.2.1.1 q.2.2 :=
    (eventually_countable_ball hD4c).2 fun q hq => by
      obtain ⟨h1, ⟨h2, h3⟩, h4⟩ := hD4S hq
      exact hcomm q.1 h1 q.2.1.1 h2 q.2.1.2 q.2.2 h3 h4
  have hyc : ∀ᵐ ω ∂P, ∀ k : ℕ, ∀ d ∈ Dy, ContinuousOn
      (fun t => unzippedField γ (ofFun (h0rev κ) + X ω, drive κ B ω) t
        (foldedCircle d (radius k))) (Icc 0 T) :=
    ae_all_iff.2 fun k => (eventually_countable_ball countable_Dy).2 fun d _ =>
      RegCont.ae_continuousOn_unzippedField κ γ hB hX hind hT d (radius_pos k)
  filter_upwards [hraw, hcm, hyc] with ω h1 h2 h3
  exact ⟨fun q => Zh q ω, hc ω, fun t ht =>
    (forall_isRegularWith_of_joint (G := fun t p => Zh (t, p) ω) (hc ω) h3 hDT hTD h1 hD4S hSD4
      h2 t ht).1⟩

/-! ## The open input and the reduction -/

/-- The regularized values `Φ_j(u, s) = ∫ avgReg y_u j d(R_{u,s})_* fc(d, 2^{-k})`. -/
def PhiJ (κ : ℝ) (B : ℝ≥0 → Ω → ℝ) (X : Ω → FieldSample) (d : ℂ) (k j : ℕ) (ω : Ω)
    (p : ℝ × ℝ) : ℝ :=
  ∫ z, avgReg (Yf κ (p.1 + p.2) p.2 B X ω) j z
    ∂(foldedCircle d (radius k)).map (revMap (Vr κ (p.1 + p.2) B ω) p.2)

/-- **Open input of D33 (uniform Cauchy over rational times).** For every dyadic folded circle
`fc(d, 2^{-k})`, almost surely the regularized values `Φ_j` of the time-`u` field at the pushed
circle `(R_{u,s})_* fc(d, 2^{-k})` are uniformly Cauchy in `j`, uniformly over the rational
points of `tri T`. -/
def UnifUCStmt (κ T : ℝ) (P : Measure Ω) (B : ℝ≥0 → Ω → ℝ) (X : Ω → FieldSample) : Prop :=
  ∀ k : ℕ, ∀ d ∈ Dy, ∀ᵐ ω ∂P, ∀ n : ℕ, ∃ N : ℕ, ∀ j, N ≤ j → ∀ j', N ≤ j' →
    ∀ p ∈ triQ T, |PhiJ κ B X d k j ω p - PhiJ κ B X d k j' ω p| ≤ 1 / ((n : ℝ) + 1)

omit [MeasurableSpace Ω] in
/-- `Φ_j` in terms of a witness of `y_u`. -/
theorem PhiJ_eq_witness {κ : ℝ} {ω : Ω} (hc : Continuous fun s => B s ω) {Z : ℝ × (ℂ × ℝ) → ℝ}
    {T : ℝ} (hZr : ∀ t ∈ Icc 0 T, IsRegularWith
      (unzippedField (Real.sqrt κ) (ofFun (h0rev κ) + X ω, drive κ B ω) t) (fun p => Z (t, p)))
    (d : ℂ) (k j : ℕ) {p : ℝ × ℝ} (hp : p ∈ tri T) :
    PhiJ κ B X d k j ω p = ∫ z, Z (p.1, (revMap (vrev (drive κ B ω) (p.1 + p.2)) p.2 z,
      radius j)) ∂foldedCircle d (radius k) := by
  have hV : Continuous (Vr κ (p.1 + p.2) B ω) :=
    continuous_vrev (drive_continuous hc) _
  have hm := CoordRegComp.measurable_avgReg_right (Yf κ (p.1 + p.2) p.2 B X ω) j
  unfold PhiJ
  rw [integral_map (TwoPoint.measurable_revMap hV hp.2.1).aemeasurable hm.aestronglyMeasurable]
  refine integral_congr_ae ((foldedCircle_ae_mem_H d (radius_pos k)).mono fun z hz => ?_)
  rw [Yf_eq_unzippedField, add_sub_cancel_right]
  exact (hZr p.1 ⟨hp.1, by linarith [hp.2.1, hp.2.2]⟩).avgReg_eq j
    (im_revMap_pos hV hz hp.2.1).le

/-- **`UnifUCStmt ⇒ UnifRC3Stmt`** (hence `B3d.CapCocycleRegStmt`, `capCocycleRegStmt_of_uc`). -/
theorem unifRC3Stmt_of_uc [IsProbabilityMeasure P] {κ T : ℝ} (hB : IsBrownianReal B P)
    (hX : IsFreeGFFModConstH X P) (hind : IndepFun (pathOf B) X P) (hT : 0 < T)
    (hU : UnifUCStmt κ T P B X) : UnifRC3Stmt κ T P B X := by
  have hUC : ∀ᵐ ω ∂P, ∀ k : ℕ, ∀ d ∈ Dy, ∀ n : ℕ, ∃ N : ℕ, ∀ j, N ≤ j → ∀ j', N ≤ j' →
      ∀ p ∈ triQ T, |PhiJ κ B X d k j ω p - PhiJ κ B X d k j' ω p| ≤ 1 / ((n : ℝ) + 1) :=
    ae_all_iff.2 fun k => (eventually_countable_ball countable_Dy).2 fun d hd => hU k d hd
  have hfix : ∀ᵐ ω ∂P, ∀ k : ℕ, ∀ d ∈ Dy, ∀ p ∈ triQ T,
      evalReg (Yf κ (p.1 + p.2) p.2 B X ω)
          ((foldedCircle d (radius k)).map (revMap (Vr κ (p.1 + p.2) B ω) p.2)) =
        Yf κ (p.1 + p.2) p.2 B X ω
          ((foldedCircle d (radius k)).map (revMap (Vr κ (p.1 + p.2) B ω) p.2)) :=
    ae_all_iff.2 fun k => (eventually_countable_ball countable_Dy).2 fun d _ =>
      (eventually_countable_ball (countable_triQ T)).2 fun p hp =>
        ae_evalReg_Yf_fc_gen hB hX hind hp.1.2.1 (le_add_of_nonneg_left hp.1.1) d (radius_pos k)
  have hyc : ∀ᵐ ω ∂P, ∀ k : ℕ, ∀ d ∈ Dy, ContinuousOn
      (fun t => unzippedField (Real.sqrt κ) (ofFun (h0rev κ) + X ω, drive κ B ω) t
        (foldedCircle d (radius k))) (Icc 0 T) :=
    ae_all_iff.2 fun k => (eventually_countable_ball countable_Dy).2 fun d _ =>
      RegCont.ae_continuousOn_unzippedField κ (Real.sqrt κ) hB hX hind hT d (radius_pos k)
  filter_upwards [hUC, hfix, hyc, ae_exists_joint_witness (γ := Real.sqrt κ) hB hX hind hT,
    hB.cont, hB.eval_zero_ae_eq_zero] with ω h1 h2 h3 h4 hc h0
  intro u s hu hs hus k d hd
  obtain ⟨Z, hZc, hZr⟩ := h4
  have hW : Continuous (drive κ B ω) := drive_continuous hc
  have hW0 : drive κ B ω 0 = 0 := drive_zero h0
  obtain ⟨Φ, hΦdef⟩ : ∃ Φ : ℕ → ℝ × ℝ → ℝ, Φ = fun j p => PhiJ κ B X d k j ω p := ⟨_, rfl⟩
  -- step 1: continuity of `Φ_j`
  have hΦc : ∀ j, ContinuousOn (Φ j) (tri T) := fun j => by
    rw [hΦdef]
    exact (continuousOn_integral_comp_R hW hZc d (radius_pos k) (radius_pos j)).congr
      fun p hp => PhiJ_eq_witness hc hZr d k j hp
  -- step 2: uniform Cauchy on `tri T`, continuous limit
  have hUCt : ∀ n : ℕ, ∃ N : ℕ, ∀ j, N ≤ j → ∀ j', N ≤ j' → ∀ p ∈ tri T,
      |Φ j p - Φ j' p| ≤ 1 / ((n : ℝ) + 1) := by
    intro n
    obtain ⟨N, hN⟩ := h1 k d hd n
    refine ⟨N, fun j hj j' hj' p hp => ?_⟩
    have hcont : ContinuousOn (fun p => |Φ j p - Φ j' p|) (tri T) := ((hΦc j).sub (hΦc j')).abs
    refine ContinuousWithinAt.closure_le (tri_subset_closure_triQ hT hp)
      ((hcont p hp).mono (triQ_subset_tri T)) continuousWithinAt_const fun q hq => ?_
    rw [hΦdef]
    exact hN j hj j' hj' q hq
  have hUCS : UniformCauchySeqOn Φ atTop (tri T) := by
    rw [Metric.uniformCauchySeqOn_iff]
    intro ε hε
    obtain ⟨n, hn⟩ := exists_nat_one_div_lt hε
    obtain ⟨N, hN⟩ := hUCt n
    exact ⟨N, fun j hj j' hj' p hp => by
      rw [Real.dist_eq]; exact (hN j hj j' hj' p hp).trans_lt hn⟩
  obtain ⟨L, hLdef⟩ : ∃ L : ℝ × ℝ → ℝ, L = fun p => limUnder atTop fun j => Φ j p := ⟨_, rfl⟩
  have hlim : ∀ p ∈ tri T, Tendsto (fun j => Φ j p) atTop (𝓝 (L p)) := fun p hp => by
    rw [hLdef]; exact (hUCS.cauchySeq hp).tendsto_limUnder
  have hLc : ContinuousOn L (tri T) :=
    (hUCS.tendstoUniformlyOn_of_tendsto hlim).continuousOn (Frequently.of_forall hΦc)
  -- step 3: the raw side is continuous
  obtain ⟨g, hgdef⟩ : ∃ g : ℝ × ℝ → ℝ, g = fun p => Yf κ (p.1 + p.2) p.2 B X ω
      ((foldedCircle d (radius k)).map (revMap (Vr κ (p.1 + p.2) B ω) p.2)) := ⟨_, rfl⟩
  have hgc : ContinuousOn g (tri T) := by
    have c1 : ContinuousOn (fun p : ℝ × ℝ => unzippedField (Real.sqrt κ)
        (ofFun (h0rev κ) + X ω, drive κ B ω) (p.1 + p.2) (foldedCircle d (radius k))) (tri T) :=
      (h3 k d hd).comp (continuous_fst.add continuous_snd).continuousOn fun p hp =>
        ⟨add_nonneg hp.1 hp.2.1, hp.2.2⟩
    have c2 := continuousOn_integral_log_deriv_R hW hW0 T d (radius_pos k)
    refine (c1.sub ((continuousOn_const (c := Qc (Real.sqrt κ))).mul c2)).congr fun p hp => ?_
    have e := single_apply_fc (Real.sqrt κ) (ofFun (h0rev κ) + X ω) hW hW0 hp.1 hp.2.1 d
      (radius_pos k)
    change unzippedField (Real.sqrt κ) (ofFun (h0rev κ) + X ω, drive κ B ω) (p.1 + p.2)
      (foldedCircle d (radius k)) = _ at e
    rw [hgdef, Pi.sub_apply, Pi.mul_apply, e, add_sub_cancel_right]
    beta_reduce
    rw [Yf_eq_unzippedField, add_sub_cancel_right]
    rfl
  -- step 4: agreement on `triQ T`, then everywhere
  have hEq : EqOn L g (triQ T) := fun p hp => by
    rw [hLdef, hgdef, hΦdef]
    exact h2 k d hd p hp
  have hfin := hEq.of_subset_closure hLc hgc (triQ_subset_tri T) (tri_subset_closure_triQ hT)
    (show (u, s) ∈ tri T from ⟨hu, hs, hus⟩)
  rw [hLdef, hgdef, hΦdef] at hfin
  exact hfin

/-- **`B3d.CapCocycleRegStmt` from `UnifUCStmt`.** -/
theorem capCocycleRegStmt_of_uc [IsProbabilityMeasure P] {κ T : ℝ} (hB : IsBrownianReal B P)
    (hX : IsFreeGFFModConstH X P) (hind : IndepFun (pathOf B) X P) (hT : 0 < T)
    (hU : UnifUCStmt κ T P B X) : B3d.CapCocycleRegStmt κ T P B X :=
  capCocycleRegStmt_of_unifRC3' hB hX hind hT (unifRC3Stmt_of_uc hB hX hind hT hU)

end RegUnif
end QuantumZipper
