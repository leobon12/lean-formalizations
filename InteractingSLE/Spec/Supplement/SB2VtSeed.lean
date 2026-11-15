/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.SB2VtLe
import InteractingSLE.Spec.Supplement.SB2WeStmt
import InteractingSLE.Spec.Supplement.SB2WeCol
import InteractingSLE.Spec.Supplement.SBS3MarkedRecenter
import InteractingSLE.Spec.Restart.RetPlumbLine
import InteractingSLE.Spec.Exist.FlowField

/-!
# The relative seed of SB2(1)'s launch word (E7 at time `0`)

Packet PROVE-AUX61-NOJUMP (round 19). Round 18's named input `Vs.SB2RelSeedAdmStatement` (in D22's bounded form
`Vt.SB2RelSeedAdmLeStatement`) is PROVED here from Theorem 1.3, Lemma S3 for `ψ ≤ π/2` and the committed second
clause of PROVE-T14-SB2WORD (`Lv.sb2StageActiveWord2Statement`).

The argument is E7's first direction at the relative time `0` (the general-time form is SB2WORD's round 3; the
deterministic lemmas below follow its proof, restricted to what time `0` needs):

* `origBad κ ψ u b`: the bad real points of the original data for the upper flow from `u` (right of `u` with right
  weight `≤ −2`, left of `u` with left weight `≤ −2`);
* `wR_eq_of_isFlowType`, `wL_eq_of_isFlowType`: the cumulative weights of the cell word at a point are the weights of
  the word's height beside it;
* `phys_bad_right`, `phys_bad_left`: by the second clause, the heights beside a bad relative point are original heights
  at free original-real points (an old lower side has right weight `> −2` since `ψ > −π/2`), so the read-back of that
  point through the inverse chart is in the closure of `origBad`;
* **`not_seed_of_good`** (deterministic): if the read-back of the entry `m` is not a real point of `closure origBad`,
  the cell's seed is not at its threshold;
* `ae_word_eq_shift`: K2's launch word is the staged witness word shifted by the entry (chart transport through the
  recentred chart and GFF uniqueness);
* `mem_sb2BadClosure_of_mem_closure_origBad`: `origBad` shifted by `u` is in NOJUMP's closed bad set;
* **`ae_seed_of_geom`**, **`sb2RelSeedAdmLeStatement`**: the relative seed almost surely on every type cell. The
  read-back of the entry is the flow's position at the entrance (`η T_L`, from one chain record), which is off the
  closed bad set (`Vr.ae_notMem_closure_badSet`);
* `sb2RelSeedAdmStatement_of_S3`: round 18's all-angle input discharged in its own context;
* **`sb2LineVersionSLeStatement_of_thm'`**: `Lv.SB2LineVersionS` for every launch problem with `ψ ≤ π/2` from
  Theorems 1.2–1.3 alone.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology Metric Finset
open scoped NNReal ENNReal
open QuantumZipper (H chiC)
open LQGMetric (DistOn)

universe u

namespace InteractingSLE.Theorem14.SB.Vt

open Exist Exist.StagedLaw Exist.Staged Restart GW1W Lv Sec7.PocketTraversal Supp8.Q3Stop
open PiecewiseConstantBoundaryData (rightLim leftLim)

/-- **The bad real points of the original data** for the upper flow from `u` at angle `ψ`. -/
def origBad (κ ψ u : ℝ) (b : ℝ → ℝ) : Set ℝ :=
  {x | u < x ∧ Sec4.cumWeightRight κ (rightLim b x + ψ * chiC κ) ≤ -2} ∪
    {x | x < u ∧ Sec4.cumWeightLeft κ (leftLim b x + ψ * chiC κ) ≤ -2}

/-! ### Weights of the cell word from its heights -/

section Weights

variable {κ ψ : ℝ} {c : BoundaryWord} {nL nR : ℕ} {xL : Fin nL → ℝ} {xR : Fin nR → ℝ} {ρL : Fin nL → ℝ}
  {ρR : Fin nR → ℝ}

/-- A finite family of reals leaves a gap right of every point. -/
theorem exists_gap_right {n : ℕ} (x : Fin n → ℝ) (y : ℝ) : ∃ y₁, y < y₁ ∧ ∀ j, ¬ (y < x j ∧ x j < y₁) := by
  classical
  set M := (univ.filter (fun j => y < x j)).image x with hM
  by_cases hne : M.Nonempty
  · refine ⟨M.min' hne, ?_, fun j hj => ?_⟩
    · obtain ⟨j, hj, he⟩ := Finset.mem_image.1 (M.min'_mem hne)
      rw [← he]
      exact (Finset.mem_filter.1 hj).2
    · have := M.min'_le (x j) (Finset.mem_image.2 ⟨j, Finset.mem_filter.2 ⟨mem_univ _, hj.1⟩, rfl⟩)
      linarith [hj.2]
  · refine ⟨y + 1, by linarith, fun j hj => hne ⟨x j, Finset.mem_image.2 ⟨j, ?_, rfl⟩⟩⟩
    exact Finset.mem_filter.2 ⟨mem_univ _, hj.1⟩

/-- A finite family of reals leaves a gap left of every point. -/
theorem exists_gap_left {n : ℕ} (x : Fin n → ℝ) (y : ℝ) : ∃ y₁, y₁ < y ∧ ∀ j, ¬ (y₁ < x j ∧ x j < y) := by
  obtain ⟨y₁, hy₁, hgap⟩ := exists_gap_right (fun j => -x j) (-y)
  refine ⟨-y₁, by linarith, fun j hj => hgap j ⟨by linarith [hj.2], by linarith [hj.1]⟩⟩

/-- **The right cumulative weight of the cell word at `y ≥ 0`** is the right weight of the word's height just right of
`y`. -/
theorem wR_eq_of_isFlowType (hκ : 0 < κ) (hft : FCDet.IsFlowType κ ψ c xL xR ρL ρR) {y : ℝ} (hy : 0 ≤ y) :
    ∃ y₁, y < y₁ ∧ ∀ y'', y < y'' → y'' < y₁ → y'' ∉ c.jumps →
      Vq.wR xR ρR y = Sec4.cumWeightRight κ (c.fn y'' + ψ * chiC κ) := by
  obtain ⟨y₁, hy₁, hgap⟩ := exists_gap_right xR y
  refine ⟨y₁, hy₁, fun y'' hy'' hy''₁ hJ => ?_⟩
  have hfilt : univ.filter (fun j => xR j ≤ y) = univ.filter (fun j => xR j ≤ y'') :=
    Finset.filter_congr fun j _ => ⟨fun h => h.trans hy''.le, fun h => by
      by_contra hn
      push Not at hn
      exact hgap j ⟨hn, lt_of_le_of_lt h hy''₁⟩⟩
  have hy''0 : y'' ≠ 0 := (lt_of_le_of_lt hy hy'').ne'
  unfold Vq.wR
  rw [hfilt, ← Sec4.cumWeightRight_forceBoundaryData hκ ρL ρR xL xR (hy.trans hy''.le),
    RetAux79.forceBoundaryData_zero_of_isFlowType hft y'',
    forceBoundaryData_flowLine_seed hκ c.isPiecewiseConstantBoundaryData 0 ψ hy''0 (by rwa [add_zero]), add_zero]

/-- **The left cumulative weight of the cell word at `y ≤ 0`** is the left weight of the word's height just left of
`y`. -/
theorem wL_eq_of_isFlowType (hκ : 0 < κ) (hft : FCDet.IsFlowType κ ψ c xL xR ρL ρR) {y : ℝ} (hy : y ≤ 0) :
    ∃ y₁, y₁ < y ∧ ∀ y'', y₁ < y'' → y'' < y → y'' ∉ c.jumps →
      Vq.wL xL ρL y = Sec4.cumWeightLeft κ (c.fn y'' + ψ * chiC κ) := by
  obtain ⟨y₁, hy₁, hgap⟩ := exists_gap_left xL y
  refine ⟨y₁, hy₁, fun y'' hy₁'' hy'' hJ => ?_⟩
  have hfilt : univ.filter (fun i => y ≤ xL i) = univ.filter (fun i => y'' < xL i) :=
    Finset.filter_congr fun i _ => ⟨fun h => lt_of_lt_of_le hy'' h, fun h => by
      by_contra hn
      push Not at hn
      exact hgap i ⟨lt_trans hy₁'' h, hn⟩⟩
  have hy''0 : y'' < 0 := lt_of_lt_of_le hy'' hy
  unfold Vq.wL
  rw [hfilt, ← Sec4.cumWeightLeft_forceBoundaryData hκ ρL ρR xL xR hy''0,
    RetAux79.forceBoundaryData_zero_of_isFlowType hft y'',
    forceBoundaryData_flowLine_seed hκ c.isPiecewiseConstantBoundaryData 0 ψ hy''0.ne (by rwa [add_zero]),
    add_zero]

end Weights

/-! ### A bad relative point is read back in the closure of the bad set -/

section Corr

variable {κ ψ u m : ℝ} {b : ℝ → ℝ} {jumps : Finset ℝ} {c : Chart} {g : ℂ → ℂ} {β cw : BoundaryWord}
  {Fw : Finset ℝ} {nL nR : ℕ} {xL : Fin nL → ℝ} {xR : Fin nR → ℝ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ}

/-- A complex limit of real points of a set is a real point of its closure. -/
theorem exists_real_mem_closure_of_tendsto {l : Filter ℝ} [l.NeBot] {f : ℝ → ℂ} {p : ℂ} (hf : Tendsto f l (𝓝 p))
    {B : Set ℝ} (hB : ∀ᶠ y in l, ∃ x ∈ B, f y = (x : ℂ)) : ∃ x₀ : ℝ, p = x₀ ∧ x₀ ∈ closure B := by
  have hcl : p ∈ closure (((↑) : ℝ → ℂ) '' B) :=
    mem_closure_of_tendsto hf (hB.mono fun y ⟨x, hx, he⟩ => ⟨x, hx, he.symm⟩)
  have him : p.im = 0 := by
    have hc : IsClosed {z : ℂ | z.im = 0} := isClosed_eq Complex.continuous_im continuous_const
    exact closure_minimal (by rintro _ ⟨x, -, rfl⟩; simp) hc hcl
  refine ⟨p.re, Complex.ext (by simp) (by simp [him]), Metric.mem_closure_iff.2 fun ε hε => ?_⟩
  obtain ⟨_, ⟨x, hx, rfl⟩, hd⟩ := Metric.mem_closure_iff.1 hcl ε hε
  refine ⟨x, hx, ?_⟩
  rw [Real.dist_eq]
  calc |p.re - x| = |(p - (x : ℂ)).re| := by simp
    _ ≤ ‖p - (x : ℂ)‖ := Complex.abs_re_le_norm _
    _ = dist p (x : ℂ) := (dist_eq_norm _ _).symm
    _ < ε := hd

theorem tendsto_g_real (hgc : ContinuousOn g {z | 0 ≤ z.im}) (l : Filter ℝ) {y : ℝ} (hly : l ≤ 𝓝 y) :
    Tendsto (fun y'' : ℝ => g ((y'' + m : ℝ) : ℂ)) l (𝓝 (g ((y + m : ℝ) : ℂ))) := by
  have hcont : Tendsto (fun y'' : ℝ => ((y'' + m : ℝ) : ℂ)) (𝓝 y) (𝓝[{z : ℂ | 0 ≤ z.im}] ((y + m : ℝ) : ℂ)) :=
    tendsto_nhdsWithin_iff.2 ⟨((Complex.continuous_ofReal.comp (continuous_id.add continuous_const)).tendsto y),
      Eventually.of_forall fun y'' => by simp⟩
  exact ((hgc _ (by simp)).tendsto.comp hcont).mono_left hly

/-- **A bad right relative point is read back in the closure of the bad set** (second clause, right side). -/
theorem phys_bad_right (hκ : 0 < κ) (hκ4 : κ < 4) (hψ : -(Real.pi / 2) < ψ)
    (hb : IsPiecewiseConstantBoundaryData b jumps) (hcc : c.IsConformal) (hgc : ContinuousOn g {z | 0 ≤ z.im})
    (hgi : EqOn g c.2.1 H) (hSC : SecondClause κ b jumps c u m β.fn β.jumps) (hcw : ∀ y ∉ Fw, cw.fn y = β.fn (y + m))
    (hft : FCDet.IsFlowType κ ψ cw xL xR ρL ρR) {y : ℝ} (hy : 0 ≤ y) (hbad : Vq.wR xR ρR y ≤ -2) :
    ∃ x₀ : ℝ, g ((y + m : ℝ) : ℂ) = x₀ ∧ x₀ ∈ closure (origBad κ ψ u b) := by
  classical
  obtain ⟨hc, S, Fx, Fy, hSm, hSc, hSo, hSy, hSr, -⟩ := hSC
  obtain ⟨y₁, hy₁, hw⟩ := wR_eq_of_isFlowType hκ hft hy
  have hl := Sec4.sleLambda_pos hκ
  have hχ := Sec4.chiC_pos hκ hκ4
  set E : Finset ℝ := cw.jumps ∪ Fw ∪ β.jumps.image (· - m) ∪ Fy.image (· - m) ∪
    (jumps ∪ Fx ∪ {u}).image (fun x => rProf c x - m) with hE
  have hgood : ∀ y'', y < y'' → y'' < y₁ → y'' ∉ E → ∃ x ∈ origBad κ ψ u b, g ((y'' + m : ℝ) : ℂ) = (x : ℂ) := by
    intro y'' h1 h2 hE''
    have hcwJ : y'' ∉ cw.jumps := fun h => hE'' (Finset.mem_union_left _ (Finset.mem_union_left _
      (Finset.mem_union_left _ (Finset.mem_union_left _ h))))
    have hFw : y'' ∉ Fw := fun h => hE'' (Finset.mem_union_left _ (Finset.mem_union_left _
      (Finset.mem_union_left _ (Finset.mem_union_right _ h))))
    have hβJ : y'' + m ∉ β.jumps := fun h => hE'' (Finset.mem_union_left _ (Finset.mem_union_left _
      (Finset.mem_union_right _ (Finset.mem_image.2 ⟨y'' + m, h, by ring⟩))))
    have hFy : y'' + m ∉ Fy := fun h => hE'' (Finset.mem_union_left _
      (Finset.mem_union_right _ (Finset.mem_image.2 ⟨y'' + m, h, by ring⟩)))
    have hwr := hw y'' h1 h2 hcwJ
    rw [hwr, hcw y'' hFw] at hbad
    have hlow : β.fn (y'' + m) + ψ * chiC κ ≤ -sleLambda κ := by
      unfold Sec4.cumWeightRight at hbad
      have : (β.fn (y'' + m) + ψ * chiC κ) / sleLambda κ ≤ -1 := by linarith
      rw [div_le_iff₀ hl] at this
      linarith
    rcases hSy (y'' + m) hβJ hFy with ⟨hβ, -⟩ | ⟨x, hxS, hxy⟩
    · exfalso
      rw [hβ] at hlow
      have : 0 < (ψ + Real.pi / 2) * chiC κ := mul_pos (by linarith) hχ
      linarith
    · have hxJ : x ∉ jumps := fun h => hE'' (Finset.mem_union_right _ (Finset.mem_image.2
        ⟨x, Finset.mem_union_left _ (Finset.mem_union_left _ h), by rw [hxy]; ring⟩))
      have hxF : x ∉ Fx := fun h => hE'' (Finset.mem_union_right _ (Finset.mem_image.2
        ⟨x, Finset.mem_union_left _ (Finset.mem_union_right _ h), by rw [hxy]; ring⟩))
      have hxu : x ≠ u := fun h => hE'' (Finset.mem_union_right _ (Finset.mem_image.2
        ⟨x, Finset.mem_union_right _ (Finset.mem_singleton.2 h), by rw [hxy]; ring⟩))
      have hzJ : rProf c x ∉ β.jumps := by rw [hxy]; exact hβJ
      have hbx : β.fn (rProf c x) = b x := hSo x hxS hxJ hxF hzJ
      have hux : u ≤ x := hSr x hxS (by rw [hxy]; linarith)
      refine ⟨x, Or.inl ⟨lt_of_le_of_ne hux (Ne.symm hxu), ?_⟩, ?_⟩
      · rw [rightLim_eq_of_notMem hb hxJ, ← hbx, hxy]
        unfold Sec4.cumWeightRight
        have : (β.fn (y'' + m) + ψ * chiC κ) / sleLambda κ ≤ -1 := by
          rw [div_le_iff₀ hl]; linarith
        linarith
      · have h1 := bdry_eq_of_chartFree hcc hgc hgi (hSc x hxS).1 (hSc x hxS).2 (hc x)
        rw [hc.eq_ofReal x, hxy] at h1
        exact h1
  have hev : ∀ᶠ y'' in 𝓝[>] y, ∃ x ∈ origBad κ ψ u b, g ((y'' + m : ℝ) : ℂ) = (x : ℂ) := by
    have h1 : ∀ᶠ y'' in 𝓝[>] y, y'' < y₁ := (gt_mem_nhds hy₁).filter_mono nhdsWithin_le_nhds
    have h2 : ∀ᶠ y'' in 𝓝[>] y, y'' ∉ (E : Set ℝ) :=
      (eventually_notMem_of_finite E.finite_toSet y).filter_mono (nhdsWithin_mono _ fun z hz => ne_of_gt hz)
    filter_upwards [self_mem_nhdsWithin, h1, h2] with y'' hy'' hy''₁ hy''E
    exact hgood y'' hy'' hy''₁ hy''E
  obtain ⟨x₀, hx₀, hcl⟩ := exists_real_mem_closure_of_tendsto
    (tendsto_g_real (m := m) hgc (𝓝[>] y) nhdsWithin_le_nhds) hev
  exact ⟨x₀, hx₀, hcl⟩

/-- **A bad left relative point is read back in the closure of the bad set** (second clause, left side). -/
theorem phys_bad_left (hκ : 0 < κ) (hb : IsPiecewiseConstantBoundaryData b jumps) (hcc : c.IsConformal)
    (hgc : ContinuousOn g {z | 0 ≤ z.im}) (hgi : EqOn g c.2.1 H) (hSC : SecondClause κ b jumps c u m β.fn β.jumps)
    (hcw : ∀ y ∉ Fw, cw.fn y = β.fn (y + m)) (hft : FCDet.IsFlowType κ ψ cw xL xR ρL ρR) {y : ℝ} (hy : y ≤ 0)
    (hbad : Vq.wL xL ρL y ≤ -2) :
    ∃ x₀ : ℝ, g ((y + m : ℝ) : ℂ) = x₀ ∧ x₀ ∈ closure (origBad κ ψ u b) := by
  classical
  obtain ⟨hc, S, Fx, Fy, hSm, hSc, hSo, hSy, -, hSl⟩ := hSC
  obtain ⟨y₁, hy₁, hw⟩ := wL_eq_of_isFlowType hκ hft hy
  set E : Finset ℝ := cw.jumps ∪ Fw ∪ β.jumps.image (· - m) ∪ Fy.image (· - m) ∪
    (jumps ∪ Fx).image (fun x => rProf c x - m) with hE
  have hgood : ∀ y'', y₁ < y'' → y'' < y → y'' ∉ E → ∃ x ∈ origBad κ ψ u b, g ((y'' + m : ℝ) : ℂ) = (x : ℂ) := by
    intro y'' h1 h2 hE''
    have hcwJ : y'' ∉ cw.jumps := fun h => hE'' (Finset.mem_union_left _ (Finset.mem_union_left _
      (Finset.mem_union_left _ (Finset.mem_union_left _ h))))
    have hFw : y'' ∉ Fw := fun h => hE'' (Finset.mem_union_left _ (Finset.mem_union_left _
      (Finset.mem_union_left _ (Finset.mem_union_right _ h))))
    have hβJ : y'' + m ∉ β.jumps := fun h => hE'' (Finset.mem_union_left _ (Finset.mem_union_left _
      (Finset.mem_union_right _ (Finset.mem_image.2 ⟨y'' + m, h, by ring⟩))))
    have hFy : y'' + m ∉ Fy := fun h => hE'' (Finset.mem_union_left _
      (Finset.mem_union_right _ (Finset.mem_image.2 ⟨y'' + m, h, by ring⟩)))
    have hwl := hw y'' h1 h2 hcwJ
    rw [hwl, hcw y'' hFw] at hbad
    rcases hSy (y'' + m) hβJ hFy with ⟨-, hmy⟩ | ⟨x, hxS, hxy⟩
    · exfalso
      linarith
    · have hxJ : x ∉ jumps := fun h => hE'' (Finset.mem_union_right _ (Finset.mem_image.2
        ⟨x, Finset.mem_union_left _ h, by rw [hxy]; ring⟩))
      have hxF : x ∉ Fx := fun h => hE'' (Finset.mem_union_right _ (Finset.mem_image.2
        ⟨x, Finset.mem_union_right _ h, by rw [hxy]; ring⟩))
      have hzJ : rProf c x ∉ β.jumps := by rw [hxy]; exact hβJ
      have hbx : β.fn (rProf c x) = b x := hSo x hxS hxJ hxF hzJ
      have hxu : x < u := hSl x hxS (by rw [hxy]; linarith)
      refine ⟨x, Or.inr ⟨hxu, ?_⟩, ?_⟩
      · rw [leftLim_eq_of_notMem hb hxJ, ← hbx, hxy]
        exact hbad
      · have h1 := bdry_eq_of_chartFree hcc hgc hgi (hSc x hxS).1 (hSc x hxS).2 (hc x)
        rw [hc.eq_ofReal x, hxy] at h1
        exact h1
  have hev : ∀ᶠ y'' in 𝓝[<] y, ∃ x ∈ origBad κ ψ u b, g ((y'' + m : ℝ) : ℂ) = (x : ℂ) := by
    have h1 : ∀ᶠ y'' in 𝓝[<] y, y₁ < y'' := (lt_mem_nhds hy₁).filter_mono nhdsWithin_le_nhds
    have h2 : ∀ᶠ y'' in 𝓝[<] y, y'' ∉ (E : Set ℝ) :=
      (eventually_notMem_of_finite E.finite_toSet y).filter_mono (nhdsWithin_mono _ fun z hz => ne_of_lt hz)
    filter_upwards [self_mem_nhdsWithin, h1, h2] with y'' hy'' hy''₁ hy''E
    exact hgood y'' hy''₁ hy'' hy''E
  obtain ⟨x₀, hx₀, hcl⟩ := exists_real_mem_closure_of_tendsto
    (tendsto_g_real (m := m) hgc (𝓝[<] y) nhdsWithin_le_nhds) hev
  exact ⟨x₀, hx₀, hcl⟩

/-- **The relative seed is admissible when the entry is read back off the closed bad set** (deterministic, E7's
first direction at time `0`). -/
theorem not_seed_of_good (hκ : 0 < κ) (hκ4 : κ < 4) (hψ : -(Real.pi / 2) < ψ)
    (hb : IsPiecewiseConstantBoundaryData b jumps) (hcc : c.IsConformal) (hgc : ContinuousOn g {z | 0 ≤ z.im})
    (hgi : EqOn g c.2.1 H) (hSC : SecondClause κ b jumps c u m β.fn β.jumps) (hcw : ∀ y ∉ Fw, cw.fn y = β.fn (y + m))
    (hft : FCDet.IsFlowType κ ψ cw xL xR ρL ρR)
    (hgood : ∀ x : ℝ, g (m : ℂ) = x → x ∉ closure (origBad κ ψ u b)) :
    ¬ ForceWord.ThresholdCondition ρL ρR 0 xL xR := by
  obtain ⟨hxL0, hxR0⟩ := RetAux79.isFlowType_signs hft
  have hm : (((0 : ℝ) + m : ℝ) : ℂ) = (m : ℂ) := by simp
  rintro (hL | hR)
  · have hw : Vq.wL xL ρL 0 ≤ -2 := by
      unfold Vq.wL
      have e : univ.filter (fun i => (0 : ℝ) ≤ xL i) = univ.filter (fun i => xL i = 0) :=
        Finset.filter_congr fun i _ => ⟨fun h => le_antisymm (hxL0 i) h, fun h => h.ge⟩
      rw [e]; exact hL
    obtain ⟨x₀, hx₀, hcl⟩ := phys_bad_left hκ hb hcc hgc hgi hSC hcw hft le_rfl hw
    rw [hm] at hx₀
    exact hgood x₀ hx₀ hcl
  · have hw : Vq.wR xR ρR 0 ≤ -2 := by
      unfold Vq.wR
      have e : univ.filter (fun j => xR j ≤ (0 : ℝ)) = univ.filter (fun j => xR j = 0) :=
        Finset.filter_congr fun j _ => ⟨fun h => le_antisymm h (hxR0 j), fun h => h.le⟩
      rw [e]; exact hR
    obtain ⟨x₀, hx₀, hcl⟩ := phys_bad_right hκ hκ4 hψ hb hcc hgc hgi hSC hcw hft le_rfl hw
    rw [hm] at hx₀
    exact hgood x₀ hx₀ hcl

end Corr

/-- **`origBad` shifted by `u` lies in NOJUMP's closed bad set of the flow from `u`.** -/
theorem mem_sb2BadClosure_of_mem_closure_origBad {κ ψ u : ℝ} (hκ : 0 < κ) {b : ℝ → ℝ} {jumps : Finset ℝ}
    (hb : IsPiecewiseConstantBoundaryData b jumps) {x : ℝ} (hx : x ∈ closure (origBad κ ψ u b)) :
    (((x - u : ℝ)) : ℂ) ∈ Vr.sb2BadClosure κ b jumps u ψ := by
  refine map_mem_closure (f := fun y : ℝ => ((y - u : ℝ) : ℂ))
    (Complex.continuous_ofReal.comp (continuous_id.sub continuous_const)) hx ?_
  rintro y (⟨hyu, hy⟩ | ⟨hyu, hy⟩)
  · refine ⟨by simp, Or.inl ⟨by simp; linarith, ?_⟩⟩
    have e := Vr.cumWeightRight_rightLim_flowLine hκ hb u ψ (y := y - u) (by linarith)
    rw [sub_add_cancel] at e
    simp only [Complex.ofReal_re]
    rw [← e]; exact hy
  · refine ⟨by simp, Or.inr ⟨by simp; linarith, ?_⟩⟩
    have e := Vr.cumWeightLeft_leftLim_flowLine hκ hb u ψ (y := y - u) (by linarith)
    rw [sub_add_cancel] at e
    simp only [Complex.ofReal_re]
    rw [← e]; exact hy

section

variable {κ : ℝ} {b : ℝ → ℝ} {jumps : Finset ℝ} {Ω : Type u} [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω]
  {P : Measure Ω} [IsProbabilityMeasure P] {h : Ω → DistOn upperHalfPlaneOpens}
  {E : ExplSpec → ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞} {k : ℕ} {u ψ : ℝ} {η : Ω → ℝ≥0 → ℂ} {ζ : Ω → ℝ≥0∞}

/-- **K2's launch word is the staged witness word shifted by the entry** (off finite sets, almost surely at a
launch). -/
theorem ae_word_eq_shift (HP : SB2LaunchProblem κ b jumps P h E k u ψ η ζ) (I : K2LaunchInputs κ b jumps P h E k u ψ)
    {β : Ω → BoundaryWord} {Y : Ω → DistOn upperHalfPlaneOpens}
    (hW : IsStageWitness κ b jumps P h (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)
      (E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)) (k + 1) β Y) :
    ∀ᵐ ω₀ ∂P, ω₀ ∈ launchSet κ b jumps E (k + 1) →
      ∀ y ∉ (I.word ω₀).jumps ∪ (BoundaryWord.shiftW (launchEntry κ b jumps E (k + 1) u ω₀) (β ω₀)).jumps,
        (I.word ω₀).fn y = (β ω₀).fn (y + launchEntry κ b jumps E (k + 1) u ω₀) := by
  set w : ExplSpec := boundaryWalkSpec b jumps (-(Real.pi / 2)) true with hwdef
  have hw := isBoundaryContinuedProgram_boundaryWalkSpec b jumps (θ := -(Real.pi / 2))
    ⟨le_rfl, by linarith [Real.pi_pos]⟩ true
  have hS := HP.staged w hw
  have h𝒢 := hS.2.1 (k + 1)
  have hrun := ae_ae_run_eq (κ := κ) runMeasStatement HP.boundary w (k := k + 1) (fun j _ => hS.1 j)
    (fun j _ => HP.drivers_regular w j) (P := P)
  have hTk := Sec7.Aux122Disint.ae_ae_condExpKernel (P := P) h𝒢 hW.2.2.1
  filter_upwards [hW.2.2.1, hW.2.2.2, hrun, hTk, I.field, I.chart_eq] with ω₀ hT₀ hG₀ hr₀ hTk₀ hfield hceq hF
  obtain ⟨⟨c₀, θ₀⟩, hcθ⟩ := Option.ne_none_iff_exists'.1 hF
  have hc₀ : Lv.launchChart κ b jumps E (k + 1) ω₀ =
      stChart (ExplState.run κ b jumps w (fun j => E w j ω₀) (k + 1)) := by
    rw [launchChart_eq hcθ, (eq_launch_of_launches _ _ hcθ).2.2]
  obtain ⟨hpc, h', hT', hG'⟩ := hfield hF
  obtain ⟨hconf, hlift, -⟩ := hT₀ hF
  set m := launchEntry κ b jumps E (k + 1) u ω₀ with hmdef
  have hceq' := hceq hF
  rw [hc₀] at hceq'
  have hae : h' =ᵐ[condExpKernel P (pastSigma κ b jumps w (E w) (k + 1)) ω₀]
      (fun ω => flowField m 0 (Y ω)) := by
    filter_upwards [hr₀, hTk₀] with ω hω hTω
    have hl : (ExplState.run κ b jumps w (fun j => E w j ω) (k + 1 + 1)).2.2.2.1 (k + 1) ≠ none := by
      rw [launches_run_succ_of_run_eq (κ := κ) (b := b) (jumps := jumps) w hω]
      exact hF
    obtain ⟨-, -, hTY⟩ := hTω hl
    rw [hω] at hTY
    have hrec := SB.S3.isChartTransport_recenter_word hconf hlift hTY m
    have hT'' := hT' ω
    rw [hceq'] at hT''
    exact hT''.unique (hconf.recenter m) hrec
  have hG'' : IsGFFWithBoundaryData (condExpKernel P (pastSigma κ b jumps w (E w) (k + 1)) ω₀) h'
      (BoundaryWord.shiftW m (β ω₀)).fn (BoundaryWord.shiftW m (β ω₀)).jumps :=
    isGFFWithBoundaryData_congr_ae (Exist.StagedLaw.isGFFWithBoundaryData_shiftW m (hG₀ hF)) hG'.1 hae.symm
  intro y hy
  rw [eq_of_isGFFWithBoundaryData hpc (BoundaryWord.shiftW m (β ω₀)).isPiecewiseConstantBoundaryData hG' hG'' y hy,
    BoundaryWord.fn_shiftW]

/-- A horizon after the entrance: `T ≤ ζ`, `T_L < T`, `0 < S₁`, `T_L + S₁ < T`. -/
theorem exists_horizon {TL Z : ℝ≥0∞} (hT : TL < Z) :
    ∃ (T : ℝ≥0) (S₁ : ℝ), (T : ℝ≥0∞) ≤ Z ∧ TL < T ∧ 0 < S₁ ∧ TL.toReal + S₁ < T := by
  have hTL : TL ≠ ⊤ := ne_top_of_lt hT
  have hcoe : ((TL.toNNReal : ℝ≥0) : ℝ≥0∞) = TL := ENNReal.coe_toNNReal hTL
  have e2 : TL.toReal = (TL.toNNReal : ℝ) := rfl
  by_cases hζ : Z = ⊤
  · refine ⟨TL.toNNReal + 2, 1, by rw [hζ]; exact le_top, ?_, one_pos, ?_⟩
    · calc TL = ((TL.toNNReal : ℝ≥0) : ℝ≥0∞) := hcoe.symm
        _ < ((TL.toNNReal + 2 : ℝ≥0) : ℝ≥0∞) := ENNReal.coe_lt_coe.2 (lt_add_of_pos_right _ two_pos)
    · rw [e2]; push_cast; linarith
  · have hZc : (((Z.toNNReal : ℝ≥0)) : ℝ≥0∞) = Z := ENNReal.coe_toNNReal hζ
    have hlt : (TL.toNNReal : ℝ) < Z.toNNReal := by
      rw [← hcoe, ← hZc, ENNReal.coe_lt_coe] at hT; exact hT
    refine ⟨Z.toNNReal, ((Z.toNNReal : ℝ) - TL.toNNReal) / 2, hZc.le, ?_, by linarith, ?_⟩
    · calc TL = ((TL.toNNReal : ℝ≥0) : ℝ≥0∞) := hcoe.symm
        _ < ((Z.toNNReal : ℝ≥0) : ℝ≥0∞) := ENNReal.coe_lt_coe.2 (by exact_mod_cast hlt)
    · rw [e2]; linarith

/-- **The relative seed almost surely on every type cell**, given the chain records almost surely at a launch
(SB2(1)'s launch problem). -/
theorem ae_seed_of_geom (HP : SB2LaunchProblem κ b jumps P h E k u ψ η ζ)
    (hgeoAE : ∀ᵐ ω ∂P, ω ∈ launchSet κ b jumps E (k + 1) → Vs.LineGeomAt κ b jumps E k u η ζ ω)
    (I : K2LaunchInputs κ b jumps P h E k u ψ) {u₀ : ℂ → ℝ} (D : EntranceUnion κ b jumps P h E k u η ζ u₀)
    (w : WordType) :
    ∀ᵐ ω ∂P, ω ∈ wordTypeCell κ ψ I.word D.event w →
      ¬ ForceWord.ThresholdCondition (typedRhoL w) (typedRhoR w) 0 (cellXL κ ψ I.word w ω)
        (cellXR κ ψ I.word w ω) := by
  obtain ⟨β, Y, hW, hβ⟩ := sb2StageActiveWord2Statement κ HP.kappa_pos HP.kappa_lt_four b jumps HP.boundary P h
    HP.field HP.admissible E HP.staged HP.pieces_regular HP.drivers_regular k
  filter_upwards [hβ u HP.seed_nonpos, ae_word_eq_shift HP I hW, hW.2.2.1, hgeoAE,
    D.ae_mem_event_iff,
    Vr.ae_notMem_closure_badSet HP.kappa_pos HP.kappa_lt_four HP.boundary HP.field HP.flow]
    with ω hβω heqω hTω hgeo hev hnv hcell
  have hD : ω ∈ D.event := hcell.1
  have hF : ω ∈ launchSet κ b jumps E (k + 1) := D.event_subset hD
  have hT : Ve.entT κ b jumps E k u η ζ ω < ζ ω := (hev hF).1 hD
  -- the launch chart is conformal
  obtain ⟨⟨c₀, θ₀⟩, hcθ⟩ := Option.ne_none_iff_exists'.1 hF
  have hc₀ : Lv.launchChart κ b jumps E (k + 1) ω =
      stChart (ExplState.run κ b jumps (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)
        (fun j => E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) j ω) (k + 1)) := by
    rw [launchChart_eq hcθ, (eq_launch_of_launches _ _ hcθ).2.2]
  have hcc : (Lv.launchChart κ b jumps E (k + 1) ω).IsConformal := by rw [hc₀]; exact (hTω hF).1
  have hft : FCDet.IsFlowType κ ψ (I.word ω) (cellXL κ ψ I.word w ω) (cellXR κ ψ I.word w ω) (typedRhoL w)
      (typedRhoR w) :=
    FCDet.isFlowType_of_mem_typeSet (mem_typeSet_of_mem_wordTypeCell hcell)
  -- one chain record: the inverse of the shifted chart, and the entry read back at the entrance
  obtain ⟨T, S₁, hTζ, hvis, hS₁, hS₁T⟩ := exists_horizon hT
  obtain ⟨p, g, β', γ, tL, Wr, ηr, -, ⟨-, hgc, hgi, -, -⟩, ⟨-, -, -, -, htL, -, hγ0, hlift⟩, hag, -, -⟩ :=
    hgeo hF T hTζ hvis S₁ hS₁ hS₁T
  set m := launchEntry κ b jumps E (k + 1) u ω with hmdef
  set c := Lv.launchChart κ b jumps E (k + 1) ω with hcdef
  have hg0 : g 0 = η ω tL - u := by
    have h1 := hlift 0
    rw [hγ0, add_zero] at h1
    rw [h1]
    exact hag tL (by linarith)
  -- the inverse of the launch chart itself
  set gc : ℂ → ℂ := fun z => g (z - m) + u with hgcdef
  have hgcc : ContinuousOn gc {z | 0 ≤ z.im} := by
    refine (hgc.comp (continuous_id.sub continuous_const).continuousOn fun z hz => ?_).add continuousOn_const
    show 0 ≤ (z - (m : ℂ)).im
    simpa using hz
  have hgci : EqOn gc c.2.1 H := by
    intro z hz
    have hz' : z - (m : ℂ) ∈ H := by
      show 0 < (z - (m : ℂ)).im
      simpa using (show 0 < z.im from hz)
    simp only [hgcdef, hgi hz', Lw.shiftChart_inv, sub_add_cancel]
  have hgcm : gc (m : ℂ) = η ω tL := by simp only [hgcdef, sub_self, hg0, sub_add_cancel]
  refine not_seed_of_good HP.kappa_pos HP.kappa_lt_four HP.angle HP.boundary hcc hgcc hgci (hβω hF).2 (heqω hF) hft
    fun x hx hcl => ?_
  -- the read-back of the entry is the flow at the entrance, off the closed bad set
  have hmem := mem_sb2BadClosure_of_mem_closure_origBad HP.kappa_pos HP.boundary hcl
  have htLζ : (tL : ℝ≥0∞) < ζ ω := by rw [htL]; exact hT
  apply hnv (lt_of_le_of_lt (zero_le) htLζ) tL htLζ
  rw [← hgcm, hx]
  exact_mod_cast hmem

end

/-- **The relative seed for `ψ ≤ π/2`, PROVED** from Theorem 1.3 and Lemma S3 for `ψ ≤ π/2`. -/
theorem sb2RelSeedAdmLeStatement (h13 : Exist.Theorem13Statement.{u})
    (hS3 : Tc.SB2EntranceNoCommonArcLeStatement.{u}) : SB2RelSeedAdmLeStatement.{u} :=
  fun _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HP _ I _ D w _ =>
    ae_seed_of_geom HP (Vc.ae_lineGeom_liftOfLe h13 hS3 HP) I D w

/-- **Round 18's named input `Vs.SB2RelSeedAdmStatement`, discharged** in its own (all-angle) context: from Theorem
1.3 and the all-angle Lemma S3 that round 18's chain takes. (D22 replaces that chain by the bounded one below.) -/
theorem sb2RelSeedAdmStatement_of_S3 (h13 : Exist.Theorem13Statement.{u})
    (hS3 : Tc.SB2EntranceNoCommonArcStatement.{u}) : Vs.SB2RelSeedAdmStatement.{u} :=
  fun _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HP I _ D w _ =>
    ae_seed_of_geom HP (Vc.ae_lineGeom_liftOf h13 hS3 HP) I D w

/-- Round 18's top without the seed input (all-angle Lemma S3). -/
theorem sb2LineVersionSStatement_of_S3 (h13 : Exist.Theorem13Statement.{u})
    (hS3 : Tc.SB2EntranceNoCommonArcStatement.{u}) : Vs.SB2LineVersionSStatement.{u} :=
  Vs.sb2LineVersionSStatement h13 hS3 (sb2RelSeedAdmStatement_of_S3 h13 hS3)

/-- **SB2(1)'s successor versions for every launch problem with `ψ ≤ π/2`, from Theorems 1.2–1.3 alone.** -/
theorem sb2LineVersionSLeStatement_of_thm' (h12p : Theorem12ParamStatement.{u})
    (h13 : Exist.Theorem13Statement.{u}) (h12p₀ : Theorem12ParamStatement.{0})
    (h13₀ : Exist.Theorem13Statement.{0}) : SB2LineVersionSLeStatement.{u} :=
  sb2LineVersionSLeStatement_of_thm h12p h13 h12p₀ h13₀
    (sb2RelSeedAdmLeStatement h13 (Tc.sb2EntranceNoCommonArcLeStatement_of_thm h12p h13 h12p₀ h13₀))

end InteractingSLE.Theorem14.SB.Vt
