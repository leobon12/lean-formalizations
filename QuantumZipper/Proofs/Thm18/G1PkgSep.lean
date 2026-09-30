import QuantumZipper.Proofs.Thm18.G1PkgChord
import Mathlib.Topology.ContinuousMap.SecondCountableSpace
import Mathlib.Topology.ContinuousMap.Compact
import Mathlib.Topology.UnitInterval

/-!
# G1 package: separability of simple chords for the sphere-uniform metric (`ChordSepStmt`)

A simple chord `η` (continuous on `[0,∞)`, `‖η t‖ → ∞`) becomes, through the stereographic map
`σ : ℂ → ℂ × ℝ` onto the unit sphere and the time change `t = s/(1−s)`, a continuous curve
`γ_η : [0,1] → ℂ × ℝ` with `γ_η(1) = (0,1)` (the north pole). The chordal distance is the
Euclidean distance of the stereographic images, hence `chordalDist z w ≤ 2 dist (σ z) (σ w)`
(sup norm on `ℂ × ℝ`). The space `C([0,1], ℂ × ℝ)` is second countable, so the curves `γ_η`
of simple chords have a countable dense subfamily: this is `ChordSepStmt`.

Own elementary argument (the standard proof that `C(K, Y)` is separable for compact `K`, applied
to the one-point compactification of the time axis; the identity for the chordal metric is the
classical formula for the stereographic projection).
-/

noncomputable section

open Filter Set Function Topology Metric unitInterval

namespace QuantumZipper
namespace Thm18Asm
namespace G1Chord

open CA.Kernel

/-- The stereographic map onto the unit sphere of `ℂ × ℝ ≅ ℝ³`. -/
def sig (z : ℂ) : ℂ × ℝ :=
  (((2 / (1 + ‖z‖ ^ 2) : ℝ) : ℂ) * z, (‖z‖ ^ 2 - 1) / (‖z‖ ^ 2 + 1))

theorem continuous_sig : Continuous sig := by
  unfold sig
  refine Continuous.prodMk ?_ ?_
  · refine Continuous.mul (Complex.continuous_ofReal.comp ?_) continuous_id
    exact Continuous.div continuous_const (by fun_prop) fun z => by positivity
  · exact Continuous.div (by fun_prop) (by fun_prop) fun z => by positivity

theorem chordalDist_sq (z w : ℂ) :
    chordalDist z w ^ 2 = ‖(sig z).1 - (sig w).1‖ ^ 2 + ((sig z).2 - (sig w).2) ^ 2 := by
  have ha : 0 < 1 + ‖z‖ ^ 2 := by positivity
  have hb : 0 < 1 + ‖w‖ ^ 2 := by positivity
  unfold chordalDist sig
  simp only
  rw [div_pow, mul_pow, mul_pow, Real.sq_sqrt ha.le, Real.sq_sqrt hb.le]
  rw [← Complex.normSq_eq_norm_sq, ← Complex.normSq_eq_norm_sq, ← Complex.normSq_eq_norm_sq,
    ← Complex.normSq_eq_norm_sq, Complex.normSq_apply, Complex.normSq_apply,
    Complex.normSq_apply, Complex.normSq_apply]
  simp only [Complex.sub_re, Complex.sub_im, Complex.mul_re, Complex.mul_im, Complex.ofReal_re,
    Complex.ofReal_im, zero_mul, sub_zero, add_zero]
  have ha1 : 1 + (z.re * z.re + z.im * z.im) ≠ 0 :=
    (show (0 : ℝ) < 1 + (z.re * z.re + z.im * z.im) by nlinarith [mul_self_nonneg z.re, mul_self_nonneg z.im]).ne'
  have hb1 : 1 + (w.re * w.re + w.im * w.im) ≠ 0 :=
    (show (0 : ℝ) < 1 + (w.re * w.re + w.im * w.im) by nlinarith [mul_self_nonneg w.re, mul_self_nonneg w.im]).ne'
  have ha2 : z.re * z.re + z.im * z.im + 1 ≠ 0 :=
    (show (0 : ℝ) < z.re * z.re + z.im * z.im + 1 by nlinarith [mul_self_nonneg z.re, mul_self_nonneg z.im]).ne'
  have hb2 : w.re * w.re + w.im * w.im + 1 ≠ 0 :=
    (show (0 : ℝ) < w.re * w.re + w.im * w.im + 1 by nlinarith [mul_self_nonneg w.re, mul_self_nonneg w.im]).ne'
  field_simp
  ring

theorem chordalDist_le_two_dist_sig (z w : ℂ) : chordalDist z w ≤ 2 * dist (sig z) (sig w) := by
  have h := chordalDist_sq z w
  have hd : dist (sig z) (sig w) = max (‖(sig z).1 - (sig w).1‖) (|(sig z).2 - (sig w).2|) := by
    rw [Prod.dist_eq, dist_eq_norm, Real.dist_eq]
  have h1 : ‖(sig z).1 - (sig w).1‖ ≤ dist (sig z) (sig w) := hd ▸ le_max_left _ _
  have h2 : |(sig z).2 - (sig w).2| ≤ dist (sig z) (sig w) := hd ▸ le_max_right _ _
  have hc0 : 0 ≤ chordalDist z w := by unfold chordalDist; positivity
  have hsq : chordalDist z w ^ 2 ≤ (2 * dist (sig z) (sig w)) ^ 2 := by
    rw [h]
    have e1 : ‖(sig z).1 - (sig w).1‖ ^ 2 ≤ dist (sig z) (sig w) ^ 2 :=
      pow_le_pow_left₀ (norm_nonneg _) h1 2
    have e2 : ((sig z).2 - (sig w).2) ^ 2 ≤ dist (sig z) (sig w) ^ 2 := by
      rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) h2 2
    nlinarith
  exact (pow_le_pow_iff_left₀ hc0 (by positivity) two_ne_zero).1 hsq

/-- The north pole is the limit of `σ` at infinity. -/
theorem tendsto_sig_cobounded : Tendsto sig (Bornology.cobounded ℂ) (𝓝 ((0 : ℂ), (1 : ℝ))) := by
  rw [Metric.tendsto_nhds]
  intro ε hε
  have hev : ∀ᶠ z in Bornology.cobounded ℂ, 4 / ε < ‖z‖ :=
    tendsto_norm_cobounded_atTop.eventually (eventually_gt_atTop _)
  filter_upwards [hev] with z hz
  have hz0 : 0 < ‖z‖ := lt_trans (by positivity) hz
  have hzε : 4 / ‖z‖ < ε := by rw [div_lt_iff₀ hz0]; rw [div_lt_iff₀ hε] at hz; linarith
  have hA : ‖((2 / (1 + ‖z‖ ^ 2) : ℝ) : ℂ) * z‖ ≤ 2 / ‖z‖ := by
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (by positivity),
      div_mul_eq_mul_div, div_le_div_iff₀ (by positivity) hz0]
    nlinarith
  have hB : |(‖z‖ ^ 2 - 1) / (‖z‖ ^ 2 + 1) - 1| ≤ 2 / ‖z‖ := by
    have e : (‖z‖ ^ 2 - 1) / (‖z‖ ^ 2 + 1) - 1 = -(2 / (‖z‖ ^ 2 + 1)) := by
      field_simp; ring
    rw [e, abs_neg, abs_of_nonneg (by positivity), div_le_div_iff₀ (by positivity) hz0]
    nlinarith
  rw [Prod.dist_eq, dist_eq_norm, Real.dist_eq, sub_zero]
  have h2 : 2 / ‖z‖ < ε :=
    lt_of_le_of_lt (div_le_div_of_nonneg_right (by norm_num) hz0.le) hzε
  exact max_lt (lt_of_le_of_lt hA h2) (lt_of_le_of_lt hB h2)

/-- The compactified curve of a chord. -/
def gam (η : ℝ → ℂ) (s : I) : ℂ × ℝ :=
  if (s : ℝ) < 1 then sig (η ((s : ℝ) / (1 - s))) else ((0 : ℂ), (1 : ℝ))

theorem continuous_gam {η : ℝ → ℂ} (hη : IsSimpleChord η) : Continuous (gam η) := by
  have hηc : Continuous fun t : ℝ => η (max t 0) :=
    hη.2.1.comp_continuous (continuous_id.max continuous_const) fun t => le_max_right t 0
  rw [continuous_iff_continuousAt]
  intro s
  by_cases hs : (s : ℝ) < 1
  · have hopen : {s : I | (s : ℝ) < 1} ∈ 𝓝 s :=
      (isOpen_lt continuous_subtype_val continuous_const).mem_nhds hs
    have he : gam η =ᶠ[𝓝 s] fun s : I => sig (η (max ((s : ℝ) / (1 - s)) 0)) := by
      filter_upwards [hopen] with u hu
      have hu' : (u : ℝ) < 1 := hu
      have h0 : 0 ≤ (u : ℝ) / (1 - u) := div_nonneg u.2.1 (by linarith)
      simp only [gam, if_pos hu', max_eq_left h0]
    refine ContinuousAt.congr ?_ he.symm
    have h1 : ContinuousAt (fun s : I => (s : ℝ) / (1 - s)) s :=
      (continuous_subtype_val.continuousAt).div
        (continuous_const.sub continuous_subtype_val).continuousAt (by linarith)
    exact continuous_sig.continuousAt.comp (hηc.continuousAt.comp h1)
  · have hs1 : (s : ℝ) = 1 := le_antisymm s.2.2 (not_lt.1 hs)
    have hgs : gam η s = ((0 : ℂ), (1 : ℝ)) := by simp only [gam, if_neg hs]
    rw [Metric.continuousAt_iff]
    intro ε hε
    have hcob : Tendsto η atTop (Bornology.cobounded ℂ) :=
      tendsto_norm_atTop_iff_cobounded.1 hη.2.2.2.2
    obtain ⟨T, hT⟩ := eventually_atTop.1
      ((tendsto_sig_cobounded.comp hcob).eventually (Metric.ball_mem_nhds _ hε))
    set T' : ℝ := max T 0 with hT'
    refine ⟨1 / (T' + 1), by positivity, fun u hu => ?_⟩
    rw [hgs]
    by_cases hu1 : (u : ℝ) < 1
    · simp only [gam, if_pos hu1]
      rw [Subtype.dist_eq, hs1, Real.dist_eq, abs_sub_comm, abs_of_pos (by linarith)] at hu
      have hpos : 0 < 1 - (u : ℝ) := by linarith
      have hge : T ≤ (u : ℝ) / (1 - u) := by
        have h1 : T' + 1 < 1 / (1 - (u : ℝ)) := by
          rw [lt_div_iff₀ hpos]
          rw [lt_div_iff₀ (by positivity)] at hu
          linarith
        have h2 : (u : ℝ) / (1 - u) = 1 / (1 - u) - 1 := by field_simp; ring
        rw [h2]
        linarith [le_max_left T 0]
      exact hT _ hge
    · simp only [gam, if_neg hu1, dist_self]
      exact hε

/-- The compactified curve of a simple chord, as a continuous map. -/
def gamC {η : ℝ → ℂ} (hη : IsSimpleChord η) : C(I, ℂ × ℝ) := ⟨gam η, continuous_gam hη⟩

theorem chordalDist_le_of_gam {η η' : ℝ → ℂ} (hη : IsSimpleChord η) (hη' : IsSimpleChord η')
    {t : ℝ} (ht : 0 ≤ t) : chordalDist (η t) (η' t) ≤ 2 * dist (gamC hη) (gamC hη') := by
  have h1t : (0 : ℝ) < 1 + t := by linarith
  set s : I := ⟨t / (1 + t), div_nonneg ht h1t.le, (div_le_one h1t).2 (by linarith)⟩ with hsdef
  have hs1 : (s : ℝ) < 1 := (div_lt_one h1t).2 (by linarith)
  have hst : (s : ℝ) / (1 - s) = t := by
    show t / (1 + t) / (1 - t / (1 + t)) = t
    field_simp
    ring
  have h1 : gamC hη s = sig (η t) := by
    show gam η s = _; simp only [gam, if_pos hs1, hst]
  have h2 : gamC hη' s = sig (η' t) := by
    show gam η' s = _; simp only [gam, if_pos hs1, hst]
  calc chordalDist (η t) (η' t) ≤ 2 * dist (sig (η t)) (sig (η' t)) :=
        chordalDist_le_two_dist_sig _ _
    _ = 2 * dist (gamC hη s) (gamC hη' s) := by rw [h1, h2]
    _ ≤ 2 * dist (gamC hη) (gamC hη') := by
        gcongr; exact ContinuousMap.dist_apply_le_dist s

/-- A simple chord: the imaginary half-axis. -/
theorem isSimpleChord_axis : IsSimpleChord fun t : ℝ => (t : ℂ) * Complex.I := by
  refine ⟨by simp, by fun_prop, fun a _ b _ h => ?_, fun t ht => ?_, ?_⟩
  · have := congrArg Complex.im h
    simpa using this
  · show 0 < ((t : ℂ) * Complex.I).im
    simpa using ht
  · have e : (fun t : ℝ => ‖(t : ℂ) * Complex.I‖) = fun t => |t| := by
      funext t; simp
    rw [e]
    exact tendsto_abs_atTop_atTop

/-- **(C1) holds**: simple chords are separable for the sphere-uniform metric. -/
theorem chordSepStmt : ChordSepStmt := by
  classical
  set S : Set C(I, ℂ × ℝ) := range fun η : {η : ℝ → ℂ // IsSimpleChord η} => gamC η.2 with hS
  obtain ⟨D, hDc, hDS, hDd⟩ := TopologicalSpace.exists_countable_dense_subset S
  set η₀ : {η : ℝ → ℂ // IsSimpleChord η} := ⟨_, isSimpleChord_axis⟩
  have hDne : D.Nonempty := by
    by_contra hne
    rw [Set.not_nonempty_iff_eq_empty] at hne
    have := hDd ⟨η₀, rfl⟩
    rw [hne, closure_empty] at this
    exact this
  obtain ⟨f, hf⟩ := hDc.exists_eq_range hDne
  have hfS : ∀ k, f k ∈ S := fun k => hDS (hf ▸ mem_range_self k)
  choose pick hpick using fun k => hfS k
  refine ⟨fun k => (pick k).1, fun k => (pick k).2, fun η hη ε hε => ?_⟩
  have hmem : gamC hη ∈ closure D := hDd ⟨⟨η, hη⟩, rfl⟩
  obtain ⟨d, hdD, hd⟩ := Metric.mem_closure_iff.1 hmem (ε / 2) (by positivity)
  rw [hf] at hdD
  obtain ⟨k, rfl⟩ := hdD
  refine ⟨k, fun t ht => ?_⟩
  have h := chordalDist_le_of_gam (pick k).2 hη ht
  have e : gamC (pick k).2 = f k := hpick k
  rw [e, dist_comm] at h
  linarith

end G1Chord
end Thm18Asm
end QuantumZipper
