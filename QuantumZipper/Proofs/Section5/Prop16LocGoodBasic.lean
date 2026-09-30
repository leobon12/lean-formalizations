import Mathlib.Probability.Kernel.Disintegration.StandardBorel
import Mathlib.Probability.Process.FiniteDimensionalLaws
import QuantumZipper.Proofs.Section5.Prop16Wire
import QuantumZipper.Proofs.GFF.K3.MixedRiesz
import QuantumZipper.Proofs.LQG.WedgeRestriction

/-!
# Proposition 1.6, node LOCGOOD (part 1): transfer tools

Tools for deriving `Prop16Asm.Prop16LocGoodStmt` from a coupling of the mixed field with a free
field living on another probability space (`Prop16LocGood.lean`):

* `locGood_ae_exists_of_map_eq`: if `F : Ω → (I → ℝ)` and `G : Ω₀ → (I → ℝ)` (`I` countable,
  `Ω₀` standard Borel) have the same law and `S ⊆ Ω₀` has full measure (not necessarily
  measurable), then for `P`-a.e. `ω` there is `ω₀ ∈ S` with `F ω = G ω₀`. Route: disintegrate
  the law of `(G, id)` over its first marginal (`Measure.condKernel`, mathlib) and apply
  Fubini for the composition-product to the measurable graph event. This replaces the
  "measurable projection" step: no image of a measurable set needs to be measurable.
* `locGood_map_eq_of_isMixedGFF`: two mixed GFFs (on possibly different spaces) have the same
  joint law along any family of admissible measures (finite-dimensional Gaussian laws are fixed
  by the covariance, `WedgeRes.map_eq_of_gaussian_vec`; projective-limit uniqueness).
* `locGood_exists_open`: `D ∪ (a,b)` is relatively open in `Hbar` (from `Prop16Geometry`).
* `locGood_isAdmissible_circle`: a folded circle whose closed half-disc lies in `D ∪ (a,b)` is
  admissible for the mixed space (`K3.isAdmissibleDual_foldedCircle_of_local`).
* `locCircSet`, `locCircSet_countable`: the dyadic folded circles read by `CircAgree`.

All arguments are own elementary ones (measure-theoretic plumbing; AGENT_GUIDE cost rule); the
disintegration theorem is mathlib's (`MeasureTheory.Measure.compProd_fst_condKernel`).
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Metric

namespace QuantumZipper

namespace Prop16Asm

/-- **Transfer along equal laws.** -/
theorem locGood_ae_exists_of_map_eq {Ω Ω₀ I : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω₀]
    [StandardBorelSpace Ω₀] [Countable I] {P : Measure Ω} {P₀ : Measure Ω₀}
    [IsProbabilityMeasure P₀] {F : Ω → I → ℝ} {G : Ω₀ → I → ℝ}
    (hF : AEMeasurable F P) (hG : Measurable G) (hlaw : P.map F = P₀.map G)
    {S : Set Ω₀} (hS : ∀ᵐ ω₀ ∂P₀, ω₀ ∈ S) :
    ∀ᵐ ω ∂P, ∃ ω₀ ∈ S, F ω = G ω₀ := by
  have hne : Nonempty Ω₀ := by
    by_contra h
    rw [not_nonempty_iff] at h
    have h1 := measure_univ (μ := P₀)
    rw [Set.univ_eq_empty_iff.2 h, measure_empty] at h1
    exact zero_ne_one h1
  set N := toMeasurable P₀ Sᶜ with hNdef
  have hN0 : P₀ N = 0 := by rw [hNdef, measure_toMeasurable]; exact ae_iff.1 hS
  let g : Ω₀ → (I → ℝ) × Ω₀ := fun ω₀ => (G ω₀, ω₀)
  have hg : Measurable g := hG.prodMk measurable_id
  set E : Set ((I → ℝ) × Ω₀) := (⋂ i, {q | q.1 i = G q.2 i}) ∩ {q | q.2 ∈ Nᶜ} with hEdef
  have hE : MeasurableSet E := by
    refine MeasurableSet.inter (MeasurableSet.iInter fun i => ?_) ?_
    · exact measurableSet_eq_fun ((measurable_pi_apply i).comp measurable_fst)
        ((measurable_pi_apply i).comp (hG.comp measurable_snd))
    · exact (measurableSet_toMeasurable _ _).compl.preimage measurable_snd
  set ρ : Measure ((I → ℝ) × Ω₀) := P₀.map g with hρdef
  have : IsProbabilityMeasure ρ := (Measure.isProbabilityMeasure_map_iff hg.aemeasurable).2 inferInstance
  have hρE : ∀ᵐ q ∂ρ, q ∈ E := by
    rw [hρdef]
    refine (ae_map_iff hg.aemeasurable hE).2 ?_
    have hN' : ∀ᵐ ω₀ ∂P₀, ω₀ ∉ N := measure_eq_zero_iff_ae_notMem.1 hN0
    filter_upwards [hN'] with ω₀ hω₀
    exact ⟨mem_iInter.2 fun i => rfl, hω₀⟩
  have hfst : ρ.fst = P₀.map G := by
    rw [hρdef, Measure.fst, Measure.map_map measurable_fst hg]; rfl
  rw [← ρ.disintegrate ρ.condKernel] at hρE
  have h2 := Measure.ae_ae_of_ae_compProd hρE
  rw [hfst, ← hlaw] at h2
  filter_upwards [ae_of_ae_map hF h2] with ω hω
  obtain ⟨ω₀, h1, h3⟩ := hω.exists
  refine ⟨ω₀, ?_, funext fun i => mem_iInter.1 h1 i⟩
  by_contra hS'
  exact h3 (subset_toMeasurable _ _ hS')

/-- **Two mixed GFFs have the same law along any admissible family.** -/
theorem locGood_map_eq_of_isMixedGFF {Ω Ω₀ I : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω₀]
    {P : Measure Ω} {P₀ : Measure Ω₀} [IsProbabilityMeasure P] [IsProbabilityMeasure P₀]
    {D S : Set ℂ} {X : Ω → FieldSample} {Y : Ω₀ → FieldSample}
    (hX : IsMixedGFF D S X P) (hY : IsMixedGFF D S Y P₀) (m : I → Measure ℂ)
    (hm : ∀ i, IsAdmissibleDual D (mixedSpace D S) (m i)) :
    P.map (fun ω i => X ω (m i)) = P₀.map (fun ω i => Y ω (m i)) := by
  let f : I → {μ // IsAdmissibleDual D (mixedSpace D S) μ} := fun i => ⟨m i, hm i⟩
  have hGX := hX.gaussian.comp_right f
  have hGY := hY.gaussian.comp_right f
  have hmX : Measurable fun ω i => X ω (m i) :=
    measurable_pi_iff.2 fun i => hX.measurable_coord _
  have hmY : Measurable fun ω i => Y ω (m i) :=
    measurable_pi_iff.2 fun i => hY.measurable_coord _
  have hfdd : ∀ J : Finset I, P.map (fun ω => J.restrict (fun i => X ω (m i))) =
      P₀.map (fun ω => J.restrict (fun i => Y ω (m i))) := by
    intro J
    exact WedgeRes.map_eq_of_gaussian_vec (U := fun (i : J) ω => X ω (m i))
      (V := fun (i : J) ω => Y ω (m i))
      (hGX.hasGaussianLaw J) (hGY.hasGaussianLaw J) (fun i => hX.measurable_coord _)
      (fun i => hY.measurable_coord _) (fun i => (hGX.hasGaussianLaw_eval (i : I)).memLp_two)
      (fun i => (hGY.hasGaussianLaw_eval (i : I)).memLp_two) (fun i => hX.centered _ (hm i))
      (fun i => hY.centered _ (hm i))
      (fun i j => by rw [hX.covariance_eq _ _ (hm i) (hm j), hY.covariance_eq _ _ (hm i) (hm j)])
  have h1 := isProjectiveLimit_map (X := fun i ω => X ω (m i)) (P := P) hmX.aemeasurable
  have h2 := isProjectiveLimit_map (X := fun i ω => Y ω (m i)) (P := P₀) hmY.aemeasurable
  have h1' : IsProjectiveLimit (P.map (fun ω i => X ω (m i)))
      (fun J : Finset I => P₀.map (fun ω => J.restrict (fun i => Y ω (m i)))) := by
    intro J
    have h := h1 J
    simp only at h ⊢
    rw [h, hfdd J]
  exact h1'.unique h2

/-- A closed half-disc inside an open set can be enlarged a little. -/
theorem locGood_exists_radius {W : Set ℂ} (hW : IsOpen W) {z : ℂ} {r : ℝ}
    (h : closedBall z r ∩ Hbar ⊆ W) : ∃ R, r < R ∧ closedBall z R ∩ Hbar ⊆ W := by
  set C := (closedBall z (r + 1) ∩ Hbar) \ W with hCdef
  have hC : IsCompact C := (Prop16Area.G.isCompact_closedBall_inter_Hbar z (r + 1)).diff hW
  rcases C.eq_empty_or_nonempty with hCe | hCn
  · refine ⟨r + 1, by linarith, fun w hw => ?_⟩
    by_contra hwW
    have hwC : w ∈ C := ⟨hw, hwW⟩
    rw [hCe] at hwC; exact hwC
  · obtain ⟨w₀, hw₀, hmin⟩ :=
      hC.exists_isMinOn hCn (continuous_id.dist continuous_const).continuousOn
    have hr0 : r < dist w₀ z := by
      by_contra hle; push Not at hle
      exact hw₀.2 (h ⟨hle, hw₀.1.2⟩)
    have hw0le : dist w₀ z ≤ r + 1 := hw₀.1.1
    refine ⟨(r + dist w₀ z) / 2, by linarith, fun w hw => ?_⟩
    by_contra hwW
    have hw1 : dist w z ≤ (r + dist w₀ z) / 2 := hw.1
    have hwC : w ∈ C := ⟨⟨show dist w z ≤ r + 1 by linarith, hw.2⟩, hwW⟩
    have hle := isMinOn_iff.1 hmin w hwC
    simp only [id] at hle
    linarith

/-- `D ∪ (a,b)` is relatively open in `Hbar`. -/
theorem locGood_exists_open {D : Set ℂ} {c d a b : ℝ} (hgeo : K3.Prop16Geometry D c d)
    (hca : c ≤ a) (hbd : b ≤ d) :
    ∃ W : Set ℂ, IsOpen W ∧ W ∩ Hbar = D ∪ realSet (Ioo a b) := by
  obtain ⟨hD, -, -, hDH, -, -, hloc⟩ := hgeo
  choose! ρ hρ hρD using hloc
  set W := D ∪ ⋃ t ∈ Ioo a b, ball (t : ℂ) (min (ρ t) (min (t - a) (b - t))) with hWdef
  refine ⟨W, hD.union (isOpen_biUnion fun _ _ => isOpen_ball), ?_⟩
  ext w
  constructor
  · rintro ⟨hw | hw, hwH⟩
    · exact Or.inl hw
    · obtain ⟨t, ht, hwt⟩ := mem_iUnion₂.1 hw
      have htcd : t ∈ Ioo c d := ⟨lt_of_le_of_lt hca ht.1, lt_of_lt_of_le ht.2 hbd⟩
      rw [mem_ball, dist_eq_norm] at hwt
      by_cases him : w.im = 0
      · right
        have hre : |w.re - t| < min (t - a) (b - t) := by
          have h1 : |(w - (t : ℂ)).re| ≤ ‖w - (t : ℂ)‖ := Complex.abs_re_le_norm _
          simp only [Complex.sub_re, Complex.ofReal_re] at h1
          exact lt_of_le_of_lt h1 (lt_of_lt_of_le hwt (min_le_right _ _))
        obtain ⟨hlo, hhi⟩ := abs_lt.1 hre
        have hm1 := min_le_left (t - a) (b - t)
        have hm2 := min_le_right (t - a) (b - t)
        refine ⟨w.re, ⟨by linarith, by linarith⟩, ?_⟩
        exact Complex.ext (by simp) (by simp [him])
      · left
        have hwH' : w ∈ H := lt_of_le_of_ne hwH (Ne.symm him)
        refine hρD t htcd ⟨?_, hwH'⟩
        rw [mem_ball, dist_eq_norm]
        exact lt_of_lt_of_le hwt (min_le_left _ _)
  · rintro (hw | ⟨t, ht, rfl⟩)
    · exact ⟨Or.inl hw, show (0 : ℝ) ≤ w.im from le_of_lt (hDH hw)⟩
    · refine ⟨Or.inr (mem_iUnion₂.2 ⟨t, ht, ?_⟩), by simp [Hbar]⟩
      have htcd : t ∈ Ioo c d := ⟨lt_of_le_of_lt hca ht.1, lt_of_lt_of_le ht.2 hbd⟩
      rw [mem_ball, dist_self]
      exact lt_min (hρ t htcd) (lt_min (by linarith [ht.1]) (by linarith [ht.2]))

/-- A folded circle whose closed half-disc lies in `D ∪ (a,b)` is mixed-admissible. -/
theorem locGood_isAdmissible_circle {D : Set ℂ} {c d a b : ℝ} (hgeo : K3.Prop16Geometry D c d)
    (hca : c ≤ a) (hbd : b ≤ d) {W : Set ℂ} (hWo : IsOpen W)
    (hWV : W ∩ Hbar = D ∪ realSet (Ioo a b)) {z : ℂ} (hz : z ∈ Hbar) {r : ℝ} (hr : 0 < r)
    (hsub : closedBall z r ∩ Hbar ⊆ W) :
    IsAdmissibleDual D (mixedSpace D (realSet (Icc c d))) (foldedCircle z r) := by
  obtain ⟨hD, -, hb, hDH, -, hfr, -⟩ := hgeo
  obtain ⟨R, hrR, hR⟩ := locGood_exists_radius hWo hsub
  have hV : ∀ w, w ∈ closedBall z R ∩ Hbar → w ∈ D ∪ realSet (Ioo a b) := fun w hw => by
    rw [← hWV]; exact ⟨hR hw, hw.2⟩
  have hab_cd : realSet (Ioo a b) ⊆ realSet (Icc c d) := image_mono fun t ht =>
    ⟨hca.trans ht.1.le, ht.2.le.trans hbd⟩
  have hclH : closure D ⊆ Hbar :=
    closure_minimal (fun w hw => show (0 : ℝ) ≤ w.im from le_of_lt (hDH hw)) isClosed_Hbar
  refine K3.isAdmissibleDual_foldedCircle_of_local hD hDH hb ?_
    ⟨hz, hr.trans hrR, hDH, ?_, ?_⟩ hr hrR
  · rintro _ ⟨t, -, rfl⟩; simp
  · intro w hw
    rcases hV w hw with h | h
    · exact subset_closure h
    · rw [← hfr] at hab_cd
      exact frontier_subset_closure (hab_cd h).1
  · rintro w ⟨hwB, hwF⟩
    have hwcl : w ∈ closure D := frontier_subset_closure hwF
    rcases hV w ⟨hwB, hclH hwcl⟩ with h | h
    · rw [hD.frontier_eq] at hwF; exact absurd h hwF.2
    · exact hab_cd h

/-- The dyadic folded circles whose closed half-disc lies in `V` (those read by `CircAgree V`). -/
def locCircSet (V : Set ℂ) : Set (Measure ℂ) :=
  {m | ∃ (n k : ℕ) (z : ℂ), z ∈ Hbar ∧ closedBall (dyadicRoundC n z) (radius k) ∩ Hbar ⊆ V ∧
    m = foldedCircle (dyadicRoundC n z) (radius k)}

theorem locCircSet_countable (V : Set ℂ) : (locCircSet V).Countable := by
  refine (Set.countable_range (fun p : ℕ × ℕ × ℤ × ℤ =>
    foldedCircle (⟨(p.2.2.1 : ℝ) / 2 ^ p.1, (p.2.2.2 : ℝ) / 2 ^ p.1⟩ : ℂ) (radius p.2.1))).mono ?_
  rintro _ ⟨n, k, z, -, -, rfl⟩
  exact ⟨(n, k, ⌊(2 : ℝ) ^ n * z.re⌋, ⌊(2 : ℝ) ^ n * z.im⌋), rfl⟩

end Prop16Asm

end QuantumZipper
