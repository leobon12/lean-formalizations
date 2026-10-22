import HigherDimLQGContinuity.Core.Interfaces
import HigherDimLQGContinuity.Sewing.Lemma31a
import HigherDimLQGMetric.Metric.Internal
import Mathlib.Topology.Connected.LocallyConnected
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

/-!
# Lemma 3.1(b): contraction of the excess
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace HigherDimLQGContinuity

open Set Metric MeasureTheory
open HigherDimLFPP (Rd)
open HigherDimLQGMetric (ContMetric)
open scoped ENNReal

/-- Extend a path on `[0,ℓ]` continuously by clamping its parameter. -/
private def sewClamp (ℓ u : ℝ) : ℝ := min (max u 0) ℓ

private theorem sewClamp_mem {ℓ : ℝ} (hℓ : 0 ≤ ℓ) (u : ℝ) :
    sewClamp ℓ u ∈ Icc 0 ℓ := by
  constructor
  · exact le_min (le_max_right _ _) hℓ
  · exact min_le_right _ _

private theorem sewClamp_eq {ℓ u : ℝ} (hu : u ∈ Icc (0 : ℝ) ℓ) :
    sewClamp ℓ u = u := by
  simp [sewClamp, hu.1, hu.2]

private theorem sewClamp_continuous (ℓ : ℝ) : Continuous (sewClamp ℓ) := by
  unfold sewClamp
  fun_prop

private theorem sewPath_continuous {d : ℕ} (P : ℝ → Rd d) {ℓ : ℝ}
    (hℓ : 0 ≤ ℓ) (hP : ContinuousOn P (Icc 0 ℓ)) :
    Continuous (P ∘ sewClamp ℓ) := by
  exact hP.comp_continuous (sewClamp_continuous ℓ) (sewClamp_mem hℓ)

/-- The component of an open preimage of a ball is an ambient open interval.
Its restriction to `[s,t]` is in the endpoint form used by `interval_cover`. -/
private theorem sew_component_representation {d : ℕ} (P : ℝ → Rd d)
    {s t : ℝ} {u : ℝ} (hu : u ∈ Icc s t)
    (z : Rd d) (r : ℝ) (hP : Continuous P) (hball : P u ∈ ball z r) :
    ∃ (V : Set ℝ) (a b : ℝ), IsOpen V ∧ u ∈ V ∧
      V = connectedComponentIn (P ⁻¹' ball z r) u ∧
      V ∩ Icc s t = Ioo a b ∩ Icc s t := by
  let U := P ⁻¹' ball z r
  let V := connectedComponentIn U u
  have hU : IsOpen U := isOpen_ball.preimage hP
  have huU : u ∈ U := hball
  have hV : IsOpen V := hU.connectedComponentIn
  have huV : u ∈ V := mem_connectedComponentIn huU
  have hconn : IsPreconnected (V ∩ Icc s t) :=
    (isPreconnected_connectedComponentIn.ordConnected.inter ordConnected_Icc).isPreconnected
  obtain ⟨a, b, hab⟩ := sew_relative_interval_representation s t (V ∩ Icc s t) V
    ⟨u, huV, hu⟩ hconn hV rfl
  exact ⟨V, a, b, hV, huV, rfl, hab⟩

/-- An excluded endpoint of a component of the preimage of an open ball maps to
the boundary sphere. This remains true when the endpoint is `s` or `t`. -/
private theorem sew_component_boundary {d : ℕ} (P : ℝ → Rd d)
    (hP : Continuous P) (z : Rd d) (r : ℝ) {u x : ℝ}
    (hu : P u ∈ ball z r)
    (hx : x ∈ closure (connectedComponentIn (P ⁻¹' ball z r) u))
    (hxnot : x ∉ connectedComponentIn (P ⁻¹' ball z r) u) :
    P x ∈ sphere z r := by
  let U : Set ℝ := P ⁻¹' ball z r
  let V : Set ℝ := connectedComponentIn U u
  have huU : u ∈ U := hu
  have hVU : V ⊆ U := connectedComponentIn_subset U u
  have hclosed : (P ⁻¹' closedBall z r)ᶜ ⊆ (closure V)ᶜ := by
    have hcl : closure V ⊆ P ⁻¹' closedBall z r :=
      closure_minimal (fun y hy => (mem_closedBall.mpr
        (le_of_lt (mem_ball.mp (hVU hy)))))
        (isClosed_closedBall.preimage hP)
    exact compl_subset_compl.mpr hcl
  have hxclosed : P x ∈ closedBall z r := by
    by_contra h
    exact (hclosed h) hx
  have hxU : x ∉ U := by
    intro hxU
    have hcomp : (⟨x, hxU⟩ : U) ∈
        connectedComponent (⟨u, huU⟩ : U) := by
      apply isClosed_connectedComponent.closure_subset
      rw [closure_subtype, ← connectedComponentIn_eq_image huU]
      exact hx
    exact hxnot (by
      rw [connectedComponentIn_eq_image huU]
      exact ⟨⟨x, hxU⟩, hcomp, rfl⟩)
  rw [mem_sphere]
  exact le_antisymm (mem_closedBall.mp hxclosed) (le_of_not_gt hxU)

private theorem sew_geodesic_continuous {d : ℕ} (R : ContMetric d)
    (P : ℝ → Rd d) {ℓ : ℝ}
    (hgeo : ∀ s ∈ Icc (0 : ℝ) ℓ, ∀ t ∈ Icc (0 : ℝ) ℓ,
      R.1 (P s, P t) = |s - t|) :
    ContinuousOn P (Icc 0 ℓ) := by
  apply R.continuousOn_pt_comp_iff.mp
  apply Metric.continuousOn_iff.mpr
  intro u hu ε hε
  refine ⟨ε, hε, ?_⟩
  intro v hv hvu
  change dist (R.pt (P v)) (R.pt (P u)) < ε
  rw [R.dist_pt, hgeo v hv u hu]
  simpa [Real.dist_eq] using hvu

/-- Compactness reduces the ball-component cover of a geodesic subsegment to
a finite family of represented relative intervals. -/
private theorem sew_finite_component_cover {d : ℕ} (R : ContMetric d)
    (F : Finset (SewBall d)) (P : ℝ → Rd d) {ℓ s t : ℝ}
    (hℓ : 0 ≤ ℓ) (hs : s ∈ Icc (0 : ℝ) ℓ) (ht : t ∈ Icc (0 : ℝ) ℓ)
    (hgeo : ∀ u ∈ Icc (0 : ℝ) ℓ, ∀ v ∈ Icc (0 : ℝ) ℓ,
      R.1 (P u, P v) = |u - v|)
    (hcov : ∀ u ∈ Icc (0 : ℝ) ℓ,
      ∃ B ∈ F, ‖P u - B.1‖ < B.2 / 10) :
    ∃ (G : Finset (Icc s t)) (B : Icc s t → SewBall d)
      (a b : Icc s t → ℝ),
      Icc s t ⊆ ⋃ i ∈ G, sewInterval s t a b i ∧
      (∀ i ∈ G, B i ∈ F ∧ i.1 ∈ sewInterval s t a b i ∧
        ‖P i.1 - (B i).1‖ < (B i).2 / 10) ∧
      (∀ i ∈ G, ∀ x ∈ sewInterval s t a b i,
        P x ∈ ball (B i).1 (B i).2) ∧
      (∀ i ∈ G, ∀ x ∈ Icc s t,
        x ∈ closure (sewInterval s t a b i) →
        x ∉ sewInterval s t a b i → P x ∈ sphere (B i).1 (B i).2) := by
  classical
  let T : Set ℝ := Icc s t
  have hT : T ⊆ Icc (0 : ℝ) ℓ := Icc_subset_Icc hs.1 ht.2
  let P₀ : ℝ → Rd d := P ∘ sewClamp ℓ
  have hP₀ : Continuous P₀ := sewPath_continuous P hℓ
    (sew_geodesic_continuous R P hgeo)
  have hP₀eq : ∀ x ∈ T, P₀ x = P x := by
    intro x hx
    simp only [P₀, Function.comp_def, sewClamp_eq (hT hx)]
  have hball : ∀ i : T, ∃ B : SewBall d,
      B ∈ F ∧ ‖P i.1 - B.1‖ < B.2 / 10 := by
    intro i
    exact hcov i.1 (hT i.2)
  choose B hBF hcore using hball
  have hcoreball : ∀ i : T, P₀ i.1 ∈ ball (B i).1 (B i).2 := by
    intro i
    rw [hP₀eq i.1 i.2, mem_ball, dist_eq_norm]
    have hr : 0 < (B i).2 := by
      have := norm_nonneg (P i.1 - (B i).1)
      linarith [hcore i]
    linarith [hcore i]
  have hrep : ∀ i : T, ∃ (V : Set ℝ) (a b : ℝ),
      IsOpen V ∧ i.1 ∈ V ∧
      V = connectedComponentIn (P₀ ⁻¹' ball (B i).1 (B i).2) i.1 ∧
      V ∩ T = Ioo a b ∩ T := by
    intro i
    exact sew_component_representation P₀ i.2 (B i).1 (B i).2 hP₀ (hcoreball i)
  choose V a b hV hiV hVeq hJ using hrep
  obtain ⟨G, hG⟩ := isCompact_Icc.elim_finite_subcover V hV (by
    intro x hx
    exact mem_iUnion.mpr ⟨⟨x, hx⟩, hiV ⟨x, hx⟩⟩)
  refine ⟨G, B, a, b, ?_, ?_, ?_, ?_⟩
  · intro x hx
    obtain ⟨i, hiG, hxi⟩ := mem_iUnion₂.mp (hG hx)
    exact mem_iUnion₂.mpr ⟨i, hiG, by rw [sewInterval, ← hJ i]; exact ⟨hxi, hx⟩⟩
  · intro i hiG
    refine ⟨hBF i, ?_, hcore i⟩
    rw [sewInterval, ← hJ i]
    exact ⟨hiV i, i.2⟩
  · intro i hiG x hx
    have hxV : x ∈ V i := by
      rw [sewInterval, ← hJ i] at hx
      exact hx.1
    have hxU := connectedComponentIn_subset
      (P₀ ⁻¹' ball (B i).1 (B i).2) i.1 (hVeq i ▸ hxV)
    change P₀ x ∈ ball (B i).1 (B i).2 at hxU
    rwa [hP₀eq x hx.2] at hxU
  · intro i hiG x hxT hxcl hxnot
    have hxclV : x ∈ closure (V i) := by
      apply closure_mono (by
        intro y hy
        change y ∈ Ioo (a i) (b i) ∩ T at hy
        rw [← hJ i] at hy
        exact hy.1)
      exact hxcl
    have hxnotV : x ∉ V i := by
      intro hxV
      apply hxnot
      rw [sewInterval, ← hJ i]
      exact ⟨hxV, hxT⟩
    have hsp := sew_component_boundary P₀ hP₀ (B i).1 (B i).2
      (hcoreball i) (hVeq i ▸ hxclV) (hVeq i ▸ hxnotV)
    rwa [hP₀eq x hxT] at hsp

/-- The first time a continuous radial coordinate, initially equal to `r`, enters
the three-quarter ball. All earlier times stay in the closed annulus. -/
private theorem sew_first_inner_crossing (f : ℝ → ℝ) (hf : Continuous f)
    {a c b r : ℝ} (hac : a < c) (hcb : c < b) (hr : 0 < r)
    (ha : f a = r) (hc : f c < r / 2)
    (houter : ∀ u ∈ Ioo a b, f u < r) :
    ∃ σ : ℝ, a < σ ∧ σ ≤ c ∧ f σ = 3 * r / 4 ∧
      ∀ u ∈ Icc a σ, 3 * r / 4 ≤ f u ∧ f u ≤ r := by
  let K : Set ℝ := Icc a c ∩ f ⁻¹' Iic (3 * r / 4)
  have hKclosed : IsClosed K := isClosed_Icc.inter (isClosed_Iic.preimage hf)
  have hcK : c ∈ K := by
    refine ⟨right_mem_Icc.mpr hac.le, ?_⟩
    change f c ≤ 3 * r / 4
    linarith
  have hKbelow : BddBelow K := ⟨a, fun u hu => hu.1.1⟩
  let σ := sInf K
  have hσK : σ ∈ K := hKclosed.csInf_mem ⟨c, hcK⟩ hKbelow
  have haσ : a ≤ σ := hσK.1.1
  have hσc : σ ≤ c := hσK.1.2
  have hσrad : f σ ≤ 3 * r / 4 := hσK.2
  have haσstrict : a < σ := by
    rcases haσ.eq_or_lt with heq | hlt
    · rw [← heq, ha] at hσrad
      linarith
    · exact hlt
  have hσeq : f σ = 3 * r / 4 := by
    apply le_antisymm hσrad
    by_contra h
    have hlt : f σ < 3 * r / 4 := lt_of_not_ge h
    have hupper : 3 * r / 4 ≤ f a := by rw [ha]; linarith
    have hlower : f σ ≤ 3 * r / 4 := hσrad
    obtain ⟨u, hu, hfu⟩ := intermediate_value_Icc' haσ hf.continuousOn
      ⟨hlower, hupper⟩
    have huσ : u < σ := by
      have hne : u ≠ σ := by
        intro heq
        rw [heq] at hfu
        linarith
      exact lt_of_le_of_ne hu.2 hne
    have huK : u ∈ K := ⟨⟨hu.1, hu.2.trans hσc⟩, hfu.le⟩
    exact (not_lt_of_ge (csInf_le hKbelow huK)) huσ
  refine ⟨σ, haσstrict, hσc, hσeq, ?_⟩
  intro u hu
  have hlow : 3 * r / 4 ≤ f u := by
    by_contra h
    have hlt : f u < 3 * r / 4 := lt_of_not_ge h
    have huK : u ∈ K := ⟨⟨hu.1, hu.2.trans hσc⟩, hlt.le⟩
    have hσu : σ ≤ u := csInf_le hKbelow huK
    have hueq : u = σ := le_antisymm hu.2 hσu
    rw [hueq, hσeq] at hlt
    exact (lt_irrefl _) hlt
  have hupp : f u ≤ r := by
    rcases eq_or_lt_of_le hu.1 with heq | hlt
    · subst u
      exact ha.le
    · exact (houter u ⟨hlt, lt_of_le_of_lt hu.2 (hσc.trans_lt hcb)⟩).le
  exact ⟨hlow, hupp⟩

/-- For a length metric, a global set-distance lower bound applies to the
metric distance between any chosen points of the two sets. -/
private theorem sew_setDist_le_dist {d : ℕ} (R : ContMetric d)
    (hR : R.IsLength) {A B : Set (Rd d)} {x y : Rd d}
    (hx : x ∈ A) (hy : y ∈ B) :
    HigherDimLQGMetric.setDistIn R univ A B ≤ ENNReal.ofReal (R.1 (x, y)) := by
  calc
    HigherDimLQGMetric.setDistIn R univ A B
        ≤ R.internal univ x y := by
          unfold HigherDimLQGMetric.setDistIn
          exact iInf_le_of_le x (iInf_le_of_le hx
            (iInf_le_of_le y (iInf_le_of_le hy le_rfl)))
    _ = ENNReal.ofReal (R.1 (x, y)) := R.internal_univ_of_isLength hR x y

private theorem sew_diameter_time {d : ℕ} (R : ContMetric d)
    (P : ℝ → Rd d) {a b : ℝ} (hab : a ≤ b)
    (hgeo : R.1 (P a, P b) = |a - b|)
    (z : Rd d) (r M SR : ℝ) (hM : 0 ≤ M) (hSR : 0 ≤ SR)
    (ha : P a ∈ sphere z r) (hb : P b ∈ sphere z r)
    (hdiam : HigherDimLQGMetric.diamIn R
      (HigherDimLQGMetric.ann z (r / 2) (7 * r / 2))
      (sphere z r) ≤ ENNReal.ofReal (M * SR)) :
    b - a ≤ M * SR := by
  have hdist : ENNReal.ofReal (R.1 (P a, P b)) ≤ ENNReal.ofReal (M * SR) := by
    calc
      ENNReal.ofReal (R.1 (P a, P b))
          ≤ R.internal (HigherDimLQGMetric.ann z (r / 2) (7 * r / 2)) (P a) (P b) :=
        R.ofReal_le_internal _ _ _
      _ ≤ HigherDimLQGMetric.diamIn R
          (HigherDimLQGMetric.ann z (r / 2) (7 * r / 2)) (sphere z r) := by
        unfold HigherDimLQGMetric.diamIn
        exact le_iSup_of_le (P a) (le_iSup_of_le ha
          (le_iSup_of_le (P b) (le_iSup_of_le hb le_rfl)))
      _ ≤ ENNReal.ofReal (M * SR) := hdiam
  rw [hgeo, abs_of_nonpos (sub_nonpos.mpr hab)] at hdist
  simp only [neg_sub] at hdist
  exact (ENNReal.ofReal_le_ofReal_iff (mul_nonneg hM hSR)).mp hdist

/-- One interior component provides a thin annular block. The block occupies
at least `m/M` of the component's time span and has a uniform minimum length. -/
private theorem sew_interior_block {d : ℕ} (R : ContMetric d)
    (hR : R.IsLength) (P : ℝ → Rd d) {ℓ W a c b : ℝ}
    (hP : ContinuousOn P (Icc 0 ℓ))
    (haI : a ∈ Icc (0 : ℝ) ℓ) (hcI : c ∈ Icc (0 : ℝ) ℓ)
    (hbI : b ∈ Icc (0 : ℝ) ℓ)
    (hac : a < c) (hcb : c < b)
    (hgeo : ∀ u ∈ Icc (0 : ℝ) ℓ, ∀ v ∈ Icc (0 : ℝ) ℓ,
      R.1 (P u, P v) = |u - v|)
    (hW : ∀ u ∈ Icc (0 : ℝ) ℓ, ‖P u‖ ≤ W)
    (H β rm r m M SR : ℝ)
    (hH : 1 ≤ H) (hβ : 0 < β) (hrm : 0 < rm) (hrmr : rm ≤ r)
    (hr : r ≤ 1 / 4) (hM : 0 < M) (hSR : 0 < SR)
    (z : Rd d)
    (haSphere : P a ∈ sphere z r) (hbSphere : P b ∈ sphere z r)
    (hinside : ∀ u ∈ Ioo a b, P u ∈ ball z r)
    (hcore : ‖P c - z‖ < r / 10)
    (hmod : ∀ x ∈ closedBall (0 : Rd d) (W + 1),
      ∀ y ∈ closedBall (0 : Rd d) (W + 1), ‖x - y‖ ≤ 1 / 2 →
        H⁻¹ * ‖x - y‖ ^ β ≤ R.1 (x, y))
    (hcross : ENNReal.ofReal (m * SR) ≤
      HigherDimLQGMetric.setDistIn R univ (sphere z (3 * r / 4)) (sphere z r))
    (hdiam : HigherDimLQGMetric.diamIn R
      (HigherDimLQGMetric.ann z (r / 2) (7 * r / 2))
      (sphere z r) ≤ ENNReal.ofReal (M * SR)) :
    ∃ σ : ℝ, a < σ ∧ σ ≤ c ∧
      P '' Icc a σ ⊆ HigherDimLQGMetric.annCl z (3 * r / 4) r ∧
      ‖P a - z‖ = r ∧ ‖P σ - z‖ = 3 * r / 4 ∧
      m * SR ≤ σ - a ∧ H⁻¹ * (rm / 4) ^ β ≤ σ - a ∧
      b - a ≤ M * SR := by
  let P₀ : ℝ → Rd d := P ∘ sewClamp ℓ
  have hℓ : 0 ≤ ℓ := haI.1.trans haI.2
  have hP₀ : Continuous P₀ := sewPath_continuous P hℓ hP
  have hP₀eq : ∀ u ∈ Icc (0 : ℝ) ℓ, P₀ u = P u := by
    intro u hu
    simp only [P₀, Function.comp_def, sewClamp_eq hu]
  let f : ℝ → ℝ := fun u => ‖P₀ u - z‖
  have hf : Continuous f := (hP₀.sub continuous_const).norm
  have hfa : f a = r := by
    change ‖P₀ a - z‖ = r
    rw [hP₀eq a haI]
    simpa [mem_sphere, dist_eq_norm] using haSphere
  have hfc : f c < r / 2 := by
    change ‖P₀ c - z‖ < r / 2
    rw [hP₀eq c hcI]
    linarith
  have houter : ∀ u ∈ Ioo a b, f u < r := by
    intro u hu
    have huI : u ∈ Icc (0 : ℝ) ℓ := ⟨haI.1.trans hu.1.le, hu.2.le.trans hbI.2⟩
    change ‖P₀ u - z‖ < r
    rw [hP₀eq u huI]
    simpa [mem_ball, dist_eq_norm] using hinside u hu
  obtain ⟨σ, haσ, hσc, hσrad, hann⟩ :=
    sew_first_inner_crossing f hf hac hcb (lt_of_lt_of_le hrm hrmr)
      hfa hfc houter
  have hσI : σ ∈ Icc (0 : ℝ) ℓ :=
    ⟨haI.1.trans haσ.le, hσc.trans hcI.2⟩
  have haNorm : ‖P a - z‖ = r := by
    simpa [mem_sphere, dist_eq_norm] using haSphere
  have hσNorm : ‖P σ - z‖ = 3 * r / 4 := by
    simpa only [f, hP₀eq σ hσI] using hσrad
  have hblockAnn : P '' Icc a σ ⊆ HigherDimLQGMetric.annCl z (3 * r / 4) r := by
    intro x hx
    obtain ⟨u, hu, rfl⟩ := hx
    have huI : u ∈ Icc (0 : ℝ) ℓ :=
      ⟨haI.1.trans hu.1, hu.2.trans hσI.2⟩
    have h := hann u hu
    change 3 * r / 4 ≤ ‖P₀ u - z‖ ∧ ‖P₀ u - z‖ ≤ r at h
    rw [hP₀eq u huI] at h
    exact h
  have hσSphere : P σ ∈ sphere z (3 * r / 4) := by
    simpa [mem_sphere, dist_eq_norm] using hσNorm
  have htimeCross : m * SR ≤ σ - a := by
    have hbound := hcross.trans (sew_setDist_le_dist R hR hσSphere haSphere)
    rw [hgeo σ hσI a haI, abs_of_nonneg (sub_nonneg.mpr haσ.le)] at hbound
    exact (ENNReal.ofReal_le_ofReal_iff (sub_nonneg.mpr haσ.le)).mp hbound
  have hdiffLow : r / 4 ≤ ‖P a - P σ‖ := by
    have h := norm_sub_norm_le (P a - z) (P σ - z)
    rw [haNorm, hσNorm] at h
    have h' : ‖(P a - z) - (P σ - z)‖ = ‖P a - P σ‖ := by
      congr 1
      abel
    rw [h'] at h
    linarith
  have hdiffHigh : ‖P a - P σ‖ ≤ 1 / 2 := by
    have h : ‖P a - P σ‖ ≤ ‖P a - z‖ + ‖P σ - z‖ := by
      calc
        ‖P a - P σ‖ = ‖(P a - z) - (P σ - z)‖ := by congr 1; abel
        _ ≤ ‖P a - z‖ + ‖P σ - z‖ := norm_sub_le _ _
    rw [haNorm, hσNorm] at h
    linarith
  have hPaW : P a ∈ closedBall (0 : Rd d) (W + 1) := by
    rw [mem_closedBall, dist_zero_right]
    linarith [hW a haI]
  have hPσW : P σ ∈ closedBall (0 : Rd d) (W + 1) := by
    rw [mem_closedBall, dist_zero_right]
    linarith [hW σ hσI]
  have htimeMin : H⁻¹ * (rm / 4) ^ β ≤ σ - a := by
    have hmod' := hmod (P a) hPaW (P σ) hPσW hdiffHigh
    rw [hgeo a haI σ hσI, abs_of_nonpos (sub_nonpos.mpr haσ.le), neg_sub] at hmod'
    have hpow : (rm / 4) ^ β ≤ ‖P a - P σ‖ ^ β :=
      Real.rpow_le_rpow (by positivity) (by linarith [hrmr, hdiffLow]) hβ.le
    have hinv : 0 ≤ H⁻¹ := inv_nonneg.mpr (by linarith)
    exact (mul_le_mul_of_nonneg_left hpow hinv).trans hmod'
  have htimeDiam := sew_diameter_time R P (le_of_lt (hac.trans hcb))
    (hgeo a haI b hbI) z r M SR hM.le hSR.le haSphere hbSphere hdiam
  exact ⟨σ, haσ, hσc, hblockAnn, haNorm, hσNorm,
    htimeCross, htimeMin, htimeDiam⟩

/-- The total real length of a compact interval cannot exceed the sum of
upper bounds for the volumes of finitely many sets covering it. -/
private theorem sew_cover_measure_bound {ι : Type*} [DecidableEq ι]
    (s t : ℝ) (F : Finset ι) (J : ι → Set ℝ)
    (w : ι → ℝ) (hcov : Icc s t ⊆ ⋃ i ∈ F, J i)
    (hw : ∀ i ∈ F, 0 ≤ w i)
    (hvol : ∀ i ∈ F, volume (J i) ≤ ENNReal.ofReal (w i)) :
    t - s ≤ ∑ i ∈ F, w i := by
  have h : ENNReal.ofReal (t - s) ≤ ∑ i ∈ F, ENNReal.ofReal (w i) := by
    calc
      ENNReal.ofReal (t - s) = volume (Icc s t) := Real.volume_Icc.symm
      _ ≤ volume (⋃ i ∈ F, J i) := measure_mono hcov
      _ ≤ ∑ i ∈ F, volume (J i) := measure_biUnion_finset_le F J
      _ ≤ ∑ i ∈ F, ENNReal.ofReal (w i) := by
        apply Finset.sum_le_sum
        intro i hi
        exact hvol i hi
  rw [← ENNReal.ofReal_sum_of_nonneg hw] at h
  exact (ENNReal.ofReal_le_ofReal_iff (Finset.sum_nonneg fun i hi => hw i hi)).mp h

/-- Sew a finite ordered family of disjoint blocks. Each gap pays the rough
comparison and each block pays the improved connector estimate. -/
private theorem sew_gap_bound {ι : Type*} [LinearOrder ι]
    (D : ℝ → ℝ → ℝ) (s t C b e : ℝ)
    (a c : ι → ℝ)
    (htriangle : ∀ x y z, D x z ≤ D x y + D y z)
    (hrough : ∀ u ∈ Icc s t, ∀ v ∈ Icc s t, u ≤ v →
      D u v ≤ C * (v - u) + e)
    (K : Finset ι)
    (hblock : ∀ i ∈ K, D (a i) (c i) ≤ b * (c i - a i))
    (hspan : ∀ i ∈ K, s ≤ a i ∧ a i ≤ c i ∧ c i ≤ t)
    (hsep : ∀ i ∈ K, ∀ j ∈ K, i < j → c i ≤ a j) :
    ∀ u ∈ Icc s t, (∀ i ∈ K, u ≤ a i) →
      D u t ≤ C * (t - u - ∑ i ∈ K, (c i - a i)) +
        b * (∑ i ∈ K, (c i - a i)) + (K.card + 1 : ℕ) * e := by
  induction K using Finset.strongInductionOn with
  | _ K ih =>
    intro u hu hstart
    by_cases hKempty : K = ∅
    · subst K
      simpa using hrough u hu t (right_mem_Icc.mpr (hu.1.trans hu.2)) hu.2
    · have hKne : K.Nonempty := Finset.nonempty_iff_ne_empty.mpr hKempty
      let i : ι := K.min' hKne
      have hi : i ∈ K := K.min'_mem hKne
      have hK' : K.erase i ⊂ K := Finset.erase_ssubset hi
      have hsepstart : ∀ j ∈ K.erase i, c i ≤ a j := by
        intro j hj
        exact hsep i hi j (Finset.mem_of_mem_erase hj)
          (K.min'_lt_of_mem_erase_min' hKne hj)
      have htail : D (c i) t ≤
          C * (t - c i - ∑ j ∈ K.erase i, (c j - a j)) +
          b * (∑ j ∈ K.erase i, (c j - a j)) +
          ((K.erase i).card + 1 : ℕ) * e := by
        apply ih (K.erase i) hK'
        · intro j hj
          exact hblock j (Finset.mem_of_mem_erase hj)
        · intro j hj
          exact hspan j (Finset.mem_of_mem_erase hj)
        · intro j hj k hk hjk
          exact hsep j (Finset.mem_of_mem_erase hj) k (Finset.mem_of_mem_erase hk) hjk
        · exact ⟨(hspan i hi).1.trans (hspan i hi).2.1,
            (hspan i hi).2.2⟩
        · exact hsepstart
      have hgap : D u (a i) ≤ C * (a i - u) + e :=
        hrough u hu (a i) ⟨(hspan i hi).1, (hspan i hi).2.1.trans
          (hspan i hi).2.2⟩ (hstart i hi)
      have htri : D u t ≤ D u (a i) + D (a i) (c i) + D (c i) t := by
        calc
          D u t ≤ D u (a i) + D (a i) t := htriangle u (a i) t
          _ ≤ D u (a i) + (D (a i) (c i) + D (c i) t) := by
            gcongr
            exact htriangle (a i) (c i) t
          _ = D u (a i) + D (a i) (c i) + D (c i) t := by ring
      have hsum : (∑ j ∈ K, (c j - a j)) =
          (c i - a i) + ∑ j ∈ K.erase i, (c j - a j) :=
        (K.add_sum_erase _ hi).symm
      have hcard : ((K.card + 1 : ℕ) : ℝ) =
          (((K.erase i).card + 1 : ℕ) : ℝ) + 1 := by
        have hcardNat := Finset.card_erase_add_one hi
        exact_mod_cast (by omega : K.card + 1 = (K.erase i).card + 1 + 1)
      calc
        D u t ≤ D u (a i) + D (a i) (c i) + D (c i) t := htri
        _ ≤ (C * (a i - u) + e) + b * (c i - a i) +
            (C * (t - c i - ∑ j ∈ K.erase i, (c j - a j)) +
             b * (∑ j ∈ K.erase i, (c j - a j)) +
             ((K.erase i).card + 1 : ℕ) * e) := by
          gcongr
          exact hblock i hi
        _ = C * (t - u - ∑ j ∈ K, (c j - a j)) +
            b * (∑ j ∈ K, (c j - a j)) + (K.card + 1 : ℕ) * e := by
          rw [hsum, hcard]
          ring

/-- One parity class carries at least half the total nonnegative block weight. -/
private theorem sew_choose_parity {n : ℕ} (K : Finset (Fin n))
    (w : Fin n → ℝ) :
    ∃ A : Finset (Fin n), A ⊆ K ∧
      (∀ i ∈ A, ∀ j ∈ A, i < j → i.val + 2 ≤ j.val) ∧
      (∑ i ∈ K, w i) ≤ 2 * (∑ i ∈ A, w i) := by
  classical
  let E := K.filter (fun i => i.val % 2 = 0)
  let O := K.filter (fun i => i.val % 2 ≠ 0)
  have hsplit : (∑ i ∈ K, w i) = (∑ i ∈ E, w i) + (∑ i ∈ O, w i) := by
    simpa only [E, O] using
      (Finset.sum_filter_add_sum_filter_not K (fun i : Fin n => i.val % 2 = 0) w).symm
  by_cases hcmp : (∑ i ∈ E, w i) ≤ (∑ i ∈ O, w i)
  · refine ⟨O, Finset.filter_subset _ _, ?_, ?_⟩
    · intro i hi j hj hij
      have hi' : i.val % 2 ≠ 0 := (Finset.mem_filter.mp hi).2
      have hj' : j.val % 2 ≠ 0 := (Finset.mem_filter.mp hj).2
      have himod := Nat.mod_lt i.val (by norm_num : 0 < 2)
      have hjmod := Nat.mod_lt j.val (by norm_num : 0 < 2)
      have hij' : i.val < j.val := hij
      omega
    · rw [hsplit]
      linarith
  · refine ⟨E, Finset.filter_subset _ _, ?_, ?_⟩
    · intro i hi j hj hij
      have hi' : i.val % 2 = 0 := (Finset.mem_filter.mp hi).2
      have hj' : j.val % 2 = 0 := (Finset.mem_filter.mp hj).2
      have hij' : i.val < j.val := hij
      omega
    · rw [hsplit]
      linarith

/-- Ordered, separated real blocks fit inside their enclosing parameter interval. -/
private theorem sew_disjoint_sum_le {ι : Type*} [LinearOrder ι]
    (K : Finset ι) (t : ℝ) (a c : ι → ℝ)
    (hspan : ∀ i ∈ K, a i ≤ c i ∧ c i ≤ t)
    (hsep : ∀ i ∈ K, ∀ j ∈ K, i < j → c i ≤ a j) :
    ∀ u, u ≤ t → (∀ i ∈ K, u ≤ a i) →
      (∑ i ∈ K, (c i - a i)) ≤ t - u := by
  induction K using Finset.strongInductionOn with
  | _ K ih =>
    intro u hut hstart
    by_cases hKempty : K = ∅
    · subst K
      simp
      linarith
    · have hKne : K.Nonempty := Finset.nonempty_iff_ne_empty.mpr hKempty
      let i : ι := K.min' hKne
      have hi : i ∈ K := K.min'_mem hKne
      have hK' : K.erase i ⊂ K := Finset.erase_ssubset hi
      have hspan' : ∀ j ∈ K.erase i, a j ≤ c j ∧ c j ≤ t := by
        intro j hj
        exact hspan j (Finset.mem_of_mem_erase hj)
      have hsep' : ∀ j ∈ K.erase i, ∀ k ∈ K.erase i,
          j < k → c j ≤ a k := by
        intro j hj k hk hjk
        exact hsep j (Finset.mem_of_mem_erase hj) k
          (Finset.mem_of_mem_erase hk) hjk
      have htail := ih (K.erase i) hK' hspan' hsep' (c i)
        (hspan i hi).2 (by
          intro j hj
          exact hsep i hi j (Finset.mem_of_mem_erase hj)
            (K.min'_lt_of_mem_erase_min' hKne hj))
      rw [← K.add_sum_erase (fun j => c j - a j) hi]
      linarith [hstart i hi]

/-- Two points of the geodesic in one covering ball are close in parameter
time by the upper Euclidean-to-`R` modulus. -/
private theorem sew_same_ball_time {d : ℕ} (R : ContMetric d)
    (P : ℝ → Rd d) {ℓ W H σ rp : ℝ}
    (hgeo : ∀ u ∈ Icc (0 : ℝ) ℓ, ∀ v ∈ Icc (0 : ℝ) ℓ,
      R.1 (P u, P v) = |u - v|)
    (hW : ∀ u ∈ Icc (0 : ℝ) ℓ, ‖P u‖ ≤ W)
    (hH : 1 ≤ H) (hσ : 0 < σ) (hrp : rp ≤ 1 / 4)
    (hmod : ∀ x ∈ closedBall (0 : Rd d) (W + 1),
      ∀ y ∈ closedBall (0 : Rd d) (W + 1), ‖x - y‖ ≤ 1 / 2 →
        R.1 (x, y) ≤ H * ‖x - y‖ ^ σ)
    {u v : ℝ} (hu : u ∈ Icc (0 : ℝ) ℓ) (hv : v ∈ Icc (0 : ℝ) ℓ)
    {z : Rd d} {r : ℝ} (hr : r ≤ rp)
    (hbu : P u ∈ ball z r) (hbv : P v ∈ ball z r) :
    |u - v| ≤ H * (2 * rp) ^ σ := by
  have hunorm : ‖P u - z‖ < r := by simpa [mem_ball, dist_eq_norm] using hbu
  have hvnorm : ‖P v - z‖ < r := by simpa [mem_ball, dist_eq_norm] using hbv
  have hdiff : ‖P u - P v‖ ≤ 2 * rp := by
    calc
      ‖P u - P v‖ = ‖(P u - z) - (P v - z)‖ := by congr 1; abel
      _ ≤ ‖P u - z‖ + ‖P v - z‖ := norm_sub_le _ _
      _ ≤ 2 * rp := by linarith
  have hhalf : ‖P u - P v‖ ≤ 1 / 2 := by linarith
  have huW : P u ∈ closedBall (0 : Rd d) (W + 1) := by
    rw [mem_closedBall, dist_zero_right]
    linarith [hW u hu]
  have hvW : P v ∈ closedBall (0 : Rd d) (W + 1) := by
    rw [mem_closedBall, dist_zero_right]
    linarith [hW v hv]
  have hpow : ‖P u - P v‖ ^ σ ≤ (2 * rp) ^ σ :=
    Real.rpow_le_rpow (norm_nonneg _) hdiff hσ.le
  calc
    |u - v| = R.1 (P u, P v) := (hgeo u hu v hv).symm
    _ ≤ H * ‖P u - P v‖ ^ σ := hmod (P u) huW (P v) hvW hhalf
    _ ≤ H * (2 * rp) ^ σ := mul_le_mul_of_nonneg_left hpow (by linarith)

private theorem sew_clipped_volume {d : ℕ} (R : ContMetric d)
    (P : ℝ → Rd d) {ℓ W H σ rp s t : ℝ}
    (hs : s ∈ Icc (0 : ℝ) ℓ) (ht : t ∈ Icc (0 : ℝ) ℓ)
    (hgeo : ∀ u ∈ Icc (0 : ℝ) ℓ, ∀ v ∈ Icc (0 : ℝ) ℓ,
      R.1 (P u, P v) = |u - v|)
    (hW : ∀ u ∈ Icc (0 : ℝ) ℓ, ‖P u‖ ≤ W)
    (hH : 1 ≤ H) (hσ : 0 < σ) (hrp : rp ≤ 1 / 4)
    (hmod : ∀ x ∈ closedBall (0 : Rd d) (W + 1),
      ∀ y ∈ closedBall (0 : Rd d) (W + 1), ‖x - y‖ ≤ 1 / 2 →
        R.1 (x, y) ≤ H * ‖x - y‖ ^ σ)
    (J : Set ℝ) (hJ : J ⊆ Icc s t)
    (z : Rd d) {r : ℝ} (hr : r ≤ rp)
    (hball : ∀ u ∈ J, P u ∈ ball z r)
    (hend : s ∈ J ∨ t ∈ J) :
    volume J ≤ ENNReal.ofReal (H * (2 * rp) ^ σ) := by
  let E : ℝ := H * (2 * rp) ^ σ
  rcases hend with hsj | htj
  · have hsub : J ⊆ Icc s (s + E) := by
      intro u hu
      have huI : u ∈ Icc (0 : ℝ) ℓ :=
        ⟨hs.1.trans (hJ hu).1, (hJ hu).2.trans ht.2⟩
      have htime := sew_same_ball_time R P hgeo hW hH hσ hrp hmod
        huI hs hr (hball u hu) (hball s hsj)
      refine ⟨(hJ hu).1, ?_⟩
      have habs : u - s ≤ |u - s| := le_abs_self _
      dsimp [E]
      linarith
    calc
      volume J ≤ volume (Icc s (s + E)) := measure_mono hsub
      _ = ENNReal.ofReal E := by rw [Real.volume_Icc]; congr 1; ring
      _ = ENNReal.ofReal (H * (2 * rp) ^ σ) := rfl

  · have hsub : J ⊆ Icc (t - E) t := by
      intro u hu
      have huI : u ∈ Icc (0 : ℝ) ℓ :=
        ⟨hs.1.trans (hJ hu).1, (hJ hu).2.trans ht.2⟩
      have htime := sew_same_ball_time R P hgeo hW hH hσ hrp hmod
        ht huI hr (hball t htj) (hball u hu)
      refine ⟨?_, (hJ hu).2⟩
      have habs : t - u ≤ |t - u| := le_abs_self _
      dsimp [E]
      linarith
    calc
      volume J ≤ volume (Icc (t - E) t) := measure_mono hsub
      _ = ENNReal.ofReal E := by rw [Real.volume_Icc]; congr 1; ring
      _ = ENNReal.ofReal (H * (2 * rp) ^ σ) := rfl

private theorem sew_disjoint_open_intervals {a b c d : ℝ}
    (hab : a < b) (hcd : c < d) (hac : a < c)
    (hdisj : ¬ (Ioo a b ∩ Ioo c d).Nonempty) : b ≤ c := by
  by_contra h
  have hcb : c < b := lt_of_not_ge h
  have hlo : max a c < min b d := by
    apply lt_min
    · exact max_lt hab hcb
    · exact max_lt (hac.trans hcd) hcd
  obtain ⟨x, hxlo, hxhi⟩ := exists_between hlo
  apply hdisj
  refine ⟨x, ?_, ?_⟩
  · exact ⟨(lt_of_le_of_lt (le_max_left _ _) hxlo),
      (lt_of_lt_of_le hxhi (min_le_left _ _))⟩
  · exact ⟨(lt_of_le_of_lt (le_max_right _ _) hxlo),
      (lt_of_lt_of_le hxhi (min_le_right _ _))⟩

/-- Lemma 3.1(b): contraction of the excess on every subsegment of an
`R`-geodesic parametrized by `R`-length. -/
theorem lemma31b {d : ℕ} (_hd : 2 ≤ d) (R Q : ContMetric d) (hR : R.IsLength)
    (F : Finset (SewBall d)) (P : ℝ → Rd d) (ℓ W : ℝ)
    (hℓ : 0 ≤ ℓ) (_hW0 : 0 ≤ W)
    (hgeo : ∀ u ∈ Icc (0 : ℝ) ℓ, ∀ v ∈ Icc (0 : ℝ) ℓ,
      R.1 (P u, P v) = |u - v|)
    (hW : ∀ u ∈ Icc (0 : ℝ) ℓ, ‖P u‖ ≤ W)
    (C e H σ β rm rp m M b : ℝ) (SR : SewBall d → ℝ)
    (hm : 0 < m) (hM : 0 < M) (hmM : m ≤ M)
    (hb : 0 ≤ b) (hbC : b ≤ C) (he : 0 ≤ e) (hH : 1 ≤ H)
    (hσ : 0 < σ) (hβ : 0 < β) (hrm : 0 < rm)
    (hrmr : rm ≤ rp) (hrp : rp ≤ 1 / 4)
    (hrough : ∀ u ∈ Icc (0 : ℝ) ℓ, ∀ v ∈ Icc (0 : ℝ) ℓ,
      Q.1 (P u, P v) ≤ C * |u - v| + e)
    (hmod : ∀ x ∈ closedBall (0 : Rd d) (W + 1),
      ∀ y ∈ closedBall (0 : Rd d) (W + 1), ‖x - y‖ ≤ 1 / 2 →
        R.1 (x, y) ≤ H * ‖x - y‖ ^ σ ∧
        H⁻¹ * ‖x - y‖ ^ β ≤ R.1 (x, y))
    (hF : ∀ B ∈ F, rm ≤ B.2 ∧ B.2 ≤ rp ∧ 0 < SR B)
    (hcov : ∀ u ∈ Icc (0 : ℝ) ℓ,
      ∃ B ∈ F, ‖P u - B.1‖ < B.2 / 10)
    (hcross : ∀ B ∈ F, ENNReal.ofReal (m * SR B) ≤
      HigherDimLQGMetric.setDistIn R univ
        (sphere B.1 (3 * B.2 / 4)) (sphere B.1 B.2))
    (hdiam : ∀ B ∈ F, HigherDimLQGMetric.diamIn R
      (HigherDimLQGMetric.ann B.1 (B.2 / 2) (7 * B.2 / 2))
      (sphere B.1 B.2) ≤ ENNReal.ofReal (M * SR B))
    (hconnector : ∀ B ∈ F, ∀ u ∈ Icc (0 : ℝ) ℓ,
      ∀ v ∈ Icc (0 : ℝ) ℓ, u ≤ v →
      P '' Icc u v ⊆ HigherDimLQGMetric.annCl B.1 (3 * B.2 / 4) B.2 →
      ((‖P u - B.1‖ = B.2 ∧ ‖P v - B.1‖ = 3 * B.2 / 4) ∨
       (‖P u - B.1‖ = 3 * B.2 / 4 ∧ ‖P v - B.1‖ = B.2)) →
      Q.1 (P u, P v) ≤ b * (v - u))
    {s t : ℝ} (hs : s ∈ Icc (0 : ℝ) ℓ) (ht : t ∈ Icc (0 : ℝ) ℓ)
    (hst : s ≤ t) :
    Q.1 (P s, P t) ≤
      (b + (1 - m / (2 * M)) * (C - b) +
        e / (H⁻¹ * (rm / 4) ^ β)) * (t - s) +
      C * (2 * H * (2 * rp) ^ σ) + e := by
  classical
  by_cases hst' : s = t
  · subst t
    simp only [sub_self, mul_zero, zero_add, Q.apply_self]
    have hC : 0 ≤ C := hb.trans hbC
    have hrp0 : 0 < rp := hrm.trans_le hrmr
    have hH0 : 0 ≤ H := by linarith
    have hE : 0 ≤ 2 * H * (2 * rp) ^ σ := by positivity
    nlinarith
  have hstlt : s < t := lt_of_le_of_ne hst hst'
  obtain ⟨G, B, a, amax, hGcov, hGdata, hGball, hGboundary⟩ :=
    sew_finite_component_cover R F P hℓ hs ht hgeo hcov
  obtain ⟨S, hSG, hScov, hSminimal, hSorder,
      first, hfirst, last, hlast, hsfirst, htlast,
      hfirstmin, hlastmax, hinterior, hneighbor⟩ :=
    interval_cover s t hstlt a amax G hGcov
  obtain ⟨j, hjimage, hjmono⟩ :=
    sew_ordered_enumeration s t a amax S hScov hSminimal
  have hjS : ∀ k : Fin S.card, j k ∈ S := by
    intro k
    rw [← hjimage]
    exact Finset.mem_image.mpr ⟨k, Finset.mem_univ _, rfl⟩
  have hsurj : ∀ i ∈ S, ∃ k : Fin S.card, j k = i := by
    intro i hi
    rw [← hjimage] at hi
    obtain ⟨k, -, hki⟩ := Finset.mem_image.mp hi
    exact ⟨k, hki⟩
  obtain ⟨kf, hkf⟩ := hsurj first hfirst
  obtain ⟨kl, hkl⟩ := hsurj last hlast
  let J : Fin S.card → Set ℝ := fun k => sewInterval s t a amax (j k)
  let α : Fin S.card → ℝ := fun k => a (j k)
  let ω : Fin S.card → ℝ := fun k => amax (j k)
  let T : ℝ := H * (2 * rp) ^ σ
  let Bmin : ℝ := H⁻¹ * (rm / 4) ^ β
  let K : Finset (Fin S.card) := (Finset.univ.erase kf).erase kl
  have hT : 0 ≤ T := by
    dsimp [T]
    have hrp0 : 0 < rp := hrm.trans_le hrmr
    positivity
  have hKint : ∀ k ∈ K,
      s ≤ α k ∧ α k < ω k ∧ ω k ≤ t ∧ J k = Ioo (α k) (ω k) := by
    intro k hk
    have hkkl : k ≠ kl := (Finset.mem_erase.mp hk).1
    have hkkf : k ≠ kf :=
      (Finset.mem_erase.mp (Finset.mem_erase.mp hk).2).1
    apply hinterior (j k) (hjS k)
    · intro h
      exact hkkf (hjmono.injective (congrArg a (h.trans hkf.symm)))
    · intro h
      exact hkkl (hjmono.injective (congrArg a (h.trans hkl.symm)))
  have hJsub : ∀ k : Fin S.card, J k ⊆ Icc s t := by
    intro k x hx
    exact hx.2
  have hJball : ∀ k : Fin S.card, ∀ x ∈ J k,
      P x ∈ ball (B (j k)).1 (B (j k)).2 := by
    intro k x hx
    exact hGball (j k) (hSG (hjS k)) x hx
  have hcoverj : Icc s t ⊆ ⋃ k ∈ (Finset.univ : Finset (Fin S.card)), J k := by
    intro x hx
    obtain ⟨i, hi, hxi⟩ := Set.mem_iUnion₂.mp (hScov hx)
    obtain ⟨k, hk⟩ := hsurj i hi
    exact Set.mem_iUnion₂.mpr ⟨k, Finset.mem_univ _, by simpa only [J, hk] using hxi⟩
  let w : Fin S.card → ℝ := fun k => if k ∈ K then ω k - α k else T
  have hw : ∀ k ∈ (Finset.univ : Finset (Fin S.card)), 0 ≤ w k := by
    intro k _
    by_cases hk : k ∈ K
    · simp only [w, ite_eq_left hk]
      exact sub_nonneg.mpr (hKint k hk).2.1.le
    · simp only [w, ite_eq_right hk]
      exact hT
  have hvol : ∀ k ∈ (Finset.univ : Finset (Fin S.card)),
      volume (J k) ≤ ENNReal.ofReal (w k) := by
    intro k _
    by_cases hk : k ∈ K
    · simp only [w, ite_eq_left hk]
      rw [(hKint k hk).2.2.2, Real.volume_Ioo]
    · have hends : k = kf ∨ k = kl := by
        simp only [K, Finset.mem_erase, Finset.mem_univ, and_true, not_and,
          not_not] at hk
        tauto
      have hbe : (B (j k)).2 ≤ rp := (hF _ (hGdata (j k) (hSG (hjS k))).1).2.1
      have hevent : s ∈ J k ∨ t ∈ J k := by
        rcases hends with h | h
        · left
          simpa only [J, h, hkf] using hsfirst
        · right
          simpa only [J, h, hkl] using htlast
      simp only [w, ite_eq_right hk]
      exact sew_clipped_volume R P hs ht hgeo hW hH hσ hrp
        (fun x hx y hy hxy => (hmod x hx y hy hxy).1)
        (J k) (hJsub k) (B (j k)).1 hbe (hJball k) hevent
  have hmeasure := sew_cover_measure_bound s t
    (Finset.univ : Finset (Fin S.card)) J w hcoverj hw hvol
  have hlengthCover : t - s ≤ 2 * T + ∑ k ∈ K, (ω k - α k) := by
    have hsplit := Finset.sum_filter_add_sum_filter_not
      (Finset.univ : Finset (Fin S.card)) (fun k => k ∈ K) w
    have hleft : (Finset.univ : Finset (Fin S.card)).filter (fun k => k ∈ K) = K := by
      ext k
      simp
    have hright : (Finset.univ : Finset (Fin S.card)).filter (fun k => k ∉ K) =
        ({kf, kl} : Finset (Fin S.card)) := by
      ext k
      simp only [Finset.mem_filter, Finset.mem_univ, true_and,
        Finset.mem_insert, Finset.mem_singleton]
      simp only [K, Finset.mem_erase, Finset.mem_univ, and_true]
      tauto
    rw [hleft, hright] at hsplit
    have hKsum : (∑ k ∈ K, w k) = ∑ k ∈ K, (ω k - α k) := by
      apply Finset.sum_congr rfl
      intro k hk
      simp [w, hk]
    have hEndSum : (∑ k ∈ ({kf, kl} : Finset (Fin S.card)), w k) ≤ 2 * T := by
      by_cases heq : kf = kl
      · subst kl
        simp [w, K]
        linarith
      · have hkfnot : kf ∉ K := by simp [K]
        have hklnot : kl ∉ K := by simp [K]
        simp [heq, w, hkfnot, hklnot]
        nlinarith
    rw [hKsum] at hsplit
    linarith
  have hP : ContinuousOn P (Icc 0 ℓ) := sew_geodesic_continuous R P hgeo
  have hblockRaw : ∀ k ∈ K, ∃ c : ℝ,
      α k < c ∧ c ≤ (j k).1 ∧
      P '' Icc (α k) c ⊆ HigherDimLQGMetric.annCl
        (B (j k)).1 (3 * (B (j k)).2 / 4) (B (j k)).2 ∧
      ‖P (α k) - (B (j k)).1‖ = (B (j k)).2 ∧
      ‖P c - (B (j k)).1‖ = 3 * (B (j k)).2 / 4 ∧
      m * SR (B (j k)) ≤ c - α k ∧ Bmin ≤ c - α k ∧
      ω k - α k ≤ M * SR (B (j k)) := by
    intro k hk
    have hint := hKint k hk
    have hiG : j k ∈ G := hSG (hjS k)
    have hballData := hGdata (j k) hiG
    have hcoreJ : (j k).1 ∈ J k := hballData.2.1
    rw [hint.2.2.2] at hcoreJ
    have hαc : α k < (j k).1 := hcoreJ.1
    have hcω : (j k).1 < ω k := hcoreJ.2
    have hαI : α k ∈ Icc (0 : ℝ) ℓ :=
      ⟨hs.1.trans hint.1, (hint.2.1.le.trans hint.2.2.1).trans ht.2⟩
    have hωI : ω k ∈ Icc (0 : ℝ) ℓ :=
      ⟨hs.1.trans (hint.1.trans hint.2.1.le), hint.2.2.1.trans ht.2⟩
    have hcI : (j k).1 ∈ Icc (0 : ℝ) ℓ :=
      ⟨hs.1.trans (j k).2.1, (j k).2.2.trans ht.2⟩
    have hαT : α k ∈ Icc s t :=
      ⟨hint.1, hint.2.1.le.trans hint.2.2.1⟩
    have hωT : ω k ∈ Icc s t :=
      ⟨hint.1.trans hint.2.1.le, hint.2.2.1⟩
    have hαcl : α k ∈ closure (J k) := by
      rw [hint.2.2.2, closure_Ioo hint.2.1.ne]
      exact left_mem_Icc.mpr hint.2.1.le
    have hωcl : ω k ∈ closure (J k) := by
      rw [hint.2.2.2, closure_Ioo hint.2.1.ne]
      exact right_mem_Icc.mpr hint.2.1.le
    have hαnot : α k ∉ J k := by rw [hint.2.2.2]; simp
    have hωnot : ω k ∉ J k := by rw [hint.2.2.2]; simp
    have hαsphere : P (α k) ∈ sphere (B (j k)).1 (B (j k)).2 :=
      hGboundary (j k) hiG (α k) hαT hαcl hαnot
    have hωsphere : P (ω k) ∈ sphere (B (j k)).1 (B (j k)).2 :=
      hGboundary (j k) hiG (ω k) hωT hωcl hωnot
    have hinside : ∀ u ∈ Ioo (α k) (ω k),
        P u ∈ ball (B (j k)).1 (B (j k)).2 := by
      intro u hu
      exact hJball k u (hint.2.2.2.symm ▸ hu)
    have hBk := hF (B (j k)) hballData.1
    have hlowMod : ∀ x ∈ closedBall (0 : Rd d) (W + 1),
        ∀ y ∈ closedBall (0 : Rd d) (W + 1), ‖x - y‖ ≤ 1 / 2 →
          H⁻¹ * ‖x - y‖ ^ β ≤ R.1 (x, y) := by
      intro x hx y hy hxy
      exact (hmod x hx y hy hxy).2
    simpa only [Bmin] using
      sew_interior_block R hR P hP hαI hcI hωI hαc hcω
        hgeo hW H β rm (B (j k)).2 m M (SR (B (j k)))
        hH hβ hrm hBk.1 (hBk.2.1.trans hrp) hM hBk.2.2
        (B (j k)).1 hαsphere hωsphere hinside hballData.2.2
        hlowMod (hcross _ hballData.1) (hdiam _ hballData.1)
  let c : Fin S.card → ℝ := fun k =>
    if hk : k ∈ K then Classical.choose (hblockRaw k hk) else α k
  have hc : ∀ k ∈ K,
      α k < c k ∧ c k ≤ (j k).1 ∧
      P '' Icc (α k) (c k) ⊆ HigherDimLQGMetric.annCl
        (B (j k)).1 (3 * (B (j k)).2 / 4) (B (j k)).2 ∧
      ‖P (α k) - (B (j k)).1‖ = (B (j k)).2 ∧
      ‖P (c k) - (B (j k)).1‖ = 3 * (B (j k)).2 / 4 ∧
      m * SR (B (j k)) ≤ c k - α k ∧ Bmin ≤ c k - α k ∧
      ω k - α k ≤ M * SR (B (j k)) := by
    intro k hk
    simpa [c, hk] using Classical.choose_spec (hblockRaw k hk)
  have hcω : ∀ k ∈ K, c k ≤ ω k := by
    intro k hk
    have hcoreJ : (j k).1 ∈ J k := (hGdata (j k) (hSG (hjS k))).2.1
    rw [(hKint k hk).2.2.2] at hcoreJ
    exact (hc k hk).2.1.trans hcoreJ.2.le
  have hGap2 : ∀ k ∈ K, ∀ l ∈ K,
      k.val + 2 ≤ l.val → ω k ≤ α l := by
    intro k hk l hl hkl2
    let mid : Fin S.card := ⟨k.val + 1, by have := l.isLt; omega⟩
    have hkm : k < mid := by change k.val < k.val + 1; omega
    have hml : mid < l := by change k.val + 1 < l.val; omega
    have hkl : k < l := hkm.trans hml
    have hbetween : ∃ i ∈ S,
        a (j k) < a i ∧ a i < a (j l) :=
      ⟨j mid, hjS mid, hjmono hkm, hjmono hml⟩
    have hdisj : ¬ (J k ∩ J l).Nonempty :=
      (hneighbor (j k) (hjS k) (j l) (hjS l) (hjmono hkl)).mp hbetween
    rw [(hKint k hk).2.2.2, (hKint l hl).2.2.2] at hdisj
    exact sew_disjoint_open_intervals (hKint k hk).2.1
      (hKint l hl).2.1 (hjmono hkl) hdisj
  obtain ⟨A, hAK, hAparity, hAweight⟩ :=
    sew_choose_parity K (fun k => c k - α k)
  have hAspan : ∀ k ∈ A, s ≤ α k ∧ α k ≤ c k ∧ c k ≤ t := by
    intro k hk
    have hkK := hAK hk
    exact ⟨(hKint k hkK).1, (hc k hkK).1.le,
      (hcω k hkK).trans (hKint k hkK).2.2.1⟩
  have hAsep : ∀ k ∈ A, ∀ l ∈ A, k < l → c k ≤ α l := by
    intro k hk l hl hkl
    exact (hcω k (hAK hk)).trans
      (hGap2 k (hAK hk) l (hAK hl) (hAparity k hk l hl hkl))
  have hratio : ∀ k ∈ K, (m / M) * (ω k - α k) ≤ c k - α k := by
    intro k hk
    have hBk : 0 < SR (B (j k)) :=
      (hF _ (hGdata (j k) (hSG (hjS k))).1).2.2
    have hbound : m * (ω k - α k) ≤ (c k - α k) * M := by
      have hd := (hc k hk).2.2.2.2.2.2.2
      have hx := (hc k hk).2.2.2.2.2.1
      nlinarith [mul_le_mul_of_nonneg_left hd hm.le,
        mul_le_mul_of_nonneg_left hx hM.le]
    calc
      (m / M) * (ω k - α k) = (m * (ω k - α k)) / M := by ring
      _ ≤ c k - α k := (div_le_iff₀ hM).mpr hbound
  have hratioSum : (m / M) * (∑ k ∈ K, (ω k - α k)) ≤
      ∑ k ∈ K, (c k - α k) := by
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum fun k hk => hratio k hk
  have hθ : 0 ≤ m / (2 * M) := by positivity
  have hθle : m / (2 * M) ≤ 1 := by
    apply (div_le_iff₀ (by positivity : 0 < 2 * M)).mpr
    nlinarith
  have hBfrac : (m / (2 * M)) * (t - s - 2 * T) ≤
      ∑ k ∈ A, (c k - α k) := by
    have hcover' : t - s - 2 * T ≤ ∑ k ∈ K, (ω k - α k) := by
      linarith [hlengthCover]
    calc
      (m / (2 * M)) * (t - s - 2 * T)
          ≤ (m / (2 * M)) * (∑ k ∈ K, (ω k - α k)) :=
        mul_le_mul_of_nonneg_left hcover' hθ
      _ = (1 / 2 : ℝ) * ((m / M) * (∑ k ∈ K, (ω k - α k))) := by ring
      _ ≤ (1 / 2 : ℝ) * (2 * ∑ k ∈ A, (c k - α k)) := by
        apply mul_le_mul_of_nonneg_left _ (by norm_num)
        exact hratioSum.trans hAweight
      _ = ∑ k ∈ A, (c k - α k) := by ring
  have hBmin : 0 < Bmin := by
    dsimp [Bmin]
    have hHpos : 0 < H := by linarith
    positivity
  have hAcount : (A.card : ℝ) * Bmin ≤ ∑ k ∈ A, (c k - α k) := by
    calc
      (A.card : ℝ) * Bmin = ∑ _k ∈ A, Bmin := by simp
      _ ≤ ∑ k ∈ A, (c k - α k) := by
        apply Finset.sum_le_sum
        intro k hk
        exact (hc k (hAK hk)).2.2.2.2.2.2.1
  have hAfit : (∑ k ∈ A, (c k - α k)) ≤ t - s :=
    sew_disjoint_sum_le A t α c
      (fun k hk => ⟨(hAspan k hk).2.1, (hAspan k hk).2.2⟩)
      hAsep s hst (fun k hk => (hAspan k hk).1)
  have hAcard : (A.card : ℝ) ≤ (t - s) / Bmin :=
    (le_div_iff₀ hBmin).mpr (hAcount.trans hAfit)
  have hAconnector : ∀ k ∈ A,
      Q.1 (P (α k), P (c k)) ≤ b * (c k - α k) := by
    intro k hk
    have hkK := hAK hk
    have hαI : α k ∈ Icc (0 : ℝ) ℓ :=
      ⟨hs.1.trans (hAspan k hk).1,
       (hAspan k hk).2.1.trans ((hAspan k hk).2.2.trans ht.2)⟩
    have hcI : c k ∈ Icc (0 : ℝ) ℓ :=
      ⟨hs.1.trans ((hAspan k hk).1.trans (hAspan k hk).2.1),
       (hAspan k hk).2.2.trans ht.2⟩
    exact hconnector (B (j k)) (hGdata (j k) (hSG (hjS k))).1
      (α k) hαI (c k) hcI (hc k hkK).1.le
      (hc k hkK).2.2.1
      (Or.inl ⟨(hc k hkK).2.2.2.1, (hc k hkK).2.2.2.2.1⟩)
  have hrough' : ∀ u ∈ Icc s t, ∀ v ∈ Icc s t, u ≤ v →
      Q.1 (P u, P v) ≤ C * (v - u) + e := by
    intro u hu v hv huv
    have huI : u ∈ Icc (0 : ℝ) ℓ := ⟨hs.1.trans hu.1, hu.2.trans ht.2⟩
    have hvI : v ∈ Icc (0 : ℝ) ℓ := ⟨hs.1.trans hv.1, hv.2.trans ht.2⟩
    simpa [abs_of_nonpos (sub_nonpos.mpr huv), neg_sub] using
      hrough u huI v hvI
  have hsew : Q.1 (P s, P t) ≤
      C * (t - s - ∑ k ∈ A, (c k - α k)) +
      b * (∑ k ∈ A, (c k - α k)) + (A.card + 1 : ℕ) * e := by
    apply sew_gap_bound (fun u v => Q.1 (P u, P v)) s t C b e α c
      (fun x y z => Q.apply_triangle _ _ _) hrough' A
      hAconnector hAspan hAsep s (left_mem_Icc.mpr hst)
    intro k hk
    exact (hAspan k hk).1
  have hC : 0 ≤ C := hb.trans hbC
  have hgain : (C - b) * ((m / (2 * M)) * (t - s - 2 * T)) ≤
      (C - b) * (∑ k ∈ A, (c k - α k)) :=
    mul_le_mul_of_nonneg_left hBfrac (sub_nonneg.mpr hbC)
  have herror : (A.card : ℝ) * e ≤ ((t - s) / Bmin) * e :=
    mul_le_mul_of_nonneg_right hAcard he
  have hcoef : (C - b) * (m / (2 * M)) ≤ C := by
    have := mul_le_mul_of_nonneg_left hθle (sub_nonneg.mpr hbC)
    nlinarith [hb]
  have hclip : ((C - b) * (m / (2 * M))) * (2 * T) ≤ C * (2 * T) :=
    mul_le_mul_of_nonneg_right hcoef (by linarith [hT])
  calc
    Q.1 (P s, P t)
        ≤ C * (t - s - ∑ k ∈ A, (c k - α k)) +
          b * (∑ k ∈ A, (c k - α k)) + (A.card + 1 : ℕ) * e := hsew
    _ = C * (t - s) - (C - b) * (∑ k ∈ A, (c k - α k)) +
          (A.card : ℝ) * e + e := by push_cast; ring
    _ ≤ C * (t - s) - (C - b) * ((m / (2 * M)) * (t - s - 2 * T)) +
          ((t - s) / Bmin) * e + e := by linarith [hgain, herror]
    _ = (b + (1 - m / (2 * M)) * (C - b) + e / Bmin) * (t - s) +
          ((C - b) * (m / (2 * M))) * (2 * T) + e := by ring
    _ ≤ (b + (1 - m / (2 * M)) * (C - b) + e / Bmin) * (t - s) +
          C * (2 * T) + e := by linarith [hclip]
    _ = (b + (1 - m / (2 * M)) * (C - b) +
          e / (H⁻¹ * (rm / 4) ^ β)) * (t - s) +
          C * (2 * H * (2 * rp) ^ σ) + e := by dsimp [T, Bmin]; ring

end HigherDimLQGContinuity
