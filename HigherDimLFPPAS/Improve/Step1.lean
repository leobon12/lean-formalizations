import HigherDimLFPPAS.Improve.Defs
import HigherDimLQGMetric.Metric.Internal

/-!
# Proposition 4.1, Step 1: closed hitting times and finite stopping

The first and last endpoint-ball hits are taken in closed Euclidean balls. This is the attained
version required by the cross-check audit.
-/

set_option autoImplicit false

noncomputable section

open Set Filter Topology Metric
open LQGMetric.MetricGeometry
open HigherDimLQGMetric
open HigherDimLFPP (Rd)

namespace HigherDimLFPPAS.Improve

variable {d : ℕ}

/-- A continuous curve attains its first hit of a closed target on a compact time interval. -/
theorem d4_exists_first_hit_closed {X : Type*} [TopologicalSpace X] {P : ℝ → X}
    {a b : ℝ} (hP : ContinuousOn P (Icc a b)) {K : Set X} (hK : IsClosed K)
    (hne : ∃ t ∈ Icc a b, P t ∈ K) :
    ∃ s ∈ Icc a b, P s ∈ K ∧ ∀ t ∈ Ico a s, P t ∉ K :=
  LQGMetric.MetricGeometry.exists_first_hit hP hK hne

/-- A continuous curve attains its last hit of a closed target on a compact time interval. -/
theorem d4_exists_last_hit_closed {X : Type*} [TopologicalSpace X] {P : ℝ → X}
    {a b : ℝ} (hP : ContinuousOn P (Icc a b)) {K : Set X} (hK : IsClosed K)
    (hne : ∃ t ∈ Icc a b, P t ∈ K) :
    ∃ s ∈ Icc a b, P s ∈ K ∧ ∀ t ∈ Ioc s b, P t ∉ K := by
  let S : Set ℝ := Icc a b ∩ P ⁻¹' K
  have hS : IsClosed S := hP.preimage_isClosed_of_isClosed isClosed_Icc hK
  have hSne : S.Nonempty := by
    obtain ⟨t, ht, htK⟩ := hne
    exact ⟨t, ht, htK⟩
  have hSbound : BddAbove S := ⟨b, fun t ht => ht.1.2⟩
  have hmem := hS.csSup_mem hSne hSbound
  refine ⟨sSup S, hmem.1, hmem.2, ?_⟩
  intro t ht htK
  have hta : a ≤ t := hmem.1.1.trans ht.1.le
  have htS : t ∈ S := ⟨⟨hta, ht.2⟩, htK⟩
  have htle : t ≤ sSup S := le_csSup hSbound htS
  exact (not_lt_of_ge htle) ht.1

/-- A first hit of a closed Euclidean ball is on its boundary if the curve starts outside. -/
theorem d4_first_closedBall_hit_boundary {P : ℝ → Rd d} {a b s : ℝ} {z : Rd d} {ρ : ℝ}
    (hP : ContinuousOn P (Icc a b)) (hs : s ∈ Icc a b)
    (hfirst : P s ∈ Metric.closedBall z ρ ∧
      ∀ t ∈ Ico a s, P t ∉ Metric.closedBall z ρ)
    (hstart : ρ < dist (P a) z) : dist (P s) z = ρ := by
  have hsle : dist (P s) z ≤ ρ := by
    simpa only [Metric.mem_closedBall, dist_comm] using hfirst.1
  rcases lt_or_eq_of_le hsle with hstrict | heq
  · let f : ℝ → ℝ := fun t => -dist (P t) z
    have hPc : ContinuousOn P (Icc a s) :=
      hP.mono (Icc_subset_Icc le_rfl hs.2)
    have hf : ContinuousOn f (Icc a s) := by
      dsimp [f]
      exact ((hPc.sub continuousOn_const).norm).neg
    have hρmem : -ρ ∈ Icc (f a) (f s) := by
      constructor <;> dsimp [f] <;> linarith
    obtain ⟨t, ht, hteq⟩ := intermediate_value_Icc hs.1 hf hρmem
    have hdist : dist (P t) z = ρ := by
      dsimp [f] at hteq
      linarith
    have hts : t < s := by
      by_contra hnot
      have hst : s ≤ t := le_of_not_gt hnot
      have htsame : t = s := le_antisymm ht.2 hst
      subst t
      linarith
    have hball : P t ∈ Metric.closedBall z ρ := by
      rw [Metric.mem_closedBall]
      calc
        dist (P t) z = ρ := hdist
        _ ≤ ρ := le_rfl
    exact False.elim ((hfirst.2 t ⟨ht.1, hts⟩) hball)
  · exact heq

/-- The last hit of a closed Euclidean ball is on its boundary if the curve ends outside. -/
theorem d4_last_closedBall_hit_boundary {P : ℝ → Rd d} {a b s : ℝ} {z : Rd d} {ρ : ℝ}
    (hP : ContinuousOn P (Icc a b)) (hs : s ∈ Icc a b)
    (hlast : P s ∈ Metric.closedBall z ρ ∧
      ∀ t ∈ Ioc s b, P t ∉ Metric.closedBall z ρ)
    (hend : ρ < dist (P b) z) : dist (P s) z = ρ := by
  have hsle : dist (P s) z ≤ ρ := by
    simpa only [Metric.mem_closedBall, dist_comm] using hlast.1
  rcases lt_or_eq_of_le hsle with hstrict | heq
  · let f : ℝ → ℝ := fun t => dist (P t) z
    have hPc : ContinuousOn P (Icc s b) :=
      hP.mono (Icc_subset_Icc hs.1 le_rfl)
    have hf : ContinuousOn f (Icc s b) := by
      dsimp [f]
      change ContinuousOn (fun t => ‖P t - z‖) (Icc s b)
      exact (hPc.sub continuousOn_const).norm
    have hρmem : ρ ∈ Icc (f s) (f b) := by
      constructor <;> dsimp [f] <;> linarith
    obtain ⟨t, ht, hteq⟩ := intermediate_value_Icc hs.2 hf hρmem
    have hts : s < t := by
      by_contra hnot
      have hts : t ≤ s := le_of_not_gt hnot
      have htsame : t = s := le_antisymm hts ht.1
      subst t
      dsimp [f] at hteq
      linarith
    have hdist : dist (P t) z = ρ := hteq
    have hball : P t ∈ Metric.closedBall z ρ := by
      rw [Metric.mem_closedBall]
      calc
        dist (P t) z = ρ := hdist
        _ ≤ ρ := le_rfl
    exact False.elim ((hlast.2 t ⟨hts, ht.2⟩) hball)
  · exact heq

/-- The corrected endpoint separation times in Step 1 of Proposition 4.1.

`Ty` is the first hit of the closed ball about `y`; `t₀` is the last hit of the closed ball about
`x` before `Ty`. When the endpoint balls are disjoint, both are attained boundary hits and
`t₀ < Ty`.
-/
theorem d4_endpoint_separation_times {P : ℝ → Rd d} {T ρ : ℝ} {x y : Rd d}
    (hT : 0 ≤ T) (hP : ContinuousOn P (Icc 0 T)) (hP0 : P 0 = x) (hPT : P T = y)
    (hρ : 0 < ρ) (hxy : 2 * ρ < dist x y) :
    ∃ t₀ Ty : ℝ, t₀ ∈ Icc 0 T ∧ Ty ∈ Icc 0 T ∧ 0 < t₀ ∧ t₀ < Ty ∧
      dist (P t₀) x = ρ ∧ dist (P Ty) y = ρ ∧
      (∀ t ∈ Ico 0 Ty, P t ∉ Metric.closedBall y ρ) ∧
      (∀ t ∈ Ioc t₀ Ty, P t ∉ Metric.closedBall x ρ) := by
  have hYhit : ∃ t ∈ Icc 0 T, P t ∈ Metric.closedBall y ρ := by
    refine ⟨T, ⟨by linarith, le_rfl⟩, ?_⟩
    rw [hPT, Metric.mem_closedBall, dist_self]
    exact hρ.le
  obtain ⟨Ty, hTy, hTyball, hTyfirst⟩ :=
    d4_exists_first_hit_closed hP Metric.isClosed_closedBall hYhit
  have hTyboundary : dist (P Ty) y = ρ :=
    d4_first_closedBall_hit_boundary hP hTy ⟨hTyball, hTyfirst⟩ (by rw [hP0]; linarith)
  have hXhit : ∃ t ∈ Icc 0 Ty, P t ∈ Metric.closedBall x ρ := by
    refine ⟨0, ⟨le_rfl, hTy.1⟩, ?_⟩
    rw [hP0, Metric.mem_closedBall, dist_self]
    exact hρ.le
  have hPty : ContinuousOn P (Icc 0 Ty) := hP.mono (Icc_subset_Icc le_rfl hTy.2)
  obtain ⟨t₀, ht₀, ht₀ball, ht₀last⟩ :=
    d4_exists_last_hit_closed hPty Metric.isClosed_closedBall hXhit
  have hTyOutside : P Ty ∉ Metric.closedBall x ρ := by
    intro hmem
    have hxmem : dist (P Ty) x ≤ ρ := by
      simpa only [Metric.mem_closedBall, dist_comm] using hmem
    have hymem : dist (P Ty) y ≤ ρ := by
      simpa only [Metric.mem_closedBall, dist_comm] using hTyball
    have htriangle : dist x y ≤ dist x (P Ty) + dist (P Ty) y := dist_triangle x (P Ty) y
    have hxmem' : dist x (P Ty) ≤ ρ := by simpa only [dist_comm] using hxmem
    linarith
  have ht₀lt : t₀ < Ty := by
    by_contra hnot
    have hle : Ty ≤ t₀ := le_of_not_gt hnot
    have heq : t₀ = Ty := le_antisymm ht₀.2 hle
    subst t₀
    exact hTyOutside ht₀ball
  have hTyOutsideDist : ρ < dist (P Ty) x := by
    simpa only [Metric.mem_closedBall, not_le, dist_comm] using hTyOutside
  have ht₀boundary : dist (P t₀) x = ρ :=
    d4_last_closedBall_hit_boundary hPty ht₀ ⟨ht₀ball, ht₀last⟩ hTyOutsideDist
  have ht₀pos : 0 < t₀ := by
    by_contra hnot
    have hle : t₀ ≤ 0 := le_of_not_gt hnot
    have heq : t₀ = 0 := le_antisymm hle ht₀.1
    rw [heq, hP0, dist_self] at ht₀boundary
    linarith
  have ht₀T : t₀ ∈ Icc 0 T := ⟨ht₀.1, ht₀.2.trans hTy.2⟩
  exact ⟨t₀, Ty, ht₀T, hTy, ht₀pos, ht₀lt, ht₀boundary, hTyboundary, hTyfirst, ht₀last⟩

/-- The first outer-sphere hit and last inner-sphere hit of one annulus crossing.

The returned segment lies in the closed annulus. The outer stopping time uses the first hit of
the closed complement of the open outer ball, so it is attained and lies on the sphere.
-/
theorem d4_annulus_crossing_times {P : ℝ → Rd d} {a b r : ℝ} {z : Rd d}
    (hab : a ≤ b) (hP : ContinuousOn P (Icc a b)) (hr : 0 < r)
    (hstart : dist (P a) z < 3 * r / 4) (hend : r < dist (P b) z) :
    ∃ s t : ℝ, a ≤ s ∧ s ≤ t ∧ t ≤ b ∧
      dist (P s) z = 3 * r / 4 ∧ dist (P t) z = r ∧
      (∀ u ∈ Ico a t, dist (P u) z < r) ∧
      MapsTo P (Icc s t) (d4F z r) := by
  let K : Set (Rd d) := (Metric.ball z r)ᶜ
  have hK : IsClosed K := Metric.isOpen_ball.isClosed_compl
  have hne : ∃ t ∈ Icc a b, P t ∈ K := by
    refine ⟨b, ⟨hab, le_rfl⟩, ?_⟩
    have hbnot : P b ∉ Metric.ball z r := by
      intro hbball
      have hb' : dist (P b) z < r := by
        simpa only [Metric.mem_ball, dist_comm] using hbball
      linarith
    simpa [K] using hbnot
  obtain ⟨t, ht, htK, hfirst⟩ := d4_exists_first_hit_closed hP hK hne
  have htLower : r ≤ dist (P t) z := by
    have hnot : ¬ dist (P t) z < r := by
      intro hlt
      have hball : P t ∈ Metric.ball z r := by
        simpa only [Metric.mem_ball, dist_comm] using hlt
      exact htK (by simpa [K] using hball)
    exact le_of_not_gt hnot
  have htSphere : dist (P t) z = r := by
    rcases lt_or_eq_of_le htLower with hgt | heq
    · have hcont : ContinuousOn (fun u : ℝ => dist (P u) z) (Icc a t) := by
        have hPc : ContinuousOn P (Icc a t) := hP.mono (Icc_subset_Icc le_rfl ht.2)
        change ContinuousOn (fun u => ‖P u - z‖) (Icc a t)
        exact (hPc.sub continuousOn_const).norm
      have hρmem : r ∈ Icc (dist (P a) z) (dist (P t) z) := ⟨by linarith [hstart, hr], hgt.le⟩
      obtain ⟨u, hu, huval⟩ := intermediate_value_Icc ht.1 hcont hρmem
      have hut : u < t := by
        by_contra hnot
        have htu : t ≤ u := le_of_not_gt hnot
        have huEq : u = t := le_antisymm hu.2 htu
        subst u
        linarith
      have huK : P u ∈ K := by
        change P u ∉ Metric.ball z r
        intro hball
        have hdistlt : dist (P u) z < r := by
          simpa only [Metric.mem_ball, dist_comm] using hball
        linarith
      exact False.elim (hfirst u ⟨hu.1, hut⟩ huK)
    · exact heq.symm
  have hPc : ContinuousOn P (Icc a t) := hP.mono (Icc_subset_Icc le_rfl ht.2)
  have hinner : ∃ u ∈ Icc a t, P u ∈ Metric.closedBall z (3 * r / 4) := by
    refine ⟨a, ⟨le_rfl, ht.1⟩, ?_⟩
    simpa only [Metric.mem_closedBall, dist_comm] using hstart.le
  obtain ⟨s, hs, hsball, hslast⟩ :=
    d4_exists_last_hit_closed hPc Metric.isClosed_closedBall hinner
  have hsSphere : dist (P s) z = 3 * r / 4 :=
    d4_last_closedBall_hit_boundary hPc hs ⟨hsball, hslast⟩ (by rw [htSphere]; linarith)
  have hsegment : MapsTo P (Icc s t) (d4F z r) := by
    intro u hu
    change 3 * r / 4 ≤ ‖P u - z‖ ∧ ‖P u - z‖ ≤ r
    constructor
    · by_cases hus : u = s
      · subst u
        rw [← dist_eq_norm, hsSphere]
      · have hsu : s < u := by
          rcases lt_or_eq_of_le hu.1 with hlt | heq
          · exact hlt
          · exact False.elim (hus heq.symm)
        have hnotball := hslast u ⟨hsu, hu.2⟩
        have hlow : 3 * r / 4 < dist (P u) z := by
          simpa only [Metric.mem_closedBall, dist_comm, not_le] using hnotball
        rw [← dist_eq_norm]
        exact hlow.le
    · by_cases hut : u = t
      · subst u
        rw [← dist_eq_norm, htSphere]
      · have hut' : u < t := by
          rcases lt_or_eq_of_le hu.2 with hlt | heq
          · exact hlt
          · exact False.elim (hut heq)
        have hnotK := hfirst u ⟨(hs.1.trans hu.1), hut'⟩
        have hball : P u ∈ Metric.ball z r := by simpa [K] using hnotK
        have hhigh : dist (P u) z < r := by
          simpa only [Metric.mem_ball, dist_comm] using hball
        rw [← dist_eq_norm]
        exact hhigh.le
  have hbefore : ∀ u ∈ Ico a t, dist (P u) z < r := by
    intro u hu
    have hnotK := hfirst u ⟨hu.1, hu.2⟩
    have hball : P u ∈ Metric.ball z r := by simpa [K] using hnotK
    simpa only [Metric.mem_ball, dist_comm] using hball
  exact ⟨s, t, hs.1, hs.2, ht.2, hsSphere, htSphere, hbefore, hsegment⟩

/-- One greedy step of Proposition 4.1: a mesh point near the current path location has a good
radius whose first outer hit gives a crossing contained in the closed good annulus. -/
theorem d4_good_crossing_exists {D M : ContMetric d} {R rmin rmax η A b : ℝ}
    {mesh : Finset (Rd d)} {radii : Finset ℝ} {c : ℝ → ℝ}
    {P : ℝ → Rd d} {T a : ℝ} {y : Rd d}
    (hcover : d4CoveringHalf D M R rmin rmax η A b mesh radii c)
    (hscale : 0 < rmin) (hrange : rmin ≤ rmax)
    (hP : ContinuousOn P (Icc 0 T))
    (hpath : MapsTo P (Icc 0 T) (Metric.ball 0 R)) (hPT : P T = y)
    (ha : 0 ≤ a) (haT : a ≤ T)
    (houtside : 2 * rmax ≤ dist (P a) y) :
    ∃ z ∈ mesh, z ∈ Metric.ball 0 (R + 1) ∧
      dist z 0 < R + rmin / 100 ∧ ∃ r ∈ radii, ∃ s t : ℝ,
      dist (P a) z ≤ rmin / 100 ∧ rmin ≤ r ∧ r ≤ rmax ∧
      d4GoodHalf D M z r (c r) η A b ∧
      a ≤ s ∧ s ≤ t ∧ t ≤ T ∧ s < t ∧
      dist (P s) z = 3 * r / 4 ∧ dist (P t) z = r ∧
      rmin / 2 ≤ dist (P a) (P t) ∧
      (∀ u ∈ Ico a t, dist (P u) z < r) ∧
      MapsTo P (Icc s t) (d4F z r) := by
  have haIcc : a ∈ Icc 0 T := ⟨ha, haT⟩
  have hPa : P a ∈ Metric.ball 0 R := hpath haIcc
  obtain ⟨z, hzmesh, hzclose⟩ := hcover.1 (P a) hPa
  have hzR1 := hcover.2.1 z hzmesh
  obtain ⟨r, hrset, hrmin, hrmax, hgood⟩ := hcover.2.2 z hzmesh
  have hPaR : dist (P a) 0 < R := by
    simpa only [Metric.mem_ball, dist_comm] using hPa
  have hzcenter : dist z 0 < R + rmin / 100 := by
    have htri := dist_triangle z (P a) 0
    have hcomm : dist z (P a) = dist (P a) z := dist_comm _ _
    rw [hcomm] at htri
    nlinarith [htri, hzclose, hPaR]
  rcases hgood with ⟨hr, hc, hη, hA, hb, hcmp₁, hdiamD, hshort₁⟩
  have hclose : dist (P a) z ≤ r / 100 := by
    nlinarith [hzclose, hrmin]
  have hstart : dist (P a) z < 3 * r / 4 := by
    nlinarith [hclose, hr]
  have htriangle := dist_triangle (P a) z y
  have houter : r < dist y z := by
    have hgap : r < 2 * rmax - rmin / 100 := by
      nlinarith [hscale, hrange]
    have hlow : 2 * rmax - rmin / 100 ≤ dist y z := by
      have hcomm : dist z y = dist y z := dist_comm _ _
      rw [← hcomm]
      nlinarith [htriangle, houtside, hzclose]
    exact hgap.trans_le hlow
  have hPsub : ContinuousOn P (Icc a T) :=
    hP.mono (Icc_subset_Icc ha le_rfl)
  obtain ⟨s, t, hast, hst, htT, hsphere, htsphere, hbefore, hF⟩ :=
    d4_annulus_crossing_times haT hPsub hr hstart (by rw [hPT]; exact houter)
  have hststrict : s < t := by
    by_contra hnot
    have hts : t ≤ s := le_of_not_gt hnot
    have heq : s = t := le_antisymm hst hts
    subst t
    linarith [hsphere, htsphere]
  have hdisplace : rmin / 2 ≤ dist (P a) (P t) := by
    have htri := dist_triangle z (P a) (P t)
    have hrad : dist z (P t) = r := by simpa only [dist_comm] using htsphere
    have hnear : dist z (P a) ≤ r / 100 := by simpa only [dist_comm] using hclose
    rw [hrad] at htri
    nlinarith [htri, hnear, hrmin, hr]
  exact ⟨z, hzmesh, hzR1, hzcenter, r, hrset, s, t, hzclose, hrmin, hrmax,
    ⟨hr, hc, hη, hA, hb, hcmp₁, hdiamD, hshort₁⟩, hast, hst, htT, hststrict,
    hsphere, htsphere, hdisplace, hbefore, hF⟩

/-- The witness data for one greedy annulus step, bundled for recursive selection. -/
structure D4CrossingData {D M : ContMetric d} {R rmin rmax η A b : ℝ}
    {mesh : Finset (Rd d)} {radii : Finset ℝ} {c : ℝ → ℝ}
    {P : ℝ → Rd d} {T a : ℝ} where
  z : Rd d
  hz : z ∈ mesh
  hzR1 : z ∈ Metric.ball 0 (R + 1)
  hzcenter : dist z 0 < R + rmin / 100
  r : ℝ
  hr : r ∈ radii
  hnear : dist (P a) z ≤ rmin / 100
  hrmin : rmin ≤ r
  hrmax : r ≤ rmax
  hgood : d4GoodHalf D M z r (c r) η A b
  s : ℝ
  t : ℝ
  hast : a ≤ s
  hst : s ≤ t
  htT : t ≤ T
  hststrict : s < t
  hsphere : dist (P s) z = 3 * r / 4
  htsphere : dist (P t) z = r
  hdisplace : rmin / 2 ≤ dist (P a) (P t)
  hbefore : ∀ u ∈ Ico a t, dist (P u) z < r
  hF : MapsTo P (Icc s t) (d4F z r)

/-- Bundle the one-step existence theorem as a nonempty type for use in a chosen recursion. -/
theorem d4_good_crossing_nonempty {D M : ContMetric d} {R rmin rmax η A b : ℝ}
    {mesh : Finset (Rd d)} {radii : Finset ℝ} {c : ℝ → ℝ}
    {P : ℝ → Rd d} {T a : ℝ} {y : Rd d}
    (hcover : d4CoveringHalf D M R rmin rmax η A b mesh radii c)
    (hscale : 0 < rmin) (hrange : rmin ≤ rmax)
    (hP : ContinuousOn P (Icc 0 T))
    (hpath : MapsTo P (Icc 0 T) (Metric.ball 0 R)) (hPT : P T = y)
    (ha : 0 ≤ a) (haT : a ≤ T)
    (houtside : 2 * rmax ≤ dist (P a) y) :
    Nonempty (D4CrossingData (D := D) (M := M) (R := R) (rmin := rmin)
      (rmax := rmax) (η := η) (A := A) (b := b) (mesh := mesh) (radii := radii)
      (c := c) (P := P) (T := T) (a := a)) := by
  obtain ⟨z, hz, hzR1, hzcenter, r, hr, s, t, hnear, hrmin, hrmax, hgood, hast, hst, htT,
      hststrict, hsphere, htsphere, hdisplace, hbefore, hF⟩ :=
    d4_good_crossing_exists hcover hscale hrange hP hpath hPT ha haT houtside
  exact ⟨⟨z, hz, hzR1, hzcenter, r, hr, hnear, hrmin, hrmax, hgood, s, t, hast, hst, htT,
    hststrict, hsphere, htsphere, hdisplace, hbefore, hF⟩⟩

/-- If each step of a bounded-time greedy construction advances by a fixed positive amount,
the construction must reach the stopping time in finitely many steps. -/
theorem d4_finite_stop_of_uniform_increment {t₀ T δ : ℝ} {t : ℕ → ℝ}
    (hδ : 0 < δ) (hinit : t 0 = t₀)
    (hstep : ∀ n, t n < T → t n + δ ≤ t (n + 1)) :
    ∃ n, T ≤ t n := by
  by_contra hstop
  push Not at hstop
  have hlinear : ∀ n : ℕ, t₀ + (n : ℝ) * δ ≤ t n := by
    intro n
    induction n with
    | zero => simp [hinit]
    | succ n ih =>
        rw [Nat.cast_succ]
        calc
          t₀ + ((n : ℝ) + 1) * δ = (t₀ + (n : ℝ) * δ) + δ := by ring
          _ ≤ t n + δ := add_le_add ih le_rfl
          _ ≤ t (n + 1) := hstep n (hstop n)
  obtain ⟨n, hn⟩ := exists_nat_gt ((T - t₀) / δ)
  have hn' : T - t₀ < (n : ℝ) * δ := (div_lt_iff₀ hδ).mp hn
  have htn : t n < T := hstop n
  have hlow := hlinear n
  nlinarith

/-- On a compact time interval, a fixed spatial displacement forces a uniform positive time
increment. This is the uniform-continuity input for termination of the greedy annulus sequence. -/
theorem d4_uniform_time_gap_of_displacement {P : ℝ → Rd d} {T ρ : ℝ}
    (hP : ContinuousOn P (Icc 0 T)) (hρ : 0 < ρ) :
    ∃ δ > 0, ∀ s ∈ Icc 0 T, ∀ t ∈ Icc 0 T,
      ρ ≤ dist (P s) (P t) → δ ≤ |t - s| := by
  have huc := isCompact_Icc.uniformContinuousOn_of_continuous hP
  obtain ⟨δ, hδ, hmod⟩ := Metric.uniformContinuousOn_iff.mp huc ρ hρ
  refine ⟨δ, hδ, ?_⟩
  intro s hs t ht hdist
  by_contra hnot
  have hsmall : dist s t < δ := by
    simpa only [Real.dist_eq, abs_sub_comm] using lt_of_not_ge hnot
  have himage := hmod s hs t ht hsmall
  exact (not_lt_of_ge hdist) himage

/-- Recursively choose good annulus crossings until the path first advances past `Ty`. The
uniform-continuity time gap and the abstract stopping lemma prove that this recursion stops after
finitely many steps. -/
theorem d4_greedy_sequence_reaches {D M : ContMetric d} {R rmin rmax η A b : ℝ}
    {mesh : Finset (Rd d)} {radii : Finset ℝ} {c : ℝ → ℝ}
    {P : ℝ → Rd d} {T t₀ Ty : ℝ} {y : Rd d}
    (hcover : d4CoveringHalf D M R rmin rmax η A b mesh radii c)
    (hscale : 0 < rmin) (hrange : rmin ≤ rmax)
    (hP : ContinuousOn P (Icc 0 T))
    (hpath : MapsTo P (Icc 0 T) (Metric.ball 0 R)) (hPT : P T = y)
    (ht₀ : 0 ≤ t₀) (ht₀T : t₀ ≤ T) (ht₀Ty : t₀ < Ty) (hTyT : Ty ≤ T)
    (hnohit : ∀ a ∈ Ico 0 Ty, P a ∉ Metric.closedBall y (2 * rmax)) :
    ∃ times : ℕ → ℝ,
      times 0 = t₀ ∧
      times 0 < Ty ∧
      (∀ n, 0 ≤ times n ∧ times n ≤ T) ∧
      (∃ N, Ty ≤ times N ∧ ∀ n < N, times n < Ty) ∧
      (∀ n, times n ≤ times (n + 1)) ∧
      (∀ n, times n < Ty →
        ∃ w : D4CrossingData (D := D) (M := M) (R := R) (rmin := rmin)
          (rmax := rmax) (η := η) (A := A) (b := b) (mesh := mesh)
          (radii := radii) (c := c) (P := P) (T := T) (a := times n),
          w.t = times (n + 1)) := by
  classical
  have hgap := d4_uniform_time_gap_of_displacement hP (by linarith : 0 < rmin / 2)
  obtain ⟨δ, hδ, hmod⟩ := hgap
  have houtside (a : ℝ) (ha : 0 ≤ a) (haTy : a < Ty) :
      2 * rmax ≤ dist (P a) y := by
    have hnot := hnohit a ⟨ha, haTy⟩
    by_contra hbad
    have hlt : dist (P a) y < 2 * rmax := lt_of_not_ge hbad
    have hmem : P a ∈ Metric.closedBall y (2 * rmax) := by
      rw [Metric.mem_closedBall]
      exact le_of_lt hlt
    exact hnot hmem
  let chooseStep : ∀ a : ℝ, 0 ≤ a → a < Ty →
      D4CrossingData (D := D) (M := M) (R := R) (rmin := rmin)
        (rmax := rmax) (η := η) (A := A) (b := b) (mesh := mesh)
        (radii := radii) (c := c) (P := P) (T := T) (a := a) :=
    fun a ha haTy => Classical.choice (d4_good_crossing_nonempty
      (D := D) (M := M) (R := R) (rmin := rmin) (rmax := rmax)
      (η := η) (A := A) (b := b) (mesh := mesh) (radii := radii) (c := c)
      (P := P) (T := T) (a := a) (y := y) hcover hscale hrange hP hpath hPT
      ha (le_trans (le_of_lt haTy) hTyT) (houtside a ha haTy))
  let next := fun (a : ℝ) =>
    if hcur : 0 ≤ a ∧ a < Ty then (chooseStep a hcur.1 hcur.2).t else a
  let times : ℕ → ℝ := Nat.rec t₀ (fun _ a => next a)
  have htimes0 : times 0 = t₀ := by simp [times]
  have htimes_succ (n : ℕ) : times (n + 1) = next (times n) := by simp [times]
  have hstate : ∀ n, 0 ≤ times n ∧ times n ≤ T := by
    intro n
    induction n with
    | zero => exact ⟨ht₀, ht₀T⟩
    | succ n ih =>
        rw [htimes_succ]
        haveI : Decidable (0 ≤ times n ∧ times n < Ty) :=
          Classical.propDecidable (0 ≤ times n ∧ times n < Ty)
        by_cases hcur : 0 ≤ times n ∧ times n < Ty
        · simp only [next, dite_eq_left hcur]
          let w := chooseStep (times n) hcur.1 hcur.2
          exact ⟨le_trans ih.1 (le_trans w.hast w.hst), w.htT⟩
        · simp only [next, dite_eq_right hcur]
          exact ih
  have hmono : ∀ n, times n ≤ times (n + 1) := by
    intro n
    rw [htimes_succ]
    haveI : Decidable (0 ≤ times n ∧ times n < Ty) :=
      Classical.propDecidable (0 ≤ times n ∧ times n < Ty)
    by_cases hcur : 0 ≤ times n ∧ times n < Ty
    · simp only [next, dite_eq_left hcur]
      let w := chooseStep (times n) hcur.1 hcur.2
      exact le_trans w.hast w.hst
    · simp only [next, dite_eq_right hcur]
      exact le_rfl
  have hstep : ∀ n, times n < Ty → times n + δ ≤ times (n + 1) := by
    intro n htn
    have hcur : 0 ≤ times n ∧ times n < Ty := ⟨(hstate n).1, htn⟩
    let w := chooseStep (times n) hcur.1 hcur.2
    have htime := hmod (times n) ⟨(hstate n).1, (hstate n).2⟩ w.t
      ⟨le_trans (le_trans (hstate n).1 w.hast) w.hst, w.htT⟩ w.hdisplace
    have htime' : δ ≤ w.t - times n := by
      rw [abs_of_nonneg (sub_nonneg.mpr (le_trans w.hast w.hst))] at htime
      exact htime
    calc
      times n + δ ≤ w.t := by linarith
      _ = times (n + 1) := by
        rw [htimes_succ]
        simp only [next, dite_eq_left hcur]
        rfl
  have hstop := d4_finite_stop_of_uniform_increment hδ htimes0 hstep
  have hdec : DecidablePred (fun n : ℕ => Ty ≤ times n) := fun n =>
    Classical.propDecidable (Ty ≤ times n)
  let N := @Nat.find (fun n : ℕ => Ty ≤ times n) hdec hstop
  have hNstop : Ty ≤ times N := by
    simpa [N] using @Nat.find_spec (fun n : ℕ => Ty ≤ times n) hdec hstop
  have hNbefore : ∀ n < N, times n < Ty := by
    intro n hn
    have hnot : ¬ Ty ≤ times n := @Nat.find_min
      (fun n : ℕ => Ty ≤ times n) hdec hstop n hn
    exact lt_of_not_ge hnot
  exact ⟨times, htimes0, ht₀Ty, hstate, ⟨N, hNstop, hNbefore⟩, hmono, by
    intro n hn
    have hcur : 0 ≤ times n ∧ times n < Ty := ⟨(hstate n).1, hn⟩
    refine ⟨chooseStep (times n) hcur.1 hcur.2, ?_⟩
    rw [htimes_succ]
    simp only [next, dite_eq_left hcur]⟩

end HigherDimLFPPAS.Improve

end
