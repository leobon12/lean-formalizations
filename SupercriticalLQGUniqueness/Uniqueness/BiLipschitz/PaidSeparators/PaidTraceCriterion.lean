import SupercriticalLQGUniqueness.Uniqueness.BiLipschitz.PaidSeparators.AcrossLocalization
import SupercriticalLQGUniqueness.Uniqueness.Toolkit.PlanarSeparation.PaidTraces
import LQGMetric.Metric.InternalOps




 





set_option autoImplicit false
noncomputable section

open Set Metric LQGMetric.MetricGeometry
open scoped ENNReal
namespace SupercriticalLQGUniqueness.Uniqueness.BiLipschitz.PaidSeparators

 
def sepAnn (x : ℂ) (r : ℝ) (hr : 0 < r) : EuclideanAnnulus :=
  ⟨(x, 2 * r, 3 * r), by linarith, by linarith⟩

 


def GoodScalar (D D' : LSCMetric) (A : ℝ) (x : ℂ) (r N : ℝ)
    (hr : 0 < r) : Prop :=
  0 < N ∧ ENNReal.ofReal (N / A) ≤ acrossDist D (eblAcrossAnn x r hr) ∧
    aroundDist D' (sepAnn x r hr) ≤ ENNReal.ofReal (A * N)

 


def GoodGridCover (D D' : LSCMetric) (A : ℝ) : Prop :=
  ∀ m : ℕ, ∃ n₀ : ℕ, ∀ n ≥ n₀,
    ∃ (k : ℕ) (x : Fin k → ℂ) (r N : Fin k → ℝ)
      (hr : ∀ i, 0 < r i),
      (∀ i, (10 : ℝ) ^ (-(2 * (n : ℤ))) ≤ r i ∧
        r i ≤ (10 : ℝ) ^ (-(n : ℤ))) ∧
      (∀ i, GoodScalar D D' A (x i) (r i) (N i) (hr i)) ∧
      ∀ y ∈ closedBall (0 : ℂ) m,
        ∃ i, dist y (x i) < r i / 2

 

theorem exists_paid_separator (D D' : LSCMetric) {A : ℝ} (hA : 1 ≤ A)
    (x : ℂ) {r N : ℝ} (hr : 0 < r)
    (hgood : GoodScalar D D' A x r N hr) :
    ∃ (P : ℝ → ℂ) (a b : ℝ), D'.IsCurve P a b ∧
      (∀ t ∈ Icc a b, P t ∈ (sepAnn x r hr).toSet) ∧
      Disconnects (P '' Icc a b) (sepAnn x r hr).innerBoundary
        (sepAnn x r hr).outerBoundary ∧
      D'.len P a b < ENNReal.ofReal (2 * A * N) := by
  have hAN : 0 < A * N := mul_pos (lt_of_lt_of_le zero_lt_one hA) hgood.1
  have hstrict : ENNReal.ofReal (A * N) < ENNReal.ofReal (2 * A * N) := by
    apply ENNReal.ofReal_lt_ofReal_iff'.mpr
    constructor
    · nlinarith
    · nlinarith
  have hlt : aroundDist D' (sepAnn x r hr) < ENNReal.ofReal (2 * A * N) :=
    hgood.2.2.trans_lt hstrict
  dsimp only [aroundDist] at hlt
  obtain ⟨P, hP⟩ := iInf_lt_iff.mp hlt
  obtain ⟨a, ha⟩ := iInf_lt_iff.mp hP
  obtain ⟨b, hb⟩ := iInf_lt_iff.mp ha
  obtain ⟨hcurve, hc⟩ := iInf_lt_iff.mp hb
  obtain ⟨hinside, hi⟩ := iInf_lt_iff.mp hc
  obtain ⟨hsep, hlen⟩ := iInf_lt_iff.mp hi
  exact ⟨P, a, b, hcurve, hinside, hsep, hlen⟩

 

theorem exists_paid_separator_geometry (D D' : LSCMetric) {A : ℝ}
    (hA : 1 ≤ A) (x : ℂ) {r N : ℝ} (hr : 0 < r)
    (hgood : GoodScalar D D' A x r N hr) :
    ∃ (P : ℝ → ℂ) (a b : ℝ),
      D'.IsCurve P a b ∧
      (∀ t ∈ Icc a b, P t ∈ (sepAnn x r hr).toSet) ∧
      D'.len P a b < ENNReal.ofReal (2 * A * N) ∧
      IsCompact (P '' Icc a b) ∧ IsConnected (P '' Icc a b) ∧
      closedBall x (2 * r) ⊆
        connectedComponentIn (P '' Icc a b)ᶜ x ∧
      connectedComponentIn (P '' Icc a b)ᶜ x ⊆ ball x (3 * r) := by
  obtain ⟨P, a, b, hcurve, hinside, hsep, hlen⟩ :=
    exists_paid_separator D D' hA x hr hgood
  have hball : P '' Icc a b ⊆ ball x (3 * r) := by
    rintro y ⟨t, ht, rfl⟩
    exact (Toolkit.PlanarSeparation.candidate_annulus_subset_radii (sepAnn x r hr) (hinside t ht)).2
  have hbounded : Bornology.IsBounded (P '' Icc a b) :=
    isBounded_ball.subset hball
  have hPc : ContinuousOn P (Icc a b) :=
    Toolkit.PlanarSeparation.LSCMetric.continuousOn_euclidean_of_bounded D' P hcurve hbounded
  have hcompact : IsCompact (P '' Icc a b) :=
    isCompact_Icc.image_of_continuousOn hPc
  have hconnected : IsConnected (P '' Icc a b) :=
    (isConnected_Icc hcurve.1).image P hPc
  have hAnn : P '' Icc a b ⊆
      {w | 2 * r < dist w x ∧ dist w x < 3 * r} := by
    rintro y ⟨t, ht, rfl⟩
    exact Toolkit.PlanarSeparation.candidate_annulus_subset_radii (sepAnn x r hr) (hinside t ht)
  have hcert : LQGMetric.Disconnects (P '' Icc a b)
      (sphere x (2 * r)) (sphere x (3 * r)) :=
    Toolkit.PlanarSeparation.candidate_disconnects_implies_path_hit hsep
  obtain ⟨hinner, houter⟩ :=
    Toolkit.PlanarSeparation.annular_component_bounds (by linarith : 0 < 2 * r)
      (by linarith : 2 * r < 3 * r) hcompact hAnn hcert
  exact ⟨P, a, b, hcurve, hinside, hlen, hcompact, hconnected, hinner, houter⟩

 

theorem finite_stage_separator_data (D D' : LSCMetric) {A : ℝ}
    (hA : 1 ≤ A) {k : ℕ} (x : Fin k → ℂ) (r N : Fin k → ℝ)
    (hr : ∀ i, 0 < r i)
    (hgood : ∀ i, GoodScalar D D' A (x i) (r i) (N i) (hr i)) :
    ∃ (Q : Fin k → ℝ → ℂ) (a b : Fin k → ℝ),
      ∀ i,
        D'.IsCurve (Q i) (a i) (b i) ∧
        (∀ t ∈ Icc (a i) (b i), Q i t ∈ (sepAnn (x i) (r i) (hr i)).toSet) ∧
        D'.len (Q i) (a i) (b i) < ENNReal.ofReal (2 * A * N i) ∧
        IsCompact (Q i '' Icc (a i) (b i)) ∧
        IsConnected (Q i '' Icc (a i) (b i)) ∧
        closedBall (x i) (2 * r i) ⊆
          connectedComponentIn (Q i '' Icc (a i) (b i))ᶜ (x i) ∧
        connectedComponentIn (Q i '' Icc (a i) (b i))ᶜ (x i) ⊆
          ball (x i) (3 * r i) := by
  have hex : ∀ i : Fin k, ∃ (P : ℝ → ℂ) (a b : ℝ),
      D'.IsCurve P a b ∧
      (∀ t ∈ Icc a b, P t ∈ (sepAnn (x i) (r i) (hr i)).toSet) ∧
      D'.len P a b < ENNReal.ofReal (2 * A * N i) ∧
      IsCompact (P '' Icc a b) ∧ IsConnected (P '' Icc a b) ∧
      closedBall (x i) (2 * r i) ⊆ connectedComponentIn (P '' Icc a b)ᶜ (x i) ∧
      connectedComponentIn (P '' Icc a b)ᶜ (x i) ⊆ ball (x i) (3 * r i) :=
    fun i => exists_paid_separator_geometry D D' hA (x i) (hr i) (hgood i)
  choose Q a b hdata using hex
  exact ⟨Q, a, b, hdata⟩

 

theorem finite_stage_min_cost {k : ℕ} (i₀ : Fin k) (N : Fin k → ℝ)
    {A : ℝ} (hA : 0 < A) (hN : ∀ i, 0 < N i) :
    ∃ η : ℝ, 0 < η ∧ ∀ i, η ≤ N i / A := by
  have hne : (Finset.univ : Finset (Fin k)).Nonempty :=
    ⟨i₀, Finset.mem_univ i₀⟩
  obtain ⟨i, -, hmin⟩ :=
    Finset.exists_min_image (Finset.univ : Finset (Fin k))
      (fun j => N j / A) hne
  exact ⟨N i / A, div_pos (hN i) hA, fun j => hmin j (Finset.mem_univ j)⟩

 

theorem paid_crossing_le_length (D : LSCMetric)
    (hB : BiLipschitz.Barrier.Barrier D) (hL : D.IsLengthSpace)
    (x : ℂ) {r : ℝ} (hr : 0 < r) {P : ℝ → ℂ} {s t : ℝ}
    (hcurve : D.IsCurve P s t)
    (hstart : ‖P s - x‖ ≤ r) (hend : 2 * r ≤ ‖P t - x‖) :
    acrossDist D (eblAcrossAnn x r hr) ≤ D.len P s t := by
  have hxy : acrossDist D (eblAcrossAnn x r hr) ≤ D (P s, P t) := by
    rw [BiLipschitz.Barrier.acrossDist_eq_iInf_internal D hB hL (eblAcrossAnn x r hr)
      (Y := Set.univ) (Set.subset_univ _)]
    exact BiLipschitz.Barrier.iInf_internal_le D hB hL (by linarith : r ≤ 2 * r)
      (Set.subset_univ _) hstart hend
  exact hxy.trans (by
    change edist (D.pt (P s)) (D.pt (P t)) ≤
      LQGMetric.MetricGeometry.curveLength (D.pt ∘ P) s t
    exact LQGMetric.MetricGeometry.edist_le_curveLength (D.pt ∘ P) hcurve.1)

 

theorem paid_separator_funded (D D' : LSCMetric)
    (hB : BiLipschitz.Barrier.Barrier D) (hL : D.IsLengthSpace)
    {A : ℝ} (hA : 1 ≤ A) (x : ℂ) {r N : ℝ} (hr : 0 < r)
    (hgood : GoodScalar D D' A x r N hr)
    {P Q : ℝ → ℂ} {s t a b : ℝ}
    (hcurve : D.IsCurve P s t)
    (hstart : ‖P s - x‖ ≤ r)
    (hhit : P t ∈ Q '' Icc a b)
    (hQinside : ∀ u ∈ Icc a b, Q u ∈ (sepAnn x r hr).toSet)
    (hlen : D'.len Q a b < ENNReal.ofReal (2 * A * N)) :
    D'.len Q a b < ENNReal.ofReal (2 * A ^ 2) * D.len P s t := by
  have hhitRad : 2 * r ≤ ‖P t - x‖ := by
    obtain ⟨u, hu, hPu⟩ := hhit
    rw [← hPu]
    have hrad := Toolkit.PlanarSeparation.candidate_annulus_subset_radii (sepAnn x r hr) (hQinside u hu)
    have hrad' : 2 * r < ‖Q u - x‖ := by
      simpa only [sepAnn, EuclideanAnnulus.innerRadius, EuclideanAnnulus.center,
        dist_eq_norm] using hrad.1
    exact hrad'.le
  have hcross := paid_crossing_le_length D hB hL x hr hcurve hstart hhitRad
  have hN : ENNReal.ofReal (N / A) ≤ D.len P s t := hgood.2.1.trans hcross
  have hAp : 0 < A := lt_of_lt_of_le zero_lt_one hA
  have hmul : (2 * A ^ 2) * (N / A) = 2 * A * N := by
    field_simp
  calc
    D'.len Q a b < ENNReal.ofReal (2 * A * N) := hlen
    _ = ENNReal.ofReal (2 * A ^ 2) * ENNReal.ofReal (N / A) := by
      rw [← ENNReal.ofReal_mul (by positivity : 0 ≤ 2 * A ^ 2), hmul]
    _ ≤ ENNReal.ofReal (2 * A ^ 2) * D.len P s t := by
      gcongr

 

theorem first_hit_stays_component {K : Set ℂ} (hK : IsClosed K)
    {P : ℝ → ℂ} {s T : ℝ} (hPc : ContinuousOn P (Icc s T))
    (hsT : s ≤ T) (hstart : P s ∉ K)
    (hhit : ∃ u ∈ Icc s T, P u ∈ K) :
    ∃ t ∈ Icc s T, s < t ∧ P t ∈ K ∧
      ∀ u ∈ Ico s t, P u ∈ connectedComponentIn Kᶜ (P s) := by
  obtain ⟨t, ht, htK, hbefore⟩ :=
    LQGMetric.MetricGeometry.exists_first_hit hPc hK hhit
  have hst : s < t := lt_of_le_of_ne ht.1 (by
    intro heq
    have : P s ∈ K := heq ▸ htK
    exact hstart this)
  refine ⟨t, ht, hst, htK, ?_⟩
  intro u hu
  have huT : u ∈ Icc s T := ⟨hu.1, hu.2.le.trans ht.2⟩
  have hsub : Icc s u ⊆ Icc s T := Icc_subset_Icc le_rfl huT.2
  have havoid : P '' Icc s u ⊆ Kᶜ := by
    rintro y ⟨v, hv, rfl⟩
    exact hbefore v ⟨hv.1, hv.2.trans_lt hu.2⟩
  have hconn : IsPreconnected (P '' Icc s u) :=
    (isPreconnected_Icc).image P (hPc.mono hsub)
  have hcomponent : P '' Icc s u ⊆ connectedComponentIn Kᶜ (P s) :=
    hconn.subset_connectedComponentIn
      ⟨s, left_mem_Icc.2 hu.1, rfl⟩ havoid
  exact hcomponent ⟨u, right_mem_Icc.2 hu.1, rfl⟩

 

theorem no_hit_stays_component {K : Set ℂ}
    {P : ℝ → ℂ} {s T : ℝ} (hPc : ContinuousOn P (Icc s T))
    (hsT : s ≤ T)
    (havoid : ∀ u ∈ Icc s T, P u ∉ K) :
    ∀ u ∈ Icc s T, P u ∈ connectedComponentIn Kᶜ (P s) := by
  have htrace : P '' Icc s T ⊆ Kᶜ := by
    rintro y ⟨u, hu, rfl⟩
    exact havoid u hu
  have hconn : IsPreconnected (P '' Icc s T) :=
    (isPreconnected_Icc).image P hPc
  have hcomponent : P '' Icc s T ⊆ connectedComponentIn Kᶜ (P s) :=
    hconn.subset_connectedComponentIn
      ⟨s, left_mem_Icc.2 hsT, rfl⟩ htrace
  intro u hu
  exact hcomponent ⟨u, hu, rfl⟩

 

theorem no_infinite_paid_steps (D : LSCMetric) {P : ℝ → ℂ}
    {T η : ℝ} (hη : 0 < η) (hT : 0 ≤ T)
    (hfin : D.len P 0 T ≠ ∞) (S : ℕ → ℝ)
    (hS0 : S 0 = 0) (hSI : ∀ n, S n ∈ Icc (0 : ℝ) T)
    (hstep : ∀ n, S n ≤ S (n + 1))
    (hcost : ∀ n, ENNReal.ofReal η ≤ D.len P (S n) (S (n + 1))) : False := by
  have hlinear : ∀ n : ℕ,
      ENNReal.ofReal ((n : ℝ) * η) ≤ D.len P 0 (S n) := by
    intro n
    induction n with
    | zero =>
        simpa [hS0, LSCMetric.len] using
          (show (0 : ℝ≥0∞) ≤ D.len P 0 0 from bot_le)
    | succ n ih =>
        have hn : 0 ≤ (n : ℝ) * η := mul_nonneg (Nat.cast_nonneg _) hη.le
        have hrec : ((↑(n + 1) : ℝ) * η) = (n : ℝ) * η + η := by
          push_cast
          ring
        rw [hrec, ENNReal.ofReal_add hn hη.le]
        calc
          ENNReal.ofReal ((n : ℝ) * η) + ENNReal.ofReal η
              ≤ D.len P 0 (S n) + D.len P (S n) (S (n + 1)) :=
                add_le_add ih (hcost n)
          _ = D.len P 0 (S (n + 1)) := by
            exact LQGMetric.MetricGeometry.curveLength_add (D.pt ∘ P)
              (hSI n).1 (hstep n)
  obtain ⟨n, hn⟩ := exists_nat_gt ((D.len P 0 T).toReal / η)
  have hnt : (D.len P 0 T).toReal < (n : ℝ) * η := by
    rwa [div_lt_iff₀ hη] at hn
  have hbound : D.len P 0 (S n) ≤ D.len P 0 T :=
    LQGMetric.MetricGeometry.curveLength_mono (D.pt ∘ P) le_rfl (hSI n).2
  have hcast := ENNReal.toReal_mono hfin ((hlinear n).trans hbound)
  rw [ENNReal.toReal_ofReal (mul_nonneg (Nat.cast_nonneg _) hη.le)] at hcast
  exact (not_lt_of_ge hcast) hnt

 

theorem component_pair_close {V : Set ℂ} {x z w : ℂ} {r ε : ℝ}
    (hr : 0 < r) (hrε : r ≤ ε)
    (hV : V ⊆ ball x (3 * r)) (hz : z ∈ V) (hw : w ∈ V) :
    dist z w < 6 * ε := by
  have hz' : dist z x < 3 * r := hV hz
  have hw' : dist w x < 3 * r := hV hw
  calc
    dist z w ≤ dist z x + dist x w := dist_triangle z x w
    _ < 6 * ε := by
      rw [dist_comm x w]
      linarith

 

theorem exists_trace_near_component {K V : Set ℂ} {x z : ℂ}
    {r ε : ℝ} (hr : 0 < r) (hrε : r ≤ ε)
    (hKne : K.Nonempty) (hK : K ⊆ ball x (3 * r))
    (hV : V ⊆ ball x (3 * r)) (hz : z ∈ closure V) :
    ∃ q ∈ K, dist z q < 7 * ε := by
  obtain ⟨q, hq⟩ := hKne
  have hz' : dist z x ≤ 3 * r := by
    have hclosed : closure V ⊆ closedBall x (3 * r) :=
      closure_minimal (hV.trans ball_subset_closedBall) isClosed_closedBall
    exact hclosed hz
  have hq' : dist q x < 3 * r := hK hq
  refine ⟨q, hq, ?_⟩
  calc
    dist z q ≤ dist z x + dist x q := dist_triangle z x q
    _ < 7 * ε := by
      rw [dist_comm x q]
      linarith

 

theorem exists_trace_near_terminal {K V Vlast : Set ℂ} {x xlast p w : ℂ}
    {r rlast ε : ℝ} (hr : 0 < r) (hrlast : 0 < rlast)
    (hrε : r ≤ ε) (hrlastε : rlast ≤ ε)
    (hKne : K.Nonempty) (hK : K ⊆ ball x (3 * r))
    (hV : V ⊆ ball x (3 * r)) (hp : p ∈ closure V)
    (hVlast : Vlast ⊆ ball xlast (3 * rlast))
    (hpLast : p ∈ Vlast) (hwLast : w ∈ Vlast) :
    ∃ q ∈ K, dist w q < 13 * ε := by
  obtain ⟨q, hq, hpq⟩ :=
    exists_trace_near_component hr hrε hKne hK hV hp
  have hpw : dist p w < 6 * ε :=
    component_pair_close hrlast hrlastε hVlast hpLast hwLast
  refine ⟨q, hq, ?_⟩
  calc
    dist w q ≤ dist w p + dist p q := dist_triangle w p q
    _ < 13 * ε := by rw [dist_comm w p]; linarith


end SupercriticalLQGUniqueness.Uniqueness.BiLipschitz.PaidSeparators
