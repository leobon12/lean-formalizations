import SupercriticalLQGUniqueness.Uniqueness.Toolkit.PlanarSeparation.Components
import LQGMetric.Metric.Geodesic
import Mathlib.Topology.MetricSpace.CoveringNumbers




 
set_option autoImplicit false
noncomputable section
open Set Metric LQGMetric.MetricGeometry
open scoped ENNReal
namespace SupercriticalLQGUniqueness.Uniqueness.Toolkit.PlanarSeparation

 
theorem trace_dist_le_len (D : LSCMetric) (P : ℝ → ℂ) {a b : ℝ}
    {x y : ℂ} (hx : x ∈ P '' Icc a b) (hy : y ∈ P '' Icc a b) :
    D (x, y) ≤ D.len P a b := by
  obtain ⟨s, hs, rfl⟩ := hx
  obtain ⟨t, ht, rfl⟩ := hy
  rcases le_total s t with hst | hts
  · change edist (D.pt (P s)) (D.pt (P t)) ≤
      curveLength (D.pt ∘ P) a b
    exact (edist_le_curveLength (D.pt ∘ P) hst).trans
      (curveLength_mono (D.pt ∘ P) hs.1 ht.2)
  · change edist (D.pt (P s)) (D.pt (P t)) ≤
      curveLength (D.pt ∘ P) a b
    rw [edist_comm]
    exact (edist_le_curveLength (D.pt ∘ P) hts).trans
      (curveLength_mono (D.pt ∘ P) ht.1 hs.2)

 
theorem paidTrace_chain_core {ι : Type*} (D : LSCMetric)
    (K : ι → Set ℂ) (L : ι → ENNReal)
    (hcost : ∀ i x y, x ∈ K i → y ∈ K i → D (x, y) ≤ L i)
    (i : ι) (l : List ι) (j : ι)
    (hchain : (i :: l).IsChain fun u v => (K u ∩ K v).Nonempty)
    (hlast : (i :: l).getLast (List.cons_ne_nil i l) = j)
    {x y : ℂ} (hx : x ∈ K i) (hy : y ∈ K j) :
    D (x, y) ≤ ((i :: l).map L).sum := by
  induction l generalizing i x with
  | nil =>
      have hij : i = j := by simpa using hlast
      subst j
      simpa using hcost i x y hx hy
  | cons k tail ih =>
      have hik : (K i ∩ K k).Nonempty := (List.isChain_cons_cons.mp hchain).1
      obtain ⟨z, hzi, hzk⟩ := hik
      have htail : (k :: tail).IsChain fun u v => (K u ∩ K v).Nonempty :=
        (List.isChain_cons_cons.mp hchain).2
      have hlast' : (k :: tail).getLast (List.cons_ne_nil k tail) = j := by
        simpa using hlast
      calc
        D (x, y) ≤ D (x, z) + D (z, y) := D.isExtMetric.2.2.2 x z y
        _ ≤ L i + ((k :: tail).map L).sum :=
          add_le_add (hcost i x z hx hzi) (ih k htail hlast' hzk)
        _ = ((i :: k :: tail).map L).sum := by simp only [List.map_cons, List.sum_cons]

 

theorem paidTrace_chain {ι : Type*} [DecidableEq ι]
    (D : LSCMetric) (S₀ : Finset ι) (K : ι → Set ℂ)
    (P : ι → ℝ → ℂ) (a b : ι → ℝ) (c : ι → ℂ) (A : Set ℂ)
    (hAne : A.Nonempty) (hA : IsPreconnected A)
    (hcov : A ⊆ ⋃ i ∈ S₀, connectedComponentIn (K i)ᶜ (c i))
    (hcurve : ∀ i ∈ S₀, D.IsCurve (P i) (a i) (b i))
    (hEucl : ∀ i ∈ S₀, ContinuousOn (P i) (Icc (a i) (b i)))
    (htrace : ∀ i ∈ S₀, K i = P i '' Icc (a i) (b i))
    (_hfinite : ∀ i ∈ S₀, D.len (P i) (a i) (b i) < ∞)
    (hbounded : ∀ i ∈ S₀,
      Bornology.IsBounded (connectedComponentIn (K i)ᶜ (c i))) :
    ∃ S ⊆ S₀,
      A ⊆ (⋃ i ∈ S, connectedComponentIn (K i)ᶜ (c i)) ∧
      ∀ i j : {i // i ∈ S}, ∀ x ∈ K i.val, ∀ y ∈ K j.val,
        D (x, y) ≤ ∑ k ∈ S, D.len (P k) (a k) (b k) := by
  classical
  have hc : ∀ i ∈ S₀, IsCompact (K i) := by
    intro i hi
    rw [htrace i hi]
    exact isCompact_Icc.image_of_continuousOn (hEucl i hi)
  have hconn : ∀ i ∈ S₀, IsConnected (K i) := by
    intro i hi
    rw [htrace i hi]
    exact (isConnected_Icc (hcurve i hi).1).image (P i) (hEucl i hi)
  obtain ⟨S, hSS₀, hSA, _, _, hchains⟩ :=
    finiteObstacle_chain S₀ K c A hAne hA hcov hc hconn hbounded
  refine ⟨S, hSS₀, hSA, ?_⟩
  intro i j x hx y hy
  obtain ⟨l, hne, hfirst, hlast, hnodup, hchain⟩ := hchains i j
  cases l with
  | nil => exact False.elim (hne rfl)
  | cons u tail =>
      have hui : u = i := by simpa using hfirst
      subst u
      have hlast' : (i :: tail).getLast (List.cons_ne_nil i tail) = j := by
        simpa using hlast
      have hcost : ∀ q : {i // i ∈ S}, ∀ v w : ℂ,
          v ∈ K q.val → w ∈ K q.val →
            D (v, w) ≤ D.len (P q.val) (a q.val) (b q.val) := by
        intro q v w hv hw
        have hq : q.val ∈ S₀ := hSS₀ q.property
        rw [htrace q.val hq] at hv hw
        exact trace_dist_le_len D (P q.val) hv hw
      have hpaid := paidTrace_chain_core D (fun q : {i // i ∈ S} => K q.val)
        (fun q => D.len (P q.val) (a q.val) (b q.val)) hcost
        i tail j hchain hlast' hx hy
      have hsub : (i :: tail).toFinset ⊆ S.attach := by
        intro q hq
        exact Finset.mem_attach S q
      have hsum : ((i :: tail).map (fun q : {i // i ∈ S} =>
          D.len (P q.val) (a q.val) (b q.val))).sum ≤
          ∑ k ∈ S, D.len (P k) (a k) (b k) := by
        rw [← List.sum_toFinset _ hnodup]
        calc
          _ ≤ ∑ q ∈ S.attach, D.len (P q.val) (a q.val) (b q.val) :=
            Finset.sum_le_sum_of_subset_of_nonneg hsub (by simp)
          _ = ∑ k ∈ S, D.len (P k) (a k) (b k) := by exact Finset.sum_attach S (fun k => D.len (P k) (a k) (b k))
      exact hpaid.trans hsum

 
theorem pathHit_time {K E F : Set ℂ} {P : ℝ → ℂ} {a b : ℝ}
    (hab : a ≤ b) (hP : ContinuousOn P (Icc a b))
    (hsep : LQGMetric.Disconnects K E F) (ha : P a ∈ E) (hb : P b ∈ F) :
    ∃ u ∈ Icc a b, P u ∈ K := by
  have hpc : IsPathConnected (P '' Icc a b) :=
    ((convex_Icc a b).isPathConnected ⟨a, ⟨le_rfl, hab⟩⟩).image' hP
  have hjoined : JoinedIn (P '' Icc a b) (P a) (P b) :=
    hpc.joinedIn (P a) ⟨a, ⟨le_rfl, hab⟩, rfl⟩
      (P b) ⟨b, ⟨hab, le_rfl⟩, rfl⟩
  obtain ⟨w, ⟨t, rfl⟩, hwK⟩ := hsep (P a) (P b) hjoined.somePath ha hb
  obtain ⟨u, hu, hPu⟩ := hjoined.somePath_mem t
  exact ⟨u, hu, hPu ▸ hwK⟩

 
theorem separator_twoSidedShortcut (D : LSCMetric) {P π : ℝ → ℂ}
    {T a c e b s t r R L : ℝ} {z : ℂ}
    (ha0 : 0 ≤ a) (hac : a < c) (hce : c ≤ e) (heb : e < b) (hbT : b ≤ T)
    (hP : ContinuousOn P (Icc 0 T))
    (hgeo : IsGeodesicCurve (D.pt ∘ P) 0 T)
    (hunit : HasUnitSpeedOn (D.pt ∘ P) (Icc 0 T))
    (hr : 0 < r) (hrR : r < R)
    (ha : R ≤ dist (P a) z) (hc : dist (P c) z ≤ r)
    (he : dist (P e) z ≤ r) (hb : R ≤ dist (P b) z)
    (_hπ : D.IsCurve π s t)
    (hsep : LQGMetric.Disconnects (π '' Icc s t) (sphere z r) (sphere z R))
    (hann : π '' Icc s t ⊆ {w | r < dist w z ∧ dist w z < R})
    (hL : 0 ≤ L) (hlen : D.len π s t = ENNReal.ofReal L) :
    ∃ u v : ℝ, a < u ∧ u < c ∧ e < v ∧ v < b ∧
      e - c ≤ v - u ∧ v - u ≤ L := by
  have hacT : Icc a c ⊆ Icc 0 T := Icc_subset_Icc ha0 (le_trans hce (le_trans heb.le hbT))
  have hebT : Icc e b ⊆ Icc 0 T := Icc_subset_Icc (le_trans ha0 (le_trans hac.le hce)) hbT
  have haout : P a ∈ (ball z R)ᶜ := by simpa only [mem_compl_iff, mem_ball, not_lt] using ha
  have hbout : P b ∈ (ball z R)ᶜ := by simpa only [mem_compl_iff, mem_ball, not_lt] using hb
  have hcin : P c ∈ closedBall z r := by simpa only [mem_closedBall] using hc
  have hein : P e ∈ closedBall z r := by simpa only [mem_closedBall] using he
  obtain ⟨u, hu, huK⟩ := pathHit_time hac.le (hP.mono hacT)
    (annularPath_hit_reverse hr hrR hsep) haout hcin
  obtain ⟨v, hv, hvK⟩ := pathHit_time heb.le (hP.mono hebT)
    (annularPath_hit hr hrR hsep) hein hbout
  have huAnn := hann huK
  have hvAnn := hann hvK
  have hau : a < u := by
    by_contra h
    have hEq : u = a := le_antisymm (not_lt.mp h) hu.1
    rw [hEq] at huAnn
    exact (not_lt_of_ge ha) huAnn.2
  have huc : u < c := by
    by_contra h
    have hEq : u = c := le_antisymm hu.2 (not_lt.mp h)
    rw [hEq] at huAnn
    exact (not_lt_of_ge hc) huAnn.1
  have hev : e < v := by
    by_contra h
    have hEq : v = e := le_antisymm (not_lt.mp h) hv.1
    rw [hEq] at hvAnn
    exact (not_lt_of_ge he) hvAnn.1
  have hvb : v < b := by
    by_contra h
    have hEq : v = b := le_antisymm hv.2 (not_lt.mp h)
    rw [hEq] at hvAnn
    exact (not_lt_of_ge hb) hvAnn.2
  have huT : u ∈ Icc 0 T := hacT hu
  have hvT : v ∈ Icc 0 T := hebT hv
  have huv : u ≤ v := le_trans (le_trans huc.le hce) hev.le
  have hcost : D (P u, P v) ≤ D.len π s t :=
    trace_dist_le_len D π huK hvK
  have hdist : D (P u, P v) = ENNReal.ofReal (v - u) :=
    hgeo.edist_eq_of_hasUnitSpeedOn hunit huT hvT huv
  rw [hdist, hlen] at hcost
  have hreal : v - u ≤ L := (ENNReal.ofReal_le_ofReal_iff hL).mp hcost
  exact ⟨u, v, hau, huc, hev, hvb, by linarith, hreal⟩

 
theorem separator_twoSidedShortcut_around (D : LSCMetric) (A : EuclideanAnnulus)
    {P : ℝ → ℂ} {T a c e b : ℝ}
    (ha0 : 0 ≤ a) (hac : a < c) (hce : c ≤ e) (heb : e < b) (hbT : b ≤ T)
    (hP : ContinuousOn P (Icc 0 T))
    (hgeo : IsGeodesicCurve (D.pt ∘ P) 0 T)
    (hunit : HasUnitSpeedOn (D.pt ∘ P) (Icc 0 T))
    (ha : A.outerRadius ≤ dist (P a) A.center)
    (hc : dist (P c) A.center ≤ A.innerRadius)
    (he : dist (P e) A.center ≤ A.innerRadius)
    (hb : A.outerRadius ≤ dist (P b) A.center) :
    ENNReal.ofReal (e - c) ≤ aroundDist D A := by
  unfold aroundDist
  apply le_iInf
  intro π
  apply le_iInf
  intro s
  apply le_iInf
  intro t
  apply le_iInf
  intro hπ
  apply le_iInf
  intro hY
  apply le_iInf
  intro hsep
  by_cases hfin : D.len π s t = ∞
  · simp only [hfin, le_top]
  · have hr : 0 < A.innerRadius := A.2.1
    have hrR : A.innerRadius < A.outerRadius := A.2.2
    have hsep' : LQGMetric.Disconnects (π '' Icc s t)
        (sphere A.center A.innerRadius) (sphere A.center A.outerRadius) :=
      candidate_disconnects_implies_path_hit hsep
    have hann : π '' Icc s t ⊆
        {w | A.innerRadius < dist w A.center ∧ dist w A.center < A.outerRadius} := by
      intro w hw
      obtain ⟨q, hq, rfl⟩ := hw
      have hA : π q ∈ A.toSet := hY q hq
      change π q ∈ ball A.center A.outerRadius ∧
        π q ∉ closure (ball A.center A.innerRadius) at hA
      rw [closure_ball A.center (ne_of_gt hr)] at hA
      exact ⟨lt_of_not_ge (by simpa only [mem_closedBall] using hA.2),
        by simpa only [mem_ball] using hA.1⟩
    have hlen : D.len π s t = ENNReal.ofReal (D.len π s t).toReal :=
      (ENNReal.ofReal_toReal hfin).symm
    obtain ⟨u, v, _, _, _, _, hbound, htime⟩ :=
      separator_twoSidedShortcut D ha0 hac hce heb hbT hP hgeo hunit
        hr hrR ha hc he hb hπ hsep' hann ENNReal.toReal_nonneg hlen
    calc
      ENNReal.ofReal (e - c) ≤ ENNReal.ofReal ((D.len π s t).toReal) :=
        ENNReal.ofReal_le_ofReal (hbound.trans htime)
      _ = D.len π s t := ENNReal.ofReal_toReal hfin

 

theorem excursionComponentCode {P : ℝ → ℂ} {O : Set ℂ} {T q : ℝ}
    (_hT : 0 ≤ T) (hP : ContinuousOn P (Icc 0 T)) (hO : IsOpen O)
    (h0 : P 0 ∉ O) (hTOut : P T ∉ O)
    (hq : q ∈ Ioo 0 T) (hqO : P q ∈ O) :
    let a := sSup {u ∈ Icc 0 q | P u ∉ O}
    let b := sInf {u ∈ Icc q T | P u ∉ O}
    0 ≤ a ∧ a < q ∧ q < b ∧ b ≤ T ∧
      P a ∉ O ∧ P b ∉ O ∧ ∀ u ∈ Ioo a b, P u ∈ O := by
  let E₁ : Set ℝ := {u ∈ Icc 0 q | P u ∉ O}
  let E₂ : Set ℝ := {u ∈ Icc q T | P u ∉ O}
  have hP₁ : ContinuousOn P (Icc 0 q) :=
    hP.mono (Icc_subset_Icc le_rfl hq.2.le)
  have hP₂ : ContinuousOn P (Icc q T) :=
    hP.mono (Icc_subset_Icc hq.1.le le_rfl)
  have hc₁ : IsClosed E₁ :=
    hP₁.preimage_isClosed_of_isClosed isClosed_Icc hO.isClosed_compl
  have hc₂ : IsClosed E₂ :=
    hP₂.preimage_isClosed_of_isClosed isClosed_Icc hO.isClosed_compl
  have hne₁ : E₁.Nonempty := ⟨0, ⟨⟨le_rfl, hq.1.le⟩, h0⟩⟩
  have hne₂ : E₂.Nonempty := ⟨T, ⟨⟨hq.2.le, le_rfl⟩, hTOut⟩⟩
  have hbd₁ : BddAbove E₁ := ⟨q, fun u hu => hu.1.2⟩
  have hbd₂ : BddBelow E₂ := ⟨q, fun u hu => hu.1.1⟩
  let a := sSup E₁
  let b := sInf E₂
  have haE : a ∈ E₁ := hc₁.csSup_mem hne₁ hbd₁
  have hbE : b ∈ E₂ := hc₂.csInf_mem hne₂ hbd₂
  have haq : a < q := lt_of_le_of_ne haE.1.2 (by
    intro h
    exact haE.2 (h.symm ▸ hqO))
  have hqb : q < b := lt_of_le_of_ne hbE.1.1 (by
    intro h
    exact hbE.2 (h ▸ hqO))
  dsimp
  refine ⟨haE.1.1, haq, hqb, hbE.1.2, haE.2, hbE.2, ?_⟩
  intro u hu
  by_contra hnot
  rcases le_total u q with huq | hqu
  · have huE : u ∈ E₁ := ⟨⟨haE.1.1.trans hu.1.le, huq⟩, hnot⟩
    exact (not_le_of_gt hu.1) (le_csSup hbd₁ huE)
  · have huE : u ∈ E₂ := ⟨⟨hqu, hu.2.le.trans hbE.1.2⟩, hnot⟩
    exact (not_le_of_gt hu.2) (csInf_le hbd₂ huE)

 

theorem excursionContactCode {P : ℝ → ℂ} {O V : Set ℂ} {T q : ℝ}
    (hT : 0 ≤ T) (hP : ContinuousOn P (Icc 0 T)) (hO : IsOpen O)
    (h0 : P 0 ∉ O) (hTOut : P T ∉ O)
    (hq : q ∈ Ioo 0 T) (hqO : P q ∈ O)
    (hVO : closure V ⊆ O)
    (hcontact : ({u ∈ Icc
      (sSup {v ∈ Icc 0 q | P v ∉ O})
      (sInf {v ∈ Icc q T | P v ∉ O}) | P u ∈ closure V}).Nonempty) :
    let a := sSup {v ∈ Icc 0 q | P v ∉ O}
    let b := sInf {v ∈ Icc q T | P v ∉ O}
    let C := {u ∈ Icc a b | P u ∈ closure V}
    let τ := sInf C
    let σ := sSup C
    a < τ ∧ τ ≤ σ ∧ σ < b ∧
      P τ ∈ closure V ∧ P σ ∈ closure V ∧
      ∀ u ∈ Icc a b, P u ∈ V → τ ≤ u ∧ u ≤ σ := by
  let a := sSup {v ∈ Icc 0 q | P v ∉ O}
  let b := sInf {v ∈ Icc q T | P v ∉ O}
  let C : Set ℝ := {u ∈ Icc a b | P u ∈ closure V}
  have hcomp := excursionComponentCode hT hP hO h0 hTOut hq hqO
  dsimp only at hcomp
  obtain ⟨ha0, haq, hqb, hbT, haOut, hbOut, _⟩ := hcomp
  change P a ∉ O at haOut
  change P b ∉ O at hbOut
  have hPab : ContinuousOn P (Icc a b) :=
    hP.mono (Icc_subset_Icc ha0 hbT)
  have hCclosed : IsClosed C :=
    hPab.preimage_isClosed_of_isClosed isClosed_Icc isClosed_closure
  have hCne : C.Nonempty := hcontact
  have hCbelow : BddBelow C := ⟨a, fun u hu => hu.1.1⟩
  have hCabove : BddAbove C := ⟨b, fun u hu => hu.1.2⟩
  let τ := sInf C
  let σ := sSup C
  have hτC : τ ∈ C := hCclosed.csInf_mem hCne hCbelow
  have hσC : σ ∈ C := hCclosed.csSup_mem hCne hCabove
  have haτ : a < τ := lt_of_le_of_ne hτC.1.1 (by
    intro h
    rw [h] at haOut
    exact haOut (hVO hτC.2))
  have hσb : σ < b := lt_of_le_of_ne hσC.1.2 (by
    intro h
    rw [← h] at hbOut
    exact hbOut (hVO hσC.2))
  have hτσ : τ ≤ σ := csInf_le_csSup hCne hCbelow hCabove
  dsimp
  refine ⟨haτ, hτσ, hσb, hτC.2, hσC.2, ?_⟩
  intro u hu huV
  have huC : u ∈ C := ⟨hu, subset_closure huV⟩
  exact ⟨csInf_le hCbelow huC, le_csSup hCabove huC⟩

 

theorem lastVisitOrZero_terminal {ι : Type*} (S : Finset ι) (V : ι → Set ℂ)
    (P : ℝ → ℂ) {T : ℝ} (hT : 0 ≤ T) :
    let visits : Set ℝ := {t ∈ Icc 0 T | ∃ i ∈ S, P t ∈ V i}
    let m := sSup (insert 0 visits)
    0 ≤ m ∧ m ≤ T ∧
      (∀ t ∈ Ioc m T, ∀ i ∈ S, P t ∉ V i) ∧
      ((∀ t ∈ Icc 0 T, ∀ i ∈ S, P t ∉ V i) → m = 0) := by
  let visits : Set ℝ := {t ∈ Icc 0 T | ∃ i ∈ S, P t ∈ V i}
  let C : Set ℝ := insert 0 visits
  have hCT : ∀ u ∈ C, u ≤ T := by
    intro u hu
    rcases hu with rfl | hu
    · exact hT
    · exact hu.1.2
  have hCbd : BddAbove C := ⟨T, hCT⟩
  have h0C : 0 ∈ C := mem_insert 0 visits
  let m := sSup C
  have hm0 : 0 ≤ m := le_csSup hCbd h0C
  have hmT : m ≤ T := csSup_le ⟨0, h0C⟩ hCT
  dsimp
  refine ⟨hm0, hmT, ?_, ?_⟩
  · intro t ht i hi hvisit
    have htvis : t ∈ visits := ⟨⟨hm0.trans ht.1.le, ht.2⟩, ⟨i, hi, hvisit⟩⟩
    have htm : t ≤ m := le_csSup hCbd (mem_insert_of_mem 0 htvis)
    exact (not_le_of_gt ht.1) htm
  · intro hnone
    have hEmpty : visits = ∅ := by
      ext t
      constructor
      · intro ht
        obtain ⟨htI, i, hi, htV⟩ := ht
        exact False.elim ((hnone t htI i hi) htV)
      · intro ht
        simp at ht
    change sSup C = 0
    simp [C, hEmpty]

 

theorem finite_of_compact_of_separated {X : Type*} [PseudoEMetricSpace X]
    {K S : Set X} (hK : IsCompact K) (hSK : S ⊆ K)
    {ε : NNReal} (hε : ε ≠ 0)
    (hsep : Metric.IsSeparated (↑(2 * ε) : ENNReal) S) : S.Finite := by
  obtain ⟨N, _, hNfinite, hcover⟩ :=
    Metric.exists_finite_isCover_of_isCompact hε hK
  have hS : S.encard ≤ N.encard :=
    (Metric.IsSeparated.encard_le_packingNumber hSK hsep).trans
      ((Metric.packingNumber_two_mul_le_externalCoveringNumber ε K).trans
        hcover.externalCoveringNumber_le_encard)
  exact Set.encard_lt_top_iff.mp
    (lt_of_le_of_lt hS (Set.encard_lt_top_iff.mpr hNfinite))

 

theorem contact_time_gap {P : ℝ → ℂ} {O V : Set ℂ} {T ρ : ℝ}
    (hP : ContinuousOn P (Icc 0 T)) (hρ : 0 < ρ)
    (hsep : ∀ x ∈ closure V, ∀ y ∈ Oᶜ, ρ ≤ dist x y) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ s ∈ Icc 0 T, ∀ t ∈ Icc 0 T,
      P s ∉ O → P t ∈ closure V → δ ≤ dist s t := by
  obtain ⟨δ, hδ, hmod⟩ :=
    (Metric.uniformContinuousOn_iff.mp
      (isCompact_Icc.uniformContinuousOn_of_continuous hP)) ρ hρ
  refine ⟨δ, hδ, ?_⟩
  intro s hs t ht hsO htV
  have hPt : ρ ≤ dist (P t) (P s) := hsep (P t) htV (P s) hsO
  have hPs : ρ ≤ dist (P s) (P t) := by simpa only [dist_comm] using hPt
  exact le_of_not_gt (fun hst => (not_lt_of_ge hPs) (hmod s hs t ht hst))

 

theorem excursionCode_eq_of_mem_component {P : ℝ → ℂ} {O : Set ℂ} {T q q' : ℝ}
    (hT : 0 ≤ T) (hP : ContinuousOn P (Icc 0 T)) (hO : IsOpen O)
    (h0 : P 0 ∉ O) (hTOut : P T ∉ O)
    (hq : q ∈ Ioo 0 T) (hqO : P q ∈ O)
    (hq' : q' ∈ Ioo
      (sSup {u ∈ Icc 0 q | P u ∉ O})
      (sInf {u ∈ Icc q T | P u ∉ O})) :
    sSup {u ∈ Icc 0 q' | P u ∉ O} = sSup {u ∈ Icc 0 q | P u ∉ O} ∧
    sInf {u ∈ Icc q' T | P u ∉ O} = sInf {u ∈ Icc q T | P u ∉ O} := by
  let a := sSup {u ∈ Icc 0 q | P u ∉ O}
  let b := sInf {u ∈ Icc q T | P u ∉ O}
  let E₁ : Set ℝ := {u ∈ Icc 0 q' | P u ∉ O}
  let E₂ : Set ℝ := {u ∈ Icc q' T | P u ∉ O}
  have hcomp := excursionComponentCode hT hP hO h0 hTOut hq hqO
  dsimp only at hcomp
  obtain ⟨ha0, _, _, hbT, haOut, hbOut, hinside⟩ := hcomp
  change P a ∉ O at haOut
  change P b ∉ O at hbOut
  have haE : a ∈ E₁ := ⟨⟨ha0, hq'.1.le⟩, haOut⟩
  have hbE : b ∈ E₂ := ⟨⟨hq'.2.le, hbT⟩, hbOut⟩
  have hbd₁ : BddAbove E₁ := ⟨q', fun u hu => hu.1.2⟩
  have hbd₂ : BddBelow E₂ := ⟨q', fun u hu => hu.1.1⟩
  have hEa : ∀ u ∈ E₁, u ≤ a := by
    intro u hu
    by_contra h
    have hau : a < u := lt_of_not_ge h
    have hub : u < b := hu.1.2.trans_lt hq'.2
    exact hu.2 (hinside u ⟨hau, hub⟩)
  have hEb : ∀ u ∈ E₂, b ≤ u := by
    intro u hu
    by_contra h
    have hub : u < b := lt_of_not_ge h
    have hau : a < u := hq'.1.trans_le hu.1.1
    exact hu.2 (hinside u ⟨hau, hub⟩)
  have haEq : sSup E₁ = a :=
    le_antisymm (csSup_le ⟨a, haE⟩ hEa) (le_csSup hbd₁ haE)
  have hbEq : sInf E₂ = b :=
    le_antisymm (csInf_le hbd₂ hbE) (le_csInf ⟨b, hbE⟩ hEb)
  exact ⟨haEq, hbEq⟩

 
theorem finite_of_compact_of_real_separated {S : Set ℝ} {T δ : ℝ}
    (hS : S ⊆ Icc 0 T) (hδ : 0 < δ)
    (hsep : ∀ x ∈ S, ∀ y ∈ S, x ≠ y → δ ≤ dist x y) : S.Finite := by
  let ε : NNReal := ⟨δ / 4, by positivity⟩
  have hε : ε ≠ 0 := by
    apply ne_of_gt
    change 0 < δ / 4
    positivity
  apply finite_of_compact_of_separated isCompact_Icc hS hε
  intro x hx y hy hxy
  have hδxy : δ ≤ dist x y := hsep x hx y hy hxy
  have hsmall : 2 * (ε : ℝ) < dist x y := by
    change 2 * (δ / 4) < dist x y
    linarith
  have hεeq : (↑(2 * ε) : ENNReal) = ENNReal.ofReal (2 * (ε : ℝ)) := by
    rw [ENNReal.coe_nnreal_eq]
    congr 1
  rw [hεeq, edist_dist]
  exact (ENNReal.ofReal_lt_ofReal_iff (lt_of_lt_of_le (by positivity) hδxy)).mpr hsmall

 

theorem finiteCanonicalExcursionStarts {P : ℝ → ℂ} {O V : Set ℂ} {T ρ : ℝ}
    (hT : 0 ≤ T) (hP : ContinuousOn P (Icc 0 T)) (hO : IsOpen O)
    (h0 : P 0 ∉ O) (hTOut : P T ∉ O)
    (hVO : closure V ⊆ O) (hρ : 0 < ρ)
    (hsep : ∀ x ∈ closure V, ∀ y ∈ Oᶜ, ρ ≤ dist x y) :
    let a : ℝ → ℝ := fun q => sSup {u ∈ Icc 0 q | P u ∉ O}
    let b : ℝ → ℝ := fun q => sInf {u ∈ Icc q T | P u ∉ O}
    let active : Set ℝ := {q | q ∈ Ioo 0 T ∧ P q ∈ O ∧
      ({u ∈ Icc (a q) (b q) | P u ∈ closure V}).Nonempty}
    {x | ∃ q ∈ active, x = a q}.Finite := by
  let a : ℝ → ℝ := fun q => sSup {u ∈ Icc 0 q | P u ∉ O}
  let b : ℝ → ℝ := fun q => sInf {u ∈ Icc q T | P u ∉ O}
  let active : Set ℝ := {q | q ∈ Ioo 0 T ∧ P q ∈ O ∧
    ({u ∈ Icc (a q) (b q) | P u ∈ closure V}).Nonempty}
  let starts : Set ℝ := {x | ∃ q ∈ active, x = a q}
  obtain ⟨δ, hδ, hgap⟩ := contact_time_gap hP hρ hsep
  have hstarts : starts ⊆ Icc 0 T := by
    intro x hx
    obtain ⟨q, hq, hxq⟩ := hx
    subst x
    have hcomp := excursionComponentCode hT hP hO h0 hTOut hq.1 hq.2.1
    dsimp only at hcomp
    exact ⟨hcomp.1, (hcomp.2.1.le.trans hq.1.2.le)⟩
  have hordered : ∀ q₁ q₂, q₁ ∈ active → q₂ ∈ active →
      a q₁ < a q₂ → δ ≤ a q₂ - a q₁ := by
    intro q₁ q₂ hq₁ hq₂ hlt
    have hcomp₁ := excursionComponentCode hT hP hO h0 hTOut hq₁.1 hq₁.2.1
    have hcomp₂ := excursionComponentCode hT hP hO h0 hTOut hq₂.1 hq₂.2.1
    dsimp only at hcomp₁ hcomp₂
    obtain ⟨ha₁0, _, _, hb₁T, ha₁Out, _, hinside₁⟩ := hcomp₁
    obtain ⟨_, _, _, _, ha₂Out, _, _⟩ := hcomp₂
    change P (a q₁) ∉ O at ha₁Out
    change P (a q₂) ∉ O at ha₂Out
    have hb₁a₂ : b q₁ ≤ a q₂ := by
      by_contra h
      exact ha₂Out (hinside₁ (a q₂) ⟨hlt, lt_of_not_ge h⟩)
    have hcontact₁ := excursionContactCode hT hP hO h0 hTOut
      hq₁.1 hq₁.2.1 hVO hq₁.2.2
    dsimp only at hcontact₁
    obtain ⟨haτ, hτσ, hσb, hτV, _, _⟩ := hcontact₁
    let τ := sInf {u ∈ Icc (a q₁) (b q₁) | P u ∈ closure V}
    have hτT : τ ∈ Icc 0 T :=
      ⟨ha₁0.trans haτ.le, (hτσ.trans_lt hσb).le.trans hb₁T⟩
    have ha₁T : a q₁ ∈ Icc 0 T :=
      ⟨ha₁0, (haτ.trans_le hτT.2).le⟩
    have hδtime : δ ≤ dist (a q₁) τ :=
      hgap (a q₁) ha₁T τ hτT ha₁Out hτV
    have hδlen : δ ≤ τ - a q₁ := by
      have hdistEq : dist (a q₁) τ = τ - a q₁ := by
        rw [Real.dist_eq, abs_sub_comm, abs_of_nonneg (sub_nonneg.mpr haτ.le)]
      rwa [hdistEq] at hδtime
    linarith
  have hseparated : ∀ x ∈ starts, ∀ y ∈ starts,
      x ≠ y → δ ≤ dist x y := by
    intro x hx y hy hxy
    obtain ⟨q₁, hq₁, hxq⟩ := hx
    obtain ⟨q₂, hq₂, hyq⟩ := hy
    subst x
    subst y
    rcases lt_or_gt_of_ne hxy with hlt | hgt
    · have h := hordered q₁ q₂ hq₁ hq₂ hlt
      rw [Real.dist_eq, abs_of_nonpos (sub_nonpos.mpr hlt.le)]
      linarith
    · have h := hordered q₂ q₁ hq₂ hq₁ hgt
      rw [Real.dist_eq, abs_of_nonneg (sub_nonneg.mpr hgt.le)]
      exact h
  exact finite_of_compact_of_real_separated hstarts hδ hseparated

end SupercriticalLQGUniqueness.Uniqueness.Toolkit.PlanarSeparation

namespace SupercriticalLQGUniqueness.Uniqueness.Toolkit.PlanarSeparation

 

theorem excursionCode_eq_of_same_start {P : ℝ → ℂ} {O : Set ℂ} {T q₁ q₂ : ℝ}
    (hT : 0 ≤ T) (hP : ContinuousOn P (Icc 0 T)) (hO : IsOpen O)
    (h0 : P 0 ∉ O) (hTOut : P T ∉ O)
    (hq₁ : q₁ ∈ Ioo 0 T) (hq₁O : P q₁ ∈ O)
    (hq₂ : q₂ ∈ Ioo 0 T) (hq₂O : P q₂ ∈ O)
    (hstart : sSup {u ∈ Icc 0 q₁ | P u ∉ O} =
      sSup {u ∈ Icc 0 q₂ | P u ∉ O}) :
    sInf {u ∈ Icc q₁ T | P u ∉ O} =
      sInf {u ∈ Icc q₂ T | P u ∉ O} := by
  let a₁ := sSup {u ∈ Icc 0 q₁ | P u ∉ O}
  let b₁ := sInf {u ∈ Icc q₁ T | P u ∉ O}
  let a₂ := sSup {u ∈ Icc 0 q₂ | P u ∉ O}
  change a₁ = a₂ at hstart
  have hcomp₁ := excursionComponentCode hT hP hO h0 hTOut hq₁ hq₁O
  have hcomp₂ := excursionComponentCode hT hP hO h0 hTOut hq₂ hq₂O
  dsimp only at hcomp₁ hcomp₂
  have ha₂q₂ : a₂ < q₂ := hcomp₂.2.1
  have hb₁Out : P b₁ ∉ O := hcomp₁.2.2.2.2.2.1
  have hb₁T : b₁ ≤ T := hcomp₁.2.2.2.1
  have ha₁b₁ : a₁ < b₁ := hcomp₁.2.1.trans hcomp₁.2.2.1
  have hq₂b₁ : q₂ < b₁ := by
    by_contra h
    have hb₁q₂ : b₁ ≤ q₂ := le_of_not_gt h
    have hb₁E : b₁ ∈ {u ∈ Icc 0 q₂ | P u ∉ O} :=
      ⟨⟨hcomp₁.1.trans ha₁b₁.le, hb₁q₂⟩, hb₁Out⟩
    have hb₁a₂ : b₁ ≤ a₂ := le_csSup ⟨q₂, fun u hu => hu.1.2⟩ hb₁E
    rw [← hstart] at hb₁a₂
    exact (not_le_of_gt ha₁b₁) hb₁a₂
  have hq₂mem : q₂ ∈ Ioo a₁ b₁ := ⟨hstart.trans_lt ha₂q₂, hq₂b₁⟩
  have heq := (excursionCode_eq_of_mem_component hT hP hO h0 hTOut
    hq₁ hq₁O hq₂mem).2
  exact heq.symm

end SupercriticalLQGUniqueness.Uniqueness.Toolkit.PlanarSeparation

namespace SupercriticalLQGUniqueness.Uniqueness.Toolkit.PlanarSeparation

 

theorem finiteCanonicalExcursionPairs {P : ℝ → ℂ} {O V : Set ℂ} {T ρ : ℝ}
    (hT : 0 ≤ T) (hP : ContinuousOn P (Icc 0 T)) (hO : IsOpen O)
    (h0 : P 0 ∉ O) (hTOut : P T ∉ O)
    (hVO : closure V ⊆ O) (hρ : 0 < ρ)
    (hsep : ∀ x ∈ closure V, ∀ y ∈ Oᶜ, ρ ≤ dist x y) :
    let a : ℝ → ℝ := fun q => sSup {u ∈ Icc 0 q | P u ∉ O}
    let b : ℝ → ℝ := fun q => sInf {u ∈ Icc q T | P u ∉ O}
    let active : Set ℝ := {q | q ∈ Ioo 0 T ∧ P q ∈ O ∧
      ({u ∈ Icc (a q) (b q) | P u ∈ closure V}).Nonempty}
    {p : ℝ × ℝ | ∃ q ∈ active, p = (a q, b q)}.Finite := by
  let a : ℝ → ℝ := fun q => sSup {u ∈ Icc 0 q | P u ∉ O}
  let b : ℝ → ℝ := fun q => sInf {u ∈ Icc q T | P u ∉ O}
  let active : Set ℝ := {q | q ∈ Ioo 0 T ∧ P q ∈ O ∧
    ({u ∈ Icc (a q) (b q) | P u ∈ closure V}).Nonempty}
  let pairs : Set (ℝ × ℝ) := {p | ∃ q ∈ active, p = (a q, b q)}
  let starts : Set ℝ := {x | ∃ q ∈ active, x = a q}
  have hstarts : starts.Finite :=
    finiteCanonicalExcursionStarts hT hP hO h0 hTOut hVO hρ hsep
  have himg : Prod.fst '' pairs = starts := by
    ext x
    constructor
    · rintro ⟨p, ⟨q, hq, rfl⟩, rfl⟩
      exact ⟨q, hq, rfl⟩
    · rintro ⟨q, hq, rfl⟩
      exact ⟨(a q, b q), ⟨q, hq, rfl⟩, rfl⟩
  have hinj : Set.InjOn Prod.fst pairs := by
    intro p hp r hr hpr
    obtain ⟨q₁, hq₁, rfl⟩ := hp
    obtain ⟨q₂, hq₂, rfl⟩ := hr
    change a q₁ = a q₂ at hpr
    have hb : b q₁ = b q₂ :=
      excursionCode_eq_of_same_start hT hP hO h0 hTOut
        hq₁.1 hq₁.2.1 hq₂.1 hq₂.2.1 hpr
    exact Prod.ext hpr hb
  exact Set.Finite.of_finite_image (himg ▸ hstarts) hinj

end SupercriticalLQGUniqueness.Uniqueness.Toolkit.PlanarSeparation

namespace SupercriticalLQGUniqueness.Uniqueness.Toolkit.PlanarSeparation

 

theorem finiteCanonicalExcursionTuples {P : ℝ → ℂ} {O V : Set ℂ} {T ρ : ℝ}
    (hT : 0 ≤ T) (hP : ContinuousOn P (Icc 0 T)) (hO : IsOpen O)
    (h0 : P 0 ∉ O) (hTOut : P T ∉ O)
    (hVO : closure V ⊆ O) (hρ : 0 < ρ)
    (hsep : ∀ x ∈ closure V, ∀ y ∈ Oᶜ, ρ ≤ dist x y) :
    let a : ℝ → ℝ := fun q => sSup {u ∈ Icc 0 q | P u ∉ O}
    let b : ℝ → ℝ := fun q => sInf {u ∈ Icc q T | P u ∉ O}
    let active : Set ℝ := {q | q ∈ Ioo 0 T ∧ P q ∈ O ∧
      ({u ∈ Icc (a q) (b q) | P u ∈ closure V}).Nonempty}
    {e : ℝ × ℝ × ℝ × ℝ | ∃ q ∈ active,
      e = (a q, b q,
        sInf {u ∈ Icc (a q) (b q) | P u ∈ closure V},
        sSup {u ∈ Icc (a q) (b q) | P u ∈ closure V})}.Finite := by
  let a : ℝ → ℝ := fun q => sSup {u ∈ Icc 0 q | P u ∉ O}
  let b : ℝ → ℝ := fun q => sInf {u ∈ Icc q T | P u ∉ O}
  let active : Set ℝ := {q | q ∈ Ioo 0 T ∧ P q ∈ O ∧
    ({u ∈ Icc (a q) (b q) | P u ∈ closure V}).Nonempty}
  let pairs : Set (ℝ × ℝ) := {p | ∃ q ∈ active, p = (a q, b q)}
  let f : (ℝ × ℝ) → (ℝ × ℝ × ℝ × ℝ) := fun p =>
    (p.1, p.2,
      sInf {u ∈ Icc p.1 p.2 | P u ∈ closure V},
      sSup {u ∈ Icc p.1 p.2 | P u ∈ closure V})
  have hpairs : pairs.Finite :=
    finiteCanonicalExcursionPairs hT hP hO h0 hTOut hVO hρ hsep
  have heq : f '' pairs = {e : ℝ × ℝ × ℝ × ℝ | ∃ q ∈ active,
      e = (a q, b q,
        sInf {u ∈ Icc (a q) (b q) | P u ∈ closure V},
        sSup {u ∈ Icc (a q) (b q) | P u ∈ closure V})} := by
    ext e
    constructor
    · rintro ⟨p, ⟨q, hq, rfl⟩, rfl⟩
      exact ⟨q, hq, rfl⟩
    · rintro ⟨q, hq, rfl⟩
      exact ⟨(a q, b q), ⟨q, hq, rfl⟩, rfl⟩
  dsimp only
  rw [← heq]
  exact hpairs.image f

end SupercriticalLQGUniqueness.Uniqueness.Toolkit.PlanarSeparation

namespace SupercriticalLQGUniqueness.Uniqueness.Toolkit.PlanarSeparation

 


theorem finiteCanonicalExcursionFamily {ι : Type*} (S : Finset ι)
    (P : ℝ → ℂ) (O V : ι → Set ℂ) {T : ℝ} (ρ : ι → ℝ)
    (hT : 0 ≤ T) (hP : ContinuousOn P (Icc 0 T))
    (hO : ∀ i ∈ S, IsOpen (O i))
    (h0 : ∀ i ∈ S, P 0 ∉ O i) (hTOut : ∀ i ∈ S, P T ∉ O i)
    (hVO : ∀ i ∈ S, closure (V i) ⊆ O i)
    (hρ : ∀ i ∈ S, 0 < ρ i)
    (hsep : ∀ i ∈ S, ∀ x ∈ closure (V i), ∀ y ∈ (O i)ᶜ,
      ρ i ≤ dist x y) :
    let F : ι → Set (ℝ × ℝ × ℝ × ℝ) := fun i =>
      let a : ℝ → ℝ := fun q => sSup {u ∈ Icc 0 q | P u ∉ O i}
      let b : ℝ → ℝ := fun q => sInf {u ∈ Icc q T | P u ∉ O i}
      let active : Set ℝ := {q | q ∈ Ioo 0 T ∧ P q ∈ O i ∧
        ({u ∈ Icc (a q) (b q) | P u ∈ closure (V i)}).Nonempty}
      {e | ∃ q ∈ active,
        e = (a q, b q,
          sInf {u ∈ Icc (a q) (b q) | P u ∈ closure (V i)},
          sSup {u ∈ Icc (a q) (b q) | P u ∈ closure (V i)})}
    (⋃ i ∈ S, (fun e => (i, e)) '' F i).Finite := by
  let F : ι → Set (ℝ × ℝ × ℝ × ℝ) := fun i =>
    let a : ℝ → ℝ := fun q => sSup {u ∈ Icc 0 q | P u ∉ O i}
    let b : ℝ → ℝ := fun q => sInf {u ∈ Icc q T | P u ∉ O i}
    let active : Set ℝ := {q | q ∈ Ioo 0 T ∧ P q ∈ O i ∧
      ({u ∈ Icc (a q) (b q) | P u ∈ closure (V i)}).Nonempty}
    {e | ∃ q ∈ active,
      e = (a q, b q,
        sInf {u ∈ Icc (a q) (b q) | P u ∈ closure (V i)},
        sSup {u ∈ Icc (a q) (b q) | P u ∈ closure (V i)})}
  have hFi : ∀ i ∈ S, (F i).Finite := by
    intro i hi
    exact finiteCanonicalExcursionTuples hT hP (hO i hi) (h0 i hi)
      (hTOut i hi) (hVO i hi) (hρ i hi) (hsep i hi)
  exact S.finite_toSet.biUnion (fun i hi => (hFi i hi).image (fun e => (i, e)))

end SupercriticalLQGUniqueness.Uniqueness.Toolkit.PlanarSeparation

namespace SupercriticalLQGUniqueness.Uniqueness.Toolkit.PlanarSeparation

 

theorem openVisit_in_canonicalContact {P : ℝ → ℂ} {O V : Set ℂ} {T t : ℝ}
    (hT : 0 ≤ T) (hP : ContinuousOn P (Icc 0 T)) (hO : IsOpen O)
    (h0 : P 0 ∉ O) (hTOut : P T ∉ O) (hVO : closure V ⊆ O)
    (ht : t ∈ Icc 0 T) (htV : P t ∈ V) :
    let a : ℝ → ℝ := fun q => sSup {u ∈ Icc 0 q | P u ∉ O}
    let b : ℝ → ℝ := fun q => sInf {u ∈ Icc q T | P u ∉ O}
    let active : Set ℝ := {q | q ∈ Ioo 0 T ∧ P q ∈ O ∧
      ({u ∈ Icc (a q) (b q) | P u ∈ closure V}).Nonempty}
    let F : Set (ℝ × ℝ × ℝ × ℝ) :=
      {e | ∃ q ∈ active,
        e = (a q, b q,
          sInf {u ∈ Icc (a q) (b q) | P u ∈ closure V},
          sSup {u ∈ Icc (a q) (b q) | P u ∈ closure V})}
    ∃ a₀ b₀ τ σ : ℝ, (a₀, b₀, τ, σ) ∈ F ∧ τ ≤ t ∧ t ≤ σ := by
  let a : ℝ → ℝ := fun q => sSup {u ∈ Icc 0 q | P u ∉ O}
  let b : ℝ → ℝ := fun q => sInf {u ∈ Icc q T | P u ∉ O}
  let C : Set ℝ := {u ∈ Icc (a t) (b t) | P u ∈ closure V}
  let τ := sInf C
  let σ := sSup C
  have htO : P t ∈ O := hVO (subset_closure htV)
  have ht0 : 0 < t := lt_of_le_of_ne ht.1 (by
    intro h
    exact h0 (h.symm ▸ htO))
  have htT : t < T := lt_of_le_of_ne ht.2 (by
    intro h
    exact hTOut (h ▸ htO))
  have htstrict : t ∈ Ioo 0 T := ⟨ht0, htT⟩
  have hcomp := excursionComponentCode hT hP hO h0 hTOut htstrict htO
  dsimp only at hcomp
  have hcontact : C.Nonempty :=
    ⟨t, ⟨hcomp.2.1.le, hcomp.2.2.1.le⟩, subset_closure htV⟩
  have hcode := excursionContactCode hT hP hO h0 hTOut
    htstrict htO hVO hcontact
  dsimp only at hcode
  have hτt : τ ≤ t ∧ t ≤ σ := hcode.2.2.2.2.2 t
    ⟨hcomp.2.1.le, hcomp.2.2.1.le⟩ htV
  refine ⟨a t, b t, τ, σ, ?_, hτt.1, hτt.2⟩
  exact ⟨t, ⟨htstrict, htO, hcontact⟩, rfl⟩

end SupercriticalLQGUniqueness.Uniqueness.Toolkit.PlanarSeparation

 
