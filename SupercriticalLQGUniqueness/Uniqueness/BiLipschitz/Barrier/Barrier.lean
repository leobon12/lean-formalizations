import SupercriticalLQGUniqueness.Frozen.WeylScale
import LQGMetric.Topo.RectCross




 












set_option autoImplicit false

noncomputable section

open Set Filter Topology Function
open scoped ENNReal

namespace SupercriticalLQGUniqueness
namespace Uniqueness.BiLipschitz.Barrier

 
def forget (D : LSCMetric) : D.Space → ℂ := id

theorem forget_pt (D : LSCMetric) (z : ℂ) : forget D (D.pt z) = z := rfl

theorem edist_pt (D : LSCMetric) (z w : ℂ) : edist (D.pt z) (D.pt w) = D (z, w) := rfl

 

theorem eq_of_tendsto_of_tendsto_pt (D : LSCMetric) {u : ℕ → ℂ} {x y : ℂ}
    (hy : Tendsto u atTop (𝓝 y)) (hx : Tendsto (fun n => D.pt (u n)) atTop (𝓝 (D.pt x))) :
    y = x := by
  have h0 : Tendsto (fun n => D (u n, x)) atTop (𝓝 0) := by
    have := (tendsto_iff_edist_tendsto_0).1 hx
    simpa only [edist_pt] using this
  by_contra hne
  have hpos : 0 < D (y, x) := by
    rcases eq_zero_or_pos (D (y, x)) with h | h
    · exact absurd (D.isExtMetric.2.1 y x h) hne
    · exact h
  obtain ⟨c, hc0, hcD⟩ := exists_between hpos
  have hlsc : ∀ᶠ p in 𝓝 (y, x), c < D p := D.lowerSemicontinuous (y, x) c hcD
  have hpair : Tendsto (fun n => (u n, x)) atTop (𝓝 (y, x)) :=
    hy.prodMk_nhds tendsto_const_nhds
  have h1 : ∀ᶠ n in atTop, c < D (u n, x) := hpair.eventually hlsc
  have h2 : ∀ᶠ n in atTop, D (u n, x) < c := h0.eventually (gt_mem_nhds hc0)
  obtain ⟨n, hn1, hn2⟩ := (h1.and h2).exists
  exact lt_asymm hn1 hn2

 
theorem isClosed_pt_image (D : LSCMetric) {K : Set ℂ} (hK : IsCompact K) :
    IsClosed (D.pt '' K) := by
  refine IsSeqClosed.isClosed fun x p hx hp => ?_
  have hxK : ∀ n, forget D (x n) ∈ K := by
    intro n
    obtain ⟨z, hz, hzx⟩ := hx n
    rw [← hzx]
    exact hz
  obtain ⟨y, hyK, φ, hφ, hyφ⟩ := hK.tendsto_subseq hxK
  have hpφ : Tendsto (fun n => D.pt (forget D (x (φ n)))) atTop (𝓝 (D.pt (forget D p))) :=
    hp.comp hφ.tendsto_atTop
  have hyp : y = forget D p := eq_of_tendsto_of_tendsto_pt D hyφ hpφ
  exact ⟨y, hyK, hyp⟩

 

theorem continuousOn_forget (D : LSCMetric) {K : Set ℂ} (hK : IsCompact K) :
    ContinuousOn (forget D) (D.pt '' K) := by
  rw [continuousOn_iff_isClosed]
  intro t ht
  refine ⟨D.pt '' (t ∩ K), isClosed_pt_image D (hK.inter_left ht), ?_⟩
  ext z
  constructor
  · rintro ⟨hzt, w, hwK, rfl⟩
    exact ⟨⟨w, ⟨hzt, hwK⟩, rfl⟩, ⟨w, hwK, rfl⟩⟩
  · rintro ⟨⟨w, ⟨hwt, hwK⟩, rfl⟩, -⟩
    exact ⟨hwt, ⟨w, hwK, rfl⟩⟩

 
theorem continuousOn_of_mapsTo_compact (D : LSCMetric) {P : ℝ → ℂ} {a b : ℝ}
    (hP : D.IsCurve P a b) {K : Set ℂ} (hK : IsCompact K) (hPK : ∀ t ∈ Icc a b, P t ∈ K) :
    ContinuousOn P (Icc a b) := by
  have hmaps : MapsTo (D.pt ∘ P) (Icc a b) (D.pt '' K) := fun t ht => ⟨P t, hPK t ht, rfl⟩
  exact (continuousOn_forget D hK).comp hP.2 hmaps

 
theorem continuousOn_of_isBounded (D : LSCMetric) {P : ℝ → ℂ} {a b : ℝ}
    (hP : D.IsCurve P a b) (hb : Bornology.IsBounded (P '' Icc a b)) :
    ContinuousOn P (Icc a b) := by
  obtain ⟨R, hR⟩ := hb.subset_closedBall 0
  exact continuousOn_of_mapsTo_compact D hP (isCompact_closedBall 0 R)
    fun t ht => hR ⟨t, ht, rfl⟩

 

section Sierpinski

variable {a b : ℝ} (F : ℕ → Set ℝ)

open Classical in
 
def colour (t : ℝ) : ℕ := if h : ∃ n, t ∈ F n then h.choose else 0

theorem mem_colour {t : ℝ} (h : ∃ n, t ∈ F n) : t ∈ F (colour F t) := by
  classical
  simp only [colour, h, ↓reduceDIte]
  exact h.choose_spec

theorem colour_eq {F : ℕ → Set ℝ} (hdisj : Pairwise (Disjoint on F)) {t : ℝ} {n : ℕ}
    (ht : t ∈ F n) : colour F t = n := by
  by_contra hne
  exact Set.disjoint_left.1 (hdisj hne) (mem_colour F ⟨n, ht⟩) ht

 

theorem avoid_step (hF : ∀ n, IsClosed (F n)) (hdisj : Pairwise (Disjoint on F))
    (hcov : Icc a b ⊆ ⋃ n, F n) (n : ℕ) {u v : ℝ} (hu : a ≤ u) (huv : u < v) (hv : v ≤ b)
    (hc : colour F u ≠ colour F v) :
    ∃ u' v', u ≤ u' ∧ u' < v' ∧ v' ≤ v ∧ colour F u' ≠ colour F v' ∧
      ∀ t ∈ Icc u' v', t ∉ F n := by
  have hcovt : ∀ t, a ≤ t → t ≤ b → ∃ m, t ∈ F m := fun t h1 h2 =>
    mem_iUnion.1 (hcov ⟨h1, h2⟩)
  by_cases hS : ∀ t ∈ Icc u v, t ∉ F n
  · exact ⟨u, v, le_rfl, huv, le_rfl, hc, hS⟩
  push Not at hS
  obtain ⟨t₀, ht₀, ht₀F⟩ := hS
  set S := F n ∩ Icc u v with hSdef
  have hSne : S.Nonempty := ⟨t₀, ht₀F, ht₀⟩
  have hSc : IsClosed S := (hF n).inter isClosed_Icc
  by_cases hun : u ∈ F n
  · 
    have hvn : v ∉ F n := fun hvF =>
      hc ((colour_eq hdisj hun).trans (colour_eq hdisj hvF).symm)
    have hSb : BddAbove S := ⟨v, fun t ht => ht.2.2⟩
    set s := sSup S with hsdef
    have hsS : s ∈ S := hSc.csSup_mem hSne hSb
    have hsv : s < v := lt_of_le_of_ne hsS.2.2 fun h => hvn (h ▸ hsS.1)
    have hgap : ∀ t ∈ Ioc s v, t ∉ F n := fun t ht htF =>
      (not_le.2 ht.1) (le_csSup hSb ⟨htF, hsS.2.1.trans ht.1.le, ht.2⟩)
    have hw : ∃ w ∈ Ioc s v, colour F w ≠ colour F v := by
      by_contra hall
      push Not at hall
      have hsub : Ioc s v ⊆ F (colour F v) := fun w hw => by
        have := mem_colour F (hcovt w (hu.trans (hsS.2.1.trans hw.1.le)) (hw.2.trans hv))
        rwa [hall w hw] at this
      have hcl : s ∈ closure (Ioc s v) := by
        rw [closure_Ioc hsv.ne]
        exact ⟨le_rfl, hsv.le⟩
      have hsF : s ∈ F (colour F v) := (hF _).closure_subset_iff.2 hsub hcl
      have hvc : colour F v ≠ n := fun h =>
        hvn (h ▸ mem_colour F (hcovt v (hu.trans huv.le) hv))
      exact Set.disjoint_left.1 (hdisj hvc) hsF hsS.1
    obtain ⟨w, hwI, hwc⟩ := hw
    have hwv : w < v := lt_of_le_of_ne hwI.2 fun h => hwc (h ▸ rfl)
    exact ⟨w, v, hsS.2.1.trans hwI.1.le, hwv, le_rfl, hwc,
      fun t ht => hgap t ⟨hwI.1.trans_le ht.1, ht.2⟩⟩
  · 
    have hSb : BddBelow S := ⟨u, fun t ht => ht.2.1⟩
    set s := sInf S with hsdef
    have hsS : s ∈ S := hSc.csInf_mem hSne hSb
    have hus : u < s := lt_of_le_of_ne hsS.2.1 fun h => hun (h ▸ hsS.1)
    have hgap : ∀ t ∈ Ico u s, t ∉ F n := fun t ht htF =>
      (not_le.2 ht.2) (csInf_le hSb ⟨htF, ht.1, ht.2.le.trans hsS.2.2⟩)
    have hw : ∃ w ∈ Ico u s, colour F w ≠ colour F u := by
      by_contra hall
      push Not at hall
      have hsub : Ico u s ⊆ F (colour F u) := fun w hw => by
        have := mem_colour F (hcovt w (hu.trans hw.1) (hw.2.le.trans (hsS.2.2.trans hv)))
        rwa [hall w hw] at this
      have hcl : s ∈ closure (Ico u s) := by
        rw [closure_Ico hus.ne]
        exact ⟨hus.le, le_rfl⟩
      have hsF : s ∈ F (colour F u) := (hF _).closure_subset_iff.2 hsub hcl
      have huc : colour F u ≠ n := fun h =>
        hun (h ▸ mem_colour F (hcovt u hu (huv.le.trans hv)))
      exact Set.disjoint_left.1 (hdisj huc) hsF hsS.1
    obtain ⟨w, hwI, hwc⟩ := hw
    have huw : u < w := lt_of_le_of_ne hwI.1 fun h => hwc (h ▸ rfl)
    exact ⟨u, w, le_rfl, huw, hwI.2.le.trans hsS.2.2, hwc.symm,
      fun t ht => hgap t ⟨ht.1, ht.2.trans_lt hwI.2⟩⟩

 

theorem sierpinski_Icc (hF : ∀ n, IsClosed (F n)) (hdisj : Pairwise (Disjoint on F))
    (hcov : Icc a b ⊆ ⋃ n, F n) : ∃ n, Icc a b ⊆ F n := by
  by_contra hne
  push Not at hne
  have hab : a ≤ b := by
    by_contra h
    exact hne 0 (by rw [Icc_eq_empty h]; exact empty_subset _)
  have hcova : ∃ m, a ∈ F m := mem_iUnion.1 (hcov ⟨le_rfl, hab⟩)
  
  obtain ⟨t, ht, htF⟩ := not_subset.1 (hne (colour F a))
  have hcovt : ∃ m, t ∈ F m := mem_iUnion.1 (hcov ht)
  have hct : colour F a ≠ colour F t := fun h => htF (h ▸ mem_colour F hcovt)
  have hat : a < t := lt_of_le_of_ne ht.1 fun h => hct (h ▸ rfl)
  
  let G := {p : ℝ × ℝ // a ≤ p.1 ∧ p.1 < p.2 ∧ p.2 ≤ b ∧ colour F p.1 ≠ colour F p.2}
  have step : ∀ (n : ℕ) (p : G), ∃ q : G, p.1.1 ≤ q.1.1 ∧ q.1.2 ≤ p.1.2 ∧
      ∀ s ∈ Icc q.1.1 q.1.2, s ∉ F n := by
    intro n p
    obtain ⟨u', v', h1, h2, h3, h4, h5⟩ :=
      avoid_step F hF hdisj hcov n p.2.1 p.2.2.1 p.2.2.2.1 p.2.2.2.2
    exact ⟨⟨(u', v'), p.2.1.trans h1, h2, h3.trans p.2.2.2.1, h4⟩, h1, h3, h5⟩
  choose next hnext1 hnext2 hnext3 using step
  let p₀ : G := ⟨(a, t), le_rfl, hat, ht.2, hct⟩
  let seq : ℕ → G := fun k => Nat.rec p₀ (fun k p => next k p) k
  have hseq : ∀ k, seq (k + 1) = next k (seq k) := fun k => rfl
  let u : ℕ → ℝ := fun k => (seq k).1.1
  let v : ℕ → ℝ := fun k => (seq k).1.2
  have hu_mono : Monotone u := monotone_nat_of_le_succ fun k => by
    show (seq k).1.1 ≤ (seq (k + 1)).1.1
    rw [hseq]; exact hnext1 k (seq k)
  have hv_anti : Antitone v := antitone_nat_of_succ_le fun k => by
    show (seq (k + 1)).1.2 ≤ (seq k).1.2
    rw [hseq]; exact hnext2 k (seq k)
  have huv : ∀ k, u k < v k := fun k => (seq k).2.2.1
  have huv' : ∀ i j, u i ≤ v j := fun i j =>
    (hu_mono (le_max_left i j)).trans ((huv _).le.trans (hv_anti (le_max_right i j)))
  have hbdd : BddAbove (range u) := ⟨v 0, by rintro _ ⟨i, rfl⟩; exact huv' i 0⟩
  set x := ⨆ k, u k with hx
  have hux : ∀ k, u k ≤ x := fun k => le_ciSup hbdd k
  have hxv : ∀ k, x ≤ v k := fun k => ciSup_le fun i => huv' i k
  have hxab : x ∈ Icc a b := ⟨(seq 0).2.1.trans (hux 0), (hxv 0).trans (seq 0).2.2.2.1⟩
  have hcovx : ∃ m, x ∈ F m := mem_iUnion.1 (hcov hxab)
  set m := colour F x
  have hxF : x ∈ F m := mem_colour F hcovx
  have hxnot : x ∉ F m := by
    have := hnext3 m (seq m) x
    rw [← hseq] at this
    exact this ⟨hux (m + 1), hxv (m + 1)⟩
  exact hxnot hxF

end Sierpinski

 

 

theorem exists_radius_of_not_isBounded (D : LSCMetric) {P : ℝ → ℂ} {a b : ℝ}
    (hP : D.IsCurve P a b) (hunb : ¬ Bornology.IsBounded (P '' Icc a b)) :
    ∃ R₀ : ℝ, ∀ ρ : ℝ, R₀ ≤ ρ → ∃ t ∈ Icc a b, ‖P t‖ = ρ := by
  by_contra hcon
  push Not at hcon
  choose rad hrad homit using hcon
  let ρ : ℕ → ℝ := fun k => Nat.rec (rad 0) (fun _ r => rad (r + 1)) k
  have hρ0 : ρ 0 = rad 0 := rfl
  have hρs : ∀ k, ρ (k + 1) = rad (ρ k + 1) := fun k => rfl
  have hρ_succ : ∀ k, ρ k + 1 ≤ ρ (k + 1) := fun k => by rw [hρs]; exact hrad _
  have hρ_ge : ∀ k : ℕ, (k : ℝ) ≤ ρ k := by
    intro k
    induction k with
    | zero => simpa [hρ0] using hrad 0
    | succ k ih => push_cast; linarith [hρ_succ k]
  have hρ_mono : StrictMono ρ := strictMono_nat_of_lt_succ fun k => by linarith [hρ_succ k]
  have hρ_omit : ∀ k, ∀ t ∈ Icc a b, ‖P t‖ ≠ ρ k := by
    intro k
    cases k with
    | zero => exact homit 0
    | succ k => rw [hρs]; exact homit _
  let lo : ℕ → ℝ := fun k => Nat.casesOn k (-1) (fun j => ρ j)
  have hlo0 : lo 0 = -1 := rfl
  have hlos : ∀ j, lo (j + 1) = ρ j := fun j => rfl
  let band : ℕ → Set ℂ := fun k => {z | lo k ≤ ‖z‖ ∧ ‖z‖ ≤ ρ k}
  have hband_compact : ∀ k, IsCompact (band k) := by
    intro k
    refine (isCompact_closedBall (0 : ℂ) (ρ k)).of_isClosed_subset ?_ ?_
    · exact (isClosed_le continuous_const continuous_norm).inter
        (isClosed_le continuous_norm continuous_const)
    · intro z hz
      simpa [Metric.mem_closedBall, dist_zero_right] using hz.2
  let F : ℕ → Set ℝ := fun k => Icc a b ∩ (D.pt ∘ P) ⁻¹' (D.pt '' band k)
  have hF_eq : ∀ k t, t ∈ F k ↔ t ∈ Icc a b ∧ P t ∈ band k := by
    intro k t
    constructor
    · rintro ⟨ht, z, hz, hzt⟩
      have hz' : z = P t := hzt
      exact ⟨ht, hz' ▸ hz⟩
    · rintro ⟨ht, hb⟩
      exact ⟨ht, P t, hb, rfl⟩
  have hFc : ∀ k, IsClosed (F k) := fun k =>
    hP.2.preimage_isClosed_of_isClosed isClosed_Icc (isClosed_pt_image D (hband_compact k))
  have hdisj : Pairwise (Disjoint on F) := by
    have key : ∀ i j, i < j → Disjoint (F i) (F j) := by
      intro i j hij
      rw [Set.disjoint_left]
      intro t hti htj
      rw [hF_eq] at hti htj
      obtain ⟨j', rfl⟩ : ∃ j', j = j' + 1 := ⟨j - 1, by omega⟩
      have h1 : ρ i ≤ ρ j' := hρ_mono.monotone (by omega)
      have h2 : lo (j' + 1) ≤ ‖P t‖ := htj.2.1
      rw [hlos] at h2
      exact hρ_omit i t hti.1 (le_antisymm hti.2.2 (h1.trans h2))
    intro i j hij
    rcases lt_or_gt_of_ne hij with h | h
    · exact key i j h
    · exact (key j i h).symm
  have hcovF : Icc a b ⊆ ⋃ k, F k := by
    intro t ht
    have hex : ∃ k, ‖P t‖ ≤ ρ k := by
      obtain ⟨k, hk⟩ := exists_nat_ge ‖P t‖
      exact ⟨k, hk.trans (hρ_ge k)⟩
    obtain ⟨k, hk, hkmin'⟩ := (wellFounded_lt (α := ℕ)).has_min {k | ‖P t‖ ≤ ρ k} hex
    have hkmin : ∀ j < k, ¬ ‖P t‖ ≤ ρ j := fun j hj hle => hkmin' j hle hj
    refine mem_iUnion.2 ⟨k, (hF_eq k t).2 ⟨ht, ?_, hk⟩⟩
    rcases Nat.eq_zero_or_pos k with hk0 | hkpos
    · rw [hk0, hlo0]
      linarith [norm_nonneg (P t)]
    · obtain ⟨j, hj⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
      have hmin := hkmin j (by omega)
      push Not at hmin
      rw [hj, hlos]
      exact hmin.le
  obtain ⟨k, hk⟩ := sierpinski_Icc F hFc hdisj hcovF
  apply hunb
  refine (Metric.isBounded_closedBall (x := (0 : ℂ)) (r := ρ k)).subset ?_
  rintro _ ⟨t, ht, rfl⟩
  have := ((hF_eq k t).1 (hk ht)).2.2
  simpa [Metric.mem_closedBall, dist_zero_right] using this

 

 
def dyadicAnnulus (n : ℕ) : EuclideanAnnulus :=
  ⟨(0, ((2 : ℝ) ^ n, (2 : ℝ) ^ (n + 1))), by positivity,
    pow_lt_pow_right₀ one_lt_two (Nat.lt_succ_self n)⟩

 

def Barrier (D : LSCMetric) : Prop :=
  ∀ n₀ M : ℕ, ∃ n, n₀ ≤ n ∧ (M : ℝ≥0∞) < acrossDist D (dyadicAnnulus n)

theorem acrossDist_dyadic_le (D : LSCMetric) (n : ℕ) {x y : ℂ} (hx : ‖x‖ = 2 ^ n)
    (hy : ‖y‖ = 2 ^ (n + 1)) : acrossDist D (dyadicAnnulus n) ≤ D (x, y) := by
  refine iInf₂_le_of_le x ?_ (iInf₂_le y ?_)
  · show x ∈ Metric.sphere (0 : ℂ) ((2 : ℝ) ^ n)
    simpa [mem_sphere_zero_iff_norm] using hx
  · show y ∈ Metric.sphere (0 : ℂ) ((2 : ℝ) ^ (n + 1))
    simpa [mem_sphere_zero_iff_norm] using hy

 

theorem isBounded_of_barrier (D : LSCMetric) (hB : Barrier D) {P : ℝ → ℂ} {a b : ℝ}
    (hP : D.IsCurve P a b) (hlen : D.len P a b ≠ ⊤) : Bornology.IsBounded (P '' Icc a b) := by
  by_contra hunb
  obtain ⟨R₀, hR₀⟩ := exists_radius_of_not_isBounded D hP hunb
  obtain ⟨M, hM⟩ := ENNReal.exists_nat_gt hlen
  obtain ⟨n₀, hn₀⟩ := pow_unbounded_of_one_lt R₀ (one_lt_two : (1 : ℝ) < 2)
  obtain ⟨n, hn, hacross⟩ := hB n₀ M
  have h2n : R₀ ≤ (2 : ℝ) ^ n := hn₀.le.trans (pow_le_pow_right₀ one_le_two hn)
  obtain ⟨s, hs, hPs⟩ := hR₀ _ h2n
  obtain ⟨t, ht, hPt⟩ :=
    hR₀ ((2 : ℝ) ^ (n + 1)) (h2n.trans (pow_le_pow_right₀ one_le_two n.le_succ))
  have h1 := acrossDist_dyadic_le D n hPs hPt
  have h2 : D (P s, P t) ≤ D.len P a b := eVariationOn.edist_le (D.pt ∘ P) hs ht
  exact lt_asymm hM (hacross.trans_le (h1.trans h2))

 
theorem continuousOn_of_barrier (D : LSCMetric) (hB : Barrier D) {P : ℝ → ℂ} {a b : ℝ}
    (hP : D.IsCurve P a b) (hlen : D.len P a b ≠ ⊤) : ContinuousOn P (Icc a b) :=
  continuousOn_of_isBounded D hP (isBounded_of_barrier D hB hP hlen)

 

 
theorem exists_pos_le_sphere (D : LSCMetric) (x : ℂ) {R : ℝ} (hR : 0 < R) :
    ∃ δ : ℝ≥0∞, 0 < δ ∧ ∀ z ∈ Metric.sphere x R, δ ≤ D (x, z) := by
  have hne : (Metric.sphere x R).Nonempty := NormedSpace.sphere_nonempty.2 hR.le
  have hlsc : LowerSemicontinuousOn (fun z => D (x, z)) (Metric.sphere x R) :=
    (D.lowerSemicontinuous.comp (continuous_const.prodMk continuous_id)).lowerSemicontinuousOn _
  obtain ⟨z₀, hz₀, hmin⟩ := hlsc.exists_isMinOn hne (isCompact_sphere x R)
  refine ⟨D (x, z₀), ?_, fun z hz => hmin hz⟩
  rcases eq_zero_or_pos (D (x, z₀)) with h | h
  · have hxz := D.isExtMetric.2.1 x z₀ h
    subst hxz
    rw [Metric.mem_sphere, dist_self] at hz₀
    exact absurd hz₀ hR.ne
  · exact h

 


theorem continuous_forget_of_barrier (D : LSCMetric) (hB : Barrier D) (hL : D.IsLengthSpace) :
    Continuous (forget D) := by
  rw [continuous_iff_continuousAt]
  intro x
  rw [ContinuousAt, (Metric.nhds_basis_eball).tendsto_iff Metric.nhds_basis_ball]
  intro ε hε
  obtain ⟨δ, hδ, hδle⟩ := exists_pos_le_sphere D (forget D x) (half_pos hε)
  refine ⟨δ, hδ, fun y hy => ?_⟩
  rw [Metric.mem_eball] at hy
  rw [Metric.mem_ball]
  by_contra hfar
  push Not at hfar
  set x' : ℂ := forget D x
  set y' : ℂ := forget D y
  have hxy : D (x', y') < δ := by
    have : edist y x = D (y', x') := rfl
    rw [this, D.isExtMetric.2.2.1] at hy
    exact hy
  obtain ⟨r, hr0, hrlt⟩ := ENNReal.lt_iff_exists_add_pos_lt.1 hxy
  obtain ⟨P, a, b, hP, hPa, hPb, hlen⟩ :=
    hL x' y' (hxy.trans_le le_top) (r : ℝ) (by exact_mod_cast hr0)
  rw [ENNReal.ofReal_coe_nnreal] at hlen
  have hlenδ : D.len P a b < δ := hlen.trans_lt hrlt
  have hcont : ContinuousOn P (Icc a b) :=
    continuousOn_of_barrier D hB hP (hlenδ.trans_le le_top).ne
  have hf : ContinuousOn (fun t => dist (P t) x') (Icc a b) :=
    (continuous_id.dist continuous_const).comp_continuousOn hcont
  obtain ⟨τ, hτ, hfτ⟩ := intermediate_value_Icc hP.1 hf
    (show ε / 2 ∈ Icc (dist (P a) x') (dist (P b) x') by
      rw [hPa, hPb, dist_self]
      exact ⟨(half_pos hε).le, (half_lt_self hε).le.trans hfar⟩)
  have hsph : P τ ∈ Metric.sphere x' (ε / 2) := hfτ
  have h1 : δ ≤ D (x', P τ) := hδle _ hsph
  have h2 : D (x', P τ) ≤ D.len P a b := by
    have := eVariationOn.edist_le (D.pt ∘ P) (left_mem_Icc.2 hP.1) hτ
    rw [← hPa]
    exact this
  exact absurd (h1.trans h2) (not_le.2 hlenδ)

 
theorem continuousOn_of_barrier_of_length (D : LSCMetric) (hB : Barrier D)
    (hL : D.IsLengthSpace) {P : ℝ → ℂ} {a b : ℝ} (hP : D.IsCurve P a b) :
    ContinuousOn P (Icc a b) :=
  (continuous_forget_of_barrier D hB hL).comp_continuousOn hP.2

 

 
def closedAnn (c : ℂ) (r₁ r₂ : ℝ) : Set ℂ := {z | r₁ ≤ ‖z - c‖ ∧ ‖z - c‖ ≤ r₂}

theorem internal_le_len' (D : LSCMetric) {Y : Set ℂ} {P : ℝ → ℂ} {s t : ℝ}
    (hP : D.IsCurve P s t) (hY : ∀ u ∈ Icc s t, P u ∈ Y) :
    D.internal Y (⟨P s, hY s (left_mem_Icc.2 hP.1)⟩, ⟨P t, hY t (right_mem_Icc.2 hP.1)⟩) ≤
      D.len P s t :=
  iInf_le_of_le P (iInf_le_of_le s (iInf_le_of_le t (iInf_le_of_le hP (iInf_le_of_le hY
    (iInf_le_of_le rfl (iInf_le _ rfl))))))

theorem edist_le_internal' (D : LSCMetric) (Y : Set ℂ) (p : Y × Y) :
    D ((p.1 : ℂ), (p.2 : ℂ)) ≤ D.internal Y p := by
  refine le_iInf fun P => le_iInf fun s => le_iInf fun t => le_iInf fun hP => le_iInf fun _ =>
    le_iInf fun hs => le_iInf fun ht => ?_
  have := eVariationOn.edist_le (D.pt ∘ P) (left_mem_Icc.2 hP.1) (right_mem_Icc.2 hP.1)
  rw [← hs, ← ht]
  exact this

 




theorem iInf_internal_le (D : LSCMetric) (hB : Barrier D) (hL : D.IsLengthSpace)
    {c : ℂ} {r₁ r₂ : ℝ} (hr : r₁ ≤ r₂) {Y : Set ℂ} (hY : closedAnn c r₁ r₂ ⊆ Y) {x y : ℂ}
    (hx : ‖x - c‖ ≤ r₁) (hy : r₂ ≤ ‖y - c‖) :
    (⨅ (p : Y × Y) (_ : ‖(p.1 : ℂ) - c‖ = r₁) (_ : ‖(p.2 : ℂ) - c‖ = r₂), D.internal Y p) ≤
      D (x, y) := by
  refine ENNReal.le_of_forall_pos_le_add fun ε hε hlt => ?_
  obtain ⟨P, a, b, hP, hPa, hPb, hlen⟩ := hL x y hlt (ε : ℝ) (by exact_mod_cast hε)
  rw [ENNReal.ofReal_coe_nnreal] at hlen
  have hfin : D.len P a b ≠ ⊤ :=
    (hlen.trans_lt (ENNReal.add_lt_top.2 ⟨hlt, ENNReal.coe_lt_top⟩)).ne
  have hcont := continuousOn_of_barrier D hB hP hfin
  have hf : ContinuousOn (fun t => ‖P t - c‖) (Icc a b) :=
    (continuous_norm.comp (continuous_id.sub continuous_const)).comp_continuousOn hcont
  obtain ⟨s, t, has, hst, htb, hfs, hft, hin⟩ :=
    LQGMetric.RectCross.exists_sub_crossing hP.1 hf hr (by simpa [hPa] using hx)
      (by simpa [hPb] using hy)
  have hPst : D.IsCurve P s t := ⟨hst, hP.2.mono (Icc_subset_Icc has htb)⟩
  have hYst : ∀ u ∈ Icc s t, P u ∈ Y := fun u hu => hY (hin u hu)
  calc (⨅ (p : Y × Y) (_ : ‖(p.1 : ℂ) - c‖ = r₁) (_ : ‖(p.2 : ℂ) - c‖ = r₂), D.internal Y p)
      ≤ D.internal Y (⟨P s, hYst s (left_mem_Icc.2 hst)⟩, ⟨P t, hYst t (right_mem_Icc.2 hst)⟩) := by
        refine iInf_le_of_le
          (⟨P s, hYst s (left_mem_Icc.2 hst)⟩, ⟨P t, hYst t (right_mem_Icc.2 hst)⟩) ?_
        exact iInf_le_of_le hfs (iInf_le_of_le hft le_rfl)
    _ ≤ D.len P s t := internal_le_len' D hPst hYst
    _ ≤ D.len P a b := eVariationOn.mono _ (Icc_subset_Icc has htb)
    _ ≤ D (x, y) + ε := hlen

 


theorem acrossDist_eq_iInf_internal (D : LSCMetric) (hB : Barrier D) (hL : D.IsLengthSpace)
    (A : EuclideanAnnulus) {Y : Set ℂ}
    (hY : closedAnn A.center A.innerRadius A.outerRadius ⊆ Y) :
    acrossDist D A = ⨅ (p : Y × Y) (_ : ‖(p.1 : ℂ) - A.center‖ = A.innerRadius)
      (_ : ‖(p.2 : ℂ) - A.center‖ = A.outerRadius), D.internal Y p := by
  apply le_antisymm
  · refine le_iInf fun p => le_iInf fun h1 => le_iInf fun h2 => ?_
    calc acrossDist D A ≤ D ((p.1 : ℂ), (p.2 : ℂ)) :=
          iInf₂_le_of_le _ (mem_sphere_iff_norm.2 h1) (iInf₂_le _ (mem_sphere_iff_norm.2 h2))
      _ ≤ D.internal Y p := edist_le_internal' D Y p
  · refine le_iInf₂ fun x hx => le_iInf₂ fun y hy => ?_
    exact iInf_internal_le D hB hL A.2.2.le hY (mem_sphere_iff_norm.1 hx).le
      (mem_sphere_iff_norm.1 hy).ge

 
def shrinkAnn (A : EuclideanAnnulus) (n : ℕ) : EuclideanAnnulus :=
  ⟨(A.center, (A.innerRadius + (A.outerRadius - A.innerRadius) / ((n : ℝ) + 2), A.outerRadius)),
    by
      have h1 : 0 < A.innerRadius := A.2.1
      have h2 : 0 < A.outerRadius - A.innerRadius := sub_pos.2 A.2.2
      show 0 < A.innerRadius + (A.outerRadius - A.innerRadius) / ((n : ℝ) + 2)
      positivity,
    by
      have h2 : 0 < A.outerRadius - A.innerRadius := sub_pos.2 A.2.2
      have hn : (1 : ℝ) < (n : ℝ) + 2 := by linarith [n.cast_nonneg (α := ℝ)]
      show A.innerRadius + (A.outerRadius - A.innerRadius) / ((n : ℝ) + 2) < A.outerRadius
      have : (A.outerRadius - A.innerRadius) / ((n : ℝ) + 2) < A.outerRadius - A.innerRadius :=
        div_lt_self h2 hn
      linarith⟩

theorem shrinkAnn_center (A : EuclideanAnnulus) (n : ℕ) : (shrinkAnn A n).center = A.center := rfl

theorem shrinkAnn_outer (A : EuclideanAnnulus) (n : ℕ) :
    (shrinkAnn A n).outerRadius = A.outerRadius := rfl

theorem shrinkAnn_inner (A : EuclideanAnnulus) (n : ℕ) :
    (shrinkAnn A n).innerRadius =
      A.innerRadius + (A.outerRadius - A.innerRadius) / ((n : ℝ) + 2) := rfl

 
theorem acrossDist_shrink_le (D : LSCMetric) (hB : Barrier D) (hL : D.IsLengthSpace)
    (A : EuclideanAnnulus) (n : ℕ) : acrossDist D (shrinkAnn A n) ≤ acrossDist D A := by
  rw [acrossDist_eq_iInf_internal D hB hL (shrinkAnn A n) (Y := univ) (subset_univ _)]
  refine le_iInf₂ fun x hx => le_iInf₂ fun y hy => ?_
  have hxr : ‖x - A.center‖ = A.innerRadius := mem_sphere_iff_norm.1 hx
  have hyr : ‖y - A.center‖ = A.outerRadius := mem_sphere_iff_norm.1 hy
  have hη : 0 ≤ (A.outerRadius - A.innerRadius) / ((n : ℝ) + 2) :=
    div_nonneg (sub_pos.2 A.2.2).le (by positivity)
  have h1 : ‖x - (shrinkAnn A n).center‖ ≤ (shrinkAnn A n).innerRadius := by
    rw [shrinkAnn_center, shrinkAnn_inner, hxr]; linarith
  have h2 : (shrinkAnn A n).outerRadius ≤ ‖y - (shrinkAnn A n).center‖ := by
    rw [shrinkAnn_center, shrinkAnn_outer, hyr]
  exact iInf_internal_le D hB hL (c := (shrinkAnn A n).center)
    (r₁ := (shrinkAnn A n).innerRadius) (r₂ := (shrinkAnn A n).outerRadius)
    (shrinkAnn A n).2.2.le (subset_univ _) h1 h2

 

theorem acrossDist_le_iSup_shrink (D : LSCMetric) (A : EuclideanAnnulus) :
    acrossDist D A ≤ ⨆ n, acrossDist D (shrinkAnn A n) := by
  set L := ⨆ n, acrossDist D (shrinkAnn A n) with hLdef
  by_cases hLtop : L = ⊤
  · rw [hLtop]; exact le_top
  set c := A.center
  set r₁ := A.innerRadius
  set r₂ := A.outerRadius
  have hslack : ∀ n : ℕ, acrossDist D (shrinkAnn A n) < L + (n : ℝ≥0∞)⁻¹ := fun n =>
    (le_iSup (fun n => acrossDist D (shrinkAnn A n)) n).trans_lt
      (ENNReal.lt_add_right hLtop (ENNReal.inv_pos.2 (ENNReal.natCast_ne_top n)).ne')
  have hchoose : ∀ n : ℕ, ∃ x y : ℂ, ‖x - c‖ = (shrinkAnn A n).innerRadius ∧
      ‖y - c‖ = r₂ ∧ D (x, y) < L + (n : ℝ≥0∞)⁻¹ := by
    intro n
    have h := hslack n
    obtain ⟨x, hx⟩ := iInf_lt_iff.1 h
    obtain ⟨hxm, hx⟩ := iInf_lt_iff.1 hx
    obtain ⟨y, hy⟩ := iInf_lt_iff.1 hx
    obtain ⟨hym, hy⟩ := iInf_lt_iff.1 hy
    exact ⟨x, y, mem_sphere_iff_norm.1 hxm, mem_sphere_iff_norm.1 hym, hy⟩
  choose x y hx hy hxy using hchoose
  have hK : IsCompact (Metric.closedBall c r₂ ×ˢ Metric.closedBall c r₂) :=
    (isCompact_closedBall c r₂).prod (isCompact_closedBall c r₂)
  have hη : ∀ n : ℕ, (shrinkAnn A n).innerRadius ≤ r₂ := fun n => (shrinkAnn A n).2.2.le
  have hmem : ∀ n, (x n, y n) ∈ Metric.closedBall c r₂ ×ˢ Metric.closedBall c r₂ := fun n =>
    ⟨by rw [Metric.mem_closedBall, dist_eq_norm, hx n]; exact hη n,
      by rw [Metric.mem_closedBall, dist_eq_norm, hy n]⟩
  obtain ⟨p, -, φ, hφ, hpφ⟩ := hK.tendsto_subseq hmem
  
  have hrad : Tendsto (fun n : ℕ => (shrinkAnn A n).innerRadius) atTop (𝓝 r₁) := by
    have h0 : Tendsto (fun n : ℕ => (r₂ - r₁) / ((n : ℝ) + 2)) atTop (𝓝 0) := by
      have := tendsto_const_div_atTop_nhds_zero_nat (𝕜 := ℝ) (r₂ - r₁)
      have h2 := (tendsto_add_atTop_iff_nat 2).2 this
      refine h2.congr fun n => ?_
      push_cast
      ring_nf
    simpa [shrinkAnn_inner] using (tendsto_const_nhds (x := r₁)).add h0
  have hp1 : ‖p.1 - c‖ = r₁ := by
    have h1 : Tendsto (fun k => ‖x (φ k) - c‖) atTop (𝓝 ‖p.1 - c‖) :=
      ((continuous_norm.comp (continuous_id.sub continuous_const)).tendsto _).comp
        ((continuous_fst.tendsto _).comp hpφ)
    have h2 : Tendsto (fun k => ‖x (φ k) - c‖) atTop (𝓝 r₁) := by
      exact (hrad.comp hφ.tendsto_atTop).congr fun k => (hx (φ k)).symm
    exact tendsto_nhds_unique h1 h2
  have hp2 : ‖p.2 - c‖ = r₂ := by
    have h1 : Tendsto (fun k => ‖y (φ k) - c‖) atTop (𝓝 ‖p.2 - c‖) :=
      ((continuous_norm.comp (continuous_id.sub continuous_const)).tendsto _).comp
        ((continuous_snd.tendsto _).comp hpφ)
    have h2 : Tendsto (fun k => ‖y (φ k) - c‖) atTop (𝓝 r₂) := by
      simp only [hy]; exact tendsto_const_nhds
    exact tendsto_nhds_unique h1 h2
  have hAp : acrossDist D A ≤ D p :=
    iInf₂_le_of_le p.1 (mem_sphere_iff_norm.2 hp1) (iInf₂_le p.2 (mem_sphere_iff_norm.2 hp2))
  refine hAp.trans (not_lt.1 fun hlt => ?_)
  obtain ⟨c', hLc', hc'p⟩ := exists_between hlt
  have hev1 : ∀ᶠ k in atTop, c' < D (x (φ k), y (φ k)) :=
    hpφ.eventually (D.lowerSemicontinuous p c' hc'p)
  have hslack0 : Tendsto (fun k => L + ((φ k : ℕ) : ℝ≥0∞)⁻¹) atTop (𝓝 (L + 0)) :=
    tendsto_const_nhds.add (ENNReal.tendsto_inv_nat_nhds_zero.comp hφ.tendsto_atTop)
  rw [add_zero] at hslack0
  have hev2 : ∀ᶠ k in atTop, L + ((φ k : ℕ) : ℝ≥0∞)⁻¹ < c' := hslack0.eventually (gt_mem_nhds hLc')
  obtain ⟨k, hk1, hk2⟩ := (hev1.and hev2).exists
  exact lt_asymm hk1 ((hxy (φ k)).trans hk2)

 

theorem acrossDist_eq_iSup_shrink (D : LSCMetric) (hB : Barrier D) (hL : D.IsLengthSpace)
    (A : EuclideanAnnulus) : acrossDist D A = ⨆ n, acrossDist D (shrinkAnn A n) :=
  le_antisymm (acrossDist_le_iSup_shrink D A) (iSup_le fun n => acrossDist_shrink_le D hB hL A n)

 



theorem acrossDist_eq_of_internal_eq (D D' : LSCMetric) (hB : Barrier D) (hB' : Barrier D')
    (hL : D.IsLengthSpace) (hL' : D'.IsLengthSpace) (A : EuclideanAnnulus) {R : ℝ}
    (hR : A.outerRadius < R)
    (hint : D.internal {z | A.innerRadius < ‖z - A.center‖ ∧ ‖z - A.center‖ < R} =
      D'.internal {z | A.innerRadius < ‖z - A.center‖ ∧ ‖z - A.center‖ < R}) :
    acrossDist D A = acrossDist D' A := by
  rw [acrossDist_eq_iSup_shrink D hB hL, acrossDist_eq_iSup_shrink D' hB' hL']
  refine iSup_congr fun n => ?_
  have hsub : closedAnn (shrinkAnn A n).center (shrinkAnn A n).innerRadius
      (shrinkAnn A n).outerRadius ⊆
        {z | A.innerRadius < ‖z - A.center‖ ∧ ‖z - A.center‖ < R} := by
    intro z hz
    rw [shrinkAnn_center, shrinkAnn_inner, shrinkAnn_outer] at hz
    have hη : 0 < (A.outerRadius - A.innerRadius) / ((n : ℝ) + 2) :=
      div_pos (sub_pos.2 A.2.2) (by positivity)
    exact ⟨by linarith [hz.1], hz.2.trans_lt hR⟩
  rw [acrossDist_eq_iInf_internal D hB hL _ hsub, acrossDist_eq_iInf_internal D' hB' hL' _ hsub,
    hint]

end Uniqueness.BiLipschitz.Barrier
end SupercriticalLQGUniqueness
