import HigherDimLQGContinuity.ForcingCount.LowerSteps
import HigherDimLQGMetric.Count.Pruning
import HigherDimLQGMetric.Count.ImageOut

/-!
# The lower multiplicity (4.18)

Packet Q9, Part B `b:lem-lowmult` ([C] p. 18–19, l. 936–971; NA2 items 18, 21, R11, R13). On the good event, for a
field `H ∈ B_𝔆` with `N_site ≥ k` eligible sites, at least `(N_site/k)^{m}` selections `Z` with `m ≤ #Z ≤ k` satisfy
`H ∈ A_Z`, for every `m ≤ ⌈κ k⌉`, `κ = a₀/(4A₀)`: the library's `pruning` with (h1)–(h3) of `LowerSteps`, and the
library's `card_image_out_ge` (both reused verbatim, ruling N9).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Filter Topology Set Metric
open scoped ENNReal

namespace HigherDimLQGContinuity

open HigherDimLQGMetric
open HigherDimLFPP (Rd e₁)

variable {d : ℕ}

section Good

open Classical

variable {K : CountData d} {𝔆 : Catalogue d}

theorem CountGood.pos {H : DistRd d} (hG : CountGood K 𝔆 H) {W : Finset (Rd d × K.cat.Label)}
    (hW : W ⊆ countUnivSites K 𝔆) : q9GoodInput K (addFun H (selBump K 𝔆.s W)) :=
  (hG.1 W (Finset.mem_powerset.2 hW)).1

theorem CountGood.neg {H : DistRd d} (hG : CountGood K 𝔆 H) {W : Finset (Rd d × K.cat.Label)}
    (hW : W ⊆ countUnivSites K 𝔆) : q9GoodInput K (addFun H (-selBump K 𝔆.s W)) :=
  (hG.1 W (Finset.mem_powerset.2 hW)).2

theorem CountGood.base {H : DistRd d} (hG : CountGood K 𝔆 H) : q9GoodInput K H := by
  have h := hG.pos (W := ∅) (Finset.empty_subset _)
  rwa [selBump_empty, addFun_zero] at h

theorem mem_countUnivSites {z : Rd d} (hz : z ∈ 𝔆.Z) (ℓ : K.cat.Label) : (z, ℓ) ∈ countUnivSites K 𝔆 := by
  simp only [countUnivSites, Finset.mem_product]
  exact ⟨hz, @Finset.mem_univ _ K.cat.fintypeLabel ℓ⟩

theorem q9_image_lab_subset {t : Finset (Rd d)} (ht : t ⊆ 𝔆.Z) (lab : Rd d → K.cat.Label) :
    t.image (fun z => (z, lab z)) ⊆ countUnivSites K 𝔆 := by
  intro p hp
  obtain ⟨z, hz, rfl⟩ := Finset.mem_image.1 hp
  exact mem_countUnivSites (ht hz) (lab z)

theorem q9_isSelection_image_lab {t : Finset (Rd d)} (ht : t ⊆ 𝔆.Z) (lab : Rd d → K.cat.Label) :
    IsSelection 𝔆 (t.image fun z => (z, lab z)) := by
  refine ⟨fun p hp => ?_, fun p hp q hq hpq => ?_⟩
  · obtain ⟨z, hz, rfl⟩ := Finset.mem_image.1 hp
    exact ht hz
  · obtain ⟨z, hz, rfl⟩ := Finset.mem_image.1 hp
    obtain ⟨z', hz', rfl⟩ := Finset.mem_image.1 hq
    simp only at hpq
    rw [hpq]

theorem q9_image_lab_injective (lab : Rd d → K.cat.Label) :
    Function.Injective fun t : Finset (Rd d) => t.image fun z => (z, lab z) := by
  intro t₁ t₂ h
  simp only at h
  ext z
  constructor
  · intro hz
    have hmem : (z, lab z) ∈ t₂.image fun z => (z, lab z) := h ▸ Finset.mem_image_of_mem _ hz
    obtain ⟨z', hz', he⟩ := Finset.mem_image.1 hmem
    rwa [← (Prod.mk.inj he).1]
  · intro hz
    have hmem : (z, lab z) ∈ t₁.image fun z => (z, lab z) := h.symm ▸ Finset.mem_image_of_mem _ hz
    obtain ⟨z', hz', he⟩ := Finset.mem_image.1 hmem
    rwa [← (Prod.mk.inj he).1]

end Good

/-- A sub-segment of a geodesic segment is a geodesic segment. -/
theorem q9_isGeodSeg_sub {D : ContMetric d} {P : ℝ → Rd d} {a c s t : ℝ} (hgeo : IsGeodSeg D P a c)
    (has : a ≤ s) (hst : s ≤ t) (htc : t ≤ c) : IsGeodSeg D P s t :=
  ⟨hst, hgeo.2.1.mono (Icc_subset_Icc has htc), q6_geod_subsegment hgeo has hst htc⟩

section Saving

variable {K : CountData d} {𝔆 : Catalogue d} {Hup sR Hlo b mc A0 d₀ Ap kp v θ ς δsep εnet εatt : ℝ}

open Classical in
/-- **(h1) The network saving of a set of eligible sites** with fixed valid labels. -/
theorem q9_saving (hK : CountHyp K 𝔆 Hup sR Hlo b mc A0 d₀ Ap kp v θ ς δsep εnet εatt)
    {H : DistRd d} (hG : CountGood K 𝔆 H) {t : Finset (Rd d)} (ht : t ⊆ 𝔆.Z)
    (lab : Rd d → K.cat.Label) (helig : ∀ z ∈ t, IsEligible K 𝔆 z H)
    (hlab : ∀ z ∈ t, K.cat.Source (lab z) (countSiteD K 𝔆.s z H) (countSiteE K 𝔆.s z H)) :
    (rho K.D (addFun H (-selBump K 𝔆.s (t.image fun z => (z, lab z))))).1 (K.x, K.y) +
      q9SiteA0 mc Hlo * ∑ z ∈ t, countUnit K 𝔆.s z H ≤ (rho K.D H).1 (K.x, K.y) := by
  have hs := hK.s_pos
  have hH0 := hG.base
  set T := t.image fun z => (z, lab z) with hTdef
  have hTsub : T ⊆ countUnivSites K 𝔆 := q9_image_lab_subset ht lab
  have hXT := hG.neg hTsub
  obtain ⟨h0, h1, hgeo⟩ := hH0.path
  set P := q9Path K.D K.x K.y H with hPdef
  have hP : ContinuousOn P (Icc 0 1) := hgeo.2.1
  -- exit intervals from the full inspections
  have hexit : ∀ z ∈ t, ∃ u w : ℝ, 0 ≤ u ∧ u ≤ w ∧ w ≤ 1 ∧ P u ∉ ball z (4 * 𝔆.s) ∧
      P w ∉ ball z (4 * 𝔆.s) ∧ (∀ τ ∈ Icc u w, P τ ∈ closedBall z (4 * 𝔆.s)) ∧
      ∃ t₀ ∈ Icc u w, P t₀ ∈ closedBall z (3 * 𝔆.s / 2) := by
    intro z hz
    obtain ⟨-, -, t₀, ht₀, hPt₀⟩ := helig z hz
    have hzZ := ht hz
    have hx := (hK.valid.2.2.2.1 z hzZ).2.1
    have hy := (hK.valid.2.2.2.1 z hzZ).2.2
    have hball : P t₀ ∈ ball z (4 * 𝔆.s) := by
      rw [mem_closedBall] at hPt₀
      rw [mem_ball]
      linarith
    have h0' : P 0 ∉ ball z (4 * 𝔆.s) := by
      rw [h0]
      exact fun h => hx (ball_subset_closedBall h)
    have h1' : P 1 ∉ ball z (4 * 𝔆.s) := by
      rw [h1]
      exact fun h => hy (ball_subset_closedBall h)
    obtain ⟨u, w, hu0, hut, htw, hw1, hPu, hPw, hin⟩ :=
      q9_exit_interval hP isOpen_ball h0' h1' ht₀ hball
    refine ⟨u, w, hu0, (hut.trans htw).le, hw1, hPu, hPw, ?_, t₀, ⟨hut.le, htw.le⟩, hPt₀⟩
    exact q9_exit_interval_closedBall (hut.trans htw) (hP.mono (Icc_subset_Icc hu0 hw1)) hin
  choose! u w hu0 huw hw1 hPu hPw hinB hcore using hexit
  set E := rho K.D (addFun H (-selBump K 𝔆.s T)) with hEdef
  set a₀ := q9SiteA0 mc Hlo
  -- per-site estimate
  have hspec' : ∀ z ∈ t, E.1 (P (u z), P (w z)) + a₀ * countUnit K 𝔆.s z H ≤
      (rho K.D H).1 (P (u z), P (w z)) := by
    intro z hz
    have hzT : (z, lab z) ∈ T := Finset.mem_image_of_mem _ hz
    have hsing : ({(z, lab z)} : Finset (Rd d × K.cat.Label)) ⊆ countUnivSites K 𝔆 :=
      Finset.singleton_subset_iff.2 (hTsub hzT)
    have hXz := hG.neg hsing
    rw [selBump_singleton] at hXz
    have hsave := q9_site_saving hK hH0 (hlab z hz) (q9_isGeodSeg_sub hgeo (hu0 z hz) (huw z hz) (hw1 z hz))
      (hPu z hz) (hPw z hz) (hcore z hz)
    have hcmp : E.1 (P (u z), P (w z)) ≤
        (rho K.D (addFun H (-q9Bump (K.cat.prof (lab z)) K.M z 𝔆.s))).1 (P (u z), P (w z)) := by
      refine q9_rho_le_of_discount hH0 hK.ξ_pos.le (fun x => ?_) hXT.1 hXz.1 _ _
      rw [selBump_erase_add hzT, ContinuousMap.add_apply]
      have := selBump_nonneg hK.M_pos.le hK.prof_nonneg 𝔆.s (T.erase (z, lab z)) x
      linarith
    linarith
  have hchain := q9_chain E P (fun a c => (rho K.D H).len P a c) 0 u w
    (fun z => ENNReal.ofReal ((rho K.D H).1 (P (u z), P (w z)) - a₀ * countUnit K 𝔆.s z H)) t 0 1
    zero_le_one (fun z hz => ⟨hu0 z hz, huw z hz, hw1 z hz⟩)
    (fun z hz z' hz' hzz' => q9_interval_disjoint (huw z hz) (huw z' hz')
      (hK.valid.2.2.2.2 z (ht hz) z' (ht hz') hzz') (hinB z hz) (hinB z' hz'))
    (fun a b c _ hab hbc _ => (rho K.D H).len_add P hab hbc)
    (fun z hz => ENNReal.ofReal_le_ofReal (by linarith [hspec' z hz]))
    (fun a c ha hac hc _ => by
      rw [add_zero]
      refine (E.ofReal_le_len P hac).trans ?_
      exact restore_discount_len_le (hH0.weylD _) hK.ξ_pos.le
        (selBump_nonneg hK.M_pos.le hK.prof_nonneg 𝔆.s T) (hP.mono (Icc_subset_Icc ha hc)))
  simp only [mul_zero, add_zero] at hchain
  have hlen : ∀ z ∈ t, (rho K.D H).len P (u z) (w z) =
      ENNReal.ofReal ((rho K.D H).1 (P (u z), P (w z))) := fun z hz =>
    q6_geod_subsegment hgeo (hu0 z hz) (huw z hz) (hw1 z hz)
  rw [Finset.sum_congr rfl hlen, hgeo.2.2, h0, h1] at hchain
  have hL0 : ∀ z ∈ t, 0 ≤ (rho K.D H).1 (P (u z), P (w z)) := fun z _ => (rho K.D H).nonneg _ _
  have hC0 : ∀ z ∈ t, 0 ≤ (rho K.D H).1 (P (u z), P (w z)) - a₀ * countUnit K 𝔆.s z H := by
    intro z hz
    have := hspec' z hz
    have := E.nonneg (P (u z)) (P (w z))
    linarith
  rw [← ENNReal.ofReal_sum_of_nonneg hL0, ← ENNReal.ofReal_sum_of_nonneg hC0,
    ← ENNReal.ofReal_add (E.nonneg _ _) (Finset.sum_nonneg hL0),
    ← ENNReal.ofReal_add ((rho K.D H).nonneg _ _) (Finset.sum_nonneg hC0),
    ENNReal.ofReal_le_ofReal_iff (add_nonneg ((rho K.D H).nonneg _ _) (Finset.sum_nonneg hC0))]
    at hchain
  rw [Finset.sum_sub_distrib, ← Finset.mul_sum] at hchain
  linarith

end Saving

/-- The selections with `m ≤ #Z ≤ k` (the index set of the count). -/
noncomputable def countSelIdx (K : CountData d) (𝔆 : Catalogue d) (m k : ℕ) :
    Finset (Finset (Rd d × K.cat.Label)) := by
  classical
  exact (countUnivSites K 𝔆).powerset.filter fun Z => IsSelection 𝔆 Z ∧ m ≤ Z.card ∧ Z.card ≤ k

theorem mem_countSelIdx {K : CountData d} {𝔆 : Catalogue d} {m k : ℕ} {Z : Finset (Rd d × K.cat.Label)} :
    Z ∈ countSelIdx K 𝔆 m k ↔ Z ⊆ countUnivSites K 𝔆 ∧ IsSelection 𝔆 Z ∧ m ≤ Z.card ∧ Z.card ≤ k := by
  classical
  simp only [countSelIdx, Finset.mem_filter, Finset.mem_powerset]

section Lower

variable {K : CountData d} {𝔆 : Catalogue d} {Hup sR Hlo b mc A0 d₀ Ap kp v θ ς δsep εnet εatt : ℝ}

open Classical in
/-- **Lower multiplicity (4.18)** (deterministic form, on the good event). -/
theorem lower_multiplicity_det (hK : CountHyp K 𝔆 Hup sR Hlo b mc A0 d₀ Ap kp v θ ς δsep εnet εatt)
    {H : DistRd d} (hG : CountGood K 𝔆 H) (hB : H ∈ countEventB K 𝔆) {k m : ℕ}
    (hm : m ≤ ⌈q9SiteA0 mc Hlo / (4 * A0) * k⌉₊)
    (hkN : k ≤ (𝔆.Z.filter fun z => IsEligible K 𝔆 z H).card) :
    (((𝔆.Z.filter fun z => IsEligible K 𝔆 z H).card : ℝ) / k) ^ m ≤
      (((countSelIdx K 𝔆 m k).filter fun Z => H ∈ countEventA K 𝔆 Z).card : ℝ) := by
  set elig := 𝔆.Z.filter fun z => IsEligible K 𝔆 z H with heligdef
  have heligZ : elig ⊆ 𝔆.Z := Finset.filter_subset _ _
  have hs := hK.s_pos
  have hH0 := hG.base
  set a₀ := q9SiteA0 mc Hlo
  have ha₀ := hK.a0_pos
  have hA₀ := hK.A0_pos
  -- `m ≤ k`
  have hκ1 : a₀ / (4 * A0) ≤ 1 := by
    rw [div_le_one (by positivity)]
    linarith [hK.a0_le_A0]
  have hmk : m ≤ k := by
    refine hm.trans (Nat.ceil_le.2 ?_)
    calc a₀ / (4 * A0) * (k : ℝ) ≤ 1 * k := by gcongr
      _ = k := one_mul _
  rcases Nat.eq_zero_or_pos k with hk0 | hkpos
  · -- `k = 0`: then `m = 0` and the left side is `1`; the empty selection is counted only if `H ∈ A_∅`
    subst hk0
    have hm0 : m = 0 := Nat.le_zero.1 hmk
    subst hm0
    simp only [pow_zero]
    have hmem : (∅ : Finset (Rd d × K.cat.Label)) ∈
        (countSelIdx K 𝔆 0 0).filter fun Z => H ∈ countEventA K 𝔆 Z := by
      refine Finset.mem_filter.2 ⟨mem_countSelIdx.2 ⟨Finset.empty_subset _, ⟨by simp, by simp⟩, le_rfl,
        by simp⟩, hB, by simp⟩
    exact_mod_cast Finset.card_pos.2 ⟨_, hmem⟩
  -- a label for every eligible site
  have hne : elig.Nonempty := Finset.card_pos.1 (lt_of_lt_of_le hkpos hkN)
  obtain ⟨z₀, hz₀⟩ := hne
  obtain ⟨ℓ₀, -⟩ := (Finset.mem_filter.1 hz₀).2.1
  let lab : Rd d → K.cat.Label := fun z =>
    if h : ∃ ℓ, K.cat.Source ℓ (countSiteD K 𝔆.s z H) (countSiteE K 𝔆.s z H) then h.choose else ℓ₀
  have hlab : ∀ z ∈ elig, K.cat.Source (lab z) (countSiteD K 𝔆.s z H) (countSiteE K 𝔆.s z H) := by
    intro z hz
    have h := (Finset.mem_filter.1 hz).2.1
    simp only [lab, dite_eq_left h]
    exact h.choose_spec
  let lsel : Finset (Rd d) → Finset (Rd d × K.cat.Label) := fun t => t.image fun z => (z, lab z)
  let good : Finset (Rd d) → Rd d → Prop := fun t z =>
    PassesTrigger (countSiteD K 𝔆.s z H)
      (q9SitePath (q9Path K.D K.x K.y (addFun H (-selBump K 𝔆.s (lsel t)))) z 𝔆.s) 0 1 K.btrig
  let Δf : Finset (Rd d) → ℝ := fun t =>
    (rho K.D H).1 (K.x, K.y) - (rho K.D (addFun H (-selBump K 𝔆.s (lsel t)))).1 (K.x, K.y)
  have hF2 := q9_siteF2 hK.mc_pos hK.Hlo_ge
  -- the pruning output of every `k`-set of eligible sites
  have hprune : ∀ t ∈ elig.powersetCard k, ∃ o ⊆ t, (∀ i ∈ o, good o i) ∧
      a₀ / (4 * A0) * t.card ≤ o.card := by
    intro t htk
    have htelig : t ⊆ elig := (Finset.mem_powersetCard.1 htk).1
    have htZ : t ⊆ 𝔆.Z := htelig.trans heligZ
    have hunit : ∀ i ∈ t, 𝔆.Q * 1 ≤ countUnit K 𝔆.s i H ∧ countUnit K 𝔆.s i H ≤ 2 * (𝔆.Q * 1) := by
      intro i hi
      have h := (Finset.mem_filter.1 (htelig hi)).2.2.1
      rw [mul_one]
      exact ⟨h.1, h.2⟩
    refine pruning t (fun i => countUnit K 𝔆.s i H) (q := 𝔆.Q) (S := 1)
      (by rw [mul_one]; exact hK.valid.2.2.1) hunit ha₀ hK.btrig_pos.le
      (by rw [hK.btrig_eq]; exact hF2.2.2.2.2.2.1) hA₀ Δf good ?_ ?_ ?_
    · -- (h1)
      have h := q9_saving hK hG htZ lab (fun z hz => (Finset.mem_filter.1 (htelig hz)).2)
        (fun z hz => hlab z (htelig hz))
      simp only [Δf, lsel]
      linarith
    · -- (h2)
      intro o hot i hio hbad
      have hoZ : o ⊆ 𝔆.Z := (hot.trans htelig).trans heligZ
      have hpi : (i, lab i) ∈ lsel o := Finset.mem_image_of_mem _ hio
      have herase : lsel (o.erase i) = (lsel o).erase (i, lab i) := by
        simp only [lsel]
        rw [Finset.image_erase (fun z₁ z₂ h => (Prod.mk.inj h).1)]
      have hrem := q9_trigger_removal hK hH0 (q9_isSelection_image_lab hoZ lab) hpi
        (by rw [← herase]; exact hG.neg (q9_image_lab_subset (Finset.erase_subset _ _ |>.trans hoZ) lab))
        (hG.neg (q9_image_lab_subset hoZ lab)) hbad
      simp only [Δf]
      rw [herase]
      linarith
    · -- (h3)
      intro o hot
      have hoZ : o ⊆ 𝔆.Z := (hot.trans htelig).trans heligZ
      have hres := q9_restoration hK hH0 (Z := lsel o) (hG.neg (q9_image_lab_subset hoZ lab))
        (by
          intro p hp
          obtain ⟨z, hz, rfl⟩ := Finset.mem_image.1 hp
          exact hlab z (hot.trans htelig hz))
      have hsum : ∑ p ∈ lsel o, countUnit K 𝔆.s p.1 H = ∑ z ∈ o, countUnit K 𝔆.s z H :=
        Finset.sum_image (fun z₁ _ z₂ _ h => (Prod.mk.inj h).1)
      rw [hsum] at hres
      simp only [Δf]
      linarith
  choose! out hout_sub hout_good hout_card using hprune
  have hout : ∀ t ∈ elig.powersetCard k, out t ⊆ t ∧ m ≤ (out t).card := by
    intro t ht
    refine ⟨hout_sub t ht, hm.trans (Nat.ceil_le.2 ?_)⟩
    have h := hout_card t ht
    rwa [(Finset.mem_powersetCard.1 ht).2] at h
  have hcount := card_image_out_ge elig hmk hkN out hout
  refine hcount.trans ?_
  have hinj : Function.Injective lsel := q9_image_lab_injective lab
  rw [← Finset.card_image_of_injective _ hinj, Finset.image_image]
  refine Nat.cast_le.2 (Finset.card_le_card fun Z hZ => ?_)
  obtain ⟨t, ht, rfl⟩ := Finset.mem_image.1 hZ
  have htelig : t ⊆ elig := (Finset.mem_powersetCard.1 ht).1
  have hoelig : out t ⊆ elig := (hout_sub t ht).trans htelig
  have hoZ : out t ⊆ 𝔆.Z := hoelig.trans heligZ
  have hcard : (lsel (out t)).card = (out t).card :=
    Finset.card_image_of_injective _ (fun z₁ z₂ h => (Prod.mk.inj h).1)
  refine Finset.mem_filter.2 ⟨mem_countSelIdx.2 ⟨q9_image_lab_subset hoZ lab,
    q9_isSelection_image_lab hoZ lab, by rw [Function.comp_apply, hcard]; exact (hout t ht).2, ?_⟩, hB, ?_⟩
  · rw [Function.comp_apply, hcard]
    exact (Finset.card_le_card (hout_sub t ht)).trans (Finset.mem_powersetCard.1 ht).2.le
  · intro p hp
    obtain ⟨z, hz, rfl⟩ := Finset.mem_image.1 hp
    exact ⟨hlab z (hoelig hz), (Finset.mem_filter.1 (hoelig hz)).2.2.1, hout_good t ht z hz⟩

end Lower

end HigherDimLQGContinuity
