import HigherDimLQGContinuity.Core.Interfaces
import HigherDimLQGMetric.Metric.WeylMetric
import HigherDimLQGMetric.Sec8b.CollectorWindow

/-!
# Deterministic path length comparisons for restoration

These helpers pass from bounds on internal distances to bounds on lengths of
continuous curves. They are used by the one-site surgery and finite restoration.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Metric Topology
open scoped ENNReal

namespace HigherDimLQGContinuity

open HigherDimLFPP (Rd)
open HigherDimLQGMetric (ContMetric)
open LQGMetric.MetricGeometry

variable {d : ℕ}

/-- Pointwise comparison of internal distances on a set compares lengths of curves in the set. -/
private theorem restore_len_le_of_internal_le {D E : ContMetric d} {U : Set (Rd d)}
    (hDE : ∀ x ∈ U, ∀ y ∈ U, E.internal U x y ≤ D.internal U x y)
    {P : ℝ → Rd d} {s t : ℝ} (hc : ContinuousOn P (Icc s t))
    (hPU : ∀ τ ∈ Icc s t, P τ ∈ U) : E.len P s t ≤ D.len P s t := by
  have hcD : ContinuousOn (D.pt ∘ P) (Icc s t) := D.continuousOn_pt_comp_iff.2 hc
  change curveLength (E.pt ∘ P) s t ≤ curveLength (D.pt ∘ P) s t
  refine iSup_le fun p => ?_
  obtain ⟨n, u, hu, hus⟩ := p
  calc
    ∑ i ∈ Finset.range n, edist (E.pt (P (u (i + 1)))) (E.pt (P (u i)))
        ≤ ∑ i ∈ Finset.range n, D.internal U (P (u i)) (P (u (i + 1))) := by
          apply Finset.sum_le_sum
          intro i _
          rw [edist_comm, E.edist_pt]
          exact (E.ofReal_le_internal U _ _).trans
            (hDE _ (hPU _ (hus i)) _ (hPU _ (hus (i + 1))))
    _ ≤ ∑ i ∈ Finset.range n, curveLength (D.pt ∘ P) (u i) (u (i + 1)) := by
          apply Finset.sum_le_sum
          intro i _
          have hi : u i ≤ u (i + 1) := hu (Nat.le_succ i)
          have hsub : Icc (u i) (u (i + 1)) ⊆ Icc s t :=
            Icc_subset_Icc (hus i).1 (hus (i + 1)).2
          obtain ⟨γ, hγ, hrange⟩ := exists_path_of_curve hi (hcD.mono hsub)
          refine (internalEDist_le_pathLength γ fun τ => ?_).trans hγ.le
          obtain ⟨r, hr, hrτ⟩ := hrange (mem_range_self τ)
          exact ⟨P r, hPU r (hsub hr), hrτ⟩
    _ = curveLength (D.pt ∘ P) (u 0) (u n) := sum_curveLength_eq _ hu n
    _ ≤ curveLength (D.pt ∘ P) s t := curveLength_mono _ (hus 0).1 (hus n).2

/-- A nonnegative Weyl discount cannot increase the length of a curve. -/
theorem restore_discount_len_le {D D' : ContMetric d} {f : C(Rd d, ℝ)} {ξ : ℝ}
    (hD' : IsWeylInternal ξ (-f) D D') (hξ : 0 ≤ ξ) (hf0 : ∀ x, 0 ≤ f x)
    {P : ℝ → Rd d} {s t : ℝ} (hc : ContinuousOn P (Icc s t)) :
    D'.len P s t ≤ D.len P s t := by
  apply restore_len_le_of_internal_le (U := univ) (fun x _ y _ => ?_) hc
    (fun _ _ => mem_univ _)
  rw [hD' univ isOpen_univ]
  have hweight : ∀ z ∈ (univ : Set (Rd d)), ξ * (-f) z ≤ 0 := by
    intro z _
    simp only [ContinuousMap.neg_apply]
    nlinarith [mul_nonneg hξ (hf0 z)]
  simpa only [Real.exp_zero, ENNReal.ofReal_one, one_mul] using
    (HigherDimLQGMetric.weylScaleOn_le_of_le (ξ := ξ) (f := -f) (D := D)
      (U := univ) (z := x) (w := y) hweight)

/-- On a continuous curve, deleting both endpoint times does not change variation. -/
private theorem restore_eVariationOn_Ioo_eq_len (E : ContMetric d)
    {P : ℝ → Rd d} {s t : ℝ} (hst : s ≤ t) (hP : ContinuousOn P (Icc s t)) :
    eVariationOn (E.pt ∘ P) (Ioo s t) = E.len P s t := by
  rcases hst.eq_or_lt with heq | hlt
  · subst t
    simpa only [Ioo_self, E.len_def, curveLength_self] using
      (eVariationOn.subsingleton (E.pt ∘ P) Set.subsingleton_empty)
  let Q : ℝ → Rd d := fun r => P ((projIcc s t hst r : ℝ))
  have hQ : Continuous Q :=
    hP.comp_continuous (continuous_subtype_val.comp continuous_projIcc)
      (fun r => (projIcc s t hst r).property)
  have hQP : EqOn Q P (Icc s t) := by
    intro r hr
    simp only [Q]
    rw [projIcc_of_mem _ hr]
  have hQcont : Continuous (E.pt ∘ Q) := E.continuous_pt.comp hQ
  have hne : (𝓝[Iio t ∩ Ioi s] s).NeBot := by
    rw [nhdsWithin_inter_of_mem
      (mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds hlt))]
    exact nhdsGT_neBot_of_exists_gt ⟨t, hlt⟩
  have hleft : eVariationOn (E.pt ∘ Q) (Ioo s t) =
      eVariationOn (E.pt ∘ Q) (Ico s t) := by
    simpa only [Iio_inter_Ioi, Iio_inter_Ici] using
      (eVariationOn.eVariationOn_inter_Ioi_eq_inter_Ici_of_continuousWithinAt
        (s := Iio t) (a := s) hne hQcont.continuousAt.continuousWithinAt)
  have hright : eVariationOn (E.pt ∘ Q) (Ico s t) =
      eVariationOn (E.pt ∘ Q) (Icc s t) :=
    eVariationOn.eVariationOn_Ico_eq_Icc_of_continuousWithinAt
      hQcont.continuousAt.continuousWithinAt
  have hopen : EqOn (E.pt ∘ Q) (E.pt ∘ P) (Ioo s t) := by
    intro r hr
    exact congrArg E.pt (hQP (Ioo_subset_Icc_self hr))
  have hclosed : EqOn (E.pt ∘ Q) (E.pt ∘ P) (Icc s t) := by
    intro r hr
    exact congrArg E.pt (hQP hr)
  calc
    eVariationOn (E.pt ∘ P) (Ioo s t) =
        eVariationOn (E.pt ∘ Q) (Ioo s t) :=
          (eVariationOn.eq_of_eqOn hopen).symm
    _ = eVariationOn (E.pt ∘ Q) (Icc s t) := hleft.trans hright
    _ = E.len P s t := by
      rw [E.len_def]
      exact eVariationOn.eq_of_eqOn hclosed

/-- Length comparison when all interior points avoid a finite collector family. -/
private theorem restore_len_le_of_agree_Ioo {D D' : ContMetric d} {ι : Type*}
    (Z : Finset ι) (C : ι → Set (Rd d))
    (hagree : ∀ (P : ℝ → Rd d) (s t : ℝ), s ≤ t → ContinuousOn P (Icc s t) →
      (∀ τ ∈ Icc s t, ∀ i ∈ Z, P τ ∉ C i) → D.len P s t = D'.len P s t)
    (P : ℝ → Rd d) {s t : ℝ} (hst : s ≤ t) (hP : ContinuousOn P (Icc s t))
    (havoid : ∀ τ ∈ Ioo s t, ∀ i ∈ Z, P τ ∉ C i) :
    D.len P s t ≤ D'.len P s t := by
  rw [← restore_eVariationOn_Ioo_eq_len D hst hP]
  refine iSup_le fun p => ?_
  obtain ⟨n, u, hu, hus⟩ := p
  have hmid : D.len P (u 0) (u n) = D'.len P (u 0) (u n) := by
    apply hagree P (u 0) (u n) (hu (Nat.zero_le n))
    · exact hP.mono (Icc_subset_Icc (le_of_lt (hus 0).1) (le_of_lt (hus n).2))
    · intro τ hτ i hi
      exact havoid τ ⟨lt_of_lt_of_le (hus 0).1 hτ.1,
        lt_of_le_of_lt hτ.2 (hus n).2⟩ i hi
  calc
    ∑ i ∈ Finset.range n, edist (D.pt (P (u (i + 1)))) (D.pt (P (u i)))
        ≤ ∑ i ∈ Finset.range n, D.len P (u i) (u (i + 1)) := by
          apply Finset.sum_le_sum
          intro i _
          rw [edist_comm, D.edist_pt]
          exact D.ofReal_le_len P (hu (Nat.le_succ i))
    _ = D.len P (u 0) (u n) := sum_curveLength_eq _ hu n
    _ = D'.len P (u 0) (u n) := hmid
    _ ≤ D'.len P s t := D'.len_mono P (le_of_lt (hus 0).1) (le_of_lt (hus n).2)

/-- Chronological restoration with the nonnegative costs required in blueprint `b:lem-restore`. -/
theorem chronological_restoration {D D' : ContMetric d} {ι : Type*} (Z : Finset ι)
    (C W : ι → Set (Rd d)) (hC : ∀ i, IsClosed (C i)) (cost : ι → ℝ)
    (hcost : ∀ i ∈ Z, 0 ≤ cost i)
    (hrepl : ∀ i ∈ Z, ∀ u ∈ C i, ∀ v ∈ C i, D.internal (W i) u v ≤ ENNReal.ofReal (cost i))
    (hagree : ∀ (P : ℝ → Rd d) (s t : ℝ), s ≤ t → ContinuousOn P (Icc s t) →
      (∀ τ ∈ Icc s t, ∀ i ∈ Z, P τ ∉ C i) → D.len P s t = D'.len P s t)
    (P : ℝ → Rd d) (a c : ℝ) (hac : a ≤ c) (hP : ContinuousOn P (Icc a c)) :
    ENNReal.ofReal (D.1 (P a, P c)) ≤ D'.len P a c + ENNReal.ofReal (∑ i ∈ Z, cost i) := by
  classical
  let Bound (T : Finset ι) : Prop :=
    ∀ (s : ℝ), a ≤ s → s ≤ c → T ⊆ Z →
      (∀ τ ∈ Ioc s c, ∀ i ∈ Z, i ∉ T → P τ ∉ C i) →
      ENNReal.ofReal (D.1 (P s, P c)) ≤
        D'.len P s c + ENNReal.ofReal (∑ i ∈ T, cost i)
  have hbound : ∀ T : Finset ι, Bound T :=
    Finset.strongInduction (p := Bound) (fun T ih => by
      intro s has hsc hTZ hout
      have hPs : ContinuousOn P (Icc s c) :=
        hP.mono (Icc_subset_Icc has le_rfl)
      by_cases hhit : ∃ τ ∈ Icc s c, ∃ i ∈ T, P τ ∈ C i
      · let K : Set (Rd d) := ⋃ i ∈ T, C i
        have hK : IsClosed K := isClosed_biUnion_finset (fun i _ => hC i)
        have hKhit : ∃ τ ∈ Icc s c, P τ ∈ K := by
          obtain ⟨τ, hτ, i, hi, hPi⟩ := hhit
          exact ⟨τ, hτ, by simp only [K, mem_iUnion]; exact ⟨i, hi, hPi⟩⟩
        obtain ⟨σ, hσ, hPσ, hbefore⟩ := exists_first_hit hPs hK hKhit
        simp only [K, mem_iUnion] at hPσ
        obtain ⟨i, hiT, hPσi⟩ := hPσ
        obtain ⟨σ₀, u, hσσ₀, hσ₀u, huc, hPσ₀, hPu, hlast⟩ :=
          HigherDimLQGMetric.s7b_first_last_hit
            (hPs.mono (Icc_subset_Icc hσ.1 le_rfl)) (hC i)
            (t₀ := σ) ⟨le_rfl, hσ.2⟩ hPσi
        have hσu : σ ≤ u := hσσ₀.trans hσ₀u
        have hsu : s ≤ u := hσ.1.trans hσu
        have hpref : D.len P s σ ≤ D'.len P s σ := by
          apply restore_len_le_of_agree_Ioo Z C hagree P hσ.1
            (hPs.mono (Icc_subset_Icc le_rfl hσ.2))
          intro τ hτ j hj
          by_cases hjT : j ∈ T
          · exact fun hτj => hbefore τ ⟨hτ.1.le, hτ.2⟩
              (by simp only [K, mem_iUnion]; exact ⟨j, hjT, hτj⟩)
          · exact hout τ ⟨hτ.1, hτ.2.le.trans hσ.2⟩ j hj hjT
        have htailOut : ∀ τ ∈ Ioc u c, ∀ j ∈ Z, j ∉ T.erase i → P τ ∉ C j := by
          intro τ hτ j hj hjout
          by_cases hjT : j ∈ T
          · have hji : j = i := by
              by_contra hne
              exact hjout (Finset.mem_erase.mpr ⟨hne, hjT⟩)
            subst j
            intro hτi
            have hτbound : τ ∈ Icc σ c := ⟨hσu.trans hτ.1.le, hτ.2⟩
            exact (not_le_of_gt hτ.1) (hlast τ hτbound hτi).2
          · exact hout τ ⟨hsu.trans_lt hτ.1, hτ.2⟩ j hj hjT
        have htail := ih (T.erase i) (Finset.erase_ssubset hiT)
          u (has.trans hsu) huc (Finset.Subset.trans (Finset.erase_subset _ _) hTZ) htailOut
        have hmiddle : ENNReal.ofReal (D.1 (P σ, P u)) ≤ ENNReal.ofReal (cost i) :=
          (D.ofReal_le_internal (W i) _ _).trans (hrepl i (hTZ hiT) _ hPσi _ hPu)
        have htri : ENNReal.ofReal (D.1 (P s, P c)) ≤
            ENNReal.ofReal (D.1 (P s, P σ)) +
              ENNReal.ofReal (D.1 (P σ, P u)) +
                ENNReal.ofReal (D.1 (P u, P c)) := by
          have h₁ := D.apply_triangle (P s) (P σ) (P u)
          have h₂ := D.apply_triangle (P s) (P u) (P c)
          have hh : D.1 (P s, P c) ≤
              D.1 (P s, P σ) + D.1 (P σ, P u) + D.1 (P u, P c) := by
            linarith only [h₁, h₂]
          simpa only [ENNReal.ofReal_add (add_nonneg (D.nonneg _ _) (D.nonneg _ _))
            (D.nonneg _ _), ENNReal.ofReal_add (D.nonneg _ _) (D.nonneg _ _)] using
            ENNReal.ofReal_le_ofReal hh
        have hsum : ENNReal.ofReal (∑ j ∈ T, cost j) =
            ENNReal.ofReal (cost i) + ENNReal.ofReal (∑ j ∈ T.erase i, cost j) := by
          have hnon : 0 ≤ ∑ j ∈ T.erase i, cost j :=
            Finset.sum_nonneg (fun j hj => hcost j (hTZ (Finset.mem_of_mem_erase hj)))
          rw [← Finset.sum_erase_add T cost hiT, ENNReal.ofReal_add hnon (hcost i (hTZ hiT))]
          ac_rfl
        calc
          ENNReal.ofReal (D.1 (P s, P c)) ≤
              ENNReal.ofReal (D.1 (P s, P σ)) +
                ENNReal.ofReal (D.1 (P σ, P u)) +
                  ENNReal.ofReal (D.1 (P u, P c)) := htri
          _ ≤ D.len P s σ + ENNReal.ofReal (cost i) +
                (D'.len P u c + ENNReal.ofReal (∑ j ∈ T.erase i, cost j)) := by
              exact add_le_add (add_le_add (D.ofReal_le_len P hσ.1) hmiddle) htail
          _ ≤ D'.len P s σ + D'.len P σ u + D'.len P u c +
                ENNReal.ofReal (∑ j ∈ T, cost j) := by
              rw [hsum]
              calc
                D.len P s σ + ENNReal.ofReal (cost i) +
                    (D'.len P u c + ENNReal.ofReal (∑ j ∈ T.erase i, cost j)) ≤
                    D'.len P s σ + ENNReal.ofReal (cost i) +
                      (D'.len P u c + ENNReal.ofReal (∑ j ∈ T.erase i, cost j)) := by
                        gcongr
                _ = D'.len P s σ + D'.len P u c +
                      (ENNReal.ofReal (cost i) +
                        ENNReal.ofReal (∑ j ∈ T.erase i, cost j)) := by ac_rfl
                _ ≤ D'.len P s σ + D'.len P σ u + D'.len P u c +
                      (ENNReal.ofReal (cost i) +
                        ENNReal.ofReal (∑ j ∈ T.erase i, cost j)) := by
                        gcongr
                        exact le_add_of_nonneg_right bot_le
          _ = D'.len P s c + ENNReal.ofReal (∑ j ∈ T, cost j) := by
              rw [D'.len_add P hσ.1 hσu, D'.len_add P hsu huc]
      · have havoid : ∀ τ ∈ Ioo s c, ∀ i ∈ Z, P τ ∉ C i := by
          intro τ hτ i hi
          by_cases hiT : i ∈ T
          · intro hτi
            exact hhit ⟨τ, ⟨hτ.1.le, hτ.2.le⟩, i, hiT, hτi⟩
          · exact hout τ ⟨hτ.1, hτ.2.le⟩ i hi hiT
        have hlen := restore_len_le_of_agree_Ioo Z C hagree P hsc hPs havoid
        calc
          ENNReal.ofReal (D.1 (P s, P c)) ≤ D.len P s c := D.ofReal_le_len P hsc
          _ ≤ D'.len P s c := hlen
          _ ≤ D'.len P s c + ENNReal.ofReal (∑ i ∈ T, cost i) := le_add_of_nonneg_right bot_le)
  exact hbound Z a le_rfl hac subset_rfl (by
    intro τ hτ i hi hnot
    exact False.elim (hnot hi))

/-- A Weyl change supported in the closed collector leaves the length of a path
unchanged when its open time interval avoids that collector. -/
theorem restore_len_eq_of_avoids_collector {D D' : ContMetric d}
    {f : C(Rd d, ℝ)} {ξ : ℝ} (hD' : IsWeylInternal ξ (-f) D D')
    (hfC : tsupport f ⊆ siteC d) {P : ℝ → Rd d} {s t : ℝ}
    (hst : s ≤ t) (hP : ContinuousOn P (Icc s t))
    (havoid : ∀ τ ∈ Ioo s t, P τ ∉ siteC d) : D.len P s t = D'.len P s t := by
  let U : Set (Rd d) := (siteC d)ᶜ
  have hU : IsOpen U := (HigherDimLQGMetric.isClosed_annCl (0 : Rd d) (3 / 2) (5 / 2)).isOpen_compl
  have hfzero : ∀ x ∈ U, f x = 0 := by
    intro x hx
    exact image_eq_zero_of_notMem_tsupport (fun hxs => hx (hfC hxs))
  have hint : ∀ x ∈ U, ∀ y ∈ U, D'.internal U x y = D.internal U x y := by
    intro x _ y _
    rw [hD' U hU x y]
    simpa only [Real.exp_zero, ENNReal.ofReal_one, one_mul] using
      (HigherDimLQGMetric.weylScaleOn_of_eq_const (ξ := ξ) (f := -f) (D := D)
        (U := U) (z := x) (w := y) (a := 0) (by
          intro z hz
          simp only [ContinuousMap.neg_apply, hfzero z hz, neg_zero, mul_zero]))
  have hmatch : ∀ (Q : ℝ → Rd d) (u v : ℝ), u ≤ v → ContinuousOn Q (Icc u v) →
      (∀ τ ∈ Icc u v, ∀ _i ∈ ({()} : Finset Unit), Q τ ∉ siteC d) →
      D.len Q u v = D'.len Q u v := by
    intro Q u v _ hQ hQavoid
    exact (HigherDimLQGMetric.curveLength_eq_of_internal_eq
      (D₁ := D) (D₂ := D') (U := U)
      (fun x hx y hy => (hint x hx y hy).symm) hQ
      (fun τ hτ => hQavoid τ hτ () (by simp)))
  have hle := restore_len_le_of_agree_Ioo ({()} : Finset Unit)
    (fun _ => siteC d) hmatch P hst hP (by
      intro τ hτ i hi
      exact havoid τ hτ)
  have hmatch' : ∀ (Q : ℝ → Rd d) (u v : ℝ), u ≤ v → ContinuousOn Q (Icc u v) →
      (∀ τ ∈ Icc u v, ∀ _i ∈ ({()} : Finset Unit), Q τ ∉ siteC d) →
      D'.len Q u v = D.len Q u v := by
    intro Q u v hu hQ hQavoid
    exact (hmatch Q u v hu hQ hQavoid).symm
  have hge := restore_len_le_of_agree_Ioo ({()} : Finset Unit)
    (fun _ => siteC d) hmatch' P hst hP (by
      intro τ hτ i hi
      exact havoid τ hτ)
  exact le_antisymm hle hge

/-- First and last visits to a closed collector agree with the interface's
`sInf` and `sSup` definitions. -/
private theorem restore_first_last {P : ℝ → Rd d} {a c : ℝ} {K : Set (Rd d)}
    (hP : ContinuousOn P (Icc a c)) (hK : IsClosed K)
    (hvisit : ∃ t ∈ Icc a c, P t ∈ K) :
    ∃ s u : ℝ, a ≤ s ∧ s ≤ u ∧ u ≤ c ∧ P s ∈ K ∧ P u ∈ K ∧
      s = firstVisit P a c K ∧ u = lastVisit P a c K ∧
      ∀ t ∈ Icc a c, P t ∈ K → s ≤ t ∧ t ≤ u := by
  obtain ⟨t₀, ht₀, hPt₀⟩ := hvisit
  obtain ⟨s, u, has, hsu, huc, hPs, hPu, hbound⟩ :=
    HigherDimLQGMetric.s7b_first_last_hit hP hK ht₀ hPt₀
  let T : Set ℝ := {t | t ∈ Icc a c ∧ P t ∈ K}
  have hTne : T.Nonempty := ⟨t₀, ht₀, hPt₀⟩
  have hTbelow : BddBelow T := ⟨a, fun t ht => ht.1.1⟩
  have hTabove : BddAbove T := ⟨c, fun t ht => ht.1.2⟩
  have hsT : s ∈ T := ⟨⟨has, hsu.trans huc⟩, hPs⟩
  have huT : u ∈ T := ⟨⟨has.trans hsu, huc⟩, hPu⟩
  have hfirst : s = firstVisit P a c K := by
    change s = sInf T
    exact le_antisymm
      (le_csInf hTne (fun t ht => (hbound t ht.1 ht.2).1))
      (csInf_le hTbelow hsT)
  have hlast : u = lastVisit P a c K := by
    change u = sSup T
    exact le_antisymm (le_csSup hTabove huT)
      (csSup_le hTne (fun t ht => (hbound t ht.1 ht.2).2))
  exact ⟨s, u, has, hsu, huc, hPs, hPu, hfirst, hlast, hbound⟩

/-- Removing a bump when its collector trigger fails costs at most `btrig`.
An unvisited collector costs zero. -/
theorem trigger_removal {D D' : ContMetric d} {f : C(Rd d, ℝ)} {ξ btrig : ℝ}
    (hD' : IsWeylInternal ξ (-f) D D') (_hξ : 0 ≤ ξ) (_hf0 : ∀ x, 0 ≤ f x)
    (hfC : tsupport f ⊆ siteC d) (P : ℝ → Rd d) (a c : ℝ)
    (hP : IsGeodSeg D' P a c) (_hbt : 0 ≤ btrig)
    (htrig : ¬ PassesTrigger D P a c btrig) :
    ENNReal.ofReal (D.1 (P a, P c)) ≤
      ENNReal.ofReal (D'.1 (P a, P c)) + ENNReal.ofReal btrig := by
  have hac : a ≤ c := hP.1
  have hcont : ContinuousOn P (Icc a c) := hP.2.1
  by_cases hvisit : ∃ t ∈ Icc a c, P t ∈ siteC d
  · have hC : IsClosed (siteC d) :=
      HigherDimLQGMetric.isClosed_annCl (0 : Rd d) (3 / 2) (5 / 2)
    obtain ⟨s, u, has, hsu, huc, hPs, hPu, hfirst, hlast, hbound⟩ :=
      restore_first_last hcont hC hvisit
    have hshort : D.internal (siteB d) (P s) (P u) ≤ ENNReal.ofReal btrig := by
      have hn : ¬ ENNReal.ofReal btrig ≤
          D.internal (siteB d) (P (firstVisit P a c (siteC d)))
            (P (lastVisit P a c (siteC d))) := by
        intro hp
        exact htrig ⟨hvisit, hp⟩
      rw [← hfirst, ← hlast] at hn
      exact le_of_lt (lt_of_not_ge hn)
    have hleftAvoid : ∀ τ ∈ Ioo a s, P τ ∉ siteC d := by
      intro τ hτ hτC
      have hτb := (hbound τ ⟨hτ.1.le, hτ.2.le.trans (hsu.trans huc)⟩ hτC).1
      exact (not_le_of_gt hτ.2) hτb
    have hrightAvoid : ∀ τ ∈ Ioo u c, P τ ∉ siteC d := by
      intro τ hτ hτC
      have hτb := (hbound τ ⟨(has.trans hsu).trans hτ.1.le, hτ.2.le⟩ hτC).2
      exact (not_le_of_gt hτ.1) hτb
    have hleft := restore_len_eq_of_avoids_collector hD' hfC has
      (hcont.mono (Icc_subset_Icc le_rfl (hsu.trans huc))) hleftAvoid
    have hright := restore_len_eq_of_avoids_collector hD' hfC huc
      (hcont.mono (Icc_subset_Icc (has.trans hsu) le_rfl)) hrightAvoid
    have htri : ENNReal.ofReal (D.1 (P a, P c)) ≤
        ENNReal.ofReal (D.1 (P a, P s)) +
          ENNReal.ofReal (D.1 (P s, P u)) +
            ENNReal.ofReal (D.1 (P u, P c)) := by
      have h₁ := D.apply_triangle (P a) (P s) (P u)
      have h₂ := D.apply_triangle (P a) (P u) (P c)
      have hh : D.1 (P a, P c) ≤
          D.1 (P a, P s) + D.1 (P s, P u) + D.1 (P u, P c) := by
        linarith only [h₁, h₂]
      simpa only [ENNReal.ofReal_add (add_nonneg (D.nonneg _ _) (D.nonneg _ _))
        (D.nonneg _ _), ENNReal.ofReal_add (D.nonneg _ _) (D.nonneg _ _)] using
        ENNReal.ofReal_le_ofReal hh
    calc
      ENNReal.ofReal (D.1 (P a, P c)) ≤
          ENNReal.ofReal (D.1 (P a, P s)) +
            ENNReal.ofReal (D.1 (P s, P u)) +
              ENNReal.ofReal (D.1 (P u, P c)) := htri
      _ ≤ D.len P a s + ENNReal.ofReal btrig + D.len P u c := by
          exact add_le_add (add_le_add (D.ofReal_le_len P has)
            ((D.ofReal_le_internal (siteB d) _ _).trans hshort))
            (D.ofReal_le_len P huc)
      _ = D'.len P a s + ENNReal.ofReal btrig + D'.len P u c := by rw [hleft, hright]
      _ ≤ D'.len P a c + ENNReal.ofReal btrig := by
          have hsplit : D'.len P a c =
              D'.len P a s + D'.len P s u + D'.len P u c := by
            calc
              D'.len P a c = D'.len P a u + D'.len P u c :=
                (D'.len_add P (has.trans hsu) huc).symm
              _ = D'.len P a s + D'.len P s u + D'.len P u c := by
                rw [D'.len_add P has hsu]
          rw [hsplit]
          calc
            D'.len P a s + ENNReal.ofReal btrig + D'.len P u c =
                (D'.len P a s + D'.len P u c) + ENNReal.ofReal btrig := by ac_rfl
            _ ≤ (D'.len P a s + D'.len P s u + D'.len P u c) +
                  ENNReal.ofReal btrig := by
                    exact add_le_add
                      (add_le_add (le_add_of_nonneg_right bot_le) le_rfl) le_rfl
      _ = ENNReal.ofReal (D'.1 (P a, P c)) + ENNReal.ofReal btrig := by rw [hP.2.2]
  · have havoid : ∀ τ ∈ Ioo a c, P τ ∉ siteC d := by
      intro τ hτ hτC
      exact hvisit ⟨τ, ⟨hτ.1.le, hτ.2.le⟩, hτC⟩
    have hlen := restore_len_eq_of_avoids_collector hD' hfC hac hcont havoid
    calc
      ENNReal.ofReal (D.1 (P a, P c)) ≤ D.len P a c := D.ofReal_le_len P hac
      _ = D'.len P a c := hlen
      _ = ENNReal.ofReal (D'.1 (P a, P c)) := hP.2.2
      _ ≤ ENNReal.ofReal (D'.1 (P a, P c)) + ENNReal.ofReal btrig :=
        le_add_of_nonneg_right bot_le

/-- The forcing certificate gives a three-piece shortcut between any two collector points. -/
private theorem restore_certificate_shortcut {D E D' : ContMetric d} {f : C(Rd d, ℝ)}
    {ξ M θ h δsep ε₀ εnet εatt aout H b v d₀ : ℝ}
    (cert : ForcingCert D E f ξ M θ h δsep ε₀ εnet εatt aout H b v d₀)
    (hD' : IsWeylInternal ξ (-f) D D') (hξ : 0 ≤ ξ)
    {x y : Rd d} (hx : x ∈ siteC d) (hy : y ∈ siteC d) :
    ENNReal.ofReal (D'.1 (x, y)) ≤
      ENNReal.ofReal ε₀ + ENNReal.ofReal εnet + ENNReal.ofReal ε₀ := by
  obtain ⟨p, hp, hxp⟩ := cert.access x hx
  obtain ⟨q, hq, hyq⟩ := cert.access y hy
  have hA : IsOpen (siteA d) := HigherDimLQGMetric.isOpen_ann _ _ _
  have hweight : ∀ z ∈ siteA d, ξ * (-f) z ≤ 0 := by
    intro z _
    simp only [ContinuousMap.neg_apply]
    nlinarith [mul_nonneg hξ (cert.f_bd z).1]
  have hacc : ∀ z w : Rd d, D'.internal (siteA d) z w ≤ D.internal (siteA d) z w := by
    intro z w
    rw [hD' (siteA d) hA]
    simpa only [Real.exp_zero, ENNReal.ofReal_one, one_mul] using
      (HigherDimLQGMetric.weylScaleOn_le_of_le (ξ := ξ) (f := -f) (D := D)
        (U := siteA d) (z := z) (w := w) hweight)
  have hnet' : D'.internal cert.Uo p q ≤ ENNReal.ofReal εnet := by
    rw [hD' cert.Uo cert.hUo]
    rw [HigherDimLQGMetric.weylScaleOn_of_eq_const (ξ := ξ) (f := -f)
      (D := D) (U := cert.Uo) (z := p) (w := q) (a := -(ξ * M)) (by
        intro z hz
        have hfM : f z = M := cert.f_eq z (cert.hUoU hz)
        simp only [ContinuousMap.neg_apply, hfM]
        ring)]
    simpa only [cert.θ_eq] using cert.net p hp q hq
  have hxp' : D'.internal (siteA d) x p ≤ ENNReal.ofReal ε₀ :=
    (hacc x p).trans hxp
  have hyq' : D'.internal (siteA d) q y ≤ ENNReal.ofReal ε₀ := by
    rw [D'.internal_comm]
    exact (hacc y q).trans hyq
  calc
    ENNReal.ofReal (D'.1 (x, y)) ≤ D'.internal univ x y :=
      D'.ofReal_le_internal univ x y
    _ ≤ D'.internal univ x p + D'.internal univ p q + D'.internal univ q y := by
      calc
        D'.internal univ x y ≤ D'.internal univ x p + D'.internal univ p y :=
          D'.internal_triangle univ x p y
        _ ≤ D'.internal univ x p +
            (D'.internal univ p q + D'.internal univ q y) :=
          add_le_add le_rfl (D'.internal_triangle univ p q y)
        _ = D'.internal univ x p + D'.internal univ p q + D'.internal univ q y :=
          by ac_rfl
    _ ≤ D'.internal (siteA d) x p + D'.internal cert.Uo p q +
          D'.internal (siteA d) q y := by
      exact add_le_add
        (add_le_add (D'.internal_anti (subset_univ _) _ _)
          (D'.internal_anti (subset_univ _) _ _))
        (D'.internal_anti (subset_univ _) _ _)
    _ ≤ ENNReal.ofReal ε₀ + ENNReal.ofReal εnet + ENNReal.ofReal ε₀ :=
      add_le_add (add_le_add hxp' hnet') hyq'

/-- A path from outside the radius-four ball into the inner core contains a
subpath in the collector whose endpoints are exactly one Euclidean unit apart.
This exact separation removes any need for a sign assumption on the exponent `b`. -/
private theorem restore_unit_crossing {P : ℝ → Rd d} {a c : ℝ}
    (hP : ContinuousOn P (Icc a c)) (ha : P a ∉ siteB d)
    (hc : P c ∉ siteB d) (hcore : ∃ t ∈ Icc a c, ‖P t‖ ≤ 3 / 2) :
    ∃ s t : ℝ, a ≤ s ∧ s ≤ t ∧ t ≤ c ∧
      (∀ τ ∈ Icc s t, P τ ∈ siteC d) ∧ ‖P s - P t‖ = 1 := by
  let B : Set (Rd d) := closedBall (0 : Rd d) (3 / 2)
  have hBa : P a ∉ ball (0 : Rd d) (3 / 2) := by
    intro h
    apply ha
    change P a ∈ ball (0 : Rd d) 4
    exact (ball_subset_ball (by norm_num : (3 / 2 : ℝ) ≤ 4)) h
  have hBc : P c ∉ ball (0 : Rd d) (3 / 2) := by
    intro h
    apply hc
    change P c ∈ ball (0 : Rd d) 4
    exact (ball_subset_ball (by norm_num : (3 / 2 : ℝ) ≤ 4)) h
  have hinner : ∃ t ∈ Icc a c, P t ∈ B := by
    obtain ⟨t, ht, hnorm⟩ := hcore
    exact ⟨t, ht, by simpa only [B, mem_closedBall, dist_zero_right] using hnorm⟩
  obtain ⟨t₀, ht₀, hPt₀⟩ := hinner
  obtain ⟨t, u, hat, htu, huc, hPt, hPu, hfirst⟩ :=
    HigherDimLQGMetric.s7b_first_last_hit hP isClosed_closedBall
      ht₀ hPt₀
  have havoidBall := HigherDimLQGMetric.s7b_first_last_avoid_open_closed hP isOpen_ball
    ⟨hat, htu, huc⟩ hBa hBc (by
      intro τ hτ hτcl
      exact hfirst τ hτ (by
        rwa [closure_ball (0 : Rd d) (by norm_num : (3 / 2 : ℝ) ≠ 0)] at hτcl))
  have htnorm : ‖P t‖ = 3 / 2 := by
    have hle : ‖P t‖ ≤ 3 / 2 := by
      simpa only [B, mem_closedBall, dist_zero_right] using hPt
    have hge : 3 / 2 ≤ ‖P t‖ := by
      have hnot := havoidBall.1 t ⟨hat, le_rfl⟩
      simpa only [mem_ball, dist_zero_right, not_lt] using hnot
    exact le_antisymm hle hge
  let g : ℝ → ℝ := fun r => ‖P r - P t‖
  have hg : ContinuousOn g (Icc a t) := by
    exact continuous_norm.comp_continuousOn
      ((hP.mono (Icc_subset_Icc le_rfl (htu.trans huc))).sub continuousOn_const)
  have hnorma : 4 ≤ ‖P a‖ := by
    simpa only [siteB, mem_ball, dist_zero_right, not_lt] using ha
  have hga : 1 ≤ g a := by
    have htri := norm_add_le (P a - P t) (P t)
    have htri' : ‖P a‖ ≤ ‖P a - P t‖ + ‖P t‖ := by
      simpa only [sub_add_cancel] using htri
    dsimp only [g]
    linarith only [htri', hnorma, htnorm]
  have hgt : g t = 0 := by simp only [g, sub_self, norm_zero]
  obtain ⟨r, hr, hgr⟩ := intermediate_value_Icc' hat hg
    (show g t ≤ 1 ∧ 1 ≤ g a by rw [hgt]; exact ⟨by norm_num, hga⟩)
  have hrSphere : P r ∈ sphere (P t) 1 := by
    simpa only [mem_sphere, dist_eq_norm, g] using hgr
  obtain ⟨r₀, s, har₀, hr₀s, hst, hPr₀, hPs, hlast⟩ :=
    HigherDimLQGMetric.s7b_first_last_hit
      (hP.mono (Icc_subset_Icc le_rfl (htu.trans huc)))
      (K := sphere (P t) 1) isClosed_sphere (t₀ := r)
      ⟨hr.1, hr.2⟩ hrSphere
  have hsbound : a ≤ s := har₀.trans hr₀s
  have hgend : ∀ τ ∈ Icc s t, g τ ≤ 1 := by
    intro τ hτ
    by_contra hbad
    have hgtau : 1 < g τ := lt_of_not_ge hbad
    have hgsub : ContinuousOn g (Icc τ t) :=
      hg.mono (Icc_subset_Icc (hsbound.trans hτ.1) le_rfl)
    obtain ⟨v, hv, hgv⟩ := intermediate_value_Icc' hτ.2 hgsub
      (show g t ≤ 1 ∧ 1 ≤ g τ by rw [hgt]; exact ⟨by norm_num, hgtau.le⟩)
    have hτv : τ < v := lt_of_le_of_ne hv.1 (by
      intro heq
      subst v
      linarith only [hgv, hgtau])
    have hvSphere : P v ∈ sphere (P t) 1 := by
      simpa only [mem_sphere, dist_eq_norm, g] using hgv
    have hvlast := (hlast v ⟨hsbound.trans (hτ.1.trans hv.1), hv.2⟩ hvSphere).2
    exact (not_lt_of_ge hvlast) (hτ.1.trans_lt hτv)
  refine ⟨s, t, hsbound, hst, htu.trans huc, ?_, ?_⟩
  · intro τ hτ
    have hupper : ‖P τ‖ ≤ 5 / 2 := by
      have htri := norm_add_le (P τ - P t) (P t)
      have htri' : ‖P τ‖ ≤ ‖P τ - P t‖ + ‖P t‖ := by
        simpa only [sub_add_cancel] using htri
      dsimp only [g] at hgend
      linarith only [htri', hgend τ hτ, htnorm]
    have hlower : 3 / 2 ≤ ‖P τ‖ := by
      by_cases heq : τ = t
      · rw [heq, htnorm]
      · have hτt : τ < t := lt_of_le_of_ne hτ.2 heq
        have hnot : P τ ∉ B := by
          intro hτB
          have hfirstτ := (hfirst τ ⟨hsbound.trans hτ.1, hτ.2.trans (htu.trans huc)⟩ hτB).1
          exact (not_lt_of_ge hfirstτ) hτt
        have : ¬ ‖P τ‖ ≤ 3 / 2 := by
          simpa only [B, mem_closedBall, dist_zero_right] using hnot
        exact le_of_lt (lt_of_not_ge this)
    change 3 / 2 ≤ ‖P τ - 0‖ ∧ ‖P τ - 0‖ ≤ 5 / 2
    simpa only [sub_zero] using ⟨hlower, hupper⟩
  · simpa only [mem_sphere, dist_eq_norm] using hPs

/-- A source geodesic through the inner core is shortened by the network by
at least `H⁻¹ - 3ε₀`. -/
theorem network_saving {D E D' : ContMetric d} {f : C(Rd d, ℝ)}
    {ξ M θ h δsep ε₀ εnet εatt aout H b v d₀ : ℝ}
    (cert : ForcingCert D E f ξ M θ h δsep ε₀ εnet εatt aout H b v d₀)
    (hD' : IsWeylInternal ξ (-f) D D') (hξ : 0 ≤ ξ) (hnet : εnet ≤ ε₀)
    (P : ℝ → Rd d) (a c : ℝ) (hP : IsGeodSeg D P a c)
    (ha : P a ∉ siteB d) (hc : P c ∉ siteB d)
    (hcore : ∃ t ∈ Icc a c, ‖P t‖ ≤ 3 / 2) :
    ENNReal.ofReal (D'.1 (P a, P c)) + ENNReal.ofReal (H⁻¹ - 3 * ε₀) ≤
      ENNReal.ofReal (D.1 (P a, P c)) := by
  obtain ⟨s, t, has, hst, htc, hinside, hsep⟩ :=
    restore_unit_crossing hP.2.1 ha hc hcore
  have hshort := restore_certificate_shortcut cert hD' hξ
    (hinside s ⟨le_rfl, hst⟩) (hinside t ⟨hst, le_rfl⟩)
  have hε₀ : 0 ≤ ε₀ := by
    by_contra hn
    have hneg : ε₀ ≤ 0 := (lt_of_not_ge hn).le
    have hnegnet : εnet ≤ 0 := hnet.trans hneg
    have hzero : ENNReal.ofReal (D'.1 (P s, P t)) = 0 := by
      have hle : ENNReal.ofReal (D'.1 (P s, P t)) ≤ 0 := by
        simpa only [ENNReal.ofReal_eq_zero.mpr hneg,
          ENNReal.ofReal_eq_zero.mpr hnegnet, add_zero, zero_add] using hshort
      exact le_antisymm hle (by simp)
    have hdistzero : D'.1 (P s, P t) = 0 :=
      le_antisymm (ENNReal.ofReal_eq_zero.mp hzero) (D'.nonneg _ _)
    have heq : P s = P t := D'.eq_of_apply_eq_zero hdistzero
    rw [heq, sub_self, norm_zero] at hsep
    norm_num at hsep
  have hshortcut : ENNReal.ofReal (D'.1 (P s, P t)) ≤ ENNReal.ofReal (3 * ε₀) := by
    calc
      ENNReal.ofReal (D'.1 (P s, P t)) ≤
          ENNReal.ofReal ε₀ + ENNReal.ofReal εnet + ENNReal.ofReal ε₀ := hshort
      _ ≤ ENNReal.ofReal ε₀ + ENNReal.ofReal ε₀ + ENNReal.ofReal ε₀ :=
        add_le_add (add_le_add le_rfl (ENNReal.ofReal_le_ofReal hnet)) le_rfl
      _ = ENNReal.ofReal (3 * ε₀) := by
        have heq : ε₀ + ε₀ + ε₀ = 3 * ε₀ := by ring
        rw [← heq, ENNReal.ofReal_add (add_nonneg hε₀ hε₀) hε₀,
          ENNReal.ofReal_add hε₀ hε₀]
  have hdisc : ∀ x, 0 ≤ f x := fun x => (cert.f_bd x).1
  have hleft : D'.len P a s ≤ D.len P a s :=
    restore_discount_len_le hD' hξ hdisc
      (hP.2.1.mono (Icc_subset_Icc le_rfl (hst.trans htc)))
  have hright : D'.len P t c ≤ D.len P t c :=
    restore_discount_len_le hD' hξ hdisc
      (hP.2.1.mono (Icc_subset_Icc (has.trans hst) le_rfl))
  have hA : siteC d ⊆ siteA d := by
    intro x hx
    change 3 / 2 ≤ ‖x - 0‖ ∧ ‖x - 0‖ ≤ 5 / 2 at hx
    change 1 / 2 < ‖x - 0‖ ∧ ‖x - 0‖ < 7 / 2
    constructor <;> linarith only [hx.1, hx.2]
  have hlower : ENNReal.ofReal H⁻¹ ≤ D.len P s t := by
    have hraw := cert.lower (P s) (hinside s ⟨le_rfl, hst⟩)
      (P t) (hinside t ⟨hst, le_rfl⟩)
    rw [hsep, Real.one_rpow, mul_one] at hraw
    exact hraw.trans (D.internal_le_len hst
      (hP.2.1.mono (Icc_subset_Icc has htc))
      (fun τ hτ => hA (hinside τ hτ)))
  have htri : ENNReal.ofReal (D'.1 (P a, P c)) ≤
      D'.len P a s + ENNReal.ofReal (D'.1 (P s, P t)) + D'.len P t c := by
    have h₁ := D'.apply_triangle (P a) (P s) (P t)
    have h₂ := D'.apply_triangle (P a) (P t) (P c)
    have hh : D'.1 (P a, P c) ≤
        D'.1 (P a, P s) + D'.1 (P s, P t) + D'.1 (P t, P c) := by
      linarith only [h₁, h₂]
    have hraw : ENNReal.ofReal (D'.1 (P a, P c)) ≤
        ENNReal.ofReal (D'.1 (P a, P s)) +
          ENNReal.ofReal (D'.1 (P s, P t)) +
            ENNReal.ofReal (D'.1 (P t, P c)) := by
      simpa only [ENNReal.ofReal_add (add_nonneg (D'.nonneg _ _) (D'.nonneg _ _))
        (D'.nonneg _ _), ENNReal.ofReal_add (D'.nonneg _ _) (D'.nonneg _ _)] using
        ENNReal.ofReal_le_ofReal hh
    exact hraw.trans (add_le_add
      (add_le_add (D'.ofReal_le_len P has) le_rfl)
      (D'.ofReal_le_len P htc))
  by_cases hsave : 0 < H⁻¹ - 3 * ε₀
  · have hH : 0 ≤ H⁻¹ := by linarith only [hsave, hε₀]
    have hcost : 0 ≤ 3 * ε₀ := by nlinarith only [hε₀]
    have hdrop : ENNReal.ofReal (D'.1 (P a, P c)) + ENNReal.ofReal H⁻¹ ≤
        ENNReal.ofReal (D.1 (P a, P c)) + ENNReal.ofReal (3 * ε₀) := by
      calc
        ENNReal.ofReal (D'.1 (P a, P c)) + ENNReal.ofReal H⁻¹ ≤
            (D'.len P a s + ENNReal.ofReal (D'.1 (P s, P t)) +
              D'.len P t c) + ENNReal.ofReal H⁻¹ :=
          add_le_add htri le_rfl
        _ ≤ (D.len P a s + ENNReal.ofReal (3 * ε₀) + D.len P t c) +
              D.len P s t := by
          exact add_le_add
            (add_le_add (add_le_add hleft hshortcut) hright) hlower
        _ = ENNReal.ofReal (D.1 (P a, P c)) + ENNReal.ofReal (3 * ε₀) := by
          have hsplit : D.len P a c = D.len P a s + D.len P s t + D.len P t c := by
            calc
              D.len P a c = D.len P a t + D.len P t c :=
                (D.len_add P (has.trans hst) htc).symm
              _ = D.len P a s + D.len P s t + D.len P t c := by
                rw [D.len_add P has hst]
          calc
            D.len P a s + ENNReal.ofReal (3 * ε₀) + D.len P t c + D.len P s t =
                (D.len P a s + D.len P s t + D.len P t c) +
                  ENNReal.ofReal (3 * ε₀) := by ac_rfl
            _ = D.len P a c + ENNReal.ofReal (3 * ε₀) := by rw [← hsplit]
            _ = ENNReal.ofReal (D.1 (P a, P c)) + ENNReal.ofReal (3 * ε₀) := by
              rw [hP.2.2]
    have hreal : D'.1 (P a, P c) + H⁻¹ ≤ D.1 (P a, P c) + 3 * ε₀ := by
      apply (ENNReal.ofReal_le_ofReal_iff
        (add_nonneg (D.nonneg _ _) hcost)).mp
      simpa only [ENNReal.ofReal_add (D'.nonneg _ _) hH,
        ENNReal.ofReal_add (D.nonneg _ _) hcost] using hdrop
    have hfinish : D'.1 (P a, P c) + (H⁻¹ - 3 * ε₀) ≤ D.1 (P a, P c) := by
      linarith only [hreal]
    simpa only [ENNReal.ofReal_add (D'.nonneg _ _) hsave.le] using
      ENNReal.ofReal_le_ofReal hfinish
  · have hsave' : H⁻¹ - 3 * ε₀ ≤ 0 := le_of_not_gt hsave
    have hglobal : ENNReal.ofReal (D'.1 (P a, P c)) ≤
        ENNReal.ofReal (D.1 (P a, P c)) := by
      calc
        ENNReal.ofReal (D'.1 (P a, P c)) ≤ D'.len P a c := D'.ofReal_le_len P hP.1
        _ ≤ D.len P a c := restore_discount_len_le hD' hξ hdisc hP.2.1
        _ = ENNReal.ofReal (D.1 (P a, P c)) := hP.2.2
    simpa only [ENNReal.ofReal_eq_zero.mpr hsave', add_zero] using hglobal

end HigherDimLQGContinuity
