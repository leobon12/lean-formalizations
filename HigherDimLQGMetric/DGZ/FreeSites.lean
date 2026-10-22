import HigherDimLQGMetric.DGZ.FreeSitesFilled

/-!
# Free sites: free-site lemma, hole lemma, free surgery (packet L3a1, MA7 D-F1, D-F3, D-FS)

Source: Ding–Gwynne–Zhuang, arXiv:2310.03996v5 ([2]), §4: the unproved d-dimensional "duality" steps
of Lemma 4.1 (TeX l. 1348, 1355–1357), Lemma 4.2 (l. 1444), Prop 4.3 (l. 1520) and Lemma 4.9
(l. 1878, 1898). Planning audit `planning/audits/MA7-ref2-sections-4-6.md`, gaps G1–G3 and
Details (a) D-F1, D-F3, D-FS; the statement shapes are those of Details (c) §A
(`DGZ/FreeSitesDefs.lean`).

Main results (namespace `HigherDimLQGMetric.DGZ`):

* `freeSiteLemma (d) (hd : 2 ≤ d) : FreeSiteLemma d` (D-F1): if every closed cluster is bounded with
  `ℓ^∞`-diameter `≤ D`, every `*`-connected set of diameter `> D` contains a free site;
* `holeLemma (d) (hd : 2 ≤ d) : HoleLemma d` (D-F3): every site is within `D + 1` of a free site;
* `freeSurgery (d) : FreeSurgery d` (D-FS(i), every `d`): two free sites are joined by an open
  L-path within `D + 1` of any reference L-path between them (HigherDimLFPP `surgeryLemma`);
* `freeToInfinity (d) (hd : 2 ≤ d) : FreeToInfinity d` (D-FS(ii)): if the closed sites lie in a
  box, a free site is joined by an open L-path to every site outside the box;
* `freeSite_of_reflTransGen` (D-FS(iii)): conversely, an open L-path to a site outside such a box
  makes its start free; with `freeSite_iff_reflTransGen` (free sites = the unbounded open cluster),
  `freeSite_of_not_withinInf` (sites outside the box are free) and `reflTransGen_of_freeSite`
  (free sites are joined to each other by open L-paths, every `d`).

Proof of D-F1 (MA7 D-F1, made explicit). Suppose no site of `S` is free; then every site of `S`
lies in the filled cluster `filled C` of some closed cluster `C`
(`exists_mem_filled_of_not_freeSite`). Fix `x ∈ S`. The closed clusters whose filled cluster
contains `x` lie in the box of radius `D` around `x` (D-F0 (a)), so there are finitely many; choose
`C₀` among them with `filled C₀` of maximal
cardinality. Then every site of `S` lies in `filled C₀`, by induction along a `*`-path in `S` from
`x`: if `s ∈ filled C₀` and `s' ∈ filled C'` are `*`-adjacent, then by D-F0 (b) either `C' = C₀`, or
`C' ⊆ Encl(C₀)` (then `filled C' ⊆ filled C₀` by (c)), or `C₀ ⊆ Encl(C')` (then
`filled C₀ ⊆ filled C'`, and maximality of the cardinality forces equality), or the two are mutually
exterior, which (d) excludes because `s, s'` are `*`-adjacent. So `S ⊆ filled C₀`, whose diameter is
`≤ D` by (a): a contradiction.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace HigherDimLQGMetric

namespace DGZ

open HigherDimLFPP HigherDimLFPP.Perc
open Relation

variable {d : ℕ}

/-! ### Non-free sites lie in filled clusters -/

/-- Under `SmallClusters`, a site that is not free lies in the filled cluster of some closed
cluster: a closed site lies in its own cluster, an open site that is not free is enclosed. -/
lemma exists_mem_filled_of_not_freeSite (hd : 1 ≤ d) {O : Set (Zd d)} {D : ℕ}
    (hsmall : SmallClusters O D) {x : Zd d} (hx : ¬ FreeSite O x) :
    ∃ C, IsClosedCluster O C ∧ x ∈ filled C := by
  by_cases hxO : x ∈ O
  · have h : ¬ ∀ C, IsClosedCluster O C → x ∉ filled C := fun h =>
      hx (freeSite_iff_filled.2 ⟨hxO, h⟩)
    push Not at h
    exact h
  · have hC := isClosedCluster_closedComp hxO
    exact ⟨closedComp O x, hC, mem_filled_of_mem hd (hsmall _ hC).1 (mem_closedComp_self O x)⟩

/-- Under `SmallClusters O D` (`d ≥ 2`), only finitely many closed clusters have a filled cluster
containing a given site `x`: they all lie in the box of radius `D` around `x`. -/
lemma finite_setOf_mem_filled (hd : 2 ≤ d) {O : Set (Zd d)} {D : ℕ}
    (hsmall : SmallClusters O D) (x : Zd d) :
    {C | IsClosedCluster O C ∧ x ∈ filled C}.Finite := by
  refine ((boxF x D).finite_toSet.finite_subsets).subset ?_
  rintro C ⟨hC, hxC⟩ c hc
  exact Finset.mem_coe.2
    (mem_boxF.2 (withinInf_of_mem_filled_of_mem hd (hsmall C hC).2 hxC hc).symm)

/-! ### D-F1: the free-site lemma -/

/-- **MA7 D-F1: free-site lemma** (`d ≥ 2`). If every closed cluster is bounded with `ℓ^∞`-diameter
`≤ D`, every `*`-connected set containing two sites at `ℓ^∞`-distance `> D` contains a free site. -/
theorem freeSiteLemma (d : ℕ) (hd : 2 ≤ d) : FreeSiteLemma d := by
  intro O D hsmall S hS hfar
  obtain ⟨x, hxS, y, hyS, hxy⟩ := hfar
  by_contra hno
  push Not at hno
  have hcov : ∀ s ∈ S, ∃ C, IsClosedCluster O C ∧ s ∈ filled C := fun s hs =>
    exists_mem_filled_of_not_freeSite (by omega) hsmall (hno s hs)
  -- a filled cluster of maximal cardinality containing `x`
  obtain ⟨C₀, ⟨hC₀, hxC₀⟩, hmax⟩ := Set.exists_max_image
    {C | IsClosedCluster O C ∧ x ∈ filled C} (fun C => (filled C).ncard)
    (finite_setOf_mem_filled hd hsmall x) (hcov x hxS)
  -- every site of `S` lies in `filled C₀`
  have hsub : ∀ s ∈ S, s ∈ filled C₀ := by
    intro s hs
    have hpath : ReflTransGen (StepIn S SAdj) x s := hS x hxS s hs
    clear hs
    induction hpath with
    | refl => exact hxC₀
    | @tail b c _ hbc ih =>
      obtain ⟨C', hC', hcC'⟩ := hcov c hbc.2.1
      by_cases hCC : C₀ = C'
      · rw [hCC]
        exact hcC'
      rcases (closedCluster_subset_ext_or_encl hC₀ hC' hCC).2 with hext | hencl
      · rcases (closedCluster_subset_ext_or_encl hC' hC₀ (Ne.symm hCC)).2 with hext' | hencl'
        · -- mutually exterior: excluded by the non-adjacency of D-F0 (d)
          exact absurd hbc.2.2 ((filled_disjoint_nonadj hd hC₀ hC' (hsmall C₀ hC₀).1
            (hsmall C' hC').1 hext hext').2 b ih c hcC')
        · -- `C₀ ⊆ Encl(C')`: nested, and maximality of `C₀` forces equality
          have hsub' : filled C₀ ⊆ filled C' :=
            filled_subset_of_subset_encl hd (hsmall C' hC').1 hencl'
          have hle : (filled C').ncard ≤ (filled C₀).ncard := hmax C' ⟨hC', hsub' hxC₀⟩
          have heq : filled C₀ = filled C' :=
            Set.eq_of_subset_of_ncard_le hsub' hle (finite_filled hd (hsmall C' hC').2)
          rw [heq]
          exact hcC'
      · -- `C' ⊆ Encl(C₀)`: nested
        exact filled_subset_of_subset_encl hd (hsmall C₀ hC₀).1 hencl hcC'
  exact hxy (withinInf_of_mem_filled hd (hsmall C₀ hC₀).2 (hsub x hxS) (hsub y hyS))

/-! ### D-F3: the hole lemma -/

/-- **MA7 D-F3: hole lemma** (`d ≥ 2`). If every closed cluster is bounded with `ℓ^∞`-diameter
`≤ D`, every site `x` has a free site within `ℓ^∞`-distance `D + 1`: apply the free-site lemma to
the segment `{x + t e₀ : 0 ≤ t ≤ D + 1}`. -/
theorem holeLemma (d : ℕ) (hd : 2 ≤ d) : HoleLemma d := by
  intro O D hsmall x
  set i₀ : Fin d := ⟨0, by omega⟩ with hi₀
  set S : Set (Zd d) := {z | ∃ t : ℕ, t ≤ D + 1 ∧ z = x + Pi.single i₀ (t : ℤ)} with hSdef
  have hmem : ∀ t : ℕ, t ≤ D + 1 → x + Pi.single i₀ (t : ℤ) ∈ S := fun t ht => ⟨t, ht, rfl⟩
  have hx0 : x ∈ S := ⟨0, Nat.zero_le _, by simp⟩
  -- every site of the segment is joined to `x` inside the segment
  have hconn0 : ∀ z ∈ S, ReflTransGen (StepIn S SAdj) x z := by
    rintro z ⟨t, ht, rfl⟩
    have h : ReflTransGen (StepIn S LAdj) x (x + Pi.single i₀ (t : ℤ)) :=
      reflTransGen_add_single_nat x i₀ t fun s hs => hmem s (by omega)
    exact ReflTransGen.mono (fun a b (hab : StepIn S LAdj a b) =>
      (⟨hab.1, hab.2.1, hab.2.2.sAdj⟩ : StepIn S SAdj a b)) _ _ h
  have hS : ConnIn S SAdj := fun z hz z' hz' =>
    (reflTransGen_sAdj_symm (hconn0 z hz)).trans (hconn0 z' hz')
  have hfar : ∃ a ∈ S, ∃ b ∈ S, ¬ WithinInf (D : ℤ) a b := by
    refine ⟨x, hx0, x + Pi.single i₀ ((D + 1 : ℕ) : ℤ), hmem (D + 1) le_rfl, fun h => ?_⟩
    have h0 := h i₀
    rw [add_single_apply_self, abs_le] at h0
    omega
  obtain ⟨y, ⟨t, ht, rfl⟩, hfree⟩ := freeSiteLemma d hd O D hsmall S hS hfar
  refine ⟨_, fun i => ?_, hfree⟩
  rw [add_single_apply]
  split_ifs <;> rw [abs_le] <;> constructor <;> omega

/-! ### Forms for consumers: sites of an L-path -/

/-- The sites of an L-chain starting at `a` are joined to `a` by a `*`-path through sites of any
set `T` containing the chain. -/
lemma reflTransGen_of_isChain_cons {T : Set (Zd d)} :
    ∀ (a : Zd d) (l : List (Zd d)), (a :: l).IsChain LAdj → (∀ x ∈ a :: l, x ∈ T) →
      ∀ x ∈ a :: l, ReflTransGen (StepIn T SAdj) a x
  | a, [], _, _, x, hx => by
    rw [List.mem_singleton] at hx
    rw [hx]
  | a, b :: l, hch, hT, x, hx => by
    rw [List.isChain_cons_cons] at hch
    rcases List.mem_cons.1 hx with hx | hx
    · rw [hx]
    · exact ReflTransGen.head
        ⟨hT a List.mem_cons_self, hT b (List.mem_cons_of_mem _ List.mem_cons_self), hch.1.sAdj⟩
        (reflTransGen_of_isChain_cons b l hch.2
          (fun y hy => hT y (List.mem_cons_of_mem _ hy)) x hx)

/-- The set of sites of an L-chain is `*`-connected. -/
lemma connIn_of_isChain {l : List (Zd d)} (hl : l.IsChain LAdj) : ConnIn {x | x ∈ l} SAdj := by
  intro x hx y hy
  cases l with
  | nil => exact absurd hx List.not_mem_nil
  | cons a t =>
    have hT : ∀ z ∈ a :: t, z ∈ {x | x ∈ a :: t} := fun z hz => hz
    exact (reflTransGen_sAdj_symm (reflTransGen_of_isChain_cons a t hl hT x hx)).trans
      (reflTransGen_of_isChain_cons a t hl hT y hy)

/-- **Free-site lemma, path form** (`d ≥ 2`; as used in MA7 D-4.9 (3)): an L-path containing two
sites at `ℓ^∞`-distance `> D` contains a free site when the closed clusters are small. -/
theorem exists_freeSite_mem_of_isChain (hd : 2 ≤ d) {O : Set (Zd d)} {D : ℕ}
    (hsmall : SmallClusters O D) {l : List (Zd d)} (hl : l.IsChain LAdj)
    (hfar : ∃ x ∈ l, ∃ y ∈ l, ¬ WithinInf (D : ℤ) x y) : ∃ x ∈ l, FreeSite O x :=
  freeSiteLemma d hd O D hsmall {x | x ∈ l} (connIn_of_isChain hl) hfar

/-- **Some site is open** (every `d`; as used in MA7 D-4.10): if every closed cluster has
`ℓ^∞`-diameter `≤ D`, a `*`-connected set containing two sites at `ℓ^∞`-distance `> D` contains an
open site (otherwise it would lie in one closed cluster). -/
theorem exists_mem_open_of_connIn {O : Set (Zd d)} {D : ℕ}
    (hdiam : ∀ C, IsClosedCluster O C → ∀ y ∈ C, ∀ y' ∈ C, WithinInf (D : ℤ) y y')
    {S : Set (Zd d)} (hS : ConnIn S SAdj) (hfar : ∃ x ∈ S, ∃ y ∈ S, ¬ WithinInf (D : ℤ) x y) :
    ∃ x ∈ S, x ∈ O := by
  obtain ⟨x, hxS, y, hyS, hxy⟩ := hfar
  by_contra hno
  push Not at hno
  obtain ⟨C, hC, hSC⟩ := exists_isClosedCluster_superset (O := O) hS (fun z hz => hno z hz) hxS
  exact hxy (hdiam C hC x (hSC hxS) y (hSC hyS))

/-! ### D-FS: free surgery and the unbounded open cluster -/

/-- A finite list of sites lies in a box `[-M, M]^d`. -/
lemma exists_withinInf_of_list (γ : List (Zd d)) : ∃ M : ℤ, ∀ x ∈ γ, WithinInf M x 0 := by
  induction γ with
  | nil => exact ⟨0, fun x hx => absurd hx List.not_mem_nil⟩
  | cons a t ih =>
    obtain ⟨M, hM⟩ := ih
    refine ⟨max M (∑ i, |a i|), fun x hx => ?_⟩
    rcases List.mem_cons.1 hx with rfl | hx
    · intro i
      rw [Pi.zero_apply, sub_zero]
      exact (Finset.single_le_sum (f := fun k => |x k|) (fun k _ => abs_nonneg (x k))
        (Finset.mem_univ i)).trans (le_max_right _ _)
    · exact (hM x hx).mono (le_max_left _ _)

/-- **MA7 D-FS(i): free surgery** (every `d`). Every closed cluster meeting the reference path `γ`
has diameter `≤ D`, so lies in `[-R, R]^d` with `R = D + max_γ |·|_∞`, and contains neither free
endpoint in its filled cluster; HigherDimLFPP's `surgeryLemma` gives the open path. -/
theorem freeSurgery (d : ℕ) : FreeSurgery d := by
  intro O D hsmall γ u v hchain hhead hlast hu hv
  obtain ⟨M, hM⟩ := exists_withinInf_of_list γ
  refine surgeryLemma d O D ((D : ℤ) + M) γ u v hchain hhead hlast hu.1 hv.1 ?_
  rintro C hC ⟨x, hxγ, hxC⟩
  have hdiam := (hsmall C hC).2
  have hbox : ∀ c ∈ C, WithinInf ((D : ℤ) + M) c 0 := fun c hc =>
    (hdiam c hc x hxC).trans (hM x hxγ)
  exact ⟨hdiam, hbox, hu.2 C hC _ hbox, hv.2 C hC _ hbox⟩

/-- `ℤ^d` is L-connected: any two sites are joined by an L-path (change one coordinate at a
time). -/
lemma reflTransGen_lAdj_univ (u v : Zd d) :
    ReflTransGen (StepIn (Set.univ : Set (Zd d)) LAdj) u v := by
  have key : ∀ n : ℕ, ReflTransGen (StepIn (Set.univ : Set (Zd d)) LAdj) u (coordPath u v n) := by
    intro n
    induction n with
    | zero => rw [coordPath_zero]
    | succ n ih =>
      by_cases hn : n < d
      · have hupd : coordPath u v (n + 1) =
            Function.update (coordPath u v n) ⟨n, hn⟩ (v ⟨n, hn⟩) := by
          funext k
          by_cases hk : k = ⟨n, hn⟩
          · subst hk
            simp [coordPath]
          · rw [Function.update_of_ne hk]
            have hkn : k.val ≠ n := fun h => hk (Fin.ext h)
            have e : (k.val < n + 1) ↔ (k.val < n) := by omega
            simp only [coordPath, e]
        rw [hupd]
        exact ih.trans (reflTransGen_update _ _ _ fun _ _ _ => Set.mem_univ _)
      · rw [coordPath_of_le u v (by omega : d ≤ n + 1)]
        rwa [coordPath_of_le u v (by omega : d ≤ n)] at ih
  have h := key d
  rwa [coordPath_of_le u v le_rfl] at h

/-- Any two sites are the endpoints of an L-chain (a reference path for `FreeSurgery`). -/
lemma exists_lAdj_chain (u v : Zd d) :
    ∃ γ : List (Zd d), γ.IsChain LAdj ∧ γ.head? = some u ∧ γ.getLast? = some v := by
  obtain ⟨l, hl, hlast⟩ :=
    List.exists_isChain_cons_of_relationReflTransGen (reflTransGen_lAdj_univ u v)
  refine ⟨u :: l, hl.imp fun _ _ h => h.2.2, rfl, ?_⟩
  rw [List.getLast?_eq_some_getLast (List.cons_ne_nil u l), hlast]

/-- **Free sites are joined by open L-paths** (every `d`; MA7 D-FS(i) along any reference path). -/
theorem reflTransGen_of_freeSite {O : Set (Zd d)} {D : ℕ} (hsmall : SmallClusters O D)
    {u v : Zd d} (hu : FreeSite O u) (hv : FreeSite O v) :
    ReflTransGen (StepIn O LAdj) u v := by
  obtain ⟨γ, hγ, hh, hl⟩ := exists_lAdj_chain u v
  have hsub : {y | y ∈ O ∧ ∃ x ∈ γ, WithinInf ((D : ℤ) + 1) y x} ⊆ O := fun _ hy => hy.1
  exact reflTransGen_stepIn_mono hsub (freeSurgery d O D hsmall γ u v hγ hh hl hu hv)

/-- **MA7 D-FS(iii)** (`d ≥ 2`): if all closed sites lie in `[-R, R]^d`, a site joined by an open
L-path to a site outside the box is free (the path avoids every closed cluster, and the far end
lies in the exterior of every subset of the box). No hypothesis on cluster sizes is needed. -/
theorem freeSite_of_reflTransGen (hd : 2 ≤ d) {O : Set (Zd d)} {R : ℤ}
    (hR : ∀ y, y ∉ O → WithinInf R y 0) {u v : Zd d} (hv : ¬ WithinInf R v 0)
    (huv : ReflTransGen (StepIn O LAdj) u v) : FreeSite O u := by
  have hvO : v ∈ O := by
    by_contra h
    exact hv (hR v h)
  refine ⟨mem_of_reflTransGen_stepIn' huv hvO, fun C hC R' hR' => ?_⟩
  have hCR : ∀ c ∈ C, WithinInf R c 0 := fun c hc => hR c (hC.2.1 hc)
  have hOC : O ⊆ Cᶜ := fun y hy hyC => hC.2.1 hyC hy
  have hvE : v ∈ Ext R C := mem_ext_of_not_withinInf hd hCR hv
  exact ext_subset_ext hd hCR hR' (mem_ext_of_reflTransGen (reflTransGen_stepIn_mono hOC huv) hvE)

/-- If all closed sites lie in `[-R, R]^d` (`d ≥ 2`), every site outside the box is free. -/
lemma freeSite_of_not_withinInf (hd : 2 ≤ d) {O : Set (Zd d)} {R : ℤ}
    (hR : ∀ y, y ∉ O → WithinInf R y 0) {v : Zd d} (hv : ¬ WithinInf R v 0) : FreeSite O v :=
  freeSite_of_reflTransGen hd hR hv ReflTransGen.refl

/-- **MA7 D-FS(ii)** (`d ≥ 2`): if the closed clusters are small and all closed sites lie in
`[-R, R]^d`, a free site is joined by an open L-path to every site outside the box (such a site is
free, `freeSite_of_not_withinInf`; then free surgery along any reference path). -/
theorem freeToInfinity (d : ℕ) (hd : 2 ≤ d) : FreeToInfinity d := by
  intro O D hsmall R hR u v hu hv
  exact reflTransGen_of_freeSite hsmall hu (freeSite_of_not_withinInf hd hR hv)

/-- **Free sites form the unbounded open cluster** (MA7 D-FS(ii)–(iii), `d ≥ 2`): if the closed
clusters are small and all closed sites lie in `[-R, R]^d`, a site is free iff it is joined by an
open L-path to some site outside the box (then, by `freeToInfinity`, to every such site). -/
theorem freeSite_iff_reflTransGen (hd : 2 ≤ d) {O : Set (Zd d)} {D : ℕ}
    (hsmall : SmallClusters O D) {R : ℤ} (hR : ∀ y, y ∉ O → WithinInf R y 0) {u : Zd d} :
    FreeSite O u ↔ ∃ v, ¬ WithinInf R v 0 ∧ ReflTransGen (StepIn O LAdj) u v := by
  constructor
  · intro hu
    have hout : ¬ WithinInf R (fun _ => R + 1 : Zd d) 0 := fun h => by
      have h0 := h ⟨0, by omega⟩
      simp only [Pi.zero_apply, sub_zero, abs_le] at h0
      omega
    exact ⟨_, hout, freeToInfinity d hd O D hsmall R hR u _ hu hout⟩
  · rintro ⟨v, hv, huv⟩
    exact freeSite_of_reflTransGen hd hR hv huv

end DGZ

end HigherDimLQGMetric
