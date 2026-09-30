import QuantumZipper.Proofs.Zipper.FieldLawler2Max
import QuantumZipper.Proofs.Thm18.LWExcDefs

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# Field–Lawler Corollary 4.2, analytic form, for finitely many real crosscuts (task FL2-C42)

Source: L. S. Field, G. F. Lawler, *Escape probability and transience for SLE*, EJP 20 (2015),
§4, Corollary 4.2, p. 11 (`literature/1407.3314.pdf`): `E_z[V] ≤ 2 P_z{σ_C < τ}`, where `V` is
the number of distinct crosscuts (on the circle `C`, here normalized to the real line) visited
before leaving `D`.

In harmonic-measure form, for crosscuts `I k = (a k, b k) ⊆ ℝ` of `D` with `h k` the harmonic
measure of `I k` in `D \ I k` and `w` that of `A = ⋃ I k` in `U = D \ A`:
`∑ k, h k z ≤ 2 w z` on `U`.

Proof route. FL's proof is probabilistic: `E_z V ≤ P_z{σ_C < τ} sup_{w ∈ C} E_w V` (strong Markov)
and `E_w V ≤ 2` since, by Prop 4.1, from a point of a crosscut the number of further crosscuts
visited is dominated by a geometric variable of parameter `1/2`. We replace both steps by
maximum-principle comparisons (own analytic rendering of FL's argument, no Brownian motion):
* `fl2C42_dom` (≙ strong Markov step): if `1 + ∑_{j ∈ S, j ≠ i} h j ≤ M` on every `I i`, `i ∈ S`,
  then `∑_{j ∈ S} h j ≤ M · v` on `D \ ⋃_{i ∈ S} I i`, `v` the harmonic measure of that union
  (Lindelöf maximum principle `fl2_harm_le_zero_off_finite`, exceptional set = endpoints).
* `fl2C42_main` (≙ geometric domination): with `M = sup_{k, p ∈ I k} (1 + ∑_{j ≠ k} h j p)`,
  `fl2C42_dom` for `S = {j ≠ k}` and Prop 4.1 (`u k ≤ 1/2` on `I k`) give `M ≤ 1 + M/2`,
  so `M ≤ 2`; then `fl2C42_dom` for `S = univ` gives the claim.
-/

open Filter Set Metric Complex
open scoped Topology

namespace QuantumZipper
namespace FieldLawler

open QuantumZipper.Thm18Asm.LWFar

/-- The real crosscut `(a, b) ⊆ ℝ ⊆ ℂ`. -/
def fl2C42Cut (a b : ℝ) : Set ℂ := (fun t : ℝ => (t : ℂ)) '' Ioo a b

lemma fl2C42Cut_closure {a b : ℝ} {z : ℂ} (hz : z ∈ closure (fl2C42Cut a b)) :
    z ∈ fl2C42Cut a b ∨ z = a ∨ z = b := by
  have hc : IsClosed ((fun t : ℝ => (t : ℂ)) '' Icc a b) :=
    (isCompact_Icc.image continuous_ofReal).isClosed
  obtain ⟨t, ht, rfl⟩ := closure_minimal (image_mono Ioo_subset_Icc_self) hc hz
  rcases eq_or_lt_of_le ht.1 with h | h
  · right; left; rw [h]
  rcases eq_or_lt_of_le ht.2 with h' | h'
  · right; right; rw [h']
  · left; exact ⟨t, ⟨h, h'⟩, rfl⟩

lemma fl2C42Cut_bdd (a b : ℝ) : Bornology.IsBounded (fl2C42Cut a b) :=
  (isCompact_Icc.image continuous_ofReal).isBounded.subset (image_mono Ioo_subset_Icc_self)

lemma fl2C42Cut_isOpen {D : Set ℂ} (hD : IsOpen D) {a b : ℝ} (ha : (a : ℂ) ∉ D)
    (hb : (b : ℂ) ∉ D) : IsOpen (D \ fl2C42Cut a b) := by
  have e : D \ fl2C42Cut a b = D ∩ (closure (fl2C42Cut a b))ᶜ := by
    ext z
    constructor
    · rintro ⟨hzD, hzC⟩
      refine ⟨hzD, fun hc => ?_⟩
      rcases fl2C42Cut_closure hc with h | rfl | rfl
      · exact hzC h
      · exact ha hzD
      · exact hb hzD
    · rintro ⟨hzD, hzC⟩
      exact ⟨hzD, fun h => hzC (subset_closure h)⟩
  rw [e]
  exact hD.inter isClosed_closure.isOpen_compl

lemma fl2C42_union_isOpen {n : ℕ} {D : Set ℂ} (hD : IsOpen D) {a b : Fin n → ℝ}
    (ha : ∀ k, (a k : ℂ) ∉ D) (hb : ∀ k, (b k : ℂ) ∉ D) (S : Finset (Fin n)) :
    IsOpen (D \ ⋃ i ∈ S, fl2C42Cut (a i) (b i)) := by
  have e : D \ ⋃ i ∈ S, fl2C42Cut (a i) (b i) = D ∩ ⋂ i ∈ S, (D \ fl2C42Cut (a i) (b i)) := by
    ext z
    simp only [Set.mem_sdiff, mem_iUnion, mem_inter_iff, mem_iInter, not_exists]
    constructor
    · rintro ⟨hzD, hz⟩
      exact ⟨hzD, fun i hi => ⟨hzD, hz i hi⟩⟩
    · rintro ⟨hzD, hz⟩
      exact ⟨hzD, fun i hi => (hz i hi).2⟩
  rw [e]
  exact hD.inter (isOpen_biInter_finset fun i _ => fl2C42Cut_isOpen hD (ha i) (hb i))

/-- A frontier point of `D \ T` outside `T` is outside `D`, so points of `D` stay away. -/
lemma fl2C42_not_mem_closure_frontier {D T : Set ℂ} (hD : IsOpen D) (hW : IsOpen (D \ T))
    {x : ℂ} (hx : x ∈ D) : x ∉ closure (frontier (D \ T) \ T) := by
  have hsub : frontier (D \ T) \ T ⊆ Dᶜ := by
    rintro y ⟨hy, hyT⟩ hyD
    rw [hW.frontier_eq] at hy
    exact hy.2 ⟨hyD, hyT⟩
  exact fun hc => closure_minimal hsub hD.isClosed_compl hc hx

lemma fl2C42_harm_sum {ι : Type*} (s : Finset ι) (g : ι → ℂ → ℝ) {x : ℂ}
    (hg : ∀ i ∈ s, InnerProductSpace.HarmonicAt (g i) x) :
    InnerProductSpace.HarmonicAt (fun z => ∑ i ∈ s, g i z) x := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert j s hj ih =>
    have e : (fun z => ∑ i ∈ insert j s, g i z) = g j + fun z => ∑ i ∈ s, g i z := by
      funext z; simp [Finset.sum_insert hj]
    rw [e]
    exact (hg j (Finset.mem_insert_self _ _)).add
      (ih fun i hi => hg i (Finset.mem_insert_of_mem hi))

lemma fl2C42_delta {U : Set ℂ} {f : ℂ → ℝ} {x₀ : ℂ} {ε : ℝ}
    (hev : ∀ᶠ y in 𝓝[U] x₀, f y < ε) : ∃ δ > 0, ∀ y ∈ U, dist y x₀ < δ → f y ≤ ε := by
  obtain ⟨δ, hδ, hsub⟩ := Metric.mem_nhdsWithin_iff.1 hev
  exact ⟨δ, hδ, fun y hy hd => (hsub ⟨mem_ball.2 hd, hy⟩).le⟩

/-- **Domination step** (analytic form of the strong-Markov step in FL Cor 4.2, p. 11): if
`1 + ∑_{j ∈ S, j ≠ i} h j ≤ M` on every crosscut `I i`, `i ∈ S`, then `∑_{j ∈ S} h j ≤ M v` on
`D \ ⋃_{i ∈ S} I i`, where `v` is the harmonic measure of `⋃_{i ∈ S} I i` there. -/
theorem fl2C42_dom {n : ℕ} {D : Set ℂ} {a b : Fin n → ℝ} (hD : IsOpen D)
    (hsub : ∀ k, ∀ t ∈ Ioo (a k) (b k), (t : ℂ) ∈ D)
    (ha : ∀ k, (a k : ℂ) ∉ D) (hb : ∀ k, (b k : ℂ) ∉ D)
    (hdisj : Pairwise fun i j => Disjoint (Ioo (a i) (b i)) (Ioo (a j) (b j)))
    {h : Fin n → ℂ → ℝ}
    (hh : ∀ k, IsHarmMeas (D \ fl2C42Cut (a k) (b k)) (fl2C42Cut (a k) (b k)) (h k))
    (S : Finset (Fin n)) {v : ℂ → ℝ}
    (hv : IsHarmMeas (D \ ⋃ i ∈ S, fl2C42Cut (a i) (b i)) (⋃ i ∈ S, fl2C42Cut (a i) (b i)) v)
    {M : ℝ} (hM0 : 0 ≤ M)
    (hM : ∀ i ∈ S, ∀ t ∈ Ioo (a i) (b i), 1 + ∑ j ∈ S.erase i, h j t ≤ M) :
    ∀ z ∈ D \ ⋃ i ∈ S, fl2C42Cut (a i) (b i), ∑ j ∈ S, h j z ≤ M * v z := by
  set A := ⋃ i ∈ S, fl2C42Cut (a i) (b i) with hA
  set U := D \ A with hU
  have hUo : IsOpen U := fl2C42_union_isOpen hD ha hb S
  have hUj : ∀ j ∈ S, U ⊆ D \ fl2C42Cut (a j) (b j) := fun j hj z hz =>
    ⟨hz.1, fun hc => hz.2 (mem_biUnion hj hc)⟩
  set f : ℂ → ℝ := fun z => ∑ j ∈ S, h j z - M * v z with hf
  set E : Finset ℂ := S.image (fun i => (a i : ℂ)) ∪ S.image (fun i => (b i : ℂ)) with hE
  have hharm : InnerProductSpace.HarmonicOnNhd f U := by
    intro z hz
    have h1 := fl2C42_harm_sum S h (fun j hj => (hh j).harm z (hUj j hj hz))
    have h2 : InnerProductSpace.HarmonicAt (M • v) z := (hv.harm z hz).const_smul
    have e : f = (fun z => ∑ j ∈ S, h j z) - M • v := by
      funext y; simp [hf]
    rw [e]
    exact h1.sub h2
  have hsum_le : ∀ z ∈ U, f z ≤ ∑ j ∈ S, h j z := by
    intro z hz
    have := mul_nonneg hM0 (hv.mem01 z hz).1
    simp only [hf]; linarith
  have hbdd : BddAbove (f '' U) := by
    refine ⟨(S.card : ℝ), ?_⟩
    rintro _ ⟨z, hz, rfl⟩
    refine (hsum_le z hz).trans ?_
    calc ∑ j ∈ S, h j z ≤ ∑ _j ∈ S, (1 : ℝ) :=
          Finset.sum_le_sum fun j hj => ((hh j).mem01 z (hUj j hj hz)).2
      _ = S.card := by simp
  have hinf : ∀ ε > 0, ∃ R, ∀ y ∈ U, R ≤ ‖y‖ → f y ≤ ε := by
    intro ε hε
    have hT : Tendsto (fun z => ∑ j ∈ S, h j z) (Bornology.cobounded ℂ ⊓ 𝓟 U)
        (𝓝 (∑ _j ∈ S, (0 : ℝ))) :=
      tendsto_finsetSum S fun j hj => ((hh j).infty (fl2C42Cut_bdd _ _)).mono_left
        (inf_le_inf_left _ (principal_mono.2 (hUj j hj)))
    simp only [Finset.sum_const_zero] at hT
    have hev := eventually_inf_principal.1 ((tendsto_order.1 hT).2 ε hε)
    obtain ⟨R, -, hR⟩ := (Metric.hasBasis_cobounded_compl_closedBall (0 : ℂ)).eventually_iff.1 hev
    refine ⟨R + 1, fun y hy hyR => ?_⟩
    have h1 := hR (by
      simp only [mem_compl_iff, mem_closedBall, dist_zero_right, not_le]; linarith) hy
    exact (hsum_le y hy).trans h1.le
  have hfr : ∀ x₀ ∈ frontier U, x₀ ∉ E → ∀ ε > 0, ∃ δ > 0, ∀ y ∈ U, dist y x₀ < δ →
      f y ≤ ε := by
    intro x₀ hx₀ hx₀E ε hε
    rw [hUo.frontier_eq] at hx₀
    obtain ⟨hx₀c, hx₀U⟩ := hx₀
    apply fl2C42_delta
    by_cases hx₀A : x₀ ∈ A
    · obtain ⟨i, hi, hxi⟩ := mem_iUnion₂.1 hx₀A
      obtain ⟨t, ht, rfl⟩ := hxi
      have hxD : ((t : ℝ) : ℂ) ∈ D := hsub i t ht
      have hWi := fl2C42Cut_isOpen hD (ha i) (hb i)
      have T1 : Tendsto (h i) (𝓝[U] (t : ℂ)) (𝓝 1) :=
        ((hh i).one _ ⟨t, ht, rfl⟩ (fl2C42_not_mem_closure_frontier hD hWi hxD)).mono_left
          (nhdsWithin_mono _ (hUj i hi))
      have T2 : Tendsto v (𝓝[U] (t : ℂ)) (𝓝 1) :=
        hv.one _ hx₀A (fl2C42_not_mem_closure_frontier hD hUo hxD)
      have T3 : Tendsto (fun z => ∑ j ∈ S.erase i, h j z) (𝓝[U] (t : ℂ))
          (𝓝 (∑ j ∈ S.erase i, h j t)) := by
        refine tendsto_finsetSum _ fun j hj => ?_
        obtain ⟨hji, -⟩ := Finset.mem_erase.1 hj
        have hxj : ((t : ℝ) : ℂ) ∈ D \ fl2C42Cut (a j) (b j) := by
          refine ⟨hxD, ?_⟩
          rintro ⟨s, hs, hst⟩
          have := Complex.ofReal_injective hst
          subst this
          exact Set.disjoint_left.1 (hdisj hji) hs ht
        exact ((hh j).harm _ hxj).1.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
      have T : Tendsto f (𝓝[U] (t : ℂ)) (𝓝 (1 + ∑ j ∈ S.erase i, h j t - M * 1)) := by
        have e : f = fun z => h i z + ∑ j ∈ S.erase i, h j z - M * v z := by
          funext z; simp only [hf]; rw [Finset.add_sum_erase S (fun j => h j z) hi]
        rw [e]
        exact (T1.add T3).sub (T2.const_mul M)
      exact (tendsto_order.1 T).2 ε (by have := hM i hi t ht; linarith)
    · have hx₀D : x₀ ∉ D := fun hD' => hx₀U ⟨hD', hx₀A⟩
      have T : Tendsto (fun z => ∑ j ∈ S, h j z) (𝓝[U] x₀) (𝓝 (∑ _j ∈ S, (0 : ℝ))) := by
        refine tendsto_finsetSum _ fun j hj => ?_
        have hWj := fl2C42Cut_isOpen hD (ha j) (hb j)
        have hfrj : x₀ ∈ frontier (D \ fl2C42Cut (a j) (b j)) := by
          rw [hWj.frontier_eq]
          exact ⟨closure_mono (hUj j hj) hx₀c, fun h' => hx₀D h'.1⟩
        have hncl : x₀ ∉ closure (fl2C42Cut (a j) (b j)) := by
          intro hc
          rcases fl2C42Cut_closure hc with h' | h' | h'
          · exact hx₀A (mem_biUnion hj h')
          · have haE : ((a j : ℝ) : ℂ) ∈ E := by
              rw [hE]; exact Finset.mem_union_left _ (Finset.mem_image_of_mem _ hj)
            exact hx₀E (by rw [h']; exact haE)
          · have hbE : ((b j : ℝ) : ℂ) ∈ E := by
              rw [hE]; exact Finset.mem_union_right _ (Finset.mem_image_of_mem _ hj)
            exact hx₀E (by rw [h']; exact hbE)
        exact ((hh j).zero x₀ hfrj hncl).mono_left (nhdsWithin_mono _ (hUj j hj))
      simp only [Finset.sum_const_zero] at T
      filter_upwards [(tendsto_order.1 T).2 ε hε, self_mem_nhdsWithin] with y hy hyU
      exact lt_of_le_of_lt (hsum_le y hyU) hy
  intro z hz
  have := fl2_harm_le_zero_off_finite E hUo hharm hbdd hfr hinf z hz
  simp only [hf] at this
  linarith

lemma fl2C42_mem_other {n : ℕ} {D : Set ℂ} {a b : Fin n → ℝ}
    (hsub : ∀ k, ∀ t ∈ Ioo (a k) (b k), (t : ℂ) ∈ D)
    (hdisj : Pairwise fun i j => Disjoint (Ioo (a i) (b i)) (Ioo (a j) (b j)))
    {i j : Fin n} (hij : i ≠ j) {t : ℝ} (ht : t ∈ Ioo (a i) (b i)) :
    (t : ℂ) ∈ D \ fl2C42Cut (a j) (b j) := by
  refine ⟨hsub i t ht, ?_⟩
  rintro ⟨s, hs, hst⟩
  have := Complex.ofReal_injective hst
  subst this
  exact Set.disjoint_left.1 (hdisj hij) ht hs

/-- **Field–Lawler, Corollary 4.2** (EJP 20 (2015), p. 11), analytic form on the real line, with
Prop 4.1 supplied as `hhalf` (`u k ≤ 1/2` on `I k`, `u k` the harmonic measure of the other
crosscuts): `∑_k h_k ≤ 2 w` on `D \ ⋃ I k`. -/
theorem fl2C42_main {n : ℕ} {D : Set ℂ} {a b : Fin n → ℝ} (hD : IsOpen D)
    (hsub : ∀ k, ∀ t ∈ Ioo (a k) (b k), (t : ℂ) ∈ D)
    (ha : ∀ k, (a k : ℂ) ∉ D) (hb : ∀ k, (b k : ℂ) ∉ D)
    (hdisj : Pairwise fun i j => Disjoint (Ioo (a i) (b i)) (Ioo (a j) (b j)))
    {h : Fin n → ℂ → ℝ}
    (hh : ∀ k, IsHarmMeas (D \ fl2C42Cut (a k) (b k)) (fl2C42Cut (a k) (b k)) (h k))
    {w : ℂ → ℝ}
    (hw : IsHarmMeas (D \ ⋃ k, fl2C42Cut (a k) (b k)) (⋃ k, fl2C42Cut (a k) (b k)) w)
    {u : Fin n → ℂ → ℝ}
    (hu : ∀ k, IsHarmMeas (D \ ⋃ (i) (_ : i ≠ k), fl2C42Cut (a i) (b i))
      (⋃ (i) (_ : i ≠ k), fl2C42Cut (a i) (b i)) (u k))
    (hhalf : ∀ k, ∀ t ∈ Ioo (a k) (b k), u k t ≤ 1 / 2) :
    ∀ z ∈ D \ ⋃ k, fl2C42Cut (a k) (b k), ∑ k, h k z ≤ 2 * w z := by
  have hnn : ∀ i j, i ≠ j → ∀ t ∈ Ioo (a i) (b i), 0 ≤ h j t ∧ h j t ≤ 1 := fun i j hij t ht =>
    (hh j).mem01 _ (fl2C42_mem_other hsub hdisj hij ht)
  set V : Set ℝ := {s | ∃ k, ∃ t ∈ Ioo (a k) (b k), s = 1 + ∑ j ∈ Finset.univ.erase k, h j t}
    with hV
  have hVbdd : BddAbove V := by
    refine ⟨1 + n, ?_⟩
    rintro _ ⟨k, t, ht, rfl⟩
    have h1 : ∑ j ∈ Finset.univ.erase k, h j t ≤ ∑ _j ∈ Finset.univ.erase k, (1 : ℝ) :=
      Finset.sum_le_sum fun j hj => (hnn k j (Finset.ne_of_mem_erase hj).symm t ht).2
    have h2 : ∑ _j ∈ Finset.univ.erase k, (1 : ℝ) ≤ ∑ _j ∈ (Finset.univ : Finset (Fin n)), 1 :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.erase_subset _ _) (fun _ _ _ => zero_le_one)
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one]
      at h1 h2
    linarith
  set M := sSup V with hMdef
  have hM0 : 0 ≤ M := Real.sSup_nonneg fun s hs => by
    obtain ⟨k, t, ht, rfl⟩ := hs
    have := Finset.sum_nonneg fun j (hj : j ∈ Finset.univ.erase k) =>
      (hnn k j (Finset.ne_of_mem_erase hj).symm t ht).1
    linarith
  have hle : ∀ s ∈ V, s ≤ 1 + M / 2 := by
    rintro _ ⟨k, t, ht, rfl⟩
    have eU : (⋃ i ∈ Finset.univ.erase k, fl2C42Cut (a i) (b i)) =
        ⋃ (i) (_ : i ≠ k), fl2C42Cut (a i) (b i) := by
      ext z; simp [Finset.mem_erase]
    have hMk : ∀ i ∈ Finset.univ.erase k, ∀ t' ∈ Ioo (a i) (b i),
        1 + ∑ j ∈ (Finset.univ.erase k).erase i, h j t' ≤ M := by
      intro i _ t' ht'
      have h1 := le_csSup hVbdd ⟨i, t', ht', rfl⟩
      have h2 : ∑ j ∈ (Finset.univ.erase k).erase i, h j t' ≤ ∑ j ∈ Finset.univ.erase i, h j t' :=
        Finset.sum_le_sum_of_subset_of_nonneg
          (Finset.erase_subset_erase i (Finset.erase_subset k _))
          (fun j hj _ => (hnn i j (Finset.ne_of_mem_erase hj).symm t' ht').1)
      linarith
    have htU : (t : ℂ) ∈ D \ ⋃ i ∈ Finset.univ.erase k, fl2C42Cut (a i) (b i) := by
      refine ⟨hsub k t ht, fun hc => ?_⟩
      obtain ⟨i, hi, hc⟩ := mem_iUnion₂.1 hc
      exact (fl2C42_mem_other hsub hdisj (Finset.ne_of_mem_erase hi).symm ht).2 hc
    have hdom := fl2C42_dom hD hsub ha hb hdisj hh (Finset.univ.erase k) (v := u k)
      (by rw [eU]; exact hu k) hM0 hMk t htU
    have := mul_le_mul_of_nonneg_left (hhalf k t ht) hM0
    linarith
  have hM2 : M ≤ 2 := by
    rcases V.eq_empty_or_nonempty with hVe | hVne
    · rw [hMdef, hVe, Real.sSup_empty]; norm_num
    · have := csSup_le hVne hle
      linarith
  have eW : (⋃ i ∈ (Finset.univ : Finset (Fin n)), fl2C42Cut (a i) (b i)) =
      ⋃ k, fl2C42Cut (a k) (b k) := by
    ext z; simp
  intro z hz
  exact fl2C42_dom hD hsub ha hb hdisj hh Finset.univ (v := w) (by rw [eW]; exact hw)
    (M := 2) (by norm_num)
    (fun i _ t ht => by have := hle _ ⟨i, t, ht, rfl⟩; linarith) z (by rw [eW]; exact hz)

end FieldLawler
end QuantumZipper
