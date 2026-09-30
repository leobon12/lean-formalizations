import QuantumZipper.Proofs.Zipper.FieldLawler3FinBasic

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# FL3-FIN: the slit half-disc minus finitely many arcs has finitely many components

Task FL3-FIN (Track A): the hypothesis `hfin` of `flExist_loewner` / `flExist_loewner_arcs`.
For `U = ((ℍ \ K) ∩ B(0, R)) \ ⋃ᵢ C_ε(αᵢ, βᵢ)` every component `C` has a frontier point `w` in
`ℍ \ K` (else `C` would be clopen in the connected set `ℍ \ K`, but `C` is bounded), and such `w`
lies on one of the removed open arcs or on `C_R ∩ ℍ` minus the tip `γ(t)`. Near `w`, `C` contains
a polar half-box on one side of the circle, and by `flFin_piece` all these half-boxes along one
piece and one side lie in one component. So there are at most `2n + 2` components.

Own elementary argument (FL, EJP 20 (2015), p. 9 use the finiteness implicitly); see
`FieldLawler3FinBasic.lean`.
-/

noncomputable section

open Set Filter Metric Complex
open scoped Topology

namespace QuantumZipper
namespace FieldLawler

open Thm18Asm.LWFar

lemma flFin_re (a b : ℝ) : ((a : ℂ) + (b : ℂ) * I).re = a := by simp
lemma flFin_im (a b : ℝ) : ((a : ℂ) + (b : ℂ) * I).im = b := by simp

lemma flFin_pol {r : ℝ} (hr : 0 < r) (θ : ℝ) :
    exp ((Real.log r : ℂ) + (θ : ℂ) * I) = (r : ℂ) * exp (θ * I) := by
  rw [Complex.exp_add, ← ofReal_exp, Real.exp_log hr]

lemma flFin_polar {R : ℝ} {v : ℂ} (hv : ‖v‖ = R) (hR : 0 < R) :
    exp ((Real.log R : ℂ) + (arg v : ℂ) * I) = v := by
  have hv0 : v ≠ 0 := fun h => by rw [h, norm_zero] at hv; linarith
  calc exp ((Real.log R : ℂ) + (arg v : ℂ) * I) = exp (Complex.log v) := by
        rw [← hv]; congr 1
    _ = v := Complex.exp_log hv0

lemma flFin_normQ {ρ s θ δ : ℝ} {y : ℂ} (hy : y ∈ flFinQ ρ s θ δ) :
    ∃ m ∈ Ioo 0 δ, ∃ θ' ∈ Ioo (θ - δ) (θ + δ),
      y = exp (((ρ + s * m : ℝ) : ℂ) + (θ' : ℂ) * I) ∧ ‖y‖ = Real.exp (ρ + s * m) := by
  obtain ⟨⟨m, θ'⟩, ⟨hm, hθ'⟩, rfl⟩ := hy
  exact ⟨m, hm, θ', hθ', rfl, flFin_norm _ _⟩

/-- **Finitely many components** (the hypothesis `hfin` of `flExist_loewner`). -/
theorem flFin_components {γ : ℝ → ℂ} {t R ε : ℝ} (ht : 0 ≤ t) (hε : 0 < ε) (hεR : ε < R)
    (hγc : ContinuousOn γ (Icc 0 t)) (hγ0 : γ 0 = 0) (hγH : ∀ s ∈ Ioc 0 t, γ s ∈ H)
    (hγR : ∀ s ∈ Ico 0 t, ‖γ s‖ < R) (hγt : ‖γ t‖ = R)
    (hpc : IsPreconnected (H \ γ '' Ioc 0 t))
    {ι : Type*} (I₀ : Finset ι) {α β : ι → ℝ}
    (hend : ∀ i ∈ I₀, (ε : ℂ) * exp (α i * I) ∈ γ '' Icc 0 t ∪ {z : ℂ | z.im ≤ 0} ∧
      (ε : ℂ) * exp (β i * I) ∈ γ '' Icc 0 t ∪ {z : ℂ | z.im ≤ 0})
    (harc : ∀ i ∈ I₀, flCircArc ε (α i) (β i) ⊆ H \ γ '' Ioc 0 t) :
    (connectedComponentIn (((H \ γ '' Ioc 0 t) ∩ ball 0 R) \
        ⋃ i ∈ I₀, flCircArc ε (α i) (β i)) ''
      (((H \ γ '' Ioc 0 t) ∩ ball 0 R) \ ⋃ i ∈ I₀, flCircArc ε (α i) (β i))).Finite := by
  set K := γ '' Ioc 0 t with hKdef
  set A := ⋃ i ∈ I₀, flCircArc ε (α i) (β i) with hAdef
  set U := ((H \ K) ∩ ball 0 R) \ A with hUdef
  set Kc := γ '' Icc 0 t with hKcdef
  have hR : 0 < R := by linarith
  have htpos : 0 < t := by
    rcases ht.eq_or_lt with h | h
    · subst h; rw [hγ0, norm_zero] at hγt; linarith
    · exact h
  have hKcc : IsClosed Kc := (isCompact_Icc.image_of_continuousOn hγc).isClosed
  have hKH : ∀ z ∈ Kc, z ∈ H → z ∈ K := by
    rintro _ ⟨s, hs, rfl⟩ hH
    rcases hs.1.eq_or_lt with h0 | hpos
    · subst h0; simp [H, hγ0] at hH
    · exact ⟨s, ⟨hpos, hs.2⟩, rfl⟩
  have hKsub : K ⊆ Kc := image_mono Ioc_subset_Icc_self
  have hKn : ∀ z ∈ Kc, ‖z‖ ≤ R := by
    rintro _ ⟨s, hs, rfl⟩
    rcases hs.2.eq_or_lt with h | h
    · rw [h, hγt]
    · exact (hγR s ⟨hs.1, h⟩).le
  have hnA : ∀ z ∈ A, ‖z‖ = ε := by
    intro z hz
    obtain ⟨i, -, θ, -, rfl⟩ := mem_iUnion₂.1 hz
    rw [norm_mul, Complex.norm_exp_ofReal_mul_I, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos hε, mul_one]
  have hmemU : ∀ y : ℂ, y ∈ H → y ∉ Kc → ‖y‖ < R → ‖y‖ ≠ ε → y ∈ U := fun y hH hK hR' hne =>
    ⟨⟨⟨hH, fun h => hK (hKsub h)⟩, by rwa [mem_ball, dist_zero_right]⟩, fun h => hne (hnA y h)⟩
  have hUb : ∀ y ∈ U, ‖y‖ < R := fun y hy => by
    have := hy.1.2; rwa [mem_ball, dist_zero_right] at this
  -- `U` is open
  set Cl := ⋃ i ∈ I₀, (fun θ : ℝ => (ε : ℂ) * exp (θ * I)) '' Icc (α i) (β i) with hCldef
  have hClc : IsClosed Cl := (I₀.finite_toSet.isCompact_biUnion fun i _ =>
    isCompact_Icc.image (by fun_prop)).isClosed
  have hL : ∀ w : ℂ, w ∈ {z : ℂ | z.im ≤ 0} → w ∉ H := by
    intro w hw hH'
    have h1 : w.im ≤ 0 := hw
    have h2 : (0 : ℝ) < w.im := hH'
    linarith
  have hUeq : U = (H ∩ ball 0 R) \ (Kc ∪ Cl) := by
    ext z
    simp only [hUdef, Set.mem_sdiff, mem_inter_iff, mem_union, not_or]
    constructor
    · rintro ⟨⟨⟨hH, hK⟩, hb⟩, hA'⟩
      refine ⟨⟨hH, hb⟩, fun hk => hK (hKH z hk hH), fun hc => ?_⟩
      obtain ⟨i, hi, θ, hθ, rfl⟩ := mem_iUnion₂.1 hc
      rcases hθ.1.eq_or_lt with h1 | h1
      · rw [← h1] at hH hK
        rcases (hend i hi).1 with h | h
        · exact hK (hKH _ h hH)
        · exact hL _ h hH
      rcases hθ.2.eq_or_lt with h2 | h2
      · rw [h2] at hH hK
        rcases (hend i hi).2 with h | h
        · exact hK (hKH _ h hH)
        · exact hL _ h hH
      exact hA' (mem_iUnion₂.2 ⟨i, hi, θ, ⟨h1, h2⟩, rfl⟩)
    · rintro ⟨⟨hH, hb⟩, hK, hC⟩
      refine ⟨⟨⟨hH, fun h => hK (hKsub h)⟩, hb⟩, fun h => hC ?_⟩
      obtain ⟨i, hi, hz⟩ := mem_iUnion₂.1 h
      exact mem_iUnion₂.2 ⟨i, hi, image_mono Ioo_subset_Icc_self hz⟩
  have hUo : IsOpen U := by
    rw [hUeq]; exact (isOpen_H.inter isOpen_ball).sdiff (hKcc.union hClc)
  -- local structure along the arcs
  have hArcLoc : ∀ i ∈ I₀, ∀ θ ∈ Ioo (α i) (β i), ∃ δ > 0,
      (∀ s : ℝ, (s = 1 ∨ s = -1) → flFinQ (Real.log ε) s θ δ ⊆ U) ∧
      ∀ θ' ∈ Ioo (θ - δ) (θ + δ), exp ((Real.log ε : ℂ) + (θ' : ℂ) * I) ∉ U := by
    intro i hi θ hθ
    have hp : (ε : ℂ) * exp (θ * I) ∈ H \ K := harc i hi ⟨θ, hθ, rfl⟩
    have hO : IsOpen ((H \ Kc) ∩ ball 0 R) := (isOpen_H.sdiff hKcc).inter isOpen_ball
    have hpO : exp ((Real.log ε : ℂ) + (θ : ℂ) * I) ∈ (H \ Kc) ∩ ball 0 R := by
      rw [flFin_pol hε θ]
      refine ⟨⟨hp.1, fun h => hp.2 (hKH _ h hp.1)⟩, ?_⟩
      rw [mem_ball, dist_zero_right, norm_mul, Complex.norm_exp_ofReal_mul_I, Complex.norm_real,
        Real.norm_eq_abs, abs_of_pos hε, mul_one]
      exact hεR
    obtain ⟨δ, hδ, hδη, hbox⟩ := flFin_local hO hpO (η := min (θ - α i) (β i - θ))
      (lt_min (by linarith [hθ.1]) (by linarith [hθ.2]))
    refine ⟨δ, hδ, fun s hs y hy => ?_, fun θ' hθ' hU => ?_⟩
    · obtain ⟨m, hm, θ', hθ', rfl, hn⟩ := flFin_normQ hy
      have hin := hbox (((Real.log ε + s * m : ℝ) : ℂ) + (θ' : ℂ) * I)
        (by rw [flFin_re]; rcases hs with rfl | rfl <;> constructor <;> linarith [hm.1, hm.2])
        (by rw [flFin_im]; exact hθ')
      refine hmemU _ hin.1.1 hin.1.2 (by have := hin.2; rwa [mem_ball, dist_zero_right] at this)
        ?_
      rw [hn]
      intro h
      have h2 : Real.log ε + s * m = Real.log ε := by
        apply Real.exp_injective; rw [h, Real.exp_log hε]
      rcases hs with rfl | rfl <;> linarith [hm.1]
    · rw [flFin_pol hε θ'] at hU
      refine hU.2 (mem_iUnion₂.2 ⟨i, hi, θ', ⟨?_, ?_⟩, rfl⟩)
      · linarith [hθ'.1, min_le_left (θ - α i) (β i - θ)]
      · linarith [hθ'.2, min_le_right (θ - α i) (β i - θ)]
  -- local structure along `C_R`
  have hRLoc : ∀ θ : ℝ, 0 < θ → θ < Real.pi → θ ≠ arg (γ t) →
      ∃ δ > 0, flFinQ (Real.log R) (-1) θ δ ⊆ U := by
    intro θ h0 hπ hne
    have hnp : ‖exp ((Real.log R : ℂ) + (θ : ℂ) * I)‖ = R := by
      rw [flFin_norm, Real.exp_log hR]
    have hpH : exp ((Real.log R : ℂ) + (θ : ℂ) * I) ∈ H := by
      show 0 < (exp ((Real.log R : ℂ) + (θ : ℂ) * I)).im
      rw [Complex.exp_im, flFin_re, flFin_im]
      exact mul_pos (Real.exp_pos _) (Real.sin_pos_of_pos_of_lt_pi h0 hπ)
    have hpK : exp ((Real.log R : ℂ) + (θ : ℂ) * I) ∉ Kc := by
      rintro ⟨s, hs, hsp⟩
      rcases hs.2.eq_or_lt with h | h
      · subst h
        apply hne
        rw [hsp, flFin_pol hR, Complex.exp_mul_I, arg_real_mul _ hR,
          arg_cos_add_sin_mul_I ⟨by linarith [Real.pi_pos], hπ.le⟩]
      · have := hγR s ⟨hs.1, h⟩
        rw [hsp, hnp] at this
        exact lt_irrefl _ this
    have hO : IsOpen ((H \ Kc) ∩ (closedBall (0 : ℂ) ε)ᶜ) :=
      (isOpen_H.sdiff hKcc).inter isClosed_closedBall.isOpen_compl
    have hpO : exp ((Real.log R : ℂ) + (θ : ℂ) * I) ∈ (H \ Kc) ∩ (closedBall (0 : ℂ) ε)ᶜ := by
      refine ⟨⟨hpH, hpK⟩, ?_⟩
      rw [mem_compl_iff, mem_closedBall, dist_zero_right, hnp]
      linarith
    obtain ⟨δ, hδ, -, hbox⟩ := flFin_local hO hpO one_pos
    refine ⟨δ, hδ, fun y hy => ?_⟩
    obtain ⟨m, hm, θ', hθ', rfl, hn⟩ := flFin_normQ hy
    have hin := hbox (((Real.log R + -1 * m : ℝ) : ℂ) + (θ' : ℂ) * I)
      (by rw [flFin_re]; constructor <;> linarith [hm.1, hm.2]) (by rw [flFin_im]; exact hθ')
    have hεy : ε < ‖exp (((Real.log R + -1 * m : ℝ) : ℂ) + (θ' : ℂ) * I)‖ := by
      have := hin.2
      rwa [mem_compl_iff, mem_closedBall, dist_zero_right, not_le] at this
    refine hmemU _ hin.1.1 hin.1.2 ?_ hεy.ne'
    rw [hn]
    have h3 : Real.exp (Real.log R + -1 * m) < Real.exp (Real.log R) :=
      Real.exp_lt_exp.2 (by linarith [hm.1])
    rwa [Real.exp_log hR] at h3
  -- the finite set of possible components
  have hγtH : γ t ∈ H := hγH t ⟨htpos, le_rfl⟩
  have harg0 : 0 ≤ arg (γ t) := Complex.arg_nonneg_iff.2 (le_of_lt hγtH)
  have hargπ : arg (γ t) ≤ Real.pi := Complex.arg_le_pi _
  have hfinS : ((⋃ i ∈ I₀, (flFinCs U (Real.log ε) 1 (Ioo (α i) (β i)) ∪
      flFinCs U (Real.log ε) (-1) (Ioo (α i) (β i)))) ∪
      (flFinCs U (Real.log R) (-1) (Ioo 0 (arg (γ t))) ∪
        flFinCs U (Real.log R) (-1) (Ioo (arg (γ t)) Real.pi))).Finite := by
    refine (I₀.finite_toSet.biUnion fun i hi =>
      ((flFin_piece isPreconnected_Ioo fun θ hθ => ?_).finite.union
        (flFin_piece isPreconnected_Ioo fun θ hθ => ?_).finite)).union
      ((flFin_piece isPreconnected_Ioo fun θ hθ => ?_).finite.union
        (flFin_piece isPreconnected_Ioo fun θ hθ => ?_).finite)
    · obtain ⟨δ, hδ, hQ, -⟩ := hArcLoc i hi θ hθ
      exact ⟨δ, hδ, hQ 1 (Or.inl rfl)⟩
    · obtain ⟨δ, hδ, hQ, -⟩ := hArcLoc i hi θ hθ
      exact ⟨δ, hδ, hQ (-1) (Or.inr rfl)⟩
    · exact hRLoc θ hθ.1 (by linarith [hθ.2]) hθ.2.ne
    · exact hRLoc θ (by linarith [hθ.1]) hθ.2 hθ.1.ne'
  refine hfinS.subset ?_
  rintro _ ⟨z, hz, rfl⟩
  set C := connectedComponentIn U z with hCdef
  have hCU : C ⊆ U := connectedComponentIn_subset _ _
  have hCo : IsOpen C := hUo.connectedComponentIn
  obtain ⟨w, hwcl, hwHK, hwC⟩ : ∃ w ∈ closure C, w ∈ H \ K ∧ w ∉ C := by
    by_contra hcon
    push Not at hcon
    have hsub := hpc.subset_of_closure_inter_subset hCo ⟨z, hz.1.1, mem_connectedComponentIn hz⟩
      (fun w hw => hcon w hw.1 hw.2)
    have hqn : ‖((R + 1 : ℝ) : ℂ) * I‖ = R + 1 := by
      rw [norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos (by linarith)]
    have hq : ((R + 1 : ℝ) : ℂ) * I ∈ H \ K := by
      refine ⟨show (0 : ℝ) < (((R + 1 : ℝ) : ℂ) * I).im by simp; linarith, fun h => ?_⟩
      have := hKn _ (hKsub h)
      linarith
    have := hUb _ (hCU (hsub hq))
    linarith
  have hwU : w ∉ U := fun h => hwC (flFin_closure_mem hz hwcl h)
  have hwR : ‖w‖ ≤ R := by
    have : closure C ⊆ closedBall 0 R := closure_minimal
      (fun y hy => mem_closedBall_zero_iff.2 (hUb y (hCU hy)).le) isClosed_closedBall
    exact mem_closedBall_zero_iff.1 (this hwcl)
  rcases hwR.lt_or_eq with hlt | heq
  · have hwA : w ∈ A := by
      by_contra h
      exact hwU ⟨⟨hwHK, by rwa [mem_ball, dist_zero_right]⟩, h⟩
    obtain ⟨i, hi, θ, hθ, hwe⟩ := mem_iUnion₂.1 hwA
    obtain ⟨δ, hδ, hQ, harcU⟩ := hArcLoc i hi θ hθ
    have hwcl' : exp ((Real.log ε : ℂ) + (θ : ℂ) * I) ∈ closure C := by
      have hwe' : (ε : ℂ) * exp (θ * I) = w := hwe
      rw [flFin_pol hε θ, hwe']; exact hwcl
    obtain ⟨x, hxre, hxim, hxC⟩ := flFin_step hwcl' hδ
    have hcomp : connectedComponentIn U (exp x) = C := (connectedComponentIn_eq hxC).symm
    rcases flFin_tri hxre hxim with h | h | h
    · exact mem_union_left _ (mem_iUnion₂.2 ⟨i, hi,
        Or.inr ⟨θ, hθ, δ, hδ, hQ (-1) (Or.inr rfl), exp x, h, hcomp⟩⟩)
    · exact mem_union_left _ (mem_iUnion₂.2 ⟨i, hi,
        Or.inl ⟨θ, hθ, δ, hδ, hQ 1 (Or.inl rfl), exp x, h, hcomp⟩⟩)
    · exact absurd (h ▸ hCU hxC) (harcU _ hxim)
  · have hwH : w ∈ H := hwHK.1
    have ha0 : 0 < arg w := lt_of_le_of_ne (Complex.arg_nonneg_iff.2 (le_of_lt hwH))
      (fun h => by
        have := (Complex.arg_eq_zero_iff.1 h.symm).2
        have h2 : (0 : ℝ) < w.im := hwH
        linarith)
    have haπ : arg w < Real.pi := Complex.arg_lt_pi_iff.2 (Or.inr (ne_of_gt hwH))
    have hne : arg w ≠ arg (γ t) := by
      intro h
      apply hwHK.2
      rw [← flFin_polar heq hR, h, flFin_polar hγt hR]
      exact ⟨t, ⟨htpos, le_rfl⟩, rfl⟩
    obtain ⟨δ, hδ, hQ⟩ := hRLoc (arg w) ha0 haπ hne
    have hwcl' : exp ((Real.log R : ℂ) + (arg w : ℂ) * I) ∈ closure C := by
      rw [flFin_polar heq hR]; exact hwcl
    obtain ⟨x, hxre, hxim, hxC⟩ := flFin_step hwcl' hδ
    have hcomp : connectedComponentIn U (exp x) = C := (connectedComponentIn_eq hxC).symm
    have hxR := hUb _ (hCU hxC)
    rcases flFin_tri hxre hxim with h | h | h
    · refine mem_union_right _ ?_
      rcases lt_or_gt_of_ne hne with hl | hg
      · exact Or.inl ⟨arg w, ⟨ha0, hl⟩, δ, hδ, hQ, exp x, h, hcomp⟩
      · exact Or.inr ⟨arg w, ⟨hg, haπ⟩, δ, hδ, hQ, exp x, h, hcomp⟩
    · exfalso
      obtain ⟨m, hm, -, -, -, hn⟩ := flFin_normQ h
      rw [hn] at hxR
      have h3 : Real.exp (Real.log R) < Real.exp (Real.log R + 1 * m) :=
        Real.exp_lt_exp.2 (by linarith [hm.1])
      rw [Real.exp_log hR] at h3
      linarith
    · exfalso
      rw [h, flFin_norm, Real.exp_log hR] at hxR
      exact lt_irrefl _ hxR

end FieldLawler
end QuantumZipper
