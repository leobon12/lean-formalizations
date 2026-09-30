import QuantumZipper.Proofs.Zipper.FLTopSepBasic
import QuantumZipper.Proofs.Thm18.JordanChord

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# FL-TOPSEP: a point of `D ∩ B(0, ε)` is cut off by one arc of `D ∩ C_ε`

`flTopSep_holds : FLTopSepStmt`. Here `D = ℍ \ γ(0, t]` for a simple curve `γ = trace W` from
`0` into `ℍ`, and `‖x‖ < ε`, `x ∈ D`.

**Source.** The separation of a simply connected domain by a crosscut (Pommerenke, *Boundary
Behaviour of Conformal Maps*, Springer 1992, Prop. 2.12, p. 29), used by Field–Lawler, *Escape
probability and transience for SLE*, EJP 20 (2015), proof of Prop. 3.4, p. 9 ("the `ηⱼ` are
crosscuts of `D`"). Pommerenke's proof is by the Jordan curve theorem; the choice of the arc is
left implicit by Field–Lawler. We follow the standard index/logarithm route instead, via
Eilenberg's criterion (Burckel, *Classical Analysis in the Complex Plane*, Exercise 4.37(i),
p. 215; `CA.Topo.hasLogOn_of_not_separates`), exactly as in `JordanChord.chordSides_disjoint`.
The selection of the arc and the index bookkeeping are an **own elementary argument**
(recorded for `DEVIATIONS.md` in the task report).

**Proof.** Put `E = [-ε, ε] ∪ γ[0, t]` (compact, connected, `E ∩ D = ∅`), `p s = ε e^{2πis}`.
1. `z - x` has a continuous logarithm `ΛE` on `E` (on the arc `γ[0,t]`: `hasLogOn_of_arc`; on the
   segment: principal branch, `Im (z - x) < 0`; glued at `0`), and `Lc` along the circle
   (`flts_circle_lift`, increment `2πi` over `[0,1]`).
2. On `T = {s ∈ [0, 1/2] : p s ∈ E}` (compact), `h s = ΛE (p s) - Lc s ∈ 2πiℤ` is continuous,
   hence locally constant, and `h 0 - h (1/2) = 2πi` (on the lower half circle `Lc` is the
   principal branch up to a constant).
3. `α = sup {s ∈ T : h s = h 0}`, `β = inf {s ∈ T : s ≥ α, h s ≠ h 0}`: `α < β`, `h α ≠ h β` and
   `(α, β) ∩ T = ∅`, so `A = p (α, β)` is a maximal arc of `D ∩ C_ε`.
4. If the component `S` of `x` in `D \ A` were unbounded, `x` and a far point `b ∈ S` would lie
   in one component of `ℂ \ X`, `X = E ∪ p [α, β]`, so `z - x` would have a continuous logarithm
   `Λ` on `X` (Eilenberg + `flts_hasLog_of_far`). Then `Λ - ΛE` is constant on `E` and
   `Λ ∘ p - Lc` is constant on `[α, β]`, which forces `h α = h β`.
-/

noncomputable section

open Set Metric Complex
open scoped Real

namespace QuantumZipper
namespace FieldLawler

open QuantumZipper.CA.Topo Thm18Asm.LWFar

/-- **FL-TOPSEP.** Every point `x` of `D = ℍ \ γ(0, t]` with `|x| < ε` lies in a bounded
component of `D \ A` for a maximal arc `A` of `D ∩ C_ε`. -/
theorem flTopSep_holds : FLTopSepStmt := by
  classical
  intro W _hW _hW0 t R ε ht hR hε _hεR h0 hcont hinj hH hhull _hlt hRt x hx hxε
  have htpos : 0 < t := by
    rcases ht.lt_or_eq with h | h
    · exact h
    · subst h; rw [h0, norm_zero] at hRt; linarith
  have hxH : 0 < x.im := hx.1
  have hxK : x ∉ fwdHull W t := hx.2
  -- the boundary set `E`
  set seg : Set ℂ := ((↑) : ℝ → ℂ) '' Icc (-ε) ε with hseg
  set Γ : Set ℂ := trace W '' Icc 0 t with hΓ
  set E : Set ℂ := seg ∪ Γ with hE
  have hxΓ : x ∉ Γ := by
    rintro ⟨s, hs, hsx⟩
    rcases hs.1.eq_or_lt with h | h
    · rw [← h, h0] at hsx; rw [← hsx] at hxH; simp at hxH
    · exact hxK (hhull ▸ ⟨s, ⟨h, hs.2⟩, hsx⟩)
  have hED : ∀ z ∈ E, z ∉ H \ fwdHull W t := by
    rintro z (⟨u, -, rfl⟩ | ⟨s, hs, rfl⟩) ⟨hzH, hzK⟩
    · have : (0 : ℝ) < ((u : ℂ)).im := hzH
      simp at this
    · rcases hs.1.eq_or_lt with h | h
      · have : (0 : ℝ) < (trace W s).im := hzH
        rw [← h, h0] at this; simp at this
      · exact hzK (hhull ▸ ⟨s, ⟨h, hs.2⟩, rfl⟩)
  have hΓcpt : IsCompact Γ := isCompact_Icc.image_of_continuousOn hcont
  have hsegcpt : IsCompact seg := isCompact_Icc.image continuous_ofReal
  have hEcl : IsClosed E := (hsegcpt.union hΓcpt).isClosed
  have h0Γ : (0 : ℂ) ∈ Γ := ⟨0, ⟨le_rfl, ht⟩, h0⟩
  have hEpre : IsPreconnected E :=
    (isPreconnected_Icc.image _ continuous_ofReal.continuousOn).union 0
      ⟨0, ⟨by linarith, by linarith⟩, by simp⟩ h0Γ (isPreconnected_Icc.image _ hcont)
  -- a logarithm of `z - x` on the arc `Γ`
  have hmaps : MapsTo (fun u : ℝ => t * u) (Icc 0 1) (Icc 0 t) := fun u hu =>
    ⟨mul_nonneg ht hu.1, mul_le_of_le_one_right ht hu.2⟩
  have himage : (fun u : ℝ => trace W (t * u)) '' Icc 0 1 = Γ := by
    rw [show (fun u : ℝ => trace W (t * u)) = trace W ∘ (fun u => t * u) from rfl, image_comp,
      image_mul_left_Icc ht zero_le_one]
    simp [hΓ]
  obtain ⟨Λ₀, hΛ₀c, hΛ₀e⟩ := hasLogOn_of_arc (γ := fun u : ℝ => trace W (t * u))
    (hcont.comp (continuous_const.mul continuous_id).continuousOn hmaps)
    (fun u hu v hv huv => mul_left_cancel₀ htpos.ne' (hinj (hmaps hu) (hmaps hv) huv))
    (g := fun z => z - x) (continuousOn_id.sub continuousOn_const)
    (fun z hz h => hxΓ (by rw [← himage]; rwa [← sub_eq_zero.1 h]))
  rw [himage] at hΛ₀c hΛ₀e
  have hx0 : -x ≠ 0 := by
    intro h; rw [neg_eq_zero.1 h] at hxH; simp at hxH
  set Λγ : ℂ → ℂ := fun z => Λ₀ z - Λ₀ 0 + log (-x) with hΛγ
  have hΛγc : ContinuousOn Λγ Γ := (hΛ₀c.sub continuousOn_const).add continuousOn_const
  have hΛγe : ∀ z ∈ Γ, exp (Λγ z) = z - x := by
    intro z hz
    simp only [hΛγ]
    rw [exp_add, exp_sub, hΛ₀e z hz, hΛ₀e 0 h0Γ, exp_log hx0]
    simp only [zero_sub]
    exact div_mul_cancel₀ _ hx0
  -- the glued logarithm on `E`
  set ΛE : ℂ → ℂ := fun z => if z ∈ Γ then Λγ z else log (z - x) with hΛE
  have hΛEseg : EqOn ΛE (fun z => log (z - x)) seg := by
    rintro z ⟨u, -, rfl⟩
    simp only [hΛE]
    split_ifs with h
    · obtain ⟨s, hs, hsu⟩ := h
      rcases hs.1.eq_or_lt with h' | h'
      · rw [← h', h0] at hsu
        rw [← hsu]; simp [hΛγ]
      · have := hH s ⟨h', hs.2⟩
        have h2 : (0 : ℝ) < (trace W s).im := this
        rw [hsu] at h2; simp at h2
    · rfl
  have hlogseg : ContinuousOn (fun z => log (z - x)) seg := by
    rintro z ⟨u, -, rfl⟩
    refine ((continuousAt_clog ?_).comp (f := fun w : ℂ => w - x)
      (by fun_prop)).continuousWithinAt
    refine mem_slitPlane_iff.2 (Or.inr ?_)
    simp; exact hxH.ne'
  have hΛEcont : ContinuousOn ΛE E :=
    ContinuousOn.union_of_isClosed (hlogseg.congr hΛEseg)
      (hΛγc.congr fun z hz => if_pos hz) hsegcpt.isClosed hΓcpt.isClosed
  have hΛEexp : ∀ z ∈ E, exp (ΛE z) = z - x := by
    rintro z (hz | hz)
    · rw [hΛEseg hz]
      refine exp_log ?_
      obtain ⟨u, -, rfl⟩ := hz
      intro h
      have := congrArg Complex.im h
      simp at this; linarith
    · simp only [hΛE, if_pos hz]; exact hΛγe z hz
  -- the circle
  obtain ⟨Lc, hLcc, hLce, hLc1⟩ := flts_circle_lift hε hxε
  set p : ℝ → ℂ := fun s => flCirc ε (2 * π * s) with hp
  have hpc : Continuous p := (flCirc_continuous ε).comp (continuous_const.mul continuous_id)
  have hpx : ∀ s, p s - x ≠ 0 := by
    intro s h
    have h' : p s = x := sub_eq_zero.1 h
    have := flCirc_norm hε (2 * π * s)
    rw [show flCirc ε (2 * π * s) = p s from rfl, h'] at this
    linarith
  have hp0 : p 0 = ε := by simp [hp, flCirc]
  have hp1 : p 1 = ε := by
    simp only [hp, flCirc, mul_one]
    push_cast
    rw [Complex.exp_two_pi_mul_I, mul_one]
  have hphalf : p (1 / 2) = -ε := by
    simp only [hp, flCirc, show (2 * π * (1 / 2) : ℝ) = π by ring]
    rw [Complex.exp_pi_mul_I]; ring
  -- lower half circle: `Lc` is the principal branch up to a constant
  have hlow : Lc 1 - log (p 1 - x) = Lc (1 / 2) - log (p (1 / 2) - x) := by
    refine flts_sub_const (S := Icc (1 / 2 : ℝ) 1) (g := fun s => log (p s - x)) isPreconnected_Icc hLcc.continuousOn
      (fun s hs => ?_) (fun s hs => ?_) ⟨by norm_num, le_rfl⟩ ⟨le_rfl, by norm_num⟩
    · refine ((continuousAt_clog ?_).comp (f := fun s : ℝ => p s - x)
        (by fun_prop)).continuousWithinAt
      refine mem_slitPlane_iff.2 (Or.inr ?_)
      have hsin : Real.sin (2 * π * s) ≤ 0 := by
        have e : Real.sin (2 * π * s) = - Real.sin (2 * π * s - π) := by
          rw [Real.sin_sub_pi]; ring
        rw [e, neg_nonpos]
        apply Real.sin_nonneg_of_nonneg_of_le_pi <;> nlinarith [Real.pi_pos, hs.1, hs.2]
      have him : (p s - x).im = ε * Real.sin (2 * π * s) - x.im := by
        simp only [sub_im, hp, flCirc_im]
      rw [him]
      nlinarith
    · rw [hLce s ⟨by linarith [hs.1], hs.2⟩, exp_log (hpx s)]
  -- the jump function `h` on `T`
  set T : Set ℝ := Icc 0 (1 / 2) ∩ p ⁻¹' E with hT
  have hTcl : IsClosed T := isClosed_Icc.inter (hEcl.preimage hpc)
  set h : ℝ → ℂ := fun s => ΛE (p s) - Lc s with hh
  have hhc : ContinuousOn h T :=
    (hΛEcont.comp hpc.continuousOn (fun s hs => hs.2)).sub hLcc.continuousOn
  have hhexp : ∀ s ∈ T, exp (h s) = 1 := by
    intro s hs
    simp only [hh]
    rw [exp_sub, hΛEexp _ hs.2, hLce s ⟨hs.1.1, by linarith [hs.1.2]⟩, div_self (hpx s)]
  have hsegE : ∀ u : ℝ, u ∈ Icc (-ε) ε → (u : ℂ) ∈ E := fun u hu => Or.inl ⟨u, hu, rfl⟩
  have h0T : (0 : ℝ) ∈ T :=
    ⟨⟨le_rfl, by norm_num⟩, by
      show p 0 ∈ E; rw [hp0]; exact hsegE ε ⟨by linarith, le_rfl⟩⟩
  have hhalfT : (1 / 2 : ℝ) ∈ T :=
    ⟨⟨by norm_num, le_rfl⟩, by
      show p (1 / 2) ∈ E; rw [hphalf, ← ofReal_neg]; exact hsegE (-ε) ⟨le_rfl, by linarith⟩⟩
  have hdiff : h 0 - h (1 / 2) = 2 * π * I := by
    simp only [hh]
    rw [hp0, hphalf, hΛEseg (⟨ε, ⟨by linarith, le_rfl⟩, rfl⟩ : (ε : ℂ) ∈ seg),
      show -(ε : ℂ) = ((-ε : ℝ) : ℂ) by push_cast; ring,
      hΛEseg (⟨-ε, ⟨le_rfl, by linarith⟩, rfl⟩ : ((-ε : ℝ) : ℂ) ∈ seg)]
    rw [hp1, hphalf] at hlow
    simp only
    push_cast
    linear_combination hLc1 - hlow
  have hne0 : h (1 / 2) ≠ h 0 := by
    intro e
    rw [e, sub_self] at hdiff
    exact two_pi_I_ne_zero' hdiff.symm
  have hgap : ∀ s ∈ T, h s ≠ h 0 → 2 * π ≤ ‖h s - h 0‖ := by
    intro s hs hne
    by_contra hlt
    push_neg at hlt
    apply hne
    refine JordanChord.eq_of_exp_eq_of_abs_im_sub_lt (by rw [hhexp s hs, hhexp 0 h0T]) ?_
    calc |(h s).im - (h 0).im| = |(h s - h 0).im| := congrArg abs (Complex.sub_im _ _).symm
      _ ≤ ‖h s - h 0‖ := abs_im_le_norm _
      _ < 2 * π := hlt
  -- the arc
  set Lset : Set ℝ := T ∩ h ⁻¹' {h 0} with hLset
  set Nset : Set ℝ := T ∩ h ⁻¹' {w | 2 * π ≤ ‖w - h 0‖} with hNset
  have hLcl : IsClosed Lset := hhc.preimage_isClosed_of_isClosed hTcl isClosed_singleton
  have hNcl : IsClosed Nset := hhc.preimage_isClosed_of_isClosed hTcl
    (isClosed_le continuous_const (continuous_id.sub continuous_const).norm)
  have hbdd : BddAbove Lset := ⟨1 / 2, fun s hs => hs.1.1.2⟩
  set a := sSup Lset with ha
  have hamem : a ∈ Lset := hLcl.csSup_mem ⟨0, h0T, rfl⟩ hbdd
  have ha0 : 0 ≤ a := le_csSup hbdd ⟨h0T, rfl⟩
  have hha : h a = h 0 := hamem.2
  set N' : Set ℝ := Nset ∩ Ici a with hN'
  have hN'cl : IsClosed N' := hNcl.inter isClosed_Ici
  have hbddb : BddBelow N' := ⟨a, fun s hs => hs.2⟩
  have hhalfN : (1 / 2 : ℝ) ∈ N' := ⟨⟨hhalfT, hgap _ hhalfT hne0⟩, hamem.1.1.2⟩
  set b := sInf N' with hb
  have hbmem : b ∈ N' := hN'cl.csInf_mem ⟨_, hhalfN⟩ hbddb
  have hhb : h b ≠ h 0 := by
    intro e
    have := hbmem.1.2
    simp only [mem_preimage, mem_setOf_eq, e, sub_self, norm_zero] at this
    linarith [Real.pi_pos]
  have hab : a < b := lt_of_le_of_ne hbmem.2 (fun e => hhb (e ▸ hha))
  have hbhalf : b ≤ 1 / 2 := hbmem.1.1.1.2
  have hgapT : ∀ s ∈ T, a < s → s < b → False := by
    intro s hs has hsb
    by_cases hs0 : h s = h 0
    · have := le_csSup hbdd ⟨hs, hs0⟩; linarith
    · have := csInf_le hbddb ⟨⟨hs, hgap s hs hs0⟩, le_of_lt has⟩; linarith
  have hpaE : p a ∈ E := hamem.1.2
  have hpbE : p b ∈ E := hbmem.1.1.2
  have h2pi : 0 < 2 * π := by positivity
  have hpθ : ∀ θ : ℝ, p (θ / (2 * π)) = flCirc ε θ := by
    intro θ; simp only [hp]; congr 1; field_simp
  refine ⟨2 * π * a, 2 * π * b, by nlinarith, by positivity, by nlinarith, ?_, ?_, ?_, ?_⟩
  · -- the open arc lies in `D`
    intro θ hθ
    have hs1 : a < θ / (2 * π) := by rw [lt_div_iff₀ h2pi]; linarith [hθ.1]
    have hs2 : θ / (2 * π) < b := by rw [div_lt_iff₀ h2pi]; linarith [hθ.2]
    refine ⟨?_, fun hK => ?_⟩
    · show 0 < (flCirc ε θ).im
      rw [flCirc_im]
      exact mul_pos hε (Real.sin_pos_of_pos_of_lt_pi (by nlinarith [hθ.1])
        (by nlinarith [hθ.2]))
    · rw [hhull] at hK
      obtain ⟨u, hu, hue⟩ := hK
      refine hgapT _ ⟨⟨by linarith, by linarith⟩, ?_⟩ hs1 hs2
      show p (θ / (2 * π)) ∈ E
      rw [hpθ]
      exact Or.inr ⟨u, ⟨hu.1.le, hu.2⟩, hue⟩
  · exact hED _ hpaE
  · exact hED _ hpbE
  · -- boundedness
    by_contra hunb
    set A : Set ℂ := flCirc ε '' Ioo (2 * π * a) (2 * π * b) with hA
    set X : Set ℂ := E ∪ p '' Icc a b with hX
    have hXcpt : IsCompact X := (hsegcpt.union hΓcpt).union (isCompact_Icc.image hpc)
    obtain ⟨r, hr⟩ := hXcpt.isBounded.subset_closedBall 0
    have hr' : X ⊆ closedBall 0 (max r 0) :=
      hr.trans (closedBall_subset_closedBall (le_max_left _ _))
    set S := connectedComponentIn ((H \ fwdHull W t) \ A) x with hS
    obtain ⟨z, hzS, hzr⟩ : ∃ z ∈ S, max r 0 < ‖z‖ := by
      by_contra hno
      push_neg at hno
      exact hunb ((isBounded_closedBall (x := (0 : ℂ)) (r := max r 0)).subset
        fun w hw => by simpa using hno w hw)
    have hxA : x ∉ A := by
      rintro ⟨θ, -, hθ⟩
      have := flCirc_norm hε θ
      rw [hθ] at this; linarith
    have hSX : S ⊆ Xᶜ := by
      intro w hw hwX
      have hwD := connectedComponentIn_subset _ _ hw
      rcases hwX with hwE | ⟨s, hs, rfl⟩
      · exact hED w hwE hwD.1
      · rcases hs.1.eq_or_lt with h1 | h1
        · rw [← h1] at hwD; exact hED _ hpaE hwD.1
        rcases hs.2.eq_or_lt with h2 | h2
        · rw [h2] at hwD; exact hED _ hpbE hwD.1
        exact hwD.2 (by rw [hA]; exact ⟨2 * π * s, ⟨by nlinarith, by nlinarith⟩, rfl⟩)
    have hzX : z ∈ connectedComponentIn Xᶜ x :=
      (isPreconnected_connectedComponentIn.subset_connectedComponentIn
        (mem_connectedComponentIn (show x ∈ (H \ fwdHull W t) \ A from ⟨hx, hxA⟩)) hSX) hzS
    obtain ⟨Λ, hΛc, hΛe⟩ := flts_hasLog_of_far (le_max_right _ _) hr' hzr
      (hasLogOn_of_not_separates hXcpt hzX)
    have e1 := flts_sub_const hEpre (hΛc.mono subset_union_left) hΛEcont
      (fun w hw => by rw [hΛe w (Or.inl hw), hΛEexp w hw]) hpaE hpbE
    have e2 := flts_sub_const (S := Icc a b) (f := fun s => Λ (p s)) (g := Lc)
      isPreconnected_Icc (hΛc.comp hpc.continuousOn (fun s hs => Or.inr ⟨s, hs, rfl⟩))
      hLcc.continuousOn
      (fun s hs => by
        rw [hΛe _ (Or.inr ⟨s, hs, rfl⟩), hLce s ⟨by linarith [hs.1], by linarith [hs.2]⟩])
      (left_mem_Icc.2 hab.le) (right_mem_Icc.2 hab.le)
    apply hhb
    rw [← hha]
    simp only [hh]
    linear_combination e1 - e2

end FieldLawler
end QuantumZipper
