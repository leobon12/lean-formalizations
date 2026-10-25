import SupercriticalLQGUniqueness.B2.Iface.Statements

 







set_option autoImplicit false
noncomputable section

namespace SupercriticalLQGUniqueness.B2.Polylog

 



def LFPPNormalizerExists : Prop :=
  ∀ ξ ε : Set.Ioi (0 : ℝ), ∃ a : Set.Ioi (0 : ℝ), IsLFPPNormalizer ξ ε a

 
theorem lfppNormalizerExists_of_existsUnique
    (h : ∀ ξ ε : Set.Ioi (0 : ℝ), ∃! a : Set.Ioi (0 : ℝ), IsLFPPNormalizer ξ ε a) :
    LFPPNormalizerExists :=
  fun ξ ε => (h ξ ε).exists

end SupercriticalLQGUniqueness.B2.Polylog
