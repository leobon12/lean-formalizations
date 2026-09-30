import QuantumZipper.Proofs.Complex.KernelChordR
import QuantumZipper.Proofs.Complex.KernelChordK
import QuantumZipper.Proofs.Complex.KernelChordRight

/-!
# KT2 (chord version of the Carathéodory kernel theorem), unconditional

The two geometric inputs `LeftReflection` (`leftReflection`, KernelChordR) and
`LeftDoubledKernel` (`leftDoubledKernel`, KernelChordK) discharge the hypotheses of
`chordKernelTheoremLeft_of`; the right-component version follows by reflection
(`chordKernelTheoremRight_of_left`).
-/

namespace QuantumZipper.CA.Kernel

/-- **KT2, left component.** -/
theorem chordKernelTheoremLeft : ChordKernelTheoremLeft :=
  chordKernelTheoremLeft_of leftReflection leftDoubledKernel

/-- **KT2, right component.** -/
theorem chordKernelTheoremRight : ChordKernelTheoremRight :=
  chordKernelTheoremRight_of_left chordKernelTheoremLeft

end QuantumZipper.CA.Kernel
