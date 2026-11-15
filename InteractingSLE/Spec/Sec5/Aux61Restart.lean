import InteractingSLE.Spec.Sec5.Aux61RestartBoundary
import InteractingSLE.Spec.Sec5.Aux61RestartMeasTarget
import InteractingSLE.Spec.Sec5.Aux61RestartNested

/-!
# Deterministic restart-chart infrastructure for Aux. lemma 61

Packet PROVE-AUX61-R1, with ruling R71's original-target setup. Main results:

* `Aux61Restart.exists_driver_of_compact_slit`: finite simple-slit driver,
  without an unbounded-continuation hypothesis;
* `Aux61Restart.exists_restart_driver_of_nested_hulls`: the original own-time
  restart, with its current access read through the own inverse-chart collar;
* `Aux61Restart.exists_restart_targetChart`: the entire retained component's
  chart, normalized at specified current-access and original-target prime ends;
* `Aux61Restart.exists_measurable_restart_discPair`: measurable charts of the
  history-selected component;
* `Aux61Restart.exists_measurable_restart_targetChart_of_approaches`: measurable
  marked charts, conditional on the two recorded prime-end approach sequences.

The last theorem's approach hypothesis still needs to be instantiated for the
specific stopped records in Proposition 5.1. No field kernel, Cameron–Martin
comparison, or eastern-endpoint exclusion is claimed by this module.
-/
