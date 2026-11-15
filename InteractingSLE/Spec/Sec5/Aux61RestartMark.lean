import InteractingSLE.Spec.Sec5.Aux61RestartMarkIncident

/-!
# Original-target restart charts for the actual counterflow histories

Packet PROVE-AUX61-R1, continuation of the geometric construction.

* `ae_actual_history_original_mark_alive`: the actual counterflow's seed
  force at zero protects the real mark -1, simultaneously at all finite stops.
* `cfGlueAE_original_target_protected`: protection of the physical target 1
  in Q holds on the actual glued space, by its Borel good-hitting certificate.
* `has_original_target_restart_chart_of_goodHit`: construct the measurable
  chart, canonical hull record and literal inherited phase on these histories.
* `has_original_target_restart_chart_of_fresh_segment`: a fresh segment in
  the original right-target component supplies current-access incidence.

The source restricts to the event that the current access lies in the
original right-target component (Astra follow-up 4, Part (1), §1.1). The
incidence or fresh-segment premise specifies this event. It is not asserted
for every retained pair of histories. Neither the selector nor the chart
uses a next forward point to choose its domain. These modules make no claim
about the conditional field kernel or the corrected fibre-cover theorem.
-/
