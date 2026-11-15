import InteractingSLE.Spec.Sec5.Aux61RestartBdryApply

/-!
# The window-to-restart-configuration bridge

Packet PROVE-AUX61-R1. Astra follow-up 4, Part (1), section 1.1; R71.

The consumer's `Aux61Kernel.IsTargetComp` uses a collar at some positive real
point. `isTargetComp_cfDrv0_iff_original_target` proves that, on a good hitting
history and an interior own prefix, this is precisely the physical target 1
used by the inherited chart. A uniformly free neighborhood of the compact
positive real interval between the two marks proves the identification.

`mem_restartConfigurationEvent_of_cfDrv_window` discharges the previously open
application inclusion for the consumer's actual `cfDrv` window. The source's
simple proper own trace and good hitting history imply all retained geometric
conditions. The earlier contact supplies nonemptiness of the counterflow hull,
its closedness gives positive tip distance, and the fresh interior excursion
gives the actual own inverse-chart approach in the physical target component.

`ae_all_windows_mem_restartConfigurationEvent` gives a single almost-sure event
for all positive rational original own times and all window codes.
`has_charted_clearance_cover_of_windows` covers those windows almost surely by
the retained measurable clearance pieces, with the full inherited chart on
each piece. Its ambient driver and observation hypotheses are exactly the
previous chart interface. Properness and good hitting are only almost-sure
source regularity inputs; no window-coverage premise remains.

No field kernel, conditional independence or per-fibre locality is asserted.
No post-contact kernel (R77) or Theorem 1.2/1.3 input (R48) is used.
-/
