import SupercriticalLQGUniqueness.B2.Iface.Statements
import SupercriticalLQGUniqueness.B2.WeakStrong.Main
import SupercriticalLQGUniqueness.B2.LscTop.Metrizable

 



namespace SupercriticalLQGUniqueness.B2.Final

theorem iface_weakToStrong_proved : B2.Iface.WeakToStrong :=
  SupercriticalLQGUniqueness.B2.WeakStrong.isStrongLQGMetric_of_isWeakLQGMetric

theorem iface_lscTop_proved : B2.Iface.LscTop :=
  SupercriticalLQGUniqueness.B2.LscTop.iface_lscTop

end SupercriticalLQGUniqueness.B2.Final
