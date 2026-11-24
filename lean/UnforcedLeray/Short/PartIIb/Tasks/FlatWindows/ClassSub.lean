import UnforcedLeray.Short.PartIIb.Sub.PartIIb_T13

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.IIb

open MeasureTheory

theorem flatCls_inHr_sub {c r : ℝ} {b b' : CProf} (h : InHr c r b) (h' : InHr c r b') :
    InHr c r (b - b') := by
  refine ⟨?_, h.meas.sub h'.meas, ?_⟩
  · filter_upwards [h.periodic, h'.periodic] with x hx hx'
    simp only [Pi.sub_apply]
    rw [hx, hx']
  · have hle := eLpNorm_sub_le' h.meas h'.meas (ENNReal.ofReal r)
    exact lt_of_le_of_lt hle
      (ENNReal.mul_lt_top (ENNReal.LpAddConst_lt_top _)
        (ENNReal.add_lt_top.2 ⟨h.finite, h'.finite⟩))

theorem flatCls_hasWeakFO_sub {v : Coord → Fin 3 → ℝ} {d : Coord → ℝ} {u u' g g' : Coord → ℂ}
    (h : HasWeakFO v d u g) (h' : HasWeakFO v d u' g') :
    HasWeakFO v d (fun x => u x - u' x) (fun x => g x - g' x) := by
  refine ⟨fun φ hφ => ⟨?_, ?_⟩, fun φ hφ => ?_⟩
  · simp only [sub_mul]
    exact (h.1 φ hφ).1.sub (h'.1 φ hφ).1
  · simp only [sub_mul] at *
    exact (h.1 φ hφ).2.sub (h'.1 φ hφ).2
  · dsimp only
    have e : (fun x => (g x - g' x) * (φ x : ℂ))
        = fun x => g x * (φ x : ℂ) - g' x * (φ x : ℂ) := by
      funext x
      ring
    have e' : (fun x => (u x - u' x) * (coordTranspose v d φ x : ℂ))
        = fun x => u x * (coordTranspose v d φ x : ℂ) - u' x * (coordTranspose v d φ x : ℂ) := by
      funext x
      ring
    rw [e, e', integral_sub (h.1 φ hφ).2 (h'.1 φ hφ).2,
      integral_sub (h.1 φ hφ).1 (h'.1 φ hφ).1, h.2 φ hφ, h'.2 φ hφ]

theorem flatCls_hasWeakVec_sub {v : Coord → Fin 3 → ℝ} {d : Coord → ℝ} {b b' g g' : CProf}
    (h : HasWeakVec v d b g) (h' : HasWeakVec v d b' g') :
    HasWeakVec v d (b - b') (g - g') := by
  intro i
  show HasWeakFO v d (fun x => (b - b') x i) (fun x => (g - g') x i)
  simp only [Pi.sub_apply, PiLp.sub_apply]
  exact flatCls_hasWeakFO_sub (h i) (h' i)

theorem flatCls_sqrtS_sub (b b' : CProf) : sqrtS (b - b') = sqrtS b - sqrtS b' := by
  funext x
  simp only [sqrtS, Pi.sub_apply, smul_sub]

theorem flatClassSub : FlatClassSub := by
  intro c r b b' hb hb'
  obtain ⟨Sb, Qb, Eb, hS, hQ, hE, hSi, hQi, hEi⟩ := hb.deriv
  obtain ⟨Sb', Qb', Eb', hS', hQ', hE', hSi', hQi', hEi'⟩ := hb'.deriv
  refine ⟨flatCls_inHr_sub hb.inHr hb'.inHr, Sb - Sb', Qb - Qb', Eb - Eb',
    flatCls_hasWeakVec_sub hS hS', flatCls_hasWeakVec_sub hQ hQ',
    flatCls_hasWeakVec_sub hE hE', flatCls_inHr_sub hSi hSi', ?_, ?_⟩
  · rw [flatCls_sqrtS_sub]
    exact flatCls_inHr_sub hQi hQi'
  · rw [flatCls_sqrtS_sub]
    exact flatCls_inHr_sub hEi hEi'

end UnforcedLeray.Short.IIb

end
