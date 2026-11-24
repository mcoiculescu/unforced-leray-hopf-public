import UnforcedLeray.Short.PartIIb.Sub.PartIIb_T09_4_2
import UnforcedLeray.Short.PartIIb.Tasks.NvCNorm.PeriodicRepresentative

/-!
# Part II-b, task `PartII-b:T09/4/2/2` (`GDivPeriodicRep`)

Source of record: `the November 2 reference manuscript`, lines 1639-1668, 1912-1916.

Measurable everywhere `c`-periodic representative of `gDiv = s (Q_ε b_r + ... )` off a periodic null
set, assembled from `periodicRepresentative` applied to `b`, `√s Q_ε b` and `√s ∂_η b`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal

namespace UnforcedLeray.Short.IIb

theorem gDivPeriodicRep : UnforcedLeray.Short.IIb.GDivPeriodicRep := by
  intro c ε r b Qb Eb hc hε hr hd
  obtain ⟨b', M1, hb'm, hb'per, hM1m, hM10, hM1per, hb'eq⟩ :=
    periodicRepresentative c r hc b hd.inHr.periodic hd.inHr.meas
  obtain ⟨Q', M2, hQ'm, hQ'per, hM2m, hM20, hM2per, hQ'eq⟩ :=
    periodicRepresentative c r hc (sqrtS Qb) hd.inQ.periodic hd.inQ.meas
  obtain ⟨E', M3, hE'm, hE'per, hM3m, hM30, hM3per, hE'eq⟩ :=
    periodicRepresentative c r hc (sqrtS Eb) hd.inE.periodic hd.inE.meas
  have hev : ∀ (f : Coord → CMerid) (i : Fin 2), Measurable f → Measurable fun x => f x i :=
    fun f i hf => (PiLp.continuous_apply 2 (fun _ : Fin 2 => ℂ) i).measurable.comp hf
  refine ⟨fun x => ((Real.sqrt x.1 : ℝ) : ℂ) * Q' x 0 + ((x.1 : ℝ) : ℂ) * ((ε : ℂ) * b' x 0)
    + ((Real.sqrt x.1 : ℝ) : ℂ) * E' x 1, M1 ∪ M2 ∪ M3, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · have hs : Measurable fun x : Coord => ((Real.sqrt x.1 : ℝ) : ℂ) :=
      Complex.measurable_ofReal.comp measurable_fst.sqrt
    have hsR : Measurable fun x : Coord => ((x.1 : ℝ) : ℂ) :=
      Complex.measurable_ofReal.comp measurable_fst
    exact ((hs.mul (hev Q' 0 hQ'm)).add
      (hsR.mul (measurable_const.mul (hev b' 0 hb'm)))).add (hs.mul (hev E' 1 hE'm))
  · intro s ξ η
    simp only [hQ'per s ξ η, hb'per s ξ η, hE'per s ξ η]
  · exact (hM1m.union hM2m).union hM3m
  · exact measure_union_null (measure_union_null hM10 hM20) hM30
  · intro s ξ η
    simp only [Set.mem_union, hM1per s ξ η, hM2per s ξ η, hM3per s ξ η]
  · intro x hx hxM
    have h1 : x ∉ M1 := fun h => hxM (Or.inl (Or.inl h))
    have h2 : x ∉ M2 := fun h => hxM (Or.inl (Or.inr h))
    have h3 : x ∉ M3 := fun h => hxM (Or.inr h)
    have hsq : ((Real.sqrt x.1 : ℝ) : ℂ) * ((Real.sqrt x.1 : ℝ) : ℂ) = ((x.1 : ℝ) : ℂ) := by
      rw [← Complex.ofReal_mul, Real.mul_self_sqrt hx.le]
    dsimp only
    rw [← hb'eq x hx h1, ← hQ'eq x hx h2, ← hE'eq x hx h3]
    simp only [gDiv, sqrtS, PiLp.smul_apply, smul_eq_mul]
    linear_combination (-(Qb x 0 + Eb x 1)) * hsq

end UnforcedLeray.Short.IIb
