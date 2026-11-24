import UnforcedLeray.Short.PartIIb.Tasks.ProfileGraphPhys.ChartDrift.Lift
import UnforcedLeray.Short.PartIIb.Tasks.ProfileGraphPhys.ChartDrift.PairPt
import UnforcedLeray.Short.PartIIb.Tasks.ProfileGraphPhys.ChartDrift.PairRep
import UnforcedLeray.Short.PartIIb.Tasks.ProfileGraphPhys.ChartDrift.PhaseAvgC
import UnforcedLeray.Short.PartIIb.Tasks.ProfileGraphPhys.ChartDrift.PairUnfold
import UnforcedLeray.Short.PartIIb.Tasks.ProfileGraphPhys.ChartDrift.PerPeriodic
import UnforcedLeray.Short.PartIIb.Tasks.ProfileGraphPhys.ChartDrift.PerSmooth

/-!
# `PartII-b:T10/6/3/1/2` (`LiftPairing`): the pairing of the lifted test with `N_v b`

Source of record: `shorter-proof-2026-11-02.tex`, lines 1912-1915 and 1900-1906.
Composition: `pairRep_proof` gives the periodic representative `b'`; `pairPt_proof` identifies the
pointwise pairing with `pairG`; `phaseAvgC_proof` (with `R = ε⁻¹`, `2c/R = 2εc`) turns the phase
integral into `πR² ∫ pairG dm`; `pairUnfold_proof` evaluates that integral as `(ε²/π) ∫ b'_i φ`,
and `π R² (ε²/π) = 1`.
-/

set_option autoImplicit false

open Set MeasureTheory Filter Topology
open scoped ENNReal ContDiff

open UnforcedLeray UnforcedLeray.PhaseSpace UnforcedLeray.Cons.C03.Concrete
open UnforcedLeray.Short.IIb UnforcedLeray.Short.IIb.ChartLift

theorem liftPairing_proof : UnforcedLeray.Short.IIb.ChartLift.LiftPairing := by
  intro c ε r φ i hc hε hr hφ b hb
  obtain ⟨b', hb'Hr, hb'meas, hb'per, hpair, hint⟩ :=
    pairRep_proof c ε r φ i b hc hε hr hφ hb
  rw [hpair, hint]
  obtain ⟨hint_int, hunf⟩ :=
    pairUnfold_proof c ε r φ i b' hc hε hr hφ hb'Hr hb'meas hb'per
  have hG : Measurable (pairG c ε φ i b') := by
    unfold pairG
    have h1 : Measurable (fun x : Coord =>
        ((c * ε ^ 2 / Real.pi * x.1 ^ ((5 : ℝ) / 2) * perCoord c φ x : ℝ) : ℂ)) := by
      apply Complex.measurable_ofReal.comp
      exact (measurable_const.mul (measurable_fst.pow_const _)).mul
        (pu_perCoord_cont hc hφ).measurable
    have h2 : Measurable (fun x : Coord => b' x i) :=
      (EuclideanSpace.proj i : EuclideanSpace ℂ (Fin 2) →L[ℂ] ℂ).continuous.measurable.comp hb'meas
    exact h1.mul h2
  have hper : ∀ s q η, pairG c ε φ i b' (s, (q + c, η)) = pairG c ε φ i b' (s, (q, η)) := by
    intro s q η
    have h1 : perCoord c φ (s, (q + c, η)) = perCoord c φ (s, (q, η)) :=
      perPeriodic_proof c φ (s, (q, η))
    unfold pairG
    rw [h1, hb'per s q η]
  have hP : 2 * ε * c = 2 * c / ε⁻¹ := by
    rw [div_inv_eq_mul]
    ring
  have hA := phaseAvgC_proof ε⁻¹ c (pairG c ε φ i b') (inv_pos.mpr hε) hc hG hper hint_int
  have key : pairF (2 * ε * c) (liftTest c ε φ i) (NvC ε⁻¹ b') =
      phaseInt (2 * c / ε⁻¹) (fun p => pairG c ε φ i b' (UnforcedLeray.Axi.chart ε⁻¹ p.1 p.2)) := by
    rw [hP]
    unfold pairF
    congr 1
    funext p
    exact pairPt_proof c ε φ i b' p hε
  have hscalar : ((Real.pi * (ε⁻¹) ^ 2 : ℝ) : ℂ) * ((ε ^ 2 / Real.pi : ℝ) : ℂ) = 1 := by
    have hπ : Real.pi ≠ 0 := Real.pi_ne_zero
    have hε0 : ε ≠ 0 := hε.ne'
    have h : Real.pi * (ε⁻¹) ^ 2 * (ε ^ 2 / Real.pi) = 1 := by
      field_simp
    rw [← Complex.ofReal_mul, h, Complex.ofReal_one]
  rw [key, hA, hunf, ← mul_assoc, hscalar, one_mul]
