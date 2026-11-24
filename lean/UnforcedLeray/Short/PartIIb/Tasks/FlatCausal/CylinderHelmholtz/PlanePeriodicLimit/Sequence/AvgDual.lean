import UnforcedLeray.Short.PartIIb.Sub.PartIIb_T12_1_4_1
import UnforcedLeray.Short.PartIIb.Tasks.FlatCausal.CylinderHelmholtz.HelmholtzUnique.MollApprox.CylLocInt.Cover

/-!
# Part II-b, task `PartII-b:T12/1/4/1/5` (`PPLAvgDual`): moving the translates onto the test

Source of record: `the November 2 reference manuscript` lines 1933-1935.

For `F_N = ppCut c N F`, `G` the planar Helmholtz companion of `F_N` and `Ψ` a planar solenoidal
test, the identity `∫ (F - H_N)·Ψ = ∫ F·Ψ - ∫ F_N·ppDual Ψ` with `H_N = ppAvg c N G`:
each translate `∫ G(· + jc e_q)·Ψ = ∫ G·Ψ(· - jc e_q)` (translation invariance), the test
`Ψ(· - jc e_q)` is again a planar solenoidal test, and `∫ (F_N - G)·Ψ(· - jc e_q) = 0`
by `IsPlaneHelmholtz`; summing over `j` gives `∫ H_N·Ψ = ∫ F_N·ppDual Ψ`.
Local integrability of `F` on balls comes from `CylLocIntCover.integrableOn_closedBall_of_cell`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.IIb

/-- A `c`-periodic `F` with `CylLp c 2 F` is integrable on every ball of `ℝ²`. -/
theorem avd_integrableOn_ball {c : ℝ} (hc : 0 < c) {F : ℝ × ℝ → CMerid} (hF : CylLp c 2 F)
    (z0 : ℝ × ℝ) (R : ℝ) : IntegrableOn F (Metric.closedBall z0 R) volume :=
  CylLocIntCover.integrableOn_closedBall_of_cell hc (by norm_num) hF.1
    (CylLocIntCover.memLp_cell_of_avg hc hF.2) z0 R

/-- An `L²(ℝ²)` field is integrable on every ball. -/
theorem avd_L2_ball {G : ℝ × ℝ → CMerid} (hG : MemLp G 2 volume) (z0 : ℝ × ℝ) (R : ℝ) :
    IntegrableOn G (Metric.closedBall z0 R) volume := by
  have : IsFiniteMeasure (volume.restrict (Metric.closedBall z0 R)) :=
    isFiniteMeasure_restrict.2 measure_closedBall_lt_top.ne
  exact MemLp.integrable one_le_two (hG.restrict _)

/-- Translates of an `L²` field in the `q` variable are `L²`. -/
theorem avd_L2_translate {G : ℝ × ℝ → CMerid} (hG : MemLp G 2 volume) (a : ℝ) :
    MemLp (fun z : ℝ × ℝ => G (z.1 + a, z.2)) 2 volume := by
  have hmp : MeasurePreserving (Prod.map (fun x : ℝ => x + a) id) (volume : Measure (ℝ × ℝ))
      volume :=
    (measurePreserving_add_right (volume : Measure ℝ) a).prod (MeasurePreserving.id _)
  exact hG.comp_measurePreserving hmp

/-- A coordinate of an integrable vector field is integrable. -/
theorem avd_coord (H : ℝ × ℝ → CMerid) (i : Fin 2) {S : Set (ℝ × ℝ)}
    (hH : IntegrableOn H S volume) : IntegrableOn (fun z => H z i) S volume := by
  have h := (EuclideanSpace.proj i : CMerid →L[ℂ] ℂ).integrable_comp hH
  exact h

/-- Coordinate of a locally integrable field times a compactly supported continuous scalar. -/
theorem avd_integrable_coord_mul (H : ℝ × ℝ → CMerid) (i : Fin 2)
    (hH : ∀ R : ℝ, IntegrableOn H (Metric.closedBall 0 R) volume)
    {φ : ℝ × ℝ → ℝ} (hφc : Continuous φ) (hφs : HasCompactSupport φ) :
    Integrable (fun z => H z i * (φ z : ℂ)) volume := by
  obtain ⟨R, hR⟩ := hφs.isCompact.isBounded.subset_closedBall (0 : ℝ × ℝ)
  have hK : IntegrableOn (fun z => H z i) (tsupport φ) volume :=
    IntegrableOn.mono_set (avd_coord H i (hH R)) hR
  have hprod : IntegrableOn (fun z => H z i * (φ z : ℂ)) (tsupport φ) volume :=
    IntegrableOn.mul_continuousOn hK (Complex.continuous_ofReal.comp hφc).continuousOn
      hφs.isCompact
  have hsupp : Function.support (fun z => H z i * (φ z : ℂ)) ⊆ tsupport φ := by
    intro z hz
    apply subset_tsupport φ
    intro h0
    apply hz
    simp [h0]
  exact (integrableOn_iff_integrable_of_support_subset hsupp).1 hprod

/-- Pairing of a locally integrable field with a vector test field is integrable. -/
theorem avd_sum_integrable {H : ℝ × ℝ → CMerid}
    (hH : ∀ R : ℝ, IntegrableOn H (Metric.closedBall 0 R) volume)
    {Φ : ℝ × ℝ → Fin 2 → ℝ} (hΦ : ∀ i : Fin 2, PlaneTest (fun z => Φ z i)) :
    Integrable (fun z => ∑ i : Fin 2, H z i * (Φ z i : ℂ)) volume :=
  integrable_finsetSum Finset.univ (fun i _ =>
    avd_integrable_coord_mul H i hH (hΦ i).smooth.continuous (hΦ i).compact)

/-- Translating a planar solenoidal test in `q` gives a planar solenoidal test. -/
theorem avd_planeSolTest_shift {Ψ : ℝ × ℝ → Fin 2 → ℝ} (hΨ : PlaneSolTest Ψ) (a : ℝ) :
    PlaneSolTest (fun z => Ψ (z.1 - a, z.2)) := by
  have hcomp : ∀ i : Fin 2, PlaneTest (fun z : ℝ × ℝ => Ψ (z.1 - a, z.2) i) := by
    intro i
    refine ⟨?_, ?_⟩
    · have hT : ContDiff ℝ ∞ (fun z : ℝ × ℝ => (z.1 - a, z.2)) := by fun_prop
      exact (hΨ.comp i).smooth.comp hT
    · have hv : (fun z : ℝ × ℝ => (z.1 - a, z.2)) = fun z => z - ((a : ℝ), (0 : ℝ)) := by
        funext z
        ext <;> simp
      convert (hΨ.comp i).compact.comp_homeomorph (Homeomorph.subRight ((a : ℝ), (0 : ℝ)))
        using 1
      funext z
      simp [← hv]
  refine ⟨hcomp, ?_⟩
  intro z
  have hw : ∀ y : ℝ × ℝ, y + (-a, (0 : ℝ)) = (y.1 - a, y.2) := fun y => by
    ext <;> simp [sub_eq_add_neg]
  have e0 : (fun y : ℝ × ℝ => Ψ (y.1 - a, y.2) 0) = fun y => Ψ (y + (-a, 0)) 0 := by
    funext y
    rw [hw]
  have e1 : (fun y : ℝ × ℝ => Ψ (y.1 - a, y.2) 1) = fun y => Ψ (y + (-a, 0)) 1 := by
    funext y
    rw [hw]
  show fderiv ℝ (fun y : ℝ × ℝ => Ψ (y.1 - a, y.2) 0) z (1, 0)
      + fderiv ℝ (fun y : ℝ × ℝ => Ψ (y.1 - a, y.2) 1) z (0, 1) = 0
  rw [e0, e1, fderiv_comp_add_right (f := fun y => Ψ y 0),
    fderiv_comp_add_right (f := fun y => Ψ y 1)]
  exact hΨ.div_free (z + (-a, 0))

/-- Translation invariance of the pairing: `∫ G(· + a e_q)·Ψ = ∫ G·Ψ(· - a e_q)`. -/
theorem avd_shift_pair (G : ℝ × ℝ → CMerid) (Ψ : ℝ × ℝ → Fin 2 → ℝ) (a : ℝ) :
    ∫ z, ∑ i : Fin 2, G (z.1 + a, z.2) i * (Ψ z i : ℂ) =
      ∫ w, ∑ i : Fin 2, G w i * (Ψ (w.1 - a, w.2) i : ℂ) := by
  have hw2 : ∀ z : ℝ × ℝ, z + ((a : ℝ), (0 : ℝ)) = (z.1 + a, z.2) := fun z => by
    ext <;> simp
  calc ∫ z, ∑ i : Fin 2, G (z.1 + a, z.2) i * (Ψ z i : ℂ)
      = ∫ z, (fun w : ℝ × ℝ => ∑ i : Fin 2, G w i * (Ψ (w.1 - a, w.2) i : ℂ))
          (z + ((a : ℝ), (0 : ℝ))) := by
        congr 1
        funext z
        rw [hw2]
        simp
    _ = ∫ w, ∑ i : Fin 2, G w i * (Ψ (w.1 - a, w.2) i : ℂ) :=
        integral_add_right_eq_self (fun w : ℝ × ℝ => ∑ i : Fin 2, G w i * (Ψ (w.1 - a, w.2) i : ℂ))
          ((a : ℝ), (0 : ℝ))

/-- Sums of coordinates of a finite sum of vector fields. -/
theorem avd_sum_apply (s : Finset ℤ) (f : ℤ → CMerid) (i : Fin 2) :
    (∑ j ∈ s, f j) i = ∑ j ∈ s, f j i := by
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, PiLp.add_apply, ih]

/-- Coordinates of the translate average. -/
theorem avd_ppAvg_apply (c : ℝ) (N : ℕ) (G : ℝ × ℝ → CMerid) (z : ℝ × ℝ) (i : Fin 2) :
    ppAvg c N G z i = (N : ℂ)⁻¹ * ∑ j ∈ Finset.Icc (-(N : ℤ)) (N : ℤ), G (z.1 + (j : ℝ) * c, z.2) i := by
  unfold ppAvg
  rw [PiLp.smul_apply, smul_eq_mul, avd_sum_apply]

/-- The translate average is `L²`. -/
theorem avd_ppAvg_memLp (c : ℝ) (N : ℕ) {G : ℝ × ℝ → CMerid} (hG : MemLp G 2 volume) :
    MemLp (ppAvg c N G) 2 volume := by
  unfold ppAvg
  have h := memLp_finsetSum' (Finset.Icc (-(N : ℤ)) (N : ℤ))
    (fun j _ => avd_L2_translate hG ((j : ℝ) * c))
  have e : (fun z : ℝ × ℝ => (N : ℂ)⁻¹ • ∑ j ∈ Finset.Icc (-(N : ℤ)) (N : ℤ),
      G (z.1 + (j : ℝ) * c, z.2)) =
      (N : ℂ)⁻¹ • ∑ j ∈ Finset.Icc (-(N : ℤ)) (N : ℤ), (fun z : ℝ × ℝ => G (z.1 + (j : ℝ) * c, z.2)) := by
    funext z
    simp [Finset.sum_apply]
  rw [e]
  exact h.const_smul ((N : ℂ)⁻¹)

/-- **Leaf `PartII-b:T12/1/4/1/5`** (SP 1933-1935): moving the translates onto the test. -/
theorem ppl_avg_dual : UnforcedLeray.Short.IIb.PPLAvgDual := by
  intro c hc N F G Ψ hF hG hPl hΨ
  obtain ⟨-, hPl2⟩ := hPl
  have hΨi : ∀ i : Fin 2, PlaneTest (fun z => Ψ z i) := fun i => hΨ.comp i
  have hFl : ∀ R : ℝ, IntegrableOn F (Metric.closedBall 0 R) volume :=
    fun R => avd_integrableOn_ball hc hF 0 R
  have hGl : ∀ R : ℝ, IntegrableOn G (Metric.closedBall 0 R) volume :=
    fun R => avd_L2_ball hG 0 R
  have hHl : ∀ R : ℝ, IntegrableOn (ppAvg c N G) (Metric.closedBall 0 R) volume :=
    fun R => avd_L2_ball (avd_ppAvg_memLp c N hG) 0 R
  have hS : MeasurableSet {z : ℝ × ℝ | 0 ≤ z.1 ∧ z.1 < (N : ℝ) * c} :=
    (measurableSet_le measurable_const measurable_fst).inter
      (measurableSet_lt measurable_fst measurable_const)
  have hFNl : ∀ R : ℝ, IntegrableOn (ppCut c N F) (Metric.closedBall 0 R) volume :=
    fun R => (hFl R).indicator hS
  have hPF : Integrable (fun z => ∑ i : Fin 2, F z i * (Ψ z i : ℂ)) volume :=
    avd_sum_integrable hFl hΨi
  have hPH : Integrable (fun z => ∑ i : Fin 2, ppAvg c N G z i * (Ψ z i : ℂ)) volume :=
    avd_sum_integrable hHl hΨi
  -- the translate pairings are integrable
  have hX : ∀ j : ℤ, Integrable
      (fun z : ℝ × ℝ => ∑ i : Fin 2, G (z.1 + (j : ℝ) * c, z.2) i * (Ψ z i : ℂ)) volume :=
    fun j => avd_sum_integrable (fun R => avd_L2_ball (avd_L2_translate hG ((j : ℝ) * c)) 0 R) hΨi
  have hYfun : ∀ j : ℤ, Integrable
      (fun z : ℝ × ℝ => ∑ i : Fin 2, ppCut c N F z i * (Ψ (z.1 - (j : ℝ) * c, z.2) i : ℂ))
      volume :=
    fun j => avd_sum_integrable hFNl (fun i => (avd_planeSolTest_shift hΨ ((j : ℝ) * c)).comp i)
  -- one translate: the shifted pairing of `G` equals that of `F_N`
  have hshift : ∀ j : ℤ,
      ∫ z, ∑ i : Fin 2, G (z.1 + (j : ℝ) * c, z.2) i * (Ψ z i : ℂ) =
        ∫ z, ∑ i : Fin 2, ppCut c N F z i * (Ψ (z.1 - (j : ℝ) * c, z.2) i : ℂ) := by
    intro j
    rw [avd_shift_pair G Ψ ((j : ℝ) * c)]
    have hT := avd_planeSolTest_shift hΨ ((j : ℝ) * c)
    have hA : Integrable
        (fun z : ℝ × ℝ => ∑ i : Fin 2, ppCut c N F z i * (Ψ (z.1 - (j : ℝ) * c, z.2) i : ℂ))
        volume := hYfun j
    have hB : Integrable
        (fun z : ℝ × ℝ => ∑ i : Fin 2, G z i * (Ψ (z.1 - (j : ℝ) * c, z.2) i : ℂ)) volume :=
      avd_sum_integrable hGl (fun i => hT.comp i)
    have h0 : ∫ z : ℝ × ℝ, ∑ i : Fin 2, (ppCut c N F z i - G z i) *
        (Ψ (z.1 - (j : ℝ) * c, z.2) i : ℂ) = 0 := (hPl2 _ hT).2
    have hsub : ∫ z : ℝ × ℝ, ∑ i : Fin 2, (ppCut c N F z i - G z i) *
        (Ψ (z.1 - (j : ℝ) * c, z.2) i : ℂ) =
        (∫ z : ℝ × ℝ, ∑ i : Fin 2, ppCut c N F z i * (Ψ (z.1 - (j : ℝ) * c, z.2) i : ℂ)) -
          ∫ z : ℝ × ℝ, ∑ i : Fin 2, G z i * (Ψ (z.1 - (j : ℝ) * c, z.2) i : ℂ) := by
      rw [← integral_sub hA hB]
      congr 1
      funext z
      simp only [sub_mul, Finset.sum_sub_distrib]
    rw [hsub] at h0
    exact (sub_eq_zero.1 h0).symm
  -- the averaged pairing, summed over the translates
  have key : ∫ z, ∑ i : Fin 2, ppAvg c N G z i * (Ψ z i : ℂ) =
      ∫ z, ∑ i : Fin 2, ppCut c N F z i * (ppDual c N Ψ z i : ℂ) := by
    have K1 : ∀ z : ℝ × ℝ, ∑ i : Fin 2, ppAvg c N G z i * (Ψ z i : ℂ) =
        (N : ℂ)⁻¹ * ∑ j ∈ Finset.Icc (-(N : ℤ)) (N : ℤ),
          ∑ i : Fin 2, G (z.1 + (j : ℝ) * c, z.2) i * (Ψ z i : ℂ) := by
      intro z
      simp only [avd_ppAvg_apply, Finset.mul_sum, Finset.sum_mul]
      rw [Finset.sum_comm]
      exact Finset.sum_congr rfl (fun j _ => Finset.sum_congr rfl (fun i _ => by ring))
    have K3 : ∀ z : ℝ × ℝ, ∑ i : Fin 2, ppCut c N F z i * (ppDual c N Ψ z i : ℂ) =
        (N : ℂ)⁻¹ * ∑ j ∈ Finset.Icc (-(N : ℤ)) (N : ℤ),
          ∑ i : Fin 2, ppCut c N F z i * (Ψ (z.1 - (j : ℝ) * c, z.2) i : ℂ) := by
      intro z
      simp only [ppDual, Complex.ofReal_mul, Complex.ofReal_sum, Complex.ofReal_inv,
        Complex.ofReal_natCast, Finset.mul_sum, Finset.sum_mul]
      rw [Finset.sum_comm]
      exact Finset.sum_congr rfl (fun j _ => Finset.sum_congr rfl (fun i _ => by ring))
    calc ∫ z, ∑ i : Fin 2, ppAvg c N G z i * (Ψ z i : ℂ)
        = ∫ z, (N : ℂ)⁻¹ * ∑ j ∈ Finset.Icc (-(N : ℤ)) (N : ℤ),
            ∑ i : Fin 2, G (z.1 + (j : ℝ) * c, z.2) i * (Ψ z i : ℂ) := by
          congr 1
          funext z
          exact K1 z
      _ = (N : ℂ)⁻¹ * ∫ z, ∑ j ∈ Finset.Icc (-(N : ℤ)) (N : ℤ),
            ∑ i : Fin 2, G (z.1 + (j : ℝ) * c, z.2) i * (Ψ z i : ℂ) := integral_const_mul _ _
      _ = (N : ℂ)⁻¹ * ∑ j ∈ Finset.Icc (-(N : ℤ)) (N : ℤ),
            ∫ z, ∑ i : Fin 2, G (z.1 + (j : ℝ) * c, z.2) i * (Ψ z i : ℂ) := by
          rw [integral_finsetSum (f := fun (j : ℤ) z => ∑ i : Fin 2,
            G (z.1 + (j : ℝ) * c, z.2) i * (Ψ z i : ℂ)) _ (fun j _ => hX j)]
      _ = (N : ℂ)⁻¹ * ∑ j ∈ Finset.Icc (-(N : ℤ)) (N : ℤ),
            ∫ z, ∑ i : Fin 2, ppCut c N F z i * (Ψ (z.1 - (j : ℝ) * c, z.2) i : ℂ) := by
          congr 1
          exact Finset.sum_congr rfl (fun j _ => hshift j)
      _ = (N : ℂ)⁻¹ * ∫ z, ∑ j ∈ Finset.Icc (-(N : ℤ)) (N : ℤ),
            ∑ i : Fin 2, ppCut c N F z i * (Ψ (z.1 - (j : ℝ) * c, z.2) i : ℂ) := by
          rw [integral_finsetSum (f := fun (j : ℤ) z => ∑ i : Fin 2,
            ppCut c N F z i * (Ψ (z.1 - (j : ℝ) * c, z.2) i : ℂ)) _ (fun j _ => hYfun j)]
      _ = ∫ z, (N : ℂ)⁻¹ * ∑ j ∈ Finset.Icc (-(N : ℤ)) (N : ℤ),
            ∑ i : Fin 2, ppCut c N F z i * (Ψ (z.1 - (j : ℝ) * c, z.2) i : ℂ) :=
          (integral_const_mul _ _).symm
      _ = ∫ z, ∑ i : Fin 2, ppCut c N F z i * (ppDual c N Ψ z i : ℂ) := by
          congr 1
          funext z
          exact (K3 z).symm
  simp only [sub_mul, Finset.sum_sub_distrib]
  rw [integral_sub hPF hPH, key]

end UnforcedLeray.Short.IIb
