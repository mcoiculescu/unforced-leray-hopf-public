import UnforcedLeray.Short.PartIIIb.Concrete.PhysLayer.Sub.PartIIIb_D2_3_1.Sub.PartIIIb_IIIb_D2_3_1_3

/-!
# Generic `r`-derivative of the outward primitive (`PartIII-b:IIIb-D2/3/1/3/2`)

Source 4178 (fundamental theorem of calculus): `∂_r Ψ_Z(r, z) = r Z_z(r, 0, z)`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter UnforcedLeray.Axi

namespace UnforcedLeray.Short.PartIIIb.Concrete

open UnforcedLeray.PhaseSpace UnforcedLeray.B0411

theorem outPrimDerivR : OutPrimDerivR := by
  intro ν R Z τ hZc hS r z hr
  -- an intermediate radius `a` with `R√(5ν/6) < a < r`
  obtain ⟨a, hra, har⟩ : ∃ a : ℝ, R * Real.sqrt (5 * ν / 6) < a ∧ a < r :=
    ⟨(R * Real.sqrt (5 * ν / 6) + r) / 2, by linarith, by linarith⟩
  have hrm : r ∈ Ioi (R * Real.sqrt (5 * ν / 6)) := lt_trans hra har
  -- the half-plane point lies in the young region
  have hmem : ∀ ρ : ℝ, R * Real.sqrt (5 * ν / 6) < ρ → (!₂[ρ, 0, z] : Space) ∈ youngOpen ν R := by
    intro ρ hρ
    show R * Real.sqrt (5 * ν / 6) < ϱ (!₂[ρ, 0, z] : Space)
    have hϱ : ϱ (!₂[ρ, 0, z] : Space) = |ρ| := by
      simp [ϱ, Real.sqrt_sq_eq_abs]
    rw [hϱ]
    exact lt_of_lt_of_le hρ (le_abs_self ρ)
  have hg : Continuous (fun ρ : ℝ => (!₂[ρ, 0, z] : Space)) := by
    fun_prop
  -- continuity of the integrand on the region
  have hFc : ContinuousOn (fun ρ : ℝ => ρ * Z τ !₂[ρ, 0, z] 2) (Ioi (R * Real.sqrt (5 * ν / 6))) := by
    have h1 : ContinuousOn (fun ρ : ℝ => Z τ !₂[ρ, 0, z]) (Ioi (R * Real.sqrt (5 * ν / 6))) :=
      hZc.continuousOn.comp hg.continuousOn (fun ρ hρ => hmem ρ hρ)
    have h2 : ContinuousOn (fun ρ : ℝ => Z τ !₂[ρ, 0, z] 2) (Ioi (R * Real.sqrt (5 * ν / 6))) :=
      (EuclideanSpace.proj (2 : Fin 3)).continuous.comp_continuousOn h1
    exact continuousOn_id.mul h2
  -- integrability on `(a, ∞)` from the decay bound at `a`
  obtain ⟨⟨B, hBi, hB⟩, -⟩ := hS a z hra
  have hFi : IntegrableOn (fun ρ : ℝ => ρ * Z τ !₂[ρ, 0, z] 2) (Ioi a) := by
    refine Integrable.mono' hBi ?_ ?_
    · exact (hFc.mono (fun x hx => lt_trans hra hx)).aestronglyMeasurable measurableSet_Ioi
    · refine (ae_restrict_mem measurableSet_Ioi).mono fun ρ hρ => ?_
      exact (hB ρ hρ z (Metric.mem_ball_self one_pos)).1
  -- splitting the tail integral at `r'`
  have hout : ∀ r' : ℝ, a < r' →
      outPrim Z τ r' z = -(∫ ρ in Ioi a, ρ * Z τ !₂[ρ, 0, z] 2) +
        ∫ ρ in a..r', ρ * Z τ !₂[ρ, 0, z] 2 := by
    intro r' hr'
    have hsplit : ∫ ρ in Ioi a, ρ * Z τ !₂[ρ, 0, z] 2 =
        (∫ ρ in Ioc a r', ρ * Z τ !₂[ρ, 0, z] 2) + ∫ ρ in Ioi r', ρ * Z τ !₂[ρ, 0, z] 2 := by
      rw [← Set.Ioc_union_Ioi_eq_Ioi hr'.le]
      refine setIntegral_union ?_ measurableSet_Ioi ?_ ?_
      · exact Set.disjoint_left.2 fun x hx hx' => absurd hx' (not_lt.2 hx.2)
      · exact hFi.mono_set fun x hx => hx.1
      · exact hFi.mono_set fun x hx => lt_trans hr' hx
    rw [intervalIntegral.integral_of_le hr'.le, hsplit]
    unfold outPrim
    ring
  -- the FTC for the interval part
  have hint : IntervalIntegrable (fun ρ : ℝ => ρ * Z τ !₂[ρ, 0, z] 2) volume a r := by
    refine ContinuousOn.intervalIntegrable (hFc.mono ?_)
    rw [Set.uIcc_of_le (le_of_lt har)]
    intro x hx
    exact lt_of_lt_of_le hra hx.1
  have hmeas : StronglyMeasurableAtFilter (fun ρ : ℝ => ρ * Z τ !₂[ρ, 0, z] 2) (nhds r) volume :=
    hFc.stronglyMeasurableAtFilter isOpen_Ioi r hrm
  have hcont := hFc.continuousAt (isOpen_Ioi.mem_nhds hrm)
  have hI : HasDerivAt (fun u => ∫ ρ in a..u, ρ * Z τ !₂[ρ, 0, z] 2)
      (r * Z τ !₂[r, 0, z] 2) r :=
    intervalIntegral.integral_hasDerivAt_right hint hmeas hcont
  have hderiv := hI.const_add (-(∫ ρ in Ioi a, ρ * Z τ !₂[ρ, 0, z] 2))
  have hev : (fun r' => outPrim Z τ r' z) =ᶠ[nhds r]
      fun r' => -(∫ ρ in Ioi a, ρ * Z τ !₂[ρ, 0, z] 2) +
        ∫ ρ in a..r', ρ * Z τ !₂[ρ, 0, z] 2 :=
    Filter.eventually_of_mem (Ioi_mem_nhds har) (fun r' hr' => hout r' hr')
  exact hderiv.congr_of_eventuallyEq hev

end UnforcedLeray.Short.PartIIIb.Concrete
