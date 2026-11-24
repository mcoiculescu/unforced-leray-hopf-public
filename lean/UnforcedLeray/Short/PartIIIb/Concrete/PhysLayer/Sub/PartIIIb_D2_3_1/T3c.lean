import UnforcedLeray.Short.PartIIIb.Concrete.PhysLayer.Sub.PartIIIb_D2_3_1.Sub.PartIIIb_IIIb_D2_3_1_3

/-!
# Generic `z`-derivative of the outward primitive (`PartIII-b:IIIb-D2/3/1/3/3`)

Source 4178-4179: `∂_z Ψ_Z(r, z) = -r Z_r(r, 0, z)`.  Proof outline:
* pointwise, for `x ≠ 0` in the region: `Z_r + x ∂_x Z_r = -x ∂_z Z_z` on the half plane
  (cylindrical divergence, using `y₀ Z_1 = y₁ Z_0` from axisymmetry);
* `∫_{(r,∞)} x ∂_z Z_z = r Z_r(r)` by the fundamental theorem of calculus on `(r,∞)`,
  with the boundary term at infinity from `StreamDecay`;
* differentiation under the integral sign, dominated by the `StreamDecay` majorant.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Metric UnforcedLeray.Axi

namespace UnforcedLeray.Short.PartIIIb.Concrete

open UnforcedLeray.PhaseSpace UnforcedLeray.B0411

theorem t3c_mem {ν R : ℝ} (z x : ℝ) (h : R * Real.sqrt (5 * ν / 6) < x) :
    (!₂[x, 0, z] : Space) ∈ youngOpen ν R := by
  show R * Real.sqrt (5 * ν / 6) < ϱ (!₂[x, 0, z] : Space)
  have hϱ : ϱ (!₂[x, 0, z] : Space) = |x| := by
    simp [ϱ, Real.sqrt_sq_eq_abs]
  rw [hϱ]
  exact lt_of_lt_of_le h (le_abs_self x)

theorem t3c_c0 (x0 z : ℝ) :
    HasDerivAt (fun x : ℝ => (!₂[x, 0, z] : Space)) (coordinateVector 0) x0 := by
  have h : HasDerivAt (fun x : ℝ => (!₂[x0, 0, z] : Space) + (x - x0) • (coordinateVector 0 : Space))
      (coordinateVector 0) x0 := by
    have h1 := ((hasDerivAt_id' x0).sub_const x0).smul_const (coordinateVector 0 : Space)
    simpa using h1.const_add (!₂[x0, 0, z] : Space)
  convert h using 1
  funext x
  ext i
  fin_cases i <;> simp [coordinateVector] <;> ring

theorem t3c_c2 (x z0 : ℝ) :
    HasDerivAt (fun z' : ℝ => (!₂[x, 0, z'] : Space)) (coordinateVector 2) z0 := by
  have h : HasDerivAt (fun z' : ℝ => (!₂[x, 0, z0] : Space) + (z' - z0) • (coordinateVector 2 : Space))
      (coordinateVector 2) z0 := by
    have h1 := ((hasDerivAt_id' z0).sub_const z0).smul_const (coordinateVector 2 : Space)
    simpa using h1.const_add (!₂[x, 0, z0] : Space)
  convert h using 1
  funext z'
  ext i
  fin_cases i <;> simp [coordinateVector] <;> ring

theorem t3c_c1 (x z : ℝ) :
    HasDerivAt (fun t : ℝ => (!₂[x, t, z] : Space)) (coordinateVector 1) 0 := by
  have h : HasDerivAt (fun t : ℝ => (!₂[x, 0, z] : Space) + (t - 0) • (coordinateVector 1 : Space))
      (coordinateVector 1) 0 := by
    have h1 := ((hasDerivAt_id' (0 : ℝ)).sub_const (0 : ℝ)).smul_const (coordinateVector 1 : Space)
    simpa using h1.const_add (!₂[x, 0, z] : Space)
  convert h using 1
  funext t
  ext i
  fin_cases i <;> simp [coordinateVector] <;> ring

theorem t3c_chain {Zf : Space → Space} {p v : Space} {c : ℝ → Space} {x : ℝ}
    (hd : DifferentiableAt ℝ Zf p) (hc : HasDerivAt c v x) (hcx : c x = p) :
    HasDerivAt (fun t => Zf (c t)) (fderiv ℝ Zf p v) x := by
  subst hcx
  exact hd.hasFDerivAt.comp_hasDerivAt x hc

theorem t3c_proj (j : Fin 3) {f : ℝ → Space} {f' : Space} {x : ℝ} (h : HasDerivAt f f' x) :
    HasDerivAt (fun t => f t j) (f' j) x := by
  have h2 := (EuclideanSpace.proj j : Space →L[ℝ] ℝ).hasFDerivAt.comp_hasDerivAt x h
  convert h2 using 1 <;> first | rfl | simp

/-- Axisymmetry relation: off the axis in the young region, `y₀ Z_1 = y₁ Z_0`. -/
theorem t3c_rel {ν R : ℝ} (Z : ℝ → Space → Space) (τ : ℝ)
    (hAx : AxiNoSwirlOn (youngOpen ν R) Z) {y : Space} (hy : y ∈ youngOpen ν R) (hax : y ∉ axis) :
    y 0 * Z τ y 1 = y 1 * Z τ y 0 := by
  have hZ0 : Z τ y 0 = Z τ (meridPt y) 0 * (y 0 / ϱ y) := by
    rw [hAx τ y hy hax]; simp [frameL_apply, eR_apply_zero, e3_apply]
  have hZ1 : Z τ y 1 = Z τ (meridPt y) 0 * (y 1 / ϱ y) := by
    rw [hAx τ y hy hax]; simp [frameL_apply, eR_apply_one, e3_apply]
  rw [hZ0, hZ1]
  ring

theorem t3c_div {ν R : ℝ} {Z : ℝ → Space → Space} {τ : ℝ}
    (hdiv : ∀ y ∈ youngOpen ν R, ∑ j : Fin 3, physPd (Z τ) j y j = 0) {p : Space}
    (hp : p ∈ youngOpen ν R) :
    fderiv ℝ (Z τ) p (coordinateVector 0) 0 + fderiv ℝ (Z τ) p (coordinateVector 1) 1 +
      fderiv ℝ (Z τ) p (coordinateVector 2) 2 = 0 := by
  have h := hdiv p hp
  simp only [physPd, Fin.sum_univ_three] at h
  exact h

/-- Pointwise cylindrical divergence identity on the half plane, `x ≠ 0`. -/
theorem t3c_key {ν R : ℝ} {Z : ℝ → Space → Space} {τ : ℝ}
    (hZc : ContDiffOn ℝ 2 (Z τ) (youngOpen ν R))
    (hdiv : ∀ y ∈ youngOpen ν R, ∑ j : Fin 3, physPd (Z τ) j y j = 0)
    (hAx : AxiNoSwirlOn (youngOpen ν R) Z) (z x0 : ℝ) (hx : R * Real.sqrt (5 * ν / 6) < x0)
    (hx0 : x0 ≠ 0) :
    Z τ !₂[x0, 0, z] 0 + x0 * fderiv ℝ (Z τ) !₂[x0, 0, z] (coordinateVector 0) 0 =
      -(x0 * fderiv ℝ (Z τ) !₂[x0, 0, z] (coordinateVector 2) 2) := by
  have hopen : IsOpen (youngOpen ν R) := isOpen_lt continuous_const continuous_ϱ
  have hp : (!₂[x0, 0, z] : Space) ∈ youngOpen ν R := t3c_mem z x0 hx
  have hdiff : DifferentiableAt ℝ (Z τ) !₂[x0, 0, z] :=
    (hZc.contDiffAt (hopen.mem_nhds hp)).differentiableAt (by norm_num)
  have hL : HasDerivAt (fun t : ℝ => Z τ !₂[x0, t, z] 1)
      (fderiv ℝ (Z τ) !₂[x0, 0, z] (coordinateVector 1) 1) 0 :=
    t3c_proj 1 (t3c_chain hdiff (t3c_c1 x0 z) rfl)
  have hR : HasDerivAt (fun t : ℝ => Z τ !₂[x0, t, z] 0)
      (fderiv ℝ (Z τ) !₂[x0, 0, z] (coordinateVector 1) 0) 0 :=
    t3c_proj 0 (t3c_chain hdiff (t3c_c1 x0 z) rfl)
  have hRHS : HasDerivAt (fun t : ℝ => t * Z τ !₂[x0, t, z] 0)
      (1 * Z τ !₂[x0, 0, z] 0 + 0 * fderiv ℝ (Z τ) !₂[x0, 0, z] (coordinateVector 1) 0) 0 :=
    (hasDerivAt_id' (0 : ℝ)).mul hR
  have hopen' : IsOpen ((fun t : ℝ => (!₂[x0, t, z] : Space)) ⁻¹' youngOpen ν R) :=
    hopen.preimage (by fun_prop)
  have h0mem : (0 : ℝ) ∈ (fun t : ℝ => (!₂[x0, t, z] : Space)) ⁻¹' youngOpen ν R := hp
  have hev : (fun t : ℝ => x0 * Z τ !₂[x0, t, z] 1) =ᶠ[nhds 0]
      (fun t : ℝ => t * Z τ !₂[x0, t, z] 0) := by
    filter_upwards [hopen'.mem_nhds h0mem] with t ht
    have hax : (!₂[x0, t, z] : Space) ∉ axis := by
      intro h
      apply hx0
      have h0 : (!₂[x0, t, z] : Space) 0 = 0 := h.1
      simpa using h0
    have := t3c_rel (ν := ν) (R := R) Z τ hAx ht hax
    simpa using this
  have hLHS : HasDerivAt (fun t : ℝ => x0 * Z τ !₂[x0, t, z] 1)
      (x0 * fderiv ℝ (Z τ) !₂[x0, 0, z] (coordinateVector 1) 1) 0 := hL.const_mul x0
  have hLHS' := hRHS.congr_of_eventuallyEq hev
  have h1 : x0 * fderiv ℝ (Z τ) !₂[x0, 0, z] (coordinateVector 1) 1 = Z τ !₂[x0, 0, z] 0 := by
    have := hLHS.unique hLHS'
    simpa using this
  have hdv := t3c_div hdiv hp
  linear_combination (-1 : ℝ) * h1 + x0 * hdv

/-- Derivative of `x ↦ x Z_0(x, 0, z)` (product rule). -/
theorem t3c_hGd {ν R : ℝ} {Z : ℝ → Space → Space} {τ : ℝ}
    (hZc : ContDiffOn ℝ 2 (Z τ) (youngOpen ν R)) (z x : ℝ) (hx : R * Real.sqrt (5 * ν / 6) < x) :
    HasDerivAt (fun x' : ℝ => x' * Z τ !₂[x', 0, z] 0)
      (Z τ !₂[x, 0, z] 0 + x * fderiv ℝ (Z τ) !₂[x, 0, z] (coordinateVector 0) 0) x := by
  have hopen : IsOpen (youngOpen ν R) := isOpen_lt continuous_const continuous_ϱ
  have hp : (!₂[x, 0, z] : Space) ∈ youngOpen ν R := t3c_mem z x hx
  have hdiff : DifferentiableAt ℝ (Z τ) !₂[x, 0, z] :=
    (hZc.contDiffAt (hopen.mem_nhds hp)).differentiableAt (by norm_num)
  have hG : HasDerivAt (fun x' : ℝ => Z τ !₂[x', 0, z] 0)
      (fderiv ℝ (Z τ) !₂[x, 0, z] (coordinateVector 0) 0) x :=
    t3c_proj 0 (t3c_chain hdiff (t3c_c0 x z) rfl)
  have := (hasDerivAt_id' x).mul hG
  exact this.congr_deriv (by ring)

/-- Continuity of the `j`-th component of `Z` on the half plane at `z'`. -/
theorem t3c_contZ {ν R : ℝ} {Z : ℝ → Space → Space} {τ : ℝ}
    (hZc : ContDiffOn ℝ 2 (Z τ) (youngOpen ν R)) (z' : ℝ) (j : Fin 3) :
    ContinuousOn (fun x : ℝ => Z τ !₂[x, 0, z'] j) (Ioi (R * Real.sqrt (5 * ν / 6))) := by
  have hg : Continuous (fun x : ℝ => (!₂[x, 0, z'] : Space)) := by fun_prop
  have h1 : ContinuousOn (fun x : ℝ => Z τ !₂[x, 0, z']) (Ioi (R * Real.sqrt (5 * ν / 6))) :=
    hZc.continuousOn.comp hg.continuousOn (fun x hx => t3c_mem z' x hx)
  exact (EuclideanSpace.proj j : Space →L[ℝ] ℝ).continuous.comp_continuousOn h1

/-- Continuity of the `v`-derivative of `Z`'s `j`-th component on the half plane. -/
theorem t3c_contD {ν R : ℝ} {Z : ℝ → Space → Space} {τ : ℝ}
    (hZc : ContDiffOn ℝ 2 (Z τ) (youngOpen ν R)) (z' : ℝ) (v : Space) (j : Fin 3) :
    ContinuousOn (fun x : ℝ => fderiv ℝ (Z τ) !₂[x, 0, z'] v j)
      (Ioi (R * Real.sqrt (5 * ν / 6))) := by
  have hopen : IsOpen (youngOpen ν R) := isOpen_lt continuous_const continuous_ϱ
  have hg : Continuous (fun x : ℝ => (!₂[x, 0, z'] : Space)) := by fun_prop
  have h1 : ContinuousOn (fun y => fderiv ℝ (Z τ) y) (youngOpen ν R) :=
    hZc.continuousOn_fderiv_of_isOpen hopen (by norm_num)
  have h2 : ContinuousOn (fun x : ℝ => fderiv ℝ (Z τ) !₂[x, 0, z'])
      (Ioi (R * Real.sqrt (5 * ν / 6))) :=
    h1.comp hg.continuousOn (fun x hx => t3c_mem z' x hx)
  have h3 : ContinuousOn (fun x : ℝ => fderiv ℝ (Z τ) !₂[x, 0, z'] v)
      (Ioi (R * Real.sqrt (5 * ν / 6))) :=
    h2.clm_apply continuousOn_const
  exact (EuclideanSpace.proj j : Space →L[ℝ] ℝ).continuous.comp_continuousOn h3

theorem outPrimDerivZ : OutPrimDerivZ := by
  intro ν R Z τ hZc hdiv hAx hS r z hr
  have hopen : IsOpen (youngOpen ν R) := isOpen_lt continuous_const continuous_ϱ
  obtain ⟨⟨B, hBi, hB⟩, hTend⟩ := hS r z hr
  have hcontF : ∀ z' : ℝ, ContinuousOn (fun x : ℝ => x * Z τ !₂[x, 0, z'] 2) (Ioi r) :=
    fun z' => (continuousOn_id.mul (t3c_contZ hZc z' 2)).mono (fun x hx => lt_trans hr hx)
  have hFz : IntegrableOn (fun x : ℝ => x * Z τ !₂[x, 0, z] 2) (Ioi r) := by
    refine Integrable.mono' hBi ((hcontF z).aestronglyMeasurable measurableSet_Ioi) ?_
    refine (ae_restrict_mem measurableSet_Ioi).mono fun x hx => ?_
    exact (hB x hx z (Metric.mem_ball_self one_pos)).1
  have hD2 : ContinuousOn (fun x : ℝ => x * fderiv ℝ (Z τ) !₂[x, 0, z] (coordinateVector 2) 2)
      (Ioi r) :=
    (continuousOn_id.mul (t3c_contD hZc z (coordinateVector 2) 2)).mono
      (fun x hx => lt_trans hr hx)
  have hgInt : IntegrableOn
      (fun x : ℝ => -(x * fderiv ℝ (Z τ) !₂[x, 0, z] (coordinateVector 2) 2)) (Ioi r) := by
    refine Integrable.mono' hBi (hD2.neg.aestronglyMeasurable measurableSet_Ioi) ?_
    refine (ae_restrict_mem measurableSet_Ioi).mono fun x hx => ?_
    rw [norm_neg]
    exact (hB x hx z (Metric.mem_ball_self one_pos)).2
  have h0 : ∀ᵐ x ∂(volume : Measure ℝ), x ≠ 0 := by
    have := (Set.countable_singleton (0 : ℝ)).ae_notMem (volume : Measure ℝ)
    filter_upwards [this] with x hx
    simpa using hx
  have hae : (fun x : ℝ => Z τ !₂[x, 0, z] 0 + x * fderiv ℝ (Z τ) !₂[x, 0, z] (coordinateVector 0) 0)
      =ᵐ[volume.restrict (Ioi r)]
      (fun x : ℝ => -(x * fderiv ℝ (Z τ) !₂[x, 0, z] (coordinateVector 2) 2)) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi, ae_restrict_of_ae h0] with x hx hx0
    exact t3c_key hZc hdiv hAx z x (lt_trans hr hx) hx0
  have hf'Int : IntegrableOn
      (fun x : ℝ => Z τ !₂[x, 0, z] 0 + x * fderiv ℝ (Z τ) !₂[x, 0, z] (coordinateVector 0) 0)
      (Ioi r) :=
    hgInt.congr_fun_ae hae.symm
  have hcont : ContinuousWithinAt (fun x : ℝ => x * Z τ !₂[x, 0, z] 0) (Ici r) r :=
    (t3c_hGd hZc z r hr).continuousAt.continuousWithinAt
  have hFTC := integral_Ioi_of_hasDerivAt_of_tendsto (f := fun x : ℝ => x * Z τ !₂[x, 0, z] 0)
    (f' := fun x : ℝ => Z τ !₂[x, 0, z] 0 + x * fderiv ℝ (Z τ) !₂[x, 0, z] (coordinateVector 0) 0)
    hcont (fun x hx => t3c_hGd hZc z x (lt_trans hr hx)) hf'Int hTend
  have hc := integral_congr_ae hae
  rw [integral_neg] at hc
  have hI2 : ∫ x in Ioi r, x * fderiv ℝ (Z τ) !₂[x, 0, z] (coordinateVector 2) 2 =
      r * Z τ !₂[r, 0, z] 0 := by
    linarith
  have hD : HasDerivAt (fun z' : ℝ => ∫ x in Ioi r, x * Z τ !₂[x, 0, z'] 2)
      (∫ x in Ioi r, x * fderiv ℝ (Z τ) !₂[x, 0, z] (coordinateVector 2) 2) z := by
    refine (hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := volume.restrict (Ioi r))
      (F := fun z' x => x * Z τ !₂[x, 0, z'] 2)
      (F' := fun z' x => x * fderiv ℝ (Z τ) !₂[x, 0, z'] (coordinateVector 2) 2)
      (bound := B) (Metric.ball_mem_nhds z one_pos) ?_ hFz ?_ ?_ hBi ?_).2
    · exact Filter.Eventually.of_forall fun z' => (hcontF z').aestronglyMeasurable measurableSet_Ioi
    · exact hD2.aestronglyMeasurable measurableSet_Ioi
    · refine (ae_restrict_mem measurableSet_Ioi).mono fun a ha x hx => ?_
      exact (hB a ha x hx).2
    · refine (ae_restrict_mem measurableSet_Ioi).mono fun a ha x _ => ?_
      have hdA : DifferentiableAt ℝ (Z τ) !₂[a, 0, x] :=
        (hZc.contDiffAt (hopen.mem_nhds (t3c_mem x a (lt_trans hr ha)))).differentiableAt
          (by norm_num)
      exact (t3c_proj 2 (t3c_chain hdA (t3c_c2 a x) rfl)).const_mul a
  have hfin := hD.neg
  unfold outPrim
  rw [← hI2]
  exact hfin

end UnforcedLeray.Short.PartIIIb.Concrete
