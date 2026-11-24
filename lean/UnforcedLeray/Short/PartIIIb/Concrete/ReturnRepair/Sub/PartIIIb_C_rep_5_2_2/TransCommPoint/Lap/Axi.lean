import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_5_2_2.TransCommPoint.Lap.Calc

/-!
# Axisymmetric swirl-free fields: line identities (`TCLap` leaves)

Source `the November 2 reference manuscript` 4176-4214.
-/

set_option autoImplicit false

noncomputable section

open Filter Set MeasureTheory UnforcedLeray.Axi
open scoped ENNReal

namespace UnforcedLeray.Short.PartIIIb.Concrete

/-- A `C²` field on `{ϱ > a}` given by its meridian trace, solenoidal. -/
structure AxiC2 (X : Space → Space) (a : ℝ) : Prop where
  ha : 0 ≤ a
  smooth : ContDiffOn ℝ 2 X {y : Space | a < ϱ y}
  rep0 : ∀ y, a < ϱ y → X y 0 = (y 0 / ϱ y) * X (meridPt y) 0
  rep1 : ∀ y, a < ϱ y → X y 1 = (y 1 / ϱ y) * X (meridPt y) 0
  rep2 : ∀ y, a < ϱ y → X y 2 = X (meridPt y) 2
  div : ∀ y, a < ϱ y → ∑ j : Fin 3, physPd X j y j = 0

variable {X : Space → Space} {a : ℝ}

theorem AxiC2.cd (H : AxiC2 X a) {y : Space} (hy : a < ϱ y) : ContDiffAt ℝ 2 X y :=
  H.smooth.contDiffAt ((isOpen_lt continuous_const continuous_ϱ).mem_nhds hy)

theorem AxiC2.cdc (H : AxiC2 X a) (i : Fin 3) {y : Space} (hy : a < ϱ y) :
    ContDiffAt ℝ 2 (fun y => X y i) y :=
  (EuclideanSpace.proj i : Space →L[ℝ] ℝ).contDiff.contDiffAt.comp y (H.cd hy)

theorem AxiC2.dc (H : AxiC2 X a) (i : Fin 3) {y : Space} (hy : a < ϱ y) :
    DifferentiableAt ℝ (fun y => X y i) y :=
  (H.cdc i hy).differentiableAt (by norm_num)

theorem AxiC2.pt (H : AxiC2 X a) {ρ : ℝ} (z : ℝ) (h : a < ρ) : a < ϱ (!₂[ρ, 0, z] : Space) := by
  rw [tcb_varrho_pt (le_trans H.ha h.le)]; exact h

theorem tcl_sqsum {y : Space} (h : 0 < ϱ y) : y 0 * y 0 + y 1 * y 1 = ϱ y ^ 2 := by
  have hsq : 0 < y 0 ^ 2 + y 1 ^ 2 := by
    by_contra hh
    have : ϱ y = 0 := by
      unfold ϱ
      rw [Real.sqrt_eq_zero_of_nonpos (not_lt.1 hh)]
    linarith
  have := Real.sq_sqrt hsq.le
  unfold ϱ
  nlinarith

/-- (R1) the radial derivative of `X₂` at `y` equals that at the trace point. -/
theorem AxiC2.r1 (H : AxiC2 X a) {y : Space} (hy : a < ϱ y) :
    y 0 * fderiv ℝ (fun y => X y 2) y (coordinateVector 0) +
      y 1 * fderiv ℝ (fun y => X y 2) y (coordinateVector 1) =
      ϱ y * fderiv ℝ (fun y => X y 2) (meridPt y) (coordinateVector 0) := by
  have hρ : 0 < ϱ y := lt_of_le_of_lt H.ha hy
  set v : Space := y 0 • (coordinateVector 0 : Space) + y 1 • (coordinateVector 1 : Space) with hv
  have hv0 : v 0 = y 0 := by simp [hv, coordinateVector]
  have hv1 : v 1 = y 1 := by simp [hv, coordinateVector]
  have hv2 : v 2 = 0 := by simp [hv, coordinateVector]
  have h1 : HasDerivAt (fun s : ℝ => X (y + s • v) 2) (fderiv ℝ (fun y => X y 2) y v) 0 := by
    have := tcl_line (f := fun y => X y 2) (q := y) v 0 (by simpa using H.dc 2 hy)
    simpa using this
  have hA : HasDerivAt (fun r : ℝ => X (!₂[r, 0, y 2]) 2)
      (fderiv ℝ (fun y => X y 2) (meridPt y) (coordinateVector 0)) (ϱ y) :=
    tcl_hasDeriv_rho (f := fun y => X y 2) (z := y 2) (ρ := ϱ y) (H.dc 2 (by
      have := H.pt (ρ := ϱ y) (y 2) hy
      exact this))
  have hϱ := tcb_hasDeriv_varrho y v hρ
  have h2 := hA.comp_of_eq (0 : ℝ) hϱ (by simp)
  have hcont : ContinuousAt (fun s : ℝ => ϱ (y + s • v)) 0 := by
    have : Continuous fun s : ℝ => ϱ (y + s • v) := continuous_ϱ.comp (by fun_prop)
    exact this.continuousAt
  have hev : ∀ᶠ s in nhds (0 : ℝ), a < ϱ (y + s • v) :=
    hcont.eventually (lt_mem_nhds (by simpa using hy))
  have heq : (fun s : ℝ => X (y + s • v) 2) =ᶠ[nhds 0]
      ((fun r : ℝ => X (!₂[r, 0, y 2]) 2) ∘ fun s : ℝ => ϱ (y + s • v)) := by
    filter_upwards [hev] with s hs
    rw [H.rep2 _ hs]
    have : meridPt (y + s • v) = !₂[ϱ (y + s • v), 0, y 2] := by
      unfold meridPt
      simp [hv2]
    simp only [Function.comp]
    rw [this]
  have h3 := h1.unique (h2.congr_of_eventuallyEq heq)
  have hlin : fderiv ℝ (fun y => X y 2) y v =
      y 0 * fderiv ℝ (fun y => X y 2) y (coordinateVector 0) +
        y 1 * fderiv ℝ (fun y => X y 2) y (coordinateVector 1) := by
    rw [hv, map_add, map_smul, map_smul]
    simp
  rw [← hlin, h3, hv0, hv1, tcl_sqsum hρ]
  field_simp


theorem tcl_varrho_e2 (y : Space) (s : ℝ) : ϱ (y + s • (coordinateVector 2 : Space)) = ϱ y := by
  simp [ϱ, coordinateVector]

/-- (R2) the vertical derivative of the radial component at `y` equals that at the trace point. -/
theorem AxiC2.r2 (H : AxiC2 X a) {y : Space} (hy : a < ϱ y) :
    y 0 * fderiv ℝ (fun y => X y 0) y (coordinateVector 2) +
      y 1 * fderiv ℝ (fun y => X y 1) y (coordinateVector 2) =
      ϱ y * fderiv ℝ (fun y => X y 0) (meridPt y) (coordinateVector 2) := by
  have hρ : 0 < ϱ y := lt_of_le_of_lt H.ha hy
  have h0 : HasDerivAt (fun s : ℝ => X (y + s • (coordinateVector 2 : Space)) 0)
      (fderiv ℝ (fun y => X y 0) y (coordinateVector 2)) 0 := by
    have := tcl_line (f := fun y => X y 0) (q := y) (coordinateVector 2) 0
      (by simpa using H.dc 0 hy)
    simpa using this
  have h1 : HasDerivAt (fun s : ℝ => X (y + s • (coordinateVector 2 : Space)) 1)
      (fderiv ℝ (fun y => X y 1) y (coordinateVector 2)) 0 := by
    have := tcl_line (f := fun y => X y 1) (q := y) (coordinateVector 2) 0
      (by simpa using H.dc 1 hy)
    simpa using this
  have hS := (h0.const_mul (y 0)).fun_add (h1.const_mul (y 1))
  have hB : HasDerivAt (fun z' : ℝ => X (!₂[ϱ y, 0, z']) 0)
      (fderiv ℝ (fun y => X y 0) (meridPt y) (coordinateVector 2)) (y 2) :=
    tcl_hasDeriv_z (f := fun y => X y 0) (z := y 2) (ρ := ϱ y) (H.dc 0 (H.pt (ρ := ϱ y) (y 2) hy))
  have h3 : HasDerivAt (fun s : ℝ => y 2 + s) 1 0 := by
    simpa using (hasDerivAt_id (0 : ℝ)).const_add (y 2)
  have hB2 := (hB.comp_of_eq (0 : ℝ) h3 (by simp)).const_mul (ϱ y)
  have heq : (fun s : ℝ => y 0 * X (y + s • (coordinateVector 2 : Space)) 0 +
      y 1 * X (y + s • (coordinateVector 2 : Space)) 1) =
      fun s => ϱ y * ((fun z' : ℝ => X (!₂[ϱ y, 0, z']) 0) ∘ fun s : ℝ => y 2 + s) s := by
    funext s
    have hs : a < ϱ (y + s • (coordinateVector 2 : Space)) := by rw [tcl_varrho_e2]; exact hy
    rw [H.rep0 _ hs, H.rep1 _ hs, tcl_varrho_e2]
    have hm : meridPt (y + s • (coordinateVector 2 : Space)) = !₂[ϱ y, 0, y 2 + s] := by
      unfold meridPt
      rw [tcl_varrho_e2]
      simp [coordinateVector]
    rw [hm]
    simp only [Function.comp]
    have e0 : (y + s • (coordinateVector 2 : Space)) 0 = y 0 := by simp [coordinateVector]
    have e1 : (y + s • (coordinateVector 2 : Space)) 1 = y 1 := by simp [coordinateVector]
    rw [e0, e1]
    rw [show ∀ B : ℝ, y 0 * (y 0 / ϱ y * B) + y 1 * (y 1 / ϱ y * B) =
      (y 0 * y 0 + y 1 * y 1) / ϱ y * B from fun B => by ring, tcl_sqsum hρ]
    field_simp
  rw [heq] at hS
  have := hS.unique hB2
  simp only [mul_one] at this
  exact this


theorem tcl_g_deriv {ρ : ℝ} (hρ : 0 < ρ) (s : ℝ) :
    HasDerivAt (fun t : ℝ => Real.sqrt (ρ ^ 2 + t ^ 2)) (s / Real.sqrt (ρ ^ 2 + s ^ 2)) s := by
  have h : HasDerivAt (fun t : ℝ => ρ ^ 2 + t ^ 2) (2 * s) s := by
    simpa using ((hasDerivAt_id s).pow 2).const_add (ρ ^ 2)
  have hne : ρ ^ 2 + s ^ 2 ≠ 0 := by positivity
  have := h.sqrt hne
  convert this using 1
  have : 0 < Real.sqrt (ρ ^ 2 + s ^ 2) := Real.sqrt_pos.2 (by positivity)
  field_simp

theorem tcl_g_zero {ρ : ℝ} (hρ : 0 < ρ) : Real.sqrt (ρ ^ 2 + 0 ^ 2) = ρ := by
  simp [Real.sqrt_sq hρ.le]

theorem tcl_g_ge {ρ : ℝ} (hρ : 0 < ρ) (t : ℝ) : ρ ≤ Real.sqrt (ρ ^ 2 + t ^ 2) := by
  calc ρ = Real.sqrt (ρ ^ 2) := (Real.sqrt_sq hρ.le).symm
    _ ≤ _ := Real.sqrt_le_sqrt (by nlinarith [sq_nonneg t])

theorem tcl_varrho_e1 (ρ z t : ℝ) :
    ϱ ((!₂[ρ, 0, z] : Space) + t • (coordinateVector 1 : Space)) = Real.sqrt (ρ ^ 2 + t ^ 2) := by
  simp [ϱ, coordinateVector]

theorem tcl_mer_e1 (ρ z t : ℝ) :
    meridPt ((!₂[ρ, 0, z] : Space) + t • (coordinateVector 1 : Space)) =
      !₂[Real.sqrt (ρ ^ 2 + t ^ 2), 0, z] := by
  unfold meridPt
  rw [tcl_varrho_e1]
  simp [coordinateVector]

/-- (i) the azimuthal second derivative of `X₂` on the half plane. -/
theorem AxiC2.i1 (H : AxiC2 X a) {ρ z : ℝ} (hρ : a < ρ) :
    sd2 (fun y => X y 2) 1 1 (!₂[ρ, 0, z]) =
      fderiv ℝ (fun y => X y 2) (!₂[ρ, 0, z]) (coordinateVector 0) / ρ := by
  have hρ0 : 0 < ρ := lt_of_le_of_lt H.ha hρ
  set p : Space := !₂[ρ, 0, z] with hp
  set g : ℝ → ℝ := fun t => Real.sqrt (ρ ^ 2 + t ^ 2) with hg
  have hgreg : ∀ t, a < g t := fun t => lt_of_lt_of_le hρ (tcl_g_ge hρ0 t)
  set A : ℝ → ℝ := fun r => X (!₂[r, 0, z]) 2 with hAdef
  set Ar : ℝ → ℝ := fun r => fderiv ℝ (fun y => X y 2) (!₂[r, 0, z]) (coordinateVector 0)
    with hArdef
  have hA : ∀ r, a < r → HasDerivAt A (Ar r) r := fun r hr =>
    tcl_hasDeriv_rho (f := fun y => X y 2) (H.dc 2 (H.pt z hr))
  have hφ : (fun t : ℝ => X (p + t • (coordinateVector 1 : Space)) 2) = A ∘ g := by
    funext t
    have hreg : a < ϱ (p + t • (coordinateVector 1 : Space)) := by
      rw [hp, tcl_varrho_e1]; exact hgreg t
    rw [H.rep2 _ hreg, hp, tcl_mer_e1]
    rfl
  have hψ : ∀ s : ℝ, fderiv ℝ (fun y => X y 2) (p + s • (coordinateVector 1 : Space))
      (coordinateVector 1) = Ar (g s) * (s / g s) := by
    intro s
    have hreg : a < ϱ (p + s • (coordinateVector 1 : Space)) := by
      rw [hp, tcl_varrho_e1]; exact hgreg s
    have h1 := tcl_line (f := fun y => X y 2) (q := p) (coordinateVector 1) s (H.dc 2 hreg)
    rw [hφ] at h1
    have h2 := (hA (g s) (hgreg s)).comp s (tcl_g_deriv hρ0 s)
    exact h1.unique h2
  have hd1 := tcl_sd_line (f := fun y => X y 2) (y := p) (H.cdc 2 (by rw [hp]; exact H.pt z hρ))
    (coordinateVector 1) (coordinateVector 1)
  have hd1' : HasDerivAt (fun s : ℝ => Ar (g s) * (s / g s))
      (sd2 (fun y => X y 2) 1 1 p) 0 := by
    have : (fun s : ℝ => Ar (g s) * (s / g s)) =
        fun s : ℝ => fderiv ℝ (fun y => X y 2) (p + s • (coordinateVector 1 : Space))
          (coordinateVector 1) := by
      funext s; rw [hψ]
    rw [this]; exact hd1
  have hAr : HasDerivAt Ar (fderiv ℝ (fun y' => fderiv ℝ (fun y => X y 2) y'
      (coordinateVector 0)) p (coordinateVector 0)) ρ := by
    have hdiff : DifferentiableAt ℝ (fun y' => fderiv ℝ (fun y => X y 2) y' (coordinateVector 0)) p :=
      (((H.cdc 2 (by rw [hp]; exact H.pt z hρ)).fderiv_right (m := 1) (by norm_num)).clm_apply
        contDiffAt_const).differentiableAt (by norm_num)
    exact tcl_hasDeriv_rho (f := fun y' => fderiv ℝ (fun y => X y 2) y' (coordinateVector 0)) hdiff
  have hg0 : g 0 = ρ := tcl_g_zero hρ0
  have hc := hAr.comp_of_eq (0 : ℝ) (tcl_g_deriv hρ0 0) hg0.symm
  have hq := ((hasDerivAt_id (0 : ℝ)).div (tcl_g_deriv hρ0 0) (by rw [tcl_g_zero hρ0]; exact hρ0.ne'))
  have hm := hc.mul hq
  have := hd1'.unique hm
  rw [this]
  simp only [Function.comp, id, hg0] at *
  simp
  field_simp
  rw [Real.sqrt_sq hρ0.le]


/-- (A1) `∂_φ X_φ = X_r / ρ` on the half plane. -/
theorem AxiC2.a1 (H : AxiC2 X a) {ρ z : ℝ} (hρ : a < ρ) :
    fderiv ℝ (fun y => X y 1) (!₂[ρ, 0, z]) (coordinateVector 1) =
      X (!₂[ρ, 0, z]) 0 / ρ := by
  have hρ0 : 0 < ρ := lt_of_le_of_lt H.ha hρ
  set p : Space := !₂[ρ, 0, z] with hp
  set g : ℝ → ℝ := fun t => Real.sqrt (ρ ^ 2 + t ^ 2) with hg
  have hgreg : ∀ t, a < g t := fun t => lt_of_lt_of_le hρ (tcl_g_ge hρ0 t)
  set B : ℝ → ℝ := fun r => X (!₂[r, 0, z]) 0 with hBdef
  have hB : HasDerivAt B (fderiv ℝ (fun y => X y 0) p (coordinateVector 0)) ρ :=
    tcl_hasDeriv_rho (f := fun y => X y 0) (H.dc 0 (H.pt z hρ))
  have h1 := tcl_line (f := fun y => X y 1) (q := p) (coordinateVector 1) 0
    (by simpa using H.dc 1 (H.pt z hρ))
  simp only [zero_smul, add_zero] at h1
  have hc := hB.comp_of_eq (0 : ℝ) (tcl_g_deriv hρ0 0) (tcl_g_zero hρ0).symm
  have hq := ((hasDerivAt_id (0 : ℝ)).div (tcl_g_deriv hρ0 0)
    (by rw [tcl_g_zero hρ0]; exact hρ0.ne'))
  have hm := hq.mul hc
  have heq : (fun t : ℝ => X (p + t • (coordinateVector 1 : Space)) 1) =
      (id / fun t => Real.sqrt (ρ ^ 2 + t ^ 2)) * (B ∘ fun t => Real.sqrt (ρ ^ 2 + t ^ 2)) := by
    funext t
    have hreg : a < ϱ (p + t • (coordinateVector 1 : Space)) := by
      rw [hp, tcl_varrho_e1]; exact hgreg t
    rw [H.rep1 _ hreg, hp, tcl_varrho_e1, tcl_mer_e1]
    simp [coordinateVector]
    left
    rfl
  rw [heq] at h1
  have := h1.unique hm
  rw [this]
  simp only [Function.comp, id, Pi.div_apply, Pi.mul_apply]
  rw [tcl_g_zero hρ0]
  simp
  field_simp
  rfl

/-- (iii) the vertical derivative of `∂_φ X_φ`. -/
theorem AxiC2.i3 (H : AxiC2 X a) {ρ z : ℝ} (hρ : a < ρ) :
    sd2 (fun y => X y 1) 2 1 (!₂[ρ, 0, z]) =
      fderiv ℝ (fun y => X y 0) (!₂[ρ, 0, z]) (coordinateVector 2) / ρ := by
  have hρ0 : 0 < ρ := lt_of_le_of_lt H.ha hρ
  set p : Space := !₂[ρ, 0, z] with hp
  have hd1 := tcl_sd_line (f := fun y => X y 1) (y := p) (H.cdc 1 (H.pt z hρ))
    (coordinateVector 2) (coordinateVector 1)
  have hpath : ∀ s : ℝ, p + s • (coordinateVector 2 : Space) = !₂[ρ, 0, z + s] := by
    intro s
    ext i
    fin_cases i <;> simp [hp, coordinateVector]
  have heq : (fun s : ℝ => fderiv ℝ (fun y => X y 1) (p + s • (coordinateVector 2 : Space))
      (coordinateVector 1)) = fun s => X (p + s • (coordinateVector 2 : Space)) 0 / ρ := by
    funext s
    rw [hpath s]
    exact H.a1 hρ
  rw [heq] at hd1
  have h2 := tcl_line (f := fun y => X y 0) (q := p) (coordinateVector 2) 0
    (by simpa using H.dc 0 (H.pt z hρ))
  simp only [zero_smul, add_zero] at h2
  have h3 := h2.div_const ρ
  exact hd1.unique h3

theorem tcl_sd_symm {f : Space → ℝ} {y : Space} (hf : ContDiffAt ℝ 2 f y) (j l : Fin 3) :
    sd2 f j l y = sd2 f l j y := by
  have hd : DifferentiableAt ℝ (fderiv ℝ f) y :=
    (hf.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have key : ∀ v w : Space, fderiv ℝ (fun y' => fderiv ℝ f y' w) y v = fderiv ℝ (fderiv ℝ f) y v w := by
    intro v w
    rw [fderiv_clm_apply hd (differentiableAt_const w)]
    simp
  have hs := hf.isSymmSndFDerivAt (by simp [minSmoothness])
  unfold sd2
  rw [key, key]
  exact hs _ _

/-- (ii) the vertical derivative of the divergence. -/
theorem AxiC2.i2 (H : AxiC2 X a) {y : Space} (hy : a < ϱ y) :
    ∑ j : Fin 3, sd2 (fun y => X y j) 2 j y = 0 := by
  have hU : IsOpen {y : Space | a < ϱ y} := isOpen_lt continuous_const continuous_ϱ
  set S : Space → ℝ := fun y' => ∑ j : Fin 3, fderiv ℝ (fun y => X y j) y' (coordinateVector j)
    with hS
  have heq : S =ᶠ[nhds y] fun _ => (0 : ℝ) := by
    filter_upwards [hU.mem_nhds hy] with y' hy'
    have hdiff : DifferentiableAt ℝ X y' := (H.cd hy').differentiableAt (by norm_num)
    have := H.div y' hy'
    rw [← this]
    refine Finset.sum_congr rfl fun j _ => ?_
    unfold physPd
    rw [fderiv_apply_coord _ _ _ _ hdiff]
  have h0 : fderiv ℝ S y = 0 := by
    rw [heq.fderiv_eq]; simp
  have hdj : ∀ j ∈ (Finset.univ : Finset (Fin 3)), DifferentiableAt ℝ
      (fun y' => fderiv ℝ (fun y => X y j) y' (coordinateVector j)) y := fun j _ =>
    (((H.cdc j hy).fderiv_right (m := 1) (by norm_num)).clm_apply
      contDiffAt_const).differentiableAt (by norm_num)
  have h1 : fderiv ℝ S y = ∑ j : Fin 3, fderiv ℝ
      (fun y' => fderiv ℝ (fun y => X y j) y' (coordinateVector j)) y := by
    rw [hS]
    exact fderiv_fun_sum hdj
  have h2 := congrArg (fun L : Space →L[ℝ] ℝ => L (coordinateVector 2)) h0
  simp only [h1, ContinuousLinearMap.sum_apply] at h2
  simpa [sd2] using h2

end UnforcedLeray.Short.PartIIIb.Concrete
