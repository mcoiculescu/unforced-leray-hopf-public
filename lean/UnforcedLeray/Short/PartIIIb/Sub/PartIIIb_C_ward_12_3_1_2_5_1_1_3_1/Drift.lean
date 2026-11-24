import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_ward_12_3_1_2_5_1_1_3_1.FarOrg
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_ward_12_3_1.GradEq.GEQuadSub.GEQMem.Ddu
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_ward_12_3_1_2_5_1_1_2

/-!
# `InletDriftFar`: exact drift cancellation of the inlet in the far field

Source `the November 2 reference manuscript`
lines 2542-2549 (far field), 1206-1222 (lift).

For `ϱ > R₀ := 2R/√H` the age cutoff is one on `s < H/4`, so the profile is `s`-independent
there (`inletProfile_form`, `inletProfile_indep`).  The lift scales as
`E(τ + 2 log λ, y) = λ E(τ, λy)` for `λ` near one (`inlet_scale`, `Efun_scale`); differentiating at
`λ = 1` gives `2 ∂_τE = E + y·∇E`, i.e. `∂_τE - ½ y·∇E - ½E = 0`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology
open scoped ContDiff
open UnforcedLeray.Cons.C03.Concrete (Params)

namespace UnforcedLeray.Short.PartIIIb.Concrete

/-! ## Elementary scaling identities of the ring chart -/

theorem varrho_smul' {y : UnforcedLeray.Space} {l : ℝ} (hl : 0 < l) :
    Axi.ϱ (l • y) = l * Axi.ϱ y := by
  unfold Axi.ϱ
  have h : (l • y) 0 ^ 2 + (l • y) 1 ^ 2 = l ^ 2 * (y 0 ^ 2 + y 1 ^ 2) := by
    simp only [PiLp.smul_apply, smul_eq_mul]
    ring
  rw [h, Real.sqrt_mul (by positivity), Real.sqrt_sq hl.le]

theorem age_smul' {R : ℝ} {y : UnforcedLeray.Space} {l : ℝ} (hl : 0 < l)
    (hy : 0 < Axi.ϱ y) :
    Axi.age R (l • y) = Axi.age R y / l ^ 2 := by
  unfold Axi.age
  rw [varrho_smul' hl]
  have h1 : Axi.ϱ y ≠ 0 := hy.ne'
  have h2 : l ≠ 0 := hl.ne'
  field_simp

theorem trans_smul' {R : ℝ} {y : UnforcedLeray.Space} {l : ℝ} (hl : 0 < l)
    (hy : 0 < Axi.ϱ y) :
    Axi.trans R (l • y) = Axi.trans R y := by
  unfold Axi.trans
  rw [varrho_smul' hl]
  simp only [PiLp.smul_apply, smul_eq_mul]
  have h1 : Axi.ϱ y ≠ 0 := hy.ne'
  have h2 : l ≠ 0 := hl.ne'
  field_simp

theorem phase_smul' {R τ : ℝ} {y : UnforcedLeray.Space} {l : ℝ} (hR : 0 < R) (hl : 0 < l)
    (hy : 0 < Axi.ϱ y) :
    Axi.phase R (τ + 2 * Real.log l) y = Axi.phase R τ (l • y) := by
  unfold Axi.phase
  have hage : 0 < Axi.age R y := div_pos (pow_pos hR 2) (pow_pos hy 2)
  rw [age_smul' hl hy, Real.log_div hage.ne' (pow_ne_zero 2 hl.ne'), Real.log_pow]
  push_cast
  ring

theorem eR_smul' {y : UnforcedLeray.Space} {l : ℝ} (hl : 0 < l) :
    Axi.eR (l • y) = Axi.eR y := by
  ext k
  fin_cases k
  · simp only [Fin.zero_eta, Axi.eR_apply_zero, PiLp.smul_apply, smul_eq_mul, varrho_smul' hl]
    exact mul_div_mul_left _ _ hl.ne'
  · simp only [Fin.mk_one, Axi.eR_apply_one, PiLp.smul_apply, smul_eq_mul, varrho_smul' hl]
    exact mul_div_mul_left _ _ hl.ne'
  · simp

theorem frameL_smul' {y : UnforcedLeray.Space} {l : ℝ} (hl : 0 < l) :
    Axi.frameL (l • y) = Axi.frameL y := by
  ext1 v
  simp only [Axi.frameL_apply, eR_smul' hl]

theorem realC_smul_real (l : ℝ) (v : UnforcedLeray.Space) :
    UnforcedLeray.B0412.realC (l • v) = l • UnforcedLeray.B0412.realC v := by
  ext j
  simp [UnforcedLeray.B0412.realC_apply, Complex.real_smul]

/-! ## `s`-independence of the inlet profile below `H/4` -/

/-- Closed form of the inlet profile on `s < H/4` (where the age cutoff is one). -/
theorem inletProfile_form {p : Params} {i : Fin 2} (hψ : ContDiff ℝ ∞ (p.frozenStream i))
    (m : ℝ × (ℝ × ℝ)) (hm : m.1 < p.H / 4) :
    p.inletProfile i m =
      (-(fderiv ℝ (p.frozenStream i) m.2 (0, 1))) • UnforcedLeray.Axi.m0 +
        (fderiv ℝ (p.frozenStream i) m.2 (1, 0) + p.R⁻¹ *
          (p.frozenStream i m.2 - m.2.2 * fderiv ℝ (p.frozenStream i) m.2 (0, 1))) •
            UnforcedLeray.Axi.m1 := by
  have hχc : ContDiff ℝ ∞ (Cons.C03.Concrete.ageCutoff p.H) :=
    Cons.C03.Concrete.contDiff_ageCutoff p.H
  have hχ : DifferentiableAt ℝ (Cons.C03.Concrete.ageCutoff p.H) m.1 :=
    (hχc.differentiable (by simp)) m.1
  have hψd : DifferentiableAt ℝ (p.frozenStream i) m.2 := hψ.differentiable (by simp) m.2
  have hone : Cons.C03.Concrete.ageCutoff p.H m.1 = 1 :=
    Cons.C03.Concrete.ageCutoff_eq_one p.H_pos hm.le
  have hder : deriv (Cons.C03.Concrete.ageCutoff p.H) m.1 = 0 := by
    have hev : Cons.C03.Concrete.ageCutoff p.H =ᶠ[𝓝 m.1] fun _ => (1 : ℝ) := by
      filter_upwards [Iio_mem_nhds hm] with t ht
      exact Cons.C03.Concrete.ageCutoff_eq_one p.H_pos (Set.mem_Iio.1 ht).le
    rw [hev.deriv_eq]
    simp
  have hcut : p.cutStream i = fun n : ℝ × (ℝ × ℝ) =>
      Cons.C03.Concrete.ageCutoff p.H n.1 * p.frozenStream i n.2 := rfl
  unfold Params.inletProfile
  rw [hcut, UnforcedLeray.Axi.ringStreamProfile_cutoff p.R hχ hψd, hone, hder]
  simp

theorem inletProfile_indep {p : Params} {i : Fin 2} (hψ : ContDiff ℝ ∞ (p.frozenStream i))
    {s t : ℝ} (hs : s < p.H / 4) (ht : t < p.H / 4) (ξ η : ℝ) :
    p.inletProfile i (s, (ξ, η)) = p.inletProfile i (t, (ξ, η)) := by
  rw [inletProfile_form hψ (s, (ξ, η)) hs, inletProfile_form hψ (t, (ξ, η)) ht]

/-! ## The scaling identity of the lift -/

theorem inlet_scale (p : Params) (i : Fin 2) (τ : ℝ) {y : UnforcedLeray.Space} {l : ℝ}
    (hl : 0 < l) (hy : 0 < Axi.ϱ y)
    (hA : Axi.age p.R y < p.H / 4) (hB : Axi.age p.R (l • y) < p.H / 4)
    (hstep : ∀ s t : ℝ, s < p.H / 4 → t < p.H / 4 → ∀ ξ η : ℝ,
      p.inletProfile i (s, (ξ, η)) = p.inletProfile i (t, (ξ, η))) :
    p.inlet i (τ + 2 * Real.log l) y = l • p.inlet i τ (l • y) := by
  have hp := p.R_pos
  have hage : 0 < Axi.age p.R y := div_pos (pow_pos hp 2) (pow_pos hy 2)
  have hsq : Real.sqrt (Axi.age p.R (l • y)) = Real.sqrt (Axi.age p.R y) / l := by
    rw [age_smul' hl hy, Real.sqrt_div hage.le, Real.sqrt_sq hl.le]
  have hc1 : Axi.chart p.R (τ + 2 * Real.log l) y =
      (Axi.age p.R y, (Axi.phase p.R τ (l • y), Axi.trans p.R (l • y))) := by
    unfold Axi.chart
    rw [phase_smul' hp hl hy, trans_smul' hl hy]
  have hc2 : Axi.chart p.R τ (l • y) =
      (Axi.age p.R (l • y), (Axi.phase p.R τ (l • y), Axi.trans p.R (l • y))) := rfl
  have hprof : p.inletProfile i (Axi.chart p.R (τ + 2 * Real.log l) y) =
      p.inletProfile i (Axi.chart p.R τ (l • y)) := by
    rw [hc1, hc2]
    exact hstep _ _ hA hB _ _
  have hl0 : l ≠ 0 := hl.ne'
  unfold Params.inlet
  unfold UnforcedLeray.Axi.Nv
  rw [hprof, frameL_smul' hl, hsq, smul_smul]
  congr 1
  field_simp

theorem Efun_scale (p : Params) (i : Fin 2) (τ : ℝ) {y : UnforcedLeray.Space} {l : ℝ}
    (hl : 0 < l) (hy : 0 < Axi.ϱ y)
    (hA : Axi.age p.R y < p.H / 4) (hB : Axi.age p.R (l • y) < p.H / 4)
    (hstep : ∀ s t : ℝ, s < p.H / 4 → t < p.H / 4 → ∀ ξ η : ℝ,
      p.inletProfile i (s, (ξ, η)) = p.inletProfile i (t, (ξ, η))) :
    p.Efun i (τ + 2 * Real.log l, y) = l • p.Efun i (τ, l • y) := by
  show UnforcedLeray.B0412.realC (p.inlet i (τ + 2 * Real.log l) y) =
    l • UnforcedLeray.B0412.realC (p.inlet i τ (l • y))
  rw [inlet_scale p i τ hl hy hA hB hstep, realC_smul_real]

/-! ## The drift identity -/

/-- **Exact drift cancellation in the far field** (source 2542-2549). -/
theorem inletDriftFar : InletDriftFar := by
  intro lam q hq dm dp hdm
  refine ⟨1, one_pos, fun p d hreg hν hm z g hg => ?_⟩
  intro i
  have hp : 0 < p.R := p.R_pos
  have hH : 0 < p.H := p.H_pos
  have hνpos : 0 < p.ν := p.ν_pos
  have hc1 : 1 ≤ p.c := by
    rw [hreg.c_eq, one_le_inv₀ (by positivity)]
    nlinarith
  obtain ⟨C, κ, N, -, -, hper⟩ := UnforcedLeray.Short.IIb.frozenStreamBounds lam q hq 0
  have hfro : ContDiff ℝ ∞ (p.frozenStream i) :=
    UnforcedLeray.Short.IIb.inletCD_frozenStream (hper p.c hc1).1 hm i
  have hI := inlet_contDiff_joint lam q hq hreg hν hm i
  have hE : ContDiff ℝ ∞ (p.Efun i) := contDiff_realC_meas.comp hI
  have hEd : ∀ x, DifferentiableAt ℝ (p.Efun i) x := fun x => hE.differentiable (by simp) x
  refine ⟨2 * p.R / Real.sqrt p.H, div_pos (by linarith) (Real.sqrt_pos.2 hH), fun τ y hR0 => ?_⟩
  -- the far-field region
  have hR0pos : 0 < 2 * p.R / Real.sqrt p.H := div_pos (by linarith) (Real.sqrt_pos.2 hH)
  have hy : 0 < Axi.ϱ y := lt_trans hR0pos hR0
  have hsq : (2 * p.R / Real.sqrt p.H) ^ 2 * p.H = 4 * p.R ^ 2 := by
    rw [div_pow, mul_pow, Real.sq_sqrt hH.le]
    field_simp
    norm_num
  have hA : Axi.age p.R y < p.H / 4 := by
    unfold Axi.age
    rw [div_lt_iff₀ (pow_pos hy 2)]
    have hlt : (2 * p.R / Real.sqrt p.H) ^ 2 < Axi.ϱ y ^ 2 :=
      pow_lt_pow_left₀ hR0 hR0pos.le two_ne_zero
    nlinarith
  -- the eventual agreement near `λ = 1`
  have hev : ∀ᶠ l in 𝓝 (1 : ℝ), 0 < l ∧ Axi.age p.R (l • y) < p.H / 4 := by
    have h1 : ∀ᶠ l in 𝓝 (1 : ℝ), Axi.age p.R y / l ^ 2 < p.H / 4 := by
      have hc : ContinuousAt (fun l : ℝ => Axi.age p.R y / l ^ 2) 1 :=
        continuousAt_const.div (continuousAt_id.pow 2) (by norm_num)
      exact hc.eventually_lt continuousAt_const (by simpa using hA)
    have h2 : ∀ᶠ l in 𝓝 (1 : ℝ), 0 < l := Ioi_mem_nhds zero_lt_one
    filter_upwards [h1, h2] with l hl1 hl2
    exact ⟨hl2, by rw [age_smul' hl2 hy]; exact hl1⟩
  have hstep : ∀ s t : ℝ, s < p.H / 4 → t < p.H / 4 → ∀ ξ η : ℝ,
      p.inletProfile i (s, (ξ, η)) = p.inletProfile i (t, (ξ, η)) :=
    fun s t hs ht ξ η => inletProfile_indep hfro hs ht ξ η
  have hfg : (fun l : ℝ => p.Efun i (τ + 2 * Real.log l, y)) =ᶠ[𝓝 (1 : ℝ)]
      (fun l : ℝ => l • p.Efun i (τ, l • y)) := by
    filter_upwards [hev] with l hl
    exact Efun_scale p i τ hl.1 hy hA hl.2 hstep
  -- derivative of the left side at `λ = 1`
  have hlog : HasDerivAt (fun l : ℝ => τ + 2 * Real.log l) (2 * (1 : ℝ)⁻¹) 1 :=
    ((Real.hasDerivAt_log one_ne_zero).const_mul 2).const_add τ
  have hpair : HasDerivAt (fun l : ℝ => (τ + 2 * Real.log l, y))
      ((2 * (1 : ℝ)⁻¹, (0 : UnforcedLeray.Space))) 1 :=
    hlog.prodMk (hasDerivAt_const (1 : ℝ) y)
  have hpt : τ + 2 * Real.log 1 = τ := by simp
  have hEd' : HasFDerivAt (p.Efun i) (fderiv ℝ (p.Efun i) (τ, y))
      (τ + 2 * Real.log 1, y) := by
    rw [hpt]
    exact (hEd (τ, y)).hasFDerivAt
  have hf := hEd'.comp_hasDerivAt (1 : ℝ) hpair
  have hdτ : fderiv ℝ (p.Efun i) (τ, y) (2 * (1 : ℝ)⁻¹, (0 : UnforcedLeray.Space)) =
      (2 : ℝ) • UnforcedLeray.PhaseSpace.dτ (p.Efun i) (τ, y) := by
    rw [show ((2 : ℝ) * (1 : ℝ)⁻¹, (0 : UnforcedLeray.Space)) =
      (2 : ℝ) • ((1 : ℝ), (0 : UnforcedLeray.Space)) by simp, map_smul]
    rfl
  rw [hdτ] at hf
  -- derivative of the right side at `λ = 1`
  have hkd : DifferentiableAt ℝ (fun x : UnforcedLeray.Space => p.Efun i (τ, x)) y := by
    have h1 : DifferentiableAt ℝ (fun x : UnforcedLeray.Space => ((τ, x) : ℝ × UnforcedLeray.Space))
        y := (differentiableAt_const τ).prodMk differentiableAt_id
    exact (hEd (τ, y)).comp y h1
  have hline : HasDerivAt (fun l : ℝ => l • y) ((1 : ℝ) • y) 1 :=
    (hasDerivAt_id' (x := (1 : ℝ))).smul_const y
  have hkf : HasFDerivAt (fun x : UnforcedLeray.Space => p.Efun i (τ, x))
      (fderiv ℝ (fun x : UnforcedLeray.Space => p.Efun i (τ, x)) y) ((1 : ℝ) • y) := by
    rw [one_smul]
    exact hkd.hasFDerivAt
  have hgk := hkf.comp_hasDerivAt (1 : ℝ) hline
  have hgD := (hasDerivAt_id' (x := (1 : ℝ))).smul hgk
  -- the two derivatives agree
  have heq := hf.unique (hgD.congr_of_eventuallyEq hfg)
  simp only [one_smul, Function.comp_apply] at heq
  -- identify the spatial derivative with `radialT`
  have hkF : HasFDerivAt (fun x : UnforcedLeray.Space => p.Efun i (τ, x))
      ((fderiv ℝ (p.Efun i) (τ, y)).comp
        ((0 : UnforcedLeray.Space →L[ℝ] ℝ).prod (ContinuousLinearMap.id ℝ UnforcedLeray.Space)))
      y :=
    (hEd (τ, y)).hasFDerivAt.comp y ((hasFDerivAt_const τ y).prodMk (hasFDerivAt_id y))
  have hk_eq : fderiv ℝ (fun x : UnforcedLeray.Space => p.Efun i (τ, x)) y y =
      fderiv ℝ (p.Efun i) (τ, y) (0, y) := by
    rw [hkF.fderiv]
    simp
  have hy_sum : y = ∑ j : Fin 3, y j • UnforcedLeray.coordinateVector j := by
    ext k
    fin_cases k <;> simp [UnforcedLeray.coordinateVector, Fin.sum_univ_three]
  have hy_eq : ((0 : ℝ), y) = ∑ j : Fin 3, y j • ((0 : ℝ), UnforcedLeray.coordinateVector j) := by
    refine Prod.ext ?_ ?_
    · simp [Prod.fst_sum]
    · simp only [Prod.snd_sum, Prod.smul_snd]
      exact hy_sum
  have hrad : UnforcedLeray.PhaseSpace.radialT (p.Efun i) (τ, y) =
      fderiv ℝ (p.Efun i) (τ, y) (0, y) := by
    rw [hy_eq, map_sum]
    simp only [map_smul, UnforcedLeray.PhaseSpace.radialT, UnforcedLeray.PhaseSpace.dy]
  rw [hk_eq, ← hrad] at heq
  -- conclude
  have hdiv : UnforcedLeray.PhaseSpace.dτ (p.Efun i) (τ, y) =
      (1 / 2 : ℝ) • ((2 : ℝ) • UnforcedLeray.PhaseSpace.dτ (p.Efun i) (τ, y)) := by
    rw [smul_smul]
    norm_num
  rw [hdiv, heq]
  module

end UnforcedLeray.Short.PartIIIb.Concrete
