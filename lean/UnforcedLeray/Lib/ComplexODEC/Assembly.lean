import UnforcedLeray.Lib.ComplexODEC.Bounds
import UnforcedLeray.Lib.PlanarSectorsB

/-!
# Membership, eigenvalue equations and zero circulation of the mode (INF18 O15 inputs)

Scoping note `scoping/INF10-INF12-INF18-Planar.md` §5 target O15; manuscript `paper/main.tex`
lines 962--982 (Proposition `prop:gaussian-existence`, unit B0058) and 1168--1192 (units
B0054--B0057).

* `memLp_modeVort_profile`, `memLp_modeVort_XG`, `memLp_modeQ_wMeasure`: `h ∈ L²(⟨r⟩^{2M} r dr)`
  for every `M`, `h ∈ X_G`, `q ∈ L²_M` for every `M` (tex lines 977--978, 1177--1178).
* `integral_modeQ`: `∫ q = 0` (zero circulation, tex line 1187), by `q(iy) = -q(y)`.
* `Lsec_modeVort`, `L0_modeVort`: `𝓛₂ h = λ h` on every `L²_M` profile space and
  `L₀ h = λ h` on `X_G`, `λ = -2ic` (tex lines 1188--1189, eq. `st18-t00006`).
* `Lsec_conj_modeVort`: the conjugate profile is a sector `-2` eigenvector with eigenvalue
  `λ̄` (tex lines 979--980, 1190--1191).
* `modeRadial_rayleigh`: `(Ω - c) Δ₂ φ - k φ = 0` on `(0, ∞)` (tex line 966).
-/

set_option autoImplicit false

noncomputable section
open Set Filter Topology MeasureTheory
open scoped ContDiff ComplexConjugate

namespace UnforcedLeray.ComplexODEC

open UnforcedLeray.GaussianVortex UnforcedLeray.Rayleigh UnforcedLeray.Sturm

variable {c : ℂ} {F : ℝ → ℂ}

/-! ### The radial equation -/

theorem contDiffOn_modeRadial (hF : WholeLineData c F) : ContDiffOn ℝ ∞ (modeRadial F) (Ioi 0) :=
  hF.smooth.comp_contDiffOn (Real.contDiffOn_log.mono fun _ hs => ne_of_gt hs)

/-- `(Ω - c) Δ₂ φ - k φ = 0` on `(0, ∞)` (tex line 966, eq. `st18-t00039` in radius). -/
theorem modeRadial_rayleigh (hF : WholeLineData c F) {r : ℝ} (hr : 0 < r) :
    ((radialOmega r : ℂ) - c) * B0034.radialDelta2 (modeRadial F) r -
      (radialK r : ℂ) * modeRadial F r = 0 :=
  B0034.radial_equation_of_log (F' := deriv F) (F'' := deriv (deriv F))
    (fun t => (hF.differentiable t).hasDerivAt) (fun t => (hF.differentiable_deriv t).hasDerivAt)
    hr (hF.mode.equation (Real.log r))

/-- `h (Ω - c) = k φ` (tex eq. `st18-t00046`). -/
theorem modeVort_mul (hF : WholeLineData c F) (r : ℝ) :
    modeVort c F r * ((radialOmega r : ℂ) - c) = (radialK r : ℂ) * modeRadial F r := by
  rw [modeVort_eq]
  have := ofReal_sub_ne_zero hF.im_ne_zero (radialOmega r)
  field_simp

/-! ### Memberships -/

/-- `‖h(r)‖ ≤ (M/|Im c|) |k(r)|` for `‖F‖ ≤ M`. -/
theorem norm_modeVort_le_radialK (hF : WholeLineData c F) {M : ℝ} (hM0 : 0 ≤ M)
    (hM : ∀ t, ‖F t‖ ≤ M) (r : ℝ) :
    ‖modeVort c F r‖ ≤ M / |c.im| * ‖(radialK r : ℂ)‖ := by
  have hc := hF.im_ne_zero
  have hpos : 0 < |c.im| := abs_pos.mpr hc
  rw [modeVort_eq, norm_div, norm_mul, div_le_iff₀ (lt_of_lt_of_le hpos
    (abs_im_le_norm_ofReal_sub c _))]
  have h1 := abs_im_le_norm_ofReal_sub c (radialOmega r)
  have h2 := hM (Real.log r)
  calc ‖(radialK r : ℂ)‖ * ‖modeRadial F r‖ ≤ ‖(radialK r : ℂ)‖ * M :=
        mul_le_mul_of_nonneg_left h2 (norm_nonneg _)
    _ = M / |c.im| * ‖(radialK r : ℂ)‖ * |c.im| := by field_simp
    _ ≤ M / |c.im| * ‖(radialK r : ℂ)‖ * ‖(radialOmega r : ℂ) - c‖ := by gcongr

theorem continuous_radialK_c : Continuous fun r : ℝ => (radialK r : ℂ) :=
  Complex.continuous_ofReal.comp B0012.continuous_radialK

theorem aestronglyMeasurable_modeVort (hF : WholeLineData c F) :
    AEStronglyMeasurable (modeVort c F) (volume.restrict (Ioi 0)) :=
  (continuousOn_modeVort hF).aestronglyMeasurable measurableSet_Ioi

/-- `h ∈ L²(⟨r⟩^{2M} 2π r dr)` for every `M` (tex lines 977--978). -/
theorem memLp_modeVort_profile (hF : WholeLineData c F) (M : ℝ) :
    MemLp (modeVort c F) 2 (Planar.profileMeasure M) := by
  obtain ⟨B, hB0, hB⟩ := hF.exists_bound
  refine (Planar.memLp_radialK_profile M).of_le_mul
    ((Planar.aestronglyMeasurable_profileMeasure_iff M).2 (aestronglyMeasurable_modeVort hF))
    (Eventually.of_forall fun r => norm_modeVort_le_radialK hF hB0 hB r)

/-- `h ∈ X_G` (tex lines 977--978, 1177--1178). -/
theorem memLp_modeVort_XG (hF : WholeLineData c F) : MemLp (modeVort c F) 2 B0010.xGMeasure := by
  obtain ⟨B, hB0, hB⟩ := hF.exists_bound
  exact B0012.memLp_k.of_le_mul
    ((aestronglyMeasurable_modeVort hF).mono_ac B0012.xG_ac)
    (Eventually.of_forall fun r => norm_modeVort_le_radialK hF hB0 hB r)

/-- `q ∈ L²_M` for every `M` (tex line 977). -/
theorem memLp_modeQ_wMeasure (hF : WholeLineData c F) (M : ℝ) :
    MemLp (modeQ c F) 2 (Planar.wMeasure M) :=
  (Planar.memLp_ofProfile_iff M 2
    ((Planar.aestronglyMeasurable_profileMeasure_iff M).2 (aestronglyMeasurable_modeVort hF))).2
    (memLp_modeVort_profile hF M)

/-- `q` is integrable on `ℝ²` (`L²_M ⊂ L¹` for `M > 1`, tex lines 657--660), so `∫ q` below is
a genuine integral. -/
theorem integrable_modeQ (hF : WholeLineData c F) : Integrable (modeQ c F) volume := by
  have hM : (1 : ℝ) < 2 := by norm_num
  have h := Planar.integrable_L2w hM ((memLp_modeQ_wMeasure hF 2).toLp (modeQ c F))
  exact h.congr ((Planar.volume_ac 2).ae_le (memLp_modeQ_wMeasure hF 2).coeFn_toLp)

/-! ### Zero circulation -/

theorem modeQ_mul_I (hF : WholeLineData c F) (y : ℂ) :
    modeQ c F (Complex.I * y) = -modeQ c F y := by
  obtain ⟨β₀, -, hβ⟩ := exists_mode_eq_regLog hF
  rw [modeQ_eq (fun t => (hβ t).1), modeQ_eq (fun t => (hβ t).1), norm_mul, Complex.norm_I,
    one_mul, mul_pow, Complex.I_sq]
  ring

/-- **Zero circulation** `∫ q = 0` (tex line 1187). -/
theorem integral_modeQ (hF : WholeLineData c F) : ∫ y, modeQ c F y = 0 := by
  have hmp := Planar.NUE.Polar.measurePreserving_rot (Real.pi / 2)
  have hemb : MeasurableEmbedding (Planar.NUE.rot (Real.pi / 2)) := by
    rw [Planar.NUE.Polar.rot_eq_rotation]
    exact (rotation (Circle.exp (Real.pi / 2))).toHomeomorph.measurableEmbedding
  have hrot : ∀ y, Planar.NUE.rot (Real.pi / 2) y = Complex.I * y := fun y => by
    rw [Planar.NUE.rot]
    congr 1
    have : ((Real.pi / 2 : ℝ) : ℂ) * Complex.I = Real.pi / 2 * Complex.I := by push_cast; ring
    rw [this, Complex.exp_pi_div_two_mul_I]
  have h := hmp.integral_comp hemb (modeQ c F)
  simp only [hrot, modeQ_mul_I hF, integral_neg] at h
  have : (2 : ℂ) * ∫ y, modeQ c F y = 0 := by linear_combination -h
  simpa using this

/-! ### Eigenvalue equations -/

theorem greenN_congr_ae {n : ℕ} {g₁ g₂ : ℝ → ℂ}
    (h : g₁ =ᵐ[volume.restrict (Ioi (0 : ℝ))] g₂) (r : ℝ) :
    Planar.greenN n g₁ r = Planar.greenN n g₂ r := by
  unfold Planar.greenN
  congr 1
  refine integral_congr_ae ?_
  filter_upwards [h] with ρ hρ
  rw [hρ]

/-- The mode identity `-2iΩh + 2ikφ = λ h`, `λ = -2ic` (tex line 1188). -/
theorem modeVort_identity (hF : WholeLineData c F) (r : ℝ) :
    -(Complex.I * 2) * (radialOmega r : ℂ) * modeVort c F r +
      Complex.I * 2 * (radialK r : ℂ) * modeRadial F r = (-2 * Complex.I * c) * modeVort c F r := by
  have := modeVort_mul hF r
  linear_combination (-(2 * Complex.I)) * this

/-- **Sector eigenvector** (tex lines 1188--1189): on every profile space `L²_M`, `M > 1`,
`𝓛₂ h = λ h` with `λ = -2ic`. -/
theorem Lsec_modeVort (hF : WholeLineData c F) {M : ℝ} (hM : 1 < M) :
    Planar.Lsec hM 2 ((memLp_modeVort_profile hF M).toLp (modeVort c F)) =
      (-2 * Complex.I * c) • (memLp_modeVort_profile hF M).toLp (modeVort c F) := by
  set w := (memLp_modeVort_profile hF M).toLp (modeVort c F)
  have hw : ⇑w =ᵐ[Planar.profileMeasure M] modeVort c F := MemLp.coeFn_toLp _
  have hgreen : ∀ r, Planar.greenN 2 w r = Planar.greenN 2 (modeVort c F) r :=
    greenN_congr_ae ((Planar.ac_profileMeasure M).ae_le hw)
  refine Lp.ext ?_
  filter_upwards [Planar.coeFn_Lsec hM 2 w, Lp.coeFn_smul (-2 * Complex.I * c) w, hw,
    Planar.ae_profile_pos M] with r h1 h2 h3 hr
  rw [h1, h2, Pi.smul_apply, h3, smul_eq_mul]
  have e : ((2 : ℤ).natAbs) = 2 := rfl
  rw [e, hgreen, ← mode_eq_green hF r hr]
  push_cast
  exact modeVort_identity hF r

/-- **`L₀ q = λ q` on `X_G`** (tex lines 1188--1189, eq. `st18-t00006`). -/
theorem L0_modeVort (hF : WholeLineData c F) :
    Planar.L0 ((memLp_modeVort_XG hF).toLp (modeVort c F)) =
      (-2 * Complex.I * c) • (memLp_modeVort_XG hF).toLp (modeVort c F) := by
  set w := (memLp_modeVort_XG hF).toLp (modeVort c F)
  have hw : ⇑w =ᵐ[B0010.xGMeasure] modeVort c F := MemLp.coeFn_toLp _
  have hgreen : ∀ r, Planar.greenN 2 w r = Planar.greenN 2 (modeVort c F) r :=
    greenN_congr_ae (B0012.restrict_ac.ae_le hw)
  refine Lp.ext ?_
  filter_upwards [Planar.coeFn_L0 w, Lp.coeFn_smul (-2 * Complex.I * c) w, hw,
    B0012.ae_xG_pos] with r h1 h2 h3 hr
  rw [h1, h2, Pi.smul_apply, h3, smul_eq_mul, hgreen, ← mode_eq_green hF r hr]
  have := modeVort_identity hF r
  linear_combination this

/-- The conjugate profile `h̄` lies in every profile space. -/
theorem memLp_conj_modeVort_profile (hF : WholeLineData c F) (M : ℝ) :
    MemLp (fun r => conj (modeVort c F r)) 2 (Planar.profileMeasure M) :=
  (memLp_modeVort_profile hF M).of_le
    (Complex.continuous_conj.comp_aestronglyMeasurable
      (memLp_modeVort_profile hF M).aestronglyMeasurable)
    (Eventually.of_forall fun r => by rw [Complex.norm_conj])

theorem greenN_conj (n : ℕ) (g : ℝ → ℂ) (r : ℝ) :
    Planar.greenN n (fun ρ => conj (g ρ)) r = conj (Planar.greenN n g r) := by
  unfold Planar.greenN
  rw [map_mul, ← integral_conj]
  congr 1
  · rw [map_neg, Complex.conj_ofReal]
  · refine integral_congr_ae (Eventually.of_forall fun ρ => ?_)
    simp

/-- **The conjugate mode** (tex lines 979--980, 1190--1191): `h̄` is a sector `-2` eigenvector
with eigenvalue `λ̄`. -/
theorem Lsec_conj_modeVort (hF : WholeLineData c F) {M : ℝ} (hM : 1 < M) :
    Planar.Lsec hM (-2) ((memLp_conj_modeVort_profile hF M).toLp _) =
      conj (-2 * Complex.I * c) • (memLp_conj_modeVort_profile hF M).toLp _ := by
  set w := (memLp_conj_modeVort_profile hF M).toLp (fun r => conj (modeVort c F r))
  have hw : ⇑w =ᵐ[Planar.profileMeasure M] fun r => conj (modeVort c F r) := MemLp.coeFn_toLp _
  have hgreen : ∀ r, Planar.greenN 2 w r = conj (Planar.greenN 2 (modeVort c F) r) := fun r => by
    rw [greenN_congr_ae ((Planar.ac_profileMeasure M).ae_le hw), greenN_conj]
  refine Lp.ext ?_
  filter_upwards [Planar.coeFn_Lsec hM (-2) w, Lp.coeFn_smul (conj (-2 * Complex.I * c)) w, hw,
    Planar.ae_profile_pos M] with r h1 h2 h3 hr
  rw [h1, h2, Pi.smul_apply, h3, smul_eq_mul]
  have e : ((-2 : ℤ).natAbs) = 2 := rfl
  rw [e, hgreen, ← mode_eq_green hF r hr]
  have hid := congrArg conj (modeVort_identity hF r)
  simp only [map_mul, map_add, map_neg, Complex.conj_I, Complex.conj_ofReal, map_ofNat] at hid
  simp only [map_mul, map_neg, Complex.conj_I, map_ofNat]
  push_cast
  linear_combination hid

/-! ### Nonvanishing -/

theorem exists_modeVort_ne_zero (hF : WholeLineData c F) : ∃ r > 0, modeVort c F r ≠ 0 := by
  by_contra hcon
  push Not at hcon
  obtain ⟨t, ht⟩ := hF.mode.nonzero
  apply ht
  have hr : (0 : ℝ) < Real.exp t := Real.exp_pos t
  have h0 : modeVort c F =ᵐ[volume.restrict (Ioi (0 : ℝ))] fun _ => 0 := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with ρ hρ
    exact hcon ρ hρ
  have := mode_eq_green hF (Real.exp t) hr
  rw [greenN_congr_ae h0] at this
  simp only [Planar.greenN, mul_zero] at this
  simpa [modeRadial, Real.log_exp] using this

theorem modeQ_ofReal (r : ℝ) (hr : 0 < r) : modeQ c F (r : ℂ) = modeVort c F r := by
  have hr' : (r : ℂ) ≠ 0 := by exact_mod_cast hr.ne'
  simp [modeQ, Planar.NUE.Ang.ofProfile, Planar.NUE.Ang.angPhase, Complex.norm_real,
    abs_of_pos hr, hr']

theorem modeQ_ne_zero (hF : WholeLineData c F) : modeQ c F ≠ 0 := by
  obtain ⟨r, hr, hne⟩ := exists_modeVort_ne_zero hF
  intro h
  apply hne
  rw [← modeQ_ofReal r hr, h, Pi.zero_apply]

end UnforcedLeray.ComplexODEC
