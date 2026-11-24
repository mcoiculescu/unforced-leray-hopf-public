import UnforcedLeray.Short.PartIIb.Sub.T12
import UnforcedLeray.Short.PartIIb.Tasks.FlatCausal.DuhamelMeasurable
import UnforcedLeray.Short.PartIIb.Tasks.FlatCausal.FlatHeatContraction
import UnforcedLeray.Units.B0284
import UnforcedLeray.Short.PartIIb.Org.QPeriodicHalfSpace.Basic

/-!
# Part II-b, task `PartII-b:T12/4` (`DuhamelBound`): the causal Duhamel operator on `H_r`

Source of record: `the November 2 reference manuscript`, SP 1923-1927 ("the causal
formula `T_0F(s) = ∫_0^s (t/s)^μ e^{ν(s-t)Δ} P_0F(t) dt/t` and weighted dilation give
`‖T_0‖_{H_r → H_r} ≤ C_r/a_r`").

Target: `duhamelBound : DuhamelBound` (`Sub/T12.lean`). For `1 < r < 3`, `a_r = Re μ + (3/r-1)/2 > 0`,
`ν, c > 0` and `G ∈ H_r`: `‖flatDuhamel ν μ G‖_{H_r} ≤ (1/a_r) ‖G‖_{H_r}`.

Proof (the argument of `UnforcedLeray.B0284.flatInverse_Hp_le`, with the Duhamel weight
`(t/s)^{Re μ} t⁻¹` in place of the Leray weight `t⁻¹`):
1. `G` is replaced by a strongly measurable representative `H` (`exists_periodic_rep`), which agrees
   with `G` almost everywhere on `{s > 0}`. Neither `flatDuhamel` nor the `H_r` norm sees the
   difference (`flatDuhamel_congr_of_ae`, `db_iter_congr`).
2. For `s > 0`, the norm of a Bochner integral is at most the integral of the norms, and the
   `L^r(dq/c dη)` norm in `z` is taken inside by Minkowski (`NonUniqueEuler.Conv.eLpNorm_lintegral_le`).
   Each slice is bounded by heat contraction (`flatHeatContraction`).
3. The substitution `t = s u` (`lintegral_Ioo_eq_mellin`) turns the bound into the Mellin
   convolution with kernel `k(u) = 1_{(0,1)}(u) u^{-1} u^{Re μ}`. The Mellin–Minkowski lemma
   `eLpNorm_mellin_le_lintegral` with `∫_0^1 u^{Re μ - 1 + γ_r} du = 1/a_r` finishes the bound.
4. Tonelli (`lintegral_prod`) identifies the `H_r` norm with the iterated norm `db_hNorm_iter`.

No hypothesis is added: every input is a proved theorem of the dependency files.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.IIb

/-! ## Measure-theoretic preliminaries -/

/-- The normalized cell measure is absolutely continuous with respect to Lebesgue measure. -/
theorem db_avg_ac (c : ℝ) : UnforcedLeray.Cyl.avgμ c ≪ volume := by
  unfold UnforcedLeray.Cyl.avgμ UnforcedLeray.Cyl.cellμ
  exact (Measure.absolutelyContinuous_of_le Measure.restrict_le_self).smul_left _

/-- The cell measure `dq/c dη` on `cell c` is σ-finite (it is `volume` restricted to a set). -/
instance db_sigmaFinite_cellμ (c : ℝ) : SigmaFinite (UnforcedLeray.Cyl.cellμ c) := by
  unfold UnforcedLeray.Cyl.cellμ
  infer_instance

/-- The normalized cell measure is σ-finite, as needed by Minkowski's inequality. -/
instance db_sigmaFinite_avg (c : ℝ) : SigmaFinite (UnforcedLeray.Cyl.avgμ c) := by
  unfold UnforcedLeray.Cyl.avgμ
  first
  | infer_instance
  | exact (inferInstance : SigmaFinite (((c⁻¹).toNNReal : NNReal) • UnforcedLeray.Cyl.cellμ c))

/-- `hMeas c r` is the age weight `s^{r/2-5/2} ds` times the normalized cell measure. -/
theorem db_hMeas_eq (c r : ℝ) :
    hMeas c r = (UnforcedLeray.B0284.ageWeight (r / 2 - 5 / 2)).prod (UnforcedLeray.Cyl.avgμ c) :=
  rfl

/-- The `L^r` norm as a power integral (`r > 0`). -/
theorem db_eLpNorm_rpow {α ε : Type*} [MeasurableSpace α] [ENorm ε] {μ : Measure α} {f : α → ε}
    {r : ℝ} (hr : 0 < r) :
    eLpNorm f (ENNReal.ofReal r) μ = (∫⁻ x, ‖f x‖ₑ ^ r ∂μ) ^ (1 / r) := by
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by simp [hr]) ENNReal.ofReal_ne_top,
    ENNReal.toReal_ofReal hr.le]

/-- A Lebesgue-almost-everywhere property of `Coord` gives the same property for almost every age
and then almost every cell point. -/
theorem db_ae_slices {P : Coord → Prop} (h : ∀ᵐ x : Coord, P x) :
    ∀ᵐ t ∂(volume : Measure ℝ), ∀ᵐ z ∂(volume : Measure (ℝ × ℝ)), P (t, z) := by
  have h' : ∀ᵐ x ∂((volume : Measure ℝ).prod (volume : Measure (ℝ × ℝ))), P x := by
    rw [← Measure.volume_eq_prod ℝ (ℝ × ℝ)]
    exact h
  exact Measure.ae_ae_of_ae_prod h'

/-- The `H_r` norm is the iterated norm (age outside, cell inside), by Tonelli. -/
theorem db_hNorm_iter {c r : ℝ} (hr : 0 < r) (K : CProf)
    (hK : AEMeasurable (fun x => ‖K x‖ₑ ^ r) (hMeas c r)) :
    hNorm c r K = eLpNorm (fun t => eLpNorm (fun z => K (t, z)) (ENNReal.ofReal r)
        (UnforcedLeray.Cyl.avgμ c)) (ENNReal.ofReal r)
      (UnforcedLeray.B0284.ageWeight (r / 2 - 5 / 2)) := by
  have hcancel : ∀ X : ℝ≥0∞, (X ^ (1 / r)) ^ r = X := fun X => by
    rw [← ENNReal.rpow_mul, one_div_mul_cancel hr.ne', ENNReal.rpow_one]
  unfold hNorm
  rw [db_hMeas_eq] at hK ⊢
  simp only [db_eLpNorm_rpow hr, enorm_eq_self, hcancel]
  congr 1
  exact lintegral_prod (fun x => ‖K x‖ₑ ^ r) hK

/-- Changing the representative of a Lebesgue-a.e. identity on `{s > 0}` does not change the
iterated `H_r` slice norms. -/
theorem db_iter_congr {c r : ℝ} {G H : CProf} (hGH : ∀ᵐ x : Coord, 0 < x.1 → G x = H x) :
    eLpNorm (fun t => eLpNorm (fun z => G (t, z)) (ENNReal.ofReal r) (UnforcedLeray.Cyl.avgμ c))
        (ENNReal.ofReal r) (UnforcedLeray.B0284.ageWeight (r / 2 - 5 / 2)) =
      eLpNorm (fun t => eLpNorm (fun z => H (t, z)) (ENNReal.ofReal r) (UnforcedLeray.Cyl.avgμ c))
        (ENNReal.ofReal r) (UnforcedLeray.B0284.ageWeight (r / 2 - 5 / 2)) := by
  have hprod : ∀ᵐ t ∂(volume : Measure ℝ), ∀ᵐ z ∂(volume : Measure (ℝ × ℝ)),
      0 < t → G (t, z) = H (t, z) := db_ae_slices hGH
  have h1 : ∀ᵐ t ∂(UnforcedLeray.B0284.ageWeight (r / 2 - 5 / 2)),
      ∀ᵐ z ∂(volume : Measure (ℝ × ℝ)), 0 < t → G (t, z) = H (t, z) :=
    (UnforcedLeray.B0284.ageWeight_ac _).ae_le (ae_restrict_of_ae hprod)
  have h2 : ∀ᵐ t ∂(UnforcedLeray.B0284.ageWeight (r / 2 - 5 / 2)),
      ∀ᵐ z ∂(UnforcedLeray.Cyl.avgμ c), G (t, z) = H (t, z) := by
    filter_upwards [h1, UnforcedLeray.B0284.ae_ageWeight_pos (r / 2 - 5 / 2)] with t ht ht0
    exact (db_avg_ac c).ae_le (ht.mono fun z hz => hz ht0)
  apply eLpNorm_congr_ae
  filter_upwards [h2] with t ht
  exact eLpNorm_congr_ae ht

/-! ## The Duhamel integrand -/

/-- The norm of the scalar Duhamel weight `(t/s)^μ t⁻¹` is `(t/s)^{Re μ} t⁻¹`. -/
theorem db_enorm_coef (μ : ℂ) {s t : ℝ} (hs : 0 < s) (ht : 0 < t) :
    ‖(((t / s : ℝ) : ℂ) ^ μ * ((t⁻¹ : ℝ) : ℂ))‖ₑ = ENNReal.ofReal ((t / s) ^ μ.re * t⁻¹) := by
  rw [← ofReal_norm, norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos (div_pos ht hs),
    Complex.norm_real, Real.norm_of_nonneg (inv_nonneg.2 ht.le)]

/-- The integrand of the Minkowski step: `(t/s)^a t⁻¹ · ‖e^{ν(s-t)Δ} H(t, ·)(z)‖`. -/
def db_integrand (ν s a : ℝ) (H : CProf) (z : ℝ × ℝ) (t : ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal ((t / s) ^ a * t⁻¹) * ‖flatHeat (ν * (s - t)) (fun w => H (t, w)) z‖ₑ

/-- The norm of the causal Duhamel integral is at most the integral of the weighted heat norms. -/
theorem db_duhamel_le {ν s : ℝ} (μ : ℂ) (H : CProf) (hs : 0 < s) (z : ℝ × ℝ) :
    ‖flatDuhamel ν μ H (s, z)‖ₑ ≤ ∫⁻ t in Ioo 0 s, db_integrand ν s μ.re H z t := by
  have hdef : flatDuhamel ν μ H (s, z) = ∫ t in Ioo 0 s,
      (((t / s : ℝ) : ℂ) ^ μ * ((t⁻¹ : ℝ) : ℂ)) • flatHeat (ν * (s - t)) (fun w => H (t, w)) z :=
    rfl
  rw [hdef]
  refine (enorm_integral_le_lintegral_enorm _).trans
    (le_of_eq (setLIntegral_congr_fun measurableSet_Ioo fun t ht => ?_))
  rw [enorm_smul, db_enorm_coef μ hs ht.1]
  rfl

/-! ## Measurability -/

/-- The flat heat semigroup applied to a slice of a strongly measurable family is jointly strongly
measurable in `(t, z)`. -/
theorem db_stronglyMeasurable_heat {ν s : ℝ} {H : CProf} (hH : StronglyMeasurable H) :
    StronglyMeasurable (fun q : Coord => flatHeat (ν * (s - q.1)) (fun w => H (q.1, w)) q.2) := by
  have hK : Measurable (fun p : Coord × (ℝ × ℝ) => flatHeatKernel (ν * (s - p.1.1)) p.2) := by
    unfold flatHeatKernel
    fun_prop
  have hHc : Measurable (fun p : Coord × (ℝ × ℝ) => ((p.1.1, p.1.2 - p.2) : Coord)) := by
    fun_prop
  have hΘ : StronglyMeasurable (fun p : Coord × (ℝ × ℝ) =>
      flatHeatKernel (ν * (s - p.1.1)) p.2 • H (p.1.1, p.1.2 - p.2)) :=
    hK.stronglyMeasurable.smul (hH.comp_measurable hHc)
  unfold flatHeat
  exact hΘ.integral_prod_right'

set_option maxHeartbeats 1000000 in
/-- The Duhamel integrand is measurable in `(z, t)`. -/
theorem db_measurable_integrand {ν s a : ℝ} {H : CProf} (hH : StronglyMeasurable H) :
    Measurable (fun q : (ℝ × ℝ) × ℝ => db_integrand ν s a H q.1 q.2) := by
  have hΦ : Measurable (fun q : Coord => flatHeat (ν * (s - q.1)) (fun w => H (q.1, w)) q.2) :=
    (db_stronglyMeasurable_heat (ν := ν) (s := s) hH).measurable
  have hcomp : Measurable (fun q : (ℝ × ℝ) × ℝ =>
      flatHeat (ν * (s - q.2)) (fun w => H (q.2, w)) q.1) :=
    hΦ.comp (measurable_snd.prodMk measurable_fst)
  have hm : Measurable (fun t : ℝ => ENNReal.ofReal ((t / s) ^ a * t⁻¹)) :=
    ENNReal.measurable_ofReal.comp (by fun_prop)
  have h1 : Measurable (fun q : (ℝ × ℝ) × ℝ => ENNReal.ofReal ((q.2 / s) ^ a * q.2⁻¹)) :=
    hm.comp measurable_snd
  have h2 : Measurable (fun q : (ℝ × ℝ) × ℝ => ‖flatHeat (ν * (s - q.2)) (fun w => H (q.2, w)) q.1‖ₑ) :=
    hcomp.enorm
  unfold db_integrand
  exact h1.mul h2

set_option maxHeartbeats 1000000 in
/-- The slice `z ↦ e^{θΔ} H(t, ·)(z)` of the flat heat semigroup is measurable. -/
theorem db_measurable_slice {ν s t : ℝ} {H : CProf} (hH : StronglyMeasurable H) :
    Measurable (fun z : ℝ × ℝ => flatHeat (ν * (s - t)) (fun w => H (t, w)) z) := by
  have hw : Measurable (fun w : ℝ × ℝ => ((t, w) : Coord)) := measurable_const.prodMk measurable_id
  have hΦ : Measurable (fun q : Coord => flatHeat (ν * (s - q.1)) (fun w => H (q.1, w)) q.2) :=
    (db_stronglyMeasurable_heat (ν := ν) (s := s) hH).measurable
  exact hΦ.comp hw

/-! ## The slice bound -/

/-- **Slice bound**: for `s > 0`, the `L^r(dq/c dη)` norm of the causal Duhamel integral of a
periodic `H` is at most the Duhamel integral of the slice norms (Minkowski in `t`, heat contraction
on each slice). -/
theorem db_slice_le {c r ν s : ℝ} (μ : ℂ) {H : CProf} (hr1 : 1 ≤ r) (hc : 0 < c) (hν : 0 < ν)
    (hs : 0 < s) (hH : StronglyMeasurable H)
    (hPer : ∀ᵐ t ∂(volume : Measure ℝ), ∀ᵐ z ∂(volume : Measure (ℝ × ℝ)),
      0 < t → H (t, (z.1 + c, z.2)) = H (t, z)) :
    eLpNorm (fun z => flatDuhamel ν μ H (s, z)) (ENNReal.ofReal r) (UnforcedLeray.Cyl.avgμ c) ≤
      ∫⁻ t in Ioo 0 s, ENNReal.ofReal ((t / s) ^ μ.re * t⁻¹) *
        eLpNorm (fun z => H (t, z)) (ENNReal.ofReal r) (UnforcedLeray.Cyl.avgμ c) := by
  have hr0 : (0 : ℝ) < r := lt_of_lt_of_le one_pos hr1
  have hp1 : (1 : ℝ≥0∞) ≤ ENNReal.ofReal r := ENNReal.one_le_ofReal.2 hr1
  have hF : Measurable (Function.uncurry (fun (z : ℝ × ℝ) (t : ℝ) => db_integrand ν s μ.re H z t)) :=
    db_measurable_integrand hH
  have hmink := NonUniqueEuler.Conv.eLpNorm_lintegral_le (μ := UnforcedLeray.Cyl.avgμ c)
    (ν := (volume : Measure ℝ).restrict (Ioo 0 s))
    (F := fun (z : ℝ × ℝ) (t : ℝ) => db_integrand ν s μ.re H z t) hF.aemeasurable hp1
    ENNReal.ofReal_ne_top
  have hpt : ∀ᵐ t ∂((volume : Measure ℝ).restrict (Ioo 0 s)),
      eLpNorm (fun z => db_integrand ν s μ.re H z t) (ENNReal.ofReal r)
          (UnforcedLeray.Cyl.avgμ c) ≤
        ENNReal.ofReal ((t / s) ^ μ.re * t⁻¹) *
          eLpNorm (fun z => H (t, z)) (ENNReal.ofReal r) (UnforcedLeray.Cyl.avgμ c) := by
    filter_upwards [ae_restrict_of_ae hPer, ae_restrict_mem measurableSet_Ioo] with t ht htI
    have hθ : 0 < ν * (s - t) := mul_pos hν (sub_pos.2 htI.2)
    have hw : Measurable (fun w : ℝ × ℝ => ((t, w) : Coord)) := measurable_const.prodMk measurable_id
    have hmeasH : AEStronglyMeasurable (fun w => H (t, w)) volume :=
      (hH.comp_measurable hw).aestronglyMeasurable
    have hcont := flatHeatContraction r c (ν * (s - t)) (fun w => H (t, w)) hr1 hc hθ
      (by filter_upwards [ht] with z hz; exact hz htI.1) hmeasH
    have hslice := db_measurable_slice (ν := ν) (s := s) (t := t) hH
    have e : eLpNorm (fun z => db_integrand ν s μ.re H z t) (ENNReal.ofReal r)
          (UnforcedLeray.Cyl.avgμ c) = ENNReal.ofReal ((t / s) ^ μ.re * t⁻¹) *
          eLpNorm (fun z => ‖flatHeat (ν * (s - t)) (fun w => H (t, w)) z‖ₑ) (ENNReal.ofReal r)
            (UnforcedLeray.Cyl.avgμ c) :=
      UnforcedLeray.B0284.eLpNorm_const_mul_enn
        (g := fun z => ‖flatHeat (ν * (s - t)) (fun w => H (t, w)) z‖ₑ)
        hslice.enorm.aemeasurable _ hr0
    rw [e, eLpNorm_enorm]
    gcongr
  calc eLpNorm (fun z => flatDuhamel ν μ H (s, z)) (ENNReal.ofReal r) (UnforcedLeray.Cyl.avgμ c)
      ≤ eLpNorm (fun z => ∫⁻ t in Ioo 0 s, db_integrand ν s μ.re H z t) (ENNReal.ofReal r)
          (UnforcedLeray.Cyl.avgμ c) :=
        eLpNorm_mono_enorm fun z => by
          rw [enorm_eq_self]
          exact db_duhamel_le μ H hs z
    _ ≤ ∫⁻ t in Ioo 0 s, eLpNorm (fun z => db_integrand ν s μ.re H z t) (ENNReal.ofReal r)
          (UnforcedLeray.Cyl.avgμ c) := hmink
    _ ≤ ∫⁻ t in Ioo 0 s, ENNReal.ofReal ((t / s) ^ μ.re * t⁻¹) *
          eLpNorm (fun z => H (t, z)) (ENNReal.ofReal r) (UnforcedLeray.Cyl.avgμ c) :=
        lintegral_mono_ae hpt

/-! ## The Mellin substitution -/

/-- The Hardy-type Mellin kernel `k(u) = 1_{(0,1)}(u) u^{-1} · u^a`. -/
def db_kernel (a : ℝ) (u : ℝ) : ℝ≥0∞ :=
  UnforcedLeray.B0284.hardyKernel u * ENNReal.ofReal (u ^ a)

theorem db_measurable_kernel (a : ℝ) : Measurable (db_kernel a) := by
  unfold db_kernel
  exact UnforcedLeray.B0284.measurable_hardyKernel.mul (by fun_prop)

/-- The slice norm `t ↦ ‖H(t, ·)‖_{L^r(dq/c dη)}`. -/
def db_slice (c r : ℝ) (H : CProf) (t : ℝ) : ℝ≥0∞ :=
  eLpNorm (fun z => H (t, z)) (ENNReal.ofReal r) (UnforcedLeray.Cyl.avgμ c)

/-- The substitution `t = s u` writes the Duhamel weighted integral as a Mellin convolution. -/
theorem db_mellin_identity (μ : ℂ) {s : ℝ} (hs : 0 < s) (ψ : ℝ → ℝ≥0∞) :
    ∫⁻ t in Ioo 0 s, ENNReal.ofReal ((t / s) ^ μ.re * t⁻¹) * ψ t =
      ∫⁻ u in Ioi 0, db_kernel μ.re u * ψ (s * u) := by
  rw [UnforcedLeray.B0284.lintegral_Ioo_eq_mellin hs
    (fun t => ENNReal.ofReal ((t / s) ^ μ.re * t⁻¹) * ψ t)]
  refine setLIntegral_congr_fun measurableSet_Ioi (fun u hu => ?_)
  have hu0 : (0 : ℝ) < u := hu
  have hsu : 0 < s * u := mul_pos hs hu0
  have hs0 : s ≠ 0 := hs.ne'
  have hsu0 : s * u ≠ 0 := hsu.ne'
  have e2 : s * u / s = u := by
    field_simp
  have e1 : s * u * (u ^ μ.re * (s * u)⁻¹) = u ^ μ.re := by
    rw [mul_comm (u ^ μ.re), ← mul_assoc, mul_inv_cancel₀ hsu0, one_mul]
  have key : ENNReal.ofReal (s * u) * ENNReal.ofReal ((s * u / s) ^ μ.re * (s * u)⁻¹) =
      ENNReal.ofReal (u ^ μ.re) := by
    rw [e2, ← ENNReal.ofReal_mul hsu.le, e1]
  unfold db_kernel
  calc UnforcedLeray.B0284.hardyKernel u * (ENNReal.ofReal (s * u) *
        (ENNReal.ofReal ((s * u / s) ^ μ.re * (s * u)⁻¹) * ψ (s * u)))
      = UnforcedLeray.B0284.hardyKernel u * ((ENNReal.ofReal (s * u) *
          ENNReal.ofReal ((s * u / s) ^ μ.re * (s * u)⁻¹)) * ψ (s * u)) := by ring
    _ = UnforcedLeray.B0284.hardyKernel u * ENNReal.ofReal (u ^ μ.re) * ψ (s * u) := by
        rw [key]
        ring

/-- The Mellin constant: `∫_0^1 u^{Re μ - 1 + γ_r} du = 1/a_r`, with `-(α+1)/r = γ_r` for
`α = r/2 - 5/2`. -/
theorem db_const (μ : ℂ) {r : ℝ} (hr : 0 < r) (ha : 0 < μ.re + (3 / r - 1) / 2) :
    ∫⁻ u in Ioi 0, db_kernel μ.re u * ENNReal.ofReal (u ^ (-(r / 2 - 5 / 2 + 1) / r)) =
      ENNReal.ofReal (1 / (μ.re + (3 / r - 1) / 2)) := by
  have hr0 : r ≠ 0 := hr.ne'
  have hexp : -(r / 2 - 5 / 2 + 1) / r = (3 / r - 1) / 2 := by
    field_simp
    ring
  rw [hexp]
  have hpt : ∀ u ∈ Ioi (0 : ℝ), db_kernel μ.re u * ENNReal.ofReal (u ^ ((3 / r - 1) / 2)) =
      UnforcedLeray.B0284.hardyKernel u * ENNReal.ofReal (u ^ (μ.re + (3 / r - 1) / 2)) := by
    intro u hu
    have hu0 : (0 : ℝ) < u := hu
    unfold db_kernel
    rw [mul_assoc, ← ENNReal.ofReal_mul (Real.rpow_nonneg hu0.le μ.re),
      ← Real.rpow_add hu0]
  rw [setLIntegral_congr_fun measurableSet_Ioi hpt]
  exact UnforcedLeray.B0284.lintegral_hardyKernel_rpow ha

/-! ## The target -/

/-- **Target of `PartII-b:T12/4`** (SP 1923-1927): the causal Duhamel operator is bounded on `H_r`
with norm at most `1/a_r`, `a_r = Re μ + (3/r-1)/2`. -/
theorem duhamelBound : DuhamelBound := by
  intro r hr1 hr3 μ ha ν c hν hc G hG
  have hr : (0 : ℝ) < r := by linarith
  have hr1' : (1 : ℝ) ≤ r := hr1.le
  obtain ⟨H, hHs, hGH⟩ := exists_periodic_rep (a := r / 2 - 5 / 2) hc hG.periodic hG.meas
  rw [flatDuhamel_congr_of_ae ν μ hGH]
  -- `H` is `c`-periodic in `q` almost everywhere on `{s > 0}`
  have hHper : ∀ᵐ x : Coord, 0 < x.1 → H (qSh c x) = H x := by
    have h1 : ∀ᵐ x : Coord, 0 < x.1 → G (qSh c x) = G x := QPerHalf.ae_imp hG.periodic
    have h2 : ∀ᵐ x : Coord, 0 < (qSh c x).1 → G (qSh c x) = H (qSh c x) :=
      (qSh_measurePreserving c).quasiMeasurePreserving.ae hGH
    filter_upwards [h1, h2, hGH] with x hx1 hx2 hx3 hx
    rw [← hx2 hx, hx1 hx]
    exact hx3 hx
  have hPer : ∀ᵐ t ∂(volume : Measure ℝ), ∀ᵐ z ∂(volume : Measure (ℝ × ℝ)),
      0 < t → H (t, (z.1 + c, z.2)) = H (t, z) := db_ae_slices hHper
  have hFD : StronglyMeasurable (flatDuhamel ν μ H) := flatDuhamel_stronglyMeasurable ν μ hHs
  have hKm : AEMeasurable (fun x => ‖flatDuhamel ν μ H x‖ₑ ^ r) (hMeas c r) :=
    (hFD.measurable.enorm.pow_const r).aemeasurable
  have hGm : AEMeasurable (fun x => ‖G x‖ₑ ^ r) (hMeas c r) :=
    hG.meas.aemeasurable.enorm.pow_const r
  rw [db_hNorm_iter hr (flatDuhamel ν μ H) hKm, db_hNorm_iter hr G hGm, db_iter_congr hGH]
  have hsb : ∀ s : ℝ, 0 < s → eLpNorm (fun z => flatDuhamel ν μ H (s, z)) (ENNReal.ofReal r)
      (UnforcedLeray.Cyl.avgμ c) ≤ ∫⁻ u in Ioi 0, db_kernel μ.re u * db_slice c r H (s * u) := by
    intro s hs
    rw [← db_mellin_identity μ hs (db_slice c r H)]
    exact db_slice_le μ hr1' hc hν hs hHs hPer
  have hψm : Measurable (db_slice c r H) := by
    have e : db_slice c r H = fun t => (∫⁻ z, ‖H (t, z)‖ₑ ^ r ∂(UnforcedLeray.Cyl.avgμ c)) ^ (1 / r) := by
      funext t
      unfold db_slice
      exact db_eLpNorm_rpow hr
    rw [e]
    exact ((hHs.measurable.enorm.pow_const r).lintegral_prod_right').pow_const _
  calc eLpNorm (fun s => eLpNorm (fun z => flatDuhamel ν μ H (s, z)) (ENNReal.ofReal r)
          (UnforcedLeray.Cyl.avgμ c)) (ENNReal.ofReal r)
        (UnforcedLeray.B0284.ageWeight (r / 2 - 5 / 2))
      ≤ eLpNorm (fun s => ∫⁻ u in Ioi 0, db_kernel μ.re u * db_slice c r H (s * u))
          (ENNReal.ofReal r) (UnforcedLeray.B0284.ageWeight (r / 2 - 5 / 2)) := by
        refine eLpNorm_mono_enorm_ae ?_
        filter_upwards [UnforcedLeray.B0284.ae_ageWeight_pos (r / 2 - 5 / 2)] with s hs
        rw [enorm_eq_self, enorm_eq_self]
        exact hsb s hs
    _ ≤ (∫⁻ u in Ioi 0, db_kernel μ.re u * ENNReal.ofReal (u ^ (-(r / 2 - 5 / 2 + 1) / r))) *
          eLpNorm (db_slice c r H) (ENNReal.ofReal r)
            (UnforcedLeray.B0284.ageWeight (r / 2 - 5 / 2)) :=
        UnforcedLeray.B0284.eLpNorm_mellin_le_lintegral hr1' (db_measurable_kernel μ.re) hψm
    _ = ENNReal.ofReal (1 / (μ.re + (3 / r - 1) / 2)) *
          eLpNorm (db_slice c r H) (ENNReal.ofReal r)
            (UnforcedLeray.B0284.ageWeight (r / 2 - 5 / 2)) := by
        rw [db_const μ hr ha]

end UnforcedLeray.Short.IIb
