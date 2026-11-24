import UnforcedLeray.Short.PartI.Sub.PartI_T04_6_1
import UnforcedLeray.Short.PartI.Tasks.VorticityFirstMoment.CurlRegularity
import UnforcedLeray.Short.PartI.Tasks.VorticityFirstMoment.LocalVorticityEquation
import UnforcedLeray.Short.PartI.Tasks.ClassicalOdd.EtaCutoffFacts

/-!
# `PartI:T04/6/1/3`: `apEnstrophyHasDeriv` (source lines 285-287)

For `s ∈ (0,T)`, `G_R(s) = ∫_cell χ_R(η) om(s,z)²` has derivative
`∫ χ_R (2 om ∂_s om)`. The scalar vorticity equation `∂_s om = -v·∇om + νΔom`
(`localVorticityEquation`) turns this into `apEnstrophyRhs`, using integration by parts in `q`
(periodicity) and `η` (compact support of `χ_R`), and `div v = 0`.

Structure: `apHD_deriv_integral` (differentiation under the integral), `apHD_core` (the algebraic
integration-by-parts identity for generic functions), and the assembly `apEnstrophyHasDeriv`.
-/

set_option autoImplicit false

noncomputable section

open Set Filter MeasureTheory Topology
open scoped ContDiff

namespace UnforcedLeray.Short.PartI

open UnforcedLeray
open UnforcedLeray.Train (Vec)
open UnforcedLeray.Cyl (Plane)

/-! ### Elementary facts -/

lemma apHD_eta_zero {R : ℝ} (hR : 0 < R) {η : ℝ} (hη : 2 * R ≤ |η|) :
    etaCutoff R η = 0 := by
  have h2 : 2 ≤ |η| / R := (le_div_iff₀ hR).2 (by linarith)
  have hle : 2 - |η| / R ≤ 0 := by linarith
  show Real.smoothTransition (2 - |η| / R) ^ 2 = 0
  simp [Real.smoothTransition.zero_of_nonpos hle]

lemma apHD_eta_abs (R η : ℝ) : |etaCutoff R η| ≤ 1 := by
  show |Real.smoothTransition (2 - |η| / R) ^ 2| ≤ 1
  rw [abs_of_nonneg (by positivity)]
  exact pow_le_one₀ (Real.smoothTransition.nonneg _) (Real.smoothTransition.le_one _)

lemma apHD_deriv_zero {φ : ℝ → ℝ} {R0 η : ℝ} (hφv : ∀ x : ℝ, R0 < |x| → φ x = 0)
    (hη : R0 < |η|) : deriv φ η = 0 := by
  have hopen : IsOpen {x : ℝ | R0 < |x|} := isOpen_lt continuous_const continuous_abs
  have hev : φ =ᶠ[𝓝 η] fun _ => (0 : ℝ) :=
    Filter.eventually_of_mem (hopen.mem_nhds hη) (fun x hx => hφv x hx)
  rw [hev.deriv_eq, deriv_const]

lemma apHD_pq_const (φ : ℝ → ℝ) (z : Plane) :
    Cyl.partialQ (fun z : Plane => φ z.2) z = 0 := by
  unfold Cyl.partialQ
  simp

lemma apHD_pq_mul (f g : Plane → ℝ) (hf : Differentiable ℝ f) (hg : Differentiable ℝ g)
    (z : Plane) :
    Cyl.partialQ (fun z : Plane => f z * g z) z =
      Cyl.partialQ f z * g z + f z * Cyl.partialQ g z :=
  ((Cyl.hasDerivAt_sliceQ hf z.1 z.2).mul (Cyl.hasDerivAt_sliceQ hg z.1 z.2)).deriv

lemma apHD_pe_mul (f g : Plane → ℝ) (hf : Differentiable ℝ f) (hg : Differentiable ℝ g)
    (z : Plane) :
    Cyl.partialEta (fun z : Plane => f z * g z) z =
      Cyl.partialEta f z * g z + f z * Cyl.partialEta g z :=
  ((Cyl.hasDerivAt_sliceEta hf z.1 z.2).mul (Cyl.hasDerivAt_sliceEta hg z.1 z.2)).deriv

lemma apHD_pq_cont {f : Plane → ℝ} (hf : ContDiff ℝ 2 f) : Continuous (Cyl.partialQ f) := by
  have hd : Differentiable ℝ f := hf.differentiable (by norm_num)
  have e : Cyl.partialQ f = fun z => fderiv ℝ f z (1, 0) :=
    funext (fun z => Cyl.partialQ_eq_fderiv hd z)
  rw [e]
  exact (hf.continuous_fderiv (by norm_num)).clm_apply continuous_const

lemma apHD_pe_cont {f : Plane → ℝ} (hf : ContDiff ℝ 2 f) : Continuous (Cyl.partialEta f) := by
  have hd : Differentiable ℝ f := hf.differentiable (by norm_num)
  have e : Cyl.partialEta f = fun z => fderiv ℝ f z (0, 1) :=
    funext (fun z => Cyl.partialEta_eq_fderiv hd z)
  rw [e]
  exact (hf.continuous_fderiv (by norm_num)).clm_apply continuous_const

lemma apHD_integ {c R0 : ℝ} {F : Plane → ℝ} (hF : Continuous F)
    (hz : ∀ z : Plane, R0 < |z.2| → F z = 0) : IntegrableOn F (Cyl.cell c) :=
  Cyl.VanishesOutside.integrableOn_cell (R := R0) hz hF c

theorem apHD_deriv_at {T : ℝ} {W : ℝ × Plane → ℝ}
    (hW : ContDiffOn ℝ 2 W (Ioo 0 T ×ˢ (univ : Set Plane))) {t : ℝ} (ht0 : 0 < t) (htT : t < T)
    (z : Plane) :
    HasDerivAt (fun u => W (u, z)) (fderiv ℝ W (t, z) ((1 : ℝ), (0 : Plane))) t := by
  have hmem : (Ioo (0 : ℝ) T ×ˢ (univ : Set Plane)) ∈ 𝓝 (t, z) :=
    (isOpen_Ioo.prod isOpen_univ).mem_nhds (Set.mk_mem_prod ⟨ht0, htT⟩ (mem_univ z))
  have hF : HasFDerivAt W (fderiv ℝ W (t, z)) (t, z) :=
    ((hW.contDiffAt hmem).differentiableAt (by norm_num)).hasFDerivAt
  have hg : HasDerivAt (fun u : ℝ => (u, z)) ((1 : ℝ), (0 : Plane)) t :=
    (hasDerivAt_id' t).prodMk (hasDerivAt_const t z)
  exact hF.comp_hasDerivAt t hg

/-! ### Differentiation under the integral sign -/

theorem apHD_deriv_integral {φ : ℝ → ℝ} (hφc : Continuous φ) {R0 : ℝ}
    (hφv : ∀ x : ℝ, R0 < |x| → φ x = 0) (hφb : ∀ x : ℝ, |φ x| ≤ 1)
    {T : ℝ} {W : ℝ × Plane → ℝ} (hW : ContDiffOn ℝ 2 W (Ioo 0 T ×ˢ (univ : Set Plane)))
    (c : ℝ) (hc : 0 < c) {r : ℝ} (hr : 0 < r) (hrT : r < T) :
    HasDerivAt (fun t => ∫ z in Cyl.cell c, φ z.2 * (W (t, z) * W (t, z)))
      (∫ z in Cyl.cell c, φ z.2 * (fderiv ℝ W (r, z) ((1 : ℝ), (0 : Plane)) * W (r, z)
          + W (r, z) * fderiv ℝ W (r, z) ((1 : ℝ), (0 : Plane)))) r := by
  have hWc : ContinuousOn W (Ioo 0 T ×ˢ (univ : Set Plane)) := hW.continuousOn
  have hGc : ContinuousOn (fun x : ℝ × Plane => fderiv ℝ W x ((1 : ℝ), (0 : Plane)))
      (Ioo 0 T ×ˢ (univ : Set Plane)) := by
    have h2 : ContinuousOn (fderiv ℝ W) (Ioo 0 T ×ˢ (univ : Set Plane)) :=
      hW.continuousOn_fderiv_of_isOpen (isOpen_Ioo.prod isOpen_univ) (by norm_num)
    exact h2.clm_apply continuousOn_const
  have hHc : ContinuousOn (fun x : ℝ × Plane => fderiv ℝ W x ((1 : ℝ), (0 : Plane)) * W x
      + W x * fderiv ℝ W x ((1 : ℝ), (0 : Plane))) (Ioo 0 T ×ˢ (univ : Set Plane)) :=
    (hGc.mul hWc).add (hWc.mul hGc)
  have hslice : ∀ t : ℝ, 0 < t → t < T → Continuous (fun z : Plane => W (t, z)) :=
    fun t ht htT => hWc.comp_continuous (f := fun z : Plane => (t, z)) (by fun_prop)
      (fun z => Set.mk_mem_prod ⟨ht, htT⟩ (mem_univ z))
  have hHs : Continuous (fun z : Plane => fderiv ℝ W (r, z) ((1 : ℝ), (0 : Plane)) * W (r, z)
      + W (r, z) * fderiv ℝ W (r, z) ((1 : ℝ), (0 : Plane))) :=
    hHc.comp_continuous (f := fun z : Plane => (r, z)) (by fun_prop)
      (fun z => Set.mk_mem_prod ⟨hr, hrT⟩ (mem_univ z))
  have hφc2 : Continuous (fun z : Plane => φ z.2) := hφc.comp continuous_snd
  have hKt : IsCompact (Icc (r / 2) ((r + T) / 2) ×ˢ (Icc (-c) c ×ˢ Icc (-R0) R0)) :=
    isCompact_Icc.prod (isCompact_Icc.prod isCompact_Icc)
  have hKt_sub : Icc (r / 2) ((r + T) / 2) ×ˢ (Icc (-c) c ×ˢ Icc (-R0) R0)
      ⊆ Ioo 0 T ×ˢ (univ : Set Plane) := by
    intro x hx
    exact Set.mk_mem_prod ⟨by linarith [hx.1.1], by linarith [hx.1.2]⟩ (mem_univ _)
  obtain ⟨Cg, hCg⟩ := hKt.exists_bound_of_continuousOn (hHc.mono hKt_sub)
  have hboxc : IsCompact (Icc (-c) c ×ˢ Icc (-R0) R0) := isCompact_Icc.prod isCompact_Icc
  have hcellm : MeasurableSet (Cyl.cell c) := by
    unfold Cyl.cell
    exact measurableSet_Ico.prod MeasurableSet.univ
  have hout : ∀ z : Plane, z ∈ Cyl.cell c → z ∉ (Icc (-c) c ×ˢ Icc (-R0) R0) → R0 < |z.2| := by
    intro z hz hm
    by_contra hlt
    rw [not_lt] at hlt
    apply hm
    have hq := hz.1
    exact Set.mk_mem_prod ⟨by linarith [hq.1], by linarith [hq.2]⟩ (abs_le.1 hlt)
  have hbound : ∀ᵐ z ∂(volume.restrict (Cyl.cell c)), ∀ t ∈ Icc (r / 2) ((r + T) / 2),
      ‖φ z.2 * (fderiv ℝ W (t, z) ((1 : ℝ), (0 : Plane)) * W (t, z)
          + W (t, z) * fderiv ℝ W (t, z) ((1 : ℝ), (0 : Plane)))‖ ≤
        (Icc (-c) c ×ˢ Icc (-R0) R0).indicator (fun _ : Plane => max Cg 0) z := by
    filter_upwards [ae_restrict_mem hcellm] with z hz
    intro t ht
    by_cases hm : z ∈ (Icc (-c) c ×ˢ Icc (-R0) R0)
    · rw [Set.indicator_of_mem hm]
      have hg : ‖fderiv ℝ W (t, z) ((1 : ℝ), (0 : Plane)) * W (t, z)
          + W (t, z) * fderiv ℝ W (t, z) ((1 : ℝ), (0 : Plane))‖ ≤ Cg :=
        hCg (t, z) (Set.mk_mem_prod ht hm)
      have h1 : ‖φ z.2‖ ≤ 1 := by rw [Real.norm_eq_abs]; exact hφb z.2
      calc ‖φ z.2 * (fderiv ℝ W (t, z) ((1 : ℝ), (0 : Plane)) * W (t, z)
          + W (t, z) * fderiv ℝ W (t, z) ((1 : ℝ), (0 : Plane)))‖
          = ‖φ z.2‖ * ‖fderiv ℝ W (t, z) ((1 : ℝ), (0 : Plane)) * W (t, z)
          + W (t, z) * fderiv ℝ W (t, z) ((1 : ℝ), (0 : Plane))‖ := norm_mul _ _
        _ ≤ 1 * Cg := mul_le_mul h1 hg (norm_nonneg _) zero_le_one
        _ ≤ max Cg 0 := by rw [one_mul]; exact le_max_left _ _
    · rw [Set.indicator_of_notMem hm, hφv z.2 (hout z hz hm)]
      simp
  have hbox_int : Integrable ((Icc (-c) c ×ˢ Icc (-R0) R0).indicator (fun _ : Plane => max Cg 0))
      (volume.restrict (Cyl.cell c)) := by
    rw [integrable_indicator_iff hboxc.isClosed.measurableSet]
    refine integrableOn_const ?_
    rw [Measure.restrict_apply hboxc.isClosed.measurableSet]
    exact ne_top_of_le_ne_top hboxc.measure_lt_top.ne (measure_mono inter_subset_left)
  have hF_meas : ∀ᶠ t in 𝓝 r, AEStronglyMeasurable
      (fun z : Plane => φ z.2 * (W (t, z) * W (t, z))) (volume.restrict (Cyl.cell c)) := by
    filter_upwards [Ioo_mem_nhds hr hrT] with t ht
    exact (hφc2.mul ((hslice t ht.1 ht.2).mul (hslice t ht.1 ht.2))).aestronglyMeasurable
  have hF_int : Integrable (fun z : Plane => φ z.2 * (W (r, z) * W (r, z)))
      (volume.restrict (Cyl.cell c)) :=
    apHD_integ (c := c) (R0 := R0) (hφc2.mul ((hslice r hr hrT).mul (hslice r hr hrT)))
      (fun z hz => by simp [hφv z.2 hz])
  have hF'_meas : AEStronglyMeasurable (fun z : Plane => φ z.2 * (fderiv ℝ W (r, z) ((1 : ℝ), (0 : Plane))
      * W (r, z) + W (r, z) * fderiv ℝ W (r, z) ((1 : ℝ), (0 : Plane))))
      (volume.restrict (Cyl.cell c)) :=
    (hφc2.mul hHs).aestronglyMeasurable
  have hdiff : ∀ᵐ z ∂(volume.restrict (Cyl.cell c)), ∀ t ∈ Icc (r / 2) ((r + T) / 2),
      HasDerivAt (fun u => φ z.2 * (W (u, z) * W (u, z)))
        (φ z.2 * (fderiv ℝ W (t, z) ((1 : ℝ), (0 : Plane)) * W (t, z)
          + W (t, z) * fderiv ℝ W (t, z) ((1 : ℝ), (0 : Plane)))) t := by
    refine ae_of_all _ (fun z t ht => ?_)
    have ht0 : 0 < t := by linarith [ht.1]
    have htT : t < T := by linarith [ht.2]
    exact ((apHD_deriv_at hW ht0 htT z).mul (apHD_deriv_at hW ht0 htT z)).const_mul (φ z.2)
  have hmain := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := volume.restrict (Cyl.cell c))
    (F := fun t z => φ z.2 * (W (t, z) * W (t, z)))
    (F' := fun t z => φ z.2 * (fderiv ℝ W (t, z) ((1 : ℝ), (0 : Plane)) * W (t, z)
          + W (t, z) * fderiv ℝ W (t, z) ((1 : ℝ), (0 : Plane))))
    (bound := (Icc (-c) c ×ˢ Icc (-R0) R0).indicator (fun _ : Plane => max Cg 0))
    (x₀ := r) (s := Icc (r / 2) ((r + T) / 2)) (Icc_mem_nhds (by linarith) (by linarith))
    hF_meas hF_int hF'_meas hbound hbox_int hdiff
  exact hmain.2

/-! ### The integration-by-parts identity (generic) -/

theorem apHD_core {φ : ℝ → ℝ} {R0 c ν : ℝ} (hφ : ContDiff ℝ 2 φ) (hc : 0 < c)
    (hφv : ∀ η : ℝ, R0 < |η| → φ η = 0)
    {om u w : Plane → ℝ} (hom : ContDiff ℝ 2 om) (hu : ContDiff ℝ 2 u) (hw : ContDiff ℝ 2 w)
    (homp : Cyl.IsPeriodic c om) (hup : Cyl.IsPeriodic c u)
    (hdiv : ∀ z : Plane, Cyl.partialQ u z + Cyl.partialEta w z = 0) :
    ∫ z in Cyl.cell c, φ z.2 * (2 * om z * (-(u z * Cyl.partialQ om z + w z * Cyl.partialEta om z)
        + ν * Train.lapS om z))
      = -2 * ν * (∫ z in Cyl.cell c, φ z.2 * (Cyl.partialQ om z ^ 2 + Cyl.partialEta om z ^ 2))
        - 2 * ν * (∫ z in Cyl.cell c, deriv φ z.2 * om z * Cyl.partialEta om z)
        + ∫ z in Cyl.cell c, om z ^ 2 * w z * deriv φ z.2 := by
  have homd : Differentiable ℝ om := hom.differentiable (by norm_num)
  have hud : Differentiable ℝ u := hu.differentiable (by norm_num)
  have hwd : Differentiable ℝ w := hw.differentiable (by norm_num)
  have homc : Continuous om := hom.continuous
  have hφ2 : ContDiff ℝ 2 (fun z : Plane => φ z.2) := hφ.comp contDiff_snd
  have hφd : Differentiable ℝ (fun z : Plane => φ z.2) := hφ2.differentiable (by norm_num)
  have hφc : Continuous (fun z : Plane => φ z.2) := hφ2.continuous
  have hφ'c : Continuous (fun z : Plane => deriv φ z.2) :=
    (hφ.continuous_deriv (by norm_num)).comp continuous_snd
  have hpqom1 : ContDiff ℝ 1 (Cyl.partialQ om) :=
    Cyl.contDiff_partialQ (n := 1) (hom.of_le (by norm_num))
  have hpeom1 : ContDiff ℝ 1 (Cyl.partialEta om) :=
    Cyl.contDiff_partialEta (n := 1) (hom.of_le (by norm_num))
  have hpqomd : Differentiable ℝ (Cyl.partialQ om) := hpqom1.differentiable (by norm_num)
  have hpeomd : Differentiable ℝ (Cyl.partialEta om) := hpeom1.differentiable (by norm_num)
  have hpqomc : Continuous (Cyl.partialQ om) := hpqom1.continuous
  have hpeomc : Continuous (Cyl.partialEta om) := hpeom1.continuous
  have hpqpqc : Continuous (Cyl.partialQ (Cyl.partialQ om)) :=
    (Cyl.contDiff_partialQ (n := 0) (h := Cyl.partialQ om) (by simpa using hpqom1)).continuous
  have hpepec : Continuous (Cyl.partialEta (Cyl.partialEta om)) :=
    (Cyl.contDiff_partialEta (n := 0) (h := Cyl.partialEta om) (by simpa using hpeom1)).continuous
  have hpqomp : Cyl.IsPeriodic c (Cyl.partialQ om) := homp.partialQ
  have hfp : Cyl.IsPeriodic c (fun z : Plane => om z * om z) := fun z => by
    show om (z.1 + c, z.2) * om (z.1 + c, z.2) = om z * om z
    rw [homp z]
  have hgup : Cyl.IsPeriodic c (fun z : Plane => φ z.2 * u z) := fun z => by
    show φ (z.1 + c, z.2).2 * u (z.1 + c, z.2) = φ z.2 * u z
    rw [hup z]
  have hgomp : Cyl.IsPeriodic c (fun z : Plane => φ z.2 * om z) := fun z => by
    show φ (z.1 + c, z.2).2 * om (z.1 + c, z.2) = φ z.2 * om z
    rw [homp z]
  have hpq_f : ∀ z : Plane, Cyl.partialQ (fun z : Plane => om z * om z) z
      = Cyl.partialQ om z * om z + om z * Cyl.partialQ om z :=
    fun z => apHD_pq_mul om om homd homd z
  have hpe_f : ∀ z : Plane, Cyl.partialEta (fun z : Plane => om z * om z) z
      = Cyl.partialEta om z * om z + om z * Cyl.partialEta om z :=
    fun z => apHD_pe_mul om om homd homd z
  have hpq_φu : ∀ z : Plane, Cyl.partialQ (fun z : Plane => φ z.2 * u z) z
      = φ z.2 * Cyl.partialQ u z := by
    intro z
    have h := apHD_pq_mul (fun z : Plane => φ z.2) u hφd hud z
    rw [apHD_pq_const] at h
    rw [h]; ring
  have hpq_φom : ∀ z : Plane, Cyl.partialQ (fun z : Plane => φ z.2 * om z) z
      = φ z.2 * Cyl.partialQ om z := by
    intro z
    have h := apHD_pq_mul (fun z : Plane => φ z.2) om hφd homd z
    rw [apHD_pq_const] at h
    rw [h]; ring
  have hpe_φw : ∀ z : Plane, Cyl.partialEta (fun z : Plane => φ z.2 * w z) z
      = deriv φ z.2 * w z + φ z.2 * Cyl.partialEta w z :=
    fun z => apHD_pe_mul (fun z : Plane => φ z.2) w hφd hwd z
  have hpe_φom : ∀ z : Plane, Cyl.partialEta (fun z : Plane => φ z.2 * om z) z
      = deriv φ z.2 * om z + φ z.2 * Cyl.partialEta om z :=
    fun z => apHD_pe_mul (fun z : Plane => φ z.2) om hφd homd z
  have hφom_c : Continuous (fun z : Plane => φ z.2 * om z) := hφc.mul homc
  have hφu_c : Continuous (fun z : Plane => φ z.2 * u z) := hφc.mul hu.continuous
  have hφw_c : Continuous (fun z : Plane => φ z.2 * w z) := hφc.mul hw.continuous
  have homom_c : Continuous (fun z : Plane => om z * om z) := homc.mul homc
  have hφ2om : ContDiff ℝ 2 (fun z : Plane => φ z.2 * om z) := hφ2.mul hom
  have hφ2u : ContDiff ℝ 2 (fun z : Plane => φ z.2 * u z) := hφ2.mul hu
  have hφ2w : ContDiff ℝ 2 (fun z : Plane => φ z.2 * w z) := hφ2.mul hw
  have hφomd : Differentiable ℝ (fun z : Plane => φ z.2 * om z) := hφd.mul homd
  have hφwd : Differentiable ℝ (fun z : Plane => φ z.2 * w z) := hφd.mul hwd
  have homomd : Differentiable ℝ (fun z : Plane => om z * om z) := homd.mul homd
  have hφud : Differentiable ℝ (fun z : Plane => φ z.2 * u z) := hφd.mul hud
  have hφwd' : Differentiable ℝ (fun z : Plane => φ z.2 * w z) := hφd.mul hwd
  have hwc : Continuous w := hw.continuous
  have hφu_pq : Continuous (fun z : Plane => φ z.2 * Cyl.partialQ u z) :=
    hφc.mul (apHD_pq_cont hu)
  have hφw_pe : Continuous (fun z : Plane => φ z.2 * Cyl.partialEta w z) :=
    hφc.mul (apHD_pe_cont hw)
  -- (q1) integration by parts in `q` for `om²` against `χ u`
  have q1 : ∫ z in Cyl.cell c, Cyl.partialQ (fun z : Plane => om z * om z) z * (φ z.2 * u z)
      = -∫ z in Cyl.cell c, (om z * om z) * (φ z.2 * Cyl.partialQ u z) := by
    have h := Cyl.integral_cell_partialQ_mul (c := c) hc homomd hφud hfp hgup
      (apHD_integ (c := c) (R0 := R0) ((apHD_pq_cont (hom.mul hom)).mul hφu_c)
        (fun z hz => by simp [hφv z.2 hz]))
      (apHD_integ (c := c) (R0 := R0) (homom_c.mul (apHD_pq_cont hφ2u))
        (fun z hz => by simp [hpq_φu, hφv z.2 hz]))
    simp only [hpq_φu] at h
    exact h
  -- (e1) integration by parts in `η` for `om²` against `χ w`
  have e1 : ∫ z in Cyl.cell c, Cyl.partialEta (fun z : Plane => om z * om z) z * (φ z.2 * w z)
      = -∫ z in Cyl.cell c, (om z * om z) * (deriv φ z.2 * w z + φ z.2 * Cyl.partialEta w z) := by
    have h := Cyl.integral_cell_partialEta_mul (c := c) (f := fun z : Plane => om z * om z)
      (g := fun z : Plane => φ z.2 * w z) homomd hφwd
      (apHD_integ (c := c) (R0 := R0) (homom_c.mul hφw_c) (fun z hz => by simp [hφv z.2 hz]))
      (apHD_integ (c := c) (R0 := R0) ((apHD_pe_cont (hom.mul hom)).mul hφw_c)
        (fun z hz => by simp [hφv z.2 hz]))
      (apHD_integ (c := c) (R0 := R0) (homom_c.mul (apHD_pe_cont hφ2w))
        (fun z hz => by simp [hpe_φw, hφv z.2 hz, apHD_deriv_zero hφv hz]))
    simp only [hpe_φw] at h
    exact h
  -- (e2) integration by parts in `η` for `∂_η²om` against `χ om`
  have e2 : ∫ z in Cyl.cell c, Cyl.partialEta (Cyl.partialEta om) z * (φ z.2 * om z)
      = -∫ z in Cyl.cell c, Cyl.partialEta om z * (deriv φ z.2 * om z + φ z.2 * Cyl.partialEta om z) := by
    have h := Cyl.integral_cell_partialEta_mul (c := c) (f := Cyl.partialEta om)
      (g := fun z : Plane => φ z.2 * om z) hpeomd hφomd
      (apHD_integ (c := c) (R0 := R0) (hpeomc.mul hφom_c) (fun z hz => by simp [hφv z.2 hz]))
      (apHD_integ (c := c) (R0 := R0) (hpepec.mul hφom_c) (fun z hz => by simp [hφv z.2 hz]))
      (apHD_integ (c := c) (R0 := R0) (hpeomc.mul (apHD_pe_cont hφ2om))
        (fun z hz => by simp [hpe_φom, hφv z.2 hz, apHD_deriv_zero hφv hz]))
    simp only [hpe_φom] at h
    exact h
  -- (q2) integration by parts in `q` for `∂_q²om` against `χ om`
  have q2 : ∫ z in Cyl.cell c, Cyl.partialQ (Cyl.partialQ om) z * (φ z.2 * om z)
      = -∫ z in Cyl.cell c, Cyl.partialQ om z * (φ z.2 * Cyl.partialQ om z) := by
    have h := Cyl.integral_cell_partialQ_mul (c := c) hc (f := Cyl.partialQ om)
      (g := fun z : Plane => φ z.2 * om z) hpqomd hφomd hpqomp hgomp
      (apHD_integ (c := c) (R0 := R0) (hpqpqc.mul hφom_c) (fun z hz => by simp [hφv z.2 hz]))
      (apHD_integ (c := c) (R0 := R0) (hpqomc.mul (apHD_pq_cont hφ2om))
        (fun z hz => by simp [hpq_φom, hφv z.2 hz]))
    simp only [hpq_φom] at h
    exact h
  -- integrability of the four pieces of the integrand
  have hJ1 : Integrable (fun z : Plane => -(Cyl.partialQ (fun z : Plane => om z * om z) z
      * (φ z.2 * u z))) (volume.restrict (Cyl.cell c)) :=
    apHD_integ (c := c) (R0 := R0) (((apHD_pq_cont (hom.mul hom)).mul hφu_c).neg)
      (fun z hz => by simp [hφv z.2 hz])
  have hJ2 : Integrable (fun z : Plane => -(Cyl.partialEta (fun z : Plane => om z * om z) z
      * (φ z.2 * w z))) (volume.restrict (Cyl.cell c)) :=
    apHD_integ (c := c) (R0 := R0) (((apHD_pe_cont (hom.mul hom)).mul hφw_c).neg)
      (fun z hz => by simp [hφv z.2 hz])
  have hJ3 : Integrable (fun z : Plane => 2 * ν * (Cyl.partialQ (Cyl.partialQ om) z
      * (φ z.2 * om z))) (volume.restrict (Cyl.cell c)) :=
    apHD_integ (c := c) (R0 := R0) ((hpqpqc.mul hφom_c).const_mul (2 * ν))
      (fun z hz => by simp [hφv z.2 hz])
  have hJ4 : Integrable (fun z : Plane => 2 * ν * (Cyl.partialEta (Cyl.partialEta om) z
      * (φ z.2 * om z))) (volume.restrict (Cyl.cell c)) :=
    apHD_integ (c := c) (R0 := R0) ((hpepec.mul hφom_c).const_mul (2 * ν))
      (fun z hz => by simp [hφv z.2 hz])
  -- pointwise decomposition of the integrand
  have hsplit : ∫ z in Cyl.cell c, φ z.2 * (2 * om z * (-(u z * Cyl.partialQ om z
        + w z * Cyl.partialEta om z) + ν * Train.lapS om z))
      = ∫ z in Cyl.cell c, ((-(Cyl.partialQ (fun z : Plane => om z * om z) z * (φ z.2 * u z))
          + -(Cyl.partialEta (fun z : Plane => om z * om z) z * (φ z.2 * w z)))
          + 2 * ν * (Cyl.partialQ (Cyl.partialQ om) z * (φ z.2 * om z)))
          + 2 * ν * (Cyl.partialEta (Cyl.partialEta om) z * (φ z.2 * om z)) := by
    refine integral_congr_ae (ae_of_all _ (fun z => ?_))
    simp only [hpq_f z, hpe_f z, Train.lapS]
    ring
  -- the splitting of the `η`-integrals in the right-hand side
  have hK1 : ∫ z in Cyl.cell c, φ z.2 * (Cyl.partialQ om z ^ 2 + Cyl.partialEta om z ^ 2)
      = (∫ z in Cyl.cell c, Cyl.partialQ om z * (φ z.2 * Cyl.partialQ om z))
        + ∫ z in Cyl.cell c, Cyl.partialEta om z * (φ z.2 * Cyl.partialEta om z) := by
    have hA1 : Integrable (fun z : Plane => Cyl.partialQ om z * (φ z.2 * Cyl.partialQ om z))
        (volume.restrict (Cyl.cell c)) :=
      apHD_integ (c := c) (R0 := R0) (hpqomc.mul (hφc.mul hpqomc))
        (fun z hz => by simp [hφv z.2 hz])
    have hB1 : Integrable (fun z : Plane => Cyl.partialEta om z * (φ z.2 * Cyl.partialEta om z))
        (volume.restrict (Cyl.cell c)) :=
      apHD_integ (c := c) (R0 := R0) (hpeomc.mul (hφc.mul hpeomc))
        (fun z hz => by simp [hφv z.2 hz])
    rw [← integral_add hA1 hB1]
    refine integral_congr_ae (ae_of_all _ (fun z => ?_))
    ring
  have hK2 : ∫ z in Cyl.cell c, Cyl.partialEta om z * (deriv φ z.2 * om z
        + φ z.2 * Cyl.partialEta om z)
      = (∫ z in Cyl.cell c, Cyl.partialEta om z * (deriv φ z.2 * om z))
        + ∫ z in Cyl.cell c, Cyl.partialEta om z * (φ z.2 * Cyl.partialEta om z) := by
    have hC1 : Integrable (fun z : Plane => Cyl.partialEta om z * (deriv φ z.2 * om z))
        (volume.restrict (Cyl.cell c)) :=
      apHD_integ (c := c) (R0 := R0) (hpeomc.mul (hφ'c.mul homc))
        (fun z hz => by simp [apHD_deriv_zero hφv hz])
    have hD1 : Integrable (fun z : Plane => Cyl.partialEta om z * (φ z.2 * Cyl.partialEta om z))
        (volume.restrict (Cyl.cell c)) :=
      apHD_integ (c := c) (R0 := R0) (hpeomc.mul (hφc.mul hpeomc))
        (fun z hz => by simp [hφv z.2 hz])
    rw [← integral_add hC1 hD1]
    refine integral_congr_ae (ae_of_all _ (fun z => ?_))
    ring
  have hK3 : ∫ z in Cyl.cell c, deriv φ z.2 * om z * Cyl.partialEta om z
      = ∫ z in Cyl.cell c, Cyl.partialEta om z * (deriv φ z.2 * om z) :=
    integral_congr_ae (ae_of_all _ (fun z => by ring))
  -- the `q`-part and the `η`-part of the transport term combine with `div v = 0`
  have C1 : (∫ z in Cyl.cell c, (om z * om z) * (φ z.2 * Cyl.partialQ u z))
      + ∫ z in Cyl.cell c, (om z * om z) * (deriv φ z.2 * w z + φ z.2 * Cyl.partialEta w z)
      = ∫ z in Cyl.cell c, om z ^ 2 * w z * deriv φ z.2 := by
    have hP : Integrable (fun z : Plane => (om z * om z) * (φ z.2 * Cyl.partialQ u z))
        (volume.restrict (Cyl.cell c)) :=
      apHD_integ (c := c) (R0 := R0) (homom_c.mul hφu_pq) (fun z hz => by simp [hφv z.2 hz])
    have hQ : Integrable (fun z : Plane => (om z * om z)
        * (deriv φ z.2 * w z + φ z.2 * Cyl.partialEta w z)) (volume.restrict (Cyl.cell c)) :=
      apHD_integ (c := c) (R0 := R0) (homom_c.mul ((hφ'c.mul hwc).add hφw_pe))
        (fun z hz => by simp [hφv z.2 hz, apHD_deriv_zero hφv hz])
    rw [← integral_add hP hQ]
    refine integral_congr_ae (ae_of_all _ (fun z => ?_))
    have hz := hdiv z
    linear_combination ((om z * om z) * φ z.2) * hz
  -- assemble
  have hS12 : Integrable (fun z : Plane => (-(Cyl.partialQ (fun z : Plane => om z * om z) z
      * (φ z.2 * u z))) + -(Cyl.partialEta (fun z : Plane => om z * om z) z * (φ z.2 * w z)))
      (volume.restrict (Cyl.cell c)) := hJ1.add hJ2
  have hS123 : Integrable (fun z : Plane => ((-(Cyl.partialQ (fun z : Plane => om z * om z) z
      * (φ z.2 * u z))) + -(Cyl.partialEta (fun z : Plane => om z * om z) z * (φ z.2 * w z)))
      + 2 * ν * (Cyl.partialQ (Cyl.partialQ om) z * (φ z.2 * om z)))
      (volume.restrict (Cyl.cell c)) := hS12.add hJ3
  rw [hsplit, integral_add hS123 hJ4, integral_add hS12 hJ3, integral_add hJ1 hJ2,
    integral_neg, integral_neg, integral_const_mul, integral_const_mul,
    q1, e1, q2, e2, hK1, hK2, hK3]
  linear_combination C1

/-! ### The leaf -/

/-- **`PartI:T04/6/1/3`**: the cutoff enstrophy has the derivative `apEnstrophyRhs`. -/
theorem apEnstrophyHasDeriv : UnforcedLeray.Short.PartI.APEnstrophyHasDeriv := by
  intro ν c T v p hν hc hcls R hR s hs
  have hR0 : 0 < R := by linarith
  have hc0 : 0 < c := by linarith
  have hW : ContDiffOn ℝ 2 (fun x : ℝ × Plane => Cyl.curl (v x.1) x.2)
      (Ioo 0 T ×ˢ (univ : Set Plane)) :=
    crSmooth hcls.classical.smooth_v
  have hφ : ContDiff ℝ ∞ (etaCutoff R) := ecContDiff R hR0
  have hφ2 : ContDiff ℝ 2 (etaCutoff R) := hφ.of_le (by simp)
  have hφv : ∀ x : ℝ, (2 * R) < |x| → etaCutoff R x = 0 :=
    fun x hx => apHD_eta_zero hR0 hx.le
  have hA := apHD_deriv_integral (φ := etaCutoff R) hφ.continuous hφv (apHD_eta_abs R) hW c hc0
    hs.1 hs.2
  have hvs : ContDiff ℝ 2 (v s) := by
    have h1 : ContDiffOn ℝ ∞ (fun z : Plane => v s z) univ :=
      hcls.classical.smooth_v.comp ((contDiff_const (c := s)).prodMk contDiff_id).contDiffOn
        (fun z _ => ⟨⟨hs.1.le, hs.2.le⟩, mem_univ z⟩)
    exact (contDiffOn_univ.mp h1).of_le (by simp)
  have hu2 : ContDiff ℝ 2 (fun z : Plane => v s z 0) :=
    (EuclideanSpace.proj (𝕜 := ℝ) (0 : Fin 2)).contDiff.comp hvs
  have hw2 : ContDiff ℝ 2 (fun z : Plane => v s z 1) :=
    (EuclideanSpace.proj (𝕜 := ℝ) (1 : Fin 2)).contDiff.comp hvs
  have hom2 : ContDiff ℝ 2 (fun z : Plane => Cyl.curl (v s) z) := by
    have h1 : ContDiffOn ℝ 2 (fun z : Plane => Cyl.curl (v s) z) univ :=
      hW.comp ((contDiff_const (c := s)).prodMk contDiff_id).contDiffOn
        (fun z _ => Set.mk_mem_prod ⟨hs.1, hs.2⟩ (mem_univ z))
    exact contDiffOn_univ.mp h1
  have hper : Cyl.IsPeriodic c (Cyl.curl (v s)) :=
    crPeriodic hcls.classical.periodic_v ⟨hs.1.le, hs.2.le⟩
  have hup : Cyl.IsPeriodic c (fun z : Plane => v s z 0) :=
    (hcls.classical.periodic_v s ⟨hs.1.le, hs.2.le⟩).fun_comp (fun x : Vec => x 0)
  have hdiv : ∀ z : Plane, Cyl.partialQ (fun z : Plane => v s z 0) z
      + Cyl.partialEta (fun z : Plane => v s z 1) z = 0 :=
    fun z => hcls.classical.solenoidal s ⟨hs.1.le, hs.2.le⟩ z
  have hcore := apHD_core (ν := ν) (φ := etaCutoff R) (R0 := 2 * R) hφ2 hc0 hφv hom2 hu2 hw2
    hper hup hdiv
  have hB : ∀ z : Plane,
      fderiv ℝ (fun x : ℝ × Plane => Cyl.curl (v x.1) x.2) (s, z) ((1 : ℝ), (0 : Plane))
        = -(v s z 0 * Cyl.partialQ (Cyl.curl (v s)) z + v s z 1 * Cyl.partialEta (Cyl.curl (v s)) z)
          + ν * Train.lapS (Cyl.curl (v s)) z := by
    intro z
    have h := localVorticityEquation ν c T v p hν hc hcls.pos hcls.classical s hs z
    have hd : deriv (fun t => Cyl.curl (v t) z) s
        = fderiv ℝ (fun x : ℝ × Plane => Cyl.curl (v x.1) x.2) (s, z) ((1 : ℝ), (0 : Plane)) :=
      (apHD_deriv_at hW hs.1 hs.2 z).deriv
    unfold UnforcedLeray.B0238.vorticityResidual at h
    rw [hd] at h
    linarith
  have hfun : apCutoffEnstrophy c v R
      = fun t => ∫ z in Cyl.cell c, etaCutoff R z.2 * (Cyl.curl (v t) z * Cyl.curl (v t) z) := by
    funext t
    unfold apCutoffEnstrophy
    simp only [pow_two]
  rw [hfun]
  have e1 : (∫ z in Cyl.cell c, etaCutoff R z.2 * (fderiv ℝ (fun x : ℝ × Plane => Cyl.curl (v x.1) x.2)
        (s, z) ((1 : ℝ), (0 : Plane)) * Cyl.curl (v s) z
        + Cyl.curl (v s) z * fderiv ℝ (fun x : ℝ × Plane => Cyl.curl (v x.1) x.2) (s, z)
          ((1 : ℝ), (0 : Plane))))
      = ∫ z in Cyl.cell c, etaCutoff R z.2 * (2 * Cyl.curl (v s) z
          * (-(v s z 0 * Cyl.partialQ (Cyl.curl (v s)) z + v s z 1 * Cyl.partialEta (Cyl.curl (v s)) z)
            + ν * Train.lapS (Cyl.curl (v s)) z)) := by
    refine integral_congr_ae (ae_of_all _ (fun z => ?_))
    try dsimp only
    rw [hB z]
    ring
  exact hA.congr_deriv (e1.trans hcore)

end UnforcedLeray.Short.PartI
