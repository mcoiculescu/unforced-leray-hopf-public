import UnforcedLeray.Short.PartIIa.Sub.PartIIa_N05
import Mathlib.Analysis.Fourier.AddCircle

/-!
# 3D Periodic Box Fourier Modes and Parseval Identity (`BoxFourier`)

Sets up the periodic box `Box = Ioc (σ / 2) (H1 + 2) ×ˢ (Ioc 0 c ×ˢ Ioc (-(L1 + 2)) (L1 + 2))`
inside `cell c` for `PartII-a:N06`, defines the 3D exponential modes `mode3D` and Fourier
coefficients `coeff3D`, and proves:
* orthogonality `coeff3D (mode3D m) n = if n = m then 1 else 0`,
* 3D Parseval `∑' n, ENNReal.ofReal (‖coeff3D f n‖ ^ 2) = ENNReal.ofReal (volBox⁻¹ * ∫ ‖f‖ ^ 2)`,
* the `L²(Box)` tail formula for any finite mode set `Λ : Finset (ℤ × ℤ × ℤ)`,
* finite Pythagoras `∫ ‖∑ n ∈ Λ, a n • mode3D n‖ ^ 2 = volBox * ∑ n ∈ Λ, ‖a n‖ ^ 2`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology Complex
open scoped ENNReal NNReal ContDiff InnerProductSpace

namespace UnforcedLeray.Short.PartIIa.N06Aux

open UnforcedLeray.B0220 UnforcedLeray.B0223

/-! ### 1. 1D `fourierCoeffOn` orthogonality and product Parseval step -/

theorem fourierCoeffOn_fourier_eq {a b : ℝ} (hab : a < b) (k l : ℤ) :
    haveI : Fact (0 < b - a) := ⟨sub_pos.2 hab⟩
    fourierCoeffOn hab (fun x : ℝ => @fourier (b - a) k (x : AddCircle (b - a))) l =
      if l = k then 1 else 0 := by
  have hT : Fact (0 < b - a) := ⟨sub_pos.2 hab⟩
  have hlen : b - a ≠ 0 := hT.out.ne'
  rw [fourierCoeffOn_eq_integral]
  simp_rw [smul_eq_mul, ← fourier_add]
  split_ifs with hlk
  · subst hlk
    simp_rw [neg_add_cancel, fourier_zero]
    rw [intervalIntegral.integral_const, smul_smul, one_div_mul_cancel hlen, one_smul]
  · set m : ℤ := k - l
    have hm_eq : -l + k = -(-m) := by omega
    have hm_ne : -m ≠ 0 := neg_ne_zero.2 (sub_ne_zero.2 (Ne.symm hlk))
    simp_rw [hm_eq]
    have hderiv : ∀ x ∈ Set.uIcc a b,
        HasDerivAt (fun y : ℝ =>
          ((b - a : ℝ) : ℂ) / (-2 * Real.pi * I * (-m : ℤ)) *
            @fourier (b - a) (-(-m)) (y : AddCircle (b - a)))
          (@fourier (b - a) (-(-m)) (x : AddCircle (b - a))) x :=
      fun x _ => has_antideriv_at_fourier_neg hT hm_ne x
    have hint : IntervalIntegrable
        (fun x : ℝ => @fourier (b - a) (-(-m)) (x : AddCircle (b - a))) volume a b :=
      ((map_continuous (@fourier (b - a) (-(-m)))).comp
        (AddCircle.continuous_mk' (b - a))).intervalIntegrable a b
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint]
    have hper : (b : AddCircle (b - a)) = (a : AddCircle (b - a)) := by
      simpa [add_sub_cancel] using AddCircle.coe_add_period (b - a) a
    rw [hper, sub_self, real_smul, mul_zero]

/-- Product Parseval step peeling the right factor `Ioc a b` off `ν.prod (volume.restrict (Ioc a b))`. -/
theorem lintegral_tsum_fourierCoeffOn_prod_right {Ω : Type*} [MeasurableSpace Ω]
    {ν : Measure Ω} [SFinite ν] {a b : ℝ} (hab : a < b) {F : Ω × ℝ → ℂ}
    (hF : MemLp F 2 (ν.prod (volume.restrict (Ioc a b)))) :
    (∀ n : ℤ, MemLp (fun z : Ω => fourierCoeffOn hab (fun x => F (z, x)) n) 2 ν) ∧
    (∑' n : ℤ, ∫⁻ z, ENNReal.ofReal (‖fourierCoeffOn hab (fun x => F (z, x)) n‖ ^ 2) ∂ν) =
      ENNReal.ofReal ((b - a)⁻¹ * ∫ z, ‖F z‖ ^ 2 ∂(ν.prod (volume.restrict (Ioc a b)))) := by
  set μI : Measure ℝ := volume.restrict (Ioc a b)
  have hlen_pos : 0 < b - a := sub_pos.2 hab
  have : Fact (0 < b - a) := ⟨hlen_pos⟩
  have hF_meas : AEStronglyMeasurable F (ν.prod μI) := hF.1
  have hF_sq : Integrable (fun z => ‖F z‖ ^ 2) (ν.prod μI) :=
    (memLp_two_iff_integrable_sq_norm hF_meas).1 hF
  have hslice_ae : ∀ᵐ z ∂ν, MemLp (fun x => F (z, x)) 2 μI := by
    filter_upwards [hF_meas.prodMk_left, hF_sq.prod_right_ae] with z h1 h2
    exact (memLp_two_iff_integrable_sq_norm h1).2 h2
  set C : ℤ → Ω → ℂ := fun n z => fourierCoeffOn hab (fun x => F (z, x)) n
  have hC_eq : ∀ (n : ℤ) (z : Ω),
      C n z = (1 / (b - a)) • ∫ x, @fourier (b - a) (-n) (x : AddCircle (b - a)) • F (z, x) ∂μI := by
    intro n z
    simp only [C, fourierCoeffOn_eq_integral, intervalIntegral.integral_of_le hab.le, μI]
  have hC_meas : ∀ n : ℤ, AEStronglyMeasurable (C n) ν := by
    intro n
    have hker_cont : Continuous (fun x : ℝ => @fourier (b - a) (-n) (x : AddCircle (b - a))) :=
      (map_continuous (@fourier (b - a) (-n))).comp (AddCircle.continuous_mk' (b - a))
    have hprod_meas : AEStronglyMeasurable
        (fun p : Ω × ℝ => @fourier (b - a) (-n) (p.2 : AddCircle (b - a)) • F p)
        (ν.prod μI) :=
      (hker_cont.aestronglyMeasurable.comp_snd).smul hF_meas
    have hint_meas : AEStronglyMeasurable
        (fun z : Ω => ∫ x, @fourier (b - a) (-n) (x : AddCircle (b - a)) • F (z, x) ∂μI) ν :=
      hprod_meas.integral_prod_right'
    rw [funext (hC_eq n)]
    exact hint_meas.const_smul (1 / (b - a))
  have hdom_int : Integrable (fun z : Ω => (b - a)⁻¹ * ∫ x, ‖F (z, x)‖ ^ 2 ∂μI) ν := by
    have h1 := hF_sq.integral_norm_prod_left
    have hrew : (fun z : Ω => ∫ x, ‖‖F (z, x)‖ ^ 2‖ ∂μI) = fun z => ∫ x, ‖F (z, x)‖ ^ 2 ∂μI := by
      ext z
      refine integral_congr_ae (Eventually.of_forall fun x => Real.norm_of_nonneg (sq_nonneg _))
    rw [hrew] at h1
    exact h1.const_mul (b - a)⁻¹
  have hC_memLp : ∀ n : ℤ, MemLp (C n) 2 ν := by
    intro n
    refine (memLp_two_iff_integrable_sq_norm (hC_meas n)).2 ?_
    refine hdom_int.mono' ((hC_meas n).norm.pow 2) ?_
    filter_upwards [hslice_ae] with z hz
    rw [Real.norm_of_nonneg (sq_nonneg _)]
    have hsum := hasSum_sq_fourierCoeffOn hab hz
    have hle := Summable.le_tsum hsum.summable n (fun i _ => sq_nonneg _)
    rw [hsum.tsum_eq, intervalIntegral.integral_of_le hab.le, smul_eq_mul] at hle
    exact hle
  refine ⟨hC_memLp, ?_⟩
  have haemeas : ∀ n : ℤ, AEMeasurable (fun z : Ω => ENNReal.ofReal (‖C n z‖ ^ 2)) ν :=
    fun n => ((hC_meas n).norm.pow 2).aemeasurable.ennreal_ofReal
  rw [← lintegral_tsum haemeas]
  have hcongr : (fun z : Ω => ∑' n : ℤ, ENNReal.ofReal (‖C n z‖ ^ 2)) =ᵐ[ν]
      fun z : Ω => ENNReal.ofReal ((b - a)⁻¹ * ∫ x, ‖F (z, x)‖ ^ 2 ∂μI) := by
    filter_upwards [hslice_ae] with z hz
    have hsum := hasSum_sq_fourierCoeffOn hab hz
    rw [← ENNReal.ofReal_tsum_of_nonneg (fun n => sq_nonneg _) hsum.summable,
      hsum.tsum_eq, intervalIntegral.integral_of_le hab.le, smul_eq_mul]
  rw [lintegral_congr_ae hcongr,
    ← ofReal_integral_eq_lintegral_ofReal hdom_int
      (Eventually.of_forall fun z => mul_nonneg (inv_nonneg.2 hlen_pos.le)
        (integral_nonneg fun _ => sq_nonneg _)),
    integral_const_mul]
  congr 2
  exact (MeasureTheory.integral_prod _ hF_sq).symm

/-! ### 2. 3D Box Geometry and Measures -/

/-- Parameters defining the 3D periodic Fourier box around `[σ, H1] × (0, c] × [-L1, L1]`. -/
structure BoxParams where
  c : ℝ
  σ : ℝ
  H1 : ℝ
  L1 : ℝ
  hc : 0 < c
  hσ : 0 < σ
  hσH1 : σ ≤ H1
  hL1 : 0 ≤ L1

namespace BoxParams

def as (B : BoxParams) : ℝ := B.σ / 2
def bs (B : BoxParams) : ℝ := B.H1 + 2
def Ts (B : BoxParams) : ℝ := B.bs - B.as

def aη (B : BoxParams) : ℝ := -(B.L1 + 2)
def bη (B : BoxParams) : ℝ := B.L1 + 2
def Tη (B : BoxParams) : ℝ := B.bη - B.aη

def Is (B : BoxParams) : Set ℝ := Ioc B.as B.bs
def Iq (B : BoxParams) : Set ℝ := Ioc 0 B.c
def Iη (B : BoxParams) : Set ℝ := Ioc B.aη B.bη

def boxSet (B : BoxParams) : Set Profile := B.Is ×ˢ (B.Iq ×ˢ B.Iη)
def volBox (B : BoxParams) : ℝ := B.Ts * B.c * B.Tη
def boxMeas (B : BoxParams) : Measure Profile := volume.restrict B.boxSet

theorem has_pos (B : BoxParams) : 0 < B.as := half_pos B.hσ

theorem has_lt_bs (B : BoxParams) : B.as < B.bs := by
  unfold as bs
  have := B.hσ
  have := B.hσH1
  linarith

theorem hTs_gt_two (B : BoxParams) : 2 < B.Ts := by
  unfold Ts bs as
  have := B.hσ
  have := B.hσH1
  linarith

theorem hTs_pos (B : BoxParams) : 0 < B.Ts := by linarith [B.hTs_gt_two]

theorem haη_lt_bη (B : BoxParams) : B.aη < B.bη := by
  unfold aη bη
  have := B.hL1
  linarith

theorem hTη_ge_four (B : BoxParams) : 4 ≤ B.Tη := by
  unfold Tη bη aη
  have := B.hL1
  linarith

theorem hTη_pos (B : BoxParams) : 0 < B.Tη := by linarith [B.hTη_ge_four]

theorem hvolBox_pos (B : BoxParams) : 0 < B.volBox :=
  mul_pos (mul_pos B.hTs_pos B.hc) B.hTη_pos

theorem measurableSet_boxSet (B : BoxParams) : MeasurableSet B.boxSet :=
  measurableSet_Ioc.prod (measurableSet_Ioc.prod measurableSet_Ioc)

theorem boxSet_subset_cell (B : BoxParams) : B.boxSet ⊆ cell B.c := by
  rintro ⟨s, q, η⟩ ⟨hs, hq, _⟩
  exact ⟨lt_trans B.has_pos hs.1, hq, trivial⟩

theorem mem_boxSet_of_obs (B : BoxParams) {p : Profile}
    (hpq : p.2.1 ∈ Ioc 0 B.c) (hps : B.σ ≤ p.1 ∧ p.1 ≤ B.H1) (hpη : |p.2.2| ≤ B.L1) :
    p ∈ B.boxSet := by
  rw [abs_le] at hpη
  refine ⟨⟨?_, ?_⟩, hpq, ⟨?_, ?_⟩⟩
  · unfold as; linarith [B.hσ]
  · unfold bs; linarith
  · unfold aη; linarith
  · unfold bη; linarith

theorem boxMeas_eq_prod (B : BoxParams) :
    B.boxMeas =
      (volume.restrict B.Is).prod ((volume.restrict B.Iq).prod (volume.restrict B.Iη)) := by
  unfold boxMeas boxSet
  rw [Measure.volume_eq_prod (α := ℝ) (β := ℝ × ℝ),
    Measure.volume_eq_prod (α := ℝ) (β := ℝ),
    Measure.prod_restrict, Measure.prod_restrict]

theorem cellMeasure_restrict_boxSet (B : BoxParams) :
    (cellMeasure B.c).restrict B.boxSet = B.boxMeas := by
  unfold cellMeasure boxMeas
  exact Measure.restrict_restrict_of_subset B.boxSet_subset_cell

theorem boxMeas_univ (B : BoxParams) : B.boxMeas univ = ENNReal.ofReal B.volBox := by
  unfold boxMeas boxSet
  rw [Measure.restrict_apply_univ,
    Measure.volume_eq_prod (α := ℝ) (β := ℝ × ℝ), Measure.prod_prod,
    Measure.volume_eq_prod (α := ℝ) (β := ℝ), Measure.prod_prod]
  simp only [Is, Iq, Iη, Real.volume_Ioc, sub_zero]
  change ENNReal.ofReal B.Ts * (ENNReal.ofReal B.c * ENNReal.ofReal B.Tη) = ENNReal.ofReal B.volBox
  rw [← ENNReal.ofReal_mul B.hc.le, ← ENNReal.ofReal_mul B.hTs_pos.le, ← mul_assoc]
  rfl

instance isFiniteMeasure_boxMeas (B : BoxParams) : IsFiniteMeasure B.boxMeas :=
  ⟨by rw [B.boxMeas_univ]; exact ENNReal.ofReal_lt_top⟩

instance isFiniteMeasure_restrict_Is (B : BoxParams) : IsFiniteMeasure (volume.restrict B.Is) :=
  ⟨by unfold Is; simp⟩

instance isFiniteMeasure_restrict_Iq (B : BoxParams) : IsFiniteMeasure (volume.restrict B.Iq) :=
  ⟨by unfold Iq; simp⟩

instance isFiniteMeasure_restrict_Iη (B : BoxParams) : IsFiniteMeasure (volume.restrict B.Iη) :=
  ⟨by unfold Iη; simp⟩

theorem integral_cellMeasure_eq_boxMeas (B : BoxParams) {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] {g : Profile → E}
    (hsupp : ∀ p : Profile, g p ≠ 0 → B.σ ≤ p.1 ∧ p.1 ≤ B.H1 ∧ |p.2.2| ≤ B.L1) :
    ∫ p, g p ∂(cellMeasure B.c) = ∫ p, g p ∂B.boxMeas := by
  rw [← B.cellMeasure_restrict_boxSet, ← integral_indicator B.measurableSet_boxSet]
  refine integral_congr_ae ?_
  filter_upwards [ae_restrict_mem (measurableSet_cell B.c)] with p hp
  by_cases hg0 : g p = 0
  · simp [Set.indicator, hg0]
  · obtain ⟨hs1, hs2, hη⟩ := hsupp p hg0
    have hmem : p ∈ B.boxSet := B.mem_boxSet_of_obs hp.2.1 ⟨hs1, hs2⟩ hη
    simp [Set.indicator, hmem]

/-! ### 3. 3D Modes `mode3D` and Fourier Coefficients `coeff3D` -/

/-- Phase linear functional `L_n (s, q, η) = 2π (n₁ s / Ts + n₂ q / c + n₃ η / Tη)`. -/
def phaseCLM (B : BoxParams) (n : ℤ × ℤ × ℤ) : Profile →L[ℝ] ℝ :=
  (2 * Real.pi * (n.1 : ℝ) / B.Ts) • ContinuousLinearMap.fst ℝ ℝ (ℝ × ℝ) +
  (2 * Real.pi * (n.2.1 : ℝ) / B.c) •
    ((ContinuousLinearMap.fst ℝ ℝ ℝ).comp (ContinuousLinearMap.snd ℝ ℝ (ℝ × ℝ))) +
  (2 * Real.pi * (n.2.2 : ℝ) / B.Tη) •
    ((ContinuousLinearMap.snd ℝ ℝ ℝ).comp (ContinuousLinearMap.snd ℝ ℝ (ℝ × ℝ)))

@[simp]
theorem phaseCLM_apply (B : BoxParams) (n : ℤ × ℤ × ℤ) (p : Profile) :
    B.phaseCLM n p =
      2 * Real.pi * (n.1 : ℝ) / B.Ts * p.1 +
      2 * Real.pi * (n.2.1 : ℝ) / B.c * p.2.1 +
      2 * Real.pi * (n.2.2 : ℝ) / B.Tη * p.2.2 := rfl

/-- 3D complex exponential mode `exp(i L_n(p))`. -/
def mode3D (B : BoxParams) (n : ℤ × ℤ × ℤ) (p : Profile) : ℂ :=
  Complex.exp (I * (B.phaseCLM n p : ℂ))

theorem contDiff_mode3D (B : BoxParams) (n : ℤ × ℤ × ℤ) : ContDiff ℝ ∞ (B.mode3D n) := by
  unfold mode3D
  exact (Complex.contDiff_exp (𝕜 := ℝ)).comp
    ((contDiff_const (c := I)).mul (Complex.ofRealCLM.contDiff.comp (B.phaseCLM n).contDiff))

theorem mode3D_eq_fourier_prod (B : BoxParams) (n : ℤ × ℤ × ℤ) (p : Profile) :
    B.mode3D n p =
      @fourier B.Ts n.1 (p.1 : AddCircle B.Ts) *
      @fourier B.c n.2.1 (p.2.1 : AddCircle B.c) *
      @fourier B.Tη n.2.2 (p.2.2 : AddCircle B.Tη) := by
  rw [fourier_coe_apply, fourier_coe_apply, fourier_coe_apply,
    ← Complex.exp_add, ← Complex.exp_add]
  unfold mode3D
  congr 1
  rw [B.phaseCLM_apply]
  push_cast
  ring

theorem conj_mode3D_eq_fourier_prod (B : BoxParams) (n : ℤ × ℤ × ℤ) (p : Profile) :
    starRingEnd ℂ (B.mode3D n p) =
      @fourier B.Ts (-n.1) (p.1 : AddCircle B.Ts) *
      @fourier B.c (-n.2.1) (p.2.1 : AddCircle B.c) *
      @fourier B.Tη (-n.2.2) (p.2.2 : AddCircle B.Tη) := by
  rw [B.mode3D_eq_fourier_prod, map_mul, map_mul, ← fourier_neg, ← fourier_neg, ← fourier_neg]

theorem norm_mode3D (B : BoxParams) (n : ℤ × ℤ × ℤ) (p : Profile) : ‖B.mode3D n p‖ = 1 := by
  unfold mode3D
  rw [mul_comm I _, Complex.norm_exp_ofReal_mul_I]

theorem qPeriodic_mode3D (B : BoxParams) (n : ℤ × ℤ × ℤ) : QPeriodic B.c (B.mode3D n) := by
  intro p
  rw [B.mode3D_eq_fourier_prod, B.mode3D_eq_fourier_prod]
  have hper : ((p.2.1 + B.c : ℝ) : AddCircle B.c) = (p.2.1 : AddCircle B.c) :=
    AddCircle.coe_add_period B.c p.2.1
  simp only [hper]

/-- 3D box Fourier coefficient of a scalar profile `f : Profile → ℂ`. -/
def coeff3D (B : BoxParams) (f : Profile → ℂ) (n : ℤ × ℤ × ℤ) : ℂ :=
  (B.volBox⁻¹ : ℝ) • ∫ p, starRingEnd ℂ (B.mode3D n p) * f p ∂B.boxMeas

theorem integrable_conj_mode3D_mul (B : BoxParams) {f : Profile → ℂ}
    (hf : Integrable f B.boxMeas) (n : ℤ × ℤ × ℤ) :
    Integrable (fun p => starRingEnd ℂ (B.mode3D n p) * f p) B.boxMeas := by
  refine hf.mono ?_ ?_
  · exact ((continuous_star.comp (B.contDiff_mode3D n).continuous).aestronglyMeasurable).mul hf.1
  · refine Eventually.of_forall fun p => ?_
    rw [norm_mul, RCLike.norm_conj, B.norm_mode3D, one_mul]

theorem coeff3D_add (B : BoxParams) {f g : Profile → ℂ}
    (hf : Integrable f B.boxMeas) (hg : Integrable g B.boxMeas) (n : ℤ × ℤ × ℤ) :
    B.coeff3D (fun p => f p + g p) n = B.coeff3D f n + B.coeff3D g n := by
  unfold coeff3D
  simp_rw [mul_add]
  rw [integral_add (B.integrable_conj_mode3D_mul hf n) (B.integrable_conj_mode3D_mul hg n),
    smul_add]

theorem coeff3D_sub (B : BoxParams) {f g : Profile → ℂ}
    (hf : Integrable f B.boxMeas) (hg : Integrable g B.boxMeas) (n : ℤ × ℤ × ℤ) :
    B.coeff3D (fun p => f p - g p) n = B.coeff3D f n - B.coeff3D g n := by
  unfold coeff3D
  simp_rw [mul_sub]
  rw [integral_sub (B.integrable_conj_mode3D_mul hf n) (B.integrable_conj_mode3D_mul hg n),
    smul_sub]

theorem coeff3D_const_mul (B : BoxParams) (α : ℂ) (f : Profile → ℂ) (n : ℤ × ℤ × ℤ) :
    B.coeff3D (fun p => α * f p) n = α * B.coeff3D f n := by
  unfold coeff3D
  have hrew : (fun p => starRingEnd ℂ (B.mode3D n p) * (α * f p)) =
      fun p => α * (starRingEnd ℂ (B.mode3D n p) * f p) :=
    funext fun p => by ring
  rw [hrew, integral_const_mul, real_smul, real_smul]
  ring

theorem coeff3D_finset_sum (B : BoxParams) {ι : Type*} (s : Finset ι) (g : ι → Profile → ℂ)
    (hg : ∀ i ∈ s, Integrable (g i) B.boxMeas) (n : ℤ × ℤ × ℤ) :
    B.coeff3D (fun p => ∑ i ∈ s, g i p) n = ∑ i ∈ s, B.coeff3D (g i) n := by
  unfold coeff3D
  simp_rw [Finset.mul_sum]
  rw [integral_finsetSum s (fun i hi => B.integrable_conj_mode3D_mul (hg i hi) n), Finset.smul_sum]

/-- Iterated 1D `fourierCoeffOn` representation of `coeff3D` for `f ∈ L¹(B.boxMeas)`. -/
theorem coeff3D_eq_iterated (B : BoxParams) {f : Profile → ℂ}
    (hf : Integrable f B.boxMeas) (n : ℤ × ℤ × ℤ) :
    B.coeff3D f n =
      fourierCoeffOn B.has_lt_bs
        (fun s => fourierCoeffOn B.hc
          (fun q => fourierCoeffOn B.haη_lt_bη (fun η => f (s, q, η)) n.2.2) n.2.1) n.1 := by
  have hint_prod : Integrable (fun p : Profile => starRingEnd ℂ (B.mode3D n p) * f p)
      ((volume.restrict B.Is).prod ((volume.restrict B.Iq).prod (volume.restrict B.Iη))) := by
    rw [← B.boxMeas_eq_prod]
    exact B.integrable_conj_mode3D_mul hf n
  have h1 := MeasureTheory.integral_prod _ hint_prod
  have h2_ae := hint_prod.prod_right_ae
  unfold coeff3D
  rw [B.boxMeas_eq_prod, h1]
  have hcongr_s : ∫ s, (∫ r : ℝ × ℝ, starRingEnd ℂ (B.mode3D n (s, r)) * f (s, r)
        ∂((volume.restrict B.Iq).prod (volume.restrict B.Iη))) ∂(volume.restrict B.Is) =
      ∫ s, @fourier B.Ts (-n.1) (s : AddCircle B.Ts) *
        (∫ q, @fourier B.c (-n.2.1) (q : AddCircle B.c) *
          (∫ η, @fourier B.Tη (-n.2.2) (η : AddCircle B.Tη) * f (s, q, η)
            ∂(volume.restrict B.Iη)) ∂(volume.restrict B.Iq)) ∂(volume.restrict B.Is) := by
    refine integral_congr_ae ?_
    filter_upwards [h2_ae] with s hs_int
    rw [MeasureTheory.integral_prod _ hs_int]
    simp_rw [B.conj_mode3D_eq_fourier_prod]
    have hpull_s : (fun q : ℝ => ∫ η, (@fourier B.Ts (-n.1) (s : AddCircle B.Ts) *
        @fourier B.c (-n.2.1) (q : AddCircle B.c) *
        @fourier B.Tη (-n.2.2) (η : AddCircle B.Tη)) * f (s, q, η) ∂(volume.restrict B.Iη)) =
        fun q : ℝ => @fourier B.Ts (-n.1) (s : AddCircle B.Ts) *
          (@fourier B.c (-n.2.1) (q : AddCircle B.c) *
            ∫ η, @fourier B.Tη (-n.2.2) (η : AddCircle B.Tη) * f (s, q, η)
              ∂(volume.restrict B.Iη)) := by
      ext q
      rw [← integral_const_mul, ← integral_const_mul]
      refine integral_congr_ae (Eventually.of_forall fun η => by ring)
    rw [hpull_s, integral_const_mul]
  rw [hcongr_s]
  have h_eta : ∀ (s q : ℝ),
      fourierCoeffOn B.haη_lt_bη (fun η => f (s, q, η)) n.2.2 =
        (B.Tη : ℂ)⁻¹ * ∫ η, @fourier B.Tη (-n.2.2) (η : AddCircle B.Tη) * f (s, q, η)
          ∂(volume.restrict B.Iη) := by
    intro s q
    rw [fourierCoeffOn_eq_integral, intervalIntegral.integral_of_le B.haη_lt_bη.le,
      show B.bη - B.aη = B.Tη from rfl, show Ioc B.aη B.bη = B.Iη from rfl]
    simp_rw [smul_eq_mul]
    rw [real_smul]
    push_cast
    ring
  have h_q : ∀ s : ℝ,
      fourierCoeffOn B.hc
        (fun q => fourierCoeffOn B.haη_lt_bη (fun η => f (s, q, η)) n.2.2) n.2.1 =
        ((B.c : ℂ)⁻¹ * (B.Tη : ℂ)⁻¹) * ∫ q, @fourier B.c (-n.2.1) (q : AddCircle B.c) *
          (∫ η, @fourier B.Tη (-n.2.2) (η : AddCircle B.Tη) * f (s, q, η)
            ∂(volume.restrict B.Iη)) ∂(volume.restrict B.Iq) := by
    intro s
    simp_rw [h_eta s]
    rw [fourierCoeffOn_eq_integral, intervalIntegral.integral_of_le B.hc.le, sub_zero,
      show Ioc 0 B.c = B.Iq from rfl]
    simp_rw [smul_eq_mul]
    rw [real_smul]
    have hpull_q :
        (∫ q, @fourier B.c (-n.2.1) (q : AddCircle B.c) *
          ((B.Tη : ℂ)⁻¹ * ∫ η, @fourier B.Tη (-n.2.2) (η : AddCircle B.Tη) * f (s, q, η)
            ∂(volume.restrict B.Iη)) ∂(volume.restrict B.Iq)) =
        (B.Tη : ℂ)⁻¹ * ∫ q, @fourier B.c (-n.2.1) (q : AddCircle B.c) *
          (∫ η, @fourier B.Tη (-n.2.2) (η : AddCircle B.Tη) * f (s, q, η)
            ∂(volume.restrict B.Iη)) ∂(volume.restrict B.Iq) := by
      rw [← integral_const_mul]
      exact integral_congr_ae (Eventually.of_forall fun q => by ring)
    rw [hpull_q]
    push_cast
    ring
  simp_rw [h_q]
  rw [fourierCoeffOn_eq_integral, intervalIntegral.integral_of_le B.has_lt_bs.le,
    show B.bs - B.as = B.Ts from rfl, show Ioc B.as B.bs = B.Is from rfl]
  simp_rw [smul_eq_mul]
  rw [real_smul, real_smul]
  have hpull_s2 :
      (∫ s, @fourier B.Ts (-n.1) (s : AddCircle B.Ts) *
        (((B.c : ℂ)⁻¹ * (B.Tη : ℂ)⁻¹) * ∫ q, @fourier B.c (-n.2.1) (q : AddCircle B.c) *
          (∫ η, @fourier B.Tη (-n.2.2) (η : AddCircle B.Tη) * f (s, q, η)
            ∂(volume.restrict B.Iη)) ∂(volume.restrict B.Iq)) ∂(volume.restrict B.Is)) =
      ((B.c : ℂ)⁻¹ * (B.Tη : ℂ)⁻¹) *
        ∫ s, @fourier B.Ts (-n.1) (s : AddCircle B.Ts) *
          (∫ q, @fourier B.c (-n.2.1) (q : AddCircle B.c) *
            (∫ η, @fourier B.Tη (-n.2.2) (η : AddCircle B.Tη) * f (s, q, η)
              ∂(volume.restrict B.Iη)) ∂(volume.restrict B.Iq)) ∂(volume.restrict B.Is) := by
    rw [← integral_const_mul]
    exact integral_congr_ae (Eventually.of_forall fun s => by ring)
  rw [hpull_s2]
  unfold volBox
  push_cast
  ring

theorem memLp_mode3D (B : BoxParams) (m : ℤ × ℤ × ℤ) : MemLp (B.mode3D m) 2 B.boxMeas := by
  refine MemLp.of_bound (B.contDiff_mode3D m).continuous.aestronglyMeasurable 1 ?_
  exact Eventually.of_forall fun p => (B.norm_mode3D m p).le

theorem integrable_mode3D (B : BoxParams) (m : ℤ × ℤ × ℤ) : Integrable (B.mode3D m) B.boxMeas :=
  (B.memLp_mode3D m).integrable one_le_two

/-- Exact orthogonality of `mode3D` on `B.boxMeas`. -/
theorem coeff3D_mode3D (B : BoxParams) (m n : ℤ × ℤ × ℤ) :
    B.coeff3D (B.mode3D m) n = if n = m then 1 else 0 := by
  rw [B.coeff3D_eq_iterated (B.integrable_mode3D m) n]
  simp_rw [B.mode3D_eq_fourier_prod]
  have hη : ∀ (s q : ℝ),
      fourierCoeffOn B.haη_lt_bη
        (fun η => (@fourier B.Ts m.1 (s : AddCircle B.Ts) *
          @fourier B.c m.2.1 (q : AddCircle B.c)) *
          @fourier B.Tη m.2.2 (η : AddCircle B.Tη)) n.2.2 =
        (@fourier B.Ts m.1 (s : AddCircle B.Ts) * @fourier B.c m.2.1 (q : AddCircle B.c)) *
          (if n.2.2 = m.2.2 then 1 else 0) := by
    intro s q
    rw [fourierCoeffOn.const_mul]
    congr 1
    exact fourierCoeffOn_fourier_eq B.haη_lt_bη m.2.2 n.2.2
  simp_rw [hη]
  have hq : ∀ s : ℝ,
      fourierCoeffOn B.hc
        (fun q => (@fourier B.Ts m.1 (s : AddCircle B.Ts) *
          @fourier B.c m.2.1 (q : AddCircle B.c)) *
          (if n.2.2 = m.2.2 then (1 : ℂ) else 0)) n.2.1 =
        @fourier B.Ts m.1 (s : AddCircle B.Ts) *
          (if n.2.1 = m.2.1 then 1 else 0) * (if n.2.2 = m.2.2 then 1 else 0) := by
    intro s
    have hrew : (fun q : ℝ => (@fourier B.Ts m.1 (s : AddCircle B.Ts) *
        @fourier B.c m.2.1 (q : AddCircle B.c)) *
        (if n.2.2 = m.2.2 then (1 : ℂ) else 0)) =
        fun q : ℝ => (@fourier B.Ts m.1 (s : AddCircle B.Ts) *
          (if n.2.2 = m.2.2 then (1 : ℂ) else 0)) *
          @fourier B.c m.2.1 (q : AddCircle B.c) :=
      funext fun _ => by ring
    rw [hrew, fourierCoeffOn.const_mul]
    have hc_orth : fourierCoeffOn (show (0 : ℝ) < B.c from B.hc)
        (fun q : ℝ => @fourier B.c m.2.1 (q : AddCircle B.c)) n.2.1 =
        if n.2.1 = m.2.1 then 1 else 0 := by
      simpa [sub_zero] using fourierCoeffOn_fourier_eq B.hc m.2.1 n.2.1
    rw [hc_orth]
    ring
  simp_rw [hq]
  have hrew_s : (fun s : ℝ => @fourier B.Ts m.1 (s : AddCircle B.Ts) *
      (if n.2.1 = m.2.1 then (1 : ℂ) else 0) * (if n.2.2 = m.2.2 then 1 else 0)) =
      fun s : ℝ => ((if n.2.1 = m.2.1 then (1 : ℂ) else 0) *
        (if n.2.2 = m.2.2 then 1 else 0)) * @fourier B.Ts m.1 (s : AddCircle B.Ts) :=
    funext fun _ => by ring
  rw [hrew_s, fourierCoeffOn.const_mul]
  have hs_orth : fourierCoeffOn B.has_lt_bs
      (fun s : ℝ => @fourier B.Ts m.1 (s : AddCircle B.Ts)) n.1 =
      if n.1 = m.1 then 1 else 0 :=
    fourierCoeffOn_fourier_eq B.has_lt_bs m.1 n.1
  rw [hs_orth]
  rcases m with ⟨m1, m2, m3⟩
  rcases n with ⟨n1, n2, n3⟩
  by_cases h1 : n1 = m1 <;> by_cases h2 : n2 = m2 <;> by_cases h3 : n3 = m3 <;>
    simp [Prod.ext_iff, h1, h2, h3]

/-! ### 4. 3D Parseval, Finite-Sum Tail Identity, and Pythagoras -/

/-- **3D Parseval identity** on `B.boxMeas` in `ℝ≥0∞`. -/
theorem tsum_coeff3D_sq (B : BoxParams) {f : Profile → ℂ} (hf : MemLp f 2 B.boxMeas) :
    (∑' n : ℤ × ℤ × ℤ, ENNReal.ofReal (‖B.coeff3D f n‖ ^ 2)) =
      ENNReal.ofReal (B.volBox⁻¹ * ∫ p, ‖f p‖ ^ 2 ∂B.boxMeas) := by
  have hf_int : Integrable f B.boxMeas := hf.integrable one_le_two
  let e : ((ℝ × ℝ) × ℝ) ≃ᵐ Profile := MeasurableEquiv.prodAssoc
  have hmp : MeasurePreserving e
      (((volume.restrict B.Is).prod (volume.restrict B.Iq)).prod (volume.restrict B.Iη))
      B.boxMeas := by
    rw [B.boxMeas_eq_prod]
    exact MeasureTheory.measurePreserving_prodAssoc
      (volume.restrict B.Is) (volume.restrict B.Iq) (volume.restrict B.Iη)
  have hf_assoc : MemLp (f ∘ e) 2
      (((volume.restrict B.Is).prod (volume.restrict B.Iq)).prod (volume.restrict B.Iη)) :=
    hf.comp_measurePreserving hmp
  obtain ⟨hC1_mem, hsum1⟩ :=
    lintegral_tsum_fourierCoeffOn_prod_right
      (ν := (volume.restrict B.Is).prod (volume.restrict B.Iq)) B.haη_lt_bη hf_assoc
  set C1 : ℤ → ℝ × ℝ → ℂ := fun n3 sq =>
    fourierCoeffOn B.haη_lt_bη (fun η => f (sq.1, sq.2, η)) n3
  set C2 : ℤ → ℤ → ℝ → ℂ := fun n3 n2 s =>
    fourierCoeffOn B.hc (fun q => C1 n3 (s, q)) n2
  have hstep2 : ∀ n3 : ℤ,
      (∀ n2 : ℤ, MemLp (C2 n3 n2) 2 (volume.restrict B.Is)) ∧
      (∑' n2 : ℤ, ∫⁻ s, ENNReal.ofReal (‖C2 n3 n2 s‖ ^ 2) ∂(volume.restrict B.Is)) =
        ENNReal.ofReal (B.c⁻¹ *
          ∫ sq, ‖C1 n3 sq‖ ^ 2 ∂((volume.restrict B.Is).prod (volume.restrict B.Iq))) := by
    intro n3
    have h := lintegral_tsum_fourierCoeffOn_prod_right (ν := volume.restrict B.Is) B.hc (hC1_mem n3)
    rw [sub_zero] at h
    exact h
  have hstep3 : ∀ (n3 n2 : ℤ),
      (∑' n1 : ℤ, ENNReal.ofReal (‖B.coeff3D f (n1, n2, n3)‖ ^ 2)) =
        ENNReal.ofReal (B.Ts⁻¹ * ∫ s, ‖C2 n3 n2 s‖ ^ 2 ∂(volume.restrict B.Is)) := by
    intro n3 n2
    have hmem := (hstep2 n3).1 n2
    have hsum := hasSum_sq_fourierCoeffOn B.has_lt_bs hmem
    have hcoeff : ∀ n1 : ℤ,
        B.coeff3D f (n1, n2, n3) = fourierCoeffOn B.has_lt_bs (C2 n3 n2) n1 :=
      fun n1 => B.coeff3D_eq_iterated hf_int (n1, n2, n3)
    simp_rw [hcoeff]
    rw [← ENNReal.ofReal_tsum_of_nonneg (fun _ => sq_nonneg _) hsum.summable,
      hsum.tsum_eq, intervalIntegral.integral_of_le B.has_lt_bs.le, smul_eq_mul]
    rfl
  let swap3 : (ℤ × ℤ × ℤ) ≃ (ℤ × ℤ × ℤ) :=
    { toFun := fun n => (n.2.2, n.2.1, n.1)
      invFun := fun n => (n.2.2, n.2.1, n.1)
      left_inv := fun ⟨_, _, _⟩ => rfl
      right_inv := fun ⟨_, _, _⟩ => rfl }
  rw [← swap3.tsum_eq, ENNReal.tsum_prod']
  simp_rw [ENNReal.tsum_prod']
  change (∑' n3 : ℤ, ∑' n2 : ℤ, ∑' n1 : ℤ, ENNReal.ofReal (‖B.coeff3D f (n1, n2, n3)‖ ^ 2)) = _
  simp_rw [hstep3]
  have hstep2' : ∀ n3 : ℤ,
      (∑' n2 : ℤ, ENNReal.ofReal (B.Ts⁻¹ * ∫ s, ‖C2 n3 n2 s‖ ^ 2 ∂(volume.restrict B.Is))) =
        ENNReal.ofReal (B.Ts⁻¹ * (B.c⁻¹ *
          ∫ sq, ‖C1 n3 sq‖ ^ 2 ∂((volume.restrict B.Is).prod (volume.restrict B.Iq)))) := by
    intro n3
    have hmul : ∀ n2 : ℤ,
        ENNReal.ofReal (B.Ts⁻¹ * ∫ s, ‖C2 n3 n2 s‖ ^ 2 ∂(volume.restrict B.Is)) =
          ENNReal.ofReal B.Ts⁻¹ *
            ∫⁻ s, ENNReal.ofReal (‖C2 n3 n2 s‖ ^ 2) ∂(volume.restrict B.Is) := by
      intro n2
      have hmem := (hstep2 n3).1 n2
      have hsq : Integrable (fun s => ‖C2 n3 n2 s‖ ^ 2) (volume.restrict B.Is) :=
        (memLp_two_iff_integrable_sq_norm hmem.1).1 hmem
      rw [ENNReal.ofReal_mul (inv_nonneg.2 B.hTs_pos.le),
        ofReal_integral_eq_lintegral_ofReal hsq (Eventually.of_forall fun _ => sq_nonneg _)]
    simp_rw [hmul, ENNReal.tsum_mul_left, (hstep2 n3).2,
      ← ENNReal.ofReal_mul (inv_nonneg.2 B.hTs_pos.le)]
  simp_rw [hstep2']
  have hmul1 : ∀ n3 : ℤ,
      ENNReal.ofReal (B.Ts⁻¹ * (B.c⁻¹ *
        ∫ sq, ‖C1 n3 sq‖ ^ 2 ∂((volume.restrict B.Is).prod (volume.restrict B.Iq)))) =
        ENNReal.ofReal (B.Ts⁻¹ * B.c⁻¹) *
          ∫⁻ sq, ENNReal.ofReal (‖C1 n3 sq‖ ^ 2)
            ∂((volume.restrict B.Is).prod (volume.restrict B.Iq)) := by
    intro n3
    have hmem := hC1_mem n3
    have hsq : Integrable (fun sq => ‖C1 n3 sq‖ ^ 2)
        ((volume.restrict B.Is).prod (volume.restrict B.Iq)) :=
      (memLp_two_iff_integrable_sq_norm hmem.1).1 hmem
    rw [← mul_assoc,
      ENNReal.ofReal_mul (mul_nonneg (inv_nonneg.2 B.hTs_pos.le) (inv_nonneg.2 B.hc.le)),
      ofReal_integral_eq_lintegral_ofReal hsq (Eventually.of_forall fun _ => sq_nonneg _)]
  simp_rw [hmul1]
  rw [ENNReal.tsum_mul_left]
  have hsum1' : (∑' n3 : ℤ, ∫⁻ sq, ENNReal.ofReal (‖C1 n3 sq‖ ^ 2)
      ∂((volume.restrict B.Is).prod (volume.restrict B.Iq))) =
      ENNReal.ofReal (B.Tη⁻¹ *
        ∫ z, ‖(f ∘ e) z‖ ^ 2
          ∂(((volume.restrict B.Is).prod (volume.restrict B.Iq)).prod (volume.restrict B.Iη))) :=
    hsum1
  rw [hsum1', ← ENNReal.ofReal_mul (mul_nonneg (inv_nonneg.2 B.hTs_pos.le) (inv_nonneg.2 B.hc.le))]
  congr 1
  have hint_eq : ∫ z, ‖(f ∘ e) z‖ ^ 2
      ∂(((volume.restrict B.Is).prod (volume.restrict B.Iq)).prod (volume.restrict B.Iη)) =
      ∫ p, ‖f p‖ ^ 2 ∂B.boxMeas :=
    hmp.integral_comp' (fun p => ‖f p‖ ^ 2)
  rw [hint_eq]
  unfold volBox
  field_simp

/-- Finite trigonometric polynomial `∑ n ∈ Λ, a n * mode3D n p`. -/
def trigSum (B : BoxParams) (Λ : Finset (ℤ × ℤ × ℤ)) (a : (ℤ × ℤ × ℤ) → ℂ) (p : Profile) : ℂ :=
  ∑ n ∈ Λ, a n * B.mode3D n p

theorem memLp_trigSum (B : BoxParams) (Λ : Finset (ℤ × ℤ × ℤ)) (a : (ℤ × ℤ × ℤ) → ℂ) :
    MemLp (B.trigSum Λ a) 2 B.boxMeas := by
  unfold trigSum
  exact memLp_finsetSum Λ fun n _ => (B.memLp_mode3D n).const_mul (a n)

theorem coeff3D_trigSum (B : BoxParams) (Λ : Finset (ℤ × ℤ × ℤ)) (a : (ℤ × ℤ × ℤ) → ℂ)
    (m : ℤ × ℤ × ℤ) :
    B.coeff3D (B.trigSum Λ a) m = if m ∈ Λ then a m else 0 := by
  unfold trigSum
  rw [B.coeff3D_finset_sum Λ (fun n p => a n * B.mode3D n p)
    (fun n _ => (B.integrable_mode3D n).const_mul (a n)) m]
  simp_rw [B.coeff3D_const_mul, B.coeff3D_mode3D]
  by_cases hm : m ∈ Λ
  · simp only [hm, ↓reduceIte]
    rw [Finset.sum_eq_single m]
    · simp
    · intro n _ hnm; simp [hnm.symm]
    · intro hm'; exact absurd hm hm'
  · simp only [hm, ↓reduceIte]
    refine Finset.sum_eq_zero fun n hn => ?_
    have hmn : m ≠ n := fun h => hm (h ▸ hn)
    simp [hmn]

/-- **Finite Pythagoras** on `B.boxMeas`: `∫ ‖∑ n ∈ Λ, a n * mode3D n‖² = volBox * ∑ n ∈ Λ, ‖a n‖²`. -/
theorem integral_trigSum_sq (B : BoxParams) (Λ : Finset (ℤ × ℤ × ℤ)) (a : (ℤ × ℤ × ℤ) → ℂ) :
    ∫ p, ‖B.trigSum Λ a p‖ ^ 2 ∂B.boxMeas = B.volBox * ∑ n ∈ Λ, ‖a n‖ ^ 2 := by
  have hparseval := B.tsum_coeff3D_sq (B.memLp_trigSum Λ a)
  simp_rw [B.coeff3D_trigSum Λ a] at hparseval
  have hite : (fun n : ℤ × ℤ × ℤ => ENNReal.ofReal (‖if n ∈ Λ then a n else 0‖ ^ 2)) =
      fun n => if n ∈ Λ then ENNReal.ofReal (‖a n‖ ^ 2) else 0 := by
    ext n
    by_cases hn : n ∈ Λ <;> simp [hn]
  rw [hite, tsum_eq_sum (s := Λ) (fun n hn => by simp [hn])] at hparseval
  have hfin : (∑ n ∈ Λ, if n ∈ Λ then ENNReal.ofReal (‖a n‖ ^ 2) else 0) =
      ENNReal.ofReal (∑ n ∈ Λ, ‖a n‖ ^ 2) := by
    rw [ENNReal.ofReal_sum_of_nonneg (fun _ _ => sq_nonneg _)]
    exact Finset.sum_congr rfl fun n hn => by simp [hn]
  rw [hfin] at hparseval
  have hnn1 : 0 ≤ ∑ n ∈ Λ, ‖a n‖ ^ 2 := Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hnn2 : 0 ≤ B.volBox⁻¹ * ∫ p, ‖B.trigSum Λ a p‖ ^ 2 ∂B.boxMeas :=
    mul_nonneg (inv_nonneg.2 B.hvolBox_pos.le) (integral_nonneg fun _ => sq_nonneg _)
  have heq_real : (∑ n ∈ Λ, ‖a n‖ ^ 2) =
      B.volBox⁻¹ * ∫ p, ‖B.trigSum Λ a p‖ ^ 2 ∂B.boxMeas := by
    have := congr_arg ENNReal.toReal hparseval
    rwa [ENNReal.toReal_ofReal hnn1, ENNReal.toReal_ofReal hnn2] at this
  have hv_ne : B.volBox ≠ 0 := B.hvolBox_pos.ne'
  calc ∫ p, ‖B.trigSum Λ a p‖ ^ 2 ∂B.boxMeas
      = B.volBox * (B.volBox⁻¹ * ∫ p, ‖B.trigSum Λ a p‖ ^ 2 ∂B.boxMeas) := by
          rw [← mul_assoc, mul_inv_cancel₀ hv_ne, one_mul]
    _ = B.volBox * ∑ n ∈ Λ, ‖a n‖ ^ 2 := by rw [← heq_real]

/-- **Exact `L²(Box)` high-frequency tail identity** for any `f ∈ L²(B.boxMeas)` and finite `Λ`. -/
theorem ofReal_integral_sub_trigSum_sq (B : BoxParams) {f : Profile → ℂ}
    (hf : MemLp f 2 B.boxMeas) (Λ : Finset (ℤ × ℤ × ℤ)) :
    ENNReal.ofReal (∫ p, ‖f p - B.trigSum Λ (B.coeff3D f) p‖ ^ 2 ∂B.boxMeas) =
      ENNReal.ofReal B.volBox *
        ∑' n : ℤ × ℤ × ℤ, if n ∈ Λ then 0 else ENNReal.ofReal (‖B.coeff3D f n‖ ^ 2) := by
  set g : Profile → ℂ := fun p => f p - B.trigSum Λ (B.coeff3D f) p
  have hg_mem : MemLp g 2 B.boxMeas := hf.sub (B.memLp_trigSum Λ (B.coeff3D f))
  have hf_int : Integrable f B.boxMeas := hf.integrable one_le_two
  have htrig_int : Integrable (B.trigSum Λ (B.coeff3D f)) B.boxMeas :=
    (B.memLp_trigSum Λ (B.coeff3D f)).integrable one_le_two
  have hg_coeff : ∀ m : ℤ × ℤ × ℤ,
      B.coeff3D g m = if m ∈ Λ then 0 else B.coeff3D f m := by
    intro m
    rw [B.coeff3D_sub hf_int htrig_int m, B.coeff3D_trigSum Λ (B.coeff3D f) m]
    by_cases hm : m ∈ Λ <;> simp [hm]
  have hparseval := B.tsum_coeff3D_sq hg_mem
  have hite : (fun n : ℤ × ℤ × ℤ => ENNReal.ofReal (‖B.coeff3D g n‖ ^ 2)) =
      fun n => if n ∈ Λ then 0 else ENNReal.ofReal (‖B.coeff3D f n‖ ^ 2) := by
    ext n
    rw [hg_coeff n]
    by_cases hn : n ∈ Λ <;> simp [hn]
  rw [hite] at hparseval
  rw [hparseval, ← ENNReal.ofReal_mul B.hvolBox_pos.le,
    ← mul_assoc, mul_inv_cancel₀ B.hvolBox_pos.ne', one_mul]

end BoxParams

end UnforcedLeray.Short.PartIIa.N06Aux
