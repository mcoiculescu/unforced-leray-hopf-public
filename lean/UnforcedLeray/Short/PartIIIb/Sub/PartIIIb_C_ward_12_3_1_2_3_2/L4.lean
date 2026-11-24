import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_ward_12_3_1_2_3_2
import UnforcedLeray.Lib.SobolevB.Mollify

/-!
# Lemma 4: approximate identity on `L^{q₀}(phaseμ P)` with gating (source 2531)

Source of record `the November 2 reference manuscript`,
line 2531 (spatial mollification in each period slice).

Proof outline:
* slice approximate identity `Moll (ρ n) f → f` in `L^{q₀}(ℝ³)` (`tendsto_cv_sub`), from the
  translation continuity of `L^{q₀}` and the mass-one, support-shrinking kernels;
* slice bound `‖gate - F‖_{q₀,slice} ≤ 2‖F_τ‖_{q₀}` (Young with an `L¹` kernel of mass one);
* dominated convergence in the period variable `τ` with dominator `2^{q₀} ∫ ‖F(τ,·)‖^{q₀}`.
-/

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.PartIIIb.Concrete

open UnforcedLeray.PhaseSpace MeasureTheory Set Filter
open scoped ENNReal ContDiff Topology

/-- The spatial mollification is the library convolution `Sob.cv` with Lebesgue measure. -/
lemma moll_eq_cv (ρ : UnforcedLeray.Space → ℝ)
    (f : UnforcedLeray.Space → UnforcedLeray.PhaseSpace.CVec3) :
    Moll ρ f = UnforcedLeray.Sob.cv volume ρ f := by
  funext y
  rw [UnforcedLeray.Sob.cv_apply]
  rfl

lemma lintegral_enorm_kernel {φ : UnforcedLeray.Space → ℝ} (hφ : Continuous φ)
    (hφs : HasCompactSupport φ) (hnn : ∀ y, 0 ≤ φ y) (hint : ∫ y, φ y = 1) :
    ∫⁻ t, ‖φ t‖ₑ ∂(volume : Measure UnforcedLeray.Space) = 1 := by
  have h := ofReal_integral_eq_lintegral_ofReal
    (hφ.integrable_of_hasCompactSupport (μ := (volume : Measure UnforcedLeray.Space)) hφs)
    (Eventually.of_forall hnn)
  rw [hint, ENNReal.ofReal_one] at h
  rw [h]
  refine lintegral_congr fun t => ?_
  rw [Real.enorm_eq_ofReal (hnn t)]

/-- Young's inequality for a mass-one kernel: mollification does not increase `L^p` norms. -/
lemma eLpNorm_cv_kernel_le {φ : UnforcedLeray.Space → ℝ} (hφ : Continuous φ)
    (hφs : HasCompactSupport φ) (hnn : ∀ y, 0 ≤ φ y) (hint : ∫ y, φ y = 1)
    {f : UnforcedLeray.Space → UnforcedLeray.PhaseSpace.CVec3}
    (hf : AEStronglyMeasurable f volume) {p : ENNReal} (hp : 1 ≤ p) (hp' : p ≠ ⊤) :
    eLpNorm (UnforcedLeray.Sob.cv volume φ f) p volume ≤ eLpNorm f p volume := by
  have := UnforcedLeray.Sob.eLpNorm_cv_le (μ := volume) hφ hf hp hp'
  rwa [lintegral_enorm_kernel hφ hφs hnn hint, one_mul] at this

/-- Mollifier error for a mass-one kernel supported in the ball of radius `r`. -/
lemma eLpNorm_cv_sub_le {φ : UnforcedLeray.Space → ℝ} (hφ : Continuous φ)
    (hφs : HasCompactSupport φ) (hnn : ∀ y, 0 ≤ φ y) (hint : ∫ y, φ y = 1) {r : ℝ}
    (hsupp : ∀ h : UnforcedLeray.Space, r < ‖h‖ → φ h = 0)
    {f : UnforcedLeray.Space → UnforcedLeray.PhaseSpace.CVec3} {p : ENNReal}
    (hf : MemLp f p volume) (hp : 1 ≤ p) (hp' : p ≠ ⊤) {η : ENNReal}
    (hη : ∀ h : UnforcedLeray.Space, ‖h‖ ≤ r →
      eLpNorm (fun y => f (y + h) - f y) p volume ≤ η) :
    eLpNorm (fun x => UnforcedLeray.Sob.cv volume φ f x - f x) p volume ≤ η := by
  have hloc : LocallyIntegrable f volume := hf.locallyIntegrable hp
  have hasm : AEStronglyMeasurable f volume := hf.aestronglyMeasurable
  have hint1 : Integrable φ volume := hφ.integrable_of_hasCompactSupport hφs
  have hrepr : ∀ x, UnforcedLeray.Sob.cv volume φ f x - f x
      = ∫ t, φ t • (f (x - t) - f x) := by
    intro x
    rw [UnforcedLeray.Sob.cv_apply_swap]
    have h1 := UnforcedLeray.Sob.integrable_kernel_swap hφ hφs hloc x
    have h2 : Integrable (fun t => φ t • f x) volume := hint1.smul_const (f x)
    simp_rw [smul_sub]
    rw [integral_sub h1 h2, integral_smul_const, hint, one_smul]
  rw [show (fun x => UnforcedLeray.Sob.cv volume φ f x - f x)
      = fun x => ∫ t, φ t • (f (x - t) - f x) from funext hrepr]
  have hmeas : AEStronglyMeasurable
      (Function.uncurry fun x t => φ t • (f (x - t) - f x)) (volume.prod volume) := by
    have h1 := UnforcedLeray.Sob.aestronglyMeasurable_kernel_prod (μ := volume) hφ hasm
    have h2 : AEStronglyMeasurable
        (fun z : UnforcedLeray.Space × UnforcedLeray.Space => φ z.2 • f z.1)
        (volume.prod volume) :=
      (hφ.comp continuous_snd).aestronglyMeasurable.smul hasm.comp_fst
    refine (h1.sub h2).congr (Eventually.of_forall fun z => ?_)
    simp [Function.uncurry, smul_sub]
  refine (NonUniqueEuler.Conv.eLpNorm_integral_le hmeas hp hp').trans ?_
  calc ∫⁻ t, eLpNorm (fun x => φ t • (f (x - t) - f x)) p volume ∂volume
      ≤ ∫⁻ t, ‖φ t‖ₑ * η ∂volume := by
        refine lintegral_mono fun t => ?_
        rw [show (fun x => φ t • (f (x - t) - f x)) = φ t • (fun x => f (x - t) - f x) from rfl,
          eLpNorm_const_smul]
        by_cases ht : ‖t‖ ≤ r
        · have h3 : eLpNorm (fun x => f (x - t) - f x) p volume ≤ η := by
            have := hη (-t) (by rw [norm_neg]; exact ht)
            simpa only [sub_eq_add_neg] using this
          gcongr
        · have h0 : φ t = 0 := hsupp t (not_le.mp ht)
          simp [h0]
    _ = η := by
        rw [lintegral_mul_const _ hφ.measurable.enorm,
          lintegral_enorm_kernel hφ hφs hnn hint, one_mul]

/-- Slice approximate identity: `Moll (ρ n) f → f` in `L^p`, `1 ≤ p < ∞`, for a mollifier
sequence `ρ` (`MollSeq ρ`). -/
lemma tendsto_cv_sub {ρ : ℕ → UnforcedLeray.Space → ℝ} (hρ : MollSeq ρ)
    {p : ENNReal} (hp1 : 1 ≤ p) (hp : p ≠ ⊤)
    {f : UnforcedLeray.Space → UnforcedLeray.PhaseSpace.CVec3} (hf : MemLp f p volume) :
    Tendsto (fun n => eLpNorm (fun x => UnforcedLeray.Sob.cv volume (ρ n) f x - f x) p volume)
      atTop (𝓝 0) := by
  have : Fact (1 ≤ p) := ⟨hp1⟩
  rw [ENNReal.tendsto_nhds_zero]
  intro ε hε
  have ht := UnforcedLeray.Sob.tendsto_eLpNorm_translate_sub hp hf
  rw [ENNReal.tendsto_nhds_zero] at ht
  obtain ⟨δ, hδ, hball⟩ := Metric.mem_nhds_iff.mp (ht ε hε)
  have hr : Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 1)) atTop (𝓝 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat
  have hev : ∀ᶠ n : ℕ in atTop, 1 / ((n : ℝ) + 1) < δ := hr.eventually (gt_mem_nhds hδ)
  filter_upwards [hev] with n hn
  obtain ⟨hdiff, hcs, hnn, hint, hsub⟩ := hρ n
  refine eLpNorm_cv_sub_le hdiff.continuous hcs hnn hint (r := 1 / ((n : ℝ) + 1)) ?_ hf hp1 hp ?_
  · intro h hh
    apply image_eq_zero_of_notMem_tsupport
    intro hmem
    have := hsub hmem
    rw [mem_closedBall_zero_iff] at this
    linarith
  · intro h hh
    exact hball (mem_ball_zero_iff.mpr (lt_of_le_of_lt hh hn))

/-- Level-`n` gated slice mollification of `F` (`gate (A n)` applied to the spatial mollification
of each period slice). -/
def gateMoll (ρ : ℕ → UnforcedLeray.Space → ℝ)
    (F : ℝ × UnforcedLeray.Space → UnforcedLeray.PhaseSpace.CVec3) (A : ℕ → Set ℝ) (n : ℕ) :
    ℝ × UnforcedLeray.Space → UnforcedLeray.PhaseSpace.CVec3 :=
  gate (A n) (fun x => Moll (ρ n) (fun z => F (x.1, z)) x.2)

lemma gateMoll_sm {ρ : ℕ → UnforcedLeray.Space → ℝ} (hρ : MollSeq ρ)
    {F : ℝ × UnforcedLeray.Space → UnforcedLeray.PhaseSpace.CVec3}
    (hF : StronglyMeasurable F) (A : ℕ → Set ℝ) (hA : ∀ n, MeasurableSet (A n)) (n : ℕ) :
    StronglyMeasurable (gateMoll ρ F A n) :=
  (stronglyMeasurable_moll (hρ n).1.continuous hF).indicator (measurable_fst (hA n))

lemma gateMoll_eq_cv {ρ : ℕ → UnforcedLeray.Space → ℝ}
    {F : ℝ × UnforcedLeray.Space → UnforcedLeray.PhaseSpace.CVec3} {A : ℕ → Set ℝ} {n : ℕ}
    {τ : ℝ} (hτ : τ ∈ A n) (y : UnforcedLeray.Space) :
    gateMoll ρ F A n (τ, y) = UnforcedLeray.Sob.cv volume (ρ n) (fun z => F (τ, z)) y := by
  rw [← moll_eq_cv]
  exact gate_of_mem (F := fun x => Moll (ρ n) (fun z => F (x.1, z)) x.2) hτ y

/-- Slice norm of the gated mollification is at most that of `F`. -/
lemma eLpNorm_gateMoll_slice_le {ρ : ℕ → UnforcedLeray.Space → ℝ} (hρ : MollSeq ρ)
    {F : ℝ × UnforcedLeray.Space → UnforcedLeray.PhaseSpace.CVec3}
    (hF : StronglyMeasurable F) (A : ℕ → Set ℝ) (n : ℕ) (τ : ℝ) {p : ENNReal} (hp1 : 1 ≤ p)
    (hp : p ≠ ⊤) :
    eLpNorm (fun y => gateMoll ρ F A n (τ, y)) p volume
      ≤ eLpNorm (fun y => F (τ, y)) p volume := by
  have hFτ : AEStronglyMeasurable (fun z => F (τ, z)) volume :=
    (hF.comp_measurable (measurable_const.prodMk measurable_id)).aestronglyMeasurable
  by_cases hτ : τ ∈ A n
  · rw [show (fun y => gateMoll ρ F A n (τ, y))
        = UnforcedLeray.Sob.cv volume (ρ n) (fun z => F (τ, z)) from funext fun y =>
          gateMoll_eq_cv hτ y]
    exact eLpNorm_cv_kernel_le (hρ n).1.continuous (hρ n).2.1 (hρ n).2.2.1 (hρ n).2.2.2.1 hFτ
      hp1 hp
  · have hG : (fun y => gateMoll ρ F A n (τ, y)) = fun _ => 0 := by
      funext y
      exact gate_of_not_mem hτ y
    rw [hG, show (fun _ : UnforcedLeray.Space => (0 : UnforcedLeray.PhaseSpace.CVec3)) = 0
      from rfl, eLpNorm_zero]
    exact zero_le

/-- Slice error bound: `‖gate - F‖_{p,slice} ≤ 2 ‖F_τ‖_{p}`. -/
lemma eLpNorm_gateMoll_sub_le {ρ : ℕ → UnforcedLeray.Space → ℝ} (hρ : MollSeq ρ)
    {F : ℝ × UnforcedLeray.Space → UnforcedLeray.PhaseSpace.CVec3}
    (hF : StronglyMeasurable F) (A : ℕ → Set ℝ) (hA : ∀ n, MeasurableSet (A n)) (n : ℕ)
    (τ : ℝ) {p : ENNReal} (hp1 : 1 ≤ p) (hp : p ≠ ⊤) :
    eLpNorm (fun y => gateMoll ρ F A n (τ, y) - F (τ, y)) p volume
      ≤ 2 * eLpNorm (fun y => F (τ, y)) p volume := by
  have hGτ : AEStronglyMeasurable (fun y => gateMoll ρ F A n (τ, y)) volume :=
    ((gateMoll_sm hρ hF A hA n).comp_measurable
      (measurable_const.prodMk measurable_id)).aestronglyMeasurable
  have hFτ : AEStronglyMeasurable (fun y => F (τ, y)) volume :=
    (hF.comp_measurable (measurable_const.prodMk measurable_id)).aestronglyMeasurable
  calc eLpNorm (fun y => gateMoll ρ F A n (τ, y) - F (τ, y)) p volume
      ≤ eLpNorm (fun y => gateMoll ρ F A n (τ, y)) p volume
          + eLpNorm (fun y => F (τ, y)) p volume := eLpNorm_sub_le hGτ hFτ hp1
    _ ≤ eLpNorm (fun y => F (τ, y)) p volume + eLpNorm (fun y => F (τ, y)) p volume :=
        add_le_add (eLpNorm_gateMoll_slice_le hρ hF A n τ hp1 hp) le_rfl
    _ = 2 * eLpNorm (fun y => F (τ, y)) p volume := (two_mul _).symm

/-- Pure ENNReal identity: `eLpNorm f q μ ^ q = ∫⁻ ‖f‖ₑ^q` for `0 < q < ∞`. -/
lemma mc_eLpNorm_rpow {α E : Type*} [MeasurableSpace α] [NormedAddCommGroup E]
    {μ : Measure α} {f : α → E} {q : ENNReal} (hq0 : q ≠ 0) (hqtop : q ≠ ⊤) :
    eLpNorm f q μ ^ q.toReal = ∫⁻ x, ‖f x‖ₑ ^ q.toReal ∂μ := by
  have hne : q.toReal ≠ 0 := ENNReal.toReal_ne_zero.2 ⟨hq0, hqtop⟩
  rw [eLpNorm_eq_lintegral_rpow_enorm hq0 hqtop, ← ENNReal.rpow_mul, one_div_mul_cancel hne,
    ENNReal.rpow_one]

/-- Slice energy `∫ ‖F(τ,y)‖^{q₀} dy`. -/
def sliceEnergy (F : ℝ × UnforcedLeray.Space → UnforcedLeray.PhaseSpace.CVec3) (p τ : ℝ) :
    ENNReal :=
  ∫⁻ y, ‖F (τ, y)‖ₑ ^ p

/-- Slice error `∫ ‖gate(τ,y) - F(τ,y)‖^{q₀} dy`. -/
def sliceErr (ρ : ℕ → UnforcedLeray.Space → ℝ)
    (F : ℝ × UnforcedLeray.Space → UnforcedLeray.PhaseSpace.CVec3) (A : ℕ → Set ℝ) (n : ℕ)
    (p τ : ℝ) : ENNReal :=
  ∫⁻ y, ‖gateMoll ρ F A n (τ, y) - F (τ, y)‖ₑ ^ p

lemma sliceErr_le_energy {ρ : ℕ → UnforcedLeray.Space → ℝ} (hρ : MollSeq ρ)
    {F : ℝ × UnforcedLeray.Space → UnforcedLeray.PhaseSpace.CVec3}
    (hF : StronglyMeasurable F) (A : ℕ → Set ℝ) (hA : ∀ n, MeasurableSet (A n)) (n : ℕ)
    (τ : ℝ) :
    sliceErr ρ F A n UnforcedLeray.B0412.q0E.toReal τ
      ≤ (2 : ENNReal) ^ UnforcedLeray.B0412.q0E.toReal
          * sliceEnergy F UnforcedLeray.B0412.q0E.toReal τ := by
  have hq1 : (1 : ENNReal) ≤ UnforcedLeray.B0412.q0E := UnforcedLeray.B0412.one_lt_q0E.le
  have hqtop : UnforcedLeray.B0412.q0E ≠ ⊤ := UnforcedLeray.B0412.q0E_ne_top
  have hq0 : UnforcedLeray.B0412.q0E ≠ 0 := (lt_of_lt_of_le zero_lt_one hq1).ne'
  have hp0' : (0 : ℝ) ≤ UnforcedLeray.B0412.q0E.toReal :=
    (ENNReal.toReal_pos hq0 hqtop).le
  calc sliceErr ρ F A n UnforcedLeray.B0412.q0E.toReal τ
      = eLpNorm (fun y => gateMoll ρ F A n (τ, y) - F (τ, y)) UnforcedLeray.B0412.q0E volume
          ^ UnforcedLeray.B0412.q0E.toReal :=
        (mc_eLpNorm_rpow hq0 hqtop).symm
    _ ≤ (2 * eLpNorm (fun y => F (τ, y)) UnforcedLeray.B0412.q0E volume)
          ^ UnforcedLeray.B0412.q0E.toReal :=
        ENNReal.rpow_le_rpow (eLpNorm_gateMoll_sub_le hρ hF A hA n τ hq1 hqtop) hp0'
    _ = (2 : ENNReal) ^ UnforcedLeray.B0412.q0E.toReal
          * eLpNorm (fun y => F (τ, y)) UnforcedLeray.B0412.q0E volume
            ^ UnforcedLeray.B0412.q0E.toReal :=
        ENNReal.mul_rpow_of_nonneg _ _ hp0'
    _ = (2 : ENNReal) ^ UnforcedLeray.B0412.q0E.toReal
          * sliceEnergy F UnforcedLeray.B0412.q0E.toReal τ :=
        congrArg (fun t => (2 : ENNReal) ^ UnforcedLeray.B0412.q0E.toReal * t)
          (mc_eLpNorm_rpow hq0 hqtop)

/-- Lemma 4 (approximate identity on `L^{q₀}(phaseμ P)` with gating; source 2531). -/
theorem mollConv : MollConv := by
  intro ρ hρ P hP F hF hFm A hA hcover
  have hq1 : (1 : ENNReal) ≤ UnforcedLeray.B0412.q0E := UnforcedLeray.B0412.one_lt_q0E.le
  have hqtop : UnforcedLeray.B0412.q0E ≠ ⊤ := UnforcedLeray.B0412.q0E_ne_top
  have hq0 : UnforcedLeray.B0412.q0E ≠ 0 := (lt_of_lt_of_le zero_lt_one hq1).ne'
  have hp0 : 0 < UnforcedLeray.B0412.q0E.toReal := ENNReal.toReal_pos hq0 hqtop
  have hp0' : (0 : ℝ) ≤ UnforcedLeray.B0412.q0E.toReal := hp0.le
  have hFmeas : Measurable F := hF.measurable
  -- Fubini splitting of the phase measure
  have hsplit : ∀ g : ℝ × UnforcedLeray.Space → ENNReal, AEMeasurable g (phaseμ P) →
      ∫⁻ x, g x ∂(phaseμ P)
        = ∫⁻ τ, ∫⁻ y, g (τ, y) ∂volume ∂(volume.restrict (Ioc (0 : ℝ) P)) :=
    fun g hg => lintegral_prod g hg
  have hJm : Measurable (fun τ : ℝ => sliceEnergy F UnforcedLeray.B0412.q0E.toReal τ) :=
    Measurable.lintegral_prod_right' (hFmeas.enorm.pow_const UnforcedLeray.B0412.q0E.toReal)
  have hsumEnergy : ∫⁻ τ, sliceEnergy F UnforcedLeray.B0412.q0E.toReal τ
      ∂(volume.restrict (Ioc (0 : ℝ) P))
        = ∫⁻ x, ‖F x‖ₑ ^ UnforcedLeray.B0412.q0E.toReal ∂(phaseμ P) :=
    (hsplit (fun x => ‖F x‖ₑ ^ UnforcedLeray.B0412.q0E.toReal)
      (hFmeas.enorm.pow_const _).aemeasurable).symm
  have hFint : ∫⁻ x, ‖F x‖ₑ ^ UnforcedLeray.B0412.q0E.toReal ∂(phaseμ P) ≠ ⊤ := by
    rw [← mc_eLpNorm_rpow (f := F) (μ := phaseμ P) hq0 hqtop]
    exact (ENNReal.rpow_lt_top_of_nonneg hp0' hFm.2.ne).ne
  have hmeasErr : ∀ n, Measurable (fun τ => sliceErr ρ F A n UnforcedLeray.B0412.q0E.toReal τ) :=
    fun n => Measurable.lintegral_prod_right'
      (f := fun x : ℝ × UnforcedLeray.Space =>
        ‖gateMoll ρ F A n x - F x‖ₑ ^ UnforcedLeray.B0412.q0E.toReal)
      ((((gateMoll_sm hρ hF A hA n).sub hF).measurable.enorm).pow_const _)
  have hsplitn : ∀ n, ∫⁻ x, ‖gateMoll ρ F A n x - F x‖ₑ ^ UnforcedLeray.B0412.q0E.toReal ∂(phaseμ P)
      = ∫⁻ τ, sliceErr ρ F A n UnforcedLeray.B0412.q0E.toReal τ
          ∂(volume.restrict (Ioc (0 : ℝ) P)) :=
    fun n => hsplit (fun x => ‖gateMoll ρ F A n x - F x‖ₑ ^ UnforcedLeray.B0412.q0E.toReal)
      ((((gateMoll_sm hρ hF A hA n).sub hF).measurable.enorm).pow_const _).aemeasurable
  have hbfin : ∫⁻ τ, (2 : ENNReal) ^ UnforcedLeray.B0412.q0E.toReal
      * sliceEnergy F UnforcedLeray.B0412.q0E.toReal τ ∂(volume.restrict (Ioc (0 : ℝ) P)) ≠ ⊤ := by
    rw [lintegral_const_mul _ hJm, hsumEnergy]
    exact ENNReal.mul_ne_top (ENNReal.rpow_lt_top_of_nonneg hp0' (by norm_num : (2 : ENNReal) ≠ ⊤)).ne hFint
  -- a.e. slice convergence
  have hJfin : ∀ᵐ τ ∂(volume.restrict (Ioc (0 : ℝ) P)),
      sliceEnergy F UnforcedLeray.B0412.q0E.toReal τ < ⊤ :=
    ae_lt_top hJm (by rw [hsumEnergy]; exact hFint)
  have hlim : ∀ᵐ τ ∂(volume.restrict (Ioc (0 : ℝ) P)),
      Tendsto (fun n => sliceErr ρ F A n UnforcedLeray.B0412.q0E.toReal τ) atTop (𝓝 0) := by
    filter_upwards [hJfin, hcover] with τ hJτ hτ
    obtain ⟨N, hN⟩ := hτ
    have hFτm : AEStronglyMeasurable (fun y => F (τ, y)) volume :=
      (hF.comp_measurable (measurable_const.prodMk measurable_id)).aestronglyMeasurable
    have hmem : MemLp (fun y => F (τ, y)) UnforcedLeray.B0412.q0E volume := by
      refine ⟨hFτm, ?_⟩
      by_contra hcon
      rw [not_lt, top_le_iff] at hcon
      have hrw := mc_eLpNorm_rpow (f := fun y => F (τ, y)) (μ := volume) hq0 hqtop
      rw [hcon, ENNReal.top_rpow_of_pos hp0] at hrw
      exact (ne_of_lt hJτ) hrw.symm
    have hconv := tendsto_cv_sub hρ hq1 hqtop hmem
    have hconv' : Tendsto (fun n => eLpNorm
        (fun x => UnforcedLeray.Sob.cv volume (ρ n) (fun z => F (τ, z)) x
          - (fun z => F (τ, z)) x) UnforcedLeray.B0412.q0E volume ^ UnforcedLeray.B0412.q0E.toReal)
        atTop (𝓝 0) := by
      have h2 : Tendsto (fun n => eLpNorm
          (fun x => UnforcedLeray.Sob.cv volume (ρ n) (fun z => F (τ, z)) x
            - (fun z => F (τ, z)) x) UnforcedLeray.B0412.q0E volume
            ^ UnforcedLeray.B0412.q0E.toReal) atTop
          (𝓝 ((0 : ENNReal) ^ UnforcedLeray.B0412.q0E.toReal)) :=
        (ENNReal.continuous_rpow_const.tendsto 0).comp hconv
      rwa [ENNReal.zero_rpow_of_pos hp0] at h2
    have hev : ∀ᶠ n in atTop,
        sliceErr ρ F A n UnforcedLeray.B0412.q0E.toReal τ
          = eLpNorm (fun x => UnforcedLeray.Sob.cv volume (ρ n) (fun z => F (τ, z)) x
              - (fun z => F (τ, z)) x) UnforcedLeray.B0412.q0E volume
            ^ UnforcedLeray.B0412.q0E.toReal := by
      filter_upwards [eventually_ge_atTop N] with n hn
      have hτn : τ ∈ A n := hN n hn
      rw [mc_eLpNorm_rpow hq0 hqtop]
      unfold sliceErr
      simp only [gateMoll_eq_cv hτn]
    exact hconv'.congr' (hev.mono fun n hn => hn.symm)
  -- dominated convergence in the period variable
  have hI : Tendsto (fun n => ∫⁻ τ, sliceErr ρ F A n UnforcedLeray.B0412.q0E.toReal τ
      ∂(volume.restrict (Ioc (0 : ℝ) P))) atTop (𝓝 0) := by
    have h := tendsto_lintegral_of_dominated_convergence
      (μ := volume.restrict (Ioc (0 : ℝ) P))
      (f := fun _ => (0 : ENNReal))
      (fun τ => (2 : ENNReal) ^ UnforcedLeray.B0412.q0E.toReal
        * sliceEnergy F UnforcedLeray.B0412.q0E.toReal τ)
      (fun n => hmeasErr n)
      (fun n => Eventually.of_forall fun τ => sliceErr_le_energy hρ hF A hA n τ)
      hbfin hlim
    simpa only [lintegral_zero] using h
  have hI' : Tendsto (fun n => ∫⁻ x, ‖gateMoll ρ F A n x - F x‖ₑ
      ^ UnforcedLeray.B0412.q0E.toReal ∂(phaseμ P)) atTop (𝓝 0) :=
    Tendsto.congr (fun n => (hsplitn n).symm) hI
  have hfinal : Tendsto (fun n => (∫⁻ x, ‖gateMoll ρ F A n x - F x‖ₑ
      ^ UnforcedLeray.B0412.q0E.toReal ∂(phaseμ P)) ^ (1 / UnforcedLeray.B0412.q0E.toReal))
      atTop (𝓝 0) := by
    have h2 : Tendsto (fun n => (∫⁻ x, ‖gateMoll ρ F A n x - F x‖ₑ
        ^ UnforcedLeray.B0412.q0E.toReal ∂(phaseμ P)) ^ (1 / UnforcedLeray.B0412.q0E.toReal))
        atTop (𝓝 ((0 : ENNReal) ^ (1 / UnforcedLeray.B0412.q0E.toReal))) :=
      (ENNReal.continuous_rpow_const.tendsto 0).comp hI'
    rwa [ENNReal.zero_rpow_of_pos (one_div_pos.mpr hp0)] at h2
  refine Tendsto.congr (fun n => ?_) hfinal
  exact (eLpNorm_eq_lintegral_rpow_enorm hq0 hqtop).symm
