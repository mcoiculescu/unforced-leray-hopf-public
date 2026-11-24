import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_IIIb_D2_1_3_1_2_1_4_1_1

/-!
# `sliceCountableTests`

Source `the November 2 reference manuscript` lines 1334-1337, 1351-1362, 1470-1480.
Slices of `Φ, a ∈ Y_2` are `L²` for a.e. phase; the slice defect is a continuous functional of the
`L²` data `(θ, Δθ)`; a countable dense family of tests suffices (model:
`Blueprint.ModeId.ae_forall_tests`).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology UnforcedLeray.Axi
open scoped ContDiff ENNReal

namespace UnforcedLeray.Short.PartIIIb.Concrete

open UnforcedLeray.PhaseSpace UnforcedLeray.B0411

/-- A property that is a.e. periodic along the orbit and holds a.e. on a period holds a.e. -/
theorem ae_of_ae_periodic_sct {T : ℝ} (hT : 0 < T) {p : ℝ → Prop}
    (hp : ∀ᵐ t : ℝ, ∀ k : ℤ, p (t + k * T) ↔ p t)
    (h : ∀ᵐ t ∂(volume.restrict (Ioc (0 : ℝ) T)), p t) : ∀ᵐ t : ℝ, p t := by
  rw [ae_restrict_iff' measurableSet_Ioc] at h
  have hk : ∀ k : ℤ, ∀ᵐ t : ℝ, (t - k * T) ∈ Ioc (0 : ℝ) T → p (t - k * T) := by
    intro k
    have := (measurePreserving_add_right (volume : Measure ℝ) (-(k * T))).quasiMeasurePreserving.ae h
    simpa only [sub_eq_add_neg] using this
  have hk' := ae_all_iff.mpr hk
  filter_upwards [hp, hk'] with t ht1 ht2
  have hmem := sub_toIocDiv_zsmul_mem_Ioc hT 0 t
  rw [zero_add] at hmem
  have e1 := ht2 (toIocDiv hT 0 t)
  have e2 := ht1 (-(toIocDiv hT 0 t))
  have hm : t - (toIocDiv hT 0 t : ℝ) * T ∈ Ioc (0 : ℝ) T := by simpa using hmem
  have := e1 hm
  rw [show t + ((-(toIocDiv hT 0 t) : ℤ) : ℝ) * T = t - (toIocDiv hT 0 t : ℝ) * T by push_cast; ring] at e2
  exact e2.mp this

/-- Slices of `Φ ∈ Y_2` are `L²` for a.e. phase. -/
theorem ae_memLp_slice_of_isInYr {P : ℝ} (hP : 0 < P) {Φ : ℝ × Space → CVec3}
    (hΦ : UnforcedLeray.Short.IIb.IsInYr P 2 Φ) :
    ∀ᵐ τ : ℝ, MemLp (fun y : Space => Φ (τ, y)) 2 volume := by
  have hmeas := hΦ.meas
  set f' : ℝ × Space → CVec3 := hmeas.mk Φ with hf'
  have hf's : StronglyMeasurable f' := hmeas.stronglyMeasurable_mk
  have hff' : Φ =ᵐ[volume] f' := hmeas.ae_eq_mk
  have hslices : ∀ᵐ t : ℝ, (fun y => Φ (t, y)) =ᵐ[volume] fun y => f' (t, y) := by
    have := hff'
    rw [Measure.volume_eq_prod] at this
    exact Measure.ae_ae_of_ae_prod this
  -- finiteness of the double integral
  have hfin := hΦ.finite
  unfold UnforcedLeray.Short.IIb.phaseLpNorm at hfin
  have hbase : (ENNReal.ofReal P⁻¹ * ∫⁻ t in Ioc (0 : ℝ) P, ∫⁻ y : Space, ‖Φ (t, y)‖ₑ ^ (2 : ℝ)) < ⊤ := by
    by_contra hcon
    have : (ENNReal.ofReal P⁻¹ * ∫⁻ t in Ioc (0 : ℝ) P, ∫⁻ y : Space, ‖Φ (t, y)‖ₑ ^ (2 : ℝ)) = ⊤ :=
      not_lt_top_iff.mp hcon
    rw [this, ENNReal.top_rpow_of_pos (by norm_num)] at hfin
    exact lt_irrefl _ hfin
  have hP' : ENNReal.ofReal P⁻¹ ≠ 0 := by
    simpa using inv_pos.mpr hP
  have hint : (∫⁻ t in Ioc (0 : ℝ) P, ∫⁻ y : Space, ‖Φ (t, y)‖ₑ ^ (2 : ℝ)) < ⊤ := by
    by_contra hcon
    have h1 : (∫⁻ t in Ioc (0 : ℝ) P, ∫⁻ y : Space, ‖Φ (t, y)‖ₑ ^ (2 : ℝ)) = ⊤ := not_lt_top_iff.mp hcon
    rw [h1, ENNReal.mul_top hP'] at hbase
    exact lt_irrefl _ hbase
  set g : ℝ → ℝ≥0∞ := fun t => ∫⁻ y : Space, ‖f' (t, y)‖ₑ ^ (2 : ℝ) with hg
  have hgm : Measurable g := by
    have : Measurable fun z : ℝ × Space => ‖f' z‖ₑ ^ (2 : ℝ) := hf's.enorm.pow_const _
    exact this.lintegral_prod_right'
  have hgeq : ∀ᵐ t : ℝ, (∫⁻ y : Space, ‖Φ (t, y)‖ₑ ^ (2 : ℝ)) = g t := by
    filter_upwards [hslices] with t ht
    refine lintegral_congr_ae ?_
    filter_upwards [ht] with y hy
    simp [hy]
  have hint' : (∫⁻ t in Ioc (0 : ℝ) P, g t) < ⊤ := by
    rw [← lintegral_congr_ae (ae_restrict_of_ae hgeq)]
    exact hint
  have hA : ∀ᵐ t ∂(volume.restrict (Ioc (0 : ℝ) P)), g t < ⊤ := ae_lt_top hgm hint'.ne
  have hslR : ∀ᵐ t ∂(volume.restrict (Ioc (0 : ℝ) P)), (fun y => Φ (t, y)) =ᵐ[volume] fun y => f' (t, y) :=
    ae_restrict_of_ae hslices
  have hQ : ∀ t, (fun y => Φ (t, y)) =ᵐ[volume] (fun y => f' (t, y)) → g t < ⊤ →
      MemLp (fun y : Space => Φ (t, y)) 2 volume := by
    intro t ht hgt
    have hmem : MemLp (fun x => f' (t, x)) 2 volume :=
      ⟨(hf's.comp_measurable measurable_prodMk_left).aestronglyMeasurable,
        (eLpNorm_lt_top_iff_lintegral_rpow_enorm_lt_top (by norm_num) (by simp)).2
          (by simpa [hg] using hgt)⟩
    exact hmem.ae_eq ht.symm
  refine ae_of_ae_periodic_sct hP (p := fun t => MemLp (fun y : Space => Φ (t, y)) 2 volume) ?_ ?_
  · -- periodic transfer
    have hpA : ∀ᵐ t : ℝ, ∀ᵐ y : Space, Φ (t + P, y) = Φ (t, y) := by
      have h := hΦ.periodic
      rw [Measure.volume_eq_prod] at h
      exact Measure.ae_ae_of_ae_prod h
    have hk : ∀ k : ℤ, ∀ᵐ t : ℝ, ∀ᵐ y : Space, Φ (t + k * P + P, y) = Φ (t + k * P, y) := by
      intro k
      exact (measurePreserving_add_right (volume : Measure ℝ) ((k : ℝ) * P)).quasiMeasurePreserving.ae hpA
    filter_upwards [ae_all_iff.mpr hk] with t ht k
    set F : ℤ → Prop := fun k => MemLp (fun y : Space => Φ (t + (k : ℝ) * P, y)) 2 volume with hF
    have step : ∀ k : ℤ, F (k + 1) ↔ F k := by
      intro k
      have := ht k
      have e : (fun y : Space => Φ (t + ((k + 1 : ℤ) : ℝ) * P, y)) =ᵐ[volume]
          fun y => Φ (t + (k : ℝ) * P, y) := by
        filter_upwards [this] with y hy
        rw [← hy]; congr 2; push_cast; ring
      exact memLp_congr_ae e
    have key : ∀ k : ℤ, F k ↔ F 0 := by
      intro k
      induction k using Int.induction_on with
      | zero => exact Iff.rfl
      | succ i ih => exact (step i).trans ih
      | pred i ih =>
        have := step (-(i : ℤ) - 1)
        rw [sub_add_cancel] at this
        exact this.symm.trans ih
    have := key k
    simpa [hF] using this
  · filter_upwards [hA, hslR] with t h1 h2 using hQ t h2 h1


/-- Coordinatewise conjugation on `CVec3`. -/
def cjV (v : CVec3) : CVec3 := WithLp.toLp 2 (fun i => (starRingEnd ℂ) (v i))

theorem cjV_continuous : Continuous cjV := by
  unfold cjV
  exact (PiLp.continuous_toLp 2 _).comp
    (continuous_pi fun i => Complex.continuous_conj.comp (PiLp.continuous_apply 2 _ i))

theorem cjV_norm (v : CVec3) : ‖cjV v‖ = ‖v‖ := by
  simp [cjV, EuclideanSpace.norm_eq]

theorem inner_cjV (v w : CVec3) : inner ℂ (cjV v) w = dotL v w := by
  simp [cjV, dotL_apply, PiLp.inner_apply, mul_comm]

/-- The `L²` pairing against a fixed `L²` field is continuous. -/
theorem pairing_continuous_L2 {f : Space → CVec3} (hf : MemLp f 2 volume) :
    Continuous (fun w : Lp CVec3 2 (volume : Measure Space) => ∫ y : Space, dotL (f y) (w y)) := by
  have : Fact ((2 : ℝ≥0∞) ≠ ⊤) := ⟨ENNReal.ofNat_ne_top⟩
  have hc : MemLp (fun y => cjV (f y)) 2 volume := by
    have hm : AEStronglyMeasurable (fun y => cjV (f y)) volume :=
      cjV_continuous.comp_aestronglyMeasurable hf.aestronglyMeasurable
    exact (memLp_congr_norm hf.aestronglyMeasurable hm
      (Eventually.of_forall fun y => (cjV_norm (f y)).symm)).mp hf
  let G : Lp CVec3 2 (volume : Measure Space) := hc.toLp _
  have : (fun w : Lp CVec3 2 (volume : Measure Space) => ∫ y : Space, dotL (f y) (w y))
      = fun w => inner ℂ G w := by
    funext w
    rw [MeasureTheory.L2.inner_def]
    refine integral_congr_ae ?_
    filter_upwards [MemLp.coeFn_toLp hc] with y hy
    rw [hy, inner_cjV]
  rw [this]
  exact continuous_const.inner continuous_id


theorem lapS_props_sct {θ : Space → CVec3} (hθ : ContDiff ℝ ∞ θ) (hc : HasCompactSupport θ) :
    ContDiff ℝ ∞ (UnforcedLeray.Short.PartIIIb.Concrete.lapS θ) ∧
      HasCompactSupport (UnforcedLeray.Short.PartIIIb.Concrete.lapS θ) := by
  have hfj : ∀ j : Fin 3, ContDiff ℝ ∞ (fun z : Space => fderiv ℝ θ z (EuclideanSpace.single j (1 : ℝ))) :=
    fun j => (contDiff_infty_iff_fderiv.mp hθ).2.clm_apply contDiff_const
  have hDj : ∀ j : Fin 3, ContDiff ℝ ∞ (fun y : Space => fderiv ℝ (fun z : Space => fderiv ℝ θ z (EuclideanSpace.single j (1 : ℝ))) y (EuclideanSpace.single j (1 : ℝ))) :=
    fun j => (contDiff_infty_iff_fderiv.mp (hfj j)).2.clm_apply contDiff_const
  have hcj : ∀ j : Fin 3, HasCompactSupport (fun z : Space => fderiv ℝ θ z (EuclideanSpace.single j (1 : ℝ))) :=
    fun j => HasCompactSupport.fderiv_apply ℝ hc (EuclideanSpace.single j (1 : ℝ))
  have hsum_eq : UnforcedLeray.Short.PartIIIb.Concrete.lapS θ
      = fun y : Space => ∑ j : Fin 3, fderiv ℝ (fun z : Space => fderiv ℝ θ z (EuclideanSpace.single j (1 : ℝ))) y (EuclideanSpace.single j (1 : ℝ)) := by
    funext y
    rfl
  have hcs : HasCompactSupport (∑ j : Fin 3, (fun y : Space => fderiv ℝ (fun z : Space => fderiv ℝ θ z (EuclideanSpace.single j (1 : ℝ))) y (EuclideanSpace.single j (1 : ℝ)))) :=
    HasCompactSupport.finset_sum fun j _ => HasCompactSupport.fderiv_apply ℝ (hcj j) (EuclideanSpace.single j (1 : ℝ))
  rw [hsum_eq]
  refine ⟨ContDiff.sum fun j _ => hDj j, ?_⟩
  convert hcs using 1
  funext y
  simp [Finset.sum_apply]



open Classical in
/-- The `L²` data of a test. -/
def sliceData (θ : Space → CVec3) : Lp CVec3 2 (volume : Measure Space) × Lp CVec3 2 (volume : Measure Space) :=
  (if h : MemLp θ 2 volume then h.toLp θ else 0,
    if h : MemLp (lapS θ) 2 volume then h.toLp (lapS θ) else 0)

theorem sliceCountableTests : SliceCountableTests := by
  intro P ν hP Φ a hΦ ha hall
  have : Fact ((2 : ℝ≥0∞) ≠ ⊤) := ⟨ENNReal.ofNat_ne_top⟩
  haveI : SecondCountableTopology (Lp CVec3 2 (volume : Measure Space)) :=
    MeasureTheory.Lp.SecondCountableTopology
  have hgood : ∀ᵐ τ : ℝ, MemLp (fun y : Space => Φ (τ, y)) 2 volume ∧
      MemLp (fun y : Space => a (τ, y)) 2 volume := by
    filter_upwards [ae_memLp_slice_of_isInYr hP hΦ, ae_memLp_slice_of_isInYr hP ha] with τ h1 h2
    exact ⟨h1, h2⟩
  classical
  let Λ : ℝ → (Lp CVec3 2 (volume : Measure Space) × Lp CVec3 2 (volume : Measure Space)) → ℂ :=
    fun τ v => if MemLp (fun y : Space => Φ (τ, y)) 2 volume ∧
        MemLp (fun y : Space => a (τ, y)) 2 volume then
      (ν : ℂ) * (∫ y : Space, dotL (Φ (τ, y)) (v.2 y)) - ∫ y : Space, dotL (a (τ, y)) (v.1 y)
    else 0
  have hΛ : ∀ τ, Continuous (Λ τ) := by
    intro τ
    by_cases hg : MemLp (fun y : Space => Φ (τ, y)) 2 volume ∧
        MemLp (fun y : Space => a (τ, y)) 2 volume
    · simp only [Λ, if_pos hg]
      exact (continuous_const.mul ((pairing_continuous_L2 hg.1).comp continuous_snd)).sub
        ((pairing_continuous_L2 hg.2).comp continuous_fst)
    · simp only [Λ, if_neg hg]
      exact continuous_const
  let T : Set (Space → CVec3) := {θ | ContDiff ℝ ∞ θ ∧ HasCompactSupport θ}
  have hval : ∀ τ, (MemLp (fun y : Space => Φ (τ, y)) 2 volume ∧
        MemLp (fun y : Space => a (τ, y)) 2 volume) → ∀ θ ∈ T,
      Λ τ (sliceData θ) = sliceDefect ν Φ a θ τ := by
    intro τ hg θ hθ
    obtain ⟨hs, hc⟩ := hθ
    obtain ⟨hLs, hLc⟩ := lapS_props_sct hs hc
    have h1 : MemLp θ 2 volume := hs.continuous.memLp_of_hasCompactSupport hc
    have h2 : MemLp (lapS θ) 2 volume := hLs.continuous.memLp_of_hasCompactSupport hLc
    simp only [Λ, if_pos hg, sliceData, dif_pos h1, dif_pos h2, sliceDefect]
    congr 1
    · congr 1
      refine integral_congr_ae ?_
      filter_upwards [MemLp.coeFn_toLp h2] with y hy
      rw [hy, dotL_apply]
    · refine integral_congr_ae ?_
      filter_upwards [MemLp.coeFn_toLp h1] with y hy
      rw [hy, dotL_apply]
  set S := sliceData '' T with hS
  obtain ⟨t, htS, htc, hSt⟩ :=
    (TopologicalSpace.IsSeparable.of_separableSpace S).exists_countable_dense_subset
  have hchoose : ∀ v : t, ∃ θ, θ ∈ T ∧ sliceData θ = v := fun v => htS v.2
  choose θs hθs using hchoose
  haveI := htc.to_subtype
  have hallt : ∀ᵐ τ : ℝ, ∀ v : t, (MemLp (fun y : Space => Φ (τ, y)) 2 volume ∧
        MemLp (fun y : Space => a (τ, y)) 2 volume) → Λ τ v = 0 := by
    rw [ae_all_iff]
    intro v
    obtain ⟨hmem, heq⟩ := hθs v
    have := hall (θs v) hmem.1 hmem.2
    filter_upwards [this] with τ hτ hg
    rw [← heq, hval τ hg _ hmem]
    exact hτ
  filter_upwards [hallt, hgood] with τ hτ hg θ hθ hc
  have hclosed : IsClosed {v | Λ τ v = 0} := isClosed_eq (hΛ τ) continuous_const
  have hsub : t ⊆ {v | Λ τ v = 0} := fun v hv => hτ ⟨v, hv⟩ hg
  have := (hclosed.closure_subset_iff.mpr hsub) (hSt ⟨θ, ⟨hθ, hc⟩, rfl⟩)
  rw [← hval τ hg θ ⟨hθ, hc⟩]
  exact this

end UnforcedLeray.Short.PartIIIb.Concrete
