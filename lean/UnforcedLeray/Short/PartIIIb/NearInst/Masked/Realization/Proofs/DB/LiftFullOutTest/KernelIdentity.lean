import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_near_masked_18_3_4
import UnforcedLeray.Short.PartIIIb.NearInst.Masked.Realization.Proofs.DB.LiftFullOutTest.RotEquiv
import UnforcedLeray.Short.PartIIIb.NearInst.Masked.Realization.Proofs.DB.LiftFullOutTest.RealNoSwirl

/-!
# `LiftKernelIdentity` (source 3916-3921, 2681-2691, 3586-3626)

Pointwise chart computation: the chart field of a box test is the kernel field after the lift
`liftVec` (`B0223.coeFn_liftVec`), with the rotation (`sepW_rot_equiv`), the no-swirl reality
(`sepW_real_noswirl`) and the `τ`-periodicity of the cartesian lift.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter UnforcedLeray.Axi
open scoped ENNReal

namespace UnforcedLeray.Short.PartIIIb.NearInst.Masked.Realization

open UnforcedLeray.Short.PartIIIb UnforcedLeray.Short.PartIIIb.Concrete
  UnforcedLeray.Short.PartIIIb.NearInst UnforcedLeray.Short.PartIIIb.NearInst.Masked

namespace KernelIdentityAux

open UnforcedLeray.B0220 (radius ageS etaCoord cellQ cellChart reduceIoc)

/-- One period `2c/R` of the phase leaves `chartOf` unchanged. -/
lemma chartOf_add_per (R c : ℝ) (hR : 0 < R) (hc : 0 < c) (z : Space) (τ : ℝ) :
    chartOf R c z (τ + 2 * c / R) = chartOf R c z τ := by
  have hR0 : R ≠ 0 := hR.ne'
  have hc0 : c ≠ 0 := hc.ne'
  have key : (R * Real.log (hRad z / R) + R * (τ + 2 * c / R) / 2) / c + 1 / 2 =
      (R * Real.log (hRad z / R) + R * τ / 2) / c + 1 / 2 + 1 := by
    field_simp
    ring
  unfold chartOf
  rw [key, Int.floor_add_one]
  congr 1
  refine Prod.ext ?_ rfl
  push_cast
  field_simp
  ring

lemma cartLift_add_per (R c : ℝ) (hR : 0 < R) (hc : 0 < c) (m : Chart → Ten3) (τ : ℝ) :
    cartLift R c m (τ + 2 * c / R) = cartLift R c m τ := by
  funext z
  unfold cartLift
  rw [chartOf_add_per R c hR hc z τ]

/-- Integer multiples of a period leave `sepW` unchanged. -/
lemma sepW_add_int_shift (ν : ℝ) (μ : ℂ) (per : ℝ) (T : ℝ → Space → Matrix (Fin 3) (Fin 3) ℝ)
    (hT : ∀ (τ : ℝ) (z : Space), T (τ + per) z = T τ z) (n : ℤ) (y : Space) (τ : ℝ) :
    UnforcedLeray.Short.IIIa.sepW ν μ T y (τ + n * per) =
      UnforcedLeray.Short.IIIa.sepW ν μ T y τ := by
  have hTn : ∀ (k : ℤ) (τ : ℝ) (z : Space), T (τ + k * per) z = T τ z := by
    intro k
    induction k using Int.induction_on with
    | zero => intro τ z; simp
    | succ k ih =>
      intro τ z
      have h1 : τ + (((k : ℤ) + 1 : ℤ) : ℝ) * per = (τ + ((k : ℤ) : ℝ) * per) + per := by
        push_cast; ring
      rw [h1, hT, ih τ z]
    | pred k ih =>
      intro τ z
      have h1 := hT (τ + ((-(k : ℤ) - 1 : ℤ) : ℝ) * per) z
      have h2 : τ + ((-(k : ℤ) - 1 : ℤ) : ℝ) * per + per = τ + ((-(k : ℤ) : ℤ) : ℝ) * per := by
        push_cast; ring
      rw [h2] at h1
      rw [← h1]
      exact ih τ z
  have hrw : ∀ (l : ℝ) (z : Space),
      T (τ + n * per + 2 * Real.log l) z = T (τ + 2 * Real.log l) z := by
    intro l z
    rw [show τ + n * per + 2 * Real.log l = (τ + 2 * Real.log l) + n * per by ring]
    exact hTn n _ z
  unfold UnforcedLeray.Short.IIIa.sepW
  simp only [hrw]

lemma hRad_smul (R : ℝ) (hR : 0 < R) (x : Space) : hRad (R • x) = R * radius x := by
  unfold hRad radius
  have h : (R • x) 0 ^ 2 + (R • x) 1 ^ 2 = R ^ 2 * (x 0 ^ 2 + x 1 ^ 2) := by
    simp only [PiLp.smul_apply, smul_eq_mul]
    ring
  rw [h, Real.sqrt_mul (sq_nonneg R), Real.sqrt_sq hR.le]

lemma hRad_eq (z : Space) : hRad z = radius z := rfl

lemma cylFrame_smul (R : ℝ) (hR : 0 < R) (x : Space) : cylFrame (R • x) = cylFrame x := by
  unfold cylFrame
  rw [hRad_smul R hR, hRad_eq x]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [PiLp.smul_apply, mul_div_mul_left _ _ hR.ne']

lemma sqrt_ageS (x : Space) : Real.sqrt (ageS x) = (radius x)⁻¹ := by
  unfold ageS
  have h0 : (0 : ℝ) ≤ radius x := by unfold radius; exact Real.sqrt_nonneg _
  rw [Real.sqrt_inv, Real.sqrt_sq h0]

lemma cellPt_snd_shift (c q : ℝ) :
    ∃ n : ℤ, (if UnforcedLeray.B0220.reduceIoc c q < c / 2 then UnforcedLeray.B0220.reduceIoc c q
      else UnforcedLeray.B0220.reduceIoc c q - c) = q - n * c := by
  unfold UnforcedLeray.B0220.reduceIoc
  split_ifs
  · exact ⟨⌈q / c⌉ - 1, by push_cast; ring⟩
  · exact ⟨⌈q / c⌉, by push_cast; ring⟩

lemma log_identity (ε : ℝ) (hε : 0 < ε) (x : Space) (τ : ℝ) :
    2 * UnforcedLeray.B0220.cellQ ε x τ / ε⁻¹ + Real.log (ageS x) = τ := by
  unfold UnforcedLeray.B0220.cellQ ageS
  rw [Real.log_inv, Real.log_pow]
  have hε0 : ε ≠ 0 := hε.ne'
  field_simp
  push_cast
  ring

lemma chartTau_cellPt (ε c : ℝ) (hε : 0 < ε) (x : Space) (τ : ℝ) :
    ∃ n : ℤ, chartTau ε⁻¹ (cellPt c (UnforcedLeray.B0220.cellChart ε c (x, τ))) =
      τ + n * (2 * c / ε⁻¹) := by
  obtain ⟨n, hn⟩ := cellPt_snd_shift c (UnforcedLeray.B0220.cellQ ε x τ)
  refine ⟨-n, ?_⟩
  have hsnd : (cellPt c (UnforcedLeray.B0220.cellChart ε c (x, τ))).2.1 =
      UnforcedLeray.B0220.cellQ ε x τ - n * c := hn
  have hfst : (cellPt c (UnforcedLeray.B0220.cellChart ε c (x, τ))).1 = ageS x := rfl
  have hl := log_identity ε hε x τ
  unfold chartTau
  rw [hsnd, hfst]
  have e : 2 * (UnforcedLeray.B0220.cellQ ε x τ - n * c) / ε⁻¹ =
      2 * UnforcedLeray.B0220.cellQ ε x τ / ε⁻¹ - n * (2 * c / ε⁻¹) := by
    ring
  rw [e]
  push_cast
  linarith

lemma chartY_cellPt (ε c : ℝ) (hε : 0 < ε) (x : Space) (τ : ℝ) (hx : radius x ≠ 0) :
    chartY ε⁻¹ (cellPt c (UnforcedLeray.B0220.cellChart ε c (x, τ))) =
      (WithLp.toLp 2 ![ε⁻¹ * radius x, 0, ε⁻¹ * x 2] : Space) := by
  have hε0 : ε ≠ 0 := hε.ne'
  ext i
  fin_cases i
  · simp [chartY, cellPt, UnforcedLeray.B0220.cellChart, sqrt_ageS, UnforcedLeray.B0220.etaCoord]
  · simp [chartY, cellPt, UnforcedLeray.B0220.cellChart]
  · simp [chartY, cellPt, UnforcedLeray.B0220.cellChart, sqrt_ageS, UnforcedLeray.B0220.etaCoord]
    field_simp


lemma fullOut_cellPt (ε c ν μ : ℝ) (hε : 0 < ε) (hc : 0 < c) (m : Chart → Ten3) (x : Space)
    (hx : radius x ≠ 0) (τ : ℝ) :
    fullOut ε⁻¹ c ν μ m (cellPt c (UnforcedLeray.B0220.cellChart ε c (x, τ))) =
      (radius x) • merRe (-UnforcedLeray.Short.IIIa.sepW ν (μ : ℂ) (cartLift ε⁻¹ c m)
        (WithLp.toLp 2 ![ε⁻¹ * radius x, 0, ε⁻¹ * x 2]) τ) := by
  obtain ⟨n, hn⟩ := chartTau_cellPt ε c hε x τ
  have hR : (0 : ℝ) < ε⁻¹ := inv_pos.2 hε
  unfold fullOut
  rw [show (cellPt c (UnforcedLeray.B0220.cellChart ε c (x, τ))).1 = ageS x from rfl,
    sqrt_ageS, inv_inv, hn, chartY_cellPt ε c hε x τ hx,
    sepW_add_int_shift ν (μ : ℂ) (2 * c / ε⁻¹) (cartLift ε⁻¹ c m)
      (fun τ' z => congrFun (cartLift_add_per ε⁻¹ c hR hc m τ') z) n _ τ]

lemma hRad_pos_of (x : Space) (hx : radius x ≠ 0) : 0 < radius x :=
  lt_of_le_of_ne (by unfold radius; exact Real.sqrt_nonneg _) (Ne.symm hx)

/-- The pointwise identity behind `LiftKernelIdentity`. -/
lemma pointwise (ν μ ε c : ℝ) (hν : 0 < ν) (hε : 0 < ε) (hc : 0 < c) (hμ : -(1 / 4 : ℝ) < μ)
    (m : Chart → Ten3) (hm : IsBoxTensor m) (x : Space) (hx : radius x ≠ 0) (τ : ℝ) :
    (Real.sqrt (2 * Real.pi) * ε)⁻¹ •
        (UnforcedLeray.B0220.liftA x • UnforcedLeray.B0223.frameC x
          (merC (fullOut ε⁻¹ c ν μ m (cellPt c (UnforcedLeray.B0220.cellChart ε c (x, τ))))))
      = (((Real.sqrt (2 * Real.pi))⁻¹ : ℝ) : ℂ) •
          (WithLp.toLp 2 (fun i => ((ε⁻¹ : ℝ) : ℂ) *
            -UnforcedLeray.Short.IIIa.sepW ν (μ : ℂ) (cartLift ε⁻¹ c m) (ε⁻¹ • x) τ i) :
            UnforcedLeray.B0223.SpaceC) := by
  have hr : 0 < radius x := hRad_pos_of x hx
  have hR : (0 : ℝ) < ε⁻¹ := inv_pos.2 hε
  have hρ : 0 < ε⁻¹ * radius x := mul_pos hR hr
  rw [fullOut_cellPt ε c ν μ hε hc m x hx τ]
  obtain ⟨hreal, hsw1⟩ :=
    sepW_real_noswirl ν ε⁻¹ c μ hν hR hc m hm τ (ε⁻¹ * radius x) (ε⁻¹ * x 2) hρ
  have hrot := sepW_rot_equiv ν ε⁻¹ c μ hν hR hc hμ m hm τ (ε⁻¹ • x)
    (by rw [hRad_smul _ hR]; exact hρ)
  have hv : (WithLp.toLp 2 ![hRad (ε⁻¹ • x), 0, (ε⁻¹ • x) 2] : Space) =
      WithLp.toLp 2 ![ε⁻¹ * radius x, 0, ε⁻¹ * x 2] := by
    congr 1
    ext i
    fin_cases i <;> simp [hRad_smul _ hR]
  rw [hv, cylFrame_smul _ hR] at hrot
  set W := UnforcedLeray.Short.IIIa.sepW ν (μ : ℂ) (cartLift ε⁻¹ c m)
    (WithLp.toLp 2 ![ε⁻¹ * radius x, 0, ε⁻¹ * x 2]) τ with hW
  have hW1 : W 1 = 0 := hsw1
  have hWim : ∀ i, (W i).im = 0 := hreal
  obtain ⟨α, hα⟩ : ∃ α : ℝ, W 0 = (α : ℂ) :=
    ⟨(W 0).re, Complex.ext (by simp) (by simp [hWim 0])⟩
  obtain ⟨β, hβ⟩ : ∃ β : ℝ, W 2 = (β : ℂ) :=
    ⟨(W 2).re, Complex.ext (by simp) (by simp [hWim 2])⟩
  have hr' : (radius x : ℂ) ≠ 0 := by exact_mod_cast hr.ne'
  have hε' : (ε : ℂ) ≠ 0 := by exact_mod_cast hε.ne'
  have hpi : (Real.sqrt Real.pi : ℂ) ≠ 0 := by exact_mod_cast (Real.sqrt_pos.2 Real.pi_pos).ne'
  have h2 : (Real.sqrt 2 : ℂ) ≠ 0 := by exact_mod_cast (Real.sqrt_pos.2 (by norm_num)).ne'
  simp only [hrot]
  ext i
  fin_cases i <;>
    simp [UnforcedLeray.B0223.frameC_apply, UnforcedLeray.B0223.unitRC,
      UnforcedLeray.B0223.unitZC, merC, merRe, UnforcedLeray.B0220.liftA, cylFrame, hRad_eq,
      Fin.sum_univ_three, hW1, hα, hβ, Pi.neg_apply]
  all_goals (field_simp [hr', hε', hpi, h2]; try ring)

/-- The axis `{radius = 0}` is null for the periodic cylinder. -/
lemma radius_ne_zero_ae (P : ℝ) [Fact (0 < P)] :
    ∀ᵐ z ∂(volume : Measure (UnforcedLeray.B0223.PSpace P)), radius z.1 ≠ 0 := by
  have hA0 : (volume : Measure Space) {x : Space | x 0 = 0} = 0 := by
    let s : Submodule ℝ Space :=
      LinearMap.ker ((EuclideanSpace.proj (0 : Fin 3) : Space →L[ℝ] ℝ) : Space →ₗ[ℝ] ℝ)
    have hs : s ≠ ⊤ := by
      intro h
      have hmem : (EuclideanSpace.single (0 : Fin 3) (1 : ℝ) : Space) ∈ s := by
        rw [h]; exact Submodule.mem_top
      simp [s] at hmem
    have hset : (s : Set Space) = {x : Space | x 0 = 0} := by
      ext x
      simp [s]
    rw [← hset]
    exact Measure.addHaar_submodule (volume : Measure Space) s hs
  have hsub : {z : UnforcedLeray.B0223.PSpace P | radius z.1 = 0} ⊆
      {x : Space | x 0 = 0} ×ˢ (univ : Set (AddCircle P)) := by
    intro z hz
    have hz' : radius z.1 = 0 := hz
    unfold radius at hz'
    rw [Real.sqrt_eq_zero'] at hz'
    have h2 : z.1 0 ^ 2 = 0 := by nlinarith [sq_nonneg (z.1 0), sq_nonneg (z.1 1)]
    have h0 : z.1 0 = 0 := by simpa using h2
    exact ⟨h0, trivial⟩
  have hS : (volume : Measure (UnforcedLeray.B0223.PSpace P)) {z | radius z.1 = 0} = 0 := by
    apply measure_mono_null hsub
    rw [Measure.volume_eq_prod, Measure.prod_prod, hA0, zero_mul]
  filter_upwards [MeasureTheory.measure_eq_zero_iff_ae_notMem.1 hS] with z hz using hz

/-- The chart form of the target field, a.e. (uses the weighted-composition transport). -/
lemma compFun_apply {P ε c : ℝ} [Fact (0 < P)] (hε : 0 < ε) (hc : 0 < c) (hP : P = 2 * ε * c)
    (b : UnforcedLeray.B0220.Profile → UnforcedLeray.B0223.MeridC)
    (z : UnforcedLeray.B0223.PSpace P) :
    (UnforcedLeray.B0223.liftVecWC hε hc hP).compFun b z =
      (Real.sqrt (2 * Real.pi) * ε)⁻¹ • UnforcedLeray.B0220.liftA z.1 •
        UnforcedLeray.B0223.frameC z.1
          (UnforcedLeray.B0220.periodize c b
            (UnforcedLeray.B0220.chart ε (UnforcedLeray.B0223.toCell P z))) := by
  simp only [UnforcedLeray.B0220.WeightedComp.compFun, UnforcedLeray.B0223.liftVecWC,
    LinearMap.smul_apply, LinearMap.restrictScalars_apply, mul_smul, UnforcedLeray.B0220.jConst]
  rfl

end KernelIdentityAux

open KernelIdentityAux in
/-- **Leaf B** (source 3916-3921, 2681-2691, 3586-3626): the lift of any representative of the
chart field of a box test is `(√(2π))⁻¹ · kernelField`. -/
theorem liftKernelIdentity : UnforcedLeray.Short.PartIIIb.NearInst.Masked.Realization.LiftKernelIdentity := by
  intro ν ε c P _ hν hε hc hP μ hμ m _htest hm G hG
  have h4 := (UnforcedLeray.B0223.liftVecWC hε hc hP).compFun_congr hG
  filter_upwards [UnforcedLeray.B0223.coeFn_liftVec hε hc hP G, h4,
    KernelIdentityAux.radius_ne_zero_ae P] with z hz1 hz4 hz5
  rw [hz1]
  rw [KernelIdentityAux.compFun_apply hε hc hP, KernelIdentityAux.compFun_apply hε hc hP] at hz4
  rw [hz4]
  exact KernelIdentityAux.pointwise ν μ ε c hν hε hc hμ m hm z.1 hz5 (UnforcedLeray.B0223.toCell P z).2

end UnforcedLeray.Short.PartIIIb.NearInst.Masked.Realization
