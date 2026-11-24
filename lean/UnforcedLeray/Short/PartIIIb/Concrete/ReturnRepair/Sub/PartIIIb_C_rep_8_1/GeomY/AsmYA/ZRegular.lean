import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_8_1.GeomY.AsmYA
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_8_1.GeomY.ActYDiff
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_8_1.GeomX.Asm.ZPrimRegular
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_srcL_6_2_3

/-!
# `PartIII-b:C/rep/8/1/1/2/4/3` (`zRegularYA`): regularity, decay and outward primitive of
`W_μ` and `W^mt_μ` on the clear region

Source `the November 2 reference manuscript`
lines 4178-4186 (outward primitive; "the separated-kernel estimates prove convergence of this
primitive and its differentiated versions"), 5400-5413 (separated kernels, radial gap: the old
source lies in `(εϱ)² ≤ ν/1.2`, the clear region is `(εϱ)² > ν/1.1`), 4163-4166 (`χ_o` vanishes
for `νs ≤ 1.2`), 4168-4171 (`W_μ` of the old source), 4776-4791 (`W^mt_μ = ε² V_μ(ε·)`).

* `zWAct = Re W_μ` of the old thin source.  The old thin source has a separated representative
  `S` with the same responses (`Sub8_1_1_2_3.thinSepData`): `P`-periodic, measurable, supported
  in `ϱ ≤ ε⁻¹√(5ν/6)`, finite `L²_τL²` moment.  So `Re W_μ = sepWre ν μ S` is `C²` off the
  source cylinder (`sepWSmoothOn_of`), and it and its gradient are `O(ϱ⁻³)` (`sepFarDecay`).
* `zWMt = mtField (youngW …)`: the zero-width Young field is `C^∞` on the outward region
  (`xsYoungWSmooth`) with `|D^kW| ≤ C(1+|w|)^{-4-k}` (`xsYoungWDecay`); `OldThinFinite` from
  `sourceLN0`.
* `PrimData` from the `O(ρ⁻³)` decay of the value and the gradient along the half-plane rays
  (`ZPrimKernel.rayDecayW_of`, `RayPrimW.primData_of_decayW`).

The generic lemmas `sepWre_cd`, `sepWre_far`, `sepWre_tendsto`, `mt_regular`, `mt_far`,
`primData_of_clear` and the field lemmas `zWAct_eq_sepWre`, `zWAct_cd`, `zWMid_cd` are public
(namespace `ZRegYA`) for `Meas.lean`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology UnforcedLeray.Axi
open scoped ENNReal

namespace UnforcedLeray.Short.PartIIIb.Concrete

open UnforcedLeray.Blueprint.Planar (PlanarData)

namespace ZRegYA

open GeomXAsm GeomXAsm.ZPrimKernel GeomXAsm.RayPrimW ZRegAux

/-! ## The separated response of one resolvent -/

/-- `Re W_μ` of a separated source is `C²` off the source cylinder. -/
theorem sepWre_cd {ν μ P r0 : ℝ} {S : ℝ → Space → Matrix (Fin 3) (Fin 3) ℝ} (hν : 0 < ν)
    (hμ : -(1 / 4) < μ) (hr0 : 0 ≤ r0) (hP : 0 < P) (hS : IIIa.IsSepSource P r0 S)
    (hM : SepMoment P S) (τ : ℝ) :
    ContDiffOn ℝ 2 (sepWre ν μ S τ) {y : Space | r0 < ϱ y} := by
  have hA := sepWSmoothOn_of IIIa.sepKernelBounds ν (μ : ℂ) r0 P S hν (by simpa using hμ) hr0
    hP hS hM τ
  refine contDiffOn_piLp' 2 fun i => ?_
  exact (Complex.reCLM.contDiff.comp_contDiffOn (hA i)).congr fun y _ => rfl

/-- Far decay `O(ρ⁻³)` of `Re W_μ` and of its gradient on the half plane (`sepFarDecay`). -/
theorem sepWre_far {ν μ ro P : ℝ} {S : ℝ → Space → Matrix (Fin 3) (Fin 3) ℝ} (hν : 0 < ν)
    (hμ : -(1 / 4) < μ) (hro : 0 < ro) (hP : 0 < P) (hS : IIIa.IsSepSource P ro S)
    (hM : SepMoment P S) (τ : ℝ) :
    ∃ C : ℝ, ∀ ρ : ℝ, 2 * ro ≤ ρ → ∀ z' : ℝ,
      ‖sepWre ν μ S τ (hpt ρ z')‖ ≤ C * ρ ^ (-3 : ℝ) ∧
      ‖fderiv ℝ (sepWre ν μ S τ) (hpt ρ z')‖ ≤ C * ρ ^ (-3 : ℝ) := by
  have hμa : -(1 / 4) < (μ : ℂ).re := by simpa using hμ
  obtain ⟨C1, h1⟩ := sepFarDecay ν (μ : ℂ) ro P S hν hμa hro.le hP hS hM τ
  have hsm := sepWSmoothOn_of IIIa.sepKernelBounds
  refine ⟨3 * C1, fun ρ hρ z' => ?_⟩
  have hρ0 : 0 < ρ := by linarith
  set y := hpt ρ z' with hy
  have hϱ : ϱ y = ρ := ϱ_hpt hρ0 z'
  have hy2 : 2 * ro ≤ ϱ y := by rw [hϱ]; exact hρ
  have hyU : y ∈ {y : Space | ro < ϱ y} := by
    show ro < ϱ y
    linarith
  have hUo : IsOpen {y : Space | ro < ϱ y} :=
    isOpen_lt continuous_const UnforcedLeray.Axi.continuous_ϱ
  have hda : ∀ i, DifferentiableAt ℝ (fun x => IIIa.sepW ν (μ : ℂ) S x τ i) y :=
    fun i => ((hsm ν (μ : ℂ) ro P S hν hμa hro.le hP hS hM τ i).differentiableOn
      (by norm_num)).differentiableAt (hUo.mem_nhds hyU)
  constructor
  · refine (norm_le_sum_coords _).trans ?_
    have hi : ∀ i : Fin 3, ‖sepWre ν μ S τ y i‖ ≤ C1 * ρ ^ (-3 : ℝ) := by
      intro i
      have ha := (h1 i y hy2).1
      rw [hϱ] at ha
      calc ‖sepWre ν μ S τ y i‖ = ‖(IIIa.sepW ν (μ : ℂ) S y τ i).re‖ := rfl
        _ ≤ ‖IIIa.sepW ν (μ : ℂ) S y τ i‖ := by
            rw [Real.norm_eq_abs]; exact Complex.abs_re_le_norm _
        _ ≤ _ := ha
    calc ∑ i, ‖sepWre ν μ S τ y i‖ ≤ ∑ _i : Fin 3, C1 * ρ ^ (-3 : ℝ) :=
          Finset.sum_le_sum fun i _ => hi i
      _ = 3 * C1 * ρ ^ (-3 : ℝ) := by simp [Finset.sum_const]; ring
  · have hcomp : ∀ i, HasFDerivAt (fun x => sepWre ν μ S τ x i)
        (Complex.reCLM.comp (fderiv ℝ (fun x => IIIa.sepW ν (μ : ℂ) S x τ i) y)) y :=
      fun i => Complex.reCLM.hasFDerivAt.comp y (hda i).hasFDerivAt
    refine (norm_fderiv_le_of_comp hcomp).trans ?_
    have hi : ∀ i : Fin 3,
        ‖Complex.reCLM.comp (fderiv ℝ (fun x => IIIa.sepW ν (μ : ℂ) S x τ i) y)‖ ≤
          C1 * ρ ^ (-3 : ℝ) := by
      intro i
      have ha := (h1 i y hy2).2
      rw [hϱ] at ha
      calc _ ≤ ‖Complex.reCLM‖ * ‖fderiv ℝ (fun x => IIIa.sepW ν (μ : ℂ) S x τ i) y‖ :=
            ContinuousLinearMap.opNorm_comp_le _ _
        _ = ‖fderiv ℝ (fun x => IIIa.sepW ν (μ : ℂ) S x τ i) y‖ := by
            rw [Complex.reCLM_norm, one_mul]
        _ ≤ _ := ha
    calc _ ≤ ∑ _i : Fin 3, C1 * ρ ^ (-3 : ℝ) := Finset.sum_le_sum fun i _ => hi i
      _ = 3 * C1 * ρ ^ (-3 : ℝ) := by simp [Finset.sum_const]; ring

/-- `Re W_μ` tends to zero along every outward ray (degree `-3` decay). -/
theorem sepWre_tendsto {ν μ P r0 : ℝ} {S : ℝ → Space → Matrix (Fin 3) (Fin 3) ℝ} (hν : 0 < ν)
    (hμ : -(1 / 4) < μ) (hr0 : 0 ≤ r0) (hP : 0 < P) (hS : IIIa.IsSepSource P r0 S)
    (hM : SepMoment P S) (τ : ℝ) {y : Space} (hy : 0 < ϱ y) :
    Tendsto (fun t : ℝ => sepWre ν μ S τ (outRay y t)) atTop (𝓝 0) := by
  obtain ⟨C1, h1⟩ := sepFarDecay ν (μ : ℂ) r0 P S hν (by simpa using hμ) hr0 hP hS hM τ
  have hz : Tendsto (fun t : ℝ => C1 * t ^ (-3 : ℝ)) atTop (𝓝 0) := by
    simpa using (tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 3)).const_mul C1
  have hcomp : Tendsto (fun t : ℝ => fun i : Fin 3 =>
      (IIIa.sepW ν (μ : ℂ) S (outRay y t) τ i).re) atTop (𝓝 (fun _ => 0)) := by
    refine tendsto_pi_nhds.2 fun i => ?_
    refine squeeze_zero_norm' ?_ hz
    filter_upwards [eventually_ge_atTop (max (2 * r0) 1)] with t ht
    have ht0 : 0 < t := lt_of_lt_of_le one_pos ((le_max_right _ _).trans ht)
    have hϱ : ϱ (outRay y t) = t := outRay_ϱ hy ht0.le
    have hb1 := (h1 i (outRay y t) (by rw [hϱ]; exact (le_max_left _ _).trans ht)).1
    rw [hϱ] at hb1
    calc ‖(IIIa.sepW ν (μ : ℂ) S (outRay y t) τ i).re‖
        ≤ ‖IIIa.sepW ν (μ : ℂ) S (outRay y t) τ i‖ := by
          rw [Real.norm_eq_abs]; exact Complex.abs_re_le_norm _
      _ ≤ C1 * t ^ (-3 : ℝ) := hb1
  have := ((PiLp.continuous_toLp 2 (fun _ : Fin 3 => ℝ)).tendsto (fun _ => 0)).comp hcomp
  have e0 : (0 : Space) = WithLp.toLp 2 (fun _ : Fin 3 => (0 : ℝ)) := rfl
  rw [e0]
  exact this

/-! ## A phase-free field `F : Vec3 → Vec3` with the decay of the zero-width Young field -/

/-- The decay hypothesis of `XSYoungWDecay` for one field. -/
def MtDecay (ν ε : ℝ) (F : Vec3 → Vec3) : Prop :=
  ∀ a : ℝ, 5 * ν / (6 * ε ^ 2) < a → ∀ k : ℕ, ∃ C : ℝ, ∀ w : Vec3, a ≤ cylR w ^ 2 →
    ‖iteratedFDeriv ℝ k F w‖ ≤ C * (1 + ‖w‖) ^ (-(4 + (k : ℝ)))

theorem clear_maps_outReg {ε ν : ℝ} (hε : 0 < ε) (hν : 0 < ν) :
    MapsTo (fun y : Space => WithLp.ofLp y) (clearSet ε ν) (outReg ν ε) := by
  intro y hy
  obtain ⟨h0, h1⟩ := hy
  simp only [mem_setOf_eq] at h0 h1
  show 5 * ν / (6 * ε ^ 2) < cylR (WithLp.ofLp y) ^ 2
  rw [← ϱ_eq_cylR']
  have h2 : ν / (11 / 10) < (ε * ϱ y) ^ 2 := h1
  have h6 : 0 < 6 * ε ^ 2 := by positivity
  rw [div_lt_iff₀ h6]
  have : 5 * ν / 6 < ν / (11 / 10) := by
    rw [div_lt_div_iff₀ (by norm_num) (by norm_num)]; nlinarith
  nlinarith [sq_nonneg ε, mul_pow ε (ϱ y) 2]

/-- A phase-free field with the Young smoothness and decay is `C¹` on the clear region and tends
to zero along every outward ray (as `ZRegAux.zMt_regular`). -/
theorem mt_regular {ν ε : ℝ} (hν : 0 < ν) (hε : 0 < ε) {F : Vec3 → Vec3}
    (hsm : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) F (outReg ν ε)) (hdec : MtDecay ν ε F)
    (τ : ℝ) :
    ContDiffOn ℝ 1 (mtField F τ) (clearSet ε ν) ∧
      ∀ y ∈ clearSet ε ν, Tendsto (fun t : ℝ => mtField F τ (outRay y t)) atTop (𝓝 0) := by
  have hzeq : mtField F τ = fun y : Space => WithLp.toLp 2 (F (WithLp.ofLp y)) := by
    funext y; rfl
  have hmaps := clear_maps_outReg hε hν
  refine ⟨?_, ?_⟩
  · rw [hzeq]
    have := (PiLp.contDiff_toLp (𝕜 := ℝ) (p := 2) (E := fun _ : Fin 3 => ℝ) (n := 1)).comp_contDiffOn
      ((hsm.comp (PiLp.contDiff_ofLp (𝕜 := ℝ) (p := 2) (E := fun _ : Fin 3 => ℝ)
        (n := ((⊤ : ℕ∞) : WithTop ℕ∞))).contDiffOn hmaps).of_le (by exact_mod_cast le_top))
    exact this
  · intro y hy
    have hyp : 0 < ϱ y := hy.1
    set a : ℝ := ν / ε ^ 2 with ha
    have ha' : 5 * ν / (6 * ε ^ 2) < a := by
      rw [ha, div_lt_div_iff₀ (by positivity) (by positivity)]
      nlinarith [pow_pos hε 2, pow_pos hν 2, mul_pos hν (pow_pos hε 2)]
    obtain ⟨C0, hC0⟩ := hdec a ha' 0
    have hq : Tendsto (fun t : ℝ => F (WithLp.ofLp (outRay y t))) atTop (𝓝 0) := by
      rw [tendsto_zero_iff_norm_tendsto_zero]
      have hw : Tendsto (fun t : ℝ => (1 + t / 2)) atTop atTop :=
        tendsto_atTop_add_const_left _ _ (tendsto_id.atTop_div_const (by norm_num))
      have hz : Tendsto (fun t : ℝ => |C0| * (1 + t / 2) ^ (-(4 : ℝ))) atTop (𝓝 0) := by
        have := (tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 4)).comp hw
        simpa using this.const_mul |C0|
      refine squeeze_zero_norm' ?_ hz
      filter_upwards [eventually_ge_atTop (ε⁻¹ * (ν + 1))] with t ht
      rw [norm_norm]
      have ht0 : 0 < t := lt_of_lt_of_le (by positivity) ht
      have hϱ : ϱ (outRay y t) = t := outRay_ϱ hyp ht0.le
      have hcyl : cylR (WithLp.ofLp (outRay y t)) = t := by rw [← ϱ_eq_cylR']; exact hϱ
      have hat : a ≤ cylR (WithLp.ofLp (outRay y t)) ^ 2 := by
        rw [hcyl, ha]
        have h1 : ε⁻¹ * (ν + 1) ≤ t := ht
        have h2 : (ε⁻¹ * (ν + 1)) ^ 2 ≤ t ^ 2 := by
          gcongr
        have h3 : ν / ε ^ 2 ≤ (ε⁻¹ * (ν + 1)) ^ 2 := by
          rw [mul_pow, inv_pow, ← div_eq_inv_mul]
          apply div_le_div_of_nonneg_right _ (by positivity)
          nlinarith
        exact h3.trans h2
      have hmain := hC0 _ hat
      rw [norm_iteratedFDeriv_zero] at hmain
      have hn := norm_le_pi_norm (WithLp.ofLp (outRay y t)) 0
      have hn1 := norm_le_pi_norm (WithLp.ofLp (outRay y t)) 1
      have e0 : (WithLp.ofLp (outRay y t)) 0 ^ 2 + (WithLp.ofLp (outRay y t)) 1 ^ 2 = t ^ 2 := by
        have := hcyl
        unfold cylR at this
        have h5 := Real.sq_sqrt (by positivity : 0 ≤ (WithLp.ofLp (outRay y t)) 0 ^ 2 +
          (WithLp.ofLp (outRay y t)) 1 ^ 2)
        rw [this] at h5
        linarith
      have hhalf : t / 2 ≤ ‖WithLp.ofLp (outRay y t)‖ := by
        set w := WithLp.ofLp (outRay y t) with hw
        have h0' : |w 0| ≤ ‖w‖ := by simpa using hn
        have h1' : |w 1| ≤ ‖w‖ := by simpa using hn1
        have h2 : t ^ 2 ≤ (2 * ‖w‖) ^ 2 := by
          rw [← e0, ← sq_abs (w 0), ← sq_abs (w 1)]
          nlinarith [abs_nonneg (w 0), abs_nonneg (w 1)]
        have h3 := abs_le_of_sq_le_sq' h2 (by positivity)
        linarith [h3.2]
      have hu : (1 + ‖WithLp.ofLp (outRay y t)‖) ^ (-(4 + ((0 : ℕ) : ℝ))) ≤
          (1 + t / 2) ^ (-(4 : ℝ)) := by
        have := Real.rpow_le_rpow_of_nonpos (x := 1 + t / 2) (y := 1 + ‖WithLp.ofLp (outRay y t)‖)
          (z := -(4 + ((0 : ℕ) : ℝ))) (by positivity) (by linarith) (by norm_num)
        simpa using this
      have hu0 : 0 ≤ (1 + ‖WithLp.ofLp (outRay y t)‖) ^ (-(4 + ((0 : ℕ) : ℝ))) :=
        Real.rpow_nonneg (by positivity) _
      calc ‖F (WithLp.ofLp (outRay y t))‖
          ≤ C0 * (1 + ‖WithLp.ofLp (outRay y t)‖) ^ (-(4 + ((0 : ℕ) : ℝ))) := hmain
        _ ≤ |C0| * (1 + ‖WithLp.ofLp (outRay y t)‖) ^ (-(4 + ((0 : ℕ) : ℝ))) :=
            mul_le_mul_of_nonneg_right (le_abs_self _) hu0
        _ ≤ |C0| * (1 + t / 2) ^ (-(4 : ℝ)) := mul_le_mul_of_nonneg_left hu (abs_nonneg _)
    rw [hzeq]
    have e0 : (0 : Space) = WithLp.toLp 2 (fun _ : Fin 3 => (0 : ℝ)) := rfl
    have := ((PiLp.continuous_toLp 2 (fun _ : Fin 3 => ℝ)).tendsto (0 : Vec3)).comp hq
    rw [e0]
    exact this

/-- Far decay `O(ρ⁻³)` of a phase-free field with the Young decay, value and gradient, on the
half plane (as `ZPrimKernel.newton_far`). -/
theorem mt_far {ν ε : ℝ} {F : Vec3 → Vec3}
    (hsm : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) F (outReg ν ε)) (hdec : MtDecay ν ε F)
    {r₀ : ℝ} (hr₀ : 0 < r₀) (hr₀b : 5 * ν / (6 * ε ^ 2) < r₀ ^ 2) (τ : ℝ) :
    ∃ C : ℝ, ∀ ρ : ℝ, r₀ ≤ ρ → ∀ z' : ℝ,
      ‖mtField F τ (hpt ρ z')‖ ≤ C * ρ ^ (-3 : ℝ) ∧
      ‖fderiv ℝ (mtField F τ) (hpt ρ z')‖ ≤ C * ρ ^ (-3 : ℝ) := by
  obtain ⟨C0, hC0⟩ := hdec (r₀ ^ 2) hr₀b 0
  obtain ⟨C1, hC1⟩ := hdec (r₀ ^ 2) hr₀b 1
  refine ⟨3 * (|C0| + |C1|), fun ρ hρ z' => ?_⟩
  have hρ0 : 0 < ρ := lt_of_lt_of_le hr₀ hρ
  set w := WithLp.ofLp (hpt ρ z') with hw
  have hcyl : cylR w = ρ := cylR_ofLp_hpt hρ0 z'
  have ha : r₀ ^ 2 ≤ cylR w ^ 2 := by rw [hcyl]; exact pow_le_pow_left₀ hr₀.le hρ 2
  have hwn : ρ ≤ ‖w‖ := ofLp_hpt_norm hρ0 z'
  have hp : 0 ≤ ρ ^ (-3 : ℝ) := Real.rpow_nonneg hρ0.le _
  have hpos : ∀ k : ℕ, 0 ≤ (1 + ‖w‖) ^ (-(4 + (k : ℝ))) := fun k =>
    Real.rpow_nonneg (by positivity) _
  have hb0 : ‖F w‖ ≤ |C0| * ρ ^ (-3 : ℝ) := by
    have := hC0 w ha
    rw [norm_iteratedFDeriv_zero] at this
    calc ‖F w‖ ≤ C0 * (1 + ‖w‖) ^ (-(4 + ((0 : ℕ) : ℝ))) := this
      _ ≤ |C0| * (1 + ‖w‖) ^ (-(4 + ((0 : ℕ) : ℝ))) :=
          mul_le_mul_of_nonneg_right (le_abs_self _) (hpos 0)
      _ ≤ |C0| * ρ ^ (-3 : ℝ) := mul_le_mul_of_nonneg_left (decay_le hρ0 hwn 0) (abs_nonneg _)
  have hb1 : ‖fderiv ℝ F w‖ ≤ |C1| * ρ ^ (-3 : ℝ) := by
    have := hC1 w ha
    rw [norm_iteratedFDeriv_one] at this
    calc ‖fderiv ℝ F w‖ ≤ C1 * (1 + ‖w‖) ^ (-(4 + ((1 : ℕ) : ℝ))) := this
      _ ≤ |C1| * (1 + ‖w‖) ^ (-(4 + ((1 : ℕ) : ℝ))) :=
          mul_le_mul_of_nonneg_right (le_abs_self _) (hpos 1)
      _ ≤ |C1| * ρ ^ (-3 : ℝ) := mul_le_mul_of_nonneg_left (decay_le hρ0 hwn 1) (abs_nonneg _)
  constructor
  · refine (norm_le_sum_coords _).trans ?_
    have hi : ∀ i : Fin 3, ‖mtField F τ (hpt ρ z') i‖ ≤ (|C0| + |C1|) * ρ ^ (-3 : ℝ) := by
      intro i
      have : ‖mtField F τ (hpt ρ z') i‖ = ‖F w i‖ := rfl
      rw [this]
      refine (norm_le_pi_norm (F w) i).trans (hb0.trans ?_)
      exact mul_le_mul_of_nonneg_right (by linarith [abs_nonneg C1]) hp
    calc _ ≤ ∑ _i : Fin 3, (|C0| + |C1|) * ρ ^ (-3 : ℝ) := Finset.sum_le_sum fun i _ => hi i
      _ = 3 * (|C0| + |C1|) * ρ ^ (-3 : ℝ) := by simp [Finset.sum_const]; ring
  · have hwU : w ∈ outReg ν ε := by
      show 5 * ν / (6 * ε ^ 2) < cylR w ^ 2
      exact lt_of_lt_of_le hr₀b ha
    have hZd : HasFDerivAt F (fderiv ℝ F w) w :=
      ((hsm.differentiableOn (by simp)).differentiableAt
        ((isOpen_outReg ν ε).mem_nhds hwU)).hasFDerivAt
    have hcomp : ∀ i, HasFDerivAt (fun x => mtField F τ x i)
        ((ContinuousLinearMap.proj i).comp ((fderiv ℝ F w).comp
          (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 3 => ℝ)).toContinuousLinearMap))
        (hpt ρ z') := fun i => by
      have h1 := hZd.comp (hpt ρ z') (PiLp.hasFDerivAt_ofLp (𝕜 := ℝ) 2 (hpt ρ z'))
      have h2 := (hasFDerivAt_apply (𝕜 := ℝ) (F' := fun _ : Fin 3 => ℝ) i (F w)).comp
        (hpt ρ z') h1
      exact h2
    refine (norm_fderiv_le_of_comp hcomp).trans ?_
    have hi : ∀ i : Fin 3, ‖(ContinuousLinearMap.proj i).comp ((fderiv ℝ F w).comp
          (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 3 => ℝ)).toContinuousLinearMap)‖ ≤
        (|C0| + |C1|) * ρ ^ (-3 : ℝ) := by
      intro i
      have hle : ‖(ContinuousLinearMap.proj i).comp ((fderiv ℝ F w).comp
          (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 3 => ℝ)).toContinuousLinearMap)‖ ≤
          ‖fderiv ℝ F w‖ := by
        refine ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _) fun v => ?_
        have hv : ‖WithLp.ofLp v‖ ≤ ‖v‖ :=
          (pi_norm_le_iff_of_nonneg (norm_nonneg v)).2 fun j => PiLp.norm_apply_le v j
        calc ‖(fderiv ℝ F w (WithLp.ofLp v)) i‖ ≤ ‖fderiv ℝ F w (WithLp.ofLp v)‖ :=
              norm_le_pi_norm _ i
          _ ≤ ‖fderiv ℝ F w‖ * ‖WithLp.ofLp v‖ := (fderiv ℝ F w).le_opNorm _
          _ ≤ ‖fderiv ℝ F w‖ * ‖v‖ := mul_le_mul_of_nonneg_left hv (norm_nonneg _)
      refine hle.trans (hb1.trans ?_)
      exact mul_le_mul_of_nonneg_right (by linarith [abs_nonneg C0]) hp
    calc _ ≤ ∑ _i : Fin 3, (|C0| + |C1|) * ρ ^ (-3 : ℝ) := Finset.sum_le_sum fun i _ => hi i
      _ = 3 * (|C0| + |C1|) * ρ ^ (-3 : ℝ) := by simp [Finset.sum_const]; ring

/-! ## `PrimData` on the clear region -/

/-- **`PrimData` from `C¹` on the clear region and far decay** (as `zPrimRegularAt_of`): at a
point `(r, 0, z)` of the clear region choose `r₀ ∈ (ε⁻¹√(ν/1.1), r)`; the half-plane points
`ρ ≥ r₀` lie in the clear region, the value and gradient are `O(ρ⁻³)` far out, hence
`RayDecayW` and `PrimData`. -/
theorem primData_of_clear {ν ε : ℝ} (hε : 0 < ε) {Z : ℝ → Space → Space} {τ : ℝ}
    (hcd : ContDiffOn ℝ 1 (Z τ) (clearSet ε ν))
    (hfar : ∀ r₀ : ℝ, 0 < r₀ → ν / (11 / 10) < (ε * r₀) ^ 2 → ∃ R₁ C : ℝ, ∀ ρ : ℝ, R₁ ≤ ρ →
      r₀ ≤ ρ → ∀ z' : ℝ,
        ‖Z τ (hpt ρ z')‖ ≤ C * ρ ^ (-3 : ℝ) ∧ ‖fderiv ℝ (Z τ) (hpt ρ z')‖ ≤ C * ρ ^ (-3 : ℝ))
    {r z : ℝ} (hr : 0 < r) (hrc : ν / (11 / 10) < (ε * r) ^ 2) : PrimData Z τ r z := by
  set a : ℝ := Real.sqrt (ν / (11 / 10)) with ha
  have ha0 : 0 ≤ a := Real.sqrt_nonneg _
  have hεr : 0 < ε * r := mul_pos hε hr
  have har : a < ε * r := (Real.sqrt_lt' hεr).2 hrc
  set r₀ : ℝ := (ε⁻¹ * a + r) / 2 with hr₀
  have hεinv : ε⁻¹ * (ε * r) = r := by field_simp
  have hεa : ε⁻¹ * a < r := by
    calc ε⁻¹ * a < ε⁻¹ * (ε * r) := mul_lt_mul_of_pos_left har (inv_pos.2 hε)
      _ = r := hεinv
  have hr₀r : r₀ < r := by rw [hr₀]; linarith
  have hr₀pos : 0 < r₀ := by
    rw [hr₀]
    have : 0 ≤ ε⁻¹ * a := mul_nonneg (inv_pos.2 hε).le ha0
    linarith
  have har₀ : a < ε * r₀ := by
    have h1 : ε * (ε⁻¹ * a) = a := by field_simp
    have h2 : ε * (ε⁻¹ * a) < ε * r₀ := by
      apply mul_lt_mul_of_pos_left _ hε
      rw [hr₀]; linarith
    linarith
  have hclear : ∀ ρ : ℝ, r₀ ≤ ρ → ν / (11 / 10) < (ε * ρ) ^ 2 := by
    intro ρ hρ
    have hερ : ε * r₀ ≤ ε * ρ := mul_le_mul_of_nonneg_left hρ hε.le
    exact (Real.sqrt_lt' (by linarith)).1 (lt_of_lt_of_le har₀ hερ)
  have hmem : ∀ ρ : ℝ, r₀ ≤ ρ → ∀ z' : ℝ, hpt ρ z' ∈ clearSet ε ν := by
    intro ρ hρ z'
    have hρ0 : 0 < ρ := lt_of_lt_of_le hr₀pos hρ
    refine ⟨?_, ?_⟩
    · show 0 < ϱ (hpt ρ z')
      rw [ϱ_hpt hρ0]; exact hρ0
    · show ν / (11 / 10) < (ε * ϱ (hpt ρ z')) ^ 2
      rw [ϱ_hpt hρ0]; exact hclear ρ hρ
  obtain ⟨R₁, C, hC⟩ := hfar r₀ hr₀pos (hclear r₀ le_rfl)
  obtain ⟨K', hK'⟩ := rayDecayW_of (GeomYAGen.isOpen_clearSet ε ν) hcd hr₀pos hmem (R₁ := R₁) (C := C)
    (fun ρ h1 h2 z' => hC ρ h1 h2 z') z
  exact primData_of_decayW hK' hr₀pos one_pos hr₀r

/-! ## The fields of `Y_A` -/

section Fields

variable (Pl : PlanarData) (K : ReturnConsts) (L : ReturnLevel) (μ : ℝ)

/-- The separated representative of the old thin source turns `zWAct` into `sepWre`. -/
theorem zWAct_eq_sepWre {S : ℝ → Space → Matrix (Fin 3) (Fin 3) ℝ} (T : LStr Pl K L)
    (hresp : ∀ (μ' : ℂ) (y : Space) (τ : ℝ),
      IIIa.sepW L.ν μ' (oldPhys L.ε⁻¹ (cOf L.ν) (thinG Pl K L T)) y τ = IIIa.sepW L.ν μ' S y τ)
    (τ : ℝ) : zWAct Pl K L μ T τ = sepWre L.ν μ S τ := by
  funext y
  simp only [zWAct, thinWardW, sepWre, hresp]

/-- `zWAct` is `C²` on the clear region, at every phase. -/
theorem zWAct_cd (hC0 : 0 < K.C0) (hmZ : 0 ≤ K.mZ) (hμ : -(1 / 4) < μ) (T : LStr Pl K L)
    (τ : ℝ) : ContDiffOn ℝ 2 (zWAct Pl K L μ T τ) (clearSet L.ε L.ν) := by
  have hν := L.ν_pos
  have hε := L.ε_pos
  obtain ⟨S, hS1, hS2, -, hresp⟩ := Sub8_1_1_2_3.thinSepData Pl K L hC0 hmZ T
  have hP : 0 < 2 * L.ε * cOf L.ν := by have := cOf_pos hν; positivity
  rw [zWAct_eq_sepWre Pl K L μ T hresp τ]
  exact (sepWre_cd hν hμ (by positivity) hP hS1 hS2 τ).mono (clear_sub_young hε hν)

/-- `zWMid` is `C²` on the clear region, at every phase: the phase mean `meanQ c (thinG T)` has
finite `|G|²` moment and vanishes a.e. for `νs ≤ 6/5` (Jensen, `ZRegAux.mean_moment_le`,
`ZRegAux.mean_ae_zero`), so it gives an a.e. separated source (`sepSrc_of_chart`). -/
theorem zWMid_cd (hC0 : 0 < K.C0) (hmZ : 0 ≤ K.mZ) (hμ : -(1 / 4) < μ) (T : LStr Pl K L)
    (τ : ℝ) : ContDiffOn ℝ 2 (zWMid Pl K L μ T τ) (clearSet L.ε L.ν) := by
  have hν := L.ν_pos
  have hε := L.ε_pos
  have hc := cOf_pos hν
  have hρb := rho_b_pos' Pl K L hC0
  set Tc := chiOStr (cOf L.ν) K.mZ (L.ρb Pl K) (gRate Pl) L.ν K.hχo (thinPart T) with hTc
  have hGdef : thinG Pl K L T = strSum Tc := rfl
  have hGm : Measurable (thinG Pl K L T) := by
    unfold thinG
    exact (Lp.stronglyMeasurable _).measurable.add (Lp.stronglyMeasurable _).measurable
  have hmom : ∫⁻ p, ‖thinG Pl K L T p‖ₑ ^ 2 ∂(ageμ (cOf L.ν) (-1 / 2)) < ⊤ := by
    rw [hGdef]
    exact strChartL2 (cOf L.ν) K.mZ (L.ρb Pl K) (gRate Pl) L.ν hρb hmZ hν Tc
  have hz : ∀ᵐ p ∂(ageμ (cOf L.ν) (-1 / 2)), L.ν * p.1 ≤ 6 / 5 → thinG Pl K L T p = 0 := by
    rw [hGdef]
    exact strSum_zero_young _ _ _ _ _ K.hχo hρb _
  have hGm' := measurable_meanQ' (cOf L.ν) hGm
  have hmom' : ∫⁻ p, ‖meanQ (cOf L.ν) (thinG Pl K L T) p‖ₑ ^ 2 ∂(ageμ (cOf L.ν) (-1 / 2)) < ⊤ :=
    lt_of_le_of_lt (mean_moment_le _ _ hc _ hGm) hmom
  have hz' := mean_ae_zero (cOf L.ν) (-1 / 2) L.ν hc _ hGm hz
  obtain ⟨P2, T2, hP2, hS2, hM2, hE2⟩ :=
    sepSrc_of_chart (cOf L.ν) L.ν L.ε hc hν hε _ hGm' hmom' hz'
  have heq : zWMid Pl K L μ T τ = sepWre L.ν μ T2 τ := by
    funext y
    simp only [zWMid, sepWre, hE2]
  rw [heq]
  exact (sepWre_cd hν hμ (by positivity) hP2 hS2 hM2 τ).mono (clear_sub_young hε hν)

/-- `ZRegularYAAt` at one regime. -/
theorem zRegularYAAt_of (hmZ : 3 / 2 < K.mZ) (hγ : 0 < gRate Pl) (hC0 : 0 < K.C0) :
    ZRegularYAAt Pl K L μ := by
  intro hLH T τ Z hZ
  have hν := L.ν_pos
  have hε := L.ε_pos
  have hc := hLH.c_pos
  have hμ : -(1 / 4) < μ := by linarith [hLH.mu_pos]
  rcases hZ with rfl | hZ
  · -- `zWAct = Re W_μ` of the old thin source
    obtain ⟨S, hS1, hS2, -, hresp⟩ := Sub8_1_1_2_3.thinSepData Pl K L hC0 (by linarith) T
    have heq := zWAct_eq_sepWre Pl K L μ T hresp τ
    have hro : 0 < L.ε⁻¹ * Real.sqrt (5 * L.ν / 6) :=
      mul_pos (inv_pos.2 hε) (Real.sqrt_pos.2 (by positivity))
    have hP : 0 < 2 * L.ε * cOf L.ν := by have := cOf_pos hν; positivity
    have hcd : ContDiffOn ℝ 1 (zWAct Pl K L μ T τ) (clearSet L.ε L.ν) :=
      (zWAct_cd Pl K L μ hC0 (by linarith) hμ T τ).of_le (by norm_num)
    refine ⟨hcd, fun y hy => ?_, fun r z hr hrc => ?_⟩
    · rw [heq]
      exact sepWre_tendsto hν hμ hro.le hP hS1 hS2 τ hy.1
    · refine primData_of_clear hε hcd (fun r₀ _ _ => ?_) hr hrc
      obtain ⟨C, hC⟩ := sepWre_far hν hμ hro hP hS1 hS2 τ
      exact ⟨2 * (L.ε⁻¹ * Real.sqrt (5 * L.ν / 6)), C, fun ρ hρ _ z' => by
        rw [heq]; exact hC ρ hρ z'⟩
  · -- `zWMt = W^mt_μ`, the zero-width Young field
    rw [Set.mem_singleton_iff] at hZ
    subst hZ
    obtain ⟨C, k, hCk⟩ := sourceLN0 K.mZ (gRate Pl) hmZ hγ
    have hfin : OldThinFinite (cOf L.ν) L.ν (thinRep T) :=
      (hCk (cOf L.ν) L.ν (L.ρb Pl K) hc hν hLH.nu_le T).1
    have hsm := xsYoungWSmooth (cOf L.ν) L.ν L.ε μ K.χo (thinRep T) hc hν hε hLH.mu_pos
      hLH.chiO hfin
    have hdec : MtDecay L.ν L.ε (youngW (cOf L.ν) L.ν L.ε μ K.χo (thinRep T)) :=
      xsYoungWDecay (cOf L.ν) L.ν L.ε μ K.χo (thinRep T) hc hν hε hLH.mu_pos hLH.chiO hfin
    obtain ⟨hcd, htd⟩ := mt_regular hν hε hsm hdec τ
    refine ⟨hcd, htd, fun r z hr hrc => ?_⟩
    refine primData_of_clear hε hcd (fun r₀ hr₀ hrc₀ => ?_) hr hrc
    have hr₀b : 5 * L.ν / (6 * L.ε ^ 2) < r₀ ^ 2 := by
      have h6 : 0 < 6 * L.ε ^ 2 := by positivity
      rw [div_lt_iff₀ h6]
      have : 5 * L.ν / 6 < L.ν / (11 / 10) := by
        rw [div_lt_div_iff₀ (by norm_num) (by norm_num)]; nlinarith
      nlinarith [mul_pow L.ε r₀ 2]
    obtain ⟨C', hC'⟩ := mt_far hsm hdec hr₀ hr₀b τ
    exact ⟨r₀, C', fun ρ _ hρ z' => hC' ρ hρ z'⟩

end Fields

end ZRegYA

open ZRegYA in
/-- **`PartIII-b:C/rep/8/1/1/2/4/3`** (`zRegularYA`): at every level, under the standing
hypotheses, `W_μ` of the old thin source and `W^mt_μ` are `C¹` on the clear region, tend to zero
along every outward ray, and have convergent, differentiable outward primitives (source
4178-4186, 5400-5413, 4163-4166). -/
theorem zRegularYA (D : SeqData) {dm dp : ℝ} (hst : D.RepairStanding dm dp) : D.ZRegularYA := by
  unfold SeqData.ZRegularYA
  exact Filter.Eventually.of_forall fun n z _ =>
    zRegularYAAt_of D.Pl D.K (D.level n) (D.mu n z) hst.mZ_gt hst.gamma_pos hst.C0_pos

end UnforcedLeray.Short.PartIIIb.Concrete
