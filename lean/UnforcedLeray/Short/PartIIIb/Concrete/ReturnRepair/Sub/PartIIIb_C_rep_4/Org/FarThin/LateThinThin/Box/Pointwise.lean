import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_4.Org.FarThin.LateThinThin.Box.Slice
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_rep_5_1_1_3_3_1_1.FarPointDom
import UnforcedLeray.Short.PartIIIb.Sub.IIIb_D2_3_1_1_1.L4

/-!
# `PartIII-b:C/rep/4/1/org/2/1` (c): the separated pointwise velocity `≤ P_ν ε² s² N₀(e^δ s)`

Source `the November 2 reference manuscript` 5342-5355 ("the separated pointwise
velocity is at most `P_νε²s²N₀(e^δ s)`"), 3604-3621 (`|∇K_t(x)| ≤ C|x|^{-4}`, `sep:resolvent`),
3905-3912 and 5588-5589 (the mask `t > e^δ s` gives `ϱ(z) < θϱ(y)`, `θ = e^{-δ/2}`, hence the
radial gap `|y - λz| ≥ (1-θ)ϱ(y) = (1-θ)R/√s`), 5573-5576 (`N₀`).

`farPt_le`: for a measurable chart tensor `g` and a chart point of age `s`,
`farPt ≤ 18|C| ((1-θ)R/√s)^{-4} πR² N₀(e^δ s)`, `R = ε⁻¹`: the pointwise bound `fpd_sepWfar_le`,
the gap, Minkowski over the atoms (`minkowski_shift_disk`) and the disk mass (`disk_mass`).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology UnforcedLeray.Axi
open scoped ENNReal

namespace UnforcedLeray.Short.PartIIIb.Concrete.FTT

open UnforcedLeray.Short.PartIIIb.Concrete.WYCore

/-- A vector of `ℂ³` has `ℝ≥0∞`-norm at most the common bound of its components. -/
theorem enorm_pi_le {X : ℝ≥0∞} (f : Fin 3 → ℂ) (h : ∀ i, ‖f i‖ₑ ≤ X) : ‖f‖ₑ ≤ X := by
  rcases eq_or_ne X ⊤ with rfl | hX
  · exact le_top
  lift X to NNReal using hX
  rw [enorm_eq_nnnorm]
  have : ‖f‖₊ ≤ X := by
    refine pi_nnnorm_le_iff.2 fun i => ?_
    have := h i
    rw [enorm_eq_nnnorm] at this
    exact_mod_cast this
  exact_mod_cast this

/-- The mask gives the disk: for `ϱ z ≠ 0`, `ϱ z < θϱ(y)` iff `e^δ s < age z` (`ϱ y = R/√s`,
`θ = e^{-δ/2}`). -/
theorem disk_iff {R δ s : ℝ} (hR : 0 < R) (hs : 0 < s) {y z : Space} (hy : ϱ y = R / Real.sqrt s)
    (hz : ϱ z ≠ 0) :
    ϱ z < Real.exp (-(δ / 2)) * ϱ y ↔ Real.exp δ * s < age R z := by
  have hzpos : 0 < ϱ z := lt_of_le_of_ne (Real.sqrt_nonneg _) (Ne.symm hz)
  have hss : 0 < Real.sqrt s := Real.sqrt_pos.2 hs
  have hθ : 0 < Real.exp (-(δ / 2)) := Real.exp_pos _
  have hprod : Real.exp (-(δ / 2)) ^ 2 * Real.exp δ = 1 := by
    rw [← Real.exp_nat_mul, ← Real.exp_add]
    norm_num
    ring_nf
  unfold age
  rw [hy, lt_div_iff₀ (by positivity)]
  constructor
  · intro h
    have h1 : ϱ z * Real.sqrt s < Real.exp (-(δ / 2)) * R := by
      have := mul_lt_mul_of_pos_right h hss
      calc ϱ z * Real.sqrt s < Real.exp (-(δ / 2)) * (R / Real.sqrt s) * Real.sqrt s := this
        _ = Real.exp (-(δ / 2)) * R := by field_simp
    have h2 : (ϱ z * Real.sqrt s) ^ 2 < (Real.exp (-(δ / 2)) * R) ^ 2 :=
      pow_lt_pow_left₀ h1 (by positivity) (by norm_num)
    have h3 : (ϱ z * Real.sqrt s) ^ 2 = ϱ z ^ 2 * s := by
      rw [mul_pow, Real.sq_sqrt hs.le]
    rw [h3] at h2
    nlinarith [mul_pos hθ hθ, Real.exp_pos δ]
  · intro h
    have h1 : ϱ z ^ 2 * s < (Real.exp (-(δ / 2)) * R) ^ 2 := by
      nlinarith [mul_pos hθ hθ, Real.exp_pos δ, sq_nonneg (ϱ z)]
    have h3 : (ϱ z * Real.sqrt s) ^ 2 = ϱ z ^ 2 * s := by
      rw [mul_pow, Real.sq_sqrt hs.le]
    rw [← h3] at h1
    have h2 : ϱ z * Real.sqrt s < Real.exp (-(δ / 2)) * R :=
      lt_of_pow_lt_pow_left₀ 2 (by positivity) h1
    calc ϱ z = ϱ z * Real.sqrt s / Real.sqrt s := by field_simp
      _ < Real.exp (-(δ / 2)) * R / Real.sqrt s := by gcongr
      _ = Real.exp (-(δ / 2)) * (R / Real.sqrt s) := by ring

/-- `srcNorm (𝒩_T g) ≤ srcW` (source 2683: `|𝒩_T g| ≤ age(z)·|g(chartOf z σ)|`). -/
theorem srcNorm_le_srcW (R c : ℝ) (g : Chart → Ten3) (σ : ℝ) (z : Space) :
    UnforcedLeray.Short.IIIa.srcNorm (NearInst.cartLift R c g) σ z ≤
      srcW R c (fun q => ‖g q‖ₑ) σ z := by
  show ENNReal.ofReal (UnforcedLeray.Short.IIIa.tensorNorm (oldPhys R c g σ z)) ≤
    ENNReal.ofReal (age R z) * ‖g (NearInst.chartOf R c z σ)‖ₑ
  have hage : 0 ≤ age R z := by unfold age; positivity
  have he : ‖g (NearInst.chartOf R c z σ)‖ₑ = ENNReal.ofReal ‖g (NearInst.chartOf R c z σ)‖ := by
    first
      | exact (ofReal_norm' _).symm
      | simp [ofReal_norm', enorm_eq_nnnorm]
      | rfl
  rw [he, ← ENNReal.ofReal_mul hage]
  apply ENNReal.ofReal_le_ofReal
  exact cartLiftFrobBound R c g σ z

/-- **The separated pointwise velocity** (source 5342-5355, 3611-3621, 5588-5589):
`farPt ≤ 18|C| ((1-θ)R/√s)^{-4} πR² N₀(e^δ s)`, `θ = e^{-δ/2}`. -/
theorem farPt_le {C : ℝ} (hC : FarKerDeriv C) {ν μ R c δ : ℝ} (hν : 0 < ν) (hR : 0 < R)
    (hc : 0 < c) (hμ : -(1 / 4) < μ) (hδ : 0 < δ) (g : Chart → Ten3) (hg : Measurable g)
    (p : Chart) (hp : 0 < p.1) :
    farPt R c ν μ δ g p ≤
      ENNReal.ofReal (18 * |C| * ((((1 - Real.exp (-(δ / 2))) * (R / Real.sqrt p.1)) ^ 4)⁻¹) *
        (Real.pi * R ^ 2)) * thinMass c g (Real.exp δ * p.1) := by
  have hsq : 0 < Real.sqrt p.1 := Real.sqrt_pos.2 hp
  have hP : 0 < 2 * c / R := div_pos (mul_pos two_pos hc) hR
  unfold farPt UnforcedLeray.Short.IIIa.ltauAt
  rw [← ENNReal.ofReal_inv_of_pos hP]
  have hy : ϱ (NearInst.chartY R p) = R / Real.sqrt p.1 := by
    unfold ϱ NearInst.chartY
    simp only [WithLp.ofLp_toLp]
    rw [show (![R / Real.sqrt p.1, 0, p.2.2 / Real.sqrt p.1] : Fin 3 → ℝ) 0 = R / Real.sqrt p.1
      from rfl, show (![R / Real.sqrt p.1, 0, p.2.2 / Real.sqrt p.1] : Fin 3 → ℝ) 1 = 0
      from rfl]
    rw [zero_pow (by norm_num), add_zero, Real.sqrt_sq (by positivity)]
  set y := NearInst.chartY R p with hydef
  set θ := Real.exp (-(δ / 2)) with hθdef
  have hθ1 : θ < 1 := by
    rw [hθdef, ← Real.exp_zero]
    exact Real.exp_lt_exp.2 (by linarith)
  set D := (1 - θ) * (R / Real.sqrt p.1) with hDdef
  have hD : 0 < D := mul_pos (sub_pos.2 hθ1) (by positivity)
  set Dk : Set Space := {z : Space | ϱ z < θ * ϱ y} with hDk
  have hDkm : MeasurableSet Dk := measurableSet_lt measurable_ϱ measurable_const
  set A : ℝ≥0∞ := ENNReal.ofReal (18 * |C| * (D ^ 4)⁻¹) with hA
  -- step 1: the pointwise bound
  have hK : ∀ τ : ℝ, ‖NearInst.sepWfar ν (μ : ℂ) R δ p.1 (NearInst.cartLift R c g) y τ‖ₑ ≤
      A * ∫⁻ l in Ioo (0 : ℝ) 1, ∫⁻ z in Dk, srcW R c (fun q => ‖g q‖ₑ) (τ + 2 * Real.log l) z := by
    intro τ
    refine enorm_pi_le _ fun i => ?_
    refine (fpd_sepWfar_le hC hν hμ hR hδ hp (NearInst.cartLift R c g) y hy i).trans ?_
    have hin : ∀ l ∈ Ioo (0 : ℝ) 1, ∫⁻ z in Dk, ENNReal.ofReal ((‖y - l • z‖ ^ 4)⁻¹) *
        UnforcedLeray.Short.IIIa.srcNorm (NearInst.cartLift R c g) (τ + 2 * Real.log l) z ≤
        ENNReal.ofReal ((D ^ 4)⁻¹) *
          ∫⁻ z in Dk, srcW R c (fun q => ‖g q‖ₑ) (τ + 2 * Real.log l) z := by
      intro l hl
      rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
      refine setLIntegral_mono' hDkm fun z hz => ?_
      refine mul_le_mul' (ENNReal.ofReal_le_ofReal ?_) (srcNorm_le_srcW R c g _ z)
      have hgap : D ≤ ‖y - l • z‖ := by
        have := fpd_gap hl.1 hl.2 hz
        rwa [hy] at this
      exact inv_anti₀ (pow_pos hD 4) (pow_le_pow_left₀ hD.le hgap 4)
    have h2 : ∫⁻ l in Ioo (0 : ℝ) 1, ∫⁻ z in Dk, ENNReal.ofReal ((‖y - l • z‖ ^ 4)⁻¹) *
        UnforcedLeray.Short.IIIa.srcNorm (NearInst.cartLift R c g) (τ + 2 * Real.log l) z ≤
        ENNReal.ofReal ((D ^ 4)⁻¹) *
          ∫⁻ l in Ioo (0 : ℝ) 1, ∫⁻ z in Dk, srcW R c (fun q => ‖g q‖ₑ) (τ + 2 * Real.log l) z := by
      rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
      exact setLIntegral_mono' measurableSet_Ioo hin
    calc ENNReal.ofReal (18 * |C|) * _ ≤ ENNReal.ofReal (18 * |C|) * (ENNReal.ofReal ((D ^ 4)⁻¹) *
          ∫⁻ l in Ioo (0 : ℝ) 1, ∫⁻ z in Dk,
            srcW R c (fun q => ‖g q‖ₑ) (τ + 2 * Real.log l) z) := mul_le_mul' le_rfl h2
      _ = A * _ := by
        rw [← mul_assoc, ← ENNReal.ofReal_mul (by positivity)]
  -- step 2: the `L²_τ` norm
  set K : ℝ → ℝ≥0∞ := fun τ => ∫⁻ l in Ioo (0 : ℝ) 1, ∫⁻ z in Dk,
    srcW R c (fun q => ‖g q‖ₑ) (τ + 2 * Real.log l) z with hKdef
  have hmink := minkowski_shift_disk (G := fun q => ‖g q‖ₑ) hR hc hg.enorm Dk hDkm
  have hmass := disk_mass (R := R) (c := c) (a := Real.exp δ * p.1) hR
    (mul_pos (Real.exp_pos δ) hp) g hg Dk hDkm (fun z hz => disk_iff hR hp hy hz) hc
  calc _
      ≤ (ENNReal.ofReal (2 * c / R)⁻¹ * ∫⁻ τ in Ioc 0 (2 * c / R), (A * K τ) ^ (2 : ℝ)) ^
        (1 / 2 : ℝ) := by
        gcongr with τ
        exact hK τ
    _ = A * (ENNReal.ofReal (2 * c / R)⁻¹ ^ (1 / 2 : ℝ) *
          (∫⁻ τ in Ioc 0 (2 * c / R), K τ ^ (2 : ℝ)) ^ (1 / 2 : ℝ)) := by
        have h1 : ∀ τ : ℝ, (A * K τ) ^ (2 : ℝ) = A ^ (2 : ℝ) * K τ ^ (2 : ℝ) := fun τ =>
          ENNReal.mul_rpow_of_nonneg _ _ (by norm_num)
        simp only [h1]
        have hAne : A ^ (2 : ℝ) ≠ ⊤ :=
          ENNReal.rpow_ne_top_of_nonneg (by norm_num) ENNReal.ofReal_ne_top
        rw [lintegral_const_mul' _ _ hAne, ← mul_assoc, mul_comm _ (A ^ (2 : ℝ)), mul_assoc,
          ENNReal.mul_rpow_of_nonneg _ _ (by norm_num), ENNReal.mul_rpow_of_nonneg _ _ (by norm_num),
          ← ENNReal.rpow_mul, show (2 : ℝ) * (1 / 2) = 1 by norm_num, ENNReal.rpow_one]
    _ ≤ A * (ENNReal.ofReal (2 * c / R)⁻¹ ^ (1 / 2 : ℝ) *
          ∫⁻ z in Dk, (∫⁻ τ in Ioc 0 (2 * c / R),
            srcW R c (fun q => ‖g q‖ₑ) τ z ^ (2 : ℝ)) ^ (1 / 2 : ℝ)) := by
        gcongr
    _ = A * ∫⁻ z in Dk, ENNReal.ofReal (age R z) * sliceL2q c g (age R z) (trans R z) := by
        congr 1
        rw [← lintegral_const_mul' _ _ (ENNReal.rpow_ne_top_of_nonneg (by norm_num)
          ENNReal.ofReal_ne_top)]
        exact lintegral_congr fun z => srcW_slice hR hc g z
    _ = _ := by
        rw [hmass, ← mul_assoc, hA, ← ENNReal.ofReal_mul (by positivity)]

end UnforcedLeray.Short.PartIIIb.Concrete.FTT

end
