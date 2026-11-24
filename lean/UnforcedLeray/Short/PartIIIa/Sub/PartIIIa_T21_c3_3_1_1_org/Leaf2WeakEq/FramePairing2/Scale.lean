import UnforcedLeray.Short.PartIIIa.Sub.PartIIIa_T21_c3_3_1_1_org.Leaf2WeakEq.FramePairing2.Core
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_asrc_kflat_1_2_3_1.KcEmbed.BSScale
import UnforcedLeray.Short.PartIIIa.Clock.LongAssemble.L4
import UnforcedLeray.Short.PartIIIa.Sub.PartIIIa_T21_c5_3_2

/-!
# Helper for `PartIII-a:T21/c3/3/1/1/2/2/3/c/2`: scaling of the kernel velocity

Source `the November 2 reference manuscript` (SP) lines 2863-2865, 2937-2958,
2983 (`J_a⁻¹ f(y) = a² f(√a y)`).
* `memLp_JscaleInv_pos`: `J_a⁻¹` maps `X_{m,c}` into `X_{m,c/√a}` for every `a > 0`
  (`⟨y⟩² ≤ max(1, a⁻¹) ⟨√a y⟩²`).
* `kerVelCx_jscaleInv`: `K_{c/√a}(J_a⁻¹ f)(y) = a^{3/2} (K_c f)(√a y)` (scaling of the kernel).
* `kerVelCx_ae_eq_of_isBiotSavart_pos`: the identification `U = K_D Ω` of `Core.lean` for every
  cell length `D > 0` (rescale to the cell of length `1`).
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal

namespace UnforcedLeray.Short.IIIa.ComplFreeRateSub.Leaf2WeakEqFrame.KerBSAux

open UnforcedLeray.Short.IIIa

/-- `J_a⁻¹` maps `X_{m,c}` into `X_{m,c/√a}` for every `a > 0`. -/
theorem memLp_JscaleInv_pos {c m a : ℝ} (hm : 0 ≤ m) (ha : 0 < a) {g : ℝ × ℝ → ℂ}
    (hg : MemLp g 2 (B0579.cellMeasure c m)) :
    MemLp (JscaleInv a g) 2 (B0579.cellMeasure (cellLen c a) m) := by
  obtain ⟨h, hmeas, hgh, -⟩ := ae_representative_xNorm c m g hg
  have hJh_meas : Measurable (JscaleInv a h) := by
    unfold JscaleInv
    exact measurable_const.mul (hmeas.comp
      ((measurable_const.mul measurable_fst).prodMk (measurable_const.mul measurable_snd)))
  have hgh' : ∀ᵐ x ∂(volume.restrict (B0579.cell c)), g x = h x :=
    (B0579.ac_cellMeasure c m).ae_le hgh
  have hae := jscale_ae_of_ae c a ha g h hgh'
  have hae2 : JscaleInv a g =ᵐ[B0579.cellMeasure (cellLen c a) m] JscaleInv a h :=
    (B0579.cellMeasure_ac (cellLen c a) m).ae_le hae
  refine ⟨hJh_meas.aestronglyMeasurable.congr hae2.symm, ?_⟩
  set G : ℝ × ℝ → ℂ := fun x => ((B0579.jb x ^ (m / 2) : ℝ) : ℂ) * g x with hG
  have hGfin : eLpNorm G 2 (volume.restrict (B0579.cell c)) < ∞ := by
    rw [← eLpNorm_cellMeasure_cx]
    exact hg.2
  set M : ℝ := max 1 a⁻¹ with hMdef
  have hM : 0 ≤ M := le_trans zero_le_one (le_max_left _ _)
  have hs : (Real.sqrt a) ^ 2 = a := Real.sq_sqrt ha.le
  have hpt : ∀ y : ℝ × ℝ, ‖((B0579.jb y ^ (m / 2) : ℝ) : ℂ) * JscaleInv a g y‖ ≤
      (a ^ 2 * M ^ (m / 2)) * ‖((1 : ℝ) : ℂ) * G (Real.sqrt a • y)‖ := by
    intro y
    have hjb : B0579.jb y ≤ M * B0579.jb (Real.sqrt a • y) := by
      have e : B0579.jb (Real.sqrt a • y) = 1 + a * y.1 ^ 2 + a * y.2 ^ 2 := by
        simp only [B0579.jb, Prod.smul_fst, Prod.smul_snd, smul_eq_mul, mul_pow, hs]
      rw [e]
      unfold B0579.jb
      have h1 : 1 ≤ M := le_max_left _ _
      have h2 : a⁻¹ ≤ M := le_max_right _ _
      have h3 : 1 ≤ M * a := by
        calc (1 : ℝ) = a⁻¹ * a := (inv_mul_cancel₀ ha.ne').symm
          _ ≤ M * a := by gcongr
      nlinarith [sq_nonneg y.1, sq_nonneg y.2]
    have hpow : B0579.jb y ^ (m / 2) ≤ M ^ (m / 2) * B0579.jb (Real.sqrt a • y) ^ (m / 2) := by
      rw [← Real.mul_rpow hM (B0579.jb_pos _).le]
      exact Real.rpow_le_rpow (B0579.jb_pos y).le hjb (by linarith)
    have e2 : (Real.sqrt a * y.1, Real.sqrt a * y.2) = Real.sqrt a • y := rfl
    simp only [JscaleInv, hG, norm_mul, Complex.norm_real, Real.norm_eq_abs, e2]
    rw [abs_of_nonneg (Real.rpow_nonneg (B0579.jb_pos y).le _),
      abs_of_nonneg (by positivity : (0 : ℝ) ≤ a ^ 2),
      abs_of_nonneg (Real.rpow_nonneg (B0579.jb_pos _).le _), abs_one, one_mul]
    have hn : 0 ≤ ‖g (Real.sqrt a • y)‖ := norm_nonneg _
    have ha2 : 0 ≤ a ^ 2 := by positivity
    calc B0579.jb y ^ (m / 2) * (a ^ 2 * ‖g (Real.sqrt a • y)‖)
        ≤ (M ^ (m / 2) * B0579.jb (Real.sqrt a • y) ^ (m / 2)) * (a ^ 2 * ‖g (Real.sqrt a • y)‖) :=
          mul_le_mul_of_nonneg_right hpow (mul_nonneg ha2 hn)
      _ = a ^ 2 * M ^ (m / 2) * (B0579.jb (Real.sqrt a • y) ^ (m / 2) * ‖g (Real.sqrt a • y)‖) := by
          ring
  rw [eLpNorm_cellMeasure_cx]
  refine lt_of_le_of_lt (eLpNorm_le_mul_eLpNorm_of_ae_le_mul (Eventually.of_forall hpt) 2) ?_
  refine ENNReal.mul_lt_top ENNReal.ofReal_lt_top ?_
  have key := eLpNorm_sq_scale_aux (c := c) ha 1 G
  set X := eLpNorm (fun y : ℝ × ℝ => ((1 : ℝ) : ℂ) * G (Real.sqrt a • y)) 2
    (volume.restrict (B0579.cell (cellLen c a))) with hX
  rcases eq_or_ne X ⊤ with hXt | hXt
  · exfalso
    rw [hXt] at key
    have ha' : ENNReal.ofReal a ≠ 0 := by simpa using ha
    have htop : ENNReal.ofReal a * (⊤ : ℝ≥0∞) ^ 2 = ⊤ := by
      rw [ENNReal.top_pow two_ne_zero, ENNReal.mul_top ha']
    rw [htop] at key
    exact (ENNReal.mul_lt_top ENNReal.ofReal_lt_top (ENNReal.pow_lt_top hGfin)).ne key.symm
  · exact lt_top_iff_ne_top.2 hXt

/-- Scaling of the kernel velocity: `K_{c/√a}(J_a⁻¹ f)(y) = a^{3/2} (K_c f)(√a y)`. -/
theorem kerVelCx_jscaleInv {c a : ℝ} (ha : 0 < a) (f : ℝ × ℝ → ℂ) (y : ℝ × ℝ) (k : Fin 2) :
    kerVelCx (cellLen c a) (JscaleInv a f) y k =
      ((a ^ ((3 : ℝ) / 2) : ℝ) : ℂ) * kerVelCx c f (Real.sqrt a * y.1, Real.sqrt a * y.2) k := by
  have hs : 0 < Real.sqrt a := Real.sqrt_pos.2 ha
  set Y : ℝ × ℝ := (Real.sqrt a * y.1, Real.sqrt a * y.2) with hY
  set H : ℝ × ℝ → ℂ := fun x => f x * ((kerD c (Y - x) k : ℝ) : ℂ) with hH
  have h52 : a ^ ((5 : ℝ) / 2) = a ^ 2 * Real.sqrt a := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast, ← Real.rpow_add ha]
    norm_num
  have h53 : a ^ ((5 : ℝ) / 2) = a ^ ((3 : ℝ) / 2) * a := by
    rw [show (5 : ℝ) / 2 = 3 / 2 + 1 by norm_num, Real.rpow_add ha, Real.rpow_one]
  have hpt : ∀ z : ℝ × ℝ, JscaleInv a f z * ((kerD (cellLen c a) (y - z) k : ℝ) : ℂ) =
      ((a ^ ((5 : ℝ) / 2) : ℝ) : ℂ) * H (Real.sqrt a * z.1, Real.sqrt a * z.2) := by
    intro z
    have hk := ComplCouplingEuler.kerD_scale c a ha (y - z) k
    have hYZ : (Real.sqrt a * (y - z).1, Real.sqrt a * (y - z).2) =
        Y - (Real.sqrt a * z.1, Real.sqrt a * z.2) := by
      ext <;> simp [hY] <;> ring
    rw [hYZ] at hk
    have hk' : kerD (cellLen c a) (y - z) k =
        Real.sqrt a * kerD c (Y - (Real.sqrt a * z.1, Real.sqrt a * z.2)) k := by
      rw [hk]
      field_simp
    simp only [JscaleInv, hH]
    rw [hk', h52]
    push_cast
    ring
  have hcv := cv_cell (c := c) ha H
  have hcv' : ∫ z in B0579.cell (cellLen c a), H (Real.sqrt a * z.1, Real.sqrt a * z.2) =
      ((a : ℂ))⁻¹ * ∫ z in B0579.cell c, H z := by
    rw [← hcv, Complex.real_smul, ← mul_assoc, inv_mul_cancel₀ (by exact_mod_cast ha.ne'),
      one_mul]
  unfold kerVelCx
  calc ∫ z in B0579.cell (cellLen c a), JscaleInv a f z * ((kerD (cellLen c a) (y - z) k : ℝ) : ℂ)
      = ∫ z in B0579.cell (cellLen c a),
          ((a ^ ((5 : ℝ) / 2) : ℝ) : ℂ) * H (Real.sqrt a * z.1, Real.sqrt a * z.2) :=
        integral_congr_ae (Eventually.of_forall hpt)
    _ = ((a ^ ((5 : ℝ) / 2) : ℝ) : ℂ) * (((a : ℂ))⁻¹ * ∫ z in B0579.cell c, H z) := by
        rw [integral_const_mul, hcv']
    _ = ((a ^ ((3 : ℝ) / 2) : ℝ) : ℂ) * ∫ z in B0579.cell c, H z := by
        have hac : (a : ℂ) ≠ 0 := by exact_mod_cast ha.ne'
        rw [h53, Complex.ofReal_mul, mul_assoc, ← mul_assoc (a : ℂ), mul_inv_cancel₀ hac,
          one_mul]

/-- **Kernel velocity = Biot-Savart velocity** for every cell length `D > 0` (`m > 8`). -/
theorem kerVelCx_ae_eq_of_isBiotSavart_pos {D m : ℝ} (hD : 0 < D) (hm : 8 < m)
    {Ω : ℝ × ℝ → ℂ} {U : ℝ × ℝ → Fin 2 → ℂ} (hΩ : MemLp Ω 2 (B0579.cellMeasure D m))
    (hZ : HasZeroCirculation D Ω) (hU : IsBiotSavart D Ω U) :
    ∀ᵐ x ∂(volume.restrict (B0579.cell D)), ∀ k : Fin 2, U x k = kerVelCx D Ω x k := by
  set a : ℝ := D ^ 2 with ha_def
  have ha : 0 < a := by positivity
  have hsa : Real.sqrt a = D := Real.sqrt_sq hD.le
  have hcl : cellLen D a = 1 := by
    unfold cellLen
    rw [hsa, div_self hD.ne']
  have hBS := PartIIIb.Concrete.isBiotSavart_jscaleInv D a hD ha Ω U hU
  rw [hcl] at hBS
  have hmem := memLp_JscaleInv_pos (c := D) (by linarith : (0 : ℝ) ≤ m) ha hΩ
  rw [hcl] at hmem
  have hint : IntegrableOn (JscaleInv a Ω) (B0579.cell 1) :=
    integrableOn_cell_of_X (by linarith) hmem
  have hcv := cv_cell (c := D) ha Ω
  rw [hcl, hZ.2] at hcv
  have hX : ∫ y in B0579.cell 1, Ω (Real.sqrt a * y.1, Real.sqrt a * y.2) = 0 := by
    rw [Complex.real_smul] at hcv
    rcases mul_eq_zero.1 hcv with h | h
    · exact absurd h (by exact_mod_cast ha.ne')
    · exact h
  have hZ1 : HasZeroCirculation 1 (JscaleInv a Ω) := by
    refine ⟨hint, ?_⟩
    unfold JscaleInv
    rw [integral_const_mul, hX, mul_zero]
  have h1 := kerVelCx_ae_eq_of_isBiotSavart le_rfl hm hmem hZ1 hBS
  have hK : ∀ y k, kerVelCx 1 (JscaleInv a Ω) y k =
      ((a ^ ((3 : ℝ) / 2) : ℝ) : ℂ) * kerVelCx D Ω (Real.sqrt a * y.1, Real.sqrt a * y.2) k := by
    intro y k
    have := kerVelCx_jscaleInv (c := D) ha Ω y k
    rwa [hcl] at this
  have hainv : 0 < a⁻¹ := inv_pos.2 ha
  have hcl' : cellLen 1 a⁻¹ = D := by
    unfold cellLen
    rw [Real.sqrt_inv, hsa, one_div, inv_inv]
  have hqmp := qmp_cell_smul (c := 1) hainv
  rw [hcl'] at hqmp
  have h2 := hqmp.ae h1
  have hne : ((a ^ ((3 : ℝ) / 2) : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast (Real.rpow_pos_of_pos ha _).ne'
  have hss : Real.sqrt a * Real.sqrt a⁻¹ = 1 := by
    rw [← Real.sqrt_mul ha.le, mul_inv_cancel₀ ha.ne', Real.sqrt_one]
  filter_upwards [h2] with x hx k
  have hx' := hx k
  rw [hK] at hx'
  have hpt : (Real.sqrt a * (Real.sqrt a⁻¹ • x).1, Real.sqrt a * (Real.sqrt a⁻¹ • x).2) = x := by
    ext <;> simp only [Prod.smul_fst, Prod.smul_snd, smul_eq_mul, ← mul_assoc, hss, one_mul]
  simp only [hpt] at hx'
  exact mul_left_cancel₀ hne hx'

end UnforcedLeray.Short.IIIa.ComplFreeRateSub.Leaf2WeakEqFrame.KerBSAux
