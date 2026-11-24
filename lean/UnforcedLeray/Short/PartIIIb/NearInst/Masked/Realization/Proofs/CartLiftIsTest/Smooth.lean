import UnforcedLeray.Short.PartIIIb.NearInst.Masked.Realization.Proofs.CartLiftIsTest.Basic

/-!
# Smoothness of `cartLift` (helpers for `CartLiftIsTest`)

Off the axis (`hRad z ≠ 0`), `cartLift` equals the smooth expression
`cylFrame z * (s • nsSym (m p)) * (cylFrame z)ᵀ` at the unreduced chart point `p = clUnred`;
near the axis it vanishes identically, since `s = R²/ϱ²` exceeds the band `s₁` there.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory UnforcedLeray.Axi Set Filter Topology
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.PartIIIb.NearInst.Masked.Realization

open UnforcedLeray.Short.PartIIIb.Concrete UnforcedLeray.Short.PartIIIb.NearInst

theorem cs_re_smooth (m : Chart → Ten3) (hm : ContDiff ℝ ∞ fun p => tv4 (m p)) (k : Fin 4) :
    ContDiff ℝ ∞ fun p => (tv4 (m p) k).re :=
  Complex.reCLM.contDiff.comp ((contDiff_piLp_apply (𝕜 := ℝ) (i := k) (p := 2)).comp hm)

/-- Every entry of `nsSym ∘ m` is smooth, since it is a real part of a `tv4` coordinate or zero. -/
theorem cs_nsSym_entry (m : Chart → Ten3) (hm : ContDiff ℝ ∞ fun p => tv4 (m p)) (i j : Fin 3) :
    ContDiff ℝ ∞ fun p => nsSym (m p) i j := by
  have hT00 : ∀ T : Ten3, nsSym T 0 0 = (tv4 T 0).re := fun T => by simp [nsSym, tv4]
  have hT02 : ∀ T : Ten3, nsSym T 0 2 = (tv4 T 1).re := fun T => by simp [nsSym, tv4, symRZ]
  have hT20 : ∀ T : Ten3, nsSym T 2 0 = (tv4 T 1).re := fun T => by simp [nsSym, tv4, symRZ]
  have hT11 : ∀ T : Ten3, nsSym T 1 1 = (tv4 T 3).re := fun T => by simp [nsSym, tv4]
  have hT22 : ∀ T : Ten3, nsSym T 2 2 = (tv4 T 2).re := fun T => by simp [nsSym, tv4]
  have hT01 : ∀ T : Ten3, nsSym T 0 1 = 0 := fun T => by simp [nsSym]
  have hT10 : ∀ T : Ten3, nsSym T 1 0 = 0 := fun T => by simp [nsSym]
  have hT12 : ∀ T : Ten3, nsSym T 1 2 = 0 := fun T => by simp [nsSym]
  have hT21 : ∀ T : Ten3, nsSym T 2 1 = 0 := fun T => by simp [nsSym]
  fin_cases i <;> fin_cases j <;>
    simp [hT00, hT01, hT02, hT10, hT11, hT12, hT20, hT21, hT22]
  all_goals first
    | exact cs_re_smooth m hm _
    | exact contDiff_const

theorem cs_coord_smooth (k : Fin 3) : ContDiff ℝ ∞ fun y : Space × ℝ => y.1 k :=
  (contDiff_piLp_apply (𝕜 := ℝ) (i := k) (p := 2)).comp contDiff_fst

theorem cs_rho2_smooth : ContDiff ℝ ∞ fun y : Space × ℝ => y.1 0 ^ 2 + y.1 1 ^ 2 :=
  ((cs_coord_smooth 0).pow 2).add ((cs_coord_smooth 1).pow 2)

theorem cs_hRad_contDiffAt (y0 : Space × ℝ) (h : hRad y0.1 ≠ 0) :
    ContDiffAt ℝ ∞ (fun y : Space × ℝ => hRad y.1) y0 := by
  have hpos : 0 < y0.1 0 ^ 2 + y0.1 1 ^ 2 := by
    have := lt_of_le_of_ne (Real.sqrt_nonneg (y0.1 0 ^ 2 + y0.1 1 ^ 2)) (Ne.symm h)
    exact Real.sqrt_pos.1 this
  exact cs_rho2_smooth.contDiffAt.sqrt hpos.ne'

theorem cs_clUnred_contDiffAt (ε : ℝ) (hε : 0 < ε) (y0 : Space × ℝ) (h : hRad y0.1 ≠ 0) :
    ContDiffAt ℝ ∞ (fun y : Space × ℝ => clUnred ε⁻¹ y.2 y.1) y0 := by
  have hr := cs_hRad_contDiffAt y0 h
  have c1 : ContDiffAt ℝ ∞ (fun y : Space × ℝ => ε⁻¹ ^ 2 / hRad y.1 ^ 2) y0 :=
    contDiffAt_const.div (hr.pow 2) (pow_ne_zero 2 h)
  have hl : ContDiffAt ℝ ∞ (fun y : Space × ℝ => Real.log (hRad y.1 / ε⁻¹)) y0 :=
    (hr.div_const ε⁻¹).log (div_ne_zero h (inv_ne_zero hε.ne'))
  have c2 : ContDiffAt ℝ ∞
      (fun y : Space × ℝ => ε⁻¹ * Real.log (hRad y.1 / ε⁻¹) + ε⁻¹ * y.2 / 2) y0 :=
    (contDiffAt_const.mul hl).add ((contDiffAt_const.mul contDiffAt_snd).div_const 2)
  have c3 : ContDiffAt ℝ ∞ (fun y : Space × ℝ => ε⁻¹ * y.1 2 / hRad y.1) y0 :=
    (contDiffAt_const.mul (cs_coord_smooth 2).contDiffAt).div hr h
  exact c1.prodMk (c2.prodMk c3)

theorem cs_cylFrame_entry (y0 : Space × ℝ) (h : hRad y0.1 ≠ 0) (i j : Fin 3) :
    ContDiffAt ℝ ∞ (fun y : Space × ℝ => cylFrame y.1 i j) y0 := by
  have hr := cs_hRad_contDiffAt y0 h
  have d0 : ContDiffAt ℝ ∞ (fun y : Space × ℝ => y.1 0 / hRad y.1) y0 :=
    (cs_coord_smooth 0).contDiffAt.div hr h
  have d1 : ContDiffAt ℝ ∞ (fun y : Space × ℝ => y.1 1 / hRad y.1) y0 :=
    (cs_coord_smooth 1).contDiffAt.div hr h
  fin_cases i <;> fin_cases j <;> simp [cylFrame]
  all_goals first
    | exact contDiffAt_const
    | exact d0
    | exact d1
    | exact d0.neg
    | exact d1.neg

theorem cs_matmul_entry (y0 : Space × ℝ) (Q N : Space × ℝ → Matrix (Fin 3) (Fin 3) ℝ)
    (s : Space × ℝ → ℝ) (hQ : ∀ i j, ContDiffAt ℝ ∞ (fun y => Q y i j) y0)
    (hN : ∀ i j, ContDiffAt ℝ ∞ (fun y => N y i j) y0) (hs : ContDiffAt ℝ ∞ s y0)
    (i j : Fin 3) :
    ContDiffAt ℝ ∞ (fun y => (Q y * (s y • N y) * (Q y).transpose) i j) y0 := by
  simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.smul_apply, smul_eq_mul]
  refine ContDiffAt.sum fun k _ => ?_
  refine ContDiffAt.mul (ContDiffAt.sum fun l _ => ?_) (hQ j k)
  exact (hQ i l).mul (hs.mul (hN l k))

/-- The formula for `cartLift` at the unreduced chart point. -/
theorem cs_cartLift_eq (ε c : ℝ) (m : Chart → Ten3)
    (hm : UnforcedLeray.B0220.QPeriodic c (fun p => tv4 (m p))) (y : Space × ℝ) :
    cartLift ε⁻¹ c m y.2 y.1 =
      cylFrame y.1 * ((clUnred ε⁻¹ y.2 y.1).1 • nsSym (m (clUnred ε⁻¹ y.2 y.1))) *
        (cylFrame y.1).transpose := by
  unfold cartLift
  rw [cl_nsSym_chartOf m ε⁻¹ c hm y.1 y.2]
  rfl

/-- `cartLift` vanishes on the open set `s₁ ϱ² < R²`, which contains the axis. -/
theorem cs_zero_region (ε c : ℝ) (hε : 0 < ε) (m : Chart → Ten3) (s0 s1 L : ℝ)
    (hb : ∀ p : Chart, tv4 (m p) ≠ 0 → p.1 ∈ Icc s0 s1 ∧ |p.2.2| ≤ L)
    (y : Space × ℝ) (hy : s1 * hRad y.1 ^ 2 < ε⁻¹ ^ 2) : cartLift ε⁻¹ c m y.2 y.1 = 0 := by
  unfold cartLift
  rcases eq_or_ne (hRad y.1) 0 with h0 | h0
  · have hs : (chartOf ε⁻¹ c y.1 y.2).1 = 0 := by
      unfold chartOf
      rw [h0]
      simp
    rw [hs, zero_smul, Matrix.mul_zero, Matrix.zero_mul]
  · have hs1 : s1 < (chartOf ε⁻¹ c y.1 y.2).1 := by
      show s1 < ε⁻¹ ^ 2 / hRad y.1 ^ 2
      rw [lt_div_iff₀ (by positivity)]
      exact hy
    have hN : tv4 (m (chartOf ε⁻¹ c y.1 y.2)) = 0 := by
      by_contra hne
      have := (hb _ hne).1.2
      linarith
    have hN' : nsSym (m (chartOf ε⁻¹ c y.1 y.2)) = 0 := by
      rw [cl_nsSym_of_tv4_eq (hN.trans cl_tv4_zero.symm), cl_nsSym_zero]
    rw [hN', smul_zero, Matrix.mul_zero, Matrix.zero_mul]

/-- **Smoothness of `cartLift`** (source 1639-1650, 2666-2668). -/
theorem cs_smooth (ε c : ℝ) (hε : 0 < ε) (m : Chart → Ten3)
    (hm : UnforcedLeray.Short.PartIIa.IsTensorTest c (fun p => tv4 (m p))) (i j : Fin 3) :
    ContDiff ℝ ∞ fun y : Space × ℝ => cartLift ε⁻¹ c m y.2 y.1 i j := by
  obtain ⟨s0, s1, L, hs0, hb⟩ := hm.band
  rw [contDiff_iff_contDiffAt]
  intro y0
  by_cases h0 : hRad y0.1 = 0
  · have hopen : IsOpen {y : Space × ℝ | s1 * hRad y.1 ^ 2 < ε⁻¹ ^ 2} := by
      apply isOpen_lt
      · unfold hRad
        fun_prop
      · exact continuous_const
    have hy0 : y0 ∈ {y : Space × ℝ | s1 * hRad y.1 ^ 2 < ε⁻¹ ^ 2} := by
      show s1 * hRad y0.1 ^ 2 < ε⁻¹ ^ 2
      rw [h0]
      have : 0 < ε⁻¹ ^ 2 := by positivity
      simpa using this
    have hev : (fun y : Space × ℝ => cartLift ε⁻¹ c m y.2 y.1 i j) =ᶠ[𝓝 y0]
        fun _ => (0 : ℝ) := by
      filter_upwards [hopen.mem_nhds hy0] with y hy
      rw [cs_zero_region ε c hε m s0 s1 L hb y hy]
      simp
    exact contDiffAt_const.congr_of_eventuallyEq hev
  · have hfun : (fun y : Space × ℝ => cartLift ε⁻¹ c m y.2 y.1 i j) =
        fun y => (cylFrame y.1 * ((clUnred ε⁻¹ y.2 y.1).1 • nsSym (m (clUnred ε⁻¹ y.2 y.1))) *
          (cylFrame y.1).transpose) i j := by
      funext y
      rw [cs_cartLift_eq ε c m hm.periodic y]
    rw [hfun]
    have hcl := cs_clUnred_contDiffAt ε hε y0 h0
    exact cs_matmul_entry y0 (fun y => cylFrame y.1)
      (fun y => nsSym (m (clUnred ε⁻¹ y.2 y.1)))
      (fun y => (clUnred ε⁻¹ y.2 y.1).1)
      (fun i j => cs_cylFrame_entry y0 h0 i j)
      (fun i j => ContDiffAt.comp y0 (cs_nsSym_entry m hm.smooth i j).contDiffAt hcl)
      hcl.fst i j

end UnforcedLeray.Short.PartIIIb.NearInst.Masked.Realization
