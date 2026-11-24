import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_asrc_kflat_1
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnInst.AffineSource.TrainGrowth
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnInst.EACoefBound.Support

/-!
# `PartIII-b:C/asrc/kflat/1/2` : decomposition of `FrakTIntProp`

Source of record: `the November 2 reference manuscript`.

Integrability of `u^{-3/2}|𝔗A|` on the old region `u > 1.2/ν` (source 4637-4640 with `k = 0`, proof
4677-4694).  With `T = 1.1/ν`, `B = B_{μ,ν}[A]` vanishes above `T` (`χ_f = 0` there, 4757-4758;
`eac_bmat_zero`), so by the cocycle `𝒰(u,t) = 𝒰(u,T)𝒰(T,t)` the Duhamel state of 4610 is
`ξ_B(u) = (T/u)^μ 𝒰(u,T) ξ_B(T)` for `u ≥ T` (`XiDLateProp`), and `K_c` is real-homogeneous a.e.
(`KcMerLinearProp`).  Hence `u^{-3/2}|𝔗A(u,·)| ≤ u^{-3/2}|v ⊗ K_c𝒰(u,T)w + K_c𝒰(u,T)w ⊗ v|` a.e. on
each old slice, `w = ξ_B(T)`, and `TrainOldStressBound` (`TrainGrowth.lean`) bounds the integral of
the right side.  Measurability is `FrakTMeasProp` (`kflat/1/1`), the integrability of the Duhamel
integrand on `(0,T]` is `DuhIntegrableProp` (`kflat/2/1`).

* `XiDLateProp` : the late-age formula for `ξ_B` (leaf `kflat/1/2/1`);
* `frakTIntProp_of` : `FrakTIntProp` from the leaves (proved here).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter UnforcedLeray.Axi

namespace UnforcedLeray.Short.PartIIIb.Concrete

open FlatSettingInst

/-- **Late-age formula for the Duhamel state** (source 4610 with the cocycle 4385-4390): if `B`
vanishes above `T > 0` and the Duhamel integrand of age `T` is integrable on `(0,T]`, then for
`u ≥ T`, `ξ_B(u) = u^{-μ}T^μ 𝒰(u,T) ξ_B(T)`. -/
def XiDLateProp (m : ℝ) [Fact (1 < m)] : Prop :=
  ∀ (κ : UnforcedLeray.Short.IIIa.PlanarFrameKernels) (ν μ : ℝ) (hν : 0 < ν)
    (tr : UnforcedLeray.B0140.TrainSol ν (cOf ν)) (FI : FlatInstData κ ν (cOf ν) m tr)
    (B : ℝ → Matrix (Fin 3) (Fin 3) ℝ) (T u : ℝ),
    haveI : Fact (0 < cOf ν) := ⟨UnforcedLeray.Short.PartIIIb.Concrete.cOf_pos hν⟩
    0 < T → T ≤ u → (∀ t, T < t → B t = 0) →
    IntegrableOn (DuhIntegrand FI μ B T) (Ioc 0 T) →
      xiD FI (μ : ℂ) B u =
        ((u : ℂ) ^ (-(μ : ℂ)) * (T : ℂ) ^ (μ : ℂ)) • FI.ev.U u T (xiD FI (μ : ℂ) B T)

theorem kfl12_continuous_frob : Continuous frob := by
  unfold frob
  exact Real.continuous_sqrt.comp (continuous_finset_sum _ fun i _ =>
    continuous_finset_sum _ fun j _ => ((continuous_apply j).comp (continuous_apply i)).pow 2)

theorem kfl12_frob_smul_le {ρ : ℝ} (h0 : 0 ≤ ρ) (h1 : ρ ≤ 1) (M : Mat3) :
    frob (ρ • M) ≤ frob M := by
  unfold frob
  apply Real.sqrt_le_sqrt
  apply Finset.sum_le_sum
  intro i _
  apply Finset.sum_le_sum
  intro j _
  have e : (ρ • M) i j = ρ * M i j := rfl
  rw [e, mul_pow]
  have hρ2 : ρ ^ 2 ≤ 1 := by nlinarith
  exact mul_le_of_le_one_left (sq_nonneg _) hρ2

/-- **`FrakTIntProp` from the leaves.** -/
theorem frakTIntProp_of (as : ℝ) (χf : ℝ → ℝ) (m : ℝ) [Fact (1 < m)]
    (hM : FrakTMeasProp as χf m) (hD : DuhIntegrableProp as χf m) (hK : KcMerLinearProp m)
    (hX : XiDLateProp m) (hS : TrainOldStressBound m) : FrakTIntProp as χf m := by
  intro hχ hm
  obtain ⟨ν₀, hν₀, hS'⟩ := hS hm
  refine ⟨min ν₀ 1, lt_min hν₀ one_pos, ?_⟩
  intro κ ν μ ε χo hν hνs hμ0 hμ1 tr htr FI A hA
  have hν1 : ν ≤ 1 := hνs.trans (min_le_right _ _)
  have hν0 : ν ≤ ν₀ := hνs.trans (min_le_left _ _)
  have hc : Fact (0 < cOf ν) := ⟨UnforcedLeray.Short.PartIIIb.Concrete.cOf_pos hν⟩
  have : SFinite (UnforcedLeray.Cyl.avgμ (cOf ν)) := by
    unfold UnforcedLeray.Cyl.avgμ; infer_instance
  obtain ⟨C, hC⟩ := hS' κ ν hν hν0 tr htr FI
  set T : ℝ := 11 / 10 / ν with hT
  set B := Bmat ν μ χf A with hBdef
  set w := xiD FI (μ : ℂ) B T with hw
  have hTpos : 0 < T := by positivity
  have hTold : T < 6 / 5 / ν := div_lt_div_of_pos_right (by norm_num) hν
  have hBz : ∀ t, T < t → B t = 0 := fun t ht => (eac_bmat_zero χf hχ ν μ hν A t ht).1
  have hIT := hD hχ κ ν μ hν hν1 hμ0 hμ1 tr FI A hA T
  have hlate : ∀ u, T ≤ u → xiD FI (μ : ℂ) B u =
      ((u : ℂ) ^ (-(μ : ℂ)) * (T : ℂ) ^ (μ : ℂ)) • FI.ev.U u T w :=
    fun u hu => hX κ ν μ hν tr FI B T u hTpos hu hBz hIT
  have hmeas := hM hχ κ ν μ ε χo hν hν1 hμ0 hμ1 tr FI A hA
  -- the slice comparison on the old region
  have hslice : ∀ u ∈ Ioi (6 / 5 / ν),
      ∫⁻ x, ‖u ^ (-(3 / 2 : ℝ)) * frob (frakT (levelFlat hν FI χo ε) ν μ χf A (u, x))‖ₑ
          ∂(UnforcedLeray.Cyl.avgμ (cOf ν)) ≤
        ∫⁻ x, ENNReal.ofReal (u ^ (-(3 / 2 : ℝ)) *
          frob (UnforcedLeray.Short.IIIa.symOuter (NearInst.trainMer tr (u, x))
            (kcMer (FI.ev.U u (11 / 10 / ν) w) x))) ∂(UnforcedLeray.Cyl.avgμ (cOf ν)) := by
    intro u hu
    have hu0 : 0 < u := lt_trans (by positivity) (Set.mem_Ioi.1 hu)
    have hTu : T ≤ u := (hTold.trans (Set.mem_Ioi.1 hu)).le
    set ρ : ℝ := u ^ (-μ) * T ^ μ with hρdef
    have hρ : (u : ℂ) ^ (-(μ : ℂ)) * (T : ℂ) ^ (μ : ℂ) = ((ρ : ℝ) : ℂ) := by
      rw [hρdef, Complex.ofReal_mul, Complex.ofReal_cpow hu0.le, Complex.ofReal_cpow hTpos.le,
        Complex.ofReal_neg]
    have hρ0 : 0 ≤ ρ := mul_nonneg (Real.rpow_nonneg hu0.le _) (Real.rpow_nonneg hTpos.le _)
    have hρ1 : ρ ≤ 1 := by
      rw [hρdef, Real.rpow_neg hu0.le, inv_mul_le_iff₀ (Real.rpow_pos_of_pos hu0 _), mul_one]
      exact Real.rpow_le_rpow hTpos.le hTu hμ0
    have hxi : xiD FI (μ : ℂ) B u = ((ρ : ℝ) : ℂ) • FI.ev.U u T w := by
      rw [hlate u hTu, hρ]
    refine lintegral_mono_ae ?_
    filter_upwards [(hK ν hν (FI.ev.U u T w) (FI.ev.U u T w) ρ).2] with x hx
    have hx' : kcMer (((ρ : ℝ) : ℂ) • FI.ev.U u T w) x = ρ • kcMer (FI.ev.U u T w) x := hx
    have e1 : frakT (levelFlat hν FI χo ε) ν μ χf A (u, x) =
        UnforcedLeray.Short.IIIa.symOuter (NearInst.trainMer tr (u, x))
          (kcMer (xiD FI (μ : ℂ) (Bmat ν μ χf A) u) x) := rfl
    rw [e1, ← hBdef, hxi, hx', symOuter_smul_right']
    have hpow : 0 < u ^ (-(3 / 2 : ℝ)) := Real.rpow_pos_of_pos hu0 _
    have hfr : 0 ≤ frob (ρ • UnforcedLeray.Short.IIIa.symOuter (NearInst.trainMer tr (u, x))
        (kcMer (FI.ev.U u T w) x)) := Real.sqrt_nonneg _
    rw [Real.enorm_eq_ofReal (mul_nonneg hpow.le hfr)]
    exact ENNReal.ofReal_le_ofReal
      (mul_le_mul_of_nonneg_left (kfl12_frob_smul_le hρ0 hρ1 _) hpow.le)
  refine ⟨?_, ?_⟩
  · exact ((measurable_fst.pow_const _).aestronglyMeasurable).mul
      (kfl12_continuous_frob.comp_aestronglyMeasurable hmeas)
  · show ∫⁻ p, ‖p.1 ^ (-(3 / 2 : ℝ)) * frob (frakT (levelFlat hν FI χo ε) ν μ χf A p)‖ₑ
        ∂(oldMeasure (cOf ν) ν) < ⊤
    calc ∫⁻ p, ‖p.1 ^ (-(3 / 2 : ℝ)) * frob (frakT (levelFlat hν FI χo ε) ν μ χf A p)‖ₑ
          ∂(oldMeasure (cOf ν) ν)
        ≤ ∫⁻ u in Ioi (6 / 5 / ν),
            ∫⁻ x, ‖u ^ (-(3 / 2 : ℝ)) * frob (frakT (levelFlat hν FI χo ε) ν μ χf A (u, x))‖ₑ
              ∂(UnforcedLeray.Cyl.avgμ (cOf ν)) := lintegral_prod_le _
      _ ≤ ∫⁻ u in Ioi (6 / 5 / ν), ∫⁻ x, ENNReal.ofReal (u ^ (-(3 / 2 : ℝ)) *
            frob (UnforcedLeray.Short.IIIa.symOuter (NearInst.trainMer tr (u, x))
              (kcMer (FI.ev.U u (11 / 10 / ν) w) x))) ∂(UnforcedLeray.Cyl.avgμ (cOf ν)) :=
          setLIntegral_mono' measurableSet_Ioi hslice
      _ ≤ ENNReal.ofReal (C * ‖w‖) := hC w
      _ < ⊤ := ENNReal.ofReal_lt_top

end UnforcedLeray.Short.PartIIIb.Concrete
