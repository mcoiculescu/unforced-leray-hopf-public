import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_asrc_kflat_1_2

/-!
# `PartIII-b:C/asrc/kflat/1/2/1` : the late-age formula for `ξ_B`

Source of record: `the November 2 reference manuscript`, the Duhamel state of 4610
with the cocycle 4385-4390.  If `B` vanishes above `T` (`χ_f = 0` there, 4757-4758), then for
`u ≥ T`, `ξ_B(u) = u^{-μ} ∫_0^T t^μ 𝒰(u,t) g_B(t) dt = u^{-μ}T^μ 𝒰(u,T) ξ_B(T)`.

Proof: the integral over `(0,u]` reduces to `(0,T]` (`g_B = 0` above `T`), the cocycle
`𝒰(u,t) = 𝒰(u,T)𝒰(T,t)` on `0 < t ≤ T ≤ u` pulls `𝒰(u,T)` out, and `ξ_B(T)` is recovered from
its own integral.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter UnforcedLeray.Axi

namespace UnforcedLeray.Short.PartIIIb.Concrete

open FlatSettingInst

theorem xiDLate (m : ℝ) [Fact (1 < m)] : XiDLateProp m := by
  intro κ ν μ hν tr FI B T u
  have : Fact (0 < cOf ν) := ⟨UnforcedLeray.Short.PartIIIb.Concrete.cOf_pos hν⟩
  intro hT hTu hB hI
  -- `g_B` vanishes above the age `T`
  have hgz : ∀ t, T < t → gBD FI B t = 0 := by
    intro t ht
    rw [gBD_apply, hB t ht]
    simp [Bd, Be, ConcreteYF.Bbeta]
  -- the integral over `(0,u]` is the integral over `(0,T]`
  have hsplit : ∫ t in Ioc 0 u, ((t : ℂ) ^ (μ : ℂ)) • (FI.ev.U u t) (gBD FI B t)
      = ∫ t in Ioc 0 T, ((t : ℂ) ^ (μ : ℂ)) • (FI.ev.U u t) (gBD FI B t) := by
    apply setIntegral_eq_of_subset_of_forall_sdiff_eq_zero measurableSet_Ioc
    · exact Ioc_subset_Ioc_right hTu
    · intro t ht
      have hTt : T < t := by
        by_contra h
        exact ht.2 ⟨ht.1.1, not_lt.1 h⟩
      rw [hgz t hTt, map_zero, smul_zero]
  -- on `(0,T]` the integrand is the cocycle-transported integrand of `DuhIntegrand`
  have hcongr : ∫ t in Ioc 0 T, ((t : ℂ) ^ (μ : ℂ)) • (FI.ev.U u t) (gBD FI B t)
      = ∫ t in Ioc 0 T, FI.ev.U u T (DuhIntegrand FI μ B T t) := by
    apply setIntegral_congr_fun measurableSet_Ioc
    intro t ht
    have ht0 : 0 ≤ t := ht.1.le
    have htT : t ≤ T := ht.2
    have hc := FI.ev.cocycle u T t ht0 htT hTu
    show ((t : ℂ) ^ (μ : ℂ)) • (FI.ev.U u t) (gBD FI B t)
      = FI.ev.U u T (((t : ℂ) ^ (μ : ℂ)) • (FI.ev.U T t) (gBD FI B t))
    rw [map_smul]
    congr 1
    rw [← ContinuousLinearMap.comp_apply, hc]
  -- the Duhamel integral of age `T`, in terms of `ξ_B(T)`
  have hpow : (T : ℂ) ^ (μ : ℂ) * (T : ℂ) ^ (-(μ : ℂ)) = 1 := by
    have hT0 : (T : ℂ) ≠ 0 := by exact_mod_cast hT.ne'
    rw [Complex.cpow_neg, mul_inv_cancel₀]
    exact Complex.cpow_ne_zero_iff.2 (Or.inl hT0)
  have hxT : ∫ t in Ioc 0 T, DuhIntegrand FI μ B T t = (T : ℂ) ^ (μ : ℂ) • xiD FI (μ : ℂ) B T := by
    show ∫ t in Ioc 0 T, ((t : ℂ) ^ (μ : ℂ)) • (FI.ev.U T t) (gBD FI B t)
      = (T : ℂ) ^ (μ : ℂ) • xiD FI (μ : ℂ) B T
    rw [xiD_apply, smul_smul, hpow, one_smul]
  -- assemble
  rw [xiD_apply FI (μ : ℂ) B u, hsplit, hcongr,
    ContinuousLinearMap.integral_comp_comm (FI.ev.U u T) (φ := DuhIntegrand FI μ B T) hI,
    hxT, map_smul, smul_smul]

end UnforcedLeray.Short.PartIIIb.Concrete
