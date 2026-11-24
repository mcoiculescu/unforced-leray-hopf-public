import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_IIIb_D5_2

/-!
# `PartIII-b:IIIb-D5/2/2` decomposition: `WeakDmuToPeriodicModeEq` from two leaves

Source `the November 2 reference manuscript` 167-182,
4145-4147, 5975-5985.  `IsWeakDmu` tests only solenoidal phase tests `Φ` (`IsSolTest`); the mode
equation tests all periodic `φ` against `ℙ div`.  The bridge is a Helmholtz approximation
(`PartIIa.wsuPressureApprox`, `PartIIa.pressure_kills_gradient`, `Cons.C08.lerayDivIntegral_eq_bodyForce`,
`IIb.lerayPairSol`): solenoidal tests `ψ_k` with the same left-hand side in the limit and with
stress pairing converging to `P⁻¹ ∫ projectedCoupling`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology UnforcedLeray.Axi
open UnforcedLeray.PhaseSpace UnforcedLeray.B0411
open UnforcedLeray.Blueprint.Planar (PlanarData)
open UnforcedLeray UnforcedLeray.Blueprint UnforcedLeray.Cons.C08

namespace UnforcedLeray.Short.PartIIIb.Concrete
namespace Wiring.ModeAux

/-- Leaf 1 (Helmholtz approximation, source 5975-5985): for a periodic test `φ` there are
solenoidal phase tests `ψ_k` with `⟨(L₀ᵗ+μ)ψ_k, w⟩ → ⟨(L₀ᵗ+μ)φ, w⟩` (`w = velPhys b`) and
`stressPair(𝒩_T(M b), ψ_k) → P⁻¹ ∫_0^P projectedCoupling U b_* φ`. -/
def HelmholtzApprox : Prop :=
  ∀ (D : SeqData) (dm dp : ℝ), D.RepairStanding dm dp → ∀ n : ℕ, D.IsActualLevel dm dp n →
    ∀ z ∈ Icc (-1 : ℝ) 1, NearAt D.Pl D.K (D.level n) (D.mu n z) →
      RegimePins D.Pl D.K (D.level n) (D.mu n z) →
      0 < D.mu n z → D.mu n z < 1 / 4 →
      ∀ (B : ReturnBase (cOf (D.level n).ν) D.K.mZ ((D.level n).ρb D.Pl D.K)
          (gRate D.Pl) (D.level n).ν (AffSp D.K.as)),
        IsExactMultiplier B (D.level n).ε⁻¹ (D.level n).V (D.level n).rb →
      ∀ (b : LVel D.Pl (D.level n)),
        IsH1Periodic (2 * (D.level n).ε * cOf (D.level n).ν) (modeBstar (D.level n) b) →
        ∀ φ : SpaceTime → Space,
          Interface.IsPeriodicTest (2 * (D.level n).ε * cOf (D.level n).ν) φ →
          ∃ ψ : ℕ → SpaceTime → Space,
            (∀ k, UnforcedLeray.Cons.C03.Concrete.IsSolTest (2 * (D.level n).ε * cOf (D.level n).ν)
              (B0005.cplxT (ψ k))) ∧
            Tendsto (fun k => UnforcedLeray.Cons.C03.Concrete.pairF
                (2 * (D.level n).ε * cOf (D.level n).ν)
                (fun x => L0T (D.level n).ν (B0005.cplxT (ψ k)) x
                  + ((D.mu n z : ℝ) : ℂ) • B0005.cplxT (ψ k) x)
                (velPhys (D.level n).ε⁻¹ (cOf (D.level n).ν) b)) atTop
              (𝓝 (UnforcedLeray.Cons.C03.Concrete.pairF (2 * (D.level n).ε * cOf (D.level n).ν)
                (fun x => L0T (D.level n).ν (B0005.cplxT φ) x
                  + ((D.mu n z : ℝ) : ℂ) • B0005.cplxT φ x)
                (velPhys (D.level n).ε⁻¹ (cOf (D.level n).ν) b))) ∧
            Tendsto (fun k => stressPair (2 * (D.level n).ε * cOf (D.level n).ν)
                (strPhys (D.level n).ε⁻¹ (cOf (D.level n).ν) (strSum (-(B.M b))))
                (B0005.cplxT (ψ k))) atTop
              (𝓝 ((((2 * (D.level n).ε * cOf (D.level n).ν)⁻¹ *
                ∫ τ in Ioc (0 : ℝ) (2 * (D.level n).ε * cOf (D.level n).ν),
                  projectedCoupling (D.level n).U (modeBstar (D.level n) b) φ τ : ℝ)) : ℂ))

/-- Leaf 2 (integrability): for `b_*` in `IsH1Periodic` and a periodic test, the weak mode
integrand is integrable on the period slab (source 167-182). -/
def WeakModeIntegrable : Prop :=
  ∀ (L : ReturnLevel) {Pl : PlanarData} (μ : ℝ) (b : LVel Pl L),
    IsH1Periodic (2 * L.ε * cOf L.ν) (modeBstar L b) →
    ∀ φ : SpaceTime → Space, Interface.IsPeriodicTest (2 * L.ε * cOf L.ν) φ →
      Integrable (weakModeIntegrand L.ν μ (modeBstar L b) φ)
        (volume.restrict (periodSlab (2 * L.ε * cOf L.ν)))

theorem weakDmuToPeriodicModeEq_of (h1 : HelmholtzApprox) (h2 : WeakModeIntegrable) :
    WeakDmuToPeriodicModeEq := by
  intro D dm dp hst n hact z hz hne hp hμ0 hμ1 B hB b hH1 hW φ hφ
  obtain ⟨ψ, hψ, hL, hS⟩ := h1 D dm dp hst n hact z hz hne hp hμ0 hμ1 B hB b hH1 φ hφ
  have heq : ∀ k, UnforcedLeray.Cons.C03.Concrete.pairF (2 * (D.level n).ε * cOf (D.level n).ν)
      (fun x => L0T (D.level n).ν (B0005.cplxT (ψ k)) x
        + ((D.mu n z : ℝ) : ℂ) • B0005.cplxT (ψ k) x)
      (velPhys (D.level n).ε⁻¹ (cOf (D.level n).ν) b) =
      -stressPair (2 * (D.level n).ε * cOf (D.level n).ν)
        (strPhys (D.level n).ε⁻¹ (cOf (D.level n).ν) (strSum (-(B.M b))))
        (B0005.cplxT (ψ k)) := fun k => hW.equation _ (hψ k)
  have hlim := tendsto_nhds_unique (hL.congr heq) hS.neg
  have hint := h2 (D.level n) (D.mu n z) b hH1 φ hφ
  rw [pairF_L0T_cplxT_velPhys (D.level n) (D.mu n z) _ hφ.smooth hint] at hlim
  have hr := by exact_mod_cast hlim
  have hPpos : 0 < 2 * (D.level n).ε * cOf (D.level n).ν :=
    mul_pos (mul_pos two_pos (D.level n).ε_pos) (cOf_pos (D.level n).ν_pos)
  have hP := inv_pos.2 hPpos
  have : (2 * (D.level n).ε * cOf (D.level n).ν)⁻¹ *
      ((∫ w in periodSlab (2 * (D.level n).ε * cOf (D.level n).ν),
          weakModeIntegrand (D.level n).ν (D.mu n z) (modeBstar (D.level n) b) φ w) +
        ∫ τ in Ioc (0 : ℝ) (2 * (D.level n).ε * cOf (D.level n).ν),
          projectedCoupling (D.level n).U (modeBstar (D.level n) b) φ τ) = 0 := by
    rw [mul_add]; linarith
  exact (mul_eq_zero.1 this).resolve_left hP.ne'

end Wiring.ModeAux
end UnforcedLeray.Short.PartIIIb.Concrete
