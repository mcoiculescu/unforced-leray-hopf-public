import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_rep_4_4_1_org_1_2
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_4.YRepStream.ShiftedResolventRep

/-!
# `PartIII-b:C/rep/4/4/1/org/1/2/3`: `sepNegSolenoidal`, decomposed

Source `the November 2 reference manuscript`
3604-3621 (`sep:kernel`, `sep:resolvent`: `W_μ = -S_μ T`, the heat-Leray kernel `K_t` has
`∂_i K_ij = 0` including its local distributional part), 4163-4174.

* `srRep_sepT`: the separated representative `T` of the old repair source `g₁ + g₂`
  (`repairSepBridge`, as in `srRep_core`), proved here;
* `SepWWeakSolenoidal`: for every separated source `T` of finite moment, `-W_μ(T)` is weakly
  solenoidal on `ℝ × ℝ³` (Fubini of the kernel integral against `∇φ`; the kernel is divergence
  free as a distribution), left as a lemma.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter UnforcedLeray.Axi
open scoped ENNReal
open UnforcedLeray.Blueprint.Planar (PlanarData)

namespace UnforcedLeray.Short.PartIIIb.Concrete

open UnforcedLeray.PhaseSpace UnforcedLeray.B0411
open UnforcedLeray.Cons.C03.Concrete (pairF phaseInt IsSolTest)

/-- The separated representative of the old repair source (as in `srRep_core`). -/
theorem srRep_sepT (Pl : PlanarData) (K : ReturnConsts) (L : ReturnLevel)
    (hC0 : 0 < K.C0) (hmZ : 0 ≤ K.mZ) (w : LVel Pl L)
    {g₁ g₂ : Chart → Ten3} (hg : IsRep Pl K L (oldRep Pl K L w) g₁ g₂) :
    ∃ T : ℝ → Space → Matrix (Fin 3) (Fin 3) ℝ,
      IIIa.IsSepSource (2 * L.ε * cOf L.ν) (L.ε⁻¹ * Real.sqrt (5 * L.ν / 6)) T ∧
      SepMoment (2 * L.ε * cOf L.ν) T ∧
      ∀ (μ' : ℂ) (τ : ℝ) (y : Space),
        IIIa.sepW L.ν μ' (oldPhys L.ε⁻¹ (cOf L.ν) (g₁ + g₂)) y τ = IIIa.sepW L.ν μ' T y τ := by
  have hν : 0 < L.ν := L.ν_pos
  have hε : 0 < L.ε := L.ε_pos
  have hR : 0 < L.ε⁻¹ := inv_pos.2 hε
  have hc : 0 < cOf L.ν := cOf_pos hν
  have hρ : 0 < L.ρb Pl K := by
    show 0 < UnforcedLeray.Short.IIb.rhoB (L.params Pl) K.m0 K.C0 K.k0
    unfold UnforcedLeray.Short.IIb.rhoB
    have h1 : 0 < ((L.params Pl).ν ^ K.k0)⁻¹ := inv_pos.2 (pow_pos (L.params Pl).ν_pos _)
    have h2 : 0 < (L.params Pl).ε ^ (3 / 11 : ℝ) := Real.rpow_pos_of_pos (L.params Pl).ε_pos _
    have h3 : 0 < Real.exp (K.m0 / (L.params Pl).ν) := Real.exp_pos _
    exact mul_pos (mul_pos (mul_pos hC0 h1) h3) h2
  obtain ⟨T, hT1, hT2, -, hresp, -⟩ :=
    repairSepBridge (cOf L.ν) K.mZ (L.ρb Pl K) (gRate Pl) L.ν L.ε K.χo K.hχo hc hρ hmZ hν hε
      (repPart (multOp Pl K L w))
  have hM0 : ((repPart (multOp Pl K L w)).fst : Chart → Ten3) =ᵐ[gainZ1Measure (cOf L.ν) K.mZ (gRate Pl) L.ν]
      (0 : Chart → Ten3) := by
    rw [repPart_fst_zero']
    exact Lp.coeFn_zero _ _ _
  have a1 := (chiOStrApply (cOf L.ν) K.mZ (L.ρb Pl K) (gRate Pl) L.ν K.χo K.hχo
    (repPart (multOp Pl K L w))).1
  have hfst : ((chiOStr (cOf L.ν) K.mZ (L.ρb Pl K) (gRate Pl) L.ν K.hχo
      (repPart (multOp Pl K L w))).fst : Chart → Ten3) =ᵐ[gainZ1Measure (cOf L.ν) K.mZ (gRate Pl) L.ν]
      (0 : Chart → Ten3) := by
    filter_upwards [a1, hM0] with p e1 e2
    rw [e1, e2]
    simp
  rw [NearInst.ae_gainZ1Measure, NearInst.ae_z1Measure] at hfst
  have hae := wo_rep_ae hρ K.hχo (repPart (multOp Pl K L w)) hg.1 hg.2
  have hsum : g₁ + g₂ =ᵐ[ageμ (cOf L.ν) (-1 / 2)]
      ((chiOStr (cOf L.ν) K.mZ (L.ρb Pl K) (gRate Pl) L.ν K.hχo
        (repPart (multOp Pl K L w))).snd : Chart → Ten3) := by
    filter_upwards [hae, hfst] with p h1 h2
    rw [h1]
    simp [strSum, h2]
  have hnull := ae_iff.1 hsum
  obtain ⟨N, hsub, hNm, hN0⟩ := exists_measurable_superset_of_null hnull
  refine ⟨T, hT1, hT2, fun μ' τ y => ?_⟩
  rw [WardX0Congr.sepW_congr L.ν μ' hR hc (g₁ + g₂) _ N hNm hN0 hsub τ y]
  exact hresp μ' y τ

/-- **`W_μ` is weakly solenoidal** (source 3604-3621: `W_μ = -2∫ λ^{2μ+2} ∫ ∇K_{ν(1-λ²)}(y-λz) :
T dz dλ` with the divergence-free heat-Leray kernel `K_t`, `∂_i K_ij = 0` also across the origin;
Fubini against `∇φ` for the finite moment `SepMoment` of the separated source). -/
def SepWWeakSolenoidal : Prop :=
  ∀ (ν μ rOut P : ℝ) (T : ℝ → Space → Matrix (Fin 3) (Fin 3) ℝ),
    0 < ν → -(1 / 4) < μ → 0 ≤ rOut → 0 < P → IIIa.IsSepSource P rOut T → SepMoment P T →
    IsWeakSolenoidal P (fun x => UnforcedLeray.B0412.realC (-(sepWre ν μ T x.1 x.2)))

variable {Pl : PlanarData} {K : ReturnConsts} {L : ReturnLevel} {μ : ℝ}

theorem sepNegSolenoidalAt_of (hW : SepWWeakSolenoidal) (hC0 : 0 < K.C0) (hmZ : 0 ≤ K.mZ)
    (hμ : -(1 / 4) < μ) : SepNegSolenoidalAt Pl K L μ := by
  intro w g₁ g₂ hg
  obtain ⟨T, hT1, hT2, hsep⟩ := srRep_sepT Pl K L hC0 hmZ w hg
  have hW' : ∀ τ y, wardW L.ν μ L.ε⁻¹ (cOf L.ν) (g₁ + g₂) τ y = sepWre L.ν μ T τ y := by
    intro τ y
    simp only [wardW, sepWre, hsep]
  have hε := L.ε_pos
  have hc := cOf_pos L.ν_pos
  have h := hW L.ν μ _ _ T L.ν_pos hμ (mul_nonneg (inv_pos.2 hε).le (Real.sqrt_nonneg _))
    (by positivity) hT1 hT2
  have e : negW L μ (g₁ + g₂) =
      fun x => UnforcedLeray.B0412.realC (-(sepWre L.ν μ T x.1 x.2)) := by
    funext x; simp only [negW, hW']
  rw [e]
  exact h

/-- `sepNegSolenoidal` from `SepWWeakSolenoidal`. -/
theorem sepNegSolenoidal_of (dm dp : ℝ) (hW : SepWWeakSolenoidal) : SepNegSolenoidal dm dp := by
  intro D hst
  filter_upwards [muWin_gt_quarter D hst] with n hn z hz
  exact sepNegSolenoidalAt_of hW hst.C0_pos (by linarith [hst.mZ_gt]) (hn z hz)

end UnforcedLeray.Short.PartIIIb.Concrete
end
