import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_4.YRepStream.EarlyRepThin.Props
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_1

/-!
# Decomposition of `earlyRepThinProduct` (`PartIII-b:C/rep/4/4/1/org/7/2`)

Source `the November 2 reference manuscript` 5169-5176 (`repair:source`,
`19/22 = 4/11 + 1/2`), 5134-5139, 4163-4166 (`1-χ_o` supported in ages `≤ 1.5/ν`, values in
`[0,1]`).  This is the proof of `repairSourceAt_level` (Sub/PartIII-b_C_rep_1.lean) with `χ_o`
replaced by `1-χ_o` and the factor `e^{γ/ν} ≤ ν^{-k}|N_ν|` replaced by `Γ`.  It reuses the leaves
`RbFacts`, `HolderPhase`, `PeriodSmall` of `rep/1` and adds three early-source leaves.
`earlyRepThinProduct_of` proves the target from them.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter UnforcedLeray.Axi
open scoped ENNReal

namespace UnforcedLeray.Short.PartIIIb.Concrete

open UnforcedLeray.Blueprint.Planar (PlanarData)
open UnforcedLeray.PhaseSpace

/-- The velocity truncated to the early support `ν s ≤ 3/2` of `1-χ_o` (source 4163-4166). -/
def earlyTrunc (ν : ℝ) (w : Chart → Merid) : Chart → Merid :=
  fun p => if ν * p.1 ≤ 3 / 2 then w p else 0

/-- **Leaf `EarlyPhasePointwise`** (source 4147, 5153-5157, 5169-5171, 4163-4166): the physical
early repair stress `(1-χ_o)(r_b ⊗ 𝒩_v w + 𝒩_v w ⊗ r_b)` satisfies
`|F| ≤ 2|r_b||𝒩_v (w 1_{νs ≤ 3/2})|` for a.e. `(τ, y)` in the cell (as `RepPhasePointwise`, with
`0 ≤ 1-χ_o ≤ 1` and `1-χ_o = 0` for `νs ≥ 3/2`). -/
def EarlyPhasePointwise : Prop :=
  ∀ (Pl : PlanarData) (K : ReturnConsts) (L : ReturnLevel) (μ : ℝ), 0 < K.C0 → NearAt Pl K L μ →
    (∃ M : Hsp (cOf L.ν) →L[ℝ] Zsp (cOf L.ν) K.mZ (L.ρb Pl K),
      NearInst.IsSplitMult M (L.params Pl).R L.V L.rb) →
    (∀ τ, AxiNoSwirlPt (L.rb τ)) →
    (∀ τ y, L.rb (τ + 2 * cOf L.ν / L.ε⁻¹) y = L.rb τ y) →
    ∀ w : LVel Pl L, ∀ᵐ τ ∂(volume.restrict (Ioc 0 (2 * L.ε * cOf L.ν))), ∀ᵐ y : Space,
      UnforcedLeray.Short.IIIa.tensorNorm
          (ertSrcPhys Pl K L (multOp Pl K L w) (τ, y)) ≤
        2 * ‖L.rb τ y‖ * ‖velPhys L.ε⁻¹ (cOf L.ν) (earlyTrunc L.ν w) (τ, y)‖

/-- **Leaf `EarlyVelSliceMeas`** (as `VelSliceMeas`, source 2683): phase slices of the truncated
`𝒩_v` are a.e.-strongly measurable. -/
def EarlyVelSliceMeas : Prop :=
  ∀ (Pl : PlanarData) (L : ReturnLevel) (w : LVel Pl L),
    ∀ᵐ τ ∂(volume.restrict (Ioc 0 (2 * L.ε * cOf L.ν))),
      AEStronglyMeasurable
        (fun y : Space => velPhys L.ε⁻¹ (cOf L.ν) (earlyTrunc L.ν w) (τ, y)) volume

/-- **Leaf `EarlyVelPhysL2`** (source 2683-2689, 5173-5176): if `g(t) ≤ Γ` for `0 ≤ t ≤ 3/(2ν)`,
the phase-normalized `L²` norm of `𝒩_v` of the early-truncated `w` is at most `C₁ R Γ ‖w‖`
(`‖w‖² = ∫ |w|² π g⁻² dageμ(-3/2)`, and on the support `g⁻¹ ≥ Γ⁻¹`). -/
def EarlyVelPhysL2 : Prop :=
  ∃ C1 : ℝ, 0 ≤ C1 ∧ ∀ (Pl : PlanarData) (L : ReturnLevel) (w : LVel Pl L) (Γ : ℝ),
    (∀ t : ℝ, 0 ≤ t → t ≤ 3 / 2 / L.ν →
      UnforcedLeray.Short.IIIa.gainG (gRate Pl) L.ν t ≤ Γ) →
    ENNReal.ofReal (2 * L.ε * cOf L.ν)⁻¹ *
      ∫⁻ t in Ioc (0 : ℝ) (2 * L.ε * cOf L.ν), ∫⁻ y : Space,
        ENNReal.ofReal ‖velPhys L.ε⁻¹ (cOf L.ν) (earlyTrunc L.ν w) (t, y)‖ ^ 2 ≤
      ENNReal.ofReal ((C1 * L.ε⁻¹ * Γ * ‖w‖) ^ 2)

theorem earlyProductAt_level (Pl : PlanarData) (K : ReturnConsts) (L : ReturnLevel) (S μ : ℝ)
    (hC0 : 0 < K.C0) (hP : 2 * L.ε * cOf L.ν ≤ 1)
    (hsplit : UnforcedLeray.Short.IIb.ExactSplitII (L.params Pl) (L.ρb Pl K) S L.V L.rb)
    (hnear : NearAt Pl K L μ)
    (hs : ∃ M : Hsp (cOf L.ν) →L[ℝ] Zsp (cOf L.ν) K.mZ (L.ρb Pl K),
      NearInst.IsSplitMult M (L.params Pl).R L.V L.rb)
    (hRb : RbFacts) (hpt : EarlyPhasePointwise) (hmeas : EarlyVelSliceMeas) (hH : HolderPhase)
    (C1 : ℝ) (hC1 : 0 ≤ C1) (w : LVel Pl L) (Γ : ℝ)
    (hΓ : ∀ t : ℝ, 0 ≤ t → t ≤ 3 / 2 / L.ν →
      UnforcedLeray.Short.IIIa.gainG (gRate Pl) L.ν t ≤ Γ)
    (hV : ENNReal.ofReal (2 * L.ε * cOf L.ν)⁻¹ *
        ∫⁻ t in Ioc (0 : ℝ) (2 * L.ε * cOf L.ν), ∫⁻ y : Space,
          ENNReal.ofReal ‖velPhys L.ε⁻¹ (cOf L.ν) (earlyTrunc L.ν w) (t, y)‖ ^ 2 ≤
        ENNReal.ofReal ((C1 * L.ε⁻¹ * Γ * ‖w‖) ^ 2)) :
    phaseL2Lr (2 * L.ε * cOf L.ν) (22 / 19)
        (ertSrcPhys Pl K L (multOp Pl K L w)) ≤
      ENNReal.ofReal ((2 * K.C0 * C1) * L.ν⁻¹ ^ K.k0 * rhoRep K L * L.ε⁻¹ * Γ * ‖w‖) := by
  obtain ⟨hax, hper, hrbm⟩ := hRb Pl K L S hsplit hP
  have hν := L.ν_pos
  have hε := L.ε_pos
  have hρeq := rhoB_eq Pl K L
  have hrho : 0 ≤ rhoRep K L := by unfold rhoRep; positivity
  have hρb : 0 ≤ L.ρb Pl K := by rw [hρeq]; positivity
  have hΓ0 : 0 ≤ Γ := by
    refine le_trans (Real.exp_pos _).le (hΓ 0 le_rfl (by positivity)) |>.trans' ?_
    exact le_refl _ |>.trans_eq' rfl
  set P := 2 * L.ε * cOf L.ν with hPdef
  set X : ℝ := C1 * L.ε⁻¹ * Γ * ‖w‖ with hX
  have hX0 : 0 ≤ X := by rw [hX]; positivity
  have hphase : ∀ᵐ τ ∂(volume.restrict (Ioc 0 P)),
      (∫⁻ y : Space, ENNReal.ofReal (UnforcedLeray.Short.IIIa.tensorNorm
          (ertSrcPhys Pl K L (multOp Pl K L w) (τ, y))) ^ (22 / 19 : ℝ)) ^ (2 / (22 / 19 : ℝ)) ≤
        (ENNReal.ofReal 2 ^ 2 * ENNReal.ofReal (L.ρb Pl K) ^ 2) *
          ∫⁻ y : Space, ENNReal.ofReal ‖velPhys L.ε⁻¹ (cOf L.ν) (earlyTrunc L.ν w) (τ, y)‖ ^ 2 := by
    filter_upwards [hpt Pl K L μ hC0 hnear hs hax hper w, hmeas Pl L w] with τ h1 h2
    refine le_trans (hH (L.rb τ) (fun y => velPhys L.ε⁻¹ (cOf L.ν) (earlyTrunc L.ν w) (τ, y)) _
      (hrbm τ) h2 h1) ?_
    have he : eLpNorm (L.rb τ) (ENNReal.ofReal UnforcedLeray.Short.IIb.bgp) volume ≤
        ENNReal.ofReal (L.ρb Pl K) :=
      le_trans le_self_add (hsplit.energy τ)
    rw [mul_assoc, mul_assoc]
    gcongr
  have hint : (∫⁻ t in Ioc (0 : ℝ) P, (∫⁻ y : Space, ENNReal.ofReal (UnforcedLeray.Short.IIIa.tensorNorm
          (ertSrcPhys Pl K L (multOp Pl K L w) (t, y))) ^ (22 / 19 : ℝ)) ^ (2 / (22 / 19 : ℝ))) ≤
      (ENNReal.ofReal 2 ^ 2 * ENNReal.ofReal (L.ρb Pl K) ^ 2) *
        ∫⁻ t in Ioc (0 : ℝ) P, ∫⁻ y : Space,
          ENNReal.ofReal ‖velPhys L.ε⁻¹ (cOf L.ν) (earlyTrunc L.ν w) (t, y)‖ ^ 2 := by
    rw [← lintegral_const_mul']
    · exact lintegral_mono_ae hphase
    · exact ENNReal.mul_ne_top (ENNReal.pow_ne_top ENNReal.ofReal_ne_top)
        (ENNReal.pow_ne_top ENNReal.ofReal_ne_top)
  have hfin : ENNReal.ofReal P⁻¹ * (∫⁻ t in Ioc (0 : ℝ) P, (∫⁻ y : Space,
        ENNReal.ofReal (UnforcedLeray.Short.IIIa.tensorNorm
          (ertSrcPhys Pl K L (multOp Pl K L w) (t, y))) ^ (22 / 19 : ℝ)) ^ (2 / (22 / 19 : ℝ))) ≤
      ENNReal.ofReal ((2 * L.ρb Pl K * X) ^ 2) := by
    calc _ ≤ ENNReal.ofReal P⁻¹ * ((ENNReal.ofReal 2 ^ 2 * ENNReal.ofReal (L.ρb Pl K) ^ 2) *
          ∫⁻ t in Ioc (0 : ℝ) P, ∫⁻ y : Space,
            ENNReal.ofReal ‖velPhys L.ε⁻¹ (cOf L.ν) (earlyTrunc L.ν w) (t, y)‖ ^ 2) := by gcongr
      _ = (ENNReal.ofReal 2 ^ 2 * ENNReal.ofReal (L.ρb Pl K) ^ 2) *
          (ENNReal.ofReal P⁻¹ * ∫⁻ t in Ioc (0 : ℝ) P, ∫⁻ y : Space,
            ENNReal.ofReal ‖velPhys L.ε⁻¹ (cOf L.ν) (earlyTrunc L.ν w) (t, y)‖ ^ 2) := by ring
      _ ≤ (ENNReal.ofReal 2 ^ 2 * ENNReal.ofReal (L.ρb Pl K) ^ 2) * ENNReal.ofReal (X ^ 2) := by
          gcongr
      _ = ENNReal.ofReal ((2 * L.ρb Pl K * X) ^ 2) := by
          rw [← ENNReal.ofReal_pow (by norm_num), ← ENNReal.ofReal_pow hρb,
            ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity)]
          congr 1; ring
  have hroot : (ENNReal.ofReal P⁻¹ * (∫⁻ t in Ioc (0 : ℝ) P, (∫⁻ y : Space,
        ENNReal.ofReal (UnforcedLeray.Short.IIIa.tensorNorm
          (ertSrcPhys Pl K L (multOp Pl K L w) (t, y))) ^ (22 / 19 : ℝ)) ^ (2 / (22 / 19 : ℝ)))) ^
        (1 / 2 : ℝ) ≤ ENNReal.ofReal (2 * L.ρb Pl K * X) := by
    calc _ ≤ (ENNReal.ofReal ((2 * L.ρb Pl K * X) ^ 2)) ^ (1 / 2 : ℝ) :=
          ENNReal.rpow_le_rpow hfin (by norm_num)
      _ = ENNReal.ofReal (2 * L.ρb Pl K * X) := by
          rw [ENNReal.ofReal_rpow_of_nonneg (by positivity) (by norm_num)]
          congr 1
          rw [← Real.sqrt_eq_rpow]
          exact Real.sqrt_sq (by positivity)
  refine le_trans hroot (ENNReal.ofReal_le_ofReal (le_of_eq ?_))
  rw [hρeq, hX]; ring

/-- **`earlyRepThinProduct` from the early leaves** (source 5169-5176, 4163-4166). -/
theorem earlyRepThinProduct_of (Pl : PlanarData) (σ₀ mZ dm dp : ℝ)
    (hRb : RbFacts) (hpt : EarlyPhasePointwise) (hmeas : EarlyVelSliceMeas) (hH : HolderPhase)
    (hV : EarlyVelPhysL2) (hPer : PeriodSmall) : EarlyRepThinProduct Pl σ₀ mZ dm dp := by
  obtain ⟨C1, hC1, hV⟩ := hV
  intro D hPl hσ hmZ hst
  refine ⟨2 * D.K.C0 * C1, D.K.k0, by have := hst.C0_pos; positivity, ?_⟩
  filter_upwards [hPer D hst, hst.actual, hst.pins, hst.near] with n h2 h3 h4 h5
  intro Γ hΓ w
  have h4' := h4 0 ⟨by norm_num, by norm_num⟩
  have hΓ' : ∀ t : ℝ, 0 ≤ t → t ≤ 3 / 2 / (D.level n).ν →
      UnforcedLeray.Short.IIIa.gainG (gRate D.Pl) (D.level n).ν t ≤ Γ := hΓ
  exact earlyProductAt_level D.Pl D.K (D.level n) (D.Sin n) (D.mu n 0) hst.C0_pos h2
    h3.split (h5 0 ⟨by norm_num, by norm_num⟩) h4'.split hRb hpt hmeas hH C1 hC1 w Γ hΓ'
    (hV D.Pl (D.level n) w Γ hΓ')

end UnforcedLeray.Short.PartIIIb.Concrete
