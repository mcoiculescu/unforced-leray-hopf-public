import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_4.Org.FarThin.ThinRepKernel.Kernel

/-!
# `PartIII-b:C/rep/4/1/org/2` (kernel): the ungained thin-to-thin far kernel

Source `the November 2 reference manuscript` 5303-5311 (far mask `s < S`,
`t > e^δs`, `S = ε^{-b}`), 5323-5333 (table, thin source → thin receiver `ε²`, common `P_νS^k`),
5342-5355 (age-zero thin-to-thin: separated pointwise velocity `≤ P_ν ε² s² N_0(e^δ s)`; after the
normalized velocity lift and thin multiplication the square root of the output stress age density
is `≤ P_ν ε²(s^{1/2}+s^{3/4})V_m(s)‖T‖_{Z_1}`, square integrable at zero, integral up to `S`
polynomial in `S`), 5573-5594 (mass estimate `N_0(a)`, logarithmic bins, radial gap
`D_j ≍ R/√s_j`), 3902-3920 (`S_far = 1_{s<S,t>e^δs}S_μ`, kernel realization on box tensors).

**The one leaf of the thin-source/thin-receiver column** (`FarThinThinBox`), stated on the dense
class of box tensors (the completion is the shared `FarBridge`, applied below, proved):
for the far-kernel output `v = farOut g` of a box tensor `g` at a standing level, the thin
component of `M_Uv` has the **ungained** `Z₁` norm
`‖(M_Uv)₁‖_{Z₁} ≤ Cν^{-k}ε^{-k₀b}ε²‖g‖_{Z₁}`, on all output ages and all source ages of the mask
(no gain on either side; `z1Ung`, 2697).  The S-degree `k₀` is chosen before the sequence.

Proved here (`farThinThinKernel_of`): from `FarThinThinBox`, the far part `Sop - SNop = Sf` with
`IsFarMaskG` (`FarThinKernel.far_part`), and `FarBridge.farBridge_le_mono` with the closed receiver
`z1Ung ∘ (M_U ·)₁` (`RecvClosed.lintegral_comp`, `z1Measure ≪ gainZ1Measure`) and the source norm
`z1Ung`, nonincreasing under truncation (`lintegral_indicator_le`), the kernel
`FarThinThinKernel`: `‖(M_U(Sop-SNop)(T₁,0))₁‖_{Z₁} ≤ Cν^{-k}ε^{-k₀b}ε²‖T₁‖_{Z₁}`.
-/

set_option autoImplicit false

noncomputable section

open Filter Set MeasureTheory UnforcedLeray.Axi
open UnforcedLeray.Blueprint.Planar (PlanarData)
open scoped ENNReal

namespace UnforcedLeray.Short.PartIIIb.Concrete

namespace SeqData

variable (D : SeqData)

/-- **The thin-to-thin far kernel on box tensors, ungained** (source 5342-5355, 5573-5594, 5303-5311,
3902-3912; the leaf): for large `n`, `z ∈ [-1,1]` (so `μ > -1/4`), every velocity `v` a.e. equal to
the far-kernel output `farOut g` (`R = ε⁻¹`, mask `δ`, output cut `S = ε^{-b}`) of a box tensor `g`,
`‖(M_Uv)₁‖_{Z₁} ≤ Cν^{-k}ε^{-k₀b}ε²‖g‖_{Z₁}`, both norms without the gain. -/
def FarThinThinBoxAt (k₀ : ℕ) : Prop :=
  ∃ (C : ℝ) (k : ℕ), 0 ≤ C ∧ ∀ᶠ n : ℕ in atTop, ∀ z ∈ Icc (-1 : ℝ) 1,
    -(1 / 4) < D.mu n z → ∀ (v : LVel D.Pl (D.level n)) (g : Chart → Ten3),
      NearInst.IsBoxTensor g →
      (v : Chart → Merid) =ᵐ[ageμ (cOf (D.level n).ν) (-3 / 2)]
        NearInst.Masked.farOut (D.level n).ε⁻¹ (cOf (D.level n).ν) (D.level n).ν (D.mu n z)
          D.K.δ ((D.level n).Scut D.K) g →
      z1Ung (cOf (D.level n).ν) D.K.mZ
          ((multOp D.Pl D.K (D.level n) v).fst : Chart → Ten3) ≤
        ENNReal.ofReal (C * (D.level n).ν⁻¹ ^ k * (D.level n).ε ^ (-((k₀ : ℝ) * D.K.b)) *
          (D.level n).ε ^ (2 : ℝ)) *
        z1Ung (cOf (D.level n).ν) D.K.mZ g

/-- **The ungained thin-to-thin far kernel** (source 5323-5333, 5342-5355): the far operator
`F_far = S_μ - S_N` on a thin source `(T₁,0)`, read on the thin receiver. -/
def FarThinThinKernelAt (k₀ : ℕ) : Prop :=
  ∃ (C : ℝ) (k : ℕ), 0 ≤ C ∧ ∀ᶠ n : ℕ in atTop, ∀ z ∈ Icc (-1 : ℝ) 1,
    ∀ T : LStr D.Pl D.K (D.level n),
      z1Ung (cOf (D.level n).ν) D.K.mZ
          ((multOp D.Pl D.K (D.level n)
            ((Sop D.Pl D.K (D.level n) (D.mu n z) - SNop D.Pl D.K (D.level n) (D.mu n z))
              (thinPart T))).fst : Chart → Ten3) ≤
        ENNReal.ofReal (C * (D.level n).ν⁻¹ ^ k * (D.level n).ε ^ (-((k₀ : ℝ) * D.K.b)) *
          (D.level n).ε ^ (2 : ℝ)) *
        z1Ung (cOf (D.level n).ν) D.K.mZ (T.fst : Chart → Ten3)

end SeqData

/-- The box leaf along every standing sequence, the S-degree `k₀` chosen from
`Pl, σ₀, m_Z, d₋, d₊` before the sequence (source 5332, 5607). -/
def FarThinThinBox (Pl : PlanarData) (σ₀ mZ dm dp : ℝ) : Prop :=
  ∃ k₀ : ℕ, ∀ D : SeqData, D.Pl = Pl → D.σ₀ = σ₀ → D.K.mZ = mZ →
    ∀ _hst : D.RepairStanding dm dp, D.FarThinThinBoxAt k₀

/-- The kernel along every standing sequence. -/
def FarThinThinKernel (Pl : PlanarData) (σ₀ mZ dm dp : ℝ) : Prop :=
  ∃ k₀ : ℕ, ∀ D : SeqData, D.Pl = Pl → D.σ₀ = σ₀ → D.K.mZ = mZ →
    ∀ _hst : D.RepairStanding dm dp, D.FarThinThinKernelAt k₀

/-- **The kernel from the box leaf** (source 3593-3594, 3902-3912, 5303-5311): the shared far bridge
with the closed receiver `z1Ung ∘ (M_U ·)₁`. -/
theorem farThinThinKernel_of (Pl : PlanarData) (σ₀ mZ dm dp : ℝ)
    (h : FarThinThinBox Pl σ₀ mZ dm dp) : FarThinThinKernel Pl σ₀ mZ dm dp := by
  obtain ⟨k₀, hk⟩ := h
  refine ⟨k₀, fun D hPl hσ hmZ hst => ?_⟩
  obtain ⟨C, k, hC, hbox⟩ := hk D hPl hσ hmZ hst
  refine ⟨C, k, hC, ?_⟩
  filter_upwards [FarThinKernel.far_part dm dp D hst, hbox,
    mu_eventually_mem D hst.omega_ne hst.sigma_pos hst.sigma_lt] with
    n hfar hbn hmu z hz T
  have hν : 0 < (D.level n).ν := (D.level n).ν_pos
  have hε : 0 < (D.level n).ε := (D.level n).ε_pos
  have hρ : 0 < (D.level n).ρb D.Pl D.K := inv_rhoB_pos hst.C0_pos
  have hμ : -(1 / 4) < D.mu n z := by
    have := (hmu z hz).1
    linarith [hst.sigma_pos]
  obtain ⟨Sf, hSf, hFS⟩ := hfar z hz
  have hac : z1Measure (cOf (D.level n).ν) D.K.mZ ≪
      gainZ1Measure (cOf (D.level n).ν) D.K.mZ (gRate D.Pl) (D.level n).ν :=
    Measure.ae_le_iff_absolutelyContinuous.1 (NearInst.ae_gainZ1Measure _ _ _ _).ge
  have hcl : FarBridge.RecvClosed (fun v : LVel D.Pl (D.level n) =>
      z1Ung (cOf (D.level n).ν) D.K.mZ
        ((multOp D.Pl D.K (D.level n) v).fst : Chart → Ten3)) :=
    FarBridge.RecvClosed.lintegral_comp (q := 2) hac two_pos
      (FarBridge.continuous_strFst.comp (multOp D.Pl D.K (D.level n)).continuous)
  have hfT := LateThinRep.ltr_strSum_thinPart hρ T
  have hmeas : Measurable (T.fst : Chart → Ten3) := (Lp.stronglyMeasurable _).measurable
  have hbr := FarBridge.farBridge_le_mono hρ hSf hcl hmeas hfT
    (Q := fun g => z1Ung (cOf (D.level n).ν) D.K.mZ g)
    (fun W _ => FarBridge.lintegral_indicator_le _ two_pos W _)
    (B := ENNReal.ofReal (C * (D.level n).ν⁻¹ ^ k * (D.level n).ε ^ (-((k₀ : ℝ) * D.K.b)) *
          (D.level n).ε ^ (2 : ℝ)))
    (fun v g hg hv => hbn z hz hμ v g hg hv)
  have hF : Sop D.Pl D.K (D.level n) (D.mu n z) - SNop D.Pl D.K (D.level n) (D.mu n z) = Sf :=
    hFS
  rw [hF]
  exact hbr

end UnforcedLeray.Short.PartIIIb.Concrete
