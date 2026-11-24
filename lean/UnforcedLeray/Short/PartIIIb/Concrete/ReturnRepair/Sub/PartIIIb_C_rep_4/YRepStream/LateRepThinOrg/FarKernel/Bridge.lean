import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_4.YRepStream.LateRepThinOrg.EarlyThinBridge
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_4.YRepStream.EarlyRepThin.Kernel.Bridge
import Mathlib.MeasureTheory.Function.ConvergenceInMeasure

/-!
# `PartIII-b:C/rep/4/4/1/org/5/1/org` (a): the far-mask bridge for the repair source, ungained

Source `the November 2 reference manuscript` 3902-3920 (`S_far = 1_{s<S, t>e^δs}S_ε`,
`S_N = S_ε - S_far`; "the notation for the mask means its exact kernel realization with tensor
partitions before distributional divergence"), 3611-3621 (`sep:resolvent`), 3593-3594 ("we begin
with smooth tensors and then complete in the norms appearing below"), 5303-5306 (far mask `s < S`,
`t > e^δs`, `S = ε^{-b}`), 2697 (`Z₁ = L²(W²s^{-1/2}dς)`).

The far operator `F_far = S_μ - S_N` is the far mask `S_far` (`SopSubIsFarSeq`, task
`PartIII-b:C/rep/5/1/1/1`), whose kernel realization `IsFarMaskG` is pinned on box tensors:
there `S_far F = farOut f`.  `RepFarSepBridgeUng` carries every bound on the **ungained** thin
receiver `z1Ung((M_U v)₁)` proved for far-kernel outputs `v = farOut f` of box tensors, in the
`L²_τL^{22/19}` norm of the lifted source, to the far operator on an arbitrary repair source
`(0,T₂)` (lifted source `𝒩_TT₂`).

Unlike the gained bridge `EarlyFarSepBridge` (`EarlyRepThin/Kernel/Bridge.lean`), whose receiver is
a continuous functional, the ungained norm `z1Ung` is not continuous on the gained stress space;
it is lower semicontinuous along `L²(g⁻²W²s^{-1/2}dς)`-convergent sequences (an a.e. convergent
subsequence and Fatou, `frk_z1Ung_le_of_tendsto`), which is what the completion needs.

Proved here from `StrBoxTrunc` (leaf of `PartIII-b:C/rep/4/4/1/org/7/1/org`) and `SopSubIsFarSeq`
(task `PartIII-b:C/rep/5/1/1/1`): `repFarSepBridgeUng_of`.
-/

set_option autoImplicit false

noncomputable section

open Filter Set MeasureTheory UnforcedLeray.Axi Topology
open UnforcedLeray.Blueprint.Planar (PlanarData)
open scoped ENNReal

namespace UnforcedLeray.Short.PartIIIb.Concrete

/-! ## 1. The repair source -/

/-- The thin component of `(0,T₂)` is zero. -/
theorem frk_repPart_fst {c mZ ρb γ ν : ℝ} (T : StrG c mZ ρb γ ν) : (repPart T).fst = 0 := by
  simp [repPart]

/-- The component sum of the repair source `(0,T₂)` is a.e. `T₂` (source 2700, 5777: the tensor
inverse acts on `T₁ + T₂`). -/
theorem frk_strSum_repPart {c mZ ρb γ ν : ℝ} (T : StrG c mZ ρb γ ν) :
    strSum (repPart T) =ᵐ[ageμ c (-1 / 2)] (T.snd : Chart → Ten3) := by
  have h0 : ∀ᵐ p ∂(gainZ1Measure c mZ γ ν), ((repPart T).fst : Chart → Ten3) p = 0 := by
    rw [frk_repPart_fst]
    exact Lp.coeFn_zero _ _ _
  rw [NearInst.ae_gainZ1Measure, NearInst.ae_z1Measure] at h0
  filter_upwards [h0] with p hp
  simp only [strSum, hp, zero_add, lrt_repPart_snd]

/-! ## 2. Lower semicontinuity of the ungained thin norm -/

/-- **Fatou for the ungained `Z₁` norm**: if `F_k → G` in the gained thin space
`L²(g⁻²W²s^{-1/2}dς)` and `‖F_k‖_{Z₁} ≤ M` (ungained), then `‖G‖_{Z₁} ≤ M` (a subsequence converges
a.e.; the gained and ungained measures have the same null sets). -/
theorem frk_z1Ung_le_of_tendsto {c mZ γ ν : ℝ}
    {F : ℕ → Lp (α := Chart) Ten3 2 (gainZ1Measure c mZ γ ν)}
    {G : Lp (α := Chart) Ten3 2 (gainZ1Measure c mZ γ ν)} {M : ℝ≥0∞}
    (hF : Tendsto F atTop (𝓝 G)) (hM : ∀ k, z1Ung c mZ (F k) ≤ M) :
    z1Ung c mZ G ≤ M := by
  obtain ⟨ns, -, hae⟩ := (tendstoInMeasure_of_tendsto_Lp hF).exists_seq_tendsto_ae
  have hae' : ∀ᵐ p ∂(z1Measure c mZ),
      Tendsto (fun i => ‖(F (ns i) : Chart → Ten3) p‖ₑ ^ (2 : ℝ)) atTop
        (𝓝 (‖(G : Chart → Ten3) p‖ₑ ^ (2 : ℝ))) := by
    rw [← NearInst.ae_gainZ1Measure c mZ γ ν]
    filter_upwards [hae] with p hp
    exact ((ENNReal.continuous_rpow_const).tendsto _).comp
      ((continuous_enorm.tendsto _).comp hp)
  have hle : ∀ k, ∫⁻ p, ‖(F k : Chart → Ten3) p‖ₑ ^ (2 : ℝ) ∂(z1Measure c mZ) ≤
      M ^ (2 : ℝ) := by
    intro k
    have h := hM k
    unfold z1Ung at h
    calc ∫⁻ p, ‖(F k : Chart → Ten3) p‖ₑ ^ (2 : ℝ) ∂(z1Measure c mZ)
        = ((∫⁻ p, ‖(F k : Chart → Ten3) p‖ₑ ^ (2 : ℝ) ∂(z1Measure c mZ)) ^ (1 / 2 : ℝ)) ^
            (2 : ℝ) := by
          rw [← ENNReal.rpow_mul]; norm_num
      _ ≤ M ^ (2 : ℝ) := ENNReal.rpow_le_rpow h (by norm_num)
  have hmeas : ∀ i, AEMeasurable
      (fun p => ‖(F (ns i) : Chart → Ten3) p‖ₑ ^ (2 : ℝ)) (z1Measure c mZ) := fun i =>
    ((Lp.stronglyMeasurable (F (ns i))).measurable.enorm.pow_const _).aemeasurable
  have hfat : ∫⁻ p, ‖(G : Chart → Ten3) p‖ₑ ^ (2 : ℝ) ∂(z1Measure c mZ) ≤ M ^ (2 : ℝ) := by
    calc ∫⁻ p, ‖(G : Chart → Ten3) p‖ₑ ^ (2 : ℝ) ∂(z1Measure c mZ)
        = ∫⁻ p, liminf (fun i => ‖(F (ns i) : Chart → Ten3) p‖ₑ ^ (2 : ℝ)) atTop
            ∂(z1Measure c mZ) := by
          refine lintegral_congr_ae ?_
          filter_upwards [hae'] with p hp
          exact hp.liminf_eq.symm
      _ ≤ liminf (fun i => ∫⁻ p, ‖(F (ns i) : Chart → Ten3) p‖ₑ ^ (2 : ℝ) ∂(z1Measure c mZ))
            atTop := lintegral_liminf_le' hmeas
      _ ≤ M ^ (2 : ℝ) := liminf_le_of_frequently_le' (Frequently.of_forall fun i => hle (ns i))
  unfold z1Ung
  calc (∫⁻ p, ‖(G : Chart → Ten3) p‖ₑ ^ (2 : ℝ) ∂(z1Measure c mZ)) ^ (1 / 2 : ℝ)
      ≤ (M ^ (2 : ℝ)) ^ (1 / 2 : ℝ) := ENNReal.rpow_le_rpow hfat (by norm_num)
    _ = M := by rw [← ENNReal.rpow_mul]; norm_num

/-- The thin component is continuous on the split stress space. -/
theorem frk_tendsto_fst {c mZ ρb γ ν : ℝ} {X : ℕ → StrG c mZ ρb γ ν} {Y : StrG c mZ ρb γ ν}
    (h : Tendsto X atTop (𝓝 Y)) : Tendsto (fun k => (X k).fst) atTop (𝓝 Y.fst) := by
  have hc : Continuous fun x : StrG c mZ ρb γ ν => x.fst :=
    (ContinuousLinearMap.fst ℝ (Lp (α := Chart) Ten3 2 (gainZ1Measure c mZ γ ν))
      (Lp (α := Chart) Ten3 2 (gainHTMeasure c ρb γ ν))).continuous.comp
      (WithLp.prodContinuousLinearEquiv 1 ℝ (Lp (α := Chart) Ten3 2 (gainZ1Measure c mZ γ ν))
        (Lp (α := Chart) Ten3 2 (gainHTMeasure c ρb γ ν))).continuous
  exact (hc.tendsto Y).comp h

/-! ## 3. The bridge -/

/-- **The far-mask bridge for the repair source, ungained thin receiver** (source 3902-3920,
3611-3621, 3593-3594, 5303-5306, 2697): for large `n` and `z ∈ [-1,1]`, every bound
`‖(M_Uv)₁‖_{Z₁} ≤ B‖𝒩_Tf‖_{L²_τL^{22/19}}` (ungained `Z₁`, period `2εc`) valid for the far-kernel
outputs `v = farOut f` (`R = ε⁻¹`, `c = ν⁻²`, gap `δ`, output cut `S = ε^{-b}`) of box tensors
`f` holds for the far operator `F_far = S_μ - S_N` on every repair source `(0,T₂)`, with its lifted
source `𝒩_TT₂` on the right. -/
def RepFarSepBridgeUng (Pl : PlanarData) (σ₀ mZ dm dp : ℝ) : Prop :=
  ∀ D : SeqData, D.Pl = Pl → D.σ₀ = σ₀ → D.K.mZ = mZ → D.RepairStanding dm dp →
    ∀ᶠ n : ℕ in atTop, ∀ z ∈ Icc (-1 : ℝ) 1, ∀ B : ℝ,
      (∀ (v : LVel D.Pl (D.level n)) (f : Chart → Ten3), NearInst.IsBoxTensor f →
        (v : Chart → Merid) =ᵐ[ageμ (cOf (D.level n).ν) (-3 / 2)]
          NearInst.Masked.farOut (D.level n).ε⁻¹ (cOf (D.level n).ν) (D.level n).ν (D.mu n z)
            D.K.δ ((D.level n).Scut D.K) f →
        z1Ung (cOf (D.level n).ν) D.K.mZ
            ((multOp D.Pl D.K (D.level n) v).fst : Chart → Ten3) ≤
          ENNReal.ofReal B * phaseL2Lr (2 * (D.level n).ε * cOf (D.level n).ν) (22 / 19)
            (strPhys (D.level n).ε⁻¹ (cOf (D.level n).ν) f)) →
      ∀ T : LStr D.Pl D.K (D.level n),
        z1Ung (cOf (D.level n).ν) D.K.mZ
            ((multOp D.Pl D.K (D.level n)
              ((Sop D.Pl D.K (D.level n) (D.mu n z) - SNop D.Pl D.K (D.level n) (D.mu n z))
                (repPart T))).fst : Chart → Ten3) ≤
          ENNReal.ofReal B * phaseL2Lr (2 * (D.level n).ε * cOf (D.level n).ν) (22 / 19)
            (strPhys (D.level n).ε⁻¹ (cOf (D.level n).ν) ((repPart T).snd : Chart → Ten3))

/-- **(a) from its leaves** (source 3593-3594, 3902-3920, 5303-5306): the box truncations
`1_{A_k}T₂` of the repair source (`StrBoxTrunc`) are box tensors carried by stresses `F_k → (0,T₂)`;
on them `S_far F_k = farOut(1_{A_k}T₂)` and the lifted source decreases pointwise
(`ebr_phaseL2Lr_indicator_le`); `(M_US_farF_k)₁ → (M_US_far(0,T₂))₁` in the gained thin space and
`z1Ung` is lower semicontinuous (`frk_z1Ung_le_of_tendsto`). -/
theorem repFarSepBridgeUng_of (Pl : PlanarData) (σ₀ mZ dm dp : ℝ) (h1 : StrBoxTrunc)
    (h3 : SopSubIsFarSeq Pl σ₀ mZ dm dp) : RepFarSepBridgeUng Pl σ₀ mZ dm dp := by
  intro D hPl hσ hmZ hst
  filter_upwards [h3 D hPl hσ hmZ hst] with n hn z hz B hB T
  obtain ⟨Sf, hSf, hFS⟩ := hn z hz
  have hc : 0 < cOf (D.level n).ν := cOf_pos (D.level n).ν_pos
  have hρ : 0 < (D.level n).ρb D.Pl D.K := inv_rhoB_pos hst.C0_pos
  have hY := frk_strSum_repPart T
  obtain ⟨A, Fn, hbox, hsum, hlim⟩ := h1 _ _ _ _ _ hc hρ (D.level n).ν_pos _ _
    (Lp.stronglyMeasurable T.snd).measurable hY
  have hbd : ∀ k, z1Ung (cOf (D.level n).ν) D.K.mZ
      ((multOp D.Pl D.K (D.level n) (Sf (Fn k))).fst : Chart → Ten3) ≤
        ENNReal.ofReal B * phaseL2Lr (2 * (D.level n).ε * cOf (D.level n).ν) (22 / 19)
          (strPhys (D.level n).ε⁻¹ (cOf (D.level n).ν) ((repPart T).snd : Chart → Ten3)) := by
    intro k
    have e := hSf (Fn k) ((A k).indicator (T.snd : Chart → Ten3)) (hbox k) (hsum k)
    refine (hB (Sf (Fn k)) _ (hbox k) e).trans ?_
    rw [lrt_repPart_snd]
    exact mul_le_mul_of_nonneg_left
      (ebr_phaseL2Lr_indicator_le _ _ _ _ (by norm_num) _ _) zero_le
  have hcont : Tendsto (fun k => (multOp D.Pl D.K (D.level n) (Sf (Fn k))).fst) atTop
      (𝓝 (multOp D.Pl D.K (D.level n) (Sf (repPart T))).fst) :=
    frk_tendsto_fst ((((multOp D.Pl D.K (D.level n)).comp Sf).continuous.tendsto _).comp hlim)
  rw [hFS]
  exact frk_z1Ung_le_of_tendsto hcont hbd

end UnforcedLeray.Short.PartIIIb.Concrete
