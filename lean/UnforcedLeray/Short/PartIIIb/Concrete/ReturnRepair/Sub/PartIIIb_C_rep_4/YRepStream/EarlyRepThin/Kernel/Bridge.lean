import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_4.YRepStream.EarlyRepThin.Props
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_5_1_1Org
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnInst.Inverses.Level
import UnforcedLeray.Short.PartIIIb.NearInst.Masked.Defs

/-!
# `PartIII-b:C/rep/4/4/1/org/7/1/org` (a): the far-mask bridge for the early repair source

Source `the November 2 reference manuscript` 3902-3920 (`S_far = 1_{s<S, t>e^δs}S_ε`,
`S_N = S_ε - S_far`; "the notation for the mask means its exact kernel realization with tensor
partitions before distributional divergence"), 3611-3621 (`sep:resolvent`, `S_μT = -W_μ`),
3593-3594 ("we begin with smooth tensors and then complete in the norms appearing below"),
5303-5308 (the early-source part `χ_yF_far(1-χ_o)` of the far mask `s < S`, `t > e^δs`,
`S = ε^{-b}`).

**Shared** by the two early-source repair entries of the table 5323-5339: the thin receiver
(`EarlyRepThinKernel`, task `PartIII-b:C/rep/4/4/1/org/7/1`) and the scaled repair receiver
(`EarlyRepRepKernel`, task `PartIII-b:C/rep/4/4/1/org/8/1`, whose blocker record
`EarlyRepRep/Kernel/Needed.lean` names this link `NeededEarlyFarSepIdentity`).

The far operator `F_far = S_μ - S_N` is the far mask `S_far` (`SopSubIsFarSeq`, task
`PartIII-b:C/rep/5/1/1/1`), whose kernel realization `IsFarMaskG` is pinned on the dense class of
box tensors: there `S_far F = farOut f` (`NearInst.Masked.farOut`: the masked `sep:resolvent`
response `1_{s<S}s^{-1/2}Re(-W_μ[1_{t>e^δs}𝒩_Tf])_{r,z}` of the lift `𝒩_Tf` read at the receiver
`(chartY, chartTau)`).  The bridge `EarlyFarSepBridge` carries every receiver bound proved for
far-kernel outputs of box tensors, in the `L²_τL^{22/19}` norm of the lifted source, to the early
repair source `(id - χ_o)(0,T₂)`, whose lifted source is `ertSrcPhys T = 𝒩_T((1-χ_o)T₂)`
(the completion of 3593-3594).

Proof (`earlyFarSepBridge_of`, proved here): the box truncations `1_{A_k}f` of a representative
`f = ertTen T` of the early source (`StrBoxTrunc`, `EarlySrcStrSum`) are box tensors carried by
stresses `F_k → Y`; on them `S_far F_k = farOut(1_{A_k}f)` and the lifted source decreases
pointwise (`ebr_phaseL2Lr_indicator_le`); continuity of `Φ ∘ S_far` passes the bound to `Y`.

Leaves: `StrBoxTrunc`, `EarlySrcStrSum` (stated here), `SopSubIsFarSeq` (task
`PartIII-b:C/rep/5/1/1/1`).
-/

set_option autoImplicit false

noncomputable section

open Filter Set MeasureTheory UnforcedLeray.Axi Topology
open UnforcedLeray.Blueprint.Planar (PlanarData)
open scoped ENNReal

namespace UnforcedLeray.Short.PartIIIb.Concrete

/-! ## 1. The early repair source -/

/-- The chart representative `(1-χ_o)T₂` of the early repair stress (source 5303-5308; the Lp
representative of the repair component of `T - χ_oT`). -/
def ertTen (Pl : PlanarData) (K : ReturnConsts) (L : ReturnLevel) (T : LStr Pl K L) :
    Chart → Ten3 :=
  ((T - chiOStr (cOf L.ν) K.mZ (L.ρb Pl K) (gRate Pl) L.ν K.hχo T).snd : Chart → Ten3)

theorem ertSrcPhys_eq (Pl : PlanarData) (K : ReturnConsts) (L : ReturnLevel) (T : LStr Pl K L) :
    ertSrcPhys Pl K L T = strPhys L.ε⁻¹ (cOf L.ν) (ertTen Pl K L T) := rfl

theorem ertTen_measurable (Pl : PlanarData) (K : ReturnConsts) (L : ReturnLevel)
    (T : LStr Pl K L) : Measurable (ertTen Pl K L T) :=
  (Lp.stronglyMeasurable _).measurable

/-! ## 2. Leaves -/

/-- **The early source of a repair part** (source 5303-5308, 4163-4166): for `ρ_b > 0`
(`C₀ > 0`) the component sum of `(id - χ_o)(0, T₂)` is a.e. the representative
`ertTen T = ((T - χ_oT)₂)` of `(1-χ_o)T₂` (`repPart` has zero thin component, `chiOStr` acts
componentwise; the gain measures have the null sets of `s^{-1/2}dς`). -/
def EarlySrcStrSum : Prop :=
  ∀ (Pl : PlanarData) (K : ReturnConsts) (L : ReturnLevel), 0 < K.C0 → ∀ T : LStr Pl K L,
    strSum ((ContinuousLinearMap.id ℝ (LStr Pl K L) -
        chiOStr (cOf L.ν) K.mZ (L.ρb Pl K) (gRate Pl) L.ν K.hχo) (repPart T))
      =ᵐ[ageμ (cOf L.ν) (-1 / 2)] ertTen Pl K L T

/-- **Box truncation of a stress** (source 3593-3594 "complete in the norms appearing below",
3905-3912 the kernel pin on the dense box class; 2697-2700 the split stress norm): for `c, ρ_b, ν > 0`
and a stress `F` whose component sum has the measurable representative `f`, there are sets `A_k`
(e.g. `{1/(k+1) ≤ s ≤ k+1, |η| ≤ k+1, ‖f‖ ≤ k+1}`) and stresses `F_k → F` (componentwise
multiplication by `1_{A_k}`) whose component sums are a.e. the box tensors `1_{A_k}f`.
(Dominated convergence in both gain-weighted `L²` components; `A_k ↑ {s > 0}`.) -/
def StrBoxTrunc : Prop :=
  ∀ (c mZ ρb γ ν : ℝ), 0 < c → 0 < ρb → 0 < ν → ∀ (F : StrG c mZ ρb γ ν) (f : Chart → Ten3),
    Measurable f → strSum F =ᵐ[ageμ c (-1 / 2)] f →
    ∃ (A : ℕ → Set Chart) (Fn : ℕ → StrG c mZ ρb γ ν),
      (∀ k, NearInst.IsBoxTensor ((A k).indicator f)) ∧
      (∀ k, strSum (Fn k) =ᵐ[ageμ c (-1 / 2)] (A k).indicator f) ∧
      Tendsto Fn atTop (𝓝 F)

/-! ## 3. The bridge -/

/-- **The far-mask bridge for the early repair source** (source 3902-3920, 3611-3621, 3593-3594,
5303-5308): for large `n` and `z ∈ [-1,1]`, every bound
`‖Φ v‖ ≤ B‖𝒩_Tf‖_{L²_τL^{22/19}}` (period `2εc`) of a continuous linear functional `Φ` of the
velocity, valid for the far-kernel outputs `v = farOut f` (`NearInst.Masked.farOut` with the
level's `R = ε⁻¹`, `c = ν⁻²`, gap `δ`, output cut `S = ε^{-b}`) of box tensors `f`, holds for
the far operator `F_far = S_μ - S_N` applied to the early repair source `(id - χ_o)(0,T₂)`, with
its lifted source `ertSrcPhys T = 𝒩_T((1-χ_o)T₂)` on the right.  Applied with
`Φ = (·)₁ ∘ M_U ∘ χ_y` (thin receiver, `earlyRepThinKernel_of`) and `Φ = (·)₂ ∘ M_U ∘ χ_y`
(scaled repair receiver, `EarlyRepRepKernel`). -/
def EarlyFarSepBridge (Pl : PlanarData) (σ₀ mZ dm dp : ℝ) : Prop :=
  ∀ D : SeqData, D.Pl = Pl → D.σ₀ = σ₀ → D.K.mZ = mZ → D.RepairStanding dm dp →
    ∀ᶠ n : ℕ in atTop, ∀ z ∈ Icc (-1 : ℝ) 1, ∀ (E : Type) [NormedAddCommGroup E]
      [NormedSpace ℝ E] (Φ : LVel D.Pl (D.level n) →L[ℝ] E) (B : ℝ),
      (∀ (v : LVel D.Pl (D.level n)) (f : Chart → Ten3), NearInst.IsBoxTensor f →
        (v : Chart → Merid) =ᵐ[ageμ (cOf (D.level n).ν) (-3 / 2)]
          NearInst.Masked.farOut (D.level n).ε⁻¹ (cOf (D.level n).ν) (D.level n).ν (D.mu n z)
            D.K.δ ((D.level n).Scut D.K) f →
        ENNReal.ofReal ‖Φ v‖ ≤ ENNReal.ofReal B *
          phaseL2Lr (2 * (D.level n).ε * cOf (D.level n).ν) (22 / 19)
            (strPhys (D.level n).ε⁻¹ (cOf (D.level n).ν) f)) →
      ∀ T : LStr D.Pl D.K (D.level n),
        ENNReal.ofReal ‖Φ ((Sop D.Pl D.K (D.level n) (D.mu n z) -
            SNop D.Pl D.K (D.level n) (D.mu n z))
          ((ContinuousLinearMap.id ℝ (LStr D.Pl D.K (D.level n)) -
            chiOStr (cOf (D.level n).ν) D.K.mZ ((D.level n).ρb D.Pl D.K) (gRate D.Pl)
              (D.level n).ν D.K.hχo) (repPart T)))‖ ≤
          ENNReal.ofReal B * phaseL2Lr (2 * (D.level n).ε * cOf (D.level n).ν) (22 / 19)
            (ertSrcPhys D.Pl D.K (D.level n) T)

/-! ## 4. Proof of the bridge from the leaves -/

theorem ebr_nsSym_zero : NearInst.nsSym (0 : Ten3) = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [NearInst.nsSym, NearInst.symRZ]

theorem ebr_tensorNorm_nonneg (M : Matrix (Fin 3) (Fin 3) ℝ) :
    0 ≤ UnforcedLeray.Short.IIIa.tensorNorm M := Real.sqrt_nonneg _

/-- The lift of a truncation is pointwise the lift or zero. -/
theorem ebr_tensorNorm_indicator_le (R c : ℝ) (A : Set Chart) (f : Chart → Ten3)
    (x : ℝ × Space) :
    UnforcedLeray.Short.IIIa.tensorNorm (strPhys R c (A.indicator f) x) ≤
      UnforcedLeray.Short.IIIa.tensorNorm (strPhys R c f x) := by
  unfold strPhys NearInst.cartLift
  by_cases h : NearInst.chartOf R c x.2 x.1 ∈ A
  · rw [Set.indicator_of_mem h]
  · rw [Set.indicator_of_notMem h, ebr_nsSym_zero, smul_zero, Matrix.mul_zero, Matrix.zero_mul]
    have h0 : UnforcedLeray.Short.IIIa.tensorNorm (0 : Matrix (Fin 3) (Fin 3) ℝ) = 0 := by
      simp [UnforcedLeray.Short.IIIa.tensorNorm]
    rw [h0]
    exact ebr_tensorNorm_nonneg _

/-- The `L²_τL^r` norm of the lifted source decreases under truncation. -/
theorem ebr_phaseL2Lr_indicator_le (P r R c : ℝ) (hr : 0 < r) (A : Set Chart)
    (f : Chart → Ten3) :
    phaseL2Lr P r (strPhys R c (A.indicator f)) ≤ phaseL2Lr P r (strPhys R c f) := by
  unfold phaseL2Lr
  refine ENNReal.rpow_le_rpow ?_ (by norm_num)
  refine mul_le_mul_of_nonneg_left ?_ zero_le
  refine lintegral_mono (fun t => ?_)
  refine ENNReal.rpow_le_rpow ?_ (by positivity)
  refine lintegral_mono (fun y => ?_)
  exact ENNReal.rpow_le_rpow (ENNReal.ofReal_le_ofReal (ebr_tensorNorm_indicator_le R c A f _))
    hr.le

/-- **(a) from its leaves** (source 3593-3594, 3902-3920, 5303-5308). -/
theorem earlyFarSepBridge_of (Pl : PlanarData) (σ₀ mZ dm dp : ℝ) (h1 : StrBoxTrunc)
    (h2 : EarlySrcStrSum) (h3 : SopSubIsFarSeq Pl σ₀ mZ dm dp) :
    EarlyFarSepBridge Pl σ₀ mZ dm dp := by
  intro D hPl hσ hmZ hst
  filter_upwards [h3 D hPl hσ hmZ hst] with n hn z hz E _ _ Φ B hB T
  obtain ⟨Sf, hSf, hFS⟩ := hn z hz
  have hc : 0 < cOf (D.level n).ν := cOf_pos (D.level n).ν_pos
  have hρ : 0 < (D.level n).ρb D.Pl D.K := inv_rhoB_pos hst.C0_pos
  have hY := h2 D.Pl D.K (D.level n) hst.C0_pos T
  obtain ⟨A, Fn, hbox, hsum, hlim⟩ := h1 _ _ _ _ _ hc hρ (D.level n).ν_pos _ _
    (ertTen_measurable D.Pl D.K (D.level n) T) hY
  have hbd : ∀ k, ENNReal.ofReal ‖Φ (Sf (Fn k))‖ ≤ ENNReal.ofReal B *
      phaseL2Lr (2 * (D.level n).ε * cOf (D.level n).ν) (22 / 19)
        (ertSrcPhys D.Pl D.K (D.level n) T) := by
    intro k
    have e := hSf (Fn k) ((A k).indicator (ertTen D.Pl D.K (D.level n) T)) (hbox k) (hsum k)
    refine (hB (Sf (Fn k)) _ (hbox k) e).trans ?_
    rw [ertSrcPhys_eq]
    exact mul_le_mul_of_nonneg_left
      (ebr_phaseL2Lr_indicator_le _ _ _ _ (by norm_num) _ _) zero_le
  have hcont : Tendsto (fun k => ENNReal.ofReal ‖Φ (Sf (Fn k))‖) atTop
      (𝓝 (ENNReal.ofReal ‖Φ (Sf ((ContinuousLinearMap.id ℝ (LStr D.Pl D.K (D.level n)) -
        chiOStr (cOf (D.level n).ν) D.K.mZ ((D.level n).ρb D.Pl D.K) (gRate D.Pl)
          (D.level n).ν D.K.hχo) (repPart T)))‖)) := by
    have h0 := ((Φ.comp Sf).continuous.tendsto _).comp hlim
    exact (ENNReal.continuous_ofReal.tendsto _).comp (h0.norm)
  rw [hFS]
  exact le_of_tendsto' hcont hbd

end UnforcedLeray.Short.PartIIIb.Concrete
