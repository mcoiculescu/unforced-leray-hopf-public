import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_8_1_1
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_8_1.GeomX.Asm.Tools
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_8_2.MeanXHess
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_8_1.GeomX.Measurable
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_8_1.HessianBound.ZActJet
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_8_1.HessianBound.StreamCutHess

/-!
# `PartIII-b:C/rep/8/1/2` (`hessianBound`): the Hessian bound of step (a)

Source `the November 2 reference manuscript`
5438-5448, 5404-5413.

`hessData = hessSize(actX) + hessSize(mnX)`.  The mean part is discharged here from `meanXHess`
(pointwise bound, phase-free field, so the cell norm is the value).  The thin-field part is the
single remaining kernel fact `ActXHess` (`‖D²X₁‖_{L²_τ} ≤ P_ν ε⁴ s³ N`, the separated kernel count
of 5404-5413 for `X₁ = 𝒞_y(W_μ - W_{μ+1})` with the stream cutoff and outward primitive).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology UnforcedLeray.Axi
open scoped ENNReal

namespace UnforcedLeray.Short.PartIIIb.Concrete

open UnforcedLeray.Blueprint.Planar (PlanarData)

section Regime

variable (Pl : PlanarData) (K : ReturnConsts) (L : ReturnLevel) (μ : ℝ)

/-- **Thin-field Hessian bound** (source 5438-5448, 5404-5413): `‖D²_yX₁‖_{L²_τ} ≤ P_ν ε⁴ s³ N`
at young chart points, with measurability of the phase function along the cell. -/
def ActXHessAt (C : ℝ) (k : ℕ) : Prop :=
  ∀ T : LStr Pl K L, ∀ s ∈ Ioc (0 : ℝ) (1 / L.ν), ∀ η : ℝ,
    AEMeasurable (fun q : ℝ => hessSize (actX Pl K L μ T (NearInst.chartTau L.ε⁻¹ (s, (q, η))))
        (NearInst.chartY L.ε⁻¹ (s, (q, η)))) (volume.restrict (Ico (-cOf L.ν / 2) (cOf L.ν / 2))) ∧
    cellL2 L.ε⁻¹ (cOf L.ν) (fun τ y => hessSize (actX Pl K L μ T τ) y) s η ≤
      ENNReal.ofReal (C * L.ν⁻¹ ^ k * (L.ε ^ 4 * s ^ 3)) * oldN1 Pl K L T

/-- The mean part of the Hessian bound from the pointwise `MeanXHessAt`. -/
theorem meanPart {C : ℝ} {k : ℕ} (hM : MeanXHessAt Pl K L μ C k) (T : LStr Pl K L)
    (s : ℝ) (hs : s ∈ Ioc (0 : ℝ) (1 / L.ν)) (η : ℝ) :
    AEMeasurable (fun q : ℝ => hessSize (mnX Pl K L μ T (NearInst.chartTau L.ε⁻¹ (s, (q, η))))
        (NearInst.chartY L.ε⁻¹ (s, (q, η)))) (volume.restrict (Ico (-cOf L.ν / 2) (cOf L.ν / 2))) ∧
    cellL2 L.ε⁻¹ (cOf L.ν) (fun τ y => hessSize (mnX Pl K L μ T τ) y) s η ≤
      ENNReal.ofReal ((9 * C) * L.ν⁻¹ ^ k * (L.ε ^ 4 * s ^ 3)) * oldN1 Pl K L T := by
  have hY : ∀ q : ℝ, NearInst.chartY L.ε⁻¹ (s, (q, η)) = NearInst.chartY L.ε⁻¹ (s, (0, η)) := by
    intro q; simp [NearInst.chartY]
  have hfun : (fun q : ℝ => hessSize (mnX Pl K L μ T (NearInst.chartTau L.ε⁻¹ (s, (q, η))))
        (NearInst.chartY L.ε⁻¹ (s, (q, η)))) =
      fun _ => hessSize (mnX Pl K L μ T 0) (NearInst.chartY L.ε⁻¹ (s, (0, η))) := by
    funext q
    rw [hY q]
    rfl
  refine ⟨?_, ?_⟩
  · rw [hfun]; exact aemeasurable_const
  · have hc : 0 < cOf L.ν := cOf_pos L.ν_pos
    rw [GeomXAsm.cellL2_eq_cellN]
    have hfun' : (fun q : ℝ => ENNReal.ofReal
        (hessSize (mnX Pl K L μ T (NearInst.chartTau L.ε⁻¹ (s, (q, η))))
          (NearInst.chartY L.ε⁻¹ (s, (q, η))))) =
        fun _ => ENNReal.ofReal (hessSize (mnX Pl K L μ T 0) (NearInst.chartY L.ε⁻¹ (s, (0, η)))) := by
      funext q
      exact congrArg ENNReal.ofReal (congrFun hfun q)
    rw [hfun', GeomXAsm.cellN_const hc]
    unfold hessSize
    rw [ENNReal.ofReal_sum_of_nonneg (fun j _ => Finset.sum_nonneg fun l _ => norm_nonneg _)]
    have hterm : ∀ j l : Fin 3,
        ENNReal.ofReal ‖physPd2 (mnX Pl K L μ T 0) j l (NearInst.chartY L.ε⁻¹ (s, (0, η)))‖ ≤
          ENNReal.ofReal (C * L.ν⁻¹ ^ k * (L.ε ^ 4 * s ^ 3)) * oldN1 Pl K L T := by
      intro j l
      have h := hM T (s, (0, η)) hs.1 hs.2 j l
      rw [ofReal_norm]
      have e : C * L.ν⁻¹ ^ k * L.ε ^ 4 * s ^ (3 : ℝ) = C * L.ν⁻¹ ^ k * (L.ε ^ 4 * s ^ 3) := by
        rw [show s ^ (3 : ℝ) = s ^ (3 : ℕ) from by exact_mod_cast Real.rpow_natCast s 3]
        ring
      simp only [] at h
      rw [e] at h
      exact h
    calc ∑ j : Fin 3, ENNReal.ofReal (∑ l : Fin 3,
          ‖physPd2 (mnX Pl K L μ T 0) j l (NearInst.chartY L.ε⁻¹ (s, (0, η)))‖)
        = ∑ j : Fin 3, ∑ l : Fin 3, ENNReal.ofReal
          ‖physPd2 (mnX Pl K L μ T 0) j l (NearInst.chartY L.ε⁻¹ (s, (0, η)))‖ :=
          Finset.sum_congr rfl fun j _ => ENNReal.ofReal_sum_of_nonneg fun l _ => norm_nonneg _
      _ ≤ ∑ _j : Fin 3, ∑ _l : Fin 3,
          ENNReal.ofReal (C * L.ν⁻¹ ^ k * (L.ε ^ 4 * s ^ 3)) * oldN1 Pl K L T :=
          Finset.sum_le_sum fun j _ => Finset.sum_le_sum fun l _ => hterm j l
      _ = 9 * (ENNReal.ofReal (C * L.ν⁻¹ ^ k * (L.ε ^ 4 * s ^ 3)) * oldN1 Pl K L T) := by
          simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
          norm_num
          ring
      _ = ENNReal.ofReal ((9 * C) * L.ν⁻¹ ^ k * (L.ε ^ 4 * s ^ 3)) * oldN1 Pl K L T := by
          have e : ENNReal.ofReal ((9 * C) * L.ν⁻¹ ^ k * (L.ε ^ 4 * s ^ 3)) =
              9 * ENNReal.ofReal (C * L.ν⁻¹ ^ k * (L.ε ^ 4 * s ^ 3)) := by
            rw [show (9 * C) * L.ν⁻¹ ^ k * (L.ε ^ 4 * s ^ 3) =
              9 * (C * L.ν⁻¹ ^ k * (L.ε ^ 4 * s ^ 3)) by ring,
              ENNReal.ofReal_mul (p := 9) (by norm_num), ENNReal.ofReal_ofNat]
          rw [e]
          ring

/-- The Hessian bound at one regime from the thin-field fact and the mean part. -/
theorem hessianBoundAt_of {C1 C2 : ℝ} {k1 k2 : ℕ} (hν1 : L.ν ≤ 1)
    (hA : ActXHessAt Pl K L μ C1 k1) (hM : MeanXHessAt Pl K L μ C2 k2) :
    HessianBoundAt Pl K L μ (|C1| + 9 * |C2|) (max k1 k2) := by
  intro T s hs η
  obtain ⟨hAm, hAb⟩ := hA T s hs η
  obtain ⟨hMm, hMb⟩ := meanPart Pl K L μ hM T s hs η
  have hF : 0 ≤ L.ε ^ 4 * s ^ 3 := by
    have := L.ε_pos; have := hs.1; positivity
  refine ⟨?_, ?_⟩
  · exact hAm.add hMm
  · have hsum := cellL2_add_le L.ε⁻¹ (cOf L.ν) (fun τ y => hessSize (actX Pl K L μ T τ) y)
      (fun τ y => hessSize (mnX Pl K L μ T τ) y)
      (fun τ y => hessSize_nonneg _ _) (fun τ y => hessSize_nonneg _ _) s η hAm hMm
    have h1 := bound_mono L.ν_pos hν1 hF (le_abs_self C1) (by positivity) (le_max_left k1 k2) hAb
    have h2 := bound_mono L.ν_pos hν1 hF (show 9 * C2 ≤ 9 * |C2| by
      have := le_abs_self C2; linarith) (by positivity) (le_max_right k1 k2) hMb
    refine hsum.trans ?_
    refine (add_le_add h1 h2).trans (le_of_eq ?_)
    have hp : 0 ≤ L.ν⁻¹ ^ max k1 k2 := pow_nonneg (inv_nonneg.2 L.ν_pos.le) _
    rw [← add_mul, ← ENNReal.ofReal_add (mul_nonneg (mul_nonneg (abs_nonneg _) hp) hF)
      (mul_nonneg (mul_nonneg (by positivity) hp) hF)]
    congr 2
    ring

end Regime

namespace SeqData

variable (D : SeqData)

/-- Sequence form of `ActXHessAt`. -/
def ActXHess : Prop :=
  ∃ (C : ℝ) (k : ℕ), ∀ᶠ n : ℕ in atTop, ∀ z ∈ Icc (-1 : ℝ) 1,
    ActXHessAt D.Pl D.K (D.level n) (D.mu n z) C k

end SeqData

/-- **`hessianBound` modulo the thin-field fact** (source 5438-5448). -/
theorem hessianBound_of (D : SeqData) {dm dp : ℝ} (hst : D.RepairStanding dm dp)
    (hA : D.ActXHess) : D.HessianBound := by
  obtain ⟨C1, k1, e1⟩ := hA
  obtain ⟨C2, k2, e2⟩ := meanXHess D hst
  have hle := retNu_retEps_eventually_le_one hst.omega_ne hst.gamma_pos D.coeff_ne
  refine ⟨|C1| + 9 * |C2|, max k1 k2, ?_⟩
  filter_upwards [e1, e2, hle] with n a1 a2 hν z hz
  exact hessianBoundAt_of D.Pl D.K (D.level n) (D.mu n z) hν.1 (a1 z hz) (a2 z hz)


/-! ## The thin-field Hessian `ActXHess`: measurability, two leaves, assembly

`X₁ = actX = 𝒞_y zAct` definitionally (`zAct = X₀ = W_μ - W_{μ+1}`, source 4171, 4180-4186).

* **Measurability** (proved, `HessBoundP.actX_hess_aemeasurable`): at a young chart point the
  receiver does not depend on `q` and is off the axis; `actX` is jointly measurable
  (`t84_ward_stream`) and `C²` off the axis (`WardXRegularAt`), so each `∂_j∂_l actX` at the fixed
  receiver is measurable in the phase (two difference-quotient limits,
  `measurable_fderiv_apply_offaxis`).
* **Leaf `StreamCutHessStmt`** (deterministic calculus, source 4178-4186): second derivatives of the
  stream cutoff `𝒞_y Z = χ_y Z + (χ_y'/r)Ψ_Z e_z` at a young point `y = (r, 0, z)`
  (`ν R²/r² ≤ 1`):
  `Σ|∂_j∂_l𝒞Z| ≤ C₀(Σ|∂_j∂_lZ| + r⁻¹Σ|∂_jZ| + r⁻²|Z| + r⁻⁴|Ψ_Z|)`, using
  `|∂^iχ_y| ≲ r^{-i}`, `|∂^i(χ_y'/r)| ≲ r^{-2-i}` (`ν R²/r² ≤ 1`), the stream identities
  `∂_rΨ = rZ_z`, `∂_zΨ = -rZ_r` (so `|DΨ| ≤ 2r|Z|`, `|D²Ψ| ≲ |Z| + r|DZ|`) and `|D²ϱ| ≤ ϱ⁻¹`.
* **Leaf `ZActJetAt`** (the separated kernel count, source 5400-5413, 4178-4184): at every young
  chart point the normalized phase `L²` norms of `|X₀|, Σ|∂X₀|, Σ|∂²X₀|` are
  `≤ P_ν ε^{2+j} s^{(4+j)/2} N` (`j = 0, 1, 2`; the gradient kernel has degree `-5`, so the field
  has degree `-4` and the Hessian `-6`; the radial gap `1/√1.2`), and that of the outward primitive
  `Ψ_{X₀}(r, z)` is `≤ P_ν s N` (`∫_r^∞ ρ ε²(R/ρ)⁴ dρ = s/2`), each with a measurable majorant.
* **Assembly** (proved, `actXHessAt_of`): with `r = R/√s`, `r⁻¹ = ε√s`, each of the four terms is
  `P_ν ε⁴ s³ N`.
-/

namespace HessBoundP

/-- Off the axis, the second partials of the Ward field at a fixed point are measurable in the
phase (source 4171, 4180-4186: `X = 𝒞_y X₀` is jointly measurable and `C²` off the axis). -/
theorem wardX_physPd2_measurable {ν μ R c : ℝ} {χy : ℝ → ℝ} (hχy : IsYoungCutoff χy)
    {g : Chart → Ten3} (hg : Measurable g) (hreg : WardXRegularAt ν μ R c χy g) {y₀ : Space}
    (hy₀ : y₀ ∉ axis) (j l : Fin 3) :
    Measurable fun τ : ℝ => physPd2 (wardX ν μ R c χy g τ) j l y₀ := by
  obtain ⟨X, hXC, hXeq, -, -, -⟩ := hreg
  have hF : Measurable fun p : ℝ × Space => wardX ν μ R c χy g p.1 p.2 :=
    T8_4.t84_ward_stream hχy hg
  have hopen : IsOpen axisᶜ := isClosed_axis.isOpen_compl
  have hev : ∀ τ y, y ∉ axis → wardX ν μ R c χy g τ =ᶠ[𝓝 y] X τ := fun τ y hy => by
    filter_upwards [hopen.mem_nhds hy] with z hz
    exact (hXeq τ z hz).symm
  have hd : ∀ τ y, y ∉ axis → DifferentiableAt ℝ (wardX ν μ R c χy g τ) y := fun τ y hy =>
    ((hXC τ).differentiable (by norm_num) y).congr_of_eventuallyEq (hev τ y hy)
  set G : ℝ → Space → Space := fun τ y =>
    if y ∈ axis then 0 else fderiv ℝ (wardX ν μ R c χy g τ) y (coordinateVector l) with hGdef
  have hG : Measurable fun p : ℝ × Space => G p.1 p.2 :=
    measurable_fderiv_apply_offaxis (F := wardX ν μ R c χy g)
      (V := fun _ _ => coordinateVector l) hF measurable_const hd
  have hGF : ∀ τ y, y ∉ axis →
      G τ =ᶠ[𝓝 y] fun z => physPd (wardX ν μ R c χy g τ) l z := by
    intro τ y hy
    filter_upwards [hopen.mem_nhds hy] with z hz
    have hz' : z ∉ axis := hz
    simp only [hGdef, physPd, hz', ↓reduceIte]
  have hGd : ∀ τ y, y ∉ axis → DifferentiableAt ℝ (G τ) y := by
    intro τ y hy
    have hX1 : ContDiff ℝ 1 (fderiv ℝ (X τ)) := (hXC τ).fderiv_right (m := 1) (by norm_num)
    have hXd : DifferentiableAt ℝ (fun z => fderiv ℝ (X τ) z (coordinateVector l)) y :=
      (hX1.differentiable (by norm_num) y).clm_apply (differentiableAt_const _)
    have hGX : G τ =ᶠ[𝓝 y] fun z => fderiv ℝ (X τ) z (coordinateVector l) := by
      filter_upwards [hopen.mem_nhds hy] with z hz
      have hz' : z ∉ axis := hz
      simp only [hGdef, hz', ↓reduceIte]
      rw [(hev τ z hz).fderiv_eq]
    exact hXd.congr_of_eventuallyEq hGX
  have hH := measurable_fderiv_apply_offaxis (F := G) (V := fun _ _ => coordinateVector j) hG
    measurable_const hGd
  have hcomp := hH.comp (measurable_id.prodMk (measurable_const (a := y₀)))
  convert hcomp using 1
  funext τ
  simp only [Function.comp_apply, id, hy₀, ↓reduceIte]
  rw [(hGF τ y₀ hy₀).fderiv_eq]
  rfl

/-- The young receivers are off the axis. -/
theorem chartY_not_axis {R s : ℝ} (hR : 0 < R) (hs : 0 < s) (q η : ℝ) :
    NearInst.chartY R (s, (q, η)) ∉ axis := by
  intro h
  have h1 := h.1
  have hsq : 0 < Real.sqrt s := Real.sqrt_pos.2 hs
  have : R / Real.sqrt s ≠ 0 := (div_pos hR hsq).ne'
  exact this (by simpa [NearInst.chartY] using h1)

/-- **Measurability of the thin-field Hessian along the cell** (source 4171, 4180-4186). -/
theorem actX_hess_aemeasurable (Pl : PlanarData) (K : ReturnConsts) (L : ReturnLevel) (μ : ℝ)
    (hχy : IsYoungCutoff K.χy) (hmZ : 0 ≤ K.mZ) (hC0 : 0 < K.C0) (hμ : -(1 / 4) < μ)
    (T : LStr Pl K L) {s : ℝ} (hs : 0 < s) (η : ℝ) :
    AEMeasurable (fun q : ℝ => hessSize (actX Pl K L μ T (NearInst.chartTau L.ε⁻¹ (s, (q, η))))
        (NearInst.chartY L.ε⁻¹ (s, (q, η)))) (volume.restrict (Ico (-cOf L.ν / 2) (cOf L.ν / 2))) := by
  have hreg := XMeas.thinG_wardXRegularAt Pl K L μ hχy hmZ hC0 hμ T
  have hg := XMeas.thinG_measurable Pl K L T
  have hY : ∀ q : ℝ, NearInst.chartY L.ε⁻¹ (s, (q, η)) = NearInst.chartY L.ε⁻¹ (s, (0, η)) := by
    intro q; simp [NearInst.chartY]
  have hy₀ := chartY_not_axis (inv_pos.2 L.ε_pos) hs 0 η
  have hm : Measurable fun τ : ℝ =>
      hessSize (actX Pl K L μ T τ) (NearInst.chartY L.ε⁻¹ (s, (0, η))) := by
    unfold hessSize
    refine Finset.measurable_sum _ fun j _ => Finset.measurable_sum _ fun l _ => ?_
    exact (wardX_physPd2_measurable hχy hg hreg hy₀ j l).norm
  have hτ : Measurable fun q : ℝ => NearInst.chartTau L.ε⁻¹ (s, (q, η)) := by
    unfold NearInst.chartTau
    fun_prop
  have hfun : (fun q : ℝ => hessSize (actX Pl K L μ T (NearInst.chartTau L.ε⁻¹ (s, (q, η))))
        (NearInst.chartY L.ε⁻¹ (s, (q, η)))) =
      fun q : ℝ => hessSize (actX Pl K L μ T (NearInst.chartTau L.ε⁻¹ (s, (q, η))))
        (NearInst.chartY L.ε⁻¹ (s, (0, η))) := by
    funext q
    rw [hY q]
  rw [hfun]
  exact (hm.comp hτ).aemeasurable

/-- The positivity of `ρ_b`. -/
theorem rhoB_pos (Pl : PlanarData) (K : ReturnConsts) (L : ReturnLevel) (hC0 : 0 < K.C0) :
    0 < L.ρb Pl K := by
  unfold ReturnLevel.ρb UnforcedLeray.Short.IIb.rhoB
  have hν' : 0 < (L.params Pl).ν := L.ν_pos
  have hε' : 0 < (L.params Pl).ε := L.ε_pos
  exact mul_pos (mul_pos (mul_pos hC0 (inv_pos.2 (pow_pos hν' _))) (Real.exp_pos _))
    (Real.rpow_pos_of_pos hε' _)

/-- `X₀ = zAct` is `C²` on the young region and its outward primitive is its stream function
(source 4171-4186; `WardX0Smooth`, `OutPrimStream`, both proved). -/
theorem zAct_regular (Pl : PlanarData) (K : ReturnConsts) (L : ReturnLevel) (μ : ℝ)
    (hmZ : 0 ≤ K.mZ) (hC0 : 0 < K.C0) (hμ : -(1 / 4) < μ) (T : LStr Pl K L) :
    (∀ τ, ContDiffOn ℝ 2 (zAct Pl K L μ T τ) (youngOpen L.ν L.ε⁻¹)) ∧
    ∀ τ r z, L.ε⁻¹ * Real.sqrt (5 * L.ν / 6) < r →
      HasDerivAt (fun r' => outPrim (zAct Pl K L μ T) τ r' z)
          (r * zAct Pl K L μ T τ !₂[r, 0, z] 2) r ∧
        HasDerivAt (fun z' => outPrim (zAct Pl K L μ T) τ r z')
          (-(r * zAct Pl K L μ T τ !₂[r, 0, z] 0)) z := by
  have hν := L.ν_pos
  have hε := L.ε_pos
  have hρb := rhoB_pos Pl K L hC0
  exact ⟨Final.wardX0Smooth_of (cOf L.ν) K.mZ (L.ρb Pl K) (gRate Pl) L.ν L.ε μ K.hχo
      (cOf_pos hν) hρb hmZ hν hε hμ (thinPart T) _ _ EventuallyEq.rfl EventuallyEq.rfl,
    outPrimStream_of (cOf L.ν) K.mZ (L.ρb Pl K) (gRate Pl) L.ν L.ε μ K.hχo
      (cOf_pos hν) hρb hmZ hν hε hμ (thinPart T) _ _ EventuallyEq.rfl EventuallyEq.rfl⟩

theorem sqrt_mul_rpow_five_half {s : ℝ} (hs : 0 ≤ s) :
    s ^ (5 / 2 : ℝ) = s ^ 2 * Real.sqrt s := by
  rw [show (5 / 2 : ℝ) = 2 + 1 / 2 by norm_num, Real.rpow_add' hs (by norm_num),
    Real.sqrt_eq_rpow, Real.rpow_two]

end HessBoundP

open GeomXAsm

section Regime

variable (Pl : PlanarData) (K : ReturnConsts) (L : ReturnLevel) (μ : ℝ)

/-! ### The assembly at one regime -/

/-- The phase `L²` bound of the thin-field Hessian from the two leaves (source 5445-5447). -/
theorem actXHessL2_of {C₀ C : ℝ} {k : ℕ} (hC₀ : 0 ≤ C₀) (hA : StreamCutHessWith K.χy C₀)
    (hK : ZActJetAt Pl K L μ C k) (T : LStr Pl K L)
    (hZ : ∀ τ, ContDiffOn ℝ 2 (zAct Pl K L μ T τ) (youngOpen L.ν L.ε⁻¹))
    (hS : ∀ τ r z, L.ε⁻¹ * Real.sqrt (5 * L.ν / 6) < r →
      HasDerivAt (fun r' => outPrim (zAct Pl K L μ T) τ r' z)
          (r * zAct Pl K L μ T τ !₂[r, 0, z] 2) r ∧
        HasDerivAt (fun z' => outPrim (zAct Pl K L μ T) τ r z')
          (-(r * zAct Pl K L μ T τ !₂[r, 0, z] 0)) z)
    {s : ℝ} (hs : s ∈ Ioc (0 : ℝ) (1 / L.ν)) (η : ℝ) :
    cellL2 L.ε⁻¹ (cOf L.ν) (fun τ y => hessSize (actX Pl K L μ T τ) y) s η ≤
      ENNReal.ofReal (4 * C₀ * C * L.ν⁻¹ ^ k * (L.ε ^ 4 * s ^ 3)) * oldN1 Pl K L T := by
  obtain ⟨B₀, B₁, B₂, B₃, m₀, m₁, m₂, m₃, h₀, h₁, h₂, h₃, n₀, n₁, n₂, n₃⟩ := hK T s hs η
  have hs0 : 0 < s := hs.1
  have hν := L.ν_pos
  have hε := L.ε_pos
  have hsq : 0 < Real.sqrt s := Real.sqrt_pos.2 hs0
  have hss : Real.sqrt s * Real.sqrt s = s := Real.mul_self_sqrt hs0.le
  set R : ℝ := L.ε⁻¹ with hRdef
  have hR : 0 < R := inv_pos.2 hε
  set r : ℝ := R / Real.sqrt s with hrdef
  have hr0 : 0 < r := div_pos hR hsq
  have hrinv : r⁻¹ = L.ε * Real.sqrt s := by
    rw [hrdef, inv_div, hRdef, div_inv_eq_mul, mul_comm]
  have hyoung : L.ν * (R ^ 2 / r ^ 2) ≤ 1 := by
    have e : R ^ 2 / r ^ 2 = s := by
      rw [hrdef, div_pow, Real.sq_sqrt hs0.le]
      field_simp
    rw [e]
    have := hs.2
    rw [le_div_iff₀ hν] at this
    linarith
  set c := cOf L.ν
  set N := oldN1 Pl K L T
  set a₁ : ℝ≥0∞ := ENNReal.ofReal r⁻¹ with ha₁
  set a₂ : ℝ≥0∞ := ENNReal.ofReal (r⁻¹ ^ 2) with ha₂
  set a₄ : ℝ≥0∞ := ENNReal.ofReal (r⁻¹ ^ 4) with ha₄
  have hri : 0 ≤ r⁻¹ := (inv_pos.2 hr0).le
  -- the pointwise bound
  have hpw : ∀ q : ℝ, ENNReal.ofReal (hessSize (actX Pl K L μ T (NearInst.chartTau R (s, (q, η))))
      (NearInst.chartY R (s, (q, η)))) ≤
      ENNReal.ofReal C₀ * (B₂ q + a₁ * B₁ q + a₂ * B₀ q + a₄ * B₃ q) := by
    intro q
    set τ := NearInst.chartTau R (s, (q, η))
    have key := hA L.ν R (zAct Pl K L μ T) τ r (η / Real.sqrt s) hν hR hr0 hyoung (hZ τ)
      (fun r' z' h => hS τ r' z' h)
    set H := hessSize (zAct Pl K L μ T τ) (hpt r (η / Real.sqrt s))
    set Gs := gradSize (zAct Pl K L μ T τ) (hpt r (η / Real.sqrt s))
    set Zn := ‖zAct Pl K L μ T τ (hpt r (η / Real.sqrt s))‖
    set P := |outPrim (zAct Pl K L μ T) τ r (η / Real.sqrt s)|
    have hH0 : 0 ≤ H := hessSize_nonneg _ _
    have hG0 : 0 ≤ Gs := Finset.sum_nonneg fun _ _ => norm_nonneg _
    have hZ0 : 0 ≤ Zn := norm_nonneg _
    have hP0 : 0 ≤ P := abs_nonneg _
    have b₂ : ENNReal.ofReal H ≤ B₂ q := h₂ q
    have b₁ : ENNReal.ofReal Gs ≤ B₁ q := h₁ q
    have b₀ : ENNReal.ofReal Zn ≤ B₀ q := h₀ q
    have b₃ : ENNReal.ofReal P ≤ B₃ q := h₃ q
    have e1 : hessSize (actX Pl K L μ T τ) (NearInst.chartY R (s, (q, η))) =
        hessSize (wardStreamCut L.ν R K.χy (zAct Pl K L μ T) τ) (hpt r (η / Real.sqrt s)) := rfl
    rw [e1]
    refine (ENNReal.ofReal_le_ofReal key).trans ?_
    rw [ENNReal.ofReal_mul hC₀]
    have t1 : 0 ≤ r⁻¹ * Gs := mul_nonneg hri hG0
    have t2 : 0 ≤ r⁻¹ ^ 2 * Zn := mul_nonneg (pow_nonneg hri 2) hZ0
    have t3 : 0 ≤ r⁻¹ ^ 4 * P := mul_nonneg (pow_nonneg hri 4) hP0
    rw [ENNReal.ofReal_add (add_nonneg (add_nonneg hH0 t1) t2) t3,
      ENNReal.ofReal_add (add_nonneg hH0 t1) t2, ENNReal.ofReal_add hH0 t1,
      ENNReal.ofReal_mul hri, ENNReal.ofReal_mul (pow_nonneg hri 2),
      ENNReal.ofReal_mul (pow_nonneg hri 4)]
    gcongr
  -- the cell norm
  have hX : a₁ * (ENNReal.ofReal (C * L.ν⁻¹ ^ k * (L.ε ^ 3 * s ^ (5 / 2 : ℝ))) * N) =
      ENNReal.ofReal (C * L.ν⁻¹ ^ k * (L.ε ^ 4 * s ^ 3)) * N := by
    rw [← mul_assoc, ha₁, ← ENNReal.ofReal_mul hri]
    congr 2
    rw [hrinv, HessBoundP.sqrt_mul_rpow_five_half hs0.le]
    linear_combination (C * L.ν⁻¹ ^ k * L.ε ^ 4 * s ^ 2) * hss
  have hX2 : a₂ * (ENNReal.ofReal (C * L.ν⁻¹ ^ k * (L.ε ^ 2 * s ^ 2)) * N) =
      ENNReal.ofReal (C * L.ν⁻¹ ^ k * (L.ε ^ 4 * s ^ 3)) * N := by
    rw [← mul_assoc, ha₂, ← ENNReal.ofReal_mul (pow_nonneg hri 2)]
    congr 2
    rw [hrinv]
    linear_combination (C * L.ν⁻¹ ^ k * L.ε ^ 4 * s ^ 2) * hss
  have hX4 : a₄ * (ENNReal.ofReal (C * L.ν⁻¹ ^ k * s) * N) =
      ENNReal.ofReal (C * L.ν⁻¹ ^ k * (L.ε ^ 4 * s ^ 3)) * N := by
    rw [← mul_assoc, ha₄, ← ENNReal.ofReal_mul (pow_nonneg hri 4)]
    congr 2
    rw [hrinv]
    linear_combination (C * L.ν⁻¹ ^ k * L.ε ^ 4 * s * (Real.sqrt s * Real.sqrt s + s)) * hss
  have ma : ∀ (a : ℝ≥0∞) (B : ℝ → ℝ≥0∞), Measurable B →
      AEMeasurable (fun q => a * B q) (cellμ c) := fun a B hB => (hB.const_mul a).aemeasurable
  rw [cellL2_eq_cellN]
  calc cellN c (fun q => ENNReal.ofReal (hessSize (actX Pl K L μ T (NearInst.chartTau R (s, (q, η))))
          (NearInst.chartY R (s, (q, η)))))
      ≤ cellN c (fun q => ENNReal.ofReal C₀ * (B₂ q + a₁ * B₁ q + a₂ * B₀ q + a₄ * B₃ q)) :=
        cellN_mono hpw
    _ = ENNReal.ofReal C₀ * cellN c (fun q => B₂ q + a₁ * B₁ q + a₂ * B₀ q + a₄ * B₃ q) :=
        cellN_const_mul c ENNReal.ofReal_ne_top _
    _ ≤ ENNReal.ofReal C₀ * (cellN c B₂ + a₁ * cellN c B₁ + a₂ * cellN c B₀ + a₄ * cellN c B₃) := by
        gcongr
        have s1 : cellN c (fun q => B₂ q + a₁ * B₁ q + a₂ * B₀ q + a₄ * B₃ q) ≤
            cellN c (fun q => B₂ q + a₁ * B₁ q + a₂ * B₀ q) + cellN c (fun q => a₄ * B₃ q) :=
          cellN_add_le (((m₂.add (m₁.const_mul a₁)).add (m₀.const_mul a₂)).aemeasurable)
            (ma a₄ B₃ m₃)
        have s2 : cellN c (fun q => B₂ q + a₁ * B₁ q + a₂ * B₀ q) ≤
            cellN c (fun q => B₂ q + a₁ * B₁ q) + cellN c (fun q => a₂ * B₀ q) :=
          cellN_add_le ((m₂.add (m₁.const_mul a₁)).aemeasurable) (ma a₂ B₀ m₀)
        have s3 : cellN c (fun q => B₂ q + a₁ * B₁ q) ≤ cellN c B₂ + cellN c (fun q => a₁ * B₁ q) :=
          cellN_add_le m₂.aemeasurable (ma a₁ B₁ m₁)
        calc _ ≤ _ := s1
          _ ≤ _ := add_le_add s2 le_rfl
          _ ≤ _ := add_le_add (add_le_add s3 le_rfl) le_rfl
          _ = _ := by
            rw [cellN_const_mul c (a := a₁) ENNReal.ofReal_ne_top B₁,
              cellN_const_mul c (a := a₂) ENNReal.ofReal_ne_top B₀,
              cellN_const_mul c (a := a₄) ENNReal.ofReal_ne_top B₃]
    _ ≤ ENNReal.ofReal C₀ * (ENNReal.ofReal (C * L.ν⁻¹ ^ k * (L.ε ^ 4 * s ^ 3)) * N +
          a₁ * (ENNReal.ofReal (C * L.ν⁻¹ ^ k * (L.ε ^ 3 * s ^ (5 / 2 : ℝ))) * N) +
          a₂ * (ENNReal.ofReal (C * L.ν⁻¹ ^ k * (L.ε ^ 2 * s ^ 2)) * N) +
          a₄ * (ENNReal.ofReal (C * L.ν⁻¹ ^ k * s) * N)) := by
        gcongr
    _ = ENNReal.ofReal (4 * C₀ * C * L.ν⁻¹ ^ k * (L.ε ^ 4 * s ^ 3)) * N := by
        rw [hX, hX2, hX4]
        have e : ENNReal.ofReal (4 * C₀ * C * L.ν⁻¹ ^ k * (L.ε ^ 4 * s ^ 3)) =
            ENNReal.ofReal 4 * ENNReal.ofReal C₀ *
              ENNReal.ofReal (C * L.ν⁻¹ ^ k * (L.ε ^ 4 * s ^ 3)) := by
          rw [← ENNReal.ofReal_mul (show (0 : ℝ) ≤ 4 by norm_num),
            ← ENNReal.ofReal_mul (mul_nonneg (show (0 : ℝ) ≤ 4 by norm_num) hC₀)]
          congr 1
          ring
        rw [e, ENNReal.ofReal_ofNat]
        ring

/-- **`ActXHessAt` from the two leaves** (source 5438-5448, 5404-5413). -/
theorem actXHessAt_of (hχy : IsYoungCutoff K.χy) (hmZ : 0 ≤ K.mZ) (hC0 : 0 < K.C0)
    (hμ : -(1 / 4) < μ) {C₀ C : ℝ} {k : ℕ} (hC₀ : 0 ≤ C₀) (hA : StreamCutHessWith K.χy C₀)
    (hK : ZActJetAt Pl K L μ C k) : ActXHessAt Pl K L μ (4 * C₀ * C) k := by
  intro T s hs η
  obtain ⟨hZ, hS⟩ := HessBoundP.zAct_regular Pl K L μ hmZ hC0 hμ T
  exact ⟨HessBoundP.actX_hess_aemeasurable Pl K L μ hχy hmZ hC0 hμ T hs.1 η,
    actXHessL2_of Pl K L μ hC₀ hA hK T hZ hS hs η⟩

end Regime

/-- **`ActXHess` from the two leaves** (source 5438-5448, 5404-5413, 4178-4186). -/
theorem actXHess_of_leaves (D : SeqData) {dm dp : ℝ} (hst : D.RepairStanding dm dp)
    (hA : StreamCutHessStmt) (hK : D.ZActJetSeq dm dp) : D.ActXHess := by
  obtain ⟨C₀, hC₀, hAC⟩ := hA D.K.χy hst.chiY
  obtain ⟨C, k, hCk⟩ := hK hst
  have hχy : IsYoungCutoff D.K.χy :=
    ⟨hst.chiY.smooth, hst.chiY.one, hst.chiY.zero, hst.chiY.range⟩
  have hmZ : 0 ≤ D.K.mZ := by have := hst.mZ_gt; linarith
  refine ⟨4 * C₀ * C, k, ?_⟩
  filter_upwards [hCk, muWin_gt_quarter D hst] with n hn hμn z hz
  exact actXHessAt_of D.Pl D.K (D.level n) (D.mu n z) hχy hmZ hst.C0_pos (hμn z hz) hC₀ hAC
    (hn z hz)

/-- **`hessianBound` from the two leaves** (source 5438-5448). -/
theorem hessianBound_of_leaves (D : SeqData) {dm dp : ℝ} (hst : D.RepairStanding dm dp)
    (hA : StreamCutHessStmt) (hK : D.ZActJetSeq dm dp) : D.HessianBound :=
  hessianBound_of D hst (actXHess_of_leaves D hst hA hK)

/-- **`ActXHess`** (source 5438-5448, 5404-5413, 4178-4186). -/
theorem actXHess (D : SeqData) {dm dp : ℝ} (hst : D.RepairStanding dm dp) : D.ActXHess :=
  actXHess_of_leaves D hst streamCutHess (zActJetSeq D dm dp)

/-- **`hessianBound`** (source 5438-5448): the Hessian bound of step (a). -/
theorem hessianBound (D : SeqData) {dm dp : ℝ} (hst : D.RepairStanding dm dp) : D.HessianBound :=
  hessianBound_of D hst (actXHess D hst)

end UnforcedLeray.Short.PartIIIb.Concrete
end
