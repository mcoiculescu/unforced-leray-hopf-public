import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_4.Org.YThinTrans

/-!
# `PartIII-b:C/rep/4/4/1/org` (a): both stream transitions on scaled repair sources

Source `the November 2 reference manuscript` 5301-5372 (`repair:age-error`), the
Ward fields 4161-4214, the old source 5148-5160, the table 5323-5331, gains 5317-5321, closure
5607-5627.

## Why not `Y` alone

The leaf `YRepStreamBound` (`YRepOrg.lean`, a bound on `Y = (wardOps ..).1` alone on repair
sources) is not a statement of the source.  By `ward:cutoff-source` (4203-4214) and
`W_μ = -S_μ(χ_oT)` (4171), `Y = -χ_yS_μχ_oT + (𝒞_y-χ_y)W_μ + [D_{μ+1},𝒞_y]X₀`, so `Y` contains the
young-old rectangle `χ_yS_μχ_o`, which lies in the far mask (5303-5306) and is cancelled only in
`S_far + Y` (5687-5689).  On repair sources (old source ages `t ≥ 1.2/ν`, gain up to `e^{γ/ν}`,
young receivers without output gain) the table entries give it the sizes
`ε^{63/22}e^{m₀/ν}|N_ν| ≍ e^{(γ/22 + m₀)/ν}` (thin receiver) and `ε^{79/22}e^{3m₀/(2ν)}|N_ν|`
(margin only `13γ/66 < 19γ/66`, repair receiver).  The bounds of 5317-5372 are for the
late-output and early-source regions and for the two stream transitions.

This file uses the split of `Org/YThinTrans.lean` (`ageVel = lateEarlyOp + transOp`,
`transOp = Y + χ_yS_μχ_o`, both transitions `transField`), and states the repair-source analogues
of its thin-source facts.

## Contents

* `oldRep w = χ_o(0, (M_Uw)₂)`, the old scaled repair source (4171-4174, 5153-5157).
* Facts at one regime (Props): `SepYoungRepAt` (`sep:resolvent` on young receivers, 3611-3621),
  `ShiftedResolventRepAt` (`D_{μ+1}X₀ = W_μ`, 4196-4201), `TransRepTableAt` (the repair-source row
  of the table for both transitions, 5323-5340, late-output gain 5317-5321).
* `transOp_coef_rep` (proved): the coefficient of `transOp (0, (M_Uw)₂)` is the concrete field
  `transField` of the old repair source.
* Along the sequence: `SepYoungRep`, `ShiftedResolventRep`, `TransRepTable` (Props), the operator
  form `TransRepOpTable`, the bridge `transRepOpTable_of` (proved), and the corrected leaf
  `AgeTransRep` (both transitions on repair sources, margin `19γ/66`).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter UnforcedLeray.Axi
open scoped ENNReal

namespace UnforcedLeray.Short.PartIIIb.Concrete

open UnforcedLeray.Blueprint.Planar (PlanarData)

/-! ## 1. The old repair source and the facts at one regime -/

section Ops

variable (Pl : PlanarData) (K : ReturnConsts) (L : ReturnLevel) (μ : ℝ)
  (hχy : IsStreamCutoff K.χy)

/-- `χ_o(0, T₂)` for `T = M_Uw`: the old scaled repair source (source 4171-4174: "the tensor
`χ_oT = χ_oM_Vw + χ_oM_{r_b}w` is identical in both resolvents. In particular the full repair
stress enters before inversion"; 5153-5157). -/
abbrev oldRep (w : LVel Pl L) : LStr Pl K L :=
  chiOStr (cOf L.ν) K.mZ (L.ρb Pl K) (gRate Pl) L.ν K.hχo (repPart (multOp Pl K L w))

/-- **`sep:resolvent` on the young receiver for the old repair source** (source 3611-3621:
`S_μT = -W_μ` with the separated kernel; 4163-4171, 5153-5157: `W_μ = -S_μ(χ_oT)`; 4187-4194: the
separated-kernel estimates for the repair `L²_τL^{22/19}` source): for representatives of the
components of `χ_o(0,(M_Uw)₂)`, the coefficient of `S_μ(χ_o(0,(M_Uw)₂))` is `-W_μ` at almost every
young chart point `s ≤ 1/ν` (separated from the source support `s ≥ 1.2/ν`). -/
def SepYoungRepAt : Prop :=
  ∀ (w : LVel Pl L) (g₁ g₂ : Chart → Ten3), IsRep Pl K L (oldRep Pl K L w) g₁ g₂ →
    ∀ᵐ p ∂(bodyMeasure (cOf L.ν) (gRate Pl) L.ν), L.ν * p.1 ≤ 1 →
      (Sop Pl K L μ (oldRep Pl K L w) : Chart → Merid) p =
        -coefOf L.ε⁻¹ (wardW L.ν μ L.ε⁻¹ (cOf L.ν) (g₁ + g₂)) p

/-- **`ward:shifted-resolvent`** (source 4196-4201: `X₀ = R_{μ+1}W_μ`, `D_{μ+1}X₀ = W_μ`) for the
old repair source, on the young region. -/
def ShiftedResolventRepAt : Prop :=
  ∀ (w : LVel Pl L) (g₁ g₂ : Chart → Ten3), IsRep Pl K L (oldRep Pl K L w) g₁ g₂ →
    ShiftedResolventYoung L.ν μ L.ε⁻¹ (cOf L.ν) (g₁ + g₂)

/-- **The repair-source row of the table for both transitions** (source 5312-5316: support
`0.8/ν < s < 1/ν`; 5317-5321: late output `g(s)⁻¹ ≤ e^{-4γ/(9ν)}`; 5323-5331: repair source, thin
receiver `ε^{63/22}e^{m₀/ν}` ("the pointwise exponent `79/22`, followed by `ρR`"), scaled repair
receiver `ε^{79/22}e^{3m₀/(2ν)}` ("the source `L^{22/19}` norm and the `L^{11/3}` kernel"), common
`P_νS^{k₁}`, `S = ε^{-b}`, factor `G(w)|N_ν|e^{-4γ/(9ν)}` for late output; 5338-5340: "The outward
stream primitive has the same norm powers, so both transition terms have the late-output
bound").  For every body velocity `w`, representatives of `χ_o(0,(M_Uw)₂)` and every body velocity
`v` whose coefficient is the transition field of that source,
`‖g⁻¹M_Uv‖_Z ≤ P_νS^{k₁}|N_ν|(ε^{63/22}e^{m₀/ν} + ε^{79/22}e^{3m₀/(2ν)})e^{-4γ/(9ν)}G(w)`. -/
def TransRepTableAt (k₁ : ℕ) (C : ℝ) (k : ℕ) : Prop :=
  ∀ (w : LVel Pl L) (g₁ g₂ : Chart → Ten3), IsRep Pl K L (oldRep Pl K L w) g₁ g₂ →
    ∀ v : LVel Pl L,
      (v : Chart → Merid) =ᵐ[bodyMeasure (cOf L.ν) (gRate Pl) L.ν]
          coefOf L.ε⁻¹ (transField L.ν μ L.ε⁻¹ (cOf L.ν) K.χy (g₁ + g₂)) →
        ‖multOp Pl K L v‖ ≤
          C * L.ν⁻¹ ^ k * L.ε ^ (-((k₁ : ℝ) * K.b)) * gaugeN Pl L *
            (L.ε ^ (63 / 22 : ℝ) * Real.exp (K.m0 / L.ν) +
              L.ε ^ (79 / 22 : ℝ) * Real.exp (3 * K.m0 / 2 / L.ν)) *
            Real.exp (-(4 * gRate Pl / 9) / L.ν) * ‖w‖

/-- **The coefficient of `transOp` on repair sources** (source 4203-4214, 5312-5316): from the
Ward pin, `sep:resolvent` on the young receiver and the shifted resolvent identity, the
coefficient of `(Y + χ_yS_μχ_o)(0,(M_Uw)₂)` is the concrete transition field of the old repair
source. -/
theorem transOp_coef_rep
    (hW : IsWardTriple (wardOps Pl K L μ).1 (wardOps Pl K L μ).2.1 (wardOps Pl K L μ).2.2 L.ε μ
      K.hχo K.χy L.U L.pres)
    (h1 : SepYoungRepAt Pl K L μ) (h2 : ShiftedResolventRepAt Pl K L μ) (w : LVel Pl L)
    {g₁ g₂ : Chart → Ten3} (hg : IsRep Pl K L (oldRep Pl K L w) g₁ g₂) :
    (transOp Pl K L μ hχy (repPart (multOp Pl K L w)) : Chart → Merid)
      =ᵐ[bodyMeasure (cOf L.ν) (gRate Pl) L.ν]
        coefOf L.ε⁻¹ (transField L.ν μ L.ε⁻¹ (cOf L.ν) K.χy (g₁ + g₂)) := by
  have hR : 0 < L.ε⁻¹ := inv_pos.2 L.ε_pos
  have hν : 0 ≤ L.ν := L.ν_pos.le
  have hY := (hW (repPart (multOp Pl K L w)) g₁ g₂ hg.1 hg.2).1
  have hS := h1 w g₁ g₂ hg
  have hres := h2 w g₁ g₂ hg
  have hM := youngMul_ae (c := cOf L.ν) (γ := gRate Pl) (ν := L.ν) hχy
    (Sop Pl K L μ (oldRep Pl K L w))
  have hadd := Lp.coeFn_add ((wardOps Pl K L μ).1 (repPart (multOp Pl K L w)))
    (youngOldOp Pl K L μ hχy (repPart (multOp Pl K L w)))
  filter_upwards [hY, hS, hM, hadd, bodyMeasure_ae_pos (cOf L.ν) (gRate Pl) L.ν]
    with p hYp hSp hMp haddp hp
  have hsplit : coefOf L.ε⁻¹ (wardY L.ν μ L.ε⁻¹ (cOf L.ν) K.χy (g₁ + g₂)) p =
      K.χy (L.ν * p.1) • coefOf L.ε⁻¹ (wardW L.ν μ L.ε⁻¹ (cOf L.ν) (g₁ + g₂)) p +
        coefOf L.ε⁻¹ (transField L.ν μ L.ε⁻¹ (cOf L.ν) K.χy (g₁ + g₂)) p := by
    rw [coefOf_congr_pt L.ε⁻¹ p (G := fun τ y => wardYoungW L.ν μ L.ε⁻¹ (cOf L.ν) K.χy (g₁ + g₂) τ y +
        transField L.ν μ L.ε⁻¹ (cOf L.ν) K.χy (g₁ + g₂) τ y)
      (wardY_split hχy hν hres _ (by rw [ϱ_chartY hR hp]; positivity)),
      coefOf_add, coefOf_wardYoungW hR hp]
  have e1 : (transOp Pl K L μ hχy (repPart (multOp Pl K L w)) : Chart → Merid) p =
      ((wardOps Pl K L μ).1 (repPart (multOp Pl K L w)) : Chart → Merid) p +
        (youngMul hχy (Sop Pl K L μ (oldRep Pl K L w)) : Chart → Merid) p := haddp
  rw [e1, hYp, hMp, hsplit]
  change K.χy (L.ν * p.1) • _ + _ + K.χy (L.ν * p.1) • _ = _
  by_cases hyl : L.ν * p.1 ≤ 1
  · rw [hSp hyl, smul_neg]
    abel
  · rw [hχy.zero _ (le_of_lt (lt_of_not_ge hyl))]
    simp

end Ops

/-! ## 2. Along the sequence: the facts, the operator table and the leaf -/

/-- (T1) `sep:resolvent` on the young receiver for the old repair source, for large `n` and
every `z ∈ [-1,1]` (source 3611-3621, 4163-4171, 4187-4194, 5153-5157). -/
def SepYoungRep (dm dp : ℝ) : Prop :=
  ∀ D : SeqData, D.RepairStanding dm dp → ∀ᶠ n : ℕ in atTop, ∀ z ∈ Icc (-1 : ℝ) 1,
    SepYoungRepAt D.Pl D.K (D.level n) (D.mu n z)

/-- (T2) The shifted resolvent identity `D_{μ+1}X₀ = W_μ` on the young region for the old repair
source (source 4196-4201). -/
def ShiftedResolventRep (dm dp : ℝ) : Prop :=
  ∀ D : SeqData, D.RepairStanding dm dp → ∀ᶠ n : ℕ in atTop, ∀ z ∈ Icc (-1 : ℝ) 1,
    ShiftedResolventRepAt D.Pl D.K (D.level n) (D.mu n z)

/-- (T3) The repair-source table row for both transitions (source 5312-5340), with the `S`-degree
`k₁` chosen before `b` (depending only on `Pl, σ₀, m_Z, dm, dp`; 5332, 5607). -/
def TransRepTable (Pl : PlanarData) (σ₀ mZ dm dp : ℝ) : Prop :=
  ∃ k₁ : ℕ, ∀ D : SeqData, D.Pl = Pl → D.σ₀ = σ₀ → D.K.mZ = mZ → D.RepairStanding dm dp →
    ∃ (C : ℝ) (k : ℕ), ∀ᶠ n : ℕ in atTop, ∀ z ∈ Icc (-1 : ℝ) 1,
      TransRepTableAt D.Pl D.K (D.level n) (D.mu n z) k₁ C k

/-- The repair-source table row as a bound on the operator `transOp` (output of
`transRepOpTable_of`). -/
def TransRepOpTable (Pl : PlanarData) (σ₀ mZ dm dp : ℝ) : Prop :=
  ∃ k₁ : ℕ, ∀ D : SeqData, D.Pl = Pl → D.σ₀ = σ₀ → D.K.mZ = mZ →
    ∀ hst : D.RepairStanding dm dp,
    ∃ (C : ℝ) (k : ℕ), ∀ᶠ n : ℕ in atTop, ∀ z ∈ Icc (-1 : ℝ) 1,
      ∀ w : LVel D.Pl (D.level n),
        ‖multOp D.Pl D.K (D.level n)
            (transOp D.Pl D.K (D.level n) (D.mu n z) hst.chiY
              (repPart (multOp D.Pl D.K (D.level n) w)))‖ ≤
          C * (D.level n).ν⁻¹ ^ k * (D.level n).ε ^ (-((k₁ : ℝ) * D.K.b)) *
            gaugeN D.Pl (D.level n) *
            ((D.level n).ε ^ (63 / 22 : ℝ) * Real.exp (D.K.m0 / (D.level n).ν) +
              (D.level n).ε ^ (79 / 22 : ℝ) * Real.exp (3 * D.K.m0 / 2 / (D.level n).ν)) *
            Real.exp (-(4 * gRate D.Pl / 9) / (D.level n).ν) * ‖w‖

/-- **Bridge** (proved): (T1)-(T3) and the Ward pin of the standing hypotheses give the table
row for the operator `transOp` on repair sources. -/
theorem transRepOpTable_of {Pl : PlanarData} {σ₀ mZ dm dp : ℝ} (h1 : SepYoungRep dm dp)
    (h2 : ShiftedResolventRep dm dp) (h3 : TransRepTable Pl σ₀ mZ dm dp) :
    TransRepOpTable Pl σ₀ mZ dm dp := by
  obtain ⟨k₁, H⟩ := h3
  refine ⟨k₁, fun D hPl hσ hmZ hst => ?_⟩
  obtain ⟨C, k, HC⟩ := H D hPl hσ hmZ hst
  refine ⟨C, k, ?_⟩
  filter_upwards [HC, h1 D hst, h2 D hst, hst.pins] with n hn s1 s2 pins z hz w
  have hW : IsWardTriple (wardOps D.Pl D.K (D.level n) (D.mu n z)).1
      (wardOps D.Pl D.K (D.level n) (D.mu n z)).2.1 (wardOps D.Pl D.K (D.level n) (D.mu n z)).2.2
      (D.level n).ε (D.mu n z) D.K.hχo D.K.χy (D.level n).U (D.level n).pres :=
    Classical.epsilon_spec (pins z hz).ward
  have hg : IsRep D.Pl D.K (D.level n) (oldRep D.Pl D.K (D.level n) w)
      ((oldRep D.Pl D.K (D.level n) w).fst : Chart → Ten3)
      ((oldRep D.Pl D.K (D.level n) w).snd : Chart → Ten3) :=
    ⟨EventuallyEq.rfl, EventuallyEq.rfl⟩
  exact hn z hz w _ _ hg _
    (transOp_coef_rep D.Pl D.K (D.level n) (D.mu n z) hst.chiY hW (s1 z hz) (s2 z hz) w hg)

namespace SeqData

/-- **Both stream transitions on scaled repair sources** (source 5312-5316, 5333-5340, the
repair-source margins of the table 5323-5331, closure 5607-5627):
`‖g⁻¹M_U(Y + χ_yS_μχ_o)(0,(M_Uw)₂)‖_Z ≤ P_ν e^{-(19γ/66-ω_b-3m₀/2)/ν}G(w)`. -/
def AgeTransRepAt (D : SeqData) (hχy : IsStreamCutoff D.K.χy) (ωb : ℝ) : Prop :=
  ∃ (C : ℝ) (k : ℕ), ∀ᶠ n : ℕ in atTop, ∀ z ∈ Icc (-1 : ℝ) 1,
    ∀ w : LVel D.Pl (D.level n),
      ‖multOp D.Pl D.K (D.level n)
          (transOp D.Pl D.K (D.level n) (D.mu n z) hχy
            (repPart (multOp D.Pl D.K (D.level n) w)))‖ ≤
        C * (D.level n).ν⁻¹ ^ k *
          Real.exp (-(19 * gRate D.Pl / 66 - ωb - 3 * D.K.m0 / 2) / (D.level n).ν) * ‖w‖

end SeqData

/-- **The repair stream-transition leaf** of `repair:age-error` (replaces `AgeYRep` /
`YRepStreamBound`, which bound `Y` alone): the `S`-degree `k₀` chosen before `b`,
`ω_b = k₀bγ/3` (5607). -/
def AgeTransRep (Pl : PlanarData) (σ₀ mZ dm dp : ℝ) : Prop :=
  ∃ k₀ : ℕ, ∀ D : SeqData, D.Pl = Pl → D.σ₀ = σ₀ → D.K.mZ = mZ →
    ∀ hst : D.RepairStanding dm dp,
      D.AgeTransRepAt hst.chiY ((k₀ : ℝ) * D.K.b * (gRate D.Pl / 3))

end UnforcedLeray.Short.PartIIIb.Concrete
