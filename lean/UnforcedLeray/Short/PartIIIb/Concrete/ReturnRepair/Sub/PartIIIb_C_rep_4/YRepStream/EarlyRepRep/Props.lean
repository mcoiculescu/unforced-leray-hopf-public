import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_4.YRepStream.EarlyRepThin.Props

/-!
# `PartIII-b:C/rep/4/4/1/org/8/org` (L4), Props file: early source, repair source → scaled repair receiver

Source `the November 2 reference manuscript` 5318-5319 (gain `g(t) ≤ e^{3γ/(5ν)}`
on early sources), 5323-5339 (table entry `ε^{79/22}e^{3m₀/(2ν)}`, factor `G(w)e^{3γ/(5ν)}`,
common `P_νS^k`; "the repair-to-repair entry uses the source `L^{22/19}` norm and the `L^{11/3}`
kernel", 5338-5339), 5303-5308 (the early-source part `χ_yF_far(1-χ_o)` of the far mask
`s < S`, `t > e^δs`, `S = ε^{-b}`), 5169-5176 (`repair:source`), 5134-5139
(`ρ = ε^{3/11}e^{m₀/ν}`), 5218-5221 (`repair:phase-gradient`: the `L^{11/3}` kernel on the
repair source has curvature power `ε^{46/11}`).

The entry is the product of

* the **separated-kernel estimate** `EarlyRepRepKernel` (new here): the early-source far operator
  maps the physical early repair stress in `L²_τL^{22/19}` to the scaled repair receiver with the
  kernel power `ε^{46/11}` of the `L^{11/3}` kernel (5218-5221, 5338-5339) times the receiver
  factor `√ρ = ε^{3/22}e^{m₀/(2ν)}` (5336), i.e. `ε^{95/22}e^{m₀/(2ν)}`, and the loss `P_νS^{k₀}`;
* the **repair product estimate, early source** `EarlyRepThinProduct` (reused from the sibling
  `YRepStream/EarlyRepThin/Props.lean`, task `PartIII-b:C/rep/4/4/1/org/7/2`; 5169-5176):
  the early repair source is `≤ P_νρRΓG(w)` where `Γ` bounds the gain `g(t)` on `0 ≤ t ≤ 1.5/ν`;
* the **gain lemma** `earlyRepThinGain` (reused from the same file, proved there):
  `g(t) ≤ e^{3γ/(5ν)}` on `0 ≤ t ≤ 1.5/ν` (5318-5319).

Then `ε^{95/22}·ε^{3/11}·ε^{-1} = ε^{79/22}` and `e^{m₀/(2ν)}e^{m₀/ν} = e^{3m₀/(2ν)}`
(`earlyRepRep_of`).  The late-output analogue is `YRepStream/LateRepRep/Props.lean`
(`LateSepKernelAt`, same kernel/receiver powers with the late gain).
-/

set_option autoImplicit false

noncomputable section

open Filter Set MeasureTheory UnforcedLeray.Axi
open UnforcedLeray.Blueprint.Planar (PlanarData)

namespace UnforcedLeray.Short.PartIIIb.Concrete

/-- **Separated-kernel estimate, early source (repair source) → scaled repair receiver** (source
5318-5319, 5323-5339: "the general separated kernel bounds ... the repair-to-repair entry uses the
source `L^{22/19}` norm and the `L^{11/3}` kernel"; kernel power `ε^{46/11}` as in
`repair:phase-gradient` 5218-5221; receiver factor `√ρ = ε^{3/22}e^{m₀/(2ν)}` of the scaled repair
receiver, 5336; far mask `s < S`, `t > e^δ s`, `S = ε^{-b}`, 5303-5308, so the young output
`s ≤ 1/ν` and the early source `t < 1.5/ν` are separated by `t > e^δ s` and `S` costs the
polynomial `S^{k₀}`): with the S-degree `k₀` chosen before `D` (before `b`), for large `n` and
`z ∈ [-1,1]`, every stress `T`,
`‖(M_Uχ_yF_far(1-χ_o)(0,T₂))₂‖ ≤ P_νS^{k₀}ε^{95/22}e^{m₀/(2ν)}‖(1-χ_o)(0,T₂)‖_{L²_τL^{22/19}}`
(physical norm with the period `2εc` of `RepairSourceAt`; the output gain `g(s)⁻¹ ≤ 1` on young
output costs nothing). -/
def EarlyRepRepKernel (Pl : PlanarData) (σ₀ mZ dm dp : ℝ) : Prop :=
  ∃ k₀ : ℕ, ∀ D : SeqData, D.Pl = Pl → D.σ₀ = σ₀ → D.K.mZ = mZ →
    ∀ hst : D.RepairStanding dm dp, ∃ (C : ℝ) (k : ℕ), 0 ≤ C ∧
      ∀ᶠ n : ℕ in atTop, ∀ z ∈ Icc (-1 : ℝ) 1, ∀ T : LStr D.Pl D.K (D.level n),
        ENNReal.ofReal ‖repPart (multOp D.Pl D.K (D.level n)
            (earlySrcOp D.Pl D.K (D.level n) (D.mu n z) hst.chiY (repPart T)))‖ ≤
          ENNReal.ofReal (C * (D.level n).ν⁻¹ ^ k * (D.level n).ε ^ (-((k₀ : ℝ) * D.K.b)) *
              (D.level n).ε ^ (95 / 22 : ℝ) * Real.exp (D.K.m0 / 2 / (D.level n).ν)) *
            phaseL2Lr (2 * (D.level n).ε * cOf (D.level n).ν) (22 / 19)
              (ertSrcPhys D.Pl D.K (D.level n) T)

/-- **(L4) from its three ingredients**: the kernel estimate `EarlyRepRepKernel`, the early repair
product estimate `EarlyRepThinProduct` and the gain lemma `earlyRepThinGain` give the table entry
`ε^{79/22}e^{3m₀/(2ν)}e^{3γ/(5ν)}G(w)` (source 5329, 5333-5334, 5338-5339):
`ε^{95/22}ε^{3/11}ε^{-1} = ε^{79/22}`, `e^{m₀/(2ν)}e^{m₀/ν} = e^{3m₀/(2ν)}`. -/
theorem earlyRepRep_of (Pl : PlanarData) (σ₀ mZ dm dp : ℝ)
    (hK : EarlyRepRepKernel Pl σ₀ mZ dm dp) (hP : EarlyRepThinProduct Pl σ₀ mZ dm dp) :
    EarlyRepRep Pl σ₀ mZ dm dp := by
  obtain ⟨k₀, hk⟩ := hK
  refine ⟨k₀, fun D hPl hσ hmZ hst => ?_⟩
  obtain ⟨C1, k1, hC1, h1⟩ := hk D hPl hσ hmZ hst
  obtain ⟨C2, k2, hC2, h2⟩ := hP D hPl hσ hmZ hst
  refine ⟨C1 * C2, k1 + k2, ?_⟩
  filter_upwards [h1, h2] with n hn1 hn2
  intro z hz w
  have hν : 0 < (D.level n).ν := (D.level n).ν_pos
  have hε : 0 < (D.level n).ε := (D.level n).ε_pos
  have hΓ : ∀ t : ℝ, 0 ≤ t → t ≤ 3 / 2 / (D.level n).ν →
      UnforcedLeray.Short.IIIa.gainG (gRate D.Pl) (D.level n).ν t ≤
        Real.exp (3 * gRate D.Pl / 5 / (D.level n).ν) :=
    fun t ht0 ht => earlyRepThinGain hst.gamma_pos.le hν ht0 ht
  have hk1 := hn1 z hz (multOp D.Pl D.K (D.level n) w)
  have hk2 := hn2 _ hΓ w
  have hA : 0 ≤ C1 * (D.level n).ν⁻¹ ^ k1 * (D.level n).ε ^ (-((k₀ : ℝ) * D.K.b)) *
      (D.level n).ε ^ (95 / 22 : ℝ) * Real.exp (D.K.m0 / 2 / (D.level n).ν) := by
    have := hν.le
    positivity
  have hB : 0 ≤ C2 * (D.level n).ν⁻¹ ^ k2 * rhoRep D.K (D.level n) * (D.level n).ε⁻¹ *
      Real.exp (3 * gRate D.Pl / 5 / (D.level n).ν) * ‖w‖ := by
    have := hν.le
    unfold rhoRep
    positivity
  have h3 := hk1.trans (mul_le_mul' le_rfl hk2)
  rw [← ENNReal.ofReal_mul hA, ENNReal.ofReal_le_ofReal_iff (mul_nonneg hA hB)] at h3
  refine le_trans h3 (le_of_eq ?_)
  have e1 : (D.level n).ε ^ (79 / 22 : ℝ) =
      (D.level n).ε ^ (95 / 22 : ℝ) * (D.level n).ε ^ (3 / 11 : ℝ) * (D.level n).ε⁻¹ := by
    rw [← Real.rpow_add hε, ← Real.rpow_neg_one, ← Real.rpow_add hε]
    norm_num
  have e2 : Real.exp (3 * D.K.m0 / 2 / (D.level n).ν) =
      Real.exp (D.K.m0 / 2 / (D.level n).ν) * Real.exp (D.K.m0 / (D.level n).ν) := by
    rw [← Real.exp_add]
    congr 1
    ring
  unfold rhoRep
  rw [pow_add, e1, e2]
  ring

end UnforcedLeray.Short.PartIIIb.Concrete
