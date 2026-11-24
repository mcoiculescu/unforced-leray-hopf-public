import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_4.YRepStream.LateEarly

/-!
# `PartIII-b:C/rep/4/4/1/org/6/org`: late output, repair source -> repair receiver

Source `the November 2 reference manuscript` 5323-5339 (table entry
`ε^{79/22}e^{3m₀/(2ν)}`, common `P_νS^k`, factor `G(w)|N_ν|e^{-4γ/(9ν)}`; "the source `L^{22/19}`
norm and the `L^{11/3}` kernel", 5338-5339), 5303-5308 (late-output part `(1-χ_y)F_far`),
5169-5176 (`repair:source`), 5134-5139 (`ρ = ε^{3/11}e^{m₀/ν}`), 5318 (late gain).

The entry is the product of two source facts.

* `LateSepKernelAt`: the separated-kernel estimate `L^{22/19}_τ → L^{11/3}` for `F_far` on the late
  region with the late gain `g(s)^{-1} ≤ e^{-4γ/(9ν)}` (`lrr_gain_late`), and the conversion
  to the scaled repair receiver (a factor `√ρ = ε^{3/22}e^{m₀/(2ν)}`): kernel power
  `ε^{46/11}` (the order of `repair:phase-gradient`, 5203-5223), receiver `ε^{3/22}`, total
  `ε^{95/22}e^{m₀/(2ν)}`; bounded by the `L²_τL^{22/19}` norm of the repair source stress.
* `RepairProductFull`: `repair:source` (5169-5176) `F_r ≤ P_νρR|N_ν|G(w)`, `R = ε^{-1}`, for the
  repair stress as it enters `F_far(0,(M_Uw)₂)` (the proof of 5176, "`19/22 = 4/11 + 1/2` and
  `g ≤ e^{γ/ν}`", does not use the cutoff `χ_o`).

Then `ε^{95/22}·ε^{-1}·ε^{3/11} = ε^{79/22}` and `e^{m₀/(2ν)}e^{m₀/ν} = e^{3m₀/(2ν)}`
(`lateRepRepAt_of`, `lateRepRep_of`).
-/

set_option autoImplicit false

noncomputable section

open Filter Set MeasureTheory UnforcedLeray.Axi
open UnforcedLeray.Blueprint.Planar (PlanarData)
open scoped ENNReal

namespace UnforcedLeray.Short.PartIIIb.Concrete

/-- **Late gain** `g(s)^{-1} ≤ e^{-4γ/(9ν)}` for `s ≥ 0.8/ν` (source 5318; `g(s) = e^{γs/(1+νs)}`,
3881, 5117). -/
theorem lrr_gain_late {γ ν s : ℝ} (hγ : 0 ≤ γ) (hν : 0 < ν) (hs : 4 / 5 / ν ≤ s) :
    (UnforcedLeray.Short.IIIa.gainG γ ν s)⁻¹ ≤ Real.exp (-(4 * γ / 9) / ν) := by
  unfold UnforcedLeray.Short.IIIa.gainG
  have hνs : 4 / 5 ≤ s * ν := (div_le_iff₀ hν).1 hs
  have hs0 : 0 < s := by
    have : 0 < s * ν := by linarith
    exact pos_of_mul_pos_left this hν.le
  have h1 : 0 < 1 + ν * s := by positivity
  rw [← Real.exp_neg, Real.exp_le_exp, neg_div, neg_le_neg_iff, div_le_div_iff₀ hν h1]
  nlinarith [mul_nonneg hγ (sub_nonneg.2 hνs)]

/-- The (unlocalised) physical repair stress `r_b ⊗ w + w ⊗ r_b` entering `F_far(0,(M_Uw)₂)`:
the lift of the repair part of `M_Uw` (compare `repStressPhys`, which carries `χ_o`). -/
def repStressFull (Pl : PlanarData) (K : ReturnConsts) (L : ReturnLevel) (w : LVel Pl L) :
    ℝ × Space → Matrix (Fin 3) (Fin 3) ℝ :=
  strPhys L.ε⁻¹ (cOf L.ν) ((repPart (multOp Pl K L w)).snd : Chart → Ten3)

namespace SeqData

variable (D : SeqData)

/-- **Separated kernel, late output, repair source -> repair receiver** (source 5323-5339, 5318):
with `P_ν = Cν^{-k}`, `S^{k₀} = ε^{-k₀b}`,
`‖(M_U(1-χ_y)F_far(0,(M_Uw)₂))₂‖ ≤ P_νS^{k₀}ε^{95/22}e^{m₀/(2ν)}e^{-4γ/(9ν)}F_r`,
`F_r = ‖r_b⊗w+w⊗r_b‖_{L²_τL^{22/19}}` (period `2εc`): kernel `L^{22/19} → L^{11/3}` with
power `ε^{46/11}`, late gain `g(s)^{-1} ≤ e^{-4γ/(9ν)}`, receiver factor `√ρ`. -/
def LateSepKernelAt (hχ : IsStreamCutoff D.K.χy) (k₀ : ℕ) : Prop :=
  ∃ (C : ℝ) (k : ℕ), 0 ≤ C ∧ ∀ᶠ n : ℕ in atTop, ∀ z ∈ Icc (-1 : ℝ) 1,
    ∀ w : LVel D.Pl (D.level n),
      ENNReal.ofReal ‖repPart (multOp D.Pl D.K (D.level n)
          (lateOutOp D.Pl D.K (D.level n) (D.mu n z) hχ
            (repPart (multOp D.Pl D.K (D.level n) w))))‖ ≤
        ENNReal.ofReal (C * (D.level n).ν⁻¹ ^ k * (D.level n).ε ^ (-((k₀ : ℝ) * D.K.b)) *
          (D.level n).ε ^ (95 / 22 : ℝ) * Real.exp (D.K.m0 / 2 / (D.level n).ν) *
          Real.exp (-(4 * gRate D.Pl / 9) / (D.level n).ν)) *
        phaseL2Lr (2 * (D.level n).ε * cOf (D.level n).ν) (22 / 19)
          (repStressFull D.Pl D.K (D.level n) w)

/-- **`repair:source` for the repair stress as it enters `F_far`** (source 5169-5176):
`F_r ≤ P_νρR|N_ν|G(w)`, `ρ = ε^{3/11}e^{m₀/ν}`, `R = ε^{-1}`. -/
def RepairProductFull : Prop :=
  ∃ (C : ℝ) (k : ℕ), ∀ᶠ n : ℕ in atTop, ∀ w : LVel D.Pl (D.level n),
    phaseL2Lr (2 * (D.level n).ε * cOf (D.level n).ν) (22 / 19)
        (repStressFull D.Pl D.K (D.level n) w) ≤
      ENNReal.ofReal (C * (D.level n).ν⁻¹ ^ k * rhoRep D.K (D.level n) * (D.level n).ε⁻¹ *
        gaugeN D.Pl (D.level n) * ‖w‖)

/-- **The entry from the two source facts**: `ε^{95/22}ε^{-1}ε^{3/11} = ε^{79/22}`,
`e^{m₀/(2ν)}e^{m₀/ν} = e^{3m₀/(2ν)}`. -/
theorem lateRepRepAt_of (hχ : IsStreamCutoff D.K.χy) (k₀ : ℕ)
    (h1 : D.LateSepKernelAt hχ k₀) (h2 : D.RepairProductFull) : D.LateRepRepAt hχ k₀ := by
  obtain ⟨C1, k1, hC1, e1⟩ := h1
  obtain ⟨C2, k2, e2⟩ := h2
  refine ⟨C1 * max C2 0, k1 + k2, ?_⟩
  filter_upwards [e1, e2] with n a b
  intro z hz w
  have hε : 0 < (D.level n).ε := (D.level n).ε_pos
  have hν : 0 < (D.level n).ν := (D.level n).ν_pos
  have hν' : 0 ≤ (D.level n).ν⁻¹ := inv_nonneg.2 hν.le
  have hN : 0 ≤ gaugeN D.Pl (D.level n) := norm_nonneg _
  have hρ : 0 ≤ rhoRep D.K (D.level n) := by
    unfold rhoRep; positivity
  have hA : 0 ≤ C1 * (D.level n).ν⁻¹ ^ k1 * (D.level n).ε ^ (-((k₀ : ℝ) * D.K.b)) * (D.level n).ε ^ (95 / 22 : ℝ) *
      Real.exp (D.K.m0 / 2 / (D.level n).ν) * Real.exp (-(4 * gRate D.Pl / 9) / (D.level n).ν) := by positivity
  have hB : 0 ≤ max C2 0 * (D.level n).ν⁻¹ ^ k2 * rhoRep D.K (D.level n) * (D.level n).ε⁻¹ *
      gaugeN D.Pl (D.level n) * ‖w‖ := by positivity
  have hB' : 0 ≤ (D.level n).ν⁻¹ ^ k2 * rhoRep D.K (D.level n) * (D.level n).ε⁻¹ *
      gaugeN D.Pl (D.level n) * ‖w‖ := by positivity
  have c2 : C2 * (D.level n).ν⁻¹ ^ k2 * rhoRep D.K (D.level n) * (D.level n).ε⁻¹ * gaugeN D.Pl (D.level n) * ‖w‖ ≤
      max C2 0 * (D.level n).ν⁻¹ ^ k2 * rhoRep D.K (D.level n) * (D.level n).ε⁻¹ * gaugeN D.Pl (D.level n) * ‖w‖ := by
    have : 0 ≤ (D.level n).ν⁻¹ ^ k2 * rhoRep D.K (D.level n) * (D.level n).ε⁻¹ * gaugeN D.Pl (D.level n) * ‖w‖ := hB'
    nlinarith [le_max_left C2 0]
  have c1 := (a z hz w).trans (mul_le_mul' le_rfl ((b w).trans (ENNReal.ofReal_le_ofReal c2)))
  rw [← ENNReal.ofReal_mul hA, ENNReal.ofReal_le_ofReal_iff (by positivity)] at c1
  have eq1 : (D.level n).ε ^ (95 / 22 : ℝ) * (D.level n).ε⁻¹ * (D.level n).ε ^ (3 / 11 : ℝ) = (D.level n).ε ^ (79 / 22 : ℝ) := by
    rw [← Real.rpow_neg_one, ← Real.rpow_add hε, ← Real.rpow_add hε]; norm_num
  have eq2 : Real.exp (D.K.m0 / 2 / (D.level n).ν) * Real.exp (D.K.m0 / (D.level n).ν) =
      Real.exp (3 * D.K.m0 / 2 / (D.level n).ν) := by
    rw [← Real.exp_add]; congr 1; ring
  have eq3 : (D.level n).ν⁻¹ ^ (k1 + k2) = (D.level n).ν⁻¹ ^ k1 * (D.level n).ν⁻¹ ^ k2 := pow_add _ _ _
  refine c1.trans_eq ?_
  unfold rhoRep
  rw [eq3]
  have e1' : (D.level n).ε ^ (79 / 22 : ℝ) = (D.level n).ε ^ (95 / 22 : ℝ) * (D.level n).ε⁻¹ * (D.level n).ε ^ (3 / 11 : ℝ) := eq1.symm
  have e2' : Real.exp (3 * D.K.m0 / 2 / (D.level n).ν) =
      Real.exp (D.K.m0 / 2 / (D.level n).ν) * Real.exp (D.K.m0 / (D.level n).ν) := eq2.symm
  rw [e1', e2']
  ring

end SeqData

/-- (L2a) The separated-kernel estimate, with `k₀` chosen from `Pl, σ₀, mZ, dm, dp` before `b`
(source 5323-5339, 5607). -/
def LateSepKernel (Pl : PlanarData) (σ₀ mZ dm dp : ℝ) : Prop :=
  ∃ k₀ : ℕ, ∀ D : SeqData, D.Pl = Pl → D.σ₀ = σ₀ → D.K.mZ = mZ →
    ∀ hst : D.RepairStanding dm dp, D.LateSepKernelAt hst.chiY k₀

/-- (L2b) The repair product estimate for every standing sequence (source 5169-5176). -/
def RepairProductAll (dm dp : ℝ) : Prop :=
  ∀ D : SeqData, D.RepairStanding dm dp → D.RepairProductFull

/-- **`LateRepRep` from the separated kernel and the repair product estimate.** -/
theorem lateRepRep_of (Pl : PlanarData) (σ₀ mZ dm dp : ℝ)
    (h1 : LateSepKernel Pl σ₀ mZ dm dp) (h2 : RepairProductAll dm dp) :
    LateRepRep Pl σ₀ mZ dm dp := by
  obtain ⟨k₀, hk⟩ := h1
  exact ⟨k₀, fun D hP hσ hZ hst => D.lateRepRepAt_of hst.chiY k₀ (hk D hP hσ hZ hst) (h2 D hst)⟩

end UnforcedLeray.Short.PartIIIb.Concrete
