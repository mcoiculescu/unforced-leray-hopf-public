import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_4.YRepStream.LateEarly

/-!
# `PartIII-b:C/rep/4/4/1/org/7` (L3), Props file: early source, repair source → thin receiver

Source `the November 2 reference manuscript` 5318-5319 (gain `g(t) ≤ e^{3γ/(5ν)}`
on early sources), 5323-5339 (table entry `ε^{63/22}e^{m₀/ν}`, factor `G(w)e^{3γ/(5ν)}`;
"the repair-to-thin entry uses the pointwise exponent `79/22`, followed by `ρR`"), 5303-5308
(the early-source part `χ_yF_far(1-χ_o)`), 5169-5176 (`repair:source`), 5134-5139 (`ρ`).

The entry is the product of

* the **separated-kernel estimate** `EarlyRepThinKernel`: the early-source far operator maps the
  physical early repair stress in `L²_τL^{22/19}` to the thin receiver with the weakest curvature
  power `ε^{79/22}` and the loss `P_νS^{k₀}`, `S = ε^{-b}` (5337-5338);
* the **repair product estimate** `EarlyRepThinProduct` (5169-5176, the early analogue of
  `RepairSourceAt`): the early repair source is `≤ P_νρR Γ G(w)` where `Γ` bounds the gain `g(t)`
  on the early support `0 ≤ t ≤ 1.5/ν`;
* the **gain lemma** `earlyRepThinGain`: `g(t) ≤ e^{3γ/(5ν)}` on `0 ≤ t ≤ 1.5/ν` (5318-5319).
-/

set_option autoImplicit false

noncomputable section

open Filter Set MeasureTheory UnforcedLeray.Axi
open UnforcedLeray.Blueprint.Planar (PlanarData)

namespace UnforcedLeray.Short.PartIIIb.Concrete

/-- **The physical early repair stress** `(1-χ_o)(0,T₂)` as a physical tensor field with the
scaling `R = ε⁻¹` (the lift `𝒩_T` of the early source, source 5303-5308, 5153-5157; the early
analogue of `repStressPhys`, which carries `χ_o`). -/
def ertSrcPhys (Pl : PlanarData) (K : ReturnConsts) (L : ReturnLevel) (T : LStr Pl K L) :
    ℝ × Space → Matrix (Fin 3) (Fin 3) ℝ :=
  strPhys L.ε⁻¹ (cOf L.ν)
    ((T - chiOStr (cOf L.ν) K.mZ (L.ρb Pl K) (gRate Pl) L.ν K.hχo T).snd : Chart → Ten3)

/-- **Separated-kernel estimate, early source (repair source) → thin receiver** (source 5318-5319,
5323-5339: "the general separated kernel bounds ... the repair-to-thin entry uses the pointwise
exponent `79/22`"; far mask `s < S`, `t > e^δ s`, `S = ε^{-b}`, 5303-5308, SP separated kernels
`IIIa.SepKernelBounds`, `IIIa.SepRepair`): with the S-degree `k₀` chosen before `D` (before `b`),
for large `n` and `z ∈ [-1,1]`, every stress `T`,
`‖(M_Uχ_yF_far(1-χ_o)(0,T₂))₁‖ ≤ P_νS^{k₀}ε^{79/22}‖(1-χ_o)(0,T₂)‖_{L²_τL^{22/19}}`
(physical norm with the period `2εc` of `RepairSourceAt`; the output gain `g(s)⁻¹ ≤ 1` on young
output costs nothing). -/
def EarlyRepThinKernel (Pl : PlanarData) (σ₀ mZ dm dp : ℝ) : Prop :=
  ∃ k₀ : ℕ, ∀ D : SeqData, D.Pl = Pl → D.σ₀ = σ₀ → D.K.mZ = mZ →
    ∀ hst : D.RepairStanding dm dp, ∃ (C : ℝ) (k : ℕ), 0 ≤ C ∧
      ∀ᶠ n : ℕ in atTop, ∀ z ∈ Icc (-1 : ℝ) 1, ∀ T : LStr D.Pl D.K (D.level n),
        ENNReal.ofReal ‖thinPart (multOp D.Pl D.K (D.level n)
            (earlySrcOp D.Pl D.K (D.level n) (D.mu n z) hst.chiY (repPart T)))‖ ≤
          ENNReal.ofReal (C * (D.level n).ν⁻¹ ^ k * (D.level n).ε ^ (-((k₀ : ℝ) * D.K.b)) *
              (D.level n).ε ^ (79 / 22 : ℝ)) *
            phaseL2Lr (2 * (D.level n).ε * cOf (D.level n).ν) (22 / 19)
              (ertSrcPhys D.Pl D.K (D.level n) T)

/-- **Repair product estimate, early source** (source 5169-5176 `repair:source`, "follows from
`19/22 = 4/11 + 1/2` and `g ≤ e^{γ/ν}`", with the gain on the early support `0 ≤ t ≤ 1.5/ν`
(`1-χ_o` vanishes for ages `≥ 1.5/ν`) in place of `e^{γ/ν}`; 5134-5139 `ρ = ε^{3/11}e^{m₀/ν}`):
if `g(t) ≤ Γ` for `0 ≤ t ≤ 1.5/ν`, then
`‖(1-χ_o)(r_b⊗w+w⊗r_b)‖_{L²_τL^{22/19}} ≤ P_νρRΓG(w)`, `G(w) = ‖w‖`, `R = ε⁻¹`. -/
def EarlyRepThinProduct (Pl : PlanarData) (_σ₀ _mZ dm dp : ℝ) : Prop :=
  ∀ D : SeqData, D.Pl = Pl → D.σ₀ = _σ₀ → D.K.mZ = _mZ →
    ∀ _hst : D.RepairStanding dm dp, ∃ (C : ℝ) (k : ℕ), 0 ≤ C ∧ ∀ᶠ n : ℕ in atTop,
      ∀ Γ : ℝ, (∀ t : ℝ, 0 ≤ t → t ≤ 3 / 2 / (D.level n).ν →
          UnforcedLeray.Short.IIIa.gainG (gRate D.Pl) (D.level n).ν t ≤ Γ) →
        ∀ w : LVel D.Pl (D.level n),
          phaseL2Lr (2 * (D.level n).ε * cOf (D.level n).ν) (22 / 19)
              (ertSrcPhys D.Pl D.K (D.level n) (multOp D.Pl D.K (D.level n) w)) ≤
            ENNReal.ofReal (C * (D.level n).ν⁻¹ ^ k * rhoRep D.K (D.level n) *
              (D.level n).ε⁻¹ * Γ * ‖w‖)

/-- **Early source**: `g(t) ≤ e^{3γ/(5ν)}` for `0 ≤ t ≤ 1.5/ν` (source 5318-5319;
`g(t) = e^{γt/(1+νt)}`). -/
theorem earlyRepThinGain {γ ν t : ℝ} (hγ : 0 ≤ γ) (hν : 0 < ν) (ht0 : 0 ≤ t)
    (ht : t ≤ 3 / 2 / ν) :
    UnforcedLeray.Short.IIIa.gainG γ ν t ≤ Real.exp (3 * γ / 5 / ν) := by
  unfold UnforcedLeray.Short.IIIa.gainG
  have htν : t * ν ≤ 3 / 2 := (le_div_iff₀ hν).1 ht
  have h1 : 0 < 1 + ν * t := by positivity
  rw [Real.exp_le_exp, div_le_div_iff₀ h1 hν]
  nlinarith [mul_nonneg hγ (sub_nonneg.2 htν)]

/-- **(L3) from its three ingredients**: kernel estimate, repair product estimate and the gain
lemma give the table entry `ε^{63/22}e^{m₀/ν}e^{3γ/(5ν)}G(w)` (source 5328, 5333-5334,
5337-5338). -/
theorem earlyRepThin_of (Pl : PlanarData) (σ₀ mZ dm dp : ℝ)
    (hK : EarlyRepThinKernel Pl σ₀ mZ dm dp) (hP : EarlyRepThinProduct Pl σ₀ mZ dm dp) :
    EarlyRepThin Pl σ₀ mZ dm dp := by
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
      UnforcedLeray.Short.IIIa.gainG (gRate D.Pl) (D.level n).ν t ≤ Real.exp (3 * gRate D.Pl / 5 / (D.level n).ν) :=
    fun t ht0 ht => earlyRepThinGain hst.gamma_pos.le hν ht0 ht
  have hk1 := hn1 z hz (multOp D.Pl D.K (D.level n) w)
  have hk2 := hn2 _ hΓ w
  have hA : 0 ≤ C1 * (D.level n).ν⁻¹ ^ k1 * (D.level n).ε ^ (-((k₀ : ℝ) * D.K.b)) * (D.level n).ε ^ (79 / 22 : ℝ) := by
    have := hν.le
    positivity
  have hB : 0 ≤ C2 * (D.level n).ν⁻¹ ^ k2 * rhoRep D.K (D.level n) * (D.level n).ε⁻¹ * Real.exp (3 * gRate D.Pl / 5 / (D.level n).ν) *
      ‖w‖ := by
    have := hν.le
    unfold rhoRep
    positivity
  have h3 := hk1.trans (mul_le_mul' le_rfl hk2)
  rw [← ENNReal.ofReal_mul hA, ENNReal.ofReal_le_ofReal_iff (mul_nonneg hA hB)] at h3
  refine le_trans h3 ?_
  apply le_of_eq
  have e : (D.level n).ε ^ (79 / 22 : ℝ) * (D.level n).ε ^ (3 / 11 : ℝ) * (D.level n).ε⁻¹ = (D.level n).ε ^ (63 / 22 : ℝ) := by
    rw [← Real.rpow_add hε, ← Real.rpow_neg_one, ← Real.rpow_add hε]
    norm_num
  simp only [rhoRep, pow_add]
  linear_combination (C1 * C2 * (D.level n).ν⁻¹ ^ k1 * (D.level n).ν⁻¹ ^ k2 * (D.level n).ε ^ (-((k₀ : ℝ) * D.K.b)) *
    Real.exp (D.K.m0 / (D.level n).ν) * Real.exp (3 * gRate D.Pl / 5 / (D.level n).ν) * ‖w‖) * e

end UnforcedLeray.Short.PartIIIb.Concrete
