import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Continuity.Defs
import UnforcedLeray.Short.PartIIIb.Concrete.SourceL.AMuInAff
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnInst.AsymMu

/-!
# The leaf `AMuCont`: `a_μ` is continuous in `μ` (source 4807-4811)

Source of record: `the November 2 reference manuscript` (73 pages).

`a_μ(s) = s^{5/2}D₀/(μ+5/2)` (source 4807-4811, `aMuFun`), so `a_μ = ((μ₀+5/2)/(μ+5/2)) a_{μ₀}`
pointwise; `a_μ ∈ 𝒜` for `μ > 0` (`aMuInAff`), and `aMuOp K μ` is the element of `𝒜` with
`ι(aMuOp K μ) = a_μ` (`ι = affIota` injective).  Hence `aMuOp K μ = ((1+5/2)/(μ+5/2)) aMuOp K 1`
for `μ > 0`, continuous on `(0, ∞)`, which contains the window `μ_n([-1,1])` for large `n`
(`mu_eventually_mem`, `0 < σ₀ < 1/4`).
-/

set_option autoImplicit false

noncomputable section

open Set Filter Topology

namespace UnforcedLeray.Short.PartIIIb.Concrete

/-- `a_μ = ((μ₀+5/2)/(μ+5/2)) a_{μ₀}` (source 4807-4811). -/
theorem aMuFun_eq_smul {μ μ₀ : ℝ} (hμ : μ + 5 / 2 ≠ 0) (hμ₀ : μ₀ + 5 / 2 ≠ 0) :
    aMuFun μ = ((μ₀ + 5 / 2) / (μ + 5 / 2)) • aMuFun μ₀ := by
  funext s
  unfold aMuFun
  by_cases hs : 0 < s
  · simp only [hs, ite_true, Pi.smul_apply, smul_smul]
    congr 1
    rw [div_mul_div_comm, mul_comm (μ₀ + 5 / 2), mul_div_mul_right _ _ hμ₀]
  · simp only [hs, ite_false, Pi.smul_apply, smul_zero]

/-- The pinned `a_μ` is `a_μ` (source 4807-4811) for `μ > 0`, `a_s ≥ 0`. -/
theorem affIota_aMuOp {K : ReturnConsts} {μ : ℝ} (has : 0 ≤ K.as) (hμ : 0 < μ) :
    affIota K.as (aMuOp K μ) = aMuFun μ :=
  Classical.epsilon_spec (exists_aMuOp_of (aMuInAff K.as μ) has hμ)

theorem aMuOp_eq_smul {K : ReturnConsts} {μ : ℝ} (has : 0 ≤ K.as) (hμ : 0 < μ) :
    aMuOp K μ = ((1 + 5 / 2) / (μ + 5 / 2)) • aMuOp K 1 := by
  apply affIota_injective
  rw [map_smul, affIota_aMuOp has hμ, affIota_aMuOp has one_pos]
  exact aMuFun_eq_smul (by linarith) (by norm_num)

/-- `μ ↦ a_μ ∈ 𝒜` is continuous on `(0, ∞)`. -/
theorem aMuOp_continuousOn (K : ReturnConsts) (has : 0 ≤ K.as) :
    ContinuousOn (fun μ => aMuOp K μ) (Ioi 0) := by
  have hc : ContinuousOn (fun μ : ℝ => (1 + 5 / 2 : ℝ) / (μ + 5 / 2)) (Ioi 0) :=
    continuousOn_const.div (continuousOn_id.add continuousOn_const) fun μ hμ => by
      have : (0 : ℝ) < μ := hμ
      exact ne_of_gt (by linarith)
  have h : ContinuousOn (fun μ : ℝ => ((1 + 5 / 2 : ℝ) / (μ + 5 / 2)) • aMuOp K 1) (Ioi 0) :=
    hc.smul continuousOn_const
  exact h.congr fun μ hμ => aMuOp_eq_smul has hμ

/-- **`AMuCont`** on the concrete sequence (source 4807-4811, 5944-5947). -/
theorem SeqData.aMuCont (D : SeqData) {dm dp : ℝ} (hst : D.RepairStanding dm dp) :
    D.AMuCont := by
  filter_upwards [mu_eventually_mem D hst.omega_ne hst.sigma_pos hst.sigma_lt] with n hn
  refine (aMuOp_continuousOn D.K hst.as_pos.le).mono ?_
  rintro _ ⟨z, hz, rfl⟩
  have h1 := (hn z hz).1
  have h0 : (0 : ℝ) < D.σ₀ / 2 := by linarith [hst.sigma_pos]
  exact lt_of_lt_of_le h0 h1

end UnforcedLeray.Short.PartIIIb.Concrete
