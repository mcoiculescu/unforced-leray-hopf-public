import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_8_1.GeomY.Pieces
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_4.Org.YThinTrans.ShiftedResolvent

/-!
# `PartIII-b:C/rep/8/1/1/2/1` (`geomY`): the exact formula for `Y₁` from the shifted resolvent

Source `shorter-proof-2026-11-02.tex` 4171-4215 (`ward:cutoff-source`) and 5427-5432.

Reduction: `Y₁ = D_{μ+1}𝒞_yX₀` and `𝒞_yW_μ + [D_{μ+1},𝒞_y]X₀ = 𝒞_yW_μ + D_{μ+1}𝒞_yX₀ - 𝒞_y(D_{μ+1}X₀)`,
so the formula is equivalent to `𝒞_y(D_{μ+1}X₀) = 𝒞_yW_μ` at every receiver with `ϱ y > 0`.  The cut at
`y` depends only on the value at `y` and on the outward ray through `y`; the ray stays in the young
region `ν·age ≤ 1`, where the shifted resolvent holds pointwise, and on the old region the stream
cutoff and its derivative vanish identically, so both sides are zero.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology UnforcedLeray.Axi

namespace UnforcedLeray.Short.PartIIIb.Concrete

open UnforcedLeray.Blueprint.Planar (PlanarData)

theorem ay_varrho_pt {ρ : ℝ} (z : ℝ) (hρ : 0 < ρ) : ϱ (!₂[ρ, 0, z] : Space) = ρ := by
  unfold ϱ
  have e : (!₂[ρ, 0, z] : Space) 0 ^ 2 + (!₂[ρ, 0, z] : Space) 1 ^ 2 = ρ ^ 2 := by simp
  rw [e]
  exact Real.sqrt_sq hρ.le

theorem ay_age_le {ν R : ℝ} (hν : 0 ≤ ν) {y : Space} (hy : 0 < ϱ y) {ρ z : ℝ} (hρ : ϱ y < ρ)
    (h : ν * age R y ≤ 1) : ν * age R (!₂[ρ, 0, z] : Space) ≤ 1 := by
  have hρ0 : 0 < ρ := hy.trans hρ
  have e : age R (!₂[ρ, 0, z] : Space) = R ^ 2 / ρ ^ 2 := by
    unfold age
    rw [ay_varrho_pt z hρ0]
  have h2 : 0 < ϱ y ^ 2 := pow_pos hy 2
  have hle : R ^ 2 / ρ ^ 2 ≤ age R y := by
    unfold age
    have hsq : ϱ y ^ 2 ≤ ρ ^ 2 := pow_le_pow_left₀ hy.le hρ.le 2
    gcongr
  rw [e]
  exact le_trans (mul_le_mul_of_nonneg_left hle hν) h

theorem ay_outPrim_congr (Z Z' : ℝ → Space → Space) (τ r z : ℝ)
    (h : ∀ ρ : ℝ, r < ρ → Z τ (!₂[ρ, 0, z] : Space) = Z' τ (!₂[ρ, 0, z] : Space)) :
    outPrim Z τ r z = outPrim Z' τ r z := by
  unfold outPrim
  congr 1
  refine setIntegral_congr_fun measurableSet_Ioi (fun ρ hρ => ?_)
  show ρ * Z τ (!₂[ρ, 0, z] : Space) 2 = ρ * Z' τ (!₂[ρ, 0, z] : Space) 2
  rw [h ρ hρ]

theorem ay_cut_congr (ν R : ℝ) (χy : ℝ → ℝ) (Z Z' : ℝ → Space → Space) (τ : ℝ) (y : Space)
    (hv : Z τ y = Z' τ y) (hp : outPrim Z τ (ϱ y) (y 2) = outPrim Z' τ (ϱ y) (y 2)) :
    wardStreamCut ν R χy Z τ y = wardStreamCut ν R χy Z' τ y := by
  unfold wardStreamCut
  rw [hv, hp]

/-- The stream cut vanishes on the old region `ν·age > 1` for every field, since `χ_y = 0` on
`[1,∞)` and so is its derivative on the open set `(1,∞)`. -/
theorem ay_cut_old (ν R : ℝ) (χy : ℝ → ℝ) (hχ : IsStreamCutoff χy) (Z : ℝ → Space → Space)
    (τ : ℝ) (y : Space) (h : 1 < ν * age R y) : wardStreamCut ν R χy Z τ y = 0 := by
  have hz : χy (ν * age R y) = 0 := hχ.zero _ h.le
  have hev : χy =ᶠ[𝓝 (ν * age R y)] fun _ => (0 : ℝ) :=
    Filter.eventually_of_mem (Ioi_mem_nhds h) (fun s hs => hχ.zero s (le_of_lt hs))
  have hd : deriv χy (ν * age R y) = 0 := by
    rw [hev.deriv_eq]
    simp
  unfold wardStreamCut
  rw [hz, hd]
  simp

/-- **The exact formula for `Y₁` from the pointwise shifted resolvent** (source 4171-4201, 5427-5432),
for a given family of shifted-resolvent identities `hSR` on the young region.  The target
`ActYFormulaAt` follows once `hSR` is supplied at the level (see the report). -/
theorem actYFormulaAt_of (Pl : PlanarData) (K : ReturnConsts) (L : ReturnLevel) (μ : ℝ)
    (hχ : IsStreamCutoff K.χy)
    (hSR : ∀ T : LStr Pl K L, ∀ (τ : ℝ) (y : Space), 0 < ϱ y → L.ν * age L.ε⁻¹ y ≤ 1 →
      physDmu L.ν (μ + 1) (zAct0 Pl K L μ T) τ y = thinWardW Pl K L μ T τ y) :
    ActYFormulaAt Pl K L μ := by
  unfold ActYFormulaAt
  intro T
  refine Filter.Eventually.of_forall (fun τ y hy => ?_)
  have key : wardStreamCut L.ν L.ε⁻¹ K.χy (physDmu L.ν (μ + 1) (zAct0 Pl K L μ T)) τ y =
      wardStreamCut L.ν L.ε⁻¹ K.χy (thinWardW Pl K L μ T) τ y := by
    by_cases hle : L.ν * age L.ε⁻¹ y ≤ 1
    · refine ay_cut_congr _ _ _ _ _ _ _ (hSR T τ y hy hle) (ay_outPrim_congr _ _ _ _ _ ?_)
      intro ρ hρ
      exact hSR T τ _ (by rw [ay_varrho_pt _ (hy.trans hρ)]; exact hy.trans hρ)
        (ay_age_le L.ν_pos.le hy hρ hle)
    · rw [ay_cut_old _ _ _ hχ _ _ _ (lt_of_not_ge hle), ay_cut_old _ _ _ hχ _ _ _ (lt_of_not_ge hle)]
  show physDmu L.ν (μ + 1) (wardStreamCut L.ν L.ε⁻¹ K.χy (zAct0 Pl K L μ T)) τ y = _
  unfold actYA actYB
  rw [key]
  abel

/-- **`PartIII-b:C/rep/8/1/1/2/1`**: the exact formula for `Y₁` (source 4171-4215, 5427-5432),
from `shiftedResolventThin` and `actYFormulaAt_of`. -/
theorem actYFormula (D : SeqData) {dm dp : ℝ} (hst : D.RepairStanding dm dp) : D.ActYFormula := by
  unfold SeqData.ActYFormula
  filter_upwards [shiftedResolventThin dm dp D hst] with n hn
  intro z hz
  refine actYFormulaAt_of D.Pl D.K (D.level n) (D.mu n z) hst.chiY ?_
  intro T τ y hy hage
  exact hn z hz T (thinG D.Pl D.K (D.level n) T |> fun _ => ((chiOStr (cOf (D.level n).ν) D.K.mZ
      ((D.level n).ρb D.Pl D.K) (gRate D.Pl) (D.level n).ν D.K.hχo (thinPart T)).fst : Chart → Ten3))
    ((chiOStr (cOf (D.level n).ν) D.K.mZ ((D.level n).ρb D.Pl D.K) (gRate D.Pl) (D.level n).ν
      D.K.hχo (thinPart T)).snd : Chart → Ten3)
    ⟨Filter.EventuallyEq.rfl, Filter.EventuallyEq.rfl⟩ τ y hy hage

end UnforcedLeray.Short.PartIIIb.Concrete
