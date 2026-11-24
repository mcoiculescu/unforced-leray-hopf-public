import UnforcedLeray.Short.PartIIb.Sub.PartIIb_T10_7_1_1_avg

/-!
# `PartII-b:T10/7/1/1/3` (`GLBuild`): decomposition

Source of record: `the November 2 reference manuscript` lines 1639-1668 (chart
`(s, q, η) = (R²/ϱ², Rτ/2 - (R/2) log s, R z/ϱ)`), 1912-1921.

Mathematics.  (i) The real/imaginary parts of `radComb g` and `g 2` are `𝒪`-equivariant, hence a.e.
`A_r(τ,ϱ,z) e_r + A_z(τ,ϱ,z) e_3` (`glAvgLift`), with measurable `A`, and `A` can be taken
everywhere `2εc`-periodic in `τ` (`GLProfFns`).  (ii) The inverse chart
`(s,q,η) ↦ (τ,ϱ,z) = (2εq + log s, ε⁻¹ s^{-1/2}, η s^{-1/2})` (`ε = 1/R`) turns `(A_r, A_z)` into the
profile `Qb(s,q,η) = s⁻¹ (A_r, A_z)(τ,ϱ,z)` (`chartProf`) with `NvC ε⁻¹ (sqrtS Qb) = A_r e_r + A_z e_3`
off the axis, `q`-periodic with period `c` since `τ(q + c) = τ + 2εc`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.IIb

open UnforcedLeray.PhaseSpace UnforcedLeray.Cons.C03.Concrete

/-- The inverse chart `(s, q, η) ↦ (τ, ϱ, z)` of `Axi.chart ε⁻¹` (valid for `s > 0`):
`ϱ = ε⁻¹ s^{-1/2}`, `τ = 2 ε q + log s`, `z = η s^{-1/2}`. -/
def invChart (ε : ℝ) (x : Coord) : ℝ × (ℝ × ℝ) :=
  (2 * ε * x.2.1 + Real.log x.1, (ε⁻¹ * (Real.sqrt x.1)⁻¹, x.2.2 * (Real.sqrt x.1)⁻¹))

/-- The profile `Qb(s,q,η) = s⁻¹ (A, B)(invChart ε (s,q,η))` for `s > 0` (and `0` for `s ≤ 0`). -/
def chartProf (ε : ℝ) (A B : ℝ × (ℝ × ℝ) → ℂ) : CProf := fun x =>
  if 0 < x.1 then
    ((x.1)⁻¹ : ℂ) • (!₂[A (invChart ε x), B (invChart ε x)] : CMerid)
  else 0

/-- **(P_A)** The measurable profile functions of one real equivariant field (SP 1912-1921):
`W` a.e.-measurable and `𝒪`-equivariant is a.e. `A(τ, mer y) e_r(y) + B(τ, mer y) e_3` with
measurable `A, B : ℝ × (ℝ × ℝ) → ℝ`.  Take a measurable representative `W' = hW.mk`, transfer
`GLEquivar` to it (rotations/reflection are measure preserving, so quasi-measure-preserving),
apply `glAvgLift` (`Sub/PartII-b_T10_7_1_1_avg.lean`) and take `A = avgR W'`, `B = avgZ W'`
(measurable by `Axi.measurable_avgR`-type lemmas of `Lib/AxisymmetricB/Average.lean`). -/
def GLAvgRep : Prop :=
  ∀ W : ℝ × Space → Space, AEStronglyMeasurable W volume → GLEquivar W →
    ∃ A B : ℝ × (ℝ × ℝ) → ℝ, Measurable A ∧ Measurable B ∧
      ∀ᵐ x : ℝ × Space ∂volume,
        W x = A (x.1, Axi.mer x.2) • Axi.eR x.2 + B (x.1, Axi.mer x.2) • Axi.e3

/-- **(P_B)** Periodic representative of profile functions: if `W` is a.e. `P`-periodic in `τ`
and is a.e. `A e_r + B e_3` with measurable `A, B`, then `A, B` can be replaced by measurable
everywhere-`P`-periodic `A', B'` with the same property.  (Components: `A(τ+P, mer y) = ⟨W(τ+P,y), e_r⟩
= ⟨W(τ,y), e_r⟩ = A(τ, mer y)` a.e. in `x`; the map `x ↦ (τ, mer y)` pulls back null sets and its
pushforward of Lebesgue is equivalent to Lebesgue on `ℝ × (0,∞) × ℝ` (weight `ϱ`), so the
`P`-periodicity of `A` holds a.e. in `(τ,ϱ,z)`; then set `A'(τ, p) = A(toIcoMod hP 0 τ, p)` and
use the countable family of shifts `k P`.) -/
def GLProfPeriodic : Prop :=
  ∀ (P : ℝ) (W : ℝ × Space → Space) (A B : ℝ × (ℝ × ℝ) → ℝ), 0 < P → Measurable A → Measurable B →
    (∀ᵐ x : ℝ × Space ∂volume,
      W x = A (x.1, Axi.mer x.2) • Axi.eR x.2 + B (x.1, Axi.mer x.2) • Axi.e3) →
    (∀ᵐ x : ℝ × Space ∂volume, W (x.1 + P, x.2) = W x) →
    ∃ A' B' : ℝ × (ℝ × ℝ) → ℝ, Measurable A' ∧ Measurable B' ∧
      (∀ p, A' (p.1 + P, p.2) = A' p) ∧ (∀ p, B' (p.1 + P, p.2) = B' p) ∧
      ∀ᵐ x : ℝ × Space ∂volume,
        W x = A' (x.1, Axi.mer x.2) • Axi.eR x.2 + B' (x.1, Axi.mer x.2) • Axi.e3

/-- **(P_C)** Complex profile functions for the two fields `radComb g` and `g 2`: measurable,
everywhere `2εc`-periodic in `τ`, with `radComb g = A_r e_r + A_z e_3` and
`g 2 = B_r e_r + B_z e_3` a.e. (complex coefficients, real vectors `B0412.realC (eR y)`,
`B0412.realC e3`). -/
def GLProfFns : Prop :=
  ∀ (c ε r : ℝ) (g : Fin 3 → ℝ × Space → CVec3), 0 < c → 0 < ε → 1 < r → r < 3 →
    (∀ j, IsInYr (2 * ε * c) r (g j)) →
    (∀ P : CVec3 → Space, (P = reS ∨ P = imS) →
      GLEquivar (fun x => P (radComb g x)) ∧ GLEquivar (fun x => P (g 2 x))) →
    ∃ Ar Az Br Bz : ℝ × (ℝ × ℝ) → ℂ,
      Measurable Ar ∧ Measurable Az ∧ Measurable Br ∧ Measurable Bz ∧
      (∀ p, Ar (p.1 + 2 * ε * c, p.2) = Ar p) ∧ (∀ p, Az (p.1 + 2 * ε * c, p.2) = Az p) ∧
      (∀ p, Br (p.1 + 2 * ε * c, p.2) = Br p) ∧ (∀ p, Bz (p.1 + 2 * ε * c, p.2) = Bz p) ∧
      (∀ᵐ x : ℝ × Space ∂volume,
        radComb g x = Ar (x.1, Axi.mer x.2) • B0412.realC (Axi.eR x.2) +
          Az (x.1, Axi.mer x.2) • B0412.realC Axi.e3) ∧
      (∀ᵐ x : ℝ × Space ∂volume,
        g 2 x = Br (x.1, Axi.mer x.2) • B0412.realC (Axi.eR x.2) +
          Bz (x.1, Axi.mer x.2) • B0412.realC Axi.e3)

/-- **(CB1)** The lift of `chartProf` off the axis (SP 1639-1668, 1903): `Axi.chart ε⁻¹ τ y`
has `age = ε⁻² / ϱ²`, so `invChart ε (Axi.chart ε⁻¹ τ y) = (τ, mer y)`, whence
`NvC ε⁻¹ (sqrtS (chartProf ε A B)) (τ, y) = A(τ, mer y) e_r + B(τ, mer y) e_3`
(`√s · s⁻¹ · √s = 1`, `Axi.frameL_apply`, `reM`/`imM` of the vector `!₂[A, B]`). -/
def GLChartNv : Prop :=
  ∀ (ε : ℝ) (A B : ℝ × (ℝ × ℝ) → ℂ) (τ : ℝ) (y : Space), 0 < ε → y ∉ Axi.axis →
    NvC ε⁻¹ (sqrtS (chartProf ε A B)) (τ, y) =
      A (τ, Axi.mer y) • B0412.realC (Axi.eR y) + B (τ, Axi.mer y) • B0412.realC Axi.e3

/-- **(CB2)** Measurability of `sqrtS (chartProf ε A B)` for measurable `A, B` (composition of
measurable maps: `Real.log`, `Real.sqrt`, inverse, `Measurable.ite` on `0 < s`). -/
def GLChartMeas : Prop :=
  ∀ (ε : ℝ) (A B : ℝ × (ℝ × ℝ) → ℂ) (μ : Measure Coord), Measurable A → Measurable B →
    AEStronglyMeasurable (sqrtS (chartProf ε A B)) μ

/-- **(CB3)** `q`-periodicity of `sqrtS (chartProf ε A B)` with period `c` when `A, B` are
`2εc`-periodic in `τ`: `invChart ε (s, q + c, η) = (τ + 2εc, ϱ, z)`; for `s ≤ 0` both sides are `0`. -/
def GLChartPeriodic : Prop :=
  ∀ (c ε : ℝ) (A B : ℝ × (ℝ × ℝ) → ℂ),
    (∀ p, A (p.1 + 2 * ε * c, p.2) = A p) → (∀ p, B (p.1 + 2 * ε * c, p.2) = B p) →
    QPeriodic c (sqrtS (chartProf ε A B))

theorem gl_build_of (h1 : GLProfFns) (h2 : GLChartNv) (h3 : GLChartMeas) (h4 : GLChartPeriodic) :
    GLBuild := by
  intro c ε r g hc hε hr1 hr3 hgY hE
  obtain ⟨Ar, Az, Br, Bz, hmAr, hmAz, hmBr, hmBz, hpAr, hpAz, hpBr, hpBz, hrad, hax⟩ :=
    h1 c ε r g hc hε hr1 hr3 hgY hE
  have hae : ∀ᵐ x : ℝ × Space ∂volume, x.2 ∉ Axi.axis := by
    rw [Measure.volume_eq_prod]
    exact Measure.quasiMeasurePreserving_snd.ae Axi.ae_not_mem_axis
  refine ⟨chartProf ε Ar Az, chartProf ε Br Bz, h4 c ε Ar Az hpAr hpAz,
    h3 ε Ar Az _ hmAr hmAz, h4 c ε Br Bz hpBr hpBz, h3 ε Br Bz _ hmBr hmBz, ?_, ?_⟩
  · filter_upwards [hax, hae] with x hx hx2
    rw [hx]
    exact h2 ε Br Bz x.1 x.2 hε hx2
  · filter_upwards [hrad, hae] with x hx hx2
    rw [hx]
    exact h2 ε Ar Az x.1 x.2 hε hx2

end UnforcedLeray.Short.IIb

#print axioms UnforcedLeray.Short.IIb.gl_build_of
