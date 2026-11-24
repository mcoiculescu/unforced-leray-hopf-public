import UnforcedLeray.Short.PartIIIb.NearInst.Delta.Sub.PartIIIb_C_near_delta_8_2

/-!
# Decomposition of `flatStressTransport` (item `PartIII-b:C/near/delta/8/2/3`)

Source of record `the November 2 reference manuscript`,
1678-1690 (existence of the stress maps `S_ε`, `ε = 0` flat case `T_0 = R_0 P_0`),
3427-3440 (uniqueness of the causal zero-entrance energy solution), 3956-3967.

Five lemmas:

* `PlanarReferenceExists` : a planar reference `P` exists (Part I; needed to apply
  `IIIa.FreeCausalExistsUnique`, which is stated per planar reference);
* `CellPtChangeAll`      : the three change-of-variables identities `CellPtHT`, `CellPtInvH`,
  `CellPtH` hold for every `c > 0` (they are proved separately in `Masked/Proofs/*`, but those
  three files define the same auxiliary `ctT` and cannot be imported together);
* `FlatStressReal`       : a stress map of `T_0` maps real tensors to real fields (1675-1679,
  the `ε = 0` case of `Masked.StressMapReal`);
* `FlatStressFree`       : the real form of a real stress map of `T_0` is `IsFreeStress`: for real
  `F'`, `S'F'` is the causal zero-entrance energy solution of the free equation (1655-1656,
  1686-1689, 3427-3440);
* `FreeStressUnique`     : two `IsFreeStress` operators coincide (uniqueness part of
  `IIIa.FreeCausalExistsUnique`, 3427-3440, via a.e. invariance and the measurable representative
  of the source, as in `flatFreeGainBound_of`).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory UnforcedLeray.Axi Set
open scoped ENNReal

namespace UnforcedLeray.Short.PartIIIb.NearInst.Delta

open UnforcedLeray.Short.PartIIIb UnforcedLeray.Short.PartIIIb.Concrete
  UnforcedLeray.Short.PartIIIb.NearInst UnforcedLeray.Cons.C03.Concrete
  UnforcedLeray.Blueprint.Planar

/-- A planar reference exists (Part I, the reference choice). -/
def PlanarReferenceExists : Prop := ∃ P : PlanarData, IsPlanarReference P

/-- The cell recentring change of variables, for all `c > 0` (see `Masked/Proofs/CellPtHT.lean`,
`CellPtInvH.lean`, `CellPtH.lean`). -/
def CellPtChangeAll : Prop :=
  ∀ c : ℝ, 0 < c → Masked.CellPtHT c ∧ Masked.CellPtInvH c ∧ Masked.CellPtH c

open UnforcedLeray.Short.PartIIa in
/-- **Flat stress maps are real** (source 1675-1679 at `ε = 0`; `T_0 = R_0 P_0` with `R_0` the
Laplace transform of the real flat semigroup and `P_0` the real Leray projection): for real
`μ > -1/4` every `S'` with `IsStressMap c 0 (T0flat)` maps real tensors to real fields. -/
def FlatStressReal : Prop :=
  ∀ (ν c : ℝ) (hc : 0 < c), 0 < ν → ∀ μ : ℝ, -(1 / 4) < μ →
    ∀ S' : HTSpace c →L[ℂ] UnforcedLeray.B0220.HSpace c UnforcedLeray.B0223.MeridC,
      IsStressMap c 0 (T0flat hc ν (μ : ℂ)) S' → Masked.IsRealStress c S'

open UnforcedLeray.Short.PartIIa in
/-- **The real flat stress map is the causal free response** (source 1655-1656, 1686-1689,
3427-3440): for `0 < μ < 1/4`, `c = ν⁻²` and a real stress map `S'` of `T_0`, the real form of `S'`
satisfies `IsFreeStress`: for every `F ∈ Z`, `S'F'` (`F'` the transport of `F₁ + F₂`) is a causal
zero-entrance energy solution of the free equation with source the meridional block of `F₁ + F₂`
(identification of `R_0 P_0 (s div M)` with the weak causal solution, passage from smooth tensors
by density). -/
def FlatStressFree : Prop :=
  ∀ (ν c μ mZ ρb : ℝ) (hc : 0 < c) (hmZ : 0 ≤ mZ) (hρ : 0 < ρb)
    (hT : Masked.CellPtHT c) (hH : Masked.CellPtInvH c), 0 < ν → c = (ν ^ 2)⁻¹ →
    0 < μ → μ < 1 / 4 →
    ∀ S' : HTSpace c →L[ℂ] UnforcedLeray.B0220.HSpace c UnforcedLeray.B0223.MeridC,
      IsStressMap c 0 (T0flat hc ν (μ : ℂ)) S' → Masked.IsRealStress c S' →
        IsFreeStress (Masked.realForm c mZ ρb hmZ hρ hT hH S') ν μ

/-- **Uniqueness of the free stress operator** (source 3427-3440): given the free causal solver,
for `K ⋐ (0, 1/4)` there is `ν₀` such that two operators `Z → H` with `IsFreeStress` (the causal
energy solution of every source `F ∈ Z`, a.e. unique) coincide. -/
def FreeStressUnique : Prop :=
  UnforcedLeray.Short.IIIa.FreeCausalExistsUnique →
  ∀ P : PlanarData, IsPlanarReference P →
  ∀ Kset : Set ℝ, IsCompact Kset → Kset ⊆ Ioo 0 (1 / 4) →
    ∃ ν₀ : ℝ, 0 < ν₀ ∧ ∀ (ν c μ mZ ρb : ℝ), 0 < ν → ν ≤ ν₀ → c = (ν ^ 2)⁻¹ →
      μ ∈ Kset → 0 ≤ mZ → 0 < ρb → ρb ≤ 1 →
      ∀ S0 S1 : Zsp c mZ ρb →L[ℝ] Hsp c, IsFreeStress S0 ν μ → IsFreeStress S1 ν μ → S0 = S1

open UnforcedLeray.Short.PartIIa in
/-- **`FlatStressTransport` from its five lemmas.** -/
theorem flatStressTransport_of (hP : PlanarReferenceExists) (hCP : CellPtChangeAll)
    (hR : FlatStressReal) (hF : FlatStressFree) (hUn : FreeStressUnique) :
    FlatStressTransport := by
  intro hS hU Kset hK hKs
  obtain ⟨P, hPref⟩ := hP
  obtain ⟨ν₀, hν₀, huniq⟩ := hUn hU P hPref Kset hK hKs
  refine ⟨ν₀, hν₀, ?_⟩
  intro ν c μ mZ ρb hc hν hνν₀ hcν hμ hmZ hρ hρ1 S0 hS0
  obtain ⟨C, -, hNS⟩ := hS
  have hμ' : μ ∈ Ioo (0 : ℝ) (1 / 4) := hKs hμ
  have hμn : ‖(μ : ℂ)‖ ≤ 1 / 4 := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hμ'.1]; exact hμ'.2.le
  have hγ : (1 / 4 : ℝ) ≤ (μ : ℂ).re + 1 / 4 := by simp; exact hμ'.1.le
  set ε : ℝ := min 1 (1 / (2 * c)) with hε
  have hε0 : 0 < ε := lt_min one_pos (by positivity)
  have hε1 : ε ≤ 1 := min_le_left _ _
  have hP0 : 0 < 2 * ε * c := by positivity
  haveI : Fact (0 < 2 * ε * c) := ⟨hP0⟩
  have hP1 : 2 * ε * c ≤ 1 := by
    have : ε ≤ 1 / (2 * c) := min_le_right _ _
    calc 2 * ε * c ≤ 2 * (1 / (2 * c)) * c := by gcongr
      _ = 1 := by field_simp
  obtain ⟨-, S'', hS'', -⟩ := hNS ν c (1 / 4) (1 / 4) hν hc (by norm_num) ε hε0 hε1
    (2 * ε * c) rfl hP1 (μ : ℂ) hμn hγ
  obtain ⟨hT, hH, hH'⟩ := hCP c hc
  have hreal : Masked.IsRealStress c S'' :=
    hR ν c hc hν μ (by linarith [hμ'.1]) S'' hS''
  have htr := Masked.isStressTransport_realForm (mZ := mZ) (ρb := ρb) hmZ hρ hT hH hH' S'' hreal
  have hfree := hF ν c μ mZ ρb hc hmZ hρ hT hH hν hcν hμ'.1 hμ'.2 S'' hS'' hreal
  have heq := huniq ν c μ mZ ρb hν hνν₀ hcν hμ hmZ hρ hρ1 S0
    (Masked.realForm c mZ ρb hmZ hρ hT hH S'') hS0 hfree
  exact ⟨S'', hS'', heq ▸ htr⟩

end UnforcedLeray.Short.PartIIIb.NearInst.Delta
