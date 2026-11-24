import UnforcedLeray.Short.PartIIa.Sub.N01.Defs
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_near_delta_8_2_3_4
import UnforcedLeray.Short.PartIIIb.NearInst.Delta.Proofs.CompactWindow.Comparison.FlatStress.FlatStressFree.FreeEnergyFlatSq
import UnforcedLeray.Short.PartIIIa.T18_FreeCausal.EnergyBound.WeightedEnergy

/-!
# `PartII-a:N01` (design): the flat smooth-test bound `FlatSmoothBound`

Source of record: `the November 2 reference manuscript`,
lines 1650-1658 (`A_0 = -S + νsΔ_{q,η}`), 1669-1674 (`T_0 = (μ - A_0)⁻¹P_0`, `S_0 = T_0 s div_0`),
1661-1664 at `ε = 0` (`div_0` sees only the meridional block), 1684-1689 ("The flat equation is
`(∂_s + μ/s - νΔ)b = P_0 div_0 M`. Pairing it with `s^{-1/2} b̄` gives the coercive constant
`Re μ + 1/4`"), with the causal zero-entrance energy class of 3420-3440 and the energy identity
3541-3552.

Route (as `PartIII-b:C/near/delta/8/2/3/4` for real `μ` and real tensors, here for complex `μ` with
`Re μ + 1/4 > 0` and complex tests):
* `FlatColumnC` (leaf `N01/9`): `T_0(s div_0 M)`, transported to the recentred chart, is a causal
  zero-entrance energy solution of the free flat equation with tensor force the planar block of `M`;
* `Delta.freeEnergyFlat_of (Delta.freeEnergyFlatSq_of IIIa.weightedEnergyIdentity)` (accepted):
  `‖b‖_𝓗 ≤ (2√((Re μ + 1/4)ν))⁻¹‖F‖_𝒯` for every such solution;
* `FlatVelTransport`, `FlatBlkTransport` (leaves `N01/10`, `/11`): the recentring
  `cellPtInv` between the `PartII-a` cell `(0, c]` with `dq` and the chart cell with `dq/c` changes
  both norms by `√c` (`Masked.CellPtInvH`, `Masked.CellPtHT`), and the Frobenius norm of the planar
  block is at most `√2` times the Euclidean norm of `(T_rr, T_rz, T_zz, T_φφ)`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal NNReal ContDiff

namespace UnforcedLeray.Short.PartIIa.N01

open UnforcedLeray.B0220 (Profile HSpace measureH)
open UnforcedLeray.B0223 (MeridC)
open UnforcedLeray.Short.PartIIIb.Concrete (Chart)

/-- **`PartII-a:N01/9` — the flat stress column is causal** (lines 1650-1658, 1669-1674,
1684-1689, 3420-3440): for `ν, c > 0`, `Re μ + 1/4 > 0`, a smooth tensor test `M` and a
representative `G` of `s div_0 M`, `T_0 G = R_0(μ)P_0 G` (transported to the recentred chart by
`Delta.velF`) has a representative `b` which, with some weak gradient `Gr`, is a causal
zero-entrance energy solution of `∂_s b + (μ/s)b - νΔb = P_0 div_0 M` with tensor force the planar
block `Delta.tblkF c M` (`IIIa.IsCausalEnergySolution`, free equation `v = 0`). -/
def FlatColumnC : Prop :=
  ∀ (c ν : ℝ) (hc : 0 < c), 0 < ν → ∀ μ : ℂ, 0 < μ.re + 1 / 4 →
    ∀ M : Profile → TensorVal, IsTensorTest c M → ∀ G : HSpace c MeridC,
      (G : Profile → MeridC) =ᵐ[measureH c] (fun p => (p.1 : ℂ) • divEps 0 M p) →
      ∃ (b : Chart → Fin 2 → ℂ) (Gr : Chart → Fin 2 → Fin 2 → ℂ),
        b =ᵐ[UnforcedLeray.Axi.ageμ c (-3 / 2)]
            UnforcedLeray.Short.PartIIIb.NearInst.Delta.velF c (T0flat hc ν μ G) ∧
          UnforcedLeray.Short.IIIa.IsCausalEnergySolution c ν μ (fun _ _ _ => 0)
            (UnforcedLeray.Short.PartIIIb.NearInst.Delta.tblkF c M) b Gr

/-- **`PartII-a:N01/10` — the velocity norm under recentring** (lines 1644-1646: `H` with `dq/c`
versus the unnormalised `dq` of `B0220.HSpace`): if `b` is a.e. the recentred field
`Delta.velF c g`, then `‖g‖_H = √c ‖b‖_𝓗` (`Masked.CellPtInvH`: `cellPtInv` carries
`ageμ c (-3/2)` to `c⁻¹ measureH c`). -/
def FlatVelTransport : Prop :=
  ∀ c : ℝ, 0 < c → ∀ (g : HSpace c MeridC) (b : Chart → Fin 2 → ℂ),
    b =ᵐ[UnforcedLeray.Axi.ageμ c (-3 / 2)]
        UnforcedLeray.Short.PartIIIb.NearInst.Delta.velF c g →
      ENNReal.ofReal ‖g‖ =
        ENNReal.ofReal (Real.sqrt c) * UnforcedLeray.Short.IIIa.hCalNorm c b

/-- **`PartII-a:N01/11` — the planar block norm under recentring** (lines 1644-1646, 1661-1664 at
`ε = 0`): `√c ‖tblkF c M‖_𝒯 ≤ √2 ‖M‖_{H_T}` (`Masked.CellPtHT`; the Frobenius norm of
`[[T_rr, T_rz], [T_rz, T_zz]]` is at most `√2 |(T_rr, T_rz, T_zz, T_φφ)|`). -/
def FlatBlkTransport : Prop :=
  ∀ c : ℝ, 0 < c → ∀ (M : Profile → TensorVal) (F : HTSpace c),
    (F : Profile → TensorVal) =ᵐ[measureHT c] M →
      ENNReal.ofReal (Real.sqrt c) *
          UnforcedLeray.Short.IIIa.tCalNorm c (UnforcedLeray.Short.PartIIIb.NearInst.Delta.tblkF c M) ≤
        ENNReal.ofReal (Real.sqrt 2 * ‖F‖)

/-- **The flat smooth-test bound** (lines 1684-1689) from the three flat leaves and the accepted
free flat energy bound. -/
theorem flatSmoothBound_of (hcol : FlatColumnC) (hv : FlatVelTransport)
    (hb : FlatBlkTransport) : FlatSmoothBound := by
  intro ν c hc hν μ hγ M hM F G hF hG
  obtain ⟨b, Gr, hbv, hsol⟩ := hcol c ν hc hν μ hγ M hM G hG
  have hmeas : ∀ i j, Measurable fun p =>
      UnforcedLeray.Short.PartIIIb.NearInst.Delta.tblkF c M p i j := fun i j =>
    UnforcedLeray.Short.PartIIIb.NearInst.Delta.fsf_measurable_tblkF
      hM.smooth.continuous.measurable i j
  have hblk := hb c hc M F hF
  have hsc : 0 < Real.sqrt c := Real.sqrt_pos.2 hc
  have hfin : UnforcedLeray.Short.IIIa.tCalNorm c
      (UnforcedLeray.Short.PartIIIb.NearInst.Delta.tblkF c M) < ⊤ := by
    have h1 := lt_of_le_of_lt hblk ENNReal.ofReal_lt_top
    rcases ENNReal.mul_lt_top_iff.1 h1 with h | h | h
    · exact h.2
    · exact absurd h (by rw [ENNReal.ofReal_eq_zero, not_le]; exact hsc)
    · rw [h]; exact ENNReal.zero_lt_top
  have hE := (UnforcedLeray.Short.PartIIIb.NearInst.Delta.freeEnergyFlat_of
    (UnforcedLeray.Short.PartIIIb.NearInst.Delta.freeEnergyFlatSq_of
      UnforcedLeray.Short.IIIa.weightedEnergyIdentity) c ν μ hc hν hγ _ hmeas hfin b Gr hsol).1
  have hV := hv c hc (T0flat hc ν μ G) b hbv
  set k : ℝ := (2 * Real.sqrt ((μ.re + 1 / 4) * ν))⁻¹ with hk
  have hk0 : 0 ≤ k := by positivity
  have hmain : ENNReal.ofReal ‖T0flat hc ν μ G‖ ≤ ENNReal.ofReal (k * (Real.sqrt 2 * ‖F‖)) := by
    rw [hV, ENNReal.ofReal_mul hk0]
    calc ENNReal.ofReal (Real.sqrt c) * UnforcedLeray.Short.IIIa.hCalNorm c b
        ≤ ENNReal.ofReal (Real.sqrt c) * (ENNReal.ofReal k * UnforcedLeray.Short.IIIa.tCalNorm c
            (UnforcedLeray.Short.PartIIIb.NearInst.Delta.tblkF c M)) := by gcongr
      _ = ENNReal.ofReal k * (ENNReal.ofReal (Real.sqrt c) * UnforcedLeray.Short.IIIa.tCalNorm c
            (UnforcedLeray.Short.PartIIIb.NearInst.Delta.tblkF c M)) := by ring
      _ ≤ ENNReal.ofReal k * ENNReal.ofReal (Real.sqrt 2 * ‖F‖) := by gcongr
  have hreal : ‖T0flat hc ν μ G‖ ≤ k * (Real.sqrt 2 * ‖F‖) :=
    (ENNReal.ofReal_le_ofReal_iff (by positivity)).1 hmain
  refine hreal.trans ?_
  have ha : 0 < Real.sqrt ((μ.re + 1 / 4) * ν) := Real.sqrt_pos.2 (mul_pos hγ hν)
  have hs2 : Real.sqrt 2 ≤ 2 := by
    nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num), Real.sqrt_nonneg 2]
  have hFn : 0 ≤ ‖F‖ := norm_nonneg F
  rw [hk]
  calc (2 * Real.sqrt ((μ.re + 1 / 4) * ν))⁻¹ * (Real.sqrt 2 * ‖F‖)
      = Real.sqrt 2 / 2 * ((Real.sqrt ((μ.re + 1 / 4) * ν))⁻¹ * ‖F‖) := by
        field_simp
    _ ≤ 1 * ((Real.sqrt ((μ.re + 1 / 4) * ν))⁻¹ * ‖F‖) := by
        gcongr
        linarith
    _ = (Real.sqrt ((μ.re + 1 / 4) * ν))⁻¹ * ‖F‖ := one_mul _

end UnforcedLeray.Short.PartIIa.N01
