import UnforcedLeray.Short.PartIIIa.Sub.AdjInterior.TimeJets.Assembly
import UnforcedLeray.Short.PartIIIa.Sub.PartIIIa_T21_2_7_2_1_2

/-!
# `PartIII-a:T21/2/7/2/1/2/1/2`: `AdjTimeJetsEnd` from `[t, s)` leaves

Source `the November 2 reference manuscript` (SP) 3060-3061 (`-∂_rφ = νΔφ + v·∇φ -
K_c^T(φ∇E)`), 3052-3058, 270-288.

This is the Ico transcription of `Sub/AdjInterior/TimeJets/Assembly.lean`.  The generic parts
(`tjSeq_spec`, `AdjHkAllOf`, `AdjHkAllLinear`, `HasXDerivOnLinear`, `AdjHkAllCoeffMul`,
`AdjHkAllKerMul`, `KerVelIsBS`) are stated for an arbitrary interval `I` and are reused.

**Design correction.** `vJet`/`eJet` use the two-sided `iteratedDeriv`, which at the age `r = 0`
(the case `t = 0`) is junk: the train is smooth on `[0, ∞) × ℝ²` only (one-sided at `0`).  Here the
operator family is `adjLopW` with the one-sided jets `vJetW`, `eJetW`
(`iteratedDerivWithin … (Ici 0)`), which agree with `vJet`, `eJet` for `r > 0`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.IIIa

/-- `∂_r^i v_l(r, x)` within the half line `[0, ∞)` (one-sided at the age `0`). -/
def vJetW {ν c : ℝ} (tr : UnforcedLeray.B0140.TrainSol ν c) (i : ℕ) (r : ℝ) (x : ℝ × ℝ)
    (l : Fin 2) : ℝ :=
  iteratedDerivWithin i (fun ρ => tr.v ρ x l) (Ici (0 : ℝ)) r

/-- `∂_r^i ∂_l E(r, x)` within the half line `[0, ∞)`. -/
def eJetW {ν c : ℝ} (tr : UnforcedLeray.B0140.TrainSol ν c) (i : ℕ) (r : ℝ) (l : Fin 2)
    (x : ℝ × ℝ) : ℝ :=
  iteratedDerivWithin i (fun ρ => B0579.pd l (UnforcedLeray.B0238.Ec tr ρ) x) (Ici (0 : ℝ)) r

/-- The operator family with one-sided age jets of the train. -/
def adjLopW {ν c : ℝ} (tr : UnforcedLeray.B0140.TrainSol ν c) (i : ℕ) (r : ℝ)
    (D : List (Fin 2) → ℝ × ℝ → ℂ) (x : ℝ × ℝ) : ℂ :=
  -((if i = 0 then (ν : ℂ) * (D [0, 0] x + D [1, 1] x) else 0) +
      ∑ l : Fin 2, ((vJetW tr i r x l : ℝ) : ℂ) * D [l] x -
      kerAdj c (fun l y => ((eJetW tr i r l y : ℝ) : ℂ) * D [] y) x)

/-! ## Ico leaves -/

/-- **(2) A continuous tested derivative is the `X_{-m,c}`-derivative** (Pettis; SP 3060): if
`f' ∈ C((a, b); X_{-m,c})` and `d/dr ∫ f(r)ψ = ∫ f'(r)ψ` for every cylinder test `ψ`, then
`f(r') - f(r) = ∫_r^{r'} f'` in `X_{-m,c}` (FTC for the tested functions, the test pairing is a
continuous functional `AdjPairing`, and the tests separate `X_{-m,c}`, `LocCylUniq`), so the
difference quotients converge to `f'(r)` in `X_{-m,c}`. -/
def XDerivOfTestedIco : Prop :=
  ∀ (c m a b : ℝ) (f f' : ℝ → ℝ × ℝ → ℂ), 0 < c →
    (∀ r ∈ Ico a b, MemLp (f r) 2 (B0579.cellMeasure c (-m))) →
    (∀ r ∈ Ico a b, MemLp (f' r) 2 (B0579.cellMeasure c (-m))) →
    (∀ r ∈ Ico a b, Tendsto (fun r' => xNorm c (-m) (f' r' - f' r)) (𝓝[Ico a b] r) (𝓝 0)) →
    (∀ ψ : ℝ × ℝ → ℝ, B0579.IsCylTest c ψ → ∀ r ∈ Ico a b,
      HasDerivWithinAt (fun r' => ∫ x in B0579.cell c, f r' x * (ψ x : ℂ))
        (∫ x in B0579.cell c, f' r x * (ψ x : ℂ)) (Ico a b) r) →
    HasXDerivOn c m (Ico a b) f f'

/-- **(3) An `X_{-m,c}`-derivative is a tested derivative**: `|∫ hψ| ≤ ‖h‖_{X_{-m,c}} ‖ψ‖_{X_{m,c}}`
for a cylinder test `ψ` (weighted Cauchy-Schwarz, `WeightedCS`), applied to the difference
quotient minus `f'(r)`. -/
def TestedOfXDerivIco : Prop :=
  ∀ (c m a b : ℝ) (f f' : ℝ → ℝ × ℝ → ℂ), 0 < c →
    (∀ r ∈ Ico a b, MemLp (f r) 2 (B0579.cellMeasure c (-m))) →
    (∀ r ∈ Ico a b, MemLp (f' r) 2 (B0579.cellMeasure c (-m))) →
    HasXDerivOn c m (Ico a b) f f' →
    ∀ χ : ℝ × ℝ → ℝ, B0579.IsCylTest c χ → ∀ r ∈ Ico a b,
      HasDerivWithinAt (fun r' => ∫ x in B0579.cell c, f r' x * (χ x : ℂ))
        (∫ x in B0579.cell c, f' r x * (χ x : ℂ)) (Ico a b) r

/-- **The upgrade**: an `X_{-m,c}`-derivative between two `C(I; H^∞_{-m,c})` families is the
`X_{-m,c}`-derivative of every derivative field (proved from `XDerivOfTestedIco` and
`TestedOfXDerivIco` by induction on the word, `xDerivUpgrade_of`). -/
def XDerivUpgradeIco : Prop :=
  ∀ (c m a b : ℝ) (f f' : ℝ → ℝ × ℝ → ℂ) (D D' : ℝ → List (Fin 2) → ℝ × ℝ → ℂ), 0 < c →
    AdjHkAll c m (Ico a b) f D → AdjHkAll c m (Ico a b) f' D' →
    HasXDerivOn c m (Ico a b) f f' →
    ∀ w : List (Fin 2), HasXDerivOn c m (Ico a b) (fun r => D r w) (fun r => D' r w)

/-- **(7) The classical equation, tested** (SP 3060: integration by parts on the cylinder): for a
cell jet `D` of order `2` of `f` and a cylinder test `ψ`,
`∫ (L^{(0)}(r)D) ψ = -∫ f (νΔψ - v(r)·∇ψ - (K_cψ)·∇E(r))`.  Here
`∫ (D [0,0] + D [1,1])ψ = ∫ fΔψ` (twice `HasWeakCellDerivC`), `∫ Σ_l v_l D [l] ψ = -∫ f v·∇ψ`
(`HasWeakCellDerivC` against the cylinder test `v_l(r)ψ`, `div v = 0`), and
`∫ K_c^T(∇E f)ψ = ∫ f (K_cψ)·∇E` (`KerAdjFubini`; `∇E(r) f ∈ L¹` by `LadTrainBdd` and weighted
Cauchy-Schwarz). -/
def AdjLopTestedW (m : ℝ) : Prop :=
  ∀ ν : ℝ, 0 < ν → ν ≤ 1 → ∀ tr : UnforcedLeray.B0140.TrainSol ν (ν ^ (-2 : ℝ)),
    (∀ S : ℝ, 0 ≤ S → ∃ C : ℝ, LadTrainBdd tr m S C) →
    ∀ r : ℝ, 0 ≤ r → ∀ (f : ℝ × ℝ → ℂ) (D : List (Fin 2) → ℝ × ℝ → ℂ),
      IsCellJet (ν ^ (-2 : ℝ)) m 2 f D →
      ∀ ψ : ℝ × ℝ → ℝ, B0579.IsCylTest (ν ^ (-2 : ℝ)) ψ →
        ∫ x in B0579.cell (ν ^ (-2 : ℝ)), adjLopW tr 0 r D x * (ψ x : ℂ) =
          -∫ x in B0579.cell (ν ^ (-2 : ℝ)), adjIntegrand tr f r ψ (kerVel (ν ^ (-2 : ℝ)) ψ) x

/-- **The first age derivative** (SP 3060): for a weak adjoint with the differentiated weak
equation and fields `D` of all orders on `(t, s)`, `∂_rφ = L^{(0)}(r)φ` in `X_{-m,c}` (proved from
`XDerivOfTestedIco`, `KerVelIsBS`, `AdjLopTestedW`, `AdjLopSmoothIco`, `adjTimeDerivBase_of`). -/
def AdjTimeDerivBaseIco (m : ℝ) : Prop :=
  ∀ ν : ℝ, 0 < ν → ν ≤ 1 → ∀ tr : UnforcedLeray.B0140.TrainSol ν (ν ^ (-2 : ℝ)),
    (∀ S : ℝ, 0 ≤ S → ∃ C : ℝ, LadTrainBdd tr m S C) → (∀ S : ℝ, 0 ≤ S → TrainSTJets tr m S) →
    ∀ t s : ℝ, 0 ≤ t → t < s → ∀ (g : ℝ × ℝ → ℂ) (φ : ℝ → ℝ × ℝ → ℂ),
      IsAdjointWeak ν (ν ^ (-2 : ℝ)) m tr t s g φ → AdjTestedDeriv tr t s φ →
      ∀ D : ℝ → List (Fin 2) → ℝ × ℝ → ℂ, AdjHkAll (ν ^ (-2 : ℝ)) m (Ico t s) φ D →
        HasXDerivOn (ν ^ (-2 : ℝ)) m (Ico t s) φ (fun r => adjLopW tr 0 r (D r))

/-- **The operators preserve `C(I; H^∞_{-m,c})`** (SP 3060, 3052-3058, 2866-2870; proved from the
coefficient and kernel leaves, `adjLopSmooth_of`). -/
def AdjLopSmoothIco (m : ℝ) : Prop :=
  ∀ ν : ℝ, 0 < ν → ν ≤ 1 → ∀ tr : UnforcedLeray.B0140.TrainSol ν (ν ^ (-2 : ℝ)),
    (∀ S : ℝ, 0 ≤ S → ∃ C : ℝ, LadTrainBdd tr m S C) → (∀ S : ℝ, 0 ≤ S → TrainSTJets tr m S) →
    ∀ a b : ℝ, 0 ≤ a → ∀ (i : ℕ) (f : ℝ → ℝ × ℝ → ℂ) (D : ℝ → List (Fin 2) → ℝ × ℝ → ℂ),
      AdjHkAll (ν ^ (-2 : ℝ)) m (Ico a b) f D →
      ∃ D', AdjHkAll (ν ^ (-2 : ℝ)) m (Ico a b) (fun r => adjLopW tr i r (D r)) D'

/-- **The product rule** `∂_r(L^{(i)}Ψ) = L^{(i+1)}Ψ + L^{(i)}∂_rΨ` (SP 3060; proved from the
coefficient and kernel leaves, `adjLopDeriv_of`). -/
def AdjLopDerivIco (m : ℝ) : Prop :=
  ∀ ν : ℝ, 0 < ν → ν ≤ 1 → ∀ tr : UnforcedLeray.B0140.TrainSol ν (ν ^ (-2 : ℝ)),
    (∀ S : ℝ, 0 ≤ S → ∃ C : ℝ, LadTrainBdd tr m S C) → (∀ S : ℝ, 0 ≤ S → TrainSTJets tr m S) →
    ∀ a b : ℝ, 0 ≤ a → ∀ (i : ℕ) (f f' : ℝ → ℝ × ℝ → ℂ)
      (D D' : ℝ → List (Fin 2) → ℝ × ℝ → ℂ),
      AdjHkAll (ν ^ (-2 : ℝ)) m (Ico a b) f D → AdjHkAll (ν ^ (-2 : ℝ)) m (Ico a b) f' D' →
      (∀ w : List (Fin 2),
        HasXDerivOn (ν ^ (-2 : ℝ)) m (Ico a b) (fun r => D r w) (fun r => D' r w)) →
      HasXDerivOn (ν ^ (-2 : ℝ)) m (Ico a b) (fun r => adjLopW tr i r (D r))
        (fun r x => adjLopW tr (i + 1) r (D r) x + adjLopW tr i r (D' r) x)

/-- **(11) Age derivative of a product with a smooth coefficient**:
`∂_r(A f) = (∂_rA) f + A ∂_r f` in `X_{-m,c}`, for `A` with uniform difference quotients. -/
def CoeffMulDerivIco : Prop :=
  ∀ (c m a b : ℝ) (A A' : ℝ → ℝ × ℝ → ℝ) (f f' : ℝ → ℝ × ℝ → ℂ), 0 < c →
    IsSmoothCoeff c (Ico a b) A → IsSmoothCoeff c (Ico a b) A' →
    HasCoeffDeriv (Ico a b) (fun _ => 1) A A' →
    (∀ r ∈ Ico a b, MemLp (f r) 2 (B0579.cellMeasure c (-m))) →
    (∀ r ∈ Ico a b, MemLp (f' r) 2 (B0579.cellMeasure c (-m))) →
    HasXDerivOn c m (Ico a b) f f' →
    HasXDerivOn c m (Ico a b) (fun r x => (A r x : ℂ) * f r x)
      (fun r x => (A' r x : ℂ) * f r x + (A r x : ℂ) * f' r x)

/-- **(20) Age derivative of the kernel term** (SP 3052-3058, `m > 1`):
`∂_r K_c^T(G f) = K_c^T(∂_rG f) + K_c^T(G ∂_r f)` in `X_{-m,c}` (`KerAdjSubAE`: the difference
quotient minus the candidate is `K_c^T` of
`(DQ f - f') G(r') + f'(G(r') - G(r)) + f(DQ G - G')`, small in `L¹ ∩ L²` by `WeightedMulL12`;
then `KerAdjXBound`). -/
def KerMulDerivIco (m : ℝ) : Prop :=
  ∀ (c a b : ℝ) (G G' : ℝ → Fin 2 → ℝ × ℝ → ℝ) (f f' : ℝ → ℝ × ℝ → ℂ), 1 ≤ c →
    IsWeightedCoeff c m (Ico a b) G → IsWeightedCoeff c m (Ico a b) G' →
    (∀ l : Fin 2, HasCoeffDeriv (Ico a b) (ejWeight m) (fun r => G r l) (fun r => G' r l)) →
    (∀ r ∈ Ico a b, MemLp (f r) 2 (B0579.cellMeasure c (-m))) →
    (∀ r ∈ Ico a b, MemLp (f' r) 2 (B0579.cellMeasure c (-m))) →
    HasXDerivOn c m (Ico a b) f f' →
    HasXDerivOn c m (Ico a b) (fun r => kerAdj c (fun l y => (G r l y : ℂ) * f r y))
      (fun r x => kerAdj c (fun l y => (G' r l y : ℂ) * f r y) x +
        kerAdj c (fun l y => (G r l y : ℂ) * f' r y) x)

/-- **(22) The velocity jets are smooth coefficients** (SP 270-288; `TrainSTJets`: every joint
derivative of `v` is bounded on `[0, S] × ℝ²`; for `r > 0` the derivatives within `[0, ∞) × ℝ²`
are the derivatives; `∂_x^w ∂_r^i v_l` is a component of `D^{i+|w|}v` applied to unit vectors,
periodic by `periodic_v`; mean value and Taylor in `r`). -/
def TrainVCoeffW (m : ℝ) : Prop :=
  ∀ ν : ℝ, 0 < ν → ν ≤ 1 → ∀ tr : UnforcedLeray.B0140.TrainSol ν (ν ^ (-2 : ℝ)),
    (∀ S : ℝ, 0 ≤ S → TrainSTJets tr m S) → ∀ a b : ℝ, 0 ≤ a → ∀ (i : ℕ) (l : Fin 2),
      IsSmoothCoeff (ν ^ (-2 : ℝ)) (Ico a b) (fun r x => vJetW tr i r x l) ∧
        HasCoeffDeriv (Ico a b) (fun _ => 1) (fun r x => vJetW tr i r x l)
          (fun r x => vJetW tr (i + 1) r x l)

/-- **(23) The vorticity-gradient jets are weighted coefficients** (SP 2866-2870; `TrainSTJets`:
every joint derivative of positive order of `E` is bounded with the weight
`(1 + x₂²)^{(m+1)/2}`; `∂_x^w ∂_r^i ∂_l E` has order `i + |w| + 1 ≥ 1`). -/
def TrainECoeffW (m : ℝ) : Prop :=
  ∀ ν : ℝ, 0 < ν → ν ≤ 1 → ∀ tr : UnforcedLeray.B0140.TrainSol ν (ν ^ (-2 : ℝ)),
    (∀ S : ℝ, 0 ≤ S → TrainSTJets tr m S) → ∀ a b : ℝ, 0 ≤ a → ∀ i : ℕ,
      IsWeightedCoeff (ν ^ (-2 : ℝ)) m (Ico a b) (fun r l x => eJetW tr i r l x) ∧
        ∀ l : Fin 2, HasCoeffDeriv (Ico a b) (ejWeight m) (fun r x => eJetW tr i r l x)
          (fun r x => eJetW tr (i + 1) r l x)

/-- **`XDerivUpgradeIco` from the two tested-derivative leaves.** -/
theorem xDerivUpgradeIco_of (hP : XDerivOfTestedIco) (hT : TestedOfXDerivIco) : XDerivUpgradeIco := by
  intro c m a b f f' D D' hc hD hD' hff' w
  have hmD : ∀ u : List (Fin 2), ∀ r ∈ Ico a b, MemLp (D r u) 2 (B0579.cellMeasure c (-m)) :=
    fun u r hr => (hD.1 r hr u.length).memX u le_rfl
  have hmD' : ∀ u : List (Fin 2), ∀ r ∈ Ico a b, MemLp (D' r u) 2 (B0579.cellMeasure c (-m)) :=
    fun u r hr => (hD'.1 r hr u.length).memX u le_rfl
  induction w with
  | nil =>
    exact hasXDerivOn_congr hff' (fun r hr => ((hD.1 r hr 0).base).symm)
      (fun r hr => ((hD'.1 r hr 0).base).symm)
  | cons j w ih =>
    refine hP c m a b (fun r => D r (j :: w)) (fun r => D' r (j :: w)) hc (hmD _) (hmD' _)
      (fun r hr => hD'.2 (j :: w) r hr) (fun ψ hψ r hr => ?_)
    have hw := hT c m a b (fun r => D r w) (fun r => D' r w) hc (hmD w) (hmD' w) ih
      (B0579.pd j ψ) (hψ.pd j) r hr
    have hibp : ∀ r' ∈ Ico a b, ∫ x in B0579.cell c, D r' (j :: w) x * (ψ x : ℂ) =
        -∫ x in B0579.cell c, D r' w x * (B0579.pd j ψ x : ℂ) := by
      intro r' hr'
      have hd := (hD.1 r' hr' (w.length + 1)).deriv j w (Nat.lt_succ_self _)
      rw [hd.2 ψ hψ, neg_neg]
    have hibp' : ∫ x in B0579.cell c, D' r (j :: w) x * (ψ x : ℂ) =
        -∫ x in B0579.cell c, D' r w x * (B0579.pd j ψ x : ℂ) := by
      have hd := (hD'.1 r hr (w.length + 1)).deriv j w (Nat.lt_succ_self _)
      rw [hd.2 ψ hψ, neg_neg]
    show HasDerivWithinAt (fun r' => ∫ x in B0579.cell c, D r' (j :: w) x * (ψ x : ℂ))
      (∫ x in B0579.cell c, D' r (j :: w) x * (ψ x : ℂ)) (Ico a b) r
    rw [hibp']
    exact hw.neg.congr (fun r' hr' => hibp r' hr') (hibp r hr)

/-- **`AdjTimeDerivBaseIco` from its leaves.** -/
theorem adjTimeDerivBaseIco_of (m : ℝ) (hP : XDerivOfTestedIco) (hK : KerVelIsBS)
    (hT : AdjLopTestedW m) (hS : AdjLopSmoothIco m) : AdjTimeDerivBaseIco m := by
  intro ν hν hν1 tr hBdd hJets t s ht hts g φ hφ hTD D hD
  have hc : (0 : ℝ) < ν ^ (-2 : ℝ) := Real.rpow_pos_of_pos hν _
  have hc1 : (1 : ℝ) ≤ ν ^ (-2 : ℝ) :=
    Real.one_le_rpow_of_pos_of_le_one_of_nonpos hν hν1 (by norm_num)
  obtain ⟨D', hD'⟩ := hS ν hν hν1 tr hBdd hJets t s ht 0 φ D hD
  refine hP _ m t s φ (fun r => adjLopW tr 0 r (D r)) hc (fun r hr => hD.memLp hr)
    (fun r hr => hD'.memLp hr) (fun r hr => ?_) (fun ψ hψ r hr => ?_)
  · have h := hD'.2 [] r hr
    refine h.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with r' hr'
    rw [(hD'.1 r' hr' 0).base, (hD'.1 r hr 0).base]
  · obtain ⟨-, hder⟩ := hTD ψ (kerVel (ν ^ (-2 : ℝ)) ψ) hψ (hK _ hc1 ψ hψ)
    have h2 := (hder r ⟨hr.1, hr.2.le⟩).mono Ico_subset_Icc_self
    have h3 := hT ν hν hν1 tr hBdd r (ht.trans hr.1) (φ r) (D r) (hD.1 r hr 2) ψ hψ
    show HasDerivWithinAt (fun r' => ∫ x in B0579.cell (ν ^ (-2 : ℝ)), φ r' x * (ψ x : ℂ))
      (∫ x in B0579.cell (ν ^ (-2 : ℝ)), adjLopW tr 0 r (D r) x * (ψ x : ℂ)) (Ico t s) r
    rw [h3]
    exact h2

/-- **`AdjLopSmoothIco` from its leaves.** -/
theorem adjLopSmoothIco_of (m : ℝ) (hL : AdjHkAllLinear) (hC : AdjHkAllCoeffMul)
    (hK : AdjHkAllKerMul m) (hV : TrainVCoeffW m) (hE : TrainECoeffW m) : AdjLopSmoothIco m := by
  intro ν hν hν1 tr hBdd hJets a b ha i f D hD
  have hc : (0 : ℝ) < ν ^ (-2 : ℝ) := Real.rpow_pos_of_pos hν _
  have hc1 : (1 : ℝ) ≤ ν ^ (-2 : ℝ) :=
    Real.one_le_rpow_of_pos_of_le_one_of_nonpos hν hν1 (by norm_num)
  have hlin := (hL (ν ^ (-2 : ℝ)) m (Ico a b)).2
  have hzero := (hL (ν ^ (-2 : ℝ)) m (Ico a b)).1
  have hdiff := hlin _ _ _ _ 1 1 (adjHkAll_shift hD [0, 0]) (adjHkAll_shift hD [1, 1])
  have htr : ∀ l : Fin 2, AdjHkAll (ν ^ (-2 : ℝ)) m (Ico a b)
      (fun r x => ((vJetW tr i r x l : ℝ) : ℂ) * D r [l] x)
      (fun r => leib (fun x => vJetW tr i r x l) (fun w => D r (w ++ [l]))) := fun l =>
    hC _ m (Ico a b) (fun r x => vJetW tr i r x l) (fun r => D r [l]) (fun r w => D r (w ++ [l]))
      hc (hV ν hν hν1 tr hJets a b ha i l).1 (adjHkAll_shift hD [l])
  have hD0 : AdjHkAll (ν ^ (-2 : ℝ)) m (Ico a b) (fun r => D r []) D :=
    adjHkAll_congr hD (fun r hr => ((hD.1 r hr 0).base).symm)
  have hker := hK _ (Ico a b) (fun r l x => eJetW tr i r l x) (fun r => D r []) D hc1
    (hE ν hν hν1 tr hJets a b ha i).1 hD0
  obtain ⟨DQ, hQ⟩ : ∃ DQ, AdjHkAll (ν ^ (-2 : ℝ)) m (Ico a b)
      (fun r x => if i = 0 then (ν : ℂ) * (D r [0, 0] x + D r [1, 1] x) else 0) DQ := by
    by_cases hi : i = 0
    · refine ⟨_, adjHkAll_congr (hlin _ _ _ _ (ν : ℂ) 0 hdiff hzero) (fun r _ => ?_)⟩
      funext x
      simp [hi]
    · refine ⟨_, adjHkAll_congr hzero (fun r _ => ?_)⟩
      funext x
      simp [hi]
  have hT := hlin _ _ _ _ 1 1 (htr 0) (htr 1)
  have hQT := hlin _ _ _ _ 1 1 hQ hT
  have hall := hlin _ _ _ _ (-1) 1 hQT hker
  refine ⟨_, adjHkAll_congr hall (fun r _ => ?_)⟩
  funext x
  simp only [adjLopW, Fin.sum_univ_two]
  ring

/-- The diffusion part `[i = 0] ν (E [0,0] + E [1,1])` of `adjLopW`. -/
def lopQW (ν : ℝ) (i : ℕ) (E : ℝ → List (Fin 2) → ℝ × ℝ → ℂ) (r : ℝ) (x : ℝ × ℝ) : ℂ :=
  if i = 0 then (ν : ℂ) * (E r [0, 0] x + E r [1, 1] x) else 0

/-- The transport part `∂_r^n v_l · E [l]` of `adjLopW`. -/
def lopTW {ν c : ℝ} (tr : UnforcedLeray.B0140.TrainSol ν c) (n : ℕ) (l : Fin 2)
    (E : ℝ → List (Fin 2) → ℝ × ℝ → ℂ) (r : ℝ) (x : ℝ × ℝ) : ℂ :=
  ((vJetW tr n r x l : ℝ) : ℂ) * E r [l] x

/-- The kernel part `K_c^T(∂_r^n∇E · E [])` of `adjLopW`. -/
def lopKW {ν c : ℝ} (tr : UnforcedLeray.B0140.TrainSol ν c) (n : ℕ)
    (E : ℝ → List (Fin 2) → ℝ × ℝ → ℂ) (r : ℝ) : ℝ × ℝ → ℂ :=
  kerAdj c (fun l y => ((eJetW tr n r l y : ℝ) : ℂ) * E r [] y)

theorem adjLopW_eq_parts {ν c : ℝ} (tr : UnforcedLeray.B0140.TrainSol ν c) (n : ℕ)
    (E : ℝ → List (Fin 2) → ℝ × ℝ → ℂ) (r : ℝ) (x : ℝ × ℝ) :
    adjLopW tr n r (E r) x = -1 * (1 * lopQW ν n E r x +
      1 * (1 * lopTW tr n 0 E r x + 1 * lopTW tr n 1 E r x)) + 1 * lopKW tr n E r x := by
  simp only [adjLopW, lopQW, lopTW, lopKW, Fin.sum_univ_two]
  ring

/-- **`AdjLopDerivIco` from its leaves.** -/
theorem adjLopDerivIco_of (m : ℝ) (hX : HasXDerivOnLinear)
    (hC : AdjHkAllCoeffMul) (hK : AdjHkAllKerMul m) (hCD : CoeffMulDerivIco) (hKD : KerMulDerivIco m)
    (hV : TrainVCoeffW m) (hE : TrainECoeffW m) : AdjLopDerivIco m := by
  intro ν hν hν1 tr hBdd hJets a b ha i f f' D D' hD hD' hDD'
  have hc : (0 : ℝ) < ν ^ (-2 : ℝ) := Real.rpow_pos_of_pos hν _
  have hc1 : (1 : ℝ) ≤ ν ^ (-2 : ℝ) :=
    Real.one_le_rpow_of_pos_of_le_one_of_nonpos hν hν1 (by norm_num)
  have hmD : ∀ u : List (Fin 2), ∀ r ∈ Ico a b,
      MemLp (D r u) 2 (B0579.cellMeasure (ν ^ (-2 : ℝ)) (-m)) :=
    fun u r hr => (hD.1 r hr u.length).memX u le_rfl
  have hmD' : ∀ u : List (Fin 2), ∀ r ∈ Ico a b,
      MemLp (D' r u) 2 (B0579.cellMeasure (ν ^ (-2 : ℝ)) (-m)) :=
    fun u r hr => (hD'.1 r hr u.length).memX u le_rfl
  -- memberships of the parts
  have hTm : ∀ (n : ℕ) (E : ℝ → List (Fin 2) → ℝ × ℝ → ℂ) (g : ℝ → ℝ × ℝ → ℂ),
      AdjHkAll (ν ^ (-2 : ℝ)) m (Ico a b) g E → ∀ l : Fin 2, ∀ r ∈ Ico a b,
      MemLp (lopTW tr n l E r) 2 (B0579.cellMeasure (ν ^ (-2 : ℝ)) (-m)) := by
    intro n E g hg l r hr
    exact (hC _ m (Ico a b) (fun r x => vJetW tr n r x l) (fun r => E r [l])
      (fun r w => E r (w ++ [l])) hc (hV ν hν hν1 tr hJets a b ha n l).1
      (adjHkAll_shift hg [l])).memLp hr
  have hKm : ∀ (n : ℕ) (E : ℝ → List (Fin 2) → ℝ × ℝ → ℂ) (g : ℝ → ℝ × ℝ → ℂ),
      AdjHkAll (ν ^ (-2 : ℝ)) m (Ico a b) g E → ∀ r ∈ Ico a b,
      MemLp (lopKW tr n E r) 2 (B0579.cellMeasure (ν ^ (-2 : ℝ)) (-m)) := by
    intro n E g hg r hr
    have hE0 : AdjHkAll (ν ^ (-2 : ℝ)) m (Ico a b) (fun r => E r []) E :=
      adjHkAll_congr hg (fun r hr => ((hg.1 r hr 0).base).symm)
    exact (hK _ (Ico a b) (fun r l x => eJetW tr n r l x) (fun r => E r []) E hc1
      (hE ν hν hν1 tr hJets a b ha n).1 hE0).memLp hr
  have hQm : ∀ (E : ℝ → List (Fin 2) → ℝ × ℝ → ℂ), (∀ u, ∀ r ∈ Ico a b,
      MemLp (E r u) 2 (B0579.cellMeasure (ν ^ (-2 : ℝ)) (-m))) → ∀ r ∈ Ico a b,
      MemLp (lopQW ν i E r) 2 (B0579.cellMeasure (ν ^ (-2 : ℝ)) (-m)) := by
    intro E hEm r hr
    unfold lopQW
    refine memLp_ite_zero _ ?_
    exact ((hEm [0, 0] r hr).add (hEm [1, 1] r hr)).const_mul (ν : ℂ)
  -- the derivatives of the parts
  have hXl := (hX (ν ^ (-2 : ℝ)) m (Ico a b)).2
  have hX0 := (hX (ν ^ (-2 : ℝ)) m (Ico a b)).1
  have hQ : HasXDerivOn (ν ^ (-2 : ℝ)) m (Ico a b) (lopQW ν i D) (lopQW ν i D') := by
    by_cases hi : i = 0
    · have h1 := hXl (fun r => D r [0, 0]) (fun r => D' r [0, 0]) (fun r => D r [1, 1])
        (fun r => D' r [1, 1]) 1 1
        (fun r hr => ⟨hmD _ r hr, hmD' _ r hr, hmD _ r hr, hmD' _ r hr⟩) (hDD' [0, 0])
        (hDD' [1, 1])
      have h2 := hXl (fun r x => 1 * D r [0, 0] x + 1 * D r [1, 1] x)
        (fun r x => 1 * D' r [0, 0] x + 1 * D' r [1, 1] x) (fun _ _ => 0) (fun _ _ => 0)
        (ν : ℂ) 0
        (fun r hr => ⟨memLp_lin 1 1 (hmD _ r hr) (hmD _ r hr),
          memLp_lin 1 1 (hmD' _ r hr) (hmD' _ r hr), MemLp.zero', MemLp.zero'⟩) h1 hX0
      refine hasXDerivOn_congr h2 (fun r _ => ?_) (fun r _ => ?_)
      · funext x
        simp [lopQW, hi]
      · funext x
        simp [lopQW, hi]
    · refine hasXDerivOn_congr hX0 (fun r _ => ?_) (fun r _ => ?_)
      · funext x
        simp [lopQW, hi]
      · funext x
        simp [lopQW, hi]
  have htr : ∀ l : Fin 2, HasXDerivOn (ν ^ (-2 : ℝ)) m (Ico a b) (lopTW tr i l D)
      (fun r x => lopTW tr (i + 1) l D r x + lopTW tr i l D' r x) := fun l =>
    hCD _ m a b (fun r x => vJetW tr i r x l) (fun r x => vJetW tr (i + 1) r x l)
      (fun r => D r [l]) (fun r => D' r [l]) hc (hV ν hν hν1 tr hJets a b ha i l).1
      (hV ν hν hν1 tr hJets a b ha (i + 1) l).1 (hV ν hν hν1 tr hJets a b ha i l).2
      (hmD [l]) (hmD' [l]) (hDD' [l])
  have hker : HasXDerivOn (ν ^ (-2 : ℝ)) m (Ico a b) (lopKW tr i D)
      (fun r x => lopKW tr (i + 1) D r x + lopKW tr i D' r x) :=
    hKD _ a b (fun r l x => eJetW tr i r l x) (fun r l x => eJetW tr (i + 1) r l x)
      (fun r => D r []) (fun r => D' r []) hc1 (hE ν hν hν1 tr hJets a b ha i).1
      (hE ν hν hν1 tr hJets a b ha (i + 1)).1 (hE ν hν hν1 tr hJets a b ha i).2
      (hmD []) (hmD' []) (hDD' [])
  -- combine
  have mT' : ∀ l : Fin 2, ∀ r ∈ Ico a b, MemLp (fun x => lopTW tr (i + 1) l D r x +
      lopTW tr i l D' r x) 2 (B0579.cellMeasure (ν ^ (-2 : ℝ)) (-m)) :=
    fun l r hr => (hTm (i + 1) D f hD l r hr).add (hTm i D' f' hD' l r hr)
  have hT := hXl (lopTW tr i 0 D) (fun r x => lopTW tr (i + 1) 0 D r x + lopTW tr i 0 D' r x)
    (lopTW tr i 1 D) (fun r x => lopTW tr (i + 1) 1 D r x + lopTW tr i 1 D' r x) 1 1
    (fun r hr => ⟨hTm i D f hD 0 r hr, mT' 0 r hr, hTm i D f hD 1 r hr, mT' 1 r hr⟩)
    (htr 0) (htr 1)
  have hQT := hXl (lopQW ν i D) (lopQW ν i D')
    (fun r x => 1 * lopTW tr i 0 D r x + 1 * lopTW tr i 1 D r x)
    (fun r x => 1 * (lopTW tr (i + 1) 0 D r x + lopTW tr i 0 D' r x) +
      1 * (lopTW tr (i + 1) 1 D r x + lopTW tr i 1 D' r x)) 1 1
    (fun r hr => ⟨hQm D hmD r hr, hQm D' hmD' r hr,
      memLp_lin 1 1 (hTm i D f hD 0 r hr) (hTm i D f hD 1 r hr),
      memLp_lin 1 1 (mT' 0 r hr) (mT' 1 r hr)⟩) hQ hT
  have hall := hXl
    (fun r x => 1 * lopQW ν i D r x + 1 * (1 * lopTW tr i 0 D r x + 1 * lopTW tr i 1 D r x))
    (fun r x => 1 * lopQW ν i D' r x + 1 * (1 * (lopTW tr (i + 1) 0 D r x + lopTW tr i 0 D' r x) +
      1 * (lopTW tr (i + 1) 1 D r x + lopTW tr i 1 D' r x)))
    (lopKW tr i D) (fun r x => lopKW tr (i + 1) D r x + lopKW tr i D' r x) (-1) 1
    (fun r hr => ⟨memLp_lin 1 1 (hQm D hmD r hr)
        (memLp_lin 1 1 (hTm i D f hD 0 r hr) (hTm i D f hD 1 r hr)),
      memLp_lin 1 1 (hQm D' hmD' r hr) (memLp_lin 1 1 (mT' 0 r hr) (mT' 1 r hr)),
      hKm i D f hD r hr, (hKm (i + 1) D f hD r hr).add (hKm i D' f' hD' r hr)⟩) hQT hker
  refine hasXDerivOn_congr hall (fun r _ => ?_) (fun r _ => ?_)
  · funext x
    simp only [adjLopW_eq_parts]
  · funext x
    simp only [adjLopW_eq_parts, lopQW, Nat.add_one_ne_zero, ↓reduceIte]
    ring


/-! ## `AdjTimeJetsEnd` -/

/-- **`AdjTimeJetsEnd` from the `[t, s)` leaves.** -/
theorem adjTimeJetsEnd_of (m : ℝ) (hJ : AdjHkAllOf) (hU : XDerivUpgradeIco)
    (hB : AdjTimeDerivBaseIco m) (hS : AdjLopSmoothIco m) (hD : AdjLopDerivIco m)
    (hL : AdjHkAllLinear) (hX : HasXDerivOnLinear) : AdjTimeJetsEnd m := by
  intro ν hν hν1 tr hBdd hJets t s ht hts g φ hφ hTD hk
  have hc : (0 : ℝ) < ν ^ (-2 : ℝ) := Real.rpow_pos_of_pos hν _
  refine ⟨tjSeq (jetOf (ν ^ (-2 : ℝ)) m (Ico t s)) (adjLopW tr) φ, tjSeq_zero _ _ _, ?_⟩
  exact tjSeq_spec (adjLopW tr) φ hL hX (hJ _ m _ φ hc hk)
    (fun i f D hfD => hS ν hν hν1 tr hBdd hJets t s ht i f D hfD)
    (fun i f f' D D' h1 h2 h3 => hD ν hν hν1 tr hBdd hJets t s ht i f f' D D' h1 h2 h3)
    (fun D hDφ => hB ν hν hν1 tr hBdd hJets t s ht hts g φ hφ hTD D hDφ)
    (fun f f' D D' h1 h2 h3 => hU _ m t s f f' D D' hc h1 h2 h3)

/-- **`AdjTimeJetsEnd` from the leaves.** -/
theorem adjTimeJetsEnd_of_leaves (m : ℝ) (h1 : AdjHkAllOf) (h2 : XDerivOfTestedIco)
    (h3 : TestedOfXDerivIco) (h4 : AdjHkAllLinear) (h5 : HasXDerivOnLinear) (h6 : KerVelIsBS)
    (h7 : AdjLopTestedW m) (h10 : AdjHkAllCoeffMul) (h11 : CoeffMulDerivIco)
    (h19 : AdjHkAllKerMul m) (h20 : KerMulDerivIco m) (h22 : TrainVCoeffW m)
    (h23 : TrainECoeffW m) : AdjTimeJetsEnd m :=
  have hS := adjLopSmoothIco_of m h4 h10 h19 h22 h23
  adjTimeJetsEnd_of m h1 (xDerivUpgradeIco_of h2 h3) (adjTimeDerivBaseIco_of m h2 h6 h7 hS) hS
    (adjLopDerivIco_of m h5 h10 h19 h11 h20 h22 h23) h4 h5

end UnforcedLeray.Short.IIIa
