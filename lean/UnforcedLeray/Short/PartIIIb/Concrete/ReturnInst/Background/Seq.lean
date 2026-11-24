import UnforcedLeray.Short.PartIIIb.Concrete.ReturnInst.Background.Levels
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnInst.AffineSource.RABound

/-!
# The three background facts along the concrete return sequence (source 2031, 2505-2562,
2706-2777, 3877-3878, 4144-4145, 5007-5008, 5094, 5926-5950)

Source of record: `the November 2 reference manuscript` (73 pages).

Part of `ORG:return-concrete/instance-3/background-facts`.  The per-level hypotheses `hsplit`,
`hax`, `hW1` of `raBoundExists_of` (`Concrete/ReturnInst/AffineSource/RABound.lean`) in their
`SeqData` forms, from the level statements of `Background/Levels.lean`:

* `seq_splitMult` (`hsplit`): from `SplitMultLevels` and `∀ᶠ n, IsActualLevel dm dp n` (the regime
  and the exact split `IIb.ExactSplitII` of the level);
* `seq_axi` (`hax`) and `seq_W1` (`hW1`): from `BgAxiLevels`, `BgW1Levels`, the actual levels and
  `∀ᶠ n, D.IsBallLevel n`: the split of level `n` is the contraction-ball background of
  `short-bg:result` with radius `ρ_b` (source 2505-2524, 2706-2711; `IsBallSplit`).  This datum is
  what `IIb.StrongRegularity` needs (`IIb.ExactSplitII` does not bound `‖z‖_Z`); it is the field
  `ball` of `SeqData.IsActualLevel` (`ORG:return-concrete/instance-3/background-facts/ball`), so
  `seq_axi_act` and `seq_W1_act` take it from the actual levels;
* `raBoundExists_of_bg` : `RABoundExists D dm dp` from `raBoundExists_of` with these three
  discharged from `IIb.StrongRegularity` (`PartII-b:S3`), `NearInst.SplitMultBound`
  (`PartIII-b:C/near/4`) and the ball datum; `raBoundExists_of_bg'` without the ball datum (from
  `IsActualLevel.ball`).

The levels use the ball constants of `D` (`ρ_b = C₀ν^{-k₀}e^{m₀/ν}ε^{3/11}`), with `C₀ > 0`,
`m₀ > 0` and `2m₀ < 3d₋/11` (the contraction condition of source 2510-2512).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter UnforcedLeray.Axi
open scoped ENNReal

namespace UnforcedLeray.Short.PartIIIb.Concrete

open UnforcedLeray.PhaseSpace UnforcedLeray.B0411
open UnforcedLeray.Cons.C03.Concrete (Params)
open UnforcedLeray.Blueprint.Planar (PlanarData)

/-- **The split of level `n` is the contraction-ball background** (source 2505-2524, 2664-2672,
2706-2711): `V_n = U_raw + Σᵢ αᵢ E_i`, `r_{b,n} = w` for a solution `z = (w, A)` of the projected
equation with `‖z‖_Z ≤ ρ_b = C₀ν_n^{-k₀}e^{m₀/ν_n}ε_n^{3/11}` (`IsBallSplit`). -/
def SeqData.IsBallLevel (D : SeqData) (n : ℕ) : Prop :=
  IsBallSplit ((D.level n).params D.Pl) ((D.level n).ρb D.Pl D.K) (D.V n) (D.rb n)

/-- **`hsplit` along the sequence** (source 2706, 2758-2762, 3877-3878): for large `n` the split
multiplier `M_U : H → Z` of level `n` exists. -/
theorem seq_splitMult (hS : SplitMultLevels) (D : SeqData) {dm dp : ℝ} (hdm : 0 < dm)
    (hm0 : 0 < D.K.m0) (hm0d : D.K.m0 ≤ 3 * dm / 11) (hC0 : 0 < D.K.C0)
    (hmZ : 3 / 2 < D.K.mZ)
    (heig : UnforcedLeray.Blueprint.Planar.IsGrowingEigenpair D.Pl.eigenvalue D.Pl.mode)
    (hω : D.Pl.eigenvalue.im ≠ 0) (hact : ∀ᶠ n : ℕ in atTop, D.IsActualLevel dm dp n) :
    ∀ᶠ n : ℕ in atTop, ∃ M : Hsp (cOf (D.level n).ν) →L[ℝ]
      Zsp (cOf (D.level n).ν) D.K.mZ ((D.level n).ρb D.Pl D.K),
      NearInst.IsSplitMult M ((D.level n).params D.Pl).R (D.level n).V (D.level n).rb := by
  obtain ⟨ν₀, hν₀, h⟩ := hS dm dp hdm D.K.m0 D.K.C0 D.K.k0 hm0 hm0d hC0 D.K.mZ hmZ D.Sig
    D.Pl.eigenvalue D.Pl.mode D.Sig_pos heig
  filter_upwards [hact, (retNu_tendsto D.σ₀ hω).eventually (ge_mem_nhds hν₀)] with n hn hν
  have := h ((D.level n).params D.Pl) _ hn.regime hν rfl rfl (D.Sin n) (D.V n) (D.rb n) hn.split
  exact this

/-- **`hax` along the sequence** (source 121-124, 2031, 2522-2523, 4144-4145): for large `n`,
`U_n = V_n + r_{b,n}` is axisymmetric without swirl at every phase. -/
theorem seq_axi (hA : BgAxiLevels) (D : SeqData) {dm dp : ℝ} (hdm : 0 < dm)
    (hm0 : 0 < D.K.m0) (h2m : 2 * D.K.m0 < 3 * dm / 11) (hC0 : 0 < D.K.C0)
    (heig : UnforcedLeray.Blueprint.Planar.IsGrowingEigenpair D.Pl.eigenvalue D.Pl.mode)
    (hω : D.Pl.eigenvalue.im ≠ 0) (hact : ∀ᶠ n : ℕ in atTop, D.IsActualLevel dm dp n)
    (hball : ∀ᶠ n : ℕ in atTop, D.IsBallLevel n) :
    ∀ᶠ n : ℕ in atTop, ∀ τ, AxiNoSwirlPt ((D.level n).U τ) := by
  obtain ⟨ν₀, hν₀, h⟩ := hA D.Sig D.Pl.eigenvalue D.Pl.mode D.Sig_pos heig D.K.m0 hm0 dm dp hdm
    h2m D.K.C0 D.K.k0 hC0
  filter_upwards [hact, hball, (retNu_tendsto D.σ₀ hω).eventually (ge_mem_nhds hν₀)]
    with n hn hb hν τ
  have := h ((D.level n).params D.Pl) _ hn.regime hν rfl rfl (D.V n) (D.rb n) hb τ
  exact this

/-- **`hW1` along the sequence** (source 2538-2541, 5007-5008, 5094): for large `n`, `U_n - U_raw`
has a finite `W^{1,∞}` bound (indeed `≤ Cν_n^{-k}e^{m₀/ν_n}ε_n^{3/11}`, `BgW1Levels`). -/
theorem seq_W1 (hW : BgW1Levels) (D : SeqData) {dm dp : ℝ} (hdm : 0 < dm)
    (hm0 : 0 < D.K.m0) (h2m : 2 * D.K.m0 < 3 * dm / 11) (hC0 : 0 < D.K.C0)
    (heig : UnforcedLeray.Blueprint.Planar.IsGrowingEigenpair D.Pl.eigenvalue D.Pl.mode)
    (hω : D.Pl.eigenvalue.im ≠ 0) (hact : ∀ᶠ n : ℕ in atTop, D.IsActualLevel dm dp n)
    (hball : ∀ᶠ n : ℕ in atTop, D.IsBallLevel n) :
    ∀ᶠ n : ℕ in atTop, ∃ d : ℝ, D.W1InfAt n d := by
  obtain ⟨C, k, ν₀, -, hν₀, h⟩ := hW D.Sig D.Pl.eigenvalue D.Pl.mode D.Sig_pos heig D.K.m0 hm0
    dm dp hdm h2m D.K.C0 D.K.k0 hC0
  filter_upwards [hact, hball, (retNu_tendsto D.σ₀ hω).eventually (ge_mem_nhds hν₀)]
    with n hn hb hν
  refine ⟨UnforcedLeray.Short.IIb.rhoB ((D.level n).params D.Pl) D.K.m0 C k, fun τ y => ?_⟩
  have := h ((D.level n).params D.Pl) _ hn.regime hν rfl rfl (D.V n) (D.rb n) hb τ y
  exact this

/-- **`RABoundExists D dm dp`** (Lemma `ret:physical-affine` with the second line of
`ret:general-affine-bounds` along the sequence, source 5001-5016, 5022-5079) from
`raBoundExists_of` with its three per-level background hypotheses discharged: the split
multiplier from `SplitMultBound` (`PartIII-b:C/near/4`) and the accepted `coeffMultExists`; the
symmetry of `U` and the `W^{1,∞}` bound of `U - U_raw` from `short-bg:strong`
(`IIb.StrongRegularity`, `PartII-b:S3`), the accepted `inletContDiff` and the ball datum
`∀ᶠ n, D.IsBallLevel n` (source 2505-2524, 2706-2711), with `m_Z > 3/2`, `C₀ > 0`, `m₀ > 0`,
`2m₀ < 3d₋/11` and the growing eigenpair of `D.Pl`. -/
theorem raBoundExists_of_bg (D : SeqData) (dm dp : ℝ) (hdm : 0 < dm)
    (hω : D.Pl.eigenvalue.im ≠ 0) (hγ : 0 < D.Pl.eigenvalue.re) (hσ0 : 0 < D.σ₀)
    (hσ1 : D.σ₀ < 1 / 4) (hχf : IsSourceCutoffC D.K.χf) (hC0 : 0 < D.K.C0) (has : 0 ≤ D.K.as)
    (hm0 : 0 < D.K.m0) (h2m : 2 * D.K.m0 < 3 * dm / 11) (hmZ : 3 / 2 < D.K.mZ)
    (heig : UnforcedLeray.Blueprint.Planar.IsGrowingEigenpair D.Pl.eigenvalue D.Pl.mode)
    (hSR : UnforcedLeray.Short.IIb.StrongRegularity) (hSB : NearInst.SplitMultBound)
    (hball : ∀ᶠ n : ℕ in atTop, D.IsBallLevel n)
    (hpin : NearInst.MultPinOfLink)
    (lh : HhatCoefLinear D.K.as D.K.χf) (lF : FACoefLinear D.K.as D.K.χf)
    (lE : EACoefLinear D.K.as D.K.χf) (bh : HhatCoefBound D.K.as D.K.χf)
    (bF : FACoefBound D.K.as D.K.χf) (bE : EACoefBound D.K.as D.K.χf)
    (hAdj : IBPAdjointC2) (hDiv : IBPDivC1) (hGrad : IBPGradC1) (hCont : IBPContC)
    (hreg : AffineLiftReg D.K.as D.K.χf) (haxi : RAPhysAxi D.K.as D.K.χf)
    (hlin : RALinear D.K.as D.K.χf) (hper : RPerBound D.K.as D.K.χf)
    (hgeo : RAGeoBound D.K.as D.K.χf) (hcv : RAConvBound D.K.as D.K.χf) :
    RABoundExists D dm dp := by
  intro hact
  have hm0d : D.K.m0 ≤ 3 * dm / 11 := by linarith
  exact raBoundExists_of D dm dp hdm hω hγ hσ0 hσ1 hχf hC0 has
    (seq_splitMult (splitMultLevels_of' hSB) D hdm hm0 hm0d hC0 hmZ heig hω hact)
    (seq_axi (bgAxiLevels_of hSR) D hdm hm0 h2m hC0 heig hω hact hball)
    (seq_W1 (bgW1Levels_of' hSR) D hdm hm0 h2m hC0 heig hω hact hball)
    hpin lh lF lE bh bF bE hAdj hDiv hGrad hCont hreg haxi hlin hper hgeo hcv hact

/-- The ball datum at the actual levels (source 2505-2524, 2706-2711): the field `ball` of
`SeqData.IsActualLevel`. -/
theorem seq_ball_of_act (D : SeqData) {dm dp : ℝ}
    (hact : ∀ᶠ n : ℕ in atTop, D.IsActualLevel dm dp n) :
    ∀ᶠ n : ℕ in atTop, D.IsBallLevel n := by
  filter_upwards [hact] with n hn
  exact hn.ball

/-- **`hax` along the sequence at the actual levels** (source 121-124, 2031, 2505-2524,
2522-2523, 4144-4145): `seq_axi` with the ball datum from `IsActualLevel.ball`. -/
theorem seq_axi_act (hA : BgAxiLevels) (D : SeqData) {dm dp : ℝ} (hdm : 0 < dm)
    (hm0 : 0 < D.K.m0) (h2m : 2 * D.K.m0 < 3 * dm / 11) (hC0 : 0 < D.K.C0)
    (heig : UnforcedLeray.Blueprint.Planar.IsGrowingEigenpair D.Pl.eigenvalue D.Pl.mode)
    (hω : D.Pl.eigenvalue.im ≠ 0) (hact : ∀ᶠ n : ℕ in atTop, D.IsActualLevel dm dp n) :
    ∀ᶠ n : ℕ in atTop, ∀ τ, AxiNoSwirlPt ((D.level n).U τ) :=
  seq_axi hA D hdm hm0 h2m hC0 heig hω hact (seq_ball_of_act D hact)

/-- **`hW1` along the sequence at the actual levels** (source 2505-2541, 5007-5008, 5094):
`seq_W1` with the ball datum from `IsActualLevel.ball`. -/
theorem seq_W1_act (hW : BgW1Levels) (D : SeqData) {dm dp : ℝ} (hdm : 0 < dm)
    (hm0 : 0 < D.K.m0) (h2m : 2 * D.K.m0 < 3 * dm / 11) (hC0 : 0 < D.K.C0)
    (heig : UnforcedLeray.Blueprint.Planar.IsGrowingEigenpair D.Pl.eigenvalue D.Pl.mode)
    (hω : D.Pl.eigenvalue.im ≠ 0) (hact : ∀ᶠ n : ℕ in atTop, D.IsActualLevel dm dp n) :
    ∀ᶠ n : ℕ in atTop, ∃ d : ℝ, D.W1InfAt n d :=
  seq_W1 hW D hdm hm0 h2m hC0 heig hω hact (seq_ball_of_act D hact)

/-- **`RABoundExists D dm dp`** (source 5001-5016, 5022-5079) as `raBoundExists_of_bg`, with the
ball datum (source 2505-2524, 2706-2711) taken from the actual levels (`IsActualLevel.ball`)
instead of a separate hypothesis. -/
theorem raBoundExists_of_bg' (D : SeqData) (dm dp : ℝ) (hdm : 0 < dm)
    (hω : D.Pl.eigenvalue.im ≠ 0) (hγ : 0 < D.Pl.eigenvalue.re) (hσ0 : 0 < D.σ₀)
    (hσ1 : D.σ₀ < 1 / 4) (hχf : IsSourceCutoffC D.K.χf) (hC0 : 0 < D.K.C0) (has : 0 ≤ D.K.as)
    (hm0 : 0 < D.K.m0) (h2m : 2 * D.K.m0 < 3 * dm / 11) (hmZ : 3 / 2 < D.K.mZ)
    (heig : UnforcedLeray.Blueprint.Planar.IsGrowingEigenpair D.Pl.eigenvalue D.Pl.mode)
    (hSR : UnforcedLeray.Short.IIb.StrongRegularity) (hSB : NearInst.SplitMultBound)
    (hpin : NearInst.MultPinOfLink)
    (lh : HhatCoefLinear D.K.as D.K.χf) (lF : FACoefLinear D.K.as D.K.χf)
    (lE : EACoefLinear D.K.as D.K.χf) (bh : HhatCoefBound D.K.as D.K.χf)
    (bF : FACoefBound D.K.as D.K.χf) (bE : EACoefBound D.K.as D.K.χf)
    (hAdj : IBPAdjointC2) (hDiv : IBPDivC1) (hGrad : IBPGradC1) (hCont : IBPContC)
    (hreg : AffineLiftReg D.K.as D.K.χf) (haxi : RAPhysAxi D.K.as D.K.χf)
    (hlin : RALinear D.K.as D.K.χf) (hper : RPerBound D.K.as D.K.χf)
    (hgeo : RAGeoBound D.K.as D.K.χf) (hcv : RAConvBound D.K.as D.K.χf) :
    RABoundExists D dm dp := by
  intro hact
  exact raBoundExists_of_bg D dm dp hdm hω hγ hσ0 hσ1 hχf hC0 has hm0 h2m hmZ heig hSR hSB
    (seq_ball_of_act D hact) hpin lh lF lE bh bF bE hAdj hDiv hGrad hCont hreg haxi hlin hper
    hgeo hcv hact

end UnforcedLeray.Short.PartIIIb.Concrete
