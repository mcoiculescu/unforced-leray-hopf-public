import UnforcedLeray.Short.PartIIIb.Concrete.Standing.Choices
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnInst.Inverses.Seq
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnInst.Background.Seq
import UnforcedLeray.Short.PartIIIb.NearInst.Body.Proofs.BodyRealForms
import UnforcedLeray.Short.PartIIIb.NearInst.Masked.Proofs.StressMapReal
import UnforcedLeray.Short.PartIIIb.NearInst.Masked.Proofs.TepsReal
import UnforcedLeray.Short.PartIIIb.NearInst.Masked.Proofs.TensorTestDense
import UnforcedLeray.Short.PartIIIb.NearInst.Masked.Proofs.TensorTestDivMem
import UnforcedLeray.Short.PartIIIb.NearInst.Delta.Proofs.CompactWindow.Comparison.FlatStress.CellPtChangeAll
import UnforcedLeray.Short.PartIIIb.NearInst.Link.Pins.Proofs.StressPairAE
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_5_1_1.HW

/-!
# The near and inverse pins of the standing hypotheses (`ORG:C/standing` (a), (b))

Source of record: `the November 2 reference manuscript` (73 pages).

Along the sequence `D` (large `n`, `z ∈ [-1, 1]`, `μ = μ_n(z)`), from the actual levels:

* `regimePins_split_of` : the split multiplier `M_U` (source 2706, 2758-2762, 3877-3878), from
  `SplitMultBound` (`PartIII-b:C/near/4`, `splitMultBound_of` of `IIIa.StressCoefficients`) and the
  accepted `coeffMultExists` (`PartIII-b:C/near/1`), through `seq_splitMult`;
* `regimePins_near_of` : the actual near operators `IsActualNear` (source 3866-3914), from
  `NearOpsExistC` (`PartIII-b:C/rep/5/1/1/1/2`, or `nearOpsExistC_of`, `PartIII-b:C/near/5`);
  `regimePins_split_of_near` reads the split multiplier off them (`IsActualNear.split`);
* `regimePins_stress_of` : the weak stress inverse `S_μ = R_μℙdiv` (source 4145, 1556-1572), from
  `PartIIa.NearStressMapExists` (`PartII-a:N01`) and the accepted leaves `stressMapReal_of`,
  `tepsReal`, `tensorTestDense`, `tensorTestDivMem`, `cpcHT_eq`, `cpcInvH_eq`, `cpcH_eq`,
  `stressMapWeakSolC`, `stressPairAE` (`seqStressInverse_of`, `Inverses/Seq.lean`);
* `regimePins_body_of` : the real form `R_ε` of the curved body inverse (source 1675-1677), from
  the accepted `bodyRealForms` (`PartIII-b:C/near/body-real/5`);
* `seq_nearAt_of` : **the near layer is invertible** (`NearAt`, source 3943-3951, 4109-4124), from
  `NearSolverC` and `NearOpsExistC`, for every datum whose choices satisfy `NearChoice` for the
  integer of the near solver (as in `pairNormAndNearSolver_concrete`, `NearInst/Link/Seq.lean`).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter

namespace UnforcedLeray.Short.PartIIIb.Concrete

open UnforcedLeray.Blueprint.Planar (PlanarData IsPlanarReference)

/-! ## 1. The split multiplier and the near operators (source 2706, 3866-3914) -/

/-- **The split multiplier along the sequence** (source 2706, 2758-2762, 3877-3878; the field
`split` of `RegimePins`), from `SplitMultBound` (`PartIII-b:C/near/4`) and `coeffMultExists`. -/
theorem regimePins_split_of (hS : NearInst.SplitMultBound) (D : SeqData) {dm dp : ℝ}
    (hdm : 0 < dm) (hm0 : 0 < D.K.m0) (hm0d : D.K.m0 ≤ 3 * dm / 11) (hC0 : 0 < D.K.C0)
    (hmZ : 3 / 2 < D.K.mZ)
    (heig : UnforcedLeray.Blueprint.Planar.IsGrowingEigenpair D.Pl.eigenvalue D.Pl.mode)
    (hω : D.Pl.eigenvalue.im ≠ 0) (hact : ∀ᶠ n : ℕ in atTop, D.IsActualLevel dm dp n) :
    ∀ᶠ n : ℕ in atTop, ∀ _z ∈ Icc (-1 : ℝ) 1,
      ∃ M : Hsp (cOf (D.level n).ν) →L[ℝ] Zsp (cOf (D.level n).ν) D.K.mZ ((D.level n).ρb D.Pl D.K),
        NearInst.IsSplitMult M ((D.level n).params D.Pl).R (D.level n).V (D.level n).rb := by
  filter_upwards [seq_splitMult (splitMultLevels_of' hS) D hdm hm0 hm0d hC0 hmZ heig hω hact]
    with n hn _ _
  exact hn

/-- **The actual near operators along the sequence** (source 3866-3914, 5785; the field `near` of
`RegimePins`): for large `n` and `z ∈ [-1, 1]` there are operators with
`IsActualNear p V r_b μ_n(z) δ ε_n^{-b}`, from `NearOpsExistC` at the window `K_σ₀`. -/
theorem regimePins_near_of (hEx : NearInst.NearOpsExistC) (D : SeqData) {dm dp : ℝ}
    (hP : IsPlanarReference D.Pl) (hω : D.Pl.eigenvalue.im ≠ 0) (hσ₀ : 0 < D.σ₀)
    (hσ₁ : D.σ₀ < 1 / 4) (hmZ : 3 / 2 < D.K.mZ) (hdm : 0 < dm) (hb : 0 < D.K.b)
    (hb1 : D.K.b < 1) (hδ : 0 < D.K.δ) (hm0 : 0 < D.K.m0) (hm0d : D.K.m0 ≤ 3 * dm / 11)
    (hC0 : 0 < D.K.C0) (hact : ∀ᶠ n : ℕ in atTop, D.IsActualLevel dm dp n) :
    ∀ᶠ n : ℕ in atTop, ∀ z ∈ Icc (-1 : ℝ) 1,
      ∃ o : NearInst.NearOps (cOf (D.level n).ν) D.K.mZ ((D.level n).ρb D.Pl D.K),
        NearInst.IsActualNear ((D.level n).params D.Pl) (D.level n).V (D.level n).rb (D.mu n z)
          D.K.δ ((D.level n).Scut D.K) o := by
  obtain ⟨ν₃, hν₃, hE⟩ := hEx D.Pl hP (NearInst.winK D.σ₀) (NearInst.isCompact_winK _)
    (NearInst.winK_sub hσ₀ hσ₁) D.K.mZ hmZ dm dp hdm D.K.b D.K.δ D.K.m0 hb hb1 hδ hm0 hm0d
    D.K.C0 D.K.k0 hC0 D.Sig D.Sig_pos
  filter_upwards [hact, (retNu_tendsto D.σ₀ hω).eventually (ge_mem_nhds hν₃),
    NearInst.eventually_mu_mem D hω hσ₀ hσ₁] with n hL hνn hμ z hz
  exact hE _ _ hL.regime hνn rfl rfl _ _ _ hL.split _ (hμ z hz)

/-- The split multiplier of the actual near operators (`IsActualNear.split`). -/
theorem regimePins_split_of_near (D : SeqData)
    (h : ∀ᶠ n : ℕ in atTop, ∀ z ∈ Icc (-1 : ℝ) 1,
      ∃ o : NearInst.NearOps (cOf (D.level n).ν) D.K.mZ ((D.level n).ρb D.Pl D.K),
        NearInst.IsActualNear ((D.level n).params D.Pl) (D.level n).V (D.level n).rb (D.mu n z)
          D.K.δ ((D.level n).Scut D.K) o) :
    ∀ᶠ n : ℕ in atTop, ∀ z ∈ Icc (-1 : ℝ) 1,
      ∃ M : Hsp (cOf (D.level n).ν) →L[ℝ] Zsp (cOf (D.level n).ν) D.K.mZ ((D.level n).ρb D.Pl D.K),
        NearInst.IsSplitMult M ((D.level n).params D.Pl).R (D.level n).V (D.level n).rb := by
  filter_upwards [h] with n hn z hz
  obtain ⟨o, ho⟩ := hn z hz
  exact ⟨o.MU, ho.split⟩

/-! ## 2. The stress and body inverses (source 1556-1572, 1675-1677, 4139-4146) -/

/-- **The weak stress inverse along the sequence** (source 4145, `free:weak-stress` 1556-1572; the
field `stress` of `RegimePins`), from `PartIIa.NearStressMapExists` and the accepted leaves of
`StressTransportExists`, `StressMapWeakSol` and `StressPairAE`. -/
theorem regimePins_stress_of (hN : UnforcedLeray.Short.PartIIa.NearStressMapExists)
    (D : SeqData) {dm dp : ℝ} (hdm : 0 < dm) (hω : D.Pl.eigenvalue.im ≠ 0) (hσ₀ : 0 < D.σ₀)
    (hσ₁ : D.σ₀ < 1 / 4) (hmZ : 0 ≤ D.K.mZ) (hC0 : 0 < D.K.C0)
    (hact : ∀ᶠ n : ℕ in atTop, D.IsActualLevel dm dp n) :
    ∀ᶠ n : ℕ in atTop, ∀ z ∈ Icc (-1 : ℝ) 1,
      ∃ S : LStr D.Pl D.K (D.level n) →L[ℝ] LVel D.Pl (D.level n),
        IsWeakStressInverse S (D.level n).ε (D.mu n z) :=
  seqStressInverse_of
    (stressTransportExists_of hN
      (NearInst.Masked.stressMapReal_of NearInst.Masked.tepsReal NearInst.Masked.tensorTestDense
        NearInst.Masked.tensorTestDivMem)
      (fun c hc => NearInst.Masked.cpcHT_eq c hc) (fun c hc => NearInst.Masked.cpcInvH_eq c hc)
      (fun c hc => NearInst.Masked.cpcH_eq c hc))
    stressMapWeakSolC NearInst.stressPairAE D hdm hω hσ₀ hσ₁ hmZ hC0 hact

/-- **The real form of the curved body inverse along the sequence** (source 1675-1677; the field
`body` of `RegimePins`), from the accepted `bodyRealForms` at the window
`[σ₀/2, (σ₀ + 1/4)/2]`. -/
theorem regimePins_body_of (D : SeqData) {dm dp : ℝ} (hdm : 0 < dm)
    (hω : D.Pl.eigenvalue.im ≠ 0) (hσ₀ : 0 < D.σ₀) (hσ₁ : D.σ₀ < 1 / 4)
    (hact : ∀ᶠ n : ℕ in atTop, D.IsActualLevel dm dp n) :
    ∀ᶠ n : ℕ in atTop, ∀ z ∈ Icc (-1 : ℝ) 1,
      ∃ R : Hsp (cOf (D.level n).ν) →L[ℝ] Hsp (cOf (D.level n).ν), NearInst.IsBodyTransport R
        (UnforcedLeray.Short.PartIIa.Teps (P := ((D.level n).params D.Pl).period)
          ((D.level n).params D.Pl).ν_pos ((D.level n).params D.Pl).ε_pos
          ((D.level n).params D.Pl).c_pos rfl ((D.mu n z : ℝ) : ℂ)) := by
  obtain ⟨ν₀, hν₀, h⟩ := NearInst.Body.bodyRealForms (Icc (D.σ₀ / 2) ((D.σ₀ + 1 / 4) / 2))
    isCompact_Icc (inv_window_sub hσ₀ hσ₁) dm dp hdm
  filter_upwards [hact, (retNu_tendsto D.σ₀ hω).eventually (ge_mem_nhds hν₀),
    mu_eventually_mem D hω hσ₀ hσ₁] with n hL hνn hμ z hz
  exact (h _ _ hL.regime hνn _ (hμ z hz)).1

/-! ## 3. The invertible near layer (source 3943-3951, 4109-4124) -/

/-- **`NearAt` along the sequence** (source 3943-3951 `near:inverse-comparison`, 4109-4124; the
field `near` of `RepairStanding`): there is an integer `Kint` (that of `near:deltaN`, chosen after
the reference, the window `K_σ₀`, `m_Z` and `[d₋, d₊]`) such that for every datum whose near
choices satisfy `NearChoice Kint`, whose levels are actual for large `n` and whose inlet supports
are below the output cut `ε_n^{-b}`, for large `n` and `z ∈ [-1, 1]` the near operators of the
level have `D_N` a unit and split multiplier `nearMU`.  Inputs: `NearSolverC` (`PartIII-b:C/near/6`
composed, `Concrete/Standing/NearLayer.lean`) and `NearOpsExistC` (`PartIII-b:C/rep/5/1/1/1/2`). -/
theorem seq_nearAt_of (hNS : NearInst.NearSolverC) (hEx : NearInst.NearOpsExistC)
    (Pl : PlanarData) (hP : IsPlanarReference Pl) (hω : Pl.eigenvalue.im ≠ 0) (σ₀ : ℝ)
    (hσ₀ : 0 < σ₀) (hσ₁ : σ₀ < 1 / 4) (mZ : ℝ) (hmZ : 3 / 2 < mZ) (dm dp : ℝ)
    (hdm : 0 < dm) :
    ∃ Kint : ℕ, ∀ D : SeqData, D.Pl = Pl → D.σ₀ = σ₀ → D.K.mZ = mZ →
      NearInst.NearChoice Kint (gRate Pl) dm D.K.b D.K.δ D.K.m0 D.K.C0 →
      (∀ᶠ n : ℕ in atTop, D.IsActualLevel dm dp n) →
      (∀ᶠ n : ℕ in atTop, D.Sin n ≤ retEps D.Pl D.σ₀ n ^ (-D.K.b)) →
      ∀ᶠ n : ℕ in atTop, ∀ z ∈ Icc (-1 : ℝ) 1, NearAt D.Pl D.K (D.level n) (D.mu n z) := by
  obtain ⟨K₁, hK₁⟩ := hNS Pl hP (NearInst.winK σ₀) (NearInst.isCompact_winK σ₀)
    (NearInst.winK_sub hσ₀ hσ₁) mZ hmZ dm dp hdm
  refine ⟨K₁, ?_⟩
  rintro D rfl rfl rfl ⟨a, Dp, ha, hb, hb1, hKab, hδ, hm0, hm0d, hη, hm0θ, hDp, hC0⟩ hact hSin
  obtain ⟨C₁, k₁, ν₁, hν₁, hS₁⟩ := hK₁ a D.K.b D.K.δ D.K.m0 Dp ha hb hb1 hKab hδ hm0 hm0d hη
    hm0θ hDp D.K.C0 D.K.k0 hC0 (NearInst.epsCst D.Pl D.σ₀) (NearInst.epsCst D.Pl D.σ₀)
    |NearInst.epsPow D.Pl D.σ₀| (NearInst.epsCst_pos D.coeff_ne) le_rfl (abs_nonneg _) D.Sig
    D.Sig_pos
  obtain ⟨ν₃, hν₃, hE⟩ := hEx D.Pl hP (NearInst.winK D.σ₀) (NearInst.isCompact_winK _)
    (NearInst.winK_sub hσ₀ hσ₁) D.K.mZ hmZ dm dp hdm D.K.b D.K.δ D.K.m0 hb hb1 hδ hm0 hm0d.le
    D.K.C0 D.K.k0 hC0 D.Sig D.Sig_pos
  have hν₀ : 0 < min ν₁ ν₃ := lt_min hν₁ hν₃
  filter_upwards [NearInst.seq_levels D hω hσ₀ hσ₁ hact hSin hν₀] with n hN z hz
  obtain ⟨hL, hSn, hνn, -, hμ⟩ := hN
  have hn1 : retNu D.Pl D.σ₀ n ≤ ν₁ := hνn.trans (min_le_left _ _)
  have hn3 : retNu D.Pl D.σ₀ n ≤ ν₃ := hνn.trans (min_le_right _ _)
  have hex : ∃ o : NearInst.NearOps (cOf (D.level n).ν) D.K.mZ ((D.level n).ρb D.Pl D.K),
      NearInst.IsActualNear ((D.level n).params D.Pl) (D.level n).V (D.level n).rb (D.mu n z)
        D.K.δ ((D.level n).Scut D.K) o :=
    hE _ _ hL.regime hn3 rfl rfl _ _ _ hL.split _ (hμ z hz)
  exact nearAt_of hex fun o ho =>
    (hS₁ _ _ hL.regime hn1 rfl rfl (NearInst.seq_epsForm D n) _ _ _ hL.split hSn _ (hμ z hz) o
      ho).2.1

/-- **`NearAt` and the flat unit `D₀` along the sequence** (source 3874-3887, 3943-3951; fields `near`, `flatUnit` of `RepairStanding`), same hypotheses as `seq_nearAt_of`.

Original doc: **`NearAt` along the sequence** (source 3943-3951 `near:inverse-comparison`, 4109-4124; the
field `near` of `RepairStanding`): there is an integer `Kint` (that of `near:deltaN`, chosen after
the reference, the window `K_σ₀`, `m_Z` and `[d₋, d₊]`) such that for every datum whose near
choices satisfy `NearChoice Kint`, whose levels are actual for large `n` and whose inlet supports
are below the output cut `ε_n^{-b}`, for large `n` and `z ∈ [-1, 1]` the near operators of the
level have `D_N` a unit and split multiplier `nearMU`.  Inputs: `NearSolverC` (`PartIII-b:C/near/6`
composed, `Concrete/Standing/NearLayer.lean`) and `NearOpsExistC` (`PartIII-b:C/rep/5/1/1/1/2`). -/
theorem seq_flatUnit_of (hNS : NearInst.NearSolverC) (hEx : NearInst.NearOpsExistC)
    (Pl : PlanarData) (hP : IsPlanarReference Pl) (hω : Pl.eigenvalue.im ≠ 0) (σ₀ : ℝ)
    (hσ₀ : 0 < σ₀) (hσ₁ : σ₀ < 1 / 4) (mZ : ℝ) (hmZ : 3 / 2 < mZ) (dm dp : ℝ)
    (hdm : 0 < dm) :
    ∃ Kint : ℕ, ∀ D : SeqData, D.Pl = Pl → D.σ₀ = σ₀ → D.K.mZ = mZ →
      NearInst.NearChoice Kint (gRate Pl) dm D.K.b D.K.δ D.K.m0 D.K.C0 →
      (∀ᶠ n : ℕ in atTop, D.IsActualLevel dm dp n) →
      (∀ᶠ n : ℕ in atTop, D.Sin n ≤ retEps D.Pl D.σ₀ n ^ (-D.K.b)) →
      ∀ᶠ n : ℕ in atTop, ∀ z ∈ Icc (-1 : ℝ) 1, NearAt D.Pl D.K (D.level n) (D.mu n z) ∧
        IsUnit (nearOpsAt D.Pl D.K (D.level n) (D.mu n z)).D0 := by
  obtain ⟨K₁, hK₁⟩ := hNS Pl hP (NearInst.winK σ₀) (NearInst.isCompact_winK σ₀)
    (NearInst.winK_sub hσ₀ hσ₁) mZ hmZ dm dp hdm
  refine ⟨K₁, ?_⟩
  rintro D rfl rfl rfl ⟨a, Dp, ha, hb, hb1, hKab, hδ, hm0, hm0d, hη, hm0θ, hDp, hC0⟩ hact hSin
  obtain ⟨C₁, k₁, ν₁, hν₁, hS₁⟩ := hK₁ a D.K.b D.K.δ D.K.m0 Dp ha hb hb1 hKab hδ hm0 hm0d hη
    hm0θ hDp D.K.C0 D.K.k0 hC0 (NearInst.epsCst D.Pl D.σ₀) (NearInst.epsCst D.Pl D.σ₀)
    |NearInst.epsPow D.Pl D.σ₀| (NearInst.epsCst_pos D.coeff_ne) le_rfl (abs_nonneg _) D.Sig
    D.Sig_pos
  obtain ⟨ν₃, hν₃, hE⟩ := hEx D.Pl hP (NearInst.winK D.σ₀) (NearInst.isCompact_winK _)
    (NearInst.winK_sub hσ₀ hσ₁) D.K.mZ hmZ dm dp hdm D.K.b D.K.δ D.K.m0 hb hb1 hδ hm0 hm0d.le
    D.K.C0 D.K.k0 hC0 D.Sig D.Sig_pos
  have hν₀ : 0 < min ν₁ ν₃ := lt_min hν₁ hν₃
  filter_upwards [NearInst.seq_levels D hω hσ₀ hσ₁ hact hSin hν₀] with n hN z hz
  obtain ⟨hL, hSn, hνn, -, hμ⟩ := hN
  have hn1 : retNu D.Pl D.σ₀ n ≤ ν₁ := hνn.trans (min_le_left _ _)
  have hn3 : retNu D.Pl D.σ₀ n ≤ ν₃ := hνn.trans (min_le_right _ _)
  have hex : ∃ o : NearInst.NearOps (cOf (D.level n).ν) D.K.mZ ((D.level n).ρb D.Pl D.K),
      NearInst.IsActualNear ((D.level n).params D.Pl) (D.level n).V (D.level n).rb (D.mu n z)
        D.K.δ ((D.level n).Scut D.K) o :=
    hE _ _ hL.regime hn3 rfl rfl _ _ _ hL.split _ (hμ z hz)
  refine ⟨nearAt_of hex fun o ho =>
    (hS₁ _ _ hL.regime hn1 rfl rfl (NearInst.seq_epsForm D n) _ _ _ hL.split hSn _ (hμ z hz) o
      ho).2.1, ?_⟩
  exact (hS₁ _ _ hL.regime hn1 rfl rfl (NearInst.seq_epsForm D n) _ _ _ hL.split hSn _ (hμ z hz) _
    (nearOpsAt_spec hex).1).1

end UnforcedLeray.Short.PartIIIb.Concrete
