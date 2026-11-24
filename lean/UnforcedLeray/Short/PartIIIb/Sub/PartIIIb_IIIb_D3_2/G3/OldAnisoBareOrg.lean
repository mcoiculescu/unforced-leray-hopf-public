import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_IIIb_D3_2.G3.OldAnisoOrg

/-!
# `PartIII-b:IIIb-D3/2/G3/1/4/org`: decomposition of `G3.BareColUnit`

Source of record: `the November 2 reference manuscript` (73 pages):
* actual bare columns `φ_{ν,+}(s) = 𝒰(s,0)q_{+,0}`, `φ_{ν,-} = φ̄_{ν,+}` (lines 4416-4426);
* comparison at `H = 2/ν` between `φ_{ν,+}(2/ν) = 𝒰(2/ν,0)q_{+,0}` and the canonical flow from
  `IIIa.preparedDatum` via `SeedLink`, `IsCanonicalBranch.asymptotic`, `FullClockLongForward`,
  and `LaterOutputRem` on `s ≥ u_o = ν^{-3/2}` (lines 4416-4457, 4509-4543);
* cell readout identity `cellInt c (2 M_{zz} - M_{rr}) = 2 Re(a (2 E_q - E_η))` for
  `xiBare (S n) μ a s` (`a ∈ {1, i}`), where the factor `2` from
  `reX (a φ_+ + ā φ̄_+) = 2 Re(a φ_+)` turns `-3πi/(4c)` into
  `(3π/(2c)) Im(a N_ν J(μ))`, with `N_ν = gaugeFactor` and `planarJ = mellinJc` on real `μ`
  (lines 3314-3343, 3392-3401, 4520-4543, 4610-4612).

Decomposition into four Haiku-sized leaf propositions:
* `BareCellAdd` (`G3/1/4/1`, `OldAnisoBare/CellAdd.lean`): additivity of the cell stress readout
  `ξ ↦ cellInt c (2 M_{zz} - M_{rr})` on `levelFlat`;
* `BareCanFlowVel` (`G3/1/4/2`, `OldAnisoBare/CanFlowVel.lean`): linearised flow `(w, u)` from a
  cell representative `qc` of `IIIa.preparedDatum P ν` and a.e. identification of the cell
  Biot-Savart velocity `kcMer` of `xiBareOf` with `2 Re(a s^{-μ} u(s))`;
* `PreparedDatumCompare D` (`G3/1/4/3`, `OldAnisoBare/PreparedCompare.lean`): existence of
  `qc : Xmc (cOf ν) m` agreeing a.e. on the cell with `IIIa.preparedDatum D.Pl ν` such that
  `‖FI.pair.q true 0 - qc‖ ≤ C ν`;
* `BandForwardAtH D` (`G3/1/4/4`, `OldAnisoBare/BandForward.lean`): forward operator bound at
  `H = 2/ν`, `‖FI.ev.U (2/ν) 0 x‖ ≤ C |F_+(2/ν, 0)| ‖x‖`, from `IIIa.FullClockLongForward`.

Assembly: `bareColUnit_of_leaves`, composed by `PartIII-b:IIIb-D3/2/G3/1/4` (`OldAnisoBare.lean`).
-/

set_option autoImplicit false

noncomputable section

open Filter Topology Set MeasureTheory
open scoped ComplexConjugate

namespace UnforcedLeray.Short.PartIIIb.Concrete.FlatUnif.G3

open ConcreteYF FlatSettingInst

/-! ## 1. Bare column from an arbitrary initial state `q` and remainder at `H = 2/ν` -/

/-- The unforced bare column combination `a 𝒰(s,0)q + ā conjX(𝒰(s,0)q)` from an initial state
`q : S.pk.X` at age `0` (source 4416-4426, 4540-4543). -/
def bareColOf (S : FlatSetting) (q : S.pk.X) (a : ℂ) (s : ℝ) : S.pk.X :=
  a • S.pk.Uev s 0 q + (starRingEnd ℂ a) • S.conjX (S.pk.Uev s 0 q)

/-- The Floquet-weighted bare column `s^{-μ}(a 𝒰(s,0)q + ā conjX(𝒰(s,0)q))` from `q`. -/
def xiBareOf (S : FlatSetting) (q : S.pk.X) (μ : ℝ) (a : ℂ) (s : ℝ) : S.pk.X :=
  ((s : ℂ) ^ (-(μ : ℂ))) • bareColOf S q a s

/-- The initial-datum discrepancy state at `H = 2/ν` between `S.pk.q true 0` and `q`, propagated
to age `H = 2/ν` (source 4421-4426, 4509-4514). -/
def bareRemAtH (S : FlatSetting) (ν : ℝ) (q : S.pk.X) (a : ℂ) : S.pk.X :=
  bareColOf S (S.pk.q true 0 - q) a (2 / ν)

/-- The real meridional velocity field `2 Re(a s^{-μ} u)` associated with a complex velocity field
`u : ℝ × ℝ → Fin 2 → ℂ` (source 4520-4543, 4610-4612). -/
def canVelRe (a : ℂ) (μ s : ℝ) (u : ℝ × ℝ → Fin 2 → ℂ) (p : ℝ × ℝ) :
    UnforcedLeray.Axi.Merid :=
  !₂[2 * (a * ((s : ℂ) ^ (-(μ : ℂ)) * u p 0)).re,
     2 * (a * ((s : ℂ) ^ (-(μ : ℂ)) * u p 1)).re]

/-- Cell-length-generalized `E_q = (2/c) ∫_{cell c} v_2 s^{-μ} u_2` (agrees with `IIIa.pairQ`
when `c = ν ^ (-2 : ℝ)`). -/
def pairQ_c {ν c : ℝ} (tr : UnforcedLeray.B0140.TrainSol ν c) (μ : ℂ)
    (u : ℝ × ℝ → Fin 2 → ℂ) (s : ℝ) : ℂ :=
  (2 / (c : ℂ)) *
    ∫ x in B0579.cell c, ((tr.v s x 1 : ℝ) : ℂ) * ((s : ℂ) ^ (-μ) * u x 1)

/-- Cell-length-generalized `E_η = (2/c) ∫_{cell c} v_1 s^{-μ} u_1` (agrees with `IIIa.pairEta`
when `c = ν ^ (-2 : ℝ)`). -/
def pairEta_c {ν c : ℝ} (tr : UnforcedLeray.B0140.TrainSol ν c) (μ : ℂ)
    (u : ℝ × ℝ → Fin 2 → ℂ) (s : ℝ) : ℂ :=
  (2 / (c : ℂ)) *
    ∫ x in B0579.cell c, ((tr.v s x 0 : ℝ) : ℂ) * ((s : ℂ) ^ (-μ) * u x 0)

theorem bareCol_eq_bareColOf (S : FlatSetting) (a : ℂ) (s : ℝ) :
    bareCol S a s = bareColOf S (S.pk.q true 0) a s := rfl

theorem xiBare_eq_xiBareOf (S : FlatSetting) (μ : ℝ) (a : ℂ) (s : ℝ) :
    xiBare S μ a s = xiBareOf S (S.pk.q true 0) μ a s := rfl

/-- `cOf ν = ν ^ (-2 : ℝ)` for `0 < ν`. -/
theorem cOf_eq_rpow {ν : ℝ} (hν : 0 < ν) : cOf ν = ν ^ (-2 : ℝ) := by
  rw [cOf, Real.rpow_neg hν.le, Real.rpow_two]

/-- Cocycle propagation of `bareColOf`: for `0 ≤ H ≤ s`, `𝒰(s,H)(bareColOf S q a H) = bareColOf S q a s`. -/
theorem uev_bareColOf {S : FlatSetting} (hL : YoungLaws S.pk S.conjX) (q : S.pk.X) (a : ℂ)
    {H s : ℝ} (h0H : 0 ≤ H) (hHs : H ≤ s) :
    S.pk.Uev s H (bareColOf S q a H) = bareColOf S q a s := by
  unfold bareColOf
  rw [map_add, map_smul, map_smul, ← hL.conj_U, ← ContinuousLinearMap.comp_apply,
    hL.trans s H 0 le_rfl h0H hHs]

/-- Decomposition of `xiBare S μ a s` at `s ≥ 2/ν` into `xiBareOf S q μ a s` plus the
later-output tail `xiFromH S ν μ (bareRemAtH S ν q a) s`. -/
theorem xiBare_eq_xiBareOf_add_xiFromH {S : FlatSetting} (hL : YoungLaws S.pk S.conjX)
    (q : S.pk.X) {ν : ℝ} (hν : 0 < ν) (μ : ℝ) (a : ℂ) {s : ℝ} (hs : 2 / ν ≤ s) :
    xiBare S μ a s = xiBareOf S q μ a s + xiFromH S ν μ (bareRemAtH S ν q a) s := by
  have h0H : 0 ≤ 2 / ν := div_nonneg zero_le_two hν.le
  unfold xiBare xiBareOf xiFromH bareRemAtH
  rw [bareCol_eq_bareColOf, uev_bareColOf hL (S.pk.q true 0 - q) a h0H hs, ← smul_add]
  congr 1
  unfold bareColOf
  have hq : S.pk.q true 0 = q + (S.pk.q true 0 - q) := (add_sub_cancel q (S.pk.q true 0)).symm
  conv_lhs => rw [hq]
  rw [map_add, hL.conj_add, smul_add, smul_add, add_add_add_comm]

/-- Norm bound `‖bareRemAtH S ν q a‖ ≤ 2 ‖a‖ ‖𝒰(2/ν, 0)(q_{+,0} - q)‖`. -/
theorem norm_bareRemAtH_le {S : FlatSetting} (hL : YoungLaws S.pk S.conjX)
    (ν : ℝ) (q : S.pk.X) (a : ℂ) :
    ‖bareRemAtH S ν q a‖ ≤ 2 * ‖a‖ * ‖S.pk.Uev (2 / ν) 0 (S.pk.q true 0 - q)‖ := by
  unfold bareRemAtH bareColOf
  set y := S.pk.Uev (2 / ν) 0 (S.pk.q true 0 - q)
  have h1 : ‖a • y + (starRingEnd ℂ a) • S.conjX y‖ ≤ ‖a • y‖ + ‖(starRingEnd ℂ a) • S.conjX y‖ :=
    norm_add_le _ _
  rw [norm_smul, norm_smul, RCLike.norm_conj, hL.conj_norm] at h1
  linarith

/-! ## 2. Leaf propositions for `G3/1/4` -/

/-- **Leaf 1 (`G3/1/4/1`, `OldAnisoBare/CellAdd.lean`): additivity of the cell stress readout**
on `levelFlat` (source 4610-4612, from `kcMerLinear` and `tr.isTrain.finite_energy`). -/
def BareCellAdd : Prop :=
  ∀ (κ : IIIa.PlanarFrameKernels) (ν : ℝ) (hν : 0 < ν) [Fact (0 < cOf ν)] (m : ℝ) [Fact (1 < m)]
    (tr : UnforcedLeray.B0140.TrainSol ν (cOf ν))
    (FI : FlatInstData κ ν (cOf ν) m tr)
    (χo : ℝ → ℝ) (ε s : ℝ) (ξ ξ' : (levelFlat hν FI χo ε).pk.X),
    cellInt (levelFlat hν FI χo ε).c (fun p =>
        2 * (levelFlat hν FI χo ε).Mcell s (ξ + ξ') p 2 2 -
          (levelFlat hν FI χo ε).Mcell s (ξ + ξ') p 0 0) =
      cellInt (levelFlat hν FI χo ε).c (fun p =>
        2 * (levelFlat hν FI χo ε).Mcell s ξ p 2 2 -
          (levelFlat hν FI χo ε).Mcell s ξ p 0 0) +
      cellInt (levelFlat hν FI χo ε).c (fun p =>
        2 * (levelFlat hν FI χo ε).Mcell s ξ' p 2 2 -
          (levelFlat hν FI χo ε).Mcell s ξ' p 0 0)

/-- **Leaf 2 (`G3/1/4/2`, `OldAnisoBare/CanFlowVel.lean`): canonical linearised flow and cell
Biot-Savart velocity of `xiBareOf`** (source 4416-4426, 4520-4543, from `FI.ev.flow`, `FI.ev.real`,
`isBiotSavart_kc`, and `IIIa.CTE.isBiotSavart_unique`). -/
def BareCanFlowVel : Prop :=
  ∀ (P : UnforcedLeray.Blueprint.Planar.PlanarData) (κ : IIIa.PlanarFrameKernels) (ν : ℝ)
    (hν : 0 < ν) [Fact (0 < cOf ν)] (m : ℝ) [Fact (1 < m)]
    (tr : UnforcedLeray.B0140.TrainSol ν (cOf ν))
    (FI : FlatInstData κ ν (cOf ν) m tr)
    (χo : ℝ → ℝ) (ε μ : ℝ)
    (qc : (levelFlat hν FI χo ε).pk.X),
    xFn qc =ᵐ[volume.restrict (B0579.cell (cOf ν))] IIIa.preparedDatum P ν →
    ∃ w u,
      IIIa.IsLinearisedFlow ν (cOf ν) m tr 0 (IIIa.preparedDatum P ν) w u ∧
      ∀ (a : ℂ) (s : ℝ), 0 ≤ s →
        kcMer (xiBareOf (levelFlat hν FI χo ε) qc μ a s)
            =ᵐ[volume.restrict (B0579.cell (cOf ν))]
          canVelRe a μ s (u s)

/-- **Leaf 3 (`G3/1/4/3`, `OldAnisoBare/PreparedCompare.lean`): comparison at `t = 0` between
`FI.pair.q true 0` and `IIIa.preparedDatum D.Pl ν`** (source 4416-4426, from `SeedLink`,
`Planar.L0_eigen_unique`, and `D.Pl.canonical.asymptotic` at `θ = ν⁻¹`). -/
def PreparedDatumCompare (D : SeqData) : Prop :=
  ∀ (dm dp : ℝ), D.RepairStanding dm dp →
  ∀ (κ : IIIa.PlanarFrameKernels), SeedLink D κ →
    ∀ (m : ℝ) [Fact (1 < m)], 8 < m →
      ∃ (C ν₀ : ℝ), 0 ≤ C ∧ 0 < ν₀ ∧
        ∀ (ν : ℝ) (hν : 0 < ν), ν ≤ ν₀ →
          haveI : Fact (0 < cOf ν) := ⟨cOf_pos hν⟩
          ∀ (tr : UnforcedLeray.B0140.TrainSol ν (cOf ν))
            (FI : FlatInstData κ ν (cOf ν) m tr),
            ∃ qc : Xmc (cOf ν) m,
              xFn qc =ᵐ[volume.restrict (B0579.cell (cOf ν))]
                IIIa.preparedDatum D.Pl ν ∧
              ‖FI.pair.q true 0 - qc‖ ≤ C * ν

/-- **Leaf 4 (`G3/1/4/4`, `OldAnisoBare/BandForward.lean`): forward operator bound on `[0, 2/ν]`**
(source 2836-2846 `prop:short-full-clock`, 4421-4426, from `IIIa.FullClockLongForward` at `t = 0`,
`s = 2/ν`). -/
def BandForwardAtH (D : SeqData) : Prop :=
  ∀ (dm dp : ℝ), D.RepairStanding dm dp →
  ∀ (κ : IIIa.PlanarFrameKernels), SeedLink D κ →
    ∀ (m : ℝ) [Fact (1 < m)], 8 < m →
      ∃ (C ν₀ : ℝ), 0 ≤ C ∧ 0 < ν₀ ∧
        ∀ (ν : ℝ) (hν : 0 < ν), ν ≤ ν₀ →
          haveI : Fact (0 < cOf ν) := ⟨cOf_pos hν⟩
          ∀ (tr : UnforcedLeray.B0140.TrainSol ν (cOf ν)),
            UnforcedLeray.Short.PartI.IsBUCTrain tr →
            ∀ (FI : FlatInstData κ ν (cOf ν) m tr)
              (x : Xmc (cOf ν) m),
              ‖FI.ev.U (2 / ν) 0 x‖ ≤
                C * ‖Fpm true D.Pl.eigenvalue D.Pl.kappa ν (2 / ν) 0‖ * ‖x‖

/-! ## 3. Bridge between `cellInt`, `pairQ`/`pairEta`, `mellinJc`, and `bareColLead` -/

/-- `cellInt c F` equals `(1/c) ∫_{B0579.cell c} F`. -/
theorem cellInt_eq_setIntegral_cell (c : ℝ) (F : ℝ × ℝ → ℝ) :
    cellInt c F = c⁻¹ * ∫ p in B0579.cell c, F p := by
  unfold cellInt
  congr 1
  have hmeas : (volume : Measure (ℝ × ℝ)).restrict (Ioo (-c / 2) (c / 2) ×ˢ univ) =
      (volume : Measure (ℝ × ℝ)).restrict (B0579.cell c) := by
    rw [B0579.cell, neg_div, Measure.volume_eq_prod, ← Measure.prod_restrict,
      ← Measure.prod_restrict, Measure.restrict_univ, Measure.restrict_congr_set Ioo_ae_eq_Ico]
  rw [hmeas]

/-- For `0 < ν ≤ 4/9` and `s ≥ ν^{-3/2}`, `3/2 ≤ ν * s`, so `χo (ν * s) = 1`. -/
theorem chiO_eq_one_of_uo_le {ν s : ℝ} (hν : 0 < ν) (hν9 : ν ≤ 4 / 9)
    {χo : ℝ → ℝ} (hχo : IsOutwardCutoff χo) (hs : ν ^ (-(3 / 2 : ℝ)) ≤ s) :
    χo (ν * s) = 1 := by
  apply hχo.one
  have hsq : Real.sqrt ν ≤ 2 / 3 := by
    rw [show (2 / 3 : ℝ) = Real.sqrt (4 / 9) by norm_num]
    exact Real.sqrt_le_sqrt hν9
  have hsqpos : 0 < Real.sqrt ν := Real.sqrt_pos.2 hν
  have h32 : 3 / 2 ≤ (Real.sqrt ν)⁻¹ := by
    rw [le_inv_comm₀ (by norm_num) hsqpos]
    exact hsq.trans_eq (by norm_num)
  have heq : ν * ν ^ (-(3 / 2 : ℝ)) = (Real.sqrt ν)⁻¹ := by
    calc ν * ν ^ (-(3 / 2 : ℝ))
        = ν ^ (1 : ℝ) * ν ^ (-(3 / 2 : ℝ)) := by rw [Real.rpow_one]
      _ = ν ^ ((1 : ℝ) + -(3 / 2 : ℝ)) := (Real.rpow_add hν _ _).symm
      _ = ν ^ (-(1 / 2 : ℝ)) := by congr 1; norm_num
      _ = (Real.sqrt ν)⁻¹ := by rw [Real.rpow_neg hν.le, Real.sqrt_eq_rpow]
  calc (3 / 2 : ℝ) ≤ (Real.sqrt ν)⁻¹ := h32
    _ = ν * ν ^ (-(3 / 2 : ℝ)) := heq.symm
    _ ≤ ν * s := mul_le_mul_of_nonneg_left hs hν.le

/-- Pointwise identity `2 M_{22} - M_{00} = 2 Re(a (4 (v_1 s^{-μ} u_1) - 2 (v_0 s^{-μ} u_0)))`
for `M = symOuter v (canVelRe a μ s u p)` (source 4520-4543, 4610-4612). -/
theorem symOuter_canVelRe_readout (v : UnforcedLeray.Axi.Merid) (a : ℂ) (μ s : ℝ)
    (u : ℝ × ℝ → Fin 2 → ℂ) (p : ℝ × ℝ) :
    2 * IIIa.symOuter v (canVelRe a μ s u p) 2 2 -
        IIIa.symOuter v (canVelRe a μ s u p) 0 0 =
      2 * (a * (4 * (((v 1 : ℝ) : ℂ) * ((s : ℂ) ^ (-(μ : ℂ)) * u p 1)) -
        2 * (((v 0 : ℝ) : ℂ) * ((s : ℂ) ^ (-(μ : ℂ)) * u p 0)))).re := by
  simp only [IIIa.symOuter, IIIa.embedMerid, canVelRe, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.tail_cons, Matrix.head_cons, Complex.sub_re, Complex.sub_im,
    Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, Complex.re_ofNat,
    Complex.im_ofNat]
  ring

/-- `tr.v s` is in `L²` on `B0579.cell c` for `s ≥ 0`. -/
theorem train_v_memLp {ν c : ℝ} (tr : UnforcedLeray.B0140.TrainSol ν c) {s : ℝ} (hs0 : 0 ≤ s) :
    MemLp (tr.v s) 2 (volume.restrict (B0579.cell c)) := by
  have hset : UnforcedLeray.Cyl.cell c = B0579.cell c := by
    unfold UnforcedLeray.Cyl.cell B0579.cell
    rw [neg_div]
  have hcont : Continuous (fun x : ℝ × ℝ => tr.v s x) := by
    have hc := tr.isTrain.smooth_v.continuousOn
    refine continuousOn_univ.1 (hc.comp (continuousOn_const.prodMk continuousOn_id) ?_)
    exact fun x _ => ⟨Set.mem_Ici.2 hs0, Set.mem_univ _⟩
  refine (memLp_two_iff_integrable_sq_norm hcont.aestronglyMeasurable).2 ?_
  rw [← hset]
  exact tr.isTrain.finite_energy s hs0

/-- Integrability of `p ↦ ((v p i : ℝ) : ℂ) * (z * u p i)` on a measure `μm` when `v` and `u · i`
are in `L²(μm)`. -/
private theorem integrable_merid_mul_complex {μm : Measure (ℝ × ℝ)}
    {v : ℝ × ℝ → UnforcedLeray.Axi.Merid} {u : ℝ × ℝ → Fin 2 → ℂ}
    (hv : MemLp v 2 μm) ( i : Fin 2) (hu : MemLp (fun p => u p i) 2 μm) (z : ℂ) :
    Integrable (fun p => ((v p i : ℝ) : ℂ) * (z * u p i)) μm := by
  have hprod : Integrable (fun p => ‖v p‖ * ‖u p i‖) μm := hv.norm.integrable_mul hu.norm
  have hcont_v : Continuous (fun x : UnforcedLeray.Axi.Merid => ((x i : ℝ) : ℂ)) :=
    Complex.continuous_ofReal.comp (PiLp.continuous_apply 2 (fun _ : Fin 2 => ℝ) i)
  have hmeas_v : AEStronglyMeasurable (fun p => ((v p i : ℝ) : ℂ)) μm :=
    hcont_v.comp_aestronglyMeasurable hv.1
  have hmeas_u : AEStronglyMeasurable (fun p => z * u p i) μm :=
    (continuous_const.mul continuous_id).comp_aestronglyMeasurable hu.1
  refine (hprod.const_mul ‖z‖).mono' (hmeas_v.mul hmeas_u) (Eventually.of_forall fun p => ?_)
  rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs]
  have hvi : |v p i| ≤ ‖v p‖ := by
    have hsq : (v p i) ^ 2 ≤ ‖v p‖ ^ 2 := by
      rw [EuclideanSpace.norm_eq, Real.sq_sqrt (by positivity), Fin.sum_univ_two]
      fin_cases i <;> simp <;> linarith [sq_nonneg (v p 0), sq_nonneg (v p 1)]
    exact abs_le.2 (abs_le_of_sq_le_sq' hsq (norm_nonneg _))
  calc |v p i| * (‖z‖ * ‖u p i‖)
      = ‖z‖ * (|v p i| * ‖u p i‖) := by ring
    _ ≤ ‖z‖ * (‖v p‖ * ‖u p i‖) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hvi (norm_nonneg _))
          (norm_nonneg _)

/-- On `s ≥ ν^{-3/2}`, if `kcMer` of `ξ s` agrees a.e. on the cell with `canVelRe a μ s (u s)` and
`u s` has `L²` components on the cell, then `itOldDens` equals
`2 Re(a ((2 pairQ_c - pairEta_c) s^{-3/2}))` (source 4520-4543, 4610-4612). -/
theorem itOldDens_eq_of_kcMer_ae {κ : IIIa.PlanarFrameKernels} {ν : ℝ} (hν : 0 < ν)
    (hν9 : ν ≤ 4 / 9) [Fact (0 < cOf ν)] {m : ℝ} [Fact (1 < m)]
    {tr : UnforcedLeray.B0140.TrainSol ν (cOf ν)}
    (FI : FlatInstData κ ν (cOf ν) m tr)
    {χo : ℝ → ℝ} (hχo : IsOutwardCutoff χo) (ε μ : ℝ)
    (ξ : ℝ → (levelFlat hν FI χo ε).pk.X)
    (u : ℝ → ℝ × ℝ → Fin 2 → ℂ) (a : ℂ) {s : ℝ} (hs : ν ^ (-(3 / 2 : ℝ)) ≤ s)
    (hu_lp : ∀ i, MemLp (fun p => u s p i) 2 (volume.restrict (B0579.cell (cOf ν))))
    (hkc : kcMer (ξ s) =ᵐ[volume.restrict (B0579.cell (cOf ν))] canVelRe a μ s (u s)) :
    itOldDens (levelFlat hν FI χo ε) ν ξ s =
      2 * (a * ((2 * pairQ_c tr (μ : ℂ) (u s) s -
        pairEta_c tr (μ : ℂ) (u s) s) * ((s ^ (-3 / 2 : ℝ) : ℝ) : ℂ))).re := by
  unfold itOldDens FlatSetting.ITdens
  have hs0 : 0 ≤ s := (Real.rpow_pos_of_pos hν _).le.trans hs
  have htr_mer : ∀ p, NearInst.trainMer tr (s, p) = tr.v s p := by
    intro p
    ext i
    simp [NearInst.trainMer, IIIa.trainVel, hs0]
  have hchi : (levelFlat hν FI χo ε).chiO s = 1 := chiO_eq_one_of_uo_le hν hν9 hχo hs
  simp only [ite_eq_left_iff.2 fun h => (h hs).elim, hchi, one_mul]
  change s ^ (-(3 / 2 : ℝ)) *
    cellInt (cOf ν) (fun p =>
      2 * IIIa.symOuter (NearInst.trainMer tr (s, p)) (kcMer (ξ s) p) 2 2 -
        IIIa.symOuter (NearInst.trainMer tr (s, p)) (kcMer (ξ s) p) 0 0) = _
  simp only [htr_mer, cellInt_eq_setIntegral_cell]
  have hae : (fun p => 2 * IIIa.symOuter (tr.v s p) (kcMer (ξ s) p) 2 2 -
        IIIa.symOuter (tr.v s p) (kcMer (ξ s) p) 0 0)
      =ᵐ[volume.restrict (B0579.cell (cOf ν))]
      (fun p => 2 * (a * (4 * (((tr.v s p 1 : ℝ) : ℂ) * ((s : ℂ) ^ (-(μ : ℂ)) * u s p 1)) -
        2 * (((tr.v s p 0 : ℝ) : ℂ) * ((s : ℂ) ^ (-(μ : ℂ)) * u s p 0)))).re) := by
    filter_upwards [hkc] with p hp
    rw [hp, symOuter_canVelRe_readout]
  rw [integral_congr_ae hae]
  have hv_lp : MemLp (tr.v s) 2 (volume.restrict (B0579.cell (cOf ν))) :=
    train_v_memLp tr hs0
  set μcell := volume.restrict (B0579.cell (cOf ν))
  set f1 : ℝ × ℝ → ℂ := fun p => ((tr.v s p 1 : ℝ) : ℂ) * ((s : ℂ) ^ (-(μ : ℂ)) * u s p 1)
  set f0 : ℝ × ℝ → ℂ := fun p => ((tr.v s p 0 : ℝ) : ℂ) * ((s : ℂ) ^ (-(μ : ℂ)) * u s p 0)
  have hf1 : Integrable f1 μcell :=
    integrable_merid_mul_complex hv_lp 1 (hu_lp 1) ((s : ℂ) ^ (-(μ : ℂ)))
  have hf0 : Integrable f0 μcell :=
    integrable_merid_mul_complex hv_lp 0 (hu_lp 0) ((s : ℂ) ^ (-(μ : ℂ)))
  have hsub_int : Integrable (fun p => a * (4 * f1 p - 2 * f0 p)) μcell :=
    ((hf1.const_mul 4).sub (hf0.const_mul 2)).const_mul a
  have hint_eq : (∫ p, 2 * (a * (4 * f1 p - 2 * f0 p)).re ∂μcell) =
      2 * (a * (4 * ∫ p, f1 p ∂μcell - 2 * ∫ p, f0 p ∂μcell)).re := by
    have hre_comm := Complex.reCLM.integral_comp_comm hsub_int
    simp only [Complex.reCLM_apply] at hre_comm
    rw [integral_const_mul, hre_comm, integral_const_mul,
      integral_sub (hf1.const_mul 4) (hf0.const_mul 2),
      integral_const_mul, integral_const_mul]
  change s ^ (-(3 / 2 : ℝ)) * ((cOf ν)⁻¹ * ∫ p, 2 * (a * (4 * f1 p - 2 * f0 p)).re ∂μcell) = _
  rw [hint_eq]
  unfold pairQ_c pairEta_c
  change s ^ (-(3 / 2 : ℝ)) * ((cOf ν)⁻¹ *
      (2 * (a * (4 * ∫ p, f1 p ∂μcell - 2 * ∫ p, f0 p ∂μcell)).re)) =
    2 * (a * ((2 * ((2 / ((cOf ν : ℝ) : ℂ)) * ∫ p, f1 p ∂μcell) -
      (2 / ((cOf ν : ℝ) : ℂ)) * ∫ p, f0 p ∂μcell) * ((s ^ (-3 / 2 : ℝ) : ℝ) : ℂ))).re
  have hpow : s ^ (-(3 / 2 : ℝ)) = s ^ (-3 / 2 : ℝ) := by congr 1; norm_num
  rw [hpow]
  set I1 : ℂ := ∫ p, f1 p ∂μcell
  set I0 : ℂ := ∫ p, f0 p ∂μcell
  set cR : ℝ := cOf ν
  set sR : ℝ := s ^ (-3 / 2 : ℝ)
  have hre : (a * ((2 * ((2 / (cR : ℂ)) * I1) - (2 / (cR : ℂ)) * I0) * (sR : ℂ))).re =
      sR * (cR⁻¹ * (a * (4 * I1 - 2 * I0)).re) := by
    have halg : a * ((2 * ((2 / (cR : ℂ)) * I1) - (2 / (cR : ℂ)) * I0) * (sR : ℂ)) =
        ((sR * cR⁻¹ : ℝ) : ℂ) * (a * (4 * I1 - 2 * I0)) := by
      push_cast
      ring
    rw [halg, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero, mul_assoc]
  rw [hre]
  ring

/-- `D.Pl.gaugeFactor ν = Nnu D.Pl.eigenvalue D.Pl.kappa ν` by definition. -/
theorem gaugeFactor_eq_Nnu (P : UnforcedLeray.Blueprint.Planar.PlanarData) (ν : ℝ) :
    P.gaugeFactor ν = Nnu P.eigenvalue P.kappa ν := rfl

/-- For real `μ : ℝ`, `IIIa.mellinJc P (μ : ℂ) = planarJ P (μ : ℂ)`. -/
theorem mellinJc_ofReal_eq_planarJ (P : UnforcedLeray.Blueprint.Planar.PlanarData) (μ : ℝ) :
    IIIa.mellinJc P (μ : ℂ) = planarJ P (μ : ℂ) := by
  unfold IIIa.mellinJc planarJ UnforcedLeray.Blueprint.Planar.PlanarData.mellinJ
  refine setIntegral_congr_fun measurableSet_Ioi fun θ hθ => ?_
  have hθ0 : 0 ≤ θ := hθ.le
  have hexp : (μ : ℂ) + 1 / 2 = ((μ + 1 / 2 : ℝ) : ℂ) := by push_cast; ring
  rw [hexp, Complex.ofReal_cpow hθ0]
  simp

/-- When `S.c = cOf (nu D n)` and `0 < nu D n`, `IIIa.scaleA` equals `oldScaleA`. -/
theorem scaleA_eq_oldScaleA (D : SeqData) (S : FlatSetting) (n : ℕ) (z : ℝ)
    (hc : S.c = cOf (nu D n)) :
    IIIa.scaleA D.Pl (nu D n) (D.mu n z : ℂ) = oldScaleA D S n z := by
  have hν : 0 < nu D n := retNu_pos D.Pl D.σ₀ n
  unfold IIIa.scaleA oldScaleA
  rw [hc, cOf_eq_rpow hν, gaugeFactor_eq_Nnu, Complex.ofReal_re]

/-- When `S.c = cOf (nu D n)`, `2 Re(a · lead_complex) = bareColLead D S n z a`
(source 4520-4543: how the factor `2` turns `-3πi/(4c)` into `(3π/(2c)) Im(a N_ν J(μ))`). -/
theorem two_re_anisoLead_eq_bareColLead (D : SeqData) (S : FlatSetting) (n : ℕ) (z : ℝ) (a : ℂ)
    (hc : S.c = cOf (nu D n)) :
    2 * (a * (3 * Complex.I * ((D.mu n z : ℂ) + 3 / 2) *
      (-((Real.pi : ℝ) : ℂ) * D.Pl.gaugeFactor (nu D n) /
        (4 * (((nu D n) ^ (-2 : ℝ) : ℝ) : ℂ)) *
        (nu D n : ℂ) ^ (3 + 2 * (D.mu n z : ℂ))) *
      IIIa.mellinJc D.Pl (D.mu n z : ℂ))).re =
      bareColLead D S n z a := by
  have hν : 0 < nu D n := retNu_pos D.Pl D.σ₀ n
  have hc' : (nu D n) ^ (-2 : ℝ) = S.c := by rw [hc, cOf_eq_rpow hν]
  have hpow : (nu D n : ℂ) ^ (3 + 2 * (D.mu n z : ℂ)) =
      (((nu D n) ^ (3 + 2 * D.mu n z) : ℝ) : ℂ) := by
    have hexp : (3 : ℂ) + 2 * (D.mu n z : ℂ) = ((3 + 2 * D.mu n z : ℝ) : ℂ) := by
      push_cast; ring
    rw [hexp, Complex.ofReal_cpow hν.le]
  rw [hc', hpow, gaugeFactor_eq_Nnu, mellinJc_ofReal_eq_planarJ]
  unfold bareColLead
  set r : ℝ := (3 * Real.pi / (4 * S.c)) * (D.mu n z + 3 / 2) * nu D n ^ (3 + 2 * D.mu n z)
  set Z : ℂ := a * Nnu D.Pl.eigenvalue D.Pl.kappa (nu D n) * planarJ D.Pl (D.mu n z : ℂ)
  have halg : a * (3 * Complex.I * ((D.mu n z : ℂ) + 3 / 2) *
      (-((Real.pi : ℝ) : ℂ) * Nnu D.Pl.eigenvalue D.Pl.kappa (nu D n) /
        (4 * (S.c : ℂ)) * (((nu D n) ^ (3 + 2 * D.mu n z) : ℝ) : ℂ)) *
      planarJ D.Pl (D.mu n z : ℂ)) =
      -(r : ℂ) * Complex.I * Z := by
    unfold r Z
    push_cast
    ring
  rw [halg]
  have hre : (-(r : ℂ) * Complex.I * Z).re = r * Z.im := by
    simp [Complex.mul_re, Complex.mul_im]
  rw [hre]
  unfold r
  ring

/-! ## 4. Admissible window `K` for `D.mu n z` and integral comparison on `(0, ∞)` -/

/-- The compact real interval `[D.σ₀ / 2, (D.σ₀ + 1 / 4) / 2]` embedded in `ℂ` is admissible for
Part III-a and contains `(D.mu n z : ℂ)` for all large `n` and `z ∈ [-1, 1]`. -/
theorem exists_admissibleK_for_mu (D : SeqData) {dm dp : ℝ} (hst : D.RepairStanding dm dp) :
    ∃ K : Set ℂ, IIIa.IsAdmissibleK K ∧
      ∀ᶠ n : ℕ in atTop, ∀ z ∈ Icc (-1 : ℝ) 1, (D.mu n z : ℂ) ∈ K := by
  have h0 : 0 < D.σ₀ := hst.sigma_pos
  have h14 : D.σ₀ < 1 / 4 := hst.sigma_lt
  set K : Set ℂ := (fun x : ℝ => (x : ℂ)) '' Icc (D.σ₀ / 2) ((D.σ₀ + 1 / 4) / 2)
  refine ⟨K, ⟨isCompact_Icc.image Complex.continuous_ofReal, ?_⟩, ?_⟩
  · rintro μ ⟨x, hx, rfl⟩
    simp only [Complex.ofReal_re]
    exact ⟨by linarith [hx.1], by linarith [hx.2]⟩
  · filter_upwards [mu_eventually_mem D hst.omega_ne h0 h14] with n hn z hz
    exact ⟨D.mu n z, hn z hz, rfl⟩

/-- Reduction of `itOld` and `Integrable (itOldDens ...)` on `(0, ∞)` to `(u_o, ∞)` when the
density is `2 Re(a · F s)` on `[u_o, ∞)` and `0` on `(-∞, u_o)`. -/
theorem itOld_and_integrable_of_onset {S : FlatSetting} {ν : ℝ} (hν : 0 < ν)
    {ξ : ℝ → S.pk.X} {F : ℝ → ℂ} (a : ℂ)
    (hF_int : IntegrableOn F (Ioi (IIIa.onsetAge ν)))
    (hdens : ∀ s : ℝ, ν ^ (-(3 / 2 : ℝ)) ≤ s → itOldDens S ν ξ s = 2 * (a * F s).re) :
    Integrable (itOldDens S ν ξ) (volume.restrict (Ioi (0 : ℝ))) ∧
      itOld S ν ξ = 2 * (a * ∫ s in Ioi (IIIa.onsetAge ν), F s).re := by
  have huo_eq : ν ^ (-(3 / 2 : ℝ)) = IIIa.onsetAge ν := by
    unfold IIIa.onsetAge; congr 1; norm_num
  have huo_pos : 0 < IIIa.onsetAge ν := by
    unfold IIIa.onsetAge; exact Real.rpow_pos_of_pos hν _
  have hsub : Ici (IIIa.onsetAge ν) ⊆ Ioi (0 : ℝ) :=
    fun _ hs => lt_of_lt_of_le huo_pos hs
  have h_ind : itOldDens S ν ξ =
      (Ici (IIIa.onsetAge ν)).indicator (fun s => 2 * (a * F s).re) := by
    ext s
    by_cases hmem : s ∈ Ici (IIIa.onsetAge ν)
    · rw [indicator_of_mem hmem]
      exact hdens s (huo_eq.trans_le hmem)
    · rw [indicator_of_notMem hmem]
      have hnle : ¬ ν ^ (-(3 / 2 : ℝ)) ≤ s := by
        rw [huo_eq]; exact hmem
      unfold itOldDens FlatSetting.ITdens
      simp [ite_eq_right_iff.2 fun h => (hnle h).elim, cellInt]
  have hmeas_eq : (volume : Measure ℝ).restrict (Ici (IIIa.onsetAge ν)) =
      (volume : Measure ℝ).restrict (Ioi (IIIa.onsetAge ν)) :=
    Measure.restrict_congr_set Ioi_ae_eq_Ici.symm
  have hRe_int_on : IntegrableOn (fun s => 2 * (a * F s).re) (Ici (IIIa.onsetAge ν)) := by
    unfold IntegrableOn
    rw [hmeas_eq]
    have h1 : Integrable (fun s => a * F s) (volume.restrict (Ioi (IIIa.onsetAge ν))) :=
      hF_int.const_mul a
    have h2 : Integrable (fun s => (a * F s).re) (volume.restrict (Ioi (IIIa.onsetAge ν))) :=
      Complex.reCLM.integrable_comp h1
    exact h2.const_mul 2
  have hInd_int : Integrable ((Ici (IIIa.onsetAge ν)).indicator (fun s => 2 * (a * F s).re))
      (volume.restrict (Ioi (0 : ℝ))) := by
    rw [integrable_indicator_iff measurableSet_Ici]
    unfold IntegrableOn at hRe_int_on ⊢
    rw [Measure.restrict_restrict measurableSet_Ici, inter_eq_self_of_subset_left hsub]
    exact hRe_int_on
  have hint : Integrable (itOldDens S ν ξ) (volume.restrict (Ioi (0 : ℝ))) := by
    rw [h_ind]; exact hInd_int
  refine ⟨hint, ?_⟩
  change (∫ s in Ioi (0 : ℝ), itOldDens S ν ξ s) = _
  have hre_comm := Complex.reCLM.integral_comp_comm (hF_int.const_mul a)
  simp only [Complex.reCLM_apply] at hre_comm
  rw [h_ind, integral_indicator measurableSet_Ici,
    Measure.restrict_restrict measurableSet_Ici, inter_eq_self_of_subset_left hsub,
    hmeas_eq, integral_const_mul, hre_comm, integral_const_mul]

/-- Transport of `CTAnisoMellin` along `c = ν ^ (-2 : ℝ)`. -/
private theorem ctAnisoMellin_at_c {P : UnforcedLeray.Blueprint.Planar.PlanarData}
    {ν m ε₀ : ℝ} {K : Set ℂ}
    (hCT_n : ∀ tr : UnforcedLeray.B0140.TrainSol ν (ν ^ (-2 : ℝ)),
      UnforcedLeray.Short.PartI.IsBUCTrain tr →
      ∀ w u, IIIa.IsLinearisedFlow ν (ν ^ (-2 : ℝ)) m tr 0 (IIIa.preparedDatum P ν) w u →
        ∀ μ ∈ K,
          IntegrableOn (fun s => (2 * IIIa.pairQ tr μ (u s) s - IIIa.pairEta tr μ (u s) s) *
              ((s ^ (-3 / 2 : ℝ) : ℝ) : ℂ)) (Ioi (IIIa.onsetAge ν)) ∧
            ‖(∫ s in Ioi (IIIa.onsetAge ν), (2 * IIIa.pairQ tr μ (u s) s -
                IIIa.pairEta tr μ (u s) s) * ((s ^ (-3 / 2 : ℝ) : ℝ) : ℂ)) -
              3 * Complex.I * (μ + 3 / 2) *
                (-((Real.pi : ℝ) : ℂ) * P.gaugeFactor ν /
                  (4 * ((ν ^ (-2 : ℝ) : ℝ) : ℂ)) * (ν : ℂ) ^ (3 + 2 * μ)) *
                IIIa.mellinJc P μ‖ ≤ ε₀ * IIIa.scaleA P ν μ)
    {c : ℝ} (hc : c = ν ^ (-2 : ℝ))
    (tr : UnforcedLeray.B0140.TrainSol ν c) (hbuc : UnforcedLeray.Short.PartI.IsBUCTrain tr)
    {w u} (hflow : IIIa.IsLinearisedFlow ν c m tr 0 (IIIa.preparedDatum P ν) w u)
    {μ : ℂ} (hμ : μ ∈ K) :
    IntegrableOn (fun s => (2 * pairQ_c tr μ (u s) s - pairEta_c tr μ (u s) s) *
        ((s ^ (-3 / 2 : ℝ) : ℝ) : ℂ)) (Ioi (IIIa.onsetAge ν)) ∧
      ‖(∫ s in Ioi (IIIa.onsetAge ν), (2 * pairQ_c tr μ (u s) s -
          pairEta_c tr μ (u s) s) * ((s ^ (-3 / 2 : ℝ) : ℝ) : ℂ)) -
        3 * Complex.I * (μ + 3 / 2) *
          (-((Real.pi : ℝ) : ℂ) * P.gaugeFactor ν /
            (4 * ((ν ^ (-2 : ℝ) : ℝ) : ℂ)) * (ν : ℂ) ^ (3 + 2 * μ)) *
          IIIa.mellinJc P μ‖ ≤ ε₀ * IIIa.scaleA P ν μ := by
  subst hc
  exact hCT_n tr hbuc w u hflow μ hμ

/-! ## 5. Conditional assembly `bareColUnit_of_leaves` -/

/-- **Conditional assembly of `BareColUnit D`** from `CTMellin`, `CTAnisotropy`,
`FullClockLongForward`, `LaterOutputRem`, and the four leaves `BareCellAdd`, `BareCanFlowVel`,
`PreparedDatumCompare`, `BandForwardAtH`.
Composed by `PartIII-b:IIIb-D3/2/G3/1/4` (`OldAnisoBare.lean`). -/
theorem bareColUnit_of_leaves (D : SeqData)
    (hM : IIIa.CTMellin)
    (hA : IIIa.CTAnisotropy)
    (_hL : IIIa.FullClockLongForward)
    (hRem : LaterOutputRem D)
    (hCell : BareCellAdd)
    (hFlow : BareCanFlowVel)
    (hPrep : PreparedDatumCompare D)
    (hFwd : BandForwardAtH D) :
    BareColUnit D := by
  have hCT : CTAnisoMellin := ctAnisoMellin_of hM hA
  intro dm dp hst κ hκ m _ hm S hS
  obtain ⟨K, hK_adm, hK_mu⟩ := exists_admissibleK_for_mu D hst
  obtain ⟨Crem, Nrem, hCrem0, hNrem⟩ := hRem dm dp hst κ hκ m hm S hS
  obtain ⟨Cprep, νprep, hCprep0, hνprep, hPrep_bd⟩ := hPrep dm dp hst κ hκ m hm
  obtain ⟨Cfwd, νfwd, hCfwd0, hνfwd, hFwd_bd⟩ := hFwd dm dp hst κ hκ m hm
  have hν_tend : Tendsto (nu D) atTop (𝓝 0) := retNu_tendsto D.σ₀ hst.omega_ne
  have hν_nhds : Tendsto (nu D) atTop (𝓝[>] (0 : ℝ)) :=
    tendsto_nhdsWithin_iff.2 ⟨hν_tend, Eventually.of_forall fun n => retNu_pos D.Pl D.σ₀ n⟩
  -- For integrability, invoke `hCT` at `ε = 1`
  have hCT1 := hν_nhds.eventually (hCT D.Pl hst.planar m hm K hK_adm 1 one_pos)
  have hev_base : ∀ᶠ n : ℕ in atTop,
      (∃ FI : FlatInstData κ (nu D n) (cOf (nu D n)) m (D.train n),
        S n = levelFlat (retNu_pos D.Pl D.σ₀ n) FI D.K.χo (retEps D.Pl D.σ₀ n)) ∧
      nu D n ≤ min (min νprep νfwd) (1 / 4) ∧
      (∀ z ∈ Icc (-1 : ℝ) 1, (D.mu n z : ℂ) ∈ K) := by
    have hν_small : ∀ᶠ n : ℕ in atTop, nu D n ≤ min (min νprep νfwd) (1 / 4) := by
      have hpos : 0 < min (min νprep νfwd) (1 / 4) :=
        lt_min (lt_min hνprep hνfwd) (by norm_num)
      filter_upwards [hν_tend.eventually (gt_mem_nhds hpos)] with n hn
      exact hn.le
    exact hS.and (hν_small.and hK_mu)
  -- Per-level helper for any `a : ℂ` and `ε₀ > 0` once `hCT` holds at `ε₀`
  have h_unit_step : ∀ {n : ℕ} {ε₀ : ℝ},
      n ≥ Nrem →
      (∃ FI : FlatInstData κ (nu D n) (cOf (nu D n)) m (D.train n),
        S n = levelFlat (retNu_pos D.Pl D.σ₀ n) FI D.K.χo (retEps D.Pl D.σ₀ n)) →
      nu D n ≤ min (min νprep νfwd) (1 / 4) →
      (∀ z ∈ Icc (-1 : ℝ) 1, (D.mu n z : ℂ) ∈ K) →
      (∀ tr : UnforcedLeray.B0140.TrainSol (nu D n) ((nu D n) ^ (-2 : ℝ)),
        UnforcedLeray.Short.PartI.IsBUCTrain tr →
        ∀ w u, IIIa.IsLinearisedFlow (nu D n) ((nu D n) ^ (-2 : ℝ)) m tr 0
            (IIIa.preparedDatum D.Pl (nu D n)) w u →
          ∀ μ ∈ K,
            IntegrableOn (fun s => (2 * IIIa.pairQ tr μ (u s) s - IIIa.pairEta tr μ (u s) s) *
                ((s ^ (-3 / 2 : ℝ) : ℝ) : ℂ)) (Ioi (IIIa.onsetAge (nu D n))) ∧
              ‖(∫ s in Ioi (IIIa.onsetAge (nu D n)), (2 * IIIa.pairQ tr μ (u s) s -
                  IIIa.pairEta tr μ (u s) s) * ((s ^ (-3 / 2 : ℝ) : ℝ) : ℂ)) -
                3 * Complex.I * (μ + 3 / 2) *
                  (-((Real.pi : ℝ) : ℂ) * D.Pl.gaugeFactor (nu D n) /
                    (4 * (((nu D n) ^ (-2 : ℝ) : ℝ) : ℂ)) * (nu D n : ℂ) ^ (3 + 2 * μ)) *
                  IIIa.mellinJc D.Pl μ‖ ≤ ε₀ * IIIa.scaleA D.Pl (nu D n) μ) →
      ∀ z ∈ Icc (-1 : ℝ) 1, ∀ a : ℂ,
        Integrable (itOldDens (S n) (nu D n) (xiBare (S n) (D.mu n z) a))
          (volume.restrict (Ioi (0 : ℝ))) ∧
        |itOld (S n) (nu D n) (xiBare (S n) (D.mu n z) a) - bareColLead D (S n) n z a| ≤
          (2 * ‖a‖ * ε₀ + 2 * ‖a‖ * Crem * Cfwd * Cprep * nu D n) *
            oldScaleA D (S n) n z := by
    intro n ε₀ hnrem ⟨FI, hFI⟩ hν_le hK_z hCT_n z hz a
    have hrem_z := hNrem n hnrem z hz
    rw [hFI] at hrem_z ⊢
    set ν := nu D n
    have hν : 0 < ν := retNu_pos D.Pl D.σ₀ n
    have : Fact (0 < cOf ν) := ⟨cOf_pos hν⟩
    have hν_prep : ν ≤ νprep := hν_le.trans ((min_le_left _ _).trans (min_le_left _ _))
    have hν_fwd : ν ≤ νfwd := hν_le.trans ((min_le_left _ _).trans (min_le_right _ _))
    have hν4 : ν ≤ 1 / 4 := hν_le.trans (min_le_right _ _)
    have hν9 : ν ≤ 4 / 9 := hν4.trans (by norm_num)
    let F_flat := levelFlat hν FI D.K.χo (retEps D.Pl D.σ₀ n)
    obtain ⟨qc, hqc_ae, hqc_bd⟩ := hPrep_bd ν hν hν_prep (D.train n) FI
    let q0 : F_flat.pk.X := qc
    obtain ⟨w, u, hflow, hkc_ae⟩ :=
      hFlow D.Pl κ ν hν m (D.train n) FI D.K.χo (retEps D.Pl D.σ₀ n) (D.mu n z) q0 hqc_ae
    have hc_eq : cOf ν = ν ^ (-2 : ℝ) := cOf_eq_rpow hν
    have hCT_inst :=
      ctAnisoMellin_at_c hCT_n hc_eq (D.train n) (D.train_buc n) hflow (hK_z z hz)
    set F_can : ℝ → ℂ := fun s =>
      (2 * pairQ_c (D.train n) (D.mu n z : ℂ) (u s) s -
        pairEta_c (D.train n) (D.mu n z : ℂ) (u s) s) *
        ((s ^ (-3 / 2 : ℝ) : ℝ) : ℂ)
    have hdens_can : ∀ s : ℝ, ν ^ (-(3 / 2 : ℝ)) ≤ s →
        itOldDens F_flat ν (xiBareOf F_flat q0 (D.mu n z) a) s = 2 * (a * F_can s).re := by
      intro s hs
      have hs0 : 0 ≤ s := (Real.rpow_pos_of_pos hν _).le.trans hs
      have hu_lp : ∀ i, MemLp (fun p => u s p i) 2 (volume.restrict (B0579.cell (cOf ν))) :=
        (hflow.biotSavart s hs0).1
      exact itOldDens_eq_of_kcMer_ae hν hν9 FI D.K.hχo (retEps D.Pl D.σ₀ n) (D.mu n z)
        (xiBareOf F_flat q0 (D.mu n z) a) u a hs hu_lp (hkc_ae a s hs0)
    obtain ⟨hint_can, hit_can⟩ :=
      itOld_and_integrable_of_onset hν a hCT_inst.1 hdens_can
    have hc_F : F_flat.c = cOf ν := rfl
    have hlead_eq := two_re_anisoLead_eq_bareColLead D F_flat n z a hc_F
    have hscale_eq := scaleA_eq_oldScaleA D F_flat n z hc_F
    have hbd_can : |itOld F_flat ν (xiBareOf F_flat q0 (D.mu n z) a) - bareColLead D F_flat n z a| ≤
        2 * ‖a‖ * ε₀ * oldScaleA D F_flat n z := by
      rw [hit_can, ← hlead_eq]
      set I_can := ∫ s in Ioi (IIIa.onsetAge ν), F_can s
      set L_can := 3 * Complex.I * ((D.mu n z : ℂ) + 3 / 2) *
        (-((Real.pi : ℝ) : ℂ) * D.Pl.gaugeFactor ν /
          (4 * ((ν ^ (-2 : ℝ) : ℝ) : ℂ)) * (ν : ℂ) ^ (3 + 2 * (D.mu n z : ℂ))) *
        IIIa.mellinJc D.Pl (D.mu n z : ℂ)
      have hsub : 2 * (a * I_can).re - 2 * (a * L_can).re =
          2 * (a * (I_can - L_can)).re := by
        rw [mul_sub, Complex.sub_re]
        ring
      rw [hsub, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
      have hre_le : |(a * (I_can - L_can)).re| ≤ ‖a‖ * ‖I_can - L_can‖ :=
        (Complex.abs_re_le_norm _).trans_eq (norm_mul a _)
      calc 2 * |(a * (I_can - L_can)).re|
          ≤ 2 * (‖a‖ * ‖I_can - L_can‖) := mul_le_mul_of_nonneg_left hre_le zero_le_two
        _ ≤ 2 * (‖a‖ * (ε₀ * IIIa.scaleA D.Pl ν (D.mu n z : ℂ))) :=
            mul_le_mul_of_nonneg_left
              (mul_le_mul_of_nonneg_left hCT_inst.2 (norm_nonneg a)) zero_le_two
        _ = 2 * ‖a‖ * ε₀ * oldScaleA D F_flat n z := by rw [hscale_eq]; ring
    -- Now bound the remainder at `H = 2/ν`
    set rH : F_flat.pk.X := bareRemAtH F_flat ν q0 a
    obtain ⟨hint_rem, hbd_rem⟩ := hrem_z rH
    have hrH_norm : ‖rH‖ ≤
        2 * ‖a‖ * Cfwd * Cprep * ν * ‖Fpm true D.Pl.eigenvalue D.Pl.kappa ν (2 / ν) 0‖ := by
      have hL_flat : YoungLaws F_flat.pk F_flat.conjX := youngLaws_actualPk FI
      have h1 := norm_bareRemAtH_le hL_flat ν q0 a
      have h2 := hFwd_bd ν hν hν_fwd (D.train n) (D.train_buc n) FI (FI.pair.q true 0 - qc)
      have h3 : ‖FI.ev.U (2 / ν) 0 (FI.pair.q true 0 - qc)‖ ≤
          Cfwd * ‖Fpm true D.Pl.eigenvalue D.Pl.kappa ν (2 / ν) 0‖ * (Cprep * ν) :=
        h2.trans (mul_le_mul_of_nonneg_left hqc_bd
          (mul_nonneg hCfwd0 (norm_nonneg _)))
      calc ‖rH‖
          ≤ 2 * ‖a‖ * (Cfwd * ‖Fpm true D.Pl.eigenvalue D.Pl.kappa ν (2 / ν) 0‖ * (Cprep * ν)) :=
            h1.trans (mul_le_mul_of_nonneg_left h3 (mul_nonneg zero_le_two (norm_nonneg a)))
        _ = 2 * ‖a‖ * Cfwd * Cprep * ν * ‖Fpm true D.Pl.eigenvalue D.Pl.kappa ν (2 / ν) 0‖ := by ring
    have hA0 : 0 ≤ oldScaleA D F_flat n z := by
      unfold oldScaleA
      rw [hc_F]
      exact div_nonneg (mul_nonneg (norm_nonneg _) (Real.rpow_nonneg hν.le _)) (cOf_pos hν).le
    have hFne : ‖Fpm true D.Pl.eigenvalue D.Pl.kappa ν (2 / ν) 0‖ ≠ 0 :=
      norm_ne_zero_iff.2 ((fpm_facts ν hν D.Pl.eigenvalue D.Pl.kappa (2 / ν) 0
        (by positivity) le_rfl).2.1 true)
    have hbd_rem' : |itOld F_flat ν (xiFromH F_flat ν (D.mu n z) rH)| ≤
        (2 * ‖a‖ * Crem * Cfwd * Cprep * ν) * oldScaleA D F_flat n z := by
      have h1 : Crem * oldScaleA D F_flat n z *
            (‖Fpm true D.Pl.eigenvalue D.Pl.kappa ν (2 / ν) 0‖⁻¹ * ‖rH‖) ≤
          Crem * oldScaleA D F_flat n z *
            (‖Fpm true D.Pl.eigenvalue D.Pl.kappa ν (2 / ν) 0‖⁻¹ *
              (2 * ‖a‖ * Cfwd * Cprep * ν * ‖Fpm true D.Pl.eigenvalue D.Pl.kappa ν (2 / ν) 0‖)) :=
        mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left hrH_norm (inv_nonneg.2 (norm_nonneg _)))
          (mul_nonneg hCrem0 hA0)
      have h2 : Crem * oldScaleA D F_flat n z *
            (‖Fpm true D.Pl.eigenvalue D.Pl.kappa ν (2 / ν) 0‖⁻¹ *
              (2 * ‖a‖ * Cfwd * Cprep * ν * ‖Fpm true D.Pl.eigenvalue D.Pl.kappa ν (2 / ν) 0‖)) =
          (2 * ‖a‖ * Crem * Cfwd * Cprep * ν) * oldScaleA D F_flat n z := by
        calc Crem * oldScaleA D F_flat n z *
              (‖Fpm true D.Pl.eigenvalue D.Pl.kappa ν (2 / ν) 0‖⁻¹ *
                (2 * ‖a‖ * Cfwd * Cprep * ν * ‖Fpm true D.Pl.eigenvalue D.Pl.kappa ν (2 / ν) 0‖))
            = (2 * ‖a‖ * Crem * Cfwd * Cprep * ν) * oldScaleA D F_flat n z *
                (‖Fpm true D.Pl.eigenvalue D.Pl.kappa ν (2 / ν) 0‖⁻¹ *
                  ‖Fpm true D.Pl.eigenvalue D.Pl.kappa ν (2 / ν) 0‖) := by ring
          _ = (2 * ‖a‖ * Crem * Cfwd * Cprep * ν) * oldScaleA D F_flat n z := by
              rw [inv_mul_cancel₀ hFne, mul_one]
      exact hbd_rem.trans (h1.trans_eq h2)
    -- Split `itOldDens F_flat ν (xiBare F_flat (D.mu n z) a)` via `BareCellAdd`
    have huo : 2 / ν ≤ ν ^ (-(3 / 2 : ℝ)) := two_div_le_uo hν hν4
    have hdens_split : ∀ s : ℝ,
        itOldDens F_flat ν (xiBare F_flat (D.mu n z) a) s =
          itOldDens F_flat ν (xiBareOf F_flat q0 (D.mu n z) a) s +
          itOldDens F_flat ν (xiFromH F_flat ν (D.mu n z) rH) s := by
      intro s
      unfold itOldDens FlatSetting.ITdens
      by_cases hs : ν ^ (-(3 / 2 : ℝ)) ≤ s
      · simp only [ite_eq_left_iff.2 fun h => (h hs).elim]
        have hL_flat : YoungLaws F_flat.pk F_flat.conjX := youngLaws_actualPk FI
        rw [xiBare_eq_xiBareOf_add_xiFromH hL_flat q0 hν (D.mu n z) a (huo.trans hs),
          hCell κ ν hν m (D.train n) FI D.K.χo (retEps D.Pl D.σ₀ n) s]
        ring
      · simp only [ite_eq_right_iff.2 fun h => (hs h).elim, cellInt, Matrix.zero_apply,
          mul_zero, sub_self, integral_zero, add_zero]
    have hint_bare : Integrable (itOldDens F_flat ν (xiBare F_flat (D.mu n z) a))
        (volume.restrict (Ioi (0 : ℝ))) := by
      rw [funext hdens_split]
      exact hint_can.add hint_rem
    have hit_split : itOld F_flat ν (xiBare F_flat (D.mu n z) a) =
        itOld F_flat ν (xiBareOf F_flat q0 (D.mu n z) a) +
        itOld F_flat ν (xiFromH F_flat ν (D.mu n z) rH) := by
      change (∫ s in Ioi (0 : ℝ), itOldDens F_flat ν (xiBare F_flat (D.mu n z) a) s) = _
      rw [funext hdens_split, integral_add hint_can hint_rem]
      rfl
    refine ⟨hint_bare, ?_⟩
    rw [hit_split]
    have htri : |itOld F_flat ν (xiBareOf F_flat q0 (D.mu n z) a) +
          itOld F_flat ν (xiFromH F_flat ν (D.mu n z) rH) - bareColLead D F_flat n z a| ≤
        |itOld F_flat ν (xiBareOf F_flat q0 (D.mu n z) a) - bareColLead D F_flat n z a| +
        |itOld F_flat ν (xiFromH F_flat ν (D.mu n z) rH)| := by
      have heq : itOld F_flat ν (xiBareOf F_flat q0 (D.mu n z) a) +
          itOld F_flat ν (xiFromH F_flat ν (D.mu n z) rH) - bareColLead D F_flat n z a =
        (itOld F_flat ν (xiBareOf F_flat q0 (D.mu n z) a) - bareColLead D F_flat n z a) +
          itOld F_flat ν (xiFromH F_flat ν (D.mu n z) rH) := by ring
      rw [heq]
      exact abs_add_le _ _
    calc |itOld F_flat ν (xiBareOf F_flat q0 (D.mu n z) a) +
          itOld F_flat ν (xiFromH F_flat ν (D.mu n z) rH) - bareColLead D F_flat n z a|
        ≤ 2 * ‖a‖ * ε₀ * oldScaleA D F_flat n z +
          (2 * ‖a‖ * Crem * Cfwd * Cprep * ν) * oldScaleA D F_flat n z :=
          htri.trans (add_le_add hbd_can hbd_rem')
      _ = (2 * ‖a‖ * ε₀ + 2 * ‖a‖ * Crem * Cfwd * Cprep * ν) * oldScaleA D F_flat n z := by ring
  -- Part 1: Integrability for `a = 1` and `a = i`
  obtain ⟨N0, hN0⟩ := eventually_atTop.1 (hev_base.and hCT1)
  refine ⟨⟨max Nrem N0, fun n hn z hz => ?_⟩, fun ε hε => ?_⟩
  · have hnrem : Nrem ≤ n := le_trans (le_max_left _ _) hn
    have hn0 : N0 ≤ n := le_trans (le_max_right _ _) hn
    obtain ⟨⟨hFI, hν_le, hK_z⟩, hCT_n⟩ := hN0 n hn0
    exact ⟨(h_unit_step hnrem hFI hν_le hK_z hCT_n z hz 1).1,
      (h_unit_step hnrem hFI hν_le hK_z hCT_n z hz Complex.I).1⟩
  · -- Part 2: `ε` bound for `a = 1` and `a = i`
    set ε₀ : ℝ := ε / 4
    have hε₀ : 0 < ε₀ := by positivity
    have hCT_ε := hν_nhds.eventually (hCT D.Pl hst.planar m hm K hK_adm ε₀ hε₀)
    have hν_rem : ∀ᶠ n : ℕ in atTop, 2 * Crem * Cfwd * Cprep * nu D n ≤ ε / 2 := by
      set M_rem : ℝ := 2 * Crem * Cfwd * Cprep + 1
      have hM_pos : 0 < M_rem := by positivity
      filter_upwards [hν_tend.eventually (gt_mem_nhds (div_pos (half_pos hε) hM_pos))] with n hn
      have hν0 : 0 ≤ nu D n := (retNu_pos D.Pl D.σ₀ n).le
      have h1 : 2 * Crem * Cfwd * Cprep * nu D n ≤ M_rem * nu D n := by
        unfold M_rem; linarith
      have h2 : M_rem * nu D n ≤ M_rem * ((ε / 2) / M_rem) :=
        mul_le_mul_of_nonneg_left hn.le hM_pos.le
      rw [mul_div_cancel₀ _ hM_pos.ne'] at h2
      exact h1.trans h2
    filter_upwards [eventually_ge_atTop Nrem, hev_base, hCT_ε, hν_rem] with
      n hnrem ⟨hFI, hν_le, hK_z⟩ hCT_n hrem_n z hz
    have hA0 : 0 ≤ oldScaleA D (S n) n z := by
      obtain ⟨FI, hFI'⟩ := hFI
      have hc_S : (S n).c = cOf (nu D n) := by rw [hFI']; rfl
      unfold oldScaleA
      rw [hc_S]
      have hν : 0 < nu D n := retNu_pos D.Pl D.σ₀ n
      exact div_nonneg (mul_nonneg (norm_nonneg _) (Real.rpow_nonneg hν.le _)) (cOf_pos hν).le
    have h1 := (h_unit_step hnrem hFI hν_le hK_z hCT_n z hz 1).2
    have hI := (h_unit_step hnrem hFI hν_le hK_z hCT_n z hz Complex.I).2
    rw [norm_one, mul_one] at h1
    rw [Complex.norm_I, mul_one] at hI
    have hcoeff : 2 * ε₀ + 2 * Crem * Cfwd * Cprep * nu D n ≤ ε := by
      unfold ε₀; linarith
    exact ⟨h1.trans (mul_le_mul_of_nonneg_right hcoeff hA0),
      hI.trans (mul_le_mul_of_nonneg_right hcoeff hA0)⟩

end G3

end UnforcedLeray.Short.PartIIIb.Concrete.FlatUnif

end
