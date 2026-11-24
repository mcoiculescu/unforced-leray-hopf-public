import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_IIIb_D3_2.G1.LaterOutput.Tail
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_asrc_kflat_1_2_2_1
import UnforcedLeray.Short.PartIIIa.FullClock
import UnforcedLeray.Short.PartIIIa.CanonicalTransfer
import UnforcedLeray.Short.PartI.StatementsTrain
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

/-!
# Decomposition of `PartIII-b:IIIb-D3/2/G1/5/2` (`G1.LaterOutput.TailBound`)

Source of record: `the November 2 reference manuscript`:
* lines 4432-4460 (`eq:young-later-output` 4454: propagation of a state at `H = 2/ν` to the
  long-clock age `b` by `eq:short-causal-long-forward` 4440-4448, uniform Biot-Savart embedding at
  `d(b) ≥ 1`, and the impulse estimates at `r = b` 4449-4455);
* lines 314-317 (`sct:integrated`: BUC train cell `L²` velocity decay before and after overlap);
* lines 3228-3240 (`eq:ct-embeddings`) and 3242-3251, 3275-3284 (`eq:ct-kinetic-impulse` and
  `eq:ct-absolute-impulse` at `r = b`).

This file states the three pointwise velocity/flow bounds on `s ≥ 2/ν`:
1. `TrainVelTailBound D` (target of `PartIII-b:IIIb-D3/2/G1/5/2/1`, from `PartI.TrainL2Decay`):
   on `2/ν ≤ s ≤ ν⁻²`, `‖v(s)‖_{L²(cell c)} ≤ C_v (ν s)⁻¹`; on all `s ≥ 2/ν`,
   `‖v(s)‖_{L²(cell c)} ≤ C_v ((ν s)⁻¹ + ν^{1/4} s^{-3/4})`.
2. `UnforcedFlowKcCoreBound D` (target of `PartIII-b:IIIb-D3/2/G1/5/2/2`, from
   `IIIa.FullClockLongForward`, `eq:ct-embeddings`, and `J_a⁻¹` scaling at `a(2/ν) = 3`):
   for `2/ν ≤ s ≤ IIIa.coreEnd ν b`, the exponential factor `e^{-γ θ(s)} θ(s)^{-Re κ}` on
   `θ(s) ≥ b` bounds `‖kcLp (𝒰(s, 2/ν) w)‖` by
   `C_u ν^9 s^4 |N_ν| |F_+(2/ν, 0)|⁻¹ ‖w‖`.
3. `UnforcedFlowKcImpulseBound D` (target of `PartIII-b:IIIb-D3/2/G1/5/2/3`, from
   `IIIa.FullClockLongForward` at `s_b = IIIa.coreEnd ν b`, `eq:ct-embeddings` at `d(b) ≥ 1`, and
   `IIIa.CTKineticImpulse` on `0 < θ(s) ≤ b`):
   for `s ≥ IIIa.coreEnd ν b`, the factor `b / θ(s)` in `eq:ct-kinetic-impulse` cancels the
   heat-rescaling factor `a(s)⁻¹ = ν θ(s)`, giving the uniform bound
   `‖kcLp (𝒰(s, 2/ν) w)‖ ≤ C_u ν |N_ν| |F_+(2/ν, 0)|⁻¹ ‖w‖`.

Using the one-cell Cauchy-Schwarz inequality `slice_gen` (`Sub/PartIII-b_C_asrc_kflat_1_2_2_1.lean`)
and splitting the tail integral at `s_b = IIIa.coreEnd ν b`, we prove `unforcedTailImpulseBound_of`
and `tailBound_of_parts`.
-/

set_option autoImplicit false

noncomputable section

open Filter Topology Set MeasureTheory UnforcedLeray.Axi
open scoped ENNReal

namespace UnforcedLeray.Short.PartIIIb.Concrete.FlatUnif.G1.LaterOutput

open ConcreteYF FlatSettingInst

/-- **(Leaf 1) BUC train cell `L²` velocity bound on the tail `s ≥ 2/ν`** (source lines 314-317
`sct:integrated` and 3261-3264, 3281-3283: before overlap `‖v(s)‖₂ ≤ C (1 + νs)⁻¹ ≤ C (νs)⁻¹`,
which in particular holds on `2/ν ≤ s ≤ ν⁻²`; after overlap `s ≥ s_c ≈ ν⁻⁵`,
`‖v(s)‖₂ ≤ C c⁻² (s/s_c)^{-3/4} ≤ C ν^{1/4} s^{-3/4}`).
Target of `PartIII-b:IIIb-D3/2/G1/5/2/1`, composed by `PartIII-b:IIIb-D3/2/G1/5/2`. -/
def TrainVelTailBound (D : SeqData) : Prop :=
  ∀ (dm dp : ℝ), D.RepairStanding dm dp →
    ∃ (Cv : ℝ) (N : ℕ), 0 ≤ Cv ∧ ∀ n ≥ N, ∀ s : ℝ, 2 / nu D n ≤ s →
      (s ≤ (nu D n) ^ (-2 : ℝ) →
        UnforcedLeray.Train.cellL2 (cOf (nu D n)) ((D.train n).v s) ≤
          ENNReal.ofReal (Cv * (nu D n * s)⁻¹)) ∧
      UnforcedLeray.Train.cellL2 (cOf (nu D n)) ((D.train n).v s) ≤
        ENNReal.ofReal (Cv * ((nu D n * s)⁻¹ + (nu D n) ^ (1 / 4 : ℝ) * s ^ (-(3 / 4 : ℝ))))

/-- **(Leaf 2) Unforced linearised flow `K_c` velocity bound on the core tail
`2/ν ≤ s ≤ IIIa.coreEnd ν b`** (source lines 4440-4450, 3020-3022 `eq:short-causal-long-forward`,
and 3228-3240 `eq:ct-embeddings`): on `b ≤ θ(s) ≤ 1/(3ν)`, `a(s)⁻¹ = ν θ(s)`,
`e^{γ θ(2/ν)} θ(2/ν)^{Re κ} = |N_ν| |F_+(2/ν, 0)|⁻¹`, and the exponential decay
`θ(s) e^{-γ θ(s)} θ(s)^{-Re κ} ≤ C_b θ(s)^{-4} ≤ 16 C_b ν^8 s^4` gives
`‖kcLp (𝒰(s, 2/ν) w)‖ ≤ C_u ν^9 s^4 |N_ν| |F_+(2/ν, 0)|⁻¹ ‖w‖`.
Target of `PartIII-b:IIIb-D3/2/G1/5/2/2`, composed by `PartIII-b:IIIb-D3/2/G1/5/2`. -/
def UnforcedFlowKcCoreBound (D : SeqData) : Prop :=
  ∀ (dm dp : ℝ), D.RepairStanding dm dp → ∀ κ : IIIa.PlanarFrameKernels, SeedLink D κ →
    ∀ (m : ℝ) [Fact (1 < m)], 8 < m →
    ∃ b₀ : ℝ, 1 ≤ b₀ ∧ ∀ b : ℝ, b₀ ≤ b →
      ∃ (Cu : ℝ) (N : ℕ), 0 ≤ Cu ∧ ∀ n ≥ N,
        ∀ (FI : FlatInstData κ (nu D n) (cOf (nu D n)) m (D.train n)),
        haveI : Fact (0 < cOf (nu D n)) := ⟨cOf_pos (retNu_pos D.Pl D.σ₀ n)⟩
        ∀ w : Xmc (cOf (nu D n)) m, ∀ s : ℝ,
          2 / nu D n ≤ s → s ≤ IIIa.coreEnd (nu D n) b →
            ‖kcLp (FI.ev.U s (2 / nu D n) w)‖ ≤
              Cu * (nu D n) ^ 9 * s ^ 4 *
                (‖Nnu D.Pl.eigenvalue D.Pl.kappa (nu D n)‖ *
                  (‖Fpm true D.Pl.eigenvalue D.Pl.kappa (nu D n) (2 / nu D n) 0‖⁻¹ * ‖w‖))

/-- **(Leaf 3) Unforced linearised flow `K_c` velocity bound past the long clock
`s ≥ IIIa.coreEnd ν b`** (source lines 4440-4455, 3228-3240 `eq:ct-embeddings` at `d(b) ≥ 1`, and
3242-3251, 3281-3284 `eq:ct-kinetic-impulse` at `r = b`): propagating `w` from `2/ν` to
`s_b = IIIa.coreEnd ν b` via `FullClockLongForward` and then from `s_b` to `s ≥ s_b` (`0 < θ(s) ≤ b`)
via `CTKineticImpulse` cancels `b / θ(s)` against `a(s)⁻¹ = ν θ(s)` and gives
`‖kcLp (𝒰(s, 2/ν) w)‖ ≤ C_u ν |N_ν| |F_+(2/ν, 0)|⁻¹ ‖w‖`.
Target of `PartIII-b:IIIb-D3/2/G1/5/2/3`, composed by `PartIII-b:IIIb-D3/2/G1/5/2`. -/
def UnforcedFlowKcImpulseBound (D : SeqData) : Prop :=
  ∀ (dm dp : ℝ), D.RepairStanding dm dp → ∀ κ : IIIa.PlanarFrameKernels, SeedLink D κ →
    ∀ (m : ℝ) [Fact (1 < m)], 8 < m →
    ∃ b₀ : ℝ, 1 ≤ b₀ ∧ ∀ b : ℝ, b₀ ≤ b →
      ∃ (Cu : ℝ) (N : ℕ), 0 ≤ Cu ∧ ∀ n ≥ N,
        ∀ (FI : FlatInstData κ (nu D n) (cOf (nu D n)) m (D.train n)),
        haveI : Fact (0 < cOf (nu D n)) := ⟨cOf_pos (retNu_pos D.Pl D.σ₀ n)⟩
        ∀ w : Xmc (cOf (nu D n)) m, ∀ s : ℝ,
          IIIa.coreEnd (nu D n) b ≤ s →
            ‖kcLp (FI.ev.U s (2 / nu D n) w)‖ ≤
              Cu * nu D n *
                (‖Nnu D.Pl.eigenvalue D.Pl.kappa (nu D n)‖ *
                  (‖Fpm true D.Pl.eigenvalue D.Pl.kappa (nu D n) (2 / nu D n) 0‖⁻¹ * ‖w‖))

/-! ## One-cell Cauchy-Schwarz reduction of `unforcedTailDens` -/

private lemma abs_entry_le_frob (A : Mat3) (i j : Fin 3) : |A i j| ≤ frob A := by
  unfold frob
  apply Real.abs_le_sqrt
  calc A i j ^ 2 ≤ ∑ j', A i j' ^ 2 :=
        Finset.single_le_sum (f := fun j' => A i j' ^ 2) (fun j' _ => sq_nonneg _) (Finset.mem_univ j)
    _ ≤ ∑ i', ∑ j', A i' j' ^ 2 :=
        Finset.single_le_sum (f := fun i' => ∑ j', A i' j' ^ 2)
          (fun i' _ => Finset.sum_nonneg fun _ _ => sq_nonneg _)
          (Finset.mem_univ i)

private lemma matNorm_le_nine_frob (A : Mat3) : matNorm A ≤ 9 * frob A := by
  unfold matNorm
  calc ∑ i : Fin 3, ∑ j : Fin 3, |A i j|
      ≤ ∑ _i : Fin 3, ∑ _j : Fin 3, frob A :=
        Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => abs_entry_le_frob A i j
    _ = 9 * frob A := by
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        ring

private lemma cellInt_eq_integral_avgμ {c : ℝ} (hc : 0 ≤ c) (F : ℝ × ℝ → ℝ) :
    cellInt c F = ∫ p, F p ∂(UnforcedLeray.Cyl.avgμ c) := by
  rw [UnforcedLeray.Cyl.integral_avgμ hc F, cellInt, smul_eq_mul]
  congr 1
  have hmeas : (volume : Measure (ℝ × ℝ)).restrict (Ioo (-c / 2) (c / 2) ×ˢ univ) =
      (volume : Measure (ℝ × ℝ)).restrict (UnforcedLeray.Cyl.cell c) := by
    rw [UnforcedLeray.Cyl.cell, Measure.volume_eq_prod, ← Measure.prod_restrict,
      ← Measure.prod_restrict, Measure.restrict_univ, Measure.restrict_congr_set Ioo_ae_eq_Ico]
  rw [hmeas]

private lemma ofReal_cellInt_symOuter_le {ν c m : ℝ} [Fact (1 < m)] [Fact (0 < c)]
    (tr : UnforcedLeray.B0140.TrainSol ν c) (s : ℝ) (y : Xmc c m) :
    ENNReal.ofReal (cellInt c (fun p =>
        matNorm (IIIa.symOuter (NearInst.trainMer tr (s, p)) (kcMer y p)))) ≤
      18 * ENNReal.ofReal c⁻¹ * UnforcedLeray.Train.cellL2 c (tr.v s) *
        ENNReal.ofReal ‖kcLp y‖ := by
  have hc : 0 < c := Fact.out
  set F : ℝ × ℝ → ℝ := fun p =>
    matNorm (IIIa.symOuter (NearInst.trainMer tr (s, p)) (kcMer y p))
  have hF0 : ∀ p, 0 ≤ F p := fun p =>
    Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => abs_nonneg _
  rw [cellInt_eq_integral_avgμ hc.le F]
  by_cases hInt : Integrable F (UnforcedLeray.Cyl.avgμ c)
  · rw [ofReal_integral_eq_lintegral_ofReal hInt (ae_of_all _ hF0)]
    have hpt : ∀ p, ENNReal.ofReal (F p) ≤
        ENNReal.ofReal 9 * ENNReal.ofReal (frob
          (IIIa.symOuter (NearInst.trainMer tr (s, p)) (kcMer y p))) := by
      intro p
      rw [← ENNReal.ofReal_mul (by norm_num)]
      exact ENNReal.ofReal_le_ofReal (matNorm_le_nine_frob _)
    calc ∫⁻ p, ENNReal.ofReal (F p) ∂(UnforcedLeray.Cyl.avgμ c)
        ≤ ∫⁻ p, ENNReal.ofReal 9 * ENNReal.ofReal (frob
            (IIIa.symOuter (NearInst.trainMer tr (s, p)) (kcMer y p)))
            ∂(UnforcedLeray.Cyl.avgμ c) := lintegral_mono hpt
      _ = ENNReal.ofReal 9 * ∫⁻ p, ENNReal.ofReal (frob
            (IIIa.symOuter (NearInst.trainMer tr (s, p)) (kcMer y p)))
            ∂(UnforcedLeray.Cyl.avgμ c) :=
          lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
      _ ≤ ENNReal.ofReal 9 * (2 * ENNReal.ofReal c⁻¹ *
            UnforcedLeray.Train.cellL2 c (tr.v s) * ENNReal.ofReal ‖kcLp y‖) := by
          gcongr
          exact slice_gen m tr s y
      _ = 18 * ENNReal.ofReal c⁻¹ * UnforcedLeray.Train.cellL2 c (tr.v s) *
            ENNReal.ofReal ‖kcLp y‖ := by
          rw [ENNReal.ofReal_ofNat]
          ring
  · rw [integral_undef hInt, ENNReal.ofReal_zero]
    exact bot_le

private lemma unforcedTailDens_le_of_bounds {κ : IIIa.PlanarFrameKernels} {ν m : ℝ}
    [Fact (1 < m)] [Fact (0 < cOf ν)] {tr : UnforcedLeray.B0140.TrainSol ν (cOf ν)}
    (FI : FlatInstData κ ν (cOf ν) m tr) (k : ℕ) (μ : ℝ) (w : Xmc (cOf ν) m)
    {s V K : ℝ} (hs : 0 < s) (hV0 : 0 ≤ V)
    (hV : UnforcedLeray.Train.cellL2 (cOf ν) (tr.v s) ≤ ENNReal.ofReal V)
    (hK : ‖kcLp (FI.ev.U s (2 / ν) w)‖ ≤ K) :
    ENNReal.ofReal (unforcedTailDens FI k μ w s) ≤
      ENNReal.ofReal (18 * (cOf ν)⁻¹ * s ^ (-(3 / 2 : ℝ) - (k : ℝ) / 2 - μ) * V * K) := by
  have hc : 0 < cOf ν := Fact.out
  have hK0 : 0 ≤ K := (norm_nonneg _).trans hK
  have hs1 : 0 ≤ s ^ (-(3 / 2 : ℝ) - (k : ℝ) / 2) := Real.rpow_nonneg hs.le _
  have hs2 : 0 ≤ s ^ (-μ) := Real.rpow_nonneg hs.le _
  have hpow : s ^ (-(3 / 2 : ℝ) - (k : ℝ) / 2) * s ^ (-μ) =
      s ^ (-(3 / 2 : ℝ) - (k : ℝ) / 2 - μ) := by
    rw [sub_eq_add_neg (-(3 / 2 : ℝ) - (k : ℝ) / 2) μ, Real.rpow_add hs]
  have hcell := ofReal_cellInt_symOuter_le tr s (FI.ev.U s (2 / ν) w)
  have hcell' : ENNReal.ofReal (cellInt (cOf ν) (fun p =>
        matNorm (IIIa.symOuter (NearInst.trainMer tr (s, p))
          (kcMer (FI.ev.U s (2 / ν) w) p)))) ≤
      ENNReal.ofReal (18 * (cOf ν)⁻¹ * V * K) := by
    calc ENNReal.ofReal (cellInt (cOf ν) (fun p =>
          matNorm (IIIa.symOuter (NearInst.trainMer tr (s, p))
            (kcMer (FI.ev.U s (2 / ν) w) p))))
        ≤ 18 * ENNReal.ofReal (cOf ν)⁻¹ * UnforcedLeray.Train.cellL2 (cOf ν) (tr.v s) *
            ENNReal.ofReal ‖kcLp (FI.ev.U s (2 / ν) w)‖ := hcell
      _ ≤ 18 * ENNReal.ofReal (cOf ν)⁻¹ * ENNReal.ofReal V * ENNReal.ofReal K := by
          gcongr
      _ = ENNReal.ofReal (18 * (cOf ν)⁻¹ * V * K) := by
          rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_mul (by positivity),
            ENNReal.ofReal_mul (by norm_num), ENNReal.ofReal_ofNat]
  unfold unforcedTailDens
  rw [ ← mul_assoc, hpow, ENNReal.ofReal_mul (by positivity)]
  calc ENNReal.ofReal (s ^ (-(3 / 2 : ℝ) - (k : ℝ) / 2 - μ)) *
        ENNReal.ofReal (cellInt (cOf ν) (fun p =>
          matNorm (IIIa.symOuter (NearInst.trainMer tr (s, p))
            (kcMer (FI.ev.U s (2 / ν) w) p))))
      ≤ ENNReal.ofReal (s ^ (-(3 / 2 : ℝ) - (k : ℝ) / 2 - μ)) *
          ENNReal.ofReal (18 * (cOf ν)⁻¹ * V * K) := by gcongr
    _ = ENNReal.ofReal (18 * (cOf ν)⁻¹ * s ^ (-(3 / 2 : ℝ) - (k : ℝ) / 2 - μ) * V * K) := by
        rw [← ENNReal.ofReal_mul (by positivity)]
        congr 1; ring

/-! ## Bounds on `IIIa.coreEnd ν b` and power integrals -/

private lemma coreEnd_bounds {ν b : ℝ} (hν : 0 < ν) (hb : 1 ≤ b) (hνb : ν * b ≤ 1 / 3) :
    2 / ν ≤ IIIa.coreEnd ν b ∧
    (2 * b)⁻¹ * ν ^ (-2 : ℝ) ≤ IIIa.coreEnd ν b ∧
    IIIa.coreEnd ν b ≤ ν ^ (-2 : ℝ) := by
  have hb0 : 0 < b := one_pos.trans_le hb
  have hνb0 : 0 < ν * b := mul_pos hν hb0
  have h3 : 3 ≤ (ν * b)⁻¹ := by
    rw [le_inv_comm₀ (by norm_num) hνb0]
    linarith
  have hpow2 : ν ^ (-2 : ℝ) = ν⁻¹ * ν⁻¹ := by
    rw [show (-2 : ℝ) = -1 + -1 by norm_num, Real.rpow_add hν, Real.rpow_neg_one]
  unfold IIIa.coreEnd
  refine ⟨?_, ?_, ?_⟩
  · rw [div_eq_inv_mul]
    exact mul_le_mul_of_nonneg_left (by linarith) (inv_nonneg.2 hν.le)
  · rw [hpow2, ← mul_assoc, mul_comm (2 * b)⁻¹ ν⁻¹, mul_assoc]
    refine mul_le_mul_of_nonneg_left ?_ (inv_nonneg.2 hν.le)
    have hinv : ν⁻¹ * (2 * b)⁻¹ = (1 / 2 : ℝ) * (ν * b)⁻¹ := by
      rw [mul_inv, mul_inv]; ring
    linarith
  · rw [hpow2]
    refine mul_le_mul_of_nonneg_left ?_ (inv_nonneg.2 hν.le)
    have hle : (ν * b)⁻¹ ≤ ν⁻¹ := inv_anti₀ hν (by nlinarith)
    linarith

private lemma lintegral_Ioi_rpow_eq {r a : ℝ} (hr : r < -1) (ha : 0 < a) :
    ∫⁻ s in Ioi a, ENNReal.ofReal (s ^ r) = ENNReal.ofReal (-a ^ (r + 1) / (r + 1)) := by
  rw [← ofReal_integral_eq_lintegral_ofReal (integrableOn_Ioi_rpow_of_lt hr ha)
    (ae_restrict_of_forall_mem measurableSet_Ioi fun s hs =>
      Real.rpow_nonneg (ha.trans hs).le _), integral_Ioi_rpow_of_lt hr ha]

private lemma core_lintegral_bound {κ : IIIa.PlanarFrameKernels} {ν m b Cv Cu A : ℝ}
    [Fact (1 < m)] [Fact (0 < cOf ν)] {tr : UnforcedLeray.B0140.TrainSol ν (cOf ν)}
    (FI : FlatInstData κ ν (cOf ν) m tr) (k : ℕ) (hk : k ≤ 1) {μ : ℝ}
    (_hμ0 : 0 ≤ μ) (hμ1 : μ ≤ 1 / 4) (hν : 0 < ν) (hb : 1 ≤ b) (hνb : ν * b ≤ 1 / 3)
    (hCv0 : 0 ≤ Cv) (hCu0 : 0 ≤ Cu) (hA0 : 0 ≤ A) (w : Xmc (cOf ν) m)
    (hVel : ∀ s, 2 / ν ≤ s → s ≤ ν ^ (-2 : ℝ) →
      UnforcedLeray.Train.cellL2 (cOf ν) (tr.v s) ≤ ENNReal.ofReal (Cv * (ν * s)⁻¹))
    (hCore : ∀ s, 2 / ν ≤ s → s ≤ IIIa.coreEnd ν b →
      ‖kcLp (FI.ev.U s (2 / ν) w)‖ ≤ Cu * ν ^ 9 * s ^ 4 * A) :
    ∫⁻ s in Ioc (2 / ν) (IIIa.coreEnd ν b), ENNReal.ofReal (unforcedTailDens FI k μ w s) ≤
      ENNReal.ofReal (18 * Cv * Cu * ((cOf ν)⁻¹ * ν ^ (3 + 2 * μ) * ν ^ k * A)) := by
  obtain ⟨h2sb, _, hsb_le⟩ := coreEnd_bounds hν hb hνb
  have hc : 0 < cOf ν := Fact.out
  set p : ℝ := 3 / 2 - (k : ℝ) / 2 - μ with hp_def
  have hk_le : (k : ℝ) ≤ 1 := by exact_mod_cast hk
  have hp0 : 0 ≤ p := by linarith
  have hpt : ∀ s ∈ Ioc (2 / ν) (IIIa.coreEnd ν b),
      ENNReal.ofReal (unforcedTailDens FI k μ w s) ≤
        ENNReal.ofReal (18 * (cOf ν)⁻¹ * Cv * Cu * ν ^ 8 * (ν ^ (-2 : ℝ)) ^ p * A) := by
    intro s hs
    have hs2 : 2 / ν ≤ s := hs.1.le
    have hspos : 0 < s := (div_pos two_pos hν).trans_le hs2
    have hs_ν2 : s ≤ ν ^ (-2 : ℝ) := hs.2.trans hsb_le
    have h1 := unforcedTailDens_le_of_bounds FI k μ w hspos (by positivity)
      (hVel s hs2 hs_ν2) (hCore s hs2 hs.2)
    refine h1.trans (ENNReal.ofReal_le_ofReal ?_)
    have hsp : s ^ (-(3 / 2 : ℝ) - (k : ℝ) / 2 - μ) * (s⁻¹ * s ^ 4) = s ^ p := by
      have h4 : s⁻¹ * s ^ 4 = s ^ (3 : ℝ) := by
        rw [← Real.rpow_neg_one, ← Real.rpow_natCast s 4, ← Real.rpow_add hspos]
        norm_num
      rw [h4, ← Real.rpow_add hspos]
      congr 1; unfold p; ring
    have hν8 : ν⁻¹ * ν ^ 9 = ν ^ 8 := by
      have hne : ν ≠ 0 := hν.ne'
      field_simp
    have hid : 18 * (cOf ν)⁻¹ * s ^ (-(3 / 2 : ℝ) - (k : ℝ) / 2 - μ) *
        (Cv * (ν * s)⁻¹) * (Cu * ν ^ 9 * s ^ 4 * A) =
        18 * (cOf ν)⁻¹ * Cv * Cu * (ν⁻¹ * ν ^ 9) *
          (s ^ (-(3 / 2 : ℝ) - (k : ℝ) / 2 - μ) * (s⁻¹ * s ^ 4)) * A := by
      rw [mul_inv]; ring
    rw [hid, hν8, hsp]
    have hsp_le : s ^ p ≤ (ν ^ (-2 : ℝ)) ^ p := Real.rpow_le_rpow hspos.le hs_ν2 hp0
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hsp_le (by positivity)) hA0
  have hmeas_le : volume (Ioc (2 / ν) (IIIa.coreEnd ν b)) ≤ ENNReal.ofReal (ν ^ (-2 : ℝ)) := by
    rw [Real.volume_Ioc]
    refine ENNReal.ofReal_le_ofReal ?_
    have : 0 ≤ 2 / ν := by positivity
    linarith
  have hpow_combine : ν ^ 8 * (ν ^ (-2 : ℝ)) ^ p * ν ^ (-2 : ℝ) = ν ^ (3 + 2 * μ) * ν ^ k := by
    rw [← Real.rpow_mul hν.le, ← Real.rpow_natCast ν 8, ← Real.rpow_add hν,
      ← Real.rpow_add hν, ← Real.rpow_natCast ν k, ← Real.rpow_add hν]
    congr 1; unfold p; ring
  calc ∫⁻ s in Ioc (2 / ν) (IIIa.coreEnd ν b), ENNReal.ofReal (unforcedTailDens FI k μ w s)
      ≤ ∫⁻ _s in Ioc (2 / ν) (IIIa.coreEnd ν b),
          ENNReal.ofReal (18 * (cOf ν)⁻¹ * Cv * Cu * ν ^ 8 * (ν ^ (-2 : ℝ)) ^ p * A) :=
        setLIntegral_mono measurable_const hpt
    _ = ENNReal.ofReal (18 * (cOf ν)⁻¹ * Cv * Cu * ν ^ 8 * (ν ^ (-2 : ℝ)) ^ p * A) *
          volume (Ioc (2 / ν) (IIIa.coreEnd ν b)) := by
        rw [setLIntegral_const]
    _ ≤ ENNReal.ofReal (18 * (cOf ν)⁻¹ * Cv * Cu * ν ^ 8 * (ν ^ (-2 : ℝ)) ^ p * A) *
          ENNReal.ofReal (ν ^ (-2 : ℝ)) := by gcongr
    _ = ENNReal.ofReal (18 * Cv * Cu * ((cOf ν)⁻¹ * ν ^ (3 + 2 * μ) * ν ^ k * A)) := by
        rw [← ENNReal.ofReal_mul (by positivity)]
        congr 1
        calc 18 * (cOf ν)⁻¹ * Cv * Cu * ν ^ 8 * (ν ^ (-2 : ℝ)) ^ p * A * ν ^ (-2 : ℝ)
            = 18 * Cv * Cu * ((cOf ν)⁻¹ * (ν ^ 8 * (ν ^ (-2 : ℝ)) ^ p * ν ^ (-2 : ℝ)) * A) := by ring
          _ = 18 * Cv * Cu * ((cOf ν)⁻¹ * (ν ^ (3 + 2 * μ) * ν ^ k) * A) := by rw [hpow_combine]
          _ = 18 * Cv * Cu * ((cOf ν)⁻¹ * ν ^ (3 + 2 * μ) * ν ^ k * A) := by ring

set_option maxHeartbeats 400000 in
private lemma impulse_lintegral_bound {κ : IIIa.PlanarFrameKernels} {ν m b Cv Cu A : ℝ}
    [Fact (1 < m)] [Fact (0 < cOf ν)] {tr : UnforcedLeray.B0140.TrainSol ν (cOf ν)}
    (FI : FlatInstData κ ν (cOf ν) m tr) (k : ℕ) (hk : k ≤ 1) {μ : ℝ}
    (hμ0 : 0 ≤ μ) (hμ1 : μ ≤ 1 / 4) (hν : 0 < ν) (hb : 1 ≤ b) (hνb : ν * b ≤ 1 / 3)
    (hCv0 : 0 ≤ Cv) (hCu0 : 0 ≤ Cu) (hA0 : 0 ≤ A) (w : Xmc (cOf ν) m)
    (hVel : ∀ s, 2 / ν ≤ s →
      UnforcedLeray.Train.cellL2 (cOf ν) (tr.v s) ≤
        ENNReal.ofReal (Cv * ((ν * s)⁻¹ + ν ^ (1 / 4 : ℝ) * s ^ (-(3 / 4 : ℝ)))))
    (hImp : ∀ s, IIIa.coreEnd ν b ≤ s →
      ‖kcLp (FI.ev.U s (2 / ν) w)‖ ≤ Cu * ν * A) :
    ∫⁻ s in Ioi (IIIa.coreEnd ν b), ENNReal.ofReal (unforcedTailDens FI k μ w s) ≤
      ENNReal.ofReal (36 * (2 * b) ^ (3 : ℝ) * Cv * Cu *
        ((cOf ν)⁻¹ * ν ^ (3 + 2 * μ) * ν ^ k * A)) := by
  obtain ⟨h2sb, hsb_lo, _⟩ := coreEnd_bounds hν hb hνb
  have hc : 0 < cOf ν := Fact.out
  have hν1 : ν ≤ 1 := by nlinarith
  set sb := IIIa.coreEnd ν b
  have hsb_pos : 0 < sb := (div_pos two_pos hν).trans_le h2sb
  set r1 : ℝ := -(5 / 2 : ℝ) - (k : ℝ) / 2 - μ
  set r2 : ℝ := -(9 / 4 : ℝ) - (k : ℝ) / 2 - μ
  have hk0 : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
  have hk1 : (k : ℝ) ≤ 1 := by exact_mod_cast hk
  have hr1_lt : r1 < -1 := by unfold r1; linarith
  have hr2_lt : r2 < -1 := by unfold r2; linarith
  set C0 : ℝ := 18 * (cOf ν)⁻¹ * Cv * Cu * A
  have hC0 : 0 ≤ C0 := by positivity
  have hpt : ∀ s ∈ Ioi sb,
      ENNReal.ofReal (unforcedTailDens FI k μ w s) ≤
        ENNReal.ofReal C0 * ENNReal.ofReal (s ^ r1) +
          ENNReal.ofReal (C0 * ν ^ (5 / 4 : ℝ)) * ENNReal.ofReal (s ^ r2) := by
    intro s hs
    have hsb_s : sb ≤ s := le_of_lt hs
    have hs2 : 2 / ν ≤ s := h2sb.trans hsb_s
    have hspos : 0 < s := hsb_pos.trans hs
    have h1 := unforcedTailDens_le_of_bounds FI k μ w hspos (by positivity)
      (hVel s hs2) (hImp s hsb_s)
    have hsplit : 18 * (cOf ν)⁻¹ * s ^ (-(3 / 2 : ℝ) - (k : ℝ) / 2 - μ) *
        (Cv * ((ν * s)⁻¹ + ν ^ (1 / 4 : ℝ) * s ^ (-(3 / 4 : ℝ)))) * (Cu * ν * A) =
        C0 * s ^ r1 + (C0 * ν ^ (5 / 4 : ℝ)) * s ^ r2 := by
      have hs_r1 : s ^ (-(3 / 2 : ℝ) - (k : ℝ) / 2 - μ) * s⁻¹ = s ^ r1 := by
        rw [← Real.rpow_neg_one, ← Real.rpow_add hspos]
        congr 1; unfold r1; ring
      have hs_r2 : s ^ (-(3 / 2 : ℝ) - (k : ℝ) / 2 - μ) * s ^ (-(3 / 4 : ℝ)) = s ^ r2 := by
        rw [← Real.rpow_add hspos]
        congr 1; unfold r2; ring
      have hν_r2 : ν ^ (1 / 4 : ℝ) * ν = ν ^ (5 / 4 : ℝ) := by
        calc ν ^ (1 / 4 : ℝ) * ν = ν ^ (1 / 4 : ℝ) * ν ^ (1 : ℝ) := by rw [Real.rpow_one]
          _ = ν ^ (5 / 4 : ℝ) := by rw [← Real.rpow_add hν]; norm_num
      have hν_inv : ν⁻¹ * ν = 1 := inv_mul_cancel₀ hν.ne'
      calc 18 * (cOf ν)⁻¹ * s ^ (-(3 / 2 : ℝ) - (k : ℝ) / 2 - μ) *
            (Cv * ((ν * s)⁻¹ + ν ^ (1 / 4 : ℝ) * s ^ (-(3 / 4 : ℝ)))) * (Cu * ν * A)
          = C0 * (ν⁻¹ * ν) * (s ^ (-(3 / 2 : ℝ) - (k : ℝ) / 2 - μ) * s⁻¹) +
              (C0 * (ν ^ (1 / 4 : ℝ) * ν)) *
                (s ^ (-(3 / 2 : ℝ) - (k : ℝ) / 2 - μ) * s ^ (-(3 / 4 : ℝ))) := by
            unfold C0; rw [mul_inv]; ring
        _ = C0 * s ^ r1 + (C0 * ν ^ (5 / 4 : ℝ)) * s ^ r2 := by
            rw [hν_inv, mul_one, hs_r1, hν_r2, hs_r2]
    refine h1.trans ?_
    rw [hsplit, ENNReal.ofReal_add (by positivity) (by positivity),
      ENNReal.ofReal_mul (p := C0) hC0,
      ENNReal.ofReal_mul (p := C0 * ν ^ (5 / 4 : ℝ)) (by positivity)]
  have hm1 : Measurable fun s : ℝ => ENNReal.ofReal (s ^ r1) :=
    ENNReal.measurable_ofReal.comp (measurable_id.pow_const r1)
  have hm2 : Measurable fun s : ℝ => ENNReal.ofReal (s ^ r2) :=
    ENNReal.measurable_ofReal.comp (measurable_id.pow_const r2)
  have hI1 := lintegral_Ioi_rpow_eq hr1_lt hsb_pos
  have hI2 := lintegral_Ioi_rpow_eq hr2_lt hsb_pos
  have hlo_pos : 0 < (2 * b)⁻¹ * ν ^ (-2 : ℝ) := by positivity
  have h2b_ge1 : 1 ≤ 2 * b := by linarith
  have hb1 : -sb ^ (r1 + 1) / (r1 + 1) ≤ (2 * b) ^ (3 : ℝ) * ν ^ (3 + 2 * μ) * ν ^ k := by
    have hden : 1 ≤ -(r1 + 1) := by unfold r1; linarith
    have hdiv : -sb ^ (r1 + 1) / (r1 + 1) ≤ sb ^ (r1 + 1) := by
      rw [neg_div, ← div_neg]
      exact div_le_self (Real.rpow_nonneg hsb_pos.le _) hden
    have hsb_r1 : sb ^ (r1 + 1) ≤ ((2 * b)⁻¹ * ν ^ (-2 : ℝ)) ^ (r1 + 1) :=
      Real.rpow_le_rpow_of_nonpos hlo_pos hsb_lo (by linarith)
    have hmul : ((2 * b)⁻¹ * ν ^ (-2 : ℝ)) ^ (r1 + 1) =
        (2 * b) ^ (-(r1 + 1)) * (ν ^ (3 + 2 * μ) * ν ^ k) := by
      rw [Real.mul_rpow (by positivity) (by positivity),
        Real.inv_rpow (by positivity), ← Real.rpow_neg (by positivity),
        ← Real.rpow_mul hν.le, ← Real.rpow_natCast ν k, ← Real.rpow_add hν]
      congr 2; unfold r1; ring
    have h2b_le : (2 * b) ^ (-(r1 + 1)) ≤ (2 * b) ^ (3 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le h2b_ge1 (by unfold r1; linarith)
    calc -sb ^ (r1 + 1) / (r1 + 1) ≤ sb ^ (r1 + 1) := hdiv
      _ ≤ ((2 * b)⁻¹ * ν ^ (-2 : ℝ)) ^ (r1 + 1) := hsb_r1
      _ = (2 * b) ^ (-(r1 + 1)) * (ν ^ (3 + 2 * μ) * ν ^ k) := hmul
      _ ≤ (2 * b) ^ (3 : ℝ) * (ν ^ (3 + 2 * μ) * ν ^ k) :=
          mul_le_mul_of_nonneg_right h2b_le (by positivity)
      _ = (2 * b) ^ (3 : ℝ) * ν ^ (3 + 2 * μ) * ν ^ k := by ring
  have hb2 : ν ^ (5 / 4 : ℝ) * (-sb ^ (r2 + 1) / (r2 + 1)) ≤
      (2 * b) ^ (3 : ℝ) * ν ^ (3 + 2 * μ) * ν ^ k := by
    have hden : 1 ≤ -(r2 + 1) := by unfold r2; linarith
    have hdiv : -sb ^ (r2 + 1) / (r2 + 1) ≤ sb ^ (r2 + 1) := by
      rw [neg_div, ← div_neg]
      exact div_le_self (Real.rpow_nonneg hsb_pos.le _) hden
    have hsb_r2 : sb ^ (r2 + 1) ≤ ((2 * b)⁻¹ * ν ^ (-2 : ℝ)) ^ (r2 + 1) :=
      Real.rpow_le_rpow_of_nonpos hlo_pos hsb_lo (by linarith)
    have hmul : ν ^ (5 / 4 : ℝ) * ((2 * b)⁻¹ * ν ^ (-2 : ℝ)) ^ (r2 + 1) =
        (2 * b) ^ (-(r2 + 1)) * (ν ^ (15 / 4 + 2 * μ) * ν ^ k) := by
      rw [Real.mul_rpow (by positivity) (by positivity),
        Real.inv_rpow (by positivity), ← Real.rpow_neg (by positivity),
        ← Real.rpow_mul hν.le, ← mul_assoc,
        mul_comm (ν ^ (5 / 4 : ℝ)) ((2 * b) ^ (-(r2 + 1))), mul_assoc,
        ← Real.rpow_add hν, ← Real.rpow_natCast ν k, ← Real.rpow_add hν]
      congr 2; unfold r2; ring
    have h2b_le : (2 * b) ^ (-(r2 + 1)) ≤ (2 * b) ^ (3 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le h2b_ge1 (by unfold r2; linarith)
    have hν_le : ν ^ (15 / 4 + 2 * μ) ≤ ν ^ (3 + 2 * μ) :=
      Real.rpow_le_rpow_of_exponent_ge hν hν1 (by linarith)
    calc ν ^ (5 / 4 : ℝ) * (-sb ^ (r2 + 1) / (r2 + 1))
        ≤ ν ^ (5 / 4 : ℝ) * ((2 * b)⁻¹ * ν ^ (-2 : ℝ)) ^ (r2 + 1) :=
          mul_le_mul_of_nonneg_left (hdiv.trans hsb_r2) (by positivity)
      _ = (2 * b) ^ (-(r2 + 1)) * (ν ^ (15 / 4 + 2 * μ) * ν ^ k) := hmul
      _ ≤ (2 * b) ^ (3 : ℝ) * (ν ^ (3 + 2 * μ) * ν ^ k) :=
          mul_le_mul h2b_le (mul_le_mul_of_nonneg_right hν_le (by positivity))
            (by positivity) (by positivity)
      _ = (2 * b) ^ (3 : ℝ) * ν ^ (3 + 2 * μ) * ν ^ k := by ring
  calc ∫⁻ s in Ioi sb, ENNReal.ofReal (unforcedTailDens FI k μ w s)
      ≤ ∫⁻ s in Ioi sb,
          (ENNReal.ofReal C0 * ENNReal.ofReal (s ^ r1) +
            ENNReal.ofReal (C0 * ν ^ (5 / 4 : ℝ)) * ENNReal.ofReal (s ^ r2)) :=
        setLIntegral_mono ((hm1.const_mul _).add (hm2.const_mul _)) hpt
    _ = ENNReal.ofReal C0 * (∫⁻ s in Ioi sb, ENNReal.ofReal (s ^ r1)) +
          ENNReal.ofReal (C0 * ν ^ (5 / 4 : ℝ)) * (∫⁻ s in Ioi sb, ENNReal.ofReal (s ^ r2)) := by
        rw [lintegral_add_left (hm1.const_mul _),
          lintegral_const_mul _ hm1, lintegral_const_mul _ hm2]
    _ = ENNReal.ofReal (C0 * (-sb ^ (r1 + 1) / (r1 + 1))) +
          ENNReal.ofReal (C0 * (ν ^ (5 / 4 : ℝ) * (-sb ^ (r2 + 1) / (r2 + 1)))) := by
        rw [hI1, hI2, ← ENNReal.ofReal_mul (p := C0) hC0,
          ← ENNReal.ofReal_mul (p := C0 * ν ^ (5 / 4 : ℝ)) (by positivity)]
        congr 2
        ring
    _ ≤ ENNReal.ofReal (C0 * ((2 * b) ^ (3 : ℝ) * ν ^ (3 + 2 * μ) * ν ^ k)) +
          ENNReal.ofReal (C0 * ((2 * b) ^ (3 : ℝ) * ν ^ (3 + 2 * μ) * ν ^ k)) := by
        gcongr
    _ = ENNReal.ofReal (36 * (2 * b) ^ (3 : ℝ) * Cv * Cu *
          ((cOf ν)⁻¹ * ν ^ (3 + 2 * μ) * ν ^ k * A)) := by
        rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
        congr 1; unfold C0; ring

set_option maxHeartbeats 400000 in
/-- **Assembly of `UnforcedTailImpulseBound` from the three tail leaves** (source 4440-4458,
3272-3289). -/
theorem unforcedTailImpulseBound_of (D : SeqData) (hVel : TrainVelTailBound D)
    (hCore : UnforcedFlowKcCoreBound D) (hImp : UnforcedFlowKcImpulseBound D) :
    UnforcedTailImpulseBound D := by
  intro dm dp hst κ hκ m _ hm
  obtain ⟨Cv, Nv, hCv0, hCv⟩ := hVel dm dp hst
  obtain ⟨b1, hb1, hC1⟩ := hCore dm dp hst κ hκ m hm
  obtain ⟨b2, hb2, hC2⟩ := hImp dm dp hst κ hκ m hm
  set b : ℝ := max b1 b2
  have hb : 1 ≤ b := hb1.trans (le_max_left _ _)
  have hb0 : 0 < b := one_pos.trans_le hb
  obtain ⟨Cu1, N1, hCu1, hCore_b⟩ := hC1 b (le_max_left _ _)
  obtain ⟨Cu2, N2, hCu2, hImp_b⟩ := hC2 b (le_max_right _ _)
  set Cu : ℝ := max Cu1 Cu2
  have hCu0 : 0 ≤ Cu := hCu1.trans (le_max_left _ _)
  have hmu_ev := mu_eventually_mem D hst.omega_ne hst.sigma_pos hst.sigma_lt
  have hnu_ev : ∀ᶠ n : ℕ in atTop, nu D n < 1 / (3 * b) :=
    (retNu_tendsto D.σ₀ hst.omega_ne).eventually (gt_mem_nhds (by positivity))
  obtain ⟨N3, hN3⟩ := eventually_atTop.1 (hmu_ev.and hnu_ev)
  set C : ℝ := 18 * Cv * Cu + 36 * (2 * b) ^ (3 : ℝ) * Cv * Cu
  refine ⟨C, max (max Nv N1) (max N2 N3), by positivity, fun n hn FI k hk z hz w => ?_⟩
  have hnv : Nv ≤ n := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hn
  have hn1 : N1 ≤ n := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hn
  have hn2 : N2 ≤ n := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hn
  have hn3 : N3 ≤ n := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hn
  obtain ⟨hmuz, hν_lt⟩ := hN3 n hn3
  let ν := nu D n
  have hν : 0 < ν := retNu_pos D.Pl D.σ₀ n
  have hc : 0 < cOf ν := cOf_pos hν
  have : Fact (0 < cOf ν) := ⟨hc⟩
  have hνb : ν * b ≤ 1 / 3 := by
    have h1 : ν * b ≤ 1 / (3 * b) * b := mul_le_mul_of_nonneg_right hν_lt.le hb0.le
    have h2 : 1 / (3 * b) * b = 1 / 3 := by
      have : b ≠ 0 := hb0.ne'
      field_simp
    linarith
  have hμ0 : 0 ≤ D.mu n z := by
    have := (hmuz z hz).1
    linarith [hst.sigma_pos]
  have hμ1 : D.mu n z ≤ 1 / 4 := by
    have := (hmuz z hz).2
    linarith [hst.sigma_lt]
  set A : ℝ := ‖Nnu D.Pl.eigenvalue D.Pl.kappa ν‖ *
    (‖Fpm true D.Pl.eigenvalue D.Pl.kappa ν (2 / ν) 0‖⁻¹ * ‖w‖)
  have hA0 : 0 ≤ A := by positivity
  obtain ⟨h2sb, _, _⟩ := coreEnd_bounds hν hb hνb
  have hsplit : Ioi (2 / ν) = Ioc (2 / ν) (IIIa.coreEnd ν b) ∪ Ioi (IIIa.coreEnd ν b) :=
    (Set.Ioc_union_Ioi_eq_Ioi h2sb).symm
  let f : ℝ → ℝ≥0∞ := fun s => ENNReal.ofReal (unforcedTailDens FI k (D.mu n z) w s)
  have hunion : ∫⁻ s in Ioi (2 / ν), f s =
      (∫⁻ s in Ioc (2 / ν) (IIIa.coreEnd ν b), f s) +
        ∫⁻ s in Ioi (IIIa.coreEnd ν b), f s := by
    rw [hsplit, lintegral_union measurableSet_Ioi (Set.Ioc_disjoint_Ioi le_rfl)]
  have hB1 := core_lintegral_bound FI k hk hμ0 hμ1 hν hb hνb hCv0 hCu0 hA0 w
    (fun s hs1 hs2 => (hCv n hnv s hs1).1 hs2)
    (fun s hs1 hs2 => (hCore_b n hn1 FI w s hs1 hs2).trans
      (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity))
          (by positivity)) hA0))
  have hB2 := impulse_lintegral_bound FI k hk hμ0 hμ1 hν hb hνb hCv0 hCu0 hA0 w
    (fun s hs1 => (hCv n hnv s hs1).2)
    (fun s hs1 => (hImp_b n hn2 FI w s hs1).trans
      (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (le_max_right _ _) hν.le) hA0))
  calc ∫⁻ s in Ioi (2 / ν), f s
      = (∫⁻ s in Ioc (2 / ν) (IIIa.coreEnd ν b), f s) +
          ∫⁻ s in Ioi (IIIa.coreEnd ν b), f s := hunion
    _ ≤ ENNReal.ofReal (18 * Cv * Cu * ((cOf ν)⁻¹ * ν ^ (3 + 2 * D.mu n z) * ν ^ k * A)) +
          ENNReal.ofReal (36 * (2 * b) ^ (3 : ℝ) * Cv * Cu *
            ((cOf ν)⁻¹ * ν ^ (3 + 2 * D.mu n z) * ν ^ k * A)) := add_le_add hB1 hB2
    _ = ENNReal.ofReal (C * ((‖Nnu D.Pl.eigenvalue D.Pl.kappa ν‖ *
          ν ^ (3 + 2 * D.mu n z) / cOf ν) * ν ^ k *
            (‖Fpm true D.Pl.eigenvalue D.Pl.kappa ν (2 / ν) 0‖⁻¹ * ‖w‖))) := by
        rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
        congr 1; unfold C A; ring

/-- **Reduction of `G1.LaterOutput.TailBound` to the three tail leaves** (source 4440-4458). -/
theorem tailBound_of_parts (D : SeqData) (hVel : TrainVelTailBound D)
    (hCore : UnforcedFlowKcCoreBound D) (hImp : UnforcedFlowKcImpulseBound D) :
    G1.LaterOutput.TailBound D :=
  tailBound_of D (unforcedTailImpulseBound_of D hVel hCore hImp)

end UnforcedLeray.Short.PartIIIb.Concrete.FlatUnif.G1.LaterOutput
