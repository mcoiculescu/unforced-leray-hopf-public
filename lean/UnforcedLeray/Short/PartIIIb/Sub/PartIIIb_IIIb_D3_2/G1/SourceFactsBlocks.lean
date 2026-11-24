import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_IIIb_D3_2.G1.SourceFacts
import UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst.Assembly
import UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst.Pair.Of
import UnforcedLeray.Short.PartIIIb.Proofs.Young.Blocks.Fpm

/-!

(source 4382-4384, 4390-4406)

Source of record: `the November 2 reference manuscript` (73 pages), lines
4382-4384 and 4390-4406 (`prop:short-full-clock`, variation-of-constants integral inequalities for
the normalised amplitude `A_j = ampN` and complement `R = cmpN` on the finite band `0 ≤ t ≤ s ≤ 2/ν`
with residual `δ_c = deltaC (K ν⁻¹^p) CS bS ν (ν⁻²)`).

What is proved unconditionally in this file:
1. **Strong continuity of the normalised block coordinates** (`continuousOn_ampN_actualPk`,
   `continuousOn_cmpN_actualPk`): for any pinned `FI : FlatInstData κ ν c m tr`, `0 < ν` and
   `0 ≤ t`, the functions `s ↦ ampN (actualPk FI) lam κ ν t x j s` and
   `s ↦ cmpN (actualPk FI) lam κ ν t x s` are continuous on `Icc t H` (from `FI.ev.jointCont`,
   `FI.pair.ell_cont`, `FI.pair.q_cont` and continuity/non-vanishing of `Fpm`).
2. **Exact identification on the finite band `[0, 2/ν]`** (`bandAge_eq_of_mem_Icc`,
   `ell_actualPk_eq_ampl`, `norm_Fpm_eq_clockN`): on `0 ≤ s ≤ 2/ν`, `(actualPk FI).ell j s
   ((actualPk FI).Uev s t x)` coincides with the moving-frame amplitude
   `IIIa.ampl (IIIa.periodizedFrame κ ν m b K hν hPF) (fun r => xFn (FI.ev.U r t x)) s (pmIdx j)`,
   and `‖Fpm j D.Pl.eigenvalue D.Pl.kappa ν s t‖ = IIIa.clockN D.Pl ν t s`.
3. **Index shift and `IsTrainPkg` instantiation** (`retainedBlocks_of_shift`,
   `retainedBlocksActual_of_trainBlockInput`): shifting by `N0` makes `S (n + N0) = levelFlat ...`
   hold for all `n`, discharging `IsTrainPkg` via `FlatSettingInst.isTrainPkg_actualPk`.
4. **Reduction to the analytic integral inequalities** (`retainedBlocksActual_of`): derives
   `G1.RetainedBlocksActual D` from `ActualBlockIntegralBounds D` (the variation-of-constants
   integral inequalities for `cmpN` and `ampN` along `actualPk FI`, with continuity discharged here).
-/

set_option autoImplicit false

noncomputable section

open Filter Topology Set MeasureTheory
open scoped ENNReal

namespace UnforcedLeray.Short.PartIIIb.Concrete.FlatUnif

open ConcreteYF FlatSettingInst

/-! ## 1. Continuity of `Fpm`, `ampN` and `cmpN` for `actualPk FI` -/

/-- `aOf ν s` is continuous in `s`. -/
theorem continuous_aOf (ν : ℝ) : Continuous (aOf ν) := by
  unfold aOf
  fun_prop

/-- `zOf ν s = s / aOf ν s` is continuous on `[t, H]` for `0 < ν` and `0 ≤ t`. -/
theorem continuousOn_zOf {ν t H : ℝ} (hν : 0 < ν) (ht : 0 ≤ t) :
    ContinuousOn (zOf ν) (Icc t H) := by
  unfold zOf
  refine continuousOn_id.div (continuous_aOf ν).continuousOn fun s hs => ?_
  exact (aOf_pos_of_nonneg ν s hν (ht.trans hs.1)).ne'

/-- For `0 < ν` and `0 ≤ t`, `s ↦ Fpm j lam κ ν s t` is continuous on `[t, H]`. -/
theorem continuousOn_Fpm (j : Bool) (lam κ : ℂ) {ν t H : ℝ} (hν : 0 < ν) (ht : 0 ≤ t) :
    ContinuousOn (fun s => Fpm j lam κ ν s t) (Icc t H) := by
  set l : ℂ := if j then lam else (starRingEnd ℂ) lam
  set k : ℂ := if j then κ else (starRingEnd ℂ) κ
  have hat : 0 < aOf ν t := aOf_pos_of_nonneg ν t hν ht
  have hdiv_pos : ∀ s ∈ Icc t H, 0 < aOf ν s / aOf ν t := fun s hs =>
    div_pos (aOf_pos_of_nonneg ν s hν (ht.trans hs.1)) hat
  have heq : EqOn (fun s => Fpm j lam κ ν s t)
      (fun s => Complex.exp (l * ((zOf ν s - zOf ν t : ℝ) : ℂ)) *
        Complex.exp (((Real.log (aOf ν s / aOf ν t) : ℝ) : ℂ) * k)) (Icc t H) := by
    intro s hs
    have hr : 0 < aOf ν s / aOf ν t := hdiv_pos s hs
    have hc : ((aOf ν s / aOf ν t : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hr.ne'
    have hcpow : ((aOf ν s / aOf ν t : ℝ) : ℂ) ^ k =
        Complex.exp (((Real.log (aOf ν s / aOf ν t) : ℝ) : ℂ) * k) := by
      rw [Complex.cpow_def_of_ne_zero hc, Complex.ofReal_log hr.le]
    dsimp only
    rw [← hcpow]
    cases j
    · simp only [l, k, Bool.false_eq_true, ↓reduceIte, fpm_false_eq]
    · simp only [l, k, ↓reduceIte, fpm_true_eq]
  refine ContinuousOn.congr ?_ heq
  have hz : ContinuousOn (fun s : ℝ => l * ((zOf ν s - zOf ν t : ℝ) : ℂ)) (Icc t H) :=
    continuousOn_const.mul
      (Complex.continuous_ofReal.comp_continuousOn ((continuousOn_zOf hν ht).sub continuousOn_const))
  have hlog : ContinuousOn (fun s : ℝ => Real.log (aOf ν s / aOf ν t)) (Icc t H) :=
    ((continuous_aOf ν).continuousOn.div_const (aOf ν t)).log fun s hs => (hdiv_pos s hs).ne'
  have hk : ContinuousOn (fun s : ℝ => ((Real.log (aOf ν s / aOf ν t) : ℝ) : ℂ) * k) (Icc t H) :=
    (Complex.continuous_ofReal.comp_continuousOn hlog).mul continuousOn_const
  exact (Complex.continuous_exp.comp_continuousOn hz).mul
    (Complex.continuous_exp.comp_continuousOn hk)

/-- For `ev : TrainEvolution m tr` and `0 ≤ t`, `s ↦ ev.U s t x` is continuous on `[t, H]`. -/
theorem continuousOn_Uev_right {ν c m : ℝ} [Fact (1 < m)] {tr : UnforcedLeray.B0140.TrainSol ν c}
    (ev : TrainEvolution m tr) {t H : ℝ} (ht : 0 ≤ t) (x : Xmc c m) :
    ContinuousOn (fun s => ev.U s t x) (Icc t H) :=
  (ev.jointCont x).comp (continuous_id.prodMk continuous_const).continuousOn
    fun _ hs => ⟨ht, hs.1⟩

/-- Continuity of `s ↦ (actualPk FI).ell j s ((actualPk FI).Uev s t x)` on `[t, H]`. -/
theorem continuousOn_ell_Uev_actualPk {κ : IIIa.PlanarFrameKernels} {ν c m : ℝ} [Fact (1 < m)]
    {tr : UnforcedLeray.B0140.TrainSol ν c} (FI : FlatInstData κ ν c m tr)
    {t H : ℝ} (ht : 0 ≤ t) (x : Xmc c m) (j : Bool) :
    ContinuousOn (fun s => (actualPk FI).ell j s ((actualPk FI).Uev s t x)) (Icc t H) :=
  (FI.pair.ell_cont j).continuousOn.clm_apply (continuousOn_Uev_right FI.ev ht x)

/-- Continuity of `s ↦ Pc (actualPk FI) s ((actualPk FI).Uev s t x)` on `[t, H]`. -/
theorem continuousOn_Pc_Uev_actualPk {κ : IIIa.PlanarFrameKernels} {ν c m : ℝ} [Fact (1 < m)]
    {tr : UnforcedLeray.B0140.TrainSol ν c} (FI : FlatInstData κ ν c m tr)
    {t H : ℝ} (ht : 0 ≤ t) (x : Xmc c m) :
    ContinuousOn (fun s => Pc (actualPk FI) s ((actualPk FI).Uev s t x)) (Icc t H) := by
  have heq : (fun s => Pc (actualPk FI) s ((actualPk FI).Uev s t x)) =
      fun s => (actualPk FI).Uev s t x -
        ((actualPk FI).ell true s ((actualPk FI).Uev s t x) • (actualPk FI).q true s +
          (actualPk FI).ell false s ((actualPk FI).Uev s t x) • (actualPk FI).q false s) := by
    funext s
    simp [Pc]
  rw [heq]
  exact (continuousOn_Uev_right FI.ev ht x).sub
    (((continuousOn_ell_Uev_actualPk FI ht x true).smul (FI.pair.q_cont true).continuousOn).add
      ((continuousOn_ell_Uev_actualPk FI ht x false).smul (FI.pair.q_cont false).continuousOn))

/-- **Strong continuity of `ampN` for `actualPk FI`** on `[t, H]` (first conjunct of
`RetainedBlocks`). -/
theorem continuousOn_ampN_actualPk {κ : IIIa.PlanarFrameKernels} {ν c m : ℝ} [Fact (1 < m)]
    {tr : UnforcedLeray.B0140.TrainSol ν c} (FI : FlatInstData κ ν c m tr)
    (lam κp : ℂ) {t H : ℝ} (hν : 0 < ν) (ht : 0 ≤ t) (x : Xmc c m) (j : Bool) :
    ContinuousOn (ampN (actualPk FI) lam κp ν t x j) (Icc t H) := by
  unfold ampN
  refine (continuousOn_ell_Uev_actualPk FI ht x j).div (continuousOn_Fpm j lam κp hν ht) ?_
  intro s hs
  exact (fpm_facts ν hν lam κp s t (ht.trans hs.1) ht).2.1 j

/-- **Strong continuity of `cmpN` for `actualPk FI`** on `[t, H]` (second conjunct of
`RetainedBlocks`). -/
theorem continuousOn_cmpN_actualPk {κ : IIIa.PlanarFrameKernels} {ν c m : ℝ} [Fact (1 < m)]
    {tr : UnforcedLeray.B0140.TrainSol ν c} (FI : FlatInstData κ ν c m tr)
    (lam κp : ℂ) {t H : ℝ} (hν : 0 < ν) (ht : 0 ≤ t) (x : Xmc c m) :
    ContinuousOn (cmpN (actualPk FI) lam κp ν t x) (Icc t H) := by
  unfold cmpN
  refine (continuousOn_Pc_Uev_actualPk FI ht x).norm.div
    (continuousOn_Fpm true lam κp hν ht).norm ?_
  intro s hs
  exact norm_ne_zero_iff.mpr ((fpm_facts ν hν lam κp s t (ht.trans hs.1) ht).2.1 true)

/-! ## 2. Exact identification on the finite band `[0, 2/ν]` with the Part III-a moving frame -/

/-- On the finite band `0 ≤ s ≤ 2/ν`, the clamped age `bandAge ν s` is `s`. -/
theorem bandAge_eq_of_mem_Icc {ν s : ℝ} (hs : s ∈ Icc (0 : ℝ) (2 / ν)) :
    bandAge ν s = s := by
  unfold bandAge flatSigma
  rw [min_eq_left hs.2, max_eq_right hs.1]

/-- On `0 ≤ s ≤ 2/ν`, `bandA ν s = IIIa.clockA ν s`. -/
theorem bandA_eq_clockA_of_mem_Icc {ν s : ℝ} (hs : s ∈ Icc (0 : ℝ) (2 / ν)) :
    bandA ν s = IIIa.clockA ν s := by
  unfold bandA
  rw [bandAge_eq_of_mem_Icc hs]

/-- On `0 ≤ s ≤ 2/ν`, `bandD ν c s = IIIa.cellLen c (IIIa.clockA ν s)`. -/
theorem bandD_eq_cellLen_of_mem_Icc {ν c s : ℝ} (hs : s ∈ Icc (0 : ℝ) (2 / ν)) :
    bandD ν c s = IIIa.cellLen c (IIIa.clockA ν s) := by
  unfold bandD
  rw [bandA_eq_clockA_of_mem_Icc hs]

/-- On `0 ≤ s ≤ 2/ν`, `(actualPk FI).ell j s ((actualPk FI).Uev s t x)` equals the Part III-a
moving-frame amplitude `IIIa.ampl (IIIa.periodizedFrame ...) (fun r => xFn (FI.ev.U r t x)) s
(pmIdx j)`. -/
theorem ell_actualPk_eq_ampl {κ : IIIa.PlanarFrameKernels} {ν m b K : ℝ} [Fact (1 < m)]
    (hν : 0 < ν) (hPF : IIIa.PerFrameFacts κ ν m b K)
    {tr : UnforcedLeray.B0140.TrainSol ν (cOf ν)}
    (FI : FlatInstData κ ν (cOf ν) m tr) (t : ℝ) (x : Xmc (cOf ν) m) (j : Bool)
    {s : ℝ} (hs : s ∈ Icc (0 : ℝ) (2 / ν)) :
    (actualPk FI).ell j s ((actualPk FI).Uev s t x) =
      IIIa.ampl (IIIa.periodizedFrame κ ν m b K hν hPF)
        (fun r => xFn (FI.ev.U r t x)) s (pmIdx j) := by
  change FI.pair.ell j s (FI.ev.U s t x) = _
  rw [FI.pair.ell_pin]
  set w : ℝ → ℝ × ℝ → ℂ := fun r => xFn (FI.ev.U r t x)
  change frozenEll κ ν (cOf ν) j s (w s) =
    IIIa.ampl (IIIa.periodizedFrame κ ν m b K hν hPF) w s (pmIdx j)
  unfold frozenEll IIIa.ampl IIIa.periodizedFrame IIIa.movingCell IIIa.movingW
  rw [bandD_eq_cellLen_of_mem_Icc hs, bandA_eq_clockA_of_mem_Icc hs, cOf_eq_rpow hν]

/-- For `0 < ν`, `0 ≤ t` and `0 ≤ s`, the modulus of `Fpm j P.eigenvalue P.kappa ν s t` equals the
Part III-a normaliser `IIIa.clockN P ν t s`. -/
theorem norm_Fpm_eq_clockN (P : UnforcedLeray.Blueprint.Planar.PlanarData) (j : Bool)
    {ν s t : ℝ} (hν : 0 < ν) (hs : 0 ≤ s) (ht : 0 ≤ t) :
    ‖Fpm j P.eigenvalue P.kappa ν s t‖ = IIIa.clockN P ν t s := by
  have hmod : ‖Fpm j P.eigenvalue P.kappa ν s t‖ = ‖Fpm true P.eigenvalue P.kappa ν s t‖ := by
    cases j
    · exact (fpm_facts ν hν P.eigenvalue P.kappa s t hs ht).2.2
    · rfl
  rw [hmod, fpm_true_eq]
  have has : 0 < aOf ν s := aOf_pos_of_nonneg ν s hν hs
  have hat : 0 < aOf ν t := aOf_pos_of_nonneg ν t hν ht
  rw [fpm_norm_formula P.eigenvalue P.kappa ν s t (div_pos has hat)]
  unfold IIIa.clockN IIIa.clockTheta zOf aOf IIIa.clockA
  have hνne : ν ≠ 0 := hν.ne'
  have hasne : 1 + ν * s ≠ 0 := has.ne'
  have hatne : 1 + ν * t ≠ 0 := hat.ne'
  have hdiff : (ν * (1 + ν * t))⁻¹ - (ν * (1 + ν * s))⁻¹ =
      s / (1 + ν * s) - t / (1 + ν * t) := by
    field_simp
    ring
  have hrat : (ν * (1 + ν * t))⁻¹ / (ν * (1 + ν * s))⁻¹ = (1 + ν * s) / (1 + ν * t) := by
    field_simp
  rw [hdiff, hrat]

/-! ## 3. Index shift and reduction of `RetainedBlocksActual` -/

/-- Unshifting the sequence index in `RetainedBlocks` (converse of `G1.retainedBlocks_shift_frozen`). -/
theorem retainedBlocks_of_shift (pk : ℕ → YoungPkg) (ν : ℕ → ℝ) (lam κ : ℂ) (Sg α : ℝ)
    (δ : ℕ → ℝ) (M : ℕ)
    (h : RetainedBlocks (fun n => pk (n + M)) (fun n => ν (n + M)) lam κ Sg α
      (fun n => δ (n + M))) :
    RetainedBlocks pk ν lam κ Sg α δ := by
  obtain ⟨C, g, N, hC, hg, hR⟩ := h
  refine ⟨C, g, N + M, hC, hg, fun n hn => ?_⟩
  obtain ⟨k, rfl⟩ : ∃ k, n = k + M := ⟨n - M, by omega⟩
  exact hR k (by omega)

/-- The `TrainSol` cast along `cOf (nu D n) = nu D n ^ (-2 : ℝ)`. -/
def trainRpow (D : SeqData) (n : ℕ) :
    UnforcedLeray.B0140.TrainSol (nu D n) (nu D n ^ (-2 : ℝ)) :=
  cOf_eq_rpow (retNu_pos D.Pl D.σ₀ n) ▸ D.train n

private theorem isTrainPkg_cast_c (pk : YoungPkg) {ν c c' m : ℝ} (hc : c = c')
    (tr : UnforcedLeray.B0140.TrainSol ν c) (emb : pk.X → ℝ × ℝ → ℂ)
    (h : IsTrainPkg pk ν c m tr emb) :
    ∃ (tr' : UnforcedLeray.B0140.TrainSol ν c'), IsTrainPkg pk ν c' m tr' emb := by
  subst hc
  exact ⟨tr, h⟩

/-- If `S n = levelFlat hν FI χo ε`, then `IsTrainPkg (S n).pk ν (ν^(-2:ℝ)) m` holds for the cast
train and `xFn`. -/
theorem isTrainPkg_of_levelFlat {κ : IIIa.PlanarFrameKernels} {ν m : ℝ} [Fact (1 < m)]
    (hν : 0 < ν) {tr : UnforcedLeray.B0140.TrainSol ν (cOf ν)}
    (FI : FlatInstData κ ν (cOf ν) m tr) (χo : ℝ → ℝ) (ε : ℝ) :
    ∃ (tr' : UnforcedLeray.B0140.TrainSol ν (ν ^ (-2 : ℝ)))
      (emb : (levelFlat hν FI χo ε).pk.X → ℝ × ℝ → ℂ),
      IsTrainPkg (levelFlat hν FI χo ε).pk ν (ν ^ (-2 : ℝ)) m tr' emb := by
  obtain ⟨tr', htr'⟩ := isTrainPkg_cast_c (actualPk FI) (cOf_eq_rpow hν) tr xFn
    (isTrainPkg_actualPk FI)
  exact ⟨tr', xFn, htr'⟩

/-- **Route via `ConcreteYF.TrainBlockInput` on the shifted sequence**: if for every shifted actual
package sequence `pk' n = (S (n + N0)).pk` the source implication `TrainBlockInput` holds for some
`CS, bS, K, p`, then `G1.RetainedBlocksActual D` follows by discharging `IsTrainPkg` with
`isTrainPkg_of_levelFlat` and unshifting via `retainedBlocks_of_shift`. -/
theorem retainedBlocksActual_of_trainBlockInput (D : SeqData)
    (hTBI : ∀ (dm dp : ℝ), D.RepairStanding dm dp → ∀ κ : IIIa.PlanarFrameKernels, SeedLink D κ →
      ∀ (m : ℝ) [Fact (1 < m)], 8 < m → ∀ (N0 : ℕ) (pk' : ℕ → YoungPkg)
        (tr' : ∀ n, UnforcedLeray.B0140.TrainSol (nu D (n + N0)) (nu D (n + N0) ^ (-2 : ℝ)))
        (emb' : ∀ n, (pk' n).X → ℝ × ℝ → ℂ),
        (∀ n, ∃ FI : FlatInstData κ (nu D (n + N0)) (cOf (nu D (n + N0))) m (D.train (n + N0)),
          pk' n = actualPk FI) →
        ∃ (CS bS K : ℝ) (p : ℕ), 0 < bS ∧ 0 ≤ CS ∧ 0 ≤ K ∧
          TrainBlockInput pk' (fun n => nu D (n + N0)) D.Pl.eigenvalue D.Pl.kappa 2 1.1
            (fun n => deltaC (K * (nu D (n + N0))⁻¹ ^ p) CS bS (nu D (n + N0))
              (nu D (n + N0) ^ (-2 : ℝ))) m tr' emb') :
    G1.RetainedBlocksActual D := by
  intro dm dp hD κ hκ m hfact hm S hS
  obtain ⟨N0, hN0⟩ := Filter.eventually_atTop.mp hS
  have hex : ∀ n, ∃ (tr' : UnforcedLeray.B0140.TrainSol (nu D (n + N0)) (nu D (n + N0) ^ (-2 : ℝ)))
      (emb' : (S (n + N0)).pk.X → ℝ × ℝ → ℂ),
      IsTrainPkg (S (n + N0)).pk (nu D (n + N0)) (nu D (n + N0) ^ (-2 : ℝ)) m tr' emb' ∧
      ∃ FI : FlatInstData κ (nu D (n + N0)) (cOf (nu D (n + N0))) m (D.train (n + N0)),
        (S (n + N0)).pk = actualPk FI := by
    intro n
    obtain ⟨FI, hFI⟩ := hN0 (n + N0) (by omega)
    have hν : 0 < nu D (n + N0) := retNu_pos D.Pl D.σ₀ (n + N0)
    have hpk : (S (n + N0)).pk = (levelFlat hν FI D.K.χo (retEps D.Pl D.σ₀ (n + N0))).pk :=
      congrArg ConcreteYF.FlatSetting.pk hFI
    rw [hpk]
    obtain ⟨tr', emb', htr'⟩ := isTrainPkg_of_levelFlat hν FI D.K.χo (retEps D.Pl D.σ₀ (n + N0))
    exact ⟨tr', emb', htr', FI, rfl⟩
  choose tr' emb' hTrain hFI_pk using hex
  obtain ⟨CS, bS, K, p, hbS, hCS, hK, hInput⟩ :=
    hTBI dm dp hD κ hκ m hm N0 (fun n => (S (n + N0)).pk) tr' emb' hFI_pk
  refine ⟨CS, bS, K, p, hbS, hCS, hK, ?_⟩
  exact retainedBlocks_of_shift (fun n => (S n).pk) (nu D) D.Pl.eigenvalue D.Pl.kappa 2 1.1
    (fun n => deltaC (K * (nu D n)⁻¹ ^ p) CS bS (nu D n) (nu D n ^ (-2 : ℝ))) N0 (hInput hTrain)

/-- **The analytic variation-of-constants integral inequalities on `actualPk FI`** (source 4382-4384,
4390-4406): the two integral inequalities of `RetainedBlocks` for the pinned package `actualPk FI`
(continuity of `ampN` and `cmpN` is proved unconditionally above by `continuousOn_ampN_actualPk` and
`continuousOn_cmpN_actualPk`). -/
def ActualBlockIntegralBounds (D : SeqData) : Prop :=
  ∀ (dm dp : ℝ), D.RepairStanding dm dp → ∀ κ : IIIa.PlanarFrameKernels, SeedLink D κ →
    ∀ (m : ℝ) [Fact (1 < m)], 8 < m →
      ∃ (CS bS K : ℝ) (p : ℕ) (C g : ℝ) (N : ℕ),
        0 < bS ∧ 0 ≤ CS ∧ 0 ≤ K ∧ 0 < C ∧ 0 < g ∧
        ∀ n ≥ N, ∀ (FI : FlatInstData κ (nu D n) (cOf (nu D n)) m (D.train n)),
          let δn := deltaC (K * (nu D n)⁻¹ ^ p) CS bS (nu D n) (nu D n ^ (-2 : ℝ))
          ∀ t ∈ Icc (0 : ℝ) (1.1 / nu D n), ∀ x : Xmc (cOf (nu D n)) m,
            (∀ s ∈ Icc t (2 / nu D n),
              cmpN (actualPk FI) D.Pl.eigenvalue D.Pl.kappa (nu D n) t x s ≤
                C * Real.exp (-g * (s - t)) *
                    cmpN (actualPk FI) D.Pl.eigenvalue D.Pl.kappa (nu D n) t x t +
                  C * (nu D n + δn) * ∫ r in t..s, Real.exp (-g * (s - r)) *
                    (‖ampN (actualPk FI) D.Pl.eigenvalue D.Pl.kappa (nu D n) t x true r‖ +
                      ‖ampN (actualPk FI) D.Pl.eigenvalue D.Pl.kappa (nu D n) t x false r‖)) ∧
            (∀ j, ∀ s ∈ Icc t (2 / nu D n),
              ‖ampN (actualPk FI) D.Pl.eigenvalue D.Pl.kappa (nu D n) t x j s -
                  ampN (actualPk FI) D.Pl.eigenvalue D.Pl.kappa (nu D n) t x j t‖ ≤
                ∫ r in t..s, (C * δn *
                    (‖ampN (actualPk FI) D.Pl.eigenvalue D.Pl.kappa (nu D n) t x true r‖ +
                      ‖ampN (actualPk FI) D.Pl.eigenvalue D.Pl.kappa (nu D n) t x false r‖) +
                  C * (nu D n + δn) *
                    cmpN (actualPk FI) D.Pl.eigenvalue D.Pl.kappa (nu D n) t x r))

/-- **Assembly of `G1.RetainedBlocksActual D`** from `ActualBlockIntegralBounds D` and the
unconditional continuity lemmas `continuousOn_ampN_actualPk` and `continuousOn_cmpN_actualPk`. -/
theorem retainedBlocksActual_of (D : SeqData) (hInt : ActualBlockIntegralBounds D) :
    G1.RetainedBlocksActual D := by
  intro dm dp hD κ hκ m hfact hm S hS
  obtain ⟨CS, bS, K, p, C, g, N1, hbS, hCS, hK, hC, hg, hB⟩ := hInt dm dp hD κ hκ m hm
  obtain ⟨N2, hN2⟩ := Filter.eventually_atTop.mp hS
  refine ⟨CS, bS, K, p, hbS, hCS, hK, C, g, max N1 N2, hC, hg, fun n hn t ht => ?_⟩
  obtain ⟨FI, hSn⟩ := hN2 n (le_trans (le_max_right _ _) hn)
  have hpk : (S n).pk = actualPk FI := congrArg ConcreteYF.FlatSetting.pk hSn
  dsimp only
  rw [hpk]
  intro x
  have hν : 0 < nu D n := retNu_pos D.Pl D.σ₀ n
  obtain ⟨hcmp, hamp⟩ := hB n (le_trans (le_max_left _ _) hn) FI t ht x
  exact ⟨fun j => continuousOn_ampN_actualPk FI D.Pl.eigenvalue D.Pl.kappa hν ht.1 x j,
    continuousOn_cmpN_actualPk FI D.Pl.eigenvalue D.Pl.kappa hν ht.1 x, hcmp, hamp⟩

end UnforcedLeray.Short.PartIIIb.Concrete.FlatUnif
