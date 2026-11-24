import UnforcedLeray.Short.PartIIb.Sub.PartIIb_F8_1_org.DuhamelRegularity.WindowGlue

/-!
# `PartII-b:F8/1/org/3` (`DuhamelRegularity.lean`): Unit-horizon Duhamel `H¹ → H²` regularity
for the global meridional correction (`MeridionalDuhamelRegularity`, SP 2301–2305)

Source of record: `the November 2 reference manuscript` (SP), lines 2296–2305:
- "On `0 < s < 2`, Duhamel and `(short-bg:hardy)` give the weighted `L^p(s^{13/8} ds; H²)` estimate.
  For `s ≥ 2` use Duhamel only on `[s - 1, s]`; weights at `s` and `s - r`, `0 < r < 1`, are
  comparable."

## Architecture

1. **Helper modules (`DuhamelRegularity/WeakAndSlices.lean`, `DuhamelRegularity/WindowGlue.lean`)**:
   - Local `Ioo a b` distributional calculus (`HasWeakFOOnIoo`, `HasWeakVecOnIoo`), distributional
     uniqueness on open age windows, and exact commutator-free spatial gluing via `Real.smoothTransition`.
   - `L¹(0, B)` integrability of `G(s) = ‖g(s)‖_{H¹}` on every bounded age horizon `(0, B]` from
     `hardyL1_proof` (`sLpNorm (13 / 8) T₀ G < ⊤`) and `tailLpNorm (-9 / 8) T₁ G < ⊤` (`0 < T₁ ≤ T₀`).
   - Borel `QPeriodic` upgrades (`locInt_of_hasWeakFO_q` + `exists_sm_rep_vol`) and Fubini slice
     extraction (`FlatBvSliceGoodAeNeeded.jointWeakToSlice_proof`) yielding `F8U.IsCylH1Datum` on
     a.e. positive age slice.
   - Vitali one-dimensional right-Lebesgue differentiation (`Mathlib.MeasureTheory.Covering.OneDim`)
     on `BochnerTime.toPathLq`, proving `h⁻¹ ∫_σ^{σ+h} ‖z₁(t) - z₁(σ)‖_{L²(cell)}² dt → 0` at a.e.
     age `σ > 0` (eliminating single-slice modification traps in weak uniqueness).
   - Countable overlapping good-age coverings (`aSeq`, `bSeq`, `winSeq`) and `Nat.unpair` dense
     good-age selection (`denseGoodSeq`), continuous `Lp` path gluing on `Ioi 0`, periodic
     `BochnerTime.exists_isJointRep_of_continuousOn` + `wrapPlane` realization, and disjointified
     `StronglyMeasurable` `D²` assembly.

2. **This file (`DuhamelRegularity.lean`)**:
   - Defines the two self-contained unit-window `(σ, σ + 1)` PDE leaves in `namespace UnforcedLeray.Short.IIb`:
     1. `CylUnitDuhamelStep`: unit-horizon Bochner–Duhamel weak solution + `H¹`/`D²` regularity on
        `(σ, σ + 1)` from `F8U.CylOseenFlowBound A p` (`w(t) = S_0(t, σ) u₀ + ∫_σ^t S_0(t, τ) g₁(τ) dτ`).
     2. `CylUnitWeakHomogeneousUnique`: unit-horizon energy uniqueness on `(σ, σ + 1)` for weak
        homogeneous `L^∞((σ, σ + 1); H¹_σ(C_c))` solutions with right-Lebesgue zero `L²(cell)` trace at `σ⁺`.
   - Proves `meridionalDuhamelRegularity_of_leaves` unconditionally (`0 sorry`, `0 axiom`), handling
     degenerate `M < 0`, upgrading `(z, zq, zη)` and `(g, gq, gη)`, identifying every good-age unit
     Duhamel window with `z` via right-Lebesgue + right-continuous trace subtraction, gluing the
     global `H¹(C_c)`-continuous version `(z', zq', zη')` and global `D²` weak derivatives, and
     passing to the early (`a_n → 0⁺` on `(0, 1]`) and late (`q_m → (s - 1)⁺` on `(1, ∞)`) Duhamel
     `D²` bounds via set-lintegral monotonicity.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.IIb

open UnforcedLeray.Cons.C03.Concrete UnforcedLeray.PhaseSpace UnforcedLeray.B0411

namespace F8Duh

/-! ## 1. Algebraic closure of `IsCylH1Datum`, `QPeriodic`, `flatBv`, and `sliceH1Norm` -/

lemma hasWeakCellDerivC_sub_local {c : ℝ} {j : Fin 2} {f₁ g₁ f₂ g₂ : B0579.Plane → ℂ}
    (h₁ : IIIa.HasWeakCellDerivC c j f₁ g₁) (h₂ : IIIa.HasWeakCellDerivC c j f₂ g₂) :
    IIIa.HasWeakCellDerivC c j (fun y => f₁ y - f₂ y) (fun y => g₁ y - g₂ y) := by
  refine ⟨fun ψ hψ => ⟨?_, ?_⟩, fun ψ hψ => ?_⟩
  · exact ((h₁.1 ψ hψ).1.sub (h₂.1 ψ hψ).1).congr_fun
      (fun y _ => by simp only [Pi.sub_apply]; ring) (B0579.measurableSet_cell c)
  · exact ((h₁.1 ψ hψ).2.sub (h₂.1 ψ hψ).2).congr_fun
      (fun y _ => by simp only [Pi.sub_apply]; ring) (B0579.measurableSet_cell c)
  · have eL : (fun y => (f₁ y - f₂ y) * (B0579.pd j ψ y : ℂ)) =
        fun y => f₁ y * (B0579.pd j ψ y : ℂ) - f₂ y * (B0579.pd j ψ y : ℂ) := by
      funext y; ring
    have eR : (fun y => (g₁ y - g₂ y) * (ψ y : ℂ)) =
        fun y => g₁ y * (ψ y : ℂ) - g₂ y * (ψ y : ℂ) := by
      funext y; ring
    rw [eL, eR, integral_sub (h₁.1 ψ hψ).1 (h₂.1 ψ hψ).1,
      integral_sub (h₁.1 ψ hψ).2 (h₂.1 ψ hψ).2, h₁.2 ψ hψ, h₂.2 ψ hψ]
    ring

lemma isCylH1Datum_sub {c : ℝ} {u₁ uq₁ uη₁ u₂ uq₂ uη₂ : B0579.Plane → CMerid}
    (h₁ : F8U.IsCylH1Datum c u₁ uq₁ uη₁) (h₂ : F8U.IsCylH1Datum c u₂ uq₂ uη₂) :
    F8U.IsCylH1Datum c (u₁ - u₂) (uq₁ - uq₂) (uη₁ - uη₂) where
  weak_q k := hasWeakCellDerivC_sub_local (h₁.weak_q k) (h₂.weak_q k)
  weak_eta k := hasWeakCellDerivC_sub_local (h₁.weak_eta k) (h₂.weak_eta k)
  solenoidal ψ hψ := by
    have heq : (fun y => (u₁ - u₂) y 0 * (B0579.pd 0 ψ y : ℂ) +
          (u₁ - u₂) y 1 * (B0579.pd 1 ψ y : ℂ)) =
        fun y => (u₁ y 0 * (B0579.pd 0 ψ y : ℂ) + u₁ y 1 * (B0579.pd 1 ψ y : ℂ)) -
          (u₂ y 0 * (B0579.pd 0 ψ y : ℂ) + u₂ y 1 * (B0579.pd 1 ψ y : ℂ)) := by
      funext y; simp only [Pi.sub_apply, PiLp.sub_apply]; ring
    rw [heq]
    exact ⟨(h₁.solenoidal ψ hψ).1.sub (h₂.solenoidal ψ hψ).1,
      by rw [integral_sub (h₁.solenoidal ψ hψ).1 (h₂.solenoidal ψ hψ).1,
        (h₁.solenoidal ψ hψ).2, (h₂.solenoidal ψ hψ).2, sub_self]⟩
  memL2 := ⟨h₁.memL2.1.sub h₂.memL2.1, h₁.memL2.2.1.sub h₂.memL2.2.1,
    h₁.memL2.2.2.sub h₂.memL2.2.2⟩

lemma qPeriodic_sub {c : ℝ} {u₁ u₂ : CProf} (h₁ : QPeriodic c u₁) (h₂ : QPeriodic c u₂) :
    QPeriodic c (u₁ - u₂) := by
  unfold QPeriodic at h₁ h₂ ⊢
  filter_upwards [h₁, h₂] with x hx₁ hx₂
  simp [hx₁, hx₂]

lemma sliceH1Norm_eq_cylH1 (c : ℝ) (u uq uη : CProf) (s : ℝ) :
    sliceH1Norm c u uq uη s = F8U.cylH1 c (F8U.slice u s) (F8U.slice uq s) (F8U.slice uη s) :=
  rfl

lemma sliceH1Norm_sub_le (c : ℝ) {u₁ uq₁ uη₁ u₂ uq₂ uη₂ : CProf}
    (hu₁ : StronglyMeasurable u₁) (huq₁ : StronglyMeasurable uq₁) (huη₁ : StronglyMeasurable uη₁)
    (hu₂ : StronglyMeasurable u₂) (huq₂ : StronglyMeasurable uq₂) (huη₂ : StronglyMeasurable uη₂)
    (s : ℝ) :
    sliceH1Norm c (u₁ - u₂) (uq₁ - uq₂) (uη₁ - uη₂) s ≤
      sliceH1Norm c u₁ uq₁ uη₁ s + sliceH1Norm c u₂ uq₂ uη₂ s := by
  unfold sliceH1Norm
  have b1 : eLpNorm (fun z => (u₁ - u₂) (s, z)) 2 (volume.restrict (B0579.cell c)) ≤
      eLpNorm (fun z => u₁ (s, z)) 2 (volume.restrict (B0579.cell c)) +
        eLpNorm (fun z => u₂ (s, z)) 2 (volume.restrict (B0579.cell c)) :=
    eLpNorm_sub_le (F8L.sliceMeas hu₁ s).aestronglyMeasurable
      (F8L.sliceMeas hu₂ s).aestronglyMeasurable (by norm_num)
  have b2 : eLpNorm (fun z => (uq₁ - uq₂) (s, z)) 2 (volume.restrict (B0579.cell c)) ≤
      eLpNorm (fun z => uq₁ (s, z)) 2 (volume.restrict (B0579.cell c)) +
        eLpNorm (fun z => uq₂ (s, z)) 2 (volume.restrict (B0579.cell c)) :=
    eLpNorm_sub_le (F8L.sliceMeas huq₁ s).aestronglyMeasurable
      (F8L.sliceMeas huq₂ s).aestronglyMeasurable (by norm_num)
  have b3 : eLpNorm (fun z => (uη₁ - uη₂) (s, z)) 2 (volume.restrict (B0579.cell c)) ≤
      eLpNorm (fun z => uη₁ (s, z)) 2 (volume.restrict (B0579.cell c)) +
        eLpNorm (fun z => uη₂ (s, z)) 2 (volume.restrict (B0579.cell c)) :=
    eLpNorm_sub_le (F8L.sliceMeas huη₁ s).aestronglyMeasurable
      (F8L.sliceMeas huη₂ s).aestronglyMeasurable (by norm_num)
  calc eLpNorm (fun z => (u₁ - u₂) (s, z)) 2 _ +
        eLpNorm (fun z => (uq₁ - uq₂) (s, z)) 2 _ +
        eLpNorm (fun z => (uη₁ - uη₂) (s, z)) 2 _
      ≤ (eLpNorm (fun z => u₁ (s, z)) 2 _ + eLpNorm (fun z => u₂ (s, z)) 2 _) +
          (eLpNorm (fun z => uq₁ (s, z)) 2 _ + eLpNorm (fun z => uq₂ (s, z)) 2 _) +
          (eLpNorm (fun z => uη₁ (s, z)) 2 _ + eLpNorm (fun z => uη₂ (s, z)) 2 _) :=
        add_le_add (add_le_add b1 b2) b3
    _ = _ := by ac_rfl

lemma flatBv_sub {ν c : ℝ} (tr : B0140.TrainSol ν c) (u₁ uq₁ uη₁ u₂ uq₂ uη₂ : CProf) (x : Coord) :
    flatBv tr (u₁ - u₂) (uq₁ - uq₂) (uη₁ - uη₂) x =
      flatBv tr u₁ uq₁ uη₁ x - flatBv tr u₂ uq₂ uη₂ x := by
  ext i
  simp only [flatBv, Pi.sub_apply, PiLp.sub_apply, WithLp.ofLp_toLp]
  ring

lemma transfer_equation_both (p : Params) {g g' z zq zη z' zq' zη' : CProf}
    (hg : g =ᵐ[volume.restrict {x : Coord | 0 < x.1}] g')
    (hz : z =ᵐ[volume.restrict {x : Coord | 0 < x.1}] z')
    (hzq : zq =ᵐ[volume.restrict {x : Coord | 0 < x.1}] zq')
    (hzη : zη =ᵐ[volume.restrict {x : Coord | 0 < x.1}] zη')
    (heq : ∀ Ψ, IsPlanarSolTest Ψ →
      Integrable (fun x => ∑ i : Fin 2, z x i * meridTranspose p.ν Ψ x i) ∧
        Integrable (cdot (flatBv p.train z zq zη) Ψ) ∧
        Integrable (cdot g Ψ) ∧
        ∫ x, (∑ i : Fin 2, z x i * meridTranspose p.ν Ψ x i +
            cdot (flatBv p.train z zq zη) Ψ x) =
          ∫ x, cdot g Ψ x) :
    ∀ Ψ, IsPlanarSolTest Ψ →
      Integrable (fun x => ∑ i : Fin 2, z' x i * meridTranspose p.ν Ψ x i) ∧
        Integrable (cdot (flatBv p.train z' zq' zη') Ψ) ∧
        Integrable (cdot g' Ψ) ∧
        ∫ x, (∑ i : Fin 2, z' x i * meridTranspose p.ν Ψ x i +
            cdot (flatBv p.train z' zq' zη') Ψ x) =
          ∫ x, cdot g' Ψ x := by
  have heq₁ := F8L.transfer_equation p hz hzq hzη heq
  intro Ψ hΨ
  obtain ⟨h1, h2, h3, h4⟩ := heq₁ Ψ hΨ
  have eG : cdot g Ψ =ᵐ[volume] cdot g' Ψ := by
    filter_upwards [F8L.ae_pos hg] with x hx
    by_cases h0 : 0 < x.1
    · simp [cdot, hx h0]
    · have hV : ∀ i : Fin 2, Ψ x i = 0 :=
        fun i => (F8L.Vanish.of_test (hΨ.smooth i)).eq h0
      simp [cdot, hV]
  exact ⟨h1, h2, (integrable_congr eG).1 h3, h4.trans (integral_congr_ae eG)⟩

/-! ## 2. Right-Lebesgue trace of `z₁ - w` from Vitali differentiation + right-initial continuity -/

lemma tendsto_avg_Ioc_of_tendsto_nhdsGT {σ : ℝ} {φ : ℝ → ℝ}
    (hφ_meas : AEStronglyMeasurable φ volume)
    (hφ_nn : ∀ t, σ < t → 0 ≤ φ t)
    (hφ_lim : Tendsto φ (𝓝[>] σ) (𝓝 0)) :
    Tendsto (fun h : ℝ => h⁻¹ * ∫ t in Ioc σ (σ + h), φ t) (𝓝[>] 0) (𝓝 0) := by
  rw [Metric.tendsto_nhds]
  intro ε hε
  have hev : {t : ℝ | φ t < ε / 2} ∈ 𝓝[>] σ :=
    hφ_lim.eventually (gt_mem_nhds (half_pos hε))
  rw [Metric.mem_nhdsWithin_iff] at hev
  obtain ⟨δ, hδ, hball⟩ := hev
  filter_upwards [Ioo_mem_nhdsGT hδ] with h hh
  have hh0 : 0 < h := hh.1
  have hhδ : h < δ := hh.2
  have hsub_le : ∀ t ∈ Ioc σ (σ + h), φ t ≤ ε / 2 := by
    intro t ht
    have hdist : t ∈ Metric.ball σ δ ∩ Ioi σ := by
      refine ⟨?_, ht.1⟩
      rw [Metric.mem_ball, Real.dist_eq, abs_of_pos (sub_pos.2 ht.1)]
      linarith [ht.2]
    exact (hball hdist).le
  have hint : IntegrableOn φ (Ioc σ (σ + h)) volume := by
    refine Integrable.mono' (integrableOn_const (C := ε / 2) (by simp [Real.volume_Ioc]))
      hφ_meas.restrict ?_
    rw [ae_restrict_iff' measurableSet_Ioc]
    exact Eventually.of_forall fun t ht => by
      rw [Real.norm_of_nonneg (hφ_nn t ht.1)]
      exact hsub_le t ht
  have h_nn : 0 ≤ h⁻¹ * ∫ t in Ioc σ (σ + h), φ t :=
    mul_nonneg (inv_nonneg.2 hh0.le)
      (setIntegral_nonneg measurableSet_Ioc (fun t ht => hφ_nn t ht.1))
  rw [Real.dist_eq, sub_zero, abs_of_nonneg h_nn]
  have hint_le : ∫ t in Ioc σ (σ + h), φ t ≤ ∫ _ in Ioc σ (σ + h), (ε / 2) :=
    setIntegral_mono_on hint (integrableOn_const (by simp [Real.volume_Ioc]))
      measurableSet_Ioc hsub_le
  have hconst_int : ∫ _ in Ioc σ (σ + h), (ε / 2) = h * (ε / 2) := by
    rw [setIntegral_const, smul_eq_mul]
    simp [Measure.real, Real.volume_Ioc, hh0.le]
  calc h⁻¹ * ∫ t in Ioc σ (σ + h), φ t
      ≤ h⁻¹ * (h * (ε / 2)) :=
        mul_le_mul_of_nonneg_left (hint_le.trans hconst_int.le) (inv_nonneg.2 hh0.le)
    _ = ε / 2 := by field_simp [hh0.ne']
    _ < ε := half_lt_self hε

lemma rightLebesgue_sub_of_initial {c M σ : ℝ} (hM : 0 ≤ M) (hσ : 0 < σ)
    {z₁ w wq wη : CProf} {uq₀ uη₀ : B0579.Plane → CMerid}
    (hz₁_sm : StronglyMeasurable z₁) (hw_sm : StronglyMeasurable w)
    (hbnd_z : ∀ᵐ t ∂volume, 0 < t → F8U.cellL2 c (F8U.slice z₁ t) ≤ ENNReal.ofReal M)
    (hmem_zσ : MemLp (F8U.slice z₁ σ) 2 (volume.restrict (B0579.cell c)))
    (hmem_w : ∀ t ∈ Ioo σ (σ + 1), MemLp (F8U.slice w t) 2 (volume.restrict (B0579.cell c)))
    (h_leb : Tendsto (fun h : ℝ => h⁻¹ *
      ∫ t in Ioc σ (σ + h), (F8U.cellL2 c (fun y => z₁ (t, y) - z₁ (σ, y))).toReal ^ 2)
      (𝓝[>] 0) (𝓝 0))
    (h_init : Tendsto (fun t => F8U.cylH1 c (fun y => w (t, y) - z₁ (σ, y))
      (fun y => wq (t, y) - uq₀ y) (fun y => wη (t, y) - uη₀ y)) (𝓝[>] σ) (𝓝 0)) :
    Tendsto (fun h : ℝ => h⁻¹ *
      ∫ t in Ioc σ (σ + h), (F8U.cellL2 c (F8U.slice (z₁ - w) t)).toReal ^ 2)
      (𝓝[>] 0) (𝓝 0) := by
  let μc := volume.restrict (B0579.cell c)
  let ψ₁ : ℝ → ℝ := fun t => (F8U.cellL2 c (fun y => z₁ (t, y) - z₁ (σ, y))).toReal ^ 2
  let ψ₂ : ℝ → ℝ := fun t => (F8U.cellL2 c (fun y => w (t, y) - z₁ (σ, y))).toReal ^ 2
  let ψ : ℝ → ℝ := fun t => (F8U.cellL2 c (F8U.slice (z₁ - w) t)).toReal ^ 2
  have hmeas_cell : ∀ f : CProf, StronglyMeasurable f →
      Measurable (fun t : ℝ => (F8U.cellL2 c (F8U.slice f t)).toReal ^ 2) := by
    intro f hf
    have hm : Measurable (fun t : ℝ => (∫⁻ y, ‖f (t, y)‖ₑ ^ (2 : ℝ) ∂μc) ^ (1 / (2 : ℝ))) :=
      ((hf.enorm.pow_const _).lintegral_prod_right').pow_const _
    have heq : (fun t : ℝ => F8U.cellL2 c (F8U.slice f t)) =
        fun t => (∫⁻ y, ‖f (t, y)‖ₑ ^ (2 : ℝ) ∂μc) ^ (1 / (2 : ℝ)) := by
      funext t
      unfold F8U.cellL2 F8U.slice
      rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by norm_num)]
      rfl
    exact ((heq ▸ hm).ennreal_toReal).pow_const 2
  have hψ₁_meas : Measurable ψ₁ :=
    hmeas_cell (fun x => z₁ x - z₁ (σ, x.2))
      (hz₁_sm.sub ((F8L.sliceMeas hz₁_sm σ).comp_measurable measurable_snd))
  have hψ₂_meas : Measurable ψ₂ :=
    hmeas_cell (fun x => w x - z₁ (σ, x.2))
      (hw_sm.sub ((F8L.sliceMeas hz₁_sm σ).comp_measurable measurable_snd))
  have hψ_meas : Measurable ψ := hmeas_cell (z₁ - w) (hz₁_sm.sub hw_sm)
  have h_w_cell : Tendsto (fun t => F8U.cellL2 c (fun y => w (t, y) - z₁ (σ, y))) (𝓝[>] σ) (𝓝 0) :=
    tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds h_init
      (fun _ => bot_le) (fun _ => le_self_add.trans le_self_add)
  have hψ₂_lim : Tendsto ψ₂ (𝓝[>] σ) (𝓝 0) := by
    have htr : Tendsto (fun t => (F8U.cellL2 c (fun y => w (t, y) - z₁ (σ, y))).toReal)
        (𝓝[>] σ) (𝓝 0) := by
      simpa [Function.comp_def] using
        (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp h_w_cell
    simpa [ψ₂] using htr.pow 2
  have h_avg₂ : Tendsto (fun h : ℝ => h⁻¹ * ∫ t in Ioc σ (σ + h), ψ₂ t) (𝓝[>] 0) (𝓝 0) :=
    tendsto_avg_Ioc_of_tendsto_nhdsGT hψ₂_meas.aestronglyMeasurable
      (fun _ _ => sq_nonneg _) hψ₂_lim
  have h_upper : Tendsto (fun h : ℝ =>
      2 * (h⁻¹ * ∫ t in Ioc σ (σ + h), ψ₁ t) + 2 * (h⁻¹ * ∫ t in Ioc σ (σ + h), ψ₂ t))
      (𝓝[>] 0) (𝓝 0) := by
    simpa using (h_leb.const_mul 2).add (h_avg₂.const_mul 2)
  have hev_int₂ : {t : ℝ | ψ₂ t < 1} ∈ 𝓝[>] σ :=
    hψ₂_lim.eventually (gt_mem_nhds one_pos)
  rw [Metric.mem_nhdsWithin_iff] at hev_int₂
  obtain ⟨δ₂, hδ₂, hball₂⟩ := hev_int₂
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds h_upper ?_ ?_
  · filter_upwards [self_mem_nhdsWithin] with h hh
    have hh0 : 0 < h := hh
    exact mul_nonneg (inv_nonneg.2 hh0.le) (integral_nonneg fun _ => sq_nonneg _)
  · filter_upwards [Ioo_mem_nhdsGT (lt_min one_pos hδ₂)] with h hh
    have hh0 : 0 < h := hh.1
    have hh1 : h < 1 := lt_of_lt_of_le hh.2 (min_le_left _ _)
    have hhδ₂ : h < δ₂ := lt_of_lt_of_le hh.2 (min_le_right _ _)
    have hint₁ : IntegrableOn ψ₁ (Ioc σ (σ + h)) volume := by
      let C₁_bnd : ℝ := (M + (F8U.cellL2 c (F8U.slice z₁ σ)).toReal) ^ 2
      refine Integrable.mono' (integrableOn_const (C := C₁_bnd) (by simp [Real.volume_Ioc]))
        hψ₁_meas.aestronglyMeasurable.restrict ?_
      rw [ae_restrict_iff' measurableSet_Ioc]
      filter_upwards [hbnd_z] with t ht_bnd ht_mem
      have ht_pos : 0 < t := lt_trans hσ ht_mem.1
      rw [Real.norm_of_nonneg (sq_nonneg _)]
      have htri : F8U.cellL2 c (fun y => z₁ (t, y) - z₁ (σ, y)) ≤
          F8U.cellL2 c (F8U.slice z₁ t) + F8U.cellL2 c (F8U.slice z₁ σ) :=
        eLpNorm_sub_le (F8L.sliceMeas hz₁_sm t).aestronglyMeasurable
          (F8L.sliceMeas hz₁_sm σ).aestronglyMeasurable (by norm_num)
      have hlt₁ : F8U.cellL2 c (F8U.slice z₁ t) < ⊤ :=
        lt_of_le_of_lt (ht_bnd ht_pos) ENNReal.ofReal_lt_top
      have hlt₂ : F8U.cellL2 c (F8U.slice z₁ σ) < ⊤ := hmem_zσ.2
      have htr_le : (F8U.cellL2 c (fun y => z₁ (t, y) - z₁ (σ, y))).toReal ≤
          M + (F8U.cellL2 c (F8U.slice z₁ σ)).toReal := by
        calc (F8U.cellL2 c (fun y => z₁ (t, y) - z₁ (σ, y))).toReal
            ≤ (F8U.cellL2 c (F8U.slice z₁ t) + F8U.cellL2 c (F8U.slice z₁ σ)).toReal :=
              ENNReal.toReal_mono (ENNReal.add_ne_top.2 ⟨hlt₁.ne, hlt₂.ne⟩) htri
          _ = (F8U.cellL2 c (F8U.slice z₁ t)).toReal + (F8U.cellL2 c (F8U.slice z₁ σ)).toReal :=
              ENNReal.toReal_add hlt₁.ne hlt₂.ne
          _ ≤ M + (F8U.cellL2 c (F8U.slice z₁ σ)).toReal :=
              add_le_add (ENNReal.toReal_le_of_le_ofReal hM (ht_bnd ht_pos)) le_rfl
      exact pow_le_pow_left₀ ENNReal.toReal_nonneg htr_le 2
    have hint₂ : IntegrableOn ψ₂ (Ioc σ (σ + h)) volume := by
      refine Integrable.mono' (integrableOn_const (C := 1) (by simp [Real.volume_Ioc]))
        hψ₂_meas.aestronglyMeasurable.restrict ?_
      rw [ae_restrict_iff' measurableSet_Ioc]
      exact Eventually.of_forall fun t ht => by
        rw [Real.norm_of_nonneg (sq_nonneg _)]
        have hdist : t ∈ Metric.ball σ δ₂ ∩ Ioi σ := by
          refine ⟨?_, ht.1⟩
          rw [Metric.mem_ball, Real.dist_eq, abs_of_pos (sub_pos.2 ht.1)]
          linarith [ht.2]
        exact (hball₂ hdist).le
    have hae_le : ∀ᵐ t ∂(volume.restrict (Ioc σ (σ + h))), ψ t ≤ 2 * ψ₁ t + 2 * ψ₂ t := by
      rw [ae_restrict_iff' measurableSet_Ioc]
      filter_upwards [hbnd_z] with t ht_bnd ht_mem
      have ht_pos : 0 < t := lt_trans hσ ht_mem.1
      have ht_in : t ∈ Ioo σ (σ + 1) := ⟨ht_mem.1, lt_of_le_of_lt ht_mem.2 (by linarith)⟩
      have heq_fn : F8U.slice (z₁ - w) t =
          (fun y => z₁ (t, y) - z₁ (σ, y)) - (fun y => w (t, y) - z₁ (σ, y)) := by
        funext y; simp [F8U.slice]
      have htri : F8U.cellL2 c (F8U.slice (z₁ - w) t) ≤
          F8U.cellL2 c (fun y => z₁ (t, y) - z₁ (σ, y)) +
            F8U.cellL2 c (fun y => w (t, y) - z₁ (σ, y)) := by
        rw [heq_fn]
        exact eLpNorm_sub_le
          ((F8L.sliceMeas hz₁_sm t).sub (F8L.sliceMeas hz₁_sm σ)).aestronglyMeasurable
          ((F8L.sliceMeas hw_sm t).sub (F8L.sliceMeas hz₁_sm σ)).aestronglyMeasurable (by norm_num)
      have hm₁z : MemLp (F8U.slice z₁ t) 2 μc :=
        ⟨(F8L.sliceMeas hz₁_sm t).aestronglyMeasurable,
          lt_of_le_of_lt (ht_bnd ht_pos) ENNReal.ofReal_lt_top⟩
      have hm₁ : MemLp (fun y => z₁ (t, y) - z₁ (σ, y)) 2 μc := hm₁z.sub hmem_zσ
      have hm₂ : MemLp (fun y => w (t, y) - z₁ (σ, y)) 2 μc := (hmem_w t ht_in).sub hmem_zσ
      have ha_le : (F8U.cellL2 c (F8U.slice (z₁ - w) t)).toReal ≤
          (F8U.cellL2 c (fun y => z₁ (t, y) - z₁ (σ, y))).toReal +
            (F8U.cellL2 c (fun y => w (t, y) - z₁ (σ, y))).toReal := by
        calc (F8U.cellL2 c (F8U.slice (z₁ - w) t)).toReal
            ≤ (F8U.cellL2 c (fun y => z₁ (t, y) - z₁ (σ, y)) +
                F8U.cellL2 c (fun y => w (t, y) - z₁ (σ, y))).toReal :=
              ENNReal.toReal_mono (ENNReal.add_ne_top.2 ⟨hm₁.2.ne, hm₂.2.ne⟩) htri
          _ = _ := ENNReal.toReal_add hm₁.2.ne hm₂.2.ne
      set a := (F8U.cellL2 c (fun y => z₁ (t, y) - z₁ (σ, y))).toReal
      set b := (F8U.cellL2 c (fun y => w (t, y) - z₁ (σ, y))).toReal
      have ha0 : 0 ≤ a := ENNReal.toReal_nonneg
      have hb0 : 0 ≤ b := ENNReal.toReal_nonneg
      have hc0 : 0 ≤ (F8U.cellL2 c (F8U.slice (z₁ - w) t)).toReal := ENNReal.toReal_nonneg
      dsimp only [ψ, ψ₁, ψ₂]
      nlinarith [sq_nonneg (a - b)]
    have hint_rhs : IntegrableOn (fun t => 2 * ψ₁ t + 2 * ψ₂ t) (Ioc σ (σ + h)) volume :=
      (hint₁.const_mul 2).add (hint₂.const_mul 2)
    have hint_ψ : IntegrableOn ψ (Ioc σ (σ + h)) volume := by
      refine Integrable.mono' hint_rhs hψ_meas.aestronglyMeasurable.restrict ?_
      filter_upwards [hae_le] with t ht
      rw [Real.norm_of_nonneg (sq_nonneg _)]
      exact ht
    have hint_le := integral_mono_ae hint_ψ hint_rhs hae_le
    rw [integral_add (hint₁.const_mul 2) (hint₂.const_mul 2),
      integral_const_mul, integral_const_mul] at hint_le
    calc h⁻¹ * ∫ t in Ioc σ (σ + h), ψ t
        ≤ h⁻¹ * ((2 * ∫ t in Ioc σ (σ + h), ψ₁ t) + 2 * ∫ t in Ioc σ (σ + h), ψ₂ t) :=
          mul_le_mul_of_nonneg_left hint_le (inv_nonneg.2 hh0.le)
      _ = 2 * (h⁻¹ * ∫ t in Ioc σ (σ + h), ψ₁ t) + 2 * (h⁻¹ * ∫ t in Ioc σ (σ + h), ψ₂ t) := by
          ring

/-! ## 3. Degenerate `M < 0` handler -/

lemma ae_zero_of_sliceH1Norm_nonpos {c M : ℝ} (hc : 0 < c) (hM : M < 0)
    {z zq zη : CProf}
    (hz_per : QPeriodic c z) (hzq : HasWeakVec vQ0 dZero z zq) (hzη : HasWeakVec vEta dZero z zη)
    (hsol : ∀ φ, IsCoordTest φ →
      Integrable (fun x => z x 0 * (cpd 1 φ x : ℂ) + z x 1 * (cpd 2 φ x : ℂ)) ∧
        ∫ x, (z x 0 * (cpd 1 φ x : ℂ) + z x 1 * (cpd 2 φ x : ℂ)) = 0)
    (hbnd : ∀ s : ℝ, 0 < s → sliceH1Norm c z zq zη s ≤ ENNReal.ofReal M) :
    (0 : CProf) =ᵐ[volume.restrict {x : Coord | 0 < x.1}] z ∧
      (0 : CProf) =ᵐ[volume.restrict {x : Coord | 0 < x.1}] zq ∧
      (0 : CProf) =ᵐ[volume.restrict {x : Coord | 0 < x.1}] zη := by
  have hof0 : ENNReal.ofReal M = 0 := ENNReal.ofReal_of_nonpos hM.le
  obtain ⟨z₁, zq₁, zη₁, hz₁_sm, hzq₁_sm, hzη₁_sm, hz₁_per, hzq₁_per, hzη₁_per,
    _, _, _, hz₁_ae, hzq₁_ae, hzη₁_ae, hsl_eq, _⟩ :=
    upgrade_weakH1_solenoidal hc hz_per hzq hzη hsol
  have hcell_zero : ∀ᵐ s ∂volume, 0 < s →
      (fun y => z₁ (s, y)) =ᵐ[volume.restrict (B0579.cell c)] 0 ∧
      (fun y => zq₁ (s, y)) =ᵐ[volume.restrict (B0579.cell c)] 0 ∧
      (fun y => zη₁ (s, y)) =ᵐ[volume.restrict (B0579.cell c)] 0 := by
    filter_upwards [hsl_eq] with s hs hs0
    have h0 : sliceH1Norm c z₁ zq₁ zη₁ s = 0 := by
      refine le_antisymm ?_ bot_le
      rw [hs hs0, ← hof0]
      exact hbnd s hs0
    unfold sliceH1Norm at h0
    have h12 : eLpNorm (fun y => z₁ (s, y)) 2 (volume.restrict (B0579.cell c)) +
        eLpNorm (fun y => zq₁ (s, y)) 2 (volume.restrict (B0579.cell c)) = 0 :=
      (add_eq_zero.1 h0).1
    have h3 : eLpNorm (fun y => zη₁ (s, y)) 2 (volume.restrict (B0579.cell c)) = 0 :=
      (add_eq_zero.1 h0).2
    have h1 : eLpNorm (fun y => z₁ (s, y)) 2 (volume.restrict (B0579.cell c)) = 0 :=
      (add_eq_zero.1 h12).1
    have h2 : eLpNorm (fun y => zq₁ (s, y)) 2 (volume.restrict (B0579.cell c)) = 0 :=
      (add_eq_zero.1 h12).2
    exact ⟨(eLpNorm_eq_zero_iff (F8L.sliceMeas hz₁_sm s).aestronglyMeasurable (by norm_num)).1 h1,
      (eLpNorm_eq_zero_iff (F8L.sliceMeas hzq₁_sm s).aestronglyMeasurable (by norm_num)).1 h2,
      (eLpNorm_eq_zero_iff (F8L.sliceMeas hzη₁_sm s).aestronglyMeasurable (by norm_num)).1 h3⟩
  have hper0 : QPeriodic c (0 : CProf) := QPerHalf.of_ae (Eventually.of_forall fun _ => rfl)
  have hvol_zero : ∀ u₁ : CProf, StronglyMeasurable u₁ → QPeriodic c u₁ →
      (∀ᵐ s ∂volume, 0 < s → (fun y => u₁ (s, y)) =ᵐ[volume.restrict (B0579.cell c)] 0) →
      (0 : CProf) =ᵐ[volume.restrict {x : Coord | 0 < x.1}] u₁ := by
    intro u₁ hu₁_sm hu₁_per hcu
    have hN : ∀ N : ℕ, ∀ᵐ x : Coord, x.1 ∈ Ioo 0 ((N : ℝ) + 1) → (0 : CProf) x = u₁ x := by
      intro N
      refine ContBodySourceAux.ae_vol_eq_of_ae_cell_periodic hc stronglyMeasurable_const hu₁_sm
        hper0 hu₁_per ?_
      filter_upwards [hcu] with s hs hsN
      exact (hs hsN.1).symm
    rw [Filter.EventuallyEq, ae_restrict_iff' (measurableSet_lt measurable_const measurable_fst)]
    filter_upwards [ae_all_iff.2 hN] with x hx hp
    obtain ⟨N, hN_gt⟩ := exists_nat_gt x.1
    exact hx N ⟨hp, by linarith⟩
  exact ⟨(hvol_zero z₁ hz₁_sm hz₁_per (hcell_zero.mono fun _ h hs => (h hs).1)).trans hz₁_ae,
    (hvol_zero zq₁ hzq₁_sm hzq₁_per (hcell_zero.mono fun _ h hs => (h hs).2.1)).trans hzq₁_ae,
    (hvol_zero zη₁ hzη₁_sm hzη₁_per (hcell_zero.mono fun _ h hs => (h hs).2.2)).trans hzη₁_ae⟩

end F8Duh

/-! ## 4. Unit-window `(σ, σ + 1)` PDE leaves (`namespace UnforcedLeray.Short.IIb`) -/

/-- **Unit-window Bochner–Duhamel step** (`CylUnitDuhamelStep`, SP 2296–2305): given the cylinder
Oseen flow bound `F8U.CylOseenFlowBound A p` (`0 < A`, `p.ν ≤ 1`), at any initial age `σ ≥ 0`, for
every initial datum `(u₀, uq₀, uη₀)` in `H¹_σ(C_c)` (`F8U.IsCylH1Datum`) and every strongly
measurable `q`-periodic forcing `(g₁, gq₁, gη₁)` in `L¹((σ, σ + 1]; H¹_σ(C_c))`, the Duhamel formula
`w(t) = S_0(t, σ) u₀ + ∫_σ^t S_0(t, τ) g₁(τ) dτ` defines strongly measurable `q`-periodic profiles
`(w, wq, wη, D2)` on `(σ, σ + 1)` that:
1. lie in `C((σ, σ + 1); H¹_σ(C_c))` with `w(t) → u₀` in `H¹(C_c)` as `t → σ⁺` and
   `‖w(t)‖_{H¹} ≤ A (‖u₀‖_{H¹} + ∫_σ^t ‖g₁(τ)‖_{H¹} dτ)`,
2. have weak first and second spatial derivatives `(wq, wη, D2)` and weak solenoidality on
   `(σ, σ + 1) × ℝ²`, and solve the forced meridional equation `(∂_s - νΔ + P_0 B_v) w = g₁` against
   every planar solenoidal test supported in `(σ, σ + 1) × ℝ²`,
3. satisfy the parabolic `H¹ → H²` Duhamel estimate
   `∑_{i,j} ‖D_{ij} w(t)‖_{L²(cell)} ≤ A ν^{-1/2} ((t - σ)^{-1/2} ‖u₀‖_{H¹} + ∫_σ^t (t - τ)^{-1/2} ‖g₁(τ)‖_{H¹} dτ)`
   for a.e. `t ∈ (σ, σ + 1)`. -/
def CylUnitDuhamelStep : Prop :=
  ∀ A : ℝ, 0 < A →
    ∀ (dm dp : ℝ) (p : Params) (d : ℝ), BgRegime p d dm dp → p.ν ≤ 1 →
      F8U.CylOseenFlowBound A p →
      ∀ σ : ℝ, 0 ≤ σ →
        ∀ (u₀ uq₀ uη₀ : B0579.Plane → CMerid) (g₁ gq₁ gη₁ : CProf),
          F8U.IsCylH1Datum p.c u₀ uq₀ uη₀ →
          StronglyMeasurable g₁ → StronglyMeasurable gq₁ → StronglyMeasurable gη₁ →
          QPeriodic p.c g₁ → QPeriodic p.c gq₁ → QPeriodic p.c gη₁ →
          (∀ᵐ τ ∂volume, τ ∈ Ioc σ (σ + 1) →
            F8U.IsCylH1Datum p.c (F8U.slice g₁ τ) (F8U.slice gq₁ τ) (F8U.slice gη₁ τ)) →
          ∫⁻ τ in Ioc σ (σ + 1), sliceH1Norm p.c g₁ gq₁ gη₁ τ < ⊤ →
          ∃ (w wq wη : CProf) (D2 : Fin 2 → Fin 2 → CProf),
            StronglyMeasurable w ∧ StronglyMeasurable wq ∧ StronglyMeasurable wη ∧
            (∀ i j, StronglyMeasurable (D2 i j)) ∧
            QPeriodic p.c w ∧ QPeriodic p.c wq ∧ QPeriodic p.c wη ∧
            (∀ i j, QPeriodic p.c (D2 i j)) ∧
            (∀ t ∈ Ioo σ (σ + 1),
              F8U.IsCylH1Datum p.c (F8U.slice w t) (F8U.slice wq t) (F8U.slice wη t) ∧
                F8U.cylH1 p.c (F8U.slice w t) (F8U.slice wq t) (F8U.slice wη t) ≤
                  ENNReal.ofReal A *
                    (F8U.cylH1 p.c u₀ uq₀ uη₀ +
                      ∫⁻ τ in Ioc σ t, sliceH1Norm p.c g₁ gq₁ gη₁ τ)) ∧
            (∀ t ∈ Ioo σ (σ + 1),
              Tendsto (fun t' => F8U.cylH1 p.c (fun y => w (t', y) - w (t, y))
                (fun y => wq (t', y) - wq (t, y)) (fun y => wη (t', y) - wη (t, y)))
                (𝓝 t) (𝓝 0)) ∧
            Tendsto (fun t => F8U.cylH1 p.c (fun y => w (t, y) - u₀ y)
              (fun y => wq (t, y) - uq₀ y) (fun y => wη (t, y) - uη₀ y))
              (𝓝[>] σ) (𝓝 0) ∧
            F8Duh.HasWeakVecOnIoo σ (σ + 1) vQ0 dZero w wq ∧
            F8Duh.HasWeakVecOnIoo σ (σ + 1) vEta dZero w wη ∧
            F8Duh.HasWeakVecOnIoo σ (σ + 1) vQ0 dZero wq (D2 0 0) ∧
            F8Duh.HasWeakVecOnIoo σ (σ + 1) vEta dZero wq (D2 0 1) ∧
            F8Duh.HasWeakVecOnIoo σ (σ + 1) vQ0 dZero wη (D2 1 0) ∧
            F8Duh.HasWeakVecOnIoo σ (σ + 1) vEta dZero wη (D2 1 1) ∧
            (∀ φ, F8Duh.IsIooTest σ (σ + 1) φ →
              Integrable (fun x => w x 0 * (cpd 1 φ x : ℂ) + w x 1 * (cpd 2 φ x : ℂ)) ∧
                ∫ x, (w x 0 * (cpd 1 φ x : ℂ) + w x 1 * (cpd 2 φ x : ℂ)) = 0) ∧
            (∀ Ψ, IsPlanarSolTest Ψ →
              (∀ i, tsupport (fun x => Ψ x i) ⊆ Ioo σ (σ + 1) ×ˢ univ) →
              Integrable (fun x => ∑ i : Fin 2, w x i * meridTranspose p.ν Ψ x i) ∧
                Integrable (cdot (flatBv p.train w wq wη) Ψ) ∧
                Integrable (cdot g₁ Ψ) ∧
                ∫ x, (∑ i : Fin 2, w x i * meridTranspose p.ν Ψ x i +
                    cdot (flatBv p.train w wq wη) Ψ x) =
                  ∫ x, cdot g₁ Ψ x) ∧
            (∀ᵐ t ∂volume, t ∈ Ioo σ (σ + 1) →
              ∑ i : Fin 2, ∑ j : Fin 2, F8U.cellL2 p.c (F8U.slice (D2 i j) t) ≤
                ENNReal.ofReal (A * p.ν ^ (-1 / 2 : ℝ)) *
                  (ENNReal.ofReal ((t - σ) ^ (-1 / 2 : ℝ)) * F8U.cylH1 p.c u₀ uq₀ uη₀ +
                    ∫⁻ τ in Ioc σ t, ENNReal.ofReal ((t - τ) ^ (-1 / 2 : ℝ)) *
                      sliceH1Norm p.c g₁ gq₁ gη₁ τ))

/-- **Unit-window weak homogeneous uniqueness** (`CylUnitWeakHomogeneousUnique`, SP 2213–2217,
2296–2305): on `(σ, σ + 1)` (`σ ≥ 0`), any strongly measurable `q`-periodic weak homogeneous
solution `(δ, δq, δη) ∈ L^∞((σ, σ + 1); H¹_σ(C_c))` of `(∂_s - νΔ + P_0 B_v) δ = 0` whose right
`L²(cell)` ergodic average `h⁻¹ ∫_σ^{σ+h} ‖δ(t)‖_{L²(cell)}² dt` vanishes as `h → 0⁺` vanishes
`volume`-a.e. on `(σ, σ + 1) × ℝ²` (Steklov/Lions–Magenes `L²` energy Grönwall with the smooth BUC
train `p.train`). -/
def CylUnitWeakHomogeneousUnique : Prop :=
  ∀ (dm dp : ℝ) (p : Params) (d : ℝ), BgRegime p d dm dp → p.ν ≤ 1 →
    ∀ σ : ℝ, 0 ≤ σ →
      ∀ (δ δq δη : CProf) (B : ℝ), 0 ≤ B →
        StronglyMeasurable δ → StronglyMeasurable δq → StronglyMeasurable δη →
        QPeriodic p.c δ → QPeriodic p.c δq → QPeriodic p.c δη →
        (∀ᵐ t ∂volume, t ∈ Ioo σ (σ + 1) → sliceH1Norm p.c δ δq δη t ≤ ENNReal.ofReal B) →
        (∀ᵐ t ∂volume, t ∈ Ioo σ (σ + 1) →
          F8U.IsCylH1Datum p.c (F8U.slice δ t) (F8U.slice δq t) (F8U.slice δη t)) →
        F8Duh.HasWeakVecOnIoo σ (σ + 1) vQ0 dZero δ δq →
        F8Duh.HasWeakVecOnIoo σ (σ + 1) vEta dZero δ δη →
        (∀ φ, F8Duh.IsIooTest σ (σ + 1) φ →
          Integrable (fun x => δ x 0 * (cpd 1 φ x : ℂ) + δ x 1 * (cpd 2 φ x : ℂ)) ∧
            ∫ x, (δ x 0 * (cpd 1 φ x : ℂ) + δ x 1 * (cpd 2 φ x : ℂ)) = 0) →
        (∀ Ψ, IsPlanarSolTest Ψ →
          (∀ i, tsupport (fun x => Ψ x i) ⊆ Ioo σ (σ + 1) ×ˢ univ) →
          Integrable (fun x => ∑ i : Fin 2, δ x i * meridTranspose p.ν Ψ x i) ∧
            Integrable (cdot (flatBv p.train δ δq δη) Ψ) ∧
            ∫ x, (∑ i : Fin 2, δ x i * meridTranspose p.ν Ψ x i +
                cdot (flatBv p.train δ δq δη) Ψ x) = 0) →
        Tendsto (fun h : ℝ => h⁻¹ *
          ∫ t in Ioc σ (σ + h), (F8U.cellL2 p.c (F8U.slice δ t)).toReal ^ 2)
          (𝓝[>] 0) (𝓝 0) →
        δ =ᵐ[volume.restrict (Ioo σ (σ + 1) ×ˢ univ)] 0

/-! ## 5. Conditional assembly of `MeridionalDuhamelRegularity` -/

/-- **Conditional assembly of `MeridionalDuhamelRegularity` (`PartII-b:F8/1/org/3`, SP 2301–2305)**
from `CylUnitDuhamelStep` and `CylUnitWeakHomogeneousUnique` with `C₁ = A`. -/
theorem meridionalDuhamelRegularity_of_leaves
    (hStep : CylUnitDuhamelStep)
    (hUniq : CylUnitWeakHomogeneousUnique) :
    MeridionalDuhamelRegularity := by
  intro A hA
  refine ⟨A, hA, ?_⟩
  intro dm dp p d hreg hν1 hFlow g gq gη z zq zη α M T₀ T₁
    hg_per hgq hgη hg_sol hz hz_M hG_meas hT₁ hT₁₀ hsLp htail
  have hν0 : 0 < p.ν := p.ν_pos
  have hc : 0 < p.c := by rw [hreg.c_eq]; positivity
  by_cases hM : 0 ≤ M
  · -- Nonnegative `0 ≤ M`: full overlapping unit-window Duhamel assembly
    obtain ⟨z₁, zq₁, zη₁, hz₁_sm, hzq₁_sm, hzη₁_sm, hz₁_per, hzq₁_per, hzη₁_per,
      hzq₁_wk, hzη₁_wk, hz₁_sol, hz₁_ae, hzq₁_ae, hzη₁_ae, hsl_z₁, hz₁_dat⟩ :=
      F8Duh.upgrade_weakH1_solenoidal hc hz.periodic hz.weak_q hz.weak_eta hz.solenoidal
    obtain ⟨g₁, gq₁, gη₁, hg₁_sm, hgq₁_sm, hgη₁_sm, hg₁_per, hgq₁_per, hgη₁_per,
      _, _, _, hg₁_ae, hgq₁_ae, hgη₁_ae, hsl_g₁, hg₁_dat⟩ :=
      F8Duh.upgrade_weakH1_solenoidal hc hg_per hgq hgη hg_sol
    have heq₁ := F8Duh.transfer_equation_both p hg₁_ae.symm hz₁_ae.symm hzq₁_ae.symm hzη₁_ae.symm
      hz.equation
    let G : ℝ → ℝ≥0∞ := sliceH1Norm p.c g gq gη
    let G₁ : ℝ → ℝ≥0∞ := sliceH1Norm p.c g₁ gq₁ gη₁
    have hG_L1 : ∀ B : ℝ, 0 < B → ∫⁻ s in Ioc 0 B, G s < ⊤ :=
      F8Duh.G_lintegral_Ioc_lt_top hT₁ hT₁₀ hG_meas hsLp htail
    have hG_ae_fin : ∀ᵐ s ∂volume, 0 < s → G s < ⊤ :=
      F8Duh.G_ae_lt_top hT₁ hT₁₀ hG_meas hsLp htail
    have hG₁_L1_unit : ∀ σ : ℝ, 0 ≤ σ → ∫⁻ τ in Ioc σ (σ + 1), G₁ τ < ⊤ := by
      intro σ hσ
      have heq_int : ∫⁻ τ in Ioc σ (σ + 1), G₁ τ = ∫⁻ τ in Ioc σ (σ + 1), G τ := by
        refine setLIntegral_congr_fun_ae measurableSet_Ioc ?_
        filter_upwards [hsl_g₁] with τ hτ hτ_mem
        exact hτ (lt_of_le_of_lt hσ hτ_mem.1)
      rw [heq_int]
      exact lt_of_le_of_lt
        (lintegral_mono_set (Ioc_subset_Ioc_left hσ))
        (hG_L1 (σ + 1) (by linarith))
    have hg₁_dat_pos : ∀ᵐ τ ∂volume, 0 < τ →
        F8U.IsCylH1Datum p.c (F8U.slice g₁ τ) (F8U.slice gq₁ τ) (F8U.slice gη₁ τ) := by
      filter_upwards [hg₁_dat, hsl_g₁, hG_ae_fin] with τ hdat h_eq h_fin hτ0
      apply hdat hτ0
      rw [h_eq hτ0]
      exact h_fin hτ0
    have hz₁_M_ae : ∀ᵐ s ∂volume, 0 < s → sliceH1Norm p.c z₁ zq₁ zη₁ s ≤ ENNReal.ofReal M := by
      filter_upwards [hsl_z₁] with s hs hs0
      rw [hs hs0]
      exact hz_M s hs0
    have hz₁_cell_M_ae : ∀ᵐ s ∂volume, 0 < s →
        F8U.cellL2 p.c (F8U.slice z₁ s) ≤ ENNReal.ofReal M := by
      filter_upwards [hz₁_M_ae] with s hs hs0
      exact (le_self_add.trans le_self_add).trans (hs hs0)
    have hz₁_dat_pos : ∀ᵐ s ∂volume, 0 < s →
        F8U.IsCylH1Datum p.c (F8U.slice z₁ s) (F8U.slice zq₁ s) (F8U.slice zη₁ s) := by
      filter_upwards [hz₁_dat, hz₁_M_ae] with s hdat hM_s hs0
      exact hdat hs0 (lt_of_le_of_lt (hM_s hs0) ENNReal.ofReal_lt_top)
    have hleb_ae := F8Duh.ae_rightLebesgue_sliceL2 hM hz₁_sm hz₁_cell_M_ae
    -- Good-age predicate on `(0, ∞)`
    let Good : ℝ → Prop := fun σ =>
      0 < σ ∧
      sliceH1Norm p.c z₁ zq₁ zη₁ σ ≤ ENNReal.ofReal M ∧
      F8U.IsCylH1Datum p.c (F8U.slice z₁ σ) (F8U.slice zq₁ σ) (F8U.slice zη₁ σ) ∧
      Tendsto (fun h : ℝ => h⁻¹ *
        ∫ t in Ioc σ (σ + h), (F8U.cellL2 p.c (fun y => z₁ (t, y) - z₁ (σ, y))).toReal ^ 2)
        (𝓝[>] 0) (𝓝 0)
    have hGood : ∀ᵐ σ ∂volume, 0 < σ → Good σ := by
      filter_upwards [hz₁_M_ae, hz₁_dat_pos, hleb_ae] with σ h1 h2 h3 hσ
      exact ⟨hσ, h1 hσ, h2 hσ, h3 hσ⟩
    -- Every good age `σ` admits a unit-window Duhamel witness agreeing a.e. with `(z₁, zq₁, zη₁)`
    have hWin_of_good : ∀ σ : ℝ, Good σ →
        ∃ (w wq wη : CProf) (D2w : Fin 2 → Fin 2 → CProf),
          StronglyMeasurable w ∧ StronglyMeasurable wq ∧ StronglyMeasurable wη ∧
          (∀ i j, StronglyMeasurable (D2w i j)) ∧
          QPeriodic p.c w ∧ QPeriodic p.c wq ∧ QPeriodic p.c wη ∧
          (∀ t ∈ Ioo σ (σ + 1),
            F8U.IsCylH1Datum p.c (F8U.slice w t) (F8U.slice wq t) (F8U.slice wη t)) ∧
          (∀ t ∈ Ioo σ (σ + 1),
            Tendsto (fun t' => F8U.cylH1 p.c (fun y => w (t', y) - w (t, y))
              (fun y => wq (t', y) - wq (t, y)) (fun y => wη (t', y) - wη (t, y)))
              (𝓝 t) (𝓝 0)) ∧
          F8Duh.HasWeakVecOnIoo σ (σ + 1) vQ0 dZero wq (D2w 0 0) ∧
          F8Duh.HasWeakVecOnIoo σ (σ + 1) vEta dZero wq (D2w 0 1) ∧
          F8Duh.HasWeakVecOnIoo σ (σ + 1) vQ0 dZero wη (D2w 1 0) ∧
          F8Duh.HasWeakVecOnIoo σ (σ + 1) vEta dZero wη (D2w 1 1) ∧
          w =ᵐ[volume.restrict (Ioo σ (σ + 1) ×ˢ univ)] z₁ ∧
          wq =ᵐ[volume.restrict (Ioo σ (σ + 1) ×ˢ univ)] zq₁ ∧
          wη =ᵐ[volume.restrict (Ioo σ (σ + 1) ×ˢ univ)] zη₁ ∧
          (∀ᵐ t ∂volume, t ∈ Ioo σ (σ + 1) →
            ∑ i : Fin 2, ∑ j : Fin 2, F8U.cellL2 p.c (F8U.slice (D2w i j) t) ≤
              ENNReal.ofReal (A * p.ν ^ (-1 / 2 : ℝ)) *
                (ENNReal.ofReal ((t - σ) ^ (-1 / 2 : ℝ) * M) +
                  ∫⁻ τ in Ioc σ t, ENNReal.ofReal ((t - τ) ^ (-1 / 2 : ℝ)) * G τ)) := by
      intro σ ⟨hσ_pos, hσ_M, hσ_dat, hσ_leb⟩
      have hg₁_Ioc : ∀ᵐ τ ∂volume, τ ∈ Ioc σ (σ + 1) →
          F8U.IsCylH1Datum p.c (F8U.slice g₁ τ) (F8U.slice gq₁ τ) (F8U.slice gη₁ τ) := by
        filter_upwards [hg₁_dat_pos] with τ hτ hτ_mem
        exact hτ (lt_trans hσ_pos hτ_mem.1)
      obtain ⟨w, wq, wη, D2w, hw_sm, hwq_sm, hwη_sm, hD2_sm,
        hw_per, hwq_per, hwη_per, _, hw_h1, hw_cont, hw_init,
        hwq_wk, hwη_wk, hD2_00, hD2_01, hD2_10, hD2_11, hw_sol, hw_eq, hw_D2_bnd⟩ :=
        hStep A hA dm dp p d hreg hν1 hFlow σ hσ_pos.le
          (F8U.slice z₁ σ) (F8U.slice zq₁ σ) (F8U.slice zη₁ σ) g₁ gq₁ gη₁
          hσ_dat hg₁_sm hgq₁_sm hgη₁_sm hg₁_per hgq₁_per hgη₁_per hg₁_Ioc
          (hG₁_L1_unit σ hσ_pos.le)
      -- Apply `CylUnitWeakHomogeneousUnique` to `δ = z₁ - w`
      let I_σ : ℝ := (∫⁻ τ in Ioc σ (σ + 1), G₁ τ).toReal
      let B : ℝ := M + A * (M + I_σ)
      have hB_nn : 0 ≤ B := by
        have : 0 ≤ I_σ := ENNReal.toReal_nonneg
        positivity
      have hδ_M : ∀ᵐ t ∂volume, t ∈ Ioo σ (σ + 1) →
          sliceH1Norm p.c (z₁ - w) (zq₁ - wq) (zη₁ - wη) t ≤ ENNReal.ofReal B := by
        filter_upwards [hz₁_M_ae] with t ht_z ht_mem
        have ht_pos : 0 < t := lt_trans hσ_pos ht_mem.1
        have h_tri := F8Duh.sliceH1Norm_sub_le p.c hz₁_sm hzq₁_sm hzη₁_sm hw_sm hwq_sm hwη_sm t
        have hw_le : sliceH1Norm p.c w wq wη t ≤ ENNReal.ofReal (A * (M + I_σ)) := by
          rw [F8Duh.sliceH1Norm_eq_cylH1]
          have hstep_le := (hw_h1 t ht_mem).2
          have hint_le : ∫⁻ τ in Ioc σ t, G₁ τ ≤ ENNReal.ofReal I_σ := by
            have hfin := (hG₁_L1_unit σ hσ_pos.le).ne
            rw [ENNReal.ofReal_toReal hfin]
            exact lintegral_mono_set (Ioc_subset_Ioc_right ht_mem.2.le)
          have hu₀_le : F8U.cylH1 p.c (F8U.slice z₁ σ) (F8U.slice zq₁ σ) (F8U.slice zη₁ σ) ≤
              ENNReal.ofReal M := hσ_M
          refine hstep_le.trans ?_
          calc ENNReal.ofReal A * (F8U.cylH1 p.c (F8U.slice z₁ σ) (F8U.slice zq₁ σ)
                (F8U.slice zη₁ σ) + ∫⁻ τ in Ioc σ t, G₁ τ)
              ≤ ENNReal.ofReal A * (ENNReal.ofReal M + ENNReal.ofReal I_σ) :=
                mul_le_mul_right (add_le_add hu₀_le hint_le) _
            _ = ENNReal.ofReal (A * (M + I_σ)) := by
                rw [← ENNReal.ofReal_add hM ENNReal.toReal_nonneg, ← ENNReal.ofReal_mul hA.le]
        refine h_tri.trans ?_
        calc sliceH1Norm p.c z₁ zq₁ zη₁ t + sliceH1Norm p.c w wq wη t
            ≤ ENNReal.ofReal M + ENNReal.ofReal (A * (M + I_σ)) :=
              add_le_add (ht_z ht_pos) hw_le
          _ = ENNReal.ofReal B :=
              (ENNReal.ofReal_add hM (mul_nonneg hA.le (add_nonneg hM ENNReal.toReal_nonneg))).symm
      have hδ_dat : ∀ᵐ t ∂volume, t ∈ Ioo σ (σ + 1) →
          F8U.IsCylH1Datum p.c (F8U.slice (z₁ - w) t) (F8U.slice (zq₁ - wq) t)
            (F8U.slice (zη₁ - wη) t) := by
        filter_upwards [hz₁_dat_pos] with t ht_z ht_mem
        exact F8Duh.isCylH1Datum_sub (ht_z (lt_trans hσ_pos ht_mem.1)) (hw_h1 t ht_mem).1
      have hδ_sol : ∀ φ, F8Duh.IsIooTest σ (σ + 1) φ →
          Integrable (fun x => (z₁ - w) x 0 * (cpd 1 φ x : ℂ) + (z₁ - w) x 1 * (cpd 2 φ x : ℂ)) ∧
            ∫ x, ((z₁ - w) x 0 * (cpd 1 φ x : ℂ) + (z₁ - w) x 1 * (cpd 2 φ x : ℂ)) = 0 := by
        intro φ hφ
        have heq_s : (fun x => (z₁ - w) x 0 * (cpd 1 φ x : ℂ) + (z₁ - w) x 1 * (cpd 2 φ x : ℂ)) =
            fun x => (z₁ x 0 * (cpd 1 φ x : ℂ) + z₁ x 1 * (cpd 2 φ x : ℂ)) -
              (w x 0 * (cpd 1 φ x : ℂ) + w x 1 * (cpd 2 φ x : ℂ)) := by
          funext x; simp only [Pi.sub_apply, PiLp.sub_apply]; ring
        rw [heq_s]
        exact ⟨(hz₁_sol φ hφ.1).1.sub (hw_sol φ hφ).1,
          by rw [integral_sub (hz₁_sol φ hφ.1).1 (hw_sol φ hφ).1,
            (hz₁_sol φ hφ.1).2, (hw_sol φ hφ).2, sub_self]⟩
      have hδ_eq : ∀ Ψ, IsPlanarSolTest Ψ →
          (∀ i, tsupport (fun x => Ψ x i) ⊆ Ioo σ (σ + 1) ×ˢ univ) →
          Integrable (fun x => ∑ i : Fin 2, (z₁ - w) x i * meridTranspose p.ν Ψ x i) ∧
            Integrable (cdot (flatBv p.train (z₁ - w) (zq₁ - wq) (zη₁ - wη)) Ψ) ∧
            ∫ x, (∑ i : Fin 2, (z₁ - w) x i * meridTranspose p.ν Ψ x i +
                cdot (flatBv p.train (z₁ - w) (zq₁ - wq) (zη₁ - wη)) Ψ x) = 0 := by
        intro Ψ hΨ hsupp
        obtain ⟨hzA, hzB, _, hzE⟩ := heq₁ Ψ hΨ
        obtain ⟨hwA, hwB, _, hwE⟩ := hw_eq Ψ hΨ hsupp
        have eA : (fun x => ∑ i : Fin 2, (z₁ - w) x i * meridTranspose p.ν Ψ x i) =
            fun x => (∑ i : Fin 2, z₁ x i * meridTranspose p.ν Ψ x i) -
              (∑ i : Fin 2, w x i * meridTranspose p.ν Ψ x i) := by
          funext x; simp only [Pi.sub_apply, PiLp.sub_apply, Fin.sum_univ_two]; ring
        have eB : cdot (flatBv p.train (z₁ - w) (zq₁ - wq) (zη₁ - wη)) Ψ =
            fun x => cdot (flatBv p.train z₁ zq₁ zη₁) Ψ x -
              cdot (flatBv p.train w wq wη) Ψ x := by
          funext x
          simp only [cdot]
          rw [F8Duh.flatBv_sub]
          simp only [PiLp.sub_apply, Fin.sum_univ_two]; ring
        have hIA : Integrable (fun x => ∑ i : Fin 2, (z₁ - w) x i * meridTranspose p.ν Ψ x i) := by
          rw [eA]; exact hzA.sub hwA
        have hIB : Integrable (cdot (flatBv p.train (z₁ - w) (zq₁ - wq) (zη₁ - wη)) Ψ) := by
          rw [eB]; exact hzB.sub hwB
        refine ⟨hIA, hIB, ?_⟩
        have eTot : (fun x => ∑ i : Fin 2, (z₁ - w) x i * meridTranspose p.ν Ψ x i +
              cdot (flatBv p.train (z₁ - w) (zq₁ - wq) (zη₁ - wη)) Ψ x) =
            fun x => (∑ i : Fin 2, z₁ x i * meridTranspose p.ν Ψ x i +
                cdot (flatBv p.train z₁ zq₁ zη₁) Ψ x) -
              (∑ i : Fin 2, w x i * meridTranspose p.ν Ψ x i +
                cdot (flatBv p.train w wq wη) Ψ x) := by
          funext x; rw [congr_fun eA x, congr_fun eB x]; ring
        have hzAB : Integrable (fun x => ∑ i : Fin 2, z₁ x i * meridTranspose p.ν Ψ x i +
            cdot (flatBv p.train z₁ zq₁ zη₁) Ψ x) := hzA.add hzB
        have hwAB : Integrable (fun x => ∑ i : Fin 2, w x i * meridTranspose p.ν Ψ x i +
            cdot (flatBv p.train w wq wη) Ψ x) := hwA.add hwB
        rw [eTot, integral_sub hzAB hwAB, hzE, hwE, sub_self]
      have hδ_leb : Tendsto (fun h : ℝ => h⁻¹ *
          ∫ t in Ioc σ (σ + h), (F8U.cellL2 p.c (F8U.slice (z₁ - w) t)).toReal ^ 2)
          (𝓝[>] 0) (𝓝 0) :=
        F8Duh.rightLebesgue_sub_of_initial hM hσ_pos hz₁_sm hw_sm hz₁_cell_M_ae hσ_dat.memL2.1
          (fun t ht => (hw_h1 t ht).1.memL2.1) hσ_leb hw_init
      have hδ_wq : F8Duh.HasWeakVecOnIoo σ (σ + 1) vQ0 dZero (z₁ - w) (zq₁ - wq) :=
        F8Duh.hasWeakVecOnIoo_sub vQ0 dZero (F8Duh.hasWeakVecOnIoo_of_global σ (σ + 1) hzq₁_wk)
          hwq_wk
      have hδ_wη : F8Duh.HasWeakVecOnIoo σ (σ + 1) vEta dZero (z₁ - w) (zη₁ - wη) :=
        F8Duh.hasWeakVecOnIoo_sub vEta dZero (F8Duh.hasWeakVecOnIoo_of_global σ (σ + 1) hzη₁_wk)
          hwη_wk
      have hδ_zero := hUniq dm dp p d hreg hν1 σ hσ_pos.le (z₁ - w) (zq₁ - wq) (zη₁ - wη)
        B hB_nn (hz₁_sm.sub hw_sm) (hzq₁_sm.sub hwq_sm) (hzη₁_sm.sub hwη_sm)
        (F8Duh.qPeriodic_sub hz₁_per hw_per) (F8Duh.qPeriodic_sub hzq₁_per hwq_per)
        (F8Duh.qPeriodic_sub hzη₁_per hwη_per)
        hδ_M hδ_dat hδ_wq hδ_wη hδ_sol hδ_eq hδ_leb
      have hδq_zero := F8Duh.weak_zero_on_Ioo hσ_pos.le vQ0 dZero hδ_zero hδ_wq
      have hδη_zero := F8Duh.weak_zero_on_Ioo hσ_pos.le vEta dZero hδ_zero hδ_wη
      have hw_eq_z₁ : w =ᵐ[volume.restrict (Ioo σ (σ + 1) ×ˢ univ)] z₁ :=
        hδ_zero.mono fun x hx => (sub_eq_zero.1 hx).symm
      have hwq_eq_zq₁ : wq =ᵐ[volume.restrict (Ioo σ (σ + 1) ×ˢ univ)] zq₁ :=
        hδq_zero.mono fun x hx => (sub_eq_zero.1 hx).symm
      have hwη_eq_zη₁ : wη =ᵐ[volume.restrict (Ioo σ (σ + 1) ×ˢ univ)] zη₁ :=
        hδη_zero.mono fun x hx => (sub_eq_zero.1 hx).symm
      have hD2_bnd' : ∀ᵐ t ∂volume, t ∈ Ioo σ (σ + 1) →
          ∑ i : Fin 2, ∑ j : Fin 2, F8U.cellL2 p.c (F8U.slice (D2w i j) t) ≤
            ENNReal.ofReal (A * p.ν ^ (-1 / 2 : ℝ)) *
              (ENNReal.ofReal ((t - σ) ^ (-1 / 2 : ℝ) * M) +
                ∫⁻ τ in Ioc σ t, ENNReal.ofReal ((t - τ) ^ (-1 / 2 : ℝ)) * G τ) := by
        filter_upwards [hw_D2_bnd] with t ht ht_mem
        refine (ht ht_mem).trans ?_
        refine mul_le_mul_right (add_le_add ?_ ?_) _
        · rw [ENNReal.ofReal_mul (Real.rpow_nonneg (sub_pos.2 ht_mem.1).le _)]
          exact mul_le_mul_right hσ_M _
        · refine le_of_eq (setLIntegral_congr_fun_ae measurableSet_Ioc ?_)
          filter_upwards [hsl_g₁] with τ hτ hτ_mem
          rw [hτ (lt_trans hσ_pos hτ_mem.1)]
      exact ⟨w, wq, wη, D2w, hw_sm, hwq_sm, hwη_sm, hD2_sm, hw_per, hwq_per, hwη_per,
        fun t ht => (hw_h1 t ht).1, hw_cont, hD2_00, hD2_01, hD2_10, hD2_11,
        hw_eq_z₁, hwq_eq_zq₁, hwη_eq_zη₁, hD2_bnd'⟩
    -- Choose witnesses along `winSeq hGood` and glue `Lp`-paths on `(0, ∞)`
    let σSeq : ℕ → ℝ := F8Duh.winSeq hGood
    have hσSeq_pg : ∀ m : ℕ, 0 < σSeq m ∧ Good (σSeq m) := F8Duh.winSeq_pos_and_good hGood
    have hσSeq_cov : ∀ s : ℝ, 0 < s → ∃ m : ℕ, s ∈ Ioo (σSeq m) (σSeq m + 1) :=
      fun s hs => F8Duh.exists_mem_winSeq hGood hs
    let wOf : ℕ → CProf := fun m => Classical.choose (hWin_of_good (σSeq m) (hσSeq_pg m).2)
    let wqOf : ℕ → CProf := fun m =>
      Classical.choose (Classical.choose_spec (hWin_of_good (σSeq m) (hσSeq_pg m).2))
    let wηOf : ℕ → CProf := fun m =>
      Classical.choose (Classical.choose_spec
        (Classical.choose_spec (hWin_of_good (σSeq m) (hσSeq_pg m).2)))
    let D2Of : ℕ → Fin 2 → Fin 2 → CProf := fun m =>
      Classical.choose (Classical.choose_spec (Classical.choose_spec
        (Classical.choose_spec (hWin_of_good (σSeq m) (hσSeq_pg m).2))))
    have hwSpec : ∀ m : ℕ,
        StronglyMeasurable (wOf m) ∧ StronglyMeasurable (wqOf m) ∧ StronglyMeasurable (wηOf m) ∧
        (∀ i j, StronglyMeasurable (D2Of m i j)) ∧
        QPeriodic p.c (wOf m) ∧ QPeriodic p.c (wqOf m) ∧ QPeriodic p.c (wηOf m) ∧
        (∀ t ∈ Ioo (σSeq m) (σSeq m + 1),
          F8U.IsCylH1Datum p.c (F8U.slice (wOf m) t) (F8U.slice (wqOf m) t)
            (F8U.slice (wηOf m) t)) ∧
        (∀ t ∈ Ioo (σSeq m) (σSeq m + 1),
          Tendsto (fun t' => F8U.cylH1 p.c (fun y => wOf m (t', y) - wOf m (t, y))
            (fun y => wqOf m (t', y) - wqOf m (t, y))
            (fun y => wηOf m (t', y) - wηOf m (t, y))) (𝓝 t) (𝓝 0)) ∧
        F8Duh.HasWeakVecOnIoo (σSeq m) (σSeq m + 1) vQ0 dZero (wqOf m) (D2Of m 0 0) ∧
        F8Duh.HasWeakVecOnIoo (σSeq m) (σSeq m + 1) vEta dZero (wqOf m) (D2Of m 0 1) ∧
        F8Duh.HasWeakVecOnIoo (σSeq m) (σSeq m + 1) vQ0 dZero (wηOf m) (D2Of m 1 0) ∧
        F8Duh.HasWeakVecOnIoo (σSeq m) (σSeq m + 1) vEta dZero (wηOf m) (D2Of m 1 1) ∧
        wOf m =ᵐ[volume.restrict (Ioo (σSeq m) (σSeq m + 1) ×ˢ univ)] z₁ ∧
        wqOf m =ᵐ[volume.restrict (Ioo (σSeq m) (σSeq m + 1) ×ˢ univ)] zq₁ ∧
        wηOf m =ᵐ[volume.restrict (Ioo (σSeq m) (σSeq m + 1) ×ˢ univ)] zη₁ ∧
        (∀ᵐ t ∂volume, t ∈ Ioo (σSeq m) (σSeq m + 1) →
          ∑ i : Fin 2, ∑ j : Fin 2, F8U.cellL2 p.c (F8U.slice (D2Of m i j) t) ≤
            ENNReal.ofReal (A * p.ν ^ (-1 / 2 : ℝ)) *
              (ENNReal.ofReal ((t - σSeq m) ^ (-1 / 2 : ℝ) * M) +
                ∫⁻ τ in Ioc (σSeq m) t, ENNReal.ofReal ((t - τ) ^ (-1 / 2 : ℝ)) * G τ)) :=
      fun m => Classical.choose_spec (Classical.choose_spec (Classical.choose_spec
        (Classical.choose_spec (hWin_of_good (σSeq m) (hσSeq_pg m).2))))
    let μc : Measure B0579.Plane := volume.restrict (B0579.cell p.c)
    let Pw : ℕ → ℝ → Lp CMerid 2 μc := fun m => UnforcedLeray.BochnerTime.toPathLq 2 μc (wOf m)
    let Pwq : ℕ → ℝ → Lp CMerid 2 μc := fun m => UnforcedLeray.BochnerTime.toPathLq 2 μc (wqOf m)
    let Pwη : ℕ → ℝ → Lp CMerid 2 μc := fun m => UnforcedLeray.BochnerTime.toPathLq 2 μc (wηOf m)
    have hPw_cont : ∀ m : ℕ, ContinuousOn (Pw m) (Ioo (σSeq m) (σSeq m + 1)) ∧
        ContinuousOn (Pwq m) (Ioo (σSeq m) (σSeq m + 1)) ∧
        ContinuousOn (Pwη m) (Ioo (σSeq m) (σSeq m + 1)) := by
      intro m
      have hdat_m := (hwSpec m).2.2.2.2.2.2.2.1
      have hcont_m := (hwSpec m).2.2.2.2.2.2.2.2.1
      refine ⟨F8Duh.continuousOn_toPathLq_of_cellL2 (fun t ht => (hdat_m t ht).memL2.1)
          (fun t ht => (F8L.dd_tendsto_of_cylH1 (hcont_m t ht)).1),
        F8Duh.continuousOn_toPathLq_of_cellL2 (fun t ht => (hdat_m t ht).memL2.2.1)
          (fun t ht => (F8L.dd_tendsto_of_cylH1 (hcont_m t ht)).2.1),
        F8Duh.continuousOn_toPathLq_of_cellL2 (fun t ht => (hdat_m t ht).memL2.2.2)
          (fun t ht => (F8L.dd_tendsto_of_cylH1 (hcont_m t ht)).2.2)⟩
    -- Helper: two continuous `toPathLq` paths agreeing `volume`-a.e. with a common profile agree pointwise on overlaps
    have hoverlap_eq : ∀ {a₁ b₁ a₂ b₂ : ℝ} {f₁ f₂ f₀ : CProf}
        (hc₁ : ContinuousOn (UnforcedLeray.BochnerTime.toPathLq 2 μc f₁) (Ioo a₁ b₁))
        (hc₂ : ContinuousOn (UnforcedLeray.BochnerTime.toPathLq 2 μc f₂) (Ioo a₂ b₂))
        (he₁ : f₁ =ᵐ[volume.restrict (Ioo a₁ b₁ ×ˢ univ)] f₀)
        (he₂ : f₂ =ᵐ[volume.restrict (Ioo a₂ b₂ ×ˢ univ)] f₀),
        ∀ t ∈ Ioo (max a₁ a₂) (min b₁ b₂),
          UnforcedLeray.BochnerTime.toPathLq 2 μc f₁ t =
            UnforcedLeray.BochnerTime.toPathLq 2 μc f₂ t := by
      intro a₁ b₁ a₂ b₂ f₁ f₂ f₀ hc₁ hc₂ he₁ he₂
      set α := max a₁ a₂
      set β := min b₁ b₂
      have hsub₁ : Ioo α β ⊆ Ioo a₁ b₁ :=
        Ioo_subset_Ioo (le_max_left _ _) (min_le_left _ _)
      have hsub₂ : Ioo α β ⊆ Ioo a₂ b₂ :=
        Ioo_subset_Ioo (le_max_right _ _) (min_le_right _ _)
      have he_ov : ∀ᵐ x : Coord, x.1 ∈ Ioo α β → f₁ x = f₂ x := by
        have h₁' := he₁; have h₂' := he₂
        rw [Filter.EventuallyEq, ae_restrict_iff' (measurableSet_Ioo.prod MeasurableSet.univ)] at h₁' h₂'
        filter_upwards [h₁', h₂'] with x hx₁ hx₂ hx_mem
        exact (hx₁ ⟨hsub₁ hx_mem, trivial⟩).trans (hx₂ ⟨hsub₂ hx_mem, trivial⟩).symm
      have hsl_ov : ∀ᵐ t ∂(volume : Measure ℝ), t ∈ Ioo α β →
          UnforcedLeray.BochnerTime.toPathLq 2 μc f₁ t =
            UnforcedLeray.BochnerTime.toPathLq 2 μc f₂ t := by
        filter_upwards [Measure.ae_ae_of_ae_prod he_ov] with t ht ht_mem
        exact UnforcedLeray.BochnerTime.toPathLq_congr_ae
          (ae_restrict_of_ae (ht.mono fun y hy => hy ht_mem))
      exact F8Duh.eqOn_Ioo_of_continuousOn_ae (hc₁.mono hsub₁) (hc₂.mono hsub₂) hsl_ov
    let Z_path : ℝ → Lp CMerid 2 μc :=
      fun s => if hs : 0 < s then Pw (Nat.find (hσSeq_cov s hs)) s else 0
    let Zq_path : ℝ → Lp CMerid 2 μc :=
      fun s => if hs : 0 < s then Pwq (Nat.find (hσSeq_cov s hs)) s else 0
    let Zη_path : ℝ → Lp CMerid 2 μc :=
      fun s => if hs : 0 < s then Pwη (Nat.find (hσSeq_cov s hs)) s else 0
    have hZ_eq_on : ∀ m : ℕ, ∀ t ∈ Ioo (σSeq m) (σSeq m + 1),
        Z_path t = Pw m t ∧ Zq_path t = Pwq m t ∧ Zη_path t = Pwη m t := by
      intro m t ht
      have ht0 : 0 < t := lt_trans (hσSeq_pg m).1 ht.1
      set k := Nat.find (hσSeq_cov t ht0)
      have hk_in : t ∈ Ioo (σSeq k) (σSeq k + 1) := Nat.find_spec (hσSeq_cov t ht0)
      have ht_ov : t ∈ Ioo (max (σSeq k) (σSeq m)) (min (σSeq k + 1) (σSeq m + 1)) :=
        ⟨max_lt hk_in.1 ht.1, lt_min hk_in.2 ht.2⟩
      simp only [Z_path, Zq_path, Zη_path, ht0, ↓reduceDIte]
      exact ⟨hoverlap_eq (hPw_cont k).1 (hPw_cont m).1
          (hwSpec k).2.2.2.2.2.2.2.2.2.2.2.2.2.1 (hwSpec m).2.2.2.2.2.2.2.2.2.2.2.2.2.1 t ht_ov,
        hoverlap_eq (hPw_cont k).2.1 (hPw_cont m).2.1
          (hwSpec k).2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 (hwSpec m).2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 t ht_ov,
        hoverlap_eq (hPw_cont k).2.2 (hPw_cont m).2.2
          (hwSpec k).2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 (hwSpec m).2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 t ht_ov⟩
    have hZ_cont : ContinuousOn Z_path (Ioi 0) ∧ ContinuousOn Zq_path (Ioi 0) ∧
        ContinuousOn Zη_path (Ioi 0) := by
      refine ⟨fun s hs => ?_, fun s hs => ?_, fun s hs => ?_⟩
      · obtain ⟨m, hm⟩ := hσSeq_cov s hs
        exact (((hPw_cont m).1.continuousAt (isOpen_Ioo.mem_nhds hm)).congr_of_eventuallyEq
          (Filter.eventually_of_mem (isOpen_Ioo.mem_nhds hm)
            (fun t ht => (hZ_eq_on m t ht).1))).continuousWithinAt
      · obtain ⟨m, hm⟩ := hσSeq_cov s hs
        exact (((hPw_cont m).2.1.continuousAt (isOpen_Ioo.mem_nhds hm)).congr_of_eventuallyEq
          (Filter.eventually_of_mem (isOpen_Ioo.mem_nhds hm)
            (fun t ht => (hZ_eq_on m t ht).2.1))).continuousWithinAt
      · obtain ⟨m, hm⟩ := hσSeq_cov s hs
        exact (((hPw_cont m).2.2.continuousAt (isOpen_Ioo.mem_nhds hm)).congr_of_eventuallyEq
          (Filter.eventually_of_mem (isOpen_Ioo.mem_nhds hm)
            (fun t ht => (hZ_eq_on m t ht).2.2))).continuousWithinAt
    -- Joint representatives + periodic extension via `wrapPlane`
    obtain ⟨U, hU_sm, hUZ⟩ :=
      UnforcedLeray.BochnerTime.exists_isJointRep_of_continuousOn measurableSet_Ioi hZ_cont.1
    obtain ⟨Uq, hUq_sm, hUqZ⟩ :=
      UnforcedLeray.BochnerTime.exists_isJointRep_of_continuousOn measurableSet_Ioi hZ_cont.2.1
    obtain ⟨Uη, hUη_sm, hUηZ⟩ :=
      UnforcedLeray.BochnerTime.exists_isJointRep_of_continuousOn measurableSet_Ioi hZ_cont.2.2
    let z' : CProf := F8Duh.perJointProf p.c U
    let zq' : CProf := F8Duh.perJointProf p.c Uq
    let zη' : CProf := F8Duh.perJointProf p.c Uη
    have hz'_sm : StronglyMeasurable z' := F8Duh.stronglyMeasurable_perJointProf hU_sm
    have hzq'_sm : StronglyMeasurable zq' := F8Duh.stronglyMeasurable_perJointProf hUq_sm
    have hzη'_sm : StronglyMeasurable zη' := F8Duh.stronglyMeasurable_perJointProf hUη_sm
    have hz'_per : QPeriodic p.c z' := F8Duh.qPeriodic_perJointProf hc U
    have hzq'_per : QPeriodic p.c zq' := F8Duh.qPeriodic_perJointProf hc Uq
    have hzη'_per : QPeriodic p.c zη' := F8Duh.qPeriodic_perJointProf hc Uη
    -- `z', zq', zη'` agree `volume`-a.e. on `Ioo (σSeq m) (σSeq m + 1) ×ˢ univ` with `(z₁, zq₁, zη₁)`
    have hz'_win_ae : ∀ m : ℕ,
        z' =ᵐ[volume.restrict (Ioo (σSeq m) (σSeq m + 1) ×ˢ univ)] z₁ ∧
        zq' =ᵐ[volume.restrict (Ioo (σSeq m) (σSeq m + 1) ×ˢ univ)] zq₁ ∧
        zη' =ᵐ[volume.restrict (Ioo (σSeq m) (σSeq m + 1) ×ˢ univ)] zη₁ := by
      intro m
      have hdat_m := (hwSpec m).2.2.2.2.2.2.2.1
      have hcell_w : ∀ t ∈ Ioo (σSeq m) (σSeq m + 1),
          (fun y => z' (t, y)) =ᵐ[μc] (fun y => wOf m (t, y)) := by
        intro t ht
        have ht0 : 0 < t := lt_trans (hσSeq_pg m).1 ht.1
        have h1 := F8Duh.slice_perJointProf_ae_cell hc hUZ ht0
        have hmem_t : MemLp (fun y => wOf m (t, y)) 2 μc := (hdat_m t ht).memL2.1
        rw [(hZ_eq_on m t ht).1] at h1
        dsimp only [Pw, μc] at h1
        rw [UnforcedLeray.BochnerTime.toPathLq_of_memLp hmem_t] at h1
        exact h1.trans (MemLp.coeFn_toLp hmem_t)
      have hcell_wq : ∀ t ∈ Ioo (σSeq m) (σSeq m + 1),
          (fun y => zq' (t, y)) =ᵐ[μc] (fun y => wqOf m (t, y)) := by
        intro t ht
        have ht0 : 0 < t := lt_trans (hσSeq_pg m).1 ht.1
        have h1 := F8Duh.slice_perJointProf_ae_cell hc hUqZ ht0
        have hmem_t : MemLp (fun y => wqOf m (t, y)) 2 μc := (hdat_m t ht).memL2.2.1
        rw [(hZ_eq_on m t ht).2.1] at h1
        dsimp only [Pwq, μc] at h1
        rw [UnforcedLeray.BochnerTime.toPathLq_of_memLp hmem_t] at h1
        exact h1.trans (MemLp.coeFn_toLp hmem_t)
      have hcell_wη : ∀ t ∈ Ioo (σSeq m) (σSeq m + 1),
          (fun y => zη' (t, y)) =ᵐ[μc] (fun y => wηOf m (t, y)) := by
        intro t ht
        have ht0 : 0 < t := lt_trans (hσSeq_pg m).1 ht.1
        have h1 := F8Duh.slice_perJointProf_ae_cell hc hUηZ ht0
        have hmem_t : MemLp (fun y => wηOf m (t, y)) 2 μc := (hdat_m t ht).memL2.2.2
        rw [(hZ_eq_on m t ht).2.2] at h1
        dsimp only [Pwη, μc] at h1
        rw [UnforcedLeray.BochnerTime.toPathLq_of_memLp hmem_t] at h1
        exact h1.trans (MemLp.coeFn_toLp hmem_t)
      exact ⟨(F8Duh.ae_vol_eq_on_Ioo_of_ae_cell_periodic hc (hσSeq_pg m).1.le hz'_sm
          (hwSpec m).1 hz'_per (hwSpec m).2.2.2.2.1 (Eventually.of_forall hcell_w)).trans
          (hwSpec m).2.2.2.2.2.2.2.2.2.2.2.2.2.1,
        (F8Duh.ae_vol_eq_on_Ioo_of_ae_cell_periodic hc (hσSeq_pg m).1.le hzq'_sm
          (hwSpec m).2.1 hzq'_per (hwSpec m).2.2.2.2.2.1 (Eventually.of_forall hcell_wq)).trans
          (hwSpec m).2.2.2.2.2.2.2.2.2.2.2.2.2.2.1,
        (F8Duh.ae_vol_eq_on_Ioo_of_ae_cell_periodic hc (hσSeq_pg m).1.le hzη'_sm
          (hwSpec m).2.2.1 hzη'_per (hwSpec m).2.2.2.2.2.2.1 (Eventually.of_forall hcell_wη)).trans
          (hwSpec m).2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1⟩
    have lift_ae_pos : ∀ {f f₁ : CProf},
        (∀ m : ℕ, f =ᵐ[volume.restrict (Ioo (σSeq m) (σSeq m + 1) ×ˢ univ)] f₁) →
        f =ᵐ[volume.restrict {x : Coord | 0 < x.1}] f₁ := by
      intro f f₁ hm
      have hm' : ∀ m : ℕ, ∀ᵐ x : Coord, x.1 ∈ Ioo (σSeq m) (σSeq m + 1) → f x = f₁ x := by
        intro m
        have h := hm m
        rw [Filter.EventuallyEq, ae_restrict_iff' (measurableSet_Ioo.prod MeasurableSet.univ)] at h
        filter_upwards [h] with x hx hx_mem
        exact hx ⟨hx_mem, trivial⟩
      rw [Filter.EventuallyEq, ae_restrict_iff' (measurableSet_lt measurable_const measurable_fst)]
      filter_upwards [ae_all_iff.2 hm'] with x hx hp
      obtain ⟨m, hm_in⟩ := hσSeq_cov x.1 hp
      exact hx m hm_in
    have hz'_ae_z₁ := lift_ae_pos (fun m => (hz'_win_ae m).1)
    have hzq'_ae_zq₁ := lift_ae_pos (fun m => (hz'_win_ae m).2.1)
    have hzη'_ae_zη₁ := lift_ae_pos (fun m => (hz'_win_ae m).2.2)
    -- Glue `D2 i j` via `glueWindowProf`
    let D2 : Fin 2 → Fin 2 → CProf := fun i j =>
      F8Duh.glueWindowProf σSeq hσSeq_cov (fun m => D2Of m i j)
    have hD2_sm : ∀ i j, StronglyMeasurable (D2 i j) := fun i j =>
      F8Duh.stronglyMeasurable_glueWindowProf (fun m => (hσSeq_pg m).1) hσSeq_cov
        (fun m => (hwSpec m).2.2.2.1 i j)
    -- On EVERY good age `τ`, `D2` satisfies `HasWeakVecOnIoo τ (τ + 1)` and the `D²` Duhamel bound!
    have hD2_on_good : ∀ τ : ℝ, Good τ →
        F8Duh.HasWeakVecOnIoo τ (τ + 1) vQ0 dZero zq' (D2 0 0) ∧
        F8Duh.HasWeakVecOnIoo τ (τ + 1) vEta dZero zq' (D2 0 1) ∧
        F8Duh.HasWeakVecOnIoo τ (τ + 1) vQ0 dZero zη' (D2 1 0) ∧
        F8Duh.HasWeakVecOnIoo τ (τ + 1) vEta dZero zη' (D2 1 1) ∧
        (∀ᵐ s ∂volume, s ∈ Ioo τ (τ + 1) →
          ∑ i : Fin 2, ∑ j : Fin 2, F8U.cellL2 p.c (F8U.slice (D2 i j) s) ≤
            ENNReal.ofReal (A * p.ν ^ (-1 / 2 : ℝ)) *
              (ENNReal.ofReal ((s - τ) ^ (-1 / 2 : ℝ) * M) +
                ∫⁻ t in Ioc τ s, ENNReal.ofReal ((s - t) ^ (-1 / 2 : ℝ)) * G t)) := by
      intro τ hτ_good
      have hτ0 : 0 ≤ τ := hτ_good.1.le
      obtain ⟨wτ, wqτ, wητ, D2τ, _, _, _, _, _, _, _, _, _,
        hd00, hd01, hd10, hd11, _, hwqτ_ae, hwητ_ae, hD2τ_bnd⟩ := hWin_of_good τ hτ_good
      have hD2_compat : ∀ (i j : Fin 2) (m : ℕ),
          D2Of m i j =ᵐ[volume.restrict (Ioo (max (σSeq m) τ) (min (σSeq m + 1) (τ + 1)) ×ˢ univ)]
            D2τ i j := by
        intro i j m
        set α := max (σSeq m) τ
        set β := min (σSeq m + 1) (τ + 1)
        by_cases hlt : α < β
        · have hα0 : 0 ≤ α := le_trans hτ0 (le_max_right _ _)
          have hsub_m : Ioo α β ×ˢ (univ : Set B0579.Plane) ⊆ Ioo (σSeq m) (σSeq m + 1) ×ˢ univ :=
            prod_mono (Ioo_subset_Ioo (le_max_left _ _) (min_le_left _ _)) Subset.rfl
          have hsub_τ : Ioo α β ×ˢ (univ : Set B0579.Plane) ⊆ Ioo τ (τ + 1) ×ˢ univ :=
            prod_mono (Ioo_subset_Ioo (le_max_right _ _) (min_le_right _ _)) Subset.rfl
          have hwq_m_ov : wqOf m =ᵐ[volume.restrict (Ioo α β ×ˢ univ)] zq₁ :=
            ae_restrict_of_ae_restrict_of_subset hsub_m
              (hwSpec m).2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
          have hwq_τ_ov : wqτ =ᵐ[volume.restrict (Ioo α β ×ˢ univ)] zq₁ :=
            ae_restrict_of_ae_restrict_of_subset hsub_τ hwqτ_ae
          have hwη_m_ov : wηOf m =ᵐ[volume.restrict (Ioo α β ×ˢ univ)] zη₁ :=
            ae_restrict_of_ae_restrict_of_subset hsub_m
              (hwSpec m).2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
          have hwη_τ_ov : wητ =ᵐ[volume.restrict (Ioo α β ×ˢ univ)] zη₁ :=
            ae_restrict_of_ae_restrict_of_subset hsub_τ hwητ_ae
          fin_cases i <;> fin_cases j
          · have h1 := F8Duh.hasWeakVecOnIoo_congr vQ0 dZero hwq_m_ov (EventuallyEq.refl _ _)
              (F8Duh.hasWeakVecOnIoo_mono (le_max_left _ _) (min_le_left _ _)
                (hwSpec m).2.2.2.2.2.2.2.2.2.1)
            have h2 := F8Duh.hasWeakVecOnIoo_congr vQ0 dZero hwq_τ_ov (EventuallyEq.refl _ _)
              (F8Duh.hasWeakVecOnIoo_mono (le_max_right _ _) (min_le_right _ _) hd00)
            have h0 := F8Duh.weak_unique_on_Ioo hα0 vQ0 dZero (h1 0) (h2 0)
            have h1' := F8Duh.weak_unique_on_Ioo hα0 vQ0 dZero (h1 1) (h2 1)
            filter_upwards [h0, h1'] with x hx0 hx1
            ext k; fin_cases k <;> assumption
          · have h1 := F8Duh.hasWeakVecOnIoo_congr vEta dZero hwq_m_ov (EventuallyEq.refl _ _)
              (F8Duh.hasWeakVecOnIoo_mono (le_max_left _ _) (min_le_left _ _)
                (hwSpec m).2.2.2.2.2.2.2.2.2.2.1)
            have h2 := F8Duh.hasWeakVecOnIoo_congr vEta dZero hwq_τ_ov (EventuallyEq.refl _ _)
              (F8Duh.hasWeakVecOnIoo_mono (le_max_right _ _) (min_le_right _ _) hd01)
            have h0 := F8Duh.weak_unique_on_Ioo hα0 vEta dZero (h1 0) (h2 0)
            have h1' := F8Duh.weak_unique_on_Ioo hα0 vEta dZero (h1 1) (h2 1)
            filter_upwards [h0, h1'] with x hx0 hx1
            ext k; fin_cases k <;> assumption
          · have h1 := F8Duh.hasWeakVecOnIoo_congr vQ0 dZero hwη_m_ov (EventuallyEq.refl _ _)
              (F8Duh.hasWeakVecOnIoo_mono (le_max_left _ _) (min_le_left _ _)
                (hwSpec m).2.2.2.2.2.2.2.2.2.2.2.1)
            have h2 := F8Duh.hasWeakVecOnIoo_congr vQ0 dZero hwη_τ_ov (EventuallyEq.refl _ _)
              (F8Duh.hasWeakVecOnIoo_mono (le_max_right _ _) (min_le_right _ _) hd10)
            have h0 := F8Duh.weak_unique_on_Ioo hα0 vQ0 dZero (h1 0) (h2 0)
            have h1' := F8Duh.weak_unique_on_Ioo hα0 vQ0 dZero (h1 1) (h2 1)
            filter_upwards [h0, h1'] with x hx0 hx1
            ext k; fin_cases k <;> assumption
          · have h1 := F8Duh.hasWeakVecOnIoo_congr vEta dZero hwη_m_ov (EventuallyEq.refl _ _)
              (F8Duh.hasWeakVecOnIoo_mono (le_max_left _ _) (min_le_left _ _)
                (hwSpec m).2.2.2.2.2.2.2.2.2.2.2.2.1)
            have h2 := F8Duh.hasWeakVecOnIoo_congr vEta dZero hwη_τ_ov (EventuallyEq.refl _ _)
              (F8Duh.hasWeakVecOnIoo_mono (le_max_right _ _) (min_le_right _ _) hd11)
            have h0 := F8Duh.weak_unique_on_Ioo hα0 vEta dZero (h1 0) (h2 0)
            have h1' := F8Duh.weak_unique_on_Ioo hα0 vEta dZero (h1 1) (h2 1)
            filter_upwards [h0, h1'] with x hx0 hx1
            ext k; fin_cases k <;> assumption
        · have hempty : Ioo α β = ∅ := Ioo_eq_empty hlt
          rw [hempty, empty_prod, Measure.restrict_empty]
          simp [Filter.EventuallyEq]
      have hD2_ae_τ : ∀ i j, D2 i j =ᵐ[volume.restrict (Ioo τ (τ + 1) ×ˢ univ)] D2τ i j :=
        fun i j => F8Duh.glueWindowProf_ae_eq_on_Ioo hσSeq_cov hτ0 (hD2_compat i j)
      have hsub_pos : Ioo τ (τ + 1) ×ˢ (univ : Set B0579.Plane) ⊆ {x : Coord | 0 < x.1} :=
        fun x hx => lt_of_le_of_lt hτ0 hx.1.1
      have hzq'_τ : wqτ =ᵐ[volume.restrict (Ioo τ (τ + 1) ×ˢ univ)] zq' :=
        hwqτ_ae.trans
          (Filter.EventuallyEq.symm (ae_restrict_of_ae_restrict_of_subset hsub_pos hzq'_ae_zq₁))
      have hzη'_τ : wητ =ᵐ[volume.restrict (Ioo τ (τ + 1) ×ˢ univ)] zη' :=
        hwητ_ae.trans
          (Filter.EventuallyEq.symm (ae_restrict_of_ae_restrict_of_subset hsub_pos hzη'_ae_zη₁))
      have hsl_D2 : ∀ i j : Fin 2, ∀ᵐ s ∂volume, s ∈ Ioo τ (τ + 1) →
          F8U.cellL2 p.c (F8U.slice (D2 i j) s) = F8U.cellL2 p.c (F8U.slice (D2τ i j) s) := by
        intro i j
        have h := hD2_ae_τ i j
        rw [Filter.EventuallyEq, ae_restrict_iff' (measurableSet_Ioo.prod MeasurableSet.univ)] at h
        filter_upwards [Measure.ae_ae_of_ae_prod h] with s hs hs_mem
        unfold F8U.cellL2 F8U.slice
        exact eLpNorm_congr_ae (ae_restrict_of_ae (hs.mono fun y hy => hy ⟨hs_mem, trivial⟩))
      have hsl_all : ∀ᵐ s ∂volume, s ∈ Ioo τ (τ + 1) →
          ∀ i j : Fin 2,
            F8U.cellL2 p.c (F8U.slice (D2 i j) s) = F8U.cellL2 p.c (F8U.slice (D2τ i j) s) := by
        filter_upwards [hsl_D2 0 0, hsl_D2 0 1, hsl_D2 1 0, hsl_D2 1 1] with s h00 h01 h10 h11 hs i j
        fin_cases i <;> fin_cases j
        · exact h00 hs
        · exact h01 hs
        · exact h10 hs
        · exact h11 hs
      refine ⟨F8Duh.hasWeakVecOnIoo_congr vQ0 dZero hzq'_τ (hD2_ae_τ 0 0).symm hd00,
        F8Duh.hasWeakVecOnIoo_congr vEta dZero hzq'_τ (hD2_ae_τ 0 1).symm hd01,
        F8Duh.hasWeakVecOnIoo_congr vQ0 dZero hzη'_τ (hD2_ae_τ 1 0).symm hd10,
        F8Duh.hasWeakVecOnIoo_congr vEta dZero hzη'_τ (hD2_ae_τ 1 1).symm hd11, ?_⟩
      filter_upwards [hsl_all, hD2τ_bnd] with s hs_eq hs_bnd hs_mem
      have hsum_eq : (∑ i : Fin 2, ∑ j : Fin 2, F8U.cellL2 p.c (F8U.slice (D2 i j) s)) =
          ∑ i : Fin 2, ∑ j : Fin 2, F8U.cellL2 p.c (F8U.slice (D2τ i j) s) :=
        Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => hs_eq hs_mem i j
      rw [hsum_eq]
      exact hs_bnd hs_mem
    -- Global `HasWeakVec` for `D2` by inductive window gluing over `aSeq` and `bSeq`
    have lift_global_D2 : ∀ {w_dir : Fin 3 → ℝ} (hw0 : w_dir 0 = 0) {u' d' : CProf}
        (h_good : ∀ τ : ℝ, Good τ → F8Duh.HasWeakVecOnIoo τ (τ + 1) (fun _ => w_dir) dZero u' d'),
        HasWeakVec (fun _ => w_dir) dZero u' d' := by
      intro w_dir hw0 u' d' h_good
      have hchain : ∀ (n K : ℕ),
          F8Duh.HasWeakVecOnIoo (F8Duh.aSeq hGood n) (F8Duh.bSeq hGood K + 1)
            (fun _ => w_dir) dZero u' d' := by
        intro n K
        induction K with
        | zero =>
          have ha_sp := F8Duh.aSeq_spec hGood n
          have hb_sp := F8Duh.bSeq_spec hGood 0
          have hov : F8Duh.bSeq hGood 0 < F8Duh.aSeq hGood n + 1 := by
            linarith [ha_sp.1.1, hb_sp.1.2]
          exact F8Duh.hasWeakVecOnIoo_glue hov hw0
            (h_good _ ha_sp.2) (h_good _ hb_sp.2)
        | succ K ih =>
          have hbK := F8Duh.bSeq_spec hGood K
          have hbK1 := F8Duh.bSeq_spec hGood (K + 1)
          have hov : F8Duh.bSeq hGood (K + 1) < F8Duh.bSeq hGood K + 1 := by
            have h1 := hbK.1.1
            have h2 := hbK1.1.2
            push_cast at h1 h2
            linarith
          exact F8Duh.hasWeakVecOnIoo_glue hov hw0 ih (h_good _ hbK1.2)
      refine F8Duh.hasWeakVec_of_exhaust_Ioo fun s₁ s₂ hs₁ hs₁₂ => ?_
      have hev_a : ∀ᶠ n in atTop, F8Duh.aSeq hGood n < s₁ :=
        (F8Duh.tendsto_aSeq hGood).eventually (gt_mem_nhds hs₁)
      obtain ⟨n, hn⟩ := hev_a.exists
      obtain ⟨K, hK⟩ := exists_nat_gt (2 * s₂)
      have hb_gt : s₂ < F8Duh.bSeq hGood K + 1 := by
        have hbK := (F8Duh.bSeq_spec hGood K).1.1
        linarith
      exact ⟨F8Duh.aSeq hGood n, F8Duh.bSeq hGood K + 1, hn, hb_gt, hchain n K⟩
    have hD2_wk00 : HasWeakVec vQ0 dZero zq' (D2 0 0) :=
      lift_global_D2 (w_dir := ![0, 1, 0]) rfl (fun τ hτ => (hD2_on_good τ hτ).1)
    have hD2_wk01 : HasWeakVec vEta dZero zq' (D2 0 1) :=
      lift_global_D2 (w_dir := ![0, 0, 1]) rfl (fun τ hτ => (hD2_on_good τ hτ).2.1)
    have hD2_wk10 : HasWeakVec vQ0 dZero zη' (D2 1 0) :=
      lift_global_D2 (w_dir := ![0, 1, 0]) rfl (fun τ hτ => (hD2_on_good τ hτ).2.2.1)
    have hD2_wk11 : HasWeakVec vEta dZero zη' (D2 1 1) :=
      lift_global_D2 (w_dir := ![0, 0, 1]) rfl (fun τ hτ => (hD2_on_good τ hτ).2.2.2.1)
    -- Early `D²` bound (`s ∈ Ioc 0 1`) via `aSeq hGood n → 0⁺`
    have hEarly : ∀ᵐ s ∂volume, s ∈ Ioc (0 : ℝ) 1 →
        ∑ i : Fin 2, ∑ j : Fin 2, F8U.cellL2 p.c (F8U.slice (D2 i j) s) ≤
          ENNReal.ofReal (A * p.ν ^ (-1 / 2 : ℝ)) *
            (ENNReal.ofReal (s ^ (-1 / 2 : ℝ) * M) +
              ∫⁻ t in Ioc 0 s, ENNReal.ofReal ((s - t) ^ (-1 / 2 : ℝ)) * G t) := by
      have ha_bnd : ∀ n : ℕ, ∀ᵐ s ∂volume,
          s ∈ Ioo (F8Duh.aSeq hGood n) (F8Duh.aSeq hGood n + 1) →
            ∑ i : Fin 2, ∑ j : Fin 2, F8U.cellL2 p.c (F8U.slice (D2 i j) s) ≤
              ENNReal.ofReal (A * p.ν ^ (-1 / 2 : ℝ)) *
                (ENNReal.ofReal ((s - F8Duh.aSeq hGood n) ^ (-1 / 2 : ℝ) * M) +
                  ∫⁻ t in Ioc (F8Duh.aSeq hGood n) s,
                    ENNReal.ofReal ((s - t) ^ (-1 / 2 : ℝ)) * G t) :=
        fun n => (hD2_on_good _ (F8Duh.aSeq_spec hGood n).2).2.2.2.2
      have h_ne1 : ∀ᵐ s ∂(volume : Measure ℝ), s ≠ 1 := by
        rw [ae_iff]; simp
      filter_upwards [ae_all_iff.2 ha_bnd, h_ne1] with s hs_n hs_ne1 hs_mem
      have hs0 : 0 < s := hs_mem.1
      have hs1 : s < 1 := lt_of_le_of_ne hs_mem.2 hs_ne1
      set J := ∫⁻ t in Ioc 0 s, ENNReal.ofReal ((s - t) ^ (-1 / 2 : ℝ)) * G t
      have hcA_pos : 0 < A * p.ν ^ (-1 / 2 : ℝ) := mul_pos hA (Real.rpow_pos_of_pos hν0 _)
      by_cases hJ : J = ⊤
      · rw [hJ, add_top, ENNReal.mul_top (ENNReal.ofReal_pos.2 hcA_pos).ne']
        exact le_top
      · have hlim_real : Tendsto (fun n : ℕ => (s - F8Duh.aSeq hGood n) ^ (-1 / 2 : ℝ) * M)
            atTop (𝓝 (s ^ (-1 / 2 : ℝ) * M)) := by
          have hsub : Tendsto (fun n : ℕ => s - F8Duh.aSeq hGood n) atTop (𝓝 s) := by
            simpa using tendsto_const_nhds.sub (F8Duh.tendsto_aSeq hGood)
          exact ((hsub.rpow tendsto_const_nhds (Or.inl hs0.ne')).mul tendsto_const_nhds)
        have hlim_enn : Tendsto (fun n : ℕ =>
            ENNReal.ofReal (A * p.ν ^ (-1 / 2 : ℝ)) *
              (ENNReal.ofReal ((s - F8Duh.aSeq hGood n) ^ (-1 / 2 : ℝ) * M) + J))
            atTop
            (𝓝 (ENNReal.ofReal (A * p.ν ^ (-1 / 2 : ℝ)) *
              (ENNReal.ofReal (s ^ (-1 / 2 : ℝ) * M) + J))) := by
          have h1 : Tendsto (fun n : ℕ =>
              ENNReal.ofReal ((s - F8Duh.aSeq hGood n) ^ (-1 / 2 : ℝ) * M))
              atTop (𝓝 (ENNReal.ofReal (s ^ (-1 / 2 : ℝ) * M))) :=
            ENNReal.continuous_ofReal.continuousAt.tendsto.comp hlim_real
          have h2 : Tendsto (fun n : ℕ =>
              ENNReal.ofReal ((s - F8Duh.aSeq hGood n) ^ (-1 / 2 : ℝ) * M) + J)
              atTop (𝓝 (ENNReal.ofReal (s ^ (-1 / 2 : ℝ) * M) + J)) :=
            h1.add tendsto_const_nhds
          exact ENNReal.Tendsto.const_mul h2 (Or.inr ENNReal.ofReal_ne_top)
        refine le_of_tendsto_of_tendsto tendsto_const_nhds hlim_enn ?_
        filter_upwards [(F8Duh.tendsto_aSeq hGood).eventually (gt_mem_nhds hs0)] with n hn
        have ha_pos : 0 < F8Duh.aSeq hGood n := (F8Duh.aSeq_spec hGood n).1.1
        have hs_in : s ∈ Ioo (F8Duh.aSeq hGood n) (F8Duh.aSeq hGood n + 1) :=
          ⟨hn, by linarith⟩
        refine (hs_n n hs_in).trans ?_
        refine mul_le_mul_right (add_le_add le_rfl ?_) _
        exact lintegral_mono_set (Ioc_subset_Ioc_left ha_pos.le)
    -- Late `D²` bound (`1 < s`) via `denseGoodSeq hGood` approaching `(s - 1)⁺`
    have hLate : ∀ᵐ s ∂volume, 1 < s →
        ∑ i : Fin 2, ∑ j : Fin 2, F8U.cellL2 p.c (F8U.slice (D2 i j) s) ≤
          ENNReal.ofReal (A * p.ν ^ (-1 / 2 : ℝ)) *
            (ENNReal.ofReal M +
              ∫⁻ r in Ioc 0 1, ENNReal.ofReal (r ^ (-1 / 2 : ℝ)) * G (s - r)) := by
      have hd_bnd : ∀ m : ℕ, ∀ᵐ s ∂volume,
          s ∈ Ioo (F8Duh.denseGoodSeq hGood m) (F8Duh.denseGoodSeq hGood m + 1) →
            ∑ i : Fin 2, ∑ j : Fin 2, F8U.cellL2 p.c (F8U.slice (D2 i j) s) ≤
              ENNReal.ofReal (A * p.ν ^ (-1 / 2 : ℝ)) *
                (ENNReal.ofReal ((s - F8Duh.denseGoodSeq hGood m) ^ (-1 / 2 : ℝ) * M) +
                  ∫⁻ t in Ioc (F8Duh.denseGoodSeq hGood m) s,
                    ENNReal.ofReal ((s - t) ^ (-1 / 2 : ℝ)) * G t) :=
        fun m => (hD2_on_good _ (F8Duh.denseGoodSeq_spec hGood m).2).2.2.2.2
      filter_upwards [ae_all_iff.2 hd_bnd] with s hs_m hs1
      set J := ∫⁻ r in Ioc 0 1, ENNReal.ofReal (r ^ (-1 / 2 : ℝ)) * G (s - r)
      have hJ_eq : J = ∫⁻ t in Ico (s - 1) s, ENNReal.ofReal ((s - t) ^ (-1 / 2 : ℝ)) * G t := by
        dsimp only [J]
        rw [F8U.lintegral_Ioc_zero_one_sub s
          (fun r => ENNReal.ofReal (r ^ (-1 / 2 : ℝ)) * G (s - r))]
        simp only [sub_sub_cancel]
      have hcA_pos : 0 < A * p.ν ^ (-1 / 2 : ℝ) := mul_pos hA (Real.rpow_pos_of_pos hν0 _)
      by_cases hJ : J = ⊤
      · rw [hJ, add_top, ENNReal.mul_top (ENNReal.ofReal_pos.2 hcA_pos).ne']
        exact le_top
      · have hex_k : ∀ k : ℕ, ∃ m : ℕ,
            F8Duh.denseGoodSeq hGood m ∈ Ioo (s - 1) (min s (s - 1 + 1 / ((k : ℝ) + 1))) := by
          intro k
          have hpos_k : (0 : ℝ) < 1 / ((k : ℝ) + 1) := by positivity
          exact F8Duh.exists_denseGoodSeq_in_Ioo hGood (sub_pos.2 hs1)
            (lt_min (sub_lt_self s zero_lt_one) (by linarith))
        let mOf : ℕ → ℕ := fun k => Classical.choose (hex_k k)
        let τSeq : ℕ → ℝ := fun k => F8Duh.denseGoodSeq hGood (mOf k)
        have hτSeq_mem : ∀ k : ℕ, τSeq k ∈ Ioo (s - 1) (min s (s - 1 + 1 / ((k : ℝ) + 1))) :=
          fun k => Classical.choose_spec (hex_k k)
        have hτ_lim : Tendsto τSeq atTop (𝓝 (s - 1)) := by
          have h_up : Tendsto (fun k : ℕ => (s - 1) + 1 / ((k : ℝ) + 1)) atTop (𝓝 (s - 1)) := by
            simpa [one_div] using
              (tendsto_const_nhds (x := s - 1)).add
                (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
          exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds h_up
            (fun k => (hτSeq_mem k).1.le)
            (fun k => (hτSeq_mem k).2.le.trans (min_le_right _ _))
        have hlim_real : Tendsto (fun k : ℕ => (s - τSeq k) ^ (-1 / 2 : ℝ) * M)
            atTop (𝓝 M) := by
          have hsub : Tendsto (fun k : ℕ => s - τSeq k) atTop (𝓝 1) := by
            have h := (tendsto_const_nhds (x := s)).sub hτ_lim
            simpa using h
          have hrpow :=
            (hsub.rpow (tendsto_const_nhds (x := (-1 / 2 : ℝ))) (Or.inl one_ne_zero)).mul
              (tendsto_const_nhds (x := M))
          simpa using hrpow
        have hlim_enn : Tendsto (fun k : ℕ =>
            ENNReal.ofReal (A * p.ν ^ (-1 / 2 : ℝ)) *
              (ENNReal.ofReal ((s - τSeq k) ^ (-1 / 2 : ℝ) * M) + J))
            atTop
            (𝓝 (ENNReal.ofReal (A * p.ν ^ (-1 / 2 : ℝ)) * (ENNReal.ofReal M + J))) := by
          have h1 : Tendsto (fun k : ℕ => ENNReal.ofReal ((s - τSeq k) ^ (-1 / 2 : ℝ) * M))
              atTop (𝓝 (ENNReal.ofReal M)) :=
            ENNReal.continuous_ofReal.continuousAt.tendsto.comp hlim_real
          have h2 : Tendsto (fun k : ℕ => ENNReal.ofReal ((s - τSeq k) ^ (-1 / 2 : ℝ) * M) + J)
              atTop (𝓝 (ENNReal.ofReal M + J)) :=
            h1.add tendsto_const_nhds
          exact ENNReal.Tendsto.const_mul h2 (Or.inr ENNReal.ofReal_ne_top)
        refine le_of_tendsto_of_tendsto' tendsto_const_nhds hlim_enn fun k => ?_
        have hk_in := hτSeq_mem k
        have hτ_lt_s : τSeq k < s := lt_of_lt_of_le hk_in.2 (min_le_left _ _)
        have hs_in : s ∈ Ioo (τSeq k) (τSeq k + 1) := ⟨hτ_lt_s, by linarith [hk_in.1]⟩
        refine (hs_m (mOf k) hs_in).trans ?_
        refine mul_le_mul_right (add_le_add le_rfl ?_) _
        rw [hJ_eq, ← restrict_Ioo_eq_restrict_Ioc]
        have hsub_t : Ioo (τSeq k) s ⊆ Ico (s - 1) s :=
          fun t ht => ⟨(lt_trans hk_in.1 ht.1).le, ht.2⟩
        exact lintegral_mono_set hsub_t
    -- Assemble all output conjuncts
    refine ⟨z', zq', zη', D2, hz'_sm, hzq'_sm, hzη'_sm, hD2_sm,
      hz'_ae_z₁.trans hz₁_ae, hzq'_ae_zq₁.trans hzq₁_ae, hzη'_ae_zη₁.trans hzη₁_ae,
      fun s hs => ?_,
      hD2_wk00, hD2_wk01, hD2_wk10, hD2_wk11, hEarly, hLate⟩
    have hc1 := F8Duh.tendsto_cellL2_perJointProf hc hZ_cont.1 hUZ hs
    have hc2 := F8Duh.tendsto_cellL2_perJointProf hc hZ_cont.2.1 hUqZ hs
    have hc3 := F8Duh.tendsto_cellL2_perJointProf hc hZ_cont.2.2 hUηZ hs
    simpa [F8U.cylH1] using (hc1.add hc2).add hc3
  · -- Degenerate `M < 0`: `(0, 0, 0, 0)` solves the entire conclusion trivially
    have hM_lt : M < 0 := lt_of_not_ge hM
    obtain ⟨hz0, hzq0, hzη0⟩ :=
      F8Duh.ae_zero_of_sliceH1Norm_nonpos hc hM_lt hz.periodic hz.weak_q hz.weak_eta hz.solenoidal
        hz_M
    have hwk0 : ∀ v : Coord → Fin 3 → ℝ, HasWeakVec v dZero 0 0 :=
      fun _ _ => ⟨fun _ _ => ⟨by simp, by simp⟩, fun _ _ => by simp⟩
    have hcell0 : ∀ s : ℝ, F8U.cellL2 p.c (F8U.slice (0 : CProf) s) = 0 := by
      intro s
      unfold F8U.cellL2 F8U.slice
      simp
    refine ⟨0, 0, 0, fun _ _ => 0,
      stronglyMeasurable_const, stronglyMeasurable_const, stronglyMeasurable_const,
      fun _ _ => stronglyMeasurable_const,
      hz0, hzq0, hzη0, fun s _ => ?_,
      hwk0 vQ0, hwk0 vEta, hwk0 vQ0, hwk0 vEta,
      Eventually.of_forall (fun s _ => by simp [hcell0]),
      Eventually.of_forall (fun s _ => by simp [hcell0])⟩
    have hzero_cyl : ∀ s' : ℝ, F8U.cylH1 p.c (fun y => (0 : CProf) (s', y) - (0 : CProf) (s, y))
        (fun y => (0 : CProf) (s', y) - (0 : CProf) (s, y))
        (fun y => (0 : CProf) (s', y) - (0 : CProf) (s, y)) = 0 := by
      intro s'
      unfold F8U.cylH1 F8U.cellL2
      simp
    simp_rw [hzero_cyl]
    exact tendsto_const_nhds

end UnforcedLeray.Short.IIb
