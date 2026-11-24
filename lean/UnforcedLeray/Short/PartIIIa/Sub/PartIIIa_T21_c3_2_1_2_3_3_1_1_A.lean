import UnforcedLeray.Short.PartIIIa.Sub.PartIIIa_T21_c3_2_1_2_3_3_1_1
import UnforcedLeray.Short.PartIIIa.Clock.FrameAmplitudeProof.WeakFTC.CutFTC.DualBounds

/-!
# `PartIII-a:T21/c3/2/1/2/3/3/1/1/1`: Leaf A `MovSolExists`, reduced to a train bound

Source of record: `the November 2 reference manuscript` (SP), lines 2861-2866
(`W = J_a⁻¹ w`, `L_{ν,c}(z) W = -V·∇W - (K_d W)·∇E_mov`).

* `V = N⁻¹ I_d W` lies in `L²_m` for every age of the block, unconditionally: `w(s) ∈ X_{m,c}`
  (`IsLinearisedFlow.memX`), `J_a⁻¹ : X_{m,c} → X_{m,d}` for `a ≥ 1` (`memLp_JscaleInv`), and the
  zero extension is an isometry `X_{m,d} → L²_m` (`memLp_cellZeroExt_cToPlane`).
* `LV = N⁻¹ I_d L_int W` lies in `L²_m` as soon as `∇E_mov(s)` has a finite weighted sup norm
  `⟨y⟩^{m+2}` on the moving cell (`RelIntA.cxInter_bound`, the cylinder kernel operator with a
  weighted coefficient). This is `TrainGradWeightedFinite m` below. Part I gives it only for
  `ν ≤ ν₀` (`RescaledTrainBounds`, `TrainWeightedJetPoly`); `MovSolExists` quantifies over every
  `ν > 0` (the hypotheses force only `ν ≤ 1`), so the leaf is proved here conditionally:
  `movSolExists_of_trainGrad`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology Metric UnforcedLeray.Blueprint.Planar
open scoped ENNReal ComplexConjugate ContDiff InnerProductSpace

namespace UnforcedLeray.Short.IIIa

open FrameShortBlockSub FrameBlockContractSub CompactDuhamelGapSub BlockPropagatorSub
  VariationOfConstantsSub VariationOfConstantsMildSub

namespace ComplMildTestedSplit

/-- **Needed train input** (SP 2866-2873, 3050-3051 at a fixed viscosity): for every `ν > 0`,
every BUC train at `c = ν⁻²` and every age `r ≥ 0` with `θ(r) ≥ 1`, the rescaled train vorticity
gradient `∇E_mov(r)` has a finite weighted sup norm `⟨y⟩^{m+2}` on the moving cell `C_{d(r)}`
(no uniformity in `ν`, `r` is required). -/
def TrainGradWeightedFinite (m : ℝ) : Prop :=
  ∀ ν : ℝ, 0 < ν → ∀ tr : UnforcedLeray.B0140.TrainSol ν (ν ^ (-2 : ℝ)),
    UnforcedLeray.Short.PartI.IsBUCTrain tr → ∀ r : ℝ, 0 ≤ r → 1 ≤ clockTheta ν r →
      ∃ C : ℝ, ∀ y ∈ B0579.cell (cellLen (ν ^ (-2 : ℝ)) (clockA ν r)),
        (|movingTrainGradE tr r y 0| + |movingTrainGradE tr r y 1|) *
          B0579.jb y ^ (m / 2 + 1) ≤ C

namespace MovSolExistsSub

/-- `θ` is antitone in the age. -/
theorem clockTheta_anti {ν s t : ℝ} (hν : 0 < ν) (hs : 0 ≤ s) (hst : s ≤ t) :
    clockTheta ν t ≤ clockTheta ν s := by
  unfold clockTheta clockA
  have h1 : 0 < ν * (1 + ν * s) := by positivity
  have h2 : ν * (1 + ν * s) ≤ ν * (1 + ν * t) := by
    have : ν * s ≤ ν * t := mul_le_mul_of_nonneg_left hst hν.le
    nlinarith
  exact inv_anti₀ h1 h2

/-- `θ(r) ≥ 1` at some age `r ≥ 0` forces `ν ≤ 1`. -/
theorem nu_le_one_of_theta {ν r : ℝ} (hν : 0 < ν) (hr : 0 ≤ r) (hθ : 1 ≤ clockTheta ν r) :
    ν ≤ 1 := by
  have ha : 1 ≤ clockA ν r := one_le_clockA hν.le hr
  have hpos : 0 < ν * clockA ν r := by positivity
  unfold clockTheta at hθ
  have h : ν * clockA ν r ≤ 1 := by
    have := (one_le_inv₀ hpos).1 hθ
    exact this
  nlinarith

/-- The localized interaction is the complex cylinder interaction with coefficient `∇E_mov`. -/
theorem movLInt_eq_cxInter' {ν : ℝ} (tr : UnforcedLeray.B0140.TrainSol ν (ν ^ (-2 : ℝ)))
    (r : ℝ) (W : ℝ × ℝ → ℂ) :
    movLInt tr r W =
      BlockPropagatorInteriorSub.OrgSplit.RelIntA.cxInter
        (cellLen (ν ^ (-2 : ℝ)) (clockA ν r))
        (fun y => (movingTrainGradE tr r y 0, movingTrainGradE tr r y 1)) W := by
  funext y
  rfl

/-- `L_int W ∈ X_{m,d}` for `W ∈ X_{m,d}` under the weighted coefficient bound. -/
theorem memLp_movLInt {m : ℝ} (hm : 8 < m) {ν r : ℝ} (hν : 0 < ν) (hr : 0 ≤ r)
    (hθ : 1 ≤ clockTheta ν r) (tr : UnforcedLeray.B0140.TrainSol ν (ν ^ (-2 : ℝ)))
    {C : ℝ}
    (hC : ∀ y ∈ B0579.cell (cellLen (ν ^ (-2 : ℝ)) (clockA ν r)),
      (|movingTrainGradE tr r y 0| + |movingTrainGradE tr r y 1|) *
        B0579.jb y ^ (m / 2 + 1) ≤ C)
    {W : ℝ × ℝ → ℂ}
    (hW : MemLp W 2 (B0579.cellMeasure (cellLen (ν ^ (-2 : ℝ)) (clockA ν r)) m)) :
    MemLp (movLInt tr r W) 2 (B0579.cellMeasure (cellLen (ν ^ (-2 : ℝ)) (clockA ν r)) m) := by
  have hν1 : ν ≤ 1 := nu_le_one_of_theta hν hr hθ
  have hd : 1 ≤ cellLen (ν ^ (-2 : ℝ)) (clockA ν r) :=
    ComplCouplingSub.one_le_cellLen_of_theta hν hν1 hr hθ
  have hcoef : IIb.IsCylWeightedCoeff (cellLen (ν ^ (-2 : ℝ)) (clockA ν r)) m (max C 0)
      (fun y => (movingTrainGradE tr r y 0, movingTrainGradE tr r y 1)) :=
    ⟨(EulerErrorSub.continuous_movingTrainGradE tr hr 0).prodMk
        (EulerErrorSub.continuous_movingTrainGradE tr hr 1),
      fun y hy => (hC y hy).trans (le_max_left _ _)⟩
  obtain ⟨hmeas, hbd⟩ := BlockPropagatorInteriorSub.OrgSplit.RelIntA.cxInter_bound hd
    (by linarith) (le_max_right C 0) hcoef hW
  rw [movLInt_eq_cxInter']
  refine ⟨hmeas, ?_⟩
  have hWfin : xNorm (cellLen (ν ^ (-2 : ℝ)) (clockA ν r)) m W < ⊤ := hW.2
  exact lt_of_le_of_lt hbd (ENNReal.mul_lt_top ENNReal.ofReal_lt_top hWfin)

open Classical in
/-- The `L²_m` class of a function (`0` if the function is not in `L²_m`). -/
def movToL2 (m : ℝ) (g : ℂ → ℂ) : Planar.L2w m :=
  if h : MemLp g 2 (Planar.wMeasure m) then h.toLp g else 0

theorem coeFn_movToL2_volume {m : ℝ} {g : ℂ → ℂ} (h : MemLp g 2 (Planar.wMeasure m)) :
    ⇑(movToL2 m g) =ᵐ[volume] g := by
  have h1 : ⇑(movToL2 m g) =ᵐ[Planar.wMeasure m] g := by
    simp only [movToL2, h, ↓reduceDIte]
    exact h.coeFn_toLp
  exact (Planar.volume_ac m).ae_le h1

/-- The normalised zero extension of a cell field in `X_{m,d}` lies in `L²_m`. -/
theorem memLp_norm_cellZeroExt {m d : ℝ} (N : ℝ) {W : ℝ × ℝ → ℂ}
    (hW : MemLp W 2 (B0579.cellMeasure d m)) :
    MemLp (fun z : ℂ => ((N : ℝ) : ℂ)⁻¹ * cellZeroExt d W (cToPlane z)) 2
      (Planar.wMeasure m) :=
  (memLp_cellZeroExt_cToPlane d m hW).const_mul _


/-- Moving-cell points rescale into the physical cell: `y ∈ C_d`, `d = c/√a` gives
`√a y ∈ C_c`. -/
theorem sqrt_mul_mem_cell {c a : ℝ} (ha : 0 < a) {y : ℝ × ℝ}
    (hy : y ∈ B0579.cell (cellLen c a)) :
    ((Real.sqrt a * y.1, Real.sqrt a * y.2) : ℝ × ℝ) ∈ B0579.cell c := by
  have hs : 0 < Real.sqrt a := Real.sqrt_pos.2 ha
  have hd : Real.sqrt a * (cellLen c a / 2) = c / 2 := by
    unfold cellLen
    field_simp
  obtain ⟨⟨h1, h2⟩, -⟩ := hy
  refine ⟨⟨?_, ?_⟩, Set.mem_univ _⟩
  · have := mul_le_mul_of_nonneg_left h1 hs.le
    simp only at this ⊢
    nlinarith
  · have := mul_lt_mul_of_pos_left h2 hs
    simp only at this ⊢
    nlinarith

/-- `⟨y⟩ ≤ ⟨√a y⟩` for `a ≥ 1`. -/
theorem jb_le_jb_sqrt_mul {a : ℝ} (ha : 1 ≤ a) (y : ℝ × ℝ) :
    B0579.jb y ≤ B0579.jb ((Real.sqrt a * y.1, Real.sqrt a * y.2) : ℝ × ℝ) := by
  unfold B0579.jb
  have hsq : Real.sqrt a ^ 2 = a := Real.sq_sqrt (by linarith)
  simp only [mul_pow, hsq]
  nlinarith [sq_nonneg y.1, sq_nonneg y.2]

/-- **The train input in the small-viscosity regime** (from Part I through
`CutFTCDual.ladTrainBddAll_unconditional`): for `ν ≤ ν₀(m)` the weighted sup bound of `∇E_mov(r)`
holds at every age `r ≥ 0`. -/
theorem trainGradWeighted_small (m : ℝ) (hm : 8 < m) :
    ∃ ν₀ : ℝ, 0 < ν₀ ∧ ∀ ν ∈ Ioc 0 ν₀, ∀ tr : UnforcedLeray.B0140.TrainSol ν (ν ^ (-2 : ℝ)),
      UnforcedLeray.Short.PartI.IsBUCTrain tr → ∀ r : ℝ, 0 ≤ r →
        ∃ C : ℝ, ∀ y ∈ B0579.cell (cellLen (ν ^ (-2 : ℝ)) (clockA ν r)),
          (|movingTrainGradE tr r y 0| + |movingTrainGradE tr r y 1|) *
            B0579.jb y ^ (m / 2 + 1) ≤ C := by
  obtain ⟨ν₀, hν₀, h⟩ := CutFTCDual.ladTrainBddAll_unconditional m
  refine ⟨ν₀, hν₀, fun ν hν tr htr r hr => ?_⟩
  obtain ⟨C, hC⟩ := h ν hν tr htr r hr
  have ha1 : 1 ≤ clockA ν r := one_le_clockA hν.1.le hr
  have ha0 : 0 < clockA ν r := by linarith
  refine ⟨clockA ν r ^ ((5 : ℝ) / 2) * (2 * C), fun y hy => ?_⟩
  have hx := sqrt_mul_mem_cell ha0 hy
  obtain ⟨-, hE⟩ := hC r ⟨hr, le_rfl⟩ _ hx
  have hjb : B0579.jb y ^ (m / 2 + 1) ≤
      B0579.jb ((Real.sqrt (clockA ν r) * y.1, Real.sqrt (clockA ν r) * y.2) : ℝ × ℝ) ^
        ((m + 2) / 2) := by
    rw [show (m + 2) / 2 = m / 2 + 1 by ring]
    exact Real.rpow_le_rpow (B0579.jb_pos y).le (jb_le_jb_sqrt_mul ha1 y) (by linarith)
  have hA : 0 ≤ clockA ν r ^ ((5 : ℝ) / 2) := Real.rpow_nonneg ha0.le _
  have hjy : 0 ≤ B0579.jb y ^ (m / 2 + 1) := Real.rpow_nonneg (B0579.jb_pos y).le _
  have hk : ∀ k : Fin 2, |movingTrainGradE tr r y k| * B0579.jb y ^ (m / 2 + 1) ≤
      clockA ν r ^ ((5 : ℝ) / 2) * C := by
    intro k
    have hk' : |movingTrainGradE tr r y k| = clockA ν r ^ ((5 : ℝ) / 2) *
        |B0579.pd k (UnforcedLeray.B0238.Ec tr r)
          ((Real.sqrt (clockA ν r) * y.1, Real.sqrt (clockA ν r) * y.2) : ℝ × ℝ)| := by
      unfold movingTrainGradE
      rw [abs_mul, abs_of_nonneg hA]
    rw [hk', mul_assoc]
    refine mul_le_mul_of_nonneg_left ?_ hA
    calc |B0579.pd k (UnforcedLeray.B0238.Ec tr r)
          ((Real.sqrt (clockA ν r) * y.1, Real.sqrt (clockA ν r) * y.2) : ℝ × ℝ)| *
          B0579.jb y ^ (m / 2 + 1)
        ≤ |B0579.pd k (UnforcedLeray.B0238.Ec tr r)
          ((Real.sqrt (clockA ν r) * y.1, Real.sqrt (clockA ν r) * y.2) : ℝ × ℝ)| *
          B0579.jb ((Real.sqrt (clockA ν r) * y.1, Real.sqrt (clockA ν r) * y.2) : ℝ × ℝ) ^
            ((m + 2) / 2) := mul_le_mul_of_nonneg_left hjb (abs_nonneg _)
      _ ≤ C := by rw [mul_comm]; exact hE k
  have h0 := hk 0
  have h1 := hk 1
  calc (|movingTrainGradE tr r y 0| + |movingTrainGradE tr r y 1|) * B0579.jb y ^ (m / 2 + 1)
      = |movingTrainGradE tr r y 0| * B0579.jb y ^ (m / 2 + 1) +
          |movingTrainGradE tr r y 1| * B0579.jb y ^ (m / 2 + 1) := by ring
    _ ≤ clockA ν r ^ ((5 : ℝ) / 2) * (2 * C) := by linarith

/-- The core of Leaf A at fixed data: given the weighted bound of `∇E_mov` at the ages of the
block, `V = N⁻¹ I_d W` and `LV = N⁻¹ I_d L_int W` exist in `L²_m`. -/
theorem exists_V_LV (P : PlanarData) {m : ℝ} (hm : 8 < m) {B b : ℝ} (hb : 1 ≤ b) {ν : ℝ}
    (hν : 0 < ν) (tr : UnforcedLeray.B0140.TrainSol ν (ν ^ (-2 : ℝ))) {t₁ t₂ : ℝ}
    (h1 : 0 ≤ t₁) (h12 : t₁ ≤ t₂) (hθ : b ≤ clockTheta ν t₂)
    (hZ : movingZ ν t₂ - movingZ ν t₁ = B) {f : ℝ × ℝ → ℂ} {w : ℝ → ℝ × ℝ → ℂ}
    {u : ℝ → ℝ × ℝ → Fin 2 → ℂ} (hfl : IsLinearisedFlow ν (ν ^ (-2 : ℝ)) m tr t₁ f w u)
    (hT : ∀ r : ℝ, 0 ≤ r → 1 ≤ clockTheta ν r →
      ∃ C : ℝ, ∀ y ∈ B0579.cell (cellLen (ν ^ (-2 : ℝ)) (clockA ν r)),
        (|movingTrainGradE tr r y 0| + |movingTrainGradE tr r y 1|) *
          B0579.jb y ^ (m / 2 + 1) ≤ C) :
    ∃ V LV : ℝ → Planar.L2w m, VRep P m B ν t₁ w V ∧ LVRep P m B ν tr t₁ w LV := by
  -- ages of the block
  have hage : ∀ τ ∈ Icc (0 : ℝ) B, ageAt ν t₁ τ ∈ Icc t₁ t₂ := fun τ hτ =>
    ageAt_mem_Icc hν h1 h12 hZ hτ
  have hθs : ∀ τ ∈ Icc (0 : ℝ) B, 1 ≤ clockTheta ν (ageAt ν t₁ τ) := fun τ hτ =>
    (hb.trans hθ).trans (clockTheta_anti hν (h1.trans (hage τ hτ).1) (hage τ hτ).2)
  -- `W(s) ∈ X_{m,d(s)}`
  have hW : ∀ τ ∈ Icc (0 : ℝ) B,
      MemLp (movingW ν w (ageAt ν t₁ τ)) 2
        (B0579.cellMeasure (cellLen (ν ^ (-2 : ℝ)) (clockA ν (ageAt ν t₁ τ))) m) := by
    intro τ hτ
    have hs0 : 0 ≤ ageAt ν t₁ τ := h1.trans (hage τ hτ).1
    exact ComplCouplingSub.memLp_JscaleInv (by linarith) (one_le_clockA hν.le hs0)
      (hfl.memX _ (hage τ hτ).1)
  refine ⟨fun τ => movToL2 m (fun z : ℂ =>
      ((clockN P ν t₁ (ageAt ν t₁ τ) : ℝ) : ℂ)⁻¹ *
        cellZeroExt (cellLen (ν ^ (-2 : ℝ)) (clockA ν (ageAt ν t₁ τ)))
          (movingW ν w (ageAt ν t₁ τ)) (cToPlane z)),
    fun σ => movToL2 m (fun z : ℂ =>
      ((clockN P ν t₁ (ageAt ν t₁ σ) : ℝ) : ℂ)⁻¹ *
        cellZeroExt (cellLen (ν ^ (-2 : ℝ)) (clockA ν (ageAt ν t₁ σ)))
          (movLInt tr (ageAt ν t₁ σ) (movingW ν w (ageAt ν t₁ σ))) (cToPlane z)),
    fun τ hτ => ?_, fun σ hσ => ?_⟩
  · exact coeFn_movToL2_volume (memLp_norm_cellZeroExt _ (hW τ hτ))
  · have hs0 : 0 ≤ ageAt ν t₁ σ := h1.trans (hage σ hσ).1
    obtain ⟨C, hC⟩ := hT (ageAt ν t₁ σ) hs0 (hθs σ hσ)
    exact coeFn_movToL2_volume (memLp_norm_cellZeroExt _
      (memLp_movLInt hm hν hs0 (hθs σ hσ) tr hC (hW σ hσ)))

end MovSolExistsSub

open MovSolExistsSub in
/-- **Leaf A, conditional on the train input** (SP 2861-2866): the normalised zero extensions
`V = N⁻¹ I_d W` and `LV = N⁻¹ I_d L_int W` exist in `L²_m` on the block. -/
theorem movSolExists_of_trainGrad (hT : ∀ m : ℝ, 8 < m → TrainGradWeightedFinite m) :
    MovSolExists := by
  intro P hP m hm B b hB0 hb ν hν tr htr t₁ t₂ h1 h12 hθ hZ f w u hfl hz
  exact exists_V_LV P hm hb hν tr h1 h12 hθ hZ hfl (hT m hm ν hν tr htr)

/-- `MovSolExists` in the small-viscosity regime `ν ≤ ν₀(m)` (the regime of Part I's train
bounds). -/
def MovSolExistsSmall : Prop :=
  ∀ m : ℝ, 8 < m → ∃ ν₀ : ℝ, 0 < ν₀ ∧
  ∀ (P : PlanarData), IsPlanarReference P →
  ∀ B b : ℝ, 0 < B → 1 ≤ b →
  ∀ ν : ℝ, 0 < ν → ν ≤ ν₀ →
    ∀ tr : UnforcedLeray.B0140.TrainSol ν (ν ^ (-2 : ℝ)),
      UnforcedLeray.Short.PartI.IsBUCTrain tr →
      ∀ t₁ t₂ : ℝ, 0 ≤ t₁ → t₁ ≤ t₂ → b ≤ clockTheta ν t₂ →
        movingZ ν t₂ - movingZ ν t₁ = B →
          ∀ f w u, IsLinearisedFlow ν (ν ^ (-2 : ℝ)) m tr t₁ f w u →
            HasZeroCirculation (ν ^ (-2 : ℝ)) f →
            ∃ V LV : ℝ → Planar.L2w m, VRep P m B ν t₁ w V ∧ LVRep P m B ν tr t₁ w LV

open MovSolExistsSub in
/-- **Leaf A in the small-viscosity regime, unconditional.** -/
theorem movSolExistsSmall : MovSolExistsSmall := by
  intro m hm
  obtain ⟨ν₀, hν₀, hT⟩ := trainGradWeighted_small m hm
  refine ⟨ν₀, hν₀, fun P _ B b _ hb ν hν hν₀' tr htr t₁ t₂ h1 h12 hθ hZ f w u hfl _ => ?_⟩
  exact exists_V_LV P hm hb hν tr h1 h12 hθ hZ hfl
    (fun r hr _ => hT ν ⟨hν, hν₀'⟩ tr htr r hr)

end ComplMildTestedSplit

end UnforcedLeray.Short.IIIa
