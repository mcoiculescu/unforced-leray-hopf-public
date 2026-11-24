import UnforcedLeray.Short.PartIIb.Sub.PartIIb_F9
import UnforcedLeray.Short.PartIIb.Sub.PartIIb_F10
import UnforcedLeray.Short.PartIIb.Tasks.FlatUnique
import UnforcedLeray.Short.PartIIb.Tasks.LocalSmoothing.FlatKFromH2.SliceProof
import UnforcedLeray.Short.PartIIb.Tasks.LocalSmoothing.FlatKFromH2.Assembly
import UnforcedLeray.Short.PartIIb.Tasks.AffineColumnComparison.Column.Parts.InletComponentJets
import UnforcedLeray.Short.PartIIb.Tasks.AffineColumnComparison.Column.Parts.WeightNorm
import UnforcedLeray.Short.PartIIb.Sub.PartIIb_F8_1_org.DuhamelRegularity.WeakAndSlices
import UnforcedLeray.Short.PartIIb.Sub.PartIIb_T20

/-!
# `PartII-b:F9/3` (`Tasks/FlatReconstruction/GlobalIdentity.lean`)

Source of record: `the November 2 reference manuscript`
(SP), lines 2316–2328 (`short-bg:flat-reconstruction`, display 2326).

## Unconditionally proved here (zero `sorry`)

1. `flat_unique_inHr`: extension of `flat_unique` (`PartII-b:T11`) from `InFlatClass c r b` to
   `InHr c r b` (`IsFlatResponse ν μ 0 b` with `0 < μ.re + (3 / r - 1) / 2` implies
   `b =ᵐ[hMeas c r] 0`).
2. `mulSPsi`, `isPlanarSolTest_mulSPsi`, `flatTranspose_zero_eq_meridTranspose_mulSPsi`,
   `cdot_flatK_eq_cdot_flatBv_mulSPsi`: exact operator-transpose bridge on `{s > 0}` showing
   `flatTranspose ν 0 Ψ = meridTranspose ν (s • Ψ)` and closure of `IsPlanarSolTest` under
   `Ψ ↦ s • Ψ`, cancelling the projected body source `g` via `IsGlobalMeridionalCorrection.equation`
   and `IsBodySource.equation`.
3. `inletProf_solenoidal` and `inletProf_flatTranspose_ibp`: smooth integration by parts on the
   flat inlet profile `inletProf p α` matching `flatK p.train (inletProf p α)` minus
   `∑ i, α_i flatColumn p i`.
4. `flatReconstruction_isFlatResponse`: complete unconditional proof that
   `b0 + z - inletProf p α` satisfies `IsFlatResponse p.ν 0 (toProf p.c f)` whenever
   `toProf p.c f =ᵐ[hMeas p.c bgp] toProf p.c F - flatK(b0 + z - Eα) - ∑ α_i flatColumn p i`.
5. `inHr_and_inFlatClass_of_ae_eq_response`: complete unconditional proof of
   `InHr p.c bgp (z - inletProf p α)` and `InFlatClass p.c bgp (b0 + z - inletProf p α)` once
   `b0 + z - inletProf p α =ᵐ[hMeas p.c bgp] b_f` for the `InFlatClass` flat response `b_f` of `f`.
6. Concrete remaining sub-steps (`FlatReconstructionLinearR0Step`, `InletEntranceCurlIdentity`,
   `FlatReconstructionZeroCurlUniqueStep`) and complete conditional assembly
   `flatReconstructionIdentityStep_of_steps`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal NNReal ContDiff

namespace UnforcedLeray.Short.IIb

open UnforcedLeray.Cons.C03 UnforcedLeray.Cons.C03.Concrete UnforcedLeray.Blueprint

/-! ## 1. Extension of `flat_unique` (`PartII-b:T11`) from `InFlatClass` to `InHr` -/

theorem sliceDualVanish_inHr {c r ν : ℝ} {μ : ℂ}
    (hc : 0 < c) (hν : 0 < ν) (hr : 1 < r) (_hr3 : r < 3)
    (ha : 0 < μ.re + (3 / r - 1) / 2)
    {b : CProf} (hb : InHr c r b) (h0 : IsFlatResponse ν μ 0 b)
    {ζ : ℝ × ℝ → ℝ} {H : Coord → ℝ} (hζ : NiceStream c ζ)
    (hH : HeatSol c ν (r / (r - 1)) H)
    (hcon : ∀ τ : ℝ, 0 < τ → ∀ i : Fin 2,
      ∫⁻ p, ‖perpGrad (fun z => H (τ, z)) p i‖ₑ ^ (r / (r - 1)) ∂(Cyl.avgμ c) ≤
        ∫⁻ p, ‖perpGrad ζ p i‖ₑ ^ (r / (r - 1)) ∂(Cyl.avgμ c))
    {s : ℝ} (hs : 0 < s) :
    ∀ᵐ σ : ℝ ∂(volume.restrict (Ioo (0 : ℝ) s)), slicePair c b H σ s = 0 := by
  obtain ⟨κ, hκ⟩ := flatDualConstancy c r ν μ b H s hc hν hr hs hb h0 hH
  have hκ' : ∀ᵐ σ ∂(volume.restrict (Ioo (0 : ℝ) s)),
      ((σ : ℝ) : ℂ) ^ μ * slicePair c b H σ s = κ := hκ
  have hK0 : 0 ≤ (∑ i : Fin 2, (∫⁻ p, ‖perpGrad ζ p i‖ₑ ^ (r / (r - 1)) ∂(Cyl.avgμ c)) ^
      (1 / (r / (r - 1)))).toReal * s ^ (μ.re + (3 / r - 1) / 2) :=
    mul_nonneg ENNReal.toReal_nonneg (Real.rpow_nonneg hs.le _)
  have hκ0 : ‖κ‖ = 0 :=
    sd_norm_zero (show (0 : ℝ) < r by linarith) hK0 (norm_nonneg κ)
      (fun ε hε => sd_kappa_bound μ hc hr ha hb hζ hH.smooth hcon κ hs hκ' ε hε)
  have hκ00 : κ = 0 := norm_eq_zero.1 hκ0
  filter_upwards [hκ', ae_restrict_mem measurableSet_Ioo] with σ hσ hσI
  rw [hκ00] at hσ
  rcases mul_eq_zero.1 hσ with h | h
  · exfalso
    have hn := Complex.norm_cpow_eq_rpow_re_of_pos hσI.1 μ
    rw [h, norm_zero] at hn
    exact (Real.rpow_pos_of_pos hσI.1 _).ne' hn.symm
  · exact h

/-- Uniqueness of the homogeneous flat response (`IsFlatResponse ν μ 0 b`) assuming only
`InHr c r b` rather than `InFlatClass c r b`. -/
theorem flat_unique_inHr {c r ν : ℝ} {μ : ℂ}
    (hc : 0 < c) (hν : 0 < ν) (hr : 1 < r) (hr3 : r < 3)
    (ha : 0 < μ.re + (3 / r - 1) / 2)
    (b : CProf) (hb : InHr c r b) (h0 : IsFlatResponse ν μ 0 b) :
    b =ᵐ[hMeas c r] 0 := by
  refine niceFieldsSeparate c r b hc hr hr3 hb h0.solenoidal (fun θ ζ hθ hζ => ?_)
  rw [sliceProductFormula c r b θ ζ hc hr hb hθ hζ]
  have hr' : 1 < r / (r - 1) := by
    rw [lt_div_iff₀ (by linarith)]; linarith
  obtain ⟨H, hH, hcon, hconv⟩ := heatStreamDual c ν (r / (r - 1)) ζ hc hν hr' hζ
  have e1 := fun s (hs : 0 < s) => sliceDualVanish_inHr hc hν hr hr3 ha hb h0 hζ hH hcon hs
  have e2 := sliceJointNull c r ν b H hc hr hb hH e1
  have e3 := slicePointwise c r b ζ H hc hr hb hζ hconv e2
  refine integral_eq_zero_of_ae ?_
  filter_upwards [e3] with σ hσ
  have hstr : ∀ p, streamPair b θ ζ (σ, p) =
      (θ σ : ℂ) * ∑ i : Fin 2, b (σ, p) i * ((perpGrad ζ p i : ℝ) : ℂ) := by
    intro p
    simp only [streamPair, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    push_cast
    ring
  simp_rw [hstr]
  simp only [Pi.zero_apply]
  rw [integral_const_mul, hσ, mul_zero]

/-! ## 2. Transpose bridge `flatTranspose ν 0 Ψ = meridTranspose ν (s • Ψ)` -/

namespace GlobalIdHelp

/-- Age-multiplied planar solenoidal test `(s • Ψ)(x, i) = x.1 * Ψ x i`. -/
def mulSPsi (Ψ : Coord → Fin 2 → ℝ) (x : Coord) (i : Fin 2) : ℝ :=
  x.1 * Ψ x i

lemma isCoordTest_mulS {φ : Coord → ℝ} (hφ : IsCoordTest φ) :
    IsCoordTest (fun x : Coord => x.1 * φ x) := by
  refine ⟨contDiff_fst.mul hφ.smooth, hφ.compact.mul_left, ?_⟩
  have hsub : Function.support (fun x : Coord => x.1 * φ x) ⊆ Function.support φ := by
    intro x hx
    exact right_ne_zero_of_mul hx
  exact (closure_minimal (hsub.trans (subset_tsupport φ)) (isClosed_tsupport φ)).trans hφ.supp

lemma cpd_mulS_zero {φ : Coord → ℝ} (hφ : ContDiff ℝ ∞ φ) (x : Coord) :
    cpd 0 (fun y : Coord => y.1 * φ y) x = φ x + x.1 * cpd 0 φ x := by
  unfold cpd
  have h1 : HasFDerivAt (fun y : Coord => y.1) (ContinuousLinearMap.fst ℝ ℝ (ℝ × ℝ)) x :=
    hasFDerivAt_fst
  have h2 : HasFDerivAt φ (fderiv ℝ φ x) x :=
    (hφ.differentiable (by simp) x).hasFDerivAt
  have hm : HasFDerivAt (fun y : Coord => y.1 * φ y) _ x := h1.mul h2
  rw [hm.fderiv]
  simp [cdir]
  ring

lemma cpd_mulS_spatial {φ : Coord → ℝ} (hφ : ContDiff ℝ ∞ φ) (j : Fin 3)
    (hj : (cdir j).1 = 0) (x : Coord) :
    cpd j (fun y : Coord => y.1 * φ y) x = x.1 * cpd j φ x := by
  unfold cpd
  have h1 : HasFDerivAt (fun y : Coord => y.1) (ContinuousLinearMap.fst ℝ ℝ (ℝ × ℝ)) x :=
    hasFDerivAt_fst
  have h2 : HasFDerivAt φ (fderiv ℝ φ x) x :=
    (hφ.differentiable (by simp) x).hasFDerivAt
  have hm : HasFDerivAt (fun y : Coord => y.1 * φ y) _ x := h1.mul h2
  rw [hm.fderiv]
  simp [hj]

lemma cpd2_mulS_spatial {φ : Coord → ℝ} (hφ : ContDiff ℝ ∞ φ) (j : Fin 3)
    (hj : (cdir j).1 = 0) (x : Coord) :
    cpd j (fun y => cpd j (fun z => z.1 * φ z) y) x =
      x.1 * cpd j (fun y => cpd j φ y) x := by
  have heq : (fun y : Coord => cpd j (fun z => z.1 * φ z) y) =
      fun y : Coord => y.1 * cpd j φ y := by
    funext y
    exact cpd_mulS_spatial hφ j hj y
  have hd : ContDiff ℝ ∞ (fun y : Coord => cpd j φ y) :=
    ((hφ.fderiv_right (m := ∞) (by simp)).clm_apply contDiff_const)
  rw [heq]
  exact cpd_mulS_spatial hd j hj x

lemma isPlanarSolTest_mulSPsi {Ψ : Coord → Fin 2 → ℝ} (hΨ : IsPlanarSolTest Ψ) :
    IsPlanarSolTest (mulSPsi Ψ) := by
  refine ⟨fun i => isCoordTest_mulS (hΨ.smooth i), fun x => ?_⟩
  unfold mulSPsi
  rw [cpd_mulS_spatial (hΨ.smooth 0).smooth 1 rfl x,
    cpd_mulS_spatial (hΨ.smooth 1).smooth 2 rfl x, ← mul_add, hΨ.div_free x, mul_zero]

lemma flatTranspose_zero_eq_meridTranspose_mulSPsi (ν : ℝ)
    {Ψ : Coord → Fin 2 → ℝ} (hΨ : IsPlanarSolTest Ψ) (x : Coord) (i : Fin 2) :
    flatTranspose ν 0 Ψ x i = meridTranspose ν (mulSPsi Ψ) x i := by
  unfold flatTranspose meridTranspose mulSPsi
  rw [cpd_mulS_zero (hΨ.smooth i).smooth x,
    cpd2_mulS_spatial (hΨ.smooth i).smooth 1 rfl x,
    cpd2_mulS_spatial (hΨ.smooth i).smooth 2 rfl x]
  push_cast
  ring

lemma cdot_flatK_eq_cdot_flatBv_mulSPsi {ν c : ℝ} (tr : B0140.TrainSol ν c)
    (b gq gη : CProf) (Ψ : Coord → Fin 2 → ℝ) (x : Coord) :
    cdot (flatK tr b gq gη) Ψ x = cdot (flatBv tr b gq gη) (mulSPsi Ψ) x := by
  unfold cdot mulSPsi
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [flatK_eq_smul_flatBv]
  simp only [PiLp.smul_apply, smul_eq_mul]
  push_cast
  ring

lemma flatK_add {ν c : ℝ} (tr : B0140.TrainSol ν c)
    (b₁ gq₁ gη₁ b₂ gq₂ gη₂ : CProf) (x : Coord) :
    flatK tr (fun y => b₁ y + b₂ y) (fun y => gq₁ y + gq₂ y) (fun y => gη₁ y + gη₂ y) x =
      flatK tr b₁ gq₁ gη₁ x + flatK tr b₂ gq₂ gη₂ x := by
  ext i
  simp only [flatK, WithLp.ofLp_toLp, PiLp.add_apply]
  ring

lemma flatK_sub {ν c : ℝ} (tr : B0140.TrainSol ν c)
    (b₁ gq₁ gη₁ b₂ gq₂ gη₂ : CProf) (x : Coord) :
    flatK tr (fun y => b₁ y - b₂ y) (fun y => gq₁ y - gq₂ y) (fun y => gη₁ y - gη₂ y) x =
      flatK tr b₁ gq₁ gη₁ x - flatK tr b₂ gq₂ gη₂ x := by
  ext i
  simp only [flatK, WithLp.ofLp_toLp, PiLp.sub_apply]
  ring

lemma flatK_smul_complex {ν c : ℝ} (tr : B0140.TrainSol ν c) (a : ℂ)
    (b gq gη : CProf) (x : Coord) :
    flatK tr (fun y => a • b y) (fun y => a • gq y) (fun y => a • gη y) x =
      a • flatK tr b gq gη x := by
  ext i
  simp only [flatK, WithLp.ofLp_toLp, PiLp.smul_apply, smul_eq_mul]
  ring

/-! ## 3. Smooth integration by parts for `inletProf` -/

lemma contDiff_cutStream {p : Params} {d dm dp : ℝ} {lam : ℂ} {q : Planar.Profile}
    (hq : Planar.IsGrowingEigenpair lam q) (hreg : BgRegime p d dm dp)
    (hν1 : p.ν ≤ 1) (hmode : p.mode = q) (i : Fin 2) :
    ContDiff ℝ ∞ (p.cutStream i) := by
  obtain ⟨_, _, _, -, -, hper⟩ := frozenStreamBounds lam q hq 0
  have hνpos : 0 < p.ν := p.ν_pos
  have hc1 : 1 ≤ p.c := by
    rw [hreg.c_eq, one_le_inv₀ (by positivity)]
    nlinarith
  have hP : ContDiff ℝ ∞ (periodicStream q p.c) := (hper p.c hc1).1
  have hfro : ContDiff ℝ ∞ (p.frozenStream i) := inletCD_frozenStream hP hmode i
  unfold Params.cutStream
  exact ((contDiff_ageCutoff p.H).comp contDiff_fst).mul (hfro.comp contDiff_snd)

lemma inletE0_div_zero {p : Params} {d dm dp : ℝ} {lam : ℂ} {q : Planar.Profile}
    (hq : Planar.IsGrowingEigenpair lam q) (hreg : BgRegime p d dm dp)
    (hν1 : p.ν ≤ 1) (hmode : p.mode = q) (i : Fin 2) (x : Coord) :
    fderiv ℝ (fun y : Coord => cplx (inletE0 p i) y 0) x (cdir 1) +
      fderiv ℝ (fun y : Coord => cplx (inletE0 p i) y 1) x (cdir 2) = 0 := by
  have hE := F10Help.contDiff_inletE0 hq hreg hν1 hmode i
  have hcut := contDiff_cutStream hq hreg hν1 hmode i
  rw [F10Help.fderiv_cplx_comp hE 0 x (cdir 1), F10Help.fderiv_cplx_comp hE 1 x (cdir 2)]
  have h0 : (fun y : Coord => inletE0 p i y 0) =
      fun y : Coord => -(fderiv ℝ (p.cutStream i) y (cdir 2)) := by
    funext y
    simp [inletE0, Axi.dEta, Axi.dQ, Axi.m0, Axi.m1, cdir]
  have h1 : (fun y : Coord => inletE0 p i y 1) =
      fun y : Coord => fderiv ℝ (p.cutStream i) y (cdir 1) := by
    funext y
    simp [inletE0, Axi.dEta, Axi.dQ, Axi.m0, Axi.m1, cdir]
  have hp0 : fderiv ℝ (inletE0 p i) x (cdir 1) 0 =
      fderiv ℝ (fun y : Coord => inletE0 p i y 0) x (cdir 1) := by
    let L0 : Axi.Merid →L[ℝ] ℝ := EuclideanSpace.proj 0
    have hf : HasFDerivAt (L0 ∘ inletE0 p i) (L0.comp (fderiv ℝ (inletE0 p i) x)) x :=
      L0.hasFDerivAt.comp x (hE.differentiable (by simp) x).hasFDerivAt
    exact (congrArg (fun T => T (cdir 1)) hf.fderiv).symm
  have hp1 : fderiv ℝ (inletE0 p i) x (cdir 2) 1 =
      fderiv ℝ (fun y : Coord => inletE0 p i y 1) x (cdir 2) := by
    let L1 : Axi.Merid →L[ℝ] ℝ := EuclideanSpace.proj 1
    have hf : HasFDerivAt (L1 ∘ inletE0 p i) (L1.comp (fderiv ℝ (inletE0 p i) x)) x :=
      L1.hasFDerivAt.comp x (hE.differentiable (by simp) x).hasFDerivAt
    exact (congrArg (fun T => T (cdir 2)) hf.fderiv).symm
  rw [hp0, hp1, h0, h1]
  have hsymm : IsSymmSndFDerivAt ℝ (p.cutStream i) x :=
    hcut.contDiffAt.isSymmSndFDerivAt (by simp)
  have hA : fderiv ℝ (fun y : Coord => -(fderiv ℝ (p.cutStream i) y (cdir 2))) x (cdir 1) =
      -(fderiv ℝ (fderiv ℝ (p.cutStream i)) x (cdir 1) (cdir 2)) := by
    have hd : HasFDerivAt (fun y : Coord => -(fderiv ℝ (p.cutStream i) y (cdir 2))) _ x :=
      (planarTest_hasFDerivAt_partial hcut (cdir 2) x).neg
    rw [hd.fderiv]
    rfl
  have hB : fderiv ℝ (fun y : Coord => fderiv ℝ (p.cutStream i) y (cdir 1)) x (cdir 2) =
      fderiv ℝ (fderiv ℝ (p.cutStream i)) x (cdir 2) (cdir 1) := by
    rw [(planarTest_hasFDerivAt_partial hcut (cdir 1) x).fderiv]
    rfl
  rw [hA, hB, hsymm (cdir 1) (cdir 2)]
  push_cast
  ring

lemma integrable_cont_mul_compact {f g : Coord → ℂ}
    (hf : Continuous f) (hg : Continuous g) (hgc : HasCompactSupport g) :
    Integrable (fun x => f x * g x) :=
  (hf.mul hg).integrable_of_hasCompactSupport hgc.mul_left

lemma integrable_cont_mul_real_compact {f : Coord → ℂ} {g : Coord → ℝ}
    (hf : Continuous f) (hg : Continuous g) (hgc : HasCompactSupport g) :
    Integrable (fun x => f x * (g x : ℂ)) :=
  (hf.mul (Complex.continuous_ofReal.comp hg)).integrable_of_hasCompactSupport
    ((hgc.comp_left Complex.ofReal_zero).mul_left)

lemma integrable_real_compact_mul_cont {f : Coord → ℝ} {g : Coord → ℂ}
    (hf : Continuous f) (hfc : HasCompactSupport f) (hg : Continuous g) :
    Integrable (fun x => (f x : ℂ) * g x) :=
  ((Complex.continuous_ofReal.comp hf).mul hg).integrable_of_hasCompactSupport
    ((hfc.comp_left Complex.ofReal_zero).mul_right)

lemma cpd_continuous {ψ : Coord → ℝ} (hψ : ContDiff ℝ ∞ ψ) (j : Fin 3) :
    Continuous (fun x => cpd j ψ x) :=
  LapWeakQHelp.fderiv_dir_continuous hψ j

lemma cpd_compact {ψ : Coord → ℝ} (hψc : HasCompactSupport ψ) (j : Fin 3) :
    HasCompactSupport (fun x => cpd j ψ x) :=
  LapWeakQHelp.fderiv_dir_compact hψc j

lemma inletE0_solenoidal {p : Params} {d dm dp : ℝ} {lam : ℂ} {q : Planar.Profile}
    (hq : Planar.IsGrowingEigenpair lam q) (hreg : BgRegime p d dm dp)
    (hν1 : p.ν ≤ 1) (hmode : p.mode = q) (i : Fin 2)
    (φ : Coord → ℝ) (hφ : IsCoordTest φ) :
    Integrable (fun x => cplx (inletE0 p i) x 0 * (cpd 1 φ x : ℂ) +
        cplx (inletE0 p i) x 1 * (cpd 2 φ x : ℂ)) ∧
      ∫ x, (cplx (inletE0 p i) x 0 * (cpd 1 φ x : ℂ) +
        cplx (inletE0 p i) x 1 * (cpd 2 φ x : ℂ)) = 0 := by
  have hE := F10Help.contDiff_inletE0 hq hreg hν1 hmode i
  have hu : ∀ m : Fin 2, ContDiff ℝ ∞ (fun x : Coord => cplx (inletE0 p i) x m) := by
    intro m
    let L : Axi.Merid →L[ℝ] ℂ :=
      Complex.ofRealCLM.comp (EuclideanSpace.proj m : EuclideanSpace ℝ (Fin 2) →L[ℝ] ℝ)
    exact L.contDiff.comp hE
  have hI1 : Integrable (fun x => cplx (inletE0 p i) x 0 * (cpd 1 φ x : ℂ)) :=
    integrable_cont_mul_real_compact (hu 0).continuous
      (cpd_continuous hφ.smooth 1) (cpd_compact hφ.compact 1)
  have hI2 : Integrable (fun x => cplx (inletE0 p i) x 1 * (cpd 2 φ x : ℂ)) :=
    integrable_cont_mul_real_compact (hu 1).continuous
      (cpd_continuous hφ.smooth 2) (cpd_compact hφ.compact 2)
  refine ⟨hI1.add hI2, ?_⟩
  rw [integral_add hI1 hI2]
  unfold cpd
  rw [LapWeakQHelp.ibp_dir hφ.smooth hφ.compact _ (hu 0) 1,
    LapWeakQHelp.ibp_dir hφ.smooth hφ.compact _ (hu 1) 2]
  have hI1' : Integrable (fun x => (φ x : ℂ) *
      fderiv ℝ (fun y => cplx (inletE0 p i) y 0) x (cdir 1)) :=
    integrable_real_compact_mul_cont hφ.smooth.continuous hφ.compact
      (((hu 0).continuous_fderiv (by simp)).clm_apply continuous_const)
  have hI2' : Integrable (fun x => (φ x : ℂ) *
      fderiv ℝ (fun y => cplx (inletE0 p i) y 1) x (cdir 2)) :=
    integrable_real_compact_mul_cont hφ.smooth.continuous hφ.compact
      (((hu 1).continuous_fderiv (by simp)).clm_apply continuous_const)
  have hadd := integral_add hI1' hI2'
  have hzero : ∫ x, ((φ x : ℂ) * fderiv ℝ (fun y => cplx (inletE0 p i) y 0) x (cdir 1) +
      (φ x : ℂ) * fderiv ℝ (fun y => cplx (inletE0 p i) y 1) x (cdir 2)) = 0 := by
    refine integral_eq_zero_of_ae (Eventually.of_forall fun x => ?_)
    show (φ x : ℂ) * fderiv ℝ (fun y => cplx (inletE0 p i) y 0) x (cdir 1) +
      (φ x : ℂ) * fderiv ℝ (fun y => cplx (inletE0 p i) y 1) x (cdir 2) = 0
    rw [← mul_add, inletE0_div_zero hq hreg hν1 hmode i x, mul_zero]
  rw [hzero] at hadd
  linear_combination hadd

lemma inletProf_solenoidal {p : Params} {d dm dp : ℝ} {lam : ℂ} {q : Planar.Profile}
    (hq : Planar.IsGrowingEigenpair lam q) (hreg : BgRegime p d dm dp)
    (hν1 : p.ν ≤ 1) (hmode : p.mode = q) (α : E2)
    (φ : Coord → ℝ) (hφ : IsCoordTest φ) :
    Integrable (fun x => inletProf p α x 0 * (cpd 1 φ x : ℂ) +
        inletProf p α x 1 * (cpd 2 φ x : ℂ)) ∧
      ∫ x, (inletProf p α x 0 * (cpd 1 φ x : ℂ) +
        inletProf p α x 1 * (cpd 2 φ x : ℂ)) = 0 := by
  obtain ⟨hI0, hZ0⟩ := inletE0_solenoidal hq hreg hν1 hmode 0 φ hφ
  obtain ⟨hI1, hZ1⟩ := inletE0_solenoidal hq hreg hν1 hmode 1 φ hφ
  have hfun : (fun x : Coord => inletProf p α x 0 * (cpd 1 φ x : ℂ) +
      inletProf p α x 1 * (cpd 2 φ x : ℂ)) =
      fun x : Coord =>
        ((α 0 : ℝ) : ℂ) * (cplx (inletE0 p 0) x 0 * (cpd 1 φ x : ℂ) +
          cplx (inletE0 p 0) x 1 * (cpd 2 φ x : ℂ)) +
        ((α 1 : ℝ) : ℂ) * (cplx (inletE0 p 1) x 0 * (cpd 1 φ x : ℂ) +
          cplx (inletE0 p 1) x 1 * (cpd 2 φ x : ℂ)) := by
    funext x
    simp only [inletProf, Fin.sum_univ_two, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]
    ring
  rw [hfun]
  refine ⟨(hI0.const_mul _).add (hI1.const_mul _), ?_⟩
  rw [integral_add (hI0.const_mul _) (hI1.const_mul _),
    integral_const_mul, integral_const_mul, hZ0, hZ1]
  simp

lemma ibp_dir_twice {ψ : Coord → ℝ} (hψs : ContDiff ℝ ∞ ψ) (hψc : HasCompactSupport ψ)
    (u : Coord → ℂ) (hu : ContDiff ℝ ∞ u) (j : Fin 3) :
    ∫ x, u x * (cpd j (fun y => cpd j ψ y) x : ℂ) =
      ∫ x, (ψ x : ℂ) * fderiv ℝ (fun y => fderiv ℝ u y (cdir j)) x (cdir j) := by
  have hDs : ContDiff ℝ ∞ (fun y : Coord => cpd j ψ y) :=
    (hψs.fderiv_right (m := ∞) (by simp)).clm_apply contDiff_const
  have hDc : HasCompactSupport (fun y : Coord => cpd j ψ y) :=
    LapWeakQHelp.fderiv_dir_compact hψc j
  have hu' : ContDiff ℝ ∞ (fun y : Coord => fderiv ℝ u y (cdir j)) :=
    (hu.fderiv_right (m := ∞) (by simp)).clm_apply contDiff_const
  change ∫ x, u x * (fderiv ℝ (fun y => cpd j ψ y) x (cdir j) : ℂ) = _
  rw [LapWeakQHelp.ibp_dir hDs hDc u hu j]
  have hswap : (fun x : Coord => (cpd j ψ x : ℂ) * fderiv ℝ u x (cdir j)) =
      fun x : Coord => fderiv ℝ u x (cdir j) * (fderiv ℝ ψ x (cdir j) : ℂ) := by
    funext x; unfold cpd; ring
  rw [hswap, LapWeakQHelp.ibp_dir hψs hψc _ hu' j, neg_neg]

lemma fderiv_cplx_dS {F : Coord → Axi.Merid} (hF : ContDiff ℝ ∞ F) (m : Fin 2) (x : Coord) :
    fderiv ℝ (fun y : Coord => cplx F y m) x (cdir 0) = cplx (Axi.dS F) x m := by
  rw [F10Help.fderiv_cplx_comp hF m x (cdir 0)]
  simp [cplx, Axi.dS, cdir]

lemma fderiv2_cplx_dQ {F : Coord → Axi.Merid} (hF : ContDiff ℝ ∞ F) (m : Fin 2) (x : Coord) :
    fderiv ℝ (fun y : Coord => fderiv ℝ (fun z => cplx F z m) y (cdir 1)) x (cdir 1) =
      cplx (Axi.dQ (Axi.dQ F)) x m := by
  have h1 : (fun y : Coord => fderiv ℝ (fun z => cplx F z m) y (cdir 1)) =
      fun y : Coord => cplx (Axi.dQ F) y m := by
    funext y
    rw [F10Help.fderiv_cplx_comp hF m y (cdir 1)]
    simp [cplx, Axi.dQ, cdir]
  have hdQ : ContDiff ℝ ∞ (Axi.dQ F) := by
    unfold Axi.dQ
    exact (hF.fderiv_right (m := ∞) (by simp)).clm_apply contDiff_const
  rw [h1, F10Help.fderiv_cplx_comp hdQ m x (cdir 1)]
  simp [cplx, Axi.dQ, cdir]

lemma fderiv2_cplx_dEta {F : Coord → Axi.Merid} (hF : ContDiff ℝ ∞ F) (m : Fin 2) (x : Coord) :
    fderiv ℝ (fun y : Coord => fderiv ℝ (fun z => cplx F z m) y (cdir 2)) x (cdir 2) =
      cplx (Axi.dEta (Axi.dEta F)) x m := by
  have h1 : (fun y : Coord => fderiv ℝ (fun z => cplx F z m) y (cdir 2)) =
      fun y : Coord => cplx (Axi.dEta F) y m := by
    funext y
    rw [F10Help.fderiv_cplx_comp hF m y (cdir 2)]
    simp [cplx, Axi.dEta, cdir]
  have hdE : ContDiff ℝ ∞ (Axi.dEta F) := by
    unfold Axi.dEta
    exact (hF.fderiv_right (m := ∞) (by simp)).clm_apply contDiff_const
  rw [h1, F10Help.fderiv_cplx_comp hdE m x (cdir 2)]
  simp [cplx, Axi.dEta, cdir]

lemma contDiff_meridTranspose (ν : ℝ) {Ψ : Coord → Fin 2 → ℝ}
    (hΨ : IsPlanarSolTest Ψ) (m : Fin 2) :
    ContDiff ℝ ∞ (fun x : Coord => meridTranspose ν Ψ x m) := by
  unfold meridTranspose cpd
  have hs := (hΨ.smooth m).smooth
  have h0 : ContDiff ℝ ∞ (fun x : Coord => fderiv ℝ (fun y => Ψ y m) x (cdir 0)) :=
    (hs.fderiv_right (m := ∞) (by simp)).clm_apply contDiff_const
  have h1a : ContDiff ℝ ∞ (fun x : Coord => fderiv ℝ (fun y => Ψ y m) x (cdir 1)) :=
    (hs.fderiv_right (m := ∞) (by simp)).clm_apply contDiff_const
  have h1 : ContDiff ℝ ∞
      (fun x : Coord => fderiv ℝ (fun y => fderiv ℝ (fun z => Ψ z m) y (cdir 1)) x (cdir 1)) :=
    (h1a.fderiv_right (m := ∞) (by simp)).clm_apply contDiff_const
  have h2a : ContDiff ℝ ∞ (fun x : Coord => fderiv ℝ (fun y => Ψ y m) x (cdir 2)) :=
    (hs.fderiv_right (m := ∞) (by simp)).clm_apply contDiff_const
  have h2 : ContDiff ℝ ∞
      (fun x : Coord => fderiv ℝ (fun y => fderiv ℝ (fun z => Ψ z m) y (cdir 2)) x (cdir 2)) :=
    (h2a.fderiv_right (m := ∞) (by simp)).clm_apply contDiff_const
  exact ((Complex.ofRealCLM.contDiff.comp h0).neg).sub
    (Complex.ofRealCLM.contDiff.comp (contDiff_const.mul (h1.add h2)))

lemma hasCompactSupport_meridTranspose (ν : ℝ) {Ψ : Coord → Fin 2 → ℝ}
    (hΨ : IsPlanarSolTest Ψ) (m : Fin 2) :
    HasCompactSupport (fun x : Coord => meridTranspose ν Ψ x m) := by
  refine HasCompactSupport.of_support_subset_isCompact (hΨ.smooth m).compact ?_
  intro x hx
  by_contra hnot
  have hc0 : cpd 0 (fun y => Ψ y m) x = 0 :=
    image_eq_zero_of_notMem_tsupport
      (fun h => hnot (tsupport_fderiv_apply_subset (𝕜 := ℝ) (cdir 0) h))
  have hc1 : cpd 1 (fun y => cpd 1 (fun z => Ψ z m) y) x = 0 :=
    image_eq_zero_of_notMem_tsupport (fun h => hnot
      (tsupport_fderiv_apply_subset (𝕜 := ℝ) (cdir 1)
        (tsupport_fderiv_apply_subset (𝕜 := ℝ) (cdir 1) h)))
  have hc2 : cpd 2 (fun y => cpd 2 (fun z => Ψ z m) y) x = 0 :=
    image_eq_zero_of_notMem_tsupport (fun h => hnot
      (tsupport_fderiv_apply_subset (𝕜 := ℝ) (cdir 2)
        (tsupport_fderiv_apply_subset (𝕜 := ℝ) (cdir 2) h)))
  exact hx (by simp [meridTranspose, hc0, hc1, hc2])

lemma inletE0_flatTranspose_ibp {p : Params} {d dm dp : ℝ} {lam : ℂ} {q : Planar.Profile}
    (hq : Planar.IsGrowingEigenpair lam q) (hreg : BgRegime p d dm dp)
    (hν1 : p.ν ≤ 1) (hmode : p.mode = q) (i : Fin 2)
    (Ψ : Coord → Fin 2 → ℝ) (hΨ : IsPlanarSolTest Ψ) :
    Integrable (fun x => ∑ m : Fin 2, (-cplx (inletE0 p i) x m) * flatTranspose p.ν 0 Ψ x m) ∧
      Integrable (cdot (fun x => flatK p.train (cplx (inletE0 p i))
          (cplx (Axi.dQ (inletE0 p i))) (cplx (Axi.dEta (inletE0 p i))) x -
        flatColumn p i x) Ψ) ∧
      ∫ x, ∑ m : Fin 2, (-cplx (inletE0 p i) x m) * flatTranspose p.ν 0 Ψ x m =
        ∫ x, cdot (fun y => flatK p.train (cplx (inletE0 p i))
            (cplx (Axi.dQ (inletE0 p i))) (cplx (Axi.dEta (inletE0 p i))) y -
          flatColumn p i y) Ψ x := by
  have hE := F10Help.contDiff_inletE0 hq hreg hν1 hmode i
  have hu : ∀ m : Fin 2, ContDiff ℝ ∞ (fun x : Coord => cplx (inletE0 p i) x m) := by
    intro m
    let L : Axi.Merid →L[ℝ] ℂ :=
      Complex.ofRealCLM.comp (EuclideanSpace.proj m : EuclideanSpace ℝ (Fin 2) →L[ℝ] ℝ)
    exact L.contDiff.comp hE
  let Ψs := mulSPsi Ψ
  have hΨs : IsPlanarSolTest Ψs := isPlanarSolTest_mulSPsi hΨ
  have hIL : ∀ m : Fin 2, Integrable (fun x =>
      (-cplx (inletE0 p i) x m) * flatTranspose p.ν 0 Ψ x m) := by
    intro m
    have heq : (fun x => (-cplx (inletE0 p i) x m) * flatTranspose p.ν 0 Ψ x m) =
        fun x => (-cplx (inletE0 p i) x m) * meridTranspose p.ν Ψs x m := by
      funext x
      rw [flatTranspose_zero_eq_meridTranspose_mulSPsi p.ν hΨ x m]
    rw [heq]
    exact integrable_cont_mul_compact (hu m).continuous.neg
      (contDiff_meridTranspose p.ν hΨs m).continuous
      (hasCompactSupport_meridTranspose p.ν hΨs m)
  have hdiff_eq : ∀ y : Coord,
      flatK p.train (cplx (inletE0 p i)) (cplx (Axi.dQ (inletE0 p i)))
          (cplx (Axi.dEta (inletE0 p i))) y - flatColumn p i y =
        -((y.1 : ℂ) • cplx (fun z => Axi.dS (inletE0 p i) z -
          p.ν • (Axi.dQ (Axi.dQ (inletE0 p i)) z + Axi.dEta (Axi.dEta (inletE0 p i)) z)) y) := by
    intro y
    simp only [flatColumn]
    abel
  have hL_cont : Continuous (fun z : Coord => Axi.dS (inletE0 p i) z -
      p.ν • (Axi.dQ (Axi.dQ (inletE0 p i)) z + Axi.dEta (Axi.dEta (inletE0 p i)) z)) := by
    have hdS : ContDiff ℝ ∞ (Axi.dS (inletE0 p i)) :=
      (hE.fderiv_right (m := ∞) (by simp)).clm_apply contDiff_const
    have hdQ1 : ContDiff ℝ ∞ (Axi.dQ (inletE0 p i)) :=
      (hE.fderiv_right (m := ∞) (by simp)).clm_apply contDiff_const
    have hdQ2 : ContDiff ℝ ∞ (Axi.dQ (Axi.dQ (inletE0 p i))) :=
      (hdQ1.fderiv_right (m := ∞) (by simp)).clm_apply contDiff_const
    have hdE1 : ContDiff ℝ ∞ (Axi.dEta (inletE0 p i)) :=
      (hE.fderiv_right (m := ∞) (by simp)).clm_apply contDiff_const
    have hdE2 : ContDiff ℝ ∞ (Axi.dEta (Axi.dEta (inletE0 p i))) :=
      (hdE1.fderiv_right (m := ∞) (by simp)).clm_apply contDiff_const
    exact hdS.continuous.sub ((hdQ2.continuous.add hdE2.continuous).const_smul p.ν)
  have hIR_m : ∀ m : Fin 2, Integrable (fun x : Coord =>
      (-((x.1 : ℂ) * cplx (fun z => Axi.dS (inletE0 p i) z -
        p.ν • (Axi.dQ (Axi.dQ (inletE0 p i)) z + Axi.dEta (Axi.dEta (inletE0 p i)) z)) x m)) *
        (Ψ x m : ℂ)) := by
    intro m
    let Lm : Axi.Merid →L[ℝ] ℂ :=
      Complex.ofRealCLM.comp (EuclideanSpace.proj m : EuclideanSpace ℝ (Fin 2) →L[ℝ] ℝ)
    have hcm : Continuous (fun x : Coord =>
        cplx (fun z => Axi.dS (inletE0 p i) z -
          p.ν • (Axi.dQ (Axi.dQ (inletE0 p i)) z + Axi.dEta (Axi.dEta (inletE0 p i)) z)) x m) :=
      Lm.continuous.comp hL_cont
    exact integrable_cont_mul_real_compact
      (((Complex.continuous_ofReal.comp continuous_fst).mul hcm).neg)
      (hΨ.smooth m).smooth.continuous (hΨ.smooth m).compact
  have heqR : cdot (fun y => flatK p.train (cplx (inletE0 p i))
      (cplx (Axi.dQ (inletE0 p i))) (cplx (Axi.dEta (inletE0 p i))) y -
      flatColumn p i y) Ψ =
      fun x => ∑ m : Fin 2,
        (-((x.1 : ℂ) * cplx (fun z => Axi.dS (inletE0 p i) z -
          p.ν • (Axi.dQ (Axi.dQ (inletE0 p i)) z + Axi.dEta (Axi.dEta (inletE0 p i)) z)) x m)) *
          (Ψ x m : ℂ) := by
    funext x
    unfold cdot
    refine Finset.sum_congr rfl fun m _ => ?_
    dsimp only
    rw [hdiff_eq x]
    simp only [PiLp.neg_apply, PiLp.smul_apply, smul_eq_mul]
  have hIR : Integrable (cdot (fun x => flatK p.train (cplx (inletE0 p i))
      (cplx (Axi.dQ (inletE0 p i))) (cplx (Axi.dEta (inletE0 p i))) x -
      flatColumn p i x) Ψ) := by
    rw [heqR]
    exact integrable_finsetSum _ fun m _ => hIR_m m
  refine ⟨integrable_finsetSum _ fun m _ => hIL m, hIR, ?_⟩
  have hm_eq : ∀ m : Fin 2,
      ∫ x, (-cplx (inletE0 p i) x m) * flatTranspose p.ν 0 Ψ x m =
        ∫ x, (-((x.1 : ℂ) * cplx (fun z => Axi.dS (inletE0 p i) z -
          p.ν • (Axi.dQ (Axi.dQ (inletE0 p i)) z + Axi.dEta (Axi.dEta (inletE0 p i)) z)) x m)) *
            (Ψ x m : ℂ) := by
    intro m
    have hψs := (hΨs.smooth m).smooth
    have hψc := (hΨs.smooth m).compact
    have hI_s : Integrable (fun x => cplx (inletE0 p i) x m * (cpd 0 (fun y => Ψs y m) x : ℂ)) :=
      integrable_cont_mul_real_compact (hu m).continuous
        (cpd_continuous hψs 0) (cpd_compact hψc 0)
    have hI_q : Integrable (fun x => cplx (inletE0 p i) x m *
        (cpd 1 (fun y => cpd 1 (fun z => Ψs z m) y) x : ℂ)) := by
      have h1s : ContDiff ℝ ∞ (fun y => cpd 1 (fun z => Ψs z m) y) :=
        (hψs.fderiv_right (m := ∞) (by simp)).clm_apply contDiff_const
      have h1c : HasCompactSupport (fun y => cpd 1 (fun z => Ψs z m) y) :=
        cpd_compact hψc 1
      exact integrable_cont_mul_real_compact (hu m).continuous
        (cpd_continuous h1s 1) (cpd_compact h1c 1)
    have hI_e : Integrable (fun x => cplx (inletE0 p i) x m *
        (cpd 2 (fun y => cpd 2 (fun z => Ψs z m) y) x : ℂ)) := by
      have h2s : ContDiff ℝ ∞ (fun y => cpd 2 (fun z => Ψs z m) y) :=
        (hψs.fderiv_right (m := ∞) (by simp)).clm_apply contDiff_const
      have h2c : HasCompactSupport (fun y => cpd 2 (fun z => Ψs z m) y) :=
        cpd_compact hψc 2
      exact integrable_cont_mul_real_compact (hu m).continuous
        (cpd_continuous h2s 2) (cpd_compact h2c 2)
    have hI_qe : Integrable (fun x =>
        cplx (inletE0 p i) x m * (cpd 1 (fun y => cpd 1 (fun z => Ψs z m) y) x : ℂ) +
          cplx (inletE0 p i) x m * (cpd 2 (fun y => cpd 2 (fun z => Ψs z m) y) x : ℂ)) :=
      hI_q.add hI_e
    have hI_νqe : Integrable (fun x =>
        (p.ν : ℂ) * (cplx (inletE0 p i) x m *
          (cpd 1 (fun y => cpd 1 (fun z => Ψs z m) y) x : ℂ) +
          cplx (inletE0 p i) x m *
          (cpd 2 (fun y => cpd 2 (fun z => Ψs z m) y) x : ℂ))) :=
      hI_qe.const_mul _
    have hsplitL : (fun x => (-cplx (inletE0 p i) x m) * flatTranspose p.ν 0 Ψ x m) =
        fun x => cplx (inletE0 p i) x m * (cpd 0 (fun y => Ψs y m) x : ℂ) +
          (p.ν : ℂ) * (cplx (inletE0 p i) x m *
            (cpd 1 (fun y => cpd 1 (fun z => Ψs z m) y) x : ℂ) +
            cplx (inletE0 p i) x m *
            (cpd 2 (fun y => cpd 2 (fun z => Ψs z m) y) x : ℂ)) := by
      funext x
      rw [flatTranspose_zero_eq_meridTranspose_mulSPsi p.ν hΨ x m]
      unfold meridTranspose
      push_cast
      ring
    have hLHS : ∫ x, (-cplx (inletE0 p i) x m) * flatTranspose p.ν 0 Ψ x m =
        (∫ x, cplx (inletE0 p i) x m * (cpd 0 (fun y => Ψs y m) x : ℂ)) +
          (p.ν : ℂ) * ((∫ x, cplx (inletE0 p i) x m *
              (cpd 1 (fun y => cpd 1 (fun z => Ψs z m) y) x : ℂ)) +
            ∫ x, cplx (inletE0 p i) x m *
              (cpd 2 (fun y => cpd 2 (fun z => Ψs z m) y) x : ℂ)) := by
      rw [hsplitL, integral_add hI_s hI_νqe, integral_const_mul, integral_add hI_q hI_e]
    have hibp0 : ∫ x, cplx (inletE0 p i) x m * (cpd 0 (fun y => Ψs y m) x : ℂ) =
        -∫ x, (Ψs x m : ℂ) * cplx (Axi.dS (inletE0 p i)) x m := by
      unfold cpd
      rw [LapWeakQHelp.ibp_dir hψs hψc _ (hu m) 0]
      congr 1; congr 1; funext x
      rw [fderiv_cplx_dS hE m x]
    have hibp1 : ∫ x, cplx (inletE0 p i) x m *
        (cpd 1 (fun y => cpd 1 (fun z => Ψs z m) y) x : ℂ) =
        ∫ x, (Ψs x m : ℂ) * cplx (Axi.dQ (Axi.dQ (inletE0 p i))) x m := by
      rw [ibp_dir_twice hψs hψc _ (hu m) 1]
      congr 1; funext x
      rw [fderiv2_cplx_dQ hE m x]
    have hibp2 : ∫ x, cplx (inletE0 p i) x m *
        (cpd 2 (fun y => cpd 2 (fun z => Ψs z m) y) x : ℂ) =
        ∫ x, (Ψs x m : ℂ) * cplx (Axi.dEta (Axi.dEta (inletE0 p i))) x m := by
      rw [ibp_dir_twice hψs hψc _ (hu m) 2]
      congr 1; funext x
      rw [fderiv2_cplx_dEta hE m x]
    let Lm : Axi.Merid →L[ℝ] ℂ :=
      Complex.ofRealCLM.comp (EuclideanSpace.proj m : EuclideanSpace ℝ (Fin 2) →L[ℝ] ℝ)
    have hdS_cd : ContDiff ℝ ∞ (Axi.dS (inletE0 p i)) :=
      (hE.fderiv_right (m := ∞) (by simp)).clm_apply contDiff_const
    have hdQ1_cd : ContDiff ℝ ∞ (Axi.dQ (inletE0 p i)) :=
      (hE.fderiv_right (m := ∞) (by simp)).clm_apply contDiff_const
    have hdQ2_cd : ContDiff ℝ ∞ (Axi.dQ (Axi.dQ (inletE0 p i))) :=
      (hdQ1_cd.fderiv_right (m := ∞) (by simp)).clm_apply contDiff_const
    have hdE1_cd : ContDiff ℝ ∞ (Axi.dEta (inletE0 p i)) :=
      (hE.fderiv_right (m := ∞) (by simp)).clm_apply contDiff_const
    have hdE2_cd : ContDiff ℝ ∞ (Axi.dEta (Axi.dEta (inletE0 p i))) :=
      (hdE1_cd.fderiv_right (m := ∞) (by simp)).clm_apply contDiff_const
    have hJ0 : Integrable (fun x => (Ψs x m : ℂ) * cplx (Axi.dS (inletE0 p i)) x m) :=
      integrable_real_compact_mul_cont hψs.continuous hψc
        (Lm.continuous.comp hdS_cd.continuous)
    have hJ1 : Integrable (fun x => (Ψs x m : ℂ) * cplx (Axi.dQ (Axi.dQ (inletE0 p i))) x m) :=
      integrable_real_compact_mul_cont hψs.continuous hψc
        (Lm.continuous.comp hdQ2_cd.continuous)
    have hJ2 : Integrable (fun x => (Ψs x m : ℂ) * cplx (Axi.dEta (Axi.dEta (inletE0 p i))) x m) :=
      integrable_real_compact_mul_cont hψs.continuous hψc
        (Lm.continuous.comp hdE2_cd.continuous)
    have hJ0n : Integrable (fun x => -((Ψs x m : ℂ) * cplx (Axi.dS (inletE0 p i)) x m)) :=
      hJ0.neg
    have hJ12 : Integrable (fun x =>
        (Ψs x m : ℂ) * cplx (Axi.dQ (Axi.dQ (inletE0 p i))) x m +
          (Ψs x m : ℂ) * cplx (Axi.dEta (Axi.dEta (inletE0 p i))) x m) :=
      hJ1.add hJ2
    have hJν : Integrable (fun x =>
        (p.ν : ℂ) * ((Ψs x m : ℂ) * cplx (Axi.dQ (Axi.dQ (inletE0 p i))) x m +
          (Ψs x m : ℂ) * cplx (Axi.dEta (Axi.dEta (inletE0 p i))) x m)) :=
      hJ12.const_mul _
    have hsplitR : (fun x : Coord =>
        (-((x.1 : ℂ) * cplx (fun z => Axi.dS (inletE0 p i) z -
          p.ν • (Axi.dQ (Axi.dQ (inletE0 p i)) z + Axi.dEta (Axi.dEta (inletE0 p i)) z)) x m)) *
            (Ψ x m : ℂ)) =
        fun x : Coord =>
          -((Ψs x m : ℂ) * cplx (Axi.dS (inletE0 p i)) x m) +
            (p.ν : ℂ) * ((Ψs x m : ℂ) * cplx (Axi.dQ (Axi.dQ (inletE0 p i))) x m +
              (Ψs x m : ℂ) * cplx (Axi.dEta (Axi.dEta (inletE0 p i))) x m) := by
      funext x
      simp only [Ψs, mulSPsi, cplx, WithLp.ofLp_toLp, PiLp.sub_apply, PiLp.smul_apply,
        PiLp.add_apply, smul_eq_mul]
      push_cast
      ring
    have hRHS : ∫ x, (-((x.1 : ℂ) * cplx (fun z => Axi.dS (inletE0 p i) z -
          p.ν • (Axi.dQ (Axi.dQ (inletE0 p i)) z + Axi.dEta (Axi.dEta (inletE0 p i)) z)) x m)) *
            (Ψ x m : ℂ) =
        (-∫ x, (Ψs x m : ℂ) * cplx (Axi.dS (inletE0 p i)) x m) +
          (p.ν : ℂ) * ((∫ x, (Ψs x m : ℂ) * cplx (Axi.dQ (Axi.dQ (inletE0 p i))) x m) +
            ∫ x, (Ψs x m : ℂ) * cplx (Axi.dEta (Axi.dEta (inletE0 p i))) x m) := by
      rw [hsplitR, integral_add hJ0n hJν, integral_neg, integral_const_mul, integral_add hJ1 hJ2]
    rw [hLHS, hibp0, hibp1, hibp2, hRHS]
  rw [integral_finsetSum _ fun m _ => hIL m, heqR, integral_finsetSum _ fun m _ => hIR_m m]
  exact Finset.sum_congr rfl fun m _ => hm_eq m

lemma inletProf_flatTranspose_ibp {p : Params} {d dm dp : ℝ} {lam : ℂ} {q : Planar.Profile}
    (hq : Planar.IsGrowingEigenpair lam q) (hreg : BgRegime p d dm dp)
    (hν1 : p.ν ≤ 1) (hmode : p.mode = q) (α : E2)
    (Ψ : Coord → Fin 2 → ℝ) (hΨ : IsPlanarSolTest Ψ) :
    Integrable (fun x => ∑ m : Fin 2, (-inletProf p α x m) * flatTranspose p.ν 0 Ψ x m) ∧
      Integrable (cdot (fun y =>
        flatK p.train (inletProf p α) (inletProfQ p α) (inletProfEta p α) y -
          ∑ i : Fin 2, ((α i : ℝ) : ℂ) • flatColumn p i y) Ψ) ∧
      ∫ x, ∑ m : Fin 2, (-inletProf p α x m) * flatTranspose p.ν 0 Ψ x m =
        ∫ x, cdot (fun y =>
          flatK p.train (inletProf p α) (inletProfQ p α) (inletProfEta p α) y -
            ∑ i : Fin 2, ((α i : ℝ) : ℂ) • flatColumn p i y) Ψ x := by
  obtain ⟨hIL0, hIR0, hEq0⟩ := inletE0_flatTranspose_ibp hq hreg hν1 hmode 0 Ψ hΨ
  obtain ⟨hIL1, hIR1, hEq1⟩ := inletE0_flatTranspose_ibp hq hreg hν1 hmode 1 Ψ hΨ
  have hK_lin : ∀ y : Coord,
      flatK p.train (inletProf p α) (inletProfQ p α) (inletProfEta p α) y -
          ∑ i : Fin 2, ((α i : ℝ) : ℂ) • flatColumn p i y =
        ((α 0 : ℝ) : ℂ) • (flatK p.train (cplx (inletE0 p 0))
            (cplx (Axi.dQ (inletE0 p 0))) (cplx (Axi.dEta (inletE0 p 0))) y -
          flatColumn p 0 y) +
        ((α 1 : ℝ) : ℂ) • (flatK p.train (cplx (inletE0 p 1))
            (cplx (Axi.dQ (inletE0 p 1))) (cplx (Axi.dEta (inletE0 p 1))) y -
          flatColumn p 1 y) := by
    intro y
    have heP : inletProf p α = fun z =>
        ((α 0 : ℝ) : ℂ) • cplx (inletE0 p 0) z + ((α 1 : ℝ) : ℂ) • cplx (inletE0 p 1) z := by
      ext z m; simp [inletProf, Fin.sum_univ_two]
    have heQ : inletProfQ p α = fun z =>
        ((α 0 : ℝ) : ℂ) • cplx (Axi.dQ (inletE0 p 0)) z +
          ((α 1 : ℝ) : ℂ) • cplx (Axi.dQ (inletE0 p 1)) z := by
      ext z m; simp [inletProfQ, Fin.sum_univ_two]
    have heE : inletProfEta p α = fun z =>
        ((α 0 : ℝ) : ℂ) • cplx (Axi.dEta (inletE0 p 0)) z +
          ((α 1 : ℝ) : ℂ) • cplx (Axi.dEta (inletE0 p 1)) z := by
      ext z m; simp [inletProfEta, Fin.sum_univ_two]
    rw [heP, heQ, heE, flatK_add, flatK_smul_complex, flatK_smul_complex, Fin.sum_univ_two]
    ext m
    simp only [PiLp.sub_apply, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]
    ring
  have hfunL : (fun x : Coord => ∑ m : Fin 2, (-inletProf p α x m) * flatTranspose p.ν 0 Ψ x m) =
      fun x : Coord =>
        ((α 0 : ℝ) : ℂ) * (∑ m : Fin 2, (-cplx (inletE0 p 0) x m) * flatTranspose p.ν 0 Ψ x m) +
        ((α 1 : ℝ) : ℂ) * (∑ m : Fin 2, (-cplx (inletE0 p 1) x m) * flatTranspose p.ν 0 Ψ x m) := by
    funext x
    simp only [inletProf, Fin.sum_univ_two, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]
    ring
  have hfunR : cdot (fun y =>
      flatK p.train (inletProf p α) (inletProfQ p α) (inletProfEta p α) y -
        ∑ i : Fin 2, ((α i : ℝ) : ℂ) • flatColumn p i y) Ψ =
      fun x : Coord =>
        ((α 0 : ℝ) : ℂ) * cdot (fun y => flatK p.train (cplx (inletE0 p 0))
            (cplx (Axi.dQ (inletE0 p 0))) (cplx (Axi.dEta (inletE0 p 0))) y -
          flatColumn p 0 y) Ψ x +
        ((α 1 : ℝ) : ℂ) * cdot (fun y => flatK p.train (cplx (inletE0 p 1))
            (cplx (Axi.dQ (inletE0 p 1))) (cplx (Axi.dEta (inletE0 p 1))) y -
          flatColumn p 1 y) Ψ x := by
    funext x
    unfold cdot
    dsimp only
    rw [hK_lin x]
    simp only [Fin.sum_univ_two, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]
    ring
  rw [hfunL, hfunR]
  have hIL0c : Integrable (fun x : Coord =>
      ((α 0 : ℝ) : ℂ) * ∑ m : Fin 2, (-cplx (inletE0 p 0) x m) * flatTranspose p.ν 0 Ψ x m) :=
    hIL0.const_mul _
  have hIL1c : Integrable (fun x : Coord =>
      ((α 1 : ℝ) : ℂ) * ∑ m : Fin 2, (-cplx (inletE0 p 1) x m) * flatTranspose p.ν 0 Ψ x m) :=
    hIL1.const_mul _
  have hIR0c : Integrable (fun x : Coord =>
      ((α 0 : ℝ) : ℂ) * cdot (fun y => flatK p.train (cplx (inletE0 p 0))
          (cplx (Axi.dQ (inletE0 p 0))) (cplx (Axi.dEta (inletE0 p 0))) y -
        flatColumn p 0 y) Ψ x) :=
    hIR0.const_mul _
  have hIR1c : Integrable (fun x : Coord =>
      ((α 1 : ℝ) : ℂ) * cdot (fun y => flatK p.train (cplx (inletE0 p 1))
          (cplx (Axi.dQ (inletE0 p 1))) (cplx (Axi.dEta (inletE0 p 1))) y -
        flatColumn p 1 y) Ψ x) :=
    hIR1.const_mul _
  refine ⟨hIL0c.add hIL1c, hIR0c.add hIR1c, ?_⟩
  rw [integral_add hIL0c hIL1c, integral_add hIR0c hIR1c,
    integral_const_mul, integral_const_mul, integral_const_mul, integral_const_mul,
    hEq0, hEq1]

end GlobalIdHelp

/-! ## 4. Unconditional assembly of `IsFlatResponse` (`flatReconstruction_isFlatResponse`) -/

/-- **Unconditional weak flat-response identity for `PartII-b:F9/3`**:
if `b0` is a flat response to `toProf p.c F`, `g` is the projected body source of `b0`,
`z` solves `IsGlobalMeridionalCorrection p g z zq zη α`, and `toProf p.c f` agrees
`hMeas p.c bgp`-a.e. with `toProf p.c F - flatK(b0 + z - Eα) - ∑ α_i flatColumn p i` (with both
sides `c`-periodic in `q`), then `b0 + z - inletProf p α` satisfies
`IsFlatResponse p.ν 0 (toProf p.c f)`. -/
theorem flatReconstruction_isFlatResponse
    {p : Params} {d dm dp : ℝ} {lam : ℂ} {q : Planar.Profile}
    (hq : Planar.IsGrowingEigenpair lam q) (hreg : BgRegime p d dm dp)
    (hν1 : p.ν ≤ 1) (hmode : p.mode = q)
    {F f : HpR p.c} {α : E2}
    {b0 b0q b0η g z zq zη : CProf}
    (hb0_resp : IsFlatResponse p.ν 0 (toProf p.c F) b0)
    (hbody : IsBodySource p.train b0 b0q b0η g)
    (hmc : IsGlobalMeridionalCorrection p g z zq zη α)
    (hRHS_per : QPeriodic p.c (fun x =>
      toProf p.c F x -
        flatK p.train (fun y => b0 y + z y - inletProf p α y)
          (fun y => b0q y + zq y - inletProfQ p α y)
          (fun y => b0η y + zη y - inletProfEta p α y) x -
        ∑ i : Fin 2, ((α i : ℝ) : ℂ) • flatColumn p i x))
    (hf_ae : toProf p.c f =ᵐ[hMeas p.c bgp] fun x =>
      toProf p.c F x -
        flatK p.train (fun y => b0 y + z y - inletProf p α y)
          (fun y => b0q y + zq y - inletProfQ p α y)
          (fun y => b0η y + zη y - inletProfEta p α y) x -
        ∑ i : Fin 2, ((α i : ℝ) : ℂ) • flatColumn p i x) :
    IsFlatResponse p.ν 0 (toProf p.c f) (fun x => b0 x + z x - inletProf p α x) := by
  have hc : 0 < p.c := p.c_pos
  refine ⟨fun φ hφ => ?_, fun Ψ hΨ => ?_⟩
  · obtain ⟨hIb0, hZb0⟩ := hb0_resp.solenoidal φ hφ
    obtain ⟨hIz, hZz⟩ := hmc.solenoidal φ hφ
    obtain ⟨hIe, hZe⟩ := GlobalIdHelp.inletProf_solenoidal hq hreg hν1 hmode α φ hφ
    have hIb0z : Integrable (fun x : Coord =>
        (b0 x 0 * (cpd 1 φ x : ℂ) + b0 x 1 * (cpd 2 φ x : ℂ)) +
          (z x 0 * (cpd 1 φ x : ℂ) + z x 1 * (cpd 2 φ x : ℂ))) :=
      hIb0.add hIz
    have hfun : (fun x : Coord =>
        (b0 x + z x - inletProf p α x) 0 * (cpd 1 φ x : ℂ) +
          (b0 x + z x - inletProf p α x) 1 * (cpd 2 φ x : ℂ)) =
        fun x : Coord =>
          (b0 x 0 * (cpd 1 φ x : ℂ) + b0 x 1 * (cpd 2 φ x : ℂ)) +
          (z x 0 * (cpd 1 φ x : ℂ) + z x 1 * (cpd 2 φ x : ℂ)) -
          (inletProf p α x 0 * (cpd 1 φ x : ℂ) + inletProf p α x 1 * (cpd 2 φ x : ℂ)) := by
      funext x
      simp only [PiLp.sub_apply, PiLp.add_apply]
      ring
    rw [hfun]
    refine ⟨hIb0z.sub hIe, ?_⟩
    rw [integral_sub hIb0z hIe, integral_add hIb0 hIz, hZb0, hZz, hZe]
    simp
  · let Ψs := GlobalIdHelp.mulSPsi Ψ
    have hΨs : IsPlanarSolTest Ψs := GlobalIdHelp.isPlanarSolTest_mulSPsi hΨ
    obtain ⟨hIb0_L, hIF_R, hEq_b0⟩ := hb0_resp.equation Ψ hΨ
    obtain ⟨hIz_L, hIBz, _hIg_mc, hEq_mc⟩ := hmc.equation Ψs hΨs
    obtain ⟨_hIg_bs, _hIBb0, hEq_bs⟩ := hbody.equation Ψs hΨs
    obtain ⟨hIe_L, hIe_R, hEq_e⟩ := GlobalIdHelp.inletProf_flatTranspose_ibp hq hreg hν1 hmode α Ψ hΨ
    have hz_tr : (fun x : Coord => ∑ i : Fin 2, z x i * flatTranspose p.ν 0 Ψ x i) =
        fun x : Coord => ∑ i : Fin 2, z x i * meridTranspose p.ν Ψs x i := by
      funext x
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [GlobalIdHelp.flatTranspose_zero_eq_meridTranspose_mulSPsi p.ν hΨ x i]
    have hIz_L' : Integrable (fun x : Coord => ∑ i : Fin 2, z x i * flatTranspose p.ν 0 Ψ x i) := by
      rwa [hz_tr]
    have hIKb0 : Integrable (cdot (flatK p.train b0 b0q b0η) Ψ) := by
      have heq : cdot (flatK p.train b0 b0q b0η) Ψ = cdot (flatBv p.train b0 b0q b0η) Ψs := by
        funext x; exact GlobalIdHelp.cdot_flatK_eq_cdot_flatBv_mulSPsi p.train b0 b0q b0η Ψ x
      rwa [heq]
    have hIKz : Integrable (cdot (flatK p.train z zq zη) Ψ) := by
      have heq : cdot (flatK p.train z zq zη) Ψ = cdot (flatBv p.train z zq zη) Ψs := by
        funext x; exact GlobalIdHelp.cdot_flatK_eq_cdot_flatBv_mulSPsi p.train z zq zη Ψ x
      rwa [heq]
    have hEq_z : ∫ x, ∑ i : Fin 2, z x i * flatTranspose p.ν 0 Ψ x i =
        -(∫ x, cdot (flatK p.train b0 b0q b0η) Ψ x) -
          ∫ x, cdot (flatK p.train z zq zη) Ψ x := by
      rw [hz_tr]
      have h1 := (integral_add hIz_L hIBz).symm
      rw [hEq_mc, hEq_bs] at h1
      have hKb0_eq : ∫ x, cdot (flatK p.train b0 b0q b0η) Ψ x =
          ∫ x, cdot (flatBv p.train b0 b0q b0η) Ψs x := by
        congr 1; funext x
        exact GlobalIdHelp.cdot_flatK_eq_cdot_flatBv_mulSPsi p.train b0 b0q b0η Ψ x
      have hKz_eq : ∫ x, cdot (flatK p.train z zq zη) Ψ x =
          ∫ x, cdot (flatBv p.train z zq zη) Ψs x := by
        congr 1; funext x
        exact GlobalIdHelp.cdot_flatK_eq_cdot_flatBv_mulSPsi p.train z zq zη Ψ x
      rw [hKb0_eq, hKz_eq]
      linear_combination h1
    have hIb0z_L : Integrable (fun x : Coord =>
        (∑ i : Fin 2, b0 x i * flatTranspose p.ν 0 Ψ x i) +
          (∑ i : Fin 2, z x i * flatTranspose p.ν 0 Ψ x i)) :=
      hIb0_L.add hIz_L'
    have hL_tot : (fun x : Coord =>
        ∑ i : Fin 2, (b0 x + z x - inletProf p α x) i * flatTranspose p.ν 0 Ψ x i) =
        fun x : Coord =>
          ((∑ i : Fin 2, b0 x i * flatTranspose p.ν 0 Ψ x i) +
            (∑ i : Fin 2, z x i * flatTranspose p.ν 0 Ψ x i)) +
          (∑ i : Fin 2, (-inletProf p α x i) * flatTranspose p.ν 0 Ψ x i) := by
      funext x
      simp only [Fin.sum_univ_two, PiLp.sub_apply, PiLp.add_apply]
      ring
    let RHS : CProf := fun x =>
      toProf p.c F x -
        flatK p.train (fun y => b0 y + z y - inletProf p α y)
          (fun y => b0q y + zq y - inletProfQ p α y)
          (fun y => b0η y + zη y - inletProfEta p α y) x -
        ∑ i : Fin 2, ((α i : ℝ) : ℂ) • flatColumn p i x
    have hRHS_cdot : cdot RHS Ψ = fun x : Coord =>
        ((cdot (toProf p.c F) Ψ x - cdot (flatK p.train b0 b0q b0η) Ψ x) -
          cdot (flatK p.train z zq zη) Ψ x) +
          cdot (fun y =>
            flatK p.train (inletProf p α) (inletProfQ p α) (inletProfEta p α) y -
              ∑ i : Fin 2, ((α i : ℝ) : ℂ) • flatColumn p i y) Ψ x := by
      funext x
      have hK_split : flatK p.train (fun y => b0 y + z y - inletProf p α y)
          (fun y => b0q y + zq y - inletProfQ p α y)
          (fun y => b0η y + zη y - inletProfEta p α y) x =
          flatK p.train b0 b0q b0η x + flatK p.train z zq zη x -
            flatK p.train (inletProf p α) (inletProfQ p α) (inletProfEta p α) x := by
        have hsub := GlobalIdHelp.flatK_sub p.train (fun y => b0 y + z y) (fun y => b0q y + zq y)
          (fun y => b0η y + zη y) (inletProf p α) (inletProfQ p α) (inletProfEta p α) x
        have hadd := GlobalIdHelp.flatK_add p.train b0 b0q b0η z zq zη x
        rw [hsub, hadd]
      unfold cdot RHS
      dsimp only
      rw [hK_split]
      simp only [Fin.sum_univ_two, PiLp.sub_apply, PiLp.add_apply]
      ring
    have hIR1 : Integrable (fun x : Coord =>
        cdot (toProf p.c F) Ψ x - cdot (flatK p.train b0 b0q b0η) Ψ x) :=
      hIF_R.sub hIKb0
    have hIR2 : Integrable (fun x : Coord =>
        (cdot (toProf p.c F) Ψ x - cdot (flatK p.train b0 b0q b0η) Ψ x) -
          cdot (flatK p.train z zq zη) Ψ x) :=
      hIR1.sub hIKz
    have hIRHS : Integrable (cdot RHS Ψ) := by
      rw [hRHS_cdot]
      exact hIR2.add hIe_R
    have hf_vol : ∀ᵐ x : Coord, 0 < x.1 → toProf p.c f x = RHS x :=
      CongrHelp.ae_volume_of_ageμ hc (inHr_toProf hc f).periodic hRHS_per hf_ae
    have hf_cdot_ae : cdot (toProf p.c f) Ψ =ᵐ[volume] cdot RHS Ψ := by
      filter_upwards [hf_vol] with x hx
      by_cases hpos : 0 < x.1
      · simp only [cdot, hx hpos]
      · have h0 : Ψ x 0 = 0 := by
          by_contra hne
          exact hpos ((hΨ.smooth 0).supp (subset_tsupport (fun y => Ψ y 0) hne)).1
        have h1 : Ψ x 1 = 0 := by
          by_contra hne
          exact hpos ((hΨ.smooth 1).supp (subset_tsupport (fun y => Ψ y 1) hne)).1
        simp [cdot, Fin.sum_univ_two, h0, h1]
    refine ⟨?_, hIRHS.congr hf_cdot_ae.symm, ?_⟩
    · rw [hL_tot]
      exact hIb0z_L.add hIe_L
    · rw [hL_tot, integral_add hIb0z_L hIe_L, integral_add hIb0_L hIz_L',
        hEq_b0, hEq_z, hEq_e, integral_congr_ae hf_cdot_ae, hRHS_cdot,
        integral_add hIR2 hIe_R, integral_sub hIR1 hIKz, integral_sub hIF_R hIKb0]
      ring

/-! ## 5. Unconditional `InHr` and `InFlatClass` transfer from a.e. response equality -/

theorem qPeriodic_inletProf (p : Params) (α : E2) :
    QPeriodic p.c (inletProf p α) := by
  unfold QPeriodic
  filter_upwards [ae_restrict_mem (isOpen_lt continuous_const continuous_fst).measurableSet]
    with x (_hx : 0 < x.1)
  have hshift_add : ∀ y : Coord, qShift p.c y = y + (0, (p.c, 0)) := fun y => by
    ext <;> simp [qShift]
  have hqS : ∀ i : Fin 2, inletE0 p i (qShift p.c x) = inletE0 p i x := by
    intro i
    have hsh : ∀ y : Coord, p.cutStream i (qShift p.c y) = p.cutStream i y := by
      intro y
      rw [hshift_add]
      exact p.cutStream_add i y
    have hfun : (fun y : Coord => p.cutStream i (qShift p.c y)) = p.cutStream i := funext hsh
    have hfd : fderiv ℝ (p.cutStream i) (qShift p.c x) = fderiv ℝ (p.cutStream i) x := by
      have h1 : fderiv ℝ (fun y : Coord => p.cutStream i (qShift p.c y)) x =
          fderiv ℝ (p.cutStream i) x := by rw [hfun]
      have hfun2 : (fun y : Coord => p.cutStream i (qShift p.c y)) =
          fun y : Coord => p.cutStream i (y + (0, (p.c, 0))) := by
        funext y; rw [hshift_add]
      rw [hfun2, fderiv_comp_add_right] at h1
      rw [hshift_add]
      exact h1
    unfold inletE0 Axi.dEta Axi.dQ
    rw [hfd]
  unfold inletProf
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [cplx, hqS i]

theorem inHr_congr_ae {c r : ℝ} {b b' : CProf} (hb_per : QPeriodic c b)
    (hb' : InHr c r b') (h : b =ᵐ[hMeas c r] b') : InHr c r b :=
  { periodic := hb_per
    meas := hb'.meas.congr h.symm
    finite := by
      unfold hNorm
      rw [eLpNorm_congr_ae h]
      exact hb'.finite }

theorem inFlatClass_congr_ae {c r : ℝ} (hc : 0 < c) {b b' : CProf}
    (hb_per : QPeriodic c b) (hb' : InFlatClass c r b') (h : b =ᵐ[hMeas c r] b') :
    InFlatClass c r b := by
  have hae : ∀ᵐ x : Coord, 0 < x.1 → b x = b' x :=
    CongrHelp.ae_volume_of_ageμ hc hb_per hb'.inHr.periodic h
  obtain ⟨Sb, Qb, Eb, hS, hQ, hE, hSi, hQi, hEi⟩ := hb'.deriv
  refine ⟨inHr_congr_ae hb_per hb'.inHr h, Sb, Qb, Eb, ?_, ?_, ?_, hSi, hQi, hEi⟩
  · intro i
    exact CongrHelp.hasWeakFO_congr (by filter_upwards [hae] with x hx hp; rw [hx hp]) (hS i)
  · intro i
    exact CongrHelp.hasWeakFO_congr (by filter_upwards [hae] with x hx hp; rw [hx hp]) (hQ i)
  · intro i
    exact CongrHelp.hasWeakFO_congr (by filter_upwards [hae] with x hx hp; rw [hx hp]) (hE i)

/-- Once `b0 + z - inletProf p α =ᵐ[hMeas p.c bgp] b_f` holds for an `InFlatClass` profile `b_f`,
both `InHr p.c bgp (z - inletProf p α)` and `InFlatClass p.c bgp (b0 + z - inletProf p α)` follow
immediately. -/
theorem inHr_and_inFlatClass_of_ae_eq_response
    {p : Params} {α : E2} {b0 z b_f : CProf}
    (hb0 : InFlatClass p.c bgp b0)
    (hz_per : QPeriodic p.c z)
    (hbf : InFlatClass p.c bgp b_f)
    (hae : (fun x => b0 x + z x - inletProf p α x) =ᵐ[hMeas p.c bgp] b_f) :
    InHr p.c bgp (fun x => z x - inletProf p α x) ∧
      InFlatClass p.c bgp (fun x => b0 x + z x - inletProf p α x) := by
  have hc : 0 < p.c := p.c_pos
  have he_per : QPeriodic p.c (inletProf p α) := qPeriodic_inletProf p α
  have hz_sub_per : QPeriodic p.c (fun x => z x - inletProf p α x) := by
    filter_upwards [hz_per, he_per] with x hzx hex
    simp only [hzx, hex]
  have htot_per : QPeriodic p.c (fun x => b0 x + z x - inletProf p α x) := by
    filter_upwards [hb0.inHr.periodic, hz_per, he_per] with x hb0x hzx hex
    simp only [hb0x, hzx, hex]
  have hsub_ae : (fun x => z x - inletProf p α x) =ᵐ[hMeas p.c bgp] (b_f - b0) := by
    filter_upwards [hae] with x hx
    simp only [Pi.sub_apply, ← hx]
    abel
  exact ⟨inHr_congr_ae hz_sub_per (flatCls_inHr_sub hbf.inHr hb0.inHr) hsub_ae,
    inFlatClass_congr_ae hc htot_per hbf hae⟩

/-! ## 6. Concrete remaining sub-steps and conditional assembly of `FlatReconstructionIdentityStep` -/

/-- **Sub-step 1 (`FlatReconstructionLinearR0Step`)**:
real-part projection on `(b0Of F, b0qOf F, b0ηOf F, gOf F, zOf F, zqOf F, zηOf F)`,
polynomial `H_p` bound on `flatK p.train (cplx (inletE0 p i)) - flatColumn p i`, `hFI` bound on
`flatK p.train b0 b0q b0η`, and bounded linear operator construction
`R0 : HpR p.c →L[ℝ] RowSpace p.c` (`F ↦ (f, α)`) with `toProf p.c f =ᵐ ...`. -/
def FlatReconstructionLinearR0Step : Prop :=
  ∀ C_late : ℝ, 0 < C_late →
  ∀ (Sig : ℝ) (lam : ℂ) (q : Blueprint.Planar.Profile), 0 < Sig →
    Blueprint.Planar.IsGrowingEigenpair lam q →
  ∀ a' : ℝ, 0 < a' → a' < lam.re / (1 + Sig) ^ 2 →
  ∀ dm dp : ℝ, 0 < dm →
  ∀ (C_ge : ℝ) (_k_ge : ℕ) (C_ls : ℝ) (k_ls : ℕ) (C_fl : ℝ)
    (C_fi : ℝ) (k_fi : ℕ) (C_col : ℝ) (k_col : ℕ),
    0 < C_ge → 0 < C_ls → 0 < C_fl → 0 < C_fi → 0 < C_col →
    ∃ (C : ℝ) (k : ℕ) (ν₀ : ℝ), 0 < C ∧ 0 < ν₀ ∧ ν₀ ≤ 1 / 2 ∧
      ∀ (p : Params) (d : ℝ), BgRegime p d dm dp → p.ν ≤ ν₀ → p.ageCut = Sig → p.mode = q →
        (∀ F b0 : CProf, InHr p.c bgp F → InFlatClass p.c bgp b0 → IsFlatResponse p.ν 0 F b0 →
          ∃ b0q b0η : CProf,
            HasWeakVec vQ0 dZero b0 b0q ∧ HasWeakVec vEta dZero b0 b0η ∧
            InHr p.c bgp (flatK p.train b0 b0q b0η) ∧
            eLpNorm (flatK p.train b0 b0q b0η) (ENNReal.ofReal bgp)
                ((hMeas p.c bgp).restrict (Ioc 0 p.H ×ˢ univ)) ≤
              ENNReal.ofReal (C_fi * (p.ν ^ k_fi)⁻¹ * (p.ν ^ (-1 / 2 : ℝ) * Real.sqrt p.H + p.H)) *
                hNorm p.c bgp F ∧
            eLpNorm (flatK p.train b0 b0q b0η) (ENNReal.ofReal bgp)
                ((hMeas p.c bgp).restrict (Ioi p.H ×ˢ univ)) ≤
              ENNReal.ofReal
                  (C_fi * (p.ν ^ k_fi)⁻¹ * p.H ^ (-1 / 2 : ℝ) * (p.ν ^ (-1 / 2 : ℝ) + 1)) *
                hNorm p.c bgp F) →
        (∀ i : Fin 2,
          InHr p.c bgp (flatColumn p i) ∧
          hNorm p.c bgp (flatColumn p i) ≤ ENNReal.ofReal (C_col * (p.ν ^ k_col)⁻¹)) →
        (∃ (αMap : HpR p.c →L[ℝ] E2)
          (b0Of b0qOf b0ηOf gOf gqOf gηOf zOf zqOf zηOf : HpR p.c →ₗ[ℝ] CProf)
          (D2zOf : Fin 2 → Fin 2 → HpR p.c →ₗ[ℝ] CProf),
          (∀ F : HpR p.c,
            let M_z := C_ls * (p.ν ^ k_ls)⁻¹ *
              Real.exp ((a' * Sig + C_late / (1 + Sig)) / p.ν + C_late * p.ν ^ 3) * ‖F‖
            let gH1_tail :=
              (∫⁻ s in Ioi (max 1 (p.H - 1)),
                sliceH1Norm p.c (gOf F) (gqOf F) (gηOf F) s ^ bgp ∂sMeas (-9 / 8)) ^ (4 / 11 : ℝ)
            InFlatClass p.c bgp (b0Of F) ∧
            IsFlatResponse p.ν 0 (toProf p.c F) (b0Of F) ∧
            HasWeakVec vQ0 dZero (b0Of F) (b0qOf F) ∧
            HasWeakVec vEta dZero (b0Of F) (b0ηOf F) ∧
            QPeriodic p.c (gOf F) ∧
            HasWeakVec vQ0 dZero (gOf F) (gqOf F) ∧
            HasWeakVec vEta dZero (gOf F) (gηOf F) ∧
            IsBodySource p.train (b0Of F) (b0qOf F) (b0ηOf F) (gOf F) ∧
            IsGlobalMeridionalCorrection p (gOf F) (zOf F) (zqOf F) (zηOf F) (αMap F) ∧
            HasWeakVec vQ0 dZero (zqOf F) (D2zOf 0 0 F) ∧
            HasWeakVec vEta dZero (zqOf F) (D2zOf 0 1 F) ∧
            HasWeakVec vQ0 dZero (zηOf F) (D2zOf 1 0 F) ∧
            HasWeakVec vEta dZero (zηOf F) (D2zOf 1 1 F) ∧
            Measurable (sliceH1Norm p.c (zOf F) (zqOf F) (zηOf F)) ∧
            Measurable (sliceH2Norm p.c (zOf F) (zqOf F) (zηOf F) (fun i j => D2zOf i j F)) ∧
            (∀ s : ℝ, 0 < s →
              sliceH1Norm p.c (zOf F) (zqOf F) (zηOf F) s + ENNReal.ofReal ‖αMap F‖ ≤
                ENNReal.ofReal M_z) ∧
            sLpNorm (13 / 8) p.H
                (sliceH2Norm p.c (zOf F) (zqOf F) (zηOf F) (fun i j => D2zOf i j F)) ≤
              ENNReal.ofReal M_z ∧
            (∫⁻ s in Ioi p.H,
                sliceH2Norm p.c (zOf F) (zqOf F) (zηOf F) (fun i j => D2zOf i j F) s ^ bgp
                  ∂sMeas (-9 / 8)) ^ (4 / 11 : ℝ) ≤
              ENNReal.ofReal (C_ls * p.ν ^ (-1 / 2 : ℝ)) *
                (ENNReal.ofReal (p.H ^ (-1 / 22 : ℝ) * M_z) + gH1_tail) ∧
            InHr p.c bgp (flatK p.train (zOf F) (zqOf F) (zηOf F)) ∧
            hNorm p.c bgp (flatK p.train (zOf F) (zqOf F) (zηOf F)) ≤
              ENNReal.ofReal M_z)) →
        ∃ R0 : HpR p.c →L[ℝ] RowSpace p.c,
          ‖R0‖ ≤ C * (p.ν ^ k)⁻¹ *
            Real.exp ((a' * Sig + C_late / (1 + Sig)) / p.ν + C_late * p.ν ^ 3) ∧
          ∀ F : HpR p.c,
            let f : HpR p.c := (WithLp.fstL 1 ℝ (HpR p.c) E2) (R0 F)
            let α : E2 := (WithLp.sndL 1 ℝ (HpR p.c) E2) (R0 F)
            ∃ (b0 b0q b0η g z zq zη : CProf),
              InFlatClass p.c bgp b0 ∧
              IsFlatResponse p.ν 0 (toProf p.c F) b0 ∧
              HasWeakVec vQ0 dZero b0 b0q ∧
              HasWeakVec vEta dZero b0 b0η ∧
              IsBodySource p.train b0 b0q b0η g ∧
              IsGlobalMeridionalCorrection p g z zq zη α ∧
              (∃ M₁ : ℝ, ∀ s : ℝ, 0 < s → sliceH1Norm p.c z zq zη s ≤ ENNReal.ofReal M₁) ∧
              QPeriodic p.c (fun x =>
                toProf p.c F x -
                  flatK p.train (fun y => b0 y + z y - inletProf p α y)
                    (fun y => b0q y + zq y - inletProfQ p α y)
                    (fun y => b0η y + zη y - inletProfEta p α y) x -
                  ∑ i : Fin 2, ((α i : ℝ) : ℂ) • flatColumn p i x) ∧
              toProf p.c f =ᵐ[hMeas p.c bgp] fun x =>
                toProf p.c F x -
                  flatK p.train (fun y => b0 y + z y - inletProf p α y)
                    (fun y => b0q y + zq y - inletProfQ p α y)
                    (fun y => b0η y + zη y - inletProfEta p α y) x -
                  ∑ i : Fin 2, ((α i : ℝ) : ℂ) • flatColumn p i x

/-- **Sub-step 2 (`InletEntranceCurlIdentity`, SP 2313–2318, 2347–2358)**:
for `0 < s < p.H / 4` (where `ageCutoff p.H = 1` in a neighborhood of `s`), the planar curl of the
flat inlet profile `inletProf p α` equals `entranceVorticityComb p α`, because
`Δ(periodicStream q p.c) = periodizePlanar p.c (dilPlanarMode q 1)`. -/
def InletEntranceCurlIdentity : Prop :=
  ∀ (lam : ℂ) (q : Blueprint.Planar.Profile),
    Blueprint.Planar.IsGrowingEigenpair lam q →
  ∀ (dm dp : ℝ), 0 < dm →
  ∀ (p : Params) (d : ℝ), BgRegime p d dm dp → p.ν ≤ 1 → p.mode = q →
  ∀ (α : E2) (s : ℝ), 0 < s → s < p.H / 4 → ∀ x : B0579.Plane,
    profCurl (inletProfQ p α) (inletProfEta p α) (s, x) =
      ((entranceVorticityComb p α x : ℝ) : ℂ)

/-- **Sub-step 3 (`FlatReconstructionZeroCurlUniqueStep`, SP 2316–2328)**:
if `b0, b_f ∈ InFlatClass p.c bgp`, `z` is `c`-periodic with weak spatial derivatives of first
order, uniformly bounded `sliceH1Norm` on `(0, ∞)`, vanishing curl difference
`‖profCurl(zq - ∂_q Eα, zη - ∂_η Eα)(s)‖_{L²(cell)} → 0` as `s → 0⁺`, and
`(b0 + z - inletProf p α) - b_f` solves the homogeneous flat response equation
`IsFlatResponse p.ν 0 0`, then `b0 + z - inletProf p α =ᵐ[hMeas p.c bgp] b_f`. -/
def FlatReconstructionZeroCurlUniqueStep : Prop :=
  ∀ (lam : ℂ) (q : Blueprint.Planar.Profile),
    Blueprint.Planar.IsGrowingEigenpair lam q →
  ∀ (dm dp : ℝ), 0 < dm →
  ∀ (p : Params) (d : ℝ), BgRegime p d dm dp → p.ν ≤ 1 / 2 → p.mode = q →
  ∀ (α : E2) (b0 z zq zη b_f : CProf),
    InFlatClass p.c bgp b0 →
    InFlatClass p.c bgp b_f →
    QPeriodic p.c z →
    HasWeakVec vQ0 dZero z zq →
    HasWeakVec vEta dZero z zη →
    (∃ M₁ : ℝ, ∀ s : ℝ, 0 < s → sliceH1Norm p.c z zq zη s ≤ ENNReal.ofReal M₁) →
    Tendsto (fun s => eLpNorm
        (fun x => profCurl (fun y => zq y - inletProfQ p α y)
          (fun y => zη y - inletProfEta p α y) (s, x))
        2 (B0579.cellMeasure p.c 0))
      (𝓝[Ioi 0] 0) (𝓝 0) →
    IsFlatResponse p.ν 0 0 (fun x => (b0 x + z x - inletProf p α x) - b_f x) →
    (fun x => b0 x + z x - inletProf p α x) =ᵐ[hMeas p.c bgp] b_f

/-- **Complete conditional assembly of `FlatReconstructionIdentityStep` (`PartII-b:F9/3`)**
from the three concrete sub-steps together with the unconditionally proved
`flatReconstruction_isFlatResponse` and `inHr_and_inFlatClass_of_ae_eq_response`. -/
theorem flatReconstructionIdentityStep_of_steps
    (hLin : FlatReconstructionLinearR0Step)
    (hCurl : InletEntranceCurlIdentity)
    (hUniq : FlatReconstructionZeroCurlUniqueStep) :
    FlatReconstructionIdentityStep := by
  intro C_late hCl Sig lam q hSig hq a' ha' ha'lt dm dp hdm
    C_ge k_ge C_ls k_ls C_fl C_fi k_fi C_col k_col hCge hCls hCfl hCfi hCcol
  obtain ⟨C, k, ν₀, hC, hν₀, hν₀_half, H_lin⟩ :=
    hLin C_late hCl Sig lam q hSig hq a' ha' ha'lt dm dp hdm
      C_ge k_ge C_ls k_ls C_fl C_fi k_fi C_col k_col hCge hCls hCfl hCfi hCcol
  refine ⟨C, k, ν₀, hC, hν₀, ?_⟩
  intro p d hreg hνle hage hmode hFl hFI hCol hLS
  have hν_half : p.ν ≤ 1 / 2 := hνle.trans hν₀_half
  have hν1 : p.ν ≤ 1 := hν_half.trans (by norm_num)
  have hc : 0 < p.c := p.c_pos
  obtain ⟨R0, hR0_norm, hR0_spec⟩ := H_lin p d hreg hνle hage hmode hFI hCol hLS
  refine ⟨R0, hR0_norm, fun F => ?_⟩
  set f : HpR p.c := (WithLp.fstL 1 ℝ (HpR p.c) E2) (R0 F)
  set α : E2 := (WithLp.sndL 1 ℝ (HpR p.c) E2) (R0 F)
  obtain ⟨b0, b0q, b0η, g, z, zq, zη, hb0_cl, hb0_resp, hb0q, hb0η,
    hbody, hmc, hH1_bd, hRHS_per, hf_ae⟩ := hR0_spec F
  have hrec_resp : IsFlatResponse p.ν 0 (toProf p.c f) (fun x => b0 x + z x - inletProf p α x) :=
    flatReconstruction_isFlatResponse hq hreg hν1 hmode hb0_resp hbody hmc hRHS_per hf_ae
  obtain ⟨b_f, hbf_cl, hbf_resp, _hbf_gb, _hbf_uniq⟩ := hFl (toProf p.c f) (inHr_toProf hc f)
  have hdiff_resp : IsFlatResponse p.ν 0 0
      (fun x => (b0 x + z x - inletProf p α x) - b_f x) :=
    flatResponseSub p.ν 0 (toProf p.c f) (fun x => b0 x + z x - inletProf p α x) b_f
      hrec_resp hbf_resp
  have hH_pos : 0 < p.H / 4 := by
    have hHp : 0 < p.H := by
      show 0 < p.ageCut / p.ν
      rw [hage]
      exact div_pos hSig p.ν_pos
    linarith
  have hcurl_ev : (fun s : ℝ => eLpNorm
      (fun x => profCurl (fun y => zq y - inletProfQ p α y)
        (fun y => zη y - inletProfEta p α y) (s, x))
      2 (B0579.cellMeasure p.c 0)) =ᶠ[𝓝[Ioi 0] 0]
      (fun s : ℝ => eLpNorm
        (fun x => profCurl zq zη (s, x) - ((entranceVorticityComb p α x : ℝ) : ℂ))
        2 (B0579.cellMeasure p.c 0)) := by
    filter_upwards [Ioo_mem_nhdsGT hH_pos] with s hs
    congr 1
    funext x
    have hE_curl := hCurl lam q hq dm dp hdm p d hreg hν1 hmode α s hs.1 hs.2 x
    unfold profCurl at hE_curl ⊢
    simp only [PiLp.sub_apply]
    rw [← hE_curl]
    ring
  have hcurl_tendsto : Tendsto (fun s => eLpNorm
      (fun x => profCurl (fun y => zq y - inletProfQ p α y)
        (fun y => zη y - inletProfEta p α y) (s, x))
      2 (B0579.cellMeasure p.c 0)) (𝓝[Ioi 0] 0) (𝓝 0) :=
    hmc.initial_curl.congr' hcurl_ev.symm
  have hae_bf : (fun x => b0 x + z x - inletProf p α x) =ᵐ[hMeas p.c bgp] b_f :=
    hUniq lam q hq dm dp hdm p d hreg hν_half hmode α b0 z zq zη b_f
      hb0_cl hbf_cl hmc.periodic hmc.weak_q hmc.weak_eta hH1_bd hcurl_tendsto hdiff_resp
  obtain ⟨hz_inHr, hrec_cl⟩ :=
    inHr_and_inFlatClass_of_ae_eq_response hb0_cl hmc.periodic hbf_cl hae_bf
  exact ⟨b0, b0q, b0η, z, zq, zη, hb0_cl, hb0_resp, hb0q, hb0η, hmc.weak_q, hmc.weak_eta,
    hz_inHr, hrec_cl, hrec_resp, hf_ae⟩

/-! ## 7. Proof of Sub-step 1 (`FlatReconstructionLinearR0Step`) -/

namespace LinearR0Help

def reCLM : ℂ →L[ℝ] ℂ := Complex.ofRealCLM.comp Complex.reCLM

@[simp]
lemma reCLM_apply (w : ℂ) : reCLM w = (w.re : ℂ) := rfl

lemma norm_reCLM_le (w : ℂ) : ‖reCLM w‖ ≤ ‖w‖ := by
  simp only [reCLM_apply, Complex.norm_real, Real.norm_eq_abs]
  exact Complex.abs_re_le_norm w

lemma reCLM_mul_ofReal (w : ℂ) (r : ℝ) : reCLM (w * (r : ℂ)) = reCLM w * (r : ℂ) := by
  simp [reCLM]

lemma reCLM_ofReal_mul (r : ℝ) (w : ℂ) : reCLM ((r : ℂ) * w) = (r : ℂ) * reCLM w := by
  simp [reCLM]

lemma reCLM_ofReal (r : ℝ) : reCLM (r : ℂ) = (r : ℂ) := by
  simp [reCLM]

def reProf (b : CProf) : CProf := fun x => liftM (reM (b x))

lemma reProf_apply (b : CProf) (x : Coord) (i : Fin 2) :
    reProf b x i = reCLM (b x i) := by
  simp [reProf, liftM, reM, reCLM]

lemma reProf_idem (b : CProf) : reProf (reProf b) = reProf b := by
  ext x i
  simp [reProf_apply]

lemma liftM_reM_reProf (b : CProf) (x : Coord) :
    liftM (reM (reProf b x)) = reProf b x := by
  ext i
  simp [reProf, liftM, reM]

lemma norm_reProf_le (b : CProf) (x : Coord) : ‖reProf b x‖ ≤ ‖b x‖ := by
  rw [← sq_le_sq₀ (norm_nonneg _) (norm_nonneg _),
    EuclideanSpace.norm_sq_eq, EuclideanSpace.norm_sq_eq]
  refine Finset.sum_le_sum fun i _ => ?_
  rw [reProf_apply]
  exact (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).2 (norm_reCLM_le (b x i))

def reProfLM : CProf →ₗ[ℝ] CProf where
  toFun := reProf
  map_add' a b := by
    ext x i
    simp [reProf_apply]
  map_smul' r a := by
    ext x i
    change reProf (r • a) x i = (r • reProf a) x i
    rw [reProf_apply]
    simp only [Pi.smul_apply, PiLp.smul_apply, reProf_apply, reCLM.map_smul]

lemma reProf_toProf (c : ℝ) (F : HpR c) : reProf (toProf c F) = toProf c F := by
  ext x i
  simp [reProf, toProf, liftM, reM]

lemma reProf_cplx (G : Coord → Axi.Merid) : reProf (cplx G) = cplx G := by
  ext x i
  simp [reProf, cplx, liftM, reM]

lemma hNorm_reProf_le (c r : ℝ) (b : CProf) : hNorm c r (reProf b) ≤ hNorm c r b :=
  eLpNorm_mono (fun x => norm_reProf_le b x)

lemma inHr_reProf {c r : ℝ} {b : CProf} (hb : InHr c r b) : InHr c r (reProf b) where
  periodic := by
    filter_upwards [hb.periodic] with x hx
    simp [reProf, hx]
  meas := (continuous_liftM.comp continuous_reM).comp_aestronglyMeasurable hb.meas
  finite := (hNorm_reProf_le c r b).trans_lt hb.finite

lemma sqrtS_reProf (b : CProf) : sqrtS (reProf b) = reProf (sqrtS b) := by
  ext x i
  simp [sqrtS, reProf_apply]

lemma hasWeakFO_reCLM {v : Coord → Fin 3 → ℝ} {d : Coord → ℝ} {u du : Coord → ℂ}
    (h : HasWeakFO v d u du) :
    HasWeakFO v d (fun x => reCLM (u x)) (fun x => reCLM (du x)) := by
  refine ⟨fun φ hφ => ?_, fun φ hφ => ?_⟩
  · obtain ⟨hIu, hIdu⟩ := h.1 φ hφ
    have eu : (fun x => reCLM (u x) * (coordTranspose v d φ x : ℂ)) =
        fun x => reCLM (u x * (coordTranspose v d φ x : ℂ)) := by
      funext x; rw [← reCLM_mul_ofReal]
    have edu : (fun x => reCLM (du x) * (φ x : ℂ)) =
        fun x => reCLM (du x * (φ x : ℂ)) := by
      funext x; rw [← reCLM_mul_ofReal]
    rw [eu, edu]
    exact ⟨reCLM.integrable_comp hIu, reCLM.integrable_comp hIdu⟩
  · obtain ⟨hIu, hIdu⟩ := h.1 φ hφ
    have heq := h.2 φ hφ
    have eu : (fun x => reCLM (u x) * (coordTranspose v d φ x : ℂ)) =
        fun x => reCLM (u x * (coordTranspose v d φ x : ℂ)) := by
      funext x; rw [← reCLM_mul_ofReal]
    have edu : (fun x => reCLM (du x) * (φ x : ℂ)) =
        fun x => reCLM (du x * (φ x : ℂ)) := by
      funext x; rw [← reCLM_mul_ofReal]
    rw [edu, eu, reCLM.integral_comp_comm hIdu, reCLM.integral_comp_comm hIu, heq]

lemma hasWeakVec_reProf {v : Coord → Fin 3 → ℝ} {d : Coord → ℝ} {b db : CProf}
    (h : HasWeakVec v d b db) : HasWeakVec v d (reProf b) (reProf db) := by
  intro i
  have hi := hasWeakFO_reCLM (h i)
  simpa only [reProf_apply] using hi

lemma inFlatClass_reProf {c r : ℝ} {b : CProf} (hb : InFlatClass c r b) :
    InFlatClass c r (reProf b) := by
  obtain ⟨Sb, Qb, Eb, hS, hQ, hE, hSi, hQi, hEi⟩ := hb.deriv
  refine ⟨inHr_reProf hb.inHr, reProf Sb, reProf Qb, reProf Eb,
    hasWeakVec_reProf hS, hasWeakVec_reProf hQ, hasWeakVec_reProf hE,
    inHr_reProf hSi, ?_, ?_⟩
  · rw [sqrtS_reProf]; exact inHr_reProf hQi
  · rw [sqrtS_reProf]; exact inHr_reProf hEi

def flatTransposeZeroR (ν : ℝ) (Ψ : Coord → Fin 2 → ℝ) (x : Coord) (i : Fin 2) : ℝ :=
  -Ψ x i - x.1 * cpd 0 (fun y => Ψ y i) x -
    ν * x.1 * (cpd 1 (fun y => cpd 1 (fun z => Ψ z i) y) x +
      cpd 2 (fun y => cpd 2 (fun z => Ψ z i) y) x)

lemma flatTranspose_zero_eq_ofReal (ν : ℝ) (Ψ : Coord → Fin 2 → ℝ) (x : Coord) (i : Fin 2) :
    flatTranspose ν 0 Ψ x i = (flatTransposeZeroR ν Ψ x i : ℂ) := by
  unfold flatTranspose flatTransposeZeroR
  push_cast
  ring

def meridTransposeR (ν : ℝ) (Ψ : Coord → Fin 2 → ℝ) (x : Coord) (i : Fin 2) : ℝ :=
  -cpd 0 (fun y => Ψ y i) x -
    ν * (cpd 1 (fun y => cpd 1 (fun z => Ψ z i) y) x +
      cpd 2 (fun y => cpd 2 (fun z => Ψ z i) y) x)

lemma meridTranspose_eq_ofReal (ν : ℝ) (Ψ : Coord → Fin 2 → ℝ) (x : Coord) (i : Fin 2) :
    meridTranspose ν Ψ x i = (meridTransposeR ν Ψ x i : ℂ) := by
  unfold meridTranspose meridTransposeR
  push_cast
  ring

lemma cdot_reProf (b : CProf) (Ψ : Coord → Fin 2 → ℝ) (x : Coord) :
    cdot (reProf b) Ψ x = reCLM (cdot b Ψ x) := by
  unfold cdot
  rw [map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [reProf_apply, reCLM_mul_ofReal]

lemma solenoidal_reProf {b : CProf}
    (hsol : ∀ φ, IsCoordTest φ →
      Integrable (fun x => b x 0 * (cpd 1 φ x : ℂ) + b x 1 * (cpd 2 φ x : ℂ)) ∧
        ∫ x, (b x 0 * (cpd 1 φ x : ℂ) + b x 1 * (cpd 2 φ x : ℂ)) = 0) :
    ∀ φ, IsCoordTest φ →
      Integrable (fun x => reProf b x 0 * (cpd 1 φ x : ℂ) + reProf b x 1 * (cpd 2 φ x : ℂ)) ∧
        ∫ x, (reProf b x 0 * (cpd 1 φ x : ℂ) + reProf b x 1 * (cpd 2 φ x : ℂ)) = 0 := by
  intro φ hφ
  obtain ⟨hI, hZ⟩ := hsol φ hφ
  have e : (fun x => reProf b x 0 * (cpd 1 φ x : ℂ) + reProf b x 1 * (cpd 2 φ x : ℂ)) =
      fun x => reCLM (b x 0 * (cpd 1 φ x : ℂ) + b x 1 * (cpd 2 φ x : ℂ)) := by
    funext x
    rw [map_add, reProf_apply, reProf_apply, reCLM_mul_ofReal, reCLM_mul_ofReal]
  rw [e]
  refine ⟨reCLM.integrable_comp hI, ?_⟩
  rw [reCLM.integral_comp_comm hI, hZ, map_zero]

lemma isFlatResponse_zero_reProf {ν : ℝ} {F b : CProf} (hr : IsFlatResponse ν 0 F b) :
    IsFlatResponse ν 0 (reProf F) (reProf b) where
  solenoidal := solenoidal_reProf hr.solenoidal
  equation := by
    intro Ψ hΨ
    obtain ⟨hIL, hIR, hEq⟩ := hr.equation Ψ hΨ
    have eL : (fun x => ∑ i : Fin 2, reProf b x i * flatTranspose ν 0 Ψ x i) =
        fun x => reCLM (∑ i : Fin 2, b x i * flatTranspose ν 0 Ψ x i) := by
      funext x
      rw [map_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [reProf_apply, flatTranspose_zero_eq_ofReal, reCLM_mul_ofReal]
    have eR : cdot (reProf F) Ψ = fun x => reCLM (cdot F Ψ x) :=
      funext (cdot_reProf F Ψ)
    rw [eL, eR]
    refine ⟨reCLM.integrable_comp hIL, reCLM.integrable_comp hIR, ?_⟩
    rw [reCLM.integral_comp_comm hIL, reCLM.integral_comp_comm hIR, hEq]

lemma reProf_flatBv {ν c : ℝ} (tr : B0140.TrainSol ν c) (b gq gη : CProf) :
    reProf (flatBv tr b gq gη) = flatBv tr (reProf b) (reProf gq) (reProf gη) := by
  ext x i
  simp only [reProf_apply, flatBv, WithLp.ofLp_toLp, map_add, reCLM_ofReal_mul, reCLM_mul_ofReal]

lemma reProf_flatK {ν c : ℝ} (tr : B0140.TrainSol ν c) (b gq gη : CProf) :
    reProf (flatK tr b gq gη) = flatK tr (reProf b) (reProf gq) (reProf gη) := by
  funext x
  ext i
  rw [reProf_apply, flatK_eq_smul_flatBv,
    flatK_eq_smul_flatBv tr (reProf b) (reProf gq) (reProf gη) x]
  simp only [PiLp.smul_apply, smul_eq_mul, reCLM_ofReal_mul, ← reProf_flatBv, reProf_apply]

lemma isBodySource_reProf {ν c : ℝ} {tr : B0140.TrainSol ν c} {b0 b0q b0η g : CProf}
    (hb : IsBodySource tr b0 b0q b0η g) :
    IsBodySource tr (reProf b0) (reProf b0q) (reProf b0η) (reProf g) where
  solenoidal := solenoidal_reProf hb.solenoidal
  equation := by
    intro Ψ hΨ
    obtain ⟨hIg, hIB, hEq⟩ := hb.equation Ψ hΨ
    have eg : cdot (reProf g) Ψ = fun x => reCLM (cdot g Ψ x) :=
      funext (cdot_reProf g Ψ)
    have eB : cdot (flatBv tr (reProf b0) (reProf b0q) (reProf b0η)) Ψ =
        fun x => reCLM (cdot (flatBv tr b0 b0q b0η) Ψ x) := by
      rw [← reProf_flatBv]
      exact funext (cdot_reProf _ Ψ)
    rw [eg, eB]
    refine ⟨reCLM.integrable_comp hIg, reCLM.integrable_comp hIB, ?_⟩
    rw [reCLM.integral_comp_comm hIg, reCLM.integral_comp_comm hIB, hEq, map_neg]

lemma isGlobalMeridionalCorrection_reProf {p : Params} {g z zq zη : CProf} {α : E2}
    (hmc : IsGlobalMeridionalCorrection p g z zq zη α) :
    IsGlobalMeridionalCorrection p (reProf g) (reProf z) (reProf zq) (reProf zη) α where
  periodic := by
    filter_upwards [hmc.periodic] with x hx
    simp [reProf, hx]
  weak_q := hasWeakVec_reProf hmc.weak_q
  weak_eta := hasWeakVec_reProf hmc.weak_eta
  solenoidal := solenoidal_reProf hmc.solenoidal
  equation := by
    intro Ψ hΨ
    obtain ⟨hIz, hIB, hIg, hEq⟩ := hmc.equation Ψ hΨ
    have ez : (fun x => ∑ i : Fin 2, reProf z x i * meridTranspose p.ν Ψ x i) =
        fun x => reCLM (∑ i : Fin 2, z x i * meridTranspose p.ν Ψ x i) := by
      funext x
      rw [map_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [reProf_apply, meridTranspose_eq_ofReal, reCLM_mul_ofReal]
    have eB : cdot (flatBv p.train (reProf z) (reProf zq) (reProf zη)) Ψ =
        fun x => reCLM (cdot (flatBv p.train z zq zη) Ψ x) := by
      rw [← reProf_flatBv]
      exact funext (cdot_reProf _ Ψ)
    have eg : cdot (reProf g) Ψ = fun x => reCLM (cdot g Ψ x) :=
      funext (cdot_reProf g Ψ)
    refine ⟨ez ▸ reCLM.integrable_comp hIz, eB ▸ reCLM.integrable_comp hIB,
      eg ▸ reCLM.integrable_comp hIg, ?_⟩
    have eLHS : (fun x => ∑ i : Fin 2, reProf z x i * meridTranspose p.ν Ψ x i +
        cdot (flatBv p.train (reProf z) (reProf zq) (reProf zη)) Ψ x) =
        fun x => reCLM (∑ i : Fin 2, z x i * meridTranspose p.ν Ψ x i +
          cdot (flatBv p.train z zq zη) Ψ x) := by
      funext x
      rw [map_add, congrFun ez x, congrFun eB x]
    have eRHS : (fun x => cdot (reProf g) Ψ x) = fun x => reCLM (cdot g Ψ x) := eg
    have hIzB : Integrable (fun x => ∑ i : Fin 2, z x i * meridTranspose p.ν Ψ x i +
        cdot (flatBv p.train z zq zη) Ψ x) _ := hIz.add hIB
    rw [eLHS, eRHS, reCLM.integral_comp_comm hIzB, reCLM.integral_comp_comm hIg, hEq]
  initial_curl := by
    have hle : ∀ s : ℝ,
        eLpNorm (fun x => profCurl (reProf zq) (reProf zη) (s, x) -
            ((entranceVorticityComb p α x : ℝ) : ℂ))
          2 (B0579.cellMeasure p.c 0) ≤
        eLpNorm (fun x => profCurl zq zη (s, x) -
            ((entranceVorticityComb p α x : ℝ) : ℂ))
          2 (B0579.cellMeasure p.c 0) := by
      intro s
      refine eLpNorm_mono fun x => ?_
      have heq : profCurl (reProf zq) (reProf zη) (s, x) -
          ((entranceVorticityComb p α x : ℝ) : ℂ) =
          reCLM (profCurl zq zη (s, x) - ((entranceVorticityComb p α x : ℝ) : ℂ)) := by
        unfold profCurl
        rw [map_sub, map_sub, reProf_apply, reProf_apply, reCLM_ofReal]
      rw [heq]
      exact norm_reCLM_le _
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hmc.initial_curl
      (fun _ => zero_le) hle

lemma sliceH1Norm_reProf_le (c : ℝ) (z zq zη : CProf) (s : ℝ) :
    sliceH1Norm c (reProf z) (reProf zq) (reProf zη) s ≤ sliceH1Norm c z zq zη s := by
  unfold sliceH1Norm
  exact add_le_add
    (add_le_add
      (eLpNorm_mono fun y => norm_reProf_le z (s, y))
      (eLpNorm_mono fun y => norm_reProf_le zq (s, y)))
    (eLpNorm_mono fun y => norm_reProf_le zη (s, y))

/-- The pure heat-operator residual on the `i`-th inlet component:
`flatK p.train (cplx (inletE0 p i)) - flatColumn p i = -s (∂_s - νΔ) (inletE0 p i)`. -/
def inletHeatDiffR (p : Params) (i : Fin 2) (x : Coord) : Axi.Merid :=
  -(x.1 • (Axi.dS (inletE0 p i) x -
    p.ν • (Axi.dQ (Axi.dQ (inletE0 p i)) x + Axi.dEta (Axi.dEta (inletE0 p i)) x)))

def inletHeatDiff (p : Params) (i : Fin 2) (x : Coord) : CMerid :=
  flatK p.train (cplx (inletE0 p i)) (cplx (Axi.dQ (inletE0 p i)))
    (cplx (Axi.dEta (inletE0 p i))) x - flatColumn p i x

lemma inletHeatDiff_eq_cplx (p : Params) (i : Fin 2) :
    inletHeatDiff p i = cplx (inletHeatDiffR p i) := by
  funext y
  ext m
  simp only [inletHeatDiff, inletHeatDiffR, flatColumn, cplx, WithLp.ofLp_toLp,
    PiLp.sub_apply, PiLp.neg_apply, PiLp.smul_apply, PiLp.add_apply, smul_eq_mul]
  push_cast
  ring

private lemma fderiv_qShift_univ {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {F : Coord → E} {c : ℝ} (hF : ∀ y : Coord, F (qShift c y) = F y) (x : Coord) :
    fderiv ℝ F (qShift c x) = fderiv ℝ F x := by
  have hshift : ∀ y : Coord, qShift c y = y + (0, (c, 0)) := fun y => by
    ext <;> simp [qShift]
  have hfun : (fun y : Coord => F (qShift c y)) = F := funext hF
  have h1 : fderiv ℝ (fun y : Coord => F (qShift c y)) x = fderiv ℝ F x := by rw [hfun]
  have hfun2 : (fun y : Coord => F (qShift c y)) = fun y => F (y + (0, (c, 0))) := by
    funext y; rw [hshift]
  rw [hfun2, fderiv_comp_add_right] at h1
  rw [hshift]
  exact h1

lemma qPeriodic_inletHeatDiff (p : Params) (i : Fin 2) :
    QPeriodic p.c (inletHeatDiff p i) := by
  have hcut : ∀ y : Coord, p.cutStream i (qShift p.c y) = p.cutStream i y := by
    intro y
    have hsh : qShift p.c y = y + (0, (p.c, 0)) := by ext <;> simp [qShift]
    rw [hsh]
    exact p.cutStream_add i y
  have hE0 : ∀ y : Coord, inletE0 p i (qShift p.c y) = inletE0 p i y := by
    intro y
    unfold inletE0 Axi.dEta Axi.dQ
    rw [fderiv_qShift_univ hcut y]
  have hdS : ∀ y : Coord, Axi.dS (inletE0 p i) (qShift p.c y) = Axi.dS (inletE0 p i) y := by
    intro y; unfold Axi.dS; rw [fderiv_qShift_univ hE0 y]
  have hdQ1 : ∀ y : Coord, Axi.dQ (inletE0 p i) (qShift p.c y) = Axi.dQ (inletE0 p i) y := by
    intro y; unfold Axi.dQ; rw [fderiv_qShift_univ hE0 y]
  have hdQ2 : ∀ y : Coord, Axi.dQ (Axi.dQ (inletE0 p i)) (qShift p.c y) =
      Axi.dQ (Axi.dQ (inletE0 p i)) y := by
    intro y
    show fderiv ℝ (Axi.dQ (inletE0 p i)) (qShift p.c y) (0, (1, 0)) =
      fderiv ℝ (Axi.dQ (inletE0 p i)) y (0, (1, 0))
    rw [fderiv_qShift_univ hdQ1 y]
  have hdE1 : ∀ y : Coord, Axi.dEta (inletE0 p i) (qShift p.c y) = Axi.dEta (inletE0 p i) y := by
    intro y; unfold Axi.dEta; rw [fderiv_qShift_univ hE0 y]
  have hdE2 : ∀ y : Coord, Axi.dEta (Axi.dEta (inletE0 p i)) (qShift p.c y) =
      Axi.dEta (Axi.dEta (inletE0 p i)) y := by
    intro y
    show fderiv ℝ (Axi.dEta (inletE0 p i)) (qShift p.c y) (0, (0, 1)) =
      fderiv ℝ (Axi.dEta (inletE0 p i)) y (0, (0, 1))
    rw [fderiv_qShift_univ hdE1 y]
  refine QPerHalf.of_ae (Eventually.of_forall fun x => ?_)
  rw [inletHeatDiff_eq_cplx]
  have hs : (qShift p.c x).1 = x.1 := rfl
  simp only [cplx, inletHeatDiffR, hs, hdS x, hdQ2 x, hdE2 x]

private lemma norm_dir_le {F : Coord → Axi.Merid} (x v : Coord) (hv : ‖v‖ ≤ 1) :
    ‖fderiv ℝ F x v‖ ≤ ‖iteratedFDeriv ℝ 1 F x‖ := by
  rw [norm_iteratedFDeriv_one]
  exact ((fderiv ℝ F x).le_opNorm v).trans (mul_le_of_le_one_right (norm_nonneg _) hv)

private lemma norm_dir2_le {F : Coord → Axi.Merid} (hF : ContDiff ℝ ∞ F)
    (x v : Coord) (hv : ‖v‖ ≤ 1) :
    ‖fderiv ℝ (fun m => fderiv ℝ F m v) x v‖ ≤ ‖iteratedFDeriv ℝ 2 F x‖ := by
  have hf : ContDiffAt ℝ ∞ (fderiv ℝ F) x :=
    (hF.fderiv_right (m := ∞) (by simp)).contDiffAt
  have h1 : ‖fderiv ℝ (fun m => fderiv ℝ F m v) x v‖ ≤
      ‖iteratedFDeriv ℝ 1 (fun m => fderiv ℝ F m v) x‖ := norm_dir_le x v hv
  have h2 : ‖iteratedFDeriv ℝ 1 (fun m => fderiv ℝ F m v) x‖ ≤
      ‖v‖ * ‖iteratedFDeriv ℝ 2 F x‖ := by
    refine (norm_iteratedFDeriv_clm_apply_const hf (by exact_mod_cast le_top)).trans ?_
    rw [norm_iteratedFDeriv_fderiv]
  exact h1.trans (h2.trans (mul_le_of_le_one_left (norm_nonneg _) hv))

lemma inletHeatDiff_vanish (p : Params) (i : Fin 2) {x : Coord} (hx : p.H / 2 < x.1) :
    inletHeatDiff p i x = 0 := by
  have hU : IsOpen {y : Coord | p.H / 2 < y.1} := isOpen_lt continuous_const continuous_fst
  have hcut0 : ∀ y ∈ {y : Coord | p.H / 2 < y.1}, p.cutStream i y = 0 := by
    intro y (hy : p.H / 2 < y.1)
    simp [Params.cutStream, ageCutoff_eq_zero p.H_pos hy.le]
  have hE0_zero : ∀ y ∈ {y : Coord | p.H / 2 < y.1}, inletE0 p i y = 0 := by
    intro y hy
    have hev : p.cutStream i =ᶠ[𝓝 y] (0 : Coord → ℝ) := by
      filter_upwards [hU.mem_nhds hy] with z hz
      exact hcut0 z hz
    unfold inletE0 Axi.dEta Axi.dQ
    rw [hev.fderiv_eq]
    simp
  have hevE0 : inletE0 p i =ᶠ[𝓝 x] (0 : Coord → Axi.Merid) := by
    filter_upwards [hU.mem_nhds hx] with y hy
    exact hE0_zero y hy
  have hdS0 : Axi.dS (inletE0 p i) x = 0 := by
    unfold Axi.dS; rw [hevE0.fderiv_eq]; simp
  have hdQ_ev : Axi.dQ (inletE0 p i) =ᶠ[𝓝 x] (0 : Coord → Axi.Merid) := by
    filter_upwards [hU.mem_nhds hx] with y hy
    have hevy : inletE0 p i =ᶠ[𝓝 y] (0 : Coord → Axi.Merid) := by
      filter_upwards [hU.mem_nhds hy] with z hz
      exact hE0_zero z hz
    unfold Axi.dQ; rw [hevy.fderiv_eq]; simp
  have hdQ2_0 : Axi.dQ (Axi.dQ (inletE0 p i)) x = 0 := by
    show fderiv ℝ (Axi.dQ (inletE0 p i)) x (0, (1, 0)) = 0
    rw [hdQ_ev.fderiv_eq]; simp
  have hdE_ev : Axi.dEta (inletE0 p i) =ᶠ[𝓝 x] (0 : Coord → Axi.Merid) := by
    filter_upwards [hU.mem_nhds hx] with y hy
    have hevy : inletE0 p i =ᶠ[𝓝 y] (0 : Coord → Axi.Merid) := by
      filter_upwards [hU.mem_nhds hy] with z hz
      exact hE0_zero z hz
    unfold Axi.dEta; rw [hevy.fderiv_eq]; simp
  have hdE2_0 : Axi.dEta (Axi.dEta (inletE0 p i)) x = 0 := by
    show fderiv ℝ (Axi.dEta (inletE0 p i)) x (0, (0, 1)) = 0
    rw [hdE_ev.fderiv_eq]; simp
  rw [inletHeatDiff_eq_cplx]
  ext m
  simp [cplx, inletHeatDiffR, hdS0, hdQ2_0, hdE2_0]

lemma inletHeatDiff_bound (Sig : ℝ) (lam : ℂ) (q : Planar.Profile) (hSig : 0 < Sig)
    (hq : Planar.IsGrowingEigenpair lam q) (dm dp : ℝ) (hdm : 0 < dm) :
    ∃ (C_hd : ℝ) (k_hd : ℕ) (ν_hd : ℝ), 0 < C_hd ∧ 0 < ν_hd ∧ ν_hd ≤ 1 ∧
      ∀ (p : Params) (d : ℝ), BgRegime p d dm dp → p.ν ≤ ν_hd → p.ageCut = Sig → p.mode = q →
        ∀ i : Fin 2,
          InHr p.c bgp (inletHeatDiff p i) ∧
          hNorm p.c bgp (inletHeatDiff p i) ≤ ENNReal.ofReal (C_hd * (p.ν ^ k_hd)⁻¹) := by
  obtain ⟨C_in, κ_in, k_in, N_in, ν_in, hC_in, hκ_in, hν_in, hν_in1, H_in⟩ :=
    inletComponentJets Sig lam q hSig hq dm dp hdm 2
  obtain ⟨K_w, hK_w, HW⟩ := colWeightNorm N_in κ_in hκ_in
  refine ⟨K_w * (3 * C_in) * (1 + Sig), k_in + 1 + 2 * (N_in + 1), ν_in,
    by positivity, hν_in, hν_in1, ?_⟩
  intro p d hreg hν hS hm i
  have hνpos : 0 < p.ν := p.ν_pos
  have hν1 : p.ν ≤ 1 := hν.trans hν_in1
  have hc1 : 1 ≤ p.c := by
    rw [hreg.c_eq, one_le_inv₀ (by positivity)]
    nlinarith
  have hH : 0 < p.H := p.H_pos
  obtain ⟨hE0_cd, _hE1_cd, hjet⟩ := H_in p d ⟨hreg, hν, hS, hm⟩ i
  have hcontR : Continuous (inletHeatDiffR p i) := by
    have hdS : ContDiff ℝ ∞ (Axi.dS (inletE0 p i)) :=
      (hE0_cd.fderiv_right (m := ∞) (by simp)).clm_apply contDiff_const
    have hdQ1 : ContDiff ℝ ∞ (Axi.dQ (inletE0 p i)) :=
      (hE0_cd.fderiv_right (m := ∞) (by simp)).clm_apply contDiff_const
    have hdQ2 : ContDiff ℝ ∞ (Axi.dQ (Axi.dQ (inletE0 p i))) :=
      (hdQ1.fderiv_right (m := ∞) (by simp)).clm_apply contDiff_const
    have hdE1 : ContDiff ℝ ∞ (Axi.dEta (inletE0 p i)) :=
      (hE0_cd.fderiv_right (m := ∞) (by simp)).clm_apply contDiff_const
    have hdE2 : ContDiff ℝ ∞ (Axi.dEta (Axi.dEta (inletE0 p i))) :=
      (hdE1.fderiv_right (m := ∞) (by simp)).clm_apply contDiff_const
    unfold inletHeatDiffR
    exact (continuous_fst.smul
      (hdS.continuous.sub ((hdQ2.continuous.add hdE2.continuous).const_smul p.ν))).neg
  have hcont : Continuous (inletHeatDiff p i) := by
    rw [inletHeatDiff_eq_cplx]
    have hcplx : Continuous (fun v : Axi.Merid =>
        (WithLp.toLp 2 (fun j => ((v j : ℝ) : ℂ)) : CMerid)) :=
      (PiLp.continuous_toLp 2 (fun _ : Fin 2 => ℂ)).comp
        (continuous_pi fun j => Complex.continuous_ofReal.comp (EuclideanSpace.proj j).continuous)
    exact hcplx.comp hcontR
  have hMnn : 0 ≤ 3 * C_in * (p.ν ^ k_in)⁻¹ := by positivity
  have hle_w := HW p.c p.H (3 * C_in * (p.ν ^ k_in)⁻¹) (inletHeatDiff p i) hc1 hH hMnn
    (fun x hx => inletHeatDiff_vanish p i hx)
    (fun x hx0 hx1 => by
      have hxH : x.1 ≤ p.H := hx1.trans (by linarith)
      have hj1 : ‖iteratedFDeriv ℝ 1 (inletE0 p i) x‖ ≤
          C_in * (p.ν ^ k_in)⁻¹ * (1 + |x.2.2|) ^ N_in *
            Real.exp (-(κ_in * |x.2.2| / p.c)) := by
        have h := hjet 1 (by omega) x hxH
        linarith [norm_nonneg (iteratedFDeriv ℝ 1 (inletE1 p i) x)]
      have hj2 : ‖iteratedFDeriv ℝ 2 (inletE0 p i) x‖ ≤
          C_in * (p.ν ^ k_in)⁻¹ * (1 + |x.2.2|) ^ N_in *
            Real.exp (-(κ_in * |x.2.2| / p.c)) := by
        have h := hjet 2 (by omega) x hxH
        linarith [norm_nonneg (iteratedFDeriv ℝ 2 (inletE1 p i) x)]
      have hdS_le : ‖Axi.dS (inletE0 p i) x‖ ≤ ‖iteratedFDeriv ℝ 1 (inletE0 p i) x‖ :=
        norm_dir_le x (1, (0, 0)) (by simp)
      have hdQ2_le : ‖Axi.dQ (Axi.dQ (inletE0 p i)) x‖ ≤
          ‖iteratedFDeriv ℝ 2 (inletE0 p i) x‖ :=
        norm_dir2_le hE0_cd x (0, (1, 0)) (by simp)
      have hdE2_le : ‖Axi.dEta (Axi.dEta (inletE0 p i)) x‖ ≤
          ‖iteratedFDeriv ℝ 2 (inletE0 p i) x‖ :=
        norm_dir2_le hE0_cd x (0, (0, 1)) (by simp)
      rw [inletHeatDiff_eq_cplx]
      have enorm : ‖cplx (inletHeatDiffR p i) x‖ = ‖inletHeatDiffR p i x‖ := liftM_norm _
      rw [enorm]
      unfold inletHeatDiffR
      rw [norm_neg, norm_smul, Real.norm_eq_abs, abs_of_pos hx0]
      set E := (1 + |x.2.2|) ^ N_in * Real.exp (-(κ_in * |x.2.2| / p.c))
      have hsub : ‖Axi.dS (inletE0 p i) x -
          p.ν • (Axi.dQ (Axi.dQ (inletE0 p i)) x + Axi.dEta (Axi.dEta (inletE0 p i)) x)‖ ≤
          3 * C_in * (p.ν ^ k_in)⁻¹ * E := by
        calc ‖Axi.dS (inletE0 p i) x -
              p.ν • (Axi.dQ (Axi.dQ (inletE0 p i)) x + Axi.dEta (Axi.dEta (inletE0 p i)) x)‖
            ≤ ‖Axi.dS (inletE0 p i) x‖ +
                ‖p.ν • (Axi.dQ (Axi.dQ (inletE0 p i)) x + Axi.dEta (Axi.dEta (inletE0 p i)) x)‖ :=
              norm_sub_le _ _
          _ ≤ ‖Axi.dS (inletE0 p i) x‖ +
                p.ν * (‖Axi.dQ (Axi.dQ (inletE0 p i)) x‖ +
                  ‖Axi.dEta (Axi.dEta (inletE0 p i)) x‖) := by
              rw [norm_smul, Real.norm_eq_abs, abs_of_pos hνpos]
              gcongr
              exact norm_add_le _ _
          _ ≤ ‖Axi.dS (inletE0 p i) x‖ +
                1 * (‖Axi.dQ (Axi.dQ (inletE0 p i)) x‖ +
                  ‖Axi.dEta (Axi.dEta (inletE0 p i)) x‖) := by
              gcongr
          _ ≤ C_in * (p.ν ^ k_in)⁻¹ * E +
                1 * (C_in * (p.ν ^ k_in)⁻¹ * E + C_in * (p.ν ^ k_in)⁻¹ * E) := by
              gcongr <;> linarith
          _ = 3 * C_in * (p.ν ^ k_in)⁻¹ * E := by ring
      calc x.1 * ‖Axi.dS (inletE0 p i) x -
            p.ν • (Axi.dQ (Axi.dQ (inletE0 p i)) x + Axi.dEta (Axi.dEta (inletE0 p i)) x)‖
          ≤ x.1 * (3 * C_in * (p.ν ^ k_in)⁻¹ * E) :=
            mul_le_mul_of_nonneg_left hsub hx0.le
        _ = 3 * C_in * (p.ν ^ k_in)⁻¹ * x.1 * (1 + |x.2.2|) ^ N_in *
              Real.exp (-(κ_in * |x.2.2| / p.c)) := by ring)
  have hHle : 1 + p.H ≤ (1 + Sig) * p.ν⁻¹ := by
    have hHeq : p.H = Sig / p.ν := by simp [Params.H, hS]
    rw [hHeq]
    have hinv1 : 1 ≤ p.ν⁻¹ := (one_le_inv₀ hνpos).2 hν1
    have h4 : (1 + Sig) * p.ν⁻¹ = p.ν⁻¹ + Sig / p.ν := by ring
    rw [h4]
    linarith
  have hcpow : p.c ^ (N_in + 1) = (p.ν ^ (2 * (N_in + 1)))⁻¹ := by
    rw [hreg.c_eq, inv_pow, ← pow_mul]
  have hnorm_le : hNorm p.c bgp (inletHeatDiff p i) ≤
      ENNReal.ofReal (K_w * (3 * C_in) * (1 + Sig) *
        (p.ν ^ (k_in + 1 + 2 * (N_in + 1)))⁻¹) := by
    refine hle_w.trans (ENNReal.ofReal_le_ofReal ?_)
    calc K_w * (3 * C_in * (p.ν ^ k_in)⁻¹) * (1 + p.H) * p.c ^ (N_in + 1)
        ≤ K_w * (3 * C_in * (p.ν ^ k_in)⁻¹) * ((1 + Sig) * p.ν⁻¹) * p.c ^ (N_in + 1) := by
          gcongr
      _ = K_w * (3 * C_in) * (1 + Sig) * (p.ν ^ (k_in + 1 + 2 * (N_in + 1)))⁻¹ := by
          rw [hcpow]
          have hp : (p.ν ^ (k_in + 1 + 2 * (N_in + 1)))⁻¹ =
              (p.ν ^ k_in)⁻¹ * p.ν⁻¹ * (p.ν ^ (2 * (N_in + 1)))⁻¹ := by
            rw [pow_add, pow_add, pow_one, mul_inv, mul_inv]
          rw [hp]
          ring
  refine ⟨⟨qPeriodic_inletHeatDiff p i, hcont.aestronglyMeasurable,
    hnorm_le.trans_lt ENNReal.ofReal_lt_top⟩, hnorm_le⟩

lemma hNorm_le_add_restrict_Ioc_Ioi {c H : ℝ} (hc : 0 < c) {K : CProf}
    (hKm : AEStronglyMeasurable K (hMeas c bgp)) :
    hNorm c bgp K ≤
      eLpNorm K (ENNReal.ofReal bgp) ((hMeas c bgp).restrict (Ioc 0 H ×ˢ univ)) +
      eLpNorm K (ENNReal.ofReal bgp) ((hMeas c bgp).restrict (Ioi H ×ˢ univ)) := by
  set A₁ : Set Coord := Ioc 0 H ×ˢ univ
  set A₂ : Set Coord := Ioi H ×ˢ univ
  have hA₁ : MeasurableSet A₁ := measurableSet_Ioc.prod MeasurableSet.univ
  have hA₂ : MeasurableSet A₂ := measurableSet_Ioi.prod MeasurableSet.univ
  have hr1 : (1 : ℝ≥0∞) ≤ ENNReal.ofReal bgp :=
    ENNReal.one_le_ofReal.2 (by norm_num [bgp])
  have hae : K =ᵐ[hMeas c bgp] fun x => A₁.indicator K x + A₂.indicator K x := by
    filter_upwards [Axi.ae_ageμ_mem hc (bgp / 2 - 5 / 2)] with x hx
    have hs : 0 < x.1 := hx.1
    rcases le_or_gt x.1 H with hle | hgt
    · have hm1 : x ∈ A₁ := ⟨⟨hs, hle⟩, trivial⟩
      have hm2 : x ∉ A₂ := fun h => (not_lt.2 hle) h.1
      simp [indicator_of_mem hm1, indicator_of_notMem hm2]
    · have hm1 : x ∉ A₁ := fun h => (not_le.2 hgt) h.1.2
      have hm2 : x ∈ A₂ := ⟨hgt, trivial⟩
      simp [indicator_of_notMem hm1, indicator_of_mem hm2]
  unfold hNorm
  rw [eLpNorm_congr_ae hae]
  calc eLpNorm (fun x => A₁.indicator K x + A₂.indicator K x) (ENNReal.ofReal bgp) (hMeas c bgp)
      ≤ eLpNorm (A₁.indicator K) (ENNReal.ofReal bgp) (hMeas c bgp) +
          eLpNorm (A₂.indicator K) (ENNReal.ofReal bgp) (hMeas c bgp) :=
        eLpNorm_add_le (hKm.indicator hA₁) (hKm.indicator hA₂) hr1
    _ = eLpNorm K (ENNReal.ofReal bgp) ((hMeas c bgp).restrict A₁) +
          eLpNorm K (ENNReal.ofReal bgp) ((hMeas c bgp).restrict A₂) := by
        rw [eLpNorm_indicator_eq_eLpNorm_restrict hA₁, eLpNorm_indicator_eq_eLpNorm_restrict hA₂]

lemma freeInteraction_hNorm_bound {p : Params} {Sig C_fi : ℝ} {k_fi : ℕ}
    (hSig : 0 < Sig) (hC_fi : 0 < C_fi) (hνSig : p.ν ≤ Sig) (hν1 : p.ν ≤ 1)
    (hage : p.ageCut = Sig)
    (hFI : ∀ F b0 : CProf, InHr p.c bgp F → InFlatClass p.c bgp b0 → IsFlatResponse p.ν 0 F b0 →
      ∃ b0q b0η : CProf,
        HasWeakVec vQ0 dZero b0 b0q ∧ HasWeakVec vEta dZero b0 b0η ∧
        InHr p.c bgp (flatK p.train b0 b0q b0η) ∧
        eLpNorm (flatK p.train b0 b0q b0η) (ENNReal.ofReal bgp)
            ((hMeas p.c bgp).restrict (Ioc 0 p.H ×ˢ univ)) ≤
          ENNReal.ofReal (C_fi * (p.ν ^ k_fi)⁻¹ * (p.ν ^ (-1 / 2 : ℝ) * Real.sqrt p.H + p.H)) *
            hNorm p.c bgp F ∧
        eLpNorm (flatK p.train b0 b0q b0η) (ENNReal.ofReal bgp)
            ((hMeas p.c bgp).restrict (Ioi p.H ×ˢ univ)) ≤
          ENNReal.ofReal
              (C_fi * (p.ν ^ k_fi)⁻¹ * p.H ^ (-1 / 2 : ℝ) * (p.ν ^ (-1 / 2 : ℝ) + 1)) *
            hNorm p.c bgp F)
    (F : HpR p.c) {b0 b0q b0η : CProf}
    (hb0_cl : InFlatClass p.c bgp b0)
    (hb0_resp : IsFlatResponse p.ν 0 (toProf p.c F) b0)
    (hb0q : HasWeakVec vQ0 dZero b0 b0q)
    (hb0η : HasWeakVec vEta dZero b0 b0η) :
    InHr p.c bgp (flatK p.train b0 b0q b0η) ∧
      hNorm p.c bgp (flatK p.train b0 b0q b0η) ≤
        ENNReal.ofReal (4 * (1 + Sig) * C_fi * (p.ν ^ (k_fi + 2))⁻¹ * ‖F‖) := by
  have hc : 0 < p.c := p.c_pos
  have hνpos : 0 < p.ν := p.ν_pos
  obtain ⟨b0q', b0η', hq', hη', hK'_inHr, hK'_early, hK'_late⟩ :=
    hFI (toProf p.c F) b0 (inHr_toProf hc F) hb0_cl hb0_resp
  have hq_vol : ∀ᵐ x : Coord, 0 < x.1 → b0q x = b0q' x :=
    GradBoundHelp.hasWeakVec_unique hb0q hq'
  have hη_vol : ∀ᵐ x : Coord, 0 < x.1 → b0η x = b0η' x :=
    GradBoundHelp.hasWeakVec_unique hb0η hη'
  have hK_vol : ∀ᵐ x : Coord, 0 < x.1 →
      flatK p.train b0 b0q b0η x = flatK p.train b0 b0q' b0η' x := by
    filter_upwards [hq_vol, hη_vol] with x hqx hηx hpos
    ext m
    simp only [flatK, WithLp.ofLp_toLp, hqx hpos, hηx hpos]
  have hK_vol_r : flatK p.train b0 b0q b0η =ᵐ[volume.restrict {x : Coord | 0 < x.1}]
      flatK p.train b0 b0q' b0η' :=
    (ae_restrict_iff' (measurableSet_lt measurable_const measurable_fst)).2 hK_vol
  have hK_per : QPeriodic p.c (flatK p.train b0 b0q b0η) :=
    F8L.qperiodic_congr hK_vol_r hK'_inHr.periodic
  have hK_ae : flatK p.train b0 b0q b0η =ᵐ[hMeas p.c bgp] flatK p.train b0 b0q' b0η' :=
    hMeasAe p.c bgp _ hc hK_vol
  have hK_inHr : InHr p.c bgp (flatK p.train b0 b0q b0η) :=
    inHr_congr_ae hK_per hK'_inHr hK_ae
  refine ⟨hK_inHr, ?_⟩
  have hnorm_eq : hNorm p.c bgp (flatK p.train b0 b0q b0η) =
      hNorm p.c bgp (flatK p.train b0 b0q' b0η') :=
    eLpNorm_congr_ae hK_ae
  rw [hnorm_eq]
  have hsplit := hNorm_le_add_restrict_Ioc_Ioi (H := p.H) hc hK'_inHr.meas
  have hHeq : p.H = Sig / p.ν := by simp [Params.H, hage]
  have hH1 : 1 ≤ p.H := by
    rw [hHeq, one_le_div hνpos]
    exact hνSig
  have hν_inv1 : 1 ≤ p.ν⁻¹ := (one_le_inv₀ hνpos).2 hν1
  have hν_rpow : p.ν ^ (-1 / 2 : ℝ) ≤ p.ν⁻¹ := by
    have h1 := Real.rpow_le_rpow_of_exponent_ge hνpos hν1 (by norm_num : (-1 : ℝ) ≤ -1 / 2)
    rwa [Real.rpow_neg_one] at h1
  have hH_sqrt : Real.sqrt p.H ≤ p.H := by
    rw [Real.sqrt_le_left (by linarith)]
    nlinarith
  have hH_rpow : p.H ^ (-1 / 2 : ℝ) ≤ 1 := by
    have h1 := Real.rpow_le_rpow_of_exponent_le hH1 (by norm_num : (-1 / 2 : ℝ) ≤ 0)
    rwa [Real.rpow_zero] at h1
  have hν_rpow_nn : 0 ≤ p.ν ^ (-1 / 2 : ℝ) := Real.rpow_nonneg hνpos.le _
  have hH_rpow_nn : 0 ≤ p.H ^ (-1 / 2 : ℝ) := Real.rpow_nonneg (by linarith) _
  have hEarly_c : C_fi * (p.ν ^ k_fi)⁻¹ * (p.ν ^ (-1 / 2 : ℝ) * Real.sqrt p.H + p.H) ≤
      2 * (1 + Sig) * C_fi * (p.ν ^ (k_fi + 2))⁻¹ := by
    have hp1 : p.ν ^ (-1 / 2 : ℝ) * Real.sqrt p.H + p.H ≤ 2 * Sig * (p.ν ^ 2)⁻¹ := by
      have hp0 : p.ν ^ (-1 / 2 : ℝ) * Real.sqrt p.H ≤ p.ν⁻¹ * p.H :=
        mul_le_mul hν_rpow hH_sqrt (Real.sqrt_nonneg _) (by positivity)
      have hH_mul : p.H = Sig * p.ν⁻¹ := by rw [hHeq, div_eq_mul_inv]
      have hν2 : (p.ν ^ 2)⁻¹ = p.ν⁻¹ * p.ν⁻¹ := by rw [sq, mul_inv]
      have hle2 : Sig * p.ν⁻¹ ≤ Sig * (p.ν⁻¹ * p.ν⁻¹) := by
        nlinarith [mul_le_mul_of_nonneg_left hν_inv1 (mul_nonneg hSig.le (inv_nonneg.2 hνpos.le))]
      rw [hH_mul] at hp0 ⊢
      rw [hν2]
      linarith
    have hpow : (p.ν ^ (k_fi + 2))⁻¹ = (p.ν ^ k_fi)⁻¹ * (p.ν ^ 2)⁻¹ := by
      rw [pow_add, mul_inv]
    calc C_fi * (p.ν ^ k_fi)⁻¹ * (p.ν ^ (-1 / 2 : ℝ) * Real.sqrt p.H + p.H)
        ≤ C_fi * (p.ν ^ k_fi)⁻¹ * (2 * Sig * (p.ν ^ 2)⁻¹) :=
          mul_le_mul_of_nonneg_left hp1 (by positivity)
      _ ≤ C_fi * (p.ν ^ k_fi)⁻¹ * (2 * (1 + Sig) * (p.ν ^ 2)⁻¹) := by
          gcongr; linarith
      _ = 2 * (1 + Sig) * C_fi * (p.ν ^ (k_fi + 2))⁻¹ := by
          rw [hpow]; ring
  have hLate_c : C_fi * (p.ν ^ k_fi)⁻¹ * p.H ^ (-1 / 2 : ℝ) * (p.ν ^ (-1 / 2 : ℝ) + 1) ≤
      2 * (1 + Sig) * C_fi * (p.ν ^ (k_fi + 2))⁻¹ := by
    have hp1 : p.H ^ (-1 / 2 : ℝ) * (p.ν ^ (-1 / 2 : ℝ) + 1) ≤ 2 * (p.ν ^ 2)⁻¹ := by
      have ha : p.H ^ (-1 / 2 : ℝ) * (p.ν ^ (-1 / 2 : ℝ) + 1) ≤ 1 * (p.ν⁻¹ + p.ν⁻¹) :=
        mul_le_mul hH_rpow (add_le_add hν_rpow hν_inv1) (by positivity) zero_le_one
      have hν2 : (p.ν ^ 2)⁻¹ = p.ν⁻¹ * p.ν⁻¹ := by rw [sq, mul_inv]
      have hb : p.ν⁻¹ ≤ p.ν⁻¹ * p.ν⁻¹ :=
        le_mul_of_one_le_right (inv_nonneg.2 hνpos.le) hν_inv1
      rw [hν2]
      linarith
    have hpow : (p.ν ^ (k_fi + 2))⁻¹ = (p.ν ^ k_fi)⁻¹ * (p.ν ^ 2)⁻¹ := by
      rw [pow_add, mul_inv]
    calc C_fi * (p.ν ^ k_fi)⁻¹ * p.H ^ (-1 / 2 : ℝ) * (p.ν ^ (-1 / 2 : ℝ) + 1)
        = C_fi * (p.ν ^ k_fi)⁻¹ * (p.H ^ (-1 / 2 : ℝ) * (p.ν ^ (-1 / 2 : ℝ) + 1)) := by ring
      _ ≤ C_fi * (p.ν ^ k_fi)⁻¹ * (2 * (p.ν ^ 2)⁻¹) :=
          mul_le_mul_of_nonneg_left hp1 (by positivity)
      _ ≤ C_fi * (p.ν ^ k_fi)⁻¹ * (2 * (1 + Sig) * (p.ν ^ 2)⁻¹) := by
          gcongr; linarith
      _ = 2 * (1 + Sig) * C_fi * (p.ν ^ (k_fi + 2))⁻¹ := by
          rw [hpow]; ring
  have hF_norm : hNorm p.c bgp (toProf p.c F) = ENNReal.ofReal ‖F‖ := by
    rw [hNorm_toProf hc F, ofReal_norm]
  set B : ℝ := 2 * (1 + Sig) * C_fi * (p.ν ^ (k_fi + 2))⁻¹
  have hB0 : 0 ≤ B := by positivity
  calc hNorm p.c bgp (flatK p.train b0 b0q' b0η')
      ≤ eLpNorm (flatK p.train b0 b0q' b0η') (ENNReal.ofReal bgp)
            ((hMeas p.c bgp).restrict (Ioc 0 p.H ×ˢ univ)) +
          eLpNorm (flatK p.train b0 b0q' b0η') (ENNReal.ofReal bgp)
            ((hMeas p.c bgp).restrict (Ioi p.H ×ˢ univ)) := hsplit
    _ ≤ ENNReal.ofReal B * ENNReal.ofReal ‖F‖ + ENNReal.ofReal B * ENNReal.ofReal ‖F‖ := by
        rw [← hF_norm]
        exact add_le_add
          (hK'_early.trans (mul_le_mul_of_nonneg_right (ENNReal.ofReal_le_ofReal hEarly_c) zero_le))
          (hK'_late.trans (mul_le_mul_of_nonneg_right (ENNReal.ofReal_le_ofReal hLate_c) zero_le))
    _ = ENNReal.ofReal (4 * (1 + Sig) * C_fi * (p.ν ^ (k_fi + 2))⁻¹ * ‖F‖) := by
        rw [← ENNReal.ofReal_mul hB0, ← ENNReal.ofReal_add (mul_nonneg hB0 (norm_nonneg F))
          (mul_nonneg hB0 (norm_nonneg F))]
        congr 1
        dsimp only [B]
        ring

lemma inHr_sub_of {c r : ℝ} (hr : 1 ≤ r) {f g : CProf} (hf : InHr c r f) (hg : InHr c r g) :
    InHr c r (fun x => f x - g x) := by
  have hneg : InHr c r (fun x => (-1 : ℂ) • g x) := inHr_const_smul_of (-1) hg
  have heq : (fun x => f x - g x) = fun x => f x + (-1 : ℂ) • g x := by
    funext x; ext i; simp [sub_eq_add_neg]
  rw [heq]
  exact inHr_add_of hr hf hneg

lemma eLpNorm_add_le' {c : ℝ} {f g : CProf}
    (hf : AEStronglyMeasurable f (hMeas c bgp))
    (hg : AEStronglyMeasurable g (hMeas c bgp)) :
    hNorm c bgp (fun x => f x + g x) ≤ hNorm c bgp f + hNorm c bgp g :=
  eLpNorm_add_le hf hg (ENNReal.one_le_ofReal.2 (by norm_num [bgp]))

lemma eLpNorm_sub_le' {c : ℝ} {f g : CProf}
    (hf : AEStronglyMeasurable f (hMeas c bgp))
    (hg : AEStronglyMeasurable g (hMeas c bgp)) :
    hNorm c bgp (fun x => f x - g x) ≤ hNorm c bgp f + hNorm c bgp g := by
  have heq : (fun x => f x - g x) = fun x => f x + (-g) x := by
    funext x; simp [sub_eq_add_neg]
  rw [heq]
  refine (eLpNorm_add_le' hf hg.neg).trans ?_
  have hneg : hNorm c bgp (-g) = hNorm c bgp g := eLpNorm_neg g _ _
  rw [hneg]

lemma hNorm_real_smul_le {c : ℝ} (r : ℝ) {u : CProf} {B : ℝ}
    (hu : hNorm c bgp u ≤ ENNReal.ofReal B) :
    hNorm c bgp (fun x => ((r : ℝ) : ℂ) • u x) ≤ ENNReal.ofReal (|r| * B) := by
  have h1 : hNorm c bgp (((r : ℝ) : ℂ) • u) ≤ ‖((r : ℝ) : ℂ)‖ₑ * hNorm c bgp u :=
    eLpNorm_const_smul_le
  have en : ‖((r : ℝ) : ℂ)‖ₑ = ENNReal.ofReal |r| := by
    rw [← ofReal_norm, Complex.norm_real, Real.norm_eq_abs]
  rw [en] at h1
  exact h1.trans ((mul_le_mul_of_nonneg_left hu zero_le).trans
    (le_of_eq (ENNReal.ofReal_mul (abs_nonneg r)).symm))

lemma memLp_reM_of_inHr {c : ℝ} {u : CProf} (hu : InHr c bgp u) (hre : reProf u = u) :
    MemLp (fun x => reM (u x)) (ENNReal.ofReal bgp) (hMeas c bgp) ∧
      eLpNorm (fun x => reM (u x)) (ENNReal.ofReal bgp) (hMeas c bgp) = hNorm c bgp u := by
  have heq : eLpNorm (fun x => reM (u x)) (ENNReal.ofReal bgp) (hMeas c bgp) = hNorm c bgp u := by
    unfold hNorm
    refine eLpNorm_congr_norm_ae (Eventually.of_forall fun x => ?_)
    have hx : liftM (reM (u x)) = u x := by
      change reProf u x = u x
      rw [hre]
    rw [← liftM_norm (reM (u x)), hx]
  exact ⟨⟨continuous_reM.comp_aestronglyMeasurable hu.meas, heq.symm ▸ hu.finite⟩, heq⟩

lemma norm_fin2_sum_le (α : E2) (M : ℝ) (hM : 0 ≤ M) :
    (|α 0| + |α 1|) * M ≤ 2 * ‖α‖ * M := by
  have h0 : |α 0| ≤ ‖α‖ := by simpa [Real.norm_eq_abs] using PiLp.norm_apply_le α (0 : Fin 2)
  have h1 : |α 1| ≤ ‖α‖ := by simpa [Real.norm_eq_abs] using PiLp.norm_apply_le α (1 : Fin 2)
  exact mul_le_mul_of_nonneg_right (by linarith) hM

lemma lift_ae_linear_to_HpR {c B : ℝ} (hc : 0 < c) (hB : 0 ≤ B)
    (rhsF : HpR c → CProf)
    (hre : ∀ F, reProf (rhsF F) = rhsF F)
    (hin : ∀ F, InHr c bgp (rhsF F))
    (hbd : ∀ F, hNorm c bgp (rhsF F) ≤ ENNReal.ofReal (B * ‖F‖))
    (hadd : ∀ F₁ F₂, rhsF (F₁ + F₂) =ᵐ[hMeas c bgp] fun x => rhsF F₁ x + rhsF F₂ x)
    (hsmul : ∀ (r : ℝ) F, rhsF (r • F) =ᵐ[hMeas c bgp] fun x => ((r : ℝ) : ℂ) • rhsF F x) :
    ∃ fCLM : HpR c →L[ℝ] HpR c,
      (∀ F, ‖fCLM F‖ ≤ B * ‖F‖) ∧
      (∀ F, toProf c (fCLM F) =ᵐ[hMeas c bgp] rhsF F) := by
  let fFun : HpR c → HpR c := fun F =>
    (memLp_reM_of_inHr (hin F) (hre F)).1.toLp (fun x => reM (rhsF F x))
  have hf_ae : ∀ F : HpR c, toProf c (fFun F) =ᵐ[hMeas c bgp] rhsF F := by
    intro F
    have hmem := (memLp_reM_of_inHr (hin F) (hre F)).1
    filter_upwards [toProf_ae_eq hc (fFun F), MemLp.coeFn_toLp hmem] with x h1 h2
    rw [h1, h2]
    change reProf (rhsF F) x = rhsF F x
    rw [hre F]
  have hf_norm : ∀ F : HpR c, ‖fFun F‖ ≤ B * ‖F‖ := by
    intro F
    obtain ⟨hmem, heq_n⟩ := memLp_reM_of_inHr (hin F) (hre F)
    have hBF_nn : 0 ≤ B * ‖F‖ := mul_nonneg hB (norm_nonneg F)
    have hen : ‖fFun F‖ₑ ≤ ENNReal.ofReal (B * ‖F‖) := by
      rw [Lp.enorm_def, eLpNorm_congr_ae (MemLp.coeFn_toLp hmem), heq_n]
      exact hbd F
    rw [← ofReal_norm] at hen
    exact (ENNReal.ofReal_le_ofReal_iff hBF_nn).1 hen
  have hf_add : ∀ F₁ F₂ : HpR c, fFun (F₁ + F₂) = fFun F₁ + fFun F₂ := by
    intro F₁ F₂
    apply toProf_eq_of_ae_eq hc
    have h12_add : toProf c (fFun F₁ + fFun F₂) =ᵐ[hMeas c bgp]
        fun x => toProf c (fFun F₁) x + toProf c (fFun F₂) x := by
      filter_upwards [toProf_ae_eq hc (fFun F₁ + fFun F₂), toProf_ae_eq hc (fFun F₁),
        toProf_ae_eq hc (fFun F₂), Lp.coeFn_add (fFun F₁) (fFun F₂)] with x e12 e1 e2 ea
      rw [e12, e1, e2, ea, Pi.add_apply, liftM_add']
    filter_upwards [hf_ae (F₁ + F₂), h12_add, hf_ae F₁, hf_ae F₂, hadd F₁ F₂]
      with x a12 hfa a1 a2 hr
    rw [a12, hfa, a1, a2, hr]
  have hf_smul : ∀ (r : ℝ) (F : HpR c), fFun (r • F) = r • fFun F := by
    intro r F
    apply toProf_eq_of_ae_eq hc
    have hr_smul : toProf c (r • fFun F) =ᵐ[hMeas c bgp]
        fun x => ((r : ℝ) : ℂ) • toProf c (fFun F) x := by
      filter_upwards [toProf_ae_eq hc (r • fFun F), toProf_ae_eq hc (fFun F),
        Lp.coeFn_smul r (fFun F)] with x e1 e2 es
      rw [e1, e2, es, Pi.smul_apply]
      ext m; simp [liftM]
    filter_upwards [hf_ae (r • F), hr_smul, hf_ae F, hsmul r F] with x ar hfs a hr
    rw [ar, hfs, a, hr]
  let fLM : HpR c →ₗ[ℝ] HpR c :=
    { toFun := fFun
      map_add' := hf_add
      map_smul' := hf_smul }
  exact ⟨fLM.mkContinuous B hf_norm, hf_norm, hf_ae⟩

lemma pair_with_E2_to_RowSpace {c B₁ B₂ : ℝ} (hB₁ : 0 ≤ B₁) (hB₂ : 0 ≤ B₂)
    (fCLM : HpR c →L[ℝ] HpR c) (hf : ∀ F, ‖fCLM F‖ ≤ B₁ * ‖F‖)
    (αMap : HpR c →L[ℝ] E2) (hα : ∀ F, ‖αMap F‖ ≤ B₂ * ‖F‖) :
    ∃ R0 : HpR c →L[ℝ] RowSpace c,
      ‖R0‖ ≤ B₁ + B₂ ∧
      (∀ F, (WithLp.fstL 1 ℝ (HpR c) E2) (R0 F) = fCLM F ∧
        (WithLp.sndL 1 ℝ (HpR c) E2) (R0 F) = αMap F) := by
  let R0 : HpR c →L[ℝ] RowSpace c :=
    (WithLp.prodContinuousLinearEquiv 1 ℝ (HpR c) E2).symm.toContinuousLinearMap.comp
      (fCLM.prod αMap)
  refine ⟨R0, ?_, fun _ => ⟨rfl, rfl⟩⟩
  refine ContinuousLinearMap.opNorm_le_bound R0 (add_nonneg hB₁ hB₂) fun F => ?_
  have hnorm_row : ‖R0 F‖ = ‖fCLM F‖ + ‖αMap F‖ := by
    rw [WithLp.prod_norm_eq_of_L1]
    rfl
  rw [hnorm_row, add_mul]
  exact add_le_add (hf F) (hα F)

lemma rhs_inHr_and_norm {p : Params} {Sig C_fi C_ls C_hd E_exp : ℝ}
    {k_fi k_ls k_hd K_max : ℕ}
    (hSig : 0 < Sig) (hCfi : 0 < C_fi) (hCls : 0 < C_ls) (hChd : 0 < C_hd)
    (hν1 : p.ν ≤ 1) (hE_ge1 : 1 ≤ E_exp)
    (hK1 : k_fi + 2 ≤ K_max) (hK2 : k_ls + k_hd ≤ K_max)
    (F : HpR p.c) (α : E2)
    (hα_le : ‖α‖ ≤ C_ls * (p.ν ^ k_ls)⁻¹ * E_exp * ‖F‖)
    {Kb0 Kz hd0 hd1 rhs : CProf}
    (hrhs_eq : rhs = fun x =>
      toProf p.c F x - Kb0 x - Kz x +
        (((α 0 : ℝ) : ℂ) • hd0 x + ((α 1 : ℝ) : ℂ) • hd1 x))
    (hKb0 : InHr p.c bgp Kb0 ∧
      hNorm p.c bgp Kb0 ≤ ENNReal.ofReal (4 * (1 + Sig) * C_fi * (p.ν ^ (k_fi + 2))⁻¹ * ‖F‖))
    (hKz_in : InHr p.c bgp Kz)
    (hKz_n : hNorm p.c bgp Kz ≤ ENNReal.ofReal (C_ls * (p.ν ^ k_ls)⁻¹ * E_exp * ‖F‖))
    (hhd0 : InHr p.c bgp hd0 ∧ hNorm p.c bgp hd0 ≤ ENNReal.ofReal (C_hd * (p.ν ^ k_hd)⁻¹))
    (hhd1 : InHr p.c bgp hd1 ∧ hNorm p.c bgp hd1 ≤ ENNReal.ofReal (C_hd * (p.ν ^ k_hd)⁻¹)) :
    InHr p.c bgp rhs ∧
      hNorm p.c bgp rhs ≤
        ENNReal.ofReal ((1 + 4 * (1 + Sig) * C_fi + C_ls + 2 * C_hd * C_ls) *
          (p.ν ^ K_max)⁻¹ * E_exp * ‖F‖) := by
  have hc : 0 < p.c := p.c_pos
  have hνpos : 0 < p.ν := p.ν_pos
  have hE_pos : 0 < E_exp := lt_of_lt_of_le one_pos hE_ge1
  have pow_inv_mono : ∀ {m n : ℕ}, m ≤ n → (p.ν ^ m)⁻¹ ≤ (p.ν ^ n)⁻¹ := fun hmn =>
    inv_anti₀ (pow_pos hνpos _) (pow_le_pow_of_le_one hνpos.le hν1 hmn)
  have hr1 : (1 : ℝ) ≤ bgp := by norm_num [bgp]
  have hTF_inHr : InHr p.c bgp (toProf p.c F) := inHr_toProf hc F
  have h12_inHr : InHr p.c bgp (fun x => toProf p.c F x - Kb0 x) :=
    inHr_sub_of hr1 hTF_inHr hKb0.1
  have h123_inHr : InHr p.c bgp (fun x => toProf p.c F x - Kb0 x - Kz x) :=
    inHr_sub_of hr1 h12_inHr hKz_in
  have hs0_in : InHr p.c bgp (fun x => ((α 0 : ℝ) : ℂ) • hd0 x) :=
    inHr_const_smul_of _ hhd0.1
  have hs1_in : InHr p.c bgp (fun x => ((α 1 : ℝ) : ℂ) • hd1 x) :=
    inHr_const_smul_of _ hhd1.1
  have hhd_sum_inHr : InHr p.c bgp
      (fun x => ((α 0 : ℝ) : ℂ) • hd0 x + ((α 1 : ℝ) : ℂ) • hd1 x) :=
    inHr_add_of hr1 hs0_in hs1_in
  have hrhs_inHr : InHr p.c bgp rhs := by
    rw [hrhs_eq]
    exact inHr_add_of hr1 h123_inHr hhd_sum_inHr
  set M_z : ℝ := C_ls * (p.ν ^ k_ls)⁻¹ * E_exp * ‖F‖
  have hTF_norm : hNorm p.c bgp (toProf p.c F) ≤
      ENNReal.ofReal (1 * ((p.ν ^ K_max)⁻¹ * E_exp * ‖F‖)) := by
    rw [hNorm_toProf hc F, ← ofReal_norm]
    apply ENNReal.ofReal_le_ofReal
    have hk1 : 1 ≤ (p.ν ^ K_max)⁻¹ := by simpa using pow_inv_mono (Nat.zero_le K_max)
    have h1E : 1 ≤ (p.ν ^ K_max)⁻¹ * E_exp := one_le_mul_of_one_le_of_one_le hk1 hE_ge1
    nlinarith [norm_nonneg F]
  have hKb0_norm' : hNorm p.c bgp Kb0 ≤
      ENNReal.ofReal ((4 * (1 + Sig) * C_fi) * ((p.ν ^ K_max)⁻¹ * E_exp * ‖F‖)) := by
    refine hKb0.2.trans (ENNReal.ofReal_le_ofReal ?_)
    have hk : (p.ν ^ (k_fi + 2))⁻¹ ≤ (p.ν ^ K_max)⁻¹ := pow_inv_mono hK1
    have hmul : (p.ν ^ (k_fi + 2))⁻¹ * 1 ≤ (p.ν ^ K_max)⁻¹ * E_exp :=
      mul_le_mul hk hE_ge1 zero_le_one (by positivity)
    have hpos_c : 0 ≤ 4 * (1 + Sig) * C_fi * ‖F‖ := by positivity
    have h2 := mul_le_mul_of_nonneg_left hmul hpos_c
    linarith [show 4 * (1 + Sig) * C_fi * ‖F‖ * ((p.ν ^ (k_fi + 2))⁻¹ * 1) =
        4 * (1 + Sig) * C_fi * (p.ν ^ (k_fi + 2))⁻¹ * ‖F‖ by ring,
      show 4 * (1 + Sig) * C_fi * ‖F‖ * ((p.ν ^ K_max)⁻¹ * E_exp) =
        (4 * (1 + Sig) * C_fi) * ((p.ν ^ K_max)⁻¹ * E_exp * ‖F‖) by ring]
  have hKzF_norm' : hNorm p.c bgp Kz ≤
      ENNReal.ofReal (C_ls * ((p.ν ^ K_max)⁻¹ * E_exp * ‖F‖)) := by
    refine hKz_n.trans (ENNReal.ofReal_le_ofReal ?_)
    have hk : (p.ν ^ k_ls)⁻¹ ≤ (p.ν ^ K_max)⁻¹ :=
      pow_inv_mono ((Nat.le_add_right k_ls k_hd).trans hK2)
    have h1 : C_ls * (p.ν ^ k_ls)⁻¹ * E_exp * ‖F‖ ≤ C_ls * (p.ν ^ K_max)⁻¹ * E_exp * ‖F‖ := by
      gcongr
    linarith
  have hhd_norm' : hNorm p.c bgp
      (fun x => ((α 0 : ℝ) : ℂ) • hd0 x + ((α 1 : ℝ) : ℂ) • hd1 x) ≤
      ENNReal.ofReal ((2 * C_hd * C_ls) * ((p.ν ^ K_max)⁻¹ * E_exp * ‖F‖)) := by
    have hs0 := hNorm_real_smul_le (α 0) hhd0.2
    have hs1 := hNorm_real_smul_le (α 1) hhd1.2
    calc hNorm p.c bgp (fun x => ((α 0 : ℝ) : ℂ) • hd0 x + ((α 1 : ℝ) : ℂ) • hd1 x)
        ≤ hNorm p.c bgp (fun x => ((α 0 : ℝ) : ℂ) • hd0 x) +
            hNorm p.c bgp (fun x => ((α 1 : ℝ) : ℂ) • hd1 x) :=
          eLpNorm_add_le' hs0_in.meas hs1_in.meas
      _ ≤ ENNReal.ofReal (|α 0| * (C_hd * (p.ν ^ k_hd)⁻¹)) +
            ENNReal.ofReal (|α 1| * (C_hd * (p.ν ^ k_hd)⁻¹)) := add_le_add hs0 hs1
      _ = ENNReal.ofReal ((|α 0| + |α 1|) * (C_hd * (p.ν ^ k_hd)⁻¹)) := by
          rw [← ENNReal.ofReal_add (by positivity) (by positivity), add_mul]
      _ ≤ ENNReal.ofReal ((2 * C_hd * C_ls) * ((p.ν ^ K_max)⁻¹ * E_exp * ‖F‖)) := by
          apply ENNReal.ofReal_le_ofReal
          have hαsum := norm_fin2_sum_le α (C_hd * (p.ν ^ k_hd)⁻¹) (by positivity)
          have hαM : 2 * ‖α‖ * (C_hd * (p.ν ^ k_hd)⁻¹) ≤
              2 * M_z * (C_hd * (p.ν ^ k_hd)⁻¹) := by gcongr
          have hk : (p.ν ^ k_ls)⁻¹ * (p.ν ^ k_hd)⁻¹ ≤ (p.ν ^ K_max)⁻¹ := by
            rw [← mul_inv, ← pow_add]
            exact pow_inv_mono hK2
          have hprod : 2 * M_z * (C_hd * (p.ν ^ k_hd)⁻¹) =
              2 * C_hd * C_ls * E_exp * ‖F‖ * ((p.ν ^ k_ls)⁻¹ * (p.ν ^ k_hd)⁻¹) := by
            dsimp only [M_z]; ring
          have hkr : 2 * C_hd * C_ls * E_exp * ‖F‖ * ((p.ν ^ k_ls)⁻¹ * (p.ν ^ k_hd)⁻¹) ≤
              2 * C_hd * C_ls * E_exp * ‖F‖ * (p.ν ^ K_max)⁻¹ :=
            mul_le_mul_of_nonneg_left hk (by positivity)
          linarith [show 2 * C_hd * C_ls * E_exp * ‖F‖ * (p.ν ^ K_max)⁻¹ =
              (2 * C_hd * C_ls) * ((p.ν ^ K_max)⁻¹ * E_exp * ‖F‖) by ring]
  refine ⟨hrhs_inHr, ?_⟩
  have h12_le := eLpNorm_sub_le' hTF_inHr.meas hKb0.1.meas
  have h123_le := (eLpNorm_sub_le' h12_inHr.meas hKz_in.meas).trans (add_le_add h12_le le_rfl)
  have htot_le : hNorm p.c bgp rhs ≤
      hNorm p.c bgp (toProf p.c F) + hNorm p.c bgp Kb0 + hNorm p.c bgp Kz +
        hNorm p.c bgp (fun x => ((α 0 : ℝ) : ℂ) • hd0 x + ((α 1 : ℝ) : ℂ) • hd1 x) := by
    rw [hrhs_eq]
    exact (eLpNorm_add_le' h123_inHr.meas hhd_sum_inHr.meas).trans (add_le_add h123_le le_rfl)
  refine htot_le.trans ((add_le_add (add_le_add (add_le_add hTF_norm hKb0_norm')
    hKzF_norm') hhd_norm').trans ?_)
  rw [← ENNReal.ofReal_add (by positivity) (by positivity),
    ← ENNReal.ofReal_add (by positivity) (by positivity),
    ← ENNReal.ofReal_add (by positivity) (by positivity)]
  exact le_of_eq (by congr 1; ring)

end LinearR0Help

/-- **Unconditional proof of Sub-step 1 (`FlatReconstructionLinearR0Step`)**. -/
theorem flatReconstructionLinearR0Step_proof : FlatReconstructionLinearR0Step := by
  intro C_late hCl Sig lam q hSig hq a' ha' _ha'lt dm dp hdm
    _C_ge _k_ge C_ls k_ls _C_fl C_fi k_fi _C_col _k_col
    _hCge hCls _hCfl hCfi _hCcol
  obtain ⟨C_hd, k_hd, ν_hd, hC_hd, hν_hd, hν_hd1, H_hd⟩ :=
    LinearR0Help.inletHeatDiff_bound Sig lam q hSig hq dm dp hdm
  set K_max : ℕ := max (k_fi + 2) (k_ls + k_hd)
  set C_f : ℝ := 1 + 4 * (1 + Sig) * C_fi + C_ls + 2 * C_hd * C_ls
  set C_tot : ℝ := C_f + C_ls
  set ν₀ : ℝ := min (1 / 2) (min Sig ν_hd)
  have hC_f : 0 < C_f := by positivity
  have hC_tot : 0 < C_tot := by positivity
  have hν₀_pos : 0 < ν₀ := lt_min (by norm_num) (lt_min hSig hν_hd)
  have hν₀_half : ν₀ ≤ 1 / 2 := min_le_left _ _
  refine ⟨C_tot, K_max, ν₀, hC_tot, hν₀_pos, hν₀_half, ?_⟩
  intro p d hreg hνle hage hmode hFI _hCol hLS
  have hc : 0 < p.c := p.c_pos
  have hνpos : 0 < p.ν := p.ν_pos
  have hν_half : p.ν ≤ 1 / 2 := hνle.trans hν₀_half
  have hν1 : p.ν ≤ 1 := hν_half.trans (by norm_num)
  have hνSig : p.ν ≤ Sig := hνle.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hν_hd_le : p.ν ≤ ν_hd := hνle.trans ((min_le_right _ _).trans (min_le_right _ _))
  have hhd0 := H_hd p d hreg hν_hd_le hage hmode 0
  have hhd1 := H_hd p d hreg hν_hd_le hage hmode 1
  obtain ⟨αMap, b0Of, b0qOf, b0ηOf, gOf, gqOf, gηOf, zOf, zqOf, zηOf, D2zOf, hLS_spec⟩ := hLS
  let b0F : HpR p.c →ₗ[ℝ] CProf := LinearR0Help.reProfLM.comp b0Of
  let b0qF : HpR p.c →ₗ[ℝ] CProf := LinearR0Help.reProfLM.comp b0qOf
  let b0ηF : HpR p.c →ₗ[ℝ] CProf := LinearR0Help.reProfLM.comp b0ηOf
  let gF : HpR p.c →ₗ[ℝ] CProf := LinearR0Help.reProfLM.comp gOf
  let zF : HpR p.c →ₗ[ℝ] CProf := LinearR0Help.reProfLM.comp zOf
  let zqF : HpR p.c →ₗ[ℝ] CProf := LinearR0Help.reProfLM.comp zqOf
  let zηF : HpR p.c →ₗ[ℝ] CProf := LinearR0Help.reProfLM.comp zηOf
  set E_exp : ℝ := Real.exp ((a' * Sig + C_late / (1 + Sig)) / p.ν + C_late * p.ν ^ 3)
  have hE_ge1 : 1 ≤ E_exp := Real.one_le_exp (by positivity)
  have hE_pos : 0 < E_exp := Real.exp_pos _
  have pow_inv_mono : ∀ {m n : ℕ}, m ≤ n → (p.ν ^ m)⁻¹ ≤ (p.ν ^ n)⁻¹ := by
    intro m n hmn
    exact inv_anti₀ (pow_pos hνpos n) (pow_le_pow_of_le_one hνpos.le hν1 hmn)
  let rhsF : HpR p.c → CProf := fun F x =>
    toProf p.c F x -
      flatK p.train (fun y => b0F F y + zF F y - inletProf p (αMap F) y)
        (fun y => b0qF F y + zqF F y - inletProfQ p (αMap F) y)
        (fun y => b0ηF F y + zηF F y - inletProfEta p (αMap F) y) x -
      ∑ i : Fin 2, ((αMap F i : ℝ) : ℂ) • flatColumn p i x
  have hrhsF_split : ∀ F : HpR p.c, rhsF F = fun x =>
      toProf p.c F x - flatK p.train (b0F F) (b0qF F) (b0ηF F) x -
        flatK p.train (zF F) (zqF F) (zηF F) x +
        (((αMap F 0 : ℝ) : ℂ) • LinearR0Help.inletHeatDiff p 0 x +
          ((αMap F 1 : ℝ) : ℂ) • LinearR0Help.inletHeatDiff p 1 x) := by
    intro F
    funext x
    have hsub := GlobalIdHelp.flatK_sub p.train
      (fun y => b0F F y + zF F y) (fun y => b0qF F y + zqF F y) (fun y => b0ηF F y + zηF F y)
      (inletProf p (αMap F)) (inletProfQ p (αMap F)) (inletProfEta p (αMap F)) x
    have hadd := GlobalIdHelp.flatK_add p.train (b0F F) (b0qF F) (b0ηF F) (zF F) (zqF F) (zηF F) x
    have heP : inletProf p (αMap F) = fun z =>
        ((αMap F 0 : ℝ) : ℂ) • cplx (inletE0 p 0) z +
          ((αMap F 1 : ℝ) : ℂ) • cplx (inletE0 p 1) z := by
      ext z m; simp [inletProf, Fin.sum_univ_two]
    have heQ : inletProfQ p (αMap F) = fun z =>
        ((αMap F 0 : ℝ) : ℂ) • cplx (Axi.dQ (inletE0 p 0)) z +
          ((αMap F 1 : ℝ) : ℂ) • cplx (Axi.dQ (inletE0 p 1)) z := by
      ext z m; simp [inletProfQ, Fin.sum_univ_two]
    have heE : inletProfEta p (αMap F) = fun z =>
        ((αMap F 0 : ℝ) : ℂ) • cplx (Axi.dEta (inletE0 p 0)) z +
          ((αMap F 1 : ℝ) : ℂ) • cplx (Axi.dEta (inletE0 p 1)) z := by
      ext z m; simp [inletProfEta, Fin.sum_univ_two]
    have hinK : flatK p.train (inletProf p (αMap F)) (inletProfQ p (αMap F))
        (inletProfEta p (αMap F)) x -
        ∑ i : Fin 2, ((αMap F i : ℝ) : ℂ) • flatColumn p i x =
        ((αMap F 0 : ℝ) : ℂ) • LinearR0Help.inletHeatDiff p 0 x +
          ((αMap F 1 : ℝ) : ℂ) • LinearR0Help.inletHeatDiff p 1 x := by
      rw [heP, heQ, heE, GlobalIdHelp.flatK_add, GlobalIdHelp.flatK_smul_complex,
        GlobalIdHelp.flatK_smul_complex, Fin.sum_univ_two]
      ext m
      simp only [LinearR0Help.inletHeatDiff, PiLp.sub_apply, PiLp.add_apply, PiLp.smul_apply,
        smul_eq_mul]
      ring
    dsimp only [rhsF]
    rw [hsub, hadd]
    ext m
    have hm := congrArg (fun v : CMerid => v m) hinK
    simp only [PiLp.sub_apply, PiLp.add_apply] at hm ⊢
    linear_combination hm
  have hrhsF_re : ∀ F : HpR p.c, LinearR0Help.reProf (rhsF F) = rhsF F := by
    intro F
    rw [hrhsF_split F]
    have hre_b0 : LinearR0Help.reProf (flatK p.train (b0F F) (b0qF F) (b0ηF F)) =
        flatK p.train (b0F F) (b0qF F) (b0ηF F) := by
      rw [LinearR0Help.reProf_flatK]
      simp only [b0F, b0qF, b0ηF, LinearMap.comp_apply, LinearR0Help.reProfLM,
        LinearMap.coe_mk, AddHom.coe_mk, LinearR0Help.reProf_idem]
    have hre_z : LinearR0Help.reProf (flatK p.train (zF F) (zqF F) (zηF F)) =
        flatK p.train (zF F) (zqF F) (zηF F) := by
      rw [LinearR0Help.reProf_flatK]
      simp only [zF, zqF, zηF, LinearMap.comp_apply, LinearR0Help.reProfLM,
        LinearMap.coe_mk, AddHom.coe_mk, LinearR0Help.reProf_idem]
    have hre_hd : ∀ j : Fin 2,
        LinearR0Help.reProf (LinearR0Help.inletHeatDiff p j) = LinearR0Help.inletHeatDiff p j := by
      intro j
      rw [LinearR0Help.inletHeatDiff_eq_cplx]
      exact LinearR0Help.reProf_cplx _
    ext x i
    rw [LinearR0Help.reProf_apply]
    simp only [PiLp.add_apply, PiLp.sub_apply, PiLp.smul_apply, smul_eq_mul,
      map_add, map_sub, LinearR0Help.reCLM_ofReal_mul]
    have hTF := congrArg (fun u : CProf => u x i) (LinearR0Help.reProf_toProf p.c F)
    have hKb := congrArg (fun u : CProf => u x i) hre_b0
    have hKz := congrArg (fun u : CProf => u x i) hre_z
    have hhd0' := congrArg (fun u : CProf => u x i) (hre_hd 0)
    have hhd1' := congrArg (fun u : CProf => u x i) (hre_hd 1)
    simp only [LinearR0Help.reProf_apply] at hTF hKb hKz hhd0' hhd1'
    rw [hTF, hKb, hKz, hhd0', hhd1']
  have hα_le_z : ∀ F : HpR p.c, ‖αMap F‖ ≤ C_ls * (p.ν ^ k_ls)⁻¹ * E_exp * ‖F‖ := by
    intro F
    obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hH1_α, _, _, _, _⟩ := hLS_spec F
    have h1 : ENNReal.ofReal ‖αMap F‖ ≤
        ENNReal.ofReal (C_ls * (p.ν ^ k_ls)⁻¹ * E_exp * ‖F‖) :=
      (le_add_self).trans (hH1_α 1 one_pos)
    exact (ENNReal.ofReal_le_ofReal_iff (by positivity)).1 h1
  have hrhs_both : ∀ F : HpR p.c,
      InHr p.c bgp (rhsF F) ∧
        hNorm p.c bgp (rhsF F) ≤ ENNReal.ofReal (C_f * (p.ν ^ K_max)⁻¹ * E_exp * ‖F‖) := by
    intro F
    obtain ⟨hb0_cl, hb0_resp, hb0q, hb0η, _, _, _, _, _, _, _, _, _, _, _, _, _, _,
      hKz_inHr, hKz_norm⟩ := hLS_spec F
    have hb0F_cl : InFlatClass p.c bgp (b0F F) := LinearR0Help.inFlatClass_reProf hb0_cl
    have hb0F_resp : IsFlatResponse p.ν 0 (toProf p.c F) (b0F F) := by
      have h := LinearR0Help.isFlatResponse_zero_reProf hb0_resp
      rwa [LinearR0Help.reProf_toProf] at h
    have hb0qF_w : HasWeakVec vQ0 dZero (b0F F) (b0qF F) := LinearR0Help.hasWeakVec_reProf hb0q
    have hb0ηF_w : HasWeakVec vEta dZero (b0F F) (b0ηF F) := LinearR0Help.hasWeakVec_reProf hb0η
    have hKb0 := LinearR0Help.freeInteraction_hNorm_bound hSig hCfi hνSig hν1 hage hFI F
      hb0F_cl hb0F_resp hb0qF_w hb0ηF_w
    have hKzF_eq : flatK p.train (zF F) (zqF F) (zηF F) =
        LinearR0Help.reProf (flatK p.train (zOf F) (zqOf F) (zηOf F)) :=
      (LinearR0Help.reProf_flatK p.train (zOf F) (zqOf F) (zηOf F)).symm
    have hKzF_inHr : InHr p.c bgp (flatK p.train (zF F) (zqF F) (zηF F)) := by
      rw [hKzF_eq]; exact LinearR0Help.inHr_reProf hKz_inHr
    have hKzF_norm : hNorm p.c bgp (flatK p.train (zF F) (zqF F) (zηF F)) ≤
        ENNReal.ofReal (C_ls * (p.ν ^ k_ls)⁻¹ * E_exp * ‖F‖) := by
      rw [hKzF_eq]
      exact (LinearR0Help.hNorm_reProf_le p.c bgp _).trans hKz_norm
    exact LinearR0Help.rhs_inHr_and_norm hSig hCfi hCls hC_hd hν1 hE_ge1
      (le_max_left _ _) (le_max_right _ _) F (αMap F) (hα_le_z F) (hrhsF_split F)
      hKb0 hKzF_inHr hKzF_norm hhd0 hhd1
  have hrhs_add : ∀ F₁ F₂ : HpR p.c,
      rhsF (F₁ + F₂) =ᵐ[hMeas p.c bgp] fun x => rhsF F₁ x + rhsF F₂ x := by
    intro F₁ F₂
    have hTF_add : toProf p.c (F₁ + F₂) =ᵐ[hMeas p.c bgp]
        fun x => toProf p.c F₁ x + toProf p.c F₂ x := by
      filter_upwards [toProf_ae_eq hc (F₁ + F₂), toProf_ae_eq hc F₁, toProf_ae_eq hc F₂,
        Lp.coeFn_add F₁ F₂] with x h12 h1 h2 hadd
      rw [h12, h1, h2, hadd, Pi.add_apply, liftM_add']
    have hadd_prof : ∀ (L : HpR p.c →ₗ[ℝ] CProf),
        L (F₁ + F₂) = fun y => L F₁ y + L F₂ y := fun L => by
      rw [L.map_add]; rfl
    filter_upwards [hTF_add] with x hTFa
    rw [hrhsF_split (F₁ + F₂), hrhsF_split F₁, hrhsF_split F₂]
    dsimp only
    rw [hTFa, hadd_prof b0F, hadd_prof b0qF, hadd_prof b0ηF,
      GlobalIdHelp.flatK_add p.train (b0F F₁) (b0qF F₁) (b0ηF F₁) (b0F F₂) (b0qF F₂) (b0ηF F₂) x,
      hadd_prof zF, hadd_prof zqF, hadd_prof zηF,
      GlobalIdHelp.flatK_add p.train (zF F₁) (zqF F₁) (zηF F₁) (zF F₂) (zqF F₂) (zηF F₂) x,
      map_add αMap]
    ext m
    simp only [PiLp.add_apply, PiLp.sub_apply, PiLp.smul_apply, smul_eq_mul, Complex.ofReal_add]
    ring
  have hrhs_smul : ∀ (r : ℝ) (F : HpR p.c),
      rhsF (r • F) =ᵐ[hMeas p.c bgp] fun x => ((r : ℝ) : ℂ) • rhsF F x := by
    intro r F
    have hTF_smul : toProf p.c (r • F) =ᵐ[hMeas p.c bgp]
        fun x => ((r : ℝ) : ℂ) • toProf p.c F x := by
      filter_upwards [toProf_ae_eq hc (r • F), toProf_ae_eq hc F, Lp.coeFn_smul r F]
        with x h1 h2 hsm
      rw [h1, h2, hsm, Pi.smul_apply]
      ext m; simp [liftM]
    have hsmul_prof : ∀ (L : HpR p.c →ₗ[ℝ] CProf),
        L (r • F) = fun y => ((r : ℝ) : ℂ) • L F y := by
      intro L
      rw [L.map_smul]
      funext y; ext m
      simp [Complex.real_smul]
    filter_upwards [hTF_smul] with x hTFs
    rw [hrhsF_split (r • F), hrhsF_split F]
    dsimp only
    rw [hTFs, hsmul_prof b0F, hsmul_prof b0qF, hsmul_prof b0ηF,
      GlobalIdHelp.flatK_smul_complex p.train ((r : ℝ) : ℂ) (b0F F) (b0qF F) (b0ηF F) x,
      hsmul_prof zF, hsmul_prof zqF, hsmul_prof zηF,
      GlobalIdHelp.flatK_smul_complex p.train ((r : ℝ) : ℂ) (zF F) (zqF F) (zηF F) x,
      αMap.map_smul]
    ext m
    simp only [PiLp.add_apply, PiLp.sub_apply, PiLp.smul_apply, smul_eq_mul, Complex.ofReal_mul]
    ring
  obtain ⟨fCLM, hfCLM_norm, hfCLM_ae⟩ :=
    LinearR0Help.lift_ae_linear_to_HpR hc (by positivity : 0 ≤ C_f * (p.ν ^ K_max)⁻¹ * E_exp)
      rhsF hrhsF_re (fun F => (hrhs_both F).1) (fun F => (hrhs_both F).2) hrhs_add hrhs_smul
  have hα_norm_K : ∀ F : HpR p.c, ‖αMap F‖ ≤ (C_ls * (p.ν ^ K_max)⁻¹ * E_exp) * ‖F‖ := by
    intro F
    refine (hα_le_z F).trans ?_
    have hk : (p.ν ^ k_ls)⁻¹ ≤ (p.ν ^ K_max)⁻¹ :=
      pow_inv_mono ((Nat.le_add_right k_ls k_hd).trans (le_max_right _ _))
    gcongr
  obtain ⟨R0, hR0_le, hR0_proj⟩ :=
    LinearR0Help.pair_with_E2_to_RowSpace
      (by positivity : 0 ≤ C_f * (p.ν ^ K_max)⁻¹ * E_exp)
      (by positivity : 0 ≤ C_ls * (p.ν ^ K_max)⁻¹ * E_exp)
      fCLM hfCLM_norm αMap hα_norm_K
  have hR0_norm : ‖R0‖ ≤ C_tot * (p.ν ^ K_max)⁻¹ * E_exp :=
    hR0_le.trans (le_of_eq (by dsimp only [C_tot]; ring))
  refine ⟨R0, hR0_norm, fun F => ?_⟩
  obtain ⟨hb0_cl, hb0_resp, hb0q, hb0η, _, _, _, hbody, hmc,
    _, _, _, _, _, _, hH1_α, _, _, _, _⟩ := hLS_spec F
  have hb0F_resp : IsFlatResponse p.ν 0 (toProf p.c F) (b0F F) := by
    have h := LinearR0Help.isFlatResponse_zero_reProf hb0_resp
    rwa [LinearR0Help.reProf_toProf] at h
  have hH1F : ∀ s : ℝ, 0 < s →
      sliceH1Norm p.c (zF F) (zqF F) (zηF F) s ≤
        ENNReal.ofReal (C_ls * (p.ν ^ k_ls)⁻¹ * E_exp * ‖F‖) := by
    intro s hs
    exact (LinearR0Help.sliceH1Norm_reProf_le p.c (zOf F) (zqOf F) (zηOf F) s).trans
      ((le_self_add).trans (hH1_α s hs))
  obtain ⟨hfst, hsnd⟩ := hR0_proj F
  refine ⟨b0F F, b0qF F, b0ηF F, gF F, zF F, zqF F, zηF F,
    LinearR0Help.inFlatClass_reProf hb0_cl, hb0F_resp,
    LinearR0Help.hasWeakVec_reProf hb0q, LinearR0Help.hasWeakVec_reProf hb0η,
    LinearR0Help.isBodySource_reProf hbody, ?_,
    ⟨C_ls * (p.ν ^ k_ls)⁻¹ * E_exp * ‖F‖, hH1F⟩, ?_, ?_⟩
  · rw [hsnd]; exact LinearR0Help.isGlobalMeridionalCorrection_reProf hmc
  · rw [hsnd]; exact (hrhs_both F).1.periodic
  · rw [hfst, hsnd]; exact hfCLM_ae F

/-! ## 8. Proof of Sub-step 2 (`InletEntranceCurlIdentity`) -/

namespace InletCurlHelp

/-- Planar Laplacian `ΔG(x) = ∂_{x₁}² G(x) + ∂_{x₂}² G(x)` on `ℝ × ℝ`. -/
def lapPlanar {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (G : ℝ × ℝ → E) (x : ℝ × ℝ) : E :=
  fderiv ℝ (fun y => fderiv ℝ G y (1, 0)) x (1, 0) +
    fderiv ℝ (fun y => fderiv ℝ G y (0, 1)) x (0, 1)

lemma fderiv_clm_comp (L : ℂ →L[ℝ] ℝ) {G : ℝ × ℝ → ℂ} (hG : ContDiff ℝ ∞ G)
    (z v : ℝ × ℝ) :
    fderiv ℝ (fun y => L (G y)) z v = L (fderiv ℝ G z v) := by
  have hf : HasFDerivAt (L ∘ G) (L.comp (fderiv ℝ G z)) z :=
    L.hasFDerivAt.comp z (hG.differentiable (by simp) z).hasFDerivAt
  exact congrArg (fun T => T v) hf.fderiv

lemma lapPlanar_clm_comp (L : ℂ →L[ℝ] ℝ) {G : ℝ × ℝ → ℂ} (hG : ContDiff ℝ ∞ G) (x : ℝ × ℝ) :
    lapPlanar (fun y => L (G y)) x = L (lapPlanar G x) := by
  have h1 : ContDiff ℝ ∞ (fun y => fderiv ℝ G y (1, 0)) :=
    (hG.fderiv_right (m := ∞) (by simp)).clm_apply contDiff_const
  have h2 : ContDiff ℝ ∞ (fun y => fderiv ℝ G y (0, 1)) :=
    (hG.fderiv_right (m := ∞) (by simp)).clm_apply contDiff_const
  have e1 : (fun y => fderiv ℝ (fun z => L (G z)) y (1, 0)) =
      fun y => L (fderiv ℝ G y (1, 0)) := funext fun y => fderiv_clm_comp L hG y (1, 0)
  have e2 : (fun y => fderiv ℝ (fun z => L (G z)) y (0, 1)) =
      fun y => L (fderiv ℝ G y (0, 1)) := funext fun y => fderiv_clm_comp L hG y (0, 1)
  unfold lapPlanar
  rw [e1, e2, fderiv_clm_comp L h1 x (1, 0), fderiv_clm_comp L h2 x (0, 1), ← map_add]

lemma fderiv_dir_eq_deriv_fst {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {g : ℝ × ℝ → E} {x : ℝ × ℝ} {A : E}
    (hg : DifferentiableAt ℝ g x)
    (hd : HasDerivAt (fun t : ℝ => g (t, x.2)) A x.1) :
    fderiv ℝ g x (1, 0) = A := by
  have hγ : HasDerivAt (fun t : ℝ => (t, x.2)) (1, 0) x.1 :=
    (hasDerivAt_id x.1).prodMk (hasDerivAt_const x.1 x.2)
  exact (hg.hasFDerivAt.comp_hasDerivAt x.1 hγ).unique hd

lemma fderiv_dir_eq_deriv_snd {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {g : ℝ × ℝ → E} {x : ℝ × ℝ} {A : E}
    (hg : DifferentiableAt ℝ g x)
    (hd : HasDerivAt (fun t : ℝ => g (x.1, t)) A x.2) :
    fderiv ℝ g x (0, 1) = A := by
  have hγ : HasDerivAt (fun t : ℝ => (x.1, t)) (0, 1) x.2 :=
    (hasDerivAt_const x.2 x.1).prodMk (hasDerivAt_id x.2)
  exact (hg.hasFDerivAt.comp_hasDerivAt x.2 hγ).unique hd

/-- Continuous `ℝ`-linear evaluation of the trace `(1,0)⊗(1,0) + (0,1)⊗(0,1)` of a second
Fréchet derivative on `ℝ × ℝ`. -/
def lapEval : ((ℝ × ℝ) [×2]→L[ℝ] ℂ) →L[ℝ] ℂ :=
  ContinuousMultilinearMap.apply ℝ (fun _ : Fin 2 => ℝ × ℝ) ℂ ![(1, 0), (1, 0)] +
    ContinuousMultilinearMap.apply ℝ (fun _ : Fin 2 => ℝ × ℝ) ℂ ![(0, 1), (0, 1)]

lemma lapPlanar_eq_lapEval_iter2 {G : ℝ × ℝ → ℂ} (hG : ContDiff ℝ ∞ G) (x : ℝ × ℝ) :
    lapPlanar G x = lapEval (iteratedFDeriv ℝ 2 G x) := by
  have hd : ContDiff ℝ ∞ (fderiv ℝ G) := hG.fderiv_right (m := ∞) (by simp)
  have hdir : ∀ v : ℝ × ℝ,
      fderiv ℝ (fun y => fderiv ℝ G y v) x v = iteratedFDeriv ℝ 2 G x ![v, v] := by
    intro v
    let ev : (ℝ × ℝ →L[ℝ] ℂ) →L[ℝ] ℂ := ContinuousLinearMap.apply ℝ ℂ v
    have hf : HasFDerivAt (ev ∘ fderiv ℝ G) (ev.comp (fderiv ℝ (fderiv ℝ G) x)) x :=
      ev.hasFDerivAt.comp x (hd.differentiable (by simp) x).hasFDerivAt
    have h1 : fderiv ℝ (fun y => fderiv ℝ G y v) x v = fderiv ℝ (fderiv ℝ G) x v v :=
      congrArg (fun T => T v) hf.fderiv
    rw [h1, iteratedFDeriv_two_apply]
    rfl
  unfold lapPlanar lapEval
  rw [hdir (1, 0), hdir (0, 1)]
  rfl

/-- Termwise planar Laplacian of a `c`-periodization `perC c G` under `(1 + |y₁|)^{-2}` jet decay. -/
lemma lapPlanar_perC {G : ℝ × ℝ → ℂ} (hG : ContDiff ℝ ∞ G)
    (hbd : ∀ j : ℕ, ∃ B : ℝ, ∀ y : ℝ × ℝ, ‖iteratedFDeriv ℝ j G y‖ ≤ B / (1 + |y.1|) ^ 2)
    {c : ℝ} (hc : 1 ≤ c) (x : ℝ × ℝ) :
    Summable (fun k : ℤ => lapPlanar G (x.1 + (k : ℝ) * c, x.2)) ∧
      lapPlanar (perC c G) x = perC c (lapPlanar G) x := by
  choose B hB using fun j => hbd j
  have hB0 : ∀ j, 0 ≤ B j := PerSmoothSumAux.hB_nonneg G B hB
  choose M hM using PerSmoothSumAux.pSBump_deriv_bound
  have hM0 : ∀ i, 0 ≤ M i := fun i => (norm_nonneg _).trans (hM i 0)
  have hper_cd : ContDiff ℝ ∞ (perC c G) := ((perSmoothSum G hG hbd).1 c hc).2
  obtain ⟨hev, _⟩ := PerSmoothSumAux.local_repr G hG B hB M hM hM0 hB0 c hc x
  obtain ⟨hf, hv⟩ := PerSmoothSumAux.term_hyps G hG B hB M hM hM0 hB0 c hc x
  have hkN : ((2 : ℕ) : ℕ∞) ≤ ⊤ := le_top
  have e : iteratedFDeriv ℝ 2 (perC c G) x =
      ∑' k : ℤ, iteratedFDeriv ℝ 2
        (fun y : ℝ × ℝ => PerSmoothSumAux.pSBump (y - x) • G (y.1 + (k : ℝ) * c, y.2)) x := by
    rw [(hev.iteratedFDeriv ℝ 2).eq_of_nhds]
    exact iteratedFDeriv_tsum_apply
      (f := fun (k : ℤ) (y : ℝ × ℝ) => PerSmoothSumAux.pSBump (y - x) • G (y.1 + (k : ℝ) * c, y.2))
      (v := fun n k => PerSmoothSumAux.pSK M B n *
        ((1 + (|x.1| + 2)) ^ 2 * (1 / (1 + |(k : ℝ)|) ^ 2)))
      hf (fun n _ => hv n)
      (fun n k y _ => PerSmoothSumAux.term_bound_local G hG B hB M hM hM0 hB0 c hc x n k y) hkN x
  have hle : ∀ k : ℤ, ‖iteratedFDeriv ℝ 2
      (fun y : ℝ × ℝ => PerSmoothSumAux.pSBump (y - x) • G (y.1 + (k : ℝ) * c, y.2)) x‖ ≤
      PerSmoothSumAux.pSK M B 2 * (1 / (1 + |x.1 + (k : ℝ) * c|) ^ 2) := by
    intro k
    refine PerSmoothSumAux.term_leibniz (PerSmoothSumAux.term_hψ x)
      (PerSmoothSumAux.term_hF G hG c k) 2 x M B _ ?_ ?_ hM0 hB0
    · intro i
      rw [iteratedFDeriv_comp_sub]
      exact hM i _
    · intro m
      exact PerSmoothSumAux.translate_bound G B hB c k m x
  have hsu : Summable (fun k : ℤ =>
      PerSmoothSumAux.pSK M B 2 * (1 / (1 + |x.1 + (k : ℝ) * c|) ^ 2)) :=
    (PerSmoothSumAux.uniform_sum c hc x.1).1.mul_left _
  have hs_loc : Summable (fun k : ℤ => iteratedFDeriv ℝ 2
      (fun y : ℝ × ℝ => PerSmoothSumAux.pSBump (y - x) • G (y.1 + (k : ℝ) * c, y.2)) x) :=
    Summable.of_norm (Summable.of_nonneg_of_le (fun _ => norm_nonneg _) hle hsu)
  have hterm : ∀ k : ℤ,
      iteratedFDeriv ℝ 2
        (fun y : ℝ × ℝ => PerSmoothSumAux.pSBump (y - x) • G (y.1 + (k : ℝ) * c, y.2)) x =
      iteratedFDeriv ℝ 2 G (x.1 + (k : ℝ) * c, x.2) := by
    intro k
    have hevk : (fun y : ℝ × ℝ => PerSmoothSumAux.pSBump (y - x) • G (y.1 + (k : ℝ) * c, y.2))
        =ᶠ[𝓝 x] (fun y : ℝ × ℝ => G (y + ((k : ℝ) * c, 0))) := by
      filter_upwards [Metric.ball_mem_nhds x one_pos] with y hy
      have hw : ‖y - x‖ ≤ 1 := by
        rw [← dist_eq_norm]
        exact (Metric.mem_ball.mp hy).le
      have hadd : (y.1 + (k : ℝ) * c, y.2) = y + ((k : ℝ) * c, 0) :=
        Prod.ext rfl (by simp)
      simp [PerSmoothSumAux.pSBump_one hw, hadd]
    rw [(hevk.iteratedFDeriv ℝ 2).eq_of_nhds, iteratedFDeriv_comp_add_right]
    have haddx : x + ((k : ℝ) * c, 0) = (x.1 + (k : ℝ) * c, x.2) :=
      Prod.ext rfl (by simp)
    rw [haddx]
  have hs_iter2 : Summable (fun k : ℤ => iteratedFDeriv ℝ 2 G (x.1 + (k : ℝ) * c, x.2)) :=
    hs_loc.congr hterm
  have hs_lap : Summable (fun k : ℤ => lapPlanar G (x.1 + (k : ℝ) * c, x.2)) := by
    refine (lapEval.summable hs_iter2).congr fun k => ?_
    exact (lapPlanar_eq_lapEval_iter2 hG _).symm
  refine ⟨hs_lap, ?_⟩
  rw [lapPlanar_eq_lapEval_iter2 hper_cd x, e]
  simp_rw [hterm]
  rw [lapEval.map_tsum hs_iter2]
  unfold perC
  exact tsum_congr fun k => (lapPlanar_eq_lapEval_iter2 hG _).symm

/-- Every iterated derivative of `planarStream q` decays at least like `B_j / (1 + |y₁|)²`. -/
lemma planarStream_jet_decay {lam : ℂ} {q : Planar.Profile}
    (hq : Planar.IsGrowingEigenpair lam q) (j : ℕ) :
    ∃ B : ℝ, ∀ y : ℝ × ℝ, ‖iteratedFDeriv ℝ j (planarStream q) y‖ ≤ B / (1 + |y.1|) ^ 2 := by
  have hF : ContDiff ℝ ∞ (planarStream q) := planarStreamSmooth lam q hq
  obtain ⟨ρ, M, hρ, hsplit⟩ := planarStreamQuadSplit lam q hq
  obtain ⟨Hc, hHc_cd, hHc_out⟩ := cutExists ρ M hρ
  obtain ⟨B₁, hB₁⟩ := hcDerivDecay Hc ρ M hHc_cd hρ hHc_out j
  obtain ⟨C₀, κ, hκ, hcore⟩ := coreGaussian (planarStream q) Hc ρ M hF hHc_cd hρ hHc_out hsplit j
  set c_κ : ℝ := max 1 κ⁻¹
  have hc_κ : 0 < c_κ := lt_max_of_lt_left one_pos
  refine ⟨max C₀ 0 * (2 * c_κ) + max B₁ 0, fun y => ?_⟩
  have hG0_cd : ContDiff ℝ ∞ (fun z : ℝ × ℝ => planarStream q z - Hc z) := hF.sub hHc_cd
  have hsum_eq : planarStream q = (fun z : ℝ × ℝ => planarStream q z - Hc z) + Hc := by
    funext z; simp
  have hit_add : iteratedFDeriv ℝ j (planarStream q) y =
      iteratedFDeriv ℝ j (fun z => planarStream q z - Hc z) y + iteratedFDeriv ℝ j Hc y := by
    conv_lhs => rw [hsum_eq]
    exact iteratedFDeriv_add_apply
      ((hG0_cd.of_le (by exact_mod_cast le_top)).contDiffAt)
      ((hHc_cd.of_le (by exact_mod_cast le_top)).contDiffAt)
  have hsq1 : (1 + |y.1|) ^ 2 ≤ 2 * (1 + (y.1 ^ 2 + y.2 ^ 2)) := by
    nlinarith [sq_nonneg (1 - |y.1|), sq_abs y.1, sq_nonneg y.2]
  set u : ℝ := y.1 ^ 2 + y.2 ^ 2
  have hu_nn : 0 ≤ u := by positivity
  have h1u : 1 + u ≤ c_κ * Real.exp (κ * u) := by
    have hle1 : 1 ≤ c_κ := le_max_left _ _
    have hle2 : κ⁻¹ ≤ c_κ := le_max_right _ _
    have hu_eq : u = κ⁻¹ * (κ * u) := by field_simp
    have hu_le : u ≤ c_κ * (κ * u) := by
      conv_lhs => rw [hu_eq]
      exact mul_le_mul_of_nonneg_right hle2 (by positivity)
    have hexp_le : 1 + κ * u ≤ Real.exp (κ * u) := by
      linarith [Real.add_one_le_exp (κ * u)]
    calc 1 + u ≤ c_κ + c_κ * (κ * u) := add_le_add hle1 hu_le
      _ = c_κ * (1 + κ * u) := by ring
      _ ≤ c_κ * Real.exp (κ * u) := mul_le_mul_of_nonneg_left hexp_le hc_κ.le
  have hexp_prod : (1 + |y.1|) ^ 2 * Real.exp (-(κ * u)) ≤ 2 * c_κ := by
    have h1 : (1 + |y.1|) ^ 2 * Real.exp (-(κ * u)) ≤
        2 * ((1 + u) * Real.exp (-(κ * u))) := by
      have hp := mul_le_mul_of_nonneg_right hsq1 (Real.exp_pos (-(κ * u))).le
      linarith
    have h2 : (1 + u) * Real.exp (-(κ * u)) ≤ c_κ := by
      have hp := mul_le_mul_of_nonneg_right h1u (Real.exp_pos (-(κ * u))).le
      have he0 : Real.exp (κ * u) * Real.exp (-(κ * u)) = 1 := by
        rw [← Real.exp_add, add_neg_cancel, Real.exp_zero]
      rwa [mul_assoc, he0, mul_one] at hp
    linarith
  have hg0_le : ‖iteratedFDeriv ℝ j (fun z => planarStream q z - Hc z) y‖ ≤
      max C₀ 0 * (2 * c_κ) / (1 + |y.1|) ^ 2 := by
    have hc1 := (hcore y).trans
      (mul_le_mul_of_nonneg_right (le_max_left C₀ 0) (Real.exp_pos _).le)
    rw [le_div_iff₀ (by positivity)]
    calc ‖iteratedFDeriv ℝ j (fun z => planarStream q z - Hc z) y‖ * (1 + |y.1|) ^ 2
        ≤ max C₀ 0 * Real.exp (-(κ * u)) * (1 + |y.1|) ^ 2 :=
          mul_le_mul_of_nonneg_right hc1 (by positivity)
      _ = max C₀ 0 * ((1 + |y.1|) ^ 2 * Real.exp (-(κ * u))) := by ring
      _ ≤ max C₀ 0 * (2 * c_κ) :=
          mul_le_mul_of_nonneg_left hexp_prod (le_max_right C₀ 0)
  have hhc_le : ‖iteratedFDeriv ℝ j Hc y‖ ≤ max B₁ 0 / (1 + |y.1|) ^ 2 :=
    (hB₁ y).trans (div_le_div_of_nonneg_right (le_max_left B₁ 0) (by positivity))
  rw [hit_add, add_div]
  exact (norm_add_le _ _).trans (add_le_add hg0_le hhc_le)

/-- Planar Laplacian of the smooth angular-two form `(x₁ + i x₂)² P(x₁² + x₂²)`. -/
lemma lapPlanar_quadP {P : ℝ → ℂ} (hP : ContDiff ℝ ∞ P) (x : ℝ × ℝ) :
    lapPlanar (fun y : ℝ × ℝ =>
        ((y.1 : ℂ) + (y.2 : ℂ) * Complex.I) ^ 2 * P (y.1 ^ 2 + y.2 ^ 2)) x =
      ((x.1 : ℂ) + (x.2 : ℂ) * Complex.I) ^ 2 *
        (12 * deriv P (x.1 ^ 2 + x.2 ^ 2) +
          4 * ((x.1 ^ 2 + x.2 ^ 2 : ℝ) : ℂ) * deriv (deriv P) (x.1 ^ 2 + x.2 ^ 2)) := by
  have hP1 : ContDiff ℝ ∞ (deriv P) :=
    contDiff_infty.mpr fun n =>
      (contDiff_succ_iff_deriv.mp
        (hP.of_le (by exact_mod_cast le_top : ((n : ℕ∞ω) + 1) ≤ (∞ : ℕ∞ω)))).2.2
  let zC : ℝ × ℝ → ℂ := fun y => (y.1 : ℂ) + (y.2 : ℂ) * Complex.I
  let uR : ℝ × ℝ → ℝ := fun y => y.1 ^ 2 + y.2 ^ 2
  let F : ℝ × ℝ → ℂ := fun y => zC y ^ 2 * P (uR y)
  have hz_cd : ContDiff ℝ ∞ zC :=
    (Complex.ofRealCLM.contDiff.comp contDiff_fst).add
      ((Complex.ofRealCLM.contDiff.comp contDiff_snd).mul contDiff_const)
  have hu_cd : ContDiff ℝ ∞ uR := (contDiff_fst.pow 2).add (contDiff_snd.pow 2)
  have hF_cd : ContDiff ℝ ∞ F := (hz_cd.pow 2).mul (hP.comp hu_cd)
  have hofR : ∀ t : ℝ, HasDerivAt (fun s : ℝ => (s : ℂ)) 1 t := fun t =>
    (Complex.ofRealCLM.hasDerivAt (x := t)).congr_deriv Complex.ofReal_one
  have hd1 : ∀ y : ℝ × ℝ, fderiv ℝ F y (1, 0) =
      2 * zC y * P (uR y) + zC y ^ 2 * (2 * (y.1 : ℂ) * deriv P (uR y)) := by
    intro y
    refine fderiv_dir_eq_deriv_fst (hF_cd.differentiable (by simp) y) ?_
    have hz1 : HasDerivAt (fun t : ℝ => (t : ℂ) + (y.2 : ℂ) * Complex.I) 1 y.1 :=
      (hofR y.1).add_const _
    have hz2 : HasDerivAt (fun t : ℝ => ((t : ℂ) + (y.2 : ℂ) * Complex.I) ^ 2) (2 * zC y) y.1 :=
      (hz1.fun_pow 2).congr_deriv (by dsimp only [zC]; norm_num)
    have hu1 : HasDerivAt (fun t : ℝ => t ^ 2 + y.2 ^ 2) (2 * y.1) y.1 :=
      (((hasDerivAt_id y.1).fun_pow 2).add_const (y.2 ^ 2)).congr_deriv (by norm_num)
    have hPu : HasDerivAt (fun t : ℝ => P (t ^ 2 + y.2 ^ 2))
        (2 * (y.1 : ℂ) * deriv P (uR y)) y.1 :=
      (((hP.differentiable (by simp) (uR y)).hasDerivAt).scomp y.1 hu1).congr_deriv
        (by simp only [Complex.real_smul]; push_cast; ring)
    exact hz2.mul hPu
  have hd2 : ∀ y : ℝ × ℝ, fderiv ℝ F y (0, 1) =
      2 * Complex.I * zC y * P (uR y) + zC y ^ 2 * (2 * (y.2 : ℂ) * deriv P (uR y)) := by
    intro y
    refine fderiv_dir_eq_deriv_snd (hF_cd.differentiable (by simp) y) ?_
    have hz1 : HasDerivAt (fun t : ℝ => (y.1 : ℂ) + (t : ℂ) * Complex.I) Complex.I y.2 :=
      (((hofR y.2).mul_const Complex.I).const_add (y.1 : ℂ)).congr_deriv (one_mul _)
    have hz2 : HasDerivAt (fun t : ℝ => ((y.1 : ℂ) + (t : ℂ) * Complex.I) ^ 2)
        (2 * Complex.I * zC y) y.2 :=
      (hz1.fun_pow 2).congr_deriv (by dsimp only [zC]; norm_num; ring)
    have hu1 : HasDerivAt (fun t : ℝ => y.1 ^ 2 + t ^ 2) (2 * y.2) y.2 :=
      (((hasDerivAt_id y.2).fun_pow 2).const_add (y.1 ^ 2)).congr_deriv (by norm_num)
    have hPu : HasDerivAt (fun t : ℝ => P (y.1 ^ 2 + t ^ 2))
        (2 * (y.2 : ℂ) * deriv P (uR y)) y.2 :=
      (((hP.differentiable (by simp) (uR y)).hasDerivAt).scomp y.2 hu1).congr_deriv
        (by simp only [Complex.real_smul]; push_cast; ring)
    exact hz2.mul hPu
  let G1 : ℝ × ℝ → ℂ := fun y =>
    2 * zC y * P (uR y) + zC y ^ 2 * (2 * (y.1 : ℂ) * deriv P (uR y))
  let G2 : ℝ × ℝ → ℂ := fun y =>
    2 * Complex.I * zC y * P (uR y) + zC y ^ 2 * (2 * (y.2 : ℂ) * deriv P (uR y))
  have hG1_cd : ContDiff ℝ ∞ G1 :=
    ((contDiff_const.mul hz_cd).mul (hP.comp hu_cd)).add
      ((hz_cd.pow 2).mul ((contDiff_const.mul (Complex.ofRealCLM.contDiff.comp contDiff_fst)).mul
        (hP1.comp hu_cd)))
  have hG2_cd : ContDiff ℝ ∞ G2 :=
    ((contDiff_const.mul hz_cd).mul (hP.comp hu_cd)).add
      ((hz_cd.pow 2).mul ((contDiff_const.mul (Complex.ofRealCLM.contDiff.comp contDiff_snd)).mul
        (hP1.comp hu_cd)))
  have hd11 : fderiv ℝ G1 x (1, 0) =
      2 * P (uR x) + 2 * zC x * (2 * (x.1 : ℂ) * deriv P (uR x)) +
        (2 * zC x * (2 * (x.1 : ℂ) * deriv P (uR x)) +
          zC x ^ 2 * (2 * deriv P (uR x) +
            2 * (x.1 : ℂ) * (2 * (x.1 : ℂ) * deriv (deriv P) (uR x)))) := by
    refine fderiv_dir_eq_deriv_fst (hG1_cd.differentiable (by simp) x) ?_
    have hz1 : HasDerivAt (fun t : ℝ => (t : ℂ) + (x.2 : ℂ) * Complex.I) 1 x.1 :=
      (hofR x.1).add_const _
    have h2z : HasDerivAt (fun t : ℝ => 2 * ((t : ℂ) + (x.2 : ℂ) * Complex.I)) 2 x.1 :=
      (hz1.const_mul (2 : ℂ)).congr_deriv (mul_one _)
    have hz2 : HasDerivAt (fun t : ℝ => ((t : ℂ) + (x.2 : ℂ) * Complex.I) ^ 2) (2 * zC x) x.1 :=
      (hz1.fun_pow 2).congr_deriv (by dsimp only [zC]; norm_num)
    have hu1 : HasDerivAt (fun t : ℝ => t ^ 2 + x.2 ^ 2) (2 * x.1) x.1 :=
      (((hasDerivAt_id x.1).fun_pow 2).add_const (x.2 ^ 2)).congr_deriv (by norm_num)
    have hPu : HasDerivAt (fun t : ℝ => P (t ^ 2 + x.2 ^ 2))
        (2 * (x.1 : ℂ) * deriv P (uR x)) x.1 :=
      (((hP.differentiable (by simp) (uR x)).hasDerivAt).scomp x.1 hu1).congr_deriv
        (by simp only [Complex.real_smul]; push_cast; ring)
    have hP1u : HasDerivAt (fun t : ℝ => deriv P (t ^ 2 + x.2 ^ 2))
        (2 * (x.1 : ℂ) * deriv (deriv P) (uR x)) x.1 := by
      have h0 := ((hP1.differentiable (by simp) (uR x)).hasDerivAt).scomp x.1 hu1
      exact h0.congr_deriv (by simp only [Complex.real_smul]; push_cast; ring)
    have h2t : HasDerivAt (fun t : ℝ => 2 * (t : ℂ)) 2 x.1 :=
      ((hofR x.1).const_mul (2 : ℂ)).congr_deriv (mul_one _)
    exact (h2z.mul hPu).add (hz2.mul (h2t.mul hP1u))
  have hd22 : fderiv ℝ G2 x (0, 1) =
      (2 * Complex.I * Complex.I) * P (uR x) +
        (2 * Complex.I * zC x) * (2 * (x.2 : ℂ) * deriv P (uR x)) +
        ((2 * Complex.I * zC x) * (2 * (x.2 : ℂ) * deriv P (uR x)) +
          zC x ^ 2 * (2 * deriv P (uR x) +
            2 * (x.2 : ℂ) * (2 * (x.2 : ℂ) * deriv (deriv P) (uR x)))) := by
    refine fderiv_dir_eq_deriv_snd (hG2_cd.differentiable (by simp) x) ?_
    have hz1 : HasDerivAt (fun t : ℝ => (x.1 : ℂ) + (t : ℂ) * Complex.I) Complex.I x.2 :=
      (((hofR x.2).mul_const Complex.I).const_add (x.1 : ℂ)).congr_deriv (one_mul _)
    have h2Iz : HasDerivAt
        (fun t : ℝ => 2 * Complex.I * ((x.1 : ℂ) + (t : ℂ) * Complex.I))
        (2 * Complex.I * Complex.I) x.2 :=
      (hz1.const_mul (2 * Complex.I)).congr_deriv (by ring)
    have hz2 : HasDerivAt (fun t : ℝ => ((x.1 : ℂ) + (t : ℂ) * Complex.I) ^ 2)
        (2 * Complex.I * zC x) x.2 :=
      (hz1.fun_pow 2).congr_deriv (by dsimp only [zC]; norm_num; ring)
    have hu1 : HasDerivAt (fun t : ℝ => x.1 ^ 2 + t ^ 2) (2 * x.2) x.2 :=
      (((hasDerivAt_id x.2).fun_pow 2).const_add (x.1 ^ 2)).congr_deriv (by norm_num)
    have hPu : HasDerivAt (fun t : ℝ => P (x.1 ^ 2 + t ^ 2))
        (2 * (x.2 : ℂ) * deriv P (uR x)) x.2 :=
      (((hP.differentiable (by simp) (uR x)).hasDerivAt).scomp x.2 hu1).congr_deriv
        (by simp only [Complex.real_smul]; push_cast; ring)
    have hP1u : HasDerivAt (fun t : ℝ => deriv P (x.1 ^ 2 + t ^ 2))
        (2 * (x.2 : ℂ) * deriv (deriv P) (uR x)) x.2 := by
      have h0 := ((hP1.differentiable (by simp) (uR x)).hasDerivAt).scomp x.2 hu1
      exact h0.congr_deriv (by simp only [Complex.real_smul]; push_cast; ring)
    have h2t : HasDerivAt (fun t : ℝ => 2 * (t : ℂ)) 2 x.2 :=
      ((hofR x.2).const_mul (2 : ℂ)).congr_deriv (mul_one _)
    exact (h2Iz.mul hPu).add (hz2.mul (h2t.mul hP1u))
  change lapPlanar F x = _
  unfold lapPlanar
  rw [funext hd1, funext hd2]
  change fderiv ℝ G1 x (1, 0) + fderiv ℝ G2 x (0, 1) = _
  rw [hd11, hd22]
  have hI2 : Complex.I * Complex.I = -1 := Complex.I_mul_I
  have hu_cast : ((x.1 ^ 2 + x.2 ^ 2 : ℝ) : ℂ) = (x.1 : ℂ) ^ 2 + (x.2 : ℂ) ^ 2 := by push_cast; ring
  rw [hu_cast]
  dsimp only [zC, uR]
  linear_combination (2 * P (x.1 ^ 2 + x.2 ^ 2)) * hI2

/-- Differential form of the Volterra ODE `P = sqVolterra lam c₀ P`:
`12 P'(u) + 4 u P''(u) = sqCoeff lam u * P u` for all `u > 0`. -/
lemma sqVolterra_ode {lam c₀ : ℂ} (hl : 0 < lam.re) {P : ℝ → ℂ}
    (hP : ContDiff ℝ ∞ P) (hvol : ∀ u : ℝ, P u = sqVolterra lam c₀ P u)
    {u : ℝ} (hu : 0 < u) :
    12 * deriv P u + 4 * (u : ℂ) * deriv (deriv P) u = sqCoeff lam u * P u := by
  let H : ℝ → ℂ := fun s => sqCoeff lam s * P s
  have hH : ContDiff ℝ ∞ H := (sqCoeff_contDiff_aux lam hl ∞).mul hP
  have hP1 : ContDiff ℝ ∞ (deriv P) :=
    contDiff_infty.mpr fun n =>
      (contDiff_succ_iff_deriv.mp
        (hP.of_le (by exact_mod_cast le_top : ((n : ℕ∞ω) + 1) ≤ (∞ : ℕ∞ω)))).2.2
  have hΦ : ContDiff ℝ (0 : WithTop ℕ∞)
      (fun v : ℝ => ∫ t in (0 : ℝ)..1, (t : ℂ) ^ 2 * H (v * t)) :=
    param_contDiff_aux 0 2 H (hH.of_le (by simp))
  have hΦc : Continuous (fun v : ℝ => ∫ t in (0 : ℝ)..1, (t : ℂ) ^ 2 * H (v * t)) :=
    hΦ.continuous
  have hderivP : ∀ v : ℝ, deriv P v =
      (1 / 4 : ℂ) * ∫ t in (0 : ℝ)..1, (t : ℂ) ^ 2 * H (v * t) := by
    intro v
    have h1 : HasDerivAt
        (fun w : ℝ => c₀ + ∫ s in (0 : ℝ)..w, (1 / 4 : ℂ) * ∫ t in (0 : ℝ)..1,
          (t : ℂ) ^ 2 * H (s * t))
        ((1 / 4 : ℂ) * ∫ t in (0 : ℝ)..1, (t : ℂ) ^ 2 * H (v * t)) v :=
      (((hΦc.const_mul (1 / 4 : ℂ)).integral_hasStrictDerivAt 0 v).hasDerivAt).const_add c₀
    have hfun : (fun w : ℝ => c₀ + ∫ s in (0 : ℝ)..w, (1 / 4 : ℂ) * ∫ t in (0 : ℝ)..1,
        (t : ℂ) ^ 2 * H (s * t)) = P := funext fun w => (hvol w).symm
    rw [hfun] at h1
    exact h1.deriv
  have hint_eq : ∀ v : ℝ,
      4 * (v : ℂ) ^ 3 * deriv P v = ∫ w in (0 : ℝ)..v, (w : ℂ) ^ 2 * H w := by
    intro v
    rw [hderivP v]
    have h1 : 4 * (v : ℂ) ^ 3 * ((1 / 4 : ℂ) * ∫ t in (0 : ℝ)..1, (t : ℂ) ^ 2 * H (v * t)) =
        (v : ℂ) * ((v : ℂ) ^ 2 * ∫ t in (0 : ℝ)..1, (t : ℂ) ^ 2 * H (v * t)) := by ring
    rw [h1, ← intervalIntegral.integral_const_mul]
    have h2 : (fun t : ℝ => (v : ℂ) ^ 2 * ((t : ℂ) ^ 2 * H (v * t))) =
        fun t : ℝ => ((v * t : ℝ) : ℂ) ^ 2 * H (v * t) := by
      funext t; push_cast; ring
    rw [h2, ← Complex.real_smul,
      intervalIntegral.smul_integral_comp_mul_left (f := fun w : ℝ => (w : ℂ) ^ 2 * H w) v]
    simp
  have hRHS_d : HasDerivAt (fun v : ℝ => ∫ w in (0 : ℝ)..v, (w : ℂ) ^ 2 * H w)
      ((u : ℂ) ^ 2 * H u) u := by
    have hc : Continuous (fun w : ℝ => (w : ℂ) ^ 2 * H w) :=
      (Complex.continuous_ofReal.pow 2).mul hH.continuous
    exact (hc.integral_hasStrictDerivAt 0 u).hasDerivAt
  have hLHS_d : HasDerivAt (fun v : ℝ => 4 * (v : ℂ) ^ 3 * deriv P v)
      (12 * (u : ℂ) ^ 2 * deriv P u + 4 * (u : ℂ) ^ 3 * deriv (deriv P) u) u := by
    have hofR : HasDerivAt (fun v : ℝ => (v : ℂ)) 1 u :=
      (Complex.ofRealCLM.hasDerivAt (x := u)).congr_deriv Complex.ofReal_one
    have hv3 : HasDerivAt (fun v : ℝ => 4 * (v : ℂ) ^ 3) (12 * (u : ℂ) ^ 2) u :=
      ((hofR.fun_pow 3).const_mul (4 : ℂ)).congr_deriv (by norm_num; ring)
    exact hv3.mul ((hP1.differentiable (by simp) u).hasDerivAt)
  rw [← funext hint_eq] at hRHS_d
  have heq := hLHS_d.unique hRHS_d
  have hu_ne : (u : ℂ) ^ 2 ≠ 0 := pow_ne_zero 2 (by exact_mod_cast hu.ne')
  apply mul_left_cancel₀ hu_ne
  dsimp only [H] at heq
  linear_combination heq

/-- Exact planar Poisson identity `Δ(planarStream q) = planarMode2D q` on all of `ℝ × ℝ`. -/
lemma lapPlanar_planarStream {lam : ℂ} {q : Planar.Profile}
    (hq : Planar.IsGrowingEigenpair lam q) (x : ℝ × ℝ) :
    lapPlanar (planarStream q) x = planarMode2D q x := by
  have hO := greenInverseOrderTwo lam q hq
  obtain ⟨g, hgc, hg⟩ := greenSqContinuous lam q hq hO
  obtain ⟨c₀, hc₀⟩ := greenSqVolterra lam q hq hO g hgc hg
  obtain ⟨P, hPc, hPvol⟩ := sqVolterraExists lam c₀ hq.re_pos
  have hPsmooth : ContDiff ℝ ∞ P := sqVolterraSmooth lam c₀ hq.re_pos P hPc hPvol
  have hG : ∀ r : ℝ, 0 < r → Planar.greenInverse q r = (r : ℂ) ^ 2 * P (r ^ 2) := by
    intro r hr
    have hr2 : 0 < r ^ 2 := by positivity
    have hsq : Real.sqrt (r ^ 2) = r := Real.sqrt_sq hr.le
    have hgp := sqVolterraUnique lam c₀ hq.re_pos g P hgc hPc.continuousOn hc₀
      (fun u _ => hPvol u) (r ^ 2) hr2.le
    have hgr := hg (r ^ 2) hr2
    rw [hsq] at hgr
    rw [← hgp, hgr]
    have hr0 : (r : ℂ) ≠ 0 := by exact_mod_cast hr.ne'
    push_cast
    field_simp
  have hps_eq : planarStream q = fun y : ℝ × ℝ =>
      ((y.1 : ℂ) + (y.2 : ℂ) * Complex.I) ^ 2 * P (y.1 ^ 2 + y.2 ^ 2) := by
    funext y
    by_cases hy : y.1 ^ 2 + y.2 ^ 2 = 0
    · have hy1 : y.1 = 0 := by nlinarith [sq_nonneg y.1, sq_nonneg y.2]
      have hy2 : y.2 = 0 := by nlinarith [sq_nonneg y.1, sq_nonneg y.2]
      simp [planarStream, angularTwo, hy1, hy2]
    · have hpos : 0 < y.1 ^ 2 + y.2 ^ 2 := lt_of_le_of_ne (by positivity) (Ne.symm hy)
      have hr : 0 < Real.sqrt (y.1 ^ 2 + y.2 ^ 2) := Real.sqrt_pos.2 hpos
      have hsq : Real.sqrt (y.1 ^ 2 + y.2 ^ 2) ^ 2 = y.1 ^ 2 + y.2 ^ 2 := Real.sq_sqrt hpos.le
      unfold planarStream angularTwo
      rw [hG _ hr, hsq]
      have hne : ((y.1 ^ 2 + y.2 ^ 2 : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hy
      have hc : ((Real.sqrt (y.1 ^ 2 + y.2 ^ 2) : ℝ) : ℂ) ^ 2 =
          ((y.1 ^ 2 + y.2 ^ 2 : ℝ) : ℂ) := by exact_mod_cast hsq
      rw [hc]
      push_cast at hne ⊢
      field_simp
  rw [hps_eq, lapPlanar_quadP hPsmooth x]
  by_cases hx : x.1 ^ 2 + x.2 ^ 2 = 0
  · have hx1 : x.1 = 0 := by nlinarith [sq_nonneg x.1, sq_nonneg x.2]
    have hx2 : x.2 = 0 := by nlinarith [sq_nonneg x.1, sq_nonneg x.2]
    simp [planarMode2D, angTwoPlanar, hx1, hx2]
  · have hpos : 0 < x.1 ^ 2 + x.2 ^ 2 := lt_of_le_of_ne (by positivity) (Ne.symm hx)
    have hr : 0 < Real.sqrt (x.1 ^ 2 + x.2 ^ 2) := Real.sqrt_pos.2 hpos
    have hsq : Real.sqrt (x.1 ^ 2 + x.2 ^ 2) ^ 2 = x.1 ^ 2 + x.2 ^ 2 := Real.sq_sqrt hpos.le
    rw [sqVolterra_ode hq.re_pos hPsmooth hPvol hpos]
    have heig := greenSqF_eigen hq.re_pos hq.eigen hr
    rw [hG _ hr, hsq] at heig
    have hc : ((Real.sqrt (x.1 ^ 2 + x.2 ^ 2) : ℝ) : ℂ) ^ 2 =
        ((x.1 ^ 2 + x.2 ^ 2 : ℝ) : ℂ) := by exact_mod_cast hsq
    rw [hc] at heig
    have hne : ((x.1 ^ 2 + x.2 ^ 2 : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hx
    unfold planarMode2D angTwoPlanar
    rw [heig]
    push_cast at hne ⊢
    field_simp

lemma dilPlanarMode_one (q : Planar.Profile) (y : B0579.Plane) :
    dilPlanarMode q 1 y = planarMode2D q y := by
  simp [dilPlanarMode]

/-- On `s < p.H / 4`, the planar curl of `cplx (inletE0 p i)` equals `(Δ(p.frozenStream i) x : ℂ)`. -/
lemma profCurl_inletE0_early {p : Params} {d dm dp : ℝ} {lam : ℂ} {q : Planar.Profile}
    (hq : Planar.IsGrowingEigenpair lam q) (hreg : BgRegime p d dm dp)
    (hν1 : p.ν ≤ 1) (hmode : p.mode = q) (i : Fin 2)
    {s : ℝ} (hs : s < p.H / 4) (x : B0579.Plane) :
    Axi.dQ (inletE0 p i) (s, x) 1 - Axi.dEta (inletE0 p i) (s, x) 0 =
      lapPlanar (p.frozenStream i) x := by
  obtain ⟨_, _, _, -, -, hper⟩ := frozenStreamBounds lam q hq 0
  have hc1 : 1 ≤ p.c := by
    have hνpos : 0 < p.ν := p.ν_pos
    rw [hreg.c_eq, one_le_inv₀ (by positivity)]
    nlinarith
  have hfro : ContDiff ℝ ∞ (p.frozenStream i) :=
    inletCD_frozenStream ((hper p.c hc1).1) hmode i
  have hE := F10Help.contDiff_inletE0 hq hreg hν1 hmode i
  have hfderiv_snd : ∀ (f : ℝ × ℝ → ℝ), ContDiff ℝ ∞ f → ∀ (m : Coord) (v : ℝ × ℝ),
      fderiv ℝ (fun z : Coord => f z.2) m (0, v) = fderiv ℝ f m.2 v := by
    intro f hf m v
    have hc : HasFDerivAt (f ∘ Prod.snd)
        ((fderiv ℝ f m.2).comp (ContinuousLinearMap.snd ℝ ℝ (ℝ × ℝ))) m :=
      (hf.differentiable (by simp) m.2).hasFDerivAt.comp m hasFDerivAt_snd
    exact congrArg (fun T => T (0, v)) hc.fderiv
  have hU : IsOpen {m : Coord | m.1 < p.H / 4} := isOpen_lt continuous_fst continuous_const
  have hcut_U : ∀ y ∈ {m : Coord | m.1 < p.H / 4},
      p.cutStream i =ᶠ[𝓝 y] (fun z : Coord => p.frozenStream i z.2) := by
    intro y hy
    filter_upwards [hU.mem_nhds hy] with z (hz : z.1 < p.H / 4)
    simp [Params.cutStream, ageCutoff_eq_one p.H_pos hz.le]
  have hE0_1 : (fun y : Coord => inletE0 p i y 1) =ᶠ[𝓝 (s, x)]
      (fun y : Coord => fderiv ℝ (p.frozenStream i) y.2 (1, 0)) := by
    filter_upwards [hU.mem_nhds hs] with y hy
    have h1 : inletE0 p i y 1 = fderiv ℝ (p.cutStream i) y (0, (1, 0)) := by
      simp [inletE0, Axi.dEta, Axi.dQ, Axi.m0, Axi.m1]
    rw [h1, (hcut_U y hy).fderiv_eq, hfderiv_snd (p.frozenStream i) hfro y (1, 0)]
  have hE0_0 : (fun y : Coord => inletE0 p i y 0) =ᶠ[𝓝 (s, x)]
      (fun y : Coord => -(fderiv ℝ (p.frozenStream i) y.2 (0, 1))) := by
    filter_upwards [hU.mem_nhds hs] with y hy
    have h0 : inletE0 p i y 0 = -(fderiv ℝ (p.cutStream i) y (0, (0, 1))) := by
      simp [inletE0, Axi.dEta, Axi.dQ, Axi.m0, Axi.m1]
    rw [h0, (hcut_U y hy).fderiv_eq, hfderiv_snd (p.frozenStream i) hfro y (0, 1)]
  have hp1 : Axi.dQ (inletE0 p i) (s, x) 1 =
      fderiv ℝ (fun y : Coord => inletE0 p i y 1) (s, x) (0, (1, 0)) := by
    let L1 : Axi.Merid →L[ℝ] ℝ := EuclideanSpace.proj 1
    have hf : HasFDerivAt (L1 ∘ inletE0 p i) (L1.comp (fderiv ℝ (inletE0 p i) (s, x))) (s, x) :=
      L1.hasFDerivAt.comp (s, x) (hE.differentiable (by simp) (s, x)).hasFDerivAt
    exact (congrArg (fun T => T (0, (1, 0))) hf.fderiv).symm
  have hp0 : Axi.dEta (inletE0 p i) (s, x) 0 =
      fderiv ℝ (fun y : Coord => inletE0 p i y 0) (s, x) (0, (0, 1)) := by
    let L0 : Axi.Merid →L[ℝ] ℝ := EuclideanSpace.proj 0
    have hf : HasFDerivAt (L0 ∘ inletE0 p i) (L0.comp (fderiv ℝ (inletE0 p i) (s, x))) (s, x) :=
      L0.hasFDerivAt.comp (s, x) (hE.differentiable (by simp) (s, x)).hasFDerivAt
    exact (congrArg (fun T => T (0, (0, 1))) hf.fderiv).symm
  have hf1_cd : ContDiff ℝ ∞ (fun z : ℝ × ℝ => fderiv ℝ (p.frozenStream i) z (1, 0)) :=
    (hfro.fderiv_right (m := ∞) (by simp)).clm_apply contDiff_const
  have hf2_cd : ContDiff ℝ ∞ (fun z : ℝ × ℝ => -(fderiv ℝ (p.frozenStream i) z (0, 1))) :=
    ((hfro.fderiv_right (m := ∞) (by simp)).clm_apply contDiff_const).neg
  rw [hp1, hp0, hE0_1.fderiv_eq, hE0_0.fderiv_eq,
    hfderiv_snd _ hf1_cd (s, x) (1, 0), hfderiv_snd _ hf2_cd (s, x) (0, 1)]
  have hneg : fderiv ℝ (fun z : ℝ × ℝ => -(fderiv ℝ (p.frozenStream i) z (0, 1))) x (0, 1) =
      -(fderiv ℝ (fun z : ℝ × ℝ => fderiv ℝ (p.frozenStream i) z (0, 1)) x (0, 1)) := by
    have hd : ContDiff ℝ ∞ (fun z : ℝ × ℝ => fderiv ℝ (p.frozenStream i) z (0, 1)) :=
      (hfro.fderiv_right (m := ∞) (by simp)).clm_apply contDiff_const
    exact congrArg (fun T => T (0, 1)) ((hd.differentiable (by simp) x).hasFDerivAt.neg.fderiv)
  rw [hneg]
  unfold lapPlanar
  ring

end InletCurlHelp

/-- **Unconditional proof of Sub-step 2 (`InletEntranceCurlIdentity`)**. -/
theorem inletEntranceCurlIdentity_proof : InletEntranceCurlIdentity := by
  intro lam q hq dm dp _hdm p d hreg hν1 hmode α s _hs0 hsH x
  have hc1 : 1 ≤ p.c := by
    have hνpos : 0 < p.ν := p.ν_pos
    rw [hreg.c_eq, one_le_inv₀ (by positivity)]
    nlinarith
  have hF_cd : ContDiff ℝ ∞ (planarStream q) := planarStreamSmooth lam q hq
  have hbd := InletCurlHelp.planarStream_jet_decay hq
  have hper_cd : ContDiff ℝ ∞ (perC p.c (planarStream q)) :=
    ((perSmoothSum (planarStream q) hF_cd hbd).1 p.c hc1).2
  obtain ⟨hs_lap, hlap_per⟩ := InletCurlHelp.lapPlanar_perC hF_cd hbd hc1 x
  have hs_mode : Summable (fun k : ℤ => planarMode2D q (x.1 + (k : ℝ) * p.c, x.2)) :=
    hs_lap.congr fun k => InletCurlHelp.lapPlanar_planarStream hq (x.1 + (k : ℝ) * p.c, x.2)
  have hlap_eq : InletCurlHelp.lapPlanar (perC p.c (planarStream q)) x =
      periodizePlanar p.c (dilPlanarMode q 1) x := by
    rw [hlap_per]
    unfold perC periodizePlanar
    refine tsum_congr fun k => ?_
    rw [InletCurlHelp.lapPlanar_planarStream hq, InletCurlHelp.dilPlanarMode_one]
  have hcomp_eq : ∀ i : Fin 2,
      InletCurlHelp.lapPlanar (p.frozenStream i) x = entranceVorticity p i x := by
    intro i
    have hps_perC : periodicStream p.mode p.c = perC p.c (planarStream q) := by
      rw [hmode]; rfl
    have hpm_per : periodizePlanar p.c (dilPlanarMode p.mode 1) x =
        ∑' k : ℤ, planarMode2D q (x.1 + (k : ℝ) * p.c, x.2) := by
      rw [hmode]
      unfold periodizePlanar
      exact tsum_congr fun k => InletCurlHelp.dilPlanarMode_one q _
    have hlap_tsum : InletCurlHelp.lapPlanar (perC p.c (planarStream q)) x =
        ∑' k : ℤ, planarMode2D q (x.1 + (k : ℝ) * p.c, x.2) := by
      rw [hlap_eq]
      unfold periodizePlanar
      exact tsum_congr fun k => InletCurlHelp.dilPlanarMode_one q _
    fin_cases i
    · change InletCurlHelp.lapPlanar (p.frozenStream 0) x = entranceVorticity p 0 x
      let L0 : ℂ →L[ℝ] ℝ := (2 : ℝ) • Complex.reCLM
      have hfr0 : p.frozenStream 0 = fun y => L0 (perC p.c (planarStream q) y) := by
        funext y
        simp [Params.frozenStream, hps_perC, L0]
      rw [hfr0, InletCurlHelp.lapPlanar_clm_comp L0 hper_cd x, hlap_tsum]
      unfold entranceVorticity frozenDirectMode
      simp only [Matrix.cons_val_zero, hpm_per]
      simp [L0]
    · change InletCurlHelp.lapPlanar (p.frozenStream 1) x = entranceVorticity p 1 x
      let L1 : ℂ →L[ℝ] ℝ := (-2 : ℝ) • Complex.imCLM
      have hfr1 : p.frozenStream 1 = fun y => L1 (perC p.c (planarStream q) y) := by
        funext y
        simp [Params.frozenStream, hps_perC, L1]
      rw [hfr1, InletCurlHelp.lapPlanar_clm_comp L1 hper_cd x, hlap_tsum]
      unfold entranceVorticity frozenDirectMode
      simp only [Matrix.cons_val_one, hpm_per]
      simp [L1]
  unfold profCurl inletProfQ inletProfEta entranceVorticityComb
  simp only [Fin.sum_univ_two, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul, cplx]
  have h0 := InletCurlHelp.profCurl_inletE0_early hq hreg hν1 hmode 0 hsH x
  have h1 := InletCurlHelp.profCurl_inletE0_early hq hreg hν1 hmode 1 hsH x
  rw [← hcomp_eq 0, ← hcomp_eq 1, ← h0, ← h1]
  push_cast
  ring

/-! ## 9. Proof of Sub-step 3 (`FlatReconstructionZeroCurlUniqueStep`) and Final Assembly -/

namespace ZeroCurlUniqueHelp

lemma cell_eq (c : ℝ) : Cyl.cell c = B0579.cell c := by
  simp only [Cyl.cell, B0579.cell, neg_div]

lemma avgμ_eq_smul_cell (c : ℝ) :
    Cyl.avgμ c = ENNReal.ofReal c⁻¹ • volume.restrict (B0579.cell c) := by
  simp only [Cyl.avgμ, Cyl.cellμ, cell_eq c]

lemma cellMeasure_zero_eq (c : ℝ) :
    B0579.cellMeasure c 0 = volume.restrict (B0579.cell c) := by
  unfold B0579.cellMeasure
  have h1 : (fun x : B0579.Plane => (B0579.density 0 x : ℝ≥0∞)) = 1 := by
    funext x
    have hd : B0579.density 0 x = 1 := by
      unfold B0579.density; simp
    simp [hd]
  rw [h1, withDensity_one]

lemma norm_cplx_le (v : Coord → Axi.Merid) (x : Coord) :
    ‖cplx v x‖ ≤ 2 * ‖v x‖ := by
  have h0 : ‖cplx v x 0‖ ≤ ‖v x‖ := by
    simpa [cplx] using PiLp.norm_apply_le (v x) 0
  have h1 : ‖cplx v x 1‖ ≤ ‖v x‖ := by
    simpa [cplx] using PiLp.norm_apply_le (v x) 1
  linarith [FlatKH2.norm_le_comp_add (cplx v x)]

lemma eLpNorm_two_exp_cell_lt_top {c B κ : ℝ} (hc : 0 < c) (hB : 0 ≤ B) (hκ : 0 < κ) :
    eLpNorm (fun y : B0579.Plane => B * Real.exp (-(κ * |y.2| / c))) 2
      (volume.restrict (B0579.cell c)) < ⊤ := by
  rw [eLpNorm_lt_top_iff_lintegral_rpow_enorm_lt_top (by norm_num) (by norm_num)]
  simp only [ENNReal.toReal_ofNat]
  set a : ℝ := 2 * κ / c
  have ha : 0 < a := by positivity
  have hpt : ∀ y : B0579.Plane,
      ‖B * Real.exp (-(κ * |y.2| / c))‖ₑ ^ (2 : ℝ) =
        ENNReal.ofReal (B ^ 2) * ENNReal.ofReal (Real.exp (-(a * |y.2|))) := by
    intro y
    have hnn : 0 ≤ B * Real.exp (-(κ * |y.2| / c)) := by positivity
    rw [Real.enorm_eq_ofReal hnn, ENNReal.ofReal_rpow_of_nonneg hnn (by norm_num),
      show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast, mul_pow,
      ← Real.exp_nat_mul, ENNReal.ofReal_mul (by positivity)]
    congr 2
    dsimp only [a]
    ring
  simp_rw [hpt]
  rw [lintegral_const_mul _ (Measurable.ennreal_ofReal (by fun_prop))]
  refine ENNReal.mul_lt_top ENNReal.ofReal_lt_top ?_
  have hprod : volume.restrict (B0579.cell c) =
      (volume.restrict (Ico (-(c / 2)) (c / 2))).prod (volume : Measure ℝ) := by
    symm
    calc (volume.restrict (Ico (-(c / 2)) (c / 2))).prod (volume : Measure ℝ)
        = (volume.restrict (Ico (-(c / 2)) (c / 2))).prod ((volume : Measure ℝ).restrict univ) := by
            rw [Measure.restrict_univ]
      _ = ((volume : Measure ℝ).prod (volume : Measure ℝ)).restrict
            (Ico (-(c / 2)) (c / 2) ×ˢ univ) := Measure.prod_restrict _ _
      _ = volume.restrict (B0579.cell c) := by
            rw [← Measure.volume_eq_prod ℝ ℝ]; rfl
  rw [hprod, lintegral_prod _ (Measurable.ennreal_ofReal (by fun_prop)).aemeasurable]
  simp only [lintegral_const]
  refine lt_of_le_of_lt
    (mul_le_mul_of_nonneg_right (WeightNormAux.lintegral_exp_neg_abs_le ha) zero_le) ?_
  refine ENNReal.mul_lt_top ENNReal.ofReal_lt_top ?_
  simp

/-- Uniform `sliceH1Norm` bound for `inletProf p α` across all ages `s : ℝ`. -/
lemma sliceH1Norm_inletProf_bound {p : Params} {d dm dp : ℝ} {lam : ℂ} {q : Planar.Profile}
    (hq : Planar.IsGrowingEigenpair lam q) (hreg : BgRegime p d dm dp)
    (hν_half : p.ν ≤ 1 / 2) (hmode : p.mode = q) (α : E2) :
    ∃ M_E : ℝ, 0 ≤ M_E ∧ ∀ s : ℝ,
      sliceH1Norm p.c (inletProf p α) (inletProfQ p α) (inletProfEta p α) s ≤
        ENNReal.ofReal M_E := by
  have hc : 0 < p.c := p.c_pos
  have hc1 : 1 ≤ p.c := by
    have hνpos : 0 < p.ν := p.ν_pos
    rw [hreg.c_eq, one_le_inv₀ (by positivity)]
    nlinarith
  obtain ⟨C0, κ, N, hC0, hκ, hcut⟩ := cutStreamJets lam q hq 2
  set B_cut : ℝ := C0 * (1 + p.H⁻¹) ^ 2 * p.c ^ N
  have hH_pos : 0 < p.H := p.H_pos
  have hB_pos : 0 < B_cut := by positivity
  have hin_jet : ∀ (i : Fin 2) (l : ℕ), l ≤ 1 → ∀ x : Coord,
      ‖iteratedFDeriv ℝ l (inletE0 p i) x‖ ≤
        2 * B_cut * Real.exp (-(κ * |x.2.2| / p.c)) := by
    intro i l hl x
    obtain ⟨hφ, hjet⟩ := hcut p hmode hc1 hH_pos i
    set b : ℝ := B_cut * Real.exp (-(κ * |x.2.2| / p.c))
    have hb : ∀ k ≤ 2, ‖iteratedFDeriv ℝ k (p.cutStream i) x‖ ≤ b := fun k hk => hjet k hk x
    have hFD : ∀ v : Coord, ContDiff ℝ ∞ (fun m => fderiv ℝ (p.cutStream i) m v) := fun v =>
      (hφ.fderiv_right (m := ∞) (by simp)).clm_apply contDiff_const
    have hdir : ∀ v : Coord, ‖v‖ ≤ 1 →
        ‖iteratedFDeriv ℝ l (fun m => fderiv ℝ (p.cutStream i) m v) x‖ ≤ b := by
      intro v hv
      refine (icj_partial hφ v l x).trans ?_
      exact (mul_le_mul hv (hb (l + 1) (by omega)) (norm_nonneg _) zero_le_one).trans
        (le_of_eq (one_mul b))
    have nQ : ‖((0 : ℝ), ((1 : ℝ), (0 : ℝ)))‖ ≤ 1 := by simp [Prod.norm_def]
    have nE : ‖((0 : ℝ), ((0 : ℝ), (1 : ℝ)))‖ ≤ 1 := by simp [Prod.norm_def]
    have hQ := hdir _ nQ
    have hE := hdir _ nE
    have hFDQ : ContDiff ℝ ∞ (Axi.dQ (p.cutStream i)) := hFD _
    have hFDE : ContDiff ℝ ∞ (Axi.dEta (p.cutStream i)) := hFD _
    have hm1 : ‖(Axi.m1 : Axi.Merid)‖ = 1 := by simp [Axi.m1]
    have hm0' : ‖-(Axi.m0 : Axi.Merid)‖ = 1 := by simp [Axi.m0]
    have hle : (l : ℕ∞ω) ≤ (∞ : ℕ∞ω) := by exact_mod_cast le_top
    have e : inletE0 p i = (fun m => Axi.dEta (p.cutStream i) m • (-Axi.m0)) +
        (fun m => Axi.dQ (p.cutStream i) m • Axi.m1) := by
      funext m; simp only [inletE0, Pi.add_apply, smul_neg, neg_smul]
    rw [e, iteratedFDeriv_add_apply]
    · refine (norm_add_le _ _).trans ?_
      have a1 := icj_smulVec hFDE (-Axi.m0) l x
      have a2 := icj_smulVec hFDQ Axi.m1 l x
      rw [hm0'] at a1
      rw [hm1] at a2
      have hQ' : ‖iteratedFDeriv ℝ l (Axi.dQ (p.cutStream i)) x‖ ≤
          B_cut * Real.exp (-(κ * |x.2.2| / p.c)) := hQ
      have hE' : ‖iteratedFDeriv ℝ l (Axi.dEta (p.cutStream i)) x‖ ≤
          B_cut * Real.exp (-(κ * |x.2.2| / p.c)) := hE
      linarith [a1, a2, hQ', hE']
    · exact ((hFDE.smul contDiff_const).of_le hle).contDiffAt
    · exact ((hFDQ.smul contDiff_const).of_le hle).contDiffAt
  set B_α : ℝ := (|α 0| + |α 1|) * (4 * B_cut)
  have hBα_nn : 0 ≤ B_α := by positivity
  have hpt_all : ∀ x : Coord,
      ‖inletProf p α x‖ ≤ B_α * Real.exp (-(κ * |x.2.2| / p.c)) ∧
      ‖inletProfQ p α x‖ ≤ B_α * Real.exp (-(κ * |x.2.2| / p.c)) ∧
      ‖inletProfEta p α x‖ ≤ B_α * Real.exp (-(κ * |x.2.2| / p.c)) := by
    intro x
    set E : ℝ := Real.exp (-(κ * |x.2.2| / p.c))
    have h0_i : ∀ i : Fin 2, ‖cplx (inletE0 p i) x‖ ≤ 4 * B_cut * E := by
      intro i
      have h := hin_jet i 0 (by omega) x
      rw [norm_iteratedFDeriv_zero] at h
      linarith [norm_cplx_le (inletE0 p i) x]
    have hQ_i : ∀ i : Fin 2, ‖cplx (Axi.dQ (inletE0 p i)) x‖ ≤ 4 * B_cut * E := by
      intro i
      have h := hin_jet i 1 le_rfl x
      rw [norm_iteratedFDeriv_one] at h
      have nQ : ‖((0 : ℝ), ((1 : ℝ), (0 : ℝ)))‖ ≤ 1 := by simp [Prod.norm_def]
      have hd : ‖Axi.dQ (inletE0 p i) x‖ ≤ 2 * B_cut * E :=
        (((fderiv ℝ (inletE0 p i) x).le_opNorm _).trans
          (mul_le_of_le_one_right (norm_nonneg _) nQ)).trans h
      linarith [norm_cplx_le (Axi.dQ (inletE0 p i)) x]
    have hE_i : ∀ i : Fin 2, ‖cplx (Axi.dEta (inletE0 p i)) x‖ ≤ 4 * B_cut * E := by
      intro i
      have h := hin_jet i 1 le_rfl x
      rw [norm_iteratedFDeriv_one] at h
      have nE : ‖((0 : ℝ), ((0 : ℝ), (1 : ℝ)))‖ ≤ 1 := by simp [Prod.norm_def]
      have hd : ‖Axi.dEta (inletE0 p i) x‖ ≤ 2 * B_cut * E :=
        (((fderiv ℝ (inletE0 p i) x).le_opNorm _).trans
          (mul_le_of_le_one_right (norm_nonneg _) nE)).trans h
      linarith [norm_cplx_le (Axi.dEta (inletE0 p i)) x]
    have hcomb : ∀ (f : Fin 2 → CProf), (∀ i, ‖f i x‖ ≤ 4 * B_cut * E) →
        ‖∑ i : Fin 2, ((α i : ℝ) : ℂ) • f i x‖ ≤ B_α * E := by
      intro f hf
      rw [Fin.sum_univ_two]
      refine (norm_add_le _ _).trans ?_
      simp only [norm_smul, Complex.norm_real, Real.norm_eq_abs]
      have s0 := mul_le_mul_of_nonneg_left (hf 0) (abs_nonneg (α 0))
      have s1 := mul_le_mul_of_nonneg_left (hf 1) (abs_nonneg (α 1))
      dsimp only [B_α]
      linarith
    exact ⟨hcomb _ h0_i, hcomb _ hQ_i, hcomb _ hE_i⟩
  have hG_lt := eLpNorm_two_exp_cell_lt_top hc hBα_nn hκ
  set R_G : ℝ := (eLpNorm (fun y : B0579.Plane => B_α * Real.exp (-(κ * |y.2| / p.c))) 2
      (volume.restrict (B0579.cell p.c))).toReal
  have hRG_eq : eLpNorm (fun y : B0579.Plane => B_α * Real.exp (-(κ * |y.2| / p.c))) 2
      (volume.restrict (B0579.cell p.c)) = ENNReal.ofReal R_G :=
    (ENNReal.ofReal_toReal hG_lt.ne).symm
  have hRG_nn : 0 ≤ R_G := ENNReal.toReal_nonneg
  refine ⟨3 * R_G, by positivity, fun s => ?_⟩
  unfold sliceH1Norm
  have b1 : eLpNorm (fun y => inletProf p α (s, y)) 2 (volume.restrict (B0579.cell p.c)) ≤
      ENNReal.ofReal R_G := hRG_eq ▸ eLpNorm_mono_real fun y => (hpt_all (s, y)).1
  have b2 : eLpNorm (fun y => inletProfQ p α (s, y)) 2 (volume.restrict (B0579.cell p.c)) ≤
      ENNReal.ofReal R_G := hRG_eq ▸ eLpNorm_mono_real fun y => (hpt_all (s, y)).2.1
  have b3 : eLpNorm (fun y => inletProfEta p α (s, y)) 2 (volume.restrict (B0579.cell p.c)) ≤
      ENNReal.ofReal R_G := hRG_eq ▸ eLpNorm_mono_real fun y => (hpt_all (s, y)).2.2
  refine (add_le_add (add_le_add b1 b2) b3).trans ?_
  rw [← ENNReal.ofReal_add hRG_nn hRG_nn, ← ENNReal.ofReal_add (by positivity) hRG_nn]
  exact le_of_eq (by congr 1; ring)

lemma stronglyMeasurable_inletProf_triple {p : Params} {d dm dp : ℝ} {lam : ℂ}
    {q : Planar.Profile} (hq : Planar.IsGrowingEigenpair lam q) (hreg : BgRegime p d dm dp)
    (hν1 : p.ν ≤ 1) (hmode : p.mode = q) (α : E2) :
    StronglyMeasurable (inletProf p α) ∧
      StronglyMeasurable (inletProfQ p α) ∧
      StronglyMeasurable (inletProfEta p α) ∧
      QPeriodic p.c (inletProfQ p α) ∧
      QPeriodic p.c (inletProfEta p α) := by
  have hE0 : ∀ i : Fin 2, ContDiff ℝ ∞ (inletE0 p i) :=
    fun i => F10Help.contDiff_inletE0 hq hreg hν1 hmode i
  have hEQ : ∀ i : Fin 2, ContDiff ℝ ∞ (Axi.dQ (inletE0 p i)) := fun i =>
    ((hE0 i).fderiv_right (m := ∞) (by simp)).clm_apply contDiff_const
  have hEE : ∀ i : Fin 2, ContDiff ℝ ∞ (Axi.dEta (inletE0 p i)) := fun i =>
    ((hE0 i).fderiv_right (m := ∞) (by simp)).clm_apply contDiff_const
  have hcplx_cd : ∀ (F : Coord → Axi.Merid), ContDiff ℝ ∞ F → Continuous (cplx F) := by
    intro F hF
    have heq : cplx F = fun x => liftM (F x) := by ext x j; simp [cplx, liftM]
    rw [heq]
    exact FreeInteractionAux.continuous_liftM.comp hF.continuous
  have hcomb_cont : ∀ (F : Fin 2 → Coord → Axi.Merid), (∀ i, ContDiff ℝ ∞ (F i)) →
      Continuous (fun x => ∑ i : Fin 2, ((α i : ℝ) : ℂ) • cplx (F i) x) := by
    intro F hF
    simp_rw [Fin.sum_univ_two]
    exact (Continuous.const_smul (hcplx_cd (F 0) (hF 0)) ((α 0 : ℝ) : ℂ)).add
      (Continuous.const_smul (hcplx_cd (F 1) (hF 1)) ((α 1 : ℝ) : ℂ))
  have hin_w := inletProf_hasWeakVec hq hreg hν1 hmode α
  have hper0 := qPeriodic_inletProf p α
  exact ⟨(hcomb_cont _ hE0).stronglyMeasurable,
    (hcomb_cont _ hEQ).stronglyMeasurable,
    (hcomb_cont _ hEE).stronglyMeasurable,
    F8L.qperiodic_deriv ![0, 1, 0] hper0 hin_w.1,
    F8L.qperiodic_deriv ![0, 0, 1] hper0 hin_w.2⟩

/-- Borel upgrade of `w = z - inletProf p α` and its spatial derivatives, together with a.e.
`L^{bgp}(Cyl.avgμ p.c)`, `MemLp 2(cell)`, and `HasWeakCellDerivC` slice regularity. -/
lemma upgrade_w_triple {p : Params} {d dm dp : ℝ} {lam : ℂ} {q : Planar.Profile}
    (hq : Planar.IsGrowingEigenpair lam q) (hreg : BgRegime p d dm dp)
    (hν_half : p.ν ≤ 1 / 2) (hmode : p.mode = q) (α : E2)
    {z zq zη : CProf} (hz_per : QPeriodic p.c z)
    (hzq : HasWeakVec vQ0 dZero z zq) (hzη : HasWeakVec vEta dZero z zη)
    {M₁ : ℝ} (hH1_z : ∀ s : ℝ, 0 < s → sliceH1Norm p.c z zq zη s ≤ ENNReal.ofReal M₁) :
    ∃ (w₁ wq₁ wη₁ : CProf) (C_w : ℝ),
      0 ≤ C_w ∧
      StronglyMeasurable w₁ ∧ StronglyMeasurable wq₁ ∧ StronglyMeasurable wη₁ ∧
      QPeriodic p.c w₁ ∧ QPeriodic p.c wq₁ ∧ QPeriodic p.c wη₁ ∧
      w₁ =ᵐ[volume.restrict {x : Coord | 0 < x.1}] (fun x => z x - inletProf p α x) ∧
      wq₁ =ᵐ[volume.restrict {x : Coord | 0 < x.1}] (fun x => zq x - inletProfQ p α x) ∧
      wη₁ =ᵐ[volume.restrict {x : Coord | 0 < x.1}] (fun x => zη x - inletProfEta p α x) ∧
      (∀ᵐ s ∂volume, 0 < s →
        eLpNorm (fun y => w₁ (s, y)) (ENNReal.ofReal bgp) (Cyl.avgμ p.c) ≤ ENNReal.ofReal C_w ∧
        MemLp (fun y => w₁ (s, y)) 2 (volume.restrict (B0579.cell p.c)) ∧
        MemLp (fun y => wq₁ (s, y)) 2 (volume.restrict (B0579.cell p.c)) ∧
        MemLp (fun y => wη₁ (s, y)) 2 (volume.restrict (B0579.cell p.c)) ∧
        (∀ i : Fin 2, IIIa.HasWeakCellDerivC p.c 0 (fun y => w₁ (s, y) i) (fun y => wq₁ (s, y) i)) ∧
        (∀ i : Fin 2, IIIa.HasWeakCellDerivC p.c 1 (fun y => w₁ (s, y) i) (fun y => wη₁ (s, y) i))) := by
  have hc : 0 < p.c := p.c_pos
  have hν : 0 < p.ν := p.ν_pos
  have hν1 : p.ν ≤ 1 := hν_half.trans (by norm_num)
  have hc4 : 4 ≤ p.c := by
    rw [hreg.c_eq]
    have h2p : 0 < p.ν ^ 2 := by positivity
    have h2 : p.ν ^ 2 ≤ 1 / 4 := by nlinarith
    rw [le_inv_comm₀ (by norm_num) h2p]
    linarith
  have hc1 : 1 ≤ p.c := by linarith
  have hzq_per : QPeriodic p.c zq := F8L.qperiodic_deriv ![0, 1, 0] hz_per hzq
  have hzη_per : QPeriodic p.c zη := F8L.qperiodic_deriv ![0, 0, 1] hz_per hzη
  have hloc_z : ∀ i : Fin 2, LocallyIntegrableOn (fun x => z x i) {x : Coord | 0 < x.1} volume :=
    fun i => (F8Duh.locInt_of_hasWeakFO_q (hzq i)).1
  have hloc_zq : ∀ i : Fin 2, LocallyIntegrableOn (fun x => zq x i) {x : Coord | 0 < x.1} volume :=
    fun i => (F8Duh.locInt_of_hasWeakFO_q (hzq i)).2
  have hloc_zη : ∀ i : Fin 2, LocallyIntegrableOn (fun x => zη x i) {x : Coord | 0 < x.1} volume := by
    intro i x₀ hx₀
    have hU : IsOpen {x : Coord | 0 < x.1} := isOpen_lt continuous_const continuous_fst
    obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 hU x₀ hx₀
    let χ : ContDiffBump x₀ := ⟨ε / 4, ε / 2, by positivity, by linarith⟩
    have hχ : IsCoordTest χ := by
      refine ⟨χ.contDiff, χ.hasCompactSupport, ?_⟩
      rw [χ.tsupport_eq]
      intro y hy
      have hy' := Metric.mem_closedBall.1 hy
      have hyb : y ∈ Metric.ball x₀ ε := by
        rw [Metric.mem_ball]; simp only [χ] at hy'; linarith
      simpa using hball hyb
    refine ⟨Metric.closedBall x₀ (ε / 4),
      mem_nhdsWithin_of_mem_nhds (Metric.closedBall_mem_nhds x₀ (by positivity)), ?_⟩
    refine (((hzη i).1 χ hχ).2.integrableOn (s := Metric.closedBall x₀ (ε / 4))).congr_fun
      (fun y hy => ?_) Metric.isClosed_closedBall.measurableSet
    simp [χ.one_of_mem_closedBall hy]
  obtain ⟨z₁, hz₁_sm, hz₁_per, hz₁_ae⟩ := F8Duh.exists_sm_qper_pos hz_per hloc_z
  obtain ⟨zq₁, hzq₁_sm, hzq₁_per, hzq₁_ae⟩ := F8Duh.exists_sm_qper_pos hzq_per hloc_zq
  obtain ⟨zη₁, hzη₁_sm, hzη₁_per, hzη₁_ae⟩ := F8Duh.exists_sm_qper_pos hzη_per hloc_zη
  have hz₁q : HasWeakVec vQ0 dZero z₁ zq₁ := fun i =>
    F8L.hasWeakFO_congr vQ0 dZero
      (hz₁_ae.symm.mono fun _ hx => congrArg (fun v => v i) hx)
      (hzq₁_ae.symm.mono fun _ hx => congrArg (fun v => v i) hx) (hzq i)
  have hz₁η : HasWeakVec vEta dZero z₁ zη₁ := fun i =>
    F8L.hasWeakFO_congr vEta dZero
      (hz₁_ae.symm.mono fun _ hx => congrArg (fun v => v i) hx)
      (hzη₁_ae.symm.mono fun _ hx => congrArg (fun v => v i) hx) (hzη i)
  obtain ⟨hE_sm, hEQ_sm, hEE_sm, hEQ_per, hEE_per⟩ :=
    stronglyMeasurable_inletProf_triple hq hreg hν1 hmode α
  have hE_per := qPeriodic_inletProf p α
  have hin_w := inletProf_hasWeakVec hq hreg hν1 hmode α
  let w₁ : CProf := fun x => z₁ x - inletProf p α x
  let wq₁ : CProf := fun x => zq₁ x - inletProfQ p α x
  let wη₁ : CProf := fun x => zη₁ x - inletProfEta p α x
  have hw₁_sm : StronglyMeasurable w₁ := hz₁_sm.sub hE_sm
  have hwq₁_sm : StronglyMeasurable wq₁ := hzq₁_sm.sub hEQ_sm
  have hwη₁_sm : StronglyMeasurable wη₁ := hzη₁_sm.sub hEE_sm
  have hw₁_per : QPeriodic p.c w₁ := by
    filter_upwards [hz₁_per, hE_per] with x h1 h2; simp [w₁, h1, h2]
  have hwq₁_per : QPeriodic p.c wq₁ := by
    filter_upwards [hzq₁_per, hEQ_per] with x h1 h2; simp [wq₁, h1, h2]
  have hwη₁_per : QPeriodic p.c wη₁ := by
    filter_upwards [hzη₁_per, hEE_per] with x h1 h2; simp [wη₁, h1, h2]
  have hw₁_q : HasWeakVec vQ0 dZero w₁ wq₁ := by
    have he1 : w₁ = fun x => z₁ x + (-1 : ℂ) • inletProf p α x := by
      funext x; ext i; simp [w₁, sub_eq_add_neg]
    have he2 : wq₁ = fun x => zq₁ x + (-1 : ℂ) • inletProfQ p α x := by
      funext x; ext i; simp [wq₁, sub_eq_add_neg]
    rw [he1, he2]
    exact F10Help.hasWeakVec_add' hz₁q (F10Help.hasWeakVec_smul (-1 : ℂ) hin_w.1)
  have hw₁_η : HasWeakVec vEta dZero w₁ wη₁ := by
    have he1 : w₁ = fun x => z₁ x + (-1 : ℂ) • inletProf p α x := by
      funext x; ext i; simp [w₁, sub_eq_add_neg]
    have he2 : wη₁ = fun x => zη₁ x + (-1 : ℂ) • inletProfEta p α x := by
      funext x; ext i; simp [wη₁, sub_eq_add_neg]
    rw [he1, he2]
    exact F10Help.hasWeakVec_add' hz₁η (F10Help.hasWeakVec_smul (-1 : ℂ) hin_w.2)
  obtain ⟨M_E, hME_nn, hH1_E⟩ := sliceH1Norm_inletProf_bound hq hreg hν_half hmode α
  obtain ⟨K_sob, hK_ne, hSob⟩ := FlatKH2.sliceSobolev_proof
  set M_w : ℝ := max M₁ 0 + M_E
  have hMw_nn : 0 ≤ M_w := by positivity
  set C_w : ℝ := K_sob.toReal * M_w
  have hCw_nn : 0 ≤ C_w := by positivity
  have hsob_ae := (ae_restrict_iff' measurableSet_Ioi).1
    (hSob p.c hc4 w₁ wq₁ wη₁ hw₁_per hw₁_sm hwq₁_sm hwη₁_sm hw₁_q hw₁_η)
  have hjw0 := FlatBvSliceGoodAeNeeded.jointWeakToSlice_proof p.c hc 0 w₁ wq₁
    hw₁_sm hwq₁_sm hw₁_per hwq₁_per hw₁_q
  have hjw1 := FlatBvSliceGoodAeNeeded.jointWeakToSlice_proof p.c hc 1 w₁ wη₁
    hw₁_sm hwη₁_sm hw₁_per hwη₁_per hw₁_η
  refine ⟨w₁, wq₁, wη₁, C_w, hCw_nn, hw₁_sm, hwq₁_sm, hwη₁_sm, hw₁_per, hwq₁_per, hwη₁_per,
    hz₁_ae.mono fun x hx => by simp [w₁, hx],
    hzq₁_ae.mono fun x hx => by simp [wq₁, hx],
    hzη₁_ae.mono fun x hx => by simp [wη₁, hx], ?_⟩
  filter_upwards [F8L.slice_ae hz₁_ae, F8L.slice_ae hzq₁_ae, F8L.slice_ae hzη₁_ae,
    hsob_ae, hjw0, hjw1] with s hs1 hs2 hs3 hsob hcd0 hcd1 hs0
  have hz₁_H1 : sliceH1Norm p.c z₁ zq₁ zη₁ s ≤ ENNReal.ofReal (max M₁ 0) := by
    unfold sliceH1Norm
    rw [eLpNorm_congr_ae (ae_restrict_of_ae (hs1 hs0)),
      eLpNorm_congr_ae (ae_restrict_of_ae (hs2 hs0)),
      eLpNorm_congr_ae (ae_restrict_of_ae (hs3 hs0))]
    exact (hH1_z s hs0).trans (ENNReal.ofReal_le_ofReal (le_max_left M₁ 0))
  have hms : Measurable (fun y : B0579.Plane => ((s, y) : Coord)) := measurable_prodMk_left
  have hsub2 : ∀ {f g : CProf}, StronglyMeasurable f → StronglyMeasurable g →
      eLpNorm (fun y => f (s, y) - g (s, y)) 2 (volume.restrict (B0579.cell p.c)) ≤
        eLpNorm (fun y => f (s, y)) 2 (volume.restrict (B0579.cell p.c)) +
          eLpNorm (fun y => g (s, y)) 2 (volume.restrict (B0579.cell p.c)) := by
    intro f g hf hg
    have heq : (fun y => f (s, y) - g (s, y)) =
        (fun y => f (s, y)) + -(fun y => g (s, y)) := by funext y; simp [sub_eq_add_neg]
    have h1 : AEStronglyMeasurable (fun y => f (s, y)) (volume.restrict (B0579.cell p.c)) :=
      (hf.comp_measurable hms).aestronglyMeasurable
    have h2 : AEStronglyMeasurable (fun y => g (s, y)) (volume.restrict (B0579.cell p.c)) :=
      (hg.comp_measurable hms).aestronglyMeasurable
    rw [heq]
    refine (eLpNorm_add_le h1 h2.neg (by norm_num)).trans ?_
    rw [eLpNorm_neg]
  have hw₁_H1 : sliceH1Norm p.c w₁ wq₁ wη₁ s ≤ ENNReal.ofReal M_w := by
    have l1 := hsub2 hz₁_sm hE_sm
    have l2 := hsub2 hzq₁_sm hEQ_sm
    have l3 := hsub2 hzη₁_sm hEE_sm
    calc sliceH1Norm p.c w₁ wq₁ wη₁ s
        ≤ sliceH1Norm p.c z₁ zq₁ zη₁ s +
            sliceH1Norm p.c (inletProf p α) (inletProfQ p α) (inletProfEta p α) s := by
          unfold sliceH1Norm
          calc _ ≤ (eLpNorm (fun y => z₁ (s, y)) 2 _ + eLpNorm (fun y => inletProf p α (s, y)) 2 _) +
                (eLpNorm (fun y => zq₁ (s, y)) 2 _ + eLpNorm (fun y => inletProfQ p α (s, y)) 2 _) +
                (eLpNorm (fun y => zη₁ (s, y)) 2 _ + eLpNorm (fun y => inletProfEta p α (s, y)) 2 _) :=
                add_le_add (add_le_add l1 l2) l3
            _ = _ := by ac_rfl
      _ ≤ ENNReal.ofReal (max M₁ 0) + ENNReal.ofReal M_E := add_le_add hz₁_H1 (hH1_E s)
      _ = ENNReal.ofReal M_w := (ENNReal.ofReal_add (le_max_right M₁ 0) hME_nn).symm
  have hmem_w : MemLp (fun y => w₁ (s, y)) 2 (volume.restrict (B0579.cell p.c)) :=
    ⟨(hw₁_sm.comp_measurable hms).aestronglyMeasurable,
      lt_of_le_of_lt ((le_self_add.trans le_self_add).trans hw₁_H1) ENNReal.ofReal_lt_top⟩
  have hmem_wq : MemLp (fun y => wq₁ (s, y)) 2 (volume.restrict (B0579.cell p.c)) :=
    ⟨(hwq₁_sm.comp_measurable hms).aestronglyMeasurable,
      lt_of_le_of_lt ((le_add_self.trans le_self_add).trans hw₁_H1) ENNReal.ofReal_lt_top⟩
  have hmem_wη : MemLp (fun y => wη₁ (s, y)) 2 (volume.restrict (B0579.cell p.c)) :=
    ⟨(hwη₁_sm.comp_measurable hms).aestronglyMeasurable,
      lt_of_le_of_lt (le_add_self.trans hw₁_H1) ENNReal.ofReal_lt_top⟩
  have hbgp_bd : eLpNorm (fun y => w₁ (s, y)) (ENNReal.ofReal bgp) (Cyl.avgμ p.c) ≤
      ENNReal.ofReal C_w := by
    calc eLpNorm (fun y => w₁ (s, y)) (ENNReal.ofReal bgp) (Cyl.avgμ p.c)
        ≤ eLpNorm (fun y => w₁ (s, y)) (ENNReal.ofReal bgp) (volume.restrict (B0579.cell p.c)) :=
          eLpNorm_mono_measure _ (FlatKH2.avgμ_le_cell hc1)
      _ ≤ K_sob * sliceH1Norm p.c w₁ wq₁ wη₁ s := hsob hs0
      _ ≤ K_sob * ENNReal.ofReal M_w := mul_le_mul_of_nonneg_left hw₁_H1 zero_le
      _ = ENNReal.ofReal C_w := by
          rw [← ENNReal.ofReal_toReal hK_ne, ← ENNReal.ofReal_mul ENNReal.toReal_nonneg]
  exact ⟨hbgp_bd, hmem_w, hmem_wq, hmem_wη, hcd0 hs0 hmem_w hmem_wq, hcd1 hs0 hmem_w hmem_wη⟩

/-- Smooth late-age cutoff `lateCut δ s = 1 - ageCutoff (4 * δ) s`: vanishes on `s ≤ δ`, equals `1`
on `2 * δ ≤ s`, and satisfies `0 ≤ lateCut δ s ≤ 1`. -/
def lateCut (δ s : ℝ) : ℝ := 1 - ageCutoff (4 * δ) s

def lateSmul (δ : ℝ) (u : CProf) (x : Coord) : CMerid :=
  ((lateCut δ x.1 : ℝ) : ℂ) • u x

lemma contDiff_lateCut (δ : ℝ) : ContDiff ℝ ∞ (lateCut δ) :=
  contDiff_const.sub (contDiff_ageCutoff (4 * δ))

lemma lateCut_eq_zero {δ s : ℝ} (hδ : 0 < δ) (hs : s ≤ δ) : lateCut δ s = 0 := by
  unfold lateCut
  rw [ageCutoff_eq_one (by positivity : 0 < 4 * δ) (by linarith), sub_self]

lemma lateCut_eq_one {δ s : ℝ} (hδ : 0 < δ) (hs : 2 * δ ≤ s) : lateCut δ s = 1 := by
  unfold lateCut
  rw [ageCutoff_eq_zero (by positivity : 0 < 4 * δ) (by linarith), sub_zero]

lemma abs_lateCut_le_one (δ s : ℝ) : |lateCut δ s| ≤ 1 := by
  unfold lateCut ageCutoff
  have h0 : 0 ≤ Real.smoothTransition (2 - 4 * s / (4 * δ)) := Real.smoothTransition.nonneg _
  have h1 : Real.smoothTransition (2 - 4 * s / (4 * δ)) ≤ 1 := Real.smoothTransition.le_one _
  rw [abs_le]
  constructor <;> linarith

lemma inHr_lateSmul_of_slice_bound {c C_w δ : ℝ} (hc : 0 < c) (hCw : 0 ≤ C_w) (hδ : 0 < δ)
    {w w₁ : CProf} (hw_per : QPeriodic c w) (hw₁_sm : StronglyMeasurable w₁)
    (hw₁_per : QPeriodic c w₁)
    (hw₁_ae : w₁ =ᵐ[volume.restrict {x : Coord | 0 < x.1}] w)
    (hbd : ∀ᵐ s ∂volume, 0 < s →
      eLpNorm (fun y => w₁ (s, y)) (ENNReal.ofReal bgp) (Cyl.avgμ c) ≤ ENNReal.ofReal C_w) :
    InHr c bgp (lateSmul δ w) := by
  have hw_late_per : QPeriodic c (lateSmul δ w) := by
    filter_upwards [hw_per] with x hx
    show ((lateCut δ (qShift c x).1 : ℝ) : ℂ) • w (qShift c x) = _
    have hs : (qShift c x).1 = x.1 := rfl
    rw [hs, hx]; rfl
  have hw₁_late_per : QPeriodic c (lateSmul δ w₁) := by
    filter_upwards [hw₁_per] with x hx
    show ((lateCut δ (qShift c x).1 : ℝ) : ℂ) • w₁ (qShift c x) = _
    have hs : (qShift c x).1 = x.1 := rfl
    rw [hs, hx]; rfl
  have hw₁_late_sm : StronglyMeasurable (lateSmul δ w₁) :=
    (Complex.continuous_ofReal.comp ((contDiff_lateCut δ).continuous.comp
      continuous_fst)).stronglyMeasurable.smul hw₁_sm
  have hbgp_pos : (0 : ℝ) < bgp := by norm_num [bgp]
  have hp0 : ENNReal.ofReal bgp ≠ 0 := (ENNReal.ofReal_pos.2 hbgp_pos).ne'
  have hpt : ENNReal.ofReal bgp ≠ ⊤ := ENNReal.ofReal_ne_top
  have hw₁_late_inHr : InHr c bgp (lateSmul δ w₁) := by
    refine ⟨hw₁_late_per, hw₁_late_sm.aestronglyMeasurable, ?_⟩
    unfold hNorm
    rw [eLpNorm_lt_top_iff_lintegral_rpow_enorm_lt_top hp0 hpt, ENNReal.toReal_ofReal hbgp_pos.le,
      smallSlice_lintegral_hMeas c bgp _ (hw₁_late_sm.measurable.enorm.pow_const bgp)]
    have hexp : (bgp / 2 - 5 / 2 : ℝ) = -9 / 8 := by norm_num [bgp]
    rw [hexp]
    have hae_maj : ∀ᵐ σ ∂(volume.restrict (Ioi (0 : ℝ))),
        ENNReal.ofReal (σ ^ (-9 / 8 : ℝ)) *
          ∫⁻ y, ‖lateSmul δ w₁ (σ, y)‖ₑ ^ bgp ∂(Cyl.avgμ c) ≤
        (Ioi δ).indicator
          (fun t => ENNReal.ofReal (C_w ^ bgp) * ENNReal.ofReal (t ^ (-9 / 8 : ℝ))) σ := by
      filter_upwards [ae_restrict_of_ae hbd, ae_restrict_mem measurableSet_Ioi] with σ hσ hσ0
      by_cases hσδ : σ ≤ δ
      · have hnot : σ ∉ Ioi δ := not_lt.2 hσδ
        rw [Set.indicator_of_notMem hnot]
        have hlc0 : lateCut δ σ = 0 := lateCut_eq_zero hδ hσδ
        have hz0 : ∀ y, ‖lateSmul δ w₁ (σ, y)‖ₑ ^ bgp = 0 := by
          intro y; simp [lateSmul, hlc0, ENNReal.zero_rpow_of_pos hbgp_pos]
        simp [hz0]
      · have hmem : σ ∈ Ioi δ := not_le.1 hσδ
        rw [Set.indicator_of_mem hmem]
        have heLp := hσ hσ0
        rw [eLpNorm_eq_lintegral_rpow_enorm_toReal hp0 hpt,
          ENNReal.toReal_ofReal hbgp_pos.le] at heLp
        have hint_le : ∫⁻ y, ‖w₁ (σ, y)‖ₑ ^ bgp ∂(Cyl.avgμ c) ≤ ENNReal.ofReal (C_w ^ bgp) := by
          have h1 := ENNReal.rpow_le_rpow heLp hbgp_pos.le
          rwa [← ENNReal.rpow_mul, one_div_mul_cancel hbgp_pos.ne', ENNReal.rpow_one,
            ENNReal.ofReal_rpow_of_nonneg hCw hbgp_pos.le] at h1
        have hlc_le : ∫⁻ y, ‖lateSmul δ w₁ (σ, y)‖ₑ ^ bgp ∂(Cyl.avgμ c) ≤
            ENNReal.ofReal (C_w ^ bgp) := by
          refine (lintegral_mono fun y => ENNReal.rpow_le_rpow ?_ hbgp_pos.le).trans hint_le
          rw [← ofReal_norm, ← ofReal_norm]
          apply ENNReal.ofReal_le_ofReal
          simp only [lateSmul, norm_smul, Complex.norm_real, Real.norm_eq_abs]
          exact mul_le_of_le_one_left (norm_nonneg _) (abs_lateCut_le_one δ σ)
        rw [mul_comm]
        exact mul_le_mul_of_nonneg_right hlc_le zero_le
    refine lt_of_le_of_lt (lintegral_mono_ae hae_maj) ?_
    rw [lintegral_indicator measurableSet_Ioi _,
      Measure.restrict_restrict measurableSet_Ioi,
      Set.inter_eq_self_of_subset_left (Ioi_subset_Ioi hδ.le),
      lintegral_const_mul _ (Axi.measurable_ofReal_rpow (-9 / 8))]
    refine ENNReal.mul_lt_top ENNReal.ofReal_lt_top ?_
    have hint_rpow :=
      (integrableOn_Ioi_rpow_of_lt (by norm_num : (-9 / 8 : ℝ) < -1) hδ).hasFiniteIntegral
    unfold HasFiniteIntegral at hint_rpow
    refine lt_of_eq_of_lt (setLIntegral_congr_fun measurableSet_Ioi fun σ hσ => ?_) hint_rpow
    have hnn : 0 ≤ σ ^ (-9 / 8 : ℝ) := Real.rpow_nonneg (hδ.trans hσ).le _
    rw [Real.enorm_eq_ofReal hnn]
  have hae_pos : ∀ᵐ x : Coord, 0 < x.1 → lateSmul δ w x = lateSmul δ w₁ x := by
    have hU : MeasurableSet {x : Coord | 0 < x.1} :=
      (isOpen_lt continuous_const continuous_fst).measurableSet
    filter_upwards [(ae_restrict_iff' hU).1 hw₁_ae] with x hx hp
    simp [lateSmul, hx hp]
  exact inHr_congr_ae hw_late_per hw₁_late_inHr (hMeasAe c bgp _ hc hae_pos)

lemma lateSmul_solenoidal (δ : ℝ) {d : CProf}
    (hsol : ∀ φ : Coord → ℝ, IsCoordTest φ →
      Integrable (fun x => d x 0 * (cpd 1 φ x : ℂ) + d x 1 * (cpd 2 φ x : ℂ)) ∧
        ∫ x, (d x 0 * (cpd 1 φ x : ℂ) + d x 1 * (cpd 2 φ x : ℂ)) = 0) :
    ∀ φ : Coord → ℝ, IsCoordTest φ →
      Integrable (fun x => lateSmul δ d x 0 * (cpd 1 φ x : ℂ) +
          lateSmul δ d x 1 * (cpd 2 φ x : ℂ)) ∧
        ∫ x, (lateSmul δ d x 0 * (cpd 1 φ x : ℂ) + lateSmul δ d x 1 * (cpd 2 φ x : ℂ)) = 0 := by
  intro φ hφ
  let ψ : Coord → ℝ := fun x => lateCut δ x.1 * φ x
  have hψ : IsCoordTest ψ :=
    ⟨((contDiff_lateCut δ).comp contDiff_fst).mul hφ.smooth,
      hφ.compact.mul_left, tsupport_mul_subset_right.trans hφ.supp⟩
  have hcpd : ∀ x : Coord,
      cpd 1 ψ x = lateCut δ x.1 * cpd 1 φ x ∧ cpd 2 ψ x = lateCut δ x.1 * cpd 2 φ x := by
    intro x
    have hf1 := (((contDiff_lateCut δ).differentiable (by simp) x.1).hasDerivAt.hasFDerivAt).comp
      x hasFDerivAt_fst
    have hfm := (hf1.mul (hφ.smooth.differentiable (by simp) x).hasFDerivAt).fderiv
    have hψ_eq : ψ = (lateCut δ ∘ Prod.fst) * φ := rfl
    constructor
    · show fderiv ℝ ψ x (cdir 1) = _
      rw [hψ_eq, hfm]; simp [cpd, cdir]
    · show fderiv ℝ ψ x (cdir 2) = _
      rw [hψ_eq, hfm]; simp [cpd, cdir]
  have heq : (fun x => lateSmul δ d x 0 * (cpd 1 φ x : ℂ) +
      lateSmul δ d x 1 * (cpd 2 φ x : ℂ)) =
      fun x => d x 0 * (cpd 1 ψ x : ℂ) + d x 1 * (cpd 2 ψ x : ℂ) := by
    funext x
    obtain ⟨c1, c2⟩ := hcpd x
    simp only [lateSmul, PiLp.smul_apply, smul_eq_mul, c1, c2, Complex.ofReal_mul]
    ring
  rw [heq]
  exact hsol ψ hψ

/-- Heat stream `heatStreamH ν ζ` satisfies `HeatSol`, `L^{r'}` gradient contraction, `L^{r'}`
initial convergence, AND `L²(cell)` contraction of `H(τ, ·)` and `∇^⊥ H(τ, ·)`. -/
lemma heatStreamH_props {c ν r : ℝ} (hc : 0 < c) (hν : 0 < ν) (hr : 1 < r)
    {ζ : ℝ × ℝ → ℝ} (hζ : NiceStream c ζ) :
    HeatSol c ν (r / (r - 1)) (heatStreamH ν ζ) ∧
    (∀ τ : ℝ, 0 < τ → ∀ i : Fin 2,
      ∫⁻ p, ‖perpGrad (fun z => heatStreamH ν ζ (τ, z)) p i‖ₑ ^ (r / (r - 1)) ∂(Cyl.avgμ c) ≤
        ∫⁻ p, ‖perpGrad ζ p i‖ₑ ^ (r / (r - 1)) ∂(Cyl.avgμ c)) ∧
    (∀ i : Fin 2, Tendsto (fun τ : ℝ =>
      ∫⁻ p, ‖perpGrad (fun z => heatStreamH ν ζ (τ, z)) p i - perpGrad ζ p i‖ₑ ^ (r / (r - 1))
        ∂(Cyl.avgμ c)) (𝓝[>] (0 : ℝ)) (𝓝 0)) ∧
    (∀ τ : ℝ, 0 < τ →
      eLpNorm (fun p => (heatStreamH ν ζ (τ, p) : ℂ)) 2 (volume.restrict (B0579.cell c)) ≤
        eLpNorm (fun p => (ζ p : ℂ)) 2 (volume.restrict (B0579.cell c)) ∧
      (∀ i : Fin 2,
        MemLp (fun p => (perpGrad (fun z => heatStreamH ν ζ (τ, z)) p i : ℂ)) 2
          (volume.restrict (B0579.cell c)))) ∧
    eLpNorm (fun p => (ζ p : ℂ)) 2 (volume.restrict (B0579.cell c)) < ⊤ := by
  set r' : ℝ := r / (r - 1)
  have hr' : 1 < r' := by rw [lt_div_iff₀ (by linarith)]; linarith
  let H : Coord → ℝ := heatStreamH ν ζ
  have hopen : IsOpen (Ioi (0 : ℝ) ×ˢ (univ : Set (ℝ × ℝ))) := isOpen_Ioi.prod isOpen_univ
  have hper : ∀ x : Coord, 0 < x.1 → H (qShift c x) = H x := by
    intro x hx
    have hx' : 0 < (qShift c x).1 := hx
    simp only [H, heatStreamH, hx, hx', ↓reduceIte]
    refine integral_congr_ae (Eventually.of_forall fun w => ?_)
    have e : (qShift c x).2 - w = ((x.2 - w).1 + c, (x.2 - w).2) := by
      ext <;> simp [qShift]
      ring
    show UnforcedLeray.B0284.heatKernel2 (ν * x.1) w * ζ ((qShift c x).2 - w) =
      UnforcedLeray.B0284.heatKernel2 (ν * x.1) w * ζ (x.2 - w)
    rw [e, hζ.periodic]
  have hdiff : ∀ τ : ℝ, 0 < τ → ∀ p : ℝ × ℝ, DifferentiableAt ℝ H (τ, p) := fun τ hτ p =>
    ((heatConvSmooth c ν ζ hc hν hζ).contDiffAt
      (hopen.mem_nhds (show (τ, p) ∈ Ioi (0 : ℝ) ×ˢ univ from ⟨hτ, mem_univ p⟩))).differentiableAt
        (by simp)
  have hperp : ∀ τ : ℝ, 0 < τ → ∀ (p : ℝ × ℝ) (i : Fin 2),
      perpGrad (fun z => H (τ, z)) p i =
        ∫ w : ℝ × ℝ, UnforcedLeray.B0284.heatKernel2 (ν * τ) w * perpGradComp ζ i (p - w) := by
    intro τ hτ p i
    have hd := hdiff τ hτ p
    have e0 := heatConvCpd c ν ζ hc hν hζ (τ, p) hτ
    fin_cases i
    · show fderiv ℝ (fun z => H (τ, z)) p (0, 1) = _
      rw [slice_fderiv hd]
      have : fderiv ℝ H (τ, p) (0, (0, 1)) = cpd 2 H (τ, p) := rfl
      rw [this, e0.2, heatStreamH_of_pos _ hτ]; rfl
    · show -fderiv ℝ (fun z => H (τ, z)) p (1, 0) = _
      rw [slice_fderiv hd]
      have : fderiv ℝ H (τ, p) (0, (1, 0)) = cpd 1 H (τ, p) := rfl
      rw [this, e0.1, heatStreamH_of_pos _ hτ, ← integral_neg]
      refine integral_congr_ae (Eventually.of_forall fun w => ?_)
      simp [perpGradComp]
  have hcomp : ∀ i : Fin 2, Continuous (perpGradComp ζ i) ∧
      (∀ z : ℝ × ℝ, perpGradComp ζ i (z.1 + c, z.2) = perpGradComp ζ i z) ∧
      (∃ L : ℝ, ∀ z : ℝ × ℝ, L ≤ |z.2| → perpGradComp ζ i z = 0) := by
    intro i
    obtain ⟨hqd, hed, -, -⟩ := niceStreamClosure c ζ ζ 1 hζ hζ
    fin_cases i
    · exact ⟨hed.smooth.continuous, hed.periodic, hed.compact⟩
    · refine ⟨hqd.smooth.continuous.neg, fun z => ?_, ?_⟩
      · show -qDer ζ (z.1 + c, z.2) = -qDer ζ z; rw [hqd.periodic]
      · obtain ⟨L, hL⟩ := hqd.compact
        exact ⟨L, fun z hz => by show -qDer ζ z = 0; rw [hL z hz, neg_zero]⟩
  have hH_sol : HeatSol c ν r' H :=
    ⟨heatConvSmooth c ν ζ hc hν hζ, hper, fun x hx => heatConvEq c ν ζ hc hν hζ x hx.1,
      fun n hn τ₁ τ₂ h₁ h₁₂ => heatDerivMemLp c ν r' ζ hc hν hr' hζ n hn τ₁ τ₂ h₁ h₁₂⟩
  have hcon : ∀ τ : ℝ, 0 < τ → ∀ i : Fin 2,
      ∫⁻ p, ‖perpGrad (fun z => H (τ, z)) p i‖ₑ ^ r' ∂(Cyl.avgμ c) ≤
        ∫⁻ p, ‖perpGrad ζ p i‖ₑ ^ r' ∂(Cyl.avgμ c) := by
    intro τ hτ i
    obtain ⟨hcont, hpp, hcpt⟩ := hcomp i
    have key := heatConvContraction c (ν * τ) r' (perpGradComp ζ i) hc (mul_pos hν hτ)
      hr'.le hcont hpp hcpt
    have e1 : ∀ p, ‖perpGrad (fun z => H (τ, z)) p i‖ₑ ^ r' =
        ‖∫ w : ℝ × ℝ, UnforcedLeray.B0284.heatKernel2 (ν * τ) w * perpGradComp ζ i (p - w)‖ₑ ^ r' :=
      fun p => by rw [hperp τ hτ p i]
    have e2 : ∀ p, ‖perpGrad ζ p i‖ₑ ^ r' = ‖perpGradComp ζ i p‖ₑ ^ r' :=
      fun p => by rw [perpGrad_eq_perpGradComp]
    simp only [e1, e2]; exact key
  have hconv : ∀ i : Fin 2, Tendsto (fun τ : ℝ =>
      ∫⁻ p, ‖perpGrad (fun z => H (τ, z)) p i - perpGrad ζ p i‖ₑ ^ r' ∂(Cyl.avgμ c))
      (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    intro i
    obtain ⟨hcont, hpp, hcpt⟩ := hcomp i
    have hlim := heatConvTendsto c r' (perpGradComp ζ i) hc (by linarith) hcont hpp hcpt
    have hmap : Tendsto (fun τ : ℝ => ν * τ) (𝓝[>] (0 : ℝ)) (𝓝[>] (0 : ℝ)) := by
      refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ ?_ ?_
      · have ht : Tendsto (fun τ : ℝ => ν * τ) (𝓝 (0 : ℝ)) (𝓝 (ν * 0)) :=
          (continuous_const.mul continuous_id).tendsto 0
        rw [mul_zero] at ht
        exact ht.mono_left nhdsWithin_le_nhds
      · filter_upwards [self_mem_nhdsWithin] with τ hτ using mul_pos hν hτ
    refine (hlim.comp hmap).congr' ?_
    filter_upwards [self_mem_nhdsWithin] with τ (hτ : 0 < τ)
    refine lintegral_congr fun p => ?_
    show ‖(∫ w : ℝ × ℝ, UnforcedLeray.B0284.heatKernel2 (ν * τ) w * perpGradComp ζ i (p - w)) -
        perpGradComp ζ i p‖ₑ ^ r' = _
    rw [← hperp τ hτ p i, ← perpGrad_eq_perpGradComp]
  have hζ_lt_top : eLpNorm (fun p => (ζ p : ℂ)) 2 (volume.restrict (B0579.cell c)) < ⊤ := by
    obtain ⟨L, hL⟩ := hζ.compact
    have hKc : IsCompact (Icc (-(c / 2)) (c / 2) ×ˢ Icc (-L) L) :=
      isCompact_Icc.prod isCompact_Icc
    obtain ⟨M, hM⟩ := hKc.exists_bound_of_continuousOn hζ.smooth.continuous.norm.continuousOn
    rw [eLpNorm_lt_top_iff_lintegral_rpow_enorm_lt_top (by norm_num) (by norm_num)]
    simp only [ENNReal.toReal_ofNat]
    have hKm : MeasurableSet (Icc (-(c / 2)) (c / 2) ×ˢ Icc (-L) L) :=
      measurableSet_Icc.prod measurableSet_Icc
    have hpt : ∀ p ∈ B0579.cell c, ‖(ζ p : ℂ)‖ₑ ^ (2 : ℝ) ≤
        (Icc (-(c / 2)) (c / 2) ×ˢ Icc (-L) L).indicator
          (fun _ => ENNReal.ofReal (max M 0) ^ (2 : ℝ)) p := by
      intro p hp
      by_cases hpK : p ∈ Icc (-(c / 2)) (c / 2) ×ˢ Icc (-L) L
      · rw [Set.indicator_of_mem hpK]
        apply ENNReal.rpow_le_rpow _ (by norm_num)
        rw [← ofReal_norm, Complex.norm_real]
        have h1 := hM p hpK
        rw [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)] at h1
        exact ENNReal.ofReal_le_ofReal (h1.trans (le_max_left M 0))
      · rw [Set.indicator_of_notMem hpK]
        have h2 : p.2 ∉ Icc (-L) L := fun h => hpK ⟨⟨hp.1.1, hp.1.2.le⟩, h⟩
        have hLa : L ≤ |p.2| := le_of_lt (by by_contra hc'; exact h2 (abs_le.1 (not_lt.1 hc')))
        simp [hL p hLa]
    calc ∫⁻ p in B0579.cell c, ‖(ζ p : ℂ)‖ₑ ^ (2 : ℝ)
        ≤ ∫⁻ p in B0579.cell c, (Icc (-(c / 2)) (c / 2) ×ˢ Icc (-L) L).indicator
            (fun _ => ENNReal.ofReal (max M 0) ^ (2 : ℝ)) p :=
          setLIntegral_mono' (B0579.measurableSet_cell c) hpt
      _ ≤ ∫⁻ p, (Icc (-(c / 2)) (c / 2) ×ˢ Icc (-L) L).indicator
            (fun _ => ENNReal.ofReal (max M 0) ^ (2 : ℝ)) p := setLIntegral_le_lintegral _ _
      _ = ENNReal.ofReal (max M 0) ^ (2 : ℝ) *
            volume (Icc (-(c / 2)) (c / 2) ×ˢ Icc (-L) L) := lintegral_indicator_const hKm _
      _ < ⊤ := ENNReal.mul_lt_top
            (ENNReal.rpow_lt_top_of_nonneg (by norm_num) ENNReal.ofReal_ne_top) hKc.measure_lt_top
  refine ⟨hH_sol, hcon, hconv, fun τ hτ => ⟨?_, fun i => ?_⟩, hζ_lt_top⟩
  · have hkey := heatConvContraction c (ν * τ) 2 ζ hc (mul_pos hν hτ) (by norm_num)
      hζ.smooth.continuous hζ.periodic hζ.compact
    have he1 : ∀ p : B0579.Plane, ‖(H (τ, p) : ℂ)‖ₑ ^ (2 : ℝ) =
        ‖∫ w : ℝ × ℝ, UnforcedLeray.B0284.heatKernel2 (ν * τ) w * ζ (p - w)‖ₑ ^ (2 : ℝ) := by
      intro p
      rw [← ofReal_norm, Complex.norm_real, ofReal_norm]
      change ‖heatStreamH ν ζ (τ, p)‖ₑ ^ (2 : ℝ) = _
      rw [heatStreamH_of_pos ζ hτ p]
    have he2 : ∀ p : B0579.Plane, ‖(ζ p : ℂ)‖ₑ ^ (2 : ℝ) = ‖ζ p‖ₑ ^ (2 : ℝ) := fun p => by
      rw [← ofReal_norm, Complex.norm_real, ofReal_norm]
    have havg : ∫⁻ p, ‖(H (τ, p) : ℂ)‖ₑ ^ (2 : ℝ) ∂(Cyl.avgμ c) ≤
        ∫⁻ p, ‖(ζ p : ℂ)‖ₑ ^ (2 : ℝ) ∂(Cyl.avgμ c) := by
      simp_rw [he1, he2]; exact hkey
    rw [avgμ_eq_smul_cell c, lintegral_smul_measure, lintegral_smul_measure, smul_eq_mul,
      smul_eq_mul] at havg
    have hc_ne0 : ENNReal.ofReal c⁻¹ ≠ 0 := (ENNReal.ofReal_pos.2 (inv_pos.2 hc)).ne'
    have hcell_le : ∫⁻ p in B0579.cell c, ‖(H (τ, p) : ℂ)‖ₑ ^ (2 : ℝ) ≤
        ∫⁻ p in B0579.cell c, ‖(ζ p : ℂ)‖ₑ ^ (2 : ℝ) :=
      (ENNReal.mul_le_mul_iff_right hc_ne0 ENNReal.ofReal_ne_top).1 havg
    rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by norm_num),
      eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by norm_num)]
    simp only [ENNReal.toReal_ofNat]
    exact ENNReal.rpow_le_rpow hcell_le (by positivity)
  · obtain ⟨hcont, hpp, hcpt⟩ := hcomp i
    have hkey := heatConvContraction c (ν * τ) 2 (perpGradComp ζ i) hc (mul_pos hν hτ)
      (by norm_num) hcont hpp hcpt
    have he1 : ∀ p, ‖(perpGrad (fun z => H (τ, z)) p i : ℂ)‖ₑ ^ (2 : ℝ) =
        ‖∫ w : ℝ × ℝ, UnforcedLeray.B0284.heatKernel2 (ν * τ) w * perpGradComp ζ i (p - w)‖ₑ ^
          (2 : ℝ) := fun p => by
      rw [← ofReal_norm, Complex.norm_real, ofReal_norm, hperp τ hτ p i]
    have he2 : ∀ p, ‖perpGrad ζ p i‖ₑ ^ (2 : ℝ) = ‖perpGradComp ζ i p‖ₑ ^ (2 : ℝ) :=
      fun p => by rw [perpGrad_eq_perpGradComp]
    have havg : ∫⁻ p, ‖(perpGrad (fun z => H (τ, z)) p i : ℂ)‖ₑ ^ (2 : ℝ) ∂(Cyl.avgμ c) < ⊤ := by
      simp_rw [he1]
      exact lt_of_le_of_lt hkey (by simp_rw [← he2]; exact sd_perp_lint_lt_top hc hζ two_pos i)
    rw [avgμ_eq_smul_cell c, lintegral_smul_measure, smul_eq_mul] at havg
    have hc_ne0 : ENNReal.ofReal c⁻¹ ≠ 0 := (ENNReal.ofReal_pos.2 (inv_pos.2 hc)).ne'
    have hcell_lt : ∫⁻ p in B0579.cell c,
        ‖(perpGrad (fun z => H (τ, z)) p i : ℂ)‖ₑ ^ (2 : ℝ) < ⊤ := by
      by_contra htop
      rw [not_lt, top_le_iff] at htop
      rw [htop, ENNReal.mul_top hc_ne0] at havg
      exact lt_irrefl ⊤ havg
    refine ⟨(Complex.continuous_ofReal.comp
      (sd_perp_slice_continuous hH_sol.smooth hτ i)).aestronglyMeasurable, ?_⟩
    rw [eLpNorm_lt_top_iff_lintegral_rpow_enorm_lt_top (by norm_num) (by norm_num)]
    simpa using hcell_lt

/-! ### `InHr`-only `dualF` local integrability and late-cutoff `DualFTestZero` -/

lemma dualFLocInt_inHr {c r ν : ℝ} {μ : ℂ} {b : CProf} {H : Coord → ℝ} {s : ℝ}
    (hc : 0 < c) (hν : 0 < ν) (hr : 1 < r) (hs : 0 < s)
    (hb : InHr c r b) (hH : HeatSol c ν (r / (r - 1)) H) :
    LocallyIntegrableOn (dualF c μ b H s) (Ioo (0 : ℝ) s) volume := by
  have : SFinite (Cyl.avgμ c) := sfinite_avgμ c
  have hm : AEStronglyMeasurable (dualF c μ b H s) (volume.restrict (Ioo (0 : ℝ) s)) := by
    set M : Measure Coord := (volume.restrict (Ioo (0 : ℝ) s)).prod (Cyl.avgμ c) with hM
    have hbM : AEStronglyMeasurable b M := b_aestronglyMeasurable_prod hc hb s
    have hMr : M = (volume.prod (Cyl.avgμ c)).restrict (Ioo (0 : ℝ) s ×ˢ (univ : Set (ℝ × ℝ))) := by
      rw [hM, ← Measure.prod_restrict, Measure.restrict_univ]
    have hS : MeasurableSet (Ioo (0 : ℝ) s ×ˢ (univ : Set (ℝ × ℝ))) :=
      measurableSet_Ioo.prod MeasurableSet.univ
    have hg : ∀ i : Fin 2, AEStronglyMeasurable
        (fun q : Coord => perpGrad (fun z => H (s - q.1, z)) q.2 i) M := by
      intro i; rw [hMr]
      exact ((perpGradH_continuousOn hH.smooth s i).mono
        (fun q hq => mem_ofPred_eq ▸ hq.1.2)).aestronglyMeasurable hS
    have hG : AEStronglyMeasurable (fun q : Coord => ∑ i : Fin 2, b q i *
        ((perpGrad (fun z => H (s - q.1, z)) q.2 i : ℝ) : ℂ)) M :=
      Finset.aestronglyMeasurable_fun_sum _ fun i _ =>
        ((EuclideanSpace.proj i).continuous.comp_aestronglyMeasurable hbM).mul
          (Complex.continuous_ofReal.comp_aestronglyMeasurable (hg i))
    exact (Complex.measurable_ofReal.pow_const μ).aestronglyMeasurable.mul hG.integral_prod_right'
  have hp : ∀ᵐ σ : ℝ ∂(volume.restrict (Ioo (0 : ℝ) s)),
      ‖dualF c μ b H s σ‖ₑ ≤
        2 * (ENNReal.ofReal (σ ^ μ.re) * dfA c r b σ * dfB c (r / (r - 1)) H (s - σ)) := by
    have hslice := ae_restrict_of_ae_restrict_of_subset
      (Ioo_subset_Ioi_self : Ioo (0 : ℝ) s ⊆ Ioi 0) (slice_aestronglyMeasurable hc hb)
    filter_upwards [hslice, ae_restrict_mem (measurableSet_Ioo : MeasurableSet (Ioo (0 : ℝ) s))]
      with σ hσ hσm
    have hσ0 : 0 < σ := hσm.1
    have hσs : σ < s := hσm.2
    set g : ℝ × ℝ → (Fin 2 → ℝ) := fun p => perpGrad (fun z => H (s - σ, z)) p
    have hgc : Continuous g := by
      refine continuous_pi fun i => ?_
      have h1 := perpGradH_continuousOn hH.smooth s i
      have h2 : ContinuousOn (fun p : ℝ × ℝ => (σ, p)) univ :=
        (by fun_prop : Continuous fun p : ℝ × ℝ => (σ, p)).continuousOn
      exact continuousOn_univ.1 (h1.comp h2 fun _ _ => hσs)
    have hp0 : ENNReal.ofReal r ≠ 0 := (ENNReal.ofReal_pos.2 (by linarith)).ne'
    have hpt : ENNReal.ofReal r ≠ ⊤ := ENNReal.ofReal_ne_top
    have hq : 0 < r / (r - 1) := div_pos (by linarith) (by linarith)
    have hq0 : ENNReal.ofReal (r / (r - 1)) ≠ 0 := (ENNReal.ofReal_pos.2 hq).ne'
    have hqt : ENNReal.ofReal (r / (r - 1)) ≠ ⊤ := ENNReal.ofReal_ne_top
    have hpq : r.HolderConjugate (r / (r - 1)) := Real.HolderConjugate.conjExponent hr
    have hAeq : dfA c r b σ = (∫⁻ p, ‖b (σ, p)‖ₑ ^ r ∂(Cyl.avgμ c)) ^ (1 / r) := by
      unfold dfA
      rw [eLpNorm_eq_lintegral_rpow_enorm_toReal hp0 hpt,
        ENNReal.toReal_ofReal (by linarith : (0 : ℝ) ≤ r)]
    have hBeq : dfB c (r / (r - 1)) H (s - σ) =
        (∫⁻ p, ‖g p‖ₑ ^ (r / (r - 1)) ∂(Cyl.avgμ c)) ^ (1 / (r / (r - 1))) := by
      unfold dfB
      rw [eLpNorm_eq_lintegral_rpow_enorm_toReal hq0 hqt, ENNReal.toReal_ofReal hq.le]
    have hnorm : ‖((σ : ℝ) : ℂ) ^ μ‖ₑ = ENNReal.ofReal (σ ^ μ.re) := by
      rw [← ofReal_norm, Complex.norm_cpow_eq_rpow_re_of_pos hσ0]
    unfold dualF
    rw [enorm_mul, hnorm]
    have hint : ‖∫ p, ∑ i : Fin 2, b (σ, p) i * ((perpGrad (fun z => H (s - σ, z)) p i : ℝ) : ℂ)
        ∂(Cyl.avgμ c)‖ₑ ≤ 2 * (dfA c r b σ * dfB c (r / (r - 1)) H (s - σ)) := by
      calc _ ≤ ∫⁻ p, ‖∑ i : Fin 2, b (σ, p) i *
            ((perpGrad (fun z => H (s - σ, z)) p i : ℝ) : ℂ)‖ₑ ∂(Cyl.avgμ c) :=
            enorm_integral_le_lintegral_enorm _
        _ ≤ ∫⁻ p, 2 * (‖b (σ, p)‖ₑ * ‖g p‖ₑ) ∂(Cyl.avgμ c) :=
            lintegral_mono fun p => dualF_pt_bound (b (σ, p)) (g p)
        _ = 2 * ∫⁻ p, (‖b (σ, p)‖ₑ * ‖g p‖ₑ) ∂(Cyl.avgμ c) :=
            lintegral_const_mul' _ _ (by simp)
        _ ≤ 2 * ((∫⁻ p, ‖b (σ, p)‖ₑ ^ r ∂(Cyl.avgμ c)) ^ (1 / r) *
              (∫⁻ p, ‖g p‖ₑ ^ (r / (r - 1)) ∂(Cyl.avgμ c)) ^ (1 / (r / (r - 1)))) := by
            gcongr
            exact ENNReal.lintegral_mul_le_Lp_mul_Lq (Cyl.avgμ c) hpq
              hσ.enorm hgc.measurable.enorm.aemeasurable
        _ = _ := by rw [hAeq, hBeq]
    calc ENNReal.ofReal (σ ^ μ.re) * _
        ≤ ENNReal.ofReal (σ ^ μ.re) * (2 * (dfA c r b σ * dfB c (r / (r - 1)) H (s - σ))) := by
          gcongr
      _ = _ := by ring
  rw [locallyIntegrableOn_iff isOpen_Ioo.isLocallyClosed]
  intro K hK hKc
  refine ⟨hm.mono_measure (Measure.restrict_mono hK le_rfl), ?_⟩
  have hae := ae_restrict_of_ae_restrict_of_subset hK hp
  have hfin := SigmaHolder_proof r μ.re s (dfA c r b) (dfB c (r / (r - 1)) H) hr hs
    (DualFABMeas_proof c r ν b H hc hν hr hb hH).1
    (DualFABMeas_proof c r ν b H hc hν hr hb hH).2
    (DualFAFinite_proof c r b hc hr hb)
    (DualFBFinite_proof c r ν H hc hν hr hH) K hKc hK
  unfold HasFiniteIntegral
  calc ∫⁻ σ in K, ‖dualF c μ b H s σ‖ₑ
      ≤ ∫⁻ σ in K, 2 * (ENNReal.ofReal (σ ^ μ.re) * dfA c r b σ *
          dfB c (r / (r - 1)) H (s - σ)) := lintegral_mono_ae hae
    _ = 2 * ∫⁻ σ in K, ENNReal.ofReal (σ ^ μ.re) * dfA c r b σ *
          dfB c (r / (r - 1)) H (s - σ) := lintegral_const_mul' _ _ (by simp)
    _ < ⊤ := ENNReal.mul_lt_top (by simp) hfin

lemma dualFLocInt_of_late_inHr {c r ν : ℝ} {d : CProf} {H : Coord → ℝ} {s : ℝ}
    (hc : 0 < c) (hν : 0 < ν) (hr : 1 < r) (hs : 0 < s)
    (hlate : ∀ δ : ℝ, 0 < δ → InHr c r (lateSmul δ d))
    (hH : HeatSol c ν (r / (r - 1)) H) :
    LocallyIntegrableOn (dualF c 0 d H s) (Ioo (0 : ℝ) s) volume := by
  rw [locallyIntegrableOn_iff isOpen_Ioo.isLocallyClosed]
  intro K hK hKc
  rcases K.eq_empty_or_nonempty with rfl | hne
  · exact integrableOn_empty
  · obtain ⟨m, hm, hmin⟩ := hKc.exists_isMinOn hne continuousOn_id
    have hm0 : 0 < m := (hK hm).1
    set δ : ℝ := m / 4
    have hδ : 0 < δ := by positivity
    have hloc := dualFLocInt_inHr (μ := 0) hc hν hr hs (hlate δ hδ) hH
    have hintK : IntegrableOn (dualF c 0 (lateSmul δ d) H s) K volume :=
      (locallyIntegrableOn_iff isOpen_Ioo.isLocallyClosed).1 hloc K hK hKc
    refine hintK.congr_fun (fun σ hσK => ?_) hKc.isClosed.measurableSet
    have hm_le : m ≤ σ := hmin hσK
    have hlc1 : lateCut δ σ = 1 := lateCut_eq_one hδ (by dsimp only [δ]; linarith)
    unfold dualF
    congr 1
    refine integral_congr_ae (Eventually.of_forall fun y => ?_)
    simp [lateSmul, hlc1]

lemma flatEqCellStream_late {c r ν : ℝ} {μ : ℂ} {d b : CProf}
    (hc : 0 < c) (hr : 1 < r) (hb : InHr c r b) (h0 : IsFlatResponse ν μ 0 d)
    {σ₀ σ Hh Lm : ℝ} (hσ : 0 < σ) (hσ₀ : σ₀ < σ)
    (hbd : ∀ x : Coord, σ₀ < x.1 → b x = d x)
    {ψ : Coord → ℝ} (hψ : ContDiff ℝ ∞ ψ) (hψper : ∀ x, ψ (qShift c x) = ψ x)
    (hv : ∀ x : Coord, (x.1 < σ ∨ Hh < x.1 ∨ Lm < |x.2.2|) → ψ x = 0) :
    ∫ x, ∑ i : Fin 2, b x i * flatTranspose ν μ (dtStream ψ) x i ∂(Axi.ageμ c 0) = 0 := by
  obtain ⟨θ, hθ, hθc, -, hθ1, hθk⟩ := CellPart.exists_partition_of_derivs hc
  have htest : IsPlanarSolTest (streamField (qMul θ ψ)) :=
    cellStreamPlanarTest θ ψ hθ hθc hψ ⟨σ, Hh, Lm, hσ, hv⟩
  obtain ⟨-, -, heq_d⟩ := h0.equation _ htest
  have h00 : ∫ x, cdot (0 : CProf) (streamField (qMul θ ψ)) x = 0 := by simp [cdot]
  rw [h00] at heq_d
  have htransfer : (fun x : Coord => ∑ i : Fin 2, b x i *
        flatTranspose ν μ (streamField (qMul θ ψ)) x i) =
      fun x : Coord => ∑ i : Fin 2, d x i *
        flatTranspose ν μ (streamField (qMul θ ψ)) x i := by
    funext x
    by_cases hx : σ₀ < x.1
    · rw [hbd x hx]
    · have hxσ : x.1 < σ := lt_of_le_of_lt (not_lt.1 hx) hσ₀
      set U : Set Coord := {y : Coord | y.1 < σ}
      have hUo : IsOpen U := isOpen_lt continuous_fst continuous_const
      have hvan : ∀ y ∈ U, qMul θ ψ y = 0 := fun y hy => by
        simp [qMul, hv y (Or.inl hy)]
      have hft0 : ∀ i : Fin 2, flatTranspose ν μ (streamField (qMul θ ψ)) x i = 0 :=
        fun i => flatTranspose_dtStream_zero ν μ U hUo (qMul θ ψ) hvan x hxσ i
      simp [hft0]
  have heq : ∫ x, ∑ i : Fin 2, b x i * flatTranspose ν μ (streamField (qMul θ ψ)) x i = 0 := by
    rw [htransfer]; exact heq_d
  have hP := cellStreamCoeffs c r ν μ b ψ hc hr hb hψ hψper σ Hh Lm hσ hv
  have hpiece : ∀ k : Fin 4,
      Integrable (fun x : Coord => ((iteratedDeriv (k : ℕ) θ x.2.1 : ℝ) : ℂ) * cellG ν μ b ψ k x)
          volume ∧
        ∫ x, ((iteratedDeriv (k : ℕ) θ x.2.1 : ℝ) : ℂ) * cellG ν μ b ψ k x =
          ((if (k : ℕ) = 0 then (1 : ℝ) else 0 : ℝ) : ℂ) *
            ∫ x in univ ×ˢ Cyl.cell c, cellG ν μ b ψ k x := by
    intro k
    obtain ⟨hk1, hk2, hk3⟩ := hP k
    obtain ⟨hcont, hcs⟩ := iteratedDeriv_compact hθ hθc (k : ℕ)
    by_cases hk0 : (k : ℕ) = 0
    · have hsum : ∀ q : ℝ, HasSum (fun n : ℤ => iteratedDeriv (k : ℕ) θ (q - n * c)) 1 := by
        intro q; rw [hk0, iteratedDeriv_zero]; exact hθ1 q
      obtain ⟨i1, -, i3⟩ := coordPeriodicUnfold c _ 1 _ σ Hh Lm hc hcont hcs hsum hk1 hk2 hk3
      exact ⟨i1, by rw [i3]; simp [hk0]⟩
    · obtain ⟨j, hj⟩ : ∃ j : ℕ, (k : ℕ) = j + 1 := ⟨(k : ℕ) - 1, by omega⟩
      have hsum : ∀ q : ℝ, HasSum (fun n : ℤ => iteratedDeriv (k : ℕ) θ (q - n * c)) 0 := by
        intro q; rw [hj]; exact hθk j q
      obtain ⟨i1, -, i3⟩ := coordPeriodicUnfold c _ 0 _ σ Hh Lm hc hcont hcs hsum hk1 hk2 hk3
      exact ⟨i1, by rw [i3]; simp [hk0]⟩
  have hdec : (fun x : Coord => ∑ i : Fin 2, b x i * flatTranspose ν μ (streamField (qMul θ ψ)) x i) =
      fun x => ∑ k : Fin 4, ((iteratedDeriv (k : ℕ) θ x.2.1 : ℝ) : ℂ) * cellG ν μ b ψ k x :=
    funext fun x => cellStreamCommutator ν μ b θ ψ hθ hψ x
  rw [hdec, integral_finsetSum _ (fun k _ => (hpiece k).1)] at heq
  simp only [(hpiece _).2, Fin.sum_univ_four] at heq
  have hJ : ∫ x in univ ×ˢ Cyl.cell c, cellG ν μ b ψ 0 x = 0 := by simpa using heq
  have hG0 : ∀ x : Coord, x ∈ (univ ×ˢ Cyl.cell c) \ (Ioi (0 : ℝ) ×ˢ Cyl.cell c) →
      cellG ν μ b ψ 0 x = 0 := by
    intro x hx
    have hx1 : x.1 ≤ 0 := by
      by_contra hpos; exact hx.2 ⟨not_le.1 hpos, hx.1.2⟩
    exact (hP 0).2.1 x (Or.inl (lt_of_le_of_lt hx1 hσ))
  have hmeasT : MeasurableSet (univ ×ˢ Cyl.cell c : Set Coord) :=
    MeasurableSet.univ.prod (measurableSet_Ico.prod MeasurableSet.univ)
  have hsub : (Ioi (0 : ℝ) ×ˢ Cyl.cell c : Set Coord) ⊆ univ ×ˢ Cyl.cell c :=
    fun _ hx => ⟨mem_univ _, hx.2⟩
  have hres : ∫ x in Ioi (0 : ℝ) ×ˢ Cyl.cell c, cellG ν μ b ψ 0 x = 0 := by
    rw [← setIntegral_eq_of_subset_of_forall_sdiff_eq_zero hmeasT hsub hG0]; exact hJ
  show ∫ x, cellG0 ν μ b ψ x ∂(Axi.ageμ c 0) = 0
  rw [CellPart.ageμ_zero_eq, integral_smul_measure]
  have hres' : ∫ x in Ioi (0 : ℝ) ×ˢ Cyl.cell c, cellG0 ν μ b ψ x = 0 := hres
  rw [hres', smul_zero]

lemma dualTestEq_late {c r ν : ℝ} {μ : ℂ} {d b : CProf}
    (hc : 0 < c) (hr : 1 < r) (hb : InHr c r b) (h0 : IsFlatResponse ν μ 0 d)
    {σ₀ σ Hh Lm : ℝ} (hσ : 0 < σ) (hσ₀ : σ₀ < σ)
    (hbd : ∀ x : Coord, σ₀ < x.1 → b x = d x)
    {ψ : Coord → ℂ} (hψ : ContDiff ℝ ∞ ψ) (hper : ∀ x, ψ (qShift c x) = ψ x)
    (hv : ∀ x : Coord, (x.1 < σ ∨ Hh < x.1 ∨ Lm < |x.2.2|) → ψ x = 0) :
    ∫ x, pairC b (fun y => flatTransposeC ν μ (perpC ψ) y) x ∂(Axi.ageμ c 0) = 0 := by
  set ψr : Coord → ℝ := fun z => (ψ z).re with hψr
  set ψi : Coord → ℝ := fun z => (ψ z).im with hψi
  have hψr_s : ContDiff ℝ ∞ ψr := Complex.reCLM.contDiff.comp hψ
  have hψi_s : ContDiff ℝ ∞ ψi := Complex.imCLM.contDiff.comp hψ
  have hre := flatEqCellStream_late (Hh := Hh) (Lm := Lm) hc hr hb h0 hσ hσ₀ hbd hψr_s
    (fun x => by simp [hψr, hper x]) (fun x hx => by simp [hψr, hv x hx])
  have him := flatEqCellStream_late (Hh := Hh) (Lm := Lm) hc hr hb h0 hσ hσ₀ hbd hψi_s
    (fun x => by simp [hψi, hper x]) (fun x hx => by simp [hψi, hv x hx])
  set U : Set Coord := {x | x.1 < σ ∨ Hh < x.1 ∨ Lm < |x.2.2|} with hU
  have hUo : IsOpen U :=
    (isOpen_lt continuous_fst continuous_const).union
      ((isOpen_lt continuous_const continuous_fst).union
        (isOpen_lt continuous_const (continuous_abs.comp (continuous_snd.comp continuous_snd))))
  have hvr : ∀ y ∈ U, ψr y = 0 := fun y hy => by simp [hψr, hv y hy]
  have hvi : ∀ y ∈ U, ψi y = 0 := fun y hy => by simp [hψi, hv y hy]
  have hbox : ∀ x, x ∉ dtBox σ Hh Lm → x ∈ U := by
    intro x hx
    by_contra hxU
    apply hx
    simp only [hU, mem_ofPred_eq, not_or, not_lt] at hxU
    exact ⟨⟨hxU.1, hxU.2.1⟩, trivial, abs_le.1 hxU.2.2⟩
  have hIA := integrable_pair_of_box hc hr hb σ Hh Lm hσ
    (fun x i => flatTranspose ν μ (dtStream ψr) x i)
    (flatTranspose_dtStream_continuous ν μ ψr hψr_s)
    (fun x hx i => flatTranspose_dtStream_zero ν μ U hUo ψr hvr x (hbox x hx) i)
  have hIB := integrable_pair_of_box hc hr hb σ Hh Lm hσ
    (fun x i => flatTranspose ν μ (dtStream ψi) x i)
    (flatTranspose_dtStream_continuous ν μ ψi hψi_s)
    (fun x hx i => flatTranspose_dtStream_zero ν μ U hUo ψi hvi x (hbox x hx) i)
  have hpt : ∀ x, pairC b (fun y => flatTransposeC ν μ (perpC ψ) y) x =
      (∑ i : Fin 2, b x i * flatTranspose ν μ (dtStream ψr) x i) +
        Complex.I * ∑ i : Fin 2, b x i * flatTranspose ν μ (dtStream ψi) x i := by
    intro x
    unfold pairC
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    beta_reduce
    rw [flatTransposeC_perpC_split ν μ ψ hψ x i]
    ring
  simp_rw [hpt]
  rw [integral_add hIA (hIB.const_mul Complex.I), integral_const_mul, hre, him]
  simp

lemma dualRemainderLimit_inHr {c r ν : ℝ} {μ : ℂ} {b : CProf} {H : Coord → ℝ} {s : ℝ}
    {χ φ : ℝ → ℝ} (hc : 0 < c) (hν : 0 < ν) (hr : 1 < r) (hs : 0 < s)
    (hb : InHr c r b) (hH : HeatSol c ν (r / (r - 1)) H) (hχ : DFChi s χ) (hφ : DFPhi φ) :
    (∀ L : ℝ, 0 < L →
      Integrable (fun x => pairC b (dualRem ν μ χ φ H s L) x) (Axi.ageμ c 0)) ∧
    Tendsto (fun L : ℝ => ∫ x, pairC b (dualRem ν μ χ φ H s L) x ∂(Axi.ageμ c 0)) atTop (𝓝 0) := by
  obtain ⟨C, _hC0, hC⟩ := dualRemPointwise c ν μ H s (r / (r - 1)) χ φ hc hν hs hH hχ hφ
  have hI := dualGWeightedInt c r ν b H s χ hc hν hr hs hb hH hχ
  set K : ℝ → ℝ := fun L => L⁻¹ + L⁻¹ ^ 2 + L⁻¹ ^ 3 with hK
  have hpt : ∀ L : ℝ, 0 < L → ∀ x : Coord,
      ‖pairC b (dualRem ν μ χ φ H s L) x‖ ≤ (2 * C * K L) * (‖b x‖ * dualG χ H s x) := by
    intro L _hL x
    unfold pairC
    refine (norm_sum_le _ _).trans ?_
    have hterm : ∀ i : Fin 2, ‖b x i * dualRem ν μ χ φ H s L x i‖ ≤
        (C * K L) * (‖b x‖ * dualG χ H s x) := by
      intro i
      rw [norm_mul]
      calc ‖b x i‖ * ‖dualRem ν μ χ φ H s L x i‖
          ≤ ‖b x‖ * (C * K L * dualG χ H s x) :=
            mul_le_mul (PiLp.norm_apply_le (b x) i) (hC L _hL x i) (norm_nonneg _) (norm_nonneg _)
        _ = (C * K L) * (‖b x‖ * dualG χ H s x) := by ring
    calc ∑ i : Fin 2, ‖b x i * dualRem ν μ χ φ H s L x i‖
        ≤ ∑ _i : Fin 2, (C * K L) * (‖b x‖ * dualG χ H s x) :=
          Finset.sum_le_sum fun i _ => hterm i
      _ = (2 * C * K L) * (‖b x‖ * dualG χ H s x) := by simp [Finset.sum_const]; ring
  have hint : ∀ L : ℝ, 0 < L →
      Integrable (fun x => pairC b (dualRem ν μ χ φ H s L) x) (Axi.ageμ c 0) := fun L hL =>
    Integrable.mono' (hI.const_mul (2 * C * K L))
      (dualRemMeasurable c r ν μ b H s χ φ L hc hν hs hr hb hH hχ hφ).1
      (Eventually.of_forall (hpt L hL))
  refine ⟨hint, ?_⟩
  set I : ℝ := ∫ x, ‖b x‖ * dualG χ H s x ∂(Axi.ageμ c 0) with hIdef
  have hKlim : Tendsto K atTop (𝓝 0) := by
    have h1' : Tendsto (fun L : ℝ => L⁻¹) atTop (𝓝 0) := tendsto_inv_atTop_zero
    simpa [hK] using (h1'.add (h1'.pow 2)).add (h1'.pow 3)
  have hbound : ∀ᶠ L in atTop, ‖∫ x, pairC b (dualRem ν μ χ φ H s L) x ∂(Axi.ageμ c 0)‖ ≤
      (2 * C * I) * K L := by
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with L hL
    calc ‖∫ x, pairC b (dualRem ν μ χ φ H s L) x ∂(Axi.ageμ c 0)‖
        ≤ ∫ x, (2 * C * K L) * (‖b x‖ * dualG χ H s x) ∂(Axi.ageμ c 0) :=
          norm_integral_le_of_norm_le (hI.const_mul _) (Eventually.of_forall (hpt L hL))
      _ = (2 * C * I) * K L := by rw [integral_const_mul, hIdef]; ring
  exact squeeze_zero_norm' hbound (by simpa using hKlim.const_mul (2 * C * I))

lemma dualMainLimit_inHr {c r ν : ℝ} {μ : ℂ} {b : CProf} {H : Coord → ℝ} {s : ℝ}
    {χ φ : ℝ → ℝ} (hc : 0 < c) (hν : 0 < ν) (hr : 1 < r) (hs : 0 < s)
    (hb : InHr c r b) (hH : HeatSol c ν (r / (r - 1)) H) (hχ : DFChi s χ) (hφ : DFPhi φ) :
    (∀ L : ℝ, 0 < L →
      Integrable (fun x => pairC b (dualMain μ χ φ H s L) x) (Axi.ageμ c 0)) ∧
    Tendsto (fun L : ℝ => ∫ x, pairC b (dualMain μ χ φ H s L) x ∂(Axi.ageμ c 0)) atTop
      (𝓝 (-∫ σ in Ioo (0 : ℝ) s, ((deriv χ σ : ℝ) : ℂ) * dualF c μ b H s σ)) := by
  have hG := dualMainInfIntegrable_proof dualPerpBridge_proof c r ν μ b H s χ hc hν hr hs hb hH hχ
  have hφc : Continuous φ := hφ.1.continuous
  have hint : ∀ L : ℝ, Integrable (fun x => pairC b (dualMain μ χ φ H s L) x) (Axi.ageμ c 0) := by
    intro L
    have hm : Continuous fun x : Coord => (φ (x.2.2 / L) : ℂ) :=
      Complex.continuous_ofReal.comp (hφc.comp ((continuous_snd.comp continuous_snd).div_const L))
    have hb' : ∀ x, ‖pairC b (dualMain μ χ φ H s L) x‖ ≤
        ‖pairC b (dualMain μ χ (fun _ => (1 : ℝ)) H s 1) x‖ := by
      intro x
      rw [pairC_dualMain, norm_mul, Complex.norm_real]
      exact mul_le_of_le_one_left (norm_nonneg _) (by simpa [Real.norm_eq_abs] using hφ.2.2.2 _)
    refine Integrable.mono hG.norm ?_
      (Eventually.of_forall fun x => (hb' x).trans_eq (norm_norm _).symm)
    exact (hm.aestronglyMeasurable.mul hG.aestronglyMeasurable).congr
      (Eventually.of_forall fun x => (pairC_dualMain μ χ φ H s L b x).symm)
  refine ⟨fun L _ => hint L, ?_⟩
  rw [← dualMainFubini_proof dualPerpBridge_proof c r ν μ b H s χ hc hν hr hs hb hH hχ hG]
  refine tendsto_integral_filter_of_dominated_convergence
    (fun x => ‖pairC b (dualMain μ χ (fun _ => (1 : ℝ)) H s 1) x‖)
    (Eventually.of_forall fun L => (hint L).aestronglyMeasurable)
    (Eventually.of_forall fun L => Eventually.of_forall fun x => ?_) hG.norm
    (Eventually.of_forall fun x => ?_)
  · rw [pairC_dualMain, norm_mul, Complex.norm_real]
    exact mul_le_of_le_one_left (norm_nonneg _) (by simpa [Real.norm_eq_abs] using hφ.2.2.2 _)
  · have h0 : Tendsto (fun L : ℝ => x.2.2 / L) atTop (𝓝 0) :=
      tendsto_const_nhds.div_atTop tendsto_id
    have ht : Tendsto (fun L : ℝ => (φ (x.2.2 / L) : ℂ)) atTop (𝓝 ((φ 0 : ℝ) : ℂ)) :=
      (Complex.continuous_ofReal.tendsto _).comp ((hφc.tendsto 0).comp h0)
    rw [hφ.2.2.1] at ht
    have h2 := ht.mul_const (pairC b (dualMain μ χ (fun _ => (1 : ℝ)) H s 1) x)
    rw [Complex.ofReal_one, one_mul] at h2
    exact h2.congr fun L => (pairC_dualMain μ χ φ H s L b x).symm

/-- `duBoisReymond` constancy of `slicePair c d H · s` on `Ioo 0 s` when `IsFlatResponse ν 0 0 d`
and `lateSmul δ d ∈ InHr c r` for every `δ > 0`. -/
lemma dualConstancy_of_late_inHr {c r ν : ℝ} {d : CProf} {H : Coord → ℝ} {s : ℝ}
    (hc : 0 < c) (hν : 0 < ν) (hr : 1 < r) (hs : 0 < s)
    (hlate : ∀ δ : ℝ, 0 < δ → InHr c r (lateSmul δ d))
    (h0 : IsFlatResponse ν 0 0 d)
    (hH : HeatSol c ν (r / (r - 1)) H) :
    ∃ κ : ℂ, ∀ᵐ σ : ℝ ∂(volume.restrict (Ioo (0 : ℝ) s)), slicePair c d H σ s = κ := by
  have hloc := dualFLocInt_of_late_inHr hc hν hr hs hlate hH
  have htest_zero : ∀ χ : ℝ → ℝ, ContDiff ℝ ∞ χ → HasCompactSupport χ →
      tsupport χ ⊆ Ioo (0 : ℝ) s →
      ∫ σ in Ioo (0 : ℝ) s, ((deriv χ σ : ℝ) : ℂ) * dualF c 0 d H s σ = 0 := by
    intro χ hχ hχc hχs
    rcases (tsupport χ).eq_empty_or_nonempty with hE | hne
    · have hχ0 : χ = 0 := funext fun t =>
        image_eq_zero_of_notMem_tsupport (by simp [hE])
      simp [hχ0]
    · obtain ⟨m, hm, hmin⟩ := hχc.isCompact.exists_isMinOn hne continuousOn_id
      obtain ⟨M, _hM, hmax⟩ := hχc.isCompact.exists_isMaxOn hne continuousOn_id
      have hm0 : 0 < m := (hχs hm).1
      set δ : ℝ := m / 4
      set σ₀ : ℝ := 3 * m / 4
      have hδ : 0 < δ := by positivity
      have hσ₀ : σ₀ < m := by dsimp only [σ₀]; linarith
      let b : CProf := lateSmul δ d
      have hb : InHr c r b := hlate δ hδ
      have hbd : ∀ x : Coord, σ₀ < x.1 → b x = d x := by
        intro x hx
        have hlc1 : lateCut δ x.1 = 1 := lateCut_eq_one hδ (by dsimp only [δ, σ₀] at *; linarith)
        simp [b, lateSmul, hlc1]
      have hχ' : DFChi s χ := ⟨hχ, hχc, hχs⟩
      obtain ⟨φ, hφ⟩ := exists_dfPhi
      obtain ⟨R, hR⟩ := hφ.2.1.isCompact.isBounded.subset_closedBall 0
      have hRφ : ∀ t : ℝ, R < |t| → φ t = 0 := by
        intro t ht
        apply image_eq_zero_of_notMem_tsupport
        intro hmem
        have h1 := hR hmem
        rw [Metric.mem_closedBall, dist_zero_right, Real.norm_eq_abs] at h1
        linarith
      obtain ⟨hRi, hRt⟩ := dualRemainderLimit_inHr (μ := 0) hc hν hr hs hb hH hχ' hφ
      obtain ⟨hMi, hMt⟩ := dualMainLimit_inHr (μ := 0) hc hν hr hs hb hH hχ' hφ
      have key : ∀ L : ℝ, 0 < L →
          ∫ x, pairC b (dualMain 0 χ φ H s L) x ∂(Axi.ageμ c 0) =
            -∫ x, pairC b (dualRem ν 0 χ φ H s L) x ∂(Axi.ageμ c 0) := by
        intro L hL
        obtain ⟨hs1, hs2, _⟩ := DualTestAdmissible_proof c ν 0 H s _ χ φ L hc hν hs hH hχ' hφ hL
        have hv_m : ∀ x : Coord, (x.1 < m ∨ M < x.1 ∨ R * L < |x.2.2|) →
            dualPsi 0 χ φ H s L x = 0 := by
          intro x hx
          rcases hx with h | h | h
          · exact dualPsi_eq_zero_of_chi 0 χ φ H s L x
              (image_eq_zero_of_notMem_tsupport fun hy => absurd (hmin hy) (not_le.2 h))
          · exact dualPsi_eq_zero_of_chi 0 χ φ H s L x
              (image_eq_zero_of_notMem_tsupport fun hy => absurd (hmax hy) (not_le.2 h))
          · apply dualPsi_eq_zero_of_phi
            apply hRφ
            rw [abs_div, abs_of_pos hL]
            exact (lt_div_iff₀ hL).2 (by linarith)
        have h0_eq := dualTestEq_late (Hh := M) (Lm := R * L) hc hr hb h0 hm0 hσ₀ hbd hs1 hs2 hv_m
        have hsplit : ∀ x,
            pairC b (fun y => flatTransposeC ν 0 (perpC (dualPsi 0 χ φ H s L)) y) x =
              pairC b (dualMain 0 χ φ H s L) x + pairC b (dualRem ν 0 χ φ H s L) x := by
          intro x
          unfold pairC
          rw [← Finset.sum_add_distrib]
          refine Finset.sum_congr rfl fun i _ => ?_
          have hh := DualHeatIdentity_proof c ν 0 H s _ χ hc hν hs hH hχ' x i
          simp only [dualMain, dualRem]
          rw [← hh]; ring
        simp_rw [hsplit] at h0_eq
        rw [integral_add (hMi L hL) (hRi L hL)] at h0_eq
        exact eq_neg_of_add_eq_zero_left h0_eq
      have hlim : Tendsto (fun L : ℝ => ∫ x, pairC b (dualMain 0 χ φ H s L) x ∂(Axi.ageμ c 0))
          atTop (𝓝 (-0)) := by
        refine hRt.neg.congr' ?_
        filter_upwards [eventually_gt_atTop (0 : ℝ)] with L hL using (key L hL).symm
      have hIb : ∫ σ in Ioo (0 : ℝ) s, ((deriv χ σ : ℝ) : ℂ) * dualF c 0 b H s σ = 0 := by
        simpa using tendsto_nhds_unique hMt hlim
      have heq_int : (fun σ : ℝ => ((deriv χ σ : ℝ) : ℂ) * dualF c 0 d H s σ) =
          fun σ : ℝ => ((deriv χ σ : ℝ) : ℂ) * dualF c 0 b H s σ := by
        funext σ
        by_cases hd0 : deriv χ σ = 0
        · simp [hd0]
        · have hmem : σ ∈ tsupport χ := by
            by_contra hnot
            have hev := notMem_tsupport_iff_eventuallyEq.1 hnot
            rw [hev.deriv_eq] at hd0
            simp at hd0
          have hm_le : m ≤ σ := hmin hmem
          have hlc1 : lateCut δ σ = 1 := lateCut_eq_one hδ (by dsimp only [δ] at *; linarith)
          congr 1
          unfold dualF
          congr 1
          refine integral_congr_ae (Eventually.of_forall fun y => ?_)
          simp [b, lateSmul, hlc1]
      rw [heq_int, hIb]
  obtain ⟨κ, hκ⟩ := duBoisReymond_proof s (dualF c 0 d H s) hs hloc htest_zero
  refine ⟨κ, ?_⟩
  filter_upwards [hκ] with σ hσ
  simpa [dualF, slicePair] using hσ

/-! ### Slice curl integration by parts on `B0579.cell c` -/

lemma slicePair_curl_bound {c : ℝ} (hc : 0 < c)
    {w wq wη w₁ wq₁ wη₁ : CProf} {H : Coord → ℝ} {ζ : ℝ × ℝ → ℝ} {s σ : ℝ}
    (hH_sm : ContDiffOn ℝ ∞ H (Ioi (0 : ℝ) ×ˢ (univ : Set (ℝ × ℝ))))
    (hH_per : ∀ x : Coord, 0 < x.1 → H (qShift c x) = H x)
    (hσs : σ < s)
    (hw_ae : ∀ᵐ y : B0579.Plane, w₁ (σ, y) = w (σ, y))
    (hwq_ae : ∀ᵐ y : B0579.Plane, wq₁ (σ, y) = wq (σ, y))
    (hwη_ae : ∀ᵐ y : B0579.Plane, wη₁ (σ, y) = wη (σ, y))
    (hmem_w : MemLp (fun y => w₁ (σ, y)) 2 (volume.restrict (B0579.cell c)))
    (hmem_wq : MemLp (fun y => wq₁ (σ, y)) 2 (volume.restrict (B0579.cell c)))
    (hmem_wη : MemLp (fun y => wη₁ (σ, y)) 2 (volume.restrict (B0579.cell c)))
    (hcd0 : ∀ i : Fin 2, IIIa.HasWeakCellDerivC c 0 (fun y => w₁ (σ, y) i) (fun y => wq₁ (σ, y) i))
    (hcd1 : ∀ i : Fin 2, IIIa.HasWeakCellDerivC c 1 (fun y => w₁ (σ, y) i) (fun y => wη₁ (σ, y) i))
    (hH_L2 : eLpNorm (fun y => (H (s - σ, y) : ℂ)) 2 (volume.restrict (B0579.cell c)) ≤
      eLpNorm (fun y => (ζ y : ℂ)) 2 (volume.restrict (B0579.cell c)))
    (hζ_fin : eLpNorm (fun y => (ζ y : ℂ)) 2 (volume.restrict (B0579.cell c)) < ⊤)
    (hperp_L2 : ∀ i : Fin 2,
      MemLp (fun y => (perpGrad (fun z => H (s - σ, z)) y i : ℂ)) 2
        (volume.restrict (B0579.cell c))) :
    Integrable (fun y : B0579.Plane =>
        ∑ i : Fin 2, w (σ, y) i * ((perpGrad (fun z => H (s - σ, z)) y i : ℝ) : ℂ))
      (Cyl.avgμ c) ∧
    ‖slicePair c w H σ s‖ ≤
      c⁻¹ * (eLpNorm (fun y => profCurl wq wη (σ, y)) 2 (B0579.cellMeasure c 0) *
        eLpNorm (fun y => (ζ y : ℂ)) 2 (volume.restrict (B0579.cell c))).toReal := by
  set τ : ℝ := s - σ
  have hτ : 0 < τ := sub_pos.2 hσs
  let g : B0579.Plane → ℝ := fun y => H (τ, y)
  have hg_cd : ContDiff ℝ ∞ g := by
    rw [contDiff_iff_contDiffAt]
    intro y
    exact (hH_sm.contDiffAt ((isOpen_Ioi.prod isOpen_univ).mem_nhds
      (show (τ, y) ∈ Ioi (0 : ℝ) ×ˢ univ from ⟨hτ, mem_univ y⟩))).comp y
        (contDiff_const.prodMk contDiff_id).contDiffAt
  have hg_per : ∀ y : B0579.Plane, g (y.1 + c, y.2) = g y :=
    fun y => hH_per (τ, y) hτ
  have hg_mem2 : MemLp (fun y => (g y : ℂ)) 2 (volume.restrict (B0579.cell c)) :=
    ⟨(Complex.continuous_ofReal.comp hg_cd.continuous).aestronglyMeasurable,
      lt_of_le_of_lt hH_L2 hζ_fin⟩
  have hw_i : ∀ i : Fin 2, MemLp (fun y => w₁ (σ, y) i) 2 (volume.restrict (B0579.cell c)) :=
    fun i => ⟨(EuclideanSpace.proj i : CMerid →L[ℂ] ℂ).continuous.comp_aestronglyMeasurable
      hmem_w.1, lt_of_le_of_lt
        (eLpNorm_mono fun y => PiLp.norm_apply_le (w₁ (σ, y)) i) hmem_w.2⟩
  have hwq_1 : MemLp (fun y => wq₁ (σ, y) 1) 2 (volume.restrict (B0579.cell c)) :=
    ⟨(EuclideanSpace.proj 1 : CMerid →L[ℂ] ℂ).continuous.comp_aestronglyMeasurable hmem_wq.1,
      lt_of_le_of_lt (eLpNorm_mono fun y => PiLp.norm_apply_le (wq₁ (σ, y)) 1) hmem_wq.2⟩
  have hwη_0 : MemLp (fun y => wη₁ (σ, y) 0) 2 (volume.restrict (B0579.cell c)) :=
    ⟨(EuclideanSpace.proj 0 : CMerid →L[ℂ] ℂ).continuous.comp_aestronglyMeasurable hmem_wη.1,
      lt_of_le_of_lt (eLpNorm_mono fun y => PiLp.norm_apply_le (wη₁ (σ, y)) 0) hmem_wη.2⟩
  have hcurl_mem2 : MemLp (fun y => profCurl wq₁ wη₁ (σ, y)) 2 (volume.restrict (B0579.cell c)) :=
    hwq_1.sub hwη_0
  have hint_pair1 : ∀ i : Fin 2, IntegrableOn
      (fun y => w₁ (σ, y) i * (perpGrad g y i : ℂ)) (B0579.cell c) :=
    fun i => (hw_i i).integrable_mul (hperp_L2 i)
  have hint_wg : IntegrableOn (fun y => w₁ (σ, y) 0 * (g y : ℂ)) (B0579.cell c) :=
    (hw_i 0).integrable_mul hg_mem2
  have hint_cg : IntegrableOn (fun y => profCurl wq₁ wη₁ (σ, y) * (g y : ℂ)) (B0579.cell c) :=
    hcurl_mem2.integrable_mul hg_mem2
  obtain ⟨φ, hφ⟩ := exists_dfPhi
  obtain ⟨R, hR⟩ := hφ.2.1.isCompact.isBounded.subset_closedBall 0
  have hRφ : ∀ t : ℝ, R < |t| → φ t = 0 := by
    intro t ht
    apply image_eq_zero_of_notMem_tsupport
    intro hmem
    have h1 := hR hmem
    rw [Metric.mem_closedBall, dist_zero_right, Real.norm_eq_abs] at h1
    linarith
  have hdφ_cs : HasCompactSupport (deriv φ) := hφ.2.1.deriv
  have hdφ_cont : Continuous (deriv φ) :=
    (contDiff_infty.1 hφ.1 1).continuous_deriv le_rfl
  obtain ⟨M_φ, hMφ⟩ := hdφ_cs.exists_bound_of_continuous hdφ_cont
  have hMφ_nn : 0 ≤ M_φ := (norm_nonneg (deriv φ 0)).trans (hMφ 0)
  have hibp_L : ∀ L : ℝ, 0 < L →
      (∫ y in B0579.cell c, (φ (y.2 / L) : ℂ) *
          ∑ i : Fin 2, w₁ (σ, y) i * (perpGrad g y i : ℂ)) +
        ((L⁻¹ : ℝ) : ℂ) *
          ∫ y in B0579.cell c, ((deriv φ (y.2 / L) : ℝ) : ℂ) * (w₁ (σ, y) 0 * (g y : ℂ)) =
      ∫ y in B0579.cell c, (φ (y.2 / L) : ℂ) * (profCurl wq₁ wη₁ (σ, y) * (g y : ℂ)) := by
    intro L hL
    let φL : B0579.Plane → ℝ := fun y => φ (y.2 / L)
    let ψL : B0579.Plane → ℝ := fun y => φL y * g y
    have hφL_cd : ContDiff ℝ ∞ φL := hφ.1.comp (contDiff_snd.div_const L)
    have hψL_test : B0579.IsCylTest c ψL :=
      { smooth := hφL_cd.mul hg_cd
        periodic := fun y => by simp [ψL, φL, hg_per y]
        band := ⟨R * L, fun y hy => by
          have ht : R < |y.2 / L| := by
            rw [abs_div, abs_of_pos hL]
            exact (lt_div_iff₀ hL).2 (by linarith)
          simp [ψL, φL, hRφ _ ht]⟩ }
    have hpd0_φL : ∀ y : B0579.Plane, B0579.pd 0 φL y = 0 := by
      intro y
      have hl : HasDerivAt (fun q' : ℝ => ((q', y.2) : ℝ × ℝ)) ((1 : ℝ), (0 : ℝ)) y.1 :=
        (hasDerivAt_id y.1).prodMk (hasDerivAt_const y.1 y.2)
      have h1 : HasDerivAt (fun q' : ℝ => φL (q', y.2)) (B0579.pd 0 φL y) y.1 := by
        have h := ((hφL_cd.differentiable (by simp)) (y.1, y.2)).hasFDerivAt.comp_hasDerivAt y.1 hl
        have e : B0579.pd 0 φL y = fderiv ℝ φL (y.1, y.2) ((1 : ℝ), (0 : ℝ)) := by
          unfold B0579.pd; simp [B0579.dir]
        rw [e]; exact h
      exact h1.unique (hasDerivAt_const y.1 (φ (y.2 / L)))
    have hpd1_φL : ∀ y : B0579.Plane, B0579.pd 1 φL y = L⁻¹ * deriv φ (y.2 / L) := by
      intro y
      have hl : HasDerivAt (fun η' : ℝ => ((y.1, η') : ℝ × ℝ)) ((0 : ℝ), (1 : ℝ)) y.2 :=
        (hasDerivAt_const y.2 y.1).prodMk (hasDerivAt_id y.2)
      have h1 : HasDerivAt (fun η' : ℝ => φL (y.1, η')) (B0579.pd 1 φL y) y.2 := by
        have h := ((hφL_cd.differentiable (by simp)) (y.1, y.2)).hasFDerivAt.comp_hasDerivAt y.2 hl
        have e : B0579.pd 1 φL y = fderiv ℝ φL (y.1, y.2) ((0 : ℝ), (1 : ℝ)) := by
          unfold B0579.pd; simp [B0579.dir]
        rw [e]; exact h
      have h2 : HasDerivAt (fun η' : ℝ => φ (η' / L)) (deriv φ (y.2 / L) * (1 / L)) y.2 :=
        (((hφ.1.differentiable (by simp)) (y.2 / L)).hasDerivAt).comp y.2
          ((hasDerivAt_id y.2).div_const L)
      rw [h1.unique h2]
      ring
    have hpd0_ψL : ∀ y : B0579.Plane, B0579.pd 0 ψL y = -(φ (y.2 / L) * perpGrad g y 1) := by
      intro y
      rw [show ψL = fun z => φL z * g z from rfl,
        B0579.pd_mul (hφL_cd.differentiable (by simp)) (hg_cd.differentiable (by simp)) 0 y,
        hpd0_φL y]
      simp [φL, perpGrad, B0579.pd, B0579.dir]
    have hpd1_ψL : ∀ y : B0579.Plane,
        B0579.pd 1 ψL y = L⁻¹ * deriv φ (y.2 / L) * g y + φ (y.2 / L) * perpGrad g y 0 := by
      intro y
      rw [show ψL = fun z => φL z * g z from rfl,
        B0579.pd_mul (hφL_cd.differentiable (by simp)) (hg_cd.differentiable (by simp)) 1 y,
        hpd1_φL y]
      simp [φL, perpGrad, B0579.pd, B0579.dir]
    have e1 := (hcd1 0).2 ψL hψL_test
    have e0 := (hcd0 1).2 ψL hψL_test
    have hI_p0 : IntegrableOn
        (fun y => (φ (y.2 / L) : ℂ) * (w₁ (σ, y) 0 * (perpGrad g y 0 : ℂ))) (B0579.cell c) := by
      refine (hint_pair1 0).norm.mono'
        (((Complex.continuous_ofReal.comp hφL_cd.continuous).aestronglyMeasurable).mul
          (hint_pair1 0).aestronglyMeasurable)
        (Eventually.of_forall fun y => ?_)
      rw [norm_mul, Complex.norm_real]
      exact mul_le_of_le_one_left (norm_nonneg _) (by simpa [Real.norm_eq_abs] using hφ.2.2.2 _)
    have hI_p1 : IntegrableOn
        (fun y => (φ (y.2 / L) : ℂ) * (w₁ (σ, y) 1 * (perpGrad g y 1 : ℂ))) (B0579.cell c) := by
      refine (hint_pair1 1).norm.mono'
        (((Complex.continuous_ofReal.comp hφL_cd.continuous).aestronglyMeasurable).mul
          (hint_pair1 1).aestronglyMeasurable)
        (Eventually.of_forall fun y => ?_)
      rw [norm_mul, Complex.norm_real]
      exact mul_le_of_le_one_left (norm_nonneg _) (by simpa [Real.norm_eq_abs] using hφ.2.2.2 _)
    have hI_dφ : IntegrableOn
        (fun y => ((deriv φ (y.2 / L) : ℝ) : ℂ) * (w₁ (σ, y) 0 * (g y : ℂ))) (B0579.cell c) := by
      refine (hint_wg.norm.const_mul M_φ).mono'
        (((Complex.continuous_ofReal.comp
          (hdφ_cont.comp (continuous_snd.div_const L))).aestronglyMeasurable).mul
            hint_wg.aestronglyMeasurable)
        (Eventually.of_forall fun y => ?_)
      rw [norm_mul, Complex.norm_real]
      exact mul_le_mul_of_nonneg_right (hMφ _) (norm_nonneg _)
    have he1_lhs : (fun y => w₁ (σ, y) 0 * (B0579.pd 1 ψL y : ℂ)) =
        fun y => (φ (y.2 / L) : ℂ) * (w₁ (σ, y) 0 * (perpGrad g y 0 : ℂ)) +
          ((L⁻¹ : ℝ) : ℂ) * (((deriv φ (y.2 / L) : ℝ) : ℂ) * (w₁ (σ, y) 0 * (g y : ℂ))) := by
      funext y; rw [hpd1_ψL y]; push_cast; ring
    have he0_lhs : (fun y => w₁ (σ, y) 1 * (B0579.pd 0 ψL y : ℂ)) =
        fun y => -((φ (y.2 / L) : ℂ) * (w₁ (σ, y) 1 * (perpGrad g y 1 : ℂ))) := by
      funext y; rw [hpd0_ψL y]; push_cast; ring
    rw [he1_lhs, integral_add hI_p0 (hI_dφ.const_mul _), integral_const_mul] at e1
    rw [he0_lhs, integral_neg] at e0
    have hI_q1 := ((hcd0 1).1 ψL hψL_test).2
    have hI_η0 := ((hcd1 0).1 ψL hψL_test).2
    have hrhs_sub : (∫ y in B0579.cell c, wq₁ (σ, y) 1 * (ψL y : ℂ)) -
        (∫ y in B0579.cell c, wη₁ (σ, y) 0 * (ψL y : ℂ)) =
        ∫ y in B0579.cell c, (φ (y.2 / L) : ℂ) * (profCurl wq₁ wη₁ (σ, y) * (g y : ℂ)) := by
      rw [← integral_sub hI_q1 hI_η0]
      refine integral_congr_ae (Eventually.of_forall fun y => ?_)
      simp only [ψL, φL, profCurl, Complex.ofReal_mul]
      ring
    have hlhs_add : (∫ y in B0579.cell c,
          (φ (y.2 / L) : ℂ) * (w₁ (σ, y) 0 * (perpGrad g y 0 : ℂ))) +
        (∫ y in B0579.cell c,
          (φ (y.2 / L) : ℂ) * (w₁ (σ, y) 1 * (perpGrad g y 1 : ℂ))) =
        ∫ y in B0579.cell c, (φ (y.2 / L) : ℂ) *
          ∑ i : Fin 2, w₁ (σ, y) i * (perpGrad g y i : ℂ) := by
      rw [← integral_add hI_p0 hI_p1]
      refine integral_congr_ae (Eventually.of_forall fun y => ?_)
      simp [Fin.sum_univ_two]; ring
    linear_combination e1 - e0 + hrhs_sub - hlhs_add
  have hφ_lim : ∀ (F : B0579.Plane → ℂ), IntegrableOn F (B0579.cell c) →
      Tendsto (fun L : ℝ => ∫ y in B0579.cell c, (φ (y.2 / L) : ℂ) * F y)
        atTop (𝓝 (∫ y in B0579.cell c, F y)) := by
    intro F hF
    refine tendsto_integral_filter_of_dominated_convergence (fun y => ‖F y‖)
      (Eventually.of_forall fun L => ?_)
      (Eventually.of_forall fun L => Eventually.of_forall fun y => ?_)
      hF.norm (Eventually.of_forall fun y => ?_)
    · exact ((Complex.continuous_ofReal.comp
        (hφ.1.continuous.comp (continuous_snd.div_const L))).aestronglyMeasurable).mul
          hF.aestronglyMeasurable
    · rw [norm_mul, Complex.norm_real]
      exact mul_le_of_le_one_left (norm_nonneg _) (by simpa [Real.norm_eq_abs] using hφ.2.2.2 _)
    · have h0 : Tendsto (fun L : ℝ => y.2 / L) atTop (𝓝 0) :=
        tendsto_const_nhds.div_atTop tendsto_id
      have ht : Tendsto (fun L : ℝ => (φ (y.2 / L) : ℂ)) atTop (𝓝 ((φ 0 : ℝ) : ℂ)) :=
        (Complex.continuous_ofReal.tendsto _).comp ((hφ.1.continuous.tendsto 0).comp h0)
      rw [hφ.2.2.1, Complex.ofReal_one] at ht
      simpa using ht.mul_const (F y)
  have hint_sum1 : IntegrableOn
      (fun y => ∑ i : Fin 2, w₁ (σ, y) i * (perpGrad g y i : ℂ)) (B0579.cell c) := by
    have heq : (fun y => ∑ i : Fin 2, w₁ (σ, y) i * (perpGrad g y i : ℂ)) =
        fun y => w₁ (σ, y) 0 * (perpGrad g y 0 : ℂ) + w₁ (σ, y) 1 * (perpGrad g y 1 : ℂ) := by
      funext y; simp [Fin.sum_univ_two]
    rw [heq]
    exact (hint_pair1 0).add (hint_pair1 1)
  have hrem_lim : Tendsto (fun L : ℝ =>
      ((L⁻¹ : ℝ) : ℂ) *
        ∫ y in B0579.cell c, ((deriv φ (y.2 / L) : ℝ) : ℂ) * (w₁ (σ, y) 0 * (g y : ℂ)))
      atTop (𝓝 0) := by
    set J : ℝ := ∫ y in B0579.cell c, M_φ * ‖w₁ (σ, y) 0 * (g y : ℂ)‖
    have hbd : ∀ᶠ L : ℝ in atTop,
        ‖((L⁻¹ : ℝ) : ℂ) * ∫ y in B0579.cell c,
          ((deriv φ (y.2 / L) : ℝ) : ℂ) * (w₁ (σ, y) 0 * (g y : ℂ))‖ ≤ L⁻¹ * J := by
      filter_upwards [eventually_gt_atTop (0 : ℝ)] with L hL
      rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (inv_nonneg.2 hL.le)]
      refine mul_le_mul_of_nonneg_left ?_ (inv_nonneg.2 hL.le)
      refine norm_integral_le_of_norm_le (hint_wg.norm.const_mul M_φ)
        (Eventually.of_forall fun y => ?_)
      rw [norm_mul, Complex.norm_real]
      exact mul_le_mul_of_nonneg_right (hMφ _) (norm_nonneg _)
    exact squeeze_zero_norm' hbd (by simpa using tendsto_inv_atTop_zero.mul_const J)
  have hLHS_lim : Tendsto (fun L : ℝ =>
      (∫ y in B0579.cell c, (φ (y.2 / L) : ℂ) *
          ∑ i : Fin 2, w₁ (σ, y) i * (perpGrad g y i : ℂ)) +
        ((L⁻¹ : ℝ) : ℂ) *
          ∫ y in B0579.cell c, ((deriv φ (y.2 / L) : ℝ) : ℂ) * (w₁ (σ, y) 0 * (g y : ℂ)))
      atTop (𝓝 (∫ y in B0579.cell c, ∑ i : Fin 2, w₁ (σ, y) i * (perpGrad g y i : ℂ))) := by
    simpa using (hφ_lim _ hint_sum1).add hrem_lim
  have hRHS_lim := hφ_lim _ hint_cg
  have hibp_eq : ∫ y in B0579.cell c, ∑ i : Fin 2, w₁ (σ, y) i * (perpGrad g y i : ℂ) =
      ∫ y in B0579.cell c, profCurl wq₁ wη₁ (σ, y) * (g y : ℂ) := by
    refine tendsto_nhds_unique hLHS_lim (hRHS_lim.congr' ?_)
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with L hL using (hibp_L L hL).symm
  have hpair_ae_cell : (fun y : B0579.Plane =>
      ∑ i : Fin 2, w₁ (σ, y) i * ((perpGrad (fun z => H (s - σ, z)) y i : ℝ) : ℂ)) =ᵐ[
        volume.restrict (B0579.cell c)]
      fun y : B0579.Plane =>
        ∑ i : Fin 2, w (σ, y) i * ((perpGrad (fun z => H (s - σ, z)) y i : ℝ) : ℂ) := by
    filter_upwards [ae_restrict_of_ae hw_ae] with y hy
    simp [hy]
  have hcurl_ae_cell : (fun y : B0579.Plane => profCurl wq₁ wη₁ (σ, y)) =ᵐ[
      volume.restrict (B0579.cell c)] fun y : B0579.Plane => profCurl wq wη (σ, y) := by
    filter_upwards [ae_restrict_of_ae hwq_ae, ae_restrict_of_ae hwη_ae] with y h1 h2
    simp [profCurl, h1, h2]
  have hint_w_cell : IntegrableOn
      (fun y : B0579.Plane =>
        ∑ i : Fin 2, w (σ, y) i * ((perpGrad (fun z => H (s - σ, z)) y i : ℝ) : ℂ))
      (B0579.cell c) := hint_sum1.congr hpair_ae_cell
  have hint_w_avg : Integrable
      (fun y : B0579.Plane =>
        ∑ i : Fin 2, w (σ, y) i * ((perpGrad (fun z => H (s - σ, z)) y i : ℝ) : ℂ))
      (Cyl.avgμ c) := by
    rw [avgμ_eq_smul_cell c]
    exact hint_w_cell.integrable.smul_measure ENNReal.ofReal_ne_top
  refine ⟨hint_w_avg, ?_⟩
  have hsp_eq : slicePair c w H σ s =
      ((c⁻¹ : ℝ) : ℂ) * ∫ y in B0579.cell c, profCurl wq wη (σ, y) * (g y : ℂ) := by
    unfold slicePair
    rw [avgμ_eq_smul_cell c, integral_smul_measure,
      ENNReal.toReal_ofReal (inv_nonneg.2 hc.le), Complex.real_smul,
      ← integral_congr_ae hpair_ae_cell, hibp_eq]
    congr 1
    refine integral_congr_ae ?_
    filter_upwards [hcurl_ae_cell] with y hy
    rw [hy]
  have hcs : ∫⁻ y in B0579.cell c, ‖profCurl wq wη (σ, y) * (g y : ℂ)‖ₑ ≤
      eLpNorm (fun y => profCurl wq wη (σ, y)) 2 (B0579.cellMeasure c 0) *
        eLpNorm (fun y => (ζ y : ℂ)) 2 (volume.restrict (B0579.cell c)) := by
    have hcm : eLpNorm (fun y => profCurl wq wη (σ, y)) 2 (B0579.cellMeasure c 0) =
        (∫⁻ y in B0579.cell c, ‖profCurl wq wη (σ, y)‖ₑ ^ (2 : ℝ)) ^ (1 / 2 : ℝ) := by
      rw [cellMeasure_zero_eq c,
        eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by norm_num)]
      simp
    have hgm : eLpNorm (fun y => (g y : ℂ)) 2 (volume.restrict (B0579.cell c)) =
        (∫⁻ y in B0579.cell c, ‖(g y : ℂ)‖ₑ ^ (2 : ℝ)) ^ (1 / 2 : ℝ) := by
      rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by norm_num)]
      simp
    have hwc_aem : AEMeasurable (fun y => ‖profCurl wq wη (σ, y)‖ₑ)
        (volume.restrict (B0579.cell c)) :=
      hcurl_mem2.1.enorm.congr (hcurl_ae_cell.mono fun _ hy => by dsimp only at hy ⊢; rw [hy])
    calc ∫⁻ y in B0579.cell c, ‖profCurl wq wη (σ, y) * (g y : ℂ)‖ₑ
        = ∫⁻ y in B0579.cell c, ‖profCurl wq wη (σ, y)‖ₑ * ‖(g y : ℂ)‖ₑ :=
          lintegral_congr fun y => enorm_mul _ _
      _ ≤ (∫⁻ y in B0579.cell c, ‖profCurl wq wη (σ, y)‖ₑ ^ (2 : ℝ)) ^ (1 / 2 : ℝ) *
            (∫⁻ y in B0579.cell c, ‖(g y : ℂ)‖ₑ ^ (2 : ℝ)) ^ (1 / 2 : ℝ) :=
          ENNReal.lintegral_mul_le_Lp_mul_Lq _ Real.HolderConjugate.two_two
            hwc_aem hg_mem2.1.enorm
      _ = eLpNorm (fun y => profCurl wq wη (σ, y)) 2 (B0579.cellMeasure c 0) *
            eLpNorm (fun y => (g y : ℂ)) 2 (volume.restrict (B0579.cell c)) := by
          rw [hcm, hgm]
      _ ≤ _ := mul_le_mul_of_nonneg_left hH_L2 zero_le
  have hcurl_fin : eLpNorm (fun y => profCurl wq wη (σ, y)) 2 (B0579.cellMeasure c 0) < ⊤ := by
    rw [cellMeasure_zero_eq c, ← eLpNorm_congr_ae hcurl_ae_cell]
    exact hcurl_mem2.2
  have hrhs_ne_top :
      eLpNorm (fun y => profCurl wq wη (σ, y)) 2 (B0579.cellMeasure c 0) *
        eLpNorm (fun y => (ζ y : ℂ)) 2 (volume.restrict (B0579.cell c)) ≠ ⊤ :=
    (ENNReal.mul_lt_top hcurl_fin hζ_fin).ne
  rw [hsp_eq, norm_mul, Complex.norm_real, Real.norm_of_nonneg (inv_nonneg.2 hc.le)]
  refine mul_le_mul_of_nonneg_left ?_ (inv_nonneg.2 hc.le)
  calc ‖∫ y in B0579.cell c, profCurl wq wη (σ, y) * (g y : ℂ)‖
      ≤ (∫⁻ y in B0579.cell c, ‖profCurl wq wη (σ, y) * (g y : ℂ)‖ₑ).toReal := by
          simpa only [ofReal_norm] using
            norm_integral_le_lintegral_norm (fun y => profCurl wq wη (σ, y) * (g y : ℂ))
    _ ≤ _ := ENNReal.toReal_mono hrhs_ne_top hcs

lemma inHr_lateSmul_of_inHr {c r : ℝ} (δ : ℝ) {u : CProf} (hu : InHr c r u) :
    InHr c r (lateSmul δ u) := by
  have hper : QPeriodic c (lateSmul δ u) := by
    filter_upwards [hu.periodic] with x hx
    show ((lateCut δ (qShift c x).1 : ℝ) : ℂ) • u (qShift c x) = _
    have hs : (qShift c x).1 = x.1 := rfl
    rw [hs, hx]; rfl
  have hmeas : AEStronglyMeasurable (lateSmul δ u) (hMeas c r) :=
    (Complex.continuous_ofReal.comp
      ((contDiff_lateCut δ).continuous.comp continuous_fst)).aestronglyMeasurable.smul hu.meas
  refine ⟨hper, hmeas, lt_of_le_of_lt ?_ hu.finite⟩
  refine eLpNorm_mono fun x => ?_
  simp only [lateSmul, norm_smul, Complex.norm_real, Real.norm_eq_abs]
  exact mul_le_of_le_one_left (norm_nonneg _) (abs_lateCut_le_one δ x.1)

lemma kappa_eq_zero_of_curl_tendsto {c ν : ℝ} (hc : 0 < c) {ζ : ℝ × ℝ → ℝ} (hζ : NiceStream c ζ)
    {H : Coord → ℝ} (hH : HeatSol c ν (bgp / (bgp - 1)) H)
    (hcon : ∀ τ : ℝ, 0 < τ → ∀ i : Fin 2,
      ∫⁻ y, ‖perpGrad (fun z => H (τ, z)) y i‖ₑ ^ (bgp / (bgp - 1)) ∂(Cyl.avgμ c) ≤
        ∫⁻ y, ‖perpGrad ζ y i‖ₑ ^ (bgp / (bgp - 1)) ∂(Cyl.avgμ c))
    (hζ_fin : eLpNorm (fun y => (ζ y : ℂ)) 2 (volume.restrict (B0579.cell c)) < ⊤)
    {b_Δ w wq wη d : CProf} (hd_eq : ∀ x : Coord, d x = b_Δ x + w x)
    (hb_Δ_inHr : InHr c bgp b_Δ)
    (hcurl_tendsto : Tendsto
      (fun σ => eLpNorm (fun y => profCurl wq wη (σ, y)) 2 (B0579.cellMeasure c 0))
      (𝓝[Ioi 0] 0) (𝓝 0))
    {s : ℝ} (hs : 0 < s) {κ : ℂ}
    (hall : ∀ᵐ σ : ℝ ∂volume, σ ∈ Ioo (0 : ℝ) s →
      slicePair c d H σ s = κ ∧
      AEStronglyMeasurable (fun y : ℝ × ℝ => b_Δ (σ, y)) (Cyl.avgμ c) ∧
      Integrable (fun y : B0579.Plane =>
          ∑ i : Fin 2, w (σ, y) i * ((perpGrad (fun z => H (s - σ, z)) y i : ℝ) : ℂ))
        (Cyl.avgμ c) ∧
      ‖slicePair c w H σ s‖ ≤
        c⁻¹ * (eLpNorm (fun y => profCurl wq wη (σ, y)) 2 (B0579.cellMeasure c 0) *
          eLpNorm (fun y => (ζ y : ℂ)) 2 (volume.restrict (B0579.cell c))).toReal) :
    κ = 0 := by
  have hr : (1 : ℝ) < bgp := by norm_num [bgp]
  apply norm_eq_zero.1
  refine le_antisymm ?_ (norm_nonneg κ)
  refine le_of_forall_pos_le_add fun ε hε => ?_
  rw [zero_add]
  set Z2 : ℝ := (eLpNorm (fun y => (ζ y : ℂ)) 2 (volume.restrict (B0579.cell c))).toReal
  set Dζ : ℝ := (∑ i : Fin 2,
      (∫⁻ y, ‖perpGrad ζ y i‖ₑ ^ (bgp / (bgp - 1)) ∂(Cyl.avgμ c)) ^
        (1 / (bgp / (bgp - 1)))).toReal
  have hZ2_nn : 0 ≤ Z2 := ENNReal.toReal_nonneg
  have hDζ_nn : 0 ≤ Dζ := ENNReal.toReal_nonneg
  set δ_c : ℝ := ε / (2 * (c⁻¹ * (Z2 + 1) + 1))
  have hδc_pos : 0 < δ_c := by positivity
  have hev_curl : ∀ᶠ σ : ℝ in 𝓝[Ioi 0] 0,
      eLpNorm (fun y => profCurl wq wη (σ, y)) 2 (B0579.cellMeasure c 0) <
        ENNReal.ofReal δ_c :=
    hcurl_tendsto.eventually (Iio_mem_nhds (ENNReal.ofReal_pos.2 hδc_pos))
  obtain ⟨σ₁, hσ₁_pos, hσ₁_sub⟩ := mem_nhdsGT_iff_exists_Ioo_subset.1 hev_curl
  set σ₀ : ℝ := min s (min σ₁ 1)
  have hσ₀_pos : 0 < σ₀ := lt_min hs (lt_min hσ₁_pos one_pos)
  set δ_b : ℝ := (ε / (2 * (Dζ + 1))) ^ bgp
  have hδb_pos : 0 < δ_b := Real.rpow_pos_of_pos (by positivity) bgp
  have hS_pos := smallSliceNorm c bgp b_Δ hc hr hb_Δ_inHr δ_b σ₀ hδb_pos hσ₀_pos
  set S : Set ℝ := {σ : ℝ | σ ∈ Ioo (0 : ℝ) σ₀ ∧
    ENNReal.ofReal (σ ^ (bgp / 2 - 3 / 2)) *
      ∫⁻ y, ‖b_Δ (σ, y)‖ₑ ^ bgp ∂(Cyl.avgμ c) ≤ ENNReal.ofReal δ_b}
  obtain ⟨σ, hσS, hκ_σ, hbΔ_m, hw_int, hw_bd⟩ : ∃ σ, σ ∈ S ∧
      slicePair c d H σ s = κ ∧
      AEStronglyMeasurable (fun y : ℝ × ℝ => b_Δ (σ, y)) (Cyl.avgμ c) ∧
      Integrable (fun y : B0579.Plane =>
          ∑ i : Fin 2, w (σ, y) i * ((perpGrad (fun z => H (s - σ, z)) y i : ℝ) : ℂ))
        (Cyl.avgμ c) ∧
      ‖slicePair c w H σ s‖ ≤
        c⁻¹ * (eLpNorm (fun y => profCurl wq wη (σ, y)) 2 (B0579.cellMeasure c 0) *
          eLpNorm (fun y => (ζ y : ℂ)) 2 (volume.restrict (B0579.cell c))).toReal := by
    by_contra hne
    have hae : ∀ᵐ σ ∂volume, σ ∉ S := by
      filter_upwards [hall] with σ hσ hσS
      have hσI : σ ∈ Ioo (0 : ℝ) s :=
        ⟨hσS.1.1, lt_of_lt_of_le hσS.1.2 (min_le_left _ _)⟩
      obtain ⟨a1, a2, a3, a4⟩ := hσ hσI
      exact hne ⟨σ, hσS, a1, a2, a3, a4⟩
    exact (ne_of_gt hS_pos) (measure_eq_zero_iff_ae_notMem.2 hae)
  have hσ0 : 0 < σ := hσS.1.1
  have hσs : σ < s := lt_of_lt_of_le hσS.1.2 (min_le_left _ _)
  have hσσ₁ : σ < σ₁ :=
    lt_of_lt_of_le hσS.1.2 ((min_le_right _ _).trans (min_le_left _ _))
  have hσ1 : σ ≤ 1 :=
    (le_of_lt hσS.1.2).trans ((min_le_right _ _).trans (min_le_right _ _))
  have hpow_ge1 : 1 ≤ σ ^ (bgp / 2 - 3 / 2) :=
    Real.one_le_rpow_of_pos_of_le_one_of_nonpos hσ0 hσ1 (by norm_num [bgp])
  have hB_le : ∫⁻ y, ‖b_Δ (σ, y)‖ₑ ^ bgp ∂(Cyl.avgμ c) ≤ ENNReal.ofReal δ_b := by
    calc ∫⁻ y, ‖b_Δ (σ, y)‖ₑ ^ bgp ∂(Cyl.avgμ c)
        = 1 * ∫⁻ y, ‖b_Δ (σ, y)‖ₑ ^ bgp ∂(Cyl.avgμ c) := (one_mul _).symm
      _ ≤ ENNReal.ofReal (σ ^ (bgp / 2 - 3 / 2)) *
            ∫⁻ y, ‖b_Δ (σ, y)‖ₑ ^ bgp ∂(Cyl.avgμ c) :=
          mul_le_mul_of_nonneg_right (ENNReal.one_le_ofReal.2 hpow_ge1) zero_le
      _ ≤ ENNReal.ofReal δ_b := hσS.2
  have hB_fin : ∫⁻ y, ‖b_Δ (σ, y)‖ₑ ^ bgp ∂(Cyl.avgμ c) < ⊤ :=
    lt_of_le_of_lt hB_le ENNReal.ofReal_lt_top
  have hbΔ_int : Integrable (fun y : B0579.Plane =>
      ∑ i : Fin 2, b_Δ (σ, y) i * ((perpGrad (fun z => H (s - σ, z)) y i : ℝ) : ℂ))
      (Cyl.avgμ c) := by
    refine ⟨Finset.aestronglyMeasurable_fun_sum _ fun i _ =>
      ((EuclideanSpace.proj i : CMerid →L[ℂ] ℂ).continuous.comp_aestronglyMeasurable
        hbΔ_m).mul
          (Complex.continuous_ofReal.comp
            (sd_perp_slice_continuous hH.smooth (sub_pos.2 hσs) i)).aestronglyMeasurable, ?_⟩
    unfold HasFiniteIntegral
    have hpq : bgp.HolderConjugate (bgp / (bgp - 1)) := Real.HolderConjugate.conjExponent hr
    have hr1' : (0 : ℝ) < bgp / (bgp - 1) := div_pos (by linarith) (by linarith)
    have hpt : ∀ y : B0579.Plane,
        ‖∑ i : Fin 2, b_Δ (σ, y) i * ((perpGrad (fun z => H (s - σ, z)) y i : ℝ) : ℂ)‖ₑ ≤
          ∑ i : Fin 2, ‖b_Δ (σ, y)‖ₑ * ‖perpGrad (fun z => H (s - σ, z)) y i‖ₑ := by
      intro y
      refine (enorm_sum_le _ _).trans (Finset.sum_le_sum fun i _ => ?_)
      rw [enorm_mul, ← ofReal_norm (perpGrad _ _ _ : ℂ), Complex.norm_real, ofReal_norm]
      refine mul_le_mul_of_nonneg_right ?_ zero_le
      rw [← ofReal_norm, ← ofReal_norm]
      exact ENNReal.ofReal_le_ofReal (PiLp.norm_apply_le _ _)
    refine lt_of_le_of_lt (lintegral_mono hpt) ?_
    have hterm_aem : ∀ i : Fin 2,
        AEMeasurable (fun y => ‖b_Δ (σ, y)‖ₑ * ‖perpGrad (fun z => H (s - σ, z)) y i‖ₑ)
          (Cyl.avgμ c) := fun i =>
      hbΔ_m.enorm.mul
        (sd_perp_slice_continuous hH.smooth (sub_pos.2 hσs) i).measurable.enorm.aemeasurable
    rw [lintegral_finsetSum' _ fun i _ => hterm_aem i]
    refine ENNReal.sum_lt_top.2 fun i _ => ?_
    refine lt_of_le_of_lt (ENNReal.lintegral_mul_le_Lp_mul_Lq (Cyl.avgμ c) hpq
      hbΔ_m.enorm
      (sd_perp_slice_continuous hH.smooth (sub_pos.2 hσs) i).measurable.enorm.aemeasurable) ?_
    refine ENNReal.mul_lt_top
      (ENNReal.rpow_lt_top_of_nonneg (by positivity) hB_fin.ne)
      (ENNReal.rpow_lt_top_of_nonneg (by positivity) ?_)
    exact (lt_of_le_of_lt (hcon (s - σ) (sub_pos.2 hσs) i)
      (sd_perp_lint_lt_top hc hζ hr1' i)).ne
  have hsp_split : slicePair c d H σ s =
      slicePair c b_Δ H σ s + slicePair c w H σ s := by
    unfold slicePair
    rw [← integral_add hbΔ_int hw_int]
    refine integral_congr_ae (Eventually.of_forall fun y => ?_)
    dsimp only
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    have hdy := congrArg (fun v : CMerid => v i) (hd_eq (σ, y))
    simp only [PiLp.add_apply] at hdy
    rw [hdy, add_mul]
  have hbΔ_sp_le : ‖slicePair c b_Δ H σ s‖ ≤ ε / 2 := by
    have hsl_bd := sd_slice_bound hc hr hζ hH.smooth hσs hbΔ_m hB_fin
      (fun i => hcon (s - σ) (sub_pos.2 hσs) i)
    have hD_fin : (∑ i : Fin 2,
        (∫⁻ y, ‖perpGrad ζ y i‖ₑ ^ (bgp / (bgp - 1)) ∂(Cyl.avgμ c)) ^
          (1 / (bgp / (bgp - 1)))) ≠ ⊤ :=
      (ENNReal.sum_lt_top.2 fun i _ =>
        ENNReal.rpow_lt_top_of_nonneg (by positivity)
          (sd_perp_lint_lt_top hc hζ (div_pos (by linarith) (by linarith)) i).ne).ne
    have hroot_le : (∫⁻ y, ‖b_Δ (σ, y)‖ₑ ^ bgp ∂(Cyl.avgμ c)) ^ (1 / bgp) ≤
        ENNReal.ofReal (ε / (2 * (Dζ + 1))) := by
      refine (ENNReal.rpow_le_rpow hB_le (by positivity)).trans (le_of_eq ?_)
      rw [ENNReal.ofReal_rpow_of_nonneg hδb_pos.le (by positivity)]
      congr 1
      dsimp only [δ_b]
      rw [← Real.rpow_mul (by positivity), mul_one_div_cancel (by linarith), Real.rpow_one]
    have hprod_fin : ENNReal.ofReal (ε / (2 * (Dζ + 1))) *
        (∑ i : Fin 2, (∫⁻ y, ‖perpGrad ζ y i‖ₑ ^ (bgp / (bgp - 1)) ∂(Cyl.avgμ c)) ^
          (1 / (bgp / (bgp - 1)))) ≠ ⊤ :=
      ENNReal.mul_ne_top ENNReal.ofReal_ne_top hD_fin
    calc ‖slicePair c b_Δ H σ s‖
        ≤ (ENNReal.ofReal (ε / (2 * (Dζ + 1))) *
            ∑ i : Fin 2, (∫⁻ y, ‖perpGrad ζ y i‖ₑ ^ (bgp / (bgp - 1)) ∂(Cyl.avgμ c)) ^
              (1 / (bgp / (bgp - 1)))).toReal :=
          hsl_bd.trans (ENNReal.toReal_mono hprod_fin
            (mul_le_mul_of_nonneg_right hroot_le zero_le))
      _ = (ε / (2 * (Dζ + 1))) * Dζ := by
          rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (by positivity)]
      _ ≤ ε / 2 := by
          have hle1 : Dζ / (Dζ + 1) ≤ 1 := (div_le_one (by linarith)).2 (by linarith)
          calc (ε / (2 * (Dζ + 1))) * Dζ = (ε / 2) * (Dζ / (Dζ + 1)) := by field_simp
            _ ≤ (ε / 2) * 1 := mul_le_mul_of_nonneg_left hle1 (by positivity)
            _ = ε / 2 := mul_one _
  have hw_sp_le : ‖slicePair c w H σ s‖ ≤ ε / 2 := by
    have hc_lt : eLpNorm (fun y => profCurl wq wη (σ, y)) 2 (B0579.cellMeasure c 0) ≤
        ENNReal.ofReal δ_c := (hσ₁_sub ⟨hσ0, hσσ₁⟩).le
    have hfin_p : ENNReal.ofReal δ_c *
        eLpNorm (fun y => (ζ y : ℂ)) 2 (volume.restrict (B0579.cell c)) ≠ ⊤ :=
      ENNReal.mul_ne_top ENNReal.ofReal_ne_top hζ_fin.ne
    calc ‖slicePair c w H σ s‖
        ≤ c⁻¹ * (ENNReal.ofReal δ_c *
            eLpNorm (fun y => (ζ y : ℂ)) 2 (volume.restrict (B0579.cell c))).toReal :=
          hw_bd.trans (mul_le_mul_of_nonneg_left
            (ENNReal.toReal_mono hfin_p (mul_le_mul_of_nonneg_right hc_lt zero_le))
            (inv_nonneg.2 hc.le))
      _ = c⁻¹ * (δ_c * Z2) := by
          rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal hδc_pos.le]
      _ ≤ ε / 2 := by
          have hnum : c⁻¹ * Z2 ≤ c⁻¹ * (Z2 + 1) + 1 := by
            have : c⁻¹ * Z2 ≤ c⁻¹ * (Z2 + 1) :=
              mul_le_mul_of_nonneg_left (by linarith) (inv_nonneg.2 hc.le)
            linarith
          have hden : 0 < c⁻¹ * (Z2 + 1) + 1 := by positivity
          have hq1 : (c⁻¹ * Z2) / (c⁻¹ * (Z2 + 1) + 1) ≤ 1 := (div_le_one hden).2 hnum
          calc c⁻¹ * (δ_c * Z2)
              = (ε / 2) * ((c⁻¹ * Z2) / (c⁻¹ * (Z2 + 1) + 1)) := by
                dsimp only [δ_c]; field_simp
            _ ≤ (ε / 2) * 1 := mul_le_mul_of_nonneg_left hq1 (by positivity)
            _ = ε / 2 := mul_one _
  rw [← hκ_σ, hsp_split]
  exact (norm_add_le _ _).trans (by linarith)

end ZeroCurlUniqueHelp

/-- **Unconditional proof of Sub-step 3 (`FlatReconstructionZeroCurlUniqueStep`)**. -/
theorem flatReconstructionZeroCurlUniqueStep_proof : FlatReconstructionZeroCurlUniqueStep := by
  intro lam q hq dm dp _hdm p d_param hreg hν_half hmode α b0 z zq zη b_f
    hb0 hbf hz_per hzq hzη ⟨M₁, hH1_z⟩ hcurl_tendsto hdiff_resp
  have hc : 0 < p.c := p.c_pos
  have hν : 0 < p.ν := p.ν_pos
  have hr : (1 : ℝ) < bgp := by norm_num [bgp]
  have hr3 : bgp < 3 := by norm_num [bgp]
  have hr1 : (1 : ℝ) ≤ bgp := hr.le
  let w : CProf := fun x => z x - inletProf p α x
  let wq : CProf := fun x => zq x - inletProfQ p α x
  let wη : CProf := fun x => zη x - inletProfEta p α x
  let b_Δ : CProf := fun x => b0 x - b_f x
  let d : CProf := fun x => (b0 x + z x - inletProf p α x) - b_f x
  have hd_eq : ∀ x : Coord, d x = b_Δ x + w x := by
    intro x; ext i; simp only [d, b_Δ, w, PiLp.add_apply, PiLp.sub_apply]; ring
  have hb_Δ_inHr : InHr p.c bgp b_Δ := LinearR0Help.inHr_sub_of hr1 hb0.inHr hbf.inHr
  have hw_per : QPeriodic p.c w := by
    filter_upwards [hz_per, qPeriodic_inletProf p α] with x h1 h2; simp [w, h1, h2]
  obtain ⟨w₁, wq₁, wη₁, C_w, hCw_nn, hw₁_sm, _hwq₁_sm, _hwη₁_sm, hw₁_per, _hwq₁_per, _hwη₁_per,
    hw₁_ae, hwq₁_ae, hwη₁_ae, hsl_all⟩ :=
    ZeroCurlUniqueHelp.upgrade_w_triple hq hreg hν_half hmode α hz_per hzq hzη hH1_z
  have hlate_w : ∀ δ : ℝ, 0 < δ → InHr p.c bgp (ZeroCurlUniqueHelp.lateSmul δ w) :=
    fun δ hδ => ZeroCurlUniqueHelp.inHr_lateSmul_of_slice_bound hc hCw_nn hδ hw_per hw₁_sm
      hw₁_per hw₁_ae (hsl_all.mono fun s hs hs0 => (hs hs0).1)
  have hlate_bΔ : ∀ δ : ℝ, 0 < δ → InHr p.c bgp (ZeroCurlUniqueHelp.lateSmul δ b_Δ) :=
    fun δ _hδ => ZeroCurlUniqueHelp.inHr_lateSmul_of_inHr δ hb_Δ_inHr
  have hlate_d : ∀ δ : ℝ, 0 < δ → InHr p.c bgp (ZeroCurlUniqueHelp.lateSmul δ d) := by
    intro δ hδ
    have heq : ZeroCurlUniqueHelp.lateSmul δ d =
        fun x => ZeroCurlUniqueHelp.lateSmul δ b_Δ x + ZeroCurlUniqueHelp.lateSmul δ w x := by
      funext x; simp [ZeroCurlUniqueHelp.lateSmul, hd_eq x, smul_add]
    rw [heq]
    exact inHr_add_of hr1 (hlate_bΔ δ hδ) (hlate_w δ hδ)
  -- Key step: `slicePair p.c d (heatStreamH p.ν ζ) · s = 0` a.e. on `Ioo 0 s` for every nice `ζ`
  have hslice_vanish : ∀ (ζ : ℝ × ℝ → ℝ), NiceStream p.c ζ → ∀ (s : ℝ), 0 < s →
      ∀ᵐ σ : ℝ ∂(volume.restrict (Ioo (0 : ℝ) s)),
        slicePair p.c d (heatStreamH p.ν ζ) σ s = 0 := by
    intro ζ hζ s hs
    let H : Coord → ℝ := heatStreamH p.ν ζ
    obtain ⟨hH, hcon, _hconv, hH_L2_all, hζ_fin⟩ :=
      ZeroCurlUniqueHelp.heatStreamH_props hc hν hr hζ
    obtain ⟨κ, hκ⟩ :=
      ZeroCurlUniqueHelp.dualConstancy_of_late_inHr hc hν hr hs hlate_d hdiff_resp hH
    have hw_curl_ae : ∀ᵐ σ : ℝ ∂(volume.restrict (Ioo (0 : ℝ) s)),
        Integrable (fun y : B0579.Plane =>
            ∑ i : Fin 2, w (σ, y) i * ((perpGrad (fun z => H (s - σ, z)) y i : ℝ) : ℂ))
          (Cyl.avgμ p.c) ∧
        ‖slicePair p.c w H σ s‖ ≤
          p.c⁻¹ * (eLpNorm (fun y => profCurl wq wη (σ, y)) 2 (B0579.cellMeasure p.c 0) *
            eLpNorm (fun y => (ζ y : ℂ)) 2 (volume.restrict (B0579.cell p.c))).toReal := by
      filter_upwards [ae_restrict_of_ae (F8L.slice_ae hw₁_ae),
        ae_restrict_of_ae (F8L.slice_ae hwq₁_ae),
        ae_restrict_of_ae (F8L.slice_ae hwη₁_ae),
        ae_restrict_of_ae hsl_all,
        ae_restrict_mem measurableSet_Ioo] with σ hs_w hs_wq hs_wη hsl hσI
      obtain ⟨_, hmw, hmwq, hmwη, hcd0, hcd1⟩ := hsl hσI.1
      obtain ⟨hHL2, hpL2⟩ := hH_L2_all (s - σ) (sub_pos.2 hσI.2)
      exact ZeroCurlUniqueHelp.slicePair_curl_bound hc hH.smooth hH.periodic hσI.2
        (hs_w hσI.1) (hs_wq hσI.1) (hs_wη hσI.1) hmw hmwq hmwη hcd0 hcd1 hHL2 hζ_fin hpL2
    have hbΔ_meas_ae : ∀ᵐ σ : ℝ ∂(volume.restrict (Ioo (0 : ℝ) s)),
        AEStronglyMeasurable (fun y : ℝ × ℝ => b_Δ (σ, y)) (Cyl.avgμ p.c) :=
      ae_restrict_of_ae_restrict_of_subset Ioo_subset_Ioi_self
        (slice_aestronglyMeasurable hc hb_Δ_inHr)
    have hall : ∀ᵐ σ : ℝ ∂volume, σ ∈ Ioo (0 : ℝ) s →
        slicePair p.c d H σ s = κ ∧
        AEStronglyMeasurable (fun y : ℝ × ℝ => b_Δ (σ, y)) (Cyl.avgμ p.c) ∧
        Integrable (fun y : B0579.Plane =>
            ∑ i : Fin 2, w (σ, y) i * ((perpGrad (fun z => H (s - σ, z)) y i : ℝ) : ℂ))
          (Cyl.avgμ p.c) ∧
        ‖slicePair p.c w H σ s‖ ≤
          p.c⁻¹ * (eLpNorm (fun y => profCurl wq wη (σ, y)) 2 (B0579.cellMeasure p.c 0) *
            eLpNorm (fun y => (ζ y : ℂ)) 2 (volume.restrict (B0579.cell p.c))).toReal := by
      filter_upwards [(ae_restrict_iff' measurableSet_Ioo).1
        (hκ.and (hbΔ_meas_ae.and hw_curl_ae))] with σ hσ hσI
      obtain ⟨h1, h2, h3, h4⟩ := hσ hσI
      exact ⟨h1, h2, h3, h4⟩
    have hκ_zero : κ = 0 :=
      ZeroCurlUniqueHelp.kappa_eq_zero_of_curl_tendsto hc hζ hH hcon hζ_fin hd_eq hb_Δ_inHr
        hcurl_tendsto hs hall
    filter_upwards [hκ] with σ hσ
    rw [hσ, hκ_zero]
  -- Conclude `lateSmul δ d =ᵐ[hMeas p.c bgp] 0` for every `δ > 0` via `niceFieldsSeparate`
  have hlate_zero : ∀ δ : ℝ, 0 < δ → ZeroCurlUniqueHelp.lateSmul δ d =ᵐ[hMeas p.c bgp] 0 := by
    intro δ hδ
    set bδ : CProf := ZeroCurlUniqueHelp.lateSmul δ d
    have hbδ : InHr p.c bgp bδ := hlate_d δ hδ
    have hsolδ := ZeroCurlUniqueHelp.lateSmul_solenoidal δ hdiff_resp.solenoidal
    refine niceFieldsSeparate p.c bgp bδ hc hr hr3 hbδ hsolδ (fun θ ζ hθ hζ => ?_)
    rw [sliceProductFormula p.c bgp bδ θ ζ hc hr hbδ hθ hζ]
    obtain ⟨hH, _hcon, hconv, _, _⟩ := ZeroCurlUniqueHelp.heatStreamH_props hc hν hr hζ
    have e1 : ∀ s : ℝ, 0 < s →
        ∀ᵐ σ : ℝ ∂(volume.restrict (Ioo (0 : ℝ) s)),
          slicePair p.c bδ (heatStreamH p.ν ζ) σ s = 0 := by
      intro s hs
      filter_upwards [hslice_vanish ζ hζ s hs] with σ hσ
      have hfac : slicePair p.c bδ (heatStreamH p.ν ζ) σ s =
          ((ZeroCurlUniqueHelp.lateCut δ σ : ℝ) : ℂ) *
            slicePair p.c d (heatStreamH p.ν ζ) σ s := by
        unfold slicePair
        rw [← integral_const_mul]
        refine integral_congr_ae (Eventually.of_forall fun y => ?_)
        dsimp only
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun i _ => ?_
        simp only [bδ, ZeroCurlUniqueHelp.lateSmul, PiLp.smul_apply, smul_eq_mul, mul_assoc]
      rw [hfac, hσ, mul_zero]
    have e2 := sliceJointNull p.c bgp p.ν bδ (heatStreamH p.ν ζ) hc hr hbδ hH e1
    have e3 := slicePointwise p.c bgp bδ ζ (heatStreamH p.ν ζ) hc hr hbδ hζ hconv e2
    refine integral_eq_zero_of_ae ?_
    filter_upwards [e3] with σ hσ
    have hstr : ∀ y, streamPair bδ θ ζ (σ, y) =
        (θ σ : ℂ) * ∑ i : Fin 2, bδ (σ, y) i * ((perpGrad ζ y i : ℝ) : ℂ) := by
      intro y
      simp only [streamPair, Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      push_cast; ring
    simp_rw [hstr]
    simp only [Pi.zero_apply]
    rw [integral_const_mul, hσ, mul_zero]
  -- Intersect over `δ = 1 / (n + 1)` (`n : ℕ`) to obtain `d =ᵐ[hMeas p.c bgp] 0`
  have hall_n : ∀ᵐ x : Coord ∂(hMeas p.c bgp),
      ∀ n : ℕ, ZeroCurlUniqueHelp.lateSmul (1 / ((n : ℝ) + 1)) d x = 0 :=
    ae_all_iff.2 fun n => hlate_zero (1 / ((n : ℝ) + 1)) (by positivity)
  filter_upwards [hall_n, Axi.ae_ageμ_mem hc (bgp / 2 - 5 / 2)] with x hx hpos
  have hx0 : 0 < x.1 := hpos.1
  obtain ⟨n, hn⟩ := exists_nat_gt (2 / x.1)
  have hδn_pos : 0 < (1 : ℝ) / ((n : ℝ) + 1) := by positivity
  have h2δ_le : 2 * (1 / ((n : ℝ) + 1)) ≤ x.1 := by
    have hn1 : 0 < (n : ℝ) + 1 := by positivity
    rw [mul_one_div, div_le_iff₀ hn1]
    have h2 : 2 < (n : ℝ) * x.1 := (div_lt_iff₀ hx0).1 hn
    nlinarith
  have hlc1 : ZeroCurlUniqueHelp.lateCut (1 / ((n : ℝ) + 1)) x.1 = 1 :=
    ZeroCurlUniqueHelp.lateCut_eq_one hδn_pos h2δ_le
  have hdn0 : d x = 0 := by
    have h : ZeroCurlUniqueHelp.lateSmul (1 / ((n : ℝ) + 1)) d x = 0 := hx n
    unfold ZeroCurlUniqueHelp.lateSmul at h
    rw [hlc1] at h
    simpa using h
  exact sub_eq_zero.1 hdn0

/-- **Unconditional proof of `FlatReconstructionIdentityStep` (`PartII-b:F9/3`)**. -/
theorem flatReconstructionIdentityStep_proof : UnforcedLeray.Short.IIb.FlatReconstructionIdentityStep :=
  flatReconstructionIdentityStep_of_steps
    flatReconstructionLinearR0Step_proof
    inletEntranceCurlIdentity_proof
    flatReconstructionZeroCurlUniqueStep_proof

end UnforcedLeray.Short.IIb

end
