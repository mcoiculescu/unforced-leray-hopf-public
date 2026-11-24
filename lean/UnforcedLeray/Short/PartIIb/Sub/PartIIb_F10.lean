import UnforcedLeray.Short.PartIIb.Sub.FlatInverseDesign
import UnforcedLeray.Short.PartIIb.Sub.G4_3_org
import UnforcedLeray.Short.PartIIb.Sub.PartIIb_T13_4
import UnforcedLeray.Short.PartIIb.Tasks.FlatWindows.ClassSub
import UnforcedLeray.Short.PartIIb.Tasks.BodySource.FlatGraphD2Slice
import UnforcedLeray.Short.PartIIb.Tasks.ProfileGraphPhys.GradBound
import UnforcedLeray.Short.PartIIb.Tasks.FlatUnique.Separate.HMeasAe
import UnforcedLeray.Short.PartIIb.Tasks.GradLapNvC.LapSmooth.WeakQ
import UnforcedLeray.Short.PartIIb.Tasks.GradLapNvC.LapSmooth.WeakEta
import UnforcedLeray.Short.PartIIb.Tasks.AffineColumnComparison.InletContDiff

/-!
# `PartII-b:F10` (`Sub/PartII-b_F10.lean`): Flat background inverse `R_0` on `H_p`

Source of record: `the November 2 reference manuscript`
(SP), lines 2326-2344 (`short-bg:flat-inverse`).

## Proved here (zero `sorry`)

1. `liftM_flatColR`, `memLp_flatColR`, `exists_C0op_of_flatColumn_inHr`: construction of
   `C0 : E2 →L[ℝ] HpR p.c` satisfying `IsC0op p C0` from `∀ i : Fin 2, InHr p.c bgp (flatColumn p i)`.
2. `toProf_eq_of_ae_eq`, `toProf_rowOp_ae`, `rowOp_eq_of_toProf_ae`: injectivity of `toProf` and the
   algebraic right-inverse identity `rowOp K0 C0 (R0 F) = F`.
3. `flatResponse_unique_ae`: a.e. uniqueness of flat responses in `InFlatClass p.c bgp`.
4. `inletProf_hasWeakVec`: smooth integration by parts proving
   `HasWeakVec vQ0 dZero (inletProf p α) (inletProfQ p α)` and
   `HasWeakVec vEta dZero (inletProf p α) (inletProfEta p α)` in `BgRegime`.
5. `flatK0_reconstructed_congr`: for any `K0` satisfying `IsK0op p K0`, when `b_0 + z - Eα` is the
   flat response `T_0 (toProf p.c f)` in `InFlatClass p.c bgp`, `toProf p.c (K0 f)` agrees
   `hMeas p.c bgp`-a.e. with `flatK p.train (b0 + z - Eα) (b0q + zq - ∂_q Eα) (b0η + zη - ∂_η Eα)`.
6. `flatInverse_of_k0Exists`: complete conditional assembly of `FlatInverse` (`PartII-b:F10`) from
   `FlatK0OperatorExists` (`PartII-b:F10/1`) and `FlatReconstruction` (`PartII-b:F9`).
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal NNReal ContDiff

namespace UnforcedLeray.Short.IIb

open UnforcedLeray.Cons.C03 UnforcedLeray.Cons.C03.Concrete UnforcedLeray.Blueprint

/-! ## 1. Construction of `C_0 : E2 →L[ℝ] HpR p.c` satisfying `IsC0op p C0` -/

/-- The real profile underlying `flatColumn p i`. -/
def flatColR (p : Params) (i : Fin 2) (x : Coord) : Axi.Merid :=
  reM (flatColumn p i x)

/-- `flatColumn p i` has purely real coordinates everywhere on `Coord`, so `liftM (flatColR p i x)`
equals `flatColumn p i x` identically. -/
theorem liftM_flatColR (p : Params) (i : Fin 2) (x : Coord) :
    liftM (flatColR p i x) = flatColumn p i x := by
  ext j
  simp [liftM, flatColR, reM, flatColumn, flatK, cplx]

/-- If `flatColumn p i` belongs to `H_p`, then `flatColR p i` belongs to `Lp Axi.Merid bgp (hMeas p.c bgp)`. -/
theorem memLp_flatColR {p : Params} {i : Fin 2} (h : InHr p.c bgp (flatColumn p i)) :
    MemLp (flatColR p i) (ENNReal.ofReal bgp) (hMeas p.c bgp) := by
  refine ⟨continuous_reM.comp_aestronglyMeasurable h.meas, ?_⟩
  have e : eLpNorm (flatColR p i) (ENNReal.ofReal bgp) (hMeas p.c bgp) =
      hNorm p.c bgp (flatColumn p i) := by
    unfold hNorm
    refine eLpNorm_congr_norm_ae (Eventually.of_forall fun x => ?_)
    rw [← liftM_norm (flatColR p i x), liftM_flatColR]
  rw [e]
  exact h.finite

/-- From `∀ i : Fin 2, InHr p.c bgp (flatColumn p i)`, construct `C0 : E2 →L[ℝ] HpR p.c`
satisfying `IsC0op p C0`. -/
theorem exists_C0op_of_flatColumn_inHr (p : Params)
    (hCol : ∀ i : Fin 2, InHr p.c bgp (flatColumn p i)) :
    ∃ C0 : E2 →L[ℝ] HpR p.c, IsC0op p C0 := by
  have hc : 0 < p.c := p.c_pos
  let g : Fin 2 → HpR p.c := fun i => (memLp_flatColR (hCol i)).toLp (flatColR p i)
  have hg : ∀ i : Fin 2, toProf p.c (g i) =ᵐ[hMeas p.c bgp] flatColumn p i := by
    intro i
    filter_upwards [toProf_ae_eq hc (g i), MemLp.coeFn_toLp (memLp_flatColR (hCol i))]
      with x h1 h2
    rw [h1, h2, liftM_flatColR]
  refine ⟨colOp g, fun α => ?_⟩
  have h2 : ((colOp g α : HpR p.c) : Coord → Axi.Merid) =ᵐ[hMeas p.c bgp]
      fun x => α 0 • (g 0 : Coord → Axi.Merid) x + α 1 • (g 1 : Coord → Axi.Merid) x := by
    rw [colOp_apply]
    filter_upwards [Lp.coeFn_add (α 0 • g 0) (α 1 • g 1), Lp.coeFn_smul (α 0) (g 0),
      Lp.coeFn_smul (α 1) (g 1)] with x hx h0 h1
    rw [hx, Pi.add_apply, h0, h1]
    rfl
  filter_upwards [toProf_ae_eq hc (colOp g α), h2, hg 0, hg 1, toProf_ae_eq hc (g 0),
    toProf_ae_eq hc (g 1)] with x a b c0 c1 d0 d1
  rw [a, b, Fin.sum_univ_two, ← c0, ← c1, d0, d1, liftM_lin]

/-! ## 2. Injectivity of `toProf` and the equation-row identity `rowOp K0 C0 (R0 F) = F` -/

theorem reM_liftM (v : Axi.Merid) : reM (liftM v) = v := by
  ext j
  simp [reM, liftM]

theorem liftM_add' (v w : Axi.Merid) : liftM (v + w) = liftM v + liftM w := by
  ext j
  simp [liftM]

/-- Two elements of `HpR c` (`c > 0`) whose `toProf c` profiles agree `hMeas c bgp`-a.e. are equal. -/
theorem toProf_eq_of_ae_eq {c : ℝ} (hc : 0 < c) {g₁ g₂ : HpR c}
    (h : toProf c g₁ =ᵐ[hMeas c bgp] toProf c g₂) : g₁ = g₂ := by
  apply Lp.ext
  filter_upwards [toProf_ae_eq hc g₁, toProf_ae_eq hc g₂, h] with x h1 h2 heq
  have h3 : liftM ((g₁ : Coord → Axi.Merid) x) = liftM ((g₂ : Coord → Axi.Merid) x) := by
    rw [← h1, ← h2, heq]
  simpa only [reM_liftM] using congrArg reM h3

/-- For any `K0, C0` and `y : RowSpace p.c`, `toProf p.c (rowOp K0 C0 y)` agrees a.e. with
`toProf p.c f + toProf p.c (K0 f) + toProf p.c (C0 α)` where `f = fstL y` and `α = sndL y`. -/
theorem toProf_rowOp_ae {c : ℝ} (hc : 0 < c)
    (K0 : HpR c →L[ℝ] HpR c) (C0 : E2 →L[ℝ] HpR c) (y : RowSpace c) :
    let f : HpR c := (WithLp.fstL 1 ℝ (HpR c) E2) y
    let α : E2 := (WithLp.sndL 1 ℝ (HpR c) E2) y
    toProf c (rowOp K0 C0 y) =ᵐ[hMeas c bgp]
      fun x => toProf c f x + toProf c (K0 f) x + toProf c (C0 α) x := by
  intro f α
  have hrow : rowOp K0 C0 y = f + K0 f + C0 α := by
    simp [rowOp, f, α]
  rw [hrow]
  filter_upwards [toProf_ae_eq hc (f + K0 f + C0 α),
    Lp.coeFn_add (f + K0 f) (C0 α), Lp.coeFn_add f (K0 f),
    toProf_ae_eq hc f, toProf_ae_eq hc (K0 f), toProf_ae_eq hc (C0 α)]
    with x htot hadd1 hadd2 hf hKf hCα
  rw [htot, hadd1, Pi.add_apply, hadd2, Pi.add_apply, liftM_add', liftM_add', ← hf, ← hKf, ← hCα]

/-- Algebraic deduction of `rowOp K0 C0 (R0 F) = F` from the `FlatReconstruction` profile identity,
`IsC0op p C0`, and `toProf p.c (K0 f) =ᵐ flatK p.train (b0 + z - Eα) ...`. -/
theorem rowOp_eq_of_toProf_ae {p : Params}
    (K0 : HpR p.c →L[ℝ] HpR p.c) (C0 : E2 →L[ℝ] HpR p.c) (hC0 : IsC0op p C0)
    (R0 : HpR p.c →L[ℝ] RowSpace p.c) (F : HpR p.c)
    (K_prof : CProf)
    (hK_ae : toProf p.c (K0 ((WithLp.fstL 1 ℝ (HpR p.c) E2) (R0 F))) =ᵐ[hMeas p.c bgp] K_prof)
    (hrec_ae : toProf p.c ((WithLp.fstL 1 ℝ (HpR p.c) E2) (R0 F)) =ᵐ[hMeas p.c bgp] fun x =>
      toProf p.c F x - K_prof x -
        ∑ i : Fin 2, ((((WithLp.sndL 1 ℝ (HpR p.c) E2) (R0 F)) i : ℝ) : ℂ) • flatColumn p i x) :
    rowOp K0 C0 (R0 F) = F := by
  have hc : 0 < p.c := p.c_pos
  let f : HpR p.c := (WithLp.fstL 1 ℝ (HpR p.c) E2) (R0 F)
  let α : E2 := (WithLp.sndL 1 ℝ (HpR p.c) E2) (R0 F)
  apply toProf_eq_of_ae_eq hc
  filter_upwards [toProf_rowOp_ae hc K0 C0 (R0 F), hrec_ae, hK_ae, hC0 α]
    with x hrow hrec hK hC
  rw [hrow, hrec, hK, hC]
  abel

/-- Any two flat responses `b₁, b₂` to the same source `F ∈ H_p` in `InFlatClass c bgp` agree
`hMeas c bgp`-almost everywhere (from `profileGraphFlat_bgp`, `PartII-b:T14`). -/
theorem flatResponse_unique_ae {ν c : ℝ} (hν : 0 < ν) (hc : 0 < c) {F b₁ b₂ : CProf}
    (hF : InHr c bgp F) (hb₁ : InFlatClass c bgp b₁) (hr₁ : IsFlatResponse ν 0 F b₁)
    (hb₂ : InFlatClass c bgp b₂) (hr₂ : IsFlatResponse ν 0 F b₂) :
    b₁ =ᵐ[hMeas c bgp] b₂ := by
  obtain ⟨_, _, H_fg⟩ := profileGraphFlat_bgp
  obtain ⟨b, _, _, _, huniq⟩ := H_fg ν c hν hc F hF
  exact (huniq b₁ hb₁ hr₁).trans (huniq b₂ hb₂ hr₂).symm

/-! ## 3. Weak derivatives of `inletProf` and uniqueness of `K_0` on reconstructed responses -/

namespace F10Help

lemma vQ0_component_smooth (j : Fin 3) : ContDiff ℝ ∞ (fun x : Coord => vQ0 x j) := by
  fin_cases j <;> simp [vQ0] <;> exact contDiff_const

lemma hasWeakFO_of_contDiff {v : Coord → Fin 3 → ℝ} (hv : ∀ j : Fin 3, ContDiff ℝ ∞ (fun x => v x j))
    {u g : Coord → ℂ} (hu : ContDiff ℝ ∞ u)
    (hg : ∀ x : Coord, g x = LapWeakQHelp.genOp v dZero u x) :
    HasWeakFO v dZero u g := by
  have hd : ContDiff ℝ ∞ dZero := contDiff_const
  have hRc : Continuous (LapWeakQHelp.genOp v dZero u) := by
    unfold LapWeakQHelp.genOp
    apply Continuous.add
    · apply continuous_finsetSum
      intro j _
      exact (Complex.continuous_ofReal.comp (hv j).continuous).mul
        ((hu.continuous_fderiv (by simp)).clm_apply continuous_const)
    · exact (Complex.continuous_ofReal.comp hd.continuous).mul hu.continuous
  have hg_eq : g = LapWeakQHelp.genOp v dZero u := funext hg
  rw [hg_eq]
  refine ⟨fun φ hφ => ⟨?_, ?_⟩, fun φ hφ => ?_⟩
  · have hct : ContDiff ℝ ∞ (coordTranspose v dZero φ) := by
      unfold coordTranspose cpd
      apply ContDiff.add
      · apply ContDiff.neg
        apply ContDiff.sum
        intro j _
        exact (((hv j).mul hφ.smooth).fderiv_right (m := ∞) (by simp)).clm_apply contDiff_const
      · exact hd.mul hφ.smooth
    have hsupp : HasCompactSupport (fun x => (coordTranspose v dZero φ x : ℂ)) := by
      refine HasCompactSupport.of_support_subset_isCompact hφ.compact ?_
      intro x hx
      by_contra hnot
      have hev : φ =ᶠ[𝓝 x] 0 := notMem_tsupport_iff_eventuallyEq.mp hnot
      have hφx : φ x = 0 := hev.self_of_nhds
      have hj : ∀ j : Fin 3, cpd j (fun y => v y j * φ y) x = 0 := by
        intro j
        have : (fun y => v y j * φ y) =ᶠ[𝓝 x] fun _ => 0 := by
          filter_upwards [hev] with y hy; simp [hy]
        unfold cpd; rw [this.fderiv_eq]; simp
      exact hx (by simp [coordTranspose, hj, hφx])
    exact (hu.continuous.mul (Complex.continuous_ofReal.comp hct.continuous)).integrable_of_hasCompactSupport
      hsupp.mul_left
  · have hφc : HasCompactSupport (fun x => (φ x : ℂ)) := hφ.compact.comp_left Complex.ofReal_zero
    exact (hRc.mul (Complex.continuous_ofReal.comp hφ.smooth.continuous)).integrable_of_hasCompactSupport
      hφc.mul_left
  · exact (LapWeakQHelp.ibp_gen v dZero hv hd u hu φ hφ).symm

lemma fderiv_cplx_comp {F : Coord → Axi.Merid} (hF : ContDiff ℝ ∞ F)
    (m : Fin 2) (x v : Coord) :
    fderiv ℝ (fun y : Coord => cplx F y m) x v = ((fderiv ℝ F x v m : ℝ) : ℂ) := by
  let L : Axi.Merid →L[ℝ] ℂ :=
    Complex.ofRealCLM.comp (EuclideanSpace.proj m : EuclideanSpace ℝ (Fin 2) →L[ℝ] ℝ)
  have hcomp : (fun y : Coord => cplx F y m) = L ∘ F := by
    ext y
    simp [L, cplx]
  have hf : HasFDerivAt (L ∘ F) (L.comp (fderiv ℝ F x)) x :=
    L.hasFDerivAt.comp x (hF.differentiable (by simp) x).hasFDerivAt
  rw [hcomp, hf.fderiv]
  simp [L]

lemma hasWeakVec_cplx_of_contDiff {F : Coord → Axi.Merid} (hF : ContDiff ℝ ∞ F) :
    HasWeakVec vQ0 dZero (cplx F) (cplx (Axi.dQ F)) ∧
    HasWeakVec vEta dZero (cplx F) (cplx (Axi.dEta F)) := by
  have hu : ∀ m : Fin 2, ContDiff ℝ ∞ (fun x : Coord => cplx F x m) := by
    intro m
    let L : Axi.Merid →L[ℝ] ℂ :=
      Complex.ofRealCLM.comp (EuclideanSpace.proj m : EuclideanSpace ℝ (Fin 2) →L[ℝ] ℝ)
    exact L.contDiff.comp hF
  refine ⟨fun m => ?_, fun m => ?_⟩
  · refine hasWeakFO_of_contDiff vQ0_component_smooth (hu m) (fun x => ?_)
    unfold LapWeakQHelp.genOp
    rw [Fin.sum_univ_three]
    have hv0 : vQ0 x 0 = 0 := rfl
    have hv1 : vQ0 x 1 = 1 := rfl
    have hv2 : vQ0 x 2 = 0 := rfl
    have hd0 : dZero x = 0 := rfl
    have hc1 : cdir 1 = (0, (1, 0)) := rfl
    rw [hv0, hv1, hv2, hd0, hc1, fderiv_cplx_comp hF m x (0, (1, 0))]
    simp [cplx, Axi.dQ]
  · refine hasWeakFO_of_contDiff LapWeakEtaHelp.vEta_component_smooth (hu m) (fun x => ?_)
    unfold LapWeakQHelp.genOp
    rw [Fin.sum_univ_three]
    have hv0 : vEta x 0 = 0 := rfl
    have hv1 : vEta x 1 = 0 := rfl
    have hv2 : vEta x 2 = 1 := rfl
    have hd0 : dZero x = 0 := rfl
    have hc2 : cdir 2 = (0, (0, 1)) := rfl
    rw [hv0, hv1, hv2, hd0, hc2, fderiv_cplx_comp hF m x (0, (0, 1))]
    simp [cplx, Axi.dEta]

lemma hasWeakFO_smul {v : Coord → Fin 3 → ℝ} {d : Coord → ℝ} (a : ℂ) {u g : Coord → ℂ}
    (h : HasWeakFO v d u g) :
    HasWeakFO v d (fun x => a * u x) (fun x => a * g x) := by
  refine ⟨fun φ hφ => ⟨?_, ?_⟩, fun φ hφ => ?_⟩
  · have h1 := ((h.1 φ hφ).1).const_mul a
    exact h1.congr (Eventually.of_forall fun x => by dsimp; ring)
  · have h2 := ((h.1 φ hφ).2).const_mul a
    exact h2.congr (Eventually.of_forall fun x => by dsimp; ring)
  · have he1 : (fun x => a * g x * (φ x : ℂ)) = fun x => a * (g x * (φ x : ℂ)) := by
      ext x; ring
    have he2 : (fun x => a * u x * (coordTranspose v d φ x : ℂ)) =
        fun x => a * (u x * (coordTranspose v d φ x : ℂ)) := by
      ext x; ring
    rw [he1, he2, integral_const_mul, integral_const_mul, h.2 φ hφ]

lemma hasWeakVec_smul {v : Coord → Fin 3 → ℝ} {d : Coord → ℝ} (a : ℂ) {b g : CProf}
    (h : HasWeakVec v d b g) :
    HasWeakVec v d (fun x => a • b x) (fun x => a • g x) := by
  intro m
  show HasWeakFO v d (fun x => a * b x m) (fun x => a * g x m)
  exact hasWeakFO_smul a (h m)

lemma hasWeakFO_add {v : Coord → Fin 3 → ℝ} {d : Coord → ℝ} {u1 u2 g1 g2 : Coord → ℂ}
    (h1 : HasWeakFO v d u1 g1) (h2 : HasWeakFO v d u2 g2) :
    HasWeakFO v d (fun x => u1 x + u2 x) (fun x => g1 x + g2 x) := by
  refine ⟨fun φ hφ => ⟨?_, ?_⟩, fun φ hφ => ?_⟩
  · have hi := ((h1.1 φ hφ).1).add ((h2.1 φ hφ).1)
    exact hi.congr (Eventually.of_forall fun x => by dsimp; ring)
  · have hi := ((h1.1 φ hφ).2).add ((h2.1 φ hφ).2)
    exact hi.congr (Eventually.of_forall fun x => by dsimp; ring)
  · have he1 : (fun x => (g1 x + g2 x) * (φ x : ℂ)) =
        fun x => g1 x * (φ x : ℂ) + g2 x * (φ x : ℂ) := by ext x; ring
    have he2 : (fun x => (u1 x + u2 x) * (coordTranspose v d φ x : ℂ)) =
        fun x => u1 x * (coordTranspose v d φ x : ℂ) + u2 x * (coordTranspose v d φ x : ℂ) := by
      ext x; ring
    rw [he1, he2, integral_add (h1.1 φ hφ).2 (h2.1 φ hφ).2,
      integral_add (h1.1 φ hφ).1 (h2.1 φ hφ).1, h1.2 φ hφ, h2.2 φ hφ]

lemma hasWeakVec_add' {v : Coord → Fin 3 → ℝ} {d : Coord → ℝ} {b1 b2 g1 g2 : CProf}
    (h1 : HasWeakVec v d b1 g1) (h2 : HasWeakVec v d b2 g2) :
    HasWeakVec v d (fun x => b1 x + b2 x) (fun x => g1 x + g2 x) := by
  intro m
  show HasWeakFO v d (fun x => b1 x m + b2 x m) (fun x => g1 x m + g2 x m)
  exact hasWeakFO_add (h1 m) (h2 m)

lemma contDiff_inletE0 {p : Params} {d dm dp : ℝ} {lam : ℂ} {q : Planar.Profile}
    (hq : Planar.IsGrowingEigenpair lam q) (hreg : BgRegime p d dm dp)
    (hν1 : p.ν ≤ 1) (hmode : p.mode = q) (i : Fin 2) :
    ContDiff ℝ ∞ (inletE0 p i) := by
  obtain ⟨_, _, _, -, -, hper⟩ := frozenStreamBounds lam q hq 0
  have hνpos : 0 < p.ν := p.ν_pos
  have hc1 : 1 ≤ p.c := by
    rw [hreg.c_eq, one_le_inv₀ (by positivity)]
    nlinarith
  have hP : ContDiff ℝ ∞ (periodicStream q p.c) := (hper p.c hc1).1
  have hfro : ContDiff ℝ ∞ (p.frozenStream i) := inletCD_frozenStream hP hmode i
  have hcut : ContDiff ℝ ∞ (p.cutStream i) := by
    unfold Params.cutStream
    exact ((contDiff_ageCutoff p.H).comp contDiff_fst).mul (hfro.comp contDiff_snd)
  have hQ : ContDiff ℝ ∞ (fun m => fderiv ℝ (p.cutStream i) m (0, (1, 0))) :=
    inletCD_fderiv_apply hcut (0, (1, 0))
  have hE : ContDiff ℝ ∞ (fun m => fderiv ℝ (p.cutStream i) m (0, (0, 1))) :=
    inletCD_fderiv_apply hcut (0, (0, 1))
  unfold inletE0 Axi.dQ Axi.dEta
  fun_prop

end F10Help

/-- In `BgRegime` with `p.ν ≤ 1` and `p.mode = q` (`IsGrowingEigenpair lam q`), the flat inlet
profile `inletProf p α` has weak `q`-derivative `inletProfQ p α` and weak `η`-derivative
`inletProfEta p α`. -/
theorem inletProf_hasWeakVec {p : Params} {d dm dp : ℝ} {lam : ℂ} {q : Planar.Profile}
    (hq : Planar.IsGrowingEigenpair lam q) (hreg : BgRegime p d dm dp)
    (hν1 : p.ν ≤ 1) (hmode : p.mode = q) (α : E2) :
    HasWeakVec vQ0 dZero (inletProf p α) (inletProfQ p α) ∧
    HasWeakVec vEta dZero (inletProf p α) (inletProfEta p α) := by
  have h0 := F10Help.hasWeakVec_cplx_of_contDiff (F10Help.contDiff_inletE0 hq hreg hν1 hmode 0)
  have h1 := F10Help.hasWeakVec_cplx_of_contDiff (F10Help.contDiff_inletE0 hq hreg hν1 hmode 1)
  have heP : inletProf p α = fun x =>
      ((α 0 : ℝ) : ℂ) • cplx (inletE0 p 0) x + ((α 1 : ℝ) : ℂ) • cplx (inletE0 p 1) x := by
    ext x m; simp [inletProf, Fin.sum_univ_two]
  have heQ : inletProfQ p α = fun x =>
      ((α 0 : ℝ) : ℂ) • cplx (Axi.dQ (inletE0 p 0)) x +
        ((α 1 : ℝ) : ℂ) • cplx (Axi.dQ (inletE0 p 1)) x := by
    ext x m; simp [inletProfQ, Fin.sum_univ_two]
  have heE : inletProfEta p α = fun x =>
      ((α 0 : ℝ) : ℂ) • cplx (Axi.dEta (inletE0 p 0)) x +
        ((α 1 : ℝ) : ℂ) • cplx (Axi.dEta (inletE0 p 1)) x := by
    ext x m; simp [inletProfEta, Fin.sum_univ_two]
  rw [heP, heQ, heE]
  exact ⟨F10Help.hasWeakVec_add' (F10Help.hasWeakVec_smul _ h0.1) (F10Help.hasWeakVec_smul _ h1.1),
    F10Help.hasWeakVec_add' (F10Help.hasWeakVec_smul _ h0.2) (F10Help.hasWeakVec_smul _ h1.2)⟩

/-- Uniqueness of the value of `K0 f` for any `K0` satisfying `IsK0op p K0` on the reconstructed
flat response `b_0 + z - Eα = T_0 (toProf p.c f)`. -/
theorem flatK0_reconstructed_congr {p : Params} {d dm dp : ℝ} {lam : ℂ} {q : Planar.Profile}
    (hq : Planar.IsGrowingEigenpair lam q) (hreg : BgRegime p d dm dp)
    (hν1 : p.ν ≤ 1) (hmode : p.mode = q)
    (K0 : HpR p.c →L[ℝ] HpR p.c) (hK0 : IsK0op p K0)
    (f : HpR p.c) (α : E2) (b0 b0q b0η z zq zη : CProf)
    (hb0q : HasWeakVec vQ0 dZero b0 b0q)
    (hb0η : HasWeakVec vEta dZero b0 b0η)
    (hzq : HasWeakVec vQ0 dZero z zq)
    (hzη : HasWeakVec vEta dZero z zη)
    (hbf_class : InFlatClass p.c bgp (fun x => b0 x + z x - inletProf p α x))
    (hbf_resp : IsFlatResponse p.ν 0 (toProf p.c f) (fun x => b0 x + z x - inletProf p α x)) :
    toProf p.c (K0 f) =ᵐ[hMeas p.c bgp] fun x =>
      flatK p.train (fun y => b0 y + z y - inletProf p α y)
        (fun y => b0q y + zq y - inletProfQ p α y)
        (fun y => b0η y + zη y - inletProfEta p α y) x := by
  have hc : 0 < p.c := p.c_pos
  have hν : 0 < p.ν := p.ν_pos
  obtain ⟨b', gq', gη', hb'_class, hb'_resp, hgq', hgη', hK0_ae⟩ := hK0 f
  have hb_ae_h : b' =ᵐ[hMeas p.c bgp] (fun x => b0 x + z x - inletProf p α x) :=
    flatResponse_unique_ae hν hc (inHr_toProf hc f) hb'_class hb'_resp hbf_class hbf_resp
  have hb_ae_vol : ∀ᵐ x : Coord, 0 < x.1 → b' x = b0 x + z x - inletProf p α x :=
    CongrHelp.ae_volume_of_ageμ hc hb'_class.inHr.periodic hbf_class.inHr.periodic hb_ae_h
  obtain ⟨hin_q, hin_η⟩ := inletProf_hasWeakVec hq hreg hν1 hmode α
  have hbf_q : HasWeakVec vQ0 dZero (fun x => b0 x + z x - inletProf p α x)
      (fun x => b0q x + zq x - inletProfQ p α x) :=
    flatCls_hasWeakVec_sub (F10Help.hasWeakVec_add' hb0q hzq) hin_q
  have hbf_η : HasWeakVec vEta dZero (fun x => b0 x + z x - inletProf p α x)
      (fun x => b0η x + zη x - inletProfEta p α x) :=
    flatCls_hasWeakVec_sub (F10Help.hasWeakVec_add' hb0η hzη) hin_η
  have hb'_q2 : HasWeakVec vQ0 dZero b' (fun x => b0q x + zq x - inletProfQ p α x) :=
    hasWeakVec_congr hb_ae_vol (Eventually.of_forall fun _ _ => rfl) hbf_q
  have hb'_η2 : HasWeakVec vEta dZero b' (fun x => b0η x + zη x - inletProfEta p α x) :=
    hasWeakVec_congr hb_ae_vol (Eventually.of_forall fun _ _ => rfl) hbf_η
  have hgq_vol : ∀ᵐ x : Coord, 0 < x.1 → gq' x = b0q x + zq x - inletProfQ p α x :=
    GradBoundHelp.hasWeakVec_unique hgq' hb'_q2
  have hgη_vol : ∀ᵐ x : Coord, 0 < x.1 → gη' x = b0η x + zη x - inletProfEta p α x :=
    GradBoundHelp.hasWeakVec_unique hgη' hb'_η2
  have hflatK_vol : ∀ᵐ x : Coord, 0 < x.1 →
      flatK p.train b' gq' gη' x =
        flatK p.train (fun y => b0 y + z y - inletProf p α y)
          (fun y => b0q y + zq y - inletProfQ p α y)
          (fun y => b0η y + zη y - inletProfEta p α y) x := by
    filter_upwards [hb_ae_vol, hgq_vol, hgη_vol] with x hb hgq hgη hpos
    ext m
    simp only [flatK, WithLp.ofLp_toLp, hb hpos, hgq hpos, hgη hpos]
  have hflatK_h : flatK p.train b' gq' gη' =ᵐ[hMeas p.c bgp]
      fun x => flatK p.train (fun y => b0 y + z y - inletProf p α y)
        (fun y => b0q y + zq y - inletProfQ p α y)
        (fun y => b0η y + zη y - inletProfEta p α y) x :=
    hMeasAe p.c bgp _ hc hflatK_vol
  exact hK0_ae.trans hflatK_h

/-! ## 4. Leaf `PartII-b:F10/1` (`FlatK0OperatorExists`) and full conditional assembly -/

/-- **Target `Prop` of `PartII-b:F10/1` (`FlatK0OperatorExists`, SP 2326-2344)**:
given the early (`0 < s ≤ p.H`) and late (`s > p.H`) `H_p` bounds on the free interaction
`flatK p.train b0 b0q b0η` from `FlatReconstruction` (`PartII-b:F9`) and `profileGraphFlat_bgp`
(`PartII-b:T14`), the flat interaction operator `K_0 = flatK p.train ∘ T_0` exists as a bounded
linear operator `K0 : HpR p.c →L[ℝ] HpR p.c` satisfying `IsK0op p K0`. -/
def FlatK0OperatorExists : Prop :=
  ∀ (Sig : ℝ) (lam : ℂ) (q : Blueprint.Planar.Profile), 0 < Sig →
    Blueprint.Planar.IsGrowingEigenpair lam q →
  ∀ dm dp : ℝ, 0 < dm → ∃ ν₀ : ℝ, 0 < ν₀ ∧
    ∀ (p : Params) (d : ℝ), BgRegime p d dm dp → p.ν ≤ ν₀ → p.ageCut = Sig → p.mode = q →
      ∀ (C : ℝ) (k : ℕ), 0 < C →
      (∀ F b0 : CProf, InHr p.c bgp F → InFlatClass p.c bgp b0 → IsFlatResponse p.ν 0 F b0 →
        ∃ b0q b0η : CProf,
          HasWeakVec vQ0 dZero b0 b0q ∧ HasWeakVec vEta dZero b0 b0η ∧
          InHr p.c bgp (flatK p.train b0 b0q b0η) ∧
          eLpNorm (flatK p.train b0 b0q b0η) (ENNReal.ofReal bgp)
              ((hMeas p.c bgp).restrict (Ioc 0 p.H ×ˢ univ)) ≤
            ENNReal.ofReal (C * (p.ν ^ k)⁻¹ * (p.ν ^ (-1 / 2 : ℝ) * Real.sqrt p.H + p.H)) *
              hNorm p.c bgp F ∧
          eLpNorm (flatK p.train b0 b0q b0η) (ENNReal.ofReal bgp)
              ((hMeas p.c bgp).restrict (Ioi p.H ×ˢ univ)) ≤
            ENNReal.ofReal
                (C * (p.ν ^ k)⁻¹ * p.H ^ (-1 / 2 : ℝ) * (p.ν ^ (-1 / 2 : ℝ) + 1)) *
              hNorm p.c bgp F) →
      ∃ K0 : HpR p.c →L[ℝ] HpR p.c, IsK0op p K0

/-- **Conditional assembly of `FlatInverse` (`PartII-b:F10`, SP 2326-2344)** from
`FlatK0OperatorExists` (`PartII-b:F10/1`) and `FlatReconstruction` (`PartII-b:F9`). -/
theorem flatInverse_of_k0Exists
    (hK0_ex : FlatK0OperatorExists)
    (hFR : FlatReconstruction) :
    FlatInverse := by
  obtain ⟨C_late, hCl, H_FR⟩ := hFR
  intro lam q hq m hm dm dp hdm
  set Sig₀ : ℝ := max 1 (4 * C_late / m)
  have hSig₀ : 0 < Sig₀ := lt_of_lt_of_le zero_lt_one (le_max_left 1 _)
  refine ⟨Sig₀, hSig₀, ?_⟩
  intro Sig hSig
  have hSig1 : 1 ≤ Sig := le_trans (le_max_left 1 _) hSig
  have hSig_pos : 0 < Sig := lt_of_lt_of_le zero_lt_one hSig1
  have h1Sig_pos : 0 < 1 + Sig := by linarith
  have hlam_pos : 0 < lam.re := hq.re_pos
  set a' : ℝ := min (m / (4 * Sig)) (lam.re / (2 * (1 + Sig) ^ 2))
  have ha'_pos : 0 < a' := lt_min (by positivity) (by positivity)
  have ha'_lt : a' < lam.re / (1 + Sig) ^ 2 := by
    have hle : a' ≤ lam.re / (2 * (1 + Sig) ^ 2) := min_le_right _ _
    have hlt : lam.re / (2 * (1 + Sig) ^ 2) < lam.re / (1 + Sig) ^ 2 := by
      have hden : 0 < (1 + Sig) ^ 2 := by positivity
      rw [div_lt_div_iff₀ (by positivity) hden]
      nlinarith
    exact lt_of_le_of_lt hle hlt
  have ha'_le : a' ≤ m / (4 * Sig) := min_le_left _ _
  obtain ⟨C, k, ν₁, hC, hν₁, H_rec⟩ := H_FR Sig lam q hSig_pos hq a' ha'_pos ha'_lt dm dp hdm
  obtain ⟨ν₂, hν₂, H_K0⟩ := hK0_ex Sig lam q hSig_pos hq dm dp hdm
  set ν₃ : ℝ := min 1 (m / (4 * C_late))
  have hν₃ : 0 < ν₃ := lt_min zero_lt_one (by positivity)
  set ν₀ : ℝ := min ν₁ (min ν₂ ν₃)
  have hν₀ : 0 < ν₀ := lt_min hν₁ (lt_min hν₂ hν₃)
  refine ⟨C, k, ν₀, hC, hν₀, ?_⟩
  intro p d hreg hν hSg hmode
  have hν₁' : p.ν ≤ ν₁ := hν.trans (min_le_left _ _)
  have hν₂' : p.ν ≤ ν₂ := hν.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hν₃' : p.ν ≤ ν₃ := hν.trans ((min_le_right _ _).trans (min_le_right _ _))
  have hν_le1 : p.ν ≤ 1 := hν₃'.trans (min_le_left _ _)
  have hν_m : p.ν ≤ m / (4 * C_late) := hν₃'.trans (min_le_right _ _)
  obtain ⟨hK_bd, hCol_bd, R0, hR0_norm, hR0_spec⟩ := H_rec p d hreg hν₁' hSg hmode
  obtain ⟨K0₀, hK0₀⟩ := H_K0 p d hreg hν₂' hSg hmode C k hC hK_bd
  obtain ⟨C0₀, hC0₀⟩ := exists_C0op_of_flatColumn_inHr p (fun i => (hCol_bd i).1)
  refine ⟨⟨K0₀, C0₀, hK0₀, hC0₀⟩, ?_⟩
  intro K0 C0 hK0 hC0
  have hν4 : C_late * p.ν ^ 4 ≤ m / 4 := by
    have hp4 : p.ν ^ 4 ≤ p.ν ^ 1 := pow_le_pow_of_le_one p.ν_pos.le hν_le1 (by norm_num)
    rw [pow_one] at hp4
    calc C_late * p.ν ^ 4 ≤ C_late * p.ν := mul_le_mul_of_nonneg_left hp4 hCl.le
      _ ≤ C_late * (m / (4 * C_late)) := mul_le_mul_of_nonneg_left hν_m hCl.le
      _ = m / 4 := by field_simp [hCl.ne']
  have hrate := flatInverse_rate_le_of_thresholds hCl hm p.ν_pos hSig ha'_le hν4
  have hR0_le : ‖R0‖ ≤ C * (p.ν ^ k)⁻¹ * Real.exp (m / p.ν) := by
    refine hR0_norm.trans ?_
    have hCk : 0 ≤ C * (p.ν ^ k)⁻¹ := by have := p.ν_pos; positivity
    exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hrate) hCk
  refine ⟨R0, fun F => ?_, hR0_le⟩
  obtain ⟨b0, b0q, b0η, z, zq, zη, _, _, hb0q, hb0η, hzq, hzη, _, hbf_class, hbf_resp, hrec_ae⟩ :=
    hR0_spec F
  have hK_ae := flatK0_reconstructed_congr hq hreg hν_le1 hmode K0 hK0
    ((WithLp.fstL 1 ℝ (HpR p.c) E2) (R0 F))
    ((WithLp.sndL 1 ℝ (HpR p.c) E2) (R0 F)) b0 b0q b0η z zq zη hb0q hb0η hzq hzη hbf_class hbf_resp
  exact rowOp_eq_of_toProf_ae K0 C0 hC0 R0 F _ hK_ae hrec_ae

end UnforcedLeray.Short.IIb

end
