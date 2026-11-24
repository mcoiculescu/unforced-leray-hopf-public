import UnforcedLeray.Short.PartIIa.Sub.N01.Defs
import UnforcedLeray.Short.PartIIIb.NearInst.Masked.Proofs.TensorTestDense
import UnforcedLeray.Short.PartIIIb.NearInst.Masked.Proofs.TensorTestDivMem

/-!
# `PartII-a:N01/8`: completion from smooth tensors (source line 1675)

The smooth tensor tests form a dense `ℂ`-submodule `testSub c` of `H_T` (`TensorTestDense`), and
`s div_ε M ∈ H` for each test (`TensorTestDivMem`).  The bound on tests and `F = 0` makes the
value `T(s div_ε M)` depend only on the class of `M`, so `F ↦ T(s div_ε M)` is a linear map on
the dense subspace; `LinearMap.extendOfNorm` (as in `F14`) gives the bounded extension.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal NNReal ContDiff

namespace UnforcedLeray.Short.PartIIa.N01

open UnforcedLeray.B0220 (Profile HSpace measureH)
open UnforcedLeray.B0223 (MeridC)

/-! ## Linearity of `div_ε` on smooth tests (copied from the `ReIm` leaf) -/

theorem diff_coord {f : Profile → TensorVal} (hf : Differentiable ℝ f) (j : Fin 4) :
    Differentiable ℝ (fun q => f q j) :=
  ((EuclideanSpace.proj j : TensorVal →L[ℂ] ℂ).restrictScalars ℝ).differentiable.comp hf

theorem fderiv_lin {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (f g : Profile → E) (hf : Differentiable ℝ f) (hg : Differentiable ℝ g) (a : ℂ)
    (p w : Profile) :
    fderiv ℝ (fun q => f q + a • g q) p w = fderiv ℝ f p w + a • fderiv ℝ g p w := by
  have hga : DifferentiableAt ℝ (fun q => a • g q) p := (hg p).const_smul a
  have hc : fderiv ℝ (fun q => a • g q) p = a • fderiv ℝ g p :=
    fderiv_const_smul (hg p) a
  have h1 : fderiv ℝ (fun q => f q + a • g q) p = fderiv ℝ f p + a • fderiv ℝ g p := by
    show fderiv ℝ (f + fun q => a • g q) p = _
    rw [fderiv_add (hf p) hga, hc]
  rw [h1, ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply]

theorem opQ_lin (u v : Profile → ℂ) (hu : Differentiable ℝ u) (hv : Differentiable ℝ v)
    (a : ℂ) (ε : ℝ) (p : Profile) :
    opQ ε (fun q => u q + a • v q) p = opQ ε u p + a • opQ ε v p := by
  simp only [opQ, opK, opS, pdQ, pdEta, pdS]
  simp only [fderiv_lin u v hu hv a]
  simp only [Complex.real_smul, smul_eq_mul]
  ring

theorem pdEta_lin (u v : Profile → ℂ) (hu : Differentiable ℝ u) (hv : Differentiable ℝ v)
    (a : ℂ) (p : Profile) :
    pdEta (fun q => u q + a • v q) p = pdEta u p + a • pdEta v p := by
  unfold pdEta
  exact fderiv_lin u v hu hv a p _

theorem divEps_apply0 (F : Profile → TensorVal) (ε : ℝ) (p : Profile) :
    divEps ε F p 0 = opQ ε (fun q => F q 0) p + pdEta (fun q => F q 1) p - (ε : ℂ) * F p 3 :=
  rfl

theorem divEps_apply1 (F : Profile → TensorVal) (ε : ℝ) (p : Profile) :
    divEps ε F p 1 = opQ ε (fun q => F q 1) p + pdEta (fun q => F q 2) p :=
  rfl

theorem divEps_lin (f g : Profile → TensorVal) (hf : Differentiable ℝ f)
    (hg : Differentiable ℝ g) (a : ℂ) (ε : ℝ) (p : Profile) :
    divEps ε (fun q => f q + a • g q) p = divEps ε f p + a • divEps ε g p := by
  have k0 := opQ_lin (fun q => f q 0) (fun q => g q 0) (diff_coord hf 0) (diff_coord hg 0) a ε p
  have k1 := opQ_lin (fun q => f q 1) (fun q => g q 1) (diff_coord hf 1) (diff_coord hg 1) a ε p
  have d1 := pdEta_lin (fun q => f q 1) (fun q => g q 1) (diff_coord hf 1) (diff_coord hg 1) a p
  have d2 := pdEta_lin (fun q => f q 2) (fun q => g q 2) (diff_coord hf 2) (diff_coord hg 2) a p
  ext j
  fin_cases j
  · show divEps ε (fun q => f q + a • g q) p 0 = (divEps ε f p + a • divEps ε g p) 0
    simp only [divEps_apply0, PiLp.add_apply, PiLp.smul_apply]
    rw [k0, d1]
    simp only [smul_eq_mul]
    ring
  · show divEps ε (fun q => f q + a • g q) p 1 = (divEps ε f p + a • divEps ε g p) 1
    simp only [divEps_apply1, PiLp.add_apply, PiLp.smul_apply]
    rw [k1, d2]
    simp only [smul_eq_mul]
    ring

theorem divEps_add (M N : Profile → TensorVal) (hM : Differentiable ℝ M)
    (hN : Differentiable ℝ N) (ε : ℝ) (p : Profile) :
    divEps ε (fun q => M q + N q) p = divEps ε M p + divEps ε N p := by
  have h := divEps_lin M N hM hN 1 ε p
  simpa using h

theorem divEps_sub (M N : Profile → TensorVal) (hM : Differentiable ℝ M)
    (hN : Differentiable ℝ N) (ε : ℝ) (p : Profile) :
    divEps ε (fun q => M q - N q) p = divEps ε M p - divEps ε N p := by
  have e : (fun q => M q - N q) = fun q => M q + (-1 : ℂ) • N q := by
    funext q
    simp [sub_eq_add_neg]
  rw [e, divEps_lin M N hM hN (-1) ε p]
  simp [sub_eq_add_neg]

theorem divEps_zero (ε : ℝ) (p : Profile) : divEps ε (fun _ => (0 : TensorVal)) p = 0 := by
  ext j
  fin_cases j
  · show divEps ε (fun _ => (0 : TensorVal)) p 0 = (0 : MeridC) 0
    simp [divEps_apply0, opQ, opK, opS, pdQ, pdEta, pdS]
  · show divEps ε (fun _ => (0 : TensorVal)) p 1 = (0 : MeridC) 1
    simp [divEps_apply1, opQ, opK, opS, pdQ, pdEta, pdS]

theorem divEps_smul (M : Profile → TensorVal) (hM : Differentiable ℝ M) (a : ℂ) (ε : ℝ)
    (p : Profile) : divEps ε (fun q => a • M q) p = a • divEps ε M p := by
  have h := divEps_lin (fun _ => (0 : TensorVal)) M (differentiable_const _) hM a ε p
  simpa [divEps_zero] using h

/-! ## The smooth tensor tests form a submodule -/

theorem isTest_zero (c : ℝ) : IsTensorTest c (fun _ => (0 : TensorVal)) :=
  { smooth := contDiff_const
    periodic := by intro p; rfl
    band := ⟨1, 1, 0, one_pos, fun _ h => absurd rfl h⟩ }

theorem isTest_add {c : ℝ} {M N : Profile → TensorVal} (hM : IsTensorTest c M)
    (hN : IsTensorTest c N) : IsTensorTest c (fun p => M p + N p) := by
  refine
    { smooth := hM.smooth.add hN.smooth
      periodic := ?_
      band := ?_ }
  · intro p
    show M (p.1, p.2.1 + c, p.2.2) + N (p.1, p.2.1 + c, p.2.2) = M p + N p
    rw [hM.periodic p, hN.periodic p]
  · obtain ⟨s0, s1, L, hs0, hb⟩ := hM.band
    obtain ⟨t0, t1, K, ht0, hk⟩ := hN.band
    refine ⟨min s0 t0, max s1 t1, max L K, lt_min hs0 ht0, fun p hne => ?_⟩
    by_cases h1 : M p = 0
    · have h2 : N p ≠ 0 := by
        intro h2
        apply hne
        simp [h1, h2]
      obtain ⟨hI, hL⟩ := hk p h2
      exact ⟨⟨le_trans (min_le_right _ _) hI.1, le_trans hI.2 (le_max_right _ _)⟩,
        le_trans hL (le_max_right _ _)⟩
    · obtain ⟨hI, hL⟩ := hb p h1
      exact ⟨⟨le_trans (min_le_left _ _) hI.1, le_trans hI.2 (le_max_left _ _)⟩,
        le_trans hL (le_max_left _ _)⟩

theorem isTest_smul {c : ℝ} {M : Profile → TensorVal} (hM : IsTensorTest c M) (a : ℂ) :
    IsTensorTest c (fun p => a • M p) := by
  refine
    { smooth := hM.smooth.const_smul a
      periodic := ?_
      band := ?_ }
  · intro p
    show a • M (p.1, p.2.1 + c, p.2.2) = a • M p
    rw [hM.periodic p]
  · obtain ⟨s0, s1, L, hs0, hb⟩ := hM.band
    exact ⟨s0, s1, L, hs0, fun p hne => hb p (fun h => hne (by simp [h]))⟩

/-- The smooth tensor tests (as elements of `H_T`) form a `ℂ`-submodule. -/
def testSub (c : ℝ) : Submodule ℂ (HTSpace c) where
  carrier := {F | ∃ M : Profile → TensorVal, IsTensorTest c M ∧
    (F : Profile → TensorVal) =ᵐ[measureHT c] M}
  add_mem' := by
    rintro F G ⟨M, hM, hFM⟩ ⟨N, hN, hGN⟩
    refine ⟨fun p => M p + N p, isTest_add hM hN, ?_⟩
    filter_upwards [Lp.coeFn_add F G, hFM, hGN] with p h1 h2 h3
    rw [h1, Pi.add_apply, h2, h3]
  zero_mem' := by
    refine ⟨fun _ => 0, isTest_zero c, ?_⟩
    filter_upwards [Lp.coeFn_zero TensorVal 2 (measureHT c)] with p hp
    simpa using hp
  smul_mem' := by
    rintro a F ⟨M, hM, hFM⟩
    refine ⟨fun p => a • M p, isTest_smul hM a, ?_⟩
    filter_upwards [Lp.coeFn_smul a F, hFM] with p h1 h2
    simp [h1, h2]

theorem testSub_dense (c : ℝ) (hc : 0 < c) : DenseRange (testSub c).subtype := by
  unfold DenseRange
  have hr : Set.range (testSub c).subtype =
      ((testSub c : Submodule ℂ (HTSpace c)) : Set (HTSpace c)) := by
    ext x
    constructor
    · rintro ⟨y, rfl⟩
      exact y.2
    · intro hx
      exact ⟨⟨x, hx⟩, rfl⟩
  rw [hr]
  intro F
  rw [Metric.mem_closure_iff]
  intro η hη
  obtain ⟨M, hMt, hMm, hdist⟩ :=
    UnforcedLeray.Short.PartIIIb.NearInst.Masked.tensorTestDense c hc F η hη
  refine ⟨hMm.toLp M, ⟨M, hMt, hMm.coeFn_toLp⟩, ?_⟩
  rw [dist_eq_norm]
  exact hdist

theorem diffOf {c : ℝ} {M : Profile → TensorVal} (h : IsTensorTest c M) :
    Differentiable ℝ M :=
  h.smooth.differentiable (by simp)

/-! ## Well-definedness of the stress map on classes of tests -/

theorem stress_key (c ε K : ℝ) (hc : 0 < c) (T : HSpace c MeridC →L[ℂ] HSpace c MeridC)
    (hyp : ∀ M : Profile → TensorVal, IsTensorTest c M → ∀ (F : HTSpace c) (G : HSpace c MeridC),
      (F : Profile → TensorVal) =ᵐ[measureHT c] M →
      (G : Profile → MeridC) =ᵐ[measureH c] (fun p => (p.1 : ℂ) • divEps ε M p) →
        ‖T G‖ ≤ K * ‖F‖)
    (M N : Profile → TensorVal) (hM : IsTensorTest c M) (hN : IsTensorTest c N)
    (hMN : M =ᵐ[measureHT c] N) (G G' : HSpace c MeridC)
    (hG : (G : Profile → MeridC) =ᵐ[measureH c] (fun p => (p.1 : ℂ) • divEps ε M p))
    (hG' : (G' : Profile → MeridC) =ᵐ[measureH c] (fun p => (p.1 : ℂ) • divEps ε N p)) :
    T G = T G' := by
  have hΔ : IsTensorTest c (fun p => M p - N p) := by
    have h := isTest_add hM (isTest_smul hN (-1))
    simpa [sub_eq_add_neg] using h
  have dM := diffOf hM
  have dN := diffOf hN
  obtain ⟨G₀, hG₀⟩ : ∃ G₀ : HSpace c MeridC,
      (G₀ : Profile → MeridC) =ᵐ[measureH c]
        (fun p => (p.1 : ℂ) • divEps ε (fun q => M q - N q) p) :=
    ⟨(UnforcedLeray.Short.PartIIIb.NearInst.Masked.tensorTestDivMem c ε hc _ hΔ).toLp _, MemLp.coeFn_toLp _⟩
  have hzero : ((0 : HTSpace c) : Profile → TensorVal) =ᵐ[measureHT c]
      (fun p => M p - N p) := by
    filter_upwards [Lp.coeFn_zero TensorVal 2 (measureHT c), hMN] with p h1 h2
    rw [h1, Pi.zero_apply, h2, sub_self]
  have hb := hyp _ hΔ 0 G₀ hzero hG₀
  rw [norm_zero, mul_zero] at hb
  have hT0 : T G₀ = 0 := norm_le_zero_iff.mp hb
  have hdiff : G - G' = G₀ := by
    apply Lp.ext
    filter_upwards [Lp.coeFn_sub G G', hG, hG', hG₀] with p h1 h2 h3 h4
    rw [h1, h4, Pi.sub_apply, h2, h3, divEps_sub M N dM dN ε p, smul_sub]
  have h5 : T G - T G' = T G₀ := by
    rw [← map_sub, hdiff]
  rw [hT0] at h5
  exact sub_eq_zero.mp h5

/-! ## The completion -/

/-- **`PartII-a:N01/8` — completion from smooth tensors** (line 1675). -/
theorem stressCompletion : StressCompletion := by
  intro c ε hc T K hK hyp
  have hrep : ∀ x : testSub c, ∃ M : Profile → TensorVal, IsTensorTest c M ∧
      ((x : HTSpace c) : Profile → TensorVal) =ᵐ[measureHT c] M := fun x => x.2
  choose Mx hMxt hMxe using hrep
  obtain ⟨Gx, hGxe⟩ : ∃ Gx : testSub c → HSpace c MeridC, ∀ x : testSub c,
      (Gx x : Profile → MeridC) =ᵐ[measureH c] (fun p => (p.1 : ℂ) • divEps ε (Mx x) p) :=
    ⟨fun x => (UnforcedLeray.Short.PartIIIb.NearInst.Masked.tensorTestDivMem c ε hc (Mx x) (hMxt x)).toLp _,
      fun x => MemLp.coeFn_toLp _⟩
  -- the representative of a sum and of a scalar multiple
  have hMNadd : ∀ x y : testSub c,
      Mx (x + y) =ᵐ[measureHT c] (fun p => Mx x p + Mx y p) := by
    intro x y
    filter_upwards [hMxe (x + y), Lp.coeFn_add (x : HTSpace c) (y : HTSpace c), hMxe x, hMxe y]
      with p h1 h2 h3 h4
    simp only [Submodule.coe_add] at h1
    rw [← h1, h2, Pi.add_apply, h3, h4]
  have hMNsmul : ∀ (a : ℂ) (x : testSub c),
      Mx (a • x) =ᵐ[measureHT c] (fun p => a • Mx x p) := by
    intro a x
    filter_upwards [hMxe (a • x), Lp.coeFn_smul a (x : HTSpace c), hMxe x] with p h1 h2 h3
    simp only [Submodule.coe_smul] at h1
    rw [← h1, h2, Pi.smul_apply, h3]
  have hGsum : ∀ x y : testSub c,
      ((Gx x + Gx y : HSpace c MeridC) : Profile → MeridC) =ᵐ[measureH c]
        fun p => (p.1 : ℂ) • divEps ε (fun q => Mx x q + Mx y q) p := by
    intro x y
    filter_upwards [Lp.coeFn_add (Gx x) (Gx y), hGxe x, hGxe y] with p h1 h2 h3
    rw [h1, Pi.add_apply, h2, h3, divEps_add (Mx x) (Mx y) (diffOf (hMxt x))
      (diffOf (hMxt y)) ε p, smul_add]
  have hGsmul : ∀ (a : ℂ) (x : testSub c),
      ((a • Gx x : HSpace c MeridC) : Profile → MeridC) =ᵐ[measureH c]
        fun p => (p.1 : ℂ) • divEps ε (fun q => a • Mx x q) p := by
    intro a x
    filter_upwards [Lp.coeFn_smul a (Gx x), hGxe x] with p h1 h2
    rw [h1, Pi.smul_apply, h2, divEps_smul (Mx x) (diffOf (hMxt x)) a ε p, smul_comm]
  -- the linear map on the dense subspace
  let φ : testSub c →ₗ[ℂ] HSpace c MeridC :=
    { toFun := fun x => T (Gx x)
      map_add' := by
        intro x y
        show T (Gx (x + y)) = T (Gx x) + T (Gx y)
        rw [← map_add]
        exact stress_key c ε K hc T hyp _ _ (hMxt _) (isTest_add (hMxt x) (hMxt y))
          (hMNadd x y) _ _ (hGxe _) (hGsum x y)
      map_smul' := by
        intro a x
        show T (Gx (a • x)) = (RingHom.id ℂ) a • T (Gx x)
        rw [RingHom.id_apply, ← map_smul]
        exact stress_key c ε K hc T hyp _ _ (hMxt _) (isTest_smul (hMxt x) a)
          (hMNsmul a x) _ _ (hGxe _) (hGsmul a x) }
  have hφb : ∀ x : testSub c, ‖φ x‖ ≤ K * ‖(x : HTSpace c)‖ := fun x =>
    hyp (Mx x) (hMxt x) x (Gx x) (hMxe x) (hGxe x)
  have hdense := testSub_dense c hc
  have hnS : ∃ C : ℝ, ∀ x : testSub c, ‖φ x‖ ≤ C * ‖(testSub c).subtype x‖ :=
    ⟨K, fun x => hφb x⟩
  set S := φ.extendOfNorm (testSub c).subtype with hS
  have hSe : ∀ x : testSub c, S ((testSub c).subtype x) = φ x :=
    fun x => LinearMap.extendOfNorm_eq hdense hnS x
  refine ⟨S, ?_, ?_⟩
  · intro M hM F G hFM hG
    have hFmem : (F : HTSpace c) ∈ testSub c := ⟨M, hM, hFM⟩
    have hSF : S F = φ ⟨F, hFmem⟩ := hSe ⟨F, hFmem⟩
    rw [hSF]
    exact stress_key c ε K hc T hyp (Mx ⟨F, hFmem⟩) M (hMxt _) hM
      ((hMxe _).symm.trans hFM) (Gx _) G (hGxe _) hG
  · intro F
    have hbS : ‖S F‖ ≤ K * ‖F‖ := by
      refine isClosed_property hdense
        (isClosed_le (S.continuous.norm) (continuous_const.mul continuous_norm)) (fun x => ?_) F
      show ‖S ((testSub c).subtype x)‖ ≤ K * ‖(testSub c).subtype x‖
      rw [hSe]
      exact hφb x
    exact hbS

end UnforcedLeray.Short.PartIIa.N01
